#!/usr/bin/env python3
"""Phase 1 Trusted Controller: Dispatch Zero-Token Air-Gapped Bohrium Sandbox for Lean 4 PR Verification.

DESIGN PRINCIPLES (Option A2):
  1. Never check out untrusted PR code into a working tree with hooks/filters/symlinks;
     extract blobs directly from a bare git repo via `git ls-tree` + `git cat-file`.
  2. Enforce strict path allowlist & forbidden-file guard (lakefile.toml, lean-toolchain,
     lake-manifest.json, Challenge.lean, comparator.json, scripts/, .github/, .olean/.ltar,
     symlinks, submodules, Trojan-Source BiDi Unicode).
  3. Launch Bohrium Sandbox from a pre-published static template with:
       - NO `--inherit-auth`
       - NO `--mount-user-storage`
       - NO secret `--env` variables
       - Hard `--timeout`
       - Optional pinned read-only Wenyon dataset (`--wenyon-mode read --wenyon-version <int>`)
       - Template-level empty egress allowlist `{"replace":[]}`
  4. Upload payload tarball, invoke baked-in `/opt/openverify-lean/bin/verify_pr_in_sandbox.py`
     (which enforces inner `bwrap --unshare-all --clearenv --uid 65534` + `REAL_ISOLATION_CANARY`).
  5. Retrieve bounded `/out/verdict.json`, strictly validate JSON schema + pinned `head_sha`,
     and ALWAYS delete the sandbox in a `finally` block.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path
from typing import Any

FORBIDDEN_EXACT = frozenset({
    "lakefile.toml",
    "lakefile.lean",
    "lake-manifest.json",
    "lean-toolchain",
    "comparator.json",
    "export-targets.txt",
    "src/Challenge.lean",
    ".gitattributes",
    ".gitmodules",
})

FORBIDDEN_PREFIXES = (
    ".github/",
    ".lake/",
    "scripts/",
    "verification/",
    "tools/",
    "ComparatorChallenges/",
)

FORBIDDEN_SUFFIXES = (
    ".olean",
    ".ilean",
    ".trace",
    ".hash",
    ".ltar",
    ".so",
    ".dll",
    ".dylib",
    ".a",
    ".o",
    ".c",
    ".h",
    ".setup.json",
)

RESERVED_TOP_MODULES = frozenset({
    "Init", "Lean", "Std", "Lake", "Mathlib", "Batteries", "Aesop",
    "Qq", "Plausible", "ProofWidgets", "LeanSearchClient", "ImportGraph", "Cli",
})

# Trojan Source / reviewer-deception BiDi & zero-width control characters
BIDI_CONTROL_RE = re.compile(
    r"[\u202a-\u202e\u2066-\u2069\u200b-\u200f\ufeff]"
)

MAX_CHANGED_FILES = 2000
MAX_SINGLE_FILE_BYTES = 32 * 1024 * 1024
MAX_TOTAL_PAYLOAD_BYTES = 256 * 1024 * 1024
MAX_VERDICT_BYTES = 64 * 1024

ALLOWED_VERDICT_KEYS = frozenset({
    "schema_version",
    "head_sha",
    "base_sha",
    "pr_number",
    "profile",
    "sandbox_id",
    "verdict",
    "build_status",
    "build_sec",
    "warnings_status",
    "comparator_status",
    "axioms",
    "tokens_before",
    "tokens_after",
    "tokens_delta",
    "tokens_delta_pct",
    "changed_files",
    "diagnostic_tail",
})


def run_cmd(
    cmd: list[str],
    *,
    timeout: int = 120,
    check: bool = True,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=check,
        env=env,
    )


def git_changed_files(bare_repo: Path, base_sha: str, head_sha: str) -> list[tuple[str, str]]:
    """Return list of (status, path) from bare git diff without touching a worktree."""
    res = run_cmd([
        "git", "--git-dir", str(bare_repo),
        "diff", "--name-status", "--no-renames", "-z", f"{base_sha}..{head_sha}",
    ])
    parts = res.stdout.decode("utf-8", errors="strict").split("\0")
    out: list[tuple[str, str]] = []
    i = 0
    while i + 1 < len(parts):
        status = parts[i]
        relpath = parts[i + 1]
        if status and relpath:
            out.append((status, relpath))
        i += 2
    return out


def git_tree_entry(bare_repo: Path, rev: str, relpath: str) -> tuple[str, str, str] | None:
    """Return (mode, obj_type, blob_sha) for relpath at rev, or None if absent."""
    res = run_cmd([
        "git", "--git-dir", str(bare_repo),
        "ls-tree", "-z", rev, "--", relpath,
    ])
    raw = res.stdout.strip(b"\0")
    if not raw:
        return None
    header, _path = raw.split(b"\t", 1)
    mode, obj_type, sha = header.decode("ascii").split(" ", 2)
    return mode, obj_type, sha


def git_cat_blob(bare_repo: Path, blob_sha: str) -> bytes:
    return run_cmd(["git", "--git-dir", str(bare_repo), "cat-file", "blob", blob_sha]).stdout


def validate_relpath(relpath: str) -> None:
    if not relpath or relpath.startswith("/") or ".." in Path(relpath).parts or "\x00" in relpath:
        raise ValueError(f"Unsafe path in PR: {relpath!r}")
    if relpath in FORBIDDEN_EXACT:
        raise ValueError(f"PR modifies protected file (requires manual maintainer audit): {relpath}")
    for pref in FORBIDDEN_PREFIXES:
        if relpath.startswith(pref):
            raise ValueError(f"PR modifies protected prefix {pref}: {relpath}")
    lower = relpath.lower()
    for suf in FORBIDDEN_SUFFIXES:
        if lower.endswith(suf):
            raise ValueError(f"PR includes forbidden binary/compiled artifact: {relpath}")
    if relpath.startswith("src/") and relpath.endswith(".lean"):
        parts = Path(relpath).parts
        if len(parts) >= 2:
            top = parts[1].removesuffix(".lean")
            if top in RESERVED_TOP_MODULES:
                raise ValueError(f"PR attempts to shadow reserved Lean module namespace: {relpath}")


def package_verified_pr_delta(
    bare_repo: Path,
    trusted_dir: Path,
    base_sha: str,
    head_sha: str,
    pr_number: int,
    out_tar: Path,
) -> dict[str, Any]:
    """Build deterministic tar.gz containing ONLY validated PR .lean deltas + trusted base config."""
    changes = git_changed_files(bare_repo, base_sha, head_sha)
    if not changes:
        raise ValueError("PR has zero changed files vs base_sha")
    if len(changes) > MAX_CHANGED_FILES:
        raise ValueError(f"PR touches {len(changes)} files (limit {MAX_CHANGED_FILES})")

    total_bytes = 0
    manifest_entries: list[dict[str, Any]] = []

    with tarfile.open(out_tar, mode="w:gz") as tf:
        # 1. Include trusted base build/verification configs (NEVER from PR!)
        for trusted_file in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "comparator.json", "export-targets.txt"):
            src_path = trusted_dir / trusted_file
            if src_path.is_file():
                data = src_path.read_bytes()
                ti = tarfile.TarInfo(name=f"trusted/{trusted_file}")
                ti.size = len(data)
                ti.mode = 0o444
                tf.addfile(ti, io.BytesIO(data))

        # 2. Extract and validate each changed file directly from git blobs
        for status, relpath in changes:
            validate_relpath(relpath)
            entry_info: dict[str, Any] = {"status": status, "path": relpath}

            if status in ("A", "M"):
                tree_meta = git_tree_entry(bare_repo, head_sha, relpath)
                if tree_meta is None:
                    raise ValueError(f"Missing blob for {relpath} at {head_sha}")
                mode, obj_type, blob_sha = tree_meta
                if obj_type != "blob" or mode not in ("100644", "100755"):
                    raise ValueError(f"Forbidden git object ({mode} {obj_type}) for {relpath}")
                blob = git_cat_blob(bare_repo, blob_sha)
                if len(blob) > MAX_SINGLE_FILE_BYTES:
                    raise ValueError(f"File exceeds {MAX_SINGLE_FILE_BYTES}B limit: {relpath}")
                total_bytes += len(blob)
                if total_bytes > MAX_TOTAL_PAYLOAD_BYTES:
                    raise ValueError(f"Total payload exceeds {MAX_TOTAL_PAYLOAD_BYTES}B limit")
                if relpath.endswith(".lean"):
                    text = blob.decode("utf-8", errors="strict")
                    if BIDI_CONTROL_RE.search(text):
                        raise ValueError(f"Forbidden BiDi/zero-width Unicode control char in {relpath}")
                ti = tarfile.TarInfo(name=f"head/{relpath}")
                ti.size = len(blob)
                ti.mode = 0o644
                tf.addfile(ti, io.BytesIO(blob))
                entry_info["head_sha256"] = hashlib.sha256(blob).hexdigest()

            if status in ("M", "D"):
                base_meta = git_tree_entry(bare_repo, base_sha, relpath)
                if base_meta is not None and base_meta[1] == "blob":
                    base_blob = git_cat_blob(bare_repo, base_meta[2])
                    ti = tarfile.TarInfo(name=f"base/{relpath}")
                    ti.size = len(base_blob)
                    ti.mode = 0o644
                    tf.addfile(ti, io.BytesIO(base_blob))
                    entry_info["base_sha256"] = hashlib.sha256(base_blob).hexdigest()

            manifest_entries.append(entry_info)

        manifest = {
            "schema_version": 1,
            "pr_number": pr_number,
            "base_sha": base_sha,
            "head_sha": head_sha,
            "files": manifest_entries,
        }
        mbytes = json.dumps(manifest, sort_keys=True, indent=2).encode("utf-8")
        ti = tarfile.TarInfo(name="manifest.json")
        ti.size = len(mbytes)
        ti.mode = 0o444
        tf.addfile(ti, io.BytesIO(mbytes))

    return manifest


def parse_last_json(stdout: bytes) -> dict[str, Any]:
    text = stdout.decode("utf-8", errors="replace").strip()
    decoder = json.JSONDecoder()
    objs: list[dict[str, Any]] = []
    idx = 0
    while idx < len(text):
        while idx < len(text) and text[idx] != "{":
            idx += 1
        if idx >= len(text):
            break
        try:
            obj, end = decoder.raw_decode(text, idx)
            if isinstance(obj, dict) and obj.get("kind") != "upgrade_available":
                objs.append(obj)
            idx = end
        except json.JSONDecodeError:
            idx += 1
    if not objs:
        raise RuntimeError(f"No JSON object found in CLI output: {text[:400]}")
    return objs[-1]


def bohr_create_zero_token_sandbox(
    bohr_bin: str,
    template: str,
    project_id: str,
    timeout_sec: int,
    wenyon_dataset_id: str | None,
    wenyon_version: str | None,
) -> str:
    """Create a zero-token, zero-user-storage Bohrium Sandbox from a pre-published template."""
    cmd = [
        bohr_bin, "sandbox", "create", template,
        "--project-id", str(project_id),
        "--timeout", str(timeout_sec),
        "-o", "json",
    ]
    # STRICT SECURITY INVARIANTS:
    #   - NEVER pass --inherit-auth
    #   - NEVER pass --mount-user-storage or --share-subpath
    #   - NEVER pass --env containing any GitHub/Bohrium secrets
    if wenyon_dataset_id and wenyon_version:
        cmd.extend([
            "--wenyon-dataset-id", wenyon_dataset_id,
            "--wenyon-mount-path", "/mnt/lean-cache",
            "--wenyon-mode", "read",
            "--wenyon-version", wenyon_version,
        ])
    res = run_cmd(cmd, timeout=180)
    payload = parse_last_json(res.stdout)
    sid = payload.get("sandboxID") or payload.get("sandbox_id") or payload.get("id")
    if not sid:
        raise RuntimeError(f"bohr sandbox create did not return sandbox_id: {payload}")
    return str(sid)


def bohr_delete_sandbox(bohr_bin: str, sandbox_id: str) -> None:
    try:
        run_cmd([bohr_bin, "sandbox", "delete", sandbox_id, "--yes"], timeout=60, check=False)
    except Exception as exc:
        print(f"[warn] failed to delete sandbox {sandbox_id}: {exc}", file=sys.stderr)


def validate_verdict_schema(
    raw_bytes: bytes,
    expected_head_sha: str,
    expected_pr_number: int,
    profile: str,
    sandbox_id: str,
) -> dict[str, Any]:
    if len(raw_bytes) > MAX_VERDICT_BYTES:
        raise ValueError(f"verdict.json exceeds {MAX_VERDICT_BYTES} bytes")
    data = json.loads(raw_bytes.decode("utf-8", errors="strict"))
    if not isinstance(data, dict):
        raise ValueError("verdict.json must be a JSON object")
    extra = set(data.keys()) - ALLOWED_VERDICT_KEYS
    if extra:
        raise ValueError(f"Unexpected keys in verdict.json: {sorted(extra)}")
    if data.get("head_sha") != expected_head_sha:
        raise ValueError(f"Verdict head_sha mismatch: {data.get('head_sha')} != {expected_head_sha}")
    if int(data.get("pr_number", -1)) != expected_pr_number:
        raise ValueError("Verdict pr_number mismatch")
    if data.get("verdict") not in ("pass", "fail", "infra_error"):
        raise ValueError(f"Invalid verdict enum: {data.get('verdict')!r}")
    data["profile"] = profile
    data["sandbox_id"] = sandbox_id
    return data


def main() -> int:
    ap = argparse.ArgumentParser(description="Zero-token Bohrium Sandbox PR verifier dispatcher")
    ap.add_argument("--bare-repo", type=Path, required=True)
    ap.add_argument("--trusted-dir", type=Path, required=True)
    ap.add_argument("--base-sha", required=True)
    ap.add_argument("--head-sha", required=True)
    ap.add_argument("--pr-number", type=int, required=True)
    ap.add_argument("--template", required=True)
    ap.add_argument("--project-id", required=True)
    ap.add_argument("--timeout-sec", type=int, default=3600)
    ap.add_argument("--run-comparator", action="store_true")
    ap.add_argument("--bohr-bin", default=shutil.which("bohr") or "bohr")
    ap.add_argument("--verdict-out", type=Path, required=True)
    ap.add_argument("--dry-run", action="store_true", help="Validate & package PR delta without creating sandbox")
    args = ap.parse_args()

    with tempfile.TemporaryDirectory(prefix="bohrium-dispatch-") as td:
        payload_tar = Path(td) / "payload.tar.gz"
        manifest = package_verified_pr_delta(
            args.bare_repo,
            args.trusted_dir,
            args.base_sha,
            args.head_sha,
            args.pr_number,
            payload_tar,
        )
        payload_sha = hashlib.sha256(payload_tar.read_bytes()).hexdigest()
        print(
            f"[dispatch] packaged {len(manifest['files'])} verified files "
            f"({payload_tar.stat().st_size} bytes, sha256={payload_sha[:16]})"
        )
        if args.dry_run:
            return 0

        sandbox_id: str | None = None
        try:
            sandbox_id = bohr_create_zero_token_sandbox(
                args.bohr_bin,
                args.template,
                args.project_id,
                args.timeout_sec,
                os.environ.get("WENYON_CACHE_DATASET_ID") or None,
                os.environ.get("WENYON_CACHE_VERSION") or None,
            )
            print(f"[dispatch] sandbox ready: {sandbox_id}")

            # Upload verified payload tarball
            run_cmd([
                args.bohr_bin, "sandbox", "files", "write",
                sandbox_id, "/tmp/pr-payload.tar.gz",
                "--source", str(payload_tar),
            ], timeout=300)

            # Execute baked-in trusted verifier as container root (it drops into bwrap UID 65534)
            comp_flag = "--run-comparator" if args.run_comparator else ""
            verify_cmd = (
                f"python3 /opt/openverify-lean/bin/verify_pr_in_sandbox.py "
                f"--payload /tmp/pr-payload.tar.gz "
                f"--expected-sha256 {payload_sha} "
                f"--verdict-out /out/verdict.json {comp_flag}"
            )
            exec_res = run_cmd([
                args.bohr_bin, "sandbox", "exec", sandbox_id,
                "--user", "root",
                "--command", verify_cmd,
                "-o", "json",
            ], timeout=args.timeout_sec + 120, check=False)
            print(f"[dispatch] verifier exec rc={exec_res.returncode}")

            # Pull bounded JSON verdict
            read_res = run_cmd([
                args.bohr_bin, "sandbox", "files", "read",
                sandbox_id, "/out/verdict.json",
            ], timeout=60)
            verdict = validate_verdict_schema(
                read_res.stdout,
                args.head_sha,
                args.pr_number,
                args.template,
                sandbox_id,
            )
            args.verdict_out.write_text(json.dumps(verdict, indent=2) + "\n", encoding="utf-8")
            return 0 if verdict["verdict"] == "pass" else 1
        finally:
            if sandbox_id:
                print(f"[dispatch] destroying sandbox {sandbox_id}")
                bohr_delete_sandbox(args.bohr_bin, sandbox_id)


if __name__ == "__main__":
    raise SystemExit(main())
