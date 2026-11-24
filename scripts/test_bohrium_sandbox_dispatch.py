#!/usr/bin/env python3
"""Unit tests for scripts/bohrium_sandbox_dispatch.py security invariants."""
from __future__ import annotations

import json
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import bohrium_sandbox_dispatch as bsd  # noqa: E402


class TestBohriumSandboxDispatch(unittest.TestCase):
    def test_validate_relpath_guards(self) -> None:
        # Allowed Lean & community paths
        bsd.validate_relpath("src/Formalism/ZetaNonvanishing/ZetaLandau.lean")
        bsd.validate_relpath("community/core6-attempt-99242/Solution.lean")

        # Forbidden exact files, prefixes, binary suffixes, path traversal, namespace shadowing
        bad_paths = [
            "../escape.lean",
            "/etc/passwd",
            "lakefile.toml",
            "lean-toolchain",
            "lake-manifest.json",
            "src/Challenge.lean",
            ".github/workflows/bohrium-verify.yml",
            "scripts/bohrium_sandbox_dispatch.py",
            "src/Foo.olean",
            "src/Mathlib.lean",
            "src/Lean/Hijack.lean",
        ]
        for bp in bad_paths:
            with self.assertRaises(ValueError, msg=f"Expected rejection for {bp}"):
                bsd.validate_relpath(bp)

    def test_validate_verdict_schema(self) -> None:
        good = json.dumps({
            "schema_version": 1,
            "head_sha": "a" * 40,
            "base_sha": "b" * 40,
            "pr_number": 7,
            "verdict": "pass",
            "build_status": "ok",
            "build_sec": 42.5,
            "warnings_status": "ok",
            "comparator_status": "ok",
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
            "tokens_before": 1000,
            "tokens_after": 400,
            "tokens_delta": -600,
            "tokens_delta_pct": -60.0,
            "changed_files": ["community/core6-attempt-99242/Solution.lean"],
            "diagnostic_tail": "",
        }).encode("utf-8")
        v = bsd.validate_verdict_schema(good, "a" * 40, 7, "core-lean4341-c8m32", "sbx-123")
        self.assertEqual(v["verdict"], "pass")
        self.assertEqual(v["sandbox_id"], "sbx-123")

        # Reject unexpected keys & SHA mismatch
        with self.assertRaises(ValueError):
            bsd.validate_verdict_schema(good, "c" * 40, 7, "core-lean4341-c8m32", "sbx-123")
        bad_extra = json.dumps({"head_sha": "a" * 40, "pr_number": 7, "verdict": "pass", "evil": 1}).encode()
        with self.assertRaises(ValueError):
            bsd.validate_verdict_schema(bad_extra, "a" * 40, 7, "core-lean4341-c8m32", "sbx-123")

    def test_package_bare_repo_blocks_bidi_and_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            work = root / "work"
            work.mkdir()
            env = {
                "GIT_AUTHOR_NAME": "Test",
                "GIT_AUTHOR_EMAIL": "t@example.com",
                "GIT_COMMITTER_NAME": "Test",
                "GIT_COMMITTER_EMAIL": "t@example.com",
            }
            subprocess.run(["git", "init", "-q"], cwd=work, check=True)
            (work / "lean-toolchain").write_text("leanprover/lean4:v4.36.0\n", encoding="utf-8")
            (work / "src").mkdir()
            (work / "src" / "Demo.lean").write_text("theorem t : True := trivial\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=work, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "base"], cwd=work, check=True, env=env)
            base_sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=work, text=True).strip()

            # Clean PR commit
            (work / "src" / "Demo.lean").write_text("theorem t : True := by trivial\n", encoding="utf-8")
            subprocess.run(["git", "commit", "-q", "-am", "clean"], cwd=work, check=True, env=env)
            clean_sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=work, text=True).strip()

            out_tar = root / "clean.tar.gz"
            manifest = bsd.package_verified_pr_delta(work / ".git", work, base_sha, clean_sha, 9, out_tar)
            self.assertEqual(len(manifest["files"]), 1)
            with tarfile.open(out_tar, "r:gz") as tf:
                names = set(tf.getnames())
                self.assertIn("head/src/Demo.lean", names)
                self.assertIn("base/src/Demo.lean", names)
                self.assertIn("trusted/lean-toolchain", names)

            # BiDi Trojan-Source commit must fail
            (work / "src" / "Demo.lean").write_text("theorem t : True := trivial -- \u202e evil\n", encoding="utf-8")
            subprocess.run(["git", "commit", "-q", "-am", "bidi"], cwd=work, check=True, env=env)
            bidi_sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=work, text=True).strip()
            with self.assertRaises(ValueError):
                bsd.package_verified_pr_delta(work / ".git", work, base_sha, bidi_sha, 9, root / "bidi.tar.gz")

            # Symlink commit must fail
            subprocess.run(["git", "checkout", "-q", base_sha], cwd=work, check=True)
            (work / "src" / "Link.lean").symlink_to("/etc/passwd")
            subprocess.run(["git", "add", "src/Link.lean"], cwd=work, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "symlink"], cwd=work, check=True, env=env)
            sym_sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=work, text=True).strip()
            with self.assertRaises(ValueError):
                bsd.package_verified_pr_delta(work / ".git", work, base_sha, sym_sha, 9, root / "sym.tar.gz")

    def test_parse_last_json_skips_upgrade_banner(self) -> None:
        raw = b'{"kind":"upgrade_available","latest":"2.9.55"}\n{"sandboxID":"sbx-abc"}\n'
        parsed = bsd.parse_last_json(raw)
        self.assertEqual(parsed["sandboxID"], "sbx-abc")


if __name__ == "__main__":
    unittest.main()
