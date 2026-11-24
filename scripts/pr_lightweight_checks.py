#!/usr/bin/env python3
"""Lightweight PR static & token-delta checks for Osgood001/riemann-hypothesis.

Designed to run in seconds on ubuntu-latest with zero Lean compilation and a
partial/sparse git clone (--filter=blob:none). Performs:
  1. Scan changed/added .lean files for `sorry`, `admit`, `sorryAx`, and custom `axiom` declarations.
  2. Compute exact Playground-compatible `TOKEN_RE` normalized token counts and
     character/line deltas on changed .lean files (comment/import-stripped).
  3. Guard `lean-toolchain` and `lake-manifest.json` against accidental modification.
  4. Render a GitHub Markdown summary (for $GITHUB_STEP_SUMMARY and sticky PR comment).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable

# Exact normalized tokenizer matching Playground verifier / ops/rh-board/board_data.py
TOKEN_RE = re.compile(
    r'"(?:\\.|[^"\\])*"'
    r"|'(?:\\.|[^'\\])'"
    r"|[0-9]+(?:\.[0-9]+)?"
    r"|(?:<;>|:=|=>|->|\.\.\.|\.\.|::|<=|>=|!=|&&|\|\||[→↔≤≥≠⊢⟨⟩∀∃λ↦∧∨¬∈∉⊆∪∩∑∏∫‖⁻¹])"
    r"|[A-Za-z_\u00c0-\u024f\u0370-\u03ff\u1d00-\u1fff\u2100-\u214f\U0001d400-\U0001d7ff]"
    r"[A-Za-z0-9_'₀-₉⁰-⁹\u00c0-\u024f\u0370-\u03ff\u1d00-\u1fff\u2100-\u214f\U0001d400-\U0001d7ff]*"
    r"|[^\s]"
)

_OUTER_SCAN_RE = re.compile(r'"(?:\\[\s\S]|[^"\\])*(?:"|\\?$)|/-|--[^\n]*')
_INNER_SCAN_RE = re.compile(r'/-|-/')
_IMPORT_LINE_RE = re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+')

# Identifier-bounded hazard regexes applied after stripping comments & masking string literals
_SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")
_ADMIT_RE = re.compile(r"(?<![A-Za-z0-9_'])admit(?![A-Za-z0-9_'])")
_SORRY_AX_RE = re.compile(r"(?<![A-Za-z0-9_'])sorryAx(?![A-Za-z0-9_'])")
_AXIOM_DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|local|noncomputable|unsafe)\s+)*axiom\s+([A-Za-z_][A-Za-z0-9_.']*)",
    flags=re.MULTILINE,
)

PROTECTED_TOOLCHAIN_FILES = ("lean-toolchain", "lake-manifest.json")
WATCHED_BUILD_FILES = ("lakefile.toml", "comparator.json")
STICKY_MARKER = "<!-- rh-pr-lightweight-checks -->"


@dataclass
class HazardHit:
    kind: str
    line: int
    detail: str


@dataclass
class LeanFileMetrics:
    path: str
    status: str  # A, M, D, R
    old_path: str | None = None
    base_tokens: int = 0
    head_tokens: int = 0
    base_chars: int = 0
    head_chars: int = 0
    base_lines: int = 0
    head_lines: int = 0
    sorry_hits: list[HazardHit] = field(default_factory=list)
    admit_hits: list[HazardHit] = field(default_factory=list)
    sorry_ax_hits: list[HazardHit] = field(default_factory=list)
    axiom_hits: list[HazardHit] = field(default_factory=list)

    @property
    def delta_tokens(self) -> int:
        return self.head_tokens - self.base_tokens

    @property
    def delta_chars(self) -> int:
        return self.head_chars - self.base_chars

    @property
    def delta_lines(self) -> int:
        return self.head_lines - self.base_lines

    @property
    def has_hazards(self) -> bool:
        return bool(self.sorry_hits or self.admit_hits or self.sorry_ax_hits or self.axiom_hits)


def strip_lean_comments(code: str, *, mask_strings: bool = False) -> str:
    """Strip Lean 4 line (`--`) and nested block (`/- ... -/`) comments.

    Preserves newline counts so line numbers remain accurate for diagnostics.
    When `mask_strings=True`, string literals are replaced with newline-preserving
    spaces so hazard regexes do not false-positive on string contents.
    """
    out: list[str] = []
    pos = 0
    n = len(code)
    depth = 0
    while pos < n:
        if depth == 0:
            m = _OUTER_SCAN_RE.search(code, pos)
            if not m:
                out.append(code[pos:])
                break
            if m.start() > pos:
                out.append(code[pos:m.start()])
            tok = m.group(0)
            if tok == "/-":
                depth = 1
            elif tok.startswith('"'):
                if mask_strings:
                    out.append("\n" * tok.count("\n"))
                else:
                    out.append(tok)
            # Single-line `--` comment is dropped (its trailing \n is not matched)
            pos = m.end()
        else:
            m = _INNER_SCAN_RE.search(code, pos)
            if not m:
                if pos < n:
                    out.append("\n" * code.count("\n", pos))
                break
            if m.start() > pos:
                out.append("\n" * code.count("\n", pos, m.start()))
            depth += 1 if m.group(0) == "/-" else -1
            pos = m.end()
    return "".join(out)


def count_normalized_tokens(code: str) -> int:
    """Count normalized Lean 4 tokens matching Playground's anti-golf TOKEN_RE."""
    clean = strip_lean_comments(code or "", mask_strings=False)
    body_lines = [ln for ln in clean.splitlines() if not _IMPORT_LINE_RE.match(ln)]
    return len(TOKEN_RE.findall("\n".join(body_lines)))


def scan_lean_hazards(code: str) -> tuple[list[HazardHit], list[HazardHit], list[HazardHit], list[HazardHit]]:
    """Scan comment- and string-masked Lean 4 code for sorry/admit/sorryAx/custom axiom."""
    masked = strip_lean_comments(code or "", mask_strings=True)
    raw_lines = (code or "").splitlines()
    masked_lines = masked.splitlines()

    sorry_hits: list[HazardHit] = []
    admit_hits: list[HazardHit] = []
    sorry_ax_hits: list[HazardHit] = []
    axiom_hits: list[HazardHit] = []

    for idx, mline in enumerate(masked_lines, start=1):
        snippet = raw_lines[idx - 1].strip()[:120] if idx - 1 < len(raw_lines) else mline.strip()[:120]
        if _SORRY_RE.search(mline):
            sorry_hits.append(HazardHit(kind="sorry", line=idx, detail=snippet))
        if _ADMIT_RE.search(mline):
            admit_hits.append(HazardHit(kind="admit", line=idx, detail=snippet))
        if _SORRY_AX_RE.search(mline):
            sorry_ax_hits.append(HazardHit(kind="sorryAx", line=idx, detail=snippet))

    for m in _AXIOM_DECL_RE.finditer(masked):
        line_no = masked.count("\n", 0, m.start()) + 1
        axiom_hits.append(HazardHit(kind="axiom", line=line_no, detail=m.group(1)))

    return sorry_hits, admit_hits, sorry_ax_hits, axiom_hits


def check_toolchain_guard(
    changed_paths: Iterable[str],
    *,
    allow_toolchain_change: bool = False,
) -> dict[str, object]:
    """Flag modifications to pinned toolchain/manifest files unless explicitly allowed."""
    changed_set = set(changed_paths)
    touched_protected = [p for p in PROTECTED_TOOLCHAIN_FILES if p in changed_set]
    touched_watched = [p for p in WATCHED_BUILD_FILES if p in changed_set]
    failed = bool(touched_protected) and not allow_toolchain_change
    return {
        "protected_touched": touched_protected,
        "watched_touched": touched_watched,
        "allow_toolchain_change": allow_toolchain_change,
        "passed": not failed,
    }


def _run_git(args: list[str], cwd: Path) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed ({proc.returncode}): {proc.stderr.strip()}")
    return proc.stdout


def _git_show_optional(ref: str, rel_path: str, cwd: Path) -> str:
    proc = subprocess.run(
        ["git", "show", f"{ref}:{rel_path}"],
        cwd=str(cwd),
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        return ""
    return proc.stdout.decode("utf-8", errors="replace")


def parse_name_status(diff_output: str) -> list[tuple[str, str, str | None]]:
    """Parse `git diff --name-status -z` output into (status_code, path, old_path)."""
    parts = diff_output.split("\0")
    entries: list[tuple[str, str, str | None]] = []
    i = 0
    while i < len(parts):
        st = parts[i]
        if not st:
            i += 1
            continue
        code = st[0]
        if code in ("R", "C"):
            if i + 2 >= len(parts):
                break
            old_path, new_path = parts[i + 1], parts[i + 2]
            entries.append((code, new_path, old_path))
            i += 3
        else:
            if i + 1 >= len(parts):
                break
            path = parts[i + 1]
            entries.append((code, path, None))
            i += 2
    return entries


def analyze_git_diff(
    repo_root: Path,
    base_ref: str,
    head_ref: str,
    *,
    allow_toolchain_change: bool = False,
) -> dict[str, object]:
    """Analyze changed files between base_ref and head_ref."""
    raw_status = _run_git(["diff", "--name-status", "-z", base_ref, head_ref], repo_root)
    changes = parse_name_status(raw_status)

    all_paths: list[str] = []
    for code, path, old_path in changes:
        all_paths.append(path)
        if old_path:
            all_paths.append(old_path)

    toolchain = check_toolchain_guard(all_paths, allow_toolchain_change=allow_toolchain_change)

    lean_metrics: list[LeanFileMetrics] = []
    for code, path, old_path in changes:
        is_lean = path.endswith(".lean") or (old_path is not None and old_path.endswith(".lean"))
        if not is_lean:
            continue

        base_code = ""
        head_code = ""
        if code != "A":
            src_path = old_path if old_path else path
            if src_path.endswith(".lean"):
                base_code = _git_show_optional(base_ref, src_path, repo_root)
        if code != "D" and path.endswith(".lean"):
            head_code = _git_show_optional(head_ref, path, repo_root)

        sorry_h, admit_h, sorry_ax_h, axiom_h = ([], [], [], [])
        if head_code:
            sorry_h, admit_h, sorry_ax_h, axiom_h = scan_lean_hazards(head_code)

        lean_metrics.append(
            LeanFileMetrics(
                path=path,
                status=code,
                old_path=old_path,
                base_tokens=count_normalized_tokens(base_code) if base_code else 0,
                head_tokens=count_normalized_tokens(head_code) if head_code else 0,
                base_chars=len(base_code),
                head_chars=len(head_code),
                base_lines=len(base_code.splitlines()) if base_code else 0,
                head_lines=len(head_code.splitlines()) if head_code else 0,
                sorry_hits=sorry_h,
                admit_hits=admit_h,
                sorry_ax_hits=sorry_ax_h,
                axiom_hits=axiom_h,
            )
        )

    total_sorry = sum(len(m.sorry_hits) for m in lean_metrics)
    total_admit = sum(len(m.admit_hits) for m in lean_metrics)
    total_sorry_ax = sum(len(m.sorry_ax_hits) for m in lean_metrics)
    total_axioms = sum(len(m.axiom_hits) for m in lean_metrics)

    totals = {
        "changed_files": len(changes),
        "changed_lean_files": len(lean_metrics),
        "base_tokens": sum(m.base_tokens for m in lean_metrics),
        "head_tokens": sum(m.head_tokens for m in lean_metrics),
        "delta_tokens": sum(m.delta_tokens for m in lean_metrics),
        "base_chars": sum(m.base_chars for m in lean_metrics),
        "head_chars": sum(m.head_chars for m in lean_metrics),
        "delta_chars": sum(m.delta_chars for m in lean_metrics),
        "base_lines": sum(m.base_lines for m in lean_metrics),
        "head_lines": sum(m.head_lines for m in lean_metrics),
        "delta_lines": sum(m.delta_lines for m in lean_metrics),
        "sorry_count": total_sorry,
        "admit_count": total_admit,
        "sorry_ax_count": total_sorry_ax,
        "custom_axiom_count": total_axioms,
    }

    hazards_passed = (total_sorry + total_admit + total_sorry_ax + total_axioms) == 0
    overall_passed = hazards_passed and bool(toolchain["passed"])

    return {
        "base_ref": base_ref,
        "head_ref": head_ref,
        "overall_passed": overall_passed,
        "hazards_passed": hazards_passed,
        "toolchain": toolchain,
        "totals": totals,
        "lean_files": [
            {
                **asdict(m),
                "delta_tokens": m.delta_tokens,
                "delta_chars": m.delta_chars,
                "delta_lines": m.delta_lines,
            }
            for m in lean_metrics
        ],
    }


def _fmt_signed(n: int) -> str:
    return f"+{n:,}" if n > 0 else f"{n:,}"


def render_markdown_report(result: dict[str, object], *, max_rows: int = 30) -> str:
    """Render a concise GitHub Markdown summary suitable for Step Summary & PR comment."""
    totals: dict[str, int] = result["totals"]  # type: ignore[assignment]
    toolchain: dict[str, object] = result["toolchain"]  # type: ignore[assignment]
    lean_files: list[dict[str, object]] = result["lean_files"]  # type: ignore[assignment]

    status_badge = "✅ PASS" if result["overall_passed"] else "❌ FAIL"
    hazard_badge = "✅ Clean (0 sorry / 0 admit / 0 custom axiom)" if result["hazards_passed"] else "❌ Hazards detected"
    if toolchain["passed"]:
        if toolchain["protected_touched"]:
            tc_badge = f"⚠️ Allowed via label/override ({', '.join(toolchain['protected_touched'])})"  # type: ignore[arg-type]
        else:
            tc_badge = "✅ Unchanged (`lean-toolchain`, `lake-manifest.json`)"
    else:
        tc_badge = f"❌ Unexpected change: {', '.join(f'`{p}`' for p in toolchain['protected_touched'])}"  # type: ignore[union-attr]

    lines: list[str] = [
        STICKY_MARKER,
        f"## Lightweight PR Checks — {status_badge}",
        "",
        "> Fast static check on `ubuntu-latest` (no `lake build`). Full Lean verification runs on gated self-hosted/Bohrium runners.",
        "",
        "| Check | Status |",
        "|---|---|",
        f"| **Proof completeness (`sorry` / `admit` / `sorryAx` / custom `axiom`)** | {hazard_badge} |",
        f"| **Toolchain & manifest guard** | {tc_badge} |",
        f"| **Changed `.lean` files** | `{totals['changed_lean_files']}` (out of `{totals['changed_files']}` total changed files) |",
        f"| **Normalized tokens (`TOKEN_RE`)** | `{totals['head_tokens']:,}` (base `{totals['base_tokens']:,}`, Δ `{_fmt_signed(totals['delta_tokens'])}`) |",
        f"| **Characters / Lines** | `{totals['head_chars']:,}` chars (Δ `{_fmt_signed(totals['delta_chars'])}`) · `{totals['head_lines']:,}` lines (Δ `{_fmt_signed(totals['delta_lines'])}`) |",
        "",
    ]

    if toolchain["watched_touched"]:
        watched_str = ", ".join(f"`{p}`" for p in toolchain["watched_touched"])  # type: ignore[union-attr]
        lines.append(f"> [!NOTE]\n> Build/verifier config modified: {watched_str}. Review carefully before running full verification.\n")

    if not toolchain["passed"]:
        lines.append(
            "> [!CAUTION]\n"
            "> `lean-toolchain` or `lake-manifest.json` was modified. Add the `allow-toolchain-change` PR label "
            "if this bump is intentional.\n"
        )

    # Hazard details section
    hazard_rows: list[str] = []
    for f in lean_files:
        for field_name in ("sorry_hits", "admit_hits", "sorry_ax_hits", "axiom_hits"):
            for hit in f[field_name]:  # type: ignore[index]
                detail = str(hit["detail"]).replace("|", "\\|").replace("`", "'")
                hazard_rows.append(f"| `{f['path']}` | `{hit['line']}` | `{hit['kind']}` | `{detail}` |")

    if hazard_rows:
        lines.extend([
            "### ❌ Detected Proof Hazards",
            "",
            "| File | Line | Kind | Snippet / Name |",
            "|---|---:|---|---|",
            *hazard_rows[:50],
            "",
        ])
        if len(hazard_rows) > 50:
            lines.append(f"_…and {len(hazard_rows) - 50} additional hazard(s) truncated._\n")

    # Per-file token/char/line delta table
    if lean_files:
        lines.extend([
            "### Changed `.lean` Files (`TOKEN_RE` Normalized Delta)",
            "",
            "| Status | File | Tokens (Δ) | Chars (Δ) | Lines (Δ) | Hazards |",
            "|---|---|---:|---:|---:|---|",
        ])
        for f in lean_files[:max_rows]:
            hz_cnt = (
                len(f["sorry_hits"])  # type: ignore[arg-type]
                + len(f["admit_hits"])  # type: ignore[arg-type]
                + len(f["sorry_ax_hits"])  # type: ignore[arg-type]
                + len(f["axiom_hits"])  # type: ignore[arg-type]
            )
            hz_str = "✅ 0" if hz_cnt == 0 else f"❌ {hz_cnt}"
            dt = int(f["delta_tokens"])  # type: ignore[arg-type]
            bt = int(f["base_tokens"])  # type: ignore[arg-type]
            pct_str = f" ({(dt / bt) * 100:+.1f}%)" if bt > 0 and f["status"] == "M" else ""
            lines.append(
                f"| `{f['status']}` | `{f['path']}` | "
                f"`{f['head_tokens']:,}` ({_fmt_signed(dt)}{pct_str}) | "
                f"`{f['head_chars']:,}` ({_fmt_signed(int(f['delta_chars']))}) | "
                f"`{f['head_lines']:,}` ({_fmt_signed(int(f['delta_lines']))}) | {hz_str} |"
            )
        if len(lean_files) > max_rows:
            lines.append(f"| … | _{len(lean_files) - max_rows} more `.lean` file(s) omitted_ | | | | |")
        lines.append("")
    else:
        lines.append("_No `.lean` files changed in this diff._\n")

    lines.append(
        f"<sub>Compare `{str(result['base_ref'])[:12]}..{str(result['head_ref'])[:12]}` · "
        "Tokenizer: Playground `TOKEN_RE` (comments & imports stripped).</sub>"
    )
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Lightweight PR Lean static & TOKEN_RE delta checker.")
    parser.add_argument("--repo", type=Path, default=Path("."), help="Path to git repository root.")
    parser.add_argument("--base", required=True, help="Base git ref/SHA.")
    parser.add_argument("--head", default="HEAD", help="Head git ref/SHA.")
    parser.add_argument(
        "--allow-toolchain-change",
        action="store_true",
        default=os.environ.get("ALLOW_TOOLCHAIN_CHANGE", "").lower() in ("1", "true", "yes"),
        help="Allow changes to lean-toolchain and lake-manifest.json.",
    )
    parser.add_argument("--markdown-out", type=Path, default=None, help="Write Markdown report to this path.")
    parser.add_argument("--json-out", type=Path, default=None, help="Write JSON report to this path.")
    parser.add_argument(
        "--no-fail",
        action="store_true",
        help="Always exit 0 after generating reports (caller inspects JSON overall_passed).",
    )
    args = parser.parse_args(argv)

    result = analyze_git_diff(
        args.repo.resolve(),
        args.base,
        args.head,
        allow_toolchain_change=args.allow_toolchain_change,
    )
    md = render_markdown_report(result)

    if args.markdown_out is not None:
        args.markdown_out.parent.mkdir(parents=True, exist_ok=True)
        args.markdown_out.write_text(md, encoding="utf-8")

    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    step_summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if step_summary:
        with open(step_summary, "a", encoding="utf-8") as fh:
            fh.write(md)
            fh.write("\n")

    sys.stdout.write(md)

    if not args.no_fail and not result["overall_passed"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
