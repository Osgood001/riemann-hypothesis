#!/usr/bin/env python3
"""Unit tests for scripts/pr_lightweight_checks.py."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pr_lightweight_checks as plc  # noqa: E402


class TestLightweightChecks(unittest.TestCase):
    def test_strip_comments_nested_and_strings(self) -> None:
        src = (
            'import Mathlib\n'
            '-- sorry admit axiom Fake\n'
            '/- outer comment\n'
            '   /- nested sorry -/\n'
            '   still comment admit\n'
            '-/\n'
            'def msg := "string with -- sorry and /- admit -/"\n'
            'theorem ok (x : ℕ) : x = x := rfl\n'
        )
        clean = plc.strip_lean_comments(src, mask_strings=False)
        self.assertIn('"string with -- sorry and /- admit -/"', clean)
        self.assertNotIn("outer comment", clean)
        self.assertNotIn("Fake", clean)
        # Line count is preserved
        self.assertEqual(len(clean.splitlines()), len(src.splitlines()))

        s, a, sax, ax = plc.scan_lean_hazards(src)
        self.assertEqual((s, a, sax, ax), ([], [], [], []))

    def test_token_count_strips_imports_and_comments(self) -> None:
        src = (
            "module\n"
            "public import Mathlib\n"
            "private import Foo.Bar\n"
            "import Baz\n"
            "-- ignored comment\n"
            "theorem foo (x : ℝ) : x ≤ x := by\n"
            "  rfl\n"
        )
        # Tokens: module, theorem, foo, (, x, :, ℝ, ), :, x, ≤, x, :=, by, rfl => 15
        self.assertEqual(plc.count_normalized_tokens(src), 15)

    def test_hazard_detection_positive_and_word_boundaries(self) -> None:
        src = (
            "def sorry_free_helper := 1\n"
            "def admitted_ok := 2\n"
            "private axiom badAxiom : False\n"
            "theorem t1 : True := by sorry\n"
            "theorem t2 : True := by admit\n"
            "theorem t3 : False := sorryAx False false\n"
        )
        s, a, sax, ax = plc.scan_lean_hazards(src)
        self.assertEqual([h.line for h in s], [4])
        self.assertEqual([h.line for h in a], [5])
        self.assertEqual([h.line for h in sax], [6])
        self.assertEqual([(h.line, h.detail) for h in ax], [(3, "badAxiom")])

    def test_toolchain_guard(self) -> None:
        r_clean = plc.check_toolchain_guard(["community/core1/Solution.lean"])
        self.assertTrue(r_clean["passed"])
        self.assertEqual(r_clean["protected_touched"], [])

        r_fail = plc.check_toolchain_guard(["lean-toolchain", "src/Main.lean"])
        self.assertFalse(r_fail["passed"])
        self.assertEqual(r_fail["protected_touched"], ["lean-toolchain"])

        r_allow = plc.check_toolchain_guard(
            ["lean-toolchain", "lake-manifest.json"],
            allow_toolchain_change=True,
        )
        self.assertTrue(r_allow["passed"])
        self.assertEqual(r_allow["protected_touched"], ["lean-toolchain", "lake-manifest.json"])

    def test_markdown_rendering(self) -> None:
        result = {
            "base_ref": "aaaaaaa1111111",
            "head_ref": "bbbbbbb2222222",
            "overall_passed": True,
            "hazards_passed": True,
            "toolchain": {
                "protected_touched": [],
                "watched_touched": [],
                "allow_toolchain_change": False,
                "passed": True,
            },
            "totals": {
                "changed_files": 2,
                "changed_lean_files": 1,
                "base_tokens": 1000,
                "head_tokens": 400,
                "delta_tokens": -600,
                "base_chars": 4000,
                "head_chars": 1500,
                "delta_chars": -2500,
                "base_lines": 120,
                "head_lines": 50,
                "delta_lines": -70,
                "sorry_count": 0,
                "admit_count": 0,
                "sorry_ax_count": 0,
                "custom_axiom_count": 0,
            },
            "lean_files": [
                {
                    "path": "community/core1/Solution.lean",
                    "status": "M",
                    "old_path": None,
                    "base_tokens": 1000,
                    "head_tokens": 400,
                    "delta_tokens": -600,
                    "base_chars": 4000,
                    "head_chars": 1500,
                    "delta_chars": -2500,
                    "base_lines": 120,
                    "head_lines": 50,
                    "delta_lines": -70,
                    "sorry_hits": [],
                    "admit_hits": [],
                    "sorry_ax_hits": [],
                    "axiom_hits": [],
                }
            ],
        }
        md = plc.render_markdown_report(result)
        self.assertIn(plc.STICKY_MARKER, md)
        self.assertIn("✅ PASS", md)
        self.assertIn("-600", md)
        self.assertIn("-60.0%", md)


if __name__ == "__main__":
    unittest.main()
