# Core Pillar 13/13 — Hermitian Curvature Lattice Box Sum, Sharp Recursion & Principal Minor Count (Playground Attempt #99274)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 13/13 — Hermitian Curvature Box Bounds](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-13-hermitian-cu-6e1ac05a) |
| **Module Family** | `Formalism/HermitianCurvature` |
| **Attempt ID** | `#99274` |
| **Playground Score** | `60.55` |
| **Normalized Tokens (`TOKEN_RE`)** | `4,072` vs baseline `13,949` (**-70.81%**, `3.43×` smaller) |
| **Characters / Lines / Files** | `14,620` chars vs `44,176` (**-66.91%**) · `266` lines · `1` `.lean` file(s) vs `6` baseline files |
| **Frozen Challenge Definitions** | 1 (`Formalism.HermitianCurvature.Statement`) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore13.hermitianCurvatureBounds :
    Formalism.FourierDecayAlt.BoxSumOne ∧
    Formalism.FourierDecayAlt.RecursionSharp ∧
    Formalism.FourierDecayAlt.LeadingMinorsCount
```

### Proof Simplification Highlights
Refactors the core argument around Mathlib lemma(s) rpow_lt_rpow_of_exponent_gt, norm_num; driven by `simp, linarith, nlinarith`.

## Corresponding Target Modules in `src/`

- `src/Formalism/HermitianCurvature/Statement.lean` (`Formalism.FourierDecayAlt.BoxSumOne`, `RecursionSharp`, `LeadingMinorsCount`)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core13-attempt-99274/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 13/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore13`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Proof already imports `Formalism.HermitianCurvature.Statement` directly and collapses 6 files into 1 concise file.
- Port from standalone `import Mathlib` (Lean `v4.34.1`) to Lean `v4.36.0` `module` / `public import` / `@[expose] public section` with `autoImplicit = false`.
- Re-export `BoxSumOne`, `RecursionSharp`, and `LeadingMinorsCount` for downstream `Formalism/HermitianCurvature/` modules.
