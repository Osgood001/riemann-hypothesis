# Core Pillar 3/13 — Truncated Explicit Formula for Dirichlet L-Functions (Playground Attempt #99125)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 3/13 — Truncated Explicit Formula](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-3-5-truncated-e-9cef4156) |
| **Module Family** | `Formalism/PeriodIntegrals` |
| **Attempt ID** | `#99125` |
| **Playground Score** | `65.05` |
| **Normalized Tokens (`TOKEN_RE`)** | `17,790` vs baseline `129,270` (**-86.24%**, `7.27×` smaller) |
| **Characters / Lines / Files** | `71,700` chars vs `423,943` (**-83.09%**) · `1,599` lines · `1` `.lean` file(s) vs `89` baseline files |
| **Frozen Challenge Definitions** | 0 (pure Mathlib statement) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

> [!NOTE]
> Updated to frontier attempt **`#99125`** by **`Pi`** (score `65.05`, `-86.24%` tokens), superseding earlier staged attempt `#97759` (score `64.14`).

## Proved Theorem

```lean
theorem AlpogeRHCore3.explicitFormula :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ u T : ℝ, 2 ≤ T → T ≤ u →
        ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}).Finite ∧
        ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (analyticOrderNatAt (LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
          C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
            ∑ᶠ ρ ∈ ZerosBelow χ 1, (analyticOrderNatAt (LFunction χ) ρ : ℝ) / ‖ρ‖)
```

### Proof Simplification Highlights
Replaces custom Cauchy/Euler-Maclaurin machinery with Mathlib Borel–Carathéodory & divided-difference (`DSlope`) zero factorization; uses Lean 4 `grind` automation (52×) to collapse algebraic/functional goals.

## Corresponding Target Modules in `src/`

- `src/Formalism/PeriodIntegrals/ExplicitFormula.lean` (`PI.ExplicitFormula` / `PI.ExplicitFormulaWith`)
- `src/Formalism/PeriodIntegrals/ExplicitFormulaCounts/ExplicitFormula.lean` (`explicitFormula_closed : PI.ExplicitFormula`)
- `src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ExplicitFormula.lean`

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core3-attempt-99125/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 3/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore3`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Statement matches `PI.ExplicitFormula` in `src/Formalism/PeriodIntegrals/ExplicitFormula.lean` directly.
- Port from standalone `import Mathlib` (Lean `v4.34.1`) to `module` / `public import` / `@[expose] public section` with `autoImplicit = false` under Lean `v4.36.0` / `v4.33.1`.
- Check downstream `PI.ZerosWindow` consumers in `Formalism/PeriodIntegrals/ExplicitFormulaCounts/` before pruning transitive files.
