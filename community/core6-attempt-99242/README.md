# Core Pillar 6/13 — CM j-Invariant & Formal Group Integrality (Playground Attempt #99242)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 6/13 — CM j-Invariant Integrality](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-6-cm-j-invarian-70b3d4ba) |
| **Module Family** | `Formalism/LocalToGlobal + ReciprocityTheory/ReductiveGroups` |
| **Attempt ID** | `#99242` |
| **Playground Score** | `59.14` |
| **Normalized Tokens (`TOKEN_RE`)** | `339,899` vs baseline `951,787` (**-64.29%**, `2.80×` smaller) |
| **Characters / Lines / Files** | `1,219,573` chars vs `3,318,710` (**-63.25%**) · `29,412` lines · `6` `.lean` file(s) vs `452` baseline files |
| **Frozen Challenge Definitions** | 1 (`Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement`) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Bundle00.lean`, `Bundle01.lean`, `Bundle02.lean`, `Bundle03.lean`, `Bundle04.lean`, `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore6.cmIntegrality :
    Formalism.L2.Th1.CM.JInvariantIntegrality ∧ Formalism.L2.Th1.CM.CM3
```

### Proof Simplification Highlights
Replaces custom Cauchy/Euler-Maclaurin machinery with Mathlib Borel–Carathéodory & divided-difference (`DSlope`) zero factorization; folds hypotheses via `simp_all` (2×).

## Corresponding Target Modules in `src/`

- `src/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgStatus.lean` (`ReciprocityTheory.ChartRestriction.L1.cm1` ∧ `cmIntegralityThree`)
- `src/Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean` (`Formalism.L2.Th1.CM.JInvariantIntegrality`, `CM3`)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core6-attempt-99242/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 6/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore6`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Proof already imports the upstream statement module `Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement`.
- Replace monolithic `import Mathlib` and local `Bundle00`–`Bundle04` module names with Lean `v4.36.0` `module` / `public import` / `@[expose] public section` under `src/ReciprocityTheory/ReductiveGroups/` & `src/Formalism/LocalToGlobal/`.
- Enforce `autoImplicit = false` / `relaxedAutoImplicit = false` and verify incremental `lake build` + Comparator on `v4.36.0` / `v4.33.1`.
