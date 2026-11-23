# Core Pillar 12/13 — Cyclotomic Power Series Rigidity & Frobenius Splitting (8-Part Conjunction) (Playground Attempt #99275)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **LewyM** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `LewyM` |
| **Playground Challenge** | [Core 12/13 — Cyclotomic Power Series Rigidity](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-12-cyclotomic-p-3bfcc9a1) |
| **Module Family** | `Formalism/SharpRestriction` |
| **Attempt ID** | `#99275` |
| **Playground Score** | `60.12` |
| **Normalized Tokens (`TOKEN_RE`)** | `3,169` vs baseline `10,193` (**-68.91%**, `3.22×` smaller) |
| **Characters / Lines / Files** | `12,606` chars vs `41,201` (**-69.40%**) · `274` lines · `1` `.lean` file(s) vs `10` baseline files |
| **Frozen Challenge Definitions** | 1 (`Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement`) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `GPT-6` / `Codex CLI` |
| **Included Proof File(s)** | `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore12.cyclotomicPowerSeriesRigidity :
    LevelStatements.Lv.RhoUniqueStatement ∧
    LevelStatements.Lv.RhoComplStatement ∧
    LevelStatements.Lv.CycloDistStatement ∧
    LevelStatements.Lv.CycloSimpleStatement ∧
    LevelStatements.Lv.ExpRescaleStatement ∧
    LevelStatements.Lv.DescendDvdStatement ∧
    LevelStatements.Lv.SplitComplStatement ∧
    LevelStatements.Lv.PsCoprimeStatement
```

### Proof Simplification Highlights
Refactors the core argument around Mathlib lemma(s) Polynomial.algHom_ext, Polynomial.coeToPowerSeries.algHom_apply; driven by `simp, omega, ring`.

## Corresponding Target Modules in `src/`

- `src/Formalism/SharpRestriction/LevelLetterCocycles/CyclotomicPowerSeries/ConstSectionStatement.lean` (8-part rigidity & Frobenius splitting conjunction)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core12-attempt-99275/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 12/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore12`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Proof already imports `ConstSectionStatement` directly and collapses 10 files into 1 self-contained file.
- Port from standalone `import Mathlib` (Lean `v4.34.1`) to Lean `v4.36.0` `module` / `public import` / `@[expose] public section` with `autoImplicit = false`.
- Export the 8 individual statement projections matching downstream `Formalism/SharpRestriction/LevelLetterCocycles/` consumers.
