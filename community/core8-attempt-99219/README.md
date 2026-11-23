# Core Pillar 8/13 — Siegel–Weil Unramified Local Hermitian Density & Siegel Series Identity (Playground Attempt #99219)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 8/13 — Siegel–Weil Local Density](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-8-siegel-weil-u-4d13d2e3) |
| **Module Family** | `Development/AutomorphicSpectrum + Development/WeilBound` |
| **Attempt ID** | `#99219` |
| **Playground Score** | `55.51` |
| **Normalized Tokens (`TOKEN_RE`)** | `33,730` vs baseline `59,681` (**-43.48%**, `1.77×` smaller) |
| **Characters / Lines / Files** | `111,218` chars vs `199,407` (**-44.23%**) · `1,958` lines · `1` `.lean` file(s) vs `53` baseline files |
| **Frozen Challenge Definitions** | 1 (`Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs`) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore8.siegelWeilLocalDensity :
    PositivityTheory.PfSWUS.Loc.SeriesEqDens ∧
    PositivityTheory.PfSWUS.Loc.UnrFormula
```

### Proof Simplification Highlights
Derives uniform character prime-sum bounds from Page/Siegel exceptional zero lower bounds; driven by `simp, nlinarith, omega`.

## Corresponding Target Modules in `src/`

- `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedLocalFormula.lean` (`seriesEqDens` ∧ `unrFormula`)
- `src/Development/WeilBound/CoreStatements/AutomorphicKernels/UnitarySchrodingerModel/LocalDefs.lean` (`PositivityTheory.PfSWUS.Loc.*`)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core8-attempt-99219/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 8/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore8`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Proof already targets `Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs`.
- Port from standalone `import Mathlib` (Lean `v4.34.1`) to Lean `v4.36.0` `module` / `public import` / `@[expose] public section` with `autoImplicit = false`.
- Wire the two conjunction components (`SeriesEqDens`, `UnrFormula`) into `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedLocalFormula.lean` and run incremental `lake build`.
