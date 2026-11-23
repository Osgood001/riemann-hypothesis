# Core Pillar 10/13 — Jacquet–Langlands / Selberg Trace Formula for Hilbert–Modular Torus Kernels (Playground Attempt #99249)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 10/13 — Jacquet–Langlands Trace Formula](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-10-jacquet-lang-8fa3c55d) |
| **Module Family** | `PositivityTheory/AutomorphicForms + GroundTheory/AutomorphicForms` |
| **Attempt ID** | `#99249` |
| **Playground Score** | `55.13` |
| **Normalized Tokens (`TOKEN_RE`)** | `90,955` vs baseline `153,957` (**-40.92%**, `1.69×` smaller) |
| **Characters / Lines / Files** | `271,754` chars vs `474,471` (**-42.72%**) · `3,580` lines · `7` `.lean` file(s) vs `60` baseline files |
| **Frozen Challenge Definitions** | 2 (`ComplexMinusRealLineMeasureCoordinates`, `MultivariableReproducingFormula`) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `B0.lean`, `B1.lean`, `B2.lean`, `B3.lean`, `B4.lean`, `B5.lean`, `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore10.jacquetLanglandsTorusTF :
    UpperTheory.Esk.TF
```

### Proof Simplification Highlights
Specializes GRH to the trivial mod-1 character to descend directly to ζ(s); folds hypotheses via `simp_all` (1×).

## Corresponding Target Modules in `src/`

- `src/PositivityTheory/AutomorphicForms/PublishedInputs/JacquetLanglands/TorusKernels/FinalTF.lean` (`UpperTheory.Esk.s_TF`)
- `src/PositivityTheory/AutomorphicForms/PublishedInputs/JacquetLanglands/TorusKernels/MultivariableReproducingFormula.lean` & `ComplexMinusRealLineMeasureCoordinates.lean`

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core10-attempt-99249/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 10/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore10`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Proof imports both frozen `TorusKernels` definition modules and factors helper lemmas across `B0.lean`–`B5.lean` + `Solution.lean`.
- Namespace `B0`–`B5` cleanly under `PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.*` with Lean `v4.36.0` `module` / `public import` / `autoImplicit = false`.
- Re-verify against Lean `v4.36.0` (`main`) and `v4.33.1` (Grand Challenge) before replacing `FinalTF.lean` and pruning redundant files.
