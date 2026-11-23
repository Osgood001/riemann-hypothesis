# Core Pillar 9/13 — Gelfand–Graev Whittaker Multiplicity One for GL_k(𝔽_q) (Playground Attempt #99253)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 9/13 — Gelfand–Graev Mult. One](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-9-gelfand-graev-509f3aa4) |
| **Module Family** | `Formalism/LocalToGlobal + Formalism/PeriodIntegrals` |
| **Attempt ID** | `#99253` |
| **Playground Score** | `69.36` |
| **Normalized Tokens (`TOKEN_RE`)** | `5,942` vs baseline `109,112` (**-94.55%**, `18.36×` smaller) |
| **Characters / Lines / Files** | `19,723` chars vs `373,329` (**-94.72%**) · `394` lines · `1` `.lean` file(s) vs `45` baseline files |
| **Frozen Challenge Definitions** | 1 (`Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase`) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore9.gelfandGraevMultOne :
    Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne
```

### Proof Simplification Highlights
Derives uniform character prime-sum bounds from Page/Siegel exceptional zero lower bounds; uses Lean 4 `grind` automation (23×) to collapse algebraic/functional goals.

## Corresponding Target Modules in `src/`

- `src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/WhitFunctDual.lean` (`whittaker_functional_dual`, `gelfand_graev_multiplicity_one`)
- `src/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicBase.lean` (`Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne`)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core9-attempt-99253/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 9/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore9`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Proof already imports `Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolicBase` directly.
- Replace `import Mathlib` with targeted `public import` headers under Lean `v4.36.0` `module` / `@[expose] public section` with `autoImplicit = false`.
- Verify `grind` and finite-field linear algebra / character-sum APIs across Lean `v4.34.1` → `v4.36.0` / `v4.33.1`, then bridge into `WhitFunctDual.lean`.
