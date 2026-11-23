# Core Pillar 11/13 — Bochner–Martin / Osgood Theorem: Nonvanishing Jacobian of Injective Holomorphic Maps (Playground Attempt #99154)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 11/13 — Bochner–Martin Jacobian ≠ 0](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-11-bochner-mart-0121963b) |
| **Module Family** | `GroundTheory/HeightsAndTheta` |
| **Attempt ID** | `#99154` |
| **Playground Score** | `60.92` |
| **Normalized Tokens (`TOKEN_RE`)** | `7,486` vs baseline `27,098` (**-72.37%**, `3.62×` smaller) |
| **Characters / Lines / Files** | `27,308` chars vs `96,430` (**-71.68%**) · `482` lines · `1` `.lean` file(s) vs `26` baseline files |
| **Frozen Challenge Definitions** | 0 (pure 4-line Mathlib statement) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

## Proved Theorem

```lean
theorem AlpogeRHCore11.injectiveHolomorphicJacobianNeZero :
    ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
      IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U →
      ∀ x ∈ U, LinearMap.det (fderiv ℂ f x : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ 0
```

### Proof Simplification Highlights
Refactors the core argument around Mathlib lemma(s) isCompact_iff_compactSpace, isCompact_Icc; uses generalized inequality rewriting `grw` (1×) to shorten estimate chains.

## Corresponding Target Modules in `src/`

- `src/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInjectiveHolomorphicJacobianNeZero.lean` (`InjectiveHolomorphicJacobianNeZero.proof`)

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core11-attempt-99154/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 11/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore11`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Zero frozen definitions — pure Mathlib statement matching `PInjectiveHolomorphicJacobianNeZero.lean` directly.
- Replace `import Mathlib` with targeted `public import` headers under Lean `v4.36.0` `module` / `@[expose] public section` and `autoImplicit = false`.
- Verify `grw` and several-complex-variables differentiation lemmas on Lean `v4.36.0` / `v4.33.1` before wiring into `GroundTheory/HeightsAndTheta/`.
