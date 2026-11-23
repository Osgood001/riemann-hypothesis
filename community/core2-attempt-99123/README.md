# Core Pillar 2/13 — Chebotarev Density Existence Theorem over ℚ (Playground Attempt #99123)

> [!IMPORTANT]
> **Draft staging directory — not yet integrated into `src/` or `lakefile.toml`.**
> Merging into `main` / `src/` awaits explicit author confirmation & open-source licensing clearance from **Pi** as well as full-repository interface porting and incremental verification.

## Attribution & Verified Playground Metrics

| Field | Value |
|---|---|
| **Contestant** | `Pi` |
| **Playground Challenge** | [Core 2/13 — Chebotarev Density (ℚ)](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-2-5-chebotarev-3c22e466) |
| **Module Family** | `ReciprocityTheory/Chebotarev + GroundTheory/GlobalFields` |
| **Attempt ID** | `#99123` |
| **Playground Score** | `62.10` |
| **Normalized Tokens (`TOKEN_RE`)** | `13,963` vs baseline `60,726` (**-77.01%**, `4.35×` smaller) |
| **Characters / Lines / Files** | `57,168` chars vs `211,345` (**-72.95%**) · `1,266` lines · `1` `.lean` file(s) vs `47` baseline files |
| **Frozen Challenge Definitions** | 0 (pure Mathlib statement) |
| **Playground Verifier Status** | Verified clean on **Lean `v4.34.1` + Comparator** (`0 sorry`, `0 admit`, `0 custom axioms`; standard axioms `propext`, `Classical.choice`, `Quot.sound` only) |
| **Reported Model / Harness** | `Gemini 4 Neon` / `Antigravity` |
| **Included Proof File(s)** | `Solution.lean` |

> [!NOTE]
> Updated to frontier attempt **`#99123`** by **`Pi`** (score `62.10`, `-77.01%` tokens), superseding earlier staged attempt `#98168` (score `61.05`).

## Proved Theorem

```lean
theorem AlpogeRHCore2.chebotarev :
    ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (σ : Gal(K/ℚ)) (T : Finset ℕ),
      ∃ p : ℕ, p.Prime ∧ p ∉ T ∧ ∃ P : Ideal (𝓞 K), ∃ _ : P.IsPrime,
        P.LiesOver (Ideal.span {(p : ℤ)}) ∧ Algebra.IsUnramifiedAt ℤ P ∧ IsArithFrobAt ℤ σ P
```

### Proof Simplification Highlights
Constructs infinite Chebotarev primes via Galois Frobenius conjugacy classes & character orthogonality; uses Lean 4 `grind` automation (19×) to collapse algebraic/functional goals.

## Corresponding Target Modules in `src/`

- `src/ReciprocityTheory/Chebotarev/CyclotomicIrreducibleOfForallIsUnramifiedAt.lean` & `EulerSum.lean` (`ReciprocityTheory.Cheb.statement_holds`)
- `src/GroundTheory/GlobalFields/TateThesis/Chebotarev.lean` & `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/ClassFieldRamification/Cheb.lean`

## Toolchain & Interface Gap (Why Placed Under `community/`)

This submission is staged under `community/core2-attempt-99123/` instead of overwriting `src/` directly so `src/` stays intact and buildable:

| Environment | Lean Toolchain | Module / Build Contract |
|---|---|---|
| **This Submission (Playground Core 2/13)** | `leanprover/lean4:v4.34.1` | Standalone `import Mathlib` (+ challenge def imports if any), Playground namespace (`AlpogeRHCore2`), default `autoImplicit` |
| **Playground Grand Challenge Baseline** | `leanprover/lean4:v4.33.1` | Levent Alpöge original full archive (`175,187` files) |
| **`Osgood001/riemann-hypothesis:main` (Upstream `leanprover-community`)** | `leanprover/lean4:v4.36.0` | Lean 4.36 `module` / `public import` / `@[expose] public section`, `autoImplicit = false`, `relaxedAutoImplicit = false`, `srcDir = "src"`, `mathlib` rev `fc4f59e5` |

### Integration Path into `src/`
- Replace monolithic `import Mathlib` with fine-grained `public import` headers under `module` / `@[expose] public section`.
- Expand compact local abbreviations where helpful and add explicit binders for `autoImplicit = false`.
- Align `AlpogeRHCore2.chebotarev` (`K/ℚ` existence closure) with `ReciprocityTheory.Cheb` (noting `UpperTheory.V.CF.cheb` is over general base number field `K`).
- Re-verify against Lean `v4.36.0` (`main`) and `v4.33.1` (Playground Grand Challenge).
