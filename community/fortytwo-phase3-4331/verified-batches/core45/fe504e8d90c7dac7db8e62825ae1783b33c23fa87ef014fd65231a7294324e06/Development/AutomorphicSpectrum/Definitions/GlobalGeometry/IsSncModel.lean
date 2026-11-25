import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure IsEmbedded {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lam : X → X → (Σ k, ι k) → ℂ) : Prop where
  isOpen : ∀ x, IsOpen (U x)
  mem_U : ∀ x, x ∈ U x
  holo : ∀ x p, A.HoloOn (U x) fun y => lam x y p
  mem : ∀ x, ∀ y ∈ U x, lam x y ∈ mcPts P
  compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lam x y) (lam x' y)
  surj : ∀ z ∈ mcPts P, ∃ x, SameOrbit (lam x x) z
  inj : ∀ x x', SameOrbit (lam x x) (lam x' x') → x = x'
  immersion : ∀ x, ∀ p : (k : K) → ι k, (∀ k, lam x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lam x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥


def IsSncModel {Ω : Type} [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)) : Prop :=
  ∀ c : (k : K) → ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ (m : ℕ) (f a : Fin m → Ω),
    (∀ l, f l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    (∀ l, a l ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) ∧
    ∑ l, a l * f l = 1 ∧ ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω,
      S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) →
      Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
        LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
        ∀ q : Ideal S, q.IsPrime →
          ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g → s ∈ q) ↔
            ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)


section Same

variable {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]


end Same

end GlobalTheory.CompanionTheory.Ar.Cmp
