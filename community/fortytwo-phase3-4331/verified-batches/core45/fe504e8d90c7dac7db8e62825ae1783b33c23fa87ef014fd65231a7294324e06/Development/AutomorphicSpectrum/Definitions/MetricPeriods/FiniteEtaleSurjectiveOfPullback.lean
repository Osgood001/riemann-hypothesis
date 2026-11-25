import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {R : Type} [Field R]

theorem form_mem_mCoordIdeal_iff (w : (Σ k, J k) → R) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∈ mCoordIdeal w ↔ MvPolynomial.aeval w g = 0 := by
  refine ⟨fun h => ?_, GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero w hg⟩
  have h' : mConeMap w g = 0 := h
  rw [GroundTheory.Heights₂.Heights.LowerBoundFree.mConeMap_of_isMultiHomog w hg] at h'
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact MvPolynomial.C_eq_zero.1 h1
  · exact absurd h1 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero _))

end GlobalTheory.CompanionTheory.Ar.PB
