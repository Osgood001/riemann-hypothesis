import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in
theorem isMultiHomog_zero (d : K → ℕ) : IsMultiHomog (0 : MRing ι) d := by
  intro m hm
  simp at hm

omit [Fintype K] in
theorem isMultiHomog_add {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g + h) d := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · exact hg m hm
  · exact hh m hm

omit [Fintype K] in
theorem isMultiHomog_mul {g h : MRing ι} {a b : K → ℕ} (hg : IsMultiHomog g a)
    (hh : IsMultiHomog h b) : IsMultiHomog (g * h) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul g h hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hg m₁ hm₁ k, hh m₂ hm₂ k]


end Homog

section Cone

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mConeMap_of_isMultiHomog (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) :
    mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [mConeMap, aeval_monomial, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  have hX : (∏ p : Σ k, ι k, (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p) =
      ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, MvPolynomial.algebraMap_apply]
  ring

theorem mem_mCoordIdeal_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [mConeMap_of_isMultiHomog y hg, h0]
  simp

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_eq_zero_of_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    {g : MRing ι} (hg : g ∈ P) : eval z (map (Int.castRingHom ℂ) g) = 0 :=
  hz.2 g hg





end Cone

section Trivial

variable {Ω : Type} [Field Ω] {κ : Type}





end Trivial

end GroundTheory.Heights₂.Heights.LowerBoundFree
