import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]







theorem isMultiHomog_X' [DecidableEq K] (b : K) (i : ι b) :
    IsMultiHomog (X ⟨b, i⟩ : MRing ι) (Pi.single b 1) := by
  intro m hm k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k = b
  · subst hk
    simp only [Pi.single_eq_same]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      apply Finsupp.single_eq_of_ne
      intro h
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact hj (by first | exact h.symm | exact h)
    · intro h; exact absurd (Finset.mem_univ i) h
  · simp [Finsupp.single_apply, hk, Ne.symm hk]




end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
