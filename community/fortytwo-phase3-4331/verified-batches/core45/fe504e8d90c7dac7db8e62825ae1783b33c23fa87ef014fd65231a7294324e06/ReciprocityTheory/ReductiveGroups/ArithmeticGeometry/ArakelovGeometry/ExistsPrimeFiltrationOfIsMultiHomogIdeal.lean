import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable abbrev lexDecEq (n : ℕ) : DecidableEq (Lex (Fin n → ℕ)) := LinearOrder.toDecidableEq

attribute [local instance 2000] lexDecEq

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

def lexW (e : K ≃ Fin n) : (Σ k, ι k) → Lex (Fin n → ℕ) :=
  fun p => toLex (Pi.single (e p.1) 1)

theorem weight_lexW (e : K ≃ Fin n) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexW (ι := ι) e) m = toLex (fun j => ∑ i, m ⟨e.symm j, i⟩) := by
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • lexW (ι := ι) e i) (fun i => zero_nsmul _)]
  show (∑ p, m p • (Pi.single (e p.1) 1 : Fin n → ℕ)) = fun j => ∑ i, m ⟨e.symm j, i⟩
  funext j
  rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single (e.symm j)]
  · simp [Pi.single_apply]
  · intro k _ hk
    refine Finset.sum_eq_zero fun i _ => ?_
    have hjk : j ≠ e k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [Pi.single_apply, hjk]
  · simp

theorem isMultiHomog_iff_lex (e : K ≃ Fin n) (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (lexW e) f (toLex (a ∘ e.symm)) := by
  constructor
  · intro h d hd
    rw [weight_lexW]
    congr 1
    funext j
    exact h d (MvPolynomial.mem_support_iff.mpr hd) (e.symm j)
  · intro h d hd k
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_lexW] at h1
    obtain ⟨j, rfl⟩ := e.symm.surjective k
    exact congrFun (toLex.injective h1) j

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomog_of_mem_lex (e : K ≃ Fin n) {f : MRing ι} {m : Lex (Fin n → ℕ)}
    (h : f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) m) :
    IsMultiHomog f (fun k => ofLex m (e k)) := by
  rw [mem_weightedHomogeneousSubmodule] at h
  rw [isMultiHomog_iff_lex e]
  have hm : (fun k => ofLex m (e k)) ∘ e.symm = ofLex m := by
    funext j
    simp
  rw [hm, toLex_ofLex]
  exact h

theorem mem_lex_of_isMultiHomog (e : K ≃ Fin n) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) (toLex (a ∘ e.symm)) := by
  rw [mem_weightedHomogeneousSubmodule]
  exact (isMultiHomog_iff_lex e f a).1 h


end Lex

section Filtration

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    by_contra h
    exact hm (if_neg (Ne.symm h))
  simp [hm0]

attribute [local instance] MvPolynomial.weightedGradedAlgebra




end Filtration

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
