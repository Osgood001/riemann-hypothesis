module

public import Mathlib

@[expose] public section

universe u_1

namespace Bl.PartialDerivativeDegree

private lemma pderiv_td_succ_le {σ : Type u_1} (i : σ) (q : MvPolynomial σ Complex)
    (h : MvPolynomial.pderiv i q ≠ 0) :
    (MvPolynomial.pderiv i q).totalDegree + 1 ≤ q.totalDegree := by
  classical
  have hdeg : (MvPolynomial.pderiv i q * MvPolynomial.X i).totalDegree ≤ q.totalDegree := by
    apply MvPolynomial.totalDegree_le_of_support_subset
    rw [MvPolynomial.support_mul_X]
    intro m hm
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hs
    exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs)
  rwa [MvPolynomial.totalDegree_mul_of_isDomain h (MvPolynomial.X_ne_zero i),
    MvPolynomial.totalDegree_X] at hdeg

theorem goal1 :
  ∀ {σ : Type u_1} (i : σ) (q L : MvPolynomial.{u_1, 0} σ Complex),
  LE.le.{0} (MvPolynomial.totalDegree.{0, u_1} L) 1 →
    LE.le.{0}
      (MvPolynomial.totalDegree.{0, u_1}
        (HMul.hMul.{u_1, u_1, u_1}
          (DFunLike.coe.{max (u_1 + 1) 1, max (u_1 + 1) 1, max (u_1 + 1) 1} (MvPolynomial.pderiv.{0, u_1} i) q) L))
      (MvPolynomial.totalDegree.{0, u_1} q) := by
  intro σ i q L hL
  by_cases h : MvPolynomial.pderiv i q = 0
  · simp [h]
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add_left hL _).trans (pderiv_td_succ_le i q h))

end Bl.PartialDerivativeDegree
