module

public import Mathlib

@[expose] public section

namespace Bl.ProductIdentities

theorem goal1 {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  let D : ContinuousMultilinearMap ℝ (fun _ : n => n → ℂ) ℂ :=
    ⟨(@Matrix.detRowAlternating n inst_1 inst ℂ _).toMultilinearMap.restrictScalars ℝ, continuous_id.matrix_det⟩
  have hA : HasDerivAt A A' 0 := hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 (h i)
  refine ((D.hasFDerivAt (A 0)).comp_hasDerivAt 0 hA).congr_deriv ?_
  rw [h0]
  refine (D.linearDeriv_apply (1 : Matrix n n ℂ) A').trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  change ((1 : Matrix n n ℂ).updateRow i (A' i)).det = A' i i
  simp [← Matrix.cramer_transpose_apply]

end Bl.ProductIdentities
