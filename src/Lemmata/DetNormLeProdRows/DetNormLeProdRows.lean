module

public import Mathlib
public import Formalism.GelfandTransference.Statement

@[expose] public section

namespace Bl.DetNormLeProdRows

theorem goal1 :
  Formalism.HadamardInequality.Hadamard := by
  classical
  intro ρ A
  let v : Fin ρ → EuclideanSpace ℂ (Fin ρ) := fun i => WithLp.toLp 2 (A i)
  suffices hnorm : ‖A.det‖ ≤ ∏ i, ‖v i‖ by
    simpa only [← Finset.prod_pow, EuclideanSpace.norm_sq_eq] using
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin ρ)) = Fintype.card (Fin ρ) := by simp
  let e := EuclideanSpace.basisFun (Fin ρ) ℂ
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h v
  have he : e.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose A]
    congr 1
  have hdet : ‖b.toBasis.det v‖ = ‖A.det‖ := by
    conv_lhs => rw [b.toBasis.det.eq_smul_basis_det e.toBasis]
    rw [smul_apply, smul_eq_mul, norm_mul, OrthonormalBasis.coe_toBasis,
      b.det_to_matrix_orthonormalBasis e, one_mul, he]
  rw [← hdet, InnerProductSpace.gramSchmidtOrthonormalBasis_det h v, norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i _
  simpa only [b.orthonormal.1 i, one_mul] using norm_inner_le_norm (b i) (v i)

end Bl.DetNormLeProdRows
