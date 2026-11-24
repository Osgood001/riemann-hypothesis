module

public import Mathlib

@[expose] public section

open MvPowerSeries

namespace Bl.PowMulVecEigen

variable {C : Type} [Field C]

theorem goal1 {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (w : Fin n → C) (lam : C)
    (h : Matrix.mulVec A w = lam • w) (f : Polynomial C) :
    Matrix.mulVec (Polynomial.aeval A f) w = f.eval lam • w := by
  rw [← Matrix.toLinAlgEquiv'_apply, ← Polynomial.aeval_algHom_apply Matrix.toLinAlgEquiv' A f]
  exact Module.End.aeval_apply_of_mem_apply_eq_smul (by rwa [Matrix.toLinAlgEquiv'_apply])

end Bl.PowMulVecEigen
