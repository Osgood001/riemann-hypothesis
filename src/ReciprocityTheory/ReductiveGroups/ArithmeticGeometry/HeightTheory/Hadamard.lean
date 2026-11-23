module

public import Mathlib
import Lemmata.DetNormLeProdRows.DetNormLeProdRows

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open scoped BigOperators ComplexOrder
open Finset Matrix

theorem psd_det_re_le_prod_diag (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosSemidef) :
    G.det.re ≤ ∏ c, (G c c).re := by
  open scoped MatrixOrder in
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hG.nonneg
  simpa only [star_eq_conjTranspose, det_mul, det_conjTranspose, Complex.star_def,
    Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum] using Bl.DetNormLeProdRows.goal1 N B

theorem psd_det_re_le_one_of_diag (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosSemidef)
    (hd : ∀ c, H c c = 1) : H.det.re ≤ 1 := by
  simpa [hd] using psd_det_re_le_prod_diag N H hH

theorem hadamard_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_prod _ (fun i _ => Finset.sum_nonneg
    fun j _ => sq_nonneg ‖A i j‖)] using Real.sqrt_le_sqrt (Bl.DetNormLeProdRows.goal1 n A)

end ReciprocityTheory.ChartRestriction.G.T0
