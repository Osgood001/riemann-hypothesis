module

public import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hadamard

@[expose] public section

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.hadam :
    ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), G.PosSemidef → (∀ a, (G a a).re ≤ 1) →
    0 ≤ G.det.re ∧ G.det.re ≤ 1 ∧ ‖G.det‖ = G.det.re := by
  intro N G hG hdiag
  refine ⟨(Complex.nonneg_iff.mp hG.det_nonneg).1, ?_, (Complex.re_eq_norm.mpr hG.det_nonneg).symm⟩
  exact (ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_prod_diag N G hG).trans
    (Finset.prod_le_one₀ (fun i _ => (Complex.nonneg_iff.mp (hG.diag_nonneg (i := i))).1)
      fun i _ => hdiag i)
