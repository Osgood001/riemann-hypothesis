module

public import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hadam

@[expose] public section

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.cramer_le_one {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (c : Fin N → ℂ)
    (hG : G.PosSemidef) (hd : ∀ j, (G j j).re ≤ 1) (hc : (star c ⬝ᵥ (G *ᵥ c)).re ≤ 1)
    (a : Fin N) : ‖G.det‖ * ‖c a‖ ≤ 1 := by
  let E := (1 : Matrix (Fin N) (Fin N) ℂ).updateCol a c
  have hE : E.det = c a := by rw [← cramer_apply, cramer_one]; rfl
  have hdiag (j : Fin N) : ((Eᴴ * G * E) j j).re ≤ 1 := by
    rw [Matrix.mul_assoc]
    by_cases h : j = a
    · subst j
      simpa [E, Matrix.mul_apply, conjTranspose_apply, updateCol_apply, dotProduct, mulVec] using hc
    · simpa [E, Matrix.mul_apply, conjTranspose_apply, updateCol_apply, h, Matrix.one_apply] using hd j
  have bound (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosSemidef) (h : ∀ j, (A j j).re ≤ 1) :
      ‖A.det‖ ≤ 1 := by
    obtain ⟨_, hle, heq⟩ := UpperTheory.V.KT.hadam N A hA h
    exact heq.trans_le hle
  apply (sq_le_one_iff₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc (‖G.det‖ * ‖c a‖) ^ 2 = ‖G.det‖ * ‖(Eᴴ * G * E).det‖ := by
         rw [det_mul, det_mul, det_conjTranspose, hE, norm_mul, norm_mul, norm_star]
         ring
       _ ≤ 1 := by
         simpa only [one_mul] using mul_le_mul (bound G hG hd)
           (bound _ (hG.conjTranspose_mul_mul_same E) hdiag) (norm_nonneg _) zero_le_one

theorem UpperTheory.V.KT.cramer :
    ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (c : Fin N → ℂ), G.PosSemidef → (∀ a, (G a a).re ≤ 1) →
    (star c ⬝ᵥ (G *ᵥ c)).re ≤ 1 → ∀ a, ‖G.det‖ * ‖c a‖ ≤ (N : ℝ) ^ N := by
  intro N G c hG hd hc a
  exact (UpperTheory.V.KT.cramer_le_one G c hG hd hc a).trans
    (by exact_mod_cast (Nat.pow_self_pos : 1 ≤ N ^ N))
