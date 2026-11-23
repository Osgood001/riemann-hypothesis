module

public import Mathlib

@[expose] public section

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.grampsd :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.IsHermitian →
    (∀ c : ι → ℤ, 0 ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))) → G.PosSemidef := by
  intro ι _ _ G hG hc
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hG, fun x => ?_⟩
  simp only [star_trivial]
  let Q : (ι → ℝ) → ℝ := fun v => v ⬝ᵥ (G *ᵥ v)
  have hQ : Continuous Q := by
    simp only [Q, dotProduct, mulVec]
    fun_prop
  have hdense : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  refine hdense.induction_on (p := fun v => 0 ≤ Q v) x (isClosed_le continuous_const hQ) ?_
  intro q
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose c h using hd
  have hcast : (fun i => (c i : ℝ)) = ((d : ℤ) : ℝ) • (fun i => (q i : ℝ)) := by
    funext i
    have hi : (c i : ℚ) = (d : ℤ) • q i := h i
    rw [zsmul_eq_mul] at hi
    change (c i : ℝ) = ((d : ℤ) : ℝ) * (q i : ℝ)
    exact_mod_cast hi
  have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.mp d.2
  apply nonneg_of_mul_nonneg_right _ (sq_pos_of_ne_zero hd0)
  simpa only [Q, hcast, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, sq, mul_assoc] using hc c
