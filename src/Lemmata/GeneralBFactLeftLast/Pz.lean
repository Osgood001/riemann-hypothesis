module

public import Mathlib

@[expose] public section

open Module Module.End

namespace Bl.general_b_fact_left_last

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem goal1 {A B : End K V} (h : Commute A B) {a b : K} {x : V}
    (hA : x ∈ A.maxGenEigenspace a) (hB : x ∈ B.maxGenEigenspace b) :
    x ∈ (A * B).maxGenEigenspace (a * b) := by
  rw [mem_maxGenEigenspace] at hA hB ⊢
  obtain ⟨k, hk⟩ := hA
  obtain ⟨l, hl⟩ := hB
  have hNB : Commute (A - a • 1) B := h.sub_left ((Commute.one_left B).smul_left a)
  have hNM : Commute (A - a • 1) (B - b • 1) :=
    hNB.sub_right ((Commute.one_right _).smul_right b)
  have hBM : Commute B (B - b • 1) :=
    (Commute.refl B).sub_right ((Commute.one_right B).smul_right b)
  have key : A * B - (a * b) • (1 : End K V) = (A - a • 1) * B + a • (B - b • 1) := by
    rw [sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]; abel
  have hc : Commute ((A - a • 1) * B) (a • (B - b • 1)) := (hNM.mul_left hBM).smul_right a
  -- The endomorphisms that kill x form a left ideal.
  let I : Ideal (End K V) := LinearMap.ker (LinearMap.toSpanSingleton (End K V) V x)
  have hLeft : ((A - a • 1) * B) ^ k ∈ I := by
    change (((A - a • 1) * B) ^ k) x = 0
    rw [hNB.eq, hNB.symm.mul_pow, mul_apply_eq_comp, hk, map_zero]
  have hRight : (a • (B - b • 1)) ^ l ∈ I := by
    change ((a • (B - b • 1)) ^ l) x = 0
    rw [smul_pow, LinearMap.smul_apply, hl, smul_zero]
  refine ⟨k + l - 1, ?_⟩
  rw [key]
  exact I.add_pow_add_pred_mem_of_pow_mem_of_commute hLeft hRight hc

end Bl.general_b_fact_left_last
