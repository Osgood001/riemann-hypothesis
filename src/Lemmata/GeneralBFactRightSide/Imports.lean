module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_right_side

theorem goal1 :
  ∀ (x : Real),
  Iff
    (Eq.{1}
      (Complex.exp
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (Complex.ofReal Real.pi)) Complex.I)
          (Complex.ofReal x)))
      1)
    (Exists.{1} fun (n : Int) ↦ Eq.{1} x (Int.cast.{0} n)) := by
  intro x
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp
    have h3 : (x : ℂ) = (n : ℂ) := by grind
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

end Bl.general_b_fact_right_side
