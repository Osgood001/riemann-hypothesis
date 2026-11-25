module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeEqLintegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntNearOfClosureShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeSumSqBallPosLtTop

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

private theorem log_ellipsoid_volume (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.PosDef) (r : ℝ) (hr : 0 < r) :
    let v := volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2}
    v ≠ ⊤ ∧ 0 < v.toReal ∧ Real.log v.toReal =
      Fintype.card ι * Real.log r - Real.log A.det / 2 +
        Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal := by
  obtain ⟨hv, hω₀, hω⟩ := volume_ellipsoid ι A hA r hr.le
  dsimp only
  rw [hv, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity [hA.det_pos])]
  have hωr := ENNReal.toReal_pos hω₀.ne' hω.ne
  refine ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.ne, by positivity [hA.det_pos], ?_⟩
  rw [Real.log_mul (by positivity [hA.det_pos]) hωr.ne', Real.log_div (by positivity) (by positivity [hA.det_pos]),
    Real.log_pow, Real.log_sqrt hA.det_pos.le]

/-- A translate of the half-radius ellipsoid injects, after taking differences, into the
lattice points of the full ellipsoid. No covering radius is needed on this side. -/
theorem log_ellCount_lower (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.PosDef) (R : ℝ) (hR : 0 < R) :
    -(Fintype.card ι * Real.log 2) ≤ Real.log (ellCount A R) -
      (Fintype.card ι * Real.log R - Real.log A.det / 2 +
        Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal) := by
  let c (z : ι → ℤ) : ι → ℝ := fun i => z i
  have hcnt : (ellCount A R : ENNReal) =
      (({z : ι → ℤ | EllCount.bf A (c z) (c z) ≤ R ^ 2}.encard : ℕ∞) : ENNReal) := by
    rw [← (EllCount.finite_pts hA (R ^ 2)).cast_ncard_eq]
    rfl
  have hvol : volume {x : ι → ℝ | EllCount.bf A x x ≤ (R / 2) ^ 2} ≤ (ellCount A R : ENNReal) := by
    rw [EllCount.volume_eq_lintegral _ (EllCount.measurableSet_ell A _)]
    refine (lintegral_mono (g := fun _ => (ellCount A R : ENNReal)) fun x => ?_).trans ?_
    · rw [hcnt]
      apply ENat.toENNReal_le.2
      let S := {z : ι → ℤ | EllCount.bf A (x + c z) (x + c z) ≤ (R / 2) ^ 2}
      change S.encard ≤ _
      obtain hS | ⟨z₀, h₀⟩ := S.eq_empty_or_nonempty
      · simp [hS]
      · refine Set.encard_le_encard_of_injOn (f := fun z => z - z₀) (fun z hz => ?_) sub_left_injective.injOn
        have hh : 0 ≤ R / 2 := by positivity
        have hd := EllCount.bf_add_le hA hh hh hz ((EllCount.bf_neg _ _).trans_le h₀)
        have e : x + c z + -(x + c z₀) = c (z - z₀) := by ext i; simp [c]; ring
        rw [e, add_halves] at hd
        exact hd
    · rw [setLIntegral_const, EllCount.volume_cube, mul_one]
  obtain ⟨-, hvpos, hvlog⟩ := log_ellipsoid_volume ι A hA (R / 2) (by positivity)
  have hv := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hvol
  rw [ENNReal.toReal_natCast] at hv
  have hl := Real.log_le_log hvpos hv
  rw [hvlog, Real.log_div hR.ne' two_ne_zero] at hl
  linarith

/-- A covering radius bounds the upper error at every positive counting radius. -/
theorem log_ellCount_upper_of_cover (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.PosDef) (s R : ℝ) (hs : 0 ≤ s) (hR : 0 < R)
    (hnear : ∀ x : ι → ℝ, ∃ z : ι → ℤ,
      ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤ s ^ 2) :
    Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal) ≤
      Fintype.card ι * Real.log (1 + s / R) := by
  obtain ⟨hfin, -, hup⟩ := ellCount_volume ι A hA s R hs hR.le hnear
  have hc : 0 < ellCount A R := (Set.ncard_pos hfin).2 ⟨0, by simp; positivity⟩
  have hhigh := add_pos_of_pos_of_nonneg hR hs
  obtain ⟨hvfin, -, hvlog⟩ := log_ellipsoid_volume ι A hA (R + s) hhigh
  have hv := ENNReal.toReal_mono hvfin hup
  rw [ENNReal.toReal_natCast] at hv
  have hl := Real.log_le_log (Nat.cast_pos.mpr hc) hv
  have he : R + s = R * (1 + s / R) := by field_simp
  rw [hvlog, he, Real.log_mul hR.ne' (by positivity : 0 < 1 + s / R).ne', mul_add] at hl
  linarith

/-- The covering radius yields separate lower and upper errors around the volume asymptotic. -/
theorem log_ellCount_of_cover (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.PosDef) (s R : ℝ) (hs : 0 ≤ s) (hsR : s < R)
    (hnear : ∀ x : ι → ℝ, ∃ z : ι → ℤ,
      ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤ s ^ 2) :
    {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧
    Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal) ∈
      Set.Icc (Fintype.card ι * Real.log (1 - s / R))
        (Fintype.card ι * Real.log (1 + s / R)) := by
  have hR : 0 < R := hs.trans_lt hsR
  have hlow : 0 < R - s := sub_pos.mpr hsR
  have hlo := (ellCount_volume ι A hA s (R - s) hs hlow.le hnear).2.1
  rw [sub_add_cancel] at hlo
  refine ⟨EllCount.finite_pts hA _, ?_, log_ellCount_upper_of_cover ι A hA s R hs hR hnear⟩
  obtain ⟨-, hvpos, hvlog⟩ := log_ellipsoid_volume ι A hA (R - s) hlow
  have hv := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hlo
  rw [ENNReal.toReal_natCast] at hv
  have hl := Real.log_le_log hvpos hv
  have he : R - s = R * (1 - s / R) := by field_simp
  have hx := sub_pos.mpr ((div_lt_one hR).mpr hsR)
  rw [hvlog, he, Real.log_mul hR.ne' hx.ne', mul_add] at hl
  linarith

/-- The loss on the lower side dominates the upper side for a nonnegative radius. -/
theorem log_ellCount_abs_of_cover (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.PosDef) (s R : ℝ) (hs : 0 ≤ s) (hsR : s < R)
    (hnear : ∀ x : ι → ℝ, ∃ z : ι → ℤ,
      ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤ s ^ 2) :
    {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧
    |Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ -(Fintype.card ι * Real.log (1 - s / R)) := by
  obtain ⟨hf, hlo, hup⟩ := log_ellCount_of_cover ι A hA s R hs hsR hnear
  have hR : 0 < R := hs.trans_lt hsR
  have hlo0 : 0 < 1 - s / R := sub_pos.mpr ((div_lt_one hR).mpr hsR)
  have hu0 : 0 < 1 + s / R := by positivity
  have hcomp : 1 + s / R ≤ (1 - s / R)⁻¹ := by
    rw [le_inv_comm₀ hu0 hlo0, ← one_div, le_div_iff₀ hu0]
    nlinarith [sq_nonneg (s / R)]
  have hl := Real.log_le_log hu0 hcomp
  rw [Real.log_inv] at hl
  refine ⟨hf, abs_le.mpr ⟨by simpa using hlo, hup.trans ?_⟩⟩
  simpa using mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (Fintype.card ι))

private theorem log_ellCount_le_log_two (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.PosDef) (s R : ℝ) (hs : 0 ≤ s) (hR : 0 < R) (hsR : s ≤ R)
    (hnear : ∀ x : ι → ℝ, ∃ z : ι → ℤ,
      ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤ s ^ 2) :
    {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧
    |Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ Fintype.card ι * Real.log 2 := by
  have hu := log_ellCount_upper_of_cover ι A hA s R hs hR hnear
  have hlo := log_ellCount_lower ι A hA R hR
  have hr : 1 + s / R ≤ 2 := by linarith [div_le_one_of_le₀ hsR hR.le]
  exact ⟨EllCount.finite_pts hA _, abs_le.mpr ⟨hlo, hu.trans (mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) hr) (Nat.cast_nonneg _))⟩⟩

/-- A short generating family suffices as soon as its square-root radius fits. -/
theorem log_ellCount_near_sqrt : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ R : ℝ), 0 ≤ ρ → 0 < R → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → Real.sqrt (Fintype.card ι) * ρ / 2 ≤ R → {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧ |Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ Fintype.card ι * Real.log 2 := by
  intro ι _ _ A hA T ρ R hρ hR hT hTz hRρ
  exact log_ellCount_le_log_two ι A hA (Real.sqrt (Fintype.card ι) * ρ / 2) R (by positivity) hR hRρ
    (exists_int_near_of_closure_short_sqrt ι A T ρ hρ hT hTz)

theorem log_ellCount_near : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ R : ℝ), 0 ≤ ρ → 0 < R → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → 2 * Fintype.card ι * ρ ≤ R → {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧ |Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ Fintype.card ι * Real.log 2 := by
  intro ι _ _ A hA T ρ R hρ hR hT hTz hRρ
  exact log_ellCount_le_log_two ι A hA ((Fintype.card ι : ℝ) * ρ) R (by positivity) hR (by linarith)
    (exists_int_near_of_closure_short ι A hA T ρ hρ hT hTz)

end GlobalTheory.HSAmp
