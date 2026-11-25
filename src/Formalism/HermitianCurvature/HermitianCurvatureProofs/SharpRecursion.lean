module

public import Formalism.HermitianCurvature.Statement

/-!
# Sharp constants for the Hermitian-curvature recurrence

For a horizon `N = r + 1` and loss `δ = ε + a`, the optimal multiplier is
`(1 + δ) ^ (2 * N)`. The least uniform linear coefficient at this horizon is
`(1 + 1 / N) ^ (2 * N) - 1`; over all horizons it is `exp 2 - 1`.
-/

@[expose] public section

namespace Formalism.FourierDecayAlt.P.Rec

open Finset Real Filter Topology

/-- Bound for a fixed horizon and a specified multiplier depending on ε + a. -/
def Control (r : ℕ) (f : ℝ → ℝ) : Prop :=
  ∀ (a ε : ℝ) (e σ : ℕ → ℝ),
    0 ≤ a → a ≤ 1 / 2 → 0 ≤ ε → ((r : ℝ) + 1) * (ε + a) ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      f (ε + a) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2

/-- The linear coefficient in the original bound, at a fixed horizon. -/
def AdmissibleAt (r : ℕ) (C : ℝ) : Prop :=
  Control r (fun y => 1 + C * ((r : ℝ) + 1) * y)

theorem recursionSharp_iff : RecursionSharp ↔ ∃ C, ∀ r, AdmissibleAt r C := Iff.rfl

/-- The sharp linear coefficient at horizon `r + 1`. -/
noncomputable def finiteConstant (r : ℕ) : ℝ :=
  (1 + 1 / ((r : ℝ) + 1)) ^ ((r + 1) * 2) - 1

/-- Exact finite-horizon envelope, before convexity. -/
theorem finite_envelope (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ)
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (he : ∀ i, 0 ≤ e i) (hσ : ∀ i, 0 ≤ σ i)
    (rec : ∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t)) :
    σ (r + 1) ^ 2 ≤ (1 + (ε + a)) ^ ((r + 1) * 2) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
  -- The lag sum is itself a first-order state: tail (k + 1) = a (σ k + tail k).
  let tail k := ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * σ (k + 1 - t)
  have tail_succ k : tail (k + 1) = a * (σ k + tail k) := by
    dsimp [tail]
    rw [← Ico_add_one_right_eq_Icc, ← sum_Ico_add' _ 1 (k + 2) 1,
      sum_eq_sum_Ico_succ_bot (by omega) _, mul_add, mul_sum]
    simp
    apply sum_congr rfl
    intro i hi
    have h := (mem_Icc.mp hi).1
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]
  have tail_nonneg k : 0 ≤ tail k := sum_nonneg fun _ _ => mul_nonneg (by positivity) (hσ _)

  -- Bound the augmented state σ k + tail k, not every past value separately.
  let growth := 1 + ε + a
  let majorant k := growth ^ k * (∏ j ∈ Icc 1 k, √(1 + e j)) * σ 0
  have bounds : ∀ k ≤ r + 1, σ k + tail k ≤ majorant k :=
    Nat.rec (by simp [majorant, tail]) fun k ih hk => by
    set s := √(1 + e (k + 1))
    have hs : 1 ≤ s := one_le_sqrt.2 (by grind)
    have h := rec (k + 1) (by omega) hk
    change σ (k + 1) ≤ (1 + ε) * s * σ k + tail k at h
    rw [tail_succ]
    trans ((1 + ε) * s + a) * (σ k + tail k)
    · rw [add_mul]
      gcongr
      rw [mul_add]
      grw [h]
      gcongr
      exact le_mul_of_one_le_left (tail_nonneg _) (one_le_mul_of_one_le_of_one_le (by linarith) hs)
    · trans (growth * s) * majorant k
      · gcongr
        · exact add_nonneg (hσ _) (tail_nonneg _)
        · dsimp [growth]
          nlinarith [mul_nonneg ha (sub_nonneg.2 hs)]
        · apply ih; omega
      · apply le_of_eq
        simp [majorant, s, pow_succ, prod_Icc_succ_top]
        ring
  have bound := bounds _ le_rfl
  have b := (le_add_of_nonneg_right (tail_nonneg _)).trans bound
  grw [b] <;> try apply hσ
  dsimp [majorant, growth]
  have hn i := add_nonneg zero_le_one (he i)
  simp_rw [mul_pow, ← prod_pow, fun i => sq_sqrt (hn i)]
  rw [pow_mul, ← add_assoc]

/-- Complete characterization of the admissible loss envelope, pointwise in δ = ε + a. -/
theorem control_iff (r : ℕ) (f : ℝ → ℝ) : Control r f ↔
    ∀ δ : ℝ, 0 ≤ δ → ((r : ℝ) + 1) * δ ≤ 1 → (1 + δ) ^ ((r + 1) * 2) ≤ f δ := by
  constructor
  · intro h δ hδ hx
    -- With no lag and no losses, σ i = (1 + δ)^i attains the envelope.
    have H := h 0 δ (fun _ => 0) (fun i => (1 + δ) ^ i) le_rfl (by norm_num) hδ
      (by simpa using hx) (fun _ => le_rfl) (fun _ => by positivity) (by
        rintro (_ | k) hi _
        · omega
        · simp only [Nat.add_sub_cancel, add_zero, sqrt_one, mul_one, pow_succ _ k]
          rw [mul_comm]
          apply le_add_of_nonneg_right
          exact sum_nonneg fun _ _ => mul_nonneg (by positivity) (by positivity))
    simpa [pow_mul] using H
  · intro h a ε e σ ha _ hε hx he hσ rec
    apply (finite_envelope r a ε e σ ha hε he hσ rec).trans
    gcongr
    · exact prod_nonneg fun i _ => add_nonneg zero_le_one (he i)
    · exact h _ (by positivity) hx

theorem finiteConstant_admissible (r : ℕ) : AdmissibleAt r (finiteConstant r) := by
  apply (control_iff ..).2
  intro δ hδ hx
  let n := (r : ℝ) + 1
  let x := n * δ
  have hn : n ≠ 0 := by positivity
  -- Convexity bounds the power by its chord between 1 and 1 + 1/n.
  have hcombo : (1 - x) * 1 + x * (1 + 1 / n) = 1 + δ := by dsimp [x]; field_simp; ring
  have hc := (convexOn_pow (𝕜 := ℝ) ((r + 1) * 2)).2 (x := 1) (y := 1 + 1 / n)
    (by simp) (by apply Set.mem_Ici.2; positivity) (sub_nonneg.2 hx) (by positivity : 0 ≤ x)
    (by dsimp [x, n]; ring)
  change (1 + δ) ^ _ ≤ _
  change ((1 - x) * 1 + x * (1 + 1 / n)) ^ ((r + 1) * 2) ≤
    (1 - x) * 1 ^ ((r + 1) * 2) + x * (1 + 1 / n) ^ ((r + 1) * 2) at hc
  rw [hcombo, one_pow, mul_one] at hc
  dsimp [x, n, finiteConstant] at *
  linarith

/-- At each horizon the zero-lag sequence attains the proposed constant exactly. -/
theorem finiteConstant_le {r : ℕ} {C : ℝ} (h : AdmissibleAt r C) : finiteConstant r ≤ C := by
  let u := 1 / ((r : ℝ) + 1)
  have hn : (r : ℝ) + 1 ≠ 0 := by positivity
  have hx : ((r : ℝ) + 1) * u = 1 := by dsimp [u]; field_simp
  have hb := (control_iff ..).1 h u (by positivity) hx.le
  change (1 + u) ^ ((r + 1) * 2) ≤ 1 + C * ((r : ℝ) + 1) * u at hb
  rw [mul_assoc, hx, mul_one] at hb
  exact sub_le_iff_le_add'.2 hb

theorem least_admissibleAt (r : ℕ) : IsLeast {C | AdmissibleAt r C} (finiteConstant r) :=
  ⟨finiteConstant_admissible r, fun _ => finiteConstant_le⟩

/-- The sharp finite-horizon coefficients converge to the sharp uniform coefficient. -/
theorem finiteConstant_tendsto : Tendsto finiteConstant atTop (𝓝 (exp 2 - 1)) := by
  have lim := (((tendsto_one_add_div_pow_exp 1).comp (tendsto_add_atTop_nat 1)).pow 2).sub_const 1
  convert lim using 1
  · ext r
    simp [finiteConstant, pow_mul]
  · norm_num [← exp_nat_mul]

/-- At all horizons together, the least admissible coefficient is exp 2 − 1.
The finite optima approach this number as the horizon grows. -/
theorem least_admissible_all : IsLeast {C | ∀ r, AdmissibleAt r C} (exp 2 - 1) := by
  constructor
  · intro r
    apply (control_iff ..).2
    intro δ hδ hx
    have hg : (1 + δ) ^ ((r + 1) * 2) ≤ (exp δ) ^ ((r + 1) * 2) := by
      gcongr
      linarith [add_one_le_exp δ]
    refine hg.trans ?_
    rw [← exp_nat_mul]
    have Hx := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 2)
      (sub_nonneg.2 hx) (by positivity) (sub_add_cancel ..)
    convert Hx using 1 <;> push_cast <;> simp [smul_eq_mul] <;> ring
  · intro C h
    exact le_of_tendsto finiteConstant_tendsto (Eventually.of_forall fun r => finiteConstant_le (h r))

end Formalism.FourierDecayAlt.P.Rec

namespace Formalism.FourierDecayAlt.P

/-- The original existential bound, witnessed by the least possible coefficient. -/
theorem sharp_recursion : RecursionSharp :=
  Rec.recursionSharp_iff.mpr ⟨_, Rec.least_admissible_all.1⟩

end Formalism.FourierDecayAlt.P
