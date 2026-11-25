module
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
@[expose] public section
noncomputable section
open Finset Filter Topology
namespace ReciprocityTheory.ChartRestriction.DS

/-- Flag-to-Haar conversion at one archimedean place. -/
def flagScale (r : ℕ) : ℝ :=
  2 ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r

def flagVolume (r : ℕ) : ℝ := volU r / flagScale r

theorem flagScale_pos {r : ℕ} (hr : 0 < r) : 0 < flagScale r := by unfold flagScale; positivity

theorem one_le_flagScale {r : ℕ} (hr : 1 ≤ r) : 1 ≤ flagScale r := by
  unfold flagScale
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (by linarith [Real.pi_gt_three]))
  · exact Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hr)

theorem flagVolume_nonneg (r : ℕ) : 0 ≤ flagVolume r := by unfold flagVolume volU flagScale; positivity

private theorem factor_le (n : ℕ) (hn : 3 ≤ n) : Real.pi ^ n ≤ (2 : ℝ) ^ n * n.factorial := by
  induction n, hn using Nat.le_induction with
  | base =>
    calc Real.pi ^ 3 ≤ (3.15 : ℝ) ^ 3 := by gcongr; exact Real.pi_lt_d2.le
      _ ≤ 2 ^ 3 * (Nat.factorial 3 : ℝ) := by norm_num [Nat.factorial]
  | succ n hn ih =>
    have hp : Real.pi ≤ 2 * ((n : ℝ) + 1) := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith [Real.pi_lt_four]
    rw [pow_succ, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
    calc Real.pi ^ n * Real.pi ≤ (2 ^ n * (n.factorial : ℝ)) * (2 * (n + 1)) := by gcongr
      _ = _ := by ring

private theorem flagVolume_step_le {n : ℕ} (hn : 3 ≤ n) : flagVolume (n + 1) ≤ flagVolume n := by
  have hn0 : 0 < n := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
  let n := m + 1
  have ht : (n + 1) * n / 2 = n * m / 2 + n := by
    have he : (n + 1) * n = n * m + 2 * n := by dsimp [n]; ring
    omega
  have hscale : flagScale n * ((2 : ℝ)^n * (2 * Real.pi)) ≤ flagScale (n + 1) := by
    unfold flagScale
    rw [show n + 1 - 1 = n by omega, ht, pow_add, show n - 1 = m by omega, show (2 * Real.pi)^n = (2 * Real.pi)^m * (2 * Real.pi) from pow_succ _ m]
    have hs : Real.sqrt n ≤ Real.sqrt (n + 1 : ℕ) := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)
    calc _ = (2 ^ (n * m / 2) * 2^n * ((2 * Real.pi)^m * (2 * Real.pi))) * Real.sqrt n := by ring
      _ ≤ _ := by gcongr; exact (pow_add (2 : ℝ) (n * m / 2) n).symm.le
  have hfac : 2 * Real.pi^(n+1) / n.factorial ≤ 2^n * (2 * Real.pi) := by
    apply (div_le_iff₀ (by positivity)).2
    rw [pow_succ]
    calc _ ≤ 2 * ((2^n * (n.factorial : ℝ)) * Real.pi) := by gcongr; exact factor_le n hn
      _ = _ := by ring
  have hpos := flagScale_pos hn0
  have hpos' : 0 < flagScale (n+1) := flagScale_pos (by omega)
  change volU (n+1) / flagScale (n+1) ≤ volU n / flagScale n
  rw [div_le_div_iff₀ hpos' hpos, show volU (n+1) = volU n * (2 * Real.pi^(n+1) / n.factorial) from prod_range_succ _ _]
  have hv : 0 ≤ volU n := by unfold volU; positivity
  calc _ ≤ (volU n * (2^n * (2 * Real.pi))) * flagScale n := by gcongr
    _ = volU n * (flagScale n * (2^n * (2 * Real.pi))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale hv

private theorem finite_flag_bound {r : ℕ} {c s : ℝ} (hr : 0 < r) (hc : 0 ≤ c)
    (hs : 0 ≤ s) (hsr : s ≤ Real.sqrt r)
    (h : (∏ i ∈ range r, 2 * (3.15 : ℝ)^(i+1) / (i.factorial : ℝ)) ≤
      c * (2 ^ (r * (r-1) / 2) * (2 * (3.14:ℝ))^(r-1) * s)) : flagVolume r ≤ c := by
  apply (div_le_iff₀ (flagScale_pos hr)).2
  calc volU r ≤ ∏ i ∈ range r, 2 * (3.15 : ℝ)^(i+1) / (i.factorial : ℝ) := by
        unfold volU; gcongr; exact Real.pi_lt_d2.le
    _ ≤ _ := h
    _ ≤ c * flagScale r := by unfold flagScale; gcongr; exact Real.pi_gt_d2.le

/-- The flag conversion absorbs the entire compact volume in ranks at least five. -/
theorem flagVolume_le_one {r : ℕ} (hr : 5 ≤ r) : flagVolume r ≤ 1 := by
  induction r, hr using Nat.le_induction with
  | base =>
    apply finite_flag_bound (s := 2.2) (by decide) zero_le_one (by norm_num)
    · apply Real.le_sqrt_of_sq_le; norm_num
    · norm_num [prod_range_succ, Nat.factorial]
  | succ r hr ih => exact (flagVolume_step_le (by omega)).trans ih

/-- A uniform envelope for the effective volume in the admissible ranks. -/
theorem flagVolume_le_nine_quarters_pow {r : ℕ} (hr : 2 ≤ r) : flagVolume r ≤ (9/4 : ℝ)^(r^2) := by
  by_cases h : 5 ≤ r
  · exact (flagVolume_le_one h).trans (one_le_pow₀ (by norm_num))
  apply finite_flag_bound (s := 1) (by omega) (by positivity) zero_le_one
  · exact Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast (by omega : 1 ≤ r))
  · interval_cases r <;> norm_num [prod_range_succ, Nat.factorial]

/-- In the compact volume the factorials dominate every fixed quadratic-exponential weight. -/
theorem summable_pow_sq_mul_volU (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ => c ^ (n ^ 2) * volU n) := by
  let f := fun n : ℕ => c ^ (n ^ 2) * volU n
  have h₀ (n : ℕ) : 0 ≤ f n := by dsimp [f, volU]; positivity
  have hratio : Tendsto (fun n : ℕ => (2 * Real.pi * c) * ((c ^ 2 * Real.pi)^n / n.factorial)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (c ^ 2 * Real.pi)).const_mul (2 * Real.pi * c)
  apply summable_of_ratio_norm_eventually_le (r := 1/2) (by norm_num)
  filter_upwards [hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hn
  change ‖f (n+1)‖ ≤ 1/2 * ‖f n‖
  rw [Real.norm_of_nonneg (h₀ _), Real.norm_of_nonneg (h₀ _)]
  have step : volU (n+1) = volU n * (2 * Real.pi^(n+1) / n.factorial) := prod_range_succ _ _
  have e : (n+1)^2 = n^2 + (2*n+1) := by ring
  calc f (n+1) = (2 * Real.pi * c) * ((c ^ 2 * Real.pi)^n / n.factorial) * f n := by
        simp only [f, e, step, pow_add, pow_one, ← pow_mul, mul_pow]
        rw [pow_mul]
        ring
    _ ≤ 1/2 * f n := mul_le_mul_of_nonneg_right hn (h₀ n)

/-- No fixed quadratic-exponential archimedean loss survives as the rank tends to infinity. -/
theorem tendsto_pow_sq_mul_flagVolume (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ (n ^ 2) * flagVolume n) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (pow_nonneg hc.le _) (flagVolume_nonneg n)) _
    (summable_pow_sq_mul_volU c hc).tendsto_atTop_zero
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc.le _)
  exact div_le_self (show 0 ≤ volU n by unfold volU; positivity) (one_le_flagScale hn)

end ReciprocityTheory.ChartRestriction.DS
