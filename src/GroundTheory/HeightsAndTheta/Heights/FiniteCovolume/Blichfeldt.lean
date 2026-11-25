module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Tactic

/-! # Blichfeldt's packing bound

The truncated quadratic weights of separated points sum to at most one. Integrating
over one lattice cell bounds the radial integral by its measure. This is the classical
1929 packing argument of H. F. Blichfeldt (doi:10.1007/BF01454863).
-/
@[expose] public section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Metric Set Module Finset
open scoped Interval ENNReal RealInnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Blichfeldt's gauge: the sum of the truncated quadratic weights of any finite
set of λ-separated centers is at most one. -/
private theorem sum_blichfeldt_weight_le_one (s : Finset ι) (v : ι → E) {lam : ℝ}
    (hlam : 0 < lam) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → lam ≤ ‖v i - v j‖) :
    ∑ i ∈ s, max 0 (1 - 2 * ‖v i‖ ^ 2 / lam ^ 2) ≤ 1 := by
  classical
  let t := s.filter fun i => 0 < 1 - 2 * ‖v i‖ ^ 2 / lam ^ 2
  have ht : ∑ i ∈ s, max 0 (1 - 2 * ‖v i‖ ^ 2 / lam ^ 2) =
      ∑ i ∈ t, (1 - 2 * ‖v i‖ ^ 2 / lam ^ 2) := by
    rw [sum_filter]
    exact sum_congr rfl fun i _ => by split_ifs with h <;> grind
  rw [ht]
  rcases t.eq_empty_or_nonempty with h | h
  · simp [h]
  have hn : (0 : ℝ) < t.card := by exact_mod_cast h.card_pos
  have hlow (i) (hi : i ∈ t) :
      (t.card : ℝ) * lam ^ 2 - lam ^ 2 ≤ ∑ j ∈ t, ‖v i - v j‖ ^ 2 := by
    calc
      _ = ∑ j ∈ t, (lam ^ 2 - if i = j then lam ^ 2 else 0) := by simp [sum_sub_distrib, hi]
      _ ≤ _ := by
        refine sum_le_sum fun j hj => ?_
        split_ifs with hij
        · simp [hij]
        · rw [sub_zero]
          exact pow_le_pow_left₀ hlam.le (hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij) 2
  have hall := sum_le_sum hlow
  -- Sum the squared pairwise distances; the remaining squared norm is nonnegative.
  have heq : (∑ i ∈ t, ∑ j ∈ t, ‖v i - v j‖ ^ 2) =
      2 * t.card * (∑ i ∈ t, ‖v i‖ ^ 2) - 2 * ‖∑ i ∈ t, v i‖ ^ 2 := by
    simp_rw [norm_sub_sq_real]
    simp [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← inner_sum, ← sum_inner]
    ring
  rw [heq] at hall
  simp only [sum_const, nsmul_eq_mul] at hall
  have htwo : ((t.card : ℝ) - 1) * lam ^ 2 ≤ 2 * ∑ i ∈ t, ‖v i‖ ^ 2 := by
    apply le_of_mul_le_mul_left (a := (t.card : ℝ)) _ hn
    nlinarith [sq_nonneg ‖∑ i ∈ t, v i‖]
  rw [sum_sub_distrib, ← sum_div, ← mul_sum]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  have hpos := sq_pos_of_pos hlam
  rw [sub_le_iff_le_add', ← sub_le_iff_le_add, le_div_iff₀ hpos]
  linarith

/-- A periodized nonnegative function bounded by one has total mass at most one cell. -/
private theorem packing_integral {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    {μ : Measure V} [μ.IsAddHaarMeasure] {L : AddSubgroup V} [Countable L] {F : Set V}
    (hF : IsAddFundamentalDomain L F μ) {f : V → ℝ} (hf : Continuous f)
    (hint : Integrable f μ) (hpos : ∀ x, 0 ≤ f x)
    (hpack : ∀ (x : V) (s : Finset L), ∑ l ∈ s, f (x + l) ≤ 1) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ F := by
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hpos), hF.lintegral_eq_tsum'']
  rw [← lintegral_tsum]
  · calc
      _ ≤ ∫⁻ _ in F, 1 ∂μ := lintegral_mono fun x ↦ by
        apply CompleteLattice.summable.tsum_le_of_sum_le
        intro s
        change ∑ l ∈ s, ENNReal.ofReal (f ((l : V) + x)) ≤ 1
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ hpos _]
        exact ENNReal.ofReal_le_one.mpr (by simpa only [add_comm x] using hpack x s)
      _ = μ F := by simp
  · intro l
    exact (hf.comp (continuous_const.add continuous_id)).measurable.ennreal_ofReal.aemeasurable

/-- Integrate the radial polynomial up to its cutoff; outside, the weight vanishes. -/
private lemma radial_weight_integral (n : ℕ) {R : ℝ} (hR : 0 < R) :
    ((n : ℝ) + 1) * (∫ r in Ioi (0 : ℝ), r ^ n * max 0 (1 - r ^ 2 / R ^ 2)) =
    (2 / ((n : ℝ) + 3)) * R ^ (n + 1) := by
  let f (r : ℝ) := r ^ n - r ^ (n + 2) * (R ^ 2)⁻¹
  have hi : ∫ r in Ioi (0 : ℝ), r ^ n * max 0 (1 - r ^ 2 / R ^ 2) = ∫ r in 0..R, f r := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Ioc 0 R).indicator f r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only
        have hr' : 0 < r := hr
        by_cases h : r ≤ R
        · rw [indicator_of_mem (show r ∈ Ioc 0 R from ⟨hr', h⟩), max_eq_right]
          · dsimp [f]
            rw [pow_add]
            ring
          · apply sub_nonneg.mpr
            rw [div_le_one₀ (by positivity)]
            exact pow_le_pow_left₀ hr'.le h _
        · rw [indicator_of_notMem (show r ∉ Ioc 0 R from fun ha => h ha.2), max_eq_left, mul_zero]
          apply sub_nonpos.mpr
          rw [one_le_div₀ (by positivity)]
          exact pow_le_pow_left₀ hR.le (le_of_not_ge h) _
      _ = _ := by
        rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self,
          intervalIntegral.integral_of_le hR.le]
  rw [hi]
  dsimp only [f]
  rw [intervalIntegral.integral_sub (f := fun r : ℝ => r ^ n) (g := fun r : ℝ => r ^ (n + 2) * (R ^ 2)⁻¹)
    ((continuous_id.pow _).intervalIntegrable ..)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_mul_const, integral_pow, integral_pow]
  simp only [zero_pow (by omega : n + 1 ≠ 0), zero_pow (by omega : n + 2 + 1 ≠ 0),
    sub_zero, Nat.cast_add, Nat.cast_ofNat]
  rw [show n + 2 + 1 = n + 1 + 2 by omega, pow_add R (n + 1) 2]
  field_simp
  ring

private theorem integral_blichfeldt_weight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {R : ℝ} (hR : 0 < R) :
    (∫ x : E, max 0 (1 - ‖x‖ ^ 2 / R ^ 2) ∂μ) =
    (2 / ((Module.finrank ℝ E : ℝ) + 2)) * μ.real (ball 0 R) := by
  obtain hE | hE := subsingleton_or_nontrivial E
  · rw [(nonempty_ball.mpr hR).eq_zero, ← setIntegral_univ, Set.univ_nonempty.eq_zero,
      integral_singleton, Module.finrank_zero_of_subsingleton]
    simp
  · have hb : μ.real (ball (0 : E) R) = R ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1) := by
      simp only [measureReal_def, μ.addHaar_ball_of_pos (0 : E) hR, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg hR.le _)]
    rw [hb, integral_fun_norm_addHaar μ (fun r => max 0 (1 - r ^ 2 / R ^ 2)), nsmul_eq_mul, smul_eq_mul]
    simp only [smul_eq_mul]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
    rw [hn]
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Nat.cast_succ]
    rw [Nat.succ_eq_add_one]
    have hi := radial_weight_integral n hR
    linear_combination μ.real (ball (0 : E) 1) * hi

private theorem hasCompactSupport_blichfeldt_weight {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {R : ℝ} (hR : 0 < R) : HasCompactSupport (fun x : E => max 0 (1 - ‖x‖ ^ 2 / R ^ 2)) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : E) R) isClosed_closedBall
  intro x hx
  have h : R ≤ ‖x‖ := le_of_lt (by simpa [mem_closedBall] using hx)
  rw [max_eq_left]
  exact sub_nonpos.mpr ((one_le_div₀ (by positivity)).mpr (pow_le_pow_left₀ hR.le h 2))

/-- Blichfeldt's lattice packing bound, before choosing a normalization of Haar measure.
For minimum distance λ, the ball of radius λ/√2 has measure at most (1 + d/2) cells. -/
theorem blichfeldt_ball_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {μ : Measure V} [μ.IsAddHaarMeasure] {L : AddSubgroup V} [Countable L]
    {F : Set V} (hF : IsAddFundamentalDomain L F μ) {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ y ∈ L, y ≠ 0 → lam ≤ ‖y‖) :
    ENNReal.ofReal ((2 / ((finrank ℝ V : ℝ) + 2)) *
      μ.real (ball 0 (lam / Real.sqrt 2))) ≤ μ F := by
  let R := lam / Real.sqrt 2
  have hR : 0 < R := div_pos hlam (Real.sqrt_pos.2 (by norm_num))
  let f (x : V) := max 0 (1 - ‖x‖ ^ 2 / R ^ 2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hpack (x : V) (s : Finset L) : ∑ l ∈ s, f (x + l) ≤ 1 := by
    have he (y : V) : f y = max 0 (1 - 2 * ‖y‖ ^ 2 / lam ^ 2) := by
      dsimp [f, R]
      rw [div_pow, Real.sq_sqrt (by norm_num), div_div_eq_mul_div]
      ring_nf
    simp_rw [he]
    apply sum_blichfeldt_weight_le_one s (fun i : L => x + (i : V)) hlam
    intro i _ j _ hij
    simpa only [add_sub_add_left_eq_sub] using
      hmin (i - j) (L.sub_mem i.property j.property) (sub_ne_zero.mpr fun h => hij (Subtype.ext h))
  rw [← integral_blichfeldt_weight μ hR]
  exact packing_integral hF hf (hf.integrable_of_hasCompactSupport (hasCompactSupport_blichfeldt_weight hR))
    (fun _ => le_max_left _ _) hpack

end GroundTheory.Heights₂.Heights.FiniteCovolume
