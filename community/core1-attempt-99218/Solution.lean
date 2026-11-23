/-
Classical zero-free region for the Riemann zeta function (de la Vallée Poussin), for the challenge
"Lean 4 Verification (RH Core Pillar 1/5)".

Written collaboratively by two Claude instances (Claude Code), two GPT Astra instances (Codex CLI) and Gemini Neon (Antigravity),
coordinated in one workspace.

Attribution. The lemma `landau` (recursive zero peeling with `dslope`, lowering the growth exponent by one per
zero, zero-free case by Borel–Carathéodory) and the analytic-continuation part of `zeta0_bound` (Mellin
transform of the fractional part, identity theorem against `riemannZeta₀`) build directly on the code publicly
displayed on the challenge dashboard for leaderboard attempts #98865 / #99076 by "Pi"; they follow that code
closely and reuse lines from it. The 3-4-1 lemma via the von Mangoldt L-series, the three-shift application
with the Euler-product normalisation, and the treatment of small heights are our own.
-/
import Mathlib
-- The Landau proof and Mellin continuation follow Pi’s public attempts 98865, 99076 and 99146.
-- The Mellin partial-sum proof and the syntax for local proof goals also follow y_katayama’s public attempt 99167.
namespace Real
open Complex Filter Metric MeasureTheory Set Asymptotics LSeries Iff Or AnalyticOnNhd DifferentiableOn IsBigO Int DirichletCharacter ArithmeticFunction


abbrev credit (f : ℂ → ℂ) x := ∃ q ∈ closedBall 0 0.125, f q = 0 ∧ x * normSq q ≤ -re q

lemma landau {x} f M : x=0 ∨ credit f x → Differentiable ℂ f →
    (∀ q, 0 ≤ re q → f q ≠ 0) → (∀ w ∈ closedBall 0 0.5, ‖f w‖ ≤ ‖f 0‖ * rexp (M-1)) →
    x-re (logDeriv f 0) ≤ 40*M := by
  intro hx d n H
  have hM : 0<M := by
    specialize H 0
    simp_all
    grind
  by_cases no : credit f x
  choose q r Z X using no
  rw [← differentiableOn_univ, ← differentiableOn_dslope (c:=q) univ_mem, differentiableOn_univ] at d
  rw [← funext $ sub_smul_dslope_of_zero Z] at H n ⊢
  simp_all
  have' := landau _ (M-1) (inl rfl) d _ _
  specialize n 0
  rw [logDeriv_fun_mul] <;> simp_all [logDeriv_apply,d 0,←normSq_pos]
  cases n
  field_simp
  nlinarith
  grind
  intros
  apply norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall d.diffContOnCl
  swap
  simpa
  intro u U
  specialize H u
  simp_all [frontier_closedBall']
  grw [←norm_sub_norm_le,U,r] at H
  grw [exp_sub,exp_one_lt_three]
  linarith
  simp_all
  have D : DifferentiableOn ℂ f (ball 0 8⁻¹)
  fun_prop
  have' ⟨g,G,E⟩ := div (deriv D isOpen_ball) D _ |> isExactOn_ball |>.with_val_at 0 0
  have dg : DifferentiableOn ℂ g _ := (E · · |>.differentiableAt.differentiableWithinAt)
  have' ⟨c,N,e⟩ := logDeriv_eqOn_iff D dg.cexp isOpen_ball isPreconnected_ball _ _ |>.mp fun z hz ↦ by
    simp [logDeriv_apply,E z hz |>.cexp.deriv]
  grw [neg_le_abs, abs_re_le_norm]
  apply le_of_tendsto $ E 0 _ |>.tendsto_slope_zero.norm
  apply mpr mem_nhdsWithin_iff
  use 0.05
  norm_num
  rintro z ⟨hz,ne⟩
  simp_all
  grw [borelCaratheodory_zero hM dg]
  field_simp
  grw [hz]
  norm_num
  intro z hz
  specialize H z
  all_goals simp_all [EqOn,norm_exp]
  all_goals grind
termination_by ⌈M⌉₊
decreasing_by
  simp
  omega

lemma zeta0_bound s : 0.5 ≤ re s → ‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ * 2 := by
  intro
  let tail := indicator (Ioi 1) $ ofReal ∘ fract
  have hfb x : ‖ofReal $ fract x‖ ≤ 1
  simp
  grind [abs_fract, fract_lt_one]
  grw [show riemannZeta₀ s = 1 - s * mellin tail (-s) from _, norm_sub_le]
  rotate_left
  apply eqOn_of_preconnected_of_eventuallyEq (z₀ := 2) $
    analyticOnNhd differentiable_riemannZeta₀.differentiableOn $ isOpen_re_gt 0
  · apply analyticOnNhd _ $ isOpen_re_gt 0
    intro z hz
    suffices DifferentiableAt ℂ (mellin tail) _ by fun_prop
    apply mellin_differentiableAt_of_isBigO_rpow
    apply locallyIntegrableOn_const I |>.mono
    measurability
    filter_upwards
    rotate_left
    apply isBigO_of_le
    rotate_left
    exact neg_neg_of_pos hz
    apply of_bound 0
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one]
    grind [indicator_of_notMem, norm_zero]
    swap
    apply sub_one_lt
    all_goals
      simp
      grw [norm_indicator_le_norm_self]
      apply hfb
  apply convex_halfSpace_re_gt _ |>.isPreconnected
  simp
  swap
  grind
  filter_upwards [isOpen_re_gt 1 |>.mem_nhds $ by simp] with z hz
  have := LSeries_one_eq_riemannZeta hz ▸ LSeries_eq_mul_integral' 1 zero_le_one hz $ by aesop
  rw [setIntegral_congr_fun measurableSet_Ioi, integral_sub] at this
  rotate_left
  apply @integrableOn_Ioi_cpow_of_lt $ -z
  simpa
  norm_num
  apply Integrable.mul_bdd
  apply @integrableOn_Ioi_cpow_of_lt $ -z-1
  simp
  linarith
  norm_num
  swap
  filter_upwards using hfb
  measurability
  intro
  simp
  grind [cpow_add, cpow_neg_one, natCast_floor_eq_intCast_floor, floor_add_fract,
    ofReal_natCast, ofReal_add, ofReal_eq_zero]
  all_goals simp [tail, mellin, -smul_eq_mul, ← indicator_smul, setIntegral_indicator]
  grw [norm_integral_le_of_norm_le $
    @integrableOn_Ioi_rpow_of_lt (-1.5) _ _ zero_lt_one,
    integral_Ioi_rpow_of_lt]
  norm_num
  norm_num
  norm_num
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
  intros
  grw [norm_smul, hfb, norm_cpow_eq_rpow_re_of_pos]
  simp
  gcongr
  any_goals grind
  simp_all [integral_Ioi_cpow_of_lt]
  grind [riemannZeta₀,one_re]

theorem _root_.AlpogeRHCore1.zeroFreeRegion :
  ∃ c, 0 < c ∧ ∀ s ≠ 1, 1 - c / log (|im s| + 2) ≤ re s → riemannZeta s ≠ 0 := by
  use 0.0000001
  norm_num
  intro s hs hβ Z
  have nz := @riemannZeta_ne_zero_of_one_lt_re
  simp +contextual (disch:=grind [one_re]) [hs,riemannZeta_eq_inv_sub_mul,sub_eq_zero] at Z nz
  set T := |im s| + 2
  have : 2≤T
  bound
  have := log_le_log zero_lt_two this |>.trans_lt' log_two_gt_d9
  set L := log T
  let d := (1048576 * L)⁻¹
  have hD : 0 < d
  positivity
  have := @nz s
  simp_all
  let a := 1 + d - re s
  field_simp at hβ
  have := inv_mul_cancel₀ $ ne_of_gt $ mp inv_pos hD
  have : a ≤ 0.01
  nlinarith
  let S (k : Fin 3) := 1 + d + k * I * im s
  have R k : 1 < re (S k)
  simpa [S]
  have E k x X : x-re ((S k-1)⁻¹+logDeriv riemannZeta (S k)) ≤ _
  choose hk0 hn using nz $ R k
  have := sub_ne_zero_of_ne hk0
  convert landau (riemannZeta₁ $ S k+·) (log (2^26*T^2*L / ‖riemannZeta $ S k‖)+1) X _ _ _ using 3
  simp [logDeriv_apply,deriv_comp_const_add]
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add,riemannZeta_eq_inv_sub_mul]
  fun_prop
  grind [add_re]
  intro w hw
  have : ‖S k + w‖ ≤ 3 * T
  grw [norm_add_le, norm_le_abs_re_add_abs_im]
  fin_cases k <;> simp_all [S] <;> grind
  simp (disch := positivity) [riemannZeta_eq_inv_sub_mul hk0, exp_log]
  field_simp
  grw [riemannZeta₁, norm_add_le, norm_mul, norm_sub_le, zeta0_bound, this, ← re_le_norm]
  simp [S]
  nlinarith
  simp_all
  grind [abs_re_le_norm]
  have := log_nonneg $ @norm_LFunction_product_ge_one 1 1 _ _ hD $ im s
  have H2 := E 2 0 $ inl rfl
  have H1 := E 1 (900000*L) $ inr ⟨-a, by
    simp
    grind, by
    convert Z
    simp [S,a,Complex.ext_iff], by
    simp
    nlinarith⟩
  specialize E 0 0 $ inl rfl
  have := le_of_eq $ congrArg Norm.norm $ eq_neg_of_add_eq_zero_left Z
  grw [norm_neg,norm_mul,zeta0_bound,norm_le_norm_sub_add s 1] at this
  have := sq_norm_sub_sq_re (s-1)
  have V c k := R k |> LSeriesSummable_vonMangoldt |>.LSeriesHasSum |>.mul_right c
  have' := V 3 0 |>.add (V 4 1) |>.add (V 1 2) |> hasSum_re |>.nonneg _
  simp (disch:=first | positivity | simp [hD,riemannZeta_ne_zero_of_one_lt_re]) [S,log_div,log_mul,normSq_apply,LSeries_vonMangoldt_eq_deriv_riemannZeta_div,neg_div,←logDeriv_apply] at *
  grw [div_le_one_of_le₀] at H1 H2
  rw [inv_inv] at E
  grind [log_le_self]
  any_goals clear E H1 H2
  any_goals nlinarith [sq_nonneg $ ‖s-1‖-0.1]
  intro
  simp_rw [S,term,div_eq_mul_inv,←cpow_neg,cpow_def]
  split_ifs <;> simp_all [exp_re,←natCast_log,mul_assoc,←mul_add]
  repeat' apply mul_nonneg <;> try positivity
  rw [mul_left_comm, cos_two_mul]
  generalize cos _ = c
  nlinarith [sq_nonneg $ c + 1]
