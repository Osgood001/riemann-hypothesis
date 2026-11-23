import Mathlib

noncomputable section

open Real hiding dist_eq
open Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul exp_sub
open Topology Metric DirichletCharacter LSeries ZetaAsymptotics Asymptotics
open MeasureTheory hiding norm_integral_le_of_norm_le_const
open _root_.Filter hiding map_map mem_map
open ArithmeticFunction hiding ext log
open Inv
open MulChar hiding mul_apply ext inv
open Finset hiding card_map mem_map ext map_cons sum_cons map_map mem_cons card_le_card
open Set hiding Icc Ioc range ext card_le_card mem_Icc
open Multiset hiding Icc Ioc ext range mem_Icc
open Or (inl inr resolve_left)
open Iff (mp mpr)
open LE.le (trans_eq)
open NeZero (pos ne)
open Option (elim elim_none elim_some eq_none_iff_forall_ne_some)
open Option.some (inj)
open Filter.Eventually (of_forall)
open ZMod (isUnit_iff_coprime natCast_zmod_val cast_natCast)
open Nat (cast_nonneg cast_pos cast_pow cast_ne_zero cast_le cast_sub cast_two floor_le floor_mono lt_floor_add_one floor_pos le_floor_iff lt_of_floor_lt floor_le_of_le measurable_floor ceil_add_one le_ceil ceil_pos ceil_lt_add_one succ_pos prime_of_mem_primeFactors one_le_iff_ne_zero factorial_ne_zero mem_divisorsAntidiagonal exists_eq_succ_of_ne_zero strong_induction_on add_sub_of_le dvd_prime_pow sum_divisors_prime_pow even_or_odd coprime_mul_iff_right card_Ioc mem_divisors le_log_of_pow_le pow_le_pow_left pow_log_le_self)
open intervalIntegral (integral_eq_sub_of_hasDerivAt integral_of_le norm_integral_le_of_norm_le_const integral_congr integral_add intervalIntegrable_cpow')
open scoped Classical Real LSeries.notation ArithmeticFunction.Moebius

abbrev a1 := @And.left
abbrev a2 := @And.right
abbrev clog := Complex.log

abbrev cR (x : ℝ) : ℂ := x
abbrev rN (n : ℕ) : ℝ := n
abbrev cN (n : ℕ) : ℂ := n
abbrev r0 : ℝ := 0
abbrev r1 : ℝ := 1

lemma dist_mk_im (w : ℂ) (x : ℝ) : dist w (mk x (im w)) = abs (re w - x) := by
  rw [dist_eq_norm, show w - mk x (im w) = cR (re w - x) by apply ext <;> simp, norm_real, norm_eq_abs]

lemma norm_cR_nn {x : ℝ} (hx : 0 ≤ x := by first | positivity | linarith) : ‖cR x‖ = x := by
  rw [norm_real, norm_of_nonneg hx]

lemma divLe {a b c : ℝ} (h : a ≤ c * b) (hb : 0 < b := by first | positivity | linarith) : a / b ≤ c := mpr (div_le_iff₀ hb) h
lemma leDiv {a b c : ℝ} (h : a * b ≤ c) (hb : 0 < b := by first | positivity | linarith) : a ≤ c / b := mpr (le_div_iff₀ hb) h
lemma invLe {a b : ℝ} (h : a ≤ b) (ha : 0 < a := by first | positivity | linarith) : inv b ≤ inv a := inv_anti₀ ha h
lemma logLe {a b : ℝ} (h : a ≤ b) (ha : 0 < a := by first | positivity | linarith) : log a ≤ log b := log_le_log ha h
lemma rpowLe {a b c : ℝ} (h : b ≤ c) (ha : 1 ≤ a := by linarith) : a ^ b ≤ a ^ c := rpow_le_rpow_of_exponent_le ha h
lemma sqExpLe {x : ℝ} (hx : 0 ≤ x := by first | positivity | linarith) : x ^ 2 * exp (-x) ≤ 2 := by
  rw [exp_neg, ← div_eq_mul_inv, div_le_iff₀ $ exp_pos x]
  linarith [quadratic_le_exp_of_nonneg hx]

def rectInt (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℂ :=
  (∫ x in x0..x1, g (mk x y0)) - (∫ x in x0..x1, g (mk x y1)) +
    I * (∫ y in y0..y1, g (mk x1 y)) - I * (∫ y in y0..y1, g (mk x0 y))

lemma mellin_strip {f : ℂ → ℂ} {g : ℝ → ℂ} {A C : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C) (hf : Differentiable ℂ f)
    (hgm : Measurable g) (hgb : ∀ x, ‖g x‖ ≤ C)
    (heq : ∀ {z}, 1 < re z → f z = z * ∫ x in Ioi A, cR x ^ (-z - 1) * g x)
    {s} (hs : 0 < re s) : ‖f s‖ ≤ C * (norm s / re s) * A ^ (-re s) := by
  have hA0 : 0 < A := by linarith
  let F := indicator (Ioi A) g
  have hme z : mellin F (-z) = ∫ x in Ioi A, cR x ^ (-z - 1) * g x := by
    rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi, mpr inter_eq_right $ Ioi_subset_Ioi hA0.le]
    simp
  have hfs : f s = s * mellin F (-s) := by
    apply (hf.differentiableOn.analyticOnNhd $ isOpen_re_gt 0).eqOn_of_preconnected_of_eventuallyEq _
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) _ _ hs
    apply DifferentiableOn.analyticOnNhd _ $ isOpen_re_gt 0
    intro z hz
    suffices DifferentiableAt ℂ (mellin F) (-z) by fun_prop
    apply mellin_differentiableAt_of_isBigO_rpow (a := 0)
    apply (locallyIntegrableOn_const C).mono (hgm.indicator measurableSet_Ioi).aestronglyMeasurable
    exact of_forall fun x => by simpa [ norm_of_nonneg hC] using le_trans (norm_indicator_le_norm_self _ _) $ hgb x
    exact IsBigO.of_bound C $ of_forall fun x => by simpa using le_trans (norm_indicator_le_norm_self _ _) $ hgb x
    simpa using hz
    apply IsBigO.of_bound 0
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    simp [F, show ¬ A < x by grind]
    swap
    apply sub_one_lt
    norm_num
    filter_upwards [(isOpen_re_gt 1).mem_nhds $ by norm_num] with z hz
    grind
  rw [hfs, hme, norm_mul]
  grw [norm_integral_le_of_norm_le (g := fun x => C * x ^ (-re s - 1)), integral_const_mul, integral_Ioi_rpow_of_lt]
  simp
  grind
  linarith
  assumption
  apply Integrable.const_mul
  apply integrableOn_Ioi_rpow_of_lt
  linarith
  assumption
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  grw [norm_mul, hgb x, norm_cpow_eq_rpow_re_of_pos $ lt_trans hA0 hx]
  simp [mul_comm]

lemma zeta0_growth_half {s : ℂ} (hs : 0.5 ≤ re s) : ‖riemannZeta₀ s‖ ≤ 1 + 2 * norm s := by
  have hs' : 0 < re s := by positivity
  have hfb x : ‖ofReal $ Int.fract x‖ ≤ 1 := by
    simp
    grind [Int.abs_fract, Int.fract_lt_one]
  rw [show riemannZeta₀ s = 1 - (1 - riemannZeta₀ s) by ring]
  grw [norm_sub_le,
    mellin_strip (f := fun z => 1 - riemannZeta₀ z) le_rfl zero_le_one
      ((differentiable_const 1).sub differentiable_riemannZeta₀) (by measurability) hfb _ hs',
    divLe (c := 2 * norm s) $ by nlinarith [norm_nonneg s]]
  simp
  intro z hz
  have h := LSeries_one_eq_riemannZeta hz ▸ LSeries_eq_mul_integral' 1 zero_le_one hz $ by simp
                                                                                           rfl
  simp at h
  rw [setIntegral_congr_fun measurableSet_Ioi ?_, integral_sub] at h
  rotate_left
  apply integrableOn_Ioi_cpow_of_lt (a := -z)
  simpa
  norm_num
  apply Integrable.mul_bdd
  apply integrableOn_Ioi_cpow_of_lt (a := -z - 1)
  simp
  linarith
  norm_num
  swap
  exact of_forall hfb
  measurability
  intro x hx
  have hx0 := lt_trans zero_lt_one hx.out
  simp [Int.fract, ← Int.natCast_floor_eq_floor $ le_of_lt hx0, neg_add_eq_sub, cpow_sub, ne_of_gt hx0, mul_sub]
  grind
  rw [integral_Ioi_cpow_of_lt] at h
  simp at *
  grind [riemannZeta₀, one_re]
  simpa
  norm_num

theorem l_function_partial_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hx_ : χ ≠ 1)
    (s : ℂ) (hs : 0 < re s) (N : ℕ) (hN : 1 ≤ N) :
    ‖LFunction χ s - ∑ n ∈ Icc 1 N, χ (n : ZMod q) * cN n ^ (-s)‖ ≤
      2 * rN q * (norm s / re s) * rN N ^ (-re s) := by
  have hN1 : r1 ≤ N := by exact_mod_cast hN
  let Ap n : ℂ := ∑ k ∈ range n, χ k
  have hzero : Ap q = 0 := by
    obtain ⟨m, rfl⟩ := exists_eq_succ_of_ne_zero $ ne q
    dsimp [Ap]
    rw [← Fin.sum_univ_eq_sum_range, ← sum_eq_zero_of_ne_one hx_]
    exact sum_congr rfl fun (i : ZMod $ m + 1) _ => congrArg χ $ natCast_zmod_val i
  have hB K : ‖Ap K‖ ≤ q := by
    induction K using strong_induction_on with | _ K ih =>
      by_cases hK : K < q
      grw [norm_sum_le, sum_le_sum fun _ _ => norm_le_one χ _]
      simpa using le_of_lt hK
      rw [show Ap K = Ap (K - q) by rw [← add_sub_of_le $ mp not_lt hK]; simp [Ap, sum_range_add, hzero]]
      apply ih
      have := pos q
      omega
  let g k : ℂ := if k ≤ N then 0 else χ k
  let S m := ∑ k ∈ Icc 1 m, g k
  have hSeq m : S m = if m ≤ N then 0 else Ap (m + 1) - Ap (N + 1) := by
    induction m with
    | zero => simp [S]
    | succ m ih =>
      dsimp [S] at ih ⊢
      rw [sum_Icc_succ_top $ succ_pos _, ih]
      split_ifs <;> grind [sum_range_succ]
  have hSb m : ‖S m‖ ≤ 2 * q := by
    rw [hSeq]
    split_ifs
    simp
    linarith [norm_sub_le (Ap $ m + 1) $ Ap $ N + 1, hB $ m + 1, hB $ N + 1]
  apply mellin_strip hN1 (by positivity) _
    ((measurable_from_top (f := S)).comp measurable_floor) (fun x => hSb ⌊x⌋₊) _ hs
  apply (differentiable_LFunction hx_).fun_sub
  apply Differentiable.fun_sum
  intro n hn
  fun_prop (disch := left; exact mpr cast_ne_zero $ by rw [mem_Icc] at hn; omega)
  intro z hz
  have hSx := LSeriesSummable_of_one_lt_re χ hz
  have hSg : LSeriesSummable g z := by
    apply Summable.of_norm_bounded hSx.norm
    intro n
    simp [norm_term_eq, g]
    split_ifs <;> simp
    positivity
  have hLg : LFunction χ z - ∑ n ∈ Icc 1 N, χ n * n ^ (-z) = LSeries g z := by
    rw [LFunction_eq_LSeries χ hz, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_comm,
      LSeries, LSeries, ← hSx.tsum_sub hSg, tsum_eq_sum]
    apply sum_congr rfl
    intro n hn
    rw [mem_Icc] at hn
    simp [term_of_ne_zero $ show n ≠ 0 by omega, g, a2 hn, div_eq_mul_inv, cpow_neg]
    intro n hn
    simp [term_def, g]
    split_ifs <;> simp_all
  rw [hLg, LSeries_eq_mul_integral g le_rfl (by linarith) hSg]
  congr 1
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi $ Ioi_subset_Ioi hN1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  grind
  intro x hx
  have : S ⌊x⌋₊ = 0 := by simp [hSeq, floor_le_of_le $ mp not_lt $ by simpa using a2 hx]
  grind
  exact IsBigO.of_bound (2 * q) $ of_forall fun n => by simpa using hSb n

def Sa (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n * cR (1 - n / x)

theorem localZeroDslope {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c 0.5)) (hf0 : f c ≠ 0)
    (hbd : ∀ z ∈ closedBall c 0.5, ‖f z‖ ≤ ‖f c‖ * exp M) :
    ∃ Z : Multiset ℂ,
      (∀ rho : ℂ, rho ∈ Z ↔ rho ∈ closedBall c 0.13 ∧ f rho = 0) ∧
      (∀ rho ∈ Z, rho ∉ Z.erase rho ↔ deriv f rho ≠ 0) ∧
      (Z.card : ℝ) ≤ M ∧
      ∀ z ∈ closedBall c 0.08, f z ≠ 0 →
        ‖deriv f z / f z - (Z.map fun rho => inv (z - rho)).sum‖ ≤ 336 * (M + 1) := by
  have hM : 0 ≤ M := by simpa [hf0] using hbd c $ mem_closedBall_self $ by norm_num
  by_cases hex : ∃ rho0 ∈ closedBall c 0.13, f rho0 = 0
  obtain ⟨rho0, hρ₀, hfρ₀⟩ := hex
  rw [← differentiableOn_dslope $ closedBall_mem_nhds_of_mem $ closedBall_subset_ball (by norm_num) hρ₀] at hf
  rw [← funext $ sub_smul_dslope_of_zero hfρ₀] at hbd hf0 ⊢
  simp at hf0
  have hgbd z (hz : z ∈ closedBall c 0.5) : ‖dslope f rho0 z‖ ≤ ‖dslope f rho0 c‖ * exp (M - 1) := by
    apply norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
    apply DifferentiableOn.diffContOnCl
    simpa
    intro w hw
    simp [frontier_closedBall', mem_sphere_iff_norm] at hw
    have h1 := hbd w $ by simp [dist_eq_norm, hw]
    simp at h1
    have := mp mem_closedBall_iff_norm hρ₀
    grw [norm_sub_rev c, this, ← show 0.37 ≤ ‖w - rho0‖ by linarith [norm_sub_le_norm_sub_add_norm_sub w rho0 c]] at h1
    grw [exp_sub, exp_one_lt_d9]
    have : 0 ≤ ‖dslope f rho0 c‖ * exp M := by positivity
    grind
    simpa
  obtain ⟨Z', hZ', hmult', hsum', hder'⟩ := localZeroDslope hf (a2 hf0) hgbd
  have hdg u (hu : u ∈ closedBall c 0.13) := hf.differentiableAt $ closedBall_mem_nhds_of_mem $ closedBall_subset_ball (by norm_num) hu
  have hmul_deriv rho (hr_ : rho ∈ closedBall c 0.13) :
      deriv (fun x => (x - rho0) • dslope f rho0 x) rho = dslope f rho0 rho + (rho - rho0) * deriv (dslope f rho0) rho := by
    simp
    rw [deriv_fun_mul (by fun_prop) $ hdg rho hr_]
    simp
  refine ⟨rho0 ::ₘ Z', fun rho => ?_, fun rho hr_ => ?_, by simp
                                                            linarith, fun z hz hfz => ?_⟩
  rw [mem_cons, hZ']
  simp only [smul_eq_mul, mul_eq_zero, sub_eq_zero]
  grind
  rcases eq_or_ne rho rho0 with rfl | hne
  rw [erase_cons_head, hZ', hmul_deriv rho hρ₀]
  grind
  have hrZ' := (mp mem_cons hr_).resolve_left hne
  obtain ⟨h1, h2⟩ := mp (hZ' rho) hrZ'
  rw [erase_cons_tail Z' (symm hne), mem_cons, not_or, hmult' rho hrZ', hmul_deriv rho h1, h2, zero_add]
  grind
  simp at hfz
  simp only [smul_eq_mul]
  rw [← logDeriv_apply, logDeriv_fun_mul, map_cons, sum_cons]
  simp [logDeriv_apply, one_div]
  grind
  exact a1 hfz
  exact a2 hfz
  fun_prop
  apply hdg z $ closedBall_subset_closedBall _ hz
  norm_num
  refine ⟨0, fun rho => ⟨by simp, fun h => absurd ⟨rho, h⟩ hex⟩, by simp, by simpa, fun z hz _ => ?_⟩
  have hfb := hf.mono $ ball_subset_closedBall.trans $ closedBall_subset_closedBall (ε₁ := 0.13) $ by norm_num
  have hneb w hw : f w ≠ 0 := fun h0 => hex ⟨w, ball_subset_closedBall hw, h0⟩
  obtain ⟨g, hg0, hgd⟩ := ((hfb.deriv isOpen_ball).div hfb hneb).isExactOn_ball.with_val_at c 0
  have hg_diff : DifferentiableOn ℂ g _ := (hgd · · |>.differentiableAt.differentiableWithinAt)
  obtain ⟨k, hk, hfg⟩ := mp (logDeriv_eqOn_iff hfb hg_diff.cexp isOpen_ball isPreconnected_ball (by simp) hneb)
    fun u hu => by simp [logDeriv_apply, (hgd u hu).cexp.deriv]
  have hsub : closedBall z 0.025 ⊆ ball c 0.13 := fun w hw => by
    simp [dist_eq_norm]
    linarith [mp mem_closedBall_iff_norm hz, mp mem_closedBall_iff_norm hw, norm_sub_le_norm_sub_add_norm_sub w z c]
  have hvc {v} (hv : v ∈ ball 0 0.13) : c + v ∈ ball c 0.13 := by simpa using hv
  rw [Multiset.map_zero, sum_zero, sub_zero, ← Pi.div_apply, ← (hgd z $ hsub $ mem_closedBall_self $ by norm_num).deriv]
  grw [norm_deriv_le_of_forall_mem_sphere_norm_le (R := 0.025) (C := 8.4 * (M + 1)) (by norm_num) $ (hg_diff.mono hsub).diffContOnCl_ball subset_rfl]
  grind
  intro w hw
  have : ‖w - c‖ ≤ 0.105 := by
    linarith [mp mem_closedBall_iff_norm hz, mp mem_sphere_iff_norm hw, norm_sub_le_norm_sub_add_norm_sub w z c]
  grw [show g w = (fun v => g $ c + v) (w - c) by simp,
    borelCaratheodory_zero (f := fun v => g $ c + v) (M := M + 1) (by linarith) $ hg_diff.comp (differentiable_id.const_add c).differentiableOn fun _ => hvc]
  exact divLe $ by nlinarith
  intro v hv
  have h := hbd (c + v) $ closedBall_subset_closedBall (by norm_num) $ ball_subset_closedBall $ hvc hv
  simp_all [hfg $ hvc hv, hfg $ mem_ball_self $ by norm_num, norm_exp]
  linarith
  norm_num
  apply mpr mem_ball_zero_iff
  linarith
  simpa using hg0
termination_by ⌈M + 1⌉₊
decreasing_by simp [ceil_add_one hM]

abbrev DC (q : ℕ) := DirichletCharacter ℂ q
abbrev c1 : DC 1 := 1
lemma c1a (x : ZMod 1) : c1 x = 1 := Subsingleton.elim x 1 ▸ map_one c1
abbrev Good {q : ℕ} (χ : DC q) := χ ≠ 1 ∨ q = 1
abbrev lcond (q : ℕ) (t : ℝ) : ℝ := log (rN q * (abs t + 2))
abbrev slog (x : ℝ) : ℝ := sqrt (log x)
abbrev zterm (y β : ℝ) : ℂ := cR y ^ cR β / (cR β * (cR β + 1))

def InRegion (c : ℝ) (q : ℕ) (s : ℂ) : Prop := 1 - c / lcond q (im s) ≤ re s
abbrev partialSumUpTo (f : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊x⌋₊, f n
def Schi {q : ℕ} (χ : DC q) (y : ℝ) : ℂ := Sa (fun n => ↑(Λ n) * χ n) y

lemma one_le_modulus_real (q : ℕ) [NeZero q] : r1 ≤ q := by exact_mod_cast one_le_iff_ne_zero.2 (ne q)
lemma lcond_ge_const (q : ℕ) [NeZero q] (t : ℝ) : 0.69 ≤ lcond q t := by
  linarith [log_two_gt_d9, log_le_log two_pos (by nlinarith [one_le_modulus_real q, abs_nonneg t] : 2 ≤ rN q * (abs t + 2))]
lemma lcond_pos (q : ℕ) [NeZero q] (t : ℝ) : 0 < lcond q t := by linarith [lcond_ge_const q t]

section
variable {q : ℕ} [NeZero q]

abbrev L1 (χ : DC q) : ℂ → ℂ := if χ = 1 then riemannZeta₁ else LFunction χ
def IsLZero (χ : DC q) (s : ℂ) : Prop := (χ ≠ 1 ∨ s ≠ 1) ∧ LFunction χ s = 0
def ExcZeros (c1_ : ℝ) (χ : DC q) (bet0 : Option ℝ) : Prop :=
  (∀ β ∈ bet0, χ ≠ 1 ∧ 0.5 ≤ β ∧ β < 1 ∧ InRegion c1_ q (cR β) ∧ LFunction χ (cR β) = 0 ∧
    deriv (LFunction χ) (cR β) ≠ 0 ∧ χ ^ 2 = 1) ∧
  ∀ s : ℂ, InRegion c1_ q s → IsLZero χ s → ∃ β ∈ bet0, s = cR β
def negLD (χ : DC q) (s : ℂ) : ℂ := -(deriv (LFunction χ) s / LFunction χ s)
def Fchi (χ : DC q) (y : ℝ) (w : ℂ) : ℂ := negLD χ w * y ^ w / (w * (w + 1))

theorem lfunction_polynomial_growth (χ : DC q) (hx_ : χ ≠ 1)
    (s : ℂ) (hs : 0.5 ≤ re s) : ‖LFunction χ s‖ ≤ 5 * q * (1 + norm s) := by
  have hs' : 0 < re s := by positivity
  have hP := l_function_partial_sum χ hx_ s hs' 1 le_rfl
  simp at hP
  grw [norm_le_insert' _ 1, hP, divLe (c := 2 * norm s) $ by nlinarith [norm_nonneg s]]
  simp
  nlinarith [one_le_modulus_real q, norm_nonneg s]

lemma negLD_eq_LSeries_mul_vonMangoldt (χ : DC q) {s : ℂ} (hs : 1 < re s) :
    negLD χ s = LSeries (↗χ * ↗Λ) s := by
  unfold negLD
  rw [LSeries_twist_vonMangoldt_eq χ hs,
    deriv_LFunction_eq_deriv_LSeries χ hs,
    LFunction_eq_LSeries χ hs]
  ring

lemma lfunction_norm_near_one (χ : DC q) (hx_ : χ ≠ 1) {w : ℂ} {dl : ℝ}
    (hd : 0 ≤ dl) (hw : 1 - dl ≤ re w) (hw4 : 0.5 ≤ re w := by norm_num) (hw2 : norm w ≤ 2 := by norm_num) :
    ‖LFunction χ w‖ ≤ (9 + log q) * rN q ^ dl := by
  have hq := one_le_modulus_real q
  grw [norm_le_insert' _ (∑ n ∈ Icc 1 q, χ n * cN n ^ (-w)), norm_sum_le, sum_le_sum (g := fun n => rN q ^ dl * inv (rN n)), ← mul_sum,
    show ∑ n ∈ Icc 1 q, inv (rN n) = harmonic q by simp [harmonic_eq_sum_Icc],
    harmonic_le_one_add_log q, l_function_partial_sum χ hx_ w (by linarith) q $ pos q, divLe (c := 4) $ by linarith]
  rw [mul_right_comm (2 * rN q) 4, mul_assoc 2, mul_comm $ rN q, ← rpow_add_one $ by linarith]
  grw [rpowLe $ show -re w + 1 ≤ dl by linarith]
  linarith
  intro n hn
  obtain ⟨h1, h2⟩ := mp mem_Icc hn
  have hn0 : 0 < rN n := mpr cast_pos h1
  rw [norm_mul, norm_natCast_cpow_of_pos h1, neg_re,
    show -re w = 1 - re w + -1 by ring, rpow_add hn0, rpow_neg_one]
  grw [norm_le_one χ _, rpowLe (show 1 - re w ≤ dl by linarith) $ by exact_mod_cast h1,
    rpow_le_rpow (le_of_lt hn0) (mpr cast_le h2) hd]
  simp

lemma negLD_341 {r : ℕ} [NeZero r] (χ : DC q) (ψ : DC r)
    (hψ : ∀ n : ℕ, IsUnit (n : ZMod q) → ψ n = χ n ^ 2) {σ : ℝ} (hs : 1 < σ) (t : ℝ) :
    0 ≤ 3 * re (negLD c1 σ) + 4 * re (negLD χ (mk σ t)) + re (negLD ψ (mk σ (2 * t))) := by
  have hS {m : ℕ} [NeZero m] (φ : DC m) u c :
      HasSum (fun n => c * re (term (↗φ * ↗Λ) (mk σ u) n)) (c * re (negLD φ (mk σ u))) := by
    rw [negLD_eq_LSeries_mul_vonMangoldt φ hs]
    exact (hasSum_re (LSeriesSummable_twist_vonMangoldt φ hs).hasSum).mul_left c
  simpa [mk_eq_add_mul_I] using (((hS c1 0 3).add $ hS χ t 4).add $ hS ψ (2 * t) 1).nonneg fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    simp
    have hre {m : ℕ} [NeZero m] (φ : DC m) u :
        re (term (↗φ * ↗Λ) (mk σ u) n) = Λ n / n ^ σ * re (φ n / n ^ (u * I)) := by
      rw [mk_eq_add_mul_I, term_of_ne_zero hn, cpow_add _ _ $ mpr cast_ne_zero hn, ← re_ofReal_mul]
      congr 1
      push_cast
      rw [ofReal_cpow $ cast_nonneg n]
      simp
      ring
    rw [hre, hre, hre]
    simp only [mul_one, one_mul, ofReal_zero, zero_mul, cpow_zero, div_one, c1a, one_re]
    have : 0 ≤ Λ n / n ^ σ := by positivity
    have hcp u : ‖cN n ^ (cR u * I)‖ = 1 := by
      rw [norm_natCast_cpow_of_pos $ pos_of_ne_zero hn]
      simp
    by_cases hu : IsUnit (n : ZMod q)
    set w := χ n / cN n ^ (cR t * I) with hw
    have : re w * re w + im w * im w ≤ 1 := by
      rw [← normSq_apply, normSq_eq_norm_sq]
      nlinarith [norm_nonneg w, show norm w ≤ 1 by simp [w, hcp, norm_le_one χ _]]
    rw [hψ n hu, show cR (2 * t) * I = cN 2 * (t * I) by push_cast; ring, cpow_nat_mul, ← div_pow, ← hw, sq, mul_re]
    nlinarith [sq_nonneg $ 1 + re w]
    rw [map_nonunit χ hu, zero_div, zero_re]
    have := neg_abs_le $ re $ ψ n / cN n ^ (cR (2 * t) * I)
    grw [abs_re_le_norm, norm_div, hcp, norm_le_one ψ n] at this
    nlinarith

lemma zeta1_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ $ sub_ne_zero_of_ne hs]

lemma L1_eq_zero_iff {χ : DC q} (hxq_ : Good χ) {s : ℂ} :
    L1 χ s = 0 ↔ IsLZero χ s := by
  by_cases h1 : χ = 1
  obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not h1
  subst h1
  simp [L1, IsLZero]
  exact ⟨fun h => have hs1 : s ≠ 1 := fun hs => by simp [hs] at h
    ⟨hs1, by have := zeta1_eq hs1
             grind⟩, fun ⟨hs1, hz_⟩ => by rw [zeta1_eq hs1, hz_, mul_zero]⟩
  simp [L1, IsLZero, h1]

lemma L1_ne_zero_of_one_le_re {χ : DC q} (hxq_ : Good χ)
    {s : ℂ} (hs : 1 ≤ re s) : L1 χ s ≠ 0 := fun h => by
  obtain ⟨hne, h0⟩ := mp (L1_eq_zero_iff hxq_) h
  exact LFunction_ne_zero_of_one_le_re χ hne hs h0

lemma L1_log_deriv {χ : DC q} (hxq_ : Good χ)
    {s : ℂ} (hs : χ ≠ 1 ∨ s ≠ 1) (hL : L1 χ s ≠ 0) :
    deriv (L1 χ) s / L1 χ s = -negLD χ s + (if χ = 1 then 1 / (s - 1) else 0) := by
  by_cases h1 : χ = 1
  obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not h1
  subst h1
  simp [negLD] at hL ⊢
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add, riemannZeta_eq_inv_sub_mul]
  simp [L1, negLD, h1]

lemma L1_local_expansion (χ : DC q) (hxq_ : Good χ) (t : ℝ) :
    ∃ Z : Multiset ℂ,
      (∀ rho, rho ∈ Z ↔ rho ∈ closedBall (mk 1.05 t) 0.13 ∧ L1 χ rho = 0) ∧
      (∀ rho ∈ Z, rho ∉ Z.erase rho ↔ deriv (L1 χ) rho ≠ 0) ∧
      rN Z.card ≤ 16 * lcond q t ∧
      (∀ z ∈ closedBall (mk 1.05 t) 0.08, L1 χ z ≠ 0 →
        ‖deriv (L1 χ) z / L1 χ z - (Z.map fun rho => inv (z - rho)).sum‖ ≤ 5900 * lcond q t) ∧
      ∀ σ, 1 < σ → σ ≤ 1.1 →
        (∀ rho ∈ Z, 0 ≤ re (inv (mk σ t - rho))) ∧
        re (negLD χ (mk σ t)) ≤ (if χ = 1 then re (inv (mk (σ - 1) t)) else 0) + 5900 * lcond q t - (Z.map fun rho => re (inv (mk σ t - rho))).sum ∧
        re (negLD χ (mk σ t)) ≤ (if χ = 1 then re (inv (mk (σ - 1) t)) else 0) + 5900 * lcond q t := by
  let z0_ := mk 1.05 t
  let T2 := abs t + 2
  have := one_le_modulus_real q
  have hqT : 2 ≤ q * T2 := by nlinarith [abs_nonneg t]
  have hlow : 1 ≤ 420 * ‖L1 χ z0_‖ := by
    have hs : 1 < re z0_ := by norm_num
    have h21 : 1 ≤ 21 * ‖LFunction χ z0_‖ := by
      have hS1 := (mpr LSeriesSummable_one_iff hs).norm
      have haux := zeta_limit_aux1 hs
      have htnn : 0 ≤ termTSum (re z0_) := tsum_nonneg fun _ => term_nonneg _ _
      grw [← @norm_one ℂ, ← mul_mu_eq_one χ hs, ← LFunction_eq_LSeries χ hs, norm_mul, LSeries,
        tsum_of_norm_bounded hS1.hasSum, hS1.tsum_eq_zero_add]
      simp_rw [norm_term_eq]
      simp [z0_] at haux htnn ⊢
      nlinarith [norm_nonneg $ LFunction χ $ mk 1.05 t]
      intro n
      apply norm_term_le
      simp
      grw [norm_le_one χ _]
      simp
      exact_mod_cast abs_moebius_le_one
    by_cases h1 : χ = 1
    obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not h1
    have : 0.05 ≤ ‖z0_ - 1‖ := by grw [← re_le_norm]
                                  simp
                                  norm_num
    subst h1
    simp [L1] at h21 ⊢
    rw [zeta1_eq $ mp sub_ne_zero $ mp norm_pos_iff $ by linarith, norm_mul]
    nlinarith
    simp [L1, h1]
    nlinarith
  have hbound z (hz : z ∈ closedBall z0_ 0.5) : ‖L1 χ z‖ ≤ ‖L1 χ z0_‖ * exp (16 * lcond q t) := by
    have := mp mem_closedBall_iff_norm hz
    have hre : 0.5 ≤ re z := by
      linarith [a1 $ mp abs_le $ abs_re_le_norm $ z - z0_, show re (z - z0_) = re z - 1.05 by simp [z0_]]
    have hsq : (norm z + 1) ^ 2 ≤ 4 * T2 ^ 2 := by
      have : norm z0_ ≤ 1.05 + abs t := by grw [norm_le_abs_re_add_abs_im]
                                           simp [z0_]
                                           norm_num
      nlinarith [norm_sub_norm_le z z0_, norm_nonneg z, abs_nonneg t]
    have hLz : ‖L1 χ z‖ ≤ 7 * rN q * (norm z + 1) ^ 2 := by
      dsimp [L1]
      split_ifs with h1
      rw [riemannZeta₁]
      grw [norm_add_le, norm_mul, norm_sub_le, zeta0_growth_half hre]
      simp
      nlinarith [norm_nonneg z]
      nlinarith [lfunction_polynomial_growth χ h1 z hre, show 1 + norm z ≤ (norm z + 1) ^ 2 by nlinarith [norm_nonneg z]]
    rw [show 16 = rN 16 by norm_num, exp_nat_mul, exp_log $ by positivity]
    grw [hLz, hsq, show rN q ≤ rN q ^ 2 by nlinarith]
    have : 11760 * (q * T2) ^ 2 ≤ (q * T2) ^ 16 := by
      grw [show (11760 : ℝ) ≤ 2 ^ 14 by norm_num, hqT]
      grind
    nlinarith
  obtain ⟨Z, hZ, hmult, hsum, hbd⟩ := localZeroDslope
    (by dsimp [L1]; split_ifs with h; exacts [differentiable_riemannZeta₁, differentiable_LFunction h] : Differentiable ℂ $ L1 χ).differentiableOn
    (fun h => by norm_num [h] at hlow) hbound
  have := lcond_ge_const q t
  refine ⟨Z, hZ, hmult, hsum, fun z hz hnz => by grind, fun σ hs1_ hs2 => ?_⟩
  let w := mk σ t
  have hwne := L1_ne_zero_of_one_le_re hxq_ (s := w) $ le_of_lt hs1_
  have h1 := (re_le_norm $ -_).trans $ (norm_neg _).trans_le $ hbd w (by
    rw [mem_closedBall, dist_mk_im w 1.05, abs_le]
    grind) hwne
  have hld := congrArg re $ L1_log_deriv hxq_ (inr fun h => by simp [ Complex.ext_iff] at h; linarith) hwne
  rw [neg_re, sub_re, show re _ = (Z.map fun rho => re $ inv $ w - rho).sum from (map_multiset_sum reAddGroupHom _).trans $ by rw [map_map]; rfl] at h1
  rw [add_re, neg_re, show w - 1 = mk (σ - 1) t by apply ext <;> simp [w]] at hld
  rw [hld] at h1
  have hnn rho (hr_ : rho ∈ Z) : 0 ≤ re (inv (mk σ t - rho)) := by
    have := lt_of_not_ge (L1_ne_zero_of_one_le_re hxq_ · $ a2 $ mp (hZ rho) hr_)
    rw [inv_re]
    exact div_nonneg (by simp; linarith) $ normSq_nonneg _
  have := sum_nonneg fun x hx => by
    obtain ⟨rho, hr_, rfl⟩ := mp mem_map hx
    exact hnn rho hr_
  refine ⟨hnn, ?_, ?_⟩ <;> (split_ifs at h1 ⊢ <;> simp only [one_div, zero_re] at h1 <;> linarith)

lemma negLD_bound_right (χ : DC q) {s : ℂ} (hs1 : 1 < re s) (hs2 : re s ≤ 1.1) :
    ‖negLD χ s‖ ≤ inv (re s - 1) + 4100 := by
  have hre : ‖negLD χ s‖ ≤ re (negLD c1 $ cR $ re s) := by
    rw [negLD_eq_LSeries_mul_vonMangoldt χ hs1, negLD_eq_LSeries_mul_vonMangoldt c1 $ by simpa using hs1]
    apply tsum_of_norm_bounded $ hasSum_re (LSeriesSummable_twist_vonMangoldt c1 $ by simpa using hs1).hasSum
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    simp
    rw [norm_term_eq, term_of_ne_zero hn, ← ofReal_natCast, ← ofReal_cpow $ cast_nonneg n]
    simp only [hn, ↓reduceIte, Pi.mul_apply, c1a, one_mul,
      ← ofReal_div, ofReal_re, norm_mul, norm_cR_nn vonMangoldt_nonneg]
    grw [norm_le_one χ _]
    simp
  obtain ⟨_, -, -, -, -, hb⟩ := L1_local_expansion c1 (inr rfl) 0
  have := a2 $ a2 $ hb (re s) hs1 hs2
  simp [mk_eq_add_mul_I, lcond, -inv_re, -ofReal_sub, ← ofReal_inv] at this
  linarith [log_two_lt_d9]

abbrev dZ : ℝ := 0.0000025
abbrev zfrC0 : ℝ := 0.0000000625

theorem exists_excZeros (χ : DC q) (hxq_ : Good χ) : ∃ bet0, ExcZeros zfrC0 χ bet0 := by
  by_cases hex : ∃ s, InRegion zfrC0 q s ∧ IsLZero χ s
  swap
  exact ⟨none, by simp, fun s hs hz => absurd ⟨s, hs, hz⟩ hex⟩
  obtain ⟨s, hs, hz⟩ := hex
  have h341 {r : ℕ} [NeZero r] (φ : DC r) (w : ℂ) (hfq : Good φ)
      (hcase : φ ^ 2 ≠ 1 ∨ dZ / lcond r (im w) ≤ abs (im w)) (hreg : InRegion zfrC0 r w) : L1 φ w ≠ 0 := by
    intro hzero
    let lv := lcond r $ im w
    let la := 2000000 * lv
    let al := inv la
    have := lcond_ge_const r $ im w
    have hLpos := lcond_pos r $ im w
    have hb1_ := lt_of_not_ge (L1_ne_zero_of_one_le_re hfq · hzero)
    let σ := 1 + al
    have hs1_ : 1 < σ := lt_add_of_pos_right 1 $ by positivity
    have hs11_ : σ ≤ 1.1 := by dsimp [σ, al]
                               linarith [invLe (a := 10) (b := la) $ by linarith]
    have hsb_ : σ - re w ≤ 1.125 * al := by
      dsimp [InRegion, σ, al, la] at hreg ⊢
      rw [div_eq_mul_inv] at hreg
      rw [mul_inv]
      linarith
    have : re (negLD c1 σ) ≤ la + 4100 := by
      simpa [σ, al] using le_trans (re_le_norm _) $ negLD_bound_right c1 (s := σ) (by simpa using hs1_) $ by simpa using hs11_
    have hpole u (hu : dZ / lv ≤ abs u) : re (inv $ mk (σ - 1) u) ≤ 0.04 * la := by
      rw [inv_re, normSq_mk]
      simp [show σ - 1 = al by ring, ← sq]
      grw [← show (dZ / lv) ^ 2 ≤ al ^ 2 + u ^ 2 by nlinarith [sq_abs u, pow_le_pow_left₀ (by positivity) hu 2]]
      apply le_of_eq
      field [ne_of_gt hLpos]
    have h2 : re (negLD φ $ mk σ $ im w) ≤ 0.04 * la + 5900 * lv - 8 / 9 * la := by
      obtain ⟨Z, hZ, -, -, -, hb⟩ := L1_local_expansion φ hfq $ im w
      obtain ⟨hnn, h2', -⟩ := hb σ hs1_ hs11_
      rw [← cons_erase $ mpr (hZ w) ⟨by
        rw [mem_closedBall, dist_mk_im, abs_le]
        constructor <;> linarith, hzero⟩, map_cons, sum_cons] at h2'
      have := sum_nonneg (s := (Z.erase w).map fun rho => re $ inv $ mk σ (im w) - rho) fun x hx => by
        obtain ⟨rho, hr_, rfl⟩ := mp mem_map hx
        exact hnn rho $ mem_of_mem_erase hr_
      have : re (inv $ mk σ (im w) - w) = inv (σ - re w) := by
        rw [show mk σ (im w) - w = cR (σ - re w) by apply ext <;> simp, ← ofReal_inv, ofReal_re]
      have := (show 8 / 9 * la = inv (1.125 * al) by field [ne_of_gt hLpos]).trans_le $ invLe hsb_
      split_ifs at h2' with hx1_
      linarith [hpole (im w) $ resolve_left hcase $ by simp [hx1_]]
      linarith
    have hlm2 {m : ℕ} [NeZero m] (hm : rN m ≤ r) : lcond m (2 * im w) ≤ 2 * lv := by
      have := one_le_modulus_real m
      conv_rhs => rw [← cast_two, ← log_pow]
      rw [lcond, abs_mul, abs_two]
      exact logLe $ by grw [hm]
                       nlinarith
    by_cases hsq : φ ^ 2 = 1
    obtain ⟨_, -, -, -, -, hb2⟩ := L1_local_expansion c1 (inr rfl) $ 2 * im w
    have hre2 := a2 $ a2 $ hb2 σ hs1_ hs11_
    simp only [↓reduceIte] at hre2
    have := hlm2 $ by simpa using (one_le_modulus_real r)
    have := negLD_341 φ c1 (fun n hu => by
      rw [c1a, ← pow_apply' φ two_ne_zero, hsq, one_apply hu]) hs1_ $ im w
    nlinarith [hpole (2 * im w) $ by rw [abs_mul, abs_two]; linarith [resolve_left hcase $ mpr not_not hsq, abs_nonneg $ im w]]
    obtain ⟨_, -, -, -, -, hb2⟩ := L1_local_expansion (φ ^ 2) (inl hsq) $ 2 * im w
    have hnr := a2 $ a2 $ hb2 σ hs1_ hs11_
    simp [hsq] at hnr
    have := hlm2 le_rfl
    have := negLD_341 φ (φ ^ 2) (fun n _ => pow_apply' φ two_ne_zero n) hs1_ $ im w
    nlinarith
  have hL10 := mpr (L1_eq_zero_iff hxq_) hz
  have hx1_ : χ ≠ 1 := by
    rintro rfl
    obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not rfl
    by_cases hbig : dZ / lcond 1 (im s) ≤ abs (im s)
    exact h341 c1 s (inr rfl) (inr hbig) hs hL10
    push Not at hbig
    have := lt_of_not_ge (L1_ne_zero_of_one_le_re (inr rfl) · hL10)
    have := lcond_ge_const 1 $ im s
    have := divLe (a := zfrC0) (b := lcond 1 $ im s) (c := 0.001) $ by linarith
    dsimp [InRegion] at hs
    have hns : ‖s - 1‖ ≤ 0.01 := by
      have := norm_le_abs_re_add_abs_im $ s - 1
      simp [abs_of_neg $ show re s - 1 < 0 by linarith] at this
      linarith [divLe (a := dZ) (b := lcond 1 $ im s) (c := 0.001) $ by linarith]
    have h1 : 1 ≤ ‖(s - 1) * riemannZeta₀ s‖ := by
      simp [L1, riemannZeta₁] at hL10
      rw [eq_neg_of_add_eq_zero_right hL10]
      simp
    grw [norm_mul, hns, zeta0_growth_half $ by linarith, show norm s ≤ 2 by have := norm_add_le (s - 1) 1; simp at this; linarith] at h1
    linarith
  have hsq := by_contra fun hsq => h341 χ s hxq_ (inl hsq) hs hL10
  have hsmall {w : ℂ} hw hwz :=
    by_contra fun hlt => h341 χ w hxq_ (inr $ mp not_lt hlt) hw $ by simpa [L1, hx1_] using hwz
  have hq := one_le_modulus_real q
  let L0_ := lcond q 0
  have hL0h : 0.5 < L0_ := by linarith [lcond_ge_const q 0]
  have hL0pos : 0 < L0_ := by linarith
  let T := 40000 * L0_
  have hT10 : 10 ≤ T := by linarith
  have hTpos : 0 < T := by positivity
  let σ := 1 + inv T
  have hs1_ : 1 < σ := lt_add_of_pos_right 1 $ mpr inv_pos hTpos
  have hs2 : σ ≤ 1.1 := by linarith [invLe hT10]
  have h0 : re (negLD c1 σ) ≤ T + 4100 := by
    simpa [σ] using le_trans (re_le_norm _) $ negLD_bound_right c1 (s := σ) (by simpa using hs1_) $ by simpa using hs2
  obtain ⟨Z, hZ, hmult, -, -, hb⟩ := L1_local_expansion χ (inl hx1_) 0
  simp only [L1, mk_eq_add_mul_I, hx1_, ↓reduceIte, ofReal_zero, zero_mul, add_zero, zero_add] at hZ hmult hb
  obtain ⟨hnnZ, hb1, -⟩ := hb σ hs1_ hs2
  have hcons rho (hr : InRegion zfrC0 q rho) (hzr : LFunction χ rho = 0) :
      rho ∈ Z ∧ 0.75 * T ≤ re (inv $ σ - rho) := by
    have := hsmall hr hzr
    have hLr : L0_ ≤ lcond q (im rho) := logLe $ by simp
                                                    nlinarith [ abs_nonneg $ im rho]
    have hdiv : dZ / lcond q (im rho) ≤ 0.1 / T := by
      grw [← hLr]
      apply le_of_eq
      field [ne_of_gt hL0pos]
    have hb1_ := lt_of_not_ge (LFunction_ne_zero_of_one_le_re χ (inl hx1_) · hzr)
    have hb_ : 1 - 0.1 / T ≤ re rho := by
      unfold InRegion at hr
      have := lcond_pos q $ im rho
      grw [show zfrC0 ≤ dZ by norm_num, hdiv] at hr
      grind
    have hg_ : abs (im rho) ≤ 0.1 / T := by linarith
    exists mpr (hZ rho) ⟨?_, hzr⟩
    rw [mem_closedBall, dist_eq]
    grw [norm_le_abs_re_add_abs_im]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    rw [abs_of_neg $ by linarith]
    grind
    rw [inv_re, normSq_apply]
    simp
    rw [le_div_iff₀ $ by nlinarith]
    rw [div_eq_mul_inv] at hb_ hg_
    have hTi := mul_inv_cancel₀ $ ne_of_gt hTpos
    have h1 : σ - re rho ≤ 1.1 * inv T := by dsimp [σ]
                                             grind
    have h2 : im rho * im rho ≤ (0.1 * inv T) ^ 2 := by nlinarith [sq_abs $ im rho, hg_, abs_nonneg $ im rho]
    have h3 : (σ - re rho) * (σ - re rho) ≤ (1.1 * inv T) ^ 2 := by nlinarith
    nlinarith
  have hF1 : (Z.map fun rho => re $ inv $ σ - rho).sum < 1.5 * T := by
    have hP := negLD_341 χ c1 (fun n hu => by
      rw [c1a, ← pow_apply' χ two_ne_zero, hsq, one_apply hu]) hs1_ 0
    simp only [mk_eq_add_mul_I, mul_zero, ofReal_zero, zero_mul, add_zero] at hP
    grind
  have htwo rho1 rho2 (h1r : InRegion zfrC0 q rho1) (h1z : LFunction χ rho1 = 0)
      (h2r : InRegion zfrC0 q rho2) (h2z : LFunction χ rho2 = 0) (h12 : rho2 ∈ Z.erase rho1) : False := by
    obtain ⟨h1Z, h1r'⟩ := hcons rho1 h1r h1z
    obtain ⟨-, h2r'⟩ := hcons rho2 h2r h2z
    rw [← cons_erase h1Z, ← cons_erase h12, map_cons, map_cons, sum_cons, sum_cons] at hF1
    linarith [   sum_nonneg (s := ((Z.erase rho1).erase rho2).map fun rho => re $ inv $ σ - rho) fun x hx => by
      obtain ⟨rho, hr_, rfl⟩ := mp mem_map hx
      exact hnnZ rho $ mem_of_mem_erase $ mem_of_mem_erase hr_]
  have hsim : im s = 0 := by
    by_contra hne
    have hconj0 : LFunction χ (starRingEnd ℂ s) = 0 := by
      have hL := differentiable_LFunction hx1_
      have hG : Differentiable ℂ $ fun z => starRingEnd ℂ $ LFunction χ $ starRingEnd ℂ z := fun z => by
        have := (hL $ starRingEnd ℂ z).conj_conj
        rwa [conj_conj] at this
      have heq := AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (analyticOnNhd_univ_iff_differentiable.2 hG)
          (analyticOnNhd_univ_iff_differentiable.2 hL) $ by
        filter_upwards [(isOpen_re_gt 1).mem_nhds $ by norm_num] with z hz_
        rw [LFunction_eq_LSeries χ $ by rwa [conj_re], LFunction_eq_LSeries χ hz_, LSeries, LSeries, conj_tsum]
        congr 1
        funext m
        rw [term_def, term_def]
        split_ifs
        simp
        rcases isQuadratic_iff_sq_eq_one.mpr hsq m with h | h | h <;>
          simp [h, cpow_conj (cN m) _ $ by simp [symm pi_ne_zero]]
      simpa [a2 hz] using symm $ congrFun heq $ starRingEnd ℂ s
    have hcr : InRegion zfrC0 q $ starRingEnd ℂ s := by simpa [InRegion, lcond] using hs
    exact htwo s _ hs (a2 hz) hcr hconj0
      (mpr (mem_erase_of_ne fun h => hne $ by have := congrArg im h; simp at this; linarith) $ a1 $ hcons _ hcr hconj0)
  have hs' : s = cR (re s) := ext (by simp) $ by simp [hsim]
  have hhalf : 0.5 ≤ re s := by
    unfold InRegion at hs
    rw [hsim] at hs
    linarith [divLe (a := zfrC0) (b := lcond q 0) (c := 0.5) $ by linarith [lcond_ge_const q 0]]
  refine ⟨some $ re s, fun β hb_ => ?_, fun s' hs'' hz' => ⟨re s, by simp,
    (by_contra fun hne => htwo s s' hs (a2 hz) hs'' (a2 hz') $ mpr (mem_erase_of_ne hne) $ a1 $ hcons s' hs'' $ a2 hz').trans hs'⟩⟩
  obtain rfl : re s = β := by simpa using hb_
  rw [← hs']
  exact ⟨hx1_, hhalf, mp not_le fun hge => LFunction_ne_zero_of_one_le_re χ (inl hx1_) hge $ a2 hz, hs, a2 hz,
    fun hd => htwo s s hs (a2 hz) hs (a2 hz) $ mp not_not fun h => mp (hmult s $ a1 $ hcons s hs $ a2 hz) h hd, hsq⟩

abbrev zfrC : ℝ := 768011800

theorem log_deriv_in_zero_free_region (χ : DC q) (bet0 : Option ℝ) (hxq_ : Good χ) (hB : ExcZeros zfrC0 χ bet0)
    (s : ℂ) (hs : InRegion (zfrC0 / 2) q s) (hs11 : re s ≤ 1.1) {dl : ℝ} (hd_ : 0 < dl)
    (hdP : ∀ p ∈ (if χ = 1 then some r1 else bet0), dl ≤ ‖s - cR p‖) :
    ‖negLD χ s‖ ≤ zfrC * lcond q (im s) ^ 2 + inv dl := by
  obtain ⟨hBmem, hBall⟩ := hB
  let lv := lcond q $ im s
  have := lcond_ge_const q $ im s
  have hLpos := lcond_pos q $ im s
  have : zfrC0 / 2 / lv ≤ inv 34 := divLe $ by nlinarith
  have hsP p (hp : p ∈ (if χ = 1 then some r1 else bet0)) : s ≠ p := fun h => by
    linarith [hdP p hp, show ‖s - cR p‖ = 0 by simp [h]]
  have hfs : L1 χ s ≠ 0 := fun h0 => by
    obtain ⟨β, hb_, hsb⟩ := hBall s (by unfold InRegion at hs ⊢; linarith [div_le_div_of_nonneg_right (show zfrC0 / 2 ≤ zfrC0 by norm_num) $ le_of_lt hLpos]) $ mp (L1_eq_zero_iff hxq_) h0
    apply hsP β _ hsb
    grind
  obtain ⟨Z, hZ, hmult, hsum, hder, -⟩ := L1_local_expansion χ hxq_ $ im s
  let z0_ := mk 1.05 $ im s
  have hs6 : s ∈ closedBall z0_ 0.08 := by
    rw [mem_closedBall, dist_mk_im, abs_le]
    unfold InRegion at hs
    constructor <;> linarith
  have hfar rho (hr_ : rho ∈ Z) (hne : ∀ β ∈ bet0, rho ≠ cR β) : inv ‖s - rho‖ ≤ 3 * lv / zfrC0 := by
    obtain ⟨hball, hzero⟩ := mp (hZ rho) hr_
    have hreg_not := lt_of_not_ge fun hreg => let ⟨β, hb_, hrb_⟩ := hBall rho hreg (mp (L1_eq_zero_iff hxq_) hzero)
      hne β hb_ hrb_
    have : abs (im rho - im s) ≤ 0.13 := by
      rw [mem_closedBall, dist_eq_norm] at hball
      simpa using le_trans (abs_im_le_norm $ rho - z0_) hball
    have hLr : lcond q (im rho) ≤ 1.2 * lv := by
      have := one_le_modulus_real q
      have : lcond q (im rho) ≤ lv + log 1.1 := by
        rw [← log_mul (by positivity) $ by norm_num]
        exact logLe $ by nlinarith [abs_sub_abs_le_abs_sub (im rho) $ im s, abs_nonneg $ im s]
      linarith [log_le_sub_one_of_pos (x := 1.1) $ by norm_num]
    have hre : zfrC0 / (3 * lv) ≤ re (s - rho) := by
      rw [sub_re]
      unfold InRegion at hs
      have := lcond_pos q $ im rho
      grw [hLr] at hreg_not
      have : zfrC0 / (3 * lv) = zfrC0 / (1.2 * lv) - zfrC0 / 2 / lv := by field [ne_of_gt hLpos]
      linarith
    exact trans_eq (invLe $ le_trans hre $ re_le_norm _) $ inv_div _ _
  let D := 768000000 * lv ^ 2
  have hmsum Z' (hZ' : Z' ≤ Z) (hne : ∀ rho ∈ Z', ∀ β ∈ bet0, rho ≠ cR β) :
      ‖(Z'.map fun rho => inv $ s - rho).sum‖ ≤ D := by
    grw [norm_multiset_sum_le, Multiset.map_map, Multiset.sum_le_card_nsmul _ $ 3 * lv / zfrC0, card_map, nsmul_eq_mul,
      show (Z'.card : ℝ) ≤ rN Z.card from mpr cast_le $ card_le_card hZ', hsum]
    grind
    intro x hx
    obtain ⟨rho, hr_, rfl⟩ := mp mem_map hx
    simpa using hfar rho (subset_of_le hZ' hr_) $ hne rho hr_
  let SZ := (Z.map fun rho => inv $ s - rho).sum
  have hSZ : ‖-SZ + (if χ = 1 then inv (s - 1) else 0)‖ ≤ D + inv dl := by
    by_cases h1 : χ = 1
    simp [h1]
    grw [norm_add_le, norm_neg, hmsum Z le_rfl fun _ _ β h => absurd h1 $ a1 $ hBmem β h, norm_inv,
      invLe $ by simpa [h1] using hdP 1]
    simp [h1, add_zero, norm_neg]
    by_cases hex : ∃ β ∈ bet0, cR β ∈ Z
    obtain ⟨β, hb_, hbZ⟩ := hex
    have hbm := hBmem β hb_
    dsimp [SZ]
    rw [← cons_erase hbZ, map_cons, sum_cons]
    grw [norm_add_le, norm_inv, invLe $ hdP β $ by simp [h1, hb_],
      hmsum (Z.erase $ cR β) (erase_le _ _) fun rho hr_ bet' hb' h => by
        obtain rfl := inj $ (symm hb_).trans hb'
        exact mpr (hmult _ hbZ) (by simpa [L1, a1 hbm] using a1 hbm.2.2.2.2.2) $ h ▸ hr_]
    linarith
    linarith [hmsum Z le_rfl fun rho hr_ β hb_ h => hex ⟨β, hb_, h ▸ hr_⟩, mpr inv_pos hd_]
  rw [show negLD χ s = -(deriv (L1 χ) s / L1 χ s - SZ) + (-SZ + (if χ = 1 then inv (s - 1) else 0)) by
    rw [L1_log_deriv hxq_ (if h1 : χ = 1 then inr (by simpa [h1] using hsP 1) else inl h1) hfs]
    simp
    ring]
  grw [norm_add_le, norm_neg, hder s hs6 hfs, hSZ]
  nlinarith

lemma perron_formula_character (χ : DC q) (y : ℝ) (hy : 1 ≤ y) (sig0 : ℝ) (hs_ : 1 < sig0) :
    Integrable (fun t : ℝ => Fchi χ y (mk sig0 t)) ∧
    Schi χ y = (inv (2 * π) : ℂ) * ∫ t : ℝ, Fchi χ y (mk sig0 t) := by
  have hy0 : 0 < y := by linarith
  have hw0 t : mk sig0 t * (mk sig0 t + 1) ≠ 0 :=
    mul_ne_zero (ne_zero_of_re_pos $ by linarith) $ ne_zero_of_re_pos $ by simp; linarith
  have hD t : 1 + t ^ 2 ≤ ‖mk sig0 t * (mk sig0 t + 1)‖ := by
    rw [← sq_le_sq₀ (by positivity) $ by positivity, Complex.sq_norm, map_mul, normSq_apply, normSq_apply]
    simp
    nlinarith
  let K u t := cR u ^ (-mk sig0 t) / (mk sig0 t * (mk sig0 t + 1))
  let g x := cR $ max (1 - x) 0
  have hg0 {x : ℝ} (hx : 1 ≤ x) : g x = 0 := by simp [g, max_eq_right $ mpr sub_nonpos hx]
  have hg_eq {w : ℂ} (hw : 0 < re w) :
      IntegrableOn (fun x => cR x ^ (w - 1) • g x) (Set.Ioc 0 1) ∧ mellin g w = inv (w * (w + 1)) := by
    have ha1 : -1 < re (w - 1) := by simp [hw]
    have ha2 : -1 < re w := by linarith
    have h1 := a1 $ @intervalIntegrable_cpow' 0 1 (w - 1) ha1
    have h2 := a1 $ @intervalIntegrable_cpow' 0 1 w ha2
    have heq : EqOn (fun x => cR x ^ (w - 1) • g x) (fun x => cR x ^ (w - 1) - cR x ^ w) $ Set.Ioc 0 1 := fun x hx => by
      simp only [g, smul_eq_mul, max_eq_left $ mpr sub_nonneg $ a2 hx]
      push_cast
      rw [show cR x ^ w = cR x ^ (w - 1 + 1) by ring_nf, cpow_add _ _ $ mpr ofReal_ne_zero $ ne_of_gt $ a1 hx, cpow_one]
      ring
    exists (h1.sub h2).congr_fun heq.symm measurableSet_Ioc
    unfold mellin
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
        fun x hx => by simp [hg0 $ le_of_lt $ mp not_le fun h => a2 hx ⟨a1 hx, h⟩],
      setIntegral_congr_fun measurableSet_Ioc heq, integral_sub h1 h2,
      ← integral_of_le zero_le_one, ← integral_of_le zero_le_one,
      integral_cpow $ inl ha1, integral_cpow $ inl ha2]
    have hw1 : w + 1 ≠ 0 := ne_zero_of_re_pos $ by simp
                                                   linarith
    simp [zero_cpow $ ne_zero_of_re_pos hw, zero_cpow hw1]
    field [ne_zero_of_re_pos hw, hw1]
  have hm t : mellin g (mk sig0 t) = inv (mk sig0 t * (mk sig0 t + 1)) := a2 $ hg_eq $ by linarith
  have hmc : MellinConvergent g sig0 := by
    unfold MellinConvergent
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact (a1 $ hg_eq $ by simp; linarith).union $
      integrableOn_zero.congr_fun (fun x hx => by simp [hg0 $ le_of_lt hx]) measurableSet_Ioi
  have hcmk : Continuous $ fun t => mk sig0 t := by simp_rw [mk_eq_add_mul_I]
                                                    fun_prop
  have hsingle {u : ℝ} (hu : 0 < u) : g u = (inv (2 * π) : ℂ) * ∫ t : ℝ, K u t := by
    rw [← mellinInv_mellin_eq sig0 g hu hmc]
    unfold mellinInv
    rw [integral_congr_ae (g := K u) $ of_forall fun t => by simp [K, ← mk_eq_add_mul_I, hm, div_eq_mul_inv], real_smul]
    push_cast
    ring
    apply (Integrable.mono' integrable_inv_one_add_sq _ _).congr $ of_forall fun t => by rw [← mk_eq_add_mul_I, hm]
    exact (Continuous.inv₀ (by fun_prop) hw0).aestronglyMeasurable
    exact of_forall fun t => by rw [norm_inv]
                                exact invLe $ hD t
    fun_prop
  let f n := Λ n * χ n
  let G n t := term (↗χ * ↗Λ) (mk sig0 t) n * (cR y ^ mk sig0 t / (mk sig0 t * (mk sig0 t + 1)))
  let Mn n := ‖term (fun k => (Λ k : ℂ)) sig0 n‖ * y ^ sig0
  have hGe {n} (hn : n ≠ 0) : G n = fun t => f n * K (n / y) t := funext fun t => by
    simp only [G, K, f, term_of_ne_zero hn, cpow_neg, ofReal_div,
      div_cpow_ofReal_nonneg (cast_nonneg n) $ le_of_lt hy0, inv_div, Pi.mul_apply]
    push_cast
    ring
  have hGn_le n t : ‖G n t‖ ≤ Mn n * inv (1 + t ^ 2) := by
    rcases eq_or_ne n 0 with rfl | hn
    simp [G, Mn]
    simp only [G, Mn, norm_mul, norm_inv, norm_term_eq, hn, ↓reduceIte, Pi.mul_apply,
      norm_cpow_eq_rpow_re_of_pos hy0, ofReal_re, div_eq_mul_inv]
    grw [norm_le_one χ _, invLe $ trans_eq (hD t) $ norm_mul _ _]
    grind
  have hGn_int n : Integrable (G n) volume := by
    rcases eq_or_ne n 0 with rfl | hn
    change Integrable (fun t => G 0 t) _
    simp [G]
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul $ Mn n) ?_ $ of_forall $ hGn_le n
    simp only [hGe hn, K]
    exact (continuous_const.mul $ (Continuous.const_cpow (by fun_prop) $
      inl $ mpr ofReal_ne_zero $ ne_of_gt $ div_pos (by positivity) hy0).div (by fun_prop) hw0).aestronglyMeasurable
  have hSM := (LSeriesSummable_vonMangoldt (s := sig0) $ by simpa using hs_).norm.mul_right $ y ^ sig0
  have hGn_sum : Summable fun n => ∫ t : ℝ, ‖G n t‖ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun n => trans_eq (integral_mono (hGn_int n).norm (integrable_inv_one_add_sq.const_mul $ Mn n) $ hGn_le n)
        (by rw [integral_const_mul, integral_univ_inv_one_add_sq])) $ hSM.mul_right π
  have hF_eq : (fun t => Fchi χ y $ mk sig0 t) = fun t => ∑' n, G n t := funext fun t => by
    rw [Fchi, mul_div_assoc, negLD_eq_LSeries_mul_vonMangoldt χ hs_, LSeries, ← tsum_mul_right]
  let hMt t := hSM.mul_right $ inv $ 1 + t ^ 2
  refine ⟨hF_eq ▸ Integrable.mono' (integrable_inv_one_add_sq.const_mul (∑' n, Mn n))
    (aestronglyMeasurable_of_tendsto_ae atTop (fun _ => aestronglyMeasurable_fun_sum _ fun n _ => a1 $ hGn_int n)
      (of_forall fun t => (Summable.of_norm_bounded (hMt t) fun n => hGn_le n t).hasSum.tendsto_sum_nat))
    (of_forall fun t => trans_eq (tsum_of_norm_bounded (hMt t).hasSum fun n => hGn_le n t) tsum_mul_right), ?_⟩
  have hterm n : (inv (2 * π) : ℂ) * ∫ t, G n t = if n = 0 then 0 else f n * g (n / y) := by
    rcases eq_or_ne n 0 with rfl | hn0
    simp [G]
    simp only [hGe hn0, hn0, ↓reduceIte, integral_const_mul]
    rw [mul_left_comm, ← hsingle $ div_pos (by positivity) hy0]
  rw [hF_eq, ← integral_tsum_of_summable_integral_norm hGn_int hGn_sum, ← tsum_mul_left, tsum_eq_sum]
  unfold Schi Sa
  apply sum_congr rfl
  intro n hn
  rw [mem_Icc] at hn
  rw [hterm]
  simp [show n ≠ 0 by omega, g, f, max_eq_left $ mpr sub_nonneg $ mpr (div_le_one hy0) $ mp (le_floor_iff $ le_of_lt hy0) $ a2 hn]
  intro n hn
  rw [hterm]
  split_ifs with hn0
  rfl
  rw [mem_Icc] at hn
  rw [hg0 $ mpr (one_le_div hy0) (le_of_lt $ lt_of_floor_lt $ by omega), mul_zero]

lemma rectangle_contour_shift_character (χ : DC q)
    (hxq_ : Good χ) (y : ℝ) (hy : 0 < y) (sig1 sig0 T : ℝ) (bet0 : Option ℝ)
    (hs1__ : 0 < sig1) (hs11__ : sig1 < 1) (hσ₀ : 1 < sig0) (hT : 0 < T)
    (hB : ∀ β ∈ bet0, χ ≠ 1 ∧ sig1 < β ∧ β < sig0 ∧ LFunction χ (cR β) = 0 ∧ deriv (LFunction χ) (cR β) ≠ 0)
    (hZ : ∀ w, sig1 ≤ re w → re w ≤ sig0 → abs (im w) ≤ T → IsLZero χ w → ∃ β ∈ bet0, w = cR β) :
    rectInt (Fchi χ y) sig1 sig0 (-T) T =
      2 * π * I * ((if χ = 1 then cR y / 2 else 0) - elim bet0 0 (zterm y)) := by
  let K := uIcc sig1 sig0 ×ℂ uIcc (-T) T
  have hK {w} (hw : w ∈ K) : sig1 ≤ re w ∧ re w ≤ sig0 ∧ abs (im w) ≤ T := by
    rw [mem_reProdIm, Set.uIcc_of_le $ by linarith, Set.uIcc_of_le $ by linarith] at hw
    exact ⟨hw.1.1, hw.1.2, mpr abs_le $ a2 hw⟩
  have hZ' w (hw : w ∈ K) := hZ w (hK hw).1 (hK hw).2.1 (hK hw).2.2
  let k z : ℂ := y ^ z / (z * (z + 1))
  have hkd : DifferentiableOn ℂ k {z | 0 < re z} :=
    DifferentiableOn.div (fun z _ => (DifferentiableAt.const_cpow differentiableAt_id $ inl $ mpr ofReal_ne_zero $ ne_of_gt hy).differentiableWithinAt)
      (by fun_prop) fun z hz => mul_ne_zero (ne_zero_of_re_pos hz) $ ne_zero_of_re_pos $ by simp; grind
  have hKsub : K ⊆ {z | 0 < re z} := fun w hw => show 0 < re w by grind
  have hPole p sgn (hp : sig1 < p ∧ p < sig0) (g : ℂ → ℂ) (hgd : Differentiable ℂ g)
      (hgne : ∀ w ∈ K, g w ≠ 0) (hld : ∀ w ∈ K, w ≠ p → negLD χ w = sgn * inv (w - p) - deriv g w / g w) :
      rectInt (Fchi χ y) sig1 sig0 (-T) T = 2 * π * I * (sgn * k p) := by
    let c := sgn * k p
    let A z := sgn * dslope k p z - deriv g z / g z * k z
    have hA : DifferentiableOn ℂ A K :=
      ((((differentiableOn_dslope ((isOpen_re_gt 0).mem_nhds $ by simp; linarith)).2 hkd).mono hKsub).const_mul sgn).sub
        ((hgd.deriv.differentiableOn.div hgd.differentiableOn hgne).mul $ hkd.mono hKsub)
    have hA0 : rectInt A sig1 sig0 (-T) T = 0 := by
      simpa only [smul_eq_mul, rectInt, mk_eq_add_mul_I] using
        integral_boundary_rect_eq_zero_of_differentiableOn A ⟨sig1, -T⟩ ⟨sig0, T⟩ hA
    have hseg (z0 d : ℂ) (a b : ℝ) (hK' : ∀ t ∈ uIcc a b, z0 + t * d ∈ K ∧ z0 + t * d ≠ p)
        (F : ℂ → ℂ) (hF : ∀ t ∈ uIcc a b, HasDerivAt F (inv $ z0 + t * d - p) $ z0 + t * d) :
        d * ∫ t in a..b, Fchi χ y (z0 + t * d) =
          d * (∫ t in a..b, A (z0 + t * d)) + c * (F (z0 + b * d) - F (z0 + a * d)) := by
      let γ t := z0 + t * d
      have hci' : IntervalIntegrable (fun t => inv $ γ t - p) volume a b :=
        (ContinuousOn.inv₀ (by fun_prop) fun t ht => sub_ne_zero_of_ne $ a2 $ hK' t ht).intervalIntegrable
      rw [integral_congr (g := fun t => A (γ t) + c * inv (γ t - p)) fun t ht => by
          obtain ⟨h1, h2⟩ := hK' t ht
          rw [Fchi, mul_div_assoc, hld _ h1 h2]
          dsimp [A, c, k]
          rw [dslope_of_ne _ h2, slope_def_field]
          field [sub_ne_zero_of_ne h2, hgne _ h1],
        integral_add (f := fun t => A $ γ t) (hA.continuousOn.comp (by fun_prop) fun t ht => a1 $ hK' t ht).intervalIntegrable $ hci'.const_mul c,
        intervalIntegral.integral_const_mul, mul_add, mul_left_comm d, ← intervalIntegral.integral_const_mul d fun t => inv $ γ t - p,
        integral_eq_sub_of_hasDerivAt (fun t ht => by
          simpa [Function.comp_def, γ] using
            (hF t ht).scomp t $ ((hasDerivAt_id t).ofReal_comp.mul_const d).const_add z0) $ hci'.const_mul d]
    have hL {s} (hs : s - cR p ∈ slitPlane) : HasDerivAt (fun s => clog $ s - cR p) (inv $ s - cR p) s := by
      simpa using ((hasDerivAt_id s).sub_const $ cR p).clog hs
    have eH v (hv : v ∈ uIcc (-T) T) (hv0 : v ≠ 0) := by
      simpa [add_comm, ← mk_eq_add_mul_I] using hseg (v * I) 1 sig1 sig0
        (fun x hx => ⟨mpr mem_reProdIm ⟨by simpa using hx, by simpa using hv⟩,
          fun h => hv0 $ by simpa using congrArg im h⟩)
        (fun s => clog $ s - cR p) fun _ _ => hL $ mpr mem_slitPlane_iff $ inr $ by simp [hv0]
    have eV x (hx : x ∈ uIcc sig1 sig0) (hxp : x ≠ p) F
        (hF : ∀ v ∈ uIcc (-T) T, HasDerivAt F (inv $ mk x v - p) $ mk x v) := by
      simpa only [← mk_eq_add_mul_I] using hseg x I (-T) T
        (fun v hv => ⟨mpr mem_reProdIm ⟨by simpa using hx, by simpa using hv⟩,
          fun h => hxp $ by simpa using congrArg re h⟩) F fun v hv => by simpa only [← mk_eq_add_mul_I] using hF v hv
    set a := mk sig1 T - p
    set b := mk sig1 (-T) - p
    have hPM : clog a - clog (-a) + (clog (-b) - clog b) = 2 * π * I := by
      apply ext <;> simp [log_re, log_im, arg_neg_eq_arg_sub_pi_of_im_pos (x := a) $ by simp [a, hT],
        arg_neg_eq_arg_add_pi_of_im_neg (x := b) $ by simp [b, hT]]
      ring
    unfold rectInt at hA0 ⊢
    rw [eH (-T) left_mem_uIcc $ mpr neg_ne_zero $ ne_of_gt hT, eH T right_mem_uIcc $ ne_of_gt hT,
      eV sig0 right_mem_uIcc (ne_of_gt $ a2 hp) _ fun _ _ => hL $ mpr mem_slitPlane_iff $ inl $ by simp; linarith,
      eV sig1 left_mem_uIcc (ne_of_lt $ a1 hp) (fun s => clog $ -(s - p)) fun s _ =>
        (((hasDerivAt_id _).sub_const $ cR p).neg.clog $ mpr mem_slitPlane_iff $ inl $ by simp; linarith).congr_deriv $ by dsimp; rw [neg_div_neg_eq, one_div]]
    linear_combination hA0 + c * hPM
  by_cases h1 : χ = 1
  obtain rfl : q = 1 := resolve_left hxq_ $ mpr not_not h1
  subst h1
  obtain rfl : bet0 = none := mpr eq_none_iff_forall_ne_some fun β hb => a1 (hB β $ by simp [hb]) rfl
  simp
  have hzne w hw : riemannZeta₁ w ≠ 0 := fun h0 => by
    simpa using hZ' w hw $ mp (L1_eq_zero_iff hxq_) $ by simpa [L1] using h0
  rw [show y / 2 = 1 * k 1 by simp [k]; ring]
  refine hPole 1 1 ⟨hs11__, hσ₀⟩ riemannZeta₁ differentiable_riemannZeta₁ hzne fun w hw hw1 => ?_
  have hld := L1_log_deriv hxq_ (inr $ by simpa using hw1) $ by simpa [L1] using hzne w hw
  simp [L1] at hld ⊢
  linear_combination hld
  have hLd := differentiable_LFunction h1
  rcases bet0 with _ | β
  simp [h1]
  have hLne w hw : LFunction χ w ≠ 0 := fun h0 => by simpa using hZ' w hw ⟨inl h1, h0⟩
  simpa using hPole ((sig1 + sig0) / 2) 0 ⟨by linarith, by linarith⟩ (LFunction χ) hLd hLne
    fun _ _ _ => by simp [negLD]
  obtain ⟨-, hb1_, hb2_, hbz, hbd_⟩ := hB β $ by simp
  simp only [h1, ↓reduceIte, elim_some, zero_sub]
  let g := dslope (LFunction χ) β
  have hgd : Differentiable ℂ g := mp differentiableOn_univ $ mpr (differentiableOn_dslope univ_mem) hLd.differentiableOn
  have hLz : (· - cR β) * g = LFunction χ := funext $ sub_smul_dslope_of_zero hbz
  have hgne w hw : g w ≠ 0 := fun h0 => by
    rcases eq_or_ne w β with rfl | hne
    apply hbd_
    simpa [g, dslope_same] using h0
    apply hne
    simpa using hZ' w hw ⟨inl h1, by rw [← hLz]
                                     simp [h0]⟩
  rw [show -zterm y β = (-1) * k β by simp [k, zterm]]
  refine hPole β (-1) ⟨hb1_, hb2_⟩ g hgd hgne fun w hw hwb => ?_
  rw [negLD, ← logDeriv_apply, ← hLz, logDeriv_mul (f := (· - cR β)) w (sub_ne_zero_of_ne hwb) (hgne w hw) (by fun_prop) $ hgd w]
  simp [logDeriv_apply]
  ring

end

section
open scoped ComplexOrder Nat

abbrev toAF {N : ℕ} (χ : DC N) : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun m : ℕ => χ m)

lemma product_lfunction_key_inequality {q1 q2 : ℕ} [NeZero q1] [NeZero q2]
    (chi1 : DC q1) (chi2 : DC q2) (ψ : DC (q1 * q2))
    (h1 : chi1 ^ 2 = 1) (h2 : chi2 ^ 2 = 1) (h1ne : chi1 ≠ 1) (h2ne : chi2 ≠ 1) (hpne : ψ ≠ 1) (hp_ : ∀ n : ℕ, ψ n = chi1 n * chi2 n)
    {σ : ℝ} (hs1_ : 0.875 ≤ σ) (hs2 : σ < 1) (hzero : LFunction chi1 σ = 0) :
    1 - σ ≤ 2 * exp 15 * (‖LFunction chi1 1‖ * ‖LFunction chi2 1‖ * ‖LFunction ψ 1‖) * rN (q1 * q2) ^ (8 * (1 - σ)) := by
  let Q := rN (q1 * q2)
  let F s := riemannZeta s * LFunction chi1 s * LFunction chi2 s * LFunction ψ s
  let lam := LFunction chi1 1 * LFunction chi2 1 * LFunction ψ 1
  let d := 1 - σ
  have h1s_ : 0 < d := by linarith
  have : Q = rN q1 * q2 := by grind
  have : r1 ≤ Q := one_le_modulus_real _
  let f : ArithmeticFunction ℂ := zetaMul chi1 * (toAF chi2 * toAF ψ)
  have hvals {N : ℕ} (χ : DC N) (hx_ : χ ^ 2 = 1) x : 0 ≤ χ x ∨ χ x = -1 := by
    rcases mpr isQuadratic_iff_sq_eq_one hx_ x with h | h | h <;> simp [h]
  have hpp {N N' : ℕ} {χ : DC N} {chi' : DC N'} (hx_ : χ ^ 2 = 1)
      (hpm : ∀ n : ℕ, ψ n = χ n * chi' n) {p : ℕ} (hp : p.Prime)
      (hc : 0 ≤ chi' p ∨ (chi' p = -1 ∧ χ p = -1)) k :
      0 ≤ (zetaMul χ * (toAF chi' * toAF ψ)) (p ^ k) := by
    rw [mul_apply]
    refine sum_nonneg fun x hx => mul_nonneg (zetaMul_nonneg hx_ _) ?_
    obtain ⟨j, -, hj⟩ := mp (dvd_prime_pow hp) $ Dvd.intro_left _ $ a1 $ mp mem_divisorsAntidiagonal hx
    rw [hj]
    have hconv : (toAF chi' * toAF ψ) (p ^ j) = chi' ((p ^ j : ℕ)) * zetaMul χ (p ^ j) := by
      rw [mul_apply, zetaMul, mul_apply, mul_sum]
      refine sum_congr rfl fun y hy => ?_
      obtain ⟨hab, -⟩ := mp mem_divisorsAntidiagonal hy
      have hy0 := mp mul_ne_zero_iff $ hab.trans_ne $ pow_ne_zero j hp.ne_zero
      simp [toAF, toArithmeticFunction, a1 hy0, a2 hy0, hpm y.2, ← hab]
      ring
    rw [hconv, cast_pow, map_pow]
    rcases hc with h | ⟨h, h'⟩
    exact mul_nonneg (pow_nonneg h j) $ zetaMul_nonneg hx_ _
    rw [h, zetaMul, coe_zeta_mul_apply, sum_divisors_prime_pow hp,
      sum_congr rfl (g := fun i => (-1) ^ i) fun i _ => by simp [toArithmeticFunction, hp.ne_zero, h'], neg_one_geom_sum]
    split_ifs with he
    simp
    rw [((even_or_odd j).resolve_right fun ho => he ho.add_one).neg_one_pow]
    norm_num
  have hmul := (isMultiplicative_zetaMul chi1).mul
    ((isMultiplicative_toArithmeticFunction chi2).mul $ isMultiplicative_toArithmeticFunction ψ)
  have ha0 n : 0 ≤ f n := by
    rcases eq_or_ne n 0 with rfl | hn
    simp
    rw [IsMultiplicative.multiplicative_factorization f hmul hn, Finsupp.prod]
    refine Finset.prod_nonneg fun p hp => ?_
    have hpr := prime_of_mem_primeFactors $ by simpa using hp
    rcases hvals chi2 h2 p with h | h
    exact hpp h1 hp_ hpr (inl h) _
    rcases hvals chi1 h1 p with h' | h'
    rw [show f = zetaMul chi2 * (toAF chi1 * toAF ψ) by simp [f, zetaMul, toAF]; ring]
    exact hpp h2 (fun m => by rw [hp_ m, mul_comm]) hpr (inl h') _
    exact hpp h1 hp_ hpr (inr ⟨h, h'⟩) _
  have hls {N : ℕ} [NeZero N] (χ : DC N) {s : ℂ} (hs : 1 < re s) : LSeriesSummable ⇑(toAF χ) s :=
    mpr (LSeriesSummable_congr s fun {n} hn => by simp [toArithmeticFunction, hn]) $ LSeriesSummable_of_one_lt_re χ hs
  have hle {N : ℕ} [NeZero N] (χ : DC N) {s : ℂ} (hs : 1 < re s) : LSeries ⇑(toAF χ) s = LFunction χ s :=
    (symm $ LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).trans $ symm $ LFunction_eq_LSeries χ hs
  have hlt2 : abscissaOfAbsConv ⇑f < (re 2) :=
    lt_of_le_of_lt (by
      simpa using abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := ⇑f) (x := 1) fun y hy =>
        LSeriesSummable_mul (LSeriesSummable_zetaMul chi1 $ by simpa using hy) $
          LSeriesSummable_mul (hls chi2 $ by simpa using hy) $ hls ψ $ by simpa using hy)
      (by exact_mod_cast (by norm_num))
  have hFa s (hs : 1 < re s) : F s = LSeries ⇑f s := by
    have h1s : LSeriesSummable ⇑(zeta : ArithmeticFunction ℂ) s :=
      mp (LSeriesSummable_congr s fun {n} hn => by simp) $ mpr LSeriesSummable_zeta_iff hs
    rw [LSeries_mul' (LSeriesSummable_zetaMul chi1 hs) $ LSeriesSummable_mul (hls chi2 hs) $ hls ψ hs,
      LSeries_mul' (hls chi2 hs) $ hls ψ hs, zetaMul, LSeries_mul' h1s $ hls chi1 hs, hle chi1 hs, hle chi2 hs, hle ψ hs,
      show L (fun n => (zeta : ArithmeticFunction ℂ) n) s = riemannZeta s from LSeries_zeta_eq_riemannZeta hs]
    ring
  let P s := LFunction chi1 s * LFunction chi2 s * LFunction ψ s
  let G := dslope (fun s => riemannZeta₁ s * P s) 1
  have hG : Differentiable ℂ G :=
    mp differentiableOn_univ $ mpr (differentiableOn_dslope univ_mem)
      (differentiable_riemannZeta₁.mul $ ((differentiable_LFunction h1ne).mul $ differentiable_LFunction h2ne).mul $ differentiable_LFunction hpne).differentiableOn
  have hGs s (hs : s ≠ 1) : G s = (riemannZeta₁ s * P s - P 1) / (s - 1) := by
    dsimp only [G]
    rw [dslope_of_ne _ hs, slope_def_field, riemannZeta₁_one, one_mul]
  have hFG s (hs : s ≠ 1) : F s = G s + lam / (s - 1) := by
    rw [hGs s hs]
    simp [F, P, lam, riemannZeta_eq_inv_sub_mul hs]
    field [sub_ne_zero_of_ne hs]
  let B := 4000000 * Q ^ 2
  have hPw {w : ℂ} (hre : 0.5 ≤ re w) (hn : norm w ≤ 3.5) : ‖P w‖ ≤ 22.5 ^ 3 * Q ^ 2 := by
    have hLs (r : ℕ) [NeZero r] (χ : DC r) (hx_ : χ ≠ 1) : ‖LFunction χ w‖ ≤ 22.5 * r :=
      le_trans (lfunction_polynomial_growth χ hx_ w hre) $ by nlinarith
    simp only [P, norm_mul]
    grw [hLs q1 chi1 h1ne, hLs q2 chi2 h2ne, hLs (q1 * q2) ψ hpne]
    nlinarith
  have hB s (hs : s ∈ sphere (2 : ℂ) 1.5) : ‖G s‖ ≤ B := by
    have := mp mem_sphere_iff_norm hs
    have hre : 0.5 ≤ re s := by
      linarith [re_le_norm $ 2 - s, show re (2 - s) = 2 - re s by simp, norm_sub_rev s 2]
    have hn : norm s ≤ 3.5 := by have := norm_sub_norm_le s 2
                                 norm_num at this
                                 linarith
    have hd : 0.5 ≤ ‖s - 1‖ := by have := norm_sub_le (s - 1) 1
                                  rw [sub_sub] at this
                                  norm_num at this
                                  linarith
    rw [hGs s $ mp sub_ne_zero $ mp norm_pos_iff $ by linarith, norm_div, div_le_iff₀ $ by linarith, riemannZeta₁]
    grw [norm_sub_le, norm_mul, norm_add_le, norm_mul, norm_sub_le, zeta0_growth_half hre, hn, hPw hre hn, hPw (by norm_num) $ by norm_num, ← hd]
    simp
    nlinarith
  let M := ⌈100 + 8 * log Q⌉₊
  have : 8 * B * 0.75 ^ M ≤ 1 := by
    rw [show 8 * B = 32000000 * exp (log Q) ^ 2 by rw [exp_log $ by linarith]; dsimp [B]; ring]
    grw [show (32000000 : ℝ) ≤ 2 ^ 25 by norm_num, show (2 : ℝ) ≤ exp 1 by linarith [add_one_le_exp 1],
      show 0.75 ≤ exp (-0.25) by linarith [add_one_le_exp $ -0.25], ← exp_nat_mul, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add]
    apply mpr exp_le_one_iff
    linarith [le_ceil $ 100 + 8 * log Q]
  set x : ℝ := 2 - σ
  let xc := cR x
  have hx0 : 0 ≤ x := by linarith
  have hcoef m : iteratedDeriv m (LSeries ⇑f) 2 = iteratedDeriv m G 2 + lam * ((-1) ^ m * cN $ m !) := by
    have hev : LSeries ⇑f =ᶠ[nhds 2] fun s => G s + lam * inv (s - 1) :=
      eventually_of_mem ((isOpen_re_gt 1).mem_nhds $ by norm_num) fun s hs =>
        (symm $ hFa s hs).trans $ by rw [hFG s fun h => by simp [h] at hs, div_eq_mul_inv]
    have hinv : ContDiffAt ℂ m (fun s => lam * inv (s - 1)) 2 := contDiffAt_const.mul ((contDiffAt_id.sub contDiffAt_const).inv $ by norm_num)
    rw [(hev.iteratedDeriv m).eq_of_nhds, iteratedDeriv_fun_add hG.contDiff.contDiffAt hinv,
      iteratedDeriv_const_mul_field, show (fun s : ℂ => inv $ s - 1) = fun z => inv (1 * z - 1) by simp]
    simp only [iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
    norm_num
  let t n := inv (cN $ n !) • (cR σ - 2) ^ n • iteratedDeriv n G 2
  have hTt : HasSum t $ G σ := hasSum_taylorSeries_of_entire hG 2 σ
  have hsplit := hTt.summable.sum_add_tsum_nat_add M
  rw [hTt.tsum_eq] at hsplit
  let β n : ℂ := inv (cN $ n !) * ((-1) ^ n * iteratedDeriv n (LSeries ⇑f) 2)
  have hsx : cR σ - 2 = -xc := by simp [x, xc]
  have ht n : t n = xc ^ n * β n - lam * xc ^ n := by
    dsimp only [t, β]
    simp [hsx, neg_pow xc n, hcoef n]
    field_simp [mpr cast_ne_zero $ factorial_ne_zero n]
    rw [neg_pow]
    ring_nf
    simp [mul_comm n 2, pow_mul]
  let S := ∑ i ∈ range M, xc ^ i * β i
  let R := ∑' i, t (i + M)
  have hfin : ∑ i ∈ range M, t i = S - lam * ((xc ^ M - 1) / (xc - 1)) := by
    rw [sum_congr rfl fun i _ => ht i, sum_sub_distrib, ← mul_sum, geom_sum_eq $ mpr ofReal_ne_one $ by linarith]
  have hpos : 1 ≤ S := by
    apply le_trans (b := LSeries ⇑f 2)
    simpa [f, hmul.map_one, LSeries] using (LSeriesSummable_of_abscissaOfAbsConv_lt_re hlt2).le_tsum 1 fun j _ => by simpa using term_nonneg (ha0 j) 2
    simpa [β] using single_le_sum (f := fun i => xc ^ i * β i) fun i _ =>
      mul_nonneg (pow_nonneg (by dsimp [xc, cR]; exact_mod_cast hx0) i) $
        mul_nonneg (mpr inv_nonneg $ cast_nonneg _) $ by simpa using iteratedDeriv_alternating ha0 hlt2 i
      (mpr mem_range $ mpr ceil_pos $ by positivity)
  have : norm R ≤ 4 * B * 0.75 ^ M := by
    grw [tsum_of_norm_bounded
      ((hasSum_geometric_of_lt_one (r := 0.75) (by norm_num) $ by norm_num).mul_left $ B * 0.75 ^ M)]
    norm_num
    grind
    intro i
    simp only [t, xc, smul_eq_mul, norm_mul, norm_inv, norm_pow, hsx, norm_neg, Complex.norm_natCast, norm_cR_nn hx0]
    grw [norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (i + M) (by norm_num) hG.diffContOnCl hB,
      show x ≤ 0.75 * 1.5 by linarith]
    rw [mul_pow, pow_add]
    field_simp
    rfl
  have hkey : F σ = S - lam * cR (x ^ M / (x - 1)) + R := by
    rw [hFG σ $ mpr ofReal_ne_one $ ne_of_lt hs2, ← hsplit, hfin,
      show cR σ - 1 = -(xc - 1) by simp [x, xc]
                                   ring]
    push_cast
    field_simp [sub_ne_zero_of_ne $ mpr ofReal_ne_one $ by linarith]
    ring
  have hpow' : x ^ M ≤ exp 15 * Q ^ (8 * d) := by
    rw [rpow_def_of_pos $ by linarith, ← exp_add]
    grw [show x ≤ exp d by linarith [add_one_le_exp d], ← exp_nat_mul]
    apply mpr exp_le_exp
    nlinarith [ceil_lt_add_one $ show 0 ≤ 100 + 8 * log Q by positivity]
  have h2 : re (lam * cR (x ^ M / (x - 1))) ≤ exp 15 * norm lam * Q ^ (8 * d) / d := by
    rw [show x - 1 = d by grind]
    grw [re_le_norm, norm_mul, norm_cR_nn, hpow']
    grind
  have := congrArg re hkey
  rw [show F σ = 0 by simp [F, hzero], zero_re, add_re, sub_re] at this
  have := mp (le_div_iff₀ h1s_) (by
    linarith [show -re R ≤ norm R by simpa using re_le_norm (-R), show 1 ≤ re S by simpa using a1 $ mp le_def hpos] :
      0.5 ≤ exp 15 * norm lam * Q ^ (8 * d) / d)
  simp only [lam, norm_mul] at this
  linarith

end

theorem exceptional_zero_bound_of (ε : ℝ) (he_ : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DC q) (β : ℝ),
      χ ^ 2 = 1 → χ ≠ 1 → LFunction χ (cR β) = 0 → β ≤ 1 - c * rN q ^ (-ε) := by
  have he6 : 0 < ε / 6 := by linarith
  have he3 : 0 < ε / 3 := by linarith
  let sig0 := max 0.875 $ 1 - ε / 48
  have hs01 : sig0 < 1 := max_lt (by norm_num) $ by linarith
  by_cases hex : ∃ (q1 : ℕ) (_ : NeZero q1) (chi1 : DC q1) (b1_ : ℝ),
      chi1 ^ 2 = 1 ∧ chi1 ≠ 1 ∧ sig0 ≤ b1_ ∧ b1_ < 1 ∧ LFunction chi1 b1_ = 0
  obtain ⟨q1, _, chi1, b1_, h1sq, h1ne, hb10, hb11, hzero⟩ := hex
  let d := 1 - b1_
  have hKa : 8 * d ≤ ε / 6 := by grind
  let L1n := ‖LFunction chi1 1‖
  have hL1 := mpr norm_pos_iff $ LFunction_apply_one_ne_zero h1ne
  obtain ⟨d1, hd1, hd1ne⟩ := mp Metric.eventually_nhds_iff
    ((((differentiable_LFunction h1ne).continuous.comp continuous_ofReal).continuousAt (x := 1)).eventually_ne $
      by simpa using LFunction_apply_one_ne_zero h1ne)
  have := one_le_modulus_real q1
  let r := min 0.25 $ ε / 6
  have hr4 : r ≤ 0.25 := min_le_left _ _
  have hr6 : r ≤ ε / 6 := min_le_right _ _
  let K1 := 9 + 6 / ε
  let K2 := (9 + 3 / ε) / r
  let c0 := d / (2 * exp 15 * L1n * K1 * rN q1 ^ (ε / 3))
  let c := min (min r d1) $ c0 / K2
  have hc : 0 < c := by positivity
  refine ⟨c, hc, fun q _ χ β hx2 hx1_ hb_ => ?_⟩
  have hq1 := one_le_modulus_real q
  have hq0 : 0 < rN q := by linarith
  have hb1_ := lt_of_not_ge fun hge => LFunction_ne_zero_of_one_le_re χ (inl hx1_) (by simpa using hge) hb_
  by_cases hbh : β ≤ 1 - r
  nlinarith [rpow_le_one_of_one_le_of_nonpos hq1 $ show -ε ≤ 0 by linarith, min_le_left (min r d1) $ c0 / K2, min_le_left r d1]
  push Not at hbh
  let c1_ := changeLevel (dvd_mul_right q1 q) chi1
  let c2_ := changeLevel (dvd_mul_left q q1) χ
  let ψ := c1_ * c2_
  by_cases hp1 : ψ = 1
  have hchg : c1_ = c2_ := by
    rw [← mul_one c1_, ← show c2_ ^ 2 = 1 by rw [← map_pow, hx2, map_one], sq, ← mul_assoc, show c1_ * c2_ = 1 from hp1, one_mul]
  have hL1eq := LFunction_changeLevel (dvd_mul_right q1 q) chi1 (s := cR β) $ inl h1ne
  dsimp [c1_] at hchg
  rw [hchg, LFunction_changeLevel (dvd_mul_left q q1) χ $ inl hx1_, hb_, zero_mul] at hL1eq
  have hprod_ne : ∏ p ∈ (q1 * q).primeFactors, (1 - chi1 p * p ^ (-cR β)) ≠ 0 :=
    mpr prod_ne_zero_iff fun p hp h0 => by
      have hpr := prime_of_mem_primeFactors hp
      have h1 := congrArg norm $ symm $ mp sub_eq_zero h0
      rw [norm_one, norm_mul, norm_natCast_cpow_of_pos hpr.pos, neg_re, ofReal_re] at h1
      have := rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpr.one_lt : r1 < p) (by linarith : -β < 0)
      nlinarith [norm_le_one chi1 p, rpow_nonneg (cast_nonneg p) $ -β]
  have hge : d1 ≤ 1 - β := by_contra fun hlt =>
    hd1ne (by rw [Real.dist_eq, abs_of_neg $ by linarith]; linarith) $ (mp mul_eq_zero $ symm hL1eq).resolve_right hprod_ne
  nlinarith [rpow_le_one_of_one_le_of_nonpos hq1 $ show -ε ≤ 0 by linarith, min_le_left (min r d1) $ c0 / K2, min_le_right r d1]
  have hp_ (n : ℕ) : ψ n = chi1 n * χ n := by
    by_cases h : IsUnit (n : ZMod $ q1 * q)
    have h1 {r : ℕ} (hr : r ∣ q1 * q) (ch : DC r) : changeLevel hr ch (n : ZMod $ q1 * q) = ch (n : ZMod r) := by
      simpa [IsUnit.unit_spec, cast_natCast hr] using changeLevel_eq_cast_of_dvd ch hr h.unit
    rw [MulChar.mul_apply, h1, h1]
    rw [MulChar.map_nonunit _ h]
    rcases mp not_and_or $ by simpa [isUnit_iff_coprime, coprime_mul_iff_right] using h with h' | h' <;>
      simp [isUnit_iff_coprime, h']
  have hlogR {x a : ℝ} (hx : 1 ≤ x) (ha : 0 < a) : 9 + log x ≤ (9 + inv a) * x ^ a := by
    nlinarith [one_le_rpow hx $ le_of_lt ha, trans_eq (log_le_rpow_div (by linarith : 0 ≤ x) ha) $ div_eq_inv_mul _ _]
  have hlow : c0 * rN q ^ (-(ε / 3)) ≤ ‖LFunction χ 1‖ := by
    let Q := rN $ q1 * q
    have hN : Q = rN q1 * q := by grind
    have hN1 : 1 ≤ Q := one_le_modulus_real _
    have h2 := product_lfunction_key_inequality chi1 χ ψ h1sq hx2 h1ne hx1_ hp1 hp_ (le_trans (le_max_left _ _) hb10) hb11 hzero
    have hLp : ‖LFunction ψ 1‖ ≤ K1 * Q ^ (ε / 6) := by
      grw [lfunction_norm_near_one ψ hp1 le_rfl $ by norm_num, rpow_zero, mul_one, hlogR hN1 he6]
      rw [inv_div]
    have hmulQ : Q ^ (ε / 6) * Q ^ (ε / 6) = rN q1 ^ (ε / 3) * rN q ^ (ε / 3) := by
      rw [← rpow_add, show ε / 6 + ε / 6 = ε / 3 by ring, hN, mul_rpow _ $ le_of_lt hq0]
      all_goals linarith
    rw [rpow_neg $ le_of_lt hq0, ← div_eq_mul_inv, div_le_iff₀ $ rpow_pos_of_pos hq0 _, div_le_iff₀ $ by positivity]
    dsimp [d]
    grw [h2, hLp, rpowLe hKa]
    apply le_of_eq
    linear_combination 2 * exp 15 * L1n * K1 * ‖LFunction χ 1‖ * hmulQ
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (C := K2 * rN q ^ (2 * ε / 3))
    (fun t _ => ((differentiable_LFunction hx1_ t).hasDerivAt.comp_ofReal).hasDerivWithinAt)
    (fun t ht => trans_eq (norm_deriv_le_of_forall_mem_sphere_norm_le (R := r) (C := (9 + 3 / ε) * rN q ^ (2 * ε / 3))
      (lt_min (by norm_num) he6) (differentiable_LFunction hx1_).diffContOnCl fun z hz => by
        have hre := a1 $ mp abs_le $ trans_eq (abs_re_le_norm $ z - t) $ mp mem_sphere_iff_norm hz
        simp only [sub_re, ofReal_re] at hre
        grw [lfunction_norm_near_one χ hx1_ (le_of_lt he3) (by grind) (by grind)
            (by linarith [norm_sub_norm_le z $ cR t, mp mem_sphere_iff_norm hz, norm_cR_nn $ by linarith [a1 ht], a2 ht]),
          hlogR hq1 he3]
        rw [mul_assoc, ← rpow_add hq0, inv_div]
        ring_nf
        rfl)
      (by dsimp [K2]; ring)) 1 ⟨le_of_lt hb1_, le_refl _⟩
  simp [hb_] at hmvt
  apply mp le_sub_comm
  rw [show -ε = -(ε / 3) - 2 * ε / 3 by ring, rpow_sub hq0]
  dsimp [c]
  grw [min_le_right (min r d1) $ c0 / K2]
  rw [div_mul_div_comm]
  exact divLe $ le_trans hlow $ trans_eq hmvt $ mul_comm _ _
  push Not at hex
  refine ⟨1 - sig0, by linarith, fun q _ χ β hx2 hx1_ hb_ => ?_⟩
  have := lt_of_not_ge fun hge => hex q _ χ β hx2 hx1_ hge (lt_of_not_ge fun hge => LFunction_ne_zero_of_one_le_re χ (inl hx1_) (by simpa using hge) hb_) hb_
  nlinarith [rpow_le_one_of_one_le_of_nonpos (one_le_modulus_real q) $ show -ε ≤ 0 by linarith]

def smA0 : ℝ := 2 * π * exp 1 * 4101 + 2 * exp 1 * (zfrC + 1) + 4 * (zfrC + 24 / zfrC0) + 2
def smC : ℝ := smA0 * (2 * (4 / zfrC0) ^ 2)

theorem smoothed_character_sum_of {q : ℕ} [NeZero q] (χ : DC q) (bet0 : Option ℝ) (y : ℝ)
    (hxq_ : Good χ) (hB : ExcZeros zfrC0 χ bet0)
    (hy : 2 ≤ y) (hs10 : 10 ≤ slog y) (hq : rN q ≤ exp (zfrC0 / 4 * slog y)) :
    ‖Schi χ y - (if χ = 1 then cR y / 2 else 0) + elim bet0 0 (zterm y)‖ ≤
      smC * y * exp (-(zfrC0 / 4) * slog y) := by
  let p0_ : Option ℝ := if χ = 1 then some 1 else bet0
  have hq1 := one_le_modulus_real q
  have hy0 : 0 < y := by linarith
  have hlogy : 0 < log y := log_pos $ by linarith
  let s := slog y
  let e1 := exp 1
  let c4 := zfrC0 / 4
  let T := exp $ zfrC0 * s / 2
  let lv := log $ q * (T + 2)
  let X := exp $ -(zfrC0 * s / 2)
  have hl : log y = s ^ 2 := by grind
  have hs0 : 0 < s := by linarith
  have hT1 : 1 ≤ T := one_le_exp $ by positivity
  have hT0 : 0 < T := exp_pos _
  have hL2 : log 2 ≤ lv := log_le_log two_pos $ by nlinarith
  have hL0 : 0 < lv := by linarith [log_two_gt_d9]
  have hL4 : 4 * lv ≤ s := by
    have hlogq : log q ≤ c4 * s := mpr (log_le_iff_le_exp $ by linarith) hq
    have hlogT : log (T + 2) ≤ 2 + zfrC0 * s / 2 := by
      rw [log_le_iff_le_exp $ by linarith, exp_add]
      dsimp [T] at hT1 ⊢
      nlinarith [add_one_le_exp 2]
    rw [show lv = log q + log (T + 2) from log_mul (by linarith) $ by linarith]
    dsimp [c4] at hlogq
    grind
  have hs1 : 1 ≤ s ^ 2 := by nlinarith
  have hLs2 : lv ≤ s ^ 2 := by nlinarith
  have hL2s2 : lv ^ 2 ≤ s ^ 2 := by nlinarith
  let u := zfrC0 / lv
  have hu0 : 0 < u := div_pos (by norm_num) hL0
  have hu1 : u ≤ 0.1 := divLe $ by linarith [ log_two_gt_d9]
  let sig1 := if ∀ p ∈ p0_, u / 24 ≤ abs (1 - u / 3 - p) then 1 - u / 3 else 1 - u / 4
  have hs1lo : 1 - u / 3 ≤ sig1 := by grind
  have hs1u : sig1 ≤ 1 - u / 4 := by grind
  have hs1Pu : ∀ p ∈ p0_, u / 24 ≤ abs (sig1 - p) := by
    dsimp [sig1]
    split_ifs with h
    assumption
    push Not at h
    obtain ⟨p, hp, hlt⟩ := h
    intro p' hp'
    obtain rfl : p = p' := inj $ (symm hp).trans hp'
    have := abs_sub_le (1 - u / 3) p $ 1 - u / 4
    rw [abs_of_neg $ by grind, abs_sub_comm p] at this
    grind
  have hhalf : 0.5 ≤ sig1 := by linarith
  have hs1lt1 : sig1 < 1 := by grind
  have hs1reg : 1 - zfrC0 / 2 / lv ≤ sig1 := by grind
  let sig0 := 1 + inv (log y)
  have hs0gt : 1 < sig0 := by linarith [mpr inv_pos hlogy]
  have hs011 : sig0 ≤ 1.1 := by
    dsimp [sig0]
    grw [invLe (a := 100) $ by nlinarith]
    norm_num
  have hsdiff : abs (sig0 - sig1) ≤ 1 := mpr abs_le ⟨by linarith, by linarith⟩
  have hyσ₀ : y ^ sig0 = e1 * y := by
    rw [rpow_add hy0, rpow_one, rpow_def_of_pos hy0, mul_inv_cancel₀ $ ne_of_gt hlogy, mul_comm]
  have hyT : y / T = y * X := by
    rw [div_eq_mul_inv, ← exp_neg]
  have hWX : T * y ^ sig1 ≤ y * X := by
    rw [rpow_def_of_pos hy0, hl, ← exp_add, ← exp_log hy0, hl, ← exp_add, exp_le_exp]
    dsimp [u] at hs1u
    have := mp (div_le_iff₀ hL0) (by grind : zfrC0 / lv ≤ 4 * (1 - sig1))
    have : zfrC0 ≤ (1 - sig1) * s := by nlinarith only [this, hL4, hs1lt1]
    have := mul_le_mul_of_nonneg_right this $ le_of_lt hs0
    ring_nf at this ⊢
    grind
  have hlmono t (ht : abs t ≤ T) : lcond q t ≤ lv :=
    logLe (mul_le_mul_of_nonneg_left (by linarith) $ by linarith) $ by positivity
  let keep := ∀ β ∈ bet0, sig1 < β
  let bf : Option ℝ := if keep then bet0 else none
  have hzer w (h1 : sig1 ≤ re w) (_ : re w ≤ sig0) (h3 : abs (im w) ≤ T) (h4 : IsLZero χ w) :
      ∃ β ∈ bf, w = cR β := by
    have hreg : InRegion zfrC0 q w := by
      unfold InRegion
      dsimp [u] at hs1lo hu0
      linarith [   div_le_div_of_nonneg_left (by norm_num : r0 ≤ zfrC0) (lcond_pos q $ im w) $ hlmono (im w) h3]
    obtain ⟨β, hbB, hwb⟩ := a2 hB w hreg h4
    have hlt := lt_of_le_of_ne (by simpa [hwb] using h1) fun h => by
      have := hs1Pu β $ by simp [p0_, a1 $ a1 hB β hbB, hbB]
      rw [h, sub_self, abs_zero] at this
      linarith
    have hk : keep := fun bet' hb' => inj ((symm hbB).trans hb') ▸ hlt
    exact ⟨β, by simpa [bf, hk] using hbB, hwb⟩
  have hFbd w N Ym dden (hN : ‖negLD χ w‖ ≤ N) (hYm : y ^ re w ≤ Ym) (hdd : dden ≤ norm w * ‖w + 1‖)
      (hdden : 0 < dden := by first | positivity | linarith) : ‖Fchi χ y w‖ ≤ N * Ym / dden := by
    have := le_trans (norm_nonneg _) hN
    unfold Fchi
    rw [norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hy0]
    grw [← hdd, hN, hYm]
  have hpt w (hwT : abs (im w) ≤ T) (hre : 1 - zfrC0 / 2 / lv ≤ re w) (hw11 : re w ≤ 1.1) dl
      (hdP : ∀ p ∈ p0_, dl ≤ ‖w - p‖) Ym dden (hYm : y ^ re w ≤ Ym) (hdd : dden ≤ norm w * ‖w + 1‖)
      (hd_ : 0 < dl := by positivity) (hdden : 0 < dden := by positivity) :
      ‖Fchi χ y w‖ ≤ (zfrC * lv ^ 2 + inv dl) * Ym / dden := by
    refine hFbd w _ Ym dden (le_trans (log_deriv_in_zero_free_region χ bet0 hxq_ hB w (hre.trans' $ by linarith [div_le_div_of_nonneg_left (by norm_num : 0 ≤ zfrC0 / 2) (lcond_pos q $ im w) $ hlmono (im w) hwT]) hw11 hd_ hdP) ?_) hYm hdd
    have := le_of_lt $ lcond_pos q $ im w
    grw [hlmono (im w) hwT]
  have hsqim z : im z ^ 2 ≤ norm z * ‖z + 1‖ := by
    rw [← sq_abs, sq]
    apply mul_le_mul (abs_im_le_norm z) _ (abs_nonneg _) $ norm_nonneg _
    simpa using abs_im_le_norm $ z + 1
  let Ec := ∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y (mk sig0 t)
  let V1 := ∫ v in (-T)..T, Fchi χ y (mk sig1 v)
  let a := ∫ x in sig1..sig0, Fchi χ y (mk x (-T))
  let b := ∫ x in sig1..sig0, Fchi χ y (mk x T)
  have hI1 : norm Ec ≤ 2 * π * e1 * 4101 * s ^ 2 * (y * X) := by
    let B := 4101 * s ^ 2 * (e1 * y)
    have hB0 : 0 ≤ B := by positivity
    have hg := (integrable_inv_one_add_sq.comp_div $ ne_of_gt hT0).const_mul $ 2 * B / T ^ 2
    refine le_trans (le_trans (norm_integral_le_of_norm_le hg.integrableOn ?_)
      (setIntegral_le_integral hg $ of_forall fun _ => by positivity)) $ le_of_eq ?_
    apply ae_restrict_of_forall_mem measurableSet_Ioc.compl fun t ht => ?_
    have ht2 : T ^ 2 ≤ t ^ 2 := by
      rcases mp not_and_or ht with h | h <;> nlinarith only [h, hT0]
    have ht2p : 0 < t ^ 2 := by nlinarith only [ht2, hT0]
    refine le_trans (hFbd (mk sig0 t) _ (e1 * y) (t ^ 2)
      (by simpa [sig0] using negLD_bound_right χ (s := mk sig0 t) hs0gt hs011)
      (le_of_eq hyσ₀) $ hsqim $ mk sig0 t) ?_
    grw [show log y + 4100 ≤ 4101 * s ^ 2 by grind]
    rw [div_le_iff₀ ht2p]
    field_simp
    nlinarith only [ht2, hB0]
    rw [integral_const_mul, Measure.integral_comp_div (fun x => inv $ 1 + x ^ 2) T,
      integral_univ_inv_one_add_sq, abs_of_pos hT0, ← hyT]
    dsimp [B]
    field_simp
  have hH v (hv : abs v = T) : ‖∫ x in sig1..sig0, Fchi χ y (mk x v)‖ ≤ e1 * (zfrC + 1) * s ^ 2 * (y * X) := by
    grw [norm_integral_le_of_norm_le_const (C := (zfrC * lv ^ 2 + 1) * (e1 * y) / T ^ 2) _,
      hsdiff, show zfrC * lv ^ 2 + 1 ≤ (zfrC + 1) * s ^ 2 by nlinarith only [hL2s2, hs1],
      ← show T ≤ T ^ 2 by nlinarith only [hT1]]
    rw [← hyT]
    ring_nf
    rfl
    intro x hx
    rw [uIoc_of_le $ by linarith] at hx
    simpa using hpt (mk x v) (le_of_eq hv) (le_trans hs1reg $ le_of_lt $ a1 hx)
      (le_trans (a2 hx) hs011) 1
      (fun p _ => le_trans hT1 $ by simpa [hv] using abs_im_le_norm $ mk x v - p) (e1 * y) (T ^ 2)
      (hyσ₀ ▸ rpowLe (a2 hx))
      (by simpa [← sq_abs v, hv] using hsqim $ mk x v)
  have hV : norm V1 ≤ 4 * (zfrC + 24 / zfrC0) * s ^ 2 * (y * X) := by
    grw [norm_integral_le_of_norm_le_const
      (C := (zfrC * lv ^ 2 + inv (u / 24)) * y ^ sig1 / 0.5) _,
      show abs (T - -T) = 2 * T by rw [abs_of_pos $ by linarith]
                                   ring]
    rw [inv_div, div_div_eq_mul_div]
    grw [hL2s2, hLs2]
    trans 4 * (zfrC + 24 / zfrC0) * s ^ 2 * (T * y ^ sig1)
    grind
    grw [hWX]
    intro v hv
    rw [uIoc_of_le $ by linarith only [hT0]] at hv
    exact hpt (mk sig1 v) (mpr abs_le ⟨le_of_lt $ a1 hv, a2 hv⟩) hs1reg
      (by linarith only [hs1lt1]) (u / 24)
      (fun p hp => le_trans (hs1Pu p hp) $ by simpa using abs_re_le_norm $ mk sig1 v - p) (y ^ sig1) 0.5
      le_rfl
      (by nlinarith only [hhalf, re_le_norm $ mk sig1 v,
            show sig1 + 1 ≤ ‖mk sig1 v + 1‖ by simpa using re_le_norm $ mk sig1 v + 1])
  have hrect := rectangle_contour_shift_character χ hxq_ y hy0 sig1 sig0 T bf (by linarith only [hhalf]) hs1lt1 hs0gt hT0
    (fun β hb_ => by
      dsimp [bf] at hb_
      split_ifs at hb_ with hk
      obtain ⟨hx1, -, hb1_, -, hbz, hd, -⟩ := a1 hB β hb_
      exact ⟨hx1, hk β hb_, by linarith, hbz, hd⟩
      simp at hb_)
    hzer
  obtain ⟨hint, hperron⟩ := perron_formula_character χ y (by linarith) sig0 hs0gt
  rw [← integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint, ← integral_of_le $ by grind] at hperron
  unfold rectInt at hrect
  let R := (if χ = 1 then cR y / 2 else 0) - elim bf 0 (zterm y)
  let D0 := Schi χ y - R
  have : 2 * π * norm D0 ≤ norm Ec + norm a + norm b + norm V1 := by
    have hEq : cR (2 * π) * D0 = Ec + I * a - I * b + V1 := by
      dsimp [D0, R]
      rw [hperron]
      push_cast
      field_simp [pi_ne_zero]
      have := congrArg (I * ·) hrect
      simp only [mul_add, mul_sub, ← mul_assoc, I_mul_I, mul_left_comm I $ 2 * ↑π] at this
      linear_combination -this
    rw [← norm_cR_nn (x := 2 * π), ← norm_mul, hEq]
    grw [norm_add_le, norm_sub_le, norm_add_le]
    simp
  let O := elim bet0 0 (zterm y) - elim bf 0 (zterm y)
  have : norm O ≤ 2 * s ^ 2 * (y * X) := by
    apply le_trans (?_ : norm O ≤ 2 * y ^ sig1)
    grw [← hs1, ← hWX, ← hT1]
    grind
    dsimp [O, bf]
    split_ifs with hk
    simp
    positivity
    rcases hβ₀ : bet0 with _ | β
    simp
    positivity
    have hbh := a1 $ a2 $ a1 hB β $ by simp [hβ₀]
    simp only [elim_some, elim_none, sub_zero, zterm]
    rw [norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, ofReal_re, norm_cR_nn,
      ← ofReal_one, ← ofReal_add, norm_cR_nn, div_le_iff₀ $ by positivity]
    grw [rpowLe $ mp not_lt fun hlt => hk fun _ hb' => inj ((symm hβ₀).trans hb') ▸ hlt, ← hbh]
    nlinarith only [hbh, rpow_nonneg (le_of_lt hy0) sig1]
  have hsum_le : ‖D0 + O‖ ≤ smA0 * (s ^ 2 * (y * X)) := by
    have hbot := hH (-T) $ by rw [abs_neg, abs_of_pos hT0]
    have htop := hH T $ abs_of_pos hT0
    dsimp [smA0, e1] at hI1 hbot htop hV ⊢
    linarith [norm_add_le D0 O, le_mul_of_one_le_left (norm_nonneg D0) (by linarith [pi_gt_three] : r1 ≤ 2 * π), hI1, hbot]
  have hsX : s ^ 2 * X ≤ 2 * (4 / zfrC0) ^ 2 * exp (-c4 * s) := by
    rw [show X = exp (-(c4 * s)) * exp (-c4 * s) by dsimp [X, c4]; rw [← exp_add]; congr 1; ring]
    nlinarith only [sqExpLe (x := zfrC0 / 4 * s), exp_pos $ -(zfrC0 / 4) * s]
  trans ‖D0 + O‖
  exact le_of_eq $ congrArg norm $ by ring
  apply le_trans hsum_le
  have : 0 ≤ smA0 := by dsimp [smA0]
                        positivity
  rw [mul_comm y X, ← mul_assoc $ s ^ 2]
  grw [hsX]
  dsimp [smC, c4, s]
  ring_nf
  rfl

lemma exp_half_sq_le_mul_exp {y c0_ : ℝ} (hy : 2 ≤ y) (hc01 : c0_ ≤ 1) :
    exp (log y / 2) ≤ y * exp (-(c0_ / 4) * slog y) := by
  have := logLe hy
  rw [← div_le_iff₀ $ exp_pos _, ← exp_sub, ← le_log_iff_exp_le $ by linarith]
  nlinarith [log_two_gt_d9, sqrt_nonneg $ log y, sq_sqrt $ show 0 ≤ log y by linarith [log_two_gt_d9]]

lemma second_diff_chebyshev_bound {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ Λ n)
    (M : ℝ → ℂ) (Z : ℂ) {c0_ Cs y : ℝ} (hc0 : 0 < c0_) (hc01 : c0_ ≤ 1)
    (hCs : 0 ≤ Cs) (hy : 2 ≤ y)
    (hM : let h := exp (-(c0_ / 2) * slog y)
      ‖cR (y * (1 + h)) * M (y * (1 + h)) - y * M y - cR (y * h) * Z‖ ≤ 2 * y ^ 2 * h ^ 2)
    (hE : ∀ z, y ≤ z → ‖Sa f z + M z‖ ≤ Cs * z * exp (-c0_ * slog z)) :
    ‖partialSumUpTo f y + Z‖ ≤ (33 / c0_ ^ 2 + 4 + 8 * Cs) * y * exp (-(c0_ / 4) * slog y) := by
  set lv := log y
  set s := slog y
  set g := exp $ -(c0_ / 4) * s
  dsimp only at hM
  set h := exp $ -(c0_ / 2) * s
  let Y := y * (1 + h)
  have : 0 < lv := by linarith [log_two_gt_d9, logLe hy]
  have : g ≤ 1 := mpr exp_le_one_iff $ mul_nonpos_of_nonpos_of_nonneg (by linarith) $ sqrt_nonneg _
  have hhg : h = g * g := by
    dsimp [h, g]
    rw [← exp_add]
    congr 1
    ring
  have : 0 < h := exp_pos _
  have : h ≤ g := by nlinarith [exp_pos $ -(c0_ / 4) * s]
  have hyY : y ≤ Y := by nlinarith
  have hErr z (hz1 : y ≤ z) (hz2 : z ≤ Y) : ‖cR z * (Sa f z + M z)‖ ≤ 2 * Cs * Y * y * h ^ 2 := by
    have : 0 ≤ z := by linarith
    rw [norm_mul, norm_cR_nn]
    grw [hE z hz1, show exp (-c0_ * slog z) ≤ h ^ 2 by
      rw [sq, ← exp_add, exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left (sqrt_le_sqrt $ logLe hz1) $ le_of_lt hc0], hz2, show z ≤ 2 * y by nlinarith]
    grind
  have hlog : log Y ≤ lv + 1 := by
    rw [log_mul $ by linarith]
    linarith [log_le_sub_one_of_pos $ show 0 < 1 + h by linarith]
    linarith
  have : lv + 1 ≤ 2 * (y * g) := by linarith [add_one_le_exp $ lv / 2, exp_half_sq_le_mul_exp hy hc01]
  have : g * (lv + 1) ≤ 33 / c0_ ^ 2 := by
    have : g * (c0_ / 4 * s) ^ 2 ≤ 2 := by
      dsimp [g]
      rw [neg_mul, mul_comm]
      exact sqExpLe
    exact leDiv $ by nlinarith [show c0_ ^ 2 * lv = 16 * (c0_ / 4 * s) ^ 2 by grind]
  let D := y * h
  have hws : ‖cR Y * Sa f Y - cR y * Sa f y - cR D * partialSumUpTo f y‖ ≤ (D + 1) * (D * (lv + 1)) := by
    have hSa z (hz : 0 < z) : cR z * Sa f z = ∑ n ∈ Icc 1 ⌊z⌋₊, f n * cR (z - n) := by
      unfold Sa
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      push_cast
      field [mpr ofReal_ne_zero $ ne_of_gt hz]
    rw [hSa Y $ by linarith, hSa y $ by linarith, partialSumUpTo, mul_sum,
      show Icc 1 ⌊Y⌋₊ = Icc 1 ⌊y⌋₊ ∪ Ioc ⌊y⌋₊ ⌊Y⌋₊ by
        have := floor_mono hyY
        ext k
        simp
        omega,
      sum_union $ disjoint_left.2 fun k => by simp
                                              omega,
      add_sub_right_comm, add_sub_right_comm, ← sum_sub_distrib, ← sum_sub_distrib,
      Finset.sum_eq_zero fun n _ => by dsimp [D, Y]
                                       push_cast
                                       ring, zero_add]
    have := log_nonneg $ show 1 ≤ Y by linarith
    grw [norm_sum_le, sum_le_card_nsmul _ _ (D * log Y) fun n hn => by
      rw [Finset.mem_Ioc] at hn
      have : y < rN n := by linarith [lt_floor_add_one y, (by exact_mod_cast a1 hn : rN ⌊y⌋₊ + 1 ≤ n)]
      have hn2 := le_trans (by exact_mod_cast a2 hn : rN n ≤ ⌊Y⌋₊) $ floor_le $ by linarith
      rw [norm_mul, norm_cR_nn]
      grw [hf n, vonMangoldt_le_log, logLe hn2, show Y - rN n ≤ D by linarith]
      exact le_of_eq $ mul_comm _ _, nsmul_eq_mul, hlog]
    gcongr
    rw [card_Ioc, cast_sub $ floor_mono hyY]
    linarith [floor_le $ show 0 ≤ Y by linarith, lt_floor_add_one y]
  refine le_of_mul_le_mul_left ?_ $ show 0 < D by positivity
  conv_lhs => rw [← norm_cR_nn (x := D), ← norm_mul]
  rw [
    show cR D * (partialSumUpTo f y + Z) = -(Y * Sa f Y - cR y * Sa f y - cR D * partialSumUpTo f y) -
      (Y * M Y - cR y * M y - cR D * Z) + (Y * (Sa f Y + M Y) - cR y * (Sa f y + M y)) by
        ring]
  grw [norm_add_le, norm_sub_le, norm_neg, hws, hM, norm_sub_le, hErr Y hyY le_rfl, hErr y le_rfl hyY]
  have : D * (lv + 1) ≤ y * g * (33 / c0_ ^ 2) := by dsimp [D]
                                                     rw [hhg]
                                                     nlinarith
  have : 4 * Cs * Y * y * h ^ 2 ≤ D * (8 * Cs * y * g) := by nlinarith [show (1 + h) * h ≤ 2 * g by nlinarith, show 0 ≤ 4 * Cs * y ^ 2 * h by positivity]
  nlinarith [show 0 ≤ D by positivity, show 0 ≤ 2 * D * y by positivity, show D = y * h from rfl]

namespace AlpogeRHCore4

theorem siegelWalfisz :
    ∀ A : ℝ, 0 < A → ∃ c C : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ),
        2 ≤ x → (q : ℝ) ≤ Real.log x ^ A →
          ‖(∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) -
            (if χ = 1 then (x : ℂ) else 0)‖ ≤
            C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  intro A hA
  let c0_ := zfrC0 / 4
  let c := c0_ / 4
  have hc0 : 0 < c0_ := by norm_num
  have hc01 : c0_ ≤ 1 := by norm_num
  have hc : 0 < c := by norm_num
  have hCs' : 0 ≤ smC := by dsimp [smC, smA0]
                            positivity
  let cbC := 33 / c0_ ^ 2 + 4 + 8 * smC + 18
  obtain ⟨cE, hcE, hEB⟩ := exceptional_zero_bound_of (inv $ 2 * A) $ by positivity
  obtain ⟨N, hN⟩ := mp eventually_atTop
    ((isLittleO_rpow_exp_pos_mul_atTop (2 * A) hc).bound one_pos)
  let U := max N 10
  let cf := min c cE
  let U2 := U ^ 2 + 1
  let eU := exp $ cf * U
  have hcf0 := lt_min hc hcE
  refine ⟨cf, cbC + U2 * eU, hcf0, fun q _ χ x hx hqL => ?_⟩
  let sx := slog x
  let E := x * exp (-cf * sx)
  let xc := cR x
  have hxpos : 0 < x := by linarith
  have hx0 := le_of_lt hxpos
  have hlx : 0 < log x := log_pos $ by linarith
  have hq1 := one_le_modulus_real q
  have : 0 ≤ E := by positivity
  rw [add_mul, add_mul, mul_assoc cbC, mul_assoc $ U2 * eU]
  change _ ≤ cbC * E + U2 * eU * E
  by_cases hsmall : exp (c * sx) < log x ^ A ∨ sx < 10
  have hLU : sx ≤ U := by
    rcases hsmall with hsmall | h10
    by_contra hcon
    have h2 := hN sx $ le_trans (le_max_left _ _) $ le_of_lt $ mp not_le hcon
    rw [norm_of_nonneg $ by positivity, norm_of_nonneg $ exp_nonneg _,
      show sx ^ (2 * A) = log x ^ A by rw [rpow_mul $ sqrt_nonneg _, rpow_two, sq_sqrt $ le_of_lt hlx]] at h2
    linarith
    exact le_trans (le_of_lt h10) $ le_max_right _ _
  grw [norm_sub_le, show ‖if χ = 1 then xc else 0‖ ≤ x by split_ifs <;> simp [xc, abs_of_nonneg hx0, hx0],
    norm_sum_le, sum_le_card_nsmul _ _ (log x) fun n hn => by
      rw [norm_mul, norm_cR_nn vonMangoldt_nonneg]
      grw [norm_le_one χ _, vonMangoldt_le_log, logLe (le_trans (mpr cast_le $ a2 $ mp mem_Icc hn) $ floor_le hx0) $ mpr cast_pos $ a1 $ mp mem_Icc hn]
      simp, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, floor_le hx0,
    show log x ≤ U ^ 2 by nlinarith [sq_sqrt $ le_of_lt hlx, sqrt_nonneg $ log x]]
  have he : 1 ≤ eU * exp (-cf * sx) := by
    rw [← exp_add]
    apply one_le_exp
    nlinarith
  apply le_add_of_nonneg_of_le
  positivity
  dsimp [U2, E, sx, slog] at he ⊢
  nlinarith [show 0 ≤ x * (U ^ 2 + 1) by positivity]
  push Not at hsmall
  obtain ⟨hsmall, hs10⟩ := hsmall
  have hq := le_trans hqL hsmall
  let h := exp $ -(c0_ / 2) * sx
  let Ex := x * exp (-c * sx)
  let h1 := 1 + h
  have hexp {a : ℝ} (ha : cf ≤ a) : x * exp (-a * sx) ≤ E :=
    mul_le_mul_of_nonneg_left (mpr exp_le_exp $ by nlinarith) hx0
  have hExE : Ex ≤ E := by grind
  by_cases hx_ : χ = 1
  subst hx_
  simp
  obtain ⟨b1, hZ1⟩ := exists_excZeros 1 $ inr rfl
  obtain rfl : b1 = none := mpr eq_none_iff_forall_ne_some fun β h => a1 (a1 hZ1 β h) rfl
  let f : ℕ → ℂ := fun n => ↑(Λ n) * c1 n
  have hm := second_diff_chebyshev_bound (f := f) fun n => by simp [f, c1a, abs_of_nonneg vonMangoldt_nonneg]
    (fun z => -(z / 2)) (-xc) hc0 hc01 hCs' hx (by
      dsimp only
      trans ‖-cR (x ^ 2 * h ^ 2 / 2)‖
      exact le_of_eq $ congrArg norm $ by dsimp [xc, h, sx]
                                          push_cast
                                          ring
      rw [norm_neg, norm_cR_nn]
      dsimp [h, sx]
      nlinarith)
    fun z hz => by
      simpa [sub_eq_add_neg, Schi, f, c0_] using smoothed_character_sum_of 1 none z (inr rfl) hZ1 (by linarith)
        (le_trans hs10 $ sqrt_le_sqrt $ logLe hz) $ by simpa using one_le_exp $ mul_nonneg (le_of_lt hc0) $ sqrt_nonneg _
  let S0 := (Icc 1 ⌊x⌋₊).filter fun n => ¬n.Coprime q ∧ Λ n ≠ 0
  let R := ∑ n ∈ S0, Λ n
  let K := Nat.log 2 ⌊x⌋₊
  have hpsi : partialSumUpTo (fun n => ↑(Λ n) * (1 : DC q) n) x - xc = (partialSumUpTo f x + -xc) - cR R := by
    rw [← sub_eq_add_neg, sub_right_comm]
    congr 1
    simp only [f, R, S0, sum_filter]
    push_cast
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    rw [c1a, mul_one]
    by_cases h : n.Coprime q
    simp [h, one_apply $ mpr (isUnit_iff_coprime n q) h]
    simp [h, MulChar.map_nonunit 1 fun hu => h $ mp (isUnit_iff_coprime n q) hu]
    split_ifs <;> simp_all
  have hnc1 : R ≤ rN K * log q := trans_eq (sum_le_sum_of_subset_of_nonneg fun n hn => by
      rw [Finset.mem_filter, mem_Icc] at hn
      obtain ⟨p, k, hp, -, rfl⟩ := mp (isPrimePow_nat_iff n) $ mp vonMangoldt_ne_zero_iff hn.2.2
      exact mpr mem_divisors ⟨(pow_dvd_pow_of_dvd (by_contra fun hc => hn.2.1 $ (mpr hp.coprime_iff_not_dvd hc).pow_left k) k).trans $ pow_dvd_pow q $ le_log_of_pow_le one_lt_two $ le_trans (pow_le_pow_left hp.two_le k) hn.1.2, pow_ne_zero _ $ ne q⟩
    fun _ _ _ => vonMangoldt_nonneg) $ by rw [vonMangoldt_sum, cast_pow, log_pow]
  have hncb : rN K * log q ≤ 16 * Ex := by
    have hK : rN K * log 2 ≤ log x := by
      rw [← log_pow]
      exact logLe $ le_trans (by exact_mod_cast pow_log_le_self 2 $ ne_of_gt $ mpr floor_pos $ by linarith) $ floor_le hx0
    grw [show rN K ≤ 2 * log x by nlinarith only [hK, log_two_gt_d9, cast_nonneg (α := ℝ) K], mpr (log_le_iff_le_exp $ by linarith) hq,
      show c ≤ 0.25 by norm_num]
    dsimp [Ex, c, sx]
    nlinarith only [quadratic_le_exp_of_nonneg $ show 0 ≤ log x / 2 by linarith,
      show sx ≤ log x by nlinarith only [sq_sqrt $ le_of_lt hlx, hs10], hlx, exp_half_sq_le_mul_exp hx hc01]
  rw [hpsi]
  have htri := trans_eq (norm_sub_le (partialSumUpTo f x + -xc) R) $ by rw [norm_cR_nn $ sum_nonneg fun _ _ => vonMangoldt_nonneg]
  apply le_add_of_le_of_nonneg ?_
  positivity
  dsimp [Ex, c, sx, cbC, R] at hnc1 hncb hExE ⊢
  nlinarith
  simp [hx_]
  obtain ⟨bet0, hB⟩ := exists_excZeros χ $ inl hx_
  let f : ℕ → ℂ := fun n => ↑(Λ n) * χ n
  let M z := elim bet0 0 $ zterm z
  let Z := elim bet0 0 fun β => xc ^ cR β / cR β
  have hM : ‖cR (x * h1) * M (x * h1) - xc * M x - cR (x * h) * Z‖ ≤ 2 * x ^ 2 * h ^ 2 := by
    rcases hβ₀ : bet0 with _ | β
    simp [M, Z, hβ₀]
    positivity
    obtain ⟨-, hb1_, hb2_, -⟩ := a1 hB β $ by simp [hβ₀]
    have hh1p : 0 < h1 := by positivity
    have hdiff0 : 0 ≤ h1 ^ (β + 1) - 1 - (β + 1) * h := by
      linarith [one_add_mul_self_le_rpow_one_add (s := h) (p := β + 1) (by linarith) $ by linarith]
    have hdiffu : h1 ^ (β + 1) - 1 - (β + 1) * h ≤ (β + 1) * h ^ 2 := by
      rw [rpow_add hh1p, rpow_one]
      nlinarith [rpow_one_add_le_one_add_mul_self (s := h) (p := β) (by linarith) (by linarith) $ le_of_lt hb2_]
    trans ‖cR (x * x ^ β / (β * (β + 1)) * (h1 ^ (β + 1) - 1 - (β + 1) * h))‖
    exact le_of_eq $ congrArg norm $ by
      simp only [M, Z, zterm, hβ₀, elim_some, xc]
      rw [← ofReal_cpow hx0, ← ofReal_cpow $ by positivity, mul_rpow hx0 $ le_of_lt hh1p, rpow_add hh1p, rpow_one]
      push_cast
      field [mpr ofReal_ne_zero $ show β ≠ 0 by linarith, show (β : ℂ) + 1 ≠ 0 by exact_mod_cast (by linarith)]
    rw [norm_cR_nn]
    grw [rpowLe $ le_of_lt hb2_, ← hb1_, hdiffu]
    rw [rpow_one]
    field_simp [show β + 1 ≠ 0 by linarith]
    linarith
  have hm := second_diff_chebyshev_bound (f := f) fun n => by
      simp only [f, norm_mul, norm_cR_nn vonMangoldt_nonneg]
      exact mul_le_of_le_one_right vonMangoldt_nonneg $ norm_le_one χ _
    M Z hc0 hc01 hCs' hx hM fun z hz => by
      simpa [hx_, Schi, f, M, c0_] using smoothed_character_sum_of χ bet0 z (inl hx_) hB (by linarith)
        (le_trans hs10 $ sqrt_le_sqrt $ logLe hz)
        (le_trans hq (mpr exp_le_exp $ by dsimp [c, c0_]; nlinarith [sqrt_le_sqrt $ logLe hz, sqrt_nonneg $ log z]))
  have : norm Z ≤ 2 * x * exp (-cE * sx) := by
    rcases hβ₀ : bet0 with _ | β
    simp [Z, hβ₀]
    positivity
    obtain ⟨-, hb1_, hblt1, -, hL0, -, hsq⟩ := a1 hB β $ by simp [hβ₀]
    have hb2_ := hEB q χ β hsq hx_ hL0
    have hq0 : 0 < rN q := by positivity
    simp only [Z, hβ₀, elim_some]
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos hxpos, ofReal_re, norm_cR_nn]
    have h3 : cE ≤ (1 - β) * sx := by
      rw [rpow_neg $ le_of_lt hq0] at hb2_
      have := mp (mul_inv_le_iff₀ $ rpow_pos_of_pos hq0 _) $ mp le_sub_comm hb2_
      have : rN q ^ inv (2 * A) ≤ sx := by
        grw [rpow_le_rpow (le_of_lt hq0) hqL $ by positivity, ← rpow_mul $ le_of_lt hlx, show A * inv (2 * A) = 1 / 2 by field_simp, ← sqrt_eq_rpow]
      nlinarith
    have hxb : x ^ β ≤ x * exp (-cE * sx) := by
      rw [rpow_def_of_pos hxpos]
      conv_rhs => rw [← exp_log hxpos, ← exp_add]
      rw [exp_le_exp]
      dsimp [sx, slog] at h3 ⊢
      nlinarith [mul_self_sqrt $ le_of_lt hlx]
    exact divLe $ by nlinarith only [hb1_, hxb, rpow_pos_of_pos hxpos β]
  have htri := norm_sub_le (partialSumUpTo f x + Z) Z
  rw [add_sub_cancel_right] at htri
  rw [mul_assoc] at hm
  change ‖partialSumUpTo f x‖ ≤ _
  apply le_add_of_le_of_nonneg ?_
  positivity
  dsimp [Ex, c, sx, cbC] at hExE ⊢
  nlinarith [htri, hm, hExE, hexp $ min_le_right c cE, show r0 ≤ 33 / c0_ ^ 2 + 4 + 8 * smC by positivity]

end AlpogeRHCore4
