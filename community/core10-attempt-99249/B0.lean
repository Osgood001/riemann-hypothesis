import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix Set Finset Filter Function Subgroup MulAction QuotientGroup
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

abbrev oR := ENNReal.ofReal
abbrev a1 := @And.left
abbrev a2 := @And.right
abbrev GL2 (R : Type) [CommRing R] := GL (Fin 2) R

lemma im_smul (g : GL2 ℝ) (z : P) : (g • z).1.im = g.val.det * z.1.im / normSq (den g z.1) := im_div g z.1

lemma nsq_sub_conj (z w : ℂ) : ‖z - conj w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im + w.im) ^ 2 := by
  rw [Complex.sq_norm, normSq_apply]; simp; ring

lemma pos_den_conj {z w : ℂ} (h : 0 < z.im * w.im) : 0 < ‖z - conj w‖ ^ 2 := by
  rw [nsq_sub_conj]; nlinarith [sq_nonneg (z.re - w.re), sq_nonneg z.im, sq_nonneg w.im]

lemma sub_conj_ne {z w : ℂ} (h : 0 < z.im * w.im) : z - conj w ≠ 0 :=
  norm_ne_zero_iff.1 (sq_pos_iff.1 (pos_den_conj h))

lemma e01_ne {F : Type} [Field F] : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1

lemma rep_spec {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (ω : D.Om) :
    ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := Quotient.out_eq ω

lemma sq_rpow_half {n : ℝ} (hn : 0 ≤ n) (k : ℕ) : (n ^ 2) ^ ((k : ℝ) / 2) = n ^ k := by
  rw [← rpow_natCast n 2, ← rpow_mul hn, ← rpow_natCast n k]; congr 1; push_cast; ring

-- === B1a: Half-plane measure invariance ===

lemma isOpen_U : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun continuous_im continuous_const
lemma openEmb_P : Topology.IsOpenEmbedding (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) := isOpen_U.isOpenEmbedding_subtypeVal
lemma measEmb_P : MeasurableEmbedding (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) := openEmb_P.measurableEmbedding

lemma cont_smul_P (g : GL2 ℝ) : Continuous (fun z : P => g • z) :=
  continuous_induced_rng.2 $ Continuous.div (by unfold num; fun_prop) (by unfold den; fun_prop) fun z => den_ne g z.2

lemma mp_smul_P (g : GL2 ℝ) : MeasurePreserving (fun z : P => g • z) volume volume := by
  let F (h : GL2 ℝ) (z : ℂ) := num h z / den h z
  have hvol (s : Set {z : ℂ // z.im ≠ 0}) (hs : MeasurableSet s) :
      (volume : Measure P) s = ∫⁻ z in Subtype.val '' s, oR (1 / z.im ^ 2) := by
    change (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).withDensity (fun z => oR (1 / z.1.im ^ 2)) s = _
    rw [withDensity_apply _ hs, measEmb_P.restrict_comap, ← measEmb_P.lintegral_map (f := fun z : ℂ => oR (1 / z.im ^ 2)),
      measEmb_P.map_comap, Measure.restrict_restrict measEmb_P.measurableSet_range, inter_eq_right.2 (image_subset_range _ _)]
  have hkey (h : GL2 ℝ) {S : Set ℂ} (hS : MeasurableSet S) (hSU : S ⊆ {z : ℂ | z.im ≠ 0}) :
      ∫⁻ x in F h '' S, oR (1 / x.im ^ 2) = ∫⁻ x in S, oR (1 / x.im ^ 2) := by
    let D z := (ContinuousLinearMap.toSpanSingleton ℂ ((h.val.det : ℂ) / den h z ^ 2)).restrictScalars ℝ
    have hfd x (hx : x ∈ S) : HasFDerivAt (F h) (D x) x := by
      have hd : HasDerivAt (F h) ((h.val.det : ℂ) / den h x ^ 2) x :=
        ((((hasDerivAt_id x).const_mul ((h 0 0 : ℝ) : ℂ)).add_const _).div
          (((hasDerivAt_id x).const_mul ((h 1 0 : ℝ) : ℂ)).add_const _) (den_ne h (hSU hx))).congr_deriv $ by
            simp only [den, id, mul_one]; rw [det_eq]; push_cast; ring
      simpa [D] using hd.hasFDerivAt.restrictScalars ℝ
    have hinj : InjOn (F h) S := fun x hx y hy hxy => by
      let px : P := ⟨x, hSU hx⟩; let py : P := ⟨y, hSU hy⟩
      exact congrArg Subtype.val (@smul_left_cancel (GL2 ℝ) P _ _ h px py (Subtype.ext hxy))
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS (fun x hx => (hfd x hx).hasFDerivWithinAt) hinj]
    refine setLIntegral_congr_fun hS fun x hx => ?_
    have hd := den_ne h (hSU hx)
    have hn : normSq (den h x) ≠ 0 := by simpa using hd
    have hdet := h.det_ne_zero
    have hdetD : (D x).det = normSq ((h.val.det : ℂ) / den h x ^ 2) := by
      simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
    rw [hdetD, abs_of_nonneg (normSq_nonneg _), ← ENNReal.ofReal_mul (normSq_nonneg _)]
    congr 1; rw [im_div, normSq_div, normSq_ofReal, map_pow]; field_simp
  refine ⟨(cont_smul_P g).measurable, Measure.ext fun s hs => ?_⟩
  let s1 : Set {z : ℂ // z.im ≠ 0} := (fun z : P => g • z) ⁻¹' s
  let s2 : Set {z : ℂ // z.im ≠ 0} := s
  rw [Measure.map_apply (cont_smul_P g).measurable hs]
  change (volume : Measure P) s1 = (volume : Measure P) s2
  rw [hvol s1 ((cont_smul_P g).measurable hs), hvol s2 hs]
  have himg : Subtype.val '' s1 = F g⁻¹ '' (Subtype.val '' s2) := by
    ext x; simp only [Set.mem_image]
    refine ⟨fun ⟨p, hp, hpx⟩ => let p' : P := p; ⟨(g • p').1, ⟨g • p', hp, rfl⟩,
        by change (g⁻¹ • (g • p')).1 = x; rwa [inv_smul_smul]⟩,
      fun ⟨_, ⟨q, hq, rfl⟩, hqx⟩ => let q' : P := q; ⟨g⁻¹ • q', by change g • (g⁻¹ • q') ∈ s; rwa [smul_inv_smul], hqx⟩⟩
  rw [himg, hkey g⁻¹ (measEmb_P.measurableSet_image.2 hs) fun _ ⟨p, _, hp⟩ => hp ▸ p.2]

theorem half_plane_measure_invariant_proof : B1a := by
  have hsf : SigmaFinite (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume) :=
    SigmaFinite.of_map _ measEmb_P.measurable.aemeasurable (by rw [measEmb_P.map_comap]; infer_instance)
  have hm : Measurable (fun z : {z : ℂ // z.im ≠ 0} => oR (1 / z.1.im ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div ((measurable_im.comp measEmb_P.measurable).pow_const 2))
  refine ⟨@SigmaFinite.withDensity_ofReal _ _ _ hsf _, ⟨fun A hA hne => ?_⟩, fun g => ⟨cont_smul_P g, mp_smul_P g⟩⟩
  have : (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap _ openEmb_P
  let A' : Set {z : ℂ // z.im ≠ 0} := A
  have hA' : IsOpen A' := hA
  change (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).withDensity (fun z => oR (1 / z.1.im ^ 2)) A' ≠ 0
  rw [Ne, withDensity_apply_eq_zero hm, show {x : {z : ℂ // z.im ≠ 0} | oR (1 / x.1.im ^ 2) ≠ 0} ∩ A' = A' from
    inter_eq_right.2 fun x _ => by have := x.2; simp [oR]; positivity]
  exact hA'.measure_ne_zero _ hne

-- === B1b & B1c: Automorphy factor, kernel algebra, and kappa properties ===

lemma clopen_pos_im : IsClopen {p : P × P | 0 < p.1.1.im * p.2.1.im} := by
  have hc : Continuous fun p : P × P => p.1.1.im * p.2.1.im := by fun_prop
  refine ⟨?_, isOpen_lt continuous_const hc⟩
  rw [show {p : P × P | 0 < p.1.1.im * p.2.1.im} = {p : P × P | 0 ≤ p.1.1.im * p.2.1.im} from
    Set.ext fun p => by simp only [Set.mem_ofPred_eq]; exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (mul_ne_zero p.1.2 p.2.2).symm⟩]
  exact isClosed_le continuous_const hc

lemma den_mul (g h : GL2 ℝ) (z : P) : den (g * h) z.1 = den g (h • z).1 * den h z.1 := by
  have h0 := den_ne h z.2; rw [coe_smul]
  conv_rhs => rw [den, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
  simp [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma j1_mul (k : ℕ) (g h : GL2 ℝ) (z : P) : j1 k (g * h) z = j1 k g (h • z) * j1 k h z := by
  simp only [j1, den_mul, mul_pow, Units.val_mul, Matrix.det_mul, abs_mul,
    mul_rpow (abs_nonneg _) (abs_nonneg _), ofReal_mul]; ring

lemma j1_ne (k : ℕ) (g : GL2 ℝ) (z : P) : j1 k g z ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (den_ne g z.2)) (ofReal_ne_zero.2 (rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne')

lemma sub_conj_smul (g : GL2 ℝ) (z w : P) :
    (g • z).1 - conj (g • w).1 = (g.val.det : ℂ) * (z.1 - conj w.1) / (den g z.1 * conj (den g w.1)) := by
  rw [coe_smul, coe_smul, map_div₀, div_sub_div _ _ (den_ne g z.2) ((map_ne_zero _).2 (den_ne g w.2))]
  congr 1; simp only [num, den, map_add, map_mul, conj_ofReal, det_eq]; push_cast; ring

lemma sign_smul (g : GL2 ℝ) (z w : P) : 0 < (g • z).1.im * (g • w).1.im ↔ 0 < z.1.im * w.1.im := by
  rw [im_smul, im_smul]
  have hd := g.det_ne_zero
  have nz : 0 < normSq (den g z.1) := normSq_pos.2 (den_ne g z.2)
  have nw : 0 < normSq (den g w.1) := normSq_pos.2 (den_ne g w.2)
  have hc : 0 < g.val.det ^ 2 / (normSq (den g z.1) * normSq (den g w.1)) := by positivity
  rw [show g.val.det * z.1.im / normSq (den g z.1) * (g.val.det * w.1.im / normSq (den g w.1))
      = g.val.det ^ 2 / (normSq (den g z.1) * normSq (den g w.1)) * (z.1.im * w.1.im) by field_simp]
  exact mul_pos_iff_of_pos_left hc

lemma q1_smul (k : ℕ) (g : GL2 ℝ) (z w : P) : q1 k (g • z) (g • w) * j1 k g w = j1 k g z * q1 k z w := by
  unfold q1; rw [if_congr (sign_smul g z w) rfl rfl]
  split_ifs with h
  · have hd : (g.val.det : ℂ) ≠ 0 := ofReal_ne_zero.2 g.det_ne_zero
    have h1 := den_ne g z.2; have h2 := den_ne g w.2
    have h3 : conj (den g w.1) ≠ 0 := (map_ne_zero _).2 h2
    have h4 := sub_conj_ne h
    have hrat : ((g • w).1 - conj (g • w).1) / ((g • z).1 - conj (g • w).1)
        = (w.1 - conj w.1) / (z.1 - conj w.1) * (den g z.1 / den g w.1) := by
      rw [sub_conj_smul, sub_conj_smul]; field_simp
    rw [hrat, mul_pow, div_pow, div_pow]; have := pow_ne_zero k h2; simp only [j1]; field_simp
  · simp

lemma kap_smul (g : GL2 ℝ) (z w : P) : kap (g • z) (g • w) = kap z w := by
  unfold kap; rw [if_congr (sign_smul g z w) rfl rfl]
  split_ifs with h
  · have hd := g.det_ne_zero
    have nz : normSq (den g z.1) ≠ 0 := (normSq_pos.2 (den_ne g z.2)).ne'
    have nw : normSq (den g w.1) ≠ 0 := (normSq_pos.2 (den_ne g w.2)).ne'
    have h4 : ‖z.1 - conj w.1‖ ≠ 0 := norm_ne_zero_iff.2 (sub_conj_ne h)
    rw [im_smul, im_smul, sub_conj_smul, norm_div, norm_mul, norm_mul, norm_conj, norm_real,
      Real.norm_eq_abs, div_pow, mul_pow, mul_pow, sq_abs]
    simp only [Complex.sq_norm]; field_simp
  · rfl

lemma norm_j1 (k : ℕ) (g : GL2 ℝ) (z : P) : ‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2) = |z.1.im| ^ ((k : ℝ) / 2) := by
  have hD : 0 < ‖den g z.1‖ := norm_pos_iff.2 (den_ne g z.2)
  have hdet : 0 < |g.val.det| := abs_pos.2 g.det_ne_zero
  rw [j1, im_smul, normSq_eq_norm_sq, abs_div, abs_mul, abs_of_nonneg (sq_nonneg ‖den g z.1‖),
    norm_mul, norm_pow, norm_real, Real.norm_of_nonneg (rpow_nonneg (abs_nonneg _) _),
    div_rpow (by positivity) (by positivity), mul_rpow (abs_nonneg _) (abs_nonneg _), sq_rpow_half (norm_nonneg _)]
  have hinv : |g.val.det| ^ (-(k : ℝ) / 2) * |g.val.det| ^ ((k : ℝ) / 2) = 1 := by
    rw [neg_div, rpow_neg (abs_nonneg _), inv_mul_cancel₀ (rpow_pos_of_pos hdet _).ne']
  have hDk : ‖den g z.1‖ ^ k ≠ 0 := pow_ne_zero _ hD.ne'
  calc ‖den g z.1‖ ^ k * |g.val.det| ^ (-(k : ℝ) / 2) * (|g.val.det| ^ ((k : ℝ) / 2) * |z.1.im| ^ ((k : ℝ) / 2) / ‖den g z.1‖ ^ k)
      = (|g.val.det| ^ (-(k : ℝ) / 2) * |g.val.det| ^ ((k : ℝ) / 2)) * |z.1.im| ^ ((k : ℝ) / 2) * (‖den g z.1‖ ^ k / ‖den g z.1‖ ^ k) := by ring
    _ = _ := by rw [hinv, div_self hDk, one_mul, mul_one]

lemma norm_q1 (k : ℕ) (z w : P) (hk : 1 ≤ k) :
    ‖q1 k z w‖ * |z.1.im| ^ ((k : ℝ) / 2) = ((k : ℝ) - 1) / (4 * π) * kap z w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold q1 kap; split_ifs with h
  · have hdn : 0 < ‖z.1 - conj w.1‖ := norm_pos_iff.2 (sub_conj_ne h)
    have hww : ‖w.1 - conj w.1‖ = 2 * |w.1.im| := by
      rw [Complex.sub_conj, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    have hc : ‖((k : ℂ) - 1) / (4 * π)‖ = ((k : ℝ) - 1) / (4 * π) := by
      rw [show ((k : ℂ) - 1) / (4 * π) = (((k : ℝ) - 1) / (4 * π) : ℝ) by push_cast; ring,
        norm_real, Real.norm_of_nonneg (div_nonneg (by linarith) (by positivity))]
    have hzw : z.1.im * w.1.im = |z.1.im| * |w.1.im| := by rw [← abs_mul, abs_of_pos h]
    have h4 : (4 : ℝ) ^ ((k : ℝ) / 2) = 2 ^ k := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sq_rpow_half (by norm_num)]
    have hsq : |w.1.im| ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) = |w.1.im| ^ k := by
      rw [← mul_rpow (abs_nonneg _) (abs_nonneg _), ← sq, sq_rpow_half (abs_nonneg _)]
    rw [norm_mul, hc, norm_pow, norm_div, hww, hzw, div_rpow (by positivity) (by positivity),
      sq_rpow_half hdn.le, mul_rpow (by norm_num) (by positivity), mul_rpow (abs_nonneg _) (abs_nonneg _),
      h4, div_pow, mul_pow, ← hsq]; ring
  · rw [norm_zero, zero_mul, zero_rpow (by linarith), mul_zero, zero_mul]

lemma cont_j1 (k : ℕ) (g : GL2 ℝ) : Continuous (j1 k g) := by unfold j1 den; fun_prop

lemma cont_q1 (k : ℕ) : Continuous fun p : P × P => q1 k p.1 p.2 := by
  unfold q1
  refine continuous_if (fun a ha => (clopen_pos_im.frontier_eq ▸ ha).elim) ?_ continuousOn_const
  rw [clopen_pos_im.1.closure_eq]
  exact (continuousOn_const.mul ((Continuous.continuousOn (by fun_prop)).div
    (Continuous.continuousOn (by fun_prop)) (fun p hp => sub_conj_ne hp) |>.pow k))

lemma hol_q1 (k : ℕ) (w : P) : Hol1 fun z => q1 k z w := fun t ht => by
  apply DifferentiableAt.differentiableWithinAt
  have hcont : Continuous fun s : ℂ => s.im * w.1.im := continuous_im.mul continuous_const
  by_cases hp : 0 < t.im * w.1.im
  · refine (show DifferentiableAt ℂ (fun s => ((k : ℂ) - 1) / (4 * π) * ((w.1 - conj w.1) / (s - conj w.1)) ^ k) t by
      fun_prop (disch := exact sub_conj_ne hp)).congr_of_eventuallyEq ?_
    filter_upwards [(hcont.tendsto t).eventually (lt_mem_nhds hp)] with s hs
    have hs' : s.im ≠ 0 := fun h0 => by simp [h0] at hs
    simp [ext1, hs', q1, hs]
  · have hneg : t.im * w.1.im < 0 := lt_of_le_of_ne (not_lt.1 hp) (mul_ne_zero ht w.2)
    refine (differentiableAt_const 0).congr_of_eventuallyEq ?_
    filter_upwards [(hcont.tendsto t).eventually (gt_mem_nhds hneg)] with s hs
    by_cases hs' : s.im ≠ 0 <;> simp [ext1, hs', q1, not_lt.2 hs.le]

theorem automorphy_factor_kernel_algebra_proof : B1b :=
  ⟨j1_mul, j1_ne, q1_smul, kap_smul, norm_j1, norm_q1, cont_j1, cont_q1, hol_q1⟩

lemma kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap; split_ifs with h; exact div_nonneg (by linarith) (sq_nonneg _); exact le_rfl

lemma kap_le_one (z w : P) : kap z w ≤ 1 := by
  unfold kap; split_ifs with h
  · rw [div_le_iff₀ (pos_den_conj h), nsq_sub_conj]
    nlinarith [sq_nonneg (z.1.re - w.1.re), sq_nonneg (z.1.im - w.1.im)]
  · norm_num

lemma kap_symm (z w : P) : kap z w = kap w z := by
  unfold kap; rw [mul_comm z.1.im w.1.im, show ‖z.1 - conj w.1‖ ^ 2 = ‖w.1 - conj z.1‖ ^ 2 by rw [nsq_sub_conj, nsq_sub_conj]; ring]

lemma kap_self (z : P) : kap z z = 1 := by
  have h := mul_self_pos.2 z.2
  rw [kap, ite_eq_left h, div_eq_one_iff_eq (pos_den_conj h).ne', nsq_sub_conj]; ring

lemma kap_tri (z w u : P) : kap z w * kap w u ≤ 4 * kap z u := by
  unfold kap; split_ifs with h1 h2 h13
  · have hkey : w.1.im ^ 2 * ‖z.1 - conj u.1‖ ^ 2 ≤ ‖z.1 - conj w.1‖ ^ 2 * ‖w.1 - conj u.1‖ ^ 2 := by
      have hp : 0 ≤ z.1.im ^ 2 + 2 * z.1.im * w.1.im := by nlinarith [sq_nonneg z.1.im]
      have hq : 0 ≤ u.1.im ^ 2 + 2 * w.1.im * u.1.im := by nlinarith [sq_nonneg u.1.im]
      rw [nsq_sub_conj, nsq_sub_conj, nsq_sub_conj]
      nlinarith [sq_nonneg ((z.1.re - w.1.re) * (w.1.re - u.1.re) - w.1.im ^ 2),
        mul_nonneg (sq_nonneg (z.1.re - w.1.re)) hq, mul_nonneg (sq_nonneg (w.1.re - u.1.re)) hp,
        mul_nonneg (sq_nonneg w.1.im) h1.le, mul_nonneg (sq_nonneg w.1.im) h2.le,
        mul_nonneg (sq_nonneg w.1.im) h13.le, mul_nonneg h13.le h1.le, mul_nonneg h13.le h2.le,
        sq_nonneg (z.1.im * u.1.im)]
    rw [div_mul_div_comm, mul_div_assoc', le_div_iff₀ (pos_den_conj h13), div_mul_eq_mul_div,
      div_le_iff₀ (mul_pos (pos_den_conj h1) (pos_den_conj h2))]
    nlinarith [mul_le_mul_of_nonneg_left hkey h13.le]
  · exfalso; have hc := not_lt.1 h13
    nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.2 hc) (sq_nonneg w.1.im)]
  all_goals simp; try positivity

lemma kap_im_le (z w : P) : kap z w * |w.1.im| ≤ 4 * |z.1.im| := by
  unfold kap; split_ifs with h
  · rw [div_mul_eq_mul_div, div_le_iff₀ (pos_den_conj h), nsq_sub_conj]
    rcases lt_or_gt_of_ne w.2 with hw | hw
    · have hz : z.1.im < 0 := by nlinarith
      rw [abs_of_neg hw, abs_of_neg hz]
      nlinarith [mul_nonneg (neg_nonneg.2 hz.le) (sq_nonneg (z.1.re - w.1.re)),
        mul_nonneg (neg_nonneg.2 hz.le) (sq_nonneg z.1.im), mul_nonneg (sq_nonneg z.1.im) (neg_nonneg.2 hw.le)]
    · have hz : 0 < z.1.im := by nlinarith
      rw [abs_of_pos hw, abs_of_pos hz]
      nlinarith [mul_nonneg hz.le (sq_nonneg (z.1.re - w.1.re)),
        mul_nonneg hz.le (sq_nonneg z.1.im), mul_nonneg (sq_nonneg z.1.im) hw.le]
  · rw [zero_mul]; positivity

lemma cont_kap : Continuous fun p : P × P => kap p.1 p.2 := by
  unfold kap
  refine continuous_if (fun a ha => (clopen_pos_im.frontier_eq ▸ ha).elim) ?_ continuousOn_const
  rw [clopen_pos_im.1.closure_eq]
  exact (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop))
    fun p hp => (pos_den_conj hp).ne'

lemma trans_iP (z : P) : ∃ g : GL2 ℝ, g 1 0 = 0 ∧ g 1 1 = 1 ∧ g • iP = z := by
  have hd : (!![z.1.im, z.1.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [det_fin_two_of]; simpa using z.2
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, rfl, rfl, Subtype.ext ?_⟩
  change num (GeneralLinearGroup.mkOfDetNeZero _ hd) I / den (GeneralLinearGroup.mkOfDetNeZero _ hd) I = z.1
  apply Complex.ext <;> simp [num, den]

theorem hyperbolic_kappa_properties_proof : B1c :=
  ⟨fun z w => ⟨kap_nonneg z w, kap_le_one z w, kap_symm z w⟩, kap_self, kap_tri, kap_im_le, cont_kap, trans_iP⟩

-- === E0a: Actions preserve measures & small-ball volume lower bound ===

lemma count_pres {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] (f : α → α)
    (hf : Bijective f) : MeasurePreserving f Measure.count Measure.count := by
  refine ⟨measurable_of_countable f, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_of_countable f) hs, Measure.count_apply hs,
    Measure.count_apply (to_countable _).measurableSet]
  exact congrArg _ $ encard_preimage_of_injective_subset_range hf.1 (hf.2.range_eq ▸ subset_univ s)

theorem actions_preserve_measures_proof : B1a → B1b → B1c → E0a := by
  intro _ _ _ F I Gf _ _ _ D ax
  have : SigmaFinite (volume : Measure P) := half_plane_measure_invariant_proof.1
  have : (volume : Measure P).IsOpenPosMeasure := half_plane_measure_invariant_proof.2.1
  have : Countable F := ax.cF
  have hPG : Countable (PG F) :=
    letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
    letI : Countable (GL2 F) := Injective.countable (f := fun g : GL2 F => (g : Matrix (Fin 2) (Fin 2) F)) fun _ _ h => Units.ext h
    QuotientGroup.mk_surjective.countable
  have : Countable D.Om := ax.cO; have : Countable D.Cj := hPG
  have : SigmaFinite (volume : Measure D.Xs) := inferInstanceAs (SigmaFinite (Measure.pi fun _ : I => (volume : Measure P)))
  have presX (γ : PG F) : MeasurePreserving (fun z : D.Xs => γ • z) volume volume := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    exact measurePreserving_pi _ _ fun v => mp_smul_P (D.r v g)
  have contX (γ : PG F) : Continuous fun z : D.Xs => γ • z := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    exact continuous_pi fun v => (cont_smul_P (D.r v g)).comp (continuous_apply v)
  refine ⟨hPG, this, presX,
    fun γ => (count_pres (γ • ·) (MulAction.bijective γ)).prod (presX γ),
    fun γ => (count_pres (γ • ·) (MulAction.bijective γ)).prod (presX γ),
    contX, inferInstanceAs (BorelSpace (I → P)), fun δ hδ => ?_⟩
  have hk1 (z : P) : Continuous (kap z) := cont_kap.comp (continuous_const.prodMk continuous_id)
  have hUp : 0 < volume {w : P | δ < kap iP w} :=
    (isOpen_lt continuous_const (hk1 iP)).measure_pos volume ⟨iP, by simpa [kap_self] using hδ⟩
  obtain ⟨c0, hc0, hc0U⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hUp
  have hS (z : P) : MeasurableSet {w | δ ≤ kap z w} := measurableSet_le measurable_const (hk1 z).measurable
  have hball (z : P) : (c0 : ℝ≥0∞) ≤ volume {w | δ ≤ kap z w} := by
    obtain ⟨g, -, -, rfl⟩ := trans_iP z
    rw [← (mp_smul_P g).measure_preimage (hS _).nullMeasurableSet,
      show (g • ·) ⁻¹' {w | δ ≤ kap (g • iP) w} = {w | δ ≤ kap iP w} from Set.ext fun w => by simp [kap_smul]]
    exact hc0U.le.trans $ measure_mono fun _ (h : δ < kap iP _) => show δ ≤ kap iP _ from h.le
  refine ⟨c0 ^ Fintype.card I, pow_pos (by exact_mod_cast hc0) _, fun z => ?_⟩
  rw [show {w : X I | Near δ z w} = univ.pi fun v => {w | δ ≤ kap (z v) w} from Set.ext fun w => by simp [Near]]
  refine ⟨MeasurableSet.univ_pi fun v => hS (z v), ?_⟩
  rw [volume_pi, Measure.pi_pi, ENNReal.coe_pow, ← card_univ, ← prod_const]
  exact Finset.prod_le_prod fun v _ => hball (z v)

-- === Pack & Mult ===

lemma kap_smulX {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (δ : PG F) (a b : D.Xs) (v : I) :
    kap ((δ • a : D.Xs) v) ((δ • b : D.Xs) v) = kap (a v) (b v) := by
  induction δ using QuotientGroup.induction_on with
  | H g => exact kap_smul (D.r v g) (a v) (b v)

theorem pf_Pack : B1b → B1c → E0a → Pack := by
  intro _ _ hE F I Gf _ _ _ D hax
  obtain ⟨hcnt, -, -, -, -, -, -, hnear⟩ := hE F I Gf D hax
  obtain ⟨c, hc0, hcz⟩ := hnear (1 / 2) (by norm_num)
  refine ⟨c⁻¹, fun y ω' h A hh hA hfin => ?_⟩
  set S0 : Set (PG F) := {γ | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}
  set N : ℝ≥0∞ := (S0.ncard : ℝ≥0∞)
  let Γ := {γ : PG F // γ • y.1 = ω'}
  let Sg (γ : Γ) : Set D.Xs := {w | Near (1 / 2) (γ.1 • y.2 : D.Xs) w}
  have hSm (γ : Γ) : MeasurableSet (Sg γ) := (hcz (γ.1 • y.2)).1
  have hone (γ : Γ) : (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ A * ∫⁻ w, (Sg γ).indicator h w := by
    calc (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ h (γ.1 • y.2) * volume (Sg γ) := by rw [mul_comm]; gcongr; exact (hcz _).2
      _ = ∫⁻ _ in Sg γ, h (γ.1 • y.2) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in Sg γ, (A : ℝ≥0∞) * h w := setLIntegral_mono' (hSm γ) fun w hw => hA _ _ hw
      _ = A * ∫⁻ w, (Sg γ).indicator h w := by rw [lintegral_const_mul _ hh, lintegral_indicator (hSm γ)]
  have hcnt_w (w : D.Xs) : ∑' γ : Γ, (Sg γ).indicator h w ≤ N * h w := by
    by_cases hT : ∃ γ₁ : Γ, w ∈ Sg γ₁
    · obtain ⟨γ₁, hγ₁⟩ := hT
      have finj : Injective (fun γ : Γ => γ₁.1⁻¹ * γ.1) := fun _ _ h => Subtype.ext (mul_left_cancel h)
      refine (ENNReal.tsum_le_tsum fun γ => ?_).trans ((ENNReal.tsum_comp_le_tsum_of_injective finj (S0.indicator fun _ => h w)).trans ?_)
      · by_cases hw : w ∈ Sg γ
        · have hmem : γ₁.1⁻¹ * γ.1 ∈ S0 := ⟨by rw [mul_smul, γ.2, inv_smul_eq_iff]; exact γ₁.2.symm, fun v => by
            have e : kap (y.2 v) (((γ₁.1⁻¹ * γ.1) • y.2 : D.Xs) v) = kap ((γ₁.1 • y.2 : D.Xs) v) ((γ.1 • y.2 : D.Xs) v) := by
              rw [← kap_smulX D γ₁.1 y.2 ((γ₁.1⁻¹ * γ.1) • y.2) v, smul_smul, mul_inv_cancel_left]
            rw [e]; have := kap_tri ((γ₁.1 • y.2 : D.Xs) v) (w v) ((γ.1 • y.2 : D.Xs) v)
            rw [kap_symm (w v)] at this; nlinarith [hγ₁ v, hw v]⟩
          simp [indicator_of_mem hw, indicator_of_mem hmem]
        · rw [indicator_of_notMem hw]; exact bot_le
      · rw [← tsum_subtype S0 fun _ => h w]
        have := hfin.fintype
        rw [tsum_fintype, sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]; simp only [N, Set.ncard_def]; exact le_rfl
    · simp only [not_exists] at hT; have h0 : ∀ γ, (Sg γ).indicator h w = 0 := fun γ => indicator_of_notMem (hT γ) h; simp [h0]
  have hkey : (c : ℝ≥0∞) * ∑' γ : Γ, h (γ.1 • y.2) ≤ A * (N * ∫⁻ w, h w) := by
    rw [← ENNReal.tsum_mul_left]
    calc _ ≤ ∑' γ, (A : ℝ≥0∞) * ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_le_tsum hone
      _ = A * ∫⁻ w, ∑' γ, (Sg γ).indicator h w := by rw [ENNReal.tsum_mul_left, lintegral_tsum fun γ => (hh.indicator (hSm γ)).aemeasurable]
      _ ≤ A * (N * ∫⁻ w, h w) := by rw [← lintegral_const_mul _ hh]; gcongr; exact hcnt_w _
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  calc ∑' γ : Γ, h (γ.1 • y.2) = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∑' γ : Γ, h (γ.1 • y.2)) :=
        (ENNReal.inv_mul_cancel_left hc' ENNReal.coe_ne_top).symm
    _ ≤ (c : ℝ≥0∞)⁻¹ * (A * (N * ∫⁻ w, h w)) := by gcongr
    _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * A * N * ∫⁻ w, h w := by rw [ENNReal.coe_inv hc0.ne']; ring

theorem pf_Mult : B1b → E0d → Mult := by
  intro _ hE F I Gf _ _ _ D hD δ c₀ hδ hc₀
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h10, -⟩ := hE F I Gf D hD
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  let A (y : D.Y) : Set (PG F) := {γ | γ • y.1 = y.1 ∧ Near δ y.2 (γ • y.2 : D.Xs)}
  have hconj (g : PG F) (y : D.Y) : (A (g • y)).Finite ↔ (A y).Finite ∧ (A (g • y)).ncard = (A y).ncard := by
    have hinj : Injective (fun γ : PG F => g * γ * g⁻¹) := fun _ _ h => by simpa using h
    have hmem (γ : PG F) : g * γ * g⁻¹ ∈ A (g • y) ↔ γ ∈ A y := by
      simp [A, Near, mul_smul, inv_smul_smul, kap_smulX]
    have hA : A (g • y) = (fun γ => g * γ * g⁻¹) '' A y := Set.ext fun γ' =>
      ⟨fun h => ⟨g⁻¹ * γ' * g, (hmem _).1 (by rwa [show g * (g⁻¹ * γ' * g) * g⁻¹ = γ' by group]), by group⟩,
       fun ⟨γ, hγ, h⟩ => h ▸ (hmem γ).2 hγ⟩
    rw [hA, finite_image_iff hinj.injOn, ncard_image_of_injective _ hinj]
    exact ⟨fun h => ⟨h, rfl⟩, a1⟩
  choose C' hC' using fun x' : Gf => hD.count (x' : Gf ⧸ D.H) δ C c hδ hc
  have hapos x : 0 < D.hf ![0, 1] (D.rep (x : Gf ⧸ D.H)) := hD.pos _ e01_ne _
  refine ⟨∑ x ∈ S, max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep (x : Gf ⧸ D.H))), fun y s hs hy => ?_⟩
  obtain ⟨γ₀, hγ₀⟩ := h10 s hs
  have e1 : D.HtY ![0, 1] ((γ₀ : PG F) • y) = D.HtY s y := by rw [h2 _ e01_ne γ₀ y, hγ₀]
  obtain ⟨b, hb10, ⟨x', hx'S, h, hh, hbx⟩, hsg⟩ := hnorm _ _ (e1.symm ▸ hy)
  have hb11 : b.val 1 1 ≠ 0 := fun h0 => b.det_ne_zero $ by rw [det_fin_two]; simp [h0, hb10]
  have hvb : ![0, 1] ᵥ* b.val = b.val 1 1 • ![(0 : F), 1] := funext fun i => by fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two, hb10]
  have hy'' : (b : PG F) • ((γ₀ : PG F) • y) = ((((x' : Gf ⧸ D.H) : D.Om), D.act b ((γ₀ : PG F) • y).2) : D.Y) := by
    refine Prod.ext ?_ (D.mk_smulX b _)
    change (b : PG F) • ((γ₀ : PG F) • y).1 = ((x' : Gf ⧸ D.H) : D.Om)
    have : (b : PG F) • ((γ₀ : PG F) • y).1 = ((D.j b * D.rep ((γ₀ : PG F) • y).1 : Gf) : Gf ⧸ D.H) := by
      conv_lhs => rw [← QuotientGroup.out_eq' ((γ₀ : PG F) • y).1]
      exact D.mk_smulO b _
    rw [this, hbx]; exact QuotientGroup.eq.2 (by simpa using hh)
  have ⟨hfin, hle⟩ := hC' x' _ hsg
  have hfin1 := ((hconj (b : PG F) ((γ₀ : PG F) • y)).1 (hy'' ▸ hfin))
  have hfin0 := ((hconj (γ₀ : PG F) y).1 hfin1.1)
  refine ⟨hfin0.1, ?_⟩
  have hHt : (∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) * D.hf ![0, 1] (D.rep (x' : Gf ⧸ D.H)) = D.HtY s y := by
    have h1 : D.HtY ![0, 1] ((((x' : Gf ⧸ D.H) : D.Om), D.act b ((γ₀ : PG F) • y).2) : D.Y) =
        (∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) * D.hf ![0, 1] (D.rep (x' : Gf ⧸ D.H)) := by simp [Dat.HtY, Dat.Ht]
    rw [← h1, ← hy'', h2 _ e01_ne b _, hvb, h3 _ e01_ne _ hb11, e1]
  have hP0 : 0 ≤ ∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im| := Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hK := single_le_sum (f := fun x => max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep (x : Gf ⧸ D.H))))
    (fun x _ => mul_nonneg (le_max_right _ _) (add_nonneg zero_le_one (div_nonneg zero_le_one (hapos x).le))) hx'S
  have ha := hapos x'
  have h1P : 1 + ∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im| ≤ (1 + 1 / D.hf ![0, 1] (D.rep (x' : Gf ⧸ D.H))) * (1 + D.HtY s y) := by
    rw [eq_div_of_mul_eq ha.ne' hHt]; have : 0 ≤ 1 / D.hf ![0, 1] (D.rep (x' : Gf ⧸ D.H)) := by positivity
    nlinarith [show (1 + 1 / D.hf ![0, 1] (D.rep (x' : Gf ⧸ D.H))) * (1 + D.HtY s y) - (1 + D.HtY s y / D.hf ![0, 1] (D.rep (x' : Gf ⧸ D.H))) = D.HtY s y + 1 / D.hf ![0, 1] (D.rep (x' : Gf ⧸ D.H)) by ring]
  change ((A y).ncard : ℝ) ≤ _
  rw [← hfin0.2, ← hfin1.2, hy'']
  have hM0 : 0 ≤ max (C' x') 0 := le_max_right _ _
  have hle' : ((A ((((x' : Gf ⧸ D.H) : D.Om), D.act b ((γ₀ : PG F) • y).2) : D.Y)).ncard : ℝ) ≤
      max (C' x') 0 * (1 + ∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) :=
    hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  nlinarith [mul_le_mul_of_nonneg_left h1P hM0, mul_le_mul_of_nonneg_right hK (by linarith : 0 ≤ 1 + D.HtY s y)]

-- === UpperHalfPlaneMeasureCoordinates ===

lemma pt_cont : Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) :=
  Continuous.subtype_mk (by fun_prop) _

lemma pt_bij : Bijective (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) :=
  ⟨fun ⟨x, y, hy⟩ ⟨x', y', hy'⟩ h => by
    have h' : (y : ℂ) * (x + I) = (y' : ℂ) * (x' + I) := congrArg Subtype.val h
    have him := congrArg im h'; have hre := congrArg re h'; simp at him hre; subst him
    have := mul_left_cancel₀ hy hre; subst this; rfl,
   fun ⟨z, hz⟩ => ⟨(z.re / z.im, ⟨z.im, hz⟩), Subtype.ext $ Complex.ext (by simp [pt]; field_simp) (by simp [pt])⟩⟩

lemma lint_comap {α : Type} [MeasurableSpace α] {p : α → Prop} (hp : MeasurableSet {a | p a}) (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x : {a // p a}, f x.1 ∂(Measure.comap Subtype.val μ) = ∫⁻ x in {a | p a}, f x ∂μ :=
  lintegral_subtype_comap hp f

lemma sf_nz : SigmaFinite (Measure.comap (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) volume) := by
  have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have hm := (MeasurableEmbedding.subtype_coe hY).map_comap (μ := (volume : Measure ℝ))
  exact SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by convert (inferInstance : SigmaFinite ((volume : Measure ℝ).restrict (range (Subtype.val : {y : ℝ // y ≠ 0} → ℝ)))); exact hm)

lemma pt_mp : MeasurePreserving (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2)
    ((volume : Measure ℝ).prod ((Measure.comap Subtype.val volume).withDensity fun y => oR (1 / |y.1|))) volume := by
  let Ψ (x y : ℝ) : ℂ := (y : ℂ) * (x + I)
  have hS := isOpen_U.measurableSet; have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have hemb := MeasurableEmbedding.subtype_coe hS
  have := sf_nz
  refine ⟨pt_cont.measurable, Measure.ext fun s hs => ?_⟩
  let G : ℂ → ℝ≥0∞ := (Subtype.val '' s).indicator 1
  have hGm : Measurable G := measurable_one.indicator (hemb.measurableSet_image.2 hs)
  have hGv (z : P) : G z.1 = s.indicator 1 z := by
    have hz : z.1 ∈ Subtype.val '' s ↔ z ∈ s := ⟨fun ⟨_, hw, e⟩ => Subtype.ext e ▸ hw, fun h => ⟨z, h, rfl⟩⟩
    by_cases h : z ∈ s <;> simp [G, indicator, hz, h]
  rw [Measure.map_apply pt_cont.measurable hs, ← lintegral_indicator_one (pt_cont.measurable hs),
    show ((fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) ⁻¹' s).indicator 1 = fun p => G (Ψ p.1 p.2.1) from
      funext fun p => (hGv (pt p.1 p.2.1 p.2.2)).symm,
    lintegral_prod (fun p : ℝ × {y : ℝ // y ≠ 0} => G (Ψ p.1 p.2.1))
      (hGm.comp (by fun_prop : Continuous fun p : ℝ × {y : ℝ // y ≠ 0} => Ψ p.1 p.2.1).measurable).aemeasurable]
  have e2 x : ∫⁻ y, G (Ψ x y.1) ∂((Measure.comap Subtype.val volume).withDensity fun y : {y : ℝ // y ≠ 0} => oR (1 / |y.1|))
      = ∫⁻ y, oR (1 / |y|) * G (Ψ x y) := by
    have hf : Measurable fun y : {y : ℝ // y ≠ 0} => G (Ψ x y.1) := hGm.comp (by fun_prop)
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
    simpa only [Pi.mul_apply, show ({y : ℝ | y ≠ 0} : Set ℝ) = {0}ᶜ from rfl, restrict_compl_singleton] using
      lint_comap hY (volume : Measure ℝ) (fun y => oR (1 / |y|) * G (Ψ x y))
  simp_rw [e2]
  have hkey : ∫⁻ x, ∫⁻ y, oR (1 / |y|) * G (Ψ x y) = ∫⁻ z, oR (1 / z.im ^ 2) * G z := by
    rw [lintegral_lintegral_swap ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hGm.comp (by fun_prop : Continuous fun p : ℝ × ℝ => Ψ p.1 p.2).measurable)).aemeasurable]
    have hR : ∫⁻ z, oR (1 / z.im ^ 2) * G z = ∫⁻ y : ℝ, ∫⁻ u : ℝ, oR (1 / y ^ 2) * G ((u : ℂ) + y * I) := by
      have hmg : Measurable fun p : ℝ × ℝ => oR (1 / (measurableEquivRealProd.symm p).im ^ 2) * G (measurableEquivRealProd.symm p) :=
        ((ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun z : ℂ => 1 / z.im ^ 2)).mul hGm).comp (MeasurableEquiv.measurable _)
      rw [← Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
        Measure.volume_eq_prod, lintegral_prod_symm _ hmg.aemeasurable]
      congr 1; funext y; congr 1; funext u; simp only [Complex.measurableEquivRealProd]; congr 2; exact mk_eq_add_mul_I u y
    rw [hR]; congr 1; funext y
    have hmx : Measurable fun x : ℝ => G (Ψ x y) := hGm.comp (by fun_prop)
    have hmu : Measurable (fun u : ℝ => G ((u : ℂ) + y * I)) := hGm.comp (by fun_prop : Continuous fun u : ℝ => (u : ℂ) + y * I).measurable
    rw [lintegral_const_mul _ hmx, lintegral_const_mul _ hmu]
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hsc : ∫⁻ x, G (Ψ x y) = oR |y⁻¹| * ∫⁻ u : ℝ, G ((u : ℂ) + y * I) := by
        calc _ = ∫⁻ x : ℝ, G (((y * x : ℝ) : ℂ) + y * I) := by congr 1; funext x; congr 1; simp [Ψ]; ring
          _ = ∫⁻ u : ℝ, G ((u : ℂ) + y * I) ∂(Measure.map (y * ·) volume) := (lintegral_map hmu (measurable_const_mul y)).symm
          _ = _ := by rw [Real.map_volume_mul_left hy, lintegral_smul_measure, smul_eq_mul]
      rw [hsc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        show 1 / |y| * |y⁻¹| = 1 / y ^ 2 by rw [abs_inv, one_div, one_div, ← mul_inv, ← sq, sq_abs]]
  rw [hkey]
  let s' : Set {z : ℂ // z.im ≠ 0} := s
  have hs' : MeasurableSet s' := hs
  change _ = (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).withDensity (fun z => oR (1 / z.1.im ^ 2)) s'
  rw [withDensity_apply _ hs', ← lintegral_indicator hs',
    show s'.indicator (fun z : {z : ℂ // z.im ≠ 0} => oR (1 / z.1.im ^ 2)) = fun z => oR (1 / z.1.im ^ 2) * G z.1 from
      funext fun z => by
        rw [hGv z, show s.indicator (1 : P → ℝ≥0∞) z = s'.indicator (fun _ => 1) z from rfl]
        by_cases h : z ∈ s' <;> simp [indicator, h],
    lint_comap hS (volume : Measure ℂ) (fun z => oR (1 / z.im ^ 2) * G z), ← lintegral_indicator hS]
  congr 1; funext z; by_cases h : z.im ≠ 0
  · simp [indicator, h]
  · simp [indicator, h, G, show z ∉ Subtype.val '' s from fun ⟨w, _, hw⟩ => h (hw ▸ w.2)]

theorem upper_half_plane_measure_coordinates : UpperHalfPlaneMeasureCoordinates := ⟨pt_mp, pt_bij, pt_cont⟩

-- === B6: Hyperbolic ball volume / kernel L¹ integrability ===

theorem hyperbolic_ball_volume_proof : B1a → B1b → B1c → UpperHalfPlaneMeasureCoordinates → B6 := by
  intro _ _ _ _ k hk
  let F (y : ℝ) := (1 + y ^ (-(1 / 2 : ℝ))) / (1 + y) ^ 2
  have hFint : IntegrableOn F (Ioi 0) := by
    have hm : Measurable F := by unfold F; fun_prop
    have h1 : IntegrableOn F (Ioo 0 2) :=
      ((integrableOn_const (C := (1 : ℝ)) (hs := by simp)).add
        ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(1 / 2 : ℝ)) (by norm_num)).2 (by norm_num))).mono'
        hm.aestronglyMeasurable $ (ae_restrict_iff' measurableSet_Ioo).2 $ Eventually.of_forall fun y hy => by
          have hy0 : 0 < y := hy.1; have := rpow_nonneg hy0.le (-(1 / 2 : ℝ))
          rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity)]; unfold F
          dsimp only [Pi.add_apply]; rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg y]
    have h2 : IntegrableOn F (Ioi 1) :=
      ((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) one_pos).const_mul 2).mono'
        hm.aestronglyMeasurable $ (ae_restrict_iff' measurableSet_Ioi).2 $ Eventually.of_forall fun y (hy : 1 < y) => by
          have hy0 : 0 < y := by linarith
          have hp := rpow_le_one_of_one_le_of_nonpos hy.le (z := -(1 / 2 : ℝ)) (by norm_num)
          have hp0 := rpow_nonneg hy0.le (-(1 / 2 : ℝ))
          rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity),
            show y ^ (-2 : ℝ) = 1 / y ^ 2 by rw [rpow_neg hy0.le, one_div]; norm_cast]
          unfold F; rw [div_le_iff₀ (by positivity)]
          have : 2 ≤ 2 * (1 / y ^ 2) * (1 + y) ^ 2 := by rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
          linarith
    exact (h1.union h2).mono_set fun y hy => if h : y < 2 then Or.inl ⟨hy, h⟩ else Or.inr (show 1 < y by linarith [show (0 : ℝ) < y from hy])
  let A : ℝ≥0∞ := ∫⁻ x : ℝ, oR ((1 + x ^ 2)⁻¹)
  let H (w : P) : ℝ≥0∞ := oR (kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))))
  let B (y : ℝ) : ℝ≥0∞ := if 0 < y then oR (16 * y ^ 2 / (1 + y) ^ 2 * (1 + y ^ (-(1 / 2 : ℝ)))) * (oR y⁻¹ * A) else 0
  have hHm : Measurable H := ENNReal.measurable_ofReal.comp
    (((cont_kap.comp (continuous_const.prodMk continuous_id)).measurable.pow_const 2).mul
      (measurable_const.add ((continuous_im.comp continuous_subtype_val).abs.measurable.pow_const _)))
  have hfin : ∫⁻ w, H w < ∞ := by
    have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
    have := sf_nz
    rw [← pt_mp.lintegral_comp hHm,
      lintegral_prod_symm (fun p : ℝ × {y : ℝ // y ≠ 0} => H (pt p.1 p.2.1 p.2.2)) (hHm.comp pt_cont.measurable).aemeasurable]
    have hinner (y : ℝ) (hy : y ≠ 0) : ∫⁻ x : ℝ, H (pt x y hy) ≤ B y := by
      rcases lt_or_gt_of_ne hy with hn | hp
      · simp [H, kap, iP, pt, not_lt.2 hn.le]
      · have hx : ∫⁻ x : ℝ, oR ((1 + (y * x) ^ 2)⁻¹) = oR y⁻¹ * A := by
          rw [← lintegral_map (by fun_prop : Measurable fun x : ℝ => oR ((1 + x ^ 2)⁻¹)) (measurable_const_mul y),
            Real.map_volume_mul_left hp.ne', lintegral_smul_measure, smul_eq_mul, abs_of_pos (inv_pos.2 hp)]
        dsimp only [B]; rw [ite_eq_left hp, ← hx, ← lintegral_const_mul _ (by fun_prop)]
        refine lintegral_mono fun x => by
          dsimp only [H]; rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hkap : kap iP (pt x y hp.ne') = 4 * y / ((y * x) ^ 2 + (1 + y) ^ 2) := by
            rw [kap, ite_eq_left (by simp [iP, pt, hp]), nsq_sub_conj]; simp [iP, pt]
          have hsq : kap iP (pt x y hp.ne') ^ 2 ≤ 16 * y ^ 2 / (1 + y) ^ 2 * (1 + (y * x) ^ 2)⁻¹ := by
            rw [hkap, show 16 * y ^ 2 / (1 + y) ^ 2 * (1 + (y * x) ^ 2)⁻¹ = (4 * y) ^ 2 / ((1 + (y * x) ^ 2) * (1 + y) ^ 2) by field_simp; ring, div_pow]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) $ by
              nlinarith [sq_nonneg ((y * x) ^ 2), mul_nonneg (sq_nonneg (y * x)) (sq_nonneg (1 + y)),
                mul_nonneg (sq_nonneg (1 + y)) (show (0 : ℝ) ≤ (1 + y) ^ 2 - 1 by nlinarith)]
          have : |(pt x y hp.ne').1.im| = y := by simp [pt, abs_of_pos hp]
          rw [this]; have := rpow_nonneg hp.le (-(1 / 2 : ℝ))
          calc _ ≤ 16 * y ^ 2 / (1 + y) ^ 2 * (1 + (y * x) ^ 2)⁻¹ * (1 + y ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_right hsq (by positivity)
            _ = _ := by ring
    calc _ ≤ ∫⁻ y : {y : ℝ // y ≠ 0}, B y.1 ∂((Measure.comap Subtype.val volume).withDensity fun y => oR (1 / |y.1|)) :=
          lintegral_mono fun y => hinner y.1 y.2
      _ = ∫⁻ y in {y : ℝ | y ≠ 0}, oR (1 / |y|) * B y := by
          have hBm : Measurable fun y : {y : ℝ // y ≠ 0} => B y.1 :=
            (Measurable.ite measurableSet_Ioi (by fun_prop : Measurable fun y : ℝ => oR (16 * y ^ 2 / (1 + y) ^ 2 * (1 + y ^ (-(1 / 2 : ℝ)))) * (oR y⁻¹ * A)) measurable_const).comp measurable_subtype_coe
          rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hBm]
          exact lint_comap hY (volume : Measure ℝ) (fun y => oR (1 / |y|) * B y)
      _ ≤ ∫⁻ y, (Set.Ioi (0 : ℝ)).indicator (fun y => oR (16 * F y) * A) y := (setLIntegral_le_lintegral _ _).trans $ lintegral_mono fun y => by
          by_cases hy : 0 < y
          · rw [indicator_of_mem (show y ∈ Set.Ioi (0 : ℝ) from hy)]; dsimp only [B]
            rw [ite_eq_left hy, abs_of_pos hy, ← mul_assoc, ← mul_assoc,
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            exact le_of_eq $ congrArg (· * A) $ congrArg oR $ by unfold F; field_simp
          · simp [B, hy]
      _ = (∫⁻ y in Ioi (0 : ℝ), oR (16 * F y)) * A := by rw [lintegral_indicator measurableSet_Ioi, lintegral_mul_const _ (by unfold F; fun_prop)]
      _ < ∞ := ENNReal.mul_lt_top (hFint.const_mul 16).lintegral_lt_top integrable_inv_one_add_sq.lintegral_lt_top
  have hrp {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t ^ ((k : ℝ) / 2) ≤ t ^ 2 := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) / 2 := by have : (4 : ℝ) ≤ k := (by exact_mod_cast hk); linarith
    rcases h0.eq_or_lt with rfl | ht
    · rw [zero_rpow (by linarith)]; positivity
    · simpa using rpow_le_rpow_of_exponent_ge ht h1 hk2
  refine ⟨(∫⁻ w, H w).toNNReal, fun z => ?_⟩
  rw [ENNReal.coe_toNNReal hfin.ne]
  obtain ⟨g, hg0, hg1, rfl⟩ := trans_iP z
  have him (w : P) : (g • w).1.im = g.val.det * w.1.im := by
    rw [im_smul, show den g w.1 = 1 by simp [den, hg0, hg1], normSq_one, div_one]
  have hkc (u : P) : Continuous (kap u) := cont_kap.comp (continuous_const.prodMk continuous_id)
  have hima : Measurable fun w : P => |w.1.im| := (continuous_im.comp continuous_subtype_val).abs.measurable
  refine ⟨?_, ?_⟩
  · rw [← (mp_smul_P g).lintegral_comp (f := fun w : P => oR (kap (g • iP) w ^ ((k : ℝ) / 2)))
      (ENNReal.measurable_ofReal.comp ((hkc _).measurable.pow_const _))]
    refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
    rw [kap_smul]
    exact (hrp (kap_nonneg iP w) (kap_le_one iP w)).trans $
      le_mul_of_one_le_right (sq_nonneg _) (by linarith [rpow_nonneg (abs_nonneg w.1.im) (-(1 / 2 : ℝ))])
  · rw [← (mp_smul_P g).lintegral_comp (f := fun w : P => oR (kap (g • iP) w ^ ((k : ℝ) / 2) * (|(g • iP).1.im| / |w.1.im|) ^ ((1 : ℝ) / 2)))
      (ENNReal.measurable_ofReal.comp (((hkc _).measurable.pow_const _).mul ((measurable_const.div hima).pow_const _)))]
    refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
    rw [kap_smul, him, him, show |g.val.det * iP.1.im| / |g.val.det * w.1.im| = |w.1.im|⁻¹ by
        rw [show iP.1.im = 1 by simp [iP], mul_one, abs_mul, div_mul_eq_div_div, div_self (abs_ne_zero.2 g.det_ne_zero), one_div],
      inv_rpow (abs_nonneg _), ← rpow_neg (abs_nonneg _)]
    have hp0 := rpow_nonneg (abs_nonneg w.1.im) (-(1 / 2 : ℝ))
    exact (mul_le_mul_of_nonneg_right (hrp (kap_nonneg iP w) (kap_le_one iP w)) hp0).trans $
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

end UpperTheory.Esk
