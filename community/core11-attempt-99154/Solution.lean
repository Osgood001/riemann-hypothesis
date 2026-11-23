import Mathlib

noncomputable section

open Complex Metric MeasureTheory Filter Topology Module Finset
open LinearMap hiding fst snd proj
open Submodule hiding fst snd
open Set hiding range
open ContinuousLinearMap hiding det
open LinearMap (det)
open scoped Real

namespace Core11

abbrev Cn n := Fin n → ℂ
abbrev Cube n := Icc (0 : Fin n → ℝ) (fun _ => 2 * π)
abbrev CB n := C(Cube n, ℂ)
abbrev tmap {n} (c : Cn n) (r : ℝ) := torusMap c fun _ => r
abbrev pj {n} (i : Fin n) : Cn n →L[ℂ] ℂ := proj (R := ℂ) (φ := fun _ => ℂ) i

instance {n} : CompactSpace (Cube n) := isCompact_iff_compactSpace.mp isCompact_Icc

lemma norm_tmap {n} (c : Cn n) {r : ℝ} (hr : 0 ≤ r) θ i : ‖tmap c r θ i - c i‖ = r := by
  simp [torusMap, norm_exp_ofReal_mul_I, abs_of_nonneg hr]

lemma tmap_mem {n} (c : Cn n) {r : ℝ} (hr : 0 ≤ r) θ : tmap c r θ ∈ closedBall c r :=
  mem_closedBall.2 $ (dist_pi_le_iff hr).2 fun i => by
    rw [dist_eq_norm, norm_tmap c hr]

lemma tmap_sub_ne {n} {c z : Cn n} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r) θ i :
    tmap c r θ i - z i ≠ 0 := fun h => by
  have := (dist_le_pi_dist z c i).trans_lt $ mem_ball.1 hz
  rw [dist_eq_norm, ← sub_eq_zero.1 h, norm_tmap c hr.le] at this
  exact this.false

lemma cont_tmap {n} (c : Cn n) (r : ℝ) : Continuous (tmap c r) :=
  continuous_pi fun _ => by
    unfold tmap torusMap
    fun_prop

lemma cauchy_polydisc : ∀ {n} (f : Cn n → ℂ) (c : Cn n) {r : ℝ}, 0 < r →
    (∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z
  | 0, f, c, _, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, f, c, r, hr, hf, z, hz => by
    rw [torusIntegral_succ $ ((continuous_finsetProd _ fun i _ => (((continuous_apply i).comp $ cont_tmap c r).sub
      continuous_const).inv₀ fun θ => tmap_sub_ne hr hz θ i).mul $ continuous_iff_continuousAt.2 fun θ =>
        (hf _ $ tmap_mem c hr.le θ).continuousAt.comp (cont_tmap c r).continuousAt).continuousOn.integrableOn_compact isCompact_Icc]
    have hz' : z ∘ Fin.succ ∈ ball (c ∘ Fin.succ) r :=
      mem_ball.2 $ (dist_pi_lt_iff hr).2 fun i => (dist_le_pi_dist z c i.succ).trans_lt $ mem_ball.1 hz
    have hcons {x y} (hx : x ∈ closedBall (c 0) r) (hy : y ∈ closedBall (c ∘ Fin.succ) r) :
        (Fin.cons x y : Cn (n + 1)) ∈ closedBall c r :=
      mem_closedBall.2 $ (dist_pi_le_iff hr.le).2 $
        Fin.cases (mem_closedBall.1 hx) fun j => (dist_le_pi_dist y (c ∘ Fin.succ) j).trans $ mem_closedBall.1 hy
    rw [circleIntegral.integral_congr hr.le (g := fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x $ z ∘ Fin.succ))) fun x hx => by
      have ih := cauchy_polydisc (fun y => f $ Fin.cons x y) (c ∘ Fin.succ) hr
        (fun ζ hζ => (hf _ $ hcons (sphere_subset_closedBall hx) hζ).comp ζ $
          (differentiable_pi.2 $ Fin.cases (differentiable_const x) differentiable_apply) ζ) (z ∘ Fin.succ) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc] at ih ⊢
      rw [torusIntegral_const_mul, ih]
      ring, circleIntegral.integral_const_mul]
    have h1 := DifferentiableOn.circleIntegral_sub_inv_smul
      (fun x hx => ((hf _ $ hcons hx $ ball_subset_closedBall hz').comp x $
        (differentiable_pi.2 $ Fin.cases differentiable_id fun _ => differentiable_const _) x).differentiableWithinAt)
      (mem_ball.2 $ (dist_le_pi_dist z c 0).trans_lt $ mem_ball.1 hz)
    simp only [smul_eq_mul, Function.comp_apply] at h1
    have hzt : Fin.cons (z 0) (z ∘ Fin.succ) = z := Fin.cons_self_tail z
    rw [h1, hzt, pow_succ]
    ring

lemma osgood {n} {U : Set (Cn n)} {f : Cn n → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {c} (hc : c ∈ U) :
    AnalyticAt ℂ f c := by
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 $ hU.mem_nhds hc
  have hfd ζ (hζ : ζ ∈ closedBall c r) := hf.differentiableAt $ hU.mem_nhds $ hrU hζ
  have hcf : Continuous fun θ => f (tmap c r θ) :=
    continuous_iff_continuousAt.2 fun θ => (hfd _ $ tmap_mem c hr.le θ).continuousAt.comp (cont_tmap c r).continuousAt
  let pI := projIcc 0 (2 * π) Real.two_pi_pos.le
  let pr (θ : Fin n → ℝ) : Cube n := ⟨fun i => pI (θ i), fun i => (pI _).2.1, fun i => (pI _).2.2⟩
  have hcp : Continuous pr := continuous_induced_rng.2 $ continuous_pi fun i =>
    continuous_subtype_val.comp $ continuous_projIcc.comp $ continuous_apply i
  let jac (θ : Fin n → ℝ) : ℂ := ∏ i, (r : ℂ) * exp (θ i * I) * I
  have hcj : Continuous jac := continuous_finsetProd _ fun _ _ => by fun_prop
  have hi (g : CB n) : IntegrableOn _ (Cube n) := ((hcj.mul $ g.continuous.comp hcp).mul hcf).integrableOn_Icc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcj.mul hcf).continuousOn
  let L : CB n →L[ℂ] ℂ := mkContinuous
    { toFun := fun g => ∫ θ in Cube n, jac θ * g (pr θ) * f (tmap c r θ)
      map_add' := fun a b => by simpa [mul_add, add_mul] using integral_add (hi a) (hi b)
      map_smul' := fun a g => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, ← integral_const_mul]
        congr 1
        funext θ
        ring }
    (M * volume.real (Cube n)) fun g => by
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top fun θ hθ => ?_).trans $ le_of_eq $ by ring
      rw [mul_comm (jac θ), mul_assoc, norm_mul, mul_comm M]
      grw [g.norm_coe_le_norm _]
      gcongr
      exact hM θ hθ
  let coord i : CB n :=
    ⟨fun θ => tmap c r θ.1 i, ((continuous_apply i).comp $ cont_tmap c r).comp continuous_subtype_val⟩
  let mkU {z} (hz : z ∈ ball c r) i : (CB n)ˣ := Units.mkOfMulEqOne (coord i - z i • 1)
    ⟨fun θ => (tmap c r θ.1 i - z i)⁻¹, ((coord i).continuous.sub continuous_const).inv₀ fun θ => tmap_sub_ne hr hz θ.1 i⟩
    (by ext θ; simpa [coord] using mul_inv_cancel₀ (tmap_sub_ne hr hz θ.1 i))
  let kern (z : Cn n) : CB n := ∏ i, Ring.inverse (coord i - z i • (1 : CB n))
  have hka : AnalyticAt ℂ kern c := by
    rw [show kern = ∏ i, fun z : Cn n => Ring.inverse (coord i - z i • (1 : CB n)) by
      funext z
      rw [Finset.prod_apply]]
    exact Finset.analyticAt_prod _ fun i _ => (analyticAt_inverse (𝕜 := ℂ) $ mkU (mem_ball_self hr) i).comp_of_eq
      (analyticAt_const.sub (((pj i).smulRight (1 : CB n)).analyticAt c)) rfl
  refine ((analyticAt_const (v := ((2 * π * I) ^ n)⁻¹)).mul $ (L.analyticAt _).comp hka).congr ?_
  filter_upwards [ball_mem_nhds c hr] with z hz
  have hL : L (kern z) = (2 * π * I) ^ n * f z := by
    rw [← cauchy_polydisc f c hr hfd z hz]
    refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    have hka' : kern z (pr θ) = ∏ i, (tmap c r θ i - z i)⁻¹ := by
      simp only [kern, ContinuousMap.coe_prod, Finset.prod_apply]
      refine prod_congr rfl fun i _ => ?_
      change Ring.inverse (mkU hz i : CB n) (pr θ) = _
      rw [Ring.inverse_unit]
      change (tmap c r (pr θ).1 i - z i)⁻¹ = _
      rw [show (pr θ : Fin n → ℝ) = θ from funext fun j => congrArg Subtype.val $ projIcc_of_mem Real.two_pi_pos.le ⟨hθ.1 j, hθ.2 j⟩]
    simp only [hka', smul_eq_mul, jac]
    ring
  change ((2 * π * I) ^ n)⁻¹ * L (kern z) = f z
  rw [hL, inv_mul_cancel_left₀ $ pow_ne_zero _ $ by simp [Real.pi_ne_zero, I_ne_zero]]

lemma analyticAt_vec {k} {U} {f : Cn k → Cn k} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x} (hx : x ∈ U) :
    AnalyticAt ℂ f x :=
  AnalyticAt.pi fun i => osgood hU (fun z hz => (differentiableWithinAt_pi.1 $ hf z hz) i) hx

lemma deriv_ne_zero_1d {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hinj : InjOn f D) {a} (ha : a ∈ D) (hder : deriv f a = 0) : False := by
  have hDa := hD.mem_nhds ha
  let g z := f z - f a
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 fun (htop : analyticOrderAt g a = ⊤) => by
    obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff.1 $ (analyticOrderAt_eq_top.1 htop).and hDa
    have ⟨h0, hD'⟩ := hrb (y := a + (r / 2 : ℝ)) $ by
      simp [abs_of_pos hr]
      linarith
    have := hinj hD' ha $ sub_eq_zero.1 h0
    simp at this
    linarith
  have hga : AnalyticAt ℂ g a := (hf.analyticAt hDa).sub analyticAt_const
  obtain ⟨u, hu, hua, hfac⟩ := hga.analyticOrderAt_eq_natCast.1 hn.symm
  simp only [smul_eq_mul] at hfac
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hua $ by simpa [g] using hfac.self_of_nhds.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hd : HasDerivAt (fun z => (z - a) * u z) (u a) a :=
      (((hasDerivAt_id' a).sub_const a).mul hu.differentiableAt.hasDerivAt).congr_deriv $ by simp
    simp only [pow_one] at hfac
    have h1 := (EventuallyEq.deriv_eq hfac).trans hd.deriv
    rw [show deriv g a = deriv f a from deriv_sub_const _, hder] at h1
    exact hua h1.symm
  let v z := (u z / u a) ^ ((n : ℂ)⁻¹)
  have hva : AnalyticAt ℂ v a := (hu.div analyticAt_const hua).cpow analyticAt_const $ by simp [hua, one_mem_slitPlane]
  let w z := (z - a) * v z
  have hwd : HasDerivAt w 1 a := (((hasDerivAt_id' a).sub_const a).mul hva.differentiableAt.hasDerivAt).congr_deriv $ by simp [v, hua]
  have hwa : AnalyticAt ℂ w a := (analyticAt_id.sub analyticAt_const).mul hva
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 $
    (hwa.eventually_constant_or_nhds_le_map_nhds.resolve_left fun hc =>
      one_ne_zero $ hwd.deriv.symm.trans $ by
        rw [EventuallyEq.deriv_eq hc]
        simp)
    (image_mem_map $ inter_mem hDa hfac)
  simp only [w, sub_self, zero_mul] at hball
  have hprim := isPrimitiveRoot_exp n hn0
  set ζ := exp (2 * π * I / n)
  obtain ⟨z₁, ⟨hz₁D, hz₁⟩, hw₁⟩ := hball (a := ((ε / 2 : ℝ) : ℂ)) $ by
    simp [abs_of_pos hε]
    linarith
  obtain ⟨z₂, ⟨hz₂D, hz₂⟩, hw₂⟩ := hball (a := ζ * ((ε / 2 : ℝ) : ℂ)) $ by
    simp [hprim.norm'_eq_one hn0, abs_of_pos hε]
    linarith
  have hf12 : f z₁ = f z₂ := by
    have : g z₁ / u a = g z₂ / u a := by
      dsimp only at hw₁ hw₂
      rw [hz₁, hz₂, mul_div_assoc, mul_div_assoc, ← cpow_nat_inv_pow (u z₁ / u a) hn0,
        ← cpow_nat_inv_pow (u z₂ / u a) hn0, ← mul_pow, ← mul_pow, hw₁, hw₂, mul_pow, hprim.pow_eq_one, one_mul]
    simpa [g, hua] using this
  rw [hinj hz₁D hz₂D hf12, hw₂] at hw₁
  exact hprim.ne_one (by omega) $ mul_right_cancel₀ (ofReal_ne_zero.2 (half_pos hε).ne') $ by simpa using hw₁

lemma criticalFlatNotInjective {k} {U : Set (Cn k)} {f : Cn k → Cn k} {a : Cn k}
    (hk : 2 ≤ k) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (haU : a ∈ U)
    (hJa : det (fderiv ℂ f a : Cn k →ₗ[ℂ] Cn k) = 0)
    (hflat : ∀ b ∈ U, det (fderiv ℂ f b : Cn k →ₗ[ℂ] Cn k) = 0 → fderiv ℂ f b = 0)
    (hinj : InjOn f U) : False := by
  let J z := det (fderiv ℂ f z : Cn k →ₗ[ℂ] Cn k)
  have hJan : AnalyticOnNhd ℂ J U := fun z hz => by
    rw [show J = fun w => ∑ σ : Equiv.Perm (Fin k),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ f w (Pi.single i 1) (σ i) by
      funext w
      dsimp only [J]
      rw [← det_toMatrix', Matrix.det_apply]
      refine sum_congr rfl fun _ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl]
    exact analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul $ analyticAt_fun_prod _ fun i _ =>
      ((((pj (σ i)).comp $ ContinuousLinearMap.apply ℂ (Cn k) $ Pi.single i 1) : (Cn k →L[ℂ] Cn k) →L[ℂ] ℂ).analyticAt _).comp (analyticAt_vec hU hf hz).fderiv
  obtain ⟨R, hR, hball⟩ := isOpen_iff.1 hU a haU
  by_cases hall : ∀ z ∈ ball a R, J z = 0
  · have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    have he0 : a + ((R / 2 : ℝ) : ℂ) • (1 : Cn k) ∈ ball a R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_of_nonneg (half_pos hR).le]
      linarith
    have h1 := congrFun (congrArg (· - a) $ hinj (hball he0) haU $
      (convex_ball a R).is_const_of_fderivWithin_eq_zero (hf.mono hball)
        (fun w hw => by
          rw [fderivWithin_of_isOpen isOpen_ball hw]
          exact hflat w (hball hw) $ hall w hw)
        he0 $ mem_ball_self hR) ⟨0, by omega⟩
    simp at h1
    linarith
  push Not at hall
  obtain ⟨z₀, hz₀B, hz₀⟩ := hall
  have hex : ∃ m, ∃ p ∈ ball a R, J p = 0 ∧ iteratedFDeriv ℂ m J p ≠ 0 := by
    by_contra hnone
    push Not at hnone
    obtain ⟨ps, ρ, hps⟩ := hJan a haU
    exact hz₀ $ (hJan.mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball a R).isPreconnected (mem_ball_self hR) (by
        filter_upwards [isOpen_eball.mem_nhds $ mem_eball_self hps.r_pos] with y hy
        have hps0 n : ps n (fun _ => y - a) = 0 := by
          have h1 := hps.iteratedFDeriv_eq_sum_of_completeSpace (n := n) (fun _ => y - a)
          simpa [hnone n a (mem_ball_self hR) hJa, Nat.factorial_ne_zero] using h1.symm
        exact HasSum.unique (hps.hasSum_sub hy) $ by simp [hps0, hasSum_zero]) hz₀B
  classical
  set m := Nat.find hex
  obtain ⟨p, hpB, hJp, hJm⟩ : ∃ p ∈ ball a R, J p = 0 ∧ iteratedFDeriv ℂ m J p ≠ 0 := Nat.find_spec hex
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (n := m) fun hm => hJm $ by
    rw [hm]
    ext
    simp [hJp]
  have hmin q (hqB : q ∈ ball a R) (hJq : J q = 0) : iteratedFDeriv ℂ r J q = 0 := by
    by_contra hne
    exact Nat.find_min hex (by omega : r < m) ⟨q, hqB, hJq, hne⟩
  rw [hr] at hJm
  obtain ⟨x, hx⟩ : ∃ x : Fin (r + 1) → Cn k, iteratedFDeriv ℂ (r + 1) J p x ≠ 0 := by
    by_contra h
    push Not at h
    exact hJm $ ContinuousMultilinearMap.ext h
  let h z := iteratedFDeriv ℂ r J z (Fin.tail x)
  have hcd_iter : ContDiffAt ℂ 1 (iteratedFDeriv ℂ r J) p := (hJan p $ hball hpB).contDiffAt.iteratedFDeriv_right le_top
  have hcd_h : ContDiffAt ℂ 1 h p :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin r => Cn k) ℂ $ Fin.tail x).contDiff.contDiffAt.comp p hcd_iter
  set L := fderiv ℂ h p
  have hLx : L (x 0) ≠ 0 := by rwa [← (hcd_iter.differentiableAt one_ne_zero).iteratedFDeriv_succ_apply_left']
  let w := (L (x 0))⁻¹ • x 0
  have hLw : L w = 1 := by simp [w, inv_mul_cancel₀ hLx]
  obtain ⟨u, huK, hu0⟩ := exists_mem_ne_zero_of_ne_bot (show ker (L : Cn k →ₗ[ℂ] ℂ) ≠ ⊥ from fun hbot => by
    have h1 := finrank_range_add_finrank_ker (L : Cn k →ₗ[ℂ] ℂ)
    have h2 : finrank ℂ (range (L : Cn k →ₗ[ℂ] ℂ)) ≤ 1 := by simpa using finrank_le (range (L : Cn k →ₗ[ℂ] ℂ))
    rw [hbot, finrank_bot, finrank_fin_fun] at h1
    omega)
  have hLu : L u = 0 := huK
  let gL : ℂ × ℂ →L[ℂ] Cn k := (fst ℂ ℂ ℂ).smulRight u + (snd ℂ ℂ ℂ).smulRight w
  let g q := p + gL q
  have hginj : Function.Injective g := fun a b hab => by
    have h1 : a.2 = b.2 := by simpa [gL, hLu, hLw] using congrArg L (add_left_cancel hab)
    exact Prod.ext (smul_left_injective ℂ hu0 $ by simpa [gL, h1] using add_left_cancel hab) h1
  let Φ (q : ℂ × ℂ) : ℂ × ℂ := (q.1, h (g q))
  have hg0 : g 0 = p := by simp [g]
  have hΦd : HasFDerivAt Φ (ContinuousLinearEquiv.refl ℂ (ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] ℂ × ℂ) 0 := by
    have hhd : HasFDerivAt h L (g 0) := by
      rw [hg0]
      exact (hcd_h.differentiableAt one_ne_zero).hasFDerivAt
    have h2 : HasFDerivAt (fun q => h (g q)) (snd ℂ ℂ ℂ) 0 := by
      have h3 := hhd.comp 0 $ gL.hasFDerivAt.const_add p
      rwa [show L.comp gL = snd ℂ ℂ ℂ from ContinuousLinearMap.ext fun ⟨s, t⟩ => by simp [gL, hLu, hLw]] at h3
    have h4 := (hasFDerivAt_fst (𝕜 := ℂ) (p := (0 : ℂ × ℂ))).prodMk h2
    rwa [show (fst ℂ ℂ ℂ).prod (snd ℂ ℂ ℂ) = (ContinuousLinearEquiv.refl ℂ (ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] ℂ × ℂ)
      from ContinuousLinearMap.ext fun ⟨s, t⟩ => by simp] at h4
  have hgc : ContDiffAt ℂ 1 g 0 := contDiffAt_const.add gL.contDiff.contDiffAt
  have hΦc : ContDiffAt ℂ 1 Φ 0 := contDiffAt_fst.prodMk $ (hg0 ▸ hcd_h).comp 0 hgc
  let H := hΦc.toOpenPartialHomeomorph Φ hΦd one_ne_zero
  have hΦ0 : Φ 0 = 0 := Prod.ext rfl $ by simp [Φ, hg0, h, hmin p hpB hJp]
  have h0T : (0 : ℂ × ℂ) ∈ H.target := hΦ0 ▸ hΦc.image_mem_toOpenPartialHomeomorph_target hΦd one_ne_zero
  have hH0 : H.symm 0 = 0 := by
    conv_lhs => rw [← hΦ0]
    exact H.left_inv $ hΦc.mem_toOpenPartialHomeomorph_source hΦd one_ne_zero
  have hinv : ContDiffAt ℂ 1 H.symm 0 := hΦ0 ▸ hΦc.to_localInverse hΦd one_ne_zero
  obtain ⟨O, hO, hOo, h0O⟩ := _root_.eventually_nhds_iff.1 $ hinv.eventually $ by simp
  let ψ q := g (H.symm q)
  have hψ0 : ψ 0 = p := by simp [ψ, hH0, hg0]
  let W := (H.target ∩ ψ ⁻¹' ball a R) ∩ O
  obtain ⟨r₀, hr₀, hr₀W⟩ := nhds_basis_closedBall.mem_iff.1 $
    inter_mem (inter_mem (H.open_target.mem_nhds h0T) $
      ((by rw [hH0]; exact hgc.continuousAt : ContinuousAt g (H.symm 0)).comp hinv.continuousAt).preimage_mem_nhds $
        hψ0 ▸ isOpen_ball.mem_nhds hpB) $ hOo.mem_nhds h0O
  have h0n : ‖(0 : ℂ)‖ ≤ r₀ := by simp [hr₀.le]
  have hJ0 {q} (hq : q ∈ W) (hJq : J (ψ q) = 0) : q.2 = 0 := by
    have h2 : h (ψ q) = q.2 := congrArg Prod.snd $ H.right_inv hq.1.1
    rw [← h2]
    exact congrFun (congrArg DFunLike.coe $ hmin _ hq.1.2 hJq) (Fin.tail x)
  have hpair (s t : ℂ) (hs : ‖s‖ ≤ r₀) (ht : ‖t‖ ≤ r₀) : ((s, t) : ℂ × ℂ) ∈ W :=
    hr₀W $ by
      rw [mem_closedBall, dist_zero_right, Prod.norm_def]
      exact max_le hs ht
  have hψd {q} (hq : q ∈ W) : DifferentiableAt ℂ ψ q :=
    (gL.differentiableAt.const_add p).comp q $ (hO _ hq.2).differentiableAt one_ne_zero
  have hcontJ {q} (hq : q ∈ W) : ContinuousAt (fun z => J (ψ z)) q :=
    (hJan _ $ hball hq.1.2).continuousAt.comp (hψd hq).continuousAt
  obtain ⟨t₀, ht₀K, ht₀min⟩ := (isCompact_sphere (0 : ℂ) r₀).exists_isMinOn (NormedSpace.sphere_nonempty.2 hr₀.le) fun t ht =>
    ((hcontJ $ hpair 0 t h0n (mem_sphere_zero_iff_norm.1 ht).le).comp $ continuousAt_const.prodMk continuousAt_id).norm.continuousWithinAt
  set μ := ‖J (ψ (0, t₀))‖
  have hμ0 : 0 < μ := norm_pos_iff.2 fun h0 => by
    have h2 := mem_sphere_zero_iff_norm.1 ht₀K
    have h1 : t₀ = 0 := hJ0 (hpair 0 t₀ h0n h2.le) h0
    rw [h1, norm_zero] at h2
    linarith
  obtain ⟨δ, hδ, hδ_all⟩ := Metric.eventually_nhds_iff.1 $
    (((isCompact_sphere (0 : ℂ) r₀).eventually_forall_of_forall_eventually (P := fun s t => μ / 2 < ‖J (ψ (s, t))‖) fun t ht =>
      (hcontJ $ hpair 0 t h0n (mem_sphere_zero_iff_norm.1 ht).le).norm.eventually $
        lt_mem_nhds (a := μ / 2) $ by
          have := isMinOn_iff.1 ht₀min t ht
          dsimp at this
          linarith).and
      ((ContinuousAt.comp (f := fun s : ℂ => (s, (0 : ℂ))) (hcontJ $ hpair 0 0 h0n h0n) $ continuousAt_id.prodMk continuousAt_const).norm.eventually $
        gt_mem_nhds (a := μ / 2) $ by simpa [show ((0 : ℂ), (0 : ℂ)) = 0 from rfl, hψ0, hJp] using half_pos hμ0)).and $
    ball_mem_nhds (0 : ℂ) hr₀
  have hW0 {t} (ht : t ∈ ball (0 : ℂ) δ) : ((t, 0) : ℂ × ℂ) ∈ W :=
    hpair t 0 (mem_ball_zero_iff.1 (hδ_all $ mem_ball.1 ht).2).le h0n
  have hJs0 {s} (hs : s ∈ ball (0 : ℂ) δ) : J (ψ (s, 0)) = 0 := by
    obtain ⟨⟨hs1, hs2⟩, hs3⟩ := hδ_all $ mem_ball.1 hs
    have hsr : ‖s‖ ≤ r₀ := (mem_ball_zero_iff.1 hs3).le
    by_contra hne0
    have hdiff : DifferentiableOn ℂ (fun t : ℂ => (J (ψ (s, t)))⁻¹) (closedBall 0 r₀) := fun t ht => by
      have hq := hpair s t hsr $ mem_closedBall_zero_iff.1 ht
      exact ((DifferentiableAt.comp (g := J) t (hJan _ $ hball hq.1.2).differentiableAt $
        (hψd hq).comp t $ (differentiableAt_const s).prodMk differentiableAt_id).inv fun h0 =>
          hne0 $ (hJ0 hq h0) ▸ h0).differentiableWithinAt
    have hbd := norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hdiff.diffContOnCl_ball subset_rfl)
      (C := (μ / 2)⁻¹) (fun t ht => by
        rw [frontier_ball 0 hr₀.ne'] at ht
        rw [norm_inv]
        exact inv_anti₀ (half_pos hμ0) (hs1 t ht).le) $ subset_closure $ mem_ball_self hr₀
    rw [norm_inv] at hbd
    linarith [(inv_lt_inv₀ (half_pos hμ0) $ norm_pos_iff.2 hne0).2 hs2]
  have hψ0d {t} (ht : t ∈ ball (0 : ℂ) δ) : DifferentiableAt ℂ (fun s : ℂ => ψ (s, 0)) t :=
    DifferentiableAt.comp (g := ψ) t (hψd $ hW0 ht) $ differentiableAt_id.prodMk $ differentiableAt_const 0
  set s₁ : ℂ := ((δ / 2 : ℝ) : ℂ)
  have hs₁ : s₁ ∈ ball (0 : ℂ) δ := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (half_pos hδ).le]
    linarith
  have hconst := (convex_ball (0 : ℂ) δ).is_const_of_fderivWithin_eq_zero (f := fun s => f (ψ (s, 0)))
    (fun t ht => ((hf.differentiableAt $ hU.mem_nhds $ hball (hW0 ht).1.2).comp t $ hψ0d ht).differentiableWithinAt)
    (fun t ht => by
      rw [fderivWithin_of_isOpen isOpen_ball ht]
      have hfd := ((hf.differentiableAt $ hU.mem_nhds $ hball (hW0 ht).1.2).hasFDerivAt.comp t (hψ0d ht).hasFDerivAt).fderiv
      rw [hflat _ (hball (hW0 ht).1.2) $ hJs0 ht, ContinuousLinearMap.zero_comp] at hfd
      exact hfd)
    hs₁ $ mem_ball_self hδ
  have h1 : (s₁, (0 : ℂ)) = 0 := by
    rw [← H.right_inv (hW0 hs₁).1.1, ← H.right_inv h0T,
      hginj $ hinj (hball (hW0 hs₁).1.2) (hball $ show ψ 0 ∈ ball a R by rwa [hψ0]) hconst]
  have h2 := congrArg Prod.fst h1
  simp [s₁] at h2
  linarith

end Core11

namespace AlpogeRHCore11

open Core11

theorem injectiveHolomorphicJacobianNeZero :
    ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
      IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U →
      ∀ x ∈ U, LinearMap.det (fderiv ℂ f x : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U f hU hf hinj x hx hdet
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [det_eq_one_of_subsingleton] at hdet
      exact one_ne_zero hdet
    · set e : Cn 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
      refine deriv_ne_zero_1d (hU.preimage e.symm.continuous)
        (e.differentiable.comp_differentiableOn $ hf.comp e.symm.differentiable.differentiableOn fun _ h => h)
        (fun s hs t ht h => e.symm.injective $ hinj hs ht $ e.injective h) (a := e x) (by simpa using hx) ?_
      have hφx := e.hasFDerivAt.comp (e x) $ ((by simpa using (hf.differentiableAt $ hU.mem_nhds hx).hasFDerivAt :
        HasFDerivAt f (fderiv ℂ f x) (e.symm (e x)))).comp (e x) e.symm.hasFDerivAt
      rw [show deriv (e ∘ f ∘ e.symm) (e x) = _ from hφx.hasDerivAt.deriv]
      rw [← det_toMatrix $ Pi.basisFun ℂ (Fin 1), Matrix.det_unique] at hdet
      simp only [toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
        show (Pi.single (default : Fin 1) (1 : ℂ) : Cn 1) = 1 from funext fun i => by fin_cases i; rfl] at hdet
      simpa [e] using hdet
  · by_cases hall : ∀ b ∈ U, det (fderiv ℂ f b : Cn k →ₗ[ℂ] Cn k) = 0 → fderiv ℂ f b = 0
    · exact criticalFlatNotInjective hk hU hf hx hdet hall hinj
    push Not at hall
    obtain ⟨b, hb, hdb, hne⟩ := hall
    set A := fderiv ℂ f b
    set AL : Cn k →ₗ[ℂ] Cn k := A.toLinearMap
    set W := range AL
    set K := ker AL
    set d := finrank ℂ K
    have hd0 : 0 < d := finrank_pos_iff_exists_ne_zero.2 $
      let ⟨v, hv, hv0⟩ := exists_mem_ne_zero_of_ne_bot (bot_lt_ker_of_det_eq_zero hdb).ne'
      ⟨⟨v, hv⟩, by simpa using hv0⟩
    have hdk : d < k := by
      simpa [finrank_fin_fun] using finrank_lt (show K ≠ ⊤ from fun h0 =>
        hne $ ContinuousLinearMap.coe_injective $ by simpa [K, ker_eq_top] using h0)
    obtain ⟨C, hWC⟩ := W.exists_isCompl
    obtain ⟨K', hKK'⟩ := K.exists_isCompl
    let eC : C ≃ₗ[ℂ] Cn d := LinearEquiv.ofFinrankEq _ _ $ by
      have h1 := finrank_range_add_finrank_ker AL
      have h2 := finrank_add_eq_of_isCompl hWC
      rw [finrank_fin_fun] at h1 h2 ⊢
      change finrank ℂ W + d = k at h1
      omega
    let eK : K ≃ₗ[ℂ] Cn d := LinearEquiv.ofFinrankEq _ _ $ by rw [finrank_fin_fun]
    let P := toContinuousLinearMap $ W.projection C hWC
    let E := toContinuousLinearMap $ C.subtype ∘ₗ eC.symm.toLinearMap
    let lam := toContinuousLinearMap $ eK.toLinearMap ∘ₗ K.projectionOnto K' hKK'
    let ℓ := toContinuousLinearMap $ eC.toLinearMap ∘ₗ C.projectionOnto W hWC.symm
    have hPE t : P (E t) = 0 := projection_apply_of_mem_right hWC (eC.symm t).2
    have hPP x : P (P x) = P x := projection_apply_of_mem_left hWC $ projection_apply_mem hWC x
    let M : Cn k →ₗ[ℂ] Cn k := AL + (E.comp lam : _)
    let M' : Cn k ≃L[ℂ] Cn k := (LinearEquiv.ofInjectiveEndo M $ (injective_iff_map_eq_zero M).2 fun v hv => by
      have hv' : A v + E (lam v) = 0 := hv
      have hAv : A v = 0 := (disjoint_def.1 hWC.disjoint) (A v) (mem_range_self _ v) $ by
        rw [eq_neg_of_add_eq_zero_left hv']
        exact C.neg_mem (eC.symm _).2
      have h1 : eK (K.projectionOnto K' hKK' v) = 0 := eC.symm.injective $ Subtype.ext $ by
        rw [hAv, zero_add] at hv'
        exact hv'.trans (map_zero E).symm
      rw [projectionOnto_apply_of_mem_left hKK' hAv, LinearEquiv.map_eq_zero_iff] at h1
      exact congrArg Subtype.val h1).toContinuousLinearEquiv
    let Φ z := P (f z) + E (lam z)
    have hΦd : HasFDerivAt Φ (M' : Cn k →L[ℂ] Cn k) b :=
      ((P.hasFDerivAt.comp b (hf.differentiableAt $ hU.mem_nhds hb).hasFDerivAt).add (E.comp lam).hasFDerivAt).congr_fderiv $ by
        ext1 v
        exact congrArg (· + E (lam v)) $ projection_apply_of_mem_left hWC $ mem_range_self AL v
    have hΦc : ContDiffAt ℂ 1 Φ b :=
      (P.contDiff.contDiffAt.comp b (analyticAt_vec hU hf hb).contDiffAt).add (E.comp lam).contDiff.contDiffAt
    let H := hΦc.toOpenPartialHomeomorph Φ hΦd one_ne_zero
    have hHb : H.symm (Φ b) = b := H.left_inv $ hΦc.mem_toOpenPartialHomeomorph_source hΦd one_ne_zero
    have hinv : ContDiffAt ℂ 1 H.symm (Φ b) := hΦc.to_localInverse hΦd one_ne_zero
    obtain ⟨O, hO, hOo, hbO⟩ := _root_.eventually_nhds_iff.1 $ hinv.eventually $ by simp
    let aff t := P (f b) + E t
    let V := aff ⁻¹' ((H.target ∩ H.symm ⁻¹' U) ∩ O)
    let γ t := H.symm (aff t)
    have hfib r (hr : r ∈ V) : W.projection C hWC (f (γ r)) = W.projection C hWC (f b) := by
      have h2 := congrArg P $ H.right_inv hr.1.1
      simp only [H, ContDiffAt.toOpenPartialHomeomorph_coe, Φ, map_add, hPE, add_zero, hPP] at h2
      exact h2.trans (show P (aff r) = P (f b) by simp [aff, hPE, hPP])
    apply ih d hdk V (fun t => ℓ (f (γ t)))
      (((H.isOpen_inter_preimage_symm hU).inter hOo).preimage $ continuous_const.add E.continuous)
      (ℓ.differentiable.comp_differentiableOn $ hf.comp
        (fun t ht => ((hO _ ht.2).differentiableAt one_ne_zero).comp t ((differentiableAt_const _).add E.differentiableAt) |>.differentiableWithinAt)
        fun _ ht => ht.1.2)
      (fun s hs t ht hst => eC.symm.injective $ Subtype.ext $ add_left_cancel (a := P (f b)) $ by
        show aff s = aff t
        rw [← H.right_inv hs.1.1, ← H.right_inv ht.1.1]
        refine congrArg H $ hinj hs.1.2 ht.1.2 ?_
        rw [← projection_add_projection_eq_self hWC (f $ γ s), ← projection_add_projection_eq_self hWC (f $ γ t),
          hfib s hs, hfib t ht, projection_apply (p := C), projection_apply (p := C), eC.injective hst])
      (lam b) ⟨⟨hΦc.image_mem_toOpenPartialHomeomorph_target hΦd one_ne_zero, by
        show H.symm (Φ b) ∈ U
        rwa [hHb]⟩, hbO⟩
    have hfd' : HasFDerivAt f A (γ (lam b)) := by
      show HasFDerivAt f A (H.symm (Φ b))
      rw [hHb]
      exact (hf.differentiableAt $ hU.mem_nhds hb).hasFDerivAt
    rw [show fderiv ℂ (fun t => ℓ (f (γ t))) (lam b) = 0 from
      (ℓ.hasFDerivAt.comp (lam b) $ hfd'.comp (lam b) $
        ((hinv.differentiableAt one_ne_zero).comp (lam b) $ (differentiableAt_const _).add E.differentiableAt).hasFDerivAt).fderiv.trans $ by
        ext1 v
        show eC (C.projectionOnto W hWC.symm (A _)) = 0
        exact (congrArg eC $ projectionOnto_apply_of_mem_right hWC.symm $
          mem_range_self AL _).trans $ map_zero eC,
      toLinearMap_zero, det_zero, finrank_fin_fun]
    exact zero_pow hd0.ne'

end AlpogeRHCore11
