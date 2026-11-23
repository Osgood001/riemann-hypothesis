import B1

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup Topology Metric
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === Reusable measurable equivalences & ext1 helpers ===

def actEquiv {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] {μ : Measure Y}
    (hP : Pres G μ) (g : G) : Y ≃ᵐ Y where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (hP g).measurable
  measurable_invFun := (hP g⁻¹).measurable

lemma ext1_coe (f : P → ℂ) (z : P) : ext1 f z.1 = f z := by unfold ext1; rw [dite_eq_left z.2]; rfl

lemma ext1_of_im (f : P → ℂ) {t : ℂ} (h : t.im ≠ 0) : ext1 f t = f ⟨t, h⟩ := by unfold ext1; rw [dite_eq_left h]

-- === FormsStableUnderOperators ===

lemma hol1_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) (h : ∀ i ∈ s, Hol1 (g i)) :
    Hol1 (fun t => ∑ i ∈ s, g i t) := by
  have e : ext1 (fun t => ∑ i ∈ s, g i t) = fun t => ∑ i ∈ s, ext1 (g i) t := funext fun t => by unfold ext1; split_ifs <;> simp
  unfold Hol1; rw [e]; exact (DifferentiableOn.sum h).congr fun _ _ => by simp [Finset.sum_apply]

lemma hol1_add {f g : P → ℂ} (hf : Hol1 f) (hg : Hol1 g) : Hol1 (fun t => f t + g t) := by
  have e : ext1 (fun t => f t + g t) = fun t => ext1 f t + ext1 g t := funext fun t => by unfold ext1; split_ifs <;> simp
  unfold Hol1 at *; rw [e]; exact hf.add hg

lemma hol1_const_mul (c : ℂ) {f : P → ℂ} (hf : Hol1 f) : Hol1 (fun t => c * f t) := by
  have e : ext1 (fun t => c * f t) = fun t => c * ext1 f t := funext fun t => by unfold ext1; split_ifs <;> simp
  unfold Hol1 at *; rw [e]; exact hf.const_mul c

lemma hol1_zero : Hol1 (fun _ : P => (0 : ℂ)) := by
  have e : ext1 (fun _ : P => (0 : ℂ)) = fun _ => 0 := funext fun t => by unfold ext1; split_ifs <;> simp
  unfold Hol1; rw [e]; exact differentiableOn_const 0

lemma isForm_sub {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf) (k : I → ℕ) :
    ∀ f, f ∈ D.M k ↔ D.IsForm k f := by
  let S : Submodule ℂ (X I × Gf → ℂ) :=
    { carrier := {f | D.IsForm k f}
      zero_mem' := ⟨fun _ => ⟨continuous_const, fun _ _ => hol1_zero⟩, fun _ _ _ => by simp, fun _ _ _ => by simp, ⟨0, fun _ _ => by simp⟩⟩
      add_mem' := fun {f g} hf hg => ⟨fun x => ⟨(hf.hol x).1.add (hg.hol x).1, fun z v => hol1_add ((hf.hol x).2 z v) ((hg.hol x).2 z v)⟩,
        fun γ z x => by simp [hf.aut, hg.aut, mul_add], fun z x h => by simp [hf.lev, hg.lev, mul_add],
        let ⟨C₁, h₁⟩ := hf.bdd; let ⟨C₂, h₂⟩ := hg.bdd
        ⟨C₁ + C₂, fun z x => (mul_le_mul_of_nonneg_right (norm_add_le _ _) (nrm_nonneg k z)).trans (by rw [add_mul]; exact add_le_add (h₁ z x) (h₂ z x))⟩⟩
      smul_mem' := fun c f hf => ⟨fun x => ⟨continuous_const.mul (hf.hol x).1, fun z v => hol1_const_mul c ((hf.hol x).2 z v)⟩,
        fun γ z x => by simp [hf.aut]; ring, fun z x h => by simp [hf.lev]; ring,
        let ⟨C, h⟩ := hf.bdd
        ⟨‖c‖ * C, fun z x => by rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (h z x) (norm_nonneg c)⟩⟩ }
  have hM : D.M k = S := Submodule.span_eq S
  exact fun f => by rw [hM]; rfl

theorem forms_stable_under_operators_proof : FormsStableUnderOperators := by
  intro F I Gf _ _ _ D _ k
  refine ⟨isForm_sub D k, fun ι _ a ha f hf => ?_⟩
  rw [isForm_sub] at hf ⊢
  obtain ⟨C, hC⟩ := hf.bdd
  exact ⟨fun x => ⟨continuous_finsetSum _ fun i _ => (hf.hol (x * a i)).1,
      fun z v => hol1_finset_sum Finset.univ _ fun i _ => (hf.hol (x * a i)).2 z v⟩,
    fun γ z x => by change ∑ i, f (D.act γ z, D.j γ * x * a i) = D.J k γ z * ∑ i, f (z, x * a i)
                    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, hf.aut],
    fun z x h => ha (fun y => f (z, y)) (fun y h' => hf.lev z y h') x h,
    ⟨Fintype.card ι * C, fun z x => (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (nrm_nonneg k z)).trans $ by
      rw [Finset.sum_mul]; exact (Finset.sum_le_sum fun i _ => hC z (x * a i)).trans (by simp)⟩⟩

-- === E3: Cusp region volume finite ===

theorem cusp_region_volume_finite_proof : B1a → UpperHalfPlaneMeasureCoordinates → C2 → E0a → E0d → E3 := by
  intro hB1a _ _ hE0a _ F I Gf _ _ _ D hD b hb
  obtain ⟨hcnt, hsf, -, hPY, -⟩ := hE0a F I Gf D hD
  have : Countable (PG F) := hcnt; have : SigmaFinite (volume : Measure D.Xs) := hsf
  have : SigmaFinite (volume : Measure P) := hB1a.1; have : Countable D.Om := hD.cO
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink; obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  let B1 : Set {z : ℂ // z.im ≠ 0} := {w | |w.1.re| ≤ C ∧ c ≤ |w.1.im|}
  have hB1m : MeasurableSet B1 :=
    (measurableSet_le (continuous_abs.comp (continuous_re.comp continuous_subtype_val)).measurable measurable_const).inter
      (measurableSet_le measurable_const (continuous_abs.comp (continuous_im.comp continuous_subtype_val)).measurable)
  have hB1fin : (volume : Measure P) B1 < ∞ := by
    have hK0 : 0 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) := by positivity
    have hG : ∫⁻ t : ℂ, oR ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) < ∞ :=
      ((Complex.volume_preserving_equiv_real_prod.integrable_comp
        (integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq).aestronglyMeasurable).2
        (integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq)).lintegral_lt_top
    have hpt (t : ℂ) (h1 : |t.re| ≤ C) (h2 : c ≤ |t.im|) :
        1 / t.im ^ 2 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by
      have hc2 : 0 < c ^ 2 := by positivity
      have hb : c ^ 2 ≤ t.im ^ 2 := by nlinarith [sq_abs t.im, mul_nonneg (sub_nonneg.2 h2) (add_nonneg (abs_nonneg t.im) hc.le)]
      have ha : t.re ^ 2 ≤ C ^ 2 := by nlinarith [sq_abs t.re, mul_nonneg (sub_nonneg.2 h1) (by linarith [abs_nonneg t.re] : 0 ≤ C + |t.re|)]
      have e1 : 1 ≤ (1 + C ^ 2) * (1 + t.re ^ 2)⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
      have e2 : 1 / t.im ^ 2 ≤ (1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹ := by
        have : 1 ≤ t.im ^ 2 / c ^ 2 := (le_div_iff₀ hc2).2 (by linarith)
        rw [← div_eq_mul_inv, div_le_div_iff₀ (hc2.trans_le hb) (by positivity), add_mul, one_mul, one_div, inv_mul_eq_div]; linarith
      calc _ = 1 * (1 / t.im ^ 2) := (one_mul _).symm
        _ ≤ _ := mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = _ := by ring
    change (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).withDensity (fun z => oR (1 / z.1.im ^ 2)) B1 < ∞
    rw [withDensity_apply _ hB1m]
    calc _ ≤ ∫⁻ z : {z : ℂ // z.im ≠ 0}, oR ((1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + z.1.re ^ 2)⁻¹ * (1 + z.1.im ^ 2)⁻¹))
              ∂(Measure.comap Subtype.val volume) :=
            (setLIntegral_mono' hB1m fun z hz => ENNReal.ofReal_le_ofReal (hpt z.1 hz.1 hz.2)).trans (setLIntegral_le_lintegral _ _)
      _ ≤ ∫⁻ t : ℂ, oR ((1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹)) :=
            (lint_comap isOpen_U.measurableSet volume fun t : ℂ => oR ((1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹))).trans_le
              (setLIntegral_le_lintegral _ _)
      _ = oR ((1 + C ^ 2) * (1 + 1 / c ^ 2)) * ∫⁻ t : ℂ, oR ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by
            simp_rw [ENNReal.ofReal_mul hK0]; exact lintegral_const_mul _ (by fun_prop)
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG
  let T : Set D.Om := (fun x : Gf => ((x : Gf ⧸ D.H) : D.Om)) '' (S : Set Gf)
  let B1P : Set P := B1
  let U : Set D.Xs := Set.univ.pi fun _ : I => B1P
  have hS : MeasurableSet (T ×ˢ U) := MeasurableSet.of_discrete.prod (MeasurableSet.univ_pi fun _ => hB1m)
  have hcover (y : D.Y) : ∃ g : PG F, g • y ∈ T ×ˢ U := by
    obtain ⟨s, hs0, hs⟩ := hmink y.2 (D.rep y.1); obtain ⟨γ, hγ⟩ := row_exists s hs0
    set y' : D.Y := (γ : PG F) • y
    have h1 : c₀ ≤ D.Ht ![0, 1] y'.2 (D.rep y'.1) := by
      change c₀ ≤ D.HtY ![0, 1] ((γ : PG F) • y); rw [htY_smul D hD ![0, 1] e01_ne γ y, hγ]; exact hs
    obtain ⟨bb, -, ⟨x', hx'S, h, hhH, hjx⟩, hSg⟩ := hnorm y'.2 (D.rep y'.1) h1
    refine ⟨(bb : PG F) * (γ : PG F), ?_, ?_⟩
    · rw [mul_smul]
      have hm := D.mk_smulO bb (D.rep y'.1); rw [rep_spec] at hm
      exact ⟨x', hx'S, by change ((x' : Gf ⧸ D.H) : D.Om) = (bb : PG F) • y'.1; rw [hm, hjx]
                          exact (QuotientGroup.eq.2 (by simpa using inv_mem hhH)).symm⟩
    · rw [mul_smul]; change (bb : PG F) • y'.2 ∈ U; rw [D.mk_smulX]
      exact fun v _ => ⟨(hSg v).1, (hSg v).2.1⟩
  refine (orbit_cover D.μY hPY b hb _ hS hcover).trans_lt ?_
  rw [Dat.μY, Measure.prod_prod]
  refine ENNReal.mul_lt_top (Measure.count_apply_lt_top.2 (S.finite_toSet.image _)) ?_
  change (Measure.pi fun _ : I => (volume : Measure P)) (Set.univ.pi fun _ : I => B1P) < ∞
  rw [Measure.pi_pi]; exact ENNReal.prod_lt_top fun _ _ => hB1fin

-- === E4 & faceMap_zero_comp_eq_one: Kernel transform & inverse symmetry ===

def tm {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)
    (k : I → ℕ) (ω : D.Om) (w : X I) (p : X I × Gf) (g : GL2 F) : ℂ :=
  D.ee ((D.rep ω)⁻¹ * (D.j g)⁻¹ * p.2) * (qq k p.1 (D.act g w) * D.J k g w)

section KernLemmas
variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

lemma tm_supp (k : I → ℕ) (ω : D.Om) (w : X I) (γ : PG F) (z : X I) (x : Gf)
    (h : γ • ω ≠ ((x : Gf ⧸ D.H) : D.Om)) : tm D k ω w (z, x) γ.out = 0 := by
  unfold tm; rw [Dat.ee, dite_eq_right, zero_mul]
  intro hm; apply h; rw [smulO_out]; exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hm)

lemma tm_center (k : I → ℕ) (hc : D.Compat k) (ω : D.Om) (w : X I) (p : X I × Gf) (g c : GL2 F)
    (hcc : c ∈ center (GL2 F)) : tm D k ω w p (g * c) = tm D k ω w p g := by
  unfold tm; set h : D.H := ⟨D.j c, D.cenH c hcc⟩
  have hz := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ (D.cenC c hcc)) (D.rep ω)⁻¹
  have e : (D.rep ω)⁻¹ * (D.j (g * c))⁻¹ * p.2 = ((h⁻¹ : D.H) : Gf) * ((D.rep ω)⁻¹ * (D.j g)⁻¹ * p.2) := by
    rw [map_mul, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, hz]; simp [h, mul_assoc]
  rw [e, ee_mul_left, J_mul, act_center D c hcc, act_mul, act_center D c hcc, J_center D k hc c hcc, map_inv]
  have hu : (((D.χ h)⁻¹ : ℂˣ) : ℂ) * (D.χ h : ℂ) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination (D.ee ((D.rep ω)⁻¹ * (D.j g)⁻¹ * p.2) * (qq k p.1 (D.act g w) * D.J k g w)) * hu

lemma norm_tm_le (hD : D.Ax) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (y : D.Y) (γ : PG F) (z : X I) (x : Gf) :
    ‖tm D k y.1 y.2 (z, x) γ.out‖ ≤
      {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)}.indicator (fun δ => Kap k z (D.act δ.out y.2)) γ *
        (cst k * nrm k y.2 / nrm k z) := by
  by_cases hγ : γ • y.1 = ((x : Gf ⧸ D.H) : D.Om)
  · rw [indicator_of_mem (show γ ∈ {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)} from hγ)]
    unfold tm; rw [norm_mul]
    calc _ ≤ 1 * ‖qq k z (D.act γ.out y.2) * D.J k γ.out y.2‖ := mul_le_mul_of_nonneg_right (norm_ee_le D hD _) (norm_nonneg _)
      _ = _ := by rw [one_mul, eq_div_of_mul_eq (nrm_pos k z).ne' (norm_qJ D k hk γ.out z y.2)]; ring
  · rw [tm_supp D k y.1 y.2 γ z x hγ]; simp [hγ]

lemma kap_sum_real (hD : D.Ax) (hS : KapSum) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (y : D.Y) :
    ∃ C : ℝ, ∀ (ω' : D.Om) (z : X I),
      Summable ({δ : PG F | δ • y.1 = ω'}.indicator fun δ => Kap k z (D.act δ.out y.2)) ∧
      ∑' δ, {δ : PG F | δ • y.1 = ω'}.indicator (fun δ => Kap k z (D.act δ.out y.2)) δ ≤ C := by
  obtain ⟨c₀, hc₀, hm⟩ := hD.mink; obtain ⟨s, hs, hsy⟩ := hm y.2 (D.rep y.1)
  obtain ⟨C, hC'⟩ := hS F I Gf D hD k hk c₀ hc₀
  refine ⟨max (C * (1 + D.HtY s y)) 0, fun ω' z => ?_⟩
  have hb := hC' y s hs hsy ω' z; simp only [smulX_out] at hb
  have hsum : Summable fun γ : {γ : PG F // γ • y.1 = ω'} => Kap k z (D.act γ.1.out y.2) := by
    simpa [ENNReal.toReal_ofReal (Kap_nonneg k _ _)] using ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  refine ⟨(summable_subtype_iff_indicator (s := {δ : PG F | δ • y.1 = ω'})).1 hsum, ?_⟩
  rw [← _root_.tsum_subtype]
  exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 $
    (ENNReal.ofReal_tsum_of_nonneg (fun _ => Kap_nonneg k _ _) hsum).trans_le
      (hb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))

end KernLemmas

theorem kernel_level_transform_proof : B1a → B1b → B1c → E0d → KapSum → KapInt → E4 := by
  intro _ _ _ _ hS hI F I Gf _ _ _ D hD k hk hc y
  have hk1 : ∀ v, 1 ≤ k v := fun v => le_trans (by norm_num) (hk v)
  obtain ⟨C, hC'⟩ := kap_sum_real D hD hS k hk y
  obtain ⟨C', A, hA⟩ := hI I k hk
  have hnrmc : Continuous (nrm k : X I → ℝ) := continuous_finsetProd _ fun v _ =>
    (continuous_abs.comp (continuous_im.comp (continuous_subtype_val.comp (continuous_apply v)))).rpow_const fun _ => Or.inr (by positivity)
  have hnear x (z₀ : X I) : ∃ U : Set (X I), IsOpen U ∧ z₀ ∈ U ∧ ∃ M : ℝ, ∀ z ∈ U, ∀ γ : PG F,
      ‖tm D k y.1 y.2 (z, x) γ.out‖ ≤ {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)}.indicator (fun δ => Kap k z₀ (D.act δ.out y.2)) γ * M := by
    have hn0 := nrm_pos k z₀
    refine ⟨(⋂ v, {z : X I | 1 / 2 < kap (z v) (z₀ v)}) ∩ {z | nrm k z₀ / 2 < nrm k z},
      (isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (cont_kap.comp ((continuous_apply v).prodMk continuous_const))).inter
        (isOpen_lt continuous_const hnrmc),
      ⟨mem_iInter.2 fun v => by show 1 / 2 < kap (z₀ v) (z₀ v); rw [kap_self]; norm_num, by show nrm k z₀ / 2 < nrm k z₀; linarith⟩,
      A * (cst k * nrm k y.2 / (nrm k z₀ / 2)), fun z ⟨hz1, hz2⟩ γ => (norm_tm_le D hD k hk1 y γ z x).trans ?_⟩
    by_cases hγ : γ • y.1 = ((x : Gf ⧸ D.H) : D.Om)
    · rw [indicator_of_mem (show γ ∈ {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)} from hγ),
          indicator_of_mem (show γ ∈ {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)} from hγ)]
      have hK : Kap k z (D.act γ.out y.2) ≤ A * Kap k z₀ (D.act γ.out y.2) := by
        rw [Kap_symm k z, Kap_symm k z₀]; exact ((hA (D.act γ.out y.2)).2.2.2 z z₀ fun v => (mem_iInter.1 hz1 v).le).1
      have hc0 : 0 ≤ cst k * nrm k y.2 := mul_nonneg (cst_nonneg k hk1) (nrm_nonneg k _)
      calc _ ≤ (A * Kap k z₀ (D.act γ.out y.2)) * (cst k * nrm k y.2 / (nrm k z₀ / 2)) :=
            mul_le_mul hK (div_le_div_of_nonneg_left hc0 (by linarith) hz2.le) (div_nonneg hc0 (nrm_pos k z).le) (mul_nonneg A.2 (Kap_nonneg k _ _))
        _ = _ := by ring
    · simp [hγ]
  have htm_cont x (g : GL2 F) : Continuous fun z : X I => tm D k y.1 y.2 (z, x) g := by
    have h1 v : Continuous fun z : I → P => (z v, D.act g y.2 v) := (continuous_apply v).prodMk continuous_const
    unfold tm qq; dsimp only
    exact continuous_const.mul ((continuous_finsetProd _ fun v _ => (cont_q1 (k v)).comp (h1 v)).mul continuous_const)
  refine ⟨fun x => ⟨continuous_iff_continuousAt.2 fun z₀ => by
        obtain ⟨U, hU, hz₀, M, hM⟩ := hnear x z₀
        exact (continuousOn_tsum (fun γ : PG F => (htm_cont x γ.out).continuousOn) ((hC' ((x : Gf ⧸ D.H) : D.Om) z₀).1.mul_right M)
          fun γ z hz => hM z hz γ).continuousAt (hU.mem_nhds hz₀),
      fun z v t₀ ht₀ => by
        obtain ⟨U, hU, hmem, M, hM⟩ := hnear x (update z v ⟨t₀, ht₀⟩)
        let U' : Set P := (update z v) ⁻¹' U
        have hU' : IsOpen U' := hU.preimage (continuous_const.update v continuous_id)
        let V : Set ℂ := Subtype.val '' U'
        have hV : IsOpen V := isOpen_U.isOpenMap_subtype_val U' hU'
        have htm_hol (γ : PG F) : Hol1 fun t => tm D k y.1 y.2 (update z v t, x) γ.out := by
          have e1 (s : P) : tm D k y.1 y.2 (update z v s, x) γ.out =
              (D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) * (∏ u ∈ Finset.univ.erase v, q1 (k u) (z u) (D.act γ.out y.2 u)) * D.J k γ.out y.2) *
                q1 (k v) s (D.act γ.out y.2 v) := by
            unfold tm qq; dsimp only; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v), update_self]
            rw [Finset.prod_congr rfl fun u hu => by rw [update_of_ne (ne_of_mem_erase hu)]]; ring
          have e : ext1 (fun t => tm D k y.1 y.2 (update z v t, x) γ.out) = fun t => _ * ext1 (fun s => q1 (k v) s (D.act γ.out y.2 v)) t :=
            funext fun t => by unfold ext1; split_ifs with ht; exact e1 _; exact (mul_zero _).symm
          unfold Hol1; rw [e]; exact (hol_q1 (k v) _).const_mul _
        have hd : DifferentiableOn ℂ (fun t => ∑' γ : PG F, ext1 (fun s => tm D k y.1 y.2 (update z v s, x) γ.out) t) V :=
          Complex.differentiableOn_tsum_of_summable_norm ((hC' ((x : Gf ⧸ D.H) : D.Om) (update z v ⟨t₀, ht₀⟩)).1.mul_right M)
            (fun γ => (htm_hol γ).mono (by rintro _ ⟨s, _, rfl⟩; exact s.2)) hV
            (by rintro γ _ ⟨s, hs, rfl⟩; exact (congrArg norm (ext1_of_im _ s.2)).trans_le (hM _ hs γ))
        have hin : t₀ ∈ V := ⟨⟨t₀, ht₀⟩, hmem, rfl⟩
        exact ((hd.differentiableAt (hV.mem_nhds hin)).congr_of_eventuallyEq $ by
          filter_upwards [hV.mem_nhds hin] with t ht; obtain ⟨s, _, rfl⟩ := ht
          exact (ext1_of_im _ s.2).trans (tsum_congr fun γ => (ext1_of_im (fun s => tm D k y.1 y.2 (update z v s, x) γ.out) s.2).symm)).differentiableWithinAt⟩,
    fun γ z x => ?_, fun z x h => ?_, ?_⟩
  · change ∑' δ : PG F, tm D k y.1 y.2 (D.act γ z, D.j γ * x) δ.out = D.J k γ z * ∑' δ : PG F, tm D k y.1 y.2 (z, x) δ.out
    rw [← Equiv.tsum_eq (Equiv.mulLeft (γ : PG F)), ← tsum_mul_left]
    refine tsum_congr fun δ => ?_
    have hmk : ((γ * δ.out : GL2 F) : PG F) = (γ : PG F) * δ := by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have h2 := QuotientGroup.eq.1 (by rw [hmk, QuotientGroup.out_eq'] : (((γ * δ.out : GL2 F) : PG F) = (((γ : PG F) * δ).out : PG F)))
    have heq : tm D k y.1 y.2 (D.act γ z, D.j γ * x) ((γ : PG F) * δ).out = tm D k y.1 y.2 (D.act γ z, D.j γ * x) (γ * δ.out) :=
      (congrArg (tm D k y.1 y.2 _) (show ((γ : PG F) * δ).out = (γ * δ.out) * ((γ * δ.out)⁻¹ * ((γ : PG F) * δ).out) by group)).trans
        (tm_center D k hc _ _ _ _ _ h2)
    refine heq.trans ?_; unfold tm
    rw [show (D.rep y.1)⁻¹ * (D.j (γ * δ.out))⁻¹ * (D.j γ * x) = (D.rep y.1)⁻¹ * (D.j δ.out)⁻¹ * x by rw [map_mul]; group]
    have hqJ : qq k (D.act γ z) (D.act (γ * δ.out) y.2) * D.J k (γ * δ.out) y.2 = D.J k γ z * (qq k z (D.act δ.out y.2) * D.J k δ.out y.2) := by
      simp only [qq, Dat.J, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => by
        change q1 (k v) (D.r v γ • z v) (D.r v (γ * δ.out) • y.2 v) * j1 (k v) (D.r v (γ * δ.out)) (y.2 v) = _
        rw [map_mul, mul_smul, j1_mul, ← mul_assoc, q1_smul, mul_assoc]; rfl
    rw [hqJ]; ring
  · change ∑' δ : PG F, tm D k y.1 y.2 (z, x * h) δ.out = D.χ h * ∑' δ : PG F, tm D k y.1 y.2 (z, x) δ.out
    rw [← tsum_mul_left]; refine tsum_congr fun δ => by
      unfold tm; rw [show (D.rep y.1)⁻¹ * (D.j δ.out)⁻¹ * (x * h) = (D.rep y.1)⁻¹ * (D.j δ.out)⁻¹ * x * h by group, ee_mul_right]; ring
  · refine ⟨C * (cst k * nrm k y.2), fun z x => ?_⟩
    obtain ⟨hs, hle⟩ := hC' ((x : Gf ⧸ D.H) : D.Om) z
    have h1 := tsum_of_norm_bounded (hs.hasSum.mul_right _) fun γ => norm_tm_le D hD k hk1 y γ z x
    have hn := nrm_pos k z
    calc _ ≤ _ * nrm k z := mul_le_mul_of_nonneg_right h1 hn.le
      _ = _ * (cst k * nrm k y.2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hle (mul_nonneg (cst_nonneg k hk1) (nrm_nonneg k _))

theorem kernel_inverse_symmetry : B1a → B1b → B1c → E0a → E0d → KapSum → faceMap_zero_comp_eq_one := by
  intro _ _ _ hE0a _ hKS F I Gf _ _ _ D hAx k hk _ p
  obtain ⟨hcount, -, -, -, -, -, hborel, -⟩ := hE0a F I Gf D hAx
  obtain ⟨c₀, hc₀, hmink⟩ := hAx.mink; obtain ⟨C, hCb⟩ := hKS F I Gf D hAx k hk c₀ hc₀
  let xH : D.Om := (p.2 : Gf ⧸ D.H); let zX : D.Xs := p.1
  obtain ⟨s, hs, hsle⟩ := hmink p.1 (D.rep xH)
  set Bnd := max (C * (1 + D.HtY s (xH, p.1))) 0
  have hT (y : D.Y) : ∑' γ : PG F, ‖tm D k y.1 y.2 p γ.out‖ₑ ≤ oR (cst k / nrm k p.1 * nrm k y.2) * oR Bnd := by
    have hk1 : ∀ v, 1 ≤ k v := fun v => le_trans (by norm_num) (hk v)
    have hle γ : ‖tm D k y.1 y.2 p γ.out‖ₑ ≤ {γ : PG F | γ • y.1 = xH}.indicator
        (fun γ => oR (cst k / nrm k p.1 * nrm k y.2) * oR (Kap k y.2 (γ⁻¹ • zX : D.Xs))) γ := by
      by_cases hγ : γ • y.1 = xH
      · rw [indicator_of_mem (show γ ∈ {γ : PG F | γ • y.1 = xH} from hγ)]
        have h1' : ‖tm D k y.1 y.2 p γ.out‖ ≤ cst k / nrm k p.1 * nrm k y.2 * Kap k y.2 (γ⁻¹ • zX : D.Xs) :=
          (norm_tm_le D hAx k hk1 y γ p.1 p.2).trans_eq $ by
            rw [indicator_of_mem (show γ ∈ {δ : PG F | δ • y.1 = xH} from hγ), ← smulX_out, Kap_swap D k γ p.1 y.2]; ring
        exact (ofReal_norm _).symm.trans_le $ (ENNReal.ofReal_le_ofReal h1').trans_eq
          (ENNReal.ofReal_mul (mul_nonneg (div_nonneg (cst_nonneg k hk1) (nrm_nonneg k _)) (nrm_nonneg k _)))
      · rw [indicator_of_notMem (show γ ∉ {γ : PG F | γ • y.1 = xH} from hγ), tm_supp D k y.1 y.2 γ p.1 p.2 hγ]; simp
    have h1 := ENNReal.tsum_le_tsum hle; rw [← _root_.tsum_subtype, ENNReal.tsum_mul_left] at h1
    let invE : {γ : PG F // γ • y.1 = xH} ≃ {δ : PG F // δ • xH = y.1} :=
      ⟨fun γ => ⟨γ.1⁻¹, by rw [inv_smul_eq_iff, γ.2]⟩, fun δ => ⟨δ.1⁻¹, by rw [inv_smul_eq_iff, δ.2]⟩,
       fun _ => Subtype.ext (inv_inv _), fun _ => Subtype.ext (inv_inv _)⟩
    refine h1.trans $ by
      gcongr
      exact (invE.tsum_eq (fun δ => oR (Kap k y.2 (δ.1 • zX : D.Xs)))).trans_le
        ((hCb (xH, p.1) s hs hsle y.1 y.2).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hsumm (y : D.Y) : Summable fun γ : PG F => ‖tm D k y.1 y.2 p γ.out‖ := by
    simpa only [toReal_enorm] using ENNReal.summable_toReal (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hT y))
  have hc0 : 0 ≤ cst k / nrm k p.1 := div_nonneg (cst_nonneg k fun v => le_trans (by norm_num) (hk v)) (nrm_nonneg k _)
  refine ⟨hsumm, ?_, ⟨cst k / nrm k p.1 * Bnd, fun y => (norm_tsum_le_tsum_norm (hsumm y)).trans ?_⟩⟩
  · have := hcount; have := hborel
    have hTm (γ : PG F) : Measurable (fun y : D.Y => tm D k y.1 y.2 p γ.out) :=
      ((Measurable.of_discrete (f := fun ω : D.Om => D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * p.2))).comp measurable_fst).mul
        (((continuous_finsetProd _ fun v _ => (cont_q1 (k v)).comp (continuous_const.prodMk ((cont_smul_P (D.r v γ.out)).comp (continuous_apply v)))).mul
          (continuous_finsetProd _ fun v _ => (cont_j1 (k v) (D.r v γ.out)).comp (continuous_apply v))).measurable.comp measurable_snd)
    exact measurable_of_tendsto_metrizable' atTop (fun s => Finset.measurable_sum s fun γ _ => hTm γ)
      (tendsto_pi_nhds.2 fun y => (hsumm y).of_norm.hasSum)
  · refine ((tsum_congr fun γ : PG F => (toReal_enorm _).symm).trans (ENNReal.tsum_toReal_eq fun _ => enorm_ne_top).symm).trans_le ?_
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hc0 (le_max_right _ _)) (nrm_nonneg k _)) $
      (hT y).trans_eq ((ENNReal.ofReal_mul (mul_nonneg hc0 (nrm_nonneg k _))).symm.trans (congrArg oR (by ring)))

-- === C3: Inverse series summable ===

theorem inverse_series_summable : C3 := by
  intro G Y _ _ _ _ μ hμ b hb f hf hfi
  let Φ (g : G) (y : Y) := b y • f (g • y)
  let Ψ (g : G) (y : Y) := b (g⁻¹ • y) • f y
  have hΦm g : Measurable (Φ g) := hb.meas.smul (hf.comp (hμ g).measurable)
  have hΨm g : Measurable (Ψ g) := (hb.meas.comp (hμ g⁻¹).measurable).smul hf
  have hhs y : HasSum (fun g : G => b (g⁻¹ • y)) 1 := (Equiv.inv G).hasSum_iff.2 (hb.sum y)
  have hΦl g : ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖Ψ g z‖ₑ ∂μ := by
    rw [← (hμ g).lintegral_comp (hΨm g).enorm]; exact lintegral_congr fun y => by simp [Φ, Ψ]
  have hsumΨ : ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := by
    calc _ = ∑' g, ∫⁻ z, oR (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ := tsum_congr fun g => lintegral_congr fun z => by
              dsimp only [Ψ]; rw [enorm_smul, Real.enorm_eq_ofReal (hb.nonneg _)]
      _ = ∫⁻ z, ∑' g, oR (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
            (lintegral_tsum fun g => ((hb.meas.comp (hμ g⁻¹).measurable).ennreal_ofReal.mul hf.enorm).aemeasurable).symm
      _ = _ := lintegral_congr fun z => by
            rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => hb.nonneg _) (hhs z).summable,
              (hhs z).tsum_eq, ENNReal.ofReal_one, one_mul]
  have hsumΦ : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ ≠ ∞ := by rw [tsum_congr hΦl, hsumΨ]; exact hfi.2.ne
  have hfun : (fun y => b y • ∑' g : G, f (g • y)) = fun y => ∑' g, Φ g y := funext fun y => (tsum_const_smul'' (b y)).symm
  refine ⟨by rw [hfun]; refine ⟨AEStronglyMeasurable.tsum fun g => (hΦm g).aestronglyMeasurable, ?_⟩
             exact ((lintegral_mono fun _ => enorm_tsum_le_tsum_enorm).trans_eq (lintegral_tsum fun g => (hΦm g).enorm.aemeasurable)).trans_lt hsumΦ.lt_top,
    ?_⟩
  rw [hfun, integral_tsum (fun g => (hΦm g).aestronglyMeasurable) hsumΦ,
    tsum_congr fun g => (integral_congr_ae (ae_of_all _ fun y => by simp [Φ, Ψ])).trans ((hμ g).integral_comp (actEquiv hμ g).measurableEmbedding (Ψ g)),
    ← integral_tsum (fun g => (hΨm g).aestronglyMeasurable) (hsumΨ.symm ▸ hfi.2.ne)]
  exact integral_congr_ae (ae_of_all _ fun z => by dsimp only [Ψ]; rw [((hhs z).smul_const (f z)).tsum_eq, one_smul])

-- === B2: Cayley transform ===

def cay (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

lemma im_cay (w : ℂ) : (cay w).im = (1 - normSq w) / normSq (1 - w) := by
  rw [cay, Complex.div_im, normSq_apply w]
  simp only [mul_im, mul_re, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im]; ring

theorem cayley_transform_proof : B2 := by
  intro h h0 hi
  have hS := isOpen_U.measurableSet
  -- Step 1: P -> {t : ℂ | 0 < t.im}
  let U0 : Set ℂ := {t : ℂ | t.im ≠ 0}
  let h' : U0 → ℂ := h
  let g (t : ℂ) : ℂ := ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t
  have h1 : IntegrableOn g {t : ℂ | 0 < t.im} ∧ ∫ z, h z = ∫ t in {t : ℂ | 0 < t.im}, g t := by
    have hρ : Measurable fun z : U0 => oR (1 / z.1.im ^ 2) := by fun_prop
    have hfin : ∀ᵐ z ∂(Measure.comap (Subtype.val : U0 → ℂ) volume), oR (1 / z.1.im ^ 2) < ∞ :=
      ae_of_all _ fun _ => ENNReal.ofReal_lt_top
    have key : (fun z : U0 => (oR (1 / z.1.im ^ 2)).toReal • h' z) = g ∘ Subtype.val := funext fun z => by
      rw [ENNReal.toReal_ofReal (by positivity)]; simp only [g, h', Function.comp_apply, real_smul, ext1_of_im h z.2]; rfl
    have iS : IntegrableOn g U0 := by
      rw [integrableOn_iff_comap_subtypeVal hS, ← key]; exact (integrable_withDensity_iff_integrable_smul' hρ hfin).1 hi
    refine ⟨iS.mono_set fun _ ht => ne_of_gt ht, ?_⟩
    change ∫ z : U0, h' z ∂((Measure.comap Subtype.val volume).withDensity fun z => oR (1 / z.1.im ^ 2)) = _
    rw [integral_withDensity_eq_integral_toReal_smul hρ hfin, key]
    change ∫ z : U0, g z.1 ∂Measure.comap Subtype.val volume = _
    rw [integral_subtype_comap hS g]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS (fun _ ht => ne_of_gt ht) fun t ⟨ht1, ht2⟩ => by
      simp [g, ext1, h0 ⟨t, ht1⟩ (lt_of_le_of_ne (not_lt.1 ht2) ht1)]
  -- Step 2: {0 < t.im} -> ball 0 1 via cay
  have hne1 {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by rintro rfl; simp at hw
  have himg : cay '' ball (0 : ℂ) 1 = {t : ℂ | 0 < t.im} := Set.ext fun t =>
    ⟨by rintro ⟨w, hw, rfl⟩
        have hn : normSq w < 1 := by rw [mem_ball_zero_iff] at hw; rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
        show 0 < (cay w).im; rw [im_cay]; exact div_pos (by linarith) (normSq_pos.2 (sub_ne_zero.2 (hne1 hw).symm)),
     fun (ht : 0 < t.im) => by
      have hd : t + I ≠ 0 := fun h => by have := congrArg im h; simp at this; linarith
      refine ⟨(t - I) / (t + I), ?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 hd), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
          ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]; simp [normSq_apply]; nlinarith
      · have h3 : 1 - (t - I) / (t + I) ≠ 0 := by rw [one_sub_div hd]; simp [hd]
        rw [cay, div_eq_iff h3]; field_simp; ring⟩
  have hinj : InjOn cay (ball (0 : ℂ) 1) := fun a ha b hb hab => by
    have h1 := sub_ne_zero.2 (hne1 ha).symm; have h2 := sub_ne_zero.2 (hne1 hb).symm
    rw [cay, cay, div_eq_div_iff h1 h2] at hab
    simpa [sub_eq_zero] using (show I * (2 * (a - b)) = 0 by linear_combination hab)
  let D w := (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * I / (1 - w) ^ 2)).restrictScalars ℝ
  have hf' w (hw : w ∈ ball (0 : ℂ) 1) : HasFDerivWithinAt cay (D w) (ball 0 1) w := by
    have hd : HasDerivAt cay (2 * I / (1 - w) ^ 2) w :=
      ((((hasDerivAt_id w).const_add 1).const_mul I).div ((hasDerivAt_id w).const_sub 1) (sub_ne_zero.2 (hne1 hw).symm)).congr_deriv (by simp; ring)
    exact (hd.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  let F (w : ℂ) : ℂ := ((4 / (1 - normSq w) ^ 2 : ℝ) : ℂ) * ext1 h (cay w)
  have hpt2 : EqOn (fun w => |(D w).det| • g (cay w)) F (ball 0 1) := fun w hw => by
    have hn : normSq w < 1 := by rw [mem_ball_zero_iff] at hw; rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    have h1w : 0 < normSq (1 - w) := normSq_pos.2 (sub_ne_zero.2 (hne1 hw).symm)
    have hdet : |(D w).det| = 4 / normSq (1 - w) ^ 2 := by
      rw [show (D w).det = normSq (2 * I / (1 - w) ^ 2) by simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq],
        abs_of_nonneg (normSq_nonneg _), map_div₀, map_pow, map_mul]; simp [normSq_apply]; norm_num
    simp only [hdet, g, F, real_smul, im_cay, ← mul_assoc, ← ofReal_mul]; congr 2; field_simp
  have h2 : IntegrableOn F (ball 0 1) ∧ ∫ t in {t : ℂ | 0 < t.im}, g t = ∫ w in ball (0 : ℂ) 1, F w := by
    rw [← himg] at h1 ⊢
    exact ⟨((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_ball hf' hinj g).1 h1.1).congr_fun hpt2 measurableSet_ball,
      by rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball hf' hinj]; exact setIntegral_congr_fun measurableSet_ball hpt2⟩
  -- Step 3: ball 0 1 -> Ioo 0 1 ×ˢ Ioo (-π) π via polarCoord
  let S := Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π
  have hSm : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have hsub : polarCoord.symm '' S ⊆ measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    rintro _ ⟨p, hp', rfl⟩
    simp only [Set.mem_preimage, mem_ball_zero_iff, measurableEquivRealProd_symm_polarCoord_symm_apply, norm_polarCoord_symm, abs_of_pos hp'.1.1]; exact hp'.1.2
  have hae : polarCoord.symm '' S =ᵐ[volume] measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    filter_upwards [polarCoord_source_ae_eq_univ] with q hq
    have hq' : q ∈ polarCoord.source := by rw [hq]; trivial
    refine propext ⟨fun h => hsub h, fun hqT => ⟨polarCoord q, ⟨⟨(polarCoord.map_source hq').1, ?_⟩, (polarCoord.map_source hq').2⟩, polarCoord.left_inv hq'⟩⟩
    change measurableEquivRealProd.symm q ∈ ball (0 : ℂ) 1 at hqT
    rw [mem_ball_zero_iff, show ‖measurableEquivRealProd.symm q‖ = √(q.1 ^ 2 + q.2 ^ 2) by
      change ‖equivRealProd.symm q‖ = _; rw [equivRealProd_symm_apply, Complex.norm_def, normSq_add_mul_I]] at hqT
    simpa using hqT
  have hG' := ((hp.integrableOn_comp_preimage measurableEquivRealProd.symm.measurableEmbedding).2 h2.1).mono_set hsub
  have hder : ∀ p ∈ S, HasFDerivWithinAt polarCoord.symm (fderivPolarCoordSymm p) S p := fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt
  have hinj3 : InjOn polarCoord.symm S := polarCoord.symm.injOn.mono fun p hp => show p.1 ∈ Ioi (0 : ℝ) ∧ p.2 ∈ Ioo (-π) π from ⟨hp.1.1, hp.2⟩
  have hpt3 : EqOn (fun p : ℝ × ℝ => |(fderivPolarCoordSymm p).det| • (F ∘ measurableEquivRealProd.symm) (polarCoord.symm p))
      (fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) * ext1 h (cay (circleMap 0 p.1 p.2))) S := by
    rintro ⟨r, θ⟩ ⟨hr, _⟩
    simp only [det_fderivPolarCoordSymm, abs_of_pos hr.1, Function.comp_apply, measurableEquivRealProd_symm_polarCoord_symm_apply,
      Complex.polarCoord_symm_apply, real_smul, F, show (r : ℂ) * (Real.cos θ + Real.sin θ * I) = circleMap 0 r θ by
        rw [circleMap, zero_add, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin],
      show normSq (circleMap 0 r θ) = r ^ 2 by rw [normSq_eq_norm_sq, norm_circleMap_zero, abs_of_pos hr.1]]
    push_cast; ring
  refine ⟨((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hSm hder hinj3 _).1 hG').congr_fun hpt3 hSm, ?_⟩
  rw [h1.2, h2.2, ← hp.setIntegral_preimage_emb measurableEquivRealProd.symm.measurableEmbedding F (ball 0 1),
    ← setIntegral_congr_set hae, integral_image_eq_integral_abs_det_fderiv_smul volume hSm hder hinj3]
  exact setIntegral_congr_fun hSm hpt3

end UpperTheory.Esk
