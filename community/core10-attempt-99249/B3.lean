import B2

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup Topology Metric
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === B3: 1D Reproducing formula ===

theorem reproducing_formula_proof : B1a → B1b → B1c → B2 → B6 → B3 := by
  intro _ _ _ hB2 hB6 k hk f hf ⟨C, hC⟩ z
  have cont_of_hol {g : P → ℂ} (hg : Hol1 g) : Continuous g := by
    have h1 : Continuous fun w : P => ext1 g w.1 := hg.continuousOn.comp_continuous continuous_subtype_val fun w => w.2
    exact h1.congr fun w => ext1_coe g w
  have hint {g : P → ℂ} (hc : Continuous g) {C' : ℝ} (hC' : ∀ w : P, ‖g w‖ * |w.1.im| ^ ((k : ℝ) / 2) ≤ C') (w0 : P) :
      Integrable fun w => q1 k w0 w * g w := by
    obtain ⟨C6, hC6⟩ := hB6 k hk
    have hki : Integrable fun w => kap w0 w ^ ((k : ℝ) / 2) :=
      ⟨((cont_kap.comp (continuous_const.prodMk continuous_id)).rpow_const fun _ => Or.inr (by positivity)).aestronglyMeasurable,
        by rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun w => rpow_nonneg (kap_nonneg _ _) _)]; exact (hC6 w0).1.trans_lt ENNReal.coe_lt_top⟩
    have hA : 0 ≤ ((k : ℝ) - 1) / (4 * π) := div_nonneg (by have : (4 : ℝ) ≤ k := (by exact_mod_cast hk); linarith) (by positivity)
    have hze : 0 < |w0.1.im| ^ ((k : ℝ) / 2) := rpow_pos_of_pos (abs_pos.2 w0.2) _
    refine (hki.const_mul (((k : ℝ) - 1) / (4 * π) * C' / |w0.1.im| ^ ((k : ℝ) / 2))).mono'
      (((cont_q1 k).comp (continuous_const.prodMk continuous_id)).mul hc).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    have hq : ‖q1 k w0 w‖ = ((k : ℝ) - 1) / (4 * π) * kap w0 w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) / |w0.1.im| ^ ((k : ℝ) / 2) :=
      (eq_div_iff hze.ne').2 (norm_q1 k w0 w (by omega))
    rw [norm_mul, hq]
    calc _ = (((k : ℝ) - 1) / (4 * π) * kap w0 w ^ ((k : ℝ) / 2) / |w0.1.im| ^ ((k : ℝ) / 2)) * (‖g w‖ * |w.1.im| ^ ((k : ℝ) / 2)) := by ring
      _ ≤ _ * C' := mul_le_mul_of_nonneg_left (hC' w) (div_nonneg (mul_nonneg hA (rpow_nonneg (kap_nonneg _ _) _)) hze.le)
      _ = _ := by ring
  refine ⟨hint (cont_of_hol hf) hC z, ?_⟩
  obtain ⟨g, -, -, rfl⟩ := trans_iP z
  let f' (w : P) := f (g • w) / j1 k g w
  have hf' : Hol1 f' := by
    have hc0 : ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne'
    have hmob : DifferentiableOn ℂ (fun t => num g t / den g t) {t : ℂ | t.im ≠ 0} := fun t ht =>
      ((by unfold num; fun_prop : Differentiable ℂ (num g)) t |>.div ((by unfold den; fun_prop : Differentiable ℂ (den g)) t) (den_ne g ht)).differentiableWithinAt
    have h1 : DifferentiableOn ℂ (fun t => ext1 f (num g t / den g t) / (den g t ^ k * ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ))) {t | t.im ≠ 0} :=
      (hf.comp hmob fun t ht => let w : P := ⟨t, ht⟩; (g • w).2).div
        (fun t _ => ((((by unfold den; fun_prop : Differentiable ℂ (den g)) t).pow k).mul_const _).differentiableWithinAt)
        fun t ht => mul_ne_zero (pow_ne_zero _ (den_ne g ht)) hc0
    exact h1.congr fun t ht => by
      let w : P := ⟨t, ht⟩
      rw [ext1_of_im _ ht]; show f (g • w) / j1 k g w = _; rw [← ext1_coe f (g • w), coe_smul]; rfl
  have hC' (w : P) : ‖f' w‖ * |w.1.im| ^ ((k : ℝ) / 2) ≤ C := by
    have hj : ‖j1 k g w‖ ≠ 0 := norm_ne_zero_iff.2 (j1_ne k g w)
    calc ‖f (g • w) / j1 k g w‖ * |w.1.im| ^ ((k : ℝ) / 2) = ‖f (g • w)‖ * |(g • w).1.im| ^ ((k : ℝ) / 2) := by
          rw [← norm_j1 k g w, norm_div]; field_simp
      _ ≤ C := hC _
  have hat_i : ∫ w, q1 k iP w * f' w = f' iP := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hvan (w : P) (hw : w.1.im < 0) : q1 (m + 2) iP w * f' w = 0 := by
      unfold q1; rw [ite_eq_right (by show ¬(0 < I.im * w.1.im); simp; linarith), zero_mul]
    obtain ⟨hIO, heq⟩ := hB2 (fun w => q1 (m + 2) iP w * f' w) hvan (hint (cont_of_hol hf') hC' iP)
    rw [heq]
    have hdisc {s : ℂ} (hs : ‖s‖ < 1) : 1 - s ≠ 0 ∧ 0 < (cay s).im := by
      have h1 : 1 - s ≠ 0 := fun h => by have : s = 1 := (by linear_combination -h); rw [this, norm_one] at hs; exact lt_irrefl _ hs
      exact ⟨h1, by rw [im_cay]; exact div_pos (by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg s]) (normSq_pos.2 h1)⟩
    have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
    have hpt : EqOn (fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) * ext1 (fun w => q1 (m + 2) iP w * f' w) (cay (circleMap 0 p.1 p.2)))
        (fun p : ℝ × ℝ => ((((m : ℝ) + 1) / π * p.1 * (1 - p.1 ^ 2) ^ m : ℝ) : ℂ) * (ext1 f' (cay (circleMap 0 p.1 p.2)) / (1 - circleMap 0 p.1 p.2) ^ (m + 2)))
        (Set.Ioo 0 1 ×ˢ Set.Ioo (-π) π) := by
      rintro ⟨r, θ⟩ ⟨⟨hr0, hr1⟩, _⟩; dsimp only
      set s := circleMap 0 r θ; set w := cay s
      have hns : ‖s‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr0]
      obtain ⟨h1s, hwim⟩ := hdisc (hns.symm ▸ hr1)
      have hcs : s * conj s = (r : ℂ) ^ 2 := by rw [Complex.mul_conj, normSq_eq_norm_sq, hns]; push_cast; ring
      have h1c : 1 - conj s ≠ 0 := fun h => h1s (by simpa using congrArg conj h)
      have hcw : conj w = -I * (1 + conj s) / (1 - conj s) := by simp [w, cay]
      have hratio : (w - conj w) / (I - conj w) = (1 - (r : ℂ) ^ 2) / (1 - s) := by
        have hI := I_ne_zero
        rw [show w - conj w = 2 * I * (1 - s * conj s) / ((1 - s) * (1 - conj s)) by rw [hcw]; simp only [w, cay]; field_simp; ring,
          show I - conj w = 2 * I / (1 - conj s) by rw [hcw]; field_simp; ring, hcs]; field_simp
      rw [ext1_of_im _ hwim.ne', ext1_of_im f' hwim.ne']
      have hqi : q1 (m + 2) iP ⟨w, hwim.ne'⟩ = (((m + 2 : ℕ) : ℂ) - 1) / (4 * π) * ((w - conj w) / (I - conj w)) ^ (m + 2) := by
        unfold q1; rw [ite_eq_left (by simpa [iP] using hwim)]; rfl
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
      have hr2 : (1 - (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by nlinarith : (1 - r ^ 2 : ℝ) ≠ 0)
      rw [hqi, hratio, div_pow]
      have hkey : ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * ((((m + 2 : ℕ) : ℂ) - 1) / (4 * π)) * (1 - (r : ℂ) ^ 2) ^ (m + 2) =
          ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) := by push_cast; field_simp; ring
      rw [← hkey]; ring
    change ∫ p : ℝ × ℝ in Set.Ioo 0 1 ×ˢ Set.Ioo (-π) π, ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) * ext1 (fun w => q1 (m + 2) iP w * f' w) (cay (circleMap 0 p.1 p.2)) = f' iP
    rw [setIntegral_congr_fun hS hpt, Measure.volume_eq_prod, setIntegral_prod _ (by rw [← Measure.volume_eq_prod]; exact hIO.congr_fun hpt hS)]
    let G (s : ℂ) := ext1 f' (cay s) / (1 - s) ^ (m + 2)
    have hGd : DifferentiableOn ℂ G (ball 0 1) :=
      (hf'.comp (fun s hs => (DifferentiableAt.div (by fun_prop) (by fun_prop) (hdisc (mem_ball_zero_iff.1 hs)).1).differentiableWithinAt)
        fun s hs => (hdisc (mem_ball_zero_iff.1 hs)).2.ne').div
        (fun s _ => (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => (1 - s) ^ (m + 2)) s).differentiableWithinAt)
        fun s hs => pow_ne_zero _ (hdisc (mem_ball_zero_iff.1 hs)).1
    have hin r (hr : r ∈ Ioo (0 : ℝ) 1) :
        ∫ θ in Ioo (-π) π, ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) * G (circleMap 0 r θ) =
          ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) * (2 * (π : ℂ) * f' iP) := by
      rw [integral_const_mul]; congr 1
      have h1 := (show DiffContOnCl ℂ G (ball 0 |r|) by
        rw [abs_of_pos hr.1]; exact (hGd.mono (by rw [closure_ball 0 hr.1.ne']; exact closedBall_subset_ball hr.2)).diffContOnCl).circleAverage
      have hper : Periodic (fun θ => G (circleMap 0 r θ)) (2 * π) := fun θ => by show G (circleMap 0 r (θ + 2 * π)) = _; rw [periodic_circleMap]
      have h2 := hper.intervalIntegral_add_eq (-π) 0; rw [show -π + 2 * π = π by ring, zero_add] at h2
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]), h2]
      rw [Real.circleAverage_def, real_smul, show G 0 = f' iP by simp [G, cay]; exact ext1_coe f' iP] at h1
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
      rw [← h1]; push_cast; field_simp
    have hrad : ∫ r in Ioo (0 : ℝ) 1, ((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m = 1 / (2 * π) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
      have hd x (_ : x ∈ uIcc (0 : ℝ) 1) : HasDerivAt (fun r : ℝ => -(1 - r ^ 2) ^ (m + 1) / (2 * π)) (((m : ℝ) + 1) / π * x * (1 - x ^ 2) ^ m) x :=
        ((((by simpa using (hasDerivAt_pow 2 x).const_sub 1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * x)) x).pow (m + 1)).neg.div_const (2 * π)).congr_deriv $ by
          have := pi_ne_zero; simp only [Nat.add_sub_cancel]; push_cast; field_simp)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((by fun_prop : Continuous fun x : ℝ => ((m : ℝ) + 1) / π * x * (1 - x ^ 2) ^ m).intervalIntegrable 0 1)]; simp; ring
    rw [setIntegral_congr_fun measurableSet_Ioo hin, integral_mul_const, integral_complex_ofReal, hrad]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    push_cast; field_simp
  let e : P ≃ₜ P := ⟨MulAction.toPerm g, cont_smul_P g, cont_smul_P g⁻¹⟩
  rw [← (mp_smul_P g).integral_comp e.measurableEmbedding (fun w => q1 k (g • iP) w * f w)]
  have hpt w : q1 k (g • iP) (g • w) * f (g • w) = j1 k g iP * (q1 k iP w * f' w) := by
    have hj := j1_ne k g w
    calc _ = (q1 k (g • iP) (g • w) * j1 k g w) * f (g • w) / j1 k g w := by field_simp
      _ = (j1 k g iP * q1 k iP w) * f (g • w) / j1 k g w := by rw [q1_smul]
      _ = _ := by unfold f'; ring
  simp_rw [hpt]; rw [integral_const_mul, hat_i]; have := j1_ne k g iP; unfold f'; field_simp

-- === MultivariableReproducingFormula ===

theorem multivariable_reproducing_formula_proof : B1a → B1b → B3 → KapInt → MultivariableReproducingFormula := by
  intro ha _ h3 hK I _ k hk f hf ⟨C, hC⟩ z
  have : SigmaFinite (volume : Measure P) := ha.1
  have hint {J : Type} [Fintype J] (k' : J → ℕ) (hk' : ∀ v, 4 ≤ k' v) (g : X J → ℂ) (hg : Continuous g) (C' : ℝ)
      (hC' : ∀ w, ‖g w‖ * nrm k' w ≤ C') (w0 : X J) : Integrable fun w => qq k' w0 w * g w := by
    obtain ⟨C1, _, h⟩ := hK J k' hk'; obtain ⟨hm, hl, -⟩ := h w0
    have hKi : Integrable (Kap k' w0) := ⟨hm.aestronglyMeasurable, by
      show ∫⁻ w, ‖Kap k' w0 w‖ₑ < ∞; simp_rw [Real.enorm_eq_ofReal (Kap_nonneg k' w0 _)]; exact hl.trans_lt ENNReal.coe_lt_top⟩
    have hc := cst_nonneg k' fun v => le_trans (by norm_num) (hk' v)
    have hqc : Continuous (qq k' w0) := continuous_finsetProd _ fun v _ => (cont_q1 (k' v)).comp (continuous_const.prodMk (continuous_apply v))
    refine (hKi.const_mul (cst k' * C' / nrm k' w0)).mono' (hqc.mul hg).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [norm_mul, div_mul_eq_mul_div, le_div_iff₀ (nrm_pos k' w0)]
    calc ‖qq k' w0 w‖ * ‖g w‖ * nrm k' w0 = (‖qq k' w0 w‖ * nrm k' w0) * ‖g w‖ := by ring
      _ = cst k' * Kap k' w0 w * (‖g w‖ * nrm k' w) := by rw [norm_qq k' (fun v => le_trans (by norm_num) (hk' v))]; ring
      _ ≤ cst k' * Kap k' w0 w * C' := mul_le_mul_of_nonneg_left (hC' w) (mul_nonneg hc (Kap_nonneg k' _ _))
      _ = _ := by ring
  refine ⟨hint k hk f hf.1 C hC z, ?_⟩
  have hfin : ∀ (n : ℕ) (k' : Fin n → ℕ), (∀ v, 4 ≤ k' v) → ∀ g : X (Fin n) → ℂ, SepHol g →
      ∀ C', (∀ w, ‖g w‖ * nrm k' w ≤ C') → ∀ w0, ∫ w, qq k' w0 w * g w = g w0 := by
    intro n; induction n with
    | zero =>
      intro k' _ g _ _ _ w0
      rw [show (fun w => qq k' w0 w * g w) = fun _ => g w0 from funext fun w => by rw [Subsingleton.elim w w0]; simp [qq],
        show (volume : Measure (X (Fin 0))) = Measure.dirac w0 from Measure.pi_of_empty _ w0, integral_const]; simp
    | succ n ih =>
      intro k' hk' g hg C' hC' w0
      have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure P)) 0
      have hsymm (p : P × (Fin n → P)) : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p = Fin.cons p.1 p.2 :=
        funext fun j => by induction j using Fin.cases <;> simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
      have hqqc t w : qq k' w0 (Fin.cons t w) = q1 (k' 0) (w0 0) t * qq (fun j => k' j.succ) (fun j => w0 j.succ) w := by
        simp only [qq, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hnrmc t w : nrm k' (Fin.cons t w : X (Fin (n + 1))) = |t.1.im| ^ ((k' 0 : ℝ) / 2) * nrm (fun j => k' j.succ) w := by
        simp only [nrm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hG : Integrable (fun p : P × (Fin n → P) => q1 (k' 0) (w0 0) p.1 * qq (fun j => k' j.succ) (fun j => w0 j.succ) p.2 * g (Fin.cons p.1 p.2))
          ((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) :=
        ((hmp.symm.integrable_comp_emb (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm.measurableEmbedding).2
          (hint k' hk' g hg.1 C' hC' w0)).congr (ae_of_all _ fun p => by simp only [Function.comp_apply, hsymm, hqqc])
      have hin (w : Fin n → P) : ∫ t, q1 (k' 0) (w0 0) t * qq (fun j => k' j.succ) (fun j => w0 j.succ) w * g (Fin.cons t w) =
          qq (fun j => k' j.succ) (fun j => w0 j.succ) w * g (Fin.cons (w0 0) w) := by
        have hol : Hol1 fun t => g (Fin.cons t w) := by
          convert hg.2 (Fin.cons (w0 0) w) 0 using 3 with t; funext j; induction j using Fin.cases <;> simp
        have hbd : ∃ C'', ∀ t : P, ‖g (Fin.cons t w)‖ * |t.1.im| ^ ((k' 0 : ℝ) / 2) ≤ C'' :=
          ⟨C' / nrm (fun j => k' j.succ) w, fun t => by rw [le_div_iff₀ (nrm_pos _ _), mul_assoc, ← hnrmc]; exact hC' _⟩
        rw [show (fun t => q1 (k' 0) (w0 0) t * qq (fun j => k' j.succ) (fun j => w0 j.succ) w * g (Fin.cons t w)) =
          fun t => qq (fun j => k' j.succ) (fun j => w0 j.succ) w * (q1 (k' 0) (w0 0) t * g (Fin.cons t w)) from funext fun _ => by ring,
          integral_const_mul, (h3 (k' 0) (hk' 0) _ hol hbd (w0 0)).2]
      have hsep : SepHol fun w : X (Fin n) => g (Fin.cons (w0 0) w) :=
        ⟨hg.1.comp (continuous_pi fun j => by induction j using Fin.cases; simpa using continuous_const; simpa using continuous_apply _),
         fun w v => by
          convert hg.2 (Fin.cons (w0 0) w) v.succ using 3 with t; funext j
          induction j using Fin.cases with
          | zero => simp [(Fin.succ_ne_zero v).symm]
          | succ j => simp only [Fin.cons_succ, update_apply, Fin.succ_inj]; split_ifs <;> simp_all⟩
      calc ∫ w, qq k' w0 w * g w
          = ∫ p : P × (Fin n → P), q1 (k' 0) (w0 0) p.1 * qq (fun j => k' j.succ) (fun j => w0 j.succ) p.2 * g (Fin.cons p.1 p.2)
              ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) :=
            (hmp.symm.integral_comp' _).symm.trans (integral_congr_ae (ae_of_all _ fun p => by simp only [hsymm, hqqc]))
        _ = ∫ w : X (Fin n), qq (fun j => k' j.succ) (fun j => w0 j.succ) w * g (Fin.cons (w0 0) w) :=
            (integral_prod_symm _ hG).trans (integral_congr_ae (ae_of_all _ hin))
        _ = g (Fin.cons (w0 0) fun j => w0 j.succ) := ih _ (fun _ => hk' _) _ hsep (C' / |(w0 0).1.im| ^ ((k' 0 : ℝ) / 2))
            (fun w => by rw [le_div_iff₀ (rpow_pos_of_pos (abs_pos.2 (w0 0).2) _), mul_assoc, mul_comm (nrm _ _), ← hnrmc]; exact hC' _) _
        _ = g w0 := congrArg g (Fin.cons_self_tail w0)
  let σ := Fintype.equivFin I
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => P) σ
  have hφ (w : X I) j : φ w j = w (σ.symm j) := by
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card I) => P) σ w (σ.symm j)
    rw [Equiv.apply_symm_apply] at this; exact this
  have hmp : MeasurePreserving φ volume volume := measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card I) => (volume : Measure P)) σ
  have hsep : SepHol fun w' : X (Fin (Fintype.card I)) => f fun i => w' (σ i) :=
    ⟨hf.1.comp (continuous_pi fun i => continuous_apply _), fun w' j => by
      convert hf.2 (fun i => w' (σ i)) (σ.symm j) using 3 with t
      funext i; simp only [update_apply, Equiv.eq_symm_apply]; split_ifs <;> rfl⟩
  have hbd w' : ‖f fun i => w' (σ i)‖ * nrm (fun j => k (σ.symm j)) w' ≤ C := by
    rw [show nrm (fun j => k (σ.symm j)) w' = nrm k fun i => w' (σ i) from Fintype.prod_equiv σ.symm _ _ fun _ => by simp]; exact hC _
  calc ∫ w, qq k z w * f w
      = ∫ w, (fun w' : X (Fin (Fintype.card I)) => qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i)) (φ w) :=
        integral_congr_ae (ae_of_all _ fun w => by
          simp only [hφ, Equiv.symm_apply_apply, show qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) (φ w) = qq k z w from
            by simp only [qq, hφ]; exact Fintype.prod_equiv σ.symm _ _ fun _ => rfl])
    _ = ∫ w', qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i) :=
        hmp.integral_comp' (fun w' : Fin (Fintype.card I) → P => qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i))
    _ = f z := by rw [hfin _ _ (fun _ => hk _) _ hsep C hbd _]; simp

-- === E5: Reproducing kernel expansion ===

theorem e5_of_reproducing_formula : B1b → C3 → E0a → faceMap_zero_comp_eq_one → MultivariableReproducingFormula → E5 := by
  intro _ hC3 hE0 _ hB3 F I Gf _ _ _ D hAx k hk _ b hb f hf ⟨z, x⟩
  obtain ⟨hcount, hsf, -, hpres, -, -, hborel, -⟩ := hE0 F I Gf D hAx
  have := hcount; have := hsf; have := hborel; have := hAx.cO
  have hrep_eq (ω : D.Om) (u : Gf) (hu : (u : Gf ⧸ D.H) = ω) : ∃ h : D.H, D.rep ω = u * h :=
    ⟨⟨u⁻¹ * D.rep ω, QuotientGroup.eq.1 (hu.trans (rep_spec D ω).symm)⟩, by simp⟩
  have hee (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) * (D.χ h : ℂ) = D.ee u := by
    rw [ee_inv_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  let ω₀ : D.Om := (x : Gf ⧸ D.H)
  let a : D.Om → ℂ := ({ω₀} : Set D.Om).indicator fun _ => 1
  let h0 : D.Xs → ℂ := fun w => qq k z w * f (w, x)
  let G : D.Y → ℂ := fun y => D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1))
  have hG : G = fun y => a y.1 * h0 y.2 := funext fun y => by
    let w : X I := y.2
    change D.ee ((D.rep y.1)⁻¹ * x) * (qq k z w * f (w, D.rep y.1)) = a y.1 * h0 y.2
    by_cases hy : y.1 = ω₀
    · obtain ⟨h, hh⟩ := hrep_eq y.1 x hy.symm
      rw [show a y.1 = 1 by simp [a, hy], one_mul, hh, hf.lev, show (x * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ by group]
      have he := hee h 1; rw [mul_one, ee_one] at he
      calc _ = (D.ee (h : Gf)⁻¹ * (D.χ h : ℂ)) * h0 y.2 := by unfold h0; ring
        _ = h0 y.2 := by rw [he, one_mul]
    · have hn : (D.rep y.1)⁻¹ * x ∉ D.H := fun hm => hy ((rep_spec D y.1).symm.trans (QuotientGroup.eq.2 hm))
      simp [a, hy, Dat.ee, hn]
  have hB := hB3 I k hk (fun w => f (w, x)) (hf.hol x) (let ⟨C, hC⟩ := hf.bdd; ⟨C, fun w => hC w x⟩) z
  have hqc : Continuous (qq k z) := continuous_finsetProd _ fun v _ => (cont_q1 (k v)).comp (continuous_const.prodMk (continuous_apply v))
  have hai : Integrable a Measure.count :=
    (integrable_indicator_iff MeasurableSet.of_discrete).2 ((integrableOn_singleton_iff (by simp)).2 (Or.inr (by simp)))
  have hKf (y : D.Y) : D.Kern k y (z, x) * f (y.2, D.rep y.1) = ∑' γ : PG F, G (γ • y) := by
    unfold Dat.Kern; rw [← tsum_mul_right]; refine tsum_congr fun γ => ?_
    obtain ⟨h, hh⟩ := hrep_eq (γ • y).1 (D.j γ.out * D.rep y.1) (by rw [Prod.smul_fst, smulO_out])
    let w : X I := y.2
    have hsm : (γ • y).2 = D.act γ.out w := by rw [Prod.smul_snd, smulX_out]
    change D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) * (qq k z (D.act γ.out w) * D.J k γ.out w) * f (w, D.rep y.1) =
      D.ee ((D.rep (γ • y).1)⁻¹ * x) * (qq k z (γ • y).2 * f ((γ • y).2, D.rep (γ • y).1))
    rw [hh, hsm, hf.lev, hf.aut,
      show (D.j γ.out * D.rep y.1 * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ * ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) by group,
      ← hee h ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x)]; ring
  calc ∫ y, b y • (D.Kern k y (z, x) * f (y.2, D.rep y.1)) ∂D.μY
      = ∫ y, b y • ∑' γ : PG F, G (γ • y) ∂D.μY := by simp_rw [hKf]
    _ = ∫ y, G y ∂D.μY := (hC3 (PG F) D.Y D.μY hpres b hb G
          (by rw [hG]; exact ((measurable_const.indicator MeasurableSet.of_discrete).comp measurable_fst).mul ((hqc.mul (hf.hol x).1).measurable.comp measurable_snd))
          (by rw [hG]; exact hai.mul_prod hB.1)).2
    _ = (∫ ω, a ω ∂Measure.count) * ∫ w, h0 w := by rw [hG]; exact integral_prod_mul a h0
    _ = f (z, x) := by
        rw [show ∫ ω, a ω ∂Measure.count = 1 by
          rw [show a = ({ω₀} : Set D.Om).indicator fun _ => (1 : ℂ) from rfl, integral_indicator MeasurableSet.of_discrete,
            setIntegral_const, Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul], one_mul]
        exact hB.2

-- === LinTr & E6 ===

theorem pf_LinTr : LinTr := by
  intro A Y _ ν _ V _ T K ev n _ hn hK hev hKb hevb hrep
  have hbm {g h : Y → ℂ} {C D : ℝ} (hC : ∀ y, ‖g y‖ ≤ C * n y) (hD : ∀ y, ‖h y‖ * n y ≤ D) y : ‖g y * h y‖ ≤ C * D := by
    have hC0 : 0 ≤ C := by by_contra hneg; have : C * n y < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) (hn y); linarith [norm_nonneg (g y), hC y]
    rw [norm_mul]; calc ‖g y‖ * ‖h y‖ ≤ C * n y * ‖h y‖ := mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)
      _ = C * (‖h y‖ * n y) := by ring
      _ ≤ C * D := mul_le_mul_of_nonneg_left (hD y) hC0
  have hintm {g h : Y → ℂ} (hg : Measurable g) (hh : Measurable h) {C D : ℝ} (hC : ∀ y, ‖g y‖ ≤ C * n y) (hD : ∀ y, ‖h y‖ * n y ≤ D) :
      Integrable (fun y => g y * h y) ν :=
    (integrable_const (C * D)).mono' (hg.mul hh).aestronglyMeasurable (ae_of_all _ fun y => hbm hC hD y)
  let evl (a : A) : Module.Dual ℂ V := (LinearMap.proj a : (A → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype
  have hspan : Submodule.span ℂ (range evl) = ⊤ := by
    by_contra h
    obtain ⟨φ, hφ0, hφk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ V).surjective φ
    have hv : v = 0 := Subtype.ext $ funext fun a => LinearMap.mem_ker.1 (hφk (Submodule.subset_span ⟨a, rfl⟩))
    exact hφ0 (by rw [hv, map_zero])
  let Good (φ : Module.Dual ℂ V) : Prop :=
    Measurable (fun y => φ (K y)) ∧ (∃ C, ∀ y, ‖φ (K y)‖ ≤ C * n y) ∧ ∀ f : V, ∫ y, φ (K y) * f.1 (ev y) ∂ν = φ f
  have hgood (φ : Module.Dual ℂ V) : Good φ := by
    let Sg : Submodule ℂ (Module.Dual ℂ V) :=
      { carrier := {ψ | Good ψ}
        zero_mem' := ⟨by simp, ⟨0, fun _ => by simp⟩, fun _ => by simp⟩
        add_mem' := fun {φ₁ φ₂} h₁ h₂ =>
          let ⟨C₁, hC₁⟩ := h₁.2.1; let ⟨C₂, hC₂⟩ := h₂.2.1
          ⟨h₁.1.add h₂.1, ⟨C₁ + C₂, fun y => by rw [LinearMap.add_apply, add_mul]; exact (norm_add_le _ _).trans (add_le_add (hC₁ y) (hC₂ y))⟩,
           fun f => let ⟨D, hD⟩ := hevb f; by
             simp only [LinearMap.add_apply, add_mul]
             rw [integral_add (hintm h₁.1 (hev f) hC₁ hD) (hintm h₂.1 (hev f) hC₂ hD), h₁.2.2 f, h₂.2.2 f]⟩
        smul_mem' := fun c ψ h => let ⟨C, hC⟩ := h.2.1
          ⟨h.1.const_mul c, ⟨‖c‖ * C, fun y => by rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)⟩,
           fun f => by simp only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]; rw [integral_const_mul, h.2.2 f]⟩ }
    have htop : Sg = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]; rintro _ ⟨a, rfl⟩; exact ⟨hK a, hKb a, fun f => hrep f a⟩
    exact show φ ∈ Sg from htop.symm ▸ Submodule.mem_top
  let b := Module.finBasis ℂ V
  have hexp y : (T (K y)).1 (ev y) = ∑ i, b.coord i (K y) * (T (b i)).1 (ev y) := by
    have e : T (K y) = ∑ i, b.repr (K y) i • T (b i) :=
      (congrArg T (b.sum_repr (K y)).symm).trans $ by rw [map_sum]; exact Finset.sum_congr rfl fun _ _ => map_smul T _ _
    rw [e]; simp [Module.Basis.coord_apply]
  choose Cs hCs using fun i => (hgood (b.coord i)).2.1
  choose Ds hDs using fun i => hevb (T (b i))
  refine ⟨by simp_rw [hexp]; exact Finset.measurable_sum _ fun i _ => (hgood (b.coord i)).1.mul (hev (T (b i))),
    ⟨∑ i, Cs i * Ds i, fun y => by rw [hexp]; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbm (hCs i) (hDs i) y)⟩, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b T, Matrix.trace]; simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => hintm (hgood (b.coord i)).1 (hev (T (b i))) (hCs i) (hDs i)]
  exact Finset.sum_congr rfl fun i _ => by rw [(hgood (b.coord i)).2.2 (T (b i))]; simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

theorem e6_of_linear_trace_identity : E0a → FormsStableUnderOperators → KernelTermsInvariantBounded → E3 → E4 → faceMap_zero_comp_eq_one → E5 → LinTr → E6 := by
  intro _ _ _ hE3 hE4 hE4b hE5 _ F I Gf ι _ _ _ _ D k a hH hfd h b hb
  have hE4' := hE4 F I Gf D hH.ax k hH.four hH.compat
  have hE4b' := hE4b F I Gf D hH.ax k hH.four hH.compat
  have hbm : Measurable fun y => (b y).toNNReal := hb.meas.real_toNNReal
  let ν : Measure D.Y := D.μY.withDensity fun y => ((b y).toNNReal : ℝ≥0∞)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity (hE3 F I Gf D hH.ax b hb).ne
  have hint (g : D.Y → ℂ) : ∫ y, g y ∂ν = ∫ y, b y • g y ∂D.μY :=
    (integral_withDensity_eq_integral_smul hbm _).trans $ integral_congr_ae $ ae_of_all _ fun y => by simp [NNReal.smul_def, coe_toNNReal _ (hb.nonneg y)]
  let K : D.Y → D.M k := fun y => ⟨D.Kern k y, (isForm_sub D k _).2 (hE4' y)⟩
  have hn_meas : Measurable fun y : D.Y => nrm k y.2 := by
    unfold nrm
    refine Finset.measurable_prod _ fun v _ => ?_
    have h1 : Measurable fun y : D.Y => |(y.2 v).1.im| :=
      continuous_abs.measurable.comp (measurable_im.comp (measurable_subtype_coe.comp ((measurable_pi_apply v).comp measurable_snd)))
    exact h1.pow_const _
  obtain ⟨hmeas, ⟨C, hC⟩, htr⟩ := pf_LinTr (X I × Gf) D.Y ν (D.M k) ((Dat.Op a).restrict h) K
    (fun y => (y.2, D.rep y.1)) (fun y => nrm k y.2) hn_meas (fun y => nrm_pos k y.2)
    (fun p => (hE4b' p).2.1)
    (fun f => have := hH.ax.cO; measurable_from_prod_countable_right fun ω => (((isForm_sub D k _).1 f.2).hol (D.rep ω)).1.measurable)
    (fun p => (hE4b' p).2.2)
    (fun f => let ⟨C, hC⟩ := ((isForm_sub D k _).1 f.2).bdd; ⟨C, fun y => hC _ _⟩)
    (fun f p => (hint _).trans (hE5 F I Gf D hH.ax k hH.four hH.compat b hb f.1 ((isForm_sub D k _).1 f.2) p))
  have hval (y : D.Y) : ((Dat.Op a).restrict h (K y)).1 (y.2, D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
    show ∑ i, D.Kern k y (y.2, D.rep y.1 * a i) = ∑' γ : PG F, D.kk k a γ y
    simp only [Dat.Kern, Dat.kk, Dat.kt, Dat.Te]
    rw [← Summable.tsum_finsetSum fun i _ => ((hE4b' (y.2, D.rep y.1 * a i)).1 y).of_norm]
    exact tsum_congr fun γ => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by simp only [mul_assoc]
  have hgi : Integrable (fun y => ∑' γ : PG F, D.kk k a γ y) ν :=
    (integrable_const C).mono' (show Measurable fun y => ∑' γ : PG F, D.kk k a γ y by simpa only [hval] using hmeas).aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [hval] using hC y)
  refine ⟨((integrable_withDensity_iff_integrable_smul hbm).1 hgi).congr (ae_of_all _ fun y => by simp [NNReal.smul_def, coe_toNNReal _ (hb.nonneg y)]),
    by rw [htr, hint]; exact integral_congr_ae (ae_of_all _ fun y => by simp only [hval])⟩

-- === C1 & C4: Action integral swap & counting measure invariance ===

theorem action_integral_swap_proof : C1 := by
  intro G Y _ _ _ _ μ hP b b' hb hb'
  have hls (b1 b2 : Y → ℝ) (hb1 : IsCut G b1) (hb2 : IsCut G b2) (u : Y → ℝ≥0∞) (hu : Measurable u) :
      ∫⁻ y, oR (b1 y) * u y ∂μ = ∑' g : G, ∫⁻ y, oR (b2 (g • y)) * (oR (b1 y) * u y) ∂μ := by
    have hm g : Measurable fun y => oR (b2 (g • y)) * (oR (b1 y) * u y) :=
      (hb2.meas.comp (hP g).measurable).ennreal_ofReal.mul (hb1.meas.ennreal_ofReal.mul hu)
    rw [← lintegral_tsum fun g => (hm g).aemeasurable]
    exact lintegral_congr fun y => by
      rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => hb2.nonneg _) (hb2.sum y).summable,
        (hb2.sum y).tsum_eq, ENNReal.ofReal_one, one_mul]
  have hle (u : Y → ℝ≥0∞) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y) :
      ∫⁻ y, oR (b y) * u y ∂μ = ∫⁻ y, oR (b' y) * u y ∂μ := by
    rw [hls b b' hb hb' u hu, hls b' b hb' hb u hu]
    calc _ = ∑' g : G, ∫⁻ y, oR (b (g⁻¹ • y)) * (oR (b' y) * u y) ∂μ := tsum_congr fun g => by
              rw [← (hP g⁻¹).lintegral_comp_emb (actEquiv hP g⁻¹).measurableEmbedding]
              exact lintegral_congr fun y => by simp [hinv]; ring
      _ = _ := (Equiv.inv G).tsum_eq fun g => ∫⁻ y, oR (b (g • y)) * (oR (b' y) * u y) ∂μ
  refine ⟨hle, fun u hu hinv hi => ?_⟩
  have hne (c : ℝ) (hc : 0 ≤ c) (v : ℂ) : ‖c • v‖ₑ = oR c * ‖v‖ₑ := by rw [enorm_smul, Real.enorm_eq_ofReal hc]
  have hi' : Integrable (fun y => b' y • u y) μ :=
    ⟨(hb'.meas.smul hu).aestronglyMeasurable, by
      have h := hi.hasFiniteIntegral; simp only [HasFiniteIntegral, hne _ (hb.nonneg _), hne _ (hb'.nonneg _)] at h ⊢
      rwa [← hle _ hu.enorm fun g y => by simp [hinv]]⟩
  have his (b1 b2 : Y → ℝ) (hb1 : IsCut G b1) (hb2 : IsCut G b2) (hI : Integrable (fun y => b1 y • u y) μ) :
      ∫ y, b1 y • u y ∂μ = ∑' g : G, ∫ y, b2 (g • y) • (b1 y • u y) ∂μ := by
    have hm g : Measurable fun y => b2 (g • y) • (b1 y • u y) := (hb2.meas.comp (hP g).measurable).smul (hb1.meas.smul hu)
    rw [← integral_tsum (fun g => (hm g).aestronglyMeasurable)]
    · exact integral_congr_ae (ae_of_all _ fun y => by dsimp only; rw [(hb2.sum y).summable.tsum_smul_const, (hb2.sum y).tsum_eq, one_smul])
    · have h := hI.hasFiniteIntegral; have e := hls b1 b2 hb1 hb2 (fun y => ‖u y‖ₑ) hu.enorm
      simp only [HasFiniteIntegral, hne _ (hb1.nonneg _), hne _ (hb2.nonneg _)] at h e ⊢; rw [← e]; exact h.ne
  refine ⟨hi', ?_⟩
  rw [his b b' hb hb' hi, his b' b hb' hb hi']
  calc _ = ∑' g : G, ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := tsum_congr fun g => by
            rw [← (hP g⁻¹).integral_comp (actEquiv hP g⁻¹).measurableEmbedding]
            exact integral_congr_ae (ae_of_all _ fun y => by simp [hinv]; ring)
    _ = _ := (Equiv.inv G).tsum_eq fun g => ∫ y, b (g • y) • (b' y • u y) ∂μ

theorem counting_measure_invariance_proof : C1 → C4 := by
  intro _ G Ω X _ _ _ _ _ _ _ _ μ _ hμ b hb u hu hinv hint R hR β hβ
  have hP : Pres G ((Measure.count : Measure Ω).prod μ) := fun g => (count_pres (g • ·) (MulAction.bijective g)).prod (hμ g)
  let cut (p : Ω × X) : ℝ := if p.1 ∈ R then β p.1 p.2 else 0
  have hcut : IsCut G cut := ⟨measurable_from_prod_countable_right fun ω => by by_cases h : ω ∈ R; simpa [cut, h] using (hβ ω h).meas; simp [cut, h],
    fun ⟨ω, x⟩ => by dsimp only [cut]; split_ifs with h; exact (hβ _ h).nonneg x; exact le_rfl,
    fun ⟨ω, x⟩ => by
      obtain ⟨r, ⟨hrR, g₀, hg₀⟩, huniq⟩ := hR ω; dsimp only at hg₀
      let e : stabilizer G r → G := fun s => (s : G) * g₀
      have he : Injective e := fun _ _ h => Subtype.ext (mul_right_cancel h)
      rw [← he.hasSum_iff]
      · convert (hβ r hrR).sum (g₀ • x) using 1; funext s
        have h2 : ((s : G) * g₀) • ω = r := by rw [mul_smul, hg₀, s.2]
        simp [e, cut, h2, hrR, mul_smul, Subgroup.smul_def]
      · intro g hg; simp only [cut, Prod.smul_mk]; rw [ite_eq_right]
        intro hgR; apply hg
        exact ⟨⟨g * g₀⁻¹, by rw [mem_stabilizer_iff, mul_smul, ← hg₀, inv_smul_smul, huniq _ ⟨hgR, mem_orbit ω g⟩, hg₀]⟩, by simp [e]⟩⟩
  obtain ⟨hI', hE⟩ := (action_integral_swap_proof G (Ω × X) _ hP b cut hb hcut).2 u hu hinv hint
  have hsec := hI'.prod_right_ae; rw [Measure.ae_count_iff] at hsec
  have hF := hI'.integral_prod_left
  have hsum : HasSum (fun ω => ∫ x, cut (ω, x) • u (ω, x) ∂μ) (∫ y, b y • u y ∂(Measure.count.prod μ)) := by
    rw [hE, integral_prod _ hI', integral_countable hF]; simp only [count_real_singleton, one_smul]
    exact (integrable_count_iff.1 hF).of_norm.hasSum
  refine ⟨fun r hr => by simpa [cut, hr] using hsec r, ?_⟩
  rw [← hasSum_subtype_iff_of_support_subset (s := R) (fun ω hω => by by_contra h; exact hω (by simp [cut, h]))] at hsum
  convert hsum using 1; funext r; simp [cut, r.2]

-- === E1: Kernel series converges ===

theorem kernel_series_converges_proof : B1b → KernelTermsInvariantBounded → E0d → Pack → Mult → KapInt → E1 := by
  intro _ _ _ hPack hMult hKI F I Gf ι _ _ _ _ D k a hyp c₀ hc₀
  set CE : ℝ := Fintype.card ι * cst k
  obtain ⟨Cp, hCp⟩ := hPack F I Gf D hyp.ax
  obtain ⟨CM, hCM⟩ := hMult F I Gf D hyp.ax (1 / 16) c₀ (by norm_num) hc₀
  obtain ⟨CK, A, hK⟩ := hKI I k hyp.four
  choose Cm hCm using fun i => hyp.ax.mul (a i)⁻¹
  set C' : ℝ := ∑ i, max (Cm i) 0
  have hC'0 : 0 ≤ C' := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hNpos (z : X I) : 0 < ∏ v, |(z v).1.im| := Finset.prod_pos fun v _ => abs_pos.2 (z v).2
  have hmain (y : D.Y) (hy : c₀ ≤ D.HtY ![0, 1] y) :
      ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤
        ((Fintype.card ι : ℝ≥0) * Cp * A * CK * toNNReal (max CE 0 * √C' * max CM 0 * (1 + 1 / c₀)) : ℝ≥0) := by
    set Ht := D.HtY ![0, 1] y
    have hHt : 0 < Ht := hc₀.trans_le hy
    let h (w : D.Xs) : ℝ≥0∞ := oR (Kap k y.2 w * ∏ v, (|(y.2 v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2))
    set K : ℝ := max CE 0 * √C' / Ht
    have hK0 : 0 ≤ K := by positivity
    let Si i := {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
    have hpt (γ : {γ : PG F // ¬ Fix ![0, 1] γ}) : ‖D.kk k a γ.1 y‖ₑ ≤ ∑ i, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ.1 := by
      by_cases h0 : D.Te a γ.1.out (D.rep y.1) = 0
      · simp [Dat.kk, Dat.kt, h0]
      obtain ⟨i, hi⟩ := kk_supp D a γ.1 y.1 h0
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (Si j).indicator (fun γ' => oR K * h (γ' • y.2)) γ.1) (fun _ _ => bot_le) (Finset.mem_univ i))
      rw [indicator_of_mem (show γ.1 ∈ Si i from hi)]
      refine (ofReal_norm _).symm.trans_le ((ENNReal.ofReal_le_ofReal ?_).trans_eq (ENNReal.ofReal_mul hK0))
      have hγ' : γ.1.out 1 0 ≠ 0 := fun h0 => γ.2 ⟨γ.1.out 1 1, funext fun j => by fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two, h0]⟩
      have hgy : D.HtY ![0, 1] (γ.1 • y) = (∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1 * a i) := by
        have e0 : D.HtY ![0, 1] (γ.1 • y) = D.Ht ![0, 1] (γ.1 • y.2) (D.rep y.1 * a i) :=
          (congrArg (D.HtY ![0, 1]) (Prod.ext hi rfl : γ.1 • y = ((((D.rep y.1 * a i : Gf) : Gf ⧸ D.H) : D.Om), γ.1 • y.2))).trans
            (htY_mk D hyp.ax _ e01_ne (γ.1 • y.2) (D.rep y.1 * a i))
        rw [e0]; simp [Dat.Ht]
      have hprod : D.HtY ![0, 1] (γ.1 • y) * Ht ≤ 1 := by
        have := htY_smul D hyp.ax ![0, 1] e01_ne γ.1.out y; rw [QuotientGroup.out_eq'] at this
        rw [this, mul_comm]; exact htY_prod D hyp.ax _ _ (by simpa [vecMul, dotProduct, Fin.sum_univ_two] using hγ') y
      have hmul : D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.hf ![0, 1] (D.rep y.1 * a i) := by simpa using hCm i _ e01_ne (D.rep y.1 * a i)
      have hCm0 : 0 ≤ Cm i := by have := hyp.ax.pos ![0, 1] e01_ne (D.rep y.1); have := hyp.ax.pos ![0, 1] e01_ne (D.rep y.1 * a i); nlinarith
      have hCi : Cm i ≤ C' := (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (Cm j) 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ i))
      have hrat : (∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) * Ht ^ 2 ≤ C' * ∏ v, |(y.2 v).1.im| := by
        have hy0 : Ht = (∏ v, |(y.2 v).1.im|) * D.hf ![0, 1] (D.rep y.1) := by simp [Ht, Dat.HtY, Dat.Ht]
        have hNg : 0 ≤ ∏ v, |((γ.1 • y.2 : D.Xs) v).1.im| := Finset.prod_nonneg fun _ _ => abs_nonneg _
        have e2 : (∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.HtY ![0, 1] (γ.1 • y) := by
          rw [hgy]; nlinarith [mul_le_mul_of_nonneg_left hmul hNg]
        calc _ = ((∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) * D.hf ![0, 1] (D.rep y.1)) * Ht * ∏ v, |(y.2 v).1.im| := by rw [sq, hy0]; ring
          _ ≤ (Cm i * D.HtY ![0, 1] (γ.1 • y)) * Ht * ∏ v, |(y.2 v).1.im| := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e2 hHt.le) (hNpos y.2).le
          _ = Cm i * (D.HtY ![0, 1] (γ.1 • y) * Ht) * ∏ v, |(y.2 v).1.im| := by ring
          _ ≤ Cm i * 1 * ∏ v, |(y.2 v).1.im| := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCm0) (hNpos y.2).le
          _ ≤ C' * ∏ v, |(y.2 v).1.im| := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hCi (hNpos y.2).le
      have hsq : ((∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2) ≤ √C' / Ht := by
        rw [← sqrt_eq_rpow]
        have hq : (∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im| ≤ C' / Ht ^ 2 :=
          (div_le_div_iff₀ (hNpos y.2) (pow_pos hHt 2)).2 hrat
        exact (sqrt_le_sqrt hq).trans_eq (by rw [sqrt_div' _ (sq_nonneg Ht), sqrt_sq hHt.le])
      have hks : Kap k y.2 (γ.1 • y.2 : D.Xs) = (Kap k y.2 (γ.1 • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ.1 • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
          ((∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2) := by
        rw [← Finset.prod_div_distrib, ← finsetProd_rpow _ _ (fun _ _ => by positivity), mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one, mul_one]
        intro v _; have h1 := abs_pos.2 (y.2 v).2; have h2 := abs_pos.2 ((γ.1 • y.2 : D.Xs) v).2
        rw [← mul_rpow (by positivity) (by positivity), show |(y.2 v).1.im| / |((γ.1 • y.2 : D.Xs) v).1.im| * (|((γ.1 • y.2 : D.Xs) v).1.im| / |(y.2 v).1.im|) = 1 by field_simp, one_rpow]
      have hX : 0 ≤ Kap k y.2 (γ.1 • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ.1 • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2) :=
        mul_nonneg (Kap_nonneg _ _ _) (Finset.prod_nonneg fun _ _ => by positivity)
      calc ‖D.kk k a γ.1 y‖ ≤ CE * Kap k y.2 (γ.1 • y.2 : D.Xs) := norm_kk_le D k a hyp γ.1 y
        _ ≤ max CE 0 * Kap k y.2 (γ.1 • y.2 : D.Xs) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Kap_nonneg _ _ _)
        _ ≤ max CE 0 * ((Kap k y.2 (γ.1 • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ.1 • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) * (√C' / Ht)) := by
              conv_lhs => rw [hks]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hX) (le_max_right _ _)
        _ = _ := by ring
    obtain ⟨hfin, hcard⟩ := hCM y ![0, 1] e01_ne hy
    have hmeas : Measurable h := by
      have hp : Measurable fun w : D.Xs => ∏ v, (|(y.2 v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2) :=
        Finset.measurable_prod _ fun v _ => by
          have hi : Measurable fun w : D.Xs => |(w v).1.im| :=
            continuous_abs.measurable.comp (measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))
          exact (measurable_const.div hi).pow_const _
      exact ((hK y.2).1.mul hp).ennreal_ofReal
    have hA (w w' : D.Xs) (hn : Near (1 / 2) w w') : h w ≤ A * h w' :=
      (ENNReal.ofReal_le_ofReal ((hK y.2).2.2.2 w w' hn).2).trans_eq
        ((ENNReal.ofReal_mul A.2).trans (congrArg (· * h w') ENNReal.ofReal_coe_nnreal))
    have hcard' : (({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℕ) : ℝ≥0∞) ≤ oR (max CM 0 * (1 + Ht)) := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    have hfinal : oR K * oR (max CM 0 * (1 + Ht)) ≤ oR (max CE 0 * √C' * max CM 0 * (1 + 1 / c₀)) := by
      rw [← ENNReal.ofReal_mul hK0]; apply ENNReal.ofReal_le_ofReal
      have h1 : (1 + Ht) / Ht ≤ 1 + 1 / c₀ := by rw [add_div, div_self hHt.ne']; linarith [one_div_le_one_div_of_le hc₀ hy]
      calc K * (max CM 0 * (1 + Ht)) = max CE 0 * √C' * max CM 0 * ((1 + Ht) / Ht) := by simp only [K]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    calc ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ
        ≤ ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ∑ i, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ.1 := ENNReal.tsum_le_tsum hpt
      _ ≤ ∑' γ : PG F, ∑ i, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ :=
            ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun γ : PG F => ∑ i, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ
      _ = ∑ i, ∑' γ : PG F, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ := Summable.tsum_finsetSum fun _ _ => ENNReal.summable
      _ ≤ ∑ _i : ι, oR K * (Cp * A * oR (max CM 0 * (1 + Ht)) * CK) := Finset.sum_le_sum fun i _ => by
            rw [← _root_.tsum_subtype, ENNReal.tsum_mul_left]; gcongr
            exact (hCp y _ h A hmeas hA hfin).trans (by gcongr; exact (hK y.2).2.2.1)
      _ = (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * (oR K * oR (max CM 0 * (1 + Ht))) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * oR (max CE 0 * √C' * max CM 0 * (1 + 1 / c₀)) := by gcongr
      _ = _ := by rw [oR, ENNReal.ofReal]; push_cast; ring
  refine ⟨(Fintype.card ι : ℝ≥0) * Cp * A * CK * toNNReal (max CE 0 * √C' * max CM 0 * (1 + 1 / c₀)), fun y s hs hy => ?_⟩
  obtain ⟨δ, hδ⟩ := row_exists s hs
  have hfix (γ : PG F) : ¬ Fix s γ ↔ ¬ Fix ![0, 1] (MulAut.conj (δ : PG F) γ) := by
    have := fix_conj ![0, 1] γ.out δ; rw [QuotientGroup.out_eq', hδ] at this; exact not_congr this.symm
  let e : {γ : PG F // ¬ Fix s γ} ≃ {γ : PG F // ¬ Fix ![0, 1] γ} := (MulAut.conj (δ : PG F)).toEquiv.subtypeEquiv hfix
  calc _ = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a (e γ).1 ((δ : PG F) • y)‖ₑ :=
          tsum_congr fun γ => by rw [show (e γ).1 = (δ : PG F) * γ.1 * (δ : PG F)⁻¹ from rfl, kk_conj D k a hyp]
    _ = ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ :=
        e.tsum_eq fun γ => ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ
    _ ≤ _ := hmain _ (by rw [htY_smul D hyp.ax _ e01_ne, hδ]; exact hy)

-- === Fsum ===

theorem pf_Fsum : E0a → Fsum := by
  intro h0 F I Gf _ _ _ D hax b hb
  obtain ⟨hcG, hsig, -⟩ := h0 F I Gf D hax
  have : Countable D.Cj := hcG; have : Countable D.Om := hax.cO
  have : SigmaFinite (volume : Measure D.Xs) := hsig
  have : SFinite D.μY := by unfold Dat.μY; infer_instance
  refine ⟨⟨hb.meas.comp (measurable_fst.snd.prodMk measurable_snd), fun _ => hb.nonneg _, fun p => hb.sum (p.1.2, p.2)⟩, fun u hu hfin => ?_⟩
  have hgm : Measurable fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2 :=
    measurable_from_prod_countable_right fun c => hb.meas.smul (hu (D.el c))
  have hgi : Integrable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) (Measure.count.prod D.μY) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) < ∞
    have hm c : Measurable fun y : D.Y => ‖b y • u (D.el c) y‖ₑ := (hb.meas.smul (hu (D.el c))).enorm
    rw [lintegral_prod _ hgm.enorm.aemeasurable, lintegral_count]
    dsimp only; rw [← lintegral_tsum fun c => (hm c).aemeasurable]
    exact (lintegral_congr fun y => by simp only [enorm_smul, Real.enorm_of_nonneg (hb.nonneg y)]; exact ENNReal.tsum_mul_left).trans_lt hfin
  have hae : ∀ᵐ y ∂D.μY, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) = b y • ∑' γ, u γ y := by
    filter_upwards [hgi.prod_left_ae] with y hy
    rw [integral_countable hy]; simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]; exact tsum_const_smul'' (b y)
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc : (D.Cj × D.Om) × D.Xs ≃ᵐ D.Cj × D.Om × D.Xs) D.μC (Measure.count.prod D.μY) := by
    have hcp : (Measure.count : Measure D.Cj).prod (Measure.count : Measure D.Om) = Measure.count :=
      Measure.ext_iff_singleton.2 fun ⟨a, b⟩ => by rw [Measure.count_singleton, ← singleton_prod_singleton, Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, one_mul]
    rw [show D.μC = (Measure.count.prod Measure.count).prod volume by unfold Dat.μC; rw [hcp]]
    exact measurePreserving_prodAssoc _ _ _
  refine ⟨measurable_from_prod_countable_right fun a => by dsimp only; exact (hu (D.el a.1)).comp measurable_prodMk_left,
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hgi, hgi.integral_prod_right.congr hae,
    (integral_congr_ae hae).symm.trans $ (integral_prod_symm _ hgi).symm.trans (hmp.integral_comp' _).symm⟩

end UpperTheory.Esk
