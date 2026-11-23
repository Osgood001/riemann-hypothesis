import B3

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup Topology Metric
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === Shared helpers for B4 & B5 ===

def ptE : ℝ × {y : ℝ // y ≠ 0} ≃ᵐ P where
  toFun p := pt p.1 p.2.1 p.2.2
  invFun z := (z.1.re / z.1.im, ⟨z.1.im, z.2⟩)
  left_inv := fun ⟨x, y, hy⟩ => Prod.ext (by simp [pt]; field_simp) (Subtype.ext (by simp [pt]))
  right_inv z := Subtype.ext $ Complex.ext (by simp [pt]; field_simp [z.2]) (by simp [pt])
  measurable_toFun := pt_cont.measurable
  measurable_invFun := ((measurable_re.comp measurable_subtype_coe).div (measurable_im.comp measurable_subtype_coe)).prodMk
    (measurable_im.comp measurable_subtype_coe).subtype_mk

def smulE (g : GL2 ℝ) : P ≃ᵐ P where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (cont_smul_P g).measurable
  measurable_invFun := (cont_smul_P g⁻¹).measurable

lemma diag_smul {g : GL2 ℝ} (hb : g 0 1 = 0) (hc : g 1 0 = 0) (z : P) : (g • z).1 = ((g 0 0 / g 1 1 : ℝ) : ℂ) * z.1 := by
  have hd : g 1 1 ≠ 0 := fun h => g.det_ne_zero (by rw [det_eq, hb, h]; ring)
  have hd' : ((g 1 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [coe_smul]; simp only [num, den, hb, hc, ofReal_zero, zero_mul, add_zero, zero_add, ofReal_div]; field_simp

-- === DiagonalIntegrandVanishes ===

theorem diagonal_integrand_vanishes_proof : DiagonalIntegrandVanishes := by
  intro k hk g hb hc hne
  have hdet : g.val.det = g 0 0 * g 1 1 := by rw [det_eq, hb]; ring
  have hdet0 : g 0 0 * g 1 1 ≠ 0 := hdet ▸ g.det_ne_zero
  have hd : g 1 1 ≠ 0 := right_ne_zero_of_mul hdet0
  have hden (z : ℂ) : den g z = ((g 1 1 : ℝ) : ℂ) := by simp [den, hc]
  have him (z : P) : (g • z).1.im * z.1.im = g 0 0 * g 1 1 * (z.1.im ^ 2 / (g 1 1 * g 1 1)) := by
    rw [im_smul, hden, normSq_ofReal, hdet]; ring
  rcases lt_or_gt_of_ne hdet0 with hneg | hpos
  · refine ⟨0, continuous_const, fun x y hy => ?_, integrable_zero _ _ _, by simp, by simp, Or.inl rfl⟩
    have : ¬(0 < (pt x y hy).1.im * (g • pt x y hy).1.im) := by
      rw [mul_comm, him]; nlinarith [div_nonneg (sq_nonneg (pt x y hy).1.im) (mul_self_nonneg (g 1 1))]
    simp [q1, this]
  · set r : ℝ := g 0 0 / g 1 1
    have hr0 : 0 < r := by rcases lt_or_gt_of_ne hd with h | h; exact div_pos_of_neg_of_neg (by nlinarith) h; exact div_pos (by nlinarith) h
    have hr1 : 1 - r ≠ 0 := fun h => hne (by simp only [r] at h; field_simp at h; linarith)
    let D (x : ℝ) : ℂ := ((1 - r : ℝ) : ℂ) * x + ((1 + r : ℝ) : ℂ) * I
    have hDne (x : ℝ) : D x ≠ 0 := fun h => by have := congrArg im h; simp [D] at this; linarith
    have hDcont : Continuous D := by unfold D; fun_prop
    have hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖(D x ^ k)⁻¹‖ ≤ K / (1 + x ^ 2) ^ 2 := by
      set m := min ((1 - r) ^ 2) 1
      have hm0 : 0 < m := lt_min (by positivity) one_pos
      refine ⟨(m ^ 2)⁻¹, by positivity, fun x => ?_⟩
      have hsq : ‖D x‖ ^ 2 = (1 - r) ^ 2 * x ^ 2 + (1 + r) ^ 2 := by rw [Complex.sq_norm, normSq_apply]; simp [D]; ring
      have h1 : m * (1 + x ^ 2) ≤ ‖D x‖ ^ 2 := by
        rw [hsq]; nlinarith [mul_le_mul_of_nonneg_right (min_le_left ((1 - r) ^ 2) 1) (sq_nonneg x), min_le_right ((1 - r) ^ 2) 1]
      have h1D : 1 ≤ ‖D x‖ :=
        (show 1 ≤ |(D x).im| by simp [D, abs_of_pos (by linarith : 0 < 1 + r)]; linarith).trans (abs_im_le_norm (D x))
      have h3 : (m * (1 + x ^ 2)) ^ 2 ≤ ‖D x‖ ^ k :=
        (pow_le_pow_left₀ (by positivity) h1 2).trans $ by rw [show (‖D x‖ ^ 2) ^ 2 = ‖D x‖ ^ 4 by ring]; exact pow_le_pow_right₀ h1D hk
      rw [norm_inv, norm_pow]; exact (inv_anti₀ (by positivity) h3).trans_eq (by rw [mul_pow, mul_inv, div_eq_mul_inv])
    have hint_of {f : ℝ → ℂ} (hf : Continuous f) {K : ℝ} (h : ∀ x, ‖f x‖ ≤ K / (1 + x ^ 2)) : Integrable f :=
      (integrable_inv_one_add_sq.const_mul K).mono' hf.aestronglyMeasurable (ae_of_all _ fun x => by rw [← div_eq_mul_inv]; exact h x)
    set c : ℂ := ((g 1 1 : ℝ) : ℂ) ^ k * ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ)
    set E : ℂ := ((k : ℂ) - 1) / (4 * π) * (2 * I * r) ^ k * c
    have hE0 : E ≠ 0 := by
      have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd)) (by exact_mod_cast (rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne')
      have hk1 : (k : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (by omega : k ≠ 1))
      have hpi : (4 * (π : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast pi_ne_zero)
      exact mul_ne_zero (mul_ne_zero (div_ne_zero hk1 hpi) (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (by exact_mod_cast hr0.ne')))) hc0
    obtain ⟨K, hK, hbnd⟩ := hbound
    have hcont : Continuous fun x => E * (D x ^ k)⁻¹ := continuous_const.mul ((hDcont.pow k).inv₀ fun x => pow_ne_zero _ (hDne x))
    refine ⟨fun x => E * (D x ^ k)⁻¹, hcont, fun x y hy => ?_,
      hint_of hcont fun x => by rw [norm_mul, mul_div_assoc]; exact mul_le_mul_of_nonneg_left ((hbnd x).trans (div_le_div_of_nonneg_left hK (by positivity) (by nlinarith [sq_nonneg x]))) (norm_nonneg E),
      ?_, ?_, Or.inr fun x => mul_ne_zero hE0 (inv_ne_zero (pow_ne_zero _ (hDne x)))⟩
    · have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
      have hw : (g • pt x y hy).1 = (r : ℂ) * ((y : ℂ) * (x + I)) := diag_smul hb hc _
      have hpos' : 0 < (pt x y hy).1.im * (g • pt x y hy).1.im := by
        rw [mul_comm, him]; exact mul_pos hpos (div_pos (pow_pos (abs_pos.2 (pt x y hy).2) 2 |> fun h => by simpa [sq_abs] using h) (mul_self_pos.2 hd))
      have hratio : ((g • pt x y hy).1 - conj (g • pt x y hy).1) / ((pt x y hy).1 - conj (g • pt x y hy).1) = 2 * I * r / D x := by
        rw [hw]; simp only [pt, map_mul, map_add, conj_ofReal, conj_I, D]
        rw [show (r : ℂ) * (y * (x + I)) - r * (y * (x + -I)) = y * (2 * I * r) by ring,
          show (y : ℂ) * (x + I) - r * (y * (x + -I)) = y * (((1 - r : ℝ) : ℂ) * x + ((1 + r : ℝ) : ℂ) * I) by push_cast; ring,
          mul_div_mul_left _ _ hy']
      simp only [q1, ite_eq_left hpos', j1, hden, hratio, div_pow, E, c]; ring
    · have hlogc : Continuous fun x : ℝ => Real.log (1 + x ^ 2) := (continuous_const.add (continuous_pow 2)).log fun x => (by positivity : (0 : ℝ) < 1 + x ^ 2).ne'
      refine hint_of ((continuous_ofReal.comp hlogc).mul hcont) (K := ‖E‖ * K) fun x => ?_
      have hl0 : 0 ≤ Real.log (1 + x ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg x])
      have hl1 : Real.log (1 + x ^ 2) ≤ 1 + x ^ 2 := by linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
      have hp : (0 : ℝ) < 1 + x ^ 2 := by positivity
      rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
      calc Real.log (1 + x ^ 2) * (‖E‖ * ‖(D x ^ k)⁻¹‖) ≤ (1 + x ^ 2) * (‖E‖ * (K / (1 + x ^ 2) ^ 2)) :=
            mul_le_mul hl1 (mul_le_mul_of_nonneg_left (hbnd x) (norm_nonneg E)) (by positivity) hp.le
        _ = ‖E‖ * K / (1 + x ^ 2) := by field_simp
    · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
      rw [integral_const_mul]
      have hA' : (1 : ℂ) - r ≠ 0 := by exact_mod_cast hr1
      have hn' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hderiv x : HasDerivAt (fun x => (-((n : ℂ) + 1) * (1 - r : ℝ))⁻¹ * (D x ^ (n + 1))⁻¹) ((D x ^ (n + 2))⁻¹) x := by
        have hD : HasDerivAt D ((1 - r : ℝ) : ℂ) x := by
          show HasDerivAt (fun x : ℝ => ((1 - r : ℝ) : ℂ) * x + ((1 + r : ℝ) : ℂ) * I) ((1 - r : ℝ) : ℂ) x
          simpa using (((hasDerivAt_id x).ofReal_comp).const_mul ((1 - r : ℝ) : ℂ)).add_const (((1 + r : ℝ) : ℂ) * I)
        refine (((hD.pow (n + 1)).fun_inv (pow_ne_zero _ (hDne x))).const_mul _).congr_deriv ?_
        have := hDne x; simp only [Pi.pow_apply, Nat.add_sub_cancel]; push_cast; field_simp; ring
      have htend {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => |x|) l atTop) : Tendsto (fun x => (D x ^ (n + 1))⁻¹) l (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hDn : Tendsto (fun x => ‖D x‖) l atTop := tendsto_atTop_mono
          (fun x => (show |1 - r| * |x| ≤ |(D x).re| by simp [D, abs_mul]).trans (abs_re_le_norm (D x))) (hl.const_mul_atTop (abs_pos.2 hr1))
        exact (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (Nat.succ_ne_zero n)).comp hDn)).congr fun _ => by simp
      have hI := integral_of_hasDerivAt_of_tendsto hderiv
        (hint_of ((hDcont.pow (n + 2)).inv₀ fun x => pow_ne_zero _ (hDne x)) fun x =>
          (hbnd x).trans (div_le_div_of_nonneg_left hK (by positivity) (by nlinarith [sq_nonneg x])))
        (by simpa using (htend tendsto_abs_atBot_atTop).const_mul (-((n : ℂ) + 1) * (1 - r : ℝ))⁻¹)
        (by simpa using (htend tendsto_abs_atTop_atTop).const_mul (-((n : ℂ) + 1) * (1 - r : ℝ))⁻¹)
      rw [hI, sub_self, mul_zero]

-- === Fcen ===

theorem pf_Fcen : Fcen := by
  intro F _ γ δ htr h
  have h' : ((δ * γ * δ⁻¹ : GL2 F) : PG F) = γ := by simp [h]
  set c := (δ * γ * δ⁻¹)⁻¹ * γ
  obtain ⟨h1, h2, h3⟩ := center_entries (show c ∈ center (GL2 F) from QuotientGroup.eq.1 h')
  have hcv : c.val = c 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  have hγ : γ = (δ * γ * δ⁻¹) * c := by dsimp only [c]; group
  have htrc : ((δ * γ * δ⁻¹ : GL2 F) : Matrix (Fin 2) (Fin 2) F).trace = γ.val.trace := by
    simp only [Units.val_mul]; rw [trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have ht : c 0 0 = 1 := mul_right_cancel₀ htr $ by
    conv_rhs => rw [one_mul, show γ.val = (δ * γ * δ⁻¹ : GL2 F).val * c.val from congrArg Units.val hγ, hcv,
      Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul, htrc]
  have hc1 : c = 1 := Units.ext (by rw [hcv, ht, one_smul, Units.val_one])
  rw [hc1, mul_one] at hγ; calc δ * γ = δ * γ * δ⁻¹ * δ := by group
    _ = γ * δ := by rw [← hγ]

-- === F2: Diagonal terms contribution ===

lemma diag_real_gl2 (g : GL2 ℝ) (hv : 4 * g.val.det < g.val.trace ^ 2) :
    ∃ g0 : GL2 ℝ, (g0⁻¹ * g * g0) 0 1 = 0 ∧ (g0⁻¹ * g * g0) 1 0 = 0 ∧ (g0⁻¹ * g * g0) 0 0 ≠ (g0⁻¹ * g * g0) 1 1 := by
  have diag_of (M Dm : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0) (hgM : g.val * M = M * Dm)
      (h1 : Dm 0 1 = 0) (h2 : Dm 1 0 = 0) (h3 : Dm 0 0 ≠ Dm 1 1) :
      ∃ g0 : GL2 ℝ, (g0⁻¹ * g * g0) 0 1 = 0 ∧ (g0⁻¹ * g * g0) 1 0 = 0 ∧ (g0⁻¹ * g * g0) 0 0 ≠ (g0⁻¹ * g * g0) 1 1 := by
    let g0 := GeneralLinearGroup.mkOfDetNeZero M hM
    have e : (g0⁻¹ * g * g0).val = Dm := by
      rw [Units.val_mul, Units.val_mul, mul_assoc, show g0.val = M from rfl, hgM, ← mul_assoc, show g0⁻¹.val * M = (g0⁻¹ * g0).val from rfl, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    exact ⟨g0, by rw [e]; exact h1, by rw [e]; exact h2, by rw [e]; exact h3⟩
  rw [det_fin_two, trace_fin_two] at hv
  by_cases hb : g 0 1 = 0
  · have hne : g 0 0 ≠ g 1 1 := fun e => by rw [e, hb] at hv; nlinarith
    exact diag_of !![g 0 0 - g 1 1, 0; g 1 0, 1] !![g 0 0, 0; 0, g 1 1]
      (by rw [det_fin_two_of]; intro e; exact hne (by linear_combination e))
      (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb] <;> ring)
      (by simp) (by simp) (by simpa using hne)
  · have hΔ : 0 < (g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by linarith
    set s := √((g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))
    have hs : s ^ 2 = (g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := sq_sqrt hΔ.le
    exact diag_of !![g 0 1, g 0 1; (g 0 0 + g 1 1 + s) / 2 - g 0 0, (g 0 0 + g 1 1 - s) / 2 - g 0 0]
      !![(g 0 0 + g 1 1 + s) / 2, 0; 0, (g 0 0 + g 1 1 - s) / 2]
      (by rw [det_fin_two_of]; intro e; rcases mul_eq_zero.1 (show g 0 1 * s = 0 by linear_combination -e) with h | h; exact hb h; exact (sqrt_pos.2 hΔ).ne' h)
      (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination (1 / 4 : ℝ) * hs | linear_combination (-1 / 4 : ℝ) * hs)
      (by simp) (by simp) (by simp; linarith [sqrt_pos.2 hΔ])

theorem diagonal_terms_contribution_proof : B1a → B1b → UpperHalfPlaneMeasureCoordinates → DiagonalIntegrandVanishes → C1 → E0a → KernelTermsInvariantBounded → Ecut → Fcen → F2 := by
  intro hB1a _ _ _ _ hE0a _ hEcut _ F I Gf ι _ _ _ _ D k a hyp γ ω hTE β hβ hint
  obtain ⟨hcount, -, hpres, -, -, -, hborel, -⟩ := hE0a F I Gf D hyp.ax
  have : SigmaFinite (volume : Measure P) := hB1a.1; have : Countable (PG F) := hcount
  have : BorelSpace D.Xs := hborel; have : BorelSpace (I → P) := hborel
  have hu (z : D.Xs) : D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) *
      ∏ i, (q1 (k i) (z i) (D.r i γ.out • z i) * j1 (k i) (D.r i γ.out) (z i)) := by
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) = _; unfold qq Dat.J; rw [← Finset.prod_mul_distrib]; rfl
  by_cases hT : D.Te a γ.out (D.rep ω) = 0
  · simp [hu, hT]
  obtain ⟨i0, hi0⟩ := kk_supp D a γ ω hT; obtain ⟨htr, htr2⟩ := kk_reg D k a hyp γ ω i0 hi0
  obtain ⟨v, hv⟩ : ∃ v, 4 * (D.r v γ.out).val.det < (D.r v γ.out).val.trace ^ 2 := by
    unfold Dat.TotEll at hTE; push Not at hTE; obtain ⟨v, hv⟩ := hTE
    exact ⟨v, by rw [r_det, r_tr]; exact lt_of_le_of_ne hv fun h => htr2 ((D.σ v).injective (by rw [map_pow, map_mul, map_ofNat]; exact h.symm))⟩
  obtain ⟨g0, h01, h10, hne⟩ := diag_real_gl2 (D.r v γ.out) hv
  obtain ⟨φ, -, hφeq, -, -, hφ0, -⟩ := diagonal_integrand_vanishes_proof (k v) (hyp.four v) (g0⁻¹ * D.r v γ.out * g0) h01 h10 hne
  set S := stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)
  have hSmem (δ : PG F) (hδ : δ ∈ S) : δ * γ * δ⁻¹ = γ ∧ δ • ω = ω := by
    have h := mem_stabilizer_iff.1 hδ; exact ⟨congrArg (fun p : D.Cj × D.Om => D.el p.1) h, congrArg Prod.snd h⟩
  obtain ⟨β0, hβ0⟩ := (hEcut F I Gf D hyp.ax).2 ω S fun δ hδ => (hSmem δ hδ).2
  let yco (w : P) : {y : ℝ // y ≠ 0} := ⟨(g0⁻¹ • w).1.im, (g0⁻¹ • w).2⟩
  let fpr (w : P) : P := g0 • pt 0 (yco w).1 (yco w).2
  let proj (z : D.Xs) : D.Xs := update z v (fpr (z v))
  have hdiag (δ : PG F) (hδ : δ ∈ S) : (g0⁻¹ * D.r v δ.out * g0) 0 1 = 0 ∧ (g0⁻¹ * D.r v δ.out * g0) 1 0 = 0 := by
    set M := g0⁻¹ * D.r v δ.out * g0; set D0 := g0⁻¹ * D.r v γ.out * g0
    have hcomm : D.r v δ.out * D.r v γ.out = D.r v γ.out * D.r v δ.out := by
      rw [← map_mul, pf_Fcen F γ.out δ.out htr (by simpa [QuotientGroup.out_eq'] using (hSmem δ hδ).1), map_mul]
    have hcm : M * D0 = D0 * M := by
      simp only [M, D0, mul_assoc, mul_inv_cancel_left]; rw [← mul_assoc (D.r v δ.out) (D.r v γ.out) g0, hcomm, mul_assoc]
    have a1 := congrArg (fun x : GL2 ℝ => x 0 1) hcm; have a2 := congrArg (fun x : GL2 ℝ => x 1 0) hcm
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h01, h10] at a1 a2
    exact ⟨(mul_eq_zero.1 (show M 0 1 * (D0 1 1 - D0 0 0) = 0 by linear_combination a1)).resolve_right (sub_ne_zero.2 hne.symm),
      (mul_eq_zero.1 (show M 1 0 * (D0 0 0 - D0 1 1) = 0 by linear_combination a2)).resolve_right (sub_ne_zero.2 hne)⟩
  have hpeq (δ : S) (z : D.Xs) : proj (δ • z) = δ • proj z := funext fun i => by
    let z' : I → P := z
    have h1 : (δ • z : D.Xs) = D.act δ.1.out z' := smulX_out D δ.1 z
    have h2 : (δ • proj z : D.Xs) = D.act δ.1.out (proj z) := smulX_out D δ.1 (proj z)
    rw [h1, h2]
    change update (D.act δ.1.out z') v (fpr (D.act δ.1.out z' v)) i = D.act δ.1.out (update z' v (fpr (z' v))) i
    dsimp only [Dat.act]
    by_cases hi : i = v
    · subst hi; simp only [update_self]
      have hd := hdiag δ.1 δ.2; set m := D.r i δ.1.out; set d := g0⁻¹ * m * g0
      have hm1 : m * g0 = g0 * d := by simp only [d]; group
      dsimp only [fpr]; rw [smul_smul, hm1, mul_smul]; congr 1; apply Subtype.ext; rw [diag_smul hd.1 hd.2]
      have e1 : g0⁻¹ • (m • z' i) = d • (g0⁻¹ • z' i) := by rw [smul_smul, smul_smul]; congr 1; simp only [d]; group
      show (((g0⁻¹ • (m • z' i)).1.im : ℝ) : ℂ) * ((0 : ℝ) + Complex.I) = _ * ((((g0⁻¹ • z' i).1.im : ℝ) : ℂ) * ((0 : ℝ) + Complex.I))
      rw [e1, diag_smul hd.1 hd.2, im_ofReal_mul]; push_cast; ring
    · simp only [update_of_ne hi]; rfl
  have hpm : Measurable proj := measurable_pi_iff.2 fun i => by
    change Measurable fun z : I → P => update z v (fpr (z v)) i
    by_cases hi : i = v
    · subst hi; simp only [update_self]
      have h1 : Continuous fpr := (cont_smul_P g0).comp (pt_cont.comp (continuous_const.prodMk
        (Continuous.subtype_mk (continuous_im.comp (continuous_subtype_val.comp (cont_smul_P g0⁻¹))) _)))
      exact h1.measurable.comp (measurable_pi_apply i)
    · simp only [update_of_ne hi]; exact measurable_pi_apply i
  have hβ' : IsCut S (fun z : D.Xs => β0 (proj z)) :=
    ⟨hβ0.meas.comp hpm, fun _ => hβ0.nonneg _, fun z => by
      have : (fun δ : S => β0 (proj (δ • z))) = fun δ : S => β0 (δ • proj z) := funext fun δ => congrArg β0 (hpeq δ z)
      show HasSum _ 1; rw [this]; exact hβ0.sum _⟩
  have hinv (δ : S) (z : D.Xs) : D.kk k a γ (ω, δ • z) = D.kk k a γ (ω, z) := by
    obtain ⟨h1, h2⟩ := hSmem δ.1 δ.2; have := kk_conj D k a hyp δ.1 γ (ω, z); rw [h1] at this; rw [← this, Prod.smul_mk, h2]; rfl
  obtain ⟨hint', heq⟩ := (action_integral_swap_proof S D.Xs volume (fun δ => hpres δ.1) β (fun z : D.Xs => β0 (proj z)) hβ hβ').2
    (fun z => D.kk k a γ (ω, z)) ((meas_kk D k a hyp γ).comp (measurable_const.prodMk measurable_id)) hinv hint
  rw [heq]
  let fac (i : I) (w : P) := q1 (k i) w (D.r i γ.out • w) * j1 (k i) (D.r i γ.out) w
  have hint'' : Integrable (fun z : X I => β0 (proj z) • (D.Te a γ.out (D.rep ω) * ∏ i, fac i (z i))) :=
    hint'.congr (ae_of_all _ fun z => by dsimp only; rw [hu])
  rw [show ∫ z : D.Xs, β0 (proj z) • D.kk k a γ (ω, z) = ∫ z : X I, β0 (proj z) • (D.Te a γ.out (D.rep ω) * ∏ i, fac i (z i)) from
    integral_congr_ae (ae_of_all _ fun z => by dsimp only; rw [hu])]
  let E : ℝ × {y : ℝ // y ≠ 0} ≃ᵐ P := ptE.trans (smulE g0)
  have hE : MeasurePreserving E ((volume : Measure ℝ).prod ((Measure.comap Subtype.val volume).withDensity fun y => oR (1 / |y.1|))) volume :=
    (mp_smul_P g0).comp pt_mp
  have : SigmaFinite (Measure.comap (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) volume) := sf_nz
  have hfac x (y : {y : ℝ // y ≠ 0}) : fac v (E (x, y)) = φ x := by
    set d := g0⁻¹ * D.r v γ.out * g0
    rw [← hφeq x y.1 y.2]
    have hgd : D.r v γ.out = g0 * d * g0⁻¹ := by simp only [d]; group
    have hsm : D.r v γ.out • g0 • pt x y.1 y.2 = g0 • d • pt x y.1 y.2 := by rw [hgd, mul_smul, mul_smul, inv_smul_smul]
    change q1 (k v) (g0 • pt x y.1 y.2) (D.r v γ.out • g0 • pt x y.1 y.2) * j1 (k v) (D.r v γ.out) (g0 • pt x y.1 y.2) = _
    rw [hsm, hgd]; exact qj_conj (k v) g0 d (pt x y.1 y.2)
  have hfE x (y : {y : ℝ // y ≠ 0}) : fpr (E (x, y)) = E (0, y) := by
    have hy' : (yco (E (x, y))).1 = y.1 := by show (g0⁻¹ • g0 • pt x y.1 y.2).1.im = y.1; rw [inv_smul_smul]; simp [pt]
    change g0 • pt 0 (yco (E (x, y))).1 _ = g0 • pt 0 y.1 y.2; congr 1; apply Subtype.ext
    show ((yco (E (x, y))).1 : ℂ) * ((0 : ℝ) + Complex.I) = (y.1 : ℂ) * ((0 : ℝ) + Complex.I); rw [hy']
  let _ : Unique {i // i = v} := ⟨⟨⟨v, rfl⟩⟩, fun a => Subtype.ext a.2⟩
  let Φ : X I ≃ᵐ P × ({i // ¬i = v} → P) :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => P) (fun i => i = v)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique {i // i = v} P) (MeasurableEquiv.refl _))
  have hΦm : MeasurePreserving Φ volume ((volume : Measure P).prod volume) := by
    have h2 : MeasurePreserving (Prod.map (MeasurableEquiv.funUnique {i // i = v} P) id)
        ((@Measure.pi {i // i = v} (fun _ => P) (Subtype.fintype (fun i => i = v)) _ fun _ => (volume : Measure P)).prod
          (Measure.pi fun _ : {i // ¬i = v} => (volume : Measure P)))
        ((volume : Measure P).prod (Measure.pi fun _ : {i // ¬i = v} => (volume : Measure P))) := by
      convert (measurePreserving_funUnique (volume : Measure P) {i // i = v}).prod
        (MeasurePreserving.id (Measure.pi fun _ : {i // ¬i = v} => (volume : Measure P)))
    exact h2.comp (measurePreserving_piEquivPiSubtypeProd (fun _ : I => (volume : Measure P)) (fun i => i = v))
  have hΦs w r : Φ.symm (w, r) = update (Φ.symm (iP, r)) v w := Φ.injective $ by
    have h0 := Φ.apply_symm_apply (iP, r); rw [Φ.apply_symm_apply]
    exact Prod.ext (by show w = update (Φ.symm (iP, r)) v w v; rw [update_self])
      (funext fun i => by show r i = update (Φ.symm (iP, r)) v w i.1; rw [update_of_ne i.2]; exact (congrFun (congrArg Prod.snd h0) i).symm)
  have hsymm := MeasurePreserving.symm Φ hΦm
  have hint3 : Integrable (fun p : P × ({i // ¬i = v} → P) => β0 (proj (Φ.symm p)) • (D.Te a γ.out (D.rep ω) * ∏ i, fac i (Φ.symm p i)))
      ((volume : Measure P).prod (volume : Measure ({i // ¬i = v} → P))) :=
    (hsymm.integrable_comp_emb Φ.symm.measurableEmbedding).2 hint''
  rw [← hsymm.integral_comp', integral_prod_symm _ hint3]
  refine (integral_congr_ae $ ae_of_all _ fun r => ?_).trans (integral_zero ({i // ¬i = v} → P) ℂ)
  have e1 w : β0 (proj (Φ.symm (w, r))) • (D.Te a γ.out (D.rep ω) * ∏ i, fac i (Φ.symm (w, r) i)) =
      (β0 (proj (update (Φ.symm (iP, r)) v w)) : ℂ) * (D.Te a γ.out (D.rep ω) * (fac v w * ∏ i ∈ Finset.univ.erase v, fac i (Φ.symm (iP, r) i))) := by
    rw [hΦs w r, real_smul, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), update_self,
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (ne_of_mem_erase hi)]]
  simp_rw [e1]; generalize (∏ i ∈ Finset.univ.erase v, fac i (Φ.symm (iP, r) i)) = K; generalize Φ.symm (iP, r) = z0
  rw [← hE.integral_comp']
  have e2 : (fun q : ℝ × {y : ℝ // y ≠ 0} => (β0 (proj (update z0 v (E q))) : ℂ) * (D.Te a γ.out (D.rep ω) * (fac v (E q) * K))) =
      fun q => (fun x : ℝ => D.Te a γ.out (D.rep ω) * K * φ x) q.1 * (fun y : {y : ℝ // y ≠ 0} => (β0 (proj (update z0 v (E (0, y)))) : ℂ)) q.2 :=
    funext fun ⟨x, y⟩ => by simp only [hfac, proj, update_idem, update_self, hfE]; ring
  refine (congrArg _ e2).trans ((integral_prod_mul (fun x : ℝ => D.Te a γ.out (D.rep ω) * K * φ x)
    (fun y : {y : ℝ // y ≠ 0} => (β0 (proj (update z0 v (E (0, y)))) : ℂ))).trans ?_)
  rw [integral_const_mul, hφ0]; simp

-- === Shared elliptic fixed-point lemma (replaces BOTH exists_fix AND fp/fix_comm!) ===

lemma ell_lower_left_ne {h : GL2 ℝ} (hh : h.val.trace ^ 2 < 4 * h.val.det) : h 1 0 ≠ 0 := fun e => by
  rw [trace_fin_two, det_eq, e] at hh; nlinarith [sq_nonneg (h 0 0 - h 1 1)]

def ell_fp (h : GL2 ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : P :=
  let hr := ell_lower_left_ne hh
  let hd : 0 < 4 * h.val.det - h.val.trace ^ 2 := by linarith
  ⟨(((h 0 0 - h 1 1) / (2 * h 1 0) : ℝ) : ℂ) + I * ((√(4 * h.val.det - h.val.trace ^ 2) / (2 * h 1 0) : ℝ) : ℂ),
    by simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_add, zero_mul, one_mul]
       exact div_ne_zero (sqrt_pos.2 hd).ne' (mul_ne_zero two_ne_zero hr)⟩

lemma ell_fix_comm {h g : GL2 ℝ} (hh : h.val.trace ^ 2 < 4 * h.val.det) (hc : g * h = h * g) :
    g • ell_fp h hh = ell_fp h hh := by
  have hr := ell_lower_left_ne hh; have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd : 0 < 4 * h.val.det - h.val.trace ^ 2 := by linarith
  set z0 := (ell_fp h hh).1
  have hQ : ((h 1 0 : ℝ) : ℂ) * z0 ^ 2 + (((h 1 1 : ℝ) : ℂ) - h 0 0) * z0 - h 0 1 = 0 := by
    have hs : ((√(4 * h.val.det - h.val.trace ^ 2) : ℝ) : ℂ) ^ 2 = ((4 * h.val.det - h.val.trace ^ 2 : ℝ) : ℂ) := by
      rw [← ofReal_pow, sq_sqrt hd.le]
    have hD : ((4 * h.val.det - h.val.trace ^ 2 : ℝ) : ℂ) = 4 * ((h 0 0 : ℂ) * h 1 1 - h 0 1 * h 1 0) - ((h 0 0 : ℂ) + h 1 1) ^ 2 := by
      simp only [trace_fin_two, det_eq]; push_cast; ring
    have hz : 2 * ((h 1 0 : ℝ) : ℂ) * z0 = ((h 0 0 : ℂ) - h 1 1) + I * (√(4 * h.val.det - h.val.trace ^ 2) : ℝ) := by
      simp only [z0, ell_fp]; push_cast; field_simp
    have h4 : 4 * ((h 1 0 : ℝ) : ℂ) * (((h 1 0 : ℝ) : ℂ) * z0 ^ 2 + (((h 1 1 : ℝ) : ℂ) - h 0 0) * z0 - h 0 1) = 0 := by
      rw [show 4 * ((h 1 0 : ℝ) : ℂ) * (((h 1 0 : ℝ) : ℂ) * z0 ^ 2 + (((h 1 1 : ℝ) : ℂ) - h 0 0) * z0 - h 0 1) =
          (2 * ((h 1 0 : ℝ) : ℂ) * z0) ^ 2 + 2 * (((h 1 1 : ℝ) : ℂ) - h 0 0) * (2 * ((h 1 0 : ℝ) : ℂ) * z0) - 4 * ((h 1 0 : ℝ) : ℂ) * h 0 1 by ring, hz]
      linear_combination ((√(4 * h.val.det - h.val.trace ^ 2) : ℝ) : ℂ) ^ 2 * I_sq - hs - hD
    exact (mul_eq_zero.1 h4).resolve_left (mul_ne_zero (by norm_num) hr')
  have e00 : ((g 0 0 : ℝ) : ℂ) * h 0 0 + g 0 1 * h 1 0 = h 0 0 * g 0 0 + h 0 1 * g 1 0 := by
    exact_mod_cast (by simpa [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M : GL2 ℝ => M 0 0) hc)
  have e10 : ((g 1 0 : ℝ) : ℂ) * h 0 0 + g 1 1 * h 1 0 = h 1 0 * g 0 0 + h 1 1 * g 1 0 := by
    exact_mod_cast (by simpa [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun M : GL2 ℝ => M 1 0) hc)
  apply Subtype.ext; rw [coe_smul, div_eq_iff (den_ne g (ell_fp h hh).2)]
  apply mul_left_cancel₀ hr'
  change ((h 1 0 : ℝ) : ℂ) * ((g 0 0 : ℂ) * z0 + g 0 1) = ((h 1 0 : ℝ) : ℂ) * (z0 * ((g 1 0 : ℂ) * z0 + g 1 1))
  linear_combination e00 - z0 * e10 - (g 1 0 : ℂ) * hQ

-- === B4: Radial integral formula (elliptic orbital integral) ===

lemma ch_mul {R : Type*} [CommRing R] (x y : R) : ∀ n, ch (x + y) (x * y) n * (x - y) = x ^ n - y ^ n
  | 0 => by simp [ch]
  | 1 => by simp [ch]
  | n + 2 => by simp only [ch]; linear_combination (x + y) * ch_mul x y (n + 1) - x * y * ch_mul x y n

lemma ch_cast (t d : ℝ) : ∀ n, ((ch t d n : ℝ) : ℂ) = ch (t : ℂ) (d : ℂ) n
  | 0 => by simp [ch]
  | 1 => by simp [ch]
  | n + 2 => by simp only [ch]; push_cast; rw [ch_cast t d (n + 1), ch_cast t d n]

lemma radial_upper_int (h22 : B2) (h6 : B6) (k : ℕ) (hk : 4 ≤ k) (m : GL2 ℝ) (a b : ℝ)
    (h00 : m 0 0 = a) (h01 : m 0 1 = b) (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) :
    let U : P → ℂ := fun z => if 0 < z.1.im then q1 k z (m • z) * j1 k m z else 0
    let eta : ℂ := ((a : ℂ) - b * I) / (√(a ^ 2 + b ^ 2) : ℂ)
    Integrable U ∧ ∫ z, U z = eta ^ k / (1 - eta ^ 2) := by
  intro U eta
  have hab : 0 < a ^ 2 + b ^ 2 := by positivity
  have hdetm : m.val.det = a ^ 2 + b ^ 2 := by rw [det_eq, h00, h01, h10, h11]; ring
  have hI : Integrable U := by
    obtain ⟨C, hC⟩ := h6 k hk
    have hint : Integrable fun w : P => kap iP w ^ ((k : ℝ) / 2) :=
      ⟨((cont_kap.comp (continuous_const.prodMk continuous_id)).rpow_const fun _ => Or.inr (by positivity)).aestronglyMeasurable,
       by rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => rpow_nonneg (kap_nonneg _ _) _)]; exact (hC iP).1.trans_lt ENNReal.coe_lt_top⟩
    have hc0 : 0 ≤ ((k : ℝ) - 1) / (4 * π) := div_nonneg (by have : (4 : ℝ) ≤ k := (by exact_mod_cast hk); linarith) (by positivity)
    have hFc : Continuous fun z : P => q1 k z (m • z) * j1 k m z := ((cont_q1 k).comp (continuous_id.prodMk (cont_smul_P m))).mul (cont_j1 k m)
    refine (hint.const_mul (((k : ℝ) - 1) / (4 * π) * ((a ^ 2 + b ^ 2) / b ^ 2) ^ ((k : ℝ) / 2))).mono'
      (Measurable.ite (isOpen_lt continuous_const (continuous_im.comp continuous_subtype_val)).measurableSet hFc.measurable measurable_const).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    simp only [U]; split_ifs with hz
    · rw [norm_qj k (by omega) m z, mul_assoc]; apply mul_le_mul_of_nonneg_left _ hc0
      rw [← mul_rpow (by positivity) (kap_nonneg _ _)]; refine rpow_le_rpow (kap_nonneg _ _) ?_ (by positivity)
      set x := z.1.re; set y := z.1.im
      have hden := den_ne m z.2; have hnd := normSq_pos.2 hden
      have hwim : (m • z).1.im = (a ^ 2 + b ^ 2) * y / normSq (den m z.1) := by rw [im_smul, hdetm]
      have hN : ‖z.1 - conj (m • z).1‖ ^ 2 = (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) / normSq (den m z.1) := by
        have hc' : conj (den m z.1) ≠ 0 := (map_ne_zero _).2 hden
        rw [show z.1 - conj (m • z).1 = (z.1 * conj (den m z.1) - conj (num m z.1)) / conj (den m z.1) by rw [coe_smul, map_div₀]; field_simp,
          Complex.sq_norm, normSq_div, normSq_conj]; congr 1
        rw [normSq_apply]; simp [num, den, h00, h01, h10, h11, x, y]; ring
      have hk1 : kap z (m • z) = 4 * (a ^ 2 + b ^ 2) * y ^ 2 / (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) := by
        rw [kap, ite_eq_left (mul_pos hz (by rw [hwim]; positivity)), hN, hwim]; field_simp; rfl
      have hk2 : kap iP z = 4 * y / (x ^ 2 + (1 + y) ^ 2) := by
        rw [kap, ite_eq_left (by simpa [iP, y] using hz), nsq_sub_conj]
        simp only [iP, I_im, I_re, one_mul, zero_sub, neg_sq]; rfl
      rw [hk1, hk2, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 2 * y ≤ x ^ 2 + y ^ 2 + 1 := by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
      have key : b ^ 2 * (y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2) ≤ b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left (show y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2 ≤ (x ^ 2 + y ^ 2 + 1) ^ 2 by nlinarith) (sq_nonneg b), sq_nonneg a, sq_nonneg y]
      rw [show x ^ 2 + (1 + y) ^ 2 = (x ^ 2 + y ^ 2 + 1) + 2 * y by ring]
      nlinarith [mul_le_mul_of_nonneg_left key (by positivity : 0 ≤ 4 * (a ^ 2 + b ^ 2) * y)]
    · rw [norm_zero]; exact mul_nonneg (mul_nonneg hc0 (rpow_nonneg (by positivity) _)) (rpow_nonneg (kap_nonneg _ _) _)
  refine ⟨hI, ?_⟩
  rw [(h22 U (fun z hz => ite_eq_right (not_lt.2 hz.le)) hI).2]
  have hηsq : ‖eta ^ 2‖ = 1 ∧ eta ^ 2 ≠ 1 := by
    have hs : (√(a ^ 2 + b ^ 2) : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos.2 hab).ne'
    refine ⟨by rw [norm_pow, Complex.sq_norm, show eta = ((a : ℂ) - b * I) / (√(a ^ 2 + b ^ 2) : ℂ) from rfl,
                map_div₀, normSq_ofReal, mul_self_sqrt hab.le, normSq_apply]; simp; rw [← sq, ← sq, div_self hab.ne'],
      fun h => by
        have h' : ((a : ℂ) - b * I) ^ 2 = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
          rw [show eta = ((a : ℂ) - b * I) / (√(a ^ 2 + b ^ 2) : ℂ) from rfl, div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hs)] at h
          rw [h, ← ofReal_pow, sq_sqrt hab.le]
        have h2 := congrArg re h'; simp [sq] at h2; exact hb (by nlinarith)⟩
  have hcay (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
      ext1 U (cay (circleMap 0 r θ)) = ((k : ℂ) - 1) / (4 * π) * (eta * (1 - (r : ℂ) ^ 2) / (1 - eta ^ 2 * (r : ℂ) ^ 2)) ^ k := by
    set u := circleMap 0 r θ; set z := cay u
    have hnu : ‖u‖ = r := by simp [u, abs_of_pos hr0]
    have hu1 : (1 : ℂ) - u ≠ 0 := fun h => by rw [sub_eq_zero] at h; rw [← h, norm_one] at hnu; linarith
    have huu : u * conj u = (r : ℂ) ^ 2 := by rw [Complex.mul_conj, normSq_eq_norm_sq, hnu]; push_cast; ring
    have hzpos : 0 < z.im := by rw [im_cay]; exact div_pos (by rw [normSq_eq_norm_sq, hnu]; nlinarith) (normSq_pos.2 hu1)
    have hz := hzpos.ne'; let zP : P := ⟨z, hz⟩
    have hext : ext1 U z = q1 k zP (m • zP) * j1 k m zP := by rw [ext1_of_im _ hz]; exact ite_eq_left hzpos
    set s := √(a ^ 2 + b ^ 2); have hs := sqrt_pos.2 hab; have hs2 := sq_sqrt hab.le
    have hS0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hα0 : (a : ℂ) + b * I ≠ 0 := fun h => hb (by simpa using congrArg im h)
    have hden : den m z = (((a : ℂ) - b * I) - ((a : ℂ) + b * I) * u) / (1 - u) := by
      rw [eq_div_iff hu1]; unfold den; rw [h10, h11]; simp only [z, cay]; push_cast; field_simp; ring
    have hnum : num m z = I * (((a : ℂ) - b * I) + ((a : ℂ) + b * I) * u) / (1 - u) := by
      rw [eq_div_iff hu1]; unfold num; rw [h00, h01]; simp only [z, cay]; field_simp; linear_combination (b * (1 - u)) * I_sq
    have h1 : ((a : ℂ) - b * I) - ((a : ℂ) + b * I) * u ≠ 0 := (div_ne_zero_iff.1 (hden ▸ den_ne m hz)).1
    have h2 : ((a : ℂ) + b * I) - ((a : ℂ) - b * I) * conj u ≠ 0 := fun h => h1 $ by
      have := congrArg conj h; simp at this; linear_combination this
    have hA : ((a : ℂ) + b * I) - ((a : ℂ) - b * I) * u * conj u ≠ 0 := fun h => by
      rw [mul_assoc, huu, ← ofReal_pow] at h
      have h3 := congrArg im h
      simp only [sub_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, add_zero, zero_add, mul_one, zero_im] at h3
      rcases mul_eq_zero.1 (show b * (1 + r ^ 2) = 0 by linarith) with h4 | h4; exact hb h4; nlinarith [sq_nonneg r]
    have hw : (m • zP).1 = I * (((a : ℂ) - b * I) + ((a : ℂ) + b * I) * u) / (((a : ℂ) - b * I) - ((a : ℂ) + b * I) * u) := by
      rw [coe_smul]; change num m z / den m z = _; rw [hnum, hden, div_div_div_cancel_right₀ hu1]
    have hwb : conj (m • zP).1 = -I * (((a : ℂ) + b * I) + ((a : ℂ) - b * I) * conj u) / (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * conj u) := by
      rw [hw]; simp; ring
    have hwim : 0 < (m • zP).1.im := by rw [im_smul, hdetm]; exact div_pos (mul_pos hab hzpos) (normSq_pos.2 (den_ne m hz))
    have hrp : |m.val.det| ^ (-(k : ℝ) / 2) = (s ^ k)⁻¹ := by
      rw [hdetm, ← hs2, abs_of_pos (by positivity), neg_div, rpow_neg (sq_nonneg _), sq_rpow_half hs.le]
    have hη2 : eta ^ 2 = ((a : ℂ) - b * I) / ((a : ℂ) + b * I) := by
      rw [show eta = ((a : ℂ) - b * I) / s from rfl, div_pow, div_eq_div_iff (pow_ne_zero 2 hS0) hα0, ← ofReal_pow, hs2]
      push_cast; linear_combination (-((a : ℂ) - b * I) * (b : ℂ) ^ 2) * I_sq
    rw [hext]; simp only [q1, j1, hrp]; rw [ite_eq_left (mul_pos hzpos hwim)]; push_cast
    rw [show ∀ c X Y S T : ℂ, X * Y / S = T → c * X ^ k * (Y ^ k * (S ^ k)⁻¹) = c * T ^ k from fun c X Y S T h => by rw [← h, div_pow, mul_pow]; ring]
    · have hI := I_ne_zero
      have e1 : z - conj (m • zP).1 = 2 * I * (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * u * conj u) / ((1 - u) * (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * conj u)) := by
        rw [hwb]; simp only [z, cay]; rw [div_sub_div _ _ hu1 h2]; congr 1; ring
      have e2 : (m • zP).1 - conj (m • zP).1 = 2 * I * ((a : ℂ) + b * I) * ((a : ℂ) - b * I) * (1 - u * conj u) /
          ((((a : ℂ) - b * I) - ((a : ℂ) + b * I) * u) * (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * conj u)) := by
        rw [hwb, hw, div_sub_div _ _ h1 h2]; congr 1; ring
      have e3 : 1 - eta ^ 2 * (r : ℂ) ^ 2 = (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * u * conj u) / ((a : ℂ) + b * I) := by
        rw [hη2, ← huu]; field_simp
      change ((m • zP).1 - conj (m • zP).1) / (z - conj (m • zP).1) * den m z / s = _
      rw [e1, e2, hden, e3, ← huu, show eta = ((a : ℂ) - b * I) / s from rfl]
      set p := (a : ℂ) + b * I; set q := (a : ℂ) - b * I
      have hp0 : p ≠ 0 := hα0; have h1' : q - p * u ≠ 0 := h1; have h2' : p - q * conj u ≠ 0 := h2; have hA' : p - q * u * conj u ≠ 0 := hA
      field_simp [hI, hu1, h1', h2', hA', hp0, hS0]
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  change ∫ p : ℝ × ℝ in Set.Ioo 0 1 ×ˢ Set.Ioo (-π) π, ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) * ext1 U (cay (circleMap 0 p.1 p.2)) = _
  rw [setIntegral_congr_fun hS fun p hp => by rw [hcay p.1 p.2 hp.1.1 hp.1.2]]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  set ζ := eta ^ 2; have hζ := hηsq.1; have hζ1 := hηsq.2
  have hne (r : ℝ) : 1 - ζ * (r : ℂ) ^ 2 ≠ 0 := fun h => by
    have h1 : ζ * (r : ℂ) ^ 2 = 1 := by linear_combination -h
    have h2 : r ^ 2 = 1 := by have := congrArg norm h1; rw [norm_mul, hζ, one_mul, norm_pow, norm_real, Real.norm_eq_abs, sq_abs, norm_one] at this; exact this
    exact hζ1 (by rw [show (r : ℂ) ^ 2 = 1 by exact_mod_cast h2, mul_one] at h1; exact h1)
  have e1 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * (eta * (1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 2)))
    (fun _ : ℝ => (1 : ℂ)) (Set.Ioo 0 1) (Set.Ioo (-π) π)
  simp only [mul_one] at e1; rw [Measure.volume_eq_prod, e1, setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [pi_pos])]
  have e2 : ∫ r in Ioo (0 : ℝ) 1, ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) *
        ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * (eta * (1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 2)) =
      ∫ r in Ioo (0 : ℝ) 1, ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * eta ^ (n + 2)) *
        (4 * (r : ℂ) * (1 - (r : ℂ) ^ 2) ^ n / (1 - ζ * (r : ℂ) ^ 2) ^ (n + 2)) :=
    setIntegral_congr_fun measurableSet_Ioo fun r hr => by
      have h1 : (1 - (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by nlinarith [hr.1, hr.2] : (1 - r ^ 2 : ℝ) ≠ 0)
      have h2 := hne r; push_cast; rw [div_pow, mul_pow]; field_simp; ring
  rw [e2, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  let G (r : ℝ) : ℂ := ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * eta ^ (n + 2)) * (2 / (((n : ℂ) + 1) * (ζ - 1))) *
    ((1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 1)
  have hderiv x (_ : x ∈ uIcc (0 : ℝ) 1) : HasDerivAt G
      (((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * eta ^ (n + 2)) * (4 * (x : ℂ) * (1 - (x : ℂ) ^ 2) ^ n / (1 - ζ * (x : ℂ) ^ 2) ^ (n + 2))) x := by
    have h1 : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * (x : ℂ))) x := by simpa using (hasDerivAt_pow 2 (x : ℂ)).const_sub 1
    have h2 : HasDerivAt (fun w : ℂ => 1 - ζ * w ^ 2) (-(ζ * (2 * (x : ℂ)))) x := by simpa using ((hasDerivAt_pow 2 (x : ℂ)).const_mul ζ).const_sub 1
    refine (((h1.div h2 (hne x)).pow (n + 1)).const_mul _).comp_ofReal.congr_deriv ?_
    have := hne x; simp only [Pi.div_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, div_pow]; field_simp; ring
  have hcont : ContinuousOn (fun x : ℝ => ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * eta ^ (n + 2)) *
      (4 * (x : ℂ) * (1 - (x : ℂ) ^ 2) ^ n / (1 - ζ * (x : ℂ) ^ 2) ^ (n + 2))) (uIcc 0 1) :=
    continuousOn_const.mul
      (((continuousOn_const.mul continuous_ofReal.continuousOn).mul ((continuousOn_const.sub (continuous_ofReal.continuousOn.pow 2)).pow n)).div
        ((continuousOn_const.sub (continuousOn_const.mul (continuous_ofReal.continuousOn.pow 2))).pow (n + 2))
        fun x _ => pow_ne_zero _ (hne x))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have h1ζ : 1 - ζ ≠ 0 := sub_ne_zero.2 hζ1.symm
  simp only [G, ofReal_one, one_pow, sub_self, zero_div, zero_pow (Nat.succ_ne_zero n), mul_zero,
    ofReal_zero, zero_sub, real_smul]; push_cast; field_simp; ring

theorem radial_integral_formula_proof : B1a → B1b → B1c → B2 → B6 → B4 := by
  intro _ _ _ h22 h6 k hk g hg
  let F (m : GL2 ℝ) (z : P) := q1 k z (m • z) * j1 k m z
  let U (m : GL2 ℝ) (z : P) := if 0 < z.1.im then F m z else 0
  let eta (a b : ℝ) : ℂ := ((a : ℂ) - b * I) / (√(a ^ 2 + b ^ 2) : ℂ)
  have hFconj (m h : GL2 ℝ) (z : P) : F (h⁻¹ * m * h) z = F m (h • z) := by
    have := qj_conj k h (h⁻¹ * m * h) z
    rw [show h * (h⁻¹ * m * h) * h⁻¹ = m by group, show h • (h⁻¹ * m * h) • z = m • h • z by rw [smul_smul, smul_smul]; congr 1; group] at this
    exact this.symm
  have hcomp (h : GL2 ℝ) (f : P → ℂ) : (Integrable (fun z => f (h • z)) ↔ Integrable f) ∧ ∫ z, f (h • z) = ∫ z, f z :=
    ⟨(mp_smul_P h).integrable_comp_emb (smulE h).measurableEmbedding, (mp_smul_P h).integral_comp (smulE h).measurableEmbedding f⟩
  have hUint := radial_upper_int h22 h6 k hk
  -- Conjugate g to rotation m fixing iP
  obtain ⟨h, -, -, hh⟩ := trans_iP (ell_fp g hg)
  set m := h⁻¹ * g * h
  have hmi : m • iP = iP := by rw [show m • iP = h⁻¹ • g • h • iP by simp [m, mul_smul], hh, ell_fix_comm hg rfl, ← hh, inv_smul_smul]
  have ⟨e11, e10⟩ : m 1 1 = m 0 0 ∧ m 1 0 = -(m 0 1) := by
    have h1 := congrArg Subtype.val hmi; rw [coe_smul, div_eq_iff (den_ne m (by simp [iP]))] at h1
    have hr := congrArg re h1; have hi := congrArg im h1; simp [num, den, iP] at hr hi; exact ⟨by linarith, by linarith⟩
  have htr : g.val.trace = m.val.trace := by
    simp only [m, Units.val_mul]; rw [trace_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hdt : g.val.det = m.val.det := by
    simp only [m, Units.val_mul, det_mul]; rw [mul_right_comm, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one, one_mul]
  set a := m 0 0; set b := m 0 1
  have htr' : m.val.trace = 2 * a := by rw [trace_fin_two]; change a + m 1 1 = _; rw [e11]; ring
  have hdt' : m.val.det = a ^ 2 + b ^ 2 := by rw [det_eq, e11, e10]; ring
  have hb : b ≠ 0 := fun h0 => by rw [htr, hdt, htr', hdt', h0] at hg; nlinarith
  -- Split F m = U m + U (dr * m * dr) ∘ (dr • ·)
  let dr : GL2 ℝ := GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, -1] (by simp)
  have hdr2 : dr * dr = 1 := GeneralLinearGroup.ext fun i j => by fin_cases i <;> fin_cases j <;> simp [dr, Matrix.mul_apply, Fin.sum_univ_two]
  have hdi : dr⁻¹ = dr := inv_eq_of_mul_eq_one_right hdr2
  set m' := dr * m * dr
  have hmul_dr i j : m' i j = (!![(1 : ℝ), 0; 0, -1] * m.val * !![(1 : ℝ), 0; 0, -1]) i j := by simp [m', dr]
  obtain ⟨hI1, hJ1⟩ := hUint m a b rfl rfl e10 e11 hb
  obtain ⟨hI2, hJ2⟩ := hUint m' a (-b) (by rw [hmul_dr]; simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]; rfl)
    (by rw [hmul_dr]; simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]; rfl)
    (by rw [hmul_dr]; simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct, e10])
    (by rw [hmul_dr]; simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct, e11]) (neg_ne_zero.2 hb)
  have hsplit : F m = fun z => U m z + U m' (dr • z) := funext fun z => by
    have hdrs : (dr • z).1 = -z.1 := by rw [coe_smul]; simp [num, den, dr, div_neg]
    have hFm : F m z = F m' (dr • z) := by rw [← hFconj, hdi, show dr * m' * dr = m by simp [m', ← mul_assoc, hdr2]; rw [mul_assoc, hdr2, mul_one]]
    simp only [U]; rcases lt_or_gt_of_ne z.2 with hz | hz
    · rw [ite_eq_right (not_lt.2 hz.le), ite_eq_left (by rw [hdrs, neg_im]; linarith), hFm, zero_add]
    · rw [ite_eq_left hz, ite_eq_right (by rw [hdrs, neg_im]; linarith), add_zero]
  -- Algebraic identity: eta a b ^ k / (1 - eta a b ^ 2) + eta a (-b) ^ k / (1 - eta a (-b) ^ 2) = - ch(2a, a^2+b^2, k-1) * (a^2+b^2)^(1-k/2)
  have hch : eta a b ^ k / (1 - eta a b ^ 2) + eta a (-b) ^ k / (1 - eta a (-b) ^ 2) =
      -((ch (2 * a) (a ^ 2 + b ^ 2) (k - 1) * (a ^ 2 + b ^ 2) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) := by
    have hp : 0 < a ^ 2 + b ^ 2 := by positivity
    set s := √(a ^ 2 + b ^ 2); have hs := sqrt_pos.2 hp; have hss := sq_sqrt hp.le; have hS : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have hr : (a ^ 2 + b ^ 2) ^ (1 - ((n + 2 : ℕ) : ℝ) / 2) = 1 / s ^ n := by
      rw [← hss, ← rpow_natCast s 2, ← rpow_mul hs.le,
        show ((2 : ℕ) : ℝ) * (1 - ((n + 2 : ℕ) : ℝ) / 2) = -(n : ℝ) by push_cast; ring, rpow_neg hs.le, rpow_natCast, one_div]
    rw [hr, show n + 2 - 1 = n + 1 by omega]
    set x : ℂ := (a : ℂ) + b * I; set y : ℂ := (a : ℂ) - b * I; set u := eta a b; set v := eta a (-b)
    have hu : u = y / s := rfl
    have hv : v = x / s := by simp [v, eta, x, s]
    have hxy : x * y = (s : ℂ) ^ 2 := by rw [← ofReal_pow, hss]; push_cast; linear_combination (-(b : ℂ) ^ 2) * I_sq
    have hu0 : u ≠ 0 := div_ne_zero (fun h0 => hb (by simpa [y] using congrArg im h0)) hS
    have hv0 : v ≠ 0 := by rw [hv]; exact div_ne_zero (fun h0 => hb (by simpa [x] using congrArg im h0)) hS
    have huv : u * v = 1 := by rw [hu, hv, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hS hS)]; linear_combination hxy
    have hvu : v - u ≠ 0 := by
      rw [hu, hv, ← sub_div]; refine div_ne_zero ?_ hS
      rw [show x - y = 2 * b * I by simp [x, y]; ring]; exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hb)) I_ne_zero
    have key := ch_mul x y (n + 1)
    rw [show x + y = ((2 * a : ℝ) : ℂ) by simp [x, y]; ring,
      show x * y = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) by rw [hxy, ← ofReal_pow, hss], ← ch_cast] at key
    have hC : ((ch (2 * a) (a ^ 2 + b ^ 2) (n + 1) : ℝ) : ℂ) / (s : ℂ) ^ n * (v - u) = v ^ (n + 1) - u ^ (n + 1) := by
      rw [show x = s * v by rw [hv]; field_simp, show y = s * u by rw [hu]; field_simp, ← mul_sub, mul_pow, mul_pow, ← mul_sub] at key
      rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero n hS)]
      exact mul_left_cancel₀ hS (by calc (s : ℂ) * (((ch (2 * a) (a ^ 2 + b ^ 2) (n + 1) : ℝ) : ℂ) * (v - u))
            = ((ch (2 * a) (a ^ 2 + b ^ 2) (n + 1) : ℝ) : ℂ) * ((s : ℂ) * (v - u)) := by ring
          _ = (s : ℂ) ^ (n + 1) * (v ^ (n + 1) - u ^ (n + 1)) := key
          _ = (s : ℂ) * ((v ^ (n + 1) - u ^ (n + 1)) * (s : ℂ) ^ n) := by rw [pow_succ']; ring)
    have t1 : u ^ (n + 2) / (1 - u ^ 2) = u ^ (n + 1) / (v - u) := by
      rw [show 1 - u ^ 2 = u * (v - u) by linear_combination -huv, pow_succ', mul_div_mul_left _ _ hu0]
    have t2 : v ^ (n + 2) / (1 - v ^ 2) = v ^ (n + 1) / (u - v) := by
      rw [show 1 - v ^ 2 = v * (u - v) by linear_combination -huv, pow_succ', mul_div_mul_left _ _ hv0]
    rw [t1, t2]; push_cast; rw [one_div, ← div_eq_mul_inv, show u - v = -(v - u) by ring, div_neg, ← sub_eq_add_neg, ← sub_div, div_eq_iff hvu]
    linear_combination hC
  obtain ⟨hc1, hc2⟩ := hcomp dr (U m'); obtain ⟨hd1, hd2⟩ := hcomp h (F g)
  have hFmI : Integrable (F m) := hsplit ▸ hI1.add (hc1.2 hI2)
  have hF' : (fun z => F g (h • z)) = F m := funext fun z => (hFconj g h z).symm
  refine ⟨hd1.1 (hF' ▸ hFmI), ?_⟩
  change ∫ z, F g z = _
  rw [htr, hdt, htr', hdt', ← hch, ← hJ1, ← hJ2, ← hd2, hF', hsplit, integral_add hI1 (hc1.2 hI2), hc2]

-- === F3: Elliptic terms contribution ===

theorem elliptic_terms_contribution_proof : B1a → B1b → B1c → B4 → C1 → E0a → KernelTermsInvariantBounded → E0d → Mult → Fcen → F3 := by
  intro hB1a _ _ hB4 _ hE0a _ _ hMult _ F I Gf ι _ _ _ _ D k a hyp γ ω hT hTe
  have : SigmaFinite (volume : Measure P) := hB1a.1
  have htr : γ.out.val.trace ≠ 0 := let ⟨i, hi⟩ := kk_supp D a γ ω hTe; (kk_reg D k a hyp γ ω i hi).1
  have hTv v : (D.r v γ.out).val.trace ^ 2 < 4 * (D.r v γ.out).val.det := by rw [r_tr, r_det]; exact hT v
  let z0 : D.Xs := fun v => ell_fp (D.r v γ.out) (hTv v)
  set S := stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)
  have memS (g : PG F) (hg : g ∈ S) : g * γ * g⁻¹ = γ ∧ g • ω = ω := by
    rw [mem_stabilizer_iff] at hg; exact ⟨congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  have fixS (g : PG F) (hg : g ∈ S) : g • z0 = z0 := by
    have hc : g.out * γ.out = γ.out * g.out := pf_Fcen F γ.out g.out htr (by simpa [QuotientGroup.out_eq'] using (memS g hg).1)
    rw [smulX_out]; exact funext fun v => ell_fix_comm (hTv v) (by rw [← map_mul, ← map_mul, hc])
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink; obtain ⟨s, hs, hsc⟩ := hmink z0 (D.rep ω)
  obtain ⟨C, hC⟩ := hMult F I Gf D hyp.ax 1 c₀ one_pos hc₀
  have hSF : Finite S := ((hC (ω, z0) s hs hsc).1.subset fun g hg =>
    ⟨(memS g hg).2, fun v => by show 1 ≤ kap (z0 v) ((g • z0 : D.Xs) v); rw [fixS g hg, kap_self]⟩).to_subtype
  refine ⟨hSF, fun β hβ => ?_⟩
  let f (v : I) (w : P) := q1 (k v) w (D.r v γ.out • w) * j1 (k v) (D.r v γ.out) w
  have hu (z : D.Xs) : D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) * ∏ v, f v (z v) := by
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) = _; rw [Finset.prod_mul_distrib]; rfl
  have hint : Integrable (fun z : D.Xs => ∏ v, f v (z v)) :=
    Integrable.fintype_prod (f := f) (μ := fun _ => volume) fun v => (hB4 (k v) (hyp.four v) _ (hTv v)).1
  have hval : ∫ z : D.Xs, ∏ v, f v (z v) = D.orb k γ.out := by
    rw [show (∫ z : D.Xs, ∏ v, f v (z v)) = ∫ z : I → P, ∏ v, f v (z v) ∂(Measure.pi fun _ => volume) from rfl, integral_fintype_prod_eq_prod]
    exact Finset.prod_congr rfl fun v _ => by rw [(hB4 (k v) (hyp.four v) _ (hTv v)).2, r_tr, r_det]
  have : Fintype S := Fintype.ofFinite S
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.2 ⟨1⟩
  let c : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcut : IsCut S (fun _ : D.Xs => c) := ⟨measurable_const, fun _ => inv_nonneg.2 hcard.le, fun _ => by
    rw [show (1 : ℝ) = ∑ _ : S, c by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']]; exact hasSum_fintype _⟩
  have hinv (g : S) (z : D.Xs) : D.kk k a γ (ω, g • z) = D.kk k a γ (ω, z) := by
    obtain ⟨h1, h2⟩ := memS g.1 g.2; have := kk_conj D k a hyp g.1 γ (ω, z); rw [h1, show (g.1 : PG F) • ((ω, z) : D.Y) = (ω, g • z) from Prod.ext h2 rfl] at this; exact this
  have hintc : Integrable (fun z : D.Xs => c • D.kk k a γ (ω, z)) :=
    ((hint.const_mul (D.Te a γ.out (D.rep ω))).smul c).congr (ae_of_all _ fun z => by dsimp only [Pi.smul_apply]; rw [hu])
  obtain ⟨-, heq⟩ := (action_integral_swap_proof (↥S) D.Xs volume (fun g => (hE0a F I Gf D hyp.ax).2.2.1 g.1) (fun _ => c) β hcut hβ).2
    (fun z : D.Xs => D.kk k a γ (ω, z)) ((meas_kk D k a hyp γ).comp measurable_prodMk_left) hinv hintc
  rw [← heq]; simp_rw [hu]; rw [integral_smul, integral_const_mul, hval, Nat.card_eq_fintype_card, real_smul]; simp [c]

end UpperTheory.Esk
