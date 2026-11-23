import B0

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === Shared algebraic & analytic lemmas (reused across B1..B5) ===

lemma j1_one (k : ℕ) (z : P) : j1 k 1 z = 1 := by simp [j1, den]

lemma j1_scalar (k : ℕ) (g : GL2 ℝ) (hb : g 0 1 = 0) (hc : g 1 0 = 0) (h : g 0 0 = g 1 1) (z : P) :
    j1 k g z = ((SignType.sign (g 0 0) : ℝ) : ℂ) ^ k := by
  have ha : g 0 0 ≠ 0 := fun h0 => g.det_ne_zero (by simp [det_eq, hb, hc, h0, ← h])
  have hdet : |g.val.det| = |g 0 0| ^ 2 := by rw [det_eq, hb, hc, ← h]; simp [sq, abs_mul]
  have hr : |g.val.det| ^ (-(k : ℝ) / 2) = (|g 0 0| ^ k)⁻¹ := by
    rw [hdet, neg_div, rpow_neg (sq_nonneg _), sq_rpow_half (abs_nonneg _)]
  have hkey : g 0 0 ^ k * (|g 0 0| ^ k)⁻¹ = (SignType.sign (g 0 0) : ℝ) ^ k := by
    rw [show g 0 0 ^ k = (SignType.sign (g 0 0) : ℝ) ^ k * |g 0 0| ^ k by rw [← mul_pow, sign_mul_abs],
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.2 ha)), mul_one]
  calc j1 k g z = ((g 0 0 ^ k * (|g 0 0| ^ k)⁻¹ : ℝ) : ℂ) := by
        simp [j1, den, hc, h, hr]
    _ = _ := by rw [hkey, ofReal_pow]

lemma qj_conj (k : ℕ) (G g : GL2 ℝ) (w : P) :
    q1 k (G • w) (G • g • w) * j1 k (G * g * G⁻¹) (G • w) = q1 k w (g • w) * j1 k g w := by
  have hAB : j1 k G⁻¹ (G • w) * j1 k G w = 1 := by rw [← j1_mul, inv_mul_cancel, j1_one]
  have e1 : j1 k (G * g * G⁻¹) (G • w) = j1 k G (g • w) * j1 k g w * j1 k G⁻¹ (G • w) := by
    rw [j1_mul, inv_smul_smul, j1_mul]
  rw [e1]
  linear_combination (j1 k g w * j1 k G⁻¹ (G • w)) * q1_smul k G w (g • w) + (q1 k w (g • w) * j1 k g w) * hAB

lemma norm_qj (k : ℕ) (hk : 1 ≤ k) (g : GL2 ℝ) (z : P) :
    ‖q1 k z (g • z) * j1 k g z‖ = ((k : ℝ) - 1) / (4 * π) * kap z (g • z) ^ ((k : ℝ) / 2) := by
  have ha : 0 < |z.1.im| ^ ((k : ℝ) / 2) := rpow_pos_of_pos (abs_pos.2 z.2) _
  have hb : 0 < |(g • z).1.im| ^ ((k : ℝ) / 2) := rpow_pos_of_pos (abs_pos.2 (g • z).2) _
  rw [norm_mul]
  apply mul_right_cancel₀ (mul_pos ha hb).ne'
  calc ‖q1 k z (g • z)‖ * ‖j1 k g z‖ * (|z.1.im| ^ ((k : ℝ) / 2) * |(g • z).1.im| ^ ((k : ℝ) / 2))
      = (‖q1 k z (g • z)‖ * |z.1.im| ^ ((k : ℝ) / 2)) * (‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2)) := by ring
    _ = _ := by rw [norm_j1, norm_q1 k z (g • z) hk]; ring

lemma nrm_pos {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => rpow_pos_of_pos (abs_pos.2 (z v).2) _

lemma nrm_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 ≤ nrm k z := (nrm_pos k z).le

lemma Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun _ _ => rpow_nonneg (kap_nonneg _ _) _

lemma Kap_symm {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : Kap k z w = Kap k w z :=
  Finset.prod_congr rfl fun v _ => by rw [kap_symm]

def cst {I : Type} [Fintype I] (k : I → ℕ) : ℝ := ∏ v, ((k v : ℝ) - 1) / (4 * π)

lemma cst_nonneg {I : Type} [Fintype I] (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) : 0 ≤ cst k :=
  Finset.prod_nonneg fun v _ => div_nonneg (by have : (1 : ℝ) ≤ k v := (by exact_mod_cast hk v); linarith) (by positivity)

lemma norm_qq {I : Type} [Fintype I] (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (z w : X I) :
    ‖qq k z w‖ * nrm k z = cst k * Kap k z w * nrm k w := by
  simp only [qq, nrm, Kap, cst, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => norm_q1 (k v) (z v) (w v) (hk v)

lemma vecMul_ne {F : Type} [Field F] {s : Fin 2 → F} (hs : s ≠ 0) (γ : GL2 F) : s ᵥ* γ.val ≠ 0 := fun h => hs $ by
  have := congrArg (· ᵥ* (γ⁻¹ : GL2 F).val) h
  simpa [Matrix.vecMul_vecMul] using this

lemma fix_mk {F : Type} [Field F] (t : Fin 2 → F) (g : GL2 F) : Fix t (g : PG F) ↔ ∃ c : F, t ᵥ* g.val = c • t := by
  obtain ⟨ζ, e⟩ := QuotientGroup.mk_out_eq_mul (center (GL2 F)) g
  obtain ⟨h1, h2, h3⟩ := center_entries ζ.2
  have hl : ζ.1 0 0 ≠ 0 := fun h0 => ζ.1.det_ne_zero (by rw [det_fin_two, h1, ← h3, h0]; ring)
  have hv (u : Fin 2 → F) : u ᵥ* ζ.1.val = ζ.1 0 0 • u := funext fun i => by
    fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two, h1, h2, h3, mul_comm]
  unfold Fix; rw [e, Units.val_mul, ← vecMul_vecMul, hv]
  exact ⟨fun ⟨c, hc⟩ => ⟨(ζ.1 0 0)⁻¹ * c, by rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hl, one_smul]⟩,
    fun ⟨c, hc⟩ => ⟨ζ.1 0 0 * c, by rw [hc, smul_smul]⟩⟩

lemma fix_conj {F : Type} [Field F] (s : Fin 2 → F) (γ δ : GL2 F) :
    Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔ ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val) := by
  rw [show (δ : PG F) * γ * (δ : PG F)⁻¹ = ((δ * γ * δ⁻¹ : GL2 F) : PG F) by simp, fix_mk]
  refine exists_congr fun c => ?_
  simp only [Units.val_mul, ← vecMul_vecMul]
  exact ⟨fun h => by have := congrArg (· ᵥ* δ.val) h; simpa [vecMul_vecMul, smul_vecMul] using this,
    fun h => by have := congrArg (· ᵥ* (δ⁻¹ : GL2 F).val) h; simpa [vecMul_vecMul, smul_vecMul] using this⟩

lemma row_exists {F : Type} [Field F] (s : Fin 2 → F) (hs : s ≠ 0) : ∃ γ : GL2 F, ![0, 1] ᵥ* γ.val = s := by
  by_cases h0 : s 0 = 0
  · have h1 : s 1 ≠ 0 := fun h1 => hs (funext fun i => by fin_cases i <;> simp [h0, h1])
    exact ⟨GeneralLinearGroup.mkOfDetNeZero !![1, 0; s 0, s 1] (by simp [det_fin_two_of, h1]),
      funext fun i => by fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two]⟩
  · exact ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 1; s 0, s 1] (by simp [det_fin_two_of, h0]),
      funext fun i => by fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two]⟩

section DatLemmas
variable {F I Gf ι : Type} [Field F] [Group Gf] (D : Dat F I Gf)

lemma r_det (v : I) (γ : GL2 F) : (D.r v γ).val.det = D.σ v γ.val.det := by
  rw [det_fin_two, det_fin_two, map_sub, map_mul, map_mul]; rfl

lemma r_tr (v : I) (γ : GL2 F) : (D.r v γ).val.trace = D.σ v γ.val.trace := by
  rw [trace_fin_two, trace_fin_two, map_add]; rfl

lemma ee_mul_left (h : D.H) (u : Gf) : D.ee (h * u) = D.χ h * D.ee u := by
  unfold Dat.ee; by_cases hu : u ∈ D.H
  · rw [dite_eq_left (D.H.mul_mem h.2 hu), dite_eq_left hu]; exact congrArg Units.val (map_mul D.χ h ⟨u, hu⟩)
  · rw [dite_eq_right (fun hm => hu (by simpa using D.H.mul_mem (D.H.inv_mem h.2) hm)), dite_eq_right hu, mul_zero]

lemma ee_mul_right (u : Gf) (h : D.H) : D.ee (u * h) = D.ee u * D.χ h := by
  unfold Dat.ee; by_cases hu : u ∈ D.H
  · rw [dite_eq_left (D.H.mul_mem hu h.2), dite_eq_left hu]; exact congrArg Units.val (map_mul D.χ ⟨u, hu⟩ h)
  · rw [dite_eq_right (fun hm => hu (by simpa using D.H.mul_mem hm (D.H.inv_mem h.2))), dite_eq_right hu, zero_mul]

lemma ee_inv_mul (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) = (D.χ h : ℂ)⁻¹ * D.ee u := by
  simpa [Units.val_inv_eq_inv_val] using ee_mul_left D h⁻¹ u

lemma ee_one : D.ee 1 = 1 := by unfold Dat.ee; rw [dite_eq_left D.H.one_mem]; exact congrArg Units.val (map_one D.χ)

lemma smul_center (v : I) (c : GL2 F) (hc : c ∈ center (GL2 F)) (w : P) : D.r v c • w = w := by
  obtain ⟨h1, h2, h3⟩ := center_entries hc
  exact center_smul _ (by change D.σ v (c 0 1) = 0; rw [h1, map_zero])
    (by change D.σ v (c 1 0) = 0; rw [h2, map_zero]) (by change D.σ v (c 0 0) = D.σ v (c 1 1); rw [h3]) w

lemma act_center (c : GL2 F) (hc : c ∈ center (GL2 F)) (z : X I) : D.act c z = z :=
  funext fun v => smul_center D v c hc (z v)

lemma act_mul (g h : GL2 F) (z : X I) : D.act (g * h) z = D.act g (D.act h z) :=
  funext fun v => by change D.r v (g * h) • z v = _; rw [map_mul, mul_smul]; rfl

lemma smulO_out (γ : PG F) (ω : D.Om) : γ • ω = ((D.j γ.out * D.rep ω : Gf) : Gf ⧸ D.H) := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ, ← QuotientGroup.out_eq' ω]
  exact D.mk_smulO γ.out (D.rep ω)

lemma smulX_out (γ : PG F) (w : D.Xs) : (γ • w : D.Xs) = D.act γ.out w := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ]
  exact D.mk_smulX γ.out w

variable [Fintype I]

lemma norm_ee_le (hx : D.Ax) (u : Gf) : ‖D.ee u‖ ≤ 1 := by
  unfold Dat.ee; split_ifs with hu; exact (hx.χn _).le; simp

lemma J_mul (k : I → ℕ) (g h : GL2 F) (w : X I) : D.J k (g * h) w = D.J k g (D.act h w) * D.J k h w := by
  simp only [Dat.J, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => by rw [map_mul]; exact j1_mul _ _ _ _

lemma J_center (k : I → ℕ) (hC : D.Compat k) (c : GL2 F) (hc : c ∈ center (GL2 F)) (w : X I) :
    D.J k c w = D.χ ⟨D.j c, D.cenH c hc⟩ := by
  rw [hC c hc]; obtain ⟨h1, h2, h3⟩ := center_entries hc
  exact Finset.prod_congr rfl fun v _ => j1_scalar (k v) (D.r v c)
    (by change D.σ v (c 0 1) = 0; rw [h1, map_zero]) (by change D.σ v (c 1 0) = 0; rw [h2, map_zero])
    (by change D.σ v (c 0 0) = D.σ v (c 1 1); rw [h3]) (w v)

lemma Kap_smul (k : I → ℕ) (δ : PG F) (z w : D.Xs) : Kap k (δ • z : D.Xs) (δ • w : D.Xs) = Kap k z w :=
  Finset.prod_congr rfl fun v _ => by rw [kap_smulX]

lemma Kap_swap (k : I → ℕ) (γ : PG F) (z w : D.Xs) : Kap k z (γ • w : D.Xs) = Kap k w (γ⁻¹ • z : D.Xs) := by
  rw [← Kap_smul D k γ⁻¹ z (γ • w), inv_smul_smul]; exact Kap_symm k _ _

lemma norm_qJ (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (g : GL2 F) (z w : X I) :
    ‖qq k z (D.act g w) * D.J k g w‖ * nrm k z = cst k * Kap k z (D.act g w) * nrm k w := by
  simp only [qq, Dat.J, Dat.act, nrm, Kap, cst, norm_mul, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have h1 := norm_q1 (k v) (z v) (D.r v g • w v) (hk v)
  have h2 := norm_j1 (k v) (D.r v g) (w v)
  calc ‖q1 (k v) (z v) (D.r v g • w v)‖ * ‖j1 (k v) (D.r v g) (w v)‖ * |(z v).1.im| ^ ((k v : ℝ) / 2)
      = (‖q1 (k v) (z v) (D.r v g • w v)‖ * |(z v).1.im| ^ ((k v : ℝ) / 2)) * ‖j1 (k v) (D.r v g) (w v)‖ := by ring
    _ = _ := by rw [h1, ← h2]; ring

-- === KernelTermsInvariantBounded ===

lemma norm_Te_le [Fintype ι] (hx : D.Ax) (a : ι → Gf) (γ : GL2 F) (x : Gf) : ‖D.Te a γ x‖ ≤ Fintype.card ι :=
  (norm_sum_le _ _).trans $ (Finset.sum_le_sum fun _ _ => norm_ee_le D hx _).trans (by simp)

lemma kt_mul_center [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hC : D.Compat k) (γ c : GL2 F)
    (hc : c ∈ center (GL2 F)) (z : X I) (x : Gf) : D.kt k a (γ * c) z x = D.kt k a γ z x := by
  have hT : D.Te a (γ * c) x = (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ)⁻¹ * D.Te a γ x := by
    rw [Dat.Te, Dat.Te, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc' := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ (D.cenC c hc)) x⁻¹
    rw [show x⁻¹ * (D.j (γ * c))⁻¹ * x * a i = (D.j c)⁻¹ * (x⁻¹ * (D.j γ)⁻¹ * x * a i) by
      rw [map_mul, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, ← mul_assoc, hc']; group]
    exact ee_inv_mul D ⟨D.j c, D.cenH c hc⟩ _
  unfold Dat.kt; rw [act_mul, act_center D c hc, J_mul, act_center D c hc, J_center D k hC c hc, hT]
  have hne : (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ) ≠ 0 := Units.ne_zero _
  linear_combination (D.Te a γ x * (qq k z (D.act γ z) * D.J k γ z)) * inv_mul_cancel₀ hne

lemma kt_mul_H [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hG : D.Good a) (γ : GL2 F) (z : X I) (x : Gf) (h : D.H) :
    D.kt k a γ z (x * h) = D.kt k a γ z x := by
  have key := hG (fun y => D.ee ((x⁻¹ * (D.j γ)⁻¹ * x) * y))
    (fun y h' => by rw [← mul_assoc, ee_mul_right, mul_comm]) 1 h
  simp only [one_mul] at key
  unfold Dat.kt; congr 1; unfold Dat.Te
  have e1 i : (x * ↑h)⁻¹ * (D.j γ)⁻¹ * (x * ↑h) * a i = (h : Gf)⁻¹ * ((x⁻¹ * (D.j γ)⁻¹ * x) * (h * a i)) := by group
  rw [Finset.sum_congr rfl fun i _ => by rw [e1, ee_inv_mul], ← Finset.mul_sum, key, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

lemma kt_conj [Fintype ι] (k : I → ℕ) (a : ι → Gf) (d g : GL2 F) (z : X I) (x : Gf) :
    D.kt k a (d * g * d⁻¹) (D.act d z) (D.j d * x) = D.kt k a g z x := by
  have hT : D.Te a (d * g * d⁻¹) (D.j d * x) = D.Te a g x :=
    Finset.sum_congr rfl fun i _ => congrArg D.ee (by simp only [map_mul, map_inv]; group)
  have hQ : qq k (D.act d z) (D.act (d * g * d⁻¹) (D.act d z)) * D.J k (d * g * d⁻¹) (D.act d z) =
      qq k z (D.act g z) * D.J k g z := by
    simp only [qq, Dat.J, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    change q1 (k v) (D.r v d • z v) (D.r v (d * g * d⁻¹) • D.r v d • z v) * j1 (k v) (D.r v (d * g * d⁻¹)) (D.r v d • z v) = _
    rw [smul_smul, ← map_mul, inv_mul_cancel_right, map_mul, mul_smul, map_mul, map_mul, map_inv]
    exact qj_conj (k v) (D.r v d) (D.r v g) (z v)
  unfold Dat.kt; rw [hT, hQ]

lemma kk_mk [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (g : GL2 F) (x : Gf) (z : X I) :
    D.kk k a (g : PG F) (((x : Gf ⧸ D.H) : D.Om), (z : D.Xs)) = D.kt k a g z x := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (center (GL2 F)) g
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul D.H x
  change D.kt k a (g : PG F).out z (Quotient.out (x : Gf ⧸ D.H)) = D.kt k a g z x
  rw [hc, hh, kt_mul_center D k a hH.compat g c c.2, kt_mul_H D k a hH.good]

lemma kk_conj [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (δ γ : PG F) (y : D.Y) :
    D.kk k a (δ * γ * δ⁻¹) (δ • y) = D.kk k a γ y := by
  obtain ⟨y1, y2⟩ := y; obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  obtain ⟨x, rfl⟩ : ∃ x : Gf, ((x : Gf ⧸ D.H) : D.Om) = y1 := QuotientGroup.mk_surjective y1
  rw [show (d : PG F) * g * (d : PG F)⁻¹ = ((d * g * d⁻¹ : GL2 F) : PG F) by simp,
    show (d : PG F) • ((((x : Gf ⧸ D.H) : D.Om), y2) : D.Y) = ((((D.j d * x : Gf) : Gf ⧸ D.H) : D.Om), D.act d y2) from
      Prod.ext (D.mk_smulO d x) (D.mk_smulX d y2)]
  calc _ = D.kt k a (d * g * d⁻¹) (D.act d y2) (D.j d * x) := kk_mk D k a hH _ _ _
    _ = D.kt k a g y2 x := kt_conj D k a d g y2 x
    _ = _ := (kk_mk D k a hH _ _ _).symm

lemma meas_kk [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (γ : PG F) : Measurable (D.kk k a γ) := by
  have := hH.ax.cO
  refine measurable_from_prod_countable_right fun ω => ?_
  have hc : Continuous fun z : X I => qq k z (D.act γ.out z) * D.J k γ.out z :=
    (continuous_finsetProd _ fun v _ => (cont_q1 (k v)).comp ((continuous_apply v).prodMk
      ((cont_smul_P (D.r v γ.out)).comp (continuous_apply v)))).mul
      (continuous_finsetProd _ fun v _ => (cont_j1 (k v) (D.r v γ.out)).comp (continuous_apply v))
  show Measurable fun z : D.Xs => D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z)
  exact measurable_const.mul hc.measurable

lemma norm_kk_le [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (γ : PG F) (y : D.Y) :
    ‖D.kk k a γ y‖ ≤ (Fintype.card ι * cst k) * Kap k y.2 (γ • y.2 : D.Xs) := by
  rw [smulX_out]; unfold Dat.kk Dat.kt; rw [norm_mul, mul_assoc]
  have hQJ : ‖qq k y.2 (D.act γ.out y.2) * D.J k γ.out y.2‖ = cst k * Kap k y.2 (D.act γ.out y.2) := by
    simp only [qq, Dat.J, Dat.act, Kap, cst, norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => norm_qj (k v) (le_trans (by norm_num) (hH.four v)) (D.r v γ.out) (y.2 v)
  have h0 := norm_nonneg (qq k y.2 (D.act γ.out y.2) * D.J k γ.out y.2)
  rw [hQJ] at h0 ⊢; exact mul_le_mul_of_nonneg_right (norm_Te_le D hH.ax a γ.out _) h0

omit [Fintype I] in
lemma kk_supp [Fintype ι] (a : ι → Gf) (γ : PG F) (y : D.Om) (hT : D.Te a γ.out (D.rep y) ≠ 0) :
    ∃ i, γ • y = ((D.rep y * a i : Gf) : Gf ⧸ D.H) := by
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hT
  have hm : (D.rep y)⁻¹ * (D.j γ.out)⁻¹ * D.rep y * a i ∈ D.H := by by_contra hn; exact hi (by simp [Dat.ee, hn])
  exact ⟨i, by rw [smulO_out]; exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hm)⟩

lemma kk_reg [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (γ : PG F) (y : D.Om) (i : ι)
    (hγ : γ • y = ((D.rep y * a i : Gf) : Gf ⧸ D.H)) :
    γ.out.val.trace ≠ 0 ∧ γ.out.val.trace ^ 2 ≠ 4 * γ.out.val.det := by
  rw [smulO_out] at hγ
  exact hH.reg γ.out (D.rep y) i (by
    rw [show (a i)⁻¹ * ((D.rep y)⁻¹ * D.j γ.out * D.rep y) = ((D.j γ.out * D.rep y)⁻¹ * (D.rep y * a i))⁻¹ by group]
    exact D.H.inv_mem (QuotientGroup.eq.1 hγ))

-- === E0d: Heights on quotient ===

lemma htY_mk (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (z : X I) (x : Gf) :
    D.HtY s ((((x : Gf ⧸ D.H) : D.Om), (z : D.Xs)) : D.Y) = D.Ht s z x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul D.H x
  simp only [Dat.HtY, Dat.Ht, Dat.rep]; rw [hh, hA.lev s hs x h h.2]

lemma htY_smul (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (γ : GL2 F) (y : D.Y) :
    D.HtY s ((γ : PG F) • y) = D.HtY (s ᵥ* γ.val) y := by
  obtain ⟨ω, z⟩ := y
  obtain ⟨x, rfl⟩ : ∃ x : Gf, ((x : Gf ⧸ D.H) : D.Om) = ω := QuotientGroup.mk_surjective ω
  have e0 : (γ : PG F) • ((((x : Gf ⧸ D.H) : D.Om), z) : D.Y) = ((((D.j γ * x : Gf) : Gf ⧸ D.H) : D.Om), (D.act γ z : D.Xs)) :=
    Prod.ext (D.mk_smulO γ x) (D.mk_smulX γ z)
  have h1 : D.HtY s ((γ : PG F) • ((((x : Gf ⧸ D.H) : D.Om), z) : D.Y)) = D.Ht s (D.act γ z) (D.j γ * x) :=
    (congrArg (D.HtY s) e0).trans (htY_mk D hA s hs (D.act γ z) (D.j γ * x))
  have h2 : D.HtY (s ᵥ* γ.val) ((((x : Gf ⧸ D.H) : D.Om), z) : D.Y) = D.Ht (s ᵥ* γ.val) z x :=
    htY_mk D hA _ (vecMul_ne hs γ) z x
  rw [h1, h2]
  simp only [Dat.Ht, Dat.act, ← hA.rat s hs γ x]
  have key v : |(D.r v γ • z v).1.im| / ‖(D.σ v (s 0) : ℂ) * (D.r v γ • z v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 =
      |D.σ v γ.val.det| * (|(z v).1.im| / ‖(D.σ v ((s ᵥ* γ.val) 0) : ℂ) * (z v).1 + (D.σ v ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2) := by
    have h0 := den_ne (D.r v γ) (z v).2
    have e : (D.σ v (s 0) : ℂ) * (D.r v γ • z v).1 + (D.σ v (s 1) : ℂ) =
        ((D.σ v ((s ᵥ* γ.val) 0) : ℂ) * (z v).1 + (D.σ v ((s ᵥ* γ.val) 1) : ℂ)) / den (D.r v γ) (z v).1 := by
      rw [coe_smul, eq_div_iff h0, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
      simp only [num, den, vecMul, dotProduct, Fin.sum_univ_two, map_add, map_mul]
      change (D.σ v (s 0) : ℂ) * ((D.σ v (γ 0 0) : ℂ) * (z v).1 + D.σ v (γ 0 1)) +
          D.σ v (s 1) * ((D.σ v (γ 1 0) : ℂ) * (z v).1 + D.σ v (γ 1 1)) = _
      push_cast; ring
    have hn : 0 < ‖den (D.r v γ) (z v).1‖ ^ 2 := by positivity
    rw [e, im_smul, r_det, norm_div, div_pow, abs_div, abs_mul, normSq_eq_norm_sq,
      abs_of_nonneg hn.le, div_div_div_cancel_right₀ hn.ne', mul_div_assoc]
  rw [Finset.prod_congr rfl fun v _ => key v, Finset.prod_mul_distrib]; ring

lemma htY_smulc (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (c : F) (hc : c ≠ 0) : D.HtY (c • s) = D.HtY s := by
  funext y; simp only [Dat.HtY, Dat.Ht, hA.smul s hs c hc]
  have key v : |(y.2 v).1.im| / ‖(D.σ v ((c • s) 0) : ℂ) * (y.2 v).1 + (D.σ v ((c • s) 1) : ℂ)‖ ^ 2 =
      (|(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2) / D.σ v c ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, ofReal_mul]
    rw [show (D.σ v c : ℂ) * D.σ v (s 0) * (y.2 v).1 + D.σ v c * D.σ v (s 1) =
        D.σ v c * (D.σ v (s 0) * (y.2 v).1 + D.σ v (s 1)) by ring, norm_mul, norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, div_div, mul_comm (D.σ v c ^ 2)]
  rw [Finset.prod_congr rfl fun v _ => key v, Finset.prod_div_distrib]
  have hp : ∏ v, D.σ v c ^ 2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero 2 ((map_ne_zero _).2 hc)
  field_simp

omit [Fintype I] in
lemma lin_ne (s : Fin 2 → F) (hs : s ≠ 0) (v : I) (z : P) : (D.σ v (s 0) : ℂ) * z.1 + (D.σ v (s 1) : ℂ) ≠ 0 := fun h => by
  have h1 := congrArg im h; have h2 := congrArg re h; simp at h1 h2
  have a0 : s 0 = 0 := h1.resolve_right z.2
  rw [a0, map_zero, zero_mul, zero_add] at h2
  exact hs $ funext fun i => by fin_cases i; exact a0; exact (map_eq_zero _).1 h2

lemma htY_pos (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (y : D.Y) : 0 < D.HtY s y :=
  mul_pos (Finset.prod_pos fun v _ => div_pos (abs_pos.2 (y.2 v).2) (pow_pos (norm_pos_iff.2 (lin_ne D s hs v _)) 2))
    (hA.pos s hs _)

lemma htY_prod (hA : D.Ax) (s s' : Fin 2 → F) (hd : s 0 * s' 1 - s 1 * s' 0 ≠ 0) (y : D.Y) :
    D.HtY s y * D.HtY s' y ≤ 1 := by
  have hs : s ≠ 0 := by rintro rfl; simp at hd
  have hs' : s' ≠ 0 := by rintro rfl; simp at hd
  have hl v : |(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 *
      (|(y.2 v).1.im| / ‖(D.σ v (s' 0) : ℂ) * (y.2 v).1 + (D.σ v (s' 1) : ℂ)‖ ^ 2) *
      D.σ v (s 0 * s' 1 - s 1 * s' 0) ^ 2 ≤ 1 := by
    set a := D.σ v (s 0); set b := D.σ v (s 1); set a' := D.σ v (s' 0); set b' := D.σ v (s' 1); set z := y.2 v
    have hw := norm_pos_iff.2 (lin_ne D s hs v z); have hw' := norm_pos_iff.2 (lin_ne D s' hs' v z)
    have hkey : |z.1.im| * |a * b' - b * a'| ≤ ‖(a : ℂ) * z.1 + b‖ * ‖(a' : ℂ) * z.1 + b'‖ := by
      have e : (((a : ℂ) * z.1 + b) * conj ((a' : ℂ) * z.1 + b')).im = (a * b' - b * a') * z.1.im := by simp; ring
      calc _ = |(((a : ℂ) * z.1 + b) * conj ((a' : ℂ) * z.1 + b')).im| := by rw [e, abs_mul, mul_comm]
        _ ≤ _ := (abs_im_le_norm _).trans_eq (by rw [norm_mul, norm_conj])
    rw [map_sub, map_mul, map_mul, ← sq_abs (a * b' - b * a'), div_mul_div_comm, div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [pow_le_pow_left₀ (by positivity) hkey 2]
  simp only [Dat.HtY, Dat.Ht]
  calc _ = ((∏ v, |(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2) *
          (∏ v, |(y.2 v).1.im| / ‖(D.σ v (s' 0) : ℂ) * (y.2 v).1 + (D.σ v (s' 1) : ℂ)‖ ^ 2)) *
          (D.hf s (D.rep y.1) * D.hf s' (D.rep y.1)) := by ring
    _ ≤ _ * ∏ v, D.σ v (s 0 * s' 1 - s 1 * s' 0) ^ 2 := mul_le_mul_of_nonneg_left (hA.prod s s' hd _) (by positivity)
    _ = ∏ v, _ := by rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => by positivity) fun v _ => hl v

lemma meas_htY (hA : D.Ax) (s : Fin 2 → F) : Measurable (D.HtY s) := by
  have := hA.cO
  refine measurable_from_prod_countable_right fun ω => ?_
  have hp : Measurable fun z : D.Xs => ∏ v, |(z v).1.im| / ‖(D.σ v (s 0) : ℂ) * (z v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 :=
    Finset.measurable_prod _ fun v _ => by
      have hz : Measurable fun z : D.Xs => (z v).1 := measurable_subtype_coe.comp (measurable_pi_apply v)
      have h1 : Measurable fun z : D.Xs => |(z v).1.im| := continuous_abs.measurable.comp (measurable_im.comp hz)
      have h2 : Measurable fun z : D.Xs => ‖(D.σ v (s 0) : ℂ) * (z v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 :=
        ((measurable_const.mul hz).add measurable_const).norm.pow_const 2
      exact h1.div h2
  exact hp.mul_const (D.hf s (D.rep ω))

lemma meas_lam (hA : D.Ax) (T : ℝ) : MeasurableSet (D.abelian₂ T) := by
  have := hA.cF
  rw [show D.abelian₂ T = ⋂ s : Fin 2 → F, ⋂ (_ : s ≠ 0), {y | D.HtY s y ≤ T} from Set.ext fun _ => by simp [Dat.abelian₂]]
  exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ => measurableSet_le (meas_htY D hA s) measurable_const

lemma lam_smul (hA : D.Ax) (T : ℝ) (δ : PG F) (y : D.Y) (h : y ∈ D.abelian₂ T) : δ • y ∈ D.abelian₂ T := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ
  intro s hs; rw [htY_smul D hA s hs]; exact h _ (vecMul_ne hs d)

lemma meas_lamF (hA : D.Ax) (T : ℝ) (γ : PG F) : MeasurableSet (D.LamF T γ) := by
  have := hA.cF
  rw [show D.LamF T γ = ⋂ s : Fin 2 → F, ⋂ (_ : s ≠ 0), ⋂ (_ : Fix s γ), {y | D.HtY s y ≤ T} from Set.ext fun _ => by simp [Dat.LamF]]
  exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    measurableSet_le (meas_htY D hA s) measurable_const

lemma lamF_smul (hA : D.Ax) (T : ℝ) (γ δ : PG F) (y : D.Y) (h : y ∈ D.LamF T γ) :
    δ • y ∈ D.LamF T (δ * γ * δ⁻¹) := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ; obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  intro s hs hf; rw [htY_smul D hA s hs]; exact h _ (vecMul_ne hs d) ((fix_mk _ g).2 ((fix_conj s g d).1 hf))

lemma htY_bdd (hA : D.Ax) (y : D.Y) : ∃ T₀, ∀ T, T₀ ≤ T → y ∈ D.abelian₂ T := by
  by_cases h : ∃ s0 : Fin 2 → F, s0 ≠ 0 ∧ 1 < D.HtY s0 y
  · obtain ⟨s0, h0, h1⟩ := h
    refine ⟨max 1 (D.HtY s0 y), fun T hT s hs => ?_⟩
    by_cases h2 : D.HtY s y ≤ 1
    · exact h2.trans ((le_max_left _ _).trans hT)
    · push Not at h2
      by_cases hd : s0 0 * s 1 - s0 1 * s 0 = 0
      · have hline : ∃ c : F, c ≠ 0 ∧ s = c • s0 := by
          by_cases a : s0 0 = 0
          · have b : s0 1 ≠ 0 := fun b => h0 (funext fun i => by fin_cases i <;> simp [a, b])
            have hs0 : s 0 = 0 := (mul_eq_zero.1 (by linear_combination -hd + a * s 1)).resolve_left b
            refine ⟨s 1 / s0 1, fun hc => hs (funext fun i => by fin_cases i <;> simp [hs0, (div_eq_zero_iff.1 hc).resolve_right b]),
              funext fun i => by fin_cases i <;> simp [hs0, a, b]⟩
          · refine ⟨s 0 / s0 0, fun hc => hs (funext fun i => by
                have e0 := (div_eq_zero_iff.1 hc).resolve_right a
                have e1 := (mul_eq_zero.1 (show s0 0 * s 1 = 0 by linear_combination hd + s0 1 * e0)).resolve_left a
                fin_cases i <;> simp [e0, e1]),
              funext fun i => by fin_cases i; simp [a]; simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]; field_simp; linear_combination hd⟩
        obtain ⟨c, hc, rfl⟩ := hline; rw [htY_smulc D hA s0 h0 c hc]; exact (le_max_right _ _).trans hT
      · exfalso; nlinarith [htY_prod D hA s0 s hd y]
  · push Not at h; exact ⟨1, fun T hT s hs => (h s hs).trans hT⟩

end DatLemmas

theorem kernel_terms_invariant_bounded_proof : B1a → B1b → KernelTermsInvariantBounded :=
  fun _ _ _ _ _ _ _ _ _ _ D k a hH =>
    ⟨fun γ z x => kk_mk D k a hH γ x z, kk_conj D k a hH, meas_kk D k a hH,
     ⟨_, norm_kk_le D k a hH⟩, kk_supp D a, kk_reg D k a hH⟩

theorem heights_on_quotient_proof : B1a → E0d := fun _ _ _ _ _ _ _ D hA =>
  ⟨htY_mk D hA, htY_smul D hA, htY_smulc D hA, htY_pos D hA, htY_prod D hA, meas_htY D hA,
   fun T => ⟨meas_lam D hA T, fun δ y => ⟨fun h => by simpa [inv_smul_smul] using lam_smul D hA T δ⁻¹ _ h, lam_smul D hA T δ y⟩⟩,
   fun T γ => ⟨meas_lamF D hA T γ, fun δ y => ⟨fun h => by
     have := lamF_smul D hA T _ δ⁻¹ _ h; rwa [inv_smul_smul, show δ⁻¹ * (δ * γ * δ⁻¹) * δ⁻¹⁻¹ = γ by group] at this, lamF_smul D hA T γ δ y⟩⟩,
   htY_bdd D hA, row_exists, fix_conj⟩

-- === KapInt & KapSum & E2 ===

lemma lint_prod {I : Type} [Fintype I] [SigmaFinite (volume : Measure P)]
    (f : I → P → ℝ) (hf0 : ∀ v x, 0 ≤ f v x) (hm : ∀ v, Measurable (f v))
    (C : I → ℝ≥0) (hC : ∀ v, ∫⁻ x, oR (f v x) ≤ C v) :
    ∫⁻ w : I → P, oR (∏ v, f v (w v)) ≤ ((∏ v, C v : ℝ≥0) : ℝ≥0∞) := by
  have hint v : Integrable (f v) := ⟨(hm v).aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hf0 v))]; exact (hC v).trans_lt ENNReal.coe_lt_top⟩
  have hP : Integrable (fun w : I → P => ∏ v, f v (w v)) := by rw [volume_pi]; exact Integrable.fintype_prod hint
  rw [← ofReal_integral_eq_lintegral_ofReal hP (ae_of_all _ fun w => Finset.prod_nonneg fun v _ => hf0 v _),
    integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg (hf0 v)), ENNReal.ofNNReal_finsetProd]
  exact Finset.prod_le_prod fun v _ => by rw [ofReal_integral_eq_lintegral_ofReal (hint v) (ae_of_all _ (hf0 v))]; exact hC v

theorem pf_KapInt : B1a → B1b → B1c → B6 → KapInt := by
  intro hA _ _ h6 I _ k hk
  have : SigmaFinite (volume : Measure P) := hA.1
  choose Cv hCv using fun v => h6 (k v) (hk v)
  have hA' : ((∏ v, toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) : ℝ≥0) : ℝ) =
      ∏ v, (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [NNReal.coe_prod]; exact Finset.prod_congr rfl fun v _ => coe_toNNReal _ (by positivity)
  have har1 (z w w' : P) (h : 1 / 2 ≤ kap w w') (e : ℝ) (he : 0 ≤ e) : kap z w ^ e ≤ (8 : ℝ) ^ e * kap z w' ^ e := by
    rw [← mul_rpow (by norm_num) (kap_nonneg _ _)]
    exact rpow_le_rpow (kap_nonneg _ _) (by nlinarith [kap_tri z w w', mul_le_mul_of_nonneg_left h (kap_nonneg z w)]) he
  have har2 (z w w' : P) (h : 1 / 2 ≤ kap w w') : (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) := by
    have hw := abs_pos.2 w.2; have hw' := abs_pos.2 w'.2
    rw [← mul_rpow (by norm_num) (div_nonneg (abs_nonneg _) hw'.le)]
    refine rpow_le_rpow (div_nonneg (abs_nonneg _) hw.le) ?_ (by norm_num)
    rw [mul_div_assoc', div_le_div_iff₀ hw hw']
    nlinarith [mul_le_mul_of_nonneg_left (show |w'.1.im| ≤ 8 * |w.1.im| by nlinarith [kap_im_le w w', mul_le_mul_of_nonneg_right h hw'.le]) (abs_nonneg z.1.im)]
  refine ⟨∏ v, Cv v, ∏ v, toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)), fun z => ?_⟩
  have hkm v : Measurable (kap (z v)) := (cont_kap.comp (continuous_const.prodMk continuous_id)).measurable
  have hm2 v : Measurable fun w : P => kap (z v) w ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) := by
    have hi : Measurable fun w : P => |w.1.im| := continuous_abs.measurable.comp (measurable_im.comp measurable_subtype_coe)
    exact ((hkm v).pow_const _).mul ((measurable_const.div hi).pow_const _)
  have hsplit (w : X I) : Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2) =
      ∏ v, (kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) :=
    (Finset.prod_mul_distrib).symm
  refine ⟨Finset.measurable_prod _ fun v _ => ((hkm v).comp (measurable_pi_apply v)).pow_const _,
    lint_prod (fun v w => kap (z v) w ^ ((k v : ℝ) / 2)) (fun _ _ => rpow_nonneg (kap_nonneg _ _) _)
      (fun v => (hkm v).pow_const _) Cv fun v => (hCv v (z v)).1,
    by simp only [hsplit]; exact lint_prod (fun v w => kap (z v) w ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |w.1.im|) ^ ((1 : ℝ) / 2))
        (fun v w => mul_nonneg (rpow_nonneg (kap_nonneg _ _) _) (rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _))
        hm2 Cv fun v => (hCv v (z v)).2,
    fun w w' hn => ⟨?_, ?_⟩⟩
  · simp only [Kap]; rw [hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => rpow_nonneg (kap_nonneg _ _) _) fun v _ => ?_
    have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) := one_le_rpow (by norm_num) (by norm_num)
    have e1 := har1 (z v) (w v) (w' v) (hn v) ((k v : ℝ) / 2) (by positivity)
    have hp : 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) :=
      mul_nonneg (by positivity) (rpow_nonneg (kap_nonneg _ _) _)
    nlinarith [mul_le_mul_of_nonneg_left h8 hp]
  · rw [hsplit w, hsplit w', hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => mul_nonneg (rpow_nonneg (kap_nonneg _ _) _) (by positivity)) fun v _ => ?_
    have e1 := har1 (z v) (w v) (w' v) (hn v) ((k v : ℝ) / 2) (by positivity)
    have e2 := har2 (z v) (w v) (w' v) (hn v)
    calc _ ≤ _ * _ := mul_le_mul e1 e2 (by positivity) (mul_nonneg (by positivity) (rpow_nonneg (kap_nonneg _ _) _))
      _ = _ := by ring

theorem pf_KapSum : Pack → Mult → KapInt → KapSum := by
  intro hPack hMult hKap F I Gf _ _ _ D hD k hk c₀ hc₀
  obtain ⟨C₁, hC₁⟩ := hPack F I Gf D hD; obtain ⟨C₃, A₃, hK⟩ := hKap I k hk
  obtain ⟨C₂, hC₂⟩ := hMult F I Gf D hD (1 / 16) c₀ (by norm_num) hc₀
  refine ⟨(C₁ : ℝ) * A₃ * max C₂ 0 * C₃, fun y s hs hy ω' z => ?_⟩
  obtain ⟨hfin, hcard⟩ := hC₂ y s hs hy; obtain ⟨hmeas, hint, -, hnear⟩ := hK z
  have hcard' : (({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℕ) : ℝ≥0∞) ≤
      oR (max C₂ 0 * (1 + D.HtY s y)) := by
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)))
  have hA (w w' : D.Xs) (hww : Near (1 / 2) w w') : oR (Kap k z w) ≤ (A₃ : ℝ≥0∞) * oR (Kap k z w') :=
    (ENNReal.ofReal_le_ofReal (hnear w w' hww).1).trans_eq
      ((ENNReal.ofReal_mul A₃.2).trans (congrArg (· * oR (Kap k z w')) ENNReal.ofReal_coe_nnreal))
  refine (hC₁ y ω' (fun w => oR (Kap k z w)) A₃ (ENNReal.measurable_ofReal.comp hmeas) hA hfin).trans ?_
  calc _ ≤ (C₁ : ℝ≥0∞) * A₃ * oR (max C₂ 0 * (1 + D.HtY s y)) * C₃ := by gcongr; exact hint
    _ = _ := by rw [show (C₁ : ℝ) * A₃ * max C₂ 0 * C₃ * (1 + D.HtY s y) =
          ((C₁ * A₃ * C₃ : ℝ≥0) : ℝ) * (max C₂ 0 * (1 + D.HtY s y)) by push_cast; ring,
        ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]; push_cast; ring

theorem kernel_sum_bounded_proof : KernelTermsInvariantBounded → E0d → KapSum → E2 := by
  intro _ _ hks F I Gf ι _ _ _ _ D k a hyp
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨C, hC⟩ := hks F I Gf D hyp.ax k hyp.four c₀ hc₀
  set C₀ : ℝ := Fintype.card ι * cst k
  have key T (y : D.Y) (hy : y ∈ D.abelian₂ T) :
      ∑' γ : PG F, ‖D.kk k a γ y‖ₑ ≤ Fintype.card ι * (oR C₀ * oR (max C 0 * (1 + T))) := by
    obtain ⟨s, hs, hcs⟩ := hmink y.2 (D.rep y.1)
    have hcs' : c₀ ≤ D.HtY s y := hcs
    have hle : D.HtY s y ≤ T := hy s hs
    let S i := {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
    let g (γ : PG F) := oR C₀ * oR (Kap k y.2 (γ • y.2 : D.Xs))
    have hpt γ : ‖D.kk k a γ y‖ₑ ≤ ∑ i, (S i).indicator g γ := by
      by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
      · simp [Dat.kk, Dat.kt, h0]
      · obtain ⟨i, hi⟩ := kk_supp D a γ y.1 h0
        refine le_trans ?_ (Finset.single_le_sum (f := fun j => (S j).indicator g γ) (fun _ _ => zero_le) (Finset.mem_univ i))
        rw [indicator_of_mem (show γ ∈ S i from hi)]
        exact (ofReal_norm _).symm.trans_le
          ((ENNReal.ofReal_le_ofReal (norm_kk_le D k a hyp γ y)).trans_eq (ENNReal.ofReal_mul' (Kap_nonneg k _ _)))
    calc _ ≤ ∑' γ, ∑ i, (S i).indicator g γ := ENNReal.tsum_le_tsum hpt
      _ = ∑ i, ∑' γ, (S i).indicator g γ := Summable.tsum_finsetSum fun _ _ => ENNReal.summable
      _ ≤ ∑ _i : ι, oR C₀ * oR (max C 0 * (1 + T)) := Finset.sum_le_sum fun i _ => by
            rw [← _root_.tsum_subtype, ENNReal.tsum_mul_left]; gcongr
            exact (hC y s hs hcs' _ y.2).trans (ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_left _ _) (by linarith) (by linarith) (le_max_right _ _)))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨fun y => ?_, fun T => ⟨Fintype.card ι * (C₀.toNNReal * (max C 0 * (1 + T)).toNNReal), fun y hy => ?_⟩⟩
  · obtain ⟨T₀, hT₀⟩ := htY_bdd D hyp.ax y
    have hnt : (Fintype.card ι : ℝ≥0∞) * (oR C₀ * oR (max C 0 * (1 + T₀))) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    exact (ENNReal.summable_toReal (ne_top_of_le_ne_top hnt (key T₀ y (hT₀ T₀ le_rfl)))).congr fun _ => toReal_enorm _
  · exact (key T y hy).trans (le_of_eq (by simp [oR, ENNReal.ofReal]))

-- === C2: Orbit cover & partition of unity ===

lemma exists_cut {G Y : Type} [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y]
    (hm : ∀ g : G, Measurable fun y : Y => g • y) (u : Y → ℝ) (hu : Measurable u)
    (h0 : ∀ y, 0 ≤ u y) (hpos : ∀ y, ∃ g : G, 0 < u (g • y)) (hs : ∀ y, Summable fun g : G => u (g • y)) :
    ∃ b : Y → ℝ, IsCut G b := by
  have hsm : Measurable fun y => ∑' g : G, u (g • y) := by
    rw [show (fun y => ∑' g : G, u (g • y)) = fun y => (∑' g : G, oR (u (g • y))).toReal from funext fun y => by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => h0 _) (hs y), ENNReal.toReal_ofReal (tsum_nonneg fun _ => h0 _)]]
    exact (Measurable.tsum fun g => (hu.comp (hm g)).ennreal_ofReal).ennreal_toReal
  have hspos y : 0 < ∑' g : G, u (g • y) := let ⟨g, hg⟩ := hpos y; hg.trans_le ((hs y).le_tsum g fun _ _ => h0 _)
  refine ⟨fun y => u y / ∑' g : G, u (g • y), hu.div hsm, fun y => div_nonneg (h0 y) (hspos y).le, fun y => ?_⟩
  have e : (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) = fun g => u (g • y) / ∑' h : G, u (h • y) :=
    funext fun g => congrArg (u (g • y) / ·) (by simp only [smul_smul]; exact (Equiv.mulRight g).tsum_eq fun h => u (h • y))
  show HasSum _ 1; rw [e, ← div_self (hspos y).ne']; exact (hs y).hasSum.div_const _

lemma orbit_cover {G Y : Type} [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y]
    (μ : Measure Y) (hP : Pres G μ) (b : Y → ℝ) (hb : IsCut G b) (S : Set Y)
    (hS : MeasurableSet S) (hc : ∀ y : Y, ∃ g : G, g • y ∈ S) : ∫⁻ y, oR (b y) ∂μ ≤ μ S := by
  have hF (g : G) : Measurable (S.indicator fun y => oR (b (g⁻¹ • y))) :=
    (hb.meas.ennreal_ofReal.comp (hP g⁻¹).measurable).indicator hS
  have hone y : ∑' g : G, oR (b (g⁻¹ • y)) = 1 := by
    rw [show (∑' g : G, oR (b (g⁻¹ • y))) = ∑' g : G, oR (b (g • y)) from (Equiv.inv G).tsum_eq (fun g : G => oR (b (g • y))),
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => hb.nonneg _) (hb.sum y).summable, (hb.sum y).tsum_eq, ENNReal.ofReal_one]
  calc ∫⁻ y, oR (b y) ∂μ ≤ ∫⁻ y, ∑' g : G, S.indicator (fun y => oR (b (g⁻¹ • y))) (g • y) ∂μ :=
        lintegral_mono fun y => let ⟨g, hg⟩ := hc y; le_trans (by rw [indicator_of_mem hg, inv_smul_smul]) (ENNReal.le_tsum g)
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => oR (b (g⁻¹ • y))) (g • y) ∂μ :=
        lintegral_tsum fun g => ((hF g).comp (hP g).measurable).aemeasurable
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => oR (b (g⁻¹ • y))) y ∂μ := tsum_congr fun g => (hP g).lintegral_comp (hF g)
    _ = ∫⁻ y, ∑' g : G, S.indicator (fun y => oR (b (g⁻¹ • y))) y ∂μ := (lintegral_tsum fun g => (hF g).aemeasurable).symm
    _ = ∫⁻ y, S.indicator 1 y ∂μ := lintegral_congr fun y => by by_cases hy : y ∈ S <;> simp [indicator, hy, hone]
    _ = μ S := lintegral_indicator_one hS

theorem orbit_cover_proof : C2 := fun _ _ _ _ _ _ => ⟨exists_cut, orbit_cover⟩

-- === Ecut ===

theorem pf_Ecut : B1b → B1c → C2 → E0a → E0d → KapSum → Ecut := by
  intro _ _ _ hE _ hK F I Gf _ _ _ D hax
  obtain ⟨hcount, -, hpres, -⟩ := hE F I Gf D hax
  have : Countable (PG F) := hcount; have : Countable D.Om := hax.cO
  obtain ⟨c₀, hc₀, hmk⟩ := hax.mink
  obtain ⟨C, hCK⟩ := hK F I Gf D hax (fun _ => 4) (fun _ => le_rfl) c₀ hc₀
  let iN : P := ⟨-Complex.I, by simp⟩
  let bs (e : I → Bool) : X I := fun v => if e v then iP else iN
  let uX (z : X I) : ℝ := ∑ e : I → Bool, Kap (fun _ => 4) (bs e) z
  have hu0 z : 0 ≤ uX z := Finset.sum_nonneg fun _ _ => Kap_nonneg _ _ _
  have hupos z : 0 < uX z := Finset.sum_pos' (fun _ _ => Kap_nonneg _ _ _)
    ⟨fun v => decide (0 < (z v).1.im), Finset.mem_univ _, Finset.prod_pos fun v _ => rpow_pos_of_pos (by
      unfold kap bs; by_cases h : 0 < (z v).1.im
      · simp only [h, decide_true, ↓reduceIte, iP]; rw [ite_eq_left (by simpa using h)]
        exact div_pos (by simp; linarith) (pos_den_conj (by simpa using h))
      · have h' : (z v).1.im < 0 := lt_of_le_of_ne (not_lt.1 h) (z v).2
        simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, iN]; rw [ite_eq_left (by simp; linarith)]
        exact div_pos (by simp; linarith) (pos_den_conj (by simp; linarith))) _⟩
  have hucont : Continuous uX := continuous_finsetSum _ fun _ _ => continuous_finsetProd _ fun v _ =>
    (cont_kap.comp (continuous_const.prodMk (continuous_apply v))).rpow_const fun _ => Or.inr (by positivity)
  have hsplit z : oR (uX z) = ∑ e : I → Bool, oR (Kap (fun _ => 4) (bs e) z) :=
    ENNReal.ofReal_sum_of_nonneg fun _ _ => Kap_nonneg _ _ _
  have hfib (y : D.Y) : ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ (e : I → Bool) (ω' : D.Om),
      ∑' γ : {γ : PG F // γ • y.1 = ω'}, oR (Kap (fun _ => 4) (bs e) (γ.1 • y.2 : D.Xs)) ≤ M :=
    let ⟨s, hs, hsy⟩ := hmk y.2 (D.rep y.1); ⟨_, ENNReal.ofReal_ne_top, fun e ω' => hCK y s hs hsy ω' (bs e)⟩
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat D.Om
  let w (ω : D.Om) : ℝ := (1 / 2 : ℝ) ^ f ω
  have hW : ∑' ω, oR (w ω) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, (1 / 2 : ℝ) ^ n)) $
      (ENNReal.tsum_comp_le_tsum_of_injective hf fun n => oR ((1 / 2 : ℝ) ^ n)).trans_eq
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) summable_geometric_two).symm
  have hm1 : Measurable fun y : D.Y => w y.1 := (Measurable.of_discrete (f := w)).comp measurable_fst
  have hm2 : Measurable fun y : D.Y => uX y.2 := hucont.measurable.comp measurable_snd
  refine ⟨exists_cut (fun g => (Measurable.of_discrete.comp measurable_fst).prodMk ((hpres g).measurable.comp measurable_snd))
      (fun y => w y.1 * uX y.2) (hm1.mul hm2)
      (fun y => mul_nonneg (by positivity) (hu0 _))
      (fun y => ⟨1, by simpa using mul_pos (by positivity : (0 : ℝ) < w y.1) (hupos y.2)⟩) fun y => ?_,
    fun ω S hS => exists_cut (fun g : S => (hpres (g : PG F)).measurable) uX hucont.measurable hu0
      (fun z => ⟨1, by simpa using hupos z⟩) fun z => ?_⟩
  · obtain ⟨M, hM, hMb⟩ := hfib y
    have hle : ∑' g : PG F, oR (w (g • y).1 * uX (g • y).2) ≤ ∑ _e : I → Bool, (∑' ω, oR (w ω)) * M := by
      calc _ = ∑' g : PG F, ∑ e : I → Bool, oR (w (g • y.1)) * oR (Kap (fun _ => 4) (bs e) (g • y.2 : D.Xs)) :=
              tsum_congr fun g => (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ w (g • y.1))).trans
                ((congrArg (oR (w (g • y.1)) * ·) (hsplit (g • y.2 : X I))).trans (Finset.mul_sum _ _ _))
        _ = ∑ e : I → Bool, ∑' g : PG F, oR (w (g • y.1)) * oR (Kap (fun _ => 4) (bs e) (g • y.2 : D.Xs)) :=
              Summable.tsum_finsetSum fun _ _ => ENNReal.summable
        _ ≤ _ := Finset.sum_le_sum fun e _ => by
              rw [← ENNReal.tsum_fiberwise _ (fun g : PG F => g • y.1), ← ENNReal.tsum_mul_right]
              exact ENNReal.tsum_le_tsum fun ω' => by
                rw [show (∑' b : (fun g : PG F => g • y.1) ⁻¹' {ω'}, oR (w (b.1 • y.1)) * oR (Kap (fun _ => 4) (bs e) (b.1 • y.2 : D.Xs)))
                  = oR (w ω') * ∑' b : {g : PG F // g • y.1 = ω'}, oR (Kap (fun _ => 4) (bs e) (b.1 • y.2 : D.Xs)) by
                    rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun b => by rw [show b.1 • y.1 = ω' from b.2]]
                gcongr; exact hMb e ω'
    exact (ENNReal.summable_toReal (ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun _ _ => ENNReal.mul_lt_top hW.lt_top hM.lt_top).ne hle)).congr
      fun _ => ENNReal.toReal_ofReal (mul_nonneg (by positivity) (hu0 _))
  · obtain ⟨M, hM, hMb⟩ := hfib ((ω, z) : D.Y)
    have hinj : Injective (fun g : S => (⟨(g : PG F), hS g.2⟩ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω})) :=
      fun _ _ h => Subtype.ext (congrArg (fun x : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} => x.1) h)
    have hle : ∑' g : S, oR (uX (g • z : D.Xs)) ≤ ∑ _e : I → Bool, M := by
      calc _ = ∑' g : S, ∑ e : I → Bool, oR (Kap (fun _ => 4) (bs e) (g • z : D.Xs)) := tsum_congr fun _ => hsplit _
        _ = ∑ e : I → Bool, ∑' g : S, oR (Kap (fun _ => 4) (bs e) (g • z : D.Xs)) := Summable.tsum_finsetSum fun _ _ => ENNReal.summable
        _ ≤ _ := Finset.sum_le_sum fun e _ => (ENNReal.tsum_comp_le_tsum_of_injective hinj
            fun γ => oR (Kap (fun _ => 4) (bs e) (γ.1 • z : D.Xs))).trans (hMb e ω)
    exact (ENNReal.summable_toReal (ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun _ _ => hM.lt_top).ne hle)).congr
      fun _ => ENNReal.toReal_ofReal (hu0 _)

end UpperTheory.Esk
