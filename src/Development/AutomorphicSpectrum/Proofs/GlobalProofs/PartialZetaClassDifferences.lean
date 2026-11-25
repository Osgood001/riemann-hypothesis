module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTrivialZeros
public import Mathlib.NumberTheory.LSeries.Injectivity
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
noncomputable section

open NumberField Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped nonZeroDivisors Classical

open Complex

/-- The first surviving coefficient is recovered uniformly in the full right half-plane. -/
theorem LSeries.tendsto_cpow_mul_re_atTop {f : ℕ → ℂ} {m : ℕ} (hm : 0 < m)
    (hprev : ∀ k, 0 < k → k < m → f k = 0) (ha : abscissaOfAbsConv f < ⊤) :
    Tendsto (fun s : ℂ => (m : ℂ)^s * LSeries f s) (comap Complex.re atTop) (𝓝 (f m)) := by
  obtain ⟨y, hy, _⟩ := EReal.exists_between_coe_real ha
  let T (s : ℂ) (k : ℕ) := (m : ℂ)^s * term f s k
  have hr : Tendsto Complex.re (comap Complex.re atTop) atTop := tendsto_comap
  have hzero {k : ℕ} (hk : k < m) (s : ℂ) : T s k = 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · simp [T]
    · simp [T, hk₀.ne', hprev k hk₀ hk]
  have hnorm {k : ℕ} (hk : 0 < k) (s : ℂ) : ‖T s k‖ = ‖f k‖ * ((m : ℝ)/k)^s.re := by
    dsimp only [T]
    rw [term_of_ne_zero hk.ne', norm_mul, norm_div, norm_natCast_cpow_of_pos hm,
      norm_natCast_cpow_of_pos hk, Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hlim (k : ℕ) : Tendsto (T · k) (comap Complex.re atTop) (𝓝 (if k = m then f m else 0)) := by
    rcases lt_trichotomy k m with hk | he | hk
    · simpa only [hzero hk, ite_eq_right hk.ne] using (tendsto_const_nhds (x := (0 : ℂ)))
    · subst k
      have eq (s : ℂ) : T s m = f m := by
        dsimp only [T]
        rw [term_of_ne_zero hm.ne', mul_comm]
        exact div_mul_cancel₀ _ (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hm.ne')))
      simpa only [eq, ite_true] using (tendsto_const_nhds (x := f m))
    · rw [ite_eq_right hk.ne']
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp_rw [hnorm (hm.trans hk)]
      have hratio : (m : ℝ)/k < 1 := (div_lt_one (by exact_mod_cast hm.trans hk)).mpr (by exact_mod_cast hk)
      simpa using ((tendsto_rpow_atTop_of_base_lt_one _ (neg_one_lt_zero.trans_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) hratio).comp hr).const_mul ‖f k‖
  have hsum : Summable (T y) := (LSeriesSummable_of_abscissaOfAbsConv_lt_re (s := (y : ℂ)) hy).mul_left _
  have hb : ∀ᶠ s in comap Complex.re atTop, ∀ k, ‖T s k‖ ≤ ‖T y k‖ := by
    filter_upwards [hr.eventually_ge_atTop y] with s hs k
    rcases lt_or_ge k m with hk | hk
    · simp [hzero hk]
    · rw [hnorm (hm.trans_le hk), hnorm (hm.trans_le hk), ofReal_re]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (div_pos (by exact_mod_cast hm) (by exact_mod_cast hm.trans_le hk))
        ((div_le_one (by exact_mod_cast hm.trans_le hk)).mpr (by exact_mod_cast hk)) hs) (norm_nonneg _)
  simpa only [T, LSeries, tsum_mul_left, tsum_ite_eq] using tendsto_tsum_of_dominated_convergence hsum.norm hlim hb

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {F : Type} [Field F] [NumberField F]

/-- Number of integral ideals in one ideal class with a given absolute norm. -/
def classNormCount (C : ClassGroup (𝓞 F)) (n : ℕ) : ℕ :=
  Nat.card {J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} // (J.val : Ideal (𝓞 F)).absNorm = n}

/-- Grouping the class Dirichlet series by norm gives its ordinary L-series coefficients. -/
theorem isPartialZeta_LSeriesHasSum {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (classNormCount C n : ℂ)) s (Z s) := by
  let N (J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C}) := (J.val : Ideal (𝓞 F)).absNorm
  refine ((hZ.2 s hs).tsum_fiberwise N).congr_fun (fun n => ?_)
  have hsn : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [LSeries.term_of_ne_zero' hsn]
  symm
  calc
    (∑' J : N ⁻¹' {n}, ((Ideal.absNorm (J.val.val : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s)) =
      ∑' _ : N ⁻¹' {n}, (n : ℂ) ^ (-s) := tsum_congr (fun J => by
        change (N J.val : ℂ) ^ (-s) = _
        rw [show N J.val = n from J.prop])
    _ = _ := by rw [tsum_const, nsmul_eq_mul, Complex.cpow_neg, div_eq_mul_inv]; rfl

private theorem classCoeff_abscissa_lt_top {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) :
    LSeries.abscissaOfAbsConv (fun n => (classNormCount C n : ℂ)) < ⊤ :=
  (isPartialZeta_LSeriesHasSum hZ (s := 2) (by norm_num)).LSeriesSummable.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)

/-- Equality away from the pole is equivalent to agreement of all ideal counts. -/
theorem isPartialZeta_eqOn_iff_norm_counts {C D : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta D W) :
    Set.EqOn Z W {1}ᶜ ↔ ∀ n ≠ 0, classNormCount C n = classNormCount D n := by
  constructor
  · intro h n hn
    apply Nat.cast_injective (R := ℂ)
    apply LSeries.eq_of_LSeries_eventually_eq (classCoeff_abscissa_lt_top hZ) (classCoeff_abscissa_lt_top hW) _ hn
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hs : 1 < (x : ℂ).re := by simpa using hx
    refine (isPartialZeta_LSeriesHasSum hZ hs).LSeries_eq.trans ((h ?_).trans (isPartialZeta_LSeriesHasSum hW hs).LSeries_eq.symm)
    rintro (ha : (x : ℂ) = 1)
    exact (ne_of_gt hx) (by exact_mod_cast ha)
  · intro h
    apply isPartialZeta_eqOn hZ
    refine ⟨hW.1, fun s hs => ?_⟩
    have hZW : Z s = W s := (isPartialZeta_LSeriesHasSum hZ hs).LSeries_eq.symm.trans
      ((LSeries_congr (fun {n} hn => congrArg (fun k : ℕ => (k : ℂ)) (h n hn)) s).trans
        (isPartialZeta_LSeriesHasSum hW hs).LSeries_eq)
    exact hZW ▸ hZ.2 s hs

/-- After every smaller positive norm cancels, the scaled difference of two class zetas
recovers the signed multiplicity difference, uniformly in the entire right half-plane. -/
theorem isPartialZeta_tendsto_sub_first {C D : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta D W) {m : ℕ} (hm : 0 < m)
    (hp : ∀ k, 0 < k → k < m → classNormCount C k = classNormCount D k) :
    Tendsto (fun s : ℂ => (m : ℂ) ^ s * (Z s - W s)) (comap Complex.re atTop)
      (𝓝 ((classNormCount C m : ℂ) - classNormCount D m)) := by
  let f := fun k => (classNormCount C k : ℂ)
  let g := fun k => (classNormCount D k : ℂ)
  have hz (k : ℕ) (hk : 0 < k) (hkm : k < m) : (f - g) k = 0 := by simp [f, g, hp k hk hkm]
  have h := LSeries.tendsto_cpow_mul_re_atTop hm hz
    ((LSeries.abscissaOfAbsConv_sub_le f g).trans_lt
      (max_lt (classCoeff_abscissa_lt_top hZ) (classCoeff_abscissa_lt_top hW)))
  apply h.congr'
  filter_upwards [(tendsto_comap (f := Complex.re)).eventually_gt_atTop 1] with s hs
  have hz' := isPartialZeta_LSeriesHasSum hZ hs
  have hw' := isPartialZeta_LSeriesHasSum hW hs
  simp only [f, g, LSeries_sub hz'.LSeriesSummable hw'.LSeriesSummable, hz'.LSeries_eq, hw'.LSeries_eq]

/-- Two genuinely distinct ordinary class zetas cannot coincide arbitrarily far to the right. -/
theorem isPartialZeta_exists_right_halfPlane_ne {C D : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta D W) (h : ¬ Set.EqOn Z W {1}ᶜ) :
    ∃ R : ℝ, ∀ s : ℂ, R ≤ s.re → Z s ≠ W s := by
  have hex : ∃ n : ℕ, classNormCount C (n + 1) ≠ classNormCount D (n + 1) := by
    by_contra! h'
    apply h ((isPartialZeta_eqOn_iff_norm_counts hZ hW).mpr ?_)
    rintro (_ | n) hn
    · exact (hn rfl).elim
    · exact h' n
  let n := Nat.find hex
  have hp (k : ℕ) (hk : 0 < k) (hk' : k < n + 1) : classNormCount C k = classNormCount D k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact not_ne_iff.mp (Nat.find_min hex (show j < n by omega))
  have hne : (classNormCount C (n + 1) : ℂ) ≠ classNormCount D (n + 1) := by exact_mod_cast Nat.find_spec hex
  have hscaled := (isPartialZeta_tendsto_sub_first hZ hW (Nat.succ_pos n) hp).eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp hscaled)
  exact ⟨R, fun s hs he => hR _ hs s rfl (by simp [he])⟩

theorem classNormCount_one (C : ClassGroup (𝓞 F)) : classNormCount C 1 = if C = 1 then 1 else 0 := by
  let T := {J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} // (J.val : Ideal (𝓞 F)).absNorm = 1}
  have hone (J : T) : J.val.val = 1 := Subtype.ext ((Ideal.absNorm_eq_one_iff.mp J.prop).trans Ideal.one_eq_top.symm)
  by_cases h : C = 1
  · subst C
    let one : T := ⟨⟨1, map_one _⟩, map_one _⟩
    let : Unique T := ⟨⟨one⟩, fun j => Subtype.ext (Subtype.ext (hone j))⟩
    simpa [classNormCount, T] using Nat.card_unique (α := T)
  · let : IsEmpty T := ⟨fun J => h (by simpa [hone J] using J.val.prop.symm)⟩
    simpa [classNormCount, T, h] using Nat.card_of_isEmpty (α := T)

/-- Uniformly in the imaginary part, only the principal class contributes at norm one. -/
theorem isPartialZeta_tendsto_re_atTop {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ} (hZ : IsPartialZeta C Z) :
    Tendsto Z (comap Complex.re atTop) (𝓝 (if C = 1 then (1 : ℂ) else 0)) := by
  have h := LSeries.tendsto_cpow_mul_re_atTop (m := 1) zero_lt_one (fun k hk hk' => by omega)
    (classCoeff_abscissa_lt_top hZ)
  have lim : Tendsto (fun s : ℂ => LSeries (fun n => (classNormCount C n : ℂ)) s) (comap Complex.re atTop)
      (𝓝 (if C = 1 then (1 : ℂ) else 0)) := by
    simpa [classNormCount_one, apply_ite] using h
  apply lim.congr'
  filter_upwards [(tendsto_comap (f := Complex.re)).eventually_gt_atTop 1] with s hs
  exact (isPartialZeta_LSeriesHasSum hZ hs).LSeries_eq

theorem isPartialZeta_principal_sub_tendsto {C : ClassGroup (𝓞 F)} (hC : C ≠ 1) {P Z : ℂ → ℂ}
    (hP : IsPartialZeta (1 : ClassGroup (𝓞 F)) P) (hZ : IsPartialZeta C Z) :
    Tendsto (fun s : ℂ => P s - Z s) (comap Complex.re atTop) (𝓝 1) := by
  simpa [hC] using (isPartialZeta_tendsto_re_atTop hP).sub (isPartialZeta_tendsto_re_atTop hZ)

/-- On sufficiently large positive integers the principal partial zeta genuinely exceeds every fixed
nonprincipal one (after taking real parts, so the assertion does not use a complex order). -/
theorem isPartialZeta_principal_eventually_gt_nat {C : ClassGroup (𝓞 F)} (hC : C ≠ 1) {P Z : ℂ → ℂ}
    (hP : IsPartialZeta (1 : ClassGroup (𝓞 F)) P) (hZ : IsPartialZeta C Z) :
    ∀ᶠ n : ℕ in atTop, (Z (n : ℂ)).re < (P (n : ℂ)).re := by
  have hl := (Complex.continuous_re.tendsto (1 : ℂ)).comp (isPartialZeta_principal_sub_tendsto hC hP hZ)
  have hl := hl.comp (show Tendsto (fun x : ℝ => (x : ℂ)) atTop (comap Complex.re atTop) by rw [tendsto_comap_iff]; exact tendsto_id)
  have hr : ∀ᶠ x : ℝ in atTop, (Z (x : ℂ)).re < (P (x : ℂ)).re := by
    simpa [Function.comp_def] using hl.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < (1 : ℂ).re))
  simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hr



/-- One half-plane works simultaneously for all class pairs of a fixed field. At any one
point there, agreement detects precisely equality of the class partial zetas away from one. -/
theorem isPartialZeta_exists_field_sample :
    ∃ R : ℝ, ∀ s : ℂ, R ≤ s.re → ∀ (C D : ClassGroup (𝓞 F)) {Z W : ℂ → ℂ},
      IsPartialZeta C Z → IsPartialZeta D W → (Z s = W s ↔ Set.EqOn Z W {1}ᶜ) := by
  have h (C D : ClassGroup (𝓞 F)) : ∀ᶠ x : ℝ in atTop, ∀ s : ℂ, x ≤ s.re →
      zetaOfClass C s = zetaOfClass D s → Set.EqOn (zetaOfClass C) (zetaOfClass D) {1}ᶜ := by
    by_cases e : Set.EqOn (zetaOfClass C) (zetaOfClass D) {1}ᶜ
    · exact .of_forall (fun _ _ _ _ => e)
    obtain ⟨r, hr⟩ := isPartialZeta_exists_right_halfPlane_ne (isPartialZeta_zetaOfClass C) (isPartialZeta_zetaOfClass D) e
    exact (eventually_ge_atTop r).mono (fun x hx s hs he => (hr s (hx.trans hs) he).elim)
  have hall := (Filter.eventually_all.mpr fun C => Filter.eventually_all.mpr (h C)).and (eventually_gt_atTop (1 : ℝ))
  obtain ⟨R, hp, hR⟩ := hall.exists
  refine ⟨R, fun s hs C D Z W hZ hW => ?_⟩
  have hs1 : s ∈ ({1}ᶜ : Set ℂ) := by rintro rfl; have := hR.trans_le hs; norm_num at this
  have e := isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C)
  have e' := isPartialZeta_eqOn hW (isPartialZeta_zetaOfClass D)
  exact ⟨fun he => e.trans ((hp C D s hs ((e hs1).symm.trans (he.trans (e' hs1)))).trans e'.symm), fun he => he hs1⟩


open NumberField.InfinitePlace GroundTheory.Global GlobalTheory.CompanionTheory.PartialZeta

/-- Every zero not forced by the archimedean factors lies in a field-dependent vertical strip,
uniformly for every nonzero ordinary class difference. Outside the left edge its zeros and their multiplicities are
exactly the forced archimedean ones. No effective or universal strip width is asserted. -/
theorem isPartialZeta_exists_field_strip (F : Type) [Field F] [NumberField F] :
    ∃ R : ℝ, 1 < R ∧ ∀ {C B : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ},
      IsPartialZeta C Z → IsPartialZeta B W → ¬ Set.EqOn Z W {1}ᶜ →
        (∀ s : ℂ, R ≤ s.re → Z s ≠ W s) ∧
        (∀ s : ℂ, s.re ≤ 1 - R → (Z s = W s ↔ classGamma F s = 0)) ∧
        (∀ n : ℕ, R ≤ 1 + (n : ℝ) → analyticOrderAt (fun s => Z s - W s) (-(n : ℂ)) =
          (if Even n then (nrRealPlaces F : ℕ∞) else 0) + nrComplexPlaces F) := by
  obtain ⟨r, hr⟩ := isPartialZeta_exists_field_sample (F := F)
  let R := max r 2
  have hrR : r ≤ R := le_max_left _ _
  have hR : 1 < R := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right _ _)
  refine ⟨R, hR, ?_⟩
  intro C B Z W hZ hW hne
  let D : (Ideal (𝓞 F))⁰ := ⟨differentIdeal ℤ (𝓞 F), mem_nonZeroDivisors_of_ne_zero _root_.differentIdeal_ne_bot⟩
  let C' := C⁻¹ * ClassGroup.mk0 D
  let B' := B⁻¹ * ClassGroup.mk0 D
  have hC : C * C' = ClassGroup.mk0 D := by simp [C']
  have hB : B * B' = ClassGroup.mk0 D := by simp [B']
  have hfe := completedZetaOfClass_sub_reflect C B C' B' D rfl hC hB
  have hdual : ¬ Set.EqOn (zetaOfClass C') (zetaOfClass B') {1}ᶜ := by
    intro eq
    have hdiff : (fun t => completedZetaOfClass C' t - completedZetaOfClass B' t) = fun _ => 0 := by
      apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (differentiable_completedZetaOfClass_sub C' B')).eq_of_eventuallyEq analyticOnNhd_const (z₀ := 2)
      have hO : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hO.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with t ht
      have h1 : t ≠ 1 := by rintro rfl; norm_num at ht
      have hγ := classGamma_ne_of_re_pos (F := F) (zero_lt_one.trans ht)
      simp only [completedZetaOfClass_eq C' hγ, completedZetaOfClass_eq B' hγ, eq h1, sub_self]
    apply hne
    intro s hs
    have hzero := (congrFun hfe s).trans (congrFun hdiff (1 - s))
    apply sub_eq_zero.mp
    rw [isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) hs,
      isPartialZeta_eqOn hW (isPartialZeta_zetaOfClass B) hs,
      zetaOfClass_sub_eq_normalized C B s, hzero, mul_zero]
  have hright (t : ℂ) (ht : r ≤ t.re) : zetaOfClass C' t ≠ zetaOfClass B' t :=
    fun e => hdual ((hr t ht C' B' (isPartialZeta_zetaOfClass C') (isPartialZeta_zetaOfClass B')).mp e)
  refine ⟨fun s hs e => hne ((hr s (hrR.trans hs) C B hZ hW).mp e), ?_, ?_⟩
  · intro s hs
    have h1 : s ≠ 1 := by intro e; subst s; simp at hs; linarith
    have ht : r ≤ (1 - s).re := by simp; linarith
    have hcomp : completedZetaOfClass C s - completedZetaOfClass B s ≠ 0 := by
      rw [congrFun hfe s]
      intro h
      exact hright _ ht (sub_eq_zero.mp (by rw [zetaOfClass_sub_eq_normalized C' B' _, h, mul_zero]))
    have hd : (dF F : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (abs_ne_zero.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))
    rw [← sub_eq_zero, isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) h1,
      isPartialZeta_eqOn hW (isPartialZeta_zetaOfClass B) h1, zetaOfClass_sub_eq_normalized]
    simp [hcomp, cpow_ne_zero_iff.mpr (Or.inl hd)]
  · intro n hn
    have hnr : r ≤ (1 + (n : ℂ)).re := by simpa using hrR.trans hn
    have horder : analyticOrderAt (fun t => zetaOfClass C' t - zetaOfClass B' t) (1 + (n : ℂ)) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr (hright _ hnr)))
    rw [isPartialZeta_sub_order_reflected hZ hW D rfl hC hB, horder, add_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂
