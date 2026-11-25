module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCMTypeEmbedding
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem completed_eq {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L) {s : ℂ}
    (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) : Λ s = archFactor n s * L s := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hA : ∀ (z : ℂ) i, (2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2))) ≠ 0 := fun z i =>
    mul_ne_zero two_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  let g : ℂ → ℂ := fun z => Λ z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
    (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹)
  have key : ∀ z : ℂ, (∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) → archFactor n z *
      ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹) = 1 := fun z hz => by
    unfold archFactor
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [mul_mul_mul_comm, mul_inv_cancel₀ (hA z i), mul_inv_cancel₀ (hz i), one_mul]
  have hg : Differentiable ℂ g := by
    refine h.1.mul (Differentiable.fun_finsetProd fun i _ => ?_)
    refine Differentiable.mul (fun z => ?_) ?_
    · refine DifferentiableAt.inv ?_ (hA z i)
      exact (((differentiableAt_id.add_const _).neg).const_cpow (Or.inl hpi)).const_mul 2
    · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have hgL : g = L := entire_eq_of_halfPlane hg hL.1 1 fun z hz => by
    have hz' : ∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => Complex.Gamma_ne_zero_of_re_pos (by
      have : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
      simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
      norm_num
      have := abs_nonneg (n i)
      have h2 : (0:ℝ) ≤ |(n i : ℝ)| := abs_nonneg _
      linarith)
    show Λ z * _ = L z
    rw [h.eq_mul hL hz, mul_comm (archFactor n z), mul_assoc, key z hz', mul_one]
  calc Λ s = Λ s * (archFactor n s * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))⁻¹)) := by rw [key s hs, mul_one]
    _ = archFactor n s * g s := by ring
    _ = archFactor n s * L s := by rw [hgL]

end GlobalTheory.LValNe

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

omit [Fintype I] in
theorem nonempty_of_isCMType [Fintype I] {φ : I → E →+* ℂ} (hφ : IsCMType φ) : Nonempty I := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  obtain ⟨i, -⟩ := hφ w.embedding
  exact ⟨i⟩

theorem exists_heckeL [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ)
    (hm : HasInf χ φ m) (hpos : ∀ i, 0 < m i) : ∃ Λ, IsHeckeL χ Λ := by
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  exact GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ m χ hφ hu hm ⟨i₀, (hpos i₀).ne'⟩

theorem gamma_int_ne_zero {k : ℤ} (hk : 0 < k) : Complex.Gamma (k : ℂ) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.intCast_re]; exact_mod_cast hk)

theorem half_abs_two_mul (a : ℤ) (ha : 0 < a) : ((|2 * a| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_of_pos (by omega)]; push_cast; ring

theorem half_abs_neg_two_mul (a : ℤ) (ha : 0 < a) : ((|-(2 * a)| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_neg, half_abs_two_mul a ha]

theorem archFactor_ne_zero {n : I → ℤ} {s : ℂ} (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) :
    archFactor n s ≠ 0 := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (mul_ne_zero two_ne_zero ?_) (hs i)
  rw [Ne, Complex.cpow_eq_zero_iff]; tauto

theorem discr_mul_conductor_pos (E : Type) [Field E] [NumberField E]
    (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) :
    0 < (discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k := by
  refine Nat.mul_pos (Int.natAbs_pos.2 (discr_ne_zero E)) ?_
  unfold Finsupp.prod
  exact Finset.prod_pos fun v _ => pow_pos (Nat.pos_of_ne_zero fun hz =>
    v.ne_bot (Ideal.absNorm_eq_zero_iff.1 hz)) _

/-- Two one-sided comparisons with the dual completed function for positive CM weights.
The boundary estimate is used only for anticyclotomic characters; the integer comparison
does not require a root number or an identity on the entire plane. -/
def CMReflectionBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (m : I → ℤ)
    (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ Λ' : ℂ → ℂ),
    IsUnitary χ → HasInf χ φ m → (∀ i, 0 < m i) → (∀ v, ExpAt χ v (a v)) →
    IsCompletedL χ (fun i => 2 * m i) Λ → IsCompletedL χ⁻¹ (fun i => -(2 * m i)) Λ' →
      (TrivOnF χ → ∀ z : ℂ, z.re = -1 / 2 → ‖Λ z‖ ≤
        (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℝ) * ‖Λ' (1 - z)‖) ∧
      ∀ k : ℤ, k ≤ 0 → (∀ i, 0 < k + m i) → ‖Λ' (1 - (k : ℂ))‖ ≤ ‖Λ k‖

theorem CMReflectionBounds.of_functionalEquation
    (h : GlobalTheory.Published.HeckeFunctionalEquationAbs) : CMReflectionBounds := by
  intro E _ _ _ I _ φ hφ χ m a Λ Λ' hu hm hpos ha hΛ hΛ'
  obtain ⟨i⟩ := nonempty_of_isCMType hφ
  have hn : ∃ j, 2 * m j ≠ 0 := ⟨i, mul_ne_zero two_ne_zero (hpos i).ne'⟩
  obtain ⟨ε, hε, hfe⟩ := h E I φ hφ χ (fun j => 2 * m j) a Λ Λ' hu hm hn ha hΛ hΛ'
  let A : ℕ := (discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k
  have hApos : 0 < A := discr_mul_conductor_pos E a
  have hnorm (z : ℂ) : ‖Λ z‖ = (A : ℝ) ^ ((1 / 2 : ℝ) - z.re) * ‖Λ' (1 - z)‖ := by
    rw [hfe z, norm_mul, norm_mul, hε, one_mul]
    change ‖(A : ℂ) ^ (1 / 2 - z)‖ * _ = _
    rw [Complex.norm_natCast_cpow_of_pos hApos]
    congr 2
    simp
  constructor
  · intro _ z hz
    rw [hnorm, hz]
    norm_num [A]
  · intro k hk _
    rw [hnorm]
    have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    refine le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow ?_ ?_)
    · exact_mod_cast hApos
    · simpa only [Complex.intCast_re] using (show 0 ≤ (1 / 2 : ℝ) - k by linarith)

theorem heckeL_ne_zero_int_of_reflection (hFE : CMReflectionBounds) (hB : CompletedLBoundedInStrips) [IsCMField E]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ) (hm : HasInf χ φ m)
    (hpos : ∀ i, 0 < m i) {L : ℂ → ℂ} (hL : IsHeckeL χ L) (s : ℤ) (hs : ∀ i, 0 < s + m i) : L s ≠ 0 := by
  rcases le_or_gt 1 s with h1 | h1
  · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [← e]
    exact hL.ne_zero_nat hu (by omega)
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  have hn : ∃ i, 2 * m i ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hn' : ∃ i, -(2 * m i) ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hm' : Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => -(2 * m i)) := GlobalTheory.Published.HeckeFEModel.hasInf_inv hm
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hmi : HasInf χ⁻¹ φ (fun i => -m i) := by
    have e : (fun i => 2 * -m i) = fun i => -(2 * m i) := funext fun i => by ring
    show Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => 2 * -m i)
    rw [e]; exact hm'
  obtain ⟨Λ, hΛ, -⟩ := hB E I φ hφ χ (fun i => 2 * m i) hu hm hn
  obtain ⟨Λ', hΛ', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -(2 * m i)) hu' hm' hn'
  obtain ⟨L', hL'⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ (fun i => -m i) χ⁻¹ hφ hu' hmi
    ⟨i₀, by have := hpos i₀; omega⟩

  have g1 : ∀ i, Complex.Gamma ((1 - (s : ℂ)) + ((|-(2 * m i)| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_neg_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (k := 1 - s + m i) (by have := hpos i; omega)
    push_cast at this; exact this
  have e1 := completed_eq hΛ' hL' g1
  have hL1 : L' (1 - (s : ℂ)) ≠ 0 := by
    have e : (((1 - s).toNat : ℕ) : ℂ) = 1 - (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [← e]
    exact hL'.ne_zero_nat hu' (by omega)
  have hΛ'1 : Λ' (1 - (s : ℂ)) ≠ 0 := by
    rw [e1]; exact mul_ne_zero (archFactor_ne_zero g1) hL1
  obtain ⟨a, ha⟩ := GlobalTheory.Published.HeckeFEModel.exists_exponents χ
  have href := (hFE E I φ hφ χ m a Λ Λ' hu hm hpos ha hΛ hΛ').2 s (by omega) hs
  have hΛs : Λ s ≠ 0 := norm_pos_iff.mp ((norm_pos_iff.mpr hΛ'1).trans_le href)

  have g0 : ∀ i, Complex.Gamma ((s : ℂ) + ((|2 * m i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (hs i)
    push_cast at this; exact this
  rw [completed_eq hΛ hL g0] at hΛs
  exact right_ne_zero_of_mul hΛs

theorem heckeL_ne_zero_int (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) [IsCMField E]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ) (hm : HasInf χ φ m)
    (hpos : ∀ i, 0 < m i) {L : ℂ → ℂ} (hL : IsHeckeL χ L) (s : ℤ) (hs : ∀ i, 0 < s + m i) : L s ≠ 0 :=
  heckeL_ne_zero_int_of_reflection (.of_functionalEquation hFE) hB hφ hu hm hpos hL s hs

end GlobalTheory.LValNe

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

theorem squareBottomHalfRankDiff_le_halfRank (D : D7) (i j : ℕ) : e0 D i j ≤ halfRank D i j := by
  unfold e0 halfRank botBig botSmall
  omega

theorem lNe_square_of_reflection (hFE : GlobalTheory.LValNe.CMReflectionBounds) (hB : CompletedLBoundedInStrips) {D : D7} {T : Type}
    {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} [IsCMField D.host.E] (hφ : IsCMType (cmPhi D)) {μ₀ : T} (hL : Lc.Is μ₀)
    (G : GridData Lc sc) (i j : Fin D.R.m) :
    (∀ t, ∃ Λ, IsHeckeL (nuH G t i j) Λ ∧ ∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0) ∧
      ∀ c, ∃ Λ, IsHeckeL (fam G μ₀ i j c) Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := by
  have hv := GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (Nat.zero_le (halfRank D i j))
  have hpos : ∀ τ, 0 < ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ) := fun τ => by
    have := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).2
    omega
  have fam_ok : ∀ χ : HChar D.host.E, IsValChar (cmPhi D) 0 (kap D sc.cGap i j 0) (condF G.pl) ∅ χ →
      ∃ Λ, IsHeckeL χ Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := fun χ h => by
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ h.1 h.2.2.1 hpos
    exact ⟨Λ, hΛ, fun s hs => hΛ.ne_zero_nat h.1 hs⟩
  refine ⟨fun t => ?_, fun c => ?_⟩
  · have e : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
      simp only [nuH, hL.xi_base, mul_one]
      exact mul_div_right_comm _ _ _
    obtain ⟨n, hn, hf⟩ := hL.xi_fin t
    have hu : IsUnitary (nuH G t i j) := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G t i j hL)
    have hm : HasInf (nuH G t i j) (cmPhi D) (fun τ => ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) := by
      intro k
      rw [e, Formalism.L2.Host.HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one (Lc.xiH t) hn hf k, mul_one]
      exact hv.1.2.2.1 k
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ hu hm hpos
    refine ⟨Λ, hΛ, fun s hs1 hs2 => GlobalTheory.LValNe.heckeL_ne_zero_int_of_reflection hFE hB hφ hu hm hpos hΛ s fun τ => ?_⟩
    have a0 := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).1
    have a1 := GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (le_refl (halfRank D i j))
    have a2 := squareBottomHalfRankDiff_le_halfRank D i j
    omega
  · cases c with
    | none => exact fam_ok _ hv.1
    | some c => exact fam_ok _ (hv.2 c)

theorem lNe_square (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) {D : D7} {T : Type}
    {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} [IsCMField D.host.E] (hφ : IsCMType (cmPhi D)) {μ₀ : T} (hL : Lc.Is μ₀)
    (G : GridData Lc sc) (i j : Fin D.R.m) :
    (∀ t, ∃ Λ, IsHeckeL (nuH G t i j) Λ ∧ ∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0) ∧
      ∀ c, ∃ Λ, IsHeckeL (fam G μ₀ i j c) Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 :=
  lNe_square_of_reflection (.of_functionalEquation hFE) hB hφ hL G i j

theorem lNe_of_reflection :
    GlobalTheory.LValNe.CMReflectionBounds → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LNe := by
  intro hFE hB hFD
  obtain ⟨CF0, h⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h'⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hCM, -, hFd, -, -⟩ := h' C hC D large₂ he hx hR T Lc μ₀ hL G
  obtain ⟨-, -, -, -, -, -, hφ, -⟩ := hFd
  exact fun i j => lNe_square_of_reflection hFE hB hφ hL G i j

theorem lNe_of_functionalEquation :
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LNe :=
  fun hFE => lNe_of_reflection (.of_functionalEquation hFE)

end GlobalTheory.SqTop
