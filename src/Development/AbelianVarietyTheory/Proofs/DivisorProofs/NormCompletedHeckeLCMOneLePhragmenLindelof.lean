module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeLFunctionLeZetaThreeHalvesPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxRealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal

noncomputable section
namespace GlobalTheory.HeckeLOneBound
open GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

theorem norm_factor (s c : ℂ) :
    ‖2 * (2 * (Real.pi : ℂ)) ^ (-(s + c)) * Complex.Gamma (s + c)‖ =
      2 * (2 * Real.pi) ^ (-(s.re + c.re)) * ‖Complex.Gamma (s + c)‖ := by
  have h2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_mul, h2, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

theorem norm_archFactor_real {I : Type} [Fintype I] (n : I → ℤ) {x : ℝ} (hx : 0 < x) :
    ‖archFactor n (x : ℂ)‖ = ∏ i, (2 * (2 * Real.pi) ^ (-(x + ((|n i| : ℤ) : ℝ) / 2)) *
      Real.Gamma (x + ((|n i| : ℤ) : ℝ) / 2)) := by
  unfold archFactor
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_factor]
  have hc : ((x : ℂ) + ((|n i| : ℤ) : ℂ) / 2) = ((x + ((|n i| : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
  rw [hc, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos (by linarith))]
  congr 3
  simp

theorem norm_archFactor_le {I : Type} [Fintype I] (n : I → ℤ) {s : ℂ} (hs : 0 < s.re) :
    ‖archFactor n s‖ ≤ ‖archFactor n (s.re : ℂ)‖ := by
  rw [norm_archFactor_real n hs]
  unfold archFactor
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_factor]
  have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
  have hre : (s + ((|n i| : ℤ) : ℂ) / 2).re = s.re + ((|n i| : ℤ) : ℝ) / 2 := by simp
  have hre' : (((|n i| : ℤ) : ℂ) / 2).re = ((|n i| : ℤ) : ℝ) / 2 := by simp
  rw [hre']
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := PI.EF.norm_Gamma_le (w := s + ((|n i| : ℤ) : ℂ) / 2) (by rw [hre]; linarith)
  rwa [hre] at this

theorem pl_strip {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b C : ℝ} (hab : a < b)
    (hbd : ∃ C' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C')
    (ha : ∀ s : ℂ, s.re = a → ‖f s‖ ≤ C) (hb : ∀ s : ℂ, s.re = b → ‖f s‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : ‖f z‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip hf.diffContOnCl ?_ ha hb hza hzb
  refine ⟨0, div_pos Real.pi_pos (sub_pos.2 hab), 0, ?_⟩
  obtain ⟨C', hC'⟩ := hbd
  refine Asymptotics.IsBigO.of_bound C' ?_
  refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall fun z hz => ?_)
  simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
  exact hC' z hz.1.le hz.2.le

/-- Log-convexity and the Gamma recurrence give the square-root loss at a half step. -/
private theorem gamma_add_half_le {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 1 / 2) ≤ Real.Gamma x * Real.sqrt x := by
  have hg := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx
    (show 0 < x + 1 by linarith) (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  rw [show 1 / 2 * x + 1 / 2 * (x + 1) = x + 1 / 2 by ring,
    Real.Gamma_add_one hx.ne', ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul hx.le, mul_left_comm, Real.mul_self_sqrt (Real.Gamma_pos_of_pos hx).le, mul_comm] at hg
  exact hg

private theorem factor_three_halves_le_sqrt {c : ℝ} (hc : 1 ≤ c) :
    2 * (2 * Real.pi) ^ (-(3 / 2 + c)) * Real.Gamma (3 / 2 + c) ≤
      2 * (2 * Real.pi) ^ (-(1 + c)) * Real.Gamma (1 + c) * Real.sqrt (1 + c) := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hpow : (2 * Real.pi) ^ (-(3 / 2 + c)) ≤ (2 * Real.pi) ^ (-(1 + c)) :=
    Real.rpow_le_rpow_of_exponent_le hpi (by linarith)
  have hg := gamma_add_half_le (show 0 < 1 + c by linarith)
  rw [show 1 + c + 1 / 2 = 3 / 2 + c by ring] at hg
  calc
    _ ≤ (2 * (2 * Real.pi) ^ (-(1 + c))) * (Real.Gamma (1 + c) * Real.sqrt (1 + c)) :=
      mul_le_mul (by gcongr) hg (Real.Gamma_pos_of_pos (by linarith)).le (by positivity)
    _ = _ := by ring

theorem archFactor_three_halves_le_sqrt {I : Type} [Fintype I] (m : I → ℤ) (hm : ∀ i, 0 < m i) :
    ‖archFactor (fun i => 2 * m i) (3 / 2)‖ ≤ ‖archFactor (fun i => 2 * m i) 1‖ * ∏ i, Real.sqrt (1 + (m i : ℝ)) := by
  have e32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e1 : (1 : ℂ) = ((1 : ℝ) : ℂ) := by simp
  rw [e32, e1, norm_archFactor_real _ (by norm_num), norm_archFactor_real _ (by norm_num), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
  · have : 0 < 3 / 2 + ((|2 * m i| : ℤ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((|2 * m i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
      linarith
    have := Real.Gamma_pos_of_pos this
    positivity
  · have hc : ((|2 * m i| : ℤ) : ℝ) / 2 = (m i : ℝ) := by
      rw [abs_of_pos (by have := hm i; omega)]; push_cast; ring
    rw [hc]
    exact factor_three_halves_le_sqrt (by exact_mod_cast hm i)

theorem factor_three_halves_le {c : ℝ} (hc : 1 ≤ c) :
    2 * (2 * Real.pi) ^ (-(3 / 2 + c)) * Real.Gamma (3 / 2 + c) ≤
      2 * (2 * Real.pi) ^ (-(1 + c)) * Real.Gamma (1 + c) * (1 + c) := by
  refine (factor_three_halves_le_sqrt hc).trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · exact Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  · have := Real.Gamma_pos_of_pos (show 0 < 1 + c by linarith)
    positivity

theorem archFactor_three_halves_le {I : Type} [Fintype I] (m : I → ℤ) (hm : ∀ i, 0 < m i) :
    ‖archFactor (fun i => 2 * m i) (3 / 2)‖ ≤ ‖archFactor (fun i => 2 * m i) 1‖ * ∏ i, (1 + (m i : ℝ)) := by
  refine (archFactor_three_halves_le_sqrt m hm).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine Finset.prod_le_prod₀ (fun _ _ => Real.sqrt_nonneg _) fun i _ => Real.sqrt_le_self_iff.mpr (Or.inr ?_)
  exact le_add_of_nonneg_right (by exact_mod_cast (hm i).le)

open Complex.HadamardThreeLines in
private theorem strip_one_quarter {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbd : ∃ C : ℝ, ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → ‖f z‖ ≤ C)
    (hleft : ∀ z : ℂ, z.re = -1 / 2 → ‖f z‖ ≤ A * B)
    (hright : ∀ z : ℂ, z.re = 3 / 2 → ‖f z‖ ≤ B) :
    ‖f 1‖ ≤ A ^ (1 / 4 : ℝ) * B := by
  obtain ⟨C, hC⟩ := hbd
  have hbdd : BddAbove ((norm ∘ f) '' verticalClosedStrip (-1 / 2) (3 / 2)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC z hz.1 hz.2
  have h := norm_le_interp_of_mem_verticalClosedStrip' (f := f) (z := 1)
    (l := -1 / 2) (u := 3 / 2) (by norm_num)
    (show (-1 / 2 : ℝ) ≤ (1 : ℂ).re ∧ (1 : ℂ).re ≤ 3 / 2 by norm_num) hf.diffContOnCl
    hbdd hleft hright
  norm_num only [Complex.one_re, one_div, sub_neg_eq_add] at h
  convert h.trans_eq _ using 1
  rw [Real.mul_rpow hA hB, mul_assoc, ← Real.rpow_add_of_nonneg hB (by norm_num) (by norm_num)]
  norm_num

end GlobalTheory.HeckeLOneBound

namespace GlobalTheory.HeckeLOneBound
open GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

theorem norm_heckeL_one_le_of_reflection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    GlobalTheory.LValNe.CMReflectionBounds → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ : ℂ → ℂ),
    IsUnitary χ → TrivOnF χ → HasInf χ φ m → (∀ i, 0 < m i) → (∀ v, ExpAt χ v (a v)) → IsHeckeL χ Λ →
    ‖Λ 1‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℝ)) ^ (1 / 4 : ℝ) * ∏ i, Real.sqrt (1 + (m i : ℝ)) := by
  intro E _ _ _ I _ φ hFE hB hφ χ m a Λ hu htr hinf hpos ha hL
  set n : I → ℤ := fun i => 2 * m i with hn_def
  set A : ℕ := (discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k with hA_def
  set Z : ℝ := ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E with hZ_def
  have hinf' : Formalism.L2.Host.HChar.HasInf χ φ n := hinf
  obtain ⟨i₀⟩ := GlobalTheory.LValNe.nonempty_of_isCMType hφ
  have hn : ∃ i, n i ≠ 0 := ⟨i₀, by have := hpos i₀; simp only [hn_def]; omega⟩
  have hn' : ∃ i, (fun i => -n i) i ≠ 0 := ⟨i₀, by have := hpos i₀; simp only [hn_def]; omega⟩
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hinv := GlobalTheory.Published.HeckeFEModel.hasInf_inv hinf'
  obtain ⟨Λc, hΛc, hbc⟩ := hB E I φ hφ χ n hu hinf' hn
  obtain ⟨Λc', hΛc', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -n i) hu' hinv hn'
  have href := (hFE E I φ hφ χ m a Λc Λc' hu hinf hpos ha hΛc hΛc').1 htr
  have hL' : IsHeckeL χ⁻¹ Λ := GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal E χ Λ htr hL
  have harch : archFactor (fun i => -n i) = archFactor n := by
    funext s; unfold archFactor; simp only [abs_neg]
  have hZ0 : 0 ≤ Z := by positivity
  set F : ℝ := ‖archFactor n (3 / 2)‖ with hF_def
  have hF0 : 0 ≤ F := norm_nonneg _

  have hline : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc s‖ ≤ F * Z := fun s hs => by
    rw [hΛc.eq_mul hL (by rw [hs]; norm_num), norm_mul]
    have h1 := norm_archFactor_le n (s := s) (by rw [hs]; norm_num)
    rw [hs] at h1
    have h1' : ‖archFactor n s‖ ≤ F := by
      rw [hF_def]; convert h1 using 3; push_cast; ring
    exact mul_le_mul h1' (GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow E χ Λ s hu hL hs.ge) (norm_nonneg _) hF0
  have hline' : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc' s‖ ≤ F * Z := fun s hs => by
    rw [hΛc'.eq_mul hL' (by rw [hs]; norm_num), norm_mul, harch]
    have h1 := norm_archFactor_le n (s := s) (by rw [hs]; norm_num)
    rw [hs] at h1
    have h1' : ‖archFactor n s‖ ≤ F := by
      rw [hF_def]; convert h1 using 3; push_cast; ring
    exact mul_le_mul h1' (GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow E χ⁻¹ Λ s hu' hL' hs.ge) (norm_nonneg _) hF0

  have hleft (s : ℂ) (hs : s.re = -1 / 2) : ‖Λc s‖ ≤ A * (F * Z) := by
    refine (href s hs).trans (mul_le_mul_of_nonneg_left (hline' _ ?_) (Nat.cast_nonneg A))
    simp only [Complex.sub_re, Complex.one_re, hs]
    norm_num
  have h1 := strip_one_quarter hΛc.1 (Nat.cast_nonneg A) (mul_nonneg hF0 hZ0)
    (hbc (-1 / 2) (3 / 2) (by norm_num)) hleft hline

  have hg : ∀ i, Complex.Gamma ((1 : ℂ) + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    have : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
    simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
    norm_num
    positivity
  have e1 := GlobalTheory.LValNe.completed_eq hΛc hL hg
  have hG : 0 < ‖archFactor n 1‖ := norm_pos_iff.2 (GlobalTheory.LValNe.archFactor_ne_zero hg)
  have hrat := archFactor_three_halves_le_sqrt m hpos
  rw [e1, norm_mul] at h1
  calc
    ‖Λ 1‖ ≤ Z * (A : ℝ) ^ (1 / 4 : ℝ) * ∏ i, Real.sqrt (1 + (m i : ℝ)) := by
      apply le_of_mul_le_mul_left _ hG
      calc
        _ ≤ (A : ℝ) ^ (1 / 4 : ℝ) * (F * Z) := h1
        _ ≤ (A : ℝ) ^ (1 / 4 : ℝ) * ((‖archFactor n 1‖ * ∏ i, Real.sqrt (1 + (m i : ℝ))) * Z) := by gcongr
        _ = _ := by ring

theorem norm_heckeL_one_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ : ℂ → ℂ),
    IsUnitary χ → TrivOnF χ → HasInf χ φ m → (∀ i, 0 < m i) → (∀ v, ExpAt χ v (a v)) → IsHeckeL χ Λ →
    ‖Λ 1‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℝ)) * ∏ i, (1 + (m i : ℝ)) := by
  intro E _ _ _ I _ φ hR hB hφ χ m a Λ hu htr hm hpos ha hΛ
  have h := norm_heckeL_one_le_of_reflection E I φ (.of_functionalEquation hR) hB hφ χ m a Λ hu htr hm hpos ha hΛ
  let A : ℕ := (discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k
  have hA1 : 1 ≤ (A : ℝ) := by exact_mod_cast GlobalTheory.LValNe.discr_mul_conductor_pos E a
  refine h.trans (mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) (by positivity))
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hA1 (by norm_num)) (by positivity)
  · refine Finset.prod_le_prod₀ (fun _ _ => Real.sqrt_nonneg _) fun i _ => Real.sqrt_le_self_iff.mpr (Or.inr ?_)
    have : (0 : ℝ) ≤ m i := by exact_mod_cast (hpos i).le
    linarith

end GlobalTheory.HeckeLOneBound

end
