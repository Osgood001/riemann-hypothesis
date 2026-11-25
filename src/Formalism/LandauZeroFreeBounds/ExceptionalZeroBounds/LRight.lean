module

public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRight
import Mathlib.Analysis.SumIntegralComparisons

@[expose] public section

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma norm_term_twist_moebius_le {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    ‖term (↗χ * ↗μ) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by
  apply LSeries.norm_term_le
  simp only [Pi.mul_apply, Pi.one_apply, norm_one, norm_mul]
  have h1 := DirichletCharacter.norm_le_one χ (n : ZMod q)
  have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  simpa only [one_mul] using mul_le_mul h1 h2 (norm_nonneg _) zero_le_one

theorem inverseBound : LInvBound := by
  intro q _ χ s hs
  have hp : -s.re < -1 := by linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s.re)) (Set.Ici (↑(1 : ℕ) : ℝ)) :=
    fun x hx y _ hxy =>
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (by exact_mod_cast hx)) hxy (by linarith)
  have htail := hanti.tsum_comp_add_le_integral 1
    (integrableOn_Ioi_rpow_of_lt hp (by norm_num))
    (fun x hx => Real.rpow_nonneg (by have h := Set.mem_Ioi.mp hx; norm_num at h; linarith) _)
  have hIntegral : (∫ x in Set.Ioi (↑(1 : ℕ) : ℝ), x ^ (-s.re)) = -(1 / (-s.re + 1)) := by
    rw [Nat.cast_one, integral_Ioi_rpow_of_lt hp zero_lt_one, Real.one_rpow, neg_div]
  rw [hIntegral] at htail
  have hs1 := (LSeriesSummable_one_iff.mpr hs).norm
  have hterm (n : ℕ) : ‖term (1 : ℕ → ℂ) s (n + 1)‖ = ((n : ℝ) + 1) ^ (-s.re) := by
    rw [norm_term_eq, ite_eq_right (Nat.succ_ne_zero n)]
    simp [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) + 1), one_div]
  have hshift := (summable_nat_add_iff 1).mpr hs1
  have hT1 : ∑' n, ‖term (1 : ℕ → ℂ) s n‖ ≤ s.re / (s.re - 1) := by
    rw [hs1.tsum_eq_zero_add, hshift.tsum_eq_zero_add]
    simp only [term_zero, norm_zero, zero_add, hterm, Nat.cast_zero, zero_add, Real.one_rpow]
    have he : (1 : ℝ) + -(1 / (-s.re + 1)) = s.re / (s.re - 1) := by
      have hne : s.re - 1 ≠ 0 := by linarith
      rw [show -s.re + 1 = -(s.re - 1) by ring, div_neg, neg_neg]
      field_simp
      ring
    rw [← he]
    simp only [Nat.cast_add, Nat.cast_one] at htail ⊢
    gcongr
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hinv : ‖LSeries ↗χ s‖⁻¹ = ‖LSeries (↗χ * ↗μ) s‖ := by
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hmul]
  rw [hinv]
  have hS2 : Summable fun n => ‖term (↗χ * ↗μ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_term_twist_moebius_le χ s n) hs1
  calc ‖LSeries (↗χ * ↗μ) s‖ = ‖∑' n, term (↗χ * ↗μ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗μ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ :=
      Summable.tsum_le_tsum (fun n => norm_term_twist_moebius_le χ s n) hS2 hs1
    _ ≤ s.re / (s.re - 1) := hT1

lemma negLD_eq_LSeries_mul_vonMangoldt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    negLD χ s = L (↗χ * ↗Λ) s := by
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries ↗χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  rw [negLD, hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, neg_div]

lemma norm_LSeries_twist_vonMangoldt_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖L (↗χ * ↗Λ) s‖ ≤ Formalism.ZF.lamF s.re := by
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  have hSΛ : Summable fun n => ‖term ↗Λ (s.re : ℂ) n‖ :=
    summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt hre)
  have hle : ∀ n, ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ (s.re : ℂ) n‖ := by
    intro n
    calc ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ s n‖ := by
          apply LSeries.norm_term_le
          simp only [Pi.mul_apply, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
      _ = ‖term ↗Λ (s.re : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re]
  have hS2 : Summable fun n => ‖term (↗χ * ↗Λ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hSΛ
  calc ‖L (↗χ * ↗Λ) s‖ = ‖∑' n, term (↗χ * ↗Λ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term ↗Λ (s.re : ℂ) n‖ := Summable.tsum_le_tsum hle hS2 hSΛ
    _ = Formalism.ZF.lamF s.re := rfl

theorem l_log_deriv_right : LLogDerivRight := by
  obtain ⟨C, hC0, hC⟩ := Formalism.ZF.logDerivBoundRightHalfPlane
  refine ⟨C, hC0, ?_⟩
  intro q _ χ s hs
  rw [negLD_eq_LSeries_mul_vonMangoldt χ hs]
  refine le_trans (norm_LSeries_twist_vonMangoldt_le χ hs) ?_
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  rw [Formalism.ZF.lamF_eq_norm hs, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre,
    neg_div, norm_neg]
  have h := hC (s.re : ℂ) hre
  simpa using h

end Formalism.ZeroFreeDirichlet
