import Mathlib
import Bundle00
import Bundle01
universe u v w
noncomputable section
section
open scoped BigOperators
open Complex (exp)
open Formalism.L2.Th1.B (fExp)

namespace Formalism.L2.Th1.F

namespace Taylor

open PowerSeries

theorem coeff_taylor0 (f : ℂ → ℂ) (n : ℕ) :
    coeff n (taylor0 f) = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  simp [taylor0]

theorem taylor0_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor0 (fun z => f z + g z) = taylor0 f + taylor0 g := by
  ext n
  rw [map_add, coeff_taylor0, coeff_taylor0, coeff_taylor0,
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

theorem taylor0_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor0 (fun z => f z * g z) = taylor0 f * taylor0 g := by
  ext n
  rw [coeff_mul, coeff_taylor0, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Nat.lt_succ_iff.mp $ Finset.mem_range.mp hi
  simp [coeff_taylor0]
  have h1 : (n.factorial : ℂ) = (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hi').symm
  have h2 : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  have h3 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h4 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  rw [h1]
  field_simp

theorem taylor0_const (c : ℂ) : taylor0 (fun _ => c) = C c := by
  ext n
  rw [coeff_taylor0, iteratedDeriv_const, coeff_C]
  split_ifs with h
  simp [h]
  simp

theorem taylor0_id : taylor0 (fun z => z) = X := by
  ext n
  rw [coeff_taylor0, iteratedDeriv_fun_id_zero, coeff_X]
  split_ifs with h
  simp [h]
  simp

theorem taylor0_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : taylor0 f = taylor0 g := by
  ext n
  rw [coeff_taylor0, coeff_taylor0, h.iteratedDeriv_eq]

theorem taylor0_deriv (f : ℂ → ℂ) : taylor0 (deriv f) = derivative (taylor0 f) := by
  ext n
  rw [coeff_derivative, coeff_taylor0, coeff_taylor0, ← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

theorem iteratedDeriv_comp_mul (a : ℂ) (n : ℕ) : ∀ f, AnalyticAt ℂ f 0 →
    iteratedDeriv n (fun z => f $ a * z) 0 = a ^ n * iteratedDeriv n f 0 := by
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have hc : Filter.Tendsto (fun z => a * z) (nhds 0) $ nhds 0 := by
      have : Continuous fun z => a * z := by fun_prop
      simpa using this.tendsto 0
    have he : deriv (fun z => f $ a * z) =ᶠ[nhds 0] fun z => a * deriv f (a * z) := by
      filter_upwards [hc.eventually hf.eventually_analyticAt] with z hz
      have h2 : HasDerivAt (fun z => a * z) a z := by
        simpa using (hasDerivAt_id z).const_mul a
      have := ((hz.differentiableAt.hasDerivAt).comp z h2).deriv
      rwa [mul_comm] at this
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq, iteratedDeriv_const_mul_field, ih _ hf.deriv,
      iteratedDeriv_succ', pow_succ]
    ring

theorem taylor0_rescale {f : ℂ → ℂ} (a : ℂ) (hf : AnalyticAt ℂ f 0) :
    taylor0 (fun z => f $ a * z) = rescale a (taylor0 f) := by
  ext n
  rw [coeff_rescale, coeff_taylor0, coeff_taylor0, iteratedDeriv_comp_mul a n f hf, mul_div_assoc]

theorem taylor0_inj {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : taylor0 f = taylor0 g) : f =ᶠ[nhds 0] g := by
  have h0 : ∀ n, iteratedDeriv n (fun z => f z - g z) 0 = 0 := by
    intro n
    have h1 := congrArg (coeff n) h
    rw [coeff_taylor0, coeff_taylor0] at h1
    have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h2 : iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
      field_simp at h1
      exact h1
    rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, h2, sub_self]
  have ht : analyticOrderAt (fun z => f z - g z) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero $ hf.fun_sub hg).mpr fun i _ => h0 i
  rw [analyticOrderAt_eq_top] at ht
  filter_upwards [ht] with z hz
  exact sub_eq_zero.mp hz

theorem ode_zero {a Y : PowerSeries ℂ} (h : derivative Y = a * Y) (h0 : constantCoeff Y = 0) :
    Y = 0 := by
  have key : ∀ n, coeff n Y = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => simpa using h0
      | succ n =>
        have h1 := congrArg (coeff n) h
        rw [coeff_derivative, coeff_mul] at h1
        have h2 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 a * coeff p.2 Y = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have : p.2 < n + 1 := by
            have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
            omega
          rw [ih _ this, mul_zero]
        rw [h2] at h1
        have h4 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
        exact (mul_eq_zero.mp h1).resolve_right h4
  ext n
  simpa using key n

theorem taylor0_exp {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    taylor0 (fun z => exp $ f z) = fExp (taylor0 f) := by
  have hE : AnalyticAt ℂ (fun z => exp $ f z) 0 := hf.cexp
  have hc : constantCoeff (taylor0 f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_taylor0]
    simp [h0]
  have hS : HasSubst $ taylor0 f := HasSubst.of_constantCoeff_zero' hc
  have he : deriv (fun z => exp $ f z) =ᶠ[nhds 0] fun z => deriv f z * exp (f z) := by
    filter_upwards [hf.eventually_analyticAt] with z hz
    have := (hz.differentiableAt.hasDerivAt.cexp).deriv
    rwa [mul_comm] at this
  have h1 : derivative (taylor0 fun z => exp $ f z)
      = derivative (taylor0 f) * taylor0 fun z => exp $ f z := by
    rw [← taylor0_deriv, taylor0_congr he, taylor0_mul hf.deriv hE, taylor0_deriv]
  have h2 : derivative (fExp $ taylor0 f)
      = derivative (taylor0 f) * fExp (taylor0 f) := by
    unfold fExp
    rw [derivative_subst hS, derivative_exp, mul_comm]
  have h3 : constantCoeff (taylor0 fun z => exp $ f z) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_taylor0]
    simp [h0]
  have h4 : constantCoeff (fExp $ taylor0 f) = 1 := by
    unfold fExp
    have h5 : exp ℂ = 1 + (exp ℂ - 1) := by ring
    have h6 : (1 : PowerSeries ℂ).subst (taylor0 f) = (1 : PowerSeries ℂ) := by
      rw [← coe_substAlgHom hS, map_one]
    have h7 : constantCoeff ((exp ℂ - 1).subst (taylor0 f) : PowerSeries ℂ) = 0 :=
      constantCoeff_subst_eq_zero hc _ $ by simp
    rw [h5, subst_add hS, h6, map_add, map_one, h7, add_zero]
  refine sub_eq_zero.mp $ ode_zero (a := derivative $ taylor0 f) ?_ ?_
  rw [map_sub, h1, h2, mul_sub]
  rw [map_sub, h3, h4, sub_self]

end Taylor

theorem taylor_ring : TaylorRing :=
  ⟨fun _ _ hf hg => ⟨Taylor.taylor0_add hf hg, Taylor.taylor0_mul hf hg⟩, Taylor.taylor0_const,
    Taylor.taylor0_id, fun _ _ h => Taylor.taylor0_congr h⟩

theorem taylor_deriv : TaylorDeriv :=
  ⟨fun f _ => Taylor.taylor0_deriv f, fun _ a hf => Taylor.taylor0_rescale a hf,
    fun _ _ hf hg h => Taylor.taylor0_inj hf hg h⟩

theorem taylor_exp : TaylorExp := fun _ hf h0 => Taylor.taylor0_exp hf h0

end Formalism.L2.Th1.F
end
section
open scoped BigOperators
open Formalism.L2.Th1.B (dz)

namespace Formalism.L2.Th1.F

open PowerSeries

namespace TaylorWp

def T (f : ℂ → ℂ) (F : PowerSeries ℂ) : Prop := AnalyticAt ℂ f 0 ∧ taylor0 f = F

theorem T.add (hr : TaylorRing) {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z + g z) $ F + G :=
  ⟨hf.1.add hg.1, by rw [(hr.1 f g hf.1 hg.1).1, hf.2, hg.2]⟩

theorem T.mul (hr : TaylorRing) {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z * g z) $ F * G :=
  ⟨hf.1.mul hg.1, by rw [(hr.1 f g hf.1 hg.1).2, hf.2, hg.2]⟩

theorem T.const (hr : TaylorRing) (c : ℂ) : T (fun _ => c) $ C c :=
  ⟨analyticAt_const, hr.2.1 c⟩

theorem T.id (hr : TaylorRing) : T (fun z => z) X :=
  ⟨analyticAt_id, hr.2.2.1⟩

theorem T.pow (hr : TaylorRing) {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) (k : ℕ) :
    T (fun z => f z ^ k) $ F ^ k := by
  induction k with
  | zero => simpa using T.const hr 1
  | succ k ih => simpa only [pow_succ] using T.mul hr ih hf

end TaylorWp

open TaylorWp

theorem weierstrass_p_series_coeff : PSeriesCoeff := by
  intro L n
  rw [pSeries, taylor0, coeff_mk, L.iteratedDeriv_weierstrassPExcept_self 0]
  by_cases hn : n = 0
  simp [hn]
  simp [hn, if_false, PeriodPair.sumInvPow_zero]
  have h : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [Nat.factorial_succ]
  push_cast
  field_simp

theorem taylorIsWp_of (hr : TaylorRing) (hd : TaylorDeriv) : TaylorIsWp := by
  intro L
  refine ⟨?_, ?_, ?_⟩
  rw [← coeff_zero_eq_constantCoeff_apply, weierstrass_p_series_coeff L 0]
  simp
  intro n hn
  rw [weierstrass_p_series_coeff L n, L.G_eq_zero_of_odd (n + 2) (by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨k + 1, by ring⟩)]
  simp
  have hp : T (L.weierstrassPExcept 0) $ pSeries L := ⟨L.analyticAt_weierstrassPExcept 0, rfl⟩
  have hp' : T (deriv $ L.weierstrassPExcept 0) $ dz $ pSeries L :=
    ⟨hp.1.deriv, hd.1 _ hp.1⟩
  have hq := T.add hr (T.const hr 1) $ T.mul hr (T.pow hr (T.id hr) 2) hp
  have h2 := T.add hr (T.add hr (T.mul hr (T.const hr 4) $ T.pow hr hq 3)
    $ T.mul hr (T.mul hr (T.const hr $ -L.g₂) $ T.pow hr (T.id hr) 4) hq)
    $ T.mul hr (T.const hr $ -L.g₃) $ T.pow hr (T.id hr) 6
  have key := hr.2.2.2 _ _ (?_ : (fun z => (-2 + z ^ 3 * deriv (L.weierstrassPExcept 0) z) ^ 2)
    =ᶠ[nhds 0] fun z => 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) ^ 3
      + -L.g₂ * z ^ 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) + -L.g₃ * z ^ 6)
  rw [(T.pow hr (T.add hr (T.const hr $ -2) $ T.mul hr (T.pow hr (T.id hr) 3) hp') 2).2, h2.2] at key
  simp [map_neg, map_ofNat, map_one] at key
  rw [key]
  ring
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz]
  by_cases hz0 : z = 0
  simp [hz0]
  norm_num
  replace hz : z ∉ L.lattice := by simp_all
  have e1 := L.weierstrassPExcept_def 0 z
  have e2 := L.derivWeierstrassPExcept_def 0 z
  simp [ZeroMemClass.coe_zero, sub_zero] at e1 e2
  rw [e1, e2]
  have e3 : (z ^ 3 * L.derivWeierstrassP z) ^ 2 = z ^ 6 * (4 * L.weierstrassP z ^ 3
      - L.g₂ * L.weierstrassP z - L.g₃) := by rw [← L.derivWeierstrassP_sq z hz]; ring
  field_simp
  simp
  linear_combination e3

theorem weierstrass_series_unique : IsWpUnique := by
  intro K _ _ g2 g3 P Q hP hQ
  obtain ⟨-, -, hP⟩ := hP
  obtain ⟨-, -, hQ⟩ := hQ
  have hX : (X : PowerSeries K) ≠ 0 := X_ne_zero
  have hdX : ∀ n : ℕ, X * derivative ((X : PowerSeries K) ^ n) = (n : PowerSeries K) * X ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_X]
      push_cast
      linear_combination X * ih
  have main : ∀ n, X ^ n ∣ P - Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨E, hE⟩ := ih
      have hD : X * (derivative P - derivative Q)
          = X ^ n * ((n : PowerSeries K) * E + X * derivative E) := by
        rw [← map_sub, hE, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        linear_combination E * hdX n
      have hc : ((n : PowerSeries K) * E + X * derivative E)
            * (-4 + X ^ 3 * (derivative P + derivative Q))
          = E * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q) + (1 + X ^ 2 * Q) ^ 2)
              - C g2 * X ^ 4) := by
        apply mul_left_cancel₀ $ pow_ne_zero (n + 2) hX
        have hs := congrArg₂ (· - ·) hP hQ
        simp [dz] at hs
        linear_combination hs
          - X ^ 2 * (-4 + X ^ 3 * (derivative P + derivative Q)) * hD
          + X ^ 2 * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q)
              + (1 + X ^ 2 * Q) ^ 2) - C g2 * X ^ 4) * hE
      have h0 := congrArg constantCoeff hc
      simp [map_mul, map_add, map_sub, map_neg, map_pow, map_natCast, map_ofNat, map_one,
        constantCoeff_X, constantCoeff_C] at h0
      have h1 : (4 * (n : K) + 12) * constantCoeff E = 0 := by
        linear_combination -h0
      have h2 : (4 * (n : K) + 12) ≠ 0 := by
        have : ((4 * n + 12 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr $ by omega
        push_cast at this
        exact this
      have h3 : constantCoeff E = 0 := (mul_eq_zero.mp h1).resolve_left h2
      obtain ⟨E', rfl⟩ := X_dvd_iff.mpr h3
      use E'
      rw [hE]
      ring
  have hz : P - Q = 0 := by
    ext m
    rw [map_zero]
    exact X_pow_dvd_iff.mp (main $ m + 1) m $ Nat.lt_succ_self m
  exact sub_eq_zero.mp hz

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.B

open PowerSeries

section One

variable {K : Type} [Field K] [CharZero K]

theorem psubst_one {ι : Type} {a : MvPowerSeries ι K} (ha : HasSubst a) :
    (1 : PowerSeries K).subst a = 1 := by
  rw [← coe_substAlgHom ha, map_one]

theorem one_add_X_mul_deriv_log : (1 + X : PowerSeries K) * derivative (log K) = 1 := by
  have hd : ∀ n, coeff n (derivative $ log K) = (-1 : K) ^ n := by
    intro n
    rw [PowerSeries.coeff_derivative]
    simp [PowerSeries.log]
    field_simp
    ring
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  simp [hd]
  rw [coeff_succ_X_mul, hd, hd, coeff_one]
  simp [pow_succ]

theorem one_add_X_subst {ι : Type} {a : MvPowerSeries ι K} (ha : HasSubst a) :
    (1 + X : PowerSeries K).subst a = 1 + a := by
  rw [← coe_substAlgHom ha, map_add, map_one, coe_substAlgHom, subst_X ha]

theorem one_add_mul_deriv_log_subst {ι : Type} {a : MvPowerSeries ι K} (ha : HasSubst a) :
    (1 + a) * (derivative $ log K).subst a = 1 := by
  have h := congrArg (PowerSeries.substAlgHom ha) $ one_add_X_mul_deriv_log (K := K)
  rwa [map_mul, map_one, coe_substAlgHom, one_add_X_subst ha] at h

private theorem constantCoeff_powerSeries_subst_mv_eq {ι : Type} (φ : PowerSeries K) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (φ.subst f) = constantCoeff φ := by
  rw [PowerSeries.constantCoeff_subst $ HasSubst.of_constantCoeff_zero hf, finsum_eq_single _ 0]
  simp
  intro d hd
  simp [hf, zero_pow hd]

private theorem constantCoeff_powerSeries_subst_eq (φ : PowerSeries K) {g : PowerSeries K}
    (hg : constantCoeff g = 0) : constantCoeff (φ.subst g) = constantCoeff φ :=
  constantCoeff_powerSeries_subst_mv_eq φ (f := g) hg

private theorem constantCoeff_log_eq_zero' : constantCoeff (log K) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [PowerSeries.log]

private theorem derivative_exp_eq_exp : derivative (exp K) = exp K := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp [coeff_exp, Nat.factorial_succ]
  field_simp

private theorem derivative_eq_pderiv_unit (f : PowerSeries K) :
    derivative f = MvPowerSeries.pderiv () f := by
  ext n
  rw [PowerSeries.coeff_derivative]
  change _ = MvPowerSeries.coeff (Finsupp.single () n) _
  rw [MvPowerSeries.coeff_pderiv, ← Finsupp.single_add, Finsupp.single_eq_same]
  rfl

private theorem derivative_subst_eq_chain_rule {g : PowerSeries K} (hg : constantCoeff g = 0)
    (φ : PowerSeries K) :
    derivative (φ.subst g) = (derivative φ).subst g * derivative g := by
  simp [derivative_eq_pderiv_unit]
  exact Formalism.G.LogCR.pderiv_psubst (R := K) (τ := Unit) (a := g) hg φ ()

theorem log_subst_exp : (log K).subst (exp K - 1) = X := by
  have hc : constantCoeff (exp K - 1 : PowerSeries K) = 0 := by simp
  apply derivative.ext
  rw [derivative_subst_eq_chain_rule hc, derivative_X, map_sub, derivative_exp_eq_exp, Derivation.map_one_eq_zero,
    sub_zero]
  have h := one_add_mul_deriv_log_subst $ HasSubst.of_constantCoeff_zero' hc
  have e : (1 : PowerSeries K) + (exp K - 1) = exp K := by ring
  rw [e] at h
  rwa [mul_comm]
  rw [constantCoeff_powerSeries_subst_eq _ hc, constantCoeff_log_eq_zero']
  simp

theorem constantCoeff_exp_subst {ι : Type} {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff ((exp K).subst f) = 1 := by
  rw [constantCoeff_powerSeries_subst_mv_eq _ hf]
  simp

private theorem eq_zero_of_one_add_X_mul_derivative_eq_self {F : PowerSeries K}
    (h : (1 + X) * derivative F = F) (h0 : constantCoeff F = 0) : F = 0 := by
  ext n
  rw [map_zero]
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hn := congrArg (coeff n) h
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_derivative] at hn
    rcases n with _ | m
    rw [coeff_zero_X_mul] at hn
    simpa [ih] using hn
    rw [coeff_succ_X_mul, PowerSeries.coeff_derivative, ih] at hn
    have hne : ((m : K) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero $ m + 1
    simpa [hne] using hn

theorem exp_subst_log : (exp K).subst (log K) = 1 + X := by
  have hE : derivative ((exp K).subst (log K)) =
      (exp K).subst (log K) * derivative (log K) := by
    rw [derivative_subst_eq_chain_rule constantCoeff_log_eq_zero', derivative_exp_eq_exp]
  rw [← sub_eq_zero]
  apply eq_zero_of_one_add_X_mul_derivative_eq_self
  rw [map_sub, hE, map_add, Derivation.map_one_eq_zero, derivative_X, zero_add, mul_sub, mul_one,
    mul_left_comm, one_add_X_mul_deriv_log, mul_one]
  rw [map_sub, constantCoeff_powerSeries_subst_eq _ constantCoeff_log_eq_zero']
  simp

private theorem eq_zero_of_forall_pderiv_eq_self {σ : Type} {u : MvPowerSeries σ K}
    (hu : ∀ i, MvPowerSeries.pderiv i u = u) (h0 : MvPowerSeries.constantCoeff u = 0) :
    u = 0 := by
  classical
  suffices H : ∀ N, ∀ n, n.degree = N → MvPowerSeries.coeff n u = 0 by
    ext n
    simpa using H _ n rfl
  intro N
  induction N with
  | zero =>
    intro n hn
    rw [Finsupp.degree_eq_zero_iff] at hn
    subst hn
    simpa using h0
  | succ N ih =>
    intro n hn
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hc
      push_neg at hc
      have : n = 0 := by
        ext j
        exact hc j
      subst this
      simp at hn
    set m := n - Finsupp.single i 1 with hm
    have hnm : n = m + Finsupp.single i 1 := by
      ext j
      simp [hm, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply]
      split_ifs with hij
      subst hij
      omega
      omega
    have hadd : (m + Finsupp.single i 1).degree = m.degree + 1 := by
      rw [map_add, Finsupp.degree_single]
    have hdeg : m.degree = N := by
      rw [← hnm] at hadd
      omega
    have key := congrArg (MvPowerSeries.coeff m) $ hu i
    rw [MvPowerSeries.coeff_pderiv, ih m hdeg, ← hnm] at key
    have hne : ((m i : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero $ m i
    simpa [hne] using key

private theorem pderiv_exp_subst_eq_mul_pderiv {ι : Type} [Finite ι] (i : ι) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.pderiv i ((exp K).subst f) = (exp K).subst f * MvPowerSeries.pderiv i f := by
  rw [Formalism.G.LogCR.pderiv_psubst hf, derivative_exp_eq_exp]

theorem exp_biv :
    (exp K).subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      (exp K).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) *
        (exp K).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_pderiv_eq_self
  intro i
  rw [map_sub, Derivation.leibniz, pderiv_exp_subst_eq_mul_pderiv i h01, pderiv_exp_subst_eq_mul_pderiv i h0,
    pderiv_exp_subst_eq_mul_pderiv i $ by simp, map_add, smul_eq_mul, smul_eq_mul]
  fin_cases i <;> simp <;> ring
  rw [map_sub, map_mul, constantCoeff_powerSeries_subst_mv_eq _ h01, constantCoeff_powerSeries_subst_mv_eq _ h0,
    constantCoeff_powerSeries_subst_mv_eq _ $ by simp]
  simp

private theorem hasSubst_of_forall_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (h : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero h

theorem psubst_msubst {ι κ : Type} (φ : PowerSeries K) {u : MvPowerSeries ι K}
    (hu : MvPowerSeries.constantCoeff u = 0) {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (φ.subst u) = φ.subst (MvPowerSeries.subst b u) := by
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_of_forall_constantCoeff_eq_zero fun _ => hu) hb]

end One

section Rules

variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem fExp_add {f g : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : fExp (f + g) = fExp f * fExp g := by
  have hb : MvPowerSeries.HasSubst ![f, g] :=
    hasSubst_of_forall_constantCoeff_eq_zero fun i => by fin_cases i <;> simpa
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h := congrArg (MvPowerSeries.subst ![f, g]) $ exp_biv (K := K)
  rw [psubst_msubst _ h01 hb, MvPowerSeries.subst_mul hb, psubst_msubst _ h0 hb,
    psubst_msubst _ h1 hb] at h
  simpa [fExp, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb] using h

theorem constantCoeff_fExp {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (fExp f) = 1 :=
  constantCoeff_exp_subst hf

theorem fLog_fExp {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    fLog (fExp f) = f := by
  have hE : constantCoeff (exp K - 1 : PowerSeries K) = 0 := by simp
  have hf' := HasSubst.of_constantCoeff_zero hf
  unfold fLog fExp
  have e : (exp K).subst f - 1 = (exp K - 1 : PowerSeries K).subst f := by
    rw [← coe_substAlgHom hf', map_sub, map_one]
  rw [e, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hE) hf',
    log_subst_exp, subst_X hf']

theorem constantCoeff_fLog {g : MvPowerSeries ι K} (hg : MvPowerSeries.constantCoeff g = 1) :
    MvPowerSeries.constantCoeff (fLog g) = 0 := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  unfold fLog
  rw [constantCoeff_powerSeries_subst_mv_eq _ hg1]
  exact constantCoeff_log_eq_zero'

theorem fExp_fLog {g : MvPowerSeries ι K} (hg : MvPowerSeries.constantCoeff g = 1) :
    fExp (fLog g) = g := by
  unfold fExp fLog
  rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' constantCoeff_log_eq_zero')
    $ HasSubst.of_constantCoeff_zero $ by simp [hg], exp_subst_log,
    one_add_X_subst $ HasSubst.of_constantCoeff_zero $ by simp [hg]]
  ring

theorem pd_fExp [Finite ι] (i : ι) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : pd i (fExp f) = fExp f * pd i f :=
  pderiv_exp_subst_eq_mul_pderiv i hf

theorem mul_pd_fLog [Finite ι] (i : ι) {g : MvPowerSeries ι K}
    (hg : MvPowerSeries.constantCoeff g = 1) : g * pd i (fLog g) = pd i g := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hL := one_add_mul_deriv_log_subst $ HasSubst.of_constantCoeff_zero hg1
  have e : (1 : MvPowerSeries ι K) + (g - 1) = g := by ring
  rw [e] at hL
  unfold fLog
  show g * MvPowerSeries.pderiv i (PowerSeries.subst (g - 1) $ log K) = MvPowerSeries.pderiv i g
  rw [Formalism.G.LogCR.pderiv_psubst hg1 (log K) i, ← mul_assoc, hL, one_mul, map_sub, Derivation.map_one_eq_zero, sub_zero]

theorem subst_fExp {κ : Type} [Finite ι] {φ : ι → MvPowerSeries κ K}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst φ (fExp f) = fExp (MvPowerSeries.subst φ f) :=
  psubst_msubst _ hf $ hasSubst_of_forall_constantCoeff_eq_zero hφ

theorem subst_fLog {κ : Type} [Finite ι] {φ : ι → MvPowerSeries κ K}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {g : MvPowerSeries ι K}
    (hg : MvPowerSeries.constantCoeff g = 1) :
    MvPowerSeries.subst φ (fLog g) = fLog (MvPowerSeries.subst φ g) := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hφ' : MvPowerSeries.HasSubst φ := hasSubst_of_forall_constantCoeff_eq_zero hφ
  unfold fLog
  rw [psubst_msubst _ hg1 hφ', ← MvPowerSeries.coe_substAlgHom hφ', map_sub, map_one]

theorem dz_prim (f : PowerSeries K) : dz (prim f) = f := by
  ext n
  rw [dz, PowerSeries.coeff_derivative]
  simp [prim, coeff_mk, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  push_cast
  field_simp

theorem constantCoeff_prim (f : PowerSeries K) : constantCoeff (prim f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [prim]

end Rules


end Formalism.L2.Th1.B
end
section
namespace Formalism.L2.Th1.B.Map

open Formalism.InvariantFactorPaths.G7 (at1 cob)

variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
























end Formalism.L2.Th1.B.Map
end
section
open Formalism.L2.Th1.B (FI atD atS constantCoeff_fExp fExp fExp_add fLog fLog_fExp par phO psubst_msubst psubst_one sgStar wpDiff)
open MvPowerSeries (hasSubst_of_constantCoeff_zero subst_sub)
open PowerSeries (coeff_subst_single subst_comp_subst_apply)
namespace Formalism.L2.Th1.B.ParO

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem fExp_zero {ι : Type} : fExp (0 : MvPowerSeries ι K) = 1 := by
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries ι K) = 0 := map_zero _
  have hne : fExp (0 : MvPowerSeries ι K) ≠ 0 := by
    intro h
    have h1 := constantCoeff_fExp h0
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne $ by rw [mul_one, ← fExp_add h0 h0, add_zero]

theorem fExp_mul_neg {ι : Type} {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    fExp f * fExp (-f) = 1 := by
  have hnf : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
  rw [← fExp_add hf hnf, add_neg_cancel, fExp_zero]


theorem subst_inVar {ι κ : Type} (f : PowerSeries K) (x : ι) {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X x : MvPowerSeries ι K) = 0 := by simp
  rw [Formalism.InvariantFactorPaths.G7.at1, psubst_msubst f hX hb, MvPowerSeries.subst_X hb]

theorem constantCoeff_inVar {ι : Type} (x : ι) {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (at1 x f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf

theorem psubst_fExp {ι : Type} {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst u (fExp f) = fExp (PowerSeries.subst u f) := by
  simp [fExp]
  exact subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
    (PowerSeries.HasSubst.of_constantCoeff_zero hu) _

theorem psubst_neg {ι : Type} {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0)
    (f : PowerSeries K) : PowerSeries.subst u (-f) = -PowerSeries.subst u f := by
  rw [← PowerSeries.coe_substAlgHom $ PowerSeries.HasSubst.of_constantCoeff_zero hu, map_neg]

theorem value_at {ι : Type} {l g ph : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (hph : PowerSeries.constantCoeff ph = 0)
    (e : PowerSeries.subst l g = PowerSeries.X * fExp (-ph))
    {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst (PowerSeries.subst U l) g = U * fExp (-PowerSeries.subst U ph) := by
  have hUS := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hnph : PowerSeries.constantCoeff (-ph) = 0 := by rw [map_neg, hph, neg_zero]
  rw [← subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl) hUS, e, PowerSeries.subst_mul hUS,
    PowerSeries.subst_X hUS, psubst_fExp hU hnph, psubst_neg hU]

theorem inVar_ne_zero {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) (x : Fin 2) :
    at1 x l ≠ 0 := by
  intro h
  have h2 := congrArg (fun φ => MvPowerSeries.coeff (Finsupp.single x 1) φ) h
  simp [Formalism.InvariantFactorPaths.G7.at1, map_zero, coeff_subst_single] at h2
  simp [hl1] at h2

theorem inVar_add_inVar_ne_zero {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) :
    at1 (0 : Fin 2) l + at1 1 l ≠ 0 := by
  intro h
  have h2 := congrArg (fun φ => MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) φ) h
  simp [Formalism.InvariantFactorPaths.G7.at1, map_add, map_zero, coeff_subst_single] at h2
  simp [hl1] at h2

theorem inVar_sub_inVar_ne_zero {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) :
    at1 (0 : Fin 2) l - at1 1 l ≠ 0 := by
  intro h
  have h2 := congrArg (fun φ => MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) φ) h
  simp [Formalism.InvariantFactorPaths.G7.at1, map_sub, map_zero, coeff_subst_single] at h2
  simp [hl1] at h2

theorem ne_zero_of_psubst {ι : Type} {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    {U : MvPowerSeries ι K} (h : PowerSeries.subst U l ≠ 0) : U ≠ 0 := by
  rintro rfl
  exact h $ PowerSeries.subst_zero_of_constantCoeff_zero hl

theorem subst_atS {ι : Type} (g : PowerSeries K) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (atS g) = PowerSeries.subst (b 0 + b 1) g := by
  have h0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  rw [atS, psubst_msubst g h0 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]

theorem subst_atD {ι : Type} (g : PowerSeries K) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (atD g) = PowerSeries.subst (b 0 - b 1) g := by
  have h0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  rw [atD, psubst_msubst g h0 hb, subst_sub hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]

theorem subst_wpDiff {ι : Type} (P : PowerSeries K) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (wpDiff P) =
      b 0 ^ 2 - b 1 ^ 2 +
        b 0 ^ 2 * b 1 ^ 2 * (PowerSeries.subst (b 1) P - PowerSeries.subst (b 0) P) := by
  rw [wpDiff]
  simp [MvPowerSeries.subst_add hb, subst_sub hb, MvPowerSeries.subst_mul hb,
    MvPowerSeries.subst_pow hb, MvPowerSeries.subst_X hb, subst_inVar P 0 hb, subst_inVar P 1 hb]

private theorem constantCoeff_vec_pair_eq_zero {ι : Type} {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    ∀ s, MvPowerSeries.constantCoeff (![a, b] s) = 0 :=
  Fin.forall_fin_two.mpr ⟨ha, hb⟩

theorem curve_at {ι : Type} {l P ep : PowerSeries K} {c0 : K}
    (hl : PowerSeries.constantCoeff l = 0)
    (h : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) (x : ι) :
    MvPowerSeries.X x ^ 2 * (1 + at1 x l ^ 2 * PowerSeries.subst (at1 x l) P) =
      at1 x l ^ 2 * (at1 x ep + MvPowerSeries.C c0 * MvPowerSeries.X x ^ 2) := by
  have hX : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have h2 := congrArg (fun φ : PowerSeries K => PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) φ) h
  simp [PowerSeries.subst_mul hX, PowerSeries.subst_add hX, PowerSeries.subst_pow hX,
    psubst_one hX, PowerSeries.subst_X hX, PowerSeries.subst_C,
    subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl) hX] at h2
  exact h2

end Alg

section Norm

variable {K : Type} [NormedField K] [CharZero K]

theorem log_law {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) :
    PowerSeries.subst F l = at1 0 l + at1 1 l := by
  have h5 := h.2.2.2.2
  simp [Formalism.InvariantFactorPaths.G7.cob] at h5
  linear_combination h5

theorem constantCoeff_FI {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) : MvPowerSeries.constantCoeff (FI F i) = 0 := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (hasSubst_of_constantCoeff_zero $ constantCoeff_vec_pair_eq_zero h0 $ constantCoeff_inVar 1 hi.1)
    (constantCoeff_vec_pair_eq_zero h0 $ constantCoeff_inVar 1 hi.1) h.1

theorem log_FI {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) : PowerSeries.subst (FI F i) l = at1 0 l - at1 1 l := by
  have hX1c : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hb : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 i] :=
    hasSubst_of_constantCoeff_zero $ constantCoeff_vec_pair_eq_zero (by simp) $ constantCoeff_inVar 1 hi.1
  rw [FI, ← psubst_msubst l h.1 hb, log_law h, MvPowerSeries.subst_add hb,
    subst_inVar l 0 hb, subst_inVar l 1 hb]
  show PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l
      + PowerSeries.subst (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) i) l
      = PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l
        - PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l
  rw [← subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hi.1) $ PowerSeries.HasSubst.X 1, hi.2.2, psubst_neg hX1c l, sub_eq_add_neg]

private theorem addition_identity_products_eq_neg_c_mul_sq {R : Type} [CommRing R] [NoZeroDivisors R]
    {L0 L1 X0 X1 F D c EF ED E0 E1 P0 P1 ep0 ep1 c0 : R}
    (hN : L0 ^ 2 * L1 ^ 2 * F * D ≠ 0)
    (KE : L0 ^ 2 * L1 ^ 2 * (F * EF * (D * ED)) =
      (X0 * E0) ^ 2 * (X1 * E1) ^ 2 * (L0 ^ 2 - L1 ^ 2 + L0 ^ 2 * L1 ^ 2 * (P1 - P0)))
    (C0 : X0 ^ 2 * (1 + L0 ^ 2 * P0) = L0 ^ 2 * (ep0 + c0 * X0 ^ 2))
    (C1 : X1 ^ 2 * (1 + L1 ^ 2 * P1) = L1 ^ 2 * (ep1 + c0 * X1 ^ 2))
    (hc : X1 ^ 2 * ep0 - X0 ^ 2 * ep1 = c * F * D) :
    EF * ED = -c * E0 ^ 2 * E1 ^ 2 := by
  have W : X0 ^ 2 * X1 ^ 2 * (L0 ^ 2 - L1 ^ 2 + L0 ^ 2 * L1 ^ 2 * (P1 - P0)) =
      -(L0 ^ 2 * L1 ^ 2 * c * F * D) := by
    linear_combination (-(L0 ^ 2 * L1 ^ 2)) * hc + (X0 ^ 2 * L0 ^ 2) * C1 - (X1 ^ 2 * L1 ^ 2) * C0
  apply mul_left_cancel₀ hN
  linear_combination KE + (E0 ^ 2 * E1 ^ 2) * W

theorem par_eq (hA : AddSgStar) (hD : PhODef) {g2 g3 s2 c0 : K} {P l i ep : PowerSeries K}
    {F c : MvPowerSeries (Fin 2) K} (hP : IsWp g2 g3 P) (hF : LawLog F l) (hi : IsInv l i)
    (h3 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2))
    (hc : MvPowerSeries.X 1 ^ 2 * at1 0 ep - MvPowerSeries.X 0 ^ 2 * at1 1 ep = c * F * FI F i) :
    par F i (phO s2 P l) = -fLog (-c) := by
  have hl0 := hF.2.2.1
  have hl1 : PowerSeries.coeff 1 l = 1 := hF.2.2.2.1
  have hF0 := hF.1
  have hD0 := constantCoeff_FI hF hi
  obtain ⟨hψ0, e⟩ := hD K s2 P l hl0 hl1
  have hAd := hA K g2 g3 s2 P hP
  have hb : MvPowerSeries.HasSubst ![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] :=
    hasSubst_of_constantCoeff_zero (constantCoeff_vec_pair_eq_zero (constantCoeff_inVar 0 hl0) (constantCoeff_inVar 1 hl0))
  have hb0 : (![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] : Fin 2 → MvPowerSeries (Fin 2) K) 0 =
      Formalism.InvariantFactorPaths.G7.at1 0 l := rfl
  have hb1 : (![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] : Fin 2 → MvPowerSeries (Fin 2) K) 1 =
      Formalism.InvariantFactorPaths.G7.at1 1 l := rfl
  have KE := congrArg
    (fun φ => MvPowerSeries.subst ![(Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 l] φ) hAd
  simp [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_pow hb, MvPowerSeries.subst_X hb,
    subst_atS (sgStar s2 P) hb, subst_atD (sgStar s2 P) hb,
    subst_inVar (sgStar s2 P) 0 hb, subst_inVar (sgStar s2 P) 1 hb,
    subst_wpDiff P hb, hb0, hb1] at KE
  have s0 : PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) (sgStar s2 P) =
      MvPowerSeries.X 0 * fExp (-Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l)) :=
    value_at hl0 hψ0 e (U := MvPowerSeries.X 0) (by simp)
  have s1 : PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 1 l : MvPowerSeries (Fin 2) K) (sgStar s2 P) =
      MvPowerSeries.X 1 * fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l)) :=
    value_at hl0 hψ0 e (U := MvPowerSeries.X 1) (by simp)
  rw [← log_law hF, ← log_FI hF hi, value_at hl0 hψ0 e hF0, value_at hl0 hψ0 e hD0, s0, s1] at KE
  have hL1 := inVar_ne_zero hl1 1
  have hFne : F ≠ 0 := ne_zero_of_psubst hl0
    (by rw [log_law hF]; exact inVar_add_inVar_ne_zero hl1)
  have hEE := addition_identity_products_eq_neg_c_mul_sq
    (L0 := (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K)) (L1 := Formalism.InvariantFactorPaths.G7.at1 1 l)
    (X0 := MvPowerSeries.X 0) (X1 := MvPowerSeries.X 1) (F := F) (D := FI F i) (c := c)
    (EF := fExp (-PowerSeries.subst F (phO s2 P l)))
    (ED := fExp (-PowerSeries.subst (FI F i) (phO s2 P l)))
    (E0 := fExp (-Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l)))
    (E1 := fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l)))
    (P0 := PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 0 l : MvPowerSeries (Fin 2) K) P)
    (P1 := PowerSeries.subst (Formalism.InvariantFactorPaths.G7.at1 1 l : MvPowerSeries (Fin 2) K) P)
    (ep0 := Formalism.InvariantFactorPaths.G7.at1 0 ep) (ep1 := Formalism.InvariantFactorPaths.G7.at1 1 ep) (c0 := MvPowerSeries.C c0)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (inVar_ne_zero hl1 0)) (pow_ne_zero 2 hL1)) hFne) (ne_zero_of_psubst hl0 (by rw [log_FI hF hi]; exact inVar_sub_inVar_ne_zero hl1))) (by linear_combination KE) (by linear_combination (curve_at (ι := Fin 2) hl0 h3 0)) (by linear_combination (curve_at (ι := Fin 2) hl0 h3 1))
    $ by linear_combination hc
  have hA0 : MvPowerSeries.constantCoeff (PowerSeries.subst F (phO s2 P l)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hF0 _ hψ0
  have ha0 : MvPowerSeries.constantCoeff
      (Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l) : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_inVar 0 hψ0
  have ha1 : MvPowerSeries.constantCoeff
      (Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l) : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_inVar 1 hψ0
  have m0 := fExp_mul_neg ha0
  have m1 := fExp_mul_neg ha1
  have hc' : -c = fExp (-PowerSeries.subst F (phO s2 P l)) *
      fExp (-PowerSeries.subst (FI F i) (phO s2 P l)) *
      fExp (Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 *
      fExp (Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 := by
    linear_combination
      (-(fExp (Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 *
        fExp (Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2)) * hEE +
      (c * (fExp (Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l) : MvPowerSeries (Fin 2) K) *
          fExp (-Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l)) + 1) *
        (fExp (Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l) : MvPowerSeries (Fin 2) K) *
          fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l))) ^ 2) * m0 +
      (c * (fExp (Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l) : MvPowerSeries (Fin 2) K) *
          fExp (-Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l)) + 1)) * m1
  have hprod : fExp (-PowerSeries.subst F (phO s2 P l)) *
      fExp (-PowerSeries.subst (FI F i) (phO s2 P l)) *
      fExp (Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 *
      fExp (Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l) : MvPowerSeries (Fin 2) K) ^ 2 =
      fExp (-PowerSeries.subst F (phO s2 P l) +
        -PowerSeries.subst (FI F i) (phO s2 P l) +
        (Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l)) +
        (Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l))) := by
    rw [fExp_add, fExp_add, fExp_add, fExp_add, fExp_add]
    ring
    all_goals simp [hA0, PowerSeries.constantCoeff_subst_eq_zero hD0 _ hψ0, ha0, ha1]
  have hlog : fLog (-c) = -PowerSeries.subst F (phO s2 P l) +
        -PowerSeries.subst (FI F i) (phO s2 P l) +
        (Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 0 (phO s2 P l)) +
        (Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l) + Formalism.InvariantFactorPaths.G7.at1 1 (phO s2 P l)) := by
    rw [hc', hprod]
    apply fLog_fExp
    simp [hA0, PowerSeries.constantCoeff_subst_eq_zero hD0 _ hψ0, ha0, ha1]
  rw [par, hlog]
  ring

end Norm

theorem ParO_of (hA : AddSgStar) (hD : PhODef) (hL : SimeqLog) : ParO := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hCC
  obtain ⟨-, -, h3, c, hcI, hc1, hc⟩ := hCC
  rw [par_eq hA hD hP hF hi h3 hc]
  have hI : Formalism.DworkPowerSeriesWeights.Integral $ -c := by
    intro n
    rw [map_neg, norm_neg]
    exact hcI n
  exact (hL K (Fin 2) (-c) (by rw [map_neg, hc1, neg_neg]) hI).2

section Alg2

variable {K : Type} [Field K] [CharZero K]





end Alg2


end Formalism.L2.Th1.B.ParO
end
section
namespace Formalism.L2.Th1.B.Ph

open PowerSeries

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem hs {l : PowerSeries K} (hl : constantCoeff l = 0) : HasSubst l := by
  exact HasSubst.of_constantCoeff_zero' hl

theorem psubst_neg {l : PowerSeries K} (hl : constantCoeff l = 0) (f : PowerSeries K) :
    subst l (-f) = -subst l f := by
  rw [← coe_substAlgHom $ hs hl, map_neg]

theorem psubst_C_mul {l : PowerSeries K} (hl : constantCoeff l = 0) (c : K) (f : PowerSeries K) :
    subst l (C c * f) = C c * subst l f := by
  rw [subst_mul $ hs hl, subst_C]
  rfl

theorem constantCoeff_psubst {l : PowerSeries K} (hl : constantCoeff l = 0) (g : PowerSeries K) :
    constantCoeff (subst l g) = constantCoeff g := by
  have h0 : constantCoeff (subst l $ g - C (constantCoeff g)) = 0 :=
    constantCoeff_subst_eq_zero hl _ $ by simp
  have hg : g = C (constantCoeff g) + (g - C (constantCoeff g)) := by ring
  conv_lhs => rw [hg]
  rw [subst_add $ hs hl, map_add, h0, subst_C, add_zero]
  rfl

theorem psubst_fExp {l f : PowerSeries K} (hl : constantCoeff l = 0) (hf : constantCoeff f = 0) :
    subst l (fExp f) = fExp (subst l f) := by
  unfold fExp
  exact subst_comp_subst_apply (hs hf) (hs hl) _



theorem coeff_prim_succ (f : PowerSeries K) (n : ℕ) :
    coeff (n + 1) (prim f) = coeff n f / ((n + 1 : ℕ) : K) := by
  simp [prim]

theorem coeff_zero_prim (f : PowerSeries K) : coeff 0 (prim f) = 0 := by
  simp [prim]


theorem constantCoeff_sigS (P : PowerSeries K) : constantCoeff (sigS P) = 0 := by
  rw [sigS, map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_prim, neg_zero]




theorem X_mul_lU {l : PowerSeries K} (hl : constantCoeff l = 0) : X * lU l = l := by
  ext n
  rcases n with _ | n
  rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, hl]
  rw [coeff_succ_X_mul, lU, coeff_mk]

theorem constantCoeff_lU (l : PowerSeries K) : constantCoeff (lU l) = coeff 1 l := by
  rw [← coeff_zero_eq_constantCoeff_apply, lU, coeff_mk]

theorem constantCoeff_gauss (c : K) {l : PowerSeries K} (hl : constantCoeff l = 0) :
    constantCoeff (-(C c * l ^ 2)) = 0 := by
  simp [hl]

theorem psubst_gauss (c : K) {l : PowerSeries K} (hl : constantCoeff l = 0) :
    subst l (fExp $ -(C c * X ^ 2)) = fExp (-(C c * l ^ 2)) := by
  rw [psubst_fExp hl $ by simp, psubst_neg hl, psubst_C_mul hl, subst_pow $ hs hl, subst_X $ hs hl]

theorem constantCoeff_phO (s2 : K) (P : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) (hl1 : coeff 1 l = 1) : constantCoeff (phO s2 P l) = 0 := by
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rwa [hl1] at this
  have hF : constantCoeff (fLog $ lU l) = 0 := constantCoeff_fLog hlu
  rw [phO, map_sub, map_add, map_neg, constantCoeff_psubst hl, constantCoeff_sigS, map_mul, map_pow, hl, hF]
  simp


end Alg

theorem logSigmaPullbackSpec : PhODef := by
  intro K _ _ s2 P l hl hl1
  use constantCoeff_phO s2 P hl hl1
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rwa [hl1] at this
  have hA : constantCoeff (fLog $ lU l) = 0 := constantCoeff_fLog hlu
  have hB : constantCoeff (subst l $ sigS P) = 0 := by rw [constantCoeff_psubst hl, constantCoeff_sigS]
  have hAB : constantCoeff (fLog (lU l) + subst l (sigS P)) = 0 := by rw [map_add, hA, hB, add_zero]
  have e : -phO s2 P l = fLog (lU l) + subst l (sigS P) + -(C (s2 / 2) * l ^ 2) := by
    rw [phO]
    ring
  rw [sgStar, sigma, subst_mul $ hs hl, subst_mul $ hs hl, subst_X $ hs hl,
    psubst_fExp hl $ constantCoeff_sigS P, psubst_gauss _ hl]
  calc l * fExp (subst l $ sigS P) * fExp (-(C (s2 / 2) * l ^ 2))
      = X * fExp (fLog $ lU l) * fExp (subst l $ sigS P) * fExp (-(C (s2 / 2) * l ^ 2)) := by
        rw [fExp_fLog hlu, X_mul_lU hl]
    _ = X * fExp (-phO s2 P l) := by
        rw [e, fExp_add hAB $ constantCoeff_gauss _ hl, fExp_add hA hB]
        ring


section Parity

variable {K : Type} [Field K] [CharZero K]




end Parity




end Formalism.L2.Th1.B.Ph
end
section
open Derivation (leibniz leibniz_pow)
open Finsupp (single)
open MvPowerSeries (coeff_X_pow pderiv pderiv_X_of_ne pderiv_X_self)
open Nat (add_one_sub_one cast_ofNat)
open PowerSeries (coeff_mk coeff_zero_eq_constantCoeff_apply derivative log subst_C)
namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (at1)

namespace Add0

section

variable {K : Type} [Field K] [CharZero K]

local notation "A2" => MvPowerSeries (Fin 2) K

theorem triple_lintegral_eq (x : Fin 2) (f : PowerSeries K) :
    (at1 x f : A2) = PowerSeries.substAlgHom (PowerSeries.HasSubst.X x) f := by
  rw [PowerSeries.coe_substAlgHom]
  rfl

private theorem coeff_at1_fin_two_eq_ite (x : Fin 2) (f : PowerSeries K) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (at1 x f : A2) = if d = single x (d x) then PowerSeries.coeff (d x) f else 0 := by
  classical
  unfold at1
  rw [PowerSeries.coeff_subst $ PowerSeries.HasSubst.X x]
  simp [coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  rw [finsum_eq_single _ (d x) fun n hn => by
    rw [if_neg]
    intro h'
    apply hn
    have := congrArg (fun e => e x) h'
    simp at this
    exact this.symm, if_pos h]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro n
  rw [if_neg]
  intro h'
  apply h
  rw [h']
  simp

theorem pderiv_series_at_variable (i x : Fin 2) (f : PowerSeries K) :
    pd i (at1 x f : A2) = at1 x (dz f) * pd i (MvPowerSeries.X x : A2) := by
  classical
  ext d
  rw [MvPowerSeries.coeff_pderiv, coeff_at1_fin_two_eq_ite]
  by_cases hix : i = x
  subst hix
  rw [show pd i (MvPowerSeries.X i : A2) = 1 from pderiv_X_self, mul_one, coeff_at1_fin_two_eq_ite,
    PowerSeries.coeff_derivative]
  by_cases hd : d = single i (d i)
  have h2 : d + single i 1 = single i ((d + single i 1 : Fin 2 →₀ ℕ) i) := by
    conv_lhs => rw [hd]
    simp
  rw [if_pos h2, if_pos hd, Finsupp.add_apply, Finsupp.single_eq_same]
  have h2 : ¬ d + single i 1 = single i ((d + single i 1 : Fin 2 →₀ ℕ) i) := by
    intro h'
    apply hd
    ext j
    have := congrArg (fun e => e j) h'
    by_cases hj : j = i
    subst hj
    simp
    simp [Ne.symm hj] at this ⊢
    exact this
  rw [if_neg h2, if_neg hd, zero_mul]
  rw [show pd i (MvPowerSeries.X x : A2) = 0 from pderiv_X_of_ne $ Ne.symm hix, mul_zero,
    map_zero]
  have h2 : ¬ d + single i 1 = single x ((d + single i 1 : Fin 2 →₀ ℕ) x) := by
    intro h'
    have := congrArg (fun e => e i) h'
    simp [Ne.symm hix] at this
  rw [if_neg h2, zero_mul]

theorem partialDeriv_inVar_self (x : Fin 2) (f : PowerSeries K) : pd x (at1 x f : A2) = at1 x (dz f) := by
  rw [pderiv_series_at_variable, show pd x (MvPowerSeries.X x : A2) = 1 from pderiv_X_self, mul_one]

theorem partialDeriv_inVar_of_ne {i x : Fin 2} (h : x ≠ i) (f : PowerSeries K) : pd i (at1 x f : A2) = 0 := by
  rw [pderiv_series_at_variable, show pd i (MvPowerSeries.X x : A2) = 0 from pderiv_X_of_ne h, mul_zero]

theorem pd_two (i : Fin 2) : pderiv i (2 : A2) = 0 := by
  rw [show (2 : A2) = ((2 : ℕ) : A2) by norm_num, Derivation.map_natCast]

def Lop (f : A2) : A2 :=
  f * (pd 0 (pd 0 f) - pd 1 (pd 1 f)) - pd 0 f ^ 2 + pd 1 f ^ 2

theorem ring_core {R : Type} [CommRing R] (a b p r p1 r1 p2 r2 h g3 : R)
    (F1a : a ^ 4 * p1 ^ 2 - 4 * a * p1 = 12 * p + 12 * a ^ 2 * p ^ 2 + 4 * a ^ 4 * p ^ 3 -
      (2 * h) * a ^ 2 * (1 + a ^ 2 * p) - g3 * a ^ 4)
    (KoszulLowersPower : a ^ 2 * p2 = 12 * p + 6 * a ^ 2 * p ^ 2 - h * a ^ 2)
    (AutomorphicLevelEquivariance : b ^ 4 * r1 ^ 2 - 4 * b * r1 = 12 * r + 12 * b ^ 2 * r ^ 2 + 4 * b ^ 4 * r ^ 3 -
      (2 * h) * b ^ 2 * (1 + b ^ 2 * r) - g3 * b ^ 4)
    (KoszulImageInIdeal : b ^ 2 * r2 = 12 * r + 6 * b ^ 2 * r ^ 2 - h * b ^ 2) :
    (a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) *
      ((2 + 2 * b ^ 2 * (r - p) - 4 * a * b ^ 2 * p1 - a ^ 2 * b ^ 2 * p2) -
        (-2 + 2 * a ^ 2 * (r - p) + 4 * a ^ 2 * b * r1 + a ^ 2 * b ^ 2 * r2)) -
      (2 * a + 2 * a * b ^ 2 * (r - p) - a ^ 2 * b ^ 2 * p1) ^ 2 +
      (-2 * b + 2 * a ^ 2 * b * (r - p) + a ^ 2 * b ^ 2 * r1) ^ 2 =
    (2 * p - 2 * r) * (a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) ^ 2 := by
  linear_combination (-b ^ 4) * F1a + (-(a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) * b ^ 2) * KoszulLowersPower +
    (a ^ 4) * AutomorphicLevelEquivariance + (-(a ^ 2 - b ^ 2 + a ^ 2 * b ^ 2 * (r - p)) * a ^ 2) * KoszulImageInIdeal

theorem pderiv_zero_weierstrass_difference (P : PowerSeries K) : pd 0 (wpDiff P) =
    2 * MvPowerSeries.X 0 + 2 * MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 2 * (at1 1 P - at1 0 P) -
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 0 (dz P) := by
  unfold wpDiff
  have s0 : ∀ f, pderiv 0 (at1 0 f : A2) = at1 0 (dz f) :=
    fun f => partialDeriv_inVar_self 0 f
  have s1 : ∀ f, pderiv 1 (at1 1 f : A2) = at1 1 (dz f) :=
    fun f => partialDeriv_inVar_self 1 f
  have n01 : ∀ f, pderiv 0 (at1 1 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have n10 : ∀ f, pderiv 1 (at1 0 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have t0 : pderiv 0 (2 : A2) = 0 := pd_two 0
  have t1 : pderiv 1 (2 : A2) = 0 := pd_two 1
  simp [pd, map_add, map_sub, map_neg, leibniz, leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    pderiv_X_self, pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) $ by decide,
    pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) $ by decide, s0, n01,
    map_zero, mul_one, mul_zero, zero_add, sub_zero, cast_ofNat, pow_one,
    add_one_sub_one]
  ring

theorem pderiv_one_weierstrass_difference (P : PowerSeries K) : pd 1 (wpDiff P) =
    -2 * MvPowerSeries.X 1 + 2 * MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 * (at1 1 P - at1 0 P) +
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 1 (dz P) := by
  unfold wpDiff
  have s0 : ∀ f, pderiv 0 (at1 0 f : A2) = at1 0 (dz f) :=
    fun f => partialDeriv_inVar_self 0 f
  have s1 : ∀ f, pderiv 1 (at1 1 f : A2) = at1 1 (dz f) :=
    fun f => partialDeriv_inVar_self 1 f
  have n01 : ∀ f, pderiv 0 (at1 1 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have n10 : ∀ f, pderiv 1 (at1 0 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have t0 : pderiv 0 (2 : A2) = 0 := pd_two 0
  have t1 : pderiv 1 (2 : A2) = 0 := pd_two 1
  simp [pd, map_add, map_sub, map_neg, leibniz, leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    pderiv_X_self, pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) $ by decide,
    pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) $ by decide, s1, n10,
    map_zero, mul_one, mul_zero, add_zero, sub_zero, cast_ofNat, pow_one,
    add_one_sub_one]
  ring

theorem pderiv_zero_zero_weierstrass_difference (P : PowerSeries K) : pd 0 (pd 0 $ wpDiff P) =
    2 + 2 * MvPowerSeries.X 1 ^ 2 * (at1 1 P - at1 0 P) -
      4 * MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 2 * at1 0 (dz P) -
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 0 (dz $ dz P) := by
  rw [pderiv_zero_weierstrass_difference]
  have s0 : ∀ f, pderiv 0 (at1 0 f : A2) = at1 0 (dz f) :=
    fun f => partialDeriv_inVar_self 0 f
  have s1 : ∀ f, pderiv 1 (at1 1 f : A2) = at1 1 (dz f) :=
    fun f => partialDeriv_inVar_self 1 f
  have n01 : ∀ f, pderiv 0 (at1 1 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have n10 : ∀ f, pderiv 1 (at1 0 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have t0 : pderiv 0 (2 : A2) = 0 := pd_two 0
  have t1 : pderiv 1 (2 : A2) = 0 := pd_two 1
  simp [pd, map_add, map_sub, map_neg, leibniz, leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    pderiv_X_self, pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) $ by decide,
    pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) $ by decide, s0, n01, t0,
    map_zero, mul_one, mul_zero, add_zero, zero_add, cast_ofNat, pow_one,
    add_one_sub_one]
  ring

theorem pderiv_one_one_weierstrass_difference (P : PowerSeries K) : pd 1 (pd 1 $ wpDiff P) =
    -2 + 2 * MvPowerSeries.X 0 ^ 2 * (at1 1 P - at1 0 P) +
      4 * MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 * at1 1 (dz P) +
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 1 (dz $ dz P) := by
  rw [pderiv_one_weierstrass_difference]
  have s0 : ∀ f, pderiv 0 (at1 0 f : A2) = at1 0 (dz f) :=
    fun f => partialDeriv_inVar_self 0 f
  have s1 : ∀ f, pderiv 1 (at1 1 f : A2) = at1 1 (dz f) :=
    fun f => partialDeriv_inVar_self 1 f
  have n01 : ∀ f, pderiv 0 (at1 1 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have n10 : ∀ f, pderiv 1 (at1 0 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have t0 : pderiv 0 (2 : A2) = 0 := pd_two 0
  have t1 : pderiv 1 (2 : A2) = 0 := pd_two 1
  simp [pd, map_add, map_sub, map_neg, leibniz, leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    pderiv_X_self, pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) $ by decide,
    pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) $ by decide, s1, n10, t1,
    map_zero, mul_one, mul_zero, add_zero, sub_zero, cast_ofNat, pow_one,
    add_one_sub_one]
  ring

theorem Lop_mulD (N : A2) :
    Lop ((MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) * N) =
      (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) ^ 2 * Lop N := by
  unfold Lop
  simp [pd, leibniz, leibniz_pow, map_sub, map_add, smul_eq_mul, nsmul_eq_mul,
    pderiv_X_self, pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) $ by decide,
    pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) $ by decide, mul_one, mul_zero, zero_mul,
    add_zero, cast_ofNat, pow_one, add_one_sub_one, sub_zero, pd_two, map_zero]
  ring

theorem series_at_variable_const (x : Fin 2) (c : K) : (at1 x (PowerSeries.C c) : A2) = MvPowerSeries.C c := by
  exact subst_C c

theorem Lop_wpDiff (h8 : WpReduced) {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) :
    Lop (wpDiff P) = (2 * at1 0 P - 2 * at1 1 P) * wpDiff P ^ 2 := by
  obtain ⟨hA, hB⟩ := h8 K g2 g3 P hP
  have hX : ∀ x : Fin 2, (at1 x PowerSeries.X : A2) = MvPowerSeries.X x := fun x =>
    PowerSeries.subst_X (PowerSeries.HasSubst.X x)
  have T : ∀ x F,
      PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := K) x) F = (at1 x F : A2) :=
    fun x F => (triple_lintegral_eq x F).symm
  have hC : (MvPowerSeries.C g2 : A2) = 2 * MvPowerSeries.C (g2 / 2) := by
    have e : g2 = 2 * (g2 / 2) := by ring
    conv_lhs => rw [e]
    rw [map_mul, map_ofNat]
  have F1 : ∀ x : Fin 2, (MvPowerSeries.X x) ^ 4 * (at1 x (dz P)) ^ 2 - 4 * MvPowerSeries.X x * at1 x (dz P) =
      12 * at1 x P + 12 * (MvPowerSeries.X x) ^ 2 * (at1 x P) ^ 2 + 4 * (MvPowerSeries.X x) ^ 4 * (at1 x P) ^ 3 -
        MvPowerSeries.C g2 * (MvPowerSeries.X x) ^ 2 * (1 + (MvPowerSeries.X x) ^ 2 * at1 x P) -
        MvPowerSeries.C g3 * (MvPowerSeries.X x) ^ 4 := by
    intro x
    have := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := K) x)) hA
    simp [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one] at this
    simp [T, hX, series_at_variable_const] at this
    exact this
  have F2 : ∀ x : Fin 2, (MvPowerSeries.X x) ^ 2 * at1 x (dz (dz P)) =
      12 * at1 x P + 6 * (MvPowerSeries.X x) ^ 2 * (at1 x P) ^ 2 -
        MvPowerSeries.C (g2 / 2) * (MvPowerSeries.X x) ^ 2 := by
    intro x
    have := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := K) x)) hB
    simp [map_sub, map_add, map_mul, map_pow, map_ofNat] at this
    simp [T, hX, series_at_variable_const] at this
    exact this
  have F1a := F1 0
  have AutomorphicLevelEquivariance := F1 1
  rw [hC] at F1a AutomorphicLevelEquivariance
  have key := ring_core (MvPowerSeries.X 0 : A2) (MvPowerSeries.X 1) (at1 0 P) (at1 1 P) (at1 0 (dz P))
    (at1 1 (dz P)) (at1 0 (dz (dz P))) (at1 1 (dz (dz P))) (MvPowerSeries.C (g2 / 2)) (MvPowerSeries.C g3)
    (by linear_combination F1a) (F2 0) (by linear_combination AutomorphicLevelEquivariance) (F2 1)
  unfold Lop
  rw [pderiv_zero_zero_weierstrass_difference, pderiv_one_one_weierstrass_difference, pderiv_zero_weierstrass_difference, pderiv_one_weierstrass_difference]
  unfold wpDiff
  linear_combination key

theorem wpDiff_eq (h9 : DqRule) {P : PowerSeries K}
    (hP : ∀ n, Odd n → PowerSeries.coeff n P = 0) :
    wpDiff P = (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) *
      (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P) := by
  unfold wpDiff
  linear_combination (-(MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 : A2)) * h9 K P hP

theorem D_ne_zero : (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2 : A2) ≠ 0 := by
  intro h
  have := congrArg (MvPowerSeries.coeff $ single (0 : Fin 2) 2) h
  have hne : (single (0 : Fin 2) 2) ≠ single 1 2 := by
    intro h'
    have := (Finsupp.single_left_inj two_ne_zero).1 h'
    apply absurd this
    decide
  simp [coeff_X_pow, hne] at this

theorem ne_zero_of_cc {N : A2} (h : MvPowerSeries.constantCoeff N = 1) : N ≠ 0 := by
  intro h0
  rw [h0, map_zero] at h
  exact zero_ne_one h

theorem Lop_log (h2 : ExpLogDeriv) {N : A2} (hN : MvPowerSeries.constantCoeff N = 1) :
    N ^ 2 * (pd 0 (pd 0 $ fLog N) - pd 1 (pd 1 $ fLog N)) = Lop N := by
  have e0 := (h2 K (Fin 2) 0).2 N hN
  have e1 := (h2 K (Fin 2) 1).2 N hN
  have d0 : pd 0 (N * pd 0 (fLog N)) = pd 0 (pd 0 N) := by rw [e0]
  have d1 : pd 1 (N * pd 1 (fLog N)) = pd 1 (pd 1 N) := by rw [e1]
  simp [pd, leibniz, smul_eq_mul] at d0 d1 e0 e1 ⊢
  unfold Lop
  simp [pd]
  linear_combination N * d0 - pderiv 0 N * e0 - N * d1 + pderiv 1 N * e1

theorem evalYZero_eq (h : A2) : ev0 h = MvPowerSeries.substAlgHom Formalism.G.LogP.hb0 h := by
  rw [MvPowerSeries.coe_substAlgHom]
  rfl

theorem evalFirst_X_one_mul_eq_zero (h : A2) : ev0 (MvPowerSeries.X 1 * h) = 0 := by
  rw [evalYZero_eq, map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X Formalism.G.LogP.hb0]
  simp

theorem fLog_one {ι : Type} : fLog (1 : MvPowerSeries ι K) = 0 := by
  unfold fLog
  rw [sub_self]
  have ha : PowerSeries.HasSubst (0 : MvPowerSeries ι K) := PowerSeries.HasSubst.of_constantCoeff_zero $ by simp
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 $ show PowerSeries.constantCoeff (log K) = 0 by
    simp [log]
  rw [hg, ← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha, zero_mul]

end

end Add0

open Add0

theorem AddSigmaLog_of (h2 : ExpLogDeriv) (h3 : ExpLogSubst) (h4 : PrimRules)
    (h5 : WaveUnique) (h6 : WaveKills) (h7 : ParCauchy) (h8 : WpReduced) (h9 : DqRule) :
    AddSigmaLog := by
  intro K _ _ g2 g3 P hP
  obtain ⟨f, hf⟩ : ∃ f, f = sigS P := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N,
      N = 1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P := ⟨_, rfl⟩
  rw [← hf, ← hNdef]
  have hN1 : MvPowerSeries.constantCoeff N = 1 := by simp [hNdef]
  obtain ⟨hpr1, -⟩ := h4 K $ prim P
  obtain ⟨hpr1', -⟩ := h4 K P
  have hddf : dz (dz f) = -P := by
    rw [hf, sigS]
    show derivative (derivative $ -prim (prim P)) = -P
    rw [map_neg, map_neg, show derivative (prim $ prim P) = prim P from hpr1,
      show derivative (prim P) = P from hpr1']
  have hLopN : Lop N = (2 * at1 0 P - 2 * at1 1 P) * N ^ 2 := by
    have e1 := Lop_wpDiff h8 hP
    rw [wpDiff_eq h9 $ hP.2.1, ← hNdef, Lop_mulD] at e1
    have hD2 : (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2 : MvPowerSeries (Fin 2) K) ^ 2 ≠ 0 :=
      pow_ne_zero _ D_ne_zero
    apply mul_left_cancel₀ hD2
    rw [e1]
    ring
  have hL : pd 0 (pd 0 $ fLog N) - pd 1 (pd 1 $ fLog N) = 2 * at1 0 P - 2 * at1 1 P := by
    have e2 := Lop_log h2 hN1
    rw [hLopN] at e2
    apply mul_left_cancel₀ $ pow_ne_zero 2 $ ne_zero_of_cc hN1
    rw [e2]
    ring
  have hW := h6 K f
  have hneg : ∀ x, (at1 x (-P) : MvPowerSeries (Fin 2) K) = -at1 x P := fun x => by
    rw [triple_lintegral_eq, map_neg, ← triple_lintegral_eq]
  rw [hddf, hneg, hneg] at hW
  obtain ⟨hc0, hc1⟩ := h7 K f (by
      rw [hf]
      simp [sigS, map_neg, neg_eq_zero]
      rw [← coeff_zero_eq_constantCoeff_apply, prim, coeff_mk, if_pos rfl]) $ by
      rw [hf]
      simp [sigS, map_neg, prim, coeff_mk, one_ne_zero, if_false, Nat.sub_self, if_true,
        zero_div, neg_zero]
  have hφ : ∀ i, MvPowerSeries.constantCoeff (![(PowerSeries.X : PowerSeries K), 0] i) = 0 := by
    intro i
    fin_cases i
    show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0
    exact PowerSeries.constantCoeff_X
    simp
  have hevN : ev0 N = 1 := by
    rw [hNdef, show (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X 1 * (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 * dq P) by ring]
    rw [evalYZero_eq, map_sub, map_one, ← evalYZero_eq, evalFirst_X_one_mul_eq_zero, sub_zero]
  have hevL : ev0 (fLog N) = 0 := by
    have e5 : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0] N = 1 := hevN
    unfold ev0
    rw [(h3 K (Fin 2) Unit ![(PowerSeries.X : PowerSeries K), 0] hφ).2 N hN1, e5, fLog_one]
  have hpdN : pd 1 N = MvPowerSeries.X 1 *
      (-(MvPowerSeries.X 0 ^ 2 * (2 * dq P + MvPowerSeries.X 1 * pd 1 (dq P)))) := by
    rw [hNdef]
    simp [pd, map_sub, map_one, leibniz, leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      pderiv_X_self, pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) $ by decide,
      Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero, cast_ofNat,
      pow_one, add_one_sub_one]
    ring
  have hevpdL : ev0 (pd 1 $ fLog N) = 0 := by
    have e6 := congrArg ev0 $ (h2 K (Fin 2) 1).2 N hN1
    rwa [hpdN, evalFirst_X_one_mul_eq_zero, evalYZero_eq, map_mul, ← evalYZero_eq, ← evalYZero_eq, hevN, one_mul] at e6
  apply sub_eq_zero.1
  apply h5 K
  simp [map_sub]
  linear_combination hW - hL
  rw [evalYZero_eq, map_sub, ← evalYZero_eq, ← evalYZero_eq, hc0, hevL, sub_zero]
  rw [show pd 1 (par0 f - fLog N) = pd 1 (par0 f) - pd 1 (fLog N) from map_sub _ _ _, evalYZero_eq, map_sub,
    ← evalYZero_eq, ← evalYZero_eq, hc1, hevpdL, sub_zero]

namespace Add0

section

variable {K : Type} [Field K] [CharZero K]

theorem subst_fExp (h3 : ExpLogSubst) {u : MvPowerSeries (Fin 2) K}
    (hu : MvPowerSeries.constantCoeff u = 0) {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst u (fExp f) = fExp (PowerSeries.subst u f) := by
  exact (h3 K Unit (Fin 2) (fun _ => u) fun _ => hu).1 f hf

theorem sigS_cc (P : PowerSeries K) : PowerSeries.constantCoeff (sigS P) = 0 := by
  simp [sigS, map_neg, neg_eq_zero]
  rw [← coeff_zero_eq_constantCoeff_apply, prim, coeff_mk, if_pos rfl]

theorem subst_sigma (h3 : ExpLogSubst) (P : PowerSeries K) {u : MvPowerSeries (Fin 2) K}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sigma P) = u * fExp (PowerSeries.subst u $ sigS P) := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero hu
  unfold sigma
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha,
    subst_fExp h3 hu $ sigS_cc P]

theorem subst_sgStar (h3 : ExpLogSubst) (s2 : K) (P : PowerSeries K)
    {u : MvPowerSeries (Fin 2) K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sgStar s2 P) =
      PowerSeries.subst u (sigma P) * fExp (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero hu
  unfold sgStar
  have hg : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) : PowerSeries K) = 0 := by
    simp
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom]
  congr 1
  rw [subst_fExp h3 hu hg]
  congr 1
  rw [← PowerSeries.coe_substAlgHom ha, map_neg, map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X ha, subst_C]

end

end Add0

theorem AddSigma_of (hL : AddSigmaLog) (h1 : ExpLogRules) (h3 : ExpLogSubst) (h9 : DqRule) :
    AddSigma := by
  intro K _ _ g2 g3 P hP
  have hLog := hL K g2 g3 P hP
  obtain ⟨hadd, -, hexplog⟩ := h1 K $ Fin 2
  have hf0 := Add0.sigS_cc P
  have hcc : ∀ (u : MvPowerSeries (Fin 2) K) (g : PowerSeries K), MvPowerSeries.constantCoeff u = 0 →
      PowerSeries.constantCoeff g = 0 → MvPowerSeries.constantCoeff (PowerSeries.subst u g) = 0 := by
    intro u g hu hg
    obtain ⟨g', rfl⟩ := PowerSeries.X_dvd_iff.2 hg
    have ha := PowerSeries.HasSubst.of_constantCoeff_zero hu
    rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha, map_mul,
      hu, zero_mul]
  have hX0 : ∀ x, MvPowerSeries.constantCoeff (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) = 0 :=
    fun x => by simp
  have eS : atS (sigma P) = (MvPowerSeries.X 0 + MvPowerSeries.X 1) * fExp (atS $ sigS P) :=
    Add0.subst_sigma h3 P $ by simp
  have eD : atD (sigma P) = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * fExp (atD $ sigS P) :=
    Add0.subst_sigma h3 P $ by simp
  have e0 : (at1 0 (sigma P) : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X 0 * fExp (at1 0 (sigS P) : MvPowerSeries (Fin 2) K) := Add0.subst_sigma h3 P $ hX0 0
  have e1 : (at1 1 (sigma P) : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X 1 * fExp (at1 1 (sigS P) : MvPowerSeries (Fin 2) K) := Add0.subst_sigma h3 P $ hX0 1
  have cS : MvPowerSeries.constantCoeff (atS $ sigS P) = 0 := hcc _ _ (by simp) hf0
  have cD : MvPowerSeries.constantCoeff (atD $ sigS P) = 0 := hcc _ _ (by simp) hf0
  have c0 : MvPowerSeries.constantCoeff (at1 0 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := hcc _ _ (hX0 0) hf0
  have c1 : MvPowerSeries.constantCoeff (at1 1 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := hcc _ _ (hX0 1) hf0
  have hN1 : MvPowerSeries.constantCoeff
      (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P : MvPowerSeries (Fin 2) K) = 1 := by simp
  obtain ⟨hlog0, hexpN⟩ := hexplog _ hN1
  have hsum : atS (sigS P) + atD (sigS P) = (at1 0 (sigS P) + at1 0 (sigS P)) +
      (at1 1 (sigS P) + at1 1 (sigS P)) + fLog (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P) := by
    unfold par0 at hLog
    linear_combination hLog
  have c00 : MvPowerSeries.constantCoeff (at1 0 (sigS P) + at1 0 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, c0, add_zero]
  have c11 : MvPowerSeries.constantCoeff (at1 1 (sigS P) + at1 1 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, c1, add_zero]
  have c0011 : MvPowerSeries.constantCoeff ((at1 0 (sigS P) + at1 0 (sigS P)) +
      (at1 1 (sigS P) + at1 1 (sigS P)) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, c00, c11, add_zero]
  have hprod : fExp (atS $ sigS P) * fExp (atD $ sigS P) =
      (fExp (at1 0 $ sigS P) * fExp (at1 0 $ sigS P)) * (fExp (at1 1 $ sigS P) * fExp (at1 1 $ sigS P)) *
        (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P) := by
    rw [← hadd _ _ cS cD, hsum, hadd _ _ c0011 hlog0, hadd _ _ c00 c11, hadd _ _ c0 c0, hadd _ _ c1 c1, hexpN]
  rw [eS, eD, e0, e1, Add0.wpDiff_eq h9 hP.2.1]
  linear_combination (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 *
    (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) : MvPowerSeries (Fin 2) K) * hprod

theorem AddSgStar_of (hA : AddSigma) (h1 : ExpLogRules) (h3 : ExpLogSubst) : AddSgStar := by
  intro K _ _ g2 g3 s2 P hP
  obtain ⟨hadd, -, -⟩ := h1 K $ Fin 2
  have hS0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hD0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hX0 : ∀ x, MvPowerSeries.constantCoeff (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) = 0 :=
    fun x => by simp
  have hq : ∀ u : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff u = 0 →
      MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) = 0 := fun u hu => by simp [hu]
  have eS : atS (sgStar s2 P) = atS (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P hS0
  have eD : atD (sgStar s2 P) = atD (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P hD0
  have e0 : (at1 0 (sgStar s2 P) : MvPowerSeries (Fin 2) K) = at1 0 (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P $ hX0 0
  have e1 : (at1 1 (sgStar s2 P) : MvPowerSeries (Fin 2) K) = at1 1 (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P $ hX0 1
  have q0 := hq _ $ hX0 0
  have q1 := hq _ $ hX0 1
  have q00 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2) +
      -(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2)) = 0 := by
    rw [map_add, q0, add_zero]
  have q11 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2) +
      -(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2)) = 0 := by
    rw [map_add, q1, add_zero]
  have hG : fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ 2)) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2)) =
      (fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2))) *
      (fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2))) := by
    rw [← hadd _ _ (hq _ hS0) $ hq _ hD0, ← hadd _ _ q0 q0, ← hadd _ _ q1 q1, ← hadd _ _ q00 q11]
    congr 1
    ring
  rw [eS, eD, e0, e1]
  linear_combination (fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ 2)) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2))) * hA K g2 g3 P hP +
    ((at1 0 (sigma P) : MvPowerSeries (Fin 2) K) ^ 2 * at1 1 (sigma P) ^ 2 * wpDiff P) * hG

end Formalism.L2.Th1.B
end
section
namespace Formalism.L2.Th1.B

open PowerSeries

section Rules

variable {K : Type} [Field K] [CharZero K]

theorem dz_ofNat (n : ℕ) [n.AtLeastTwo] : dz (OfNat.ofNat n : PowerSeries K) = 0 := by
  rw [show (OfNat.ofNat n : PowerSeries K) = C (OfNat.ofNat n : K) from (map_ofNat C n).symm]
  exact PowerSeries.derivative_C

theorem dz_one : dz (1 : PowerSeries K) = 0 := by
  exact Derivation.map_one_eq_zero _

theorem dz_C (a : K) : dz (C a : PowerSeries K) = 0 := PowerSeries.derivative_C

theorem dz_X : dz (X : PowerSeries K) = 1 := PowerSeries.derivative_X

theorem dz_add (f g : PowerSeries K) : dz (f + g) = dz f + dz g := map_add _ f g

theorem dz_sub (f g : PowerSeries K) : dz (f - g) = dz f - dz g := map_sub _ f g


theorem dz_mul (f g : PowerSeries K) : dz (f * g) = f * dz g + g * dz f := by
  simp [dz, Derivation.leibniz, smul_eq_mul]

theorem dz_two : dz (2 : PowerSeries K) = 0 := dz_ofNat 2

theorem dz_four : dz (4 : PowerSeries K) = 0 := dz_ofNat 4

theorem two_ne : (2 : PowerSeries K) ≠ 0 := by
  intro h
  have h2 := congrArg (constantCoeff (R := K)) h
  rw [map_ofNat, map_zero] at h2
  exact two_ne_zero h2

theorem dz_sq (f : PowerSeries K) : dz (f ^ 2) = 2 * f * dz f := by
  rw [pow_two, dz_mul]
  ring

theorem dz_cube (f : PowerSeries K) : dz (f ^ 3) = 3 * f ^ 2 * dz f := by
  rw [pow_succ, dz_mul, dz_sq]
  ring


theorem X_ne : (X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero

theorem ne_zero_of_constantCoeff {f : PowerSeries K} (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h $ map_zero _

end Rules

theorem weierstrassReducedEquations : WpReduced := by
  intro K _ _ g2 g3 P hP
  obtain ⟨_, _, hE⟩ := hP
  have E1 : X ^ 4 * dz P ^ 2 - 4 * X * dz P =
      12 * P + 12 * X ^ 2 * P ^ 2 + 4 * X ^ 4 * P ^ 3 - C g2 * X ^ 2 * (1 + X ^ 2 * P) -
        C g3 * X ^ 4 := by
    apply mul_left_cancel₀ $ pow_ne_zero 2 $ X_ne (K := K)
    linear_combination hE
  use E1
  have hg : (C g2 : PowerSeries K) = 2 * C (g2 / 2) := by
    rw [← map_ofNat C 2, ← map_mul]
    congr 1
    field_simp
  rw [hg] at E1
  have d4 : dz ((X : PowerSeries K) ^ 4) = 4 * X ^ 3 := by
    rw [show (X : PowerSeries K) ^ 4 = (X ^ 2) ^ 2 by ring, dz_sq, dz_sq, dz_X]
    ring
  have hdiff : 4 * X ^ 3 * dz P ^ 2 + 2 * X ^ 4 * dz P * dz (dz P) - 4 * dz P - 4 * X * dz (dz P) =
      12 * dz P + 24 * X * P ^ 2 + 24 * X ^ 2 * P * dz P + 16 * X ^ 3 * P ^ 3 +
        12 * X ^ 4 * P ^ 2 * dz P - 2 * C (g2 / 2) * (2 * X + 4 * X ^ 3 * P + X ^ 4 * dz P) -
        4 * C g3 * X ^ 3 := by
    have h := congrArg dz E1
    have c12 : dz (12 : PowerSeries K) = 0 := dz_ofNat 12
    simp [dz_add, dz_sub, dz_mul, dz_sq, dz_cube, dz_C, dz_X, dz_two, dz_four, c12, dz_one, d4] at h
    linear_combination h
  refine mul_left_cancel₀ (?_ : (2 * X * (X ^ 3 * dz P - 2) : PowerSeries K) ≠ 0) ?_
  refine mul_ne_zero (mul_ne_zero two_ne X_ne) $ ne_zero_of_constantCoeff ?_
  rw [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, map_ofNat]
  norm_num
  linear_combination X ^ 2 * hdiff - 4 * X * E1




end Formalism.L2.Th1.B
end
section
open Filter Topology

namespace Formalism.L2.Th1.F

namespace TaylorSigmaUniqueness

open PowerSeries in

lemma formal_unique (P U V : PowerSeries ℂ) (hV : X * derivative V = -(X * P))
    (hV0 : constantCoeff V = 0) (hU : X * derivative U = X * (V * U))
    (hU0 : constantCoeff U = 1) : U = B.fExp (B.sigS P) := by
  have hV' : derivative V = -P := by
    apply mul_left_cancel₀ $ X_ne_zero (R := ℂ)
    rw [hV, mul_neg]
  have hVp : V = -B.prim P := by
    refine derivative.ext ?_ ?_
    rw [hV', map_neg]
    exact congrArg Neg.neg (B.dz_prim P).symm
    rw [hV0, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0 : constantCoeff (B.sigS P) = 0 := by
    rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0' : constantCoeff (-B.sigS P) = 0 := by rw [map_neg, hS0, neg_zero]
  have hSd : derivative (B.sigS P) = V := by
    rw [B.sigS, map_neg, hVp]
    exact congrArg Neg.neg $ B.dz_prim _
  have key : U * (C.mvExp (-B.sigS P) : PowerSeries ℂ) = 1 := by
    refine derivative.ext ?_ ?_
    rw [Derivation.leibniz, C.derivative_mvExp hS0', map_neg, hSd, mul_left_cancel₀ (X_ne_zero (R := ℂ)) hU, Derivation.map_one_eq_zero]
    simp [smul_eq_mul]
    ring
    rw [map_mul, hU0, map_one, one_mul]
    exact C.constantCoeff_mvExp hS0'
  calc U = U * ((C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P)) := by rw [C.mvExp_neg hS0, mul_one]
    _ = C.mvExp (B.sigS P) := by rw [← mul_assoc, key, one_mul]
    _ = B.fExp (B.sigS P) := rfl

lemma constantCoeff_taylor0 (f : ℂ → ℂ) : PowerSeries.constantCoeff (taylor0 f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, taylor0, PowerSeries.coeff_mk]
  simp

def u (L : PeriodPair) (z : ℂ) : ℂ := ∏' l : L.lattice, wFactor (l : ℂ) z

lemma differentiable_u (L : PeriodPair) : Differentiable ℂ $ u L :=
  SigmaBasic.differentiable_tprod sigma_product_locally_uniform L

lemma u_zero (L : PeriodPair) : u L 0 = 1 := by
  simp [u, SigmaBasic.wFactor_zero_right]

lemma analyticAt_v (L : PeriodPair) : AnalyticAt ℂ (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) 0 :=
  (AnalyticIdentityTheoremsZetaFacts.differentiableOn_zetaExcept L 0).analyticAt $ L.compl_lattice_sdiff_singleton_mem_nhds 0

lemma analyticAt_pExcept (L : PeriodPair) : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 :=
  (L.differentiableOn_weierstrassPExcept 0).analyticAt $ L.compl_lattice_sdiff_singleton_mem_nhds 0

lemma ode_u (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv (u L) z = z * (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases h0 : z = 0
  simp [h0]
  have h2 : HasDerivAt (wSigma L) (1 * u L z + z * deriv (u L) z) z :=
    (hasDerivAt_id z).mul (differentiable_u L z).hasDerivAt
  have h3 := (sigmaLogDeriv_of sigma_product_locally_uniform sigma_summable zeta_summable L z fun h => hz ⟨h, h0⟩).unique h2
  rw [← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L z] at h3
  have h4 : wSigma L z = z * u L z := rfl
  rw [h4] at h3
  have h5 : (1 / z) * z = 1 := by field_simp
  linear_combination -h3 + u L z * h5

lemma ode_v (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -(z * L.weierstrassPExcept 0 z) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases h0 : z = 0
  simp [h0]
  have h2 : HasDerivAt (fun w => 1 / w) (-(1 / z ^ 2)) z := by
    simpa [one_div] using hasDerivAt_inv h0
  have h3 : AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 = fun w => wZeta L w - 1 / w := by
    funext w
    rw [← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L w]
    ring
  have h4 : deriv (fun w => wZeta L w - 1 / w) z = -(L.weierstrassP z) - -(1 / z ^ 2) :=
    ((zeta_has_deriv L z fun h => hz ⟨h, h0⟩).sub h2).deriv
  rw [h3, h4]
  have h5 := L.weierstrassPExcept_add 0 z
  simp [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h5
  rw [← h5]
  ring

end TaylorSigmaUniqueness

open TaylorSigmaUniqueness in

theorem taylorSigma_of (hr : TaylorRing) (hd : TaylorDeriv) : TaylorSigma := by
  intro L
  obtain ⟨hadd, hC, hX, hgerm⟩ := hr
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hu : AnalyticAt ℂ (u L) 0 := (differentiable_u L).analyticAt 0
  have hv := analyticAt_v L
  have hp := analyticAt_pExcept L
  have e1 : taylor0 (wSigma L) = PowerSeries.X * taylor0 (u L) := by
    have := (hadd (fun z => z) (u L) hid hu).2
    rwa [hX] at this
  have eU : PowerSeries.X * PowerSeries.derivative (taylor0 $ u L)
      = PowerSeries.X * (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) * taylor0 (u L)) := by
    have hvu : AnalyticAt ℂ (fun z => AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) 0 := hv.mul hu
    rw [← hd.1 _ hu, ← hX, ← (hadd _ _ hid hu.deriv).2, ← (hadd _ _ hv hu).2,
      ← (hadd _ _ hid hvu).2]
    exact hgerm _ _ $ ode_u L
  rw [e1, B.sigma]
  congr 1
  refine formal_unique (pSeries L) _ _ (by
      have hneg : taylor0 (fun z => (-1 : ℂ) * (z * L.weierstrassPExcept 0 z))
          = -(PowerSeries.X * pSeries L) := by
        have hzp : AnalyticAt ℂ (fun z => z * L.weierstrassPExcept 0 z) 0 := hid.mul hp
        rw [(hadd (fun _ => (-1 : ℂ)) _ analyticAt_const hzp).2, hC,
          (hadd _ _ hid hp).2, hX, pSeries]
        simp
      rw [← hd.1 _ hv, ← hneg, ← hX, ← (hadd _ _ hid hv.deriv).2]
      refine hgerm _ _ $ (ode_v L).mono fun z hz => ?_
      show z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -1 * (z * L.weierstrassPExcept 0 z)
      rw [hz]
      ring) ?_ eU ?_
  rw [constantCoeff_taylor0, AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_zero]
  rw [constantCoeff_taylor0, u_zero]

theorem taylorSgStar_of (h : TaylorSigma) (hr : TaylorRing) (he : TaylorExp) (hent : SigmaEntire) :
    TaylorSgStar := by
  intro L
  obtain ⟨hadd, hC, hX, -⟩ := hr
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hzz : AnalyticAt ℂ (fun z : ℂ => z * z) 0 := hid.mul hid
  have hf : AnalyticAt ℂ (fun z : ℂ => -(s2 L / 2) * (z * z)) 0 := analyticAt_const.mul hzz
  have hef : AnalyticAt ℂ (fun z : ℂ => Complex.exp $ -(s2 L / 2) * (z * z)) 0 := hf.cexp
  have hTf : taylor0 (fun z : ℂ => -(s2 L / 2) * (z * z))
      = -(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) := by
    rw [(hadd (fun _ => -(s2 L / 2)) _ analyticAt_const hzz).2, hC,
      (hadd _ _ hid hid).2, hX, map_neg]
    ring
  have hfun : sgStar L = fun z => wSigma L z * Complex.exp (-(s2 L / 2) * (z * z)) := by
    funext z
    rw [sgStar]
    congr 2
    ring
  rw [hfun, (hadd _ _ ((hent L).analyticAt 0) hef).2, h L, he _ hf $ by simp, hTf, B.sgStar]

namespace TaylorSigmaUniqueness

lemma dblInt_eq (e : PowerSeries ℂ) : C.dblInt e = B.prim (B.prim e) := by
  ext n
  simp [C.dblInt, B.prim, PowerSeries.coeff_mk]
  rcases n with _ | _ | n
  simp
  simp
  have h1 : ((n : ℂ) + 1 + 1) ≠ 0 := by
    have : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr $ by omega
    push_cast at this
    intro h
    apply this; linear_combination h
  simp
  field_simp

end TaylorSigmaUniqueness

open TaylorSigmaUniqueness in

theorem taylorSgStar'_of (h : TaylorSgStar) : TaylorSgStar' := by
  intro L
  rw [h L, B.sgStar, B.sigma, C.sgStar, C.lam, dblInt_eq, mul_assoc]
  congr 1
  have h1 : MvPowerSeries.constantCoeff (B.sigS $ pSeries L) = 0 := by
    have : PowerSeries.constantCoeff (B.sigS $ pSeries L) = 0 := by
      rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
    exact this
  have h2 : MvPowerSeries.constantCoeff
      (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by
    have : PowerSeries.constantCoeff
        (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by simp
    exact this
  rw [← B.fExp_add h1 h2, B.sigS, ← neg_add]
  rfl

end Formalism.L2.Th1.F
end
section
open scoped BigOperators
open Filter Topology

namespace Formalism.L2.Th1.F

namespace EndoZ

open PowerSeries TaylorWp

theorem T.congr {f g : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) (h : f =ᶠ[𝓝 0] g) : T g F :=
  ⟨hf.1.congr h, (taylor_ring.2.2.2 f g h).symm.trans hf.2⟩

private theorem T_const (c : ℂ) : T (fun _ => c) $ C c :=
  ⟨analyticAt_const, taylor_ring.2.1 c⟩

theorem T.neg {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) : T (fun z => -f z) $ -F := by
  convert T.mul taylor_ring (T_const $ -1) hf using 1
  funext z
  simp
  simp

theorem T.sub {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z - g z) $ F - G := by
  simpa [← sub_eq_add_neg] using T.add taylor_ring hf $ T.neg hg

theorem T.sum {ι : Type} (s : Finset ι) (f : ι → ℂ → ℂ) (F : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, T (f i) $ F i) : T (fun z => ∑ i ∈ s, f i z) (∑ i ∈ s, F i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  intro _
  convert T_const (0 : ℂ) using 1 <;> simp
  intro a s ha ih h
  have h1 := T.add taylor_ring (h a $ Finset.mem_insert_self a s)
    $ ih fun i hi => h i $ Finset.mem_insert_of_mem hi
  convert h1 using 1
  funext z
  rw [Finset.sum_insert ha]
  rw [Finset.sum_insert ha]

theorem T.prod {ι : Type} (s : Finset ι) (f : ι → ℂ → ℂ) (F : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, T (f i) $ F i) : T (fun z => ∏ i ∈ s, f i z) (∏ i ∈ s, F i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  intro _
  convert T_const (1 : ℂ) using 1 <;> simp
  intro a s ha ih h
  have h1 := T.mul taylor_ring (h a $ Finset.mem_insert_self a s)
    $ ih fun i hi => h i $ Finset.mem_insert_of_mem hi
  convert h1 using 1
  funext z
  rw [Finset.prod_insert ha]
  rw [Finset.prod_insert ha]

theorem T.deriv {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) :
    T (deriv f) $ derivative F :=
  ⟨hf.1.deriv, by rw [taylor_deriv.1 f hf.1, hf.2]⟩

theorem T.rescale {f : ℂ → ℂ} {F : PowerSeries ℂ} (a : ℂ) (hf : T f F) :
    T (fun z => f $ a * z) $ rescale a F := by
  refine ⟨?_, by rw [taylor_deriv.2.1 f a hf.1, hf.2]⟩
  apply hf.1.comp_of_eq $ analyticAt_const.mul analyticAt_id
  simp
theorem T.unique {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G)
    (h : f =ᶠ[𝓝[≠] 0] g) : F = G := by
  rw [← hf.2, ← hg.2]
  exact taylor_ring.2.2.2 f g $ (hf.1.frequently_eq_iff_eventually_eq hg.1).1 h.frequently

theorem T_p (L : PeriodPair) : T (L.weierstrassPExcept 0) $ pSeries L :=
  ⟨TaylorSigmaUniqueness.analyticAt_pExcept L, rfl⟩

theorem wp_eq (L : PeriodPair) (z : ℂ) :
    L.weierstrassP z = 1 / z ^ 2 + L.weierstrassPExcept 0 z := by
  rw [IsogenyPAux.P_local L 0 L.lattice.zero_mem z, sub_zero, add_comm]

private theorem analyticAt_weierstrassP_of_not_mem (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    AnalyticAt ℂ L.weierstrassP P := by
  have hda : DifferentiableOn ℂ L.weierstrassP (L.lattice : Set ℂ)ᶜ := fun w hw =>
    (PDeriv.hasDerivAt_P L hw).differentiableAt.differentiableWithinAt
  exact hda.analyticAt $ (PeriodPair.isClosed_lattice L).isOpen_compl.mem_nhds hP

theorem T_shift (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    T (fun z => L.weierstrassP $ z + P) $ taylor0 fun z => L.weierstrassP $ z + P := by
  refine ⟨?_, rfl⟩
  apply (analyticAt_weierstrassP_of_not_mem L hP).comp_of_eq $ analyticAt_id.add analyticAt_const
  simp
theorem ev_notMem (L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  first
  | exact ThreeTermRelation.eventually_notMem L 0
  | exact Filter.inf_principal_eq_bot.1
      $ (discreteTopology_subtype_iff.1 $ inferInstanceAs $ DiscreteTopology L.lattice) 0
        L.lattice.zero_mem

theorem tendsto_mul_nhdsNE {α : ℂ} (hα : α ≠ 0) :
    Tendsto (fun z => α * z) (𝓝[≠] 0) $ 𝓝[≠] 0 := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
  have h0 : Tendsto (fun z => α * z) (𝓝 0) $ 𝓝 $ α * 0 := (continuous_const_mul α).tendsto 0
  rw [mul_zero] at h0
  exact h0.mono_left nhdsWithin_le_nhds
  exact mul_ne_zero hα hz

theorem ev_shift_notMem (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z + P ∉ L.lattice := by
  have ho : IsOpen {z : ℂ | z + P ∉ L.lattice} :=
    (PeriodPair.isClosed_lattice L).isOpen_compl.preimage $ continuous_id.add continuous_const
  apply ho.mem_nhds
  simpa using hP
theorem wp_congr (L : PeriodPair) {a b : ℂ} (h : a - b ∈ L.lattice) :
    L.weierstrassP a = L.weierstrassP b := by
  rw [IsogenyPAux.P_local L (a - b) h a, sub_sub_cancel,
    IsogenyPAux.P_local L 0 L.lattice.zero_mem b, sub_zero]

theorem clause3 (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (hα : α ≠ 0) (hm : MulStable L α)
    (hS : IsKerReps L α S) :
    C (α ^ 2) * rescale α (pSeries L) = pSeries L
      + ∑ P : S, (taylor0 (fun z => L.weierstrassP $ z + (P : ℂ)) - C (L.weierstrassP (P : ℂ))) := by
  have hR := T.add taylor_ring (T_p L) $ T.sum Finset.univ
    (fun (P : S) (z : ℂ) => L.weierstrassP (z + (P : ℂ)) - L.weierstrassP (P : ℂ))
    (fun (P : S) => taylor0 (fun z => L.weierstrassP $ z + (P : ℂ)) - C (L.weierstrassP (P : ℂ)))
    fun P _ => T.sub (T_shift L (hS.1 P P.2).2) $ T_const _
  refine T.unique (T.mul taylor_ring (T_const $ α ^ 2) $ T.rescale α $ T_p L) hR ?_
  filter_upwards [ev_notMem L, (tendsto_mul_nhdsNE hα).eventually $ ev_notMem L,
    self_mem_nhdsWithin] with z hz hαz hz0
  have hip := isogenyP L α S hα hm hS z hαz
  rw [← Finset.sum_coe_sort S] at hip
  have e1 : L.weierstrassPExcept 0 (α * z) = L.weierstrassP (α * z) - 1 / (α * z) ^ 2 := by
    rw [wp_eq L $ α * z]
    ring
  have e2 : L.weierstrassPExcept 0 z = L.weierstrassP z - 1 / z ^ 2 := by
    rw [wp_eq L z]
    ring
  beta_reduce
  rw [e1, e2, mul_sub, hip]
  field_simp
  ring

private theorem hasDerivAt_sgStar' (L : PeriodPair) {u : ℂ} (hu : u ∉ L.lattice) :
    HasDerivAt (sgStar L) (sgStar L u * (wZeta L u - s2 L * u)) u := by
  have h3 : HasDerivAt (fun w => -(s2 L) * w ^ 2 / 2) (-(s2 L) * u) u :=
    (((hasDerivAt_pow 2 u).const_mul $ -(s2 L)).div_const 2).congr_deriv (by norm_num <;> ring)
  unfold sgStar
  apply ((sigmaLogDeriv L u hu).mul h3.cexp).congr_deriv
  ring
theorem wp_logDeriv (L : PeriodPair) {P z : ℂ} (hP : P ∉ L.lattice) (hz : z ∉ L.lattice)
    (hp : z + P ∉ L.lattice) (hm : z - P ∉ L.lattice) :
    L.derivWeierstrassP z = (L.weierstrassP z - L.weierstrassP P)
      * (wZeta L (z + P) + wZeta L (z - P) - 2 * wZeta L z) := by
  have hev : (fun u => sgStar L (u + P) * sgStar L (u - P)) =ᶠ[𝓝 z]
      fun u => -(sgStar L u ^ 2 * sgStar L P ^ 2 * (L.weierstrassP u - L.weierstrassP P)) := by
    filter_upwards [(PeriodPair.isClosed_lattice L).isOpen_compl.mem_nhds hz] with u hu
    exact sgStarAdd L u P hu hP
  have hg := ((hasDerivAt_sgStar' L hp).comp z $ (hasDerivAt_id' z).add_const P).mul
    $ (hasDerivAt_sgStar' L hm).comp z $ (hasDerivAt_id' z).sub_const P
  have hsq : HasDerivAt (fun u => sgStar L u ^ 2)
      (2 * sgStar L z * (sgStar L z * (wZeta L z - s2 L * z))) z := by
    apply ((hasDerivAt_sgStar' L hz).pow 2).congr_deriv
    norm_num <;> ring
  have hh := ((hsq.mul_const $ sgStar L P ^ 2).mul
    $ (PDeriv.hasDerivAt_P L hz).sub_const $ L.weierstrassP P).neg
  have heq := hg.unique $ hh.congr_of_eventuallyEq hev
  simp [Function.comp_apply] at heq
  have hs : sgStar L z ≠ 0 := mul_ne_zero (fun h => hz $ (sigmaZero L z).1 h) $ Complex.exp_ne_zero _
  have hc : sgStar L P ≠ 0 := mul_ne_zero (fun h => hP $ (sigmaZero L P).1 h) $ Complex.exp_ne_zero _
  have key : sgStar L z ^ 2 * sgStar L P ^ 2 * (L.derivWeierstrassP z - (L.weierstrassP z
      - L.weierstrassP P) * (wZeta L (z + P) + wZeta L (z - P) - 2 * wZeta L z)) = 0 := by
    linear_combination heq - (wZeta L (z + P) + wZeta L (z - P) - 2 * s2 L * z) * sgStarAdd L z P hz hP
  linear_combination ((mul_eq_zero.1 key).resolve_left $ mul_ne_zero (pow_ne_zero _ hs) $ pow_ne_zero _ hc)

def U (L : PeriodPair) (P : ℂ) : Set ℂ :=
  {w | w ∉ L.lattice ∧ w + P ∉ L.lattice ∧ w - P ∉ L.lattice}

theorem isOpen_U (L : PeriodPair) (P : ℂ) : IsOpen $ U L P := by
  have hc := (PeriodPair.isClosed_lattice L).isOpen_compl
  exact (hc.preimage continuous_id).inter $ (hc.preimage $ continuous_id.add continuous_const).inter
    $ hc.preimage $ continuous_id.sub continuous_const

theorem U_mem (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) : U L P ∈ 𝓝[≠] (0 : ℂ) := by
  have hP' : -P ∉ L.lattice := fun h => hP $ by simpa using L.lattice.neg_mem h
  filter_upwards [ev_notMem L, nhdsWithin_le_nhds $ ev_shift_notMem L hP, nhdsWithin_le_nhds $ ev_shift_notMem L hP'] with z a b c
  exact ⟨a, b, by simpa [sub_eq_add_neg] using c⟩

def fP (L : PeriodPair) (P : ℂ) (z : ℂ) : ℂ :=
  1 + z ^ 2 * (L.weierstrassPExcept 0 z - L.weierstrassP P)

def mP (L : PeriodPair) (P : ℂ) (z : ℂ) : ℂ :=
  2 * z⁻¹ + wZeta L (z + P) + wZeta L (z - P) - 2 * wZeta L z

theorem ne_zero_of_notMem (L : PeriodPair) {w : ℂ} (hw : w ∉ L.lattice) : w ≠ 0 := by
  rintro rfl
  exact hw L.lattice.zero_mem

theorem hasDerivAt_fP (L : PeriodPair) {P w : ℂ} (hP : P ∉ L.lattice) (hw : w ∈ U L P) :
    HasDerivAt (fP L P) (fP L P w * mP L P w) w := by
  obtain ⟨hw0, hwp, hwm⟩ := hw
  have hne := ne_zero_of_notMem L hw0
  have hex : L.weierstrassPExcept 0 = fun u => L.weierstrassP u - (u ^ 2)⁻¹ := by
    funext u
    rw [wp_eq L u]; ring
  have hinv : HasDerivAt (fun u => (u ^ 2)⁻¹) (-(2 * w) / (w ^ 2) ^ 2) w :=
    ((hasDerivAt_pow 2 w).inv $ pow_ne_zero 2 hne).congr_deriv (by norm_num <;> ring)
  have hE : HasDerivAt (L.weierstrassPExcept 0)
      (L.derivWeierstrassP w - (-(2 * w) / (w ^ 2) ^ 2)) w := by
    rw [hex]
    exact (PDeriv.hasDerivAt_P L hw0).sub hinv
  have hF : HasDerivAt (fP L P) (2 * w * (L.weierstrassPExcept 0 w - L.weierstrassP P)
      + w ^ 2 * (L.derivWeierstrassP w - (-(2 * w) / (w ^ 2) ^ 2))) w := by
    have h1 := ((hasDerivAt_pow 2 w).mul $ hE.sub_const $ L.weierstrassP P).const_add 1
    apply h1.congr_deriv
    norm_num <;> ring
  refine hF.congr_deriv ?_
  rw [wp_logDeriv L hP hw0 hwp hwm]
  simp [fP, mP, hex]
  field_simp
  ring

theorem hasDerivAt_mP (L : PeriodPair) {P w : ℂ} (hw : w ∈ U L P) :
    HasDerivAt (mP L P) (2 * L.weierstrassPExcept 0 w - L.weierstrassP (w + P)
      - L.weierstrassP (w - P)) w := by
  obtain ⟨hw0, hwp, hwm⟩ := hw
  have h := ((((hasDerivAt_inv $ ne_zero_of_notMem L hw0).const_mul 2).add $ (zetaHasDeriv L _ hwp).comp w $ (hasDerivAt_id' w).add_const P).add $ (zetaHasDeriv L _ hwm).comp w $ (hasDerivAt_id' w).sub_const P).sub $ (zetaHasDeriv L _ hw0).const_mul 2
  refine h.congr_deriv ?_
  rw [wp_eq L w]
  field_simp
  ring

theorem d2log_fP (L : PeriodPair) {P w : ℂ} (hP : P ∉ L.lattice) (hw : w ∈ U L P) :
    deriv (deriv $ fP L P) w * fP L P w - deriv (fP L P) w ^ 2
      = (2 * L.weierstrassPExcept 0 w - L.weierstrassP (w + P) - L.weierstrassP (w - P))
        * fP L P w ^ 2 := by
  have hev : deriv (fP L P) =ᶠ[𝓝 w] fun u => fP L P u * mP L P u :=
    Filter.eventually_of_mem ((isOpen_U L P).mem_nhds hw) fun u hu => (hasDerivAt_fP L hP hu).deriv
  have hd2 : deriv (deriv $ fP L P) w = fP L P w * mP L P w * mP L P w
      + fP L P w * (2 * L.weierstrassPExcept 0 w - L.weierstrassP (w + P)
        - L.weierstrassP (w - P)) := by
    rw [hev.deriv_eq]
    exact ((hasDerivAt_fP L hP hw).mul $ hasDerivAt_mP L hw).deriv
  rw [hd2, (hasDerivAt_fP L hP hw).deriv]
  ring

theorem T_fP (L : PeriodPair) (P : ℂ) :
    T (fP L P) $ Formalism.L2.Th1.C.wpShift (pSeries L) $ L.weierstrassP P := by
  have hX : T (fun z => z) X := ⟨analyticAt_id, taylor_ring.2.2.1⟩
  have h := T.add taylor_ring (T_const 1) $ T.mul taylor_ring
    (T.pow taylor_ring hX 2) $ T.sub (T_p L) $ T_const $ L.weierstrassP P
  unfold fP Formalism.L2.Th1.C.wpShift
  convert h using 1
  simp

theorem clause2 (L : PeriodPair) {P Q : ℂ} (hP : P ∉ L.lattice) (hQ : Q + P ∈ L.lattice) :
    Formalism.L2.Th1.C.HasSecondLogDeriv (Formalism.L2.Th1.C.wpShift (pSeries L) $ L.weierstrassP P)
      $ 2 * pSeries L - taylor0 (fun z => L.weierstrassP $ z + P)
        - taylor0 fun z => L.weierstrassP $ z + Q := by
  have hF := T_fP L P
  have h1 := T.deriv hF
  have hR := T.mul taylor_ring
    (T.sub (T.sub (T.mul taylor_ring (T_const 2) $ T_p L) $ T_shift L hP) $ T_shift L (by
        intro hq
        apply hP
        have h3 := L.lattice.sub_mem hQ hq
        rwa [add_sub_cancel_left] at h3))
    (T.pow taylor_ring hF 2)
  have heq := T.unique (T.sub (T.mul taylor_ring (T.deriv h1) hF) $ T.pow taylor_ring h1 2) hR $ by
    filter_upwards [U_mem L hP] with w hw
    have hc := wp_congr L (by
      have e : w + Q - (w - P) = Q + P := by ring
      rw [e]
      exact hQ)
    beta_reduce
    rw [d2log_fP L hP hw, hc]
  unfold Formalism.L2.Th1.C.HasSecondLogDeriv
  rw [heq, show (C (2 : ℂ) : PowerSeries ℂ) = 2 from map_ofNat C 2]

theorem exists_neg (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (hS : IsKerReps L α S) (P : S) :
    ∃ Q : S, (Q : ℂ) + (P : ℂ) ∈ L.lattice := by
  obtain ⟨hPα, hPn⟩ := hS.1 P P.2
  obtain ⟨Q, hQ, hQm⟩ := hS.2.2 _ (by rw [mul_neg]; exact L.lattice.neg_mem hPα) fun h => hPn $ by simpa using L.lattice.neg_mem h
  use ⟨Q, hQ⟩
  have h3 := L.lattice.neg_mem hQm
  have e : -(-(P : ℂ) - Q) = Q + P := by ring
  rwa [e] at h3

theorem taylorSgStar' : TaylorSgStar' :=
  taylorSgStar'_of $ taylorSgStar_of (taylorSigma_of taylor_ring taylor_deriv)
    taylor_ring taylor_exp sigmaEntire

theorem T_sgStar (L : PeriodPair) :
    T (sgStar L) $ Formalism.L2.Th1.C.sgStar (pSeries L) $ s2 L := by
  refine ⟨?_, taylorSgStar' L⟩
  have h1 : Differentiable ℂ fun z => Complex.exp $ -(s2 L) * z ^ 2 / 2 := by fun_prop
  exact ((sigmaEntire L).mul h1).analyticAt 0

theorem fP_eq (L : PeriodPair) (P : ℂ) {z : ℂ} (hz : z ≠ 0) :
    fP L P z = z ^ 2 * (L.weierstrassP z - L.weierstrassP P) := by
  unfold fP
  rw [wp_eq L z]
  field_simp
  ring

end EndoZ

theorem integer_endomorphism_instance : EndoZInstance := by
  intro L α S hα hm hS
  choose neg hneg using EndoZ.exists_neg L α S hS
  use neg, hneg
  unfold Formalism.L2.Th1.C.IsEndoZ
  refine ⟨?_, ?_, ?_⟩
  intro P
  apply Subtype.ext
  apply hS.2.1 _ (neg $ neg P).2 _ P.2
  have e : ((neg (neg P) : ℂ) - P) = ((neg (neg P) : ℂ) + neg P) - (neg P + P) := by ring
  rw [e]
  exact L.lattice.sub_mem (hneg $ neg P) $ hneg P
  intro P
  exact EndoZ.clause2 L (hS.1 P P.2).2 $ hneg P
  exact EndoZ.clause3 L α S hα hm hS

open EndoZ TaylorWp in

theorem isogeny_formula_instance : IsogenyFormulaInstance := by
  intro L α S hα hm hS
  have hX : T (fun z => z) PowerSeries.X := ⟨analyticAt_id, taylor_ring.2.2.1⟩
  have hsg := T_sgStar L
  have hL := T.mul taylor_ring (T.pow taylor_ring (T.rescale α hsg) 2)
    $ T.pow taylor_ring hX $ 2 * Fintype.card S
  have hR := T.mul taylor_ring
    (T.mul taylor_ring (T_const $ α ^ 2)
      $ T.pow taylor_ring hsg $ 2 * (Fintype.card S + 1))
    (T.prod Finset.univ (fun (P : S) (z : ℂ) => fP L P z)
      (fun (P : S) => Formalism.L2.Th1.C.wpShift (pSeries L) $ L.weierstrassP (P : ℂ))
      fun P _ => T_fP L P)
  have heq := T.unique hL hR (by
    filter_upwards [ev_notMem L, self_mem_nhdsWithin] with z hz hz0
    have hz0' := hz0
    beta_reduce
    have hsig := isogenySigma L α S hα hm hS z hz
    have hp : ∏ P : S, fP L (P : ℂ) z
        = ∏ P : S, (z ^ 2 * (L.weierstrassP z - L.weierstrassP (P : ℂ))) :=
      Finset.prod_congr rfl fun P _ => fP_eq L P hz0'
    rw [hp, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Finset.prod_coe_sort S fun P => L.weierstrassP z - L.weierstrassP P, hsig,
      Fintype.card_coe]
    ring)
  unfold Formalism.L2.Th1.C.IsogenyFormula
  exact heq

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.F

theorem hasCMByStable : HasCMByStable := has_cm_stable
theorem hasCMByScale : HasCMByScale := has_cm_scale

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.F

theorem taylorRing : TaylorRing := taylor_ring
theorem taylorDeriv : TaylorDeriv := taylor_deriv
theorem endoZInstance : EndoZInstance := integer_endomorphism_instance
theorem isogenyFormulaInstance : IsogenyFormulaInstance := isogeny_formula_instance

end Formalism.L2.Th1.F
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def VeluIntegralX : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (A g : PowerSeries K) (ι : Type) [Fintype ι]
    (xs : ι → PowerSeries K) (xP : ι → K) (al r : K),
    IsOneUnit R A → (∀ P, IntPS R $ xs P) → (∀ P, xP P ∈ R) → r ∈ R → al ∈ R → al ≠ 0 →
    (2 : K)⁻¹ ∈ R → PowerSeries.constantCoeff g = 1 →
    PowerSeries.C (al ^ 2) * PowerSeries.subst (PowerSeries.C al * PowerSeries.X * g) A
        * PowerSeries.X ^ 2 =
      (PowerSeries.C al * PowerSeries.X * g) ^ 2 * veluXs A xs xP r →
    IntPS R g

def IsEndoR {K : Type} [Field K] (R : Subring K) (e l : PowerSeries K) (c0 : K) {ι : Type}
    [Fintype ι] (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al albar : K) : Prop :=
  IsEndoZ e neg (fun P => xP P + c0) w al ∧ al * albar = (Fintype.card ι : K) + 1 ∧
  (∀ P, PowerSeries.subst l (w P) = xs P + PowerSeries.C c0) ∧ (∀ P, IntPS R $ xs P) ∧
  (∀ P, xP P ∈ R) ∧ al ∈ R ∧ al⁻¹ ∈ R ∧ (al ^ 2 - 1) * c0 ∈ R

def EndIntFromDatum : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (e l linv A : PowerSeries K) (c0 : K)
    (ι : Type) [Fintype ι] (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al albar : K),
    IsLogPair l linv → XIsWp e l A c0 → IsOneUnit R A → (2 : K)⁻¹ ∈ R →
    IsEndoR R e l c0 neg xP w xs al albar → EndInt R l linv al

def PhNormFromDatum : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (e : PowerSeries K) (s2 : K)
    (l linv ph A : PowerSeries K) (c0 : K)
    (ι : Type) [Fintype ι] (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al albar : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 → IsOneUnit R A → (2 : K)⁻¹ ∈ R →
    IsEndoR R e l c0 neg xP w xs al albar →
    al * (al - albar) * s2 = ∑ P, (xP P + c0) →
    PhNormAt R l linv ph al albar


def SimeqIffCong : Prop :=
  ∀ (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (f g : MvPowerSeries ι K),
    Formalism.InvariantFactorPaths.G7.Simeq f g ↔ Cong (Formalism.G.unitBall K) f g


def PhOIsPh : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e l : PowerSeries K) (s2 : K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    Formalism.L2.Th1.B.sgStar s2 e = sgStar e s2 ∧ IsPh e s2 l (Formalism.L2.Th1.B.phO s2 e l)

def FirstLevelFromUniversal : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F : MvPowerSeries (Fin 2) K)
    (l linv ph : PowerSeries K), IsLogPair l linv → Formalism.L2.Th1.B.LawLog F l →
    PowerSeries.constantCoeff ph = 0 →
    Formalism.InvariantFactorPaths.G7.Simeq (Formalism.InvariantFactorPaths.G7.d1 F $ Formalism.InvariantFactorPaths.G7.cob F ph) 0 →
    F = fadd l linv (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∧ FGInt (Formalism.G.unitBall K) l linv ∧
      F1 (Formalism.G.unitBall K) l linv ph


end Formalism.L2.Th1.C
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.C

open Formalism.L2.Th1.A

section Defs8

variable {K : Type} [Field K]

def CoeffIn (R : Subring K) (W : WeierstrassCurve K) : Prop :=
  W.a₁ ∈ R ∧ W.a₂ ∈ R ∧ W.a₃ ∈ R ∧ W.a₄ ∈ R ∧ W.a₆ ∈ R

def wTr (W : WeierstrassCurve K) (xP yP : K) : PowerSeries K :=
  PowerSeries.subst (expSer W) (xPlus W xP yP) + PowerSeries.C (W.b₂ / 12)

def IsEndoCurve (W : WeierstrassCurve K) {ι : Type} [Fintype ι] (neg : ι → ι) (xP yP : ι → K)
    (al : K) : Prop :=
  (∀ P, W.toAffine.Equation (xP P) $ yP P) ∧ (∀ P, neg (neg P) = P) ∧
  (∀ P, xP (neg P) = xP P ∧ yP (neg P) = W.toAffine.negY (xP P) (yP P)) ∧
  PowerSeries.C (al ^ 2) * PowerSeries.rescale al (wpReg W) =
    wpReg W + ∑ P, (wTr W (xP P) (yP P) - PowerSeries.C (xP P + W.b₂ / 12))

end Defs8

def CurveFrame : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (W : WeierstrassCurve K), CoeffIn R W →
    IsLogPair (logSer W) (expSer W) ∧ XIsWp (wpReg W) (logSer W) (xS W) (W.b₂ / 12) ∧
    IsOneUnit R (xS W) ∧ FGInt R (logSer W) (expSer W) ∧
    IsOneUnit R (PowerSeries.derivative $ logSer W)

def CurveSecondLogDerivative : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    HasSecondLogDeriv (wpShift (wpReg W) $ xP + W.b₂ / 12)
      (2 * wpReg W - wTr W xP yP - wTr W xP (W.toAffine.negY xP yP))

def CurveEndoZ : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP yP : ι → K) (al : K), IsEndoCurve W neg xP yP al →
    IsEndoZ (wpReg W) neg (fun P => xP P + W.b₂ / 12) (fun P => wTr W (xP P) $ yP P) al

def CurveEndoR : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (W : WeierstrassCurve K), CoeffIn R W →
    ∀ (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K) (al albar : K),
    IsEndoCurve W neg xP yP al → (∀ P, xP P ∈ R) → (∀ P, yP P ∈ R) →
    al * albar = (Fintype.card ι : K) + 1 → al ∈ R → al⁻¹ ∈ R → (al ^ 2 - 1) * (W.b₂ / 12) ∈ R →
    IsEndoR R (wpReg W) (logSer W) (W.b₂ / 12) neg xP (fun P => wTr W (xP P) $ yP P)
      (fun P => xPlus W (xP P) $ yP P) al albar

end Formalism.L2.Th1.C
end
section
namespace Formalism.L2.Th1.C

namespace Dict

section Alg

variable {K : Type} [Field K] {σ τ : Type} {l linv : PowerSeries K}

theorem substMv_fadd [Finite σ] (h : IsLogPair l linv) {u v : MvPowerSeries σ K}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    {a : σ → MvPowerSeries τ K} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (fadd l linv u v) =
      fadd l linv (MvPowerSeries.subst a u) (MvPowerSeries.subst a v) := by
  have hsa := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have psub : ∀ (b : MvPowerSeries σ K), MvPowerSeries.constantCoeff b = 0 → ∀ f : PowerSeries K,
      MvPowerSeries.subst a (PowerSeries.subst b f) = PowerSeries.subst (MvPowerSeries.subst a b) f := by
    intro b hb f
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (a := fun _ : Unit => b)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hb) hsa]
  unfold fadd
  rw [psub _ $ by rw [map_add, PowerSeries.constantCoeff_subst_eq_zero hu l h.1, PowerSeries.constantCoeff_subst_eq_zero hv l h.1, add_zero], ← MvPowerSeries.coe_substAlgHom hsa, map_add,
    MvPowerSeries.coe_substAlgHom hsa, psub u hu, psub v hv]

theorem subst_biextension_form [Finite σ] (h : IsLogPair l linv) (ph : PowerSeries K) {u v : MvPowerSeries σ K}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    {a : σ → MvPowerSeries τ K} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (be0 l linv ph u v) =
      be0 l linv ph (MvPowerSeries.subst a u) (MvPowerSeries.subst a v) := by
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have psub : ∀ (b : MvPowerSeries σ K), MvPowerSeries.constantCoeff b = 0 → ∀ f : PowerSeries K,
      MvPowerSeries.subst a (PowerSeries.subst b f) = PowerSeries.subst (MvPowerSeries.subst a b) f := by
    intro b hb f
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (a := fun _ : Unit => b)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hb) hsa]
  have hf : MvPowerSeries.constantCoeff (fadd l linv u v) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, PowerSeries.constantCoeff_subst_eq_zero hu l h.1, PowerSeries.constantCoeff_subst_eq_zero hv l h.1, add_zero]) linv h.2.2.1
  unfold be0
  rw [← MvPowerSeries.coe_substAlgHom hsa, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hsa,
    psub _ hf, psub u hu, psub v hv, substMv_fadd h hu hv ha]

theorem constantCoeff_vec_three_eq_zero {x y z : MvPowerSeries τ K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (hz : MvPowerSeries.constantCoeff z = 0) :
    ∀ s, MvPowerSeries.constantCoeff (![x, y, z] s) = 0 := by
  intro s
  fin_cases s
  simpa using hx
  simpa using hy
  simpa using hz

theorem cob_eq (ph : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) $ MvPowerSeries.X (1 : Fin 2)) ph =
      be0 l linv ph (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)) := rfl

theorem subst_cob (h : IsLogPair l linv) (ph : PowerSeries K) {x y : MvPowerSeries τ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst ![x, y]
      (Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) $ MvPowerSeries.X (1 : Fin 2)) ph) =
      be0 l linv ph x y := by
  rw [cob_eq, subst_biextension_form h ph (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1)
      (by
          intro s
          fin_cases s
          simpa using hx
          simpa using hy),
    MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero $ by
        intro s
        fin_cases s
        simpa using hx
        simpa using hy,
    MvPowerSeries.subst_X $ MvPowerSeries.hasSubst_of_constantCoeff_zero $ by
        intro s
        fin_cases s
        simpa using hx
        simpa using hy]
  rfl

theorem coboundary_formal_add_biextension (h : IsLogPair l linv) (ph : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.d1 (fadd l linv (MvPowerSeries.X (0 : Fin 2)) $ MvPowerSeries.X (1 : Fin 2))
      (Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) $ MvPowerSeries.X (1 : Fin 2)) ph) =
      be0 l linv ph (fadd l linv (MvPowerSeries.X (0 : Fin 3)) $ MvPowerSeries.X (1 : Fin 3))
          (MvPowerSeries.X (2 : Fin 3)) -
        be0 l linv ph (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (2 : Fin 3)) -
        be0 l linv ph (MvPowerSeries.X (1 : Fin 3)) (MvPowerSeries.X (2 : Fin 3)) := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have h2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 2
  have e : Formalism.InvariantFactorPaths.G7.in3
      (fadd l linv (MvPowerSeries.X (0 : Fin 2)) $ MvPowerSeries.X (1 : Fin 2)) =
      fadd l linv (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (1 : Fin 3)) :=
    (Pts.fadd_eq_substMv h h0 h1).symm
  rw [Formalism.InvariantFactorPaths.G7.d1, e, subst_cob h ph (Pts.constantCoeff_fadd h h0 h1) h2, subst_cob h ph h0 h2,
    subst_cob h ph h1 h2]

theorem law_eq (h : IsLogPair l linv) {F : MvPowerSeries (Fin 2) K}
    (hF : MvPowerSeries.constantCoeff F = 0) (hc : Formalism.InvariantFactorPaths.G7.cob F l = 0) :
    F = fadd l linv (MvPowerSeries.X 0) (MvPowerSeries.X 1) := by
  have e : PowerSeries.subst F l = PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l +
      PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l := by
    have := hc
    rw [Formalism.InvariantFactorPaths.G7.cob, Formalism.InvariantFactorPaths.G7.at1, Formalism.InvariantFactorPaths.G7.at1] at this
    linear_combination this
  rw [fadd, ← e, Pts.subst_linv_l h hF]

end Alg

section Sigma

variable {K : Type} [Field K] [CharZero K]

theorem prim_prim (e : PowerSeries K) : Formalism.L2.Th1.B.prim (Formalism.L2.Th1.B.prim e) = dblInt e := by
  ext n
  match n with
  | 0 => rw [Formalism.L2.Th1.B.Ph.coeff_zero_prim, dblInt, PowerSeries.coeff_mk, if_pos $ by norm_num]
  | 1 =>
    rw [Formalism.L2.Th1.B.Ph.coeff_prim_succ, Formalism.L2.Th1.B.Ph.coeff_zero_prim, zero_div, dblInt,
      PowerSeries.coeff_mk, if_pos $ by norm_num]
  | m + 2 =>
    rw [Formalism.L2.Th1.B.Ph.coeff_prim_succ, Formalism.L2.Th1.B.Ph.coeff_prim_succ, dblInt,
      PowerSeries.coeff_mk, if_neg $ by omega, Nat.add_sub_cancel, div_div]
    congr 1
    push_cast
    ring

theorem sgStar_eq (e : PowerSeries K) (s2 : K) : Formalism.L2.Th1.B.sgStar s2 e = sgStar e s2 := by
  have h1 : MvPowerSeries.constantCoeff (-(dblInt e) : PowerSeries K) = 0 := by
    rw [← prim_prim]
    exact Formalism.L2.Th1.B.Ph.constantCoeff_sigS e
  have h2 : MvPowerSeries.constantCoeff
      (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) : PowerSeries K) = 0 := by
    show PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) = 0
    simp
  have e1 : -(lam e s2) = -(dblInt e) + -(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) := by
    rw [lam]
    ring
  rw [sgStar, e1, mvExp_add h1 h2, Formalism.L2.Th1.B.sgStar, Formalism.L2.Th1.B.sigma, Formalism.L2.Th1.B.sigS,
    prim_prim, mul_assoc]
  rfl

end Sigma

end Dict

theorem simeq_iff_congruence : SimeqIffCong := fun _ _ _ _ _ _ _ => Iff.rfl


theorem odd_phi_is_phi : PhOIsPh := by
  intro K _ _ e l s2 hl hl1
  obtain ⟨h0, h1⟩ := Formalism.L2.Th1.B.Ph.logSigmaPullbackSpec K s2 e l hl hl1
  use Dict.sgStar_eq e s2, h0
  rw [← Dict.sgStar_eq, h1]
  rfl

theorem first_level_from_universal_holds : FirstLevelFromUniversal := by
  intro K _ _ _ F l linv ph h hL hph hS
  obtain ⟨hF0, hFi, -, -, hc⟩ := hL
  have hF := Dict.law_eq h hF0 hc
  refine ⟨hF, by
      rw [FGInt, ← hF]
      exact hFi, ?_⟩
  intro σ x x' y hx hx' hy
  have ha := Dict.constantCoeff_vec_three_eq_zero hx.1 hx'.1 hy.1
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have key := lGSubstMv K (Formalism.G.unitBall K) (Fin 3) _ (by
      have := (simeq_iff_congruence K (Fin 3) _ _).1 hS
      rwa [Cong, sub_zero] at this) σ ![x, x', y] $ by
      intro s
      fin_cases s
      exact hx
      exact hx'
      exact hy
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have h2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 2
  rw [hF, Dict.coboundary_formal_add_biextension h ph, MvPowerSeries.subst_sub hs, MvPowerSeries.subst_sub hs,
    Dict.subst_biextension_form h ph (Pts.constantCoeff_fadd h h0 h1) h2 ha, Dict.subst_biextension_form h ph h0 h2 ha,
    Dict.subst_biextension_form h ph h1 h2 ha, Dict.substMv_fadd h h0 h1 ha, MvPowerSeries.subst_X hs,
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs] at key
  rwa [Cong, ← sub_sub]


end Formalism.L2.Th1.C
end
section
open scoped BigOperators
open PowerSeries

namespace Formalism.L2.Th1.C

namespace CompactOperatorsAlt

section Below

variable {K : Type} [Field K] {R : Subring K}

theorem below_mul {n : ℕ} {f h : PowerSeries K} (hf : ∀ m < n, coeff m f ∈ R)
    (hh : ∀ m < n, coeff m h ∈ R) : ∀ m < n, coeff m (f * h) ∈ R := by
  intro m hm
  rw [PowerSeries.coeff_mul]
  refine Subring.sum_mem _ fun p hp => ?_
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact R.mul_mem (hf _ $ by omega) $ hh _ $ by omega

theorem below_subst {n : ℕ} {A a : PowerSeries K} (hA : IntPS R A)
    (ha0 : constantCoeff a = 0) (ha : ∀ m < n, coeff m a ∈ R) :
    ∀ m < n, coeff m (A.subst a) ∈ R := by
  intro m hm
  rw [PowerSeries.coeff_subst' $ HasSubst.of_constantCoeff_zero' ha0]
  refine finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun k => ?_
  rw [smul_eq_mul]
  exact R.mul_mem (hA k) $ Pts.coeff_pow_mem ha k m hm

theorem below_shift {n : ℕ} {g : PowerSeries K} {al : K} (hal : al ∈ R)
    (hg : ∀ m < n, coeff m g ∈ R) : ∀ m < n + 1, coeff m (C al * X * g) ∈ R := by
  intro m hm
  have h : C al * X * g = X * (C al * g) := by ring
  rw [h]
  cases m with
  | zero => rw [coeff_zero_X_mul]; exact R.zero_mem
  | succ m => rw [coeff_succ_X_mul, coeff_C_mul]; exact R.mul_mem hal $ hg m $ by omega

theorem coeff_of_sq {n : ℕ} {g : PowerSeries K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hg0 : constantCoeff g = 1) (hg : ∀ m < n, coeff m g ∈ R) (hgg : coeff n (g * g) ∈ R) :
    coeff n g ∈ R := by
  have h1 : IntPS R (1 : PowerSeries K) := by simpa using USideA.intPS_X_pow (R := R) (K := K) 0
  have hh0 : coeff 0 (g - 1) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, hg0, map_one, sub_self]
  have hh : ∀ m < n, coeff m (g - 1) ∈ R := fun m hm => by
    rw [map_sub]
    exact R.sub_mem (hg m hm) $ h1 m
  have hid : coeff n (g - 1) = (2 : K)⁻¹ * (coeff n (g * g) - coeff n (1 : PowerSeries K)
      - coeff n ((g - 1) * (g - 1))) := by
    have : g * g - 1 - (g - 1) * (g - 1) = (g - 1) + (g - 1) := by ring
    rw [← map_sub, ← map_sub, this, map_add]
    field_simp
    ring
  have : g = (g - 1) + 1 := by ring
  rw [this, map_add]
  exact R.add_mem (by
      rw [hid, PowerSeries.coeff_mul n $ g - 1]
      refine R.mul_mem h2 $ R.sub_mem (R.sub_mem hgg $ h1 n) $ Subring.sum_mem _ fun p hp => ?_
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases hp1 : p.1 = 0
      rw [hp1, hh0, zero_mul]
      exact R.zero_mem
      by_cases hp2 : p.2 = 0
      rw [hp2, hh0, mul_zero]
      exact R.zero_mem
      exact R.mul_mem (hh _ $ by omega) $ hh _ $ by omega) $ h1 n

theorem int_of_eq {A V g : PowerSeries K} {al : K} (h2 : (2 : K)⁻¹ ∈ R) (h20 : (2 : K) ≠ 0)
    (hA : IntPS R A) (hV : IsOneUnit R V) (hal : al ∈ R) (hg0 : constantCoeff g = 1)
    (hEq : A.subst (C al * X * g) = g * g * V) : IntPS R g := by
  have hinv := PowerSeries.mul_inv_cancel V (by rw [hV.1]; exact one_ne_zero)
  have hgg : g * g = A.subst (C al * X * g) * V⁻¹ := by
    rw [hEq, mul_assoc, hinv, mul_one]
  have key : ∀ n, ∀ m < n, coeff m g ∈ R := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
      exact ih m h
      subst h
      refine coeff_of_sq h2 h20 hg0 ih ?_
      rw [hgg]
      exact below_mul (below_subst hA (by simp) $ below_shift hal ih) (fun k _ => (USideA.intPS_of_mul_eq_one hV.2 hV.1 hinv) k) m
        $ Nat.lt_succ_self m
  exact fun n => key (n + 1) n $ Nat.lt_succ_self n

theorem isOneUnit_veluXs {A : PowerSeries K} {ι : Type} [Fintype ι] {xs : ι → PowerSeries K}
    {xP : ι → K} {r : K} (hA : IsOneUnit R A) (hxs : ∀ P, IntPS R $ xs P) (hxP : ∀ P, xP P ∈ R)
    (hr : r ∈ R) : IsOneUnit R $ veluXs A xs xP r := by
  refine ⟨by simp [veluXs, hA.1], ?_⟩
  exact USideA.intPS_add hA.2 $ USideA.intPS_mul (USideA.intPS_X_pow 2)
    $ USideA.intPS_sub (USideA.intPS_sum _ fun P _ =>
      USideA.intPS_sub (hxs P) $ USideA.intPS_C $ hxP P) $ USideA.intPS_C hr

theorem exists_mulBy_eq {l linv : PowerSeries K} (h : IsLogPair l linv) {al : K} (hal : al ≠ 0) :
    ∃ g, constantCoeff g = 1 ∧ mulBy l linv al = C al * X * g := by
  have ha0 : constantCoeff (C al * l) = 0 := by rw [map_mul, h.1, mul_zero]
  have hv0 : coeff 0 (mulBy l linv al) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact Pts.constantCoeff_mulBy h al
  have hv1 : coeff 1 (mulBy l linv al) = al := by
    have hc := IntegralMvPolynomialLemmas.coeff_subst_congr (g := linv) (h := (X : PowerSeries K)) (a := C al * l) ha0
      (Finsupp.single () 1) fun k hk => by
        rw [Finsupp.degree_single] at hk
        interval_cases k
        simp [h.2.2.1]
        rw [Pts.coeff_one_linv h, coeff_one_X]
    rw [PowerSeries.subst_X $ Pts.hasSubst ha0] at hc
    have h1 : coeff 1 (mulBy l linv al) = coeff 1 (C al * l) := hc
    rw [h1, coeff_C_mul, h.2.1, mul_one]
  refine ⟨PowerSeries.mk fun n => al⁻¹ * coeff (n + 1) (mulBy l linv al), ?_, ?_⟩
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add, hv1, inv_mul_cancel₀ hal]
  have hr : ∀ g, C al * X * g = X * (C al * g) := fun g => by ring
  rw [hr]
  ext n
  cases n with
  | zero => rw [coeff_zero_X_mul, hv0]
  | succ n => rw [coeff_succ_X_mul, coeff_C_mul, coeff_mk, mul_inv_cancel_left₀ hal]

end Below

theorem ne_zero_of_isEndoR {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {al albar : K}
    (hN : al * albar = (Fintype.card ι : K) + 1) : al ≠ 0 := by
  intro h
  rw [h, zero_mul] at hN
  exact (Nat.cast_add_one_ne_zero (R := K) $ Fintype.card ι) hN.symm

end CompactOperatorsAlt

open CompactOperatorsAlt

theorem velu_x_coordinate_integral : VeluIntegralX := by
  intro K _ _ R A g ι _ xs xP al r hA hxs hxP hr hal hal0 h2 hg0 hEq
  refine int_of_eq h2 two_ne_zero hA.2 (isOneUnit_veluXs hA hxs hxP hr) hal hg0 ?_
  have hC : (C (al ^ 2) : PowerSeries K) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    rw [constantCoeff_C, map_zero] at this
    exact pow_ne_zero 2 hal0 this
  exact sub_eq_zero.mp $ (mul_eq_zero.mp (by
      have : C (al ^ 2) * X ^ 2 * (A.subst (C al * X * g) - g * g * veluXs A xs xP r) =
          C (al ^ 2) * A.subst (C al * X * g) * X ^ 2 -
            (C al * X * g) ^ 2 * veluXs A xs xP r := by
        rw [map_pow]
        ring
      rw [this, hEq, sub_self])).resolve_left $ mul_ne_zero hC $ pow_ne_zero 2 X_ne_zero

theorem integral_endomorphism_from_datum : EndIntFromDatum := by
  intro K _ _ R e l linv A c0 ι _ neg xP w xs al albar hL hX hA h2 hD
  obtain ⟨hZ, hN, hw, hxs, hxP, hal, -, hr⟩ := hD
  have hal0 := ne_zero_of_isEndoR hN
  obtain ⟨g, hg0, hvg⟩ := exists_mulBy_eq hL hal0
  have hV := veluXFromZ K e l linv A c0 ι neg xP w xs al hL hX hZ hw
  rw [hvg] at hV
  show IntPS R $ mulBy l linv al
  rw [hvg]
  exact USideA.intPS_mul (USideA.intPS_mul (USideA.intPS_C hal) USideA.intPS_X) $ velu_x_coordinate_integral K R A g ι xs xP al _ hA hxs hxP hr hal hal0 h2 hg0 hV

theorem phi_norm_from_datum : PhNormFromDatum := by
  intro K _ _ R e s2 l linv ph A c0 ι _ neg xP w xs al albar hL hPh hX hA h2 hD hs
  have hE :=
    integral_endomorphism_from_datum K R e l linv A c0 ι neg xP w xs al albar hL hX hA h2 hD
  obtain ⟨hZ, hN, -, -, hxP, hal, hali, -⟩ := hD
  have hal0 := ne_zero_of_isEndoR hN
  have hI :=
    (isogenyIffBar K e s2 ι neg xP c0 w al albar hal0 hN hZ).mpr hs
  have := phNormUnit K R e s2 l linv ph A c0 ι xP al hL hPh hX hI hA hxP hal hali hal0 h2 hE
  show Cong R (PowerSeries.subst (mulBy l linv al) ph) $ (al * albar) • ph
  rwa [hN]


end Formalism.L2.Th1.C
end
section
open Formalism.L2.Th1.B (CurveHyp IsHalf IsInv IsWp LawLog)
open PowerSeries


namespace Formalism.L2.Th1.A

def IntModel {K : Type} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1

def BridgeWp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    IsWp (g₂ W) (g₃ W) $ wpReg W

def BridgeLaw : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    LawLog (fgl W) (logSer W) ∧ IsInv (logSer W) (iSer W) ∧
    (‖(2 : K)‖ = 1 → IsHalf (logSer W) (halfSer W))

def BridgeCurve : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    CurveHyp (fgl W) (iSer W) (logSer W) (wpReg W) (xS W) (W.b₂ / 12)


end Formalism.L2.Th1.A
end
section
open PowerSeries



namespace Formalism.L2.Th1.A






def FlowUniqueZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (x y x' y' : K⟦X⟧),
    IsFlow (curveS W) (derivative (R := K)) x y → IsFlow (curveS W) (derivative (R := K)) x' y' →
    constantCoeff x = constantCoeff x' → constantCoeff y = constantCoeff y' → x = x' ∧ y = y'



end Formalism.L2.Th1.A
end
section
open scoped BigOperators
open Formalism.L2.Th1.B (phO)

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A
open Formalism.G (unitBall)






def CurveNegNorm : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (W : WeierstrassCurve K), CoeffIn R W →
    (2 : K)⁻¹ ∈ R → ∀ s2 : K,
    PhNormAt R (logSer W) (expSer W) (phO s2 (wpReg W) $ logSer W) (-1) $ -1

def WeierstrassBiadditiveModEquiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 → ∀ s2 : K,
    F1 (unitBall K) (logSer W) (expSer W) $ phO s2 (wpReg W) $ logSer W


end Formalism.L2.Th1.G
end
section
open PowerSeries


namespace Formalism.L2.Th1.A

namespace Bridge

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_of_coeff {f : K⟦X⟧} (h : ∀ n, coeff n f ∈ Formalism.G.unitBall K) :
    Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) f := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  have e : n = Finsupp.single () (n ()) := by
    ext
    simp
  rw [e]
  exact h $ n ()

theorem integral_of_mvCoeff {ι : Type} {f : MvPowerSeries ι K}
    (h : ∀ n, MvPowerSeries.coeff n f ∈ Formalism.G.unitBall K) : Formalism.DworkPowerSeriesWeights.Integral f := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  exact h

theorem integral_map {ι : Type} (c : MvPowerSeries ι (Formalism.G.unitBall K)) :
    Formalism.DworkPowerSeriesWeights.Integral $ MvPowerSeries.map (Formalism.G.unitBall K).subtype c := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff n c).2

def model (W : WeierstrassCurve K) (h : IntModel W) : WeierstrassCurve $ Formalism.G.unitBall K :=
  ⟨⟨W.a₁, h.1⟩, ⟨W.a₂, h.2.1⟩, ⟨W.a₃, h.2.2.1⟩, ⟨W.a₄, h.2.2.2.1⟩, ⟨W.a₆, h.2.2.2.2⟩⟩

theorem model_map (W : WeierstrassCurve K) (h : IntModel W) :
    (model W h).map (Formalism.G.unitBall K).subtype = W := by
  rfl

end Ball

end Bridge

open Bridge

theorem bridgeWp_of (h : WpCleared.{0}) : BridgeWp := by
  unfold BridgeWp
  intro K _ _ W
  exact h K W

theorem bridgeLaw_of (hM : CoeffMem.{0}) (hFL : FglLog.{0}) (hHS : HalfSpec.{0})
    (hHL : HalfLog.{0, 0}) : BridgeLaw := by
  intro K _ _ _ W hW
  obtain ⟨-, -, -, -, -, hi, hF, -, hh, -, -⟩ :=
    hM K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  obtain ⟨hl0, hl1, -, -⟩ := logSpec K W
  refine ⟨⟨(fglChord K W).2.2.2.2.1, integral_of_mvCoeff hF, hl0, hl1, ?_⟩,
    ⟨(iSerSpec K W).1, integral_of_coeff hi, (logNeg K W).1⟩, fun h2 => ?_⟩
  unfold Formalism.InvariantFactorPaths.G7.cob Formalism.InvariantFactorPaths.G7.at1
  rw [(hFL K W).1]
  ring
  have hu : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
  refine ⟨(hHS K W hu).1, integral_of_coeff $ hh ⟨2⁻¹, ?_, mul_inv_cancel₀ two_ne_zero⟩, ?_⟩
  change ‖(2 : K)⁻¹‖ ≤ 1
  rw [norm_inv, h2, inv_one]
  have key := hHL.1 K W
  have h21 : (C (2 : K)⁻¹ : K⟦X⟧) * 2 = 1 := by
    rw [← map_ofNat (C : K →+* K⟦X⟧) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  calc (logSer W).subst (halfSer W)
      = (C (2 : K)⁻¹ * 2) * (logSer W).subst (halfSer W) := by rw [h21, one_mul]
    _ = C (2 : K)⁻¹ * (2 * (logSer W).subst (halfSer W)) := by ring
    _ = C (2 : K)⁻¹ * logSer W := by rw [key]

theorem bridgeCurve_of (hM : CoeffMem.{0}) (hU : WpInU.{0}) (hC : CubeTwoR.{0}) :
    BridgeCurve := by
  intro K _ _ _ W hW
  obtain ⟨-, hx, -⟩ :=
    hM K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  use integral_of_coeff hx, CurveSer.xS_cc W, hU K W
  obtain ⟨c, hc0, hc⟩ := hC (Formalism.G.unitBall K) $ model W hW
  refine ⟨MvPowerSeries.map (Formalism.G.unitBall K).subtype c, integral_map c, ?_, ?_⟩
  rw [MvPowerSeries.constantCoeff_map, hc0]
  simp
  have hi0 : constantCoeff (iSer $ model W hW) = 0 := (iSerSpec _ $ model W hW).1
  have hs : MvPowerSeries.HasSubst
      (![U₁, (iSer $ model W hW).subst
          (U₂ : MvPowerSeries (Fin 2) $ Formalism.G.unitBall K)] :
        Fin 2 → MvPowerSeries (Fin 2) (Formalism.G.unitBall K)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i
    simp
    simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 1) _ hi0
  have key := congrArg (MvPowerSeries.map (Formalism.G.unitBall K).subtype) hc
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, MvPowerSeries.map_X,
    MvPowerSeries.map_X, PowerSeries.map_subst $ HasSubst.X 0,
    PowerSeries.map_subst $ HasSubst.X 1, MvPowerSeries.map_X, MvPowerSeries.map_X,
    CurveSer.map_xS, MvPowerSeries.map_subst hs, fglMap, model_map] at key
  unfold Formalism.L2.Th1.B.FI Formalism.InvariantFactorPaths.G7.at1
  rw [key]
  congr 2
  funext i
  fin_cases i
  simp
  simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [PowerSeries.map_subst $ HasSubst.X 1, MvPowerSeries.map_X, CurveSer.map_iSer, model_map]


end Formalism.L2.Th1.A
end
section
namespace Formalism.L2.Th1.A

theorem plusZ : PlusZ.{u} := addition_integral
theorem wpInU : WpInU.{u} := wpInU_of wpShape
theorem tInZ : TInZ.{u} := tInZ_of wpShape

theorem bridgeWp : BridgeWp := bridgeWp_of wpCleared
theorem bridgeLaw : BridgeLaw := bridgeLaw_of coeffMem fglLog halfSpec halfLog
theorem bridgeCurve : BridgeCurve := bridgeCurve_of coeffMem wpInU cubeTwoR

end Formalism.L2.Th1.A
end
section
namespace Formalism.L2.Th1.A

theorem zMap : ZMap.{u, v} := z_series_map_spec

theorem plusZCleared : PlusZCleared.{u} := plusZCleared_of plusZ tInZ

end Formalism.L2.Th1.A
end
section
open Formalism.L2.Th1.A (BridgeWp bridgeWp)
namespace Formalism.L2.Th1.F

theorem curveBridge_of (hw : BridgeWp) (hu : IsWpUnique) (ht : TaylorIsWp) : CurveBridge := by
  intro W L h2 h3
  have h := hw ℂ W
  rw [h2, h3] at h
  exact hu ℂ L.g₂ L.g₃ _ _ h $ ht L

theorem curve_weierstrass_series_eq : CurveBridge :=
  curveBridge_of bridgeWp weierstrass_series_unique $ taylorIsWp_of taylor_ring taylor_deriv

end Formalism.L2.Th1.F
end
section
namespace Formalism.L2.Th1.F

theorem curveBridge : CurveBridge := curve_weierstrass_series_eq

end Formalism.L2.Th1.F
end
section
open PowerSeries



namespace Formalism.L2.Th1.A

namespace Q2

section Parity

variable {R : Type u} [CommRing R]



variable {K : Type u} [Field K] [CharZero K]


end Parity

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]









end Ball

end Q2

open Q2


theorem flow_unique_integral : FlowUniqueZ.{u} := by
  intro K _ _ W x y x' y' hF hF' hx0 hy0
  obtain ⟨-, hx, hy⟩ := hF
  obtain ⟨-, hx', hy'⟩ := hF'
  have hR : ∀ (n : ℕ) (r : K), n ≠ 0 → (n : K) * r = 0 → r = 0 := fun n r hn h =>
    (mul_eq_zero.1 h).resolve_left $ Nat.cast_ne_zero.2 hn
  simp [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄] at hx hy hx' hy'
  have dx : derivative (x - x') = 2 * (y - y') + C W.a₁ * (x - x') := by
    rw [map_sub, hx, hx']
    ring
  have dy : derivative (y - y')
      = (x - x') * (3 * (x + x') + 2 * C W.a₂) - C W.a₁ * (y - y') := by
    rw [map_sub, hy, hy']
    ring
  have cy : constantCoeff (y - y') = 0 := by rw [map_sub, hy0, sub_self]
  have key : ∀ n, X ^ n ∣ x - x' ∧ X ^ n ∣ y - y' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨ix, iy⟩ := ih
      refine ⟨Nn.X_pow_succ_dvd_of_derivative hR (by rw [map_sub, hx0, sub_self]) ?_, Nn.X_pow_succ_dvd_of_derivative hR cy ?_⟩
      rw [dx]
      exact dvd_add (Dvd.dvd.mul_left iy _) $ Dvd.dvd.mul_left ix _
      rw [dy]
      exact dvd_sub (Dvd.dvd.mul_right ix _) $ Dvd.dvd.mul_left iy _
  constructor
  exact sub_eq_zero.1 $ Nn.eq_zero_of_forall_X_pow_dvd fun n => (key n).1
  exact sub_eq_zero.1 $ Nn.eq_zero_of_forall_X_pow_dvd fun n => (key n).2
end Formalism.L2.Th1.A
end
section
namespace Formalism.L2.Th1.A

theorem flowUniqueZ : FlowUniqueZ.{u} := flow_unique_integral

end Formalism.L2.Th1.A
end
section
open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)





theorem coeff_single_variable_series {K ι : Type} [Field K] [DecidableEq ι] (x : ι) (f : PowerSeries K)
    (n : ι →₀ ℕ) : MvPowerSeries.coeff n (at1 x f) =
      if n = Finsupp.single x (n x) then PowerSeries.coeff (n x) f else 0 := by
  unfold at1
  rw [PowerSeries.coeff_subst $ PowerSeries.HasSubst.of_constantCoeff_zero $ by simp]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul]
  rw [finsum_eq_single _ $ n x]
  simp
  intro d hd
  rw [if_neg, mul_zero]
  intro h
  apply hd
  rw [h]
  simp


theorem coeff_mvExp {K ι : Type} [NormedField K] [CharZero K] {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (mvExp f) =
      ∑ k ∈ range (n.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ k) := by
  classical
  unfold mvExp
  rw [PowerSeries.coeff_subst $ PowerSeries.HasSubst.of_constantCoeff_zero hf, finsum_eq_sum_of_support_subset (s := range $ n.degree + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PowerSeries.coeff_exp, smul_eq_mul]
  simp
  intro k hk
  simp only [Function.mem_support] at hk
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hk
  rw [MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simpa using hf)
    $ by omega, smul_zero]












def AA (K : Type) [Field K] (p : ℕ) (x y : Fin 2) : MvPowerSeries (Fin 2) K :=
  fun n => ∑ i ∈ range (n x + 1), ∑ j ∈ range (n y + 1),
    if i ≤ j ∧ n x = (p ^ 2) ^ i ∧ n y = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0
















end Formalism.InvariantFactorPaths.G7
end
section
namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (at1 coeff_single_variable_series)
open MvPowerSeries (coeff constantCoeff)

section

variable {K : Type} [Field K] [CharZero K]

theorem hasSubst_eval_second_zero : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries K), 0] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s
    first
      | exact PowerSeries.constantCoeff_X
      | exact MvPowerSeries.constantCoeff_X ()
      | (simp [PowerSeries.X]; done)
      | rfl
    simp

theorem eval_second_zero_eq_algHom (h : MvPowerSeries (Fin 2) K) :
    ev0 h = MvPowerSeries.substAlgHom (hasSubst_eval_second_zero (K := K)) h := by
  rw [MvPowerSeries.coe_substAlgHom]
  rfl

theorem evalYZero_add (g h : MvPowerSeries (Fin 2) K) : ev0 (g + h) = ev0 g + ev0 h := by
  rw [eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_add]

theorem eval_second_zero_sub (g h : MvPowerSeries (Fin 2) K) : ev0 (g - h) = ev0 g - ev0 h := by
  rw [eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_sub]


theorem evalYZero_mul (g h : MvPowerSeries (Fin 2) K) : ev0 (g * h) = ev0 g * ev0 h := by
  rw [eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_mul]

theorem eval_second_zero_X_zero : ev0 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = PowerSeries.X := by
  unfold ev0
  rw [MvPowerSeries.subst_X hasSubst_eval_second_zero]
  rfl

theorem eval_second_zero_X_one : ev0 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
  unfold ev0
  rw [MvPowerSeries.subst_X hasSubst_eval_second_zero]
  rfl

theorem evalYZero_subst (f : PowerSeries K) {u : MvPowerSeries (Fin 2) K} (hu : constantCoeff u = 0) :
    ev0 (PowerSeries.subst u f) = PowerSeries.subst (ev0 u) f := by
  unfold ev0 PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hu).const hasSubst_eval_second_zero]

theorem psubst_X (f : PowerSeries K) : PowerSeries.subst (PowerSeries.X : PowerSeries K) f = f := by
  unfold PowerSeries.subst
  have : (fun _ => (PowerSeries.X : PowerSeries K)) = MvPowerSeries.X := by
    funext u
    cases u
    rfl
  rw [this, MvPowerSeries.subst_self]
  rfl

theorem eval_second_zero_at_sum (f : PowerSeries K) : ev0 (atS f) = f := by
  unfold atS
  rw [evalYZero_subst _ $ by simp, evalYZero_add, eval_second_zero_X_zero, eval_second_zero_X_one, add_zero, psubst_X]

theorem eval_second_zero_at_difference (f : PowerSeries K) : ev0 (atD f) = f := by
  unfold atD
  rw [evalYZero_subst _ $ by simp, eval_second_zero_sub, eval_second_zero_X_zero, eval_second_zero_X_one, sub_zero, psubst_X]

theorem eval_second_zero_at_variable_zero (f : PowerSeries K) : ev0 (at1 0 f) = f := by
  unfold at1
  rw [evalYZero_subst _ $ by simp, eval_second_zero_X_zero, psubst_X]

private theorem coeff_ev0_eq_coeff_single_zero (h : MvPowerSeries (Fin 2) K) (k : ℕ) :
    PowerSeries.coeff k (ev0 h) = coeff (Finsupp.single 0 k) h := by
  have hc : ∀ m, MvPowerSeries.coeff (Finsupp.single () k) ((PowerSeries.X : PowerSeries K) ^ m) =
      if k = m then 1 else 0 := fun m => PowerSeries.coeff_X_pow k m
  show MvPowerSeries.coeff (Finsupp.single () k) (ev0 h) = _
  unfold ev0
  rw [MvPowerSeries.coeff_subst hasSubst_eval_second_zero, finsum_eq_single _ $ Finsupp.single 0 k]
  rw [Finsupp.prod_single_index $ by simp]
  simp only [Matrix.cons_val_zero, hc, if_true, smul_eq_mul, mul_one]
  intro d hd
  rw [Finsupp.prod_fintype _ _ $ by simp, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h1 : d 1 = 0
  have hd0 : k ≠ d 0 := by
    intro hk
    apply hd
    ext a
    fin_cases a <;> simp [h1, hk]
  rw [h1, pow_zero, mul_one, hc, if_neg hd0, smul_zero]
  rw [zero_pow h1, mul_zero, map_zero, smul_zero]

theorem restrictSecondZero_inVar_one (f : PowerSeries K) :
    ev0 (at1 1 f) = PowerSeries.C (PowerSeries.constantCoeff f) := by
  ext k
  rw [coeff_ev0_eq_coeff_single_zero, coeff_single_variable_series, PowerSeries.coeff_C]
  by_cases hk : k = 0
  subst hk
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [if_neg hk, if_neg]
  intro h
  have := congrArg (fun n => n 0) h
  simp at this
  exact hk this

theorem coeff_evalYZero (h : MvPowerSeries (Fin 2) K) (k : ℕ) :
    PowerSeries.coeff k (ev0 h) = coeff (Finsupp.single 0 k) h := by
  have hc : ∀ m, MvPowerSeries.coeff (Finsupp.single () k) ((PowerSeries.X : PowerSeries K) ^ m) =
      if k = m then 1 else 0 := fun m => PowerSeries.coeff_X_pow k m
  show MvPowerSeries.coeff (Finsupp.single () k) (ev0 h) = _
  unfold ev0
  rw [MvPowerSeries.coeff_subst hasSubst_eval_second_zero, finsum_eq_single _ $ Finsupp.single 0 k]
  rw [Finsupp.prod_single_index $ by simp]
  simp only [Matrix.cons_val_zero, hc, if_true, smul_eq_mul, mul_one]
  intro d hd
  rw [Finsupp.prod_fintype _ _ $ by simp, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h1 : d 1 = 0
  have hd0 : k ≠ d 0 := by
    intro hk
    apply hd
    ext a
    fin_cases a <;> simp [h1, hk]
  rw [h1, pow_zero, mul_one, hc, if_neg hd0, smul_zero]
  rw [zero_pow h1, mul_zero, map_zero, smul_zero]

theorem coeff_eq_zero_of_eval_second_zero {h : MvPowerSeries (Fin 2) K} (h0 : ev0 h = 0) (n : Fin 2 →₀ ℕ)
    (hn : n 1 = 0) : coeff n h = 0 := by
  have hn' : n = Finsupp.single 0 (n 0) := by
    ext a
    fin_cases a <;> simp [hn]
  rw [hn', ← coeff_evalYZero, h0, map_zero]

end

theorem wave_equation_unique : WaveUnique := by
  intro K _ _ h hw h0 h1
  have hpp : ∀ a m, coeff m (pd a $ pd a h) =
      coeff (m + Finsupp.single a 2) h * (((m a : ℕ) : K) + 2) * (((m a : ℕ) : K) + 1) := by
    intro a m
    unfold pd
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv]
    have : m + Finsupp.single a 1 + Finsupp.single a 1 = m + Finsupp.single a 2 := by
      rw [add_assoc, ← Finsupp.single_add]
    rw [this]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring
  have key : ∀ j i, coeff (Finsupp.single 0 i + Finsupp.single 1 j) h = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i
      rcases j with _ | _ | j
      exact coeff_eq_zero_of_eval_second_zero h0 _ $ by simp
      have := congrArg (PowerSeries.coeff i) h1
      unfold pd at this
      rw [coeff_evalYZero, map_zero, MvPowerSeries.coeff_pderiv] at this
      simpa using this
      have e := congrArg (coeff $ Finsupp.single 0 i + Finsupp.single 1 j) hw
      rw [hpp, hpp] at e
      have e1 : Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single (0 : Fin 2) 2
          = Finsupp.single 0 (i + 2) + Finsupp.single 1 j := by
        ext a
        fin_cases a <;> simp
      have e2 : Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single (1 : Fin 2) 2
          = Finsupp.single 0 i + Finsupp.single 1 (j + 2) := by
        ext a
        fin_cases a <;> simp
      rw [e1, e2, ih j (by omega) $ i + 2, zero_mul, zero_mul] at e
      have hA : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 2 ≠ 0 := by
        have : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 2
            = ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 + 1 : ℕ) : K) + 1 := by push_cast
                                                                                                   ring
        rw [this]
        exact Nat.cast_add_one_ne_zero _
      have hB : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 1 ≠ 0 :=
        Nat.cast_add_one_ne_zero _
      rcases mul_eq_zero.1 e.symm with e' | e'
      rcases mul_eq_zero.1 e' with e'' | e''
      exact e''
      exact absurd e'' hA
      exact absurd e' hB
  ext n
  have hn : n = Finsupp.single 0 (n 0) + Finsupp.single 1 (n 1) := by
    ext a
    fin_cases a <;> simp
  rw [hn, key, map_zero]

section

variable {K : Type} [Field K] [CharZero K]

theorem pd_atS (i : Fin 2) (f : PowerSeries K) : pd i (atS f) = atS (dz f) := by
  unfold atS
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst $ by simp, map_add, MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_X]
  fin_cases i <;> simp

theorem pderiv_zero_series_at_difference (f : PowerSeries K) : pd 0 (atD f) = atD (dz f) := by
  unfold atD
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst $ by simp, map_sub, MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_X]
  simp

theorem pderiv_one_series_at_difference (f : PowerSeries K) : pd 1 (atD f) = -atD (dz f) := by
  unfold atD
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst $ by simp, map_sub, MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_X]
  simp

theorem partialDeriv_inVar_self (i : Fin 2) (f : PowerSeries K) : pd i (at1 i f) = at1 i (dz f) := by
  unfold at1
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst $ by simp, MvPowerSeries.pderiv_X]
  simp

theorem pderiv_at_variable_of_ne {i j : Fin 2} (hij : j ≠ i) (f : PowerSeries K) : pd i (at1 j f) = 0 := by
  unfold at1
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst $ by simp, MvPowerSeries.pderiv_X, Pi.single_eq_of_ne hij, mul_zero]

theorem pderiv_zero_parallelogram_defect (f : PowerSeries K) :
    pd 0 (par0 f) = atS (dz f) + atD (dz f) - 2 * at1 0 (dz f) := by
  simp only [par0, two_mul, map_add, map_sub, pd_atS, pderiv_zero_series_at_difference, partialDeriv_inVar_self,
    pderiv_at_variable_of_ne $ show (1 : Fin 2) ≠ 0 by decide]
  abel

theorem pderiv_one_parallelogram_defect (f : PowerSeries K) :
    pd 1 (par0 f) = atS (dz f) - atD (dz f) - 2 * at1 1 (dz f) := by
  simp [par0, two_mul, map_add, map_sub, pd_atS, pderiv_one_series_at_difference, partialDeriv_inVar_self,
    pderiv_at_variable_of_ne $ show (0 : Fin 2) ≠ 1 by decide]
  abel

end

theorem wave_operator_kills : WaveKills := by
  intro K _ _ f
  rw [pderiv_zero_parallelogram_defect, pderiv_one_parallelogram_defect]
  simp [two_mul, map_add, map_sub, map_neg, pd_atS, pderiv_zero_series_at_difference, pderiv_one_series_at_difference, partialDeriv_inVar_self,
    pderiv_at_variable_of_ne $ show (1 : Fin 2) ≠ 0 by decide]
  ring

theorem parallelogram_cauchy_equation : ParCauchy := by
  intro K _ _ f hf0 hf1
  have hd0 : PowerSeries.constantCoeff (dz f) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, zero_add, hf1,
      zero_mul]
  constructor
  simp [par0, two_mul]
  rw [eval_second_zero_sub, eval_second_zero_sub, evalYZero_add, evalYZero_add, evalYZero_add, eval_second_zero_at_sum, eval_second_zero_at_difference, eval_second_zero_at_variable_zero, restrictSecondZero_inVar_one, hf0,
    map_zero]
  abel
  rw [pderiv_one_parallelogram_defect]
  simp [two_mul]
  rw [eval_second_zero_sub, eval_second_zero_sub, evalYZero_add, eval_second_zero_at_sum, eval_second_zero_at_difference, restrictSecondZero_inVar_one, hd0, map_zero]
  abel

theorem coeff_dq {K : Type} [Field K] [CharZero K] (P : PowerSeries K) (n : Fin 2 →₀ ℕ) :
    coeff n (dq P) =
      if Even (n 0) ∧ Even (n 1) then PowerSeries.coeff (n 0 + n 1 + 2) P else 0 := rfl

theorem eq_single_zero_iff (n : Fin 2 →₀ ℕ) : n = Finsupp.single 0 (n 0) ↔ n 1 = 0 := by
  constructor
  intro h
  rw [h]
  simp
  intro h
  ext a
  fin_cases a <;> simp [h]

theorem eq_single_one_iff (n : Fin 2 →₀ ℕ) : n = Finsupp.single 1 (n 1) ↔ n 0 = 0 := by
  constructor
  intro h
  rw [h]
  simp
  intro h
  ext a
  fin_cases a <;> simp [h]

theorem difference_quotient_rule_holds : DqRule := by
  intro K _ _ P hodd
  have hc : ∀ m, ¬ Even m → PowerSeries.coeff m P = 0 := fun m hm => hodd m (Nat.not_even_iff_odd.1 hm)
  have hev : ∀ m, 2 ≤ m → (Even (m - 2) ↔ Even m) := by
    intro m hm
    rw [Nat.even_sub hm]
    simp
  have main : ∀ i j, (if j = 0 then PowerSeries.coeff i P else 0) -
      (if i = 0 then PowerSeries.coeff j P else 0) =
      (if 2 ≤ i then (if Even (i - 2) ∧ Even j then PowerSeries.coeff (i - 2 + j + 2) P else 0) else 0) -
      (if 2 ≤ j then (if Even i ∧ Even (j - 2) then PowerSeries.coeff (i + (j - 2) + 2) P else 0)
        else 0) := by
    intro i j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    rw [if_pos rfl, if_neg (by omega : ¬ 2 ≤ 0), sub_zero]
    rcases Nat.lt_or_ge i 2 with hi | hi
    rw [if_neg (by omega : ¬ 2 ≤ i)]
    interval_cases i
    simp
    simp [hc 1 (by decide)]
    rw [if_pos hi, if_neg (by omega : i ≠ 0), sub_zero, show i - 2 + 0 + 2 = i by omega]
    simp [hev i hi]
    by_cases he : Even i
    simp [he]
    simp [he, hc i he]
    rw [if_neg (by omega : j ≠ 0)]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    rw [if_pos rfl, if_neg (by omega : ¬ 2 ≤ 0), zero_sub, zero_sub]
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    have : j = 1 := by omega
    subst this
    simp [hc 1 (by decide)]
    rw [if_pos hj2, show 0 + (j - 2) + 2 = j by omega]
    simp [hev j hj2]
    by_cases he : Even j
    simp [he]
    simp [he, hc j he]
    rw [if_neg (by omega : i ≠ 0)]
    have t1 : (if 2 ≤ i then (if Even (i - 2) ∧ Even j then PowerSeries.coeff (i - 2 + j + 2) P
        else 0) else 0) = if Even i ∧ Even j then PowerSeries.coeff (i + j) P else 0 := by
      by_cases hi2 : 2 ≤ i
      rw [if_pos hi2, show i - 2 + j + 2 = i + j by omega]
      simp [hev i hi2]
      have : i = 1 := by omega
      subst this
      simp
    have t2 : (if 2 ≤ j then (if Even i ∧ Even (j - 2) then PowerSeries.coeff (i + (j - 2) + 2) P
        else 0) else 0) = if Even i ∧ Even j then PowerSeries.coeff (i + j) P else 0 := by
      by_cases hj2 : 2 ≤ j
      rw [if_pos hj2, show i + (j - 2) + 2 = i + j by omega]
      simp [hev j hj2]
      have : j = 1 := by omega
      subst this
      simp
    rw [t1, t2]
    simp
  ext n
  rw [map_sub, coeff_single_variable_series, coeff_single_variable_series, sub_mul, map_sub, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, coeff_dq, coeff_dq]
  simp [eq_single_zero_iff, eq_single_one_iff, Finsupp.single_le_iff, Finsupp.tsub_apply,
    Finsupp.single_apply, one_mul]
  simpa using main (n 0) (n 1)

end Formalism.L2.Th1.B
end
section
namespace Formalism.L2.Th1.B

theorem expLogRules : ExpLogRules := by
  intro K _ _ ι
  exact ⟨fun f g hf hg => fExp_add hf hg, fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩,
    fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩
theorem expLogDeriv : ExpLogDeriv := by
  intro K _ _ ι _ i
  constructor
  exact fun f hf => pd_fExp i hf
  exact fun g hg => mul_pd_fLog i hg
theorem expLogSubst : ExpLogSubst := by
  intro K _ _ ι κ _ φ hφ
  constructor
  exact fun f hf => subst_fExp hφ hf
  exact fun g hg => subst_fLog hφ hg
theorem primRules : PrimRules := by
  intro K _ _ f
  constructor
  exact dz_prim f
  exact constantCoeff_prim f
theorem waveUnique : WaveUnique := wave_equation_unique
theorem waveKills : WaveKills := wave_operator_kills
theorem parCauchy : ParCauchy := parallelogram_cauchy_equation
theorem dqRule : DqRule := difference_quotient_rule_holds
theorem wpReduced : WpReduced := weierstrassReducedEquations
theorem addSigmaLog : AddSigmaLog :=
  AddSigmaLog_of expLogDeriv expLogSubst primRules waveUnique waveKills parCauchy wpReduced dqRule
theorem addSigma : AddSigma := AddSigma_of addSigmaLog expLogRules expLogSubst dqRule
theorem addSgStar : AddSgStar := AddSgStar_of addSigma expLogRules expLogSubst

end Formalism.L2.Th1.B
end
section
open PowerSeries


namespace Formalism.LT

open Formalism.G

def DivByMv {K : Type u} [NormedField K] {ι : Type v} (x : K) (F : MvPowerSeries ι K) : Prop :=
  ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ ‖x‖

def SolveExists : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Finite ι] (f : PowerSeries R)
    (G : MvPowerSeries ι R),
    constantCoeff f = 0 → coeff 1 f = 1 → MvPowerSeries.constantCoeff G = 0 →
      ∃ h : MvPowerSeries ι R, MvPowerSeries.constantCoeff h = 0 ∧ f.subst h = G

def InvIntegralOfClass : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Finite ι]
    (C : MvPowerSeries ι K → Prop) (f : PowerSeries K),
    constantCoeff f = 0 → coeff 1 f = 1 →
    (∀ a b, C a → C b → C (a - b)) →
    (∀ P : MvPowerSeries ι K, MvPowerSeries.constantCoeff P = 0 → IntegralMv P →
      C (f.subst P)) →
    (∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d : ι →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1) →
    ∀ h : MvPowerSeries ι K, MvPowerSeries.constantCoeff h = 0 → C (f.subst h) → IntegralMv h

def FunEqLowCoeff : Prop :=
  ∀ (K : Type u) [NormedField K] (ι : Type v) (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K), 2 ≤ q →
    ∀ D : MvPowerSeries ι K, IsFunEqTypeMv p q hq σ D → ∀ N : ℕ, 1 ≤ N →
      (∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d : ι →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1

def IntegralSubst : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) (f : PowerSeries K)
    (P : MvPowerSeries ι K),
    IntegralPS f → MvPowerSeries.constantCoeff P = 0 → IntegralMv P → IntegralMv (f.subst P)

def CoeffBound : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → IsFunEqType p q σ f →
      ∀ n : ℕ, ∃ k : ℕ, q ^ k ∣ n ∧ ‖coeff n f‖ * ‖(p : K)‖ ^ k ≤ 1

def PowCongr : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) (p : ℕ), p.Prime →
    ∀ A B : MvPowerSeries ι K, IntegralMv A → IntegralMv B → ∀ r : ℕ, 1 ≤ r →
      DivByMv ((p : K) ^ r) (A - B) →
      ∀ j m : ℕ, DivByMv ((p : K) ^ (r + j)) $ A ^ (p ^ j * m) - B ^ (p ^ j * m)

def FrobCongr : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) (A : MvPowerSeries ι K), IntegralMv A →
      DivByMv (p : K) (A ^ q - MvPowerSeries.expand q hq (MvPowerSeries.map σ A))

end Formalism.LT
end
section
open PowerSeries


namespace Formalism.FG

open Formalism.G Formalism.LT

section Laws

variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]





abbrev v3 (a : Fin 3) (i : ι) : MvPowerSeries (Fin 3 × ι) R := MvPowerSeries.X (a, i)




def IsIdMod2 (f : ι → MvPowerSeries ι R) : Prop :=
  (∀ j, MvPowerSeries.constantCoeff (f j) = 0) ∧
  ∀ j i, MvPowerSeries.coeff (Finsupp.single i 1) (f j) = if i = j then 1 else 0


end Laws



section FunEq

variable {K : Type u} [NormedField K]



end FunEq




















end Formalism.FG
end
section
open MvPowerSeries (coeff constantCoeff subst)
open PowerSeries


namespace Formalism.FG

open Formalism.G Formalism.LT

def SolveExistsV : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] [DecidableEq ι] (τ : Type w) [Finite τ]
    (f : ι → MvPowerSeries ι R) (G : ι → MvPowerSeries τ R), IsIdMod2 f →
    (∀ j, constantCoeff (G j) = 0) →
      ∃ h : ι → MvPowerSeries τ R, (∀ i, constantCoeff (h i) = 0) ∧
        ∀ j, subst h (f j) = G j

def SubstInjectiveV : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] [DecidableEq ι] (τ : Type w) [Finite τ]
    (f : ι → MvPowerSeries ι R) (a b : ι → MvPowerSeries τ R), IsIdMod2 f →
    (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
    (∀ j, subst a (f j) = subst b (f j)) → a = b





def InvIntegralV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (τ : Type w) [Finite τ] (C : (ι → MvPowerSeries τ K) → Prop) (f : ι → MvPowerSeries ι K),
    IsIdMod2 f →
    (∀ a b, C a → C b → C (a - b)) →
    (∀ P : ι → MvPowerSeries τ K, (∀ i, constantCoeff (P i) = 0) →
      (∀ i, IntegralMv $ P i) → C fun j => subst P $ f j) →
    (∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖coeff d (D j)‖ ≤ 1) →
    ∀ h : ι → MvPowerSeries τ K, (∀ i, constantCoeff (h i) = 0) →
      C (fun j => subst h $ f j) → ∀ i, IntegralMv $ h i


end Formalism.FG
end
section
open Finset (mem_univ prod_insert sum_eq_zero univ)
open Finsupp (degree_eq_sum degree_eq_zero_iff prod_fintype prod_single_index single)
namespace Formalism.FG

namespace InjVAux

open MvPowerSeries

variable {R : Type*} [CommRing R] {τ : Type*}

def HasOrd (n : ℕ) (z : MvPowerSeries τ R) : Prop :=
  ∀ d : τ →₀ ℕ, d.degree < n → coeff d z = 0

theorem hasOrd_zero_left (z : MvPowerSeries τ R) : HasOrd 0 z :=
  fun _ hd => absurd hd $ Nat.not_lt_zero _

theorem hasOrd_zero (n : ℕ) : HasOrd n (0 : MvPowerSeries τ R) := fun _ _ => by simp

theorem HasOrd.mono {m n : ℕ} {z : MvPowerSeries τ R} (h : HasOrd n z) (hmn : m ≤ n) :
    HasOrd m z :=
  fun d hd => h d $ lt_of_lt_of_le hd hmn

theorem HasOrd.add {n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd n x) (hy : HasOrd n y) :
    HasOrd n $ x + y :=
  fun d hd => by rw [map_add, hx d hd, hy d hd, add_zero]

theorem HasOrd.sub {n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd n x) (hy : HasOrd n y) :
    HasOrd n $ x - y :=
  fun d hd => by rw [map_sub, hx d hd, hy d hd, sub_zero]

theorem HasOrd.mul {m n : ℕ} {x y : MvPowerSeries τ R} (hx : HasOrd m x) (hy : HasOrd n y) :
    HasOrd (m + n) $ x * y := by
  classical
  intro d hd
  rw [coeff_mul]
  apply sum_eq_zero
  intro p hp
  have hp' : p.1 + p.2 = d := by simpa using hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by rw [← map_add, hp']
  by_cases h1 : p.1.degree < m
  rw [hx _ h1, zero_mul]
  rw [hy _ $ by omega, mul_zero]

def Good (N k : ℕ) (x x' : MvPowerSeries τ R) : Prop :=
  HasOrd k x ∧ HasOrd k x' ∧ HasOrd (N + k) (x - x')

theorem good_one (N : ℕ) : Good N 0 (1 : MvPowerSeries τ R) 1 :=
  ⟨hasOrd_zero_left _, hasOrd_zero_left _, by rw [sub_self]; exact hasOrd_zero _⟩

theorem Good.mul {N k l : ℕ} {x x' y y' : MvPowerSeries τ R} (hx : Good N k x x')
    (hy : Good N l y y') : Good N (k + l) (x * y) $ x' * y' := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  use hx1.mul hy1, hx2.mul hy2
  have e : x * y - x' * y' = x * (y - y') + (x - x') * y' := by ring
  rw [e]
  exact ((hx1.mul hy3).mono $ by omega).add $ (hx3.mul hy2).mono $ by omega

theorem Good.pow {N k : ℕ} {x x' : MvPowerSeries τ R} (hx : Good N k x x') (n : ℕ) :
    Good N (k * n) (x ^ n) $ x' ^ n := by
  induction n with
  | zero => simpa using good_one N
  | succ n ih => rw [pow_succ, pow_succ, Nat.mul_succ]; exact ih.mul hx

theorem good_prod {N : ℕ} {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (x x' : ι → MvPowerSeries τ R) (h : ∀ i ∈ s, Good N (k i) (x i) $ x' i) :
    Good N (∑ i ∈ s, k i) (∏ i ∈ s, x i) (∏ i ∈ s, x' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_one N
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, prod_insert hi, prod_insert hi]
    exact (h i $ Finset.mem_insert_self i s).mul
      $ ih fun j hj => h j $ Finset.mem_insert_of_mem hj

theorem eq_single_of_degree_eq_one {ι : Type*} [Fintype ι] (e : ι →₀ ℕ)
    (he : e.degree = 1) : ∃ i, e = single i 1 := by
  classical
  rw [degree_eq_sum] at he
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hc
    simp [not_exists, not_not] at hc
    rw [sum_eq_zero fun k _ => hc k] at he
    exact zero_ne_one he
  have hsplit := Finset.add_sum_erase univ e $ mem_univ i
  rw [he] at hsplit
  have hei : e i = 1 := by omega
  use i
  ext k
  by_cases hk : k = i
  subst hk
  simp [hei]
  rw [Finsupp.single_apply, if_neg $ Ne.symm hk]
  have : e k ≤ ∑ x ∈ Finset.univ.erase i, e x :=
    Finset.single_le_sum (f := fun x => e x) (fun _ _ => Nat.zero_le _)
      $ Finset.mem_erase.2 ⟨hk, mem_univ k⟩
  omega

theorem hasOrd_one_of_cc {z : MvPowerSeries τ R} (hz : constantCoeff z = 0) : HasOrd 1 z := by
  intro d hd
  have : d = 0 := (degree_eq_zero_iff d).1 $ by omega
  subst this
  simpa using hz

theorem main {ι : Type*} [Fintype ι] [DecidableEq ι] [Finite τ]
    (f : ι → MvPowerSeries ι R) (a b : ι → MvPowerSeries τ R) (hf : IsIdMod2 f)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (h : ∀ j, subst a (f j) = subst b (f j)) :
    ∀ N, ∀ i, HasOrd (N + 1) (a i - b i) := by
  have haS := hasSubst_of_constantCoeff_zero ha
  have hbS := hasSubst_of_constantCoeff_zero hb
  intro N
  induction N with
  | zero => intro i; exact (hasOrd_one_of_cc (ha i)).sub (hasOrd_one_of_cc (hb i))
  | succ N ih =>
    intro j d hd
    have hgood : ∀ i, Good N 1 (a i) (b i) :=
      fun i => ⟨hasOrd_one_of_cc (ha i), hasOrd_one_of_cc (hb i), ih i⟩
    have hj := congrArg (coeff d) (h j)
    rw [coeff_subst haS, coeff_subst hbS] at hj
    have hdiff := congrArg (fun t => t - finsum fun e =>
      coeff e (f j) • coeff d (e.prod fun s n => b s ^ n)) hj
    simp only [sub_self] at hdiff
    rw [← finsum_sub_distrib (coeff_subst_finite haS (f j) d)
      $ coeff_subst_finite hbS (f j) d] at hdiff
    rw [finsum_eq_single _ (single j 1)] at hdiff
    rw [prod_single_index (by simp), prod_single_index (by simp),
      hf.2 j j, if_pos rfl, one_smul, one_smul, pow_one, pow_one] at hdiff
    rw [map_sub, hdiff]
    intro e he
    rw [← smul_sub, ← map_sub]
    rcases Nat.lt_or_ge e.degree 2 with hlt | hge
    rcases Nat.lt_or_ge e.degree 1 with h0 | h1
    have : e = 0 := (degree_eq_zero_iff e).1 (by omega)
    subst this
    simp
    obtain ⟨i, rfl⟩ := eq_single_of_degree_eq_one e (by omega)
    rw [hf.2 j i, if_neg fun hij => he (by rw [hij]), zero_smul]
    rw [prod_fintype _ _ fun _ => pow_zero _,
      prod_fintype _ _ fun _ => pow_zero _]
    have hg := good_prod univ (fun i => 1 * e i) (fun i => a i ^ e i)
      (fun i => b i ^ e i) fun i _ => (hgood i).pow (e i)
    have hsum : ∑ i ∈ univ, 1 * e i = e.degree := by
      rw [degree_eq_sum]; simp
    rw [hsum] at hg
    rw [hg.2.2.mono (n := N + e.degree) (by omega) d hd, smul_zero]

end InjVAux

open MvPowerSeries in
theorem subst_injective_vector : Formalism.FG.SubstInjectiveV.{u, v, w} := by
  intro R _ ι _ _ τ _ f a b hf ha hb h
  funext i
  ext d
  have := InjVAux.main f a b hf ha hb h d.degree i d $ by omega
  rwa [map_sub, sub_eq_zero] at this

end Formalism.FG
end
section
namespace Formalism.FG.IntegralSubstitution

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

theorem integral_mul {A B : MvPowerSeries τ K} (hA : IntegralMv A) (hB : IntegralMv B) :
    IntegralMv $ A * B := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _) (norm_nonneg _) $ hB _

theorem integral_one : IntegralMv (1 : MvPowerSeries τ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integral_pow {A : MvPowerSeries τ K} (hA : IntegralMv A) (n : ℕ) :
    IntegralMv $ A ^ n := by
  induction n with
  | zero => simpa using integral_one
  | succ n ih => rw [pow_succ]; exact integral_mul ih hA

theorem integral_finsuppProd {ι : Type v} (a : ι → MvPowerSeries τ K) (ha : ∀ i, IntegralMv (a i))
    (n : ι →₀ ℕ) : IntegralMv $ n.prod fun s e => (a s) ^ e := by
  classical
  unfold Finsupp.prod
  exact Finset.prod_induction _ IntegralMv (fun _ _ hx hy => integral_mul hx hy)
    integral_one fun i _ => integral_pow (ha i) _

theorem integralSubstV {ι : Type v} [Finite ι] (g : MvPowerSeries ι K)
    (a : ι → MvPowerSeries τ K) (hg : IntegralMv g)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha : ∀ i, IntegralMv $ a i) :
    IntegralMv $ MvPowerSeries.subst a g := by
  intro d
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  rw [MvPowerSeries.coeff_subst hs g d, finsum_eq_sum _ $ MvPowerSeries.coeff_subst_finite hs g d]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
  rw [smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hg n) (norm_nonneg _) $ integral_finsuppProd a ha n d

end Formalism.FG.IntegralSubstitution
end
section
namespace Formalism.FG.InvIntVAux

open Formalism.G Formalism.G.LogCR

variable {K : Type u} [NormedField K]

def Low {σ : Type*} (m : ℕ) (x : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < m → MvPowerSeries.coeff d x = 0

section Basic

variable {σ : Type*}

theorem Low.mono {m k : ℕ} {x : MvPowerSeries σ K} (h : Low m x) (hk : k ≤ m) : Low k x := by
  intro d hd
  exact h d $ lt_of_lt_of_le hd hk

theorem Low.mul {m k : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) $ x * y := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = d := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | exact (_root_.Finset.mem_antidiagonal).mp hp
      | simpa using hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by
    rw [← hp']
    first
      | exact (Finsupp.degree_add p.1 p.2).symm
      | exact (map_add Finsupp.degree p.1 p.2).symm
      | simp
  by_cases h1 : p.1.degree < m
  rw [hx _ h1, zero_mul]
  rw [hy _ $ by omega, mul_zero]

theorem Low.add {m : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low m y) :
    Low m $ x + y := by
  intro d hd
  rw [map_add, hx d hd, hy d hd, add_zero]

theorem Low.sum {α : Type*} {m : ℕ} (s : Finset α) (x : α → MvPowerSeries σ K)
    (h : ∀ a ∈ s, Low m $ x a) : Low m (∑ a ∈ s, x a) := by
  intro d hd
  rw [map_sum]
  exact Finset.sum_eq_zero fun a ha => h a ha d hd

theorem low_one {x : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0) : Low 1 x := by
  intro d hd
  have h0 : d = 0 := by
    first
      | exact (Finsupp.degree_eq_zero_iff d).1 $ by omega
      | exact Finsupp.degree_eq_zero_iff.1 $ by omega
      | simpa using (show d.degree = 0 by omega)
  subst h0
  first
    | exact hx
    | simpa using hx

theorem low_of_agree {N : ℕ} {a b : MvPowerSeries σ K} (hab : Agree N a b) : Low N $ a - b := by
  intro d hd
  rw [map_sub, hab d hd, sub_self]

end Basic

theorem eq_single_of_degree_eq_one {ι : Type*} [Fintype ι] (e : ι →₀ ℕ)
    (he : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  classical
  have hd : e.degree = ∑ j ∈ e.support, e j := by
    first
      | rfl
      | simp [Finsupp.degree]
  rw [hd] at he
  have hcard : e.support.card ≤ 1 := by
    have h1 : ∑ j ∈ e.support, (1 : ℕ) ≤ ∑ j ∈ e.support, e j :=
      Finset.sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.mpr $ Finsupp.mem_support_iff.mp hj
    rwa [he, Finset.sum_const, smul_eq_mul, mul_one] at h1
  have hpos : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.sum_empty] at he
    omega
  have hc1 : e.support.card = 1 := by
    have := Finset.card_pos.mpr hpos
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc1
  use i
  rw [hi, Finset.sum_singleton] at he
  ext j
  by_cases hj : j = i
  rw [hj, he, Finsupp.single_eq_same]
  have hz : e j = 0 := by
    by_contra hne
    have hmem : j ∈ e.support := Finsupp.mem_support_iff.mpr hne
    rw [hi, Finset.mem_singleton] at hmem
    exact hj hmem
  rw [hz]
  simp [Ne.symm hj]

theorem decomp {σ : Type*} [Fintype σ] [LinearOrder σ] (m : ℕ) (x : MvPowerSeries σ K)
    (hx : Low (m + 1) x) :
    ∃ y : σ → MvPowerSeries σ K, (∀ i, Low m $ y i) ∧ x = ∑ i, MvPowerSeries.X i * y i := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : σ → MvPowerSeries σ K, ∀ i e, MvPowerSeries.coeff e (y i) =
      if (e + Finsupp.single i 1).support.min = (i : WithTop σ) then
        MvPowerSeries.coeff (e + Finsupp.single i 1) x else 0 :=
    ⟨fun i e => if (e + Finsupp.single i 1).support.min = (i : WithTop σ) then
        MvPowerSeries.coeff (e + Finsupp.single i 1) x else 0, fun i e => rfl⟩
  have hd0 : (0 : σ →₀ ℕ).degree = 0 := by
    first | rfl | simp
  refine ⟨y, fun i e he => ?_, ?_⟩
  rw [hy]
  split_ifs with hmin
  have hdeg : (e + Finsupp.single i 1).degree = e.degree + 1 := by
    first
      | rw [Finsupp.degree_add, Finsupp.degree_single]
      | simp
  apply hx _
  omega
  rfl
  ext d
  rw [map_sum]
  have hXm : ∀ i (φ : MvPowerSeries σ K), MvPowerSeries.coeff d (MvPowerSeries.X i * φ) =
      if Finsupp.single i 1 ≤ d then MvPowerSeries.coeff (d - Finsupp.single i 1) φ else 0 := by
    intro i φ
    first
      | rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, one_mul]
      | rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
      | simp [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
  simp only [hXm]
  by_cases hdz : d = 0
  subst hdz
  rw [hx 0 (by rw [hd0]; omega)]
  refine (Finset.sum_eq_zero fun i _ => ?_).symm
  have hnle : ¬ Finsupp.single i 1 ≤ (0 : σ →₀ ℕ) := by
    intro hle
    have := hle i
    simp at this
  rw [if_neg hnle]
  have hne : d.support.Nonempty := Finsupp.support_nonempty_iff.mpr hdz
  obtain ⟨i0, hmin⟩ := Finset.min_of_nonempty hne
  have hd1 := Nat.one_le_iff_ne_zero.mpr $ Finsupp.mem_support_iff.mp $ Finset.mem_of_min hmin
  have hle : Finsupp.single i0 1 ≤ d := by
    first
      | exact Finsupp.single_le_iff.mpr hd1
      | (intro j; by_cases hj : i0 = j; (subst hj; simpa using hd1); simp [Finsupp.single_apply, hj])
  rw [Finset.sum_eq_single i0]
  rw [if_pos hle, hy, tsub_add_cancel_of_le hle, if_pos hmin]
  intro i _ hi
  split_ifs with hle'
  have hc : ¬ d.support.min = (i : WithTop σ) := by
    rw [hmin]
    intro h
    exact hi (WithTop.coe_injective h).symm
  rw [hy, tsub_add_cancel_of_le hle', if_neg hc]
  rfl
  intro h
  exact absurd (Finset.mem_univ i0) h

private theorem subst_diff_lemma {σ τ : Type*} [Fintype σ] [Finite τ] (N : ℕ) :
    ∀ (z : MvPowerSeries σ K) (a b : σ → MvPowerSeries τ K),
      (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
      (∀ i, MvPowerSeries.constantCoeff (b i) = 0) → (∀ i, Agree N (a i) $ b i) →
      Low N (MvPowerSeries.subst a z - MvPowerSeries.subst b z) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  induction N with
  | zero => intro z a b _ _ _ d hd; exact absurd hd $ Nat.not_lt_zero _
  | succ N ih =>
    intro z a b ha hb hab
    have hsa := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    have hsb := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
    have hφa : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst a w = MvPowerSeries.substAlgHom (R := K) hsa w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsa) w).symm
        | rfl
    have hφb : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst b w = MvPowerSeries.substAlgHom (R := K) hsb w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsb) w).symm
        | rfl
    obtain ⟨c, hc⟩ : ∃ c, c = MvPowerSeries.constantCoeff z := ⟨_, rfl⟩
    have hcz : MvPowerSeries.constantCoeff (algebraMap K (MvPowerSeries σ K) c) = c := by
      first
        | (simp; done)
        | (simp [MvPowerSeries.algebraMap_apply]; done)
        | (simp [← MvPowerSeries.c_eq_algebraMap]; done)
        | (rw [Algebra.algebraMap_eq_smul_one]; simp; done)
        | (rw [Algebra.algebraMap_eq_smul_one, MvPowerSeries.constantCoeff_smul]; simp; done)
        | rfl
    obtain ⟨y, -, hy⟩ := decomp 0 (z - algebraMap K (MvPowerSeries σ K) c) $ by
        apply low_one
        rw [map_sub, hcz, hc, sub_self]
    have hz : z = algebraMap K (MvPowerSeries σ K) c + ∑ i, MvPowerSeries.X i * y i := by
      rw [← hy]
      abel
    have hab' : ∀ i, Agree N (a i) $ b i := fun i e he => hab i e $ by omega
    rw [hz, hφa, hφb, map_add, map_add, AlgHom.commutes, AlgHom.commutes, map_sum, map_sum,
      add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Low.sum
    intro i _
    beta_reduce
    rw [map_mul, map_mul, ← hφa, ← hφa, ← hφb, ← hφb, MvPowerSeries.subst_X hsa,
      MvPowerSeries.subst_X hsb]
    have hsplit : a i * MvPowerSeries.subst a (y i) - b i * MvPowerSeries.subst b (y i) =
        (a i - b i) * MvPowerSeries.subst a (y i) +
          b i * (MvPowerSeries.subst a (y i) - MvPowerSeries.subst b (y i)) := by ring
    rw [hsplit]
    apply Low.add
    have h1 := Low.mul (low_of_agree $ hab i)
      (show Low 0 (MvPowerSeries.subst a $ y i) from fun e he => absurd he $ Nat.not_lt_zero _)
    rwa [add_zero] at h1
    have h2 := Low.mul (low_one $ hb i) $ ih (y i) a b ha hb hab'
    rwa [add_comm] at h2

private theorem low_one_subst_lemma_2 {σ τ : Type*} [Fintype σ] [Finite τ] (w : MvPowerSeries σ K)
    (hw : Low 1 w) (a : σ → MvPowerSeries τ K)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    Low 1 $ MvPowerSeries.subst a w := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have hsa := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hφa : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst a w = MvPowerSeries.substAlgHom (R := K) hsa w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsa) w).symm
        | rfl
  obtain ⟨y, -, hy⟩ := decomp 0 w hw
  rw [hy, hφa, map_sum]
  apply Low.sum
  intro i _
  beta_reduce
  rw [map_mul, ← hφa, ← hφa, MvPowerSeries.subst_X hsa]
  have h1 := Low.mul (low_one $ ha i)
    $ show Low 0 (MvPowerSeries.subst a $ y i) from fun e he => absurd he $ Nat.not_lt_zero _
  rwa [add_zero] at h1

theorem low_subst_diff {σ τ : Type*} [Fintype σ] [Finite τ] (g : MvPowerSeries σ K)
    (hg : Low 2 g) {N : ℕ} {a b : σ → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hab : ∀ i, Agree N (a i) $ b i) :
    Low (N + 1) $ MvPowerSeries.subst a g - MvPowerSeries.subst b g := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have hsa := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hsb := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  have hφa : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst a w = MvPowerSeries.substAlgHom (R := K) hsa w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsa) w).symm
        | rfl
  have hφb : ∀ w : MvPowerSeries σ K, MvPowerSeries.subst b w = MvPowerSeries.substAlgHom (R := K) hsb w := by
      intro w
      first
        | rw [MvPowerSeries.coe_substAlgHom]
        | exact (congrFun (MvPowerSeries.coe_substAlgHom (R := K) hsb) w).symm
        | rfl
  obtain ⟨y, hy1, hy⟩ := decomp 1 g hg
  rw [hy, hφa, hφb, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Low.sum
  intro i _
  beta_reduce
  rw [map_mul, map_mul, ← hφa, ← hφa, ← hφb, ← hφb, MvPowerSeries.subst_X hsa,
    MvPowerSeries.subst_X hsb]
  have hsplit : a i * MvPowerSeries.subst a (y i) - b i * MvPowerSeries.subst b (y i) =
      (a i - b i) * MvPowerSeries.subst a (y i) +
        b i * (MvPowerSeries.subst a (y i) - MvPowerSeries.subst b (y i)) := by ring
  rw [hsplit]
  apply Low.add
  exact Low.mul (low_of_agree $ hab i) $ low_one_subst_lemma_2 (y i) (hy1 i) a ha
  have h2 := Low.mul (low_one $ hb i) $ subst_diff_lemma N (y i) a b ha hb hab
  rwa [add_comm] at h2

theorem tail_low {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → MvPowerSeries ι K)
    (hf : IsIdMod2 f) (j : ι) : Low 2 $ f j - MvPowerSeries.X j := by
  intro d hd
  obtain h0 | h1 : d.degree = 0 ∨ d.degree = 1 := by omega
  have hL : Low 1 $ f j - MvPowerSeries.X j := low_one $ by simp [hf.1 j]
  apply hL d
  omega
  obtain ⟨i, rfl⟩ := eq_single_of_degree_eq_one d h1
  rw [map_sub, hf.2 j i, MvPowerSeries.coeff_X]
  by_cases hij : i = j
  subst hij
  simp
  have hne : Finsupp.single i 1 ≠ Finsupp.single j 1 := by
    intro heq
    exact hij $ Finsupp.single_left_injective one_ne_zero heq
  rw [if_neg hij, if_neg hne, sub_zero]

theorem main (ι : Type v) [Fintype ι] [DecidableEq ι]
    (τ : Type w) [Finite τ] (C : (ι → MvPowerSeries τ K) → Prop) (f : ι → MvPowerSeries ι K)
    (hf : IsIdMod2 f)
    (hsub : ∀ a b, C a → C b → C (a - b))
    (hP : ∀ P : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (P i) = 0) →
      (∀ i, IntegralMv $ P i) → C fun j => MvPowerSeries.subst P $ f j)
    (hlowC : ∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ j (d : τ →₀ ℕ), d.degree < N → MvPowerSeries.coeff d (D j) = 0) →
      ∀ j (d : τ →₀ ℕ), d.degree = N → ‖MvPowerSeries.coeff d (D j)‖ ≤ 1)
    (h : ι → MvPowerSeries τ K) (hh0 : ∀ i, MvPowerSeries.constantCoeff (h i) = 0)
    (hCh : C fun j => MvPowerSeries.subst h $ f j) : ∀ i, IntegralMv $ h i := by
  classical
  have hcc : ∀ x : MvPowerSeries τ K, MvPowerSeries.constantCoeff x = MvPowerSeries.coeff 0 x :=
    fun x => by first | rfl | simp
  have hdz : ∀ e : τ →₀ ℕ, e.degree = 0 → e = 0 := fun e he => by
    first
      | exact (Finsupp.degree_eq_zero_iff e).1 he
      | exact Finsupp.degree_eq_zero_iff.1 he
      | simpa using he
  have hd0 : (0 : τ →₀ ℕ).degree = 0 := by
    first | rfl | simp
  have hsubX : ∀ (a : ι → MvPowerSeries τ K), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) →
      ∀ j, MvPowerSeries.subst a (f j) =
        a j + MvPowerSeries.subst a (f j - MvPowerSeries.X j) := by
    intro a ha j
    have hs : MvPowerSeries.HasSubst a := by
      first
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
        | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
            fun s => by rw [ha s]; exact IsNilpotent.zero
        | exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩
    have hsub' : MvPowerSeries.subst a (f j - MvPowerSeries.X j) =
        MvPowerSeries.subst a (f j) -
          MvPowerSeries.subst a (MvPowerSeries.X j : MvPowerSeries ι K) := by
      first
        | exact MvPowerSeries.subst_sub hs _ _
        | rw [eq_sub_iff_add_eq, ← MvPowerSeries.subst_add hs, sub_add_cancel]
        | (rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_sub _ _ _)
    rw [hsub', MvPowerSeries.subst_X hs]
    abel
  have key : ∀ N : ℕ, ∀ i (d : τ →₀ ℕ), d.degree < N →
      ‖MvPowerSeries.coeff d (h i)‖ ≤ 1 := by
    intro N
    induction N with
    | zero => intro i d hd; exact absurd hd $ Nat.not_lt_zero _
    | succ N ih =>
      intro i d hd
      rcases Nat.lt_or_ge d.degree N with hlt | hge
      exact ih i d hlt
      have hdN : d.degree = N := by omega
      rcases Nat.eq_zero_or_pos N with hN | hN
      have hd00 : d = 0 := hdz d $ by omega
      subst hd00
      rw [← hcc, hh0 i, norm_zero]
      exact zero_le_one
      obtain ⟨P, hPc⟩ : ∃ P : ι → MvPowerSeries τ K, ∀ j e,
          MvPowerSeries.coeff e (P j) =
            if e.degree < N then MvPowerSeries.coeff e $ h j else 0 :=
        ⟨fun j e => if e.degree < N then MvPowerSeries.coeff e $ h j else 0, fun j e => rfl⟩
      have h0N : (0 : τ →₀ ℕ).degree < N := by rw [hd0]; exact hN
      have hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0 := by
        intro j
        rw [hcc, hPc, if_pos h0N, ← hcc, hh0 j]
      have hPint : ∀ j, IntegralMv $ P j := by
        intro j e
        rw [hPc]
        split_ifs with he
        exact ih j e he
        rw [norm_zero]
        exact zero_le_one
      have hagree : ∀ j, Agree N (h j) $ P j := by
        intro j e he
        rw [hPc, if_pos he]
      have hDc : ∀ j (e : τ →₀ ℕ), e.degree ≤ N →
          MvPowerSeries.coeff e (((fun j : ι => MvPowerSeries.subst h $ f j) -
            (fun j : ι => MvPowerSeries.subst P $ f j)) j) =
          if e.degree < N then 0 else MvPowerSeries.coeff e $ h j := by
        intro j e he
        simp only [Pi.sub_apply]
        rw [hsubX h hh0 j, hsubX P hP0 j]
        have hrw : h j + MvPowerSeries.subst h (f j - MvPowerSeries.X j) -
            (P j + MvPowerSeries.subst P (f j - MvPowerSeries.X j)) =
            (h j - P j) + (MvPowerSeries.subst h (f j - MvPowerSeries.X j) -
              MvPowerSeries.subst P (f j - MvPowerSeries.X j)) := by abel
        have he1 : e.degree < N + 1 := by omega
        rw [hrw, map_add, (low_subst_diff (f j - MvPowerSeries.X j) (tail_low f hf j) hh0 hP0 hagree) e he1, add_zero, map_sub, hPc]
        split_ifs with h1
        exact sub_self _
        exact sub_zero _
      have hvan : ∀ j (e : τ →₀ ℕ), e.degree < N →
          MvPowerSeries.coeff e (((fun j : ι => MvPowerSeries.subst h $ f j) -
            (fun j : ι => MvPowerSeries.subst P $ f j)) j) = 0 := by
        intro j e he
        rw [hDc j e he.le, if_pos he]
      have hN1 : 1 ≤ N := by omega
      have hb := hlowC _ (hsub _ _ hCh $ hP P hP0 hPint) N hN1 hvan i d hdN
      have hnlt : ¬ d.degree < N := by omega
      rw [hDc i d hdN.le, if_neg hnlt] at hb
      exact hb
  intro i d
  exact key (d.degree + 1) i d $ Nat.lt_succ_self _

end Formalism.FG.InvIntVAux

theorem Formalism.FG.inverse_integral_vector : Formalism.FG.InvIntegralV.{u, v, w} := by
  intro K _ _ ι _ _ τ _ C f hf hsub hP hlowC h hh0 hCh
  exact Formalism.FG.InvIntVAux.main ι τ C f hf hsub hP hlowC h hh0 hCh
end
section
open Finsupp (degree_eq_zero_iff degree_single ext induction_linear single single_le_iff)
namespace Formalism.FG.SolveVAux

open MvPowerSeries

section Low

variable {R : Type u} [CommRing R] {τ : Type w}

def Low (N : ℕ) (p : MvPowerSeries τ R) : Prop :=
  ∀ d : τ →₀ ℕ, d.degree < N → coeff d p = 0

theorem low_zero (p : MvPowerSeries τ R) : Low 0 p := fun _ hd => absurd hd $ Nat.not_lt_zero _

theorem low_mono {M N : ℕ} (h : M ≤ N) {p : MvPowerSeries τ R} (hp : Low N p) : Low M p :=
  fun d hd => hp d $ lt_of_lt_of_le hd h

theorem low_of_zero (N : ℕ) : Low N (0 : MvPowerSeries τ R) := fun d _ => by simp

theorem low_add {N : ℕ} {p q : MvPowerSeries τ R} (hp : Low N p) (hq : Low N q) :
    Low N $ p + q :=
  fun d hd => by rw [map_add, hp d hd, hq d hd, add_zero]

theorem low_neg {N : ℕ} {p : MvPowerSeries τ R} (hp : Low N p) : Low N $ -p :=
  fun d hd => by rw [map_neg, hp d hd, neg_zero]

theorem low_sub {N : ℕ} {p q : MvPowerSeries τ R} (hp : Low N p) (hq : Low N q) :
    Low N $ p - q :=
  fun d hd => by rw [map_sub, hp d hd, hq d hd, sub_zero]

theorem low_mul {M N : ℕ} {p q : MvPowerSeries τ R} (hp : Low M p) (hq : Low N q) :
    Low (M + N) $ p * q := by
  classical
  intro d hd
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree := map_add _ _ _
  rw [hx] at hdeg
  rcases lt_or_ge x.1.degree M with h1 | h1
  rw [hp _ h1, zero_mul]
  rw [hq _ $ by omega, mul_zero]

theorem low_one_iff (p : MvPowerSeries τ R) : Low 1 p ↔ constantCoeff p = 0 := by
  constructor
  intro hp
  rw [← coeff_zero_eq_constantCoeff_apply]
  apply hp 0
  simp
  intro hp d hd
  have : d = 0 := (degree_eq_zero_iff d).1 $ by omega
  rw [this, coeff_zero_eq_constantCoeff_apply, hp]

theorem low_mul_sub {M : ℕ} {a a' b b' : MvPowerSeries τ R} (ha : Low M (a - a'))
    (hb : Low M $ b - b') : Low M $ a * b - a' * b' := by
  have e : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [e]
  refine low_add ?_ ?_
  simpa using low_mul ha $ low_zero b
  simpa using low_mul (low_zero a') hb

end Low

section Prod

variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}

def P (k : ι → MvPowerSeries τ R) (e : ι →₀ ℕ) : MvPowerSeries τ R :=
  e.prod fun s n => k s ^ n

theorem P_add (k : ι → MvPowerSeries τ R) (e₁ e₂ : ι →₀ ℕ) :
    P k (e₁ + e₂) = P k e₁ * P k e₂ :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _

theorem P_single (k : ι → MvPowerSeries τ R) (i : ι) (n : ℕ) :
    P k (single i n) = k i ^ n :=
  Finsupp.prod_single_index $ pow_zero _

theorem P_zero (k : ι → MvPowerSeries τ R) : P k 0 = 1 := Finsupp.prod_zero_index

theorem low_pow {p : MvPowerSeries τ R} (hp : Low 1 p) (n : ℕ) : Low n $ p ^ n := by
  induction n with
  | zero => exact low_zero _
  | succ n ih => rw [pow_succ]; exact low_mul ih hp

theorem low_P {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) (e : ι →₀ ℕ) :
    Low e.degree $ P k e := by
  induction e using induction_linear with
  | zero => exact low_zero _
  | add e₁ e₂ h₁ h₂ =>
    rw [P_add, map_add]
    exact low_mul h₁ h₂
  | single i n =>
    rw [P_single, degree_single]
    exact low_pow (hk i) n

theorem low_pow_sub₂ {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hkk : ∀ i, Low M (k i - k' i))
    (e : ι →₀ ℕ) : Low M $ P k e - P k' e := by
  induction e using induction_linear with
  | zero => rw [P_zero, P_zero, sub_self]; exact low_of_zero _
  | add e₁ e₂ h₁ h₂ =>
    rw [P_add, P_add]; exact low_mul_sub h₁ h₂
  | single i n =>
    rw [P_single, P_single]
    induction n with
    | zero => rw [pow_zero, pow_zero, sub_self]; exact low_of_zero _
    | succ n ih => rw [pow_succ, pow_succ]; exact low_mul_sub ih $ hkk i

theorem low_pow_sub_succ {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i))
    (hk' : ∀ i, Low 1 $ k' i) (hkk : ∀ i, Low M $ k i - k' i) (e : ι →₀ ℕ)
    (he : 2 ≤ e.degree) : Low (M + 1) $ P k e - P k' e := by
  classical
  have hne : e ≠ 0 := by rintro rfl
                         simp at he
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra! hc
    exact hne $ ext hc
  have hle : single i 1 ≤ e := by
    rw [single_le_iff]
    omega
  set e' := e - single i 1 with he'
  have hsplit : e = e' + single i 1 := (tsub_add_cancel_of_le hle).symm
  have hdeg : e.degree = e'.degree + 1 := by
    conv_lhs => rw [hsplit]
    rw [map_add, degree_single]
  rw [hsplit, P_add, P_add, P_single, P_single, pow_one, pow_one]
  have e2 : P k e' * k i - P k' e' * k' i =
      (P k e' - P k' e') * k i + P k' e' * (k i - k' i) := by
    ring
  rw [e2]
  refine low_add (low_mul (low_pow_sub₂ hkk e') $ hk i) ?_
  rw [add_comm]
  exact low_mul (low_mono (by omega) $ low_P hk' e') $ hkk i

end Prod

section Subst

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}

theorem hasSubst_of_low {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) : HasSubst k :=
  hasSubst_of_constantCoeff_zero fun i => (low_one_iff _).1 $ hk i

theorem low_subst {k : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i)) {p : MvPowerSeries ι R}
    (hp : Low 1 p) : Low 1 $ subst k p :=
  (low_one_iff _).2 $ constantCoeff_subst_eq_zero (hasSubst_of_low hk)
    (fun i => (low_one_iff _).1 $ hk i) $ (low_one_iff _).1 hp

theorem low_subst_sub {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i))
    (hk' : ∀ i, Low 1 $ k' i) (hkk : ∀ i, Low M $ k i - k' i) {g : MvPowerSeries ι R}
    (hg : Low 2 g) : Low (M + 1) $ subst k g - subst k' g := by
  intro d hd
  have hs := hasSubst_of_low hk
  have hs' := hasSubst_of_low hk'
  rw [map_sub, coeff_subst hs, coeff_subst hs', ← finsum_sub_distrib (coeff_subst_finite hs g d)
    $ coeff_subst_finite hs' g d]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rw [← smul_sub]
  rcases lt_or_ge e.degree 2 with he | he
  rw [hg e he, zero_smul]
  have := low_pow_sub_succ hk hk' hkk e he d hd
  rw [map_sub] at this
  simp [P] at this
  rw [this, smul_zero]

end Subst

theorem degree_eq_one {ι : Type v} (d : ι →₀ ℕ) (hd : d.degree = 1) :
    ∃ i, d = single i 1 := by
  classical
  have hne : d ≠ 0 := by rintro rfl
                         simp at hd
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra! hc
    exact hne $ ext hc
  have hi1 := hd ▸ Finsupp.le_degree i d
  have hle : single i 1 ≤ d := by
    rw [single_le_iff]
    omega
  have hsplit :=
    (tsub_add_cancel_of_le hle).symm
  have hdeg : d.degree = (d - single i 1).degree + 1 := by
    conv_lhs => rw [hsplit]
    rw [map_add, degree_single]
  have h0 : d - single i 1 = 0 := (degree_eq_zero_iff _).1 $ by omega
  use i
  rw [hsplit, h0, zero_add]

section Main

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}

def phi (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (k : ι → MvPowerSeries τ R) :
    ι → MvPowerSeries τ R :=
  fun j => G j - subst k (g j)

def seq (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (n : ℕ) :
    ι → MvPowerSeries τ R :=
  (phi G g)^[n] 0

def lim (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) : ι → MvPowerSeries τ R :=
  fun i d => coeff d $ seq G g (d.degree + 1) i

theorem seq_succ (G : ι → MvPowerSeries τ R) (g : ι → MvPowerSeries ι R) (n : ℕ) :
    seq G g (n + 1) = phi G g (seq G g n) :=
  Function.iterate_succ_apply' _ _ _

variable {G : ι → MvPowerSeries τ R} {g : ι → MvPowerSeries ι R}

theorem phi_low (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) {k : ι → MvPowerSeries τ R}
    (hk : ∀ i, Low 1 $ k i) (j : ι) : Low 1 $ phi G g k j :=
  low_sub (hG j) $ low_subst hk $ low_mono (by omega) $ hg j

theorem phi_sub (hg : ∀ j, Low 2 (g j)) {M : ℕ} {k k' : ι → MvPowerSeries τ R}
    (hk : ∀ i, Low 1 $ k i) (hk' : ∀ i, Low 1 $ k' i) (hkk : ∀ i, Low M $ k i - k' i) (j : ι) :
    Low (M + 1) $ phi G g k j - phi G g k' j := by
  have e : phi G g k j - phi G g k' j = subst k' (g j) - subst k (g j) := by
    simp only [phi]
    abel
  rw [e]
  refine low_subst_sub hk' hk (fun i => ?_) $ hg j
  have := low_neg $ hkk i
  rwa [neg_sub] at this

theorem seq_low (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n : ℕ) (i : ι) :
    Low 1 $ seq G g n i := by
  induction n generalizing i with
  | zero => exact low_of_zero _
  | succ n ih => rw [seq_succ]; exact phi_low hG hg ih i

theorem seq_step (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n : ℕ) (i : ι) :
    Low n $ seq G g (n + 1) i - seq G g n i := by
  induction n generalizing i with
  | zero => exact low_zero _
  | succ n ih =>
    have := phi_sub (G := G) hg (seq_low hG hg $ n + 1) (seq_low hG hg n) ih i
    rwa [← seq_succ, ← seq_succ] at this

theorem seq_stable (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n m : ℕ) (hnm : n ≤ m)
    (i : ι) : Low n $ seq G g m i - seq G g n i := by
  induction m, hnm using Nat.le_induction with
  | base => rw [sub_self]; exact low_of_zero _
  | succ m hnm ih =>
    have e : seq G g (m + 1) i - seq G g n i =
        (seq G g (m + 1) i - seq G g m i) + (seq G g m i - seq G g n i) := by abel
    rw [e]
    exact low_add (low_mono hnm $ seq_step hG hg m i) ih

theorem coeff_lim (d : τ →₀ ℕ) (i : ι) :
    coeff d (lim G g i) = coeff d (seq G g (d.degree + 1) i) :=
  rfl

theorem lim_close (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (n : ℕ) (i : ι) :
    Low n $ lim G g i - seq G g n i := by
  intro d hd
  have := seq_stable hG hg (d.degree + 1) n (by omega) i d $ by omega
  rw [map_sub, sub_eq_zero] at this
  rw [map_sub, coeff_lim, this, sub_self]

theorem lim_low (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (i : ι) :
    Low 1 $ lim G g i := by
  have := low_add (lim_close hG hg 1 i) $ seq_low hG hg 1 i
  rwa [sub_add_cancel] at this

theorem lim_fixed (hG : ∀ j, Low 1 (G j)) (hg : ∀ j, Low 2 (g j)) (j : ι) :
    phi G g (lim G g) j = lim G g j := by
  ext d
  have h1 := phi_sub (G := G) hg (lim_low hG hg) (seq_low hG hg _) (lim_close hG hg $ d.degree + 1) j d
    $ by omega
  have h2 := lim_close hG hg (d.degree + 2) j d $ by omega
  rw [← seq_succ] at h1
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2]

end Main

end Formalism.FG.SolveVAux

namespace Formalism.FG

open MvPowerSeries SolveVAux

theorem solve_exists_vector : Formalism.FG.SolveExistsV.{u, v, w} := by
  intro R _ ι _ _ τ _ f G hf hG
  classical
  obtain ⟨hf0, hf1⟩ := hf
  set g : ι → MvPowerSeries ι R := fun j => f j - X j with hgdef
  have hg : ∀ j, Low 2 $ g j := by
    intro j d hd
    simp [hgdef, map_sub]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hd with h0 | h1
    have : d = 0 := (degree_eq_zero_iff d).1 $ by omega
    subst this
    rw [coeff_zero_eq_constantCoeff_apply, hf0 j, coeff_X,
      if_neg fun h => (Finsupp.single_ne_zero.2 one_ne_zero) h.symm, sub_zero]
    obtain ⟨i, rfl⟩ := degree_eq_one d h1
    rw [hf1 j i, coeff_X]
    by_cases hij : i = j
    subst hij
    simp
    simp [hij, Finsupp.single_left_inj one_ne_zero]
  have hGl : ∀ j, Low 1 $ G j := fun j => (low_one_iff _).2 $ hG j
  refine ⟨lim G g, fun i => (low_one_iff _).1 $ lim_low hGl hg i, fun j => ?_⟩
  have hs := hasSubst_of_low $ lim_low hGl hg
  have hfix := lim_fixed hGl hg j
  simp [phi] at hfix
  have hfj : f j = g j + X j := by simp [hgdef]
  rw [hfj, subst_add hs, subst_X hs, ← hfix]
  abel

end Formalism.FG
end
section
open Formalism.G (IntegralMv)
namespace Formalism.HermitianLattices.ExpSeriesBivariate

open Finset

def expS {σ K : Type} [Field K] [Algebra ℚ K] (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst f $ PowerSeries.exp K

def InLam {σ K : Type} [NormedField K] [Algebra ℚ K] (f : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ IntegralMv (expS f)








def IntegralInverse : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type) [Fintype σ] [DecidableEq σ]
    (T : σ → MvPowerSeries σ K) (J' : Matrix σ σ K),
    (∀ i, MvPowerSeries.constantCoeff (T i) = 0) → (∀ i, IntegralMv $ T i) →
    (∀ i j, ‖J' i j‖ ≤ 1) →
    (Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single j 1) $ T i) * J' = 1 →
    ∃ X' : σ → MvPowerSeries σ K, (∀ i, MvPowerSeries.constantCoeff (X' i) = 0) ∧
      (∀ i, IntegralMv $ X' i) ∧ (∀ i, MvPowerSeries.subst X' (T i) = MvPowerSeries.X i) ∧
      ∀ i, MvPowerSeries.subst T (X' i) = MvPowerSeries.X i













open Classical in



open Classical in



open Classical in







open Complex in



def ee (t : ℝ) : ℂ := Complex.exp $ 2 * Real.pi * Complex.I * t






















end Formalism.HermitianLattices.ExpSeriesBivariate
end
section
namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition

open Finset Formalism.G Formalism.HermitianLattices.ExpSeriesBivariate

section Alg

variable {σ K : Type} [Field K] [Algebra ℚ K]

theorem exp_biv :
    expS (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      expS (MvPowerSeries.X 0) * expS (MvPowerSeries.X 1) := by
  ext e
  unfold expS
  rw [PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  simp only [PowerSeries.coeff_exp]
  rw [← map_natCast $ algebraMap ℚ K, ← map_mul, ← map_mul]
  congr 1
  have h' : (((e 0 + e 1).choose (e 0) : ℕ) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) =
      ((e 0 + e 1).factorial : ℚ) := by
    rw [Nat.choose_symm_add]
    exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial (e 0) $ e 1)
  have h0 : ((e 0).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h1 : ((e 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h2 : ((e 0 + e 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  field_simp
  linarith

theorem subst_expS {τ : Type} [Finite σ] (h : σ → MvPowerSeries τ K)
    (hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0) (f : MvPowerSeries σ K)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst h (expS f) = expS (MvPowerSeries.subst h f) := by
  have hs : MvPowerSeries.HasSubst h := MvPowerSeries.hasSubst_of_constantCoeff_zero hh
  have ha : MvPowerSeries.HasSubst fun _ => f :=
    PowerSeries.hasSubst_iff.mp $ PowerSeries.HasSubst.of_constantCoeff_zero hf
  unfold expS
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha hs]

theorem expS_add (f g : MvPowerSeries σ K) (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : expS (f + g) = expS f * expS g := by
  classical
  let h := ![f, g]
  have hh : ∀ i, MvPowerSeries.constantCoeff (h i) = 0 := by
    intro i
    fin_cases i
    exact hf
    exact hg
  have hS : MvPowerSeries.HasSubst h := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hh
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hh
    | exact ⟨fun s => by rw [hh s]; exact IsNilpotent.zero,
        by rw [Filter.cofinite_eq_bot]
           exact Filter.tendsto_bot⟩
  have e2 : ∀ i, MvPowerSeries.subst h (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = h i :=
    fun i => MvPowerSeries.subst_X hS i
  have e1 : MvPowerSeries.subst h (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      f + g := by
    rw [MvPowerSeries.subst_add hS, e2, e2]
    rfl
  have h0 : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  rw [← e1, ← subst_expS h hh _ $ by rw [map_add, h0, h0, add_zero], exp_biv,
    MvPowerSeries.subst_mul hS, subst_expS h hh _ $ h0 0, subst_expS h hh _ $ h0 1, e2, e2]
  rfl

def Low (m : ℕ) (x : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < m → MvPowerSeries.coeff d x = 0

theorem Low.mul {m k : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) $ x * y := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  replace hp : p.1 + p.2 = d := by
    first
    | exact _root_.Finset.mem_antidiagonal.1 hp
    | exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by
    rw [← hp]
    first
    | exact (map_add Finsupp.degree p.1 p.2).symm
    | exact (Finsupp.degree_add p.1 p.2).symm
    | (rw [Finsupp.degree_eq_weight_one, Finsupp.degree_eq_weight_one,
        Finsupp.degree_eq_weight_one]; exact (map_add _ _ _).symm)
    | (simp [Finsupp.degree]; exact (Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl).symm)
  by_cases h1 : p.1.degree < m
  rw [hx p.1 h1, zero_mul]
  rw [hy p.2 $ by omega, mul_zero]




theorem expS_zero : expS (0 : MvPowerSeries σ K) = 1 := by
  unfold expS
  ext e
  rw [PowerSeries.coeff_subst $ PowerSeries.HasSubst.of_constantCoeff_zero $ map_zero _, finsum_eq_single _ 0]
  simp
  intro d hd
  simp [zero_pow hd]

theorem constantCoeff_expS (f : MvPowerSeries σ K) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (expS f) = 1 := by
  unfold expS
  rw [PowerSeries.constantCoeff_subst $ PowerSeries.HasSubst.of_constantCoeff_zero hf, finsum_eq_single _ 0]
  simp
  intro d hd
  simp [hf, zero_pow hd]

end Alg

section Normed

variable {σ K : Type} [NormedField K]

theorem integral_of_mul_eq_one [IsUltrametricDist K] {u v : MvPowerSeries σ K} (huv : u * v = 1)
    (hu0 : MvPowerSeries.constantCoeff u = 1) (hu : IntegralMv u) : IntegralMv v := by
  classical
  have key : ∀ n, ∀ d, d.degree = n → ‖MvPowerSeries.coeff d v‖ ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro d hd
      have hmul := congrArg (MvPowerSeries.coeff d) huv
      rw [MvPowerSeries.coeff_mul] at hmul
      have hmem : ((0 : σ →₀ ℕ), d) ∈ Finset.HasAntidiagonal.antidiagonal d :=
        Finset.HasAntidiagonal.mem_antidiagonal.2 $ zero_add d
      rw [← Finset.add_sum_erase _ _ hmem] at hmul
      have hc : MvPowerSeries.coeff (0 : σ →₀ ℕ) u = 1 := by
        first
        | rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hu0
        | simpa using hu0
      simp only [hc, one_mul] at hmul
      rw [eq_sub_of_add_eq hmul]
      have hsub : ∀ a b : K, ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
        intro a b
        first
        | (rw [sub_eq_add_neg]
           have h1 := IsUltrametricDist.norm_add_le_max a $ -b
           rwa [norm_neg] at h1)
        | (have h1 := IsUltrametricDist.dist_triangle_max a 0 b
           simpa [dist_eq_norm] using h1)
      refine (hsub _ _).trans $ max_le ?_ ?_
      rw [MvPowerSeries.coeff_one]
      split_ifs <;> simp
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      intro p hp
      rw [Finset.mem_erase] at hp
      have hp2 : p.1 + p.2 = d := by
        first
        | exact _root_.Finset.mem_antidiagonal.1 hp.2
        | exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp.2
      have hp1 : p.1 ≠ 0 := by
        intro h0
        apply hp.1
        rw [h0, zero_add] at hp2
        exact Prod.ext h0 hp2
      have hdeg : p.1.degree + p.2.degree = d.degree := by
        rw [← hp2]
        first
        | exact (map_add Finsupp.degree p.1 p.2).symm
        | exact (Finsupp.degree_add p.1 p.2).symm
      have hpos : 0 < p.1.degree := by
        rcases Nat.eq_zero_or_pos p.1.degree with h | h
        exfalso
        apply hp1
        first
        | exact (Finsupp.degree_eq_zero_iff p.1).mp h
        | exact Finsupp.degree_eq_zero_iff.mp h
        exact h
      rw [norm_mul]
      apply (mul_le_mul (hu p.1) (ih p.2.degree (by omega) p.2 rfl) (norm_nonneg _)
        zero_le_one).trans
      norm_num
  intro d
  exact key _ d rfl

def CT (F : ℕ → MvPowerSeries σ K) (f : MvPowerSeries σ K) : Prop :=
  ∀ n, Filter.Tendsto (fun k => MvPowerSeries.coeff n $ F k) Filter.atTop
    $ nhds $ MvPowerSeries.coeff n f

theorem CT.mul {F G : ℕ → MvPowerSeries σ K} {f g : MvPowerSeries σ K} (hF : CT F f)
    (hG : CT G g) : CT (fun k => F k * G k) $ f * g := by
  classical
  intro n
  simp [MvPowerSeries.coeff_mul]
  apply tendsto_finset_sum
  intro p _
  exact (hF p.1).mul $ hG p.2

theorem CT.pow {F : ℕ → MvPowerSeries σ K} {f : MvPowerSeries σ K} (hF : CT F f) (n : ℕ) :
    CT (fun k => F k ^ n) $ f ^ n := by
  induction n with
  | zero =>
    intro d
    simp only [pow_zero]
    exact tendsto_const_nhds
  | succ n ih =>
    simp only [pow_succ]
    exact ih.mul hF

theorem inLam_zero [IsUltrametricDist K] [Algebra ℚ K] : InLam (0 : MvPowerSeries σ K) := by
  use map_zero _
  classical
  rw [expS_zero]
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem inLam_add [IsUltrametricDist K] [Algebra ℚ K] {f g : MvPowerSeries σ K} (hf : InLam f)
    (hg : InLam g) : InLam $ f + g := by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  rw [expS_add f g hf.1 hg.1]
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro p _
  rw [norm_mul]
  apply (mul_le_mul (hf.2 p.1) (hg.2 p.2) (norm_nonneg _) zero_le_one).trans
  norm_num
theorem inLam_neg [IsUltrametricDist K] [Algebra ℚ K] {f : MvPowerSeries σ K} (hf : InLam f) :
    InLam $ -f := by
  refine ⟨by simp [hf.1], ?_⟩
  exact integral_of_mul_eq_one (by
      rw [← expS_add f (-f) hf.1 $ by simp [hf.1]]
      first
      | rw [add_neg_cancel, expS_zero]
      | rw [add_right_neg, expS_zero]
      | simp [expS_zero]) (constantCoeff_expS f hf.1) hf.2

theorem inLam_nsmul [IsUltrametricDist K] [Algebra ℚ K] {f : MvPowerSeries σ K} (hf : InLam f)
    (m : ℕ) : InLam $ m • f := by
  induction m with
  | zero => simpa using (inLam_zero : InLam (0 : MvPowerSeries σ K))
  | succ m ih =>
    rw [succ_nsmul]
    exact inLam_add ih hf

end Normed

end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition

namespace Formalism.HermitianLattices.ExpSeriesBivariate

open ExpSeriesAddition

end Formalism.HermitianLattices.ExpSeriesBivariate
end
section
open Formalism.FG (IsIdMod2 inverse_integral_vector solve_exists_vector subst_injective_vector)
open Formalism.G (IntegralMv)
open MvPowerSeries (coe_substAlgHom coeff coeff_C_mul hasSubst_of_constantCoeff_zero subst)
namespace Formalism.HermitianLattices.ExpSeriesBivariate

open Finset

private theorem g3cw2_lin_integral {K : Type} [NormedField K] [IsUltrametricDist K] {σ τ : Type}
    [Fintype σ] (a : σ → K) (ha : ∀ k, ‖a k‖ ≤ 1) (g : σ → MvPowerSeries τ K)
    (hg : ∀ k, IntegralMv $ g k) :
    IntegralMv (∑ k, MvPowerSeries.C (a k) * g k) := by
  intro d
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [coeff_C_mul, norm_mul]
  exact mul_le_one₀ (ha k) (norm_nonneg _) $ hg k d

private theorem g3cw2_subst_lin {K : Type} [Field K] {σ ρ τ : Type} [Fintype σ]
    (a : σ → K) (g : σ → MvPowerSeries ρ K) (h : ρ → MvPowerSeries τ K)
    (hh : MvPowerSeries.HasSubst h) :
    subst h (∑ k, MvPowerSeries.C (a k) * g k) =
      ∑ k, MvPowerSeries.C (a k) * subst h (g k) := by
  rw [← coe_substAlgHom (R := K) hh, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, coe_substAlgHom, MvPowerSeries.subst_C]

private theorem g3cw2_inv_lin {K : Type} [Field K] {σ τ : Type} [Fintype σ] [DecidableEq σ]
    (J J' : Matrix σ σ K) (hJ : J * J' = 1) (a : σ → MvPowerSeries τ K) (i : σ) :
    ∑ j, MvPowerSeries.C (J i j) * ∑ k, MvPowerSeries.C (J' j k) * a k = a i := by
  calc ∑ j, MvPowerSeries.C (J i j) * ∑ k, MvPowerSeries.C (J' j k) * a k
      = ∑ j, ∑ k, MvPowerSeries.C (J i j * J' j k) * a k := by
        simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
    _ = ∑ k, ∑ j, MvPowerSeries.C (J i j * J' j k) * a k := Finset.sum_comm
    _ = ∑ k, MvPowerSeries.C ((J * J') i k) * a k := by
        simp_rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
    _ = a i := by
        rw [hJ]
        simp [Matrix.one_apply]

theorem integralInverse_statement : IntegralInverse := by
  intro K _ _ σ _ _ T J' hT0 hTI hJ'I hLJ
  set L : Matrix σ σ K := Matrix.of fun i j => coeff (Finsupp.single j 1) (T i) with hL
  have hTs := hasSubst_of_constantCoeff_zero hT0

  let f : σ → MvPowerSeries σ K := fun j => ∑ i, MvPowerSeries.C (J' j i) * T i
  have hf0 : ∀ j, MvPowerSeries.constantCoeff (f j) = 0 := by
    intro j
    simp [f, map_sum, hT0]
  have hfI : ∀ j, IntegralMv $ f j := fun j => g3cw2_lin_integral _ (hJ'I j) _ hTI
  have hfId : IsIdMod2 f := by
    refine ⟨hf0, fun j m => ?_⟩
    have h1 : coeff (Finsupp.single m 1) (f j) = (J' * L) j m := by
      simp [f, map_sum, coeff_C_mul, Matrix.mul_apply, hL, Matrix.of_apply]
    rw [h1, (Matrix.mul_eq_one_comm_of_card_eq σ σ K rfl).mp hLJ, Matrix.one_apply]
    simp [eq_comm]
  have hTf : ∀ i, T i = ∑ j, MvPowerSeries.C (L i j) * f j := fun i => (g3cw2_inv_lin L J' hLJ T i).symm
  have hXI : ∀ k, IntegralMv (MvPowerSeries.X k : MvPowerSeries σ K) := by
    intro k d
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  let G : σ → MvPowerSeries σ K := fun j => ∑ k, MvPowerSeries.C (J' j k) * MvPowerSeries.X k
  obtain ⟨X', hX'0, hX'⟩ := solve_exists_vector K σ σ f G hfId $ by
      intro j
      simp [G, map_sum]
  have hX's := hasSubst_of_constantCoeff_zero hX'0
  refine ⟨X', hX'0, by
      refine inverse_integral_vector K σ σ (fun D => ∀ j, IntegralMv $ D j) f hfId ?_ ?_ ?_ X' hX'0 ?_
      intro a b ha hb j d
      rw [Pi.sub_apply, map_sub, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        $ max_le (ha j d) (by rw [norm_neg]; exact hb j d)
      intro P hP0 hPI j
      exact Formalism.FG.IntegralSubstitution.integralSubstV (f j) P (hfI j) hP0 hPI
      intro D hD N _ _ j d _
      exact hD j d
      intro j
      show IntegralMv $ subst X' $ f j
      rw [hX' j]
      exact g3cw2_lin_integral _ (hJ'I j) _ hXI, fun i => ?_, fun i => ?_⟩
  rw [hTf i, g3cw2_subst_lin _ f X' hX's]
  simp_rw [hX']
  exact g3cw2_inv_lin L J' hLJ MvPowerSeries.X i
  ·
    have key := subst_injective_vector K σ σ f (fun i => subst T $ X' i)
      MvPowerSeries.X hfId
      (fun i => MvPowerSeries.constantCoeff_subst_eq_zero hTs hT0 $ hX'0 i)
      MvPowerSeries.constantCoeff_X fun j => ?_
    exact congrFun key i
    rw [← MvPowerSeries.subst_comp_subst_apply hX's hTs, hX' j]
    rw [MvPowerSeries.subst_self, g3cw2_subst_lin _ _ T hTs]
    simp_rw [MvPowerSeries.subst_X hTs]
    rfl

end Formalism.HermitianLattices.ExpSeriesBivariate
end
section
namespace Formalism.L2.Th1.B.Sim

open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition

variable {K ι : Type} [NormedField K] [CharZero K]

theorem simeq_iff (f g : MvPowerSeries ι K) : Simeq f g ↔ InLam (f - g) := Iff.rfl

theorem inLam_zsmul [IsUltrametricDist K] {f : MvPowerSeries ι K} (hf : InLam f) (n : ℤ) :
    InLam $ n • f := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  rw [natCast_zsmul]
  exact inLam_nsmul hf m
  rw [neg_zsmul, natCast_zsmul]
  exact inLam_neg $ inLam_nsmul hf m



theorem inLam_fLog {g : MvPowerSeries ι K} (hg0 : MvPowerSeries.constantCoeff g = 1)
    (hg : Integral g) : InLam $ fLog g := by
  use constantCoeff_fLog hg0
  have h : Integral $ fExp $ fLog g := by rw [fExp_fLog hg0]
                                          exact hg
  exact h

end Formalism.L2.Th1.B.Sim

namespace Formalism.L2.Th1.B.Sim

open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_add inLam_neg)

theorem simeq_integral_series : SimeqInt := by
  intro K ι _ _ _ f g f' g' h h'
  rw [simeq_iff] at h h'
  refine ⟨?_, ?_, fun n => ?_⟩
  rw [simeq_iff]
  have e : f - f' - (g - g') = (f - g) + -(f' - g') := by ring
  rw [e]
  exact inLam_add h $ inLam_neg h'
  rw [simeq_iff]
  have e : -f - -g = -(f - g) := by ring
  rw [e]
  exact inLam_neg h
  rw [simeq_iff]
  have e : (n : MvPowerSeries ι K) * f - n * g = n • (f - g) := by
    rw [zsmul_eq_mul]
    ring
  rw [e]
  exact inLam_zsmul h n


theorem simeq_formal_log : SimeqLog := by
  intro K ι _ _ _ g hg0 hg
  have h := inLam_fLog hg0 hg
  constructor
  rwa [simeq_iff, sub_zero]
  rw [simeq_iff, sub_zero]
  exact inLam_neg h

end Formalism.L2.Th1.B.Sim
end
section
open scoped BigOperators
open Finset (mul_sum sum_congr sum_subset)
open Nat (add_sub_cancel_left le_add_right)
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.FG.SolveVAux


theorem low_sum {K ι α : Type} [Field K] (s : Finset α) (f : α → MvPowerSeries ι K) (N : ℕ)
    (h : ∀ a ∈ s, Low N $ f a) : Low N (∑ a ∈ s, f a) := by
  intro d hd
  rw [map_sum]
  exact Finset.sum_eq_zero fun a ha => h a ha d hd











theorem sum_triangle {A : Type} [AddCommMonoid A] (g : ℕ → ℕ → A) (M : ℕ) :
    ∑ i ∈ range M, ∑ b ∈ range (i + 1), g b (i - b) =
      ∑ b ∈ range M, ∑ a ∈ range (M - b), g b a := by
  rw [Finset.sum_comm' (t' := range M) (s' := fun b => Finset.Ico b M)
    (by intro i b; simp [mem_range, Finset.mem_Ico]; omega)]
  refine sum_congr rfl fun b _ => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  exact sum_congr rfl fun a _ => by rw [add_sub_cancel_left]



def expSum {K ι : Type} [Field K] (f : MvPowerSeries ι K) (M : ℕ) : MvPowerSeries ι K :=
  ∑ k ∈ range M, MvPowerSeries.C ((k.factorial : K)⁻¹) * f ^ k

theorem low_mvExp_sub {K ι : Type} [NormedField K] [CharZero K] {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) (M : ℕ) : Low M $ mvExp f - expSum f M := by
  intro d hd
  rw [map_sub, coeff_mvExp hf, expSum, map_sum, sub_eq_zero]
  simp [MvPowerSeries.coeff_C_mul]
  refine sum_subset (Finset.range_subset_range.2 $ by omega) fun k _ hk => ?_
  rw [low_pow ((low_one_iff _).2 hf) k d (by simp [mem_range] at hk; omega), mul_zero]

theorem eq_of_low {K ι : Type} [Field K] {f g : MvPowerSeries ι K} (h : ∀ M, Low M (f - g)) :
    f = g := by
  ext d
  have := h (d.degree + 1) d $ by omega
  rwa [map_sub, sub_eq_zero] at this

theorem exp_term {K ι : Type} [Field K] [CharZero K] (a b : MvPowerSeries ι K) (i : ℕ) :
    MvPowerSeries.C ((i.factorial : K)⁻¹) * (a + b) ^ i =
      ∑ k ∈ range (i + 1), (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
        (MvPowerSeries.C (((i - k).factorial : K)⁻¹) * b ^ (i - k)) := by
  rw [add_pow, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  obtain ⟨l, rfl⟩ : ∃ l, i = k + l := ⟨i - k, by simp [mem_range] at hk; omega⟩
  have key : (MvPowerSeries.C (((k + l).factorial : K)⁻¹) : MvPowerSeries ι K) *
      (((k + l).choose k : ℕ) : MvPowerSeries ι K) =
      MvPowerSeries.C ((k.factorial : K)⁻¹) * MvPowerSeries.C ((l.factorial : K)⁻¹) := by
    rw [← map_natCast (MvPowerSeries.C : K →+* MvPowerSeries ι K), ← map_mul, ← map_mul]
    congr 1
    have h1 := Nat.choose_mul_factorial_mul_factorial $ le_add_right k l
    rw [add_sub_cancel_left] at h1
    have h2 : (((k + l).choose k : ℕ) : K) * (k.factorial : K) * (l.factorial : K) =
        ((k + l).factorial : K) := by exact_mod_cast h1
    have hc : (((k + l).choose k : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos $ le_add_right k l).ne'
    have hk0 : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
    have hl0 : (l.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 l.factorial_ne_zero
    rw [← h2]
    field_simp
  rw [add_sub_cancel_left]
  linear_combination (a ^ k * b ^ l) * key

theorem mvExp_add {K ι : Type} [NormedField K] [CharZero K] {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    mvExp (a + b) = mvExp a * mvExp b := by
  refine eq_of_low fun M => ?_
  have h3 : Low M $ expSum a M * expSum b M - expSum (a + b) M := by
    have e : expSum (a + b) M = ∑ k ∈ range M, ∑ l ∈ range (M - k),
        (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l) := by
      unfold expSum
      rw [sum_congr rfl fun i _ => exp_term a b i]
      exact sum_triangle (fun k l => (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l)) M
    rw [e]
    unfold expSum
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine low_sum _ _ _ fun k _ => ?_
    rw [mul_sum]
    intro d hd
    rw [map_sub, map_sum, map_sum, sub_eq_zero]
    symm
    refine sum_subset (Finset.range_subset_range.2 $ Nat.sub_le _ _) fun l _ hl => ?_
    have hkl : Low (k + l) $ (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l) := by
      simpa using low_mul (low_mul (low_zero $ MvPowerSeries.C $ (k.factorial : K)⁻¹) $ low_pow ((low_one_iff _).2 ha) k)
        $ low_mul (low_zero $ MvPowerSeries.C $ (l.factorial : K)⁻¹) $ low_pow ((low_one_iff _).2 hb) l
    apply hkl d
    simp [mem_range] at hl
    omega
  have e : mvExp (a + b) - mvExp a * mvExp b = (mvExp (a + b) - expSum (a + b) M) -
      ((mvExp a - expSum a M) * mvExp b + expSum a M * (mvExp b - expSum b M) +
        (expSum a M * expSum b M - expSum (a + b) M)) := by ring
  rw [e]
  refine low_sub (low_mvExp_sub (by rw [map_add, ha, hb, add_zero]) M) $ low_add (low_add ?_ ?_) h3
  simpa using low_mul (low_mvExp_sub ha M) $ low_zero $ mvExp b
  simpa using low_mul (low_zero $ expSum a M) $ low_mvExp_sub hb M















end Formalism.InvariantFactorPaths.G7
end
section
open scoped BigOperators
open MvPowerSeries (coeff coeff_map constantCoeff hasSubst_of_constantCoeff_zero map subst)
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace LogarithmEquivalence

noncomputable def ballRing (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K :=
  _root_.UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing K


theorem integral_iff_lift {K ι : Type} [NormedField K] [IsUltrametricDist K]
    {f : MvPowerSeries ι K} :
    Integral f ↔ ∃ f₀ : MvPowerSeries ι $ ballRing K, map (ballRing K).subtype f₀ = f := by
  constructor
  intro h
  let f₀ : MvPowerSeries ι $ ballRing K := fun n => ⟨coeff n f, h n⟩
  use f₀
  ext n
  exact (coeff_map _ _ _).trans rfl
  rintro ⟨f₀, rfl⟩ n
  rw [coeff_map]
  exact (coeff n f₀).2

theorem integral_mul' {K ι : Type} [NormedField K] [IsUltrametricDist K] {f g : MvPowerSeries ι K}
    (hf : Integral f) (hg : Integral g) : Integral $ f * g := by
  obtain ⟨f₀, rfl⟩ := integral_iff_lift.1 hf
  obtain ⟨g₀, rfl⟩ := integral_iff_lift.1 hg
  exact integral_iff_lift.2 ⟨f₀ * g₀, map_mul _ _ _⟩

theorem integral_one' {K ι : Type} [NormedField K] [IsUltrametricDist K] :
    Integral (1 : MvPowerSeries ι K) :=
  integral_iff_lift.2 ⟨1, map_one _⟩

theorem constantCoeff_lift {K ι : Type} [NormedField K] [IsUltrametricDist K]
    {f₀ : MvPowerSeries ι $ ballRing K} {c : ballRing K}
    (h : constantCoeff (map (ballRing K).subtype f₀) = c) :
    constantCoeff f₀ = c := by
  rw [MvPowerSeries.constantCoeff_map] at h
  exact Subtype.ext h

theorem integral_subst' {K ι κ : Type} [Finite ι] [NormedField K] [IsUltrametricDist K]
    {f : MvPowerSeries ι K} {φ : ι → MvPowerSeries κ K}
    (h0 : ∀ i, constantCoeff (φ i) = 0) (hφ : ∀ i, Integral $ φ i)
    (hf : Integral f) : Integral $ subst φ f := by
  obtain ⟨f₀, rfl⟩ := integral_iff_lift.1 hf
  choose φ₀ hφ₀ using fun i => integral_iff_lift.1 $ hφ i
  refine integral_iff_lift.2 ⟨subst φ₀ f₀, ?_⟩
  rw [MvPowerSeries.map_subst $ hasSubst_of_constantCoeff_zero fun i => constantCoeff_lift (c := 0) (by rw [hφ₀ i, h0 i]; rfl)]
  congr 1
  funext i
  exact hφ₀ i

theorem integral_of_mul_eq_one {K ι : Type} [NormedField K] [IsUltrametricDist K]
    {u v : MvPowerSeries ι K} (hu : Integral u) (h1 : constantCoeff u = 1)
    (huv : v * u = 1) : Integral v := by
  obtain ⟨u₀, rfl⟩ := integral_iff_lift.1 hu
  obtain ⟨w, hw⟩ := (MvPowerSeries.isUnit_iff_constantCoeff.2 (by rw [constantCoeff_lift (c := 1) (by rw [h1]; rfl)]; exact isUnit_one)).exists_right_inv
  have e : v = map (ballRing K).subtype w := by
    calc v = v * (map (ballRing K).subtype u₀ *
          map (ballRing K).subtype w) := by rw [← map_mul, hw, map_one, mul_one]
      _ = map (ballRing K).subtype w := by rw [← mul_assoc, huv, one_mul]
  rw [e]
  exact integral_iff_lift.2 ⟨w, rfl⟩

theorem mvExp_zero' {K ι : Type} [NormedField K] [CharZero K] :
    mvExp (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_mvExp $ map_zero _, Finset.sum_eq_single 0]
  simp
  intro k _ hk
  rw [zero_pow hk, map_zero, mul_zero]
  intro h
  exact absurd (mem_range.2 $ Nat.succ_pos _) h

theorem constantCoeff_mvExp' {K ι : Type} [NormedField K] [CharZero K] {f : MvPowerSeries ι K}
    (hf : constantCoeff f = 0) : constantCoeff (mvExp f) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mvExp hf]
  simp

theorem subst_mvExp' {K ι κ : Type} [NormedField K] [CharZero K] {a : ι → MvPowerSeries κ K}
    (hs : MvPowerSeries.HasSubst a) {f : MvPowerSeries ι K}
    (hf : constantCoeff f = 0) :
    subst a (mvExp f) = mvExp (subst a f) := by
  unfold mvExp
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const hs]

theorem exp_integral_add {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {a b : MvPowerSeries ι K}
    (ha : constantCoeff a = 0 ∧ Integral (mvExp a))
    (hb : constantCoeff b = 0 ∧ Integral (mvExp b)) :
    constantCoeff (a + b) = 0 ∧ Integral (mvExp $ a + b) := by
  refine ⟨by rw [map_add, ha.1, hb.1, add_zero], ?_⟩
  rw [mvExp_add ha.1 hb.1]
  exact integral_mul' ha.2 hb.2

theorem simeqRules : SimeqRules := by
  intro K ι _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  intro f
  unfold Simeq
  rw [sub_self, mvExp_zero']
  constructor
  exact map_zero _
  exact integral_one'
  intro f g h
  unfold Simeq at h ⊢
  have e : g - f = -(f - g) := by ring
  have h0 : constantCoeff (-(f - g)) = 0 := by rw [map_neg, h.1, neg_zero]
  rw [e]
  refine ⟨h0, integral_of_mul_eq_one h.2 (constantCoeff_mvExp' h.1) ?_⟩
  rw [← mvExp_add h0 h.1, neg_add_cancel, mvExp_zero']
  intro f g h h1 h2
  unfold Simeq at h1 h2 ⊢
  have e : f - h = (f - g) + (g - h) := by ring
  rw [e]
  exact exp_integral_add h1 h2
  intro f g f' g' h1 h2
  unfold Simeq at h1 h2 ⊢
  have e : f + f' - (g + g') = (f - g) + (f' - g') := by ring
  rw [e]
  exact exp_integral_add h1 h2
  intro κ _ f g φ h0 hφ h
  unfold Simeq at h ⊢
  have hs := hasSubst_of_constantCoeff_zero h0
  rw [← MvPowerSeries.subst_sub hs, ← subst_mvExp' hs h.1]
  constructor
  exact MvPowerSeries.constantCoeff_subst_eq_zero hs h0 h.1
  exact integral_subst' h0 hφ h.2
end LogarithmEquivalence

theorem equivalence_rules : SimeqRules := LogarithmEquivalence.simeqRules




end Formalism.InvariantFactorPaths.G7
end
section
open PowerSeries (subst_comp_subst_apply subst_zero_of_constantCoeff_zero)
namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7
open Formalism.G.LogP

section Alg

variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem subst_at_variable_one_eq (f : PowerSeries K) (x : Fin 2) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [psubst_subst f (by simp) hb, MvPowerSeries.subst_X hb]

theorem constantCoeff_subst_two_variables (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![U, V] F) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hs2 hU hV)
    (fun i => by fin_cases i <;> simpa) hF

theorem constantCoeff_subst_one_variable (g : PowerSeries K) (hg : PowerSeries.constantCoeff g = 0)
    (U : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst U g) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hU g hg

theorem cube_cob_subst (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f - PowerSeries.subst U f -
        PowerSeries.subst V f := by
  have hb := hs2 hU hV
  unfold cob
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hb,
    psubst_subst f hF hb, subst_at_variable_one_eq f 0 hb, subst_at_variable_one_eq f 1 hb]
  rfl

theorem cube_par_subst (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (i f : PowerSeries K) (hi : PowerSeries.constantCoeff i = 0) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (par F i f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f +
        PowerSeries.subst (MvPowerSeries.subst ![U, PowerSeries.subst V i] F) f -
        2 * PowerSeries.subst U f - 2 * PowerSeries.subst V f := by
  have hb := hs2 hU hV
  have h1 : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0 := constantCoeff_subst_one_variable i hi _ $ by simp
  have hFI : MvPowerSeries.constantCoeff (FI F i) = 0 := constantCoeff_subst_two_variables F hF _ _ (by simp) h1
  unfold par
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, map_add, map_mul, map_mul, map_ofNat,
    MvPowerSeries.coe_substAlgHom hb, psubst_subst f hF hb, psubst_subst f hFI hb,
    subst_at_variable_one_eq f 0 hb, subst_at_variable_one_eq f 1 hb]
  unfold FI
  rw [subst2_subst F (by simp) h1 hb, MvPowerSeries.subst_X hb, subst_at_variable_one_eq i 1 hb]
  rfl

theorem two_mul_C_inv_two : (2 : MvPowerSeries ι K) * MvPowerSeries.C (2 : K)⁻¹ = 1 := by
  rw [(map_ofNat MvPowerSeries.C 2).symm, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

end Alg

section Norm

variable {K : Type} [NormedField K] [CharZero K] {ι : Type}

theorem cube_log_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![U, V] F) l =
      PowerSeries.subst U l + PowerSeries.subst V l := by
  obtain ⟨hF, -, -, -, hc⟩ := h
  have e := cube_cob_subst F hF l U V hU hV
  rw [hc, subst_zero' $ hs2 hU hV] at e
  linear_combination -e

theorem cube_log_inv {l i : PowerSeries K} (hi : IsInv l i) (V : MvPowerSeries ι K)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    PowerSeries.subst (PowerSeries.subst V i) l = -PowerSeries.subst V l := by
  have hVs := PowerSeries.HasSubst.of_constantCoeff_zero hV
  rw [← subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hi.1) hVs,
    hi.2.2, ← PowerSeries.coe_substAlgHom hVs, map_neg]

theorem cube_log_half {l hf : PowerSeries K} (hh : IsHalf l hf) (V : MvPowerSeries ι K)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    2 * PowerSeries.subst (PowerSeries.subst V hf) l = PowerSeries.subst V l := by
  have hVs := PowerSeries.HasSubst.of_constantCoeff_zero hV
  rw [← subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hh.1) hVs,
    hh.2.2, PowerSeries.subst_mul hVs, PowerSeries.subst_C, ← mul_assoc, two_mul_C_inv_two, one_mul]

theorem cube_add_eq {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0)
    (e : PowerSeries.subst U l + PowerSeries.subst V l = PowerSeries.subst W l) :
    MvPowerSeries.subst ![U, V] F = W :=
  psubst_injective h.2.2.1 h.2.2.2.1 (constantCoeff_subst_two_variables F h.1 U V hU hV) hW
    $ (cube_log_add h U V hU hV).trans e

theorem cube_sub_eq {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0)
    (e : PowerSeries.subst U l - PowerSeries.subst V l = PowerSeries.subst W l) :
    MvPowerSeries.subst ![U, PowerSeries.subst V i] F = W :=
  cube_add_eq h U _ W hU (constantCoeff_subst_one_variable i hi.1 V hV) hW (by rw [cube_log_inv hi V hV, ← e]; ring)

theorem cube_identity {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (f : PowerSeries K) (hf0 : PowerSeries.constantCoeff f = 0)
    (x0 x1 x2 A B C : MvPowerSeries ι K)
    (h0 : MvPowerSeries.constantCoeff x0 = 0) (h1 : MvPowerSeries.constantCoeff x1 = 0)
    (h2 : MvPowerSeries.constantCoeff x2 = 0) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hC : MvPowerSeries.constantCoeff C = 0)
    (eA : PowerSeries.subst A l = PowerSeries.subst x0 l + PowerSeries.subst B l)
    (eB : 2 * PowerSeries.subst B l = PowerSeries.subst x1 l + PowerSeries.subst x2 l)
    (eC : 2 * PowerSeries.subst C l = PowerSeries.subst x1 l - PowerSeries.subst x2 l) :
    MvPowerSeries.subst ![A, B] (par F i f) - MvPowerSeries.subst ![A, C] (par F i f) +
        MvPowerSeries.subst ![B, C] (par F i f) - MvPowerSeries.subst ![B, B] (par F i f) =
      PowerSeries.subst (MvPowerSeries.subst ![MvPowerSeries.subst ![x0, x1] F, x2] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x0, x1] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x0, x2] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x1, x2] F) f +
        PowerSeries.subst x0 f + PowerSeries.subst x1 f + PowerSeries.subst x2 f := by
  have c01 := constantCoeff_subst_two_variables F h.1 x0 x1 h0 h1
  have l01 := cube_log_add h x0 x1 h0 h1
  have l012 := cube_log_add h _ x2 c01 h2
  have fz : PowerSeries.subst (0 : MvPowerSeries ι K) f = 0 :=
    subst_zero_of_constantCoeff_zero hf0
  have e2 : MvPowerSeries.subst ![A, PowerSeries.subst B i] F = x0 :=
    cube_sub_eq h hi A B _ hA hB h0 $ by linear_combination eA
  have hc := two_mul_C_inv_two (K := K) (ι := ι)
  have sBC : PowerSeries.subst B l + PowerSeries.subst C l = PowerSeries.subst x1 l := by
    linear_combination (MvPowerSeries.C (2 : K)⁻¹) * eB + (MvPowerSeries.C (2 : K)⁻¹) * eC -
      (PowerSeries.subst B l + PowerSeries.subst C l - PowerSeries.subst x1 l) * hc
  have dBC : PowerSeries.subst B l - PowerSeries.subst C l = PowerSeries.subst x2 l := by
    linear_combination (MvPowerSeries.C (2 : K)⁻¹) * eB - (MvPowerSeries.C (2 : K)⁻¹) * eC -
      (PowerSeries.subst B l - PowerSeries.subst C l - PowerSeries.subst x2 l) * hc
  have e3 := cube_add_eq h A C _ hA hC c01 (by rw [l01]; linear_combination eA + sBC)
  have e4 := cube_sub_eq h hi A C _ hA hC (constantCoeff_subst_two_variables F h.1 x0 x2 h0 h2) (by rw [cube_log_add h x0 x2 h0 h2]; linear_combination eA + dBC)
  have e5 := cube_add_eq h B C _ hB hC h1 sBC
  have e6 : MvPowerSeries.subst ![B, PowerSeries.subst C i] F = x2 :=
    cube_sub_eq h hi B C _ hB hC h2 dBC
  have e8 : MvPowerSeries.subst ![B, PowerSeries.subst B i] F = 0 :=
    cube_sub_eq h hi B B _ hB hB (by simp) (by rw [subst_zero_of_constantCoeff_zero h.2.2.1]; ring)
  rw [cube_par_subst F h.1 i f hi.1 A B hA hB, cube_par_subst F h.1 i f hi.1 A C hA hC,
    cube_par_subst F h.1 i f hi.1 B C hB hC, cube_par_subst F h.1 i f hi.1 B B hB hB,
    cube_add_eq h A B _ hA hB (constantCoeff_subst_two_variables F h.1 _ x2 c01 h2) (by rw [l012, l01]; linear_combination eA + eB), e2, e3, e4, e5, e6, cube_add_eq h B B _ hB hB (constantCoeff_subst_two_variables F h.1 x1 x2 h1 h2) (by rw [cube_log_add h x1 x2 h1 h2]; linear_combination eB), e8, fz]
  ring

theorem parallelogram_coboundary_three_vars (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    d1 F (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F,
          MvPowerSeries.X 2] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F) f +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) f +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) f +
        PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f := by
  unfold d1 in3
  rw [cube_cob_subst F hF f _ _ (constantCoeff_subst_two_variables F hF _ _ (by simp) $ by simp) $ by simp,
    cube_cob_subst F hF f _ _ (by simp) $ by simp, cube_cob_subst F hF f _ _ (by simp) $ by simp]
  ring

theorem cube_simeq_congr {f g f' g' : MvPowerSeries ι K} (h : f - g = f' - g')
    (hs : Simeq f g) : Simeq f' g' := by
  unfold Simeq at hs ⊢
  rwa [← h]

theorem integral_mvPowerSeries_X (x : ι) : Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem constantCoeff_eq_zero_of_parallelogram {F : MvPowerSeries (Fin 2) K} {l i f : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (hq : Simeq (par F i f) 0) : PowerSeries.constantCoeff f = 0 := by
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have e := Formalism.G.LogP.constantCoeff_subst_of_zero (par F i f)
    (b := ![(0 : MvPowerSeries (Fin 2) K), 0]) fun j => by fin_cases j <;> simp
  have hq0 : MvPowerSeries.constantCoeff (par F i f) = 0 := by simpa using hq.1
  rw [hq0, cube_par_subst F h.1 i f hi.1 0 0 h0 h0,
    cube_add_eq h 0 0 0 h0 h0 h0 (by rw [subst_zero_of_constantCoeff_zero h.2.2.1]; ring),
    cube_sub_eq h hi 0 0 0 h0 h0 h0 (by rw [subst_zero_of_constantCoeff_zero h.2.2.1]; ring),
    PowerSeries.subst_zero_eq_C_constantCoeff] at e
  have e' : PowerSeries.constantCoeff f + PowerSeries.constantCoeff f -
      2 * PowerSeries.constantCoeff f - 2 * PowerSeries.constantCoeff f = 0 := by
    have c2 : MvPowerSeries.constantCoeff (2 : MvPowerSeries (Fin 2) K) = 2 :=
      map_ofNat MvPowerSeries.constantCoeff 2
    simpa [c2] using e
  have e2 : (2 : K) * PowerSeries.constantCoeff f = 0 := by linear_combination -e'
  exact (mul_eq_zero.1 e2).resolve_left two_ne_zero

end Norm

section Ultra

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}

theorem integral_subst_two_variables {F : MvPowerSeries (Fin 2) K} (hF : Integral F) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0)
    (iU : Integral U) (iV : Integral V) : Integral $ MvPowerSeries.subst ![U, V] F :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun j => by fin_cases j <;> simpa)
    (fun j => by fin_cases j <;> simpa) hF

theorem integral_subst_one_variable {g : PowerSeries K} (hg : Integral (ι := Unit) g) (U : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (iU : Integral U) :
    Integral $ PowerSeries.subst U g :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (φ := fun _ => U) (fun _ => hU) (fun _ => iU) hg

theorem cube_simeq_subst2 {q : MvPowerSeries (Fin 2) K} (hq : Simeq q 0) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0)
    (iU : Integral U) (iV : Integral V) : Simeq (MvPowerSeries.subst ![U, V] q) 0 := by
  have e := (equivalence_rules K $ Fin 2).2.2.2.2 ι q 0 ![U, V] (fun j => by fin_cases j <;> simpa)
    (fun j => by fin_cases j <;> simpa) hq
  rwa [subst_zero' $ hs2 hU hV] at e


end Ultra

theorem Cube_of (hH : HalfExists) (hI : SimeqInt) : Cube := by
  intro K _ _ _ F l i f h hi h2 hq
  obtain ⟨hf, hh⟩ := hH K F l h h2
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have c2 : MvPowerSeries.constantCoeff (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 3)
  have i2 := integral_mvPowerSeries_X (K := K) (2 : Fin 3)

  obtain ⟨S, hS⟩ : ∃ S, S = MvPowerSeries.subst
    ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K),
    PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) i] F := ⟨_, rfl⟩
  have cN := constantCoeff_subst_one_variable i hi.1 _ c2
  have cS := hS ▸ constantCoeff_subst_two_variables F h.1 _ _ c1 c2
  have cD := hD ▸ constantCoeff_subst_two_variables F h.1 _ _ c1 cN
  have lS := hS ▸ cube_log_add h _ _ c1 c2
  have cB := constantCoeff_subst_one_variable hf hh.1 S cS
  have cC := constantCoeff_subst_one_variable hf hh.1 D cD
  have iB := integral_subst_one_variable hh.2.1 S cS (hS ▸ integral_subst_two_variables h.2.1 _ _ c1 c2 i1 i2)
  have iC := integral_subst_one_variable hh.2.1 D cD (hD ▸ integral_subst_two_variables h.2.1 _ _ c1 cN i1 (integral_subst_one_variable hi.2.1 _ c2 i2))
  have cA := constantCoeff_subst_two_variables F h.1 _ _ c0 cB
  have iA := integral_subst_two_variables h.2.1 _ _ c0 cB (integral_mvPowerSeries_X (K := K) (0 : Fin 3)) iB
  have key := cube_identity h hi f (constantCoeff_eq_zero_of_parallelogram h hi hq) (MvPowerSeries.X 0) (MvPowerSeries.X 1) (MvPowerSeries.X 2)
    _ _ _ c0 c1 c2 cA cB cC (cube_log_add h _ _ c0 cB)
    ((cube_log_half hh S cS).trans lS) ((cube_log_half hh D cD).trans (by rw [hD, cube_log_add h _ _ c1 cN, cube_log_inv hi _ c2]; ring))
  rw [parallelogram_coboundary_three_vars F h.1 f, ← key]
  have qAB := cube_simeq_subst2 hq _ _ cA cB iA iB
  have qAC := cube_simeq_subst2 hq _ _ cA cC iA iC
  have qBC := cube_simeq_subst2 hq _ _ cB cC iB iC
  have qBB := cube_simeq_subst2 hq _ _ cB cB iB iB
  have s1 := (hI K (Fin 3) _ _ _ _ qAB qAC).1
  have s2 := (equivalence_rules K (Fin 3)).2.2.2.1 _ _ _ _ s1 qBC
  have s3 := (hI K (Fin 3) _ _ _ _ s2 qBB).1
  exact cube_simeq_congr (by ring) s3




end Formalism.L2.Th1.B
end
section
open MvPowerSeries (HasSubst coe_substAlgHom coeff_rescale rescale_eq_subst subst_X)
namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7
open Formalism.G.LogP

theorem log_inj {K : Type} [Field K] {ι : Type} (l : PowerSeries K)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (h : PowerSeries.subst U l = PowerSeries.subst V l) :
    U = V :=
  psubst_injective h0 h1 hU hV h

section Alg

variable {K : Type} [Field K] {ι : Type}

theorem subst_at_variable_eq_subst (f : PowerSeries K) (x : Fin 2) {b : Fin 2 → MvPowerSeries ι K}
    (hb : HasSubst b) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [psubst_subst f (by simp) hb, subst_X hb]

theorem law_cob_subst (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f - PowerSeries.subst U f -
        PowerSeries.subst V f := by
  have hb := hs2 hU hV
  unfold cob
  rw [← coe_substAlgHom hb, map_sub, map_sub, coe_substAlgHom hb,
    psubst_subst f hF hb, subst_at_variable_eq_subst f 0 hb, subst_at_variable_eq_subst f 1 hb]
  rfl

theorem law_constantCoeff_subst2 (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![U, V] F) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hs2 hU hV)
    (fun i => by fin_cases i <;> simpa) hF

theorem law_coeff_axis0 (H : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) (hn : n 1 = 0) :
    MvPowerSeries.coeff n H = MvPowerSeries.coeff n
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H) := by
  have e : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] =
      (![1, 0] : Fin 2 → K) • MvPowerSeries.X := by
    funext s
    fin_cases s <;> simp
  rw [e, ← rescale_eq_subst, coeff_rescale,
    Finsupp.prod_fintype _ _ $ by simp]
  simp [Fin.prod_univ_two, hn]

theorem law_coeff_axis1 (H : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) (hn : n 0 = 0) :
    MvPowerSeries.coeff n H = MvPowerSeries.coeff n
      (MvPowerSeries.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] H) := by
  have e : ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] =
      (![0, 1] : Fin 2 → K) • MvPowerSeries.X := by
    funext s
    fin_cases s <;> simp
  rw [e, ← rescale_eq_subst, coeff_rescale,
    Finsupp.prod_fintype _ _ $ by simp]
  simp [Fin.prod_univ_two, hn]

end Alg

section Norm

variable {K : Type} [NormedField K] {ι : Type}

theorem law_subst {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![U, V] F) l =
      PowerSeries.subst U l + PowerSeries.subst V l := by
  obtain ⟨hF, -, -, -, hc⟩ := h
  have e := law_cob_subst F hF l U V hU hV
  rw [hc, Formalism.G.LogP.subst_zero' $ hs2 hU hV] at e
  linear_combination -e

theorem law_eq_of_log {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0)
    (e : PowerSeries.subst U l + PowerSeries.subst V l = PowerSeries.subst W l) :
    MvPowerSeries.subst ![U, V] F = W :=
  log_inj l h.2.2.1 h.2.2.2.1 _ _ (law_constantCoeff_subst2 F h.1 U V hU hV) hW
    $ (law_subst h U V hU hV).trans e

theorem law_subst_zero (l : PowerSeries K) (h0 : PowerSeries.constantCoeff l = 0) :
    PowerSeries.subst (0 : MvPowerSeries ι K) l = 0 :=
  PowerSeries.subst_zero_of_constantCoeff_zero h0

theorem law_right_zero {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0) :
    MvPowerSeries.subst ![U, 0] F = U :=
  law_eq_of_log h U 0 U hU (by simp) hU $ by rw [law_subst_zero l h.2.2.1, add_zero]

theorem law_left_zero {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (V : MvPowerSeries ι K) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![0, V] F = V :=
  law_eq_of_log h 0 V V (by simp) hV hV $ by rw [law_subst_zero l h.2.2.1, zero_add]

theorem law_comm {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] F = MvPowerSeries.subst ![V, U] F :=
  law_eq_of_log h U V _ hU hV (law_constantCoeff_subst2 F h.1 V U hV hU)
    $ by rw [law_subst h V U hV hU, add_comm]


end Norm

theorem coboundary_rules_hold : CobRules := by
  intro K _ _ _ F l f h hf
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h00 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  constructor
  intro n hn
  rcases hn with hn | hn
  rw [law_coeff_axis1 _ n hn, law_cob_subst F h.1 f _ _ h00 hX1, law_left_zero h _ hX1,
    law_subst_zero f hf]
  simp
  rw [law_coeff_axis0 _ n hn, law_cob_subst F h.1 f _ _ hX0 h00, law_right_zero h _ hX0,
    law_subst_zero f hf]
  simp
  unfold swap2
  rw [law_cob_subst F h.1 f _ _ hX1 hX0, law_comm h _ _ hX1 hX0, Formalism.G.LogP.subst_XX]
  unfold cob at1
  ring

section Ultra

variable {K : Type} [NormedField K]

theorem law_integral_X {ι : Type} (x : ι) : Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem law_c0X : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by
  have : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
  exact this


end Ultra


theorem law_coeff_one_subst {K : Type} [Field K] (l D : PowerSeries K)
    (hD : PowerSeries.constantCoeff D = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst D l : PowerSeries K) =
      PowerSeries.coeff 1 l * PowerSeries.coeff 1 D := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hD
  have key : ∀ g : PowerSeries K, PowerSeries.coeff 1 g =
      PowerSeries.constantCoeff (PowerSeries.derivative g) := by
    intro g
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  have hc : ∀ g, PowerSeries.constantCoeff (PowerSeries.subst D g : PowerSeries K) =
      PowerSeries.constantCoeff g := by
    intro g
    have e : g = PowerSeries.C (PowerSeries.constantCoeff g) +
        (g - PowerSeries.C (PowerSeries.constantCoeff g)) := by ring
    conv_lhs => rw [e]
    rw [PowerSeries.subst_add hs, map_add, PowerSeries.subst_C]
    have := PowerSeries.constantCoeff_subst_eq_zero (a := D) hD
      (g - PowerSeries.C (PowerSeries.constantCoeff g)) $ by simp
    erw [this, add_zero]
    exact MvPowerSeries.constantCoeff_C _
  rw [key, PowerSeries.derivative_subst hs, map_mul, hc, ← key, ← key]

theorem formal_halving_exists : HalfExists := by
  intro K _ _ _ F l h h2
  obtain ⟨hF, hFi, hl0, hl1, -⟩ := id h
  have hX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
  let D : PowerSeries K := MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), PowerSeries.X] F
  have hD0 : PowerSeries.constantCoeff D = 0 := law_constantCoeff_subst2 F hF _ _ hX hX
  have hD1 : PowerSeries.coeff 1 D = 2 := by
    have e := law_subst h (PowerSeries.X : PowerSeries K) PowerSeries.X hX hX
    rw [PowerSeries.X_subst l] at e
    have e' := congrArg (PowerSeries.coeff 1) e
    rw [law_coeff_one_subst l D hD0, map_add, hl1] at e'
    linear_combination e'
  obtain ⟨X', hX0, hXi, hXT, -⟩ := Formalism.HermitianLattices.ExpSeriesBivariate.integralInverse_statement K Unit (fun _ => D)
    (Matrix.of fun _ _ => (2 : K)⁻¹) (fun _ => hD0) (fun _ => Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun k => by fin_cases k <;> exact law_c0X) (fun k => by fin_cases k <;> exact law_integral_X ()) hFi)
    (fun _ _ => by rw [Matrix.of_apply, norm_inv, h2, inv_one])
    $ by
      ext i j
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.of_apply,
        Matrix.one_apply]
      have : MvPowerSeries.coeff (Finsupp.single (default : Unit) 1) D = 2 := hD1
      rw [this, mul_inv_cancel₀ two_ne_zero, if_pos trivial]
  have hsX : HasSubst X' := MvPowerSeries.hasSubst_of_constantCoeff_zero hX0
  let g : PowerSeries K := X' ()
  have hg0 := hX0 ()
  have e1 : MvPowerSeries.subst ![g, g] F = (PowerSeries.X : PowerSeries K) := by
    have := hXT ()
    rw [subst2_subst F hX hX hsX] at this
    have eg : MvPowerSeries.subst X' (PowerSeries.X : PowerSeries K) = g :=
      subst_X hsX ()
    rwa [eg] at this
  use g, hg0, hXi ()
  have e3 := law_subst h g g hg0 hg0
  rw [e1, PowerSeries.X_subst l] at e3
  have hC : (PowerSeries.C (2 : K)⁻¹ : PowerSeries K) * 2 = 1 := by
    have : (2 : PowerSeries K) = PowerSeries.C (2 : K) := (map_ofNat PowerSeries.C 2).symm
    rw [this, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  linear_combination (-(PowerSeries.C (2 : K)⁻¹ : PowerSeries K)) * e3 +
    (-(PowerSeries.subst g l : PowerSeries K)) * hC

section Diff

variable {K : Type} [NormedField K]






end Diff

end Formalism.L2.Th1.B
end
section
namespace Formalism.L2.Th1.B

theorem halfExists : HalfExists := by
  exact formal_halving_exists
theorem cobRules : CobRules := by
  exact coboundary_rules_hold
theorem simeqInt : SimeqInt := by
  exact Sim.simeq_integral_series
theorem simeqLog : SimeqLog := by
  exact Sim.simeq_formal_log
theorem phODef : PhODef := by
  exact Ph.logSigmaPullbackSpec
theorem parO : ParO := by
  exact ParO.ParO_of addSgStar phODef simeqLog
theorem cube : Cube := by
  exact Cube_of halfExists simeqInt

theorem f1O : LogSigmaPullbackCocycle := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2
  have hl := hF.2.2
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF $ (phODef K s2 P l hl.1 hl.2.1).1
  have hd := cube K F l i (phO s2 P l) hF hi h2 $ parO K g2 g3 s2 c0 P l i ep F hP hF hi hC
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩


end Formalism.L2.Th1.B
end
section
open PowerSeries


namespace Formalism.LT.InvIntP

open Formalism.G Formalism.G.LogCR

section Basic

variable {K : Type u} [NormedField K] {ι : Type v}

def Low (m : ℕ) (x : MvPowerSeries ι K) : Prop :=
  ∀ d : ι →₀ ℕ, d.degree < m → MvPowerSeries.coeff d x = 0

theorem Low.mono {m k : ℕ} {x : MvPowerSeries ι K} (h : Low m x) (hk : k ≤ m) : Low k x := by
  exact fun d hd => h d $ lt_of_lt_of_le hd hk

theorem Low.mul {m k : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low k y) :
    Low (m + k) $ x * y := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ab hab => ?_
  have hab' : ab.1 + ab.2 = d := by simpa using hab
  have hdeg : ab.1.degree + ab.2.degree = d.degree := by rw [← hab', map_add]
  by_cases h1 : ab.1.degree < m
  rw [hx _ h1, zero_mul]
  rw [hy _ $ by omega, mul_zero]

theorem Low.add {m : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low m y) :
    Low m $ x + y := by
  intro d hd
  rw [map_add, hx d hd, hy d hd, add_zero]

theorem Low.sub {m : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low m y) :
    Low m $ x - y := by
  intro d hd
  rw [map_sub, hx d hd, hy d hd, sub_zero]

theorem low_zero (x : MvPowerSeries ι K) : Low 0 x := by
  intro d hd
  exact absurd hd $ Nat.not_lt_zero _

theorem low_one {x : MvPowerSeries ι K} (hx : MvPowerSeries.constantCoeff x = 0) : Low 1 x := by
  intro d hd
  have h0 := (Finsupp.degree_eq_zero_iff d).1 $ by omega
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hx]

end Basic

section Ultra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

theorem integral_mul {A B : MvPowerSeries ι K} (hA : IntegralMv A) (hB : IntegralMv B) :
    IntegralMv $ A * B := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun ab _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _) (norm_nonneg _) $ hB _

theorem integral_one : IntegralMv (1 : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integral_pow {A : MvPowerSeries ι K} (hA : IntegralMv A) (n : ℕ) :
    IntegralMv $ A ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact integral_one
  | succ n ih =>
    rw [pow_succ]
    exact integral_mul ih hA

theorem integralSubst (f : PowerSeries K) (P : MvPowerSeries ι K)
    (hf : IntegralPS f) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    IntegralMv (f.subst P) := by
  intro e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hP0)]
  by_cases hfin : (Function.support fun n => PowerSeries.coeff n f • MvPowerSeries.coeff e (P ^ n)).Finite
  rw [finsum_eq_sum _ hfin]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
  rw [norm_smul]
  exact mul_le_one₀ (hf n) (norm_nonneg _) (integral_pow hP n e)
  rw [finsum_of_infinite_support hfin, norm_zero]
  exact zero_le_one

end Ultra

theorem coeff_expand_low {K : Type u} [NormedField K] {ι : Type v} (q : ℕ) (hq : q ≠ 0)
    (hq2 : 2 ≤ q) (σ : K →+* K) (D : MvPowerSeries ι K) (N : ℕ) (hN : 1 ≤ N)
    (hlow : ∀ d, d.degree < N → MvPowerSeries.coeff d D = 0)
    (d : ι →₀ ℕ) (hd : d.degree = N) :
    MvPowerSeries.coeff d (MvPowerSeries.expand q hq $ MvPowerSeries.map σ D) = 0 := by
  classical
  by_cases hall : ∀ i, q ∣ d i
  set m : ι →₀ ℕ := Finsupp.mapRange (fun k => k / q) (Nat.zero_div q) d with hm
  have hdm : d = q • m := by
    ext i
    simp [Finsupp.smul_apply, smul_eq_mul, hm, Finsupp.mapRange_apply]
    exact (Nat.mul_div_cancel' $ hall i).symm
  have hdeg : d.degree = q * m.degree := by rw [hdm, map_nsmul, smul_eq_mul]
  have hmlt : m.degree < N := by
    rcases Nat.eq_zero_or_pos m.degree with h0 | hpos
    omega
    nlinarith
  rw [hdm, MvPowerSeries.coeff_expand_smul, MvPowerSeries.coeff_map, hlow m hmlt, map_zero]
  push_neg at hall
  obtain ⟨i, hi⟩ := hall
  exact MvPowerSeries.coeff_expand_of_not_dvd q hq _ hi

theorem funEqLowCoeff {K : Type u} [NormedField K] {ι : Type v} (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K) (hq2 : 2 ≤ q) (D : MvPowerSeries ι K) (hD : IsFunEqTypeMv p q hq σ D)
    (N : ℕ) (hN : 1 ≤ N) (hlow : ∀ d, d.degree < N → MvPowerSeries.coeff d D = 0)
    (d : ι →₀ ℕ) (hd : d.degree = N) : ‖MvPowerSeries.coeff d D‖ ≤ 1 := by
  have h := hD d
  rwa [map_sub, map_smul, coeff_expand_low q hq hq2 σ D N hN hlow d hd, smul_zero, sub_zero] at h

section Inv

variable {K : Type u} [NormedField K] {ι : Type v}

def tail2 (f : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => coeff (n + 2) f

theorem decomp (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1) :
    f = X + X ^ 2 * tail2 f := by
  ext n
  rcases n with _ | _ | n <;>
    simp [tail2, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X, h0, h1]

theorem subst_eq (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    {a : MvPowerSeries ι K} (ha0 : MvPowerSeries.constantCoeff a = 0) :
    f.subst a = a + a ^ 2 * (tail2 f).subst a := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  conv_lhs => rw [decomp f h0 h1]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

theorem agree_psubst [Finite ι] (g : PowerSeries K) {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Agree N (g.subst a) $ g.subst b := by
  exact Agree.subst (f := g) (f' := g) (a := fun _ => a) (a' := fun _ => b)
    (fun _ => ha0) (fun _ => hb0) (fun _ _ => rfl) fun _ => hab

theorem low_of_agree {N : ℕ} {a b : MvPowerSeries ι K} (hab : Agree N a b) : Low N $ a - b := by
  intro d hd
  rw [map_sub, hab d hd, sub_self]

theorem key [Finite ι] (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Low (N + 1) $ f.subst a - f.subst b - (a - b) := by
  rw [subst_eq f h0 h1 ha0, subst_eq f h0 h1 hb0]
  have e : a + a ^ 2 * (tail2 f).subst a - (b + b ^ 2 * (tail2 f).subst b) - (a - b) =
      (a - b) * (a + b) * (tail2 f).subst a + b ^ 2 * ((tail2 f).subst a - (tail2 f).subst b) := by ring
  rw [e]
  have hs : Low 1 $ a + b := low_one $ by simp [ha0, hb0]
  have hb2 : Low 2 $ b ^ 2 := by
    have := (low_one hb0).mul $ low_one hb0
    rwa [pow_two]
  refine Low.add ?_ ?_
  have := ((low_of_agree hab).mul hs).mul $ low_zero $ (tail2 f).subst a
  simpa using this
  exact (hb2.mul $ low_of_agree $ agree_psubst _ ha0 hb0 hab).mono $ by omega

end Inv

theorem invIntegralOfClass (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v)
    [Finite ι] (C : MvPowerSeries ι K → Prop) (f : PowerSeries K)
    (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    (hsub : ∀ a b, C a → C b → C (a - b))
    (hP : ∀ P, MvPowerSeries.constantCoeff P = 0 → IntegralMv P →
      C (f.subst P))
    (hlowC : ∀ D, C D → ∀ N, 1 ≤ N →
      (∀ d, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0) (hCh : C $ f.subst h) :
    IntegralMv h := by
  have main : ∀ N, ∀ d, d.degree < N → ‖MvPowerSeries.coeff d h‖ ≤ 1 := by
    intro N
    induction N with
    | zero =>
      intro d hd
      omega
    | succ N ih =>
      intro d hd
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hlt | heq
      exact ih d hlt
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      subst hN0
      have hd0 := (Finsupp.degree_eq_zero_iff d).1 heq
      subst hd0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0, norm_zero]
      exact zero_le_one
      let T : MvPowerSeries ι K := fun e => if e.degree < N then MvPowerSeries.coeff e h else 0
      have hTc : ∀ e, MvPowerSeries.coeff e T = if e.degree < N then MvPowerSeries.coeff e h else 0 :=
        fun e => rfl
      have hT0 : MvPowerSeries.constantCoeff T = 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hTc]
        simp [hNpos, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hh0]
      have hTint : IntegralMv T := by
        intro e
        rw [hTc]
        split_ifs with he
        exact ih e he
        simp
      have hAg : Agree N h T := by
        intro e he
        rw [hTc, if_pos he]
      have hk := key f h0 h1 hh0 hT0 hAg d $ by omega
      rw [map_sub, map_sub, map_sub, hTc, if_neg $ by omega, sub_zero] at hk
      have hcd : MvPowerSeries.coeff d h = MvPowerSeries.coeff d (f.subst h - f.subst T) := by
        rw [map_sub]
        linear_combination -hk
      rw [hcd]
      exact hlowC _ (hsub _ _ hCh $ hP T hT0 hTint) N hNpos (low_of_agree $ agree_psubst f hh0 hT0 hAg) d heq
  intro d
  exact main (d.degree + 1) d $ Nat.lt_succ_self _

end Formalism.LT.InvIntP

theorem Formalism.LT.InvIntP.InvIntegralOfClass_proof : Formalism.LT.InvIntegralOfClass.{u, v} := by
  intro K _ _ ι _ C f h0 h1 hsub hP hlowC h hh0 hCh
  exact Formalism.LT.InvIntP.invIntegralOfClass K ι C f h0 h1 hsub hP hlowC h hh0 hCh

theorem Formalism.LT.InvIntP.FunEqLowCoeff_proof : Formalism.LT.FunEqLowCoeff.{u, v} := by
  intro K _ ι p q hq σ hq2 D hD N hN hlow d hd
  exact Formalism.LT.InvIntP.funEqLowCoeff p q hq σ hq2 D hD N hN hlow d hd

theorem Formalism.LT.InvIntP.IntegralSubst_proof : Formalism.LT.IntegralSubst.{u, v} := by
  intro K _ _ ι f P hf hP0 hP
  exact Formalism.LT.InvIntP.integralSubst f P hf hP0 hP

theorem Formalism.LT.InvIntegralOfClass_proof : Formalism.LT.InvIntegralOfClass.{u, v} := by
  exact Formalism.LT.InvIntP.InvIntegralOfClass_proof
theorem Formalism.LT.FunEqLowCoeff_proof : Formalism.LT.FunEqLowCoeff.{u, v} := by
  exact Formalism.LT.InvIntP.FunEqLowCoeff_proof
theorem Formalism.LT.IntegralSubst_proof : Formalism.LT.IntegralSubst.{u, v} := by
  exact Formalism.LT.InvIntP.IntegralSubst_proof
end
section
open PowerSeries

namespace Formalism.LT.PadicP

theorem coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R)
    (hf0 : constantCoeff f = 0) (ha0 : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by
  change MvPowerSeries.coeff (Finsupp.single () 1) _ = _
  rw [coeff_subst $ HasSubst.of_constantCoeff_zero' ha0]
  change ∑ᶠ d, coeff d f • coeff 1 (a ^ d) = _
  rw [finsum_eq_single _ 1]
  rw [pow_one, smul_eq_mul]
  intro d hd
  obtain ⟨a', rfl⟩ := X_dvd_iff.mpr ha0
  rcases Nat.lt_or_gt_of_ne hd with h | h
  have h0 : d = 0 := by omega
  subst h0
  rw [pow_zero, coeff_one, if_neg one_ne_zero, smul_zero]
  rw [mul_pow, coeff_X_pow_mul', if_neg $ by omega, smul_zero]

end Formalism.LT.PadicP
end
section
namespace Formalism.LT.LTL

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_finsum_le' {α : Type*} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  rw [finsum_eq_sum g hfin]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ => hg i
  rw [finsum_of_infinite_support hfin]
  simpa using hC

end Formalism.LT.LTL
end
section
open PowerSeries


namespace Formalism.LT.Asm

open Formalism.G

section Integral

variable {K : Type u} [NormedField K] [IsUltrametricDist K]


theorem integralMv_sub {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv $ a - b := by
  intro d
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le (ha d) ?_
  rw [norm_neg]
  exact hb d

theorem integralMv_X {ι : Type*} (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp


theorem funEqMv_sub {ι : Type*} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K) {a b : MvPowerSeries ι K}
    (ha : IsFunEqTypeMv p q hq σ a) (hb : IsFunEqTypeMv p q hq σ b) :
    IsFunEqTypeMv p q hq σ $ a - b := by
  unfold IsFunEqTypeMv at *
  convert integralMv_sub ha hb using 1
  simp [map_sub, smul_sub]
  abel

end Integral

theorem q_ne_zero {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : q ≠ 0 := by
  obtain ⟨hp, ⟨k, -, rfl⟩, -⟩ := h
  exact pow_ne_zero _ hp.ne_zero

theorem two_le_q {K : Type u} [NormedField K] {p q : ℕ} {σ : K →+* K}
    (h : FunctionalEquationSetting K p q σ) : 2 ≤ q := by
  obtain ⟨hp, ⟨k, hk, rfl⟩, -⟩ := h
  exact hp.two_le.trans $ Nat.le_self_pow (by omega) _

theorem funEqInv (h2 : InvIntegralOfClass.{u, 0}) (h3 : FunEqLowCoeff.{u, 0})
    (hk : Formalism.G.FunEqSubst.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {p q : ℕ} {σ : K →+* K}
    (hS : FunctionalEquationSetting K p q σ) {ι : Type} [Finite ι] {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hfE : IsFunEqType p q σ f)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hC : IsFunEqTypeMv p q (q_ne_zero hS) σ $ f.subst h) : IntegralMv h :=
  h2 K ι (IsFunEqTypeMv p q (q_ne_zero hS) σ) f hf0 hf1
    (fun _ _ ha hb => funEqMv_sub _ _ ha hb)
    (fun P hP0 hPI => hk K p q (q_ne_zero hS) σ hS f hf0 hfE ι P hP0 hPI)
    (fun D hD N hN hlow d hd => h3 K ι p q (q_ne_zero hS) σ (two_le_q hS) D hD N hN hlow d hd)
    h hh0 hC


theorem funEqType_unit {K : Type u} [NormedField K] {p q : ℕ} (hq : q ≠ 0) {σ : K →+* K}
    {g : PowerSeries K} (hg : IsFunEqType p q σ g) :
    IsFunEqTypeMv (ι := Unit) p q hq σ (g : MvPowerSeries Unit K) := by
  have hx : (PowerSeries.map σ g).subst ((PowerSeries.X : PowerSeries K) ^ q) =
      MvPowerSeries.expand q hq (MvPowerSeries.map σ g) := by
    rw [← PowerSeries.expand_apply q hq]
    rfl
  intro d
  have := hg $ d ()
  rw [hx] at this
  have hd : d = Finsupp.single () (d ()) := by
    ext
    simp
  rwa [hd]

theorem FunEqHom_of' (h1 : SolveExists.{u, 0}) (h2 : InvIntegralOfClass.{u, 0})
    (h3 : FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} := by
  intro K _ _ _ p q σ hS f g hf0 hf1 hfE hg0 hgE
  obtain ⟨h, hh0, hh⟩ := h1 K Unit f (g : MvPowerSeries Unit K) hf0 hf1 hg0
  have hI := funEqInv h2 h3 hk hS hf0 hf1 hfE h hh0 $ by
    rw [hh]
    exact funEqType_unit (q_ne_zero hS) hgE
  exact ⟨h, hh0, fun n => hI _, hh⟩

section FG

open Formalism.G.LogP




theorem cc_subst2 {R : Type*} [CommRing R] {τ : Type*} [Finite τ] (F : MvPowerSeries (Fin 2) R)
    (hF0 : MvPowerSeries.constantCoeff F = 0) {u v : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.constantCoeff (F.subst ![u, v]) = 0 := by
  have hc : ∀ s, MvPowerSeries.constantCoeff (![u, v] s) = 0 := by
    intro s
    fin_cases s <;> simp [hu, hv]
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hc) hc hF0


variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def lift {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) :
    MvPowerSeries τ $ unitBall K :=
  fun d => ⟨MvPowerSeries.coeff d F, hF d⟩




end FG


end Formalism.LT.Asm

namespace Formalism.LT



theorem FunEqHom_of (h1 : Formalism.LT.SolveExists.{u, 0}) (h2 : Formalism.LT.InvIntegralOfClass.{u, 0})
    (h3 : Formalism.LT.FunEqLowCoeff.{u, 0}) (hk : Formalism.G.FunEqSubst.{u, 0}) : Formalism.G.FunEqHom.{u} :=
  Formalism.LT.Asm.FunEqHom_of' h1 h2 h3 hk

end Formalism.LT
end
section
open Ideal (span)
open MvPowerSeries (coeff coeff_map expand map map_expand)
namespace Formalism.LT.FrobP

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem norm_sigma_le {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1)
    (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le ((hσ a ha).trans hp.le) $ by
        rw [norm_pow]
        first
          | exact pow_le_one₀ (norm_nonneg a) ha
          | exact pow_le_one q (norm_nonneg a) ha

def sigmaO {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1) :
    unitBall K →+* unitBall K :=
  (σ.comp (unitBall K).subtype).codRestrict (unitBall K)
    fun x => norm_sigma_le hσ hp x.1 x.2

theorem natCast_coe (p : ℕ) : (((p : unitBall K)) : K) = (p : K) := by
  first
    | exact map_natCast (unitBall K).subtype p
    | simp

theorem norm_le_of_mem_span {p : ℕ} (x : unitBall K)
    (hx : x ∈ span {((p : ℕ) : unitBall K)}) : ‖(x : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have e : ((y * ((p : ℕ) : unitBall K) : unitBall K) : K) = (y : K) * (p : K) := by
    rw [← natCast_coe p]
    rfl
  rw [e, norm_mul]
  calc ‖(y : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right (y.2) (norm_nonneg _)
    _ = ‖(p : K)‖ := one_mul _

theorem mem_span_of_norm_le {p : ℕ} (hp0 : (p : K) ≠ 0) (x : unitBall K)
    (hx : ‖(x : K)‖ ≤ ‖(p : K)‖) : x ∈ span {((p : ℕ) : unitBall K)} := by
  have hy : ‖(x : K) / (p : K)‖ ≤ 1 := by
    rw [norm_div]
    first
      | exact div_le_one_of_le₀ hx $ norm_nonneg _
      | exact (div_le_one $ norm_pos_iff.mpr hp0).mpr hx
  refine Ideal.mem_span_singleton'.mpr ⟨⟨(x : K) / (p : K), hy⟩, ?_⟩
  apply Subtype.ext
  show (x : K) / (p : K) * ((p : unitBall K) : K) = (x : K)
  rw [natCast_coe, div_mul_cancel₀ _ hp0]

theorem natCast_nonunit {p : ℕ} (hp : ‖(p : K)‖ < 1) :
    ((p : ℕ) : unitBall K) ∈ nonunits (unitBall K) := by
  rw [mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu'⟩ := hu.exists_left_inv
  have h2 : (u : K) * (p : K) = 1 := by
    rw [← natCast_coe p]
    exact congrArg Subtype.val hu'
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  have h4 : ‖(u : K)‖ * ‖(p : K)‖ ≤ ‖(p : K)‖ := by
    calc ‖(u : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right (u.2) (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _
  linarith

def liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries ι $ unitBall K :=
  fun d => ⟨coeff d A, hA d⟩

theorem map_liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    map (unitBall K).subtype (liftO A hA) = A := by
  ext d
  rw [coeff_map]
  rfl

theorem main {ι : Type v} (p h : ℕ) (hpr : p.Prime) (σ : K →+* K) (hp0 : (p : K) ≠ 0)
    (hp : ‖(p : K)‖ < 1) (hσ : IsFrobLift p (p ^ h) σ) (A : MvPowerSeries ι K)
    (hA : IntegralMv A) :
    DivByMv (p : K) $ A ^ (p ^ h) - expand (p ^ h) (pow_ne_zero h hpr.ne_zero)
      (map σ A) := by
  classical
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI hchar : CharP (unitBall K ⧸ span {((p : ℕ) : unitBall K)}) p :=
    CharP.quotient (unitBall K) p $ natCast_nonunit hp
  haveI : ExpChar (unitBall K ⧸ span {((p : ℕ) : unitBall K)}) p := ExpChar.prime hpr
  have hq := pow_ne_zero h hpr.ne_zero
  have hkey : (Ideal.Quotient.mk $ span {((p : ℕ) : unitBall K)}).comp (sigmaO hσ hp)
      = (iterateFrobenius (unitBall K ⧸ span {((p : ℕ) : unitBall K)}) p h).comp
          (Ideal.Quotient.mk $ span {((p : ℕ) : unitBall K)}) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def, ← map_pow]
    first
      | rw [Ideal.Quotient.eq]
      | rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply mem_span_of_norm_le hp0
    first
      | exact hσ c.1 c.2
      | (push_cast; exact hσ c.1 c.2)
  have h1 : map (Ideal.Quotient.mk $ span {((p : ℕ) : unitBall K)})
        (map (sigmaO hσ hp) $ liftO A hA)
      = map (iterateFrobenius (unitBall K ⧸ span {((p : ℕ) : unitBall K)}) p h)
        (map (Ideal.Quotient.mk $ span {((p : ℕ) : unitBall K)}) $ liftO A hA) := by
    ext d
    simp [coeff_map]
    exact RingHom.congr_fun hkey _
  have hmain : map (Ideal.Quotient.mk $ span {((p : ℕ) : unitBall K)})
      ((liftO A hA) ^ (p ^ h) - expand (p ^ h) hq
        (map (sigmaO hσ hp) $ liftO A hA)) = 0 := by
    rw [map_sub, map_pow, map_expand, h1, ← map_expand,
      MvPowerSeries.map_iterateFrobenius_expand p hpr.ne_zero, sub_self]
  have hcoeffI : ∀ d, coeff d ((liftO A hA) ^ (p ^ h) - expand (p ^ h) hq
      (map (sigmaO hσ hp) $ liftO A hA)) ∈ span {((p : ℕ) : unitBall K)} := by
    intro d
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, hmain, map_zero]
  have h2 : map (unitBall K).subtype (map (sigmaO hσ hp) $ liftO A hA)
      = map σ A := by
    ext d
    first
      | rfl
      | (simp [coeff_map]; rfl)
  have hsub : map (unitBall K).subtype ((liftO A hA) ^ (p ^ h)
      - expand (p ^ h) hq (map (sigmaO hσ hp) $ liftO A hA))
      = A ^ (p ^ h) - expand (p ^ h) (pow_ne_zero h hpr.ne_zero) (map σ A) := by
    rw [map_sub, map_pow, map_expand, h2, map_liftO]
  intro d
  rw [← hsub, coeff_map]
  exact norm_le_of_mem_span (p := p) _ $ hcoeffI d

end Formalism.LT.FrobP

namespace Formalism.LT

open Formalism.G

theorem FrobCongr_valid : Formalism.LT.FrobCongr.{u, v} := by
  intro K _ _ _ p q hq σ hset ι A hA
  obtain ⟨hpr, ⟨h, _, rfl⟩, hp, hσ⟩ := hset
  exact FrobP.main p h hpr σ (Nat.cast_ne_zero.mpr hpr.ne_zero) hp hσ A hA

end Formalism.LT
end
section
open MvPowerSeries (coeff constantCoeff expand)
open PowerSeries (HasSubst coeff_subst coeff_subst_finite subst_X subst_pow)
open PowerSeries


namespace Formalism.LT

open Formalism.G

namespace InverseIntegralClassesKeyFacts

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma norm_finsum_le {g : ℕ → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  rw [finsum_eq_sum g hfin]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ => hg i
  rw [finsum_of_infinite_support hfin]
  simpa using hC

lemma norm_add_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a + b‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max a b).trans $ max_le ha hb

lemma norm_sub_le_of {a b : K} {C : ℝ} (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) : ‖a - b‖ ≤ C := by
  rw [sub_eq_add_neg]
  exact norm_add_le_of ha $ by simpa using hb

lemma norm_sigma_le_one {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp1 : ‖(p : K)‖ ≤ 1)
    {a : K} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h2 : ‖a ^ q‖ ≤ 1 := by rw [norm_pow]
                              exact pow_le_one₀ (norm_nonneg _) ha
  have : σ a = (σ a - a ^ q) + a ^ q := by ring
  rw [this]
  exact norm_add_le_of ((hσ a ha).trans hp1) h2

end InverseIntegralClassesKeyFacts

open InverseIntegralClassesKeyFacts

theorem FunEqSubst_of (h4 : Formalism.LT.IntegralSubst.{u, v}) (h5 : Formalism.LT.CoeffBound.{u})
    (h6 : Formalism.LT.PowCongr.{u, v}) (h7 : Formalism.LT.FrobCongr.{u, v}) : Formalism.G.FunEqSubst.{u, v} := by
  intro K _ _ _ p q hq σ hS f hf0 hfT ι α hα0 hαI
  obtain ⟨hp, ⟨h, hh, hqh⟩, hp1, hσ⟩ := id hS
  have hp1' : ‖(p : K)‖ ≤ 1 := hp1.le
  set fs : PowerSeries K := PowerSeries.map σ f with hfs
  set g : PowerSeries K := f - (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) with hg
  set β : MvPowerSeries ι K := expand q hq (MvPowerSeries.map σ α) with hβ
  have hαS : HasSubst α := HasSubst.of_constantCoeff_zero hα0
  have hαq0 : constantCoeff (α ^ q) = 0 := by
    rw [map_pow, hα0, zero_pow hq]
  have hαqS : HasSubst $ α ^ q := HasSubst.of_constantCoeff_zero hαq0
  have hmα0 : constantCoeff (MvPowerSeries.map σ α) = 0 := by
    simp [hα0]
  have hmαS : HasSubst $ MvPowerSeries.map σ α := HasSubst.of_constantCoeff_zero hmα0
  have hβ0 : constantCoeff β = 0 := by
    rw [hβ, MvPowerSeries.constantCoeff_expand, hmα0]
  have hβS : HasSubst β := HasSubst.of_constantCoeff_zero hβ0
  have hdec : f.subst α - (p : K)⁻¹ • expand q hq (MvPowerSeries.map σ $ f.subst α)
      = g.subst α + (p : K)⁻¹ • (fs.subst (α ^ q) - fs.subst β) := by
    have e1 : f = g + (p : K)⁻¹ • fs.subst ((PowerSeries.X : PowerSeries K) ^ q) := by
      rw [hg]
      abel
    have e2 : PowerSeries.subst α (fs.subst ((PowerSeries.X : PowerSeries K) ^ q) : PowerSeries K) = fs.subst (α ^ q) := by
      rw [PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' $ by simp [hq]) hαS, subst_pow hαS,
        subst_X hαS]
    have e3 : expand q hq (MvPowerSeries.map σ $ f.subst α) = fs.subst β := by
      rw [PowerSeries.map_subst hαS, PowerSeries.expand_subst q hq hmαS]
    have e4 : f.subst α = g.subst α + (p : K)⁻¹ • fs.subst (α ^ q) := by
      conv_lhs => rw [e1]
      rw [PowerSeries.subst_add hαS, PowerSeries.subst_smul hαS, e2]
    rw [e3, e4, smul_sub]
    abel

  have hXqI : IntegralPS $ (PowerSeries.X : PowerSeries K) ^ q := by
    intro n
    rw [PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have hαqI : IntegralMv $ α ^ q := by
    have := h4 K ι _ α hXqI hα0 hαI
    rwa [subst_pow hαS, subst_X hαS] at this
  have hdiv : DivByMv (p : K) $ α ^ q - β := h7 K p q hq σ hS ι α hαI
  have hβI : IntegralMv β := by
    intro d
    have e : coeff d β
        = coeff d (α ^ q) - coeff d (α ^ q - β) := by
      rw [map_sub]
      ring
    rw [e]
    exact norm_sub_le_of (hαqI d) $ (hdiv d).trans hp1'

  have hbr : ∀ d, ‖coeff d (fs.subst (α ^ q) - fs.subst β)‖ ≤ ‖(p : K)‖ := by
    intro d
    rw [map_sub, coeff_subst hαqS, coeff_subst hβS,
      ← finsum_sub_distrib (coeff_subst_finite hαqS fs d)
        $ coeff_subst_finite hβS fs d]
    apply norm_finsum_le $ norm_nonneg _
    intro n
    rw [← smul_sub, ← map_sub, smul_eq_mul, norm_mul, hfs, PowerSeries.coeff_map]
    obtain ⟨k, hkdvd, hk⟩ := h5 K p q σ hS f hf0 hfT n
    obtain ⟨m, rfl⟩ := hkdvd
    have hn : q ^ k * m = p ^ (h * k) * m := by rw [hqh, ← pow_mul]
    have hdiv' : DivByMv ((p : K) ^ 1) $ α ^ q - β := by simpa using hdiv
    have hc0 := h6 K ι p hp (α ^ q) β hαqI hβI 1 le_rfl hdiv' (h * k) m d
    rw [← hn] at hc0
    have hs : ‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k ≤ 1 := by
      have h0 : ‖coeff (q ^ k * m) f * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]
                                                              exact hk
      have h' := norm_sigma_le_one hσ hp1' h0
      rwa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h'
    have hc : ‖coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ := by
      refine hc0.trans ?_
      rw [norm_pow, pow_add, pow_one, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg _) hp1' $ Nat.le_mul_of_pos_left k hh) $ norm_nonneg _
    calc ‖σ (coeff (q ^ k * m) f)‖ * ‖coeff d ((α ^ q) ^ (q ^ k * m) - β ^ (q ^ k * m))‖
        ≤ ‖σ (coeff (q ^ k * m) f)‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖) :=
          mul_le_mul_of_nonneg_left hc $ norm_nonneg _
      _ = (‖σ (coeff (q ^ k * m) f)‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ := by ring
      _ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hs $ norm_nonneg _
      _ = ‖(p : K)‖ := one_mul _

  unfold IsFunEqTypeMv
  rw [hdec]
  intro d
  rw [map_add, MvPowerSeries.coeff_smul]
  refine norm_add_le_of ((h4 K ι g α hfT hα0 hαI) d) ?_
  rw [norm_mul, norm_inv]
  calc ‖(p : K)‖⁻¹ * ‖coeff d (fs.subst (α ^ q) - fs.subst β)‖
      ≤ ‖(p : K)‖⁻¹ * ‖(p : K)‖ := mul_le_mul_of_nonneg_left (hbr d) $ inv_nonneg.mpr $ norm_nonneg _
    _ = 1 := inv_mul_cancel₀ (norm_pos_iff.mpr $ Nat.cast_ne_zero.mpr hp.ne_zero).ne'

end Formalism.LT
end
section
open IsUltrametricDist (norm_add_le_max norm_natCast_le_one norm_sum_le_of_forall_le_of_nonneg)
open Nat (cast_one succ_le_of_lt zero_le)
open PowerSeries


namespace Formalism.LT.CoeffP

open Formalism.G

section Ball

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma sigma_norm_le_one {p q : ℕ} {σ : K →+* K} (hp : ‖(p : K)‖ ≤ 1)
    (hσ : IsFrobLift p q σ) (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := norm_add_le_max _ _
    _ ≤ 1 := max_le ((hσ a ha).trans hp) $ by
        rw [norm_pow]
        simpa using pow_le_pow_of_le_one (norm_nonneg a) ha $ zero_le q

lemma coeff_split (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K) (f : PowerSeries K) (n : ℕ) :
    coeff n f = coeff n (f - (p : K)⁻¹ • (PowerSeries.map σ f).subst
        ((PowerSeries.X : PowerSeries K) ^ q)) +
      (p : K)⁻¹ * (if q ∣ n then σ $ coeff (n / q) f else 0) := by
  rw [map_sub, map_smul, PowerSeries.coeff_subst_X_pow hq, PowerSeries.coeff_map, smul_eq_mul]
  split_ifs <;> simp

end Ball

private lemma norm_add_inv_mul_mul_norm_pow_succ_le_one {L : Type*} [NormedField L] [IsUltrametricDist L] (a s π : L) (k : ℕ)
    (ha : ‖a‖ ≤ 1) (hs : ‖s‖ * ‖π‖ ^ k ≤ 1) (hπ : ‖π‖ ≤ 1) (hπ0 : π ≠ 0) :
    ‖a + π⁻¹ * s‖ * ‖π‖ ^ (k + 1) ≤ 1 := by
  have hn := norm_pos_iff.mpr hπ0
  have hpow0 : 0 ≤ ‖π‖ ^ (k + 1) := pow_nonneg hn.le _
  refine (mul_le_mul_of_nonneg_right (norm_add_le_max _ _) hpow0).trans ?_
  rw [max_mul_of_nonneg _ _ hpow0]
  refine max_le ?_ ?_
  calc ‖a‖ * ‖π‖ ^ (k + 1) ≤ 1 * 1 := mul_le_mul ha (by simpa using pow_le_pow_of_le_one hn.le hπ $ zero_le $ k + 1) hpow0 zero_le_one
    _ = 1 := one_mul 1
  calc ‖π⁻¹ * s‖ * ‖π‖ ^ (k + 1) = ‖s‖ * ‖π‖ ^ k * (‖π‖⁻¹ * ‖π‖) := by
        rw [norm_mul, norm_inv, pow_succ]
        ring
    _ = ‖s‖ * ‖π‖ ^ k := by rw [inv_mul_cancel₀ hn.ne', mul_one]
    _ ≤ 1 := hs

theorem coeffBound : Formalism.LT.CoeffBound.{u} := by
  unfold Formalism.LT.CoeffBound
  intro K _ _ _ p q σ hset f hf0 hfe n
  obtain ⟨hp, ⟨e, he, hqe⟩, hp1, hσ⟩ := hset
  have hq2 : 2 ≤ q := by
    rw [hqe]
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos $ succ_le_of_lt he
  have hq0 : q ≠ 0 := by omega
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero

  have hσb : ∀ x k, ‖x‖ * ‖(p : K)‖ ^ k ≤ 1 → ‖σ x‖ * ‖(p : K)‖ ^ k ≤ 1 := by
    intro x k hx
    have h1 : ‖x * (p : K) ^ k‖ ≤ 1 := by rw [norm_mul, norm_pow]
                                          exact hx
    have h2 := sigma_norm_le_one hp1.le hσ _ h1
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h2
    exact h2
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.eq_zero_or_pos n with hn | hn
  subst hn
  refine ⟨0, dvd_zero _, ?_⟩
  have h0 : PowerSeries.coeff 0 f = 0 := by simpa using hf0
  rw [h0, norm_zero, zero_mul]
  exact zero_le_one
  have hg : ‖PowerSeries.coeff n (f - (p : K)⁻¹ •
      (PowerSeries.map σ f).subst ((PowerSeries.X : PowerSeries K) ^ q))‖ ≤ 1 := hfe n
  rw [coeff_split p q hq0 σ f n]
  by_cases hdiv : q ∣ n
  have hlt : n / q < n := Nat.div_lt_self hn $ by omega
  obtain ⟨k, hk, hkb⟩ := ih (n / q) hlt
  refine ⟨k + 1, ?_, ?_⟩
  have hnq : n = q * (n / q) := (Nat.mul_div_cancel' hdiv).symm
  rw [hnq, pow_succ']
  exact mul_dvd_mul_left q hk
  rw [if_pos hdiv]
  exact norm_add_inv_mul_mul_norm_pow_succ_le_one _ _ _ k hg (hσb _ _ hkb) hp1.le hpK
  refine ⟨0, by rw [pow_zero]; exact one_dvd n, ?_⟩
  rwa [if_neg hdiv, mul_zero, add_zero, pow_zero, mul_one]

section Bd

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}

def Bd (c : ℝ) (F : MvPowerSeries ι K) : Prop := ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ c

lemma Bd.mono {a b : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (h : a ≤ b) : Bd b F := by
  intro d
  exact (hF d).trans h

lemma Bd.mul {a b : ℝ} {F G : MvPowerSeries ι K} (hF : Bd a F) (hG : Bd b G) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : Bd (a * b) $ F * G := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul]
  refine norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hF x.1) (hG x.2) (norm_nonneg _) ha

lemma Bd.one : Bd 1 (1 : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

lemma Bd.pow {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (ha : 0 ≤ a) :
    ∀ n : ℕ, Bd (a ^ n) $ F ^ n
  | 0 => by simpa using (Bd.one : Bd 1 (1 : MvPowerSeries ι K))
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (Bd.pow hF ha n).mul hF (pow_nonneg ha n) ha

lemma Bd.sum {α : Type*} {a : ℝ} (ha : 0 ≤ a) {s : Finset α} {F : α → MvPowerSeries ι K}
    (h : ∀ i ∈ s, Bd a $ F i) : Bd a (∑ i ∈ s, F i) := by
  intro d
  rw [map_sum]
  exact norm_sum_le_of_forall_le_of_nonneg ha fun i hi => h i hi d

lemma Bd.mul_natCast {a : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (n : ℕ) :
    Bd (‖(n : K)‖ * a) $ F * (n : MvPowerSeries ι K) := by
  intro d
  rw [mul_comm F, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hF d) $ norm_nonneg _

private lemma bd_add' {c : ℝ} {F G : MvPowerSeries ι K} (hF : Bd c F) (hG : Bd c G) :
    Bd c $ F + G := by
  intro d
  rw [map_add]
  exact (norm_add_le_max _ _).trans $ max_le (hF d) $ hG d

lemma powp_step {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (_hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) $ A - B) :
    Bd (‖(p : K)‖ ^ (r + 1)) $ A ^ p - B ^ p := by
  have hpn : 0 ≤ ‖(p : K)‖ := norm_nonneg _
  have hp1 : ‖(p : K)‖ ≤ 1 := norm_natCast_le_one K p

  have hexp : A ^ p - B ^ p = ∑ m ∈ Finset.range p,
      (A - B) ^ (m + 1) * B ^ (p - (m + 1)) * ((p.choose (m + 1) : ℕ) : MvPowerSeries ι K) := by
    have h := add_pow (A - B) B p
    rw [sub_add_cancel, Finset.sum_range_succ'] at h
    rw [h, pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, cast_one, mul_one,
      add_sub_cancel_right]
  rw [hexp]
  refine Bd.sum (pow_nonneg hpn _) fun m hm => ?_
  have hBm : Bd 1 $ B ^ (p - (m + 1)) := by
    have h := Bd.pow hB zero_le_one $ p - (m + 1)
    rwa [one_pow] at h
  refine Bd.mono (Bd.mul_natCast (by
      have h := Bd.mul (by
          rw [pow_mul]
          exact Bd.pow hD (pow_nonneg hpn _) $ m + 1) hBm (pow_nonneg hpn _) zero_le_one
      rwa [mul_one] at h) $ p.choose (m + 1)) ?_
  rcases Nat.lt_or_ge (m + 1) p with hlt | hge
  ·
    obtain ⟨t, ht⟩ := hp.dvd_choose_self (Nat.succ_ne_zero m) hlt
    calc ‖((p.choose (m + 1) : ℕ) : K)‖ * ‖(p : K)‖ ^ (r * (m + 1))
        ≤ ‖(p : K)‖ * ‖(p : K)‖ ^ r := mul_le_mul (by
            rw [ht, Nat.cast_mul, norm_mul]
            calc ‖(p : K)‖ * ‖(t : K)‖ ≤ ‖(p : K)‖ * 1 :=
                  mul_le_mul_of_nonneg_left (norm_natCast_le_one K t) hpn
              _ = ‖(p : K)‖ := mul_one _) (pow_le_pow_of_le_one hpn hp1 $ Nat.le_mul_of_pos_right r $ Nat.succ_pos m) (pow_nonneg hpn _) hpn
      _ = ‖(p : K)‖ ^ (r + 1) := by ring
  ·
    have hm1 : m + 1 = p := Nat.le_antisymm (succ_le_of_lt $ Finset.mem_range.mp hm) hge
    rw [hm1, Nat.choose_self, cast_one, norm_one, one_mul]
    apply pow_le_pow_of_le_one hpn hp1
    calc r + 1 ≤ r * 2 := by omega
      _ ≤ r * p := Nat.mul_le_mul_left r hp.two_le

lemma powpj {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) {A B : MvPowerSeries ι K}
    (hA : Bd 1 A) (hB : Bd 1 B) (hD : Bd (‖(p : K)‖ ^ r) $ A - B) :
    ∀ j, Bd (‖(p : K)‖ ^ (r + j)) $ A ^ (p ^ j) - B ^ (p ^ j)
  | 0 => by simpa using hD
  | j + 1 => by
    rw [pow_succ p j, pow_mul, pow_mul, ← add_assoc]
    exact powp_step hp (by omega) (by simpa using hA.pow zero_le_one $ p ^ j)
      (by simpa using hB.pow zero_le_one $ p ^ j) $ powpj hp hr hA hB hD j

lemma pow_sub_pow_bd {c : ℝ} (hc : 0 ≤ c) {A B : MvPowerSeries ι K} (hA : Bd 1 A) (hB : Bd 1 B)
    (hD : Bd c $ A - B) (m : ℕ) : Bd c $ A ^ m - B ^ m := by
  induction m with
  | zero =>
    intro d
    simp [hc]
  | succ m ih =>
    have hAm : Bd 1 $ A ^ m := by simpa using Bd.pow hA zero_le_one m
    have e : A ^ (m + 1) - B ^ (m + 1) = A ^ m * (A - B) + (A ^ m - B ^ m) * B := by ring
    rw [e]
    exact bd_add' (by simpa using Bd.mul hAm hD zero_le_one hc) $ by simpa using Bd.mul ih hB hc zero_le_one

end Bd

theorem powCongr : Formalism.LT.PowCongr.{u, v} := by
  unfold Formalism.LT.PowCongr
  intro K _ _ ι p hp A B hA hB r hr hD j m
  have hA' := hA
  have hB' := hB
  have h1 := powpj hp hr hA' hB' (by
      intro d
      rw [← norm_pow]
      exact hD d) j
  have hBj : Bd 1 $ B ^ (p ^ j) := by simpa using Bd.pow hB' zero_le_one $ p ^ j
  intro d
  rw [norm_pow, pow_mul, pow_mul]
  exact (pow_sub_pow_bd (pow_nonneg (norm_nonneg _) _) (by simpa using Bd.pow hA' zero_le_one $ p ^ j) hBj h1 m) d

end Formalism.LT.CoeffP

theorem Formalism.LT.CoeffBound_valid : Formalism.LT.CoeffBound.{u} := Formalism.LT.CoeffP.coeffBound

theorem Formalism.LT.PowCongr_valid : Formalism.LT.PowCongr.{u, v} := Formalism.LT.CoeffP.powCongr
end
section
namespace Formalism.LT.SolveP

open PowerSeries

theorem SolveExists_proof : Formalism.LT.SolveExists.{u, v} := by
  intro R _ ι _ f G hf0 hf1 hG0
  have hu : IsUnit $ coeff 1 f := by rw [hf1]
                                     exact isUnit_one
  set g := f.substInvOfIsUnit hu with hg
  have hGS := HasSubst.of_constantCoeff_zero hG0
  refine ⟨g.subst G, ?_, ?_⟩
  exact constantCoeff_subst_eq_zero hG0 g $ constantCoeff_substInvOfIsUnit f hu
  rw [← subst_comp_subst_apply (HasSubst.substInvOfIsUnit f hu) hGS, subst_substInvOfIsUnit_right f hf0 hu, subst_X hGS]

end Formalism.LT.SolveP

theorem Formalism.LT.SolveExists_proof : Formalism.LT.SolveExists.{u, v} := Formalism.LT.SolveP.SolveExists_proof
end
section
namespace Formalism.LT


theorem funEqSubst : Formalism.G.FunEqSubst.{u, v} :=
  FunEqSubst_of IntegralSubst_proof CoeffBound_valid PowCongr_valid FrobCongr_valid



theorem funEqHom : Formalism.G.FunEqHom.{u} :=
  FunEqHom_of SolveExists_proof InvIntegralOfClass_proof FunEqLowCoeff_proof funEqSubst




end Formalism.LT
end
section
open scoped BigOperators
open MvPowerSeries (coeff coeff_map constantCoeff map)

namespace Formalism.L2.Th1.C

namespace Calc

open Pts

section CongCalc

variable {K : Type} [Field K] [CharZero K] {R : Subring K} {σ : Type}

theorem lg_zero : LG R (0 : MvPowerSeries σ K) := by
  classical
  unfold LG
  use map_zero _
  rw [mvExp_zero]
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  exact R.one_mem
  exact R.zero_mem

theorem lg_add {f g : MvPowerSeries σ K} (hf : LG R f) (hg : LG R g) : LG R $ f + g := by
  classical
  unfold LG at *
  refine ⟨by rw [map_add, hf.1, hg.1, add_zero], ?_⟩
  rw [mvExp_add hf.1 hg.1]
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf.2 p.1) $ hg.2 p.2

private lemma intMv_of_mul_eq_one_lemma {a b : MvPowerSeries σ K} (hb : IntMv R b)
    (hb0 : constantCoeff b = 1) (hab : a * b = 1) : IntMv R a := by
  let bR : MvPowerSeries σ R := fun n => ⟨coeff n b, hb n⟩
  have hmap : map R.subtype bR = b := by
    ext n
    rw [coeff_map]
    try rfl
  have hu : IsUnit bR := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    have h1 : constantCoeff bR = 1 := by
      apply Subtype.ext
      first
        | exact hb0
        | exact (MvPowerSeries.coeff_zero_eq_constantCoeff_apply b).trans hb0
    rw [h1]
    exact isUnit_one
  obtain ⟨u, hu⟩ := hu
  have hc : map R.subtype (↑u⁻¹ : MvPowerSeries σ R) * b = 1 := by
    rw [← hmap, ← map_mul, ← hu, Units.inv_mul, map_one]
  have ha : a = map R.subtype (↑u⁻¹ : MvPowerSeries σ R) := by
    calc a = a * (b * map R.subtype (↑u⁻¹ : MvPowerSeries σ R)) := by
          rw [mul_comm b, hc, mul_one]
      _ = _ := by rw [← mul_assoc, hab, one_mul]
  intro n
  rw [ha, coeff_map]
  exact (coeff n (↑u⁻¹ : MvPowerSeries σ R)).2

theorem lg_neg {f : MvPowerSeries σ K} (hf : LG R f) : LG R $ -f := by
  unfold LG at *
  refine ⟨by rw [map_neg, hf.1, neg_zero], ?_⟩
  exact intMv_of_mul_eq_one_lemma hf.2 (constantCoeff_mvExp hf.1) $ mvExp_neg hf.1







end CongCalc

end Calc

end Formalism.L2.Th1.C
end
section
namespace Formalism.L2.Th1.C


theorem zLinInt : ZLinInt := scalarLinearInt'


theorem endIntFromDatum : EndIntFromDatum := integral_endomorphism_from_datum
theorem phNormFromDatum : PhNormFromDatum := phi_norm_from_datum

end Formalism.L2.Th1.C
end
section
namespace Formalism.L2.Th1.C

theorem phOIsPh : PhOIsPh := odd_phi_is_phi
theorem first_level_from_universal_law : FirstLevelFromUniversal := first_level_from_universal_holds




end Formalism.L2.Th1.C
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.C

open Formalism.L2.Th1.A

namespace WeierstrassCurveSeries

variable {K : Type} [Field K] [CharZero K]

theorem logPair (W : WeierstrassCurve K) : IsLogPair (logSer W) $ expSer W := by
  obtain ⟨h0, h1, -, -⟩ := Formalism.L2.Th1.A.logSpec.{0} K W
  obtain ⟨e0, -, e2, e3, -⟩ := Formalism.L2.Th1.A.expSpec.{0} K W
  exact ⟨h0, h1, e0, e3, e2⟩

theorem xIsWp (W : WeierstrassCurve K) : XIsWp (wpReg W) (logSer W) (xS W) $ W.b₂ / 12 := by
  have hl :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (logPair W).1
  unfold XIsWp wpShift
  rw [map_zero, sub_zero, PowerSeries.subst_add hl, PowerSeries.subst_mul hl,
    PowerSeries.subst_pow hl, PowerSeries.subst_X hl, ← PowerSeries.coe_substAlgHom hl, map_one,
    PowerSeries.coe_substAlgHom hl, Formalism.L2.Th1.A.wpInU.{0} K W]
  ring

theorem subst_wTr (W : WeierstrassCurve K) (xP yP : K) :
    PowerSeries.subst (logSer W) (wTr W xP yP) = xPlus W xP yP + PowerSeries.C (W.b₂ / 12) := by
  have h := logPair W
  unfold wTr
  rw [PowerSeries.subst_add $ PowerSeries.HasSubst.of_constantCoeff_zero' h.1, Pts.subst_subst h.2.2.1 h.1, h.2.2.2.1, PowerSeries.X_subst,
    PowerSeries.subst_C]
  rfl

end WeierstrassCurveSeries

open WeierstrassCurveSeries

theorem curve_formal_frame : CurveFrame := by
  intro K _ _ R W hW
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  obtain ⟨-, hx, -, -, hom, -, hF, -⟩ := Formalism.L2.Th1.A.coeffMem.{0} K W R h1 h2 h3 h4 h6
  refine ⟨logPair W, xIsWp W, ⟨(Formalism.L2.Th1.A.wSerFactor.{0} K W).2.2.2.1, hx⟩, ?_, ?_⟩
  intro n
  have := (Formalism.L2.Th1.A.fglLog.{0} K W).2
  unfold fadd
  rw [← this]
  exact hF n
  rw [(Formalism.L2.Th1.A.logSpec.{0} K W).2.2.1]
  constructor
  exact (Formalism.L2.Th1.A.unitSpec.{0} K W).2.2.1
  exact hom
theorem curveEndoZ_of (hD : CurveSecondLogDerivative) : CurveEndoZ := by
  intro K _ _ W ι _ neg xP yP al h
  obtain ⟨hE, hn, hxy, hsum⟩ := h
  refine ⟨hn, ?_, hsum⟩
  intro P
  have := hD K W (xP P) (yP P) $ hE P
  show HasSecondLogDeriv (wpShift (wpReg W) $ xP P + W.b₂ / 12)
    $ 2 * wpReg W - wTr W (xP P) (yP P) - wTr W (xP $ neg P) (yP $ neg P)
  rwa [(hxy P).1, (hxy P).2]

theorem curveEndoR_of (hD : CurveSecondLogDerivative) : CurveEndoR := by
  intro K _ _ R W hW ι _ neg xP yP al albar h hx hy hN ha ha' hc
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  refine ⟨curveEndoZ_of hD K W ι neg xP yP al h, hN, fun P => subst_wTr W _ _, ?_, hx, ha, ha', hc⟩
  intro P n
  exact ((Formalism.L2.Th1.A.coeffMem.{0} K W R h1 h2 h3 h4 h6).2.2.2.2.2.2.2.2.2.2 (xP P) (hx P) (yP P) (hy P) n).1


theorem curve_second_log_derivative_holds : CurveSecondLogDerivative := by
  intro K _ _ W xP yP hP
  exact Formalism.L2.Th1.A.plusZCleared.{0} K W xP yP hP


theorem curve_real_multiplication_series : CurveEndoR := curveEndoR_of curve_second_log_derivative_holds


end Formalism.L2.Th1.C
end
section
namespace Formalism.L2.Th1.C

theorem curveFrame : CurveFrame := curve_formal_frame
theorem curveEndoR : CurveEndoR := curve_real_multiplication_series

end Formalism.L2.Th1.C
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A
open Formalism.G (unitBall)

namespace WeierstrassCurveSeries

theorem rescale_neg_one_of_even {K : Type} [Field K] (e : PowerSeries K)
    (h : ∀ n, Odd n → PowerSeries.coeff n e = 0) : PowerSeries.rescale (-1 : K) e = e := by
  ext n
  rw [PowerSeries.coeff_rescale]
  rcases Nat.even_or_odd n with hn | hn
  rw [hn.neg_one_pow, one_mul]
  rw [h n hn, mul_zero]

theorem endoCurve_neg_one {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) :
    IsEndoCurve W (id : Empty → Empty) (fun _ => (0 : K)) (fun _ => (0 : K)) $ -1 := by
  use fun P => P.elim, fun P => P.elim, fun P => P.elim
  rw [rescale_neg_one_of_even _ (Formalism.L2.Th1.A.wpShape.{0} K W).2.2.1]
  simp

theorem inv_mem_unitBall {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (h : ‖x‖ = 1) :
    x⁻¹ ∈ unitBall K := by
  have h1 : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv, h, inv_one]
  first
    | exact h1
    | simpa [Formalism.G.unitBall] using h1


end WeierstrassCurveSeries

open WeierstrassCurveSeries

theorem curve_neg_norm_holds : CurveNegNorm := by
  intro K _ _ R W hW h2 s2
  obtain ⟨hlp, hwp, hA, -, -⟩ := curveFrame K R W hW
  have hm := R.neg_mem R.one_mem
  have hE := curveEndoR K R W hW Empty id (fun _ => (0 : K)) (fun _ => (0 : K)) (-1) (-1)
    (endoCurve_neg_one W) (fun P => P.elim) (fun P => P.elim) (by simp) hm
    (by rw [inv_neg, inv_one]; exact hm) $ by simp
  apply phNormFromDatum K R (wpReg W) s2 (logSer W) (expSer W) _ (xS W) (W.b₂ / 12) Empty id _ _ _
    (-1) (-1) hlp ((phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2) hwp hA h2 hE
  simp
theorem curve_formal_first_level_holds : WeierstrassBiadditiveModEquiv := by
  intro K _ _ _ W hc h2 s2
  have hW := hc
  obtain ⟨hlp, -, -, -, -⟩ := curveFrame K (unitBall K) W hc
  obtain ⟨hlaw, hinv, -⟩ := Formalism.L2.Th1.A.bridgeLaw K W hW
  have hu := (Formalism.L2.Th1.B.f1O K (Formalism.L2.Th1.A.g₂ W) (Formalism.L2.Th1.A.g₃ W) s2 (W.b₂ / 12) (wpReg W)
    (logSer W) (Formalism.L2.Th1.A.iSer W) (xS W) (Formalism.L2.Th1.A.fgl W) (Formalism.L2.Th1.A.bridgeWp K W) hlaw
    hinv (Formalism.L2.Th1.A.bridgeCurve K W hW) h2).2.2.1
  exact (first_level_from_universal_law K (Formalism.L2.Th1.A.fgl W) (logSer W) (expSer W) _ hlp hlaw ((phOIsPh K (wpReg W) (logSer W) s2 hlp.1 hlp.2.1).2.1) hu).2.2



end Formalism.L2.Th1.G
end
end
