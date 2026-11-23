import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Bundle00
import Bundle01
import Bundle02
noncomputable section
section
namespace Formalism.L2.Th1.G


theorem curveNegNorm : CurveNegNorm := curve_neg_norm_holds
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := curve_formal_first_level_holds



end Formalism.L2.Th1.G
end
section
open scoped BigOperators

namespace Formalism.L2.Th1.C

open Formalism.L2.Th1.A

theorem mem_unitBall_iff {K : Type} [NormedField K] [IsUltrametricDist K] (x : K) :
    x ∈ Formalism.G.unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem inv_mem_unitBall {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (h : ‖x‖ = 1) :
    x⁻¹ ∈ Formalism.G.unitBall K := by
  rw [mem_unitBall_iff, norm_inv, h, inv_one]



end Formalism.L2.Th1.C
end
section
open Complex (exp exp_nat_mul)
open Real (pi)
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1
open scoped ComplexConjugate

theorem an_two_shift (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ) :
    F.sgStar L (z + ω₀ / 2)
      = -(exp ((pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2)) := by
  have h := F.sgStarQuasi L ω₀ (z - ω₀ / 2) h0
  have e1 : z - ω₀ / 2 + ω₀ = z + ω₀ / 2 := by ring
  have e2 : (pi : ℂ) * F.herm L (z - ω₀ / 2) ω₀ + (pi : ℂ) * F.herm L ω₀ ω₀ / 2
      = (pi : ℂ) * F.herm L z ω₀ := by
    unfold F.herm
    ring
  have e3 : F.semiChar L ω₀ = -1 := by
    unfold F.semiChar
    exact if_neg h1
  rw [e1, e2, e3] at h
  rw [h]
  ring

theorem an_two_sq (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    exp ((pi : ℂ) * F.herm L z ω₀) * F.sgStar L (z - ω₀ / 2) ^ 2
      = F.sgStar L z ^ 2 * F.sgStar L (ω₀ / 2) ^ 2
        * (L.weierstrassP z - L.weierstrassP (ω₀ / 2)) := by
  have h := F.sgStarAdd L z (ω₀ / 2) hz h1
  rw [an_two_shift L ω₀ h0 h1 z] at h
  linear_combination -h

theorem an_two_kap (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) * F.sgStar L (ω₀ / 2) ^ 4
      = exp ((pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
  have hz : ω₀ / 4 ∉ L.lattice := by
    intro h
    apply h1
    have := L.lattice.add_mem h h
    have e : ω₀ / 4 + ω₀ / 4 = ω₀ / 2 := by ring
    rwa [e] at this
  have hzt : ω₀ / 4 + ω₀ / 2 ∉ L.lattice := by
    intro h
    apply hz
    have := L.lattice.sub_mem h0 h
    have e : ω₀ - (ω₀ / 4 + ω₀ / 2) = ω₀ / 4 := by ring
    rwa [e] at this
  have hH := F.halfShift L (ω₀ / 2) (ω₀ / 4) h1 (by
      have e : 2 * (ω₀ / 2) = ω₀ := by ring
      rwa [e]) hz hzt
  have hA := an_two_shift L ω₀ h0 h1 $ ω₀ / 4
  have hB1 := an_two_sq L ω₀ h0 h1 (ω₀ / 4) hz
  have hB2 := an_two_sq L ω₀ h0 h1 (ω₀ / 4 + ω₀ / 2) hzt
  have e1 : ω₀ / 4 + ω₀ / 2 - ω₀ / 2 = ω₀ / 4 := by ring
  have e2 : exp ((pi : ℂ) * F.herm L (ω₀ / 4 + ω₀ / 2) ω₀)
      = exp ((pi : ℂ) * F.herm L (ω₀ / 4) ω₀)
        * exp ((pi : ℂ) * F.herm L ω₀ ω₀ / 2) := by
    rw [← Complex.exp_add]
    congr 1; unfold F.herm; ring
  rw [e1, e2, hA] at hB2
  have hs : F.sgStar L (ω₀ / 4) ≠ 0 := fun h => hz $ ((F.sgStarBasic L).2.2.1 _).1 h
  have hE : exp ((pi : ℂ) * F.herm L (ω₀ / 4) ω₀) ≠ 0 := Complex.exp_ne_zero _
  have hne : exp ((pi : ℂ) * F.herm L (ω₀ / 4) ω₀) * F.sgStar L (ω₀ / 4) ^ 2 ≠ 0 :=
    mul_ne_zero hE $ pow_ne_zero _ hs
  apply mul_left_cancel₀ hne
  rw [← hH]
  generalize exp ((pi : ℂ) * F.herm L (ω₀ / 4) ω₀) = E at *
  generalize exp ((pi : ℂ) * F.herm L ω₀ ω₀ / 2) = X at *
  generalize F.sgStar L (ω₀ / 4) = s at *
  generalize F.sgStar L (ω₀ / 4 - ω₀ / 2) = s' at *
  generalize F.sgStar L (ω₀ / 2) = T at *
  generalize L.weierstrassP (ω₀ / 4) - L.weierstrassP (ω₀ / 2) = a at *
  generalize L.weierstrassP (ω₀ / 4 + ω₀ / 2) - L.weierstrassP (ω₀ / 2) = b at *
  linear_combination (-1 : ℂ) * hB2 + (-(E * T ^ 2 * b)) * hB1

theorem an_two_odd (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (m : ℕ) :
    F.sgStar L (((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2)) ^ 2
      = exp ((pi : ℂ) * F.herm L ω₀ ω₀ / 2) ^ (2 * (m ^ 2 + m))
        * F.sgStar L (ω₀ / 2) ^ 2 := by
  have e1 : ((2 * m + 1 : ℕ) : ℂ) * (ω₀ / 2) = ω₀ / 2 + (m : ℂ) * ω₀ := by push_cast
                                                                           ring
  have hchi : F.semiChar L ((m : ℂ) * ω₀) ^ 2 = 1 := by
    unfold F.semiChar
    split_ifs <;> norm_num
  rw [e1, F.sgStarQuasi L ((m : ℂ) * ω₀) (ω₀ / 2) (by rw [← nsmul_eq_mul]; exact L.lattice.nsmul_mem h0 m), mul_pow, mul_pow, hchi, one_mul, ← exp_nat_mul, ← exp_nat_mul]
  congr 2
  unfold F.herm
  simp [map_mul, Complex.conj_natCast]
  push_cast
  ring

theorem an_two_card (L : PeriodPair) (n : ℕ) (hn : n ≠ 0) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) : S.card + 1 = n ^ 2 := by
  have hst : F.MulStable L (n : ℂ) := by
    intro ω hω
    rw [← nsmul_eq_mul]
    exact L.lattice.nsmul_mem hω n
  have h := F.kerRepsCard L (n : ℂ) S (by exact_mod_cast hn) hst hS
  have e : Complex.normSq (n : ℂ) = (n : ℝ) ^ 2 := by
    rw [← Complex.ofReal_natCast, Complex.normSq_ofReal]
    ring
  rw [e] at h
  exact_mod_cast h

theorem an_two (L : PeriodPair) (n : ℕ) (hn : Odd n) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (h1 : ω₀ / 2 ∉ L.lattice) :
    ((n : ℂ) ^ 2 * ∏ P ∈ S, (L.weierstrassP (ω₀ / 2) - L.weierstrassP P)) ^ 2
      = (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) ^ (n ^ 2 - 1) := by
  obtain ⟨m, rfl⟩ := hn
  have hn0 : 2 * m + 1 ≠ 0 := by omega
  have hI := F.isogenySigma L ((2 * m + 1 : ℕ) : ℂ) S (by exact_mod_cast hn0) (by
      intro ω hω
      rw [← nsmul_eq_mul]
      exact L.lattice.nsmul_mem hω _) hS (ω₀ / 2) h1
  rw [an_two_card L _ hn0 S hS, an_two_odd L ω₀ h0 m, ← an_two_kap L ω₀ h0 h1] at hI
  have hT : F.sgStar L (ω₀ / 2) ≠ 0 := fun h => h1 $ ((F.sgStarBasic L).2.2.1 _).1 h
  have ek : (2 * m + 1) ^ 2 - 1 = 4 * (m ^ 2 + m) := by
    have : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
    omega
  have ek2 : 2 * (2 * m + 1) ^ 2 = 8 * (m ^ 2 + m) + 2 := by ring
  rw [ek]
  rw [ek2] at hI
  clear ek ek2
  generalize m ^ 2 + m = k at *
  generalize F.sgStar L (ω₀ / 2) = T at *
  generalize (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) = κ at *
  generalize ∏ P ∈ S, (L.weierstrassP (ω₀ / 2) - L.weierstrassP P) = Q at *
  generalize ((2 * m + 1 : ℕ) : ℂ) = N at *
  have hT' : T ^ (8 * k + 2) ≠ 0 := pow_ne_zero _ hT
  have h3 : κ ^ (2 * k) = N ^ 2 * Q := by
    apply mul_left_cancel₀ hT'
    have : (κ * T ^ 4) ^ (2 * k) * T ^ 2 = T ^ (8 * k + 2) * κ ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, pow_add]
      have : 4 * (2 * k) = 8 * k := by ring
      rw [this]
      ring
    rw [← this, hI]
    ring
  rw [← h3, ← pow_mul]
  congr 1
  ring

end ReciprocityTheory.ChartRestriction.L1
end
section
open IsUltrametricDist (norm_add_le_max)
namespace ReciprocityTheory.ChartRestriction.L1

theorem kap_unit {K : Type} [NormedField K] [IsUltrametricDist K] (g2 g3 e : K) (h2 : ‖g2‖ ≤ 1)
    (h3 : ‖g3‖ ≤ 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (h22 : ‖(2 : K)‖ = 1)
    (he : 4 * e ^ 3 - g2 * e - g3 = 0) : ‖e‖ ≤ 1 ∧ ‖3 * e ^ 2 - g2 / 4‖ = 1 := by
  have hn1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact (norm_add_le_max _ _).trans (max_le ih (by simp))
  have h4 : ‖(4 : K)‖ = 1 := by
    rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h22, one_mul]
  have h4ne : (4 : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h4
    exact zero_ne_one h4
  have h3n : ‖(3 : K)‖ ≤ 1 := by simpa using hn1 3
  have h12n : ‖(12 : K)‖ ≤ 1 := by simpa using hn1 12
  have h15n : ‖(15 : K)‖ ≤ 1 := by simpa using hn1 15
  have h36n : ‖(36 : K)‖ ≤ 1 := by simpa using hn1 36
  have he1 : ‖e‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have hE : 4 * e ^ 3 = g2 * e + g3 := by linear_combination he
    have hn : ‖(4 : K) * e ^ 3‖ = ‖e‖ ^ 3 := by rw [norm_mul, h4, one_mul, norm_pow]
    have hle : ‖g2 * e + g3‖ ≤ ‖e‖ := by
      refine (norm_add_le_max _ _).trans (max_le ?_ ?_)
      rw [norm_mul]
      nlinarith [norm_nonneg g2, norm_nonneg e]
      linarith
    rw [← hE, hn] at hle
    have hsq : 1 < ‖e‖ ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hsq (by linarith : (0 : ℝ) < ‖e‖)]
  use he1
  have hg3 : g3 = 4 * e ^ 3 - g2 * e := by linear_combination -he
  have hid : g2 ^ 3 - 27 * g3 ^ 2 = (g2 - 12 * e ^ 2) * (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4) := by
    rw [hg3]
    ring
  have hk : 3 * e ^ 2 - g2 / 4 = -(g2 - 12 * e ^ 2) / 4 := by
    field_simp
    ring
  have hen := norm_nonneg e
  have he4 : ‖e‖ ^ 4 ≤ 1 := pow_le_one₀ hen he1
  have hQ : ‖g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4‖ ≤ 1 := by
    refine (norm_add_le_max _ _).trans (max_le ?_ ?_)
    rw [sub_eq_add_neg]
    refine (norm_add_le_max _ _).trans (max_le ?_ ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) h2
    rw [norm_neg, norm_mul, norm_mul, norm_pow]
    exact mul_le_one₀ (mul_le_one₀ h15n (by positivity) (pow_le_one₀ hen he1)) (norm_nonneg _) h2
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ h36n (by positivity) he4
  have hP : ‖g2 - 12 * e ^ 2‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (norm_add_le_max _ _).trans (max_le h2 ?_)
    rw [norm_neg, norm_mul, norm_pow]
    exact mul_le_one₀ h12n (by positivity) (pow_le_one₀ hen he1)
  have hP1 : 1 ≤ ‖g2 - 12 * e ^ 2‖ := by
    have := hΔ
    rw [hid, norm_mul] at this
    nlinarith [norm_nonneg (g2 - 12 * e ^ 2), norm_nonneg (g2 ^ 2 - 15 * e ^ 2 * g2 + 36 * e ^ 4)]
  rw [hk, norm_div, norm_neg, h4, div_one]
  exact le_antisymm hP hP1

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section Concrete

variable (l : ℕ) [Fact l.Prime]

def muP : Set ℂ_[l] := {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}

def Rmu : Subring ℂ_[l] := Subring.closure $ muP l

def Kmu : Subfield ℂ_[l] := Subfield.closure $ muP l

def Tch : Set ℂ_[l] := insert 0 $ muP l

theorem kur_complete : CompleteSpace $ MaximalUnramifiedExtension l :=
  (Subfield.isClosed_topologicalClosure $ Kmu l).completeSpace_coe

end Concrete

structure FrobField (K : Type) [NormedField K] (l : ℕ) (σ : K →+* K) : Prop where
  prime : l.Prime
  norm_l : ‖(l : K)‖ < 1
  isom : ∀ x : K, ‖σ x‖ = ‖x‖
  frob : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ l‖ ≤ ‖(l : K)‖
  discrete : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : K)‖

def ResClosed (K : Type) [NormedField K] (l : ℕ) : Prop :=
  ∀ P : Polynomial K, P.Monic → 0 < P.natDegree → (∀ i, ‖P.coeff i‖ ≤ 1) →
    ∃ x : K, ‖x‖ ≤ 1 ∧ ‖P.eval x‖ ≤ ‖(l : K)‖

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Abstract

variable {K : Type} [NormedField K]

structure LawD (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) : Prop where
  lam0 : constantCoeff lam = 0
  lam1 : coeff 1 lam = 1
  Φ0 : MvPowerSeries.constantCoeff Φ = 0
  Φint : IntegralMv Φ
  log : lam.subst Φ = atX lam + atY lam

structure HD (σ : K →+* K) (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K)
    (a : K) : Prop extends LawD lam Φ where
  A0 : constantCoeff A = 0
  Aint : IntegralPS A
  Alog : lam.subst A = C a * lam
  a_ne : ‖σ a - a‖ = 1
  a_sq : σ (σ a) = a

structure QCls (l : ℕ) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K) (b : K)
    (D : PowerSeries K) : Prop where
  D0 : constantCoeff D = 0
  dInt : IntegralPS $ derivative D
  add : DivByMv (l : K) $ D.subst Φ - atX D - atY D
  eig : DivBy (l : K) $ D.subst A - C b * D

structure HomCls (l : ℕ) (Φ₁ : MvPowerSeries (Fin 2) K) (A₁ : PowerSeries K)
    (Φ₂ : MvPowerSeries (Fin 2) K) (A₂ : PowerSeries K) (g : PowerSeries K) : Prop where
  g0 : constantCoeff g = 0
  gInt : IntegralPS g
  add : DivByMv (l : K) $ g.subst Φ₁ - Φ₂.subst ![atX g, atY g]
  eig : DivBy (l : K) $ g.subst A₁ - A₂.subst g

def desc (l : ℕ) (D : PowerSeries K) : PowerSeries K := PowerSeries.mk fun m => coeff (l * m) D

def d2 (Φ : MvPowerSeries (Fin 2) K) : PowerSeries K :=
  PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) Φ

end Abstract

open Classical in

def lgS {K : Type} [Field K] (g2 g3 : K) : PowerSeries K :=
  if h : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X then h.choose else 0

end ReciprocityTheory.ChartRestriction.L1
end
section
open PowerSeries (coeff_subst' map subst_X subst_comp_subst_apply subst_substInvOfIsUnit_left)
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Field
variable {K : Type} [Field K] (g2 g3 : K)

theorem coeff_one_subst_of_constantCoeff_eq_zero (f g : PowerSeries K) (hg : constantCoeff g = 0) :
    coeff 1 (f.subst g) = coeff 1 f * coeff 1 g := by
  rw [coeff_subst' $ HasSubst.of_constantCoeff_zero hg, finsum_eq_single _ 1]
  simp [smul_eq_mul]
  intro d hd
  rcases Nat.lt_or_gt_of_ne hd with h | h
  have : d = 0 := by omega
  subst this
  simp
  have h2 : X ^ d ∣ g ^ d := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hg) d
  simp [X_pow_dvd_iff.mp h2 1 h]

theorem uSer_const : constantCoeff (uSer g2 g3) = 0 := by
  unfold uSer
  rw [map_mul, map_mul, constantCoeff_X, zero_mul, zero_mul]
theorem uSer_coeff_one : coeff 1 (uSer g2 g3) = 1 := by
  unfold uSer
  rw [mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
    map_mul, constantCoeff_inv]
  unfold wpNum wpDen
  simp [← coeff_zero_eq_constantCoeff_apply]

theorem isUnit_coeff_one_weierstrassExp : IsUnit $ coeff 1 $ uSer g2 g3 := by
  rw [uSer_coeff_one]
  exact isUnit_one

theorem exists_rightInverse_weierstrassExp : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X := ⟨(uSer g2 g3).substInvOfIsUnit $ isUnit_coeff_one_weierstrassExp g2 g3, PowerSeries.constantCoeff_substInvOfIsUnit _ _,
  PowerSeries.subst_substInvOfIsUnit_right _ (uSer_const g2 g3) _⟩

theorem lgS_const : constantCoeff (lgS g2 g3) = 0 := by
  unfold lgS
  rw [dif_pos $ exists_rightInverse_weierstrassExp g2 g3]
  exact (exists_rightInverse_weierstrassExp g2 g3).choose_spec.1
theorem uSer_subst_lgS : (uSer g2 g3).subst (lgS g2 g3) = X := by
  unfold lgS
  rw [dif_pos $ exists_rightInverse_weierstrassExp g2 g3]
  exact (exists_rightInverse_weierstrassExp g2 g3).choose_spec.2
theorem lgS_coeff_one : coeff 1 (lgS g2 g3) = 1 := by
  have h := congrArg (coeff 1) $ uSer_subst_lgS g2 g3
  rw [coeff_one_subst_of_constantCoeff_eq_zero _ _ $ lgS_const g2 g3, uSer_coeff_one, one_mul] at h
  simpa using h

theorem eq_substInv_of_rightInverse (t : PowerSeries K) (ht : constantCoeff t = 0)
    (h : (uSer g2 g3).subst t = X) :
    t = (uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3) := by
  have h1 := subst_comp_subst_apply (HasSubst.of_constantCoeff_zero $ uSer_const g2 g3)
    (HasSubst.of_constantCoeff_zero ht) $ (uSer g2 g3).substInvOfIsUnit $ isUnit_coeff_one_weierstrassExp g2 g3
  rw [subst_substInvOfIsUnit_left _ $ uSer_const g2 g3, subst_X $ HasSubst.of_constantCoeff_zero ht,
    h, PowerSeries.X_subst] at h1
  exact h1

theorem weierstrassLog_eq_substInv : lgS g2 g3 = (uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3) := eq_substInv_of_rightInverse g2 g3 (lgS g2 g3) (lgS_const g2 g3) $ uSer_subst_lgS g2 g3

theorem lgS_subst_uSer : (lgS g2 g3).subst (uSer g2 g3) = X := by
  rw [weierstrassLog_eq_substInv]
  exact subst_substInvOfIsUnit_left _ (uSer_const g2 g3) _

theorem lgS_unique (t : PowerSeries K) (ht : constantCoeff t = 0) (h : (uSer g2 g3).subst t = X) :
    t = lgS g2 g3 := by
  exact (eq_substInv_of_rightInverse g2 g3 t ht h).trans (weierstrassLog_eq_substInv g2 g3).symm

theorem constantCoeff_C_mul_weierstrassLog (b : K) : constantCoeff (C b * lgS g2 g3) = 0 := by
  rw [map_mul, constantCoeff_C, lgS_const, mul_zero]

theorem mult_const (b : K) : constantCoeff ((uSer g2 g3).subst (C b * lgS g2 g3)) = 0 := by
  have hs := constantCoeff_C_mul_weierstrassLog g2 g3 b
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' $ HasSubst.of_constantCoeff_zero hs, finsum_eq_single _ 0]
  simp [uSer_const]
  intro d hd
  simp [map_pow, hs, zero_pow hd]
theorem mult_log (b : K) :
    (lgS g2 g3).subst ((uSer g2 g3).subst (C b * lgS g2 g3)) = C b * lgS g2 g3 := by
  have ha := HasSubst.of_constantCoeff_zero $ constantCoeff_C_mul_weierstrassLog g2 g3 b
  have h1 := subst_comp_subst_apply (HasSubst.of_constantCoeff_zero $ uSer_const g2 g3) ha $ lgS g2 g3
  rw [lgS_subst_uSer, subst_X ha] at h1
  exact h1.symm
theorem mult_unique (b : K) (e : PowerSeries K) (he : constantCoeff e = 0)
    (h : (lgS g2 g3).subst e = C b * lgS g2 g3) : e = (uSer g2 g3).subst (C b * lgS g2 g3) := by
  have hE := HasSubst.of_constantCoeff_zero he
  have h1 := subst_comp_subst_apply (HasSubst.of_constantCoeff_zero $ lgS_const g2 g3) hE $ uSer g2 g3
  rwa [uSer_subst_lgS, subst_X hE, h] at h1

theorem ltLog_const (l : ℕ) (hl : 2 ≤ l) : constantCoeff (ltLog K l) = 0 := by
  first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, dif_neg]
  rintro ⟨j, hj⟩
  have h0 : 0 < (l ^ 2) ^ j := pow_pos (pow_pos (by omega) 2) j
  rw [← hj] at h0
  exact lt_irrefl 0 h0

end Field

section Map
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)

theorem cW_unfold {K : Type} [Field K] (g2 g3 : K) (k : ℕ) : cW g2 g3 k =
    if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
    if 4 ≤ k then
      3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
        ∑ m : Fin $ k - 3, cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
    else 0 := by
  rw [cW]
  first
    | (rw [Nat.strongRecOn_beta]; rfl)
    | (rw [Nat.strongRecOn'_beta]; rfl)
    | (rw [Nat.strongRecOn_eq]; rfl)
    | (unfold Nat.strongRecOn; rw [Nat.strongRec_eq]; rfl)
    | (exact (Nat.strongRecOn_beta' ..).trans rfl)

theorem cW_map (k : ℕ) : φ (cW g2 g3 k) = cW (φ g2) (φ g3) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_unfold, cW_unfold (φ g2) $ φ g3]
    split_ifs with h1 h2 h3
    rw [map_div₀]
    congr 1
    exact_mod_cast map_natCast φ 20
    rw [map_div₀]
    congr 1
    exact_mod_cast map_natCast φ 28
    simp only [map_mul, map_div₀, map_sum, map_ofNat, map_natCast, map_sub, map_add, map_one]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    have hm := m.2
    rw [ih _ $ by omega, ih _ $ by omega]
    simp

theorem wpNum_map : map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) := by
  ext n
  unfold wpNum
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp [cW_map]

theorem wpDen_map : map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) := by
  ext n
  unfold wpDen
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp [cW_map]

theorem wpDen_const' {K : Type} [Field K] (g2 g3 : K) : constantCoeff (wpDen g2 g3) = 1 := by
  unfold wpDen
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp

theorem uSer_map : map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by
  have hD : constantCoeff (wpDen (φ g2) $ φ g3) ≠ 0 := by rw [wpDen_const']
                                                          exact one_ne_zero
  have hD0 : constantCoeff (wpDen g2 g3) ≠ 0 := by rw [wpDen_const']
                                                   exact one_ne_zero
  have h : map φ (wpDen g2 g3)⁻¹ = (wpDen (φ g2) $ φ g3)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one hD, ← wpDen_map, ← map_mul,
      PowerSeries.inv_mul_cancel _ hD0, map_one]
  unfold uSer
  rw [map_mul, map_mul, map_X, wpNum_map, h]

theorem map_subst_ps {a : PowerSeries K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    map φ (f.subst a) = (map φ f).subst (map φ a) := by
  erw [PowerSeries.map_subst $ HasSubst.of_constantCoeff_zero ha]
  try rfl

theorem lgS_map : map φ (lgS g2 g3) = lgS (φ g2) (φ g3) := by
  refine lgS_unique (φ g2) (φ g3) _ ?_ ?_
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
    lgS_const, map_zero]
  rw [← uSer_map, ← map_subst_ps φ $ lgS_const g2 g3, uSer_subst_lgS, map_X]

theorem ltLog_map (l : ℕ) : map φ (ltLog K l) = ltLog L l := by
  ext n
  first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp

theorem mult_map (b : K) :
    map φ ((uSer g2 g3).subst (C b * lgS g2 g3))
      = (uSer (φ g2) $ φ g3).subst (C (φ b) * lgS (φ g2) (φ g3)) := by
  rw [map_subst_ps φ $ constantCoeff_C_mul_weierstrassLog g2 g3 b, uSer_map, map_mul, map_C, lgS_map]

theorem lt_map (l : ℕ) (hl : 2 ≤ l) (ε : K) :
    map φ ((uSer g2 g3).subst (C ε * ltLog K l))
      = (uSer (φ g2) $ φ g3).subst (C (φ ε) * ltLog L l) := by
  have h0 : constantCoeff (C ε * ltLog K l) = 0 := by
    rw [map_mul, constantCoeff_C, ltLog_const l hl, mul_zero]
  rw [map_subst_ps φ h0, uSer_map, map_mul, map_C, ltLog_map]

end Map

theorem omegaK_quad (d : ℕ) (hd : d % 4 = 3) :
    omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  unfold omegaK
  have h4 : (((d + 1) / 4 : ℕ) : ℂ) = ((d : ℂ) + 1) / 4 := by
    have h : 4 ∣ d + 1 := by omega
    rw [Nat.cast_div h $ by norm_num]
    push_cast
    ring
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt $ Nat.cast_nonneg _]
    norm_cast
  rw [h4]
  linear_combination (((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4 : ℂ) * hs

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K]

section Ring
variable {ι : Type}

theorem integralMv_iff_divBy_one (F : MvPowerSeries ι K) : IntegralMv F ↔ DivByMv (1 : K) F := by
  first
  | exact Iff.rfl
  | (unfold IntegralMv DivByMv; simp)
  | simp [IntegralMv, DivByMv]
theorem integralPS_iff_mv (f : PowerSeries K) : IntegralPS f ↔ IntegralMv (ι := Unit) f := by
  rw [integralMv_iff_divBy_one]
  unfold IntegralPS DivByMv
  constructor
  intro h d
  have hd : d = Finsupp.single () (d ()) := by
    refine Finsupp.ext fun u => ?_
    cases u
    simp
  rw [hd, norm_one]
  exact h $ d ()
  intro h n
  have := h $ Finsupp.single () n
  rwa [norm_one] at this
theorem divBy_iff_mv (x : K) (f : PowerSeries K) : DivBy x f ↔ DivByMv (ι := Unit) x f := by
  unfold DivBy DivByMv
  constructor
  intro h d
  have hd : d = Finsupp.single () (d ()) := by
    refine Finsupp.ext fun u => ?_
    cases u
    simp
  rw [hd]
  exact h $ d ()
  intro h n
  exact h $ Finsupp.single () n
theorem divByMv_zero (x : K) : DivByMv x (0 : MvPowerSeries ι K) := by
  intro d
  rw [map_zero, norm_zero]
  exact norm_nonneg _
theorem divByMv_add {x : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv x G) :
    DivByMv x $ F + G := by
  intro d
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le (hF d) $ hG d
theorem divByMv_sub {x : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv x G) :
    DivByMv x $ F - G := by
  intro d
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    $ max_le (hF d) (by rw [norm_neg]; exact hG d)
theorem divByMv_neg {x : K} {F : MvPowerSeries ι K} (hF : DivByMv x F) : DivByMv x $ -F := by
  intro d
  rw [map_neg, norm_neg]
  exact hF d
theorem divByMv_mul {x y : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv y G) :
    DivByMv (x * y) $ F * G := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul, norm_mul]
  refine Finset.sum_induction _ (fun z => ‖z‖ ≤ ‖x‖ * ‖y‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans $ max_le ha hb)
    (by rw [norm_zero]; positivity) ?_
  intro p _
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) $ norm_nonneg _
theorem divByMv_mul_left {x : K} {F G : MvPowerSeries ι K} (hF : IntegralMv F) (hG : DivByMv x G) :
    DivByMv x $ F * G := by
  have h := divByMv_mul ((integralMv_iff_divBy_one F).mp hF) hG
  rwa [one_mul] at h
theorem divByMv_sum {x : K} {α : Type} (s : Finset α) (F : α → MvPowerSeries ι K)
    (hF : ∀ i ∈ s, DivByMv x $ F i) : DivByMv x (∑ i ∈ s, F i) := by
  exact Finset.sum_induction _ (DivByMv x) (fun _ _ => divByMv_add) (divByMv_zero x) hF
theorem integralMv_one : IntegralMv (1 : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp
theorem integralMv_X (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp
theorem integralMv_C {c : K} (hc : ‖c‖ ≤ 1) : IntegralMv (MvPowerSeries.C c : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_C]
  split_ifs <;> simp [hc]
theorem integralMv_mul {F G : MvPowerSeries ι K} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv $ F * G := by
  rw [integralMv_iff_divBy_one] at *
  have h := divByMv_mul hF hG
  rwa [one_mul] at h
theorem integralMv_pow {F : MvPowerSeries ι K} (hF : IntegralMv F) (n : ℕ) : IntegralMv $ F ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact integralMv_one
  | succ n ih => rw [pow_succ]; exact integralMv_mul ih hF

theorem divByMv_iff_smul {x : K} (hx : x ≠ 0) (F : MvPowerSeries ι K) :
    DivByMv x F ↔ ∃ G, IntegralMv G ∧ F = x • G := by
  constructor
  intro h
  refine ⟨x⁻¹ • F, ?_, by rw [smul_smul, mul_inv_cancel₀ hx, one_smul]⟩
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_smul, norm_mul, norm_inv, norm_one,
    inv_mul_le_iff₀ $ norm_pos_iff.mpr hx, mul_one]
  exact h d
  rintro ⟨G, hG, rfl⟩ d
  have h1 := (integralMv_iff_divBy_one G).mp hG d
  rw [norm_one] at h1
  rw [MvPowerSeries.coeff_smul, norm_mul]
  calc ‖x‖ * ‖MvPowerSeries.coeff d G‖ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖x‖ := mul_one _

end Ring

section OneVar

theorem divBy_add {x : K} {f g : PowerSeries K} (hf : DivBy x f) (hg : DivBy x g) :
    DivBy x $ f + g :=
  (divBy_iff_mv _ _).mpr $ divByMv_add ((divBy_iff_mv _ _).mp hf) $ (divBy_iff_mv _ _).mp hg
theorem divBy_neg {x : K} {f : PowerSeries K} (hf : DivBy x f) : DivBy x $ -f :=
  (divBy_iff_mv _ _).mpr $ divByMv_neg $ (divBy_iff_mv _ _).mp hf
theorem divBy_mul_left {x : K} {f g : PowerSeries K} (hf : IntegralPS f) (hg : DivBy x g) :
    DivBy x $ f * g :=
  (divBy_iff_mv _ _).mpr $ divByMv_mul_left ((integralPS_iff_mv _).mp hf) $ (divBy_iff_mv _ _).mp hg
theorem integralPS_iff_divBy_one (f : PowerSeries K) : IntegralPS f ↔ DivBy (1 : K) f := by
  rw [integralPS_iff_mv, integralMv_iff_divBy_one, divBy_iff_mv]
theorem integralPS_X : IntegralPS (X : PowerSeries K) := by
  exact (integralPS_iff_mv _).mpr $ integralMv_X ()
theorem integralPS_C {c : K} (hc : ‖c‖ ≤ 1) : IntegralPS (C c : PowerSeries K) := by
  exact (integralPS_iff_mv _).mpr $ integralMv_C hc
theorem integralPS_mul {f g : PowerSeries K} (hf : IntegralPS f) (hg : IntegralPS g) :
    IntegralPS $ f * g := by
  rw [integralPS_iff_mv] at *
  exact integralMv_mul hf hg
theorem integralPS_pow {f : PowerSeries K} (hf : IntegralPS f) (n : ℕ) : IntegralPS $ f ^ n := by
  rw [integralPS_iff_mv] at *
  exact integralMv_pow hf n
private theorem norm_natCast_le_one_unramified_integrals (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le ih $ by simp

theorem divBy_derivative {x : K} {f : PowerSeries K} (hf : DivBy x f) :
    DivBy x $ derivative f := by
  unfold DivBy at hf ⊢
  intro n
  rw [PowerSeries.coeff_derivative, norm_mul]
  calc ‖coeff (n + 1) f‖ * ‖((n : K) + 1)‖ ≤ ‖x‖ * 1 :=
        mul_le_mul (hf _) (by
            have := norm_natCast_le_one_unramified_integrals (K := K) $ n + 1
            push_cast at this
            exact this) (norm_nonneg _) $ norm_nonneg _
    _ = ‖x‖ := mul_one _
theorem integralPS_derivative {f : PowerSeries K} (hf : IntegralPS f) :
    IntegralPS $ derivative f := by
  rw [integralPS_iff_divBy_one] at *
  exact divBy_derivative hf

theorem integralPS_inv {f : PowerSeries K} (hf : IntegralPS f) (h0 : ‖constantCoeff f‖ = 1) :
    IntegralPS f⁻¹ := by
  unfold IntegralPS at hf ⊢
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  rw [PowerSeries.coeff_inv]
  split_ifs with hn
  rw [norm_inv, h0, inv_one]
  rw [norm_mul, norm_neg, norm_inv, h0, inv_one, one_mul]
  refine Finset.sum_induction _ (fun z => ‖z‖ ≤ 1)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans $ max_le ha hb)
    (by rw [norm_zero]; exact zero_le_one) ?_
  intro p _
  split_ifs with hlt
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) $ ih _ hlt
  rw [norm_zero]
  exact zero_le_one

theorem divBy_of_mul_unit {x : K} {f g : PowerSeries K} (hf : IntegralPS f)
    (h0 : ‖constantCoeff f‖ = 1) (h : DivBy x $ f * g) : DivBy x g := by
  have hf0 : constantCoeff f ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at h0
    exact zero_ne_one h0
  have e : g = f⁻¹ * (f * g) := by rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hf0, one_mul]
  rw [e]
  exact divBy_mul_left (integralPS_inv hf h0) h
private theorem coeff_subst_X_pow_eq_ite_dvd' (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
  rw [PowerSeries.coeff_subst' $ PowerSeries.HasSubst.of_constantCoeff_zero' $ by simp [hk]]
  simp [← pow_mul, PowerSeries.coeff_X_pow]
  split_ifs with hd
  obtain ⟨q, rfl⟩ := hd
  rw [finsum_eq_single _ q]
  simp [Nat.mul_div_cancel_left q $ Nat.pos_of_ne_zero hk]
  intro d hd
  have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
  simp [this]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro d
  have : m ≠ k * d := fun h => hd ⟨d, h⟩
  simp [this]

theorem divBy_expand_iff (x : K) (n : ℕ) (hn : n ≠ 0) (f : PowerSeries K) :
    DivBy x (f.subst ((X : PowerSeries K) ^ n)) ↔ DivBy x f := by
  unfold DivBy
  constructor
  intro h m
  have := h $ n * m
  rwa [coeff_subst_X_pow_eq_ite_dvd' f hn, if_pos $ dvd_mul_right n m,
    Nat.mul_div_cancel_left m $ Nat.pos_of_ne_zero hn] at this
  intro h m
  rw [coeff_subst_X_pow_eq_ite_dvd' f hn]
  split_ifs
  exact h _
  rw [norm_zero]
  exact norm_nonneg _
theorem divByMv_expand_iff {ι : Type} (x : K) (n : ℕ) (hn : n ≠ 0) (F : MvPowerSeries ι K) :
    DivByMv x (MvPowerSeries.expand n hn F) ↔ DivByMv x F := by
  classical
  constructor
  intro h d
  have := h $ n • d
  rwa [MvPowerSeries.coeff_expand_smul] at this
  intro h d
  by_cases hd : ∀ i, n ∣ d i
  have e : d = n • Finsupp.mapRange (fun k => k / n) (Nat.zero_div n) d := by
    ext i
    simp [Nat.mul_div_cancel' $ hd i]
  rw [e, MvPowerSeries.coeff_expand_smul]
  exact h _
  push_neg at hd
  obtain ⟨i, hi⟩ := hd
  rw [MvPowerSeries.coeff_expand_of_not_dvd n hn F hi, norm_zero]
  exact norm_nonneg _

end OneVar

section Subst
variable {ι : Type}

private theorem norm_finsum_le_of_forall_norm_le {α : Type} (g : α → K) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖g i‖ ≤ C) : ‖∑ᶠ i, g i‖ ≤ C := by
  by_cases hs : (Function.support g).Finite
  rw [finsum_eq_sum g hs]
  exact Finset.sum_induction _ (fun z => ‖z‖ ≤ C)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans $ max_le ha hb)
    (by rw [norm_zero]; exact hC) fun i _ => h i
  rwa [finsum_of_infinite_support hs, norm_zero]

theorem integralMv_subst {f : PowerSeries K} {P : MvPowerSeries ι K} (hf : IntegralPS f)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) : IntegralMv $ f.subst P := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [norm_one]
  have hPk : ∀ k, ‖MvPowerSeries.coeff d (P ^ k)‖ ≤ 1 := fun k => by
    have h1 := (integralMv_iff_divBy_one _).mp (integralMv_pow hP k) d
    rwa [norm_one] at h1
  first
  | rw [PowerSeries.coeff_subst ha]
  | rw [PowerSeries.coeff_subst' ha]
  exact norm_finsum_le_of_forall_norm_le _ zero_le_one fun k => by
    rw [smul_eq_mul, norm_mul]
    exact mul_le_one₀ (hf k) (norm_nonneg _) $ hPk k
theorem divByMv_subst {x : K} {f : PowerSeries K} {P : MvPowerSeries ι K} (hf : DivBy x f)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) : DivByMv x $ f.subst P := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  intro d
  have hPk : ∀ k, ‖MvPowerSeries.coeff d (P ^ k)‖ ≤ 1 := fun k => by
    have h1 := (integralMv_iff_divBy_one _).mp (integralMv_pow hP k) d
    rwa [norm_one] at h1
  first
  | rw [PowerSeries.coeff_subst ha]
  | rw [PowerSeries.coeff_subst' ha]
  exact norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun k => by
    rw [smul_eq_mul, norm_mul]
    calc ‖coeff k f‖ * ‖MvPowerSeries.coeff d (P ^ k)‖ ≤ ‖x‖ * 1 :=
          mul_le_mul (hf k) (hPk k) (norm_nonneg _) $ norm_nonneg _
      _ = ‖x‖ := mul_one _

theorem divByMv_subst_congr {x : K} (hx : ‖x‖ ≤ 1) {f : PowerSeries K} {P Q : MvPowerSeries ι K}
    (hf : IntegralPS f) (hP0 : MvPowerSeries.constantCoeff P = 0)
    (hQ0 : MvPowerSeries.constantCoeff Q = 0) (hP : IntegralMv P) (hQ : IntegralMv Q)
    (hPQ : DivByMv x $ P - Q) : DivByMv x $ f.subst P - f.subst Q := by
  by_cases hx : x = 0
  subst hx
  have hPQ' : P = Q := by
    ext d
    have h1 := hPQ d
    rw [norm_zero, map_sub] at h1
    exact sub_eq_zero.mp $ norm_le_zero_iff.mp h1
  rw [hPQ', sub_self]
  exact divByMv_zero _
  obtain ⟨R, hR, hPR⟩ := (divByMv_iff_smul hx _).mp hPQ
  have haP := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  have haQ := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  intro d
  rw [map_sub, PowerSeries.coeff_subst haP, PowerSeries.coeff_subst haQ,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite haP f d) $ PowerSeries.coeff_subst_finite haQ f d]
  refine norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun k => ?_
  have hG : IntegralMv (∑ i ∈ Finset.range k, P ^ i * Q ^ (k - 1 - i)) := by
    rw [integralMv_iff_divBy_one]
    exact divByMv_sum _ _ fun i _ =>
      (integralMv_iff_divBy_one _).mp $ integralMv_mul (integralMv_pow hP i) $ integralMv_pow hQ _
  have hGR := (integralMv_iff_divBy_one _).mp (integralMv_mul hG hR) d
  rw [norm_one] at hGR
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, ← geom_sum₂_mul, hPR, mul_smul_comm,
    MvPowerSeries.coeff_smul, norm_mul, norm_mul]
  calc ‖coeff k f‖ * (‖x‖ * ‖MvPowerSeries.coeff d ((∑ i ∈ Finset.range k, P ^ i * Q ^ (k - 1 - i)) * R)‖)
      ≤ 1 * (‖x‖ * 1) := mul_le_mul (hf k) (mul_le_mul_of_nonneg_left hGR $ norm_nonneg _)
        (by positivity) zero_le_one
    _ = ‖x‖ := by ring
theorem divByMv_subst2 {x : K} {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : DivByMv x F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv $ P i) : DivByMv x $ F.subst P := by
  have ha : MvPowerSeries.HasSubst P := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hP0
    | exact ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hprod : ∀ e : Fin 2 →₀ ℕ, IntegralMv $ e.prod fun s k => P s ^ k := by
    intro e
    unfold Finsupp.prod
    exact Finset.prod_induction _ IntegralMv (fun _ _ => integralMv_mul) integralMv_one
      fun s _ => integralMv_pow (hP s) _
  intro d
  rw [MvPowerSeries.coeff_subst ha]
  exact norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun e => by
    rw [smul_eq_mul, norm_mul]
    have h1 := (integralMv_iff_divBy_one _).mp (hprod e) d
    rw [norm_one] at h1
    calc ‖MvPowerSeries.coeff e F‖ * ‖MvPowerSeries.coeff d (e.prod fun s k => P s ^ k)‖
        ≤ ‖x‖ * 1 := mul_le_mul (hF e) h1 (norm_nonneg _) $ norm_nonneg _
      _ = ‖x‖ := mul_one _
theorem integralMv_subst2 {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : IntegralMv F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv $ P i) : IntegralMv $ F.subst P := by
  rw [integralMv_iff_divBy_one] at hF ⊢
  exact divByMv_subst2 hF hP0 hP
theorem divByMv_subst2_congr {x : K} (hx : ‖x‖ ≤ 1) {F : MvPowerSeries (Fin 2) K}
    {P Q : Fin 2 → MvPowerSeries ι K} (hF : IntegralMv F)
    (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hQ0 : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0) (hP : ∀ i, IntegralMv $ P i)
    (hQ : ∀ i, IntegralMv $ Q i) (hPQ : ∀ i, DivByMv x $ P i - Q i) :
    DivByMv x $ F.subst P - F.subst Q := by
  have haP : MvPowerSeries.HasSubst P := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hP0
    | exact ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have haQ : MvPowerSeries.HasSubst Q := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hQ0
    | exact ⟨fun s => by rw [hQ0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hpow : ∀ i k, DivByMv x $ P i ^ k - Q i ^ k := by
    intro i k
    rw [← geom_sum₂_mul]
    refine divByMv_mul_left ?_ $ hPQ i
    rw [integralMv_iff_divBy_one]
    exact divByMv_sum _ _ fun j _ =>
      (integralMv_iff_divBy_one _).mp $ integralMv_mul (integralMv_pow (hP i) j) $ integralMv_pow (hQ i) _
  have hprod : ∀ e : Fin 2 →₀ ℕ,
      DivByMv x $ (e.prod fun s k => P s ^ k) - e.prod fun s k => Q s ^ k := by
    intro e
    rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _, Finsupp.prod_fintype _ _ fun _ => pow_zero _,
      Fin.prod_univ_two, Fin.prod_univ_two]
    have e2 : P 0 ^ e 0 * P 1 ^ e 1 - Q 0 ^ e 0 * Q 1 ^ e 1
        = P 0 ^ e 0 * (P 1 ^ e 1 - Q 1 ^ e 1) + Q 1 ^ e 1 * (P 0 ^ e 0 - Q 0 ^ e 0) := by ring
    rw [e2]
    exact divByMv_add (divByMv_mul_left (integralMv_pow (hP 0) _) $ hpow 1 _)
      $ divByMv_mul_left (integralMv_pow (hQ 1) _) $ hpow 0 _
  intro d
  rw [map_sub, MvPowerSeries.coeff_subst haP, MvPowerSeries.coeff_subst haQ,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite haP F d)
      $ MvPowerSeries.coeff_subst_finite haQ F d]
  refine norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun e => ?_
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub, norm_mul]
  have h1 := (integralMv_iff_divBy_one F).mp hF e
  rw [norm_one] at h1
  calc ‖MvPowerSeries.coeff e F‖ *
        ‖MvPowerSeries.coeff d ((e.prod fun s k => P s ^ k) - e.prod fun s k => Q s ^ k)‖
      ≤ 1 * ‖x‖ := mul_le_mul h1 (hprod e d) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _

end Subst

section Frob
variable {l : ℕ} {σ : K →+* K} {ι : Type}

theorem FrobField.integralMv_map (h : FrobField K l σ) {F : MvPowerSeries ι K} (hF : IntegralMv F) :
    IntegralMv $ MvPowerSeries.map σ F := by
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_map, h.isom]
  exact (integralMv_iff_divBy_one F).mp hF d

theorem norm_natCast_of_coprime (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (m : ℕ) (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hint : ∀ a : ℤ, ‖(a : K)‖ ≤ 1 := by
    intro a
    rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
    push_cast
    exact norm_natCast_le_one_unramified_integrals n
    push_cast
    rw [norm_neg]
    exact norm_natCast_le_one_unramified_integrals n
  have hb := Nat.gcd_eq_gcd_ab m l
  rw [((Nat.Prime.coprime_iff_not_dvd hl).mpr hm).symm] at hb
  have hbK : (1 : K) = (m : K) * (Nat.gcdA m l : K) + (l : K) * (Nat.gcdB m l : K) := by
    have := congrArg (fun z : ℤ => (z : K)) hb
    push_cast at this
    exact this
  refine le_antisymm (norm_natCast_le_one_unramified_integrals m) ?_
  by_contra hlt
  push_neg at hlt
  have h1 := IsUltrametricDist.norm_add_le_max ((m : K) * (Nat.gcdA m l : K))
    $ (l : K) * (Nat.gcdB m l : K)
  rw [← hbK, norm_one] at h1
  have h3 : ‖(l : K) * (Nat.gcdB m l : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖((Nat.gcdB m l : ℤ) : K)‖ ≤ ‖(l : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hint _) $ norm_nonneg _
      _ < 1 := by rw [mul_one]
                  exact hl1
  exact lt_irrefl _ $ lt_of_le_of_lt h1 $ max_lt (by
      rw [norm_mul]
      calc ‖(m : K)‖ * ‖((Nat.gcdA m l : ℤ) : K)‖ ≤ ‖(m : K)‖ * 1 :=
            mul_le_mul_of_nonneg_left (hint _) $ norm_nonneg _
        _ < 1 := by rw [mul_one]
                    exact hlt) h3
theorem FrobField.funEqSetting [CharZero K] (h : FrobField K l σ) : FunctionalEquationSetting K l l σ := by
  use h.prime, ⟨1, one_pos, (pow_one l).symm⟩, h.norm_l
  exact h.frob

end Frob

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def LeadAt (f : PowerSeries K) (r : ℝ) (i : ℕ) : Prop :=
  0 < r ∧ (∀ n, ‖coeff n f‖ ≤ r) ∧ (∀ n, n < i → ‖coeff n f‖ < r) ∧ ‖coeff i f‖ = r

theorem gauss_norm_add_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem gauss_norm_sum_lt {α : Type} (s : Finset α) (f : α → K) {r : ℝ} (hr : 0 < r)
    (h : ∀ a ∈ s, ‖f a‖ < r) : ‖∑ a ∈ s, f a‖ < r := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  simpa using hr
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
  exact hle.trans_lt $ h i hi

theorem LeadAt.mul {f g : PowerSeries K} {r s : ℝ} {i j : ℕ} (hf : LeadAt f r i) (hg : LeadAt g s j) :
    LeadAt (f * g) (r * s) $ i + j := by
  obtain ⟨hr, hf1, hf2, hf3⟩ := hf
  obtain ⟨hs, hg1, hg2, hg3⟩ := hg
  have small : ∀ p q, (p < i ∨ q < j) → ‖coeff p f * coeff q g‖ < r * s := by
    intro p q hpq
    rw [norm_mul]
    rcases hpq with hp | hq
    calc ‖coeff p f‖ * ‖coeff q g‖ ≤ ‖coeff p f‖ * s :=
          mul_le_mul_of_nonneg_left (hg1 q) $ norm_nonneg _
      _ < r * s := mul_lt_mul_of_pos_right (hf2 p hp) hs
    calc ‖coeff p f‖ * ‖coeff q g‖ ≤ r * ‖coeff q g‖ :=
          mul_le_mul_of_nonneg_right (hf1 p) $ norm_nonneg _
      _ < r * s := mul_lt_mul_of_pos_left (hg2 q hq) hr
  refine ⟨mul_pos hr hs, fun n => ?_, fun n hn => ?_, ?_⟩
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_pos hr hs).le fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hf1 _) (hg1 _) (norm_nonneg _) hr.le
  rw [coeff_mul]
  refine gauss_norm_sum_lt _ _ (mul_pos hr hs) fun x hx => small _ _ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  omega
  have hmem : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
  have hlt : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal $ i + j).erase (i, j), coeff x.1 f * coeff x.2 g‖ < r * s := by
    refine gauss_norm_sum_lt _ _ (mul_pos hr hs) fun x hx => small _ _ ?_
    obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_contra hc
    push Not at hc
    exact hne $ Prod.ext (by simp only; omega) (by simp only; omega)
  have hij : ‖coeff i f * coeff j g‖ = r * s := by rw [norm_mul, hf3, hg3]
  rw [gauss_norm_add_of_lt $ by rwa [hij], hij]

theorem leadAt_one : LeadAt (1 : PowerSeries K) 1 0 := by
  refine ⟨one_pos, fun n => ?_, fun n hn => absurd hn $ Nat.not_lt_zero _, by simp⟩
  rw [coeff_one]
  split_ifs <;> simp

theorem leadAt_C {c : K} (hc : c ≠ 0) : LeadAt (C c : PowerSeries K) ‖c‖ 0 := by
  refine ⟨norm_pos_iff.mpr hc, fun n => ?_, fun n hn => absurd hn $ Nat.not_lt_zero _, by simp⟩
  rw [coeff_C]
  split_ifs <;> simp

theorem leadAt_factor {A : PowerSeries K} (hA : IntegralPS A) (hA0 : constantCoeff A = 1) (x : K) :
    ∃ i, i ≤ 2 ∧ LeadAt (A - C x * X ^ 2) (max 1 ‖x‖) i := by
  have hc : ∀ n, coeff n (A - C x * X ^ 2) = coeff n A - if n = 2 then x else 0 := by
    intro n
    rw [map_sub, coeff_C_mul_X_pow]
  by_cases hx : ‖x‖ ≤ 1
  refine ⟨0, by norm_num, ?_⟩
  rw [max_eq_left hx]
  refine ⟨one_pos, fun n => ?_, fun n hn => absurd hn $ Nat.not_lt_zero _, ?_⟩
  rw [hc]
  split_ifs
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le (hA n) (by rw [norm_neg]; exact hx)
  rw [sub_zero]
  exact hA n
  rw [hc, if_neg $ by norm_num, sub_zero, coeff_zero_eq_constantCoeff_apply, hA0, norm_one]
  push Not at hx
  refine ⟨2, le_rfl, ?_⟩
  rw [max_eq_right hx.le]
  have h2 : ‖coeff 2 A - x‖ = ‖x‖ := by
    rw [sub_eq_neg_add, gauss_norm_add_of_lt (by rw [norm_neg]; exact (hA 2).trans_lt hx), norm_neg]
  refine ⟨one_pos.trans hx, fun n => ?_, fun n hn => ?_, ?_⟩
  rw [hc]
  split_ifs with h
  subst h
  exact h2.le
  rw [sub_zero]
  exact (hA n).trans hx.le
  rw [hc, if_neg $ by omega, sub_zero]
  exact (hA n).trans_lt hx
  rw [hc, if_pos rfl, h2]

theorem leadAt_prod {α : Type} (S : Finset α) (x : α → K) {A : PowerSeries K} (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) :
    ∃ i, i ≤ 2 * S.card ∧ LeadAt (∏ P ∈ S, (A - C (x P) * X ^ 2)) (∏ P ∈ S, max 1 ‖x P‖) i := by
  classical
  refine Finset.induction_on S ⟨0, le_rfl, by simpa using leadAt_one⟩ ?_
  intro a T ha ih
  obtain ⟨i, hi, h⟩ := ih
  obtain ⟨j, hj, h'⟩ := leadAt_factor hA hA0 $ x a
  refine ⟨j + i, ?_, ?_⟩
  rw [Finset.card_insert_of_notMem ha]
  omega
  rw [Finset.prod_insert ha, Finset.prod_insert ha]
  exact h'.mul h

theorem gauss_bound {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K)
    (hG : IntegralPS (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))) :
    ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ ≤ 1 := by
  by_cases hc : c = 0
  simp [hc]
  obtain ⟨i, -, h⟩ := leadAt_prod S x hA hA0
  rw [← ((leadAt_C hc).mul h).2.2.2]
  exact hG _

theorem gauss_unit {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K) (hc : ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ = 1) :
    ∃ i, i ≤ 2 * S.card ∧ ‖coeff i (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))‖ = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨i, hi, h⟩ := leadAt_prod S x hA hA0
  exact ⟨0 + i, by omega, ((leadAt_C hc0).mul h).2.2.2.trans hc⟩

theorem leadAt_first_unit {g : PowerSeries K} (hg : IntegralPS g) (h : ∃ i, ‖coeff i g‖ = 1) :
    ∃ i₀, (∀ i, ‖coeff i g‖ = 1 → i₀ ≤ i) ∧ LeadAt g 1 i₀ := by
  classical
  refine ⟨Nat.find h, fun i hi => Nat.find_min' h hi, one_pos, hg,
    fun n hn => lt_of_le_of_ne (hg n) $ Nat.find_min h hn, Nat.find_spec h⟩

theorem unit_coeff_mul {f g : PowerSeries K} (hf : IntegralPS f) (hg : IntegralPS g)
    (hf0 : ‖constantCoeff f‖ = 1) (N : ℕ) (h : ∃ i, i ≤ N ∧ ‖coeff i g‖ = 1) :
    ∃ i, i ≤ N ∧ ‖coeff i (f * g)‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  obtain ⟨i₀, hmin, hl⟩ := leadAt_first_unit hg ⟨i, hi⟩
  have hf' : LeadAt f 1 0 := ⟨one_pos, hf, fun n hn => absurd hn $ Nat.not_lt_zero _,
    by rw [coeff_zero_eq_constantCoeff_apply, hf0]⟩
  refine ⟨0 + i₀, by have := hmin i hi; omega, ?_⟩
  rw [(hf'.mul hl).2.2.2, one_mul]

theorem unit_coeff_of_sq {e : PowerSeries K} (he : IntegralPS e) (N : ℕ)
    (h : ∃ i, i ≤ 2 * N ∧ ‖coeff i (e ^ 2)‖ = 1) : ∃ i, i ≤ N ∧ ‖coeff i e‖ = 1 := by
  obtain ⟨i, hiN, hi⟩ := h
  obtain ⟨j, -, hl⟩ := leadAt_first_unit he (by
      by_contra hno
      push Not at hno
      have : ‖coeff i (e ^ 2)‖ < 1 := by
        rw [sq, coeff_mul]
        refine gauss_norm_sum_lt _ _ one_pos fun x _ => ?_
        rw [norm_mul]
        calc ‖coeff x.1 e‖ * ‖coeff x.2 e‖ ≤ ‖coeff x.1 e‖ * 1 :=
              mul_le_mul_of_nonneg_left (he _) $ norm_nonneg _
          _ < 1 := by rw [mul_one]
                      exact (fun n => lt_of_le_of_ne (he n) $ hno n) _
      exact this.ne hi)
  have hm := hl.mul hl
  rw [one_mul, ← sq] at hm
  refine ⟨j, ?_, hl.2.2.2⟩
  by_contra hc
  push Not at hc
  exact (hm.2.2.1 i $ by omega).ne hi

theorem integral_of_sq_eq {e U G : PowerSeries K} (he : IntegralPS e) (he0 : constantCoeff e = 0)
    (hU : IntegralPS U) (hU0 : constantCoeff U = 1) (h : e ^ 2 = X ^ 2 * U * G) : IntegralPS G := by
  obtain ⟨e', rfl⟩ := (PowerSeries.X_dvd_iff).mpr he0
  have he' : IntegralPS e' := fun n => by
    have := he $ n + 1
    rwa [coeff_succ_X_mul] at this
  have h2 : e' ^ 2 = U * G := by
    have hX : (X : PowerSeries K) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [← mul_assoc, ← h]
    ring
  have hG : G = U⁻¹ * e' ^ 2 := by
    rw [h2, ← mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [hU0]; exact one_ne_zero), one_mul]
  rw [hG]
  exact integralPS_mul (integralPS_inv hU $ by rw [hU0, norm_one]) $ integralPS_pow he' 2

end ReciprocityTheory.ChartRestriction.L1
end
section
open IsUltrametricDist (norm_intCast_le_one norm_natCast_le_one norm_sum_le_of_forall_le_of_nonneg)
open Nat (cast_mul cast_one gcdA gcdB succ_ne_zero)
open PowerSeries (HasSubst coeff_subst coeff_subst_finite)
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

private theorem norm_finsum_le_of_forall_norm_le_univ_sort {α : Type*} (f : α → K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ a, ‖f a‖ ≤ C) :
    ‖∑ᶠ a, f a‖ ≤ C := by
  classical
  rw [finsum_def]
  split_ifs with hs
  exact norm_sum_le_of_forall_le_of_nonneg hC fun i _ => h i
  simpa using hC

private theorem mvPowerSeries_norm_coeff_mul_le_mul {ι : Type} {F G : MvPowerSeries ι K} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ a) (hG : ∀ e, ‖MvPowerSeries.coeff e G‖ ≤ b) :
    ∀ e, ‖MvPowerSeries.coeff e (F * G)‖ ≤ a * b := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun p _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) ha

private theorem mvPowerSeries_norm_coeff_pow_le_pow {ι : Type} {F : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ c) :
    ∀ m e, ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ c ^ m := by
  classical
  intro m
  induction m with
  | zero =>
    intro e
    rw [pow_zero, pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc m) hc ih hF

private theorem mvPowerSeries_norm_coeff_pow_le_one {ι : Type} {F : MvPowerSeries ι K}
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ 1) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ 1 := by
  simpa using mvPowerSeries_norm_coeff_pow_le_pow zero_le_one hF m e

private theorem mvPowerSeries_norm_coeff_pow_sub_pow_le {ι : Type} {A B : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ e, ‖MvPowerSeries.coeff e A‖ ≤ 1) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ m - B ^ m)‖ ≤ c := by
  classical
  have hs : ∀ e, ‖MvPowerSeries.coeff e (∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i))‖ ≤ 1 := by
    intro e
    rw [map_sum]
    refine norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one zero_le_one (mvPowerSeries_norm_coeff_pow_le_one hA i) (mvPowerSeries_norm_coeff_pow_le_one hB $ m - 1 - i) e
  rw [← geom_sum₂_mul]
  simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one hc hs hAB e

private theorem mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {A B : MvPowerSeries ι K}
    {c : ℝ} (hc : 0 ≤ c) (hcl : c ≤ ‖(l : K)‖) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ l - B ^ l)‖ ≤ c * ‖(l : K)‖ := by
  classical
  obtain ⟨D, rfl⟩ : ∃ D, A = D + B := ⟨A - B, by ring⟩
  simp only [add_sub_cancel_right] at hAB
  have hc1 := hcl.trans hl1.le
  have hl2 := hl.two_le
  rw [add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, cast_one, mul_one,
    add_sub_cancel_right]
  rw [map_sum]
  refine norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc $ norm_nonneg _)
    fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [← Nat.cast_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, norm_mul]
  have hterm : ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖ ≤ c ^ (i + 1) := by
    simpa using mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc _) zero_le_one (mvPowerSeries_norm_coeff_pow_le_pow hc hAB $ i + 1) (mvPowerSeries_norm_coeff_pow_le_one hB _) e
  have hch : ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) ≤ c * ‖(l : K)‖ := by
    obtain h | h : i + 1 < l ∨ i + 1 = l := by omega
    obtain ⟨q, hq⟩ := hl.dvd_choose_self (succ_ne_zero i) h
    rw [hq, cast_mul, norm_mul]
    have hq1 := norm_natCast_le_one K q
    have hpc := pow_le_of_le_one hc hc1 $ succ_ne_zero i
    calc ‖(l : K)‖ * ‖(q : K)‖ * c ^ (i + 1) ≤ ‖(l : K)‖ * 1 * c := by
          gcongr
      _ = c * ‖(l : K)‖ := by ring
    rw [h, Nat.choose_self, cast_one, norm_one, one_mul]
    obtain ⟨j, rfl⟩ : ∃ j, l = j + 2 := ⟨l - 2, by omega⟩
    calc c ^ (j + 2) = c * c ^ (j + 1) := by ring
      _ ≤ c * ‖((j + 2 : ℕ) : K)‖ := by gcongr
                                        exact (pow_le_of_le_one hc hc1 $ succ_ne_zero j).trans hcl
  calc ‖((l.choose (i + 1) : ℕ) : K)‖ * ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖
      ≤ ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) := by gcongr
    _ ≤ c * ‖(l : K)‖ := hch

private theorem mvPowerSeries_norm_coeff_pow_prime_pow_sub_le {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {P Q : MvPowerSeries ι K}
    (hQ : ∀ e, ‖MvPowerSeries.coeff e Q‖ ≤ 1)
    (hPQ : ∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖) :
    ∀ v e, ‖MvPowerSeries.coeff e (P ^ (l ^ v) - Q ^ (l ^ v))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
  intro v
  induction v with
  | zero => simpa using hPQ
  | succ v ih =>
    intro e
    rw [pow_succ, pow_mul, pow_mul, pow_succ _ $ v + 1]
    exact mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm hl hl1 (pow_nonneg (norm_nonneg _) _)
      (pow_le_of_le_one (norm_nonneg _) hl1.le $ succ_ne_zero v) (mvPowerSeries_norm_coeff_pow_le_one hQ _) ih e

private theorem norm_natCast_eq_one_of_not_prime_dvd (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {m : ℕ} (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = 1 := by
  have h1 := Nat.gcd_eq_gcd_ab l m
  rw [((Nat.coprime_or_dvd_of_prime hl m).resolve_right hm).gcd_eq_one] at h1
  have h2 : (1 : K) = (l : K) * (gcdA l m : K) + (m : K) * (gcdB l m : K) := by
    have h3 := congrArg (fun x : ℤ => (x : K)) h1
    push_cast at h3
    exact h3
  refine le_antisymm (norm_natCast_le_one K m) $ not_lt.mp fun hlt => ?_
  have h4 : ‖(1 : K)‖ < 1 := by
    rw [h2]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) $ max_lt ?_ ?_
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖((gcdA l m : ℤ) : K)‖ ≤ ‖(l : K)‖ * 1 := by
          gcongr
          exact norm_intCast_le_one K _
      _ < 1 := by simpa using hl1
    rw [norm_mul]
    calc ‖(m : K)‖ * ‖((gcdB l m : ℤ) : K)‖ ≤ ‖(m : K)‖ * 1 := by
          gcongr
          exact norm_intCast_le_one K _
      _ < 1 := by simpa using hlt
  simp at h4

theorem qls {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS $ derivative z) (P Q : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hQ0 : MvPowerSeries.constantCoeff Q = 0)
    (hP : IntegralMv P) (hQ : IntegralMv Q) (hPQ : DivByMv (l : K) $ P - Q) :
    DivByMv (l : K) $ z.subst P - z.subst Q := by
  classical
  have hPs : HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  have hQs : HasSubst Q := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  have hzi : ∀ n, ‖PowerSeries.coeff n (derivative z)‖ ≤ 1 := by
    unfold IntegralPS at hz
    exact hz
  have hpow := mvPowerSeries_norm_coeff_pow_prime_pow_sub_le hl hl1 (by
      unfold IntegralMv at hQ
      exact hQ) $ by
      unfold DivByMv at hPQ
      exact hPQ
  have hterm : ∀ d e,
      ‖PowerSeries.coeff d z • MvPowerSeries.coeff e (P ^ d) -
        PowerSeries.coeff d z • MvPowerSeries.coeff e (Q ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d e
    rw [← smul_sub, ← map_sub, norm_smul]
    rcases d with _ | k
    have h0 : PowerSeries.coeff 0 z = 0 := by
      rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [h0, norm_zero, zero_mul]
    exact norm_nonneg _
    obtain ⟨v, m, hm, hkm0⟩ := Nat.exists_eq_pow_mul_and_not_dvd (succ_ne_zero k) l hl.ne_one
    have hkm : k + 1 = l ^ v * m := hkm0
    have hz' : ‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖ ≤ 1 := by
      have h1 := hzi k
      rw [PowerSeries.coeff_derivative] at h1
      simpa [norm_mul] using h1
    have hn : ‖((k + 1 : ℕ) : K)‖ = ‖(l : K)‖ ^ v := by
      rw [hkm, cast_mul, Nat.cast_pow, norm_mul, norm_pow, norm_natCast_eq_one_of_not_prime_dvd hl hl1 hm, mul_one]
    have hPQn : ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
      rw [hkm, pow_mul, pow_mul]
      exact mvPowerSeries_norm_coeff_pow_sub_pow_le (pow_nonneg (norm_nonneg _) _) (mvPowerSeries_norm_coeff_pow_le_one (by
          unfold IntegralMv at hP
          exact hP) _) (mvPowerSeries_norm_coeff_pow_le_one (by
              unfold IntegralMv at hQ
              exact hQ) _) (hpow v) m e
    calc ‖PowerSeries.coeff (k + 1) z‖ * ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖
        ≤ ‖PowerSeries.coeff (k + 1) z‖ * ‖(l : K)‖ ^ (v + 1) := by gcongr
      _ = (‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖) * ‖(l : K)‖ := by
        rw [hn, pow_succ, mul_assoc]
      _ ≤ 1 * ‖(l : K)‖ := by gcongr
      _ = ‖(l : K)‖ := one_mul _
  unfold DivByMv
  intro e
  rw [map_sub, coeff_subst hPs, coeff_subst hQs,
    ← finsum_sub_distrib (coeff_subst_finite hPs z e)
      $ coeff_subst_finite hQs z e]
  exact norm_finsum_le_of_forall_norm_le_univ_sort _ (norm_nonneg _) fun d => hterm d e

theorem qls1 (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS $ derivative z) (P Q : PowerSeries K)
    (hP0 : constantCoeff P = 0) (hQ0 : constantCoeff Q = 0)
    (hP : IntegralPS P) (hQ : IntegralPS Q) (hPQ : DivBy (l : K) $ P - Q) :
    DivBy (l : K) $ z.subst P - z.subst Q := by
  have key : ∀ (F : PowerSeries K) (d : Unit →₀ ℕ),
      MvPowerSeries.coeff d F = PowerSeries.coeff (d ()) F := by
    intro F d
    conv_lhs => rw [Finsupp.unique_single d]
    rfl
  have hP' : IntegralMv P := by
    unfold IntegralMv
    intro d
    rw [key]
    exact hP _
  have h := qls hl hl1 z hz0 hz P Q hP0 hQ0 hP' (by
      unfold IntegralMv
      intro d
      rw [key]
      exact hQ _) $ by
      unfold DivByMv
      intro d
      rw [key]
      exact hPQ _
  unfold DivBy
  intro k
  have hk := h $ Finsupp.single () k
  rwa [key, Finsupp.single_eq_same] at hk

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Ev

variable {R : Type} [CommRing R]

def ev0 (F : MvPowerSeries (Fin 2) R) : PowerSeries R :=
  MvPowerSeries.subst ![(X : PowerSeries R), 0] F

theorem coeff_evalYZero (F : MvPowerSeries (Fin 2) R) (n : ℕ) :
    coeff n (ev0 F) = MvPowerSeries.coeff (Finsupp.single 0 n) F := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp
  have hc : ∀ f : PowerSeries R, MvPowerSeries.coeff (Finsupp.single () n) f = coeff n f := fun f => rfl
  unfold ev0
  rw [← hc, MvPowerSeries.coeff_subst ha F $ Finsupp.single () n, finsum_eq_single _ $ Finsupp.single 0 n]
  rw [Finsupp.prod_single_index $ by simp, hc]
  simp
  intro d hd
  rw [hc, Finsupp.prod_fintype _ _ fun i => by simp, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h1 : d 1 = 0
  rw [h1, pow_zero, mul_one, coeff_X_pow, if_neg, smul_zero]
  intro h0
  apply hd
  ext i
  fin_cases i
  simp [h0]
  simp [h1]
  rw [zero_pow h1, mul_zero, map_zero, smul_zero]

theorem evalYZero_add (F G : MvPowerSeries (Fin 2) R) : ev0 (F + G) = ev0 F + ev0 G := by
  unfold ev0
  rw [MvPowerSeries.subst_add (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)]

theorem evalYZero_mul (F G : MvPowerSeries (Fin 2) R) : ev0 (F * G) = ev0 F * ev0 G := by
  unfold ev0
  rw [MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)]

theorem evalYZero_subst (φ : PowerSeries R) {P : MvPowerSeries (Fin 2) R}
    (hP : MvPowerSeries.constantCoeff P = 0) : ev0 (φ.subst P) = φ.subst (ev0 P) := by
  unfold ev0
  unfold PowerSeries.subst
  exact MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hP) (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp) φ

private theorem mvPowerSeries_coeff_subst_X_eq_ite_single {S : Type} [CommRing S] {ι : Type} [DecidableEq ι] (i : ι) (f : PowerSeries S)
    (e : ι →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst (MvPowerSeries.X i : MvPowerSeries ι S)) =
      if e = Finsupp.single i (e i) then coeff (e i) f else 0 := by
  rw [PowerSeries.coeff_subst $ HasSubst.of_constantCoeff_zero $ MvPowerSeries.constantCoeff_X i]
  simp [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  split_ifs with h
  rw [finsum_eq_single _ $ e i]
  rw [if_pos h]
  intro d hd
  rw [if_neg]
  intro he
  apply hd
  rw [he, Finsupp.single_eq_same]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro d
  rw [if_neg]
  intro he
  apply h
  rw [he, Finsupp.single_eq_same]
theorem evalYZero_atX (φ : PowerSeries R) : ev0 (atX φ) = φ := by
  ext n
  rw [coeff_evalYZero]
  unfold atX
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single]
  simp

theorem evalYZero_atY (φ : PowerSeries R) : ev0 (atY φ) = C (constantCoeff φ) := by
  ext n
  rw [coeff_evalYZero, coeff_C]
  unfold atY
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  simp
  rw [if_neg $ show ¬ n = 0 by omega, if_neg]
  intro h
  have h1 := congrArg (fun e => e 0) h
  simp at h1
  omega

end Ev

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}

theorem partialYAtZero_eq (F : MvPowerSeries (Fin 2) K) : d2 F = ev0 (MvPowerSeries.pderiv 1 F) := by
  ext n
  rw [coeff_evalYZero, MvPowerSeries.coeff_pderiv]
  simp [d2]

theorem integralPS_partialYAtZero (hΦ : IntegralMv Φ) : IntegralPS $ d2 Φ := by
  unfold IntegralMv at hΦ
  unfold IntegralPS d2
  intro n
  rw [coeff_mk]
  exact hΦ _

theorem divBy_partialYAtZero {x : K} {F : MvPowerSeries (Fin 2) K} (hF : DivByMv x F) : DivBy x $ d2 F := by
  unfold DivByMv at hF
  unfold DivBy d2
  intro n
  rw [coeff_mk]
  exact hF _

theorem partialYAtZero_subst (D : PowerSeries K) {P : MvPowerSeries (Fin 2) K}
    (hP : MvPowerSeries.constantCoeff P = 0) :
    d2 (D.subst P) = (derivative D).subst (ev0 P) * d2 P := by
  rw [partialYAtZero_eq, Formalism.G.LogCR.pderiv_psubst hP, evalYZero_mul, evalYZero_subst _ hP, partialYAtZero_eq]

theorem partialYAtZero_atX (D : PowerSeries K) : d2 (atX D) = 0 := by
  ext n
  unfold d2 atX
  rw [coeff_mk, mvPowerSeries_coeff_subst_X_eq_ite_single, if_neg, map_zero]
  intro h
  have h1 := congrArg (fun e => e 1) h
  simp at h1

theorem partialYAtZero_atY (D : PowerSeries K) : d2 (atY D) = C (coeff 1 D) := by
  ext n
  unfold d2 atY
  rw [coeff_mk, mvPowerSeries_coeff_subst_X_eq_ite_single, coeff_C]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  simp
  rw [if_neg $ show ¬ n = 0 by omega, if_neg]
  intro h
  have h1 := congrArg (fun e => e 0) h
  simp at h1
  omega

theorem partialYAtZero_sub (F G : MvPowerSeries (Fin 2) K) : d2 (F - G) = d2 F - d2 G := by
  ext n
  simp [d2, PowerSeries.coeff_mk, map_sub]

theorem partialYAtZero_add (F G : MvPowerSeries (Fin 2) K) : d2 (F + G) = d2 F + d2 G := by
  ext n
  simp [d2, PowerSeries.coeff_mk, map_add]

theorem LawD.evalYZero_eq (h : LawD lam Φ) : ev0 Φ = X := by
  have hc : constantCoeff (ev0 Φ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_evalYZero, Finsupp.single_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h.Φ0
  have h1 := congrArg ev0 h.log
  rw [evalYZero_subst lam h.Φ0, evalYZero_add, evalYZero_atX, evalYZero_atY, h.lam0, map_zero, add_zero] at h1
  have hu : IsUnit $ coeff 1 lam := by rw [h.lam1]
                                       exact isUnit_one
  have he := HasSubst.of_constantCoeff_zero hc
  have h2 := PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero h.lam0) he $ lam.substInvOfIsUnit hu
  rw [PowerSeries.subst_substInvOfIsUnit_left lam h.lam0 hu, PowerSeries.subst_X he, h1,
    PowerSeries.subst_substInvOfIsUnit_left lam h.lam0 hu] at h2
  exact h2

private theorem powerSeries_subst_X_self_commRing {S : Type} [CommRing S] (t : PowerSeries S) :
    t.subst (X : PowerSeries S) = t := by
  ext n
  rw [PowerSeries.coeff_subst' $ HasSubst.of_constantCoeff_zero constantCoeff_X, finsum_eq_single _ n]
  simp
  intro d hd
  simp [coeff_X_pow, Ne.symm hd]

theorem LawD.coeffY_subst (h : LawD lam Φ) (D : PowerSeries K) :
    d2 (D.subst Φ) = derivative D * d2 Φ := by
  rw [partialYAtZero_subst D h.Φ0, h.evalYZero_eq, powerSeries_subst_X_self_commRing]

theorem LawD.deriv_mul (h : LawD lam Φ) : derivative lam * d2 Φ = 1 := by
  have h1 := congrArg d2 h.log
  rwa [h.coeffY_subst, partialYAtZero_add, partialYAtZero_atX, partialYAtZero_atY, h.lam1, zero_add, map_one] at h1

theorem LawD.deriv_const (h : LawD lam Φ) : constantCoeff (derivative lam) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
  simp [h.lam1]

theorem LawD.constantCoeff_partialYAtZero (h : LawD lam Φ) : constantCoeff (d2 Φ) = 1 := by
  have h1 := congrArg constantCoeff h.deriv_mul
  rwa [map_mul, h.deriv_const, one_mul, map_one] at h1

theorem LawD.deriv_integral (h : LawD lam Φ) : IntegralPS $ derivative lam := by
  have ha := integralPS_partialYAtZero h.Φint
  unfold IntegralPS at ha ⊢
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    simp [h.deriv_const]
    have hc := congrArg (coeff n) $ h.deriv_mul
    simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Nat.sub_self, coeff_zero_eq_constantCoeff_apply, h.constantCoeff_partialYAtZero, mul_one, coeff_one,
      if_neg $ show n ≠ 0 by omega] at hc
    have e : coeff n (derivative lam) =
        -∑ k ∈ Finset.range n, coeff k (derivative lam) * coeff (n - k) (d2 Φ) := by
      linear_combination hc
    rw [e, norm_neg]
    refine Finset.sum_induction _ (fun x => ‖x‖ ≤ 1)
      (fun x y hx hy => (IsUltrametricDist.norm_add_le_max x y).trans $ max_le hx hy)
      (by simp) fun k hk => ?_
    rw [norm_mul]
    calc ‖coeff k (derivative lam)‖ * ‖coeff (n - k) (d2 Φ)‖ ≤ 1 * 1 :=
          mul_le_mul (ih k $ Finset.mem_range.mp hk) (ha _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem hon_deriv (h : LawD lam Φ) (x : K) (D : PowerSeries K)
    (hadd : DivByMv x $ D.subst Φ - atX D - atY D) :
    DivBy x $ derivative D - C (coeff 1 D) * derivative lam := by
  have h1 := divBy_partialYAtZero hadd
  rw [partialYAtZero_sub, partialYAtZero_sub, h.coeffY_subst, partialYAtZero_atX, partialYAtZero_atY, sub_zero] at h1
  have e : derivative D - C (coeff 1 D) * derivative lam =
      derivative lam * (derivative D * d2 Φ - C (coeff 1 D)) := by
    linear_combination (-derivative D) * h.deriv_mul
  rw [e]
  have hl := h.deriv_integral
  unfold DivBy at h1 ⊢
  unfold IntegralPS at hl
  intro n
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖x‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans $ max_le ha hb)
    (by simp) fun p _ => ?_
  rw [norm_mul]
  calc ‖coeff p.1 (derivative lam)‖ * ‖coeff p.2 (derivative D * d2 Φ - C (coeff 1 D))‖
        ≤ 1 * ‖x‖ := mul_le_mul (hl _) (h1 _) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem desc_const (D : PowerSeries K) : constantCoeff (desc l D) = constantCoeff D := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    desc, PowerSeries.coeff_mk, mul_zero]

theorem desc_integral {D : PowerSeries K} (hD : IntegralPS D) : IntegralPS $ desc l D := by
  unfold IntegralPS at hD ⊢
  intro n
  rw [desc, PowerSeries.coeff_mk]
  exact hD _

theorem coeff_one_desc (D : PowerSeries K) : coeff 1 (desc l D) = coeff l D := by
  rw [desc, PowerSeries.coeff_mk, mul_one]

private theorem coeff_subst_X_pow_lemma (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
  rw [PowerSeries.coeff_subst' $ PowerSeries.HasSubst.of_constantCoeff_zero' $ by simp [hk]]
  simp [← pow_mul, PowerSeries.coeff_X_pow]
  split_ifs with hd
  obtain ⟨q, rfl⟩ := hd
  rw [finsum_eq_single _ q]
  simp [Nat.mul_div_cancel_left q $ Nat.pos_of_ne_zero hk]
  intro d hd
  have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
  simp [this]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro d
  have : m ≠ k * d := fun h => hd ⟨d, h⟩
  simp [this]

theorem desc_congr (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (D : PowerSeries K)
    (hD : DivBy (l : K) $ derivative D) :
    DivBy (l : K) (D - (desc l D).subst ((X : PowerSeries K) ^ l)) ∧
      IntegralPS (derivative $ desc l D) := by
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.mpr $ Nat.cast_ne_zero.mpr hl.ne_zero
  have hD2 : ∀ m, ‖coeff (m + 1) D‖ * ‖((m : K) + 1)‖ ≤ ‖(l : K)‖ := by
    intro m
    have h := hD m
    rwa [PowerSeries.coeff_derivative, norm_mul] at h
  constructor
  intro m
  rw [map_sub, coeff_subst_X_pow_lemma _ hl.ne_zero]
  split_ifs with hd
  obtain ⟨q, rfl⟩ := hd
  rw [desc, PowerSeries.coeff_mk, Nat.mul_div_cancel_left q hl.pos, sub_self, norm_zero]
  exact norm_nonneg _
  rw [sub_zero]
  have hm0 : m ≠ 0 := fun h => hd $ h ▸ dvd_zero l
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h1 := hD2 m'
  have hu : ‖((m' : K) + 1)‖ = 1 := by
    have h2 := norm_natCast_of_coprime hl hl1 (m' + 1) hd
    push_cast at h2
    exact h2
  rwa [hu, mul_one] at h1
  intro m
  rw [PowerSeries.coeff_derivative, desc, PowerSeries.coeff_mk, norm_mul]
  have e : l * (m + 1) - 1 + 1 = l * (m + 1) :=
    Nat.sub_add_cancel $ Nat.one_le_iff_ne_zero.mpr $ Nat.mul_ne_zero hl.ne_zero $ Nat.succ_ne_zero m
  have e2 : ((l * (m + 1) - 1 : ℕ) : K) + 1 = (l : K) * ((m : K) + 1) := by
    rw [← Nat.cast_add_one, e]
    push_cast
    ring
  have h1 := hD2 $ l * (m + 1) - 1
  rw [e2, e, norm_mul] at h1
  exact le_of_mul_le_mul_left (by linarith [h1]) hlpos

theorem desc_key {ι : Type} (hF : FrobField K l σ) {D : PowerSeries K}
    (hD0 : constantCoeff D = 0) (hD' : DivBy (l : K) $ derivative D) (P : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) $ MvPowerSeries.expand l hF.prime.ne_zero
      ((desc l D).subst (MvPowerSeries.map σ P)) - D.subst P := by
  have hl0 := hF.prime.ne_zero
  obtain ⟨h1, h2⟩ := desc_congr hF.prime hF.norm_l D hD'
  have hσP0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ P) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hP0, map_zero]
  have hPs := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.expand_subst l hl0 $ PowerSeries.HasSubst.of_constantCoeff_zero hσP0]
  have hEi : IntegralMv $ MvPowerSeries.expand l hl0 $ MvPowerSeries.map σ P := by
    rw [integralMv_iff_divBy_one, divByMv_expand_iff, ← integralMv_iff_divBy_one]
    exact hF.integralMv_map hP
  have hPl0 : MvPowerSeries.constantCoeff (P ^ l) = 0 := by
    rw [map_pow, hP0, zero_pow hl0]
  have h3 := qls hF.prime hF.norm_l (desc l D) (by rw [desc_const, hD0]) h2
    (MvPowerSeries.expand l hl0 $ MvPowerSeries.map σ P) (P ^ l) (by rw [MvPowerSeries.constantCoeff_expand, hσP0]) hPl0 hEi
    (integralMv_pow hP l) $ by
      have := divByMv_neg $ FrobCongr_valid K l l hl0 σ hF.funEqSetting ι P hP
      rwa [neg_sub] at this
  have h4 : (desc l D).subst (P ^ l) =
      PowerSeries.subst P ((desc l D).subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) hPs,
      PowerSeries.subst_pow hPs, PowerSeries.subst_X hPs]
  have h5 := divByMv_subst h1 hP0 hP
  rw [PowerSeries.subst_sub hPs, ← h4] at h5
  have := divByMv_sub h3 h5
  rwa [sub_sub_sub_cancel_right] at this

theorem desc_QCls (hF : FrobField K l σ) {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {b : K}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (hΦ : IntegralMv Φ) (hA0 : constantCoeff A = 0)
    (hA : IntegralPS A) (hb : ‖b‖ ≤ 1) {D : PowerSeries K} (hD : QCls l Φ A b D)
    (hD' : DivBy (l : K) $ derivative D) :
    QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) b $ desc l D := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  refine ⟨by rw [desc_const, hD.D0], (desc_congr hF.prime hF.norm_l D hD').2, ?_, ?_⟩
  rw [← divByMv_expand_iff _ l hl0, map_sub, map_sub]
  have h2 := desc_key hF hD.D0 hD' (MvPowerSeries.X (0 : Fin 2)) (by simp) $ integralMv_X _
  have h3 := desc_key hF hD.D0 hD' (MvPowerSeries.X (1 : Fin 2)) (by simp) $ integralMv_X _
  rw [MvPowerSeries.map_X] at h2 h3
  convert (divByMv_add (divByMv_sub (divByMv_sub (desc_key hF hD.D0 hD' Φ hΦ0 hΦ) h2) h3) hD.add) using 1
  simp [atX, atY]
  ring
  rw [divBy_iff_mv, ← divByMv_expand_iff _ l hl0, map_sub, map_mul]
  have h2 := desc_key hF hD.D0 hD' (ι := Unit) (X : PowerSeries K) (by simp [PowerSeries.X])
    $ (integralPS_iff_mv _).1 integralPS_X
  rw [show MvPowerSeries.map σ (X : PowerSeries K) = (X : PowerSeries K) from PowerSeries.map_X σ,
    PowerSeries.X_subst, PowerSeries.X_subst] at h2
  have hC : MvPowerSeries.expand l hl0 (C b : PowerSeries K) = (C b : PowerSeries K) :=
    PowerSeries.expand_C l hl0 b
  rw [hC]
  convert (divByMv_add (divByMv_sub (desc_key hF hD.D0 hD' (ι := Unit) A hA0 $ (integralPS_iff_mv A).1 hA) $ divByMv_mul_left ((integralPS_iff_mv _).1 $ integralPS_C hb) h2) $ (divBy_iff_mv _ _).1 hD.eig) using 1
  simp [PowerSeries.map]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}

theorem homE_coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R) (ha : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by
  rw [PowerSeries.coeff_subst' $ HasSubst.of_constantCoeff_zero ha, finsum_eq_single _ 1]
  simp [smul_eq_mul]
  intro d hd
  rcases Nat.lt_or_gt_of_ne hd with h | h
  have : d = 0 := by omega
  subst this
  simp
  have h2 : X ^ d ∣ a ^ d := pow_dvd_pow_of_dvd (X_dvd_iff.mpr ha) d
  simp [X_pow_dvd_iff.mp h2 1 h]

private theorem mvPowerSeries_coeff_subst_X_eq_ite_single__b12 {S : Type} [CommRing S] {ι : Type} [DecidableEq ι] (i : ι) (f : PowerSeries S)
    (e : ι →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst (MvPowerSeries.X i : MvPowerSeries ι S)) =
      if e = Finsupp.single i (e i) then coeff (e i) f else 0 := by
  rw [PowerSeries.coeff_subst $ HasSubst.of_constantCoeff_zero $ MvPowerSeries.constantCoeff_X i]
  simp [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  split_ifs with h
  rw [finsum_eq_single _ $ e i]
  rw [if_pos h]
  intro d hd
  rw [if_neg]
  intro he
  apply hd
  rw [he, Finsupp.single_eq_same]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro d
  rw [if_neg]
  intro he
  apply h
  rw [he, Finsupp.single_eq_same]
theorem homE_norm_coeff_atX_mul_atY {x : K} (a b : PowerSeries K) (ha : IntegralPS a)
    (hb : ‖coeff 1 b‖ ≤ ‖x‖) (n : ℕ) :
    ‖MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) (atX a * atY b)‖ ≤ ‖x‖ := by
  unfold IntegralPS at ha
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖x‖)
    (fun u v hu hv => (IsUltrametricDist.norm_add_le_max u v).trans $ max_le hu hv)
    (by simp) fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  unfold atX atY
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single__b12, mvPowerSeries_coeff_subst_X_eq_ite_single__b12]
  split_ifs with h1 h2
  have e1 := congrArg (fun f => f 1) hp
  simp [Finsupp.add_apply] at e1
  rw [h1] at e1
  simp at e1
  rw [norm_mul, e1]
  calc ‖coeff (p.1 0) a‖ * ‖coeff 1 b‖ ≤ 1 * ‖x‖ :=
        mul_le_mul (ha _) hb (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _
  all_goals simp

theorem homE_norm_coeff_one_pow {x : K} (hg0 : constantCoeff g = 0) (h0 : ‖coeff 1 g‖ ≤ ‖x‖) (j : ℕ) :
    ‖coeff 1 (g ^ j)‖ ≤ ‖x‖ := by
  rcases j with _ | _ | j
  simp
  simpa using h0
  have hX : X ∣ g := X_dvd_iff.mpr hg0
  rw [X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX $ j + 1 + 1) 1 $ by omega, norm_zero]
  exact norm_nonneg _

theorem divBy_partialYAtZero_subst_atX_atY {x : K} (hΦ₂ : IntegralMv Φ₂) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) (h0 : ‖coeff 1 g‖ ≤ ‖x‖) :
    DivBy x $ d2 $ Φ₂.subst ![atX g, atY g] := by
  intro n
  have hP' : MvPowerSeries.HasSubst ![atX g, atY g] := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => ?_
    fin_cases i
    exact PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg0
    exact PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg0
  rw [d2, coeff_mk, MvPowerSeries.coeff_subst hP']
  refine Formalism.LT.LTL.norm_finsum_le' (norm_nonneg _) fun m => ?_
  rw [smul_eq_mul, norm_mul, Finsupp.prod_fintype _ _ $ by simp, Fin.prod_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [atX, atY, ← PowerSeries.subst_pow $ PowerSeries.HasSubst.X 0, ← PowerSeries.subst_pow $ PowerSeries.HasSubst.X 1]
  have := homE_norm_coeff_atX_mul_atY (g ^ m 0) (g ^ m 1) (integralPS_pow hg _)
    (homE_norm_coeff_one_pow hg0 h0 _) n
  exact (mul_le_mul (hΦ₂ m) this (norm_nonneg _) zero_le_one).trans_eq $ one_mul _

theorem hom_deriv (hl1 : ‖(l : K)‖ ≤ 1) (h₁ : LawD lam₁ Φ₁) (h₂ : LawD lam₂ Φ₂)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h0 : ‖coeff 1 g‖ ≤ ‖(l : K)‖) :
    DivBy (l : K) $ derivative g := by
  have h1 := divBy_partialYAtZero hg.add
  rw [partialYAtZero_sub, h₁.coeffY_subst] at h1
  have h2 := divBy_partialYAtZero_subst_atX_atY (x := (l : K)) h₂.Φint hg.g0 hg.gInt h0
  have h3 : DivBy (l : K) $ derivative g * d2 Φ₁ := by
    unfold DivBy at h1 h2 ⊢
    intro n
    have h4 := IsUltrametricDist.norm_add_le_max
      (coeff n $ derivative g * d2 Φ₁ - d2 (Φ₂.subst ![atX g, atY g]))
      $ coeff n $ d2 $ Φ₂.subst ![atX g, atY g]
    rw [← map_add, sub_add_cancel] at h4
    exact h4.trans $ max_le (h1 n) $ h2 n
  have e : derivative g = derivative lam₁ * (derivative g * d2 Φ₁) := by
    linear_combination (-derivative g) * h₁.deriv_mul
  rw [e]
  have hl := h₁.deriv_integral
  unfold DivBy at h3 ⊢
  unfold IntegralPS at hl
  intro n
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖(l : K)‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans $ max_le ha hb)
    (by simp) fun p _ => ?_
  rw [norm_mul]
  calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul (hl _) (h3 _) (norm_nonneg _) zero_le_one
    _ = ‖(l : K)‖ := one_mul _

theorem hom_eigen (hA₁ : constantCoeff A₁ = 0) (hA₂ : constantCoeff A₂ = 0)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h : ‖coeff 1 A₁ - coeff 1 A₂‖ = 1) :
    ‖coeff 1 g‖ ≤ ‖(l : K)‖ := by
  have h0 := hg.eig
  unfold DivBy at h0
  have h1 := h0 1
  have e : coeff 1 g * coeff 1 A₁ - coeff 1 A₂ * coeff 1 g =
      coeff 1 g * (coeff 1 A₁ - coeff 1 A₂) := by ring
  rw [map_sub, homE_coeff_one_subst _ _ hA₁, homE_coeff_one_subst _ _ hg.g0, e, norm_mul, h,
    mul_one] at h1
  exact h1

theorem homE_expand_subst_map_congr {ι : Type} (hF : FrobField K l σ) {g₁ : PowerSeries K}
    (hg₁ : IntegralPS g₁) (hc : DivBy (l : K) $ g - g₁.subst ((X : PowerSeries K) ^ l))
    (P : MvPowerSeries ι K) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) $ MvPowerSeries.expand l hF.prime.ne_zero (g₁.subst (MvPowerSeries.map σ P))
      - g.subst P := by
  have hl0 := hF.prime.ne_zero
  have hσ0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ P) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hP0, map_zero]
  have hPs := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.of_constantCoeff_zero hσ0) g₁]
  have T1 : DivByMv (l : K) $ g₁.subst (MvPowerSeries.expand l hl0 $ MvPowerSeries.map σ P)
      - g₁.subst (P ^ l) := by
    refine divByMv_subst_congr hF.norm_l.le hg₁ ?_ ?_ ?_ (integralMv_pow hP l) ?_
    rw [MvPowerSeries.constantCoeff_expand, hσ0]
    rw [map_pow, hP0, zero_pow hl0]
    exact (integralMv_iff_divBy_one _).2 $ (divByMv_expand_iff 1 l hl0 _).2
      $ (integralMv_iff_divBy_one _).1 $ hF.integralMv_map hP
    rw [← neg_sub]
    exact divByMv_neg $ Formalism.LT.FrobCongr_valid K l l hl0 σ hF.funEqSetting ι P hP
  have T2 : g₁.subst (P ^ l) = PowerSeries.subst P (g₁.subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) hPs,
      PowerSeries.subst_pow hPs, PowerSeries.subst_X hPs]
  have T3 : DivByMv (l : K) $ PowerSeries.subst P (g₁.subst ((X : PowerSeries K) ^ l) : PowerSeries K) - g.subst P := by
    rw [← PowerSeries.subst_sub hPs]
    refine divByMv_subst ?_ hP0 hP
    rw [← neg_sub]
    exact divBy_neg hc
  rw [T2] at T1
  have := divByMv_add T1 T3
  rwa [sub_add_sub_cancel] at this

theorem homE_vec_const {f : PowerSeries K} (hf0 : constantCoeff f = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff (![atX f, atY f] i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  fin_cases i <;> simp [atX, atY, mvPowerSeries_coeff_subst_X_eq_ite_single__b12, hf0]

theorem homE_vec_integral {f : PowerSeries K} (hf : IntegralPS f) (i : Fin 2) :
    IntegralMv $ ![atX f, atY f] i := by
  unfold IntegralPS at hf
  unfold IntegralMv
  intro e
  fin_cases i <;> simp [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, atX, atY, mvPowerSeries_coeff_subst_X_eq_ite_single__b12]
  all_goals split_ifs
  all_goals first | exact hf _ | simp

theorem homE_vec_divBy {x : K} {f h : PowerSeries K} (hfh : DivBy x (f - h)) (i : Fin 2) :
    DivByMv x $ ![atX f, atY f] i - ![atX h, atY h] i := by
  unfold DivBy at hfh
  unfold DivByMv
  intro e
  fin_cases i <;> simp [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, atX, atY, map_sub, mvPowerSeries_coeff_subst_X_eq_ite_single__b12]
  all_goals split_ifs
  all_goals first | (rw [← map_sub]; exact hfh _) | simp

theorem homE_expand_subst_X (hl0 : l ≠ 0) (f : PowerSeries K) (i : Fin 2) :
    MvPowerSeries.expand l hl0 (f.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)
        (f.subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
  rw [PowerSeries.expand_subst l hl0 $ PowerSeries.HasSubst.X i, MvPowerSeries.expand_X,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) $ PowerSeries.HasSubst.X i,
    PowerSeries.subst_pow $ PowerSeries.HasSubst.X i, PowerSeries.subst_X $ PowerSeries.HasSubst.X i]

theorem hom_desc (hF : FrobField K l σ) (hΦ₁0 : MvPowerSeries.constantCoeff Φ₁ = 0)
    (hΦ₁ : IntegralMv Φ₁) (hΦ₂0 : MvPowerSeries.constantCoeff Φ₂ = 0) (hΦ₂ : IntegralMv Φ₂)
    (hA₁0 : constantCoeff A₁ = 0) (hA₁ : IntegralPS A₁) (hA₂0 : constantCoeff A₂ = 0)
    (hA₂ : IntegralPS A₂) (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (hg' : DivBy (l : K) $ derivative g) :
    DivBy (l : K) (g - (desc l g).subst ((X : PowerSeries K) ^ l)) ∧
      HomCls l (MvPowerSeries.map σ Φ₁) (PowerSeries.map σ A₁) Φ₂ A₂ (desc l g) := by
  have hl0 := hF.prime.ne_zero
  have hc := (desc_congr hF.prime hF.norm_l g hg').1
  use hc
  have hg₁0 : constantCoeff (desc l g) = 0 := by rw [desc_const, hg.g0]
  have hg₁ : IntegralPS $ desc l g := desc_integral hg.gInt
  generalize desc l g = g₁ at hc hg₁0 hg₁ ⊢
  obtain ⟨E, hE⟩ : ∃ E, E = g₁.subst ((X : PowerSeries K) ^ l) := ⟨_, rfl⟩
  have hE0 : constantCoeff E = 0 := by
    rw [hE]
    exact PowerSeries.constantCoeff_subst_eq_zero
      (by rw [map_pow]; exact (congrArg (· ^ l) $ constantCoeff_X (R := K)).trans $ zero_pow hl0) g₁ hg₁0
  have hEint : IntegralPS E := by
    rw [hE]
    exact (integralPS_iff_divBy_one _).2 $ (divBy_expand_iff 1 l hl0 g₁).2
      $ (integralPS_iff_divBy_one _).1 hg₁
  have hc' : DivBy (l : K) $ g - E := by rw [hE]
                                         exact hc
  refine ⟨hg₁0, hg₁, ?_, ?_⟩
  rw [← divByMv_expand_iff (l : K) l hl0, map_sub]
  have hex : MvPowerSeries.expand l hl0 (Φ₂.subst ![atX g₁, atY g₁]) =
      Φ₂.subst ![atX E, atY E] := by
    rw [MvPowerSeries.expand_subst l hl0 $ MvPowerSeries.hasSubst_of_constantCoeff_zero $ homE_vec_const hg₁0]
    congr 1
    funext i
    fin_cases i
    show MvPowerSeries.expand l hl0 (atX g₁) = atX E
    rw [atX, atX, homE_expand_subst_X hl0, hE]
    show MvPowerSeries.expand l hl0 (atY g₁) = atY E
    rw [atY, atY, homE_expand_subst_X hl0, hE]
  have T5 :=
    divByMv_subst2_congr hF.norm_l.le hΦ₂ (homE_vec_const hg.g0) (homE_vec_const hE0)
      (homE_vec_integral hg.gInt) (homE_vec_integral hEint) $ homE_vec_divBy hc'
  rw [hex]
  have := divByMv_add (divByMv_add (homE_expand_subst_map_congr hF hg₁ hc Φ₁ hΦ₁0 hΦ₁) hg.add) T5
  rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
  rw [divBy_iff_mv, ← divByMv_expand_iff (l : K) l hl0, map_sub]
  have hex : MvPowerSeries.expand l hl0 (A₂.subst g₁) = A₂.subst E := by
    rw [PowerSeries.expand_subst l hl0 $ PowerSeries.HasSubst.of_constantCoeff_zero' hg₁0, hE]
    congr 1
    exact PowerSeries.expand_apply l hl0 g₁
  have T5 := divByMv_subst_congr (ι := Unit) hF.norm_l.le hA₂ hg.g0 hE0 ((integralPS_iff_mv _).1 hg.gInt)
      ((integralPS_iff_mv _).1 hEint) $ (divBy_iff_mv _ _).1 hc'
  rw [hex]
  have := divByMv_add (divByMv_add (homE_expand_subst_map_congr (ι := Unit) hF hg₁ hc A₁ hA₁0 $ (integralPS_iff_mv _).1 hA₁) $ (divBy_iff_mv _ _).1 hg.eig) T5
  rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Tools

variable {R : Type} [CommRing R]


theorem coeffOne_subst_zero {f s : PowerSeries R} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by
  rw [PowerSeries.coeff_subst' $ HasSubst.of_constantCoeff_zero hs, finsum_eq_single _ 1]
  simp [smul_eq_mul]
  intro d hd
  rcases Nat.lt_or_gt_of_ne hd with h | h
  have : d = 0 := by omega
  subst this
  simp
  have h2 : X ^ d ∣ s ^ d := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hs) d
  simp [X_pow_dvd_iff.mp h2 1 h]

theorem subst_C_mul_mv {ι : Type} {P : MvPowerSeries ι R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = MvPowerSeries.C c * f.subst P := by
  rw [← smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

theorem subst_C_mul_ps {P : PowerSeries R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = C c * f.subst P := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

end Tools

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.map (hF : FrobField K l σ) (h : LawD lam Φ) :
    LawD (PowerSeries.map σ lam) $ MvPowerSeries.map σ Φ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.lam0,
    map_zero]
  rw [coeff_map, h.lam1, map_one]
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  have h1 := h.Φint
  unfold IntegralMv at h1 ⊢
  intro e
  rw [MvPowerSeries.coeff_map, hF.isom]
  exact h1 e
  have h1 := congrArg (MvPowerSeries.map σ) h.log
  unfold atX atY at h1 ⊢
  rw [map_add] at h1
  erw [PowerSeries.map_subst $ HasSubst.of_constantCoeff_zero h.Φ0,
    PowerSeries.map_subst $ HasSubst.of_constantCoeff_zero $ MvPowerSeries.constantCoeff_X 0,
    PowerSeries.map_subst $ HasSubst.of_constantCoeff_zero $ MvPowerSeries.constantCoeff_X 1,
    MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
  exact h1

theorem HD.map (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) $ σ a := by
  refine ⟨h.toLawD.map hF, ?_, ?_, ?_, ?_, ?_⟩
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.A0,
    map_zero]
  have h1 := h.Aint
  unfold IntegralPS at h1 ⊢
  intro n
  rw [coeff_map, hF.isom]
  exact h1 n
  have h1 := congrArg (PowerSeries.map σ) h.Alog
  erw [PowerSeries.map_subst $ HasSubst.of_constantCoeff_zero h.A0] at h1
  rwa [map_mul, map_C] at h1
  rw [h.a_sq, norm_sub_rev]
  exact h.a_ne
  rw [h.a_sq]

theorem HD.coeff_one_A (h : HD σ lam Φ A a) : coeff 1 A = a := by
  have h1 := congrArg (coeff 1) h.Alog
  rwa [coeffOne_subst_zero h.A0, coeff_C_mul, h.lam1, one_mul, mul_one] at h1

theorem HD.norm_a (h : HD σ lam Φ A a) : ‖a‖ ≤ 1 := by
  have h1 := h.Aint
  unfold IntegralPS at h1
  rw [← h.coeff_one_A]
  exact h1 1


theorem eigen_trick {A : PowerSeries K} {b : K} (hA0 : constantCoeff A = 0) (D : PowerSeries K)
    (hD0 : constantCoeff D = 0) (h : DivBy (l : K) $ D.subst A - C b * D)
    (hb : ‖coeff 1 A - b‖ = 1) : ‖coeff 1 D‖ ≤ ‖(l : K)‖ := by
  have h0 := h
  unfold DivBy at h0
  have h1 := h0 1
  have e : coeff 1 D * coeff 1 A - b * coeff 1 D = coeff 1 D * (coeff 1 A - b) := by ring
  rwa [map_sub, coeffOne_subst_zero hA0, coeff_C_mul, e, norm_mul, hb, mul_one] at h1


theorem divBy_C_mul' {x c : K} (hc : ‖c‖ ≤ ‖x‖) {f : PowerSeries K} (hf : IntegralPS f) :
    DivBy x $ C c * f := by
  unfold DivBy IntegralPS at *
  intro n
  rw [coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖coeff n f‖ ≤ ‖x‖ * 1 := mul_le_mul hc (hf n) (norm_nonneg _) (norm_nonneg _)
    _ = ‖x‖ := mul_one _

theorem derivative_C_mul' (c : K) (f : PowerSeries K) :
    derivative (C c * f) = C c * derivative f := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul]

theorem QCls.norm_coeff_one {b : K} {D : PowerSeries K} (hD : QCls l Φ A b D) :
    ‖coeff 1 D‖ ≤ 1 := by
  have h0 := hD.dInt
  unfold IntegralPS at h0
  have h1 := h0 0
  rw [coeff_derivative] at h1
  simpa using h1

theorem HD.qcls_sub (h : HD σ lam Φ A a) {D : PowerSeries K} (hD : QCls l Φ A a D) :
    QCls l Φ A a $ D - C (coeff 1 D) * lam := by
  set c := coeff 1 D with hc
  have hΦ : HasSubst Φ := HasSubst.of_constantCoeff_zero h.Φ0
  have hA : HasSubst A := HasSubst.of_constantCoeff_zero h.A0
  have hX0 : HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero $ MvPowerSeries.constantCoeff_X 0
  have hX1 : HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero $ MvPowerSeries.constantCoeff_X 1
  have sub_subst : ∀ {P : MvPowerSeries (Fin 2) K} (_ : HasSubst P) (f g : PowerSeries K),
      (f - g).subst P = f.subst P - g.subst P := fun hP f g => by
    rw [← coe_substAlgHom hP, map_sub]
  have sub_substA : (D - C c * lam).subst A = D.subst A - C c * lam.subst A := by
    rw [← coe_substAlgHom hA, map_sub, coe_substAlgHom hA, subst_C_mul_ps hA]
  refine ⟨?_, ?_, ?_, ?_⟩
  simp [hD.D0, h.lam0]
  have hd := hD.dInt
  have hl := h.toLawD.deriv_integral
  unfold IntegralPS at hd hl ⊢
  intro n
  rw [map_sub, derivative_C_mul', map_sub, coeff_C_mul, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le (hd n) ?_
  rw [norm_neg, norm_mul]
  calc ‖c‖ * ‖coeff n (derivative lam)‖ ≤ 1 * 1 :=
        mul_le_mul (hD.norm_coeff_one) (hl n) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1
  have e : (D - C c * lam).subst Φ - atX (D - C c * lam) - atY (D - C c * lam) =
      (D.subst Φ - atX D - atY D) - MvPowerSeries.C c * (lam.subst Φ - atX lam - atY lam) := by
    unfold atX atY
    rw [sub_subst hΦ, sub_subst hX0, sub_subst hX1, subst_C_mul_mv hΦ, subst_C_mul_mv hX0,
      subst_C_mul_mv hX1]
    ring
  have e2 : lam.subst Φ - atX lam - atY lam = 0 := by rw [h.log]
                                                      ring
  rw [e, e2, mul_zero, sub_zero]
  exact hD.add
  have e : (D - C c * lam).subst A - C a * (D - C c * lam) = D.subst A - C a * D := by
    rw [sub_substA, h.Alog]
    ring
  rw [e]
  exact hD.eig

theorem lemmaQ (hF : FrobField K l σ) (h : HD σ lam Φ A a) {D : PowerSeries K}
    (hD : QCls l Φ A a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * lam - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl0 := hF.prime.ne_zero
  set E : PowerSeries K := D - C (coeff 1 D) * lam with hE
  have hE' : DivBy (l : K) $ derivative E := by
    have := hon_deriv h.toLawD (l : K) D hD.add
    rwa [hE, map_sub, derivative_C_mul']
  have h1 :=
    desc_QCls hF h.Φ0 h.Φint h.A0 h.Aint h.norm_a (h.qcls_sub hD) hE'
  have hσ := h.map hF
  have hs := eigen_trick hσ.A0 _ h1.D0 h1.eig (by rw [hσ.coeff_one_A]; exact h.a_ne)
  have h1' : DivBy (l : K) $ derivative $ desc l E := by
    have h2 := hon_deriv hσ.toLawD (l : K) _ h1.add
    have h3 := divBy_add h2 $ divBy_C_mul' hs hσ.toLawD.deriv_integral
    rwa [sub_add_cancel] at h3
  refine ⟨desc l $ desc l E, ?_, ?_⟩
  have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
    ext d
    simp
  have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
    ext d
    simp
  rw [e1, e2]
  exact desc_QCls hF hσ.Φ0 hσ.Φint hσ.A0 hσ.Aint h.norm_a h1 h1'
  have hXl : HasSubst $ (X : PowerSeries K) ^ l :=
    HasSubst.of_constantCoeff_zero' $ by simp [hl0]
  have c3 := (divBy_expand_iff (l : K) l hl0 _).2 $ (desc_congr hF.prime hF.norm_l _ h1').1
  rw [subst_sub hXl, subst_comp_subst_apply hXl hXl, subst_pow hXl, subst_X hXl, ← pow_mul,
    ← sq] at c3
  have c4 := divBy_add ((desc_congr hF.prime hF.norm_l E hE').1) c3
  rwa [sub_add_sub_cancel] at c4

end ReciprocityTheory.ChartRestriction.L1
end
section
open Finset (range sum_range_one)
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

def triSol {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) : ℕ → K
  | m => (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m

theorem triSol_eq {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) (ha : ∀ m, a m m ≠ 0)
    (m : ℕ) : ∑ i ∈ range (m + 1), triSol a b i * a i m = b m := by
  have h : triSol a b m = (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m := by
    rw [triSol]
  rw [Finset.sum_range_succ, Finset.sum_range, h, div_mul_cancel₀ _ $ ha m]
  ring

theorem triSol_norm (a : ℕ → ℕ → K) (b : ℕ → K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (r : ℝ) (hb : ∀ m, ‖b m‖ ≤ r) (m : ℕ) : ‖triSol a b m‖ ≤ r := by
  have hr := (norm_nonneg _).trans $ hb 0
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [triSol, norm_div, ha, div_one, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le (hb m) ?_
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun i _ => ?_
    rw [norm_mul]
    calc ‖triSol a b i.1‖ * ‖a i.1 m‖ ≤ r * 1 :=
          mul_le_mul (ih i.1 i.2) (ha1 _ _) (norm_nonneg _) hr
      _ = r := mul_one r

theorem norm_pow_apply_of_isometric (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hτ, ih]

def triIter {K : Type} [Field K] (a : ℕ → ℕ → K) (π : K) : ℕ → ℕ → K
  | 0 => triSol a fun m => if m = 0 then a 0 0 else 0
  | k + 1 => triSol a fun m => if m = 0 then 0 else π * triIter a π k (m + 1)

theorem triIter_norm (a : ℕ → ℕ → K) (π : K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (k m : ℕ) : ‖triIter a π k m‖ ≤ ‖π‖ ^ k := by
  induction k generalizing m with
  | zero =>
    rw [triIter, pow_zero]
    refine triSol_norm a _ ha1 ha 1 (fun j => ?_) m
    split_ifs
    exact ha1 0 0
    simp
  | succ k ih =>
    rw [triIter]
    refine triSol_norm a _ ha1 ha _ (fun j => ?_) m
    split_ifs
    simp
    rw [norm_mul, pow_succ']
    exact mul_le_mul_of_nonneg_left (ih _) $ norm_nonneg _

theorem twisted_division (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (hπ : ‖π‖ < 1)
    (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ range n, t i * (τ ^ i) (c $ n - 1 - i) := by
  set a : ℕ → ℕ → K := fun i m => (τ ^ i) (c $ m - i) with ha_def
  have ha1 : ∀ i m, ‖a i m‖ ≤ 1 := fun i m => by
    rw [ha_def]
    simp only; rw [norm_pow_apply_of_isometric τ hτ]; exact hc _
  have ha : ∀ m, ‖a m m‖ = 1 := fun m => by
    rw [ha_def]
    simp only; rw [norm_pow_apply_of_isometric τ hτ, Nat.sub_self]; exact hc0
  have ha0 : ∀ m, a m m ≠ 0 := fun m h => by
    have := ha m
    rw [h, norm_zero] at this; exact zero_ne_one this
  have hsum : ∀ m, Summable fun k => triIter a π k m := fun m =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg π) hπ)
      fun k => triIter_norm a π ha1 ha k m
  have hz0 : triIter a π 0 0 = 1 := by
    have h := triSol_eq a (if · = 0 then a 0 0 else 0) ha0 0
    simp only [zero_add, sum_range_one, if_true] at h
    rw [triIter]
    exact mul_right_cancel₀ (ha0 0) $ h.trans (one_mul _).symm
  have hzs : ∀ k, triIter a π (k + 1) 0 = 0 := fun k => by
    have h := triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 0
    simp only [zero_add, sum_range_one, if_true] at h
    rw [triIter]
    exact (mul_eq_zero.mp h).resolve_right $ ha0 0
  refine ⟨fun m => ∑' k, triIter a π k m, ?_, fun n => ?_, fun n hn => ?_⟩
  simp only
  rw [(hsum 0).tsum_eq_zero_add, hz0]
  simp [hzs]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun k => ?_
  exact (triIter_norm a π ha1 ha k n).trans $ pow_le_one₀ (norm_nonneg _) hπ.le
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hterm : ∀ i, (∑' k, triIter a π k i) * (τ ^ i) (c $ m + 2 - 1 - i)
      = ∑' k, triIter a π k i * a i (m + 1) := fun i => by
    rw [tsum_mul_right]
    rfl
  simp only [hterm]
  rw [← Summable.tsum_finsetSum fun i _ => (hsum i).mul_right _]
  have hS : Summable fun k => ∑ i ∈ range (m + 2), triIter a π k i * a i (m + 1) :=
    summable_sum fun i _ => (hsum i).mul_right _
  rw [hS.tsum_eq_zero_add, ← tsum_mul_left]
  have h0 : ∑ i ∈ range (m + 2), triIter a π 0 i * a i (m + 1) = 0 := by
    simpa [triIter] using (triSol_eq a (if · = 0 then a 0 0 else 0) ha0 $ m + 1)
  rw [h0, zero_add]
  refine tsum_congr fun k => ?_
  simpa [triIter] using (triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 $ m + 1).symm

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem powerSeries_subst_subst_of_constantCoeff_zero {R : Type} [CommRing R] {α β : Type} (φ : PowerSeries R)
    {u : MvPowerSeries α R} (hu : MvPowerSeries.constantCoeff u = 0) {b : α → MvPowerSeries β R}
    (hb : MvPowerSeries.HasSubst b) : (φ.subst u).subst b = φ.subst (u.subst b) := by
  rw [PowerSeries.subst, PowerSeries.subst]
  first
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.of_constantCoeff_zero fun _ => hu) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hu) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ((PowerSeries.HasSubst.of_constantCoeff_zero hu).hasSubst) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ⟨fun _ => by rw [hu]; exact IsNilpotent.zero, by simp⟩ hb φ

theorem mulN_integral {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} (h : LawD lam Φ) (n : ℕ) :
    ∃ e : PowerSeries K, constantCoeff e = 0 ∧ IntegralPS e ∧ lam.subst e = C (n : K) * lam := by
  have hXs : lam.subst (X : PowerSeries K) = lam := by
    have ha1 : PowerSeries.HasSubst (X : PowerSeries K) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X
    ext m
    rw [PowerSeries.coeff_subst' ha1, finsum_eq_single _ m]
    rw [PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]
    intro d hd
    rw [PowerSeries.coeff_X_pow, if_neg $ Ne.symm hd, smul_zero]
  induction n with
  | zero =>
    refine ⟨0, map_zero _, by unfold IntegralPS; intro k; simp, ?_⟩
    ext k
    rw [PowerSeries.coeff_subst' $ PowerSeries.HasSubst.of_constantCoeff_zero' $ map_zero _,
      Nat.cast_zero, map_zero, zero_mul, map_zero]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, zero_smul]
    rw [zero_pow hd.ne', map_zero, smul_zero]
  | succ n ih =>
    obtain ⟨e, he0, he, hlog⟩ := ih
    have hP0 : ∀ s, MvPowerSeries.constantCoeff ((![e, X] : Fin 2 → PowerSeries K) s) = 0 := by
      intro s
      fin_cases s
      exact he0
      exact PowerSeries.constantCoeff_X
    have hPint : ∀ s, IntegralMv $ (![e, X] : Fin 2 → PowerSeries K) s := by
      intro s
      fin_cases s
      exact (integralPS_iff_mv e).mp he
      exact (integralPS_iff_mv _).mp integralPS_X
    have ha : MvPowerSeries.HasSubst (![e, X] : Fin 2 → PowerSeries K) :=
      ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    refine ⟨Φ.subst (![e, X] : Fin 2 → PowerSeries K), ?_, ?_, ?_⟩
    have h0 : MvPowerSeries.constantCoeff (Φ.subst (![e, X] : Fin 2 → PowerSeries K)) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst ha]
      apply finsum_eq_zero_of_forall_eq_zero
      intro d
      by_cases hd : d = 0
      rw [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, zero_smul]
      obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hd $ Finsupp.ext hc
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) $ by rw [map_pow, hP0 s, zero_pow hs],
        smul_zero]
    exact h0
    exact (integralPS_iff_mv _).mpr $ integralMv_subst2 h.Φint hP0 hPint
    rw [← powerSeries_subst_subst_of_constantCoeff_zero lam h.Φ0 ha, h.log]
    unfold atX atY
    first
    | rw [MvPowerSeries.subst_add ha]
    | rw [← MvPowerSeries.coe_substAlgHom ha, map_add, MvPowerSeries.coe_substAlgHom]
    rw [powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 0) ha,
      powerSeries_subst_subst_of_constantCoeff_zero lam (MvPowerSeries.constantCoeff_X 1) ha,
      MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hlog, hXs, Nat.cast_succ, map_add, map_one]
    ring

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem phNorm_int {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hF : C.Frame R l linv ph) (h1 : C.F1 R l linv ph) (hneg : C.PhNormAt R l linv ph (-1) $ -1)
    (h2 : (2 : K)⁻¹ ∈ R) (n : ℤ) : C.PhNormAt R l linv ph (n : K) (n : K) := by
  have hl : C.IsLogPair l linv := hF.1
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 :=
    PowerSeries.constantCoeff_X
  have hXpt : C.IsPt R (PowerSeries.X : MvPowerSeries Unit K) := C.Pts.isPt_X

  set q : K → MvPowerSeries Unit K :=
    fun a => PowerSeries.subst (C.fmul l linv a (PowerSeries.X : MvPowerSeries Unit K)) ph with hq
  set B : MvPowerSeries Unit K :=
    C.be0 l linv ph (PowerSeries.X : MvPowerSeries Unit K) (PowerSeries.X : MvPowerSeries Unit K)
    with hB
  have hE : ∀ m : ℤ, C.LG R $ q (1 + (m : K)) - ph - q (m : K) - (m : K) • B := by
    intro m
    have h := C.zLinInt K R l linv ph hF h1 m Unit _ _ hXpt hXpt
    unfold C.Cong at h
    rw [C.be0] at h
    have e : C.fadd l linv (PowerSeries.X : MvPowerSeries Unit K)
        (C.fmul l linv (m : K) (PowerSeries.X : MvPowerSeries Unit K)) =
        C.fmul l linv (1 + (m : K)) (PowerSeries.X : MvPowerSeries Unit K) := by
      rw [C.Pts.fmul_add hl 1 (m : K) hX, C.Pts.fmul_one hl hX]
    rwa [e, PowerSeries.X_subst ph] at h
  have hq0 : q 0 = 0 := by
    simp [hq]
    rw [C.Pts.fmul_zero_left hl, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2]
  have hN : C.LG R $ q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K)) := by
    have h := hneg
    unfold C.PhNormAt C.Cong at h
    rwa [C.Pts.mulBy_eq_fmul] at h

  have hG : C.LG R $ B - (2 : K) • (ph : MvPowerSeries Unit K) := by
    have h := C.Calc.lg_add (hE $ -1) hN
    have e : (q (1 + ((-1 : ℤ) : K)) - ph - q ((-1 : ℤ) : K) - ((-1 : ℤ) : K) • B) +
        (q (-1) - (((-1 : K) * (-1 : K)) • (ph : MvPowerSeries Unit K))) =
        B - (2 : K) • (ph : MvPowerSeries Unit K) := by
      have e0 : (1 : K) + ((-1 : ℤ) : K) = 0 := by push_cast
                                                   ring
      have e1 : (((-1 : ℤ) : K)) = -1 := by push_cast
                                            ring
      rw [e0, hq0, e1]
      module
    rwa [e] at h
  have hstep : ∀ m : ℤ, C.LG R $ (q (((m + 1 : ℤ)) : K) -
      ((((m + 1 : ℤ)) : K) * (((m + 1 : ℤ)) : K)) • (ph : MvPowerSeries Unit K)) -
      (q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K)) := by
    intro m
    have h := C.Calc.lg_add (hE m) $ C.lGBinom K R Unit (m : K) (C.intBinomScalar K R m) _ hG
    have e1 : (((m + 1 : ℤ)) : K) = 1 + (m : K) := by push_cast
                                                      ring
    rw [e1]
    convert h using 1
    module
  have main : ∀ m : ℤ, C.LG R $ q (m : K) - ((m : K) * (m : K)) • (ph : MvPowerSeries Unit K) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      have : q ((0 : ℤ) : K) - (((0 : ℤ) : K) * ((0 : ℤ) : K)) • (ph : MvPowerSeries Unit K) = 0 := by
        rw [Int.cast_zero, hq0]
        simp
      rw [this]
      exact C.Calc.lg_zero
    | succ i ih =>
      have h := C.Calc.lg_add (hstep i) ih
      rwa [sub_add_cancel] at h
    | pred i ih =>
      have h := C.Calc.lg_add (C.Calc.lg_neg $ hstep $ -(i : ℤ) - 1) ih
      rw [sub_add_cancel] at h
      convert h using 1
      abel
  unfold C.PhNormAt C.Cong
  rw [C.Pts.mulBy_eq_fmul]
  exact main n

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section General

variable {R : Type*} [CommRing R] (p : ℕ)

def FrobFix (x : R) : Prop := ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x

variable {p}

theorem frobFix_iter {x : R} {f : ℕ} (h : (p : R) ∣ x ^ (p ^ f) - x) (k : ℕ) :
    (p : R) ∣ x ^ (p ^ (f * (k + 1))) - x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have e : x ^ (p ^ (f * (k + 1 + 1))) = (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) := by
      rw [← pow_mul, ← pow_add]
      congr 2
    rw [e]
    have h1 : (p : R) ∣ (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) - x ^ (p ^ f) :=
      dvd_trans ih $ sub_dvd_pow_sub_pow _ _ _
    have h2 := dvd_add h1 h
    rwa [sub_add_sub_cancel] at h2

theorem frobFix_common {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    ∃ f, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x ∧ (p : R) ∣ y ^ (p ^ f) - y := by
  obtain ⟨f1, hf1, h1⟩ := hx
  obtain ⟨f2, hf2, h2⟩ := hy
  refine ⟨f1 * f2, Nat.mul_pos hf1 hf2, ?_, ?_⟩
  have h := frobFix_iter h1 $ f2 - 1
  rwa [Nat.sub_add_cancel hf2] at h
  have h := frobFix_iter h2 $ f1 - 1
  rwa [Nat.sub_add_cancel hf1, mul_comm] at h

theorem frobFix_mul {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) : FrobFix p $ x * y := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  use f, hf
  have e : (x * y) ^ (p ^ f) - x * y = x ^ (p ^ f) * (y ^ (p ^ f) - y) + y * (x ^ (p ^ f) - x) := by
    ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right h2 _) $ dvd_mul_of_dvd_right h1 _

private theorem frobFix_add_lemma (hp : p.Prime) (x y : R) (n : ℕ) :
    (p : R) ∣ (x + y) ^ (p ^ n) - (x ^ (p ^ n) + y ^ (p ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : (p : R) ∣ ((x + y) ^ (p ^ n)) ^ p - (x ^ (p ^ n) + y ^ (p ^ n)) ^ p :=
      dvd_trans ih $ sub_dvd_pow_sub_pow _ _ _
    have hB : (p : R) ∣ (x ^ (p ^ n) + y ^ (p ^ n)) ^ p - ((x ^ (p ^ n)) ^ p + (y ^ (p ^ n)) ^ p) := by
      rw [add_pow_prime_eq hp, add_sub_cancel_left]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have e : ∀ a : R, a ^ (p ^ (n + 1)) = (a ^ (p ^ n)) ^ p := fun a => by
      rw [pow_succ, pow_mul]
    rw [e, e, e]
    have h := dvd_add hA hB
    rwa [sub_add_sub_cancel] at h

theorem frobFix_add (hp : p.Prime) {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    FrobFix p $ x + y := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  use f, hf
  have e : (x + y) ^ (p ^ f) - (x + y) =
      ((x + y) ^ (p ^ f) - (x ^ (p ^ f) + y ^ (p ^ f))) + (x ^ (p ^ f) - x) + (y ^ (p ^ f) - y) := by
    ring
  rw [e]
  exact dvd_add (dvd_add (frobFix_add_lemma hp x y f) h1) h2

theorem frobFix_neg_one (hp : p.Prime) : FrobFix p (-1 : R) := by
  use 1, one_pos
  rcases hp.eq_two_or_odd' with rfl | hodd
  rw [show (-1 : R) ^ (2 ^ 1) - -1 = ((2 : ℕ) : R) by push_cast; ring]
  rw [pow_one, hodd.neg_one_pow, sub_self]
  exact dvd_zero _

theorem frobFix_neg (hp : p.Prime) {x : R} (hx : FrobFix p x) : FrobFix p $ -x := by
  simpa using frobFix_mul (frobFix_neg_one (R := R) hp) hx

theorem frobFix_zero (hp : p.Prime) : FrobFix p (0 : R) :=
  ⟨1, one_pos, by rw [pow_one, zero_pow hp.ne_zero, sub_zero]; exact dvd_zero _⟩

theorem frobFix_one : FrobFix p (1 : R) :=
  ⟨1, one_pos, by simp⟩

theorem frobFix_root (hp : p.Prime) {x : R} {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n)
    (hx : x ^ n = 1) : FrobFix p x := by
  use n.totient, Nat.totient_pos.2 hn
  have key : ∀ m, x ^ m = x ^ (m % n) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hx, one_pow, mul_one]
  have hx' : x ^ (p ^ n.totient) = x := by
    rw [key, Nat.ModEq.pow_totient $ (Nat.Prime.coprime_iff_not_dvd hp).2 hpn, ← key, pow_one]
  rw [hx', sub_self]
  exact dvd_zero _


end General

variable (l : ℕ) [Fact l.Prime]

theorem rmu_frob (x : ℂ_[l]) (hx : x ∈ Rmu l) :
    ∃ f, 0 < f ∧ ∃ r ∈ Rmu l, x ^ (l ^ f) - x = (l : ℂ_[l]) * r := by
  have hp : l.Prime := Fact.out
  have key : ∀ y hy, FrobFix l (⟨y, hy⟩ : Rmu l) := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨n, hn, hln, hzn⟩ := hz
      exact frobFix_root hp hn hln $ Subtype.ext (by simpa using hzn)
    | zero => exact frobFix_zero hp
    | one => exact frobFix_one
    | add a b ha' hb' ha hb =>
      have e : (⟨a + b, Subring.add_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ + ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_add hp ha hb
    | neg a ha' ha =>
      have e : (⟨-a, Subring.neg_mem _ ha'⟩ : Rmu l) = -⟨a, ha'⟩ := Subtype.ext (by simp)
      rw [e]
      exact frobFix_neg hp ha
    | mul a b ha' hb' ha hb =>
      have e : (⟨a * b, Subring.mul_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ * ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_mul ha hb
  obtain ⟨f, hf, r, hr⟩ := key x hx
  use f, hf, r, r.2
  simpa using (congrArg Subtype.val hr)

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def newtonBall (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans $ max_le ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rwa [norm_neg]

theorem newton_exists_poly (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    ∃ Q : Polynomial $ newtonBall K, Q.map (newtonBall K).subtype = P := by
  have hp : (↑P.coeffs : Set K) ⊆ newtonBall K := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp $ Finset.mem_coe.mp hc
    exact hP i
  exact ⟨P.toSubring (newtonBall K) hp, Polynomial.map_toSubring P (newtonBall K) hp⟩

theorem newton_eval_ball (Q : Polynomial (newtonBall K)) (a : newtonBall K) :
    (Q.map (newtonBall K).subtype).eval (a : K) = ((Q.eval a : newtonBall K) : K) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (newtonBall K).subtype a

theorem newton_expansion (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∃ k : K, ‖k‖ ≤ 1 ∧ P.eval (x + y) = P.eval x + P.derivative.eval x * y + k * y ^ 2 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion Q ⟨x, hx⟩ ⟨y, hy⟩
  use k, k.2
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q $ ⟨x, hx⟩ + ⟨y, hy⟩
  have e2 := newton_eval_ball Q ⟨x, hx⟩
  have e3 := newton_eval_ball (Polynomial.derivative Q) ⟨x, hx⟩
  rw [Polynomial.derivative_map]
  simp [Subring.coe_add, Subring.coe_mul, Subring.coe_pow] at h e1 e2 e3
  rw [e1, e2, e3, h]

theorem newton_lipschitz (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.evalSubFactor Q ⟨x, hx⟩ ⟨y, hy⟩
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q ⟨x, hx⟩
  have e2 := newton_eval_ball Q ⟨y, hy⟩
  simp [AddSubgroupClass.coe_sub, Subring.coe_mul] at h e1 e2
  rw [e1, e2, h, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) k.2

theorem newton_derivative_coeff (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (i : ℕ) :
    ‖P.derivative.coeff i‖ ≤ 1 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  rw [Polynomial.derivative_map, Polynomial.coeff_map]
  exact ((Polynomial.derivative Q).coeff i).2

theorem newton_step (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x : K) (hx : ‖x‖ ≤ 1)
    (h0 : ‖P.eval x‖ < 1) (h1 : ‖P.derivative.eval x‖ = 1) :
    ∃ y, ‖y‖ ≤ 1 ∧ ‖P.derivative.eval y‖ = 1 ∧ ‖P.eval y‖ ≤ ‖P.eval x‖ ^ 2 ∧
      ‖y - x‖ ≤ ‖P.eval x‖ := by
  have hd : P.derivative.eval x ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  set t : K := -(P.eval x / P.derivative.eval x) with ht
  have hnt : ‖t‖ = ‖P.eval x‖ := by rw [ht, norm_neg, norm_div, h1, div_one]
  have ht1 := hnt ▸ h0.le
  have hy := (IsUltrametricDist.norm_add_le_max x t).trans $ max_le hx ht1
  obtain ⟨k, hk, he⟩ := newton_expansion P hP x t hx ht1
  refine ⟨x + t, hy, ?_, ?_, ?_⟩
  have hl := newton_lipschitz P.derivative (newton_derivative_coeff P hP) (x + t) x hy hx
  rw [add_sub_cancel_left, hnt] at hl
  have hlt : ‖P.derivative.eval (x + t) - P.derivative.eval x‖ < ‖P.derivative.eval x‖ := by
    rw [h1]
    exact lt_of_le_of_lt hl h0
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
  rwa [sub_add_cancel, max_eq_right hlt.le, h1] at this
  have hz : P.eval x + P.derivative.eval x * t = 0 := by
    rw [ht]
    field_simp; ring
  rw [he, hz, zero_add, norm_mul, norm_pow, hnt]
  exact mul_le_of_le_one_left (by positivity) hk
  rw [add_sub_cancel_left, hnt]

end Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem newton_root (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x₀ : K) (hx : ‖x₀‖ ≤ 1)
    (h0 : ‖P.eval x₀‖ < 1) (h1 : ‖P.derivative.eval x₀‖ = 1) :
    ∃ x : K, P.eval x = 0 ∧ ‖x - x₀‖ ≤ ‖P.eval x₀‖ := by
  set c : ℝ := ‖P.eval x₀‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  let S : Type := {x : K // ‖x‖ ≤ 1 ∧ ‖P.eval x‖ < 1 ∧ ‖P.derivative.eval x‖ = 1}
  have step : ∀ s : S, ∃ s' : S, ‖P.eval s'.1‖ ≤ ‖P.eval s.1‖ ^ 2 ∧
      ‖s'.1 - s.1‖ ≤ ‖P.eval s.1‖ := by
    intro s
    obtain ⟨y, hy, hy1, hy2, hy3⟩ := newton_step P hP s.1 s.2.1 s.2.2.1 s.2.2.2
    have : ‖P.eval y‖ < 1 :=
      lt_of_le_of_lt hy2 $ pow_lt_one₀ (norm_nonneg _) s.2.2.1 two_ne_zero
    exact ⟨⟨y, hy, this, hy1⟩, hy2, hy3⟩
  choose g hg1 hg2 using step
  let u : ℕ → S := fun n => Nat.rec ⟨x₀, hx, h0, h1⟩ (fun _ s => g s) n
  have hu0 : (u 0).1 = x₀ := rfl
  have hus : ∀ n, u (n + 1) = g (u n) := fun _ => rfl
  have hval : ∀ n, ‖P.eval (u n).1‖ ≤ c * c ^ n := by
    intro n
    induction n with
    | zero => rw [hu0, pow_zero, mul_one]
    | succ n ih =>
      calc ‖P.eval (u $ n + 1).1‖ ≤ ‖P.eval (u n).1‖ ^ 2 := by rw [hus]; exact hg1 _
        _ = ‖P.eval (u n).1‖ * ‖P.eval (u n).1‖ := sq _
        _ ≤ (c * c ^ n) * c := mul_le_mul ih (ih.trans $ mul_le_of_le_one_right hc0 $ pow_le_one₀ hc0 h0.le) (norm_nonneg _) $ by positivity
        _ = c * c ^ (n + 1) := by ring
  have hdist : ∀ n, dist (u n).1 (u $ n + 1).1 ≤ c * c ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, hus]
    exact (hg2 _).trans $ hval n
  obtain ⟨x, hxl⟩ := cauchySeq_tendsto_of_complete $ cauchySeq_of_le_geometric c c h0 hdist
  have hnear : ∀ n, ‖(u n).1 - x₀‖ ≤ c := by
    intro n
    induction n with
    | zero => rw [hu0, sub_self, norm_zero]; exact hc0
    | succ n ih =>
      have h2 : ‖(u $ n + 1).1 - (u n).1‖ ≤ c := by
        rw [← dist_eq_norm, dist_comm]
        exact (hdist n).trans $ mul_le_of_le_one_right hc0 $ pow_le_one₀ hc0 h0.le
      have := IsUltrametricDist.norm_add_le_max ((u $ n + 1).1 - (u n).1) $ (u n).1 - x₀
      rw [sub_add_sub_cancel] at this
      exact this.trans $ max_le h2 ih
  refine ⟨x, ?_, ?_⟩
  have hl1 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop $ nhds $ P.eval x :=
    (P.continuous.tendsto x).comp hxl
  exact tendsto_nhds_unique hl1 $ by
      apply squeeze_zero_norm hval
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 h0).const_mul c
      rwa [mul_zero] at this
  have hl : Filter.Tendsto (fun n => ‖(u n).1 - x₀‖) Filter.atTop $ nhds ‖x - x₀‖ :=
    (hxl.sub_const x₀).norm
  exact le_of_tendsto' hl hnear

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open PowerSeries (coeff mk)
open ModularForm EisensteinSeries ModularFormClass

namespace ReciprocityTheory.ChartRestriction.L1

def DD (τ : ℍ) : ℂ := ModularForm.discriminant τ

def AA (τ : ℍ) : ℂ := E₄ τ ^ 3

def jT (τ : ℍ) : ℂ := AA τ / DD τ

def Tm (m : ℕ) : Finset $ ℕ × ℕ × ℕ :=
  (m.divisors.sigma fun a => Finset.range $ m / a).image fun x => (x.1, x.2, m / x.1)

def pt (a b e : ℕ) (τ : ℍ) : ℍ := UpperHalfPlane.ofComplex $ ((a : ℂ) * τ + b) / e

def fac (t : ℕ × ℕ × ℕ) (τ : ℍ) : ℂ :=
  AA τ * DD (pt t.1 t.2.1 t.2.2 τ) - AA (pt t.1 t.2.1 t.2.2 τ) * DD τ

def Gm (m : ℕ) (τ : ℍ) : ℂ := ∏ t ∈ Tm m, fac t τ

def zetaC (m : ℕ) : ℂ := Complex.exp $ 2 * Real.pi * Complex.I / m

def Rm (m : ℕ) : Subring ℂ := Subring.closure {zetaC m}

def CoeffIn (R : Subring ℂ) (f : PowerSeries ℂ) : Prop := ∀ n, coeff n f ∈ R

def IsTauOf (L : PeriodPair) (c : ℂ) (τ : ℍ) : Prop :=
  c ≠ 0 ∧ ∀ x : ℂ, x ∈ L.lattice ↔ ∃ u v : ℤ, x = c * (u * (τ : ℂ) + v)

def Tmat (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(t.1 : ℤ), (t.2.1 : ℤ); 0, (t.2.2 : ℤ)]

def IsMF (k : ℤ) (f : ℍ → ℂ) : Prop := ∃ g : ModularForm 𝒮ℒ k, ∀ τ, g τ = f τ

def e4Z : PowerSeries ℤ :=
  mk fun n => if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ)

def e6Z : PowerSeries ℤ :=
  mk fun n => if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ)

def aZ : PowerSeries ℤ := e4Z ^ 3

def dZ : PowerSeries ℤ := mk fun n => coeff n (e4Z ^ 3 - e6Z ^ 2) / 1728

def aC : PowerSeries ℂ := aZ.map $ Int.castRingHom ℂ

def dC : PowerSeries ℂ := dZ.map $ Int.castRingHom ℂ

def xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) : PowerSeries R :=
  mk fun n => if k ∣ n then coeff (n / k) f else 0

def Conv (f : PowerSeries ℂ) : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 → Summable fun n => ‖coeff n f‖ * ‖x‖ ^ n

def ev (f : PowerSeries ℂ) (x : ℂ) : ℂ := ∑' n, coeff n f * x ^ n

def sub1 (c : ℂ) (k : ℕ) (f : PowerSeries ℂ) : PowerSeries ℂ := xp k $ PowerSeries.rescale c f

def facSer (m : ℕ) (t : ℕ × ℕ × ℕ) : PowerSeries ℂ :=
  xp m aC * sub1 (zetaC t.2.2 ^ t.2.1) (t.1 ^ 2) dC - sub1 (zetaC t.2.2 ^ t.2.1) (t.1 ^ 2) aC * xp m dC

def prodSer (m : ℕ) : PowerSeries ℂ := ∏ t ∈ Tm m, facSer m t

def LowUnit (R : Subring ℂ) (f : PowerSeries ℂ) (n0 : ℕ) (u : ℂ) : Prop :=
  u ∈ R ∧ u⁻¹ ∈ R ∧ u ≠ 0 ∧ (∀ n < n0, coeff n f = 0) ∧ coeff n0 f = u

def qm (m : ℕ) (τ : ℍ) : ℂ := Complex.exp $ 2 * Real.pi * Complex.I * τ / m

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem mem_Tm {m : ℕ} (hm : 0 < m) (t : ℕ × ℕ × ℕ) :
    t ∈ Tm m ↔ t.1 * t.2.2 = m ∧ t.2.1 < t.2.2 := by
  rw [Tm, Finset.mem_image]
  constructor
  rintro ⟨⟨a, b⟩, hx, rfl⟩
  rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at hx
  constructor
  exact Nat.mul_div_cancel' hx.1.1
  exact hx.2
  obtain ⟨a, b, e⟩ := t
  rintro ⟨h1, h2⟩
  simp only at h1 h2
  have he : m / a = e := by rw [← h1, Nat.mul_div_cancel_left _ $ Nat.pos_of_ne_zero (by rintro rfl; omega)]
  refine ⟨⟨a, b⟩, ?_, ?_⟩
  rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
  constructor
  constructor
  exact ⟨e, h1.symm⟩
  exact hm.ne'
  rwa [he]
  simp [he]

theorem Tm_pos {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : 0 < t.1 ∧ 0 < t.2.2 := by
  have hpos := (((mem_Tm hm t).mp ht).1) ▸ hm
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩ <;>
    rw [h0] at hpos <;> simp at hpos

theorem pt_coe {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    ((pt a b e τ : ℍ) : ℂ) = ((a : ℂ) * τ + b) / e := by
  have hz : 0 < (((a : ℂ) * τ + b) / e).im := by
    rw [Complex.div_natCast_im]
    simp [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
      UpperHalfPlane.coe_im]
    apply div_pos $ mul_pos (by exact_mod_cast ha) τ.im_pos
    exact_mod_cast he
  unfold pt
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem DD_ne_zero (τ : ℍ) : DD τ ≠ 0 := by
  exact ModularForm.discriminant_ne_zero τ

theorem smul_of_form {k : ℤ} (g : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    g (γ • τ) = denom γ τ ^ k * g τ := by
  have h := SlashInvariantForm.slash_action_eqn'' g (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) τ
  exact h

theorem isMF_AA : IsMF 12 AA := by
  refine ⟨ModularForm.mcast (by norm_num) $ ModularForm.E₄.mul $ ModularForm.E₄.mul ModularForm.E₄, fun τ => ?_⟩
  show (ModularForm.E₄.mul $ ModularForm.E₄.mul ModularForm.E₄) τ = AA τ
  rw [ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_mul, Pi.mul_apply]
  unfold AA
  ring

theorem isMF_DD : IsMF 12 DD := by
  first
    | exact ⟨ModularFormClass.modularForm ModularForm.discriminantCuspForm, fun τ => rfl⟩
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩

theorem IsMF.smul_eq {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = denom γ τ ^ k * f τ := by
  obtain ⟨g, hg⟩ := h
  rw [← hg, ← hg]
  exact smul_of_form g γ τ

theorem AA_smul (γ : SL(2, ℤ)) (τ : ℍ) : AA (γ • τ) = denom γ τ ^ 12 * AA τ := by
  exact isMF_AA.smul_eq γ τ

theorem DD_smul (γ : SL(2, ℤ)) (τ : ℍ) : DD (γ • τ) = denom γ τ ^ 12 * DD τ := by
  exact isMF_DD.smul_eq γ τ


theorem IsMF.congr_weight {k k' : ℤ} {f : ℍ → ℂ} (h : IsMF k f) (hk : k = k') : IsMF k' f := by
  subst hk
  exact h

theorem IsMF.add {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k fun τ => f τ + g τ := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' + g', fun τ => by simp [hf', hg']⟩

theorem IsMF.sub {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k g) : IsMF k fun τ => f τ - g τ := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f' - g', fun τ => by simp [hf', hg']⟩

theorem IsMF.const_mul {k : ℤ} {f : ℍ → ℂ} (c : ℂ) (hf : IsMF k f) : IsMF k fun τ => c * f τ := by
  obtain ⟨f', hf'⟩ := hf
  exact ⟨c • f', fun τ => by simp [hf']⟩

theorem IsMF.mul {k k' : ℤ} {f g : ℍ → ℂ} (hf : IsMF k f) (hg : IsMF k' g) :
    IsMF (k + k') fun τ => f τ * g τ := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨f'.mul g', fun τ => by rw [ModularForm.coe_mul, Pi.mul_apply, hf', hg']⟩

theorem IsMF.pow {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (n : ℕ) : IsMF (n * k) fun τ => f τ ^ n := by
  induction n with
  | zero =>
    refine IsMF.congr_weight (k := 0) ⟨1, fun τ => ?_⟩ $ by simp
    simp
  | succ n ih =>
    simpa [pow_succ] using ((ih.mul hf).congr_weight (show (n : ℤ) * k + k = ((n + 1 : ℕ) : ℤ) * k by push_cast; ring))

theorem zetaC_pow_self {m : ℕ} (hm : 0 < m) : zetaC m ^ m = 1 := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I := by field_simp
  rw [this, Complex.exp_two_pi_mul_I]




theorem Rm_isIntegral {m : ℕ} (hm : 0 < m) {x : ℂ} (hx : x ∈ Rm m) : IsIntegral ℤ x := by
  have hζ : IsIntegral ℤ $ zetaC m :=
    IsIntegral.of_pow hm (by rw [zetaC_pow_self hm]; exact isIntegral_one)
  have hle : Rm m ≤ (integralClosure ℤ ℂ).toSubring :=
    Subring.closure_le.mpr $ Set.singleton_subset_iff.mpr hζ
  exact hle hx

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open PowerSeries (coeff coeff_mul)
open ReciprocityTheory.ChartRestriction.L1 (CoeffIn LowUnit)
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem coeff_xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) (n : ℕ) :
    coeff n (xp k f) = if k ∣ n then coeff (n / k) f else 0 := by
  rw [xp, PowerSeries.coeff_mk]








theorem CoeffIn.map_int (R : Subring ℂ) (f : PowerSeries ℤ) : CoeffIn R $ f.map $ Int.castRingHom ℂ := by
  intro n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem R _

theorem CoeffIn.add {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R $ f + g := by
  intro n
  rw [map_add]
  exact add_mem (hf n) $ hg n

theorem CoeffIn.sub {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R $ f - g := by
  intro n
  rw [map_sub]
  exact sub_mem (hf n) $ hg n

theorem CoeffIn.mul {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R $ f * g := by
  intro n
  rw [coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf _) $ hg _

theorem CoeffIn.one (R : Subring ℂ) : CoeffIn R 1 := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  exact one_mem R
  exact zero_mem R

theorem CoeffIn.pow {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (n : ℕ) : CoeffIn R $ f ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.one R
  | succ n ih =>
    rw [pow_succ]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.mul ih hf

theorem CoeffIn.prod {R : Subring ℂ} {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ)
    (hf : ∀ t ∈ s, CoeffIn R (f t)) : CoeffIn R (∏ t ∈ s, f t) := Finset.prod_induction f (CoeffIn R)
    (fun a b ha hb => ReciprocityTheory.ChartRestriction.L1.CoeffIn.mul ha hb) (ReciprocityTheory.ChartRestriction.L1.CoeffIn.one R) hf

theorem CoeffIn.xp {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (k : ℕ) : CoeffIn R $ xp k f := by
  intro n
  rw [coeff_xp]
  split_ifs
  exact hf _
  exact zero_mem R

theorem CoeffIn.sub1 {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) {c : ℂ} (hc : c ∈ R) (k : ℕ) :
    CoeffIn R $ sub1 c k f := by
  have hr : CoeffIn R $ PowerSeries.rescale c f := fun m => by
    rw [PowerSeries.coeff_rescale]
    exact mul_mem (pow_mem hc m) $ hf m
  exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.xp hr k

theorem LowUnit.mul {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ} (hf : LowUnit R f n u)
    (hg : LowUnit R g n' u') : LowUnit R (f * g) (n + n') $ u * u' := by
  obtain ⟨hu, hui, hu0, hlow, hc⟩ := hf
  obtain ⟨hu', hui', hu0', hlow', hc'⟩ := hg
  refine ⟨mul_mem hu hu', by rw [mul_inv]; exact mul_mem hui hui', mul_ne_zero hu0 hu0', ?_, ?_⟩
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h1 : p.1 < n
  rw [hlow _ h1, zero_mul]
  rw [hlow' _ $ by omega, mul_zero]
  rw [coeff_mul, Finset.sum_eq_single (n, n')]
  rw [hc, hc']
  intro p hp hne
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h1 : p.1 < n
  rw [hlow _ h1, zero_mul]
  have h2 : p.2 < n' := by
    by_contra h2
    exact hne $ Prod.ext (by show p.1 = n; omega) (by show p.2 = n'; omega)
  rw [hlow' _ h2, mul_zero]
  intro h
  exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (rfl : n + n' = n + n')) h

theorem LowUnit.one (R : Subring ℂ) : LowUnit R 1 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn $ Nat.not_lt_zero n, ?_⟩
  simp

theorem LowUnit.prod {R : Subring ℂ} {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ)
    (hf : ∀ t ∈ s, ∃ n u, LowUnit R (f t) n u) : ∃ n u, LowUnit R (∏ t ∈ s, f t) n u := Finset.prod_induction f (fun g => ∃ n u, LowUnit R g n u)
    (fun a b ⟨n, u, ha⟩ ⟨n', u', hb⟩ => ⟨n + n', u * u', ReciprocityTheory.ChartRestriction.L1.LowUnit.mul ha hb⟩)
    ⟨0, 1, ReciprocityTheory.ChartRestriction.L1.LowUnit.one R⟩ hf

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_sq (d : ℕ) : 4 * omegaK d ^ 2 = 4 * omegaK d - (1 + d) := by
  have hs : (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt $ Nat.cast_nonneg d]
    push_cast
    ring
  unfold omegaK
  linear_combination hs

theorem omegaK_lin {d : ℕ} (hd : 0 < d) {t n : ℤ} (h : (t : ℂ) * omegaK d + n = 0) :
    t = 0 ∧ n = 0 := by
  have h2 : (t : ℂ) * (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) + 2 * n = 0 := by
    rw [omegaK] at h
    linear_combination 2 * h
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr $ by exact_mod_cast hd
  have h3 : (((t : ℝ) + 2 * n : ℝ) : ℂ) + (((t : ℝ) * Real.sqrt d : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination h2
  have him : (t : ℝ) * Real.sqrt d = 0 := by
    have := congrArg Complex.im h3
    simpa using this
  have hre : (t : ℝ) + 2 * n = 0 := by
    have := congrArg Complex.re h3
    simpa using this
  have ht : (t : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    exact h
    exact absurd h hsq.ne'
  have hn : (n : ℝ) = 0 := by linarith
  constructor
  exact_mod_cast ht
  exact_mod_cast hn
theorem cmPoint {d : ℕ} (hd : 0 < d) {L : PeriodPair} (hL : HasCMBy d L) {c : ℂ} {τ : ℍ}
    (h : IsTauOf L c τ) (x y : ℤ) :
    ∃ A B C D : ℤ, ((x : ℂ) + y * omegaK d) * τ = A * τ + B ∧ (x : ℂ) + y * omegaK d = C * τ + D ∧
      4 * (A * D - B * C) = 4 * x ^ 2 + 4 * x * y + y ^ 2 * (1 + d) := by
  obtain ⟨hc, hmem⟩ := h
  have hmul : ∀ w ∈ L.lattice, ((x : ℂ) + y * omegaK d) * w ∈ L.lattice := by
    intro w hw
    have h1 : (x : ℂ) * w ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem hw x
    have h2 : (y : ℂ) * (omegaK d * w) ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem (hL w hw) y
    have e : ((x : ℂ) + y * omegaK d) * w = (x : ℂ) * w + (y : ℂ) * (omegaK d * w) := by ring
    rw [e]
    exact add_mem h1 h2
  have hcτ : c * (τ : ℂ) ∈ L.lattice := (hmem _).2 ⟨1, 0, by push_cast; ring⟩
  obtain ⟨A, B, hAB⟩ := (hmem _).1 $ hmul _ hcτ
  obtain ⟨C, D, hCD⟩ := (hmem _).1 $ hmul _ $ (hmem _).2 ⟨0, 1, by push_cast; ring⟩
  have e1 : ((x : ℂ) + y * omegaK d) * τ = A * τ + B := by
    apply mul_left_cancel₀ hc
    linear_combination hAB
  have e2 : (x : ℂ) + y * omegaK d = C * τ + D := by
    apply mul_left_cancel₀ hc
    linear_combination hCD
  use A, B, C, D, e1, e2
  have key : ((x : ℂ) + y * omegaK d - A) * ((x : ℂ) + y * omegaK d - D) = B * C := by
    linear_combination ((x : ℂ) + y * omegaK d - A) * e2 + (C : ℂ) * e1
  have hω := omegaK_sq d
  obtain ⟨ht, hn⟩ := omegaK_lin hd (t := 8 * x * y + 4 * y ^ 2 - 4 * (A + D) * y)
    (n := 4 * x ^ 2 - y ^ 2 * (1 + d) - 4 * (A + D) * x + 4 * (A * D - B * C)) $ by
      push_cast
      linear_combination 4 * key - (y : ℂ) ^ 2 * hω
  by_cases hy : y = 0
  subst hy
  simp only [Int.cast_zero, zero_mul, add_zero] at e1 e2
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  have e2' : (x : ℂ) - D = (C : ℂ) * τ := by linear_combination e2
  have e1' : ((x : ℂ) - A) * τ = (B : ℂ) := by linear_combination e1
  have hC : C = 0 := by
    have := congrArg Complex.im e2'
    simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re] at this
    have h0 : (C : ℝ) * (τ : ℂ).im = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h0 | h0
    exact_mod_cast h0
    exact absurd h0 hτ.ne'
  have hA : A = x := by
    have := congrArg Complex.im e1'
    simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
      Complex.sub_re] at this
    have h0 : ((x : ℝ) - A) * (τ : ℂ).im = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h0 | h0
    have : (A : ℝ) = x := by linarith
    exact_mod_cast this
    exact absurd h0 hτ.ne'
  subst hC hA
  have hD : D = A := by
    have : ((A : ℤ) : ℂ) = D := by linear_combination e2'
    exact_mod_cast this.symm
  subst hD
  ring
  have h4 : 4 * (y * (2 * x + y - (A + D))) = 0 := by linear_combination ht
  have hs :=
    (mul_eq_zero.mp $ (mul_eq_zero.mp h4).resolve_left $ by norm_num).resolve_left hy
  linear_combination hn - 4 * x * hs

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open Nat (choose factorial succ_eq_add_one)
open PowerSeries (coeff coeff_map coeff_mk)
open Real (pi pi_ne_zero)
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

private theorem hasSum_sigma_mul_qParam_pow_modularForm_E {k : ℕ} (hk : 3 ≤ k) (hke : Even k) (C : ℂ)
    (hC : (riemannZeta k)⁻¹ * (-2 * (pi : ℂ) * Complex.I) ^ k / ((k - 1).factorial : ℂ) = C)
    (τ : ℍ) :
    HasSum (fun m => (if m = 0 then (1 : ℂ) else C * (ArithmeticFunction.sigma (k - 1) m : ℂ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) $ ModularForm.E hk τ := by
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hqe : Complex.exp (2 * (pi : ℂ) * Complex.I * τ) = q := by
    simp [hqdef, Function.Periodic.qParam]
  have hq : ‖q‖ < 1 := by
    rw [hqdef, Function.Periodic.norm_qParam]
    refine (Real.exp_lt_exp.mpr ?_).trans_eq Real.exp_zero
    have := τ.im_pos
    have := Real.pi_pos
    simp only [UpperHalfPlane.coe_im, div_one]
    nlinarith
  have hσ : ∀ n, ‖((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n‖ ≤ (n : ℝ) ^ k * ‖q‖ ^ n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    calc ∑ d ∈ n.divisors, (d : ℝ) ^ (k - 1) ≤ ∑ d ∈ n.divisors, (n : ℝ) ^ (k - 1) :=
          Finset.sum_le_sum fun d hd => pow_le_pow_left₀ (by positivity)
            (by exact_mod_cast Nat.divisor_le hd) _
      _ = (n.divisors.card : ℝ) * (n : ℝ) ^ (k - 1) := by simp
      _ ≤ (n : ℝ) * (n : ℝ) ^ (k - 1) := by
          gcongr
          exact_mod_cast Nat.card_divisors_le_self n
      _ = (n : ℝ) ^ k := by
          rw [← pow_succ']
          congr 1
          omega
  have hsum :=
    Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one k $ by simpa using hq) hσ
  rw [EisensteinSeries.q_expansion_riemannZeta hk hke τ, hC, hqe, ← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, if_true, mul_one,
    add_sub_cancel_left, Nat.add_eq_zero, one_ne_zero, and_false, if_false]
  convert ((summable_nat_add_iff 1).mpr hsum).hasSum.mul_left C using 1 <;>
    first
    | rfl
    | (funext n <;> ring)
    | (congr 1 <;> (rw [← tsum_pnat_eq_tsum_succ (f := fun n => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n)]; apply tsum_congr; intro n; simp))

theorem map_eisensteinFourInt : e4Z.map (Int.castRingHom ℂ) = qExpansion 1 E₄ := by
  have hE : E₄ = ModularForm.E (k := 4) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₄) (h := 1)
    (c := fun m => coeff m $ e4Z.map $ Int.castRingHom ℂ) one_pos (by simp) ?_ m
  intro τ
  have hC : (riemannZeta ((4 : ℕ) : ℂ))⁻¹ * (-2 * (pi : ℂ) * Complex.I) ^ 4 /
      (((4 - 1).factorial : ℕ) : ℂ) = 240 := by
    have hpi : (pi : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    rw [show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
    simp only [factorial, succ_eq_add_one]
    field_simp
    ring_nf
    rw [Complex.I_pow_four]
    ring
  rw [hE]
  convert (hasSum_sigma_mul_qParam_pow_modularForm_E (k := 4) (by norm_num) (by decide) 240 hC τ) using 2 with n
  simp only [e4Z, coeff_map, coeff_mk]
  split_ifs <;> simp

theorem map_eisensteinSixInt : e6Z.map (Int.castRingHom ℂ) = qExpansion 1 E₆ := by
  have hE : E₆ = ModularForm.E (k := 6) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₆) (h := 1)
    (c := fun m => coeff m $ e6Z.map $ Int.castRingHom ℂ) one_pos (by simp) ?_ m
  intro τ
  have hb6 : bernoulli 6 = 1 / 42 := by
    have h5 : bernoulli' 5 = 0 := by
      rw [bernoulli'_def]
      norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
        bernoulli'_three, bernoulli'_four, choose]
    rw [bernoulli_eq_bernoulli'_of_ne_one $ by norm_num, bernoulli'_def]
    norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5, choose]
  have hz6 : riemannZeta ((6 : ℕ) : ℂ) = (pi : ℂ) ^ 6 / 945 := by
    rw [show ((6 : ℕ) : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, riemannZeta_two_mul_nat (k := 3) $ by norm_num, hb6]
    norm_num [factorial]
    ring
  have hC : (riemannZeta ((6 : ℕ) : ℂ))⁻¹ * (-2 * (pi : ℂ) * Complex.I) ^ 6 /
      (((6 - 1).factorial : ℕ) : ℂ) = -504 := by
    have hpi : (pi : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    rw [hz6]
    have hI : Complex.I ^ 6 = -1 := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]
      norm_num
    simp only [factorial, succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  rw [hE]
  convert (hasSum_sigma_mul_qParam_pow_modularForm_E (k := 6) (by norm_num) (by decide) (-504) hC τ) using 2 with n
  simp only [e6Z, coeff_map, coeff_mk]
  split_ifs <;> simp

theorem aC_eq : aC = qExpansion 1 AA := by
  have h1 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos $ by simp
  have h2 : AnalyticAt ℂ (cuspFunction 1 $ ⇑E₄ * ⇑E₄) 0 := by
    have h3 := ModularFormClass.analyticAt_cuspFunction_zero (E₄.mul E₄) one_pos $ by simp
    rwa [ModularForm.coe_mul] at h3
  have hA : AA = ⇑E₄ * (⇑E₄ * ⇑E₄) := by
    funext τ
    simp [AA, Pi.mul_apply]
    ring
  rw [hA, qExpansion_mul h1 h2, qExpansion_mul h1 h1, ← map_eisensteinFourInt]
  simp [aC, aZ, map_pow]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem twelve_dvd_five_pow_three_add_seven_pow_five (d : ℤ) : (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
  have key : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * d ^ 3 + 7 * d ^ 5) 12).mp
    (by push_cast; exact key _)
  exact_mod_cast h

theorem sigma_congr (n : ℕ) :
    (12 : ℤ) ∣ 5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => twelve_dvd_five_pow_three_add_seven_pow_five _

def s3Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 3 n : ℤ)

def s5Z : PowerSeries ℤ := PowerSeries.mk fun n => (ArithmeticFunction.sigma 5 n : ℤ)

def tZ : PowerSeries ℤ := PowerSeries.mk fun n =>
  (5 * (ArithmeticFunction.sigma 3 n : ℤ) + 7 * (ArithmeticFunction.sigma 5 n : ℤ)) / 12

theorem eisensteinFourInt_eq : e4Z = 1 + PowerSeries.C (240 : ℤ) * s3Z := by
  ext n
  simp [e4Z, s3Z, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  subst h
  simp
  ring

theorem eisensteinSixInt_eq : e6Z = 1 - PowerSeries.C (504 : ℤ) * s5Z := by
  ext n
  simp [e6Z, s5Z, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]
  split_ifs with h
  subst h
  simp
  ring

theorem tZ_mul : PowerSeries.C (12 : ℤ) * tZ =
    PowerSeries.C (5 : ℤ) * s3Z + PowerSeries.C (7 : ℤ) * s5Z := by
  ext n
  simp [map_add, PowerSeries.coeff_C_mul, tZ, s3Z, s5Z, PowerSeries.coeff_mk]
  exact Int.mul_ediv_cancel' $ sigma_congr n

theorem eisenstein_cube_sub_sq_eq : e4Z ^ 3 - e6Z ^ 2 = PowerSeries.C (1728 : ℤ) *
    (tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 + PowerSeries.C (8000 : ℤ) * s3Z ^ 3
      - PowerSeries.C (147 : ℤ) * s5Z ^ 2) := by
  have h := tZ_mul
  rw [eisensteinFourInt_eq, eisensteinSixInt_eq]
  simp [map_ofNat] at h ⊢
  linear_combination (-144 : PowerSeries ℤ) * h

theorem dZ_mul : PowerSeries.C (1728 : ℤ) * dZ = e4Z ^ 3 - e6Z ^ 2 := by
  ext n
  rw [PowerSeries.coeff_C_mul, dZ, PowerSeries.coeff_mk, eisenstein_cube_sub_sq_eq, PowerSeries.coeff_C_mul]
  exact Int.mul_ediv_cancel' $ dvd_mul_right _ _

private theorem dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq : dZ = tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 +
    PowerSeries.C (8000 : ℤ) * s3Z ^ 3 - PowerSeries.C (147 : ℤ) * s5Z ^ 2 := by
  refine mul_left_cancel₀ (fun h0 => ?_) $ dZ_mul.trans eisenstein_cube_sub_sq_eq
  have := congrArg PowerSeries.constantCoeff h0
  rw [PowerSeries.constantCoeff_C, map_zero] at this
  norm_num at this

theorem dZ_coeff_zero : PowerSeries.coeff 0 dZ = 0 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dZ_coeff_one : PowerSeries.coeff 1 dZ = 1 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num

theorem dC_eq : dC = qExpansion 1 DD := by
  have h4 : qExpansion 1 ⇑((E₄.mul E₄).mul E₄) = qExpansion 1 E₄ ^ 3 := by
    rw [ModularForm.qExpansion_mul one_pos $ by simp, ModularForm.qExpansion_mul one_pos $ by simp]
    ring
  have h6 : qExpansion 1 ⇑(E₆.mul E₆) = qExpansion 1 E₆ ^ 2 := by
    rw [ModularForm.qExpansion_mul one_pos $ by simp]
    ring
  have hfun : DD = ⇑((1 / 1728 : ℂ) • ((E₄.mul E₄).mul E₄)) - ⇑((1 / 1728 : ℂ) • (E₆.mul E₆)) := by
    funext τ
    simp only [DD, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, Pi.sub_apply,
      ModularForm.coe_smul, ModularForm.coe_mul, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hd := congrArg (PowerSeries.map $ Int.castRingHom ℂ) dZ_mul
  rw [map_mul, map_sub, map_pow, map_pow, PowerSeries.map_C, map_eisensteinFourInt, map_eisensteinSixInt] at hd
  rw [hfun, ModularForm.qExpansion_sub one_pos $ by simp, ModularForm.coe_smul, ModularForm.coe_smul,
    ModularForm.qExpansion_smul one_pos $ by simp, ModularForm.qExpansion_smul one_pos $ by simp,
    h4, h6, ← smul_sub, ← hd, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul]
  rw [show (1 / 1728 : ℂ) * (Int.castRingHom ℂ) 1728 = 1 by norm_num, map_one, one_mul]
  rfl

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem Conv.summable_norm {f : PowerSeries ℂ} (hf : Conv f) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n => ‖PowerSeries.coeff n f * x ^ n‖ := by
  refine (hf x hx).congr fun n => ?_
  rw [norm_mul, norm_pow]

theorem Conv.summable {f : PowerSeries ℂ} (hf : Conv f) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n => PowerSeries.coeff n f * x ^ n := (hf.summable_norm hx).of_norm

theorem Conv.hasSum {f : PowerSeries ℂ} (hf : Conv f) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n f * x ^ n) $ ev f x := (hf.summable hx).hasSum

theorem conv_of_hasSum {f : PowerSeries ℂ}
    (h : ∀ x, ‖x‖ < 1 → Summable fun n => PowerSeries.coeff n f * x ^ n) : Conv f := by
  intro x hx
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 := lt_of_le_of_lt (norm_nonneg x) hxr
  have hrn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    $ Metric.isBounded_range_of_tendsto _ (h (r : ℂ) (by rw [hrn]; exact hr1)).tendsto_atTop_zero
  have hq0 : 0 ≤ ‖x‖ / r := div_nonneg (norm_nonneg _) hr0.le
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    $ (summable_geometric_of_lt_one hq0 $ (div_lt_one hr0).mpr hxr).mul_left C
  have h1 : ‖PowerSeries.coeff n f * (r : ℂ) ^ n‖ ≤ C := hC _ ⟨n, rfl⟩
  rw [norm_mul, norm_pow, hrn] at h1
  calc ‖PowerSeries.coeff n f‖ * ‖x‖ ^ n
      = (‖PowerSeries.coeff n f‖ * r ^ n) * (‖x‖ / r) ^ n := by
        rw [div_pow]
        field_simp
    _ ≤ C * (‖x‖ / r) ^ n := mul_le_mul_of_nonneg_right h1 $ pow_nonneg hq0 n

theorem Conv.add {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) : Conv $ f + g := by
  intro x hx
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) $ (hf x hx).add $ hg x hx
  rw [map_add, ← add_mul]
  apply mul_le_mul_of_nonneg_right $ norm_add_le _ _
  positivity
theorem Conv.sub {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) : Conv $ f - g := by
  intro x hx
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) $ (hf x hx).add $ hg x hx
  rw [map_sub, ← add_mul]
  apply mul_le_mul_of_nonneg_right $ norm_sub_le _ _
  positivity
theorem coeff_mul_term (f g : PowerSeries ℂ) (x : ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) * x ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * x ^ kl.1) * (PowerSeries.coeff kl.2 g * x ^ kl.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl]
  ring

theorem Conv.mul {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) : Conv $ f * g := by
  intro x hx
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm (hf.summable_norm hx)
    $ hg.summable_norm hx).congr fun n => ?_
  beta_reduce
  rw [← coeff_mul_term, norm_mul, norm_pow]

theorem conv_one : Conv (1 : PowerSeries ℂ) := by
  intro x _
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  rw [Finset.mem_singleton] at hn
  simp [PowerSeries.coeff_one, hn]


theorem Conv.pow {f : PowerSeries ℂ} (hf : Conv f) (n : ℕ) : Conv $ f ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact conv_one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem Conv.prod {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ) (hf : ∀ t ∈ s, Conv (f t)) :
    Conv (∏ t ∈ s, f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact conv_one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a $ Finset.mem_insert_self a s).mul
      $ ih fun t ht => hf t $ Finset.mem_insert_of_mem ht


theorem xp_term (f : PowerSeries ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) (m : ℕ) :
    PowerSeries.coeff (k * m) (xp k f) * x ^ (k * m) = PowerSeries.coeff m f * (x ^ k) ^ m := by
  rw [xp, PowerSeries.coeff_mk, if_pos $ dvd_mul_right k m,
    Nat.mul_div_cancel_left m $ Nat.pos_of_ne_zero hk, pow_mul]

theorem xp_support (f : PowerSeries ℂ) (k : ℕ) (x : ℂ) :
    ∀ n ∉ Set.range fun m => k * m, PowerSeries.coeff n (xp k f) * x ^ n = 0 := by
  intro n hn
  rw [xp, PowerSeries.coeff_mk, if_neg fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩, zero_mul]

theorem natMul_injective {k : ℕ} (hk : k ≠ 0) : Function.Injective fun m => k * m := fun _ _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h

theorem Conv.xp {f : PowerSeries ℂ} (hf : Conv f) {k : ℕ} (hk : k ≠ 0) : Conv $ xp k f := by
  intro x hx
  refine ((natMul_injective hk).summable_iff $ by
      intro n hn
      rw [ReciprocityTheory.ChartRestriction.L1.xp, PowerSeries.coeff_mk, if_neg fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩, norm_zero, zero_mul]).mp ?_
  refine (hf (x ^ k) $ by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg x) hx hk).congr fun m => ?_
  show ‖PowerSeries.coeff m f‖ * ‖x ^ k‖ ^ m =
    ‖PowerSeries.coeff (k * m) (ReciprocityTheory.ChartRestriction.L1.xp k f)‖ * ‖x‖ ^ (k * m)
  rw [ReciprocityTheory.ChartRestriction.L1.xp, PowerSeries.coeff_mk, if_pos $ dvd_mul_right k m,
    Nat.mul_div_cancel_left m $ Nat.pos_of_ne_zero hk, norm_pow, pow_mul]

theorem Conv.rescale {f : PowerSeries ℂ} (hf : Conv f) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    Conv $ PowerSeries.rescale c f := by
  intro x hx
  refine (hf (c * x) (by
      rw [norm_mul]
      calc ‖c‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg x)
        _ < 1 := by rw [one_mul]
                    exact hx)).congr fun n => ?_
  simp [PowerSeries.coeff_rescale, norm_mul, norm_pow, mul_pow]
  ring

theorem Conv.sub1 {f : PowerSeries ℂ} (hf : Conv f) {c : ℂ} (hc : ‖c‖ ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    Conv $ sub1 c k f := (hf.rescale hc).xp hk


theorem ev_sub {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f - g) x = ev f x - ev g x := by
  have h := (hf.hasSum hx).sub $ hg.hasSum hx
  have e : (fun n => PowerSeries.coeff n (f - g) * x ^ n) =
      fun n => PowerSeries.coeff n f * x ^ n - PowerSeries.coeff n g * x ^ n := by
    funext n
    rw [map_sub, sub_mul]
  rw [← e] at h
  exact h.tsum_eq

theorem ev_mul {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) {x : ℂ} (hx : ‖x‖ < 1) :
    ev (f * g) x = ev f x * ev g x := by
  unfold ev
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hf.summable_norm hx)
    $ hg.summable_norm hx]
  exact tsum_congr fun n => coeff_mul_term f g x n


theorem ev_xp (f : PowerSeries ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) : ev (xp k f) x = ev f (x ^ k) := by
  have hsupp : Function.support (fun n => PowerSeries.coeff n (xp k f) * x ^ n) ⊆
      Set.range fun m => k * m := by
    intro n hn
    by_contra h
    exact hn $ xp_support f k x n h
  unfold ev
  rw [← (natMul_injective hk).tsum_eq hsupp]
  exact tsum_congr fun m => xp_term f hk x m

theorem evalSeries_rescaleExpand (f : PowerSeries ℂ) (c : ℂ) {k : ℕ} (hk : k ≠ 0) (x : ℂ) :
    ev (sub1 c k f) x = ev f (c * x ^ k) := by
  rw [sub1, ev_xp _ hk]
  unfold ev
  exact tsum_congr fun n => by rw [PowerSeries.coeff_rescale, mul_pow]
                               ring

private theorem eq_zero_at_zero_of_tsum_mul_pow_eq_zero (b : ℕ → ℂ) (hb : Summable fun i => ‖b i‖ * (1 / 2 : ℝ) ^ i)
    (h0 : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∑' i, b i * (t : ℂ) ^ i = 0) : b 0 = 0 := by
  have hK : Summable fun i => ‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i := by
    refine (((summable_nat_add_iff 1).mpr hb).mul_left 2).congr fun i => ?_
    beta_reduce
    ring
  have hmain : ∀ t, 0 < t → t ≤ 1 / 2 →
      ‖b 0‖ ≤ t * ∑' i, ‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i := by
    intro t ht hle
    have hbd : ∀ i, ‖b i * (t : ℂ) ^ i‖ ≤ ‖b i‖ * (1 / 2 : ℝ) ^ i := by
      intro i
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hle i) $ norm_nonneg _
    have hGn : Summable fun i => ‖b i * (t : ℂ) ^ i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbd hb
    have hG : Summable fun i => b i * (t : ℂ) ^ i := hGn.of_norm
    have hsplit := hG.tsum_eq_zero_add
    rw [h0 t ht hle, pow_zero, mul_one] at hsplit
    have hb0 : b 0 = -∑' i, b (i + 1) * (t : ℂ) ^ (i + 1) := by linear_combination -hsplit
    have hGn1 : Summable fun i => ‖b (i + 1) * (t : ℂ) ^ (i + 1)‖ :=
      (summable_nat_add_iff 1).mpr hGn
    have hle2 : ∀ i, ‖b (i + 1) * (t : ℂ) ^ (i + 1)‖ ≤ t * (‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i) := by
      intro i
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, pow_succ]
      calc ‖b (i + 1)‖ * (t ^ i * t) = t * (‖b (i + 1)‖ * t ^ i) := by ring
        _ ≤ t * (‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hle i) $ norm_nonneg _) ht.le
    rw [hb0, norm_neg]
    exact (norm_tsum_le_tsum_norm hGn1).trans $ hasSum_le hle2 hGn1.hasSum $ hK.hasSum.mul_left t
  generalize hKd : (∑' i, ‖b (i + 1)‖ * (1 / 2 : ℝ) ^ i) = K at hmain
  have hK0 := hKd ▸ tsum_nonneg fun i => by positivity
  by_contra hne
  have hc : 0 < ‖b 0‖ := norm_pos_iff.mpr hne
  have hK1 : (0 : ℝ) < 2 * (K + 1) := by linarith
  have h3 : ‖b 0‖ ≤ ‖b 0‖ / (2 * (K + 1)) * K := (hmain _ (lt_min (by norm_num) $ div_pos hc hK1) $ min_le_left _ _).trans $ mul_le_mul_of_nonneg_right (min_le_right _ _) hK0
  rw [div_mul_eq_mul_div, le_div_iff₀ hK1] at h3
  nlinarith [mul_nonneg hc.le hK0]

private theorem coeff_eq_zero_of_ev_eq_zero_of_lower_eq_zero {f : PowerSeries ℂ} (hf : Conv f)
    (h : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = 0) (n : ℕ)
    (ih : ∀ j < n, PowerSeries.coeff j f = 0) : PowerSeries.coeff n f = 0 := by
  have key := eq_zero_at_zero_of_tsum_mul_pow_eq_zero (fun i => PowerSeries.coeff (i + n) f) ?_ ?_
  simpa using key
  have h2 : ‖((1 / 2 : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
    norm_num
  have hs := (summable_nat_add_iff n).mpr (hf _ h2)
  rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hs
  refine (hs.mul_left (2 ^ n)).congr fun i => ?_
  beta_reduce
  generalize ‖PowerSeries.coeff (i + n) f‖ = c
  rw [pow_add]
  calc (2 : ℝ) ^ n * (c * ((1 / 2) ^ i * (1 / 2) ^ n)) = c * (1 / 2) ^ i * ((1 / 2) ^ n * 2 ^ n) := by
        ring
    _ = c * (1 / 2) ^ i := by rw [← mul_pow]
                              norm_num
  intro t ht hle
  have hev := h _ (by
      rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
      exact ht) (by
      rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
      linarith)
  have e1 : ev f (t : ℂ) = ∑' i, PowerSeries.coeff (i + n) f * (t : ℂ) ^ (i + n) :=
    ((add_left_injective n).tsum_eq (by
        intro j hj
        by_cases hjn : j < n
        rw [Function.mem_support] at hj
        exact absurd (by simp [ih j hjn]) hj
        exact ⟨j - n, Nat.sub_add_cancel (not_lt.mp hjn)⟩)).symm
  have e2 : ∑' i, PowerSeries.coeff (i + n) f * (t : ℂ) ^ (i + n) =
      (t : ℂ) ^ n * ∑' i, PowerSeries.coeff (i + n) f * (t : ℂ) ^ i := by
    rw [← tsum_mul_left]
    exact tsum_congr fun i => by ring
  rw [e1, e2] at hev
  exact (mul_eq_zero.mp hev).resolve_left (pow_ne_zero _ (by exact_mod_cast ht.ne'))

theorem eq_zero_of_ev_eq_zero {f : PowerSeries ℂ} (hf : Conv f)
    (h : ∀ x, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = 0) : f = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih => exact coeff_eq_zero_of_ev_eq_zero_of_lower_eq_zero hf h n ih

theorem eq_of_ev_eq {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g)
    (h : ∀ x, 0 < ‖x‖ → ‖x‖ < 1 → ev f x = ev g x) : f = g := by
  have h0 := eq_zero_of_ev_eq_zero (hf.sub hg) fun x hx0 hx1 => by
    rw [ev_sub hf hg hx1, h x hx0 hx1, sub_self]
  exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem qm_eq_qParam (m : ℕ) (τ : ℍ) : qm m τ = Function.Periodic.qParam (m : ℝ) τ := by
  simp [qm, Function.Periodic.qParam]

theorem qm_norm_lt_one {m : ℕ} (hm : 0 < m) (τ : ℍ) : ‖qm m τ‖ < 1 := by
  rw [qm_eq_qParam]
  exact Function.Periodic.norm_qParam_lt_one (by exact_mod_cast hm) τ.im_pos

theorem qm_surj {m : ℕ} (hm : 0 < m) {x : ℂ} (h0 : 0 < ‖x‖) (h1 : ‖x‖ < 1) : ∃ τ : ℍ, qm m τ = x := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have him : 0 < (Function.Periodic.invQParam (m : ℝ) x).im := by
    rw [Function.Periodic.im_invQParam]
    refine mul_pos_of_neg_of_neg ?_ $ Real.log_neg h0 h1
    apply div_neg_of_neg_of_pos $ by linarith
    positivity
  use ⟨_, him⟩
  rw [qm_eq_qParam]
  exact Function.Periodic.qParam_right_inv hmR.ne' $ norm_pos_iff.mp h0

theorem qm_pow {m : ℕ} (hm : 0 < m) (τ : ℍ) : qm m τ ^ m = qm 1 τ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [qm, qm, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem qm_one_eq (τ : ℍ) : qm 1 τ = Function.Periodic.qParam 1 τ := by
  simpa using qm_eq_qParam 1 τ

theorem qm_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    qm 1 (pt a b e τ) = zetaC e ^ b * qm (a * e) τ ^ (a ^ 2) := by
  rw [qm, qm, zetaC, pt_coe ha he, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem IsMF.hasSum {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) :
    HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) $ f τ := by
  obtain ⟨g, hg⟩ := hf
  have h := ModularForm.hasSum_qExpansion (f := g) one_pos one_mem_strictPeriods_SL τ
  rwa [funext hg, ← qm_one_eq] at h

theorem IsMF.conv {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : Conv $ qExpansion 1 f := by
  apply conv_of_hasSum
  intro x hx
  by_cases h0 : x = 0
  subst h0
  exact (hasSum_single 0 fun n hn => by simp [zero_pow hn]).summable
  obtain ⟨τ, hτ⟩ := qm_surj one_pos (norm_pos_iff.mpr h0) hx
  rw [← hτ]
  exact (hf.hasSum τ).summable

theorem IsMF.ev_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) : ev (qExpansion 1 f) (qm 1 τ) = f τ := by
  exact (hf.hasSum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open PowerSeries (coeff coeff_map coeff_rescale)
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem zetaRoot_mem_cyclotomicSubring_self (m : ℕ) : zetaC m ∈ Rm m := by
  exact Subring.subset_closure $ Set.mem_singleton _

theorem zetaRoot_ne_zero (e : ℕ) : zetaC e ≠ 0 := by
  exact Complex.exp_ne_zero _

private theorem dvd_and_eq_div_of_mem_Tm {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    t.1 ∣ m ∧ 0 < t.1 ∧ t.2.2 = m / t.1 ∧ t.1 * t.2.2 = m := by
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at ht
  obtain ⟨⟨a, b⟩, ⟨⟨hdvd, _⟩, _⟩, rfl⟩ := ht
  exact ⟨hdvd, Nat.pos_of_dvd_of_pos hdvd hm, rfl, Nat.mul_div_cancel' hdvd⟩

private theorem zetaC_div_eq_pow_of_dvd {m a : ℕ} (hm : 0 < m) (ha : a ∣ m) : zetaC (m / a) = zetaC m ^ a := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast (by
      rintro rfl
      rw [zero_dvd_iff] at ha
      omega)
  unfold zetaC
  rw [← Complex.exp_nat_mul, Nat.cast_div ha ha']
  congr 1
  field_simp

theorem zetaRoot_pow_mem_of_mem_hermiteTriples {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    zetaC t.2.2 ^ t.2.1 ∈ Rm m ∧ (zetaC t.2.2 ^ t.2.1)⁻¹ ∈ Rm m := by
  obtain ⟨hdvd, _, he, _⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  have hz : zetaC t.2.2 ^ t.2.1 = zetaC m ^ (t.1 * t.2.1) := by
    rw [he, zetaC_div_eq_pow_of_dvd hm hdvd, pow_mul]
  have hzm : zetaC m ^ m = 1 := by
    unfold zetaC
    rw [← Complex.exp_nat_mul]
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [show (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I by field_simp]
    exact Complex.exp_two_pi_mul_I
  have hinv : (zetaC m)⁻¹ = zetaC m ^ (m - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hm, hzm]
  rw [hz]
  constructor
  exact pow_mem (zetaRoot_mem_cyclotomicSubring_self m) _
  rw [← inv_pow, hinv, ← pow_mul]
  exact pow_mem (zetaRoot_mem_cyclotomicSubring_self m) _

theorem norm_zetaRoot_pow_of_mem_hermiteTriples {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    ‖zetaC t.2.2 ^ t.2.1‖ = 1 := by
  rw [norm_pow, zetaC, Complex.norm_exp]
  simp

theorem convergesOnDisk_eisensteinFourCubeSeries : Conv aC := by
  rw [aC_eq]
  exact isMF_AA.conv

theorem convergesOnDisk_discriminantSeries : Conv dC := by
  rw [dC_eq]
  exact isMF_DD.conv

theorem evalSeries_eisensteinFourCubeSeries (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  rw [aC_eq]
  exact isMF_AA.ev_eq τ

theorem evalSeries_discriminantSeries (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  rw [dC_eq]
  exact isMF_DD.ev_eq τ

theorem eisensteinFourCubeSeries_coeff_zero : coeff 0 aC = 1 := by
  rw [aC, coeff_map, aZ, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, e4Z]
  simp

theorem discriminantSeries_coeff_zero : coeff 0 dC = 0 := by
  rw [dC, coeff_map, dZ_coeff_zero]
  simp

theorem discriminantSeries_coeff_one : coeff 1 dC = 1 := by
  rw [dC, coeff_map, dZ_coeff_one]
  simp

theorem facSer_coeffIn {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    CoeffIn (Rm m) $ facSer m t := by
  obtain ⟨hc, _⟩ := zetaRoot_pow_mem_of_mem_hermiteTriples hm ht
  have hA : CoeffIn (Rm m) aC := CoeffIn.map_int _ _
  have hD : CoeffIn (Rm m) dC := CoeffIn.map_int _ _
  unfold facSer
  exact ((hA.xp m).mul $ hD.sub1 hc _).sub $ (hA.sub1 hc _).mul $ hD.xp m

theorem facSer_conv {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : Conv $ facSer m t := by
  have hc := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ (dvd_and_eq_div_of_mem_Tm hm ht).2.1.ne'
  unfold facSer
  exact ((convergesOnDisk_eisensteinFourCubeSeries.xp hm.ne').mul $ convergesOnDisk_discriminantSeries.sub1 hc hk).sub
    $ (convergesOnDisk_eisensteinFourCubeSeries.sub1 hc hk).mul $ convergesOnDisk_discriminantSeries.xp hm.ne'

theorem facSer_ev {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (τ : ℍ) :
    ev (facSer m t) (qm m τ) = fac t τ := by
  obtain ⟨hdvd, ha0, he, hae⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  have he0 : 0 < t.2.2 := by
    rw [he]
    exact Nat.div_pos (Nat.le_of_dvd hm hdvd) ha0
  have hq := qm_norm_lt_one hm τ
  have hc := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ ha0.ne'
  have hA := convergesOnDisk_eisensteinFourCubeSeries
  have hD := convergesOnDisk_discriminantSeries
  have hpt : zetaC t.2.2 ^ t.2.1 * qm m τ ^ (t.1 ^ 2) = qm 1 (pt t.1 t.2.1 t.2.2 τ) := by
    rw [qm_pt ha0 he0, hae]
  unfold facSer fac
  rw [ev_sub ((hA.xp hm.ne').mul $ hD.sub1 hc hk) ((hA.sub1 hc hk).mul $ hD.xp hm.ne') hq,
    ev_mul (hA.xp hm.ne') (hD.sub1 hc hk) hq, ev_mul (hA.sub1 hc hk) (hD.xp hm.ne') hq,
    ev_xp _ hm.ne', ev_xp _ hm.ne', evalSeries_rescaleExpand _ _ hk, evalSeries_rescaleExpand _ _ hk, qm_pow hm, hpt]
  simp [evalSeries_eisensteinFourCubeSeries, evalSeries_discriminantSeries]

theorem LowUnit.facSub_left {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ}
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n < n') : LowUnit R (f - g) n u := by
  obtain ⟨hu, hui, hu0, hlow, hval⟩ := hf
  obtain ⟨_, _, _, hglow, _⟩ := hg
  refine ⟨hu, hui, hu0, fun k hk => ?_, ?_⟩
  rw [map_sub, hlow k hk, hglow k $ hk.trans h, sub_zero]
  rw [map_sub, hval, hglow n h, sub_zero]

theorem LowUnit.facSub_right {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ}
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n' < n) : LowUnit R (f - g) n' $ -u' := by
  obtain ⟨_, _, _, hflow, _⟩ := hf
  obtain ⟨hu, hui, hu0, hglow, hval⟩ := hg
  refine ⟨neg_mem hu, by rw [inv_neg]; exact neg_mem hui, neg_ne_zero.2 hu0, fun k hk => ?_, ?_⟩
  rw [map_sub, hflow k $ hk.trans h, hglow k hk, sub_zero]
  rw [map_sub, hflow n' h, hval, zero_sub]

theorem hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries (R : Subring ℂ) (c : ℂ) {k : ℕ} (hk : k ≠ 0) :
    LowUnit R (sub1 c k aC) 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn $ Nat.not_lt_zero n, ?_⟩
  rw [sub1, coeff_xp, if_pos $ dvd_zero k, Nat.zero_div, coeff_rescale, pow_zero, one_mul,
    eisensteinFourCubeSeries_coeff_zero]

theorem hasUnitLeadingCoeff_rescaleExpand_discriminantSeries {R : Subring ℂ} {c : ℂ} (hc : c ∈ R) (hc' : c⁻¹ ∈ R) (hc0 : c ≠ 0) {k : ℕ}
    (hk : k ≠ 0) : LowUnit R (sub1 c k dC) k c := by
  refine ⟨hc, hc', hc0, fun n hn => ?_, ?_⟩
  rw [sub1, coeff_xp]
  split_ifs with hd
  have h0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hn
  subst h0
  rw [Nat.zero_div, coeff_rescale, discriminantSeries_coeff_zero, mul_zero]
  rfl
  rw [sub1, coeff_xp, if_pos dvd_rfl, Nat.div_self $ Nat.pos_of_ne_zero hk, coeff_rescale,
    pow_one, discriminantSeries_coeff_one, mul_one]

theorem rescaleExpand_one (k : ℕ) (f : PowerSeries ℂ) : sub1 1 k f = xp k f := by
  simp [sub1, PowerSeries.rescale_one]

theorem facSer_low {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (hne : t.1 ≠ t.2.2) :
    ∃ n0 u, LowUnit (Rm m) (facSer m t) n0 u := by
  obtain ⟨hdvd, ha0, he, hae⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  obtain ⟨hc, hci⟩ := zetaRoot_pow_mem_of_mem_hermiteTriples hm ht
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ ha0.ne'
  have hxa : LowUnit (Rm m) (xp m aC) 0 1 := by
    rw [← rescaleExpand_one]
    exact hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries _ 1 hm.ne'
  have hxd : LowUnit (Rm m) (xp m dC) m 1 := by
    rw [← rescaleExpand_one]
    exact hasUnitLeadingCoeff_rescaleExpand_discriminantSeries (one_mem _) (by rw [inv_one]; exact one_mem _) one_ne_zero hm.ne'
  have h1 := hxa.mul $ hasUnitLeadingCoeff_rescaleExpand_discriminantSeries hc hci (pow_ne_zero _ $ zetaRoot_ne_zero _) hk
  have h2 := (hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries (Rm m) (zetaC t.2.2 ^ t.2.1) hk).mul hxd
  simp [zero_add, one_mul] at h1 h2
  unfold facSer
  rcases lt_or_gt_of_ne hne with hlt | hgt
  exact ⟨_, _, h1.facSub_left h2 (by rw [← hae]; nlinarith)⟩
  exact ⟨_, _, h1.facSub_right h2 (by rw [← hae]; nlinarith)⟩

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open UpperHalfPlane (coe_smul denom denom_ne_zero num)
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem denom_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  first
  | rfl
  | simp [denom]
  | (simp [denom]; norm_cast)

theorem smul_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  first
  | (rw [coe_smul, num, denom_SL_coe]; simp)
  | (rw [UpperHalfPlane.specialLinearGroup_apply]; simp)
  | simp [coe_smul, num, denom]

theorem pt_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    pt t.1 t.2.1 t.2.2 (γ • τ) = γ' • pt t'.1 t'.2.1 t'.2.2 τ ∧
      denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * denom γ τ := by
  have hm : ∀ i j, (Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ)) i j =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') i j := fun i j => by rw [h]
  have z00 : (t.1 : ℤ) * γ 0 0 + (t.2.1 : ℤ) * γ 1 0 = γ' 0 0 * (t'.1 : ℤ) := by
    have hh := hm 0 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z01 : (t.1 : ℤ) * γ 0 1 + (t.2.1 : ℤ) * γ 1 1 = γ' 0 0 * (t'.2.1 : ℤ) + γ' 0 1 * (t'.2.2 : ℤ) := by
    have hh := hm 0 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z10 : (t.2.2 : ℤ) * γ 1 0 = γ' 1 0 * (t'.1 : ℤ) := by
    have hh := hm 1 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z11 : (t.2.2 : ℤ) * γ 1 1 = γ' 1 0 * (t'.2.1 : ℤ) + γ' 1 1 * (t'.2.2 : ℤ) := by
    have hh := hm 1 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have c00 : (t.1 : ℂ) * ((γ 0 0 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z00
  have c01 : (t.1 : ℂ) * ((γ 0 1 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 0 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z01
  have c10 : (t.2.2 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z10
  have c11 : (t.2.2 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 1 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z11
  have he : (t.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht.2.ne'
  have he' : (t'.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]
                                                                      exact denom_ne_zero _ _
  have hD' : ((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]
                                                                                                     exact denom_ne_zero _ _
  have hZ : ((γ • τ : ℍ) : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) = ((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ) := by
    rw [smul_SL_coe γ τ]
    exact div_mul_cancel₀ _ hD
  have hW : ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) * (t'.2.2 : ℂ) = (t'.1 : ℂ) * (τ : ℂ) + (t'.2.1 : ℂ) := by
    rw [pt_coe ht'.1 ht'.2]
    exact div_mul_cancel₀ _ he'
  have c2 : (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    linear_combination ((γ' 1 0 : ℤ) : ℂ) * hW - (τ : ℂ) * c10 - c11
  refine ⟨UpperHalfPlane.ext ?_, ?_⟩
  rw [pt_coe ht.1 ht.2, smul_SL_coe γ' $ pt t'.1 t'.2.1 t'.2.2 τ, div_eq_div_iff he hD']
  have key : ((t'.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) *
      (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) - (((γ' 0 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 0 1 : ℤ) : ℂ)) * (t.2.2 : ℂ)) = 0 := by
    linear_combination (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * c2 +
      ((t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * ((t.1 : ℂ) * hZ - ((γ' 0 0 : ℤ) : ℂ) * hW + (τ : ℂ) * c00 + c01)
  rcases mul_eq_zero.mp key with h0 | h0
  exact absurd h0 $ mul_ne_zero he' hD
  exact sub_eq_zero.mp h0
  rwa [denom_SL_coe, denom_SL_coe]

theorem fac_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    fac t (γ • τ) = denom γ τ ^ 24 * ((t.2.2 : ℂ) / t'.2.2) ^ 12 * fac t' τ := by
  obtain ⟨h1, h2⟩ := pt_smul ht ht' γ γ' h τ
  have he' : ((t'.2.2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hd : denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) = (t.2.2 : ℂ) / t'.2.2 * denom γ τ := by
    rwa [div_mul_eq_mul_div, eq_div_iff he']
  simp only [fac]
  rw [h1, AA_smul, DD_smul, AA_smul, DD_smul, hd]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def latMap {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (v : Fin 2 → ℤ) : L.lattice :=
  ⟨c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)), (h.2 _).2 ⟨v 0, v 1, rfl⟩⟩

theorem latMap_bijective {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    Function.Bijective $ latMap h := by
  constructor
  intro v w hvw
  have h2 := mul_left_cancel₀ h.1 $ congrArg Subtype.val hvw
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him hre
  have hτ : (τ : ℂ).im ≠ 0 := τ.im_ne_zero
  have h0 := mul_right_cancel₀ hτ him
  rw [h0] at hre
  funext i
  fin_cases i
  exact_mod_cast h0
  exact_mod_cast (add_left_cancel hre)
  rintro ⟨x, hx⟩
  obtain ⟨u, v, rfl⟩ := (h.2 x).1 hx
  use ![u, v]
  simp [latMap]
theorem G_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    L.G k = (c ^ k)⁻¹ * (2 * riemannZeta k) * E hk τ := by
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := by
    rw [show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
      eisensteinSeriesSIF_apply 0 k τ, smul_eq_mul]
  trans ∑' v : Fin 2 → ℤ, (c ^ k)⁻¹ * eisSummand k v τ
  rw [PeriodPair.G, ← (Equiv.ofBijective _ $ latMap_bijective h).tsum_eq]
  refine tsum_congr fun v => ?_
  simp [latMap, eisSummand, mul_pow, mul_comm]
  rw [tsum_mul_left, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ, hE]
  ring

theorem sixVal : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    simp [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four]
    norm_num [Nat.choose]
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    simp [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four, h5]
    norm_num [Nat.choose]
  have hB : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one $ by norm_num, h6]
  have h := riemannZeta_two_mul_nat (k := 3) $ by norm_num
  norm_num [Nat.factorial, hB] at h
  rw [h]
  ring

theorem g₂_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ = (c ^ 4)⁻¹ * (4 * (Real.pi : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [PeriodPair.g₂, G_eq h (k := 4) (by norm_num) ⟨2, rfl⟩,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
  have hE : E (k := 4) (by norm_num) τ = E₄ τ := rfl
  rw [hE]
  ring

theorem g₃_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₃ = (c ^ 6)⁻¹ * (8 * (Real.pi : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [PeriodPair.g₃, G_eq h (k := 6) (by norm_num) ⟨3, rfl⟩,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, sixVal]
  have hE : E (k := 6) (by norm_num) τ = E₆ τ := rfl
  rw [hE]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open Matrix (det_fin_two mul_apply)
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_hermite_normal_form_coords {m : ℕ} (hm : 0 < m) (p q r s : ℤ) (h : p * s - q * r = m) :
    ∃ x y z w a b e, x * w - y * z = 1 ∧ a * e = m ∧ b < e ∧
      p = x * a ∧ q = x * b + y * e ∧ r = z * a ∧ s = z * b + w * e := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  set g : ℕ := Int.gcd p r with hg
  have hgZ : (0 : ℤ) < g := by exact_mod_cast (by
      rcases Nat.eq_zero_or_pos g with h0 | h0
      rw [hg, Int.gcd_eq_zero_iff] at h0
      rw [h0.1, h0.2] at h
      simp at h
      omega
      exact h0)
  obtain ⟨x, hx⟩ : (g : ℤ) ∣ p := Int.gcd_dvd_left p r
  obtain ⟨z, hz⟩ : (g : ℤ) ∣ r := Int.gcd_dvd_right p r
  set u := Int.gcdA p r
  set v := Int.gcdB p r
  have hbez : (g : ℤ) = p * u + r * v := Int.gcd_eq_gcd_ab p r
  have h1 : x * u + z * v = 1 := by
    have : (g : ℤ) * (x * u + z * v) = g * 1 := by
      rw [mul_one]
      conv_rhs => rw [hbez, hx, hz]
      ring
    exact mul_left_cancel₀ hgZ.ne' this
  set E : ℤ := x * s - z * q with hE
  have hgE : (g : ℤ) * E = m := by rw [← h, hx, hz, hE]
                                   ring
  have hE0 : 0 < E := by
    by_contra hc
    have : (g : ℤ) * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgZ.le $ not_lt.mp hc
    omega
  set b0 : ℤ := u * q + v * s with hb0
  have hmod1 : b0 % E < E := Int.emod_lt_of_pos _ hE0
  set k := b0 / E
  set B := b0 % E
  have hEn : ((E.toNat : ℕ) : ℤ) = E := Int.toNat_of_nonneg hE0.le
  have hBn : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg $ Int.emod_nonneg _ hE0.ne'
  refine ⟨x, x * k - v, z, z * k + u, g, B.toNat, E.toNat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  linear_combination h1
  have : ((g * E.toNat : ℕ) : ℤ) = m := by push_cast
                                           rw [hEn]; exact hgE
  exact_mod_cast this
  omega
  rw [hx]
  ring
  rw [hEn, hBn]
  have : x * B + (x * k - v) * E = x * b0 - v * E := by rw [← (Int.emod_add_mul_ediv b0 E)]
                                                        ring
  rw [this, hb0, hE]
  linear_combination (-q) * h1
  rw [hz]
  ring
  rw [hEn, hBn]
  have : z * B + (z * k + u) * E = z * b0 + u * E := by rw [← (Int.emod_add_mul_ediv b0 E)]
                                                        ring
  rw [this, hb0, hE]
  linear_combination (-s) * h1

theorem hnf_exists {m : ℕ} (hm : 0 < m) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = m) :
    ∃ (γ : SL(2, ℤ)) (t : ℕ × ℕ × ℕ), t ∈ Tm m ∧ M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t := by
  rw [det_fin_two] at hM
  obtain ⟨x, y, z, w, a, b, e, hdet, hae, hbe, h00, h01, h10, h11⟩ :=
    exists_hermite_normal_form_coords hm (M 0 0) (M 0 1) (M 1 0) (M 1 1) hM
  refine ⟨⟨!![x, y; z, w], by rw [Matrix.det_fin_two_of]; exact hdet⟩, (a, b, e),
    (mem_Tm hm _).2 ⟨hae, hbe⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tmat, mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]

theorem hnf_unique {m : ℕ} (hm : 0 < m) {t t' : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (ht' : t' ∈ Tm m)
    (γ : SL(2, ℤ)) (h : Tmat t = (γ : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') : t = t' := by
  obtain ⟨a, b, e⟩ := t
  obtain ⟨a', b', e'⟩ := t'
  obtain ⟨hae, hbe⟩ := (mem_Tm hm _).1 ht
  obtain ⟨hae', hbe'⟩ := (mem_Tm hm _).1 ht'
  obtain ⟨ha, he⟩ := Tm_pos hm ht
  obtain ⟨ha', he'⟩ := Tm_pos hm ht'
  simp only at hae hbe hae' hbe' ha he ha' he'
  have hdet : γ.1 0 0 * γ.1 1 1 - γ.1 0 1 * γ.1 1 0 = 1 := by
    rw [← det_fin_two]
    exact γ.2
  have h00 : (a : ℤ) = γ.1 0 0 * a' := by
    have := congrFun (congrFun h 0) 0
    simpa [Tmat, mul_apply, Fin.sum_univ_two] using this
  have h01 : (b : ℤ) = γ.1 0 0 * b' + γ.1 0 1 * e' := by
    have := congrFun (congrFun h 0) 1
    simpa [Tmat, mul_apply, Fin.sum_univ_two] using this
  have h10 : (0 : ℤ) = γ.1 1 0 * a' := by
    have := congrFun (congrFun h 1) 0
    simpa [Tmat, mul_apply, Fin.sum_univ_two] using this
  have h11 : (e : ℤ) = γ.1 1 0 * b' + γ.1 1 1 * e' := by
    have := congrFun (congrFun h 1) 1
    simpa [Tmat, mul_apply, Fin.sum_univ_two] using this
  generalize γ.1 0 0 = x at *
  generalize γ.1 0 1 = y at *
  generalize γ.1 1 0 = z at *
  generalize γ.1 1 1 = w at *
  have haZ : (0 : ℤ) < a := by exact_mod_cast ha
  have haZ' : (0 : ℤ) < a' := by exact_mod_cast ha'
  have heZ' : (0 : ℤ) < e' := by exact_mod_cast he'
  have hz : z = 0 := by
    rcases mul_eq_zero.1 h10.symm with h0 | h0
    exact h0
    omega
  subst hz
  have hxw : x * w = 1 := by linear_combination hdet
  have hx0 : 0 < x := by
    by_contra hc
    have : x * a' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) haZ'.le
    omega
  have hx : x = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hxw with h0 | h0
    exact h0
    omega
  subst hx
  have hw : w = 1 := by linear_combination hxw
  subst hw
  have e1 : a = a' := by omega
  have e2 : e = e' := by omega
  subst e1 e2
  have hy : y = 0 := by
    have hbZ : (b : ℤ) < e := by exact_mod_cast hbe
    have hbZ' : (b' : ℤ) < e := by exact_mod_cast hbe'
    by_contra hc
    rcases lt_or_gt_of_ne hc with h0 | h0
    have : y * e ≤ -1 * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
    omega
    have : 1 * (e : ℤ) ≤ y * e := mul_le_mul_of_nonneg_right (by omega) heZ'.le
    omega
  subst hy
  have e3 : b = b' := by omega
  subst e3
  rfl

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem disc_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ := by
  have hD : DD τ = (E₄ τ ^ 3 - E₆ τ ^ 2) / 1728 := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [g₂_eq h, g₃_eq h, hD]
  field_simp
  ring

theorem jInv_eq_jT {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) : jInv L = jT τ := by
  have hc := h.1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDD := DD_ne_zero τ
  show 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = E₄ τ ^ 3 / DD τ
  rw [disc_eq h, g₂_eq h]
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem latTau_snd_ne (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1

theorem latTau_im_ne (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  obtain ⟨r, hr⟩ : ∃ r : ℝ, L.ω₁ / L.ω₂ = (r : ℂ) :=
    ⟨(L.ω₁ / L.ω₂).re, Complex.ext (by simp) $ by simp [h]⟩
  have h1 : L.ω₁ = (r : ℂ) * L.ω₂ := by rw [← hr, div_mul_cancel₀ _ $ latTau_snd_ne L]
  have h3 := (LinearIndependent.pair_iff.mp L.indep) 1 (-r)
    (by rw [Complex.real_smul, Complex.real_smul, h1]; push_cast; ring)
  norm_num at h3

theorem latTau (L : PeriodPair) : ∃ (c : ℂ) (τ : ℍ), IsTauOf L c τ := by
  have h2 := latTau_snd_ne L
  rcases lt_or_gt_of_ne (latTau_im_ne L) with hneg | hpos
  refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by rw [Complex.neg_im]; linarith⟩, h2, fun x => ?_⟩
  rw [PeriodPair.mem_lattice]
  try simp only
  constructor
  rintro ⟨m, n, rfl⟩
  exact ⟨-m, n, by push_cast; field_simp; try ring⟩
  rintro ⟨u, v, rfl⟩
  exact ⟨-u, v, by push_cast; field_simp; try ring⟩
  refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, hpos⟩, h2, fun x => ?_⟩
  rw [PeriodPair.mem_lattice]
  try simp only
  constructor
  rintro ⟨m, n, rfl⟩
  exact ⟨m, n, by field_simp; try ring⟩
  rintro ⟨u, v, rfl⟩
  exact ⟨u, v, by field_simp; try ring⟩

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem perm_Tmat_det {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : (Tmat t).det = m := by
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at ht
  obtain ⟨⟨a, b⟩, ⟨⟨hdvd, _⟩, _⟩, rfl⟩ := ht
  simp only [Tmat, Matrix.det_fin_two_of, mul_zero, sub_zero]
  exact_mod_cast Nat.mul_div_cancel' hdvd

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem Gm_smul {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) (τ : ℍ) :
    Gm m (γ • τ) = denom γ τ ^ (24 * (Tm m).card) * Gm m τ := by
  classical
  have hex : ∀ t ∈ Tm m, ∃ (γ' : SL(2, ℤ)) (t' : ℕ × ℕ × ℕ), t' ∈ Tm m ∧
      Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t' := by
    intro t ht
    apply hnf_exists hm
    rw [Matrix.det_mul, perm_Tmat_det hm ht, Matrix.SpecialLinearGroup.det_coe, mul_one]
  choose! g σ hσ hg using hex
  have hinvR : ∀ A : SL(2, ℤ),
      (A : Matrix (Fin 2) (Fin 2) ℤ) * ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinvL : ∀ A,
      ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (A : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinj : Set.InjOn σ $ Tm m := by
    intro t1 h1 t2 h2 he
    have e2 := hg t2 h2
    rw [← he] at e2
    have key : Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (Tmat t2 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
      rw [hg t1 h1, e2, Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc, mul_assoc (g t1 : Matrix (Fin 2) (Fin 2) ℤ),
        hinvL, mul_one]
    apply hnf_unique hm h1 h2 $ g t1 * (g t2)⁻¹
    calc Tmat t1 = Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [mul_assoc, hinvR, mul_one]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 *
            (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [key]
          simp [mul_assoc]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 := by
          rw [mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hinvR, mul_one]
  have himg : (Tm m).image σ = Tm m := by
    apply Finset.eq_of_subset_of_card_le
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact hσ t ht
    rw [Finset.card_image_of_injOn hinj]
  have hprod : ∀ F : ℕ × ℕ × ℕ → ℂ, ∏ t ∈ Tm m, F (σ t) = ∏ t ∈ Tm m, F t := by
    intro F
    conv_rhs => rw [← himg]
    rw [Finset.prod_image hinj]
  have hne : ∏ t ∈ Tm m, (t.2.2 : ℂ) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro t ht
    exact_mod_cast (Tm_pos hm ht).2.ne'
  unfold Gm
  rw [Finset.prod_congr rfl fun t ht => fac_smul (Tm_pos hm ht) (Tm_pos hm $ hσ t ht) γ (g t) (hg t ht) τ, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, hprod fun t => fac t τ,
    Finset.prod_pow, Finset.prod_div_distrib, hprod fun t => (t.2.2 : ℂ), div_self hne, one_pow, mul_one]

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open Finset (induction_on mem_insert_of_mem mem_insert_self prod_insert)
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.mdiff {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : MDiff f := by
  obtain ⟨g, hg⟩ := h
  have e := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.holo g

theorem IsMF.bdd {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : IsBoundedAtImInfty f := by
  obtain ⟨g, hg⟩ := h
  have e := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.bdd_at_infty g

theorem pt_im {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    (pt a b e τ).im = (a : ℝ) / e * τ.im := by
  have h1 : (((a : ℂ) * (τ : ℂ) + b) / e).im = (a : ℝ) / e * τ.im := by
    rw [Complex.div_natCast_im]
    simp
    ring
  have hpos : 0 < (((a : ℂ) * (τ : ℂ) + b) / e).im := by
    rw [h1]
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have he' : (0 : ℝ) < e := by exact_mod_cast he
    positivity
  unfold pt
  rwa [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]

theorem mdiff_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff fun τ => f $ pt a b e τ := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hmap : Set.MapsTo (fun z => ((a : ℂ) * z + b) / e) {z | 0 < z.im} {z | 0 < z.im} := by
    intro z hz
    have h := pt_im ha he b ⟨z, hz⟩
    have h2 := congrArg Complex.im $ pt_coe ha he b ⟨z, hz⟩
    have h3 := (pt a b e ⟨z, hz⟩).im_pos
    rw [UpperHalfPlane.coe_im] at h2
    rwa [h2] at h3
  refine (hf.comp (by fun_prop) hmap).congr fun z hz => ?_
  simp [Function.comp_apply, pt, ofComplex_apply_of_im_pos hz]

theorem tendsto_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) :
    Filter.Tendsto (pt a b e) atImInfty atImInfty := by
  rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
  have h : (UpperHalfPlane.im ∘ pt a b e) = fun τ => (a : ℝ) / e * τ.im := funext fun τ => pt_im ha he b τ
  rw [h]
  have hc : (0 : ℝ) < (a : ℝ) / e := by positivity
  exact Filter.Tendsto.const_mul_atTop hc Filter.tendsto_comap

theorem bdd_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ}
    (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty fun τ => f $ pt a b e τ := by
  exact hf.comp_tendsto $ tendsto_pt ha he b

theorem fac_mdiff {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : MDiff (fac t) := by
  have hA := isMF_AA.mdiff
  have hD := isMF_DD.mdiff
  exact (hA.mul $ mdiff_comp_pt ht.1 ht.2 t.2.1 hD).sub $ (mdiff_comp_pt ht.1 ht.2 t.2.1 hA).mul hD

theorem fac_bdd {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : IsBoundedAtImInfty $ fac t := by
  have hA := isMF_AA.bdd
  have hD := isMF_DD.bdd
  exact (hA.mul $ bdd_comp_pt ht.1 ht.2 t.2.1 hD).sub $ (bdd_comp_pt ht.1 ht.2 t.2.1 hA).mul hD

theorem Gm_mdiff {m : ℕ} (hm : 0 < m) : MDiff (Gm m) := by
  unfold Gm
  have key : ∀ s, s ⊆ Tm m → MDiff fun τ => ∏ t ∈ s, fac t τ := by
    intro s
    induction s using induction_on with
    | empty =>
      intro _
      simpa using (mdifferentiable_const : MDiff fun _ : ℍ => (1 : ℂ))
    | insert t s ht ih =>
      intro hs
      simp [prod_insert ht]
      exact (fac_mdiff $ Tm_pos hm $ hs $ mem_insert_self t s).mul
        $ ih fun x hx => hs $ mem_insert_of_mem hx
  exact key _ subset_rfl

theorem Gm_bdd {m : ℕ} (hm : 0 < m) : IsBoundedAtImInfty $ Gm m := by
  unfold Gm
  have key : ∀ s, s ⊆ Tm m → IsBoundedAtImInfty fun τ => ∏ t ∈ s, fac t τ := by
    intro s
    induction s using induction_on with
    | empty =>
      intro _
      simp [Finset.prod_empty]
      exact Filter.const_boundedAtFilter atImInfty (1 : ℂ)
    | insert t s ht ih =>
      intro hs
      simp [prod_insert ht]
      exact Filter.BoundedAtFilter.mul (fac_bdd $ Tm_pos hm $ hs $ mem_insert_self t s)
        $ ih fun x hx => hs $ mem_insert_of_mem hx
  exact key _ subset_rfl

theorem Gm_slash {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    (Gm m) ∣[24 * ((Tm m).card : ℤ)] γ = Gm m := by
  funext τ
  rw [SL_slash_apply, Gm_smul hm γ τ]
  have : (24 * ((Tm m).card : ℤ)) = ((24 * (Tm m).card : ℕ) : ℤ) := by push_cast
                                                                       ring
  rw [this, zpow_neg, zpow_natCast]
  field_simp

theorem gmForm {m : ℕ} (hm : 0 < m) : IsMF (24 * ((Tm m).card : ℤ)) $ Gm m := by
  refine ⟨{ toFun := Gm m
            slash_action_eq' := ?_
            holo' := Gm_mdiff hm
            bdd_at_cusps' := ?_ }, fun τ => rfl⟩
  intro A hA
  obtain ⟨A, rfl⟩ := hA
  exact Gm_slash hm A
  intro c hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ _
  rw [Gm_slash hm γ]
  exact Gm_bdd hm

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open PowerSeries (coeff coeff_one)
open Real (pi)
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem prodSer_coeffIn {m : ℕ} (hm : 0 < m) : CoeffIn (Rm m) $ prodSer m := by
  unfold prodSer
  refine Finset.prod_induction _ (CoeffIn $ Rm m) (fun a b ha hb => ha.mul hb) ?_
    fun t ht => facSer_coeffIn hm ht
  intro n
  rw [coeff_one]
  split_ifs
  exact Subring.one_mem _
  exact Subring.zero_mem _

theorem prodSer_conv {m : ℕ} (hm : 0 < m) : Conv $ prodSer m := by
  unfold prodSer
  refine Finset.prod_induction _ Conv (fun a b ha hb => ha.mul hb) ?_
    fun t ht => facSer_conv hm ht
  intro x _
  refine (hasSum_single 0 fun n hn => ?_).summable
  simp [coeff_one, hn]

theorem prodSer_ev {m : ℕ} (hm : 0 < m) (τ : ℍ) : ev (prodSer m) (qm m τ) = Gm m τ := by
  have hx : ‖qm m τ‖ < 1 := by
    unfold qm
    rw [Complex.norm_exp]
    have e : (2 * (pi : ℂ) * Complex.I * (τ : ℂ) / (m : ℂ)).re = -(2 * pi * τ.im) / m := by
      rw [Complex.div_natCast_re]
      simp
    rw [e, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr $ div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos, τ.im_pos]) $ by exact_mod_cast hm
  have h1 : Conv (1 : PowerSeries ℂ) := by
    intro x _
    refine (hasSum_single 0 fun n hn => ?_).summable
    simp [coeff_one, hn]
  have key : ∀ s ⊆ Tm m, Conv (∏ t ∈ s, facSer m t) ∧
      ev (∏ t ∈ s, facSer m t) (qm m τ) = ∏ t ∈ s, fac t τ := by
    intro s
    classical
    refine Finset.induction_on s ?_ ?_
    intro _
    refine ⟨by simpa using h1, ?_⟩
    simp [Finset.prod_empty]
    unfold ev
    rw [tsum_eq_single 0 fun n hn => by simp [coeff_one, hn]]
    simp
    intro a s ha ih hs
    have has := hs $ Finset.mem_insert_self a s
    obtain ⟨c1, c2⟩ := ih fun y hy => hs $ Finset.mem_insert_of_mem hy
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    constructor
    exact (facSer_conv hm has).mul c1
    rw [ev_mul (facSer_conv hm has) c1 hx, facSer_ev hm has, c2]
  unfold prodSer Gm
  exact (key _ subset_rfl).2

theorem prodSer_low {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) : ∃ n0 u, LowUnit (Rm m) (prodSer m) n0 u := by
  unfold prodSer
  refine LowUnit.prod _ _ fun t ht => facSer_low hm ht ?_
  intro heq
  apply hsq
  unfold Tm at ht
  rw [Finset.mem_image] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  rw [Finset.mem_sigma, Nat.mem_divisors] at hx
  dsimp only at heq
  use x.1
  have h2 := Nat.div_mul_cancel hx.1.1
  rw [← heq] at h2
  exact h2.symm

theorem gmQ_xp {m : ℕ} (hm : 0 < m) : xp m (qExpansion 1 $ Gm m) = prodSer m := by
  have hm0 : m ≠ 0 := hm.ne'
  have hF := gmForm hm
  refine eq_of_ev_eq (hF.conv.xp hm0) (prodSer_conv hm) ?_
  intro x hx0 hx1
  rw [ev_xp _ hm0]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog := Real.log_neg hx0 hx1

  let w : ℂ := ⟨(m : ℝ) * Complex.arg x / (2 * pi), -((m : ℝ) * Real.log ‖x‖) / (2 * pi)⟩
  have him : 0 < w.im := by
    apply div_pos _ $ by positivity
    nlinarith
  let τ : ℍ := ⟨w, him⟩
  have hτ : (τ : ℂ) = w := rfl
  have hlogx : 2 * (pi : ℂ) * Complex.I * w / (m : ℂ) = Complex.log x := by
    apply Complex.ext
    rw [Complex.div_natCast_re, Complex.log_re]
    simp [w]
    field_simp
    rw [Complex.div_natCast_im, Complex.log_im]
    simp [w]
    field_simp
  have hq : qm m τ = x := by
    unfold qm
    rw [hτ, hlogx, Complex.exp_log $ norm_pos_iff.mp hx0]
  have hq1 : qm 1 τ = x ^ m := by
    rw [← hq]
    unfold qm
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [← hq1, hF.ev_eq τ, ← prodSer_ev hm τ, hq]

theorem gmQ_coeffIn {m : ℕ} (hm : 0 < m) : CoeffIn (Rm m) $ qExpansion 1 $ Gm m := by
  intro n
  have h := congrArg (coeff $ m * n) $ gmQ_xp hm
  simp [xp, PowerSeries.coeff_mk, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hm] at h
  rw [h]
  exact prodSer_coeffIn hm $ m * n

theorem gmQ_low {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) :
    ∃ n0 u, LowUnit (Rm m) (qExpansion 1 $ Gm m) n0 u := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hn0⟩ := prodSer_low hm hsq
  have hc : ∀ n, coeff n (prodSer m) =
      if m ∣ n then coeff (n / m) $ qExpansion 1 $ Gm m else 0 := by
    intro n
    rw [← gmQ_xp hm]
    simp [xp]
  have hdvd : m ∣ n0 := by
    by_contra h
    rw [hc, if_neg h] at hn0
    exact hu3 hn0.symm
  obtain ⟨k, rfl⟩ := hdvd
  refine ⟨k, u, hu1, hu2, hu3, fun j hj => ?_, ?_⟩
  have h2 := hlow (m * j) $ by nlinarith
  rwa [hc, if_pos $ dvd_mul_right m j, Nat.mul_div_cancel_left j hm] at h2
  rwa [hc, if_pos $ dvd_mul_right m k, Nat.mul_div_cancel_left k hm] at hn0

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.analytic {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : AnalyticAt ℂ (cuspFunction 1 f) 0 := by
  obtain ⟨g, hg⟩ := hf
  have hfg := funext fun τ => (hg τ).symm
  subst hfg
  apply ModularFormClass.analyticAt_cuspFunction_zero g one_pos
  simp
theorem qExp_AA_pow (n : ℕ) : qExpansion 1 (fun τ => AA τ ^ n) = aC ^ n := by
  induction n with
  | zero =>
    have : (fun τ => AA τ ^ 0) = (1 : ℍ → ℂ) := by funext τ
                                                   simp
    rw [this, qExpansion_one, pow_zero]
  | succ n ih =>
    have : (fun τ => AA τ ^ (n + 1)) = (fun τ => AA τ ^ n) * AA := by funext τ
                                                                      simp [pow_succ]
    rw [this, qExpansion_mul (isMF_AA.pow n).analytic isMF_AA.analytic, ih, pow_succ, aC_eq]

theorem aC_coeff_zero : PowerSeries.coeff 0 aC = 1 := by
  have h4 : PowerSeries.coeff 0 e4Z = 1 := by rw [e4Z, PowerSeries.coeff_mk, if_pos rfl]
  rw [aC, aZ, PowerSeries.coeff_map]
  simp [pow_succ, PowerSeries.coeff_mul, h4]

theorem IsMF.div_DD {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f)
    (h0 : PowerSeries.coeff 0 (qExpansion 1 f) = 0) :
    ∃ h, IsMF (k - 12) h ∧ (∀ τ, f τ = DD τ * h τ) ∧
      qExpansion 1 f = dC * qExpansion 1 h := by
  obtain ⟨g, hg⟩ := hf
  obtain rfl : (⇑g : ℍ → ℂ) = f := funext hg
  refine ⟨CuspForm.discriminantEquiv $ toCuspForm g h0, ⟨_, fun _ => rfl⟩, fun τ => ?_, ?_⟩
  exact (discriminant_mul_discriminantEquiv_apply (toCuspForm g h0) τ).symm
  rw [dC_eq]
  exact qExpansion_eq_qExpansion_discriminant_mul g h0

theorem coeff_mul_low (V G : PowerSeries ℂ) (hV : PowerSeries.coeff 0 V = 1) (n : ℕ)
    (hG : ∀ i < n, PowerSeries.coeff i G = 0) :
    (∀ i < n, PowerSeries.coeff i (V * G) = 0) ∧
      PowerSeries.coeff n (V * G) = PowerSeries.coeff n G := by
  constructor
  intro i hi
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [hG x.2 $ by omega, mul_zero]
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
  rw [hV, one_mul]
  intro x hx hne
  obtain ⟨a, b⟩ := x
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hb : b < n := by
    by_contra hb'
    apply hne
    have ha0 : a = 0 := by simp only at hx
                           omega
    have hbn : b = n := by simp only at hx
                           omega
    rw [ha0, hbn]
  rw [hG b hb, mul_zero]
  intro h
  exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 $ by simp) h

theorem exists_dC_inv : ∃ v, PowerSeries.coeff 0 v = 1 ∧
    ∀ H, PowerSeries.X * H = v.map (Int.castRingHom ℂ) * (dC * H) := by
  set u : PowerSeries ℤ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) dZ with hu
  have hd0 : PowerSeries.coeff 0 dZ = 0 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ]
  have hd1 : PowerSeries.coeff 1 dZ = 1 := by
    rw [dZ, PowerSeries.coeff_mk]
    simp [e4Z, e6Z, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ] <;> norm_num
  have hXu : dZ = PowerSeries.X * u := by
    ext n
    rcases n with _ | n
    rw [hd0, PowerSeries.coeff_zero_X_mul]
    rw [PowerSeries.coeff_succ_X_mul, hu, PowerSeries.coeff_mk]
  refine ⟨PowerSeries.invOfUnit u 1, ?_, fun H => ?_⟩
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  have hinv := PowerSeries.mul_invOfUnit u 1 $ by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hu, PowerSeries.coeff_mk, zero_add, hd1, Units.val_one]
  rw [dC, hXu, map_mul, PowerSeries.map_X]
  have h1 : (u.map $ Int.castRingHom ℂ) * (PowerSeries.invOfUnit u 1).map (Int.castRingHom ℂ) = 1 := by
    rw [← map_mul, hinv, map_one]
  linear_combination (-(PowerSeries.X * H)) * h1

theorem coeffIn_of_dC_mul (R : Subring ℂ) (H : PowerSeries ℂ) (h : CoeffIn R (dC * H)) : CoeffIn R H := by
  obtain ⟨v, -, hv⟩ := exists_dC_inv
  intro n
  rw [← PowerSeries.coeff_succ_X_mul, hv H, PowerSeries.coeff_mul]
  refine sum_mem fun x _ => mul_mem ?_ $ h x.2
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem _ _

theorem low_of_dC_mul (H : PowerSeries ℂ) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (dC * H) = 0) (h1 : PowerSeries.coeff n0 (dC * H) = u) :
    ∃ k, n0 = k + 1 ∧ (∀ n < k, PowerSeries.coeff n H = 0) ∧ PowerSeries.coeff k H = u := by
  obtain ⟨v, hv0, hv⟩ := exists_dC_inv
  have hV : PowerSeries.coeff 0 (v.map $ Int.castRingHom ℂ) = 1 := by
    rw [PowerSeries.coeff_map, hv0, map_one]
  obtain ⟨hlow, hn0⟩ := coeff_mul_low _ _ hV n0 h0
  rw [h1, ← hv H] at hn0
  rw [← hv H] at hlow
  rcases n0 with _ | k
  rw [PowerSeries.coeff_zero_X_mul] at hn0
  exact absurd hn0.symm hu
  refine ⟨k, rfl, fun n hn => ?_, ?_⟩
  rw [← PowerSeries.coeff_succ_X_mul]
  apply hlow _
  omega
  rwa [← PowerSeries.coeff_succ_X_mul]

theorem exists_integral_poly_of_qExpansion (R : Subring ℂ) (N : ℕ) : ∀ f : ℍ → ℂ, IsMF (12 * (N : ℤ)) f →
    CoeffIn R (qExpansion 1 f) →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
      (∀ τ, f τ = DD τ ^ N * P.eval (jT τ)) ∧
      ∀ n0 (u : ℂ), u ≠ 0 → (∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0) →
        PowerSeries.coeff n0 (qExpansion 1 f) = u → P.leadingCoeff = u := by
  induction N with
  | zero =>
    intro f hf hR
    obtain ⟨g, hg⟩ := hf.congr_weight (k' := 0) $ by simp
    obtain ⟨c, hc⟩ := levelOne_weight_zero_const g
    have hfc : f = c • (1 : ℍ → ℂ) := by
      funext τ
      rw [← hg τ, hc]; simp
    have hq : qExpansion 1 f = c • (1 : PowerSeries ℂ) := by
      have h1 : AnalyticAt ℂ (cuspFunction 1 (1 : ℍ → ℂ)) 0 := by
        have : IsMF 0 (1 : ℍ → ℂ) := ⟨1, fun τ => by simp⟩
        exact this.analytic
      rw [hfc, qExpansion_smul h1, qExpansion_one]
    refine ⟨Polynomial.C c, fun i => ?_, by simp, fun τ => ?_, fun n0 u hu h0 h1 => ?_⟩
    have := hR 0
    rw [hq] at this
    rw [Polynomial.coeff_C]
    split_ifs
    simpa using this
    exact R.zero_mem
    rw [hfc]
    simp
    rw [hq] at h1
    rw [Polynomial.leadingCoeff_C]
    cases n0 with
    | zero => simpa using h1
    | succ k =>
      exfalso
      apply hu; rw [← h1]
      simp [PowerSeries.coeff_one]
  | succ N ih =>
    intro f hf hR
    set a0 : ℂ := PowerSeries.coeff 0 (qExpansion 1 f) with ha0
    have hA : IsMF (12 * ((N + 1 : ℕ) : ℤ)) fun τ => AA τ ^ (N + 1) :=
      (isMF_AA.pow $ N + 1).congr_weight $ by ring
    have hqg : qExpansion 1 (fun τ => f τ - a0 * AA τ ^ (N + 1)) =
        qExpansion 1 f - a0 • aC ^ (N + 1) := by
      have e1 : (fun τ => f τ - a0 * AA τ ^ (N + 1)) = f - a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ
        simp
      have e2 : (fun τ => a0 * AA τ ^ (N + 1)) = a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ
        simp
      rw [e1, qExpansion_sub hf.analytic $ e2 ▸ (hA.const_mul a0).analytic, qExpansion_smul hA.analytic,
        qExp_AA_pow]
    have haR := hR 0
    have hac : ∀ n, PowerSeries.coeff n (aC ^ (N + 1)) ∈ R := by
      intro n
      have : aC ^ (N + 1) = (aZ ^ (N + 1)).map (Int.castRingHom ℂ) := by rw [map_pow]
                                                                         rfl
      rw [this, PowerSeries.coeff_map]
      exact intCast_mem R _
    have hac0 : PowerSeries.coeff 0 (aC ^ (N + 1)) = 1 := by
      have := aC_coeff_zero
      simp only [PowerSeries.coeff_zero_eq_constantCoeff] at this ⊢
      rw [map_pow, this, one_pow]
    obtain ⟨h, hh, hfh, hqh⟩ := (hf.sub $ hA.const_mul a0).div_DD (by rw [hqg, map_sub, PowerSeries.coeff_smul, hac0]; simp [ha0])
    obtain ⟨P', hP1, hP2, hP3, hP4⟩ := ih h (hh.congr_weight (by push_cast; ring)) $ by
        apply coeffIn_of_dC_mul
        rw [← hqh, hqg]
        intro n
        rw [map_sub, PowerSeries.coeff_smul]
        exact R.sub_mem (hR n) $ R.mul_mem haR $ hac n
    refine ⟨Polynomial.C a0 * Polynomial.X ^ (N + 1) + P', fun i => ?_, ?_, fun τ => ?_,
      fun n0 u hu h0 h1 => ?_⟩
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
    refine R.add_mem ?_ $ hP1 i
    split_ifs
    exact haR
    exact R.zero_mem
    refine (Polynomial.natDegree_add_le _ _).trans $ max_le ?_ $ by omega
    exact Polynomial.natDegree_C_mul_X_pow_le _ _
    have hD := DD_ne_zero τ
    have e := hfh τ
    rw [hP3 τ] at e
    have : f τ = a0 * AA τ ^ (N + 1) + DD τ * (DD τ ^ N * P'.eval (jT τ)) := by
      rw [← e]
      ring
    rw [this]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    have hj : DD τ ^ (N + 1) * jT τ ^ (N + 1) = AA τ ^ (N + 1) := by
      rw [← mul_pow, jT, mul_div_cancel₀ _ hD]
    rw [← hj]
    ring
    by_cases hz : a0 = 0
    have hq' : qExpansion 1 f = dC * qExpansion 1 h := by
      rw [← hqh, hqg, hz]
      simp
    rw [hq'] at h0 h1
    obtain ⟨k, -, hk0, hk1⟩ := low_of_dC_mul _ n0 u hu h0 h1
    rw [hz]
    simp only [map_zero, zero_mul, zero_add]
    exact hP4 k u hu hk0 hk1
    have hn0 : n0 = 0 := by
      by_contra hne
      exact hz $ h0 0 $ Nat.pos_of_ne_zero hne
    subst hn0
    rw [Polynomial.leadingCoeff_add_of_degree_lt', Polynomial.leadingCoeff_mul_X_pow,
      Polynomial.leadingCoeff_C]
    exact h1
    rw [Polynomial.degree_C_mul_X_pow _ hz]
    refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hP2) ?_
    exact_mod_cast Nat.lt_succ_self N


theorem qPrin_low (R : Subring ℂ) (N : ℕ) (f : ℍ → ℂ) (hf : IsMF (12 * (N : ℤ)) f)
    (hR : CoeffIn R $ qExpansion 1 f) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0)
    (h1 : PowerSeries.coeff n0 (qExpansion 1 f) = u) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧ P.leadingCoeff = u ∧
      ∀ τ, f τ = DD τ ^ N * P.eval (jT τ) := by
  obtain ⟨P, hc, hd, he, hl⟩ := exists_integral_poly_of_qExpansion R N f hf hR
  exact ⟨P, hc, hd, hl n0 u hu h0 h1, he⟩

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem fac_eq_zero_of_smul (t : ℕ × ℕ × ℕ) (τ : ℍ) (γ : SL(2, ℤ))
    (h : γ • pt t.1 t.2.1 t.2.2 τ = τ) : fac t τ = 0 := by
  unfold fac
  have h1 : AA τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * AA (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← AA_smul, h]
  have h2 : DD τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * DD (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← DD_smul, h]
  rw [h1, h2]
  ring

private lemma exists_SL2_mul_eq_Tmat_of_det_eq {m : ℕ} (hm : 0 < m) (A B C D : ℤ) (hdet : A * D - B * C = m) :
    ∃ g : SL(2, ℤ), ∃ s ∈ Tm m, 0 < s.2.2 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) * !![A, B; C, D] = Tmat s := by
  have hAC : A ≠ 0 ∨ C ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (m : ℤ) = 0 := by rw [← hdet, hc.1, hc.2]
                                ring
    omega
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = Int.gcd A C := ⟨_, rfl⟩
  have hGpos : 0 < G := by
    rw [hG]
    first
    | exact Int.gcd_pos_iff.mpr hAC
    | (rcases hAC with h | h
       exact Int.gcd_pos_of_ne_zero_left C h
       exact Int.gcd_pos_of_ne_zero_right A h)
  obtain ⟨a0, ha0⟩ : (G : ℤ) ∣ A := by
    rw [hG]
    first | exact Int.gcd_dvd_left | exact Int.gcd_dvd_left A C | exact Int.gcd_dvd_left _ _
  obtain ⟨c0, hc0⟩ : (G : ℤ) ∣ C := by
    rw [hG]
    first | exact Int.gcd_dvd_right | exact Int.gcd_dvd_right A C | exact Int.gcd_dvd_right _ _
  obtain ⟨x, y, hbez⟩ : ∃ x y : ℤ, (G : ℤ) = A * x + C * y :=
    ⟨_, _, by rw [hG]; exact Int.gcd_eq_gcd_ab A C⟩
  have hG0 : (G : ℤ) ≠ 0 := by exact_mod_cast hGpos.ne'
  have h1 : a0 * x + c0 * y = 1 := by
    apply mul_left_cancel₀ hG0
    linear_combination -hbez - x * ha0 - y * hc0
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = a0 * D - c0 * B := ⟨_, rfl⟩
  have hGd : (G : ℤ) * d = m := by
    rw [hd]
    linear_combination hdet - D * ha0 + B * hc0
  have hdpos : 0 < d := by
    have h2 : 0 < (G : ℤ) * d := by rw [hGd]
                                    exact_mod_cast hm
    have h3 : (0 : ℤ) < G := by exact_mod_cast hGpos
    by_contra h4
    push_neg at h4
    nlinarith
  obtain ⟨q, b, hdiv, hb0, hbd⟩ : ∃ q b : ℤ, d * q + b = x * B + y * D ∧ 0 ≤ b ∧ b < d :=
    ⟨(x * B + y * D) / d, (x * B + y * D) % d,
      (by first
          | (have h5 := Int.emod_add_ediv (x * B + y * D) d; linarith)
          | (have h5 := Int.ediv_add_emod' (x * B + y * D) d; linarith)
          | (have h5 := Int.mul_ediv_add_emod (x * B + y * D) d; linarith)), Int.emod_nonneg _ hdpos.ne',
      Int.emod_lt_of_pos _ hdpos⟩
  have hdet1 : (x + q * c0) * a0 - (y - q * a0) * -c0 = 1 := by linear_combination h1
  have e1 : (x + q * c0) * A + (y - q * a0) * C = (G : ℤ) := by
    linear_combination -hbez + q * c0 * ha0 - q * a0 * hc0
  have e2 : (x + q * c0) * B + (y - q * a0) * D = b := by
    linear_combination -hdiv + q * hd
  have e3 : -c0 * A + a0 * C = 0 := by
    linear_combination -c0 * ha0 + a0 * hc0
  have e4 : -c0 * B + a0 * D = d := by
    linear_combination -hd
  lift d to ℕ using hdpos.le
  lift b to ℕ using hb0
  have hGdn : G * d = m := by exact_mod_cast hGd
  have hmd : m / G = d := by rw [← hGdn, Nat.mul_div_cancel_left _ hGpos]
  refine ⟨⟨!![x + q * c0, y - q * a0; -c0, a0], by rw [Matrix.det_fin_two_of]; exact hdet1⟩, (G, b, d), ?_, by show 0 < d; exact_mod_cast hdpos, ?_⟩
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
  refine ⟨⟨G, b⟩, ⟨⟨⟨d, hGdn.symm⟩, hm.ne'⟩, ?_⟩, ?_⟩
  rw [hmd]
  exact_mod_cast hbd
  simp [hmd]
  show !![x + q * c0, y - q * a0; -c0, a0] * !![A, B; C, D] = Tmat (G, b, d)
  rw [Matrix.mul_fin_two, e1, e2, e3, e4]
  all_goals first | rfl | (unfold Tmat; rfl) | simp [Tmat]

theorem Gm_vanish {m : ℕ} (hm : 0 < m) (τ : ℍ) (A B C D : ℤ) (hdet : A * D - B * C = m)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : Gm m τ = 0 := by
  obtain ⟨g, s, hs, he, hgs⟩ := exists_SL2_mul_eq_Tmat_of_det_eq hm A B C D hdet
  obtain ⟨p, q, r, w, hg⟩ : ∃ p q r w : ℤ, (g : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, w] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdg : p * w - q * r = 1 := by
    have h0 := Matrix.SpecialLinearGroup.det_coe g
    rwa [hg, Matrix.det_fin_two_of] at h0
  have hp : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by rw [hg]
                                                         rfl
  have hq : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q := by rw [hg]
                                                         rfl
  have hr : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r := by rw [hg]
                                                         rfl
  have hw : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = w := by rw [hg]
                                                         rfl
  rw [hg] at hgs
  unfold Tmat at hgs
  rw [Matrix.mul_fin_two] at hgs
  have ea : (s.1 : ℂ) = p * A + q * C := by exact_mod_cast (congrFun (congrFun hgs 0) 0).symm
  have eb : (s.2.1 : ℂ) = p * B + q * D := by exact_mod_cast (congrFun (congrFun hgs 0) 1).symm
  have ez : (r : ℂ) * A + w * C = 0 := by exact_mod_cast (congrFun (congrFun hgs 1) 0)
  have ee : (s.2.2 : ℂ) = r * B + w * D := by exact_mod_cast (congrFun (congrFun hgs 1) 1).symm
  have hE : (s.2.2 : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hden : (r : ℂ) * τ + w ≠ 0 := by
    intro h0
    have him : (r : ℝ) * τ.im = 0 := by
      have h3 := congrArg Complex.im h0
      simpa using h3
    have hτ := τ.im_pos
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp him with h4 | h4
      exact_mod_cast h4
      linarith
    rw [hr0] at h0
    have hw0 : w = 0 := by
      have h3 := congrArg Complex.re h0
      simp at h3
      exact_mod_cast h3
    rw [hr0, hw0] at hdg
    simp at hdg
  have c1 : ∀ z : ℤ, (((algebraMap ℤ ℝ) z : ℝ) : ℂ) = (z : ℂ) := by
    intro z
    rw [eq_intCast]
    push_cast
    rfl
  have hform : ((g • τ : ℍ) : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.σ, hp, hq, hr, hw]
    try rw [c1 p, c1 q, c1 r, c1 w]
  have hX : ((s.1 : ℂ) * τ + (s.2.1 : ℂ)) / (s.2.2 : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    rw [div_eq_div_iff hE hden]
    linear_combination ((τ : ℂ) * (r * τ + w)) * ea + ((r : ℂ) * τ + w) * eb
      + ((p : ℂ) * (r * τ + w) - (p * τ + q) * r) * hfix + ((p : ℂ) * τ + q) * τ * ez
      - ((p : ℂ) * τ + q) * ee
  have hpt : pt s.1 s.2.1 s.2.2 τ = g • τ := by
    unfold pt
    rw [hX, ← hform]
    first
    | exact UpperHalfPlane.ofComplex_apply $ g • τ
    | simp
  unfold Gm
  apply Finset.prod_eq_zero hs
  apply fac_eq_zero_of_smul s τ g⁻¹
  rw [hpt, inv_smul_smul]

end ReciprocityTheory.ChartRestriction.L1
end
section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem isIntegral_of_root {P : Polynomial ℂ} (hP : ∀ i, IsIntegral ℤ (P.coeff i))
    (hu : IsIntegral ℤ (P.leadingCoeff)⁻¹) (h0 : P.leadingCoeff ≠ 0) {x : ℂ} (hx : P.eval x = 0) :
    IsIntegral ℤ x := by
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff (Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one $ inv_mul_cancel₀ h0) (by
      rw [Polynomial.natDegree_C_mul $ inv_ne_zero h0]
      intro hd
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.eval_C] at hx
      apply h0
      rw [Polynomial.leadingCoeff, hd]
      exact hx) ?_ ?_
  rw [Polynomial.eval_mul, hx, mul_zero]
  exact isIntegral_zero
  intro i
  rw [Polynomial.coeff_C_mul]
  exact hu.mul $ hP i

theorem jT_isIntegral {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) {τ : ℍ} (h : Gm m τ = 0) :
    IsIntegral ℤ $ jT τ := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hcoef⟩ := gmQ_low hm hsq
  have hmf : IsMF (12 * ((2 * (Tm m).card : ℕ) : ℤ)) $ Gm m :=
    (gmForm hm).congr_weight (by push_cast; ring)
  obtain ⟨P, hPR, -, hlead, hval⟩ := qPrin_low (Rm m) _ (Gm m) hmf (gmQ_coeffIn hm) n0 u hu3 hlow hcoef
  have h1 := hval τ
  rw [h] at h1
  have h2 : P.eval (jT τ) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    exact absurd h3 $ pow_ne_zero _ $ DD_ne_zero τ
    exact h3
  exact isIntegral_of_root (fun i => Rm_isIntegral hm $ hPR i) (by rw [hlead]; exact Rm_isIntegral hm hu2)
    (by rw [hlead]; exact hu3) h2

theorem cm1 : JInvariantIntegrality := by
  intro d L hsf hd4 hL
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hd : 0 < d := by omega
  obtain ⟨A, B, C, D, h1, h2, h3⟩ := cmPoint hd hL hτ (-1) 2
  rw [jInv_eq_jT hτ]
  refine jT_isIntegral hd ?_ $ Gm_vanish hd τ A B C D (by linarith) ?_
  rintro ⟨r, hr⟩
  have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [hr, Nat.mul_mod, h] at hd4
  rw [← h1, h2]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
section
open Subring (subset_closure sum_mem zsmul_mem)
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Polynomial

variable (l : ℕ) [Fact l.Prime]

def muM : Submonoid ℂ_[l] where
  carrier := muP l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' $ Nat.dvd_one.1 h, one_pow 1⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
      · exact hln h
      · exact hlm h
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]

theorem muM_common (S : Finset (muM l)) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ ∀ a ∈ S, (a : ℂ_[l]) ^ n = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' $ Nat.dvd_one.1 h, by simp⟩
  | insert a S _ ih =>
    obtain ⟨n, hn, hln, hS⟩ := ih
    obtain ⟨m, hm, hlm, ha⟩ := a.2
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    rcases ((Fact.out : l.Prime).dvd_mul).1 h with h | h
    exact hln h
    exact hlm h
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    rw [mul_comm, pow_mul, ha, one_pow]
    rw [pow_mul, hS b hb, one_pow]

theorem muM_exists_gen (n : ℕ) (hn : 0 < n) :
    ∃ g, g ^ n = 1 ∧ ∀ a : ℂ_[l], a ^ n = 1 → ∃ k : ℕ, g ^ k = a := by
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := rootsOfUnity n ℂ_[l])
  refine ⟨((g : ℂ_[l]ˣ) : ℂ_[l]), ?_, fun a ha => ?_⟩
  have := g.2
  rwa [mem_rootsOfUnity'] at this
  obtain ⟨k, hk⟩ := hg $ rootsOfUnity.mkOfPowEq a ha
  use k
  have := congrArg (fun x : rootsOfUnity n ℂ_[l] => ((x : ℂ_[l]ˣ) : ℂ_[l])) hk
  simpa using this

theorem muM_eval_pow_eq_zero {K : Type*} [Field K] [CharZero K] (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n)
    (g : K) (hg : g ^ n = 1) (p : ℤ[X]) (hp : p.eval₂ (Int.castRingHom K) g = 0) :
    p.eval₂ (Int.castRingHom K) (g ^ l) = 0 := by
  rw [← algebraMap_int_eq, ← aeval_def] at hp ⊢
  have hd := orderOf_dvd_of_pow_eq_one hg
  have hprim := IsPrimitiveRoot.orderOf g
  have hdvd := minpoly.isIntegrallyClosed_dvd (hprim.isIntegral $ Nat.pos_of_dvd_of_pos hd hn) hp
  rw [hprim.minpoly_eq_pow_coprime $ ((Fact.out : l.Prime).coprime_iff_not_dvd).2 fun h => hln $ h.trans hd] at hdvd
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd $ minpoly.aeval ℤ $ g ^ l

def phiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] := MonoidAlgebra.lift ℤ ℂ_[l] (muM l) (muM l).subtype

def psiM : MonoidAlgebra ℤ (muM l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muM l) $ (muM l).subtype.comp $ powMonoidHom l

theorem phiM_ker_le (f : MonoidAlgebra ℤ (muM l)) (hf : phiM l f = 0) : psiM l f = 0 := by
  classical
  obtain ⟨n, hn, hln, hS⟩ := muM_common l f.coeff.support
  obtain ⟨g, hg, hgen⟩ := muM_exists_gen l n hn
  have hk : ∀ a : muM l, ∃ k : ℕ, a ∈ f.coeff.support → g ^ k = (a : ℂ_[l]) := by
    intro a
    by_cases ha : a ∈ f.coeff.support
    obtain ⟨k, hk⟩ := hgen a $ hS a ha
    exact ⟨k, fun _ => hk⟩
    exact ⟨0, fun h => absurd h ha⟩
  choose k hk using hk
  have h2 := muM_eval_pow_eq_zero l n hn hln g hg (∑ a ∈ f.coeff.support, C (f.coeff a) * X ^ (k a)) $ by
      rw [← hf, phiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, hk a ha]
      simp [zsmul_eq_mul]
  rw [← h2, psiM, MonoidAlgebra.lift_apply, Finsupp.sum, eval₂_finsetSum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul, mul_comm l, pow_mul, hk a ha]
  simp [zsmul_eq_mul]

theorem phiM_mem (f : MonoidAlgebra ℤ (muM l)) : phiM l f ∈ Rmu l := by
  rw [phiM, MonoidAlgebra.lift_apply]
  exact sum_mem _ fun a _ => zsmul_mem _ (subset_closure a.2) _

theorem psiM_mem (f : MonoidAlgebra ℤ (muM l)) : psiM l f ∈ Rmu l := by
  rw [psiM, MonoidAlgebra.lift_apply]
  exact sum_mem _ fun a _ => zsmul_mem _ (subset_closure (a ^ l).2) _

theorem phiM_surj (x : ℂ_[l]) (hx : x ∈ Rmu l) : ∃ f, phiM l f = x := by
  have : Rmu l ≤ (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).range := by
    refine Subring.closure_le.2 fun ζ hζ => ⟨MonoidAlgebra.single ⟨ζ, hζ⟩ 1, ?_⟩
    simp [phiM]
  exact this hx

theorem rmu_sigma : ∃ s : Rmu l →+* Rmu l,
    ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l), ((s ⟨ζ, subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l := by
  let φ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (phiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) $ phiM_mem l
  let ψ : MonoidAlgebra ℤ (muM l) →+* Rmu l :=
    (psiM l : MonoidAlgebra ℤ (muM l) →+* ℂ_[l]).codRestrict (Rmu l) $ psiM_mem l
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf⟩ := phiM_surj l x hx
    exact ⟨f, Subtype.ext hf⟩
  refine ⟨RingHom.liftOfSurjective φ hφ ⟨ψ, by
      intro f hf
      rw [RingHom.mem_ker] at hf ⊢
      exact Subtype.ext (phiM_ker_le l f $ congrArg Subtype.val hf)⟩, fun ζ hζ => ?_⟩
  have h1 : (⟨ζ, subset_closure hζ⟩ : Rmu l) = φ (MonoidAlgebra.single ⟨ζ, hζ⟩ 1) :=
    Subtype.ext (by simp [φ, phiM])
  rw [h1, RingHom.liftOfRightInverse_comp_apply]
  simp [ψ, psiM]

theorem rmu_sigma_congr (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ∃ r ∈ Rmu l, ((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l = (l : ℂ_[l]) * r := by
  have hl : l.Prime := Fact.out
  have key : ∀ y hy, ∃ r, s ⟨y, hy⟩ - ⟨y, hy⟩ ^ l = (l : Rmu l) * r := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem ζ hζ => exact ⟨0, Subtype.ext (by simp [hs ζ hζ])⟩
    | zero =>
      use 0
      have : (⟨0, zero_mem _⟩ : Rmu l) = 0 := rfl
      rw [this, map_zero, zero_pow hl.ne_zero]
      simp
    | one =>
      use 0
      have : (⟨1, one_mem _⟩ : Rmu l) = 1 := rfl
      rw [this, map_one, one_pow]
      simp
    | add a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      obtain ⟨u, hu⟩ := exists_add_pow_prime_eq hl (⟨a, ha⟩ : Rmu l) ⟨b, hb⟩
      use r + t - ⟨a, ha⟩ * ⟨b, hb⟩ * u
      have : (⟨a + b, add_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this, map_add, hu]
      linear_combination hr + ht
    | neg a ha iha =>
      obtain ⟨r, hr⟩ := iha
      have : (⟨-a, neg_mem ha⟩ : Rmu l) = -⟨a, ha⟩ := rfl
      rw [this, map_neg]
      rcases hl.eq_two_or_odd' with h2 | hodd
      refine ⟨-r - ⟨a, ha⟩ ^ 2, ?_⟩
      subst h2
      push_cast at hr ⊢
      linear_combination -hr
      refine ⟨-r, ?_⟩
      rw [hodd.neg_pow]
      linear_combination -hr
    | mul a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      use r * s ⟨b, hb⟩ + ⟨a, ha⟩ ^ l * t
      have : (⟨a * b, mul_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, map_mul, mul_pow]
      linear_combination s ⟨b, hb⟩ * hr + ⟨a, ha⟩ ^ l * ht
  obtain ⟨r, hr⟩ := key x.1 x.2
  use r, r.2
  have := congrArg (Subtype.val) hr
  simpa using this

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation

open Polynomial Finset

variable (l : ℕ) [Fact l.Prime]

theorem norm_eq_of_norm_sub_lt' {a b : ℂ_[l]} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - b) (y := b) h.ne
  rwa [sub_add_cancel, max_eq_right h.le] at this

theorem exists_root_near (P : ℂ_[l][X]) (hP : P.Monic) (x : ℂ_[l]) (h : ‖P.eval x‖ < 1) :
    ∃ a, P.IsRoot a ∧ ‖x - a‖ < 1 := by
  by_contra hcon
  push Not at hcon
  have key : ∀ s : Multiset ℂ_[l], (∀ a ∈ s, 1 ≤ ‖x - a‖) →
      1 ≤ ‖((s.map fun a => X - C a).prod).eval x‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul]
      simp [eval_sub, eval_X, eval_C]
      exact one_le_mul_of_one_le_of_one_le (hs a $ Multiset.mem_cons_self _ _)
        $ ih fun b hb => hs b $ Multiset.mem_cons_of_mem hb
  have := key P.roots fun a ha => hcon a $ (mem_roots hP.ne_zero).1 ha
  rw [prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP IsAlgClosed.card_roots_eq_natDegree] at this
  linarith

theorem norm_pow_sub_one_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) : ‖y ^ k - 1‖ ≤ ‖y - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le ?_ le_rfl
    rwa [norm_mul, hy, one_mul]

theorem norm_geom_sum_sub_le {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) :
    ‖(∑ i ∈ range k, y ^ i) - k‖ ≤ ‖y - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (∑ i ∈ range (k + 1), y ^ i) - ((k + 1 : ℕ) : ℂ_[l]) =
        ((∑ i ∈ range k, y ^ i) - k) + (y ^ k - 1) := by
      rw [sum_range_succ]
      push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le ih $ norm_pow_sub_one_le l hy k

theorem norm_geom_sum_eq_one {y : ℂ_[l]} (hy : ‖y - 1‖ < 1) {m : ℕ} (hm : ‖(m : ℂ_[l])‖ = 1) :
    ‖∑ i ∈ range m, y ^ i‖ = 1 := by
  have := norm_geom_sum_sub_le l (by
      have := norm_eq_of_norm_sub_lt' l (a := y) (b := 1) $ by rwa [norm_one]
      rwa [norm_one] at this) m
  rw [← hm]
  apply norm_eq_of_norm_sub_lt' l
  rw [hm]
  exact lt_of_le_of_lt this hy
end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
end
section
open Set (mem_insert mem_insert_of_mem)
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Polynomial

variable (l : ℕ) [Fact l.Prime]

theorem norm_natCast_Cl (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← PadicComplex.norm_extends' l (n : ℚ_[l])]
  congr 1
  simp

theorem norm_sub_le_max_Cl (a b : ℂ_[l]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ :=
  by simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a $ -b

theorem norm_l_Cl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_Cl, Padic.norm_p]

theorem norm_natCast_Cl_of_not_dvd {n : ℕ} (hn : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by
  rw [norm_natCast_Cl, Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hn

theorem muP_norm {ζ : ℂ_[l]} (hζ : ζ ∈ muP l) : ‖ζ‖ = 1 := by
  obtain ⟨n, hn, -, h⟩ := hζ
  have : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

theorem tch_norm_le {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ‖ξ‖ ≤ 1 := by
  rcases hξ with rfl | h
  simp
  exact (muP_norm l h).le

theorem tch_mul {ξ ξ' : ℂ_[l]} (h : ξ ∈ Tch l) (h' : ξ' ∈ Tch l) : ξ * ξ' ∈ Tch l := by
  rcases h with rfl | ⟨n, hn, hln, hζ⟩
  rw [zero_mul]
  exact mem_insert _ _
  rcases h' with rfl | ⟨m, hm, hlm, hζ'⟩
  rw [mul_zero]
  exact mem_insert _ _
  refine mem_insert_of_mem _ ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  intro hd
  rcases ((Fact.out : l.Prime).dvd_mul).1 hd with h1 | h1
  exact hln h1
  exact hlm h1
  rw [mul_pow, pow_mul, hζ, one_pow, one_mul, mul_comm n m, pow_mul, hζ', one_pow]

theorem tch_inv {ξ : ℂ_[l]} (h : ξ ∈ Tch l) : ξ⁻¹ ∈ Tch l := by
  rcases h with rfl | ⟨n, hn, hln, hζ⟩
  rw [inv_zero]
  exact mem_insert _ _
  exact mem_insert_of_mem _ ⟨n, hn, hln, by rw [inv_pow, hζ, inv_one]⟩

theorem tch_near (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (f : ℕ) (hf : 0 < f) (r : ℝ) (hr : r < 1)
    (h : ‖x ^ (l ^ f) - x‖ ≤ r) : ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ r := by
  have hq := le_trans ((Fact.out : l.Prime).two_le) (Nat.le_self_pow hf.ne' l)
  obtain ⟨m, hm⟩ : ∃ m, l ^ f = m + 1 := ⟨l ^ f - 1, by omega⟩
  have hm0 : 0 < m := by omega
  have hlm : ¬ l ∣ m := by
    intro hd
    have h1 := hm ▸ dvd_pow_self l hf.ne'
    have h2 := (Nat.dvd_add_right hd).1 h1
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h2)
  by_cases hsmall : ‖x‖ ≤ r
  exact ⟨0, mem_insert _ _, by simpa using hsmall⟩
  push Not at hsmall
  have hx1 : ‖x‖ = 1 := by
    have h1 : ‖x‖ ≤ max ‖x ^ (l ^ f)‖ ‖x ^ (l ^ f) - x‖ := by
      calc ‖x‖ = ‖x ^ (l ^ f) - (x ^ (l ^ f) - x)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le_max_Cl l _ _
    have h2 : ‖x‖ ≤ ‖x‖ ^ (l ^ f) := by
      rw [← norm_pow]
      rcases le_max_iff.1 h1 with h3 | h3
      exact h3
      linarith
    by_contra hne
    have := pow_lt_self_of_lt_one₀ (lt_of_le_of_lt (le_trans (norm_nonneg _) h) hsmall) (lt_of_le_of_ne hx hne) (by omega : 1 < l ^ f)
    linarith
  have hxm : ‖x ^ m - 1‖ ≤ r := by
    have e : x ^ (l ^ f) - x = x * (x ^ m - 1) := by rw [hm]
                                                     ring
    rwa [e, norm_mul, hx1, one_mul] at h
  obtain ⟨ζ, hζroot, hζ⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near l (X ^ m - C 1)
    (monic_X_pow_sub_C 1 hm0.ne') x
    (by simp [eval_sub, eval_pow, eval_X, eval_C]; exact lt_of_le_of_lt hxm hr)
  have hζm : ζ ^ m = 1 := by
    have : ζ ^ m - 1 = 0 := by simpa using hζroot
    exact sub_eq_zero.1 this
  have hmu : ζ ∈ muP l := ⟨m, hm0, hlm, hζm⟩
  use ζ, mem_insert_of_mem _ hmu
  have hζ1 : ‖ζ‖ = 1 := muP_norm l hmu
  have hζ0 : ζ ≠ 0 := by rintro rfl
                         simp at hζ1
  have e1 : x - ζ = ζ * (x * ζ⁻¹ - 1) := by
    rw [mul_sub, mul_one, mul_comm x ζ⁻¹, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  have e2 : x ^ m - 1 = (∑ i ∈ Finset.range m, (x * ζ⁻¹) ^ i) * (x * ζ⁻¹ - 1) := by
    rw [geom_sum_mul, mul_pow, inv_pow, hζm, inv_one, mul_one]
  have hy : ‖x * ζ⁻¹ - 1‖ = ‖x - ζ‖ := by rw [e1, norm_mul, hζ1, one_mul]
  rw [e2, norm_mul, ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_eq_one l (hy ▸ hζ)
    $ norm_natCast_Cl_of_not_dvd l hlm, one_mul, hy] at hxm
  exact hxm

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem rmu_norm_le {x : ℂ_[l]} (hx : x ∈ Rmu l) : ‖x‖ ≤ 1 := by
  induction hx using Subring.closure_induction with
  | mem x hx => exact (muP_norm l hx).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    exact (IsUltrametricDist.norm_add_le_max x y).trans $ max_le hx hy
  | neg x _ hx => rwa [norm_neg]
  | mul x y _ _ hx hy =>
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

theorem kmu_frac {x : ℂ_[l]} (hx : x ∈ Kmu l) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, b ≠ 0 ∧ x = a / b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 hx
  by_cases hz0 : z = 0
  refine ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, one_ne_zero, ?_⟩
  rw [hz0, div_zero, zero_div]
  exact ⟨y, hy, z, hz, hz0, rfl⟩

theorem exists_power_mul_unitNorm (k : ℕ) : ∀ a ∈ Rmu l, a ≠ 0 → 1 < (l : ℝ) ^ k * ‖a‖ →
    ∃ m, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  induction k with
  | zero =>
    intro a ha _ h
    rw [pow_zero, one_mul] at h
    exact absurd (rmu_norm_le l ha) (not_le.2 h)
  | succ k ih =>
    intro a ha ha0 h
    rcases (rmu_norm_le l ha).eq_or_lt with h1 | h1
    exact ⟨0, a, ha, 1, (Rmu l).one_mem, h1, norm_one, by rw [pow_zero, one_mul, mul_one]⟩
    obtain ⟨f, hf, r, hr, he⟩ := rmu_frob l a ha
    have hl1 := (Fact.out : l.Prime).one_lt
    have hq : 1 ≤ l ^ f - 1 := by
      have : 2 ≤ l ^ f := le_trans (Fact.out : l.Prime).two_le (Nat.le_self_pow hf.ne' l)
      omega
    set u := a ^ (l ^ f - 1) - 1 with hu
    have hu1 : ‖u‖ = 1 := by
      have hsm : ‖a ^ (l ^ f - 1)‖ < 1 := by
        rw [norm_pow]
        apply pow_lt_one₀ (norm_nonneg _) h1
        omega
      have := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_eq_of_norm_sub_lt' l (a := u) (b := -1)
        (by rw [hu, sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one]; exact hsm)
      rwa [norm_neg, norm_one] at this
    have hau : a * u = (l : ℂ_[l]) * r := by
      rw [← he, hu, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ l ^ f)]
    have hnr : ‖r‖ = l * ‖a‖ := by
      have := congrArg norm hau
      rw [norm_mul, norm_mul, hu1, mul_one, norm_l_Cl] at this
      have hl0 : (l : ℝ) ≠ 0 := by positivity
      rw [this, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
    obtain ⟨m, c, hc, v, hv, hc1, hv1, hrv⟩ := ih r hr (by
        rintro rfl
        rw [norm_zero] at hnr
        have : (0 : ℝ) < l * ‖a‖ := mul_pos (by positivity) (norm_pos_iff.2 ha0)
        linarith) (by rw [hnr, ← mul_assoc, ← pow_succ]
                      exact h)
    refine ⟨m + 1, c, hc, u * v, mul_mem (sub_mem (pow_mem ha _) (Rmu l).one_mem) hv, hc1, by rw [norm_mul, hu1, hv1, one_mul], ?_⟩
    rw [← mul_assoc, hau, mul_assoc, hrv, pow_succ]
    ring

theorem rmu_shape {a : ℂ_[l]} (ha : a ∈ Rmu l) (ha0 : a ≠ 0) :
    ∃ m, ∃ c ∈ Rmu l, ∃ u ∈ Rmu l, ‖c‖ = 1 ∧ ‖u‖ = 1 ∧ a * u = (l : ℂ_[l]) ^ m * c := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖a‖⁻¹) (by exact_mod_cast (Fact.out : l.Prime).one_lt :
    (1 : ℝ) < l)
  refine exists_power_mul_unitNorm l k a ha ha0 ?_
  have hpos := norm_pos_iff.2 ha0
  calc (1 : ℝ) = ‖a‖⁻¹ * ‖a‖ := (inv_mul_cancel₀ hpos.ne').symm
    _ < (l : ℝ) ^ k * ‖a‖ := mul_lt_mul_of_pos_right hk hpos

theorem kmu_shape {x : ℂ_[l]} (hx : x ∈ Kmu l) (hx0 : x ≠ 0) :
    ∃ m : ℤ, ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ x = (l : ℂ_[l]) ^ m * (a / b) := by
  obtain ⟨a, ha, b, hb, hb0, rfl⟩ := kmu_frac l hx
  obtain ⟨m, c, hc, u, hu, hc1, hu1, hau⟩ := rmu_shape l ha (by rintro rfl; exact hx0 $ zero_div b)
  obtain ⟨n, d, hd, v, hv, hd1, hv1, hbv⟩ := rmu_shape l hb hb0
  have hu0 : u ≠ 0 := by rintro rfl
                         simp at hu1
  have hv0 : v ≠ 0 := by rintro rfl
                         simp at hv1
  refine ⟨(m : ℤ) - n, c * v, mul_mem hc hv, d * u, mul_mem hd hu,
    by rw [norm_mul, hc1, hv1, one_mul], by rw [norm_mul, hd1, hu1, one_mul], ?_⟩
  rw [zpow_sub₀ $ Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero, zpow_natCast, zpow_natCast]
  have ha' : a = (l : ℂ_[l]) ^ m * c / u := by rw [← hau, mul_div_cancel_right₀ _ hu0]
  have hb' : b = (l : ℂ_[l]) ^ n * d / v := by rw [← hbv, mul_div_cancel_right₀ _ hv0]
  rw [ha', hb']
  field_simp

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem rmu_le_kmu {x : ℂ_[l]} (hx : x ∈ Rmu l) : x ∈ Kmu l := by
  have h : Rmu l ≤ (Kmu l).toSubring := by
    rw [Rmu, Subring.closure_le]
    intro z hz
    exact Subfield.subset_closure hz
  exact h hx

theorem kmu_le_kur {x : ℂ_[l]} (hx : x ∈ Kmu l) : x ∈ MaximalUnramifiedExtension l := (Kmu l).le_topologicalClosure hx

theorem tch_mem_kur {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ξ ∈ MaximalUnramifiedExtension l := by
  rcases Set.mem_insert_iff.mp hξ with rfl | h
  exact (MaximalUnramifiedExtension l).zero_mem
  exact kmu_le_kur l $ Subfield.subset_closure h

theorem norm_sub_le_max_padic (x y : ℂ_[l]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.dist_triangle_max x 0 y
  rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, zero_sub, norm_neg] at h

theorem norm_eq_of_norm_sub_lt_max {x y : ℂ_[l]} (h : ‖x - y‖ < max ‖x‖ ‖y‖) : ‖x‖ = ‖y‖ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  have h1 := norm_sub_le_max_padic l x $ x - y
  rw [sub_sub_cancel] at h1
  rw [max_eq_right hlt.le] at h
  have h2 := max_lt hlt h
  linarith
  have h1 := norm_sub_le_max_padic l y $ y - x
  rw [sub_sub_cancel] at h1
  rw [max_eq_left hgt.le, norm_sub_rev] at h
  have h2 := max_lt hgt h
  linarith

private theorem norm_natCast_l_padicComplex_eq_inv : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends (p := l) ((l : ℚ_[l]) : PadicAlgCl l)
  rw [PadicAlgCl.norm_extends, Padic.norm_p] at h
  simp at h
  exact h

theorem norm_prime_pos_complexPadic : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  apply inv_pos.mpr
  exact_mod_cast (Fact.out : Nat.Prime l).pos
theorem norm_prime_lt_one_complexPadic : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast (Fact.out : Nat.Prime l).one_lt
theorem kmu_discrete {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  rw [hx0, norm_zero]
  exact norm_nonneg _
  obtain ⟨m, a, -, b, -, ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]
    simp
  rw [hn] at h1 ⊢
  calc ‖(l : ℂ_[l])‖ ^ m ≤ ‖(l : ℂ_[l])‖ ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le $ by
            by_contra hc
            have hm0 : m ≤ 0 := by omega
            have := one_le_zpow_of_nonpos₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm0
            linarith
    _ = ‖(l : ℂ_[l])‖ := zpow_one _

theorem exists_teichmuller_rep_mod_prime {a : ℂ_[l]} (ha : a ∈ Rmu l) : ∃ ξ ∈ Tch l, ‖a - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨f, hf, r, hr, h⟩ := rmu_frob l a ha
  refine tch_near l a (rmu_norm_le l ha) f hf _ (norm_prime_lt_one_complexPadic l) ?_
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) $ rmu_norm_le l hr

theorem kmu_rep {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases lt_or_eq_of_le h1 with h1 | h1
  exact ⟨0, Set.mem_insert _ _, by rw [sub_zero]; exact kmu_discrete l hx h1⟩
  obtain ⟨m, a, ha', b, hb', ha, hb, rfl⟩ := kmu_shape l hx (by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1)
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]
    simp
  rw [hn] at h1
  have hm : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    have := one_lt_zpow_of_neg₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
    linarith
    exact h
    have := zpow_lt_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
    linarith
  subst hm
  obtain ⟨α, hα, hαa⟩ := exists_teichmuller_rep_mod_prime l ha'
  obtain ⟨β, hβ, hβb⟩ := exists_teichmuller_rep_mod_prime l hb'
  have hβ1 : ‖β‖ = 1 := by
    rw [← norm_eq_of_norm_sub_lt_max l $ lt_of_le_of_lt hβb $ lt_of_lt_of_le (norm_prime_lt_one_complexPadic l) $ hb ▸ le_max_left _ _, hb]
  have hb0 : b ≠ 0 := by intro h
                         rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hβ0 : β ≠ 0 := by intro h
                         rw [h, norm_zero] at hβ1; exact zero_ne_one hβ1
  use α * β⁻¹, tch_mul l hα $ tch_inv l hβ
  have he : (l : ℂ_[l]) ^ (0 : ℤ) * (a / b) - α * β⁻¹
      = ((a - α) * β - α * (b - β)) / (b * β) := by
    field_simp
    ring
  rw [he, norm_div, norm_mul b, hb, hβ1, mul_one, div_one]
  refine (norm_sub_le_max_padic l _ _).trans $ max_le ?_ ?_
  rw [norm_mul, hβ1, mul_one]
  exact hαa
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) $ tch_norm_le l hα).trans hβb

theorem kur_approx {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (e : ℝ) (he : 0 < e) :
    ∃ y ∈ Kmu l, ‖x - y‖ < e := by
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hx e he
  exact ⟨y, hy, by rwa [dist_eq_norm] at hd⟩

theorem kur_discrete {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  rw [norm_zero]
  exact norm_nonneg _
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖x‖ (norm_pos_iff.mpr hx0)
  rw [norm_eq_of_norm_sub_lt_max l $ lt_of_lt_of_le hxy $ le_max_left _ _] at h1 ⊢
  exact kmu_discrete l hy h1

theorem kur_rep {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖(l : ℂ_[l])‖ (norm_prime_pos_complexPadic l)
  have hl1 := norm_prime_lt_one_complexPadic l
  have hy1 : ‖y‖ ≤ 1 := by
    have h := norm_sub_le_max_padic l x $ x - y
    rw [sub_sub_cancel] at h
    exact h.trans $ max_le h1 $ by linarith
  obtain ⟨ξ, hξ, hyξ⟩ := kmu_rep l hy hy1
  use ξ, hξ
  have h := norm_sub_le_max_padic l (x - y) $ ξ - y
  rw [sub_sub_sub_cancel_right, norm_sub_rev ξ y] at h
  exact h.trans $ max_le hxy.le hyξ

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem norm_prime_lt_one_padicField : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_l_Cl]
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast (Fact.out : l.Prime).one_lt
theorem norm_prime_pos_padicField : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_l_Cl]
  apply inv_pos.mpr
  exact_mod_cast (Fact.out : l.Prime).pos
theorem frobeniusLift_near_pow (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨r, hr, h⟩ := rmu_sigma_congr l s hs x
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) $ rmu_norm_le l hr

theorem frobeniusLift_norm_one (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l)
    (hx : ‖(x : ℂ_[l])‖ = 1) : ‖((s x : Rmu l) : ℂ_[l])‖ = 1 := by
  have h1 : ‖(x : ℂ_[l]) ^ l‖ = 1 := by rw [norm_pow, hx, one_pow]
  have h2 : ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ < ‖(x : ℂ_[l]) ^ l‖ := by
    rw [h1]
    exact lt_of_le_of_lt (frobeniusLift_near_pow l s hs x) $ norm_prime_lt_one_padicField l
  have h3 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm $ ne_of_lt h2
  rwa [sub_add_cancel, max_eq_right h2.le, h1] at h3

theorem unitBall_eq_frac_normOne {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖b‖ = 1 ∧ x * b = a := by
  by_cases hx0 : x = 0
  exact ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, norm_one, by simp [hx0]⟩
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l hx hx0
  have hb0 : b ≠ 0 := by intro h0
                         rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖x‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]
    simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd h1 $ not_le.mpr this
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  use (l : ℂ_[l]) ^ k * a, (Rmu l).mul_mem ((Rmu l).pow_mem (natCast_mem _ l) k) ha, b, hb, hnb
  rw [h, zpow_natCast]
  field_simp

theorem rmu_sigma_norm (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l])‖ = ‖(x : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  simp [hx0]
  have hx0' : (x : ℂ_[l]) ≠ 0 := fun h => hx0 $ Subtype.ext h
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l (rmu_le_kmu l x.2) hx0'
  have hb0 : b ≠ 0 := by intro h0
                         rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖(x : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]
    simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd (rmu_norm_le l x.2) $ not_le.mpr this
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  have he : x * (⟨b, hb⟩ : Rmu l) = (l : Rmu l) ^ k * (⟨a, ha⟩ : Rmu l) := by
    apply Subtype.ext
    push_cast
    rw [h, zpow_natCast]
    field_simp
  have hs' := congrArg (fun z : Rmu l => ‖(z : ℂ_[l])‖) $ congrArg s he
  simp only [map_mul, map_pow, map_natCast] at hs'
  push_cast at hs'
  rw [norm_mul, norm_mul, norm_pow, frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb,
    frobeniusLift_norm_one l s hs ⟨a, ha⟩ hna, mul_one, mul_one] at hs'
  rw [hs', hn, zpow_natCast]

section Generic

variable {K : Type*} [Field K] (R : Subring K) (F : Subfield K) (h : R ≤ F.toSubring)

def subringInclusionSubfield : R →+* F := Subring.inclusion h

theorem subringInclusionSubfield_coe (x : R) : ((subringInclusionSubfield R F h x : F) : K) = (x : K) := rfl

theorem subringInclusionSubfield_injective : Function.Injective $ subringInclusionSubfield R F h := fun x y e =>
  Subtype.ext (by rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, e])

theorem isFractionRing_subringInclusion (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b) :
    @IsFractionRing R _ F _ (subringInclusionSubfield R F h).toAlgebra := by
  let _ := (subringInclusionSubfield R F h).toAlgebra
  have : FaithfulSMul R F :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr $ subringInclusionSubfield_injective R F h
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, ha, b, hb, -, e⟩ := hf z z.2
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext ?_⟩
  rw [Subfield.coe_div, e]
  rfl

theorem exists_extend_endomorphism_fractions (h : R ≤ F.toSubring) (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b)
    (s : R →+* R) (hsinj : Function.Injective s) :
    ∃ σ : F →+* F, ∀ (x : F) (a b : R), (x : K) * b = a →
      ((σ x : F) : K) * (s b : R) = (s a : R) := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : IsFractionRing R F := isFractionRing_subringInclusion R F h hf
  have hg : Function.Injective $ (subringInclusionSubfield R F h).comp s := (subringInclusionSubfield_injective R F h).comp hsinj
  have hσ : ∀ x, IsFractionRing.lift hg (subringInclusionSubfield R F h x) = subringInclusionSubfield R F h (s x) :=
    fun x => IsFractionRing.lift_algebraMap hg x
  refine ⟨IsFractionRing.lift hg, fun x a b e => ?_⟩
  have h' : x * subringInclusionSubfield R F h b = subringInclusionSubfield R F h a :=
    Subtype.ext (by rw [Subfield.coe_mul, subringInclusionSubfield_coe, subringInclusionSubfield_coe, e])
  have h2 := congrArg (IsFractionRing.lift hg) h'
  rw [map_mul, hσ, hσ] at h2
  rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, ← Subfield.coe_mul, h2]

end Generic

theorem frobeniusLift_injective (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) : Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := rmu_sigma_norm l s hs x
  rw [hx, Subring.coe_zero, norm_zero] at this
  exact Subtype.ext (norm_eq_zero.mp this.symm)

theorem norm_unramifiedField_coe (x : Kmu l) : ‖x‖ = ‖(x : ℂ_[l])‖ := rfl

theorem kmu_sigma : ∃ s : Kmu l →+* Kmu l, (∀ x : Kmu l, ‖s x‖ = ‖x‖) ∧
    ∀ x : Kmu l, ‖x‖ ≤ 1 → ‖s x - x ^ l‖ ≤ ‖(l : Kmu l)‖ := by
  obtain ⟨s, hs⟩ := rmu_sigma l
  obtain ⟨σ, key⟩ := exists_extend_endomorphism_fractions (Rmu l) (Kmu l) (fun _ hx => rmu_le_kmu l hx)
    (fun _ hx => kmu_frac l hx) s $ frobeniusLift_injective l s hs
  refine ⟨σ, ?_, ?_⟩
  intro x
  obtain ⟨a, ha, b, hb, hb0, h⟩ := kmu_frac l x.2
  have h1 : (x : ℂ_[l]) * b = a := by rw [h]
                                      field_simp
  have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
  have h3 := congrArg norm h2
  have h4 := congrArg norm h1
  rw [norm_mul, rmu_sigma_norm l s hs, rmu_sigma_norm l s hs] at h3
  rw [norm_mul] at h4
  rw [norm_unramifiedField_coe, norm_unramifiedField_coe]
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hb0) $ h3.trans h4.symm
  intro x hx
  rw [norm_unramifiedField_coe] at hx
  obtain ⟨a, ha, b, hb, hnb, h1⟩ := unitBall_eq_frac_normOne l x.2 hx
  have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
  have hsb := frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb
  have hna := frobeniusLift_near_pow l s hs ⟨a, ha⟩
  have hnb' := frobeniusLift_near_pow l s hs ⟨b, hb⟩
  rw [norm_unramifiedField_coe, norm_unramifiedField_coe, Subfield.coe_sub, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
  generalize ((s ⟨a, ha⟩ : Rmu l) : ℂ_[l]) = sa at h2 hna
  generalize ((s ⟨b, hb⟩ : Rmu l) : ℂ_[l]) = sb at h2 hnb' hsb
  generalize ((σ x : Kmu l) : ℂ_[l]) = y at h2 ⊢
  simp only at hna hnb'
  have e : (y - (x : ℂ_[l]) ^ l) * sb = (sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l)) := by
    rw [← h1, ← h2]
    ring
  trans ‖(sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l))‖
  rw [← e, norm_mul, hsb, mul_one]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le hna ?_
  rw [norm_neg, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx)).trans hnb'

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

def kmuIncl : Kmu l →+* MaximalUnramifiedExtension l := Subfield.inclusion $ Subfield.le_topologicalClosure $ Kmu l

theorem kmuIncl_norm (x : Kmu l) : ‖kmuIncl l x‖ = ‖x‖ := rfl

theorem kmuIncl_isometry : Isometry $ kmuIncl l :=
  AddMonoidHomClass.isometry_of_norm (kmuIncl l) $ kmuIncl_norm l

theorem kmuIncl_denseRange : DenseRange $ kmuIncl l := by
  intro x
  rw [Metric.mem_closure_iff]
  intro e he
  obtain ⟨y, hy, hxy⟩ := kur_approx l x.2 e he
  exact ⟨kmuIncl l ⟨y, hy⟩, ⟨_, rfl⟩, by rw [dist_eq_norm]; exact hxy⟩

theorem kurFrob : ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ := by
  obtain ⟨s, hs1, hs2⟩ := kmu_sigma l
  have : CompleteSpace $ MaximalUnramifiedExtension l := kur_complete l
  have hiso := AddMonoidHomClass.isometry_of_norm _ fun x => by
      rw [RingHom.comp_apply, kmuIncl_norm, hs1]
  let σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l :=
    IsDenseInducing.extendRingHom (i := kmuIncl l) (f := (kmuIncl l).comp s)
      (kmuIncl_isometry l).isUniformInducing (kmuIncl_denseRange l) hiso.uniformContinuous
  have hσc : Continuous σ :=
    (uniformContinuous_uniformly_extend (kmuIncl_isometry l).isUniformInducing
      (kmuIncl_denseRange l) hiso.uniformContinuous).continuous
  have hσi : ∀ x : Kmu l, σ (kmuIncl l x) = kmuIncl l (s x) := fun x =>
    ((kmuIncl_isometry l).isUniformInducing.isDenseInducing $ kmuIncl_denseRange l).extend_eq hiso.continuous x
  have hl : ‖(l : MaximalUnramifiedExtension l)‖ = ‖(l : ℂ_[l])‖ := rfl
  refine ⟨σ, Fact.out, ?_, ?_, ?_, ?_⟩
  rw [hl, norm_l_Cl]
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast (Fact.out : l.Prime).one_lt
  intro x
  refine (kmuIncl_denseRange l).induction_on (p := fun x => ‖σ x‖ = ‖x‖) x
    (isClosed_eq hσc.norm continuous_norm) fun y => ?_
  rw [hσi, kmuIncl_norm, kmuIncl_norm, hs1]
  intro x hx
  have hmem : x ∈ closure (Metric.closedBall (0 : MaximalUnramifiedExtension l) 1 ∩ Set.range (kmuIncl l)) :=
    (kmuIncl_denseRange l).open_subset_closure_inter (IsUltrametricDist.isOpen_closedBall _ one_ne_zero) $ by simpa using hx
  refine closure_minimal ?_ (isClosed_le (hσc.sub $ continuous_pow l).norm continuous_const) hmem
  rintro _ ⟨hy1, y, rfl⟩
  have := hs2 y $ by
      rwa [mem_closedBall_zero_iff, kmuIncl_norm] at hy1
  show ‖σ (kmuIncl l y) - (kmuIncl l y) ^ l‖ ≤ ‖(l : MaximalUnramifiedExtension l)‖
  rwa [hσi, ← map_pow, ← map_sub, kmuIncl_norm]
  intro x hx
  exact kur_discrete l x.2 hx

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1.KE

open Formalism.L2.Th1.CM

theorem norm_le_one_of_integral {K R : Type*} [NormedField K] [IsUltrametricDist K] [CommRing R]
    [Algebra R K] (hR : ∀ r : R, ‖algebraMap R K r‖ ≤ 1) (δ : K) (h : IsIntegral R δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨p, hp, hpe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hpe
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap R K (p.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ p.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ $ lt_trans zero_lt_one hlt]
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.mp hi
    calc ‖algebraMap R K (p.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by
          gcongr
          exact hR _
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ p.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ p.natDegree / ‖δ‖ < ‖δ‖ ^ p.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ p.natDegree‖ = ‖δ‖ ^ p.natDegree := norm_pow _ _
  rw [eq_neg_of_add_eq_zero_right hpe, norm_neg] at h4
  linarith

theorem norm_int_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] (n : ℤ) :
    ‖algebraMap ℤ K n‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_intCast_le_one K n

theorem norm_le_one_of_integral_int {K : Type*} [NormedField K] [IsUltrametricDist K] (δ : K)
    (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 :=
  norm_le_one_of_integral norm_int_le_one δ h

theorem norm_pow_sub_pow_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖x ^ i - y ^ i‖ ≤ ‖x - y‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : x ^ (i + 1) - y ^ (i + 1) = x * (x ^ i - y ^ i) + (x - y) * y ^ i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le ?_ ?_
    rw [norm_mul]
    calc ‖x‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by gcongr
      _ = _ := one_mul _
    rw [norm_mul, norm_pow]
    calc ‖x - y‖ * ‖y‖ ^ i ≤ ‖x - y‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hy
      _ = _ := mul_one _

theorem norm_eval_sub_eval_le {K : Type*} [NormedField K] [IsUltrametricDist K] (P : Polynomial K)
    (hP : ∀ i, ‖P.coeff i‖ ≤ 1) {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖P.coeff i‖ * ‖x ^ i - y ^ i‖ ≤ 1 * ‖x - y‖ := by
        gcongr
        exact hP i
        exact norm_pow_sub_pow_le hx hy i
    _ = _ := one_mul _

theorem finite_domain_frob (R : Type*) [CommRing R] [IsDomain R] [Finite R] (l : ℕ) (hl : l.Prime)
    (h0 : (l : R) = 0) : ∃ f, 0 < f ∧ ∀ x : R, x ^ (l ^ f) = x := by
  classical
  have hch := (CharP.charP_iff_prime_eq_zero hl).mpr h0
  let _ := Fintype.ofFinite R
  let _ := Fintype.fieldOfDomain R
  obtain ⟨n, -, hq⟩ := FiniteField.card R l
  exact ⟨n, n.pos, fun x => hq ▸ FiniteField.pow_card x⟩

theorem frob_fix_of_integral {K : Type*} [NormedField K] [IsUltrametricDist K] (l : ℕ)
    (hlp : l.Prime) (hl : ‖(l : K)‖ < 1) (δ : K) (hδ : IsIntegral ℤ δ) :
    ∃ f : ℕ, 0 < f ∧ ‖δ ^ (l ^ f) - δ‖ < 1 := by
  let A : Subalgebra ℤ K := Algebra.adjoin ℤ {δ}
  have hA : ∀ x : A, ‖(x : K)‖ ≤ 1 := fun x =>
    norm_le_one_of_integral norm_int_le_one _ $ adjoin_le_integralClosure hδ x.2
  let I : Ideal A :=
    { carrier := {x | ‖(x : K)‖ < 1}
      add_mem' := fun {a b} ha hb =>
        lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) $ max_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ‖((c * x : A) : K)‖ < 1
        rw [MulMemClass.coe_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hA c) (norm_nonneg _) hx }
  have hImem : ∀ x, x ∈ I ↔ ‖(x : K)‖ < 1 := fun x => Iff.rfl
  have hIprime : I.IsPrime := by
    constructor
    intro h
    have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
    rw [hImem] at h1
    simp at h1
    intro x y hxy
    by_contra hcon
    rw [not_or, hImem, hImem, not_lt, not_lt] at hcon
    rw [hImem, MulMemClass.coe_mul, norm_mul] at hxy
    have := one_le_mul_of_one_le_of_one_le hcon.1 hcon.2
    linarith
  have : Module.Finite ℤ A := Algebra.finite_adjoin_simple_of_isIntegral hδ
  have hl0 : ((l : ℕ) : A ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I) l, Ideal.Quotient.eq_zero_iff_mem, hImem]
    have h2 : (((l : ℕ) : A) : K) = (l : K) := map_natCast A.val l
    rwa [h2]
  have htors : Module.IsTorsion ℤ $ A ⧸ I := fun {x} =>
    ⟨⟨(l : ℤ), mem_nonZeroDivisors_of_ne_zero $ by exact_mod_cast hlp.ne_zero⟩, by
      change (l : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hl0, zero_mul]⟩
  have : Finite $ A ⧸ I := Module.finite_of_fg_torsion _ htors
  obtain ⟨f, hf, h⟩ := finite_domain_frob (A ⧸ I) l hlp hl0
  use f, hf
  let d : A := ⟨δ, Algebra.self_mem_adjoin_singleton ℤ δ⟩
  have h3 := h $ Ideal.Quotient.mk I d
  rwa [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hImem] at h3

variable (l : ℕ) [Fact l.Prime]

theorem rmu_isIntegral_int {x : ℂ_[l]} (hx : x ∈ Rmu l) : IsIntegral ℤ x := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨n, hn, -, h⟩ := hx
    exact IsIntegral.of_pow hn $ h ▸ isIntegral_one
  | zero => exact isIntegral_zero
  | one => exact isIntegral_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | mul x y _ _ hx hy => exact hx.mul hy

theorem isIntegral_int_of_rmu (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) :
    (Int.castRingHom ℂ_[l]).IsIntegralElem δ := by
  have : Algebra.IsIntegral ℤ $ Rmu l := ⟨fun x => by
    have := rmu_isIntegral_int l x.2
    exact (isIntegral_algebraMap_iff (A := Rmu l) (B := ℂ_[l])).mp this⟩
  exact (Subsingleton.elim (algebraMap ℤ ℂ_[l]) $ Int.castRingHom ℂ_[l]) ▸ (isIntegral_trans δ hδ)

theorem tch_mem_rmu {x : ℂ_[l]} (hx : x ∈ Tch l) : x ∈ Rmu l := by
  rcases hx with rfl | hx
  exact (Rmu l).zero_mem
  exact Subring.subset_closure hx

end ReciprocityTheory.ChartRestriction.L1.KE
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem kq_norm_l_lt : ‖(l : ℂ_[l])‖ < 1 := by
  have e : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [e, norm_algebraMap']
  first
  | exact Padic.norm_p_lt_one
  | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ $ by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem kq_add_le (x y : ℂ_[l]) (r : ℝ) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r := (IsUltrametricDist.norm_add_le_max x y).trans $ max_le hx hy

theorem kq_add_lt (x y : ℂ_[l]) (r : ℝ) (hx : ‖x‖ < r) (hy : ‖y‖ < r) : ‖x + y‖ < r := (IsUltrametricDist.norm_add_le_max x y).trans_lt $ max_lt hx hy

private theorem kq_intnorm_lemma (n : ℤ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← map_intCast $ algebraMap ℚ_[l] ℂ_[l], norm_algebraMap']

theorem kq_int_le (n : ℤ) : ‖(n : ℂ_[l])‖ ≤ 1 := by
  rw [kq_intnorm_lemma]
  first
  | exact padicNormE.norm_int_le_one n
  | exact Padic.norm_int_le_one n

theorem kq_int_dvd (n : ℤ) (h : (l : ℤ) ∣ n) : ‖(n : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨m, rfl⟩ := h
  push_cast
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) $ kq_int_le l m

theorem kq_int_unit (n : ℤ) (h : ¬ (l : ℤ) ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by
  refine le_antisymm (kq_int_le l n) ?_
  have hp := Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)
  obtain ⟨a, b, hab⟩ := by
      first
      | exact (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr h
      | exact (Prime.coprime_iff_not_dvd hp).mpr h
  have e : (a : ℂ_[l]) * (l : ℂ_[l]) + (b : ℂ_[l]) * (n : ℂ_[l]) = 1 := by exact_mod_cast hab
  have h1 := IsUltrametricDist.norm_add_le_max ((a : ℂ_[l]) * (l : ℂ_[l])) $ (b : ℂ_[l]) * (n : ℂ_[l])
  rw [e, norm_one, norm_mul, norm_mul] at h1
  rcases le_max_iff.mp h1 with h2 | h2
  exact absurd (h2.trans $ mul_le_of_le_one_left (norm_nonneg _) $ kq_int_le l a)
    $ not_le.mpr $ kq_norm_l_lt l
  exact h2.trans $ mul_le_of_le_one_left (norm_nonneg _) $ kq_int_le l b

theorem kq_zmod (n : ℤ) (h : (n : ZMod l) = 0) : ‖(n : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := kq_int_dvd l n $ (ZMod.intCast_zmod_eq_zero_iff_dvd n l).mp h

theorem kq_euler (d : ℕ) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a, a ^ 2 = -(d : ZMod l)) : (-(d : ZMod l)) ^ (l / 2) = -1 := by
  have hd0 : (-(d : ZMod l)) ≠ 0 := by
    rw [neg_ne_zero]
    intro h0
    apply hld
    exact (CharP.cast_eq_zero_iff (ZMod l) l d).mp h0
  rcases ZMod.pow_div_two_eq_neg_one_or_one l hd0 with h | h
  all_goals first
    | exact h
    | (exfalso
       obtain ⟨a, ha⟩ := (ZMod.euler_criterion l hd0).mpr h
       exact hin ⟨a, by rw [ha, sq]⟩)

variable {l}

theorem kq_pow_odd (δ c : ℂ_[l]) (hδ : δ ^ 2 = c) (n m : ℕ) (h : n = 2 * m + 1) :
    δ ^ n = δ * c ^ m := by
  rw [h, pow_succ, pow_mul, hδ, mul_comm]

theorem kq_pow_l (d : ℕ) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a, a ^ 2 = -(d : ZMod l)) (δ : ℂ_[l]) (hδ : δ ^ 2 = -(d : ℂ_[l]))
    (hn : ‖δ‖ = 1) : ‖δ ^ l + δ‖ ≤ ‖(l : ℂ_[l])‖ := by
  have hodd : l = 2 * (l / 2) + 1 := by
    have h2 := (Fact.out : l.Prime).mod_two_eq_one_iff_ne_two.mpr hl
    have h3 := Nat.div_add_mod l 2
    omega
  rw [kq_pow_odd δ _ hδ l (l / 2) hodd]
  have e : δ * (-(d : ℂ_[l])) ^ (l / 2) + δ = δ * ((((-(d : ℤ)) ^ (l / 2) + 1 : ℤ)) : ℂ_[l]) := by
    push_cast
    ring
  rw [e, norm_mul, hn, one_mul]
  apply kq_zmod
  push_cast
  rw [kq_euler l d hld hin]
  ring

theorem norm_sqrtNeg_pow_prime_sq_sub (d : ℕ) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a, a ^ 2 = -(d : ZMod l)) (δ : ℂ_[l]) (hδ : δ ^ 2 = -(d : ℂ_[l]))
    (hn : ‖δ‖ = 1) : ‖δ ^ (l ^ 2) - δ‖ ≤ ‖(l : ℂ_[l])‖ := by
  have hodd : l = 2 * (l / 2) + 1 := by
    have := (Fact.out : l.Prime).eq_two_or_odd
    omega
  have e0 : δ ^ l = δ * (((-(d : ℤ)) ^ (l / 2) : ℤ) : ℂ_[l]) := by
    rw [kq_pow_odd δ _ hδ l (l / 2) hodd]
    push_cast
    ring
  have e : δ ^ (l ^ 2) - δ = δ * ((((-(d : ℤ)) ^ (l / 2)) ^ (l + 1) - 1 : ℤ) : ℂ_[l]) := by
    rw [sq, pow_mul, e0, mul_pow, e0]
    push_cast
    ring
  rw [e, norm_mul, hn, one_mul]
  apply kq_zmod
  push_cast
  rw [kq_euler l d hld hin]
  have : l + 1 = 2 * (l / 2 + 1) := by omega
  rw [this, pow_mul]
  simp

theorem kq_mem (d : ℕ) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a, a ^ 2 = -(d : ZMod l)) (δ : ℂ_[l]) (hδ : δ ^ 2 = -(d : ℂ_[l]))
    (hn : ‖δ‖ = 1) : δ ∈ MaximalUnramifiedExtension l := by
  obtain ⟨ξ, hξ, hξδ⟩ := tch_near l δ hn.le 2 (by norm_num) ‖(l : ℂ_[l])‖ (kq_norm_l_lt l)
    $ norm_sqrtNeg_pow_prime_sq_sub d hl hld hin δ hδ hn
  have hlt := hξδ.trans_lt $ kq_norm_l_lt l
  have hξ1 : ‖ξ‖ = 1 := by
    refine le_antisymm (tch_norm_le l hξ) $ not_lt.mp fun h => ?_
    have : ‖(δ - ξ) + ξ‖ < 1 := kq_add_lt l _ _ 1 hlt h
    rw [sub_add_cancel, hn] at this
    exact lt_irrefl _ this
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := kq_int_unit l 2 $ by
      intro h
      have h' : l ∣ 2 := by exact_mod_cast h
      exact hl $ (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'
    simpa using this
  have : CompleteSpace $ MaximalUnramifiedExtension l := kur_complete l
  let x₀ : MaximalUnramifiedExtension l := ⟨ξ, tch_mem_kur l hξ⟩
  let P := Polynomial.X ^ 2 + Polynomial.C (d : MaximalUnramifiedExtension l)
  have hev : ((P.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l]) = (ξ - δ) * (ξ + δ) := by
    have : (ξ - δ) * (ξ + δ) = ξ ^ 2 - δ ^ 2 := by ring
    rw [this, hδ]
    simp [P, x₀]
  have hdv : ((P.derivative.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l]) = 2 * ξ := by
    simp [P, x₀]
    left
    norm_num
  have hd1 : ‖(d : ℂ_[l])‖ ≤ 1 := by simpa using kq_int_le l (d : ℤ)
  obtain ⟨x, hx, -⟩ := newton_root P
    (by
      intro i
      change ‖((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ 1
      simp [P, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      by_cases h2i : i = 2
      subst h2i
      simp
      by_cases h0 : i = 0
      subst h0
      simpa using hd1
      simp [h2i, h0])
    x₀ hξ1.le
    (by
      change ‖((P.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1
      rw [hev, norm_mul, norm_sub_rev]
      have : ‖ξ + δ‖ ≤ 1 := kq_add_le l _ _ 1 hξ1.le hn.le
      exact (mul_le_of_le_one_right (norm_nonneg _) this).trans_lt hlt)
    (by
      change ‖((P.derivative.eval x₀ : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1
      rw [hdv, norm_mul, h2, hξ1, one_mul])
  have hx' : (x : ℂ_[l]) ^ 2 = δ ^ 2 := by
    have : ((P.eval x : MaximalUnramifiedExtension l) : ℂ_[l]) = 0 := by rw [hx]
                                                                         rfl
    simp [P, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at this
    push_cast at this
    rw [hδ]
    linear_combination this
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx' with h | h
  rw [← h]
  exact x.2
  have : δ = -(x : ℂ_[l]) := by rw [h, neg_neg]
  rw [this]
  exact neg_mem x.2

variable (l)

theorem kur_quad (d : ℕ) (hd : d % 4 = 3) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (a : ℂ_[l])
    (ha : a ^ 2 - a + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0) :
    ‖a‖ ≤ 1 ∧ ‖1 - 2 * a‖ = 1 ∧ ∃ ha' : a ∈ MaximalUnramifiedExtension l, ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ →
      σ ⟨a, ha'⟩ = 1 - ⟨a, ha'⟩ := by
  have h4 : (((d + 1) / 4 : ℕ) : ℂ_[l]) * 4 = (d : ℂ_[l]) + 1 := by
    have h44 : (d + 1) / 4 * 4 = d + 1 := by omega
    exact_mod_cast h44
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℂ_[l], δ = 1 - 2 * a := ⟨_, rfl⟩
  have hδ : δ ^ 2 = -(d : ℂ_[l]) := by
    rw [hδdef]
    linear_combination 4 * ha - h4
  have hd1 : ‖(d : ℂ_[l])‖ = 1 := by
    have hu := kq_int_unit l (d : ℤ) $ by exact_mod_cast hld
    exact_mod_cast hu
  have hn : ‖δ‖ = 1 := by
    have hh := congrArg norm hδ
    rw [norm_pow, norm_neg, hd1] at hh
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hh
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hu := kq_int_unit l 2 $ by
      intro h2d
      have h2n : l ∣ 2 := by exact_mod_cast h2d
      exact hl $ (Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h2n
    exact_mod_cast hu
  have ha2 : a * 2 = 1 - δ := by
    rw [hδdef]
    ring
  have hna : ‖a‖ ≤ 1 := by
    have hh : ‖a‖ = ‖1 - δ‖ := by rw [← ha2, norm_mul, h2, mul_one]
    rw [hh, sub_eq_add_neg]
    apply kq_add_le l _ _ 1 $ by simp
    rw [norm_neg, hn]
  have hδK : δ ∈ MaximalUnramifiedExtension l := kq_mem d hl hld hin δ hδ hn
  have h20 : (2 : ℂ_[l]) ≠ 0 := two_ne_zero
  have haK : a ∈ MaximalUnramifiedExtension l := by
    have hh : a = (1 - δ) / 2 := by rw [eq_div_iff h20, ha2]
    rw [hh]
    exact div_mem (sub_mem (one_mem _) hδK) $ by simpa using natCast_mem (MaximalUnramifiedExtension l) 2
  refine ⟨hna, by rw [← hδdef]; exact hn, haK, fun σ hσ => ?_⟩
  obtain ⟨-, -, -, f4⟩ := hσ
  obtain ⟨D, hD⟩ : ∃ D : MaximalUnramifiedExtension l, (D : ℂ_[l]) = δ := ⟨⟨δ, hδK⟩, rfl⟩
  have hD2 : D ^ 2 = -((d : ℕ) : MaximalUnramifiedExtension l) := Subtype.ext (by simp [hD, hδ])
  have hσD : σ D ^ 2 = D ^ 2 := by rw [← map_pow, hD2, map_neg, map_natCast]
  have hneg : σ D = -D := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hσD with h | h
    exfalso
    have hf' : ‖δ - δ ^ l‖ ≤ ‖(l : ℂ_[l])‖ := by
      have h5 := f4 D $ le_of_eq $ by
          rw [← hn, ← hD]
          rfl
      rw [h] at h5
      rwa [← hD]
    have hsum : (2 : ℂ_[l]) * δ = (δ - δ ^ l) + (δ ^ l + δ) := by ring
    have h2d : ‖(2 : ℂ_[l]) * δ‖ = 1 := by rw [norm_mul, h2, hn, one_mul]
    have hlt := kq_add_lt l _ _ 1 (hf'.trans_lt $ kq_norm_l_lt l)
      $ (kq_pow_l d hl hld hin δ hδ hn).trans_lt $ kq_norm_l_lt l
    rw [← hsum, h2d] at hlt
    exact lt_irrefl 1 hlt
    exact h
  have e2 : ((2 : MaximalUnramifiedExtension l) : ℂ_[l]) = 2 := by
    first
    | rfl
    | norm_cast
    | simp
  have hA2 : (⟨a, haK⟩ : MaximalUnramifiedExtension l) * 2 = 1 - D := by
    apply Subtype.ext
    show a * ((2 : MaximalUnramifiedExtension l) : ℂ_[l]) = ((1 - D : MaximalUnramifiedExtension l) : ℂ_[l])
    rw [e2, ha2, ← hD]
    rfl
  have h2ne : (2 : MaximalUnramifiedExtension l) ≠ 0 := fun h0 => h20 (by rw [← e2, h0]; rfl)
  apply mul_right_cancel₀ h2ne
  trans 1 + D
  have h6 := congrArg σ hA2
  rw [map_mul, map_ofNat, map_sub, map_one, hneg] at h6
  rw [h6]
  ring
  rw [sub_mul, hA2]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
section
open IsUltrametricDist (norm_add_le_max)
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

omit [CompleteSpace K] [CharZero K] in
theorem semilin_norm_add_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

omit [CompleteSpace K] [CharZero K] in
theorem semilin_norm_sub_le {a b : K} {t : ℝ} (ha : ‖a‖ ≤ t) (hb : ‖b‖ ≤ t) : ‖a - b‖ ≤ t := by
  rw [sub_eq_add_neg]
  exact (norm_add_le_max _ _).trans $ max_le ha $ by rwa [norm_neg]

omit [CompleteSpace K] [CharZero K] in

theorem semilin_norm_pow_sub_pow {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [e]
    refine (norm_add_le_max _ _).trans $ max_le ?_ ?_
    rw [norm_mul]
    calc ‖a‖ * ‖a ^ n - b ^ n‖ ≤ 1 * ‖a - b‖ := mul_le_mul ha ih (norm_nonneg _) zero_le_one
      _ = ‖a - b‖ := one_mul _
    rw [norm_mul, norm_pow]
    calc ‖a - b‖ * ‖b‖ ^ n ≤ ‖a - b‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) $ norm_nonneg _
      _ = ‖a - b‖ := mul_one _

omit [CompleteSpace K] [CharZero K] in

theorem FrobField.norm_sq_sub_pow_le {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (x : K) (hx : ‖x‖ ≤ 1) :
    ‖σ (σ x) - x ^ (l ^ 2)‖ ≤ ‖(l : K)‖ := by
  have hp : x ^ (l ^ 2) = (x ^ l) ^ l := by rw [← pow_mul, sq]
  have e : σ (σ x) - x ^ (l ^ 2) = σ (σ x - x ^ l) + ((σ x) ^ l - (x ^ l) ^ l) := by
    rw [hp, map_sub, map_pow]
    ring
  have h1 := h.frob x hx
  rw [e]
  refine (norm_add_le_max _ _).trans $ max_le ?_ ?_
  rwa [h.isom]
  refine (semilin_norm_pow_sub_pow (by rw [h.isom]; exact hx) ?_ l).trans h1
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hx

omit [CompleteSpace K] [CharZero K] in
open Polynomial in

theorem semilin_root {l : ℕ} (hR : ResClosed K l) {m : ℕ} (hm : 2 ≤ m) (a b : K) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) : ∃ x, ‖x‖ ≤ 1 ∧ ‖x ^ m + a * x + b‖ ≤ ‖(l : K)‖ := by
  have hdeg : (C a * X + C b : K[X]).degree < (X ^ m : K[X]).degree := by
    rw [degree_X_pow]
    apply lt_of_le_of_lt degree_linear_le
    exact_mod_cast hm
  have hnat : (X ^ m + (C a * X + C b) : K[X]).natDegree = m := by
    rw [natDegree_add_eq_left_of_degree_lt hdeg, natDegree_X_pow]
  obtain ⟨x, hx, hev⟩ := hR _ (monic_X_pow_add $ by rwa [degree_X_pow] at hdeg) (by omega) (by
      intro i
      simp only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
      refine (norm_add_le_max _ _).trans (max_le ?_
        $ (norm_add_le_max _ _).trans $ max_le ?_ ?_) <;> split_ifs <;> simp [ha, hb])
  use x, hx
  simpa [add_assoc] using hev

open Filter Topology in

theorem lang_semilinear {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (hR : ResClosed K l)
    (c : K) (hc : ‖c‖ = 1) : ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * σ (σ ε) := by
  have hl2 := h.prime.two_le
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ $ norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr h.prime.ne_zero
  have hl1 := h.norm_l
  have hq4 : 4 ≤ l ^ 2 := by nlinarith

  let P : ℕ → K → Prop := fun n ε => ‖ε‖ = 1 ∧ ‖ε - c * σ (σ ε)‖ ≤ ‖(l : K)‖ ^ (n + 1)
  have h0 : ∃ ε, P 0 ε := by
    obtain ⟨x, hx, hev⟩ := semilin_root hR (m := l ^ 2 - 1) (by omega) 0 (-c⁻¹) (by simp)
      $ by rw [norm_neg, hci]
    rw [zero_mul, add_zero, ← sub_eq_add_neg] at hev
    have hx1 : ‖x‖ = 1 := by
      have h1 : ‖x ^ (l ^ 2 - 1)‖ = 1 := by
        have e : x ^ (l ^ 2 - 1) = c⁻¹ + (x ^ (l ^ 2 - 1) - c⁻¹) := by ring
        rw [e, semilin_norm_add_of_lt (by rw [hci]; exact hev.trans_lt hl1), hci]
      rw [norm_pow] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) $ by omega).mp h1
    use x, hx1
    have hxq : x ^ (l ^ 2) = x * x ^ (l ^ 2 - 1) := by
      rw [← pow_succ']
      congr 1; omega
    have e : x - c * σ (σ x) = -(c * x) * (x ^ (l ^ 2 - 1) - c⁻¹) - c * (σ (σ x) - x ^ (l ^ 2)) := by
      rw [hxq]
      linear_combination (-x) * hcc
    rw [e, zero_add, pow_one]
    refine semilin_norm_sub_le ?_ ?_
    rwa [norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]
    rw [norm_mul, hc, one_mul]
    exact h.norm_sq_sub_pow_le x hx
  have hstep : ∀ n ε, P n ε → ∃ ε', P (n + 1) ε' ∧ ‖ε' - ε‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
    rintro n ε ⟨hε1, hε2⟩
    have hlam0 : (l : K) ^ (n + 1) ≠ 0 := pow_ne_zero _ hl0
    have hnl : ‖(l : K) ^ (n + 1)‖ = ‖(l : K)‖ ^ (n + 1) := norm_pow _ _
    have hsm : ‖(l : K)‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hl1 $ Nat.succ_ne_zero n
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ε - c * σ (σ ε) = (l : K) ^ (n + 1) * ρ :=
      ⟨(ε - c * σ (σ ε)) / (l : K) ^ (n + 1), by field_simp⟩
    have hρ1 : ‖ρ‖ ≤ 1 := by
      have hpos : 0 < ‖(l : K)‖ ^ (n + 1) := by rw [← hnl]
                                                exact norm_pos_iff.mpr hlam0
      rw [hρ, norm_mul, hnl] at hε2
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    obtain ⟨δ, hδ, hev⟩ := semilin_root hR (m := l ^ 2) (by omega) (-c⁻¹) (-(c⁻¹ * ρ))
      (by rw [norm_neg, hci]) (by rw [norm_neg, norm_mul, hci, one_mul]; exact hρ1)
    have hσl : σ (σ $ (l : K) ^ (n + 1)) = (l : K) ^ (n + 1) := by simp [map_pow, map_natCast]
    have hlδ : ‖(l : K) ^ (n + 1) * δ‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
      rw [norm_mul, hnl]
      calc ‖(l : K)‖ ^ (n + 1) * ‖δ‖ ≤ ‖(l : K)‖ ^ (n + 1) * 1 :=
            mul_le_mul_of_nonneg_left hδ $ by positivity
        _ = _ := mul_one _
    refine ⟨ε + (l : K) ^ (n + 1) * δ, ⟨?_, ?_⟩, ?_⟩
    rw [semilin_norm_add_of_lt (by rw [hε1]; exact hlδ.trans_lt hsm), hε1]
    have e : ε + (l : K) ^ (n + 1) * δ - c * σ (σ $ ε + (l : K) ^ (n + 1) * δ) =
        (l : K) ^ (n + 1) * (-c * (δ ^ (l ^ 2) + -c⁻¹ * δ + -(c⁻¹ * ρ)) - c * (σ (σ δ) - δ ^ (l ^ 2))) := by
      rw [map_add, map_add, map_mul, map_mul, hσl]
      linear_combination hρ - ((l : K) ^ (n + 1) * ρ + (l : K) ^ (n + 1) * δ) * hcc
    rw [e, norm_mul, hnl, pow_succ ‖(l : K)‖ (n + 1)]
    refine mul_le_mul_of_nonneg_left (semilin_norm_sub_le ?_ ?_) $ by positivity
    rwa [norm_mul, norm_neg, hc, one_mul]
    rw [norm_mul, hc, one_mul]
    exact h.norm_sq_sub_pow_le δ hδ
    rw [add_sub_cancel_left]
    exact hlδ

  obtain ⟨ε0, hε0⟩ := h0
  choose g hg using hstep
  let v : (n : ℕ) → {x : K // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : K // P n x}) ⟨ε0, hε0⟩
      (fun n ih => ⟨g n ih.1 ih.2, (hg n ih.1 ih.2).1⟩) n
  let u : ℕ → K := fun n => (v n).1
  have hu : ∀ n, P n $ u n := fun n => (v n).2
  have hud : ∀ n, ‖u (n + 1) - u n‖ ≤ ‖(l : K)‖ ^ (n + 1) := fun n => (hg n (u n) $ hu n).2
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 fun n => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact hud n
  obtain ⟨ε, hlim⟩ := cauchySeq_tendsto_of_complete hcau
  have hσc : Continuous σ := ((AddMonoidHomClass.isometry_iff_norm σ).mpr h.isom).continuous
  have hres0 := squeeze_zero_norm (fun n => (hu n).2.trans $ pow_le_pow_of_le_one (norm_nonneg _) hl1.le $ Nat.le_succ n)
      $ tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1
  have hn : Tendsto (fun n => ‖u n‖) atTop $ 𝓝 ‖ε‖ := hlim.norm
  rw [funext fun n => (hu n).1] at hn
  exact ⟨ε, tendsto_nhds_unique hn tendsto_const_nhds, sub_eq_zero.mp $ tendsto_nhds_unique (hlim.sub $ (((hσc.comp hσc).tendsto ε).comp hlim).const_mul c) hres0⟩

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem FrobField.funEqSetting_sq [CompleteSpace K] (h : FrobField K l σ) :
    FunctionalEquationSetting K l (l ^ 2) $ σ.comp σ :=
  ⟨h.prime, ⟨2, two_pos, rfl⟩, h.norm_l, fun a ha => h.norm_sq_sub_pow_le a ha⟩

omit [IsUltrametricDist K] [CharZero K] in

theorem ltLog_sub_eq_X (hl : 2 ≤ l) (τ : K →+* K) :
    ltLog K l - (l : K)⁻¹ • (PowerSeries.map τ $ ltLog K l).subst ((X : PowerSeries K) ^ (l ^ 2))
      = X := by
  have hq : 2 ≤ l ^ 2 := by nlinarith
  have hq0 : l ^ 2 ≠ 0 := by omega
  have hsub : ∀ f {k} (_ : k ≠ 0) m,
      coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
    intro f k hk m
    have ha : PowerSeries.HasSubst $ (X : PowerSeries K) ^ k :=
      PowerSeries.HasSubst.of_constantCoeff_zero' $ by simp [hk]
    rw [PowerSeries.coeff_subst' ha]
    simp [← pow_mul, PowerSeries.coeff_X_pow]
    split_ifs with hd
    obtain ⟨q, rfl⟩ := hd
    rw [finsum_eq_single _ q]
    simp [Nat.mul_div_cancel_left q $ Nat.pos_of_ne_zero hk]
    intro d hd
    have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
    simp [this]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    have : m ≠ k * d := fun h => hd ⟨d, h⟩
    simp [this]
  have hpow : ∀ j, coeff ((l ^ 2) ^ j) (ltLog K l) = ((l : K) ^ j)⁻¹ := by
    intro j
    have hex : ∃ i, (l ^ 2) ^ j = (l ^ 2) ^ i := ⟨j, rfl⟩
    rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dif_pos hex]
    have hf : Nat.find hex = j := (Nat.pow_right_injective hq $ Nat.find_spec hex).symm
    rw [hf]
  ext n
  rw [map_sub, PowerSeries.coeff_smul, hsub _ hq0, PowerSeries.coeff_X]
  by_cases hn : ∃ j, n = (l ^ 2) ^ j
  obtain ⟨j, rfl⟩ := hn
  rcases j with _ | j
  have h1 : (l ^ 2) ^ 0 = 1 := pow_zero _
  have hnd : ¬ l ^ 2 ∣ (l ^ 2) ^ 0 := by
    rw [h1]
    intro h
    have := Nat.le_of_dvd one_pos h
    omega
  rw [if_neg hnd, hpow 0, h1, if_pos rfl]
  simp
  have hd : l ^ 2 ∣ (l ^ 2) ^ (j + 1) := dvd_pow_self _ $ Nat.succ_ne_zero j
  have hdiv : (l ^ 2) ^ (j + 1) / l ^ 2 = (l ^ 2) ^ j := by
    rw [pow_succ (l ^ 2) j, Nat.mul_div_cancel _ $ by omega]
  have hne : (l ^ 2) ^ (j + 1) ≠ 1 := by
    have : l ^ 2 ≤ (l ^ 2) ^ (j + 1) := Nat.le_self_pow (Nat.succ_ne_zero j) _
    omega
  rw [if_pos hd, hdiv, PowerSeries.coeff_map, hpow, hpow,
    if_neg hne, map_inv₀, map_pow, map_natCast, pow_succ (l : K) j, mul_inv]
  ring
  have h0 : coeff n (ltLog K l) = 0 := by rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dif_neg hn]
  have hX : n ≠ 1 := fun h => hn ⟨0, by rw [h, pow_zero]⟩
  rw [h0, if_neg hX]
  split_ifs with hd
  obtain ⟨m, rfl⟩ := hd
  have hm : ¬ ∃ j, m = (l ^ 2) ^ j := fun ⟨j, hj⟩ => hn ⟨j + 1, by rw [hj, pow_succ (l ^ 2) j, mul_comm]⟩
  rw [Nat.mul_div_cancel_left m $ by omega, PowerSeries.coeff_map, Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk,
    dif_neg hm, map_zero]
  simp
  simp

theorem ltLog_type (hl : 2 ≤ l) (τ : K →+* K) : IsFunEqType l (l ^ 2) τ $ ltLog K l := by
  unfold IsFunEqType
  rw [ltLog_sub_eq_X hl τ]
  exact integralPS_X

omit [IsUltrametricDist K] [CharZero K] in

theorem isFunEqType_of_mv {p q : ℕ} (hq : q ≠ 0) (τ : K →+* K) (f : PowerSeries K)
    (h : IsFunEqTypeMv (ι := Unit) p q hq τ f) : IsFunEqType p q τ f := by
  unfold IsFunEqType IsFunEqTypeMv at *
  have he : (PowerSeries.map τ f).subst ((X : PowerSeries K) ^ q)
      = MvPowerSeries.expand q hq (MvPowerSeries.map τ f) := by
    first
    | rfl
    | exact (MvPowerSeries.expand_eq_subst _ _ _).symm
    | (simp [MvPowerSeries.expand, PowerSeries.subst]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom]; congr 1)
    | (unfold MvPowerSeries.expand; rw [MvPowerSeries.coe_substAlgHom, PowerSeries.subst]; congr 1)
  rw [he]
  unfold IntegralPS
  intro n
  first
  | exact h $ Finsupp.single () n
  | exact (by unfold IntegralMv at h; exact h $ Finsupp.single () n)

omit [IsUltrametricDist K] [CharZero K] in
theorem inv_mul_inv_eq_of_eq_mul (c ε t x : K) (hc : c ≠ 0) (h : ε = c * t) :
    x⁻¹ * t⁻¹ = ε⁻¹ * (c / x) := by
  rw [h, mul_inv, div_eq_mul_inv]
  calc x⁻¹ * t⁻¹ = (c⁻¹ * c) * (t⁻¹ * x⁻¹) := by rw [inv_mul_cancel₀ hc, one_mul, mul_comm]
    _ = c⁻¹ * t⁻¹ * (c * x⁻¹) := by ring

theorem fin_integral [CompleteSpace K] (hF : FrobField K l σ) (ex lam : PowerSeries K)
    (hlam0 : constantCoeff lam = 0) (hlam1 : coeff 1 lam = 1) (hex0 : constantCoeff ex = 0)
    (hinv : ex.subst lam = X) (c ε : K) (hc : ‖c‖ = 1) (hε : ‖ε‖ = 1) (hcε : ε = c * σ (σ ε))
    (hT : IntegralPS $ lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) :
    IntegralPS $ ex.subst (C ε * ltLog K l) := by
  have hl2 := hF.prime.two_le
  have hq := pow_ne_zero 2 hF.prime.ne_zero
  have hS := hF.funEqSetting_sq
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hτε0 : σ (σ ε) ≠ 0 := fun h => hε0 $ by rw [hcε, h, mul_zero]
  set f0 : PowerSeries K := ε⁻¹ • lam with hf0
  have hf0T : IsFunEqType l (l ^ 2) (σ.comp σ) f0 := by
    unfold IsFunEqType
    have e : f0 - (l : K)⁻¹ • (PowerSeries.map (σ.comp σ) f0).subst ((X : PowerSeries K) ^ (l ^ 2))
        = C ε⁻¹ * (lam - (c / (l : K)) •
          (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
      have e1 : PowerSeries.map (σ.comp σ) f0 = (σ $ σ ε)⁻¹ • PowerSeries.map (σ.comp σ) lam := by
        ext n
        rw [hf0, coeff_map, PowerSeries.coeff_smul, PowerSeries.coeff_smul, coeff_map, smul_eq_mul,
          smul_eq_mul, map_mul, map_inv₀]
        rfl
      rw [e1, PowerSeries.subst_smul $ PowerSeries.HasSubst.X_pow hq, smul_smul, ← smul_eq_C_mul, smul_sub, smul_smul, hf0]
      congr 2
      have hc0 : c ≠ 0 := fun h => by simp [h] at hc
      exact inv_mul_inv_eq_of_eq_mul c ε _ _ hc0 hcε
    rw [e]
    exact integralPS_mul (integralPS_C $ by rw [norm_inv, hε, inv_one]) hT

  set α : PowerSeries K := C ε * X with hα
  have hα0 : constantCoeff α = 0 := by rw [hα, map_mul, constantCoeff_X, mul_zero]
  have hαs : PowerSeries.HasSubst α := PowerSeries.HasSubst.of_constantCoeff_zero' hα0
  have hαI : IntegralPS α := integralPS_mul (integralPS_C hε.le) integralPS_X
  set f1 : PowerSeries K := f0.subst α with hf1
  have hf1T := isFunEqType_of_mv hq _ _ $ Formalism.LT.funEqSubst K l (l ^ 2) hq (σ.comp σ) hS f0 (by
      rw [hf0, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul,
        coeff_zero_eq_constantCoeff_apply, hlam0, smul_zero]) hf0T Unit α
      hα0 $ (integralPS_iff_mv α).1 hαI
  have hf1e : f1 = ε⁻¹ • PowerSeries.rescale ε lam := by
    rw [hf1, hf0, PowerSeries.subst_smul hαs, PowerSeries.rescale_eq_subst, hα, ← smul_eq_C_mul]
  have hf11 : coeff 1 f1 = 1 := by
    rw [hf1e, PowerSeries.coeff_smul, coeff_rescale, hlam1, pow_one, mul_one, smul_eq_mul,
      inv_mul_cancel₀ hε0]
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.LT.funEqHom K l (l ^ 2) (σ.comp σ) hS f1 (ltLog K l) (by
      rw [hf1e, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul, coeff_rescale,
        coeff_zero_eq_constantCoeff_apply, hlam0]; simp) hf11
    hf1T (ltLog_const l hl2) $ ltLog_type hl2 _
  have hhs : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hβ0 : constantCoeff (C ε * h) = 0 := by rw [map_mul, hh0, mul_zero]
  have hβs : PowerSeries.HasSubst $ C ε * h := PowerSeries.HasSubst.of_constantCoeff_zero' hβ0
  have e2 : α.subst h = C ε * h := by
    rw [hα, PowerSeries.subst_mul hhs, PowerSeries.subst_X hhs, PowerSeries.subst_C]
    rfl
  have e3 : lam.subst (C ε * h) = C ε * ltLog K l := by
    rw [← hh, hf1, PowerSeries.subst_comp_subst_apply hαs hhs, e2, hf0,
      PowerSeries.subst_smul hβs, smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hε0,
      map_one, one_mul]
  rw [← e3, ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlam0) hβs, hinv, PowerSeries.subst_X hβs]
  exact integralPS_mul (integralPS_C hε.le) hhI

end ReciprocityTheory.ChartRestriction.L1
end
section
open Formalism.L2.Th1.A (IntModel bridgeLaw expSpec fgl fglLog logSer logSpec shortW uSerEq)
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem lgS_eq_logSer {K : Type} [Field K] [CharZero K] (g2 g3 : K) :
    lgS g2 g3 = logSer (shortW g2 g3) := by
  obtain ⟨h0, -, -, -⟩ := logSpec K $ shortW g2 g3
  obtain ⟨-, -, -, h4, -⟩ := expSpec K $ shortW g2 g3
  refine (lgS_unique g2 g3 _ h0 ?_).symm
  rwa [uSerEq K g2 g3]

theorem shortW_intModel {K : Type} [NormedField K] (g2 g3 : K)
    (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1) (h : ‖(2 : K)‖ = 1) :
    IntModel $ shortW g2 g3 := by
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, h, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [shortW, h4, h2, h3]

theorem curve_law {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K)
    (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1) (h : ‖(2 : K)‖ = 1) :
    LawD (lgS g2 g3) $ fgl $ shortW g2 g3 := by
  rw [lgS_eq_logSer]
  obtain ⟨⟨hF0, hFi, hl0, hl1, -⟩, -, -⟩ :=
    bridgeLaw K (shortW g2 g3) $ shortW_intModel g2 g3 h2 h3 h
  exact ⟨hl0, hl1, hF0, hFi, (fglLog K $ shortW g2 g3).1⟩

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

structure LatModel (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) :
    Prop where
  eq2 : g2 = ι L.g₂
  eq3 : g3 = ι L.g₃
  n2 : ‖g2‖ ≤ 1
  n3 : ‖g3‖ ≤ 1

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem good_lattice (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hg : IsGoodModel l L ι g2 g3) :
    ∃ L' : PeriodPair, LatModel l L' ι g2 g3 ∧ ∀ d, HasCMBy d L → HasCMBy d L' := by
  obtain ⟨-, -, h2, h3, -, lam, hlam, e2, e3⟩ := hg
  have hm : ι.symm lam ≠ 0 := by
    intro h
    apply hlam
    have := congrArg ι h
    simpa using this
  have hc := inv_ne_zero hm
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := F.homogeneity L (ι.symm lam)⁻¹ hc
  refine ⟨F.scalePair L (ι.symm lam)⁻¹ hc, ⟨?_, ?_, h2, h3⟩,
    fun d hd => F.hasCMByScale d L _ hc hd⟩
  rw [hg2, e2]
  simp
  rw [hg3, e3]
  simp

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem shortW_map (l : ℕ) [Fact l.Prime] (g2 g3 : ℂ) (ι : ℂ ≃+* ℂ_[l]) :
    A.shortW (ι g2) (ι g3) = (A.shortW g2 g3).map (ι : ℂ →+* ℂ_[l]) := by
  ext <;> simp [A.shortW, WeierstrassCurve.map, map_ofNat]

theorem wp_bridge (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) :
    A.wpReg (A.shortW (ι L.g₂) $ ι L.g₃) = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) := by
  rw [← F.curveBridge (A.shortW L.g₂ L.g₃) L (A.shortInv ℂ _ _).2.1 (A.shortInv ℂ _ _).2.2.1, (A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) $ A.shortW L.g₂ L.g₃).2.2.1, shortW_map]

end ReciprocityTheory.ChartRestriction.L1
end
section
open PowerSeries (constantCoeff map map_C map_X)
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

section MapLemmas

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem anIso_map_dblInt (e : PowerSeries K) :
    map φ (C.dblInt e) = C.dblInt (map φ e) := by
  ext n
  simp [C.dblInt, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs
  simp
  simp [map_div₀]

theorem anIso_constantCoeff_dblInt (e : PowerSeries K) :
    constantCoeff (C.dblInt e) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [C.dblInt]

theorem anIso_map_lam (e : PowerSeries K) (s2 : K) :
    map φ (C.lam e s2) = C.lam (map φ e) (φ s2) := by
  simp [C.lam, map_add, map_mul, map_pow, anIso_map_dblInt, map_C, map_X,
    map_div₀, map_ofNat]

theorem anIso_constantCoeff_lam (e : PowerSeries K) (s2 : K) :
    constantCoeff (C.lam e s2) = 0 := by
  simp [C.lam, anIso_constantCoeff_dblInt]

theorem anIso_map_sgStar [CharZero K] [CharZero K'] (e : PowerSeries K) (s2 : K) :
    map φ (C.sgStar e s2) = C.sgStar (map φ e) (φ s2) := by
  have h0 : constantCoeff (-(C.lam e s2)) = 0 := by
    simp [anIso_constantCoeff_lam]
  have h1 : map φ (C.mvExp $ -(C.lam e s2))
      = C.mvExp (-(C.lam (map φ e) $ φ s2)) := by
    unfold C.mvExp
    have := PowerSeries.map_subst (h := φ) (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      $ PowerSeries.exp K
    rw [PowerSeries.map_exp] at this
    rwa [← anIso_map_lam, ← map_neg]
  rw [C.sgStar, map_mul, map_X, h1, C.sgStar]

theorem anIso_map_wpShift (e : PowerSeries K) (c : K) :
    map φ (C.wpShift e c) = C.wpShift (map φ e) (φ c) := by
  simp [C.wpShift, map_add, map_one, map_mul, map_pow, map_sub, map_C,
    map_X]

end MapLemmas

theorem isogenyFormula_map {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
    (φ : K →+* K') (e : PowerSeries K) (s2 : K) {κ : Type} [Fintype κ] (c : κ → K) (al : K)
    (h : C.IsogenyFormula e s2 c al) :
    C.IsogenyFormula (map φ e) (φ s2) (fun P => φ $ c P) $ φ al := by
  have h' := congrArg (map φ) h
  unfold C.IsogenyFormula
  simp [map_mul, map_pow, map_prod, map_X, map_C, anIso_map_wpShift,
    anIso_map_sgStar, ← PowerSeries.rescale_map] at h'
  rwa [map_pow]

theorem iso_formula (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    C.IsogenyFormula (A.wpReg $ A.shortW (ι L.g₂) $ ι L.g₃) (ι $ F.s2 L)
      (fun P : S => ι $ L.weierstrassP (P : ℂ)) $ ι α := by
  rw [wp_bridge]
  exact isogenyFormula_map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) (F.s2 L)
    (fun P : S => L.weierstrassP (P : ℂ)) α $ F.isogenyFormulaInstance L α S hα hst hS

end ReciprocityTheory.ChartRestriction.L1
end
section
open PowerSeries (map)
open WeierstrassCurve (map_a₁ map_a₂ map_a₃ map_a₄)
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem trans_ev (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    ∀ᶠ z in nhds (0 : ℂ), z + t ∉ L.lattice := by
  have hc : ContinuousAt (fun z => z + t) 0 := by fun_prop
  have : (L.lattice : Set ℂ)ᶜ ∈ nhds ((fun z => z + t) 0) := by
    apply (L.isClosed_lattice.isOpen_compl).mem_nhds
    simpa using ht
  exact hc.eventually this

theorem trans_an (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    AnalyticAt ℂ (fun z => L.weierstrassP $ z + t) 0 ∧
      AnalyticAt ℂ (fun z => L.derivWeierstrassP $ z + t) 0 := by
  have h3 : AnalyticAt ℂ (fun z => z + t) 0 := by fun_prop
  exact ⟨AnalyticAt.comp (g := L.weierstrassP) (f := fun z => z + t) (L.analyticOnNhd_weierstrassP _ $ by simpa using ht) h3,
    AnalyticAt.comp (g := L.derivWeierstrassP) (f := fun z => z + t) (L.analyticOnNhd_derivWeierstrassP _ $ by simpa using ht) h3⟩

theorem trans_taylor_quad (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a b : ℂ) :
    F.taylor0 (fun z => a * (f z * f z) + b) = C a * (F.taylor0 f * F.taylor0 f) + C b := by
  obtain ⟨hR, hC, -, -⟩ := F.taylorRing
  have hff := hf.mul hf
  rw [(hR (fun z => a * (f z * f z)) (fun _ => b) (analyticAt_const.mul hff) analyticAt_const).1, (hR (fun _ => a) (fun z => f z * f z) analyticAt_const hff).2, (hR f f hf hf).2, hC, hC]

theorem trans_taylor_cubic (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a b c : ℂ) :
    F.taylor0 (fun z => a * (f z * (f z * f z)) + (b * f z + c))
      = C a * (F.taylor0 f * (F.taylor0 f * F.taylor0 f)) + (C b * F.taylor0 f + C c) := by
  obtain ⟨hR, hC, -, -⟩ := F.taylorRing
  have hff := hf.mul hf
  have hfff := hf.mul hff
  have h1 := (hR f f hf hf).2
  have h2 := (hR f (fun z => f z * f z) hf hff).2
  have h3 := (hR (fun _ => a) (fun z => f z * (f z * f z)) analyticAt_const hfff).2
  have h4 := (hR (fun _ => b) f analyticAt_const hf).2
  have h5 := (hR (fun z => b * f z) (fun _ => c) (analyticAt_const.mul hf) analyticAt_const).1
  have h6 := (hR (fun z => a * (f z * (f z * f z))) (fun z => b * f z + c) (analyticAt_const.mul hfff) $ (analyticAt_const.mul hf).add analyticAt_const).1
  rw [h6, h5, h4, h3, h2, h1, hC, hC, hC]

theorem trans_taylor (L : PeriodPair) (t : ℂ) (ht : t ∉ L.lattice) :
    derivative (F.taylor0 fun z => L.weierstrassP $ z + t)
        = F.taylor0 (fun z => L.derivWeierstrassP $ z + t) ∧
    derivative (F.taylor0 fun z => L.derivWeierstrassP $ z + t)
        = C 6 * (F.taylor0 (fun z => L.weierstrassP $ z + t)
            * F.taylor0 fun z => L.weierstrassP $ z + t) + C (-(L.g₂ / 2)) ∧
    F.taylor0 (fun z => L.derivWeierstrassP $ z + t) * F.taylor0 (fun z => L.derivWeierstrassP $ z + t)
        = C 4 * (F.taylor0 (fun z => L.weierstrassP $ z + t)
            * (F.taylor0 (fun z => L.weierstrassP $ z + t)
              * F.taylor0 fun z => L.weierstrassP $ z + t))
          + (C (-L.g₂) * F.taylor0 (fun z => L.weierstrassP $ z + t) + C (-L.g₃)) := by
  obtain ⟨haf, hag⟩ := trans_an L t ht
  obtain ⟨hR, hC, -, hG⟩ := F.taylorRing
  obtain ⟨hD, -, -⟩ := F.taylorDeriv
  have hev := trans_ev L t ht
  refine ⟨?_, ?_, ?_⟩
  rw [← hD _ haf]
  congr 1
  funext z
  rw [deriv_comp_add_const, L.deriv_weierstrassP]
  rw [← hD _ hag, ← trans_taylor_quad _ haf]
  apply hG
  filter_upwards [hev] with z hz
  rw [deriv_comp_add_const, (F.pSecond L (z + t) hz).deriv]
  ring
  rw [← (hR _ _ hag hag).2, ← trans_taylor_cubic _ haf]
  apply hG
  filter_upwards [hev] with z hz
  have := L.derivWeierstrassP_sq (z + t) hz
  linear_combination this

theorem trans_derivative_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R⟦X⟧) :
    derivative (map φ f) = map φ (derivative f) := by
  ext n
  simp [coeff_derivative]

theorem trans_constSubst {K : Type*} [CommRing K] (f a : K⟦X⟧) (ha : constantCoeff a = 0) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have h1 := constantCoeff_subst_eq_zero (S := K) ha (f - C (constantCoeff f)) $ by simp
  rw [subst_sub $ HasSubst.of_constantCoeff_zero' ha, subst_C] at h1
  have h2 : constantCoeff (subst a f - C (constantCoeff f)) = 0 := h1
  rwa [map_sub, constantCoeff_C, sub_eq_zero] at h2

theorem trans_plus_const {K : Type} [Field K] (g2 g3 xP yP : K) :
    constantCoeff (A.yPlus (A.shortW g2 g3) xP yP) = yP ∧
    constantCoeff (A.xPlus (A.shortW g2 g3) xP yP) = xP := by
  obtain ⟨-, -, -, hx, hy⟩ := A.wSerFactor K $ A.shortW g2 g3
  have ht : constantCoeff (A.tDen (A.shortW g2 g3) xP) = 1 := by simp [A.tDen, hx]
  have h1 : (A.shortW g2 g3).a₁ = 0 := rfl
  have h3 : (A.shortW g2 g3).a₃ = 0 := rfl
  constructor
  simp [A.yPlus, A.xPlus, A.nS, hx, hy, ht, h1, h3]
  ring
  simp [A.xPlus]

theorem trans_bridge (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (t : ℂ)
    (ht : t ∉ L.lattice) :
    map (ι : ℂ →+* ℂ_[l]) (F.taylor0 fun z => L.weierstrassP $ z + t)
      = (A.xPlus (A.shortW (ι L.g₂) $ ι L.g₃) (ι $ L.weierstrassP t)
          $ ι (L.derivWeierstrassP t) / 2).subst (A.expSer $ A.shortW (ι L.g₂) $ ι L.g₃) := by
  obtain ⟨e1, e2, e3⟩ := trans_taylor L t ht
  set p := F.taylor0 (fun z => L.weierstrassP $ z + t) with hp
  set q := F.taylor0 (fun z => L.derivWeierstrassP $ z + t) with hq
  set W := A.shortW (ι L.g₂) (ι L.g₃) with hW
  have a1 : W.a₁ = 0 := rfl
  have a2 : W.a₂ = 0 := rfl
  have a3 : W.a₃ = 0 := rfl
  have a4 : W.a₄ = -ι L.g₂ / 4 := rfl
  have a6 : W.a₆ = -ι L.g₃ / 4 := rfl
  have hpt : W.toAffine.Equation (ι $ L.weierstrassP t) $ ι (L.derivWeierstrassP t) / 2 := by
    rw [WeierstrassCurve.Affine.equation_iff, a1, a2, a3, a4, a6]
    have := congrArg ι $ L.derivWeierstrassP_sq t ht
    simp only [map_pow, map_sub, map_mul, map_ofNat] at this
    linear_combination (1 / 4 : ℂ_[l]) * this
  obtain ⟨hfl, -, -⟩ := A.plusZ ℂ_[l] W _ _ hpt
  set P := map (ι : ℂ →+* ℂ_[l]) p with hP
  set Q := map (ι : ℂ →+* ℂ_[l]) q with hQ
  have E2 : derivative Q = C 6 * (P * P) + C (-(ι L.g₂ / 2)) := by
    rw [hQ, trans_derivative_map, e2]
    simp [hP, map_ofNat ι 2, map_ofNat ι 6]
  have E3 : Q * Q = C 4 * (P * (P * P)) + (C (-ι L.g₂) * P + C (-ι L.g₃)) := by
    rw [hQ, ← map_mul, e3]
    simp [hP, map_ofNat ι 4]
  have h2 : (C (1 / 2 : ℂ_[l]) : ℂ_[l]⟦X⟧) * 2 = 1 := by
    rw [← map_ofNat (C : ℂ_[l] →+* ℂ_[l]⟦X⟧) 2, ← map_mul]
    norm_num
  have hfl' : A.IsFlow (A.curveS W) (derivative (R := ℂ_[l])) P $ C (1 / 2 : ℂ_[l]) * Q := by
    have c4 : (C (-ι L.g₂ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₂) := by
      rw [← map_mul, ← map_mul]
      congr 1; ring
    have c6 : (C (-ι L.g₃ / 4) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (1 / 2) * C (-ι L.g₃) := by
      rw [← map_mul, ← map_mul]
      congr 1; ring
    have c2 : (C (-(ι L.g₂ / 2)) : ℂ_[l]⟦X⟧) = C (1 / 2) * C (-ι L.g₂) := by
      rw [← map_mul]
      congr 1; ring
    have k4 : (C 4 : ℂ_[l]⟦X⟧) = 4 := map_ofNat _ 4
    have k6 : (C 6 : ℂ_[l]⟦X⟧) = 6 := map_ofNat _ 6
    refine ⟨?_, ?_, ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [map_a₁, map_a₂, map_a₃,
      map_a₄, WeierstrassCurve.map_a₆, a1, a2, a3, a4, a6, map_zero, c4, c6]
    rw [k4] at E3
    linear_combination (C (1 / 2 : ℂ_[l]) * C (1 / 2)) * E3 +
      (P ^ 3 * (C (1 / 2 : ℂ_[l]) * 2 + 1)) * h2
    simp only [map_a₁, map_a₃, a1, a3, map_zero]
    rw [hP, trans_derivative_map, e1]
    linear_combination (-Q) * h2
    simp only [map_a₁, map_a₂, map_a₄,
      a1, a2, a4, map_zero, c4]
    rw [← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul, E2, k6, c2]
    linear_combination (3 * P ^ 2) * h2
  have hc0 := (A.expSpec ℂ_[l] W).1
  refine (A.flowUniqueZ ℂ_[l] W _ _ _ _ hfl' hfl ?_ ?_).1
  rw [trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).2, hP, hp]
  simp [← coeff_zero_eq_constantCoeff_apply, F.taylor0]
  rw [trans_constSubst _ _ hc0, (trans_plus_const _ _ _ _).1, hQ, hq]
  simp [← coeff_zero_eq_constantCoeff_apply, F.taylor0]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
section
open PowerSeries (map rescale)
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem endo_curve (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    ∃ neg : S → S, C.IsEndoCurve (A.shortW (ι L.g₂) (ι L.g₃)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ))) (fun P : S => ι (L.derivWeierstrassP (P : ℂ)) / 2)
      $ ι α := by
  obtain ⟨neg, hneg, hinv, -, hid⟩ := F.endoZInstance L α S hα hst hS
  have hb2 : (A.shortW (ι L.g₂) $ ι L.g₃).b₂ = 0 := by
    simp [A.shortW, WeierstrassCurve.b₂]
  have hnegeq : ∀ P, (neg P : ℂ) = -(P : ℂ) + ((⟨_, hneg P⟩ : L.lattice) : ℂ) := by
    intro P
    simp
  refine ⟨neg, ?_, hinv, ?_, ?_⟩
  intro P
  have h := L.derivWeierstrassP_sq (P : ℂ) (hS.1 P P.2).2
  have h' := congrArg ι h
  simp [map_pow, map_sub, map_mul, map_ofNat] at h'
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [A.shortW]
  linear_combination (1 / 4 : ℂ_[l]) * h'
  intro P
  constructor
  show ι (L.weierstrassP (neg P : ℂ)) = _
  rw [hnegeq P, L.weierstrassP_add_coe, L.weierstrassP_neg]
  show ι (L.derivWeierstrassP (neg P : ℂ)) / 2 = _
  rw [hnegeq P, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_neg]
  simp [WeierstrassCurve.Affine.negY, A.shortW, neg_div]
  have h := congrArg (map (ι : ℂ →+* ℂ_[l])) hid
  rw [wp_bridge]
  simp [C.wTr, hb2, zero_div, add_zero, map_zero]
  simp [← trans_bridge l L ι _ (hS.1 _ $ Subtype.coe_prop _).2]
  simp [map_mul, map_add, map_sum, map_sub, PowerSeries.map_C, map_pow] at h
  have hr : map (ι : ℂ →+* ℂ_[l]) (rescale α $ F.pSeries L)
      = rescale (ι α) (map (ι : ℂ →+* ℂ_[l]) $ F.pSeries L) := by
    ext n
    simp [PowerSeries.coeff_rescale]
  rw [hr] at h
  simpa using h

end ReciprocityTheory.ChartRestriction.L1
end
end
