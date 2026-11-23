import Mathlib
import Bundle03
noncomputable section
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem exists_powerSeries_square_formula {K : Type} [Field K] [CharZero K] (R : Subring K) (M a ph G : PowerSeries K)
    (c : ℕ) (m : K) (ha : constantCoeff a = 0) (hph : constantCoeff ph = 0)
    (hc : (c : K) + 1 = m)
    (hiso : M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c) =
      G * X ^ (2 * (c + 1)) * C.mvExp (-((2 * ((c : K) + 1)) • ph)))
    (hcong : C.Cong R a $ m • ph) :
    ∃ U, constantCoeff U = 1 ∧ C.IntPS R U ∧ M ^ 2 = X ^ 2 * U * G := by
  obtain ⟨h0, h1, hadd, -⟩ := C.mvExpLaws K Unit
  obtain ⟨-, hLadd, -⟩ := C.lGSubgroup K R Unit
  have hD := hLadd _ _ hcong hcong
  have ha' : MvPowerSeries.constantCoeff a = 0 := ha
  have hph' : MvPowerSeries.constantCoeff ph = 0 := hph
  have c1 : MvPowerSeries.constantCoeff (-((2 : K) • a)) = 0 := by
    rw [map_neg, MvPowerSeries.smul_eq_C_mul, map_mul, ha', mul_zero, neg_zero]
  have c2 : MvPowerSeries.constantCoeff ((2 : K) • a) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, ha', mul_zero]
  have c3 : MvPowerSeries.constantCoeff (-((2 * ((c : K) + 1)) • ph)) = 0 := by
    rw [map_neg, MvPowerSeries.smul_eq_C_mul, map_mul, hph', mul_zero, neg_zero]
  use C.mvExp $ (a - m • ph) + (a - m • ph), h1 _ hD.1, fun n => hD.2 _
  have e1 : C.mvExp (-((2 : K) • a)) * C.mvExp ((2 : K) • a) = 1 := by
    rw [← hadd _ _ c1 c2, neg_add_cancel, h0]
  have e2 : C.mvExp (-((2 * ((c : K) + 1)) • ph)) * C.mvExp ((2 : K) • a)
      = C.mvExp ((a - m • ph) + (a - m • ph)) := by
    rw [← hadd _ _ c3 c2, hc]
    congr 1
    rw [mul_smul, two_smul, two_smul]
    abel
  apply mul_right_cancel₀ $ pow_ne_zero _ X_ne_zero
  calc M ^ 2 * X ^ (2 * c)
      = (M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c)) * C.mvExp ((2 : K) • a) := by
        rw [show M ^ 2 * C.mvExp (-((2 : K) • a)) * X ^ (2 * c) * C.mvExp ((2 : K) • a)
          = M ^ 2 * X ^ (2 * c) * (C.mvExp (-((2 : K) • a)) * C.mvExp ((2 : K) • a)) by ring,
          e1, mul_one]
    _ = G * X ^ (2 * (c + 1)) *
          (C.mvExp (-((2 * ((c : K) + 1)) • ph)) * C.mvExp ((2 : K) • a)) := by
        rw [hiso]
        ring
    _ = X ^ 2 * C.mvExp ((a - m • ph) + (a - m • ph)) * G * X ^ (2 * c) := by
        rw [e2]
        ring

theorem sq_formula (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (n : ℕ) (hn : 0 < n) (S : Finset ℂ)
    (hS : F.IsKerReps L (n : ℂ) S) :
    ∃ U, constantCoeff U = 1 ∧ IntegralPS U ∧
      ((uSer g2 g3).subst (C (n : ℂ_[l]) * lgS g2 g3)) ^ 2 =
        X ^ 2 * U * (C ((n : ℂ_[l]) ^ 2) *
          ∏ P ∈ S, (A.xS (A.shortW g2 g3) - C (ι (L.weierstrassP P)) * X ^ 2)) := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have : ¬ l ∣ 2 := fun hd => hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
    exact_mod_cast norm_natCast_Cl_of_not_dvd l this
  have h2R : (2 : ℂ_[l])⁻¹ ∈ unitBall ℂ_[l] := by
    change ‖(2 : ℂ_[l])⁻¹‖ ≤ 1
    rw [norm_inv, h2, inv_one]
  have h4 : ‖(4 : ℂ_[l])‖ = 1 := by
    have : (4 : ℂ_[l]) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  set W := A.shortW g2 g3 with hW
  have hco : C.CoeffIn (unitBall ℂ_[l]) W := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    exact (unitBall ℂ_[l]).zero_mem
    exact (unitBall ℂ_[l]).zero_mem
    exact (unitBall ℂ_[l]).zero_mem
    change ‖-g2 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]
    exact hM.n2
    change ‖-g3 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]
    exact hM.n3
  have hb2 : W.b₂ / 12 = 0 := by
    rw [(A.shortInv ℂ_[l] g2 g3).1, zero_div]
  obtain ⟨hLP, hXW, -, hFG, -⟩ := C.curveFrame ℂ_[l] (unitBall ℂ_[l]) W hco
  set s2 : ℂ_[l] := ι (F.s2 L) with hs2
  set ph := B.phO s2 (A.wpReg W) (A.logSer W) with hph
  have hPh : C.IsPh (A.wpReg W) s2 (A.logSer W) ph :=
    (C.phOIsPh ℂ_[l] (A.wpReg W) (A.logSer W) s2 hLP.1 hLP.2.1).2
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hst : F.MulStable L (n : ℂ) := by
    intro ω hω
    have := L.lattice.nsmul_mem hω n
    rwa [nsmul_eq_mul] at this
  have hIF := iso_formula l L ι (n : ℂ) S hn0 hst hS
  rw [← hM.eq2, ← hM.eq3, map_natCast] at hIF
  have hU := C.isogenyU ℂ_[l] (A.wpReg W) s2 (A.logSer W) (A.expSer W) ph (A.xS W) (W.b₂ / 12) S
    (fun P => ι (L.weierstrassP (P : ℂ))) (n : ℂ_[l]) hLP hPh hXW
    $ by simpa only [hb2, add_zero] using hIF
  have hN := phNorm_int (unitBall ℂ_[l]) (A.logSer W) (A.expSer W) ph (⟨hLP, hFG, hPh.1⟩)
    (G.weierstrass_biadditive_mod_equiv ℂ_[l] W hco h2 s2) (G.curveNegNorm ℂ_[l] (unitBall ℂ_[l]) W hco h2R s2) h2R (n : ℤ)
  rw [Int.cast_natCast] at hN
  have hMul : (uSer g2 g3).subst (C (n : ℂ_[l]) * lgS g2 g3)
      = C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l]) := by
    rw [lgS_eq_logSer, A.uSerEq ℂ_[l] g2 g3]
    rfl
  have hM0 : constantCoeff (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) = 0 := by
    rw [← hMul]
    exact mult_const g2 g3 _
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_powerSeries_square_formula (unitBall ℂ_[l])
    (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l]))
    (PowerSeries.subst (C.mulBy (A.logSer W) (A.expSer W) (n : ℂ_[l])) ph) ph
    (C ((n : ℂ_[l]) ^ 2) * ∏ P : S, (A.xS W - C (ι (L.weierstrassP (P : ℂ))) * X ^ 2))
    (Fintype.card S) ((n : ℂ_[l]) * (n : ℂ_[l])) (constantCoeff_subst_eq_zero hM0 _ hPh.1) hPh.1 (by
        have h := F.kerRepsCard L (n : ℂ) S hn0 hst hS
        rw [Complex.normSq_natCast] at h
        rw [Fintype.card_coe]
        exact_mod_cast (by exact_mod_cast h))
    (by rw [hU]; ring) hN
  use U, hU1, hU2
  rw [hMul, hU3, Finset.prod_coe_sort S
    fun P => A.xS W - C (ι (L.weierstrassP P)) * X ^ 2]

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem le_one_of_prod_max_le_one {α : Type} (S : Finset α) (f : α → ℝ)
    (h : ∏ P ∈ S, max 1 (f P) ≤ 1) (Q : α) (hQ : Q ∈ S) : f Q ≤ 1 := by
  classical
  rw [← Finset.mul_prod_erase S _ hQ] at h
  exact (le_max_right _ _).trans $ (le_mul_of_one_le_right (le_trans zero_le_one $ le_max_left _ _) $ by
      simpa using Finset.prod_le_prod₀ (s := S.erase Q) (fun _ _ => zero_le_one)
        fun P _ => le_max_left (1 : ℝ) $ f P).trans h

theorem tor_integral (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (n : ℕ) (hn : 0 < n) (hln : ¬ l ∣ n) (P : ℂ)
    (hP : (n : ℂ) * P ∈ L.lattice) (hP' : P ∉ L.lattice) :
    ‖ι (L.weierstrassP P)‖ ≤ 1 ∧ ‖ι (L.derivWeierstrassP P)‖ ≤ 1 := by
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := norm_natCast_Cl_of_not_dvd l (n := 2)
      fun h => hl $ (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h
    simpa using this
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hst : F.MulStable L (n : ℂ) := fun ω hω => by
    have := L.lattice.nsmul_mem hω n
    rwa [nsmul_eq_mul] at this
  obtain ⟨S, hS⟩ := F.kerRepsExist L (n : ℂ) hn0 hst
  obtain ⟨U, hU0, hUi, hsq⟩ := sq_formula l hl L ι g2 g3 hM n hn S hS
  obtain ⟨e, he0, hei, hel⟩ := mulN_integral (curve_law g2 g3 hM.n2 hM.n3 h2) n
  rw [← mult_unique g2 g3 (n : ℂ_[l]) e he0 hel] at hsq
  obtain ⟨hxi, hx0, -, -⟩ := A.bridgeCurve ℂ_[l] (A.shortW g2 g3)
    $ shortW_intModel g2 g3 hM.n2 hM.n3 h2
  have hb := gauss_bound S (fun P => ι $ L.weierstrassP P) _ ((integralPS_iff_mv _).2 hxi) hx0 _ $ integral_of_sq_eq hei he0 hUi hU0 hsq
  rw [norm_pow, norm_natCast_Cl_of_not_dvd l hln, one_pow, one_mul] at hb
  obtain ⟨Q, hQ, hPQ⟩ := hS.2.2 P hP hP'
  have hPQ' : L.weierstrassP P = L.weierstrassP Q := by
    have := L.weierstrassP_add_coe Q ⟨P - Q, hPQ⟩
    simpa using this
  have hx : ‖ι (L.weierstrassP P)‖ ≤ 1 := by rw [hPQ']
                                             exact le_one_of_prod_max_le_one S (fun P => ‖ι (L.weierstrassP P)‖) hb Q hQ
  use hx
  have hrel := congrArg ι $ L.derivWeierstrassP_sq P hP'
  simp [map_pow, map_sub, map_mul, ← hM.eq2, ← hM.eq3] at hrel
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 $ by
      rw [← norm_pow, hrel]
      refine (norm_sub_le_max_Cl l _ _).trans $ max_le ?_ hM.n3
      refine (norm_sub_le_max_Cl l _ _).trans $ max_le ?_ ?_
      rw [norm_mul, norm_pow]
      exact mul_le_one₀ (by
          have : ι (4 : ℂ) = ((4 : ℕ) : ℂ_[l]) := by
            rw [← map_natCast ι 4]
            norm_num
          rw [this]
          exact IsUltrametricDist.norm_natCast_le_one ℂ_[l] 4) (by positivity) $ pow_le_one₀ (norm_nonneg _) hx
      rw [norm_mul]
      exact mul_le_one₀ hM.n2 (norm_nonneg _) hx

end ReciprocityTheory.ChartRestriction.L1
end
section
open Formalism.L2.Th1.A (shortW uSerEq)
open Formalism.L2.Th1.C (curveEndoR curveFrame endIntFromDatum inv_mem_unitBall)
open Formalism.L2.Th1.F (IsKerReps hasCMByStable kerRepsCard kerRepsExist)
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem end_not_dvd (d : ℕ) (hd : d % 4 = 3) (l : ℕ) [Fact l.Prime]
    (hin : ¬ ∃ a, a ^ 2 = -(d : ZMod l)) : ¬ l ∣ (d + 1) / 4 := by
  intro h
  apply hin
  use 1
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h0 : ((d + 1 : ℕ) : ZMod l) = 0 := by
    rw [← h4, ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.mul_left h 4
  push_cast at h0
  linear_combination h0

theorem end_unit (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : ¬ l ∣ n) (a : ℂ_[l]) (ha : ‖a‖ ≤ 1)
    (hq : a ^ 2 - a + (n : ℂ_[l]) = 0) : ‖a‖ = 1 := by
  have hnn : ‖(n : ℂ_[l])‖ = 1 := by
    simpa using kq_int_unit l (n : ℤ) $ by exact_mod_cast hn
  have hprod : a * (1 - a) = n := by linear_combination -hq
  refine le_antisymm ha ?_
  rw [← hnn, ← hprod, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) $ by
      have e : 1 - a = 1 + -a := by ring
      rw [e]
      apply kq_add_le l _ _ 1 $ by simp
      rwa [norm_neg]

theorem end_card (d : ℕ) (hd : d % 4 = 3) (L : PeriodPair) (hCM : HasCMBy d L) (S : Finset ℂ)
    (h0 : omegaK d ≠ 0) (hS : IsKerReps L (omegaK d) S) :
    S.card + 1 = (d + 1) / 4 := by
  have h2 := (hasCMByStable d L hCM 0 1).2
  have h4' : (4 : ℝ) * (((d + 1) / 4 : ℕ) : ℝ) = (d : ℝ) + 1 := by exact_mod_cast (by omega)
  simp at h2
  have h3 : ((S.card + 1 : ℕ) : ℝ) = (((d + 1) / 4 : ℕ) : ℝ) := by
    push_cast
    rw [kerRepsCard L (omegaK d) S h0 hCM hS, h2]
    push_cast
    linarith
  exact_mod_cast h3

theorem end_integral (d : ℕ) (L : PeriodPair) (hd : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (hl : 5 ≤ l) (hld : ¬ l ∣ d) (hin : ¬ ∃ a, a ^ 2 = -(d : ZMod l))
    (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    IntegralPS ((uSer g2 g3).subst (C (ι (omegaK d)) * lgS g2 g3)) := by
  obtain ⟨L', hM, hCM'⟩ := good_lattice l L ι g2 g3 hg
  have hCM1 := hCM' d hCM
  have hl2 : l ≠ 2 := by omega
  have hquadC := omegaK_quad d hd
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι hquadC
    simpa using this
  have hln := end_not_dvd d hd l hin
  obtain ⟨ha1, -, -⟩ := kur_quad l d hd hl2 hld hin _ hquad
  have hau : ‖ι (omegaK d)‖ = 1 := end_unit l _ hln _ ha1 hquad
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := kq_int_unit l 2 (by
      intro h
      have h' : l ∣ 2 := by exact_mod_cast h
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'))
    simpa using this
  have hα : omegaK d ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hau
    exact zero_ne_one hau
  obtain ⟨S, hS⟩ := kerRepsExist L' (omegaK d) hα hCM1
  obtain ⟨neg, hE⟩ := endo_curve l L' ι (omegaK d) S hα hCM1 hS
  rw [← hM.eq2, ← hM.eq3] at hE
  have htor : ∀ P : S, ‖ι (L'.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L'.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    obtain ⟨hP1, hP2⟩ := hS.1 P P.2
    refine tor_integral l hl2 L' ι g2 g3 hM _ (by omega) hln P ?_ hP2
    have e : (((d + 1) / 4 : ℕ) : ℂ) * (P : ℂ) = omegaK d * (P : ℂ) - omegaK d * (omegaK d * (P : ℂ)) := by
      linear_combination (P : ℂ) * hquadC
    rw [e]
    exact sub_mem hP1 (hCM1 _ hP1)
  have hc :=
    shortW_intModel g2 g3 hM.n2 hM.n3 h2
  obtain ⟨hlp, hwp, hAx, -, -⟩ := curveFrame ℂ_[l] (unitBall ℂ_[l]) _ hc
  have hDat := curveEndoR ℂ_[l] (unitBall ℂ_[l]) _ hc S neg _ _ (ι (omegaK d))
    (1 - ι (omegaK d)) hE (fun P => (htor P).1)
    (fun P => by
      change ‖ι (L'.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
      rw [norm_div, h2, div_one]
      exact (htor P).2)
    (by
      rw [Fintype.card_coe]
      have : ((S.card : ℂ_[l]) + 1) = (((d + 1) / 4 : ℕ) : ℂ_[l]) := by exact_mod_cast (end_card d hd L' hCM1 S hα hS)
      rw [this]
      linear_combination -hquad)
    hau.le (inv_mem_unitBall hau)
    $ by
      have : (shortW g2 g3).b₂ = 0 := by
        simp [shortW, WeierstrassCurve.b₂]
      rw [this]
      simp
  have hEnd := endIntFromDatum ℂ_[l] (unitBall ℂ_[l]) _ _ _ _ _ S neg _ _ _ _ _
    hlp hwp hAx (inv_mem_unitBall h2) hDat
  rwa [lgS_eq_logSer, uSerEq]

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem half_cubic (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hM : LatModel l L ι g2 g3) :
    4 * ι (L.weierstrassP $ L.ω₁ / 2) ^ 3 - g2 * ι (L.weierstrassP $ L.ω₁ / 2) - g3 = 0 := by
  have h := L.derivWeierstrassP_sq _ L.ω₁_div_two_notMem_lattice
  rw [(F.pDerivZero L _ L.ω₁_div_two_notMem_lattice).2 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice)] at h
  have h' := congrArg ι h
  simp only [map_pow, map_mul, map_sub, map_zero, map_ofNat] at h'
  rw [hM.eq2, hM.eq3, ← h']
  norm_num

theorem half_prod_norm (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (S : Finset ℂ) (hS : F.IsKerReps L (l : ℂ) S)
    (hκ : ‖3 * ι (L.weierstrassP $ L.ω₁ / 2) ^ 2 - g2 / 4‖ = 1) :
    ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L.weierstrassP $ L.ω₁ / 2) - ι (L.weierstrassP P)‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have h := congrArg ι $ an_two L l (hlp.odd_of_ne_two hl) S hS L.ω₁ L.ω₁_mem_lattice
    L.ω₁_div_two_notMem_lattice
  simp [map_pow, map_mul, map_prod, map_sub, map_natCast, map_div₀, map_ofNat] at h
  rw [← hM.eq2] at h
  have hn := congrArg norm h
  rw [norm_pow, norm_pow _ $ l ^ 2 - 1, hκ, one_pow, norm_mul, norm_prod] at hn
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 hn

theorem level_le (L : PeriodPair) (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer g2 g3).subst (C (l : ℂ_[l]) * lgS g2 g3))‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := by omega
  obtain ⟨L', hM, -⟩ := good_lattice l L ι g2 g3 hg
  obtain ⟨-, -, h2, h3, hΔ, -⟩ := hg
  have h22 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := norm_natCast_Cl_of_not_dvd (l := l) (n := 2)
      fun h => hl2 $ (Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h
    simpa using this
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hst : F.MulStable L' (l : ℂ) := fun ω hω => by
    have := L'.lattice.smul_mem (l : ℤ) hω
    simpa using this
  obtain ⟨S, hS⟩ := F.kerRepsExist L' (l : ℂ) hl0 hst
  have hcard : S.card + 1 = l ^ 2 := by
    have := F.kerRepsCard L' (l : ℂ) S hl0 hst hS
    rw [Complex.normSq_natCast] at this
    have h' : ((S.card + 1 : ℕ) : ℝ) = ((l ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [this]
      ring
    exact_mod_cast h'
  obtain ⟨U, hU0, hUi, hsq⟩ := sq_formula l hl2 L' ι g2 g3 hM l hlp.pos S hS
  obtain ⟨e', he'0, he'i, he'l⟩ := mulN_integral (curve_law g2 g3 h2 h3 h22) l
  rw [← mult_unique g2 g3 _ e' he'0 he'l] at hsq ⊢
  obtain ⟨hAi, hA0, -⟩ :=
    A.bridgeCurve ℂ_[l] (A.shortW g2 g3) $ shortW_intModel g2 g3 h2 h3 h22
  have hAi' := (integralPS_iff_mv _).2 hAi
  have hGi := integral_of_sq_eq he'i he'0 hUi hU0 hsq
  obtain ⟨he1, hκ⟩ := kap_unit g2 g3 _ h2 h3 hΔ h22 $ half_cubic l L' ι g2 g3 hM
  have hle : ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L'.weierstrassP $ L'.ω₁ / 2) - ι (L'.weierstrassP P)‖
      ≤ ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, max 1 ‖ι (L'.weierstrassP P)‖ := by
    refine mul_le_mul_of_nonneg_left ?_ $ norm_nonneg _
    refine Finset.prod_le_prod₀ (fun P _ => norm_nonneg _) fun P _ => ?_
    exact (norm_sub_le_max_Cl l _ _).trans $ max_le_max he1 le_rfl
  rw [half_prod_norm l hl2 L' ι g2 g3 hM S hS hκ] at hle
  obtain ⟨i, hi, hi1⟩ := unit_coeff_mul hUi hGi (by rw [hU0, norm_one]) _
    $ gauss_unit S (fun P => ι $ L'.weierstrassP P) _ hAi' hA0 _ $ le_antisymm (gauss_bound S (fun P => ι $ L'.weierstrassP P) _ hAi' hA0 _ hGi) hle
  refine unit_coeff_of_sq he'i (l ^ 2) ⟨i + 2, by omega, ?_⟩
  rwa [hsq, mul_assoc, coeff_X_pow_mul]

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.subst_of_log (h : LawD lam Φ) {e : PowerSeries K} {c : K} (he0 : constantCoeff e = 0)
    (hlog : lam.subst e = C c * lam) : e.subst Φ = Φ.subst ![atX e, atY e] := by
  have hes := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero $ MvPowerSeries.constantCoeff_X i
  have hx0 : MvPowerSeries.constantCoeff (atX e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hy0 : MvPowerSeries.constantCoeff (atY e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hb := Formalism.G.LogP.hs2 hx0 hy0
  refine Formalism.G.LogP.psubst_injective h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero h.Φ0 _ he0)
    (MvPowerSeries.constantCoeff_subst_eq_zero hb (by intro i; fin_cases i <;> simpa) h.Φ0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hΦs, hlog', PowerSeries.subst_smul hΦs, h.log,
    ← Formalism.G.LogP.psubst_subst lam h.Φ0 hb, h.log, MvPowerSeries.subst_add hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  show _ = lam.subst (e.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
    + lam.subst (e.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
  rw [← PowerSeries.subst_comp_subst_apply hes $ hX 0, ← PowerSeries.subst_comp_subst_apply hes $ hX 1,
    hlog', PowerSeries.subst_smul $ hX 0, PowerSeries.subst_smul $ hX 1, smul_add]

theorem LawD.comm_of_log (h : LawD lam Φ) {e f : PowerSeries K} {c d : K}
    (he0 : constantCoeff e = 0) (hf0 : constantCoeff f = 0)
    (hlog : lam.subst e = C c * lam) (hlogf : lam.subst f = C d * lam) :
    e.subst f = f.subst e := by
  have hes := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hfs := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hlogf' : lam.subst f = d • lam := by rw [hlogf, smul_eq_C_mul]
  refine Formalism.G.LogP.psubst_injective (σ := Unit) h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero hf0 _ he0)
    (PowerSeries.constantCoeff_subst_eq_zero he0 _ hf0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hfs, ← PowerSeries.subst_comp_subst_apply hfs hes,
    hlog', hlogf', PowerSeries.subst_smul hfs, PowerSeries.subst_smul hes, hlog', hlogf',
    smul_smul, smul_smul, mul_comm]

theorem mulL_homCls (h : HD σ lam Φ A a) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) : HomCls l Φ A Φ A e where
  g0 := he0
  gInt := he
  add := by
    rw [h.toLawD.subst_of_log he0 hlog, sub_self]
    exact divByMv_zero _
  eig := by
    rw [h.toLawD.comm_of_log he0 h.A0 hlog h.Alog, sub_self]
    intro n
    simp

theorem mulL_deriv (h : LawD lam Φ) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    DivBy (l : K) $ derivative e := by
  have h1 : (derivative lam).subst e * derivative e = C (l : K) * derivative lam := by
    rw [← PowerSeries.derivative_subst $ PowerSeries.HasSubst.of_constantCoeff_zero' he0, hlog]
    simp
  have hc : constantCoeff ((derivative lam).subst e) = 1 := by
    rw [← h.deriv_const]
    exact Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (τ := Unit) (derivative lam)
      (b := fun _ => e) fun _ => he0
  refine divBy_of_mul_unit ((integralPS_iff_mv _).2 $ integralMv_subst h.deriv_integral he0 $ (integralPS_iff_mv _).1 he) (by rw [hc, norm_one]) ?_
  rw [h1]
  intro n
  rw [coeff_C_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) $ h.deriv_integral n

theorem hon_shape (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    ∃ hh,
      HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh ∧
      DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2))) ∧
      coeff 1 hh = coeff (l ^ 2) e := by
  have hl0 := hF.prime.ne_zero
  have hσ := h.map hF
  obtain ⟨hc1, hH1⟩ := hom_desc hF h.Φ0 h.Φint h.Φ0 h.Φint h.A0 h.Aint h.A0 h.Aint
    (mulL_homCls h he0 he hlog) $ mulL_deriv h.toLawD he0 he hlog
  have hd1 :=
    hom_deriv hF.norm_l.le hσ.toLawD h.toLawD hH1 $ by
        refine hom_eigen hσ.A0 h.A0 hH1 ?_
        rw [hσ.coeff_one_A, h.coeff_one_A]
        exact h.a_ne
  obtain ⟨hc2, hH2⟩ := hom_desc hF hσ.Φ0 hσ.Φint h.Φ0 h.Φint hσ.A0 hσ.Aint h.A0 h.Aint hH1 hd1
  refine ⟨desc l $ desc l e, ?_, ?_, ?_⟩
  have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
    ext d
    simp
  have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
    ext d
    simp
  rwa [e1, e2]
  have hXs : PowerSeries.HasSubst $ (X : PowerSeries K) ^ l :=
    PowerSeries.HasSubst.of_constantCoeff_zero' $ by simp [hl0]
  have h3 := (divBy_expand_iff (l : K) l hl0 _).2 hc2
  rw [PowerSeries.subst_sub hXs, PowerSeries.subst_comp_subst_apply hXs hXs,
    PowerSeries.subst_pow hXs, PowerSeries.subst_X hXs, ← pow_mul, ← sq] at h3
  have h4 := divBy_add hc1 h3
  rwa [sub_add_sub_cancel] at h4
  rw [coeff_one_desc, desc, coeff_mk, sq]

theorem hon_level (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) : ‖coeff (l ^ 2) e‖ = 1 := by
  obtain ⟨hh, -, hc, -⟩ := hon_shape hF h he0 he hlog
  obtain ⟨i, hi, hi1⟩ := hlev
  by_cases hdvd : l ^ 2 ∣ i
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  rw [coeff_zero_eq_constantCoeff_apply, he0, norm_zero] at hi1
  exact absurd hi1 zero_ne_one
  rwa [← le_antisymm hi $ Nat.le_of_dvd hpos hdvd]
  have h1 := hc i
  rw [map_sub, coeff_subst_X_pow $ pow_ne_zero _ hF.prime.ne_zero, if_neg hdvd, sub_zero, hi1] at h1
  exact absurd h1 $ not_le.2 hF.norm_l

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem HD.map_frobenius_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map (σ.comp σ) lam) (MvPowerSeries.map (σ.comp σ) Φ)
      (PowerSeries.map (σ.comp σ) A) a := by
  have hτa : (σ.comp σ) a = a := h.a_sq
  have e := congrArg (PowerSeries.map $ σ.comp σ) h.Alog
  rw [map_mul, PowerSeries.map_C, hτa] at e
  have e2 := congrArg (MvPowerSeries.map $ σ.comp σ) h.log
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, h.a_ne, h.a_sq⟩
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, map_zero]
  rw [PowerSeries.coeff_map, h.lam1, map_one]
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
  exact (integralMv_iff_divBy_one Φ).mp h.Φint d
  have hX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero $ by simp
  unfold atX atY at e2 ⊢
  rw [PowerSeries.map_subst $ PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0, map_add,
    PowerSeries.map_subst $ hX 0, PowerSeries.map_subst $ hX 1, MvPowerSeries.map_X,
    MvPowerSeries.map_X] at e2
  exact e2
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, h.A0, map_zero]
  unfold IntegralPS
  intro n
  rw [PowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
  exact h.Aint n
  have e' : MvPowerSeries.map (σ.comp σ) (lam.subst A) = C a * PowerSeries.map (σ.comp σ) lam := e
  rwa [PowerSeries.map_subst $ PowerSeries.HasSubst.of_constantCoeff_zero' h.A0] at e'

theorem HD.map_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) :
    HD σ (PowerSeries.map ((σ.comp σ) ^ i) lam) (MvPowerSeries.map ((σ.comp σ) ^ i) Φ)
      (PowerSeries.map ((σ.comp σ) ^ i) A) a := by
  induction i with
  | zero =>
    simp only [pow_zero, RingHom.one_def, MvPowerSeries.map_id, PowerSeries.map_id, RingHom.id_apply]
    exact h
  | succ i ih =>
    simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
      RingHom.comp_apply]
    exact HD.map_frobenius_sq hF ih

theorem honF_subst_subst {ι κ : Type} (φ : PowerSeries K) {u : MvPowerSeries ι K}
    (hu : MvPowerSeries.constantCoeff u = 0) {b : ι → MvPowerSeries κ K}
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

theorem honF_integral_subst {f g : PowerSeries K} (hf : IntegralPS f) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) : IntegralPS $ f.subst g :=
  (integralPS_iff_mv _).mpr $ integralMv_subst hf hg0 $ (integralPS_iff_mv g).mp hg

theorem hon_mu (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e hh : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hh1 : HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh)
    (hh2 : DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a (lam.subst hh) ∧
      DivBy (l : K) (C (l : K) * lam - PowerSeries.subst ((X : PowerSeries K) ^ (l ^ 2)) (lam.subst hh : PowerSeries K)) ∧
      coeff 1 (lam.subst hh) = coeff 1 hh := by
  have hl := hF.prime
  have hl1 := hF.norm_l
  have hlam' := h.toLawD.deriv_integral
  have h' := h.map_frobenius_sq hF
  have Hh : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh1.g0
  have HΦ' : PowerSeries.HasSubst (MvPowerSeries.map (σ.comp σ) Φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h'.Φ0
  have hXq0 : constantCoeff ((X : PowerSeries K) ^ (l ^ 2)) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow (pow_ne_zero _ hl.ne_zero)]
  have hX0 : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (hX0 i)
  have hp0 : ∀ i, MvPowerSeries.constantCoeff (![atX hh, atY hh] i) = 0 := by
    intro i
    fin_cases i
    exact PowerSeries.constantCoeff_subst_eq_zero (hX0 0) hh hh1.g0
    exact PowerSeries.constantCoeff_subst_eq_zero (hX0 1) hh hh1.g0
  have Hp : MvPowerSeries.HasSubst ![atX hh, atY hh] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hp0
  refine ⟨⟨PowerSeries.constantCoeff_subst_eq_zero hh1.g0 lam h.lam0, ?_, ?_, ?_⟩, ?_, ?_⟩
  rw [derivative_subst Hh]
  exact integralPS_mul (honF_integral_subst hlam' hh1.g0 hh1.gInt) (integralPS_derivative hh1.gInt)
  have key := qls hl hl1 lam h.lam0 hlam' (hh.subst (MvPowerSeries.map (σ.comp σ) Φ))
    (Φ.subst ![atX hh, atY hh])
    (PowerSeries.constantCoeff_subst_eq_zero h'.Φ0 hh hh1.g0)
    (MvPowerSeries.constantCoeff_subst_eq_zero Hp hp0 h.Φ0)
    (integralMv_subst hh1.gInt h'.Φ0 h'.Φint) (integralMv_subst2 h.Φint hp0 (by
        intro i
        fin_cases i
        exact integralMv_subst hh1.gInt (hX0 0) (integralMv_X 0)
        exact integralMv_subst hh1.gInt (hX0 1) (integralMv_X 1))) hh1.add
  have ex : atX (lam.subst hh) = lam.subst (atX hh) :=
    PowerSeries.subst_comp_subst_apply Hh (HX 0) lam
  have ey : atY (lam.subst hh) = lam.subst (atY hh) :=
    PowerSeries.subst_comp_subst_apply Hh (HX 1) lam
  have ax : (atX lam).subst ![atX hh, atY hh] = lam.subst (atX hh) :=
    (honF_subst_subst lam (hX0 0) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
  have ay : (atY lam).subst ![atX hh, atY hh] = lam.subst (atY hh) :=
    (honF_subst_subst lam (hX0 1) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
  have e1 : lam.subst (Φ.subst ![atX hh, atY hh]) = atX (lam.subst hh) + atY (lam.subst hh) := by
    rw [ex, ey, ← honF_subst_subst lam h.Φ0 Hp, h.log, MvPowerSeries.subst_add Hp, ax, ay]
  rw [e1] at key
  rwa [PowerSeries.subst_comp_subst_apply Hh HΦ', sub_sub]
  have key := qls1 hl hl1 lam h.lam0 hlam' (hh.subst (PowerSeries.map (σ.comp σ) A))
    (A.subst hh) (PowerSeries.constantCoeff_subst_eq_zero h'.A0 hh hh1.g0)
    (PowerSeries.constantCoeff_subst_eq_zero hh1.g0 A h.A0)
    (honF_integral_subst hh1.gInt h'.A0 h'.Aint) (honF_integral_subst h.Aint hh1.g0 hh1.gInt) hh1.eig
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' h.A0) Hh, h.Alog, PowerSeries.subst_mul Hh,
    PowerSeries.subst_C] at key
  rwa [PowerSeries.subst_comp_subst_apply Hh (PowerSeries.HasSubst.of_constantCoeff_zero' h'.A0)]
  have key := qls1 hl hl1 lam h.lam0 hlam' e (hh.subst ((X : PowerSeries K) ^ (l ^ 2))) he0
    (PowerSeries.constantCoeff_subst_eq_zero hXq0 hh hh1.g0) he
    (honF_integral_subst hh1.gInt hXq0 (integralPS_pow integralPS_X _)) hh2
  rw [hlog] at key
  rwa [PowerSeries.subst_comp_subst_apply Hh (PowerSeries.HasSubst.of_constantCoeff_zero' hXq0)]
  rw [Formalism.LT.PadicP.coeff_one_subst lam hh h.lam0 hh1.g0, h.lam1, one_mul]

theorem lemmaQ_tw (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) {D : PowerSeries K}
    (hD : QCls l (MvPowerSeries.map ((σ.comp σ) ^ i) Φ) (PowerSeries.map ((σ.comp σ) ^ i) A) a D) :
    ∃ Dp,
      QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
        (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * PowerSeries.map ((σ.comp σ) ^ i) lam
        - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  obtain ⟨Dp, hDp, hdiv⟩ := lemmaQ hF (HD.map_sq hF h i) hD
  refine ⟨Dp, ?_, hdiv⟩
  simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
    RingHom.comp_apply]
  exact hDp

theorem hon_series (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : ℕ → K, ‖c 0‖ = 1 ∧ (∀ i, ‖c i‖ ≤ 1) ∧ ∀ N : ℕ, ∃ R : PowerSeries K,
      constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam).subst
              ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1)))) := by
  obtain ⟨hh, hhom, hdiv, hc1⟩ := hon_shape hF h he0 he hlog
  obtain ⟨hQ, hmod, hcoef⟩ := hon_mu hF h he0 he hlog hhom hdiv
  have hl0 := hF.prime.ne_zero
  let seq : (i : ℕ) → {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D} := fun i =>
    Nat.rec (motive := fun i => {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D}) ⟨lam.subst hh, by simpa using hQ⟩
      (fun i D => ⟨Classical.choose (lemmaQ_tw hF h (i + 1) D.2),
        (Classical.choose_spec $ lemmaQ_tw hF h (i + 1) D.2).1⟩) i
  have hstep : ∀ i, DivBy (l : K) $ (seq i).1 - C (coeff 1 (seq i).1) *
      PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam - (seq $ i + 1).1.subst ((X : PowerSeries K) ^ (l ^ 2)) :=
    fun i => (Classical.choose_spec $ lemmaQ_tw hF h (i + 1) (seq i).2).2

  have hsub : ∀ m, m ≠ 0 → PowerSeries.HasSubst ((X : PowerSeries K) ^ m) := fun m hm =>
    PowerSeries.HasSubst.of_constantCoeff_zero' $ by simp [hm]
  have hcomp : ∀ (f : PowerSeries K) (m q : ℕ), m ≠ 0 → q ≠ 0 →
      PowerSeries.subst ((X : PowerSeries K) ^ m) (f.subst ((X : PowerSeries K) ^ q) : PowerSeries K) =
        f.subst ((X : PowerSeries K) ^ (m * q)) := by
    intro f m q hm hq
    rw [PowerSeries.subst_comp_subst_apply (hsub q hq) $ hsub m hm]
    congr 1
    rw [← PowerSeries.coe_substAlgHom $ hsub m hm, map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X $ hsub m hm, ← pow_mul]
  refine ⟨fun i => coeff 1 (seq i).1, ?_, fun i => (seq i).2.norm_coeff_one,
    fun N => ⟨(seq N).1, (seq N).2.D0, ?_⟩⟩
  show ‖coeff 1 (lam.subst hh)‖ = 1
  rw [hcoef, hc1]
  exact hon_level hF h he0 he hlog hlev
  induction N with
  | zero =>
    simp [Finset.range_zero, Finset.sum_empty, sub_zero, zero_add, pow_one]
    exact hmod
  | succ N ih =>
    have hm : (l ^ 2) ^ (N + 1) ≠ 0 := pow_ne_zero _ $ pow_ne_zero _ hl0
    have h1 := (divBy_expand_iff (l : K) ((l ^ 2) ^ (N + 1)) hm _).2 $ hstep N
    rw [← PowerSeries.coe_substAlgHom $ hsub _ hm, map_sub, map_sub, ← PowerSeries.smul_eq_C_mul,
      map_smul, PowerSeries.smul_eq_C_mul, PowerSeries.coe_substAlgHom, hcomp _ _ _ hm $ pow_ne_zero _ hl0, ← pow_succ] at h1
    have := divBy_add ih h1
    convert this using 1
    simp [Finset.sum_range_succ]
    ring

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Regroup

variable {K : Type} [Field K]

theorem hon_regroup (τ : K →+* K) (π : K) (c t w : ℕ → K) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ m, M ≤ m → w m = 0) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c $ n - 1 - i)) :
    ∑ i ∈ Finset.range M, t i * (π * w i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * w (i + j + 1))
      = π * w 0 - (c 0 - π * t 1) * w 1 := by
  obtain ⟨K', rfl⟩ : ∃ K', M = K' + 1 := ⟨M - 1, by omega⟩

  have hS : ∑ i ∈ Finset.range (K' + 1), ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
      = ∑ n ∈ Finset.range (K' + 1), w (n + 1) * ∑ i ∈ Finset.range (n + 1), t i * (τ ^ i) (c $ n - i) := by
    have hA : ∀ i ∈ Finset.range (K' + 1),
        ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
          = ∑ j ∈ Finset.range (K' + 1 - i), t i * (τ ^ i) (c j) * w (i + j + 1) := by
      intro i _
      symm
      refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
        fun j _ hj => ?_
      simp only [Finset.mem_range, not_lt] at hj
      rw [hw _ $ by omega, mul_zero]
    rw [Finset.sum_congr rfl hA]
    have hflip := Finset.sum_range_diag_flip (K' + 1)
      fun i j => t i * (τ ^ i) (c j) * w (i + j + 1)
    beta_reduce at hflip
    rw [← hflip]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have e : i + (n - i) + 1 = n + 1 := by omega
    rw [e]
    ring
  have hsplit : ∀ i, t i * (π * w i - ∑ j ∈ Finset.range (K' + 1), (τ ^ i) (c j) * w (i + j + 1))
      = π * (t i * w i) - ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1) := by
    intro i
    rw [mul_sub, Finset.mul_sum]
    congr 1
    ring
    exact Finset.sum_congr rfl fun j _ => by ring
  have hF : ∀ n ∈ Finset.range K',
      w (n + 1 + 1) * ∑ i ∈ Finset.range (n + 1 + 1), t i * (τ ^ i) (c $ n + 1 - i)
        = π * (t (n + 1 + 1) * w (n + 1 + 1)) := by
    intro n _
    have h2 := ht (n + 1 + 1) $ by omega
    simp only [Nat.add_sub_cancel] at h2
    rw [← mul_assoc, h2]
    ring
  have hF0 : w (0 + 1) * ∑ i ∈ Finset.range (0 + 1), t i * (τ ^ i) (c $ 0 - i) = c 0 * w 1 := by
    simp [ht0] <;> ring
  have htel := Finset.sum_range_sub' (fun m => t (m + 1) * w (m + 1)) K'
  beta_reduce at htel
  rw [Finset.sum_sub_distrib, zero_add] at htel
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib, ← Finset.mul_sum, hS,
    Finset.sum_range_succ', Finset.sum_range_succ']
  try beta_reduce
  rw [Finset.sum_congr rfl hF, ← Finset.mul_sum, hF0, ht0]
  linear_combination π * htel - π * t (K' + 1) * hw _ le_rfl

end Regroup

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem hon_lt_sq_pow (hl : 2 ≤ l) (n : ℕ) : n < (l ^ 2) ^ n := by
  have h4 : 1 < l ^ 2 := by nlinarith
  first
  | exact Nat.lt_pow_self h4
  | exact Nat.lt_pow_self h4 n

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

theorem hon_series_coeff (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K)
    (h : ∀ N, ∃ R : PowerSeries K, constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1))))) (n : ℕ) :
    ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter fun i => (l ^ 2) ^ (i + 1) ∣ n,
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖ := by
  obtain ⟨R, hR0, hR⟩ := h n
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 $ by omega
  have hRn : coeff n (R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (n + 1)))) = 0 := by
    rw [coeff_subst_X_pow_eq_ite_dvd' R $ pow_ne_zero _ hq]
    split_ifs
    rw [Nat.div_eq_of_lt $ lt_of_lt_of_le (hon_lt_sq_pow hl n)
        $ Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq) $ Nat.le_succ n,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hR0]
    rfl
  have hsum : coeff n (∑ i ∈ Finset.range n, C (c i) *
        (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1))))
      = ∑ i ∈ (Finset.range n).filter fun i => (l ^ 2) ^ (i + 1) ∣ n,
          c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam) := by
    rw [map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_C_mul, coeff_subst_X_pow_eq_ite_dvd' _ $ pow_ne_zero _ hq]
    split_ifs
    rw [PowerSeries.coeff_map]
    rw [mul_zero]
  unfold DivBy at hR
  have hcoef := hR n
  rwa [map_sub, map_sub, PowerSeries.coeff_C_mul, hsum, hRn, sub_zero] at hcoef

def twC (l : ℕ) (τ : K →+* K) (lam : PowerSeries K) (n m : ℕ) : K :=
  if (l ^ 2) ^ m ∣ n then (τ ^ m) $ coeff (n / (l ^ 2) ^ m) lam else 0

theorem twC_zero (τ : K →+* K) (n : ℕ) : twC l τ lam n 0 = coeff n lam := by
  simp [twC]

theorem twC_one (τ : K →+* K) (n : ℕ) :
    twC l τ lam n 1 = if l ^ 2 ∣ n then τ $ coeff (n / l ^ 2) lam else 0 := by
  simp [twC]

theorem twC_eq_zero (hl : 2 ≤ l) (τ : K →+* K) (h0 : constantCoeff lam = 0) {n m : ℕ}
    (hnm : n ≤ m) : twC l τ lam n m = 0 := by
  unfold twC
  split_ifs with hd
  have hlt : n < (l ^ 2) ^ m := lt_of_le_of_lt hnm $ hon_lt_sq_pow hl m
  rw [Nat.div_eq_of_lt hlt, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  rfl

theorem twC_shift (τ : K →+* K) {n i : ℕ} (hd : (l ^ 2) ^ i ∣ n) (j : ℕ) :
    (τ ^ i) (twC l τ lam (n / (l ^ 2) ^ i) j) = twC l τ lam n (i + j) := by
  unfold twC
  simp [pow_add, RingHom.mul_def, RingHom.comp_apply, Nat.dvd_div_iff_mul_dvd hd,
    Nat.div_div_eq_div_mul]
  split_ifs <;> simp

theorem twC_of_not_dvd (τ : K →+* K) {n i : ℕ} (hd : ¬ (l ^ 2) ^ i ∣ n) (j : ℕ) :
    twC l τ lam n (i + j) = 0 := by
  unfold twC
  rw [if_neg]
  intro h
  exact hd $ dvd_trans (pow_dvd_pow _ $ Nat.le_add_right i j) h

theorem hon_norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hτ, ih]

theorem hon_coeff_unif (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K) (h0 : constantCoeff lam = 0)
    (E : ∀ n, ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter fun i => (l ^ 2) ^ (i + 1) ∣ n,
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖) {n M : ℕ} (hM : n ≤ M) :
    ‖(l : K) * coeff n lam - ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1)‖ ≤ ‖(l : K)‖ := by
  have h1 : ∑ i ∈ (Finset.range n).filter fun i => (l ^ 2) ^ (i + 1) ∣ n,
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)
      = ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold twC
    split_ifs <;> simp
  have h2 : ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1)
      = ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1) := by
    refine Finset.sum_subset (fun x hx => by simp [Finset.mem_range] at hx ⊢; omega)
      fun j _ hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [twC_eq_zero hl τ h0 $ by omega, mul_zero]
  rw [← h2, ← h1]
  exact E n

theorem hon_coeff_shift (hl : 2 ≤ l) (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (c : ℕ → K)
    (h0 : constantCoeff lam = 0)
    (E : ∀ n, ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter fun i => (l ^ 2) ^ (i + 1) ∣ n,
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖) {n M : ℕ} (hM : n ≤ M)
    (i : ℕ) :
    ‖(l : K) * twC l τ lam n i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * twC l τ lam n (i + j + 1)‖
      ≤ ‖(l : K)‖ := by
  by_cases hd : (l ^ 2) ^ i ∣ n
  have e1 : twC l τ lam n i = (τ ^ i) (coeff (n / (l ^ 2) ^ i) lam) := by
    rw [← twC_zero (l := l) τ $ n / (l ^ 2) ^ i, twC_shift τ hd 0, add_zero]
  have e2 : ∀ j, twC l τ lam n (i + j + 1) = (τ ^ i) (twC l τ lam (n / (l ^ 2) ^ i) $ j + 1) := by
    intro j
    rw [twC_shift τ hd $ j + 1, add_assoc]
  have hn' : n / (l ^ 2) ^ i ≤ M := le_trans (Nat.div_le_self _ _) hM
  have key := hon_coeff_unif hl τ c h0 E hn'
  rw [← hon_norm_pow_apply τ hτ i] at key
  convert key using 2
  rw [map_sub, map_mul, map_natCast, e1, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, e2]
  have e1 : twC l τ lam n i = 0 := by simpa using twC_of_not_dvd (lam := lam) τ hd 0
  have e2 : ∀ j, twC l τ lam n (i + j + 1) = 0 := fun j => by
    rw [add_assoc]
    exact twC_of_not_dvd τ hd $ j + 1
  simp only [e1, e2, mul_zero, Finset.sum_const_zero, sub_zero, norm_zero]
  exact norm_nonneg _

theorem hon_main (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : K, ‖c‖ = 1 ∧ IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl := hF.prime.two_le
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr $ by omega
  obtain ⟨c, hc0, hc, hN⟩ := hon_series hF h he0 he hlog hlev
  have hτ : ∀ x, ‖(σ.comp σ) x‖ = ‖x‖ := fun x => (hF.isom _).trans $ hF.isom x
  obtain ⟨t, ht0, htn, ht⟩ := twisted_division (σ.comp σ) hτ (l : K) hF.norm_l c hc0 hc
  have hlt : ‖(l : K) * t 1‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) $ htn 1).trans_lt hF.norm_l
  refine ⟨c 0 - (l : K) * t 1, ?_, fun n => ?_⟩
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by rw [norm_neg, hc0]; exact hlt.ne'), norm_neg, hc0]
  exact max_eq_left hlt.le
  have key := hon_regroup (σ.comp σ) (l : K) c t (twC l (σ.comp σ) lam n) (n + 1) (by omega)
    (fun m hm => twC_eq_zero hl _ h.lam0 $ by omega) ht0 ht
  have bd : ‖(l : K) * twC l (σ.comp σ) lam n 0
      - (c 0 - (l : K) * t 1) * twC l (σ.comp σ) lam n 1‖ ≤ ‖(l : K)‖ := by
    rw [← key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul]
    exact (mul_le_mul (htn i) (hon_coeff_shift hl _ hτ c h.lam0 (hon_series_coeff hl (σ.comp σ) c hN) (Nat.le_succ n) i)
      (norm_nonneg _) zero_le_one).trans (one_mul _).le
  rw [twC_zero, twC_one] at bd
  rw [map_sub, coeff_smul, coeff_subst_X_pow $ pow_ne_zero _ $ by omega, smul_eq_mul]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have : coeff n lam - (c 0 - (l : K) * t 1) / (l : K) *
      (if l ^ 2 ∣ n then coeff (n / l ^ 2) $ PowerSeries.map (σ.comp σ) lam else 0)
      = ((l : K) * coeff n lam - (c 0 - (l : K) * t 1) *
        (if l ^ 2 ∣ n then (σ.comp σ) $ coeff (n / l ^ 2) lam else 0)) / (l : K) := by
    rw [coeff_map]
    field_simp
  rw [this, norm_div]
  exact div_le_one_of_le₀ bd $ norm_nonneg _

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem tch_of_integral (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) : ∃ ξ ∈ Tch l, ‖δ - ξ‖ < 1 := by
  have hZ := KE.isIntegral_int_of_rmu (l := l) δ hδ
  obtain ⟨f, hf, hfr⟩ := KE.frob_fix_of_integral l (Fact.out : l.Prime) (by
      rw [norm_l_Cl (l := l)]
      exact inv_lt_one_of_one_lt₀ $ by exact_mod_cast (Fact.out : l.Prime).one_lt) δ hZ
  obtain ⟨ξ, hξ, hd⟩ := tch_near (l := l) δ (KE.norm_le_one_of_integral_int δ hZ) f hf _ hfr le_rfl
  exact ⟨ξ, hξ, lt_of_le_of_lt hd hfr⟩

open Polynomial in
theorem kur_resClosed : ResClosed (MaximalUnramifiedExtension l) l := by
  classical
  intro P hPm hPd hPc
  choose g hgT hgd using fun i => kur_rep (l := l) (P.coeff i).2 $ hPc i
  have hgR : ∀ i, g i ∈ Rmu l := fun i => KE.tch_mem_rmu (l := l) $ hgT i
  have hQ'deg : (∑ i : Fin P.natDegree, C (⟨g i, hgR i⟩ : Rmu l) * X ^ (i : ℕ)).degree
      < (P.natDegree : WithBot ℕ) := degree_sum_fin_lt _
  let Q' :=
    X ^ P.natDegree + ∑ i : Fin P.natDegree, C (⟨g i, hgR i⟩ : Rmu l) * X ^ (i : ℕ)
  have hQ'm := monic_X_pow_add hQ'deg
  let Qc := Q'.map $ algebraMap (Rmu l) ℂ_[l]
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_root Qc $ by
      have hX : (X ^ P.natDegree : Polynomial $ Rmu l).degree = P.natDegree := degree_X_pow _
      have hQ'd : Q'.degree = P.natDegree := by
        rw [← hX]
        exact degree_add_eq_left_of_degree_lt $ hX ▸ hQ'deg
      rw [hQ'm.degree_map, hQ'd]
      first | exact_mod_cast hPd.ne' | simpa using hPd.ne'
  have hδint : IsIntegral (Rmu l) δ := ⟨Q', hQ'm, by rw [← eval_map]; exact hδ⟩
  have hQeval : ∀ y,
      Qc.eval y = y ^ P.natDegree + ∑ i : Fin P.natDegree, g i * y ^ (i : ℕ) := by
    intro y
    simp [Qc, Q', eval_map, eval₂_finset_sum] <;> rfl
  obtain ⟨ξ, hξT, hξd⟩ := tch_of_integral l δ hδint
  have hξ1 : ‖ξ‖ ≤ 1 := tch_norm_le (l := l) hξT
  have hξK : ξ ∈ MaximalUnramifiedExtension l := tch_mem_kur (l := l) hξT
  have hδ1 : ‖δ‖ ≤ 1 :=
    KE.norm_le_one_of_integral (fun r => rmu_norm_le (l := l) r.2) δ hδint
  have hQc : ∀ i, ‖Qc.coeff i‖ ≤ 1 := by
    intro i
    rw [coeff_map]
    exact rmu_norm_le (l := l) (Q'.coeff i).2
  set F : ℂ_[l] := ξ ^ P.natDegree + ∑ i : Fin P.natDegree, g i * ξ ^ (i : ℕ) with hF
  have hFK : F ∈ MaximalUnramifiedExtension l :=
    add_mem (pow_mem hξK _)
      $ sum_mem fun i _ => mul_mem (tch_mem_kur (l := l) $ hgT i) $ pow_mem hξK _
  have hFl := kur_discrete (l := l) hFK $ by
      have h := KE.norm_eval_sub_eval_le Qc hQc hξ1 hδ1
      rw [hQeval ξ, hδ.eq_zero, sub_zero, norm_sub_rev] at h
      exact lt_of_le_of_lt h hξd

  have hsum : ∀ s (f : Fin P.natDegree → ℂ_[l]),
      (∀ i ∈ s, ‖f i‖ ≤ ‖(l : ℂ_[l])‖) → ‖∑ i ∈ s, f i‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro s f
    refine Finset.induction_on s (fun _ => by simp) ?_
    intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      $ max_le (h a $ Finset.mem_insert_self a s) $ ih fun i hi => h i $ Finset.mem_insert_of_mem hi
  have hS : ‖∑ i : Fin P.natDegree, (((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - g i) * ξ ^ (i : ℕ)‖
      ≤ ‖(l : ℂ_[l])‖ := by
    apply hsum
    intro i _
    rw [norm_mul, norm_pow]
    calc ‖((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - g i‖ * ‖ξ‖ ^ (i : ℕ) ≤ ‖(l : ℂ_[l])‖ * 1 :=
          mul_le_mul (hgd i) (pow_le_one₀ (norm_nonneg _) hξ1) (by positivity) $ norm_nonneg _
      _ = ‖(l : ℂ_[l])‖ := mul_one _
  use ⟨ξ, hξK⟩, tch_norm_le (l := l) hξT
  have hPx : ((P.eval (⟨ξ, hξK⟩ : MaximalUnramifiedExtension l) : MaximalUnramifiedExtension l) : ℂ_[l]) =
      ξ ^ P.natDegree + ∑ i : Fin P.natDegree, ((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) * ξ ^ (i : ℕ) := by
    conv_lhs => rw [hPm.as_sum]
    simp [eval_finset_sum, Finset.sum_range]
  have hlK : ((l : MaximalUnramifiedExtension l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  show ‖((P.eval (⟨ξ, hξK⟩ : MaximalUnramifiedExtension l) : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ ‖((l : MaximalUnramifiedExtension l) : ℂ_[l])‖
  rw [hPx, hlK]
  have hsplit : ξ ^ P.natDegree + ∑ i : Fin P.natDegree, ((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) * ξ ^ (i : ℕ)
      = (∑ i : Fin P.natDegree, (((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - g i) * ξ ^ (i : ℕ)) + F := by
    rw [hF]
    simp [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans $ max_le hS hFl

end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem integral_of_map_kur {l : ℕ} [Fact l.Prime] {f : PowerSeries (MaximalUnramifiedExtension l)}
    (h : IntegralPS $ PowerSeries.map (MaximalUnramifiedExtension l).subtype f) : IntegralPS f := fun n => by
  have := h n
  rwa [PowerSeries.coeff_map] at this

theorem cm3 : CM3 := by
  intro d L _hsq hd hCM l _ hl hld hin ι g2 g3 hg
  obtain ⟨hg2, hg3, hn2, hn3, -, -⟩ := id hg
  have : CompleteSpace $ MaximalUnramifiedExtension l := kur_complete l
  obtain ⟨σ, hσ⟩ := kurFrob l
  obtain ⟨-, ha1, ha', haσ⟩ := kur_quad l d hd (by omega) hld hin _ $ by
      have := congrArg ι $ omegaK_quad d hd
      simpa using this
  have haσ' := haσ σ hσ
  have hlaw := curve_law (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ hn2 hn3 $ by
      have := norm_natCast_of_coprime (K := MaximalUnramifiedExtension l) hσ.prime hσ.norm_l 2
        (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
      simpa using this
  have hD : HD σ (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) _
      ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
        (C (⟨ι $ omegaK d, ha'⟩ : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))
      ⟨ι $ omegaK d, ha'⟩ :=
    { toLawD := hlaw
      A0 := mult_const _ _ _
      Aint := integral_of_map_kur $ by
        rw [mult_map]
        exact end_integral d L hd hCM l hl hld hin ι g2 g3 hg
      Alog := mult_log _ _ _
      a_ne := by
        rw [haσ']
        have : ‖((1 - (⟨ι $ omegaK d, ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι $ omegaK d, ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 := by
          have e : ((1 - (⟨ι $ omegaK d, ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι $ omegaK d, ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])
              = 1 - 2 * ι (omegaK d) := by
            push_cast
            ring
          rwa [e]
        exact this
      a_sq := by
        rw [haσ', map_sub, map_one, haσ']
        ring }
  have hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))‖ = 1 := by
    obtain ⟨i, hi, hu⟩ := level_le L l hl ι g2 g3 hg
    use i, hi
    have hm := mult_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ ((l : ℕ) : MaximalUnramifiedExtension l)
    have hl' : (MaximalUnramifiedExtension l).subtype ((l : ℕ) : MaximalUnramifiedExtension l) = ((l : ℕ) : ℂ_[l]) := map_natCast _ _
    rw [hl'] at hm
    have hc := congrArg (coeff i) hm
    rw [PowerSeries.coeff_map] at hc
    have : ‖(MaximalUnramifiedExtension l).subtype (coeff i $ (uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))‖ = 1 := by
      rwa [hc]
    exact this
  obtain ⟨c, hc, hT⟩ := hon_main hσ hD (mult_const _ _ _) (by
      obtain ⟨e', h0, hint, hlog⟩ := mulN_integral hlaw l
      rw [← mult_unique _ _ _ e' h0 hlog]
      exact hint) (mult_log _ _ _) hlev
  obtain ⟨ε, hε, hcε⟩ := lang_semilinear hσ (kur_resClosed l) c hc
  have hfin := fin_integral hσ (uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)
    (lgS_const _ _) (lgS_coeff_one _ _) (uSer_const _ _) (uSer_subst_lgS _ _) c ε hc hε hcε hT
  refine ⟨ε, ε.2, hε, fun n => ?_⟩
  have hc' := congrArg (coeff n) $ lt_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ l (by omega) ε
  rw [PowerSeries.coeff_map] at hc'
  have hc'' : coeff n ((uSer g2 g3).subst (C (ε : ℂ_[l]) * ltLog ℂ_[l] l))
      = (MaximalUnramifiedExtension l).subtype (coeff n $ (uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
          (C ε * ltLog (MaximalUnramifiedExtension l) l)) := hc'.symm
  rw [hc'']
  constructor
  exact SetLike.coe_mem _
  exact hfin n
end ReciprocityTheory.ChartRestriction.L1
end
section
namespace ReciprocityTheory.ChartRestriction.L1

theorem cmIntegralityThree : Formalism.L2.Th1.CM.CM3 := cm3

end ReciprocityTheory.ChartRestriction.L1
end
end
