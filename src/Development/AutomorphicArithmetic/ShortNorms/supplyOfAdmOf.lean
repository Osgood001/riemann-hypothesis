module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AutomorphicArithmetic.CharacterBoxes.Imports
public import Development.AutomorphicArithmetic.CharacterBoxes.WinPairs
public import Development.AutomorphicArithmetic.CharacterBoxes.FieldChi
public import Development.AutomorphicArithmetic.CharacterBoxes.IsChiField
public import Development.AutomorphicArithmetic.CharacterBoxes.BoundedTw
public import Development.AutomorphicArithmetic.CharacterBoxes.PairHyp
public import Development.AutomorphicArithmetic.CharacterBoxes.EventuallyRankLeRpowOfLtOneDivFiftytwo
public import Development.AutomorphicArithmetic.MeanSquareBounds.pairEx

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

namespace UpperTheory.Top

/-- The arithmetic tests need only cover those epsilons at which the host request is imposed. -/
def RankWindowsOn (ψ : PChar) (P : ℝ → Prop) (w : ℝ) : Prop :=
  ∃ cut : ℝ → ℝ → ℝ,
    (∀ eps : ℝ, 0 < eps → eps < 1 / 52 → P eps → JointWindowAtWidth ψ eps w (cut eps)) ∧
    ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → P eps →
      ∀ k : ℝ, 1 ≤ k → k ^ (2 + 8 * eps) ≤ Nat.card (Subgroup.zpowers ψ.χ) →
        ∃ M : ℝ, ∀ x ≥ M, 10708 * (k * x) ^ rankExponent eps ≤ cut eps x

/-- At every admissible epsilon, the supplied window depths cover the actual host ranks
after rescaling by the order of the character field. -/
def RankWindowsAtWidth (ψ : PChar) (δ w : ℝ) : Prop :=
  ∃ cut : ℝ → ℝ → ℝ, JointVWinBelowWidth ψ δ w cut ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → eps < δ →
    ∀ k : ℝ, 1 ≤ k → k ^ (2 + 8 * eps) ≤ Nat.card (Subgroup.zpowers ψ.χ) →
      ∃ M : ℝ, ∀ x ≥ M, 10708 * (k * x) ^ rankExponent eps ≤ cut eps x

/-- The square-window specialization. -/
def RankWindowsAt (ψ : PChar) (δ : ℝ) : Prop := RankWindowsAtWidth ψ δ 2

/-- A fixed rescaling and a positive leading coefficient can be absorbed by any strict exponent gap. -/
theorem eventually_scaled_rpow_le {a b C D k : ℝ} (hab : a < b) (hk : 0 ≤ k) (hD : 0 < D) :
    ∃ M : ℝ, ∀ x ≥ M, C * (k * x) ^ a ≤ D * x ^ b := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop (C * k ^ a / D)).and
      (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨M, fun x hx => ?_⟩
  obtain ⟨h, hx₁⟩ := hM x hx
  have hx₀ := zero_lt_one.trans_le hx₁
  rw [Real.mul_rpow hk hx₀.le, ← mul_assoc]
  calc C * k ^ a * x ^ a ≤ (x ^ (b - a) * D) * x ^ a :=
         mul_le_mul_of_nonneg_right ((div_le_iff₀ hD).mp h) (Real.rpow_nonneg hx₀.le _)
       _ = D * x ^ b := by rw [mul_comm _ D, mul_assoc, ← Real.rpow_add hx₀, sub_add_cancel]

/-- An arbitrarily small positive multiplier suffices above the fixed-epsilon exponent. -/
theorem RankWindowsOn.of_power {ψ : PChar} {P : ℝ → Prop} {w : ℝ} {C b : ℝ → ℝ}
    (hV : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → P eps → JointWindowAtWidth ψ eps w (fun x => C eps * x ^ b eps))
    (h : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → P eps → 0 < C eps ∧ rankExponent eps < b eps) :
    RankWindowsOn ψ P w := by
  refine ⟨_, hV, fun eps he he' hsmall k hk _ => ?_⟩
  obtain ⟨hC, hb⟩ := h eps he he' hsmall
  exact eventually_scaled_rpow_le hb (zero_le_one.trans hk) hC

theorem RankWindowsAtWidth.of_power {ψ : PChar} {δ w : ℝ} {C b : ℝ → ℝ}
    (hV : JointVWinBelowWidth ψ δ w (fun eps x => C eps * x ^ b eps))
    (h : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → eps < δ → 0 < C eps ∧ rankExponent eps < b eps) :
    RankWindowsAtWidth ψ δ w :=
  RankWindowsOn.of_power hV h

theorem RankWindowsAt.of_power {ψ : PChar} {δ : ℝ} {C b : ℝ → ℝ}
    (hV : JointVWinBelow ψ δ (fun eps x => C eps * x ^ b eps))
    (h : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → eps < δ → 0 < C eps ∧ rankExponent eps < b eps) :
    RankWindowsAt ψ δ :=
  RankWindowsAtWidth.of_power hV h

/-- The host bound for all of the construction's admissible epsilons. -/
abbrev RankWindows (ψ : PChar) : Prop := RankWindowsAt ψ (1 / 52)

theorem RankWindows.of_power {ψ : PChar} {C b : ℝ → ℝ}
    (hV : JointVWinFor ψ (fun eps x => C eps * x ^ b eps))
    (h : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → 0 < C eps ∧ rankExponent eps < b eps) :
    RankWindows ψ :=
  RankWindowsAt.of_power (fun eps he he' _ => hV eps he he') (fun eps he he' _ => h eps he he')

/-- The field-order factor in the rank cutoff after rescaling a character window. -/
noncomputable def fieldRankCoeff (ψ : PChar) (eps : ℝ) : ℝ :=
  10708 * (Nat.card (Subgroup.zpowers ψ.χ) : ℝ) ^ (rankExponent eps / (2 + 8 * eps))

/-- At the fixed-epsilon exponent, retain the character's field-order multiplier. -/
theorem RankWindowsOn.of_critical {ψ : PChar} {P : ℝ → Prop} {w : ℝ}
    (hV : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → P eps →
      JointWindowAtWidth ψ eps w (fun x => fieldRankCoeff ψ eps * x ^ rankExponent eps)) :
    RankWindowsOn ψ P w := by
  refine ⟨_, hV, fun eps he _ _ k hk hc => ⟨0, fun x hx => ?_⟩⟩
  have hk₀ : 0 ≤ k := zero_le_one.trans hk
  have hd : 0 < 2 + 8 * eps := by positivity
  have he₀ : 0 ≤ rankExponent eps / (2 + 8 * eps) := by unfold rankExponent; positivity
  have hle := Real.rpow_le_rpow (Real.rpow_nonneg hk₀ _) hc he₀
  rw [← Real.rpow_mul hk₀, show (2 + 8 * eps) * (rankExponent eps / (2 + 8 * eps)) =
    rankExponent eps by field_simp] at hle
  rw [Real.mul_rpow hk₀ hx, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num)) (Real.rpow_nonneg hx _)

theorem RankWindows.of_critical {ψ : PChar}
    (hV : JointVWinFor ψ (fun eps x =>
      10708 * (Nat.card (Subgroup.zpowers ψ.χ) : ℝ) ^ (rankExponent eps / (2 + 8 * eps)) *
        x ^ rankExponent eps)) : RankWindows ψ :=
  RankWindowsOn.of_critical fun eps he he' _ => hV eps he he'

/-- The interval of admissible epsilons is open, so coefficient one works at its uniform endpoint. -/
theorem RankWindows.of_uniform {ψ : PChar} {C : ℝ → ℝ}
    (hV : JointVWinFor ψ (fun eps x => C eps * x ^ rankExponent (1 / 52)))
    (hC : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → 0 < C eps) : RankWindows ψ :=
  .of_power hV fun eps he he' => ⟨hC eps he he', by unfold rankExponent; linarith⟩

theorem CofinalVWinAt.rankWindows {ψ : PChar} (hV : CofinalVWinAt ψ 401) : RankWindows ψ := by
  apply RankWindows.of_power (C := fun _ => 1) (b := fun _ => 401)
  · simpa using CofinalVWinFor.toJoint hV QH.pairEx
  · intro eps _ he'
    constructor
    · norm_num
    · unfold rankExponent
      linarith

/-- Any fixed power above the limit as epsilon tends to zero suffices. -/
theorem RankWindowsAtWidth.of_limiting_power {ψ : PChar} {δ b w : ℝ} {C : ℝ → ℝ}
    (hδ : 0 < δ) (hb : 797 / 2 < b)
    (hV : JointVWinBelowWidth ψ δ w (fun eps x => C eps * x ^ b))
    (hC : ∀ eps : ℝ, 0 < eps → eps < δ → 0 < C eps) :
    ∃ η > 0, RankWindowsAtWidth ψ η w := by
  let η := min δ ((b - 797 / 2) / (929 / 16))
  have hη : 0 < η := lt_min hδ (div_pos (sub_pos.mpr hb) (by norm_num))
  refine ⟨η, hη, RankWindowsAtWidth.of_power
    (fun e he he' hh => hV e he he' (hh.trans_le (min_le_left _ _))) ?_⟩
  intro eps he _ hsmall
  have hlim := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 929 / 16)).mp
    (hsmall.trans_le (min_le_right _ _))
  exact ⟨hC eps he (hsmall.trans_le (min_le_left _ _)), by unfold rankExponent; linarith⟩

theorem RankWindowsAt.of_limiting_power {ψ : PChar} {δ b : ℝ} {C : ℝ → ℝ}
    (hδ : 0 < δ) (hb : 797 / 2 < b)
    (hV : JointVWinBelow ψ δ (fun eps x => C eps * x ^ b))
    (hC : ∀ eps : ℝ, 0 < eps → eps < δ → 0 < C eps) :
    ∃ η > 0, RankWindowsAt ψ η :=
  RankWindowsAtWidth.of_limiting_power hδ hb hV hC

end UpperTheory.Top

local macro "HostSupply" : term =>
  `((∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C0 → ∃ CT2 C8 c6 Cb x0 : ℝ, C0 ≤ C8 ∧ 0 < c6 ∧ 0 < Cb ∧
      ∀ (s : Scale) (R : Ranks) (H0 : HostAx R.toFrame) (M : ℕ) (Y : ℝ), s.eps = eps → x0 ≤ s.x → RankVal s R →
        s.J ≤ C0 → (R.o : ℝ) ≤ C0 → (H0.QS : ℝ) ≤ C0 * R.n → 0 < M → (M : ℝ) ≤ C0 → H0.QS ∣ Nat.lcm (2 ^ (R.e + 2)) M →
        PairWin s Y → PairGood M eps Y s.x H0.q H0.d → FieldRows H0.toHostRaw ⌊Y ^ (eps / 5)⌋₊ → admitted R H0 →
        ∃ (H : Host R) (q0 : ℕ), H.toHostAx = H0 ∧ H.CT2 = CT2 ∧ HostGood s C8 4 c6 Cb H q0 ∧
          R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps))))

local macro "AdmitsRanks(" ψ:term ")" : term =>
  `((∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (φ : Frame) (H0 : HostAx φ), s.eps = eps → x0 ≤ s.x →
        s.x ^ (2 + 8 * eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * eps) → φ.o = (Level.cyc $ψ).o → KerChi $ψ H0.toHostRaw →
        ∃ (R : Ranks) (h : R.toFrame = φ), RankVal s R ∧ admitted R (h ▸ H0)))

theorem UpperTheory.T3.supplyOfAdmOfRankWindowsOn {P : ℝ → Prop} {w la : ℝ} (hla : 1 < la) (hlw : la < w) :
    HostSupply → ∀ ψ : PChar, RankWindowsOn ψ P w →
      AdmitsRanks(ψ) →
      HostExW la (fun _ s R H _ => P s.eps → EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧ VVle H.E R.t (Real.sqrt s.b)) := by
  classical
  intro hSup ψ hV hAdm eps heps heps'
  have := ψ.ne
  have hN0 : 0 < ψ.N := Nat.pos_of_ne_zero (NeZero.ne _)
  have heps0 : eps ≠ 0 := heps.ne'
  obtain ⟨cut, hwinV, hdepth⟩ := hV
  obtain ⟨c, e0, hc, hcOrder, hF⟩ := UpperTheory.Top.fieldChi_bounded ψ
  let need := fun x : ℝ => if P eps then 10708 * x ^ rankExponent eps else 0
  have hw : JointWindowAtWidth ψ eps w (fun x => if P eps then cut eps x else 0) := by
    by_cases hp : P eps
    · simpa [hp] using hwinV eps heps heps' hp
    · simpa [hp] using jointWindowAtWidth_zero ψ eps w heps heps' (hla.trans hlw) QH.pairEx
  obtain ⟨J, hJ, hwin⟩ := winPairsForWidth ψ eps c w la _ need heps (by exact_mod_cast hc)
    hla hlw hw (by
      intro k hk hkc
      by_cases hsmall : P eps
      · simpa [need, hsmall] using
          hdepth eps heps heps' hsmall k hk (hkc.trans_le (by exact_mod_cast hcOrder))
      · exact ⟨0, fun x _ => by simp [need, hsmall]⟩)
  obtain ⟨C0, hC1, hCJ, hCo, hCN⟩ : ∃ C0 : ℝ, 1 ≤ C0 ∧ J ≤ C0 ∧ ((Level.cyc ψ).o : ℝ) ≤ C0 ∧
      8 * (ψ.N : ℝ) ≤ C0 :=
    by
      have h1 : (0 : ℝ) ≤ ((Level.cyc ψ).o : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (ψ.N : ℝ) := Nat.cast_nonneg _
      exact ⟨J + ((Level.cyc ψ).o : ℝ) + 8 * (ψ.N : ℝ), by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨CT2, C8, c6, Cb, x0A, hC8, hc6, hCb, hA⟩ := hSup eps C0 heps heps' hC1
  obtain ⟨x0B, hB⟩ := hAdm eps heps heps'
  obtain ⟨K, hK5, hK4⟩ : ∃ K : ℝ, 5 ≤ K ∧ 4 * (ψ.N : ℝ) ≤ K :=
    by
      have h2 : (0 : ℝ) ≤ (ψ.N : ℝ) := Nat.cast_nonneg _
      exact ⟨5 + 4 * (ψ.N : ℝ), by linarith, by linarith⟩
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨A, hA0, hAK⟩ : ∃ A : ℝ, 0 ≤ A ∧ A ^ (eps / 5) = K := by
    refine ⟨K ^ (5 / eps), Real.rpow_nonneg hK0 _, ?_⟩
    rw [← Real.rpow_mul hK0, show 5 / eps * (eps / 5) = (1 : ℝ) by field_simp, Real.rpow_one]
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hAJ0 : 0 ≤ A ^ J := Real.rpow_nonneg hA0 _
  obtain ⟨x1, h1A, h1B, h1J, h1c⟩ : ∃ x1 : ℝ, x0A ≤ x1 ∧ x0B ≤ x1 ∧ A ^ J ≤ x1 ∧
      (c : ℝ) * 2 ^ e0 < x1 := by
    have h2 : (0 : ℝ) ≤ (c : ℝ) * 2 ^ e0 := by positivity
    refine ⟨|x0A| + |x0B| + A ^ J + (c : ℝ) * 2 ^ e0 + 1, ?_, ?_, ?_, ?_⟩ <;>
      linarith [le_abs_self x0A, le_abs_self x0B, abs_nonneg x0A, abs_nonneg x0B]
  refine ⟨CT2, C8, 4, c6, Cb, x1, le_trans hC1 hC8, by norm_num, hc6, hCb, ?_⟩
  refine ⟨⟨J, hJ, {x | ∃ Y q d e, WinDatumAt ψ eps J c x Y q d e ⌊need x⌋₊}, hwin⟩, ?_⟩
  rintro s hs hx ⟨hsJ, Y, q, d, e, hW⟩
  have hx1 : 1 < s.x := s.one_lt_alt
  have hJ0 : 0 < J := by linarith
  have hYA : A ≤ Y := by
    calc A = (A ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hA0 hJ0.ne']
      _ ≤ s.x ^ (1 / J) := Real.rpow_le_rpow hAJ0 (h1J.trans hx) (div_nonneg zero_le_one hJ0.le)
      _ ≤ Y := hW.lo
  have hY0 : 0 ≤ Y := hA0.trans hYA
  have hYK : K ≤ Y ^ (eps / 5) := by
    rw [← hAK]
    exact Real.rpow_le_rpow hA0 hYA (by positivity)
  obtain ⟨hHyp, hjac, -⟩ := UpperTheory.Top.pairHyp eps Y q d hW.good.pair
  have hq3 : q ≠ 3 := by
    intro hq
    have h1 := hW.good.pair.q_lo
    rw [hq] at h1
    push_cast at h1
    have h2 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    linarith
  have he : e ≥ e0 := by
    by_contra hlt
    push Not at hlt
    have h1 : (2 : ℝ) ^ e ≤ 2 ^ e0 := pow_le_pow_right₀ (by norm_num) hlt.le
    have h2 : s.x ≤ s.x ^ (2 + 8 * eps) := by
      calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h3 := hW.n_lo
    linarith [mul_le_mul_of_nonneg_left h1 hc0]
  have h4N : 4 * ψ.N ≤ ⌊Y ^ (eps / 5)⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hjacb : ∀ p : ℕ, Nat.Prime p → p ≠ 2 → p ≤ ⌊Y ^ (eps / 5)⌋₊ → jacobiSym (-(d : ℤ)) p = 1 :=
    fun p hp hp2 hpb => hjac p hp hp2 ((Nat.cast_le.2 hpb).trans (Nat.floor_le (Real.rpow_nonneg hY0 _)))
  obtain ⟨φ, H0, hφe, hφord, hHq, hHd, hφo, hFR, hQSdvd, hQSle, hkept, hps, hker, htw⟩ :=
    hF e he q d ⌊Y ^ (eps / 5)⌋₊ hHyp hq3 hW.good.coprime h4N hjacb
  obtain ⟨R, h, hRV, hAdmR⟩ := hB s φ H0 hs (h1B.trans hx)
    (by rw [hφord]; push_cast; exact hW.n_lo) (by rw [hφord]; push_cast; exact hW.n_up) hφo hker
  subst h
  have hnlo := hRV.n_lo
  rw [hs] at hnlo
  have hQS : (H0.QS : ℝ) ≤ C0 * R.n := by
    have hq' : (H0.QS : ℝ) ≤ 4 * ψ.N * R.toFrame.ord := by exact_mod_cast hQSle
    have hord : (R.toFrame.ord : ℝ) = c * 2 ^ e := by rw [hφord]; push_cast; ring
    have hn : (0 : ℝ) ≤ R.n := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ ψ.N := Nat.cast_nonneg _
    rw [hord] at hq'
    have h5 := hW.n_up
    nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 4 * ψ.N),
      mul_le_mul_of_nonneg_left hnlo (by positivity : (0 : ℝ) ≤ 8 * ψ.N),
      mul_le_mul_of_nonneg_right hCN hn]
  obtain ⟨H, q0, hH, hCT, hGood, hSh⟩ := hA s R H0 ψ.N Y hs (h1A.trans hx) hRV
    (by rw [hsJ]; exact hCJ) (by rw [hφo]; exact hCo) hQS hN0
    (by have : (0 : ℝ) ≤ ψ.N := Nat.cast_nonneg _; linarith)
    (by rw [hφe]; exact hQSdvd) ⟨by rw [hsJ]; exact hW.lo, hW.up⟩
    (by rw [hHq, hHd]; exact hW.good) hFR hAdmR
  subst hH
  refine ⟨R, H, q0, hRV, hCT, hGood, fun hsmall => ⟨?_, ?_⟩⟩
  · have hprime : ∀ l : ℕ, Nat.Prime l → l ∣ H.QS → l ∣ 2 * ψ.N := by
      intro l hl hlQ
      have h1 : l ∣ 2 ^ (e + 2) * ψ.N := hlQ.trans (hQSdvd.trans (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))
      rcases (Nat.Prime.dvd_mul hl).1 h1 with h2 | h2
      · have h3 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h2)
        subst h3
        exact dvd_mul_right 2 _
      · exact dvd_mul_of_dvd_right h2 2
    have hbd := UpperTheory.Top.boundedTw ψ R.toFrame H.toHostRaw eps Y s.x heps hx1.le hW.up htw hker.1 hprime
      (by rw [hHq, hHd]; exact hW.good)
    rw [hs] at hSh ⊢
    exact ⟨hφo, hkept, hps, hSh, hbd.1, hbd.2⟩
  · have hCF := UpperTheory.Top.isChiField ψ R.toFrame H.toHostRaw hker
    rw [hφe, hHq, hHd] at hCF
    have hv := hW.bound H.E hCF
    refine hv.mono ?_ (le_of_eq ?_)
    · apply Nat.le_floor
      simpa [need, rankExponent, hs, (hs ▸ hsmall : P eps)] using rank_window_bound hRV
    · rw [Formalism.BasicNotions.Scale.b, Formalism.BasicNotions.Scale.L, hs]

theorem UpperTheory.T3.supplyOfAdmOfRankWindowsAtWidth {δ w la : ℝ} (hla : 1 < la) (hlw : la < w) :
    HostSupply → ∀ ψ : PChar, RankWindowsAtWidth ψ δ w →
      AdmitsRanks(ψ) →
      HostExW la (fun _ s R H _ => s.eps < δ → EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧ VVle H.E R.t (Real.sqrt s.b)) :=
  UpperTheory.T3.supplyOfAdmOfRankWindowsOn (P := (· < δ)) hla hlw

theorem UpperTheory.T3.supplyOfAdmOfRankWindowsAt {δ : ℝ} :
    HostSupply → ∀ ψ : PChar, RankWindowsAt ψ δ →
      AdmitsRanks(ψ) →
      HostExW (3 / 2) (fun _ s R H _ => s.eps < δ → EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧ VVle H.E R.t (Real.sqrt s.b)) :=
  UpperTheory.T3.supplyOfAdmOfRankWindowsAtWidth (w := 2) (la := 3 / 2) (by norm_num) (by norm_num)

theorem UpperTheory.T3.supplyOfAdmOfCofinal :
    HostSupply → ∀ ψ : PChar, CofinalVWinAt ψ 401 →
      AdmitsRanks(ψ) →
      HostExW (3 / 2) (fun _ s R H _ => EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧ VVle H.E R.t (Real.sqrt s.b)) := by
  intro hSup ψ hV hAdm
  simpa only [Scale.eps_lt, true_implies] using
    UpperTheory.T3.supplyOfAdmOfRankWindowsAt hSup ψ hV.rankWindows hAdm

theorem UpperTheory.T3.supplyOfAdmOf :
    HostSupply → ∀ ψ : PChar, VWinAt ψ 401 →
      AdmitsRanks(ψ) →
      HostExW (3 / 2) (fun _ s R H _ => EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧ VVle H.E R.t (Real.sqrt s.b)) :=
  fun hSup ψ hV => UpperTheory.T3.supplyOfAdmOfCofinal hSup ψ hV.cofinal
