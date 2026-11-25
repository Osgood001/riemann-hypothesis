module

public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AutomorphicArithmetic.CharacterBoxes.DyadicWindows
public import Development.AutomorphicArithmetic.CharacterBoxes.Imports
public import Development.AutomorphicArithmetic.CharacterBoxes.HostOfField
public import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

theorem UpperTheory.Top.supplyChi_of_rank_windows_on {P : ℝ → Prop} {w la : ℝ} (hla : 1 < la) (hlw : la < w) :
    ∀ ψ : PChar, RankWindowsOn ψ P w → HostExW la ((GChi ψ).whenEps P).req := by
  intro ψ hψ
  refine UpperTheory.T3.supplyOfAdmOfRankWindowsOn hla hlw hostOfField ψ hψ ?_
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := admissibleClassesTwistedChar eps he0 he1
  refine ⟨x0, fun s φ H0 hs hx hlo hhi _ _ => ?_⟩
  subst hs
  exact hx0 s φ H0 rfl hx hlo hhi

theorem UpperTheory.Top.supplyChi_of_rank_windows_at_width {δ w la : ℝ} (hla : 1 < la) (hlw : la < w) :
    ∀ ψ : PChar, RankWindowsAtWidth ψ δ w → HostExW la ((GChi ψ).below δ).req :=
  supplyChi_of_rank_windows_on (P := (· < δ)) hla hlw

theorem UpperTheory.Top.supplyChi_of_rank_windows_at {δ : ℝ} :
    ∀ ψ : PChar, RankWindowsAt ψ δ → HostExW (3 / 2) ((GChi ψ).below δ).req :=
  supplyChi_of_rank_windows_at_width (w := 2) (la := 3 / 2) (by norm_num) (by norm_num)

theorem UpperTheory.Top.supplyChi_of_cofinal :
    ∀ ψ : PChar, CofinalVWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req := by
  intro ψ hV
  have h : (GChi ψ).below (1 / 52) = GChi ψ := by
    funext s φ H TT t
    exact propext ⟨fun hg => hg s.eps_lt, fun hg _ => hg⟩
  simpa only [h] using supplyChi_of_rank_windows_at ψ hV.rankWindows

theorem UpperTheory.Top.supplyChi :
    ∀ ψ : PChar, VWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req :=
  fun ψ hψ => supplyChi_of_cofinal ψ hψ.cofinal


namespace UpperTheory.Top

/-- Sampling at page boundaries and rescaling by the field order contribute one combined factor. -/
theorem fieldRankCoeff_mul_page {ψ : PChar} {eps y : ℝ} (hy : 0 ≤ y) :
    fieldRankCoeff ψ eps * (pageRatio eps * y) ^ rankExponent eps =
      10708 * (2 * (Nat.card (Subgroup.zpowers ψ.χ) : ℝ)) ^ (rankExponent eps / (2 + 8 * eps)) *
        y ^ rankExponent eps := by
  unfold fieldRankCoeff pageRatio
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) hy,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.mul_rpow (by norm_num) (by positivity),
    show (2 + 8 * eps)⁻¹ * rankExponent eps = rankExponent eps / (2 + 8 * eps) by ring]
  ring

/-- Dyadic boundary tests at the rank exponent itself, including the field and page factors. -/
def CriticalDyadicWindowAt (ψ : PChar) (eps w : ℝ) : Prop :=
  DyadicWindowFor ψ eps w (fun y =>
    10708 * (2 * (Nat.card (Subgroup.zpowers ψ.χ) : ℝ)) ^ (rankExponent eps / (2 + 8 * eps)) *
      y ^ rankExponent eps)

theorem DyadicWindowAtWidth.critical {ψ : PChar} {eps w b : ℝ}
    (h : DyadicWindowAtWidth ψ eps w b) (hb : rankExponent eps < b) : CriticalDyadicWindowAt ψ eps w := by
  let C := 10708 * (2 * (Nat.card (Subgroup.zpowers ψ.χ) : ℝ)) ^ (rankExponent eps / (2 + 8 * eps))
  obtain ⟨M, hM⟩ := eventually_scaled_rpow_le (C := C) (D := 1) (k := 1) hb zero_le_one zero_lt_one
  exact (show DyadicWindowFor ψ eps w (fun y => y ^ b) from h).mono_eventually
    (M := M) fun y hy => by simpa only [one_mul] using hM y hy

/-- Only the sampled critical bound, and only at coinitial good ε, is needed for gated hosts. -/
theorem exists_coinitial_host_of_critical_dyadic {la w : ℝ} (ψ : PChar)
    (hla : 1 < la) (hlw : la < w)
    (h : ∀ η > (0 : ℝ), ∃ eps > (0 : ℝ), eps < η ∧ CriticalDyadicWindowAt ψ eps w) :
    ∃ P : ℝ → Prop, (∀ η > (0 : ℝ), ∃ eps > (0 : ℝ), eps < η ∧ P eps) ∧
      HostExW la ((GChi ψ).whenEps P).req := by
  let P := fun eps => CriticalDyadicWindowAt ψ eps w
  obtain ⟨v, hlv, hvw⟩ := exists_between hlw
  refine ⟨P, h, supplyChi_of_rank_windows_on hla hlv ψ (RankWindowsOn.of_critical ?_)⟩
  intro eps he _ hP
  apply DyadicWindowFor.toJoint_critical he hvw (by unfold rankExponent; positivity)
    (by unfold fieldRankCoeff; positivity)
  exact (show DyadicWindowFor ψ eps w _ from hP).mono_eventually (M := 0) fun y hy =>
    (fieldRankCoeff_mul_page hy).le

end UpperTheory.Top

theorem UpperTheory.Top.exists_coinitial_host_of_dyadic {la w : ℝ} (ψ : PChar)
    (hla : 1 < la) (hlw : la < w)
    (h : ∀ η : ℝ, 0 < η → ∃ eps : ℝ, 0 < eps ∧ eps < η ∧
      ∃ b : ℝ, rankExponent eps < b ∧ DyadicWindowAtWidth ψ eps w b) :
    ∃ P : ℝ → Prop, (∀ η : ℝ, 0 < η → ∃ eps : ℝ, 0 < eps ∧ eps < η ∧ P eps) ∧
      HostExW la ((GChi ψ).whenEps P).req := by
  apply exists_coinitial_host_of_critical_dyadic ψ hla hlw
  intro η hη
  obtain ⟨eps, he, hη', b, hb, hV⟩ := h η hη
  exact ⟨eps, he, hη', hV.critical hb⟩
