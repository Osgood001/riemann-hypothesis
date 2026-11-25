module

public import Development.AutomorphicArithmetic.CharacterBoxes.DyadicWindows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopPlug

@[expose] public section

open Formalism.HC Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

namespace UpperTheory.Top

local notation "SideHyps" => Nonempty (_root_.GlobalTheory.Fc.HypsAlt
  (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)

/-- Any fixed arithmetic power window of width greater than one suffices for the cyclic level. -/
theorem cyclicLevel_of_green_narrow_window (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (b w : ℝ) (hb : 797 / 2 < b) (hw : 1 < w) (ψ : PChar)
    (hV : ∃ δ > 0, JointVWinBelowWidth ψ δ w (fun _ x => x ^ b)) : (Level.cyc ψ).ZeroFreeLevel := by
  obtain ⟨δ, hδ, hV⟩ := hV
  have hwindow : JointVWinBelowWidth ψ δ w (fun _ x => 1 * x ^ b) := by simpa only [one_mul] using hV
  obtain ⟨η, hη, hr⟩ := RankWindowsAtWidth.of_limiting_power (C := fun _ => 1) hδ hb hwindow (by intros; norm_num)
  obtain ⟨la, hla, hlw⟩ := exists_between hw
  exact h.elim fun side => cyclicLevel_zeroFree_of_topG_at ψ hla
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (shape_closed_link_n_of_green_at hG)
      trivial trivial side) hη (supplyChi_of_rank_windows_at_width hla hlw ψ hr)

theorem cyclicLevel_of_green_power_window (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (b : ℝ) (hb : 797 / 2 < b) (ψ : PChar)
    (hV : ∃ δ > 0, JointVWinBelow ψ δ (fun _ x => x ^ b)) : (Level.cyc ψ).ZeroFreeLevel :=
  cyclicLevel_of_green_narrow_window hG h b 2 hb (by norm_num) ψ hV

/-- A window need not be supplied for each character separately: it suffices
that the cyclic levels of the tested characters cover their primitive parts. -/
theorem every_character_of_green_narrow_cover (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (tested : Set PChar)
    (cover : ∀ ψ : PChar, ∃ ρ ∈ tested, ψ ∈ (Level.cyc ρ).KEPT)
    (win : ∀ ρ ∈ tested, ∃ b > (797 / 2 : ℝ), ∃ w > 1, ∃ δ > 0,
      JointVWinBelowWidth ρ δ w (fun _ x => x ^ b)) :
    UpperTheory.EveryCharacter := by
  apply imprimitive
  intro ψ _
  obtain ⟨ρ, hρ, hψ⟩ := cover ψ
  obtain ⟨b, hb, w, hw, δ, hδ, hV⟩ := win ρ hρ
  exact cyclicLevel_of_green_narrow_window hG h b w hb hw ρ ⟨δ, hδ, hV⟩ ψ hψ

theorem every_character_of_green_window_cover (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (b : ℝ) (hb : 797 / 2 < b) (tested : Set PChar)
    (cover : ∀ ψ : PChar, ∃ ρ ∈ tested, ψ ∈ (Level.cyc ρ).KEPT)
    (win : ∀ ρ ∈ tested, ∃ δ > 0, JointVWinBelow ρ δ (fun _ x => x ^ b)) :
    UpperTheory.EveryCharacter :=
  every_character_of_green_narrow_cover hG h tested cover fun ρ hρ =>
    ⟨b, hb, 2, by norm_num, win ρ hρ⟩

/-- For a modulus with cyclic unit group, a single character window suffices.
Its primitive part may have smaller conductor than the modulus. -/
theorem one_narrow_window_at_cyclic_modulus (N : ℕ) [NeZero N] [IsCyclic (ZMod N)ˣ] :
    ∃ ξ : DirichletCharacter ℂ N, ∀ (b w : ℝ), 797 / 2 < b → 1 < w →
      (∃ δ > 0, JointVWinBelowWidth (PChar.of ξ) δ w (fun _ x => x ^ b)) →
      GlobalTheory.GLq.Green → SideHyps →
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := Level.exists_cyc_keeps_all_of_isCyclic_units (n := N)
  refine ⟨ξ, fun b w hb hw hv hG h χ => ?_⟩
  apply imprimitive_of_primitive χ
  exact cyclicLevel_of_green_narrow_window hG h b w hb hw _ hv (PChar.of χ) (hξ χ)

theorem one_window_at_cyclic_modulus (N : ℕ) [NeZero N] [IsCyclic (ZMod N)ˣ] :
    ∃ ξ : DirichletCharacter ℂ N, ∀ (b : ℝ), 797 / 2 < b →
      (∃ δ > 0, JointVWinBelow (PChar.of ξ) δ (fun _ x => x ^ b)) →
      GlobalTheory.GLq.Green → SideHyps →
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := one_narrow_window_at_cyclic_modulus N
  exact ⟨ξ, fun b hb => hξ b 2 hb (by norm_num)⟩

/-- Finite Sha samples at the rank exponent itself, along epsilons tending to zero. -/
def CriticalDyadicSupply (ψ : PChar) : Prop :=
  ∃ w > (1 : ℝ), ∀ η > (0 : ℝ), ∃ eps > (0 : ℝ), eps < η ∧ CriticalDyadicWindowAt ψ eps w

/-- Each chosen character needs one positive window width, but Sha estimates only along some
sequence of epsilons tending to zero. The excess over the rank exponent need not be uniform. -/
def CoinitialDyadicWindows (ψ : PChar) : Prop :=
  ∃ w > (1 : ℝ), ∀ η > (0 : ℝ), ∃ eps > (0 : ℝ), eps < η ∧
    ∃ b > rankExponent eps, DyadicWindowAtWidth ψ eps w b

/-- A larger pure power eventually dominates the field and page multiplier at each selected ε. -/
theorem CoinitialDyadicWindows.critical {ψ : PChar} (h : CoinitialDyadicWindows ψ) :
    CriticalDyadicSupply ψ := by
  obtain ⟨w, hw, h⟩ := h
  refine ⟨w, hw, fun η hη => ?_⟩
  obtain ⟨eps, he, hη', b, hb, win⟩ := h η hη
  exact ⟨eps, he, hη', win.critical hb⟩

/-- Any fixed power above the limiting exponent works throughout a sufficiently small ε range. -/
theorem DyadicVWinBelowWidth.coinitial {ψ : PChar} {δ w b : ℝ} (h : DyadicVWinBelowWidth ψ δ w b)
    (hδ : 0 < δ) (hw : 1 < w) (hb : 797 / 2 < b) : CoinitialDyadicWindows ψ := by
  refine ⟨w, hw, fun η hη => ?_⟩
  let cutoff := min (min (min η δ) (1 / 52)) ((b - 797 / 2) / (929 / 16))
  have hc : 0 < cutoff := lt_min (lt_min (lt_min hη hδ) (by norm_num))
    (div_pos (sub_pos.mpr hb) (by norm_num))
  obtain ⟨eps, he, ht⟩ := exists_between hc
  have hh := lt_min_iff.mp ht
  obtain ⟨hηδ, h52⟩ := lt_min_iff.mp hh.1
  obtain ⟨heη, heδ⟩ := lt_min_iff.mp hηδ
  refine ⟨eps, he, heη, b, ?_, h eps he h52 heδ⟩
  have h' := (lt_div_iff₀ (show (0 : ℝ) < 929 / 16 by norm_num)).mp hh.2
  unfold rankExponent
  linarith

theorem cyclicLevel_of_green_critical_dyadic (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (ψ : PChar) (win : CriticalDyadicSupply ψ) : (Level.cyc ψ).ZeroFreeLevel := by
  obtain ⟨w, hw, win⟩ := win
  obtain ⟨la, hla, hlw⟩ := exists_between hw
  obtain ⟨P, hP, hH⟩ := exists_coinitial_host_of_critical_dyadic ψ hla hlw win
  exact h.elim fun side => cyclicLevel_of_coinitial_hosts hla
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (shape_closed_link_n_of_green_on hG)
      trivial trivial side) hP ψ hH

theorem every_character_of_green_critical_dyadic (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (tested : Set PChar) (cover : ∀ ψ : PChar, ∃ ρ ∈ tested, ψ ∈ (Level.cyc ρ).KEPT)
    (win : ∀ ρ ∈ tested, CriticalDyadicSupply ρ) : UpperTheory.EveryCharacter := by
  apply imprimitive
  intro ψ _
  obtain ⟨ρ, hρ, hψ⟩ := cover ψ
  exact cyclicLevel_of_green_critical_dyadic hG h ρ (win ρ hρ) ψ hψ

theorem one_critical_dyadic_window_at_cyclic_modulus (N : ℕ) [NeZero N] [IsCyclic (ZMod N)ˣ] :
    ∃ ξ : DirichletCharacter ℂ N, CriticalDyadicSupply (PChar.of ξ) →
      GlobalTheory.GLq.Green → SideHyps →
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := Level.exists_cyc_keeps_all_of_isCyclic_units (n := N)
  refine ⟨ξ, fun win hG h χ => imprimitive_of_primitive χ ?_⟩
  exact cyclicLevel_of_green_critical_dyadic hG h _ win (PChar.of χ) (hξ χ)

theorem cyclicLevel_of_green_coinitial_windows (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (ψ : PChar) (win : CoinitialDyadicWindows ψ) : (Level.cyc ψ).ZeroFreeLevel :=
  cyclicLevel_of_green_critical_dyadic hG h ψ win.critical

theorem every_character_of_green_coinitial_windows (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (tested : Set PChar) (cover : ∀ ψ : PChar, ∃ ρ ∈ tested, ψ ∈ (Level.cyc ρ).KEPT)
    (win : ∀ ρ ∈ tested, CoinitialDyadicWindows ρ) : UpperTheory.EveryCharacter :=
  every_character_of_green_critical_dyadic hG h tested cover fun ρ hρ => (win ρ hρ).critical

theorem one_coinitial_window_at_cyclic_modulus (N : ℕ) [NeZero N] [IsCyclic (ZMod N)ˣ] :
    ∃ ξ : DirichletCharacter ℂ N, CoinitialDyadicWindows (PChar.of ξ) →
      GlobalTheory.GLq.Green → SideHyps →
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := one_critical_dyadic_window_at_cyclic_modulus N
  exact ⟨ξ, fun win => hξ win.critical⟩

/-- It suffices to test the finite list of dyadic page boundaries in each retained window. -/
theorem cyclicLevel_of_green_dyadic_window (hG : GlobalTheory.GLq.Green) (h : SideHyps) (ψ : PChar)
    (win : ∃ b > (797 / 2 : ℝ), ∃ w > 1, ∃ δ > 0, DyadicVWinBelowWidth ψ δ w b) :
    (Level.cyc ψ).ZeroFreeLevel := by
  obtain ⟨b, hb, w, hw, δ, hδ, hV⟩ := win
  exact cyclicLevel_of_green_coinitial_windows hG h ψ (hV.coinitial hδ hw hb)

theorem every_character_of_green_dyadic_cover (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (tested : Set PChar) (cover : ∀ ψ : PChar, ∃ ρ ∈ tested, ψ ∈ (Level.cyc ρ).KEPT)
    (win : ∀ ρ ∈ tested, ∃ b > (797 / 2 : ℝ), ∃ w > 1, ∃ δ > 0, DyadicVWinBelowWidth ρ δ w b) :
    UpperTheory.EveryCharacter :=
  every_character_of_green_coinitial_windows hG h tested cover fun ρ hρ => by
    obtain ⟨b, hb, w, hw, δ, hδ, hV⟩ := win ρ hρ
    exact hV.coinitial hδ hw hb

theorem one_dyadic_window_at_cyclic_modulus (N : ℕ) [NeZero N] [IsCyclic (ZMod N)ˣ] :
    ∃ ξ : DirichletCharacter ℂ N,
      (∃ b > (797 / 2 : ℝ), ∃ w > 1, ∃ δ > 0, DyadicVWinBelowWidth (PChar.of ξ) δ w b) →
      GlobalTheory.GLq.Green → SideHyps →
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := one_coinitial_window_at_cyclic_modulus N
  refine ⟨ξ, fun win => ?_⟩
  obtain ⟨b, hb, w, hw, δ, hδ, hV⟩ := win
  exact hξ (hV.coinitial hδ hw hb)

end UpperTheory.Top
