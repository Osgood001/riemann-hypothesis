module

public import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
public import Development.AutomorphicArithmetic.CharacterBoxes.Imprimitive
public import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShapeOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShape

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

namespace UpperTheory.Top

local notation "SideHyps" => Nonempty (_root_.GlobalTheory.Fc.HypsAlt
  (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)

theorem zero_free_all_of_green_small_rank_windows (hG : GlobalTheory.GLq.Green) (hV : ∀ ψ, ∃ δ > 0, RankWindowsAt ψ δ)
    (h : SideHyps) : Formalism.HC.ZeroFreeAll :=
  h.elim fun h => zeroFreeAll_of_topG_at (la := 3 / 2) (by norm_num)
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (shape_closed_link_n_of_green_at hG) trivial trivial h) fun ψ => by
      obtain ⟨δ, hδ, hv⟩ := hV ψ
      exact ⟨δ, hδ, supplyChi_of_rank_windows_at ψ hv⟩

theorem every_character_of_green_small_rank_windows (hG : GlobalTheory.GLq.Green) (hV : ∀ ψ, ∃ δ > 0, RankWindowsAt ψ δ)
    (h : SideHyps) : UpperTheory.EveryCharacter :=
  imprimitive (zero_free_all_of_green_small_rank_windows hG hV h)

theorem every_character_of_green_power_windows (hG : GlobalTheory.GLq.Green) (b : ℝ) (hb : 797 / 2 < b)
    (hV : ∀ ψ, ∃ δ > 0, JointVWinBelow ψ δ (fun _ x => x ^ b))
    (h : SideHyps) : UpperTheory.EveryCharacter := by
  apply every_character_of_green_small_rank_windows hG _ h
  intro ψ
  obtain ⟨δ, hδ, hv⟩ := hV ψ
  apply RankWindowsAt.of_limiting_power (C := fun _ => 1) hδ hb
  · simpa only [one_mul] using hv
  · intros; norm_num

theorem every_character_of_green_uniform_v_win (hG : GlobalTheory.GLq.Green) (C : Formalism.HC.PChar → ℝ → ℝ)
    (hC : ∀ ψ eps, 0 < eps → eps < 1 / 52 → 0 < C ψ eps)
    (hV : ∀ ψ, JointVWinFor ψ (fun eps x =>
      C ψ eps * x ^ rankExponent (1 / 52)))
    (h : SideHyps) : UpperTheory.EveryCharacter :=
  every_character_of_green_small_rank_windows hG
    (fun ψ => ⟨1 / 52, by norm_num, RankWindows.of_uniform (hV ψ) (hC ψ)⟩) h

theorem every_character_of_green_critical_v_win (hG : GlobalTheory.GLq.Green)
    (hV : ∀ ψ, JointVWinFor ψ (fun eps x =>
      10708 * (Nat.card (Subgroup.zpowers ψ.χ) : ℝ) ^ (rankExponent eps / (2 + 8 * eps)) * x ^ rankExponent eps))
    (h : SideHyps) : UpperTheory.EveryCharacter :=
  every_character_of_green_small_rank_windows hG
    (fun ψ => ⟨1 / 52, by norm_num, RankWindows.of_critical (hV ψ)⟩) h

theorem zero_free_all_of_green_cofinal_v_win (hG : GlobalTheory.GLq.Green) (hV : ∀ ψ, CofinalVWinAt ψ 401)
    (h : SideHyps) : Formalism.HC.ZeroFreeAll :=
  zero_free_all_of_green_small_rank_windows hG
    (fun ψ => ⟨1 / 52, by norm_num, (hV ψ).rankWindows⟩) h

theorem every_character_of_green_cofinal_v_win (hG : GlobalTheory.GLq.Green) (hV : ∀ ψ, CofinalVWinAt ψ 401)
    (h : SideHyps) : UpperTheory.EveryCharacter :=
  imprimitive (zero_free_all_of_green_cofinal_v_win hG hV h)

theorem zero_free_all_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : VWin)
    (h : SideHyps) : Formalism.HC.ZeroFreeAll :=
  zero_free_all_of_green_cofinal_v_win hG (fun ψ => (hV ψ).cofinal) h

theorem every_character_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : VWin)
    (h : SideHyps) : UpperTheory.EveryCharacter :=
  imprimitive (zero_free_all_of_green_v_win hG hV h)

end UpperTheory.Top
end
