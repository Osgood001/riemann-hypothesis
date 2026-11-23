import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Development.AutomorphicArithmetic.CharacterBoxes.Imprimitive
import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShapeOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShape

namespace AlpogeRHCore14

set_option synthInstance.maxHeartbeats 200000

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

/-- Core 14 target, stated in the published unfolded form.  This keeps the
three hypotheses `hG`, `hV`, `h` and eliminates the `EveryCharacter` wrapper,
the dead `plugWin`/`plugAll` route, and the single-use
`zero_free_all_of_green_v_win` wrapper. -/
theorem everyCharacterOfGreenVWin
    (hG : GlobalTheory.GLq.Green)
    (hV : UpperTheory.Top.VWin)
    (h : Nonempty (_root_.GlobalTheory.Fc.HypsAlt
      (fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm)
      _root_.GlobalTheory.Fc.DefiniteSideCondition)) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 :=
  UpperTheory.Top.imprimitive
    (h.elim fun h =>
      UpperTheory.Top.zeroFreeAll_of_topG (la := 3 / 2) (by norm_num)
        (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _
          (_root_.UpperTheory.Top.shape_closed_link_n_of_green hG) trivial trivial h)
        fun ψ => UpperTheory.Top.supplyChi ψ (hV ψ))

end AlpogeRHCore14
