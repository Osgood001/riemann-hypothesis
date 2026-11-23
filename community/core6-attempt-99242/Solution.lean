import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Bundle03
import Bundle04

namespace AlpogeRHCore6

theorem cmIntegrality :
    Formalism.L2.Th1.CM.JInvariantIntegrality ∧ Formalism.L2.Th1.CM.CM3 :=
  ⟨ReciprocityTheory.ChartRestriction.L1.cm1,
   ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree⟩

end AlpogeRHCore6
