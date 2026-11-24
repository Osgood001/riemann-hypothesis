module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity

@[expose] public section

namespace Formalism.ZF

open Formalism.ZeroFreeDirichlet in
/-- The zeta inequality is the modulus-one case of Dirichlet log-derivative positivity. -/
theorem mertensInequality : ThreeFourOne := by
  intro σ t hσ
  simpa only [one_pow, negLD, DirichletCharacter.LFunction_modOne_eq] using
    (negLogDerivPositivity 1 σ hσ).1 (1 : DirichletCharacter ℂ 1) t

end Formalism.ZF
