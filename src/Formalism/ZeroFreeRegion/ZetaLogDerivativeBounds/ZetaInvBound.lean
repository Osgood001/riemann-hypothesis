module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight

@[expose] public section

namespace Formalism.ZF

/-- The inverse zeta bound is the modulus-one case of the Dirichlet bound. -/
theorem zetaInvBound_statement : ZetaInvBound := by
  intro s hs
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    ZeroFreeDirichlet.inverseBound 1 (1 : DirichletCharacter ℂ 1) s hs

end Formalism.ZF
