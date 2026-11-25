module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteDimensionalHodgeCohomologyOfSmoothProj

@[expose] public section

namespace UpperTheory.Gal.LocalSmoothExtension

/-- Finiteness follows from projectivity, independently of the fixed-point formula. -/
theorem hodgeFin_holds : HodgeFin := by
  intro Z s _ _ hproj a b
  exact UpperTheory.finiteDimensional_hodgeCohomology_of_proj s hproj a b

theorem hodgeFin_of : HolomorphicLefschetzFormula → HodgeFin := fun _ => hodgeFin_holds

end UpperTheory.Gal.LocalSmoothExtension
