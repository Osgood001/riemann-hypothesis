import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice

namespace AlpogeRHCore33

theorem sharpMassVolumeAndHostDegree :
    (SiegelMassRatioCM → MassVolumeBoundsAll) ∧
    (∀ (D : D7), SiegelMassRatioModels → AbsoluteConstantSecondPart D) ∧
    (∀ (D : D7), PrimeSumLogBound D) :=
  ⟨Formalism.MainNotions.StandardLattice.volumeMass_all_of_standardMassRatio, Formalism.MainNotions.StandardLattice.stmt2All_of_mod, Formalism.MainNotions.StandardLattice.hostDegree_holds⟩

end AlpogeRHCore33
