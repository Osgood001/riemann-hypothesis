module

public import Mathlib

@[expose] public section

namespace Bl.ThirdBlockLemmaC

noncomputable def goal1 {K : Type} [Field K] [NumberField K] (σ : K →+* K)
    (M : Submodule (NumberField.RingOfIntegers K) K) : Submodule (NumberField.RingOfIntegers K) K :=
  M.comap (σ₁₂ := NumberField.RingOfIntegers.mapRingHom σ)
    { toFun := σ
      map_add' := σ.map_add
      map_smul' := fun r x => σ.map_mul (r : K) x }

end Bl.ThirdBlockLemmaC
