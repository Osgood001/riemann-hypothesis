module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Covolume

@[expose] public section

namespace GroundTheory.Heights₂.Heights

open Metric

theorem finite_lattice_closedBall {V : Type*} [NormedAddCommGroup V] [ProperSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] (r : ℝ) : {x : V | x ∈ L ∧ ‖x‖ ≤ r}.Finite := by
  have h := Metric.finite_isBounded_inter_isClosed (K := closedBall (0 : V) r)
    (s := (L : Set V)) DiscreteTopology.isDiscrete isBounded_closedBall
    (by rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discreteTopology)
  exact h.subset (fun _ ⟨hv, hr⟩ => ⟨by simpa using hr, hv⟩)

end GroundTheory.Heights₂.Heights
