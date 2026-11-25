module

public import Mathlib
public import Lemmata.OrbitSpans.Basic

@[expose] public section

namespace GlobalTheory.SpanOrbitTop

theorem span_orbit_eq_top {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : Representation.IsIrreducible π) {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G ↦ π g v) = ⊤ := by
  exact congrArg Subrepresentation.toSubmodule (Bl.OrbitSpans.orbitSpan_eq_top π v hv)

end GlobalTheory.SpanOrbitTop
