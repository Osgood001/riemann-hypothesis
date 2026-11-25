module

public import Mathlib

@[expose] public section

namespace Bl.FirstBlockLemmaG

theorem goal1 {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a m : O} :
    IsUnit a → m ∈ IsLocalRing.maximalIdeal O → IsUnit (a - m) := by
  intro ha hm
  rw [← IsLocalRing.notMem_maximalIdeal, Submodule.sub_mem_iff_left _ hm]
  exact IsLocalRing.notMem_maximalIdeal.mpr ha

end Bl.FirstBlockLemmaG
