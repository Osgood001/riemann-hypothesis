module

public import Mathlib

@[expose] public section

universe u_1

namespace Bl.SmulListSum

open scoped Pointwise in
theorem goal1 :
  ∀ {U : Type u_1} [inst : AddCommGroup.{u_1} U] [inst_1 : Module.{0, u_1} Complex U] {G : Set.{u_1} U},
  (∀ (w : U),
      Membership.mem.{u_1, u_1} G w → ∀ (c : Complex), Membership.mem.{u_1, u_1} G (HSMul.hSMul.{0, u_1, u_1} c w)) →
    ∀ {y : U},
      Membership.mem.{u_1, u_1}
        (@Submodule.span.{0, u_1} Complex U _ inst.toAddCommMonoid inst_1 G) y →
        Exists.{u_1 + 1} fun (l : List.{u_1} U) ↦
          And (∀ (w : U), Membership.mem.{u_1, u_1} l w → Membership.mem.{u_1, u_1} G w)
            (Eq.{u_1 + 1} y (List.sum.{u_1} l)) := by
  intro U _ _ G hG y hy
  have hy' : y ∈ AddSubmonoid.closure ((Set.univ : Set Complex) • G) := by
    rwa [← Submodule.span_eq_closure]
  obtain ⟨l, hl, hsum⟩ := AddSubmonoid.exists_list_of_mem_closure hy'
  refine ⟨l, ?_, hsum.symm⟩
  intro w hw
  obtain ⟨c, -, v, hv, rfl⟩ := hl w hw
  exact hG v hv c

end Bl.SmulListSum
