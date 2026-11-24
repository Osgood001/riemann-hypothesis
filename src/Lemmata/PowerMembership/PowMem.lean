module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.PowerMembership

theorem goal1 :
  ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing.{u_1} R] [inst_1 : AddCommGroup.{u_2} M]
  [inst_2 : Module.{u_1, u_2} R M]
  (S : @Submodule.{u_1, u_2} R M
    (@CommRing.toCommSemiring R inst).toSemiring inst_1.toAddCommMonoid inst_2)
  (f : Module.End.{u_1, u_2} R M),
  (∀ (v : M),
      Membership.mem.{u_2, u_2} S v → Membership.mem.{u_2, u_2} S (DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1} f v)) →
    ∀ (P : Polynomial.{u_1} R) {v : M},
      Membership.mem.{u_2, u_2} S v →
        Membership.mem.{u_2, u_2} S
          (DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1}
            (DFunLike.coe.{max (u_2 + 1) (u_1 + 1), u_1 + 1, u_2 + 1} (Polynomial.aeval.{u_1, u_2} f) P) v) := by
  intro R M _ _ _ S f hf P v hv
  exact Polynomial.aeval_apply_smul_mem_of_le_comap hv P f (fun w hw => hf w hw)

end Bl.PowerMembership
