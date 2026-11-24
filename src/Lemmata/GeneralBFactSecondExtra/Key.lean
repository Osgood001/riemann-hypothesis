module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact_second'''

private lemma key {O : Type*} {Y : Type*} [CommRing O] [AddCommGroup Y] [Module O Y]
    (R S D E : Submodule O Y) (hD : ∀ y, y ∈ D ↔ y ∈ R ∧ y ∈ S) (hE : E ≤ D) :
    Module.length O (R ⧸ E.comap R.subtype) =
      Module.length O (R ⧸ S.comap R.subtype) + Module.length O (D ⧸ E.comap D.subtype) := by
  have hDR : D ≤ R := fun y hy => ((hD y).1 hy).1
  have hDS : D.comap R.subtype = S.comap R.subtype := by
    ext x
    exact (hD x).trans (and_iff_right x.2)
  have hES : E.comap R.subtype ≤ S.comap R.subtype := by
    rw [← hDS]
    exact Submodule.comap_mono hE
  have hcomap : (E.comap R.subtype).comap (Submodule.inclusion hDR) = E.comap D.subtype := rfl
  rw [add_comm]
  refine Module.length_eq_add_of_exact
    ((E.comap D.subtype).mapQ (E.comap R.subtype) (Submodule.inclusion hDR) hcomap.ge)
    (Submodule.factor hES) ?_ (Submodule.factor_surjective hES) ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  · rw [LinearMap.exact_iff, Submodule.range_mapQ, Submodule.ker_mapQ,
      Submodule.range_inclusion, hDS, Submodule.comap_id]

theorem goal1 :
  ∀ {O : Type u_1} {Y : Type u_2} [inst : CommRing.{u_1} O] [inst_1 : AddCommGroup.{u_2} Y]
  [inst_2 : Module.{u_1, u_2} O Y]
  (R S D E : @Submodule.{u_1, u_2} O Y inst.toCommSemiring.toSemiring inst_1.toAddCommMonoid inst_2),
  (∀ (y : Y),
      Iff (Membership.mem.{u_2, u_2} D y) (And (Membership.mem.{u_2, u_2} R y) (Membership.mem.{u_2, u_2} S y))) →
    LE.le.{u_2} E D →
      Eq.{1}
        (Module.length.{u_1, u_2} O
          (HasQuotient.Quotient.{u_2, u_2} (Subtype.{u_2 + 1} fun (x : Y) ↦ Membership.mem.{u_2, u_2} R x)
            (Submodule.comap.{u_1, u_1, u_2, u_2} (Submodule.subtype.{u_1, u_2} R) E)))
        (HAdd.hAdd.{0, 0, 0}
          (Module.length.{u_1, u_2} O
            (HasQuotient.Quotient.{u_2, u_2} (Subtype.{u_2 + 1} fun (x : Y) ↦ Membership.mem.{u_2, u_2} R x)
              (Submodule.comap.{u_1, u_1, u_2, u_2} (Submodule.subtype.{u_1, u_2} R) S)))
          (Module.length.{u_1, u_2} O
            (HasQuotient.Quotient.{u_2, u_2} (Subtype.{u_2 + 1} fun (x : Y) ↦ Membership.mem.{u_2, u_2} D x)
              (Submodule.comap.{u_1, u_1, u_2, u_2} (Submodule.subtype.{u_1, u_2} D) E)))) := by
  intro O Y _ _ _ R S D E hD hE
  exact key R S D E hD hE

end Bl.general_b_fact_second'''
