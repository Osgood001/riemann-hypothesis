module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.ComplementLifts

private lemma compl_lift {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N N' : Submodule R M) (hN : IsCompl N N') (A B : Submodule R N) (hAB : IsCompl A B) :
    IsCompl (A.map N.subtype) (B.map N.subtype ⊔ N') := by
  have hsum : A.map N.subtype ⊔ B.map N.subtype = N := by
    rw [← Submodule.map_sup, hAB.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  have hdisj := Submodule.disjoint_map N.subtype_injective hAB.disjoint
  exact hdisj.isCompl_sup_right_of_isCompl_sup_left (hsum.symm ▸ hN)

theorem goal1 :
  ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing.{u_1} R] [IsDomain.{u_1} R] [IsPrincipalIdealRing.{u_1} R]
  [inst_3 : AddCommGroup.{u_2} M] [inst_4 : Module.{u_1, u_2} R M]
  (N N' S : @Submodule.{u_1, u_2} R M inst.toCommSemiring.toSemiring inst_3.toAddCommMonoid inst_4),
  IsCompl.{u_2} N N' →
    ∀ [Module.Finite.{u_1, u_2} R (Subtype.{u_2 + 1} fun (x : M) ↦ Membership.mem.{u_2, u_2} N x)],
      LE.le.{u_2} S N →
        (∀ (a : R) (x : M),
            Ne.{u_1 + 1} a 0 →
              Membership.mem.{u_2, u_2} S (HSMul.hSMul.{u_1, u_2, u_2} a x) → Membership.mem.{u_2, u_2} S x) →
          Exists.{u_2 + 1} fun (T : Submodule.{u_1, u_2} R M) ↦ IsCompl.{u_2} S T := by
  intro R M _ _ _ _ _ N N' S hN _ hSN hsat
  let S' : Submodule R N := S.comap N.subtype
  have : Module.IsTorsionFree R (N ⧸ S') := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective S' q
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [S', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul] at hq ⊢
      exact hsat r x hr hq
  obtain ⟨h, hh⟩ := LinearMap.exists_rightInverse_of_surjective S'.mkQ (Submodule.range_mkQ S')
  have hidem : IsIdempotentElem (h ∘ₗ S'.mkQ) :=
    LinearMap.ext fun x => congrArg h (LinearMap.congr_fun hh (S'.mkQ x))
  have hinj := LinearMap.injective_of_comp_eq_id h S'.mkQ hh
  have hker : LinearMap.ker (h ∘ₗ S'.mkQ) = S' := by
    rw [LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot_of_injective hinj), S'.ker_mkQ]
  have hc : IsCompl S' (LinearMap.range (h ∘ₗ S'.mkQ)) := by
    simpa only [hker] using (LinearMap.IsIdempotentElem.isCompl hidem).symm
  have hS : S'.map N.subtype = S := by
    simp only [S', Submodule.map_comap_subtype]
    exact inf_eq_right.2 hSN
  refine ⟨(LinearMap.range (h ∘ₗ S'.mkQ)).map N.subtype ⊔ N', ?_⟩
  have := compl_lift N N' hN S' _ hc
  rwa [hS] at this

end Bl.ComplementLifts
