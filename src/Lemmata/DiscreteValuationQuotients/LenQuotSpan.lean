module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.DiscreteValuationQuotients

private lemma lenQuotSpan {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (x : O) : Module.length O (O ⧸ Ideal.span ({x} : Set O)) =
      IsDiscreteValuationRing.addVal O x := by
  rw [Module.length_quotient, ← Order.coheight_orderIso (IsDiscreteValuationRing.idealOrderIsoENat O)]
  exact (Order.height_enat _).trans <| (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2
    (Submodule.IsPrincipal.associated_generator_span_self x)

theorem goal1 {O : Type u_1} {M : Type u_2} [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] [inst_3 : AddCommGroup M] [inst_4 : Module O M]
    [Module.Free O M] [Module.Finite O M] (φ : M →ₗ[O] M) (hφ : Function.Injective φ) :
    Module.length O (M ⧸ LinearMap.range φ) = IsDiscreteValuationRing.addVal O (LinearMap.det φ) := by
  classical
  let e0 : M ≃ₗ[O] LinearMap.range φ := LinearEquiv.ofInjective φ hφ
  have h : Module.finrank O (LinearMap.range φ) = Module.finrank O M := e0.finrank_eq.symm
  let b := Module.Free.chooseBasis O M
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[O] LinearMap.range φ := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[O] M := (LinearMap.range φ).subtype ∘ₗ (e' : M →ₗ[O] LinearMap.range φ)
  have hφf : φ = (LinearMap.range φ).subtype ∘ₗ (e0 : M →ₗ[O] LinearMap.range φ) :=
    LinearMap.ext fun x => rfl
  have hassoc : Associated (LinearMap.det φ) (LinearMap.det f) := by
    rw [hφf]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _) (b' i) : LinearMap.range φ) : M) = _
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [(Submodule.quotientEquivPiSpan (LinearMap.range φ) b h).length_eq, Module.length_pi_of_fintype,
    (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 hassoc, hdet]
  trans ∑ i, IsDiscreteValuationRing.addVal O (a i)
  · exact Finset.sum_congr rfl fun i _ => lenQuotSpan (a i)
  · exact (map_prod (AddValuation.toValuation (IsDiscreteValuationRing.addVal O)) a Finset.univ).symm

end Bl.DiscreteValuationQuotients
