module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory

variable (R T : Type) [CommRing R] [AddCommGroup T] [Module R T] [TopologicalSpace T] [DiscreteTopology T]

local instance : ContinuousConstSMul R T := ⟨fun _ => continuous_of_discreteTopology⟩

/-- The étale sheaf of locally constant functions with values in the discrete module `T`. -/
noncomputable def locallyConstantEtaleSheaf : Shv R where
  obj := Et.cPre R T
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{1} (ULift.{1} R))),
      isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf Scheme.etaleTopology (continuousMapPresheaf.{0} T ⋙ uliftFunctor.{1})
    rw [Presieve.isSheaf_comp_uliftFunctor_iff]
    exact Presieve.isSheaf_of_le _
      (Scheme.etaleTopology_le_proetaleTopology.trans Scheme.proetaleTopology_le_fpqcTopology)
      ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqcTopology_continuousMapPresheaf.{0, 0} T))

private abbrev coeffFunctor := (Functor.const CommRingCat.{0}).obj (ModuleCat.of (ULift.{1} R) (ULift.{1} T))

private noncomputable def constSection :
    coeffFunctor R T ⟶ onRings (locallyConstantEtaleSheaf R T) where
  app A := ModuleCat.ofHom
    { toFun := fun t => ULift.up (ContinuousMap.const (Spec A) t.down)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  naturality _ _ _ := rfl

attribute [local instance] IsFiltered.isConnected in
theorem locallyConstantEtaleSheaf_finitary : Finitary (locallyConstantEtaleSheaf R T) := by
  let F := locallyConstantEtaleSheaf R T
  let M := coeffFunctor R T
  let η := constSection R T
  refine GlobalTheory.T.finitary_of_locally_bijective_from_filtered_functor R M F η ?_ ?_ ?_
  · exact ⟨fun J _ _ => ⟨fun {_} => ⟨fun {_} _ => ⟨isColimitConstCocone J _⟩⟩⟩⟩
  · intro A x
    let f : C(Spec A, T) := x.down
    obtain ⟨ι, hι, B, g, he, hc, hP⟩ := GlobalTheory.finite_etale_family (A := A)
      (fun B g => ∃ m : M.obj B, (η.app B).hom m = ((onRings F).map g).hom x) (fun p => by
        let U : (Spec A).Opens := ⟨f ⁻¹' {f p}, (isOpen_discrete _).preimage f.continuous⟩
        let v : U := ⟨p, rfl⟩
        obtain ⟨i, z, hz⟩ := U.toScheme.affineCover.exists_eq v
        let j := U.toScheme.affineCover.f i ≫ U.ι
        obtain ⟨B, g, k, w, he, hk, hw⟩ := GlobalTheory.etale_affine_ring j z
        refine ⟨B, g, w, he, ?_, ULift.up (f p), ?_⟩
        · rw [hk, Scheme.Hom.comp_apply, hw]; change U.ι (U.toScheme.affineCover.f i z) = p
          rw [hz]; rfl
        · change ULift.up (ContinuousMap.const _ (f p)) = ULift.up (f.comp (Spec.map g).base.hom)
          congr 1
          ext b
          change f p = f (Spec.map g b)
          rw [hk, Scheme.Hom.comp_apply]
          exact ((U.toScheme.affineCover.f i (k b)).2 : f _ = f p).symm)
    choose m hm using hP
    exact ⟨ι, hι, B, g, m, he, hc, hm⟩
  · intro A m hm
    refine GlobalTheory.finite_etale_family (A := A) (fun B g => (M.map g).hom m = 0) fun p => ?_
    refine ⟨A, 𝟙 A, p, ?_, ?_, ?_⟩
    · change (algebraMap A A).Etale
      rw [RingHom.etale_algebraMap]; infer_instance
    · simp
    · change m = 0
      apply ULift.ext
      exact congrArg (fun (s : ULift.{1} C(Spec A, T)) => s.down p) hm

private theorem locallyConstantEtaleSheaf_pull_zero_of_comap
    {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B')
    (h : Function.Bijective (fun a : LocallyConstant (PrimeSpectrum B) T =>
      a.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩)) :
    Function.Bijective (pull R (spMap φ) (locallyConstantEtaleSheaf R T) 0) := by
  let F := locallyConstantEtaleSheaf R T
  let g : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom φ)
  let E (X : Scheme.{0}) : LocallyConstant X T ≃ Sec F X :=
    (Equiv.ofBijective LocallyConstant.toContinuousMap ⟨LocallyConstant.toContinuousMap_injective,
      fun f => ⟨⟨f, (IsLocallyConstant.iff_continuous f).2 f.continuous⟩, rfl⟩⟩).trans Equiv.ulift.symm
  have hsec : Function.Bijective (Sec.res (F := F) g) := by
    apply (Function.Bijective.of_comp_iff _ (E _).bijective).1
    let gφ : C(PrimeSpectrum B', PrimeSpectrum B) := ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩
    change Function.Bijective ((E (Spec (CommRingCat.of B'))) ∘ (fun a : LocallyConstant (PrimeSpectrum B) T => a.comap gφ))
    exact (E _).bijective.comp h
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  apply (Function.Bijective.of_comp_iff _ (e _).bijective).1
  have hn : pull R (sch.map g) F 0 ∘ e _ = e _ ∘ Sec.res (F := F) g := funext (he g)
  rw [hn]
  exact (e _).bijective.comp hsec

/-- Integral surjective Čech descent for discrete constant coefficients, with no invertibility
or finiteness condition on the coefficient ring or module. -/
theorem integral_surjective_descent_locallyConstant {Y X : Scheme.{0}} (f : Y ⟶ X)
    [IsIntegralHom f] [Surjective f] : Eqv R (cechAug f) (locallyConstantEtaleSheaf R T) := by
  apply GlobalTheory.EtC.integral_surjective_descent_of_closedFiberH0 _
    (locallyConstantEtaleSheaf_finitary R T) f
  intro O _ _ s hs A _ _ _
  obtain ⟨_, _⟩ := hs.1
  exact locallyConstantEtaleSheaf_pull_zero_of_comap R T _
    (GlobalTheory.T.bijective_locallyConstant_comap_algClosure_tensor_of_henselian T O A)

end UpperTheory
