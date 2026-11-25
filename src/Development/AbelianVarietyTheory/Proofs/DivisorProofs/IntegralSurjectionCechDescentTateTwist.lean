module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfStalkwiseBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem eqv_cechAug_of_comp_iso (R : Type) [CommRing R] (F : Shv R) {V W T : Scheme.{0}} (g : V ⟶ W) (t : W ⟶ T) [IsIso t]
    (h : Eqv R (cechAug (g ≫ t)) F) : Eqv R (cechAug g) F := by
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  let e : Arrow.mk (yoneda.map g) ≅ Arrow.mk (yoneda.map (g ≫ t)) :=
    Arrow.isoMk (Iso.refl _) (yoneda.mapIso (asIso t)) (by simp)
  let φ := SimplicialObject.augmentedCechNerve.mapIso e
  have hw : φ.hom.left ≫ cechAug (g ≫ t) = cechAug g ≫ (SimplicialObject.const _).map φ.hom.right := φ.hom.w
  have hl : IsIso φ.hom.left := (SimplicialObject.Augmented.drop.mapIso φ).isIso_hom
  have hr : IsIso ((SimplicialObject.const _).map φ.hom.right) := by
    have : IsIso φ.hom.right := (SimplicialObject.Augmented.point.mapIso φ).isIso_hom
    infer_instance
  have h1 : Eqv R (φ.hom.left ≫ cechAug (g ≫ t)) F := ((E.2.1 _ _ _ _ _).1 (E.1 _ _ _ hl)) h
  rw [hw] at h1
  exact (E.2.1 _ _ _ _ _).2.2 (E.1 _ _ _ hr) h1

/-- Integral-surjective Čech descent is a degree-zero closed-fiber test for finitary coefficients. -/
theorem integral_surjective_descent_of_closedFiberH0 {R : Type} [CommRing R] (F : Shv R) (hF : Finitary F)
    {Y X : Scheme.{0}} (f : Y ⟶ X) [IsIntegralHom f] [Surjective f]
    (hzero : ∀ (O : Type) [CommRing O] [IsLocalRing O] (s : Spec (CommRingCat.of O) ⟶ X),
      IsStalk O s → IntegralClosedFiberH0 F O) : Eqv R (cechAug f) F := by
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  refine GlobalTheory.T.equiv_of_stalkwise_base_change R F X (cech f) (sch.obj X) (cechAug f) (sch.map (𝟙 X))
    hF ?_ ?_ ?_
  · intro k
    obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom Y X f ‹_› k
    have := hπ
    refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
    rw [CategoryTheory.Functor.map_id, Category.comp_id, he]
  · intro k
    refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
    simp [sch]
  · intro O _ s hs
    obtain ⟨e₁, e₂, h⟩ := GlobalTheory.T.baseChange_cechNerveAugmentation_iso X X Y (𝟙 X) f (Over.mk s)
    obtain ⟨hH, _⟩ := hs.1
    have hg : Eqv _ (cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom))) F :=
      eqv_cechAug_of_comp_iso _ _ _ (pullback.snd (𝟙 X) s)
        (cechAug_eqv_of_closedFiberH0 F hF O hs.1 (hzero O s hs) _ _ inferInstance inferInstance)
    have hm : (bcMap (cechAug f) (sch.map (𝟙 X))).app (Over.mk s) =
        e₁.inv ≫ cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) ≫ e₂.hom := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [hm]
    exact (E.2.1 _ _ _ _ _).1 (E.1 _ _ _ inferInstance) ((E.2.1 _ _ _ _ _).1 hg (E.1 _ _ _ inferInstance))


/-- The formalization's Tate sheaves satisfy integral-surjective descent at every modulus.
At noninvertible stalks their primitive-root generators vanish. -/
theorem integral_surjective_descent_tate (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X)
    [IsIntegralHom f] [Surjective f] : Eqv (ZMod q) (cechAug f) (tw q i) :=
  integral_surjective_descent_of_closedFiberH0 (tw q i) (GlobalTheory.T.tateTwist_finitary q i) f
    (fun O _ _ _ hs => integralClosedFiberH0_tate q i O hs.1)

theorem b4 : B4 := by
  intro q Y X f _ _ _ i
  exact integral_surjective_descent_tate q i f

end GlobalTheory.EtC
