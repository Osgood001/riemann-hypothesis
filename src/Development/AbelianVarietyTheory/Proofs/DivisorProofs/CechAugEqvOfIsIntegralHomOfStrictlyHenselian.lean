module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TateSectionsAtNonunitModulus
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationEquivOfSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLocallyConstantComapAlgClosureTensorOfHStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCyclotomicPrimitiveRootsOfStrictlyHenselStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelwiseEquivalenceIntegralPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalencePullbackIntegralAffineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointAlgClosureResidueFieldOfIntegralSurjeStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.IntDescent

theorem isIntegral_algClosure_residue (A : Type) [CommRing A] [IsLocalRing A] :
    Algebra.IsIntegral A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  have : Algebra.IsIntegral A (IsLocalRing.ResidueField A) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId A (IsLocalRing.ResidueField A)) IsLocalRing.residue_surjective
  have : Algebra.IsIntegral (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
    Algebra.IsAlgebraic.isIntegral
  exact Algebra.IsIntegral.trans (IsLocalRing.ResidueField A)

theorem isIntegral_tensor (A C B : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    [Algebra.IsIntegral A C] [Algebra.IsIntegral A B] : Algebra.IsIntegral A (C ⊗[A] B) := by
  have : Algebra.IsIntegral C (C ⊗[A] B) := inferInstance
  exact Algebra.IsIntegral.trans C

theorem L1 : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)],
    IsUnit (q : A) → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
    Eqv (ZMod q) (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom) (tw q i) := by
  intro q i A _ _ _ hq B _ _ _
  have hSH : SH A := ⟨inferInstance, inferInstance⟩
  obtain ⟨ζ0⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A hSH hq
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) := ζ0.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i (Spec (CommRingCat.of A)) ζ
  have := isIntegral_algClosure_residue A
  have := isIntegral_tensor A (AlgebraicClosure (IsLocalRing.ResidueField A)) B
  have hfin := GlobalTheory.T.tateTwist_finitary q i
  have hU := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A B hSH
  have hU' := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A (AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B) hSH
  have hbij := GlobalTheory.T.bijective_locallyConstant_comap_algClosure_tensor_of_henselian (ZMod q) A B
  exact GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) _ _ hgen (Spec (CommRingCat.of B)) _
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) _ hU hU' hbij

end GlobalTheory.EtC.IntDescent

namespace GlobalTheory.EtC


/-- Test only degree zero after passing to the geometric residue field. -/
def IntegralClosedFiberH0 {R : Type} [CommRing R] (F : Shv R)
    (A : Type) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
    Function.Bijective (pull R (spMap (Algebra.TensorProduct.includeRight :
      B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom) F 0)

open IntDescent in
private theorem integral_closedFiber_equiv_iff_H0 {R : Type} [CommRing R] (F : Shv R) (hF : Finitary F)
    (A : Type) [CommRing A] [IsLocalRing A] (hSH : SH A) (B : Type) [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] :
    let f := spMap (Algebra.TensorProduct.includeRight :
      B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom
    Eqv R f F ↔ Function.Bijective (pull R f F 0) := by
  refine ⟨fun h => h 0, fun hzero n => ?_⟩
  have := isIntegral_algClosure_residue A
  have := isIntegral_tensor A (AlgebraicClosure (IsLocalRing.ResidueField A)) B
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hneg := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F).1
    have := hneg (sp B) n hn
    have := hneg (sp (AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B)) n hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  · exact hzero
  · have := GlobalTheory.T.integral_strictHenselian_acyclic_finitary R F hF A B hSH n hn
    have := GlobalTheory.T.integral_strictHenselian_acyclic_finitary R F hF A
      (AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B) hSH n hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

open IntDescent in
theorem integralClosedFiberH0_tate (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A]
    (hSH : SH A) : IntegralClosedFiberH0 (tw q i) A := by
  obtain ⟨hH, hsep⟩ := hSH
  intro B _ _ _
  by_cases hq : IsUnit (q : A)
  · exact L1 q i A hq B 0
  · have := isIntegral_algClosure_residue A
    have := isIntegral_tensor A (AlgebraicClosure (IsLocalRing.ResidueField A)) B
    have := UpperTheory.subsingleton_tate_H0_of_not_isUnit q i A B hq
    have := UpperTheory.subsingleton_tate_H0_of_not_isUnit q i A
      (AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B) hq
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

open IntDescent in
theorem cechAug_eqv_of_closedFiberH0 {R : Type} [CommRing R] (F : Shv R) (hF : Finitary F)
    (A : Type) [CommRing A] [IsLocalRing A] (hSH : SH A) (hzero : IntegralClosedFiberH0 F A)
    (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)) (hg : IsIntegralHom g) (hsurj : Surjective g) :
    Eqv R (cechAug g) F := by
  set Ω := AlgebraicClosure (IsLocalRing.ResidueField A)
  set u : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ω)) with hu_def
  have hpb : IsPullback (pullback.fst g u) (pullback.snd g u) g u := IsPullback.of_hasPullback g u
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst g u) (pullback.snd g u) g u hpb
  have hsq : ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of Ω)) (φ : Z' ⟶ Z),
      IsIntegralHom h → IsPullback φ h' h u → Eqv R (sch.map φ) F :=
    GlobalTheory.T.etaleCohomologyEquivalence_pullback_integral_affine R F A Ω (fun B _ _ _ => integral_closedFiber_equiv_iff_H0 F hF A hSH B |>.2 (hzero B))
  have hEm : Eqv R m F :=
    GlobalTheory.T.levelwiseEquivalence_isEquivalence R m F (GlobalTheory.T.cechNerve_levelwise_equivalence_integral_pullback R F _ _ _ _ _ _ g u hpb hg hsq m hm)
  have hEu : Eqv R (sch.map u) F :=
    hsq _ _ (𝟙 _) (𝟙 _) u inferInstance (IsPullback.id_vert u)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_point_algClosure_residueField_of_integral_surjective A Y g hg hsurj
  have hEs : Eqv R (cechAug (pullback.snd g u)) F :=
    GlobalTheory.T.etaleCechAugmentation_equiv_of_section R F _ _ (pullback.snd g u) (pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp]))
      (pullback.lift_snd _ _ _)
  obtain ⟨-, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  have h1 : Eqv R (cechAug (pullback.snd g u) ≫ sch.map u) F :=
    (hcomp _ _ _ _ _).1 hEs hEu
  rw [← hm.w] at h1
  exact (hcomp _ _ _ _ _).2.1 hEm h1


open IntDescent in
theorem cechAug_eqv_of_isIntegralHom_of_strictlyHenselian : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  intro q i A _ hSH _ Y g hg hsurj
  obtain ⟨hH, hsep⟩ := hSH
  exact cechAug_eqv_of_closedFiberH0 (tw q i) (GlobalTheory.T.tateTwist_finitary q i) A
    ⟨hH, hsep⟩ (integralClosedFiberH0_tate q i A ⟨hH, hsep⟩) Y g hg hsurj

end GlobalTheory.EtC
