import Mathlib
import Bundle00
noncomputable section
open CategoryTheory AlgebraicGeometry
open Set (empty_subset eq_empty_of_forall_notMem eq_empty_or_nonempty eq_univ_iff_forall eq_univ_of_forall eq_univ_of_univ_subset image_comp image_congr image_singleton mem_biUnion mem_compl_iff mem_empty_iff_false mem_iUnion mem_image_of_mem mem_ofPred_eq mem_preimage mem_range_self mem_singleton mem_univ nonempty_iff_ne_empty preimage preimage_compl preimage_univ range range_comp singleton_subset_iff subset_univ univ)
open List (eraseIdx length length_eraseIdx_add_one mem_cons mem_of_mem_eraseIdx)
open Nat (add_sub_cancel card card_eq_fintype_card card_sum cast_ne_zero cast_one cast_zero eq_zero_of_le_zero exists_eq_succ_of_ne_zero le_add_left le_induction le_of_succ_le le_succ lt_succ_self not_lt_zero sub_add_cancel sub_eq_zero_of_le zero_add zero_le)
open Ideal (comap comap_isMaximal_of_surjective comap_isPrime comap_mono comap_symm eq_top_iff_one isPrime_bot isRadical_iff_quotient_reduced map_comap_of_surjective map_id map_le_iff_le_comap map_map map_mono map_span mem_comap mem_map_of_mem mem_span_singleton mem_span_singleton' mk_ker mul_mem_left mul_mem_right one_eq_top radical_eq_sInf span span_eq span_le span_singleton_pow subset_span)
open TopologicalSpace.Opens (coe_iSup coe_top isBasis_iff_nbhd mem_iSup)
open Submodule (disjoint_def eq_bot_of_le_smul_of_le_jacobson_bot eq_top_iff' mem_iInf mem_iSup_of_mem mem_of_span_eq_top_of_smul_pow_mem mul_induction_on' range_subtype)
open IsLocalization (algEquiv away_of_isUnit_of_bijective eq_iff_exists injective lift_eq map_radical map_under map_units mem_map_algebraMap_iff mk'_eq_zero_iff mk'_spec ringHom_ext)
open Algebra (FiniteType FormallyEtale FormallySmooth IsSeparable IsStandardSmoothOfRelativeDimension PreSubmersivePresentation Presentation SubmersivePresentation adjoin adjoin_le algebraMap_eq_smul_one algebra_ext linearMap ofId ofId_apply smul_def subset_adjoin toSMul)
open Finset (prod_empty prod_insert sum_congr sum_eq_single sum_eq_zero)
open RingHom (IsStandardSmooth Smooth coe_coe coe_comp comp_apply comp_assoc id_apply isStandardSmooth_respectsIso ker_eq_comap_bot map_det mem_ker smooth_algebraMap toAlgebra)
open MvPolynomial (aeval aeval_C aeval_X aeval_def aeval_map_algebraMap algHom_ext algebraMap_eq eval₂Hom induction_on map_surjective pderiv pderiv_C pderiv_X_of_ne pderiv_X_self pderiv_map pderiv_mul)
open Polynomial (C_mul_X_pow_eq_monomial as_sum_support coeff_monomial lcoeff lcoeff_apply map_ne_zero_iff mem_support_iff monomial monomial_mul_monomial monomial_zero_one)
open Scheme (GSpecIso IdealSheafData isBasis_affineOpens isoSpec_Spec_inv isoSpec_hom mem_basicOpen_top mem_zeroLocus_iff preimage_basicOpen zariskiPrecoverage)
open TensorProduct (inductionOn lid smul_tmul' tmul_add tmul_smul)
open SetLike (GradedMonoid coe_injective ext'_iff le_def mem_coe not_le_iff_exists)
open Submonoid (mem_powers powers powers_le)
open CommRingCat (hom_comp hom_id hom_inv_apply inv_hom_apply ofHom ofHom_comp ofHom_hom)
open Function (Bijective Exact Injective LeftInverse injective_id surjInv surjInv_eq)
open LinearMap (exact_iff mem_range rTensor)
open Localization (Away mk_eq_mk' mk_eq_mk_iff mk_mul mk_one_eq_algebraMap r_iff_exists)
open IsIso (hom_inv_id_apply inv_hom_id_apply of_isIso_comp_left)
open IsLocalRing (ResidueField eq_maximalIdeal isField_iff_maximalIdeal_eq jacobson_eq_maximalIdeal le_maximalIdeal maximalIdeal mem_maximalIdeal residue)
open HasRingHomProperty (Spec_iff iff_of_isAffine iff_of_source_openCover instIsZariskiLocalAtSource)
open PrimeSpectrum (asIdeal isRadical_vanishingIdeal le_iff_mem_closure mem_basicOpen mem_vanishingIdeal mem_zeroLocus zeroLocus_vanishingIdeal_eq_closure)
open Module (FinitePresentation Projective finitePresentation_of_finite free_of_flat_of_isLocalRing)
open IsAffineOpen (SpecMap_appLE_fromSpec fromSpec_top iSup_basicOpen_eq_self_iff)
open Scheme.IdealSheafData (comap_comp comap_id comap_map_le comap_top ideal_comap_of_isOpenImmersion ideal_mul ideal_pow ker_subschemeι le_map_iff_comap_le le_ofIdeals_iff mem_support_iff_of_mem ofIdealTop radical_ideal subscheme subschemeι support support_eq_bot_iff support_top vanishingIdeal vanishingIdeal_ideal vanishingIdeal_support)
open Scheme.Hom (appIso appIso_hom' appIso_inv_app appLE appLE_comp_appLE appLE_eq_app appLE_map appTop app_eq_appLE app_surjective comp_app comp_appTop comp_preimage finiteType_appLE germ_stalkMap isClosedEmbedding isOpenEmbedding ker ker_apply ker_comp ker_comp_of_isIso le_ker_comp pre preimage_smoothLocus_eq preimage_top resLE stalkMap)
open Category (assoc comp_id id_comp)
open Limits.pullback (condition fst hom_ext lift_fst lift_snd snd)
open Iso (cancel_iso_hom_left hom_inv_id hom_inv_id_assoc inv inv_comp_eq inv_hom_id inv_hom_id_assoc symm_hom trans_hom)
open CommRingCat.Hom (hom)
open Ideal.Quotient (eq_zero_iff_mem liftₐ mk mk_surjective mkₐ)
open Algebra.PreSubmersivePresentation (comp_jacobian_eq_jacobian_smul_jacobian jacobiMatrix_apply jacobian_eq_jacobiMatrix_det localizationAway)
open Proj (basicOpen iSup_basicOpen_eq_top toSpecZero)
open Sum (inl inr)
open Algebra.TensorProduct (includeLeftRingHom includeRight lift_tmul tmul_mul_tmul)
open Algebra.Generators (algebraMap_apply ker_eq_ker_aeval_val ofSurjective)
open DFunLike (congr_fun)
open Spec (map_comp)
open ULift (up)
open IsPullback (of_bot of_hasPullback of_horiz_isIso of_iso_pullback)
open HomogeneousLocalization (eq_num_div_den ext_iff_val fromZeroRingHom val_mul val_zero)
open IsLocalization.Away (algebraMap_isUnit lift)
open Localization.Away (invSelf)
open IsScalarTower (of_algebraMap_eq of_algebraMap_eq')
open AlgHom (coe_toRingHom toRingHom_eq_coe)
open IsClosedImmersion (lift_fac)
open Algebra.FormallySmooth (of_equiv of_isLocalization)
open Subsingleton (elim)
open Scheme.Pullback (exists_preimage_pullback)
open Scheme.Cover (mkOfCovers pullbackHom)
open AlgebraicGeometry (IsAffineHom Proj smooth_iff)
open Limits.Sigma (desc)
open TopologicalSpace (Closeds NoetherianSpace Opens)
open Iff (mp mpr)
open Scheme.Opens (toScheme ι)
section
set_option maxSynthPendingDepth 1

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace StandardSmoothLift


section

variable {S R B : Type} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite σ]
  (hsurj : Function.Surjective $ algebraMap S R)
  (P : SubmersivePresentation R B ι σ)

noncomputable def liftedRelation (j : σ) : MvPolynomial ι S :=
  surjInv (map_surjective (algebraMap S R) hsurj) $ P.relation j

theorem map_liftedRelation j :
    m45 (algebraMap S R) (liftedRelation hsurj P j) = P.relation j :=
  surjInv_eq (map_surjective (algebraMap S R) hsurj) $ P.relation j

abbrev LiftedQuotient : Type :=
  MvPolynomial ι S ⧸ span (range (liftedRelation hsurj P))

theorem aeval_mk_X_liftedQuotient_surjective :
    Function.Surjective
      ⇑(aeval (fun i =>
          mk (span (range (liftedRelation hsurj P))) (m7 i)) :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) := by
  let _c0 := span $ range $ liftedRelation hsurj P
  have hEq : (aeval (fun i =>
      mk _c0 $ m7 i) :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) =
      mkₐ S _c0 :=
    algHom_ext fun i => by simp
  have h : ∀ q,
      (aeval (fun i =>
        mk _c0 $ m7 i) :
        MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) q =
      mk _c0 q := by simp_all
  intro x
  obtain ⟨q, rfl⟩ := mk_surjective x
  exact ⟨q, h q⟩

noncomputable def liftedGenerators : Algebra.Generators S (LiftedQuotient hsurj P) ι where
  val i := mk (span (range (liftedRelation hsurj P))) (m7 i)
  σ' := surjInv (aeval_mk_X_liftedQuotient_surjective hsurj P)
  aeval_val_σ' := surjInv_eq (aeval_mk_X_liftedQuotient_surjective hsurj P)

noncomputable def liftedPresentation : Presentation S (LiftedQuotient hsurj P) ι σ where
  toGenerators := liftedGenerators hsurj P
  relation := liftedRelation hsurj P
  span_range_relation_eq_ker := by
    have hval : (liftedGenerators hsurj P).val =
        fun i : ι => mk (span (range (liftedRelation hsurj P)))
          (m7 i) := rfl
    have h : (aeval (liftedGenerators hsurj P).val :
          MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) =
        mkₐ S (span (range (liftedRelation hsurj P))) :=
      algHom_ext fun i => by
        simp [hval]
    have hq : ∀ q : MvPolynomial ι S,
        (aeval (liftedGenerators hsurj P).val) q =
          mk (span (range (liftedRelation hsurj P))) q :=
      fun q => congr_fun h q
    refine Ideal.ext fun q => ?_
    have hmem : q ∈ (liftedGenerators hsurj P).ker ↔
        (aeval (liftedGenerators hsurj P).val) q = 0 := m22
    rw [hmem, hq q, eq_zero_iff_mem]

noncomputable def liftedPreSubmersivePresentation :
    PreSubmersivePresentation S (LiftedQuotient hsurj P) ι σ where
  toPresentation := liftedPresentation hsurj P
  map := P.map
  map_inj := P.map_inj

@[simp] theorem liftedPreSubmersivePresentation_relation (j : σ) :
    (liftedPreSubmersivePresentation hsurj P).relation j = liftedRelation hsurj P j := rfl

@[simp] theorem liftedPreSubmersivePresentation_map :
    (liftedPreSubmersivePresentation hsurj P).map = P.map := rfl

abbrev LiftedAlgebra : Type := Away (liftedPreSubmersivePresentation hsurj P).jacobian

noncomputable def liftedSubmersivePresentation :
    SubmersivePresentation S (LiftedAlgebra hsurj P) (Unit ⊕ ι) (Unit ⊕ σ) where
  toPreSubmersivePresentation :=
    Algebra.PreSubmersivePresentation.comp
      (localizationAway (S := LiftedAlgebra hsurj P)
        (liftedPreSubmersivePresentation hsurj P).jacobian) (liftedPreSubmersivePresentation hsurj P)
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian,
      smul_def]
    exact (algebraMap_isUnit (S := LiftedAlgebra hsurj P)
        (liftedPreSubmersivePresentation hsurj P).jacobian).mul
      (Algebra.SubmersivePresentation.localizationAway (S := LiftedAlgebra hsurj P)
        (liftedPreSubmersivePresentation hsurj P).jacobian).jacobian_isUnit

noncomputable def mvPolynomialToBaseChange :
    MvPolynomial ι R →ₐ[R] R ⊗[S] LiftedAlgebra hsurj P :=
  aeval fun i : ι =>
    (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
      (mk (span (range (liftedRelation hsurj P))) (m7 i)))

theorem mvPolynomialToBaseChange_map f :
    mvPolynomialToBaseChange hsurj P (m45 (algebraMap S R) f) =
      (1 : R) ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
        (mk (span (range (liftedRelation hsurj P))) f)) := by
  induction f using induction_on
  next a =>
    have hI : mk (span $ range $ liftedRelation hsurj P)
        (MvPolynomial.C a) = algebraMap S (LiftedQuotient hsurj P) a := by
      rw [← algebraMap_eq]
      exact (mkₐ S $ span $ range $ liftedRelation hsurj P).commutes a
    have hL : mvPolynomialToBaseChange hsurj P (m45 (algebraMap S R) $ m8 a)
        = algebraMap S (R ⊗[S] LiftedAlgebra hsurj P) a := by simp_all
    rw [hL, hI, ← IsScalarTower.algebraMap_apply S (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) a,
      Algebra.algebraMap_eq_smul_one a, Algebra.algebraMap_eq_smul_one a,
      Algebra.TensorProduct.one_def, TensorProduct.tmul_smul]
  next p q hp hq =>
    simp [hp, hq, tmul_add]
  next p i hp =>
    have hX : mvPolynomialToBaseChange hsurj P (m7 i)
        = 1 ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
            (mk (span $ range $ liftedRelation hsurj P)
              (m7 i))) := by
      simp [mvPolynomialToBaseChange]
    simp [hp, hX, tmul_mul_tmul]

theorem mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero q
    (hq : (aeval P.val : MvPolynomial ι R →ₐ[R] B) q = 0) :
    mvPolynomialToBaseChange hsurj P q = 0 := by
  have hmem : q ∈ span (range P.relation) := by
    rw [P.span_range_relation_eq_ker, ker_eq_ker_aeval_val]
    simpa only [mem_ker, toRingHom_eq_coe, coe_coe] using hq
  have hsub : span (range P.relation) ≤
      m41 (mvPolynomialToBaseChange hsurj P) := by
    rw [span_le]
    rintro x ⟨j, rfl⟩
    simp [mem_coe, mem_ker]
    have h := mvPolynomialToBaseChange_map hsurj P $ liftedRelation hsurj P j
    rw [map_liftedRelation hsurj P j, Ideal.Quotient.eq_zero_iff_mem.mpr $ subset_span $ mem_range_self j] at h
    simpa using h
  simpa only [mem_ker, coe_toRingHom] using hsub hmem

theorem mvPolynomialToBaseChange_section_mul x y :
    mvPolynomialToBaseChange hsurj P (P.σ' (x * y)) =
      mvPolynomialToBaseChange hsurj P (P.σ' x) * mvPolynomialToBaseChange hsurj P (P.σ' y) := by
  have hker : (aeval P.val)
      (P.σ' (x * y) - P.σ' x * P.σ' y) = 0 := by
    simp [P.aeval_val_σ']
  have h := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ hker
  rw [map_sub, map_mul] at h
  linear_combination h

theorem mvPolynomialToBaseChange_section_add x y :
    mvPolynomialToBaseChange hsurj P (P.σ' (x + y)) =
      mvPolynomialToBaseChange hsurj P (P.σ' x) + mvPolynomialToBaseChange hsurj P (P.σ' y) := by
  have h1 : (aeval P.val)
      (P.σ' (x + y) - (P.σ' x + P.σ' y)) = 0 := by
    rw [map_sub, map_add, P.aeval_val_σ' $ x + y, P.aeval_val_σ' x, P.aeval_val_σ' y, sub_self]
  have h0 := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ h1
  rw [map_sub, map_add] at h0
  linear_combination h0

theorem mvPolynomialToBaseChange_section_algebraMap r :
    mvPolynomialToBaseChange hsurj P (P.σ' (algebraMap R B r)) =
      algebraMap R (R ⊗[S] LiftedAlgebra hsurj P) r := by
  let _a0 := algebraMap R B r
  have h1 : (aeval P.val)
      (P.σ' _a0 - m8 r) = 0 := by
    rw [map_sub, P.aeval_val_σ' _a0, aeval_C, sub_self]
  have h0 := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ h1
  have hC : mvPolynomialToBaseChange hsurj P (m8 r) =
      algebraMap R (R ⊗[S] LiftedAlgebra hsurj P) r := by simp_all
  rw [map_sub, hC] at h0
  linear_combination h0

noncomputable def invBaseChangeHom : B →ₐ[R] R ⊗[S] LiftedAlgebra hsurj P where
  toFun b := mvPolynomialToBaseChange hsurj P (P.σ' b)
  map_one' := by
    have h1 : (aeval P.val : MvPolynomial ι R →ₐ[R] B) (P.σ' (1 : B) - 1) = 0 := by
      rw [map_sub, map_one, P.aeval_val_σ' 1, sub_self]
    have h0 := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ h1
    rw [map_sub, map_one] at h0
    linear_combination h0
  map_mul' := mvPolynomialToBaseChange_section_mul hsurj P
  map_zero' := by
    have h0 :=
      P.aeval_val_σ' 0
    exact mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ h0
  map_add' := mvPolynomialToBaseChange_section_add hsurj P
  commutes' := mvPolynomialToBaseChange_section_algebraMap hsurj P

theorem invBaseChangeHom_aeval q :
    invBaseChangeHom hsurj P (aeval P.val q) = mvPolynomialToBaseChange hsurj P q := by
  let _m0 := (aeval P.val : MvPolynomial ι R →ₐ[R] B)
  let _a0 := P.σ' $ _m0 q
  have hker : _m0
      (_a0 - q) = 0 := by
    rw [map_sub, P.aeval_val_σ', sub_self]
  have h := mvPolynomialToBaseChange_eq_zero_of_aeval_eq_zero hsurj P _ hker
  rw [map_sub] at h
  have hf : invBaseChangeHom hsurj P (_m0 q)
      = mvPolynomialToBaseChange hsurj P
          _a0 := rfl
  rw [hf]
  linear_combination h

section

variable [Algebra S B] [IsScalarTower S R B]

theorem aeval_eq_zero_of_mem_span_liftedRelation q
    (hq : q ∈ span (range $ liftedRelation hsurj P)) :
    (aeval P.val : MvPolynomial ι S →ₐ[S] B) q = 0 := by
  let _c0 := (aeval P.val : MvPolynomial ι S →ₐ[S] B)
  have hsub : span (range $ liftedRelation hsurj P) ≤
      m41 _c0.toRingHom := by
    rw [span_le]
    rintro x ⟨j, rfl⟩
    have hmem : P.relation j ∈ span (range P.relation) :=
      subset_span ⟨j, rfl⟩
    rw [P.span_range_relation_eq_ker, ker_eq_ker_aeval_val] at hmem
    have h0 := by
      simpa only [mem_ker, toRingHom_eq_coe, coe_coe] using hmem
    let _a0 := liftedRelation hsurj P j
    have h1 : (aeval P.val)
        (m45 (algebraMap S R) _a0) =
          _c0 _a0 := by
      rw [aeval_map_algebraMap]
    rw [map_liftedRelation hsurj P j] at h1
    have h2 : _c0
        _a0 = 0 := by
      rwa [← h1]
    simpa only [mem_coe, mem_ker, toRingHom_eq_coe,
      coe_coe] using h2
  simpa only [mem_ker, toRingHom_eq_coe, coe_coe] using hsub hq

noncomputable def liftedQuotientHom : LiftedQuotient hsurj P →ₐ[S] B :=
  liftₐ (span (range (liftedRelation hsurj P)))
    (aeval P.val : MvPolynomial ι S →ₐ[S] B)
    (aeval_eq_zero_of_mem_span_liftedRelation hsurj P)

@[simp] theorem liftedQuotientHom_mk (q : MvPolynomial ι S) :
    liftedQuotientHom hsurj P
        (mk (span $ range $ liftedRelation hsurj P) q) =
      (aeval P.val : MvPolynomial ι S →ₐ[S] B) q := rfl

theorem isUnit_liftedQuotientHom_jacobian :
    IsUnit ((liftedQuotientHom hsurj P).toRingHom (liftedPreSubmersivePresentation hsurj P).jacobian) := by
  let _c0 := liftedPreSubmersivePresentation hsurj P
  let _c1 := span $ range $ liftedRelation hsurj P
  classical
  let _ := Fintype.ofFinite σ
  have hval : _c0.val =
      fun i => mk _c1
        (m7 i) := rfl
  have hmk : ∀ q,
      (aeval _c0.val) q =
        mk _c1 q := by
    have h : (aeval _c0.val :
          MvPolynomial ι S →ₐ[S] LiftedQuotient hsurj P) =
        mkₐ S _c1 :=
      algHom_ext fun i => by simp [hval]
    exact fun q => congr_fun h q
  let _a0 := algebraMap S R
  have hmat : ∀ a b,
      m45 _a0 (_c0.jacobiMatrix a b)
        = P.jacobiMatrix a b := by
    intro a b
    rw [jacobiMatrix_apply,
      jacobiMatrix_apply, liftedPreSubmersivePresentation_map,
      liftedPreSubmersivePresentation_relation, ← pderiv_map, map_liftedRelation]
  have h1 : _c0.jacobiMatrix.map
      (m45 _a0) = P.jacobiMatrix := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.map_apply]
    exact hmat a b
  have hdet : m45 _a0
      (_c0.jacobiMatrix.det) = P.jacobiMatrix.det := by
    calc m45 _a0 (_c0.jacobiMatrix.det)
        = (_c0.jacobiMatrix.map
            (m45 _a0)).det := map_det ..
      _ = P.jacobiMatrix.det := by rw [h1]
  have hjS : _c0.jacobian =
      mk _c1
        (_c0.jacobiMatrix.det) := by
    rw [jacobian_eq_jacobiMatrix_det]
    exact hmk _
  have hjR : P.jacobian =
      (m165 P.val) P.jacobiMatrix.det := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.Generators.algebraMap_apply]
  have h2 : IsUnit $ liftedQuotientHom hsurj P $ _c0.jacobian := by
    have hkey : liftedQuotientHom hsurj P (_c0.jacobian) = P.jacobian := by
      rw [hjS, liftedQuotientHom_mk, hjR, ← hdet]
      simp [aeval_def, MvPolynomial.eval₂_map]
      rw [← IsScalarTower.algebraMap_eq S R B]
    rw [hkey]
    exact P.jacobian_isUnit
  simpa only [toRingHom_eq_coe, coe_coe] using h2

theorem awayLift_jacobian_algebraMap_eq s :
    ((lift (liftedPreSubmersivePresentation hsurj P).jacobian
        (isUnit_liftedQuotientHom_jacobian hsurj P) : LiftedAlgebra hsurj P →+* B))
      (algebraMap S (LiftedAlgebra hsurj P) s) = algebraMap S B s := by
  let _a0 := LiftedQuotient hsurj P
  let _a1 := LiftedAlgebra hsurj P
  let _a2 := liftedQuotientHom hsurj P
  have h : ∀ x,
      (lift (liftedPreSubmersivePresentation hsurj P).jacobian
          (isUnit_liftedQuotientHom_jacobian hsurj P) : RingHom _a1 B)
        (algebraMap _a0 _a1 x) =
        _a2.toRingHom x := by
    intro x
    exact lift_eq ..
  rw [IsScalarTower.algebraMap_apply S _a0 _a1 s, h]
  exact _a2.commutes s

noncomputable def liftedAlgebraHom : LiftedAlgebra hsurj P →ₐ[S] B :=
  { (lift (liftedPreSubmersivePresentation hsurj P).jacobian
      (isUnit_liftedQuotientHom_jacobian hsurj P) : LiftedAlgebra hsurj P →+* B) with
    commutes' := awayLift_jacobian_algebraMap_eq hsurj P }

theorem liftedAlgebraHom_algebraMap x :
    liftedAlgebraHom hsurj P (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) =
      liftedQuotientHom hsurj P x := by
  have h : liftedAlgebraHom hsurj P (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) =
      (lift (liftedPreSubmersivePresentation hsurj P).jacobian
        (isUnit_liftedQuotientHom_jacobian hsurj P) : LiftedAlgebra hsurj P →+* B)
        (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) x) := rfl
  rw [h]
  simp [IsLocalization.Away.lift_eq, toRingHom_eq_coe, coe_coe]

theorem liftedAlgebraHom_surjective : Function.Surjective (liftedAlgebraHom hsurj P) := by
  intro b
  let _a0 := algebraMap S R
  obtain ⟨p, hp⟩ := map_surjective _a0 hsurj $ P.σ' b
  have h1 : (aeval P.val)
      (m45 _a0 p) =
        (aeval P.val) p := by
    rw [aeval_map_algebraMap]
  refine ⟨algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P)
    (mk (span $ range $ liftedRelation hsurj P) p), ?_⟩
  rw [liftedAlgebraHom_algebraMap, liftedQuotientHom_mk, ← h1, hp]
  exact P.aeval_val_σ' b

noncomputable def baseChangeHom : (R ⊗[S] LiftedAlgebra hsurj P) →ₐ[R] B :=
  Algebra.TensorProduct.lift (ofId R B) (liftedAlgebraHom hsurj P)
    (fun _ _ => Commute.all _ _)

theorem invBaseChangeHom_liftedAlgebraHom x :
    invBaseChangeHom hsurj P (liftedAlgebraHom hsurj P x) = (1 : R) ⊗ₜ[S] x := by
  have key : (invBaseChangeHom hsurj P).toRingHom.comp (liftedAlgebraHom hsurj P).toRingHom =
      (includeRight :
        LiftedAlgebra hsurj P →ₐ[S] R ⊗[S] LiftedAlgebra hsurj P).toRingHom := by
    refine ringHom_ext
      (powers (liftedPreSubmersivePresentation hsurj P).jacobian) ?_
    refine m48 fun q => ?_
    have h : invBaseChangeHom hsurj P (liftedQuotientHom hsurj P q) = 1 ⊗ₜ[S] (algebraMap (LiftedQuotient hsurj P) (LiftedAlgebra hsurj P) q) := by
      obtain ⟨p, rfl⟩ := mk_surjective q
      have h1 : (aeval P.val)
          (m45 (algebraMap S R) p) =
            (aeval P.val) p := by
        rw [aeval_map_algebraMap]
      rw [liftedQuotientHom_mk, ← h1, invBaseChangeHom_aeval]
      exact mvPolynomialToBaseChange_map hsurj P p
    rwa [← liftedAlgebraHom_algebraMap hsurj P q] at h
  exact congr_fun key x

theorem baseChangeHom_bijective : Bijective (baseChangeHom hsurj P) := by
  let _a0 := invBaseChangeHom hsurj P
  constructor
  have hleft : LeftInverse _a0 $ baseChangeHom hsurj P := by
    intro t
    refine inductionOn t ?_ ?_
    intro r x
    have h1 : baseChangeHom hsurj P (r ⊗ₜ[S] x)
        = algebraMap R B r * liftedAlgebraHom hsurj P x := by
      simp [baseChangeHom, lift_tmul, ofId_apply]
    have h2 : invBaseChangeHom hsurj P (algebraMap R B r)
        = r ⊗ₜ[S] 1 := _a0.commutes r
    rw [h1, map_mul, h2, invBaseChangeHom_liftedAlgebraHom,
      tmul_mul_tmul, mul_one, one_mul]
    intro a b ha hb
    rw [map_add, map_add, ha, hb]
  exact hleft.injective
  intro b
  obtain ⟨x, hx⟩ := liftedAlgebraHom_surjective hsurj P b
  refine ⟨1 ⊗ₜ[S] x, ?_⟩
  rw [← hx]
  simp [baseChangeHom, lift_tmul, map_one, one_mul]

noncomputable def baseChangeEquiv : (R ⊗[S] LiftedAlgebra hsurj P) ≃ₐ[R] B :=
  AlgEquiv.ofBijective (baseChangeHom hsurj P) (baseChangeHom_bijective hsurj P)

theorem baseChangeEquiv_one_tmul b' :
    baseChangeEquiv hsurj P (1 ⊗ₜ[S] b') = liftedAlgebraHom hsurj P b' := by
  have h : baseChangeEquiv hsurj P (1 ⊗ₜ[S] b')
      = (ofId R B) 1 * liftedAlgebraHom hsurj P b' := rfl
  rw [h, map_one, one_mul]

end

end

end StandardSmoothLift
end FunctorialResolution.EmbeddedResolution
end
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

namespace StandardSmoothLift

section

variable {S R B : Type} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite ι] [Finite σ]
  (hsurj : Function.Surjective $ algebraMap S R)
  (P : SubmersivePresentation R B ι σ)

theorem liftedSubmersivePresentation_dimension :
    (liftedSubmersivePresentation hsurj P).dimension = P.dimension := by
  have hu : card Unit = 1 := by
    rw [card_eq_fintype_card, Fintype.card_unit]
  have h1 : card (Unit ⊕ ι) = card ι + 1 := by
    rw [card_sum, hu]
    omega
  have h2 : card (Unit ⊕ σ) = card σ + 1 := by
    rw [card_sum, hu]
    omega
  show card (Unit ⊕ ι) - card (Unit ⊕ σ) = card ι - card σ
  rw [h1, h2]
  omega

end

end StandardSmoothLift

section

variable (S R B : Type) [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] [Algebra S B] [IsScalarTower S R B]

theorem exists_lift_of_isStandardSmoothOfRelativeDimension r
    [IsStandardSmoothOfRelativeDimension r R B]
    (hsurj : Function.Surjective (algebraMap S R)) :
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra S B') (f : B' →ₐ[S] B),
      IsStandardSmoothOfRelativeDimension r S B' ∧ Function.Surjective f ∧
        ∃ e : (R ⊗[S] B') ≃ₐ[R] B, ∀ b', e (1 ⊗ₜ[S] b') = f b' := by
  have hinst : IsStandardSmoothOfRelativeDimension r R B := ‹_›
  obtain ⟨ι, σ, hsg_, hio, P, hdim⟩ := hinst.out
  have : Finite ι := hio
  exact ⟨StandardSmoothLift.LiftedAlgebra hsurj P, inferInstance, inferInstance,
    StandardSmoothLift.liftedAlgebraHom hsurj P, ⟨⟨Unit ⊕ ι, Unit ⊕ σ, inferInstance, inferInstance, StandardSmoothLift.liftedSubmersivePresentation hsurj P, tr_ (StandardSmoothLift.liftedSubmersivePresentation_dimension hsurj P) hdim⟩⟩,
    StandardSmoothLift.liftedAlgebraHom_surjective hsurj P,
    StandardSmoothLift.baseChangeEquiv hsurj P,
    StandardSmoothLift.baseChangeEquiv_one_tmul hsurj P⟩

end

end FunctorialResolution.EmbeddedResolution
end
section
open Polynomial

namespace FunctorialResolution.Blowup

variable {R : Type} [CommRing R]

section
variable (I : Ideal R)
theorem mem_pow_one {a} (ha : a ∈ I) : a ∈ I ^ 1 := by
  rwa [pow_one]

theorem mem_pow_zero r : r ∈ I ^ 0 :=by simp_all
section
variable (n : ℕ)
noncomputable def reesGrading : Submodule R ↥(reesAlgebra I) :=
  Submodule.comap (reesAlgebra I).val.toLinearMap
    (LinearMap.range $ monomial (R := R) n)

section
variable (p : ↥(reesAlgebra I))
theorem mem_reesGrading_iff_monomial :
    p ∈ reesGrading I n ↔ ∃ r ∈ I ^ n, (p : R[X]) = monomial n r := by
  have hmem : p ∈ reesGrading I n ↔ ∃ r : R, monomial n r = p := m22
  rw [hmem]
  constructor
  rintro ⟨r, hr⟩
  have hp := mp_ (mem_reesAlgebra_iff I _) p.2 n
  have hcoef : (monomial n r).coeff n = r := by simp
  rw [← hr, hcoef] at hp
  exact ⟨r, hp, sy_ hr⟩
  rintro ⟨r, -, hpr⟩
  exact ⟨r, sy_ hpr⟩

theorem mem_reesGrading_iff_coeff :
    p ∈ reesGrading I n ↔ ∀ i, i ≠ n → (p : R[X]).coeff i = 0 := by
  have key : p ∈ reesGrading I n ↔ ∃ r : R, monomial n r = p := m22
  rw [key]
  constructor
  rintro ⟨r, hr⟩ i hi
  rw [← hr, coeff_monomial, if_neg $ m113 hi]
  intro h
  refine ⟨(p : R[X]).coeff n, ?_⟩
  ext i
  rcases eq_or_ne i n with rfl | hi
  simp
  simp [coeff_monomial, m113 hi, h i hi]
end
end

theorem reesGrading_mul_mem {m n} {p q}
    (hp : p ∈ reesGrading I m) (hq : q ∈ reesGrading I n) :
    p * q ∈ reesGrading I (m + n) := by
  have key : ∀ (k : ℕ) (x : (reesAlgebra I)),
      x ∈ reesGrading I k ↔ ∃ r : R, monomial k r = x :=
    fun _ _ => m22
  obtain ⟨a, ha⟩ := (key m p).1 hp
  obtain ⟨b, hb⟩ := (key n q).1 hq
  refine (key (m + n) $ p * q).2 ⟨a * b, ?_⟩
  have hpq : ((p * q : (reesAlgebra I)) : (R[X])) = p * q := rfl
  rw [hpq, ← ha, ← hb, monomial_mul_monomial]
end

instance instGradedMonoidReesGrading (I : Ideal R) : GradedMonoid $ reesGrading I where
  one_mem := by
    refine mem_range.2 ⟨1, ?_⟩
    simp
  mul_mem := @fun _ _ _ _ hp hq => reesGrading_mul_mem I hp hq

section
variable (I : Ideal R)
theorem reesGrading_iSupIndep : iSupIndep $ reesGrading I := by
  intro n
  rw [disjoint_def]
  intro p hp hp'
  have hker : (⨆ (j : ℕ) (_ : j ≠ n), reesGrading I j) ≤
      m177 ((lcoeff R n).comp $ (reesAlgebra I).val.toLinearMap) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro x hx
    simpa [LinearMap.mem_ker, lcoeff_apply] using ((mem_reesGrading_iff_coeff I j x).1 hx n $ m113 hj)
  have hpn : (p : R[X]).coeff n = 0 := by
    simpa [LinearMap.mem_ker, lcoeff_apply] using (hker hp')
  have hp0 : p = 0 := by
    ext i
    rcases eq_or_ne i n with rfl | hi
    simpa using hpn
    simpa using ((mem_reesGrading_iff_coeff I n p).1 hp) i hi
  exact m26 $ by simpa using hp0

theorem monomial_mem_reesGrading {n} {r} (hr : r ∈ I ^ n) :
    (⟨monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ : ↥(reesAlgebra I))
      ∈ reesGrading I n := by
  refine (mem_reesGrading_iff_coeff I n _).2 fun i hi => ?_
  rw [coeff_monomial, if_neg $ m113 hi]

theorem reesGrading_iSup_eq_top : (⨆ n : ℕ, reesGrading I n) = ⊤ := by
  refine eq_top_iff'.2 fun p => ?_
  let _a0 := reesAlgebra I
  have hval : ∀ x y,
      _a0.val x = _a0.val y → x = y := fun _ _ h => m26 h
  let _a1 := (p : R[X])
  have hsum : p = ∑ i ∈ support _a1,
      (⟨monomial i $ _a1.coeff i,
        reesAlgebra.monomial_mem.mpr $ p.2 i⟩ : _a0) :=
    hval _ _ (by rw [map_sum]; exact as_sum_support _)
  rw [hsum]
  exact sum_mem fun i _ => mem_iSup_of_mem i
    (monomial_mem_reesGrading I $ p.2 i)

theorem reesGrading_isInternal : DirectSum.IsInternal $ reesGrading I := by
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top $ reesGrading I).2
    ⟨reesGrading_iSupIndep I, reesGrading_iSup_eq_top I⟩

noncomputable def directSumReesGradingEquiv :
    DirectSum ℕ (fun n => ↥(reesGrading I n)) ≃ ↥(reesAlgebra I) :=
  Equiv.ofBijective (DirectSum.coeAddMonoidHom $ reesGrading I) $ reesGrading_isInternal I

end

noncomputable instance instGradedAlgebraReesGrading (I : Ideal R) :
    GradedAlgebra $ reesGrading I where
  __ := instGradedMonoidReesGrading I
  decompose' := ⇑(directSumReesGradingEquiv I).symm
  left_inv := fun x => (directSumReesGradingEquiv I).apply_symm_apply x
  right_inv := fun x => (directSumReesGradingEquiv I).symm_apply_apply x


section
variable (I : Ideal R)
section
variable (n) (r) (hr : r ∈ I ^ n)
noncomputable def reesMonomial :
    ↥(reesAlgebra I) :=
  ⟨monomial n r, reesAlgebra.monomial_mem.mpr hr⟩

@[simp] theorem reesMonomial_coe :
    ((reesMonomial I n r hr : ↥(reesAlgebra I)) : R[X]) = monomial n r := rfl
end

theorem reesMonomial_mem_reesGrading {n} {r} (hr : r ∈ I ^ n) :
    reesMonomial I n r hr ∈ reesGrading I n := by
  rw [mem_reesGrading_iff_monomial]
  exact ⟨r, hr, reesMonomial_coe I n r hr⟩

noncomputable def reesDegreeOneMonomial (a : R) (ha : a ∈ I) : ↥(reesAlgebra I) :=
  reesMonomial I 1 a $ mem_pow_one I ha


section
variable (a : ↥I)
noncomputable def reesGenerator : ↥(reesAlgebra I) :=
  reesDegreeOneMonomial I (a : R) a.2

@[simp] theorem reesGenerator_coe :
    ((reesGenerator I a : ↥(reesAlgebra I)) : R[X]) = monomial 1 (a : R) := rfl

theorem reesGenerator_mem_reesGrading : reesGenerator I a ∈ reesGrading I 1 :=
  by
  exact reesMonomial_mem_reesGrading I $ mem_pow_one I $ a.2
end

section
variable (p : ↥(reesAlgebra I)) (i : ℕ)
noncomputable def reesMonomialOfCoeff :
    ↥(reesAlgebra I) :=
  reesMonomial I i ((p : R[X]).coeff i) $ (p.2 i)

theorem reesComponent_coe :
    ((reesMonomialOfCoeff I p i : ↥(reesAlgebra I)) : R[X])
      = monomial i ((p : R[X]).coeff i) := rfl

theorem reesComponent_mem_reesGrading :
    reesMonomialOfCoeff I p i ∈ reesGrading I i := by
  refine (mem_reesGrading_iff_coeff I i _).2 fun j hj => ?_
  rw [reesComponent_coe, coeff_monomial, if_neg $ m113 hj]
end

theorem mem_span_reesGenerator_of_eq_monomial_succ :
    ∀ n r, r ∈ I ^ (n + 1) →
      ∀ x : ↥(reesAlgebra I), (x : R[X]) = monomial (n + 1) r →
        x ∈ span (range $ reesGenerator I) := by
  let _a2 := R[X]
  intro n
  induction n with
  | zero =>
    intro r hr x hx
    have hr' : r ∈ I := by simpa using hr
    have hxe : x = reesGenerator I ⟨r, hr'⟩ := m26 $ tr_ hx rfl
    rw [hxe]
    exact subset_span $ mem_range_self _
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine mul_induction_on'
      (C := fun s _ => ∀ x : (reesAlgebra I),
        (x : _a2) = monomial (n + 1 + 1) s →
          x ∈ span (range $ reesGenerator I)) ?_ ?_ hr
    intro m hm a ha x hx
    let _a1 := reesMonomial I (n + 1) m hm
    let _a0 := monomial (n + 1 + 1) $ m * a
    have hco : ((_a1 * reesGenerator I ⟨a, ha⟩ : (reesAlgebra I)) : _a2)
        = _a0 := by
      show (monomial (n + 1) m : _a2) * monomial 1 a
          = _a0
      rw [monomial_mul_monomial]
    have hxe :=
      m26 $ tr_ hx hco.symm
    rw [hxe]
    exact mul_mem_right _ _ $ ih m hm _a1 rfl
    intro s hs t ht hs' ht' x hx
    have hsm : s ∈ I ^ (n + 1 + 1) := by rw [pow_succ]
                                         exact hs
    have htm : t ∈ I ^ (n + 1 + 1) := by rw [pow_succ]
                                         exact ht
    have hxe : x = reesMonomial I (n + 1 + 1) s hsm
        + reesMonomial I (n + 1 + 1) t htm := by
      refine m26 ?_
      show (x : _a2) = monomial (n + 1 + 1) s + monomial (n + 1 + 1) t
      rw [hx]
      exact map_add (monomial (R := R) $ n + 1 + 1) s t
    rw [hxe]
    exact add_mem (hs' _ rfl) $ ht' _ rfl

theorem reesGrading_irrelevant_le_span :
    (HomogeneousIdeal.irrelevant (reesGrading I)).toIdeal ≤
      span (range (reesGenerator I)) := by
  intro p hp
  have hp1 : p ∈ HomogeneousIdeal.irrelevant (reesGrading I) := hp
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hp1
  let _a1 := support (p : R[X])
  have hsum : p = ∑ i ∈ _a1, reesMonomialOfCoeff I p i := by
    let _a4 := reesAlgebra I
    have hval : ∀ x y,
        _a4.val x = _a4.val y → x = y := fun _ _ h => m26 h
    exact hval _ _ (by rw [map_sum]; exact as_sum_support _)
  let _a0 := GradedRing.proj (reesGrading I) 0
  have hprojsum := hp1
  rw [hsum, map_sum _a0 (fun i => reesMonomialOfCoeff I p i) _a1] at hprojsum
  have hsingle : ∑ i ∈ _a1,
      _a0 (reesMonomialOfCoeff I p i)
      = _a0 (reesMonomialOfCoeff I p 0) := by
    refine sum_eq_single 0 (fun i _ hi => ?_) fun h0 => ?_
    rw [GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_ne (reesGrading I) (reesComponent_mem_reesGrading I p i) hi
    have hc :=
      mp_ not_not fun h => h0 $ mpr_ mem_support_iff h
    have hz : reesMonomialOfCoeff I p 0 = 0 := by
      refine m26 ?_
      show monomial 0 ((p : R[X]).coeff 0) = (0 : R[X])
      rw [hc, map_zero]
    rw [hz, map_zero]
  have hz0 : reesMonomialOfCoeff I p 0 = 0 := by
    have h1 : _a0 (reesMonomialOfCoeff I p 0) = 0 := by
      rwa [← hsingle]
    rw [GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same (reesGrading I) (reesComponent_mem_reesGrading I p 0)] at h1
    exact h1
  rw [hsum]
  refine sum_mem fun i _ => ?_
  rcases m73 i with rfl | hi
  rw [hz0]
  exact zero_mem _
  obtain ⟨k, rfl⟩ := exists_eq_succ_of_ne_zero hi.ne'
  exact mem_span_reesGenerator_of_eq_monomial_succ I k ((p : R[X]).coeff (k + 1))
    (p.2 (k + 1)) (reesMonomialOfCoeff I p (k + 1))
    (reesComponent_coe I p (k + 1))

noncomputable def reesDegreeZeroMonomial (r : R) : ↥(reesGrading I 0) :=
  ⟨reesMonomial I 0 r $ mem_pow_zero I r,
    reesMonomial_mem_reesGrading I $ mem_pow_zero I r⟩

noncomputable def reesDegreeZeroRingHom : R →+* ↥(reesGrading I 0) where
  toFun := reesDegreeZeroMonomial I
  map_one' := by
    refine m26 $ m26 ?_
    exact monomial_zero_one
  map_mul' := by
    intro r s
    exact m26 $ m26 $ (monomial_mul_monomial 0 0 r s).symm
  map_zero' := by
    refine m26 $ m26 ?_
    show (monomial 0 (0 : R) : R[X]) = 0
    rw [map_zero]
  map_add' := by
    intro r s
    exact m26 $ m26 $ map_add (monomial (R := R) 0) r s

@[simp] theorem reesDegreeZeroRingHom_coe_coe (r : R) :
    ((reesDegreeZeroRingHom I r : ↥(reesAlgebra I)) : R[X]) = Polynomial.C r := by
  show (monomial 0 r : R[X]) = m141 r
  simp

theorem reesDegreeZeroRingHom_injective :
    Injective $ reesDegreeZeroRingHom I := by
  intro r s h
  simpa using (congrArg (fun p : R[X] => p.coeff 0) $ congrArg (fun x : (reesGrading I 0) => ((x : (reesAlgebra I)) : R[X])) h)

theorem reesDegreeZeroRingHom_surjective :
    Function.Surjective $ reesDegreeZeroRingHom I := by
  rintro ⟨x, hx⟩
  let _m0 := ((x : (reesAlgebra I)) : R[X])
  refine ⟨_m0.coeff 0, m26 $ m26 ?_⟩
  show (monomial 0 (_m0.coeff 0) : R[X])
      = _m0
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  simp
  rw [coeff_monomial, if_neg $ m113 hi]
  exact sy_ $ ((mem_reesGrading_iff_coeff I 0 x).1 hx) i hi

noncomputable def reesDegreeZeroEquiv : R ≃+* ↥(reesGrading I 0) :=
  RingEquiv.ofBijective (reesDegreeZeroRingHom I) $ (⟨reesDegreeZeroRingHom_injective I, reesDegreeZeroRingHom_surjective I⟩)

@[simp] theorem reesDegreeZeroEquiv_apply (r : R) :
    reesDegreeZeroEquiv I r = reesDegreeZeroRingHom I r := rfl

theorem reesDegreeZeroEquiv_coe_coe (r : R) :
    ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)) : R[X]) = m141 r :=by simp_all
end

end FunctorialResolution.Blowup
end
section

namespace FunctorialResolution.Blowup


variable {R : Type} [CommRing R]

theorem reesGenerator_coe_eq_C_mul_X (I : Ideal R) (a : ↥I) :
    ((reesGenerator I a : ↥(reesAlgebra I)) : Polynomial R) =
      m141 (a : R) * Polynomial.X := by
  rw [reesGenerator_coe, ← C_mul_X_pow_eq_monomial, pow_one]

theorem localization_mk_eq_zero_iff {A : Type} [CommRing A] {M : Submonoid A} (x : A)
    (s : ↥M) : Localization.mk x s = (0 : Localization M) ↔ ∃ c : ↥M, (c : A) * x = 0 := by
  rw [mk_eq_mk']
  exact mk'_eq_zero_iff x s

noncomputable def affineBlowup (I : Ideal R) : Sch :=
  Proj $ reesGrading I


namespace AffineBlowup

noncomputable def toSpec (I : Ideal R) :
    affineBlowup I ⟶ Sp R :=
  toSpecZero (reesGrading I) ≫
    AlgebraicGeometry.Spec.map
      (ofHom
        ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0)))

theorem toSpec_eq_toSpecZero_comp (I : Ideal R) :
    toSpec I =
      toSpecZero (reesGrading I) ≫
        AlgebraicGeometry.Spec.map
          (ofHom
            ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0))) := rfl

end AffineBlowup

section
variable (I : Ideal R) (a : ↥I)
noncomputable def affineBlowupChart :
    Spec
        (m10 $ HomogeneousLocalization.Away (reesGrading I) $ reesGenerator I a) ⟶
      affineBlowup I :=
  AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
    m176

theorem affineBlowupChart_eq_awayio :
    affineBlowupChart I a =
      AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
        m176 := rfl
end

instance instIsOpenImmersionAffineBlowupChart (I : Ideal R) (a : ↥I) :
    IsOpenImmersion $ affineBlowupChart I a :=
  inferInstanceAs $ AlgebraicGeometry.IsOpenImmersion
    (AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
      m176)

section
variable (I : Ideal R)
section
variable (a : ↥I)
theorem opensRange_affineBlowupChart_eq_basicOpen :
    (affineBlowupChart I a).opensRange =
      basicOpen (reesGrading I) (reesGenerator I a) :=
  AlgebraicGeometry.Proj.opensRange_awayι ..

noncomputable def chartRingHom :
    R →+* HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a) :=
  (fromZeroRingHom (reesGrading I)
      (powers $ reesGenerator I a)).comp
    ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0))

theorem chartRingHom_apply r :
    chartRingHom I a r =
      fromZeroRingHom (reesGrading I) (powers $ reesGenerator I a)
        (reesDegreeZeroEquiv I r) := rfl

private theorem val_chartRingHom (r : R) :
    HomogeneousLocalization.val (chartRingHom I a r) =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesAlgebra I)))
        (1 : ↥(powers $ reesGenerator I a)) := rfl
end

theorem iSup_proj_basicOpen_reesGenerator_eq_top :
    (⨆ a : ↥I, basicOpen (reesGrading I) (reesGenerator I a)) = ⊤ := by
  apply iSup_basicOpen_eq_top
  exact reesGrading_irrelevant_le_span I

theorem exists_mem_range_affineBlowupChart x :
    ∃ a, x ∈ range (affineBlowupChart I a).base := by
  have h2 : (⋃ a : I,
      ((basicOpen (reesGrading I) (reesGenerator I a) :
          (Proj $ reesGrading I).Opens) :
        Set $ Proj $ reesGrading I)) = univ := by
    rw [← coe_iSup, iSup_proj_basicOpen_reesGenerator_eq_top]
    simp
  have hx : x ∈ (⋃ a : I,
      ((basicOpen (reesGrading I) (reesGenerator I a) :
          (Proj $ reesGrading I).Opens) :
        Set $ Proj $ reesGrading I)) := by
    rw [h2]
    exact mem_univ _
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  refine ⟨a, ?_⟩
  have hs : range (affineBlowupChart I a).base =
      ((basicOpen (reesGrading I) (reesGenerator I a) :
          (Proj $ reesGrading I).Opens) :
        Set $ Proj $ reesGrading I) :=
    congrArg (fun U : Opn (affineBlowup I) => opS U)
      (opensRange_affineBlowupChart_eq_basicOpen I a)
  rwa [hs]

noncomputable def affineBlowupAffineOpenCover : (affineBlowup I).AffineOpenCover where
  I₀ := ↥I
  X a := CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) $ reesGenerator I a)
  f a := affineBlowupChart I a
  idx x := (exists_mem_range_affineBlowupChart I x).choose
  covers x := (exists_mem_range_affineBlowupChart I x).choose_spec
  map_prop a := instIsOpenImmersionAffineBlowupChart I a
end

noncomputable instance AffineBlowup.instAlgebraChart (I : Ideal R) (a : ↥I) :
    Algebra R $ HomogeneousLocalization.Away (reesGrading I) $ reesGenerator I a :=
  toAlgebra $ chartRingHom I a

section
variable (I : Ideal R)
section
variable (a : ↥I)
theorem algebraMap_chart_eq_chartRingHom :
    @algebraMap R (HomogeneousLocalization.Away (reesGrading I) $ reesGenerator I a) _ _
        (AffineBlowup.instAlgebraChart I a) =
      chartRingHom I a := rfl


theorem affineBlowupChart_comp_toSpec :
    affineBlowupChart I a ≫ AffineBlowup.toSpec I =
      AlgebraicGeometry.Spec.map
        (ofHom
          (@algebraMap R (HomogeneousLocalization.Away (reesGrading I) $ reesGenerator I a) _ _
            (AffineBlowup.instAlgebraChart I a))) := by
  let _a0 := reesGenerator I a
  show AlgebraicGeometry.Proj.awayι (reesGrading I) _a0 (reesGenerator_mem_reesGrading I a)
        m176 ≫
      (AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
        m12
          (ofHom
            ((reesDegreeZeroEquiv I : R ≃+* (reesGrading I 0)) : R →+* (reesGrading I 0)))) =
      m12
        (ofHom
          (@algebraMap R (HomogeneousLocalization.Away (reesGrading I) _a0) _ _
            (AffineBlowup.instAlgebraChart I a)))
  rw [← assoc, AlgebraicGeometry.Proj.awayι_toSpecZero,
    ← map_comp]
  rfl

theorem reesGenerator_pow_one_mem_reesGrading_one :
    reesGenerator I a ^ 1 ∈ reesGrading I 1 := by
  rw [pow_one]
  exact reesGenerator_mem_reesGrading I a

theorem chartRingHom_mem_nonZeroDivisors :
    chartRingHom I a (a : R) ∈
      nonZeroDivisors (HomogeneousLocalization.Away (reesGrading I) $ reesGenerator I a) := by
  have key : ∀ z : HomogeneousLocalization.Away (reesGrading I) $ reesGenerator I a,
      chartRingHom I a (a : R) * z = 0 → z = 0 := by
    intro z hz
    have hz' : HomogeneousLocalization.val (chartRingHom I a (a : R) * z) = 0 := by simp_all
    rw [val_mul, val_chartRingHom,
      eq_num_div_den z, mk_mul,
      localization_mk_eq_zero_iff] at hz'
    obtain ⟨c, hc⟩ := hz'
    obtain ⟨m, hm⟩ := c.2
    rw [← hm] at hc
    have hP : reesGenerator I a ^ (m + 1) * HomogeneousLocalization.num z = 0 := by
      apply m26
      have h1 := congrArg (fun p : (reesAlgebra I) => (p : Polynomial R)) hc
      push_cast [reesGenerator_coe_eq_C_mul_X, reesDegreeZeroEquiv_coe_coe] at h1
      push_cast [reesGenerator_coe_eq_C_mul_X]
      linear_combination (Polynomial.X : Polynomial R) * h1
    rw [ext_iff_val, val_zero,
      eq_num_div_den z, localization_mk_eq_zero_iff]
    exact ⟨⟨reesGenerator I a ^ (m + 1), Submonoid.pow_mem _ (mem_powers _) $ m + 1⟩, hP⟩
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun z hz => key z $ tr_ (mul_comm (chartRingHom I a (a : R)) z) hz⟩
end

section
variable (a b : ↥I)
noncomputable def chartFraction :
    HomogeneousLocalization.Away (reesGrading I) $ reesGenerator I a :=
  HomogeneousLocalization.mk
    { deg := 1
      num := ⟨reesGenerator I b, reesGenerator_mem_reesGrading I b⟩
      den := ⟨reesGenerator I a ^ 1, reesGenerator_pow_one_mem_reesGrading_one I a⟩
      den_mem := (Submonoid.pow_mem _ (mem_powers _) 1) }

theorem chartFraction_eq_mk :
    chartFraction I a b =
      HomogeneousLocalization.mk
        { deg := 1
          num := ⟨reesGenerator I b, reesGenerator_mem_reesGrading I b⟩
          den := ⟨reesGenerator I a ^ 1, reesGenerator_pow_one_mem_reesGrading_one I a⟩
          den_mem := Submonoid.pow_mem _ (mem_powers _) 1 } := rfl

theorem chartRingHom_coe_eq_chartFraction_mul :
    chartRingHom I a (b : R) = chartFraction I a b * chartRingHom I a (a : R) := by
  rw [ext_iff_val, val_mul,
    val_chartRingHom, val_chartRingHom, chartFraction_eq_mk, HomogeneousLocalization.val_mk,
    mk_mul, mk_eq_mk_iff, r_iff_exists]
  refine ⟨1, ?_⟩
  apply m26
  push_cast [reesGenerator_coe_eq_C_mul_X, reesDegreeZeroEquiv_coe_coe]
  ring
end

theorem map_chartRingHom_eq_span_singleton (a : ↥I) :
    Ideal.map (chartRingHom I a) I = span {chartRingHom I a (a : R)} := by
  apply le_antisymm
  rw [map_le_iff_le_comap]
  intro x hx
  rw [mem_comap, mem_span_singleton']
  exact ⟨chartFraction I a ⟨x, hx⟩, sy_ $ chartRingHom_coe_eq_chartFraction_mul I a ⟨x, hx⟩⟩
  rw [span_le, singleton_subset_iff]
  exact mem_map_of_mem _ a.2
end

end FunctorialResolution.Blowup
end
section

namespace FunctorialResolution.Blowup


variable {R : Type} [CommRing R]

section
variable (I : Ideal R)
theorem algebraMap_degreeZero_apply x :
    algebraMap ↥(reesGrading I 0) ↥(reesAlgebra I) x = (x : ↥(reesAlgebra I)) := rfl

theorem algebraMap_reesAlgebra_eq_algebraMap_degreeZero r :
    algebraMap R ↥(reesAlgebra I) r =
      algebraMap ↥(reesGrading I 0) ↥(reesAlgebra I) (reesDegreeZeroEquiv I r) := by
  apply m26
  rw [algebraMap_degreeZero_apply, reesDegreeZeroEquiv_coe_coe]
  rfl

section
variable (s : Set ↥(reesAlgebra I))
noncomputable def adjoinOverDegreeZero :
    Subalgebra R ↥(reesAlgebra I) where
  toSubsemiring := (adjoin ↥(reesGrading I 0) s).toSubsemiring
  algebraMap_mem' := fun r => by
    rw [algebraMap_reesAlgebra_eq_algebraMap_degreeZero]
    exact Subalgebra.algebraMap_mem (adjoin ↥(reesGrading I 0) s) _

theorem mem_restrictScalars_of_mem_adjoin_degreeZero
    x (hx : x ∈ adjoin ↥(reesGrading I 0) s) :
    x ∈ adjoinOverDegreeZero I s := hx

theorem adjoin_le_adjoin_degreeZero :
    adjoin R s ≤ adjoinOverDegreeZero I s := by
  refine adjoin_le ?_
  intro y hy
  rw [mem_coe]
  exact mem_restrictScalars_of_mem_adjoin_degreeZero I s y $ subset_adjoin hy

theorem adjoin_degreeZero_eq_top_of_adjoin_eq_top
    (hs : adjoin R s = ⊤) : adjoin ↥(reesGrading I 0) s = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ adjoin R s := by simp_all
  exact adjoin_le_adjoin_degreeZero I s hx
end
end

theorem isProper_comp_of_isIso {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProper f) (hg : IsIso g) :
    IsProper $ f ≫ g := by
  infer_instance

theorem isProper_affineBlowup_toSpec (I : Ideal R) [IsNoetherianRing R] :
    IsProper $ AffineBlowup.toSpec I := by
  let _a0 := reesAlgebra I
  have hft : FiniteType (reesGrading I 0) _a0 :=
    by
    obtain ⟨s, hs⟩ := (inferInstance : FiniteType R _a0).out
    exact ⟨⟨s, adjoin_degreeZero_eq_top_of_adjoin_eq_top I (s : Set _a0) hs⟩⟩
  have h1 : IsProper $ toSpecZero $ reesGrading I :=
    inferInstance
  rw [AffineBlowup.toSpec_eq_toSpecZero_comp]
  exact isProper_comp_of_isIso _ _ h1 $ mpr_ isIso_SpecMap_iff (reesDegreeZeroEquiv I).bijective








end FunctorialResolution.Blowup
end
section


namespace FunctorialResolution.Blowup

universe v

section

variable {R : Type} {S : Type v} [CommRing R] [CommRing S]

section
variable (ph_ : R →+* S) (s : S)
def polynomialEvalInvSelf : Polynomial R →+* Away s :=
  Polynomial.eval₂RingHom
    (((algebraMap S $ Away s) : S →+* Away s).comp ph_)
    (invSelf s)

theorem polynomialEvalInvSelf_monomial (n : ℕ) (r : R) :
    polynomialEvalInvSelf ph_ s (monomial n r) =
      algebraMap S (Away s) (ph_ r) * invSelf s ^ n := by
  simp [polynomialEvalInvSelf]
end

theorem algebraMap_mul_invSelf {T : Type v} [CommRing T] (t : T) :
    algebraMap T (Away t) t * invSelf t = 1 := by
  have h : invSelf t
      = Localization.mk 1 ⟨t, mem_powers t⟩ := rfl
  rw [h, mk_eq_mk', mul_comm, mk'_spec, map_one]

section
variable (I : Ideal R) (ph_ : R →+* S) (s : S) (hI : Ideal.map ph_ I = span {s})
include hI
theorem exists_mul_pow_of_mem_pow n r (hr : r ∈ I ^ n) :
    ∃ c, ph_ r = c * s ^ n := by
  have hmem : ph_ r ∈ span {s ^ n} := by
    have h1 := mem_map_of_mem ph_ hr
    rwa [m219, hI, span_singleton_pow] at h1
  obtain ⟨c, hc⟩ := mp_ mem_span_singleton hmem
  exact ⟨c, by rw [hc, mul_comm]⟩

theorem exists_algebraMap_eq_polynomialEvalInvSelf (p : ↥(reesAlgebra I)) :
    ∃ c, algebraMap S (Away s) c = polynomialEvalInvSelf ph_ s (p : Polynomial R) := by
  let _a0 := (p : Polynomial R)
  have hmem : ∀ i, _a0.coeff i ∈ I ^ i := by
    have hp := p.2
    rwa [mem_reesAlgebra_iff] at hp
  have key := fun i =>
    exists_mul_pow_of_mem_pow I ph_ s hI i (_a0.coeff i) $ hmem i
  choose c hc using key
  refine ⟨∑ i ∈ m65 (_a0.natDegree + 1), c i, ?_⟩
  have hEval : polynomialEvalInvSelf ph_ s (p : Polynomial R) =
      Polynomial.eval₂
        (((algebraMap S $ Away s) : S →+* Away s).comp ph_)
        (invSelf s) p := rfl
  rw [map_sum, hEval, Polynomial.eval₂_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  rw [comp_apply, hc i, map_mul, map_pow, mul_assoc, ← mul_pow,
    algebraMap_mul_invSelf s, one_pow, mul_one]

def reesAlgebraLiftFun (_hs : s ∈ nonZeroDivisors S)
    (p : ↥(reesAlgebra I)) : S :=
  (exists_algebraMap_eq_polynomialEvalInvSelf I ph_ s hI p).choose

section
variable (hs : s ∈ nonZeroDivisors S)
theorem algebraMap_reesAlgebraLiftFun
    (p : ↥(reesAlgebra I)) :
    algebraMap S (Away s) (reesAlgebraLiftFun I ph_ s hI hs p) =
      polynomialEvalInvSelf ph_ s (p : Polynomial R) :=
  (exists_algebraMap_eq_polynomialEvalInvSelf I ph_ s hI p).choose_spec

section
variable (p q : ↥(reesAlgebra I))
theorem reesAlgebraLiftFun_mul :
    reesAlgebraLiftFun I ph_ s hI hs (p * q) = reesAlgebraLiftFun I ph_ s hI hs p * reesAlgebraLiftFun I ph_ s hI hs q := by
  have hM : powers s ≤ nonZeroDivisors S := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact pow_mem hs n
  apply injective (S := Away s) (M := powers s) hM
  have hcoe : ((p * q : (reesAlgebra I)) : Polynomial R)
      = p * q := rfl
  rw [map_mul, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, hcoe, map_mul]

theorem reesAlgebraLiftFun_add :
    reesAlgebraLiftFun I ph_ s hI hs (p + q) = reesAlgebraLiftFun I ph_ s hI hs p + reesAlgebraLiftFun I ph_ s hI hs q := by
  have hM : powers s ≤ nonZeroDivisors S := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact pow_mem hs n
  apply injective (S := Away s) (M := powers s) hM
  have hcoe : ((p + q : (reesAlgebra I)) : Polynomial R)
      = p + q := rfl
  rw [map_add, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, algebraMap_reesAlgebraLiftFun, hcoe, map_add]
end

def reesAlgebraLift :
    ↥(reesAlgebra I) →+* S where
  toFun := reesAlgebraLiftFun I ph_ s hI hs
  map_one' := by
    have hinj :=
      injective (Away s) $ mpr powers_le hs
    apply hinj
    rw [algebraMap_reesAlgebraLiftFun I ph_ s hI hs 1]
    simp
  map_mul' := reesAlgebraLiftFun_mul I ph_ s hI hs
  map_zero' := by
    have hinj :=
      injective (Away s) $ mpr powers_le hs
    apply hinj
    rw [algebraMap_reesAlgebraLiftFun I ph_ s hI hs 0]
    simp
  map_add' := reesAlgebraLiftFun_add I ph_ s hI hs

theorem reesAlgebraLift_apply
    (p : ↥(reesAlgebra I)) :
    reesAlgebraLift I ph_ s hI hs p = reesAlgebraLiftFun I ph_ s hI hs p := rfl

theorem reesAlgebraLift_reesGenerator
    (a : ↥I) (ha : ph_ (a : R) = s) :
    reesAlgebraLift I ph_ s hI hs (reesGenerator I a) = 1 := by
  apply injective (Away s) $ mpr_ powers_le hs
  rw [reesAlgebraLift_apply, algebraMap_reesAlgebraLiftFun I ph_ s hI hs, reesGenerator_coe, polynomialEvalInvSelf_monomial, ha,
    pow_one, algebraMap_mul_invSelf,
    map_one $ algebraMap S $ Away s]

theorem reesAlgebraLift_algebraMap r :
    reesAlgebraLift I ph_ s hI hs (algebraMap R ↥(reesAlgebra I) r) = ph_ r := by
  apply injective (Away s) $ mpr_ powers_le hs
  rw [reesAlgebraLift_apply, algebraMap_reesAlgebraLiftFun I ph_ s hI hs]
  have hcoe : ((algebraMap R (reesAlgebra I) r : (reesAlgebra I)) : Polynomial R)
      = m141 r := rfl
  rw [hcoe]
  simp [polynomialEvalInvSelf]
end
end

end

section

variable {R : Type} [CommRing R]

section
variable {W} (g : W ⟶ Sp R)
def globalSectionsRingHom : R →+* Γ(W, ⊤) :=
  (inv (GSpecIso $ CommRingCat.of R) ≫ appTop g).hom

theorem globalSectionsRingHom_eq :
    globalSectionsRingHom g = (inv (GSpecIso $ CommRingCat.of R) ≫ appTop g).hom := rfl
end

section
variable {B : Type} [CommRing B] (J : Ideal B)
def homogeneousLocalizationAwayVal (a : ↥J) :
    HomogeneousLocalization.Away (reesGrading J) (reesGenerator J a) →+*
      Away (reesGenerator J a) where
  toFun := HomogeneousLocalization.val
  map_one' := by simp
  map_mul' := fun p q => by simp
  map_zero' := by simp
  map_add' := fun p q => by simp

theorem homogeneousLocalizationAwayVal_apply a
    p :
    homogeneousLocalizationAwayVal J a p = HomogeneousLocalization.val p := rfl

section
variable {T : Type v} [CommRing T] (ph_ : B →+* T) (a : ↥J) (hgen : Ideal.map ph_ J = span {ph_ (a : B)}) (hnzd : ph_ (a : B) ∈ nonZeroDivisors T)
theorem isUnit_reesAlgebraLift_powers :
    ∀ y : powers $ reesGenerator J a,
      IsUnit $ reesAlgebraLift J ph_ (ph_ (a : B)) hgen hnzd (y : ↥(reesAlgebra J)) := by
  intro y
  obtain ⟨n, hn⟩ := y.2
  rw [sy_ hn, map_pow, reesAlgebraLift_reesGenerator J ph_ (ph_ a) hgen hnzd a rfl, one_pow]
  exact isUnit_one

def homogeneousAwayLift :
    HomogeneousLocalization.Away (reesGrading J) (reesGenerator J a) →+* T :=
  RingHom.comp
    (IsLocalization.lift (S := Away $ reesGenerator J a)
      (g := reesAlgebraLift J ph_ (ph_ (a : B)) hgen hnzd) $ isUnit_reesAlgebraLift_powers J ph_ a hgen hnzd)
    (homogeneousLocalizationAwayVal J a)

theorem homogeneousAwayLift_chartRingHom (r : B) :
    homogeneousAwayLift J ph_ a hgen hnzd (chartRingHom J a r) = ph_ r := by
  have hcoe : ((algebraMap B (reesAlgebra J) r : (reesAlgebra J)) : Polynomial B)
      = m141 r := rfl
  let _m0 := ((reesDegreeZeroEquiv J r : (reesGrading J 0)) : (reesAlgebra J))
  have h1 : _m0
      = algebraMap B (reesAlgebra J) r := by
    apply m26
    rw [reesDegreeZeroEquiv_coe_coe, hcoe]
  have hz : HomogeneousLocalization.val
        (fromZeroRingHom (reesGrading J)
          (powers $ reesGenerator J a) $ reesDegreeZeroEquiv J r)
      = Localization.mk _m0 1 := rfl
  unfold homogeneousAwayLift
  rw [comp_apply, homogeneousLocalizationAwayVal_apply, chartRingHom_apply, hz, h1, mk_one_eq_algebraMap, lift_eq,
    reesAlgebraLift_algebraMap]
end
end

theorem exists_lift_affineBlowup (I : Ideal R) {W : Sch} [IsAffine W]
    (g : W ⟶ Sp R) (a : ↥I)
    (hgen : Ideal.map (globalSectionsRingHom g) I = span {globalSectionsRingHom g (a : R)})
    (hnzd : globalSectionsRingHom g (a : R) ∈ nonZeroDivisors Γ(W, ⊤)) :
    ∃ h : W ⟶ affineBlowup I,
      h ≫ AffineBlowup.toSpec I = g ∧
        range h.base ⊆ range (affineBlowupChart I a).base := by
  let _a0 := ofHom $ homogeneousAwayLift I (globalSectionsRingHom g) a hgen hnzd
  let _a1 := ofHom $ chartRingHom I a
  refine ⟨W.toSpecΓ ≫
      m12 _a0 ≫
        affineBlowupChart I a, ?_, ?_⟩
  have h2 : affineBlowupChart I a ≫ AffineBlowup.toSpec I
      = m12 _a1 := by
    rw [affineBlowupChart_comp_toSpec, algebraMap_chart_eq_chartRingHom]
  have h3 : _a1 ≫
        _a0
      = ofHom (globalSectionsRingHom g) := by
    rw [← ofHom_comp]
    exact congrArg ofHom
      (m48 fun r => homogeneousAwayLift_chartRingHom I (globalSectionsRingHom g) a hgen hnzd r)
  have nat : W.toSpecΓ ≫ m12 g.appTop = g ≫ (Sp R).toSpecΓ := by
    rw [Scheme.toSpecΓ_naturality]
  have tri : (Sp R).toSpecΓ ≫
      m12 (GSpecIso $ m10 R).inv = 𝟙 (Sp R) := by
    simp
  rw [assoc, assoc, h2, ← map_comp, h3, globalSectionsRingHom_eq,
    ofHom_hom, map_comp, ← assoc, nat, assoc, tri,
    comp_id]
  rintro x ⟨w, rfl⟩
  exact ⟨bsM (W.toSpecΓ ≫
    m12 _a0) w,
    by simp⟩

end

end FunctorialResolution.Blowup
end
section
open CategoryTheory.Limits TopologicalSpace Opposite

namespace FunctorialResolution.Blowup

section

section
variable {X' X : Sch} (f : X' ⟶ X)
def exceptionalIdeal (Z : ISD X) :
    IdealSheafData X' :=
  Z.comap f

theorem exceptionalIdeal_eq_comap (Z : ISD X) :
    exceptionalIdeal f Z = Z.comap f := rfl

section
variable (Z J : ISD X)
def strictTransformOpens :
    (subscheme $ J.comap f).Opens :=
  subschemeι (J.comap f) ⁻¹ᵁ (Z.comap f).support.compl

theorem strictTransformOpens_eq :
    strictTransformOpens f Z J =
      subschemeι (J.comap f) ⁻¹ᵁ (Z.comap f).support.compl := rfl

def strictTransformImmersion :
    toScheme (strictTransformOpens f Z J) ⟶ X' :=
  ι (strictTransformOpens f Z J) ≫ subschemeι (J.comap f)

theorem strictTransformImmersion_eq :
    strictTransformImmersion f Z J =
      ι (strictTransformOpens f Z J) ≫ subschemeι (J.comap f) := rfl

def strictTransform :
    IdealSheafData X' :=
  (strictTransformImmersion f Z J).ker

theorem strictTransform_eq_ker :
    strictTransform f Z J = (strictTransformImmersion f Z J).ker := rfl
end
end

def schemeImageIdeal {X Y : Sch} (f : X ⟶ Y) (I : ISD X) : ISD Y :=
  (subschemeι I ≫ f).ker


theorem isClosedImmersion_lift_comp {X Y Z : Sch} (f : X ⟶ Z) [IsClosedImmersion f] (g : Y ⟶ Z)
    (h : ker f ≤ ker g) : IsClosedImmersion.lift f g h ≫ f = g := by
  simp

section
variable {X Y : Sch} (f : X ⟶ Y) [IsClosedImmersion f] (I : ISD X)
theorem comap_ker_subschemeio_comp :
    ((subschemeι I ≫ f).ker).comap f = I := by
  rw [ker_comp, q2]
  refine le_antisymm (comap_map_le I f) ?_
  let _a0 := siI I ≫ f
  have hle : _a0.ker ≤ ker (I.map f).si :=
    le_of_eq $ by
      rw [q2, ker_comp,
        q2]
  have hcomap : (I.map f).comap f =
      ker (pullback.fst f (I.map f).si) := rfl
  rw [hcomap]
  refine le_trans (le_of_eq (q2 I).symm) ?_
  let g := siI $ I.map f
  let ι := siI I
  let m := m64 _a0 (I.map f).si hle
  have hu : pullback.snd f g ≫ m ≫ ι = pullback.fst f g := by
    rw [← cancel_mono f]
    simp [assoc]
    rw [isClosedImmersion_lift_comp _a0 (I.map f).si hle, pullback.condition]
  rw [← hu]
  exact le_trans (le_ker_comp m ι)
    (le_ker_comp (pullback.snd f g) $ m ≫ ι)

theorem comap_schemeImageIdeal : (schemeImageIdeal f I).comap f = I :=
  comap_ker_subschemeio_comp f I
end

theorem comap_le_strictTransform {X X1 : Sch} (p : X1 ⟶ X) (Z D : ISD X) :
    D.comap p ≤ strictTransform p Z D := by
  rw [strictTransform_eq_ker, strictTransformImmersion_eq]
  have h := le_ker_comp (strictTransformOpens p Z D).i (cmI D p).si
  rwa [q2] at h

end

end FunctorialResolution.Blowup
end
section

universe v

open CategoryTheory.Limits Opposite

section

namespace FunctorialResolution.Blowup

def IsLocallyGeneratedByNonZeroDivisor {X : Sch} (I : ISD X) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U.1)),
    x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧ I.ideal U = span {f}

def IsBlowupAlongIdealSheaf {X X' : Sch} (pi_ : X' ⟶ X) (I : ISD X) : Prop :=
  IsLocallyGeneratedByNonZeroDivisor (I.comap pi_) ∧
    ∀ (W : Sch) (g : W ⟶ X), IsLocallyGeneratedByNonZeroDivisor (I.comap g) →
      ∃! h : W ⟶ X', h ≫ pi_ = g

end FunctorialResolution.Blowup

end

end
section

universe v

open CategoryTheory.Limits Opposite

section

namespace FunctorialResolution.EmbeddedResolution

structure SequenceOfBlowups (X : Sch) : Type 1 where
  length : ℕ
  tower : ℕᵒᵖ ⥤ Sch
  isoZero : tower.obj (op 0) ≅ X
  center : ∀ i : ℕ, IdealSheafData $ tower.obj $ op i
  isBlowup : ∀ i : ℕ, i < length →
    Blowup.IsBlowupAlongIdealSheaf (tower.map (homOfLE $ le_succ i).op) (center i)

namespace SequenceOfBlowups

variable {X : Sch}

section
variable (s : SequenceOfBlowups X)
abbrev schemeAt (i : ℕ) : Sch := s.tower.obj $ op i

def transitionMap {i i' : ℕ} (h : i ≤ i') : s.schemeAt i' ⟶ s.schemeAt i :=
  s.tower.map (homOfLE h).op

def transitionMapSucc (i : ℕ) : s.schemeAt (i + 1) ⟶ s.schemeAt i :=
  s.transitionMap $ le_succ i

def projectionToBase (i : ℕ) : s.schemeAt i ⟶ X :=
  s.transitionMap (zero_le i) ≫ s.isoZero.hom

abbrev lastObj : Sch := s.schemeAt s.length

def lastStructMap : s.lastObj ⟶ X := s.projectionToBase s.length

theorem transitionMap_comp_projectionToBase {i i' : ℕ} (h : i ≤ i') :
    s.transitionMap h ≫ s.projectionToBase i = s.projectionToBase i' :=
  m32 (assoc (s.transitionMap h) (s.transitionMap $ zero_le i) s.isoZero.hom).symm
    (congrArg (fun g => g ≫ s.isoZero.hom)
      (show s.transitionMap h ≫ s.transitionMap (zero_le i) = s.transitionMap (zero_le i') from
        sy_ $ s.tower.map_comp (homOfLE h).op (homOfLE $ zero_le i).op))

def pullbackTransitionMap {X' : Sch} (ph_ : X' ⟶ X) {i i' : ℕ} (h : i ≤ i') :
    pullback ph_ (s.projectionToBase i') ⟶ pullback ph_ (s.projectionToBase i) :=
  pullback.map ph_ (s.projectionToBase i') ph_ (s.projectionToBase i) (𝟙 X') (s.transitionMap h) (𝟙 X)
    ((comp_id ph_).trans (id_comp ph_).symm)
    ((comp_id $ s.projectionToBase i').trans (s.transitionMap_comp_projectionToBase h).symm)

def CentersLieOver (S : Set X) : Prop :=
  ∀ i : ℕ, i < length s → ∀ x ∈ support (s.center i), (s.projectionToBase i).base x ∈ S
end

end SequenceOfBlowups

def smoothLocusComplement {X Y : Sch} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Closeds X :=
  ⟨(f.smoothLocus : Set X)ᶜ, mpr isClosed_compl_iff f.smoothLocus.isOpen⟩

def reducedInverseImage {X X' : Sch} (f : X' ⟶ X) (S : Closeds X) :
    IdealSheafData X' :=
  vanishingIdeal
    ⟨f.base ⁻¹' (S : Set X), IsClosed.preimage f.base.hom.continuous S.2⟩

def IsRegularParameterSystem (R : Type v) [CommRing R] [IsLocalRing R] (n : ℕ)
    (x : Fin n → R) : Prop :=
  span (range x) = maximalIdeal R ∧ (n : WithBot ENat) = ringKrullDim R

def IsStrictNormalCrossingsDivisor {Y : Sch} (D : ISD Y) : Prop :=
  ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) ∧
    ∃ (U : Y.affineOpens) (hy : y ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y, U.1)) (J : FinSet n),
      IsRegularParameterSystem (Y.presheaf.stalk y) n
          (fun i => Y.presheaf.germ U.1 y hy $ f i) ∧
        D.ideal U = span {∏ i ∈ J, f i}

def IsPullbackBlowupSequence {X X' : Sch} (ph_ : X' ⟶ X) (s' : SequenceOfBlowups X') (s : SequenceOfBlowups X) :
    Prop :=
  ∃ (r : ℕ → ℕ)
    (e : ∀ i, i ≤ s'.length →
      @Iso Sch _ (s'.schemeAt i) (pullback ph_ $ s.projectionToBase $ r i)),
    (∀ i, i < s'.length → r i < s.length) ∧
    (∀ i j, j ≤ s'.length → i < j → r i < r j) ∧
    r s'.length = s.length ∧
    (∀ i, i < s.length →
      ((∃ x, x ∈ ((s.center i).comap $ pullback.snd ph_ $ s.projectionToBase i).support) ↔
        ∃ j, j < s'.length ∧ r j = i)) ∧
    (∀ i, ∀ hi : i ≤ s'.length,
      (e i hi).hom ≫ pullback.fst ph_ (s.projectionToBase $ r i) = s'.projectionToBase i) ∧
    (∀ i, ∀ hi : i < s'.length, ∀ hr : r i ≤ r (i + 1),
      s'.transitionMapSucc i ≫ (e i hi.le).hom = (e (i + 1) hi).hom ≫ s.pullbackTransitionMap ph_ hr) ∧
    (∀ i, ∀ hi : i < s'.length,
      s'.center i
        = (s.center $ r i).comap ((e i hi.le).hom ≫ pullback.snd ph_ (s.projectionToBase $ r i)))

abbrev specMapAlgebraMap (k K : Type) [Field k] [Field K] [Algebra k K] :
    Sp K ⟶ Sp k :=
  Spec.map $ ofHom $ algebraMap k K

section
variable {X} {k : Type} [Field k] (p : X ⟶ Sp k) (K : Type) [Field K] [Algebra k K]
abbrev baseChange : Sch :=
  pullback p $ specMapAlgebraMap k K

abbrev baseChangeProjection : baseChange p K ⟶ X :=
  pullback.fst p $ specMapAlgebraMap k K

abbrev baseChangeToSpec :
    baseChange p K ⟶ Sp K :=
  pullback.snd p $ specMapAlgebraMap k K
end

abbrev ResolutionRule : Type 1 :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Sch)
    (f : X ⟶ Sp k) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsReduced X],
    SequenceOfBlowups X

section
variable (R : ResolutionRule)
def IsStrongResolutionRule : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Sch)
    (f : X ⟶ Sp k) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsReduced X],
    Smooth ((R k X f).lastStructMap ≫ f) ∧
    IsProper (R k X f).lastStructMap ∧
    IsIso
      (morphismRestrict (R k X f).lastStructMap f.smoothLocus) ∧
    Dense ((R k X f).lastStructMap.base ⁻¹' (f.smoothLocus : Set X)) ∧
    (R k X f).CentersLieOver ((smoothLocusComplement f : Closeds X) : Set X) ∧
    IsStrictNormalCrossingsDivisor (reducedInverseImage (R k X f).lastStructMap $ smoothLocusComplement f)

def IsCompatibleWithSmoothMorphisms : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X X' : Sch)
    (f : X ⟶ Sp k) (f' : X' ⟶ Sp k)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced X]
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsReduced X']
    (ph_ : X' ⟶ X) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r ph_],
    ph_ ≫ f = f' → IsPullbackBlowupSequence ph_ (R k X' f') (R k X f)

def IsCompatibleWithFieldExtension : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Sch)
    (f : X ⟶ Sp k) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsReduced X]
    (K : Type) [Field K] [CharZero K] [Algebra k K]
    [IsReduced $ baseChange f K],
    IsPullbackBlowupSequence (baseChangeProjection f K)
      (R K (baseChange f K) $ baseChangeToSpec f K) $ R k X f
end

def StrongResolutionOfSingularitiesCharZero : Prop :=
  ∃ R : ResolutionRule,
    IsStrongResolutionRule R ∧ IsCompatibleWithSmoothMorphisms R ∧ IsCompatibleWithFieldExtension R

end FunctorialResolution.EmbeddedResolution

end

end
section
open CategoryTheory.Limits Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
section
variable (I : ISD X)
section
variable (U : Opn X)
abbrev restrictIdeal :
    U.toScheme.IdealSheafData :=
  I.comap U.ι

theorem restrictIdeal_eq_comap_io :
    restrictIdeal I U = I.comap U.i := rfl

theorem restrictIdeal_eq_top_iff_forall_notMem_support :
    restrictIdeal I U = ⊤ ↔ ∀ x, x ∈ U → x ∉ support I := by
  let _a0 := ((⊥ : m182 U.toScheme) : Set U.toScheme)
  have hbot : _a0 = ∅ := rfl
  have hbot' : ∀ A : m182 U.toScheme,
      (A = ⊥ ↔ ∀ y : oSch U, y ∉ A) := by
    intro A
    constructor
    rintro rfl y hy
    have hy' : y ∈ _a0 := hy
    rwa [hbot] at hy'
    intro hall
    exact coe_injective $ tr_ (m15 (fun y hy => absurd hy $ hall y) $ empty_subset _) hbot.symm
  have key : ∀ x (hx : x ∈ U),
      ((⟨x, hx⟩ : oSch U) ∈ spI (cmI I U.i) ↔ x ∈ spI I) := by
    intro x hx
    simp
    rfl
  rw [restrictIdeal_eq_comap_io, ← support_eq_bot_iff, hbot']
  constructor
  intro h x hx hmem
  exact h ⟨x, hx⟩ $ mpr_ (key x hx) hmem
  rintro h ⟨x, hx⟩ hy
  exact h x hx $ mp_ (key x hx) hy
end

theorem restrictIdeal_eq_comap_homOfLE_restrictIdeal
    {U V : Opn X} (h : V ≤ U) :
    restrictIdeal I V = (restrictIdeal I U).comap (X.homOfLE h) := by
  have hcomp : X.homOfLE h ≫ opI U = opI V := by simp
  rw [← comap_comp, hcomp]

abbrev zeroLocus : Closeds X :=
  support I


def NonzeroOnComponents : Prop :=
  ∀ T ∈ irreducibleComponents (↥X), ¬ T ⊆ (support I : Set ↥X)

theorem nonzeroOnComponents_iff :
    NonzeroOnComponents I ↔ ∀ T ∈ irreducibleComponents (↥X), ¬ T ⊆ (support I : Set ↥X) :=
  m22
end

theorem restrictIdeal_eq_of_le_of_eq {I J : ISD X} {U V : Opn X}
    (h : V ≤ U) (hU : restrictIdeal I U = restrictIdeal J U) :
    restrictIdeal I V = restrictIdeal J V := by
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal I h,
    restrictIdeal_eq_comap_homOfLE_restrictIdeal J h, hU]

section
variable {k : Type} [Field k] (p : X ⟶ Sp k) (D : ISD X)
def IsSmoothDivisor : Prop :=
  Blowup.IsLocallyGeneratedByNonZeroDivisor D ∧ Smooth (subschemeι D ≫ p)

theorem isSmoothDivisor_iff :
    IsSmoothDivisor p D ↔
      Blowup.IsLocallyGeneratedByNonZeroDivisor D ∧ Smooth (subschemeι D ≫ p) :=
  m22
end

def VanishesAlong (I J : ISD X) : Prop := I ≤ J

theorem vanishesAlong_iff_le (I J : ISD X) :
    VanishesAlong I J ↔ I ≤ J := m22
end

section
variable (k : Type) [Field k] (m : ℕ)
abbrev affineSpaceFin : Sch :=
  AffineSpace (UFin m) $ Sp k

abbrev affineSpaceFinToSpec :
    affineSpaceFin k m ⟶ Sp k :=
  (affineSpaceFin k m ↘ Sp k)
end

theorem restrictIdeal_comap_eq_comap_resLE_restrictIdeal {X Y : Sch} (f : X ⟶ Y)
    (I : ISD Y) (U : Opn Y) (V : Opn X) (h : V ≤ pre f U) :
    restrictIdeal (I.comap f) V = (restrictIdeal I U).comap (f.resLE U V h) := by
  have hcomp : f.resLE U V h ≫ ι U = ι V ≫ f := by simp
  show (I.comap f).comap V.i = (I.comap U.i).comap (f.resLE U V h)
  rw [← comap_comp, ← comap_comp, hcomp]

structure EtaleChart {X : Sch} {k : Type} [Field k]
    (p : X ⟶ Sp k) (U : Opn X) (m : ℕ) : Type where
  map : toScheme U ⟶ affineSpaceFin k m
  comp_struct : map ≫ affineSpaceFinToSpec k m = ι U ≫ p
  isEtale : Etale map

section
variable (k : Type) [Field k] (m) (S : FinSet m)
def coordSubspaceIdeal :
    IdealSheafData $ affineSpaceFin k m :=
  ofIdealTop
    (span
      ((fun i : Fin m => AffineSpace.coord (Sp k) $ up i) ''
        (S : Set $ Fin m)))

theorem coordSubspaceIdeal_eq_ofIdealTop_span_coord :
    coordSubspaceIdeal k m S =
      ofIdealTop
        (span
          ((fun i => AffineSpace.coord (Sp k) $ up i) ''
            (S : Set $ Fin m))) := rfl
end

section
variable {X : Sch} {k : Type} [Field k]
section
variable {p : X ⟶ Sp k} {U : Opn X} {m : ℕ} (c : EtaleChart p U m) (S : FinSet m)
def EtaleChart.coordIdeal : U.toScheme.IdealSheafData :=
  (coordSubspaceIdeal k m S).comap c.map

theorem EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal :
    c.coordIdeal S = (coordSubspaceIdeal k m S).comap c.map := rfl
end

section
variable (p : X ⟶ Sp k)
section
variable (E : Bdy X)
def InStrictNormalCrossingPositionAt (x : X) : Prop :=
  ∃ (U : Opn X) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
    (∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
    (∀ i, ∀ h : i < length E, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
    (∀ i, ∀ h : i < length E, ∀ t : Fin m, a i = some t →
      restrictIdeal (E[i]'h) U = c.coordIdeal {t})

def InStrictNormalCrossingPosition : Prop :=
  (∀ D ∈ E, IsSmoothDivisor p D) ∧ ∀ x : X, InStrictNormalCrossingPositionAt p E x

theorem inStrictNormalCrossingPosition_iff :
    InStrictNormalCrossingPosition p E ↔
      (∀ D ∈ E, IsSmoothDivisor p D) ∧ ∀ x, InStrictNormalCrossingPositionAt p E x :=
  m22
end

section
variable (Z : ISD X) (E : Bdy X)
def HasStrictNormalCrossingsWith : Prop :=
  ∀ x ∈ support Z,
    ∃ (U : Opn X) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
      (S : FinSet m),
      (∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < length E, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < length E, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      restrictIdeal Z U = c.coordIdeal S

theorem hasStrictNormalCrossingsWith_iff :
    HasStrictNormalCrossingsWith p Z E ↔
      ∀ x ∈ support Z,
        ∃ (U : Opn X) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
          (S : FinSet m),
          (∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
          (∀ i, ∀ h : i < length E, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
          (∀ i, ∀ h : i < length E, ∀ t : Fin m, a i = some t →
            restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
          restrictIdeal Z U = c.coordIdeal S :=
  m22
end
end

section
variable {p : X ⟶ Sp k}
section
variable {Z : ISD X} {E : Bdy X}
theorem HasStrictNormalCrossingsWith.exists_etaleChart (h : HasStrictNormalCrossingsWith p Z E) {x : X} (hx : x ∈ support Z) :
    ∃ (U : Opn X) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
      (S : FinSet m),
      (∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < length E, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < length E, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      restrictIdeal Z U = c.coordIdeal S :=
  h x hx

theorem hasStrictNormalCrossingsWith_of_forall_exists_etaleChart
    (h : ∀ x ∈ support Z,
      ∃ (U : Opn X) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
        (S : FinSet m),
        (∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
        (∀ i, ∀ h : i < length E, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
        (∀ i, ∀ h : i < length E, ∀ t : Fin m, a i = some t →
          restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
        restrictIdeal Z U = c.coordIdeal S) :
    HasStrictNormalCrossingsWith p Z E :=
  h
end

section
variable {E : Bdy X} {x : X}
theorem inStrictNormalCrossingPositionAt_of_exists_etaleChart
    (h : ∃ (U : Opn X) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
      (∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < length E, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < length E, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t})) :
    InStrictNormalCrossingPositionAt p E x :=
  h

theorem InStrictNormalCrossingPositionAt.exists_etaleChart
    (h : InStrictNormalCrossingPositionAt p E x) :
    ∃ (U : Opn X) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m)),
      (∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
      (∀ i, ∀ h : i < length E, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < length E, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) :=
  h
end

theorem HasStrictNormalCrossingsWith.exists_etaleChart_of_cons {Z : ISD X}
    {H : ISD X} {E : Bdy X}
    (h : HasStrictNormalCrossingsWith p Z (H :: E)) {x : X} (hx : x ∈ support Z) :
    ∃ (U : Opn X) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (S : FinSet m)
      (aH : Option $ Fin m) (a : ℕ → Option (Fin m)),
      restrictIdeal Z U = c.coordIdeal S ∧
      (aH = none → restrictIdeal H U = ⊤) ∧
      (∀ t : Fin m, aH = some t → restrictIdeal H U = c.coordIdeal {t}) ∧
      (∀ i, ∀ h : i < length E, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < length E, ∀ t : Fin m, a i = some t →
        restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
      (∀ i < length E, ∀ t : Fin m, a i = some t → aH ≠ some t) ∧
      (∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j) := by
  obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := h x hx
  have hzero : 0 < lenL (H :: E) := by simp
  refine ⟨U, hU, m, c, S, a 0, fun i => a $ i + 1, h4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  intro h0
  simpa using (h2 0 hzero h0)
  intro t ht
  simpa using (h3 0 hzero t ht)
  intro i hi hni
  have hi' : i + 1 < lenL (H :: E) := by simp_all
  simpa using (h2 (i + 1) hi' hni)
  intro i hi t ht
  have hi' : i + 1 < lenL (H :: E) := by simp_all
  simpa using (h3 (i + 1) hi' t ht)
  intro i hi t ht hc
  have hi' : i + 1 < lenL (H :: E) := by simp_all
  have := h1 (i + 1) hi' 0 hzero t ht hc
  omega
  intro i hi j hj t hti htj
  have hi' : i + 1 < lenL (H :: E) := by simp_all
  have hj' : j + 1 < lenL (H :: E) := by simp_all
  have := h1 (i + 1) hi' (j + 1) hj' t hti htj
  omega
end
end


def HasEtaleCoordCodim {X X' : Sch} {k : Type} [Field k]
    (p : X' ⟶ Sp k) (ta_ : X ⟶ X') (c : ℕ) : Prop :=
  ∀ x : X, ∃ (U : Opn X') (_ : ta_.base x ∈ U) (m : ℕ) (ch : EtaleChart p U m)
    (S : FinSet m), S.card = c ∧ restrictIdeal ta_.ker U = ch.coordIdeal S


abbrev affineSpaceCoord (k : Type) [Field k] (m : ℕ) (j : Fin m) :=
  AffineSpace.coord (Sp k) (up j : UFin m)

section

variable {X : Sch} {k : Type} [Field k] {q : X ⟶ Sp k}
  {U : Opn X} {m : ℕ}

@[reducible] def EtaleChart.coordTop (c : EtaleChart q U m) (j : Fin m) :
    U.toScheme.presheaf.obj $ op ⊤ :=
  c.map.appTop.hom $ affineSpaceCoord k m j

end

def pointOfMem {P : Sch} (V : Opn P) (p : ↥P) (hp : p ∈ V) : ↥(toScheme V) :=
  ⟨p, hp⟩

def specResidueFieldPoint {X : Sch} (x : ↥X) : ↥(Spec $ X.residueField x) :=
  (⟨⊥, isPrime_bot⟩ : PrimeSpectrum $ X.residueField x)

section

variable {P : Sch} {k : Type} [Field k] {q : P ⟶ Sp k}
  {V : Opn P} {n : ℕ}

section
variable (c1_ c2_ : EtaleChart q V n)
abbrev chartPullback : Sch := pullback c1_.map c2_.map

abbrev chartPullbackFst : chartPullback c1_ c2_ ⟶ P :=
  pullback.fst c1_.map c2_.map ≫ ι V

abbrev chartPullbackSnd : chartPullback c1_ c2_ ⟶ P :=
  pullback.snd c1_.map c2_.map ≫ ι V

theorem etale_pullback_fst_map :
    Etale $ pullback.fst c1_.map c2_.map := by
  have := c2_.isEtale
  infer_instance
end

instance instEtalePullbackFstChart (c1_ c2_ : EtaleChart q V n) :
    Etale $ pullback.fst c1_.map c2_.map :=
  etale_pullback_fst_map c1_ c2_

instance instEtaleChartPairFst (c1_ c2_ : EtaleChart q V n) :
    Etale $ chartPullbackFst c1_ c2_ :=
  by
    have h1_ :=
      etale_pullback_fst_map c1_ c2_
    have h2_ : Etale V.i := inferInstance
    have := h1_
    have := h2_
    infer_instance

instance instEtaleChartPairSnd (c1_ c2_ : EtaleChart q V n) :
    Etale $ chartPullbackSnd c1_ c2_ :=
  by
    have h1_ : Etale $ pullback.snd c1_.map c2_.map := by
      have h1 := c1_.isEtale
      have h2 := c2_.isEtale
      exact inferInstance
    have h2_ : Etale V.i := inferInstance
    have := h1_
    have := h2_
    infer_instance

section
variable (c1_ c2_ : EtaleChart q V n)
theorem chartPullbackFst_comp_eq_chartPullbackSnd_comp :
    chartPullbackFst c1_ c2_ ≫ q = chartPullbackSnd c1_ c2_ ≫ q := by
  have h : (pullback.fst c1_.map c2_.map ≫ c1_.map) ≫ affineSpaceFinToSpec k n
      = (pullback.snd c1_.map c2_.map ≫ c2_.map) ≫ affineSpaceFinToSpec k n := by
    rw [pullback.condition]
  rw [assoc, assoc, c1_.comp_struct, c2_.comp_struct] at h
  simpa only [assoc] using h

section
variable (p) (hp : p ∈ V)
abbrev ChartsAgreeAt : Prop :=
  V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c1_.map =
    V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c2_.map

section
variable (h : ChartsAgreeAt c1_ c2_ p hp)
def chartPullbackLift :
    Spec (V.toScheme.residueField (pointOfMem V p hp)) ⟶ chartPullback c1_ c2_ :=
  pullback.lift (V.toScheme.fromSpecResidueField (pointOfMem V p hp))
    (V.toScheme.fromSpecResidueField (pointOfMem V p hp)) h

@[simp] theorem chartPullbackLift_fst :
    chartPullbackLift c1_ c2_ p hp h ≫ pullback.fst c1_.map c2_.map =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) :=
  pullback.lift_fst _ _ _

@[simp] theorem chartPullbackLift_snd :
    chartPullbackLift c1_ c2_ p hp h ≫ pullback.snd c1_.map c2_.map =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) :=
  pullback.lift_snd _ _ _

def chartPullbackPoint : ↥(chartPullback c1_ c2_) :=
  (chartPullbackLift c1_ c2_ p hp h).base $ specResidueFieldPoint $ pointOfMem V p hp
end
end

theorem chartPullback_comap_coordIdeal_eq S :
    (c1_.coordIdeal S).comap (pullback.fst c1_.map c2_.map) =
      (c2_.coordIdeal S).comap (pullback.snd c1_.map c2_.map) := by
  rw [c1_.coordIdeal_eq_comap_coordSubspaceIdeal S, c2_.coordIdeal_eq_comap_coordSubspaceIdeal S, ← comap_comp,
    ← comap_comp, pullback.condition]
end

section
variable {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C)
private theorem appTop_comp_apply
    x :
    (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl

private theorem comp_base_apply
    x : (f ≫ g).base x = g.base (f.base x) := rfl
end

section
variable {W} (c1_ c2_ : EtaleChart q V n) (p) (hp : p ∈ V) (h : ChartsAgreeAt c1_ c2_ p hp) (g : toScheme V ⟶ W)
@[simp] theorem chartPullbackLift_fst_assoc :
    chartPullbackLift c1_ c2_ p hp h ≫ pullback.fst c1_.map c2_.map ≫ g =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ g := by
  rw [← assoc, chartPullbackLift_fst]

@[simp] theorem chartPullbackLift_snd_assoc :
    chartPullbackLift c1_ c2_ p hp h ≫ pullback.snd c1_.map c2_.map ≫ g =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ g := by
  rw [← assoc, chartPullbackLift_snd]
end

section
variable (c1_ c2_ : EtaleChart q V n)
theorem chartPullback_coordTop_eq j :
    (pullback.fst c1_.map c2_.map).appTop.hom (c1_.coordTop j) =
      (pullback.snd c1_.map c2_.map).appTop.hom (c2_.coordTop j) := by
  let _a0 := affineSpaceCoord k n j
  have h : (pullback.fst c1_.map c2_.map ≫ c1_.map).appTop.hom _a0
      = (pullback.snd c1_.map c2_.map ≫ c2_.map).appTop.hom _a0 := by
    rw [pullback.condition]
  rwa [appTop_comp_apply, appTop_comp_apply] at h

section
variable (p : ↥P) (hp : p ∈ V) (h : ChartsAgreeAt c1_ c2_ p hp)
theorem chartPullbackFst_base_chartPullbackPoint :
    (chartPullbackFst c1_ c2_).base (chartPullbackPoint c1_ c2_ p hp h) = p := by
  let _a0 := pointOfMem V p hp
  have hfs : bsM (V.toScheme.fromSpecResidueField _a0)
      (specResidueFieldPoint _a0) = _a0 := by
    simp
  have e : bsM (chartPullbackLift c1_ c2_ p hp h ≫ pullback.fst c1_.map c2_.map)
      (specResidueFieldPoint _a0) = _a0 := by
    rwa [chartPullbackLift_fst]
  let _a1 := bsM (pullback.fst c1_.map c2_.map) $ chartPullbackPoint c1_ c2_ p hp h
  have key : _a1
      = _a0 := e
  have key2 : opIb V _a1
      = opIb V _a0 := by rw [key]
  exact key2

theorem chartPullbackSnd_base_chartPullbackPoint :
    (chartPullbackSnd c1_ c2_).base (chartPullbackPoint c1_ c2_ p hp h) = p := by
  let _a0 := pointOfMem V p hp
  have e1 : bsM (V.toScheme.fromSpecResidueField _a0)
      (specResidueFieldPoint _a0) = _a0 := by
    simp
  let _a1 := chartPullbackLift c1_ c2_ p hp h
  let _a2 := pullback.snd c1_.map c2_.map ≫ opI V
  have hA := comp_base_apply _a1
      _a2 $ specResidueFieldPoint _a0
  have hB := comp_base_apply
      (V.toScheme.fromSpecResidueField _a0) V.i
      (specResidueFieldPoint _a0)
  have h3 : bsM (_a1 ≫ _a2)
        (specResidueFieldPoint _a0)
      = bsM (V.toScheme.fromSpecResidueField _a0 ≫ opI V)
        (specResidueFieldPoint _a0) := by
    rw [chartPullbackLift_snd_assoc c1_ c2_ p hp h V.i]
  exact st_ hA $ tr_ h3 $ tr_ hB $ tr_ (congrArg V.ib e1) rfl
end
end

theorem specResidueField_eq_zero_of_not_isUnit {X : Sch} (x : ↥X)
    (t : Γ(Spec $ X.residueField x, ⊤)) (ht : ¬ IsUnit t) : t = 0 := by
  let _c0 := GSpecIso $ X.residueField x
  have h2 : _c0.inv.hom
      (_c0.hom.hom t) = t := by
    have e1 := congrArg hom
      (hom_inv_id _c0)
    rw [hom_comp, hom_id] at e1
    exact congr_fun e1 t
  by_contra hne
  have hne0 : _c0.hom.hom t ≠ 0 := by
    intro h0
    apply hne
    rw [← h2, h0]
    exact map_zero _
  have hu2 :=
    (mpr_ isUnit_iff_ne_zero hne0).map _c0.inv.hom
  rw [h2] at hu2
  exact ht hu2

theorem affineSpaceFin_hom_ext {K : Type} [Field K] {m} {Z}
    (f g : Z ⟶ affineSpaceFin K m)
    (h1_ : f ≫ affineSpaceFinToSpec K m = g ≫ affineSpaceFinToSpec K m)
    (h2_ : ∀ i : UFin m,
      f.appTop.hom (AffineSpace.coord (Sp K) i) =
        g.appTop.hom (AffineSpace.coord (Sp K) i)) :
    f = g := by
  apply m46
  exact h1_
  exact h2_


theorem fromSpecResidueField_appTop_eq_zero {X : Sch} (x : ↥X)
    (hx : x ∈ (⊤ : Opn X)) (s : Γ(X, ⊤))
    (hs : (X.presheaf.germ ⊤ x hx).hom s ∈ maximalIdeal (X.presheaf.stalk x)) :
    (X.fromSpecResidueField x).appTop.hom s = 0 := by
  have hxb := fun hmem =>
    (fun {a} ha => mp (mem_maximalIdeal a) ha) hs $ (X.mem_basicOpen_top s x).1 hmem
  have hy : bsM (X.fromSpecResidueField x) (specResidueFieldPoint x) = x := by simp
  have hynot : specResidueFieldPoint x ∉ bOpn (Spec $ X.residueField x)
      ((X.fromSpecResidueField x).appTop.hom s) := by
    intro hmem
    have h1 : specResidueFieldPoint x ∈ (X.fromSpecResidueField x) ⁻¹ᵁ (bOpn X s) := by
      rwa [preimage_basicOpen]
    have h2 : bsM (X.fromSpecResidueField x) (specResidueFieldPoint x) ∈ bOpn X s := h1
    rw [hy] at h2
    exact hxb h2
  refine specResidueField_eq_zero_of_not_isUnit x _ ?_
  intro hu
  apply hynot
  rw [mem_basicOpen_top]
  exact hu.map
    (pGerm (Spec $ X.residueField x) ⊤ (specResidueFieldPoint x) $ by trivial).hom

theorem chartsAgreeAt_of_germ_sub_mem_maximalIdeal (c1_ c2_ : EtaleChart q V n) p
    (hp : p ∈ V)
    (h : ∀ j : Fin n,
      (V.toScheme.presheaf.germ ⊤ (pointOfMem V p hp) $ by trivial).hom
          (c1_.coordTop j - c2_.coordTop j) ∈
        maximalIdeal (V.toScheme.presheaf.stalk $ pointOfMem V p hp)) :
    ChartsAgreeAt c1_ c2_ p hp := by
  let _a0 := pointOfMem V p hp
  have hover : (V.toScheme.fromSpecResidueField _a0 ≫ c1_.map) ≫
        affineSpaceFinToSpec k n =
      (V.toScheme.fromSpecResidueField _a0 ≫ c2_.map) ≫
        affineSpaceFinToSpec k n := by
    rw [assoc, assoc, c1_.comp_struct, c2_.comp_struct]
  refine affineSpaceFin_hom_ext _ _ hover ?_
  rintro ⟨j⟩
  have h0 := fromSpecResidueField_appTop_eq_zero _a0 (by trivial)
    (c1_.coordTop j - c2_.coordTop j) $ h j
  rw [map_sub, sub_eq_zero] at h0
  rwa [appTop_comp_apply, appTop_comp_apply]

end

section

variable {P : Sch} {k : Type} [Field k] {q : P ⟶ Sp k}
  {V : Opn P} {n : ℕ}

section
variable (c1_ c2_ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V) (h : ChartsAgreeAt c1_ c2_ p hp)
def chartPullbackFstStalkMap :
    P.presheaf.stalk p ⟶ (chartPullback c1_ c2_).presheaf.stalk (chartPullbackPoint c1_ c2_ p hp h) :=
  eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
      (chartPullbackFst_base_chartPullbackPoint c1_ c2_ p hp h).symm) ≫
    (chartPullbackFst c1_ c2_).stalkMap (chartPullbackPoint c1_ c2_ p hp h)

def chartPullbackSndStalkMap :
    P.presheaf.stalk p ⟶ (chartPullback c1_ c2_).presheaf.stalk (chartPullbackPoint c1_ c2_ p hp h) :=
  eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
      (chartPullbackSnd_base_chartPullbackPoint c1_ c2_ p hp h).symm) ≫
    (chartPullbackSnd c1_ c2_).stalkMap (chartPullbackPoint c1_ c2_ p hp h)

theorem chartPullbackFstStalkMap_eq :
    chartPullbackFstStalkMap c1_ c2_ p hp h =
      eqToHom (congrArg (fun y => P.presheaf.stalk y)
          (chartPullbackFst_base_chartPullbackPoint c1_ c2_ p hp h).symm) ≫
        (chartPullbackFst c1_ c2_).stalkMap (chartPullbackPoint c1_ c2_ p hp h) := rfl

theorem chartPullbackSndStalkMap_eq :
    chartPullbackSndStalkMap c1_ c2_ p hp h =
      eqToHom (congrArg (fun y => P.presheaf.stalk y)
          (chartPullbackSnd_base_chartPullbackPoint c1_ c2_ p hp h).symm) ≫
        (chartPullbackSnd c1_ c2_).stalkMap (chartPullbackPoint c1_ c2_ p hp h) := rfl
end

end




section
variable {X Y : Sch} {k : Type} [Field k] (s : Y ⟶ Sp k) (t : X ⟶ Y) (c : ℕ)
def HasSmoothCoordCodim : Prop :=
  ∀ x : X, ∃ (U : Opn Y) (_ : t.base x ∈ U)
    (q : toScheme U ⟶ affineSpaceIndexedBy k (UFin c)),
    Smooth q ∧
      q ≫ affineSpaceIndexedByToSpec k (UFin c) = ι U ≫ s ∧
      restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q

theorem hasSmoothCoordCodim_iff :
    HasSmoothCoordCodim s t c ↔
      ∀ x, ∃ (U : Opn Y) (_ : t.base x ∈ U)
        (q : toScheme U ⟶ affineSpaceIndexedBy k (UFin c)),
        Smooth q ∧
          q ≫ affineSpaceIndexedByToSpec k (UFin c) = ι U ≫ s ∧
          restrictIdeal t.ker U = (coordSubspaceIdeal k c Finset.univ).comap q :=
  m22
end





variable {al_ : Type}

def indexBeforeMoveToFront (j : ℕ) : ℕ → ℕ
  | 0 => j
  | (i + 1) => if i < j then i else i + 1

section
variable (j : ℕ)
theorem indexBeforeMoveToFront_zero : indexBeforeMoveToFront j 0 = j := rfl

def indexInMoveToFront (i : ℕ) : ℕ := if i = j then 0 else if i < j then i + 1 else i

theorem indexBeforeMoveToFront_injective : Function.Injective $ indexBeforeMoveToFront j := by
  intro a b hab
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | succ i =>
      exfalso
      simp [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega
  | succ i =>
    cases b with
    | zero =>
      exfalso
      simp [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega
    | succ i' =>
      simp [indexBeforeMoveToFront] at hab
      split_ifs at hab <;> omega

theorem indexInMoveToFront_self : indexInMoveToFront j j = 0 := by
  simp [indexInMoveToFront]

theorem indexInMoveToFront_injective : Function.Injective $ indexInMoveToFront j := by
  intro a b hab
  simp [indexInMoveToFront] at hab
  split_ifs at hab <;> omega
end

section
variable (E : List al_) (j : ℕ)
def moveToFront : List al_ :=
  match E[j]? with
  | some a => a :: eraseIdx E j
  | none => E

section
variable (hj : j < length E)
include hj
theorem indexBeforeMoveToFront_lt_length (i : ℕ)
    (hi : i < length E) : indexBeforeMoveToFront j i < length E := by
  cases i with
  | zero => exact hj
  | succ n =>
    show (if n < j then n else n + 1) < length E
    split <;> omega

theorem moveToFront_eq_cons :
    moveToFront E j = (E[j]'hj) :: eraseIdx E j := by
  simp [moveToFront, List.getElem?_eq_getElem hj]

theorem length_moveToFront :
    length (moveToFront E j) = length E := by
  rw [moveToFront_eq_cons E j hj, List.length_cons,
    length_eraseIdx_add_one hj]

section
variable (i) (hi : i < length E)
include hi
theorem indexInMoveToFront_lt_length :
    indexInMoveToFront j i < length (moveToFront E j) := by
  rw [length_moveToFront E j hj]
  show (if i = j then 0 else if i < j then i + 1 else i) < length E
  split_ifs <;> omega

theorem getElem_eq_getElem_moveToFront :
    E[i]'hi = (moveToFront E j)[indexInMoveToFront j i]'(indexInMoveToFront_lt_length E j hj i hi) := by
  rcases lt_trichotomy i j with h | h | h
  have hb : indexInMoveToFront j i = i + 1 := by
    simp [indexInMoveToFront]
    split_ifs <;> omega
  simp [moveToFront_eq_cons E j hj, hb, List.getElem_eraseIdx_of_lt, h]
  subst h
  simp [moveToFront_eq_cons E _ hj, indexInMoveToFront_self, List.getElem_cons_zero]
  have hb : indexInMoveToFront j i = i := by
    simp [indexInMoveToFront]
    split_ifs <;> omega
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hjk : j ≤ k := by omega
  simp [moveToFront_eq_cons E j hj, hb, List.getElem_eraseIdx_of_ge, hjk]
end
end
end

section
variable {X : Sch} {k : Type} [Field k]
theorem chartAssignment_comp_of_injective
    {p : X ⟶ Sp k} {U : Opn X} {m : ℕ}
    (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
    (E E' : Bdy X) (σ : ℕ → ℕ)
    (hinj : Function.Injective σ)
    (hlt : ∀ i, i < length E' → σ i < length E)
    (hEq : ∀ i, ∀ h : i < length E', (E'[i]'h) = E[σ i]'(hlt i h))
    (hainj : ∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ i, ∀ h : i < length E, a i = none → restrictIdeal (E[i]'h) U = ⊤)
    (hsome : ∀ i, ∀ h : i < length E, ∀ t : Fin m, a i = some t →
      restrictIdeal (E[i]'h) U = c.coordIdeal {t}) :
    (∀ i < length E', ∀ j < length E', ∀ t : Fin m,
        (a ∘ σ) i = some t → (a ∘ σ) j = some t → i = j) ∧
      (∀ i, ∀ h : i < length E', (a ∘ σ) i = none → restrictIdeal (E'[i]'h) U = ⊤) ∧
      (∀ i, ∀ h : i < length E', ∀ t : Fin m, (a ∘ σ) i = some t →
        restrictIdeal (E'[i]'h) U = c.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  intro i hi j hj t hit hjt
  simp at hit hjt
  exact hinj $ hainj (σ i) (hlt i hi) (σ j) (hlt j hj) t hit hjt
  intro i h hn
  simp at hn
  rw [hEq i h]
  exact hnone (σ i) (hlt i h) hn
  simp_all

theorem hasStrictNormalCrossingsWith_of_moveToFront
    (p : X ⟶ Sp k) (Z : ISD X)
    (E : Bdy X) (j : ℕ) (hj : j < length E)
    (hZ : HasStrictNormalCrossingsWith p Z $ moveToFront E j) :
    HasStrictNormalCrossingsWith p Z E := by
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, h1, h2, h3, h4⟩ := hZ x hx
  have hlt :=
    fun i hi => indexInMoveToFront_lt_length E j hj i hi
  have hEq :=
    fun i h => getElem_eq_getElem_moveToFront E j hj i h
  obtain ⟨k1, k2, k3⟩ := chartAssignment_comp_of_injective c a (moveToFront E j) E (indexInMoveToFront j)
    (indexInMoveToFront_injective j) hlt hEq h1 h2 h3
  exact ⟨U, hxU, m, c, a ∘ indexInMoveToFront j, S, k1, k2, k3, h4⟩
end

theorem indexBeforeMoveToFront_succ j i : indexBeforeMoveToFront j (i + 1) = if i < j then i else i + 1 := rfl

theorem getElem_moveToFront (E : List al_) (j : ℕ) (hj : j < length E) (i : ℕ)
    (hi : i < length (moveToFront E j)) :
    (moveToFront E j)[i]'hi =
      E[indexBeforeMoveToFront j i]'(indexBeforeMoveToFront_lt_length E j hj i (by
        rw [length_moveToFront E j hj] at hi; exact hi)) := by
  have hi' : i < lenL E := by rw [length_moveToFront E j hj] at hi
                              exact hi
  have key : (moveToFront E j)[i]? = E[indexBeforeMoveToFront j i]? := by
    rw [moveToFront_eq_cons E j hj]
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero, indexBeforeMoveToFront_zero, List.getElem?_eq_getElem hj]
    | succ m =>
      rw [List.getElem?_cons_succ, indexBeforeMoveToFront_succ]
      by_cases hm : m < j
      rw [if_pos hm]
      simp [List.getElem?_eraseIdx_of_lt, hm]
      rw [if_neg hm]
      have hm' : j ≤ m := by omega
      simp [List.getElem?_eraseIdx_of_ge, hm']
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem $ indexBeforeMoveToFront_lt_length E j hj i hi'] at key
  exact m105 key

theorem inStrictNormalCrossingPosition_moveToFront {X : Sch} {k : Type} [Field k]
    (p : X ⟶ Sp k) (E : Bdy X) (j : ℕ)
    (hj : j < length E) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition p $ moveToFront E j := by
  constructor
  intro D hD
  refine hE.1 D ?_
  rw [moveToFront_eq_cons E j hj] at hD
  rcases mem_cons.mp hD with h1 | h2
  subst h1
  simp
  exact mem_of_mem_eraseIdx h2
  intro x
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := hE.2 x
  let _a0 := moveToFront E j
  have hlt : ∀ i, i < length _a0 → indexBeforeMoveToFront j i < length E := by
    intro i hi
    refine indexBeforeMoveToFront_lt_length E j hj i ?_
    rwa [length_moveToFront E j hj] at hi
  have hEq :=
    fun i h => getElem_moveToFront E j hj i h
  obtain ⟨k1, k2, k3⟩ := chartAssignment_comp_of_injective c a E _a0 (indexBeforeMoveToFront j)
    (indexBeforeMoveToFront_injective j) hlt hEq h1 h2 h3
  exact ⟨U, hxU, m, c, a ∘ indexBeforeMoveToFront j, k1, k2, k3⟩

end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution


structure IdealBlowupSequence {k : Type} [Field k] {X : Sch}
    (p : X ⟶ Sp k) (I : ISD X)
    (E : Bdy X) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, IdealSheafData $ toSequenceOfBlowups.schemeAt i
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap (toSequenceOfBlowups.projectionToBase 0)
  boundary_zero : boundary 0 = E.map fun D => D.comap $ toSequenceOfBlowups.projectionToBase 0
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    Smooth
      ((toSequenceOfBlowups.center i).si ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  ideal_vanishes : ∀ i, i < toSequenceOfBlowups.length →
    VanishesAlong (ideal i) (toSequenceOfBlowups.center i)
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (Blowup.strictTransform (toSequenceOfBlowups.transitionMapSucc i) $ toSequenceOfBlowups.center i) ++
        [Blowup.exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) $ toSequenceOfBlowups.center i]

namespace IdealBlowupSequence

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {E : Bdy X}

section
variable (s : IdealBlowupSequence p I E)
section
variable (i : ℕ)
def structureMorphism :
    s.toSequenceOfBlowups.schemeAt i ⟶ Sp k :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p

theorem structureMorphism_def :
    s.structureMorphism i = s.toSequenceOfBlowups.projectionToBase i ≫ p := rfl

theorem smooth_center_subschemeio (h : i < s.toSequenceOfBlowups.length) :
    Smooth $ subschemeι (s.toSequenceOfBlowups.center i) ≫ s.structureMorphism i :=
  s.center_smooth i h

theorem hasStrictNormalCrossingsWith_center (h : i < s.toSequenceOfBlowups.length) :
    HasStrictNormalCrossingsWith (s.structureMorphism i) (s.toSequenceOfBlowups.center i) $ s.boundary i :=
  s.center_snc i h

def exceptionalIdeal : IdealSheafData $ s.toSequenceOfBlowups.schemeAt $ i + 1 :=
  Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) $ s.toSequenceOfBlowups.center i

theorem exceptionalIdeal_eq :
    s.exceptionalIdeal i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := rfl

theorem boundary_succ_eq_map_strictTransform_append (h : i < s.toSequenceOfBlowups.length) :
    s.boundary (i + 1) =
      (s.boundary i).map
          (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) $ s.toSequenceOfBlowups.center i) ++
        [s.exceptionalIdeal i] :=
  s.boundary_succ i h
end

def lastIdeal :
    IdealSheafData $ s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length :=
  s.ideal s.toSequenceOfBlowups.length

theorem lastIdeal_eq :
    s.lastIdeal = s.ideal s.toSequenceOfBlowups.length := rfl
end

end IdealBlowupSequence

end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits Opposite

namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowups

variable {X : Sch}

section
variable (s : SequenceOfBlowups X)
theorem transitionMap_def {i i'} (h : i ≤ i') :
    s.transitionMap h = s.tower.map (homOfLE h).op := rfl

section
variable {X' : Sch} (ph_ : X' ⟶ X) {i i' : ℕ} (h : i ≤ i')
theorem pullbackTransitionMap_fst :
    s.pullbackTransitionMap ph_ h ≫ pullback.fst ph_ (s.projectionToBase i) = pullback.fst ph_ (s.projectionToBase i') :=
  m32 (pullback.lift_fst _ _ _) $ comp_id _

theorem pullbackTransitionMap_snd :
    s.pullbackTransitionMap ph_ h ≫ pullback.snd ph_ (s.projectionToBase i)
      = pullback.snd ph_ (s.projectionToBase i') ≫ s.transitionMap h :=
  pullback.lift_snd _ _ _
end

theorem transitionMap_trans {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    s.transitionMap hjl ≫ s.transitionMap hij = s.transitionMap (hij.trans hjl) :=
  (s.tower.map_comp (homOfLE hjl).op (homOfLE hij).op).symm

theorem transitionMap_self {i : ℕ} (h : i ≤ i) : s.transitionMap h = 𝟙 (s.schemeAt i) := by
  rw [transitionMap_def, show (homOfLE h).op = 𝟙 (op i) from rfl, s.tower.map_id]

section
variable (i : ℕ)
theorem isBlowupAlongIdealSheaf_blowupMorphism (h : i < length s) :
    Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) $ s.center i := s.isBlowup i h

theorem blowupMorphism_eq_transitionMap :
    s.transitionMapSucc i = s.transitionMap (le_succ i) := rfl

theorem projectionToBase_def :
    s.projectionToBase i = s.transitionMap (zero_le i) ≫ s.isoZero.hom := rfl

theorem projectionToBase_succ :
    s.projectionToBase (i + 1) = s.transitionMapSucc i ≫ s.projectionToBase i := by
  rw [blowupMorphism_eq_transitionMap]
  exact sy_ $ s.transitionMap_comp_projectionToBase $ le_succ i
end

theorem projectionToBase_zero : s.projectionToBase 0 = s.isoZero.hom := by
  rw [projectionToBase_def, s.transitionMap_self, id_comp]

theorem lastStructMap_eq_projectionToBase : s.lastStructMap = s.projectionToBase s.length := rfl
end

end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
end
section


namespace FunctorialResolution.EmbeddedResolution

section
variable {S X : Sch}
section
variable (σ : S ⟶ X) (I : ISD S)
def imageIdealSheaf : ISD X :=
  (subschemeι I ≫ σ).ker

theorem imageIdealSheaf_eq_ker :
    imageIdealSheaf σ I = (subschemeι I ≫ σ).ker := rfl
end

def IsPushforwardBlowupSeq (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X) : Prop :=
  BS.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ BS.length → (BS.schemeAt i ⟶ B.schemeAt i),
      (∀ i : ℕ, ∀ hi : i ≤ BS.length, IsClosedImmersion $ σ i hi) ∧
      (σ 0 (zero_le _) ≫ B.isoZero.hom = BS.isoZero.hom ≫ j) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        σ (i + 1) hi ≫ B.transitionMapSucc i = BS.transitionMapSucc i ≫ σ i hi.le) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        B.center i = imageIdealSheaf (σ i hi.le) (BS.center i)) ∧
      (∀ i : ℕ, ∀ hi : i < BS.length,
        (σ (i + 1) hi).ker =
          Blowup.strictTransform (B.transitionMapSucc i) (B.center i) (σ i hi.le).ker)

theorem map_eq_imageIdealSheaf (f : S ⟶ X) (I : ISD S) :
    I.map f = imageIdealSheaf f I := rfl
end

section
variable {X' X : Sch}
def IsStrictPullbackBlowupSeq (ph_ : X' ⟶ X)
    (B' : SequenceOfBlowups X') (B : SequenceOfBlowups X) : Prop :=
  B'.length = B.length ∧
    ∃ σ : ∀ i : ℕ, i ≤ B'.length → (B'.schemeAt i ⟶ B.schemeAt i),
      (σ 0 (zero_le _) ≫ B.isoZero.hom = B'.isoZero.hom ≫ ph_) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        IsPullback (σ (i + 1) hi) (B'.transitionMapSucc i) (B.transitionMapSucc i) $ σ i hi.le) ∧
      (∀ i : ℕ, ∀ hi : i < B'.length,
        B'.center i = (B.center i).comap (σ i hi.le))

section
variable (g : X' ⟶ X) (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
def schemeAtHomOfEqZero
    (i : ℕ) (hi0 : i = 0) : t.schemeAt i ⟶ s.schemeAt i :=
  eqToHom (congrArg t.schemeAt hi0) ≫ t.isoZero.hom ≫ g ≫ s.isoZero.inv ≫
    eqToHom (congrArg s.schemeAt hi0).symm

theorem IsStrictPullbackBlowupSeq.of_length_zero (ht : t.length = 0) (hs : s.length = 0) :
    IsStrictPullbackBlowupSeq g t s := by
  refine ⟨tr_ ht hs.symm,
    fun i hi => schemeAtHomOfEqZero g t s i $ eq_zero_of_le_zero $ le_of_le_of_eq hi ht,
    ?_, ?_, ?_⟩
  simp [schemeAtHomOfEqZero]
  simp_all
  simp_all
end

theorem IsStrictPullbackBlowupSeq.length_eq {ph_}
    {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq ph_ B' B) :
    B'.length = B.length := an1 h
end

def SequenceOfBlowups.Isomorphic {X : Sch} (B B' : SequenceOfBlowups X) : Prop :=
  length B = length B' ∧
    ∃ e : ∀ i : ℕ, i ≤ length B → (B.schemeAt i ≅ B'.schemeAt i),
      ((e 0 $ zero_le _).hom ≫ B'.isoZero.hom = B.isoZero.hom) ∧
      (∀ i : ℕ, ∀ hi : i < length B,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) ∧
      (∀ i : ℕ, ∀ hi : i < length B,
        (B'.center i).comap (e i hi.le).hom = B.center i)

theorem SequenceOfBlowups.isomorphic_refl {X} (B : SequenceOfBlowups X) : B.Isomorphic B := by
  refine ⟨rfl, fun i _ => Iso.refl _, ?_, ?_, ?_⟩ <;> simp

theorem imageIdealSheaf_comp {W A B : Sch} (g : W ⟶ A) (w : A ⟶ B) (I : ISD W) :
    imageIdealSheaf (g ≫ w) I = imageIdealSheaf w (imageIdealSheaf g I) := by
  simp [← map_eq_imageIdealSheaf, Scheme.IdealSheafData.map_comp]

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
theorem mem_closure_singleton_iff_fromSpec {U} (hU : IsAffineOpen U)
    a b :
    a ∈ closure ({b} : Set $ PrimeSpectrum $ X.sec U) ↔
      hU.fromSpec a ∈ closure ({hU.fromSpec b} : Set (X : Type)) := by
  have hind := (isOpenEmbedding hU.fromSpec).toIsEmbedding.toIsInducing
  constructor
  intro hab
  exact mp_ specializes_iff_mem_closure $ hind.specializes_iff.mpr $ mpr_ specializes_iff_mem_closure hab
  intro hab
  exact mp_ specializes_iff_mem_closure $ hind.specializes_iff.mp $ mpr_ specializes_iff_mem_closure hab

theorem mem_primeIdealOf_of_mem_support {I : ISD X}
    {U : X.affineOpens} {x} (hx : x ∈ U.1) {f}
    (hf : f ∈ I.ideal U) (hxs : x ∈ support I) :
    f ∈ asIdeal (U.2.primeIdealOf ⟨x, hx⟩) := by
  have hz :=
    mp (mem_support_iff_of_mem hx) hxs
  rw [mem_zeroLocus_iff] at hz
  let hU := U.2
  by_contra hfn
  apply hz f hf
  let _a0 := hU.primeIdealOf ⟨x, hx⟩
  have h1 : _a0 ∈ hU.fromSpec ⁻¹ᵁ bOpn X f := by
    rw [hU.fromSpec_preimage_basicOpen f]
    exact mpr_ (mem_basicOpen f _) hfn
  have h2 : hU.fromSpec _a0 ∈ bOpn X f := h1
  rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h2

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.not_irreducibleComponent_subset_support {D : ISD X} (hD : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor D)
    {Z} (hZ : Z ∈ irreducibleComponents (X : Type)) :
    ¬ Z ⊆ (support D : Set (X : Type)) := by
  intro hsub
  obtain ⟨xi_, hxi_⟩ := m140 hZ.1 $ isClosed_of_mem_irreducibleComponents Z hZ
  have hxi_' := hxi_
  have hxiZ_ : xi_ ∈ Z := by rw [← hxi_']
                             exact subset_closure rfl
  obtain ⟨U, f, hxU, hf, hDU⟩ := hD xi_
  have hfD : f ∈ D.ideal U := by rw [hDU]
                                 exact subset_span rfl
  have hfp :=
    EmbeddedResolution.mem_primeIdealOf_of_mem_support hxU hfD $ hsub hxiZ_
  let _s0 := U.2.primeIdealOf ⟨xi_, hxU⟩
  refine notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hfp ?_ hf
  refine ⟨⟨_s0.isPrime, bot_le⟩, ?_⟩
  rintro q ⟨hq, -⟩ hqle
  have hxy :=
    mp (le_iff_mem_closure ⟨q, hq⟩ _s0) hqle
  let _s1 := (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))
  let _m0 := ({U.2.fromSpec _s1} : Set X)
  have hxicl : xi_ ∈ closure _m0 := by
    have h2 := mp_ (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec U.2 _s0 ⟨q, hq⟩) hxy
    rwa [U.2.fromSpec_primeIdealOf ⟨xi_, hxU⟩] at h2
  have hZsub : Z ⊆ closure _m0 := by
    rw [← hxi_']
    exact closure_minimal (mpr_ singleton_subset_iff hxicl) isClosed_closure
  have hyZ :=
    an2 hZ isIrreducible_singleton.closure hZsub $ subset_closure rfl
  have hy : U.2.fromSpec _s1
      ∈ closure ({xi_} : Set X) := by
    rwa [hxi_']
  have hprimeLe := by
    refine mpr_ (le_iff_mem_closure _s0 ⟨q, hq⟩) ?_
    refine mpr_ (_root_.FunctorialResolution.EmbeddedResolution.mem_closure_singleton_iff_fromSpec U.2 ⟨q, hq⟩ _s0) ?_
    rwa [U.2.fromSpec_primeIdealOf ⟨xi_, hxU⟩]
  exact hprimeLe
end

end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

abbrev PrincipalizationAlgorithm : Type 1 :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Sch)
    (p : X ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (I : IdealSheafData X), NonzeroOnComponents I →
      ∀ E : List X.IdealSheafData, InStrictNormalCrossingPosition p E → IdealBlowupSequence p I E

section
variable (k K : Type) [Field k] [Field K] (f : k →+* K)
abbrev specMapOfFieldHom :
    Sp K ⟶ Sp k :=
  Spec.map $ ofHom f

theorem specMapOfFieldHom_eq :
    specMapOfFieldHom k K f = Spec.map (ofHom f) := rfl
end

instance instSurjectiveSpecMapOfFieldHom (k K : Type) [Field k] [Field K] (f : k →+* K) :
    Surjective $ specMapOfFieldHom k K f := by
  have hk : Subsingleton $ PrimeSpectrum k := by
    refine ⟨fun x y => ?_⟩
    have hx : asIdeal x = ⊥ := x.asIdeal.eq_bot_or_top.resolve_right x.isPrime.ne_top
    have hy : asIdeal y = ⊥ := y.asIdeal.eq_bot_or_top.resolve_right y.isPrime.ne_top
    exact PrimeSpectrum.ext (hx.trans hy.symm)
  obtain ⟨x⟩ : Nonempty $ PrimeSpectrum K := inferInstance
  refine ⟨fun y => ⟨x, ?_⟩⟩
  exact elim (α := PrimeSpectrum k) _ _

instance instFlatSpecMapOfFieldHom (k K : Type) [Field k] [Field K] (f : k →+* K) :
    Flat $ specMapOfFieldHom k K f := by
  show Flat $ Spec.map $ ofHom f
  let _inst : Algebra k K := f.toAlgebra
  have hflat : Module.Flat k K := inferInstance
  have hf : RingHom.Flat (ofHom f).hom := hflat
  exact HasRingHomProperty.Spec_iff.mpr hf

structure IsFunctorialPrincipalization (A : PrincipalizationAlgorithm) : Prop where
  pushforward :
    ∀ (k : Type) [Field k] [CharZero k] (S X : Sch)
      (pS : S ⟶ Sp k) (p : X ⟶ Sp k)
      [Smooth pS] [LocallyOfFiniteType pS]
      [QuasiCompact pS]
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (j : S ⟶ X) [IsClosedImmersion j] (_ : j ≫ p = pS)
      (c : ℕ) (_ : 1 ≤ c) (_ : HasEtaleCoordCodim p j c)
      (I : ISD S) (hI : NonzeroOnComponents I)
      (hIX : NonzeroOnComponents $ imageIdealSheaf j I)
      (hES : InStrictNormalCrossingPosition pS ([] : Bdy S))
      (hEX : InStrictNormalCrossingPosition p ([] : Bdy X)),
      IsPushforwardBlowupSeq j (A k S pS I hI [] hES).toSequenceOfBlowups
        (A k X p (imageIdealSheaf j I) hIX [] hEX).toSequenceOfBlowups
  base_change :
    ∀ (k : Type) [Field k] [CharZero k] (X : Sch)
      (p : X ⟶ Sp k)
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (I : ISD X) (hI : NonzeroOnComponents I)
      (E : Bdy X) (hE : InStrictNormalCrossingPosition p E)
      (K : Type) [Field K] [CharZero K] (f : k →+* K)
      [Smooth $ pullback.snd p $ specMapOfFieldHom k K f]
      [LocallyOfFiniteType $ pullback.snd p $ specMapOfFieldHom k K f]
      [QuasiCompact $ pullback.snd p $ specMapOfFieldHom k K f]
      (hI' : NonzeroOnComponents $ I.comap $ pullback.fst p $ specMapOfFieldHom k K f)
      (hE' : InStrictNormalCrossingPosition (pullback.snd p $ specMapOfFieldHom k K f)
        (E.map fun D => D.comap $ pullback.fst p $ specMapOfFieldHom k K f)),
      IsPullbackBlowupSequence (pullback.fst p $ specMapOfFieldHom k K f)
        (A K (pullback p $ specMapOfFieldHom k K f) (pullback.snd p $ specMapOfFieldHom k K f)
          (I.comap $ pullback.fst p $ specMapOfFieldHom k K f) hI'
          (E.map fun D => D.comap $ pullback.fst p $ specMapOfFieldHom k K f) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  base_change_strict :
    ∀ (k : Type) [Field k] [CharZero k] (X : Sch)
      (p : X ⟶ Sp k)
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (I : ISD X) (hI : NonzeroOnComponents I)
      (E : Bdy X) (hE : InStrictNormalCrossingPosition p E)
      (K : Type) [Field K] [CharZero K] (f : k →+* K)
      [Smooth $ pullback.snd p $ specMapOfFieldHom k K f]
      [LocallyOfFiniteType $ pullback.snd p $ specMapOfFieldHom k K f]
      [QuasiCompact $ pullback.snd p $ specMapOfFieldHom k K f]
      (hI' : NonzeroOnComponents $ I.comap $ pullback.fst p $ specMapOfFieldHom k K f)
      (hE' : InStrictNormalCrossingPosition (pullback.snd p $ specMapOfFieldHom k K f)
        (E.map fun D => D.comap $ pullback.fst p $ specMapOfFieldHom k K f)),
      IsStrictPullbackBlowupSeq (pullback.fst p $ specMapOfFieldHom k K f)
        (A K (pullback p $ specMapOfFieldHom k K f) (pullback.snd p $ specMapOfFieldHom k K f)
          (I.comap $ pullback.fst p $ specMapOfFieldHom k K f) hI'
          (E.map fun D => D.comap $ pullback.fst p $ specMapOfFieldHom k K f) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  lastIdeal_eq_top :
    ∀ (k : Type) [Field k] [CharZero k] X
      p
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      I hI
      E hE,
      (A k X p I hI E hE).lastIdeal = ⊤
  smooth_pullback :
    ∀ (k : Type) [Field k] [CharZero k] (X : Sch)
      (p : X ⟶ Sp k)
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (I : ISD X) (hI : NonzeroOnComponents I)
      (E : Bdy X) (hE : InStrictNormalCrossingPosition p E)
      (X' : Sch) (p' : X' ⟶ Sp k)
      [Smooth p'] [LocallyOfFiniteType p']
      [QuasiCompact p']
      (ph_ : X' ⟶ X) [Smooth ph_] (_ : ph_ ≫ p = p')
      (hI' : NonzeroOnComponents $ I.comap ph_)
      (hE' : InStrictNormalCrossingPosition p' $ E.map fun D => D.comap ph_),
      IsPullbackBlowupSequence ph_
        (A k X' p' (I.comap ph_) hI' (E.map fun D => D.comap ph_) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  smooth_pullback_strict :
    ∀ (k : Type) [Field k] [CharZero k] (X : Sch)
      (p : X ⟶ Sp k)
      [Smooth p] [LocallyOfFiniteType p]
      [QuasiCompact p]
      (I : ISD X) (hI : NonzeroOnComponents I)
      (E : Bdy X) (hE : InStrictNormalCrossingPosition p E)
      (X' : Sch) (p' : X' ⟶ Sp k)
      [Smooth p'] [LocallyOfFiniteType p']
      [QuasiCompact p']
      (ph_ : X' ⟶ X) [Smooth ph_] [Surjective ph_]
      (_ : ph_ ≫ p = p')
      (hI' : NonzeroOnComponents $ I.comap ph_)
      (hE' : InStrictNormalCrossingPosition p' $ E.map fun D => D.comap ph_),
      IsStrictPullbackBlowupSeq ph_
        (A k X' p' (I.comap ph_) hI' (E.map fun D => D.comap ph_) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups


section
variable {A B : Sch}
section
variable (f : A ⟶ B) [IsIso f]
theorem comap_eq_ker_subschemeio_comp_inv
    (I : ISD B) :
    I.comap f = (subschemeι I ≫ inv f).ker := by
  have :=
    (of_hasPullback f I.si).flip.isIso_fst_of_isIso
  have hw : fst f I.si
      = snd f I.si ≫ siI I ≫ inv f := by
    rw [← assoc, ← condition, assoc, m118,
      comp_id]
  unfold AlgebraicGeometry.Scheme.IdealSheafData.comap
  rw [hw, ker_comp_of_isIso]

theorem imageIdealSheaf_eq_comap_inv
    (J : ISD A) :
    imageIdealSheaf f J = J.comap (inv f) := by
  rw [imageIdealSheaf_eq_ker, comap_eq_ker_subschemeio_comp_inv (inv f) J, IsIso.inv_inv]

theorem comap_imageIdealSheaf
    J :
    (imageIdealSheaf f J).comap f = J := by
  rw [imageIdealSheaf_eq_comap_inv, ← comap_comp,
    m118, comap_id]

theorem imageIdealSheaf_comap
    (I : ISD B) :
    imageIdealSheaf f (I.comap f) = I := by
  rw [imageIdealSheaf_eq_comap_inv, ← comap_comp,
    m117, comap_id]
end

theorem compl_support_comap (v : A ⟶ B) (I : ISD B) :
    (I.comap v).support.compl = (TopologicalSpace.Opens.map v.base).obj I.support.compl := by
  ext x
  simp
end

theorem opens_map_comp {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) (U : Opn C) :
    (TopologicalSpace.Opens.map (f ≫ g).base).obj U
      = (TopologicalSpace.Opens.map f.base).obj ((TopologicalSpace.Opens.map g.base).obj U) := by
  ext x
  simp

theorem ker_comp_eq_imageIdealSheaf_ker {W A B : Sch} (g : W ⟶ A) (w : A ⟶ B) :
    (g ≫ w).ker = imageIdealSheaf w g.ker := by
  rw [imageIdealSheaf_eq_ker, ker_comp,
    ker_comp, ker_subschemeι]

private theorem exists_iso_subscheme_comap_of_isIso {A B : Sch} (w : A ⟶ B) [IsIso w]
    (I : ISD B) :
    ∃ th_ : subscheme (I.comap w) ≅ subscheme I,
      th_.hom ≫ subschemeι I = subschemeι (I.comap w) ≫ w := by
  let _m0 := siI (cmI I w) ≫ w
  have e1 : _m0.ker = I := by
    rw [ker_comp_eq_imageIdealSheaf_ker, ker_subschemeι,
      imageIdealSheaf_comap]
  let _a0 := siI I ≫ inv w
  have e2 : _a0.ker = cmI I w := by
    rw [ker_comp_eq_imageIdealSheaf_ker, ker_subschemeι,
      imageIdealSheaf_eq_comap_inv, IsIso.inv_inv]
  have h1 : I.subschemeι.ker ≤ _m0.ker :=
    le_of_eq $ by rw [e1, ker_subschemeι]
  have h2 : (cmI I w).subschemeι.ker ≤ _a0.ker :=
    le_of_eq $ by rw [e2, ker_subschemeι]
  refine ⟨⟨m64 I.si _m0 h1,
    m64 (cmI I w).si _a0 h2, ?_, ?_⟩, lift_fac ..⟩
  rw [← cancel_mono (cmI I w).si, assoc, lift_fac,
    ← assoc, lift_fac, assoc, m118,
    comp_id, id_comp]
  rw [← cancel_mono I.si, assoc, lift_fac,
    ← assoc, lift_fac, assoc, m117,
    comp_id, id_comp]

theorem imageIdealSheaf_comp_comap_of_isIso {A B C : Sch} (w : A ⟶ B) [IsIso w] (g : B ⟶ C)
    (I : ISD B) :
    imageIdealSheaf (w ≫ g) (I.comap w) = imageIdealSheaf g I := by
  obtain ⟨th_, hth⟩ := exists_iso_subscheme_comap_of_isIso w I
  rw [imageIdealSheaf_eq_ker (w ≫ g) $ cmI I w, imageIdealSheaf_eq_ker g I, ← assoc, ← hth,
    assoc, ker_comp_of_isIso]

theorem ker_eq_of_iso_comp {P Q T : Sch} (c : Q ≅ P) (h1_ : P ⟶ T) (h2_ : Q ⟶ T)
    (hc : c.hom ≫ h1_ = h2_) : h1_.ker = h2_.ker := by
  rw [← hc, ker_comp_of_isIso]

theorem opens_map_id {B : Sch} W :
    (TopologicalSpace.Opens.map (𝟙 B : B ⟶ B).base).obj W = W := by
  ext x
  exact m22

theorem exists_iso_opens_preimage {A B : Sch} (th_ : A ≅ B) (V' : Opn A) (V : Opn B)
    (hVV' : V' = (TopologicalSpace.Opens.map th_.hom.base).obj V) :
    ∃ c : (↑V' : Sch) ≅ (↑V : Sch), c.hom ≫ ι V = ι V' ≫ th_.hom := by
  have hcomp : (m54 $ ibM th_).obj V'
      = (m54 (isoI th_ ≫ isoH th_).base).obj V := by
    rw [hVV', opens_map_comp]
  have hle : V ≤ (m54 $ ibM th_).obj V' :=
    le_of_eq $ by rw [hcomp, inv_hom_id, opens_map_id]
  refine ⟨⟨resLE th_.hom V V' $ le_of_eq hVV',
    resLE th_.inv V' V hle, ?_, ?_⟩, q4 ..⟩
  rw [← cancel_mono V'.i, assoc, q4, ← assoc,
    q4, assoc, hom_inv_id, comp_id, id_comp]
  rw [← cancel_mono V.i, assoc, q4, ← assoc,
    q4, assoc, inv_hom_id, comp_id, id_comp]

theorem imageIdealSheaf_strictTransform_of_comm_sq {X X1 Y Y1 : Sch}
    (ph_ : X1 ⟶ X) (ps_ : Y1 ⟶ Y) (u : X ⟶ Y) (u1 : X1 ⟶ Y1) [IsIso u] [IsIso u1]
    (hsq : u1 ≫ ps_ = ph_ ≫ u) (Z D : ISD X) :
    imageIdealSheaf u1 (Blowup.strictTransform ph_ Z D)
      = Blowup.strictTransform ps_ (imageIdealSheaf u Z) (imageIdealSheaf u D) := by
  have hps_ : ps_ = inv u1 ≫ ph_ ≫ u := by
    rw [← hsq, ← assoc, m117, id_comp]
  have hmaps : ps_ ≫ inv u = inv u1 ≫ ph_ := by
    rw [hps_, assoc, assoc, m118, comp_id]
  have hcm : ∀ I : ISD X,
      (imageIdealSheaf u I).comap ps_ = (cmI I ph_).comap (inv u1) := by
    intro I
    rw [imageIdealSheaf_eq_comap_inv,
      ← comap_comp,
      ← comap_comp, hmaps]
  obtain ⟨th_, hth⟩ := exists_iso_subscheme_comap_of_isIso (inv u1) $ cmI D ph_
  have hVV' : (m54 ((D.comap ph_).comap $ inv u1).subschemeι.base).obj
        ((Z.comap ph_).comap $ inv u1).support.compl
      = (m54 th_.hom.base).obj
        ((m54 (D.comap ph_).subschemeι.base).obj
          (cmI Z ph_).support.compl) := by
    rw [compl_support_comap, ← opens_map_comp, ← opens_map_comp, hth]
  obtain ⟨c, hc⟩ := exists_iso_opens_preimage th_ _ _ hVV'
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq,
    Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq, Blowup.strictTransformOpens_eq,
    hcm Z, hcm D, ← ker_comp_eq_imageIdealSheaf_ker]
  refine ker_eq_of_iso_comp c _ _ ?_
  simp [assoc]
  rw [← assoc c.hom, hc, assoc, reassoc_of% hth]
  simp

namespace IsPushforwardBlowupSeq

section
variable {S X} (j) [IsClosedImmersion j]
theorem of_isomorphic
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (he : B.Isomorphic B') :
    IsPushforwardBlowupSeq j BS B' := by
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  obtain ⟨hlen2, e, he0, hestep, hecent⟩ := he
  have hestep' : ∀ i (hp : i + 1 ≤ B.length) (hq : i ≤ B.length),
      (e (i + 1) hp).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ isoH (e i hq) :=
    fun i hp _ => hestep i hp
  have hecent' : ∀ i (hp : i < B.length) (hq : i ≤ B.length),
      (B'.center i).comap (e i hq).hom = B.center i := fun i hp _ => hecent i hp
  refine ⟨by omega, fun i hi => σ i hi ≫ isoH (e i (by omega)), ?_, ?_, ?_, ?_, ?_⟩
  intro i hi
  infer_instance
  have hgoal : (σ 0 (zero_le _) ≫ isoH (e 0 (zero_le _))) ≫ B'.isoZero.hom
      = BS.isoZero.hom ≫ j := by
    rw [assoc, he0, h0]
  exact hgoal
  intro i hi
  have hiB : i < B.length := by omega
  have hgoal : (σ (i + 1) hi ≫ isoH (e (i + 1) hiB)) ≫ B'.transitionMapSucc i
      = BS.transitionMapSucc i ≫ (σ i hi.le ≫ isoH (e i hiB.le)) := by
    rw [assoc, hestep' i hiB hiB.le, ← assoc, hstep i hi, assoc]
  exact hgoal
  intro i hi
  have hiB : i < B.length := by omega
  symm
  rw [imageIdealSheaf_comp, ← hcent i hi, ← hecent' i hiB hiB.le,
    imageIdealSheaf_comap]
  intro i hi
  have hiB : i < B.length := by omega
  have hcen : imageIdealSheaf (e i hiB.le).hom (B.center i) = B'.center i := by
    rw [← hecent' i hiB hiB.le, imageIdealSheaf_comap]
  rw [ker_comp_eq_imageIdealSheaf_ker, hker i hi,
    imageIdealSheaf_strictTransform_of_comm_sq (B.transitionMapSucc i) (B'.transitionMapSucc i)
      (e i hiB.le).hom (e (i + 1) hiB).hom (hestep' i hiB hiB.le) (B.center i)
      (m149 (σ i hi.le)),
    hcen, ker_comp_eq_imageIdealSheaf_ker]

theorem of_length_eq_zero
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hS : BS.length = 0) (hX : B.length = 0) :
    IsPushforwardBlowupSeq j BS B := by
  have key : ∀ i, i ≤ BS.length → i = 0 := fun i hi => by omega
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt $ key i hi) ≫ BS.isoZero.hom ≫ j ≫ B.isoZero.inv ≫
        eqToHom (congrArg B.schemeAt (key i hi).symm), ?_, ?_, ?_, ?_, ?_⟩
  intro i hi
  infer_instance
  simp
  simp_all
  simp_all
  simp_all
end

theorem isIso_comp {S' S X : Sch} (e : S' ⟶ S) [IsIso e]
    (j : S ⟶ X) [IsClosedImmersion j] (j' : S' ⟶ X) [IsClosedImmersion j']
    (hj : j' = e ≫ j)
    {BS' : SequenceOfBlowups S'} {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X}
    (hpb : IsStrictPullbackBlowupSeq e BS' BS) (h : IsPushforwardBlowupSeq j BS B) :
    IsPushforwardBlowupSeq j' BS' B := by
  obtain ⟨hlen2, ta_, hta0, htasq, htacent⟩ := hpb
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  have hiso : ∀ i (hi : i ≤ BS'.length), IsIso $ ta_ i hi := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hzz : ta_ 0 hi = BS'.isoZero.hom ≫ e ≫ BS.isoZero.inv := by
          rw [← assoc, ← (fun _ => hta0) hi]
          simp
        rw [hzz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < BS'.length := by omega
        exact (htasq n hn).isIso_fst_of_isIso
  refine ⟨by omega, fun i hi => ta_ i hi ≫ σ i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  intro i hi
  infer_instance
  have hgoal : (ta_ 0 (zero_le _) ≫ σ 0 (zero_le _)) ≫ B.isoZero.hom
      = BS'.isoZero.hom ≫ j' := by
    rw [hj, assoc, h0, ← assoc, hta0, assoc]
  exact hgoal
  intro i hi
  have hiS : i < BS.length := by omega
  have hgoal : (ta_ (i + 1) hi ≫ σ (i + 1) hiS) ≫ B.transitionMapSucc i
      = BS'.transitionMapSucc i ≫ (ta_ i hi.le ≫ σ i hiS.le) := by
    rw [assoc, hstep i hiS, ← assoc, (htasq i hi).w, assoc]
  exact hgoal
  intro i hi
  have hiS : i < BS.length := by omega
  symm
  rw [htacent i hi, hcent i hiS]
  exact imageIdealSheaf_comp_comap_of_isIso (ta_ i hi.le) (σ i hiS.le) $ BS.center i
  intro i hi
  have hiS : i < BS.length := by omega
  rw [ker_comp_of_isIso,
    ker_comp_of_isIso]
  exact hker i hiS

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

def AffineEmbedsIntoAffineSpace : Prop :=
  ∀ (k : Type) [Field k] (Y : Sch) [IsAffine Y]
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p],
    ∃ (n : ℕ) (e : Y ⟶ affineSpaceIndexedBy k (UFin n)),
      IsClosedImmersion e ∧ NonzeroOnComponents e.ker ∧
        e ≫ affineSpaceIndexedByToSpec k (UFin n) = p

def NilIsStrictNormalCrossingsOnAffineSpace : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ),
    InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k $ UFin n)
      ([] : List (affineSpaceIndexedBy k $ UFin n).IdealSheafData)

def AffineSpaceIsSmooth : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ),
    Smooth $ affineSpaceIndexedByToSpec k $ UFin n

def ClosedEmbeddingsRelatedByAutomorphism : Prop :=
  ∀ (k : Type) [Field k] (Y : Sch) [IsAffine Y]
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p] (n m : ℕ)
    (e1_ : Y ⟶ affineSpaceIndexedBy k (UFin n))
    [IsClosedImmersion e1_]
    (e2_ : Y ⟶ affineSpaceIndexedBy k (UFin m))
    [IsClosedImmersion e2_],
    e1_ ≫ affineSpaceIndexedByToSpec k (UFin n) = p →
    e2_ ≫ affineSpaceIndexedByToSpec k (UFin m) = p →
    ∃ Ph_ : affineSpaceIndexedBy k (UFS n m) ≅
            affineSpaceIndexedBy k (UFS n m),
      Ph_.hom ≫ affineSpaceIndexedByToSpec k (UFS n m) =
          affineSpaceIndexedByToSpec k (UFS n m) ∧
        AffineSpace.homOfVector p (coordVectorInl n m e1_) ≫ Ph_.hom =
          AffineSpace.homOfVector p (coordVectorInr n m e2_)

abbrev AffineResolutionRule : Type 1 :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y], SequenceOfBlowups Y

section
variable (R : AffineResolutionRule)
def IsCompatibleWithOpenImmersions : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y V : Sch)
    (pY : Y ⟶ Sp k) (pV : V ⟶ Sp k)
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    [IsReduced V] [IsAffine V]
    (ph_ : V ⟶ Y) [IsOpenImmersion ph_],
    ph_ ≫ pY = pV → IsPullbackBlowupSequence ph_ (R k V pV) (R k Y pY)

def IsCompatibleWithEtaleCovers : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y W : Sch)
    (pY : Y ⟶ Sp k) (pW : W ⟶ Sp k)
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType pW] [QuasiCompact pW]
    [IsReduced W] [IsAffine W]
    (ph_ : W ⟶ Y) [Etale ph_],
    ph_ ≫ pY = pW → (∀ y : ↥Y, ∃ w : ↥W, ph_.base w = y) →
    IsStrictPullbackBlowupSeq ph_ (R k W pW) (R k Y pY)

def IsCompatibleWithFieldBaseChange : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (K : Type) [Field K] [CharZero K] [Algebra k K]
    [IsReduced $ baseChange p K]
    [IsAffine $ baseChange p K],
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) $ baseChangeToSpec p K) $ R k Y p

def IsInducedByAffineRule (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) (B : SequenceOfBlowups Y) : Prop :=
  ∀ (W : Sch) (q : W ⟶ Sp k)
    [LocallyOfFiniteType q] [QuasiCompact q]
    [IsReduced W] [IsAffine W]
    (ph_ : W ⟶ Y) [Etale ph_],
    ph_ ≫ p = q → (∀ y : ↥Y, ∃ w : ↥W, ph_.base w = y) → IsStrictPullbackBlowupSeq ph_ (R k W q) B

def ExistsGluedBlowupSequence : Prop :=
  IsCompatibleWithEtaleCovers R →
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y],
    ∃ B : SequenceOfBlowups Y, (∀ i, i < B.length → B.center i ≠ ⊤) ∧ IsInducedByAffineRule R k Y p B

def InducedRuleCompatibleWithFieldExtension : Prop :=
  IsCompatibleWithOpenImmersions R → IsCompatibleWithFieldBaseChange R →
  ∀ F : ResolutionRule,
    (∀ (k : Type) [Field k] [CharZero k] (X : Sch)
      (f : X ⟶ Sp k) [LocallyOfFiniteType f]
      [QuasiCompact f] [IsReduced X],
      IsInducedByAffineRule R k X f $ F k X f) →
    IsCompatibleWithFieldExtension F
end


private theorem iso_hom_comp_projectionToBase {X' : Sch} {s' s'' : SequenceOfBlowups X'}
    (ep_ : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ≅ s''.schemeAt i))
    (h0 : (ep_ 0 $ zero_le _).hom ≫ s''.isoZero.hom = s'.isoZero.hom)
    (hst : ∀ i : ℕ, ∀ hi : i < s'.length,
      (ep_ (i + 1) hi).hom ≫ s''.transitionMapSucc i = s'.transitionMapSucc i ≫ (ep_ i hi.le).hom) :
    ∀ i : ℕ, ∀ hi : i ≤ s'.length, (ep_ i hi).hom ≫ s''.projectionToBase i = s'.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro hi
    rwa [s''.projectionToBase_zero, s'.projectionToBase_zero]
  | succ n ih =>
    intro hi
    rw [s''.projectionToBase_succ n, s'.projectionToBase_succ n, ← assoc,
      hst n hi, assoc, ih $ le_of_succ_le hi]

section
variable {X X'} (ph_ : X' ⟶ X) (s : SequenceOfBlowups X)
section
variable {a b} (h : a = b)
def pullbackProjectionToBaseIsoOfEq :
    Limits.pullback ph_ (s.projectionToBase a) ≅ Limits.pullback ph_ (s.projectionToBase b) :=
  eqToIso $ by rw [h]

theorem comap_pullbackIsoOfEq {W : Sch} (g : W ⟶ Limits.pullback ph_ (s.projectionToBase a)) :
    (s.center b).comap (g ≫ (pullbackProjectionToBaseIsoOfEq ph_ s h).hom ≫ snd ph_ (s.projectionToBase b))
      = (s.center a).comap (g ≫ snd ph_ (s.projectionToBase a)) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]

theorem pullbackIsoOfEq_hom_fst :
    (pullbackProjectionToBaseIsoOfEq ph_ s h).hom ≫ fst ph_ (s.projectionToBase b)
      = fst ph_ (s.projectionToBase a) := by
  subst h
  simp [pullbackProjectionToBaseIsoOfEq]
end

theorem pullbackIsoOfEq_hom_comp_pullbackTransitionMap {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
    (pullbackProjectionToBaseIsoOfEq ph_ s hb).hom ≫ s.pullbackTransitionMap ph_ hab'
      = s.pullbackTransitionMap ph_ hab ≫ (pullbackProjectionToBaseIsoOfEq ph_ s ha).hom := by
  subst ha
  subst hb
  have hpr : hab = hab' := rfl
  subst hpr
  simp [pullbackProjectionToBaseIsoOfEq]
end

section
variable {n m L : ℕ} {r q : ℕ → ℕ} {P : ℕ → Prop}
theorem strictMono_enumeration_le
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    ∀ i, i < n → i < m → r i ≤ q i := by
  have main : ∀ k i, i < k → i < n → i < m → r i ≤ q i := by
    intro k
    induction k with
    | zero => intro i hik; exact absurd hik $ not_lt_zero i
    | succ k ih =>
      intro i hik hin him
      by_contra hcon
      push Not at hcon
      have hqL := hq1 i him
      obtain ⟨j, hjn, hj⟩ := mp_ (hr4 (q i) hqL) $ mpr_ (hq4 (q i) hqL) ⟨i, him, rfl⟩
      have hji : j < i := by
        by_contra hc
        push Not at hc
        rcases Nat.eq_or_lt_of_le hc with h' | h'
        rw [← h'] at hj
        omega
        have hlt := hr2 i j hjn.le h'
        omega
      have h1 := ih j (by omega) (by omega) $ by omega
      have h2 := hq2 j i him.le hji
      omega
  intro i hin him
  exact main (i + 1) i (lt_succ_self i) hin him

theorem strictMono_enumeration_unique
    (hr1 : ∀ i, i < n → r i < L)
    (hr2 : ∀ i j : ℕ, j ≤ n → i < j → r i < r j)
    (hrn : r n = L)
    (hr4 : ∀ i, i < L → (P i ↔ ∃ j, j < n ∧ r j = i))
    (hq1 : ∀ i, i < m → q i < L)
    (hq2 : ∀ i j : ℕ, j ≤ m → i < j → q i < q j)
    (hqm : q m = L)
    (hq4 : ∀ i, i < L → (P i ↔ ∃ j, j < m ∧ q j = i)) :
    n = m ∧ ∀ i, i ≤ n → r i = q i := by
  have heq := fun i h1 h2 =>
    le_antisymm ((strictMono_enumeration_le hr2 hq1 hq2 hr4 hq4) i h1 h2) $ (strictMono_enumeration_le hq2 hr1 hr2 hq4 hr4) i h2 h1
  have hnm : n = m := by
    rcases lt_trichotomy n m with hlt | heqnm | hgt
    exfalso
    have hqn := hq1 n hlt
    obtain ⟨j, hjn, hj⟩ := mp (hr4 (q n) hqn) $ mpr (hq4 (q n) hqn) ⟨n, hlt, rfl⟩
    have ha := heq j hjn $ hjn.trans hlt
    have hb := hq2 j n hlt.le hjn
    omega
    exact heqnm
    exfalso
    have hrm := hr1 m hgt
    obtain ⟨j, hjm, hj⟩ := mp (hq4 (r m) hrm) $ mpr (hr4 (r m) hrm) ⟨m, hgt, rfl⟩
    have ha := heq j (hjm.trans hgt) hjm
    have hb := hr2 j m hgt.le hjm
    omega
  refine ⟨hnm, ?_⟩
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with h | h
  simp_all
  simp_all
end

namespace IsPullbackBlowupSequence

section
variable {X X'} {ph_} {s : SequenceOfBlowups X} {s' s'' : SequenceOfBlowups X'} (h : IsPullbackBlowupSequence ph_ s' s)
include h
theorem of_isomorphic (e : s'.Isomorphic s'') : IsPullbackBlowupSequence ph_ s'' s := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨hlen, ep_, h0, hst, hc⟩ := e
  have hcl : ∀ i, i ≤ s''.length → i ≤ s'.length := fun i hi => le_of_le_of_eq hi hlen.symm
  have hcl' : ∀ i, i < s''.length → i < s'.length := fun i hi => lt_of_lt_of_eq hi hlen.symm
  refine ⟨r, fun i hi => (ep_ i $ hcl i hi).symm ≪≫ E i (hcl i hi),
    fun i hi => hr1 i $ hcl' i hi, fun i j hj hij => hr2 i j (hcl j hj) hij,
    ?_, ?_, ?_, ?_, ?_⟩
  rwa [← hlen]
  intro i hi
  rw [hr4 i hi, hlen]
  intro i hi
  simp only [trans_hom, symm_hom, assoc, hfst i $ hcl i hi]
  rw [← (iso_hom_comp_projectionToBase ep_ h0 hst) i $ hcl i hi]
  simp
  intro i hi hr
  let _a0 := ep_ (i + 1) $ hcl' i hi
  have key : s''.transitionMapSucc i ≫ (ep_ i $ hcl i hi.le).inv
      = isoI _a0 ≫ s'.transitionMapSucc i := by
    rw [← cancel_iso_hom_left _a0, ← assoc, hst i $ hcl' i hi]
    simp
  simp only [trans_hom, symm_hom]
  rw [← assoc, key, assoc, hstepE i (hcl' i hi) hr, assoc]
  intro i hi
  simp only [trans_hom, symm_hom, assoc]
  rw [comap_comp, ← hcen i $ hcl' i hi, ← hc i $ hcl' i hi, ← comap_comp,
    inv_hom_id, comap_id]

theorem isomorphic (h' : IsPullbackBlowupSequence ph_ s'' s) : s'.Isomorphic s'' := by
  obtain ⟨r, E, hr1, hr2, hr3, hr4, hfst, hstepE, hcen⟩ := h
  obtain ⟨q, G, hq1, hq2, hq3, hq4, gfst, gstep, gcen⟩ := h'
  obtain ⟨hnm, hall⟩ := strictMono_enumeration_unique hr1 hr2 hr3 hr4 hq1 hq2 hq3 hq4
  refine ⟨hnm, fun i hi => E i hi ≪≫ pullbackProjectionToBaseIsoOfEq ph_ s (hall i hi) ≪≫
    (G i $ le_of_le_of_eq hi hnm).symm, ?_, ?_, ?_⟩
  have hG0 : isoI (G 0 $ le_of_le_of_eq (zero_le _) hnm) ≫ s''.projectionToBase 0
      = fst ph_ (s.projectionToBase $ q 0) := by
    rw [← gfst 0 $ le_of_le_of_eq (zero_le _) hnm]
    simp
  simp only [trans_hom, symm_hom, assoc]
  rw [← s''.projectionToBase_zero, hG0, pullbackIsoOfEq_hom_fst, hfst 0 $ zero_le _,
    s'.projectionToBase_zero]
  intro i hi
  have hr := ltLe $ hr2 i (i + 1) hi $ lt_succ_self i
  have hq' :=
    (hq2 i (i + 1) (le_of_le_of_eq hi hnm) $ lt_succ_self i).le
  have hGinv : isoI (G (i + 1) $ le_of_le_of_eq hi hnm) ≫ s''.transitionMapSucc i
      = s.pullbackTransitionMap ph_ hq' ≫ isoI (G i $ le_of_le_of_eq (le_of_succ_le hi) hnm) := by
    rw [← cancel_iso_hom_left $ G (i + 1) $ le_of_le_of_eq hi hnm, ← assoc,
      hom_inv_id, id_comp, ← assoc, ← gstep i (lt_of_lt_of_eq hi hnm) hq']
    simp
  have htrans := pullbackIsoOfEq_hom_comp_pullbackTransitionMap ph_ s (hall i $ le_of_succ_le hi)
    (hall (i + 1) hi) hr hq'
  simp only [trans_hom, symm_hom, assoc, hGinv]
  rw [reassoc_of% (hstepE i hi hr), reassoc_of% htrans]
  intro i hi
  simp only [trans_hom, symm_hom]
  rw [gcen i $ lt_of_lt_of_eq hi hnm, hcen i hi, ← comap_comp]
  simp only [assoc, inv_hom_id_assoc]
  exact comap_pullbackIsoOfEq ph_ s (hall i $ le_of_succ_le hi) _
end

end IsPullbackBlowupSequence




def SmoothPullbackHasLocalAmbientEmbedding : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X Y A : Sch)
    (pX : X ⟶ Sp k) (pY : Y ⟶ Sp k)
    (pA : A ⟶ Sp k) [IsAffine A] [Smooth pA]
    [LocallyOfFiniteType pA] [QuasiCompact pA]
    (i : X ⟶ A) [IsClosedImmersion i], i ≫ pA = pX →
    ∀ (M c : ℕ) (rh_ : A ⟶ affineSpaceIndexedBy k (UFin M)) [IsClosedImmersion rh_],
      rh_ ≫ affineSpaceIndexedByToSpec k (UFin M) = pA →
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFin M) rh_ c →
    ∀ (r : ℕ) (h : Y ⟶ X) [SmoothOfRelativeDimension r h], h ≫ pX = pY →
    ∀ y : Y,
      ∃ (V : Opn Y) (_ : y ∈ V) (_ : IsAffineOpen V)
        (A' : Sch) (pA' : A' ⟶ Sp k),
        IsAffine A' ∧ Smooth pA' ∧ LocallyOfFiniteType pA' ∧ QuasiCompact pA' ∧
        ∃ g : A' ⟶ A, Smooth g ∧ g ≫ pA = pA' ∧
          ∃ j : toScheme V ⟶ A', IsClosedImmersion j ∧
            IsPullback j (ι V ≫ h) g i ∧
            ∃ N0 : ℕ, r ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
              ∃ σ : A' ⟶ affineSpaceIndexedBy k (UFin $ M + N),
                IsClosedImmersion σ ∧
                σ ≫ affineSpaceIndexedByToSpec k (UFin $ M + N) = pA' ∧
                HasSmoothCoordCodim
                  (affineSpaceIndexedByToSpec k $ UFin $ M + N) σ (c + (N - r))





section
variable {X Y : Sch} (f : X ⟶ Y)
theorem closure_image_mem_irreducibleComponents_of_generalizingMap (hf : GeneralizingMap fun x : ↥X => f x)
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y := by
  have hCirr := an1 hC
  have hCmax := an2 hC
  have hCclosed : IsClosed C := by rw [← subset_antisymm (hCmax hCirr.closure subset_closure) subset_closure]
                                   exact isClosed_closure
  obtain ⟨et_, het_⟩ := m140 hCirr hCclosed
  have het' := het_
  have hetC : et_ ∈ C := by rw [← het']
                            exact subset_closure rfl
  have key : closure (imS f C) = closure ({f et_} : Set Y) := by
    have h1 : imS f C ⊆ closure ({f et_} : Set Y) := by
      rw [← het']
      intro w hw
      have hw2 := image_closure_subset_closure_image f.continuous hw
      rwa [image_singleton] at hw2
    have h2 : ({f et_} : Set Y) ⊆ imS f C :=
      mpr singleton_subset_iff $ mem_image_of_mem _ hetC
    exact subset_antisymm (closure_minimal h1 isClosed_closure) $ closure_mono h2
  have hmax : ∀ y, y ⤳ f et_ → y = f et_ := by
    intro y hy
    obtain ⟨x', hx'et, hfx'⟩ := hf hy
    have h1 := mp_ specializes_iff_mem_closure hx'et
    have h2 : C ⊆ closure ({x'} : Set X) := by
      rw [← het']
      exact closure_minimal (mpr_ singleton_subset_iff h1) isClosed_closure
    have hetx' : et_ ⤳ x' := mpr_ specializes_iff_mem_closure (by rw [het']; exact hCmax isIrreducible_singleton.closure h2 $ subset_closure rfl)
    have hins : Inseparable x' et_ := le_antisymm hx'et hetx'
    rw [← hfx', hins.eq]
  rw [key]
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro Z hZ hsub
  obtain ⟨z, hz⟩ := m140 hZ.closure isClosed_closure
  have hz' := hz
  have h1 : f et_ ∈ closure ({z} : Set Y) := by
    rw [hz']
    exact subset_closure $ hsub $ subset_closure rfl
  intro w hw
  rw [← (hmax z $ mpr_ specializes_iff_mem_closure h1), hz']
  exact subset_closure hw

theorem support_comap (I : ISD Y) :
    (support (I.comap f) : Set ↥X) = (fun x : ↥X => f x) ⁻¹' (support I : Set ↥Y) :=by simp_all
end

namespace NonzeroOnComponents

section
variable {X Y : Sch} {I : ISD Y} (hI : NonzeroOnComponents I) (f : X ⟶ Y)
include hI
theorem comap_of_generalizingMap
    (hf : GeneralizingMap fun x : ↥X => f x) :
    NonzeroOnComponents $ I.comap f := by
  intro T hT hsub
  refine hI _ (closure_image_mem_irreducibleComponents_of_generalizingMap f hf hT) ?_
  refine closure_minimal ?_ I.support.2
  rintro _ ⟨x, hxT, rfl⟩
  have hx := hsub hxT
  rwa [support_comap f I] at hx

theorem comap_of_flat [Flat f] :
    NonzeroOnComponents $ I.comap f :=
  hI.comap_of_generalizingMap f $ AlgebraicGeometry.Flat.generalizingMap f

theorem comap_of_isOpenImmersion [IsOpenImmersion f] :
    NonzeroOnComponents $ I.comap f :=
  hI.comap_of_generalizingMap f f.isOpenEmbedding.generalizingMap
end

end NonzeroOnComponents

section
variable (k : Type) [Field k] (n : ℕ)
theorem specIso_inv_comp_affineSpaceIndexedByToSpec :
    inv (AffineSpace.SpecIso (UFin n) $ CommRingCat.of k) ≫
        affineSpaceIndexedByToSpec k (UFin n) =
      Spec.map (ofHom
        (MvPolynomial.C : k →+* MvU n k)) :=
  AffineSpace.SpecIso_inv_over _

theorem affineSpaceIndexedByToSpec_eq :
    affineSpaceIndexedByToSpec k (UFin n) =
      (AffineSpace.SpecIso (UFin n) $ CommRingCat.of k).hom ≫
        Spec.map (ofHom
          (MvPolynomial.C : k →+* MvU n k)) := by
  rw [← specIso_inv_comp_affineSpaceIndexedByToSpec k n, hom_inv_id_assoc]
end

theorem affineSpaceIsSmooth : AffineSpaceIsSmooth := by
  intro k _ n
  have hC : Smooth
      (m12 $ ofHom
        (m8 : k →+* MvU n k)) :=
    (Spec_iff
      (P := @Smooth)).mpr $ mpr_ smooth_algebraMap $ ⟨inferInstance, inferInstance⟩
  rw [affineSpaceIndexedByToSpec_eq k n]
  infer_instance

theorem nilIsStrictNormalCrossingsOnAffineSpace : NilIsStrictNormalCrossingsOnAffineSpace := by
  intro k _ n
  refine ⟨by simp, fun x => ⟨⊤, trivial, n,
    ⟨opI (⊤ : (affineSpaceIndexedBy k $ UFin n).Opens), rfl, ?_⟩,
    fun _ => none, by simp, by simp, by simp⟩⟩
  infer_instance




def IsStrongResolution (k : Type) [Field k] (X : Sch)
    (f : X ⟶ Sp k) [LocallyOfFiniteType f]
    (s : SequenceOfBlowups X) : Prop :=
  Smooth (s.lastStructMap ≫ f) ∧
  IsProper s.lastStructMap ∧
  IsIso
    (morphismRestrict s.lastStructMap f.smoothLocus) ∧
  Dense (s.lastStructMap.base ⁻¹' (f.smoothLocus : Set X)) ∧
  s.CentersLieOver ((smoothLocusComplement f : Closeds X) : Set X) ∧
  IsStrictNormalCrossingsDivisor (reducedInverseImage s.lastStructMap $ smoothLocusComplement f)

theorem isStrongResolutionRule_iff R :
    IsStrongResolutionRule R ↔
      ∀ (k : Type) [Field k] [CharZero k] X
        f [LocallyOfFiniteType f]
        [QuasiCompact f] [IsReduced X],
        IsStrongResolution k X f $ R k X f :=
  m22

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

section

variable {X : Sch}

section
variable (s : SequenceOfBlowups X) {i j} (h : i = j)
def SequenceOfBlowups.schemeAtIsoOfEq : s.schemeAt i ≅ s.schemeAt j :=
  eqToIso $ congrArg s.schemeAt h

theorem SequenceOfBlowups.schemeAtIsoOfEq_hom_projectionToBase :
    (s.schemeAtIsoOfEq h).hom ≫ s.projectionToBase j = s.projectionToBase i := by
  subst h
  simp [SequenceOfBlowups.schemeAtIsoOfEq]
end

end

structure BlowupSequencePullbackComparison {S T : Sch} (ph_ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) where
  reindex : ℕ → ℕ
  iso : ∀ i : ℕ, i ≤ s'.length →
    (s'.schemeAt i ≅ (pullback ph_ (s.projectionToBase $ reindex i) : Sch))
  reindex_length : reindex s'.length = s.length
  retention : ∀ i : ℕ, i < s.length →
    ((∃ j : ℕ, ∃ _ : j < s'.length, reindex j = i) ↔
      ∃ x, x ∈ ((s.center i).comap $ pullback.snd ph_ $ s.projectionToBase i).support)
  iso_hom_fst : ∀ (i : ℕ) (h : i ≤ s'.length),
    (iso i h).hom ≫ pullback.fst ph_ (s.projectionToBase $ reindex i) = s'.projectionToBase i
  center_eq : ∀ (i : ℕ) (h : i < s'.length),
    s'.center i =
      (s.center $ reindex i).comap
        ((iso i h.le).hom ≫ pullback.snd ph_ (s.projectionToBase $ reindex i))

theorem nonempty_pullbackComparison_of_isPullback {S T : Sch} (ph_ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) (h : IsPullbackBlowupSequence ph_ s' s) : Nonempty $ BlowupSequencePullbackComparison ph_ s' s := by
  unfold IsPullbackBlowupSequence at h
  obtain ⟨r, e, hlt, hmono, hlen, hret, hfst, hblow, hcen⟩ := h
  refine ⟨⟨r, e, hlen, ?_, hfst, hcen⟩⟩
  simp_all

structure LocalResolutionData (k : Type) [instFieldk : Field k] {X : Sch}
    (f : X ⟶ Sp k) [LocallyOfFiniteType f] (s : SequenceOfBlowups X) where
  cover : AlgebraicGeometry.Scheme.OpenCover.{0, 0} X
  seq : ∀ i : cover.I₀, SequenceOfBlowups $ cover.X i
  isPullback : ∀ i : cover.I₀, IsPullbackBlowupSequence (cover.f i) (seq i) s
  finiteType : ∀ i : cover.I₀, LocallyOfFiniteType $ cover.f i ≫ f
  isResolution : ∀ i : cover.I₀,
    @IsStrongResolution k instFieldk (cover.X i) (cover.f i ≫ f) (finiteType i) $ seq i

attribute [instance] LocalResolutionData.finiteType

namespace LocalResolutionData

variable {k : Type} [Field k] {X} {f : X ⟶ Sp k}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

section
variable (d : LocalResolutionData k f s) (i : d.cover.I₀)
def comparison :
    BlowupSequencePullbackComparison (d.cover.f i) (d.seq i) s :=
  (nonempty_pullbackComparison_of_isPullback (d.cover.f i) (d.seq i) s $ d.isPullback i).some

def reindex : ℕ → ℕ := (d.comparison i).reindex

section
variable (j : ℕ)
section
variable (hj : j ≤ (d.seq i).length)
def schemeAtIsoPullback :
    ((d.seq i).schemeAt j ≅ (pullback (d.cover.f i) (s.projectionToBase $ d.reindex i j) : Sch)) :=
  (d.comparison i).iso j hj

theorem schemeAtIsoPullback_hom_fst :
    (d.schemeAtIsoPullback i j hj).hom ≫ pullback.fst (d.cover.f i) (s.projectionToBase $ d.reindex i j)
      = (d.seq i).projectionToBase j :=
  (d.comparison i).iso_hom_fst j hj
end

theorem localSequence_center_eq_comap
    (hj : j < (d.seq i).length) :
    (d.seq i).center j =
      (s.center $ d.reindex i j).comap
        ((d.schemeAtIsoPullback i j hj.le).hom ≫
          pullback.snd (d.cover.f i) (s.projectionToBase $ d.reindex i j)) :=
  (d.comparison i).center_eq j hj

theorem exists_reindex_eq_iff_exists_mem_support (hj : j < s.length) :
    ((∃ l : ℕ, ∃ _ : l < (d.seq i).length, d.reindex i l = j) ↔
      ∃ x, x ∈ ((s.center j).comap $ pullback.snd (d.cover.f i) $ s.projectionToBase j).support) :=
  (d.comparison i).retention j hj
end

theorem reindex_length :
    d.reindex i (d.seq i).length = s.length :=
  (d.comparison i).reindex_length

theorem pullback_projectionToBase_eq_pullback_lastStructMap :
    (pullback (d.cover.f i) (s.projectionToBase $ d.reindex i (d.seq i).length) : Sch)
      = (pullback (d.cover.f i) s.lastStructMap : Sch) := by
  exact tr_ (congrArg (fun n => (pullback (d.cover.f i) (s.projectionToBase n) : Sch)) $ d.reindex_length i) $ congrArg (fun g => (pullback (d.cover.f i) g : Sch)) s.lastStructMap_eq_projectionToBase.symm

def lastObjIsoPullback :
    ((d.seq i).lastObj ≅ (pullback (d.cover.f i) s.lastStructMap : Sch)) :=
  (d.schemeAtIsoPullback i (d.seq i).length le_rfl).trans $ eqToIso $ d.pullback_projectionToBase_eq_pullback_lastStructMap i

def chartToLastObj : (d.seq i).lastObj ⟶ s.lastObj :=
  (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap

theorem chartToLastObj_eq :
    d.chartToLastObj i = (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap :=
  rfl

theorem isOpenImmersion_chartToLastObj :
    IsOpenImmersion $ d.chartToLastObj i := by
  rw [d.chartToLastObj_eq i]
  infer_instance
end

theorem eqToHom_comp_pullback_fst {X0 X1 Y0 Y1 : Sch} (ph_ : X1 ⟶ X0)
    {g : Y0 ⟶ X0} {g' : Y1 ⟶ X0} (hY : Y0 = Y1) (hg : eqToHom hY ≫ g' = g)
    (e : (pullback ph_ g : Sch) = (pullback ph_ g' : Sch)) :
    eqToHom e ≫ pullback.fst ph_ g' = pullback.fst ph_ g := by
  subst hY
  simp [eqToHom_refl, id_comp] at hg
  subst hg
  simp

theorem lastObjIsoPullback_hom_fst (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (d.lastObjIsoPullback i).hom ≫ pullback.fst (d.cover.f i) s.lastStructMap = (d.seq i).lastStructMap := by
  let _a0 := congrArg s.schemeAt $ d.reindex_length i
  have hg : eqToHom _a0 ≫ s.lastStructMap
      = s.projectionToBase (d.reindex i (d.seq i).length) := by
    rw [s.lastStructMap_eq_projectionToBase]
    exact s.schemeAtIsoOfEq_hom_projectionToBase $ d.reindex_length i
  have key := eqToHom_comp_pullback_fst (d.cover.f i)
    _a0 hg $ d.pullback_projectionToBase_eq_pullback_lastStructMap i
  have e1 : (d.lastObjIsoPullback i).hom
      = (d.schemeAtIsoPullback i (d.seq i).length le_rfl).hom ≫ eqToHom (d.pullback_projectionToBase_eq_pullback_lastStructMap i) := rfl
  rw [e1, assoc, key, d.schemeAtIsoPullback_hom_fst i (d.seq i).length le_rfl,
    (d.seq i).lastStructMap_eq_projectionToBase]

private theorem base_comp_apply {A B C : Sch} (a : A ⟶ B) (b : B ⟶ C) (t : ↥A) :
    (a ≫ b).base t = b.base (a.base t) := by
  simp

instance instIsOpenImmersionChartEmbedding (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsOpenImmersion $ d.chartToLastObj i :=
  d.isOpenImmersion_chartToLastObj i

section
variable (d : LocalResolutionData k f s)
section
variable (i : d.cover.I₀)
theorem chartToLastObj_comp_lastStructMap :
    d.chartToLastObj i ≫ s.lastStructMap = (d.seq i).lastStructMap ≫ d.cover.f i := by
  rw [d.chartToLastObj_eq i, assoc, ← pullback.condition, ← assoc,
    d.lastObjIsoPullback_hom_fst i]

section
variable [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)]
theorem preimage_smoothLocus_cover_map :
    (d.cover.f i) ⁻¹ᵁ f.smoothLocus = (d.cover.f i ≫ f).smoothLocus := by
  exact preimage_smoothLocus_eq _ _

theorem preimage_smoothLocusComplement_cover_map :
    (d.cover.f i).base ⁻¹' ((smoothLocusComplement f : Closeds ↥X) : Set ↥X)
      = ((smoothLocusComplement (d.cover.f i ≫ f) :
          Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  let _a0 := d.cover.X i
  let _a1 := (d.cover.f i ≫ f).smoothLocus
  have h : (bsM (d.cover.f i) ⁻¹' (f.smoothLocus : Set X))
      = opS _a1 :=
    congrArg (fun U : Opens _a0 => (U : Set _a0))
      (d.preimage_smoothLocus_cover_map i)
  show bsM (d.cover.f i) ⁻¹' (f.smoothLocus : Set X)ᶜ
      = (_a1 : Set _a0)ᶜ
  rw [preimage_compl, h]
end
end

theorem exists_chartToLastObj_eq (x : ↥(s.lastObj)) :
    ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i).base y = x := by
  obtain ⟨w, hw⟩ := d.cover.covers $ s.lastStructMap.base x
  obtain ⟨p, hp1, hp2⟩ := exists_preimage_pullback w x hw
  refine ⟨d.cover.idx $ s.lastStructMap.base x, ibM (d.lastObjIsoPullback _) p, ?_⟩
  let _m0 := d.cover.idx $ s.lastStructMap.base x
  have h2 : isoI (d.lastObjIsoPullback _m0) ≫
      d.chartToLastObj _m0
      = pullback.snd (d.cover.f _m0) s.lastStructMap := by
    rw [d.chartToLastObj_eq, ← assoc, inv_hom_id, id_comp]
  have h3 := congrArg
    (fun m : (pullback (d.cover.f _m0) s.lastStructMap : Sch) ⟶ s.lastObj
      => bsM m p) h2
  simp at h3
  exact tr_ h3 hp2

theorem exists_chartToLastObj_apply_eq :
    ∀ x : ↥(s.lastObj), ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i) y = x :=
  d.exists_chartToLastObj_eq

def lastObjCover : AlgebraicGeometry.Scheme.OpenCover.{0, 0} s.lastObj :=
  mkOfCovers d.cover.I₀ (fun i => (d.seq i).lastObj)
    (fun i => d.chartToLastObj i) d.exists_chartToLastObj_apply_eq
    (fun i => d.isOpenImmersion_chartToLastObj i)
end

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type} [Field k] {X} {f}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem comp_base_apply__b27 {A B C : Sch} (a : A ⟶ B) (b : B ⟶ C) (z : ↥A) :
    (a ≫ b).base z = b.base (a.base z) := by
  simp

theorem hom_base_inv_base_apply {A B : Sch} (e : A ≅ B) (z : ↥B) :
    e.hom.base (e.inv.base z) = z :=by simp_all
theorem mem_support_comap_of_mem_support {Z W : Sch} (g : Z ⟶ W) (I : ISD W)
    (z : ↥Z) (hz : g.base z ∈ I.support) : z ∈ (I.comap g).support := by
  rwa [m19]

theorem centersLieOver_smoothLocusComplement (d : LocalResolutionData k f s) :
    s.CentersLieOver ((smoothLocusComplement f : Closeds ↥X) : Set ↥X) := by
  intro i hi x hx
  obtain ⟨i0_, u, hu⟩ : ∃ (i0_ : d.cover.I₀) (u : (d.cover.X i0_)),
      (d.cover.f i0_).base u = bsM (s.projectionToBase i) x := by
    obtain ⟨u, hu⟩ := d.cover.covers $ bsM (s.projectionToBase i) x
    exact ⟨d.cover.idx $ bsM (s.projectionToBase i) x, u, hu⟩
  obtain ⟨w, hw1, hw2⟩ := exists_preimage_pullback u x hu
  have hw2' := hw2
  have hws : w ∈ spI (cmI (s.center i) $ pullback.snd (d.cover.f i0_) $ s.projectionToBase i) := by
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rwa [hw2']
  obtain ⟨l, hl, hr⟩ := (d.exists_reindex_eq_iff_exists_mem_support i0_ i hi).2 ⟨w, hws⟩
  subst hr
  let _a1 := ibM (d.schemeAtIsoPullback i0_ l hl.le) w
  have ht : _a1 ∈ spI ((d.seq i0_).center l) := by
    rw [d.localSequence_center_eq_comap i0_ l hl]
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rwa [comp_base_apply__b27, hom_base_inv_base_apply, hw2']
  have key : bsM ((d.seq i0_).projectionToBase l) _a1
      = bsM (pullback.fst (d.cover.f i0_) $ s.projectionToBase $ d.reindex i0_ l) w := by
    rw [← d.schemeAtIsoPullback_hom_fst i0_ l hl.le, comp_base_apply__b27, hom_base_inv_base_apply]
  have hres := d.isResolution i0_
  unfold FunctorialResolution.EmbeddedResolution.IsStrongResolution at hres
  obtain ⟨-, -, -, -, hC, -⟩ := hres
  have hCt := hC l hl _ ht
  rw [← d.preimage_smoothLocusComplement_cover_map i0_] at hCt
  rwa [← hu, ← hw1, ← key]

end LocalResolutionData




namespace LocalResolutionData

variable {k : Type} [Field k] {X} {f : X ⟶ Sp k}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem dense_preimage_smoothLocus (d : LocalResolutionData k f s) :
    Dense ((s.lastStructMap.pre f.smoothLocus : Opens ↥(s.lastObj)) : Set ↥(s.lastObj)) := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨x, hxV⟩ := hVne
  obtain ⟨i, y, hy⟩ := d.exists_chartToLastObj_eq x
  let _a1 := (d.seq i).lastObj
  have hyW : y ∈ (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : Opens $ s.lastObj) :
      Opens _a1) : Set _a1) := by simp_all
  obtain ⟨z, hz1, hz2⟩ := mp_ dense_iff_inter_open ((d.isResolution i).2.2.2.1) _ (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : Opens $ s.lastObj)).2) ⟨y, hyW⟩
  let _a0 := bsM (d.chartToLastObj i) z
  refine ⟨_a0, hz1, ?_⟩
  have hmem := hz2
  rw [← d.preimage_smoothLocus_cover_map i] at hmem
  have hbase := by
    simpa using (congrArg (fun m : (d.seq i).lastObj ⟶ X => bsM m z) $ d.chartToLastObj_comp_lastStructMap i)
  show bsM (s.lastStructMap) _a0 ∈ f.smoothLocus
  rwa [hbase]

end LocalResolutionData





namespace LocalResolutionData

variable {k : Type} [Field k] {X} {f}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

section
variable (d : LocalResolutionData k f s)
include d
def pullbackIsoLastObj (i : d.cover.I₀) :
    ((pullback s.lastStructMap (d.cover.f i) : Sch) ≅ (d.seq i).lastObj) :=
  (pullbackSymmetry s.lastStructMap $ d.cover.f i).trans (d.lastObjIsoPullback i).symm

theorem pullbackIsoLastObj_hom_lastStructMap i :
    (d.pullbackIsoLastObj i).hom ≫ (d.seq i).lastStructMap = pullback.snd s.lastStructMap (d.cover.f i) := by
  rw [pullbackIsoLastObj]
  simp [trans_hom, symm_hom, assoc]
  rw [← d.lastObjIsoPullback_hom_fst i, inv_hom_id_assoc]
  exact pullbackSymmetry_hom_comp_fst _ _

theorem isProper_lastStructMap : IsProper s.lastStructMap := by
  have key : ∀ i, IsProper (d.seq i).lastStructMap := by
    intro i
    obtain ⟨-, h, -⟩ := d.isResolution i
    exact h
  obtain ⟨-, h2⟩ := (inferInstance :
    MorphismProperty.IsLocalAtTarget (@IsProper) zariskiPrecoverage)
  refine h2 (R := d.cover.presieve₀) d.cover.mem₀ ?_
  intro U g _inst hg
  obtain ⟨i⟩ := hg
  rw [← d.pullbackIsoLastObj_hom_lastStructMap i]
  infer_instance
end

end LocalResolutionData





namespace LocalResolutionData

variable {k : Type} [Field k] {X} {f}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

section
variable {A B} [IsAffine B] (g : A ⟶ B) (Wc_ : AlgebraicGeometry.Scheme.OpenCover.{0, 0} A) [hv0_4 : ∀ i, IsAffine (Wc_.X i)]
include hv0_4
theorem ringHom_smooth_appTop_of_smooth
    (hg : Smooth g) i :
    Smooth $ (Wc_.f i ≫ g).appTop.hom :=
  mp (iff_of_source_openCover Wc_) hg i

theorem smooth_of_ringHom_smooth_appTop
    (h : ∀ i : Wc_.I₀, Smooth $ (Wc_.f i ≫ g).appTop.hom) :
    Smooth g :=
  mpr (iff_of_source_openCover Wc_) h
end

section
variable (d : LocalResolutionData k f s)
include d
section
variable (j : d.cover.I₀)
theorem chartToLastObj_comp_lastStructMap_assoc :
    d.chartToLastObj j ≫ (s.lastStructMap ≫ f) = (d.seq j).lastStructMap ≫ (d.cover.f j ≫ f) := by
  rw [← assoc, d.chartToLastObj_comp_lastStructMap j, assoc]

theorem smooth_chartToLastObj_comp :
    Smooth $ d.chartToLastObj j ≫ (s.lastStructMap ≫ f) := by
  rw [d.chartToLastObj_comp_lastStructMap_assoc j]
  exact an1 $ d.isResolution j

theorem smooth_appTop_affineCover_chartToLastObj
    a :
    Smooth $ ((((d.seq j).lastObj.affineCover).f a ≫ d.chartToLastObj j)
      ≫ (s.lastStructMap ≫ f)).appTop.hom := by
  have h := ringHom_smooth_appTop_of_smooth (d.chartToLastObj j ≫ (s.lastStructMap ≫ f))
    ((d.seq j).lastObj.affineCover) (smooth_chartToLastObj_comp d j) a
  rwa [assoc]
end

theorem smooth_lastStructMap_comp :
    Smooth $ s.lastStructMap ≫ f := by
  have haffine : ∀ i : (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).I₀,
      IsAffine
        ((d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover).X i) := by
    rintro ⟨j, a⟩
    exact inferInstanceAs $ IsAffine $ ((d.lastObjCover.X j).affineCover).X a
  refine smooth_of_ringHom_smooth_appTop (s.lastStructMap ≫ f)
    (d.lastObjCover.bind fun j => (d.lastObjCover.X j).affineCover) ?_
  rintro ⟨j, a⟩
  exact smooth_appTop_affineCover_chartToLastObj d j a
end

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type} [Field k] {X} {f}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem support_vanishingIdeal_eq {Y : Sch} (Z : Closeds ↥Y) :
    support (vanishingIdeal Z) = Z := rfl

private theorem comap_vanishingIdeal_of_isOpenImmersion {Y T : Sch} (g : T ⟶ Y)
    [IsOpenImmersion g] (Z : Closeds ↥Y) (W : Closeds ↥T)
    (hW : (W : Set ↥T) = g.base ⁻¹' (Z : Set ↥Y)) :
    (vanishingIdeal Z).comap g
      = vanishingIdeal W := by
  let _a0 := cmI (vanishingIdeal Z) g
  have hrad : _a0.radical
      = _a0 := by
    refine m29 $ funext fun U => ?_
    rw [radical_ideal,
      ideal_comap_of_isOpenImmersion,
      vanishingIdeal_ideal]
    exact ((isRadical_vanishingIdeal _).comap _).radical
  have hsupp : support _a0 = W := by
    rw [m19, support_vanishingIdeal_eq]
    exact m134 hW.symm
  rw [← hsupp, vanishingIdeal_support, hrad]

theorem isRegularParameterSystem_of_ringEquiv_apply_eq {R S : Type} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R) (y : Fin n → S)
    (hxy : ∀ i, e (x i) = y i) (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n y := by
  have hy := sy_ $ funext hxy
  subst hy
  unfold IsRegularParameterSystem at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  have hmax : comap e (maximalIdeal S)
      = maximalIdeal R :=
    eq_maximalIdeal
      (comap_isMaximal_of_surjective e e.surjective)
  have hm : Ideal.map e (maximalIdeal R)
      = maximalIdeal S := by
    rw [← hmax]
    exact map_comap_of_surjective e e.surjective _
  have himg : span (range fun i => e $ x i)
      = Ideal.map e (span $ range x) := by
    rw [map_span]
    congr 1
    ext b
    constructor
    simp_all
    rintro ⟨a, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  rw [himg, h1, hm]
  rw [h2]
  exact ringKrullDim_eq_of_ringEquiv e

theorem surjective_iso_inv {A B : CRC} (e : A ≅ B) :
    Function.Surjective $ hom e.inv := by
  intro a
  refine ⟨(hom e.hom) a, ?_⟩
  simp

theorem map_eqToHom_germ {T : Sch} {U V}
    (h : Opposite.op U = Opposite.op V) z (hz : z ∈ U) (hz' : z ∈ V) :
    T.presheaf.map (eqToHom h) ≫ T.presheaf.germ V z hz' = T.presheaf.germ U z hz :=by simp_all
section
variable {Y T : Sch} (g : T ⟶ Y) [IsOpenImmersion g] (U) (z) (hz : z ∈ U) (hgz : g.base z ∈ (g.im U : Opn Y))
theorem appIso_inv_germ_stalkMap_apply
    (a : (T.sec U)) :
    (ConcreteCategory.hom $ stalkMap g z)
        ((ConcreteCategory.hom $ Y.presheaf.germ (g.im U) (g.base z) hgz)
          ((ConcreteCategory.hom (appIso g U).inv) a))
      = (ConcreteCategory.hom $ T.presheaf.germ U z hz) a := by
  have _i25 : isoI (appIso g U) ≫ pGerm Y (imU g U) (bsM g z) hgz ≫ stalkMap g z = pGerm T U z hz := by
    rw [germ_stalkMap g (imU g U) z hgz, ← assoc]
    simp
    exact map_eqToHom_germ _ z hz hgz
  have h := congrArg (fun m => (m23 m) a)
    _i25
  simpa only [m78] using h
end

section
variable (d : LocalResolutionData k f s) (i) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)]
theorem chartToLastObj_preimage_smoothLocusComplement :
    (d.chartToLastObj i).base ⁻¹'
        (s.lastStructMap.base ⁻¹' ((smoothLocusComplement f : Closeds ↥X) : Set ↥X))
      = (d.seq i).lastStructMap.base ⁻¹'
        ((smoothLocusComplement (d.cover.f i ≫ f) : Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  ext x
  simp only [mem_preimage]
  have hx := by
    simpa using (congrArg (fun g : (d.seq i).lastObj ⟶ X => bsM g x) $ d.chartToLastObj_comp_lastStructMap i)
  rw [hx, ← mem_preimage, d.preimage_smoothLocusComplement_cover_map i]

theorem comap_reducedInverseImage_chartToLastObj :
    (reducedInverseImage s.lastStructMap $ smoothLocusComplement f).comap (d.chartToLastObj i)
      = reducedInverseImage (d.seq i).lastStructMap (smoothLocusComplement $ d.cover.f i ≫ f) := by
  unfold reducedInverseImage
  exact comap_vanishingIdeal_of_isOpenImmersion (d.chartToLastObj i) _ _ (d.chartToLastObj_preimage_smoothLocusComplement i).symm
end

theorem isStrictNormalCrossingsDivisor_of_openCover {Y : Sch} (I : ISD Y)
    (H : ∀ y : ↥Y, ∃ (T : Sch) (g : T ⟶ Y) (_ : IsOpenImmersion g) (z : ↥T),
      g.base z = y ∧ IsStrictNormalCrossingsDivisor (I.comap g)) : IsStrictNormalCrossingsDivisor I := by
  intro y
  obtain ⟨T, g, hg, z, hzy, hSNC⟩ := H y
  subst hzy
  obtain ⟨hreg, U, hzU, n, F, J, hpar, hid⟩ := hSNC z
  let _a1 := stalkMap g z
  obtain ⟨E, hE⟩ : ∃ E : ((stkX Y (bsM g z)) : Type) ≃+* (stkX T z),
      ∀ x, E x = (ConcreteCategory.hom _a1) x :=
    ⟨(asIso _a1).commRingCatIsoToRingEquiv, fun _ => rfl⟩
  have hgz : bsM g z ∈ (g.im (U : Opn T) : Opn Y) := ⟨z, hzU, rfl⟩
  refine ⟨IsRegularLocalRing.of_ringEquiv E.symm,
    ⟨imU g U, (U.2 : IsAffineOpen (U : Opn T)).image_of_isOpenImmersion g⟩, hgz, n,
    fun i => (ConcreteCategory.hom (appIso g U).inv) (F i), J, ?_, ?_⟩
  refine isRegularParameterSystem_of_ringEquiv_apply_eq E.symm n _ _ ?_ hpar
  intro i
  have hgerm := appIso_inv_germ_stalkMap_apply g U z hzU hgz $ F i
  rw [← hE] at hgerm
  rw [← hgerm, E.symm_apply_apply]
  have h1 := ideal_comap_of_isOpenImmersion I g U
  rw [hid] at h1
  let _s0 := hom (appIso g U).inv
  have h2 : Ideal.map _s0
      (span {∏ i ∈ J, F i})
      = span {∏ i ∈ J,
          _s0 (F i)} := by
    rw [map_span, image_singleton, map_prod]
  exact tr_ (st_ (map_comap_of_surjective _ (surjective_iso_inv (appIso g U)) _)
    (congrArg (Ideal.map _s0)
      h1.symm)) h2

theorem isStrictNormalCrossingsDivisor_reducedInverseImage (d : LocalResolutionData k f s) [LocallyOfFinitePresentation f] :
    IsStrictNormalCrossingsDivisor $ reducedInverseImage s.lastStructMap $ smoothLocusComplement f := by
  refine isStrictNormalCrossingsDivisor_of_openCover _ ?_
  intro y
  obtain ⟨i, z, hz⟩ := d.exists_chartToLastObj_eq y
  refine ⟨(d.seq i).lastObj, d.chartToLastObj i, inferInstance, z, hz, ?_⟩
  rw [d.comap_reducedInverseImage_chartToLastObj i]
  exact (d.isResolution i).2.2.2.2.2

end LocalResolutionData




theorem mem_specMap_asIdeal {A B : CRC} (ps_ : A ⟶ B)
    (q : PrimeSpectrum B) (a : A) :
    a ∈ asIdeal ((Spec.map ps_) q) ↔ (ConcreteCategory.hom ps_) a ∈ asIdeal q := m22

theorem vanishingIdeal_preimage_specMap {A B : CRC} (ph_ : A ⟶ B) [IsIso ph_]
    (W : Set $ PrimeSpectrum A) :
    PrimeSpectrum.vanishingIdeal (⇑(Spec.map ph_) ⁻¹' W)
      = Ideal.map (ConcreteCategory.hom ph_) (PrimeSpectrum.vanishingIdeal W) := by
  have hinv : ∀ p,
      ((m12 ph_) ((m12 $ inv ph_) p) : PrimeSpectrum A) = p := by
    intro p
    apply m210
    apply Ideal.ext
    intro a
    constructor
    intro hmem
    have h1 :=
      mp (mem_specMap_asIdeal (inv ph_) p _) $ mp_ (mem_specMap_asIdeal ph_ _ a) hmem
    rwa [hom_inv_id_apply] at h1
    intro hmem
    refine mpr_ (mem_specMap_asIdeal ph_ _ a) ?_
    refine mpr_ (mem_specMap_asIdeal (inv ph_) p _) ?_
    rwa [hom_inv_id_apply]
  apply le_antisymm
  intro a ha
  rw [mem_vanishingIdeal] at ha
  have hmem : (m23 $ inv ph_) a ∈ m184 W := by
    rw [mem_vanishingIdeal]
    intro p hp
    exact mp_ (mem_specMap_asIdeal (inv ph_) p a) $ ha _ $ cast (congrArg (fun x => x ∈ W) $ hinv p).symm hp
  have h5 := mem_map_of_mem (m23 ph_) hmem
  rwa [inv_hom_id_apply] at h5
  rw [map_le_iff_le_comap]
  intro a ha
  rw [mem_vanishingIdeal] at ha
  rw [mem_comap, mem_vanishingIdeal]
  intro q hq
  exact mp_ (mem_specMap_asIdeal ph_ q a) $ ha _ hq

section
variable {X : Sch}
theorem eqToIso_hom_comp_projectionToBase_of_eq (s : SequenceOfBlowups X) {i j : ℕ}
    (hij : i = j) : (eqToIso $ congrArg s.schemeAt hij).hom ≫ s.projectionToBase j = s.projectionToBase i := by
  subst hij
  simp

theorem iso_hom_comp_projectionToBase_of_commute_blowupMorphism {B B' : SequenceOfBlowups X}
    (e : ∀ i : ℕ, i ≤ B.length → (B.schemeAt i ≅ B'.schemeAt i))
    (h0 : (e 0 $ zero_le _).hom ≫ B'.isoZero.hom = B.isoZero.hom)
    (hstep : ∀ i : ℕ, ∀ hi : i < B.length,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) :
    ∀ i hi, (e i hi).hom ≫ B'.projectionToBase i = B.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro _
    rwa [B'.projectionToBase_zero, B.projectionToBase_zero]
  | succ n ih =>
    intro hi
    have hn : n < B.length := hi
    rw [B'.projectionToBase_succ, B.projectionToBase_succ, ← assoc, hstep n hn, assoc, ih hn.le]

theorem SequenceOfBlowups.Isomorphic.exists_lastObjIso {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') :
    ∃ e : B.lastObj ≅ B'.lastObj, e.hom ≫ B'.lastStructMap = B.lastStructMap := by
  obtain ⟨hL, e, h0, hstep, _⟩ := h
  refine ⟨e B.length le_rfl ≪≫ eqToIso (congrArg B'.schemeAt hL), ?_⟩
  rw [SequenceOfBlowups.lastStructMap_eq_projectionToBase, SequenceOfBlowups.lastStructMap_eq_projectionToBase, trans_hom,
    assoc, eqToIso_hom_comp_projectionToBase_of_eq B' hL]
  exact iso_hom_comp_projectionToBase_of_commute_blowupMorphism e h0 hstep B.length le_rfl

theorem SequenceOfBlowups.Isomorphic.trans {B B' B'' : SequenceOfBlowups X}
    (h : B.Isomorphic B') (h' : B'.Isomorphic B'') : B.Isomorphic B'' := by
  obtain ⟨hL, e, h0, hstep, hcen⟩ := h
  obtain ⟨hL', g, g0, gstep, gcen⟩ := h'
  have p1 : (isoH (e 0 $ zero_le _) ≫ isoH (g 0 $ zero_le _)) ≫ B''.isoZero.hom
      = B.isoZero.hom := by simp_all
  have p2 : ∀ i (hi : i < length B),
      (isoH (e (i + 1) hi) ≫ isoH (g (i + 1) $ by omega)) ≫ B''.transitionMapSucc i
        = B.transitionMapSucc i ≫ (isoH (e i hi.le) ≫ isoH (g i $ by omega)) := by simp_all
  refine ⟨tr_ hL hL', fun i hi => (e i hi) ≪≫ (g i $ by omega), p1, p2, ?_⟩
  simp_all
end

section
variable {Y Z : Sch}
private theorem mem_support_of_mem_support_comap (g : Y ⟶ Z)
    (I : ISD Z) {x : Y} (hx : x ∈ support (I.comap g)) : g x ∈ support I := by
  rwa [m19 I g] at hx

theorem isIso_restrict_of_eq {f1_ f2_ : Y ⟶ Z} (hf : f1_ = f2_)
    (U : Opn Z) (h : IsIso $ f1_ ∣_ U) : IsIso $ f2_ ∣_ U := by
  subst hf
  exact h
end

section
variable {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
theorem map_mem_maximalIdeal_ringEquiv {a}
    (h : a ∈ maximalIdeal R) : e a ∈ maximalIdeal S :=by simp_all
theorem isRegularParameterSystem_ringEquiv (n : ℕ) (x : Fin n → R)
    (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n fun i => e $ x i := by
  obtain ⟨hspan, hdim⟩ := h
  have hle : span (range fun i => e $ x i) ≤ maximalIdeal S := by
    rw [span_le]
    rintro z ⟨i, rfl⟩
    refine map_mem_maximalIdeal_ringEquiv e ?_
    rw [← hspan]
    exact subset_span ⟨i, rfl⟩
  refine ⟨le_antisymm hle ?_, tr_ hdim $ ringKrullDim_eq_of_ringEquiv e⟩
  intro y hy
  have h1 : span (range x)
      ≤ comap e (span $ range fun i => e $ x i) := by
    rw [span_le]
    rintro z ⟨i, rfl⟩
    simp [mem_coe]
    exact subset_span ⟨i, rfl⟩
  have h3 : e.symm y ∈ span (range x) := by rw [hspan]
                                            exact map_mem_maximalIdeal_ringEquiv e.symm hy
  have h4 := h1 h3
  rw [mem_comap] at h4
  simpa using h4
end

theorem vanishingIdeal_preimage_fromSpec_of_isIso {Y Y' : Sch} (ps_ : Y' ⟶ Y) [IsIso ps_]
    (T : Set Y) (U : Y.affineOpens) (hV : IsAffineOpen $ pre ps_ (U : Opn Y)) :
    PrimeSpectrum.vanishingIdeal (⇑hV.fromSpec ⁻¹' (⇑ps_ ⁻¹' T))
      = Ideal.map (ConcreteCategory.hom $ ps_.app (U : Opn Y))
          (PrimeSpectrum.vanishingIdeal $ ⇑U.2.fromSpec ⁻¹' T) := by
  have : IsIso $ ps_.app U := inferInstance
  have hU := U.2
  have happ : appLE ps_ U (preU ps_ U) le_rfl = ps_.app U := by
    simp [appLE]
  have hsq : m12 (ps_.app U) ≫ hU.fromSpec = hV.fromSpec ≫ ps_ := by
    rw [← happ]
    exact SpecMap_appLE_fromSpec ps_ hU hV le_rfl
  have hpt : ∀ z, ps_ (hV.fromSpec z) = hU.fromSpec ((m12 $ ps_.app U) z) := by
    intro z
    have h := congrArg
      (fun m : Spec Γ(Y', preU ps_ U) ⟶ Y => m z) hsq
    simpa using sy_ h
  exact m32 (congrArg m184 (Set.ext fun z => iff_of_eq (congrArg (· ∈ T) $ hpt z))) $ vanishingIdeal_preimage_specMap (ps_.app U) $ pIm hU.fromSpec T

theorem isRegularParameterSystem_congr {R : Type} [CommRing R] [IsLocalRing R]
    (n : ℕ) {x y : Fin n → R} (h : ∀ i, x i = y i) (hy : IsRegularParameterSystem R n y) :
    IsRegularParameterSystem R n x := by
  rwa [funext h]

theorem isStrictNormalCrossingsDivisor_reducedInverseImage_iso_inv_comp {Y Y' X : Sch} (g : Y ≅ Y') (p : Y ⟶ X)
    (S : Closeds X) (hS : IsStrictNormalCrossingsDivisor $ reducedInverseImage p S) :
    IsStrictNormalCrossingsDivisor $ reducedInverseImage (inv g ≫ p) S := by
  intro y'
  obtain ⟨hreg, U, hy, n, fs, J, hrsp, hideal⟩ := hS $ ibM g y'
  have hsi : IsIso $ g.inv.stalkMap y' := inferInstance
  have hV := U.2.preimage_of_isIso g.inv
  let _a1 := asIso $ g.inv.stalkMap y'
  have he : ∀ t, _a1.commRingCatIsoToRingEquiv t
      = (ConcreteCategory.hom $ g.inv.stalkMap y') t := fun _ => rfl
  have hnat : ∀ s,
      (ConcreteCategory.hom $ pGerm Y' (g.inv.pre U) y' hy)
          ((ConcreteCategory.hom $ g.inv.app U) s)
        = _a1.commRingCatIsoToRingEquiv
            ((ConcreteCategory.hom $ pGerm Y U (ibM g y') hy) s) := by simp_all
  refine ⟨?_, ⟨g.inv.pre U, hV⟩, hy, n,
    fun i => (ConcreteCategory.hom $ g.inv.app U) $ fs i, J, ?_, ?_⟩
  exact IsRegularLocalRing.of_ringEquiv (asIso $ g.inv.stalkMap y').commRingCatIsoToRingEquiv
  exact isRegularParameterSystem_congr n (fun i => hnat $ fs i) $ isRegularParameterSystem_ringEquiv (asIso $ g.inv.stalkMap y').commRingCatIsoToRingEquiv n (fun i => (ConcreteCategory.hom $ pGerm Y U (ibM g y') hy) $ fs i) hrsp
  have h1 : (reducedInverseImage (isoI g ≫ p) S).ideal ⟨g.inv.pre U, hV⟩
      = PrimeSpectrum.vanishingIdeal
          (hV.fromSpec ⁻¹' ((isoI g ≫ p) ⁻¹' S)) := by
    simp [reducedInverseImage, vanishingIdeal_ideal]
  have h2 : (reducedInverseImage p S).ideal U
      = PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (p ⁻¹' S)) := by
    simp [reducedInverseImage, vanishingIdeal_ideal]
  have hcomp : (preimage (isoI g ≫ p) S) = preimage g.inv (p ⁻¹' S) := by
    ext z
    simp
  rw [h1, hcomp, vanishingIdeal_preimage_fromSpec_of_isIso g.inv (preimage p S) U hV, ← h2, hideal,
    map_span]
  simp [map_prod]

theorem SequenceOfBlowups.Isomorphic.symm {X : Sch} {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') : B'.Isomorphic B := by
  obtain ⟨hL, e, h0, hstep, hcen⟩ := h
  have p1 := sy_ h0
  rw [← inv_comp_eq] at p1
  have p2 : ∀ i (hi : i < length B'),
      inv (e (i + 1) $ by omega) ≫ B.transitionMapSucc i
        = B'.transitionMapSucc i ≫ isoI (e i $ by omega) := by
    intro i hi
    have hi' : i < length B := by omega
    rw [inv_comp_eq, ← assoc, hstep i hi', assoc, hom_inv_id, comp_id]
  have p3 : ∀ i (hi : i < length B'),
      (B.center i).comap (e i $ by omega).inv = B'.center i := by
    intro i hi
    have hi' : i < length B := by omega
    rw [← hcen i hi', ← comap_comp, inv_hom_id,
      comap_id]
  exact ⟨hL.symm, fun i hi => (e i $ by omega).symm, p1, p2, p3⟩

theorem IsStrongResolution.of_isomorphic (k : Type) [Field k] (X : Sch)
    (f : X ⟶ Sp k) [LocallyOfFiniteType f]
    {B B' : SequenceOfBlowups X} (h : B.Isomorphic B') (hB : IsStrongResolution k X f B) :
    IsStrongResolution k X f B' := by
  obtain ⟨ep_, hep⟩ := h.exists_lastObjIso
  obtain ⟨hs, hp, hiso, hd, hc, hsnc⟩ := hB
  have hmap : B'.lastStructMap = isoI ep_ ≫ B.lastStructMap := by
    rw [← hep, ← assoc, inv_hom_id, id_comp]
  have q1 : Smooth $ B'.lastStructMap ≫ f := by
    rw [hmap, assoc]
    infer_instance
  have q2 : IsProper B'.lastStructMap := by
    rw [hmap]
    infer_instance
  have q3 : IsIso
      (morphismRestrict B'.lastStructMap f.smoothLocus) := by
    have hres : IsIso $ ep_.hom.mr $ B'.lastStructMap.pre f.smoothLocus := inferInstance
    have hA : IsIso $ ep_.hom.mr (B'.lastStructMap.pre f.smoothLocus) ≫ B'.lastStructMap.mr f.smoothLocus := by
      have h0 :=
        isIso_restrict_of_eq hep.symm f.smoothLocus hiso
      rwa [AlgebraicGeometry.morphismRestrict_comp] at h0
    exact of_isIso_comp_left (ep_.hom.mr $ B'.lastStructMap.pre f.smoothLocus)
      (B'.lastStructMap.mr f.smoothLocus)
  have q4 : Dense $ preimage B'.lastStructMap f.smoothLocus := by
    have hpre : preimage B'.lastStructMap f.smoothLocus
        = preimage ep_.inv (pIm B.lastStructMap f.smoothLocus) := by
      rw [hmap]
      ext x
      simp
    rw [hpre]
    exact hd.preimage $ (m207 ep_.symm).isOpenMap
  have q5 : B'.CentersLieOver ((smoothLocusComplement f) : Set X) := by
    obtain ⟨hL, eiso, h0, hstep, hcen⟩ := h
    intro i hi x hx
    have hi' : i < B.length := by omega
    let _a0 := eiso i hi'.le
    have hy : isoI _a0 x ∈ ((B'.center i).comap _a0.hom).support := by
      let I := B'.center i
      have hI : (I.comap _a0.hom).comap _a0.inv = I := by
        rw [← comap_comp, inv_hom_id, comap_id]
      refine mem_support_of_mem_support_comap _a0.inv (I.comap _a0.hom) ?_
      rwa [hI]
    rw [hcen i hi'] at hy
    have hpt := hc i hi' _ hy
    have hinv : isoI _a0 ≫ B.projectionToBase i = B'.projectionToBase i := by
      rw [← iso_hom_comp_projectionToBase_of_commute_blowupMorphism eiso h0 hstep i hi'.le, ← assoc, inv_hom_id, id_comp]
    have hval : B'.projectionToBase i x = B.projectionToBase i (isoI _a0 x) := by
      rw [← hinv]
      simp
    rwa [hval]
  refine ⟨q1, q2, q3, q4, q5, ?_⟩
  rw [hmap]
  exact isStrictNormalCrossingsDivisor_reducedInverseImage_iso_inv_comp ep_ B.lastStructMap (smoothLocusComplement f) hsnc





namespace LocalResolutionData

variable {k : Type} [Field k] {X : Sch} {f : X ⟶ Sp k}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

section
variable (d : LocalResolutionData k f s)
include d
theorem isPullback_chartToLastObj i :
    IsPullback (d.chartToLastObj i) ((d.seq i).lastStructMap) s.lastStructMap $ d.cover.f i := by
  exact (of_iso_pullback ⟨sy_ $ d.chartToLastObj_comp_lastStructMap i⟩ (d.lastObjIsoPullback i) (d.lastObjIsoPullback_hom_fst i) (d.chartToLastObj_eq i).symm).flip

theorem exists_restrict_smoothLocus_apply_eq :
    ∀ x : ↥(f.smoothLocus.toScheme), ∃ (i : d.cover.I₀)
      (y : ↥(toScheme $ d.cover.f i ⁻¹ᵁ f.smoothLocus)),
        (d.cover.f i ∣_ f.smoothLocus) y = x := by
  intro x
  have hx : x.1 ∈ (⨆ i, (d.cover.f i).opensRange : Opn X) := by
    rw [d.cover.iSup_opensRange]
    trivial
  obtain ⟨i, hi⟩ := mp_ mem_iSup hx
  obtain ⟨y0_, hy0_⟩ := hi
  have hmem := by
    show bsM (d.cover.f i) y0_ ∈ f.smoothLocus
    rw [hy0_]
    exact x.2
  refine ⟨i, ⟨y0_, hmem⟩, ?_⟩
  exact tr_ (congrFun (morphismRestrict_base (d.cover.f i) f.smoothLocus) ⟨y0_, hmem⟩) $ m26 hy0_

def smoothLocusOpenCover :
    AlgebraicGeometry.Scheme.OpenCover.{0, 0} $ f.smoothLocus.toScheme :=
  mkOfCovers d.cover.I₀
    (fun i => toScheme $ d.cover.f i ⁻¹ᵁ f.smoothLocus)
    (fun i => d.cover.f i ∣_ f.smoothLocus)
    (exists_restrict_smoothLocus_apply_eq d)
    (fun i => show IsOpenImmersion (d.cover.f i ∣_ f.smoothLocus) from inferInstance)

theorem isIso_lastStructMap_restrict_smoothLocus :
    IsIso (s.lastStructMap ∣_ f.smoothLocus) := by
  have hh : ∀ i : d.cover.I₀, MorphismProperty.isomorphisms Sch
      (pullbackHom (smoothLocusOpenCover d) (s.lastStructMap.mr f.smoothLocus) i) := by
    intro i
    have hp := isPullback_morphismRestrict s.lastStructMap f.smoothLocus
    have hc := isPullback_morphismRestrict (d.cover.f i) f.smoothLocus
    have ht := isPullback_morphismRestrict ((d.seq i).lastStructMap) (d.cover.f i ⁻¹ᵁ f.smoothLocus)
    have hbig := ht.paste_vert (d.isPullback_chartToLastObj i).flip
    have hw := hbig.w
    rw [← hc.w, ← assoc] at hw
    have hsq : IsPullback ((d.seq i).lastStructMap ∣_ (d.cover.f i ⁻¹ᵁ f.smoothLocus))
        (hp.lift _ _ hw) (d.cover.f i ∣_ f.smoothLocus) (mrU s.lastStructMap f.smoothLocus) := by
      refine of_bot ?_ ?_ hp
      simp_all
      rw [hp.lift_fst]
    have hiso := (d.isResolution i).2.2.1
    rw [← d.preimage_smoothLocus_cover_map i] at hiso
    have hcomp := hiso
    rw [← hsq.flip.isoPullback_hom_snd] at hcomp
    exact of_isIso_comp_left hsq.flip.isoPullback.hom
      (pullback.snd (mrU s.lastStructMap f.smoothLocus) (d.cover.f i ∣_ f.smoothLocus))
  exact IsZariskiLocalAtTarget.of_openCover (smoothLocusOpenCover d) hh
end

end LocalResolutionData




section
variable {X : Sch}
private theorem transitionMap_self (u : SequenceOfBlowups X) {a : ℕ}
    (h : a ≤ a) : u.transitionMap h = 𝟙 (u.schemeAt a) := by
  have h0 : (CategoryTheory.homOfLE h).op = 𝟙 (m112 a) := rfl
  rw [u.transitionMap_def, h0, CategoryTheory.Functor.map_id]

section
variable (s t : SequenceOfBlowups X) (L : ℕ) (e : ∀ i : ℕ, i ≤ L → (s.schemeAt i ≅ t.schemeAt i)) (hstep : ∀ i : ℕ, ∀ hi : i < L, (e (i + 1) hi).hom ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ (e i hi.le).hom)
include hstep
theorem SequenceOfBlowups.iso_hom_comp_transitionMap :
    ∀ a b, ∀ hab : a ≤ b, ∀ hb,
      (e b hb).hom ≫ t.transitionMap hab = s.transitionMap hab ≫ (e a $ hab.trans hb).hom := by
  intro a b hab
  induction b, hab using le_induction with
  | base =>
      intro hb
      rw [transitionMap_self t $ le_refl a, transitionMap_self s $ le_refl a, comp_id, id_comp]
  | succ n hn ih =>
      intro hb
      have h1 := le_succ n
      rw [← t.transitionMap_trans hn h1, ← s.transitionMap_trans hn h1, ← t.blowupMorphism_eq_transitionMap n,
        ← s.blowupMorphism_eq_transitionMap n, ← assoc, hstep n hb, assoc, ih $ le_of_succ_le hb]
      simp

theorem SequenceOfBlowups.iso_hom_comp_projectionToBase
    (hzero : (e 0 $ zero_le _).hom ≫ t.isoZero.hom = s.isoZero.hom) :
    ∀ b : ℕ, ∀ hb : b ≤ L, (e b hb).hom ≫ t.projectionToBase b = s.projectionToBase b := by
  intro b hb
  rw [FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def, ← assoc,
    (FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.iso_hom_comp_transitionMap s t L e hstep 0 b (zero_le b) hb), assoc, hzero]
end
end

section
variable {X' X : Sch}
theorem isPullback_transitionMap_of_isPullback_blowupMorphism
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) $ σ i hi.le) :
    ∀ a b : ℕ, ∀ hab : a ≤ b, ∀ hb : b ≤ L,
      IsPullback (σ b hb) (t.transitionMap hab) (s.transitionMap hab) $ σ a $ hab.trans hb := by
  intro a b hab
  induction b, hab using le_induction with
  | base =>
      intro hb
      rw [transitionMap_self, transitionMap_self]
      exact (of_horiz_isIso ⟨by simp⟩).flip
  | succ b hab ih =>
      intro hb
      have hlt : b < L := hb
      have key := (hstep b hlt).paste_vert $ ih hlt.le
      let _a0 := hab.trans $ le_succ b
      have e1_ : t.transitionMapSucc b ≫ t.transitionMap hab = t.transitionMap _a0 := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_trans]
      have e2_ : s.transitionMapSucc b ≫ s.transitionMap hab = s.transitionMap _a0 := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_trans]
      rwa [e1_, e2_] at key

theorem isPullback_projectionToBase_of_isPullback_blowupMorphism (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : σ 0 (zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) $ σ i hi.le) :
    ∀ b : ℕ, ∀ hb : b ≤ L,
      IsPullback (σ b hb) (t.projectionToBase b) (s.projectionToBase b) g := by
  intro b hb
  rw [t.projectionToBase_def b, s.projectionToBase_def b]
  exact (isPullback_transitionMap_of_isPullback_blowupMorphism t s L σ hstep 0 b (zero_le b) hb).paste_vert $ (of_horiz_isIso ⟨sy_ hzero⟩).flip

theorem surjective_of_isPullback_blowupMorphism (g : X' ⟶ X)
    [Surjective g]
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : σ 0 (zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) $ σ i hi.le) :
    ∀ i : ℕ, ∀ hi : i ≤ L, Surjective $ σ i hi := by
  intro i hi
  exact m98 (P := @Surjective) (isPullback_projectionToBase_of_isPullback_blowupMorphism g t s L σ hzero hstep i hi).flip inferInstance
end

namespace IsStrictPullbackBlowupSeq

section
variable {X' X : Sch} {g : X' ⟶ X}
theorem of_isomorphic_pullback
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (he : t.Isomorphic t') :
    IsStrictPullbackBlowupSeq g t' s := by
  have hlen := an1 h
  obtain ⟨σ, hzero, hpb, hcen⟩ := an2 h
  have hlen' := he.1
  obtain ⟨e, hezero, hestep, hecen⟩ := he.2
  have hconv : ∀ i, i ≤ t'.length → i ≤ t.length := fun i hi => by omega
  refine ⟨st_ hlen' hlen,
    fun i hi => isoI (e i $ hconv i hi) ≫ σ i (hconv i hi), ?_, ?_, ?_⟩
  have key : (isoI (e 0 $ hconv 0 $ zero_le t'.length) ≫
      σ 0 (hconv 0 $ zero_le t'.length)) ≫ s.isoZero.hom = t'.isoZero.hom ≫ g := by
    rw [assoc, hzero, inv_comp_eq, ← assoc, hezero]
  exact key
  intro i hi
  have hi' : i < t.length := by omega
  have hsq : CommSq (e (i + 1) hi').inv (t'.transitionMapSucc i) (t.transitionMapSucc i) (e i hi'.le).inv := by
    refine ⟨?_⟩
    rw [inv_comp_eq, ← assoc, hestep i hi', assoc, hom_inv_id,
      comp_id]
  exact (of_horiz_isIso hsq).paste_horiz $ hpb i hi'
  intro i hi
  have hi' : i < t.length := by omega
  have key : t'.center i = (s.center i).comap (isoI (e i hi'.le) ≫ σ i hi'.le) := by
    rw [comap_comp, ← hcen i hi', ← hecen i hi',
      ← comap_comp, inv_hom_id, comap_id]
  exact key

section
variable {t : SequenceOfBlowups X'}
section
variable {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s)
include h
theorem center_eq_top (i : ℕ) (hi : i < s.length)
    (hs : s.center i = ⊤) : t.center i = ⊤ := by
  obtain ⟨hlen, σ, -, -, hcen⟩ := h
  have hi' : i < t.length := by omega
  rw [hcen i hi', hs, comap_top]

theorem center_ne_top_of_forall_center_ne_top
    (ht : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) :
    ∀ i, i < s.length → s.center i ≠ ⊤ := by
  obtain ⟨hlen, _, _, _, hcen⟩ := h
  intro i hi htop
  have hi' : i < t.length := by omega
  refine ht i hi' ?_
  rw [hcen i hi', htop]
  simp
end

theorem of_isomorphic_base {s s' : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (he : s.Isomorphic s') :
    IsStrictPullbackBlowupSeq g t s' := by
  obtain ⟨hl1, σ, hz1, hp1, hc1⟩ := h
  obtain ⟨hl2, e, hz2, hp2, hc2⟩ := he
  have hle : ∀ i, i ≤ t.length → i ≤ s.length := fun i hi => by omega
  have hlt : ∀ i, i < t.length → i < s.length := fun i hi => by omega
  refine ⟨tr_ hl1 hl2, fun i hi => σ i hi ≫ isoH (e i $ hle i hi), ?_, ?_, ?_⟩
  rwa [assoc, hz2]
  intro i hi
  exact (hp1 i hi).paste_horiz $ of_horiz_isIso ⟨hp2 i $ hlt i hi⟩
  intro i hi
  rw [hc1 i hi, ← hc2 i $ hlt i hi]
  simp [comap_comp]
end
end

section
variable {X} (s : SequenceOfBlowups X)
private theorem projectionToBase_zero :
    s.projectionToBase 0 = s.isoZero.hom := by
  rw [SequenceOfBlowups.projectionToBase_def, transitionMap_self s $ le_refl 0, id_comp]

theorem blowupMorphism_comp_projectionToBase (i : ℕ) :
    s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) := by
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]
end

theorem idealSheafData_eq_top_of_comap_eq_top {Y Z : Sch} (f : Y ⟶ Z)
    [Surjective f] (I : ISD Z)
    (h : I.comap f = ⊤) : I = ⊤ := by
  refine mp_ (support_eq_bot_iff I) ?_
  have hsup := m19 I f
  rw [h, support_top] at hsup
  refine TopologicalSpace.Closeds.coe_eq_empty.mp $ eq_empty_of_forall_notMem ?_
  intro z hz
  obtain ⟨y, hy⟩ := f.surjective z
  rw [← hy] at hz
  have h2 : y ∈ (⊥ : m182 Y) := by
    rwa [hsup]
  exact h2

section
variable {X' X : Sch} {g : X' ⟶ X}
theorem isomorphic
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (h' : IsStrictPullbackBlowupSeq g t' s) :
    t.Isomorphic t' := by
  obtain ⟨hl, σ, hz, hp, hc⟩ := h
  obtain ⟨hl', ta_, hz', hp', hc'⟩ := h'
  have hlen := le_of_eq $ tr_ hl hl'.symm
  have hA :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length σ hz hp
  have hB :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t' s t'.length ta_ hz' hp'
  have key : ∀ i, ∀ hi : i ≤ t.length, ∃ e : t.schemeAt i ≅ t'.schemeAt i,
      e.hom ≫ ta_ i (hi.trans hlen) = σ i hi ∧ e.hom ≫ t'.projectionToBase i = t.projectionToBase i :=
    fun i hi =>
      ⟨(hA i hi).isoIsPullback _ _ $ hB i $ hi.trans hlen,
        (hA i hi).isoIsPullback_hom_fst _ _ $ hB i $ hi.trans hlen,
        (hA i hi).isoIsPullback_hom_snd _ _ $ hB i $ hi.trans hlen⟩
  choose e he1 he2 using key
  refine ⟨tr_ hl hl'.symm, e, ?_, ?_, ?_⟩
  have h0 := he2 0 $ zero_le t.length
  rwa [projectionToBase_zero t', projectionToBase_zero t] at h0
  intro i hi
  refine (hB i $ hi.le.trans hlen).hom_ext ?_ ?_
  have w1 :=
    (hp' i $ lt_of_lt_of_le hi hlen).w
  rw [assoc, assoc, ← w1, he1 i hi.le, ← assoc,
    he1 (i + 1) hi]
  exact (hp i hi).w
  rw [assoc, assoc, blowupMorphism_comp_projectionToBase t' i,
    he2 (i + 1) hi, he2 i hi.le, blowupMorphism_comp_projectionToBase t i]
  intro i hi
  rw [hc' i $ lt_of_lt_of_le hi hlen, hc i hi, ← he1 i hi.le]
  simp [comap_comp]

theorem center_eq_top_iff
    [Surjective g]
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i < s.length) :
    t.center i = ⊤ ↔ s.center i = ⊤ := by
  refine ⟨?_, fun hs => center_eq_top h i hi hs⟩
  intro ht
  obtain ⟨hlen, σ, hzero, hpb, hcen⟩ := h
  have hi' : i < t.length := by omega
  have hsurj :=
    surjective_of_isPullback_blowupMorphism g t s t.length σ hzero hpb i hi'.le
  have hc := hcen i hi'
  rw [ht] at hc
  exact idealSheafData_eq_top_of_comap_eq_top (σ i hi'.le) (s.center i) hc.symm
end

theorem comp {X'' X' X : Sch} {ps_ : X'' ⟶ X'} {ph_ : X' ⟶ X}
    {u : SequenceOfBlowups X''} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (hu : IsStrictPullbackBlowupSeq ps_ u t) (ht : IsStrictPullbackBlowupSeq ph_ t s) :
    IsStrictPullbackBlowupSeq (ps_ ≫ ph_) u s := by
  obtain ⟨hl1, σ, hz1, hp1, hc1⟩ := hu
  obtain ⟨hl2, ta_, hz2, hp2, hc2⟩ := ht
  have hle : ∀ i, i ≤ u.length → i ≤ t.length := fun i hi => by omega
  have hlt : ∀ i, i < u.length → i < t.length := fun i hi => by omega
  refine ⟨tr_ hl1 hl2, fun i hi => σ i hi ≫ ta_ i (hle i hi), ?_, ?_, ?_⟩
  rw [assoc, hz2, ← assoc, hz1, assoc]
  intro i hi
  exact (hp1 i hi).paste_horiz $ hp2 i $ hlt i hi
  intro i hi
  rw [hc1 i hi, hc2 i $ hlt i hi]
  simp [comap_comp]

end IsStrictPullbackBlowupSeq


private theorem mem_support_comap {A B : Sch} (f : A ⟶ B) (I : ISD B)
    (x : ↥A) : x ∈ support (I.comap f) ↔ f.base x ∈ support I := by
  rw [m19]
  exact m22

namespace IsPullbackBlowupSequence

theorem comp_isStrictPullbackSequenceOfBlowups {W V Y : Sch} {u : V ⟶ Y} {c : W ⟶ V}
    [Surjective c]
    {s : SequenceOfBlowups Y} {s' : SequenceOfBlowups V} {t : SequenceOfBlowups W}
    (h : IsPullbackBlowupSequence u s' s) (hc : IsStrictPullbackBlowupSeq c t s') :
    IsPullbackBlowupSequence (c ≫ u) t s := by
  unfold FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence at h ⊢
  unfold FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq at hc
  obtain ⟨r, e, hr1, hr2, hr3, hr4, hefst, hestep, hecenter⟩ := h
  obtain ⟨hlen, σ, hzero, hstep, hcenter⟩ := hc
  have hle : ∀ i, i ≤ t.length → i ≤ s'.length := by
    intro i hi
    omega
  let _a0 := c ≫ u
  have hpaste : ∀ i (hi : i ≤ t.length),
      IsPullback (t.projectionToBase i)
        (σ i hi ≫ isoH (e i $ hle i hi) ≫ snd u (s.projectionToBase $ r i))
        _a0 $ s.projectionToBase $ r i := by
    intro i hi
    have hcomm : s'.projectionToBase i ≫ u =
        (isoH (e i $ hle i hi) ≫ snd u (s.projectionToBase $ r i)) ≫
          s.projectionToBase (r i) := by
      rw [← hefst i $ hle i hi, assoc, assoc, condition]
    exact ((isPullback_projectionToBase_of_isPullback_blowupMorphism c t s' t.length σ hzero hstep) i hi).flip.paste_vert
      (of_iso_pullback ⟨hcomm⟩ (e i $ hle i hi) (hefst i $ hle i hi) rfl)
  have hFfst :=
    fun i hi => (hpaste i hi).isoPullback_hom_fst
  have hFsnd :=
    fun i hi => (hpaste i hi).isoPullback_hom_snd
  have hFsnd' : ∀ i (hi : i ≤ t.length) {Z : Sch} (k : s.schemeAt (r i) ⟶ Z),
      ((hpaste i hi).isoPullback).hom ≫
          snd _a0 (s.projectionToBase $ r i) ≫ k =
        σ i hi ≫ isoH (e i $ hle i hi) ≫
          snd u (s.projectionToBase $ r i) ≫ k := by simp_all
  have hc1 : ∀ i < t.length, r i < s.length := by simp_all
  have hc2 : ∀ i j, j ≤ t.length → i < j → r i < r j := by simp_all
  have hc3 := hr3
  rw [← hlen] at hc3
  have hc4 : ∀ i < s.length,
      (∃ x, x ∈ spI (cmI (s.center i)
        (snd _a0 $ s.projectionToBase i))) ↔
        ∃ j < t.length, r j = i := by
    intro i hi
    have _i30 : (∃ x, x ∈ spI (cmI (s.center i) $ snd (c ≫ u) $ s.projectionToBase i)) ↔ (∃ x, x ∈ spI (cmI (s.center i) $ snd u $ s.projectionToBase i)) := by
      let g := s.projectionToBase i
      let _a2 := c ≫ u
      let _a0 := snd _a2 g
      let _a1 := fst _a2 g
      obtain ⟨q, hq1, hq2⟩ :
          ∃ q,
            q ≫ fst u g = _a1 ≫ c ∧
              q ≫ snd u g = _a0 :=
        ⟨m107 (_a1 ≫ c)
            _a0
            (by rw [assoc]; exact condition),
          lift_fst _ _ _, lift_snd _ _ _⟩
      have hA := by
        refine of_bot ?_ hq1.symm $ of_hasPullback u g
        rw [hq2]
        exact of_hasPullback _a2 g
      have hqs : Surjective q := by
        rw [← hA.isoPullback_hom_snd]
        infer_instance
      have hbase : ∀ x : ↥(m131 _a2 g),
          _a0.base x =
            (snd u g).base (bsM q x) := by
        intro x
        rw [← hq2]
        simp
      constructor
      rintro ⟨x, hx⟩
      rw [mem_support_comap] at hx
      refine ⟨bsM q x, ?_⟩
      rwa [mem_support_comap, ← hbase x]
      rintro ⟨y, hy⟩
      rw [mem_support_comap] at hy
      obtain ⟨x, hx⟩ := hqs.surj y
      refine ⟨x, ?_⟩
      rwa [mem_support_comap, hbase x, hx]
    refine _i30.trans ?_
    refine (hr4 i hi).trans ?_
    constructor
    simp_all
    simp_all
  have hc6 : ∀ i (hi : i < t.length) (hrr : r i ≤ r (i + 1)),
      t.transitionMapSucc i ≫ isoH ((hpaste i $ m49 hi).isoPullback) =
        ((hpaste (i + 1) hi).isoPullback).hom ≫ s.pullbackTransitionMap _a0 hrr := by
    intro i hi hrr
    apply hom_ext
    simp [assoc, SequenceOfBlowups.pullbackTransitionMap_fst, hFfst]
    rw [t.blowupMorphism_eq_transitionMap]
    exact t.transitionMap_comp_projectionToBase _
    simp [assoc, SequenceOfBlowups.pullbackTransitionMap_snd, hFsnd, hFsnd']
    rw [← assoc, ← (hstep i hi).w, assoc,
      ← assoc $ s'.transitionMapSucc i, hestep i (by omega) hrr, assoc,
      SequenceOfBlowups.pullbackTransitionMap_snd]
  have hc7 : ∀ i (hi : i < t.length),
      t.center i = cmI (s.center $ r i)
        (isoH ((hpaste i $ m49 hi).isoPullback) ≫
          snd _a0 (s.projectionToBase $ r i)) := by simp_all
  exact ⟨r, fun i hi => (hpaste i hi).isoPullback, hc1, hc2, hc3, hc4, hFfst, hc6, hc7⟩

end IsPullbackBlowupSequence

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.Blowup

def StrictTransformIsBlowupOfClosedSubscheme : Prop :=
  ∀ (X X1 S : Sch) [IsLocallyNoetherian X]
    (j : S ⟶ X) [IsClosedImmersion j] (pi_ : X1 ⟶ X)
    (Z : ISD X), IsBlowupAlongIdealSheaf pi_ Z →
    (∀ T ∈ irreducibleComponents (↥S), ¬ (j.base '' T) ⊆ (support Z : Set ↥X)) →
    ∃ ps_ : subscheme (strictTransform pi_ Z j.ker) ⟶ S,
      ps_ ≫ j = subschemeι (strictTransform pi_ Z j.ker) ≫ pi_ ∧
        IsBlowupAlongIdealSheaf ps_ (Z.comap j)

def BlowupIsProper : Prop :=
  ∀ (X X' : Sch) [IsLocallyNoetherian X] (pi_ : X' ⟶ X)
    (Z : ISD X), IsBlowupAlongIdealSheaf pi_ Z → IsProper pi_

def BlowupIsIsoOffCenter : Prop :=
  ∀ (X X' : Sch) (pi_ : X' ⟶ X) (Z : ISD X),
    IsBlowupAlongIdealSheaf pi_ Z →
      IsIso (morphismRestrict pi_ Z.support.compl)

end FunctorialResolution.Blowup
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

def StrictNormalCrossingsRestrictToClopen : Prop :=
  ∀ (k : Type) [Field k] (W : Sch) (p : W ⟶ Sp k)
    [Smooth p] (E : Bdy W) (Z : ISD W),
    InStrictNormalCrossingPosition p E → HasStrictNormalCrossingsWith p Z E →
    ∀ U : (subscheme Z).Opens, IsClosed (U : CSet $ subscheme Z) →
    (∀ D ∈ E, ∀ T ∈ irreducibleComponents (↥(toScheme U)),
        ¬ ((ι U ≫ subschemeι Z).base '' T) ⊆ (support D : Set ↥W)) →
    IsStrictNormalCrossingsDivisor ((E.prod.comap $ ι U ≫ subschemeι Z).radical)

end FunctorialResolution.EmbeddedResolution
end
section
namespace AlgebraicGeometry.Scheme

section
variable {X : Sch}
theorem exists_isAffineOpen_mem (x : X) :
    ∃ U : Opn X, x ∈ U ∧ IsAffineOpen U := by
  obtain ⟨U, hU, hxU, -⟩ :=
    mp isBasis_iff_nbhd (isBasis_affineOpens X)
      (show x ∈ (⊤) from trivial)
  exact ⟨U, hxU, hU⟩

theorem exists_affineOpens_mem (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  have hx : x ∈ (⨆ U : affO X, (U : Opn X)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := mp_ mem_iSup hx
  exact ⟨U, hU⟩

theorem exists_affineOpens_mem_le {x} {U : Opn X} (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U := by
  obtain ⟨V, hV, hxV, hsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  obtain ⟨W, hW, rfl⟩ := hV
  exact ⟨⟨W, hW⟩, hxV, hsub⟩
end

end AlgebraicGeometry.Scheme
end
section
open Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Sch}

section
variable (I : ISD Y)
theorem notMem_support_of_comap_ι_eq_top {U : Opn Y}
    (h : I.comap U.i = ⊤) {x} (hxU : x ∈ U) : x ∉ support I := by
  intro hx
  let _a0 := (⟨x, hxU⟩ : ↥U)
  have h1 : _a0 ∈ support (I.comap U.i) := by
    rwa [m19]
  rw [h, support_top] at h1
  have h2 : _a0 ∈ ((⊥) : Set ↥U) := h1
  simp at h2
end

private theorem appLE_top_eq_appTop (f : X ⟶ Y) e0 :
    appLE f (⊤ : Opn Y) (⊤ : Opn X) e0 = appTop f := by
  let _a0 := pMap X (homOfLE e0).op
  have h1 : _a0 = 𝟙 Γ(X, ⊤) := X.presheaf.map_id $ op (⊤)
  calc f.appLE (⊤) (⊤) e0
      = f.app (⊤) ≫ _a0 := rfl
    _ = f.app (⊤) ≫ 𝟙 Γ(X, ⊤) := by rw [h1]
    _ = hAT f := comp_id _

theorem comap_ι_comp_eq_of_comap_ι_eq f (V : Opn Y) (U : Opn X)
    (hle : U ≤ pre f V) (I J : ISD Y)
    (h : I.comap V.i = J.comap V.i) : I.comap (ι U ≫ f) = J.comap (ι U ≫ f) := by
  have hfac : X.homOfLE hle ≫ ((mrU f V) ≫ opI V) = opI U ≫ f := by simp_all
  have e : ∀ K : ISD Y,
      ((K.comap V.i).comap $ f.mr V).comap (X.homOfLE hle) = K.comap (ι U ≫ f) := by
    intro K
    rw [← comap_comp,
      ← comap_comp, assoc, hfac]
  rw [← e I, ← e J, h]

section
variable {X : Sch}
theorem eq_top_iff_support_eq_empty (I : ISD X) :
    I = ⊤ ↔ (support I : Set X) = ∅ := by
  rw [← support_eq_bot_iff, ext'_iff]
  simp

theorem support_nonempty_iff_ne_top (I : ISD X) :
    (support I : Set X).Nonempty ↔ I ≠ ⊤ := by
  rw [ne_eq, eq_top_iff_support_eq_empty, nonempty_iff_ne_empty, ne_eq]

private theorem mem_basicOpen_iff_notMem_primeIdealOf {U}
    (hU : IsAffineOpen U) {x} (hx : x ∈ U) g :
    x ∈ X.basicOpen g ↔ g ∉ asIdeal (hU.primeIdealOf ⟨x, hx⟩) := by
  let _a0 := hU.primeIdealOf ⟨x, hx⟩
  have h1 : hU.fromSpec.base _a0 = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : hU.fromSpec.pre (bOpn X g) = PrimeSpectrum.basicOpen g :=
    hU.fromSpec_preimage_basicOpen g
  constructor
  intro h
  rw [← h1] at h
  have h3 : _a0 ∈ hU.fromSpec.pre (bOpn X g) := h
  rw [h2] at h3
  exact mp_ (m209 g _) h3
  intro h
  have h3 : _a0 ∈ PrimeSpectrum.basicOpen g :=
    mpr (m209 g _) h
  rw [← h2] at h3
  have h4 : hU.fromSpec.base _a0 ∈ bOpn X g := h3
  rwa [h1] at h4

theorem mem_support_iff_ideal_le_primeIdealOf (I : ISD X)
    {U : Opn X} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    x ∈ support I ↔ I.ideal ⟨U, hU⟩ ≤ asIdeal (hU.primeIdealOf ⟨x, hx⟩) := by
  rw [mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hx,
    mem_zeroLocus_iff]
  constructor
  intro h
  rw [SetLike.le_def]
  intro f hf
  have hb := h f hf
  rw [mem_basicOpen_iff_notMem_primeIdealOf hU hx f] at hb
  exact mp_ not_not hb
  intro h f hf
  rw [mem_basicOpen_iff_notMem_primeIdealOf hU hx f]
  exact mpr_ not_not $ h hf
end

private theorem appLE_congr_hom {Z W : Sch} {g1_ g2_ : Z ⟶ W} (h : g1_ = g2_)
    (U : Opn W) (V : Opn Z) (e1_ : V ≤ g1_ ⁻¹ᵁ U) :
    appLE g1_ U V e1_ = appLE g2_ U V (h ▸ e1_) := by
  subst h
  rfl

section
variable (I : ISD Y) (f : X ⟶ Y) (U : Y.affineOpens) (V : X.affineOpens) (e : (V : Opn X) ≤ pre f (U : Opn Y))
theorem ker_pullbackFst_le_map_appLE :
    RingHom.ker ((Limits.pullback.fst f I.subschemeι).app (V : Opn X)).hom ≤
      Ideal.map (appLE f (U : Opn Y) (V : Opn X) e).hom (I.ideal U) := by
  let _a3 := appLE f U V e
  obtain ⟨C, q, hq⟩ : ∃ (C : CRC) (q : X.sec V ⟶ C),
      RingHom.ker q.hom = Ideal.map _a3.hom (I.ideal U) :=
    ⟨_, CommRingCat.ofHom $ Ideal.Quotient.mk
        (Ideal.map _a3.hom $ I.ideal U), mk_ker⟩
  obtain ⟨ps_, hps_⟩ : ∃ ps_ : Γ(subS I, siI I ⁻¹ᵁ U) ⟶ C, I.subschemeι.app U ≫ ps_ = _a3 ≫ q := by
    let hq := le_of_eq hq.symm
    refine ⟨isoH (I.subschemeObjIso U) ≫ ofHom
        (Ideal.Quotient.lift (I.ideal U)
          (q.hom.comp _a3.hom) ?_), ?_⟩
    intro a ha
    have h := hq $ mem_map_of_mem _ ha
    rwa [mem_ker] at h
    rw [subschemeι_app, assoc, inv_hom_id_assoc]
    ext a
    rfl
  obtain ⟨th_, hth⟩ : ∃ th_ : Γ(Limits.pullback f I.subschemeι, fst f I.subschemeι ⁻¹ᵁ V) ⟶ C, (fst f I.subschemeι).app V ≫ th_ = q := by
    have hV := V.2
    have hU := U.2
    have hio := SpecMap_appLE_fromSpec I.si hU
        (hU.preimage I.si) $ le_refl $ siI I ⁻¹ᵁ U
    have hsq : (Spec.map q ≫ hV.fromSpec) ≫ f
        = (Spec.map ps_ ≫ (hU.preimage I.si).fromSpec) ≫ siI I := by
      rw [Category.assoc, Category.assoc, ← SpecMap_appLE_fromSpec f hU hV e, ← hio, ← Category.assoc, ← Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp, Scheme.Hom.appLE_eq_app, hps_]
    obtain ⟨g, hlift⟩ : ∃ g,
        g ≫ fst f I.si = Spec.map q ≫ hV.fromSpec :=
      ⟨Limits.pullback.lift _ _ hsq, lift_fst _ _ _⟩
    have hpre : (⊤)
        ≤ g ⁻¹ᵁ (fst f I.si ⁻¹ᵁ V) := by
      have h4 := by simpa using (congrArg (preU · V) hlift)
      rw [h4, hV.fromSpec_preimage_self]
      simp
    have e1_ :=
      le_of_eq (hV.fromSpec_preimage_self).symm
    let _a2 := X.sec V
    let _a0 := Spec _a2
    have e2_ : (⊤)
        ≤ Spec.map q ⁻¹ᵁ (⊤) := by simp
    have hsplit := appLE_comp_appLE (Spec.map q) hV.fromSpec V
        (⊤) (⊤) e1_ e2_
    have h0 : ∀ i : (op (⊤))
        ⟶ op (⊤),
        _a0.presheaf.map i = 𝟙 _ := by
      intro i
      have hi : i = 𝟙 _ := rfl
      rw [hi, CategoryTheory.Functor.map_id]
    have hdef : hV.fromSpec.appLE V (⊤) e1_
        = hV.fromSpec.app V
          ≫ pMap _a0 (homOfLE e1_).op := rfl
    have ha : hV.fromSpec.appLE V (⊤) e1_
        = isoI (GSpecIso _a2) := by
      rw [hdef, hV.fromSpec_app_self, assoc, ← Functor.map_comp, ← op_comp,
        h0, comp_id]
    have hb : appTop (Spec.map q)
        = isoH (GSpecIso _a2) ≫ q ≫ isoI (GSpecIso C) := by
      rw [Scheme.ΓSpecIso_inv_naturality, hom_inv_id_assoc]
    refine ⟨appLE g (fst f I.si ⁻¹ᵁ V)
        (⊤) hpre ≫ isoH (GSpecIso C), ?_⟩
    rw [← assoc, ← appLE_eq_app $ fst f I.si,
      appLE_comp_appLE, appLE_congr_hom hlift, ← hsplit, ha, appLE_top_eq_appTop, hb]
    simp
  rw [← hq]
  intro x hx
  rw [mem_ker] at hx ⊢
  rw [← hth, CommRingCat.hom_comp, comp_apply, hx, map_zero]

theorem comap_ideal_eq_map_appLE :
    (I.comap f).ideal V = (I.ideal U).map (appLE f (U : Opn Y) (V : Opn X) e).hom := by
  let _a2 := fst f I.si
  have _i31 : (cmI I f).ideal V = m41 (_a2.app V).hom := by
    have hc : cmI I f = ker _a2 := rfl
    rw [hc, ← map_bot, ideal_map_of_isAffineHom,
      ideal_bot]
    exact (ker_eq_comap_bot _).symm
  rw [_i31]
  refine le_antisymm (ker_pullbackFst_le_map_appLE I f U V e)
    ?_
  let _a0 := _a2
  let _a1 := snd f I.si
  have hcond : _a0 ≫ f
      = _a1 ≫ siI I := condition
  have h2 : preU _a0 (pre f U)
      = preU _a1 (preU I.si U) := by
    have h3 := congrArg
      (fun g : (m131 f I.si) ⟶ Y => preU g U) hcond
    simpa using h3
  have hle : preU _a0 V
      ≤ preU _a1 (preU I.si U) := by
    rw [← h2]
    intro x hx
    exact e hx
  have happ : appLE f U V e
        ≫ _a0.app V
      = I.subschemeι.app U
        ≫ appLE _a1 (siPre I U)
            (preU _a0 V) hle := by
    rw [← appLE_eq_app _a0,
      ← appLE_eq_app I.si, appLE_comp_appLE,
      appLE_comp_appLE, appLE_congr_hom hcond]
  rw [map_le_iff_le_comap]
  intro a ha
  have hker : (I.subschemeι.app U).hom a = 0 := by
    rwa [← mem_ker, I.ker_subschemeι_app U]
  simp [mem_comap, mem_ker]
  rw [← comp_apply, ← hom_comp, happ, hom_comp,
    comp_apply, hker, map_zero]

theorem comap_ideal_eq_span_image (s : Set (Y.sec (U : Opn Y)))
    (hs : I.ideal U = span s) :
    (I.comap f).ideal V
      = span ((appLE f (U : Opn Y) (V : Opn X) e).hom '' s) := by
  rw [comap_ideal_eq_map_appLE I f U V e, hs, map_span]

theorem map_appLE_le_comap_ideal :
    (I.ideal U).map (appLE f (U : Opn Y) (V : Opn X) e).hom ≤ (I.comap f).ideal V :=
  ge_of_eq $ comap_ideal_eq_map_appLE I f U V e

theorem appLE_mem_comap_ideal {x : (Y.sec (U : Opn Y))}
    (hx : x ∈ I.ideal U) :
    (appLE f (U : Opn Y) (V : Opn X) e).hom x ∈ (I.comap f).ideal V :=
  map_appLE_le_comap_ideal I f U V e $ mem_map_of_mem _ hx
end

theorem comap_ideal_top_eq_map_appTop [IsAffine X] [IsAffine Y]
    (I : ISD Y) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  have e0 : (⊤) ≤ preU f (⊤) := by simp
  rw [comap_ideal_eq_map_appLE I f ⟨⊤, isAffineOpen_top Y⟩ ⟨⊤, isAffineOpen_top X⟩ e0]
  exact congrArg
    (fun ph_ => m6 (hom ph_) $ I.ideal ⟨⊤, isAffineOpen_top Y⟩)
    (appLE_top_eq_appTop f e0)

theorem ofIdealTop_mul [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    ofIdealTop (I * J) = ofIdealTop I * ofIdealTop J := by
  ext U : 2
  exact m220 _ _ _

theorem comap_mul (I J : ISD Y) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine ext_of_iSup_eq_top
    (fun W : {W : affO X // ∃ U : affO Y, W ≤ pre f U} =>
      W.1) ?_ ?_
  refine m55 ?_
  simp only [coe_iSup, coe_top,
    eq_univ_iff_forall, mem_iUnion]
  intro x
  obtain ⟨W, hxW⟩ := Scheme.exists_affineOpens_mem $ bsM f x
  obtain ⟨V, hxV, hVW⟩ :
      ∃ V : affO X, x ∈ (V : Opn X) ∧ (V : Opn X) ≤ preU f (W : Opn Y) :=
    Scheme.exists_affineOpens_mem_le hxW
  exact ⟨⟨V, W, hVW⟩, hxV⟩
  rintro ⟨V, W, hVW⟩
  rw [comap_ideal_eq_map_appLE (I * J) f W V hVW]
  simp only [ideal_mul, Pi.mul_apply]
  rw [m220, comap_ideal_eq_map_appLE I f W V hVW,
    comap_ideal_eq_map_appLE J f W V hVW]

section
variable {X Y : Sch} (f : X ⟶ Y)
theorem comap_iSup {ι : Sort*} (I : ι → ISD Y) :
    (⨆ i, I i).comap f = ⨆ i, (I i).comap f :=
  (map_gc f).l_iSup

theorem comap_finset_prod {ι : Type} (s : Finset ι)
    (F : ι → ISD Y) :
    (∏ i ∈ s, F i).comap f = ∏ i ∈ s, (F i).comap f := by
  classical
  refine Finset.induction_on s ?_ ?_
  simp only [prod_empty]
  exact comap_top f
  intro a t ha ih
  simp only [prod_insert ha, comap_mul, ih]

theorem comap_listProd (L : Bdy Y) :
    L.prod.comap f = (L.map (·.comap f)).prod := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    exact comap_top f
  | cons D E ih => simp only [m75, List.prod_cons, comap_mul, ih]
end

theorem ofIdealTop_ideal_top {Z : Sch} [IsAffine Z] (J : Ideal Γ(Z, ⊤)) :
    (ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J := by
  have h := (equivOfIsAffine (X := Z)).apply_symm_apply J
  rwa [equivOfIsAffine_symm_apply, equivOfIsAffine_apply] at h

theorem isReduced_of_ringEquiv {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : _root_.IsReduced B) : _root_.IsReduced A := by
  exact ⟨fun a ha => e.injective $ by simpa using (ha.map e).eq_zero⟩

theorem isReduced_stalk_of_radical (I : ISD X)
    (hrad : ∀ U : X.affineOpens, (I.ideal U).IsRadical) (y : ↥I.subscheme) :
    _root_.IsReduced $ I.subscheme.presheaf.stalk y := by
  obtain ⟨U, hU⟩ := Scheme.exists_affineOpens_mem $ I.subschemeι.base y
  have hy := hU
  let _s0 := siPre I U
  have hTop := isReduced_of_ringEquiv (Scheme.Opens.topIso
    _s0).commRingCatIsoToRingEquiv $ isReduced_of_ringEquiv (I.subschemeObjIso U).commRingCatIsoToRingEquiv $ mp_ (isRadical_iff_quotient_reduced $ I.ideal U) $ hrad U
  let _m0 := _s0
  have : IsAffine _m0 := IsAffineOpen.preimage (U.2) I.si
  have : IsReduced _m0 :=
    isReduced_of_isAffine_isReduced _
  exact isReduced_of_ringEquiv
    (Scheme.Opens.stalkIso _s0
      (⟨y, hy⟩ : _s0)).symm.commRingCatIsoToRingEquiv $ isReduced_stalk_of_isReduced _m0 (⟨y, hy⟩ : _s0)

theorem comap_ofIdealTop [IsAffine X] [IsAffine Y] (J : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (ofIdealTop J).comap f = ofIdealTop (J.map f.appTop.hom) := by
  have h : (cmI (ofIdealTop J) f).ideal ⟨⊤, isAffineOpen_top X⟩
      = (ofIdealTop $ J.map f.appTop.hom).ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [comap_ideal_top_eq_map_appTop, ofIdealTop_ideal_top, ofIdealTop_ideal_top]
  exact (equivOfIsAffine (X := X)).injective h

theorem comap_ι_eq_top_iff_ideal_eq_top {Y : Sch} (I : ISD Y) {V : Opn Y}
    (hV : IsAffineOpen V) : I.comap V.i = ⊤ ↔ I.ideal ⟨V, hV⟩ = ⊤ := by
  have hVaff : IsAffine V.toScheme := hV
  have htop : ∀ U, (⊤ : V.toScheme.IdealSheafData).ideal U = ⊤ := by
    intro U
    simp
  have e : (⊤) ≤ opPre V V := by simp
  have himg : V.i.im (⊤) = V := by simp
  have hiso : ∀ U, U = V.i.im (⊤) →
      ∀ e' : (⊤) ≤ opPre V U,
        IsIso $ V.ι.appLE U (⊤) e' := by
    rintro U rfl e'
    rw [← appIso_hom' V.i (⊤)]
    infer_instance
  obtain ⟨ph_, hph, hmap⟩ : ∃ ph_ : Y.sec V ⟶ Γ(toScheme V, ⊤), IsIso ph_ ∧
      (I.comap V.i).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
        = (I.ideal ⟨V, hV⟩).map ph_.hom :=
    ⟨V.ι.appLE V (⊤) e, hiso V himg.symm e,
      comap_ideal_eq_map_appLE I V.i ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ e⟩
  constructor
  intro h
  rw [h, htop] at hmap
  have h3 : ((I.ideal ⟨V, hV⟩).map ph_.hom).map (m83 ph_).hom
      = I.ideal ⟨V, hV⟩ := by
    rw [map_map, ← m225, m118, CommRingCat.hom_id, m167]
  rw [← hmap, m166] at h3
  exact sy_ h3
  intro h
  have h2 : (I.comap V.i).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
      = (⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩ := by
    rw [hmap, h, m166, htop]
  exact (equivOfIsAffine (X := toScheme V)).injective h2

theorem comap_pow (I : ISD Y) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, comap_mul, ih]

theorem mem_support_comap {f : X ⟶ Y} {I : ISD Y} {x : X} :
    x ∈ support (I.comap f) ↔ f.base x ∈ support I := by
  constructor
  intro hx
  rwa [m19] at hx
  intro hx
  rwa [m19]

theorem ne_top_of_mem_support (J : ISD Y) (x : ↥Y) (hx : x ∈ support J) : J ≠ ⊤ := by
  intro hc
  have hx2 : x ∈ (support J : Set Y) := hx
  rw [mpr_ (support_eq_bot_iff J) hc] at hx2
  simp at hx2

theorem isReduced_subscheme_vanishingIdeal
    (W : Sch) (Z : Closeds W) :
    IsReduced (vanishingIdeal Z).subscheme := by
  have : ∀ y : (subS $ vanishingIdeal Z),
      _root_.IsReduced
        ((vanishingIdeal Z).subscheme.presheaf.stalk y) := by
    intro y
    refine isReduced_stalk_of_radical _ ?_ y
    intro U
    rw [vanishingIdeal_ideal]
    exact isRadical_vanishingIdeal _
  exact isReduced_of_isReduced_stalk _


end AlgebraicGeometry.Scheme.IdealSheafData

namespace FunctorialResolution.Blowup

theorem noetherianSpace_subscheme {X : Sch} (I : ISD X)
    [NoetherianSpace ↥X] :
    NoetherianSpace ↥I.subscheme :=
  (isClosedEmbedding
    I.si).toIsEmbedding.toIsInducing.noetherianSpace

instance instNoetherianSpaceSubscheme {X : Sch} (I : ISD X)
    [NoetherianSpace ↥X] :
    NoetherianSpace ↥I.subscheme :=
  noetherianSpace_subscheme I

theorem idealSheafData_prod_nil (X : Sch) :
    ([] : Bdy X).prod = ⊤ :=by simp_all
theorem idealSheafData_prod_cons (X : Sch) (D : ISD X)
    (E : Bdy X) : (D :: E).prod = D * E.prod :=
  List.prod_cons

theorem comap_ker_comp_of_isOpenImmersion {A B C : Sch} (j : A ⟶ B) (f : B ⟶ C)
    [IsOpenImmersion f] [QuasiCompact j] [QuasiCompact $ j ≫ f] :
    (j ≫ f).ker.comap f = j.ker := by
  refine m29 ?_
  funext V
  have e := (f.preimage_image_eq V.1).ge
  have hopeq : preU j V.1 = preU (j ≫ f) (imU f V.1) := by simp_all
  have hop := hopeq.le
  let _a0 := pMap A (homOfLE hop).op
  let _a2 := (j ≫ f).app $ imU f V.1
  have key : appLE f (imU f V.1) V.1 e ≫ j.app V.1
      = _a2 ≫ _a0 := by
    rw [app_eq_appLE j]
    exact appLE_comp_appLE j f (imU f V.1) V.1 (preU j V.1) e le_rfl
  let _a1 := hom $ appLE f (imU f V.1) V.1 e
  have keyr : ∀ x, (hom $ j.app V.1)
        (_a1 x)
      = hom _a0
        ((hom _a2) x) := by
    intro x
    simpa only [hom_comp, comp_apply] using (congrArg (fun m => (hom m) x) key)
  have hrh_ : ∀ y, (hom _a0) y = 0 → y = 0 := by
    intro y hy
    have hcomp : _a0 ≫ pMap A (homOfLE hopeq.ge).op
        = 𝟙 (pObj A $ m112 $ preU (j ≫ f) $ imU f V.1) := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp,
        elim (homOfLE hopeq.ge ≫ homOfLE hop) $ 𝟙 _, op_id,
        CategoryTheory.Functor.map_id]
    have h2 := congrArg (fun m => (hom m) y) hcomp
    simp only [hom_comp, comp_apply, hom_id, id_apply,
      hy, map_zero] at h2
    exact sy_ h2
  have hph : Function.Surjective _a1 := by
    have : IsIso $ appLE f (imU f V.1) V.1 e := by
      rw [← appIso_hom' f V.1]
      infer_instance
    intro y
    refine ⟨(hom $ inv $ appLE f (imU f V.1) V.1 e) y, ?_⟩
    have h3 := congrArg (fun m => (hom m) y)
      (m117 $ appLE f (imU f V.1) V.1 e)
    simpa only [hom_comp, comp_apply, hom_id,
      id_apply] using h3
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ f ⟨imU f V.1, V.2.image_of_isOpenImmersion f⟩ V e,
    ker_apply, ker_apply]
  dsimp only
  refine le_antisymm ?_ ?_
  rw [map_le_iff_le_comap]
  intro x hx
  rw [mem_comap, mem_ker, keyr x]
  rw [mem_ker] at hx
  rw [hx, map_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := hph y
  apply mem_map_of_mem
  rw [mem_ker] at hy ⊢
  exact hrh_ _ $ st_ (keyr x) hy

end FunctorialResolution.Blowup

namespace AlgebraicGeometry.Scheme.IdealSheafData

theorem exists_iso_subscheme_comap_of_isIso {Y Y' : Sch} (g : Y ⟶ Y') [IsIso g]
    (I : ISD Y') :
    ∃ m : subscheme (I.comap g) ⟶ subscheme I,
      IsIso m ∧ m ≫ subschemeι I = subschemeι (I.comap g) ≫ g := by
  let _c0 := siI (cmI I g) ≫ g
  have : QuasiCompact (cmI I g).si := inferInstance
  have : QuasiCompact _c0 := inferInstance
  have hq := FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (cmI I g).si g
  rw [q2] at hq
  have e1 : ∀ J : ISD Y', (J.comap g).comap (inv g) = J := by
    intro J
    rw [← comap_comp, m117,
      comap_id]
  have hkk : _c0.ker = I.subschemeι.ker := by
    rw [q2,
      ← e1 $ _c0.ker, hq, e1]
  exact ⟨m64 I.si _c0
      (le_of_eq hkk.symm), IsClosedImmersion.isIso_of_ker_eq _c0 I.si _ (lift_fac _ _ _) hkk, lift_fac _ _ _⟩

end AlgebraicGeometry.Scheme.IdealSheafData
end
section
open CategoryTheory.Limits

namespace FunctorialResolution.Blowup

theorem range_coprod_inr_eq_compl (X Y : Sch) :
    range ⇑(coprod.inr : Y ⟶ X ⨿ Y).base
      = (range ⇑(coprod.inl : X ⟶ X ⨿ Y).base)ᶜ := by
  exact (isCompl_range_inl_inr ..).compl_eq.symm

theorem isClosed_range_coprod_inl (X Y : Sch) :
    IsClosed $ range ⇑(coprod.inl : X ⟶ X ⨿ Y).base := by
  have h := isCompl_range_inl_inr X Y
  have hopen :=
    (coprod.inr : Y ⟶ X ⨿ Y).isOpenEmbedding.isOpen_range
  rwa [← isOpen_compl_iff, h.compl_eq]



instance instIsClosedImmersionCoprodInl (X Y : Sch) :
    IsClosedImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  exact ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding,
    isClosed_range_coprod_inl X Y⟩


theorem isClosedEmbedding_coprod_inl_base (X Y : Sch) :
    Topology.IsClosedEmbedding ⇑(coprod.inl : X ⟶ X ⨿ Y).base :=
  ⟨(coprod.inl : X ⟶ X ⨿ Y).isOpenEmbedding.toIsEmbedding, isClosed_range_coprod_inl X Y⟩

instance instQuasiCompactCoprodInl (X Y : Sch) :
    QuasiCompact (coprod.inl : X ⟶ X ⨿ Y) := by
  constructor
  intro U _ hU
  exact (isClosedEmbedding_coprod_inl_base X Y).isCompact_preimage hU



section

variable {ι : Type} (X : ι → Sch) [HasCoproduct X]

theorem sigmaio_base_ne {i j : ι} (hij : i ≠ j) (x : ↥(X i)) (y : ↥(X j)) :
    (Sigma.ι X i).base x ≠ (Sigma.ι X j).base y := by
  intro h
  exact hij $ congrArg Sigma.fst $ mp_ (sigmaι_eq_iff X i j x y) h

section
variable {ka_ : Type} (Y : ka_ → Sch) [HasCoproduct Y]
def iSupOpensRangeSigmaio : (∐ Y).Opens :=
  ⟨⋃ i, range ⇑(Sigma.ι Y i).base,
    isOpen_iUnion fun i => (Sigma.ι Y i).isOpenEmbedding.isOpen_range⟩

theorem isClosedEmbedding_sigmaio_base (j : ka_) (hc : IsClosed (range ⇑(Sigma.ι Y j).base)) :
    Topology.IsClosedEmbedding ⇑(Sigma.ι Y j).base :=
  ⟨(Sigma.ι Y j).isOpenEmbedding.toIsEmbedding, hc⟩

theorem range_sigmaio_subset_iUnion
    (i : ka_) : range ⇑(Sigma.ι Y i).base ⊆ range ⇑(iSupOpensRangeSigmaio Y).ib := by
  rw [q1]
  intro z hz
  exact Set.mem_iUnion.mpr ⟨i, hz⟩
end

theorem surjective_base_of_comp_eq_id {A B : Sch} (g : A ⟶ B) (h : B ⟶ A)
    (hgh : g ≫ h = 𝟙 A) : Function.Surjective ⇑h.base := by
  intro x
  refine ⟨bsM g x, ?_⟩
  have h1 := congrArg (fun m : A ⟶ A => bsM m x) hgh
  simpa using h1

theorem exists_sigmaio_base_eq {ka_ : Type} (Y : ka_ → Sch) [HasCoproduct Y]
    (x : ↥(∐ Y)) : ∃ (i : ka_) (y : ↥(Y i)), (Sigma.ι Y i).base y = x := by
  have hid : (desc fun i =>
      m43 (iSupOpensRangeSigmaio Y).i (Sigma.ι Y i) $ range_sigmaio_subset_iUnion Y i) ≫
        opI (iSupOpensRangeSigmaio Y) = 𝟙 (∐ Y) := by
    apply Sigma.hom_ext
    intro i
    have hfac := m115 (iSupOpensRangeSigmaio Y).i (Sigma.ι Y i)
      (range_sigmaio_subset_iUnion Y i)
    simp [hfac]
  obtain ⟨w, hw⟩ := surjective_base_of_comp_eq_id _ _ hid x
  have hmem : x ∈ range (iSupOpensRangeSigmaio Y).ib := ⟨w, hw⟩
  rw [q1] at hmem
  have hmem2 := hmem
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hmem2
  exact ⟨i, y, hy⟩

theorem quasiCompact_sigmaio (j : ι) : QuasiCompact $ Sigma.ι X j := by
  constructor
  intro U _ hU
  refine (isClosedEmbedding_sigmaio_base X j ?_).isCompact_preimage hU
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  rw [mem_compl_iff] at hx
  obtain ⟨i, y, rfl⟩ := exists_sigmaio_base_eq X x
  have hij : i ≠ j := by
    intro h
    subst h
    exact hx ⟨y, rfl⟩
  let _a0 := Sigma.ι X i
  refine ⟨range _a0.base, ?_,
    _a0.isOpenEmbedding.isOpen_range, mem_range_self y⟩
  intro u hu
  obtain ⟨z, rfl⟩ := hu
  rw [mem_compl_iff]
  intro hmem
  obtain ⟨w, hw⟩ := hmem
  exact sigmaio_base_ne X hij z w hw.symm

instance instQuasiCompactSigmaio (j : ι) : QuasiCompact $ Sigma.ι X j :=
  quasiCompact_sigmaio X j

end

end FunctorialResolution.Blowup
end
section
universe v

open CategoryTheory.Limits TopologicalSpace Opposite

namespace FunctorialResolution.Blowup





theorem noetherianSpace_toScheme (X : Sch) [NoetherianSpace ↥X] (U : Opn X) :
    NoetherianSpace ↥(toScheme U) := by
  have h : Topology.IsInducing fun x : { y : X // y ∈ U } => (x : X) := ⟨rfl⟩
  exact h.noetherianSpace

instance instNoetherianSpaceToScheme (X : Sch) [NoetherianSpace ↥X] (U : Opn X) :
    NoetherianSpace ↥(toScheme U) :=
  noetherianSpace_toScheme X U

theorem isAffineHom_pullback_fst {X Y S : Sch} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom g] :
    IsAffineHom $ pullback.fst f g :=
  m98 (P := @IsAffineHom)
    (of_hasPullback f g).flip ‹IsAffineHom g›

instance instIsAffineHomSpecMapPullbackFst {k K : Type} [Field k] [Field K] {X : Sch}
    (p : X ⟶ Sp k) (ph_ : CommRingCat.of k ⟶ CommRingCat.of K) :
    IsAffineHom $ pullback.fst p $ Spec.map ph_ :=
  (@isAffineHom_pullback_fst X _ _ p (Spec.map ph_) (inferInstance))

section
variable {S X : Sch} (ι : S ⟶ X) [IsClosedImmersion ι] (Z : ISD S)
theorem le_comap_map_of_isClosedImmersion : Z ≤ (Z.map ι).comap ι := by
  let _a2 := subschemeι Z ≫ ι
  have hmapdef : Z.map ι = _a2.ker := rfl
  let _a0 := pullback.fst ι (Z.map ι).si
  have hcomapdef : (Z.map ι).comap ι
      = _a0.ker := rfl
  have hle : _a2.ker
      ≤ ker (Z.map ι).si := by simp_all
  set u := m64 _a2 (Z.map ι).si hle with hudef
  let _a1 := (pullback.snd ι (Z.map ι).si ≫ u) ≫ subschemeι Z
  have hk : _a1
      = _a0 := by
    have h2 : _a1 ≫ ι
        = _a0 ≫ ι := by
      rw [assoc, assoc, lift_fac _ _ hle]
      exact pullback.condition.symm
    exact mp_ (cancel_mono ι) h2
  rw [hcomapdef, ← hk, ker_comp]
  calc Z = (⊥ : Z.subscheme.IdealSheafData).map Z.si := by
        rw [Scheme.IdealSheafData.map_bot, q2]
    _ ≤ _ := Scheme.IdealSheafData.map_mono Z.si bot_le

theorem comap_map_of_isClosedImmersion :
    (Z.map ι).comap ι = Z :=
  le_antisymm (comap_map_le Z ι) $ le_comap_map_of_isClosedImmersion ι Z
end

theorem isOpen_connectedComponent_of_noetherianSpace (T : Type v) [TopologicalSpace T]
    [NoetherianSpace T] (x : T) : IsOpen $ connectedComponent x := by
  classical
  have hfin : {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}.Finite := by
    refine m197
      (m169) ?_
    rintro Z ⟨hZ, -⟩
    exact hZ
  have heq : (connectedComponent x)ᶜ
      = ⋃ Z ∈ {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}, Z := by
    apply m15
    intro y hy
    exact mem_biUnion
      (⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy $ h mem_irreducibleComponent⟩ :
        irreducibleComponent y ∈
          {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x})
      mem_irreducibleComponent
    intro z hz
    simp [mem_iUnion, mem_ofPred_eq, exists_prop] at hz
    obtain ⟨Z, ⟨hZ, hZ'⟩, hzZ⟩ := hz
    intro hzc
    have h1 :=
      hZ.1.2.isPreconnected.subset_connectedComponent hzZ
    rw [← connectedComponent_eq hzc] at h1
    exact hZ' h1
  rw [← isClosed_compl_iff, heq]
  exact hfin.isClosed_biUnion fun Z hZ => isClosed_of_mem_irreducibleComponents _ hZ.1

end FunctorialResolution.Blowup

namespace TopologicalSpace.NoetherianSpace

section
variable (Y : Type) [TopologicalSpace Y] [NoetherianSpace Y]
theorem finite_range_connectedComponent :
    (Set.range fun x : Y => connectedComponent x).Finite := by
  classical
  refine m197 (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.image fun Z => ⋃ z ∈ Z, connectedComponent z) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩
  apply m15
  intro y hy
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
  rwa [← connectedComponent_eq $ ((irreducibleComponent_mem_irreducibleComponents x).1.2.isPreconnected.subset_connectedComponent mem_irreducibleComponent) hz] at hyz
  intro y hy
  exact mem_biUnion mem_irreducibleComponent hy

theorem isClosed_setOf_connectedComponent_subset (A : Set Y) : IsClosed {x : Y | connectedComponent x ⊆ A} := by
  classical
  have hfin :
      {C : Set Y | C ∈ m30 connectedComponent ∧ C ⊆ A}.Finite := by
    refine (finite_range_connectedComponent Y).subset ?_
    rintro C ⟨hC, -⟩
    exact hC
  have heq : {x : Y | connectedComponent x ⊆ A}
      = ⋃ C ∈ {C : Set Y | C ∈ m30 connectedComponent ∧ C ⊆ A}, C := by
    apply m15
    intro x hx
    exact mem_biUnion ⟨⟨x, rfl⟩, hx⟩ mem_connectedComponent
    intro x hx
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨⟨y, hy⟩, hCA⟩ := hC
    rw [← hy] at hxC hCA
    dsimp
    rwa [← connectedComponent_eq hxC]
  rw [heq]
  refine hfin.isClosed_biUnion ?_
  rintro C ⟨⟨x, hx⟩, -⟩
  rw [sy_ hx]
  exact isClosed_connectedComponent
end

end TopologicalSpace.NoetherianSpace

namespace AlgebraicGeometry

namespace Scheme

theorem presheaf_map_eq_of_parallel (X1 : Sch) {A B : (X1.Opens)ᵒᵖ} (g1_ g2_ : A ⟶ B) :
    X1.presheaf.map g1_ = X1.presheaf.map g2_ :=
  congrArg X1.presheaf.map $ Quiver.Hom.unop_inj $ elim _ _

namespace Hom

theorem appLE_congr_hom {A B : Sch} {f g : A ⟶ B} (hfg : f = g) (O : Opn B)
    (S : Opn A) (h1 : S ≤ f ⁻¹ᵁ O) (h2 : S ≤ g ⁻¹ᵁ O) :
    appLE f O S h1 = appLE g O S h2 := by
  subst hfg
  rfl

theorem range_comp_base {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  have hcomp : ∀ x, bsM (f ≫ g) x = bsM g (bsM f x) := fun _ => rfl
  apply m15
  rintro z ⟨x, rfl⟩
  exact ⟨bsM f x, ⟨x, rfl⟩, sy_ $ hcomp x⟩
  rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
  exact ⟨x, hcomp x⟩

end Hom

end Scheme

theorem quasiCompact_of_compactSpace_of_subsingleton {W S : Sch} (f : W ⟶ S)
    [CompactSpace ↥W] [Subsingleton ↥S] : QuasiCompact f := by
  constructor
  intro U _ _
  rcases eq_empty_or_nonempty (bsM f ⁻¹' U) with h | ⟨w, hw⟩
  rw [h]
  exact isCompact_empty
  have h2 : bsM f ⁻¹' U = univ := by
    refine eq_univ_of_forall fun w' => ?_
    have hww : bsM f w' = bsM f w := elim _ _
    show bsM f w' ∈ U
    rw [hww]
    exact hw
  rw [h2]
  exact isCompact_univ

end AlgebraicGeometry
end
section
open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution


section
variable (Y : Sch) {ι : Type}
section
variable (U : ι → Opn Y)
noncomputable abbrev sigmaOpens : Sch :=
  ∐ fun i => toScheme $ U i

noncomputable abbrev sigmaOpensDesc :
    sigmaOpens Y U ⟶ Y :=
  desc fun i => (U i).ι

theorem sigma_io_sigmaOpensDesc (i : ι) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U = (U i).i := by
  simp

theorem sigma_io_sigmaOpensDesc_assoc (i : ι)
    {Z : Sch} (h : Y ⟶ Z) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U ≫ h = (U i).i ≫ h := by
  simp
end

theorem isAffine_sigmaOpens [Finite ι] (U : ι → Opn Y)
    (hU : ∀ i, IsAffineOpen $ U i) : IsAffine $ sigmaOpens Y U := by
  have : ∀ i, IsAffine (U i).toScheme := hU
  exact inferInstanceAs $ IsAffine $ ∐ fun i => oSch $ U i
end

theorem isReduced_of_forall_isReduced_stalk (X : Sch)
    (h : ∀ x : X, _root_.IsReduced $ X.presheaf.stalk x) : IsReduced X := by
  exact isReduced_of_isReduced_stalk X

theorem isReduced_sigmaOpens (Y : Sch) [IsReduced Y] {ι : Type} (U : ι → Opn Y) :
    IsReduced $ sigmaOpens Y U := by
  refine isReduced_of_forall_isReduced_stalk _ ?_
  intro x
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun i => oSch $ U i).surjective x
  have hx' := by simpa using hx
  subst hx'
  let e := ((asIso $ (Sigma.ι (fun i => oSch $ U i) i).stalkMap y).commRingCatIsoToRingEquiv).trans
      ((asIso $ (opI $ U i).stalkMap y).commRingCatIsoToRingEquiv.symm)
  exact ⟨fun _ hx => e.injective $ ((hx.map e).eq_zero).trans (map_zero e).symm⟩

instance instIsReducedOpensCoprod (Y : Sch) [IsReduced Y] {ι : Type} (U : ι → Opn Y) :
    IsReduced $ sigmaOpens Y U :=
  isReduced_sigmaOpens Y U

theorem etale_isZariskiLocalAtSource : IsZariskiLocalAtSource $ @Etale.{0} := by
  exact @instIsZariskiLocalAtSource (@Etale.{0}) _ inferInstance

theorem etale_sigmaDesc {ι : Type} {X : ι → Sch} {Z : Sch}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Etale $ f i) : Etale $ desc f := by
  have hloc := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc hf

theorem etale_sigmaOpensDesc (Y : Sch) {ι : Type} (U : ι → Opn Y) :
    Etale $ sigmaOpensDesc Y U := by
  have hloc := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

instance instEtaleOpensCoprodDesc (Y : Sch) {ι : Type} (U : ι → Opn Y) :
    Etale $ sigmaOpensDesc Y U :=
  etale_sigmaOpensDesc Y U

theorem locallyOfFiniteType_sigmaOpensDesc (Y : Sch) {ι : Type} (U : ι → Opn Y) :
    LocallyOfFiniteType $ sigmaOpensDesc Y U := by
  infer_instance

instance instLocallyOfFiniteTypeOpensCoprodDesc (Y : Sch) {ι : Type} (U : ι → Opn Y) :
    LocallyOfFiniteType $ sigmaOpensDesc Y U :=
  locallyOfFiniteType_sigmaOpensDesc Y U

section
variable (Y : Sch)
theorem surjective_sigmaOpensDesc {ι : Type} (U : ι → Opn Y)
    (hU : iSup U = ⊤) : Surjective $ sigmaOpensDesc Y U := by
  constructor
  intro y
  have hy : y ∈ iSup U := by rw [hU]
                             trivial
  obtain ⟨i, hi⟩ := mp_ mem_iSup hy
  exact ⟨bsM (Sigma.ι (fun i => oSch $ U i) i) (⟨y, hi⟩ : (oSch $ U i)), congrArg (fun f : oSch (U i) ⟶ Y => bsM f (⟨y, hi⟩ : (oSch $ U i))) $ sigma_io_sigmaOpensDesc Y U i⟩

private theorem exists_isAffineOpen_mem (x : Y) :
    ∃ U : Opn Y, IsAffineOpen U ∧ x ∈ U := by
  exact ⟨(Y.affineOpenCover.3 $ Y.affineOpenCover.4 x).opensRange,
    isAffineOpen_opensRange _, Y.affineOpenCover.5 x⟩

theorem exists_finite_affine_cover [CompactSpace Y] :
    ∃ (ι : Type) (_ : Finite ι) (U : ι → Opn Y),
      (∀ i, IsAffineOpen $ U i) ∧ iSup U = ⊤ := by
  classical
  choose V hV hxV using exists_isAffineOpen_mem Y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set Y))
    (fun x => (V x).isOpen) fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩
  refine ⟨{ x : Y // x ∈ t }, inferInstance, fun i => V i.1, fun i => hV i.1, ?_⟩
  refine m55 ?_
  rw [coe_iSup, coe_top]
  refine eq_univ_of_univ_subset fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp $ ht $ mem_univ x
  exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
end

theorem exists_affine_etale_cover_of_isReduced {k : Type} [Field k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced Y] :
    ∃ (W : Sch) (q : W ⟶ Sp k) (g : W ⟶ Y),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType q ∧ QuasiCompact q ∧
        Etale g ∧ Surjective g ∧ g ≫ p = q := by
  have hsub : Subsingleton $ Sp k := inferInstanceAs $ Subsingleton $ PrimeSpectrum k
  have hcs : CompactSpace $ Sp k := inferInstance
  have hcY : CompactSpace Y := by
    constructor
    have h := (‹QuasiCompact p›).isCompact_preimage univ isOpen_univ isCompact_univ
    rwa [preimage_univ] at h
  obtain ⟨ι, hio, U, hUaff, hUsup⟩ := exists_finite_affine_cover Y
  have hW := isAffine_sigmaOpens Y U hUaff
  have : CompactSpace $ sigmaOpens Y U := inferInstance
  refine ⟨sigmaOpens Y U, sigmaOpensDesc Y U ≫ p, sigmaOpensDesc Y U, hW,
    isReduced_sigmaOpens Y U, ?_, quasiCompact_of_compactSpace_of_subsingleton _, etale_sigmaOpensDesc Y U,
    surjective_sigmaOpensDesc Y U hUsup, rfl⟩
  infer_instance

instance instIsZariskiLocalAtSourceSmooth : IsZariskiLocalAtSource $ @Smooth.{0} :=
  by
  have hrh : HasRingHomProperty (@Smooth.{0}) Smooth := inferInstance
  exact @instIsZariskiLocalAtSource (@Smooth.{0}) _ hrh

theorem smooth_sigmaDesc {ι : Type} {X : ι → Sch} {Z : Sch}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Smooth $ f i) : Smooth $ desc f :=
  IsZariskiLocalAtSource.sigmaDesc hf



theorem isReduced_of_isOpenImmersion_cover {X : Sch} {J : Type} {V : J → Sch}
    (m : (j : J) → V j ⟶ X) (hm : ∀ j, IsOpenImmersion $ m j)
    (hV : ∀ j, IsReduced $ V j)
    (hcov : ∀ x : ↥X, ∃ (j : J) (y : ↥(V j)), (m j).base y = x) :
    IsReduced X := by
  have : ∀ x, _root_.IsReduced $ stkX X x := by
    intro x
    obtain ⟨j, y, hy⟩ := hcov x
    subst hy
    let _a0 := (m j).stalkMap y
    exact isReduced_of_injective (hom _a0)
      (asIso _a0).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk X

section
variable (Y : Sch) {ι : Type} (U : ι → Opn Y)
section
variable (W') (g' : W' ⟶ Y)
section
variable (V) (r : V ⟶ pullback g' (sigmaOpensDesc Y U))
theorem etale_comp_fst_pullback_sigmaOpensDesc [Etale r] :
    Etale $ r ≫ pullback.fst g' (sigmaOpensDesc Y U) := by
  have : Etale $ pullback.fst g' $ sigmaOpensDesc Y U := inferInstance
  infer_instance

theorem comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc :
    r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ g' =
      r ≫ pullback.snd g' (sigmaOpensDesc Y U) ≫ sigmaOpensDesc Y U := by
  rw [pullback.condition]
end

theorem etale_comp_snd_pullback_sigmaOpensDesc [Etale g'] (V : Sch)
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale $ r ≫ pullback.snd g' (sigmaOpensDesc Y U) := by
  have : Etale $ pullback.snd g' $ sigmaOpensDesc Y U := inferInstance
  infer_instance

theorem surjective_comp_snd_pullback_sigmaOpensDesc [Surjective g'] (V : Sch)
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective $ r ≫ pullback.snd g' (sigmaOpensDesc Y U) := by
  have : Surjective $ pullback.snd g' $ sigmaOpensDesc Y U := inferInstance
  infer_instance
end

theorem surjective_comp_fst_pullback_sigmaOpensDesc (hU : iSup U = ⊤)
    (W' : Sch) (g' : W' ⟶ Y) (V : Sch)
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective $ r ≫ pullback.fst g' (sigmaOpensDesc Y U) := by
  have := surjective_sigmaOpensDesc Y U hU
  have : Surjective $ pullback.fst g' $ sigmaOpensDesc Y U := inferInstance
  infer_instance
end

section
variable {k : Type} [Field k]
theorem quasiCompact_of_isAffine_of_locallyOfFiniteType {W' : Sch}
    [IsAffine W'] (q : W' ⟶ Sp k) [LocallyOfFiniteType q]
    {Z : Sch} (g : W' ⟶ Z) : QuasiCompact g := by
  let _a0 := Γ(W', ⊤)
  let : Algebra Γ(Sp k, ⊤) _a0 := (hAT q).hom.toAlgebra
  have : FiniteType Γ(Sp k, ⊤) _a0 := (iff_of_isAffine (P := @LocallyOfFiniteType) (Q := @RingHom.FiniteType) (f := q)).mp inferInstance
  have : IsNoetherianRing Γ(Sp k, ⊤) := by
    have e :=
      (GSpecIso $ m10 k).symm.commRingCatIsoToRingEquiv
    exact isNoetherianRing_of_surjective (m10 k) Γ(Sp k, ⊤)
      e.toRingHom e.surjective
  have : IsNoetherianRing _a0 :=
    Algebra.FiniteType.isNoetherianRing Γ(Sp k, ⊤) _a0
  have : m86 $ Spec Γ(W', ⊤) :=
    inferInstanceAs $ m86 $ PrimeSpectrum _a0
  refine ⟨fun Vo hVo hVc => ?_⟩
  have he : IsCompact $ (TopCat.homeoOfIso $ Scheme.forgetToTop.mapIso W'.isoSpec) '' (preimage g Vo) := TopologicalSpace.NoetherianSpace.isCompact _
  rwa [Homeomorph.isCompact_image] at he
end

theorem exists_sigma_io_base_eq {J : Type} (f : J → Sch) (x : ↥(∐ f)) :
    ∃ (j : J) (y : ↥(f j)), (Sigma.ι f j).base y = x := by
  refine ⟨((sigmaMk f).symm x).1, ((sigmaMk f).symm x).2, ?_⟩
  rw [← sigmaMk_mk]
  simp

theorem exists_affine_etale_cover_pullback_sigmaOpensDesc {k : Type} [Field k]
    (Y : Sch) (p : Y ⟶ Sp k)
    [LocallyOfFiniteType p] [QuasiCompact p]
    {ι : Type} [Finite ι] (U : ι → Opn Y) (hU : ∀ i, IsAffineOpen $ U i)
    (W' : Sch) [IsAffine W'] [IsReduced W'] (q : W' ⟶ Sp k)
    [LocallyOfFiniteType q] [QuasiCompact q] (g' : W' ⟶ Y) [Etale g'] (_hg : g' ≫ p = q) :
    ∃ (V : Sch) (s : V ⟶ Sp k)
      (r : V ⟶ pullback g' (sigmaOpensDesc Y U)),
      IsAffine V ∧ IsReduced V ∧ LocallyOfFiniteType s ∧ QuasiCompact s ∧
        Etale r ∧ Surjective r ∧
        r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ q = s := by
  let _c0 := sigmaOpensDesc Y U
  have := quasiCompact_of_isAffine_of_locallyOfFiniteType q g'
  let _a1 := pullback g' _c0
  have : IsReduced _a1 :=
    by
    refine isReduced_of_isOpenImmersion_cover
      (fun i => pullback.fst (pullback.snd g' _c0)
        (Sigma.ι (fun j => oSch $ U j) i)) (fun i => inferInstance) ?_ ?_
    intro i
    have hoi : IsOpenImmersion
        (Sigma.ι (fun j => oSch $ U j) i ≫ sigmaOpensDesc Y U) := by
      rw [sigma_io_sigmaOpensDesc]
      infer_instance
    have :=
      isReduced_of_isOpenImmersion
        (pullback.fst g' $ Sigma.ι (fun j => oSch $ U j) i ≫ sigmaOpensDesc Y U)
    exact isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso g' _c0
        (Sigma.ι (fun j => oSch $ U j) i)).hom
    intro x
    obtain ⟨i, y, hy⟩ :=
      exists_sigma_io_base_eq (fun j => oSch $ U j)
        (bsM (pullback.snd g' _c0) x)
    obtain ⟨z, hz1, _⟩ :=
      exists_preimage_pullback
        (f := pullback.snd g' _c0)
        (g := Sigma.ι (fun j => oSch $ U j) i) x y hy.symm
    exact ⟨i, z, hz1⟩
  have : CompactSpace _a1 :=
    by
    have := isAffine_sigmaOpens Y U hU
    have : CompactSpace $ sigmaOpens Y U := inferInstance
    have : QuasiCompact $ pullback.snd g' _c0 := inferInstance
    constructor
    have hcp := QuasiCompact.isCompact_preimage (f := pullback.snd g' _c0)
      univ isOpen_univ isCompact_univ
    simpa using hcp
  have : LocallyOfFiniteType $ pullback.fst g' _c0 := inferInstance
  let _a0 := pullback.fst g' _c0 ≫ q
  have : LocallyOfFiniteType _a0 := inferInstance
  have : QuasiCompact _a0 :=
    by
      have : Subsingleton $ Sp k := inferInstance
      refine ⟨fun W hW hW' => ?_⟩
      rcases eq_empty_or_nonempty W with rfl | ⟨z, hz⟩
      simp
      have hW2 := eq_univ_of_forall fun w => by
        rwa [elim w z]
      rw [hW2]
      simpa using isCompact_univ
  obtain ⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_affine_etale_cover_of_isReduced _a1
      _a0
  exact ⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩

end FunctorialResolution.EmbeddedResolution
end
section
open TensorProduct

namespace FunctorialResolution.EmbeddedResolution

theorem algebraMap_tmul_one_eq_one_tmul_algebraMap {A B A' : Type} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (a : A) :
    (algebraMap A B a) ⊗ₜ[A] (1 : A') = (1 : B) ⊗ₜ[A] (algebraMap A A' a) := by
  let _a0 := (1 : B)
  calc (algebraMap A B a) ⊗ₜ[A] (1 : A') = (a • _a0) ⊗ₜ[A] (1 : A') := by
        rw [algebraMap_eq_smul_one]
    _ = a • (_a0 ⊗ₜ[A] (1 : A')) := smul_tmul' a (1 : B) (1 : A')
    _ = _a0 ⊗ₜ[A] (a • (1 : A')) := sy_ $ tmul_smul a (1 : B) (1 : A')
    _ = _a0 ⊗ₜ[A] (algebraMap A A' a) := by rw [algebraMap_eq_smul_one]

theorem appLE_congr_of_eq {X Y : Sch} {f f' : X ⟶ Y} (hf : f = f')
    (U : Opn Y) (W : Opn X) (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ f' ⁻¹ᵁ U) :
    appLE f U W e = appLE f' U W e' := by
  subst hf
  rfl

theorem lid_rTensor_subtype_mem_map {R A' : Type} [CommRing R] [CommRing A'] [Algebra R A']
    (K : Ideal R) (y : K ⊗[R] A') :
    (lid R A') (rTensor A' K.subtype y) ∈ K.map (algebraMap R A') := by
  induction y using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact m97 _
  | tmul k a =>
      have hka : (lid R A') (rTensor A' K.subtype $ k ⊗ₜ[R] a)
          = (k : R) • a := by simp
      rw [hka, smul_def]
      exact mul_mem_right _ _ $ mem_map_of_mem _ k.2
  | add y z hy hz =>
      rw [map_add, map_add]
      exact m60 _ hy hz

theorem span_eq_top_of_le_iSup_basicOpen {X : Sch} (V : X.affineOpens)
    (s : Set ↑(X.sec (V : Opn X)))
    (hcov : (V : Opn X) ≤ ⨆ f : s, X.basicOpen (f : ↑(X.sec (V : Opn X)))) :
    span s = ⊤ :=
  mp (V.2.self_le_iSup_basicOpen_iff (s := s)) hcov

theorem ker_includeRight_eq_map_ker (R B A' : Type) [CommRing R] [CommRing B] [CommRing A']
    [Algebra R B] [Algebra R A'] [Module.Flat R A'] :
    RingHom.ker (includeRight : A' →ₐ[R] B ⊗[R] A').toRingHom =
      (RingHom.ker $ algebraMap R B).map (algebraMap R A') := by
  have hex : Exact ((m41 $ algebraMap R B).subtype) $ linearMap R B := by
    rw [exact_iff, range_subtype]
    ext r
    simp [mem_ker]
  apply le_antisymm
  intro x hx
  have hx0 : (1 : B) ⊗ₜ[R] x = 0 := by simp_all
  have key : (rTensor A' $ linearMap R B) ((1 : R) ⊗ₜ[R] x) = 0 := by
    simpa using hx0
  have hmem : (1 : R) ⊗ₜ[R] x ∈
      LinearMap.range (rTensor A' $ (m41 $ algebraMap R B).subtype) := by
    rw [← mp_ exact_iff $ Module.Flat.rTensor_exact (R := R) (M := A') hex]
    exact LinearMap.mem_ker.mpr key
  obtain ⟨y, hy⟩ := hmem
  have hx1 : x = (lid R A') ((1 : R) ⊗ₜ[R] x) := by simp
  rw [hx1, ← hy]
  exact lid_rTensor_subtype_mem_map _ y
  rw [map_le_iff_le_comap]
  intro k hk
  rw [mem_comap, mem_ker]
  simp_all

theorem exists_pow_mul_mem_of_map_le {A Af : Type} [CommRing A] [CommRing Af]
    [Algebra A Af] (f : A) [IsLocalization.Away f Af] {I J : Ideal A}
    (hle : I.map (algebraMap A Af) ≤ J.map (algebraMap A Af)) {x : A} (hx : x ∈ I) :
    ∃ n : ℕ, f ^ n * x ∈ J := by
  have hmem :=
    hle $ mem_map_of_mem _ hx
  rw [mem_map_algebraMap_iff (powers f) Af] at hmem
  obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hxy⟩ := hmem
  obtain ⟨k, hk⟩ := hm
  have hk' := hk
  rw [← map_mul] at hxy
  obtain ⟨c, hc⟩ := mp_ (eq_iff_exists (powers f) Af) hxy
  obtain ⟨l, hl⟩ := c.2
  let _a0 := c
  have hl' : f ^ l = _a0 := hl
  have hc' : _a0 * (x * m) = _a0 * y := hc
  refine ⟨l + k, ?_⟩
  have key : f ^ (l + k) * x = _a0 * (x * m) := by
    rw [pow_add, hl', ← hk']
    ring
  rw [key, hc']
  exact mul_mem_left _ _ hy

theorem ideal_eq_of_span_eq_top {A : Type} [CommRing A] {I J : Ideal A} {s : Set A}
    (hspan : span s = ⊤)
    (hIJ : ∀ f ∈ s, ∀ x ∈ I, ∃ n : ℕ, f ^ n * x ∈ J)
    (hJI : ∀ f ∈ s, ∀ x ∈ J, ∃ n : ℕ, f ^ n * x ∈ I) : I = J := by
  apply le_antisymm
  intro x hx
  refine mem_of_span_eq_top_of_smul_pow_mem J s hspan x ?_
  rintro ⟨f, hf⟩
  obtain ⟨n, hn⟩ := hIJ f hf x hx
  exact ⟨n, by simpa [smul_eq_mul] using hn⟩
  intro x hx
  refine mem_of_span_eq_top_of_smul_pow_mem I s hspan x ?_
  rintro ⟨f, hf⟩
  obtain ⟨n, hn⟩ := hJI f hf x hx
  exact ⟨n, by simpa [smul_eq_mul] using hn⟩

theorem ideal_eq_of_ideal_affineBasicOpen_eq {X : Sch} (I J : ISD X) (V : X.affineOpens)
    (s : Set $ X.sec (V : Opn X)) (hspan : span s = ⊤)
    (hs : ∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) :
    I.ideal V = J.ideal V := by
  have key : ∀ I J : ISD X,
      (∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) →
      ∀ f ∈ s, ∀ x ∈ I.ideal V, ∃ n, f ^ n * x ∈ J.ideal V := by
    intro I J hs f hf x hx
    have := V.2.isLocalization_basicOpen f
    let _a0 := pMap X (homOfLE $ X.basicOpen_le f).op
    have hmap : (I.ideal V).map _a0.hom
        = (J.ideal V).map _a0.hom := by
      rw [I.map_ideal_basicOpen V f, J.map_ideal_basicOpen V f, hs f hf]
    exact exists_pow_mul_mem_of_map_le (Af := Γ(X, bOpn X f)) f (le_of_eq hmap) hx
  exact ideal_eq_of_span_eq_top hspan (key I J hs) $ key J I fun f hf => sy_ $ hs f hf

theorem mem_map_iInf_ker_of_forall_one_tmul_eq_zero {R A' : Type} [CommRing R] [CommRing A']
    [Algebra R A'] [Module.Flat R A'] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → Type) [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)] (s : A')
    (hs : ∀ j, (1 : B j) ⊗ₜ[R] s = 0) :
    s ∈ Ideal.map (algebraMap R A') (⨅ j, RingHom.ker (algebraMap R (B j))) := by
  have h0 : (1 : ∀ j, B j) ⊗ₜ[R] s = 0 := by
    have h1 : (1 : ∀ j, B j) = ∑ j : ι, Pi.single j (1 : B j) := by
      ext k
      simp [Finset.sum_apply]
    rw [h1, TensorProduct.sum_tmul]
    refine sum_eq_zero ?_
    intro j _
    have h2 : (Pi.single j 1) ⊗ₜ[R] s
        = rTensor A' (LinearMap.single R B j) (1 ⊗ₜ[R] s) := by
      simp
    rw [h2, hs j, map_zero]
  have hk : m41 (algebraMap R (∀ j, B j)) = ⨅ j, m41 (algebraMap R (B j)) := by
    ext r
    simp [mem_ker, mem_iInf, funext_iff]
  rw [← hk, ← ker_includeRight_eq_map_ker R (∀ j, B j) A']
  simpa [mem_ker] using h0

theorem appLE_top_comp_GaSpecIso_hom {Y : Sch} {V : Opn Y} (hV : IsAffineOpen V)
    {S : CRC} (rh_ : (Y.sec V) ⟶ S) (q : Spec S ⟶ Y)
    (hqe : q = Spec.map rh_ ≫ hV.fromSpec) (e : (⊤ : (Spec S).Opens) ≤ q ⁻¹ᵁ V) :
    appLE q V ⊤ e ≫ (Scheme.ΓSpecIso S).hom = rh_ := by
  subst hqe
  have h1 :=
    SpecMap_appLE_fromSpec _ hV (isAffineOpen_top $ Spec S) e
  rw [fromSpec_top, isoSpec_Spec_inv, ← assoc, ← map_comp] at h1
  have h3 := mp_ (cancel_mono hV.fromSpec) h1
  have h4 := Spec.map_injective h3
  rw [h4, assoc, inv_hom_id, comp_id]

section
variable {Z X X' Z' : Sch} {h : Z ⟶ X} {g : X' ⟶ X} {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g)
include H
theorem quasiCompact_of_isPullback [QuasiCompact h] :
    QuasiCompact h' :=
  m122 (P := @QuasiCompact) H ‹QuasiCompact h›

theorem one_tmul_eq_zero_of_app_eq_zero
    (U : X.affineOpens) (V : X'.affineOpens) (e : (V : Opn X') ≤ g ⁻¹ᵁ (U : Opn X))
    (W : Z.affineOpens) (hW : (W : Opn Z) ≤ h ⁻¹ᵁ (U : Opn X))
    [Algebra ↑(X.sec (U : Opn X)) ↑(X'.sec (V : Opn X'))]
    [Algebra ↑(X.sec (U : Opn X)) ↑(Z.sec (W : Opn Z))]
    (hVa : (algebraMap ↑(X.sec (U : Opn X)) ↑(X'.sec (V : Opn X')))
        = (appLE g (U : Opn X) (V : Opn X') e).hom)
    (hWa : (algebraMap ↑(X.sec (U : Opn X)) ↑(Z.sec (W : Opn Z)))
        = (appLE h (U : Opn X) (W : Opn Z) hW).hom)
    (s : ↑(X'.sec (V : Opn X'))) (hs : (h'.app (V : Opn X')).hom s = 0) :
    (1 : ↑(Z.sec (W : Opn Z))) ⊗ₜ[↑(X.sec (U : Opn X))] s = 0 := by
  have hUaff := U.2
  have hVaff := V.2
  let _a2 := V
  have hWaff := W.2
  set T : CRC :=
    m10 ((Z.sec W) ⊗[X.sec U] (X'.sec _a2)) with hT
  set il : Z.sec W ⟶ T :=
    ofHom (includeLeftRingHom) with hil
  set ir : X'.sec _a2 ⟶ T :=
    ofHom (includeRight).toRingHom with hir
  let _a0 := appLE h U W hW
  let _a4 := appLE g U V e
  have h3 : _a0 ≫ il
      = _a4 ≫ ir := by
    ext a
    dsimp
    rw [← hWa, ← hVa]
    exact algebraMap_tmul_one_eq_one_tmul_algebraMap a
  set p : Spec T ⟶ Z := m12 il ≫ hWaff.fromSpec with hp
  set q : Spec T ⟶ X' := m12 ir ≫ hVaff.fromSpec with hq
  have hcomm : p ≫ h = q ≫ g := by
    have h1 := SpecMap_appLE_fromSpec h hUaff hWaff hW
    have h2 := SpecMap_appLE_fromSpec g hUaff hVaff e
    calc p ≫ h = m12 il ≫ (hWaff.fromSpec ≫ h) := by rw [hp, assoc]
      _ = m12 il ≫ m12 _a0 ≫ hUaff.fromSpec := by
          rw [h1]
      _ = Spec.map (_a0 ≫ il) ≫ hUaff.fromSpec := by
          rw [map_comp, assoc]
      _ = Spec.map (_a4 ≫ ir) ≫ hUaff.fromSpec := by rw [h3]
      _ = Spec.map ir ≫ Spec.map _a4 ≫ hUaff.fromSpec := by
          rw [map_comp, assoc]
      _ = Spec.map ir ≫ (hVaff.fromSpec ≫ g) := by rw [h2]
      _ = q ≫ g := by rw [hq, assoc]
  have hr := H.lift_snd p q hcomm
  have hqpre : q ⁻¹ᵁ V = ⊤ := by
    rw [hq, comp_preimage, hVaff.fromSpec_preimage_self, preimage_top]
  have e1 := hqpre.ge
  let _m0 := h' ⁻¹ᵁ V
  have hrp : H.lift p q hcomm ⁻¹ᵁ _m0 = ⊤ := by
    rw [← comp_preimage, hr, hqpre]
  have hsplit : appLE q V ⊤ e1
      = appLE h' V _m0 le_rfl
        ≫ appLE (H.lift p q hcomm) _m0 ⊤ hrp.ge := by
    rw [appLE_comp_appLE]
    exact appLE_congr_of_eq hr.symm _ _ _ _
  have hA : (appLE q V ⊤ e1).hom s = 0 := by
    rw [hsplit]
    simp [hom_comp, coe_comp, Function.comp_apply]
    rw [← app_eq_appLE h' (U := _a2), hs, map_zero]
  have step : ir.hom s = 0 := by
    rw [← appLE_top_comp_GaSpecIso_hom hVaff ir q hq e1]
    simp [hom_comp, coe_comp, Function.comp_apply]
    rw [hA, map_zero]
  exact step

theorem ker_app_eq_map_ker_of_isPullback_of_flat [QuasiCompact h]
    [Flat g] (U : X.affineOpens) (V : X'.affineOpens)
    (e : (V : Opn X') ≤ g ⁻¹ᵁ (U : Opn X)) :
    RingHom.ker (h'.app (V : Opn X')).hom =
      Ideal.map (appLE g (U : Opn X) (V : Opn X') e).hom
        (RingHom.ker (h.app (U : Opn X)).hom) := by
  classical
  have hpre : h' ⁻¹ᵁ V ≤ g' ⁻¹ᵁ (h ⁻¹ᵁ U) := by
    rw [← comp_preimage, H.w, comp_preimage]
    exact fun x hx => e hx
  have hcomm : appLE h U (preU h U) le_rfl
      ≫ appLE g' (preU h U) (preU h' V) hpre
      = appLE g U V e
        ≫ appLE h' V (preU h' V) le_rfl := by
    rw [appLE_comp_appLE, appLE_comp_appLE]
    exact appLE_congr_of_eq H.w _ _ _ _
  apply le_antisymm
  intro s hs
  have hs0 := RingHom.mem_ker.mp hs
  let _a0 := pre h (U : Opn X)
  have hcov : (_a0 : Set Z)
      ⊆ ⋃ W : {W : affO Z // W ≤ pre h U},
          (((W.1 : affO Z) : Opn Z) : Set Z) := by
    intro z hz
    let _a2 := pre h (U : Opn X)
    obtain ⟨W, hW1, hW2⟩ : ∃ W : affO Z, (W : Opn Z) ≤ _a2 ∧ z ∈ (W : Opn Z) := by
      obtain ⟨y, hy⟩ := Z.affineCover.covers z
      let _a0 := Z.affineCover.f $ Z.affineCover.idx z
      have hWaff : IsAffineOpen _a0.opensRange :=
        isAffineOpen_opensRange _
      have hz1 : z ∈ _a0.opensRange := ⟨y, hy⟩
      obtain ⟨f, hfle, hzf⟩ := hWaff.exists_basicOpen_le (V := _a2) ⟨z, hz⟩ hz1
      exact ⟨⟨bOpn Z f, hWaff.basicOpen f⟩, hfle, hzf⟩
    exact Set.mem_iUnion.mpr ⟨⟨W, hW1⟩, hW2⟩
  obtain ⟨t, ht⟩ := (QuasiCompact.isCompact_preimage (f := h) (((U : Opn X)) : Set X) (U : Opn X).isOpen U.2.isCompact).elim_finite_subcover
    (fun W : {W : affO Z // W ≤ pre h U} =>
      ((W.1 : Opn Z) : Set Z))
    (fun W => (W.1 : Opn Z).isOpen) hcov
  let _a1 := X'.sec V
  let _ : Algebra (X.sec U) _a1 :=
    (appLE g U V e).hom.toAlgebra
  have : Module.Flat (X.sec U) _a1 := AlgebraicGeometry.HasRingHomProperty.appLE (P := @Flat) g ‹_› U V e
  let _ : ∀ j : {x // x ∈ t},
      Algebra (X.sec U) Γ(Z, (j.1.1 : Opn Z)) :=
    fun j => (appLE h U (j.1.1 : Opn Z) j.1.2).hom.toAlgebra
  have hzero : ∀ j : {x // x ∈ t},
      (1 : Γ(Z, (j.1.1 : Opn Z)))
        ⊗ₜ[X.sec U] s = 0 := by
    intro j
    exact one_tmul_eq_zero_of_app_eq_zero H U V e j.1.1 j.1.2 rfl rfl s hs0
  have hmem := mem_map_iInf_ker_of_forall_one_tmul_eq_zero
    (fun j : {x // x ∈ t} => Γ(Z, (j.1.1 : Opn Z))) s hzero
  have hcover2 : _a0
      ≤ ⨆ j : {x // x ∈ t}, (j.1.1 : Opn Z) := by
    intro z hz
    obtain ⟨W, hW1, hW2⟩ := Set.mem_iUnion₂.mp $ ht hz
    exact mpr_ mem_iSup ⟨⟨W, hW1⟩, hW2⟩
  refine map_mono ?_ hmem
  intro a ha
  rw [mem_ker]
  refine Z.sheaf.eq_of_locally_eq'
    (fun j : {x // x ∈ t} => (j.1.1 : Opn Z))
    (preU h U) (fun j => homOfLE j.1.2) hcover2 _ 0 ?_
  intro j
  exact tr_ (RingHom.mem_ker.mp $ mp_ (mem_iInf _) ha j) $ sy_ $ map_zero _
  rw [map_le_iff_le_comap]
  intro a ha
  rw [mem_comap, mem_ker]
  have h1 := congrArg (fun m : X.sec U ⟶ Γ(Z', pre h' V) =>
    (hom m) a) hcomm
  simp [hom_comp, coe_comp] at h1
  have hzero : (appLE h U (pre h U) le_rfl).hom a = 0 := by
    rw [← app_eq_appLE h (U := U)]
    exact RingHom.mem_ker.mp ha
  rw [app_eq_appLE h' (U := V), ← h1, hzero, map_zero]

theorem ker_eq_comap_ker_of_isPullback_of_flat
    [QuasiCompact h] [QuasiCompact h'] [Flat g] :
    h'.ker = h.ker.comap g := by
  classical
  apply m29
  funext V
  set s : Set $ xSec X' V :=
    {f | ∃ U : affO X, bOpn X' f ≤ pre g U} with hsdef
  have hs : ∀ f ∈ s, h'.ker.ideal (X'.affineBasicOpen f)
      = (kCm h g).ideal (X'.affineBasicOpen f) := by
    rintro f ⟨U, hU⟩
    have hV' := hU
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE h.ker g U
      (X'.affineBasicOpen f) hV', ker_apply, ker_apply]
    exact ker_app_eq_map_ker_of_isPullback_of_flat H U (X'.affineBasicOpen f) hV'
  have hspan : span s = ⊤ := by
    refine span_eq_top_of_le_iSup_basicOpen V s ?_
    intro x hx
    obtain ⟨y, hy⟩ := X.affineCover.covers $ bsM g x
    let _s0 := X.affineCover.idx $ bsM g x
    obtain ⟨f, hfle, hxf⟩ := V.2.exists_basicOpen_le
      (V := V ⊓ g ⁻¹ᵁ (X.affineCover.f _s0).opensRange)
      ⟨x, ⟨hx, ⟨y, hy⟩⟩⟩ hx
    exact mpr_ mem_iSup ⟨⟨f, ⟨⟨(X.affineCover.f _s0).opensRange, isAffineOpen_opensRange _⟩, le_trans hfle inf_le_right⟩⟩, hxf⟩
  exact ideal_eq_of_ideal_affineBasicOpen_eq _ _ V s hspan hs
end

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

section
variable (k : Type) [CommRing k]
section
variable {X : Sch} (p : X ⟶ Sp k)
section
variable (U : Opn X)
theorem le_preimage_top :
    U ≤ p ⁻¹ᵁ ⊤ := by
  intro _ _
  trivial

noncomputable def sectionsAlgebraMap : k →+* (X.sec U) :=
  (inv (GSpecIso $ CommRingCat.of k) ≫ appLE p ⊤ U (le_preimage_top k p U)).hom

theorem sectionsAlgebraMap_eq :
    sectionsAlgebraMap k p U =
      (inv (GSpecIso $ CommRingCat.of k) ≫ appLE p ⊤ U (le_preimage_top k p U)).hom :=
  rfl

@[reducible] noncomputable def sectionsAlgebra : Algebra k $ X.sec U :=
  (sectionsAlgebraMap k p U).toAlgebra

theorem algebraMap_sectionsAlgebra :
    @algebraMap k (X.sec U) _ _ (sectionsAlgebra k p U) = sectionsAlgebraMap k p U :=
  rfl
end

theorem finiteType_sections [LocallyOfFiniteType p] (U : X.affineOpens)
    [Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    FiniteType k Γ(X, U.1) := by
  let _c0 := GSpecIso $ m10 k
  have hft : (appLE p ⊤ U.1 $ le_preimage_top k p U.1).hom.FiniteType := by
    apply finiteType_appLE p (isAffineOpen_top _) U.2
  have hcomp : _c0.inv.hom.comp
      _c0.hom.hom = m99 _ := by
    rw [← hom_comp, hom_inv_id, hom_id]
  have hsurj : Function.Surjective _c0.inv.hom := fun y =>
    ⟨_c0.hom.hom y, congr_fun hcomp y⟩
  have hst : (sectionsAlgebraMap k p U.1).FiniteType := by
    rw [sectionsAlgebraMap_eq, hom_comp]
    exact hft.comp $ RingHom.FiniteType.of_surjective _ hsurj
  have hinst : ‹Algebra k Γ(X, U.1)› = (sectionsAlgebraMap k p U.1).toAlgebra :=
    algebra_ext _ _ fun r => congr_fun h r
  rwa [hinst]

section
variable {U V : Opn X} (h : V ≤ U)
theorem sectionsAlgebraMap_comp_restrict :
    (X.presheaf.map (homOfLE h).op).hom.comp (sectionsAlgebraMap k p U) =
      sectionsAlgebraMap k p V := by
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k p V, ← hom_comp, assoc, appLE_map]

theorem sectionsAlgebraMap_restrict_apply (a : k) :
    (X.presheaf.map (homOfLE h).op).hom (sectionsAlgebraMap k p U a) =
      sectionsAlgebraMap k p V a :=
  congr_fun (sectionsAlgebraMap_comp_restrict k p h) a
end

theorem isScalarTower_sections (U : Opn X) (f : (X.sec U))
    [Algebra k $ X.sec U] [Algebra k Γ(X, X.basicOpen f)]
    [Algebra (X.sec U) Γ(X, X.basicOpen f)]
    (hU : algebraMap k (X.sec U) = sectionsAlgebraMap k p U)
    (hV : algebraMap k Γ(X, X.basicOpen f) = sectionsAlgebraMap k p (X.basicOpen f))
    (hres : algebraMap (X.sec U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE $ X.basicOpen_le f).op).hom) :
    IsScalarTower k (X.sec U) Γ(X, X.basicOpen f) :=
  of_algebraMap_eq fun x => by
    rw [hV, hres, hU, sectionsAlgebraMap_restrict_apply]
end

section
variable [IsNoetherianRing k] {X : Sch} (p : X ⟶ Sp k) [LocallyOfFiniteType p]
section
variable (U : X.affineOpens) [hv6_1 : Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1)
include hv6_1 h
theorem isNoetherianRing_sections :
    IsNoetherianRing Γ(X, U.1) := by
  have := finiteType_sections k p U h
  exact Algebra.FiniteType.isNoetherianRing k Γ(X, U.1)

theorem finitePresentation_kaehlerDifferential_sections :
    FinitePresentation Γ(X, U.1) $ KaehlerDifferential k Γ(X, U.1) := by
  have := finiteType_sections k p U h
  have := isNoetherianRing_sections k p U h
  have : Module.Finite Γ(X, U.1) $ KaehlerDifferential k Γ(X, U.1) := inferInstance
  exact finitePresentation_of_finite ..
end

section
variable (I : ISD X)
noncomputable def derivIdealSheaf :
    IdealSheafData X where
  ideal U := @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) $ I.ideal U
  map_ideal_basicOpen := by
    intro U f
    let algU := sectionsAlgebra k p U.1
    let algV := sectionsAlgebra k p $ X.basicOpen f
    let algUV :=
      (X.presheaf.map (homOfLE $ X.basicOpen_le f).op).hom.toAlgebra
    have htower :=
      isScalarTower_sections k p U.1 f rfl rfl rfl
    have hloc := U.2.isLocalization_basicOpen f
    have hfp :=
      finitePresentation_kaehlerDifferential_sections k p U rfl
    have hI := I.map_ideal_basicOpen U f
    have key := map_derivIdeal_away (k := k) (S' := Γ(X, X.basicOpen f)) f $ I.ideal U
    exact key.trans $ congrArg (@derivIdeal k _ Γ(X, X.basicOpen f) _ algV) hI

@[simp] theorem derivIdealSheaf_ideal (U : X.affineOpens) :
    (derivIdealSheaf k p I).ideal U = @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) :=
  rfl

theorem derivIdealSheaf_pow_succ_le (n : ℕ) :
    derivIdealSheaf k p (I ^ (n + 1)) ≤ I ^ n * derivIdealSheaf k p I := by
  intro U
  have hmul : ∀ A B : ISD X, (A * B).ideal U = A.ideal U * B.ideal U := by simp_all
  have hpow := fun m =>
    congrFun (ideal_pow I m) U
  rw [hmul, derivIdealSheaf_ideal, derivIdealSheaf_ideal, hpow, hpow]
  exact @derivIdeal_pow_succ_le k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) n

theorem le_derivIdealSheaf :
    I ≤ derivIdealSheaf k p I := by
  exact fun U => @le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) $ I.ideal U
end

theorem derivIdealSheaf_mul_le (I J : ISD X) :
    derivIdealSheaf k p (I * J) ≤ I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I := by
  intro U
  have hmul : ∀ A B : ISD X, (A * B).ideal U = A.ideal U * B.ideal U := by simp_all
  have key := @derivIdeal_mul_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
    (I.ideal U) $ J.ideal U
  have h1 : (derivIdealSheaf k p $ I * J).ideal U =
      @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U * J.ideal U) := by
    rw [derivIdealSheaf_ideal, hmul]
  have h2 := sy_ $ derivIdealSheaf_ideal k p I U
  have h3 := (derivIdealSheaf_ideal k p J U).symm
  rw [h1]
  refine key.trans $ sup_le ?_ ?_
  rw [h3, ← hmul]
  exact Scheme.IdealSheafData.le_def.mp le_sup_left U
  rw [h2, ← hmul]
  exact Scheme.IdealSheafData.le_def.mp le_sup_right U

theorem derivIdealSheaf_mono :
    Monotone $ derivIdealSheaf k p := by
  intro I J h
  intro U
  have hU := h U
  rw [derivIdealSheaf_ideal, derivIdealSheaf_ideal]
  exact @derivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) _ _ hU
end
end

noncomputable def derivIdealSheafIterate (k : Type) [CommRing k] [IsNoetherianRing k]
    {X : Sch} (p : X ⟶ Sp k) [LocallyOfFiniteType p] :
    ℕ → ISD X → ISD X
  | 0, I => I
  | (r + 1), I => derivIdealSheaf k p $ derivIdealSheafIterate k p r I

section
variable (k : Type) [CommRing k] [IsNoetherianRing k] {X : Sch} (p) [LocallyOfFiniteType p]
@[simp] theorem derivIdealSheafIterate_zero
    (I : ISD X) : derivIdealSheafIterate k p 0 I = I :=
  rfl

theorem derivIdealSheafIterate_one (I : ISD X) :
    derivIdealSheafIterate k p 1 I = derivIdealSheaf k p I :=
  rfl

section
variable (r : ℕ) (I : ISD X)
theorem derivIdealSheafIterate_succ :
    derivIdealSheafIterate k p (r + 1) I = derivIdealSheaf k p (derivIdealSheafIterate k p r I) :=
  rfl

@[simp] theorem derivIdealSheafIterate_ideal (U : X.affineOpens) :
    (derivIdealSheafIterate k p r I).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) r (I.ideal U) := by
  induction r with
  | zero =>
      rw [derivIdealSheafIterate_zero,
        @derivIdealIterate_zero k _ _ _ (sectionsAlgebra k p U.1) $ I.ideal U]
  | succ n ih =>
      rw [derivIdealSheafIterate_succ, derivIdealSheaf_ideal, ih,
        @derivIdealIterate_succ k _ _ _ (sectionsAlgebra k p U.1) n $ I.ideal U]

theorem le_derivIdealSheafIterate :
    I ≤ derivIdealSheafIterate k p r I := by
  induction r with
  | zero => exact le_rfl
  | succ n ih =>
    rw [derivIdealSheafIterate_succ]
    exact le_trans ih $ le_derivIdealSheaf k p $ derivIdealSheafIterate k p n I
end

theorem derivIdealSheafIterate_add (r s : ℕ) (I : ISD X) :
    derivIdealSheafIterate k p (r + s) I =
      derivIdealSheafIterate k p r (derivIdealSheafIterate k p s I) := by
  induction r with
  | zero => rw [zero_add, derivIdealSheafIterate_zero]
  | succ n ih =>
      rw [add_right_comm, derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih]
end


open TopologicalSpace


variable {X : Sch}

noncomputable def stalkIdeal (I : ISD X) (x : X) : Ideal (X.presheaf.stalk x) :=
  ⨆ U : {U : X.affineOpens // x ∈ U.1.1},
    Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1)

theorem map_germ_ideal_congr {X : Sch} (I : ISD X) (x : X)
    (W W' : X.affineOpens) (h : W = W') (hW : x ∈ W.1) (hW' : x ∈ W'.1) :
    Ideal.map (X.presheaf.germ W.1 x hW).hom (I.ideal W)
      = Ideal.map (X.presheaf.germ W'.1 x hW').hom (I.ideal W') := by
  subst h
  rfl

open CategoryTheory in
theorem map_germ_ideal_affineBasicOpen {X : Sch} (I : ISD X) (x : X)
    (U : X.affineOpens) (f : Γ(X, U.1)) (hxU : x ∈ U.1)
    (hxf : x ∈ (X.affineBasicOpen f).1) :
    Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U)
      = Ideal.map (X.presheaf.germ (X.affineBasicOpen f).1 x hxf).hom
          (I.ideal $ X.affineBasicOpen f) := by
  have hxf' : x ∈ bOpn X f := hxf
  let _a0 := pGerm X (bOpn X f) x hxf'
  have h1 : Ideal.map _a0.hom
      (Ideal.map (pMap X (homOfLE $ X.basicOpen_le f).op).hom $ I.ideal U)
      = Ideal.map (pGerm X U.1 x hxU).hom (I.ideal U) := by
    rw [map_map, ← hom_comp, X.presheaf.germ_res]
  rw [← h1]
  exact congrArg (fun J : Ideal Γ(X, bOpn X f) =>
    Ideal.map _a0.hom J) $ I.map_ideal_basicOpen U f

section
variable {X : Sch}
section
variable (I : ISD X) (x : X)
theorem map_germ_ideal_eq
    (V U : X.affineOpens) (hxV : x ∈ V.1) (hxU : x ∈ U.1) :
    Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V)
      = Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) := by
  obtain ⟨f, g, hfg, hxf⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter V.2 U.2 x ⟨hxV, hxU⟩
  have hxg : x ∈ X.basicOpen g := by rw [← hfg]
                                     exact hxf
  rw [map_germ_ideal_affineBasicOpen I x V f hxV hxf,
    map_germ_ideal_affineBasicOpen I x U g hxU hxg]
  exact map_germ_ideal_congr I x (X.affineBasicOpen f) (X.affineBasicOpen g) (m26 hfg) hxf hxg

theorem map_germ_le_stalkIdeal
    (U : {U : X.affineOpens // x ∈ U.1.1}) :
    Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (I.ideal U.1) ≤ stalkIdeal I x :=
  le_iSup (fun V : {V : affO X // x ∈ V.1.1} =>
    m6 (pGerm X V.1.1 x V.2).hom $ I.ideal V.1) U
end

theorem germ_mem_maximalIdeal_iff_not_mem_basicOpen (x : X) (U : Opn X) (hxU : x ∈ U)
    (f : (X.sec U)) :
    (X.presheaf.germ U x hxU).hom f ∈ maximalIdeal (X.presheaf.stalk x) ↔
      x ∉ X.basicOpen f := by
  have h := AlgebraicGeometry.Scheme.mem_basicOpen X f x hxU
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  simp_all
  simp_all

theorem stalkIdeal_sup_le (I J : ISD X) (x : X) :
    stalkIdeal (I ⊔ J) x ≤ stalkIdeal I x ⊔ stalkIdeal J x := by
  refine iSup_le fun U => ?_
  have h1 : (I ⊔ J).ideal U.1 = I.ideal U.1 ⊔ J.ideal U.1 := rfl
  rw [h1, Ideal.map_sup]
  exact sup_le (le_sup_of_le_left $ map_germ_le_stalkIdeal I x U)
    (le_sup_of_le_right $ map_germ_le_stalkIdeal J x U)

theorem idealSheafData_one_eq_top :
    (1 : ISD X) = ⊤ := rfl
end

section
variable (I : ISD X) (x : X)
section
variable (U : X.affineOpens) (hx : x ∈ U.1)
theorem stalkIdeal_eq_map_germ :
    stalkIdeal I x = Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) := by
  have h : stalkIdeal I x = ⨆ V : {V : affO X // x ∈ V.1.1},
      m6 (pGerm X V.1.1 x V.2).hom (I.ideal V.1) := rfl
  rw [h]
  refine le_antisymm (iSup_le ?_) (le_iSup (fun V : {V : affO X // x ∈ V.1.1} => m6 (pGerm X V.1.1 x V.2).hom (I.ideal V.1)) ⟨U, hx⟩)
  rintro ⟨V, hxV⟩
  exact le_of_eq $ map_germ_ideal_eq I x V U hxV hx

theorem germ_mem_stalkIdeal
    {s : Γ(X, U.1)} (hs : s ∈ I.ideal U) :
    (X.presheaf.germ U.1 x hx).hom s ∈ stalkIdeal I x := by
  exact SetLike.le_def.mp (le_iSup (fun V : {V : affO X // x ∈ V.1.1} => m6 (pGerm X V.1.1 x V.2).hom $ I.ideal V.1) ⟨U, hx⟩) $ mem_map_of_mem _ hs
end

theorem mem_support_iff_stalkIdeal_le_maximalIdeal :
    x ∈ support I ↔ stalkIdeal I x ≤ maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hxU0⟩ := X.exists_affineOpens_mem x
  have hxU := hxU0
  have _i38 : x ∈ spI I ↔ ∀ f ∈ I.ideal U, (pGerm X U.1 x hxU).hom f ∈ maximalIdeal (stkX X x) := by
    rw [mem_support_iff_of_mem (I := I) (U := U) hxU,
      mem_zeroLocus_iff]
    constructor
    intro h f hf
    exact mpr_ (germ_mem_maximalIdeal_iff_not_mem_basicOpen x U.1 hxU f) $ h f hf
    intro h f hf
    exact mp_ (germ_mem_maximalIdeal_iff_not_mem_basicOpen x U.1 hxU f) $ h f hf
  rw [stalkIdeal_eq_map_germ I x U hxU, map_le_iff_le_comap,
    _i38]
  constructor
  intro h f hf
  exact h f hf
  intro h f hf
  exact h hf

theorem mem_support_iff_stalkIdeal_ne_top :
    x ∈ support I ↔ stalkIdeal I x ≠ ⊤ := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal]
  refine ⟨fun h htop => ?_, le_maximalIdeal⟩
  rw [htop, top_le_iff] at h
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top h

noncomputable def orderAt : ℕ∞ :=
  idealOrder $ stalkIdeal I x

theorem le_orderAt_iff (n : ℕ) :
    (n : ENat) ≤ orderAt I x ↔
      stalkIdeal I x ≤ maximalIdeal (X.presheaf.stalk x) ^ n :=
  le_idealOrder_iff (stalkIdeal I x) n

theorem orderAt_eq_idealOrder :
    orderAt I x = idealOrder (stalkIdeal I x) := rfl

theorem one_le_orderAt_iff_mem_support :
    1 ≤ orderAt I x ↔ x ∈ support I := by
  rw [orderAt_eq_idealOrder, one_le_idealOrder_iff, mem_support_iff_stalkIdeal_le_maximalIdeal]

theorem orderAt_eq_zero_iff_not_mem_support :
    orderAt I x = 0 ↔ x ∉ support I := by
  rw [orderAt_eq_idealOrder, idealOrder_eq_zero_iff,
    mem_support_iff_stalkIdeal_le_maximalIdeal]

theorem orderAt_eq_one_iff :
    orderAt I x = 1 ↔
      stalkIdeal I x ≤ maximalIdeal (X.presheaf.stalk x) ∧
        ¬ stalkIdeal I x ≤ maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  constructor
  intro h
  constructor
  have ha : ((1 : ℕ) : ENat) ≤ orderAt I x := by rw [h]
                                                 simp
  simpa using (le_orderAt_iff I x 1).mp ha
  intro hle
  have h2 := mpr_ (le_orderAt_iff I x 2) hle
  rw [h] at h2
  have h3 : 2 ≤ 1 := by exact_mod_cast h2
  omega
  rintro ⟨ha, hb⟩
  have ha' := mpr_ (le_orderAt_iff I x 1) $ by simpa using ha
  have hb' := fun hc => hb $ mp_ (le_orderAt_iff I x 2) hc
  rcases eq_or_ne (orderAt I x) ⊤ with htop | hfin
  exact absurd (htop ▸ le_top) hb'
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn] at ha' hb' ⊢
  have hn1 : 1 ≤ n := by exact_mod_cast ha'
  have hn2 : ¬ (2 ≤ n) := fun hc => hb' $ by exact_mod_cast hc
  have hn3 : n = 1 := by omega
  rw [hn3, cast_one]
end

section
variable {R : Type} [CommRing R]
theorem maximalIdeal_not_le_sq [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≠ ⊥) :
    ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := by
  intro hle
  refine h $ eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R)
      (maximalIdeal R) (m187 _) ?_ $ (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  rwa [Ideal.smul_eq_mul, ← pow_two]

theorem mem_of_vanishingIdeal_le
    (W : Set $ PrimeSpectrum R) (hW : IsClosed W) (q : PrimeSpectrum R)
    (h : PrimeSpectrum.vanishingIdeal W ≤ asIdeal q) : q ∈ W := by
  have h0 :=
    mpr (mem_zeroLocus _ _) fun y hy => h hy
  rwa [zeroLocus_vanishingIdeal_eq_closure, hW.closure_eq] at h0
end

section
variable {I J : ISD X}
section
variable (h : I ≤ J) (x : X)
include h
theorem stalkIdeal_mono :
    stalkIdeal I x ≤ stalkIdeal J x := by
  exact iSup_mono fun U => map_mono $ h U.1

theorem orderAt_le_of_le :
    orderAt J x ≤ orderAt I x :=
  idealOrder_le_of_le $ stalkIdeal_mono h x
end

theorem orderAt_eq_of_stalkIdeal_eq {x : X}
    (h : stalkIdeal I x = stalkIdeal J x) : orderAt I x = orderAt J x := by
  rw [orderAt_eq_idealOrder, orderAt_eq_idealOrder, h]
end

section
variable (I J : ISD X) (x : X)
theorem stalkIdeal_sup :
    stalkIdeal (I ⊔ J) x = stalkIdeal I x ⊔ stalkIdeal J x :=
  le_antisymm (stalkIdeal_sup_le I J x)
    (sup_le (stalkIdeal_mono le_sup_left x) $ stalkIdeal_mono le_sup_right x)

theorem stalkIdeal_mul :
    stalkIdeal (I * J) x = stalkIdeal I x * stalkIdeal J x := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hmul : (I * J).ideal U = I.ideal U * J.ideal U :=
    congrFun (ideal_mul ..) U
  rw [stalkIdeal_eq_map_germ (I * J) x U hxU, stalkIdeal_eq_map_germ I x U hxU,
    stalkIdeal_eq_map_germ J x U hxU, hmul, m220]

theorem orderAt_sup :
    orderAt (I ⊔ J) x = min (orderAt I x) (orderAt J x) := by
  rw [orderAt_eq_idealOrder, stalkIdeal_sup, idealOrder_sup]
  rfl

theorem add_orderAt_le_orderAt_mul :
    orderAt I x + orderAt J x ≤ orderAt (I * J) x := by
  rw [orderAt_eq_idealOrder $ I * J, stalkIdeal_mul]
  exact add_idealOrder_le_idealOrder_mul (stalkIdeal I x) $ stalkIdeal J x
end

section
variable {R S : Type} [CommRing R] [CommRing S]
theorem map_algebraMap_eq_maximalIdeal
    [Algebra R S] [IsLocalRing S] (p : Ideal R) [p.IsPrime] [IsLocalization p.primeCompl S]
    (J : Ideal R) (hJ : J.IsRadical) (hJp : J ≤ p)
    (hmin : ∀ q : Ideal R, q.IsPrime → J ≤ q → q ≤ p → q = p) :
    Ideal.map (algebraMap R S) J = maximalIdeal S := by
  let _a0 := algebraMap R S
  have hmap : m6 _a0 p = maximalIdeal S :=
    IsLocalization.AtPrime.map_eq_maximalIdeal ..
  have hcomap_le : comap _a0 (maximalIdeal S) ≤ p := by
    intro r hr
    by_contra hrp
    rw [mem_comap] at hr
    have hrp' : r ∈ p.primeCompl := hrp
    have hunit := map_units S ⟨r, hrp'⟩
    have hnu := mp_ (mem_maximalIdeal _) hr
    rw [mem_nonunits_iff] at hnu
    exact hnu hunit
  refine le_antisymm (le_trans (map_mono hJp) $ le_of_eq hmap) ?_
  have hle : maximalIdeal S ≤ (m6 _a0 J).radical := by
    rw [radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hPle, hPprime⟩
    have : P.IsPrime := hPprime
    have hPmax := le_maximalIdeal hPprime.ne_top
    have h1 : comap _a0 P = p := by
      refine hmin _ (comap_isPrime _a0 P) ?_ $ le_trans (comap_mono hPmax) hcomap_le
      rwa [← map_le_iff_le_comap]
    have heq : maximalIdeal S = P := by
      rw [← hmap, ← h1]
      exact map_under p.primeCompl S P
    exact heq.le
  refine hle.trans ?_
  rw [← map_radical p.primeCompl S J]
  exact map_mono hJ

section
variable [IsLocalRing R] [hv3_1 : IsLocalRing S] (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x)
include hv3_1 hgf hfg
theorem map_maximalIdeal_of_inverse :
    Ideal.map f (maximalIdeal R) = maximalIdeal S := by
  refine le_antisymm ?_ ?_
  rw [map_le_iff_le_comap]
  intro x hx
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hx
  have h2 := hu.map g
  rwa [hgf] at h2
  intro z hz
  rw [mem_maximalIdeal, mem_nonunits_iff] at hz
  have hgz : g z ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hz
    have h2 := hu.map f
    rwa [hfg] at h2
  have h3 : f (g z) ∈ m6 f (maximalIdeal R) := mem_map_of_mem _ hgz
  rwa [hfg] at h3

theorem idealOrder_map_of_inverse (J : Ideal R) :
    idealOrder (Ideal.map f J) = idealOrder J := by
  have hf := map_maximalIdeal_of_inverse f g hgf hfg
  have hg := map_maximalIdeal_of_inverse g f hfg hgf
  have hcomp : g.comp f = m99 R := m48 hgf
  let _a0 := Ideal.map f J
  have h2 : Ideal.map g _a0 = J := by
    rw [map_map, hcomp, map_id]
  have h3 :=
    idealOrder_le_idealOrder_map g hg.le _a0
  rw [h2] at h3
  exact le_antisymm h3 $ idealOrder_le_idealOrder_map f hf.le J
end
end

section
variable (x : X)
theorem stalkIdeal_top : stalkIdeal (⊤ : ISD X) x = ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have h1 : (1 : Γ(X, U.1)) ∈ (⊤ : ISD X).ideal U := by simp
  have h2 := mem_map_of_mem (pGerm X U.1 x hxU).hom h1
  rw [map_one] at h2
  exact mpr_ (eq_top_iff_one _) $ SetLike.le_def.mp (le_iSup (fun V : {V : affO X // x ∈ V.1.1} => m6 (pGerm X V.1.1 x V.2).hom $ (⊤ : ISD X).ideal V.1) ⟨U, hxU⟩) h2

theorem stalkIdeal_bot : stalkIdeal (⊥ : ISD X) x = ⊥ := by
  have h : ∀ U, (⊥ : ISD X).ideal U = ⊥ := fun U => by simp
  simp [stalkIdeal, h, Ideal.map_bot, iSup_bot]

theorem orderAt_top : orderAt (⊤ : ISD X) x = 0 := by
  rw [orderAt_eq_idealOrder, stalkIdeal_top, idealOrder_top]

theorem orderAt_bot : orderAt (⊥ : ISD X) x = ⊤ := by
  rw [orderAt_eq_idealOrder, stalkIdeal_bot, idealOrder_bot]
end

section
variable [hv0_0 : IsLocallyNoetherian X] (I : ISD X) (x : X)
include hv0_0
theorem orderAt_ne_top_of_stalkIdeal_ne_bot (h : stalkIdeal I x ≠ ⊥) : orderAt I x ≠ ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hxU' := hxU
  have hnoeth := m188 U
  let germAlgebra :=
    (pGerm X U.1 x hxU').hom.toAlgebra
  have hloc := U.2.isLocalization_stalk ⟨x, hxU'⟩
  have : IsNoetherianRing $ stkX X x :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl _ hnoeth
  rw [orderAt_eq_idealOrder]
  exact idealOrder_ne_top_of_ne_bot h

theorem orderAt_eq_top_iff :
    orderAt I x = ⊤ ↔ stalkIdeal I x = ⊥ := by
  constructor
  intro h
  by_contra hne
  exact orderAt_ne_top_of_stalkIdeal_ne_bot I x hne h
  intro h
  rw [orderAt_eq_idealOrder, h, idealOrder_bot]
end

theorem stalkIdeal_pow (I : ISD X) (n : ℕ) (x : X) :
    stalkIdeal (I ^ n) x = stalkIdeal I x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, idealSheafData_one_eq_top, stalkIdeal_top, one_eq_top]
  | succ n ih =>
    rw [pow_succ, pow_succ, stalkIdeal_mul, ih]

section
variable [IsLocallyNoetherian X] (Z : Closeds X) (xi_) (T) (hT : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (Z : Set X)) T) (hxi_ : IsGenericPoint xi_ T)
include hT hxi_
theorem orderAt_vanishingIdeal_eq_one
    (hne : maximalIdeal (X.presheaf.stalk xi_) ≠ ⊥) :
    orderAt (vanishingIdeal Z) xi_ = 1 :=
  by
    let x := xi_
    let h : stalkIdeal (vanishingIdeal Z) xi_ = maximalIdeal (stkX X xi_) := by
      obtain ⟨U, hxU0⟩ := X.exists_affineOpens_mem xi_
      have hxU := hxU0
      have hU : IsAffineOpen U.1 := U.2
      have hZcl := Z.2
      have hcont := (hU.fromSpec).continuous
      have hxiT : xi_ ∈ T := by
        rw [← hxi_]
        exact subset_closure $ mem_singleton xi_
      have hxiZ_ := hT.1.2 hxiT
      have hJdef : (vanishingIdeal Z).ideal U
          = m184 (preimage hU.fromSpec Z) := rfl
      have hfp : (hU.fromSpec) (hU.primeIdealOf ⟨xi_, hxU⟩) = xi_ :=
        hU.fromSpec_primeIdealOf ⟨xi_, hxU⟩
      have hmemW : hU.primeIdealOf ⟨xi_, hxU⟩ ∈ (preimage (hU.fromSpec) Z) := by
        show (hU.fromSpec) (hU.primeIdealOf ⟨xi_, hxU⟩) ∈ Z
        rwa [hfp]
      rw [stalkIdeal_eq_map_germ _ xi_ U hxU, hJdef]
      let _a2 := pGerm X U.1 xi_ hxU
      let germAlgebra :=
        _a2.hom.toAlgebra
      have hloc := hU.isLocalization_stalk ⟨xi_, hxU⟩
      have halg : _a2.hom
          = algebraMap Γ(X, U.1) (stkX X xi_) := rfl
      rw [halg]
      refine map_algebraMap_eq_maximalIdeal (hU.primeIdealOf ⟨xi_, hxU⟩).asIdeal _
        (isRadical_vanishingIdeal _) ?_ ?_
      intro f hf
      exact mp_ (mem_vanishingIdeal _ _) hf _ hmemW
      intro q hq hJq hqp
      let _s0 := (⟨q, hq⟩ : PrimeSpectrum Γ(X, U.1))
      have hQP : _s0 ⤳ hU.primeIdealOf ⟨xi_, hxU⟩ := by
        rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton,
          PrimeSpectrum.mem_zeroLocus]
        exact fun y hy => hqp hy
      have hzspec : (hU.fromSpec) _s0 ⤳ xi_ := by
        have hmapped := hQP.map hcont
        rwa [hfp] at hmapped
      have hzZ := mem_of_vanishingIdeal_le _ (hZcl.preimage hcont) ⟨q, hq⟩ hJq
      have hirr : IsIrreducible
          (closure {(hU.fromSpec) _s0}) :=
        isIrreducible_singleton.closure
      have hTsub : T ⊆ closure {(hU.fromSpec) _s0} := by
        rw [← hxi_]
        exact closure_minimal
          (mpr_ singleton_subset_iff $ mp_ specializes_iff_mem_closure hzspec) isClosed_closure
      have hmax := hT.2 ⟨hirr, hZcl.closure_subset_iff.mpr $ mpr_ singleton_subset_iff hzZ⟩ hTsub
      have hxiz : xi_ ⤳ (hU.fromSpec) _s0 :=
        mpr specializes_iff_mem_closure (by rw [hxi_]; exact hmax $ subset_closure $ mem_singleton _)
      have h3 := hxiz
      rw [← hfp] at h3
      have hPQ : hU.primeIdealOf ⟨xi_, hxU⟩ ⤳ _s0 :=
        ((hU.fromSpec).isOpenEmbedding.toIsEmbedding.toIsInducing).specializes_iff.mp h3
      have hpq : asIdeal (hU.primeIdealOf ⟨xi_, hxU⟩) ≤ q := by
        have h2 := mp_ specializes_iff_mem_closure hPQ
        rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus] at h2
        exact fun y hy => h2 hy
      exact le_antisymm hqp hpq
    obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
    have hxU' := hxU
    have hnoeth := m188 U
    let germAlgebra :=
      (pGerm X U.1 x hxU').hom.toAlgebra
    have hloc := U.2.isLocalization_stalk ⟨x, hxU'⟩
    have : IsNoetherianRing $ stkX X x :=
      IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl _ hnoeth
    rw [orderAt_eq_one_iff]
    refine ⟨h.le, ?_⟩
    rw [h]
    exact maximalIdeal_not_le_sq hne

theorem orderAt_vanishingIdeal_eq_one_of_not_isField
    (hfield : ¬ IsField (X.presheaf.stalk xi_)) :
    orderAt (vanishingIdeal Z) xi_ = 1 :=
  orderAt_vanishingIdeal_eq_one Z xi_ T hT hxi_ fun hb => hfield $ mpr_ isField_iff_maximalIdeal_eq hb
end

open CategoryTheory in
theorem hom_hom_apply_of_comp_eq {A B C : CRC} (f : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (hk : f ≫ g = k) (x : A) : g.hom (f.hom x) = k.hom x := by
  rw [← hk, hom_comp]
  rfl

open CategoryTheory in
theorem orderAt_comap_of_isOpenImmersion {Y : Sch} (h : Y ⟶ X) [IsOpenImmersion h]
    (I : ISD X) (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  obtain ⟨U, sectionFrameQuotient⟩ := Y.exists_affineOpens_mem y
  have hyU := sectionFrameQuotient
  have hVaff := U.2.image_of_isOpenImmersion h
  have hxV : h.base y ∈ (imU h U.1) := ⟨y, hyU, rfl⟩
  let _a1 := h.appIso U.1
  have hid : (cmI I h).ideal U
      = m6 (_a1.hom).hom (I.ideal ⟨imU h U.1, hVaff⟩) := by
    rw [ideal_comap_of_isOpenImmersion I h U]
    exact comap_symm _a1.commRingCatIsoToRingEquiv ..
  let _a0 := h.app (h ''ᵁ U.1) ≫ pGerm Y (h ⁻¹ᵁ h ''ᵁ U.1) y hxV
  have key : inv _a1 ≫
        _a0
      = pGerm Y U.1 y hyU := by
    rw [← assoc, appIso_inv_app]
    exact Y.presheaf.germ_res _ y hxV
  let _a2 := pGerm X (imU h U.1) (h.base y) hxV
  have hcat : _a1.hom ≫ pGerm Y U.1 y hyU
      = _a2 ≫ h.stalkMap y := by
    calc _a1.hom ≫ pGerm Y U.1 y hyU
        = _a1.hom ≫ (inv _a1 ≫
            _a0) := by rw [key]
      _ = _a0 := by
          rw [← assoc, hom_inv_id, id_comp]
      _ = _a2 ≫ h.stalkMap y :=
          (germ_stalkMap h (imU h U.1) y hxV).symm
  let _a4 := (h.stalkMap y).hom
  have hcomp : (pGerm Y U.1 y hyU).hom.comp (_a1.hom).hom
      = _a4.comp _a2.hom := by
    have h4 := congrArg hom hcat
    rwa [hom_comp, hom_comp] at h4
  let _a3 := inv $ h.stalkMap y
  have hsgf : ∀ x, (_a3.hom) ((h.stalkMap y).hom x) = x := fun x => by
    rw [hom_hom_apply_of_comp_eq _ _ _ (m118 $ h.stalkMap y) x, hom_id]
    rfl
  have hsfg : ∀ x, _a4 (_a3.hom x) = x := fun x => by
    rw [hom_hom_apply_of_comp_eq _ _ _ (m117 $ h.stalkMap y) x, hom_id]
    rfl
  rw [orderAt_eq_idealOrder, orderAt_eq_idealOrder,
    stalkIdeal_eq_map_germ (cmI I h) y U hyU,
    stalkIdeal_eq_map_germ I (h.base y) ⟨imU h U.1, hVaff⟩ hxV, hid, map_map, hcomp,
    ← map_map]
  exact idealOrder_map_of_inverse (h.stalkMap y).hom _a3.hom hsgf hsfg _

open CategoryTheory in
theorem orderAt_comap_of_isIso {A B : Sch} (f : A ⟶ B) [IsIso f] (J : ISD B)
    (x : ↥A) : orderAt (J.comap f) x = orderAt J (f.base x) :=
  orderAt_comap_of_isOpenImmersion f J x

section
variable (I : ISD X)
section
variable (m : ℕ)
noncomputable def orderAtLeastLocus : Set X :=
  {x : X | (m : ENat) ≤ orderAt I x}

theorem mem_orderAtLeastLocus_iff (x : X) :
    x ∈ orderAtLeastLocus I m ↔ (m : ENat) ≤ orderAt I x := m22

theorem mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow
    (x : X) :
    x ∈ orderAtLeastLocus I m ↔
      stalkIdeal I x ≤ maximalIdeal (X.presheaf.stalk x) ^ m := by
  rw [mem_orderAtLeastLocus_iff, le_orderAt_iff]
end

theorem orderAtLeastLocus_subset_of_le {m m' : ℕ} (h : m ≤ m') :
    orderAtLeastLocus I m' ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  refine le_trans ?_ hx
  exact_mod_cast h

theorem mem_orderAtLeastLocus_one_iff (x : X) :
    x ∈ orderAtLeastLocus I 1 ↔ x ∈ support I := by
  rw [mem_orderAtLeastLocus_iff, cast_one, one_le_orderAt_iff_mem_support]

theorem orderAtLeastLocus_subset_orderAtLeastLocus_pow (c m : ℕ) :
    orderAtLeastLocus I m ⊆ orderAtLeastLocus (I ^ c) (c * m) := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  let _a0 := I ^ c
  calc ((c * m) : ENat) = c * m := by push_cast
                                      ring
    _ ≤ c * orderAt I x := by gcongr
    _ ≤ orderAt _a0 x := by
      rw [orderAt_eq_idealOrder _a0, stalkIdeal_pow]
      exact mul_idealOrder_le_idealOrder_pow (stalkIdeal I x) c

theorem orderAtLeastLocus_zero : orderAtLeastLocus I 0 = univ := by
  ext x
  simp [mem_orderAtLeastLocus_iff]

end

theorem orderAtLeastLocus_subset_of_le_ideal {I J : ISD X} (h : I ≤ J) (m : ℕ) :
    orderAtLeastLocus J m ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  exact le_trans hx $ orderAt_le_of_le h x

theorem inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul (I J : ISD X) (m m' : ℕ) :
    orderAtLeastLocus I m ∩ orderAtLeastLocus J m' ⊆ orderAtLeastLocus (I * J) (m + m') := by
  rintro x ⟨hx, hx'⟩
  rw [mem_orderAtLeastLocus_iff] at hx hx' ⊢
  calc ((m + m') : ENat) = m + m' := by push_cast
                                        ring
    _ ≤ orderAt I x + orderAt J x := add_le_add hx hx'
    _ ≤ orderAt (I * J) x := add_orderAt_le_orderAt_mul I J x

theorem orderAtLeastLocus_top_eq_empty (m : ℕ) (hm : 1 ≤ m) :
    orderAtLeastLocus (⊤ : ISD X) m = ∅ := by
  ext x
  simp only [mem_orderAtLeastLocus_iff, mem_empty_iff_false, iff_false, not_le, orderAt_top]
  exact_mod_cast hm

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

section
variable (k : Type)
section
variable [CommRing k]
section
variable {X : Sch} (p : X ⟶ Sp k)
section
variable (x : X)
noncomputable def stalkAlgebraMap : k →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x $ Opens.mem_top x).hom.comp $ sectionsAlgebraMap k p ⊤

@[reducible] noncomputable def stalkAlgebra : Algebra k $ X.presheaf.stalk x :=
  (stalkAlgebraMap k p x).toAlgebra

theorem algebraMap_stalkAlgebra :
    @algebraMap k (X.presheaf.stalk x) _ _ (stalkAlgebra k p x) = stalkAlgebraMap k p x :=
  rfl
end

section
variable (U : Opn X) (x : X) (hx : x ∈ U)
theorem sectionsAlgebraMap_comp_germ :
    (X.presheaf.germ U x hx).hom.comp (sectionsAlgebraMap k p U) = stalkAlgebraMap k p x := by
  have hle : U ≤ (⊤) := le_top
  have key : pMap X (homOfLE hle).op ≫ pGerm X U x hx
      = pGerm X (⊤) x (Opens.mem_top x) := by
    simp
  have key' : (pGerm X U x hx).hom.comp (pMap X (homOfLE hle).op).hom
      = (pGerm X (⊤) x $ Opens.mem_top x).hom := by
    rw [← hom_comp, key]
  show (pGerm X U x hx).hom.comp (sectionsAlgebraMap k p U)
      = (pGerm X (⊤) x $ Opens.mem_top x).hom.comp (sectionsAlgebraMap k p ⊤)
  rw [← key', comp_assoc, sectionsAlgebraMap_comp_restrict k p hle]

theorem isScalarTower_stalk
    [Algebra k $ X.sec U] [Algebra k $ X.presheaf.stalk x] [Algebra (X.sec U) $ X.presheaf.stalk x]
    (hU : algebraMap k (X.sec U) = sectionsAlgebraMap k p U)
    (hstalk : algebraMap k (X.presheaf.stalk x) = stalkAlgebraMap k p x)
    (hgerm : algebraMap (X.sec U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom) :
    IsScalarTower k (X.sec U) $ X.presheaf.stalk x := by
  refine of_algebraMap_eq' ?_
  rw [hstalk, hgerm, hU, sectionsAlgebraMap_comp_germ]

theorem germ_sectionsAlgebraMap_apply (a : k) :
    (X.presheaf.germ U x hx).hom (sectionsAlgebraMap k p U a) = stalkAlgebraMap k p x a :=
  congr_fun (sectionsAlgebraMap_comp_germ k p U x hx) a
end
end

section
variable [IsNoetherianRing k] {X : Sch} (p) [LocallyOfFiniteType p]
theorem stalkIdeal_derivIdealSheaf
    (I : ISD X) (x : X) :
    stalkIdeal (derivIdealSheaf k p I) x =
      @derivIdeal k _ _ _ (stalkAlgebra k p x) (stalkIdeal I x) := by
  let _a0 := derivIdealSheaf k p I
  rcases isEmpty_or_nonempty {U : affO X // x ∈ U.1.1} with hE | ⟨⟨U, hx⟩⟩
  have h1 : ∀ J : ISD X, stalkIdeal J x = ⊥ := fun J =>
    iSup_of_empty fun U : {U : affO X // x ∈ U.1.1} =>
      m6 (pGerm X U.1.1 x U.2).hom $ J.ideal U.1
  rw [h1 _a0, h1 I]
  exact sy_ $ @derivIdeal_bot k _ _ _ $ stalkAlgebra k p x
  have hU := U.2
  let algk := sectionsAlgebra k p U.1
  let algst := stalkAlgebra k p x
  let algS :=
    (pGerm X U.1 x hx).hom.toAlgebra
  have :=
    isScalarTower_stalk k p U.1 x hx rfl rfl rfl
  have :=
    finitePresentation_kaehlerDifferential_sections k p U rfl
  have _hloc := hU.isLocalization_stalk ⟨x, hx⟩
  rw [stalkIdeal_eq_map_germ _a0 x U hx,
    stalkIdeal_eq_map_germ I x U hx, derivIdealSheaf_ideal]
  exact map_derivIdeal (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl $ I.ideal U

theorem stalkIdeal_derivIdealSheafIterate (r : ℕ)
    (I : ISD X) (x : X) :
    stalkIdeal (derivIdealSheafIterate k p r I) x =
      @derivIdealIterate k _ _ _ (stalkAlgebra k p x) r (stalkIdeal I x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have h := stalkIdeal_derivIdealSheaf k p (derivIdealSheafIterate k p r I) x
      rw [derivIdealSheafIterate_succ, h, ih, derivIdealIterate_succ]

theorem le_orderAt_derivIdealSheafIterate
    (I : ISD X) (x : X) (n r : ℕ) (h : ((n + r : ℕ) : ENat) ≤ orderAt I x) :
    (n : ENat) ≤ orderAt (derivIdealSheafIterate k p r I) x := by
  rw [le_orderAt_iff] at h ⊢
  rw [stalkIdeal_derivIdealSheafIterate k p r I x]
  have key := @derivIdealIterate_le_pow_of_le_pow k _ _ _ (stalkAlgebra k p x)
    (stalkIdeal I x) (maximalIdeal $ stkX X x) (n + r) r h
  rwa [add_sub_cancel] at key

theorem orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate (I : ISD X) (r m : ℕ) :
    orderAtLeastLocus I m ⊆ orderAtLeastLocus (derivIdealSheafIterate k p r I) (m - r) := by
  rcases m63 m r with h | h
  rw [sub_eq_zero_of_le $ le_of_lt h, orderAtLeastLocus_zero]
  exact subset_univ _
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  refine le_orderAt_derivIdealSheafIterate k p I x (m - r) r ?_
  rwa [sub_add_cancel h]
end

theorem formallySmooth_of_ringEquiv (R : Type)
    [CommRing R] [Algebra k R] (e : k ≃+* R) (he : ∀ x : k, e x = algebraMap k R x) :
    FormallySmooth k R := by
  have : FormallySmooth k k := inferInstance
  exact of_equiv $ AlgEquiv.ofRingEquiv (f := e) he
end

section
variable [Field k]
section
variable [CharZero k]
section
variable (L : Type) [Field L] [Algebra k L]
theorem formallySmooth_of_isTranscendenceBasis {ι : Type} {x : ι → L}
    (hx : IsTranscendenceBasis k x) : FormallySmooth k L := by
  have hai := an1 hx
  have _fsA :=
    of_equiv hai.aevalEquiv
  have _halg := hx.isAlgebraic
  let _a0 := adjoin k $ range x
  have _hdom : IsDomain _a0 := inferInstance
  let A0_ := _a0
  let hinj : Injective $ algebraMap _a0 L := fun a b h => m26 h
  have hunit : ∀ y : nonZeroDivisors A0_, IsUnit $ algebraMap A0_ L y := by
    intro y
    refine mpr_ isUnit_iff_ne_zero fun hy => ?_
    have h0 : (y : A0_) = 0 := hinj $ by rw [hy, map_zero]
    exact nonZeroDivisors.coe_ne_zero y h0
  let algFL : Algebra (FractionRing A0_) L := (IsLocalization.lift hunit).toAlgebra
  have _twr1 : IsScalarTower k A0_ $ FractionRing A0_ := inferInstance
  have _twr2 : IsScalarTower A0_ (FractionRing A0_) L :=
    of_algebraMap_eq fun a => sy_ $ lift_eq hunit a
  have _twr3 : IsScalarTower k (FractionRing A0_) L := by
    refine of_algebraMap_eq fun c => ?_
    rw [IsScalarTower.algebraMap_apply k A0_ (FractionRing A0_) c,
      ← IsScalarTower.algebraMap_apply A0_ (FractionRing A0_) L,
      ← IsScalarTower.algebraMap_apply k A0_ L]
  have _fs1 : FormallySmooth A0_ $ FractionRing A0_ :=
    of_isLocalization $ nonZeroDivisors A0_
  have _fs2 :=
    m139 k A0_ $ FractionRing A0_
  have _hchar :=
    charZero_of_injective_algebraMap $ RingHom.injective $ algebraMap k $ FractionRing A0_
  have _halgF : Algebra.IsAlgebraic (FractionRing A0_) L := by
    refine ⟨fun a => ?_⟩
    obtain ⟨q, hq0, hqa⟩ := (Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic A0_ a)
    refine ⟨q.map $ algebraMap A0_ $ FractionRing A0_, mpr_ (map_ne_zero_iff $ IsFractionRing.injective A0_ $ FractionRing A0_) hq0, ?_⟩
    rwa [Polynomial.aeval_map_algebraMap]
  have _hsep : IsSeparable (FractionRing A0_) L := by
    exact ⟨fun a => (minpoly.irreducible $ (Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic (FractionRing A0_) a).isIntegral).separable⟩
  have _fet : FormallyEtale (FractionRing A0_) L :=
    Algebra.FormallyEtale.of_isSeparable ..
  have _fs3 : FormallySmooth (FractionRing A0_) L := inferInstance
  exact m139 k (FractionRing A0_) L
end

section
variable {X : Sch} (p : X ⟶ Sp k)
include p
theorem isUnit_natCast_stalk (x : X) {n : ℕ} (hn : 1 ≤ n) :
    IsUnit ((n : ℕ) : X.presheaf.stalk x) := by
  have hne : (n : k) ≠ 0 := mpr_ cast_ne_zero $ by omega
  have hk := IsUnit.mk0 _ hne
  have h := hk.map $ stalkAlgebraMap k p x
  rwa [map_natCast] at h

theorem formallySmooth_residueField [Smooth p] (x : X)
    [Algebra k $ ResidueField $ X.presheaf.stalk x]
    (_h : algebraMap k (ResidueField $ X.presheaf.stalk x) =
      (residue $ X.presheaf.stalk x).comp (stalkAlgebraMap k p x)) :
    FormallySmooth k $ ResidueField $ X.presheaf.stalk x :=
  by
  let L := ResidueField $ stkX X x
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k L
  exact formallySmooth_of_isTranscendenceBasis k L hB
end
end

section
variable {X : Sch} (p : X ⟶ Sp k) [Smooth p]
include p
section
variable (U) (hU : IsAffineOpen U)
include hU
theorem formallySmooth_sections [Algebra k (X.sec U)]
    (h : algebraMap k (X.sec U) = sectionsAlgebraMap k p U) :
    FormallySmooth k $ X.sec U := by
  let _a1 := le_preimage_top k p U
  let algSections :=
    (appLE p ⊤ U _a1).hom.toAlgebra
  have hS := mp (smooth_iff p) ‹Smooth p› (isAffineOpen_top $ Sp k) hU _a1
  have : FormallySmooth Γ(Sp k, ⊤) U.sec := hS.formallySmooth
  let _a0 := GSpecIso $ m10 k
  let algGlobal :=
    _a0.inv.hom.toAlgebra
  have : FormallySmooth k Γ(Sp k, ⊤) :=
    formallySmooth_of_ringEquiv k Γ(Sp k, ⊤)
      _a0.symm.commRingCatIsoToRingEquiv fun _ => rfl
  have : IsScalarTower k Γ(Sp k, ⊤) U.sec :=
    of_algebraMap_eq' $ tr_ h rfl
  exact m139 k Γ(Sp k, ⊤) U.sec

theorem isNoetherianRing_sections_of_smooth : IsNoetherianRing $ X.sec U := by
  have : IsNoetherianRing k := inferInstance
  let _a0 := le_preimage_top k p U
  let algSections :=
    (appLE p ⊤ U _a0).hom.toAlgebra
  have hS := mp (smooth_iff p) ‹Smooth p› (isAffineOpen_top $ Sp k) hU _a0
  have e :=
    (GSpecIso $ m10 k).symm.commRingCatIsoToRingEquiv
  let _a1 := Γ(Sp k, ⊤)
  have :=
    isNoetherianRing_of_surjective k (_a1) e.toRingHom e.surjective
  obtain ⟨n, f, hf, -⟩ := hS.finitePresentation
  exact isNoetherianRing_of_surjective
    (MvPolynomial (Fin n) (_a1)) (U.sec) f.toRingHom hf
end

theorem isNoetherianRing_stalk (x : X) :
    IsNoetherianRing $ X.presheaf.stalk x := by
  have : IsLocallyNoetherian X := ⟨fun U => isNoetherianRing_sections_of_smooth k p U.1 U.2⟩
  infer_instance
end
end
end

theorem finite_kaehlerDifferential_of_isLocalization (k A B : Type) [CommRing k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (M : Submonoid A) [IsLocalization M B]
    (hfin : Module.Finite A $ KaehlerDifferential k A) :
    Module.Finite B $ KaehlerDifferential k B := by
  let _a0 := m132 k k A B
  have : IsLocalizedModule M _a0 := inferInstance
  have : Module.Finite B $ TensorProduct A B $ KaehlerDifferential k A := inferInstance
  exact Module.Finite.equiv (IsLocalizedModule.isBaseChange M B _a0).equiv

theorem eq_top_or_exists_eq_natCast (a : ENat) : a = ⊤ ∨ ∃ n : ℕ, a = (n : ENat) := by
  rcases eq_or_ne a ⊤ with h | h
  exact m51 h
  exact m61 ⟨a.toNat, sy_ $ ENat.natCast_toNat h⟩

theorem exists_isAffineOpen_mem__b47 (X : Sch) (x : X) :
    ∃ U : Opn X, x ∈ U ∧ IsAffineOpen U :=
  ⟨(X.affineCover.f $ X.affineCover.idx x).opensRange, X.affineCover.covers x,
    isAffineOpen_opensRange _⟩

section
variable (k : Type) [Field k]
section
variable {X : Sch} (p) [Smooth p] (x : X)
include p x
theorem formallySmooth_stalk :
    @FormallySmooth k _ _ _ $ stalkAlgebra k p x := by
  obtain ⟨U, hxU, hU⟩ := exists_isAffineOpen_mem__b47 X x
  let algU := sectionsAlgebra k p U
  let algStalk := stalkAlgebra k p x
  let algGerm := (pGerm X U x hxU).hom.toAlgebra
  have _tower :=
    isScalarTower_stalk k p U x hxU rfl rfl rfl
  have _fsU := formallySmooth_sections k p U hU rfl
  have _loc := hU.isLocalization_stalk ⟨x, hxU⟩
  have _fsStalk : FormallySmooth U.sec $ stkX X x :=
    of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact m139 k U.sec $ stkX X x

theorem finite_kaehlerDifferential_stalk :
    letI := stalkAlgebra k p x
    Module.Finite (stkX X x) $ KaehlerDifferential k $ stkX X x := by
  let algStalk := stalkAlgebra k p x
  obtain ⟨U, hxU, hUaff⟩ := exists_isAffineOpen_mem__b47 X x
  let algSections := sectionsAlgebra k p U
  let algGerm := (pGerm X U x hxU).hom.toAlgebra
  have :=
    isScalarTower_stalk k p U x hxU rfl rfl rfl
  have := hUaff.isLocalization_stalk ⟨x, hxU⟩
  have :=
    finitePresentation_kaehlerDifferential_sections k p ⟨U, hUaff⟩ rfl
  exact finite_kaehlerDifferential_of_isLocalization k U.sec (stkX X x)
    (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl inferInstance

theorem free_kaehlerDifferential_stalk :
    letI := stalkAlgebra k p x
    Module.Free (stkX X x) $ KaehlerDifferential k $ stkX X x := by
  let algst := stalkAlgebra k p x
  have _hN := isNoetherianRing_stalk k p x
  have _hFS := formallySmooth_stalk k p x
  have _hFin :=
    finite_kaehlerDifferential_stalk k p x
  let A := stkX X x
  have _h1 : FinitePresentation A $ KaehlerDifferential k A :=
    finitePresentation_of_finite ..
  have _h2 : Projective A $ KaehlerDifferential k A := inferInstance
  have _h3 : Module.Flat A $ KaehlerDifferential k A := inferInstance
  exact free_of_flat_of_isLocalRing
end

section
variable [hv2_0 : CharZero k] {X : Sch} (p : X ⟶ Sp k) [Smooth p] (I : ISD X)
include hv2_0 p
theorem orderAt_derivIdealSheafIterate_eq_sub
    (x : X) {r : ℕ} (hr : orderAt I x = (r : ENat)) {j : ℕ} (hj : j ≤ r) :
    orderAt (derivIdealSheafIterate k p j I) x = ((r - j : ℕ) : ENat) := by
  let algst := stalkAlgebra k p x
  have _hN := isNoetherianRing_stalk k p x
  have _hFS := formallySmooth_stalk k p x
  have _hFin :=
    finite_kaehlerDifferential_stalk k p x
  have _hFree :=
    free_kaehlerDifferential_stalk k p x
  let algres :=
    ((residue $ stkX X x).comp $ stalkAlgebraMap k p x).toAlgebra
  have _tower : IsScalarTower k (stkX X x)
      (ResidueField $ stkX X x) :=
    of_algebraMap_eq' rfl
  have _hFSres :=
    formallySmooth_residueField k p x rfl
  obtain ⟨h, y, δ, hspan, hde_⟩ := exists_local_parameters_and_dual_derivations k $ stkX X x
  have hI' : idealOrder (stalkIdeal I x) = r := by
    rwa [← orderAt_eq_idealOrder]
  rw [orderAt_eq_idealOrder, stalkIdeal_derivIdealSheafIterate k p j I x]
  exact idealOrder_derivIdealIterate_of_isUnit_natCast k y δ hde_ hspan
    (fun n hn => isUnit_natCast_stalk k p x hn) hI' hj

theorem orderAtLeastLocus_derivIdealSheafIterate
    {r m : ℕ} (h : r < m) :
    orderAtLeastLocus (derivIdealSheafIterate k p r I) (m - r) = orderAtLeastLocus I m := by
  refine m15 ?_ $ orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p I r m
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx ⊢
  rcases eq_top_or_exists_eq_natCast (orderAt I x) with htop | ⟨n, hn⟩
  simp_all
  rcases m63 n r with hnr | hrn
  exfalso
  have hzero :=
    orderAt_derivIdealSheafIterate_eq_sub k p I x hn le_rfl
  simp at hzero
  have hsplit : r - n + n = r := by omega
  have hadd :=
    derivIdealSheafIterate_add k p (r - n) n I
  rw [hsplit] at hadd
  have hle : derivIdealSheafIterate k p n I ≤ derivIdealSheafIterate k p r I := by
    rw [hadd]
    exact le_derivIdealSheafIterate k p (r - n) $ derivIdealSheafIterate k p n I
  have h1 : orderAt (derivIdealSheafIterate k p r I) x ≤ 0 := by
    have h2 := orderAt_le_of_le hle x
    rwa [hzero] at h2
  have h3 := le_trans hx h1
  have h4 : m - r ≤ 0 := by exact_mod_cast h3
  omega
  have key :=
    orderAt_derivIdealSheafIterate_eq_sub k p I x hn hrn
  rw [key] at hx
  have hmn : m - r ≤ n - r := by exact_mod_cast hx
  have hmn' : m ≤ n := by omega
  rw [hn]
  exact_mod_cast hmn'

theorem support_derivIdealSheafIterate_eq_orderAtLeastLocus {m : ℕ} (hm : 1 ≤ m) :
    (support (derivIdealSheafIterate k p (m - 1) I) : Set X) = orderAtLeastLocus I m := by
  have h1 : m - 1 < m := by omega
  have h2 : m - (m - 1) = 1 := by omega
  have h3 := orderAtLeastLocus_derivIdealSheafIterate k p I (r := m - 1) (m := m) h1
  rw [h2] at h3
  rw [← h3]
  ext x
  exact (mem_orderAtLeastLocus_one_iff (derivIdealSheafIterate k p (m - 1) I) x).symm

theorem isClosed_orderAtLeastLocus
    (m : ℕ) : IsClosed $ orderAtLeastLocus I m := by
  rcases m73 m with hm | hm
  subst hm
  rw [orderAtLeastLocus_zero]
  exact isClosed_univ
  have hm1 : 1 ≤ m := by omega
  rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1]
  exact (derivIdealSheafIterate k p (m - 1) I).support.2
end
end

theorem derivIdealSheafIterate_eq_top_of_orderAtLeastLocus_eq_empty (k : Type) [Field k] [CharZero k] {X : Sch}
    (p : X ⟶ Sp k) [Smooth p] (I : ISD X)
    (m : ℕ) (h : orderAtLeastLocus I (m + 1) = (∅ : Set X)) :
    derivIdealSheafIterate k p m I = ⊤ := by
  let _a0 := derivIdealSheafIterate k p m I
  have hsupp := by
    have h2 := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) $ le_add_left 1 m
    simp [add_sub_cancel] at h2
    exact tr_ h2 h
  refine le_antisymm le_top ?_
  intro U
  have _i42 : _a0.ideal U = ⊤ := by
    let J := _a0
    let _a0 := Γ(X, U.1)
    have hcover : (⨆ f : (J.ideal U : Set Γ(X, U.1)), bOpn X (f : _a0)) = U.1 := by
      refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : _a0)) ?_
      rw [le_def]
      intro x hxU
      have hxs : x ∉ spI J := by
        intro hc
        have hmem : x ∈ (spI J : Set X) := hc
        rw [hsupp] at hmem
        simp at hmem
      have hnle : ¬ stalkIdeal J x ≤ maximalIdeal (stkX X x) := fun hc =>
        hxs $ mpr_ (mem_support_iff_stalkIdeal_le_maximalIdeal J x) hc
      rw [stalkIdeal_eq_map_germ J x U hxU, map_le_iff_le_comap,
        not_le_iff_exists] at hnle
      obtain ⟨a, ha, ha2⟩ := hnle
      refine Opens.mem_iSup.mpr ⟨⟨a, ha⟩, ?_⟩
      refine mpr_ (X.mem_basicOpen a x hxU) ?_
      by_contra hc
      exact ha2 $ Ideal.mem_comap.mpr $ mpr_ (mem_maximalIdeal _)
        (mpr_ mem_nonunits_iff hc)
    have hspan := mp_ (iSup_basicOpen_eq_self_iff U.2) hcover
    rwa [span_eq] at hspan
  rw [_i42]
  exact le_top


section
variable (k : Type) [CommRing k] [IsNoetherianRing k] {X : Sch} (p) [LocallyOfFiniteType p]
section
variable (P I : ISD X)
noncomputable def logDerivIdealSheaf : ISD X where
  ideal U := @logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U)
  map_ideal_basicOpen := by
    intro U f
    have hUaff := U.2
    let algU := sectionsAlgebra k p U.1
    let algV := sectionsAlgebra k p (X.basicOpen f)
    let algUV :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have tower :=
      isScalarTower_sections k p U.1 f rfl rfl rfl
    have loc := hUaff.isLocalization_basicOpen f
    have fp :=
      finitePresentation_kaehlerDifferential_sections k p U rfl
    have noeth := isNoetherianRing_sections k p U rfl
    have hP : (P.ideal U).FG := IsNoetherian.noetherian _
    have key := logDerivIdeal_map_away (S' := Γ(X, X.basicOpen f)) k f hP (I.ideal U)
    rw [← P.map_ideal_basicOpen U f, ← I.map_ideal_basicOpen U f]
    exact key

@[simp] theorem logDerivIdealSheaf_ideal (U : X.affineOpens) :
    (logDerivIdealSheaf k p P I).ideal U =
      @logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) (I.ideal U) :=
  rfl

theorem logDerivIdealSheaf_le_derivIdealSheaf :
    logDerivIdealSheaf k p P I ≤ derivIdealSheaf k p I := by
  intro U
  exact @logDerivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) $ I.ideal U
end

theorem logDerivIdealSheaf_mono (P : ISD X) :
    Monotone $ logDerivIdealSheaf k p P := by
  intro I J h U
  exact @logDerivIdeal_le_logDerivIdeal k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U)
    (I.ideal U) (J.ideal U) $ h U
end

noncomputable def logDerivIdealSheafIterate (k : Type) [CommRing k] [IsNoetherianRing k]
    {X : Sch} (p : X ⟶ Sp k) [LocallyOfFiniteType p]
    (P : ISD X) : ℕ → ISD X → ISD X
  | 0, I => I
  | (r + 1), I => logDerivIdealSheaf k p P $ logDerivIdealSheafIterate k p P r I

section
variable (k : Type) [CommRing k] [IsNoetherianRing k] {X : Sch} (p) [LocallyOfFiniteType p]
@[simp] theorem logDerivIdealSheafIterate_zero
    (P I : ISD X) : logDerivIdealSheafIterate k p P 0 I = I :=
  rfl

section
variable (P : ISD X)
section
variable (r : ℕ)
section
variable (I : ISD X)
theorem logDerivIdealSheafIterate_succ :
    logDerivIdealSheafIterate k p P (r + 1) I =
      logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r I) :=
  rfl


@[simp] theorem logDerivIdealSheafIterate_ideal (U : X.affineOpens) :
    (logDerivIdealSheafIterate k p P r I).ideal U =
      @logDerivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) r (I.ideal U) := by
  induction r with
  | zero =>
      rw [logDerivIdealSheafIterate_zero,
        @logDerivIdealIterate_zero k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) $ I.ideal U]
  | succ r ih =>
      rw [logDerivIdealSheafIterate_succ, logDerivIdealSheaf_ideal, ih,
        @logDerivIdealIterate_succ k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) r $ I.ideal U]

theorem logDerivIdealSheafIterate_le_derivIdealSheafIterate :
    logDerivIdealSheafIterate k p P r I ≤ derivIdealSheafIterate k p r I := by
  induction r with
  | zero =>
      exact le_of_eq
        (tr_ (logDerivIdealSheafIterate_zero k p P I) (derivIdealSheafIterate_zero k p I).symm)
  | succ r ih =>
      rw [logDerivIdealSheafIterate_succ, derivIdealSheafIterate_succ]
      exact le_trans
        (logDerivIdealSheaf_le_derivIdealSheaf k p P $ logDerivIdealSheafIterate k p P r I)
        (derivIdealSheaf_mono k p ih)
end

theorem logDerivIdealSheafIterate_mono :
    Monotone $ logDerivIdealSheafIterate k p P r := by
  induction r with
  | zero =>
      intro I J h
      rwa [logDerivIdealSheafIterate_zero, logDerivIdealSheafIterate_zero]
  | succ r ih =>
      intro I J h
      rw [logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ]
      exact logDerivIdealSheaf_mono k p P $ ih h
end

theorem logDerivIdealSheafIterate_add (r s : ℕ) (I : ISD X) :
    logDerivIdealSheafIterate k p P (r + s) I =
      logDerivIdealSheafIterate k p P r (logDerivIdealSheafIterate k p P s I) := by
  induction r with
  | zero =>
      rw [zero_add, logDerivIdealSheafIterate_zero]
  | succ r ih =>
      have hrs : r + 1 + s = (r + s) + 1 := by omega
      rw [hrs, logDerivIdealSheafIterate_succ, logDerivIdealSheafIterate_succ, ih]
end
end


private theorem comp_app_apply {X Y Z : Sch} (u : X ⟶ Y) (q : Y ⟶ Z) (U : Opn Z)
    (a : (Z.sec U)) : ((u ≫ q).app U).hom a = (u.app $ pre q U).hom ((q.app U).hom a) := by
  have h := comp_app u q U
  exact congr_fun (congrArg hom h) a

section
variable (k : Type) [CommRing k]
theorem derivIdealIterate_mono_of_le {T : Type} [CommRing T]
    [Algebra k T] (r : ℕ) {I J : Ideal T} (h : I ≤ J) :
    derivIdealIterate k r I ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact h
  | succ r ih =>
      rw [derivIdealIterate_succ, derivIdealIterate_succ]
      exact derivIdeal_mono k ih

section
variable {X S : Sch} (p : X ⟶ Sp k) (ι : S ⟶ X) (U : Opn X)
theorem app_comp_sectionsAlgebraMap :
    (ι.app U).hom.comp (sectionsAlgebraMap k p U) = sectionsAlgebraMap k (ι ≫ p) (pre ι U) := by
  let _a2 := appLE ι U (pre ι U) le_rfl
  have happ : _a2 = ι.app U := appLE_eq_app ι
  let _a4 := ι ≫ p
  let _a0 := le_preimage_top k _a4 $ pre ι U
  let _a1 := le_preimage_top k p U
  have hc : appLE p ⊤ U _a1 ≫ _a2
      = appLE _a4 ⊤ (pre ι U) _a0 :=
    appLE_comp_appLE ι p ⊤ U (pre ι U) _a1 le_rfl
  let _a3 := isoI $ GSpecIso $ m10 k
  have hmor : (_a3 ≫ appLE p ⊤ U _a1)
        ≫ ι.app U
      = _a3
        ≫ appLE _a4 ⊤ (pre ι U) _a0 := by simp_all
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k _a4 $ pre ι U]
  exact congrArg hom hmor

private theorem app_sectionsAlgebraMap (a : k) :
    (ι.app U).hom (sectionsAlgebraMap k p U a) = sectionsAlgebraMap k (ι ≫ p) (pre ι U) a :=
  congr_fun (app_comp_sectionsAlgebraMap k p ι U) a
end

section
variable [IsNoetherianRing k] {X S : Sch} (p) [LocallyOfFiniteType p] (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)] (A : ISD X) (r : ℕ)
theorem map_logDerivIdealSheafIterate_ideal_le (U : X.affineOpens) :
    Ideal.map (ι.app (U : Opn X)).hom ((logDerivIdealSheafIterate k p ι.ker r A).ideal U)
      ≤ (derivIdealSheafIterate k (ι ≫ p) r $ A.comap ι).ideal
          ⟨pre ι (U : Opn X), U.2.preimage ι⟩ := by
  let _a1 := ι ≫ p
  let _c0 := sectionsAlgebra k _a1 $ pre ι U
  let _a2 := sectionsAlgebra k p U
  have hcomm : ∀ a,
      (ι.app U).hom
          (@algebraMap k _ _ _ _a2 a)
        = @algebraMap k _ _ _ _c0 a := by
    intro a
    rw [algebraMap_sectionsAlgebra k p U, algebraMap_sectionsAlgebra k _a1 $ pre ι U]
    exact app_sectionsAlgebraMap k p ι U a
  have hmapLE : ∀ (V : affO S) (e : V ≤ pre ι U),
      m6 (appLE ι U V e).hom (A.ideal U)
        ≤ (cmI A ι).ideal V := by
    intro V e
    apply Scheme.IdealSheafData.map_appLE_le_comap_ideal
  have hmap : m6 (ι.app U).hom (A.ideal U)
      ≤ (cmI A ι).ideal ⟨pre ι U, U.2.preimage ι⟩ := by
    rw [app_eq_appLE]
    exact hmapLE ⟨pre ι U, U.2.preimage ι⟩ le_rfl
  have halg := @map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker k _ _ _ _ _
      _a2
      _c0
      (@AlgHom.mk k _ _ _ _ _ _a2
        _c0 (ι.app U).hom hcomm)
      (app_surjective ι U U.2) _ rfl r $ A.ideal U
  rw [logDerivIdealSheafIterate_ideal, ker_apply, derivIdealSheafIterate_ideal]
  exact le_trans halg $ @derivIdealIterate_mono_of_le k _ _ _ _c0 r _ _ hmap

theorem logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  by
    let L := logDerivIdealSheafIterate k p ι.ker r A
    let D := derivIdealSheafIterate k (ι ≫ p) r $ cmI A ι
    have key : ∀ (U : affO X), L.ideal U
        ≤ m41 ((siI D ≫ ι).app U).hom := by
      intro U a ha
      have h1 := (map_logDerivIdealSheafIterate_ideal_le k p ι A r) U $ mem_map_of_mem _ ha
      have h2 : (ker D.si).ideal ⟨pre ι U, U.2.preimage ι⟩
          = m41 (D.subschemeι.app $ pre ι U).hom := by
        rw [ker_apply]
      rw [q2] at h2
      rw [h2] at h1
      refine RingHom.mem_ker.mpr ?_
      rw [comp_app_apply]
      exact RingHom.mem_ker.mp h1
    have hle : L ≤ ker (siI D ≫ ι) := by
      unfold ker
      exact mpr_ le_ofIdeals_iff key
    rwa [← le_map_iff_comap_le]

theorem comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate k p ι A r
end
end


theorem map_eq_comap_of_inverse {A B : Type} [CommRing A] [CommRing B]
    (ph_ : A →+* B) (ps_ : B →+* A) (h1 : ∀ a, ps_ (ph_ a) = a) (h2 : ∀ b, ph_ (ps_ b) = b) (J : Ideal A) :
    Ideal.map ph_ J = comap ps_ J := by
  apply le_antisymm
  rw [map_le_iff_le_comap]
  intro a ha
  rwa [mem_comap, mem_comap, h1]
  intro x hx
  rw [mem_comap] at hx
  have hmem := mem_map_of_mem ph_ hx
  rwa [h2 x] at hmem

theorem ideal_comap_eq_map_appLE {X Y : Sch} (I : ISD Y) (f : X ⟶ Y)
    [IsOpenImmersion f] (V : X.affineOpens) (hU : IsAffineOpen $ f.im (V : Opn X))
    (e : (V : Opn X) ≤ f ⁻¹ᵁ (f.im (V : Opn X))) :
    (I.comap f).ideal V =
      (I.ideal ⟨f.im (V : Opn X), hU⟩).map
        (appLE f (f.im (V : Opn X)) (V : Opn X) e).hom := by
  rw [ideal_comap_of_isOpenImmersion I f V]
  rw [(appIso_hom' f V).symm]
  let _a0 := f.appIso V
  have h1 :=
    fun a => inv_hom_apply _a0 a
  have h2 :=
    fun b => hom_inv_apply _a0 b
  exact sy_ $ map_eq_comap_of_inverse _ _ h1 h2 _

section
variable (K : Type) [CommRing K]
theorem map_logDerivIdealIterate_of_bijective
    {S S' : Type} [CommRing S] [CommRing S'] [Algebra K S] [Algebra K S']
    (ph_ : S →+* S') (hph : Bijective ph_)
    (hcomp : ∀ a : K, ph_ (algebraMap K S a) = algebraMap K S' a)
    [FinitePresentation S Ω[S⁄K]]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    Ideal.map ph_ (logDerivIdealIterate K P r J) =
      logDerivIdealIterate K (Ideal.map ph_ P) r (Ideal.map ph_ J) := by
  let _ := ph_.toAlgebra
  have := of_algebraMap_eq fun a => sy_ $ hcomp a
  have :=
    away_of_isUnit_of_bijective (hr := isUnit_one) (H := hph)
  exact logDerivIdealIterate_map_away K 1 hP r J

theorem map_appLE_logDerivIdealIterate_of_bijective [IsNoetherianRing K]
    {Z W : Sch} (q : Z ⟶ Sp K) [LocallyOfFiniteType q]
    (f : W ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    (U : Z.affineOpens) (V : W.affineOpens) (e : (V : Opn W) ≤ pre f (U : Opn Z))
    (hbij : Bijective (appLE f (U : Opn Z) (V : Opn W) e).hom)
    (P A : Ideal (Z.sec (U : Opn Z))) (r : ℕ) :
    Ideal.map (appLE f (U : Opn Z) (V : Opn W) e).hom
        (@logDerivIdealIterate K _ _ _ (sectionsAlgebra K q (U : Opn Z)) P r A) =
      @logDerivIdealIterate K _ _ _ (sectionsAlgebra K (f ≫ q) (V : Opn W))
        (Ideal.map (appLE f (U : Opn Z) (V : Opn W) e).hom P) r
        (Ideal.map (appLE f (U : Opn Z) (V : Opn W) e).hom A) := by
  let _a0 := sectionsAlgebra K q U
  let _a2 := algebraMap_sectionsAlgebra K q U
  have hfp := @finitePresentation_kaehlerDifferential_sections K _ _ Z q _ U
    _a0 _a2
  have hno := @isNoetherianRing_sections K _ _ Z q _ U
    _a0 _a2
  have hP := m187 P
  let _a3 := f ≫ q
  refine @map_logDerivIdealIterate_of_bijective K _ (Z.sec U) (W.sec V) _ _
    _a0 (sectionsAlgebra K _a3 V)
    (appLE f U V e).hom hbij ?_ hfp P hP r A
  intro a
  rw [algebraMap_sectionsAlgebra, algebraMap_sectionsAlgebra]
  let U := U
  let V := V
  have key : (appLE f U V e).hom.comp (sectionsAlgebraMap K q U)
      = sectionsAlgebraMap K _a3 V := by
    rw [sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← hom_comp, assoc,
      appLE_comp_appLE]
  exact congr_fun key a
end

variable (k : Type) [CommRing k] [IsNoetherianRing k] {X Y : Sch}
  (p : X ⟶ Sp k) [LocallyOfFiniteType p]
  (g : Y ⟶ X) [IsOpenImmersion g] [LocallyOfFiniteType $ g ≫ p]

section
variable (P A : ISD X) (r : ℕ)
theorem logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion (V : Y.affineOpens) :
    ((logDerivIdealSheafIterate k p P r A).comap g).ideal V =
      (logDerivIdealSheafIterate k (g ≫ p) (P.comap g) r $ A.comap g).ideal V := by
  have hU := V.2.image_of_isOpenImmersion g
  have e : V ≤ preU g (g.im V) := by simp_all
  have hbij : Bijective (appLE g (imU g V) V e).hom := by
    let f := g
    let V := V
    have h := sy_ $ appIso_hom' f V
    rw [h]
    exact m189 (f.appIso V).hom
  rw [ideal_comap_eq_map_appLE _ g V hU e, logDerivIdealSheafIterate_ideal,
    logDerivIdealSheafIterate_ideal, ideal_comap_eq_map_appLE P g V hU e,
    ideal_comap_eq_map_appLE A g V hU e]
  exact map_appLE_logDerivIdealIterate_of_bijective k p g ⟨imU g V, hU⟩ V e hbij _ _ r

theorem logDerivIdealSheafIterate_comap_of_isOpenImmersion :
    (logDerivIdealSheafIterate k p P r A).comap g =
      logDerivIdealSheafIterate k (g ≫ p) (P.comap g) r (A.comap g) :=
  m29
    (funext fun V => logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion k p g P A r V)
end

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

theorem comp_presheafMap_comp_presheafMap {X1 : Sch} {R : CRC}
    {A B C : (X1.Opens)ᵒᵖ} (h : R ⟶ X1.presheaf.obj A) (g1_ : A ⟶ B) (g2_ : B ⟶ C) (g3 : A ⟶ C) :
    (h ≫ X1.presheaf.map g1_) ≫ X1.presheaf.map g2_ = h ≫ X1.presheaf.map g3 := by
  rw [assoc, ← m222, Scheme.presheaf_map_eq_of_parallel X1 (g1_ ≫ g2_) g3]

theorem appTop_comp_topIso_hom {X1 Y1 : Sch} (f : X1 ⟶ Y1) (V : Opn X1)
    (hV : V ≤ pre f (⊤ : Opn Y1)) :
    appTop (ι V ≫ f) ≫ V.topIso.hom = appLE f ⊤ V hV := by
  have hR : appLE f ⊤ V hV = f.app ⊤ ≫ pMap X1 (homOfLE hV).op := rfl
  simp
  rw [hR]
  exact comp_presheafMap_comp_presheafMap _ _ _ _

theorem appLE_top_comp_topIso_inv {X Y : Sch} (f : X ⟶ Y) (V : Opn X)
    (hV : V ≤ pre f (⊤ : Opn Y)) :
    appLE f ⊤ V hV ≫ V.topIso.inv = appTop (ι V ≫ f) := by
  rw [← appTop_comp_topIso_hom f V hV, assoc, hom_inv_id, comp_id]

def affineSpaceGlobalSectionsHom (k : Type) [Field k] (m : ℕ) :
    MvU m k →+* Γ(affineSpaceFin k m, ⊤) :=
  (inv (GSpecIso $ CommRingCat.of (MvU m k)) ≫
      (AffineSpace.SpecIso (UFin m) $ CommRingCat.of k).hom.appTop).hom

variable {X : Sch} {k : Type} [Field k] {p : X ⟶ Sp k}
  {U : Opn X} {m : ℕ}

section
variable (c : EtaleChart p U m)
def EtaleChart.coord (j : Fin m) : (X.sec U) :=
  U.topIso.hom.hom
    (c.map.appTop.hom
      (AffineSpace.coord (Sp k) (up j : UFin m)))

theorem EtaleChart.coord_def (j : Fin m) :
    c.coord j =
      U.topIso.hom.hom
        (c.map.appTop.hom
          (AffineSpace.coord (Sp k) (up j : UFin m))) :=
  rfl

def EtaleChart.coordRingHom :
    MvU m k →+* (X.sec U) :=
  (U.topIso.hom.hom.comp c.map.appTop.hom).comp $ affineSpaceGlobalSectionsHom k m

theorem EtaleChart.coordRingHom_def :
    c.coordRingHom = (U.topIso.hom.hom.comp c.map.appTop.hom).comp (affineSpaceGlobalSectionsHom k m) :=
  rfl
end

private theorem appTop_hom_appTop_inv_apply {A B : Sch} (e : A ≅ B) (x : Γ(A, ⊤)) :
    (appTop e.hom).hom ((appTop e.inv).hom x) = x := by
  have h : appTop e.inv ≫ appTop e.hom = 𝟙 Γ(A, ⊤) := by
    rw [← comp_appTop, e.hom_inv_id]
    simp
  have h2 := congrArg (fun f : Γ(A, ⊤) ⟶ Γ(A, ⊤) => hom f x) h
  simpa using h2

section
variable (K : Type) [Field K] (n) (j : Fin n)
theorem affineSpace_specIso_inv_appTop_coord :
    ((AffineSpace.SpecIso (UFin n) $ CommRingCat.of K).inv.appTop).hom
        (AffineSpace.coord (Sp K) (up j : UFin n))
      = (inv $ GSpecIso $ CommRingCat.of (MvU n K)).hom
          (MvPolynomial.X (up j : UFin n)) := by
  exact AffineSpace.SpecIso_inv_appTop_coord (m10 K) $ up j

private theorem affineSpaceGlobalSectionsHom_X :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.X (up j : UFin n))
      = AffineSpace.coord (Sp K) (up j : UFin n) := by
  simp [affineSpaceGlobalSectionsHom, hom_comp, coe_comp]
  rw [← affineSpace_specIso_inv_appTop_coord K n j]
  exact appTop_hom_appTop_inv_apply _ _
end

@[simp] theorem EtaleChart.coordRingHom_X (c : EtaleChart p U m) (j : Fin m) :
    c.coordRingHom (MvPolynomial.X (up j : UFin m)) = c.coord j := by
  rw [EtaleChart.coordRingHom_def, EtaleChart.coord_def]
  simp only [comp_apply, affineSpaceGlobalSectionsHom_X]

section
variable (c : EtaleChart p U m)
theorem EtaleChart.coordRingHom_comp_C :
    c.coordRingHom.comp (MvPolynomial.C : k →+* MvU m k) =
      sectionsAlgebraMap k p U := by
  let _c0 := UFin m
  have key : ofHom (m8 : k →+* MvPolynomial _c0 k) ≫
        inv (GSpecIso $ m10 $ MvPolynomial _c0 k) ≫
          (m69 _c0 $ m10 k).hom.appTop ≫
            c.map.appTop ≫ U.topIso.hom =
      inv (GSpecIso $ m10 k) ≫ appLE p ⊤ U (le_preimage_top k p U) := by
    have _i45 : isoH (m69 (UFin m) $ m10 k) ≫ m12 (ofHom m8) = affineSpaceFinToSpec k m := by
      have h : isoI (m69 (UFin m) $ m10 k) ≫
          affineSpaceFinToSpec k m =
          m12 (ofHom
            m8) := by
        simp
      rw [← h, hom_inv_id_assoc]
    rw [← assoc, Scheme.ΓSpecIso_inv_naturality _, assoc,
      ← assoc _ _ $ c.map.appTop ≫ U.topIso.hom, ← comp_appTop,
      _i45, ← assoc _ _ U.topIso.hom,
      ← comp_appTop, c.comp_struct, appTop_comp_topIso_hom p U $ le_preimage_top k p U]
  have h := congrArg hom key
  exact m48 fun x => congr_fun h x

theorem EtaleChart.coordRingHom_C (a : k) :
    c.coordRingHom (MvPolynomial.C a) = sectionsAlgebraMap k p U a :=
  congr_fun (EtaleChart.coordRingHom_comp_C c) a

theorem EtaleChart.coordRingHom_etale (hU : IsAffineOpen U) :
    c.coordRingHom.Etale := by
  let _c0 := m69 (UFin m) $ m10 k
  have hUaff : IsAffine U.toScheme := hU
  have hEt : Etale c.map := c.isEtale
  have hAaff : IsAffine $ affineSpaceFin k m := inferInstance
  have hbeta : IsIso $ appTop
      _c0.hom :=
    inferInstanceAs $ IsIso
      (_c0.hom.app ⊤)
  have hResp := RingHom.Etale.respectsIso
  exact mpr_ (hResp.cancel_left_isIso
      (isoI $ GSpecIso $ m10 $ MvU m k)
      (appTop _c0.hom ≫
        appTop c.map ≫ U.topIso.hom))
    (mpr_ (hResp.cancel_left_isIso
        (appTop _c0.hom)
        (appTop c.map ≫ U.topIso.hom))
      (mpr_ (hResp.cancel_right_isIso (appTop c.map) U.topIso.hom) $ mp iff_of_isAffine c.isEtale))

@[reducible] def EtaleChart.algebra :
    Algebra (MvU m k) $ X.sec U :=
  c.coordRingHom.toAlgebra

theorem EtaleChart.algebraMap_eq_coordRingHom :
    @algebraMap (MvU m k) (X.sec U) _ _ c.algebra = c.coordRingHom :=
  rfl

theorem EtaleChart.algebra_etale (hU : IsAffineOpen U) :
    @Algebra.Etale (MvU m k) (X.sec U) _ _ c.algebra := by
  exact EtaleChart.coordRingHom_etale c hU

theorem EtaleChart.algebra_formallyEtale (hU : IsAffineOpen U) :
    @FormallyEtale (MvU m k) (X.sec U) _ _ c.algebra := by
  have h := EtaleChart.algebra_etale c hU
  exact h.1

theorem EtaleChart.isScalarTower :
    @IsScalarTower k (MvU m k) (X.sec U)
      (@toSMul k (MvU m k) _ _ _)
      (@toSMul (MvU m k) (X.sec U) _ _ c.algebra)
      (@toSMul k (X.sec U) _ _ $ sectionsAlgebra k p U) := by
  let instPoly := c.algebra
  let instBase := sectionsAlgebra k p U
  exact of_algebraMap_eq fun x => sy_ $ EtaleChart.coordRingHom_C c x
end

section
variable {X1 : Sch} (V : Opn X1)
theorem ideal_map_topIso_inv_injective
    {J1 J2 : Ideal $ X1.sec V}
    (hJ : Ideal.map V.topIso.inv.hom J1 = Ideal.map V.topIso.inv.hom J2) : J1 = J2 := by
  have hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = m99 _ := by
    ext x
    exact Iso.inv_hom_id_apply V.topIso x
  have key : ∀ J : Ideal V.sec,
      Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom J) = J := by
    intro J
    rw [map_map, hid, map_id]
  rw [← key J1, hJ, key J2]

private theorem io_appLE_top_eq_topIso_inv
    (e : (⊤ : (toScheme V).Opens) ≤ ι V ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact Scheme.presheaf_map_eq_of_parallel X1 _ _
end

section
variable (c : EtaleChart p U m)
theorem EtaleChart.ideal_eq_span_coord (hU : IsAffineOpen U)
    (I : ISD X) (S : FinSet m)
    (h : restrictIdeal I U = c.coordIdeal S) :
    I.ideal ⟨U, hU⟩ = span (c.coord '' (S : Set $ Fin m)) := by
  have hUaff : IsAffine U.toScheme := hU
  have e : (⊤ : Opn $ oSch U) ≤ opPre U U := by simp_all
  have hL : (restrictIdeal I U).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩
      = Ideal.map U.topIso.inv.hom (I.ideal ⟨U, hU⟩) := by
    rw [restrictIdeal_eq_comap_io, ← io_appLE_top_eq_topIso_inv U e]
    exact Scheme.IdealSheafData.comap_ideal_eq_map_appLE I U.i ⟨U, hU⟩
      ⟨⊤, isAffineOpen_top U.toScheme⟩ e
  have hR : (c.coordIdeal S).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩
      = Ideal.map U.topIso.inv.hom (span $ c.coord '' (S : Set $ Fin m)) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop,
      coordSubspaceIdeal_eq_ofIdealTop_span_coord, AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal_top,
      map_span, map_span, ← image_comp, ← image_comp]
    exact congrArg span $ image_congr fun j _ => sy_ $ Iso.hom_inv_id_apply U.topIso _
  have hfin : Ideal.map U.topIso.inv.hom (I.ideal ⟨U, hU⟩)
      = Ideal.map U.topIso.inv.hom (span $ c.coord '' (S : Set $ Fin m)) := by simp_all
  exact ideal_map_topIso_inv_injective U hfin

theorem EtaleChart.etaleCoordinates_coord (j : Fin m) :
    @EtaleCoordinates.coord k _ (UFin m) (X.sec U) _ c.algebra
      (up j : UFin m) = c.coord j := by
  exact EtaleChart.coordRingHom_X c j
end

end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
section
variable {A B : (X.Opens)ᵒᵖ} (f g : A ⟶ B)
theorem opens_op_hom_ext : f = g := by
  apply Quiver.Hom.unop_inj
  apply elim

private theorem presheaf_map_eq :
    X.presheaf.map f = X.presheaf.map g := by
  rw [opens_op_hom_ext f g]
end

theorem appTop_homOfLE_comp_topIso_hom {V W : Opn X} (h : W ≤ V) :
    appTop (X.homOfLE h) ≫ W.topIso.hom =
      V.topIso.hom ≫ X.presheaf.map (homOfLE h).op := by
  simp
  exact st_ (X.presheaf.map_comp _ _)
    (tr_ (presheaf_map_eq _ _) $ X.presheaf.map_comp _ _)

private theorem exists_mem_basicOpen_of_span_eq_top {U : Opn X}
    (x : X) (hx : x ∈ U) (s : Set $ X.sec U) (hs : span s = ⊤) :
    ∃ t ∈ s, x ∈ X.basicOpen t := by
  by_contra hcon
  push Not at hcon
  have : IsLocalRing $ stkX X x := inferInstance
  have hnu : ∀ t ∈ s, t ∈ comap (pGerm X U x hx).hom
      (maximalIdeal $ stkX X x) := by
    intro t ht
    rw [mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    exact hcon t ht $ mpr_ (X.mem_basicOpen t x hx) hunit
  have hle := Ideal.span_le.mpr hnu
  rw [hs] at hle
  have h1 := hle (Submodule.mem_top : (1 : xSec X U) ∈ ⊤)
  rw [mem_comap, map_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal $ stkX X x).ne_top
    (mpr_ (eq_top_iff_one _) h1)
end

theorem exists_etale_eval2Hom_of_submersivePresentation {k S : Type} [CommRing k] [CommRing S] [Algebra k S]
    {ι σ : Type} [Finite ι] [Finite σ] (P : SubmersivePresentation k S ι σ) :
    ∃ (n : ℕ) (v : UFin n → S),
      RingHom.Etale $ eval₂Hom (algebraMap k S) v := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨n, ⟨g0⟩⟩ := Finite.exists_equiv_fin ((range P.map)ᶜ : Set ι)
  obtain ⟨e, he⟩ : ∃ e, ∀ s, e (inl s) = P.map s :=
    ⟨(Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj)
        ((g0.trans Equiv.ulift.symm).symm)).trans
          (Equiv.Set.sumCompl $ range P.map), fun s => rfl⟩
  refine ⟨n, fun t => P.val $ e $ inr t, ?_⟩
  let _s0 := UFin n
  let :=
    (eval₂Hom (algebraMap k S) fun t => P.val $ e $ inr t).toAlgebra
  have halg : ∀ z,
      algebraMap (MvPolynomial _s0 k) S z =
        eval₂Hom (algebraMap k S) (fun t => P.val $ e $ inr t) z := fun _ => rfl
  have : IsScalarTower k (MvPolynomial _s0 k) S := by
    refine of_algebraMap_eq fun a => ?_
    rw [halg]
    simp
  obtain ⟨Ph_, hPhl, hPhr, hPhC⟩ :
      ∃ Ph_ : MvPolynomial ι k →+* MvPolynomial σ (MvPolynomial _s0 k),
        (∀ s, Ph_ (m7 $ e $ inl s) = m7 s) ∧
        (∀ t, Ph_ (m7 $ e $ inr t) = m8 (m7 t)) ∧
        (∀ a, Ph_ (m8 a) = m8 (m8 a)) := by
    refine ⟨(aeval (fun i => Sum.elim m7
        (fun t => m8 $ m7 t) $ e.symm i) :
          MvPolynomial ι k →ₐ[k] MvPolynomial σ (MvPolynomial _s0 k)).toRingHom,
      ?_, ?_, ?_⟩
    intro s
    simp
    intro t
    simp
    simp_all
  have hecases : ∀ i, (∃ s, i = e (inl s)) ∨ (∃ t, i = e (inr t)) := by
    intro i
    rcases h : e.symm i with s | t
    exact m51 ⟨s, by rw [← h, e.apply_symm_apply]⟩
    exact m61 ⟨t, by rw [← h, e.apply_symm_apply]⟩
  have hPhsurj : Function.Surjective Ph_ := by
    intro z
    induction z using induction_on with
    | C q =>
        induction q using induction_on with
        | C a => exact ⟨m8 a, hPhC a⟩
        | add q1_ q2_ h1_ h2_ =>
            obtain ⟨x, hx⟩ := h1_
            obtain ⟨y, hy⟩ := h2_
            exact ⟨x + y, by rw [map_add, hx, hy, ← map_add]⟩
        | mul_X q t hq =>
            obtain ⟨x, hx⟩ := hq
            exact ⟨x * m7 (e $ inr t), by rw [map_mul, hx, hPhr, ← map_mul]⟩
    | add z1_ z2_ h1_ h2_ =>
        obtain ⟨x, hx⟩ := h1_
        obtain ⟨y, hy⟩ := h2_
        exact ⟨x + y, by rw [map_add, hx, hy]⟩
    | mul_X z s hz =>
        obtain ⟨x, hx⟩ := hz
        exact ⟨x * m7 (e $ inl s), by rw [map_mul, hx, hPhl]⟩
  have hA : ∀ y, algebraMap P.Ring S y = aeval P.val y :=
    fun y => algebraMap_apply _ y
  have hcompX : ∀ i,
      (aeval fun s => P.val $ e $ inl s) (Ph_ $ m7 i) = P.val i := by
    intro i
    rcases hecases i with ⟨s, rfl⟩ | ⟨t, rfl⟩
    simp_all
    simp_all
  have hcomp : ∀ z,
      (aeval fun s => P.val $ e $ inl s) (Ph_ z) =
        aeval P.val z := by
    intro z
    induction z using induction_on with
    | C a =>
        rw [hPhC, aeval_C, halg, aeval_C]
        simp
    | add z1_ z2_ h1_ h2_ => simp [map_add, h1_, h2_]
    | mul_X z i hz => simp [map_mul, hz, hcompX, aeval_X]
  have hpdX : ∀ s i,
      pderiv s (Ph_ $ m7 i) =
        Ph_ (pderiv (P.map s) $ m7 i) := by
    intro s i
    rcases hecases i with ⟨s', rfl⟩ | ⟨t, rfl⟩
    rw [hPhl, he]
    by_cases hss : s = s'
    subst hss
    rw [pderiv_X_self, pderiv_X_self, map_one]
    rw [pderiv_X_of_ne $ m113 hss,
      pderiv_X_of_ne fun hh => hss (P.map_inj hh).symm, map_zero]
    have hne : e (inr t) ≠ P.map s := by
      intro hh
      have hsum : (inr t) = inl s := by
        apply e.injective
        rw [hh, he]
      simp at hsum
    rw [hPhr, pderiv_C, pderiv_X_of_ne hne, map_zero]
  have hpd : ∀ s q,
      pderiv s (Ph_ q) = Ph_ (pderiv (P.map s) q) := by
    intro s q
    induction q using induction_on with
    | C a => rw [hPhC, pderiv_C, pderiv_C, map_zero]
    | add q1_ q2_ h1_ h2_ => simp [map_add, h1_, h2_]
    | mul_X q i hq => simp [map_mul, map_add, hq, hpdX]
  have hsurjW : Function.Surjective
      (aeval (R := MvPolynomial _s0 k)
        (fun s => P.val $ e $ inl s)) := by
    intro s
    exact ⟨Ph_ $ P.σ' s, by rw [hcomp, P.aeval_val_σ']⟩
  let G :=
    ofSurjective (fun s => P.val $ e $ inl s) hsurjW
  have hGval : G.val = fun s => P.val $ e $ inl s := rfl
  have hspanQ : span (range fun j => Ph_ $ P.relation j) = G.ker := by
    have h1 : (range fun j => Ph_ $ P.relation j) = Ph_ '' range P.relation :=
      range_comp _ _
    have h2 : P.ker = comap Ph_ G.ker := by
      rw [ker_eq_ker_aeval_val, ker_eq_ker_aeval_val]
      ext z
      simp [mem_comap, mem_ker, hGval, hcomp]
    rw [h1, ← map_span, P.span_range_relation_eq_ker, h2,
      map_comap_of_surjective Ph_ hPhsurj]
  obtain ⟨Q, hQmap, hQrel, hQalg⟩ :
      ∃ Q : PreSubmersivePresentation (MvPolynomial _s0 k) S σ σ,
        (∀ i, Q.map i = i) ∧ (∀ j, Q.relation j = Ph_ (P.relation j)) ∧
        (∀ z, algebraMap Q.Ring S z =
          aeval (fun s => P.val $ e $ inl s) z) :=
    ⟨{ toGenerators := G
       relation := fun j => Ph_ $ P.relation j
       span_range_relation_eq_ker := hspanQ
       map := id
       map_inj := injective_id },
      fun i => rfl, fun j => rfl, fun z => algebraMap_apply G z⟩
  have hmat : ∀ i j, Q.jacobiMatrix i j = Ph_ (P.jacobiMatrix i j) := by
    intro i j
    rw [jacobiMatrix_apply,
      jacobiMatrix_apply, hQmap, hQrel]
    exact hpd i $ P.relation j
  have hdet : Ph_ P.jacobiMatrix.det = Q.jacobiMatrix.det := by
    rw [map_det Ph_ P.jacobiMatrix,
      Matrix.ext fun i j => hmat i j]
    rfl
  have hjac : Q.jacobian = P.jacobian := by
    rw [jacobian_eq_jacobiMatrix_det,
      jacobian_eq_jacobiMatrix_det, hA, hQalg, ← hdet, hcomp]
  have hunit : IsUnit Q.jacobian := by
    rw [hjac]
    exact P.jacobian_isUnit
  have : IsStandardSmoothOfRelativeDimension 0
      (MvPolynomial _s0 k) S := by
    refine ⟨σ, σ, inferInstance, inferInstance, ⟨Q, hunit⟩, ?_⟩
    simp [Algebra.Presentation.dimension]
  show m121 (MvPolynomial _s0 k) S
  infer_instance

section
variable {X : Sch} {k : Type} [Field k]
section
variable {p : X ⟶ Sp k} {U : Opn X} {m : ℕ} (c : EtaleChart p U m) {V : Opn X} (hVU : V ≤ U)
def EtaleChart.restrict : EtaleChart p V m where
  map := X.homOfLE hVU ≫ c.map
  comp_struct := by
    rw [assoc, c.comp_struct, ← assoc, Scheme.homOfLE_ι]
  isEtale := by
    have := c.isEtale
    infer_instance

@[simp]
theorem EtaleChart.restrict_map :
    (c.restrict hVU).map = X.homOfLE hVU ≫ c.map := rfl
end

section
variable (p : X ⟶ Sp k)
section
variable (U : Opn X) {m} (v : UFin m → U.toScheme.presheaf.obj (op ⊤))
section
variable (he : Etale (AffineSpace.homOfVector (ι U ≫ p) v))
def EtaleChart.ofCoords :
    EtaleChart p U m where
  map := AffineSpace.homOfVector (ι U ≫ p) v
  comp_struct := by
    simp
  isEtale := he

@[simp]
theorem EtaleChart.ofCoords_map :
    (EtaleChart.ofCoords p U v he).map = AffineSpace.homOfVector (ι U ≫ p) v := rfl
end
end

section
variable [Smooth p] (x : X)
theorem exists_etaleChart :
    ∃ U m, x ∈ U ∧ IsAffineOpen U ∧ Nonempty (EtaleChart p U m) := by
  classical
  obtain ⟨V, hxV, hV⟩ := Scheme.exists_isAffineOpen_mem (X := X) x
  have : IsAffine V.toScheme := hV
  set thV : m10 k ⟶ Γ(oSch V, ⊤) :=
    inv (GSpecIso $ m10 k) ≫ appTop (opI V ≫ p) with hthVdef
  set psV : m10 k ⟶ X.sec V := thV ≫ V.topIso.hom with hpsVdef
  have hsmV : Smooth psV.hom := by
    have h1 : Smooth $ hom
      (inv (GSpecIso $ m10 k) ≫ appTop (opI V ≫ p)) := by
      have : IsAffine V.toScheme := hV
      have hfac : V.toScheme.isoSpec.hom ≫
          Spec.map (inv (GSpecIso $ CommRingCat.of k) ≫ appTop (opI V ≫ p)) =
            opI V ≫ p := by
        rw [isoSpec_hom, map_comp, ← assoc, ← Scheme.toSpecΓ_naturality]
        simp
      have h3 := congrArg
        (fun f => V.toScheme.isoSpec.inv ≫ f) hfac
      simp only [← assoc, inv_hom_id, id_comp] at h3
      have h2 : Smooth
          (Spec.map $ inv (GSpecIso $ CommRingCat.of k) ≫ appTop (opI V ≫ p)) := by
        rw [h3]
        infer_instance
      exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp h2
    have h2 := RingHom.Smooth.respectsIso.left thV.hom V.topIso.commRingCatIsoToRingEquiv h1
    rwa [hpsVdef, hom_comp]
  obtain ⟨s, hspan, hloc⟩ := RingHom.Smooth.locally_isStandardSmooth hsmV
  obtain ⟨t, hts, hxt⟩ := exists_mem_basicOpen_of_span_eq_top x hxV s hspan
  have hUV := X.basicOpen_le t
  have hU := hV.basicOpen t
  have : IsAffine (bOpn X t).toScheme := hU
  set thU : m10 k ⟶ Γ(oSch $ bOpn X t, ⊤) :=
    inv (GSpecIso $ m10 k) ≫
      appTop (opI (bOpn X t) ≫ p) with hthUdef
  set psU : m10 k ⟶ Γ(X, bOpn X t) :=
    thU ≫ (bOpn X t).topIso.hom with hpsUdef
  have hpsUeq : psU = psV ≫ pMap X (homOfLE hUV).op := by
    have e1 : opI (bOpn X t) ≫ p = X.homOfLE hUV ≫ (opI V ≫ p) := by
      rw [← assoc, Scheme.homOfLE_ι]
    rw [hpsUdef, hthUdef, e1, comp_appTop, hpsVdef, hthVdef]
    simp only [assoc]
    rw [appTop_homOfLE_comp_topIso_hom]
  have hstdpsU : IsStandardSmooth psU.hom := by
    have := hV.isLocalization_basicOpen t
    have h1 := isStandardSmooth_respectsIso.left
      ((algebraMap V.sec $ Away t).comp psV.hom)
      (algEquiv (powers t) (Away t)
        Γ(X, bOpn X t)).toRingEquiv $ hloc t hts
    have h2 : (((algEquiv (powers t) (Away t)
        Γ(X, bOpn X t)).toRingEquiv : Away t →+* Γ(X, bOpn X t)).comp
        ((algebraMap (X.sec V) $ Away t).comp psV.hom)) = psU.hom := by
      rw [hpsUeq, hom_comp]
      apply RingHom.ext
      intro a
      exact (algEquiv (powers t) (Away t)
        Γ(X, bOpn X t)).commutes $ psV.hom a
    rwa [← h2]
  have hstdthU : IsStandardSmooth thU.hom := by
    have h1 := isStandardSmooth_respectsIso.left psU.hom
      (bOpn X t).topIso.symm.commRingCatIsoToRingEquiv hstdpsU
    have h3 : thU = psU ≫ (bOpn X t).topIso.inv := by
      rw [hpsUdef, assoc, hom_inv_id, comp_id]
    have h2 : (((bOpn X t).topIso.symm.commRingCatIsoToRingEquiv :
        Γ(X, bOpn X t) →+* Γ(oSch $ bOpn X t, ⊤)).comp psU.hom) = thU.hom := by
      rw [h3, hom_comp]
      rfl
    rwa [← h2]
  let : Algebra (m10 k) Γ(oSch $ bOpn X t, ⊤) := thU.hom.toAlgebra
  obtain ⟨⟨ι, σ, hsg_, hio, ⟨P⟩⟩⟩ := hstdthU
  have : Finite σ := hsg_
  have : Finite ι := hio
  obtain ⟨n, v, hv⟩ := exists_etale_eval2Hom_of_submersivePresentation P
  set ph_ : m10 (MvPolynomial (UFin n) $ m10 k) ⟶
      Γ(oSch $ bOpn X t, ⊤) :=
    ofHom (eval₂Hom
      (algebraMap (m10 k) Γ(oSch $ bOpn X t, ⊤)) v) with hphdef
  have : Etale $ m12 ph_ :=
    AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr hv
  have hphC : ofHom m8 ≫ ph_ = thU := by
    apply CommRingCat.hom_ext
    apply m48
    intro a
    exact MvPolynomial.eval₂_C _ _ a
  refine ⟨bOpn X t, n, hxt, hU,
    ⟨⟨(bOpn X t).toScheme.isoSpec.hom ≫ m12 ph_ ≫
      inv (m69 (UFin n) $ m10 k), ?_, inferInstance⟩⟩⟩
  rw [assoc, assoc, AffineSpace.SpecIso_inv_over, ← map_comp, hphC,
    hthUdef]
  rw [isoSpec_hom, map_comp, ← assoc, ← Scheme.toSpecΓ_naturality]
  simp

theorem exists_etaleChart_le
    (W : Opn X) (hx : x ∈ W) :
    ∃ U m, x ∈ U ∧ U ≤ W ∧ IsAffineOpen U ∧ Nonempty (EtaleChart p U m) := by
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  let _a0 := U ⊓ W
  have hxUW : x ∈ _a0 := ⟨hxU, hx⟩
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, hxUW⟩ : _a0) hxU
  have hle := X.basicOpen_le f
  exact ⟨bOpn X f, m, hxf, le_trans hfle inf_le_right, hU.basicOpen f, ⟨c.restrict hle⟩⟩
end
end
end

end FunctorialResolution.EmbeddedResolution
end
end
-- BEGIN_E2_B01_RECV
noncomputable section
open CategoryTheory AlgebraicGeometry
abbrev sbAt {X : Sch} (s : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups X) := s.schemeAt
abbrev sbCtr {X : Sch} (s : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups X) := s.center
abbrev sbPrj {X : Sch} (s : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups X) := s.projectionToBase
abbrev sbTrS {X : Sch} (s : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups X) := s.transitionMapSucc
abbrev sbIzH {X : Sch} (s : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups X) := s.isoZero.hom
abbrev sbIzI {X : Sch} (s : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups X) := s.isoZero.inv
end
-- END_E2_B01_RECV
-- BEGIN_E2_PROJ_Bundle01
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
abbrev p5 := @FunctorialResolution.Blowup.exceptionalIdeal
abbrev p6 := @FunctorialResolution.Blowup.strictTransform
abbrev p9 := @FunctorialResolution.Blowup.exceptionalIdeal_eq_comap
abbrev p13 := @FunctorialResolution.Blowup.AffineBlowup.toSpec
abbrev p15 := @FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf
abbrev p17 := @FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
abbrev p30 := @FunctorialResolution.Blowup.comap_map_of_isClosedImmersion
abbrev p32 := @AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE
abbrev p33 := @EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal
abbrev p35 := @FunctorialResolution.Blowup.reesGenerator
abbrev p51 := @FunctorialResolution.Blowup.chartRingHom
abbrev p55 := @orderAt
end
-- END_E2_PROJ_Bundle01
-- BEGIN_F2_B01_RECV
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
end
-- END_F2_B01_RECV
