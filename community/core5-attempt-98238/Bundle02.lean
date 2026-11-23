import Mathlib
import Bundle00
import Bundle01
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Finset (add_sum_erase card_compl card_eq_one card_insert_of_notMem card_le_one card_pos card_singleton coe_image coe_insert coe_singleton eq_empty_or_nonempty filter_subset mem_coe mem_compl mem_insert mem_insert_of_mem mem_insert_self mem_of_mem_erase mem_sdiff mem_singleton_self mul_prod_erase mul_sum ne_of_mem_erase orderEmbOfFin_mem prod_attach prod_coe_sort prod_congr prod_empty prod_image prod_induction prod_insert prod_union range_orderEmbOfFin sdiff_disjoint sdiff_union_of_subset sum_add_distrib sum_congr sum_eq_single sum_eq_single_of_mem univ)
open Ideal (bot_isMaximal comap comap_injective_of_surjective comap_isMaximal_of_surjective comap_isPrime comap_map_of_bijective comap_map_of_surjective comap_mono eq_top_iff_one eq_top_of_isUnit_mem exists_le_maximal height_le_spanFinrank isMaximal_comap_of_isIntegral_of_isMaximal' isPrime_bot isPrime_map_C_iff_isPrime isRadical_iff_quotient_reduced le_comap_map map map_isPrime_of_surjective map_le_iff_le_comap map_map map_mono map_span mem_bot mem_comap mem_map_C_iff mem_map_iff_of_surjective mem_map_of_mem mem_quotient_iff_mem mem_radical_iff mem_span_singleton mem_span_singleton' mem_span_singleton_self mk_ker mul_mem_left mul_mem_right one_eq_top pow_right_mono primeCompl quotEquivOfEq quotientEquivAlgOfEq quotientKerAlgEquivOfSurjective quotientMap quotientMap_mk radical_eq_sInf span span_insert span_le span_singleton_eq_bot span_singleton_eq_top span_singleton_le_iff_mem span_singleton_mul_left_unit span_singleton_mul_span_singleton span_singleton_one span_singleton_pow subset_span sum_mem toCotangent_surjective top_mul under)
open Set (disjoint_left image image_comp image_congr image_image image_insert_eq image_mono image_preimage_eq_inter_range image_preimage_eq_of_subset image_singleton mem_image_of_mem mem_range mem_range_self mem_singleton mem_univ preimage range range_comp sUnion_eq_biUnion sUnion_subset sdiff_subset singleton_subset_iff subset_sUnion_of_mem)
open TopologicalSpace.Opens (isBasis_iff_nbhd mem_iSup)
open Nat (add_sub_cancel cast_add cast_eq_zero cast_le cast_mul cast_ne_zero lt_succ_self succ_ne_zero)
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates (algebraMap_X_inl algebraMap_det_basisKaehler basisKaehler basisKaehler_apply exists_adapted_parameters exists_away_ideal_eq_span_and_formallyEtale formallyEtale_aeval_of_isUnit_det formallyEtale_trans map_derivIdeal_sum partialDeriv_apply partialDeriv_coord partialDeriv_coord_of_ne partialDeriv_coord_self sumEvalAlgebra sumEvalAlgebra_isScalarTower)
open Submodule (exists_span_set_card_eq_spanRank iSup_induction map_subtype_top mem_colon mem_of_span_eq_top_of_smul_pow_mem mem_sup mem_sup_left mem_sup_right mem_top mul_induction_on smul_mem spanRank_span_le_card span_induction sub_mem)
open Matrix (cramer cramer_apply cramer_one det_submatrix_equiv_self det_succ_row_zero det_transpose submatrix_submatrix transpose_submatrix updateCol updateCol_apply)
open PrimeSpectrum (asIdeal asIdeal_le_asIdeal asIdeal_lt_asIdeal comap_asIdeal isClosed_singleton_iff_isMaximal isIrreducible_iff_vanishingIdeal_isPrime le_iff_specializes mem_vanishingIdeal mem_zeroLocus topologicalKrullDim_eq_ringKrullDim vanishingIdeal_zeroLocus_eq_radical zeroLocus_anti_mono)
open Scheme (GSpecIso basicOpen basicOpen_le basicOpen_mul exists_affineOpens_mem exists_affineOpens_mem_le exists_isAffineOpen_mem homeoOfIso isBasis_affineOpens isoSpec_hom mem_basicOpen mem_zeroLocus_iff presheaf_map_eq_of_parallel range_fromSpecStalk)
open Algebra (EssFiniteType FinitePresentation FiniteType FormallyEtale FormallySmooth FormallyUnramified HasGoingDown adjoin adjoin_le algebraMapSubmonoid algebra_ext ofId ofId_apply smul_def subset_adjoin)
open Polynomial (coeff_X_one coeff_X_zero coeff_add coeff_one_zero mul_coeff_zero quotient_mk_comp_C_isIntegral_of_isJacobsonRing)
open Fin (addCases append append_left append_right castAdd castSucc_lt_succ le_last natAdd rev rev_lt_rev rev_rev zero_le)
open CommRingCat (hom_comp hom_id hom_ofHom ofHom subsingleton_of_isTerminal)
open Spec (map_comp structureSheaf)
open Cardinal (aleph0 lift_lt_aleph0 mk_image_le_lift toNat toNat_le_toNat toNat_lift)
open IsRegularLocalRing (iff_finrank_cotangentSpace isDomain isPrime_span_singleton isRadical_span_singleton_prod notMem_maximalIdeal_sq of_ringEquiv ringKrullDim_quotient_span_singleton_add_one spanFinrank_maximalIdeal)
open Equiv (symm_apply_apply ulift)
open FunctorialResolution.EmbeddedResolution.EtaleChart (algebraMap_eq_coordRingHom algebra_etale coordIdeal_eq_comap_coordSubspaceIdeal coordRingHom_X coord_def ideal_eq_span_coord ofCoords ofCoords_map restrict restrict_map)
open RingHom (algebraMap_toAlgebra comp_apply ker ker_eq_comap_bot mem_ker quotientKerEquivOfSurjective toAlgebra)
open IsLocalization (algEquiv eq_iff_exists flat isPrime_of_isPrime_disjoint lift_eq map_under map_units mem_map_algebraMap_iff nonZeroDivisors_le_comap surj)
open MvPolynomial (X_injective X_ne_zero aeval aeval_C aeval_X algHom_ext algebraMap_eq finSuccEquiv renameEquiv ringHom_ext)
open Submonoid (mem_powers mem_powers_iff mul_mem powers prod_mem)
open IsLocalRing (CotangentSpace ResidueField le_maximalIdeal map_maximalIdeal_le map_maximalIdeal_of_surjective maximalIdeal maximalIdeal_comap maximalIdeal_height_eq_ringKrullDim mem_maximalIdeal residue)
open Iso (hom_inv_id hom_inv_id_apply hom_inv_id_assoc inv inv_hom_id inv_hom_id_apply)
open Scheme.IdealSheafData (comapIso comapIso_hom_fst comap_comp comap_ideal_eq_map_appLE comap_ideal_eq_span_image comap_ideal_top_eq_map_appTop comap_top ideal_comap_of_isOpenImmersion ideal_mul ideal_pow ker_subschemeι_app le_def le_ofIdeals_iff mem_support_iff_of_mem ofIdealTop ofIdealTop_ideal radical_ideal range_subschemeι subscheme subschemeι subschemeι_app subschemeι_app_surjective support support_antitone support_eq_bot_iff support_top vanishingIdeal)
open Module (Basis Flat finBasis finrank finrank_eq_card_basis flat_iff_of_isLocalization)
open IsAffineOpen (fromSpec fromSpec_preimage_basicOpen fromSpec_primeIdealOf iSup_basicOpen_eq_self_iff isLocalization_stalk primeIdealOf)
open Ideal.Quotient (eq_zero_iff_mem field mk mk_surjective mkₐ)
open Scheme.Hom (appIso appLE appLE_comp_appLE appLE_congr_hom appLE_eq_app appTop app_eq_appLE closePoints_subset_preimage_closedPoints comp_appTop comp_preimage germ_stalkMap id_appTop image_preimage_eq_opensRange_inf isEmbedding ker_apply ker_comp_of_isIso map_appLE pre support_ker)
open ULift (down up)
open CommRingCat.Hom (hom)
open IsScalarTower (algebraMap_apply of_algebraMap_eq of_algebraMap_eq')
open Localization (AtPrime Away)
open Function (Injective Surjective update update_apply)
open IsLocalization.AtPrime (isLocalRing isUnit_to_map_iff map_eq_maximalIdeal to_map_mem_maximal_iff under_maximalIdeal)
open List (getElem_cons_succ getElem_cons_zero getElem_map length length_cons mem_filter)
open Category (assoc id_comp)
open Algebra.TensorProduct (includeLeft includeRight lift lift_tmul tmul_mul_tmul)
open Algebra.FormallyEtale (comp of_equiv of_isLocalization)
open Subtype (range_coe val)
open Limits.pullback (condition fst snd)
open DFunLike (congr_fun)
open RingHom.Etale (of_bijective stableUnderComposition)
open HasRingHomProperty (Spec_iff iff_of_isAffine instIsZariskiLocalAtSource isLocal_ringHomProperty)
open Module.Flat (isSMulRegular_of_nonZeroDivisors trans)
open Derivation (commutator_apply leibniz)
open Flat (generalizingMap stalkMap)
open Subsingleton (elim)
open Quiver.Hom (unop_inj)
open Algebra.FiniteType (isNoetherianRing of_restrictScalars_finiteType)
open Algebra.FormallyUnramified (localization_base map_maximalIdeal)
open IsLocalRing.maximalIdeal (isMaximal)
open Set.Finite (isClosed_biUnion of_finite_image)
open IsOpenImmersion (bijective_appLE_of_image_eq)
open Classical (choose_spec decEq)
open Iff (mp mpr)
open Scheme.Opens (toScheme ι)
section


namespace FunctorialResolution.EmbeddedResolution

theorem isAffineOpen_preimage_subschemeio {X : Sch} (Z : ISD X) {U}
    (hU : IsAffineOpen U) : IsAffineOpen $ subschemeι Z ⁻¹ᵁ U :=
  hU.preimage Z.si

section
variable (m) (S : FinSet m)
theorem card_compl_eq_sub : Sᶜ.card = m - S.card := by
  rw [card_compl, Fintype.card_fin]

def complOrderEmb : Fin (m - S.card) ↪o Fin m :=
  Sᶜ.orderEmbOfFin $ card_compl_eq_sub m S

theorem complOrderEmb_notMem i :
    complOrderEmb m S i ∉ S :=
  mp mem_compl $ orderEmbOfFin_mem Sᶜ (card_compl_eq_sub m S) i

theorem exists_complOrderEmb_eq {j} (hj : j ∉ S) :
    ∃ i : Fin $ m - S.card, complOrderEmb m S i = j := by
  have hmem := mpr_ mem_coe $ mpr_ mem_compl hj
  rw [← range_orderEmbOfFin Sᶜ $ card_compl_eq_sub m S] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact ⟨i, hi⟩
end

section
variable (k : Type) [Field k] (m) (S : FinSet m)
def mvPolynomialCoordIdeal :
    Ideal $ MvU m k :=
  span $ (fun j : Fin m => MvPolynomial.X $ up j) '' (S : Set $ Fin m)

theorem mvPolynomialCoordIdeal_eq_span :
    mvPolynomialCoordIdeal k m S =
      span ((fun j => MvPolynomial.X $ up j) '' (S : Set $ Fin m)) :=
  rfl

theorem X_mem_mvPolynomialCoordIdeal {j}
    (hj : j ∈ S) :
    MvPolynomial.X (up j) ∈ mvPolynomialCoordIdeal k m S :=
  subset_span ⟨j, mpr_ mem_coe hj, rfl⟩

def renameCompl :
    MvPolynomial (UFin $ m - S.card) k →ₐ[k] MvU m k :=
  aeval fun i : UFin (m - S.card) =>
    MvPolynomial.X $ up $ complOrderEmb m S i.down

@[simp] theorem renameCompl_X
    (i : Fin $ m - S.card) :
    renameCompl k m S (MvPolynomial.X (up i)) =
      MvPolynomial.X (up (complOrderEmb m S i)) :=
  aeval_X _ _

theorem renameCompl_C a :
    renameCompl k m S (MvPolynomial.C a) = MvPolynomial.C a := by
  simp

def substZeroOnFinset
    (j : UFin m) : MvPolynomial (UFin $ m - S.card) k :=
  if h : j.down ∈ S then 0
  else MvPolynomial.X $ up $ Classical.choose (exists_complOrderEmb_eq m S h)

def setCoordsZero :
    MvU m k →ₐ[k] MvPolynomial (UFin $ m - S.card) k :=
  aeval $ substZeroOnFinset k m S

theorem setCoordsZero_X_of_mem {j}
    (hj : j ∈ S) : setCoordsZero k m S (MvPolynomial.X $ up j) = 0 := by
  have h1 : setCoordsZero k m S (m7 $ up j) = substZeroOnFinset k m S (up j) :=
    aeval_X _ _
  rw [h1]
  exact dif_pos hj

theorem setCoordsZero_X_complOrderEmb
    i :
    setCoordsZero k m S (MvPolynomial.X $ up $ complOrderEmb m S i) =
      MvPolynomial.X (up i) := by
  let _c0 := up $ complOrderEmb m S i
  have hnot : complOrderEmb m S i ∉ S := complOrderEmb_notMem m S i
  have h1 : setCoordsZero k m S (m7 _c0)
      = substZeroOnFinset k m S _c0 := aeval_X _ _
  let _a0 := exists_complOrderEmb_eq m S hnot
  have h2 : substZeroOnFinset k m S _c0
      = m7 (up $ Classical.choose _a0) :=
    dif_neg hnot
  have h3 : Classical.choose _a0 = i :=
    (complOrderEmb m S).injective $ choose_spec _a0
  rw [h1, h2, h3]

theorem setCoordsZero_eq_zero_of_mem
    {q} (hq : q ∈ mvPolynomialCoordIdeal k m S) :
    setCoordsZero k m S q = 0 := by
  have hker : mvPolynomialCoordIdeal k m S ≤ ker ((setCoordsZero k m S).toRingHom) := by
    rw [mvPolynomialCoordIdeal_eq_span, span_le]
    rintro x ⟨j, hj, rfl⟩
    exact RingHom.mem_ker.mpr $ setCoordsZero_X_of_mem k m S $ mp_ mem_coe hj
  exact RingHom.mem_ker.mp $ hker hq
end

open scoped TensorProduct in
theorem etale_quotientMap {P A : Type} [CommRing P] [CommRing A] {f : P →+* A}
    (hf : f.Etale) I :
    (quotientMap (map f I) f le_comap_map).Etale := by
  let instPA : Algebra P A := f.toAlgebra
  have hfA : m121 P A := hf
  let instQuot : Algebra (P ⧸ I) (A ⧸ map f I) :=
    (quotientMap (map f I) f le_comap_map).toAlgebra
  have hqm : ∀ x, algebraMap (P ⧸ I) (A ⧸ map f I) (mk I x)
      = mk (map f I) (f x) := by
    intro x
    show quotientMap (map f I) f le_comap_map (mk I x) = _
    rw [quotientMap_mk]
  have hst : IsScalarTower P (P ⧸ I) (A ⧸ map f I) := by
    refine of_algebraMap_eq fun x => ?_
    show mk (map f I) (f x)
      = algebraMap (P ⧸ I) (A ⧸ map f I) (algebraMap P (P ⧸ I) x)
    rw [m203, hqm x]
  let _a1 := (1 : P ⧸ I)
  have hcomm : ∀ x, _a1 ⊗ₜ[P] (f x) = (mk I x) ⊗ₜ[P] (1 : A) := by
    intro x
    have h1 : (includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)) (f x)
        = algebraMap P ((P ⧸ I) ⊗[P] A) x :=
      AlgHom.commutes (includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)) x
    let _m0 := (includeLeft : (P ⧸ I) →ₐ[P] ((P ⧸ I) ⊗[P] A))
    have h2 : _m0
        (mk I x) = algebraMap P ((P ⧸ I) ⊗[P] A) x :=
      AlgHom.commutes _m0 x
    have h3 : (includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)) (f x)
        = _a1 ⊗ₜ[P] (f x) := rfl
    have h4 : _m0
        (mk I x) = (mk I x) ⊗ₜ[P] 1 := rfl
    rw [← h3, ← h4, h1, h2]
  have hb : ∀ x (a : A),
      _a1 ⊗ₜ[P] (f x * a) = (mk I x) ⊗ₜ[P] a := by
    intro x a
    let _m1 := _a1 ⊗ₜ[P] a
    have e1 : (_a1 ⊗ₜ[P] (f x)) * _m1
        = _a1 ⊗ₜ[P] (f x * a) := by
      rw [tmul_mul_tmul, one_mul]
    have e2 : ((mk I x) ⊗ₜ[P] 1) * _m1
        = (mk I x) ⊗ₜ[P] a := by
      rw [tmul_mul_tmul, mul_one, one_mul]
    rw [← e1, ← e2, hcomm]
  obtain ⟨ph_, hph⟩ : ∃ ph_ : ((P ⧸ I) ⊗[P] A) →ₐ[P ⧸ I] (A ⧸ map f I),
      ∀ q (a : A), ph_ (q ⊗ₜ[P] a)
        = algebraMap (P ⧸ I) (A ⧸ map f I) q * mk (map f I) a :=
    ⟨lift (ofId (P ⧸ I) (A ⧸ map f I))
        (mkₐ P (map f I)) fun _ _ => Commute.all _ _,
      fun q a => by
        simp [lift_tmul, ofId_apply, Ideal.Quotient.mkₐ_eq_mk]⟩
  obtain ⟨ps_, hps_⟩ : ∃ ps_ : (A ⧸ map f I) →+* ((P ⧸ I) ⊗[P] A),
      ∀ a, ps_ (mk (map f I) a) = _a1 ⊗ₜ[P] a := by
    refine ⟨m201 (map f I)
      (includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)).toRingHom ?_,
      fun _ => rfl⟩
    have hle : map f I ≤ ker
        (includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)).toRingHom := by
      rw [map_le_iff_le_comap]
      intro x hx
      rw [mem_comap, mem_ker]
      show _a1 ⊗ₜ[P] (f x) = 0
      rw [hcomm, Ideal.Quotient.eq_zero_iff_mem.mpr hx, TensorProduct.zero_tmul]
    intro a ha
    exact RingHom.mem_ker.mp $ hle ha
  have hleft : ∀ t : ((P ⧸ I) ⊗[P] A), ps_ (ph_ t) = t := by
    intro t
    refine TensorProduct.inductionOn t ?_ ?_
    intro q a
    obtain ⟨x, rfl⟩ := mk_surjective q
    rw [hph, hqm, ← map_mul (mk (map f I)), hps_]
    exact hb x a
    intro u v hu hv
    rw [map_add, map_add, hu, hv]
  have hsurj : Surjective ph_ := by
    intro b
    obtain ⟨a, rfl⟩ := mk_surjective b
    exact ⟨_a1 ⊗ₜ[P] a, by rw [hph, map_one, one_mul]⟩
  have e : ((P ⧸ I) ⊗[P] A) ≃ₐ[P ⧸ I] (A ⧸ map f I) :=
    AlgEquiv.ofBijective ph_ ⟨Function.LeftInverse.injective hleft, hsurj⟩
  have hbc : m121 (P ⧸ I) ((P ⧸ I) ⊗[P] A) := inferInstance
  show m121 (P ⧸ I) (A ⧸ map f I)
  exact ⟨of_equiv e, hbc.finitePresentation.equiv e⟩

section
variable (k : Type) [Field k] (m) (S : FinSet m)
theorem setCoordsZero_renameCompl
    q :
    setCoordsZero k m S (renameCompl k m S q) = q := by
  have h : (setCoordsZero k m S).comp (renameCompl k m S) = AlgHom.id k _ := by
    refine algHom_ext fun i => ?_
    obtain ⟨i⟩ := i
    rw [AlgHom.comp_apply, renameCompl_X, setCoordsZero_X_complOrderEmb, AlgHom.id_apply]
  exact congr_fun h q

theorem etale_quotientMk_comp_renameCompl
    {A : Type} [CommRing A] (f : MvU m k →+* A)
    (hf : f.Etale) J (hJ : J = map f (mvPolynomialCoordIdeal k m S)) :
    (((mk J).comp f).comp (renameCompl k m S).toRingHom).Etale := by
  let _a0 := renameCompl k m S
  let _c0 := mvPolynomialCoordIdeal k m S
  subst hJ
  let _a1 := map f _c0
  have hcomp : ((mk _a1).comp f).comp
        _a0.toRingHom
      = (quotientMap _a1 f le_comap_map).comp
        ((mk _c0).comp _a0.toRingHom) :=
    m48 fun q => by
      simp [comp_apply, quotientMap_mk]
  rw [hcomp]
  apply stableUnderComposition
  apply of_bijective
  constructor
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hq' : renameCompl k m S q ∈ mvPolynomialCoordIdeal k m S :=
    (eq_zero_iff_mem).1 hq
  have h0 := setCoordsZero_eq_zero_of_mem k m S hq'
  rwa [setCoordsZero_renameCompl] at h0
  intro x
  obtain ⟨p, rfl⟩ := mk_surjective x
  refine ⟨setCoordsZero k m S p, ?_⟩
  have h : (mkₐ k _c0).comp
        (_a0.comp $ setCoordsZero k m S)
      = mkₐ k _c0 := by
    refine algHom_ext fun j => ?_
    obtain ⟨j⟩ := j
    by_cases hj : j ∈ S
    rw [AlgHom.comp_apply, AlgHom.comp_apply, setCoordsZero_X_of_mem k m S hj, map_zero, map_zero]
    symm
    rw [Ideal.Quotient.mkₐ_eq_mk, eq_zero_iff_mem]
    exact X_mem_mvPolynomialCoordIdeal k m S hj
    obtain ⟨i, rfl⟩ := exists_complOrderEmb_eq m S hj
    rw [AlgHom.comp_apply, AlgHom.comp_apply, setCoordsZero_X_complOrderEmb, renameCompl_X]
  exact congr_fun h p
  exact etale_quotientMap hf _c0
end

theorem EtaleChart.coord_restrict {X : Sch} {k : Type} [Field k]
    {p : X ⟶ Sp k} {U V : Opn X} {m : ℕ} (c : EtaleChart p U m)
    (hVU : V ≤ U) (j : Fin m) :
    (c.restrict hVU).coord j = (X.presheaf.map (homOfLE hVU).op).hom (c.coord j) := by
  have key : ∀ {A B C D : (Opens X)ᵒᵖ} {R : CRC} (f : R ⟶ pObj X A)
      (al_ : A ⟶ B) (be_ : B ⟶ D) (ga_ : A ⟶ C) (δ : C ⟶ D) (z : R),
      (pMap X be_).hom ((f ≫ pMap X al_).hom z)
        = (pMap X δ).hom ((pMap X ga_).hom $ f.hom z) := by
    intro A B C D R f al_ be_ ga_ δ z
    exact congrArg (fun g : pObj X A ⟶ pObj X D => g.hom $ f.hom z) $ (st_ $ X.presheaf.map_comp al_ be_) $ (congrArg X.presheaf.map $ unop_inj $ elim _ _).trans $ X.presheaf.map_comp ga_ δ
  simp [restrict, EtaleChart.coord]
  all_goals
    first
      | rfl
      | exact key _ _ _ _ _ _

variable {X : Sch} {k : Type} [Field k] {p : X ⟶ Sp k}
  {U : Opn X} {m : ℕ}

section
variable (c : EtaleChart p U m)
theorem EtaleChart.map_mvPolynomialCoordIdeal_eq_ideal (hU : IsAffineOpen U)
    (Z : ISD X) S (h : restrictIdeal Z U = c.coordIdeal S) :
    Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k m S) = Z.ideal ⟨U, hU⟩ := by
  rw [c.ideal_eq_span_coord hU Z S h, mvPolynomialCoordIdeal_eq_span, map_span]
  congr 1
  rw [image_image]
  exact congrArg (fun g => g '' (S : Set $ Fin m)) $ funext c.coordRingHom_X

def EtaleChart.restrictToSubschemeCoords (Z : ISD X)
    (S : FinSet m) (i : UFin $ m - S.card) :
    Γ(toScheme $ subschemeι Z ⁻¹ᵁ U, ⊤) :=
  (subschemeι Z ⁻¹ᵁ U).topIso.inv.hom
    ((Z.subschemeι.appLE U (subschemeι Z ⁻¹ᵁ U) le_rfl).hom $ c.coord $ complOrderEmb m S i.down)

theorem coordRingHom_apply
    x :
    c.coordRingHom x = U.topIso.hom.hom (c.map.appTop.hom $ affineSpaceGlobalSectionsHom k m x) :=
  rfl
end

section
variable {A B : CRC} (e : A ≅ B)
theorem commRingCatIso_hom_inv_apply x :
    e.hom.hom (e.inv.hom x) = x := by
  simp

theorem bijective_commRingCatIso_inv :
    Function.Bijective e.inv.hom := by
  constructor
  intro x y hxy
  have h := congrArg e.hom.hom hxy
  rwa [commRingCatIso_hom_inv_apply, commRingCatIso_hom_inv_apply] at h
  intro x
  refine ⟨e.hom.hom x, ?_⟩
  simp
end

private theorem appTop_comp_hom_apply {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)) :
    (appTop $ f ≫ g).hom x = (appTop f).hom ((appTop g).hom x) := rfl

section
variable (K : Type) [Field K] (n : ℕ)
theorem affineSpaceGlobalSectionsHom_apply
    x :
    affineSpaceGlobalSectionsHom K n x =
      ((AffineSpace.SpecIso (UFin n) $ CommRingCat.of K).hom.appTop).hom
        ((GSpecIso $ CommRingCat.of (MvU n K)).inv.hom x) :=
  rfl

theorem affineSpaceGlobalSectionsHom_C (a : K) :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.C a) =
      (appTop $ affineSpaceFinToSpec K n).hom
        ((GSpecIso $ CommRingCat.of K).inv.hom a) := by
  let _c1 := UFin n
  let _c0 := ofHom (m8 : K →+* MvPolynomial _c1 K)
  have hov : inv (m69 _c1 $ m10 K) ≫
      affineSpaceFinToSpec K n =
      m12 _c0 :=
    AffineSpace.SpecIso_inv_over ..
  let _a0 := inv $ GSpecIso $ m10 $ MvPolynomial _c1 K
  have h1 : _a0.hom (m8 a)
      = (hAT $ m12 _c0).hom
        ((GSpecIso $ m10 K).inv.hom a) := by
    have hnat := Scheme.ΓSpecIso_inv_naturality
      _c0
    show (_c0 ≫
      _a0).hom a = _
    conv_lhs => rw [hnat]
    rfl
  rw [affineSpaceGlobalSectionsHom_apply, h1, ← appTop_comp_hom_apply, ← hov, hom_inv_id_assoc]
end

theorem appTop_comp_specIso_eq_affineSpaceGlobalSectionsHom {Wsch} {K : Type} [Field K] {n}
    (F : Wsch ⟶ affineSpaceFin K n) (x : MvU n K) :
    ((inv (GSpecIso $ CommRingCat.of (MvU n K)) ≫
        appTop (F ≫ (AffineSpace.SpecIso (UFin n) $ CommRingCat.of K).hom)).hom) x
      = (appTop F).hom (affineSpaceGlobalSectionsHom K n x) := by
  rw [affineSpaceGlobalSectionsHom_apply]
  show (hAT $ F ≫ (m69 (UFin n) $ m10 K).hom).hom
      ((GSpecIso $ m10 $ MvU n K).inv.hom x) = _
  rw [appTop_comp_hom_apply]

private theorem presheaf_map_comp_eq {W : Sch} {A B C : (Opens ↥W)ᵒᵖ}
    (al_ : A ⟶ B) (be_ : B ⟶ C) (ga_ : A ⟶ C) :
    W.presheaf.map al_ ≫ W.presheaf.map be_ = W.presheaf.map ga_ :=
  (st_ $ W.presheaf.map_comp al_ be_)
    (congrArg W.presheaf.map $ unop_inj $ elim _ _)

theorem opens_io_appLE_top_eq_topIso_inv {W : Sch} (V : Opn W)
    (e : (⊤ : (toScheme V).Opens) ≤ ι V ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp [appLE]
  exact presheaf_map_comp_eq _ _ _

theorem iso_hom_appTop_inv_appTop_apply {A B : Sch} (e : A ≅ B) (x : Γ(A, ⊤)) :
    (e.hom.appTop).hom ((e.inv.appTop).hom x) = x := by
  have h1 : (hAT $ e.hom ≫ inv e).hom x
      = (hAT $ m74 A).hom x := by rw [e.hom_inv_id]
  rw [appTop_comp_hom_apply] at h1
  rw [h1]
  simp

theorem affineSpaceGlobalSectionsHom_X_eq_coord (K : Type) [Field K] (n : ℕ) (i : UFin n) :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.X i) =
      AffineSpace.coord (Sp K) i := by
  rw [affineSpaceGlobalSectionsHom_apply, ← AffineSpace.SpecIso_inv_appTop_coord (m10 K) i]
  exact iso_hom_appTop_inv_appTop_apply
    (m69 (UFin n) $ m10 K) _

theorem etale_homOfVector_of_appTop_etale {Wsch : Sch} [IsAffine Wsch]
    {K : Type} [Field K]
    {n : ℕ} (q : Wsch ⟶ Sp K) (v : UFin n → Γ(Wsch, ⊤))
    (hv : ((inv (GSpecIso $ CommRingCat.of (MvU n K)) ≫
      (AffineSpace.homOfVector q v ≫
        (AffineSpace.SpecIso (UFin n) $ CommRingCat.of K).hom).appTop).hom).Etale) :
    Etale $ AffineSpace.homOfVector q v := by
  let _c0 := CommRingCat.of $ MvU n K
  set f := AffineSpace.homOfVector q v
  set e := AffineSpace.SpecIso (UFin n) $ CommRingCat.of K
  set ph_ := isoI (GSpecIso _c0) ≫
      appTop (f ≫ isoH e) with hph
  have key : f = Wsch.toSpecΓ ≫ Spec.map ph_ ≫ isoI e := by
    rw [hph, map_comp]
    calc f = ((f ≫ isoH e) ≫
        (Spec _c0).toSpecΓ) ≫
          Spec.map (GSpecIso
            _c0).inv ≫ isoI e := by simp
      _ = (Wsch.toSpecΓ ≫ Spec.map (f ≫ isoH e).appTop) ≫
          Spec.map (GSpecIso
            _c0).inv ≫ isoI e := by rw [Scheme.toSpecΓ_naturality _]
      _ = Wsch.toSpecΓ ≫ (Spec.map (f ≫ isoH e).appTop ≫
          Spec.map (GSpecIso
            _c0).inv) ≫ isoI e := by
            simp [assoc]
  have : Etale $ Spec.map ph_ := by
    rwa [Spec_iff (P := @Etale)]
  rw [key]
  infer_instance

theorem subschemeio_appLE_apply (Zd : ISD X) Uo
    (hUo : IsAffineOpen Uo) z :
    (Zd.subschemeι.appLE Uo (subschemeι Zd ⁻¹ᵁ Uo) le_rfl).hom z
      = (Zd.subschemeObjIso ⟨Uo, hUo⟩).inv.hom
          (mk (Zd.ideal ⟨Uo, hUo⟩) z) := by
  have h2 : Zd.subschemeι.appLE Uo (siPre Zd Uo) le_rfl = Zd.subschemeι.app Uo := by
    simp [appLE]
  rw [h2]
  conv_lhs => rw [subschemeι_app Zd ⟨Uo, hUo⟩]
  rfl

theorem subschemeio_appLE_topIso_hom_appTop_apply {Wsch Ysch : Sch} (q : Wsch ⟶ Ysch)
    (Zd : ISD Wsch) (Uo : Opn Wsch) (x : Γ(Ysch, ⊤)) :
    (Zd.si ⁻¹ᵁ Uo).topIso.inv.hom
        ((Zd.subschemeι.appLE Uo (Zd.si ⁻¹ᵁ Uo) le_rfl).hom
          (Uo.topIso.hom.hom $ ((Uo.i ≫ q).appTop).hom x))
      = (((Zd.subschemeι ⁻¹ᵁ Uo).i ≫ (Zd.si ≫ q)).appTop).hom x := by
  let _c0 := siPre Zd Uo
  have htop1 : preU q (⊤) = ⊤ := by simp
  let _m0 := siI Zd ≫ q
  have htop2 : preU _m0 (⊤) = ⊤ := by simp
  have key : (opI Uo ≫ q).appTop ≫ Uo.topIso.hom ≫
        Zd.subschemeι.appLE Uo _c0 le_rfl ≫
          _c0.topIso.inv
      = (opI _c0 ≫ _m0).appTop := by
    rw [(appLE_top_comp_topIso_inv q Uo $ le_top.trans htop1.ge).symm, ← appLE_top_comp_topIso_inv _m0 _c0 $ le_top.trans htop2.ge, assoc, m213, ← assoc,
      appLE_comp_appLE]
  show ((opI Uo ≫ q).appTop ≫ Uo.topIso.hom ≫
      Zd.subschemeι.appLE Uo _c0 le_rfl ≫
        _c0.topIso.inv) x = _
  rw [key]

section
variable (c : EtaleChart p U m) (hU : IsAffineOpen U) (Z : ISD X) (S : FinSet m)
include hU
theorem appTop_homOfVector_restrictToSubschemeCoords_eq :
    ((inv (GSpecIso (CommRingCat.of (MvPolynomial (UFin (m - S.card)) k))) ≫
        (AffineSpace.homOfVector (ι (subschemeι Z ⁻¹ᵁ U) ≫ (subschemeι Z ≫ p))
            (c.restrictToSubschemeCoords Z S) ≫
          (AffineSpace.SpecIso (UFin (m - S.card))
            (CommRingCat.of k)).hom).appTop).hom)
      = ((((subschemeι Z ⁻¹ᵁ U).topIso.inv.hom).comp
            ((Z.subschemeObjIso ⟨U, hU⟩).inv.hom)).comp
          (((mk (Z.ideal ⟨U, hU⟩)).comp c.coordRingHom).comp
            (renameCompl k m S).toRingHom)) := by
  let _a2 := siI Z ≫ p
  let _a0 := Z.subschemeObjIso ⟨U, hU⟩
  let _a1 := Z.ideal ⟨U, hU⟩
  let _c0 := siPre Z U
  refine ringHom_ext (fun a => ?_) fun i => ?_
  have hover : m52 (opI _c0 ≫ _a2)
      (c.restrictToSubschemeCoords Z S) ≫ affineSpaceFinToSpec k (m - S.card)
      = opI _c0 ≫ _a2 := m179 ..
  rw [appTop_comp_specIso_eq_affineSpaceGlobalSectionsHom, affineSpaceGlobalSectionsHom_C, ← appTop_comp_hom_apply, hover]
  show _ = _c0.topIso.inv.hom
    (_a0.inv.hom
      (mk _a1
        (c.coordRingHom $ renameCompl k m S $ m8 a)))
  rw [renameCompl_C, coordRingHom_apply, affineSpaceGlobalSectionsHom_C, ← appTop_comp_hom_apply,
    c.comp_struct, ← subschemeio_appLE_apply Z U hU, subschemeio_appLE_topIso_hom_appTop_apply]
  obtain ⟨i⟩ := i
  rw [appTop_comp_specIso_eq_affineSpaceGlobalSectionsHom, affineSpaceGlobalSectionsHom_X_eq_coord, m87]
  show _c0.topIso.inv.hom
      ((Z.subschemeι.appLE U _c0 le_rfl).hom $ c.coord $ complOrderEmb m S i)
    = _c0.topIso.inv.hom
      (_a0.inv.hom
        (mk _a1
          (c.coordRingHom $ renameCompl k m S $ m7 $ up i)))
  rw [renameCompl_X, coordRingHom_X, ← subschemeio_appLE_apply Z U hU]

section
variable (h : restrictIdeal Z U = c.coordIdeal S)
include h
theorem EtaleChart.etale_homOfVector_restrictToSubschemeCoords :
    Etale $ AffineSpace.homOfVector (ι (subschemeι Z ⁻¹ᵁ U) ≫ (subschemeι Z ≫ p))
      (c.restrictToSubschemeCoords Z S) := by
  have hVa : IsAffine (siPre Z U).toScheme := isAffineOpen_preimage_subschemeio Z hU
  refine etale_homOfVector_of_appTop_etale _ _ ?_
  rw [appTop_homOfVector_restrictToSubschemeCoords_eq c hU Z S]
  apply stableUnderComposition
  exact etale_quotientMk_comp_renameCompl k m S c.coordRingHom (c.coordRingHom_etale hU) (Z.ideal ⟨U, hU⟩)
    (c.map_mvPolynomialCoordIdeal_eq_ideal hU Z S h).symm
  apply of_bijective
  exact (bijective_commRingCatIso_inv (siPre Z U).topIso).comp
    (bijective_commRingCatIso_inv $ Z.subschemeObjIso ⟨U, hU⟩)

def EtaleChart.restrictToSubscheme :
    EtaleChart (subschemeι Z ≫ p) (subschemeι Z ⁻¹ᵁ U) $ m - S.card :=
  ofCoords (subschemeι Z ≫ p) (subschemeι Z ⁻¹ᵁ U) (c.restrictToSubschemeCoords Z S)
    (c.etale_homOfVector_restrictToSubschemeCoords hU Z S h)

section
variable (i : Fin (m - S.card))
theorem EtaleChart.restrictToSubscheme_coord :
    (c.restrictToSubscheme hU Z S h).coord i =
      (Z.subschemeι.appLE U (subschemeι Z ⁻¹ᵁ U) le_rfl).hom (c.coord $ complOrderEmb m S i) := by
  let _a0 := c.restrictToSubscheme hU Z S h
  let _a1 := siI Z ≫ p
  let _a2 := c.restrictToSubschemeCoords Z S
  have hmapeq : _a0.map =
      m52 (opI (preU Z.si U) ≫ _a1)
        _a2 :=
    ofCoords_map _a1 (siPre Z U)
      _a2 $ c.etale_homOfVector_restrictToSubschemeCoords hU Z S h
  have hcoord : (_a0.map.appTop).hom
      (m9 (Sp k)
        (up i : UFin $ m - S.card))
      = (siPre Z U).topIso.inv.hom
          ((Z.subschemeι.appLE U (siPre Z U) le_rfl).hom
            (c.coord $ complOrderEmb m S i)) := by
    rw [hmapeq]
    apply m87
  rw [coord_def _a0 i, hcoord]
  exact commRingCatIso_hom_inv_apply _ _

theorem restrictToSubscheme_map_appTop_coord :
    ((c.restrictToSubscheme hU Z S h).map.appTop).hom
        (AffineSpace.coord (Sp k) $ up i) =
      (subschemeι Z ⁻¹ᵁ U).topIso.inv.hom
        ((Z.subschemeι.appLE U (subschemeι Z ⁻¹ᵁ U) le_rfl).hom $ c.coord $ complOrderEmb m S i) := by
  simp [EtaleChart.restrictToSubscheme, ofCoords_map,
    EtaleChart.restrictToSubschemeCoords]

theorem EtaleChart.restrictToSubscheme_coordIdeal_singleton (E : ISD X)
    (hE : restrictIdeal E U = c.coordIdeal {complOrderEmb m S i}) :
    restrictIdeal (E.comap Z.si) (subschemeι Z ⁻¹ᵁ U) =
      (c.restrictToSubscheme hU Z S h).coordIdeal {i} := by
  let _c0 := siPre Z U
  have hVaff : IsAffineOpen _c0 := isAffineOpen_preimage_subschemeio Z hU
  have hVa : IsAffine _c0.toScheme := hVaff
  have hAa : IsAffine $ affineSpaceFin k $ m - S.card := inferInstance
  have e1 : (⊤ : Opn $ oSch _c0) ≤
      opPre _c0 _c0 := by simp
  let _a0 := (cmI E Z.si).ideal ⟨siPre Z U, hVaff⟩
  have hL1 : (restrictIdeal (cmI E Z.si) _c0).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      m6 (_c0.ι.appLE _c0 ⊤ e1).hom
        _a0 :=
    comap_ideal_eq_map_appLE (cmI E Z.si)
      _c0.i ⟨Z.si.pre U, hVaff⟩ ⟨⊤, isAffineOpen_top _⟩ e1
  have hL2 : _a0 =
      m6 (Z.subschemeι.appLE U _c0 le_rfl).hom (E.ideal ⟨U, hU⟩) :=
    p32 E Z.si ⟨U, hU⟩
      ⟨siPre Z U, hVaff⟩ le_rfl
  have hL3 : E.ideal ⟨U, hU⟩ = span {c.coord $ complOrderEmb m S i} := by
    rw [c.ideal_eq_span_coord hU E {complOrderEmb m S i} hE, coe_singleton,
      image_singleton]
  let _a5 := c.restrictToSubscheme hU Z S h
  have hR1 : (_a5.coordIdeal {i}).ideal ⟨⊤, isAffineOpen_top _⟩ =
      m6 (_a5.map.appTop).hom
        ((coordSubspaceIdeal k (m - S.card) {i}).ideal ⟨⊤, isAffineOpen_top _⟩) := by
    rw [coordIdeal_eq_comap_coordSubspaceIdeal]
    exact comap_ideal_top_eq_map_appTop _ _
  have hR2 : (coordSubspaceIdeal k (m - S.card) {i}).ideal ⟨⊤, isAffineOpen_top _⟩ =
      span {m9 (Sp k) $ up i} := by
    rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, Scheme.IdealSheafData.ofIdealTop_ideal_top, coe_singleton,
      image_singleton]
  refine m170 ?_
  rw [hL1, hL2, hL3, hR1, hR2]
  simp only [map_span, image_singleton]
  rw [restrictToSubscheme_map_appTop_coord, opens_io_appLE_top_eq_topIso_inv]
end
end
end

theorem restrictIdeal_comap_subschemeio_eq_top {X : Sch} (Z : ISD X)
    U (E : ISD X) (hE : restrictIdeal E U = ⊤) :
    restrictIdeal (E.comap Z.si) (subschemeι Z ⁻¹ᵁ U) = ⊤ := by
  rw [restrictIdeal_eq_comap_io] at hE
  rw [restrictIdeal_eq_comap_io, ← comap_comp,
    ← morphismRestrict_ι Z.si U, comap_comp, hE,
    comap_top]

end FunctorialResolution.EmbeddedResolution
end
section

namespace FunctorialResolution.EmbeddedResolution

variable {X : Sch} {k : Type} [Field k] {p : X ⟶ Sp k} {m : ℕ}

section
variable {Y : Sch}
theorem restrictIdeal_eq_top_of_le (Z : ISD Y) {U V : Opn Y}
    (hVU : V ≤ U) (h : restrictIdeal Z U = ⊤) : restrictIdeal Z V = ⊤ := by
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal Z hVU, h, comap_top]

end

section
variable {σ k : Type} [Field k] {j s} (hjs : j ≠ s)
include hjs
theorem mem_span_X_of_X_mul_mem r
    (hr : MvPolynomial.X s * r ∈ span {(MvPolynomial.X j : MvPolynomial σ k)}) :
    r ∈ span {(MvPolynomial.X j : MvPolynomial σ k)} := by
  classical
  obtain ⟨ps_, hpsC, hpsXj, hpsXi⟩ : ∃ ps_ : MvPolynomial σ k →+* MvPolynomial σ k,
      (∀ a : k, ps_ (m8 a) = m8 a) ∧
        ps_ (m7 j) = 0 ∧
        ∀ i : σ, i ≠ j → ps_ (m7 i) = m7 i := by
    refine ⟨MvPolynomial.eval₂Hom m8
        (fun i => if i = j then 0 else m7 i), ?_, ?_, ?_⟩
    intro a
    simp
    simp
    simp_all
  let _a0 := span {(m7 j : MvPolynomial σ k)}
  have key : (mk _a0).comp ps_
      = mk _a0 := by
    apply ringHom_ext
    simp_all
    intro i
    rw [comp_apply]
    by_cases h : i = j
    subst h
    rw [hpsXj, map_zero]
    exact sy_ $ Ideal.Quotient.eq_zero_iff_mem.mpr $ mem_span_singleton_self _
    rw [hpsXi i h]
  obtain ⟨t, ht⟩ := mp_ mem_span_singleton hr
  have h0 : ps_ (m7 s * r) = 0 := by simp_all
  rw [map_mul, hpsXi s $ m113 hjs] at h0
  have hpsr : ps_ r = 0 := by simp_all
  have h3 := congr_fun key r
  rw [comp_apply, hpsr, map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3.symm

theorem eq_of_mk_X_mul_eq_quotient_span_X
    a b
    (h : (mk $ span {(MvPolynomial.X j : MvPolynomial σ k)})
            (MvPolynomial.X s) * a
        = (mk $ span {(MvPolynomial.X j : MvPolynomial σ k)})
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := m108 a
  obtain ⟨b', rfl⟩ := m108 b
  rw [← map_mul, ← map_mul, m202, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr $ mem_span_X_of_X_mul_mem hjs (a' - b') h

theorem X_pow_dvd_of_X_pow_dvd_X_mul :
    ∀ n r,
      (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ MvPolynomial.X s * r →
        (MvPolynomial.X j : MvPolynomial σ k) ^ n ∣ r := by
  let _c0 := (m7 j : MvPolynomial σ k)
  intro n
  induction n with
  | zero =>
    intro r _
    rw [pow_zero]
    exact one_dvd r
  | succ n ih =>
    intro r hr
    obtain ⟨r', rfl⟩ := mp mem_span_singleton $ mem_span_X_of_X_mul_mem hjs r $ mpr_ mem_span_singleton $ dvd_trans (dvd_pow_self _ $ succ_ne_zero n) hr
    have h3 : _c0 * m7 j ^ n ∣
        m7 j * (m7 s * r') := by
      have e1 : _c0 * (m7 s * r')
          = m7 s * (m7 j * r') := by ring
      have e2 : _c0 * m7 j ^ n
          = m7 j ^ (n + 1) := by ring
      rwa [e1, e2]
    have e3 : _c0 ^ (n + 1)
        = m7 j * m7 j ^ n := by ring
    rw [e3]
    exact mul_dvd_mul_left _ $ ih r' $ mp (mul_dvd_mul_iff_left $ X_ne_zero _) h3

theorem eq_of_mk_X_mul_eq_quotient_span_X_pow n
    a b
    (h : (mk $ span {(MvPolynomial.X j : MvPolynomial σ k) ^ n})
            (MvPolynomial.X s) * a
        = (mk $ span {(MvPolynomial.X j : MvPolynomial σ k) ^ n})
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := m108 a
  obtain ⟨b', rfl⟩ := m108 b
  rw [← map_mul, ← map_mul, m202, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr $ mpr_ mem_span_singleton
    (X_pow_dvd_of_X_pow_dvd_X_mul hjs n (a' - b') $ mp_ mem_span_singleton h)
end

theorem restrictIdeal_eq_restrict_coordIdeal_of_le {U V : Opn X} (hVU : V ≤ U) (c : EtaleChart p U m)
    (Z : ISD X) S (h : restrictIdeal Z U = c.coordIdeal S) :
    restrictIdeal Z V = (c.restrict hVU).coordIdeal S := by
  have h' : Z.comap U.i = (coordSubspaceIdeal k m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_io, h, coordIdeal_eq_comap_coordSubspaceIdeal]
  rw [restrictIdeal_eq_comap_io, coordIdeal_eq_comap_coordSubspaceIdeal, restrict_map,
    comap_comp, ← h', ← comap_comp,
    Scheme.homOfLE_ι]

theorem mem_map_of_mul_mem_of_etale {P A : Type} [CommRing P] [CommRing A]
    {f : P →+* A} (hf : f.Etale) I w
    (hw : ∀ a b,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    x (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  let _a3 := map f I
  let _a1 := quotientMap _a3 f le_comap_map
  let _ : Algebra (P ⧸ I) $ A ⧸ _a3 :=
    _a1.toAlgebra
  have : m121 (P ⧸ I) $ A ⧸ _a3 := etale_quotientMap hf I
  have : Flat (P ⧸ I) $ A ⧸ _a3 := inferInstance
  let _a0 := (mk I) w
  have hreg : IsSMulRegular (P ⧸ I) _a0 := by
    intro a b h
    exact hw a b $ by simpa only [smul_eq_mul] using h
  let _a2 := mk _a3
  have hy : _a0 • _a2 x
      = _a0 • 0 := by
    rw [smul_zero]
    show _a1 _a0 *
        _a2 x = 0
    rw [quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp $ hreg.of_flat hy

section
variable {U} (hU : IsAffineOpen U) (c : EtaleChart p U m) {j s} (hjs : j ≠ s)
include hU hjs
theorem mem_span_coord_of_coord_mul_mem x
    (hx : c.coord s * x ∈ Ideal.span {c.coord j}) : x ∈ Ideal.span {c.coord j} := by
  classical
  let _a0 := span {(m7 (up j) : MvU m k)}
  have hmapspan : map c.coordRingHom
      _a0
      = span {c.coord j} := by
    rw [map_span, image_singleton, c.coordRingHom_X]
  have hju := fun h => hjs $ congrArg down h
  have hx' : c.coordRingHom (m7 $ up s) * x
      ∈ m6 c.coordRingHom
          _a0 := by simp_all
  have hfin := mem_map_of_mul_mem_of_etale (c.coordRingHom_etale hU)
      _a0
      (m7 $ up s) (fun a b h => eq_of_mk_X_mul_eq_quotient_span_X hju a b h) x hx'
  rwa [hmapspan] at hfin

theorem mem_span_coord_pow_of_mul_mem n x
    (hx : c.coord s * x ∈ Ideal.span {c.coord j ^ n}) :
    x ∈ Ideal.span {c.coord j ^ n} := by
  let _c0 := m17 {(m7 (ULift.up j) : MvU m k) ^ n}
  classical
  have hmapspan : map c.coordRingHom
      _c0
      = span {c.coord j ^ n} := by
    rw [map_span, image_singleton, map_pow, c.coordRingHom_X]
  have hju := fun h => hjs $ congrArg down h
  have hx' : c.coordRingHom (m7 $ up s) * x
      ∈ m6 c.coordRingHom
          _c0 := by simp_all
  have hfin := mem_map_of_mul_mem_of_etale (c.coordRingHom_etale hU)
      _c0
      (m7 $ up s) (fun a b h => eq_of_mk_X_mul_eq_quotient_span_X_pow hju n a b h) x hx'
  rwa [hmapspan] at hfin
end

section
variable (Z : ISD X)
theorem smooth_io_comp_subschemeio_comp_of_eq_coordIdeal {U}
    (hU : IsAffineOpen U) (c : EtaleChart p U m) (S : FinSet m)
    (h : restrictIdeal Z U = c.coordIdeal S) :
    Smooth $ ι (subschemeι Z ⁻¹ᵁ U) ≫ (subschemeι Z ≫ p) := by
  let _c0 := c.restrictToSubscheme hU Z S h
  have hsm : Smooth $ affineSpaceFinToSpec k $ m - S.card := affineSpaceIsSmooth ..
  have het : Etale _c0.map :=
    _c0.isEtale
  have hsm2 : Smooth _c0.map := inferInstance
  rw [← _c0.comp_struct]
  infer_instance

theorem smooth_subschemeio_comp_of_locally_eq_coordIdeal
    (h : ∀ x : X, x ∈ support Z →
      ∃ (U : Opn X) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n) (S : FinSet n),
        restrictIdeal Z U = c.coordIdeal S) :
    Smooth $ subschemeι Z ≫ p := by
  classical
  have i3 : HasRingHomProperty (@Smooth.{0})
      (fun {R S : Type} [CommRing R] [CommRing S] g => g.Smooth) := inferInstance
  have key : ∀ y, ∃ W : Opn $ subS Z,
      y ∈ W ∧ Smooth (opI W ≫ (siI Z ≫ p)) := by
    intro y
    have hy : Z.subschemeι.base y ∈ spI Z := by
      have hmem : Z.subschemeι.base y ∈ range Z.subschemeι.base := mem_range_self y
      simpa using hmem
    obtain ⟨U, hxU, n, c, S, hS⟩ := h _ hy
    obtain ⟨V, hV, hxV, hVU⟩ :=
      mp isBasis_iff_nbhd X.isBasis_affineOpens hxU
    exact ⟨siPre Z V, hxV, smooth_io_comp_subschemeio_comp_of_eq_coordIdeal Z hV (c.restrict hVU) S $ restrictIdeal_eq_restrict_coordIdeal_of_le hVU c Z S hS⟩
  choose W hyW hWsm using key
  refine mpr_ (IsZariskiLocalAtSource.iff_of_iSup_eq_top W ?_) hWsm
  rw [eq_top_iff]
  intro y _
  exact Opens.mem_iSup.mpr ⟨y, hyW y⟩

theorem smooth_subschemeio_comp_of_hasStrictNormalCrossingsWith E
    (h : HasStrictNormalCrossingsWith p Z E) : Smooth $ subschemeι Z ≫ p := by
  unfold HasStrictNormalCrossingsWith at h
  refine smooth_subschemeio_comp_of_locally_eq_coordIdeal Z ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, S, -, -, -, hS⟩ := h x hx
  exact ⟨U, hxU, n, c, S, hS⟩
end

theorem algebraMap_mem_nonZeroDivisors_of_flat {R A : Type} [CommRing R]
    [CommRing A] [Algebra R A] [Flat R A] {r} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R A r ∈ nonZeroDivisors A := by
  have hreg : IsSMulRegular A r := isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ x, algebraMap R A r * x = 0 → x = 0 := by
    intro x hx
    have hsm : r • x = r • 0 := by
      rwa [smul_zero, smul_def]
    exact hreg hsm
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩

theorem coord_mem_nonZeroDivisors {U} (hU : IsAffineOpen U) (c : EtaleChart p U m)
    j : c.coord j ∈ nonZeroDivisors ↑(X.presheaf.obj $ op U) := by
  let _c0 := MvU m k
  let _c1 := pObj X $ op U
  let _ := c.algebra
  have :=
    c.algebra_etale hU
  have : Flat _c0 _c1 :=
    inferInstance
  have hXne : (m7 (up j) : MvU m k) ≠ 0 :=
    X_ne_zero _
  have key : (algebraMap _c0 _c1)
      (m7 $ up j) ∈ nonZeroDivisors _c1 :=
    algebraMap_mem_nonZeroDivisors_of_flat $ mem_nonZeroDivisors_of_ne_zero hXne
  rw [c.algebraMap_eq_coordRingHom] at key
  rwa [c.coordRingHom_X j] at key

section
variable (D : ISD X) (h : ∀ x : X, ∃ (U : Opn X) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n), restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
include h
theorem isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal :
    Blowup.IsLocallyGeneratedByNonZeroDivisor D := by
  intro x
  obtain ⟨U, hxU, n, c, hc⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ := m227 hxU
  obtain ⟨f, hf, hfspan⟩ :
      ∃ f, f ∈ nonZeroDivisors (pObj X $ op V) ∧
        D.ideal ⟨V, hV⟩ = span {f} := by
    rcases hc with htop | ⟨j, hj⟩
    refine ⟨1, one_mem _, ?_⟩
    have _i10 : D.ideal ⟨V, hV⟩ = ⊤ := by
      have : IsAffine V.toScheme := hV
      have hle := V.ι_preimage_self.ge
      have key := comap_ideal_eq_map_appLE D V.i ⟨V, hV⟩
          ⟨⊤, isAffineOpen_top V.toScheme⟩ hle
      rw [← restrictIdeal_eq_comap_io, restrictIdeal_eq_top_of_le D hVU htop] at key
      have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
        simp
      rw [h0] at key
      have hcomap : comap (hom $ V.ι.appLE V ⊤ hle)
          (map (hom $ V.ι.appLE V ⊤ hle) $ D.ideal ⟨V, hV⟩)
          = D.ideal ⟨V, hV⟩ := by
        apply comap_map_of_bijective
        have _i7 : V.ι.appLE V ⊤ hle = V.topIso.inv := by
          simp
          rfl
        rw [_i7]
        exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective
      rw [← hcomap, sy_ key, Ideal.comap_top]
    rw [_i10,
      span_singleton_one]
    refine ⟨(c.restrict hVU).coord j, coord_mem_nonZeroDivisors hV (c.restrict hVU) j, ?_⟩
    rw [(c.restrict hVU).ideal_eq_span_coord hV D {j}
      (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D {j} hj), coe_singleton,
      image_singleton]
  exact ⟨⟨V, hV⟩, f, hxV, hf, hfspan⟩

theorem isSmoothDivisor_of_locally_coordIdeal :
    IsSmoothDivisor p D := by
  rw [isSmoothDivisor_iff]
  refine ⟨isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal D h, smooth_subschemeio_comp_of_locally_eq_coordIdeal D ?_⟩
  intro x hx
  obtain ⟨U, hxU, n, c, hc⟩ := h x
  rcases hc with hc | ⟨j, hj⟩
  have _i8 : x ∉ support D := by
    intro hx
    let _a0 := (⟨x, hxU⟩ : ↥U)
    have h1 : _a0 ∈ support (D.comap U.i) := by
      rwa [m19]
    rw [← restrictIdeal_eq_comap_io, hc, AlgebraicGeometry.Scheme.IdealSheafData.support_top] at h1
    have h2 : _a0 ∈ ((⊥) : Set ↥U) := h1
    simp at h2
  exact absurd hx _i8
  exact ⟨U, hxU, n, c, {j}, hj⟩
end

theorem smooth_of_iSup_eq_top {W Y : Sch} (f : W ⟶ Y) {ι : Sort*} (U : ι → Opn W)
    (hU : iSup U = ⊤) (h : ∀ i, Smooth $ (U i).i ≫ f) : Smooth f := by
  have i3 : HasRingHomProperty (@Smooth.{0})
      (fun {R S : Type} [CommRing R] [CommRing S] g => g.Smooth) := inferInstance
  have hVtop : (⨆ i : PLift ι, U i.down) = ⊤ := by
    rw [← hU]
    exact le_antisymm (iSup_le fun i => le_iSup U i.down)
      (iSup_le fun i => le_iSup (fun j : PLift ι => U j.down) $ PLift.up i)
  exact mpr_ (IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun i : PLift ι => U i.down) hVtop)
    fun i => h i.down

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

theorem algebraMap_quotient_map_mk {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A]
    I r :
    algebraMap (R ⧸ I) (A ⧸ map (algebraMap R A) I) (mk I r)
      = mk (map (algebraMap R A) I) (algebraMap R A r) := rfl

theorem algebraMap_quotient_apply {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
    I a :
    algebraMap k (R ⧸ I) a = mk I (algebraMap k R a) := rfl

theorem formallySmooth_quotient_map_of_isLocalization (k : Type) [CommRing k] {R : Type} [CommRing R]
    [Algebra k R] (M : Submonoid R) (A : Type) [CommRing A] [Algebra R A] [IsLocalization M A]
    [Algebra k A] [IsScalarTower k R A] (I : Ideal R)
    (h : FormallySmooth k $ R ⧸ I) :
    FormallySmooth k $ A ⧸ map (algebraMap R A) I := by
  let _a1 := map (algebraMap R A) I
  let _c0 := A ⧸ _a1
  have : FormallyEtale (R ⧸ I) _c0 :=
    of_isLocalization $ algebraMapSubmonoid (R ⧸ I) M
  have : IsScalarTower k (R ⧸ I) _c0 := by
    refine of_algebraMap_eq fun a => ?_
    rw [algebraMap_quotient_apply I a, algebraMap_quotient_map_mk I $ algebraMap k R a,
      algebraMap_quotient_apply _a1 a, algebraMap_apply k R A]
  exact m139 k (R ⧸ I) _c0

theorem map_algebraMap_eq_map_map_of_algEquiv {R L M : Type} [CommRing R] [CommRing L]
    [CommRing M] [Algebra R L] [Algebra R M] (e : L ≃ₐ[R] M) J :
    map (algebraMap R M) J
      = map e.toAlgHom.toRingHom (map (algebraMap R L) J) := by
  rw [map_map]
  exact congrArg (map · J) $ m48 fun r => sy_ $ e.commutes r

private theorem io_appLE_eq_topIso_inv {X : Sch} (U : Opn X)
    e : U.ι.appLE U ⊤ e = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE U U ⊤ e, Scheme.Opens.topIso_inv]
  exact congrArg X.presheaf.map $ unop_inj $ elim _ _

private theorem ofIdealTop_ideal_top {Y : Sch} J
    (hY : IsAffineOpen (⊤ : Opn Y)) :
    (ofIdealTop J).ideal ⟨⊤, hY⟩ = J :=by simp_all
section
variable (k : Type)
section
variable [Field k] (m : ℕ)
theorem affineSpaceGlobalSectionsHom_eq_eval2Hom :
    affineSpaceGlobalSectionsHom k m =
      MvPolynomial.eval₂Hom
        ((inv (GSpecIso $ CommRingCat.of k) ≫ appTop (affineSpaceFinToSpec k m)).hom)
        (fun i => AffineSpace.coord (Sp k) i) := by
  show (inv (GSpecIso $ m10 $ MvU m k) ≫
      (m69 (UFin m) $ m10 k).hom.appTop).hom = _
  rw [AffineSpace.SpecIso_hom_appTop, ← assoc, inv_hom_id, id_comp,
    hom_ofHom]

private theorem affineSpaceGlobalSectionsHom_X i :
    affineSpaceGlobalSectionsHom k m (MvPolynomial.X i) = AffineSpace.coord (Sp k) i := by
  rw [affineSpaceGlobalSectionsHom_eq_eval2Hom, MvPolynomial.eval₂Hom_X']

theorem affineSpaceGlobalSectionsHom_C__b2 b :
    affineSpaceGlobalSectionsHom k m (MvPolynomial.C b) =
      (affineSpaceFinToSpec k m).appTop.hom ((GSpecIso $ CommRingCat.of k).inv.hom b) := by
  rw [affineSpaceGlobalSectionsHom_eq_eval2Hom, MvPolynomial.eval₂Hom_C]
  rfl

def affineSpaceGlobalSectionsEquiv :
    MvU m k ≃+* Γ(affineSpaceFin k m, ⊤) where
  toFun := affineSpaceGlobalSectionsHom k m
  invFun := fun z =>
    (GSpecIso $ CommRingCat.of (MvU m k)).hom.hom
      ((AffineSpace.SpecIso (UFin m) $ CommRingCat.of k).inv.appTop.hom z)
  left_inv := by
    intro x
    have e : inv (GSpecIso $ CommRingCat.of (MvU m k)) ≫
        ((AffineSpace.SpecIso (UFin m) $ CommRingCat.of k).hom.appTop ≫
          (AffineSpace.SpecIso (UFin m) $ CommRingCat.of k).inv.appTop) ≫
        (GSpecIso $ CommRingCat.of (MvU m k)).hom = 𝟙 _ := by
      rw [← comp_appTop, inv_hom_id, id_appTop, id_comp,
        inv_hom_id]
    exact congrArg
      (fun ph_ : CommRingCat.of (MvU m k) ⟶
        CommRingCat.of (MvU m k) => ph_.hom x) e
  right_inv := by
    intro z
    have e : (AffineSpace.SpecIso (UFin m) $ CommRingCat.of k).inv.appTop ≫
        ((GSpecIso $ CommRingCat.of (MvU m k)).hom ≫
          inv (GSpecIso $ CommRingCat.of (MvU m k))) ≫
        (AffineSpace.SpecIso (UFin m) $ CommRingCat.of k).hom.appTop = 𝟙 _ := by
      rw [hom_inv_id, id_comp, ← comp_appTop, hom_inv_id,
        id_appTop]
    exact congrArg
      (fun ph_ : Γ(affineSpaceFin k m, ⊤) ⟶ Γ(affineSpaceFin k m, ⊤) => ph_.hom z) e
  map_mul' := (affineSpaceGlobalSectionsHom k m).map_mul
  map_add' := (affineSpaceGlobalSectionsHom k m).map_add
end

section
variable [CommRing k]
theorem sectionsAlgebraMap_apply_eq {X}
    (p : X ⟶ Sp k) U a :
    sectionsAlgebraMap k p U a =
      (appLE p ⊤ U $ le_preimage_top k p U).hom
        ((GSpecIso $ CommRingCat.of k).inv.hom a) := by
  rw [sectionsAlgebraMap_eq]
  rfl

section
variable {X W : Sch} (f : W ⟶ X) (p : X ⟶ Sp k) (U : Opn X)
theorem appLE_top_comp_app :
    appLE p ⊤ U (le_preimage_top k p U) ≫ f.app U
      = appLE (f ≫ p) ⊤ (pre f U) (le_preimage_top k (f ≫ p) $ pre f U) := by
  let _a0 := homOfLE $ le_preimage_top k p U
  have hn := f.c.naturality _a0.op
  let _a1 := f ≫ p
  show (p.app ⊤ ≫ pMap X _a0.op) ≫ f.app U
      = _a1.app ⊤ ≫ pMap W (homOfLE $ le_preimage_top k _a1 $ preU f U).op
  rw [assoc]
  exact congrArg (fun t => p.app ⊤ ≫ t) hn

private theorem app_sectionsAlgebraMap a :
    (f.app U).hom (sectionsAlgebraMap k p U a)
      = sectionsAlgebraMap k (f ≫ p) (pre f U) a := by
  rw [sectionsAlgebraMap_apply_eq, sectionsAlgebraMap_apply_eq]
  exact congrArg
    (fun ph_ : Γ(Sp k, ⊤) ⟶ Γ(W, preU f U) =>
      ph_.hom $ (GSpecIso $ m10 k).inv.hom a) $ appLE_top_comp_app k f p U
end
end
end

section
variable {X : Sch}
theorem mem_basicOpen_of_notMem_primeIdealOf {U}
    (hU : IsAffineOpen U) {x} (hx : x ∈ U) g
    (hg : g ∉ asIdeal (hU.primeIdealOf ⟨x, hx⟩)) : x ∈ basicOpen X g := by
  let _a0 := hU.primeIdealOf ⟨x, hx⟩
  have h3 : _a0 ∈ hU.fromSpec ⁻¹ᵁ (bOpn X g) := by
    rw [hU.fromSpec_preimage_basicOpen g]
    exact mpr_ (m209 g _) hg
  have h4 : hU.fromSpec.base _a0 ∈ bOpn X g := h3
  rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h4

theorem ideal_le_primeIdealOf (Z : ISD X) {U}
    (hU : IsAffineOpen U) {x} (hx : x ∈ U) (hxZ : x ∈ support Z) :
    Z.ideal ⟨U, hU⟩ ≤ asIdeal (hU.primeIdealOf ⟨x, hx⟩) := by
  have h :=
    mp (mem_support_iff_of_mem (I := Z) (U := ⟨U, hU⟩) hx) hxZ
  intro f hf
  by_contra hfp
  rw [mem_zeroLocus_iff] at h
  exact h f hf $ mem_basicOpen_of_notMem_primeIdealOf hU hx f hfp

section
variable {k : Type} [Field k]
theorem restrictIdeal_eq_coordIdeal_of_ideal_eq_span
    {p : X ⟶ Sp k} {U : Opn X} (hU : IsAffineOpen U) {m : ℕ}
    (c : EtaleChart p U m) (Z : ISD X) (S : FinSet m)
    (h : Z.ideal ⟨U, hU⟩ = span (c.coord '' (S : Set $ Fin m))) :
    restrictIdeal Z U = c.coordIdeal S := by
  have : IsAffine U.toScheme := hU
  have e : (⊤) ≤ opPre U U := fun z _ => z.2
  have hsets : (U.topIso.inv.hom) '' (c.coord '' S)
      = (c.map.appTop.hom) ''
        ((fun i => m9 (Sp k) $ up i) ''
          S) := by
    rw [image_image, image_image]
    refine congrArg (fun g : Fin m → Γ(oSch U, ⊤) => g '' S) ?_
    funext j
    rw [coord_def]
    exact Iso.hom_inv_id_apply U.topIso _
  rw [restrictIdeal_eq_comap_io, c.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  apply m170
  rw [p32 Z U.i ⟨U, hU⟩ ⟨⊤, isAffineOpen_top U.toScheme⟩ e,
    comap_ideal_top_eq_map_appTop, ofIdealTop_ideal_top, h,
    io_appLE_eq_topIso_inv, map_span, map_span]
  exact congrArg span hsets

section
variable (p : X ⟶ Sp k) {U : Opn X} (hU : IsAffineOpen U) {m : ℕ} (y : UFin m → (X.sec U)) (f : MvU m k →+* (X.sec U)) (hC : ∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p U a) (hX : ∀ i : UFin m, f (MvPolynomial.X i) = y i) (hf : f.Etale)
include hU hC hX hf
theorem etale_homOfVector_of_ringHom_etale :
    Etale
      (AffineSpace.homOfVector (U.i ≫ p) fun i => U.topIso.inv.hom (y i)) := by
  have : IsAffine U.toScheme := hU
  have hresp :=
    (isLocal_ringHomProperty
      (P := @Etale)).respectsIso
  let _a2 := opI U ≫ p
  have hover : m52 _a2 (fun i => U.topIso.inv.hom $ y i) ≫
      affineSpaceFinToSpec k m = _a2 := by simp
  have e1 : hAT (affineSpaceFinToSpec k m) ≫
      (m52 _a2 fun i => U.topIso.inv.hom $ y i).appTop
        = hAT _a2 := by
    rw [← comp_appTop, hover]
  let _a1 := (U.topIso.inv.hom).comp f
  have key : ((m52 _a2
        (fun i => U.topIso.inv.hom $ y i)).appTop.hom).comp (affineSpaceGlobalSectionsHom k m)
      = _a1 := by
    apply ringHom_ext
    intro b
    show (m52 _a2 fun i => U.topIso.inv.hom $ y i).appTop.hom
        (affineSpaceGlobalSectionsHom k m (m8 b))
        = U.topIso.inv.hom (f (m8 b))
    rw [affineSpaceGlobalSectionsHom_C__b2, hC, sectionsAlgebraMap_apply_eq]
    exact congrArg (fun ph_ : Γ(Sp k, ⊤) ⟶ Γ(oSch U, ⊤) =>
      ph_.hom ((GSpecIso (m10 k)).inv.hom b)) (tr_ e1 (appLE_top_comp_topIso_inv p U (le_preimage_top k p U)).symm)
    intro i
    show (m52 _a2 fun i => U.topIso.inv.hom $ y i).appTop.hom
        (affineSpaceGlobalSectionsHom k m (m7 i))
        = U.topIso.inv.hom (f (m7 i))
    rw [affineSpaceGlobalSectionsHom_X, hX]
    exact m87 _a2
      (fun i => U.topIso.inv.hom $ y i) i
  let _a3 := affineSpaceGlobalSectionsEquiv k m
  have hA : (m52 _a2 fun i => U.topIso.inv.hom $ y i).appTop.hom
      = _a1.comp _a3.symm.toRingHom := by
    refine m48 fun z => ?_
    let _a0 := _a3.symm z
    have h1 := congr_fun key _a0
    simp [comp_apply] at h1 ⊢
    rw [show affineSpaceGlobalSectionsHom k m _a0 = z from
      _a3.apply_symm_apply z] at h1
    exact h1
  rw [iff_of_isAffine (P := @Etale), hA]
  exact hresp.right _ _a3.symm
    (hresp.left f U.topIso.commRingCatIsoToRingEquiv.symm hf)

theorem exists_etaleChart_coord_eq :
    ∃ c : EtaleChart p U m, ∀ j, c.coord j = y (up j) := by
  refine ⟨ofCoords p U (fun i => U.topIso.inv.hom $ y i)
      (etale_homOfVector_of_ringHom_etale p hU y f hC hX hf), fun j => ?_⟩
  rw [coord_def, ofCoords_map, m87]
  exact inv_hom_id_apply U.topIso $ y $ up j
end

section
variable [hv3_0 : CharZero k] (p : X ⟶ Sp k) [Smooth p] (Z : ISD X) [Smooth (subschemeι Z ≫ p)]
include hv3_0
section
variable (x : X) (hx : x ∈ Z.support)
include hx
theorem exists_chart_ideal_eq_span_coord :
    ∃ (U : Opn X) (hU : IsAffineOpen U) (m : ℕ) (c : EtaleChart p U m) (S : FinSet m),
      x ∈ U ∧ Z.ideal ⟨U, hU⟩ = span (c.coord '' (S : Set $ Fin m)) := by
  obtain ⟨U0_, m, hxU0_, hU0_, ⟨c⟩⟩ := exists_etaleChart p x
  let _ : Algebra k U0_.sec := sectionsAlgebra k p U0_
  have hk :=
    algebraMap_sectionsAlgebra k p U0_
  let _a1 := MvU m k
  let _ : Algebra _a1 U0_.sec := c.algebra
  have : IsScalarTower k _a1 U0_.sec := c.isScalarTower
  have : FormallyEtale _a1 U0_.sec :=
    c.algebra_formallyEtale hU0_
  have : IsNoetherianRing U0_.sec := isNoetherianRing_sections k p ⟨U0_, hU0_⟩ hk
  have : DecidableEq $ UFin m := decEq _
  let P : PrimeSpectrum U0_.sec := hU0_.primeIdealOf ⟨x, hxU0_⟩
  have : IsNoetherianRing $ AtPrime P.asIdeal :=
    IsLocalization.isNoetherianRing P.asIdeal.primeCompl
      (AtPrime P.asIdeal) inferInstance
  let _a8 := siI Z ≫ p
  let _ : Algebra k Γ(subS Z, siPre Z U0_) :=
    sectionsAlgebra k _a8 $ siPre Z U0_
  have : FormallySmooth k Γ(subS Z, siPre Z U0_) :=
    formallySmooth_sections k _a8 (siPre Z U0_) (isAffineOpen_preimage_subschemeio Z hU0_)
      (algebraMap_sectionsAlgebra k _a8 $ siPre Z U0_)
  have hker :=
    Z.ker_subschemeι_app ⟨U0_, hU0_⟩
  have hsurj :=
    Z.subschemeι_app_surjective ⟨U0_, hU0_⟩
  let _a4 := X.sec U0_
  let Ph_ : _a4 →ₐ[k] Γ(subS Z, siPre Z U0_) :=
    { (Z.subschemeι.app U0_).hom with
      commutes' := fun a => app_sectionsAlgebraMap k Z.si p U0_ a }
  have hPhsurj : Surjective Ph_ := hsurj
  let _a3 := Z.ideal ⟨U0_, hU0_⟩
  have hfs : FormallySmooth k $ _a4 ⧸ _a3 := by
    have e1 :=
      quotientEquivAlgOfEq k hker.symm
    have e2 :=
      quotientKerAlgEquivOfSurjective hPhsurj
    exact Algebra.FormallySmooth.of_equiv (e1.trans e2).symm
  have : FormallySmooth k
      ((AtPrime P.asIdeal) ⧸
        map (algebraMap U0_.sec $ AtPrime P.asIdeal)
          _a3) :=
    formallySmooth_quotient_map_of_isLocalization k P.asIdeal.primeCompl
      (AtPrime P.asIdeal) _a3 hfs
  obtain ⟨g, w, T, hgq, hwI, hspanmap, hcoords, hfe⟩ :=
    exists_away_ideal_eq_span_and_formallyEtale k (UFin m) U0_.sec
      _a3 P.asIdeal (AtPrime P.asIdeal) $ ideal_le_primeIdealOf Z hU0_ hxU0_ hx
  let _ : Algebra k Γ(X, bOpn X g) := sectionsAlgebra k p $ bOpn X g
  let _a2 := algebraMap k $ X.sec U0_
  let _a5 := algebraMap U0_.sec $ Away g
  let _ : Algebra _a1 $ Away g :=
    toAlgebra $ MvPolynomial.eval₂Hom
      (_a5.comp _a2)
      (fun j => algebraMap U0_.sec (Away g) $ w j)
  have : FormallyEtale _a1 $ Away g := hfe
  let _a0 := (algebraMap U0_.sec Γ(X, bOpn X g)).comp $ algebraMap k U0_.sec
  let _ : Algebra _a1 Γ(X, bOpn X g) :=
    toAlgebra $ MvPolynomial.eval₂Hom
      _a0
      (fun j => algebraMap U0_.sec Γ(X, bOpn X g) $ w j)
  have : m215 g Γ(X, bOpn X g) := hU0_.isLocalization_basicOpen g
  let e : Away g ≃ₐ[_a4] Γ(X, bOpn X g) :=
    algEquiv (powers g) (Away g) Γ(X, bOpn X g)
  have hcomm : (e.toAlgHom.toRingHom).comp
      (MvPolynomial.eval₂Hom
        (_a5.comp _a2)
        (fun j => algebraMap U0_.sec (Away g) $ w j))
      = MvPolynomial.eval₂Hom
        _a0
        (fun j => algebraMap U0_.sec Γ(X, bOpn X g) $ w j) := by
    apply ringHom_ext
    intro a
    simp [comp_apply, MvPolynomial.eval₂Hom_C]
    exact e.commutes _
    intro i
    simp [MvPolynomial.eval₂Hom_X']
    exact e.commutes _
  have : FormallyEtale _a1 Γ(X, bOpn X g) :=
    of_equiv $ AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun z => congrArg (fun ph_ => ph_ z) hcomm
  have : FiniteType k Γ(X, bOpn X g) :=
    finiteType_sections k p ⟨bOpn X g, hU0_.basicOpen g⟩
      (algebraMap_sectionsAlgebra k p $ bOpn X g)
  have : IsScalarTower k _a1 Γ(X, bOpn X g) := by
    refine of_algebraMap_eq fun a => ?_
    have h1 : algebraMap _a1 Γ(X, bOpn X g)
        (algebraMap k _a1 a)
        = algebraMap U0_.sec Γ(X, bOpn X g) (algebraMap k U0_.sec a) := by
      rw [algebraMap_eq]
      exact MvPolynomial.eval₂Hom_C _ _ a
    rw [h1]
    exact (sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a).symm
  have : FiniteType _a1 Γ(X, bOpn X g) :=
    of_restrictScalars_finiteType k
      _a1 Γ(X, bOpn X g)
  have : FinitePresentation _a1
      Γ(X, bOpn X g) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : m121 _a1 Γ(X, bOpn X g) := by
    constructor <;> infer_instance
  have hC : ∀ a, (MvPolynomial.eval₂Hom
      _a0
      (fun j => algebraMap U0_.sec Γ(X, bOpn X g) $ w j))
        (m8 a) = sectionsAlgebraMap k p (bOpn X g) a := by
    intro a
    rw [MvPolynomial.eval₂Hom_C]
    exact sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a
  have hf :=
    ‹m121 _a1 Γ(X, bOpn X g)›
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p (hU0_.basicOpen g)
    (fun i => algebraMap U0_.sec Γ(X, bOpn X g) $ w i)
    (MvPolynomial.eval₂Hom
      _a0
      (fun j => algebraMap U0_.sec Γ(X, bOpn X g) $ w j))
    hC (MvPolynomial.eval₂Hom_X' _ _) hf
  refine ⟨bOpn X g, hU0_.basicOpen g, m, c', T.image down, mem_basicOpen_of_notMem_primeIdealOf hU0_ hxU0_ g hgq, ?_⟩
  have hmap : map (algebraMap U0_.sec Γ(X, bOpn X g)) _a3
      = Z.ideal ⟨bOpn X g, hU0_.basicOpen g⟩ := Z.map_ideal_basicOpen ⟨U0_, hU0_⟩ g
  have htrans : map (algebraMap U0_.sec Γ(X, bOpn X g))
        (span $ imS w (T))
      = map (algebraMap U0_.sec Γ(X, bOpn X g)) _a3 := by
    rw [map_algebraMap_eq_map_map_of_algEquiv e, map_algebraMap_eq_map_map_of_algEquiv e, hspanmap]
  have hSset : ((T.image down) : Set $ Fin m)
      = imS down (T) := coe_image
  have himg : (fun i : UFin m => algebraMap U0_.sec Γ(X, bOpn X g) $ w i)
      = c'.coord ∘ down := by
    funext i
    dsimp
    rw [hc' i.down]
  rw [← hmap, ← htrans, map_span]
  refine congrArg span ?_
  rw [image_image, hSset, ← image_comp]
  exact congrArg (fun h =>
    h '' (T)) himg

theorem exists_chart_restrictIdeal_eq_coordIdeal :
    ∃ (U : Opn X) (m : ℕ) (c : EtaleChart p U m) (S : FinSet m),
      x ∈ U ∧ IsAffineOpen U ∧ restrictIdeal Z U = c.coordIdeal S := by
  obtain ⟨U, hU, m, c, S, hxU, hspan⟩ := exists_chart_ideal_eq_span_coord p Z x hx
  exact ⟨U, m, c, S, hxU, hU, restrictIdeal_eq_coordIdeal_of_ideal_eq_span hU c Z S hspan⟩
end

theorem hasStrictNormalCrossingsWith_nil_of_smooth :
    HasStrictNormalCrossingsWith p Z [] := by
  unfold HasStrictNormalCrossingsWith
  intro x hx
  obtain ⟨U, m, c, S, hxU, hU, hres⟩ := exists_chart_restrictIdeal_eq_coordIdeal p Z x hx
  refine ⟨U, hxU, m, c, fun _ => none, S, ?_, ?_, ?_, hres⟩
  simp_all
  simp_all
  simp_all
end
end
end


section
variable {k : Type} [Field k]
theorem one_mem_of_mul_mem_of_dual_derivations {B : Type} [CommRing B]
    [Algebra k B] (I : Ideal B) (y1_ y2_ f a b : B) (de1 de2 : Derivation k B B)
    (hf : f ∈ I) (hy1_ : y1_ = a * f) (hy2_ : y2_ = b * f)
    (e11 : de1 y1_ = 1) (e12 : de1 y2_ = 0) (e21 : de2 y1_ = 0) (e22 : de2 y2_ = 1) :
    (1 : B) ∈ I := by
  have hpif := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have key : ∀ (δ : Derivation k B B) (c : B),
      (mk I) (δ $ c * f) =
        (mk I) c * (mk I) (δ f) := by simp_all
  let _a0 := (mk I) $ de1 f
  let _a2 := (mk I) a
  have k11 : _a2 * _a0 = 1 := by
    rw [← key de1 a, ← hy1_, e11, map_one]
  let _a1 := (mk I) $ de2 f
  have k12 : _a2 * _a1 = 0 := by
    rw [← key de2 a, ← hy1_, e21, map_zero]
  let _a3 := (mk I) b
  have k21 : _a3 * _a0 = 0 := by
    rw [← key de1 b, ← hy2_, e12, map_zero]
  have k22 : _a3 * _a1 = 1 := by
    rw [← key de2 b, ← hy2_, e22, map_one]
  let _a4 := (1 : B ⧸ I)
  have hone : _a4 = 0 := by
    calc _a4
        = (_a2 * _a0) *
            (_a3 * _a1) := by
          rw [k11, k22, one_mul]
      _ = (_a2 * _a1) *
            (_a3 * _a0) := by ring
      _ = 0 := by rw [k12, k21, mul_zero]
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  rwa [map_one]

theorem one_mem_of_coord_mem_span_singleton_of_ne {m : ℕ} {B : Type} [CommRing B]
    [Algebra (MvU m k) B] [Algebra k B]
    [IsScalarTower k (MvU m k) B]
    [FormallyEtale (MvU m k) B]
    (I : Ideal B) (h : B) (hI : I = span ({h} : Set B))
    (j1 j2_ : Fin m) (hne : j1 ≠ j2_)
    (hm1 : EtaleCoordinates.coord k (UFin m) B (up j1) ∈ I)
    (hm2 : EtaleCoordinates.coord k (UFin m) B (up j2_) ∈ I) :
    (1 : B) ∈ I := by
  let _c0 := UFin m
  have hh : h ∈ I := by simp_all
  rw [hI] at hm1 hm2
  obtain ⟨a, ha⟩ := mp_ mem_span_singleton' hm1
  obtain ⟨b, hb⟩ := mp_ mem_span_singleton' hm2
  have hne' : (up j1) ≠ up j2_ := fun hc =>
    hne $ congrArg down hc
  exact one_mem_of_mul_mem_of_dual_derivations I _ _ h a b
    (p27 k _c0 B $ up j1)
    (p27 k _c0 B $ up j2_)
    hh ha.symm hb.symm
    (partialDeriv_coord_self k _c0 B $ up j1)
    (partialDeriv_coord_of_ne k _c0 B _ _ hne')
    (partialDeriv_coord_of_ne k _c0 B _ _ hne'.symm)
    (partialDeriv_coord_self k _c0 B $ up j2_)
end

section
variable {X : Sch}
section
variable (D : ISD X) (W1 W2 : X.affineOpens) (hW : (W1 : Opn X) = (W2 : Opn X))
include hW
theorem ideal_eq_bot_of_opens_eq
    (h : D.ideal W1 = ⊥) : D.ideal W2 = ⊥ := by
  obtain rfl : W1 = W2 := m26 hW
  exact h

theorem exists_ideal_eq_span_singleton_of_opens_eq
    (h : ∃ f, D.ideal W2 = span ({f} : Set $ X.sec (W2 : Opn X))) :
    ∃ f, D.ideal W1 = span ({f} : Set $ X.sec (W1 : Opn X)) := by
  obtain rfl : W1 = W2 := m26 hW
  exact h
end

section
variable {k : Type} [Field k] [CharZero k] (p : X ⟶ Sp k) [Smooth p] (D : ISD X) (hD : IsSmoothDivisor p D)
include hD
theorem exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton (x : X) (hx : x ∈ D.support) :
    ∃ (U : Opn X) (m : ℕ) (c : EtaleChart p U m) (j : Fin m),
      x ∈ U ∧ restrictIdeal D U = c.coordIdeal ({j} : FinSet m) := by
  rw [isSmoothDivisor_iff] at hD
  obtain ⟨hcart, hsm⟩ := hD
  have : Smooth $ siI D ≫ p := hsm
  obtain ⟨U, m, c, S, hxU, hU, hDU⟩ := exists_chart_restrictIdeal_eq_coordIdeal p D x hx
  let _a3 := D.ideal ⟨U, hU⟩
  have hideal : _a3 = span (c.coord '' (S : Set $ Fin m)) :=
    c.ideal_eq_span_coord hU D S hDU
  obtain ⟨V, f, hxV, hfnzd, hVf⟩ := hcart x
  obtain ⟨g, g', hgg', hxg⟩ := exists_basicOpen_le_affine_inter hU V.2 x ⟨hxU, hxV⟩
  have hWaff := hU.basicOpen g
  let _a0 := pMap X (homOfLE $ X.basicOpen_le g).op
  have hresU : map _a0.hom
      _a3 = D.ideal ⟨bOpn X g, hWaff⟩ :=
    D.map_ideal_basicOpen ⟨U, hU⟩ g
  have hspan : D.ideal ⟨bOpn X g, hWaff⟩ =
      span ((fun j =>
        _a0.hom $ c.coord j) ''
          (S : Set $ Fin m)) := by
    rw [← hresU, hideal, map_span, ← image_comp]
    rfl
  have hxg' := hgg' ▸ hxg
  have hmap := D.map_ideal_basicOpen V g'
  rw [hVf, map_span, image_singleton] at hmap
  have hSne : S.Nonempty := by
    rcases eq_empty_or_nonempty S with rfl | hne
    exfalso
    have h0 : D.ideal ⟨bOpn X g, hWaff⟩ = ⊥ := by simp_all
    have hfzero := mp_ span_singleton_eq_bot $ tr_ hmap $ ideal_eq_bot_of_opens_eq D ⟨bOpn X g, hWaff⟩ (X.affineBasicOpen g') hgg' h0
    let _m1 := Γ(X, bOpn X g')
    have instLoc' :=
      V.2.isLocalization_basicOpen g'
    let _m0 := X.sec V
    have hfa : algebraMap _m0 _m1 f = 0 := hfzero
    obtain ⟨cc, hcc⟩ :=
      (eq_iff_exists (powers g')
        _m1).mp $ show
          algebraMap _m0 _m1 f =
            algebraMap _m0 _m1 0 by
          rw [hfa, map_zero]
    have hz : (cc : _m0) = 0 :=
      (mp_ mem_nonZeroDivisors_iff hfnzd).2 _ $ by rw [hcc, mul_zero]
    have hunit :=
      map_units _m1 cc
    rw [hz, map_zero] at hunit
    have h01 := mp_ isUnit_zero_iff hunit
    have h10 : (0 : stkX X x) = 1 := by
      have hq := congrArg (pGerm X (bOpn X g') x hxg').hom h01
      rwa [map_zero, map_one] at hq
    exact zero_ne_one h10
    exact hne
  have hcard1 : ∀ j1 ∈ S, ∀ j2_ ∈ S, j1 = j2_ := by
    intro j1 hj1_ j2_ hj2_
    by_contra hne
    obtain ⟨h, hI⟩ :=
      exists_ideal_eq_span_singleton_of_opens_eq D ⟨bOpn X g, hWaff⟩ (X.affineBasicOpen g') hgg'
        ⟨_, hmap.symm⟩
    let _a1 := MvU m k
    let _a5 := (_a0.hom).comp c.coordRingHom
    let instPB : Algebra _a1 Γ(X, bOpn X g) :=
      _a5.toAlgebra
    let instkB : Algebra k Γ(X, bOpn X g) :=
      (_a5.comp
        MvPolynomial.C).toAlgebra
    have instTower : IsScalarTower k _a1
        Γ(X, bOpn X g) :=
      of_algebraMap_eq fun _ => by
        rw [algebraMap_eq]
        rfl
    let instPA : Algebra _a1 U.sec := c.algebra
    have instFE1 : FormallyEtale _a1 U.sec :=
      c.algebra_formallyEtale hU
    have instScalarTower : IsScalarTower _a1 U.sec
        Γ(X, bOpn X g) :=
      of_algebraMap_eq fun _ => rfl
    have instLoc : IsLocalization.Away g Γ(X, bOpn X g) := hU.isLocalization_basicOpen g
    have instFE2 : FormallyEtale U.sec Γ(X, bOpn X g) :=
      of_isLocalization $ powers g
    have instFE3 : FormallyEtale _a1
        Γ(X, bOpn X g) :=
      comp _a1 U.sec
        Γ(X, bOpn X g)
    have hcoord : ∀ j,
        EtaleCoordinates.coord k (UFin m) Γ(X, bOpn X g) (up j) =
          _a0.hom (c.coord j) := by
      intro j
      rw [EtaleCoordinates.coord_def]
      show _a0.hom
          (c.coordRingHom $ MvPolynomial.X $ up j) = _
      rw [c.coordRingHom_X]
    have hm1 : EtaleCoordinates.coord k (UFin m) Γ(X, bOpn X g) (up j1) ∈
        D.ideal ⟨bOpn X g, hWaff⟩ := by
      rw [hcoord, hspan]
      exact subset_span ⟨j1, hj1_, rfl⟩
    have hm2 : EtaleCoordinates.coord k (UFin m) Γ(X, bOpn X g) (up j2_) ∈
        D.ideal ⟨bOpn X g, hWaff⟩ := by
      rw [hcoord, hspan]
      exact subset_span ⟨j2_, hj2_, rfl⟩
    have htop := mpr_ (eq_top_iff_one _) $ one_mem_of_coord_mem_span_singleton_of_ne (D.ideal ⟨bOpn X g, hWaff⟩) h hI j1 j2_ hne hm1 hm2
    have hle := ideal_le_primeIdealOf D hWaff hxg hx
    rw [htop] at hle
    exact (hWaff.primeIdealOf ⟨x, hxg⟩).isPrime.ne_top $ mp_ top_le_iff hle
  obtain ⟨j, hj⟩ :=
    card_eq_one.mp
      (le_antisymm (mpr_ card_le_one hcard1) $ mpr_ card_pos hSne)
  exact ⟨U, m, c, j, hxU, by rw [hDU, hj]⟩

theorem inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor :
    InStrictNormalCrossingPosition p [D] := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, fun x => ?_⟩
  simp_all
  by_cases hx : x ∈ spI D
  obtain ⟨U, m, c, j, hxU, hDU⟩ :=
    exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p D hD x hx
  refine ⟨U, hxU, m, c, fun _ => some j, ?_, ?_, ?_⟩
  simp_all
  simp_all
  simp_all
  obtain ⟨U, m, hxU, hUW, hUaff, hc⟩ :=
    exists_etaleChart_le p x
      (⟨D.supportᶜ, D.support.2.isOpen_compl⟩ : Opn X) hx
  obtain ⟨c⟩ := hc
  have hbot : support (D.comap U.i) = ⊥ := by
    rw [m19]
    refine le_antisymm ?_ bot_le
    intro y hy
    have h2 : opIb U y ∈ (U : Set X) := by
      rw [← q1 U]
      exact mem_range_self y
    exact absurd hy $ hUW h2
  have htop : restrictIdeal D U = ⊤ := by
    rw [restrictIdeal_eq_comap_io]
    exact mp_ (support_eq_bot_iff _) hbot
  refine ⟨U, hxU, m, c, fun _ => none, ?_, ?_, ?_⟩
  simp_all
  simp_all
  simp_all
end
end


section

variable {P : Sch}

section
variable {A B : Sch} (f : A ⟶ B)
theorem ker_ideal_eq_ker_appLE [QuasiCompact f]
    V :
    f.ker.ideal V = ker (appLE f (V : Opn B) (pre f (V : Opn B)) le_rfl).hom := by
  simp only [appLE_eq_app]
  simp

theorem ker_appLE_congr W
    {V1 V2} (h : V1 = V2) e1_ e2_ :
    ker (appLE f W V1 e1_).hom = ker (appLE f W V2 e2_).hom := by
  subst h
  rfl
end

private theorem comp_app_apply {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C)
    U x :
    ((f ≫ g).app U).hom x = (f.app $ pre g U).hom ((g.app U).hom x) := rfl

section
variable (H : ISD P) (Z : H.subscheme.IdealSheafData)
theorem ker_comp_subschemeio_ideal_eq_comap
    {U} (hU : IsAffineOpen U) :
    (subschemeι Z ≫ subschemeι H).ker.ideal ⟨U, hU⟩ =
      comap (H.subschemeι.appLE U (subschemeι H ⁻¹ᵁ U) le_rfl).hom
        (Z.ideal ⟨subschemeι H ⁻¹ᵁ U, isAffineOpen_preimage_subschemeio H hU⟩) := by
  have hopen : preU (siI Z ≫ siI H) U
      = siPre Z (preU H.si U) :=
    comp_preimage ..
  have hle := le_of_eq hopen.symm
  have hcomp : H.subschemeι.appLE U (siPre H U) le_rfl ≫
      Z.subschemeι.appLE (siPre H U)
        (siPre Z $ preU H.si U) le_rfl
      = appLE (siI Z ≫ siI H) U
        (siPre Z $ preU H.si U) hle := by
    simp [appLE_comp_appLE]
  rw [tr_ (ker_ideal_eq_ker_appLE (siI Z ≫ siI H) ⟨U, hU⟩) $ ker_appLE_congr (siI Z ≫ siI H) U hopen le_rfl hle, (st_ $ congrArg (fun I : H.subscheme.IdealSheafData => I.ideal ⟨siPre H U, isAffineOpen_preimage_subschemeio H hU⟩) $ q2 Z) $ ker_ideal_eq_ker_appLE Z.si ⟨siPre H U, isAffineOpen_preimage_subschemeio H hU⟩, ← hcomp, hom_comp]
  ext x
  simp [mem_ker, mem_comap, comp_apply]

theorem le_ker_comp_subschemeio :
    H ≤ (subschemeι Z ≫ subschemeι H).ker := by
  simp only [Scheme.Hom.ker]
  refine mpr_ le_ofIdeals_iff ?_
  intro U x hx
  simp only [mem_ker]
  have _i15 : (H.subschemeι.app U.1).hom x = 0 := by
    have hpt : (H.subschemeι.app U.1).hom x
        = (H.subschemeObjIso U).inv.hom (mk (H.ideal U) x) :=
      congrArg (hom · x) $ subschemeι_app H U
    rw [hpt, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  rw [comp_app_apply Z.si H.si U.1 x,
    _i15]
  exact map_zero _
end

variable {k : Type} [Field k]

end

section

variable {X : Sch} {k : Type} [Field k]

theorem etaleChart_numCoords_eq (p : X ⟶ Sp k)
    [LocallyOfFiniteType p] {U : Opn X} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) {m m' : ℕ} (c : EtaleChart p U m) (c' : EtaleChart p U m') : m = m' := by
  let instk := sectionsAlgebra k p U
  let instc := c.algebra
  let instc' := c'.algebra
  have instt :=
    c.isScalarTower
  have instt' :=
    c'.isScalarTower
  have instfe :=
    c.algebra_formallyEtale hU
  have instfe' :=
    c'.algebra_formallyEtale hU
  have instnt :=
    RingHom.domain_nontrivial (pGerm X U x hx).hom
  simpa using ((finrank_eq_card_basis $ basisKaehler k (UFin m) U.sec).symm.trans $ finrank_eq_card_basis $ basisKaehler k (UFin m') U.sec)

end

section

variable {P : Sch} {k : Type} [Field k]

section
variable (p : P ⟶ Sp k) (H : ISD P)
theorem etaleChart_numCoords_add_one_of_hypersurface
    [LocallyOfFiniteType $ subschemeι H ≫ p]
    {U} (hU : IsAffineOpen U) {n} (c : EtaleChart p U n) (j1 : Fin n)
    (hH : restrictIdeal H U = c.coordIdeal {j1})
    {V} (_hV : IsAffineOpen V) {m'}
    (c' : EtaleChart (subschemeι H ≫ p) V m')
    y (hyU : y ∈ subschemeι H ⁻¹ᵁ U) (hyV : y ∈ V) :
    m' + 1 = n := by
  have hymem : y ∈ (siPre H U) ⊓ V := ⟨hyU, hyV⟩
  obtain ⟨W, hWmem, hyW, hWle⟩ :=
    mp isBasis_iff_nbhd H.subscheme.isBasis_affineOpens hymem
  have key := etaleChart_numCoords_eq (siI H ≫ p) hWmem y hyW
    ((c.restrictToSubscheme hU H {j1} hH).restrict $ le_trans hWle inf_le_left) $ c'.restrict $ le_trans hWle inf_le_right
  have hcard := card_singleton j1
  have hlt := j1.isLt
  omega

def HasLocalCoordsOnSmoothHypersurface
    (N : Bdy P) (Z : H.subscheme.IdealSheafData) : Prop :=
  ∀ x ∈ (subschemeι Z ≫ subschemeι H).ker.support,
    ∃ (U : Opn P) (hU : IsAffineOpen U) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n)
      (j0_ : Fin n) (lab : ℕ → Option (Fin n)) (S : FinSet n),
      restrictIdeal H U = c.coordIdeal {j0_} ∧
      (∀ i, ∀ hi : i < length N, lab i = none → restrictIdeal (N[i]'hi) U = ⊤) ∧
      (∀ i, ∀ hi : i < length N, ∀ j : Fin n, lab i = some j →
        restrictIdeal (N[i]'hi) U = c.coordIdeal {j}) ∧
      (∀ i i' : ℕ, i < length N → i' < length N → ∀ j : Fin n,
        lab i = some j → lab i' = some j → i = i') ∧
      Z.ideal ⟨subschemeι H ⁻¹ᵁ U, isAffineOpen_preimage_subschemeio H hU⟩ =
        span
          ((fun j : Fin n =>
            (H.subschemeι.appLE U (subschemeι H ⁻¹ᵁ U) le_rfl).hom $ c.coord j) ''
              (S : Set $ Fin n))
end

section
variable {X1 : Sch}
theorem restrictIdeal_eq_coordIdeal_restrict {K : Type} [Field K]
    {q : X1 ⟶ Sp K} {U V : Opn X1} (hVU : V ≤ U) {m : ℕ}
    (c : EtaleChart q U m) (I : ISD X1) (S : FinSet m)
    (h : restrictIdeal I U = c.coordIdeal S) :
    restrictIdeal I V = (c.restrict hVU).coordIdeal S := by
  have h' : I.comap U.i = (coordSubspaceIdeal K m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_io, h, coordIdeal_eq_comap_coordSubspaceIdeal]
  rw [restrictIdeal_eq_comap_io, coordIdeal_eq_comap_coordSubspaceIdeal, restrict_map,
    comap_comp, ← h', ← comap_comp,
    Scheme.homOfLE_ι]

private theorem io_appLE_self_top_eq_topIso_inv (V : Opn X1)
    e :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact X1.presheaf_map_eq_of_parallel _ _
end

section
variable {Y : Sch}
section
variable (I : ISD Y)
section
variable {V : Opn Y} (hV : IsAffineOpen V)
theorem ideal_ne_top_of_mem_support {x} (hxV : x ∈ V) (hx : x ∈ support I) :
    I.ideal ⟨V, hV⟩ ≠ ⊤ := by
  obtain ⟨y, hy⟩ : ∃ y, I.subschemeι.base y = x := by
    have hxr : x ∈ range I.subschemeι.base := by simpa using hx
    exact hxr
  have hyV : y ∈ siPre I V := by simp_all
  have hnt :=
    RingHom.domain_nontrivial (I.subscheme.presheaf.germ (siPre I V) y hyV).hom
  intro htop
  have hker :=
    ker_subschemeι_app I ⟨V, hV⟩
  have hmem1 : 1 ∈ ker (I.subschemeι.app V).hom := by
    rw [hker, htop]
    exact mem_top
  have hzero : (1 : Γ(subS I, siPre I V)) = 0 := by
    have h' := RingHom.mem_ker.mp hmem1
    rwa [map_one] at h'
  exact one_ne_zero hzero

theorem ideal_eq_top_of_restrictIdeal_eq_top__b4 (h : restrictIdeal I V = ⊤) :
    I.ideal ⟨V, hV⟩ = ⊤ := by
  have hVaff : IsAffine V.toScheme := hV
  have htop : (⊤) ≤ opPre V V := by simp_all
  have key := I.comap_ideal_eq_map_appLE V.i ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ htop
  rw [io_appLE_self_top_eq_topIso_inv V htop] at key
  have h' : I.comap V.i = ⊤ := h
  rw [h'] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  rw [eq_top_iff_one]
  have hone : (1 : Γ(oSch V, ⊤)) ∈ map V.topIso.inv.hom (I.ideal ⟨V, hV⟩) := by
    rw [← key]
    exact mem_top
  obtain ⟨a, haI, hfa⟩ :=
    mp (mem_map_iff_of_surjective _ V.topIso.symm.commRingCatIsoToRingEquiv.surjective) hone
  have ha1 : a = 1 := V.topIso.symm.commRingCatIsoToRingEquiv.injective $ by rw [hfa, map_one]
  exact ha1 ▸ haI
end

theorem restrictIdeal_eq_top_of_le_of_eq_top {U V : Opn Y}
    (hVU : V ≤ U) (h : restrictIdeal I U = ⊤) : restrictIdeal I V = ⊤ := by
  have e1 : I.comap V.i = (I.comap U.i).comap (Y.homOfLE hVU) := by
    rw [← comap_comp, Scheme.homOfLE_ι]
  have h' : I.comap U.i = ⊤ := h
  show I.comap V.i = ⊤
  rw [e1, h']
  simp
end
end

theorem appLE_eq_appLE_comp_presheaf_map {X1 Y1 : Sch} (f : X1 ⟶ Y1) U
    {A B} e e' (hAB : A ≤ B) :
    f.appLE U A e = f.appLE U B e' ≫ X1.presheaf.map (homOfLE hAB).op := by
  let _a0 := pMap X1 (homOfLE e).op
  have h1 : f.appLE U A e = f.app U ≫ _a0 := rfl
  let _a1 := pMap X1 (homOfLE e').op
  have h2 : f.appLE U B e' = f.app U ≫ _a1 := rfl
  rw [h1, h2]
  have _i17 : ((f.app U) ≫ _a1) ≫ pMap X1 (homOfLE hAB).op = (f.app U) ≫ _a0 := by
    rw [assoc, ← m222, X1.presheaf_map_eq_of_parallel ((homOfLE e').op ≫ (homOfLE hAB).op) $ (homOfLE e).op]
  exact sy_ _i17

theorem io_appLE_apply_topIso_hom {X1 Y1 : Sch} (V : Opn X1)
    (g : toScheme V ⟶ Y1) {W} e1
    e2 x :
    (V.ι.appLE V W e1).hom (V.topIso.hom.hom $ g.appTop.hom x)
      = (appLE g ⊤ W e2).hom x := by
  have htop : (⊤) ≤ opPre V V := by simp_all
  have hb : appLE g (⊤) W e2
      = hAT g ≫ V.toScheme.presheaf.map (homOfLE le_top).op := by
    have h1 : appLE g (⊤) W e2
        = hAT g ≫ V.toScheme.presheaf.map (homOfLE e2).op := rfl
    rw [h1]
    exact congrArg (fun z => hAT g ≫ z) $ V.toScheme.presheaf_map_eq_of_parallel _ _
  rw [appLE_eq_appLE_comp_presheaf_map V.i V e1 htop le_top, io_appLE_self_top_eq_topIso_inv V htop, hb]
  simp only [hom_comp, comp_apply]
  rw [hom_inv_id_apply]

section
variable {X1 : Sch} {K : Type} [Field K] {q : X1 ⟶ Sp K} {U : Opn X1} {m : ℕ} (c : EtaleChart q U m)
theorem io_appLE_coord
    {W} e1
    e2 j :
    (U.ι.appLE U W e1).hom (c.coord j)
      = (c.map.appLE ⊤ W e2).hom
          (AffineSpace.coord (Sp K) (up j : UFin m)) := by
  rw [coord_def]
  exact io_appLE_apply_topIso_hom U c.map e1 e2 _

theorem restrictIdeal_eq_coordIdeal_of_isAffineOpen_ideal_eq_span (hU : IsAffineOpen U) (I : ISD X1) (S : FinSet m)
    (h : I.ideal ⟨U, hU⟩ = span (c.coord '' (S : Set $ Fin m))) :
    restrictIdeal I U = c.coordIdeal S := by
  have hcoord : (coordSubspaceIdeal K m S).ideal ⟨⊤, isAffineOpen_top $ affineSpaceFin K m⟩
      = span ((fun i =>
          m9 (Sp K) $ up i) '' (S : Set $ Fin m)) := by
    rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
    simp
  refine m29 $ funext ?_
  intro W
  have htop : (⊤) ≤ opPre U U := by simp_all
  have eW : W.1 ≤ opPre U U := le_trans le_top htop
  have eW' : W.1 ≤ c.map ⁻¹ᵁ (⊤ : Opn $ affineSpaceFin K m) := by
    intro y _
    trivial
  show (cmI I U.i).ideal W = (cmI (coordSubspaceIdeal K m S) c.map).ideal W
  rw [I.comap_ideal_eq_map_appLE U.i ⟨U, hU⟩ W eW,
    (coordSubspaceIdeal K m S).comap_ideal_eq_map_appLE c.map
      ⟨⊤, isAffineOpen_top $ affineSpaceFin K m⟩ W eW',
    h, hcoord, map_span, map_span, ← image_comp, ← image_comp]
  exact congrArg span $ image_congr fun j _ => io_appLE_coord c eW eW' j
end

section
variable {σ K : Type} [Field K] {j s} (hjs : j ≠ s)
include hjs
theorem mem_span_X_of_mul_X_mem r
    (hr : MvPolynomial.X s * r ∈ span {(MvPolynomial.X j : MvPolynomial σ K)}) :
    r ∈ span {(MvPolynomial.X j : MvPolynomial σ K)} := by
  classical
  obtain ⟨ps_, hpsC, hpsXj, hpsXi⟩ : ∃ ps_ : MvPolynomial σ K →+* MvPolynomial σ K,
      (∀ a : K, ps_ (m8 a) = m8 a) ∧
        ps_ (m7 j) = 0 ∧
        ∀ i : σ, i ≠ j → ps_ (m7 i) = m7 i := by
    refine ⟨MvPolynomial.eval₂Hom m8
        (fun i => if i = j then 0 else m7 i), ?_, ?_, ?_⟩
    intro a
    simp
    simp
    simp_all
  let _a0 := span {(m7 j : MvPolynomial σ K)}
  have key : (mk _a0).comp ps_
      = mk _a0 := by
    apply ringHom_ext
    simp_all
    intro i
    rw [comp_apply]
    by_cases h : i = j
    subst h
    rw [hpsXj, map_zero]
    exact sy_ $ Ideal.Quotient.eq_zero_iff_mem.mpr $ mem_span_singleton_self _
    rw [hpsXi i h]
  obtain ⟨t, ht⟩ := mp_ mem_span_singleton hr
  have h0 : ps_ (m7 s * r) = 0 := by simp_all
  rw [map_mul, hpsXi s $ m113 hjs] at h0
  have hpsr : ps_ r = 0 := by simp_all
  have h3 := congr_fun key r
  rw [comp_apply, hpsr, map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3.symm

theorem quotient_span_X_mul_X_cancel
    a b
    (h : (mk $ span {(MvPolynomial.X j : MvPolynomial σ K)})
            (MvPolynomial.X s) * a
        = (mk $ span {(MvPolynomial.X j : MvPolynomial σ K)})
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := m108 a
  obtain ⟨b', rfl⟩ := m108 b
  rw [← map_mul, ← map_mul, m202, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr $ mem_span_X_of_mul_X_mem hjs (a' - b') h
end

theorem mem_map_of_mul_mem_of_etale__b4 {Pr A : Type} [CommRing Pr] [CommRing A]
    {f : Pr →+* A} (hf : f.Etale) I w
    (hw : ∀ a b : Pr ⧸ I,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    x (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  let _a0 := (mk I) w
  let _a3 := map f I
  let _a1 := quotientMap _a3 f le_comap_map
  let _a2 := mk _a3
  have hy : _a1
        _a0 * _a2 x = 0 := by
    rw [quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let algInst : Algebra (Pr ⧸ I) $ A ⧸ _a3 :=
    _a1.toAlgebra
  have instEt : m121 (Pr ⧸ I) $ A ⧸ _a3 := etale_quotientMap hf I
  have instFlat : Flat (Pr ⧸ I) $ A ⧸ _a3 := inferInstance
  have hreg : IsSMulRegular (Pr ⧸ I) _a0 := fun a b h => hw a b h
  have hregA : IsSMulRegular (A ⧸ _a3) _a0 := hreg.of_flat
  have hsmul : _a0 • _a2 x
      = _a0 • 0 := by
    rwa [smul_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp $ hregA hsmul

theorem span_coord_eq_top_of_mem_span {X1 : Sch} {K : Type} [Field K]
    {q : X1 ⟶ Sp K} {V : Opn X1} (hV : IsAffineOpen V) {m : ℕ}
    (c : EtaleChart q V m) {j s : Fin m} (hjs : j ≠ s)
    (hmem : c.coord s ∈ Ideal.span {c.coord j}) :
    Ideal.span {c.coord j} = (⊤ : Ideal $ X1.sec V) := by
  classical
  let _a0 := span {(m7 (up j) : MvU m K)}
  have hmapspan : map c.coordRingHom
      _a0
      = span {c.coord j} := by
    rw [map_span, image_singleton, c.coordRingHom_X]
  have hju := fun h => hjs $ congrArg down h
  have hx' : c.coordRingHom (m7 $ up s) * 1
      ∈ m6 c.coordRingHom
        _a0 := by simp_all
  have hfin := mem_map_of_mul_mem_of_etale__b4 (c.coordRingHom_etale hV)
    _a0
    (m7 $ up s) (fun a b h => quotient_span_X_mul_X_cancel hju a b h) 1 hx'
  rw [hmapspan] at hfin
  exact mpr_ (eq_top_iff_one _) hfin

theorem hasStrictNormalCrossingsWith_ker_cons_of_hasLocalCoordsOnSmoothHypersurface [CharZero k] (p : P ⟶ Sp k)
    [Smooth p] (H : ISD P) (N : Bdy P)
    (Z : H.subscheme.IdealSheafData)
    (hN : InStrictNormalCrossingPosition p (H :: N))
    (_hZ : HasStrictNormalCrossingsWith (subschemeι H ≫ p) Z (N.map fun D => D.comap H.si))
    (hdata : HasLocalCoordsOnSmoothHypersurface p H N Z) :
    HasStrictNormalCrossingsWith p (subschemeι Z ≫ subschemeι H).ker (H :: N) := by
  classical
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hU, hxU, n, c, j0_, lab, S, h1, h2, h3, h4, h5⟩ := hdata x hx
  obtain ⟨-, hNpos⟩ := mp_ (inStrictNormalCrossingPosition_iff p (H :: N)) hN
  have hclash : ∀ i, i < lenL N → lab i ≠ some j0_ := by
    intro i hi hlabi
    obtain ⟨U', hxU', m', c', a', hinj', hnone', hsome'⟩ := (hNpos x).exists_etaleChart
    obtain ⟨V, hVb, hxV, hVle⟩ :=
      mp isBasis_iff_nbhd P.isBasis_affineOpens
        (show x ∈ U ⊓ U' from ⟨hxU, hxU'⟩)
    have hV := hVb
    have hVU' := le_trans hVle inf_le_right
    have hEqU : restrictIdeal (N[i]'hi) U = restrictIdeal H U := by
      rw [h3 i hi j0_ hlabi, h1]
    have hEqV :=
      restrictIdeal_eq_of_le_of_eq (le_trans hVle inf_le_left) hEqU
    have hproper : H.ideal ⟨V, hV⟩ ≠ ⊤ := by
      intro htop
      have hle := le_ker_comp_subschemeio H Z ⟨V, hV⟩
      rw [htop] at hle
      exact ideal_ne_top_of_mem_support _ hV hxV hx $ mp_ top_le_iff hle
    have hlen0 : 0 < lenL (H :: N) := by simp
    have hleni : i + 1 < lenL (H :: N) := by simpa using hi
    cases hop : a' 0 with
    | none =>
      refine hproper (ideal_eq_top_of_restrictIdeal_eq_top__b4 H hV
        (restrictIdeal_eq_top_of_le_of_eq_top H hVU' ?_))
      simpa using hnone' 0 hlen0 hop
    | some t0 =>
      cases hop1 : a' (i + 1) with
      | none =>
        have hNtop : restrictIdeal (N[i]'hi) U' = ⊤ := by
          simpa using hnone' (i + 1) hleni hop1
        have hVtop := restrictIdeal_eq_top_of_le_of_eq_top _ hVU' hNtop
        rw [hEqV] at hVtop
        exact hproper $ ideal_eq_top_of_restrictIdeal_eq_top__b4 H hV hVtop
      | some t1_ =>
        have hne : t0 ≠ t1_ := by
          intro hteq
          exact absurd (hinj' 0 hlen0 (i + 1) hleni t0 hop (by rw [hop1, hteq])) (by omega)
        have hHU' : restrictIdeal H U' = c'.coordIdeal {t0} := by
          simpa using hsome' 0 hlen0 t0 hop
        have hNU' : restrictIdeal (N[i]'hi) U' = c'.coordIdeal {t1_} := by
          simpa using hsome' (i + 1) hleni t1_ hop1
        let _a0 := c'.restrict hVU'
        have hHV2 : restrictIdeal H V = _a0.coordIdeal {t1_} := by
          rw [← hEqV]
          exact restrictIdeal_eq_coordIdeal_restrict hVU' c' (N[i]'hi) {t1_} hNU'
        have hA : H.ideal ⟨V, hV⟩ = span {_a0.coord t0} := by
          simpa using _a0.ideal_eq_span_coord hV H {t0} (restrictIdeal_eq_coordIdeal_restrict hVU' c' H {t0} hHU')
        have hB : H.ideal ⟨V, hV⟩ = span {_a0.coord t1_} := by
          simpa using _a0.ideal_eq_span_coord hV H {t1_} hHV2
        refine hproper $ tr_ hA (span_coord_eq_top_of_mem_span hV (c'.restrict hVU') hne ?_)
        rw [← hA, hB]
        exact mem_span_singleton_self _
  obtain ⟨a, ha0, has⟩ : ∃ a : ℕ → Option (Fin n), a 0 = some j0_ ∧ ∀ i, a (i + 1) = lab i :=
    ⟨fun i => if i = 0 then some j0_ else lab (i - 1), if_pos rfl, fun i => by
      show (if i + 1 = 0 then some j0_ else lab (i + 1 - 1)) = lab i
      rw [if_neg (by omega : ¬ (i + 1 = 0)), add_sub_cancel]⟩
  refine ⟨U, hxU, n, c, a, insert j0_ S, ?_, ?_, ?_, ?_⟩
  intro i hi j hj t hti htj
  cases i with
  | zero =>
    cases j with
    | zero => rfl
    | succ j' =>
      have heq : j0_ = t := by simp_all
      rw [has j', ← heq] at htj
      exact absurd htj $ hclash j' (by simpa using hj)
  | succ i' =>
    cases j with
    | zero =>
      have heq : j0_ = t := by simp_all
      rw [has i', ← heq] at hti
      exact absurd hti $ hclash i' (by simpa using hi)
    | succ j' =>
      rw [has i'] at hti
      rw [has j'] at htj
      have hij := h4 i' j' (by simpa using hi) (by simpa using hj) t hti htj
      omega
  intro i hi hn
  cases i with
  | zero =>
    rw [ha0] at hn
    exact absurd hn (by simp)
  | succ i' =>
    rw [has i'] at hn
    have hi' : i' < lenL N := by simpa using hi
    simpa using h2 i' hi' hn
  intro i hi t ht
  cases i with
  | zero =>
    have heq : j0_ = t := by simp_all
    rw [← heq]
    simpa using h1
  | succ i' =>
    rw [has i'] at ht
    have hi' : i' < lenL N := by simpa using hi
    simpa using h3 i' hi' t ht
  have _i16 : (siI Z ≫ siI H).ker.ideal ⟨U, hU⟩ = span (c.coord '' ((insert j0_ S : FinSet n) : Set (Fin n))) := by
    classical
    have happ : H.subschemeι.appLE U (siPre H U) le_rfl = H.subschemeι.app U := by
      rw [appLE_eq_app]
    have hsurj : Surjective (H.subschemeι.appLE U (siPre H U) le_rfl).hom := by
      rw [happ]
      exact subschemeι_app_surjective H ⟨U, hU⟩
    have hcomap : comap (H.subschemeι.appLE U (siPre H U) le_rfl).hom ⊥
        = H.ideal ⟨U, hU⟩ := by
      rw [happ, ← ker_eq_comap_bot]
      exact ker_subschemeι_app H ⟨U, hU⟩
    have key := ker_comp_subschemeio_ideal_eq_comap H Z hU
    rw [h5] at key
    rw [key, sy_ (image_image _ _ _), ← (map_span _ _), comap_map_of_surjective _ hsurj, hcomap, c.ideal_eq_span_coord hU H {j0_} h1, coe_singleton, image_singleton,
      coe_insert, image_insert_eq, span_insert]
    exact le_antisymm (sup_le le_sup_right le_sup_left) (sup_le le_sup_right le_sup_left)
  exact restrictIdeal_eq_coordIdeal_of_isAffineOpen_ideal_eq_span c hU _ (insert j0_ S)
    _i16

end


section

theorem algebraMap_mem_nonZeroDivisors_of_flat__b5 {R A : Type} [CommRing R]
    [CommRing A] [Algebra R A] [Flat R A] {r} (hr : r ∈ nonZeroDivisors R) :
    algebraMap R A r ∈ nonZeroDivisors A := by
  have key : ∀ x, algebraMap R A r * x = 0 → x = 0 := by
    intro x hx
    have hsm : r • x = r • 0 := by
      rwa [smul_zero, smul_def]
    exact isSMulRegular_of_nonZeroDivisors hr hsm
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun x hx => key x (by rw [mul_comm]; exact hx)⟩

theorem coord_mem_nonZeroDivisors_of_isAffineOpen {X : Sch} {k : Type} [Field k]
    {p : X ⟶ Sp k} {U : Opn X} {m : ℕ} (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (j : Fin m) :
    c.coord j ∈ nonZeroDivisors ↑(X.presheaf.obj $ op U) := by
  let _c0 := MvU m k
  let _c1 := pObj X $ op U
  let _ := c.algebra
  have :=
    c.algebra_etale hU
  have : Flat _c0 _c1 :=
    inferInstance
  have hXne : (m7 (up j) : MvU m k) ≠ 0 :=
    X_ne_zero _
  have key : (algebraMap _c0 _c1)
      (m7 $ up j) ∈ nonZeroDivisors _c1 :=
    algebraMap_mem_nonZeroDivisors_of_flat__b5 $ mem_nonZeroDivisors_of_ne_zero hXne
  rw [c.algebraMap_eq_coordRingHom] at key
  rwa [c.coordRingHom_X j] at key

end

section

variable {R : Type} [CommRing R]

theorem exists_unit_mul_of_span_eq {a b : R} (hb : b ∈ nonZeroDivisors R)
    (h : span ({a} : Set R) = span ({b} : Set R)) :
    ∃ u : Rˣ, a = (u : R) * b := by
  have ha : a ∈ span ({b} : Set R) := by
    rw [← h]
    exact mem_span_singleton_self a
  have hb' : b ∈ span ({a} : Set R) := by
    rw [h]
    exact mem_span_singleton_self b
  obtain ⟨c, hc⟩ := mp_ mem_span_singleton' ha
  obtain ⟨d, hd⟩ := mp_ mem_span_singleton' hb'
  have hzero : (d * c - 1) * b = 0 := by
    have hx : d * c * b = b := by rw [mul_assoc, hc, hd]
    rw [sub_mul, one_mul, hx, sub_self]
  have hdc := mp_ sub_eq_zero $ (an2 $ mp_ mem_nonZeroDivisors_iff hb) _ hzero
  refine ⟨⟨c, d, by rw [mul_comm]; exact hdc, hdc⟩, sy_ hc⟩

end

section

variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

theorem derivation_mapsTo_span_self {B : Type} [CommRing B] [Algebra k B]
    (D : Derivation k B B) (h : B) (hD : D h = 0) :
    ∀ x ∈ span ({h} : Set B), D x ∈ span ({h} : Set B) := by
  intro x hx
  obtain ⟨c, rfl⟩ := mp_ mem_span_singleton' hx
  rw [leibniz, hD, smul_zero, zero_add, smul_eq_mul]
  exact mul_mem_right _ _ $ mem_span_singleton_self h

section
variable (pi_ : R →ₐ[k] S)
theorem algHom_map_derivation_eq_zero (h : R)
    (hker : ker pi_.toRingHom = span ({h} : Set R))
    (D : Derivation k R R) (hD : D h = 0) :
    ∀ r : R, pi_ r = 0 → pi_ (D r) = 0 := by
  intro r hr
  have hrk : r ∈ span ({h} : Set R) := by
    rwa [← hker]
  have h2 := derivation_mapsTo_span_self D h hD r hrk
  rw [← hker] at h2
  exact RingHom.mem_ker.mp h2

section
variable (hpi_ : Surjective pi_) (h : R) (hker : ker pi_.toRingHom = span ({h} : Set R)) (D : Derivation k R R) (hD : D h = 0)
def liftDerivationOfKerEqSpan : Derivation k S S :=
  D.liftOfSurjective hpi_ $ algHom_map_derivation_eq_zero pi_ h hker D hD

theorem liftDerivationOfKerEqSpan_apply (r : R) :
    liftDerivationOfKerEqSpan pi_ hpi_ h hker D hD (pi_ r) = pi_ (D r) :=
  D.liftOfSurjective_apply hpi_ (algHom_map_derivation_eq_zero pi_ h hker D hD) r
end
end

end

section

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem det_eq_det_submatrix_succ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ b : Fin $ n + 1, M 0 b = if b = 0 then (1 : R) else 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_row_zero, sum_eq_single (0 : Fin $ n + 1)]
  simp_all
  simp_all
  simp_all

section
variable (e : ι ≃ Fin (n + 1)) (M : Matrix ι ι R)
theorem det_eq_det_submatrix_of_row_eq_single
    (h : ∀ b : ι, M (e.symm 0) b = if b = e.symm 0 then (1 : R) else 0) :
    M.det =
      (M.submatrix (fun i : Fin n => e.symm i.succ) fun i : Fin n => e.symm i.succ).det := by
  have hN : ∀ b : Fin $ n + 1,
      (M.submatrix e.symm e.symm) 0 b = if b = 0 then 1 else 0 := by simp_all
  have h2 := det_eq_det_submatrix_succ (M.submatrix e.symm e.symm) hN
  rw [det_submatrix_equiv_self] at h2
  rw [h2, submatrix_submatrix]
  rfl

theorem det_eq_det_submatrix_of_col_eq_single
    (h : ∀ a : ι, M a (e.symm 0) = if a = e.symm 0 then (1 : R) else 0) :
    M.det =
      (M.submatrix (fun i : Fin n => e.symm i.succ) fun i : Fin n => e.symm i.succ).det := by
  have h1 := det_eq_det_submatrix_of_row_eq_single e M.transpose h
  rw [det_transpose] at h1
  rw [h1, ← transpose_submatrix, det_transpose]
end

end

section

variable {X : Sch} {k : Type} [Field k]

theorem exists_unit_mul_coord_of_span_eq (p : X ⟶ Sp k) {U : Opn X}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (j : Fin n) (g : (X.sec U))
    (h : span ({g} : Set $ X.sec U) = span ({c.coord j} : Set $ X.sec U)) :
    ∃ v : ((X.sec U))ˣ, g = (v : (X.sec U)) * c.coord j :=
  exists_unit_mul_of_span_eq (coord_mem_nonZeroDivisors_of_isAffineOpen hU c j) h

end


section
variable (R S : Type) [CommRing R] [CommRing S]
section
variable [Algebra R S] [HasGoingDown R S]
theorem exists_prime_le_under_eq_of_hasGoingDown (p : Ideal R) [p.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hle : p ≤ under R Q) :
    ∃ P : Ideal S, P ≤ Q ∧ P.IsPrime ∧ under R P = p := by
  rcases eq_or_lt_of_le hle with h | h
  exact ⟨Q, le_rfl, ‹Q.IsPrime›, sy_ h⟩
  obtain ⟨P, hPQ, hP, hlo⟩ :=
    Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (R := R) Q h
  exact ⟨P, hPQ, hP, hlo.over.symm⟩

theorem exists_ltSeries_le_of_hasGoingDown n :
    ∀ (p : LTSeries $ PrimeSpectrum R), p.length = n →
      ∀ Q, Q.IsPrime → p.last.asIdeal ≤ under R Q →
        ∃ q : LTSeries $ PrimeSpectrum S, q.length = n ∧ q.last.asIdeal ≤ Q ∧
          under R q.last.asIdeal = p.last.asIdeal := by
  induction n with
  | zero =>
      intro p hp Q hQ hle
      have := hQ
      have := p.last.isPrime
      obtain ⟨P, hPQ, hP, hunder⟩ := exists_prime_le_under_eq_of_hasGoingDown R S p.last.asIdeal Q hle
      exact ⟨RelSeries.singleton _ ⟨P, hP⟩, rfl, hPQ, hunder⟩
  | succ n ih =>
      intro p hp Q hQ hle
      have := hQ
      have := p.last.isPrime
      obtain ⟨P, hPQ, hP, hunder⟩ := exists_prime_le_under_eq_of_hasGoingDown R S p.last.asIdeal Q hle
      have hlen : p.length ≠ 0 := by omega
      have hltI :=
        (asIdeal_lt_asIdeal _ _).mpr $ p.eraseLast_last_rel_last hlen
      have hlen' : p.eraseLast.length = n := by
        have := RelSeries.eraseLast_length p
        omega
      have hle' : p.eraseLast.last.asIdeal ≤ under R P := by
        rw [hunder]
        exact le_of_lt hltI
      obtain ⟨q, hq1, hq2, hq3⟩ := ih p.eraseLast hlen' P hP hle'
      have hne : q.last.asIdeal ≠ P := by
        intro h
        rw [h, hunder] at hq3
        exact (ne_of_lt hltI) hq3.symm
      have hrel : q.last < (⟨P, hP⟩ : PrimeSpectrum S) :=
        (asIdeal_lt_asIdeal _ _).mp $ lt_of_le_of_ne hq2 hne
      refine ⟨q.snoc ⟨P, hP⟩ hrel, ?_, ?_, ?_⟩
      simp_all
      simp_all
      simp_all
end

theorem spanFinrank_map_le [IsNoetherianRing R]
    [Algebra R S] (I : Ideal R) :
    (map (algebraMap R S) I).spanFinrank ≤ I.spanFinrank := by
  obtain ⟨s, hcard, hspan⟩ := exists_span_set_card_eq_spanRank I
  have hIfg := m187 I
  have hslt : Cardinal.mk s < aleph0 := by simp_all
  let _m0 := algebraMap R S
  let _a0 := Cardinal.mk $ imS _m0 s
  have h1 : (map _m0 I).spanRank ≤ _a0 := by
    rw [← hspan, map_span]
    exact spanRank_span_le_card _
  have h2 := mk_image_le_lift (f := algebraMap R S) (s := s)
  have hliftlt :=
    mpr lift_lt_aleph0 hslt
  have h3 : toNat _a0 ≤
      toNat (Cardinal.mk s) := by
    have := toNat_le_toNat h2 hliftlt
    rwa [toNat_lift, toNat_lift] at this
  calc (map _m0 I).spanFinrank
      = toNat (map _m0 I).spanRank :=
        Submodule.spanFinrank.eq_def _
    _ ≤ toNat _a0 := toNat_le_toNat h1 $ mp lift_lt_aleph0 $ lt_of_le_of_lt h2 hliftlt
    _ ≤ toNat (Cardinal.mk s) := h3
    _ = I.spanFinrank := by rw [hcard, ← Submodule.spanFinrank.eq_def]

section
variable [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S]
section
variable [hv7_0 : IsLocalHom (algebraMap R S)] [hv7_1 : EssFiniteType R S] [hv7_2 : FormallyUnramified R S] [hv7_3 : Flat R S]
include hv7_0 hv7_1 hv7_2 hv7_3
theorem ringKrullDim_eq_of_flat_formallyUnramified :
    ringKrullDim S = ringKrullDim R := by
  have : IsLocalRing R := inferInstance
  have : IsNoetherianRing R := inferInstance
  have : HasGoingDown R S := inferInstance
  have h1 := by
    have key : ∀ p : LTSeries $ PrimeSpectrum R, p.length ≤ ringKrullDim S := by
      intro p
      have hp := fun x hx => map_nonunit (algebraMap R S) x $ (le_maximalIdeal p.last.isPrime.ne_top) hx
      obtain ⟨q, hq1, -, -⟩ :=
        exists_ltSeries_le_of_hasGoingDown R S p.length p rfl (maximalIdeal S)
          inferInstance hp
      calc (p.length : WithBot ENat) = (q.length : WithBot ENat) := by rw [hq1]
        _ ≤ ringKrullDim S := Order.LTSeries.length_le_krullDim q
    exact iSup_le key
  refine le_antisymm ?_ h1
  have : IsNoetherianRing R := inferInstance
  have hfr : (maximalIdeal S).spanFinrank ≤
      (maximalIdeal R).spanFinrank := by
    rw [(map_maximalIdeal (R := R) (S := S)).symm]
    exact spanFinrank_map_le R S _
  rw [← (spanFinrank_maximalIdeal (R := R)), ← maximalIdeal_height_eq_ringKrullDim (R := S)]
  exact_mod_cast (le_trans (height_le_spanFinrank _ $ (isMaximal S).ne_top) $ mpr_ cast_le hfr)

theorem isRegularLocalRing_of_flat_formallyUnramified :
    _root_.IsRegularLocalRing S := by
  have : IsLocalRing R := inferInstance
  have : IsNoetherianRing R := inferInstance
  have h4 : (maximalIdeal S).spanFinrank
      ≤ (maximalIdeal R).spanFinrank := by
    rw [(map_maximalIdeal (R := R) (S := S)).symm]
    exact spanFinrank_map_le R S _
  have hle1 : ringKrullDim S ≤ ((maximalIdeal S).spanFinrank : WithBot ENat) := by
    rw [← maximalIdeal_height_eq_ringKrullDim (R := S)]
    exact_mod_cast (height_le_spanFinrank _ (isMaximal S).ne_top)
  refine mpr_ (isRegularLocalRing_iff S) $ le_antisymm ?_ hle1
  rw [ringKrullDim_eq_of_flat_formallyUnramified R S, ← (isRegularLocalRing_iff R).mp inferInstance]
  exact_mod_cast h4
end
end
end

theorem isRegularLocalRing_stalk_of_iso_spec {X : Sch} (R : Type) [CommRing R]
    (hreg : ∀ p hp,
      _root_.IsRegularLocalRing $ @AtPrime R _ p hp)
    (e : X ≅ Sp R) x :
    _root_.IsRegularLocalRing $ X.presheaf.stalk x := by
  let y : PrimeSpectrum R := e.hom.base x
  have h1 :=
    hreg y.asIdeal $ y.isPrime
  let _s0 := (structureSheaf R).presheaf.stalk y
  have h2 :=
    StructureSheaf.IsLocalization.to_stalk R y
  have e2 :=
    (algEquiv y.asIdeal.primeCompl (AtPrime y.asIdeal)
      _s0).toRingEquiv
  have h3 :=
    of_ringEquiv e2
  have h4 : IsIso $ e.hom.stalkMap x := inferInstance
  have e3 : _s0 ≃+* (stkX X x) :=
    (asIso $ e.hom.stalkMap x).commRingCatIsoToRingEquiv
  exact of_ringEquiv e3

section
variable {Y} (R) (e : Y ≅ Spec R) (y : Y)
noncomputable def pointOfIsoSpec :
    PrimeSpectrum ↥R :=
  e.hom.base y

end

section
variable {al_ : Type} [TopologicalSpace al_]
theorem eq_closure_of_mem_irreducibleComponents
    {V} (hVopen : IsOpen V) (hVirr : IsIrreducible V) {T}
    (hT : T ∈ irreducibleComponents al_) {x} (hxV : x ∈ V) (hxT : x ∈ T) : T = closure V := by
  have hsub : T ⊆ closure V := by
    intro y hy
    rw [mem_closure_iff]
    intro o ho hyo
    obtain ⟨z, -, hzo, hzV⟩ := hT.1.2 o V ho hVopen ⟨y, hy, hyo⟩ ⟨x, hxT, hxV⟩
    exact ⟨z, hzo, hzV⟩
  exact le_antisymm hsub $ an2 hT hVirr.closure hsub

theorem exists_isOpen_isIrreducible_of_unique_irreducibleComponent
    (hfin : (irreducibleComponents al_).Finite) {T0} (hT0_ : IsIrreducible T0) {z}
    (_hz : z ∈ T0) (huniq : ∀ T ∈ irreducibleComponents al_, z ∈ T → T = T0) :
    ∃ W, IsOpen W ∧ IsIrreducible W ∧ z ∈ W := by
  have hScl : IsClosed (⋃₀ {T : Set al_ | T ∈ irreducibleComponents al_ ∧ z ∉ T}) := by
    rw [sUnion_eq_biUnion]
    exact isClosed_biUnion (m197 hfin fun T hT => an1 hT)
      (fun T hT => isClosed_of_mem_irreducibleComponents _ hT.1)
  have hzW : z ∈ (⋃₀ {T : Set al_ | T ∈ irreducibleComponents al_ ∧ z ∉ T})ᶜ := by
    intro hcon
    obtain ⟨T, hTS, hzT⟩ := hcon
    exact an2 hTS hzT
  have hWT : (⋃₀ {T : Set al_ | T ∈ irreducibleComponents al_ ∧ z ∉ T})ᶜ ⊆ T0 := by
    intro y hy
    have hc :=
      irreducibleComponent_mem_irreducibleComponents y
    have hzc : z ∈ irreducibleComponent y := by
      by_contra hcon
      exact hy ⟨irreducibleComponent y, ⟨hc, hcon⟩, mem_irreducibleComponent⟩
    rw [← huniq _ hc hzc]
    exact mem_irreducibleComponent
  refine ⟨_, hScl.isOpen_compl, ⟨⟨z, hzW⟩, ?_⟩, hzW⟩
  intro u v hu hv hu' hv'
  obtain ⟨a, haW, hau⟩ := hu'
  obtain ⟨b, hbW, hbv⟩ := hv'
  obtain ⟨c, -, ⟨hcu, hcW⟩, hcv, -⟩ :=
    hT0_.2 (u ∩ (⋃₀ {T : Set al_ | T ∈ irreducibleComponents al_ ∧ z ∉ T})ᶜ)
      (v ∩ (⋃₀ {T : Set al_ | T ∈ irreducibleComponents al_ ∧ z ∉ T})ᶜ)
      (hu.inter hScl.isOpen_compl) (hv.inter hScl.isOpen_compl)
      ⟨a, hWT haW, hau, haW⟩ ⟨b, hWT hbW, hbv, hbW⟩
  exact ⟨c, hcW, hcu, hcv⟩
end

theorem isRegularLocalRing_stalk_of_stalkMap_flat_formallyUnramified {Y Z : Sch} (f : Y ⟶ Z) y
    (hZ : _root_.IsRegularLocalRing $ Z.presheaf.stalk $ f.base y)
    (hflat : (f.stalkMap y).hom.Flat)
    (heft : (f.stalkMap y).hom.EssFiniteType)
    (hfu : (f.stalkMap y).hom.FormallyUnramified) :
    _root_.IsRegularLocalRing $ Y.presheaf.stalk y := by
  let _c0 := stkX Z $ bsM f y
  let _ :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom $ algebraMap _c0 $ stkX Y y :=
    inferInstanceAs $ IsLocalHom (f.stalkMap y).hom
  have : Flat _c0 $ stkX Y y := hflat
  have : EssFiniteType _c0 $ stkX Y y := heft
  have : FormallyUnramified _c0 $ stkX Y y := hfu
  have : IsNoetherianRing $ stkX Y y :=
    Algebra.EssFiniteType.isNoetherianRing
      _c0 $ stkX Y y
  exact isRegularLocalRing_of_flat_formallyUnramified
    _c0 $ stkX Y y

theorem isRegularLocalRing_stalk_affineSpace (k : Type) [Field k] (n : Type) [Finite n]
    x :
    _root_.IsRegularLocalRing $ (AffineSpace n $ Sp k).presheaf.stalk x :=
  isRegularLocalRing_stalk_of_iso_spec (MvPolynomial n k)
    (fun p hp => by have := hp; infer_instance)
    (m69 n $ m10 k) x

section
variable {X : Sch} {k : Type} [Field k] (p : X ⟶ Sp k)
theorem isRegularLocalRing_stalk_of_smooth [Smooth p] x :
    _root_.IsRegularLocalRing $ X.presheaf.stalk x := by
  obtain ⟨U, m, hxU, -, ⟨c⟩⟩ := exists_etaleChart p x
  have := c.isEtale
  have := isRegularLocalRing_stalk_of_stalkMap_flat_formallyUnramified c.map (⟨x, hxU⟩ : U) (isRegularLocalRing_stalk_affineSpace k (UFin m) _) (stalkMap c.map (⟨x, hxU⟩ : U)) (AlgebraicGeometry.LocallyOfFiniteType.stalkMap c.map (⟨x, hxU⟩ : U)) $ AlgebraicGeometry.FormallyUnramified.stalkMap c.map (⟨x, hxU⟩ : U)
  exact of_ringEquiv (U.stalkIso (⟨x, hxU⟩ : U)).commRingCatIsoToRingEquiv

theorem isDomain_stalk_of_smooth [Smooth p] x :
    IsDomain $ X.presheaf.stalk x := by
  have :=
    isRegularLocalRing_stalk_of_smooth p x
  exact isDomain _


theorem isReduced_of_smooth [Smooth p] :
    IsReduced X := by
  have : ∀ x, _root_.IsReduced $ stkX X x := by
    intro x
    have := isDomain_stalk_of_smooth p x
    infer_instance
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk X

theorem smooth_isDomain_stalk (hp : Smooth p) x :
    IsDomain $ X.presheaf.stalk x := by
  exact isDomain_stalk_of_smooth p x

theorem smooth_isReduced (hp : Smooth p) :
    IsReduced X := by
  exact isReduced_of_smooth p
end

theorem exists_isOpen_isIrreducible_of_unique_minimal_prime_le {A : Type} [CommRing A]
    [IsNoetherianRing A] (P : PrimeSpectrum A) (K : Ideal A) (hK : K.IsPrime)
    (hmin : ∀ q : Ideal A, q.IsPrime → q ≤ asIdeal P → K ≤ q) :
    ∃ W : Set $ PrimeSpectrum A, IsOpen W ∧ IsIrreducible W ∧ P ∈ W := by
  let _a0 := PrimeSpectrum.zeroLocus (K : Set A)
  have hT0irr : IsIrreducible _a0 := by
    rw [isIrreducible_iff_vanishingIdeal_isPrime,
      vanishingIdeal_zeroLocus_eq_radical, hK.radical]
    exact hK
  have hPT0 : P ∈ _a0 := by
    rw [mem_zeroLocus]
    exact fun a ha => hmin P.asIdeal P.isPrime le_rfl ha
  refine exists_isOpen_isIrreducible_of_unique_irreducibleComponent m169 hT0irr hPT0 ?_
  intro T hT hPmem
  have hTeq : PrimeSpectrum.zeroLocus ((m184 T) : Set A)
      = T := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, (isClosed_of_mem_irreducibleComponents _ hT).closure_eq]
  have hqP := fun a ha =>
    (mem_vanishingIdeal T a).mp ha P hPmem
  have hTsub : T ⊆ _a0 := by
    rw [← hTeq]
    exact zeroLocus_anti_mono $ SetLike.coe_subset_coe.mpr $ hmin _ (PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hT.1) hqP
  exact le_antisymm hTsub $ an2 hT hT0irr hTsub

theorem exists_isOpen_isIrreducible_of_iso_spec_of_isDomain_stalk {Y : Sch} (R : CRC)
    [IsNoetherianRing ↥R] (e : Y ≅ Spec R) (y : Y)
    (hdom : IsDomain ↥(Y.presheaf.stalk y)) :
    ∃ V, IsOpen V ∧ IsIrreducible V ∧ y ∈ V := by
  let _a0 := pointOfIsoSpec R e y
  let _c0 := AtPrime _a0.asIdeal
  have hPp := _a0.isPrime
  have hdomL : IsDomain $ AtPrime (pointOfIsoSpec R e y).asIdeal := by
    let _c0 := pointOfIsoSpec R e y
    have hp : _c0.asIdeal.IsPrime := _c0.isPrime
    let _a0 := (structureSheaf R).presheaf.stalk _c0
    have h4 : IsIso $ e.hom.stalkMap y := inferInstance
    exact (((algEquiv _c0.asIdeal.primeCompl (AtPrime _c0.asIdeal) _a0).toRingEquiv).trans $ (asIso $ e.hom.stalkMap y).commRingCatIsoToRingEquiv).toMulEquiv.isDomain _
  have hbot : (⊥ : Ideal _c0).IsPrime :=
    isPrime_bot
  let _a3 := comap (algebraMap R _c0) (⊥)
  let _m0 := _a3
  have hKp : _m0.IsPrime :=
    comap_isPrime _ _
  have hmin : ∀ q : Ideal R, q.IsPrime → q ≤ asIdeal _a0 →
      _a3 ≤ q := by
    intro q hq hqP a ha
    have h0 := by
      simpa [mem_comap, Submodule.mem_bot] using ha
    have h1 : algebraMap R _c0 a
        = algebraMap R _c0 0 := by
      rw [h0, map_zero]
    obtain ⟨c, hc⟩ := (eq_iff_exists
      _a0.asIdeal.primeCompl
      _c0).mp h1
    rw [mul_zero] at hc
    have hmem : c * a ∈ q := by simp_all
    rcases hq.mem_or_mem hmem with h | h
    exact absurd (hqP h) c.2
    exact h
  obtain ⟨W, hWopen, hWirr, hPW⟩ :=
    exists_isOpen_isIrreducible_of_unique_minimal_prime_le _a0
      _m0 hKp hmin
  let _a2 := homeoOfIso e
  refine ⟨_a2.symm '' W,
    _a2.symm.isOpenMap W hWopen,
    hWirr.image _ (homeoOfIso e).symm.continuous.continuousOn,
    ⟨_a0, hPW, _a2.symm_apply_apply y⟩⟩

section
variable {X} {k : Type} [Field k] (p : X ⟶ Sp k)
theorem exists_isOpen_isIrreducible_mem_of_smooth [Smooth p] (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ V := by
  obtain ⟨U, hxU, hU'⟩ := exists_isAffineOpen_mem x
  have : IsAffine U.toScheme := hU'
  have hnoeth : IsNoetherianRing Γ(oSch U, ⊤) := by
    let V := U
    let _a0 := isoI (GSpecIso $ m10 k) ≫ appTop (opI V ≫ p)
    have hft : RingHom.FiniteType $ hom
        _a0 := by
      have : IsAffine V.toScheme := hU'
      have hfac : V.toScheme.isoSpec.hom ≫
          Spec.map _a0
            = opI V ≫ p := by
        rw [isoSpec_hom, map_comp, ← assoc, ← Scheme.toSpecΓ_naturality]
        simp
      have h3 := congrArg
        (fun f => V.toScheme.isoSpec.inv ≫ f) hfac
      simp [← assoc, inv_hom_id, id_comp] at h3
      have h2 : LocallyOfFiniteType
          (Spec.map _a0) := by
        rw [h3]
        infer_instance
      exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp h2
    let _a1 := Γ(oSch V, ⊤)
    let _ : Algebra (m10 k) _a1 :=
      (hom _a0).toAlgebra
    have : FiniteType (m10 k) _a1 := hft
    have : IsNoetherianRing $ m10 k := inferInstanceAs $ IsNoetherianRing k
    exact isNoetherianRing (m10 k) _a1
  have hdomX := isDomain_stalk_of_smooth p x
  obtain ⟨V, hVopen, hVirr, hyV⟩ :=
    exists_isOpen_isIrreducible_of_iso_spec_of_isDomain_stalk Γ(oSch U, ⊤) U.toScheme.isoSpec
      (⟨x, hxU⟩ : U) $ (U.stalkIso (⟨x, hxU⟩ : U)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have hoe := U.ι.isOpenEmbedding
  exact ⟨opIb U '' V, hoe.isOpenMap V hVopen,
    hVirr.image _ hoe.continuous.continuousOn, ⟨(⟨x, hxU⟩ : U), hyV, rfl⟩⟩

theorem isClopen_irreducibleComponent_of_smooth (hp : Smooth p)
    {T : Set ↥X} (hT : T ∈ irreducibleComponents ↥X) : IsClopen T := by
  refine ⟨isClosed_of_mem_irreducibleComponents _ hT, ?_⟩
  rw [isOpen_iff_forall_mem_open]
  intro z hzT
  obtain ⟨W, hWopen, hWirr, hzW⟩ := exists_isOpen_isIrreducible_mem_of_smooth p z
  refine ⟨W, ?_, hWopen, hzW⟩
  rw [eq_closure_of_mem_irreducibleComponents hWopen hWirr hT hzW hzT]
  exact subset_closure
end


section
variable (k : Type) [Field k] (m : ℕ)
@[reducible] def CoordPolynomialRing : Type :=
  MvU m k

section
variable (S : Type) [CommRing S] [Algebra (CoordPolynomialRing k m) S] (j : Fin m)
noncomputable def etaleChartCoord : S :=
  algebraMap (CoordPolynomialRing k m) S $ MvPolynomial.X $ up j

theorem etaleChartCoord_def :
    etaleChartCoord k m S j =
      algebraMap (CoordPolynomialRing k m) S (MvPolynomial.X $ up j) :=
  rfl
end

theorem isRegularLocalRing_localization_coordPolynomialRing
    (p : Ideal $ CoordPolynomialRing k m) (hp : p.IsPrime) :
    IsRegularLocalRing $ AtPrime p := by
  infer_instance
end

theorem isRegularLocalRing_and_ringKrullDim_eq_of_etale (P S : Type) [CommRing P] [CommRing S] [Algebra P S]
    [Algebra.Etale P S] [IsNoetherianRing P]
    (hreg : ∀ (p : Ideal P) [p.IsPrime], IsRegularLocalRing $ AtPrime p)
    (q : Ideal S) [q.IsPrime] (A : Type) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A ∧
      ringKrullDim A = ringKrullDim (AtPrime $ q.comap $ algebraMap P S) := by
  let _a1 := algebraMap P S
  let _a0 := q.comap _a1
  let _c0 := AtPrime _a0
  let _c1 := _a0
  have : FiniteType P S := inferInstance
  have : IsNoetherianRing S := isNoetherianRing P S
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing q.primeCompl A inferInstance
  have : IsLocalRing A := isLocalRing A q
  let : Algebra P A := ((algebraMap S A).comp _a1).toAlgebra
  have : IsScalarTower P S A := of_algebraMap_eq fun _ => rfl
  have : Flat P S := inferInstance
  have : Flat S A := flat A q.primeCompl
  have : Flat P A := trans P S A
  have : FormallyUnramified P S := inferInstance
  have : FormallyUnramified S A :=
    Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  have : FormallyUnramified P A := Algebra.FormallyUnramified.comp P S A
  have : EssFiniteType P S := inferInstance
  have : EssFiniteType S A := Algebra.EssFiniteType.of_isLocalization A q.primeCompl
  have : EssFiniteType P A := Algebra.EssFiniteType.comp P S A
  have hunits : ∀ y : _c1.primeCompl, IsUnit $ algebraMap P A y := by
    rintro ⟨y, hy⟩
    have hy' : algebraMap P S y ∈ q.primeCompl := hy
    have h := map_units A ⟨algebraMap P S y, hy'⟩
    rwa [algebraMap_apply P S A]
  let : Algebra _c0 A :=
    (IsLocalization.lift hunits).toAlgebra
  have : IsScalarTower P _c0 A :=
    of_algebraMap_eq fun x => sy_ $ lift_eq hunits x
  have : Flat _c0 A :=
    (flat_iff_of_isLocalization _c0
      _c1.primeCompl A).mpr ‹_›
  have : FormallyUnramified _c0 A :=
    localization_base (M := _c1.primeCompl)
  have : EssFiniteType _c0 A :=
    Algebra.EssFiniteType.of_comp P _c0 A
  have : IsRegularLocalRing _c0 :=
    hreg _
  let _a2 := algebraMap _c0 A
  have : IsLocalHom _a2 := by
    constructor
    intro r hr
    obtain ⟨⟨x, s⟩, hx⟩ :=
      surj (M := _c1.primeCompl) r
    have hxA : algebraMap _c0 A r
        * algebraMap P A s = algebraMap P A x := by
      have h := congrArg _a2 hx
      rw [map_mul] at h
      rw [algebraMap_apply P
            _c0 A s,
        algebraMap_apply P
            _c0 A x]
      exact h
    have h2 := hr.mul $ hunits s
    rw [hxA] at h2
    have h3 := h2
    rw [algebraMap_apply P S A] at h3
    have h5 : x ∈ _c1.primeCompl := mp (isUnit_to_map_iff A q $ algebraMap P S x) h3
    have h6 : IsUnit $ algebraMap P _c0 x :=
      map_units _ ⟨x, h5⟩
    rw [← hx] at h6
    exact an1 $ IsUnit.mul_iff.mp h6
  exact ⟨isRegularLocalRing_of_flat_formallyUnramified
      _c0 A,
    ringKrullDim_eq_of_flat_formallyUnramified
      _c0 A⟩

section
variable (k : Type) [Field k] (m) (S : Type) [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime]
include k m
theorem isRegularLocalRing_of_isLocalization_etale (A : Type) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A :=
  (isRegularLocalRing_and_ringKrullDim_eq_of_etale (CoordPolynomialRing k m) S
    (by intro p hp; exact isRegularLocalRing_localization_coordPolynomialRing k m p hp) q A).1

theorem isRegularLocalRing_localization_atPrime_etale :
    IsRegularLocalRing $ AtPrime q :=
  isRegularLocalRing_of_isLocalization_etale k m S q $ AtPrime q
end


section
variable (k : Type) [Field k] (m) (S : Type) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
section
variable (J : FinSet m)
noncomputable def etaleChartCoordIdeal : Ideal S :=
  span $ etaleChartCoord k m S '' (J : Set $ Fin m)

theorem etaleChartCoordIdeal_eq_span_image :
    etaleChartCoordIdeal k m S J = span (etaleChartCoord k m S '' (J : Set $ Fin m)) :=
  rfl

theorem etaleChartCoordIdeal_le I
    (hI : ∀ j ∈ J, etaleChartCoord k m S j ∈ I) : etaleChartCoordIdeal k m S J ≤ I := by
  refine Ideal.span_le.mpr ?_
  rintro x ⟨j, hj, rfl⟩
  exact hI j $ mp_ mem_coe hj

@[reducible] noncomputable def algebraQuotientCoordIdeal :
    Algebra (MvPolynomial (UFin $ m - J.card) k) $ S ⧸ etaleChartCoordIdeal k m S J :=
  toAlgebra
    (((mk $ etaleChartCoordIdeal k m S J).comp
      $ algebraMap (CoordPolynomialRing k m) S).comp (renameCompl k m J).toRingHom)
end

section
variable [Algebra.Etale (CoordPolynomialRing k m) S]
theorem etale_algebraMap_coordPolynomialRing :
    (algebraMap (CoordPolynomialRing k m) S).Etale := by
  let _a1 := CoordPolynomialRing k m
  let _a0 := algebraMap _a1 S
  have hiff : _a0.toAlgebra
      = (inferInstance : Algebra _a1 S) :=
    algebra_ext _ _ fun r => rfl
  show @m121 _ _ _ _ _a0.toAlgebra
  rw [hiff]
  infer_instance

section
variable (q : Ideal S) [q.IsPrime] (A : Type) [CommRing A] [Algebra S A] [IsLocalization q.primeCompl A]
theorem isRegularLocalRing_quotient_map_etaleChartCoordIdeal (J : FinSet m)
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    IsRegularLocalRing
      (A ⧸ map (algebraMap S A) (etaleChartCoordIdeal k m S J)) := by
  let _c0 := etaleChartCoordIdeal k m S J
  let _c1 := S ⧸ etaleChartCoordIdeal k m S J
  classical
  have hIq := etaleChartCoordIdeal_le k m S J q hJ
  let _m0 := map (mk _c0) q
  have hq' : _m0.IsPrime :=
    map_isPrime_of_surjective mk_surjective
      (by rw [mk_ker]; exact hIq)
  let _a1 := CoordPolynomialRing k $ m - J.card
  let algQuotient : Algebra _a1 _c1 :=
    algebraQuotientCoordIdeal k m S J
  let _a3 := algebraMap (CoordPolynomialRing k m) S
  have _i26 : map _a3 (mvPolynomialCoordIdeal k m J) = etaleChartCoordIdeal k m S J := by
    rw [etaleChartCoordIdeal_eq_span_image, mvPolynomialCoordIdeal_eq_span, map_span, image_image]
    rfl
  have : m121 _a1 _c1 :=
    etale_quotientMk_comp_renameCompl k m J _a3
      (etale_algebraMap_coordPolynomialRing k m S) _c0
      _i26.symm
  let _a2 := Submonoid.map (mk _c0) q.primeCompl
  have h2 : _a2
      = _m0.primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := mk_surjective x
    constructor
    rintro ⟨b, hb, hba⟩ hcon
    refine hb $ mp_ (mem_quotient_iff_mem hIq) ?_
    rwa [hba]
    intro ha
    exact ⟨a, fun hq => ha $ mpr_ (mem_quotient_iff_mem hIq) hq, rfl⟩
  let _a0 := map (algebraMap S A) _c0
  have hloc : IsLocalization
      _a2
      (A ⧸ _a0) :=
    inferInstanceAs $ IsLocalization
      (algebraMapSubmonoid _c1 q.primeCompl)
      (A ⧸ _a0)
  have : IsLocalization _m0.primeCompl
      (A ⧸ _a0) := h2 ▸ hloc
  exact isRegularLocalRing_of_isLocalization_etale k (m - J.card)
    _c1
    _m0
    (A ⧸ _a0)

theorem ringKrullDim_quotient_map_etaleChartCoordIdeal_add_card (J : FinSet m)
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q) :
    ringKrullDim (A ⧸ map (algebraMap S A) (etaleChartCoordIdeal k m S J)) +
        (J.card : WithBot ENat) = ringKrullDim A := by
  let _a4 := algebraMap S A
  classical
  have : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  revert hJ
  induction J using m178 with
  | empty =>
      intro _
      have h0 : map _a4 (etaleChartCoordIdeal k m S (∅ : FinSet m)) = ⊥ := by
        rw [etaleChartCoordIdeal_eq_span_image]
        simp
      have hker : (⊥ : Ideal A) = ker (m99 A) := by
        ext a
        simp [mem_ker]
      have e :=
        (quotEquivOfEq hker).trans
          (quotientKerEquivOfSurjective
            (fun a => ⟨a, rfl⟩))
      rw [h0, ringKrullDim_eq_of_ringEquiv e]
      simp
  | @insert j J' hjJ ih =>
      intro hJ
      have hJ' := fun i hi =>
        hJ i (mem_insert_of_mem hi)
      have hjq := hJ j $ mem_insert_self _ _
      set I' := map _a4 (etaleChartCoordIdeal k m S J') with hI'
      let _a1 := etaleChartCoord k m S j
      have hR :=
        isRegularLocalRing_quotient_map_etaleChartCoordIdeal k m S q A J' hJ'
      set y : A := algebraMap S A _a1 with hy
      have hins : map (algebraMap S A) (etaleChartCoordIdeal k m S (insert j J'))
          = I' ⊔ span {y} := by
        rw [hI', hy, etaleChartCoordIdeal_eq_span_image, etaleChartCoordIdeal_eq_span_image, coe_insert,
          image_insert_eq, span_insert, Ideal.map_sup, map_span, map_span,
          image_singleton]
        exact sup_comm _ _
      let _a2 := span {y}
      have hspan : map (mk I') _a2
          = span {mk I' y} := by
        rw [map_span, image_singleton]
      have e := (quotEquivOfEq hspan.symm).trans
        (DoubleQuot.quotQuotEquivQuotSup I' _a2)
      have hdim1 : ringKrullDim
          (A ⧸ map (algebraMap S A) (etaleChartCoordIdeal k m S (insert j J')))
          = ringKrullDim ((A ⧸ I') ⧸ span {mk I' y}) := by
        rw [hins]
        exact sy_ (ringKrullDim_eq_of_ringEquiv e)
      have hmaxR :=
        (map_maximalIdeal_of_surjective (mk I')
          mk_surjective).symm
      have hy1 : mk I' y ∈ maximalIdeal (A ⧸ I') := by
        rw [hmaxR, hy]
        exact mem_map_of_mem _
          (mpr_ (to_map_mem_maximal_iff A q _a1
            inferInstance) hjq)
      have hy2 : mk I' y ∉ maximalIdeal (A ⧸ I') ^ 2 := by
        rw [hmaxR, ← m219]
        intro hcon
        have hcon2 : y ∈ comap (mk I')
            (map (mk I') (maximalIdeal A ^ 2)) := hcon
        rw [comap_map_of_surjective _ mk_surjective,
          ← ker_eq_comap_bot, mk_ker] at hcon2
        rw [hy, hI'] at hcon2
        have _i28 : algebraMap S A (etaleChartCoord k m S j) ∉ maximalIdeal A ^ 2 ⊔ map (algebraMap S A) (etaleChartCoordIdeal k m S J') := by
          let hj := hjJ
          classical
          let _a1 := CoordPolynomialRing k m
          let algebraKS : Algebra k S := ((algebraMap _a1 S).comp
            (algebraMap k _a1)).toAlgebra
          have : IsScalarTower k _a1 S := of_algebraMap_eq' rfl
          let algebraKA : Algebra k A := ((algebraMap S A).comp (algebraMap k S)).toAlgebra
          have : IsScalarTower k S A := of_algebraMap_eq' rfl
          let D : Derivation k S S :=
            p27 k (UFin m) S (up j)
          let DA : Derivation k A A := D.mapToLocalization q.primeCompl
          have hderivAlgebraMap : ∀ s, DA (algebraMap S A s) = algebraMap S A (D s) :=
            Derivation.mapToLocalization_algebraMap D q.primeCompl
          let _a0 := etaleChartCoord k m S j
          have hDx : D _a0 = 1 :=
            partialDeriv_coord_self k (UFin m) S (up j)
          have hDne : ∀ i, i ≠ j → D (etaleChartCoord k m S i) = 0 := by
            intro i hne
            have hup : (up j) ≠ up i := fun h => hne (congrArg down h).symm
            exact partialDeriv_coord_of_ne k (UFin m) S
              (up j) (up i) hup
          have hspan_le : span ((fun i => algebraMap S A $ etaleChartCoord k m S i) ''
              (J' : Set (Fin m))) ≤ maximalIdeal A := by
            refine Ideal.span_le.mpr ?_
            rintro x ⟨i, hi, rfl⟩
            exact mpr_ (to_map_mem_maximal_iff A q (etaleChartCoord k m S i)
              inferInstance) (hJ' i (mp_ mem_coe hi))
          intro hmem
          obtain ⟨a, ha, b, hb, hab⟩ := mp_ mem_sup hmem
          have hsq : maximalIdeal A ^ 2
              = maximalIdeal A * maximalIdeal A := sq _
          rw [hsq] at ha
          have hDa : DA a ∈ maximalIdeal A := by
            refine mul_induction_on ha ?_ ?_
            intro p hp r hr
            rw [DA.leibniz, smul_eq_mul, smul_eq_mul]
            exact add_mem (mul_mem_right _ _ hp) $ mul_mem_right _ _ hr
            intro x y hx hy
            rw [map_add]
            exact add_mem hx hy
          rw [etaleChartCoordIdeal_eq_span_image, map_span, image_image] at hb
          have hDb : DA b ∈ maximalIdeal A := by
            refine span_induction ?_ ?_ ?_ ?_ hb
            rintro z ⟨i, hi, rfl⟩
            rw [hderivAlgebraMap, hDne i (by rintro rfl; exact hj $ mp_ mem_coe hi), map_zero]
            exact zero_mem _
            rw [map_zero]
            exact zero_mem _
            intro x y hx hy px py
            rw [map_add]
            exact add_mem px py
            intro c x hx px
            have hxm : x ∈ maximalIdeal A := hspan_le hx
            rw [smul_eq_mul, DA.leibniz, smul_eq_mul, smul_eq_mul]
            exact add_mem (mul_mem_left _ _ px) $ mul_mem_right _ _ hxm
          have hone : DA (algebraMap S A _a0) = 1 := by
            rw [hderivAlgebraMap, hDx, map_one]
          rw [← hab, map_add] at hone
          have h1 : (1 : A) ∈ maximalIdeal A := by
            rw [← hone]
            exact add_mem hDa hDb
          exact (isMaximal A).ne_top (mpr_ (eq_top_iff_one _) h1)
        exact _i28 hcon2
      have hstep :=
        ringKrullDim_quotient_span_singleton_add_one hy1 hy2
      rw [hdim1, card_insert_of_notMem hjJ]
      have hcard : (((J'.card + 1 : ℕ)) : WithBot ENat) = 1 + (J'.card : WithBot ENat) := by
        push_cast
        ring
      rw [hcard, ← add_assoc, hstep]
      exact ih hJ'
end
end
end

theorem exists_regularSystemOfParameters_containing_etaleChartCoords (k : Type) [Field k] m
    (S : Type) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (J0_ : FinSet m)
    (hJ0_ : ∀ j ∈ J0_, etaleChartCoord k m S j ∈ q) :
    ∃ (d : ℕ) (x : Fin d → S),
      (∀ i, x i ∈ q) ∧
      (∀ j ∈ J0_, ∃ i, x i = etaleChartCoord k m S j) ∧
      span (range fun i => algebraMap S A (x i)) = maximalIdeal A ∧
      (d : WithBot ENat) = ringKrullDim A := by
  let _a1 := algebraMap S A
  classical
  set I := map _a1 (etaleChartCoordIdeal k m S J0_) with hIdef
  have hreg :=
    isRegularLocalRing_quotient_map_etaleChartCoordIdeal k m S q A J0_ hJ0_
  have : IsLocalRing $ A ⧸ I := inferInstance
  obtain ⟨n, z, hzspan, hzdim⟩ : ∃ (n : ℕ) (z : Fin n → A ⧸ I), span (range z) = maximalIdeal (A ⧸ I) ∧ n = ringKrullDim (A ⧸ I) := by
    let Q := A ⧸ I
    classical
    have : IsLocalRing Q := inferInstance
    have : IsNoetherianRing Q := inferInstance
    have : Module.Finite (ResidueField Q) $ CotangentSpace Q :=
      inferInstance
    have hsurjres : Surjective $ algebraMap Q $ ResidueField Q := by
      intro x
      obtain ⟨y, rfl⟩ := mk_surjective x
      exact ⟨y, rfl⟩
    set b := finBasis (ResidueField Q) (CotangentSpace Q) with hb
    choose w hw using fun i => (toCotangent_surjective _) $ b i
    have hspanQ : m72 Q (range b) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ m72 (ResidueField Q) (range b) := by simp_all
      refine span_induction ?_ (zero_mem _) ?_ ?_ hx
      intro y hy
      exact Submodule.subset_span hy
      intro y z _ _ hy hz
      exact add_mem hy hz
      intro c y _ hy
      obtain ⟨c', rfl⟩ := hsurjres c
      rw [algebraMap_smul]
      exact smul_mem _ _ hy
    have himg : (maximalIdeal Q).toCotangent '' (range w) = range b := by
      rw [← range_comp]
      exact congrArg range $ funext hw
    have hMtop : m72 Q (range w) = ⊤ := by
      refine IsLocalRing.CotangentSpace.map_eq_top_iff.mp ?_
      rwa [Submodule.map_span, himg]
    refine ⟨finrank (ResidueField Q) $ CotangentSpace Q,
      fun i => (w i : Q), ?_, mp_ (iff_finrank_cotangentSpace Q) ‹_›⟩
    have h1 : Submodule.map (maximalIdeal Q).subtype
        (m72 Q $ range w) = span (range fun i => (w i : Q)) := by
      rw [Submodule.map_span, ← range_comp]
      rfl
    rw [← h1, hMtop, map_subtype_top]
  have hIle : I ≤ maximalIdeal A := by
    rw [hIdef]
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro s hs
    exact mpr_ (to_map_mem_maximal_iff A q s inferInstance)
      (etaleChartCoordIdeal_le k m S J0_ q hJ0_ hs)
  have hmaxQ :=
    (map_maximalIdeal_of_surjective (mk I)
      mk_surjective).symm
  choose a ha using fun i => mk_surjective $ z i
  have hamem : ∀ i, a i ∈ maximalIdeal A := by
    intro i
    refine mp_ (mem_quotient_iff_mem hIle) ?_
    rw [← hmaxQ, ha i, ← hzspan]
    exact subset_span ⟨i, rfl⟩
  choose rt hrt using fun i => surj (M := q.primeCompl) $ a i
  have hsq : ∀ i, (rt i).1 ∈ q := by
    intro i
    refine mp_ (to_map_mem_maximal_iff A q (rt i).1 inferInstance) ?_
    rw [← hrt i]
    exact mul_mem_right _ _ $ hamem i
  refine ⟨J0_.card + n,
    append
      (fun i => etaleChartCoord k m S ((J0_.equivFin.symm i) : Fin m))
      (fun i => (rt i).1), ?_, ?_, ?_, ?_⟩
  intro i
  refine addCases (fun i => ?_) (fun i => ?_) i
  rw [append_left]
  exact hJ0_ _ (J0_.equivFin.symm i).2
  rw [append_right]
  exact hsq i
  intro j hj
  refine ⟨castAdd n $ J0_.equivFin ⟨j, hj⟩, ?_⟩
  rw [append_left, symm_apply_apply]
  have hxq : ∀ i : Fin $ J0_.card + n,
      append
        (fun i =>
          etaleChartCoord k m S ((J0_.equivFin.symm i) : Fin m))
        (fun i => (rt i).1) i ∈ q := by
    intro i
    refine addCases (fun i => ?_) (fun i => ?_) i
    simp_all
    simp_all
  have hTle : span (range fun i =>
      algebraMap S A $ append
        (fun i =>
          etaleChartCoord k m S ((J0_.equivFin.symm i) : Fin m))
        (fun i => (rt i).1) i) ≤ maximalIdeal A := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact mpr_ (to_map_mem_maximal_iff A q _ inferInstance) $ hxq i
  have hIT : I ≤ span (range fun i =>
      algebraMap S A $ append
        (fun i =>
          etaleChartCoord k m S ((J0_.equivFin.symm i) : Fin m))
        (fun i => (rt i).1) i) := by
    rw [hIdef, etaleChartCoordIdeal_eq_span_image, map_span, image_image]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, hj, rfl⟩
    refine subset_span ⟨castAdd n $ J0_.equivFin ⟨j, mp_ mem_coe hj⟩, ?_⟩
    refine congrArg _a1 ?_
    rw [append_left, symm_apply_apply]
  refine le_antisymm hTle ?_
  intro y hy
  refine mp_ (mem_quotient_iff_mem hIT) ?_
  have hz : ∀ i, z i ∈ map (mk I) (span $ range fun i =>
      algebraMap S A $ append
        (fun i =>
          etaleChartCoord k m S ((J0_.equivFin.symm i) : Fin m))
        (fun i => (rt i).1) i) := by
    intro i
    have hunit :=
      (map_units A $ (rt i).2).map $ mk I
    obtain ⟨v, hv⟩ := mp_ isUnit_iff_exists_inv hunit
    have hmem : mk I (algebraMap S A $ (rt i).1)
        ∈ map (mk I) (span $ range fun i =>
          algebraMap S A $ append
            (fun i =>
              etaleChartCoord k m S ((J0_.equivFin.symm i) : Fin m))
            (fun i => (rt i).1) i) := by
      exact mem_map_of_mem _ $ subset_span ⟨natAdd J0_.card i, congrArg _a1 $ append_right _ _ i⟩
    have heq : mk I (algebraMap S A $ (rt i).1)
        = z i * mk I (algebraMap S A ((rt i).2 : S)) := by
      rw [← hrt i, map_mul, ha i]
    have hzi : z i = mk I (algebraMap S A $ (rt i).1) * v := by
      rw [heq, mul_assoc, hv, mul_one]
    rw [hzi]
    exact mul_mem_right _ _ hmem
  have hmq : maximalIdeal (A ⧸ I) ≤ map (mk I)
      (span $ range fun i =>
        algebraMap S A $ append
          (fun i =>
            etaleChartCoord k m S ((J0_.equivFin.symm i) : Fin m))
          (fun i => (rt i).1) i) := by
    rw [← hzspan]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hz i
  refine hmq ?_
  rw [hmaxQ]
  exact mem_map_of_mem _ hy
  have h2 := ringKrullDim_quotient_map_etaleChartCoordIdeal_add_card k m S q A J0_ hJ0_
  rw [← hIdef] at h2
  rw [← h2, ← hzdim, cast_add]
  exact add_comm _ _


theorem isRadical_span_singleton_of_isRadical_map_atPrime {S : Type} [CommRing S] a
    (h : ∀ (Q : Ideal S) [Q.IsPrime],
      (map (algebraMap S $ AtPrime Q) $ span ({a} : Set S)).IsRadical) :
    (span ({a} : Set S)).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := mp_ mem_radical_iff hx
  by_contra hxI
  let _m0 := ({a} : Set S)
  obtain ⟨K, hKmem⟩ : ∃ K : Ideal S, ∀ b : S, b ∈ K ↔ b * x ∈ span _m0 :=
    ⟨{ carrier := {s : S | s * x ∈ span _m0}
       zero_mem' := by
         show (0 : S) * x ∈ span _m0
         rw [zero_mul]
         exact m216 _
       add_mem' := by
         intro b c hb hc
         show (b + c) * x ∈ span _m0
         rw [add_mul]
         exact m128 _ hb hc
       smul_mem' := by
         intro c b hb
         show (c • b) * x ∈ span _m0
         rw [smul_eq_mul, mul_assoc]
         exact mul_mem_left _ c hb },
     fun b => m22⟩
  have hKne : K ≠ ⊤ := by
    intro htop
    have h1 : 1 ∈ K := by rw [htop]
                          exact mem_top
    have h2 := mp_ (hKmem 1) h1
    rw [one_mul] at h2
    exact hxI h2
  obtain ⟨Q, hQmax, hKQ⟩ := exists_le_maximal K hKne
  have hQp := hQmax.isPrime
  have hpow : (algebraMap S (AtPrime Q) x) ^ n ∈
      map (algebraMap S $ AtPrime Q) (span _m0) := by
    rw [← map_pow]
    exact mem_map_of_mem _ hn
  have hxmem :=
    (h Q) $ mpr_ mem_radical_iff ⟨n, hpow⟩
  rw [map_span, image_singleton] at hxmem
  obtain ⟨c, hc⟩ := mp_ mem_span_singleton' hxmem
  obtain ⟨⟨y, s⟩, hys⟩ := surj (M := Q.primeCompl) c
  have key : algebraMap S (AtPrime Q) (x * s) =
      algebraMap S (AtPrime Q) (a * y) := by
    have h1 : algebraMap S (AtPrime Q) (x * s)
        = (c * algebraMap S (AtPrime Q) s) *
            algebraMap S (AtPrime Q) a := by
      rw [map_mul, ← hc]
      ring
    rw [h1, hys, map_mul]
    ring
  obtain ⟨dd, hd⟩ := mp_ (eq_iff_exists Q.primeCompl $ AtPrime Q) key
  let _m1 := (dd : S) * (s : S)
  have hmem0 : _m1 * x ∈ span _m0 := by
    have heq : _m1 * x = (dd : S) * (x * (s : S)) := by ring
    rw [heq, hd]
    exact mul_mem_left _ _ $ mul_mem_right y _ $ mem_span_singleton_self a
  have hQmem := hKQ $ mpr_ (hKmem _) hmem0
  rcases hQp.mem_or_mem hQmem with hcase | hcase
  exact dd.2 hcase
  exact s.2 hcase

section
variable (k : Type) [Field k] (m) (S : Type) [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
theorem etaleChartCoord_injective
    [Nontrivial S] : Injective $ etaleChartCoord k m S := by
  have hinj : Injective $ algebraMap (CoordPolynomialRing k m) S := by
    refine mpr_ (injective_iff_map_eq_zero _) ?_
    intro a ha
    by_contra h
    have hreg := isSMulRegular_of_nonZeroDivisors (M := S)
      (mem_nonZeroDivisors_of_ne_zero h)
    have h1 : 1 = 0 := by simp_all
    exact one_ne_zero h1
  intro i j hij
  have h : (m7 (up i) : CoordPolynomialRing k m)
      = m7 (up j) := by
    apply hinj
    rwa [← etaleChartCoord_def, ← etaleChartCoord_def]
  exact congrArg down $ X_injective h

theorem linearIndependent_toCotangent_etaleChartCoord
    (q : Ideal S) [q.IsPrime] (A : Type) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (J : FinSet m)
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q)
    (hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A)
      (fun j : { x : Fin m // x ∈ J } =>
          (maximalIdeal A).toCotangent
            ⟨algebraMap S A $ etaleChartCoord k m S (j : Fin m), hJA (j : Fin m) j.2⟩ :
        { x : Fin m // x ∈ J } → CotangentSpace A) := by
  classical
  have hreg := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hnt : Nontrivial S := by
    rcases subsingleton_or_nontrivial S with hs | hs
    exfalso
    have h10 : (1 : S) = (0 : S) := elim _ _
    have hA : (1 : A) = 0 := by
      calc (1 : A) = algebraMap S A 1 := sy_ (map_one _)
        _ = algebraMap S A 0 := by rw [h10]
        _ = 0 := map_zero _
    exact one_ne_zero hA
    exact hs
  obtain ⟨d, w, hwq, hwJ, hspan, hdim⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m S q A J hJ
  have hwm : ∀ i, algebraMap S A (w i) ∈ maximalIdeal A := by
    intro i
    rw [← hspan]
    exact subset_span ⟨i, rfl⟩
  let _a1 := maximalIdeal A
  obtain ⟨y, hy⟩ : ∃ y : Fin d → CotangentSpace A,
      ∀ i, y i = _a1.toCotangent ⟨algebraMap S A $ w i, hwm i⟩ :=
    ⟨_, fun i => rfl⟩
  let _a0 := m72 (ResidueField A) $ range y
  have key : ∀ b, b ∈ span (range fun i => algebraMap S A $ w i) →
      ∀ hb,
        _a1.toCotangent ⟨b, hb⟩ ∈
          _a0 := by
    intro b hb0
    have hb' := hb0
    clear hb0
    induction hb' using span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        intro hz'
        exact Submodule.subset_span ⟨i, by rw [hy i]⟩
    | zero =>
        intro hz'
        have h0 : (⟨0, hz'⟩ : maximalIdeal A) = 0 := rfl
        rw [h0, map_zero]
        exact m97 _
    | add z z' hz hz' ihz ihz' =>
        intro hbb
        have hzm : z ∈ maximalIdeal A := by rw [← hspan]
                                            exact hz
        have hzm' : z' ∈ maximalIdeal A := by rw [← hspan]
                                              exact hz'
        have hsum : (⟨z + z', hbb⟩ : maximalIdeal A) = ⟨z, hzm⟩ + ⟨z', hzm'⟩ := rfl
        rw [hsum, map_add]
        exact m60 _ (ihz hzm) $ ihz' hzm'
    | smul c z hz ih =>
        intro hbb
        have hzm : z ∈ maximalIdeal A := by rw [← hspan]
                                            exact hz
        have hsm : (⟨c • z, hbb⟩ : maximalIdeal A) = c • ⟨z, hzm⟩ := rfl
        rw [hsm, map_smul, ← IsScalarTower.algebraMap_smul (ResidueField A) c]
        exact smul_mem _ _ $ ih hzm
  have hspanY : ⊤ ≤ _a0 := by
    intro v _
    obtain ⟨⟨b, hb⟩, rfl⟩ := toCotangent_surjective (maximalIdeal A) v
    exact key b (by rw [hspan]; exact hb) hb
  have hcard : Fintype.card (Fin d) =
      finrank (ResidueField A) (CotangentSpace A) := by
    rw [Fintype.card_fin]
    exact_mod_cast (hdim.trans (mp_ (iff_finrank_cotangentSpace A) ‹_›).symm)
  have hchoice : ∀ j : { x : Fin m // x ∈ J },
      ∃ i, w i = etaleChartCoord k m S j := fun j => hwJ j j.2
  choose f hf using hchoice
  have hfinj : m120 f := by
    intro j1 j2_ hjj
    have h1 : etaleChartCoord k m S j1 = etaleChartCoord k m S j2_ := by
      rw [← hf j1, ← hf j2_, hjj]
    exact m26 $ etaleChartCoord_injective k m S h1
  have hcomp := (linearIndependent_of_top_le_span_of_card_eq_finrank hspanY hcard).comp f hfinj
  have heq : y ∘ f = fun j : { x : Fin m // x ∈ J } =>
      _a1.toCotangent
        ⟨algebraMap S A $ etaleChartCoord k m S j, hJA j j.2⟩ := by
    funext j
    have h1 : (⟨algebraMap S A $ w $ f j, hwm $ f j⟩ : maximalIdeal A)
        = ⟨algebraMap S A $ etaleChartCoord k m S j, hJA j j.2⟩ :=
      m26 $ congrArg (algebraMap S A) $ hf j
    dsimp
    rw [hy $ f j]
    exact congrArg _ h1
  rwa [← heq]

theorem isRadical_span_singleton_prod_etaleChartCoord
    (T : FinSet m) :
    (span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S)).IsRadical := by
  refine isRadical_span_singleton_of_isRadical_map_atPrime (∏ j ∈ T, etaleChartCoord k m S j) ?_
  intro Q hQ
  let q := Q
  let A := AtPrime Q
  classical
  obtain ⟨J, hJdef⟩ : ∃ J,
      J = T.filter fun j => etaleChartCoord k m S j ∈ q := ⟨_, rfl⟩
  have hJsub : J ⊆ T := by rw [hJdef]
                           exact filter_subset _ _
  have hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q := by simp_all
  have hunit : IsUnit (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) := by
    refine prod_induction _ _ (fun u v hu hv => hu.mul hv) isUnit_one ?_
    intro j hj
    have h1 := mp_ mem_sdiff hj
    refine map_units A (⟨etaleChartCoord k m S j, ?_⟩ : q.primeCompl)
    intro hmem
    exact an2 h1 (by rw [hJdef]; exact Finset.mem_filter.mpr ⟨an1 h1, hmem⟩)
  have hsplit : ∏ j ∈ T, algebraMap S A (etaleChartCoord k m S j)
      = (∏ j ∈ T \ J, algebraMap S A (etaleChartCoord k m S j)) *
        ∏ j ∈ J, algebraMap S A (etaleChartCoord k m S j) := by
    rw [← prod_union sdiff_disjoint, sdiff_union_of_subset hJsub]
  rw [map_span, image_singleton, map_prod, hsplit,
    span_singleton_mul_left_unit hunit _]
  classical
  have hreg := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hJA := fun j hj => mpr_ (to_map_mem_maximal_iff A q
      (etaleChartCoord k m S j)) (hJ j hj)
  have hmain := isRadical_span_singleton_prod
    (fun j : { x : Fin m // x ∈ J } => algebraMap S A (etaleChartCoord k m S j))
    (fun j => hJA j j.2) (linearIndependent_toCotangent_etaleChartCoord k m S q A J hJ hJA)
  rwa [← prod_coe_sort J fun j => algebraMap S A (etaleChartCoord k m S j)]
end



theorem germ_mem_maximalIdeal_iff {X : Sch} {U} (hU : IsAffineOpen U)
    x (hx : x ∈ U) s :
    X.presheaf.germ U x hx s ∈ maximalIdeal (X.presheaf.stalk x) ↔
      s ∈ asIdeal (hU.primeIdealOf ⟨x, hx⟩) := by
  let instSt :=
    (pGerm X U x hx).hom.toAlgebra
  have instLoc := hU.isLocalization_stalk ⟨x, hx⟩
  exact to_map_mem_maximal_iff (stkX X x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s

variable {X : Sch} {k : Type} [Field k] {p : X ⟶ Sp k}
  {U : Opn X} {m : ℕ}

section
variable (hU : IsAffineOpen U) (c : EtaleChart p U m) (x) (hx : x ∈ U) (J0_ : FinSet m)
include hU
theorem exists_sections_span_eq_maximalIdeal_with_coords
    (hJ0_ : ∀ j ∈ J0_, X.presheaf.germ U x hx (c.coord j) ∈
      maximalIdeal (X.presheaf.stalk x)) :
    ∃ (d : ℕ) (f : Fin d → (X.sec U)),
      (∀ i, X.presheaf.germ U x hx (f i) ∈
          maximalIdeal (X.presheaf.stalk x)) ∧
      (∀ j ∈ J0_, ∃ i, f i = c.coord j) ∧
      span (range fun i => X.presheaf.germ U x hx $ f i) =
          maximalIdeal (X.presheaf.stalk x) ∧
      (d : WithBot ENat) = ringKrullDim (X.presheaf.stalk x) := by
  let instAlg := c.algebra
  have instEt := c.algebra_etale hU
  let instSt :=
    (pGerm X U x hx).hom.toAlgebra
  let _a0 := hU.primeIdealOf ⟨x, hx⟩
  have instLoc := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ t,
      algebraMap U.sec (stkX X x) t = pGerm X U x hx t := fun _ => rfl
  have hcoord : ∀ j, etaleChartCoord k m U.sec j = c.coord j := by
    intro j
    exact c.coordRingHom_X j
  have hq : ∀ j ∈ J0_, etaleChartCoord k m U.sec j ∈ asIdeal _a0 := by
    intro j hj
    rw [hcoord j]
    exact mp_ (germ_mem_maximalIdeal_iff hU x hx $ c.coord j) $ hJ0_ j hj
  obtain ⟨d, f, hf1, hf2, hf3, hf4⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m U.sec
      _a0.asIdeal (stkX X x) J0_ hq
  refine ⟨d, f, ?_, ?_, ?_, hf4⟩
  intro i
  exact mpr_ (germ_mem_maximalIdeal_iff hU x hx $ f i) $ hf1 i
  intro j hj
  obtain ⟨i, hi⟩ := hf2 j hj
  exact ⟨i, by rw [hi, hcoord j]⟩
  simp_all

theorem exists_isRegularParameterSystem_with_coords_of_mem_prime
    (hJ0_ : ∀ j ∈ J0_, c.coord j ∈ asIdeal (hU.primeIdealOf ⟨x, hx⟩)) :
    ∃ (n : ℕ) (f : Fin n → (X.sec U)),
      (∀ j ∈ J0_, ∃ i, f i = c.coord j) ∧
      IsRegularParameterSystem (X.presheaf.stalk x) n
        (fun i => X.presheaf.germ U x hx $ f i) := by
  obtain ⟨d, f, -, h2, h3, h4⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J0_
      (fun j hj => mpr_ (germ_mem_maximalIdeal_iff hU x hx $ c.coord j) $ hJ0_ j hj)
  exact ⟨d, f, h2, h3, h4⟩
end

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
section
variable (Z : ISD X) (W : Z.subscheme.Opens)
def openSubschemeKer :
    X.IdealSheafData :=
  (Scheme.Opens.ι W ≫ subschemeι Z).ker

section
variable (hW : IsClosed (W : Set Z.subscheme))
include hW
theorem exists_opens_notMem_image (x : X)
    (hx : x ∉ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :
    ∃ U : Opn X, x ∈ U ∧ ∀ w : subscheme Z, w ∈ W → Z.subschemeι.base w ∉ U := by
  refine ⟨⟨(Z.subschemeι.base '' W)ᶜ, (Z.subschemeι.isClosedEmbedding.isClosedMap _ hW).isOpen_compl⟩, hx, ?_⟩
  intro w hw hmem
  exact hmem ⟨w, hw, rfl⟩

end

theorem exists_opens_preimage_subschemeio_le x
    (hx : x ∈ ⇑Z.subschemeι.base '' (W : Set Z.subscheme)) :
    ∃ U, x ∈ U ∧ (subschemeι Z ⁻¹ᵁ U) ≤ W := by
  obtain ⟨t, ht, hteq⟩ := (Z.subschemeι.isEmbedding.toIsInducing).isOpen_iff.mp W.isOpen
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨⟨t, ht⟩, ?_, ?_⟩
  have hwt : w ∈ preimage Z.subschemeι.base t := by
    rwa [hteq]
  exact hwt
  intro y hy
  have hy' : y ∈ preimage Z.subschemeι.base t := hy
  rwa [hteq] at hy'

theorem openSubschemeKer_eq_ker :
    openSubschemeKer Z W = (Scheme.Opens.ι W ≫ Z.subschemeι).ker := rfl

theorem support_openSubschemeKer
    (hW : IsClosed (W : Set Z.subscheme)) :
    (support (openSubschemeKer Z W) : Set X) = ⇑Z.subschemeι.base '' (W : Set Z.subscheme) := by
  have hrangeW : range (p4 W).base = W := by
    rw [q1]
  have hqcW : QuasiCompact $ p4 W := by
    refine ⟨fun U _ hUc => ?_⟩
    refine ((p4 W).isEmbedding.toIsInducing).isCompact_iff.mpr ?_
    rw [image_preimage_eq_inter_range, hrangeW]
    exact hUc.inter_right hW
  let _a0 := p4 W ≫ siI Z
  have hqc : QuasiCompact _a0 := inferInstance
  have hcomp : _a0.base
      = Z.subschemeι.base ∘ (p4 W).base := rfl
  rw [openSubschemeKer_eq_ker, support_ker, hcomp, range_comp, hrangeW]
  exact (Z.subschemeι.isClosedEmbedding.isClosedMap _ hW).closure_eq
end

end

section
variable {Y : Sch}
section
variable (V O : Opn Y) (h : O ≤ V)
include h
theorem image_preimage_opensio_of_le :
    Scheme.Opens.ι V ''ᵁ (Scheme.Opens.ι V ⁻¹ᵁ O) = O := by
  rw [image_preimage_eq_opensRange_inf]
  refine mpr_ inf_eq_right ?_
  intro x hx
  show x ∈ range (p4 V).base
  rw [q1]
  exact h hx

theorem injective_app_opensio_of_le :
    Injective $ hom $ (Scheme.Opens.ι V).app O := by
  have hb := bijective_appLE_of_image_eq (Scheme.Opens.ι V) O
    (Scheme.Opens.ι V ⁻¹ᵁ O) le_rfl $ image_preimage_opensio_of_le V O h
  rw [app_eq_appLE]
  exact an1 hb
end

section
variable (V : Opn Y) (hV : V = ⊥)
include hV
theorem subsingleton_sections_of_eq_bot : Subsingleton ↥(Y.presheaf.obj $ Opposite.op V) := by
  exact subsingleton_of_isTerminal $ Y.sheaf.isTerminalOfEqEmpty hV

theorem one_eq_zero_sections_of_eq_bot :
    (1 : (Y.sec V)) = 0 := by
  have := subsingleton_sections_of_eq_bot V hV
  exact elim _ _
end
end

section
variable {X : Sch} (Z : ISD X) (W : Z.subscheme.Opens)
theorem ker_app_opensio_comp_subschemeio_eq_of_preimage_le
    V (hVW : (subschemeι Z ⁻¹ᵁ V) ≤ W) :
    ker (hom $ (Scheme.Opens.i W ≫ subschemeι Z).app V)
      = ker (hom $ Z.subschemeι.app V) := by
  ext a
  let _a0 := (p4 W).app $ siPre Z V
  have hfac : (hom $ (p4 W ≫ siI Z).app V) a
      = hom _a0
        ((hom $ Z.subschemeι.app V) a) := by
    show (hom $ Z.subschemeι.app V ≫
      _a0) a = _
    rw [hom_comp, comp_apply]
  simp only [mem_ker, hfac]
  constructor
  intro ha
  exact injective_app_opensio_of_le W (siPre Z V) hVW $ tr_ ha (map_zero _).symm
  intro ha
  exact tr_ (congrArg _ ha) $ map_zero _

theorem isLocallyGeneratedByNonZeroDivisor_openSubschemeKer (hW : IsClosed (W : Set Z.subscheme))
    (hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor Z) : Blowup.IsLocallyGeneratedByNonZeroDivisor $ openSubschemeKer Z W := by
  have hrangeW : range (p4 W).base = W := by
    rw [q1]
  have hqcW : QuasiCompact $ p4 W := by
    refine ⟨fun U _ hUc => ?_⟩
    refine ((p4 W).isEmbedding.toIsInducing).isCompact_iff.mpr ?_
    rw [image_preimage_eq_inter_range, hrangeW]
    exact hUc.inter_right hW
  have hqc : QuasiCompact $ p4 W ≫ siI Z := inferInstance
  have hpiece : ∀ V : affO X, (siI Z ⁻¹ᵁ V.1) ≤ W →
      (openSubschemeKer Z W).ideal V = Z.ideal V := by
    intro V hVW
    have h2 : ker (hom $ Z.subschemeι.app V.1) = Z.ideal V := by
      rw [← ker_apply Z.si V,
        q2]
    rw [openSubschemeKer_eq_ker, ker_apply, ker_app_opensio_comp_subschemeio_eq_of_preimage_le Z W V.1 hVW, h2]
  have hpiecetop : ∀ V : affO X,
      (preU (p4 W ≫ siI Z) V.1) = ⊥ → (openSubschemeKer Z W).ideal V = ⊤ := by
    intro V hbot
    rw [openSubschemeKer_eq_ker, ker_apply, eq_top_iff_one,
      mem_ker, map_one]
    exact one_eq_zero_sections_of_eq_bot _ hbot
  intro x
  by_cases hx : x ∈ Z.subschemeι.base '' W
  obtain ⟨N, hxN, hNle⟩ := exists_opens_preimage_subschemeio_le Z W x hx
  obtain ⟨U1_, f1_, hxU1, hf1_, hZU1⟩ := hZ x
  have hU1 := U1_.2
  obtain ⟨s, hsN, hxs⟩ := hU1.exists_basicOpen_le (⟨x, hxN⟩ : N) hxU1
  obtain ⟨f, hf, hZU⟩ : ∃ f' : Γ(X, bOpn X s), f' ∈ nonZeroDivisors Γ(X, bOpn X s) ∧ Z.ideal ⟨bOpn X s, U1_.2.basicOpen s⟩ = span {f'} := by
    let U := U1_
    have hmap := Z.map_ideal_basicOpen U s
    rw [hZU1, map_span, image_singleton] at hmap
    have := U.2.isLocalization_basicOpen s
    exact ⟨_, nonZeroDivisors_le_comap (powers s) Γ(X, bOpn X s) hf1_, sy_ hmap⟩
  have hVW : (Z.si.pre $ bOpn X s) ≤ W := fun v hv => hNle $ hsN hv
  exact ⟨⟨bOpn X s, hU1.basicOpen s⟩, f, hxs, hf, tr_ (hpiece ⟨bOpn X s, hU1.basicOpen s⟩ hVW) hZU⟩
  obtain ⟨N, hxN, hNno⟩ := exists_opens_notMem_image Z W hW x hx
  obtain ⟨U0_, hxU0_⟩ : ∃ U0_ : affO X, x ∈ U0_.1 := by
    have hx' : x ∈ (⊤ : Opn X) := mem_univ x
    rw [← iSup_affineOpens_eq_top X] at hx'
    obtain ⟨U0_, hU0_⟩ := Opens.mem_iSup.mp hx'
    exact ⟨U0_, hU0_⟩
  have hU0_ := U0_.2
  obtain ⟨s, hsN, hxs⟩ := hU0_.exists_basicOpen_le (⟨x, hxN⟩ : N) hxU0_
  refine ⟨⟨bOpn X s, hU0_.basicOpen s⟩, 1, hxs, one_mem _, ?_⟩
  have hbot : (p4 W ≫ siI Z).pre (bOpn X s) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro w hw
    have hmem : (bsM (p4 W) w) ∈ (W : Set Z.subscheme) := by
      rw [← q1 W]
      exact ⟨w, rfl⟩
    exact absurd (hsN hw) $ hNno _ hmem
  rw [span_singleton_one]
  exact hpiecetop ⟨bOpn X s, hU0_.basicOpen s⟩ hbot
end

theorem smooth_subschemeio_openSubschemeKer_comp {X S : Sch} (Z : ISD X)
    (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (g : X ⟶ S)
    [Smooth $ Z.si ≫ g] :
    Smooth $ (openSubschemeKer Z W).si ≫ g := by
  obtain ⟨e, he, hfac⟩ : ∃ e : oSch W ⟶ subS (openSubschemeKer Z W), IsIso e ∧ e ≫ siI (openSubschemeKer Z W) = p4 W ≫ siI Z := by
    have := W.isClosedImmersion_ι_of_isClosed hW
    let _a0 := p4 W ≫ siI Z
    have : IsClosedImmersion _a0 := inferInstance
    let _a1 := openSubschemeKer Z W
    have hker :=
      (q2 _a1).symm
    exact ⟨m64 _a1.si
        _a0 $ le_of_eq hker.symm, IsClosedImmersion.isIso_of_ker_eq _a0 _a1.si _ (m154 _ _ _) hker,
      m154 _ _ _⟩
  have := he
  have hfac2 : inv e ≫ p4 W ≫ siI Z ≫ g
      = siI (openSubschemeKer Z W) ≫ g := by
    rw [← assoc (p4 W) Z.si g, ← hfac, assoc,
      IsIso.inv_hom_id_assoc]
  have key : Smooth $ inv e ≫ p4 W ≫ siI Z ≫ g := inferInstance
  rwa [hfac2] at key

theorem comap_eq_ker_fst {A B : Sch} (f : A ⟶ B) (I : ISD B) :
    I.comap f = (fst f I.si).ker := rfl

theorem ker_app_morphismRestrict_eq_map_ker {Y T : Sch} (m : Y ⟶ T) (V : Opn T)
    (P : V.toScheme.affineOpens)
    e :
    ker (hom ((m ∣_ V).app P.1))
      = map (hom (appLE (Scheme.Opens.ι V)
            (Scheme.Opens.ι V ''ᵁ P.1) P.1 e))
          (ker (hom (m.app (Scheme.Opens.ι V ''ᵁ P.1)))) := by
  let _c0 := p4 V ''ᵁ P.1
  let _c1 := p4 $ preU m V
  have hpre2 : ((mrU m V) ⁻¹ᵁ P.1)
      = Scheme.Opens.ι (m ⁻¹ᵁ V) ⁻¹ᵁ (m ⁻¹ᵁ _c0) := by
    rw [← comp_preimage, ← morphismRestrict_ι, comp_preimage, (Scheme.Opens.ι V).preimage_image_eq P.1]
  have hQV : _c0 ≤ V := Scheme.Opens.ι_image_le ..
  have himg : p4 (preU m V) ''ᵁ ((mrU m V) ⁻¹ᵁ P.1)
      = preU m _c0 := by
    rw [hpre2]
    exact image_preimage_opensio_of_le (preU m V) (preU m _c0) fun x hx => hQV hx
  have hbij := bijective_appLE_of_image_eq (p4 V)
    _c0 P.1 e rfl
  have hinj := an1 (bijective_appLE_of_image_eq
    _c1 (preU m _c0)
    (preU (mrU m V) P.1) hpre2.le himg)
  have hsq : appLE (p4 V) _c0 P.1 e ≫
        (mrU m V).app P.1
      = m.app _c0 ≫
        appLE _c1
          (preU m _c0) (preU (mrU m V) P.1) hpre2.le := by
    rw [app_eq_appLE (mrU m V), app_eq_appLE m,
      appLE_comp_appLE (mrU m V) (p4 V) _c0 P.1
        (preU (mrU m V) P.1) e le_rfl,
      appLE_comp_appLE _c1 m _c0
        (preU m _c0) (preU (mrU m V) P.1) le_rfl hpre2.le]
    exact appLE_congr_hom (morphismRestrict_ι m V) _ _ _ _
  have hsqr : ∀ x, (hom ((mrU m V).app P.1))
        ((hom
          (appLE (p4 V) _c0 P.1 e)) x)
      = hom (appLE _c1
          (preU m _c0) (preU (mrU m V) P.1) hpre2.le)
        ((hom (m.app _c0)) x) := by
    intro x
    simpa only [hom_comp, comp_apply] using (congrArg (fun mm => (hom mm) x) hsq)
  refine le_antisymm ?_ ?_
  intro y hy
  rw [mem_ker] at hy
  obtain ⟨x, rfl⟩ := an2 hbij y
  refine mem_map_of_mem _ ?_
  rw [mem_ker]
  apply hinj
  rw [← hsqr x, hy, map_zero]
  rw [map_le_iff_le_comap]
  intro x hx
  rw [mem_comap, mem_ker, hsqr x]
  rw [mem_ker] at hx
  rw [hx, map_zero]

theorem comap_opensio_eq_ker_morphismRestrict {T : Sch} (K : ISD T)
    (V : Opn T) : K.comap (Scheme.Opens.ι V) = (subschemeι K ∣_ V).ker := by
  rw [comap_eq_ker_fst, ← (isPullback_morphismRestrict K.si V).isoPullback_hom_fst, ker_comp_of_isIso]

section
variable {X : Sch} (Z : ISD X) (W : Z.subscheme.Opens) (hW : IsClosed (W : Set Z.subscheme)) (U : Opn X)
include hW
theorem restrictIdeal_openSubschemeKer_of_preimage_le
    (hU : (subschemeι Z ⁻¹ᵁ U) ≤ W) :
    restrictIdeal (openSubschemeKer Z W) U = restrictIdeal Z U := by
  have hrangeW : range (p4 W).base = W := by
    rw [q1]
  have hqcW : QuasiCompact (p4 W) := by
    refine ⟨fun V _ hVc => ?_⟩
    refine ((p4 W).isEmbedding.toIsInducing).isCompact_iff.mpr ?_
    rw [image_preimage_eq_inter_range, hrangeW]
    exact hVc.inter_right hW
  let _a4 := p4 W ≫ siI Z
  have hqc : QuasiCompact _a4 := inferInstance
  let _a6 := openSubschemeKer Z W
  have hqc1 : QuasiCompact (_a6.si.mr U) := inferInstance
  have hqc2 : QuasiCompact (Z.si.mr U) := inferInstance
  rw [restrictIdeal_eq_comap_io (openSubschemeKer Z W) U, restrictIdeal_eq_comap_io Z U,
    comap_opensio_eq_ker_morphismRestrict (openSubschemeKer Z W) U,
    comap_opensio_eq_ker_morphismRestrict Z U]
  refine m29 ?_
  funext P
  have hQaff :=
    P.2.image_of_isOpenImmersion (p4 U)
  have hpre : p4 U ⁻¹ᵁ (p4 U ''ᵁ P.1) = P.1 :=
    (p4 U).preimage_image_eq P.1
  have e : P.1 ≤ p4 U ⁻¹ᵁ (p4 U ''ᵁ P.1) := hpre.ge
  have hQU : (p4 U ''ᵁ P.1) ≤ U := Scheme.Opens.ι_image_le ..
  have hmono : siI Z ⁻¹ᵁ (p4 U ''ᵁ P.1) ≤ (siI Z ⁻¹ᵁ U) :=
    fun x hx => hQU hx
  let _a0 := hom $ (p4 W ≫ siI Z).app (p4 U ''ᵁ P.1)
  let _a2 := hom $ _a6.subschemeι.app (p4 U ''ᵁ P.1)
  have hkerA : ker _a2
      = ker _a0 := by
    have h1 := ker_apply (openSubschemeKer Z W).si
      ⟨p4 U ''ᵁ P.1, hQaff⟩
    have h2 := ker_apply _a4
      ⟨p4 U ''ᵁ P.1, hQaff⟩
    rw [q2] at h1
    rw [← h1, ← h2, openSubschemeKer_eq_ker]
  let _a1 := Z.subschemeι.app $ p4 U ''ᵁ P.1
  have hmain : ker _a2
      = ker (hom
        _a1) := by
    rw [hkerA]
    ext x
    let _a3 := (p4 W).app (siI Z ⁻¹ᵁ (p4 U ''ᵁ P.1))
    have hfac : _a0 x
        = hom _a3
          ((hom _a1) x) := by
      show (hom (_a1 ≫
        _a3)) x = _
      rw [hom_comp, comp_apply]
    simp only [mem_ker, hfac]
    constructor
    intro hx
    exact injective_app_opensio_of_le W (siI Z ⁻¹ᵁ (p4 U ''ᵁ P.1)) (le_trans hmono hU) $ tr_ hx (map_zero _).symm
    intro hx
    exact tr_ (congrArg _ hx) (map_zero _)
  rw [ker_apply (_a6.si.mr U) P,
    ker_apply (Z.si.mr U) P,
    ker_app_morphismRestrict_eq_map_ker (openSubschemeKer Z W).si U P e,
    ker_app_morphismRestrict_eq_map_ker Z.si U P e, hmain]

theorem restrictIdeal_openSubschemeKer_eq_top
    (hU : ∀ w : subscheme Z, w ∈ W → Z.subschemeι.base w ∉ U) :
    restrictIdeal (openSubschemeKer Z W) U = ⊤ := by
  let _c0 := openSubschemeKer Z W
  have hnot : ∀ y : subS _c0,
      _c0.subschemeι.base y ∉ U := by
    intro y hy
    have hmem : _c0.subschemeι.base y ∈ (spI _c0 : Set X) := by
      rw [← range_subschemeι]
      exact mem_range_self y
    rw [support_openSubschemeKer Z W hW] at hmem
    obtain ⟨w, hwW, hw⟩ := hmem
    refine hU w hwW ?_
    rwa [hw]
  let _a0 := oSch $ siPre _c0 U
  have hempty : ∀ _y : _a0, False := by
    intro y
    have h1 : bsM (p4 $ siPre _c0 U) y ∈
        (siPre _c0 U : Set _c0.subscheme) := by
      rw [← Scheme.Opens.range_ι]
      exact mem_range_self y
    exact hnot _ h1
  have hObot : ∀ O : Opn _a0, O = ⊥ := by
    intro O
    refine le_antisymm ?_ bot_le
    intro y _
    exact (hempty y).elim
  rw [restrictIdeal_eq_comap_io, comap_opensio_eq_ker_morphismRestrict _c0 U]
  refine m29 ?_
  funext V
  have hker : ker (hom
      ((_c0.si.mr U).app V.1)) = ⊤ := by
    have := subsingleton_sections_of_eq_bot
      (preU (_c0.si.mr U) V.1) $ hObot _
    rw [eq_top_iff_one, mem_ker]
    exact elim _ _
  rw [ker_apply (_c0.si.mr U) V, hker]
  simp
end




section
variable {S : Type} [CommRing S]
theorem comap_C_map_C (I : Ideal S) :
    comap (Polynomial.C : S →+* Polynomial S) (I.map (Polynomial.C : S →+* Polynomial S))
      = I := by
  refine Ideal.ext fun a => ?_
  constructor
  intro h
  simpa using (mp_ (mem_map_C_iff) h 0)
  intro h
  exact mem_map_of_mem _ h

theorem map_C_ne_of_isMaximal (N : Ideal S) (hN : N.IsMaximal)
    (M' : Ideal $ Polynomial S) (hM' : M'.IsMaximal) :
    N.map (Polynomial.C : S →+* Polynomial S) ≠ M' := by
  intro h
  have hX : Polynomial.X ∉ M' := by
    rw [← h]
    intro hmem
    have h1 := mp_ (mem_map_C_iff) hmem 1
    rw [coeff_X_one] at h1
    exact hN.ne_top $ mpr_ (eq_top_iff_one N) h1
  obtain ⟨y, i, hi, hyi⟩ := hM'.exists_inv hX
  rw [← h] at hi
  have h0 : (y * Polynomial.X + i).coeff 0 = (1 : Polynomial S).coeff 0 := by rw [hyi]
  rw [coeff_add, coeff_one_zero, mul_coeff_zero,
    coeff_X_zero, mul_zero, zero_add] at h0
  refine hN.ne_top $ mpr_ (eq_top_iff_one N) ?_
  rw [← h0]
  exact mp_ (mem_map_C_iff) hi 0

theorem isMaximal_comap_C [IsJacobsonRing S]
    (M' : Ideal (Polynomial S)) (hM' : M'.IsMaximal) :
    (comap (Polynomial.C : S →+* Polynomial S) M').IsMaximal := by
  have hbot : (⊥ : (Ideal $ Polynomial S ⧸ M')).IsMaximal := by
    let fieldQuot := field M'
    exact bot_isMaximal
  let _a0 := (mk M').comp (m141 : S →+* Polynomial S)
  have hmax := isMaximal_comap_of_isIntegral_of_isMaximal'
    _a0 (quotient_mk_comp_C_isIntegral_of_isJacobsonRing M')
    (⊥)
  have hker : comap _a0
      (⊥) = comap m141 M' := by
    refine Ideal.ext fun a => ?_
    rw [mem_comap, mem_comap, mem_bot, comp_apply,
      eq_zero_iff_mem]
  rwa [← hker]
end

section
variable {A B : Type} [CommRing A] [CommRing B] (ph_ : A ≃+* B)
theorem comap_comap_symm
    I : comap (ph_ : A →+* B) (comap (ph_.symm : B →+* A) I) = I :=by simp_all
theorem comap_symm_comap
    J : comap (ph_.symm : B →+* A) (comap (ph_ : A →+* B) J) = J := by
  refine Ideal.ext fun b => ?_
  have h : (ph_ : RingHom A B) ((ph_.symm : RingHom B A) b) = b := ph_.apply_symm_apply b
  constructor
  intro hmem
  have hmem' : (ph_ : RingHom A B) ((ph_.symm : RingHom B A) b) ∈ J := hmem
  rwa [h] at hmem'
  intro hmem
  show (ph_ : RingHom A B) ((ph_.symm : RingHom B A) b) ∈ J
  rwa [h]

theorem exists_ltSeries_comap
    (s : LTSeries $ PrimeSpectrum B) :
    ∃ t : LTSeries $ PrimeSpectrum A, t.length = s.length ∧
      t.last.asIdeal = comap (ph_ : A →+* B) s.last.asIdeal := by
  let _m0 := (ph_ : RingHom A B)
  have hmono : Monotone $ PrimeSpectrum.comap _m0 := by
    intro p q h
    rw [← asIdeal_le_asIdeal, comap_asIdeal,
      PrimeSpectrum.comap_asIdeal]
    exact comap_mono $ mpr_ (PrimeSpectrum.asIdeal_le_asIdeal p q) h
  have hinj : m120 $ PrimeSpectrum.comap _m0 := by
    intro p q h
    have h' : Ideal.comap _m0 p.asIdeal = Ideal.comap _m0 q.asIdeal := by
      rw [← comap_asIdeal, ← comap_asIdeal, h]
    have h2 := congrArg (comap (ph_.symm : RingHom B A)) h'
    rw [comap_symm_comap ph_ p.asIdeal, comap_symm_comap ph_ q.asIdeal] at h2
    exact m210 h2
  exact ⟨⟨s.length, fun i => PrimeSpectrum.comap _m0 $ s i, fun i => hmono.strictMono_of_injective hinj $ s.step i⟩,
    rfl, rfl⟩
end

section
variable {Y W : Sch} (f : Y ⟶ W) [Etale f] (y) [IsNoetherianRing (Y.presheaf.stalk y)] [_root_.IsRegularLocalRing (W.presheaf.stalk (f.base y))]
theorem ringKrullDim_stalk_le_of_etale :
    ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (W.presheaf.stalk $ f.base y) := by
  let _c0 := stkX W $ bsM f y
  let algStalk :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom $ algebraMap _c0 $ stkX Y y :=
    inferInstanceAs $ IsLocalHom (f.stalkMap y).hom
  have : Flat _c0 $ stkX Y y :=
    stalkMap f y
  have : EssFiniteType _c0 $ stkX Y y := AlgebraicGeometry.LocallyOfFiniteType.stalkMap f y
  have : FormallyUnramified _c0 $ stkX Y y := AlgebraicGeometry.FormallyUnramified.stalkMap f y
  exact le_of_eq $ FunctorialResolution.EmbeddedResolution.ringKrullDim_eq_of_flat_formallyUnramified
    _c0 $ stkX Y y

theorem ringKrullDim_stalk_eq_of_etale :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (W.presheaf.stalk $ f.base y) := by
  let _c0 := stkX W $ bsM f y
  let algStalk :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom $ algebraMap _c0 $ stkX Y y :=
    inferInstanceAs $ IsLocalHom (f.stalkMap y).hom
  have : Flat _c0 $ stkX Y y :=
    stalkMap f y
  have : EssFiniteType _c0 $ stkX Y y := AlgebraicGeometry.LocallyOfFiniteType.stalkMap f y
  have : FormallyUnramified _c0 $ stkX Y y := AlgebraicGeometry.FormallyUnramified.stalkMap f y
  exact FunctorialResolution.EmbeddedResolution.ringKrullDim_eq_of_flat_formallyUnramified
    _c0 $ stkX Y y
end

section
variable (X : Sch) (x : X)
noncomputable def fromSpecStalkPoint
    (p : PrimeSpectrum $ X.presheaf.stalk x) : X :=
  (X.fromSpecStalk x).base p

theorem exists_fromSpecStalkPoint_eq_of_specializes {y} (h : y ⤳ x) :
    ∃ p : PrimeSpectrum $ X.presheaf.stalk x, fromSpecStalkPoint X x p = y := by
  have hy : y ∈ range (X.fromSpecStalk x).base := by
    rwa [range_fromSpecStalk]
  obtain ⟨p, hp⟩ := hy
  exact ⟨p, hp⟩

theorem le_ringKrullDim_stalk_of_chain n
    z (hspec : ∀ i, z i ⤳ x)
    (hmono : ∀ i j : Fin (n + 1), i < j → z i ⤳ z j) (hinj : Function.Injective z) :
    ((n : ENat) : WithBot ENat) ≤ ringKrullDim (X.presheaf.stalk x) := by
  choose q hq using fun i => exists_fromSpecStalkPoint_eq_of_specializes X x $ hspec i
  have hstep : ∀ i : Fin n, q i.castSucc < q i.succ := by
    intro i
    have h1 : fromSpecStalkPoint X x (q i.castSucc) ⤳ fromSpecStalkPoint X x (q i.succ) := by simp_all
    have hle :=
      (le_iff_specializes _ _).mpr
        (mp_ ((isEmbedding (X.fromSpecStalk x)).toIsInducing.specializes_iff) h1)
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hz : z i.castSucc = z i.succ := by
      rw [← hq i.castSucc, ← hq i.succ, hEq]
    exact absurd (hinj hz) Fin.castSucc_lt_succ.ne
  have hlen :=
    le_iSup (fun t : LTSeries (PrimeSpectrum (stkX X x)) => (t.length : WithBot ENat))
      ⟨n, q, hstep⟩
  have hcast : ((n : ENat) : WithBot ENat) = ((n : ℕ) : WithBot ENat) := by norm_cast
  rwa [hcast]

theorem ringKrullDim_stalk_le_topologicalKrullDim :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  exact le_trans ((topologicalKrullDim_eq_ringKrullDim _).ge) (isEmbedding $ X.fromSpecStalk x).toIsInducing.topologicalKrullDim_le
end

section
variable (k : Type) [Field k]
theorem exists_ltSeries_of_isMaximal_mvPolynomial :
    ∀ m (M : Ideal $ MvPolynomial (Fin m) k), M.IsMaximal →
      ∃ s : LTSeries $ PrimeSpectrum $ MvPolynomial (Fin m) k,
        s.length = m ∧ s.last.asIdeal = M := by
  intro m
  induction m with
  | zero =>
    intro M hM
    exact ⟨RelSeries.singleton _ ⟨M, hM.isPrime⟩, rfl, rfl⟩
  | succ n ih =>
    intro M hM
    let _a0 := MvPolynomial (Fin n) k
    have hJ : IsJacobsonRing _a0 := by
      have : FiniteType k _a0 := inferInstance
      exact isJacobsonRing_of_finiteType (A := k)
    let ph_ :=
      (finSuccEquiv k n).toRingEquiv
    let M' :=
      comap
        ph_.symm M
    have hM'max : M'.IsMaximal :=
      comap_isMaximal_of_surjective _ $ RingEquiv.surjective ph_.symm
    let N :=
      comap
        m141 M'
    have hNmax := isMaximal_comap_C M' hM'max
    obtain ⟨t, htlen, htlast⟩ := ih N hNmax
    let _a2 := PrimeSpectrum $ Polynomial _a0
    have hFs : StrictMono fun p : PrimeSpectrum _a0 =>
        (⟨p.asIdeal.map
            m141,
          (isPrime_map_C_iff_isPrime p.asIdeal).mpr p.isPrime⟩ :
          _a2) := by
      refine Monotone.strictMono_of_injective ?_ ?_
      intro p q hpq
      rw [← asIdeal_le_asIdeal]
      exact map_mono $ mpr_ (asIdeal_le_asIdeal p q) hpq
      intro p q hpq
      have h' : p.asIdeal.map
            m141
          = q.asIdeal.map
            m141 :=
        congrArg asIdeal hpq
      refine m210 ?_
      rw [← comap_C_map_C p.asIdeal, ← comap_C_map_C q.asIdeal, h']
    let t1 : LTSeries _a2 :=
      ⟨t.length, fun i => ⟨(t i).asIdeal.map
          m141,
        (isPrime_map_C_iff_isPrime (t i).asIdeal).mpr (t i).isPrime⟩,
        fun i => hFs $ t.step i⟩
    have ht1last : t1.last.asIdeal = N.map
        m141 := by
      show (t.last).asIdeal.map
          m141 = _
      rw [htlast]
    have hle : t1.last.asIdeal ≤ M' := by
      rw [ht1last]
      exact Ideal.map_le_iff_le_comap.mpr le_rfl
    have hlt : t1.last <
        (⟨M', hM'max.isPrime⟩ : _a2) := by
      refine lt_of_le_of_ne (mp_ (asIdeal_le_asIdeal _ _) hle) ?_
      intro hEq
      have hEq' := congrArg asIdeal hEq
      rw [ht1last] at hEq'
      exact map_C_ne_of_isMaximal N hNmax M' hM'max hEq'
    obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_comap ph_ $ t1.snoc _ hlt
    refine ⟨s, ?_, ?_⟩
    rw [hslen]
    show t.length + 1 = n + 1
    rw [htlen]
    rw [hslast, RelSeries.last_snoc]
    exact comap_comap_symm ph_ M

end

theorem specializes_of_fromSpecStalk_base_specializes {X : Sch} x
    {a b}
    (hab : (X.fromSpecStalk x).base a ⤳ (X.fromSpecStalk x).base b) : a ⤳ b := by
  exact (isEmbedding $ X.fromSpecStalk x).toIsInducing.specializes_iff.mp hab

section
variable {X : Sch} (U : Opn X) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
include hU hne
theorem exists_isClosed_singleton_of_isAffineOpen :
    ∃ x, IsClosed ({x} : Set U.toScheme) := by
  have : IsAffine U.toScheme := hU
  obtain ⟨x0, hx0⟩ := hne
  let A := oSch U
  let a : oSch U := ⟨x0, hx0⟩
  let _a0 := Γ(A, ⊤)
  have h : A ≃ₜ PrimeSpectrum _a0 := homeoOfIso A.isoSpec
  have hp : PrimeSpectrum _a0 := h a
  obtain ⟨M, hM, -⟩ := exists_le_maximal hp.asIdeal hp.isPrime.ne_top
  refine ⟨h.symm ⟨M, hM.isPrime⟩, ?_⟩
  have hq : IsClosed ({(⟨M, hM.isPrime⟩ : PrimeSpectrum _a0)} :
      Set $ PrimeSpectrum _a0) :=
    (isClosed_singleton_iff_isMaximal _).mpr hM
  have h2 := h.symm.isClosedMap _ hq
  rwa [image_singleton] at h2

theorem exists_mem_isClosed_singleton_of_isAffineOpen :
    ∃ x, ∃ hx, IsClosed ({(⟨x, hx⟩ : toScheme U)} : Set U.toScheme) := by
  obtain ⟨x, hx⟩ := exists_isClosed_singleton_of_isAffineOpen U hU hne
  obtain ⟨y, hy⟩ := x
  exact ⟨y, hy, hx⟩
end

theorem topologicalKrullDim_spec_le_ringKrullDim R :
    topologicalKrullDim ↥(Spec R) ≤ ringKrullDim ↥R := by
  exact le_of_eq $ topologicalKrullDim_eq_ringKrullDim R

section
variable {k : Type} [Field k] {m} {Y : Sch} (c : Y ⟶ AffineSpace (UFin m) (Sp k)) [Etale c] (y) [IsNoetherianRing (Y.presheaf.stalk y)]
include c
theorem ringKrullDim_stalk_le_of_etale_affineSpace :
    ringKrullDim (Y.presheaf.stalk y) ≤ ((m : ENat) : WithBot ENat) := by
  have hreg :=
    isRegularLocalRing_stalk_affineSpace k (UFin m) $ bsM c y
  let _a0 := AffineSpace (UFin m) $ Sp k
  have h2 := ringKrullDim_stalk_le_topologicalKrullDim
      _a0 $ bsM c y
  let _a1 := MvU m k
  have _i36 : topologicalKrullDim _a0 ≤ ringKrullDim _a1 := by
    exact ((Homeomorph.isEmbedding $ homeoOfIso $ m69 (UFin m) $ m10 k).toIsInducing.topologicalKrullDim_le).trans
      (topologicalKrullDim_spec_le_ringKrullDim
        (m10 _a1))
  refine (ringKrullDim_stalk_le_of_etale c y).trans $ h2.trans $ _i36.trans
    ?_
  have he :=
    ringKrullDim_eq_of_ringEquiv
      (renameEquiv k (ulift : UFin m ≃ Fin m)).toRingEquiv
  rw [he]
  simp

theorem ringKrullDim_stalk_eq_of_etale_affineSpace
    (hy : IsClosed ({y} : Set Y)) :
    ringKrullDim (Y.presheaf.stalk y) = ((m : ENat) : WithBot ENat) := by
  have hreg :=
    isRegularLocalRing_stalk_affineSpace k (UFin m) $ c.base y
  refine le_antisymm (ringKrullDim_stalk_le_of_etale_affineSpace c y) ?_
  have heq := ringKrullDim_stalk_eq_of_etale c y
  rw [heq]
  let x := c.base y
  let _c0 := UFin m
  let e :=
    homeoOfIso $ m69 _c0 $ m10 k
  have hclosed : IsClosed ({e x} : Set $ PrimeSpectrum $ MvPolynomial _c0 k) := by
    have h2 := e.isClosedMap _ $ closePoints_subset_preimage_closedPoints c hy
    rwa [image_singleton] at h2
  have hmax :=
    (isClosed_singleton_iff_isMaximal $ e x).mp hclosed
  obtain ⟨s, hslen, hslast⟩ : ∃ s : LTSeries $ PrimeSpectrum $ MvU m k, s.length = m ∧ s.last.asIdeal = asIdeal (e x) := by
    let M := asIdeal $ e x
    let ph_ : MvU m k ≃+* MvPolynomial (Fin m) k :=
      (renameEquiv k ulift).toRingEquiv
    have hmax :
        (comap (ph_.symm : MvPolynomial (Fin m) k →+* MvU m k)
          M).IsMaximal :=
      comap_isMaximal_of_surjective _ $ RingEquiv.surjective ph_.symm
    obtain ⟨t, htlen, htlast⟩ := exists_ltSeries_of_isMaximal_mvPolynomial k m _ hmax
    obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_comap ph_ t
    refine ⟨s, by rw [hslen, htlen], ?_⟩
    rw [hslast, htlast]
    exact comap_comap_symm ph_ M
  have hlast := m210 hslast
  have hspec : ∀ i, (fun j => e.symm $ s j) i ⤳ x := by
    intro i
    have h1 := s.strictMono.monotone $ le_last i
    have h2 : (s i) ⤳ s.last := (le_iff_specializes _ _).mp h1
    have h3 := h2.map e.symm.continuous
    rwa [hlast, e.symm_apply_apply] at h3
  have hmono : ∀ i j, i < j → (fun l => e.symm $ s l) i ⤳ (fun l => e.symm $ s l) j := by
    intro i j hij
    have h1 := s.strictMono hij
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp h1.le).map e.symm.continuous
  have hinj : m120 fun i => e.symm $ s i := by
    intro i j hij
    exact s.strictMono.injective $ e.symm.injective hij
  have key := le_ringKrullDim_stalk_of_chain
    (AffineSpace _c0 $ Sp k) x s.length
    (fun i => e.symm $ s i) hspec hmono hinj
  rwa [hslen] at key
end

theorem topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le (X : Sch) d
    (h : ∀ x, ringKrullDim (X.presheaf.stalk x) ≤ d) :
    topologicalKrullDim X ≤ d := by
  unfold topologicalKrullDim
  refine iSup_le fun p => ?_
  have hSM := p.strictMono
  let _a2 := Fin $ p.length + 1
  have key : ∀ i : _a2, ∃ z : X, closure ({z} : Set X) = (p i) := by
    intro i
    obtain ⟨z, hz⟩ := m140 (p i).isIrreducible' (p i).isClosed'
    exact ⟨z, hz⟩
  choose y hy using key
  have hspec : ∀ i j : _a2, i ≤ j → y j ⤳ y i := by
    intro i j hij
    have hmem : y i ∈ closure ({y j} : Set X) := by
      rw [hy j]
      apply SetLike.coe_subset_coe.mpr (hSM.monotone hij)
      rw [← hy i]
      exact subset_closure rfl
    exact mpr_ specializes_iff_mem_closure hmem
  have hinj : m120 y := by
    intro i j hij
    apply hSM.injective
    apply SetLike.coe_injective
    rw [← hy i, ← hy j, hij]
  let _a0 := X.fromSpecStalk $ y 0
  let _a1 := PrimeSpectrum $ stkX X (y 0)
  have hrange : ∀ i : _a2,
      ∃ z : _a1, bsM _a0 z = y i := by
    intro i
    have hmem : y i ∈ range _a0.base := by
      rw [range_fromSpecStalk]
      exact hspec 0 i $ zero_le i
    exact hmem
  choose q hq using hrange
  have hg : StrictMono fun i : _a2 => q i.rev := by
    intro i j hij
    have hsp : bsM _a0 (q i.rev) ⤳ _a0.base (q j.rev) := by
      rw [hq i.rev, hq j.rev]
      exact hspec j.rev i.rev (mpr_ rev_lt_rev hij).le
    refine lt_of_le_of_ne ((le_iff_specializes _ _).mpr (specializes_of_fromSpecStalk_base_specializes (y 0) hsp)) ?_
    intro hcon
    have h4 := congrArg rev $ hinj ((st_ (hq i.rev)) (tr_ (congrArg (fun z : _a1 => _a0.base z) hcon) (hq j.rev)))
    rw [rev_rev, rev_rev] at h4
    exact absurd h4 $ ne_of_lt hij
  exact le_trans (le_iSup (fun t : LTSeries _a1 => (t.length : WithBot ENat)) ⟨p.length, fun i => q i.rev, fun i => hg castSucc_lt_succ⟩) $ h (y 0)

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

section
variable {n} (P) [DecidablePred P] {o : Option (Fin n)} {j : Fin n}
theorem eq_some_and_not_of_bind_ite_eq_some
    (h : o.bind (fun j0 => if P j0 then none else some j0) = some j) : o = some j ∧ ¬ P j := by
  cases o with
  | none => simp at h
  | some j0 =>
    by_cases hb : P j0
    simp_all
    simp_all

theorem of_bind_ite_eq_none (hg : o = some j)
    (h : o.bind (fun j0 => if P j0 then none else some j0) = none) : P j :=by simp_all
end

section
variable {X : Sch}
theorem eq_top_of_forall_ideal_eq_top (I : ISD X)
    (h : ∀ W : X.affineOpens, I.ideal W = ⊤) : I = ⊤ := by
  have hfun : I.ideal = (⊤ : ISD X).ideal := by
    funext W
    have htop : (⊤ : ISD X).ideal W = ⊤ := rfl
    rw [h W, htop]
  exact m29 hfun

theorem mem_support_iff_forall_notMem_basicOpen (I : ISD X)
    {x} {U} (hU : IsAffineOpen U) (hx : x ∈ U) :
    x ∈ support I ↔ ∀ f ∈ I.ideal ⟨U, hU⟩, x ∉ basicOpen X f := by
  have h0 : x ∈ spI I ↔
      x ∈ X.zeroLocus ((I.ideal ⟨U, hU⟩) : Set U.sec) :=
    mem_support_iff_of_mem hx
  rw [h0, mem_zeroLocus_iff]
  exact m22

private theorem mem_basicOpen_iff_notMem_primeIdealOf {U : Opn X}
    (hU : IsAffineOpen U) (f : (X.sec U)) (x : ↥U) :
    (x : ↥X) ∈ basicOpen X f ↔ f ∉ asIdeal (hU.primeIdealOf x) := by
  have h2 :=
    fromSpec_primeIdealOf hU x
  have h1 :=
    fromSpec_preimage_basicOpen hU f
  constructor
  intro hx
  have hmem : primeIdealOf hU x
      ∈ fromSpec hU ⁻¹ᵁ bOpn X f := by
    show bsM (fromSpec hU)
      (primeIdealOf hU x) ∈ bOpn X f
    rwa [h2]
  rw [h1] at hmem
  exact mp_ (m209 f _) hmem
  intro hx
  have hmem :=
    mpr (m209 f _) hx
  rw [← h1] at hmem
  have h3 : bsM (fromSpec hU)
      (primeIdealOf hU x) ∈ bOpn X f := hmem
  rwa [h2] at h3

section
variable (I : ISD X) {x} {U} (hU : IsAffineOpen U) (hx : x ∈ U) (g) (hI : I.ideal ⟨U, hU⟩ = span {g})
include hx hI
theorem mem_support_of_ideal_eq_span_singleton (hg : x ∉ basicOpen X g) : x ∈ support I := by
  rw [mem_support_iff_forall_notMem_basicOpen I hU hx]
  intro f hf
  rw [hI, mem_span_singleton] at hf
  obtain ⟨a, rfl⟩ := hf
  have hle : bOpn X (g * a) ≤ bOpn X g := by simp_all
  exact fun hc => hg $ hle hc

theorem mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton (hs : x ∈ support I) :
    g ∈ asIdeal (hU.primeIdealOf ⟨x, hx⟩) := by
  have h := mp_ (mem_support_iff_forall_notMem_basicOpen I hU hx) hs g
    (by rw [hI]; exact mem_span_singleton_self g)
  by_contra hc
  exact h $ mpr_ (mem_basicOpen_iff_notMem_primeIdealOf hU g ⟨x, hx⟩) hc
end
end

theorem subschemeio_base_mem_support_of_subscheme {W : Sch} (Z : ISD W)
    z : Z.subschemeι.base z ∈ support Z := by
  have h : Z.subschemeι.base z ∈ range Z.subschemeι.base := ⟨z, rfl⟩
  rwa [q5] at h

theorem restrictIdeal_eq_top_of_le_basicOpen {X : Sch} {U}
    (hU : IsAffineOpen U) (I : ISD X) f
    (hI : I.ideal ⟨U, hU⟩ = span {f}) {V : Opn X} (hVb : V ≤ basicOpen X f) :
    restrictIdeal I V = ⊤ := by
  have hbU := X.basicOpen_le f
  rw [restrictIdeal_eq_comap_io]
  refine eq_top_of_forall_ideal_eq_top _ ?_
  intro Wa
  have e : Wa ≤ opI V ⁻¹ᵁ U := fun x _ => (hVb.trans hbU) x.2
  have e' : Wa ≤ opI V ⁻¹ᵁ bOpn X f := fun x _ => hVb x.2
  rw [comap_ideal_eq_span_image I V.i ⟨U, hU⟩ Wa e {f} hI,
    image_singleton, span_singleton_eq_top]
  let _a1 := pMap X (homOfLE hbU).op
  let _a2 := V.ι.appLE (bOpn X f) Wa e'
  have hfac : V.ι.appLE U Wa e
      = _a1 ≫
        _a2 := by
    rw [map_appLE]
  have hcp : ((_a1 ≫
        _a2).hom) f
      = _a2.hom
          (_a1.hom f) := rfl
  rw [hfac, hcp]
  exact IsUnit.map _ $ X.toRingedSpace.isUnit_res_basicOpen f

section
variable (m) (S : FinSet m)
def complOrderEmbInv (t : Fin m) : Option $ Fin $ m - S.card :=
  if h : t ∈ S then none else some $ Classical.choose (exists_complOrderEmb_eq m S h)

theorem complInv_def t :
    complOrderEmbInv m S t =
      if h : t ∈ S then none else some $ Classical.choose (exists_complOrderEmb_eq m S h) :=
  rfl

section
variable (o : Option (Fin m))
theorem eq_some_complOrderEmb_of_bind_complInv_eq_some
    j (h : o.bind (complOrderEmbInv m S) = some j) :
    o = some (complOrderEmb m S j) := by
  cases o with
  | none => simp at h
  | some t =>
    have _i37 : complOrderEmbInv m S t = some j ↔ complOrderEmb m S j = t := by
      constructor
      intro h
      by_cases ht : t ∈ S
      rw [complInv_def, dif_pos ht] at h
      simp at h
      rw [complInv_def, dif_neg ht] at h
      have hspec := choose_spec $ exists_complOrderEmb_eq m S ht
      rwa [m105 h] at hspec
      intro h
      have ht : t ∉ S := by
        rw [← h]
        exact complOrderEmb_notMem m S j
      rw [complInv_def, dif_neg ht]
      have heq : Classical.choose (exists_complOrderEmb_eq m S ht) = j :=
        (complOrderEmb m S).injective $ by rw [choose_spec $ exists_complOrderEmb_eq m S ht, h]
      rw [heq]
    rw [mp_ _i37 h]

theorem eq_none_of_bind_complInv_eq_none
    (hnot : ∀ t, o = some t → t ∉ S) (h : o.bind (complOrderEmbInv m S) = none) : o = none := by
  cases o with
  | none => rfl
  | some t =>
    exfalso
    have h' : complOrderEmbInv m S t = none := h
    rw [complInv_def, dif_neg $ hnot t rfl] at h'
    simp at h'
end
end

section

variable {Y Y' : Sch} {k : Type} [Field k] {p : Y ⟶ Sp k}
  {V : Opn Y} {n : ℕ}

section
variable (c : EtaleChart p V n) (f : Y' ⟶ Y) [IsOpenImmersion f]
theorem morphismRestrict_comp_map_comp_affineSpaceFinToSpec :
    (morphismRestrict f V ≫ c.map) ≫ affineSpaceFinToSpec k n = ι (f ⁻¹ᵁ V) ≫ (f ≫ p) := by
  rw [assoc, c.comp_struct, ← assoc, morphismRestrict_ι, assoc]

theorem etale_morphismRestrict_comp_map :
    Etale $ morphismRestrict f V ≫ c.map := by
  let _a0 := morphismRestrict f V
  have h0 : IsOpenImmersion $ _a0 ≫ opI V := by
    rw [morphismRestrict_ι]
    infer_instance
  have h1 := c.isEtale
  have h3 : Etale _a0 := inferInstance
  infer_instance

def EtaleChart.pullbackOpenImmersion :
    EtaleChart (f ≫ p) (pre f V) n :=
  ⟨morphismRestrict f V ≫ c.map, morphismRestrict_comp_map_comp_affineSpaceFinToSpec c f,
    etale_morphismRestrict_comp_map c f⟩

theorem EtaleChart.pullbackOpenImmersion_map :
    (c.pullbackOpenImmersion f).map = morphismRestrict f V ≫ c.map :=
  rfl

theorem restrictIdeal_comap_eq_coordIdeal_pullbackOpenImmersion (D : ISD Y) S
    (h : restrictIdeal D V = c.coordIdeal S) :
    restrictIdeal (D.comap f) (pre f V) = (c.pullbackOpenImmersion f).coordIdeal S := by
  have h1 : (c.pullbackOpenImmersion f).coordIdeal S
      = cmI (c.coordIdeal S) (morphismRestrict f V) := by
    rw [coordIdeal_eq_comap_coordSubspaceIdeal, coordIdeal_eq_comap_coordSubspaceIdeal,
      EtaleChart.pullbackOpenImmersion_map, comap_comp]
  rw [h1, ← h, restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
    ← morphismRestrict_ι, comap_comp]
end

end

theorem restrictIdeal_comap_preimage_eq_top {Y Y' : Sch} (f : Y' ⟶ Y) (V : Opn Y)
    (D : ISD Y) (h : restrictIdeal D V = ⊤) :
    restrictIdeal (D.comap f) (pre f V) = ⊤ := by
  have h1 : restrictIdeal (D.comap f) (pre f V)
      = (restrictIdeal D V).comap (morphismRestrict f V) := by
    rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
      ← morphismRestrict_ι, comap_comp]
  rw [h1, h, comap_top]

theorem image_subset_of_image_inter_subset {al_ : Type} {be_ : Type} [TopologicalSpace al_]
    [TopologicalSpace be_] {A O : Set al_} {g : al_ → be_} {C : Set be_} (hA : IsIrreducible A)
    (hO : IsOpen O) (hAO : (A ∩ O).Nonempty) (hg : Continuous g) (hC : IsClosed C)
    (h : g '' (A ∩ O) ⊆ C) : g '' A ⊆ C := by
  have hsub : A ⊆ closure (A ∩ O) := by
    intro x hx
    rw [mem_closure_iff]
    intro u hu hxu
    obtain ⟨z, hz⟩ := an2 hA u O hu hO ⟨x, hx, hxu⟩ hAO
    exact ⟨z, hz.2.1, an1 hz, hz.2.2⟩
  rintro _ ⟨x, hx, rfl⟩
  exact closure_minimal h hC $ image_closure_subset_closure_image hg ⟨x, hsub hx, rfl⟩

section

variable {X : Sch} {k : Type} [Field k] {p : X ⟶ Sp k}

theorem exists_etaleChart_coord_mem_primeIdealOf (F : Bdy X) y (U : Opn X)
    (hU : IsAffineOpen U) (hyU : y ∈ U) {n : ℕ} (c : EtaleChart p U n) (ga_ : ℕ → Option (Fin n))
    (hdesc : ∀ i, ∀ hi : i < length F,
      (ga_ i = none → restrictIdeal (F[i]'hi) U = ⊤) ∧
        ∀ j, ga_ i = some j → restrictIdeal (F[i]'hi) U = c.coordIdeal {j})
    (hinj : ∀ i i', i < length F → i' < length F → ∀ j, ga_ i = some j → ga_ i' = some j → i = i') :
    ∃ (U' : Opn X) (hU' : IsAffineOpen U') (hy' : y ∈ U') (n' : ℕ)
      (c' : EtaleChart p U' n') (ga' : ℕ → Option (Fin n')),
      (∀ i, ∀ hi,
        (ga' i = none → restrictIdeal (F[i]'hi) U' = ⊤) ∧
          ∀ j, ga' i = some j → restrictIdeal (F[i]'hi) U' = c'.coordIdeal {j}) ∧
      (∀ i i', i < length F → i' < length F → ∀ j, ga' i = some j → ga' i' = some j → i = i') ∧
      (∀ i, i < length F → ∀ j, ga' i = some j →
        c'.coord j ∈ (hU'.primeIdealOf ⟨y, hy'⟩).asIdeal) := by
  let _c0 := hU.primeIdealOf ⟨y, hyU⟩
  classical
  set notInPrime : FinSet n :=
    Finset.univ.filter (c.coord · ∉ _c0.asIdeal) with hBadDef
  have hBad : ∀ j, j ∈ notInPrime ↔ c.coord j ∉ _c0.asIdeal := by
    intro j
    rw [hBadDef]
    simp
  set t : X.sec U := ∏ j ∈ notInPrime, c.coord j with htdef
  have ht : t ∉ _c0.asIdeal := by
    have hmem :=
      fun j hj => mp_ (hBad j) hj
    have hprod := prod_mem (primeCompl _c0.asIdeal) hmem
    rwa [← htdef] at hprod
  have hUt := hU.basicOpen t
  have hle := X.basicOpen_le t
  have hy' := mpr_ (mem_basicOpen_iff_notMem_primeIdealOf hU t ⟨y, hyU⟩) ht
  have hbasic_le : ∀ j ∈ notInPrime, X.basicOpen t ≤ X.basicOpen (c.coord j) := by
    intro j hj
    have hsplit : t = c.coord j * ∏ i ∈ notInPrime.erase j, c.coord i := by
      rw [htdef]
      exact sy_ $ mul_prod_erase notInPrime c.coord hj
    rw [hsplit, basicOpen_mul]
    exact inf_le_left
  refine ⟨X.basicOpen t, hUt, hy', n, c.restrict hle,
    fun i => (ga_ i).bind fun j0 => if j0 ∈ notInPrime then none else some j0, ?_, ?_, ?_⟩
  intro i hi
  obtain ⟨hA, hB⟩ := hdesc i hi
  constructor
  intro hnone
  by_cases hg : ga_ i = none
  exact restrictIdeal_eq_top_of_le _ hle $ hA hg
  obtain ⟨j0, hj0⟩ := Option.ne_none_iff_exists'.mp hg
  have hb := of_bind_ite_eq_none (· ∈ notInPrime) hj0 hnone
  refine restrictIdeal_eq_top_of_le_basicOpen hU _ (c.coord j0) ?_ $ hbasic_le j0 hb
  rw [c.ideal_eq_span_coord hU _ _ $ hB j0 hj0, coe_singleton,
    image_singleton]
  intro j hj
  have hj' := hj
  obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some (· ∈ notInPrime) hj'
  exact restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ $ hB j hg
  intro i i' hi hi' j hj hj'
  exact hinj i i' hi hi' j (eq_some_and_not_of_bind_ite_eq_some (· ∈ notInPrime) hj).1
    (eq_some_and_not_of_bind_ite_eq_some (· ∈ notInPrime) hj').1
  intro i hi j hj
  obtain ⟨_, hB⟩ := hdesc i hi
  obtain ⟨hg, hb⟩ := eq_some_and_not_of_bind_ite_eq_some (· ∈ notInPrime) hj
  have hmemP : c.coord j ∈ _c0.asIdeal := by
    by_contra hcon
    exact hb $ mpr_ (hBad j) hcon
  have hidU : (F[i]'hi).ideal ⟨U, hU⟩ = span {c.coord j} := by
    rw [c.ideal_eq_span_coord hU _ _ $ hB j hg, coe_singleton, image_singleton]
  have hynb := fun hc =>
    mp (mem_basicOpen_iff_notMem_primeIdealOf hU (c.coord j) ⟨y, hyU⟩) hc hmemP
  refine mem_primeIdealOf_of_mem_support_of_ideal_eq_span_singleton _ hUt hy' _ ?_ $ mem_support_of_ideal_eq_span_singleton _ hU hyU (c.coord j) hidU hynb
  rw [(c.restrict hle).ideal_eq_span_coord hUt _ _
    (restrictIdeal_eq_restrict_coordIdeal_of_le hle c _ _ $ hB j hg), coe_singleton,
    image_singleton]

end





section
variable {X : Sch}
theorem ideal_top U :
    (⊤ : ISD X).ideal U = ⊤ := by simp

theorem presheaf_map_mem_primeIdealOf {V V'}
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V) x
    (hxV : x ∈ V) (hxV' : x ∈ V') s
    (hs : s ∈ asIdeal (hV.primeIdealOf ⟨x, hxV⟩)) :
    (X.presheaf.map (homOfLE hle).op).hom s ∈ asIdeal (hV'.primeIdealOf ⟨x, hxV'⟩) := by
  have hgerm := congrArg
    (hom · s) $ X.presheaf.germ_res (homOfLE hle) x hxV'
  simp only [hom_comp, comp_apply] at hgerm
  have h1 :=
    mpr (germ_mem_maximalIdeal_iff hV x hxV s) hs
  refine mp_ (germ_mem_maximalIdeal_iff hV' x hxV' _) ?_
  rwa [hgerm]

theorem etaleChartCoord_eq_coord {k : Type} [Field k]
    {p} {V} {m} (c : EtaleChart p V m) j :
    @etaleChartCoord k _ m (X.sec V) _ c.algebra j = c.coord j := by
  rw [etaleChartCoord_def, c.algebraMap_eq_coordRingHom, c.coordRingHom_X]
end

section
variable {Y : Sch}
theorem top_le_io_preimage_self (V : Opn Y) :
    (⊤ : V.toScheme.Opens) ≤ (Opens.map V.ib).obj V :=by simp_all
private theorem io_appLE_top_eq_topIso_inv (V : Opn Y) :
    V.ι.appLE V ⊤ (top_le_io_preimage_self V) = V.topIso.inv := by
  simp
  rfl

private theorem ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top (D : ISD Y)
    {V : Opn Y} (hV : IsAffineOpen V) (htop : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have key := comap_ideal_eq_map_appLE D V.i ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ $ top_le_io_preimage_self V
  rw [← restrictIdeal_eq_comap_io, htop] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  have hbij : Injective (hom $ V.ι.appLE V ⊤ (top_le_io_preimage_self V)) ∧
      Surjective (hom $ V.ι.appLE V ⊤ (top_le_io_preimage_self V)) := by
    rw [io_appLE_top_eq_topIso_inv]
    exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective
  have hcomap : comap (hom $ V.ι.appLE V ⊤ (top_le_io_preimage_self V))
      (map (hom $ V.ι.appLE V ⊤ (top_le_io_preimage_self V))
        (D.ideal ⟨V, hV⟩)) = D.ideal ⟨V, hV⟩ := by
    apply comap_map_of_bijective
    exact hbij
  rw [sy_ key, Ideal.comap_top] at hcomap
  exact sy_ hcomap
end

theorem exists_finset_comap_prod_ideal_eq_span_prod_coord {Y W : Sch} {k : Type}
    [Field k] {pY : Y ⟶ Sp k} (g : Y ⟶ W) (U : W.affineOpens) {V : Opn Y}
    (hV : IsAffineOpen V) (e : V ≤ pre g (U : Opn W)) {n : ℕ} (c : EtaleChart pY V n) :
    ∀ (F : Bdy W) (ga_ : ℕ → Option (Fin n)),
      (∀ i, ∀ h : i < length F, ga_ i = none → restrictIdeal ((F[i]'h).comap g) V = ⊤) →
      (∀ i, ∀ h : i < length F, ∀ j, ga_ i = some j →
        restrictIdeal ((F[i]'h).comap g) V = c.coordIdeal {j}) →
      (∀ i i', i < length F → i' < length F → ∀ j, ga_ i = some j → ga_ i' = some j → i = i') →
      ∃ J : FinSet n,
        (∀ j ∈ J, ∃ i, ∃ _ : i < length F, ga_ i = some j) ∧
        (F.prod.comap g).ideal ⟨V, hV⟩ = span {∏ j ∈ J, c.coord j} := by
  intro F
  induction F with
  | nil =>
      intro ga_ _ _ _
      refine ⟨∅, by simp, ?_⟩
      have h1 : (([] : Bdy W).prod).comap g = (⊤ : ISD Y) := by
        rw [Blowup.idealSheafData_prod_nil]
        simp
      rw [h1, prod_empty, span_singleton_one]
      exact ideal_top _
  | cons D F ih =>
      intro ga_ hnone hsome hinj
      have hlen : ∀ i, i < length F → i + 1 < length (D :: F) := by
        intro i hi
        simp only [length_cons]
        omega
      have hD0 : (0 : ℕ) < length (D :: F) := by
        simp only [length_cons]
        omega
      obtain ⟨J', hJ'mem, hJ'⟩ := ih (fun i => ga_ $ i + 1)
        (fun i h hg => hnone (i + 1) (hlen i h) hg)
        (fun i h j hg => hsome (i + 1) (hlen i h) j hg)
        (fun i i' hi hi' j h1 h2 => by
          have h3 := hinj (i + 1) (i' + 1) (hlen i hi) (hlen i' hi') j h1 h2
          omega)
      have hprod : ((D :: F).prod.comap g).ideal ⟨V, hV⟩
          = (cmI D g).ideal ⟨V, hV⟩ * (cmI (F.prod) g).ideal ⟨V, hV⟩ := by
        rw [Blowup.idealSheafData_prod_cons]
        rw [comap_ideal_eq_map_appLE (D * F.prod) g U ⟨V, hV⟩ e,
        comap_ideal_eq_map_appLE D g U ⟨V, hV⟩ e,
        comap_ideal_eq_map_appLE F.prod g U ⟨V, hV⟩ e,
        ideal_mul, Pi.mul_apply, m220]
      cases hga0 : ga_ 0 with
      | none =>
          have hD : (cmI D g).ideal ⟨V, hV⟩ = ⊤ :=
            ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top _ hV $ hnone 0 hD0 hga0
          refine ⟨J', ?_, ?_⟩
          intro j hj
          obtain ⟨i, hi, hgai⟩ := hJ'mem j hj
          exact ⟨i + 1, hlen i hi, hgai⟩
          rw [hprod, hD, hJ', top_mul]
      | some j0 =>
          have hD : (cmI D g).ideal ⟨V, hV⟩ = span {c.coord j0} := by
            have h2 := ideal_eq_span_coord c hV (cmI D g) {j0}
              (hsome 0 hD0 j0 hga0)
            rwa [coe_singleton, image_singleton] at h2
          have hj0 : j0 ∉ J' := by
            intro hj0mem
            obtain ⟨i, hi, hgai⟩ := hJ'mem j0 hj0mem
            have h3 := hinj 0 (i + 1) hD0 (hlen i hi) j0 hga0 hgai
            omega
          refine ⟨insert j0 J', ?_, ?_⟩
          intro j hj
          rcases mem_insert.mp hj with rfl | hj'
          exact ⟨0, hD0, hga0⟩
          obtain ⟨i, hi, hgai⟩ := hJ'mem j hj'
          exact ⟨i + 1, hlen i hi, hgai⟩
          rw [hprod, hD, hJ', span_singleton_mul_span_singleton,
            prod_insert hj0]

theorem strictNormalCrossingsRestrictToClopen : StrictNormalCrossingsRestrictToClopen := by
  intro k _ W p _ E Z hE hZ T hTclosed hcomp y
  have hsmZ :=
    smooth_subschemeio_comp_of_hasStrictNormalCrossingsWith Z E hZ
  let _a10 := subschemeι Z ≫ p
  let _a2 := ι T ≫ _a10
  have hsmT : Smooth _a2 := inferInstance
  let _a9 := ι T ≫ subschemeι Z
  obtain ⟨V, hV, hyV, n, c, ga_, hga_, hinjga, hmem⟩ : ∃ (U : T.toScheme.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (n : ℕ) (c : EtaleChart (ι T ≫ _a10) U n) (ga_ : ℕ → Option (Fin n)), (∀ i, ∀ hi : i < length E, (ga_ i = none → restrictIdeal ((E[i]'hi).comap _a9) U = ⊤) ∧ ∀ j, ga_ i = some j → restrictIdeal ((E[i]'hi).comap _a9) U = c.coordIdeal {j}) ∧ (∀ i i', i < length E → i' < length E → ∀ j, ga_ i = some j → ga_ i' = some j → i = i') ∧ (∀ i, i < length E → ∀ j, ga_ i = some j → c.coord j ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) := by
    let _c0 := _a9
    classical
    obtain ⟨U, hU, hy, n, c, ga_, hdesc, hinj⟩ : ∃ (U : T.toScheme.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (n : ℕ) (c : EtaleChart (ι T ≫ _a10) U n) (ga_ : ℕ → Option (Fin n)), (∀ i, ∀ hi : i < length E, (ga_ i = none → restrictIdeal ((E[i]'hi).comap _a9) U = ⊤) ∧ ∀ j, ga_ i = some j → restrictIdeal ((E[i]'hi).comap _a9) U = c.coordIdeal {j}) ∧ (∀ i i', i < length E → i' < length E → ∀ j, ga_ i = some j → ga_ i' = some j → i = i') := by
      classical
      let _a0 := _a9
      have hbase : ∀ z : toScheme T,
          _a0.base z = Z.subschemeι.base (T.ib z) := fun _ => rfl
      have hcont : Continuous fun z : toScheme T => bsM _a0 z :=
        _a0.base.hom.continuous
      have hw : Z.subschemeι.base (T.ib y) ∈ support Z := subschemeio_base_mem_support_of_subscheme Z _
      obtain ⟨U, hwU, m, c, a, S, hainj, hanone, hasome, hZU⟩ := hZ.exists_etaleChart hw
      obtain ⟨U0_, hU0aff, hwU0, hU0le⟩ := exists_isAffineOpen_mem_and_subset hwU
      have hZU0 :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hU0le c Z S hZU
      have hE0none : ∀ (i : ℕ) (hi : i < length E), a i = none →
          restrictIdeal (E[i]'hi) U0_ = ⊤ := fun i hi h =>
        restrictIdeal_eq_top_of_le _ hU0le $ hanone i hi h
      have hE0some : ∀ (i : ℕ) (hi : i < length E) (t : Fin m), a i = some t →
          restrictIdeal (E[i]'hi) U0_ = (c.restrict hU0le).coordIdeal {t} := fun i hi t h =>
        restrictIdeal_eq_restrict_coordIdeal_of_le hU0le c _ _ $ hasome i hi t h
      have hnotS : ∀ (i : ℕ) (hi : i < length E) (t : Fin m), a i = some t → t ∉ S := by
        intro i hi t hat htS
        have hEle : (E[i]'hi).ideal ⟨U0_, hU0aff⟩ ≤ Z.ideal ⟨U0_, hU0aff⟩ := by
          rw [(c.restrict hU0le).ideal_eq_span_coord hU0aff _ _ $ hE0some i hi t hat,
            (c.restrict hU0le).ideal_eq_span_coord hU0aff _ _ hZU0,
            coe_singleton, image_singleton, span_singleton_le_iff_mem]
          exact subset_span ⟨t, mpr_ mem_coe htS, rfl⟩
        refine hcomp (E[i]'hi) (List.getElem_mem hi) (irreducibleComponent y)
          (irreducibleComponent_mem_irreducibleComponents y) ?_
        refine image_subset_of_image_inter_subset isIrreducible_irreducibleComponent
          (U0_.2.preimage hcont) ⟨y, mem_irreducibleComponent, ?_⟩ hcont
          (E[i]'hi).support.2 ?_
        show bsM _a0 y ∈ (U0_ : Set W)
        rwa [hbase y]
        rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
        have hzU0 := hz
        have hzZ : bsM _a0 z ∈ support Z := by
          rw [hbase z]
          exact subschemeio_base_mem_support_of_subscheme Z _
        exact mpr_ (mem_support_iff_forall_notMem_basicOpen _ hU0aff hzU0)
          (fun f hf => mp_ (mem_support_iff_forall_notMem_basicOpen Z hU0aff hzU0) hzZ f $ hEle hf)
      have hyV : y ∈ T.i.pre (preU Z.si U0_) := hwU0
      obtain ⟨U1_, hU1aff, hyU1, hU1le⟩ := exists_isAffineOpen_mem_and_subset hyV
      set d := (c.restrict hU0le).restrictToSubscheme hU0aff Z S hZU0 with hd
      set d' := d.pullbackOpenImmersion T.i with hd'
      refine ⟨U1_, hU1aff, hyU1, m - S.card, d'.restrict hU1le,
        fun i => (a i).bind $ complOrderEmbInv m S, ?_, ?_⟩
      intro i hi
      constructor
      intro hnone
      have ha :=
        eq_none_of_bind_complInv_eq_none m S (a i) (fun t ht => hnotS i hi t ht) hnone
      have h1 := hE0none i hi ha
      have h2 : restrictIdeal ((E[i]'hi).comap Z.si) (Z.si.pre U0_) = ⊤ :=
        restrictIdeal_comap_subschemeio_eq_top Z U0_ _ h1
      have h3 : restrictIdeal (((E[i]'hi).comap Z.si).comap T.i)
          (T.i.pre $ preU Z.si U0_) = ⊤ :=
        restrictIdeal_comap_preimage_eq_top T.i _ _ h2
      have h4 := restrictIdeal_eq_top_of_le _ hU1le h3
      rwa [comap_comp]
      intro j hj
      have hj' := hj
      have h1 := hE0some i hi _ $ eq_some_complOrderEmb_of_bind_complInv_eq_some m S (a i) j hj'
      have h2 : restrictIdeal ((E[i]'hi).comap Z.si) (Z.si.pre U0_)
          = d.coordIdeal {j} :=
        (c.restrict hU0le).restrictToSubscheme_coordIdeal_singleton hU0aff Z S hZU0 j _ h1
      have h3 : restrictIdeal (((E[i]'hi).comap Z.si).comap T.i)
          (T.i.pre $ preU Z.si U0_) = d'.coordIdeal {j} :=
        restrictIdeal_comap_eq_coordIdeal_pullbackOpenImmersion d T.i _ _ h2
      have h4 := restrictIdeal_eq_restrict_coordIdeal_of_le hU1le d' _ _ h3
      rwa [comap_comp]
      intro i i' hi hi' j hj hj'
      exact hainj i hi i' hi' (complOrderEmb m S j) (eq_some_complOrderEmb_of_bind_complInv_eq_some m S (a i) j hj)
        (eq_some_complOrderEmb_of_bind_complInv_eq_some m S (a i') j hj')
    have hlen : length (E.map fun D : ISD W => D.comap _c0)
        = length E := by
      simp
    have hdesc' : ∀ i, ∀ hi : i < (E.map fun D : ISD W =>
          D.comap _c0).length,
        (ga_ i = none → restrictIdeal ((E.map fun D : ISD W =>
            D.comap _c0)[i]'hi) U = ⊤) ∧
          ∀ j, ga_ i = some j → restrictIdeal ((E.map fun D : ISD W =>
            D.comap _c0)[i]'hi) U = c.coordIdeal {j} := by
      intro i hi
      have hi' : i < length E := by rwa [hlen] at hi
      obtain ⟨hA, hB⟩ := hdesc i hi'
      simp [getElem_map]
      exact ⟨hA, hB⟩
    have hinj' : ∀ i i', i < (E.map fun D : ISD W =>
        D.comap _c0).length →
        i' < length (E.map fun D : ISD W => D.comap _c0) →
        ∀ j, ga_ i = some j → ga_ i' = some j → i = i' := by
      intro i i' hi hi' j h1 h2
      rw [hlen] at hi hi'
      exact hinj i i' hi hi' j h1 h2
    obtain ⟨U', hU', hy', n', c', ga', h1, h2, h3⟩ :=
      exists_etaleChart_coord_mem_primeIdealOf
        (E.map fun D : ISD W => D.comap _c0) y U hU hy c ga_
        hdesc' hinj'
    refine ⟨U', hU', hy', n', c', ga', ?_, ?_, ?_⟩
    intro i hi
    have hi' : i < (E.map fun D : ISD W =>
        D.comap _c0).length := by omega
    obtain ⟨hA, hB⟩ := h1 i hi'
    simp [getElem_map] at hA hB
    exact ⟨hA, hB⟩
    intro i i' hi hi' j hj hj'
    exact h2 i i' (by rw [hlen]; exact hi) (by rw [hlen]; exact hi') j hj hj'
    intro i hi j hj
    exact h3 i (by rw [hlen]; exact hi) j hj
  let _s0 := _a9
  obtain ⟨U, hyU, hU⟩ : ∃ U : Opn W, bsM _s0 y ∈ U ∧ IsAffineOpen U := by
    obtain ⟨U, hUmem, hxU, -⟩ :=
      mp isBasis_iff_nbhd (isBasis_affineOpens W)
        (show bsM _s0 y ∈ (⊤ : Opn W) from trivial)
    exact ⟨U, hxU, hUmem⟩
  have hyVU : y ∈ (V ⊓ _s0.pre U : (toScheme T).Opens) := ⟨hyV, hyU⟩
  obtain ⟨fs, hfle, hyf⟩ := hV.exists_basicOpen_le ⟨y, hyVU⟩ hyV
  obtain ⟨V', hV', hV'V, hV'U, hyV'⟩ :
      ∃ V' : (toScheme T).Opens, IsAffineOpen V' ∧ V' ≤ V ∧
        V' ≤ _s0.pre U ∧ y ∈ V' :=
    ⟨T.toScheme.basicOpen fs, hV.basicOpen fs, le_trans hfle inf_le_left,
      le_trans hfle inf_le_right, hyf⟩
  have hga' : ∀ i, ∀ h : i < length E,
      (ga_ i = none → restrictIdeal ((E[i]'h).comap _s0) V' = ⊤) ∧
      (∀ j, ga_ i = some j →
        restrictIdeal ((E[i]'h).comap _s0) V'
          = (c.restrict hV'V).coordIdeal {j}) := by
    intro i h
    let _a6 := hga_ i h
    exact ⟨fun hg => restrictIdeal_eq_top_of_le _ hV'V $ _a6.1 hg, fun j hg => restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c _ {j} $ _a6.2 j hg⟩
  obtain ⟨J0_, hJ0mem, hJ0_⟩ :=
    exists_finset_comap_prod_ideal_eq_span_prod_coord _s0 ⟨U, hU⟩ hV' hV'U
      (c.restrict hV'V) E ga_ (fun i h => (hga' i h).1) (fun i h => (hga' i h).2) hinjga
  let _a3 := hV'.primeIdealOf ⟨y, hyV'⟩
  have hJ0prime : ∀ j ∈ J0_,
      (c.restrict hV'V).coord j ∈ _a3.asIdeal := by
    intro j hj
    obtain ⟨i, hi, hgai⟩ := hJ0mem j hj
    rw [FunctorialResolution.EmbeddedResolution.EtaleChart.coord_restrict c hV'V j]
    exact presheaf_map_mem_primeIdealOf hV hV' hV'V y hyV hyV' (c.coord j) $ hmem i hi j hgai
  have hntr : Nontrivial $ T.toScheme.presheaf.obj $ op V' := by
    rcases subsingleton_or_nontrivial (T.toScheme.presheaf.obj (op V')) with hs | hs
    exfalso
    refine _a3.isPrime.ne_top ?_
    rw [eq_top_iff_one, @elim _ hs 1 0]
    exact m97 _
    exact hs
  have hcinj : Injective (c.restrict hV'V).coord := by
    have h := @etaleChartCoord_injective k _ n (T.toScheme.presheaf.obj $ op V') _
      (c.restrict hV'V).algebra ((c.restrict hV'V).algebra_etale hV') hntr
    intro a b hab
    refine h ?_
    simp [etaleChartCoord_eq_coord]
    exact hab
  have hrad := @isRadical_span_singleton_prod_etaleChartCoord k _ n
    (T.toScheme.presheaf.obj $ op V') _ (c.restrict hV'V).algebra
    ((c.restrict hV'V).algebra_etale hV') J0_
  simp [etaleChartCoord_eq_coord] at hrad
  obtain ⟨N, f, hfcoord, hfreg⟩ :=
    exists_isRegularParameterSystem_with_coords_of_mem_prime hV' (c.restrict hV'V) y hyV'
      J0_ hJ0prime
  choose ι hio using hfcoord
  have hinj2 : ∀ a ∈ J0_.attach, ∀ b ∈ J0_.attach,
      (fun j : { x // x ∈ J0_ } => ι j.1 j.2) a = (fun j : { x // x ∈ J0_ } => ι j.1 j.2) b →
        a = b := by
    intro a _ b _ hab
    have h1 : (c.restrict hV'V).coord a.1 = (c.restrict hV'V).coord b.1 := by
      rw [← hio a.1 a.2, ← hio b.1 b.2]
      exact congrArg f hab
    exact m26 $ hcinj h1
  have hprodJ : (∏ i ∈ J0_.attach.image fun j : { x // x ∈ J0_ } => ι j.1 j.2, f i)
      = ∏ j ∈ J0_, (c.restrict hV'V).coord j := by
    rw [prod_image hinj2, ← prod_attach J0_ fun j => (c.restrict hV'V).coord j]
    exact prod_congr rfl fun j _ => hio j.1 j.2
  refine ⟨isRegularLocalRing_stalk_of_smooth _a2 y,
    ⟨V', hV'⟩, hyV', N, f, J0_.attach.image fun j : { x // x ∈ J0_ } => ι j.1 j.2, hfreg, ?_⟩
  rw [radical_ideal, hJ0_, hrad.radical, hprodJ]





section
variable {X : Sch} {k : Type} [Field k] (p : X ⟶ Sp k) [Smooth p]
theorem inStrictNormalCrossingPositionAt_nil x :
    InStrictNormalCrossingPositionAt p ([] : Bdy X) x := by
  obtain ⟨U, m, hxU, _, hc⟩ := exists_etaleChart p x
  obtain ⟨c⟩ := hc
  refine ⟨U, hxU, m, c, fun _ => none, ?_, ?_, ?_⟩
  simp_all
  simp_all
  simp_all

theorem inStrictNormalCrossingPosition_nil :
    InStrictNormalCrossingPosition p ([] : Bdy X) := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, fun x => inStrictNormalCrossingPositionAt_nil p x⟩
  intro D hD
  simp at hD
end


variable {X : Sch} {k : Type} [Field k]

noncomputable def filterNeTop (E : Bdy X) : Bdy X :=
  E.filter fun D => @decide (D ≠ ⊤) $ Classical.propDecidable _

theorem filterNeTop_nil : filterNeTop ([] : Bdy X) = [] := rfl

private theorem filterNeTop_cons_of_ne_top (D : ISD X) (T : Bdy X)
    (h : D ≠ ⊤) : filterNeTop (D :: T) = D :: filterNeTop T := by
  simp [filterNeTop, h]

private theorem filterNeTop_cons_top T :
    filterNeTop ((⊤ : ISD X) :: T) = filterNeTop T := by
  simp [filterNeTop]

section
variable {D : ISD X} {E : Bdy X}
theorem mem_of_mem_filterNeTop
    (h : D ∈ filterNeTop E) : D ∈ E := by
  simp [filterNeTop, mem_filter] at h
  exact an1 h

theorem mem_filterNeTop
    (hD : D ∈ E) (h : D ≠ ⊤) : D ∈ filterNeTop E := by
  simp [filterNeTop, mem_filter]
  exact ⟨hD, by simpa using h⟩
end

def unshiftIndex (g0_ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => g0_ i

def shiftIndex (g0_ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => g0_ i + 1

theorem exists_index_map_of_filterNeTop_eq n :
    ∀ (E E' : Bdy X),
    length E + length E' ≤ n → filterNeTop E' = filterNeTop E →
    ∃ g : ℕ → ℕ,
      (∀ i, i < length E' → E'[i]? ≠ some ⊤ → g i < length E ∧ E[g i]? = E'[i]?) ∧
      (∀ i j, i < length E' → j < length E' → E'[i]? ≠ some ⊤ → E'[j]? ≠ some ⊤ →
        g i = g j → i = j) := by
  induction n with
  | zero =>
    intro E E' hlen _
    have h0 : length E' = 0 := by omega
    exact ⟨id, fun i hi _ => absurd hi $ by omega, fun i j hi _ _ _ _ => absurd hi $ by omega⟩
  | succ n ih =>
    intro E E' hlen hfilt
    cases E' with
    | nil =>
      exact ⟨id, fun i hi _ => absurd hi $ by simp, fun i j hi _ _ _ _ => absurd hi $ by simp⟩
    | cons D T' =>
      by_cases hD : D = ⊤
      subst hD
      rw [filterNeTop_cons_top] at hfilt
      have hlen' : length E + length T' ≤ n := by
        simp only [length_cons] at hlen
        omega
      obtain ⟨g0_, h1, h2⟩ := ih E T' hlen' hfilt
      refine ⟨unshiftIndex g0_, ?_, ?_⟩
      intro i hi hne
      cases i with
      | zero => simp at hne
      | succ i =>
        simp only [List.getElem?_cons_succ] at hne
        simp only [length_cons] at hi
        simp only [unshiftIndex, List.getElem?_cons_succ]
        exact h1 i (by omega) hne
      intro i j hi hj hni hnj hgij
      cases i with
      | zero => simp at hni
      | succ i =>
        cases j with
        | zero => simp at hnj
        | succ j =>
          have e1 : unshiftIndex g0_ (i + 1) = g0_ i := rfl
          have e2 : unshiftIndex g0_ (j + 1) = g0_ j := rfl
          have hij : g0_ i = g0_ j := by omega
          simp only [List.getElem?_cons_succ] at hni hnj
          simp only [length_cons] at hi hj
          have := h2 i j (by omega) (by omega) hni hnj hij
          omega
      rw [filterNeTop_cons_of_ne_top D T' hD] at hfilt
      cases E with
      | nil =>
        rw [filterNeTop_nil] at hfilt
        exact absurd hfilt $ List.cons_ne_nil _ _
      | cons C T =>
        by_cases hC : C = ⊤
        subst hC
        rw [filterNeTop_cons_top] at hfilt
        have hlen' : length T + length (D :: T') ≤ n := by
          simp only [length_cons] at hlen ⊢
          omega
        have hfilt' := hfilt
        rw [← filterNeTop_cons_of_ne_top D T' hD] at hfilt'
        obtain ⟨g0_, h1, h2⟩ := ih T (D :: T') hlen' hfilt'
        refine ⟨fun i => g0_ i + 1, ?_, ?_⟩
        intro i hi hne
        obtain ⟨ha, hb⟩ := h1 i hi hne
        refine ⟨by simp only [length_cons]; omega, ?_⟩
        simpa using hb
        intro i j hi hj hni hnj hgij
        have hgij' : g0_ i + 1 = g0_ j + 1 := hgij
        exact h2 i j hi hj hni hnj $ by omega
        rw [filterNeTop_cons_of_ne_top C T hC] at hfilt
        simp only [List.cons.injEq] at hfilt
        obtain ⟨hcond, hTT⟩ := hfilt
        have hlen' : length T + length T' ≤ n := by
          simp only [length_cons] at hlen
          omega
        obtain ⟨g0_, h1, h2⟩ := ih T T' hlen' hTT
        refine ⟨shiftIndex g0_, ?_, ?_⟩
        intro i hi hne
        cases i with
        | zero =>
          simp only [shiftIndex]
          refine ⟨by simp, ?_⟩
          simp [hcond]
        | succ i =>
          simp only [List.getElem?_cons_succ] at hne
          simp only [length_cons] at hi
          obtain ⟨ha, hb⟩ := h1 i (by omega) hne
          simp only [shiftIndex, List.getElem?_cons_succ]
          exact ⟨by simp only [length_cons]; omega, hb⟩
        intro i j hi hj hni hnj hgij
        cases i with
        | zero =>
          cases j with
          | zero => rfl
          | succ j =>
            have e1 : shiftIndex g0_ 0 = 0 := rfl
            have e2 : shiftIndex g0_ (j + 1) = g0_ j + 1 := rfl
            omega
        | succ i =>
          cases j with
          | zero =>
            have e1 : shiftIndex g0_ 0 = 0 := rfl
            have e2 : shiftIndex g0_ (i + 1) = g0_ i + 1 := rfl
            omega
          | succ j =>
            have e1 : shiftIndex g0_ (i + 1) = g0_ i + 1 := rfl
            have e2 : shiftIndex g0_ (j + 1) = g0_ j + 1 := rfl
            have hij : g0_ i = g0_ j := by omega
            simp only [List.getElem?_cons_succ] at hni hnj
            simp only [length_cons] at hi hj
            have := h2 i j (by omega) (by omega) hni hnj hij
            omega

open Classical in
def transportAssignment {m : ℕ} (E' : Bdy X) (a : ℕ → Option (Fin m))
    (g : ℕ → ℕ) : ℕ → Option (Fin m) :=
  fun i => if E'[i]? = some ⊤ then none else a $ g i

section
variable {m} (E' : Bdy X) (a : ℕ → Option (Fin m)) (g : ℕ → ℕ) (i : ℕ)
theorem transportAssignment_of_eq_top (h : E'[i]? = some ⊤) :
    transportAssignment E' a g i = none := by
  simp [transportAssignment, h]

theorem transportAssignment_of_ne_top (h : E'[i]? ≠ some ⊤) :
    transportAssignment E' a g i = a (g i) := by
  simp [transportAssignment, h]
end

theorem transportAssignment_injective_and_coordIdeal {p : X ⟶ Sp k} {U : Opn X} {m : ℕ}
    (c : EtaleChart p U m) (E E' : Bdy X) (a : ℕ → Option (Fin m)) (g : ℕ → ℕ)
    (hg1 : ∀ i, i < length E' → E'[i]? ≠ some ⊤ → g i < length E ∧ E[g i]? = E'[i]?)
    (hg2 : ∀ i j, i < length E' → j < length E' → E'[i]? ≠ some ⊤ → E'[j]? ≠ some ⊤ →
      g i = g j → i = j)
    (hinj : ∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ i hi, a i = none → restrictIdeal E[i] U = ⊤)
    (hsome : ∀ i hi t, a i = some t →
      restrictIdeal E[i] U = c.coordIdeal {t}) :
    (∀ i < length E', ∀ j < length E', ∀ t,
        transportAssignment E' a g i = some t → transportAssignment E' a g j = some t → i = j) ∧
      (∀ i hi, transportAssignment E' a g i = none →
        restrictIdeal E'[i] U = ⊤) ∧
      (∀ i hi t, transportAssignment E' a g i = some t →
        restrictIdeal E'[i] U = c.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  intro i hi j hj t hti htj
  have hni : E'[i]? ≠ some ⊤ := by
    intro hc
    rw [transportAssignment_of_eq_top E' a g i hc] at hti
    simp at hti
  have hnj : E'[j]? ≠ some ⊤ := by
    intro hc
    rw [transportAssignment_of_eq_top E' a g j hc] at htj
    simp at htj
  rw [transportAssignment_of_ne_top E' a g i hni] at hti
  rw [transportAssignment_of_ne_top E' a g j hnj] at htj
  obtain ⟨hgi, -⟩ := hg1 i hi hni
  obtain ⟨hgj, -⟩ := hg1 j hj hnj
  exact hg2 i j hi hj hni hnj $ hinj (g i) hgi (g j) hgj t hti htj
  intro i hi hn
  by_cases hc : E'[i]? = some ⊤
  have he := by
    rw [List.getElem?_eq_getElem hi] at hc
    exact Option.some_inj.mp hc
  rw [he]
  exact comap_top U.i
  rw [transportAssignment_of_ne_top E' a g i hc] at hn
  obtain ⟨hgi, hb⟩ := hg1 i hi hc
  have he : E[g i] = E'[i] := by simp_all
  rw [← he]
  exact hnone (g i) hgi hn
  intro i hi t hti
  have hc : E'[i]? ≠ some ⊤ := by
    intro hc
    rw [transportAssignment_of_eq_top E' a g i hc] at hti
    simp at hti
  rw [transportAssignment_of_ne_top E' a g i hc] at hti
  obtain ⟨hgi, hb⟩ := hg1 i hi hc
  have he : E[g i] = E'[i] := by simp_all
  rw [← he]
  exact hsome (g i) hgi t hti

section
variable (p : X ⟶ Sp k)
theorem isSmoothDivisor_top
    [Smooth p] :
    IsSmoothDivisor p (⊤ : ISD X) := by
  refine isSmoothDivisor_of_locally_coordIdeal (p := p) ⊤ ?_
  intro x
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  exact ⟨U, hxU, m, c, m51 $ comap_top U.i⟩

theorem inStrictNormalCrossingPositionAt_of_filterNeTop_eq
    (E E' : Bdy X) (h : filterNeTop E = filterNeTop E') (x : X)
    (hE : InStrictNormalCrossingPositionAt p E x) : InStrictNormalCrossingPositionAt p E' x := by
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := hE.exists_etaleChart
  obtain ⟨g, hg1, hg2⟩ :=
    exists_index_map_of_filterNeTop_eq (lenL E + lenL E') E E' le_rfl h.symm
  obtain ⟨k1, k2, k3⟩ := transportAssignment_injective_and_coordIdeal c E E' a g hg1 hg2 hinj hnone hsome
  exact inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, c, transportAssignment E' a g, k1, k2, k3⟩

theorem inStrictNormalCrossingPosition_of_filterNeTop_eq
    [Smooth p] E E'
    (h : filterNeTop E = filterNeTop E') (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition p E' := by
  rw [inStrictNormalCrossingPosition_iff] at hE ⊢
  obtain ⟨hsm, hpos⟩ := hE
  refine ⟨?_, fun x => inStrictNormalCrossingPositionAt_of_filterNeTop_eq p E E' h x $ hpos x⟩
  intro D hD
  by_cases hDt : D = ⊤
  rw [hDt]
  exact isSmoothDivisor_top p
  have h1 := mem_filterNeTop hD hDt
  rw [← h] at h1
  exact hsm D $ mem_of_mem_filterNeTop h1

theorem hasStrictNormalCrossingsWith_of_filterNeTop_eq
    (Z : ISD X) (E E' : Bdy X)
    (h : filterNeTop E = filterNeTop E') (hE : HasStrictNormalCrossingsWith p Z E) :
    HasStrictNormalCrossingsWith p Z E' := by
  obtain ⟨g, hg1, hg2⟩ :=
    exists_index_map_of_filterNeTop_eq (lenL E + lenL E') E E' le_rfl h.symm
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZ⟩ := hE.exists_etaleChart hx
  obtain ⟨k1, k2, k3⟩ := transportAssignment_injective_and_coordIdeal c E E' a g hg1 hg2 hinj hnone hsome
  exact ⟨U, hxU, m, c, transportAssignment E' a g, S, k1, k2, k3, hZ⟩
end

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

section
variable {X Y : Sch} (g : Y ⟶ X)
section
variable (Z : ISD X)
theorem exists_comp_subschemeio_eq_subschemeio_comp :
    ∃ q : subscheme (Z.comap g) ⟶ subscheme Z,
      q ≫ subschemeι Z = subschemeι (Z.comap g) ≫ g := by
  let _a0 := fst g Z.si
  have : IsClosedImmersion _a0 := inferInstance
  refine ⟨m64 _a0
      (cmI Z g).si (le_of_eq (q2 $ cmI Z g).symm) ≫ snd g Z.si, ?_⟩
  rw [assoc, ← condition, ← assoc,
    m154]

def subschemeMapOfComap :
    subscheme (Z.comap g) ⟶ subscheme Z :=
  (exists_comp_subschemeio_eq_subschemeio_comp g Z).choose

theorem subschemeMapOfComap_comp :
    subschemeMapOfComap g Z ≫ subschemeι Z = subschemeι (Z.comap g) ≫ g :=
  (exists_comp_subschemeio_eq_subschemeio_comp g Z).choose_spec
end

theorem flat_of_comp_subschemeio_eq_of_iso_pullback [Flat g]
    (Z : ISD X)
    (e : subscheme (Z.comap g) ≅ Limits.pullback g Z.si)
    (he : e.hom ≫ fst g Z.si = subschemeι (Z.comap g))
    q
    (hq : q ≫ subschemeι Z = subschemeι (Z.comap g) ≫ g) :
    Flat q := by
  have hq' : q = isoH e ≫ snd g Z.si := by
    rw [← cancel_mono Z.si, hq, assoc, ← condition,
      ← assoc, he]
  rw [hq']
  infer_instance
end

instance instFlatComapSubschemeMap {X Y : Sch} (g : Y ⟶ X)
    [Flat g] (Z : ISD X) :
    Flat $ subschemeMapOfComap g Z :=
  by
  refine flat_of_comp_subschemeio_eq_of_iso_pullback g Z (comapIso ..) ?_ _
    (subschemeMapOfComap_comp g Z)
  exact comapIso_hom_fst ..

section
variable {X Y : Sch} (g : Y ⟶ X)
theorem subschemeMapOfComap_base (Z : ISD X)
    y :
    Z.subschemeι.base ((subschemeMapOfComap g Z).base y) =
      g.base ((Z.comap g).subschemeι.base y) := by
  have h2 : bsM (subschemeMapOfComap g Z ≫ siI Z) y
      = bsM (siI (cmI Z g) ≫ g) y := by rw [subschemeMapOfComap_comp g Z]
  simpa using h2

theorem generalizing_subschemeMapOfComap
    [Flat g] (Z : ISD X)
    y x
    (hx : x ⤳ (subschemeMapOfComap g Z).base y) :
    ∃ y' : subscheme $ Z.comap g, y' ⤳ y ∧ (subschemeMapOfComap g Z).base y' = x := by
  exact generalizingMap (subschemeMapOfComap g Z) hx

theorem restrictIdeal_comap_preimage_eq_comap_restrict
    (I : ISD X) U :
    restrictIdeal (I.comap g) (pre g U) = (restrictIdeal I U).comap (g.mr U) := by
  rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
    ← comap_comp, morphismRestrict_ι]
end

section
variable {X : Sch}
private theorem span_eq_top_of_basicOpen_cover (W : X.affineOpens)
    (S : Set $ X.sec (W : Opn X))
    (hcov : ∀ x ∈ (W : Opn X), ∃ f ∈ S, x ∈ basicOpen X f) :
    span S = ⊤ := by
  rw [← W.2.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : X.sec W)) ?_
  rw [SetLike.le_def]
  intro x hx
  obtain ⟨f, hfS, hxf⟩ := hcov x hx
  exact mpr_ mem_iSup ⟨⟨f, hfS⟩, hxf⟩

section
variable (A B : ISD X) (W : X.affineOpens)
theorem ideal_le_of_basicOpen_cover
    (hcov : ∀ x ∈ (W : Opn X), ∃ f : (X.sec (W : Opn X)), x ∈ basicOpen X f ∧
      A.ideal (X.affineBasicOpen f) = B.ideal (X.affineBasicOpen f)) :
    A.ideal W ≤ B.ideal W := by
  intro s hs
  have hspan : span {f : (X.sec W) |
      A.ideal (X.affineBasicOpen f) = B.ideal (X.affineBasicOpen f)} = ⊤ := by
    refine span_eq_top_of_basicOpen_cover W _ fun x hx => ?_
    obtain ⟨f, hxf, hf⟩ := hcov x hx
    exact ⟨f, hf, hxf⟩
  refine mem_of_span_eq_top_of_smul_pow_mem _ _ hspan s ?_
  rintro ⟨f, hf⟩
  obtain ⟨n, hn⟩ : ∃ n, f ^ n * s ∈ B.ideal W := by
    have := W.2.isLocalization_basicOpen f
    have hA := A.map_ideal_basicOpen W f
    rw [hf, ← B.map_ideal_basicOpen W f] at hA
    let _m0 := X.sec W
    let _m1 := Γ(X, bOpn X f)
    let _a0 := algebraMap _m0 _m1
    have halg : _a0
        = hom (pMap X (homOfLE $ X.basicOpen_le f).op) := rfl
    have hmem : _a0 s
        ∈ map _a0 (B.ideal W) := by
      rw [halg, ← hA]
      exact mem_map_of_mem _ hs
    obtain ⟨⟨y, m⟩, hym⟩ :=
      mp (mem_map_algebraMap_iff (powers f) _m1) hmem
    rw [← map_mul] at hym
    obtain ⟨c, hc⟩ :=
      mp (eq_iff_exists (powers f) _m1) hym
    obtain ⟨n1, hn1⟩ := mp_ (mem_powers_iff (m : _m0) f) m.2
    obtain ⟨n2, hn2⟩ := mp_ (mem_powers_iff (c : _m0) f) c.2
    refine ⟨n2 + n1, ?_⟩
    have hrw : f ^ (n2 + n1) * s
        = (c : _m0) * (s * (m : _m0)) := by
      rw [← hn1, ← hn2]
      ring
    rw [hrw, hc]
    exact mul_mem_left _ _ y.2
  exact ⟨n, by rwa [smul_eq_mul]⟩
end

theorem idealSheafData_eq_of_forall_restrictIdeal_eq (I J : ISD X)
    (h : ∀ x : X, ∃ U : Opn X, x ∈ U ∧ restrictIdeal I U = restrictIdeal J U) : I = J := by
  have hloc : ∀ W : affO X, ∀ x ∈ (W : Opn X),
      ∃ f : X.sec (W : Opn X), x ∈ bOpn X f ∧
        I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f) := by
    intro W x hx
    obtain ⟨U, hxU, hU⟩ := h x
    have hU' : I.comap U.i = J.comap U.i := hU
    obtain ⟨f, hfU, hxf⟩ := W.2.exists_basicOpen_le (⟨x, hxU⟩ : U) hx
    refine ⟨f, hxf, ?_⟩
    have hbo : I.comap (bOpn X f).ι = J.comap (bOpn X f).ι := by
      rw [← Scheme.homOfLE_ι X hfU, comap_comp,
        comap_comp, hU']
    let V := bOpn X f
    let hV := W.2.basicOpen f
    have : IsAffine V.toScheme := hV
    have main : ∀ W : affO X, W = V → I.ideal W = J.ideal W →
        I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩ := by
      rintro ⟨W, hWaff⟩ rfl hW
      exact hW
    refine main ⟨opI V ''ᵁ (⊤),
      (isAffineOpen_top V.toScheme).image_of_isOpenImmersion V.i⟩
      (Scheme.Opens.ι_image_top V) ?_
    have h3 : (I.comap V.i).ideal ⟨⊤, isAffineOpen_top _⟩
        = (J.comap V.i).ideal ⟨⊤, isAffineOpen_top _⟩ := by rw [hbo]
    rw [ideal_comap_of_isOpenImmersion,
      ideal_comap_of_isOpenImmersion] at h3
    let _s0 := appIso V.i (⊤)
    have hid : (hom _s0.inv).comp
        (hom _s0.hom)
        = m99 _ := by
      rw [← m225, _s0.hom_inv_id,
        hom_id]
    exact comap_injective_of_surjective _ (fun y => ⟨m4 _s0.hom y, m156 hid y⟩) h3
  refine m29
    (funext fun W => le_antisymm (ideal_le_of_basicOpen_cover I J W $ hloc W) ?_)
  refine ideal_le_of_basicOpen_cover J I W fun x hx => ?_
  obtain ⟨f, hxf, hf⟩ := hloc W x hx
  exact ⟨f, hxf, sy_ hf⟩
end

theorem mem_connectedComponent_of_specializes {al_ : Type} [TopologicalSpace al_] {x y z : al_}
    (hy : y ∈ connectedComponent x) (h : y ⤳ z) : z ∈ connectedComponent x := by
  have hz := (((isPreconnected_singleton : _root_.IsPreconnected ({y} : Set al_)).closure).subset_connectedComponent $ subset_closure $ mem_singleton y) $ mp_ specializes_iff_mem_closure h
  rwa [← connectedComponent_eq hy] at hz

theorem openSubschemeKer_comap {X Y : Sch} (g : Y ⟶ X) [Flat g]
    (Z : ISD X) (A : Set X) (hA : IsClosed A)
    (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (hWc : IsClosed (W : Set Z.subscheme))
    (hW'c : IsClosed (W' : Set (Z.comap g).subscheme))
    (hirr : ∀ w : subscheme Z, IsIrreducible $ connectedComponent w) :
    openSubschemeKer (Z.comap g) W' = (openSubschemeKer Z W).comap g := by
  let _a0 := Set (cmI Z g).subscheme
  let _c0 := subschemeMapOfComap g Z
  apply idealSheafData_eq_of_forall_restrictIdeal_eq
  intro y
  by_cases hy : bsM g y ∈ Z.subschemeι.base '' W
  obtain ⟨U, hxU, hUW⟩ := exists_opens_preimage_subschemeio_le Z W (bsM g y) hy
  refine ⟨preU g U, hxU, ?_⟩
  have hsub : ((cmI Z g).si.pre $ preU g U) ≤ W' := by
    intro y' hy'
    have h0 := hy'
    have h1 : bsM _c0 y' ∈ (siPre Z U) := by
      show Z.subschemeι.base (bsM _c0 y') ∈ U
      rwa [subschemeMapOfComap_base g Z y']
    let y := y'
    let hy := hUW h1
    have hyW : connectedComponent (bsM _c0 y) ⊆ preimage Z.subschemeι.base A := by
      have h0 : bsM _c0 y ∈ (W : Set Z.subscheme) := hy
      rwa [hW] at h0
    have hmem : y ∈ (W' : _a0) := by
      rw [hW']
      intro z hz
      have h1 := (IsPreconnected.subset_connectedComponent (isPreconnected_connectedComponent.image _ (_c0.base.hom.continuous).continuousOn) ⟨y, mem_connectedComponent, rfl⟩) ⟨z, hz, rfl⟩
      have h2 : Z.subschemeι.base (bsM _c0 z) ∈ A := hyW h1
      rwa [subschemeMapOfComap_base g Z z] at h2
    exact hmem
  have e1 :=
    restrictIdeal_openSubschemeKer_of_preimage_le (cmI Z g) W' hW'c (preU g U) hsub
  rw [e1, restrictIdeal_comap_preimage_eq_comap_restrict g Z U,
    restrictIdeal_comap_preimage_eq_comap_restrict g (openSubschemeKer Z W) U, restrictIdeal_openSubschemeKer_of_preimage_le Z W hWc U hUW]
  obtain ⟨U, hxU, hUn⟩ := exists_opens_notMem_image Z W hWc (bsM g y) hy
  refine ⟨preU g U, hxU, ?_⟩
  have e1 : restrictIdeal (openSubschemeKer (cmI Z g) W') (preU g U) = ⊤ := by
    refine restrictIdeal_openSubschemeKer_eq_top (cmI Z g) W' hW'c (preU g U) ?_
    intro w' hw'
    have hw :=
      by
      let y := w'
      have hyset : connectedComponent y ⊆
          (cmI Z g).subschemeι.base ⁻¹' (pIm g.base A) := by
        have h0 : y ∈ (W' : _a0) := hw'
        rwa [hW'] at h0
      have hmem : bsM _c0 y ∈ (W : Set Z.subscheme) := by
        rw [hW]
        have hC :=
          hirr $ bsM _c0 y
        obtain ⟨et_, hetmem, hetspec⟩ :
            ∃ et_, et_ ∈ connectedComponent (bsM _c0 y) ∧
              ∀ z ∈ connectedComponent (bsM _c0 y), et_ ⤳ z :=
          ⟨hC.genericPoint, (hC.isGenericPoint_genericPoint isClosed_connectedComponent).mem,
            fun z hz => (hC.isGenericPoint_genericPoint isClosed_connectedComponent).specializes hz⟩
        obtain ⟨y', hy'spec, hy'eq⟩ := generalizing_subschemeMapOfComap g Z y et_ $ hetspec _ mem_connectedComponent
        have hy'cc : y' ∈ connectedComponent y := by
          rw [← connectedComponent_eq $ mem_connectedComponent_of_specializes mem_connectedComponent hy'spec]
          exact mem_connectedComponent
        have h4 : Z.subschemeι.base et_ ∈ A := by
          rw [← hy'eq, subschemeMapOfComap_base g Z y']
          exact hyset hy'cc
        intro x hx
        have hx3 := (hetspec x hx).map $ Z.subschemeι.base.hom.continuous
        exact hx3.mem_closed hA h4
      exact hmem
    have h2 := hUn _ hw
    rwa [subschemeMapOfComap_base g Z w'] at h2
  rw [e1, restrictIdeal_comap_preimage_eq_comap_restrict g (openSubschemeKer Z W) U, restrictIdeal_openSubschemeKer_eq_top Z W hWc U hUn]
  simp

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

variable {X : Sch} {k : Type} [Field k] (p : X ⟶ Sp k)

theorem le_one_of_not_two_le {a} (h : ¬ ((2 : ℕ) : ENat) ≤ a) : a ≤ 1 :=by simp_all
section
variable {V} (hV : IsAffineOpen V) {n} (c : EtaleChart p V n)
include hV
section
variable (S) (j) (hj : j ∈ S) (D : ISD X) (hD : restrictIdeal D V = c.coordIdeal S) (y) (hy : y ∈ V)
include hj hD hy
theorem orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal :
    orderAt D y ≤ 1 := by
  let _a1 := pGerm X V y hy
  classical
  by_cases hys : y ∈ spI D
  have hgerm : _a1.hom (c.coord j) ∈ stalkIdeal D y := by
    refine germ_mem_stalkIdeal D y ⟨V, hV⟩ hy ?_
    rw [ideal_eq_span_coord c hV D S hD]
    exact subset_span ⟨j, mpr_ mem_coe hj, rfl⟩
  have hmax :=
    mp (mem_support_iff_stalkIdeal_le_maximalIdeal D y) hys
  let _a2 := germ_mem_maximalIdeal_iff hV y hy $ c.coord j
  have hmem :=
    mp _a2 $ hmax hgerm
  refine le_one_of_not_two_le ?_
  intro h2
  rw [le_orderAt_iff] at h2
  have _i43 : _a1.hom (c.coord j) ∉ maximalIdeal (stkX X y) ^ 2 := by
    classical
    let instS := c.algebra
    have instEt :=
      algebra_etale c hV
    let instAlg :=
      _a1.hom.toAlgebra
    have hloc := hV.isLocalization_stalk ⟨y, hy⟩
    let _a0 := hV.primeIdealOf ⟨y, hy⟩
    have hreg :=
      isRegularLocalRing_of_isLocalization_etale k n V.sec
        _a0.asIdeal $ stkX X y
    have hcoord : ∀ i, etaleChartCoord k n V.sec i = c.coord i := fun i =>
      coordRingHom_X c i
    let _s0 := ({j} : FinSet n)
    have hJ : ∀ i ∈ _s0,
        etaleChartCoord k n V.sec i ∈ asIdeal _a0 := by
      intro i hi
      rwa [Finset.mem_singleton.mp hi, hcoord j]
    have hJA : ∀ i ∈ _s0,
        algebraMap V.sec (stkX X y) (etaleChartCoord k n V.sec i)
          ∈ maximalIdeal (stkX X y) := by
      intro i hi
      rw [Finset.mem_singleton.mp hi, hcoord j]
      exact mpr_ _a2 hmem
    have hli := linearIndependent_toCotangent_etaleChartCoord k n V.sec
      _a0.asIdeal (stkX X y) _s0 hJ hJA
    have hnot := notMem_maximalIdeal_sq
      (fun i : {x : Fin n // x ∈ _s0} =>
        algebraMap V.sec (stkX X y) $ etaleChartCoord k n V.sec i)
      (fun i => hJA i i.2) hli ⟨j, mem_singleton_self j⟩
    intro hcon
    have h2 := hcon
    rw [← hcoord j] at h2
    exact hnot h2
  exact _i43 $ h2 hgerm
  rw [mpr_ (orderAt_eq_zero_iff_not_mem_support D y) hys]
  exact zero_le_one

theorem orderAt_eq_one_of_restrictIdeal_eq_coordIdeal (hys : y ∈ support D) :
    orderAt D y = 1 :=
  le_antisymm (orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal p hV c S j hj D hD y hy)
    (mpr_ (one_le_orderAt_iff_mem_support D y) hys)

theorem orderAt_le_one_of_restrictIdeal_eq_coordIdeal :
    orderAt D y ≤ 1 :=
  orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal p hV c S j hj D hD y hy
end

theorem orderAt_eq_one_of_restrictIdeal_eq_coordIdeal_singleton j (D : ISD X)
    (hD : restrictIdeal D V = c.coordIdeal {j}) y (hy : y ∈ V) (hys : y ∈ support D) :
    orderAt D y = 1 :=
  le_antisymm (orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal p hV c {j} j (mem_singleton_self j) D hD y hy)
    (mpr_ (one_le_orderAt_iff_mem_support D y) hys)
end

end FunctorialResolution.EmbeddedResolution
end
section

namespace FunctorialResolution.EmbeddedResolution

section
variable (k : Type) [CommRing k] {X Y : Sch} (p : X ⟶ Sp k) (h : Y ⟶ X) (W) (V) (e : V ≤ pre h W)
theorem sectionsAlgebraMap_comp_appLE :
    (appLE h W V e).hom.comp (sectionsAlgebraMap k p W) = sectionsAlgebraMap k (h ≫ p) V := by
  rw [sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← hom_comp, assoc,
    appLE_comp_appLE]

theorem sectionsAlgebraMap_appLE_apply a :
    (appLE h W V e).hom (sectionsAlgebraMap k p W a) = sectionsAlgebraMap k (h ≫ p) V a :=
  congr_fun (sectionsAlgebraMap_comp_appLE k p h W V e) a
end

theorem exists_pow_mul_mem_of_mem_map {R S : Type} [CommRing R] [CommRing S]
    [Algebra R S] f [IsLocalization.Away f S] (N : Ideal R) x
    (hx : algebraMap R S x ∈ N.map (algebraMap R S)) : ∃ n, f ^ n * x ∈ N := by
  obtain ⟨⟨a, t⟩, hmul⟩ :=
    mp (mem_map_algebraMap_iff (M := powers f) (S := S)) hx
  have hmul' := hmul
  rw [← map_mul] at hmul'
  obtain ⟨c, hceq⟩ :=
    mp (eq_iff_exists (M := powers f) (S := S)) hmul'
  obtain ⟨i, hi⟩ := t.2
  obtain ⟨j, hj⟩ := c.2
  have hi' : f ^ i = t := hi
  have hj' : f ^ j = c := hj
  refine ⟨i + j, ?_⟩
  have key : f ^ (i + j) * x = f ^ j * (x * f ^ i) := by ring
  rw [key, hi', hj', hceq]
  exact N.mul_mem_left _ a.2

section
variable {Y : Sch} (J1 J2 : ISD Y)
theorem idealSheafData_ideal_le_congr
    {A B} (hAB : A = B) (h : J1.ideal B ≤ J2.ideal B) :
    J1.ideal A ≤ J2.ideal A := by
  subst hAB
  exact h

theorem idealSheafData_ideal_le_of_locally_le
    (H : ∀ y : Y, ∃ V hV, y ∈ V ∧
      J1.ideal ⟨V, hV⟩ ≤ J2.ideal ⟨V, hV⟩) (U : Y.affineOpens) :
    J1.ideal U ≤ J2.ideal U := by
  let _a0 := Γ(Y, U.1)
  intro x hx
  set s : Set Γ(Y, U.1) := {f : _a0 | ∃ n, f ^ n * x ∈ J2.ideal U} with hs
  have hcover : U.1 ≤ ⨆ f : s, bOpn Y (f : _a0) := by
    intro z hz
    obtain ⟨V, hV, hzV, hle⟩ := H z
    obtain ⟨f, g, hfg, hzf⟩ := exists_basicOpen_le_affine_inter U.2 hV z ⟨hz, hzV⟩
    let _s0 := pMap Y (homOfLE $ Y.basicOpen_le f).op
    have hres : map _s0.hom (J1.ideal U)
        ≤ map _s0.hom (J2.ideal U) := by
      rw [J1.map_ideal_basicOpen U f, J2.map_ideal_basicOpen U f]
      have hABO : Y.affineBasicOpen f = Y.affineBasicOpen (U := ⟨V, hV⟩) g := m26 hfg
      refine idealSheafData_ideal_le_congr J1 J2 hABO ?_
      rw [← J1.map_ideal_basicOpen ⟨V, hV⟩ g, ← J2.map_ideal_basicOpen ⟨V, hV⟩ g]
      exact map_mono hle
    have hfs : f ∈ s := by
      have := U.2.isLocalization_basicOpen f
      rw [hs]
      refine exists_pow_mul_mem_of_mem_map (S := Γ(Y, bOpn Y f)) f (J2.ideal U) x ?_
      have halg : (algebraMap Γ(Y, U.1) Γ(Y, bOpn Y f))
          = _s0.hom := rfl
      rw [halg]
      exact hres $ mem_map_of_mem _ hx
    exact Opens.mem_iSup.mpr ⟨⟨f, hfs⟩, hzf⟩
  refine mem_of_span_eq_top_of_smul_pow_mem (J2.ideal U) s (mp_ (U.2.self_le_iSup_basicOpen_iff) hcover) x ?_
  rintro ⟨f, hf⟩
  rw [hs] at hf
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

private theorem idealSheafData_eq_of_locally_eq
    (H : ∀ y : Y, ∃ V hV, y ∈ V ∧
      J1.ideal ⟨V, hV⟩ = J2.ideal ⟨V, hV⟩) : J1 = J2 := by
  refine m29 $ funext ?_
  intro U
  refine le_antisymm (idealSheafData_ideal_le_of_locally_le J1 J2 ?_ U)
    (idealSheafData_ideal_le_of_locally_le J2 J1 ?_ U)
  intro y
  obtain ⟨V, hV, h1, h2⟩ := H y
  exact ⟨V, hV, h1, h2.le⟩
  intro y
  obtain ⟨V, hV, h1, h2⟩ := H y
  exact ⟨V, hV, h1, h2.ge⟩
end

attribute [local instance] sumEvalAlgebra in
theorem exists_affineOpen_derivIdealSheaf_comap_ideal_eq (k : Type) [Field k] [IsNoetherianRing k]
    {X Y : Sch} (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType $ h ≫ p] (I : ISD X) (y : Y) :
    ∃ V hV, y ∈ V ∧
      (derivIdealSheaf k (h ≫ p) $ I.comap h).ideal ⟨V, hV⟩
        = ((derivIdealSheaf k p I).comap h).ideal ⟨V, hV⟩ := by
  classical
  obtain ⟨W0, m, hxW0, -, ⟨c0_⟩⟩ := exists_etaleChart p $ bsM h y
  obtain ⟨W, V, d, e, hW, hV, hyV, hWW0, -, g, hgE, hg⟩ :=
    SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le h y W0 hxW0 ⊤ (by trivial)
  refine ⟨V, hV, hyV, ?_⟩
  let c := c0_.restrict hWW0
  let instkS := sectionsAlgebra k p W
  let instkT := sectionsAlgebra k (h ≫ p) V
  let _s2 := UFin m
  let instPS := c.algebra
  let instTow1 := c.isScalarTower
  have instFE1 :=
    c.algebra_formallyEtale hW
  let _s0 := MvPolynomial (UFin d) $ X.sec W
  let instChartAlgebra := chartAlgebra hW g
  have instFE2 :=
    chartAlgebra_formallyEtale hW hV g
  let instST := (appLE h W V e).hom.toAlgebra
  let instTowkST :=
    of_algebraMap_eq fun a => sy_ $ sectionsAlgebraMap_appLE_apply k p h W V e a
  let instScalarTowerChart :=
    chartAlgebra_isScalarTower hW h e g hg
  let _s1 := UFin m ⊕ UFin d
  let _a0 := MvPolynomial _s1 k
  let instSumT : Algebra _a0 V.sec :=
    ((algebraMap _s0 V.sec).comp
      (algebraMap _a0
        _s0)).toAlgebra
  let instScalarTowerSum : IsScalarTower _a0
      _s0 V.sec :=
    of_algebraMap_eq fun _ => rfl
  have instTowkSum : IsScalarTower k _a0
      V.sec := by
    have :=
      sumEvalAlgebra_isScalarTower k _s2 (UFin d)
        W.sec
    refine of_algebraMap_eq fun a => ?_
    rw [algebraMap_apply _a0
        _s0 V.sec
        (algebraMap k _a0 a),
      ← algebraMap_apply k _a0
        _s0 a,
      algebraMap_apply k W.sec _s0 a,
      ← algebraMap_apply W.sec _s0 V.sec,
      ← algebraMap_apply k W.sec V.sec]
  have instFE3 :=
    formallyEtale_trans k _s2 (UFin d)
      W.sec V.sec
  have hcoord : ∀ i,
      algebraMap W.sec V.sec (EtaleCoordinates.coord k _s2 W.sec i)
        = EtaleCoordinates.coord k _s1 V.sec
            (Sum.inl i) := by
    intro i
    rw [EtaleCoordinates.coord_def k _s1 V.sec $ Sum.inl i,
      algebraMap_apply _a0
        _s0 V.sec,
      algebraMap_X_inl k _s2 (UFin d) W.sec,
      ← algebraMap_eq,
      ← algebraMap_apply W.sec _s0 V.sec]
  rw [comap_ideal_eq_map_appLE (derivIdealSheaf k p I) h ⟨W, hW⟩ ⟨V, hV⟩ e]
  simp [derivIdealSheaf_ideal]
  rw [comap_ideal_eq_map_appLE I h ⟨W, hW⟩ ⟨V, hV⟩ e]
  exact sy_ $ map_derivIdeal_sum k _s2 (UFin d)
    W.sec V.sec hcoord $ I.ideal ⟨W, hW⟩

section
variable (k : Type) [Field k] [IsNoetherianRing k] {X Y : Sch} (p) [Smooth p] [LocallyOfFiniteType p] (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)]
theorem derivIdealSheafIterate_comap (r : ℕ) (I : ISD X) :
    derivIdealSheafIterate k (h ≫ p) r (I.comap h) = (derivIdealSheafIterate k p r I).comap h := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih,
      (idealSheafData_eq_of_locally_eq _ _ fun y => exists_affineOpen_derivIdealSheaf_comap_ideal_eq k p h (derivIdealSheafIterate k p r I) y)]
end

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

private theorem span_eq_top_of_forall_mem_basicOpen {X : Sch} {U : Opn X}
    (hU : IsAffineOpen U) (s : Set $ X.sec U)
    (hcov : ∀ x : X, x ∈ U → ∃ t ∈ s, x ∈ basicOpen X t) :
    span s = ⊤ := by
  refine mp_ (iSup_basicOpen_eq_self_iff hU) ?_
  refine le_antisymm (iSup_le fun f => basicOpen_le (X := X) (f : X.sec U))
    (SetLike.le_def.mpr ?_)
  intro x hx
  obtain ⟨t, hts, hxt⟩ := hcov x hx
  exact mpr_ mem_iSup ⟨⟨t, hts⟩, hxt⟩

section
variable {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (M : Submonoid R) (hlocal : @IsLocalization R _ M S _ g.toAlgebra)
include hlocal
theorem exists_mul_mem_of_map_mem_map
    (b : Ideal R) f (hf : g f ∈ map g b) :
    ∃ t ∈ M, t * f ∈ b := by
  let _ : Algebra R S := g.toAlgebra
  have : IsLocalization M S := hlocal
  have hf' : algebraMap R S f ∈ map (algebraMap R S) b := hf
  obtain ⟨⟨y, m⟩, he⟩ := mp_ (mem_map_algebraMap_iff (M := M) (S := S)) hf'
  rw [← map_mul] at he
  obtain ⟨c, hc⟩ := mp_ (eq_iff_exists (M := M) (S := S)) he
  let _a0 := c
  refine ⟨_a0 * m, M.mul_mem c.2 m.2, ?_⟩
  have h3 : _a0 * m * f = _a0 * y := by rw [← hc]
                                        ring
  rw [h3]
  exact b.mul_mem_left _ y.2

theorem isUnit_map_of_mem_of_isLocalization
    t (ht : t ∈ M) : IsUnit $ g t := by
  let _ := g.toAlgebra
  exact map_units S (⟨t, ht⟩ : M)
end

theorem mem_of_span_mul_mem_eq_top {R : Type} [CommRing R] (b : Ideal R)
    f (h : span {t : R | t * f ∈ b} = ⊤) : f ∈ b := by
  have hC : ∀ g ∈ span {t : R | t * f ∈ b}, g * f ∈ b := by
    intro g hg
    induction hg using span_induction with
    | mem x hx => exact hx
    | zero => simp
    | add x y hx hy ihx ihy => simpa [add_mul] using b.add_mem ihx ihy
    | smul a x hx ih => simpa [smul_eq_mul, mul_assoc] using b.mul_mem_left a ih
  have h1 : 1 ∈ span {t : R | t * f ∈ b} := by
    rw [h]
    exact mem_top
  simpa using hC 1 h1

section
variable {X : Sch}
theorem le_iff_forall_stalkIdeal_le (I J : ISD X) :
    I ≤ J ↔ ∀ x, stalkIdeal I x ≤ stalkIdeal J x := by
  refine ⟨fun h x => stalkIdeal_mono h x, fun h => ?_⟩
  rw [le_def]
  intro U f hf
  have hU := U.2
  have hlocal : ∀ x (hx : x ∈ U.1),
      @IsLocalization Γ(X, U.1) _
        (primeIdealOf hU ⟨x, hx⟩).asIdeal.primeCompl
        (stkX X x) _ $ (pGerm X U.1 x hx).hom.toAlgebra := by
    intro x hx
    exact isLocalization_stalk hU ⟨x, hx⟩
  have hbasic : ∀ x (hx : x ∈ U.1) t,
      IsUnit ((pGerm X U.1 x hx).hom t) → x ∈ bOpn X t := by
    intro x hx t ht
    exact mpr (mem_basicOpen X t x hx) ht
  have key : ∀ x (hx : x ∈ U.1),
      ∃ t, t * f ∈ J.ideal U ∧ x ∈ bOpn X t := by
    intro x hx
    let _a1 := (pGerm X U.1 x hx).hom f
    have hmemI : _a1 ∈ stalkIdeal I x := by
      rw [stalkIdeal_eq_map_germ I x U hx]
      exact mem_map_of_mem _ hf
    have hmem : _a1 ∈
        map (pGerm X U.1 x hx).hom (J.ideal U) := by
      have hh := h x hmemI
      rwa [stalkIdeal_eq_map_germ J x U hx] at hh
    let _a2 := hlocal x hx
    obtain ⟨t, htM, htf⟩ := exists_mul_mem_of_map_mem_map (pGerm X U.1 x hx).hom
      (primeIdealOf hU ⟨x, hx⟩).asIdeal.primeCompl _a2 (J.ideal U) f hmem
    exact ⟨t, htf, hbasic x hx t $ isUnit_map_of_mem_of_isLocalization
      (pGerm X U.1 x hx).hom _ _a2 t htM⟩
  refine mem_of_span_mul_mem_eq_top (J.ideal U) f ?_
  refine span_eq_top_of_forall_mem_basicOpen hU {t : (Γ(X, U.1)) | t * f ∈ J.ideal U}
    (fun x hx => ?_)
  obtain ⟨t, htf, hxt⟩ := key x hx
  exact ⟨t, htf, hxt⟩

theorem notMem_support_of_mem_opens_of_restrictIdeal_eq_top (Z : ISD X)
    (U : Opn X) (h : restrictIdeal Z U = ⊤) x (hx : x ∈ U) : x ∉ support Z := by
  intro hxZ
  obtain ⟨y, hy⟩ : x ∈ range (ι U) := by
    rwa [q1]
  have h' : Z.comap U.i = ⊤ := h
  have h3 := hxZ
  rw [← hy] at h3
  have h4 : y ∈ support (Z.comap U.i) := by
    rwa [m19 Z U.i]
  rwa [h', support_top] at h4


theorem isClosed_of_maximal_irreducible_subset_support (D : ISD X)
    {C} (hC : IsIrreducible C) (hCsub : C ⊆ (support D : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (support D : Set X) → C' = C) :
    IsClosed C := by
  rw [← hCmax (closure C) hC.closure subset_closure $ closure_minimal hCsub D.support.2]
  exact isClosed_closure
end

variable {X : Sch} {k : Type} [Field k] (p : X ⟶ Sp k)

section
variable {V} (hV : IsAffineOpen V) {n} (c : EtaleChart p V n) (j) (D) (hD : restrictIdeal D V = c.coordIdeal {j}) (y) (hy : y ∈ V)
include hV hD
theorem stalkIdeal_eq_span_germ_coord :
    stalkIdeal D y =
      span ({(X.presheaf.germ V y hy).hom $ c.coord j} : Set $ X.presheaf.stalk y) := by
  rw [stalkIdeal_eq_map_germ D y ⟨V, hV⟩ hy, ideal_eq_span_coord c hV D {j} hD, map_span]
  simp

end

section
variable {Y : Sch}
section
variable {W : Opn Y} (hW : IsAffineOpen W)
theorem isUnit_germ_iff_notMem_primeIdealOf y (hy : y ∈ W) f :
    IsUnit ((Y.presheaf.germ W y hy).hom f) ↔ f ∉ asIdeal (hW.primeIdealOf ⟨y, hy⟩) := by
  let _a0 := hW.primeIdealOf ⟨y, hy⟩
  let _ := (pGerm Y W y hy).hom.toAlgebra
  have :=
    hW.isLocalization_stalk ⟨y, hy⟩
  constructor
  intro hu hmem
  exact mp_ (isUnit_to_map_iff (stkX Y y)
    _a0.asIdeal f) hu hmem
  intro hmem
  exact map_units (S := stkX Y y)
    (M := _a0.asIdeal.primeCompl) ⟨f, hmem⟩

theorem primeIdealOf_le_of_specializes a b (ha : a ∈ W) (hb : b ∈ W) (h : a ⤳ b) :
    asIdeal (hW.primeIdealOf ⟨a, ha⟩) ≤ asIdeal (hW.primeIdealOf ⟨b, hb⟩) := by
  intro f hf
  by_contra hcon
  exact (mp_ (isUnit_germ_iff_notMem_primeIdealOf hW a ha f)
    (mp_ (mem_basicOpen Y f a ha) $ h.mem_open (bOpn Y f).isOpen $ mpr (mem_basicOpen Y f b hb) $ mpr_ (isUnit_germ_iff_notMem_primeIdealOf hW b hb f) hcon)) hf
end

theorem isPrime_span_germ_coord {K : Type} [Field K]
    {pr : Y ⟶ Sp K} {W : Opn Y} (hW : IsAffineOpen W) {n : ℕ}
    (c : EtaleChart pr W n) (j : Fin n) (y : Y) (hy : y ∈ W)
    (hcoord : c.coord j ∈ asIdeal (hW.primeIdealOf ⟨y, hy⟩)) :
    (span ({(Y.presheaf.germ W y hy).hom $ c.coord j} :
      Set $ Y.presheaf.stalk y)).IsPrime := by
  let _a0 := Y.sec W
  let instPoly := c.algebra
  have instEt :=
    c.algebra_etale hW
  let instAlg :=
    (pGerm Y W y hy).hom.toAlgebra
  let _a1 := hW.primeIdealOf ⟨y, hy⟩
  have instPrime :=
    _a1.isPrime
  have instLoc := hW.isLocalization_stalk ⟨y, hy⟩
  have hcoordeq : etaleChartCoord K n _a0 j = c.coord j := by
    rw [etaleChartCoord_def]
    exact coordRingHom_X c j
  have h : (span ({algebraMap _a0 (stkX Y y) $ etaleChartCoord K n _a0 j} : Set $ stkX Y y)).IsPrime := by
    let k := K
    let A := stkX Y y
    let hj : etaleChartCoord K n _a0 j ∈ (asIdeal _a1) := by rw [hcoordeq]
                                                             exact hcoord
    have := isRegularLocalRing_of_isLocalization_etale k n _a0 _a1.asIdeal A
    let _m0 := ({j} : FinSet n)
    have hJ : ∀ i ∈ _m0, etaleChartCoord k n _a0 i ∈ asIdeal _a1 := by
      intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      exact hj
    have hJA : ∀ i ∈ _m0,
        algebraMap _a0 A (etaleChartCoord k n _a0 i) ∈ maximalIdeal A := by
      intro i hi
      exact mpr_ (to_map_mem_maximal_iff A _a1.asIdeal _) $ hJ i hi
    exact isPrime_span_singleton
      (fun i : { x : Fin n // x ∈ _m0 } =>
        algebraMap _a0 A $ etaleChartCoord k n _a0 i)
      (fun i => hJA i i.2) (linearIndependent_toCotangent_etaleChartCoord k n _a0 _a1.asIdeal A {j} hJ hJA) ⟨j, mem_singleton_self j⟩
  rwa [hcoordeq] at h
end

section
variable {V : Opn X} (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n) (j : Fin n) (D : ISD X) (hD : restrictIdeal D V = c.coordIdeal {j}) (x et_ : X)
include hD
theorem primeIdealOf_eq_comap_span_germ_coord (hx : x ∈ V) (het_ : et_ ∈ V)
    (hspec : et_ ⤳ x) (hets : et_ ∈ support D)
    (hmin : ∀ P : Ideal $ X.sec V, P.IsPrime → c.coord j ∈ P →
      P ≤ asIdeal (hV.primeIdealOf ⟨et_, het_⟩) → P = asIdeal (hV.primeIdealOf ⟨et_, het_⟩)) :
    asIdeal (hV.primeIdealOf ⟨et_, het_⟩) =
      comap (X.presheaf.germ V x hx).hom
        (span ({(X.presheaf.germ V x hx).hom $ c.coord j} :
          Set $ X.presheaf.stalk x)) := by
  let _a1 := pGerm X V x hx
  let _c0 := ({_a1.hom $ c.coord j} : Set $ stkX X x)
  let _c1 := _a1
  let _c3 := ({c.coord j} : Set V.sec)
  have hcoordq :=
    by
      let y := et_
      let hy := het_
      by_contra hcon
      let _ :=
        (pGerm X V y hy).hom.toAlgebra
      let _a0 := hV.primeIdealOf ⟨y, hy⟩
      have := hV.isLocalization_stalk ⟨y, hy⟩
      have hunit :=
        map_units (S := stkX X y)
          (M := _a0.asIdeal.primeCompl) ⟨c.coord j, hcon⟩
      refine mp_ (mem_support_iff_stalkIdeal_ne_top D y) hets ?_
      rw [stalkIdeal_eq_span_germ_coord p hV c j D hD y hy]
      exact mpr_ span_singleton_eq_top hunit
  have hqle :=
    primeIdealOf_le_of_specializes hV et_ x het_ hx hspec
  have hsp :=
    isPrime_span_germ_coord hV c j x hx $ hqle hcoordq
  let _a0 := comap _c1.hom $ span _c0
  have hPprime : _a0.IsPrime := inferInstance
  have htP : c.coord j ∈ _a0 := by
    rw [mem_comap]
    exact mem_span_singleton_self _
  have hmapspan : map _c1.hom
      (span _c3)
      = span _c0 := by
    rw [map_span, image_singleton]
  have hloc :=
    hV.isLocalization_stalk ⟨x, hx⟩
  refine sy_ $ hmin _ hPprime htP ?_
  intro a ha
  rw [mem_comap, ← hmapspan] at ha
  obtain ⟨s, hs, hsa⟩ := exists_mul_mem_of_map_mem_map _c1.hom
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl hloc
    (span _c3) a ha
  have hs' := hs
  have hle :=
    mpr (span_singleton_le_iff_mem _) hcoordq
  exact ((hV.primeIdealOf ⟨et_, het_⟩).isPrime.mem_or_mem $ hle hsa).resolve_left fun hcon => hs' $ hqle hcon

theorem stalkIdeal_eq_maximalIdeal_of_minimal (_hx : x ∈ V) (het_ : et_ ∈ V)
    (_hspec : et_ ⤳ x) (hets : et_ ∈ support D)
    (hmin : ∀ P : Ideal $ X.sec V, P.IsPrime → c.coord j ∈ P →
      P ≤ asIdeal (hV.primeIdealOf ⟨et_, het_⟩) → P = asIdeal (hV.primeIdealOf ⟨et_, het_⟩)) :
    stalkIdeal D et_ = maximalIdeal (X.presheaf.stalk et_) := by
  let _a0 := pGerm X V et_ het_
  let _ :=
    _a0.hom.toAlgebra
  let _a1 := hV.primeIdealOf ⟨et_, het_⟩
  have := hV.isLocalization_stalk ⟨et_, het_⟩
  let _s0 := algebraMap (X.sec V) $ stkX X et_
  have halg : _s0 = _a0.hom := rfl
  have hsub : comap _a0.hom
      (maximalIdeal $ stkX X et_) ≤
      asIdeal _a1 := by
    intro a ha
    by_contra hcon
    rw [mem_comap, mem_maximalIdeal, mem_nonunits_iff] at ha
    exact ha $ map_units (S := stkX X et_) (M := _a1.asIdeal.primeCompl) ⟨a, hcon⟩
  have h1 : map _s0
      (comap _s0
        (maximalIdeal $ stkX X et_))
      = maximalIdeal (stkX X et_) :=
    map_under (M := _a1.asIdeal.primeCompl)
      (S := stkX X et_) _
  refine le_antisymm (le_maximalIdeal $ mp_ (mem_support_iff_stalkIdeal_ne_top D et_) hets) ?_
  rw [stalkIdeal_eq_span_germ_coord p hV c j D hD et_ het_, ← h1, map_le_iff_le_comap, halg]
  exact le_trans hsub $ le_of_eq $ primeIdealOf_eq_comap_span_germ_coord p hV c j D hD et_ et_ het_ het_ specializes_rfl hets hmin
end

theorem mem_span_pow_of_mul_mem_span_pow {A : Type} [CommRing A] ta_
    (hprime : (span ({ta_} : Set A)).IsPrime) (hnzd : ta_ ∈ nonZeroDivisors A) a :
    ∀ s f, s ∉ span ({ta_} : Set A) →
      s * f ∈ span ({ta_ ^ a} : Set A) → f ∈ span ({ta_ ^ a} : Set A) := by
  induction a with
  | zero =>
      intro s f _ _
      rw [pow_zero, span_singleton_one]
      exact mem_top
  | succ b ih =>
      intro s f hs hsf
      obtain ⟨d, hd⟩ := mp_ mem_span_singleton hsf
      have hsf1 : s * f ∈ span ({ta_} : Set A) := by
        refine mpr_ mem_span_singleton ⟨ta_ ^ b * d, ?_⟩
        rw [hd]
        ring
      obtain ⟨f', rfl⟩ := mp_ mem_span_singleton $ (hprime.mem_or_mem hsf1).resolve_left hs
      let _a0 := s * f' - ta_ ^ b * d
      have hcancel : _a0 * ta_ = 0 := by
        have h2 : _a0 * ta_ = s * (ta_ * f') - ta_ ^ (b + 1) * d := by ring
        rw [h2, hd, sub_self]
      obtain ⟨e, he⟩ := mp_ mem_span_singleton $ ih s f' hs $ mpr_ mem_span_singleton ⟨d, eq_of_sub_eq_zero $ an2 (mp_ mem_nonZeroDivisors_iff hnzd) _ hcancel⟩
      refine mpr_ mem_span_singleton ⟨e, ?_⟩
      rw [he]
      ring

section
variable {Y : Sch} {V : Opn Y} (hV : IsAffineOpen V)
theorem specializes_of_primeIdealOf_le a b (ha : a ∈ V) (hb : b ∈ V)
    (h : asIdeal (hV.primeIdealOf ⟨a, ha⟩) ≤ asIdeal (hV.primeIdealOf ⟨b, hb⟩)) : a ⤳ b := by
  rw [specializes_iff_mem_closure, mem_closure_iff]
  intro W hWopen hbW
  obtain ⟨f, hfW, hbf⟩ :=
    hV.exists_basicOpen_le (⟨b, hbW⟩ : (⟨W, hWopen⟩ : Opn Y)) hb
  have hfa := fun hcon => mp (isUnit_germ_iff_notMem_primeIdealOf hV b hb f) (mp_ (mem_basicOpen Y f b hb) hbf) $ h hcon
  exact ⟨a, SetLike.le_def.mp hfW $ mpr (mem_basicOpen Y f a ha) $ mpr_ (isUnit_germ_iff_notMem_primeIdealOf hV a ha f) hfa, rfl⟩

theorem exists_mem_primeIdealOf_eq_of_isPrime
    (P : Ideal $ Y.sec V) (hP : P.IsPrime) :
    ∃ xi_ hxi_, asIdeal (hV.primeIdealOf ⟨xi_, hxi_⟩) = P := by
  let _c0 := (⟨P, hP⟩ : PrimeSpectrum V.sec)
  have hmem : hV.fromSpec.base _c0 ∈ V :=
    hV.range_fromSpec.subset $ mem_range_self _
  refine ⟨hV.fromSpec.base _c0, hmem, ?_⟩
  exact congrArg asIdeal $ hV.fromSpec.isOpenEmbedding.injective $ hV.fromSpec_primeIdealOf ⟨hV.fromSpec.base _c0, hmem⟩
end

section
variable (D : ISD X) (hloc : ∀ x : X, ∃ (U : Opn X) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n), restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (support D : Set X)) (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (support D : Set X) → C' = C)
include hloc hCsub hCmax
theorem exists_etaleChart_genericPoint_mem
    (x : X) (hx : x ∈ C) :
    ∃ (V : Opn X) (hV : IsAffineOpen V) (_ : x ∈ V) (het_ : hC.genericPoint ∈ V) (n : ℕ)
      (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧ hC.genericPoint ⤳ x ∧
        hC.genericPoint ∈ support D ∧
        ∀ P : Ideal $ X.sec V, P.IsPrime → c.coord j ∈ P →
          P ≤ (hV.primeIdealOf ⟨hC.genericPoint, het_⟩).asIdeal →
          P = (hV.primeIdealOf ⟨hC.genericPoint, het_⟩).asIdeal := by
  let _m0 := ({hC.genericPoint} : Set X)
  have hgen0 : closure _m0 = closure C :=
    (m140 hC.closure isClosed_closure).choose_spec
  have hgen : closure _m0 = C := by
    rw [hgen0]
    exact (isClosed_of_maximal_irreducible_subset_support D hC hCsub hCmax).closure_eq
  have hetC : hC.genericPoint ∈ C := by
    have h1 : hC.genericPoint ∈ closure _m0 := subset_closure rfl
    rwa [hgen] at h1
  have hspec : hC.genericPoint ⤳ x := by
    have h1 : x ∈ closure _m0 := by
      rwa [hgen]
    exact mpr_ specializes_iff_mem_closure h1
  obtain ⟨U, hxU, n, c, hcase⟩ := hloc x
  have hne := fun htop =>
    notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U htop x hxU $ hCsub hx
  obtain ⟨j, hDU⟩ := hcase.resolve_left hne
  obtain ⟨W, hxW, hW⟩ := exists_isAffineOpen_mem x
  obtain ⟨f, hfU, hxf⟩ := hW.exists_basicOpen_le (⟨x, hxU⟩ : U) hxW
  have hVaff := hW.basicOpen f
  have hVU := hfU
  have hxV := hxf
  have hetV := hspec.mem_open (bOpn X f).isOpen hxV
  have hDV :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D {j} hDU
  refine ⟨bOpn X f, hVaff, hxV, hetV, n, c.restrict hVU, j, hDV, hspec, hCsub hetC, ?_⟩
  intro P hP hcoord hPle
  obtain ⟨xi_, hxiV_, hxiP⟩ := exists_mem_primeIdealOf_eq_of_isPrime hVaff P hP
  have hxisupp : xi_ ∈ spI D := by
    rw [mem_support_iff_stalkIdeal_ne_top,
      stalkIdeal_eq_span_germ_coord p hVaff (c.restrict hVU) j D hDV xi_ hxiV_]
    intro htop
    have hnot :=
      mp (isUnit_germ_iff_notMem_primeIdealOf hVaff xi_ hxiV_ $ (c.restrict hVU).coord j) $ mp_ span_singleton_eq_top htop
    rw [hxiP] at hnot
    exact hnot hcoord
  have hxiet :=
    specializes_of_primeIdealOf_le hVaff xi_ hC.genericPoint hxiV_ hetV
      (by rw [hxiP]; exact hPle)
  have hCsubxi : C ⊆ closure ({xi_} : Set X) := by
    have h1 :=
      closure_minimal (mpr_ singleton_subset_iff $ mp_ specializes_iff_mem_closure hxiet)
        isClosed_closure
    rwa [hgen] at h1
  have hxiC_ : xi_ ∈ C := by
    have h1 : xi_ ∈ closure ({xi_} : Set X) := subset_closure rfl
    rwa [hCmax _ isIrreducible_singleton.closure hCsubxi $ closure_minimal (mpr_ singleton_subset_iff hxisupp) D.support.2] at h1
  have hetxi : hC.genericPoint ⤳ xi_ := by
    have h1 := hxiC_
    rw [← hgen] at h1
    exact mpr_ specializes_iff_mem_closure h1
  refine le_antisymm hPle ?_
  rw [← hxiP]
  exact primeIdealOf_le_of_specializes hVaff hC.genericPoint xi_ hetV hxiV_ hetxi

theorem stalkIdeal_le_pow_of_le_orderAt_genericPoint
    (I : ISD X) (a : ℕ) (ha : (a : ENat) ≤ orderAt I hC.genericPoint)
    (x : X) (hx : x ∈ C) :
    stalkIdeal I x ≤ stalkIdeal D x ^ a := by
  obtain ⟨V, hV, hxV, hetV, n, c, j, hD, hspec, hets, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC hCsub hCmax x hx
  let et_ := hC.genericPoint
  let hx := hxV
  let het_ := hetV
  let _a3 := pGerm X V x hx
  let _c0 := ({_a3.hom (c.coord j)} : Set (stkX X x))
  let _c1 := hV.primeIdealOf ⟨et_, het_⟩
  let _c2 := _a3
  let _c3 := hV.primeIdealOf ⟨x, hx⟩
  let _a0 := X.sec V
  let _ : Algebra _a0 (stkX X x) := _c2.hom.toAlgebra
  have : IsLocalization.AtPrime (stkX X x) _c3.asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  let _a1 := pGerm X V et_ het_
  let _ : Algebra _a0 (stkX X et_) := _a1.hom.toAlgebra
  have : IsLocalization.AtPrime (stkX X et_) _c1.asIdeal :=
    hV.isLocalization_stalk ⟨et_, het_⟩
  let _m0 := algebraMap _a0 $ stkX X et_
  have halget : _m0 = _a1.hom := rfl
  have hqcomap :=
    primeIdealOf_eq_comap_span_germ_coord p hV c j D hD x et_ hx het_ hspec hets hmin
  have hqle : ∀ z, _c2.hom z ∈
      span _c0 →
      z ∈ asIdeal _c1 := by
    intro z hz
    rwa [hqcomap]
  have hnetop : (span _c0) ≠ ⊤ := by
    intro hcon
    refine _c1.isPrime.ne_top ?_
    rw [hqcomap, hcon, Ideal.comap_top]
  have hqp : asIdeal _c1 ≤ asIdeal _c3 := by
    intro r hr
    by_contra hcon
    refine hnetop $ eq_top_of_isUnit_mem _ ?_ (map_units (S := stkX X x) (M := _c3.asIdeal.primeCompl) ⟨r, hcon⟩)
    rwa [hqcomap] at hr
  have hdisj : Disjoint (_c3.asIdeal.primeCompl : Set _a0)
      (asIdeal _c1 : Set _a0) := by
    rw [disjoint_left]
    intro r hr hr'
    exact hr $ hqp hr'
  have hmapq : map (algebraMap _a0 (stkX X x))
      _c1.asIdeal =
      span _c0 := by
    rw [hqcomap]
    exact map_under (M := _c3.asIdeal.primeCompl)
      (S := stkX X x) _
  have hprime : (span _c0).IsPrime := by
    rw [← hmapq]
    exact isPrime_of_isPrime_disjoint
      _c3.asIdeal.primeCompl (stkX X x)
      _c1.asIdeal _c1.isPrime hdisj
  have hDet : stalkIdeal D et_ =
      span ({_a1.hom (c.coord j)} : Set (stkX X et_)) :=
    stalkIdeal_eq_span_germ_coord p hV c j D hD et_ het_
  let _a2 := maximalIdeal $ stkX X et_
  have hmaxet : stalkIdeal D et_ = _a2 :=
    stalkIdeal_eq_maximalIdeal_of_minimal p hV c j D hD x et_ hx het_ hspec hets hmin
  let _a4 := span ({c.coord j ^ a} : Set _a0)
  have hmapet : _a2 ^ a =
      map _m0
        _a4 := by
    rw [← hmaxet, hDet, span_singleton_pow, map_span, halget]
    simp [image_singleton, map_pow]
  rw [stalkIdeal_eq_span_germ_coord p hV c j D hD x hx, span_singleton_pow, stalkIdeal_eq_map_germ I x ⟨V, hV⟩ hx,
    map_le_iff_le_comap]
  intro g hg
  rw [mem_comap]
  have hstep := (mp (le_orderAt_iff I et_ a) ha) (germ_mem_stalkIdeal I et_ ⟨V, hV⟩ het_ hg)
  rw [hmapet] at hstep
  obtain ⟨w, hw⟩ := (mem_map_algebraMap_iff
    (M := _c1.asIdeal.primeCompl) (S := stkX X et_)).mp hstep
  let _a5 := (w.1 : _a0)
  let _a6 := (w.2 : _a0)
  have hw' : algebraMap _a0 (stkX X et_) (g * _a6) =
      algebraMap _a0 (stkX X et_) _a5 := by
    rwa [map_mul]
  obtain ⟨cc, hcc⟩ := (eq_iff_exists
    (M := _c1.asIdeal.primeCompl)
    (S := stkX X et_)).mp hw'
  let _s0 := (cc : _a0) * _a6
  have hug : _s0 * g ∈
      _a4 := by
    have heq : _s0 * g = (cc : _a0) * _a5 := by
      rw [← hcc]
      ring
    rw [heq]
    exact mul_mem_left _ _ w.1.2
  have hnotin : _c2.hom _s0 ∉
      span _c0 := by
    intro hcon
    exact mul_mem _ cc.2 w.2.2 $ hqle _ hcon
  obtain ⟨d, hd⟩ := mp mem_span_singleton hug
  refine mem_span_pow_of_mul_mem_span_pow _ hprime (nonZeroDivisors_le_comap _c3.asIdeal.primeCompl (stkX X x) (coord_mem_nonZeroDivisors hV c j)) a _ _ hnotin ?_
  refine mpr mem_span_singleton ⟨_c2.hom d, ?_⟩
  rw [← map_mul, hd, map_mul, map_pow]

theorem stalkIdeal_genericPoint_eq_maximalIdeal :
    stalkIdeal D hC.genericPoint =
      maximalIdeal (X.presheaf.stalk hC.genericPoint) := by
  obtain ⟨x, hx⟩ := an1 hC
  obtain ⟨V, hV, hxV, hetV, n, c, j, hD, hspec, hets, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC hCsub hCmax x hx
  exact stalkIdeal_eq_maximalIdeal_of_minimal p hV c j D hD x hC.genericPoint hxV hetV hspec
    hets hmin

theorem not_stalkIdeal_le_pow_succ_genericPoint
    (I : ISD X) (a : ℕ) (ha : orderAt I hC.genericPoint = (a : ENat)) :
    ¬ stalkIdeal I hC.genericPoint ≤ stalkIdeal D hC.genericPoint ^ (a + 1) := by
  intro hcon
  rw [stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC hCsub hCmax] at hcon
  have h :=
    mpr (le_orderAt_iff I hC.genericPoint $ a + 1) hcon
  rw [ha] at h
  refine absurd h $ mpr_ not_le ?_
  exact_mod_cast lt_succ_self a
end

end FunctorialResolution.EmbeddedResolution
end
section

namespace FunctorialResolution.EmbeddedResolution

namespace EtaleCoordinates

theorem partialDeriv_comm (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (T : Type) [CommRing T] [Algebra k T] [Algebra (MvPolynomial ι k) T]
    [IsScalarTower k (MvPolynomial ι k) T] [FormallyEtale (MvPolynomial ι k) T]
    i j a :
    partialDeriv k ι T i (partialDeriv k ι T j a)
      = partialDeriv k ι T j (partialDeriv k ι T i a) := by
  have hzero : ⁅partialDeriv k ι T i, partialDeriv k ι T j⁆ = 0 := by
    refine derivation_ext_of_coord k ι T T _ _ ?_
    intro l
    rw [commutator_apply]
    simp [partialDeriv_coord]
    split_ifs <;> simp
  have h2 : ⁅partialDeriv k ι T i, partialDeriv k ι T j⁆ a = 0 := by
    rw [hzero]
    simp
  rw [commutator_apply] at h2
  linear_combination h2

end EtaleCoordinates

section
variable (k : Type)
section
variable [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι]
theorem exists_commuting_dual_derivations (A : Type) [CommRing A] [Algebra k A] [FormallySmooth k A]
    (e : Basis ι A $ KaehlerDifferential k A) (w : ι → A)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k A $ w i)) :
    ∃ D : ι → Derivation k A A,
      (∀ i j : ι, D i (w j) = if i = j then 1 else 0) ∧
      (∀ i j : ι, ∀ a : A, D i (D j a) = D j (D i a)) := by
  let _a0 := MvPolynomial ι k
  let _ : Algebra _a0 A :=
    (aeval w).toRingHom.toAlgebra
  have : IsScalarTower k _a0 A :=
    of_algebraMap_eq fun a => by
      rw [algebraMap_toAlgebra]
      simp
  have :=
    formallyEtale_aeval_of_isUnit_det e w hdet
  have hcoord : ∀ i, EtaleCoordinates.coord k ι A i = w i := by
    intro i
    rw [EtaleCoordinates.coord_def, algebraMap_toAlgebra]
    simp
  refine ⟨fun i => p27 k ι A i, ?_, ?_⟩
  intro i j
  rw [← hcoord j]
  exact partialDeriv_coord k ι A i j
  intro i j a
  exact EtaleCoordinates.partialDeriv_comm k ι A i j a

end

section
variable [hv1_0 : Field k] [hv1_1 : CharZero k] {X : Sch} (p : X ⟶ Sp k) [Smooth p]
include hv1_0 hv1_1 p
theorem exists_regularParameters_stalk_of_smooth (x : X) :
    letI := stalkAlgebra k p x
    ∃ (h : ℕ) (y : Fin h → stkX X x)
      (D : Fin h → Derivation k (stkX X x) (stkX X x)),
      span (range y) = maximalIdeal (stkX X x) ∧
      (∀ i j : Fin h, D i (y j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin h, ∀ a : stkX X x, D i (D j a) = D j (D i a)) := by
  let _ := stalkAlgebra k p x
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  let _ := sectionsAlgebra k p U
  let _ := c.algebra
  let _ : DecidableEq $ UFin m := decEq _
  have := c.algebra_formallyEtale hU
  have := c.isScalarTower
  let _ : Algebra U.sec $ stkX X x := (pGerm X U x hxU).hom.toAlgebra
  have : IsScalarTower k U.sec $ stkX X x :=
    isScalarTower_stalk k p U x hxU (algebraMap_sectionsAlgebra k p U)
      (algebraMap_stalkAlgebra k p x) rfl
  have : IsLocalization (asIdeal $ hU.primeIdealOf ⟨x, hxU⟩).primeCompl
      (stkX X x) := hU.isLocalization_stalk ⟨x, hxU⟩
  have := isNoetherianRing_stalk k p x
  let _ : Algebra k $ ResidueField $ stkX X x :=
    ((residue $ stkX X x).comp $ stalkAlgebraMap k p x).toAlgebra
  have : IsScalarTower k (stkX X x)
      (ResidueField $ stkX X x) :=
    of_algebraMap_eq fun a => by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      rfl
  have := formallySmooth_residueField k p x rfl
  let ι := UFin m
  let S := X.sec U
  let q := asIdeal $ hU.primeIdealOf ⟨x, hxU⟩
  let A := stkX X x
  obtain ⟨g, w, J, hgq, -, hspan, -, hgdet, -⟩ :=
    exists_adapted_parameters k ι S q A
  let _s0 := MvPolynomial ι k
  let _a0 := (algebraMap S A).comp $ algebraMap _s0 S
  let _ : Algebra _s0 A :=
    _a0.toAlgebra
  have halg : (algebraMap _s0 A)
      = _a0 := rfl
  have : IsScalarTower _s0 S A :=
    of_algebraMap_eq fun z => by rw [halg]
                                 rfl
  have : IsScalarTower k _s0 A :=
    of_algebraMap_eq fun a => by
      rw [halg, comp_apply, ← algebraMap_apply k _s0 S,
        ← algebraMap_apply k S A]
  have : FormallyEtale S A := of_isLocalization q.primeCompl
  have : FormallyEtale _s0 A :=
    comp _s0 S A
  have : FormallySmooth k A := m139 k _s0 A
  obtain ⟨e, he⟩ : ∃ e : Basis ι A $ KaehlerDifferential k A,
      IsUnit (e.det fun i : ι => m13 k A $ algebraMap S A $ w i) := by
    refine ⟨basisKaehler k ι A, ?_⟩
    rw [← algebraMap_det_basisKaehler k ι S A w, ← hgdet]
    exact map_units (M := q.primeCompl) A ⟨g, hgq⟩
  obtain ⟨D, hD, hDD⟩ :=
    exists_commuting_dual_derivations k ι A e (fun i => algebraMap S A $ w i) he
  obtain ⟨h, ix, hix, hrange⟩ :
      ∃ (h : ℕ) (ix : Fin h → ι), m120 ix ∧ m30 ix = (J : Set ι) := by
    refine ⟨J.card, fun i => ((J.equivFin.symm i : {a : ι // a ∈ J}) : ι), ?_, ?_⟩
    intro a b hab
    exact J.equivFin.symm.injective $ m26 hab
    ext l
    simp [mem_range]
    constructor
    rintro ⟨i, rfl⟩
    exact (J.equivFin.symm i).2
    intro hl
    exact ⟨J.equivFin ⟨l, hl⟩, by simp⟩
  have hset : (algebraMap S A) '' (imS w (J))
      = range fun i => algebraMap S A $ w $ ix i := by
    rw [← hrange]
    ext a
    constructor
    rintro ⟨b, ⟨l, ⟨i, rfl⟩, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
    rintro ⟨i, rfl⟩
    exact ⟨w $ ix i, ⟨ix i, ⟨i, rfl⟩, rfl⟩, rfl⟩
  refine ⟨h, fun i => algebraMap S A $ w $ ix i, fun i => D $ ix i, ?_, ?_, ?_⟩
  rw [← hspan, map_span, hset]
  intro i j
  rw [hD]
  simp [show (ix i = ix j) ↔ (i = j) from ⟨fun hc => hix hc, fun hc => by rw [hc]⟩]
  intro i j a
  exact hDD (ix i) (ix j) a

theorem orderAt_mul
    (I J : ISD X) (x : X) :
    orderAt (I * J) x = orderAt I x + orderAt J x := by
  let _ := stalkAlgebra k p x
  have := isNoetherianRing_stalk k p x
  obtain ⟨h, y, D, hspan, hD, hDD⟩ := exists_regularParameters_stalk_of_smooth k p x
  simp [orderAt_eq_idealOrder, stalkIdeal_mul]
  exact idealOrder_mul y D hspan hD hDD (fun n hn => isUnit_natCast_stalk k p x hn)
    (stalkIdeal I x) $ stalkIdeal J x

theorem orderAt_pow
    (I : ISD X) (c : ℕ) (x : X) :
    orderAt (I ^ c) x = (c : ENat) * orderAt I x := by
  let _ := stalkAlgebra k p x
  have := isNoetherianRing_stalk k p x
  obtain ⟨h, y, D, hspan, hD, hDD⟩ := exists_regularParameters_stalk_of_smooth k p x
  simp [orderAt_eq_idealOrder, stalkIdeal_pow]
  exact idealOrder_pow y D hspan hD hDD (fun n hn => isUnit_natCast_stalk k p x hn)
    (stalkIdeal I x) c
end
end

theorem natCast_mul_le_mul_iff {c : ℕ} (hc : 1 ≤ c) (m : ℕ) (a : ENat) :
    (c : ENat) * (m : ENat) ≤ (c : ENat) * a ↔ (m : ENat) ≤ a := by
  induction a using ENat.recTopCoe with
  | top =>
    have hc0 : c ≠ 0 := by
      simp [ne_eq]
      omega
    have htop : (c : ENat) * ⊤ = ⊤ := by simp [hc0]
    simp [htop]
  | coe n =>
    constructor
    intro hle
    have h' : c * m ≤ c * n := by exact_mod_cast hle
    exact_mod_cast (Nat.le_of_mul_le_mul_left h' $ by omega)
    intro hle
    have h' : m ≤ n := by exact_mod_cast hle
    exact_mod_cast (Nat.mul_le_mul (le_refl c) h')

theorem orderAtLeastLocus_pow_mul (k : Type) [Field k] [CharZero k] {X : Sch}
    (p : X ⟶ Sp k) [Smooth p]
    (I : ISD X) {c : ℕ} (hc : 1 ≤ c) (m : ℕ) :
    orderAtLeastLocus (I ^ c) (c * m) = orderAtLeastLocus I m := by
  ext x
  rw [mem_orderAtLeastLocus_iff, mem_orderAtLeastLocus_iff, orderAt_pow k p I c x, cast_mul]
  exact natCast_mul_le_mul_iff hc m $ orderAt I x


theorem le_natCast_or_succ_le (a : ENat) (r : ℕ) :
    a ≤ (r : ENat) ∨ ((r + 1 : ℕ) : ENat) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  exact m61 le_top
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 ha
  rcases m63 r m with hm | hm
  exact m61 $ by exact_mod_cast hm
  exact m51 $ by exact_mod_cast hm

section
variable {X Y : Sch} (h : Y ⟶ X) (I : ISD X) (y : Y)
theorem stalkIdeal_comap :
    stalkIdeal (I.comap h) y =
      map (h.stalkMap y).hom (stalkIdeal I $ h.base y) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    m227
      (show bsM h y ∈ (⊤) from trivial)
  obtain ⟨V, hV, hyV, e⟩ :=
    m227 $ show y ∈ preU h U from hxU
  have hcomp :=
    by
    let hy := hyV
    have key : appLE h U V e ≫ pGerm Y V y hy
        = pGerm X U (bsM h y) (e hy) ≫ h.stalkMap y := by
      simp [appLE, assoc]
      exact sy_ $ germ_stalkMap ..
    simpa only [hom_comp] using congrArg hom key
  rw [stalkIdeal_eq_map_germ (cmI I h) y ⟨V, hV⟩ hyV,
    stalkIdeal_eq_map_germ I (bsM h y) ⟨U, hU⟩ hxU,
    comap_ideal_eq_map_appLE I h ⟨U, hU⟩ ⟨V, hV⟩ e,
    map_map, map_map]
  exact congrArg (fun ph_ => map ph_ $ I.ideal ⟨U, hU⟩) hcomp

theorem orderAt_le_orderAt_comap :
    orderAt I (h.base y) ≤ orderAt (I.comap h) y := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_orderAt_iff] at hn ⊢
  rw [stalkIdeal_comap]
  exact le_trans (map_mono hn)
    (le_trans (m219 ..).le
      (pow_right_mono (map_maximalIdeal_le ..) n))
end

section
variable (k : Type) [Field k] [CharZero k] {X Y : Sch} (p : X ⟶ Sp k) [Smooth p] (h : Y ⟶ X) [Smooth h] (I : ISD X)
include p
theorem orderAt_comap y :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  have : LocallyOfFiniteType p := inferInstance
  have : LocallyOfFiniteType $ h ≫ p := inferInstance
  refine le_antisymm ?_ $ orderAt_le_orderAt_comap h I y
  rcases eq_or_ne (orderAt I (bsM h y)) ⊤ with hI | hI
  simp_all
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 hI
  rw [← hr]
  rcases le_natCast_or_succ_le (orderAt (cmI I h) y) r with hle | hlt
  exact hle
  exfalso
  have h1 :=
    le_orderAt_derivIdealSheafIterate k (h ≫ p) (cmI I h) y 1 r $ by
      rw [Nat.add_comm]
      exact hlt
  rw [derivIdealSheafIterate_comap k p h r I] at h1
  let _a0 := derivIdealSheafIterate k p r I
  have h2 : (1 : ENat) ≤ orderAt (cmI _a0 h) y := by exact_mod_cast h1
  have h3 : (1 : ENat) ≤ orderAt _a0 (bsM h y) := by
    let _a1 := ((1 : ℕ) : ENat)
    have h1 : _a1 ≤ orderAt (cmI _a0 h) y := by exact_mod_cast h2
    suffices hs : _a1 ≤ orderAt _a0 (bsM h y) by exact_mod_cast hs
    rw [le_orderAt_iff] at h1 ⊢
    rw [stalkIdeal_comap, pow_one] at h1
    rw [pow_one]
    simpa only [maximalIdeal_comap] using
      Ideal.le_comap_map.trans $ comap_mono h1
  rw [orderAt_derivIdealSheafIterate_eq_sub k p I (bsM h y) hr.symm $ le_refl r, Nat.sub_self] at h3
  simp at h3

theorem orderAtLeastLocus_comap m :
    orderAtLeastLocus (I.comap h) m = ⇑h.base ⁻¹' orderAtLeastLocus I m := by
  ext y
  simp [mem_orderAtLeastLocus_iff, orderAt_comap k p h I y]
end


namespace EtaleCoordinates

variable (k : Type) [CommRing k] (ι S : Type) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [FormallyEtale (MvPolynomial ι k) S]

section
variable (h : ι)
section
variable (J : Ideal S)
def partialDerivIdeal : Ideal S :=
  J ⊔ span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x}

theorem partialDerivIdeal_def :
    partialDerivIdeal k ι S h J =
      J ⊔ span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x} := rfl

theorem partialDeriv_mem_partialDerivIdeal {g} (hg : g ∈ J) :
    partialDeriv k ι S h g ∈ partialDerivIdeal k ι S h J := by
  rw [partialDerivIdeal_def]
  exact mem_sup_right $ subset_span ⟨g, hg, rfl⟩

theorem le_partialDerivIdeal : J ≤ partialDerivIdeal k ι S h J := by
  rw [partialDerivIdeal_def]
  exact le_sup_left
end

theorem partialDerivIdeal_le_iff J K :
    partialDerivIdeal k ι S h J ≤ K ↔ J ≤ K ∧ ∀ g ∈ J, partialDeriv k ι S h g ∈ K := by
  rw [partialDerivIdeal_def, sup_le_iff, span_le]
  constructor
  rintro ⟨h1, h2⟩
  exact ⟨h1, fun g hg => h2 ⟨g, hg, rfl⟩⟩
  rintro ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  intro x hx
  obtain ⟨g, hg, rfl⟩ := hx
  exact h2 g hg

theorem partialDerivIdeal_le {J K} (hJK : J ≤ K)
    (hD : ∀ g ∈ J, partialDeriv k ι S h g ∈ K) : partialDerivIdeal k ι S h J ≤ K :=
  mpr (partialDerivIdeal_le_iff k ι S h J K) ⟨hJK, hD⟩

theorem partialDerivIdeal_mono : Monotone $ partialDerivIdeal k ι S h := by
  intro I J hIJ
  rw [partialDerivIdeal_le_iff]
  exact ⟨hIJ.trans $ le_partialDerivIdeal k ι S h J, fun g hg => partialDeriv_mem_partialDerivIdeal k ι S h J $ hIJ hg⟩
end

section
variable {i h : ι} (hih : i ≠ h)
include hih
theorem partialDeriv_mem_tangentDerivations_of_ne :
    partialDeriv k ι S i ∈ tangentDerivations k (span ({coord k ι S h} : Set S)) := by
  rw [mem_tangentDerivations_span_singleton, partialDeriv_coord_of_ne k ι S i h hih]
  exact m97 _

theorem partialDeriv_mem_logDerivIdeal_of_ne J {g}
    (hg : g ∈ J) :
    partialDeriv k ι S i g ∈ logDerivIdeal k (span ({coord k ι S h} : Set S)) J :=
  derivation_apply_mem_logDerivIdeal k (span ({coord k ι S h} : Set S)) J
    (partialDeriv k ι S i) (partialDeriv_mem_tangentDerivations_of_ne k ι S hih) hg
end

def evalDerivationAddHom (g : S) : Derivation k S S →+ S where
  toFun D := D g
  map_zero' := rfl
  map_add' _ _ := rfl

def partialDerivIdealIterate (h : ι) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | l + 1, J => partialDerivIdeal k ι S h $ partialDerivIdealIterate h l J

theorem partialDerivIdealIterate_zero (h : ι) J :
    partialDerivIdealIterate k ι S h 0 J = J := rfl

theorem partialDerivIdealIterate_succ (h : ι) l J :
    partialDerivIdealIterate k ι S h (l + 1) J =
      partialDerivIdeal k ι S h (partialDerivIdealIterate k ι S h l J) := rfl


omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [FormallyEtale (MvPolynomial ι k) S] in
private theorem derivation_sum_apply (s : Finset ι) (f : ι → Derivation k S S) (g : S) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g :=
  map_sum (evalDerivationAddHom k S g) f s

theorem derivation_apply_eq_sum_partialDeriv [Fintype ι] (D : Derivation k S S) (g : S) :
    D g = ∑ i, D (coord k ι S i) * partialDeriv k ι S i g := by
  exact tr_ (congrArg (fun E => E g) $ eq_sum_smul_partialDeriv k ι S D) $ derivation_sum_apply k ι S univ (fun i => D (coord k ι S i) • partialDeriv k ι S i) g

theorem derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal [Fintype ι] (h : ι) I :
    derivIdeal k I ≤
      logDerivIdeal k (span ({coord k ι S h} : Set S)) I ⊔ partialDerivIdeal k ι S h I := by
  rw [derivIdeal_le_iff]
  refine ⟨(le_logDerivIdeal k (span ({coord k ι S h} : Set S)) I).trans le_sup_left, ?_⟩
  intro D g hg
  rw [derivation_apply_eq_sum_partialDeriv k ι S D g]
  refine sum_mem _ ?_
  intro i _
  by_cases hi : i = h
  rw [hi]
  exact mem_sup_right
    (mul_mem_left _ _ $ partialDeriv_mem_partialDerivIdeal k ι S h I hg)
  exact mem_sup_left
    (mul_mem_left _ _ $ partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hg)

section
variable (h : ι) (K : Ideal S)
def idealInfComapPartialDeriv : Ideal S where
  carrier := {g : S | g ∈ K ∧ partialDeriv k ι S h g ∈ K}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨Submodule.add_mem K ha1 hb1, ?_⟩
    rw [map_add]
    exact Submodule.add_mem K ha2 hb2
  zero_mem' := by
    refine ⟨Submodule.zero_mem K, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem K
  smul_mem' := by
    intro c x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨mul_mem_left K c hx1, ?_⟩
    have hl : partialDeriv k ι S h (c * x)
        = c * partialDeriv k ι S h x + x * partialDeriv k ι S h c := by
      rw [leibniz, smul_eq_mul, smul_eq_mul]
    show partialDeriv k ι S h (c * x) ∈ K
    rw [hl]
    exact Submodule.add_mem K (mul_mem_left K c hx2) $ mul_mem_right _ K hx1

theorem mem_idealInfComapPartialDeriv_iff g :
    g ∈ idealInfComapPartialDeriv k ι S h K ↔ g ∈ K ∧ partialDeriv k ι S h g ∈ K := m22
end

section
variable [Fintype ι] [DecidableEq ι] (h : ι)
theorem partialDerivIdeal_logDerivIdeal_le I :
    partialDerivIdeal k ι S h
        (logDerivIdeal k (span ({coord k ι S h} : Set S)) I) ≤
      logDerivIdeal k (span ({coord k ι S h} : Set S)) (partialDerivIdeal k ι S h I) := by
  let _m0 := span ({coord k ι S h} : Set S)
  let _a1 := partialDerivIdeal k ι S h I
  have key : logDerivIdeal k _m0 I ≤
      idealInfComapPartialDeriv k ι S h
        (logDerivIdeal k _m0
          _a1) := by
    rw [logDerivIdeal_le_iff]
    constructor
    · intro g hg
      rw [mem_idealInfComapPartialDeriv_iff]
      constructor
      · exact le_logDerivIdeal k _ _ $ le_partialDerivIdeal k ι S h I hg
      · exact le_logDerivIdeal k _ _ $ partialDeriv_mem_partialDerivIdeal k ι S h I hg
    · intro D hD y hy
      rw [mem_idealInfComapPartialDeriv_iff]
      obtain ⟨c, hc⟩ := mp_ mem_span_singleton' (mp (mem_tangentDerivations_span_singleton k (coord k ι S h) D) hD)
      constructor
      · exact logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I)
          (derivation_apply_mem_logDerivIdeal k _ I D hD hy)
      · rw [derivation_apply_eq_sum_partialDeriv k ι S D y]
        rw [map_sum]
        refine sum_mem _ ?_
        intro i _
        rw [leibniz]
        refine m60 _ ?_ ?_
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul, ← hc, mul_assoc]
            refine mul_mem_left _ _ ?_
            let hg := partialDeriv_mem_partialDerivIdeal k ι S h I hy
            have hmem := derivation_apply_mem_logDerivIdeal k (span ({coord k ι S h} : Set S)) _a1
              (coord k ι S h • partialDeriv k ι S h)
              (smul_mem_tangentDerivations k (span ({coord k ι S h} : Set S))
    (mem_span_singleton_self (coord k ι S h)) (partialDeriv k ι S h)) hg
            simpa [smul_eq_mul] using hmem
          · rw [smul_eq_mul, partialDeriv_comm k ι S h i y]
            exact mul_mem_left _ _ (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi _a1 (partialDeriv_mem_partialDerivIdeal k ι S h I hy))
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul]
            exact mul_mem_right _ _ (le_logDerivIdeal k _ _ $ partialDeriv_mem_partialDerivIdeal k ι S h I hy)
          · rw [smul_eq_mul]
            exact mul_mem_right _ _ (logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I) (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hy))
  refine partialDerivIdeal_le k ι S h ?_ ?_
  · intro g hg
    exact an1 (mp_ (mem_idealInfComapPartialDeriv_iff k ι S h _ g) (key hg))
  · intro g hg
    exact an2 (mp_ (mem_idealInfComapPartialDeriv_iff k ι S h _ g) (key hg))

theorem partialDerivIdeal_logDerivIdealIterate_le m
    I :
    partialDerivIdeal k ι S h
        (logDerivIdealIterate k (span ({coord k ι S h} : Set S)) m I) ≤
      logDerivIdealIterate k (span ({coord k ι S h} : Set S)) m
        (partialDerivIdeal k ι S h I) := by
  induction m with
  | zero => exact le_of_eq $ by simp [logDerivIdealIterate_zero]
  | succ m ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact (partialDerivIdeal_logDerivIdeal_le k ι S h _).trans $ logDerivIdeal_mono k _ ih

theorem derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate n J :
    derivIdealIterate k n J ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealIterate k (span ({coord k ι S h} : Set S)) (n - l)
          (partialDerivIdealIterate k ι S h l J) := by
  let _c0 := span ({coord k ι S h} : Set S)
  induction n with
  | zero =>
      rw [derivIdealIterate_zero]
      exact le_iSup₂ (f := fun m (_ : m ≤ 0) =>
        logDerivIdealIterate k _c0 (0 - m)
          (partialDerivIdealIterate k ι S h m J)) 0 le_rfl
  | succ n ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun l => ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun hl => ?_
      refine le_trans (derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal k ι S h _) ?_
      refine sup_le ?_ ?_
      rw [← logDerivIdealIterate_succ, show n - l + 1 = n + 1 - l from by omega]
      exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
        logDerivIdealIterate k _c0 (n + 1 - m)
          (partialDerivIdealIterate k ι S h m J)) l $ by omega
      refine le_trans (partialDerivIdeal_logDerivIdealIterate_le k ι S h (n - l) _) ?_
      rw [← partialDerivIdealIterate_succ, show n - l = n + 1 - (l + 1) from by omega]
      exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
        logDerivIdealIterate k _c0 (n + 1 - m)
          (partialDerivIdealIterate k ι S h m J)) (l + 1) $ by omega
end

end EtaleCoordinates

namespace EtaleCoordinates

section

variable (k : Type) [CommRing k] (ι S : Type) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]

theorem partialDerivIdeal_iSup_le {ka_ : Sort*} (h : ι) (F : ka_ → Ideal S) :
    partialDerivIdeal k ι S h (⨆ j, F j) ≤ ⨆ j, partialDerivIdeal k ι S h (F j) := by
  refine partialDerivIdeal_le k ι S h (iSup_mono fun j => le_partialDerivIdeal k ι S h (F j)) ?_
  intro g hg
  refine iSup_induction (motive := fun x =>
      partialDeriv k ι S h x ∈ ⨆ j, partialDerivIdeal k ι S h (F j)) F hg ?_ ?_ ?_
  intro j x hx
  exact le_iSup (fun j => partialDerivIdeal k ι S h (F j)) j
    (partialDeriv_mem_partialDerivIdeal k ι S h (F j) hx)
  simp only [map_zero]
  exact m97 _
  intro x y hx hy
  simp only [map_add]
  exact m60 _ hx hy

theorem partialDerivIdeal_biSup_le (h : ι) (n : ℕ) (F : ℕ → Ideal S) :
    partialDerivIdeal k ι S h (⨆ i, ⨆ _ : i ≤ n, F i) ≤
      ⨆ i, ⨆ _ : i ≤ n, partialDerivIdeal k ι S h (F i) :=
  (partialDerivIdeal_iSup_le k ι S h fun i => ⨆ _ : i ≤ n, F i).trans
    (iSup_mono fun i => partialDerivIdeal_iSup_le k ι S h fun _ => F i)

end

section

variable (k : Type) [CommRing k] (ι : Type) [DecidableEq ι]
  (S : Type) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]
  (S1_ : Type) [CommRing S1_] [Algebra k S1_] [Algebra (MvPolynomial ι k) S1_]
  [IsScalarTower k (MvPolynomial ι k) S1_] [FormallyEtale (MvPolynomial ι k) S1_]
  (ph_ : S →ₐ[k] S1_) (T : Finset ι) (s h : ι)

theorem partialDerivIdealIterate_controlledTransform_le_iSup
    (hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → ph_ (coord k ι S i) = coord k ι S1_ i * coord k ι S1_ s)
    (hs : ph_ (coord k ι S s) = coord k ι S1_ s)
    (hout : ∀ i ∉ T, ph_ (coord k ι S i) = coord k ι S1_ i)
    (hnzd : coord k ι S1_ s ∈ nonZeroDivisors S1_)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S1_) (m : ℕ)
    (hL : ∀ i ≤ m,
      span {coord k ι S1_ s ^ (m - i)} * L i = map ph_ (derivIdealIterate k i J))
    (l : ℕ) (hl : l ≤ m) :
    partialDerivIdealIterate k ι S1_ h l (L 0) ≤ ⨆ i, ⨆ _ : i ≤ l, L i := by
  revert hl
  induction l with
  | zero =>
      intro _
      rw [partialDerivIdealIterate_zero]
      exact le_iSup₂ (f := fun i (_ : i ≤ 0) => L i) 0 le_rfl
  | succ l ih =>
      intro hl
      rw [partialDerivIdealIterate_succ]
      refine le_trans (partialDerivIdeal_mono k ι S1_ h $ ih $ m212 hl) ?_
      refine le_trans (partialDerivIdeal_biSup_le k ι S1_ h l L) ?_
      refine iSup_le fun i => iSup_le fun hi => ?_
      have him : i < m := lt_of_le_of_lt hi $ by omega
      have hstep : partialDerivIdeal k ι S1_ h (L i) ≤ L i ⊔ L (i + 1) := by
        refine partialDerivIdeal_le k ι S1_ h le_sup_left ?_
        intro g hg
        let _a0 := m - i - 1
        have hc : m - i = _a0 + 1 := by omega
        let _a1 := derivIdealIterate k i J
        have hJ : span {coord k ι S1_ s ^ (_a0 + 1)} * L i
            = map ph_ _a1 := by
          rw [← hc]
          exact hL i $ le_of_lt him
        refine partialDeriv_mem_sup_of_span_pow_mul_eq_map k ι S S1_ ph_ T s hin hs hout hnzd h hhT hhs
          _a1 (L i) (L $ i + 1) (m - i - 1) hJ ?_ g hg
        have h2 := hL (i + 1) $ by omega
        have h3 : m - (i + 1) = m - i - 1 := by omega
        rw [h3] at h2
        rw [← derivIdealIterate_succ]
        exact le_of_eq h2.symm
      refine hstep.trans $ sup_le ?_ ?_
      exact le_iSup₂ (f := fun j (_ : j ≤ l + 1) => L j) i $ by omega
      exact le_iSup₂ (f := fun j (_ : j ≤ l + 1) => L j) (i + 1) $ by omega

theorem derivIdealIterate_le_iSup_logDerivIdealIterate_controlledTransform [Fintype ι]
    (hsT : s ∈ T)
    (hin : ∀ i ∈ T, i ≠ s → ph_ (coord k ι S i) = coord k ι S1_ i * coord k ι S1_ s)
    (hs : ph_ (coord k ι S s) = coord k ι S1_ s)
    (hout : ∀ i ∉ T, ph_ (coord k ι S i) = coord k ι S1_ i)
    (hnzd : coord k ι S1_ s ∈ nonZeroDivisors S1_)
    (hhT : h ∈ T) (hhs : h ≠ s)
    (J : Ideal S) (L : ℕ → Ideal S1_) (m : ℕ)
    (hL : ∀ i ≤ m,
      span {coord k ι S1_ s ^ (m - i)} * L i = map ph_ (derivIdealIterate k i J))
    (n : ℕ) (hn : n ≤ m) :
    derivIdealIterate k n (L 0) ≤
      ⨆ i, ⨆ _ : i ≤ n,
        logDerivIdealIterate k (span ({coord k ι S1_ h} : Set S1_)) (n - i) (L i) := by
  let _c0 := span ({coord k ι S1_ h} : Set S1_)
  refine (derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate k ι S1_ h n $ L 0).trans ?_
  refine iSup_le fun l => iSup_le fun hln => ?_
  refine (logDerivIdealIterate_mono k _c0 (n - l) $ partialDerivIdealIterate_controlledTransform_le_iSup k ι S S1_ ph_ T s h hsT hin hs hout hnzd hhT hhs J L m hL l $ hln.trans hn).trans ?_
  refine (logDerivIdealIterate_iSup_le k _c0 (n - l)
    (fun i => ⨆ _ : i ≤ l, L i)).trans ?_
  refine iSup_le fun i => ?_
  refine (logDerivIdealIterate_iSup_le k _c0 (n - l)
    (fun _ => L i)).trans ?_
  refine iSup_le fun hi => ?_
  have h2 :=
    logDerivIdealIterate_le_of_le k _c0
      (by omega : n - l ≤ n - i) $ L i
  exact h2.trans $ le_iSup₂
    (f := fun j (_ : j ≤ n) =>
      logDerivIdealIterate k _c0 (n - j) $ L j)
    i $ hi.trans hln

end

end EtaleCoordinates

section
variable {X : Sch}
theorem support_subset_orderAtLeastLocus_of_le_pow (Z I : ISD X) m
    (h : I ≤ Z ^ m) : (support Z : Set X) ⊆ orderAtLeastLocus I m := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow]
  have h1 := stalkIdeal_mono h x
  rw [stalkIdeal_pow] at h1
  exact h1.trans $ pow_right_mono (mp (mem_support_iff_stalkIdeal_le_maximalIdeal Z x) hx) m

theorem mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen (I : ISD X) {U}
    (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ support I ↔ I.ideal ⟨U, hU⟩ ≤ asIdeal (hU.primeIdealOf x) := by
  have := hU.isLocalization_stalk x
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I x ⟨U, hU⟩ x.2]
  constructor
  intro hle y hy
  exact mp_ (to_map_mem_maximal_iff
    (stkX X x) (hU.primeIdealOf x).asIdeal y) $ hle $ mem_map_of_mem _ hy
  intro hle
  rw [map_le_iff_le_comap]
  intro y hy
  exact mpr_ (to_map_mem_maximal_iff
    (stkX X x) (hU.primeIdealOf x).asIdeal y) $ hle hy

section
variable {U : Opn X} (hU : IsAffineOpen U)
theorem exists_point_primeIdealOf_eq
    q : ∃ x, hU.primeIdealOf x = q := by
  have hmem : hU.fromSpec.base q ∈ U := by
    have h1 : hU.fromSpec.base q ∈ range hU.fromSpec.base := ⟨q, rfl⟩
    rwa [hU.range_fromSpec] at h1
  refine ⟨⟨hU.fromSpec.base q, hmem⟩, ?_⟩
  apply hU.fromSpec.isOpenEmbedding.injective
  exact hU.fromSpec_primeIdealOf ⟨hU.fromSpec.base q, hmem⟩

theorem ideal_le_of_support_subset
    (Z J : ISD X) (hrad : (Z.ideal ⟨U, hU⟩).IsRadical)
    (hsupp : ∀ x : X, x ∈ support Z → x ∈ U → x ∈ support J) :
    J.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ := by
  rw [← hrad.radical, radical_eq_sInf]
  refine le_sInf ?_
  rintro q ⟨hq1, hq2⟩
  obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq hU ⟨q, hq2⟩
  have hxq' := congrArg asIdeal hxq
  have hxZ := by
    refine mpr_ (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen Z hU x) ?_
    rwa [hxq']
  have hfin := mp_ (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen J hU x) $ hsupp x hxZ x.2
  rwa [hxq'] at hfin
end

theorem ideal_eq_top_of_disjoint_support (Z : ISD X)
    (W : X.affineOpens) (hW : ∀ y : X, y ∈ W.1 → y ∉ support Z) : Z.ideal W = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := exists_le_maximal _ hne
  obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq W.2 ⟨P, hP.isPrime⟩
  refine hW x x.2 ?_
  refine mpr_ (mem_support_iff_ideal_le_primeIdealOf_of_isAffineOpen Z W.2 x) ?_
  rwa [congrArg asIdeal hxq]

theorem le_pow_of_forall_le_pow_basicOpen (Z I : ISD X) m
    (hloc : ∀ (V : X.affineOpens) (x : X), x ∈ V.1 →
      ∃ g : Γ(X, V.1), x ∈ basicOpen X g ∧
        I.ideal (X.affineBasicOpen g) ≤ Z.ideal (X.affineBasicOpen g) ^ m) :
    I ≤ Z ^ m := by
  have key : ∀ V : affO X, I.ideal V ≤ (Z ^ m).ideal V := by
    intro V
    rw [ideal_pow, Pi.pow_apply]
    intro a ha
    by_contra hcon
    have hcol : ((Z.ideal V) ^ m).colon (span {a}) ≠ ⊤ := by
      intro htop
      have h1 : (1 : Γ(X, V.1)) ∈ ((Z.ideal V) ^ m).colon (span {a}) := by
        rw [htop]
        exact mem_top
      have h2 := mp_ mem_colon h1 a $ mem_span_singleton_self a
      rw [smul_eq_mul, one_mul] at h2
      exact hcon h2
    obtain ⟨P, hP, hPle⟩ := exists_le_maximal _ hcol
    have : P.IsPrime := hP.isPrime
    obtain ⟨x, hxq⟩ := exists_point_primeIdealOf_eq V.2 ⟨P, hP.isPrime⟩
    obtain ⟨g, hxg, hgle⟩ := hloc V x x.2
    have hgP : g ∉ P := by
      have hg : g ∉ asIdeal ((V.2).primeIdealOf x) := by
        let hU := V.2
        have := hU.isLocalization_stalk x
        intro hmem
        have h2 := mpr_ (to_map_mem_maximal_iff
          (stkX X x) (hU.primeIdealOf x).asIdeal g) hmem
        exact mp_ (mem_maximalIdeal _) h2 $ mp (X.mem_basicOpen g x x.2) hxg
      rwa [congrArg asIdeal hxq] at hg
    let _ :=
      (pMap X (homOfLE $ X.basicOpen_le g).op).hom.toAlgebra
    have : m215 g Γ(X, bOpn X g) := V.2.isLocalization_basicOpen g
    have hZ : map (algebraMap Γ(X, V.1) Γ(X, bOpn X g)) (Z.ideal V) =
        Z.ideal (X.affineBasicOpen g) := Z.map_ideal_basicOpen V g
    have hmem : (algebraMap Γ(X, V.1) Γ(X, bOpn X g)) a ∈
        map (algebraMap Γ(X, V.1) Γ(X, bOpn X g)) ((Z.ideal V) ^ m) := by
      rw [m219, hZ]
      exact hgle $ (I.map_ideal_basicOpen V g) ▸ mem_map_of_mem _ ha
    rw [mem_map_algebraMap_iff $ powers g] at hmem
    obtain ⟨⟨bb, sm⟩, heq⟩ := hmem
    rw [← map_mul] at heq
    obtain ⟨tm, hct⟩ := mp_ (eq_iff_exists (powers g)
      Γ(X, bOpn X g)) heq
    have hmemB : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a ∈ (Z.ideal V) ^ m := by
      have h3 : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a
          = (tm : Γ(X, V.1)) * (a * (sm : Γ(X, V.1))) := by ring
      rw [h3, hct]
      exact mul_mem_left _ _ bb.2
    have hcolmem : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) ∈
        ((Z.ideal V) ^ m).colon (span {a}) := by
      refine mpr_ mem_colon ?_
      intro q hq
      obtain ⟨cc, rfl⟩ := mp_ mem_span_singleton' hq
      have h4 : ((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) • (cc * a)
          = cc * (((tm : Γ(X, V.1)) * (sm : Γ(X, V.1))) * a) := by
        rw [smul_eq_mul]
        ring
      rw [h4]
      exact mul_mem_left _ _ hmemB
    obtain ⟨i, hi⟩ := tm.2
    obtain ⟨j, hj⟩ := sm.2
    have hts : (tm : Γ(X, V.1)) * (sm : Γ(X, V.1)) = g ^ (i + j) := by
      rw [← hi, ← hj, pow_add]
    exact hgP $ hP.isPrime.mem_of_pow_mem _ $ hts ▸ hPle hcolmem
  exact key

section
variable {k : Type} [Field k]
theorem isRadical_ideal_of_restrictIdeal_eq_coordIdeal
    (p : X ⟶ Sp k) {U : Opn X} (hU : IsAffineOpen U) {n : ℕ}
    (c : EtaleChart p U n) (Z : ISD X) (S : FinSet n)
    (h : restrictIdeal Z U = c.coordIdeal S) :
    (Z.ideal ⟨U, hU⟩).IsRadical := by
  let _a0 := Z.ideal ⟨U, hU⟩
  let _c0 := U.sec ⧸ _a0
  classical
  have hg := etale_quotientMk_comp_renameCompl k n S c.coordRingHom (c.coordRingHom_etale hU)
    _a0 (c.map_mvPolynomialCoordIdeal_eq_ideal hU Z S h).symm
  let _ :=
    toAlgebra
      (((mk _a0).comp c.coordRingHom).comp (renameCompl k n S).toRingHom)
  have : m121 (CoordPolynomialRing k $ n - S.card) _c0 := hg
  refine mpr_ (isRadical_iff_quotient_reduced _) ?_
  refine isReduced_ofLocalizationMaximal _ ?_
  intro q hq
  have : q.IsPrime := hq.isPrime
  have := isRegularLocalRing_localization_atPrime_etale k (n - S.card)
    _c0 q
  have : IsDomain $ AtPrime q := inferInstance
  exact ⟨fun x hx => hx.eq_zero⟩

section
variable [hv3_0 : CharZero k] (p : X ⟶ Sp k) [Smooth p]
include hv3_0
theorem ideal_le_pow_of_restrictIdeal_eq_coordIdeal {U : Opn X}
    (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n) (Z : ISD X)
    (S : FinSet n) (h : restrictIdeal Z U = c.coordIdeal S) (m : ℕ)
    (I : ISD X)
    (hord : ∀ x : X, x ∈ Z.support → x ∈ U → x ∈ orderAtLeastLocus I m) :
    I.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ ^ m := by
  classical
  rcases m73 m with hm0 | hm
  subst hm0
  rw [pow_zero, one_eq_top]
  exact le_top
  let algR := sectionsAlgebra k p U
  let algP := c.algebra
  have htower := c.isScalarTower
  have hfet :=
    c.algebra_formallyEtale hU
  let xs : {i : Fin n // i ∈ S} → X.sec U := fun i => c.coord i.1
  let Ds : {i : Fin n // i ∈ S} → Derivation k U.sec U.sec :=
    fun i => p27 k (UFin n) U.sec $ up i.1
  have hD : ∀ i j : {i : Fin n // i ∈ S}, Ds i (xs j) = if i = j then 1 else 0 := by
    intro i j
    show (p27 k (UFin n) U.sec $ up i.1)
        (c.coord j.1) = if i = j then 1 else 0
    rw [← c.etaleCoordinates_coord j.1, partialDeriv_coord]
    have hiff : (up i.1 = up j.1) ↔ i = j := by
      constructor
      intro hh
      exact m26 $ congrArg down hh
      intro hh
      rw [hh]
    by_cases hij : i = j
    rw [if_pos $ mpr_ hiff hij, if_pos hij]
    rw [if_neg fun hh => hij $ mp_ hiff hh, if_neg hij]
  have hrange : range xs = c.coord '' (S : Set $ Fin n) := by
    ext y
    constructor
    rintro ⟨i, rfl⟩
    exact ⟨i.1, i.2, rfl⟩
    rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hspan : span (range xs) = Z.ideal ⟨U, hU⟩ := by
    rw [hrange, c.ideal_eq_span_coord hU Z S h]
  have hunit : ∀ r : ℕ, 1 ≤ r → IsUnit (r : X.sec U) := by
    intro r hr
    let R := X.sec U
    have h0 : (r : k) ≠ 0 := mpr_ cast_ne_zero $ by omega
    let _a6 := algebraMap k R
    have h1 := sy_ $ map_natCast _a6 r
    rw [h1]
    exact IsUnit.map _a6 $ IsUnit.mk0 (r : k) h0
  let _a1 := I.ideal ⟨U, hU⟩
  let _a4 := derivIdealIterate k (m - 1) _a1
  have hbase : _a4 ≤ Z.ideal ⟨U, hU⟩ := by
    let _m0 := derivIdealSheafIterate k p (m - 1) I
    have h1 : _m0.ideal ⟨U, hU⟩ ≤ Z.ideal ⟨U, hU⟩ := by
      refine ideal_le_of_support_subset hU Z _m0
        (isRadical_ideal_of_restrictIdeal_eq_coordIdeal p hU c Z S h) ?_
      intro y hy hyU
      have h2 :=
        support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
      have h3 := hord y hy hyU
      rwa [← h2] at h3
    calc _a4
        = _m0.ideal ⟨U, hU⟩ :=
          (derivIdealSheafIterate_ideal k p (m - 1) I ⟨U, hU⟩).symm
      _ ≤ Z.ideal ⟨U, hU⟩ := h1
  have key : ∀ j, 1 ≤ j → j ≤ m →
      derivIdealIterate k (m - j) _a1 ≤ Z.ideal ⟨U, hU⟩ ^ j := by
    intro j
    induction j with
    | zero => intro hj; exact absurd hj $ by omega
    | succ j ih =>
      intro _ hjm
      rcases m73 j with hj0 | hj0
      subst hj0
      simpa using hbase
      intro f hf
      have hmem1 :=
        derivIdealIterate_le_of_le k (show m - (j + 1) ≤ m - j by omega) _ hf
      have hfW := ih hj0 (by omega) hmem1
      have hdf : ∀ i : {i : Fin n // i ∈ S}, (Ds i) f ∈ Z.ideal ⟨U, hU⟩ ^ j := by
        intro i
        refine ih hj0 (by omega) ?_
        have h4 :=
          derivation_apply_mem_derivIdeal k _ (Ds i) hf
        rw [← derivIdealIterate_succ] at h4
        exact derivIdealIterate_le_of_le k (show m - (j + 1) + 1 ≤ m - j by omega) _ h4
      have hf' : f ∈ span (range xs) ^ j := by rw [hspan]; exact hfW
      have hdf' : ∀ i : {i : Fin n // i ∈ S}, (Ds i) f ∈ span (range xs) ^ j := by
        intro i
        rw [hspan]
        exact hdf i
      have hres := mem_pow_succ_of_deriv_mem_pow k xs Ds hD (hunit j hj0) hf' hdf'
      rwa [hspan] at hres
  have hfin := key m hm le_rfl
  rwa [Nat.sub_self, derivIdealIterate_zero] at hfin

theorem le_pow_of_support_subset_orderAtLeastLocus_of_coordIdeal (Z I : ISD X)
    m
    (hchart : ∀ x : X, x ∈ support Z →
      ∃ (U : Opn X) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n) (S : FinSet n),
        restrictIdeal Z U = c.coordIdeal S)
    (hord : (support Z : Set X) ⊆ orderAtLeastLocus I m) :
    I ≤ Z ^ m := by
  refine le_pow_of_forall_le_pow_basicOpen Z I m ?_
  intro V x hx
  by_cases hxZ : x ∈ spI Z
  obtain ⟨U, hxU, n, c, S, hS⟩ := hchart x hxZ
  obtain ⟨g, hgU, hxg⟩ := V.2.exists_basicOpen_le (⟨x, hxU⟩ : U) hx
  refine ⟨g, hxg, ?_⟩
  exact ideal_le_pow_of_restrictIdeal_eq_coordIdeal p (V.2.basicOpen g) (c.restrict hgU) Z S (restrictIdeal_eq_restrict_coordIdeal_of_le hgU c Z S hS) m I
    (fun y hy _ => hord hy)
  have hOmopen := Z.support.2.isOpen_compl
  obtain ⟨g, hgOm, hxg⟩ :=
    V.2.exists_basicOpen_le (⟨x, hxZ⟩ : (⟨Z.supportᶜ, hOmopen⟩ : Opn X)) hx
  refine ⟨g, hxg, ?_⟩
  have htop := by
    refine ideal_eq_top_of_disjoint_support Z (X.affineBasicOpen g) ?_
    intro y hy
    exact hgOm hy
  rw [htop, ← one_eq_top, one_pow, one_eq_top]
  exact le_top

theorem le_pow_of_hasStrictNormalCrossingsWith (Z I : ISD X)
    E (hE : HasStrictNormalCrossingsWith p Z E) m
    (hord : (support Z : Set X) ⊆ orderAtLeastLocus I m) :
    I ≤ Z ^ m := by
  refine le_pow_of_support_subset_orderAtLeastLocus_of_coordIdeal p Z I m ?_ hord
  unfold HasStrictNormalCrossingsWith at hE
  intro x hx
  obtain ⟨U, hxU, n, c, _, S, _, _, _, hZ⟩ := hE x hx
  exact ⟨U, hxU, n, c, S, hZ⟩
end
end
end

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

theorem isPreirreducible_of_isPreirreducible_image_val {al_ : Type} [TopologicalSpace al_] {s : Set al_}
    {T : Set s} (h : IsPreirreducible $ val '' T) : IsPreirreducible T := by
  intro u v hu hv hTu hTv
  obtain ⟨u', hu', rfl⟩ := mp_ isOpen_induced_iff hu
  obtain ⟨v', hv', rfl⟩ := mp_ isOpen_induced_iff hv
  obtain ⟨a, haT, hau⟩ := hTu
  obtain ⟨b, hbT, hbv⟩ := hTv
  obtain ⟨w, ⟨t, htT, rfl⟩, hwu, hwv⟩ :=
    h u' v' hu' hv' ⟨a, ⟨a, haT, rfl⟩, hau⟩ ⟨b, ⟨b, hbT, rfl⟩, hbv⟩
  exact ⟨t, htT, hwu, hwv⟩

section
variable {X : Sch}
theorem exists_fromSpec_mem_and_primeIdealOf_eq {V : Opn X} (hV : IsAffineOpen V)
    (P : PrimeSpectrum $ X.sec V) :
    ∃ hz : hV.fromSpec.base P ∈ V, hV.primeIdealOf ⟨hV.fromSpec.base P, hz⟩ = P := by
  have hz : hV.fromSpec.base P ∈ V := by
    have h : hV.fromSpec.base P ∈ range hV.fromSpec.base := ⟨P, rfl⟩
    rwa [hV.range_fromSpec] at h
  refine ⟨hz, hV.fromSpec.isOpenEmbedding.injective ?_⟩
  rw [hV.fromSpec_primeIdealOf]

private theorem mem_support_iff_ideal_le_primeIdealOf (I : ISD X)
    {V} (hV : IsAffineOpen V) {x} (hx : x ∈ V) :
    x ∈ support I ↔ I.ideal ⟨V, hV⟩ ≤ asIdeal (hV.primeIdealOf ⟨x, hx⟩) := by
  let _ :=
    toAlgebra (pGerm X V x hx).hom
  have :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hcomap := by
    have h := under_maximalIdeal (R := V.sec)
      (S := stkX X x) (I := asIdeal $ hV.primeIdealOf ⟨x, hx⟩)
    exact h
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I x ⟨V, hV⟩ hx,
    map_le_iff_le_comap]
  exact iff_of_eq $ congrArg (fun J => I.ideal ⟨V, hV⟩ ≤ J) hcomap

theorem vanishingIdeal_ideal_le_primeIdealOf (Z : Closeds ↥X)
    {V : Opn X} (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) (hxZ : x ∈ (Z : Set ↥X)) :
    (vanishingIdeal Z).ideal ⟨V, hV⟩
      ≤ asIdeal (hV.primeIdealOf ⟨x, hx⟩) := by
  have heq : (vanishingIdeal Z).ideal ⟨V, hV⟩
      = m184 (preimage hV.fromSpec.base Z) := rfl
  intro f hf
  rw [heq, mem_vanishingIdeal] at hf
  let _a0 := hV.primeIdealOf ⟨x, hx⟩
  refine hf _a0 ?_
  have := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  show hV.fromSpec.base _a0 ∈ Z
  rwa [this]

theorem le_vanishingIdeal_of_subset_support (I : ISD X)
    (Z : Closeds ↥X) (h : (Z : Set ↥X) ⊆ (support I : Set ↥X)) :
    I ≤ vanishingIdeal Z := by
  have key : ∀ U : affO X,
      I.ideal U ≤ (vanishingIdeal Z).ideal U := by
    intro U f hf
    have heq : (vanishingIdeal Z).ideal U
        = m184 (pIm U.2.fromSpec.base Z) := rfl
    rw [heq, mem_vanishingIdeal]
    intro P hP
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq U.2 P
    have hzs : U.2.fromSpec.base P ∈ spI I := h hP
    rw [mem_support_iff_ideal_le_primeIdealOf I U.2 hz, hzP] at hzs
    exact hzs hf
  exact key
end

structure IsIrreducibleComponentOfSupport {X : Sch} (D : ISD X) (C : Set X) : Prop where
  isIrreducible : IsIrreducible C
  maximal : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (support D : Set X) → C' = C
  subset_support : C ⊆ (support D : Set X)

namespace IsIrreducibleComponentOfSupport

variable {X : Sch} {D : ISD X} {C : Set X}

section
variable (hC : IsIrreducibleComponentOfSupport D C)
include hC
theorem isClosed : IsClosed C :=
  isClosed_of_maximal_irreducible_subset_support D hC.isIrreducible hC.subset_support hC.maximal

theorem closure_genericPoint :
    closure {hC.isIrreducible.genericPoint} = C :=
  hC.isIrreducible.isGenericPoint_genericPoint hC.isClosed

theorem genericPoint_mem :
    hC.isIrreducible.genericPoint ∈ C := by
  have h : hC.isIrreducible.genericPoint ∈ closure {hC.isIrreducible.genericPoint} :=
    subset_closure $ mem_singleton _
  rwa [hC.closure_genericPoint] at h

theorem genericPoint_specializes {x} (hx : x ∈ C) :
    hC.isIrreducible.genericPoint ⤳ x := by
  refine mpr_ specializes_iff_mem_closure ?_
  rwa [hC.closure_genericPoint]

theorem genericPoint_mem_support :
    hC.isIrreducible.genericPoint ∈ (support D : Set X) :=
  hC.subset_support hC.genericPoint_mem
end

end IsIrreducibleComponentOfSupport

section
variable {X : Sch}
theorem exists_isIrreducibleComponentOfSupport (D : ISD X) x
    (hx : x ∈ (support D : Set X)) :
    ∃ C, IsIrreducibleComponentOfSupport D C ∧ x ∈ C := by
  let _a0 := spI D
  have hchain : ∀ c ⊆ {t : Set X | IsIrreducible t ∧ t ⊆ _a0},
      IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {t : Set X | IsIrreducible t ∧ t ⊆ _a0}, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hch hne
    refine ⟨⋃₀ c, ⟨⟨?_, ?_⟩, sUnion_subset fun t ht => an2 $ hcS ht⟩, fun s hs => subset_sUnion_of_mem hs⟩
    obtain ⟨t, ht⟩ := hne
    obtain ⟨y, hy⟩ := (hcS ht).1.nonempty
    exact ⟨y, t, ht, hy⟩
    rintro u v hu hv ⟨y, ⟨q, hq, hyq⟩, hyu⟩ ⟨z, ⟨r, hr, hzr⟩, hzv⟩
    rcases hch.total hq hr with h | h
    obtain ⟨w, hw, hwuv⟩ := (hcS hr).1.2 u v hu hv ⟨y, h hyq, hyu⟩ ⟨z, hzr, hzv⟩
    exact ⟨w, ⟨r, hr, hw⟩, hwuv⟩
    obtain ⟨w, hw, hwuv⟩ := (hcS hq).1.2 u v hu hv ⟨y, hyq, hyu⟩ ⟨z, h hzr, hzv⟩
    exact ⟨w, ⟨q, hq, hw⟩, hwuv⟩
  obtain ⟨m, hxm, hm⟩ := zorn_subset_nonempty
    {t : Set X | IsIrreducible t ∧ t ⊆ _a0} hchain {x}
    ⟨isIrreducible_singleton, mpr_ singleton_subset_iff hx⟩
  exact ⟨m, ⟨hm.1.1, fun C' hC' hmC' hC'S =>
    m15 (an2 hm ⟨hC', hC'S⟩ hmC') hmC', hm.1.2⟩, hxm rfl⟩

theorem finite_isIrreducibleComponentOfSupport [TopologicalSpace.NoetherianSpace ↥X]
    (D : ISD X) :
    {C : Set X | IsIrreducibleComponentOfSupport D C}.Finite := by
  let _a0 := (spI D : Set X)
  have himg : ∀ C ∈ {C : Set X | IsIrreducibleComponentOfSupport D C},
      (preimage val C) ∈
        irreducibleComponents _a0 := by
    intro C hC
    have hCsub := hC.subset_support
    have himgC :
        (val '' (preimage val C : Set _a0) : Set X) = C :=
      image_preimage_eq_of_subset (by rw [range_coe]; exact hCsub)
    have hirr : IsIrreducible (preimage val C : Set _a0) := by
      obtain ⟨y, hy⟩ := hC.isIrreducible.nonempty
      refine ⟨⟨⟨y, hCsub hy⟩, hy⟩, ?_⟩
      apply isPreirreducible_of_isPreirreducible_image_val
      rw [himgC]
      exact hC.isIrreducible.2
    refine ⟨hirr, ?_⟩
    intro T' hT' hle
    have h1 :=
      hT'.image _ continuous_subtype_val.continuousOn
    let _a1 := val '' T'
    have h2 : _a1 ⊆ _a0 := by
      rintro _ ⟨t, _, rfl⟩
      exact t.2
    have h3 : C ⊆ _a1 := by
      rw [← himgC]
      exact image_mono hle
    intro t ht
    rw [← hC.maximal _ h1 h3 h2]
    exact ⟨t, ht, rfl⟩
  have hsub : (fun C => preimage val C) ''
      {C : Set X | IsIrreducibleComponentOfSupport D C} ⊆ irreducibleComponents _a0 := by
    rintro _ ⟨C, hC, rfl⟩
    exact himg C hC
  refine of_finite_image (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset hsub) ?_
  intro C1 h1 C2 h2 heq
  have e1 :
      (val '' (preimage val C1 : Set _a0) : Set X) = C1 :=
    image_preimage_eq_of_subset (by rw [range_coe]; exact h1.subset_support)
  have e2 :
      (val '' (preimage val C2 : Set _a0) : Set X) = C2 :=
    image_preimage_eq_of_subset (by rw [range_coe]; exact h2.subset_support)
  rw [← e1, ← e2]
  exact congrArg (image val) heq

theorem stalkIdeal_ne_bot_of_nonzeroOnComponents (I : ISD X)
    (hI : NonzeroOnComponents I) x : stalkIdeal I x ≠ ⊥ := by
  intro hbot
  rw [nonzeroOnComponents_iff] at hI
  refine hI (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x) ?_
  have hTirr : IsIrreducible $ irreducibleComponent x := isIrreducible_irreducibleComponent
  have hgen :=
    hTirr.isGenericPoint_genericPoint isClosed_irreducibleComponent
  have hspec : hTirr.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, hgen]
    exact mem_irreducibleComponent
  obtain ⟨V, hxV⟩ := exists_affineOpens_mem x
  have hetaV := hspec.mem_open (V : Opn X).isOpen hxV
  have hmapeq : hom (pGerm X (V : Opn X) hTirr.genericPoint hetaV)
      = (hom $ X.presheaf.stalkSpecializes hspec).comp
        (hom $ pGerm X V x hxV) := by
    rw [← hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have hetabot : stalkIdeal I hTirr.genericPoint = ⊥ := by
    rw [stalkIdeal_eq_map_germ I hTirr.genericPoint V hetaV, hmapeq, ← map_map,
      ← stalkIdeal_eq_map_germ I x V hxV, hbot, Ideal.map_bot]
  let _a0 := (⊥ : Ideal $ stkX X hTirr.genericPoint)
  have hbt : _a0 ≠ ⊤ := by
    intro h
    have h1 : (1 : (stkX X hTirr.genericPoint)) ∈
        _a0 := by
      rw [h]
      exact mem_top
    rw [mem_bot] at h1
    exact one_ne_zero h1
  have hmem :=
    mpr (mem_support_iff_stalkIdeal_ne_top I _) (by rw [hetabot]; exact hbt)
  let _a1 := spI I
  calc irreducibleComponent x = closure {hTirr.genericPoint} := sy_ hgen
    _ ⊆ closure _a1 :=
        closure_mono $ mpr_ singleton_subset_iff hmem
    _ = _a1 := I.support.isClosed.closure_eq

theorem orderAt_ne_top_of_nonzeroOnComponents [IsLocallyNoetherian X]
    (I : ISD X) (hI : NonzeroOnComponents I) (x : X) : orderAt I x ≠ ⊤ :=
  orderAt_ne_top_of_stalkIdeal_ne_bot I x $ stalkIdeal_ne_bot_of_nonzeroOnComponents I hI x

theorem vanishingIdeal_ideal_eq_of_restrictIdeal_eq_coordIdeal {k : Type} [Field k]
    {p : X ⟶ Sp k} (D : ISD X) {C : Set ↥X} (hCcl : IsClosed C)
    (hCsub : C ⊆ (support D : Set ↥X))
    {W : Opn X} (hW : IsAffineOpen W) {n : ℕ} (c : EtaleChart p W n) (S : FinSet n)
    (hD : restrictIdeal D W = c.coordIdeal S)
    (hWC : ∀ y : ↥X, y ∈ W → y ∈ (support D : Set ↥X) → y ∈ C) :
    (vanishingIdeal (⟨C, hCcl⟩ : Closeds ↥X)).ideal ⟨W, hW⟩
      = D.ideal ⟨W, hW⟩ := by
  refine le_antisymm ?_ $ le_vanishingIdeal_of_subset_support D (⟨C, hCcl⟩ : Closeds X) hCsub ⟨W, hW⟩
  have hJ : D.ideal ⟨W, hW⟩ = sInf {P : Ideal W.sec | D.ideal ⟨W, hW⟩ ≤ P ∧ P.IsPrime} := by
    rw [← radical_eq_sInf, (isRadical_ideal_of_restrictIdeal_eq_coordIdeal p hW c D S hD).radical]
  rw [hJ]
  refine le_sInf ?_
  rintro P ⟨hPle, hPprime⟩
  obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq hW ⟨P, hPprime⟩
  have hzs : hW.fromSpec.base (⟨P, hPprime⟩ : PrimeSpectrum W.sec) ∈ spI D := by
    rwa [mem_support_iff_ideal_le_primeIdealOf D hW hz, hzP]
  have hfinal :=
    vanishingIdeal_ideal_le_primeIdealOf (⟨C, hCcl⟩ : Closeds X) hW hz $ hWC _ hz hzs
  rwa [hzP] at hfinal
end

namespace IsIrreducibleComponentOfSupport

variable {X : Sch} {D : ISD X} {C : Set X}

theorem orderAt_genericPoint_ne_top [IsLocallyNoetherian X] (hC : IsIrreducibleComponentOfSupport D C)
    (I : ISD X) (hI : NonzeroOnComponents I) :
    orderAt I hC.isIrreducible.genericPoint ≠ ⊤ :=
  orderAt_ne_top_of_nonzeroOnComponents I hI hC.isIrreducible.genericPoint

variable {k : Type} [Field k]

theorem disjoint {C' : Set X} (hC : IsIrreducibleComponentOfSupport D C) (hC' : IsIrreducibleComponentOfSupport D C')
    (p : X ⟶ Sp k)
    (hloc : ∀ x : X, ∃ (U : Opn X) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    (hne : C ≠ C') : Disjoint C C' := by
  rw [disjoint_left]
  intro y hyC hyC'
  apply hne
  obtain ⟨V, hV, hyV, hetaV, n, c, j, hD, hspec, hetas, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC.isIrreducible hC.subset_support hC.maximal y hyC
  have hspec' := hC'.genericPoint_specializes hyC'
  have heta'V := hspec'.mem_open V.isOpen hyV
  have hmin' : ∀ P : Ideal V.sec, P.IsPrime → c.coord j ∈ P →
      P ≤ asIdeal (hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩) →
      P = asIdeal (hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩) := by
    intro P hP hcoord hle
    obtain ⟨hz, hzP⟩ := exists_fromSpec_mem_and_primeIdealOf_eq hV ⟨P, hP⟩
    have hzs : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum V.sec) ∈ spI D := by
      rw [mem_support_iff_ideal_le_primeIdealOf D hV hz, hzP, c.ideal_eq_span_coord hV D {j} hD, span_le]
      rintro f ⟨i, hi, rfl⟩
      have hij : i = j := by simpa using hi
      subst hij
      exact hcoord
    have hsp : (⟨P, hP⟩ : PrimeSpectrum V.sec) ⤳
        hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩ := by
      rw [specializes_iff_mem_closure, PrimeSpectrum.closure_singleton,
        mem_zeroLocus]
      exact hle
    have hspz : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum V.sec) ⤳
        hC'.isIrreducible.genericPoint := by
      have hmapped := hsp.map hV.fromSpec.base.hom.continuous
      rwa [hV.fromSpec_primeIdealOf] at hmapped
    have hclo : closure {hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum V.sec)} = C' := by
      refine hC'.maximal _ isIrreducible_singleton.closure ?_ ?_
      have h1 :=
        mpr singleton_subset_iff $ mp_ specializes_iff_mem_closure hspz
      have h2 := closure_mono h1
      rw [closure_closure] at h2
      rwa [← hC'.closure_genericPoint]
      have h3 :=
        closure_mono $ mpr_ singleton_subset_iff hzs
      rwa [D.support.isClosed.closure_eq] at h3
    have hzC' : hV.fromSpec.base (⟨P, hP⟩ : PrimeSpectrum V.sec) ∈ C' := by
      rw [← hclo]
      exact subset_closure $ mem_singleton _
    have hfin : hV.primeIdealOf ⟨hC'.isIrreducible.genericPoint, heta'V⟩
        = (⟨P, hP⟩ : PrimeSpectrum V.sec) := by
      rw [← hzP]
      congr 1
      exact m26 ((hspz.antisymm $ hC'.genericPoint_specializes hzC').eq).symm
    exact sy_ $ congrArg asIdeal hfin
  have e1 := primeIdealOf_eq_comap_span_germ_coord p hV c j D hD y
    hC.isIrreducible.genericPoint hyV hetaV hspec hetas hmin
  have e2 := primeIdealOf_eq_comap_span_germ_coord p hV c j D hD y
    hC'.isIrreducible.genericPoint hyV heta'V hspec' hC'.genericPoint_mem_support hmin'
  have hpts : hC.isIrreducible.genericPoint = hC'.isIrreducible.genericPoint := by
    simpa only [hV.fromSpec_primeIdealOf] using (congrArg hV.fromSpec.base $ m210 $ tr_ e1 e2.symm)
  rw [← hC.closure_genericPoint, ← hC'.closure_genericPoint, hpts]

section
variable [TopologicalSpace.NoetherianSpace ↥X] (hC : IsIrreducibleComponentOfSupport D C) (p : X ⟶ Sp k) (hloc : ∀ x : X, ∃ (U : Opn X) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n), restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}) (x : X) (hx : x ∈ C)
include hloc hx
theorem exists_affineOpen_etaleChart_coordIdeal :
    ∃ (V : Opn X) (hV : IsAffineOpen V) (_ : x ∈ V) (n : ℕ) (c : EtaleChart p V n) (j : Fin n),
      restrictIdeal D V = c.coordIdeal {j} ∧
      (∀ y : X, y ∈ V → y ∈ (support D : Set X) → y ∈ C) ∧
      (vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal ⟨V, hV⟩ = D.ideal ⟨V, hV⟩ ∧
      (∀ W : X.affineOpens, (↑W : Opn X) ≤ V →
        (vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).ideal W = D.ideal W) ∧
      (∀ y : X, y ∈ V →
        stalkIdeal (vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) y = stalkIdeal D y) := by
  let _a1 := vanishingIdeal (⟨C, hC.isClosed⟩ : Closeds X)
  obtain ⟨U, hxU, n, c0_, hU⟩ := hloc x
  let _a3 := suppI D
  have hDUex : ∃ j, restrictIdeal D U = c0_.coordIdeal {j} := by
    rcases hU with h | h
    exact absurd (hC.subset_support hx) $ notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U h x hxU
    exact h
  obtain ⟨j, hDU⟩ := hDUex
  obtain ⟨B, hBclosed, hxB, hBmem⟩ :
      ∃ B, IsClosed B ∧ x ∉ B ∧
        ∀ y, y ∈ _a3 → y ∉ B → y ∈ C := by
    refine ⟨⋃ C'' ∈ {C'' : Set X | IsIrreducibleComponentOfSupport D C''} \ {C}, C'', ?_, ?_, ?_⟩
    refine isClosed_biUnion
      ((finite_isIrreducibleComponentOfSupport D).subset sdiff_subset) ?_
    intro C'' hC''
    exact hC''.1.isClosed
    intro hmem
    obtain ⟨C'', hC''mem, hxC''⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.disjoint_left.mp
      (hC.disjoint hC''mem.1 p hloc fun h => hC''mem.2 h.symm) hx hxC''
    intro y hys hyB
    obtain ⟨C'', hC''comp, hyC''⟩ := exists_isIrreducibleComponentOfSupport D y hys
    by_cases h : C'' = C
    exact h ▸ hyC''
    simp_all
  have hxUB : x ∈ (⟨(U : Set X) ∩ Bᶜ, U.isOpen.inter hBclosed.isOpen_compl⟩ : Opn X) :=
    ⟨hxU, hxB⟩
  obtain ⟨V, hxV, hVle⟩ := exists_affineOpens_mem_le hxUB
  let _a0 := (V : Opn X)
  have hVU : _a0 ≤ U := fun y hy => (hVle hy).1
  have hDV :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c0_ D {j} hDU
  have hVC : ∀ y, y ∈ _a0 → y ∈ _a3 → y ∈ C :=
    fun y hy hys => hBmem y hys $ (fun y hy => (hVle hy).2) y hy
  have key : ∀ W : affO X, (W : Opn X) ≤ _a0 →
      _a1.ideal W = D.ideal W := by
    intro W hWV
    exact vanishingIdeal_ideal_eq_of_restrictIdeal_eq_coordIdeal D hC.isClosed hC.subset_support W.2
      ((c0_.restrict hVU).restrict hWV) {j} (restrictIdeal_eq_restrict_coordIdeal_of_le hWV (c0_.restrict hVU) D {j} hDV)
      (fun y hy hys => hVC y (hWV hy) hys)
  refine ⟨_a0, V.2, hxV, n, c0_.restrict hVU, j, hDV, hVC, key V le_rfl, ?_, ?_⟩
  intro W hWV
  exact key W hWV
  intro y hy
  rw [stalkIdeal_eq_map_germ
      _a1 y V hy,
    stalkIdeal_eq_map_germ D y V hy, key V le_rfl]

theorem stalkIdeal_vanishingIdeal_eq :
    stalkIdeal (vanishingIdeal
      (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) x = stalkIdeal D x := by
  obtain ⟨V, hV, hxV, n, c, j, -, -, -, -, hstalk⟩ := hC.exists_affineOpen_etaleChart_coordIdeal p hloc x hx
  exact hstalk x hxV
end

end IsIrreducibleComponentOfSupport


theorem det_update_eq_repr {K V : Type} [CommRing K] [AddCommGroup V] [Module K V]
    {ι : Type} [Fintype ι] [DecidableEq ι] (e : Basis ι K V) j v :
    e.det (update (⇑e) j v) = e.repr v j := by
  have key : ∀ b : ι → K, (updateCol 1 j b).det = b j := by
    intro b
    have h : (cramer 1) b j
        = (updateCol 1 j b).det := by
      rw [cramer_apply]
    rw [← h]
    simp [cramer_one]
  have hm : e.toMatrix (update (e) j v)
      = updateCol 1 j (e.repr v) := by
    ext i l
    rw [Module.Basis.toMatrix_apply, updateCol_apply, update_apply]
    by_cases hl : l = j
    simp [hl]
    rcases eq_or_ne i l with rfl | hil
    simp_all
    simp_all
  rw [Module.Basis.det_apply, hm]
  exact key _

section
variable {X : Sch}
section
variable {U} (hU : IsAffineOpen U) {x} (hx : x ∈ U)
theorem notMem_basicOpen_of_mem_primeIdealOf f
    (hf : f ∈ asIdeal (hU.primeIdealOf ⟨x, hx⟩)) : x ∉ basicOpen X f := by
  intro hmem
  let _a0 := hU.primeIdealOf ⟨x, hx⟩
  have h2 : _a0 ∈ hU.fromSpec ⁻¹ᵁ bOpn X f := by
    show hU.fromSpec.base _a0 ∈ bOpn X f
    rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩]
  rw [hU.fromSpec_preimage_basicOpen] at h2
  exact mp_ (m209 f _) h2 hf

theorem map_germ_primeIdealOf_eq_maximalIdeal :
    map (X.presheaf.germ U x hx).hom (hU.primeIdealOf ⟨x, hx⟩).asIdeal =
      maximalIdeal (X.presheaf.stalk x) := by
  let instAlgStalk :=
    (pGerm X U x hx).hom.toAlgebra
  have instLocStalk := hU.isLocalization_stalk ⟨x, hx⟩
  exact map_eq_maximalIdeal (hU.primeIdealOf ⟨x, hx⟩).asIdeal $ stkX X x
end

section
variable {k : Type} [Field k]
section
variable {p : X ⟶ Sp k} {U : Opn X}
theorem ideal_eq_span_coord_of_restrictIdeal_eq (hU : IsAffineOpen U) {m}
    (c : EtaleChart p U m) (I : ISD X) j
    (h : restrictIdeal I U = c.coordIdeal {j}) :
    I.ideal ⟨U, hU⟩ = span ({c.coord j} : Set $ X.sec U) := by
  rw [c.ideal_eq_span_coord hU I {j} h, coe_singleton, image_singleton]

section
variable {m} (c : EtaleChart p U m)
theorem basisKaehler_apply_eq_D_coord
    [Algebra k $ X.sec U] [Algebra (MvU m k) $ X.sec U]
    [IsScalarTower k (MvU m k) $ X.sec U]
    [FormallyEtale (MvU m k) $ X.sec U]
    (_hk : algebraMap k (X.sec U) = sectionsAlgebraMap k p U)
    (hc : algebraMap (MvU m k) (X.sec U) = c.coordRingHom)
    j :
    basisKaehler k (UFin m) (X.sec U) (up j) =
      KaehlerDifferential.D k (X.sec U) (c.coord j) := by
  rw [basisKaehler_apply, EtaleCoordinates.coord_def, hc,
    coordRingHom_X]

def IsCoordLabeling (lab : ℕ → Option (Fin m))
    (N : Bdy X) : Prop :=
  ∀ i : ℕ, ∀ hi : i < length N,
    (lab i = none → restrictIdeal (N[i]'hi) U = ⊤) ∧
    (∀ j : Fin m, lab i = some j → restrictIdeal (N[i]'hi) U = c.coordIdeal {j})
end
end

theorem ringHom_etale_of_formallyEtale
    p [Smooth p] {V}
    (hV : IsAffineOpen V) {m}
    (f : MvU m k →+* (X.sec V))
    (hC : ∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p V a)
    (hf : @FormallyEtale (MvU m k) (X.sec V) _ _
      f.toAlgebra) :
    f.Etale := by
  let _s0 := MvU m k
  let instP := f.toAlgebra
  let instk := sectionsAlgebra k p V
  have hk :=
    algebraMap_sectionsAlgebra k p V
  have h1 : (algebraMap _s0 V.sec) = f := rfl
  have instTower : IsScalarTower k _s0 V.sec := by
    refine of_algebraMap_eq fun a => ?_
    rw [hk, h1, algebraMap_eq, hC]
  have instFiniteType := finiteType_sections k p ⟨V, hV⟩ hk
  have hFTp : FiniteType _s0 V.sec := by
    obtain ⟨t, ht⟩ := instFiniteType.out
    refine ⟨⟨t, ?_⟩⟩
    rw [Algebra.eq_top_iff]
    intro x
    let _s1 := (t : Set V.sec)
    have hx : x ∈ adjoin k _s1 := by
      rw [ht]
      exact Algebra.mem_top
    have hle : adjoin k _s1 ≤
        Subalgebra.restrictScalars k
          (adjoin _s0 _s1) :=
      adjoin_le subset_adjoin
    exact hle hx
  have hFP := hFTp
  rw [Algebra.FinitePresentation.of_finiteType] at hFP
  exact ⟨hf, hFP⟩
end

theorem mem_support_of_ideal_le_primeIdealOf (D : ISD X) {U}
    (hU : IsAffineOpen U) {x} (hx : x ∈ U)
    (h : D.ideal ⟨U, hU⟩ ≤ asIdeal (hU.primeIdealOf ⟨x, hx⟩)) : x ∈ D.support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ D x ⟨U, hU⟩ hx]
  exact le_trans (map_mono h) $ le_of_eq $ map_germ_primeIdealOf_eq_maximalIdeal hU hx
end

section
variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (y : ι → R) (S : Finset ι)
theorem span_image_update_sum_eq (a : ι → R) (j : ι) (hj : j ∈ S) (ha : IsUnit (a j)) :
    span (update y j (∑ i ∈ S, a i * y i) '' (S : Set ι)) =
      span (y '' (S : Set ι)) := by
  have hzj : update y j (∑ t ∈ S, a t * y t) j = ∑ t ∈ S, a t * y t := by
    simp
  have hzne : ∀ i, i ≠ j →
      update y j (∑ t ∈ S, a t * y t) i = y i := by simp_all
  have key1 : ∀ i ∈ S, update y j (∑ t ∈ S, a t * y t) i
      ∈ span (imS y S) := by
    intro i hi
    by_cases h : i = j
    rw [h, hzj]
    exact sum_mem _ fun t ht =>
      mul_mem_left _ _
        (subset_span $ mem_image_of_mem y $ mpr_ mem_coe ht)
    rw [hzne i h]
    exact subset_span $ mem_image_of_mem y $ mpr_ mem_coe hi
  let _a0 := span $ update y j (∑ t ∈ S, a t * y t) '' S
  have hmemj : a j * y j ∈
      _a0 := by
    have h1 : a j * y j
        = update y j (∑ t ∈ S, a t * y t) j - ∑ t ∈ S.erase j, a t * y t := by
      rw [hzj, (add_sum_erase S (fun t => a t * y t) hj).symm]
      ring
    rw [h1]
    refine sub_mem _
      (subset_span $ mem_image_of_mem _ $ mpr_ mem_coe hj) ?_
    refine sum_mem _ fun t ht => mul_mem_left _ _ ?_
    rw [← hzne t $ ne_of_mem_erase ht]
    exact subset_span
      (mem_image_of_mem _ $ mpr_ mem_coe $ mem_of_mem_erase ht)
  have key2 : ∀ i ∈ S, y i ∈
      _a0 := by
    intro i hi
    by_cases h : i = j
    obtain ⟨u, hu⟩ := ha
    have hyj : y j = (u⁻¹) * (a j * y j) := by
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
    rw [h, hyj]
    exact mul_mem_left _ _ hmemj
    rw [← hzne i h]
    exact subset_span $ mem_image_of_mem _ $ mpr_ mem_coe hi
  refine le_antisymm (Ideal.span_le.mpr ?_) $ Ideal.span_le.mpr ?_
  rintro _ ⟨i, hi, rfl⟩
  exact SetLike.mem_coe.mpr $ key1 i $ mp_ mem_coe hi
  rintro _ ⟨i, hi, rfl⟩
  exact SetLike.mem_coe.mpr $ key2 i $ mp_ mem_coe hi

theorem exists_coeffs_of_mem_span_image (z : R)
    (hz : z ∈ span (y '' (S : Set ι))) :
    ∃ a : ι → R, z = ∑ j ∈ S, a j * y j := by
  classical
  have hle : span (imS y S) ≤
      ({ carrier := {w : R | ∃ a : ι → R, w = ∑ j ∈ S, a j * y j}
         add_mem' := by
           rintro u v ⟨au, rfl⟩ ⟨av, rfl⟩
           refine ⟨fun i => au i + av i, ?_⟩
           rw [← sum_add_distrib]
           exact sum_congr rfl fun i _ => by ring
         zero_mem' := ⟨0, by simp⟩
         smul_mem' := by
           rintro r u ⟨au, rfl⟩
           refine ⟨fun i => r * au i, ?_⟩
           rw [smul_eq_mul, mul_sum]
           exact sum_congr rfl fun i _ => by ring } : Ideal R) := by
    rw [span_le]
    rintro w ⟨j, hj, rfl⟩
    refine ⟨fun i => if i = j then 1 else 0, ?_⟩
    rw [sum_eq_single_of_mem j $ mp_ mem_coe hj]
    simp
    simp_all
  exact hle hz
end

theorem exists_coord_eq_sum_coeff_not_mem_of_le {X : Sch} {k : Type} [Field k]
    (p : X ⟶ Sp k) [Smooth p] {U : Opn X}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {m : ℕ} (c : EtaleChart p U m)
    (lab : ℕ → Option (Fin m)) (S : FinSet m) {m' : ℕ} (c' : EtaleChart p U m')
    (j0 : Fin m') (lab' : ℕ → Option (Fin m')) (Z H : ISD X)
    (N : Bdy X)
    (hxZ : x ∈ support Z)
    (hlab : IsCoordLabeling c lab N)
    (hZU : restrictIdeal Z U = c.coordIdeal S)
    (hHU : restrictIdeal H U = c'.coordIdeal {j0})
    (hlab' : IsCoordLabeling c' (fun i => lab' (i + 1)) N)
    (hj0 : ∀ i : ℕ, i < length N → lab' (i + 1) ≠ some j0)
    (hHZ : H ≤ Z) :
    ∃ a : Fin m → (X.sec U),
      c'.coord j0 = ∑ j ∈ S, a j * c.coord j ∧
      ∃ j ∈ S, a j ∉ asIdeal (hU.primeIdealOf ⟨x, hx⟩) ∧
        ∀ i : ℕ, i < length N → lab i ≠ some j := by
  let _c0 := hU.primeIdealOf ⟨x, hx⟩
  let _c1 := UFin m'
  classical
  let instAlgBase := sectionsAlgebra k p U
  let instAlgPoly := c'.algebra
  have instTower :=
    c'.isScalarTower
  have instFormallyEtale :=
    c'.algebra_formallyEtale hU
  obtain ⟨D, hD1, hD0⟩ : ∃ D : Derivation k U.sec U.sec,
      D (c'.coord j0) = 1 ∧ ∀ t, t ≠ j0 → D (c'.coord t) = 0 := by
    refine ⟨p27 k _c1 U.sec (up j0), ?_, ?_⟩
    rw [← c'.etaleCoordinates_coord j0]
    exact partialDeriv_coord_self k _c1 U.sec
      (up j0)
    intro t ht
    rw [← c'.etaleCoordinates_coord t]
    exact partialDeriv_coord_of_ne k _c1 U.sec
      (up j0) (up t) fun hcon => ht (congrArg down hcon).symm
  have hZideal :=
    c.ideal_eq_span_coord hU Z S hZU
  have hcP : ∀ j ∈ S, c.coord j ∈ asIdeal _c0 := by
    intro j hj
    refine (ideal_le_primeIdealOf Z hU hx hxZ) ?_
    rw [hZideal]
    exact subset_span ⟨j, mpr_ mem_coe hj, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin m → X.sec U, c'.coord j0 = ∑ j ∈ S, a j * c.coord j := by
    refine exists_coeffs_of_mem_span_image c.coord S (c'.coord j0) ?_
    rw [← hZideal]
    refine hHZ ⟨U, hU⟩ ?_
    rw [ideal_eq_span_coord_of_restrictIdeal_eq hU c' H j0 hHU]
    exact subset_span rfl
  refine ⟨a, ha, ?_⟩
  by_cases hex : ∃ j ∈ S, a j ∉ asIdeal _c0 ∧
      ∀ i, i < lenL N → lab i ≠ some j
  exact hex
  exfalso
  have hlabelMem : ∀ j ∈ S, ∀ i, i < lenL N → lab i = some j →
      D (c.coord j) ∈ asIdeal _c0 := by
    intro j hjS i hi hli
    obtain ⟨-, hsome⟩ := hlab i hi
    have hNideal :=
      ideal_eq_span_coord_of_restrictIdeal_eq hU c (N[i]'hi) j (hsome j hli)
    have hNle : (N[i]'hi).ideal ⟨U, hU⟩ ≤ asIdeal _c0 := by
      rw [hNideal, span_le, singleton_subset_iff]
      exact hcP j hjS
    obtain ⟨hnone', hsome'⟩ := hlab' i hi
    cases hlv : lab' (i + 1) with
    | none =>
        exact absurd (mem_support_of_ideal_le_primeIdealOf (N[i]'hi) hU hx hNle)
          (notMem_support_of_mem_opens_of_restrictIdeal_eq_top (N[i]'hi) U (hnone' hlv) x hx)
    | some t =>
        have htj0 := fun hcon =>
          hj0 i hi (tr_ hlv (congrArg Option.some hcon))
        have hNideal' :=
          ideal_eq_span_coord_of_restrictIdeal_eq hU c' (N[i]'hi) t (hsome' t hlv)
        have hct : c'.coord t ∈ asIdeal _c0 := by
          refine hNle ?_
          rw [hNideal']
          exact subset_span rfl
        have hmem : c.coord j ∈ span ({c'.coord t} : Set U.sec) := by
          rw [← hNideal', hNideal]
          exact subset_span rfl
        obtain ⟨v, hv⟩ := mp_ mem_span_singleton' hmem
        rw [← hv, leibniz, hD0 t htj0, smul_zero, zero_add, smul_eq_mul]
        exact mul_mem_right _ _ hct
  let _m0 := (1 : X.sec U)
  have hone : _m0 ∈ asIdeal _c0 := by
    have hsum : _m0 = ∑ j ∈ S, (a j * D (c.coord j) + c.coord j * D (a j)) := by
      calc _m0 = D (c'.coord j0) := sy_ hD1
        _ = D (∑ j ∈ S, a j * c.coord j) := by rw [ha]
        _ = ∑ j ∈ S, D (a j * c.coord j) := map_sum D (fun j => a j * c.coord j) S
        _ = ∑ j ∈ S, (a j * D (c.coord j) + c.coord j * D (a j)) := by
            refine sum_congr rfl fun j _ => ?_
            simp [leibniz, smul_eq_mul]
    rw [hsum]
    refine sum_mem _ fun j hj => add_mem ?_ (mul_mem_right _ _ $ hcP j hj)
    by_cases hlj : ∃ i, i < lenL N ∧ lab i = some j
    obtain ⟨i, hi, hli⟩ := hlj
    exact mul_mem_left _ _ $ hlabelMem j hj i hi hli
    have haj : a j ∈ asIdeal _c0 := by
      by_contra hajP
      exact hex ⟨j, hj, hajP, fun i hi hli => hlj ⟨i, hi, hli⟩⟩
    exact mul_mem_right _ _ haj
  exact _c0.isPrime.ne_top $ mpr_ (eq_top_iff_one _) hone

section
variable {X1 : Sch} (V : Opn X1)
theorem eq_of_ideal_map_topIso_inv_eq
    {J1 J2}
    (hJ : map V.topIso.inv.hom J1 = map V.topIso.inv.hom J2) : J1 = J2 := by
  have hid : (V.topIso.hom.hom).comp (V.topIso.inv.hom) = m99 _ := by
    ext x
    exact V.topIso.inv_hom_id_apply x
  have key : ∀ J : Ideal V.sec,
      map V.topIso.hom.hom (map V.topIso.inv.hom J) = J := by
    intro J
    rw [map_map, hid, m167]
  rw [← key J1, hJ, key J2]
end

theorem ideal_eq_span_image_map_of_le {X : Sch} (D : ISD X) {U U' : Opn X}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U' ≤ U) s
    (hs : D.ideal ⟨U, hU⟩ = span s) :
    D.ideal ⟨U', hU'⟩ = span ((X.presheaf.map (homOfLE h).op).hom '' s) := by
  have hU'aff : IsAffine U'.toScheme := hU'
  have htop := isAffineOpen_top U'.toScheme
  let _a0 := (⊤ : Opn $ oSch U')
  have e2 : _a0 ≤ opPre U' U' := by
    intro x _
    exact x.2
  have e1 : _a0 ≤ opPre U' U := by
    intro x _
    exact h x.2
  let _a1 := pMap X (homOfLE h).op
  have happ : U'.ι.appLE U ⊤ e1 = _a1 ≫ U'.ι.appLE U' ⊤ e2 := by
    rw [map_appLE]
  have hmain : D.ideal ⟨U', hU'⟩
      = map _a1.hom (D.ideal ⟨U, hU⟩) := by
    refine eq_of_ideal_map_topIso_inv_eq U' ?_
    have _i49 : U'.ι.appLE U' ⊤ e2 = U'.topIso.inv := by
      simp
      exact presheaf_map_eq_of_parallel ..
    rw [← _i49, ← D.comap_ideal_eq_map_appLE U'.i ⟨U', hU'⟩ ⟨⊤, htop⟩ e2, D.comap_ideal_eq_map_appLE U'.i ⟨U, hU⟩ ⟨⊤, htop⟩ e1, happ, hom_comp,
      ← map_map]
  rw [hmain, hs, map_span]

theorem exists_basis_isUnit_det_of_isLocalization {k : Type} [Field k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {S : Type} [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]
    {S' : Type} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
    (M : Submonoid S) [IsLocalization M S'] (v : ι → S)
    (h : IsUnit $ algebraMap S S'
      ((basisKaehler k ι S).det
        fun i : ι => KaehlerDifferential.D k S $ v i)) :
    ∃ e : Basis ι S' $ KaehlerDifferential k S',
      IsUnit (e.det fun i : ι =>
        KaehlerDifferential.D k S' $ algebraMap S S' $ v i) := by
  let _a0 := MvPolynomial ι k
  let instPS' : Algebra _a0 S' :=
    ((algebraMap S S').comp $ algebraMap _a0 S).toAlgebra
  have instT1 : IsScalarTower _a0 S S' :=
    of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k _a0 S' :=
    of_algebraMap_eq fun x => by
      rw [algebraMap_apply k S S' x,
        algebraMap_apply k _a0 S x]
      rfl
  have instFEloc : FormallyEtale S S' :=
    of_isLocalization (M := M)
  have instFormallyEtale :=
    comp _a0 S S'
  refine ⟨basisKaehler k ι S', ?_⟩
  rwa [← algebraMap_det_basisKaehler k ι S S' v]

theorem exists_etaleChart_update_coord {X : Sch} {k : Type} [Field k]
    (p : X ⟶ Sp k) [Smooth p] {U : Opn X}
    (hU : IsAffineOpen U) {m : ℕ} (c : EtaleChart p U m) {x : X} (hx : x ∈ U)
    (S : FinSet m) (a : Fin m → (X.sec U)) (j : Fin m) (hjS : j ∈ S)
    (hS : ∀ i ∈ S, c.coord i ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
    (haj : a j ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (V : Opn X) (_ : IsAffineOpen V) (hVU : V ≤ U) (_ : x ∈ V) (c' : EtaleChart p V m),
      (∀ i : Fin m, i ≠ j →
          c'.coord i = (X.presheaf.map (homOfLE hVU).op).hom (c.coord i)) ∧
      c'.coord j = (X.presheaf.map (homOfLE hVU).op).hom (∑ i ∈ S, a i * c.coord i) ∧
      IsUnit ((X.presheaf.map (homOfLE hVU).op).hom $ a j) := by
  classical
  let instAlgU := sectionsAlgebra k p U
  let instPolyU := c.algebra
  have instTowerU :=
    c.isScalarTower
  have instFEU :=
    c.algebra_formallyEtale hU
  obtain ⟨v, hvj, hvne⟩ : ∃ v : UFin m → X.sec U,
      v (up j) = ∑ i ∈ S, a i * c.coord i ∧
        ∀ i : UFin m, i ≠ up j → v i = c.coord i.down := by
    refine ⟨update (fun i : UFin m => c.coord i.down) (up j)
      (∑ i ∈ S, a i * c.coord i), ?_, fun i hi => ?_⟩
    simp_all
    simp_all
  let _a4 := algebraMap_sectionsAlgebra k p U
  have hBcoord : ∀ i : UFin m,
      basisKaehler k (UFin m) U.sec i =
        m13 k U.sec (c.coord i.down) := fun i =>
    basisKaehler_apply_eq_D_coord c _a4
      (algebraMap_eq_coordRingHom c) i.down
  let _a1 := basisKaehler k (UFin m) $ X.sec U
  let _a6 := m13 k U.sec
  have hfam : (fun i => _a6 $ v i) =
      update (_a1)
        (up j) (m13 k U.sec (∑ i ∈ S, a i * c.coord i)) := by
    funext i
    by_cases hi : i = up j
    rw [update_apply, if_pos hi, hi, hvj]
    rw [update_apply, if_neg hi, hvne i hi, hBcoord i]
  have hdeteq : _a1.det
        (fun i => _a6 $ v i) =
      p27 k (UFin m) U.sec (up j)
        (∑ i ∈ S, a i * c.coord i) := by
    rw [hfam, det_update_eq_repr, partialDeriv_apply]
  have hDself : p27 k (UFin m) U.sec (up j)
      (c.coord j) = 1 := by
    rw [← c.etaleCoordinates_coord j]
    exact partialDeriv_coord_self k (UFin m) U.sec $ up j
  have hDne : ∀ i, i ≠ j →
      p27 k (UFin m) U.sec (up j)
        (c.coord i) = 0 := by
    intro i hi
    rw [← c.etaleCoordinates_coord i]
    exact partialDeriv_coord_of_ne k (UFin m) U.sec
      (up j) (up i) fun h => hi (congrArg down h).symm
  have hsumeq : p27 k (UFin m) U.sec (up j)
        (∑ i ∈ S, a i * c.coord i) =
      a j + ∑ i ∈ S, c.coord i *
        p27 k (UFin m) U.sec (up j) (a i) := by
    have h3 : ∀ i ∈ S, i ≠ j →
        a i * p27 k (UFin m) U.sec (up j)
          (c.coord i) = 0 := by
      intro i _ hij
      rw [hDne i hij, mul_zero]
    have h1 : p27 k (UFin m) U.sec (up j)
          (∑ i ∈ S, a i * c.coord i) =
        (∑ i ∈ S, a i * p27 k (UFin m) U.sec
          (up j) (c.coord i)) +
          ∑ i ∈ S, c.coord i * p27 k (UFin m) U.sec
            (up j) (a i) := by
      rw [map_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp [leibniz, smul_eq_mul]
    rw [h1, sum_eq_single_of_mem j hjS h3, hDself, mul_one]
  let _a3 := hU.primeIdealOf ⟨x, hx⟩
  have hdetP : _a1.det
      (fun i => _a6 $ v i) ∉
      _a3.asIdeal := by
    rw [hdeteq]
    intro hmem
    refine haj ?_
    have hrw : a j =
        p27 k (UFin m) U.sec (up j)
          (∑ i ∈ S, a i * c.coord i) -
          ∑ i ∈ S, c.coord i * p27 k (UFin m) U.sec
            (up j) (a i) := by
      rw [hsumeq]
      ring
    rw [hrw]
    exact sub_mem _ hmem
      (sum_mem _ fun i hi => mul_mem_right _ _ $ hS i hi)
  obtain ⟨g, hgdef⟩ : ∃ g, g =
      _a1.det
        (fun i => _a6 $ v i) * a j := ⟨_, rfl⟩
  have hgP : g ∉ _a3.asIdeal := by
    rw [hgdef]
    intro hmem
    rcases _a3.isPrime.mem_or_mem hmem with h | h
    exact hdetP h
    exact haj h
  have hVaff := hU.basicOpen g
  have hVU := X.basicOpen_le g
  have hxV := mem_basicOpen_of_notMem_primeIdealOf hU hx g hgP
  let instAlgV := sectionsAlgebra k p $ bOpn X g
  have instLocV :=
    hU.isLocalization_basicOpen g
  let _a2 := algebraMap_sectionsAlgebra k p $ bOpn X g
  have instTowerV :=
    isScalarTower_sections k p U g _a4
      _a2 rfl
  have hgunit :=
    map_units (M := powers g) Γ(X, bOpn X g)
      ⟨g, mem_powers g⟩
  have hmul : algebraMap U.sec Γ(X, bOpn X g) g =
      algebraMap U.sec Γ(X, bOpn X g)
        (_a1.det
          (fun i => _a6 $ v i)) *
        algebraMap U.sec Γ(X, bOpn X g) (a j) := by simp_all
  rw [hmul] at hgunit
  have hdetunit := isUnit_of_mul_isUnit_left hgunit
  have hajunit := isUnit_of_mul_isUnit_right hgunit
  obtain ⟨e, he⟩ := exists_basis_isUnit_det_of_isLocalization (powers g) v hdetunit
  obtain ⟨w, hw⟩ : ∃ w : UFin m → Γ(X, bOpn X g),
      ∀ i, w i = algebraMap U.sec Γ(X, bOpn X g) (v i) :=
    ⟨_, fun _ => rfl⟩
  have he' : IsUnit $ e.det fun i =>
      m13 k Γ(X, bOpn X g) $ w i := by simp_all
  have instFSV :=
    formallySmooth_sections k p (bOpn X g) hVaff
      _a2
  have hformallyEtale := formallyEtale_aeval_of_isUnit_det e w he'
  let _a0 := (aeval w : (MvU m k) →ₐ[k] Γ(X, bOpn X g)).toRingHom
  have hC : ∀ b,
      _a0
        (m8 b) = sectionsAlgebraMap k p (bOpn X g) b := by
    intro b
    have h1 := aeval_C w b
    exact tr_ h1 $ congr_fun _a2 b
  have hXv : ∀ i,
      _a0
        (m7 i) = w i := fun i => aeval_X w i
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p hVaff w
    _a0
    hC hXv $ ringHom_etale_of_formallyEtale p hVaff _a0 hC hformallyEtale
  refine ⟨bOpn X g, hVaff, hVU, hxV, c', ?_, tr_ (tr_ (hc' j) $ hw $ up j) $ congrArg (algebraMap U.sec Γ(X, bOpn X g)) hvj, hajunit⟩
  intro i hi
  exact tr_ (tr_ (hc' i) $ hw $ up i)
    (congrArg (algebraMap U.sec Γ(X, bOpn X g))
      (hvne (up i) fun h => hi $ congrArg down h))

def LabelingInjective {m : ℕ} (lab : ℕ → Option (Fin m)) (n : ℕ) : Prop :=
  ∀ i i' : ℕ, i < n → i' < n → ∀ j : Fin m, lab i = some j → lab i' = some j → i = i'

section
variable {X : Sch} {k : Type} [Field k] (p : X ⟶ Sp k)
theorem exists_etaleCharts_of_inStrictNormalCrossingPosition_cons (Z H : ISD X) (N : Bdy X)
    (hN : InStrictNormalCrossingPosition p (H :: N)) (hZ : HasStrictNormalCrossingsWith p Z N) (hHZ : H ≤ Z)
    (x : X) (hx : x ∈ support Z) :
    ∃ (U : Opn X) (_ : IsAffineOpen U) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m)
      (lab : ℕ → Option (Fin m)) (S : FinSet m) (m' : ℕ) (c' : EtaleChart p U m')
      (j0 : Fin m') (lab' : ℕ → Option (Fin m')),
      restrictIdeal Z U = c.coordIdeal S ∧
      restrictIdeal H U = c'.coordIdeal {j0} ∧
      IsCoordLabeling c lab N ∧
      LabelingInjective lab N.length ∧
      IsCoordLabeling c' (fun i => lab' $ i + 1) N ∧
      (∀ i : ℕ, i < length N → lab' (i + 1) ≠ some j0) := by
  obtain ⟨U1_, hxU1, m1, c1_, a1_, S1_, hinj1, hnone1, hsome1, hZU1⟩ := hZ.exists_etaleChart hx
  obtain ⟨U2_, hxU2, m2, c2_, a2_, hinj2_, hnone2, hsome2⟩ := (an2 (mp_ (inStrictNormalCrossingPosition_iff p (H :: N)) hN) x).exists_etaleChart
  obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := U1_ ⊓ U2_) ⟨hxU1, hxU2⟩
  have hVU1 := le_trans hVW inf_le_left
  have hVU2 := le_trans hVW inf_le_right
  have hlen0 : 0 < lenL (H :: N) := by simp
  obtain ⟨j0, hj0⟩ : ∃ j0, a2_ 0 = some j0 := by
    cases hcase : a2_ 0 with
    | none =>
        exfalso
        have h := hnone2 0 hlen0 hcase
        simp [getElem_cons_zero] at h
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top H U2_ h x hxU2 $ support_antitone hHZ hx
    | some j => exact ⟨j, rfl⟩
  refine ⟨V, hVaff, hxV, m1, c1_.restrict hVU1, a1_, S1_, m2, c2_.restrict hVU2, j0, a2_,
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU1 c1_ Z S1_ hZU1, ?_, ?_, ?_, ?_, ?_⟩
  have h := hsome2 0 hlen0 j0 hj0
  simp [getElem_cons_zero] at h
  exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU2 c2_ H {j0} h
  intro i hi
  exact ⟨fun hn => restrictIdeal_eq_top_of_le (N[i]'hi) hVU1 $ hnone1 i hi hn, fun j hs => restrictIdeal_eq_restrict_coordIdeal_of_le hVU1 c1_ (N[i]'hi) {j} $ hsome1 i hi j hs⟩
  intro i i' hi hi' j h h'
  exact hinj1 i hi i' hi' j h h'
  intro i hi
  have hi' : i + 1 < lenL (H :: N) := by simp_all
  refine ⟨fun hn => ?_, fun j hs => ?_⟩
  have h := hnone2 (i + 1) hi' hn
  simp [getElem_cons_succ] at h
  exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU2 h
  have h := hsome2 (i + 1) hi' j hs
  simp [getElem_cons_succ] at h
  exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU2 c2_ (N[i]'hi) {j} h
  intro i hi hcon
  have hi' : i + 1 < lenL (H :: N) := by simp_all
  have hzero := hinj2_ (i + 1) hi' 0 hlen0 j0 hcon hj0
  omega

theorem hasStrictNormalCrossingsWith_cons_of_le [Smooth p] (Z H : ISD X)
    (N : Bdy X) (hN : InStrictNormalCrossingPosition p (H :: N)) (hZ : HasStrictNormalCrossingsWith p Z N)
    (hHZ : H ≤ Z) : HasStrictNormalCrossingsWith p Z (H :: N) := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hU, hxU, m, c, lab, S, m', c', j0, lab', hZU, hHU, hlab, hlabinj, hlab', hj0⟩ :=
    exists_etaleCharts_of_inStrictNormalCrossingPosition_cons p Z H N hN hZ hHZ x hx
  obtain ⟨a, ha, j, hjS, hajP, hjlab⟩ :=
    exists_coord_eq_sum_coeff_not_mem_of_le p hU hxU c lab S c' j0 lab' Z H N hx hlab hZU hHU hlab' hj0 hHZ
  have hZideal :=
    c.ideal_eq_span_coord hU Z S hZU
  have hHideal :=
    ideal_eq_span_coord_of_restrictIdeal_eq hU c' H j0 hHU
  have hcP : ∀ i ∈ S, c.coord i ∈ asIdeal (hU.primeIdealOf ⟨x, hxU⟩) := by
    intro i hi
    refine ideal_le_primeIdealOf Z hU hxU hx ?_
    rw [hZideal]
    exact subset_span ⟨i, mpr mem_coe hi, rfl⟩
  obtain ⟨V, hV, hVU, hxV, c2, hc2ne, hc2j, hc2unit⟩ :=
    exists_etaleChart_update_coord p hU c hxU S a j hjS hcP hajP
  let _a0 := pMap X (homOfLE hVU).op
  have hcoordfun : c2.coord = update
      (fun i => _a0.hom $ c.coord i) j
      (∑ i ∈ S, _a0.hom (a i) *
        _a0.hom (c.coord i)) := by
    funext i
    by_cases hij : i = j
    rw [update_apply, if_pos hij, hij, hc2j, map_sum]
    exact sum_congr rfl fun t _ => map_mul _ _ _
    rw [update_apply, if_neg hij]
    exact hc2ne i hij
  have hupd : span (c2.coord '' S)
      = span (imS (fun i => _a0.hom $ c.coord i) S) := by
    rw [hcoordfun]
    exact span_image_update_sum_eq
      (fun i => _a0.hom $ c.coord i) S
      (fun i => _a0.hom $ a i) j hjS hc2unit
  have hZVspan : Z.ideal ⟨V, hV⟩ = span (c2.coord '' S) := by
    rw [hupd, ideal_eq_span_image_map_of_le Z hU hV hVU (c.coord '' S) hZideal,
      image_image]
  have hZVcoord :=
    restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c2 Z S hZVspan
  have hHVspan : H.ideal ⟨V, hV⟩
      = span (c2.coord '' ((({j} : FinSet m)) : Set $ Fin m)) := by
    rw [coe_singleton, image_singleton,
      ideal_eq_span_image_map_of_le H hU hV hVU ({c'.coord j0} : Set U.sec) hHideal,
      image_singleton, ha, ← hc2j]
  have hHVcoord :=
    restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c2 H {j} hHVspan
  have hNVcoord : ∀ i (hi : i < lenL N) t, lab i = some t →
      restrictIdeal (N[i]'hi) V = c2.coordIdeal {t} := by
    intro i hi t hlt
    have htj : t ≠ j := by
      intro hcon
      exact hjlab i hi $ by rw [hlt, hcon]
    have hUeq := an2 (hlab i hi) t hlt
    have hideal :=
      ideal_eq_span_coord_of_restrictIdeal_eq hU c (N[i]'hi) t hUeq
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c2 (N[i]'hi) {t} ?_
    rw [coe_singleton, image_singleton, hc2ne t htj,
      ideal_eq_span_image_map_of_le (N[i]'hi) hU hV hVU ({c.coord t} : Set U.sec) hideal,
      image_singleton]
  have hNVtop : ∀ i (hi : i < lenL N), lab i = none →
      restrictIdeal (N[i]'hi) V = ⊤ := by
    intro i hi hn
    exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU $ an1 (hlab i hi) hn
  obtain ⟨relab, hnl0, hnls⟩ :
      ∃ nl : ℕ → Option (Fin m), nl 0 = some j ∧ ∀ i, nl (i + 1) = lab i :=
    ⟨fun i => if i = 0 then some j else lab $ i - 1, by simp, fun i => by simp⟩
  refine ⟨V, hxV, m, c2, relab, S, ?_, ?_, ?_, hZVcoord⟩
  intro i hi i' hi' t h1 h2
  rcases i with _ | i1
  rcases i' with _ | i1'
  rfl
  simp_all
  rcases i' with _ | i1'
  exfalso
  rw [hnl0] at h2
  rw [hnls i1] at h1
  have hb : i1 < lenL N := by simp_all
  exact hjlab i1 hb $ h1.trans h2.symm
  rw [hnls i1] at h1
  rw [hnls i1'] at h2
  have hb1 : i1 < lenL N := by simp_all
  have hb2 : i1' < lenL N := by simp_all
  have hee := hlabinj i1 i1' hb1 hb2 t h1 h2
  omega
  intro i hi hn
  rcases i with _ | i1
  simp_all
  simp_all
  intro i hi t hs
  rcases i with _ | i1
  simp_all
  simp_all
end

end FunctorialResolution.EmbeddedResolution
end
end
