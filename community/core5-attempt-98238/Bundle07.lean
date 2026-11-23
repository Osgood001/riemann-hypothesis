import Mathlib
import Bundle00
import Bundle01
import Bundle02
import Bundle03
import Bundle04
import Bundle05
import Bundle06
noncomputable section
open CategoryTheory AlgebraicGeometry
open FunctorialResolution.Blowup (IsBlowupAlongIdealSheaf IsLocallyGeneratedByNonZeroDivisor comap_ker_comp_of_isOpenImmersion exceptionalIdeal exceptionalIdeal_eq_comap sigmaio_base_ne strictTransform)
open Finset (card_bij card_eq_one card_erase_of_mem card_pos card_singleton coe_image coe_singleton cons_induction induction_on inf_empty inf_insert inf_le le_inf mem_coe mem_erase mem_insert_of_mem mem_insert_self mem_range mem_singleton_self mem_toList mem_univ nodup_toList prod_congr prod_empty prod_eq_single prod_induction single_le_sum sum_congr sum_eq_single sum_range_succ univ_eq_empty)
open List (ext_getElem finRange get getElem_cons_succ getElem_cons_zero getElem_mem getElem_of_mem length length_cons length_nil map_append map_congr_left map_cons map_map map_nil mem_append mem_cons mem_filter mem_map nodup_cons ofFn ofFn_succ ofFn_zero prod prod_append prod_cons prod_eq_one prod_le_prod' prod_nil range_succ)
open Ideal (comap eq_top_iff_one eq_top_of_isUnit_mem list_prod_le_getElem mapHom map_id map_le_iff_le_comap map_mono mem_comap mem_map_iff_of_surjective mem_map_of_mem mem_span_singleton' mem_span_singleton_self mul_le mul_le_inf mul_mem_left mul_mem_mul mul_mem_right mul_mono one_eq_top pow_le_pow_right pow_le_self pow_right_mono span span_le span_mono span_singleton_eq_top span_singleton_le_iff_mem span_singleton_mul_span_singleton span_singleton_one span_singleton_pow sub_mem subset_span top_pow)
open Set (disjoint_left eq_empty_iff_forall_notMem eq_univ_of_forall image_comp image_congr image_image image_singleton mem_biUnion mem_empty_iff_false mem_iUnion mem_inter mem_ofPred_eq mem_range_self mem_sUnion mem_singleton mem_singleton_iff nonempty_iff_ne_empty preimage preimage_empty preimage_univ range range_eq_empty_iff sUnion_eq_biUnion sdiff_subset singleton_subset_iff subset_empty_iff univ)
open TopologicalSpace.Opens (coe_bot coe_iSup coe_top isBasis_iff_nbhd mem_iSup)
open Scheme.IdealSheafData (coe_support_vanishingIdeal comapIso_hom_fst comap_comp comap_iSup comap_id comap_ideal_eq_map_appLE comap_listProd comap_mono comap_mul comap_pow comap_top eq_top_iff_support_eq_empty exists_iso_subscheme_comap_of_isIso ext_of_iSup_eq_top ideal_iInf ideal_inf ideal_mul ideal_pow ideal_top ker_subschemeι ker_subschemeι_app le_def map_comp mem_support_comap mul_top ofIdealTop subschemeι subschemeι_app_surjective support support_antitone support_nonempty_iff_ne_top top_mul vanishingIdeal vanishingIdeal_ideal)
open FunctorialResolution.EmbeddedResolution.MaxContactReduction (descendStrictPullback dropTrivialBoundary_boundary dropTrivialBoundary_dim dropTrivialBoundary_mult emptyMarkedSeq reduceOrder reduceOrder_of_orderAtLeastLocus_eq_empty)
open Matrix (det det_diagonal det_mul det_submatrix_equiv_self diagonal mul_diagonal of_apply)
open FunctorialResolution.EmbeddedResolution (comap_ker_subschemeio_comp isSmoothDivisor_of_locally_coordIdeal kerSubschemeIso kerSubschemeIso_hom_comp kerSubschemeIso_inv_comp restrictIdeal_eq_of_le_of_eq)
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates (basisKaehler basisKaehler_apply derivIdealIterate_le_iSup_logDerivIdealIterate_controlledTransform eq_sum_smul_partialDeriv map_logDerivIdealIterate_le_span_pow_mul partialDeriv partialDeriv_apply partialDeriv_coord partialDeriv_coord_of_ne partialDeriv_coord_self)
open Nat (add_sub_cancel cast_succ lt_of_succ_le lt_succ_of_le mul_le_mul not_lt_zero sub_le sub_zero zero_le)
open Fin (cast cons_succ cons_zero elim0 eq_zero_or_eq_succ pred_succ prod_congr' prod_univ_def prod_univ_succ succ_ne_zero)
open FunctorialResolution.EmbeddedResolution.MaxContactCoverData (balancedTunedIdeal cT coverMap coverMarkedBlowupData coverTriple coverTriple_structureMorphism emptyMarkedSeq_length exists_descendStrictPullback_eq_some isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some reduceOrder_eq_toMarkedSequence tunedMult)
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups (boundaryLocus ideal_zero isResolution_iff lastIdeal_eq mem_boundaryLocus_iff projectionToSpec projectionToSpec_eq)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (IsAdmissible IsBalanced SameNontrivialBoundary baseChange_mult bc boundary ideal isOrderBoundedByMult_iff mult scheme structMap withBoundary withBoundary_dim withBoundary_mult withSchemeIdealBoundary_ideal withSchemeIdealBoundary_mult)
open Classical (decEq propDecidable)
open Fintype (bijective_iff_injective_and_card card card_congr card_fin card_subtype_compl card_subtype_eq card_ulift equivOfCardEq)
open Equiv (apply_symm_apply ofBijective sumCompl symm_apply_apply symm_symm ulift)
open Surjective (surj)
open IsAffineOpen (exists_basicOpen_le range_fromSpec)
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (toMarkedSequence_blowupMorphism toMarkedSequence_boundary toMarkedSequence_center toMarkedSequence_ideal toMarkedSequence_length toMarkedSequence_projectionToBase toMarkedSequence_toSequenceOfBlowups)
open IsOpenImmersion (isOpen_range isoOfRangeEq)
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData (boundary_zero controlledTransform_zero projectionToBase toMarkedBlowupSequenceData_boundary toMarkedBlowupSequenceData_ideal toMarkedBlowupSequenceData_length toMarkedBlowupSequenceData_projectionToBase toMarkedBlowupSequenceData_toSequenceOfBlowups toSequenceOfBlowups_length)
open FunctorialResolution.EmbeddedResolution.EtaleChart (coordIdeal_eq_comap_coordSubspaceIdeal etaleCoordinates_coord ideal_eq_span_coord restrictToSubscheme_coord restrict_map)
open IsLocalRing (jacobson_eq_maximalIdeal maximalIdeal mem_maximalIdeal)
open Scheme (IdealSheafData basicOpen exists_affineOpens_mem exists_affineOpens_mem_le isNilpotent_iff_basicOpen_eq_bot_of_isCompact)
open Scheme.Hom (app appIso_hom' appLE appLE_eq_app ker ker_apply ker_comp le_ker_comp pre resLE support_ker)
open Category (assoc comp_id id_comp)
open ULift (down up)
open Or (inl inr)
open Ideal.Quotient (eq_zero_iff_mem mk)
open Set.Finite (coe_toFinset isClosed_biUnion mem_toFinset)
open Limits.pullback (condition fst snd)
open IsClosedImmersion (isClosedEmbedding isIso_of_ker_eq lift lift_fac of_comp)
open Module.Basis (det_apply isUnit_det repr_reindex_apply toMatrix_apply)
open Function (Bijective Injective comp_apply comp_def)
open MorphismProperty.IsStableUnderBaseChange (of_isPullback)
open TopologicalSpace (NoetherianSpace)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (center projectionToBase_succ projectionToBase_zero schemeAt transitionMapSucc)
open CommRingCat.Hom (hom)
open IsLocalization (eq_iff_exists map_units)
open RingHom (coe_comp map_det)
open Option.some (inj)
open CommRingCat (hom_comp ofHom)
section
open TopologicalSpace
open Eq (symm)

namespace FunctorialResolution.EmbeddedResolution

section
variable {Y : Sch}
theorem ideal_mul_apply (A B : ISD Y) V :
    (A * B).ideal V = A.ideal V * B.ideal V := rfl

theorem ideal_pow_apply (A : ISD Y) n
    V : (A ^ n).ideal V = A.ideal V ^ n :=
  congrFun (ideal_pow A n) V

theorem ideal_top_eq_top V :
    (⊤ : ISD Y).ideal V = ⊤ := by simp

theorem restrictIdeal_top_eq_top V :
    restrictIdeal (⊤ : ISD Y) V = ⊤ := comap_top _

theorem ideal_le_ideal_of_le {A B : ISD Y} (h : A ≤ B)
    V : A.ideal V ≤ B.ideal V := h V
end

theorem ideal_map_congr {R S : Type} [CommRing R] [CommRing S] {F G : Type}
    [FunLike F R S] [RingHomClass F R S] [FunLike G R S] [RingHomClass G R S]
    (f : F) (g : G) (h : ∀ x, f x = g x) (I : Ideal R) :
    Ideal.map f I = Ideal.map g I := by
  refine le_antisymm ?_ ?_
  rw [map_le_iff_le_comap]
  intro x hx
  rw [mem_comap, h x]
  exact mem_map_of_mem _ hx
  rw [map_le_iff_le_comap]
  intro x hx
  rw [mem_comap, ← h x]
  exact mem_map_of_mem _ hx

section
variable (k : Type)
theorem logDerivIdealSheafIterate_congr_hom [CommRing k]
    [IsNoetherianRing k] {Y : Sch} {q q' : Y ⟶ Sp k}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q') (P : ISD Y) (r : ℕ)
    (I : ISD Y) :
    logDerivIdealSheafIterate k q P r I = logDerivIdealSheafIterate k q' P r I := by
  subst h
  rfl

section
variable [hv1_0 : Field k] [hv1_1 : CharZero k] {X X1 : Sch} (p : X ⟶ Sp k) [Smooth p] (pi_ : X1 ⟶ X)
include hv1_0 hv1_1
theorem exists_affineOpen_comap_logDerivIdealSheafIterate_eq [Smooth (pi_ ≫ p)] (W : Opn X)
    [IsIso $ morphismRestrict pi_ W] x1_ (hx1_ : x1_ ∈ pre pi_ W)
    (a : ℕ) (P K : ISD X) :
    ∃ V : X1.affineOpens, x1_ ∈ V.1 ∧ V.1 ≤ pre pi_ W ∧
      ((logDerivIdealSheafIterate k p P a K).comap pi_).ideal V =
        (logDerivIdealSheafIterate k (pi_ ≫ p) (P.comap pi_) a $ K.comap pi_).ideal V := by
  let _a5 := pi_ ≫ p
  let _c0 := (pre pi_ W).i ≫ _a5
  obtain ⟨⟨V, hVaff⟩, hxV, hVU⟩ :
      ∃ V : X1.affineOpens, x1_ ∈ V.1 ∧ V.1 ≤ pre pi_ W := by
    apply exists_affineOpens_mem_le
    exact hx1_
  refine ⟨⟨V, hVaff⟩, hxV, hVU, ?_⟩
  have : IsOpenImmersion $ pi_.mr W := inferInstance
  let _a6 := W.i ≫ p
  have : LocallyOfFiniteType _a6 := inferInstance
  let _a2 := _a6
  have : LocallyOfFiniteType $ (pi_.mr W) ≫ _a2 := inferInstance
  have : LocallyOfFiniteType _c0 := inferInstance
  have hq : (pi_.mr W) ≫ _a2 = (pre pi_ W).i ≫ _a5 := by
    rw [← assoc, morphismRestrict_ι, assoc]
  have hP : (P.comap W.i).comap (pi_.mr W) = (P.comap pi_).comap (pre pi_ W).i := by
    rw [← comap_comp, ← comap_comp,
      morphismRestrict_ι]
  have hKc : (K.comap W.i).comap (pi_.mr W) = (K.comap pi_).comap (pre pi_ W).i := by
    rw [← comap_comp, ← comap_comp,
      morphismRestrict_ι]
  let _m0 := logDerivIdealSheafIterate k p P a K
  have e1 : (_m0.comap pi_).comap (pre pi_ W).i
      = (_m0.comap W.i).comap (pi_.mr W) := by
    rw [← comap_comp, ← comap_comp,
      morphismRestrict_ι]
  have e2 : (_m0.comap W.i).comap (pi_.mr W)
      = (logDerivIdealSheafIterate k _a6 (P.comap W.i) a $ K.comap W.i).comap (pi_.mr W) := by
    rw [logDerivIdealSheafIterate_comap_of_isOpenImmersion k p W.i P K a]
  have e4 : logDerivIdealSheafIterate k ((pi_.mr W) ≫ _a2) ((P.comap W.i).comap $ pi_.mr W) a
        ((K.comap W.i).comap $ pi_.mr W)
      = logDerivIdealSheafIterate k _c0 ((P.comap pi_).comap (pre pi_ W).i) a
          ((K.comap pi_).comap (pre pi_ W).i) := by
    rw [hP, hKc]
    exact logDerivIdealSheafIterate_congr_hom k hq _ _ _
  exact ideal_eq_of_restrictIdeal_eq _ _ ⟨V, hVaff⟩ $ restrictIdeal_eq_of_le_of_eq hVU $ e1.trans $ tr_ e2 $ tr_ (logDerivIdealSheafIterate_comap_of_isOpenImmersion k _a6 (pi_.mr W) (P.comap W.i) (K.comap W.i) a) $ tr_ e4 (logDerivIdealSheafIterate_comap_of_isOpenImmersion k _a5 (pre pi_ W).i (P.comap pi_) (K.comap pi_) a).symm

section
variable [hv7_0 : IsLocallyNoetherian X1] (Z H : ISD X) (E : Bdy X) [QuasiCompact (strictTransformio pi_ Z H)] (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (K : ISD X) (c : ℕ) (hK : K ≤ Z ^ c) (a : ℕ) (ha : a ≤ c)
include hv7_0 hsnc hHZ hpi_ hK ha
theorem exists_affineOpen_comap_logDerivIdealSheafIterate_le
    (x1_ : ↥X1) (hx1_ : pi_.base x1_ ∈ Z.support) :
    haveI : Smooth (pi_ ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
    ∃ V : affO X1, x1_ ∈ V.1 ∧
      (cmI (logDerivIdealSheafIterate k p H a K) pi_).ideal V ≤
        (exceptionalIdeal pi_ Z ^ (c - a) *
            logDerivIdealSheafIterate k (pi_ ≫ p) (strictTransform pi_ Z H) a
              (controlledTransform pi_ Z K c hpi_ hK)).ideal V := by
  have hsm := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
  obtain ⟨U0, hxU0, m, c0, S, aH, aE, hZ0, hHnone, hHsome, -, -, -, -⟩ :=
    hsnc.exists_etaleChart_of_cons hx1_
  obtain ⟨⟨U, hUaff⟩, hxU, hUU0⟩ :
      ∃ V : affO X, pi_.base x1_ ∈ V.1 ∧ V.1 ≤ U0 := by
    apply exists_affineOpens_mem_le
    exact hxU0
  let c1 := c0.restrict hUU0
  have hZ1 :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hUU0 c0 Z S hZ0
  have hx1U := hxU
  obtain ⟨s, hsS, hx1B0⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c1 S hpi_ hZ1 x1_ hx1U
  let B0 := blowupChartOfIsBlowup pi_ c1 S hpi_ hZ1 s hsS
  have hx1B0' := hx1B0
  obtain ⟨Vsub, hVsubDomain, hV0aff, hx1V0⟩ := B0.exists_isAffineOpen_mem_le_domain x1_ hx1B0'
  let B := B0.restrict Vsub hVsubDomain
  have hdom := BlowupChart.restrict_domain B0 Vsub hVsubDomain
  have hBaff : IsAffineOpen B.domain := by rw [hdom]
                                           exact hV0aff
  have hx1B : x1_ ∈ B.domain := by rw [hdom]
                                   exact hx1V0
  have hEideal : (exceptionalIdeal pi_ Z).ideal ⟨B.domain, hBaff⟩
      = span {B.chart.coord s} := by
    have h := ideal_eq_span_coord B.chart hBaff (exceptionalIdeal pi_ Z) {s} (B.restrictIdeal_exceptionalIdeal Z hsS hZ1)
    simpa using h
  refine ⟨⟨B.domain, hBaff⟩, hx1B, ?_⟩
  have hofEqTop : restrictIdeal (strictTransform pi_ Z H) B.domain = ⊤ →
      (cmI (logDerivIdealSheafIterate k p H a K) pi_).ideal ⟨B.domain, hBaff⟩ ≤
        (exceptionalIdeal pi_ Z ^ (c - a) *
            logDerivIdealSheafIterate k (pi_ ≫ p) (strictTransform pi_ Z H) a
              (controlledTransform pi_ Z K c hpi_ hK)).ideal ⟨B.domain, hBaff⟩ := by
    intro hST
    have hST2 : restrictIdeal (strictTransform pi_ Z H) B.domain
        = restrictIdeal (⊤) B.domain := by
      rw [hST, restrictIdeal_top_eq_top]
    have hST' : (strictTransform pi_ Z H).ideal ⟨B.domain, hBaff⟩ = ⊤ :=
      (ideal_eq_of_restrictIdeal_eq _ _ ⟨B.domain, hBaff⟩ hST2).trans (ideal_top_eq_top _)
    have h1 : (logDerivIdealSheafIterate k p H a K).ideal ⟨U, hUaff⟩ ≤
        (derivIdealSheafIterate k p a K).ideal ⟨U, hUaff⟩ :=
      ideal_le_ideal_of_le (logDerivIdealSheafIterate_le_derivIdealSheafIterate k p H a K) _
    have h2 : (cmI (logDerivIdealSheafIterate k p H a K) pi_).ideal ⟨B.domain, hBaff⟩ ≤
        (cmI (derivIdealSheafIterate k p a K) pi_).ideal ⟨B.domain, hBaff⟩ := by
      rw [comap_ideal_eq_map_appLE (logDerivIdealSheafIterate k p H a K) pi_
          ⟨U, hUaff⟩ ⟨B.domain, hBaff⟩ B.domain_le,
        comap_ideal_eq_map_appLE (derivIdealSheafIterate k p a K) pi_
          ⟨U, hUaff⟩ ⟨B.domain, hBaff⟩ B.domain_le]
      exact map_mono h1
    have h3 := comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p pi_ Z (H :: E) hsnc hpi_
      K c hK a ha
    refine le_trans h2 $ le_trans (ideal_le_ideal_of_le h3 ⟨B.domain, hBaff⟩) (le_of_eq ?_)
    rw [ideal_mul_apply, ideal_mul_apply, logDerivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal,
      hST', logDerivIdealIterate_top_eq_derivIdealIterate]
  cases haH : aH with
  | none =>
      have hHU := restrictIdeal_eq_top_of_le H hUU0 $ hHnone haH
      exact hofEqTop $ B.restrictIdeal_strictTransform_of_eq_top Z H hHU
  | some t =>
      have hHU :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hUU0 c0 H {t} (hHsome t haH)
      by_cases hts : t = s
      subst hts
      exact hofEqTop $ B.restrictIdeal_strictTransform_coordIdeal_self Z H hsS hZ1 hHU
      have htS :=
        mem_of_restrictIdeal_eq_coordIdeal_of_le hUaff c1 Z H S t hHZ hHU hZ1 (pi_.base x1_) hxU hx1_
      have hHideal : H.ideal ⟨U, hUaff⟩ = span {c1.coord t} := by
        have h := ideal_eq_span_coord c1 hUaff H {t} hHU
        simpa using h
      have hSTideal : (strictTransform pi_ Z H).ideal ⟨B.domain, hBaff⟩
          = span {B.chart.coord t} := by
        have h := ideal_eq_span_coord B.chart hBaff (strictTransform pi_ Z H) {t} (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hsS hZ1 t htS hts hHU)
        simpa using h
      let algU := sectionsAlgebra k p U
      let algB := sectionsAlgebra k (pi_ ≫ p) B.domain
      let ph_ : X.sec U →ₐ[k] B.domain.sec :=
        { toRingHom := (appLE pi_ U B.domain B.domain_le).hom
          commutes' := sectionsAlgebraMap_appLE_apply k p pi_ U B.domain B.domain_le }
      have hph : ∀ x, ph_ x = (appLE pi_ U B.domain B.domain_le).hom x := fun _ => rfl
      have hmapRestrict : ∀ I : Ideal U.sec,
          Ideal.map ph_ I = Ideal.map (appLE pi_ U B.domain B.domain_le).hom I :=
        fun I => ideal_map_congr ph_ (appLE pi_ U B.domain B.domain_le).hom hph I
      have hcoordU : ∀ i : UFin m,
          @EtaleCoordinates.coord k _ (UFin m) U.sec _ c1.algebra i
            = c1.coord i.down :=
        fun i => etaleCoordinates_coord c1 i.down
      have hcoordW : ∀ i : UFin m,
          @EtaleCoordinates.coord k _ (UFin m) B.domain.sec _ B.chart.algebra i
            = B.chart.coord i.down :=
        fun i => etaleCoordinates_coord B.chart i.down
      have hcoordUt := etaleCoordinates_coord c1 t
      have hcoordWs :=
        etaleCoordinates_coord B.chart s
      have hin : ∀ i ∈ uliftFinset m S, i ≠ (up s) →
          ph_ (@EtaleCoordinates.coord k _ (UFin m) U.sec _ c1.algebra i) =
            (@EtaleCoordinates.coord k _ (UFin m) B.domain.sec _
                B.chart.algebra i) *
              (@EtaleCoordinates.coord k _ (UFin m) B.domain.sec _
                B.chart.algebra (up s)) := by
        intro i hi hne
        rw [hcoordU i, hcoordW i, hcoordW (up s), hph]
        exact B.appLE_coord_of_mem i.down (down_mem_of_mem_uliftFinset hi)
          (fun h => hne (congrArg up h))
      have hself : ph_ (@EtaleCoordinates.coord k _ (UFin m) U.sec _ c1.algebra
            (up s))
          = @EtaleCoordinates.coord k _ (UFin m) B.domain.sec _ B.chart.algebra
            (up s) := by
        rw [hcoordU (up s), hcoordW $ up s, hph]
        exact B.appLE_coord_self
      have hout : ∀ i ∉ uliftFinset m S,
          ph_ (@EtaleCoordinates.coord k _ (UFin m) U.sec _ c1.algebra i) =
            @EtaleCoordinates.coord k _ (UFin m) B.domain.sec _
              B.chart.algebra i := by
        intro i hi
        rw [hcoordU i, hcoordW i, hph]
        exact B.appLE_coord_of_not_mem i.down fun h => hi $ up_mem_uliftFinset h
      have hnzd : (@EtaleCoordinates.coord k _ (UFin m) B.domain.sec _
          B.chart.algebra (up s)) ∈ nonZeroDivisors B.domain.sec := by
        rw [hcoordWs]
        exact coord_mem_nonZeroDivisors hBaff B.chart s
      have hJ : Ideal.map ph_ (K.ideal ⟨U, hUaff⟩) ≤
          span {(@EtaleCoordinates.coord k _ (UFin m) B.domain.sec _
              B.chart.algebra (up s)) ^ c} *
            (controlledTransform pi_ Z K c hpi_ hK).ideal ⟨B.domain, hBaff⟩ := by
        rw [hcoordWs, hmapRestrict]
        refine le_of_eq ?_
        rw [← span_singleton_pow, ← hEideal, ← ideal_pow_apply, ← ideal_mul_apply,
          exceptionalIdeal_pow_mul_controlledTransform pi_ Z K c hpi_ hK]
        exact (comap_ideal_eq_map_appLE K pi_ ⟨U, hUaff⟩
          ⟨B.domain, hBaff⟩ B.domain_le).symm
      have key := @map_logDerivIdealIterate_le_span_pow_mul k _ (UFin m)
        (decEq (UFin m))
        U.sec _ (sectionsAlgebra k p U) c1.algebra c1.isScalarTower
        (c1.algebra_formallyEtale hUaff)
        B.domain.sec _ (sectionsAlgebra k (pi_ ≫ p) B.domain) B.chart.algebra
        B.chart.isScalarTower (B.chart.algebra_formallyEtale hBaff)
        ph_ (uliftFinset m S) (up s) _
        hin hself hout (up_mem_uliftFinset hsS) hnzd (up t) (up_mem_uliftFinset htS)
        (fun h => hts $ congrArg down h)
        (K.ideal ⟨U, hUaff⟩) ((controlledTransform pi_ Z K c hpi_ hK).ideal ⟨B.domain, hBaff⟩)
        c hJ a ha
      rw [hcoordUt, hcoordWs, etaleCoordinates_coord B.chart t, hmapRestrict] at key
      rw [comap_ideal_eq_map_appLE (logDerivIdealSheafIterate k p H a K) pi_
          ⟨U, hUaff⟩ ⟨B.domain, hBaff⟩ B.domain_le,
        logDerivIdealSheafIterate_ideal, hHideal, ideal_mul_apply, ideal_pow_apply, hEideal,
        logDerivIdealSheafIterate_ideal, hSTideal, span_singleton_pow]
      exact key

theorem comap_logDerivIdealSheafIterate_le_exceptionalIdeal_pow_mul :
    haveI : Smooth $ pi_ ≫ p := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
    cmI (logDerivIdealSheafIterate k p H a K) pi_ ≤
      p5 pi_ Z ^ (c - a) *
        logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) a
          (controlledTransform pi_ Z K c hpi_ hK) := by
  have hsm := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
  refine le_of_forall_exists_affineOpen ?_
  intro y
  by_cases hy : bsM pi_ y ∈ spI Z
  exact exists_affineOpen_comap_logDerivIdealSheafIterate_le k p pi_ Z H E hsnc hHZ hpi_ K c hK a ha
    y hy
  have :=
    isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hpi_ Z.support.compl fun x hx => hx
  obtain ⟨V, hyV, hVW, heq⟩ :=
    exists_affineOpen_comap_logDerivIdealSheafIterate_eq k p pi_ Z.support.compl y hy a H K
  have hEV2 : restrictIdeal (p5 pi_ Z) V.1
      = restrictIdeal (⊤) V.1 := by
    rw [restrictIdeal_exceptionalIdeal_eq_top_of_le_compl pi_ Z V.1 hVW, restrictIdeal_top_eq_top]
  have hEV :=
    (ideal_eq_of_restrictIdeal_eq _ _ V hEV2).trans $ ideal_top_eq_top _
  have hCTV : (controlledTransform pi_ Z K c hpi_ hK).ideal V = (cmI K pi_).ideal V := by
    have h := congrArg (fun A : ISD X1 => A.ideal V)
      (exceptionalIdeal_pow_mul_controlledTransform pi_ Z K c hpi_ hK)
    simp [ideal_mul_apply, ideal_pow_apply, hEV] at h
    rwa [← one_eq_top, one_pow, one_mul] at h
  have hexcPow : (p5 pi_ Z ^ (c - a) *
        logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) a
          (controlledTransform pi_ Z K c hpi_ hK)).ideal V
      = (logDerivIdealSheafIterate k (pi_ ≫ p) (cmI H pi_) a $ cmI K pi_).ideal V := by
    rw [ideal_mul_apply, ideal_pow_apply, hEV, ← one_eq_top, one_pow, one_mul,
      logDerivIdealSheafIterate_ideal, logDerivIdealSheafIterate_ideal, ideal_eq_of_restrictIdeal_eq _ _ V $ restrictIdeal_strictTransform_eq_comap_of_le_compl pi_ Z H V.1 hVW, hCTV]
  exact ⟨V, hyV, le_of_eq $ tr_ heq hexcPow.symm⟩
end
end
end


theorem le_natCast_iff_not_succ_le (a : ENat) (m : ℕ) :
    a ≤ (m : ENat) ↔ ¬ ((m + 1 : ℕ) : ENat) ≤ a := by
  induction a using ENat.recTopCoe with
  | top =>
      refine iff_of_false ?_ ?_
      simp_all
      simp_all
  | coe n =>
      constructor
      intro h h'
      have h1 : n ≤ m := by exact_mod_cast h
      have h2 : m + 1 ≤ n := by exact_mod_cast h'
      omega
      intro h
      have h2 : n ≤ m := by
        by_contra hc
        exact h $ by exact_mod_cast (by omega : m + 1 ≤ n)
      exact_mod_cast h2

theorem orderAt_le_iff_notMem_orderAtLeastLocus {X : Sch} (I : ISD X) (m : ℕ)
    (x : X) :
    orderAt I x ≤ (m : ENat) ↔ x ∉ orderAtLeastLocus I (m + 1) := by
  rw [mem_orderAtLeastLocus_iff]
  exact le_natCast_iff_not_succ_le (orderAt I x) m

section
variable (k : Type) [Field k] [CharZero k]
section
variable {X : Sch} (p) [Smooth p] (I : ISD X) (m : ℕ) (x : X)
theorem notMem_support_derivIdealSheafIterate_iff_orderAt_le :
    x ∉ support (derivIdealSheafIterate k p m I) ↔ orderAt I x ≤ (m : ENat) := by
  have h0 := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I (m := m + 1) (hm := by omega)
  rw [add_sub_cancel] at h0
  rw [orderAt_le_iff_notMem_orderAtLeastLocus, ← SetLike.mem_coe, h0]

theorem stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le :
    stalkIdeal (derivIdealSheafIterate k p m I) x = ⊤ ↔ orderAt I x ≤ (m : ENat) := by
  rw [← notMem_support_derivIdealSheafIterate_iff_orderAt_le k p I m x,
    mem_support_iff_stalkIdeal_ne_top]
  simp
end

section
variable {X X1 : Sch} (p : X ⟶ Sp k) [Smooth p] (pi_ : X1 ⟶ X) [IsLocallyNoetherian X1] (Z : ISD X) (E : Bdy X) (hZ : HasStrictNormalCrossingsWith p Z E) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (I : ISD X) (m : ℕ) (hI : I ≤ Z ^ m)
include hZ
theorem orderAt_controlledTransform_le z (hz : orderAt I z ≤ (m : ENat)) x1_
    (hx1_ : pi_.base x1_ = z) :
    orderAt (controlledTransform pi_ Z I m hpi_ hI) x1_ ≤ (m : ENat) := by
  subst hx1_
  have hsm := smooth_comp_of_isBlowupAlongIdealSheaf hZ hpi_
  have h2 :=
    comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p pi_ Z E hZ hpi_ I m hI m le_rfl
  rw [Nat.sub_self, pow_zero, one_mul] at h2
  have h4 := stalkIdeal_mono h2 x1_
  rw [stalkIdeal_comap, (stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k p I m $ bsM pi_ x1_).2 hz, m166, top_le_iff] at h4
  exact (stalkIdeal_derivIdealSheafIterate_eq_top_iff_orderAt_le k (pi_ ≫ p)
    (controlledTransform pi_ Z I m hpi_ hI) m x1_).1 h4

theorem orderAt_controlledTransform_le_of_orderAt_image_le x1_ (hx1_ : orderAt I (pi_.base x1_) ≤ (m : ENat)) :
    orderAt (controlledTransform pi_ Z I m hpi_ hI) x1_ ≤ (m : ENat) :=
  orderAt_controlledTransform_le k p pi_ Z E hZ hpi_ I m hI (bsM pi_ x1_) hx1_ x1_ rfl


theorem orderAt_controlledTransform_le_of_forall_le (h : ∀ x : X, orderAt I x ≤ (m : ENat)) x1_ :
    orderAt (controlledTransform pi_ Z I m hpi_ hI) x1_ ≤ (m : ENat) :=
  orderAt_controlledTransform_le k p pi_ Z E hZ hpi_ I m hI (bsM pi_ x1_) (h $ bsM pi_ x1_) x1_ rfl

theorem orderAtLeastLocus_controlledTransform_subset_preimage :
    orderAtLeastLocus (controlledTransform pi_ Z I m hpi_ hI) (m + 1) ⊆
      ⇑pi_.base ⁻¹' orderAtLeastLocus I (m + 1) := by
  intro x1_ hx1_
  by_contra hz
  rw [m163, mem_orderAtLeastLocus_iff] at hz
  have h := (fun k [Field k] [CharZero k] p [Smooth p] pi_ Z E hZ hpi_ I m hI z hz x1_ hx1_ => orderAt_controlledTransform_le k p pi_ Z E hZ hpi_ I m hI z
    ((orderAt_le_iff_notMem_orderAtLeastLocus I m z).2 hz) x1_ hx1_) k p pi_ Z E hZ hpi_ I m hI
    (bsM pi_ x1_) hz x1_ rfl
  rw [mem_orderAtLeastLocus_iff] at hx1_
  have hcontra : m + 1 ≤ m := by exact_mod_cast (le_trans hx1_ h)
  omega
end
end


section
variable (k : Type) [Field k] [CharZero k] {X : Sch} (p : X ⟶ Sp k) [Smooth p] (I : ISD X) (m : ℕ) (E : Bdy X) (d : BlowupSequenceData X) (hd : d.IsMarked p I m E) (hI : ∀ x : ↥X, orderAt I x ≤ (m : ENat)) (t : ℕ) (ht : t ≤ d.length)
include hd hI ht
theorem smooth_projectionToBase_comp_and_orderAt_controlledTransform_le :
    Smooth (d.projectionToBase t ≫ p) ∧
      ∀ x : ↥(d.obj t), orderAt (d.controlledTransform I m t) x ≤ (m : ENat) := by
  revert ht
  induction t with
  | zero =>
      intro _
      constructor
      rw [p23]
      infer_instance
      intro x
      rw [controlledTransform_zero, orderAt_comap_of_isOpenImmersion]
      exact hI _
  | succ s ih =>
      intro hs
      have hs' := hs
      obtain ⟨ihsm, ihord⟩ := ih $ le_of_lt hs'
      let _a1 := d.projectionToBase s ≫ p
      have hpi_ := d.isBlowup s hs'
      have hsnc := hd.center_snc s hs'
      have hsm1 : Smooth $ d.projectionToBase (s + 1) ≫ p := by
        rw [p43, assoc]
        exact smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
      refine ⟨hsm1, ?_⟩
      have : IsLocallyNoetherian $ d.obj $ s + 1 :=
        by
        exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian $ d.projectionToBase (s + 1) ≫ p
      let _a2 := d.controlledTransform I m s
      let _a4 := d.boundaryFrom E s
      have hIle :=
        le_pow_of_hasStrictNormalCrossingsWith _a1 (d.center s) _a2 _a4
          hsnc m $ hd.center_order s hs'
      intro x
      rw [eq_controlledTransform_of_mul_eq_comap (d.map s) (d.center s) _a2 m hpi_ hIle (d.controlledTransform I m $ s + 1) $ d.pow_exceptionalIdeal_mul_controlledTransform_succ I m s $ hd.divisible s hs']
      exact orderAt_controlledTransform_le_of_forall_le k _a1 (d.map s) (d.center s)
        _a4 hsnc hpi_ _a2 m hIle ihord x

theorem orderAt_controlledTransform_le_of_isMarked x :
    orderAt (d.controlledTransform I m t) x ≤ (m : ENat) :=
  (smooth_projectionToBase_comp_and_orderAt_controlledTransform_le k p I m E d hd hI t ht).2 x
end


section
variable {Y : Sch}
theorem top_ideal_eq_top U :
    (⊤ : ISD Y).ideal U = ⊤ := by
  simp [ideal_top]

theorem pow_ideal_eq_ideal_pow (A : ISD Y)
    U : ∀ j, (A ^ j).ideal U = A.ideal U ^ j :=
  fun j => congrFun (ideal_pow A j) U

theorem restrictIdeal_top U :
    restrictIdeal (⊤ : ISD Y) U = ⊤ := by
  simp [restrictIdeal_eq_comap_io]

private theorem ideal_affineOpen_eq_top_of_restrictIdeal_eq_top (D : ISD Y)
    {V} (hV : IsAffineOpen V) (h : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have h2 := h
  rw [← restrictIdeal_top] at h2
  rw [ideal_eq_of_restrictIdeal_eq D ⊤ ⟨V, hV⟩ h2, top_ideal_eq_top]
end

section
variable (k : Type) [Field k] [CharZero k] {X X1 : Sch} (p : X ⟶ Sp k) [Smooth p] (pi_ : X1 ⟶ X) [IsLocallyNoetherian X1] (Z H : ISD X) (E : Bdy X) (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) [QuasiCompact (strictTransformio pi_ Z H)] (A : ISD X) (m : ℕ) (L : ℕ → ISD X1) (hL : ∀ l ≤ m, exceptionalIdeal pi_ Z ^ (m - l) * L l = (derivIdealSheafIterate k p l A).comap pi_) (n : ℕ) (hn : n ≤ m)
include hsnc hHZ hpi_ hL hn
theorem exists_affineOpen_derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate x1_ (hx1_ : pi_.base x1_ ∈ support Z) :
    haveI : Smooth (pi_ ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
    ∃ V : affO X1, x1_ ∈ V.1 ∧
      (derivIdealSheafIterate k (pi_ ≫ p) n (L 0)).ideal V ≤
        (⨆ l, ⨆ _ : l ≤ n,
            logDerivIdealSheafIterate k (pi_ ≫ p) (strictTransform pi_ Z H) (n - l) (L l)).ideal V := by
  let hsmooth := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
  show ∃ V : affO X1, x1_ ∈ V.1 ∧
      (derivIdealSheafIterate k (pi_ ≫ p) n (L 0)).ideal V ≤
        (⨆ l, ⨆ _ : l ≤ n,
            logDerivIdealSheafIterate k (pi_ ≫ p) (strictTransform pi_ Z H) (n - l) (L l)).ideal V
  obtain ⟨U, hxU, mm, c, S, aH, a, hZU, hHtop, hHcoord, -, -, -, -⟩ :=
    hsnc.exists_etaleChart_of_cons hx1_
  obtain ⟨U', _mm2, hxU', hU'U, hU'aff, -⟩ := exists_etaleChart_le p (bsM pi_ x1_) U hxU
  obtain ⟨cU, hZU', hHU'⟩ : ∃ cU : EtaleChart p U' mm, restrictIdeal Z U' = cU.coordIdeal S ∧
      (restrictIdeal H U' = ⊤ ∨ ∃ t, restrictIdeal H U' = cU.coordIdeal {t}) := by
    refine ⟨c.restrict hU'U, restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c Z S hZU, ?_⟩
    cases haH : aH with
    | none => exact inl $ FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_of_le H hU'U (hHtop haH)
    | some t =>
        exact inr ⟨t, restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c H {t} (hHcoord t haH)⟩
  have hx1U' := hxU'
  obtain ⟨s, hs, hx1dom⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ cU S hpi_ hZU' x1_ hx1U'
  obtain ⟨B, hBaff, hx1B⟩ : ∃ B : BlowupChart pi_ cU S s, IsAffineOpen B.domain ∧ x1_ ∈ B.domain := by
    obtain ⟨V, hVle, hVaff, hxV⟩ :=
      (blowupChartOfIsBlowup pi_ cU S hpi_ hZU' s hs).exists_isAffineOpen_mem_le_domain x1_ hx1dom
    refine ⟨(blowupChartOfIsBlowup pi_ cU S hpi_ hZU' s hs).restrict V hVle, ?_, ?_⟩
    rwa [BlowupChart.restrict_domain]
    rwa [BlowupChart.restrict_domain]
  have hcase : (strictTransform pi_ Z H).ideal ⟨B.domain, hBaff⟩ = ⊤ ∨
      ∃ t, (strictTransform pi_ Z H).ideal ⟨B.domain, hBaff⟩
          = span {B.chart.coord t} ∧ t ≠ s ∧ t ∈ S := by
    rcases hHU' with hHtopU | ⟨t, hHt⟩
    exact inl (ideal_affineOpen_eq_top_of_restrictIdeal_eq_top _ hBaff
      (B.restrictIdeal_strictTransform_of_eq_top Z H hHtopU))
    by_cases hts : t = s
    subst hts
    exact inl (ideal_affineOpen_eq_top_of_restrictIdeal_eq_top _ hBaff
      (B.restrictIdeal_strictTransform_coordIdeal_self Z H hs hZU' hHt))
    have htS :=
      mem_of_restrictIdeal_eq_coordIdeal_of_le hU'aff cU Z H S t hHZ hHt hZU'
        (bsM pi_ x1_) hxU' hx1_
    refine inr ⟨t, ?_, hts, htS⟩
    rw [B.chart.ideal_eq_span_coord hBaff _ {t}
      (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZU' t htS hts hHt)]
    simp
  rcases hcase with hP | ⟨t, hP, hts, htS⟩
  refine ⟨⟨B.domain, hBaff⟩, hx1B, ?_⟩
  refine le_trans ?_ (Scheme.IdealSheafData.le_def.mp (le_iSup₂ (f := fun l (_ : l ≤ n) =>
    logDerivIdealSheafIterate k (pi_ ≫ p) (strictTransform pi_ Z H) (n - l) (L l)) 0
    (zero_le n)) _)
  rw [derivIdealSheafIterate_ideal, logDerivIdealSheafIterate_ideal, hP,
    logDerivIdealIterate_top_eq_derivIdealIterate, sub_zero]
  refine ⟨⟨B.domain, hBaff⟩, hx1B, ?_⟩
  let instS := sectionsAlgebra k p U'
  let instS1 := sectionsAlgebra k (pi_ ≫ p) B.domain
  let instPS := cU.algebra
  let instPS1 :=
    B.chart.algebra
  have instST :=
    cU.isScalarTower
  have instST1 : IsScalarTower k (MvU mm k) B.domain.sec :=
    B.chart.isScalarTower
  have instFormallyEtale :=
    cU.algebra_formallyEtale hU'aff
  have instFE1_ :
      Algebra.FormallyEtale (MvU mm k) B.domain.sec :=
    B.chart.algebra_formallyEtale hBaff
  let instDecEq : DecidableEq (UFin mm) := decEq _
  have hcoordU :=
    cU.etaleCoordinates_coord
  have hcoordV :=
    B.chart.etaleCoordinates_coord
  have hBle := B.domain_le
  let ph_ : X.sec U' →ₐ[k] B.domain.sec :=
    { ((appLE pi_ U' B.domain hBle).hom) with
      commutes' := fun x => sectionsAlgebraMap_appLE_apply k p pi_ U' B.domain hBle x }
  obtain ⟨T, hmemT⟩ : ∃ T : Finset (UFin mm),
      ∀ i : UFin mm, i ∈ T ↔ i.down ∈ S := by
    refine ⟨S.map ⟨up, fun x y hxy => by simpa using hxy⟩, fun i => ?_⟩
    constructor
    intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.1 hi
    rwa [← hji]
    intro hi
    exact Finset.mem_map.2 ⟨i.down, hi, rfl⟩
  have hsT := (hmemT ⟨s⟩).2 hs
  have hhT := (hmemT ⟨t⟩).2 htS
  have hhs := fun hh => hts $ congrArg down hh
  have hin : ∀ i ∈ T, i ≠ (⟨s⟩ : UFin mm) →
      ph_ (EtaleCoordinates.coord k (UFin mm) U'.sec i) =
        EtaleCoordinates.coord k (UFin mm) B.domain.sec i *
          EtaleCoordinates.coord k (UFin mm) B.domain.sec ⟨s⟩ := by
    rintro ⟨i⟩ hiT hine
    rw [hcoordU, hcoordV, hcoordV]
    exact B.appLE_coord_of_mem i ((hmemT ⟨i⟩).1 hiT) fun hh => hine $ congrArg up hh
  have hsc : ph_ (EtaleCoordinates.coord k (UFin mm) U'.sec
        (⟨s⟩ : UFin mm)) =
      EtaleCoordinates.coord k (UFin mm) B.domain.sec ⟨s⟩ := by
    rw [hcoordU, hcoordV]
    exact B.appLE_coord_self
  have hout : ∀ i ∉ T,
      ph_ (EtaleCoordinates.coord k (UFin mm) U'.sec i) =
        EtaleCoordinates.coord k (UFin mm) B.domain.sec i := by
    rintro ⟨i⟩ hiT
    rw [hcoordU, hcoordV]
    exact B.appLE_coord_of_not_mem i fun hh => hiT $ (hmemT ⟨i⟩).2 hh
  have hnzd : EtaleCoordinates.coord k (UFin mm) B.domain.sec
      (⟨s⟩ : UFin mm) ∈ nonZeroDivisors B.domain.sec := by
    rw [hcoordV]
    exact coord_mem_nonZeroDivisors hBaff B.chart s
  have hE : (exceptionalIdeal pi_ Z).ideal ⟨B.domain, hBaff⟩
      = span {B.chart.coord s} := by
    rw [B.chart.ideal_eq_span_coord hBaff _ {s} (B.restrictIdeal_exceptionalIdeal Z hs hZU')]
    simp
  have hL' : ∀ i ≤ m,
      span {EtaleCoordinates.coord k (UFin mm) B.domain.sec
          (⟨s⟩ : UFin mm) ^ (m - i)} * (L i).ideal ⟨B.domain, hBaff⟩ =
        Ideal.map ph_ (derivIdealIterate k i (A.ideal ⟨U', hU'aff⟩)) := by
    intro i hi
    have hmul : (exceptionalIdeal pi_ Z ^ (m - i) * L i).ideal ⟨B.domain, hBaff⟩ =
        (exceptionalIdeal pi_ Z ^ (m - i)).ideal ⟨B.domain, hBaff⟩ *
          (L i).ideal ⟨B.domain, hBaff⟩ := by
      simp [ideal_mul, Pi.mul_apply]
    rw [hcoordV, ← span_singleton_pow, ← hE, ← pow_ideal_eq_ideal_pow, ← hmul,
      hL i hi,
      comap_ideal_eq_map_appLE _ pi_ ⟨U', hU'aff⟩ ⟨B.domain, hBaff⟩ hBle,
      derivIdealSheafIterate_ideal]
    rfl
  have key :=
    derivIdealIterate_le_iSup_logDerivIdealIterate_controlledTransform
      k (UFin mm) U'.sec B.domain.sec ph_ T ⟨s⟩ ⟨t⟩
      hsT hin hsc hout hnzd hhT hhs (A.ideal ⟨U', hU'aff⟩)
      (fun i => (L i).ideal ⟨B.domain, hBaff⟩) m hL' n hn
  rw [hcoordV] at key
  rw [derivIdealSheafIterate_ideal]
  refine le_trans key ?_
  refine iSup_le fun i => ?_
  refine iSup_le fun hi => ?_
  have hre : logDerivIdealIterate k (span {B.chart.coord t}) (n - i)
        ((L i).ideal ⟨B.domain, hBaff⟩) =
      (logDerivIdealSheafIterate k (pi_ ≫ p) (strictTransform pi_ Z H) (n - i) (L i)).ideal
        ⟨B.domain, hBaff⟩ := by simp_all
  rw [hre]
  exact Scheme.IdealSheafData.le_def.mp (le_iSup₂ (f := fun l (_ : l ≤ n) =>
    logDerivIdealSheafIterate k (pi_ ≫ p) (strictTransform pi_ Z H) (n - l) (L l)) i hi) _

theorem derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_strictTransform :
    haveI : Smooth (pi_ ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
    derivIdealSheafIterate k (pi_ ≫ p) n (L 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) (n - l) (L l) := by
  let hsmooth := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
  show derivIdealSheafIterate k (pi_ ≫ p) n (L 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) (n - l) (L l)
  have main : ∀ y, ∃ V : affO X1, y ∈ V.1 ∧
      (derivIdealSheafIterate k (pi_ ≫ p) n (L 0)).ideal V ≤
        (⨆ l, ⨆ _ : l ≤ n,
            logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) (n - l) (L l)).ideal V := by
    intro y
    by_cases hy : bsM pi_ y ∈ spI Z
    exact exists_affineOpen_derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate
      k p pi_ Z H E hsnc hHZ hpi_ A m L hL n hn y hy
    have hyW := hy
    have :=
      isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hpi_ (suppC Z) fun x hx => hx
    obtain ⟨V, hyV, hVW, heq⟩ :=
      exists_affineOpen_comap_derivIdealSheafIterate_eq k p pi_ (suppC Z) y hyW n A
    refine ⟨V, hyV, ?_⟩
    have hiterate : ∀ l, l ≤ m →
        (L l).ideal V = (cmI (derivIdealSheafIterate k p l A) pi_).ideal V := by
      intro l hl
      have hx : (p5 pi_ Z ^ (m - l) * L l).ideal V
          = (cmI (derivIdealSheafIterate k p l A) pi_).ideal V := by rw [hL l hl]
      have hmul : (p5 pi_ Z ^ (m - l) * L l).ideal V
          = (p5 pi_ Z ^ (m - l)).ideal V * (L l).ideal V := by
        simp [ideal_mul, Pi.mul_apply]
      rwa [hmul, pow_ideal_eq_ideal_pow, ideal_affineOpen_eq_top_of_restrictIdeal_eq_top _ V.2 (restrictIdeal_exceptionalIdeal_eq_top_of_le_compl pi_ Z V hVW), top_pow, Ideal.top_mul] at hx
    have h0 : (L 0).ideal V = (cmI A pi_).ideal V := by
      have h00 := hiterate 0 $ zero_le m
      rwa [derivIdealSheafIterate_zero] at h00
    have hstep : (derivIdealSheafIterate k (pi_ ≫ p) n (L 0)).ideal V = (L n).ideal V := by
      rw [derivIdealSheafIterate_ideal, h0,
        ← derivIdealSheafIterate_ideal k (pi_ ≫ p) n (cmI A pi_) V, ← heq, ← hiterate n hn]
    rw [hstep]
    have hmono := Scheme.IdealSheafData.le_def.mp (le_iSup₂ (f := fun l (_ : l ≤ n) =>
      logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) (n - l) (L l)) n
      (le_refl n)) V
    rwa [Nat.sub_self, logDerivIdealSheafIterate_zero] at hmono
  exact le_of_forall_exists_affineOpen main
end

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

theorem appLE_preimage_naturality {Y Q : Sch} (f : Y ⟶ Q) {A B}
    (h : B ≤ A) (h' : pre f B ≤ pre f A) z :
    (appLE f B (pre f B) le_rfl).hom ((Q.presheaf.map (homOfLE h).op).hom z)
      = (Y.presheaf.map (homOfLE h').op).hom ((appLE f A (pre f A) le_rfl).hom z) := by
  have key : pMap Q (homOfLE h).op ≫ appLE f B (preU f B) le_rfl
      = appLE f A (preU f A) le_rfl ≫ pMap Y (homOfLE h').op := by simp_all
  have h2 := congrArg (fun ph_ : xSec Q A ⟶ Γ(Y, preU f B) => hom ph_ z) key
  simp only [hom_comp, coe_comp, comp_apply] at h2
  exact h2

section

variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem det_derivation_mul_sub_mem_of_eq_one_or_mem {B : Type} [CommRing B] [Algebra k B]
    (δ : ι → Derivation k B B) (v x : ι → B) (m : Ideal B)
    (h : ∀ b : ι, v b = 1 ∨ x b ∈ m) :
    (Matrix.of fun a b : ι => δ a $ v b * x b).det
        - (Matrix.of fun a b : ι => δ a $ x b).det * ∏ b : ι, v b ∈ m := by
  have hmat : (m53 fun a b => (mk m) $ δ a $ v b * x b)
      = (m53 fun a b => (mk m) $ δ a $ x b)
        * diagonal fun b => (mk m) $ v b := by
    ext a b
    rcases h b with hv | hxb
    simp [mul_diagonal, hv]
    have hx0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxb
    simp [mul_diagonal, Derivation.leibniz, hx0, mul_comm]
  have h1 : (mk m) (m53 fun a b => δ a $ v b * x b).det
      = (m53 fun a b => (mk m) $ δ a $ v b * x b).det := by
    rw [map_det]
    rfl
  have h2 : (mk m) (m53 fun a b => δ a $ x b).det
      = (m53 fun a b => (mk m) $ δ a $ x b).det := by
    rw [map_det]
    rfl
  rw [← eq_zero_iff_mem, map_sub, map_mul, map_prod, h1, h2, hmat,
    det_mul, det_diagonal, sub_self]

theorem det_derivation_notMem_comap_of_eq_one_or_mem {R S : Type} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (q : R →+* S) (δ : ι → Derivation k R R)
    (de' : ι → Derivation k S S)
    (hcompat : ∀ a r, q (δ a r) = de' a (q r))
    (f : ι → R) (v : ι → Sˣ) (x : ι → S)
    (hf : ∀ b : ι, q (f b) = (v b : S) * x b)
    (m : Ideal S) (hm : m ≠ ⊤)
    (h : ∀ b : ι, v b = 1 ∨ x b ∈ m)
    (hdet : IsUnit (Matrix.of fun a b : ι => de' a $ x b).det) :
    (Matrix.of fun a b : ι => δ a $ f b).det ∉ comap q m := by
  intro hcon
  rw [mem_comap] at hcon
  have hmat : q.mapMatrix (m53 fun a b => δ a $ f b)
      = m53 fun a b => de' a $ (v b : S) * x b := by
    ext a b
    show q (δ a $ f b) = de' a ((v b : S) * x b)
    rw [hcompat, hf]
  have hq : q (m53 fun a b => δ a $ f b).det
      = (m53 fun a b => de' a $ (v b : S) * x b).det := by
    rw [map_det, hmat]
  rw [hq] at hcon
  have hv1 : ∀ b, (v b : S) = 1 ∨ x b ∈ m := by
    intro b
    rcases h b with hb | hb
    simp_all
    exact inr hb
  have h4 : (m53 fun a b => de' a $ x b).det * ∏ b : ι, (v b : S) ∈ m := by
    simpa using (sub_mem m hcon $ det_derivation_mul_sub_mem_of_eq_one_or_mem (k := k) de' (fun b => (v b : S)) x m hv1)
  exact hm $ eq_top_of_isUnit_mem m h4 $ hdet.mul $ prod_induction (fun b => (v b : S)) IsUnit (fun r s hr hs => hr.mul hs) isUnit_one fun b _ => (v b).isUnit

end

theorem primeIdealOf_eq_comap_primeIdealOf {Y Q : Sch} (f : Y ⟶ Q) {U}
    (hU : IsAffineOpen U) (hW : IsAffineOpen $ f ⁻¹ᵁ U) {y} (hy : y ∈ f ⁻¹ᵁ U) :
    (hU.primeIdealOf ⟨f.base y, hy⟩).asIdeal
      = comap (app f U).hom (hW.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have hbo : ∀ s,
      f ⁻¹ᵁ bOpn Q s = Y.basicOpen ((app f U).hom s) := by
    intro s
    simp
  ext s
  simp [mem_comap]
  constructor
  intro hs
  by_contra hcon
  have hyb :=
    mem_basicOpen_of_notMem_primeIdealOf hW hy _ hcon
  rw [← hbo s] at hyb
  exact notMem_basicOpen_of_mem_primeIdealOf hU hy s hs hyb
  intro hs
  by_contra hcon
  have hyb : y ∈ f ⁻¹ᵁ bOpn Q s := mem_basicOpen_of_notMem_primeIdealOf hU hy s hcon
  rw [hbo s] at hyb
  exact notMem_basicOpen_of_mem_primeIdealOf hW hy _ hs hyb

section
variable {Q : Sch} (H : ISD Q)
theorem exists_basicOpen_subschemeio_preimage_le {U}
    (hU : IsAffineOpen U) V {y}
    (hyU : y ∈ subschemeι H ⁻¹ᵁ U) (hyV : y ∈ V) :
    ∃ f : (Q.sec U), y ∈ subschemeι H ⁻¹ᵁ (basicOpen Q f) ∧
      subschemeι H ⁻¹ᵁ (basicOpen Q f) ≤ V ∧ basicOpen Q f ≤ U := by
  obtain ⟨g, hgle, hyg⟩ :=
    (isAffineOpen_preimage_subschemeio H hU).exists_basicOpen_le (⟨y, ⟨hyV, hyU⟩⟩ : ↥(V ⊓ siPre H U)) hyU
  obtain ⟨f, hf⟩ := subschemeι_app_surjective H ⟨U, hU⟩ g
  refine ⟨f, ?_, ?_, Q.basicOpen_le f⟩
  simp_all
  simp_all
end

theorem span_image_eq_of_isUnit_mul {R : Type} [CommRing R] {ι : Type} (s : Set ι)
    (a b : ι → R) (h : ∀ i ∈ s, ∃ u : R, IsUnit u ∧ a i = u * b i) :
    span (a '' s) = span (b '' s) := by
  apply le_antisymm
  rw [span_le]
  rintro z ⟨i, hi, rfl⟩
  obtain ⟨u, -, hu⟩ := h i hi
  rw [hu]
  exact mul_mem_left _ _ $ subset_span ⟨i, hi, rfl⟩
  rw [span_le]
  rintro z ⟨i, hi, rfl⟩
  obtain ⟨u, hunit, hu⟩ := h i hi
  obtain ⟨u', hu'⟩ := hunit.exists_left_inv
  have hb : b i = u' * a i := by
    rw [hu, ← mul_assoc, hu', one_mul]
  rw [hb]
  exact mul_mem_left _ _ $ subset_span ⟨i, hi, rfl⟩

theorem exists_equiv_subtype_ne_compatible {n m} (hnm : m + 1 = n) j0_ len
    (ga_ : ℕ → Option (Fin n)) (a' : ℕ → Option (Fin m))
    (hinjga : ∀ i i' : ℕ, i < len → i' < len → ∀ j : Fin n,
      ga_ i = some j → ga_ i' = some j → i = i')
    (hinja : ∀ i i' : ℕ, i < len → i' < len → ∀ b : Fin m,
      a' i = some b → a' i' = some b → i = i')
    (hj0_ : ∀ i : ℕ, i < len → ga_ i ≠ some j0_)
    (hfwd : ∀ i : ℕ, i < len → ∀ j : Fin n, ga_ i = some j → ∃ b : Fin m, a' i = some b) :
    ∃ rh_ : Fin m ≃ {j : Fin n // j ≠ j0_},
      ∀ i : ℕ, i < len → ∀ j b, ga_ i = some j → a' i = some b →
        ((rh_ b : Fin n) = j) := by
  classical
  have hQ : ∀ jj : {jj : {j : Fin n // j ≠ j0_} //
        ∃ i, i < len ∧ ga_ i = some ((jj : {j : Fin n // j ≠ j0_}) : Fin n)},
      ∃ b : Fin m, ∀ i, i < len →
        ga_ i = some ((jj : {j : Fin n // j ≠ j0_}) : Fin n) → a' i = some b := by
    rintro ⟨jj, i0_, hi0_, hga0_⟩
    obtain ⟨b, hb⟩ := hfwd i0_ hi0_ _ hga0_
    refine ⟨b, ?_⟩
    intro i hi hga_
    have := hinjga i0_ i hi0_ hi _ hga0_ hga_
    rwa [← this]
  choose g hg using hQ
  have hginj : m120 g := by
    intro j1 j2_ hgj
    obtain ⟨i1_, hi1_, he1_⟩ := j1.2
    obtain ⟨i2_, hi2_, he2_⟩ := j2_.2
    have h1 := hg j1 i1_ hi1_ he1_
    have h2 : a' i2_ = some (g j1) := by
      rw [hgj]
      exact hg j2_ i2_ hi2_ he2_
    have hii := hinja i1_ i2_ hi1_ hi2_ (g j1) h1 h2
    subst hii
    have : (some ((j1 : {j : Fin n // j ≠ j0_}) : Fin n))
        = some ((j2_ : {j : Fin n // j ≠ j0_}) : Fin n) := by rw [← he1_, ← he2_]
    exact m26 $ m26 $ inj this
  have he1 : ∃ e1 : {jj : {j : Fin n // j ≠ j0_} //
        ∃ i, i < len ∧ ga_ i = some ((jj : {j : Fin n // j ≠ j0_}) : Fin n)}
      ≃ {b : Fin m // ∃ jj, g jj = b}, ∀ jj, ((e1 jj : {b : Fin m // ∃ jj, g jj = b}) : Fin m)
        = g jj := by
    refine ⟨ofBijective (fun jj => ⟨g jj, ⟨jj, rfl⟩⟩) ⟨?_, ?_⟩, fun jj => rfl⟩
    intro a b hab
    exact hginj $ congrArg m161 hab
    rintro ⟨b, jj, rfl⟩
    exact ⟨jj, rfl⟩
  obtain ⟨e1, he1val⟩ := he1
  let _a0 := card {j : Fin n // j ≠ j0_}
  have hcardT : _a0 = m := by
    have h1 : card {j : Fin n // ¬ (j = j0_)}
        = card (Fin n) - card {j : Fin n // j = j0_} :=
      card_subtype_compl _
    have h2 : _a0 = n - 1 := by
      rw [show _a0
          = card {j : Fin n // ¬ (j = j0_)} from rfl, h1, card_subtype_eq,
        card_fin]
    omega
  have hA : card {jj : {j : Fin n // j ≠ j0_} //
        ¬ ∃ i, i < len ∧ ga_ i = some ((jj : {j : Fin n // j ≠ j0_}) : Fin n)}
      = _a0
        - card {jj : {j : Fin n // j ≠ j0_} //
            ∃ i, i < len ∧ ga_ i = some ((jj : {j : Fin n // j ≠ j0_}) : Fin n)} :=
    card_subtype_compl _
  have hB : card {b : Fin m // ¬ ∃ jj, g jj = b}
      = card (Fin m) - card {b : Fin m // ∃ jj, g jj = b} :=
    card_subtype_compl _
  have hcard1 := card_congr e1
  have hcardm := card_fin m
  have hcompl : card {jj : {j : Fin n // j ≠ j0_} //
        ¬ ∃ i, i < len ∧ ga_ i = some ((jj : {j : Fin n // j ≠ j0_}) : Fin n)}
      = card {b : Fin m // ¬ ∃ jj, g jj = b} := by
    omega
  have e2 := equivOfCardEq hcompl
  obtain ⟨σ, hsg_⟩ : ∃ σ : {j : Fin n // j ≠ j0_} ≃ Fin m,
      ∀ (jj : {j : Fin n // j ≠ j0_})
        (hQ : ∃ i, i < len ∧ ga_ i = some jj), σ jj = g ⟨jj, hQ⟩ := by
    refine ⟨(sumCompl fun jj : {j : Fin n // j ≠ j0_} =>
        ∃ i, i < len ∧ ga_ i = some jj).symm.trans
      ((e1.sumCongr e2).trans $ sumCompl fun b : Fin m => ∃ jj, g jj = b), ?_⟩
    intro jj hQ
    have hsymm : (sumCompl fun jj : {j : Fin n // j ≠ j0_} =>
        ∃ i, i < len ∧ ga_ i = some jj).symm jj = m44 ⟨jj, hQ⟩ := by
      apply (sumCompl _).injective
      rw [apply_symm_apply]
      rfl
    show (sumCompl fun b : Fin m => ∃ jj, g jj = b)
      ((e1.sumCongr e2) $ (sumCompl fun jj : {j : Fin n // j ≠ j0_} =>
        ∃ i, i < len ∧ ga_ i = some jj).symm jj) = g ⟨jj, hQ⟩
    rw [hsymm]
    show ((e1 ⟨jj, hQ⟩ : {b : Fin m // ∃ jj, g jj = b}) : Fin m) = g ⟨jj, hQ⟩
    exact he1val ⟨jj, hQ⟩
  refine ⟨σ.symm, ?_⟩
  intro i hi j b hga_ hb
  have hjne : j ≠ j0_ := by
    intro hcon
    exact hj0_ i hi $ by rw [hga_, hcon]
  have hQj : ∃ i', i' < len ∧ ga_ i' = some ((⟨j, hjne⟩ : {j : Fin n // j ≠ j0_}) : Fin n) :=
    ⟨i, hi, hga_⟩
  have hsgb : σ ⟨j, hjne⟩ = b := by
    rw [hsg_ ⟨j, hjne⟩ hQj, inj $ st_ (hg ⟨⟨j, hjne⟩, hQj⟩ i hi hga_) hb]
  have hfin : σ.symm b = ⟨j, hjne⟩ := by
    rw [← hsgb, symm_apply_apply]
  exact congrArg m161 hfin

section

variable {X : Sch} {k : Type} [Field k]

theorem appLE_subschemeio_chartPartialDeriv_complOrderEmb {p : X ⟶ Sp k}
    [Smooth p]
    {U : Opn X} (hU : IsAffineOpen U) {n : ℕ} (c : EtaleChart p U n)
    (H : ISD X) [Smooth $ subschemeι H ≫ p] (j0_ : Fin n)
    (hH : restrictIdeal H U = c.coordIdeal {j0_})
    (i : Fin $ n - ({j0_} : FinSet n).card) r :
    (H.subschemeι.appLE U (subschemeι H ⁻¹ᵁ U) le_rfl).hom
        (chartPartialDeriv hU c (complOrderEmb n {j0_} i) r)
      = chartPartialDeriv (isAffineOpen_preimage_subschemeio H hU)
          (c.restrictToSubscheme hU H {j0_} hH) i
          ((H.subschemeι.appLE U (subschemeι H ⁻¹ᵁ U) le_rfl).hom r) := by
  classical
  let instU := sectionsAlgebra k p U
  let instW :=
    sectionsAlgebra k (siI H ≫ p) $ siPre H U
  let instcU := c.algebra
  have instTU := c.isScalarTower
  have instFEU :=
    c.algebra_formallyEtale hU
  let _a3 := c.restrictToSubscheme hU H {j0_} hH
  let instcW := _a3.algebra
  have instTW := _a3.isScalarTower
  have instFEW :=
    _a3.algebra_formallyEtale $ isAffineOpen_preimage_subschemeio H hU
  have hcomm : ∀ a,
      (H.subschemeι.appLE U (siPre H U) le_rfl).hom (algebraMap k U.sec a)
        = algebraMap k Γ(subS H, siPre H U) a := by
    intro a
    exact sectionsAlgebraMap_appLE_apply k p H.si U (siPre H U) le_rfl a
  let pi_ : X.sec U →ₐ[k] Γ(subS H, siPre H U) :=
    { (H.subschemeι.appLE U (siPre H U) le_rfl).hom with commutes' := hcomm }
  have hpisurj : Function.Surjective pi_ := by
    intro z
    obtain ⟨w, hw⟩ := subschemeι_app_surjective H ⟨U, hU⟩ z
    refine ⟨w, ?_⟩
    show (H.subschemeι.appLE U (siPre H U) le_rfl).hom w = z
    rwa [appLE_eq_app]
  have hker : RingHom.ker pi_.toRingHom = span ({c.coord j0_} : Set U.sec) := by
    have h1 :=
      ker_subschemeι_app H ⟨U, hU⟩
    have h2 :=
      c.ideal_eq_span_coord hU H {j0_} hH
    have h3 : (c.coord '' ((({j0_} : FinSet n)) : Set $ Fin n))
        = ({c.coord j0_} : Set U.sec) := by
      simp
    show RingHom.ker (H.subschemeι.appLE U (siPre H U) le_rfl).hom = _
    rw [appLE_eq_app, h1, h2, h3]
  have hne : complOrderEmb n {j0_} i ≠ j0_ := by
    simpa using (complOrderEmb_notMem n {j0_} i)
  let _a1 := up $ complOrderEmb n {j0_} i
  let _a7 := partialDeriv k (UFin n) U.sec _a1
  have hD0 : _a7 (c.coord j0_) = 0 := by
    rw [← c.etaleCoordinates_coord j0_]
    refine partialDeriv_coord_of_ne k (UFin n) U.sec
      _a1 (up j0_) ?_
    intro hcon
    exact hne $ congrArg down hcon
  set δ := _a7 with hdedef
  set de' := liftDerivationOfKerEqSpan pi_ hpisurj (c.coord j0_) hker δ hD0 with hde'def
  have hdesc := fun z =>
    liftDerivationOfKerEqSpan_apply pi_ hpisurj (c.coord j0_) hker δ hD0 z
  have hval : ∀ b : ULift $ Fin $ n - ({j0_} : FinSet n).card,
      de' (EtaleCoordinates.coord k (ULift $ Fin $ n - ({j0_} : FinSet n).card)
            Γ(subS H, siPre H U) b)
        = if b = up i then (1 : Γ(subS H, siPre H U)) else 0 := by
    intro b
    have hcd : _a3.coord b.down
        = pi_ (c.coord $ complOrderEmb n {j0_} b.down) :=
      restrictToSubscheme_coord c hU H {j0_} hH b.down
    rw [_a3.etaleCoordinates_coord b.down, hcd, hdesc]
    by_cases hb : b.down = i
    have h1 : δ (c.coord $ complOrderEmb n {j0_} b.down) = 1 := by
      rw [hb, hdedef, ← c.etaleCoordinates_coord $ complOrderEmb n {j0_} i]
      exact partialDeriv_coord_self k (UFin n) U.sec
        _a1
    have h2 : b = up i := by
      cases b
      exact congrArg up hb
    rw [h1, h2]
    simp
    have h1 : δ (c.coord $ complOrderEmb n {j0_} b.down) = 0 := by
      rw [hdedef, ← c.etaleCoordinates_coord $ complOrderEmb n {j0_} b.down]
      refine partialDeriv_coord_of_ne k (UFin n) U.sec
        _a1 (up $ complOrderEmb n {j0_} b.down) ?_
      intro hcon
      exact hb ((complOrderEmb n {j0_}).injective $ congrArg down hcon).symm
    have h2 : ¬ (b = up i) := by
      intro hcon
      exact hb $ congrArg down hcon
    rw [h1, if_neg h2]
    simp
  have hde'eq : de' = partialDeriv k
      (ULift $ Fin $ n - ({j0_} : FinSet n).card)
      Γ(subS H, siPre H U) (up i) := by
    rw [eq_sum_smul_partialDeriv k
      (ULift $ Fin $ n - ({j0_} : FinSet n).card)
      Γ(subS H, siPre H U) de']
    simp [hval]
  show pi_ (δ r) = partialDeriv k
      (ULift $ Fin $ n - ({j0_} : FinSet n).card)
      Γ(subS H, siPre H U) (up i) (pi_ r)
  rw [← hde'eq]
  exact sy_ $ hdesc r

end

section

variable {P : Sch} {k : Type} [Field k]

theorem hasLocalCoordsOnSmoothHypersurface_of_comap (p : P ⟶ Sp k)
    [Smooth p] (H : ISD P) (N : Bdy P)
    (Z : H.subscheme.IdealSheafData)
    (hN : InStrictNormalCrossingPosition p (H :: N))
    (hZ : HasStrictNormalCrossingsWith (H.si ≫ p) Z (N.map fun D => D.comap H.si)) :
    HasLocalCoordsOnSmoothHypersurface p H N Z := by
  classical
  intro x hx
  have hxH :=
    support_antitone (le_ker_comp_subschemeio H Z) hx
  have hHsm := (hN.1 H (by simp)).2
  have hHft : LocallyOfFiniteType (siI H ≫ p) := inferInstance
  obtain ⟨y, hyx⟩ := (q5 H).ge hxH
  obtain ⟨U0_, hxU0_, n0, c0_, a0_, hinj0_, hnone0, hsome0⟩ := hN.2 x
  obtain ⟨U1_, hU1, hxU1, hU1U0⟩ := exists_isAffineOpen_mem_and_subset hxU0_
  have hdesc1 : ∀ i, ∀ hi : i < (H :: N).length,
      ((a0_ i = none → restrictIdeal ((H :: N)[i]'hi) U1_ = ⊤) ∧
        ∀ j, a0_ i = some j →
          restrictIdeal ((H :: N)[i]'hi) U1_ = (c0_.restrict hU1U0).coordIdeal {j}) := by
    intro i hi
    exact ⟨fun hn => restrictIdeal_eq_top_of_le _ hU1U0 $ hnone0 i hi hn,
      fun j hj => restrictIdeal_eq_restrict_coordIdeal_of_le hU1U0 c0_ _ {j} (hsome0 i hi j hj)⟩
  obtain ⟨U, hU, hxU, n, c, ga_, hdesc, hinj, hcoord⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf (H :: N) x U1_ hU1 hxU1 (c0_.restrict hU1U0) a0_ hdesc1
      (fun i i' hi hi' j h1 h2 => hinj0_ i hi i' hi' j h1 h2)
  have h0len : 0 < (H :: N).length := by simp
  have hH0 : restrictIdeal ((H :: N)[0]'h0len) U = restrictIdeal H U := by simp
  obtain ⟨j0_, hj0_⟩ : ∃ j0_, ga_ 0 = some j0_ := by
    cases hc : ga_ 0 with
    | none =>
        refine absurd hxH $ notMem_support_of_restrictIdeal_eq_top H U x hxU ?_
        rw [← hH0]
        exact (hdesc 0 h0len).1 hc
    | some j => exact ⟨j, rfl⟩
  have hHU := (hdesc 0 h0len).2 j0_ hj0_
  rw [hH0] at hHU
  have hyU : y ∈ siPre H U := by
    show H.subschemeι.base y ∈ U
    rwa [hyx]
  have hWaff := isAffineOpen_preimage_subschemeio H hU
  have hprimeEq : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      = comap (H.subschemeι.appLE U (siPre H U) le_rfl).hom
          (hWaff.primeIdealOf ⟨y, hyU⟩).asIdeal := by
    rw [appLE_eq_app]
    have hpt : (⟨H.subschemeι.base y, hyU⟩ : U) = ⟨x, hxU⟩ := m26 hyx
    rw [← hpt]
    exact primeIdealOf_eq_comap_primeIdealOf H.si hU hWaff hyU
  have hyZ : y ∈ spI Z := by
    refine mem_support_of_ideal_le_primeIdealOf Z hWaff hyU ?_
    intro a ha
    obtain ⟨b, hb⟩ : ∃ b, (H.subschemeι.appLE U (siPre H U) le_rfl).hom b = a := by
      obtain ⟨b, hb⟩ := subschemeι_app_surjective H ⟨U, hU⟩ a
      refine ⟨b, ?_⟩
      rwa [appLE_eq_app]
    have hbker : b ∈ (siI Z ≫ siI H).ker.ideal ⟨U, hU⟩ := by
      rwa [ker_comp_subschemeio_ideal_eq_comap H Z hU, mem_comap, hb]
    have hmem := ideal_le_primeIdealOf (siI Z ≫ siI H).ker hU hxU hx hbker
    rwa [hprimeEq, mem_comap, hb] at hmem
  obtain ⟨V, hyV, m, c', a', S', hinj', hnone', hsome', hZV⟩ := hZ y hyZ
  obtain ⟨V1, hV1_, hyV1, hV1V⟩ := exists_isAffineOpen_mem_and_subset hyV
  obtain ⟨U', hU'aff, hyU', hW'V1, hU'U⟩ :
      ∃ U', IsAffineOpen U' ∧ y ∈ siPre H U' ∧
        (H.si.pre U') ≤ V1 ∧ U' ≤ U := by
    obtain ⟨g, hyg, hgV, hgU⟩ := exists_basicOpen_subschemeio_preimage_le H hU V1 hyU hyV1
    exact ⟨bOpn P g, hU.basicOpen g, hyg, hgV, hgU⟩
  have hxU' : x ∈ U' := by
    rwa [← hyx]
  have hW'aff := isAffineOpen_preimage_subschemeio H hU'aff
  have hHU' :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c H {j0_} hHU
  have hZW' : restrictIdeal Z (siPre H U')
      = ((c'.restrict hV1V).restrict hW'V1).coordIdeal S' := by
    have h1 :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hV1V c' Z S' hZV
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hW'V1 (c'.restrict hV1V) Z S' h1
  have hmn :=
    etaleChart_numCoords_add_one_of_hypersurface p H hU'aff (c.restrict hU'U) j0_ hHU' hW'aff
      ((c'.restrict hV1V).restrict hW'V1) y hyU' hyU'
  have hPx' : (hU'aff.primeIdealOf ⟨x, hxU'⟩).asIdeal
      = comap (H.subschemeι.appLE U' (siPre H U') le_rfl).hom
          (hW'aff.primeIdealOf ⟨y, hyU'⟩).asIdeal := by
    rw [appLE_eq_app]
    have hpt : (⟨H.subschemeι.base y, hyU'⟩ : U') = ⟨x, hxU'⟩ := m26 hyx
    rw [← hpt]
    exact primeIdealOf_eq_comap_primeIdealOf H.si hU'aff hW'aff hyU'
  have hpisurj : Function.Surjective
      (H.subschemeι.appLE U' (siPre H U') le_rfl).hom := by
    rw [appLE_eq_app]
    exact subschemeι_app_surjective H ⟨U', hU'aff⟩
  have hcomapideal := fun D =>
    comap_ideal_eq_map_appLE D H.si ⟨U', hU'aff⟩
      ⟨siPre H U', hW'aff⟩ le_rfl
  have hNsome : ∀ i (hi : i < N.length) (j : Fin n), ga_ (i + 1) = some j →
      restrictIdeal (N[i]'hi) U' = (c.restrict hU'U).coordIdeal {j} := by
    intro i hi j hij
    refine restrictIdeal_eq_restrict_coordIdeal_of_le hU'U c _ {j} ?_
    have h := (hdesc (i + 1) (by simpa using hi)).2 j hij
    simpa using h
  have hxN : ∀ i (hi : i < N.length) (j : Fin n), ga_ (i + 1) = some j →
      x ∈ spI (N[i]'hi) := by
    intro i hi j hij
    refine mem_support_of_ideal_le_primeIdealOf _ hU hxU ?_
    have hid : (N[i]'hi).ideal ⟨U, hU⟩
        = span (c.coord '' ((({j} : FinSet n)) : Set (Fin n))) := by
      refine c.ideal_eq_span_coord hU _ {j} ?_
      have h := (hdesc (i + 1) (by simpa using hi)).2 j hij
      simpa using h
    rw [hid, span_le]
    rintro z ⟨j', hj', rfl⟩
    have hjj : j' = j := by simpa using hj'
    subst hjj
    exact hcoord (i + 1) (by simpa using hi) j' hij
  have hyND : ∀ i (hi : i < N.length) (j : Fin n), ga_ (i + 1) = some j →
      y ∈ spI (cmI (N[i]'hi) H.si) := by
    intro i hi j hij
    refine mem_support_of_ideal_le_primeIdealOf _ hW'aff hyU' ?_
    rw [hcomapideal, map_le_iff_le_comap, ← hPx']
    exact ideal_le_primeIdealOf _ hU'aff hxU' $ hxN i hi j hij
  have ha'some : ∀ i (hi : i < N.length) (j : Fin n), ga_ (i + 1) = some j →
      ∃ b, a' i = some b := by
    intro i hi j hij
    cases hb : a' i with
    | some b => exact ⟨b, rfl⟩
    | none =>
        exfalso
        have hiE : i < (N.map fun D => cmI D H.si).length := by simpa using hi
        have htop := hnone' i hiE hb
        have hE : ((N.map fun D => cmI D H.si)[i]'hiE)
            = cmI (N[i]'hi) H.si := by simp
        rw [hE] at htop
        exact notMem_support_of_restrictIdeal_eq_top _ _ y hyU' (restrictIdeal_eq_top_of_le _ (le_trans hW'V1 hV1V) htop) $ hyND i hi j hij
  have hinja : ∀ i i', i < N.length → i' < N.length → ∀ b,
      a' i = some b → a' i' = some b → i = i' := by
    intro i i' hi hi' b h1 h2
    exact hinj' i (by simpa using hi) i' (by simpa using hi') b h1 h2
  have hinjga : ∀ i i', i < N.length → i' < N.length → ∀ j,
      ga_ (i + 1) = some j → ga_ (i' + 1) = some j → i = i' := by
    intro i i' hi hi' j h1 h2
    have h := hinj (i + 1) (i' + 1) (by simpa using hi) (by simpa using hi') j h1 h2
    omega
  have hj0ne : ∀ i, i < N.length → ga_ (i + 1) ≠ some j0_ := by
    intro i hi hcon
    have h := hinj 0 (i + 1) h0len (by simpa using hi) j0_ hj0_ hcon
    omega
  obtain ⟨rh_, hrh_⟩ := exists_equiv_subtype_ne_compatible hmn j0_ N.length (fun i => ga_ (i + 1)) a'
    hinjga hinja hj0ne (fun i hi j hij => ha'some i hi j hij)
  have hmatched : ∀ i (hi : i < N.length) (j : Fin n) (b : Fin m),
      ga_ (i + 1) = some j → a' i = some b →
      (∃ v : (Γ(subS H, siPre H U'))ˣ,
        (H.subschemeι.appLE U' (siPre H U') le_rfl).hom ((c.restrict hU'U).coord j)
          = (v : Γ(subS H, siPre H U')) *
              ((c'.restrict hV1V).restrict hW'V1).coord b) ∧
      ((c'.restrict hV1V).restrict hW'V1).coord b ∈
        (hW'aff.primeIdealOf ⟨y, hyU'⟩).asIdeal := by
    intro i hi j b hij hib
    have hiE : i < (N.map fun D => cmI D H.si).length := by simpa using hi
    have hE : ((N.map fun D => cmI D H.si)[i]'hiE)
        = cmI (N[i]'hi) H.si := by simp
    have hcoordW : restrictIdeal (cmI (N[i]'hi) H.si) (siPre H U')
        = ((c'.restrict hV1V).restrict hW'V1).coordIdeal {b} := by
      have h1 := hsome' i hiE b hib
      rw [hE] at h1
      have h2 := restrictIdeal_eq_restrict_coordIdeal_of_le hV1V c' _ {b} h1
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hW'V1 (c'.restrict hV1V) _ {b} h2
    have hspanW : (cmI (N[i]'hi) H.si).ideal ⟨siPre H U', hW'aff⟩
        = span {((c'.restrict hV1V).restrict hW'V1).coord b} := by
      have h := ((c'.restrict hV1V).restrict hW'V1).ideal_eq_span_coord hW'aff _ {b} hcoordW
      simpa using h
    have hspanU : (N[i]'hi).ideal ⟨U', hU'aff⟩
        = span {(c.restrict hU'U).coord j} := by
      have h := (c.restrict hU'U).ideal_eq_span_coord hU'aff _ {j} (hNsome i hi j hij)
      simpa using h
    have hmapeq : span {(H.subschemeι.appLE U' (siPre H U') le_rfl).hom
          ((c.restrict hU'U).coord j)}
        = span {((c'.restrict hV1V).restrict hW'V1).coord b} := by
      rw [← hspanW, hcomapideal, hspanU, m218, image_singleton]
    refine ⟨exists_unit_mul_coord_of_span_eq (siI H ≫ p) hW'aff
      ((c'.restrict hV1V).restrict hW'V1) b _ hmapeq, ?_⟩
    rw [← span_singleton_le_iff_mem, ← hspanW]
    exact ideal_le_primeIdealOf _ hW'aff hyU' $ hyND i hi j hij
  have hlift : ∀ b, ∃ (wbb : P.sec U')
      (vbb : (Γ(subS H, siPre H U'))ˣ),
      (H.subschemeι.appLE U' (siPre H U') le_rfl).hom wbb
          = (vbb : Γ(subS H, siPre H U')) *
              ((c'.restrict hV1V).restrict hW'V1).coord b ∧
      (vbb = 1 ∨ ((c'.restrict hV1V).restrict hW'V1).coord b ∈
        (hW'aff.primeIdealOf ⟨y, hyU'⟩).asIdeal) ∧
      (∀ i, i < N.length → ∀ j, ga_ (i + 1) = some j → a' i = some b →
        wbb = (c.restrict hU'U).coord j) := by
    intro b
    by_cases hb : ∃ i, ∃ _ : i < N.length, ∃ j : Fin n, ga_ (i + 1) = some j ∧ a' i = some b
    obtain ⟨i, hi, j, hij, hib⟩ := hb
    obtain ⟨⟨v, hv⟩, hmem⟩ := hmatched i hi j b hij hib
    refine ⟨(c.restrict hU'U).coord j, v, hv, inr hmem, ?_⟩
    intro i' hi' j' hij' hib'
    have hii := hinja i' i hi' hi b hib' hib
    subst hii
    have hjj := inj $ st_ hij' hij
    rw [hjj]
    obtain ⟨wbb, hwbb⟩ := hpisurj $ ((c'.restrict hV1V).restrict hW'V1).coord b
    refine ⟨wbb, 1, ?_, inl rfl, ?_⟩
    rw [hwbb]
    simp
    intro i hi j hij hib
    exact absurd ⟨i, hi, j, hij, hib⟩ hb
  choose wb vb hvb1 hvb2 hvb3 using hlift
  obtain ⟨w, hw0, hwrh⟩ : ∃ w : UFin n → P.sec U',
      w (up j0_) = (c.restrict hU'U).coord j0_ ∧
      ∀ b : Fin m, w (up (rh_ b : Fin n)) = wb b := by
    refine ⟨fun t => if h : t.down = j0_ then (c.restrict hU'U).coord j0_
      else wb (rh_.symm ⟨t.down, h⟩), dif_pos rfl, ?_⟩
    intro b
    have hne := (rh_ b).2
    show (if h : (rh_ b : Fin n) = j0_ then (c.restrict hU'U).coord j0_
      else wb (rh_.symm ⟨(rh_ b : Fin n), h⟩)) = wb b
    rw [dif_neg hne]
    congr 1
    have hsub : (⟨(rh_ b : Fin n), hne⟩ : {j : Fin n // j ≠ j0_}) = rh_ b := rfl
    rw [hsub, symm_apply_apply]
  let instkU := sectionsAlgebra k p U'
  let instcU :=
    (c.restrict hU'U).algebra
  have instTU :=
    (c.restrict hU'U).isScalarTower
  have instFEU :=
    (c.restrict hU'U).algebra_formallyEtale hU'aff
  let instkW :=
    sectionsAlgebra k (siI H ≫ p) (siPre H U')
  let instcW := ((c'.restrict hV1V).restrict hW'V1).algebra
  have instTW := ((c'.restrict hV1V).restrict hW'V1).isScalarTower
  have instFEW :=
    ((c'.restrict hV1V).restrict hW'V1).algebra_formallyEtale hW'aff
  let _a3 := (c.restrict hU'U).restrictToSubscheme hU'aff H {j0_} hHU'
  let instcA :=
    _a3.algebra
  have instTA :=
    _a3.isScalarTower
  have instFEA :=
    _a3.algebra_formallyEtale hW'aff
  have hcard : n - ({j0_} : FinSet n).card = m := by
    rw [card_singleton]
    omega
  let _a0 := Fin $ n - ({j0_} : FinSet n).card
  have hioAex : ∀ b, ∃ i,
      complOrderEmb n {j0_} i = (rh_ b : Fin n) := by
    intro b
    exact exists_complOrderEmb_eq n {j0_} (by simpa using (rh_ b).2)
  choose ioA hioA using hioAex
  have hioAinj : m120 ioA := by
    intro a b hab
    have h : (rh_ a : Fin n) = (rh_ b : Fin n) := by rw [← hioA a, ← hioA b, hab]
    exact rh_.injective (m26 h)
  have hioAbij : Bijective ioA := by
    refine (bijective_iff_injective_and_card ioA).mpr ⟨hioAinj, ?_⟩
    rw [card_fin, card_fin, hcard]
  have hcompat : ∀ a (r : P.sec U'),
      (H.subschemeι.appLE U' (siPre H U') le_rfl).hom
        (partialDeriv k (UFin n) U'.sec
          (up (rh_ a : Fin n)) r)
      = partialDeriv k
          (ULift _a0)
          Γ(subS H, siPre H U') (up (ioA a))
          ((H.subschemeι.appLE U' (siPre H U') le_rfl).hom r) := by
    intro a r
    have h := appLE_subschemeio_chartPartialDeriv_complOrderEmb hU'aff (c.restrict hU'U) H j0_ hHU' (ioA a) r
    rwa [hioA a] at h
  have hdet : IsUnit (m53 fun a b =>
      partialDeriv k
        (ULift _a0)
        Γ(subS H, siPre H U') (up (ioA a))
        (((c'.restrict hV1V).restrict hW'V1).coord b)).det := by
    have hta : ∃ ta_ : UFin m ≃ ULift _a0,
        ∀ t, ta_ t = up (ioA t.down) :=
      ⟨ulift.trans ((ofBijective ioA hioAbij).trans ulift.symm), fun t => rfl⟩
    obtain ⟨ta_, htaapp⟩ := hta
    let _m0 := (basisKaehler k (ULift _a0) Γ(subS H, siPre H U')).reindex ta_.symm
    let _a5 := basisKaehler k (UFin m) Γ(subS H, siPre H U')
    have h1 : IsUnit (_m0.det
        _a5) :=
      isUnit_det _ _
    have h2 : _m0.det
        _a5
        = (m53 fun a b =>
            partialDeriv k
              (ULift _a0)
              Γ(subS H, siPre H U') (up (ioA a))
              (((c'.restrict hV1V).restrict hW'V1).coord b)).det := by
      rw [det_apply, ← det_submatrix_equiv_self ulift
        (m53 fun a b =>
          partialDeriv k
            (ULift _a0)
            Γ(subS H, siPre H U') (up (ioA a))
            (((c'.restrict hV1V).restrict hW'V1).coord b))]
      congr 1
      ext s t
      rw [toMatrix_apply, repr_reindex_apply, symm_symm,
        basisKaehler_apply, htaapp,
        ← partialDeriv_apply,
        ((c'.restrict hV1V).restrict hW'V1).etaleCoordinates_coord t.down]
      rfl
    rwa [h2] at h1
  let _a12 := Fin $ m + 1
  obtain ⟨F, hF0, hFsucc⟩ : ∃ F : _a12 → UFin n,
      F 0 = up j0_ ∧ ∀ b : Fin m, F b.succ = up (rh_ b : Fin n) := by
    refine ⟨fun t => if h : t = 0 then up j0_
      else up (rh_ (t.pred h) : Fin n), ?_, ?_⟩
    show (if h : (0 : _a12) = 0 then up j0_
      else up (rh_ ((0 : _a12).pred h) : Fin n)) = up j0_
    exact dif_pos rfl
    intro b
    show (if h : b.succ = 0 then up j0_
      else up (rh_ (b.succ.pred h) : Fin n)) = up (rh_ b : Fin n)
    rw [dif_neg (succ_ne_zero b), pred_succ]
  have hbij : Bijective F := by
    refine (bijective_iff_injective_and_card F).mpr ⟨?_, ?_⟩
    intro t1_ t2_ ht
    rcases eq_zero_or_eq_succ t1_ with rfl | ⟨b1_, rfl⟩
    rcases eq_zero_or_eq_succ t2_ with rfl | ⟨b2_, rfl⟩
    rfl
    rw [hF0, hFsucc] at ht
    exact absurd (congrArg down ht).symm (rh_ b2_).2
    rcases eq_zero_or_eq_succ t2_ with rfl | ⟨b2_, rfl⟩
    rw [hF0, hFsucc] at ht
    exact absurd (congrArg down ht) (rh_ b1_).2
    rw [hFsucc, hFsucc] at ht
    exact congrArg Fin.succ $ rh_.injective (m26 (congrArg down ht))
    rw [card_fin, card_ulift, card_fin, hmn]
  obtain ⟨e, he0, hesucc⟩ : ∃ e : UFin n ≃ Fin (m + 1),
      e.symm 0 = up j0_ ∧ ∀ b : Fin m, e.symm b.succ = up (rh_ b : Fin n) := by
    refine ⟨(ofBijective F hbij).symm, ?_, fun b => ?_⟩
    rwa [symm_symm]
    rw [symm_symm]
    exact hFsucc b
  have hcol : ∀ a,
      (m53 fun a b =>
        partialDeriv k (UFin n) U'.sec a (w b)) a (e.symm 0)
        = if a = e.symm 0 then (1 : P.sec U') else 0 := by
    intro a
    rw [he0]
    show partialDeriv k (UFin n) U'.sec a (w (up j0_))
      = if a = up j0_ then (1 : P.sec U') else 0
    rw [hw0, ← (c.restrict hU'U).etaleCoordinates_coord j0_]
    exact partialDeriv_coord k (UFin n) U'.sec a $ up j0_
  have hsub : (m53 fun a b =>
        partialDeriv k (UFin n) U'.sec a (w b)).submatrix
        (fun i : Fin m => e.symm i.succ) (fun i : Fin m => e.symm i.succ)
      = m53 fun a b : Fin m =>
        partialDeriv k (UFin n) U'.sec
          (up (rh_ a : Fin n)) (wb b) := by
    ext a b
    show partialDeriv k (UFin n) U'.sec
        (e.symm a.succ) (w (e.symm b.succ))
      = partialDeriv k (UFin n) U'.sec
        (up (rh_ a : Fin n)) (wb b)
    rw [hesucc a, hesucc b, hwrh b]
  have hM := congrArg det hsub
  rw [← det_eq_det_submatrix_of_col_eq_single e _ hcol] at hM
  have hnotmem := det_derivation_notMem_comap_of_eq_one_or_mem (k := k) (ι := Fin m)
    (H.subschemeι.appLE U' (siPre H U') le_rfl).hom
    (fun a => partialDeriv k (UFin n) U'.sec
      (up (rh_ a : Fin n)))
    (fun a => partialDeriv k
      (ULift _a0)
      Γ(subS H, siPre H U') (up (ioA a)))
    hcompat wb vb (fun b => ((c'.restrict hV1V).restrict hW'V1).coord b) hvb1
    (hW'aff.primeIdealOf ⟨y, hyU'⟩).asIdeal
    (hW'aff.primeIdealOf ⟨y, hyU'⟩).isPrime.ne_top hvb2 hdet
  have hdet0 := hnotmem
  rw [← hPx', ← hM] at hdet0
  have hdet := hdet0
  have _i5 : (basisKaehler k (UFin n) U'.sec).det (fun i : (UFin n) => m13 k U'.sec $ w i) = (m53 fun i j : (UFin n) => partialDeriv k (UFin n) U'.sec i $ w j).det := by
    let ι := UFin n
    let S := P.sec U'
    have hM : (basisKaehler k ι S).toMatrix
          (fun i => m13 k S $ w i)
        = m53 fun i j => partialDeriv k ι S i (w j) := by
      ext i j
      simp [of_apply, toMatrix_apply]
      rw [partialDeriv_apply]
    rw [det_apply, hM]
  rw [← _i5] at hdet
  obtain ⟨V', hV'aff, hV'U', hxV', c3_, hc3_⟩ :=
    exists_etaleChart_restrict_coord_eq_of_jacobianDet_notMem hU'aff
      (c.restrict hU'U) hxU' w hdet
  have hV'U := le_trans hV'U' hU'U
  have hpreV' : (siPre H V') ≤ (siPre H U') := fun a ha => hV'U' ha
  refine ⟨V', hV'aff, hxV', n, c3_, j0_, fun i => ga_ (i + 1),
    S'.image (fun b => (rh_ b : Fin n)), ?_, ?_, ?_, ?_, ?_⟩
  refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV'aff c3_ H {j0_} ?_
  have h1 : H.ideal ⟨U', hU'aff⟩ = span {(c.restrict hU'U).coord j0_} := by
    have h := (c.restrict hU'U).ideal_eq_span_coord hU'aff H {j0_} hHU'
    simpa using h
  have h2 := ideal_eq_span_image_map_of_le H hU'aff hV'aff hV'U' _ h1
  rw [h2]
  congr 1
  rw [coe_singleton, image_singleton, image_singleton, hc3_ j0_, hw0]
  intro i hi hnone
  have h := (hdesc (i + 1) (by simpa using hi)).1 hnone
  refine restrictIdeal_eq_top_of_le _ hV'U ?_
  simpa using h
  intro i hi j hij
  obtain ⟨b, hb⟩ := ha'some i hi j hij
  have hrhb := hrh_ i hi j b hij hb
  have hwj : w (up j) = (c.restrict hU'U).coord j := by
    have h1 : w (up j) = wb b := by
      rw [← hrhb]
      exact hwrh b
    rw [h1]
    exact hvb3 b i hi j hij hb
  refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV'aff c3_ _ {j} ?_
  have h1 : (N[i]'hi).ideal ⟨U', hU'aff⟩ = span {(c.restrict hU'U).coord j} := by
    have h := (c.restrict hU'U).ideal_eq_span_coord hU'aff _ {j} (hNsome i hi j hij)
    simpa using h
  have h2 := ideal_eq_span_image_map_of_le (N[i]'hi) hU'aff hV'aff hV'U' _ h1
  rw [h2]
  congr 1
  rw [coe_singleton, image_singleton, image_singleton, hc3_ j, hwj]
  intro i i' hi hi' j h1 h2
  exact hinjga i i' hi hi' j h1 h2
  have hZideal :=
    ((c'.restrict hV1V).restrict hW'V1).ideal_eq_span_coord hW'aff Z S' hZW'
  rw [ideal_eq_span_image_map_of_le Z hW'aff (isAffineOpen_preimage_subschemeio H hV'aff) hpreV' _ hZideal, coe_image, ← image_comp, ← image_comp]
  refine (span_image_eq_of_isUnit_mul (S' : Set (Fin m)) _ _ ?_).symm
  intro b hb
  let _a11 := H.subscheme.presheaf.map (homOfLE hpreV').op
  have h1 : (H.subschemeι.appLE V' (siPre H V') le_rfl).hom
        (c3_.coord (rh_ b : Fin n))
      = _a11.hom
          ((vb b : Γ(subS H, siPre H U'))
            * ((c'.restrict hV1V).restrict hW'V1).coord b) := by
    rw [hc3_ (rh_ b : Fin n), appLE_preimage_naturality H.si hV'U' hpreV', hwrh b,
      hvb1 b]
  exact ⟨_a11.hom
      (vb b : Γ(subS H, siPre H U')), IsUnit.map _ (vb b).isUnit,
    h1.trans (map_mul _ _ _)⟩

end

theorem hasStrictNormalCrossingsWith_ker_cons_of_comap :
    ∀ (k : Type) [Field k] [CharZero k] P
      (p : P ⟶ Sp k) [Smooth p]
      (H : ISD P) (N : Bdy P),
      InStrictNormalCrossingPosition p (H :: N) →
      ∀ Z : H.subscheme.IdealSheafData,
        HasStrictNormalCrossingsWith (subschemeι H ≫ p) Z (N.map fun D => D.comap H.si) →
        HasStrictNormalCrossingsWith p (subschemeι Z ≫ subschemeι H).ker (H :: N) := by
  intro k _ _ P p _ H N hN Z hZ
  exact hasStrictNormalCrossingsWith_ker_cons_of_hasLocalCoordsOnSmoothHypersurface p H N Z hN hZ
    (hasLocalCoordsOnSmoothHypersurface_of_comap p H N Z hN hZ)

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

section
variable {A B C D : Sch} {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ D} {d : C ⟶ D} (sq : IsPullback a b c d)
include sq
theorem flat_of_isPullback (hd : Flat d) :
    Flat a := by
  have : Flat $ pullback.snd d c := inferInstance
  rw [← sq.flip.isoPullback_hom_snd]
  infer_instance

theorem isClosedImmersion_of_isPullback (hd : IsClosedImmersion d) : IsClosedImmersion a := by
  have : IsClosedImmersion $ pullback.snd d c := inferInstance
  rw [← sq.flip.isoPullback_hom_snd]
  infer_instance
end

namespace IsPushforwardBlowupSeq

theorem of_flat_isPullback {S X S' X'}
    j j' g p
    [IsClosedImmersion j] [IsClosedImmersion j'] [Flat g]
    (hsq : IsPullback j' p g j)
    (s : SequenceOfBlowups S) (t : SequenceOfBlowups X) (s' : SequenceOfBlowups S') (t' : SequenceOfBlowups X')
    (hnoeth : ∀ i, i ≤ t.length → IsLocallyNoetherian (schemeAt t i))
    (hnoeth' : ∀ i, i ≤ t'.length → IsLocallyNoetherian (schemeAt t' i))
    (hpush : IsPushforwardBlowupSeq j s t)
    (hs' : IsStrictPullbackBlowupSeq p s' s)
    (ht' : IsStrictPullbackBlowupSeq g t' t) :
    IsPushforwardBlowupSeq j' s' t' := by
  obtain ⟨hlen1, σ, hsgci, hsg0, hsgstep, hsgcen, hsgker⟩ := hpush
  obtain ⟨hlen2, ta_, hta0, htastep, htacen⟩ := hs'
  obtain ⟨hlen3, rh_, hrh0, hrhstep, hrhcen⟩ := ht'
  have hA : ∀ i, i ≤ s'.length → i ≤ s.length := fun i hi => by omega
  have hB : ∀ i, i ≤ s'.length → i ≤ t'.length := fun i hi => by omega
  have Pt := isPullback_projectionToBase_of_isPullback_blowupMorphism g t' t t'.length rh_ hrh0 hrhstep
  have Ps := isPullback_projectionToBase_of_isPullback_blowupMorphism p s' s s'.length ta_ hta0 htastep
  have hsgS : ∀ b, ∀ hb, σ b hb ≫ t.projectionToBase b = s.projectionToBase b ≫ j := by
    intro b
    induction b with
    | zero =>
      intro hb
      rwa [projectionToBase_zero, projectionToBase_zero]
    | succ n ih =>
      intro hb
      have hn : n < s.length := hb
      rw [projectionToBase_succ, projectionToBase_succ, ← assoc, hsgstep n hn,
        assoc, ih hn.le, assoc]
  have hflatrh : ∀ i, ∀ hi, Flat (rh_ i hi) := fun i hi =>
    flat_of_isPullback (Pt i hi) inferInstance
  have hw : ∀ i, ∀ hi,
      (ta_ i hi ≫ σ i (hA i hi)) ≫ t.projectionToBase i = (s'.projectionToBase i ≫ j') ≫ g := by
    intro i hi
    rw [assoc, hsgS i $ hA i hi, ← assoc, (Ps i hi).w, assoc,
      ← hsq.w, assoc]
  obtain ⟨σ', hsg'1, hsg'2⟩ :
      ∃ σ' : ∀ i, i ≤ s'.length → (schemeAt s' i ⟶ schemeAt t' i),
        (∀ i, ∀ hi,
          σ' i hi ≫ rh_ i (hB i hi) = ta_ i hi ≫ σ i (hA i hi)) ∧
        (∀ i, ∀ hi,
          σ' i hi ≫ t'.projectionToBase i = s'.projectionToBase i ≫ j') :=
    ⟨fun i hi => (Pt i (hB i hi)).lift (ta_ i hi ≫ σ i (hA i hi)) (s'.projectionToBase i ≫ j') (hw i hi),
      fun i hi => (Pt i (hB i hi)).lift_fst _ _ (hw i hi),
      fun i hi => (Pt i (hB i hi)).lift_snd _ _ (hw i hi)⟩
  have Psq : ∀ i, ∀ hi,
      IsPullback (σ' i hi) (ta_ i hi) (rh_ i (hB i hi)) (σ i (hA i hi)) := by
    intro i hi
    refine IsPullback.of_right ?_ (hsg'1 i hi) (Pt i (hB i hi)).flip
    rw [hsg'2 i hi, hsgS i (hA i hi)]
    exact ((Ps i hi).flip).paste_horiz hsq
  have hci' : ∀ i, ∀ hi, IsClosedImmersion (σ' i hi) := fun i hi =>
    isClosedImmersion_of_isPullback (Psq i hi) (hsgci i (hA i hi))
  have hzero' : σ' 0 (zero_le _) ≫ sbIzH t' = sbIzH s' ≫ j' := by
    have h := hsg'2 0 $ zero_le _
    rwa [projectionToBase_zero, projectionToBase_zero] at h
  have hstep' : ∀ i, ∀ hi : i < s'.length,
      σ' (i + 1) hi ≫ sbTrS t' i = sbTrS s' i ≫ σ' i hi.le := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    refine (Pt i (hB i hi.le)).hom_ext ?_ ?_
    simp [assoc]
    rw [← (hrhstep i hit).w, hsg'1 i hi.le, ← assoc, hsg'1 (i + 1) hi,
      assoc, hsgstep i his, ← assoc, (htastep i hi).w, assoc]
    simp [assoc]
    rw [← projectionToBase_succ, hsg'2 (i + 1) hi, hsg'2 i hi.le,
      projectionToBase_succ, assoc]
  have hcen' : ∀ i, ∀ hi : i < s'.length,
      center t' i = imageIdealSheaf (σ' i hi.le) (center s' i) := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    have := hsgci i $ hA i hi.le
    have : QuasiCompact (σ i (hA i hi.le)) := inferInstance
    have := hflatrh i $ hB i hi.le
    rw [hrhcen i hit, htacen i hi, hsgcen i his, ← map_eq_imageIdealSheaf, ← map_eq_imageIdealSheaf]
    exact comap_map_eq_map_comap_of_isPullback (Psq i hi.le).flip (center s i)
  have hker' : ∀ i, ∀ hi : i < s'.length,
      (σ' (i + 1) hi).ker =
        p6 (sbTrS t' i) (center t' i) (σ' i hi.le).ker := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    have hitt : i < t.length := by omega
    have := hsgci i $ hA i hi.le
    have := hsgci (i + 1) $ hA (i + 1) hi
    have := hci' i hi.le
    have := hci' (i + 1) hi
    have := hflatrh i $ hB i hi.le
    let _a0 := hB (i + 1) hi
    have := hflatrh (i + 1) _a0
    have := hnoeth (i + 1) (by omega)
    have := hnoeth' (i + 1) (by omega)
    rw [ker_eq_comap_ker_of_isPullback_of_flat (Psq (i + 1) hi).flip,
      ker_eq_comap_ker_of_isPullback_of_flat (Psq i hi.le).flip, hsgker i his, hrhcen i hit]
    exact comap_strictTransform_of_flat_of_isLocallyNoetherian (sbTrS t i)
      (rh_ i (hB i hi.le)) (sbTrS t' i) (rh_ (i + 1) _a0) (hrhstep i hit)
      (center t i) (σ i (hA i hi.le)).ker (t.isBlowupAlongIdealSheaf_blowupMorphism i hitt)
  refine m157 ?_ (Exists.intro σ' ⟨hci', hzero', hstep', hcen', hker'⟩)
  omega

end IsPushforwardBlowupSeq




theorem ker_le_ker_of_comp_eq {A B T : Sch} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    (h : e ≫ g = f) : g.ker ≤ f.ker := by
  subst h
  exact le_ker_comp e g


section
variable {X X1 S S1_ : Sch} {k : Type} [Field k] (p : X ⟶ Sp k) (pi_ : X1 ⟶ X) (Z : ISD X) (ι : S ⟶ X) (io1 : S1_ ⟶ X1) (rh_ : S1_ ⟶ S) [IsClosedImmersion ι] [IsClosedImmersion io1] [IsLocallyNoetherian X1] [IsLocallyNoetherian S1_] (hsq : io1 ≫ pi_ = rh_ ≫ ι) (hker : ker io1 = strictTransform pi_ Z (ker ι)) (E : Bdy X) (hsnc : HasStrictNormalCrossingsWith p Z (ker ι :: E)) (hHZ : ker ι ≤ Z) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
include hsq hker hsnc hHZ hpi_
theorem comap_strictTransform_of_closedImmersion_commSq
    (D : ISD X) (hD : D ∈ E) :
    (strictTransform pi_ Z D).comap io1 =
      strictTransform rh_ (Z.comap ι) (D.comap ι) := by
  let _a5 := strictTransform pi_ Z (ker ι)
  let _a9 := subschemeι (ker ι)
  obtain ⟨e, e1_, he, he1_, hcomm⟩ : ∃ (e : S ≅ subS (ker ι)) (e1_ : S1_ ≅ subS _a5), isoH e ≫ _a9 = ι ∧ isoH e1_ ≫ subschemeι _a5 = io1 ∧ isoH e1_ ≫ strictTransformSubschemeLift pi_ Z (ker ι) = rh_ ≫ isoH e := by
    let _c0 := _a5
    have hkH : (ker ι).subschemeι.ker = ker ι :=
      q2 _
    have hkT : _c0.subschemeι.ker
        = _a5 :=
      q2 _
    let _a1 := lift (ker ι).subschemeι ι (le_of_eq hkH)
    have hu : _a1 ≫
        _a9 = ι := lift_fac _ _ _
    let _m0 := _a1
    have : IsIso _m0 :=
      isIso_of_ker_eq ι (ker ι).subschemeι _ hu hkH.symm
    let _a0 := lift _c0.subschemeι io1 (le_of_eq (tr_ hkT hker.symm))
    have hu1_ : _a0 ≫
        subschemeι _c0 = io1 :=
      lift_fac _ _ _
    have : IsIso _a0 :=
      isIso_of_ker_eq io1 _c0.subschemeι _
        hu1_ (tr_ hker hkT.symm)
    refine ⟨asIso _m0,
      asIso _a0, hu, hu1_, ?_⟩
    rw [← cancel_mono (ker ι).subschemeι, assoc,
      strictTransformSubschemeLift_comp_subschemeio pi_ Z (ker ι), ← assoc]
    simp only [asIso_hom]
    rw [hu1_, assoc, hu, hsq]
  have : IsLocallyNoetherian _a5.subscheme :=
    isLocallyNoetherian_subscheme _
  have hq := isBlowupAlongIdealSheaf_strictTransformSubschemeLift pi_ Z (ker ι) hpi_
  let _a0 := strictTransformSubschemeLift pi_ Z (ker ι)
  let _a11 := isoH e1_ ≫ _a0
  have hfinal : _a11 ≫
      _a9 = rh_ ≫ ι := by
    rw [assoc, strictTransformSubschemeLift_comp_subschemeio, ← assoc, he1_, hsq]
  have hmain := comap_strictTransform_eq_strictTransformSubschemeLift p pi_ Z (ker ι) E hsnc hHZ hpi_ D hD
  let _a7 := Z.comap (ker ι).subschemeι
  let _a8 := D.comap (ker ι).subschemeι
  have _i10 : (strictTransform _a0 _a7 _a8).comap e1_.hom = strictTransform _a11 _a7 _a8 := by
    let Z := _a7
    let D := _a8
    have hRHS :=
      strictTransform_eq_of_comap_eq _a11 e1_.hom Z D (cmI Z _a0) (cmI D _a0)
        (by rw [comap_comp])
        (by rw [comap_comp])
    obtain ⟨m0, hiso, hm0_⟩ :=
      exists_iso_subscheme_comap_of_isIso e1_.hom (cmI D _a0)
    have hsupp : ((cmI Z _a0).comap e1_.hom).support.compl
        = isoH e1_ ⁻¹ᵁ (cmI Z _a0).support.compl := by
      rw [m19]
      rfl
    let _a1 := (cmI D _a0).comap e1_.hom
    have h1 : m0 ⁻¹ᵁ strictTransformOpens _a0 Z D
        = subschemeι _a1 ⁻¹ᵁ (isoH e1_ ⁻¹ᵁ (suppC (cmI Z _a0))) :=
      congrArg (fun w => w ⁻¹ᵁ (suppC (cmI Z _a0))) hm0_
    have hV' : strictTransformOpens e1_.hom (cmI Z _a0) (cmI D _a0)
        = m0 ⁻¹ᵁ strictTransformOpens _a0 Z D := by
      rw [h1]
      exact congrArg (fun W => subschemeι _a1 ⁻¹ᵁ W) hsupp
    let _a3 := subschemeι (cmI D _a0) ≫ inv e1_.hom
    have hm02 : m0 ≫ _a3
        = subschemeι _a1 := by
      rw [← assoc, hm0_, assoc, m118, comp_id]
    have hm03 : inv m0 ≫ subschemeι _a1
        = _a3 := by
      rw [IsIso.inv_comp_eq, hm02]
    have hinvle : strictTransformOpens _a0 Z D
        ≤ inv m0 ⁻¹ᵁ strictTransformOpens e1_.hom (cmI Z _a0) (cmI D _a0) := by
      rw [hV']
      have h3 : inv m0 ⁻¹ᵁ (m0 ⁻¹ᵁ strictTransformOpens _a0 Z D)
          = (inv m0 ≫ m0) ⁻¹ᵁ strictTransformOpens _a0 Z D := rfl
      rw [h3, m117]
      simp
    have hfac1 : (resLE m0 (strictTransformOpens _a0 Z D)
          (strictTransformOpens e1_.hom (cmI Z _a0) (cmI D _a0)) (le_of_eq hV'))
        ≫ (strictTransformio _a0 Z D ≫ inv e1_.hom)
        = strictTransformio e1_.hom (cmI Z _a0) (cmI D _a0) := by
      rw [strictTransformio_eq_io_comp_subschemeio _a0 Z D,
        strictTransformio_eq_io_comp_subschemeio e1_.hom (cmI Z _a0) (cmI D _a0),
        ← assoc, ← assoc, q4, assoc,
        assoc, hm02]
    have hfac2 : (resLE (inv m0)
          (strictTransformOpens e1_.hom (cmI Z _a0) (cmI D _a0))
          (strictTransformOpens _a0 Z D) hinvle)
        ≫ strictTransformio e1_.hom (cmI Z _a0) (cmI D _a0)
        = strictTransformio _a0 Z D ≫ inv e1_.hom := by
      rw [strictTransformio_eq_io_comp_subschemeio e1_.hom (cmI Z _a0) (cmI D _a0),
        strictTransformio_eq_io_comp_subschemeio _a0 Z D, ← assoc, q4,
        assoc, hm03, assoc]
    have hcomp : (strictTransformio _a0 Z D ≫ inv e1_.hom) ≫ isoH e1_
        = strictTransformio _a0 Z D := by simp_all
    have : QuasiCompact (strictTransformio _a0 Z D ≫ inv e1_.hom) := inferInstance
    have : QuasiCompact ((strictTransformio _a0 Z D ≫ inv e1_.hom) ≫ isoH e1_) := by
      rw [hcomp]
      infer_instance
    have hL := comap_ker_comp_of_isOpenImmersion
      (strictTransformio _a0 Z D ≫ inv e1_.hom) e1_.hom
    rw [hcomp] at hL
    rw [hRHS, strictTransform_eq_ker_strictTransformio _a0 Z D, hL,
      strictTransform_eq_ker_strictTransformio e1_.hom (cmI Z _a0) (cmI D _a0)]
    exact le_antisymm (ker_le_ker_of_comp_eq _ _ _ hfac1) $ ker_le_ker_of_comp_eq _ _ _ hfac2
  rw [← he1_, comap_comp, hmain, _i10]
  refine strictTransform_eq_of_comap_eq _ rh_ _ _ _ _ ?_ ?_
  rw [← comap_comp, ← comap_comp, hfinal]
  rw [← comap_comp, ← comap_comp, hfinal]

theorem map_comap_strictTransform_append_exceptionalIdeal :
    (List.map (strictTransform pi_ Z) E ++ [exceptionalIdeal pi_ Z]).map
        (fun A => A.comap io1) =
      List.map (strictTransform rh_ $ Z.comap ι) (List.map (fun D => D.comap ι) E) ++
        [exceptionalIdeal rh_ $ Z.comap ι] := by
  simp only [map_append, map_map, map_cons, map_nil]
  refine congrArg₂ (· ++ ·) ?_ ?_
  refine map_congr_left ?_
  intro D hD
  exact comap_strictTransform_of_closedImmersion_commSq p pi_ Z ι io1 rh_ hsq hker E hsnc hHZ hpi_ D hD
  have _i9 : (exceptionalIdeal pi_ Z).comap io1 = exceptionalIdeal rh_ (Z.comap ι) := by
    rw [exceptionalIdeal_eq_comap, exceptionalIdeal_eq_comap, ← comap_comp,
      ← comap_comp, hsq]
  rw [_i9]
end

end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

namespace TransportedDivisor

section
variable {X} (d : BlowupSequenceData X) (B : IdealSheafData (d.obj 0))
def iteratedComap (t : ℕ) :
    IdealSheafData $ d.obj t :=
  Nat.rec (motive := fun n => IdealSheafData $ d.obj n) B
    (fun n ih => ih.comap $ d.map n) t

@[simp]
theorem iteratedComap_zero :
    iteratedComap d B 0 = B := rfl

@[simp]
theorem iteratedComap_succ
    (t : ℕ) : iteratedComap d B (t + 1) = (iteratedComap d B t).comap (d.map t) := rfl
end

theorem support_strictTransform_subset_preimage {Y Y' : Sch} [IsLocallyNoetherian Y']
    (pi_ : Y' ⟶ Y) (Z D : ISD Y) :
    (support (strictTransform pi_ Z D) : Set Y') ⊆ ⇑pi_.base ⁻¹' (support D : Set Y) := by
  have hpre : ((spI (cmI D pi_) : Closeds Y') : Set Y') =
      preimage pi_.base D.support := by simp_all
  rw [support_strictTransform_eq_closure_sdiff pi_ Z D, ← hpre]
  exact closure_minimal sdiff_subset $ (cmI D pi_).support.2

theorem isSmoothDivisor_strictTransform_of_disjoint_center {k : Type} [Field k] [CharZero k] {X : Sch}
    (p : X ⟶ Sp k) (d : BlowupSequenceData X) (L : ℕ) (hL : L ≤ d.length)
    (hnoeth : ∀ t, t ≤ L → IsLocallyNoetherian (d.obj t))
    (hsm : ∀ t, t ≤ L → Smooth (projectionToBase d t ≫ p))
    (K A : ∀ t : ℕ, IdealSheafData $ d.obj t) (B0_ : IdealSheafData $ d.obj 0)
    (hK0 : K 0 = A 0 * B0_)
    (hdisj0 : Disjoint ((A 0).support : Set $ d.obj 0) ((B0_).support : Set $ d.obj 0))
    (hKsucc : ∀ t, t < L → K (t + 1) = strictTransform (d.map t) (d.center t) (K t))
    (hAsucc : ∀ t, t < L → A (t + 1) = strictTransform (d.map t) (d.center t) (A t))
    (hB0_ : IsSmoothDivisor (projectionToBase d 0 ≫ p) B0_)
    (hA : ∀ t, t ≤ L → IsSmoothDivisor (projectionToBase d t ≫ p) (A t))
    (hcent : ∀ t, t < L →
      Disjoint (((d.center t).support : Set $ d.obj t))
        ((iteratedComap d B0_ t).support : Set $ d.obj t)) :
    ∀ t, t ≤ L → IsSmoothDivisor (projectionToBase d t ≫ p) (K t) := by
  intro t ht
  have hst := hsm t ht
  have _i12 : ∀ t, t ≤ L → K t = A t * iteratedComap d B0_ t ∧ Disjoint (spI (A t) : Set $ d.obj t) (spI (iteratedComap d B0_ t) : Set $ d.obj t) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨hK0, hdisj0⟩
    | succ n ih =>
      intro hn
      have hlt := lt_of_succ_le hn
      have hle := le_of_lt hlt
      obtain ⟨hKn, hdn⟩ := ih hle
      have hnoe := hnoeth (n + 1) hn
      have hmul : K (n + 1) = A (n + 1) * iteratedComap d B0_ (n + 1) := by
        rw [hKsucc n hlt, hKn, strictTransform_mul_of_disjoint_support (d.map n) (d.center n)
          (A n) (iteratedComap d B0_ n) (hcent n hlt).symm, hAsucc n hlt, iteratedComap_succ]
      refine ⟨hmul, ?_⟩
      have hsub : (spI (A $ n + 1) : Set $ d.obj $ n + 1) ⊆
          (d.map n).base ⁻¹' (spI (A n) : Set $ d.obj n) := by
        rw [hAsucc n hlt]
        exact support_strictTransform_subset_preimage (d.map n) (d.center n) $ A n
      have hpre : ((spI (cmI (iteratedComap d B0_ n) $ d.map n) : Closeds $ d.obj $ n + 1) :
            Set $ d.obj $ n + 1) =
          (d.map n).base ⁻¹' (spI (iteratedComap d B0_ n) : Set $ d.obj n) := by simp_all
      rw [iteratedComap_succ, hpre]
      rw [disjoint_left] at hdn ⊢
      intro x hx hx'
      exact hdn (hsub hx) hx'
  have hfac := _i12 t ht
  have _i11 : ∀ t, t ≤ L → IsSmoothDivisor (projectionToBase d t ≫ p) (iteratedComap d B0_ t) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact hB0_
    | succ n ih =>
      intro hn
      have hlt := lt_of_succ_le hn
      have hle := le_of_lt hlt
      have hs1 := hsm n hle
      have heq : projectionToBase d (n + 1) ≫ p = d.map n ≫ projectionToBase d n ≫ p := by simp_all
      have hs2 := hsm (n + 1) hn
      rw [heq] at hs2
      have key := isSmoothDivisor_comap_of_isBlowupAlongIdealSheaf (projectionToBase d n ≫ p) (d.map n)
        (d.center n) (iteratedComap d B0_ n) (d.isBlowup n $ lt_of_lt_of_le hlt hL) (ih hle) $ hcent n hlt
      rwa [iteratedComap_succ, heq]
  rw [an1 hfac]
  let p := projectionToBase d t ≫ p
  let A := A t
  let B := iteratedComap d B0_ t
  refine isSmoothDivisor_of_locally_coordIdeal (p := p) (A * B) ?_
  intro x
  by_cases hxA : x ∈ spI A
  have hxB := fun h => Set.disjoint_left.mp (an2 hfac) hxA h
  obtain ⟨U, m, c, j, hxU, hAU⟩ :=
    exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p A (hA t ht) x hxA
  refine ⟨U ⊓ suppC B, ⟨hxU, hxB⟩, m, c.restrict inf_le_left, inr ⟨j, ?_⟩⟩
  have hBtop : restrictIdeal B (U ⊓ suppC B) = ⊤ := by
    refine mpr_ (restrictIdeal_eq_top_iff_forall_notMem_support ..) ?_
    intro y hy
    exact an2 hy
  have hc := restrictIdeal_eq_restrict_coordIdeal_of_le (U := U) (V := U ⊓ suppC B)
    inf_le_left c A {j} hAU
  rw [restrictIdeal_mul, hBtop, mul_top, hc]
  by_cases hxB : x ∈ spI B
  obtain ⟨U, m, c, j, hxU, hBU⟩ :=
    exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p B (_i11 t ht) x hxB
  refine ⟨U ⊓ suppC A, ⟨hxU, hxA⟩, m, c.restrict inf_le_left, inr ⟨j, ?_⟩⟩
  have hAtop : restrictIdeal A (U ⊓ suppC A) = ⊤ := by
    refine mpr_ (restrictIdeal_eq_top_iff_forall_notMem_support ..) ?_
    intro y hy
    exact an2 hy
  have hc := restrictIdeal_eq_restrict_coordIdeal_of_le (U := U) (V := U ⊓ suppC A)
    inf_le_left c B {j} hBU
  rw [restrictIdeal_mul, hAtop, top_mul, hc]
  obtain ⟨U, m, hxU, hUW, -, ⟨c⟩⟩ :=
    exists_etaleChart_le p x (suppC A ⊓ suppC B) ⟨hxA, hxB⟩
  refine ⟨U, hxU, m, c, inl ?_⟩
  have hAtopW : restrictIdeal A (suppC A ⊓ suppC B) = ⊤ := by
    refine mpr_ (restrictIdeal_eq_top_iff_forall_notMem_support ..) ?_
    intro y hy
    exact an1 hy
  have hBtopW : restrictIdeal B (suppC A ⊓ suppC B) = ⊤ := by
    refine mpr_ (restrictIdeal_eq_top_iff_forall_notMem_support ..) ?_
    intro y hy
    exact an2 hy
  rw [restrictIdeal_mul, restrictIdeal_eq_top_of_le A hUW hAtopW, restrictIdeal_eq_top_of_le B hUW hBtopW, mul_top]

end TransportedDivisor

end FunctorialResolution.EmbeddedResolution

end
section
open Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

theorem mem_span_of_pow_mul_mem_span {R : Type} [CommRing R] (g h : R)
    (hcan : ∀ n z, h * z ∈ span ({g ^ n} : Set R) →
      z ∈ span ({g ^ n} : Set R)) n m :
    ∀ z, h ^ m * z ∈ span ({g ^ n} : Set R) → z ∈ span ({g ^ n} : Set R) := by
  induction m with
  | zero =>
      intro z hz
      simpa using hz
  | succ m ih =>
      intro z hz
      refine ih z $ hcan n (h ^ m * z) ?_
      have hmul : h * (h ^ m * z) = h ^ (m + 1) * z := by ring
      rwa [hmul]

variable {X : Sch}

theorem stalkIdeal_one x : stalkIdeal (1 : ISD X) x = ⊤ := by
  have h := stalkIdeal_mul 1 (⊤) x
  rw [one_mul, stalkIdeal_top] at h
  refine le_antisymm le_top ?_
  rw [h]
  exact mpr_ mul_le fun r hr s _ => mul_mem_right s _ hr

theorem stalkIdeal_listProd (L : Bdy X) x :
    stalkIdeal L.prod x = (L.map fun I => stalkIdeal I x).prod := by
  induction L with
  | nil =>
      rw [prod_nil, map_nil, prod_nil, stalkIdeal_one x, one_eq_top]
  | cons J L ih =>
      rw [prod_cons, stalkIdeal_mul, ih, map_cons, prod_cons]

variable {k : Type} [Field k]

section
variable (p : X ⟶ Sp k)
@[reducible]
def IsEtaleLocallyCoordinateDivisor (D : ISD X) : Prop :=
  ∀ x : X, ∃ (U : Opn X) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
    restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}

theorem not_mem_support_of_stalkIdeal_eq_maximalIdeal
    {V} (hV : IsAffineOpen V) {m} (c : EtaleChart p V m)
    {D D' : ISD X} {t s} (hts : t ≠ s)
    (hDV : restrictIdeal D V = c.coordIdeal {t})
    (hD'V : restrictIdeal D' V = c.coordIdeal {s})
    {x} (hx : x ∈ V)
    (hmax : stalkIdeal D x = maximalIdeal (X.presheaf.stalk x))
    (hxD' : x ∈ D'.support) : False := by
  classical
  have hDspan :=
    stalkIdeal_eq_span_germ_coord p hV c t D hDV x hx
  let _a1 := pGerm X V x hx
  have hmem : _a1.hom (c.coord s) ∈ stalkIdeal D x := by
    rw [hmax]
    refine ((mem_support_iff_stalkIdeal_le_maximalIdeal D' x).mp hxD') ?_
    rw [stalkIdeal_eq_span_germ_coord p hV c s D' hD'V x hx]
    exact mem_span_singleton_self _
  rw [hDspan, mem_span_singleton'] at hmem
  obtain ⟨g, hg⟩ := hmem
  let := _a1.hom.toAlgebra
  have hlocz := hV.isLocalization_stalk ⟨x, hx⟩
  have halg : (algebraMap V.sec $ stkX X x) = _a1.hom := rfl
  obtain ⟨w, hw⟩ := IsLocalization.surj
    (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) g
  have hw' := hw
  rw [halg] at hw'
  have heq : (algebraMap V.sec $ stkX X x) (w.2 * c.coord s)
      = (algebraMap V.sec $ stkX X x) (w.1 * c.coord t) := by
    rw [map_mul, map_mul, halg, ← hg, ← hw']
    ring
  obtain ⟨v, hv⟩ :=
    (eq_iff_exists (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      (S := stkX X x)).mp heq
  let _a3 := v
  have hspan := by
    refine mem_span_coord_of_coord_mul_mem hV c hts (_a3 * w.2) ?_
    have hmul : c.coord s * (_a3 * w.2)
        = (_a3 * w.1) * c.coord t := by linear_combination hv
    rw [hmul]
    exact mem_span_singleton'.mpr ⟨_a3 * w.1, rfl⟩
  have hunit : IsUnit $ _a1.hom $ _a3 * w.2 := by
    rw [← halg, map_mul]
    exact (map_units (stkX X x) v).mul
      (map_units (stkX X x) w.2)
  refine (mem_nonunits_iff.mp $ (mem_maximalIdeal _).mp ?_) hunit
  rw [← hmax, hDspan]
  obtain ⟨z, hz⟩ := mem_span_singleton'.mp hspan
  refine mem_span_singleton'.mpr ⟨_a1.hom z, ?_⟩
  rw [← map_mul, hz]

theorem isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition
    E (hE : InStrictNormalCrossingPosition p E) D (hD : D ∈ E) :
    IsEtaleLocallyCoordinateDivisor p D := by
  obtain ⟨i, hi, hiD⟩ := getElem_of_mem hD
  obtain ⟨-, hpos⟩ := mp_ (inStrictNormalCrossingPosition_iff p E) hE
  intro x
  obtain ⟨U, hxU, m, c, a, -, hnone, hsome⟩ := InStrictNormalCrossingPositionAt.exists_etaleChart $ hpos x
  refine ⟨U, hxU, m, c, ?_⟩
  cases hai : a i with
  | none =>
      left
      have h := hnone i hi hai
      rwa [hiD] at h
  | some t =>
      right
      refine ⟨t, ?_⟩
      have h := hsome i hi t hai
      rwa [hiD] at h
end

def supportComponentsFinset [NoetherianSpace ↥X] (D : ISD X) :
    Finset $ Set X :=
  (finite_isIrreducibleComponentOfSupport D).toFinset

section
variable (a b : ISD X)
private theorem idealSheafData_mul_le_left : a * b ≤ a := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact mpr_ mul_le fun r hr s _ => mul_mem_right s _ hr

theorem idealSheafData_mul_le_right : a * b ≤ b := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact mpr_ mul_le fun r _ s hs => mul_mem_left _ r hs

theorem stalkIdeal_inf_eq_top x
    (ha : stalkIdeal a x = ⊤) (hb : stalkIdeal b x = ⊤) :
    stalkIdeal (a ⊓ b) x = ⊤ := by
  refine le_antisymm le_top ?_
  have hmono := stalkIdeal_mono
    (le_inf (idealSheafData_mul_le_left a b) $ idealSheafData_mul_le_right a b) x
  rw [stalkIdeal_mul, ha, hb] at hmono
  have htop : (⊤ : Ideal $ stkX X x) * ⊤ = ⊤ := by simp_all
  rwa [htop] at hmono
end

section
variable {al_ M : Type} [CommMonoid M] (g : al_ → M)
theorem prod_map_eq_one_of_forall_eq_one (L : List al_) (h : ∀ b ∈ L, g b = 1) : (L.map g).prod = 1 :=
  prod_eq_one fun x hx => by
    obtain ⟨a, ha, rfl⟩ := mp_ mem_map hx
    exact h a ha

theorem prod_map_eq_apply_of_nodup_of_forall_ne : ∀ (L : List al_) (a : al_), L.Nodup → a ∈ L →
      (∀ b ∈ L, b ≠ a → g b = 1) → (L.map g).prod = g a := by
  intro L
  induction L with
  | nil =>
      intro a _ ha _
      simp at ha
  | cons b L ih =>
      intro a hnd ha hone
      rw [map_cons, prod_cons]
      rcases mem_cons.mp ha with h | h
      have hL := by
        refine prod_map_eq_one_of_forall_eq_one g L ?_
        intro c hc
        refine hone c (mpr_ mem_cons $ inr hc) ?_
        intro hca
        exact absurd (show b ∈ L by rw [← h, ← hca]; exact hc) (mp_ nodup_cons hnd).1
      rw [hL, mul_one, h]
      have hb := by
        refine hone b (mpr_ mem_cons $ inl rfl) ?_
        intro hba
        exact absurd (show b ∈ L by rw [hba]; exact h) (mp_ nodup_cons hnd).1
      rw [hb, one_mul]
      exact ih a (mp_ nodup_cons hnd).2 h
        (fun c hc => hone c $ mpr_ mem_cons $ inr hc)

theorem prod_map_eq_apply_getElem_of_forall_ne :
    ∀ (L : List al_) (i : ℕ) (hi : i < length L),
      (∀ j (hj : j < length L), j ≠ i → g L[j] = 1) → (L.map g).prod = g L[i] := by
  intro L
  induction L with
  | nil =>
      intro i hi
      exact absurd hi (by simp only [length_nil]; omega)
  | cons b L ih =>
      intro i hi hone
      cases i with
      | zero =>
          have h1 := by
            refine prod_map_eq_one_of_forall_eq_one g L ?_
            intro y hy
            obtain ⟨j, hj, hjy⟩ := getElem_of_mem hy
            have h2 := hone (j + 1) (by simp only [length_cons]; omega) $ by omega
            rw [← hjy]
            simpa using h2
          show (List.map g (b :: L)).prod = g b
          rw [map_cons, prod_cons, h1, mul_one]
      | succ i =>
          have hi' : i < length L := by
            simp only [length_cons] at hi
            omega
          have hb := by
            have h0 := hone 0 (by simp only [length_cons]; omega) $ by omega
            simpa using h0
          have hrest := by
            refine ih i hi' ?_
            intro j hj hji
            have h2 := hone (j + 1) (by simp only [length_cons]; omega) $ by omega
            simpa using h2
          show (List.map g (b :: L)).prod = g L[i]
          rwa [map_cons, prod_cons, hb, one_mul]
end

section
variable (Ω : Opn X)
theorem exists_affineOpens_ideal_comap_io_eq_map
    (V : Ω.toScheme.affineOpens) :
    ∃ (W : X.affineOpens) (e : (V : Ω.toScheme.Opens) ≤
        (TopologicalSpace.Opens.map Ω.ib).obj (W : Opn X)),
      (W : Opn X) ≤ Ω ∧ ∀ A : ISD X,
        (A.comap Ω.i).ideal V
          = Ideal.map (Ω.ι.appLE (W : Opn X) (V : Ω.toScheme.Opens) e).hom (A.ideal W) := by
  have haff :=
    V.2.image_of_isOpenImmersion Ω.i
  have he : V ≤
      (m54 Ω.ib).obj (Ω.i.im V) := by
    intro y hy
    exact ⟨y, hy, rfl⟩
  refine ⟨⟨_, haff⟩, he, ?_, fun A =>
    comap_ideal_eq_map_appLE A Ω.i ⟨_, haff⟩ V he⟩
  rintro z ⟨y, -, rfl⟩
  exact y.2

private theorem idealSheafData_comap_prod :
    ∀ n (J : Fin n → ISD X),
      (∏ i, J i).comap Ω.i = ∏ i, (J i).comap Ω.i := by
  intro n
  induction n with
  | zero =>
      intro J
      simp only [univ_eq_empty, prod_empty]
      rw [Scheme.IdealSheafData.one_eq_top]
      exact comap_top _
  | succ n ih =>
      intro J
      rw [prod_univ_succ, comap_mul, ih fun i => J i.succ,
        prod_univ_succ]
end

section
variable (I : ISD X) {C : Set X} (hC : IsIrreducible C)
def orderAlongComponent : ℕ :=
  (orderAt I hC.genericPoint).toNat

theorem orderAlongComponent_eq_orderAt_genericPoint :
    orderAlongComponent I hC = (orderAt I hC.genericPoint).toNat := rfl
end

section
variable (I D : ISD X)
def componentPowerIdeal (C : Set X) : ISD X :=
  letI : Decidable $ IsIrreducibleComponentOfSupport D C := propDecidable _
  if h : IsIrreducibleComponentOfSupport D C then
    vanishingIdeal (⟨C, h.isClosed⟩ : TopologicalSpace.Closeds ↥X) ^
      orderAlongComponent I h.isIrreducible
  else ⊤

theorem componentPowerIdeal_of_not_isIrreducibleComponentOfSupport {C}
    (h : ¬ IsIrreducibleComponentOfSupport D C) : componentPowerIdeal I D C = ⊤ :=
  @dif_neg (IsIrreducibleComponentOfSupport D C) (propDecidable $ IsIrreducibleComponentOfSupport D C) h
    X.IdealSheafData _ _

theorem componentPowerIdeal_of_isIrreducibleComponentOfSupport {C}
    (h : IsIrreducibleComponentOfSupport D C) :
    componentPowerIdeal I D C =
      vanishingIdeal (⟨C, h.isClosed⟩ : TopologicalSpace.Closeds ↥X) ^
        orderAlongComponent I h.isIrreducible := by
  unfold componentPowerIdeal
  exact dif_pos h

theorem stalkIdeal_componentPowerIdeal_of_not_mem C {x}
    (hx : x ∉ C) : stalkIdeal (componentPowerIdeal I D C) x = ⊤ := by
  by_cases hC : IsIrreducibleComponentOfSupport D C
  have htop : stalkIdeal (vanishingIdeal
      (⟨C, hC.isClosed⟩ : m182 X)) x = ⊤ := by
    by_contra h
    have hmem : x ∈ (spI (vanishingIdeal
        (⟨C, hC.isClosed⟩ : m182 X)) : Set X) :=
      (mem_support_iff_stalkIdeal_ne_top _ x).mpr h
    rw [coe_support_vanishingIdeal] at hmem
    exact hx hmem
  rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, stalkIdeal_pow, htop, ← one_eq_top,
    one_pow]
  rw [componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC, stalkIdeal_top]
end

section
variable [NoetherianSpace ↥X]
def monomialPartAlongDivisor (I D : ISD X) :
    IdealSheafData X :=
  (supportComponentsFinset D).inf fun C => componentPowerIdeal I D C

theorem monomialPartAlongDivisor_eq_inf_componentPowerIdeal (I D : ISD X) :
    monomialPartAlongDivisor I D = (supportComponentsFinset D).inf fun C => componentPowerIdeal I D C := rfl

section
variable (E : Bdy X) (I : ISD X)
def monomialFactorIdeal : ISD X :=
  (E.map fun D => monomialPartAlongDivisor I D).prod

theorem stalkIdeal_monomialFactorIdeal x :
    stalkIdeal (monomialFactorIdeal E I) x =
      (E.map fun D => stalkIdeal (monomialPartAlongDivisor I D) x).prod := by
  have h : monomialFactorIdeal E I = (E.map $ monomialPartAlongDivisor I).prod := rfl
  rw [h, stalkIdeal_listProd, map_map]
  rfl

theorem monomialFactorIdeal_eq_prod_monomialPartAlongDivisor :
    monomialFactorIdeal E I = (E.map fun D => monomialPartAlongDivisor I D).prod := rfl
end

section
variable [hv1_0 : IsLocallyNoetherian X] (E : Bdy X) (I : ISD X)
include hv1_0
def nonMonomialFactorIdeal : ISD X :=
  idealSheafColon I $ monomialFactorIdeal E I

theorem nonMonomialFactorIdeal_eq_idealSheafColon :
    nonMonomialFactorIdeal E I = idealSheafColon I (monomialFactorIdeal E I) := rfl
end
end

theorem idealSheafData_ideal_top W :
    (⊤ : ISD X).ideal W = ⊤ :=
  (eq_top_iff_one _).mpr $ by simp

theorem idealSheafData_ideal_one W :
    (1 : ISD X).ideal W = 1 :=by simp_all
theorem idealSheafData_ideal_mul (I J : ISD X) W :
    (I * J).ideal W = I.ideal W * J.ideal W := rfl

theorem idealSheafData_ideal_listProd (L : Bdy X) W :
    L.prod.ideal W = (L.map fun J => J.ideal W).prod := by
  induction L with
  | nil => rw [prod_nil, map_nil, prod_nil]; exact idealSheafData_ideal_one W
  | cons J L ih =>
      rw [prod_cons, map_cons, prod_cons, idealSheafData_ideal_mul, ih]

theorem comap_io_eq_of_forall_affineOpens_ideal_eq (A B : ISD X) (Ω : Opn X)
    (h : ∀ W : X.affineOpens, (W : Opn X) ≤ Ω → A.ideal W = B.ideal W) :
    A.comap Ω.i = B.comap Ω.i := by
  refine le_antisymm ?_ ?_
  intro V
  obtain ⟨W, e, hW, hform⟩ := exists_affineOpens_ideal_comap_io_eq_map Ω V
  rw [hform A, hform B, h W hW]
  intro V
  obtain ⟨W, e, hW, hform⟩ := exists_affineOpens_ideal_comap_io_eq_map Ω V
  rw [hform A, hform B, h W hW]

theorem stalkIdeal_finsetInf_eq_top {be_ : Type} (f : be_ → ISD X) (x : X)
    (s : Finset be_) : (∀ b ∈ s, stalkIdeal (f b) x = ⊤) → stalkIdeal (s.inf f) x = ⊤ := by
  classical
  refine induction_on s ?_ ?_
  intro _
  rw [inf_empty]
  exact stalkIdeal_top x
  intro a t ha ih hs
  rw [inf_insert]
  exact stalkIdeal_inf_eq_top _ _ x (hs a $ mem_insert_self a t)
    (ih fun b hb => hs b $ mem_insert_of_mem hb)

theorem stalkIdeal_monomialPartAlongDivisor_of_not_mem_support [NoetherianSpace ↥X]
    (I D : ISD X) {x : X} (hx : x ∉ (D.support : Set X)) :
    stalkIdeal (monomialPartAlongDivisor I D) x = ⊤ := by
  rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
  refine stalkIdeal_finsetInf_eq_top (fun C => componentPowerIdeal I D C) x
    (supportComponentsFinset D) ?_
  intro C hC
  exact stalkIdeal_componentPowerIdeal_of_not_mem I D C fun hxC => hx $ ((mem_toFinset $ finite_isIrreducibleComponentOfSupport D).mp hC).subset_support hxC

theorem idealSheafData_ideal_pow (J : ISD X) n
    W : (J ^ n).ideal W = J.ideal W ^ n :=by simp_all
theorem ideal_componentPowerIdeal_eq_top_of_disjoint I D C
    (W : X.affineOpens) (h : ∀ y : X, y ∈ (W : Opn X) → y ∉ C) :
    (componentPowerIdeal I D C).ideal W = ⊤ := by
  by_cases hC : IsIrreducibleComponentOfSupport D C
  have _i15 : (vanishingIdeal (⟨C, hC.isClosed⟩ : m182 X)).ideal W = ⊤ := by
    refine mpr_ (eq_top_iff_one _) ?_
    rw [vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    have hmem0 : bsM (W.2.fromSpec) q ∈ (W : Set X) := by
      rw [← range_fromSpec W.2]
      exact mem_range_self q
    exact absurd hq $ h _ hmem0
  rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, idealSheafData_ideal_pow,
    _i15, ← one_eq_top, one_pow]
  rw [componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC]
  exact idealSheafData_ideal_top W

theorem natCast_add_one_le_of_not_le (n : ℕ) (b : ENat) (h : ¬ b ≤ (n : ENat)) :
    ((n + 1 : ℕ) : ENat) ≤ b := by
  rw [cast_succ]
  exact ENat.natCast_add_one_le_iff.2 $ mp_ not_le h

theorem mem_prod_map_of_forall_mem_span {R : Type} [CommRing R] {al_ : Type}
    F :
    ∀ (L : List al_) (g : ℕ → R),
      (∀ i (h : i < length L), F L[i] = span ({g i} : Set R)) →
      (∀ i, i < length L → ∀ j, j < length L → i ≠ j →
        ∀ n (w : R), g j * w ∈ span ({g i ^ n} : Set R) →
          w ∈ span ({g i ^ n} : Set R)) →
      ∀ z, (∀ i, i < length L → z ∈ span ({g i} : Set R)) →
        z ∈ (L.map F).prod := by
  intro L
  induction L with
  | nil =>
      intro g _ _ z _
      rw [map_nil, prod_nil, one_eq_top]
      exact Submodule.mem_top
  | cons b L ih =>
      intro g hF hcan z hz
      have hb0 := by
        have h := hF 0 (by simp only [length_cons]; omega)
        simpa using h
      have hz0 :=
        hz 0 (by simp only [length_cons]; omega)
      obtain ⟨y, hy⟩ := mp_ mem_span_singleton' hz0
      have hzy : z = g 0 * y := by rw [← hy]
                                   ring
      have hyprod : y ∈ (L.map F).prod := by
        refine ih (fun i => g $ i + 1) ?_ ?_ y ?_
        intro i h
        have h2 := hF (i + 1) (by simp only [length_cons]; omega)
        simpa using h2
        intro i hi j hj hij n w hw
        exact hcan (i + 1) (by simp only [length_cons]; omega) (j + 1)
          (by simp only [length_cons]; omega) (by omega) n w hw
        intro i h
        have hzi :=
          hz (i + 1) (by simp only [length_cons]; omega)
        have hzi' : g 0 * y ∈ span ({g (i + 1) ^ 1} : Set R) := by simp_all
        have h3 := hcan (i + 1) (by simp only [length_cons]; omega) 0
          (by simp only [length_cons]; omega) (by omega) 1 y hzi'
        rwa [pow_one] at h3
      have hg0 : g 0 ∈ F b := by simp_all
      rw [map_cons, prod_cons, hzy]
      exact mul_mem_mul hg0 hyprod

theorem mem_span_algebraMap_of_mul_mem {S : Type} [CommRing S] {q : Submonoid S}
    {A : Type} [CommRing A] [Algebra S A] [IsLocalization q A] (b d : S)
    (hcan : ∀ w : S, b * w ∈ span ({d} : Set S) → w ∈ span ({d} : Set S))
    z (hz : algebraMap S A b * z ∈ span ({algebraMap S A d} : Set A)) :
    z ∈ span ({algebraMap S A d} : Set A) := by
  obtain ⟨u, hu⟩ := mp_ mem_span_singleton' hz
  obtain ⟨⟨z0, w1_⟩, hz1_⟩ := IsLocalization.surj (M := q) (S := A) z
  obtain ⟨⟨u0_, w2_⟩, hu1_⟩ := IsLocalization.surj (M := q) (S := A) u
  have key : algebraMap S A (b * z0 * w2_) = algebraMap S A (d * u0_ * w1_) := by
    let _a4 := algebraMap S A w1_
    simp [map_mul]
    linear_combination (-(algebraMap S A b) * algebraMap S A w2_) * hz1_ +
      (algebraMap S A d * _a4) * hu1_ +
      (-_a4 * algebraMap S A w2_) * hu
  obtain ⟨cc, hcc⟩ := mp_ (eq_iff_exists (M := q) (S := A)) key
  have hmem : b * (z0 * w2_ * cc) ∈ span ({d} : Set S) :=
    mem_span_singleton'.mpr ⟨u0_ * w1_ * cc, by linear_combination -hcc⟩
  obtain ⟨v, hv⟩ := mp_ mem_span_singleton' $ hcan _ hmem
  let _a3 := span ({algebraMap S A d} : Set A)
  have hstep : z * algebraMap S A (w1_ * w2_ * cc) ∈
      _a3 := by
    refine mpr_ mem_span_singleton' ⟨algebraMap S A v, ?_⟩
    have h6 : algebraMap S A (z0 * w2_ * cc) = algebraMap S A (v * d) := by rw [hv]
    simp [map_mul] at h6 ⊢
    linear_combination -h6 - (algebraMap S A w2_ * algebraMap S A cc) * hz1_
  have hunit : IsUnit $ algebraMap S A $ w1_ * w2_ * cc := by
    rw [map_mul, map_mul]
    exact ((map_units (M := q) (S := A) w1_).mul $ map_units (M := q) (S := A) w2_).mul $ map_units (M := q) (S := A) cc
  obtain ⟨eu, heu⟩ := hunit
  have h7 := _a3.mul_mem_right ((eu⁻¹ : Aˣ) : A) hstep
  rwa [mul_assoc, ← heu, Units.mul_inv, mul_one] at h7

theorem mem_span_germ_coord_pow_of_mul_mem (p : X ⟶ Sp k)
    {V : Opn X} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart p V m) {x : X} (hx : x ∈ V)
    {i j : Fin m} (hij : i ≠ j) (N : ℕ) (z : X.presheaf.stalk x)
    (hz : (X.presheaf.germ V x hx).hom (c.coord j) * z ∈
      span ({(X.presheaf.germ V x hx).hom (c.coord i) ^ N} : Set $ X.presheaf.stalk x)) :
    z ∈ span ({(X.presheaf.germ V x hx).hom (c.coord i) ^ N} :
      Set $ X.presheaf.stalk x) := by
  let _a0 := pGerm X V x hx
  let := _a0.hom.toAlgebra
  have :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hmap : ∀ y, algebraMap V.sec (stkX X x) y =
      _a0.hom y := fun _ => rfl
  let _a2 := c.coord i ^ N
  have hpow : algebraMap V.sec (stkX X x) _a2 =
      _a0.hom (c.coord i) ^ N := by
    rw [map_pow, hmap]
  have hmain := mem_span_algebraMap_of_mul_mem
    (q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (c.coord j) _a2
    (fun w hw => mem_span_coord_pow_of_mul_mem hV c hij N w hw) z
    (by rw [hpow, hmap]; exact hz)
  rwa [hpow] at hmain

theorem coe_orderAlongComponent_eq_orderAt_genericPoint [IsLocallyNoetherian X] {D I : ISD X} {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) (hI : NonzeroOnComponents I) :
    (orderAlongComponent I hC.isIrreducible : ENat) = orderAt I hC.isIrreducible.genericPoint := by
  rw [orderAlongComponent_eq_orderAt_genericPoint, ENat.natCast_toNat $ hC.orderAt_genericPoint_ne_top I hI]

theorem idealSheafData_listProd_le_of_mem :
    ∀ (L : Bdy X) (a : ISD X), a ∈ L → L.prod ≤ a := by
  intro L
  induction L with
  | nil =>
      intro a ha
      simp at ha
  | cons b L ih =>
      intro a ha
      rw [prod_cons]
      rcases mem_cons.mp ha with h | h
      rw [h]
      exact idealSheafData_mul_le_left _ _
      exact le_trans (idealSheafData_mul_le_right _ _) $ ih a h

section
variable [NoetherianSpace ↥X]
section
variable (p : X ⟶ Sp k)
theorem stalkIdeal_monomialPartAlongDivisor_of_mem (I : ISD X) {D : ISD X}
    (hD : IsEtaleLocallyCoordinateDivisor p D) {C : Set X} (hC : IsIrreducibleComponentOfSupport D C) {x : X}
    (hx : x ∈ C) :
    stalkIdeal (monomialPartAlongDivisor I D) x = stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible := by
  let _a1 := supportComponentsFinset D
  classical
  have hmemiff : ∀ C', C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp [supportComponentsFinset, mem_toFinset, mem_ofPred_eq]
  have hCS := mpr_ (hmemiff C) hC
  have hCpart : stalkIdeal (componentPowerIdeal I D C) x = stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible := by
    rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, stalkIdeal_pow,
      hC.stalkIdeal_vanishingIdeal_eq p hD x hx]
  refine le_antisymm ?_ ?_
  have h1 : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C := by
    rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
    exact inf_le hCS
  have h2 := stalkIdeal_mono h1 x
  rwa [hCpart] at h2
  have hle : (_a1.toList.map (componentPowerIdeal I D)).prod
      ≤ monomialPartAlongDivisor I D := by
    rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
    refine le_inf ?_
    intro C' hC'
    exact idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C')
      (mpr_ mem_map ⟨C', mpr_ mem_toList hC', rfl⟩)
  have hprod : stalkIdeal
      (_a1.toList.map (componentPowerIdeal I D)).prod x
      = stalkIdeal (componentPowerIdeal I D C) x := by
    rw [stalkIdeal_listProd, map_map]
    refine prod_map_eq_apply_of_nodup_of_forall_ne (fun C' => stalkIdeal (componentPowerIdeal I D C') x)
      (_a1.toList) C (nodup_toList _)
      (mpr_ mem_toList hCS) ?_
    intro C' hC' hne
    show stalkIdeal (componentPowerIdeal I D C') x = 1
    rw [stalkIdeal_componentPowerIdeal_of_not_mem I D C' (Set.disjoint_left.mp (hC.disjoint (mp_ (hmemiff C') (mp_ mem_toList hC')) p hD $ m113 hne) hx), one_eq_top]
  have h3 := stalkIdeal_mono hle x
  rwa [hprod, hCpart] at h3

theorem stalkIdeal_monomialFactorIdeal_genericPoint (E : Bdy X) I
    (hE : InStrictNormalCrossingPosition p E) {D} (hD : D ∈ E) {C}
    (hC : IsIrreducibleComponentOfSupport D C) :
    stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      stalkIdeal D hC.isIrreducible.genericPoint ^ orderAlongComponent I hC.isIrreducible := by
  classical
  obtain ⟨i0, hi0, hi0D⟩ := getElem_of_mem hD
  have hloc := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
  obtain ⟨-, hpos⟩ := mp_ (inStrictNormalCrossingPosition_iff p E) hE
  obtain ⟨U, hetU, m, c, a, hinj, hnone, hsome⟩ :=
    InStrictNormalCrossingPositionAt.exists_etaleChart $ hpos hC.isIrreducible.genericPoint
  obtain ⟨t, hat⟩ : ∃ t, a i0 = some t := by
    cases hai : a i0 with
    | none =>
        refine absurd hC.genericPoint_mem_support $ notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ _ hetU
        rw [← hi0D]
        exact hnone i0 hi0 hai
    | some t =>
        refine ⟨t, ?_⟩
        simp
  have hDU := hsome i0 hi0 t hat
  rw [hi0D] at hDU
  have hother : ∀ j (hj : j < lenL E), j ≠ i0 →
      hC.isIrreducible.genericPoint ∉ (E[j].support) := by
    intro j hj hji0 hmem
    cases haj : a j with
    | none =>
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top E[j] U (hnone j hj haj) _ hetU hmem
    | some s =>
        have hts : t ≠ s := by
          intro h
          exact hji0 $ hinj j hj i0 hi0 t (by rw [haj, h]) hat
        have hxtop : hC.isIrreducible.genericPoint ∈ (⨆ W : affO X, (W : Opn X)) := by
          rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
          trivial
        obtain ⟨W, hetW⟩ := mp_ mem_iSup hxtop
        obtain ⟨f, hfU, hetf⟩ :=
          W.2.exists_basicOpen_le (⟨hC.isIrreducible.genericPoint, hetU⟩ : U) hetW
        exact not_mem_support_of_stalkIdeal_eq_maximalIdeal p (W.2.basicOpen f) (c.restrict hfU) hts
          (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c D {t} hDU)
          (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c E[j] {s} $ hsome j hj s haj)
          hetf (stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal) hmem
  have hprod : (E.map fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint).prod
      = stalkIdeal (monomialPartAlongDivisor I E[i0]) hC.isIrreducible.genericPoint := by
    refine prod_map_eq_apply_getElem_of_forall_ne
      (fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint) E i0 hi0 ?_
    intro j hj hji0
    show stalkIdeal (monomialPartAlongDivisor I E[j]) hC.isIrreducible.genericPoint = 1
    rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I E[j] $ hother j hj hji0, one_eq_top]
  rw [stalkIdeal_monomialFactorIdeal, hprod, hi0D,
    stalkIdeal_monomialPartAlongDivisor_of_mem p I hloc hC hC.genericPoint_mem]

section
variable (I D : ISD X) (hD : IsEtaleLocallyCoordinateDivisor p D) (x : X)
include hD
theorem exists_nhds_ideal_monomialPartAlongDivisor_eq_pow :
    ∃ Ω : Opn X, x ∈ Ω ∧ ∃ a : ℕ, ∀ W : X.affineOpens, (W : Opn X) ≤ Ω →
      (monomialPartAlongDivisor I D).ideal W = (D ^ a).ideal W := by
  classical
  have hmemiff : ∀ C', C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp [supportComponentsFinset, mem_toFinset, mem_ofPred_eq]
  have hprodle : ∀ W,
      (((supportComponentsFinset D).toList.map (componentPowerIdeal I D)).prod).ideal W
        ≤ (monomialPartAlongDivisor I D).ideal W := by
    intro W
    have hle : ((supportComponentsFinset D).toList.map (componentPowerIdeal I D)).prod
        ≤ monomialPartAlongDivisor I D := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      refine le_inf ?_
      intro C' hC'
      exact idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C')
        (mpr_ mem_map ⟨C', mpr_ mem_toList hC', rfl⟩)
    exact hle W
  by_cases hx : ∃ C ∈ supportComponentsFinset D, x ∈ C
  obtain ⟨C0_, hC0mem, hxC0⟩ := hx
  have hC0_ := mp_ (hmemiff C0_) hC0mem
  obtain ⟨V, hV, hxV, n, c, j, hDV, hVsupp, -, hagree, -⟩ :=
    hC0_.exists_affineOpen_etaleChart_coordIdeal p hD x hxC0
  refine ⟨V, hxV, orderAlongComponent I hC0_.isIrreducible, ?_⟩
  intro W hWV
  have hDW := by
    simpa using (ideal_eq_span_coord (c.restrict hWV) W.2 D {j} (restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV))
  have hcomp0 : (componentPowerIdeal I D C0_).ideal W
      = span {(c.restrict hWV).coord j ^ orderAlongComponent I hC0_.isIrreducible} := by
    rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC0_, idealSheafData_ideal_pow,
      hagree W hWV, hDW, span_singleton_pow]
  have hDpow : (D ^ orderAlongComponent I hC0_.isIrreducible).ideal W
      = span {(c.restrict hWV).coord j ^ orderAlongComponent I hC0_.isIrreducible} := by
    rw [idealSheafData_ideal_pow, hDW, span_singleton_pow]
  have hother : ∀ C, C ∈ (supportComponentsFinset D).toList → C ≠ C0_ →
      (componentPowerIdeal I D C).ideal W = ⊤ := by
    intro C hCmem hne
    have hCcomp := mp_ (hmemiff C) (mp_ mem_toList hCmem)
    refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
    intro y hy hyC
    exact (Set.disjoint_left.mp (hCcomp.disjoint hC0_ p hD hne) hyC) (hVsupp y (hWV hy) (hCcomp.subset_support hyC))
  have hprodideal : (((supportComponentsFinset D).toList.map
      (componentPowerIdeal I D)).prod).ideal W = (componentPowerIdeal I D C0_).ideal W := by
    rw [idealSheafData_ideal_listProd, map_map]
    refine prod_map_eq_apply_of_nodup_of_forall_ne (fun C => (componentPowerIdeal I D C).ideal W)
      ((supportComponentsFinset D).toList) C0_ (nodup_toList _)
      (mpr_ mem_toList hC0mem) ?_
    intro C' hC' hne
    show (componentPowerIdeal I D C').ideal W = 1
    rw [one_eq_top]
    exact hother C' hC' hne
  rw [hDpow, ← hcomp0]
  refine le_antisymm ?_ ?_
  have hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C0_ := by
    rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
    exact inf_le hC0mem
  exact hle W
  rw [← hprodideal]
  exact hprodle W
  push Not at hx
  have hclosed : IsClosed (⋃ C ∈ supportComponentsFinset D, C) := by
    refine isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_
    intro C hC
    exact (mp_ (hmemiff C) (mp_ mem_coe hC)).isClosed
  refine ⟨⟨(⋃ C ∈ supportComponentsFinset D, C)ᶜ, hclosed.isOpen_compl⟩,
    ?_, 0, ?_⟩
  simp_all
  intro W hWOm
  rw [pow_zero, idealSheafData_ideal_one, one_eq_top]
  have hall : ∀ C ∈ (supportComponentsFinset D).toList,
      (componentPowerIdeal I D C).ideal W = 1 := by
    intro C hC
    rw [one_eq_top]
    refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
    intro y hy hyC
    exact absurd (mem_biUnion (mpr_ mem_coe (mp_ mem_toList hC)) hyC) (hWOm hy)
  have hprodtop : (((supportComponentsFinset D).toList.map
      (componentPowerIdeal I D)).prod).ideal W = ⊤ := by
    rw [idealSheafData_ideal_listProd, map_map, ← one_eq_top]
    exact prod_map_eq_one_of_forall_eq_one (fun C => (componentPowerIdeal I D C).ideal W)
      ((supportComponentsFinset D).toList) hall
  refine le_antisymm le_top ?_
  rw [← hprodtop]
  exact hprodle W
end

section
variable (I : ISD X) (x : X)
theorem exists_prod_monomialPartAlongDivisor_eq_span_singleton :
    ∀ L : Bdy X, (∀ D ∈ L, IsEtaleLocallyCoordinateDivisor p D) →
      ∃ Ω : Opn X, x ∈ Ω ∧ ∀ W : X.affineOpens, (W : Opn X) ≤ Ω →
        ∃ g ∈ nonZeroDivisors (X.sec W),
          ((L.map fun D => monomialPartAlongDivisor I D).prod).ideal W = span {g} := by
  intro L
  induction L with
  | nil =>
      intro _
      refine ⟨⊤, trivial, ?_⟩
      intro W _
      refine ⟨1, one_mem _, ?_⟩
      rw [map_nil, prod_nil, span_singleton_one]
      exact idealSheafData_ideal_top W
  | cons D L ih =>
      intro hmem
      obtain ⟨Om1, hxOm1, h1_⟩ : ∃ Ω : Opn X, x ∈ Ω ∧ ∀ W : affO X, W ≤ Ω → ∃ g ∈ nonZeroDivisors (xSec X W), (monomialPartAlongDivisor I D).ideal W = span {g} := by
        let hD := hmem D $ mpr_ mem_cons (inl rfl)
        classical
        have hmemiff : ∀ C', C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
          intro C'
          simp [supportComponentsFinset, mem_toFinset, mem_ofPred_eq]
        have hprodle : ∀ W,
            (((supportComponentsFinset D).toList.map (componentPowerIdeal I D)).prod).ideal W
              ≤ (monomialPartAlongDivisor I D).ideal W := by
          intro W
          have hle : ((supportComponentsFinset D).toList.map (componentPowerIdeal I D)).prod
              ≤ monomialPartAlongDivisor I D := by
            rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
            refine le_inf ?_
            intro C' hC'
            exact idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C')
              (mpr_ mem_map ⟨C', mpr_ mem_toList hC', rfl⟩)
          exact hle W
        by_cases hx : ∃ C ∈ supportComponentsFinset D, x ∈ C
        obtain ⟨C0_, hC0mem, hxC0⟩ := hx
        have hC0_ := mp_ (hmemiff C0_) hC0mem
        obtain ⟨V, hV, hxV, n, c, j, hDV, hVsupp, -, hagree, -⟩ :=
          hC0_.exists_affineOpen_etaleChart_coordIdeal p hD x hxC0
        refine ⟨V, hxV, ?_⟩
        intro W hWV
        refine ⟨(c.restrict hWV).coord j ^ orderAlongComponent I hC0_.isIrreducible,
          pow_mem (coord_mem_nonZeroDivisors W.2 (c.restrict hWV) j) _, ?_⟩
        have hDW := by
          simpa using (ideal_eq_span_coord (c.restrict hWV) W.2 D {j} (restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV))
        have hcomp0 : (componentPowerIdeal I D C0_).ideal W
            = span {(c.restrict hWV).coord j ^ orderAlongComponent I hC0_.isIrreducible} := by
          rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC0_, idealSheafData_ideal_pow,
            hagree W hWV, hDW, span_singleton_pow]
        have hother : ∀ C : Set X, C ∈ (supportComponentsFinset D).toList → C ≠ C0_ →
            (componentPowerIdeal I D C).ideal W = ⊤ := by
          intro C hCmem hne
          have hCcomp := mp_ (hmemiff C) (mp_ mem_toList hCmem)
          refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
          intro y hy hyC
          exact (Set.disjoint_left.mp (hCcomp.disjoint hC0_ p hD hne) hyC) (hVsupp y (hWV hy) (hCcomp.subset_support hyC))
        have hprodideal : (((supportComponentsFinset D).toList.map
            (componentPowerIdeal I D)).prod).ideal W = (componentPowerIdeal I D C0_).ideal W := by
          rw [idealSheafData_ideal_listProd, map_map]
          refine prod_map_eq_apply_of_nodup_of_forall_ne (fun C => (componentPowerIdeal I D C).ideal W)
            ((supportComponentsFinset D).toList) C0_ (nodup_toList _)
            (mpr_ mem_toList hC0mem) ?_
          intro C' hC' hne
          show (componentPowerIdeal I D C').ideal W = 1
          rw [one_eq_top]
          exact hother C' hC' hne
        refine le_antisymm ?_ ?_
        rw [← hcomp0]
        have hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C0_ := by
          rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
          exact inf_le hC0mem
        exact hle W
        rw [← hcomp0, ← hprodideal]
        exact hprodle W
        push Not at hx
        have hclosed : IsClosed (⋃ C ∈ supportComponentsFinset D, C) := by
          refine isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_
          intro C hC
          exact (mp_ (hmemiff C) (mp_ mem_coe hC)).isClosed
        refine ⟨⟨(⋃ C ∈ supportComponentsFinset D, C)ᶜ, hclosed.isOpen_compl⟩, ?_, ?_⟩
        intro hmem
        rw [Set.mem_iUnion₂] at hmem
        obtain ⟨C, hC, hxC⟩ := hmem
        exact hx C (mp_ mem_coe hC) hxC
        intro W hWOm
        refine ⟨1, one_mem _, ?_⟩
        rw [span_singleton_one]
        have hall : ∀ C ∈ (supportComponentsFinset D).toList,
            (componentPowerIdeal I D C).ideal W = 1 := by
          intro C hC
          rw [one_eq_top]
          refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
          intro y hy hyC
          exact absurd (mem_biUnion (mpr_ mem_coe (mp_ mem_toList hC)) hyC) (hWOm hy)
        have hprodtop : (((supportComponentsFinset D).toList.map
            (componentPowerIdeal I D)).prod).ideal W = ⊤ := by
          rw [idealSheafData_ideal_listProd, map_map, ← one_eq_top]
          exact prod_map_eq_one_of_forall_eq_one (fun C => (componentPowerIdeal I D C).ideal W)
            ((supportComponentsFinset D).toList) hall
        refine le_antisymm le_top ?_
        rw [← hprodtop]
        exact hprodle W
      obtain ⟨Om2, hxOm2, h2_⟩ := ih fun D' hD' => hmem D' $ mpr_ mem_cons (inr hD')
      refine ⟨Om1 ⊓ Om2, ⟨hxOm1, hxOm2⟩, ?_⟩
      intro W hW
      obtain ⟨g1_, hg1_, he1_⟩ := h1_ W $ le_trans hW inf_le_left
      obtain ⟨g2_, hg2_, he2_⟩ := h2_ W $ le_trans hW inf_le_right
      refine ⟨g1_ * g2_, mul_mem hg1_ hg2_, ?_⟩
      rw [map_cons, prod_cons, idealSheafData_ideal_mul, he1_, he2_,
        span_singleton_mul_span_singleton]

theorem exists_prod_monomialPartAlongDivisor_eq_prod_pow :
    ∀ (n : ℕ) (g : Fin n → ISD X), (∀ i, IsEtaleLocallyCoordinateDivisor p $ g i) →
      ∃ Ω : Opn X, x ∈ Ω ∧ ∃ a : Fin n → ℕ, ∀ W : X.affineOpens, (W : Opn X) ≤ Ω →
        ((ofFn fun i => monomialPartAlongDivisor I $ g i).prod).ideal W = (∏ i, g i ^ a i).ideal W := by
  intro n
  induction n with
  | zero =>
      intro g _
      refine ⟨⊤, trivial, elim0, ?_⟩
      intro W _
      simp only [ofFn_zero, prod_nil, univ_eq_empty, prod_empty]
  | succ n ih =>
      intro g hg
      obtain ⟨Om1, hxOm1, a0_, h1_⟩ := exists_nhds_ideal_monomialPartAlongDivisor_eq_pow p I (g 0) (hg 0) x
      obtain ⟨Om2, hxOm2, a', h2_⟩ := ih (fun i => g i.succ) fun i => hg i.succ
      refine ⟨Om1 ⊓ Om2, ⟨hxOm1, hxOm2⟩, m223 a0_ a', ?_⟩
      intro W hW
      simp only [ofFn_succ, prod_cons, prod_univ_succ]
      rw [idealSheafData_ideal_mul, idealSheafData_ideal_mul, h1_ W $ le_trans hW inf_le_left, h2_ W $ le_trans hW inf_le_right]
      simp only [cons_zero, cons_succ]
end

theorem isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal E (I : ISD X)
    (hE : InStrictNormalCrossingPosition p E) : IsLocallyGeneratedByNonZeroDivisor $ monomialFactorIdeal E I := by
  intro x
  obtain ⟨Ω, hxOm, hOm⟩ := exists_prod_monomialPartAlongDivisor_eq_span_singleton p I x E
    (fun D hD => isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD)
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  obtain ⟨f, hfle, hxf⟩ := (U.2).exists_basicOpen_le (⟨x, hxOm⟩ : Ω) hxU
  obtain ⟨g, hg, hgeq⟩ := hOm (X.affineBasicOpen f) hfle
  refine ⟨X.affineBasicOpen f, g, hxf, hg, ?_⟩
  rwa [monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]
end

section
variable [IsLocallyNoetherian X]
section
variable (p : X ⟶ Sp k) [LocallyOfFiniteType p] (E : Bdy X) (I : ISD X) (hE : InStrictNormalCrossingPosition p E)
include hE
theorem orderAt_monomialFactorIdeal_genericPoint
    (hI : NonzeroOnComponents I) {D : ISD X} (hD : D ∈ E) {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) :
    orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (orderAlongComponent I hC.isIrreducible : ENat) := by
  classical
  have hloc := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
  have hmaxD :=
    stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal
  have hstalk :=
    stalkIdeal_monomialFactorIdeal_genericPoint p E I hE hD hC
  have hmono : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
      = maximalIdeal (stkX X hC.isIrreducible.genericPoint)
        ^ orderAlongComponent I hC.isIrreducible := by simp_all
  have hordI :=
    symm (coe_orderAlongComponent_eq_orderAt_genericPoint hC hI)
  have h3 : stalkIdeal I hC.isIrreducible.genericPoint
      ≤ maximalIdeal (stkX X hC.isIrreducible.genericPoint)
        ^ orderAlongComponent I hC.isIrreducible := by
    rw [← hmaxD]
    exact stalkIdeal_le_pow_of_le_orderAt_genericPoint p D hloc hC.isIrreducible
      hC.subset_support hC.maximal I (orderAlongComponent I hC.isIrreducible)
      (le_of_eq hordI.symm) hC.isIrreducible.genericPoint hC.genericPoint_mem
  refine le_antisymm ?_ (mpr_ (le_orderAt_iff _ _ _) (le_of_eq hmono))
  by_contra hcon
  have h2 :=
    natCast_add_one_le_of_not_le (orderAlongComponent I hC.isIrreducible) _ hcon
  rw [le_orderAt_iff, hmono] at h2
  exact not_stalkIdeal_le_pow_succ_genericPoint p D hloc hC.isIrreducible hC.subset_support
    hC.maximal I (orderAlongComponent I hC.isIrreducible) hordI
    (by rw [hmaxD]; exact le_trans h3 h2)

theorem monomialFactorIdeal_mul_nonMonomialFactorIdeal :
    monomialFactorIdeal E I * nonMonomialFactorIdeal E I = I := by
  have hIM : I ≤ monomialFactorIdeal E I := by
    rw [le_iff_forall_stalkIdeal_le]
    intro x
    obtain ⟨-, hposall⟩ := mp_ (inStrictNormalCrossingPosition_iff p E) hE
    obtain ⟨U, hxU, m, c, aa, hinj, hnone, hsome⟩ := InStrictNormalCrossingPositionAt.exists_etaleChart $ hposall x
    obtain ⟨V, hVaff, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    let _a1 := Set $ stkX X x
    let _a4 := pGerm X V x hxV
    have hdata : ∀ i, ∃ ee, ∀ h,
        stalkIdeal (monomialPartAlongDivisor I $ E[i]'h) x = span ({ee} : _a1) ∧
        stalkIdeal I x ≤ span ({ee} : _a1) ∧
        (ee = 1 ∨ ∃ t bb, aa i = some t ∧
          ee = _a4.hom ((c.restrict hVU).coord t) ^ bb) := by
      intro i
      by_cases hi : i < lenL E
      by_cases hxs : x ∈ (spI (E[i]'hi) : Set X)
      have hDloc :=
        isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E[i]'hi) $ getElem_mem hi
      obtain ⟨C, hC, hxC⟩ := exists_isIrreducibleComponentOfSupport (E[i]'hi) x hxs
      have hopt : ∃ t, aa i = some t := by
        by_contra hcon
        push Not at hcon
        refine absurd hxs $ notMem_support_of_mem_opens_of_restrictIdeal_eq_top (E[i]'hi) U
          (hnone i hi ?_) x hxU
        cases hca : aa i with
        | none => rfl
        | some t => exact absurd hca $ hcon t
      obtain ⟨t, haa⟩ := hopt
      have hst :=
        stalkIdeal_eq_span_germ_coord p hVaff (c.restrict hVU) t (E[i]'hi) (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {t} $ hsome i hi t haa) x hxV
      let _a0 := _a4.hom ((c.restrict hVU).coord t) ^ orderAlongComponent I hC.isIrreducible
      have hA : stalkIdeal (monomialPartAlongDivisor I $ E[i]'hi) x =
          (span ({_a0} : _a1)) := by
        rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I hDloc hC hxC, hst, span_singleton_pow]
      refine ⟨_a0,
        fun _ => ⟨hA, ?_, inr ⟨t, orderAlongComponent I hC.isIrreducible, haa, rfl⟩⟩⟩
      have hn : ((orderAlongComponent I hC.isIrreducible) : ENat) ≤
          orderAt I hC.isIrreducible.genericPoint := by
        rw [orderAlongComponent_eq_orderAt_genericPoint]
        exact ENat.natCast_toNat_le_self _
      have hle := stalkIdeal_le_pow_of_le_orderAt_genericPoint p (E[i]'hi) hDloc
        hC.isIrreducible hC.subset_support hC.maximal I
        (orderAlongComponent I hC.isIrreducible) hn x hxC
      rwa [hst, span_singleton_pow] at hle
      have hA : stalkIdeal (monomialPartAlongDivisor I $ E[i]'hi) x =
          span ({1} : _a1) := by
        rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I (E[i]'hi) hxs,
          span_singleton_one]
      refine ⟨1, fun _ => ⟨hA, ?_, inl rfl⟩⟩
      rw [span_singleton_one]
      exact le_top
      exact ⟨1, fun h => absurd h hi⟩
    choose ee hee using hdata
    have hcan : ∀ i, i < lenL E → ∀ j, j < lenL E → i ≠ j →
        ∀ n w,
          ee j * w ∈ span ({ee i ^ n} : _a1) →
            w ∈ span ({ee i ^ n} : _a1) := by
      intro i hi j hj hij n w hw
      rcases (hee i hi).2.2 with hi1 | ⟨ti, bi, hai, hei⟩
      rw [hi1, one_pow, span_singleton_one]
      exact Submodule.mem_top
      rcases (hee j hj).2.2 with hj1 | ⟨tj, bj, haj, hej⟩
      simp_all
      have htne : ti ≠ tj := by
        intro htt
        refine hij ?_
        refine hinj i hi j hj ti hai ?_
        rw [htt]
        exact haj
      have hsingle :=
        fun N zz hzz =>
          mem_span_germ_coord_pow_of_mul_mem p hVaff (c.restrict hVU) hxV htne N zz hzz
      rw [hei, hej] at hw
      rw [hei]
      rw [← pow_mul] at hw ⊢
      exact mem_span_of_pow_mul_mem_span _ _ hsingle (bi * n) bj w hw
    rw [stalkIdeal_monomialFactorIdeal]
    intro z hz
    refine mem_prod_map_of_forall_mem_span (fun D => stalkIdeal (monomialPartAlongDivisor I D) x) E ee ?_
      hcan z ?_
    intro i h
    exact an1 $ hee i h
    intro i h
    exact (hee i h).2.1 hz
  rw [nonMonomialFactorIdeal_eq_idealSheafColon]
  exact (isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal p E I hE).mul_idealSheafColon hIM
end

theorem exists_isMonomialSplitting
    [CharZero k] (p : X ⟶ Sp k) [Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (E : Bdy X)
    (hE : InStrictNormalCrossingPosition p E) (I : ISD X) (hI : NonzeroOnComponents I) :
    ∃ M N : ISD X, IsMonomialSplitting E I M N := by
  classical
  have hetaleCoord : ∀ i, IsEtaleLocallyCoordinateDivisor p $ get E i := by
    intro i
    refine isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE _ ?_
    simp
  refine ⟨monomialFactorIdeal E I, nonMonomialFactorIdeal E I, sy_ $ monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE, ?_, ?_, ?_⟩
  intro z hz
  by_contra hcon
  have hnot : ∀ D ∈ E, z ∉ D.support := by simp_all
  refine mp_ (mem_support_iff_stalkIdeal_ne_top (monomialFactorIdeal E I) z) hz ?_
  rw [stalkIdeal_monomialFactorIdeal, ← one_eq_top]
  refine prod_map_eq_one_of_forall_eq_one (fun D => stalkIdeal (monomialPartAlongDivisor I D) z) E ?_
  intro D hD
  rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I D $ hnot D hD, one_eq_top]
  intro x
  obtain ⟨Ω, hxOm, a, ha⟩ :=
    exists_prod_monomialPartAlongDivisor_eq_prod_pow p I x E.length E.get hetaleCoord
  refine ⟨Ω, hxOm, a, ?_⟩
  have hlist : (ofFn fun i => monomialPartAlongDivisor I $ get E i)
      = E.map fun D => monomialPartAlongDivisor I D := by
    refine ext_getElem (by simp) ?_
    intro i h1 h2
    simp
  have hcongr : (monomialFactorIdeal E I).comap Ω.i
      = (∏ i : Fin E.length, get E i ^ a i).comap Ω.i := by
    refine comap_io_eq_of_forall_affineOpens_ideal_eq _ _ Ω ?_
    intro W hW
    have hW' := ha W hW
    rw [hlist] at hW'
    rwa [monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]
  rw [hcongr, idealSheafData_comap_prod Ω E.length fun i => get E i ^ a i]
  exact prod_congr rfl
    (fun i _ => comap_pow (get E i) Ω.i $ a i)
  intro D hD C hCirr hCsub hCmax hCN
  have hC : IsIrreducibleComponentOfSupport D C :=
    { isIrreducible := hCirr
      maximal := fun C' h1 h2 h3 => m15 (hCmax C' h1 h3 h2) h2
      subset_support := hCsub }
  have hstalkM : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
      = maximalIdeal (stkX X hC.isIrreducible.genericPoint)
        ^ orderAlongComponent I hC.isIrreducible := by
    rw [stalkIdeal_monomialFactorIdeal_genericPoint p E I hE hD hC, stalkIdeal_genericPoint_eq_maximalIdeal p D (isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD) hC.isIrreducible hC.subset_support hC.maximal]
  have hIeq : stalkIdeal I hC.isIrreducible.genericPoint
      = stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
        * stalkIdeal (nonMonomialFactorIdeal E I) hC.isIrreducible.genericPoint := by
    rw [← stalkIdeal_mul, monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE]
  have hle : stalkIdeal I hC.isIrreducible.genericPoint
      ≤ maximalIdeal (stkX X hC.isIrreducible.genericPoint)
        ^ (orderAlongComponent I hC.isIrreducible + 1) := by
    rw [hIeq, hstalkM, pow_succ]
    exact mul_mono le_rfl $ (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp $ hCN hC.genericPoint_mem
  have h2 :=
    (le_orderAt_iff I _ _).mpr hle
  rw [← coe_orderAlongComponent_eq_orderAt_genericPoint hC hI] at h2
  have h3 : orderAlongComponent I hC.isIrreducible + 1
      ≤ orderAlongComponent I hC.isIrreducible := by exact_mod_cast h2
  omega
end
end

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

variable {X Y : Sch}

private theorem comap_finset_prod {ι : Type} (s : Finset ι) (F : ι → ISD X)
    (h : Y ⟶ X) : (∏ i ∈ s, F i).comap h = ∏ i ∈ s, (F i).comap h := by
  induction s using cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, comap_mul, ih]

theorem comap_comap_io (h : Y ⟶ X) (J : ISD X) (U : Opn X) :
    (J.comap h).comap (h ⁻¹ᵁ U).i = (J.comap U.i).comap (h.mr U) := by
  rw [← comap_comp, ← comap_comp, morphismRestrict_ι]

theorem IsMonomialIn.comap_of_isMonomialIn {E : Bdy X} {M : ISD X}
    (hM : IsMonomialIn E M) (h : Y ⟶ X) :
    IsMonomialIn (E.map fun D : ISD X => D.comap h) $ M.comap h := by
  intro y
  obtain ⟨U, hU, a, ha⟩ := hM $ bsM h y
  have hlen : lenL (E.map fun D : ISD X => cmI D h) = lenL E := by simp
  refine ⟨preU h U, hU, fun i => a $ cast hlen i, ?_⟩
  have hget : ∀ i : Fin (E.map fun D : ISD X => cmI D h).length,
      get (E.map fun D : ISD X => cmI D h) i
        = cmI (get E $ cast hlen i) h := by simp_all
  have hterm : ∀ i,
      ((cmI (get E i) U.i) ^ a i).comap (mrU h U)
        = cmI (cmI (get E i) h) (preU h U).i ^ a i := by
    intro i
    rw [comap_pow, ← comap_comap_io h (get E i) U]
  rw [comap_comap_io h M U, ha, comap_finset_prod, prod_congr rfl fun i _ => hterm i,
    ← prod_congr'
      (fun j => cmI (cmI (get E j) h) (preU h U).i ^ a j) hlen]
  refine prod_congr rfl ?_
  intro i _
  rw [hget i]

section
variable (h : Y ⟶ X)
section
variable (hg : GeneralizingMap fun y : Y => h.base y)
include hg
theorem isMonomialSplitting_comap_of_generalizingMap {E : Bdy X}
    {I M N : ISD X} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (E.map fun D : ISD X => D.comap h) (I.comap h) (M.comap h)
      (N.comap h) where
  eq_mul := by rw [hs.eq_mul, comap_mul]
  monomial_support := by
    intro y hy
    obtain ⟨D, hD, hyD⟩ := Set.mem_iUnion₂.mp $ (hs.monomial_support) $ mp_ mem_support_comap hy
    exact Set.mem_iUnion₂.mpr ⟨cmI D h, mpr_ mem_map ⟨D, hD, rfl⟩, mpr_ mem_support_comap hyD⟩
  monomial := hs.monomial.comap_of_isMonomialIn h
  transversal := by
    rintro D' hD' C hC hCsub hCmax hCN
    obtain ⟨D, hD, hDD⟩ := mp_ mem_map hD'
    have hDD' := sy_ hDD
    subst hDD'
    have hCclosed : IsClosed C := by
      rw [← closure_subset_iff_isClosed]
      exact hCmax (closure C) hC.closure
        (closure_minimal hCsub (cmI D h).support.isClosed) subset_closure
    obtain ⟨xi_, hxi_⟩ := m140 hC hCclosed
    have hxiC_ : xi_ ∈ C := by
      rw [← hxi_]
      exact subset_closure $ mem_singleton xi_
    have hxD :=
      mem_support_comap.mp $ hCsub hxiC_
    have hxN :=
      mem_support_comap.mp $ hCN hxiC_
    let _a0 := closure ({h.base xi_} : Set X)
    refine (hs.transversal) D hD _a0 isIrreducible_singleton.closure
      (closure_minimal (mpr_ singleton_subset_iff hxD) D.support.isClosed) ?_
      (closure_minimal (mpr_ singleton_subset_iff hxN) N.support.isClosed)
    intro C'' hC'' hC''sub hsub
    obtain ⟨et_, het_⟩ := m140 hC''.closure isClosed_closure
    have hetmem : et_ ∈ closure C'' := by
      rw [← het_]
      exact subset_closure $ mem_singleton et_
    have hetD :=
      closure_minimal hC''sub D.support.isClosed hetmem
    have hetspec : et_ ⤳ bsM h xi_ := by
      refine mpr_ specializes_iff_mem_closure ?_
      rw [het_]
      exact subset_closure $ hsub $ subset_closure $ mem_singleton _
    obtain ⟨xi', hxi'1, hxi'2⟩ := hg hetspec
    have hxi'D : xi' ∈ (spI (cmI D h) : Set Y) := by simp_all
    have hclos :=
      closure_minimal (mpr_ singleton_subset_iff hxi'D) (cmI D h).support.isClosed
    let _a1 := closure ({xi'} : Set Y)
    have hCsubxi' : C ⊆ _a1 := by
      rw [← hxi_]
      exact closure_minimal
        (mpr_ singleton_subset_iff $ mp_ specializes_iff_mem_closure hxi'1) isClosed_closure
    have hclosure :=
      hCmax _a1 isIrreducible_singleton.closure hclos hCsubxi'
    have hxi'C := hclosure $ subset_closure $ mem_singleton _
    have hspec : xi_ ⤳ xi' := by
      refine mpr_ specializes_iff_mem_closure ?_
      rwa [hxi_]
    have hetclos : et_ ∈ _a0 := by
      rw [← hxi'2]
      exact mp_ specializes_iff_mem_closure $ hspec.map h.continuous
    intro z hz
    have hzc := subset_closure hz
    rw [← het_] at hzc
    exact closure_minimal (mpr_ singleton_subset_iff hetclos) isClosed_closure hzc
end

theorem isMonomialSplitting_comap_of_flat [Flat h]
    {E : Bdy X} {I M N : ISD X} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (E.map fun D : ISD X => D.comap h) (I.comap h) (M.comap h)
      (N.comap h) :=
  isMonomialSplitting_comap_of_generalizingMap h (AlgebraicGeometry.Flat.generalizingMap h) hs

end

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

variable {X : Sch}

theorem orderAt_eq_of_stalkIdeal_eq_maximalIdeal_pow [IsLocallyNoetherian X]
    (M : ISD X) (et_ : X) (a : ℕ)
    (hM : stalkIdeal M et_ = maximalIdeal ↥(X.presheaf.stalk et_) ^ a)
    (hfin : orderAt M et_ ≠ ⊤) :
    orderAt M et_ = (a : ENat) := by
  have hle := mpr_ (le_orderAt_iff M et_ a) $ le_of_eq hM
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hordn := sy_ hn
  have han : a ≤ n := by
    rw [hordn] at hle
    exact_mod_cast hle
  have hna : n ≤ a := by
    by_contra hc
    push Not at hc
    have hc' : a + 1 ≤ n := by omega
    have h1 : ((a + 1) : ENat) ≤ orderAt M et_ := by
      rw [hordn]
      exact_mod_cast hc'
    have h2 :=
      (le_orderAt_iff M et_ $ a + 1).mp h1
    let _a0 := maximalIdeal $ stkX X et_
    have hps : _a0 •
        (_a0 ^ a)
        = _a0 ^ (a + 1) := by
      rw [Ideal.smul_eq_mul, pow_succ, mul_comm]
    have hsm : (_a0 ^ a) ≤
        _a0 •
          (_a0 ^ a) := by
      rwa [hps, ← hM]
    have hz :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
        _a0
        (_a0 ^ a)
        (m187 _) hsm
        (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    exact (fun h => hfin $ mpr_ (orderAt_eq_top_iff M et_) h) $ by rw [hM, hz]
  rw [hordn]
  exact_mod_cast le_antisymm hna han

def IsMonomialOnOpen (E : Bdy X) (M : ISD X) (U : Opn X)
    (a : Fin E.length → ℕ) : Prop :=
  restrictIdeal M U =
    ((finRange E.length).map fun j => restrictIdeal (get E j) U ^ a j).prod

section
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
theorem ideal_map_listProd
    (L : List $ Ideal R) :
    Ideal.map f L.prod = (L.map fun I => Ideal.map f I).prod :=
  map_list_prod (mapHom f) L

theorem eq_of_ideal_map_eq_of_ringHom_leftInverse (g : S →+* R) (hgf : ∀ z, g (f z) = z) {A B}
    (hAB : Ideal.map f A = Ideal.map f B) : A = B := by
  have hcomp : g.comp f = RingHom.id R := RingHom.ext hgf
  have hA : Ideal.map g (Ideal.map f A) = A := by rw [Ideal.map_map, hcomp, Ideal.map_id]
  have hB : Ideal.map g (Ideal.map f B) = B := by rw [Ideal.map_map, hcomp, map_id]
  rw [← hA, ← hB, hAB]
end

theorem inv_hom_apply_hom_apply {A B : CRC} (f : A ⟶ B) [IsIso f]
    (z : A) : (inv f).hom (f.hom z) = z :=by simp_all
theorem stalkIdeal_eq_prod_of_isMonomialOnOpen (E : Bdy X) M
    (U : Opn X) a (h : IsMonomialOnOpen E M U a) x (hx : x ∈ U) :
    stalkIdeal M x =
      ((finRange E.length).map fun j => stalkIdeal (get E j) x ^ a j).prod := by
  have hxr : x ∈ range (U.ib) := by simp_all
  obtain ⟨y, hy⟩ := hxr
  subst hy
  have hgf :=
    fun z => inv_hom_apply_hom_apply (U.ι.stalkMap y) z
  refine eq_of_ideal_map_eq_of_ringHom_leftInverse (U.ι.stalkMap y).hom (inv $ U.ι.stalkMap y).hom hgf ?_
  have hL : ((finRange E.length).map
        (fun j => stalkIdeal (get E j) (opIb U y) ^ a j)).map
        (fun I => m6 (U.ι.stalkMap y).hom I)
      = ((finRange E.length).map fun j => restrictIdeal (get E j) U ^ a j).map
        (stalkIdeal · y) := by
    rw [map_map, map_map]
    refine map_congr_left ?_
    intro j _
    show Ideal.map (U.ι.stalkMap y).hom (stalkIdeal (get E j) (opIb U y) ^ a j)
        = stalkIdeal (restrictIdeal (get E j) U ^ a j) y
    rw [stalkIdeal_pow, restrictIdeal_eq_comap_io, stalkIdeal_comap, Ideal.map_pow]
  rw [ideal_map_listProd, hL, ← stalkIdeal_listProd, ← h, restrictIdeal_eq_comap_io,
    stalkIdeal_comap]

section
variable {k : Type} [Field k] [CharZero k] [NoetherianSpace ↥X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] (E : Bdy X)
theorem orderAt_genericPoint_eq_of_isMonomialSplitting (_hE : InStrictNormalCrossingPosition p E) {I M N : ISD X}
    (_hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    {D : ISD X} (hD : D ∈ E) {C} (hC : IsIrreducibleComponentOfSupport D C) :
    orderAt M hC.isIrreducible.genericPoint = orderAt I hC.isIrreducible.genericPoint := by
  have hmax' : ∀ C', IsIrreducible C' → C' ⊆ spI D → C ⊆ C' → C' ⊆ C := by
    intro C' h1 h2 h3
    intro y hy
    rwa [hC.maximal C' h1 h3 h2] at hy
  have hetN : hC.isIrreducible.genericPoint ∉ spI N := by
    intro h
    refine (hsplit.transversal D hD C hC.isIrreducible hC.subset_support hmax') ?_
    rw [← hC.closure_genericPoint]
    exact (N.support.2).closure_subset_iff.mpr $ mpr_ singleton_subset_iff h
  rw [hsplit.eq_mul, orderAt_mul k p M N hC.isIrreducible.genericPoint, (orderAt_eq_zero_iff_not_mem_support N hC.isIrreducible.genericPoint).mpr hetN, add_zero]

theorem exponent_le_orderAlongComponent (_hE : InStrictNormalCrossingPosition p E) {I M N}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (U : Opn X) a (ha : IsMonomialOnOpen E M U a)
    l {C'} (hC' : IsIrreducibleComponentOfSupport (get E l) C')
    x (hxU : x ∈ U) (hxC : x ∈ C') :
    a l ≤ orderAlongComponent I hC'.isIrreducible := by
  have hxcl := hxC
  rw [← hC'.closure_genericPoint] at hxcl
  have hetU : hC'.isIrreducible.genericPoint ∈ U := by
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hxcl U U.isOpen hxU
    rw [mem_singleton_iff] at hz
    rwa [← hz]
  have hlen : l <
      ((finRange E.length).map
        (fun j => stalkIdeal (get E j) hC'.isIrreducible.genericPoint ^ a j)).length := by
    simp
  have hget : ((finRange E.length).map
        (fun j => stalkIdeal (get E j) hC'.isIrreducible.genericPoint ^ a j))[l]'hlen
      = stalkIdeal (get E l) hC'.isIrreducible.genericPoint ^ a l := by
    simp
  have h1 : stalkIdeal M hC'.isIrreducible.genericPoint ≤
      stalkIdeal (get E l) hC'.isIrreducible.genericPoint ^ a l := by
    rw [stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a ha hC'.isIrreducible.genericPoint hetU, ← hget]
    exact list_prod_le_getElem _ _ hlen
  have hIM : I ≤ M := by
    rw [hsplit.eq_mul]
    refine (le_iff_forall_stalkIdeal_le _ _).mpr fun y => ?_
    rw [stalkIdeal_mul]
    exact mul_le_inf.trans inf_le_left
  have h4 := ((le_orderAt_iff M hC'.isIrreducible.genericPoint $ a l).mpr $ h1.trans $ pow_right_mono ((mem_support_iff_stalkIdeal_le_maximalIdeal (get E l) hC'.isIrreducible.genericPoint).mp hC'.genericPoint_mem_support) $ a l).trans $ orderAt_le_of_le hIM hC'.isIrreducible.genericPoint
  rw [← coe_orderAlongComponent_eq_orderAt_genericPoint hC' hI] at h4
  exact_mod_cast h4
end

section
variable {R : Type} [CommRing R]
section
variable (L : List (Ideal R))
theorem ideal_listProd_le_mul_getElem_of_lt :
    ∀ i j (hi : i < length L) (hj : j < length L), i < j →
      L.prod ≤ (L[i]'hi) * (L[j]'hj) := by
  induction L with
  | nil =>
      intro i _ hi _ _
      simp at hi
  | cons A L ih =>
      intro i j hi hj hij
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd hij $ lt_irrefl 0
          | succ j' =>
              have hj' := by simpa using hj
              simp [prod_cons, getElem_cons_zero, getElem_cons_succ]
              exact mul_mono le_rfl $ list_prod_le_getElem L j' hj'
      | succ i' =>
          cases j with
          | zero => exact absurd hij $ not_lt_zero _
          | succ j' =>
              have hi' := by simpa using hi
              have hj' := by simpa using hj
              simp [prod_cons, getElem_cons_succ]
              exact le_trans (le_trans mul_le_inf inf_le_right)
                (ih i' j' hi' hj' $ by omega)

end

theorem ideal_listProd_le_pow_add m
    (L : List $ Ideal R) i j (hi : i < length L) (hj : j < length L) (hij : i ≠ j)
    b c (hbi : (L[i]'hi) ≤ m ^ b) (hcj : (L[j]'hj) ≤ m ^ c) :
    L.prod ≤ m ^ (b + c) := by
  have _i23 : L.prod ≤ (L[i]'hi) * (L[j]'hj) := by
    rcases lt_or_gt_of_ne hij with h | h
    exact ideal_listProd_le_mul_getElem_of_lt L i j hi hj h
    rw [mul_comm]
    exact ideal_listProd_le_mul_getElem_of_lt L j i hj hi h
  refine le_trans _i23 ?_
  rw [pow_add]
  exact mul_mono hbi hcj

theorem ideal_listProd_finRange_eq_of_ne_eq_top {n : ℕ}
    (f : Fin n → Ideal R) (j : Fin n) (h : ∀ l : Fin n, l ≠ j → f l = ⊤) :
    ((finRange n).map f).prod = f j := by
  rw [← prod_univ_def]
  refine prod_eq_single j (fun l _ hl => ?_) fun hj => absurd (mem_univ j) hj
  rw [h l hl, one_eq_top]
end

theorem map_finRange_get_eq_map {al_ : Type} {be_ : Type} (l : List al_) (g : al_ → be_) :
    (finRange l.length).map (fun j => g $ get l j) = l.map g := by
  refine ext_getElem (by simp) ?_
  intro n h1 h2
  simp

section
variable {k : Type} [Field k] [CharZero k] [NoetherianSpace ↥X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] (E : Bdy X) (hE : InStrictNormalCrossingPosition p E)
include hE
section
variable {I M N : ISD X} (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
include hI hsplit
theorem stalkIdeal_eq_stalkIdeal_monomialFactorIdeal (x : X) :
    stalkIdeal M x = stalkIdeal (monomialFactorIdeal E I) x := by
  obtain ⟨U, hxU, a, haU⟩ := hsplit.monomial x
  have hmon : IsMonomialOnOpen E M U a := by
    show M.comap U.i
        = ((finRange E.length).map fun j => (get E j).comap U.i ^ a j).prod
    rw [haU, prod_univ_def]
  have hstep : ∀ j,
      stalkIdeal (get E j) x ^ a j = stalkIdeal (monomialPartAlongDivisor I $ get E j) x := by
    intro j
    have hmem : get E j ∈ E := by simp
    by_cases hx : x ∈ (spI (get E j) : Set X)
    obtain ⟨C, hC, hxC⟩ := exists_isIrreducibleComponentOfSupport (get E j) x hx
    have _i24 : a j = orderAlongComponent I hC.isIrreducible := by
      have hD : get E j ∈ E := by simp
      have hxcl := hxC
      rw [← hC.closure_genericPoint] at hxcl
      have hetU : hC.isIrreducible.genericPoint ∈ U := by
        obtain ⟨z, hzU, hz⟩ := mp_ mem_closure_iff hxcl (U : Set X) U.isOpen hxU
        rw [mem_singleton_iff] at hz
        rwa [← hz]
      have hlocj :=
        isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (get E j) hD
      have hbj : stalkIdeal (monomialPartAlongDivisor I $ get E j) hC.isIrreducible.genericPoint ≤
          maximalIdeal (stkX X hC.isIrreducible.genericPoint) ^
            orderAlongComponent I hC.isIrreducible := by
        rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I hlocj hC hC.genericPoint_mem]
        exact pow_right_mono ((mem_support_iff_stalkIdeal_le_maximalIdeal (get E j) hC.isIrreducible.genericPoint).mp hC.genericPoint_mem_support) _
      have hzero : ∀ l, l ≠ j →
          stalkIdeal (get E l) hC.isIrreducible.genericPoint ^ a l = ⊤ := by
        intro l hlj
        by_cases hs : hC.isIrreducible.genericPoint ∈ (spI (get E l) : Set X)
        have hal : a l = 0 := by
          obtain ⟨C', hC', hetC'⟩ :=
            exists_isIrreducibleComponentOfSupport (get E l) hC.isIrreducible.genericPoint hs
          have hDl : get E l ∈ E := by simp
          have hlmax :=
            mp_ (mem_support_iff_stalkIdeal_le_maximalIdeal (get E l)
              hC.isIrreducible.genericPoint) hs
          have hbl : stalkIdeal (monomialPartAlongDivisor I $ get E l) hC.isIrreducible.genericPoint ≤
              maximalIdeal (stkX X hC.isIrreducible.genericPoint) ^ a l := by
            rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I (isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (get E l) hDl) hC' hetC']
            exact le_trans (pow_right_mono hlmax _) $ pow_le_pow_right $ exponent_le_orderAlongComponent p E hE hI hsplit U a hmon l hC' hC.isIrreducible.genericPoint hetU hetC'
          have hjlen : (j : ℕ) <
              lenL (E.map fun D => stalkIdeal (monomialPartAlongDivisor I D)
                hC.isIrreducible.genericPoint) := by
            simp
          have hllen : (l : ℕ) <
              lenL (E.map fun D => stalkIdeal (monomialPartAlongDivisor I D)
                hC.isIrreducible.genericPoint) := by
            simp
          have hjne : (j : ℕ) ≠ (l : ℕ) := by
            intro hv
            apply hlj
            ext
            exact sy_ hv
          have hgj : (E.map fun D => stalkIdeal (monomialPartAlongDivisor I D)
              hC.isIrreducible.genericPoint)[(j : ℕ)]'hjlen =
              stalkIdeal (monomialPartAlongDivisor I $ get E j) hC.isIrreducible.genericPoint := by
            simp
          have hgl : (E.map fun D => stalkIdeal (monomialPartAlongDivisor I D)
              hC.isIrreducible.genericPoint)[(l : ℕ)]'hllen =
              stalkIdeal (monomialPartAlongDivisor I $ get E l) hC.isIrreducible.genericPoint := by
            simp
          have hPle : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint ≤
              maximalIdeal (stkX X hC.isIrreducible.genericPoint) ^
                (orderAlongComponent I hC.isIrreducible + a l) := by
            rw [stalkIdeal_monomialFactorIdeal E I hC.isIrreducible.genericPoint]
            refine ideal_listProd_le_pow_add _ _ (j : ℕ) (l : ℕ) hjlen hllen hjne _ _ ?_ ?_
            simp_all
            simp_all
          have hord :=
            mpr_ (le_orderAt_iff (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
              (orderAlongComponent I hC.isIrreducible + a l)) hPle
          rw [orderAt_monomialFactorIdeal_genericPoint p E I hE hI hD hC] at hord
          have hnat : orderAlongComponent I hC.isIrreducible + a l ≤
              orderAlongComponent I hC.isIrreducible := by exact_mod_cast hord
          omega
        rw [hal, pow_zero, one_eq_top]
        have hstop : stalkIdeal (get E l) hC.isIrreducible.genericPoint = ⊤ := by
          by_contra hcon
          exact hs $ mpr_ (mem_support_iff_stalkIdeal_ne_top (get E l)
            hC.isIrreducible.genericPoint) hcon
        rw [hstop, ← one_eq_top, one_pow]
      have hprod :=
        stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a hmon hC.isIrreducible.genericPoint hetU
      have hMstalk : stalkIdeal M hC.isIrreducible.genericPoint =
          stalkIdeal (get E j) hC.isIrreducible.genericPoint ^ a j := by
        rw [hprod]
        exact ideal_listProd_finRange_eq_of_ne_eq_top
          (fun i => stalkIdeal (get E i) hC.isIrreducible.genericPoint ^ a i) j hzero
      have hmaxj :=
        stalkIdeal_genericPoint_eq_maximalIdeal p (get E j) hlocj hC.isIrreducible
          hC.subset_support hC.maximal
      have hMI :=
        orderAt_genericPoint_eq_of_isMonomialSplitting p E hE hI hsplit hD hC
      have hfin : orderAt M hC.isIrreducible.genericPoint ≠ ⊤ := by
        rw [hMI]
        exact orderAt_ne_top_of_nonzeroOnComponents I hI hC.isIrreducible.genericPoint
      have hMord :=
        orderAt_eq_of_stalkIdeal_eq_maximalIdeal_pow M hC.isIrreducible.genericPoint (a j)
          (by rw [hMstalk, hmaxj]) hfin
      have hco := coe_orderAlongComponent_eq_orderAt_genericPoint hC hI
      have hfinal : ((a j : ℕ) : ENat) = ((orderAlongComponent I hC.isIrreducible : ℕ) : ENat) := by simp_all
      exact_mod_cast hfinal
    rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I (isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (get E j) hmem) hC hxC,
      _i24]
    have h1 : stalkIdeal (get E j) x = ⊤ := by
      by_contra hne
      exact hx $ mpr_ (mem_support_iff_stalkIdeal_ne_top (get E j) x) hne
    rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I (get E j) hx, h1,
      ← one_eq_top, one_pow]
  have hlist : (finRange E.length).map (fun j => stalkIdeal (get E j) x ^ a j)
      = E.map fun D => stalkIdeal (monomialPartAlongDivisor I D) x := by
    rw [← map_finRange_get_eq_map E fun D => stalkIdeal (monomialPartAlongDivisor I D) x]
    exact map_congr_left fun j _ => hstep j
  rw [stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a hmon x hxU,
    stalkIdeal_monomialFactorIdeal E I x, hlist]

theorem eq_monomialFactorIdeal :
    M = monomialFactorIdeal E I := by
  let _a0 := monomialFactorIdeal E I
  have hstalk :=
    fun x => stalkIdeal_eq_stalkIdeal_monomialFactorIdeal p E hE hI hsplit x
  refine le_antisymm ?_ ?_
  exact mpr_ (le_iff_forall_stalkIdeal_le M _a0)
    (fun x => le_of_eq $ hstalk x)
  exact mpr_ (le_iff_forall_stalkIdeal_le _a0 M)
    (fun x => le_of_eq (hstalk x).symm)

theorem eq_nonMonomialFactorIdeal :
    N = nonMonomialFactorIdeal E I := by
  have hM := eq_monomialFactorIdeal p E hE hI hsplit
  have hF :=
    isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal p E I hE
  have hIM : I ≤ monomialFactorIdeal E I := by
    rw [← hM, hsplit.eq_mul]
    refine (le_iff_forall_stalkIdeal_le _ _).mpr fun y => ?_
    rw [stalkIdeal_mul]
    exact mul_le_inf.trans inf_le_left
  refine hF.eq_of_mul_eq_mul ?_
  rw [nonMonomialFactorIdeal_eq_idealSheafColon, hF.mul_idealSheafColon hIM, ← hM]
  exact hsplit.eq_mul.symm
end

theorem isMonomialSplitting_unique {I M N M' N'}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (hsplit' : IsMonomialSplitting E I M' N') :
    M = M' ∧ N = N' :=
  ⟨tr_ (eq_monomialFactorIdeal p E hE hI hsplit)
      (eq_monomialFactorIdeal p E hE hI hsplit').symm,
    (eq_nonMonomialFactorIdeal p E hE hI hsplit).trans
      (eq_nonMonomialFactorIdeal p E hE hI hsplit').symm⟩
end

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

structure StrictPullbackBlowupSeq {X' X : Sch} (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) where
  comp : ∀ i : ℕ, i ≤ t.length → (schemeAt t i ⟶ schemeAt s i)
  comp_zero : comp 0 (zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g
  pullback : ∀ i : ℕ, ∀ hi : i < t.length,
    IsPullback (comp (i + 1) hi) (transitionMapSucc t i) (transitionMapSucc s i) $ comp i hi.le
  length_eq : t.length = s.length
  center_eq : ∀ i : ℕ, ∀ hi : i < t.length,
    center t i = (center s i).comap (comp i hi.le)

namespace StrictPullbackBlowupSeq

variable {X' X} {g : X' ⟶ X} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}

theorem isStrictPullback (D : StrictPullbackBlowupSeq g t s) : IsStrictPullbackBlowupSeq g t s :=
  ⟨D.length_eq, D.comp, D.comp_zero, D.pullback, D.center_eq⟩

theorem map_zero_eq (D : StrictPullbackBlowupSeq g t s) :
    D.comp 0 (zero_le _) = t.isoZero.hom ≫ g ≫ s.isoZero.inv := by
  rw [← assoc, ← D.comp_zero, assoc, m145, comp_id]

theorem flat_map [Flat g] (D : StrictPullbackBlowupSeq g t s)
    i (hi : i ≤ t.length) : Flat $ D.comp i hi := by
  revert hi
  induction i with
  | zero =>
      intro hi
      exact (of_isPullback
    (P := @Flat) (IsPullback.of_horiz_isIso ⟨D.comp_zero.symm⟩) inferInstance)
  | succ j ih =>
      intro hi
      have hjl : j < t.length := hi
      exact (of_isPullback
    (P := @Flat) (D.pullback j hjl).flip $ ih hjl.le)

theorem surjective_map [Flat g] [Surjective g]
    (D : StrictPullbackBlowupSeq g t s) i (hi : i ≤ t.length) :
    Surjective $ D.comp i hi :=
  (flat_and_surjective_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero D.pullback i hi).2

end StrictPullbackBlowupSeq

noncomputable def IsStrictPullbackBlowupSeq.toStrictPullbackBlowupSeq {X' X : Sch} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s) :
    StrictPullbackBlowupSeq g t s where
  comp := h.2.choose
  comp_zero := h.2.choose_spec.1
  pullback := h.2.choose_spec.2.1
  length_eq := h.length_eq
  center_eq := h.2.choose_spec.2.2

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X} (t : MarkedBlowupSequenceData p I m E) {i : ℕ}
theorem MarkedBlowupSequenceData.le_toSequenceOfBlowups_length (hi : i ≤ t.length) :
    i ≤ t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length :=by simp_all
theorem MarkedBlowupSequenceData.lt_toSequenceOfBlowups_length (hi : i < t.length) :
    i < t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length :=by simp_all
end

section

variable {k : Type} [Field k] {X' X : Sch} {q : X' ⟶ Sp k}
  {g : X' ⟶ X} {I : ISD X} {m : ℕ} {E : Bdy X} {d : BlowupSequenceData X}

section
variable (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g)) (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
include D
section
variable (i : ℕ)
def MarkedBlowupSequenceData.strictPullbackComparisonMap (hi : i ≤ t.length) : t.obj i ⟶ d.obj i :=
  D.comp i $ t.le_toSequenceOfBlowups_length hi

theorem MarkedBlowupSequenceData.strictPullbackComparisonMap_eq_map (hi : i ≤ t.length) :
    t.strictPullbackComparisonMap D i hi = D.comp i (t.le_toSequenceOfBlowups_length hi) := rfl

section
variable (hi : i < t.length)
theorem MarkedBlowupSequenceData.isPullback_strictPullbackComparisonMap :
    IsPullback (t.strictPullbackComparisonMap D (i + 1) $ show i + 1 ≤ t.length from hi) (t.map i) (d.map i)
      (t.strictPullbackComparisonMap D i hi.le) := by
  have h := D.pullback i $ t.lt_toSequenceOfBlowups_length hi
  rwa [toMarkedSequence_blowupMorphism, p50] at h

theorem MarkedBlowupSequenceData.strictPullbackComparisonMap_comp_blowupMorphism :
    t.strictPullbackComparisonMap D (i + 1) (show i + 1 ≤ t.length from hi) ≫ d.map i =
      t.map i ≫ t.strictPullbackComparisonMap D i hi.le :=
  (t.isPullback_strictPullbackComparisonMap D i hi).w

theorem MarkedBlowupSequenceData.center_eq_comap_strictPullbackComparisonMap :
    t.center i = (d.center i).comap (t.strictPullbackComparisonMap D i hi.le) :=
  D.center_eq i $ t.lt_toSequenceOfBlowups_length hi

theorem MarkedBlowupSequenceData.exceptionalIdeal_eq_comap_strictPullbackComparisonMap :
    exceptionalIdeal (t.map i) (t.center i) =
      (exceptionalIdeal (d.map i) $ d.center i).comap
        (t.strictPullbackComparisonMap D (i + 1) $ show i + 1 ≤ t.length from hi) := by
  rw [p9, p9, t.center_eq_comap_strictPullbackComparisonMap D i hi, ← comap_comp,
    ← comap_comp, t.strictPullbackComparisonMap_comp_blowupMorphism D i hi]
end
end

theorem MarkedBlowupSequenceData.strictPullbackComparisonMap_zero :
    t.strictPullbackComparisonMap D 0 (zero_le _) ≫ d.isoZero.hom = t.isoZero.hom ≫ g :=
  D.comp_zero

theorem MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq :
    t.length = d.length := by
  have h := D.length_eq
  rw [toMarkedSequence_toSequenceOfBlowups] at h
  simpa only [toSequenceOfBlowups_length] using h

theorem MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform
    (hdiv : ∀ i < d.length, ∃ B : IdealSheafData $ d.obj $ i + 1,
      exceptionalIdeal (d.map i) (d.center i) ^ m * B =
        (d.controlledTransform I m i).comap (d.map i))
    i (hi : i ≤ t.length) :
    t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i hi) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      rw [t.ideal_zero, d.controlledTransform_zero I m, ← comap_comp,
        ← comap_comp, t.strictPullbackComparisonMap_zero D]
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have hjd : j < d.length := by
        have hlen := t.length_eq_of_strictPullbackBlowupSeq D
        omega
      let _a0 := p5 (t.map j) $ t.center j
      let _a1 := t.strictPullbackComparisonMap D (j + 1) hi
      have hexc : _a0 =
          (p5 (d.map j) $ d.center j).comap _a1 :=
        t.exceptionalIdeal_eq_comap_strictPullbackComparisonMap D j hj
      have hcomp : _a1 ≫ d.map j = t.map j ≫ t.strictPullbackComparisonMap D j hj.le :=
        t.strictPullbackComparisonMap_comp_blowupMorphism D j hj
      have hih : t.ideal j = cmI (d.controlledTransform I m j) (t.strictPullbackComparisonMap D j hj.le) := ih hj.le
      have hsucc : _a0 ^ m * t.ideal (j + 1) =
          (t.ideal j).comap (t.map j) := t.ideal_succ j hj
      have main : _a0 ^ m *
          (d.controlledTransform I m $ j + 1).comap _a1 =
          _a0 ^ m * t.ideal (j + 1) := by
        rw [hsucc, hih, hexc, ← comap_pow,
          ← comap_mul, d.pow_exceptionalIdeal_mul_controlledTransform_succ I m j $ hdiv j hjd, ← comap_comp,
          ← comap_comp, hcomp]
      exact sy_ $ ((isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal
        (t.isBlowup j hj)).pow m).eq_of_mul_eq_mul main
end

section
variable [Flat g]
section
variable (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g)) (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
theorem MarkedBlowupSequenceData.flat_strictPullbackComparisonMap
    i (hi : i ≤ t.length) : Flat $ t.strictPullbackComparisonMap D i hi := by
  rw [MarkedBlowupSequenceData.strictPullbackComparisonMap_eq_map]
  exact D.flat_map i $ t.le_toSequenceOfBlowups_length hi

theorem MarkedBlowupSequenceData.boundary_eq_comap_strictPullbackComparisonMap
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    i (hi : i ≤ t.length) :
    t.boundary i = (d.boundaryFrom E i).map fun A => A.comap (t.strictPullbackComparisonMap D i hi) := by
  revert hi
  induction i with
  | zero =>
      intro hi
      have key : ∀ A : ISD X,
          (cmI A g).comap t.isoZero.hom =
            (cmI A d.isoZero.hom).comap (t.strictPullbackComparisonMap D 0 hi) := by
        intro A
        rw [← m56, ← m56, t.strictPullbackComparisonMap_zero D]
      rw [MarkedBlowupSequenceData.boundary_zero, BlowupSequenceData.boundary_zero]
      simp [List.map_map, Function.comp_def, key]
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have hlen := t.length_eq_of_strictPullbackBlowupSeq D
      have hjd : j < d.length := by omega
      have : IsLocallyNoetherian (d.obj (j + 1)) := hNd (j + 1) hjd
      have : IsLocallyNoetherian (t.obj (j + 1)) := hNt (j + 1) hi
      have : Flat (t.strictPullbackComparisonMap D j hj.le) := t.flat_strictPullbackComparisonMap D j hj.le
      have hst : ∀ A : ISD (d.obj j),
          p6 (t.map j) (t.center j) (cmI A (t.strictPullbackComparisonMap D j hj.le)) =
            (p6 (d.map j) (d.center j) A).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
        intro A
        have h := comap_strictTransform_of_flat_of_isLocallyNoetherian (d.map j)
          (t.strictPullbackComparisonMap D j hj.le) (t.map j) (t.strictPullbackComparisonMap D (j + 1) hi)
          (t.isPullback_strictPullbackComparisonMap D j hj) (d.center j) A (d.isBlowup j hjd)
        rw [h, t.center_eq_comap_strictPullbackComparisonMap D j hj]
      rw [t.boundary_succ j hj, ih hj.le, d.boundary_succ E j]
      simp [map_append, map_map, map_cons, map_nil,
        comp_def, hst, t.exceptionalIdeal_eq_comap_strictPullbackComparisonMap D j hj]
end

theorem MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap
    [Surjective g]
    (t : MarkedBlowupSequenceData q (I.comap g) m $ E.map fun A => A.comap g)
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    i (hi : i ≤ t.length) : Surjective $ t.strictPullbackComparisonMap D i hi := by
  rw [MarkedBlowupSequenceData.strictPullbackComparisonMap_eq_map]
  exact D.surjective_map i $ t.le_toSequenceOfBlowups_length hi
end

end

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

@[reducible] def lowerDimensionalFamily (A : ℕ → PrincipalizationAssignment) (T : MarkedIdealWithBoundary) :
    ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups :=
  fun S _ j => A j S

section
variable (hinv : ComapIsoInvariance) (A : ℕ → PrincipalizationAssignment)
noncomputable def maxContactPrincipalization :
    PrincipalizationAssignment :=
  fun T => reduceOrder hinv T $ lowerDimensionalFamily A T

@[simp] theorem maxContactPrincipalization_apply
    (T : MarkedIdealWithBoundary) :
    maxContactPrincipalization hinv A T = reduceOrder hinv T (lowerDimensionalFamily A T) := rfl
end

structure OrderReductionHypotheses (P : ℕ → Prop) (T : MarkedIdealWithBoundary) : Prop where
  dim_prop : P T.krullDimSucc
  orderLE : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)
  coSupport_nonempty : (orderAtLeastLocus T.ideal T.mult).Nonempty
  valid : IsAdmissible T

theorem OrderReductionHypotheses.orderAtLeastLocus_ne_empty {P} {T : MarkedIdealWithBoundary} (h : OrderReductionHypotheses P T) :
    orderAtLeastLocus T.ideal T.mult ≠ ∅ :=
  h.coSupport_nonempty.ne_empty

def IsLocalIsomorphism {W' W : Sch} (g : W' ⟶ W) : Prop :=
  ∀ x : ↥W', ∃ U : Opn W', x ∈ U ∧ IsOpenImmersion (U.i ≫ g)

noncomputable abbrev coverBlowupSequence (hinv : ComapIsoInvariance) (A : ℕ → PrincipalizationAssignment)
    (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) :
    MarkedBlowupSequenceData (cT hv).structMap
      (cT hv).ideal (cT hv).mult
      (cT hv).boundary :=
  coverMarkedBlowupData T hv hinv $ lowerDimensionalFamily A T

structure CoverSequenceProperties (hinv : ComapIsoInvariance) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment) : Prop where
  center_ne_top : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T),
    ∀ i < (coverBlowupSequence hinv A T h.valid).length,
      (coverBlowupSequence hinv A T h.valid).center i ≠ ⊤
  cert : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T), T.mult = 1 →
    ∀ i < (coverBlowupSequence hinv A T h.valid).length,
      OrderCertificate ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.schemeAt i)
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.projectionToBase i ≫
          (cT h.valid).structMap)
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.ideal i) 1
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.boundaryLocus i)
        ((coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.center i)
  descends : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T),
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq (coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups
  hypersurface : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T), T.boundary = [] → T.mult = 1 →
    ∀ Y q e
      [IsClosedImmersion e], e ≫ T.structMap = q →
      IsSmoothDivisor T.structMap (ker e) →
    ∀ J : ISD Y,
      (T.withSchemeIdealBoundary Y q J ([] : Bdy Y)).IsAdmissible →
      T.ideal = imageIdealSheaf e J →
      IsStrictPullbackBlowupSeq (coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups
        (A 0 $ T.withBoundary [ker e]).toSequenceOfBlowups
  resolves : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T),
    orderAtLeastLocus ((coverBlowupSequence hinv A T h.valid).ideal (coverBlowupSequence hinv A T h.valid).length)
      (tunedMult T) = ∅

structure DescentHypotheses (hinv : ComapIsoInvariance) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) : Prop where
  tuning : IsMarkedIffBalancedTunedSheaf
  cert_descend : ∀ (k : Type) [Field k] (W' W : Sch)
      (p : W ⟶ Sp k) (g : W' ⟶ W),
      IsLocalIsomorphism g → Surjective g →
    ∀ (N : ISD W) (mu_ : ℕ) (Mem : Set ↥W) (Z : ISD W),
      OrderCertificate W' (g ≫ p) (N.comap g) mu_ (g.base ⁻¹' Mem) (Z.comap g) →
      OrderCertificate W p N mu_ Mem Z
  base_change : ∀ T : MarkedIdealWithBoundary, IsAdmissible T → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (bc T f).scheme.IdealSheafData),
      SameNontrivialBoundary (bc T f).boundary E' →
      (withBoundary (bc T f) E').IsAdmissible →
      P (withBoundary (bc T f) E').krullDimSucc →
      (∀ x : ↥(withBoundary (bc T f) E').scheme,
        orderAt (withBoundary (bc T f) E').ideal x ≤ (mult T : ENat)) →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (maxContactPrincipalization hinv A (withBoundary (bc T f) E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  base_change_strict : ∀ T : MarkedIdealWithBoundary, IsAdmissible T → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (bc T f).scheme.IdealSheafData),
      SameNontrivialBoundary (bc T f).boundary E' →
      (withBoundary (bc T f) E').IsAdmissible →
      P (withBoundary (bc T f) E').krullDimSucc →
      (∀ x : ↥(withBoundary (bc T f) E').scheme,
        orderAt (withBoundary (bc T f) E').ideal x ≤ (mult T : ENat)) →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (maxContactPrincipalization hinv A (withBoundary (bc T f) E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  comp_openImmersion : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme)
      (D : StrictPullbackBlowupSeq (coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
      (i : ℕ) (hi : i ≤ (coverBlowupSequence hinv A T h.valid).length),
      IsLocalIsomorphism
        (D.comp i ((coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi))
  locallyNoetherian : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme),
      IsStrictPullbackBlowupSeq (coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups →
      (∀ i ≤ d.length, IsLocallyNoetherian (d.obj i)) ∧
      (∀ i ≤ (coverBlowupSequence hinv A T h.valid).length,
        IsLocallyNoetherian ((coverBlowupSequence hinv A T h.valid).obj i))
  isMarked : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme),
      IsStrictPullbackBlowupSeq (coverMap T h.valid)
        (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups →
      d.IsMarked T.structMap (balancedTunedIdeal T h.valid)
        (tunedMult T) T.boundary
  isMarked_of_trim : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
    ∀ (d : BlowupSequenceData T.scheme) (I : tISD T) (m : ℕ),
      d.IsMarked T.structMap I m (MaxContactReduction.dropTrivialBoundary T).boundary →
      d.IsMarked T.structMap I m T.boundary
  order_le : ∀ T : MarkedIdealWithBoundary, IsAdmissible T →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
    ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.length →
      ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (mult T : ENat)
  smooth_pullback : ∀ T : MarkedIdealWithBoundary, IsAdmissible T → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (g : Y ⟶ scheme T)
      [Smooth g], g ≫ structMap T = q →
    ∀ E' : Bdy Y,
      SameNontrivialBoundary (T.pbA q g).boundary E' →
      IsAdmissible (T.pbB q g E') →
      P (T.pbB q g E').krullDimSucc →
      (∀ x : ↥(T.pbB q g E').scheme,
        orderAt (T.pbB q g E').ideal x ≤ (mult T : ENat)) →
      IsPullbackBlowupSequence g
        (maxContactPrincipalization hinv A (T.pbB q g E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ T : MarkedIdealWithBoundary, IsAdmissible T → P T.krullDimSucc →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (g : Y ⟶ scheme T)
      [Smooth g] [Surjective g], g ≫ structMap T = q →
    ∀ E' : Bdy Y,
      SameNontrivialBoundary (T.pbA q g).boundary E' →
      IsAdmissible (T.pbB q g E') →
      P (T.pbB q g E').krullDimSucc →
      (∀ x : ↥(T.pbB q g E').scheme,
        orderAt (T.pbB q g E').ideal x ≤ (mult T : ENat)) →
      IsStrictPullbackBlowupSeq g
        (maxContactPrincipalization hinv A (T.pbB q g E')).toSequenceOfBlowups
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups
  flat_coverMap : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T),
      Flat (coverMap T h.valid)
  surjective_coverMap : ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T),
      Surjective (coverMap T h.valid)
  valid_subst_ker : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (e : Y ⟶ scheme T)
      [IsClosedImmersion e], e ≫ structMap T = q →
    ∀ J : ISD Y, IsAdmissible (T.withSchemeIdealBoundary Y q J ([] : Bdy Y)) →
    ∀ (ep_ : Y ⟶ (ker e).subscheme),
      ep_ ≫ (ker e).si = e →
      (T.withSchemeIdealBoundary (ker e).subscheme
          ((ker e).si ≫ structMap T) (imageIdealSheaf ep_ J)
          ([] : List (ker e).subscheme.IdealSheafData)).IsAdmissible ∧
      (T.withSchemeIdealBoundary (ker e).subscheme
          ((ker e).si ≫ structMap T) (imageIdealSheaf ep_ J)
          ([] : List (ker e).subscheme.IdealSheafData)).krullDimSucc =
        (T.withSchemeIdealBoundary Y q J ([] : Bdy Y)).krullDimSucc
  tunedIdeal_of_mult_one : ∀ (T : MarkedIdealWithBoundary) (hv : IsAdmissible T), mult T = 1 →
      balancedTunedIdeal T hv = ideal T
  valid_trim : ∀ T : MarkedIdealWithBoundary, IsAdmissible T → IsAdmissible (MaxContactReduction.dropTrivialBoundary T)
  valid_withDivisor : ∀ T : MarkedIdealWithBoundary, IsAdmissible T → boundary T = [] →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (e : Y ⟶ scheme T)
      [IsClosedImmersion e], e ≫ structMap T = q →
      IsSmoothDivisor T.structMap (ker e) →
      IsAdmissible (withBoundary T [ker e])

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
end
section
universe v

open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {A B C : Sch}

section
variable (ga_ : A ⟶ B)
section
variable (W : Opn A) (h : IsOpenImmersion (W.i ≫ ga_))
def rangeOpens : Opn B :=
  ⟨range ⇑(W.ι ≫ ga_).base, by
    have := h
    exact isOpen_range _⟩

theorem mem_rangeOpens_iff
    b : b ∈ rangeOpens ga_ W h ↔ ∃ w, (W.i ≫ ga_).base w = b :=
  m22

theorem range_io_comp_eq_range_rangeOpens_io :
    range ⇑(W.i ≫ ga_).base = range ⇑(rangeOpens ga_ W h).ib :=
  (q1 $ rangeOpens ga_ W h).symm

noncomputable def isoRangeOpens :
    W.toScheme ≅ (rangeOpens ga_ W h).toScheme :=
  letI : IsOpenImmersion $ W.ι ≫ ga_ := h
  isoOfRangeEq (W.ι ≫ ga_) (rangeOpens ga_ W h).ι $ range_io_comp_eq_range_rangeOpens_io ga_ W h

theorem isoRangeOpens_hom_io :
    (isoRangeOpens ga_ W h).hom ≫ (rangeOpens ga_ W h).i = W.i ≫ ga_ := by
  let _a1 := opI W ≫ ga_
  let _a0 := rangeOpens ga_ W h
  have hsub : range _a1.base ⊆ range _a0.ib := by
    intro x hx
    rwa [← range_io_comp_eq_range_rangeOpens_io ga_ W h]
  exact m115 _a0.i _a1 hsub

theorem isoRangeOpens_inv_comp :
    (isoRangeOpens ga_ W h).inv ≫ W.ι ≫ ga_ = (rangeOpens ga_ W h).ι := by
  let _a1 := opI W ≫ ga_
  let _a0 := rangeOpens ga_ W h
  show isoI (isoOfRangeEq _a1 _a0.i
      (range_io_comp_eq_range_rangeOpens_io ga_ W h)) ≫ _a1 = opI _a0
  simp

theorem isoRangeOpens_hom_io_assoc
    (f : B ⟶ C) :
    (isoRangeOpens ga_ W h).hom ≫ (rangeOpens ga_ W h).i ≫ f = W.i ≫ ga_ ≫ f := by
  rw [← assoc, isoRangeOpens_hom_io, assoc]

theorem isoRangeOpens_inv_comp_assoc
    (f : B ⟶ C) :
    (isoRangeOpens ga_ W h).inv ≫ W.i ≫ ga_ ≫ f = (rangeOpens ga_ W h).i ≫ f := by
  have hassoc : isoI (isoRangeOpens ga_ W h) ≫ opI W ≫ ga_ ≫ f
      = (isoI (isoRangeOpens ga_ W h) ≫ opI W ≫ ga_) ≫ f := by
    simp [assoc]
  rw [hassoc, ← isoRangeOpens_hom_io ga_ W h, ← assoc, m114, id_comp]
end

theorem exists_mem_rangeOpens
    (hga_ : MaxContactFunctoriality.IsLocalIsomorphism ga_) [Surjective ga_]
    b :
    ∃ (U : Opn A) (hU : IsOpenImmersion $ U.i ≫ ga_), b ∈ rangeOpens ga_ U hU := by
  obtain ⟨a, ha⟩ := surj (f := ga_) b
  obtain ⟨U, haU, hU⟩ := hga_ a
  have hmem : a ∈ range U.ib := by simp_all
  obtain ⟨w, hw⟩ := hmem
  refine ⟨U, hU, mpr_ (mem_rangeOpens_iff ga_ U hU b) ⟨w, ?_⟩⟩
  have h1 : bsM (opI U ≫ ga_) w = bsM ga_ (opIb U w) := by simp
  rw [h1, hw, ha]
end

theorem le_of_map_le_of_leftInverse {R S : Type} [CommRing R] [CommRing S]
    (ps_ : R →+* S) (ps' : S →+* R) (hinv : ∀ x, ps' (ps_ x) = x) {A C : Ideal R}
    (hle : A.map ps_ ≤ C.map ps_) : A ≤ C := by
  intro a ha
  have h2 := Ideal.mem_map_of_mem ps' $ hle $ mem_map_of_mem ps_ ha
  rw [hinv a, Ideal.map_map] at h2
  have h3 : ps'.comp ps_ = m99 R := m48 hinv
  rwa [h3, m167] at h2

section
variable {X : Sch}
private theorem span_eq_top_of_forall_mem_basicOpen {V : Opn X}
    (hV : IsAffineOpen V) (S : Set $ X.sec V)
    (hcov : ∀ x : ↥X, x ∈ V → ∃ f ∈ S, x ∈ basicOpen X f) :
    span S = ⊤ := by
  rw [← hV.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : xSec X V)) ?_
  intro x hx
  obtain ⟨f, hfS, hxf⟩ := hcov x hx
  exact mpr_ mem_iSup ⟨⟨f, hfS⟩, hxf⟩

theorem comap_io_le_comap_io_of_le {I J : ISD X}
    {V W : Opn X} (hVW : V ≤ W) (hIJ : I.comap W.i ≤ J.comap W.i) :
    I.comap V.i ≤ J.comap V.i := by
  have hsub : range V.ib ⊆ range W.ib := by simp_all
  have hfac :=
    m115 W.i V.i hsub
  let _a0 := m43 W.i V.i hsub
  have h1 : (I.comap W.i).comap _a0 = I.comap V.i := by
    rw [← comap_comp, hfac]
  have h2 : (J.comap W.i).comap _a0 = J.comap V.i := by
    rw [← comap_comp, hfac]
  rw [← h1, ← h2]
  exact comap_mono _ hIJ

theorem ideal_le_ideal_of_comap_io_le {I J : ISD X}
    (V : X.affineOpens)
    (hc : I.comap (V : Opn X).ι ≤ J.comap (V : Opn X).ι) :
    I.ideal V ≤ J.ideal V := by
  let _a0 := (V : Opn X)
  have haffine : IsAffineOpen $ opI _a0 ''ᵁ (⊤ : _a0.toScheme.Opens) := by
    rw [Scheme.Opens.ι_image_top]
    exact V.2
  have e : (⊤)
      ≤ opI _a0 ⁻¹ᵁ (opI _a0 ''ᵁ (⊤)) :=
    fun x hx => ⟨x, hx, rfl⟩
  have hV : V = (⟨opI _a0 ''ᵁ (⊤ : _a0.toScheme.Opens), haffine⟩ : affO X) :=
    m26 (Scheme.Opens.ι_image_top _).symm
  have hI := comap_ideal_eq_map_appLE I (V : Opn X).i
      ⟨opI _a0 ''ᵁ (⊤ : _a0.toScheme.Opens), haffine⟩
      ⟨⊤, isAffineOpen_top (V : Opn X).toScheme⟩ e
  have hJ := comap_ideal_eq_map_appLE J (V : Opn X).i
      ⟨opI _a0 ''ᵁ (⊤ : _a0.toScheme.Opens), haffine⟩
      ⟨⊤, isAffineOpen_top (V : Opn X).toScheme⟩ e
  have hle : (cmI I (V : Opn X).i).ideal ⟨⊤, isAffineOpen_top (V : Opn X).toScheme⟩
      ≤ (cmI J (V : Opn X).i).ideal ⟨⊤, isAffineOpen_top (V : Opn X).toScheme⟩ :=
    hc ⟨⊤, isAffineOpen_top (V : Opn X).toScheme⟩
  rw [hI, hJ] at hle
  let _a1 := (opI _a0).appIso (⊤)
  have happ : appLE (opI _a0)
        (opI _a0 ''ᵁ (⊤))
        (⊤) e
      = isoH _a1 :=
    (appIso_hom' _ _).symm
  rw [happ] at hle
  rw [hV]
  refine le_of_map_le_of_leftInverse _
    (_a1.inv.hom) ?_ hle
  intro x
  let _m0 := _a0.ι.appIso (⊤)
  have h2 : (_m0.hom ≫
      _m0.inv).hom x = x := by simp_all
  simp only [hom_comp, coe_comp, comp_apply] at h2
  exact h2

theorem exists_pow_smul_mem_of_map_mem (V : X.affineOpens)
    (C : Ideal $ X.sec (V : Opn X)) (f a : (X.sec (V : Opn X)))
    (hmem : (X.presheaf.map (homOfLE $ X.basicOpen_le f).op).hom a ∈
      Ideal.map (X.presheaf.map (homOfLE $ X.basicOpen_le f).op).hom C) :
    ∃ n : ℕ, f ^ n • a ∈ C := by
  let _c0 := algebraMap (xSec X V) Γ(X, bOpn X f)
  have := V.2.isLocalization_basicOpen f
  have halg : _c0
      = (pMap X (homOfLE $ X.basicOpen_le f).op).hom := rfl
  rw [← halg, IsLocalization.mem_map_algebraMap_iff $ Submonoid.powers f] at hmem
  obtain ⟨⟨⟨c, hc⟩, ⟨m, hm⟩⟩, heq⟩ := hmem
  obtain ⟨k, hk⟩ := hm
  have heq' : _c0 (a * m)
      = _c0 c := by
    simpa using heq
  obtain ⟨d, hd⟩ :=
    (eq_iff_exists (Submonoid.powers f) Γ(X, bOpn X f)).mp heq'
  obtain ⟨j, hj⟩ := d.2
  refine ⟨j + k, ?_⟩
  have hmul := hd
  rw [← mul_comm m a, ← mul_assoc, ← hk, ← hj, ← pow_add] at hmul
  rw [smul_eq_mul, hmul]
  exact mul_mem_left _ _ hc
end

theorem le_of_forall_comap_io_le {ι : Type v} (U : ι → Opn B)
    (hU : ∀ b : ↥B, ∃ i, b ∈ U i) (J K : ISD B)
    (h : ∀ i, J.comap (U i).i ≤ K.comap (U i).i) : J ≤ K := by
  show ∀ V : affO B, J.ideal V ≤ K.ideal V
  intro V a ha
  have hVaff := V.2
  have hspan : span {f : (B.sec V) | ∃ i, bOpn B f ≤ U i} = ⊤ := by
    refine span_eq_top_of_forall_mem_basicOpen hVaff _ ?_
    intro x hx
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨f, hfle, hxf⟩ :=
      exists_basicOpen_le hVaff (⟨x, hi⟩ : (U i)) hx
    exact ⟨f, ⟨i, hfle⟩, hxf⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (K.ideal V) _ hspan a ?_
  rintro ⟨f, i, hfle⟩
  have ha' : (pMap B (homOfLE $ B.basicOpen_le f).op).hom a
      ∈ J.ideal (B.affineBasicOpen f) := by
    rw [← J.map_ideal_basicOpen V f]
    exact mem_map_of_mem _ ha
  have ha'' := (ideal_le_ideal_of_comap_io_le (B.affineBasicOpen f) $ comap_io_le_comap_io_of_le hfle $ h i) ha'
  rw [← K.map_ideal_basicOpen V f] at ha''
  exact exists_pow_smul_mem_of_map_mem V (K.ideal V) f a ha''

private theorem comap_inv_comap_hom {X Y : Sch} (e : X ≅ Y) (I : ISD Y) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← comap_comp, m114, comap_id]

theorem le_of_comap_le (ga_ : A ⟶ B)
    (hga_ : MaxContactFunctoriality.IsLocalIsomorphism ga_) [Surjective ga_]
    (J K : ISD B) (h : J.comap ga_ ≤ K.comap ga_) : J ≤ K := by
  refine le_of_forall_comap_io_le
    (fun p : { U : Opn A // IsOpenImmersion (opI U ≫ ga_) } => rangeOpens ga_ p.1 p.2) ?_ J K ?_
  intro b
  obtain ⟨U, hU, hb⟩ := exists_mem_rangeOpens ga_ hga_ b
  exact ⟨⟨U, hU⟩, hb⟩
  rintro ⟨W, hW⟩
  let _m0 := rangeOpens ga_ W hW
  show J.comap _m0.i ≤ K.comap _m0.i
  let _a0 := isoRangeOpens ga_ W hW
  have key : ∀ L : ISD B,
      (L.comap _m0.i).comap _a0.hom
        = (cmI L ga_).comap W.i := by
    intro L
    rw [← comap_comp, isoRangeOpens_hom_io,
      ← comap_comp]
  have h1 : (J.comap _m0.i).comap _a0.hom
      ≤ (K.comap _m0.i).comap _a0.hom := by
    rw [key J, key K]
    exact comap_mono W.i h
  have h2 : ((J.comap _m0.i).comap _a0.hom).comap
        _a0.inv
      ≤ ((K.comap _m0.i).comap _a0.hom).comap
        _a0.inv :=
    comap_mono _a0.inv h1
  rwa [comap_inv_comap_hom, comap_inv_comap_hom] at h2

private theorem smooth_of_smooth_iso_hom_comp {X Y Z : Sch} (e : X ≅ Y) (k : Y ⟶ Z)
    (hk : Smooth $ e.hom ≫ k) : Smooth k := by
  have h2 : Smooth $ isoI e ≫ isoH e ≫ k := inferInstance
  rwa [← assoc, e.inv_hom_id, id_comp] at h2

theorem smooth_of_smooth_comp_of_isLocalIsomorphism {S : Sch} (ga_ : A ⟶ B) (f : B ⟶ S)
    [IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0})]
    [Surjective ga_]
    (hga_ : MaxContactFunctoriality.IsLocalIsomorphism ga_)
    (h : Smooth (ga_ ≫ f)) : Smooth f := by
  choose U hU hmem using fun b => exists_mem_rangeOpens ga_ hga_ b
  have htop : (⨆ b : B, rangeOpens ga_ (U b) (hU b)) = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    exact mpr_ mem_iSup ⟨x, hmem x⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top _ htop ?_
  intro b
  refine smooth_of_smooth_iso_hom_comp (isoRangeOpens ga_ (U b) (hU b))
    (opI (rangeOpens ga_ (U b) (hU b)) ≫ f) ?_
  rw [isoRangeOpens_hom_io_assoc ga_ (U b) (hU b) f]
  infer_instance

theorem smooth_subschemeio_comp_of_smooth_comap_comp {S : Sch} (ga_ : A ⟶ B) (f : B ⟶ S)
    (Z : ISD B)
    [IsZariskiLocalAtSource $ @AlgebraicGeometry.Smooth.{0}]
    [Surjective ga_]
    (hga_ : MaxContactFunctoriality.IsLocalIsomorphism ga_)
    (h : Smooth $ subschemeι (Z.comap ga_) ≫ ga_ ≫ f) :
    Smooth $ subschemeι Z ≫ f := by
  have h1 := by
    refine smooth_of_smooth_iso_hom_comp (Z.comapIso ga_)
      (fst ga_ Z.si ≫ ga_ ≫ f) ?_
    rwa [← assoc, comapIso_hom_fst Z ga_]
  have h2 := h1
  rw [← assoc, condition, assoc] at h2
  refine smooth_of_smooth_comp_of_isLocalIsomorphism (snd ga_ Z.si) (siI Z ≫ f)
    ?_ h2
  let t := siI Z
  intro x
  let _a0 := fst ga_ t
  obtain ⟨V, hxV, hV⟩ := hga_ $ bsM _a0 x
  refine ⟨preU _a0 V, hxV, ?_⟩
  rw [← ((m226 _a0 V).paste_vert $ m186 ga_ t).isoPullback_hom_snd]
  infer_instance

section
variable {X Y : Sch}
section
variable {k : Type} [Field k] (q : Y ⟶ Sp k) (ga_ : X ⟶ Y) {V W : Opn X} (hWV : W ≤ V) (hW : IsOpenImmersion (W.i ≫ ga_)) {m : ℕ} (c : EtaleChart (ga_ ≫ q) V m)
noncomputable def etaleChartOnRangeOpens :
    EtaleChart q (rangeOpens ga_ W hW) m where
  map := (isoRangeOpens ga_ W hW).inv ≫ X.homOfLE hWV ≫ c.map
  comp_struct := by
    have h1 : (X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m = W.i ≫ ga_ ≫ q := by
      calc (X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m
          = X.homOfLE hWV ≫ c.map ≫ affineSpaceFinToSpec k m := assoc _ _ _
        _ = X.homOfLE hWV ≫ V.ι ≫ ga_ ≫ q := by rw [c.comp_struct]
        _ = (X.homOfLE hWV ≫ V.i) ≫ ga_ ≫ q := (assoc _ _ _).symm
        _ = W.ι ≫ ga_ ≫ q := by rw [Scheme.homOfLE_ι]
    calc ((isoRangeOpens ga_ W hW).inv ≫ X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m
        = (isoRangeOpens ga_ W hW).inv ≫ (X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m := by
          simp only [assoc]
      _ = (isoRangeOpens ga_ W hW).inv ≫ W.ι ≫ ga_ ≫ q := by rw [h1]
      _ = (rangeOpens ga_ W hW).i ≫ q := isoRangeOpens_inv_comp_assoc ga_ W hW q
  isEtale := by
    have : Etale c.map := c.isEtale
    have : IsOpenImmersion (isoRangeOpens ga_ W hW).inv := inferInstance
    infer_instance

theorem coordIdeal_etaleChartOnRangeOpens
    T :
    (etaleChartOnRangeOpens q ga_ hWV hW c).coordIdeal T
      = ((c.coordIdeal T).comap $ X.homOfLE hWV).comap (isoRangeOpens ga_ W hW).inv := by
  let _c0 := isoI (isoRangeOpens ga_ W hW) ≫ X.homOfLE hWV
  have e1 : ((c.coordIdeal T).comap $ X.homOfLE hWV).comap (isoRangeOpens ga_ W hW).inv
      = (c.coordIdeal T).comap _c0 := by
    rw [← comap_comp]
  let _a0 := coordSubspaceIdeal k m T
  have e2 : (c.coordIdeal T).comap _c0
      = _a0.comap
          (_c0 ≫ c.map) := by
    rw [coordIdeal_eq_comap_coordSubspaceIdeal, ← comap_comp]
  exact sy_ $ tr_ (tr_ e1 e2) $ congrArg _a0.comap $ assoc (isoRangeOpens ga_ W hW).inv (X.homOfLE hWV) c.map
end

theorem restrictIdeal_rangeOpens ga_ {V W : Opn X}
    (hWV : W ≤ V) (hW : IsOpenImmersion $ W.i ≫ ga_) (J : ISD Y) :
    restrictIdeal J (rangeOpens ga_ W hW)
      = ((restrictIdeal (J.comap ga_) V).comap $ X.homOfLE hWV).comap
          (isoRangeOpens ga_ W hW).inv := by
  let _a2 := isoRangeOpens ga_ W hW
  have hcomp : ((isoI (isoRangeOpens ga_ W hW) ≫ X.homOfLE hWV) ≫ opI V) ≫ ga_
      = opI (rangeOpens ga_ W hW) := by
    calc ((isoI (isoRangeOpens ga_ W hW) ≫ X.homOfLE hWV) ≫ opI V) ≫ ga_
        = isoI (isoRangeOpens ga_ W hW) ≫ (X.homOfLE hWV ≫ opI V) ≫ ga_ := by
          simp [assoc]
      _ = isoI (isoRangeOpens ga_ W hW) ≫ opI W ≫ ga_ := by rw [Scheme.homOfLE_ι]
      _ = opI (rangeOpens ga_ W hW) := isoRangeOpens_inv_comp ga_ W hW
  let _a3 := cmI (cmI J ga_) V.i
  have e1 : (cmI _a3 $ X.homOfLE hWV).comap _a2.inv
      = _a3.comap (isoI (isoRangeOpens ga_ W hW) ≫ X.homOfLE hWV) := by
    rw [← comap_comp]
  have e2 : _a3.comap (isoI (isoRangeOpens ga_ W hW) ≫ X.homOfLE hWV)
      = (cmI J ga_).comap ((isoI (isoRangeOpens ga_ W hW) ≫ X.homOfLE hWV) ≫ opI V) := by
    rw [← comap_comp]
  have e3 : (cmI J ga_).comap ((isoI (isoRangeOpens ga_ W hW) ≫ X.homOfLE hWV) ≫ opI V)
      = J.comap (((isoI (isoRangeOpens ga_ W hW) ≫ X.homOfLE hWV) ≫ opI V) ≫ ga_) := by
    rw [← comap_comp]
  have e4 : cmI J (((isoI (isoRangeOpens ga_ W hW) ≫ X.homOfLE hWV) ≫ opI V) ≫ ga_)
      = cmI J (rangeOpens ga_ W hW).i := by rw [hcomp]
  show cmI J (rangeOpens ga_ W hW).i
      = cmI (cmI _a3 $ X.homOfLE hWV) _a2.inv
  exact (tr_ (tr_ e1 e2) $ tr_ e3 e4).symm
end

section
variable {k : Type} [Field k]
theorem hasStrictNormalCrossingsWith_of_comap (p : B ⟶ Sp k)
    (ga_ : A ⟶ B) [Surjective ga_]
    (hga_ : MaxContactFunctoriality.IsLocalIsomorphism ga_)
    (Z : ISD B) (L : Bdy B)
    (h : HasStrictNormalCrossingsWith (ga_ ≫ p) (Z.comap ga_) $ L.map fun D => D.comap ga_) :
    HasStrictNormalCrossingsWith p Z L := by
  intro x hx
  obtain ⟨a, ha⟩ := surj (f := ga_) x
  have haZ : a ∈ spI (cmI Z ga_) := by
    rw [← one_le_orderAt_iff_mem_support]
    refine le_trans ?_ $ orderAt_le_orderAt_comap ga_ Z a
    rw [ha]
    exact mpr_ (one_le_orderAt_iff_mem_support Z x) hx
  obtain ⟨V, haV, m, c, af, S, hinj, hnone, hsome, hZV⟩ := h a haZ
  obtain ⟨U0, haU0, hU0⟩ := hga_ a
  have hWV : V ⊓ U0 ≤ V := inf_le_left
  have hWio : opI (V ⊓ U0) ≫ ga_ = A.homOfLE inf_le_right ≫ opI U0 ≫ ga_ := by simp_all
  have hW : IsOpenImmersion $ opI (V ⊓ U0) ≫ ga_ := by
    rw [hWio]
    infer_instance
  have hmem : a ∈ range (V ⊓ U0).ib := by
    rw [q1]
    exact ⟨haV, haU0⟩
  obtain ⟨w, hw⟩ := hmem
  have hxP : x ∈ rangeOpens ga_ (V ⊓ U0) hW := by
    refine mpr_ (mem_rangeOpens_iff ga_ (V ⊓ U0) hW x) ⟨w, ?_⟩
    have hc : bsM (opI (V ⊓ U0) ≫ ga_) w = bsM ga_ (opIb (V ⊓ U0) w) := by simp
    rw [hc, hw, ha]
  have hlen : (L.map (·.comap ga_)).length = lenL L := by simp
  refine ⟨rangeOpens ga_ (V ⊓ U0) hW, hxP, m, etaleChartOnRangeOpens p ga_ hWV hW c, af, S,
    ?_, ?_, ?_, ?_⟩
  intro i hi j hj t hti htj
  exact hinj i (by rw [hlen]; exact hi) j (by rw [hlen]; exact hj) t hti htj
  intro i hi hni
  have hi' : i < (L.map (·.comap ga_)).length := by rw [hlen]
                                                    exact hi
  have h2 : (L.map (·.comap ga_))[i]'hi' = cmI (L[i]'hi) ga_ := by simp
  have h1 := hnone i hi' hni
  rw [h2] at h1
  rw [restrictIdeal_rangeOpens ga_ hWV hW $ L[i]'hi, h1, comap_top,
    comap_top]
  intro i hi t hti
  have hi' : i < (L.map (·.comap ga_)).length := by rw [hlen]
                                                    exact hi
  have h2 : (L.map (·.comap ga_))[i]'hi' = cmI (L[i]'hi) ga_ := by simp
  have h1 := hsome i hi' t hti
  rw [h2] at h1
  rw [restrictIdeal_rangeOpens ga_ hWV hW $ L[i]'hi, h1, coordIdeal_etaleChartOnRangeOpens]
  rw [restrictIdeal_rangeOpens ga_ hWV hW Z, hZV, coordIdeal_etaleChartOnRangeOpens]

theorem smooth_markedBlowupSequenceData_projectionToBase_comp {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
    {E : Bdy X} [Smooth p]
    (t : MarkedBlowupSequenceData p I m E) :
    ∀ i : ℕ, i ≤ t.length → Smooth (t.proj i ≫ p) := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [t.proj_zero]
      infer_instance
  | succ j ih =>
      intro hi
      have hj := hi
      have := ih $ le_of_lt hj
      rw [t.proj_succ j, assoc]
      exact smooth_comp_of_isBlowupAlongIdealSheaf (t.center_snc j hj) $ t.isBlowup j hj

theorem strictPullbackComparisonMap_comp_projectionToBase {X X' : Sch}
    {q : X' ⟶ Sp k} {g : X' ⟶ X} {I : ISD X} {m : ℕ}
    {E : Bdy X} {d : BlowupSequenceData X}
    (t : MarkedBlowupSequenceData q (I.comap g) m $ E.map fun A => A.comap g)
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups) :
    ∀ i hi, t.strictPullbackComparisonMap D i hi ≫ d.projectionToBase i = t.proj i ≫ g := by
  intro i
  induction i with
  | zero =>
      intro hi
      rw [p23, t.proj_zero]
      exact t.strictPullbackComparisonMap_zero D
  | succ j ih =>
      intro hi
      have hj := hi
      let _a0 := t.strictPullbackComparisonMap D (j + 1) hi
      calc _a0 ≫ d.projectionToBase (j + 1)
          = _a0 ≫ d.map j ≫ d.projectionToBase j := by rw [p43]
        _ = (_a0 ≫ d.map j) ≫ d.projectionToBase j := sy_ $ assoc _ _ _
        _ = (t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj)) ≫ d.projectionToBase j := by rw [t.strictPullbackComparisonMap_comp_blowupMorphism D j hj]
        _ = t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj) ≫ d.projectionToBase j := assoc _ _ _
        _ = t.map j ≫ t.proj j ≫ g := by rw [ih $ le_of_lt hj]
        _ = (t.map j ≫ t.proj j) ≫ g := sy_ $ assoc _ _ _
        _ = t.proj (j + 1) ≫ g := by rw [t.proj_succ j]

section
variable [CharZero k] {X X' : Sch}
section
variable {p : X ⟶ Sp k} {g : X' ⟶ X} [Smooth p] [Smooth g] [Flat g] [Surjective g] {I : ISD X} {m : ℕ} {E : Bdy X} {d : BlowupSequenceData X} (t : MarkedBlowupSequenceData (g ≫ p) (I.comap g) m (E.map fun A => A.comap g)) (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
theorem controlledTransform_le_center_pow
    (hcomp : ∀ i hi,
      MaxContactFunctoriality.IsLocalIsomorphism $ D.comp i $ t.le_toSequenceOfBlowups_length hi)
    (i : ℕ) (hi : i < t.length)
    (hmt : t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i $ le_of_lt hi)) :
    d.controlledTransform I m i ≤ d.center i ^ m := by
  let _c0 := t.strictPullbackComparisonMap D i $ le_of_lt hi
  have := smooth_markedBlowupSequenceData_projectionToBase_comp t i $ le_of_lt hi
  have :=
    t.surjective_strictPullbackComparisonMap D i $ le_of_lt hi
  refine le_of_comap_le _c0 (hcomp i $ le_of_lt hi) _ _ ?_
  calc (d.controlledTransform I m i).comap _c0
      = t.ideal i := sy_ hmt
    _ ≤ t.center i ^ m := le_pow_of_hasStrictNormalCrossingsWith (t.proj i ≫ g ≫ p) (t.center i) (t.ideal i) (t.boundary i) (t.center_snc i hi) m $ t.center_order i hi
    _ = ((d.center i).comap _c0) ^ m := by rw [(t.center_eq_comap_strictPullbackComparisonMap D i hi).symm]
    _ = cmI (d.center i ^ m) _c0 :=
        (comap_pow (d.center i) _c0 m).symm

private theorem ideal_eq_comap_controlledTransform
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian $ d.obj i)
    (hcomp : ∀ i hi,
      MaxContactFunctoriality.IsLocalIsomorphism $ D.comp i $ t.le_toSequenceOfBlowups_length hi) :
    ∀ i hi,
      t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i hi) := by
  intro i
  induction i with
  | zero =>
      intro hi
      let _a4 := t.strictPullbackComparisonMap D 0 hi
      calc t.ideal 0 = (I.comap g).comap t.isoZero.hom := t.ideal_zero
        _ = I.comap (t.isoZero.hom ≫ g) := by rw [← comap_comp]
        _ = I.comap (_a4 ≫ bdIzH d) := by rw [t.strictPullbackComparisonMap_zero D]
        _ = (I.comap $ bdIzH d).comap _a4 := by
              rw [comap_comp]
        _ = (d.controlledTransform I m 0).comap _a4 := by rw [controlledTransform_zero]
  | succ j ih =>
      intro hi
      have hj := hi
      have hmj :=
        ih $ le_of_lt hj
      have hjd : j < d.length := by rw [← t.length_eq_of_strictPullbackBlowupSeq D]
                                    exact hj
      have := hNd (j + 1) hjd
      let _a3 := d.controlledTransform I m j
      obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map j) (d.center j)
        _a3 m (d.isBlowup j hjd) $ controlledTransform_le_center_pow t D hcomp j hj hmj
      refine eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul
        (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal $ t.isBlowup j hj) m ?_
      let _a5 := t.strictPullbackComparisonMap D j $ le_of_lt hj
      calc p5 (t.map j) (t.center j) ^ m * t.ideal (j + 1)
          = (t.ideal j).comap (t.map j) := t.ideal_succ j hj
        _ = (_a3.comap _a5).comap (t.map j) := by
            rw [hmj]
        _ = _a3.comap (t.map j ≫ _a5) := by
            rw [← comap_comp]
        _ = _a3.comap (t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j) := by rw [t.strictPullbackComparisonMap_comp_blowupMorphism D j hj]
        _ = (_a3.comap $ d.map j).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
            rw [comap_comp]
        _ = (p5 (d.map j) (d.center j) ^ m *
              d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by rw [d.pow_exceptionalIdeal_mul_controlledTransform_succ I m j ⟨B, hB⟩]
        _ = (p5 (d.map j) (d.center j) ^ m).comap (t.strictPullbackComparisonMap D (j + 1) hi) *
              (d.controlledTransform I m $ j + 1).comap (t.strictPullbackComparisonMap D (j + 1) hi) :=
            comap_mul _ _ _
        _ = ((p5 (d.map j) $ d.center j).comap $ t.strictPullbackComparisonMap D (j + 1) hi) ^ m *
              (d.controlledTransform I m $ j + 1).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
            rw [comap_pow]
        _ = exceptionalIdeal (t.map j) (t.center j) ^ m *
              (d.controlledTransform I m $ j + 1).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by rw [t.exceptionalIdeal_eq_comap_strictPullbackComparisonMap D j hj]
end

theorem isMarked_of_strictPullbackBlowupSeq (p : X ⟶ Sp k) (g : X' ⟶ X)
    [Smooth p] [Smooth g]
    [Flat g] [Surjective g]
    [IsZariskiLocalAtSource $ @AlgebraicGeometry.Smooth.{0}]
    (I : ISD X) (m : ℕ) (E : Bdy X) (d : BlowupSequenceData X)
    (t : MarkedBlowupSequenceData (g ≫ p) (I.comap g) m $ E.map fun A => A.comap g)
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian $ d.obj i)
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian $ t.obj i)
    (hcomp : ∀ i hi,
      MaxContactFunctoriality.IsLocalIsomorphism $ D.comp i $ t.le_toSequenceOfBlowups_length hi) :
    d.IsMarked p I m E := by
  have hlen := t.length_eq_of_strictPullbackBlowupSeq D
  have hle : ∀ i, i < t.length → d.controlledTransform I m i ≤ d.center i ^ m := by
    intro i hi
    exact controlledTransform_le_center_pow t D hcomp i hi $ (ideal_eq_comap_controlledTransform t D hNd hcomp) i $ le_of_lt hi
  refine ⟨?_, ?_, ?_, ?_⟩
  intro i hid
  have hi : i < t.length := by rw [hlen]
                               exact hid
  have := hNd (i + 1) hid
  obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map i) (d.center i)
    (d.controlledTransform I m i) m (d.isBlowup i hid) $ hle i hi
  exact ⟨B, hB⟩
  intro i hid
  have hi : i < t.length := by rw [hlen]
                               exact hid
  exact support_subset_orderAtLeastLocus_of_le_pow (d.center i) (d.controlledTransform I m i) m $ hle i hi
  intro i hid
  have hi : i < t.length := by rw [hlen]
                               exact hid
  have :=
    t.surjective_strictPullbackComparisonMap D i $ le_of_lt hi
  refine smooth_subschemeio_comp_of_smooth_comap_comp (t.strictPullbackComparisonMap D i $ le_of_lt hi) (d.projectionToBase i ≫ p) (d.center i)
    (hcomp i $ le_of_lt hi) ?_
  have hpr : t.strictPullbackComparisonMap D i (le_of_lt hi) ≫ d.projectionToBase i ≫ p = t.proj i ≫ g ≫ p := by
    rw [← assoc, strictPullbackComparisonMap_comp_projectionToBase t D i $ le_of_lt hi, assoc]
  rw [(t.center_eq_comap_strictPullbackComparisonMap D i hi).symm, hpr]
  exact t.center_smooth i hi
  intro i hid
  have hi : i < t.length := by rw [hlen]
                               exact hid
  have :=
    t.surjective_strictPullbackComparisonMap D i $ le_of_lt hi
  refine hasStrictNormalCrossingsWith_of_comap (d.projectionToBase i ≫ p) (t.strictPullbackComparisonMap D i $ le_of_lt hi)
    (hcomp i $ le_of_lt hi) (d.center i) (d.boundaryFrom E i) ?_
  rw [(t.center_eq_comap_strictPullbackComparisonMap D i hi).symm, (t.boundary_eq_comap_strictPullbackComparisonMap D hNd hNt i $ le_of_lt hi).symm, ← assoc, strictPullbackComparisonMap_comp_projectionToBase t D i $ le_of_lt hi, assoc]
  exact t.center_snc i hi
end
end

theorem isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq (hinv : ComapIsoInvariance) (P : ℕ → Prop)
    (Afam : ℕ → PrincipalizationAssignment) (T : MarkedIdealWithBoundary)
    (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    [CharZero T.base]
    [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap]
    [Smooth $ coverMap T h.valid]
    [Surjective $ coverMap T h.valid]
    [IsZariskiLocalAtSource $ @AlgebraicGeometry.Smooth.{0}]
    (_hoi : MaxContactFunctoriality.IsLocalIsomorphism $ coverMap T h.valid)
    (_hmult : 1 ≤ tunedMult T)
    (d : BlowupSequenceData T.scheme)
    (hpb : IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian $ d.obj i)
    (hNt : ∀ i ≤ (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).length,
      IsLocallyNoetherian $ (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).obj i)
    (hcomp : ∀ D : StrictPullbackBlowupSeq (coverMap T h.valid)
        (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups,
      ∀ i (hi : i ≤ (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).length),
        MaxContactFunctoriality.IsLocalIsomorphism
          (D.comp i $ (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).le_toSequenceOfBlowups_length hi)) :
    d.IsMarked T.structMap (balancedTunedIdeal T h.valid)
      (tunedMult T) T.boundary := by
  let _a0 := coverMap T h.valid
  have : Flat _a0 := inferInstance
  have D :=
    hpb.toStrictPullbackBlowupSeq
  exact isMarked_of_strictPullbackBlowupSeq T.structMap _a0
    (balancedTunedIdeal T h.valid) (tunedMult T) T.boundary d
    (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid) D hNd hNt $ hcomp D

end FunctorialResolution.EmbeddedResolution
end
section

namespace FunctorialResolution.EmbeddedResolution

theorem orderAtLeastLocus_eq_empty_of_comap_eq_empty {A B : Sch} (f : A ⟶ B)
    [Surjective f] (J : ISD B) mu_
    (h : orderAtLeastLocus (J.comap f) mu_ = ∅) : orderAtLeastLocus J mu_ = ∅ := by
  ext x
  simp [mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, rfl⟩ := f.surjective x
  have hmem : y ∈ orderAtLeastLocus (cmI J f) mu_ := by
    rw [mem_orderAtLeastLocus_iff]
    exact le_trans (mp_ (mem_orderAtLeastLocus_iff J mu_ $ bsM f y) hx)
      (orderAt_le_orderAt_comap f J y)
  rw [h] at hmem
  simp at hmem

namespace MaxContactFunctoriality

theorem OrderReductionHypotheses.dropTrivialBoundary {P} {T} (h : OrderReductionHypotheses P T)
    {hinv : ComapIsoInvariance} {A} {B}
    (hd : DescentHypotheses hinv P A B) : OrderReductionHypotheses P $ MaxContactReduction.dropTrivialBoundary T := by
  refine ⟨?_, ?_, h.coSupport_nonempty, hd.valid_trim T h.valid⟩
  have hdim := h.dim_prop
  rwa [← dropTrivialBoundary_dim T] at hdim
  intro x
  exact h.orderLE x

section

variable (hinv : ComapIsoInvariance) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment)
  (B : PrincipalizationAssignment)

section
variable (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary)
include hd
theorem isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq (h : OrderReductionHypotheses P T)
    (d : BlowupSequenceData T.scheme) :
    (d.IsMarked T.structMap T.ideal T.mult T.boundary ↔
      d.IsMarked T.structMap (balancedTunedIdeal T h.valid)
        (tunedMult T) T.boundary) ∧
    (d.IsMarked T.structMap T.ideal T.mult T.boundary →
      ∀ i ≤ d.length,
        orderAtLeastLocus (d.controlledTransform (balancedTunedIdeal T h.valid)
            (tunedMult T) i) (tunedMult T) =
          orderAtLeastLocus (d.controlledTransform T.ideal T.mult i) T.mult) := by
  have := h.valid.charZero
  have := h.valid.smooth
  have := h.valid.locallyOfFiniteType
  have h2 := hd.tuning
  unfold IsMarkedIffBalancedTunedSheaf at h2
  have key := h2 T.base T.scheme T.structMap T.ideal T.mult h.valid.one_le_mult
    ⟨mpr_ (orderLE_iff T.ideal T.mult) h.orderLE, h.coSupport_nonempty⟩ T.boundary d
  exact ⟨an1 key, key.2.1⟩

end

section
variable (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary)
include hstar hd
theorem exists_blowupSequenceData_isStrictPullback_cover (h : OrderReductionHypotheses P T) :
    ∃ (d : BlowupSequenceData T.scheme)
      (hm : d.IsMarked T.structMap T.ideal T.mult T.boundary),
      IsStrictPullbackBlowupSeq
          (coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
          (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
            (lowerDimensionalFamily A $ MaxContactReduction.dropTrivialBoundary T)).toBlowupSequenceData.toSequenceOfBlowups
          d.toSequenceOfBlowups ∧
        maxContactPrincipalization hinv A T =
          (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm).toMarkedSequenceOfBlowups := by
  obtain ⟨d0, hpb0⟩ := hstar.descends (p11 T) $ h.dropTrivialBoundary hd
  obtain ⟨d, hdesc⟩ :
      ∃ e : BlowupSequenceData (p11 T).scheme,
        descendStrictPullback (p11 T)
            (coverTriple (p11 T) (h.dropTrivialBoundary hd).valid)
            (coverMap (p11 T) (h.dropTrivialBoundary hd).valid)
            (coverMarkedBlowupData (p11 T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A $ p11 T)) = some e :=
    exists_descendStrictPullback_eq_some _ _ ⟨d0, hpb0⟩
  have hpb :=
    isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some _ _ hdesc
  have hm :=
    hd.isMarked_of_trim T h.valid d T.ideal T.mult $ (an1 $ isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (p11 T) (h.dropTrivialBoundary hd) d).mpr $ hd.isMarked (p11 T) (h.dropTrivialBoundary hd) d hpb
  exact ⟨d, hm, hpb, reduceOrder_eq_toMarkedSequence hinv T (lowerDimensionalFamily A T) h.valid h.orderAtLeastLocus_ne_empty (h.dropTrivialBoundary hd).valid d hdesc hm⟩

end

theorem length_eq_zero_of_orderAtLeastLocus_eq_empty (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) (_hdim : P T.krullDimSucc)
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    (hemp : orderAtLeastLocus T.ideal T.mult = ∅) :
    (maxContactPrincipalization hinv A T).length = 0 := by
  rw [maxContactPrincipalization_apply, reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp, emptyMarkedSeq_length]

theorem orderAtLeastLocus_controlledTransform_eq_empty_of_flat_surjective {k : Type} [Field k] {X' X : Sch}
    {q : X' ⟶ Sp k} {g : X' ⟶ X}
    (hflat : Flat g) (hsurj : Surjective g)
    {I : ISD X} {m : ℕ} {E : Bdy X} {d : BlowupSequenceData X}
    (t : MarkedBlowupSequenceData q (I.comap g) m $ List.map (fun Z => Z.comap g) E)
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hdiv : ∀ i < d.length, ∃ Bb,
      exceptionalIdeal (d.map i) (d.center i) ^ m * Bb = (d.controlledTransform I m i).comap (d.map i))
    (hres : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus (d.controlledTransform I m d.length) m = ∅ := by
  have :=
    MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap t D t.length le_rfl
  have h0 := hres
  rw [MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform t D hdiv t.length le_rfl] at h0
  have h1 := orderAtLeastLocus_eq_empty_of_comap_eq_empty (t.strictPullbackComparisonMap D t.length le_rfl)
    (d.controlledTransform I m t.length) m h0
  rwa [MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq t D] at h1

end

end MaxContactFunctoriality


section
variable {k : Type} [Field k]
theorem orderCertificate_congr_mult {W : Sch}
    {p : W ⟶ Sp k} {N : ISD W} {mu_ mu' : ℕ}
    {Mem : Set ↥W} {Z : ISD W} (h : mu_ = mu')
    (c : OrderCertificate W p N mu_ Mem Z) : OrderCertificate W p N mu' Mem Z := by
  subst h
  exact c

theorem orderCertificate_congr_map {W : Sch}
    {p p' : W ⟶ Sp k} {N : ISD W} {mu_ : ℕ}
    {Mem : Set ↥W} {Z : ISD W} (h : p = p')
    (c : OrderCertificate W p N mu_ Mem Z) : OrderCertificate W p' N mu_ Mem Z := by
  subst h
  exact c

theorem boundaryLocus_eq_iUnion_support {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
    {E : Bdy X} (s : MarkedSequenceOfBlowups p I m E) (t : ℕ) :
    boundaryLocus s t
      = ⋃ D ∈ s.boundary t, (↑D.support : CSet $ s.schemeAt t) := by
  ext x
  rw [mem_boundaryLocus_iff]
  constructor
  simp_all
  simp_all

section
variable {X' X : Sch} {q : X' ⟶ Sp k} {g} {I : ISD X} {m : ℕ} {E : Bdy X} {d : BlowupSequenceData X} (hf : Flat g)
include hf
theorem boundary_eq_map_comap_strictPullbackComparisonMap_of_flat
    (s : MarkedBlowupSequenceData q (I.comap g) m $ List.map (fun A => A.comap g) E)
    D
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian $ d.obj i)
    (hNt : ∀ i ≤ s.length, IsLocallyNoetherian $ s.obj i)
    i (hi : i ≤ s.length) :
    s.boundary i = List.map (fun A => A.comap $ s.strictPullbackComparisonMap D i hi) (d.boundaryFrom E i) := by
  exact MarkedBlowupSequenceData.boundary_eq_comap_strictPullbackComparisonMap s D hNd hNt i hi

theorem surjective_strictPullbackComparisonMap_of_flat_of_surjective (hs : Surjective g)
    (s : MarkedBlowupSequenceData q (I.comap g) m $ List.map (fun A => A.comap g) E)
    (D : StrictPullbackBlowupSeq g s.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ s.length) :
    Surjective $ s.strictPullbackComparisonMap D i hi := by
  exact MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap s D i hi
end
end

theorem iUnion_support_comap_eq_preimage {X Y : Sch} f
    (l : Bdy Y) :
    (⋃ J ∈ l.map fun D => D.comap f, (↑J.support : Set ↥X)) =
      (⇑f) ⁻¹' (⋃ J ∈ l, (↑J.support : Set ↥Y)) :=by simp_all
namespace MaxContactFunctoriality

theorem mem_boundary_of_forall_mem {X} (d : BlowupSequenceData X)
    E E' (hEE : ∀ D ∈ E, D ∈ E') :
    ∀ t (D : IdealSheafData $ d.obj t), D ∈ d.boundaryFrom E t → D ∈ d.boundaryFrom E' t := by
  intro t
  induction t with
  | zero =>
      intro D hD
      rw [boundary_zero] at hD ⊢
      obtain ⟨A, hA, rfl⟩ := mem_map.1 hD
      exact mem_map.2 ⟨A, hEE A hA, rfl⟩
  | succ t ih =>
      intro D hD
      rw [p52] at hD ⊢
      rcases mem_append.1 hD with hmem | hmem
      obtain ⟨A, hA, rfl⟩ := mem_map.1 hmem
      exact mem_append.2 $ inl $ mem_map.2 ⟨A, ih A hA, rfl⟩
      exact mem_append.2 $ inr hmem

theorem mem_boundary_of_mem_boundary_dropTrivialBoundary (T : MarkedIdealWithBoundary) (d : BlowupSequenceData T.scheme) t
    D
    (hD : D ∈ d.boundaryFrom (MaxContactReduction.dropTrivialBoundary T).boundary t) :
    D ∈ d.boundaryFrom T.boundary t := by
  refine mem_boundary_of_forall_mem d _ _ ?_ t D hD
  intro A hA
  rw [dropTrivialBoundary_boundary] at hA
  exact (mem_filter.1 hA).1

section

variable (hinv : ComapIsoInvariance) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment)
  (B : PrincipalizationAssignment)

section
variable (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary)
include hstar hd
theorem orderCertificate_of_isStrictPullbackBlowupSeq (h : OrderReductionHypotheses P T) (hone : T.mult = 1)
    (d : BlowupSequenceData T.scheme)
    (hmk : d.IsMarked T.structMap T.ideal T.mult T.boundary)
    (hpb : IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).toSequenceOfBlowups d.toSequenceOfBlowups)
    (t : ℕ) (ht : t < d.length) :
    OrderCertificate ((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.schemeAt t)
      (projectionToSpec
        (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t)
      ((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.ideal t)
      T.mult
      (boundaryLocus
        (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t)
      ((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.center t) := by
  classical
  have hflat := hd.flat_coverMap T h
  have htun :=
    hd.tunedIdeal_of_mult_one T h.valid hone
  have hmul : tunedMult T = T.mult := by
    show tuningExponent T.mult = T.mult
    rw [hone]
    exact tuningExponent_one
  have hstrictPullback := hpb.toStrictPullbackBlowupSeq
  have hlen :=
    MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq _ hstrictPullback
  have htu : t ≤ (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).length := by omega
  have htlt : t < (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).length := by omega
  have hN := hd.locallyNoetherian T h d hpb
  have hdiv := hmk.1
  rw [← hmul, ← htun] at hdiv
  have hid := MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform
    (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T) hstrictPullback hdiv t htu
  have hctr := MarkedBlowupSequenceData.center_eq_comap_strictPullbackComparisonMap
    (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T) hstrictPullback t htlt
  have hbd := boundary_eq_map_comap_strictPullbackComparisonMap_of_flat hflat
    (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T) hstrictPullback hN.1 hN.2 t htu
  have hstr := isPullback_projectionToBase_of_isPullback_blowupMorphism (coverMap T h.valid)
    (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups
    (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length
    (fun i hi => hstrictPullback.comp i hi) hstrictPullback.comp_zero (fun i hi => hstrictPullback.pullback i hi) t
    (MarkedBlowupSequenceData.le_toSequenceOfBlowups_length _ htu)
  have hw := hstr.w.symm
  rw [p36] at hw
  have e1 :=
    (congrArg (fun ph_ =>
        (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).toMarkedSequenceOfBlowups.projectionToBase t ≫ ph_)
        (coverTriple_structureMorphism T h.valid)).trans
      (tr_ (sy_ $ assoc _ _ _)
        (tr_ (congrArg (fun ph_ => ph_ ≫ T.structMap) hw) $ assoc _ _ _))
  have hci : d.controlledTransform (balancedTunedIdeal T h.valid)
      (cT h.valid).mult t = d.controlledTransform T.ideal T.mult t := by simp_all
  let _a1 := d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk
  have e2 : (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).toMarkedSequenceOfBlowups.ideal t =
      ((_a1.toMarkedSequenceOfBlowups.ideal t).comap
        ((coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).strictPullbackComparisonMap hstrictPullback t htu)) := by
    simp only [toMarkedSequence_ideal]
    exact tr_ hid $ congrArg (fun J => J.comap
      ((coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).strictPullbackComparisonMap hstrictPullback t htu)) hci
  have e3 : (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).toMarkedSequenceOfBlowups.center t =
      ((_a1.toMarkedSequenceOfBlowups.center t).comap
        ((coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).strictPullbackComparisonMap hstrictPullback t htu)) := by
    simp only [toMarkedSequence_center]
    exact hctr
  have e4 : boundaryLocus
      (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).toMarkedSequenceOfBlowups t =
      ((coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).strictPullbackComparisonMap hstrictPullback t htu) ⁻¹'
        boundaryLocus
          _a1.toMarkedSequenceOfBlowups t := by
    simp only [boundaryLocus_eq_iUnion_support, toMarkedSequence_boundary,
      toMarkedBlowupSequenceData_boundary]
    rw [hbd]
    exact iUnion_support_comap_eq_preimage _ _
  have hp : projectionToSpec
      _a1.toMarkedSequenceOfBlowups t
      = d.projectionToBase t ≫ T.structMap := by
    simp only [projectionToSpec_eq, toMarkedSequence_projectionToBase,
      toMarkedBlowupSequenceData_projectionToBase]
    rfl
  refine orderCertificate_congr_map hp.symm ?_
  refine hd.cert_descend T.base
      ((coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).obj t) _ _
      ((coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).strictPullbackComparisonMap hstrictPullback t htu) (hd.comp_openImmersion T h d hstrictPullback t htu) ?_
      _ _ _ _ ?_
  exact surjective_strictPullbackComparisonMap_of_flat_of_surjective hflat (hd.surjective_coverMap T h)
    (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T) hstrictPullback t htu
  have hc :=
    hstar.cert T h hone t htlt
  rw [e1, e2, e3, e4] at hc
  exact orderCertificate_congr_mult hone.symm hc

end

end

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {A B C : Sch}

section
variable (ga_ : A ⟶ B) (W : Opn A) (h : IsOpenImmersion (W.i ≫ ga_))
theorem comap_isoRangeOpens_inv
    (J : ISD B) :
    ((J.comap ga_).comap W.i).comap (isoRangeOpens ga_ W h).inv = J.comap (rangeOpens ga_ W h).i := by
  simp [← isoRangeOpens_inv_comp ga_ W h]

theorem preimage_isoRangeOpens_inv
    S :
    (isoRangeOpens ga_ W h).inv.base ⁻¹' (W.ι.base ⁻¹' (ga_.base ⁻¹' S))
      = (rangeOpens ga_ W h).ι.base ⁻¹' S := by
  ext x
  simp [← isoRangeOpens_inv_comp ga_ W h]

end

def OrderCertificateLocalToGlobal : Prop :=
  ∀ (k : Type) [Field k] (W : Sch) (p : W ⟶ Sp k)
    (N : ISD W) (mu_ : ℕ) (Mem : Set ↥W) (Z : ISD W),
    (∀ x : ↥W, ∃ V : Opn W, x ∈ V ∧
      OrderCertificate V.toScheme (V.i ≫ p) (N.comap V.i) mu_ (V.ib ⁻¹' Mem) (Z.comap V.i)) →
    OrderCertificate W p N mu_ Mem Z

section
variable (hopen : ∀ (k : Type) [Field k], OpenImmersionStability k)
include hopen
theorem exists_opens_orderCertificate_of_isLocalIsomorphism
    {k : Type} [Field k] {W W' : Sch} (p : W ⟶ Sp k)
    (g : W' ⟶ W) (hg : MaxContactFunctoriality.IsLocalIsomorphism g)
    [Surjective g]
    (N : ISD W) (mu_ : ℕ) (Mem : Set ↥W) (Z : ISD W)
    (hcert : OrderCertificate W' (g ≫ p) (N.comap g) mu_ (g.base ⁻¹' Mem) $ Z.comap g)
    (x : ↥W) :
    ∃ V : Opn W, x ∈ V ∧
      OrderCertificate V.toScheme (V.i ≫ p) (N.comap V.i) mu_ (V.ib ⁻¹' Mem) (Z.comap V.i) := by
  obtain ⟨U, hU, hxU⟩ := exists_mem_rangeOpens g hg x
  refine ⟨rangeOpens g U hU, hxU, ?_⟩
  have htr := OrderCertificate.comap_iso_of_eq_iso_hom_comp (isoRangeOpens g U hU).symm
    (sy_ $ isoRangeOpens_inv_comp_assoc g U hU p) $ hcert.restrict (hopen k) U
  simp [Iso.symm_hom, comap_isoRangeOpens_inv, preimage_isoRangeOpens_inv] at htr
  exact htr

theorem orderCertificate_of_comap_of_isLocalIsomorphism
    (hglue : OrderCertificateLocalToGlobal)
    (k : Type) [Field k] (W W' : Sch) (p : W ⟶ Sp k)
    (g : W' ⟶ W) (hg : MaxContactFunctoriality.IsLocalIsomorphism g)
    [Surjective g]
    (N : ISD W) (mu_ : ℕ) (Mem : Set ↥W) (Z : ISD W)
    (hcert : OrderCertificate W' (g ≫ p) (N.comap g) mu_ (g.base ⁻¹' Mem) $ Z.comap g) :
    OrderCertificate W p N mu_ Mem Z :=
  hglue k W p N mu_ Mem Z
    (fun x => exists_opens_orderCertificate_of_isLocalIsomorphism hopen p g hg N mu_ Mem Z hcert x)
end

end FunctorialResolution.EmbeddedResolution
end
section

namespace FunctorialResolution.EmbeddedResolution

theorem coe_support_eq_range_subschemeio {X : Sch} (I : ISD X) :
    (↑I.support : Set ↥X) = range (⇑I.subschemeι.base) := by
  simp

theorem eq_top_of_imageIdealSheaf_eq_top {S X : Sch} (σ : S ⟶ X) (J : ISD S)
    (h : imageIdealSheaf σ J = ⊤) : J = ⊤ := by
  have hker := h
  rw [imageIdealSheaf_eq_ker] at hker
  let _a0 := siI J ≫ σ
  have hle : (⊤ : ISD X).subschemeι.ker ≤ _a0.ker :=
    le_of_eq $ by rw [ker_subschemeι, hker]
  have hZ : IsEmpty J.subscheme := by
    refine ⟨fun z => ?_⟩
    have _i33 : IsEmpty $ subS (⊤ : ISD X) := by
      have h2 :=
        (eq_top_iff_support_eq_empty (⊤ : ISD X)).mp rfl
      rw [coe_support_eq_range_subschemeio] at h2
      exact mp_ range_eq_empty_iff h2
    exact _i33.elim
      (bsM (lift (⊤ : ISD X).si _a0 hle) z)
  rw [eq_top_iff_support_eq_empty, coe_support_eq_range_subschemeio,
    range_eq_empty_iff]
  exact hZ

theorem isBalanced_of_mult_eq_one (T : MarkedIdealWithBoundary)
    (hft : LocallyOfFiniteType T.structMap) (h : mult T = 1) :
    T.IsBalanced hft := by
  unfold IsBalanced
  simp [h]
  apply isDerivBalanced_one

private theorem toSequenceOfBlowups_heq_of_eq {S1_ S2_ : MarkedIdealWithBoundary} (h : S1_ = S2_)
    (L : PrincipalizationAssignment) : HEq (L S1_).toSequenceOfBlowups (L S2_).toSequenceOfBlowups := by
  cases h
  rfl

namespace MaxContactFunctoriality

end MaxContactFunctoriality


namespace MaxContactFunctoriality

theorem isOrderReduction_maxContact_of_descentHypotheses
    (hinv : ComapIsoInvariance) (P Q : ℕ → Prop) (A : ℕ → PrincipalizationAssignment)
    (L L' : PrincipalizationAssignment)
    (hdimlink : ∀ a b : ℕ, a < b → P b → Q a)
    (hlow : IsMaxOrderReduction Q L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) L)
    (hstar : CoverSequenceProperties hinv P A)
    (hdes : DescentHypotheses hinv P A L) :
    IsOrderReduction P (maxContactPrincipalization hinv A) L := by
  refine
    { cert := ?_, base_change := ?_, base_change_strict := ?_, pushforward := ?_,
      order_le := ?_, center_nonempty := ?_, resolves := ?_, smooth_pullback := ?_,
      smooth_pullback_strict := ?_, trivial_of_coSupport_empty := ?_ }
  intro T hv hdim hO i hi
  let B := L
  let hord := mp_ (isOrderBoundedByMult_iff T) hO
  classical
  rcases m63 T.mult 2 with hm2 | hm2
  have hone := le_antisymm (by omega) hv.one_le_mult
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  have h0 := length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hdim hord hemp
  omega
  have hyp : OrderReductionHypotheses P T := ⟨hdim, hord, nonempty_iff_ne_empty.2 hemp, hv⟩
  obtain ⟨d, hm', hpb', heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hdes T hyp
  have honeT : (p11 T).mult = 1 := by simp_all
  have htrim := hyp.dropTrivialBoundary hdes
  have hmk0 := hdes.isMarked (p11 T) htrim d hpb'
  have htun :=
    hdes.tunedIdeal_of_mult_one (p11 T) htrim.valid honeT
  have hmul : tunedMult (p11 T)
      = (p11 T).mult := by
    show tuningExponent (p11 T).mult = (p11 T).mult
    rw [honeT]
    exact tuningExponent_one
  rw [htun, hmul] at hmk0
  have htlen : i < d.length := by simp_all
  have hcert := orderCertificate_of_isStrictPullbackBlowupSeq hinv P A B hstar hdes (p11 T) htrim honeT d
    hmk0 hpb' i htlen
  have hsub : boundaryLocus
      (d.toMarkedBlowupSequenceData (p11 T).structMap (p11 T).ideal
        (p11 T).mult (p11 T).boundary hmk0).toMarkedSequenceOfBlowups i ⊆
      boundaryLocus
        (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm').toMarkedSequenceOfBlowups i := by
    simp [boundaryLocus_eq_iUnion_support, toMarkedSequence_boundary,
      toMarkedBlowupSequenceData_boundary]
    intro x hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion₂.2 ⟨D, mem_boundary_of_mem_boundary_dropTrivialBoundary T d i D hD, hxD⟩
  have hfin := orderCertificate_mono_of_subset hsub hcert
  rw [heq]
  exact orderCertificate_congr_mult (dropTrivialBoundary_mult T) hfin
  exact OrderCertificate.of_two_le _ _ _ _ _ _ hm2
  intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
  have hord : ∀ x : ((T.bc f).withBoundary E').scheme,
      orderAt ((T.bc f).withBoundary E').ideal x ≤ T.mult := by
    intro x
    have h := mp_ (isOrderBoundedByMult_iff $ (T.bc f).withBoundary E') hO' x
    rwa [withBoundary_mult, baseChange_mult] at h
  exact hdes.base_change T hv hdim (mp_ (isOrderBoundedByMult_iff T) hO) K f E' hBE hV'
    hP' hord
  intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
  have hord : ∀ x : ((T.bc f).withBoundary E').scheme,
      orderAt ((T.bc f).withBoundary E').ideal x ≤ T.mult := by
    intro x
    have h := mp_ (isOrderBoundedByMult_iff $ (T.bc f).withBoundary E') hO' x
    rwa [withBoundary_mult, baseChange_mult] at h
  exact hdes.base_change_strict T hv hdim (mp_ (isOrderBoundedByMult_iff T) hO) K f E' hBE
    hV' hP' hord
  intro T hv hdim hO hbdry hmult Y q e _ hq hsm J hJv hJd hJi
  let hP := hdim
  let hJvalid := hJv
  let hJideal := hJi
  let _a1 := (e.ker).si ≫ T.structMap
  let _a2 := T.withSchemeIdealBoundary Y q J []
  let _a4 := imageIdealSheaf (kerSubschemeIso e).inv J
  let _c0 := T.withSchemeIdealBoundary (e.ker).subscheme _a1 _a4 []
  let _c1 := _a4
  let _c2 := (p11 T).withBoundary [e.ker]
  let _c3 := _a2
  have hord' :=
    (isOrderBoundedByMult_iff T).mp hO
  have hQdim := hdimlink _ _ hJd hP
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  have hlen0 :=
    length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hP hord' hemp
  have h1 : orderAtLeastLocus T.ideal 1 = ∅ := by
    rwa [← hmult]
  have hsupp : T.ideal.supp = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have hx1 := mpr_ (mem_orderAtLeastLocus_one_iff T.ideal x) hx
    rwa [h1] at hx1
  have htop :=
    (eq_top_iff_support_eq_empty T.ideal).mpr hsupp
  have hJtop : J = ⊤ := by
    refine eq_top_of_imageIdealSheaf_eq_top e J ?_
    rwa [← hJideal]
  refine IsPushforwardBlowupSeq.of_length_eq_zero e _ _ ?_ hlen0
  refine hlow.trivial_of_coSupport_empty _c3 hJvalid hQdim ?_
  rw [withSchemeIdealBoundary_ideal, withSchemeIdealBoundary_mult, hJtop, hmult]
  exact orderAtLeastLocus_top_eq_empty 1 le_rfl
  have hne := mpr_ nonempty_iff_ne_empty hemp
  have hH : OrderReductionHypotheses P T := ⟨hP, hord', hne, hv⟩
  have hdropHyp := hH.dropTrivialBoundary hdes
  have hSb : (MaxContactReduction.dropTrivialBoundary T).boundary = [] := by
    unfold MaxContactReduction.dropTrivialBoundary
    simp [hbdry]
    rfl
  have hmultOne := hmult
  have hSq := hq
  have hSsm := hsm
  have hSsub := hJvalid
  have hSideal := hJideal
  have hci : @IsClosedImmersion Y (p11 T).scheme e :=
    inferInstanceAs $ IsClosedImmersion e
  have hhyp :=
    hstar.hypersurface (p11 T) hdropHyp hSb hmultOne Y q e hSq hSsm J hSsub hSideal
  obtain ⟨d, hm, hpb, hmain⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A L hstar hdes T hH
  have hflat := hdes.flat_coverMap (p11 T) hdropHyp
  have hsurj := hdes.surjective_coverMap (p11 T) hdropHyp
  have hequiv :=
    @IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic _ _ _ hflat hsurj _ _ _ _ hpb hhyp $ SequenceOfBlowups.isomorphic_refl _
  have hmainseq : (maxContactPrincipalization hinv A T).toSequenceOfBlowups = d.toSequenceOfBlowups := by simp_all
  have hequiv2 :
      (A 0 _c2).toSequenceOfBlowups.Isomorphic
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
    rw [hmainseq]
    exact hequiv.symm
  have hepe :=
    kerSubschemeIso_inv_comp e
  let _a3 := isoI $ kerSubschemeIso e
  let _m1 := _a3
  have hsmInv : Smooth _m1 := inferInstance
  have hsuInv : Surjective _m1 := inferInstance
  have hkerdata := hdes.valid_subst_ker T hv Y q e hq J hJvalid (kerSubschemeIso e).inv hepe
  have hT'valid : _c2.IsAdmissible :=
    hdes.valid_withDivisor T hv hbdry Y q e hq hsm
  have hT'P : P _c2.krullDimSucc := by
    rwa [withBoundary_dim]
  have hT'ord : _c2.IsOrderBoundedByMult := by
    rwa [isOrderBoundedByMult_iff]
  have hT'm : _c2.mult = 1 := by
    rwa [withBoundary_mult]
  have hT'db :=
    isBalanced_of_mult_eq_one _ hT'valid.locallyOfFiniteType hT'm
  have hT'j : 0 < _c2.boundary.length := by
    rw [MarkedIdealWithBoundary.withBoundary_boundary]
    exact Nat.zero_lt_one
  have hVsub : _c0.IsAdmissible := hkerdata.1
  have hDsub : _c0.krullDimSucc < T.krullDimSucc := by
    rwa [hkerdata.2]
  have hIdsub : T.ideal
      = imageIdealSheaf (e.ker).si
          _c1 := by
    have h1 := imageIdealSheaf_comp_comap_of_isIso (kerSubschemeIso e).inv
      (e.ker).si _c1
    rw [comap_imageIdealSheaf, hepe] at h1
    rwa [hJideal]
  have hpushD :=
    (hdiv 0).pushforward _c2 hT'valid
      hT'P hT'ord hT'db hT'j hT'm _c1 hVsub hDsub hIdsub
  have hS2Q := hdimlink _ _ hDsub hP
  have hqep : _a3 ≫ _c0.structMap = q := by
    have h0 : _a3
        ≫ _a1 = q := by
      rwa [← assoc, hepe]
    exact h0
  let _m0 := _c0.pullbackAlong Y q (kerSubschemeIso e).inv
  let _a6 := _m0.withBoundary []
  have htripleeq : _a6
      = _a2 := by
    show T.withSchemeIdealBoundary Y q
        (_c1.comap (kerSubschemeIso e).inv) []
      = _a2
    rw [comap_imageIdealSheaf]
  have hbe : SameNontrivialBoundary
      _m0.boundary [] :=
    MarkedIdealWithBoundary.SameNontrivialBoundary.refl []
  have hvalid' : _a6.IsAdmissible := by
    rwa [htripleeq]
  have hQ' : Q _a6.krullDimSucc := by
    rwa [htripleeq]
  have hstrict := @IsMaxOrderReduction.smooth_pullback_strict Q L L' hlow
    _c0 hVsub hS2Q Y q _m1
    hsmInv hsuInv hqep [] hbe hvalid' hQ'
  have hLeq :=
    eq_of_heq $ toSequenceOfBlowups_heq_of_eq htripleeq L
  have hstrict2 : IsStrictPullbackBlowupSeq _m1
      (L _c3).toSequenceOfBlowups
      (L _c0).toSequenceOfBlowups := by
    rwa [← hLeq]
  have hpushY :=
    IsPushforwardBlowupSeq.isIso_comp (kerSubschemeIso e).inv (e.ker).si e
      hepe.symm hstrict2 hpushD
  exact IsPushforwardBlowupSeq.of_isomorphic e hpushY hequiv2
  intro T hv hdim hO i hi x
  exact hdes.order_le T hv (mp_ (isOrderBoundedByMult_iff T) hO) (maxContactPrincipalization hinv A T) i hi x
  intro T hv hdim hO i hi
  let B := L
  let hd := hdes
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  exfalso
  have hb : maxContactPrincipalization hinv A T = emptyMarkedSeq T :=
    reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
  rw [hb, emptyMarkedSeq_length] at hi
  exact not_lt_zero i hi
  have h : OrderReductionHypotheses P T := ⟨hdim, mp_ (isOrderBoundedByMult_iff T) hO, mpr_ nonempty_iff_ne_empty hemp, hv⟩
  obtain ⟨d, hm, hpb, heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T h
  let _a0 := coverMarkedBlowupData (p11 T) (h.dropTrivialBoundary hd).valid hinv $ lowerDimensionalFamily A $ p11 T
  have hstarseq : ∀ j,
      j < _a0.toBlowupSequenceData.toSequenceOfBlowups.length →
      _a0.toBlowupSequenceData.toSequenceOfBlowups.center j ≠ ⊤ := by
    intro j hj
    rw [toSequenceOfBlowups_length] at hj
    exact hstar.center_ne_top (p11 T) (h.dropTrivialBoundary hd) j hj
  have hdseq := hpb.center_ne_top_of_forall_center_ne_top hstarseq
  rw [heq] at hi ⊢
  rw [toMarkedBlowupSequenceData_toSequenceOfBlowups] at hi ⊢
  exact mpr_ (support_nonempty_iff_ne_top _) $ hdseq i hi
  intro T hv hdim hO
  let B := L
  let hd := hdes
  rw [isResolution_iff, lastIdeal_eq]
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  have h1 :=
    reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
  rw [maxContactPrincipalization_apply, h1, emptyMarkedSeq_length, ideal_zero,
    hinv.coSupport_comap, hemp, preimage_empty]
  have h : OrderReductionHypotheses P T := ⟨hdim, mp_ (isOrderBoundedByMult_iff T) hO, mpr_ nonempty_iff_ne_empty hemp, hv⟩
  have h' := h.dropTrivialBoundary hd
  obtain ⟨d, hm, hpb, heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T h
  rw [heq]
  simp [toMarkedSequence_ideal, toMarkedSequence_length,
    toMarkedBlowupSequenceData_ideal, toMarkedBlowupSequenceData_length]
  have hm0 :=
    hd.isMarked (p11 T) h' d hpb
  let _m0 := isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (p11 T) h' d
  have htc := _m0.2
    (_m0.1.mpr hm0) d.length le_rfl
  have D := hpb.toStrictPullbackBlowupSeq
  rw [← toMarkedSequence_toSequenceOfBlowups] at D
  have key :=
    orderAtLeastLocus_controlledTransform_eq_empty_of_flat_surjective (hd.flat_coverMap (p11 T) h')
      (hd.surjective_coverMap (p11 T) h')
      (I := balancedTunedIdeal (p11 T) h'.valid)
      (m := tunedMult $ p11 T)
      (E := (p11 T).boundary) (d := d)
      (coverMarkedBlowupData (p11 T) h'.valid hinv
        (lowerDimensionalFamily A $ p11 T))
      D hm0.divisible $ hstar.resolves (p11 T) h'
  exact st_ htc key
  intro T hv hdim hO Y q g _ hq E' hBE hV' hP' hO'
  have hm :=
    (withBoundary_mult (T.pbA q g) E').trans
      (T.pullbackAlong_mult Y q g)
  refine hdes.smooth_pullback T hv hdim (mp_ (isOrderBoundedByMult_iff T) hO) Y q g hq E' hBE
    hV' hP' ?_
  intro x
  have h := mp_ (isOrderBoundedByMult_iff $ T.pbB q g E') hO' x
  rwa [hm] at h
  intro T hv hdim hO Y q g _ _ hq E' hBE hV' hP' hO'
  refine hdes.smooth_pullback_strict T hv hdim (mp_ (isOrderBoundedByMult_iff T) hO) Y q g hq
    E' hBE hV' hP' ?_
  intro x
  have h := mp_ (isOrderBoundedByMult_iff $ T.pbB q g E') hO' x
  rwa [tr_ (withBoundary_mult (T.pbA q g) E') $ T.pullbackAlong_mult Y q g] at h
  intro T hv hdim hO hemp
  exact length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hdim
    (mp_ (isOrderBoundedByMult_iff T) hO) hemp

theorem isOrderReduction_maxContact_dim_le_of_descentHypotheses
    (hinv : ComapIsoInvariance) n A
    L L'
    (hlow : IsMaxOrderReduction (fun d => d < n) L L')
    (hdiv : ∀ j, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (hstar : CoverSequenceProperties hinv (fun d => d ≤ n) A)
    (hdes : DescentHypotheses hinv (fun d => d ≤ n) A L) :
    IsOrderReduction (fun d => d ≤ n) (maxContactPrincipalization hinv A) L :=
  isOrderReduction_maxContact_of_descentHypotheses hinv (· ≤ n) (· < n) A L L'
    (fun _ _ hab hb => lt_of_lt_of_le hab hb) hlow hdiv hstar hdes

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactReduction

namespace FiniteOpenCoverWithIdeals

variable {T : MarkedIdealWithBoundary}

section
variable (D : FiniteOpenCoverWithIdeals T) (i : D.idx)
abbrev piece : Sch := (D.opens i).toScheme

abbrev summandio : D.piece i ⟶ D.disjointUnion :=
  Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i
end

instance instIsOpenImmersionSummandio (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsOpenImmersion $ D.summandio i :=
  by
  show IsOpenImmersion $ Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i
  infer_instance



instance instQuasiCompactSummandio (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    QuasiCompact $ D.summandio i :=
  by
  show QuasiCompact $ Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i
  infer_instance

section
variable (D : FiniteOpenCoverWithIdeals T)
section
variable (i : D.idx)
theorem summandio_comp_disjointUnionMap :
    D.summandio i ≫ D.disjointUnionMap = (D.opens i).ι :=
  sigma_io_sigmaOpensDesc T.scheme D.opens i

theorem disjointUnionMap_summandio_mem y :
    D.disjointUnionMap.base ((D.summandio i).base y) ∈ D.opens i := by
  have hmem : D.disjointUnionMap.base (bsM (D.summandio i) y) ∈ range (D.opens i).ι.base := by
    rw [← summandio_comp_disjointUnionMap D i]
    exact ⟨y, rfl⟩
  rwa [q1] at hmem

theorem comap_imageIdealSheaf_summandio :
    (imageIdealSheaf (D.summandio i) $ D.localIdeal i).comap (D.summandio i) = D.localIdeal i :=
  comap_ker_subschemeio_comp (D.localIdeal i) $ D.summandio i

abbrev summandOpen : D.disjointUnion.Opens :=
  (D.summandio i).opensRange

theorem range_summandio :
    range (D.summandio i).base = range (D.summandOpen i).ib :=
  (q1 $ D.summandOpen i).symm

abbrev summandIso :
    D.piece i ≅ (D.summandOpen i).toScheme :=
  isoOfRangeEq (D.summandio i) (D.summandOpen i).ι $ range_summandio D i

theorem isAffineOpen_summandOpen (h : IsAffineOpen (D.opens i)) :
    IsAffineOpen $ D.summandOpen i := by
  have hA : IsAffine $ oSch $ D.opens i := h
  exact isAffineOpen_opensRange $ D.summandio i

theorem restrictIdeal_summandOpen (J : D.disjointUnion.IdealSheafData) :
    restrictIdeal J (D.summandOpen i) = (J.comap $ D.summandio i).comap (D.summandIso i).inv := by
  have h : isoI (D.summandIso i) ≫ D.summandio i = opI (D.summandOpen i) := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [restrictIdeal_eq_comap_io, ← comap_comp, h]

theorem summandOpen_io_comp_disjointUnionMap :
    (D.summandOpen i).i ≫ D.disjointUnionMap = (D.summandIso i).inv ≫ (D.opens i).i := by
  have h : isoI (D.summandIso i) ≫ D.summandio i = (D.summandOpen i).i := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [← h, assoc, summandio_comp_disjointUnionMap]

section
variable {n} (c : EtaleChart T.structMap (D.opens i) n)
def summandEtaleChart :
    EtaleChart (D.disjointUnionMap ≫ structMap T) (D.summandOpen i) n where
  map := (D.summandIso i).inv ≫ c.map
  comp_struct := by
    rw [assoc, c.comp_struct, ← assoc, ← summandOpen_io_comp_disjointUnionMap,
      assoc]
  isEtale := by
    have h1 := c.isEtale
    have h4 : Etale $ (D.summandIso i).inv := inferInstance
    infer_instance

theorem summandEtaleChart_map :
    (D.summandEtaleChart i c).map = (D.summandIso i).inv ≫ c.map := rfl

theorem summandEtaleChart_coordIdeal S :
    (D.summandEtaleChart i c).coordIdeal S = (c.coordIdeal S).comap (D.summandIso i).inv := by
  rw [coordIdeal_eq_comap_coordSubspaceIdeal, coordIdeal_eq_comap_coordSubspaceIdeal, summandEtaleChart_map,
    ← comap_comp]
end

theorem restrictIdeal_comap_disjointUnionMap_summandOpen
    (J : tISD T) :
    restrictIdeal (J.comap D.disjointUnionMap) (D.summandOpen i) =
      (restrictIdeal J $ D.opens i).comap (D.summandIso i).inv := by
  rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
    ← comap_comp, summandOpen_io_comp_disjointUnionMap]
end

theorem exists_summandio_base_eq (x : ↥D.disjointUnion) :
    ∃ i y, (D.summandio i).base y = x := by
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun j => oSch $ D.opens j).surjective x
  refine ⟨i, y, ?_⟩
  show bsM (Sigma.ι (fun j => oSch $ D.opens j) i) y = x
  simpa using hx

theorem exists_mem_summandOpen (x : ↥D.disjointUnion) :
    ∃ i : D.idx, x ∈ D.summandOpen i := by
  obtain ⟨i, y, hy⟩ := D.exists_summandio_base_eq x
  exact ⟨i, ⟨y, hy⟩⟩

end

section
variable {A B : Type} [CommRing A] [CommRing B] (ph_ : A →+* B) (hinj : Injective ph_) (hsurj : Function.Surjective ph_) {I I' : Ideal A}
include hinj hsurj
theorem eq_of_map_eq_of_bijective (h : Ideal.map ph_ I = Ideal.map ph_ I') : I = I' := by
  ext x
  constructor
  intro hx
  have hmem : ph_ x ∈ Ideal.map ph_ I' := by
    rw [← h]
    exact mem_map_of_mem ph_ hx
  obtain ⟨a, ha, hax⟩ := mp_ (mem_map_iff_of_surjective (f := ph_) hsurj) hmem
  rwa [hinj hax] at ha
  intro hx
  have hmem : ph_ x ∈ Ideal.map ph_ I := by
    rw [h]
    exact mem_map_of_mem ph_ hx
  obtain ⟨a, ha, hax⟩ := mp_ (mem_map_iff_of_surjective (f := ph_) hsurj) hmem
  rwa [hinj hax] at ha

theorem ideal_le_of_map_le_of_bijective (h : Ideal.map ph_ I ≤ Ideal.map ph_ I') : I ≤ I' := by
  intro a ha
  obtain ⟨b, hb, hba⟩ := mp_ (mem_map_iff_of_surjective (f := ph_) hsurj) $ h $ mem_map_of_mem ph_ ha
  rwa [hinj hba] at hb
end

section
variable {X : Sch}
theorem top_le_preimage_opens (V : Opn X) :
    (⊤ : V.toScheme.Opens) ≤ (TopologicalSpace.Opens.map V.ib).obj V :=by simp_all
theorem appLE_io_eq_topIso_inv (V : Opn X) :
    V.ι.appLE V ⊤ (top_le_preimage_opens V) = V.topIso.inv := by
  simp
  rfl

private theorem ideal_eq_of_comap_io_eq {I J : ISD X}
    (V : Opn X) (hV : IsAffineOpen V) (h : I.comap V.i = J.comap V.i) :
    I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have key1 := comap_ideal_eq_map_appLE I V.i ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ $ top_le_preimage_opens V
  have key2 := comap_ideal_eq_map_appLE J V.i ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ $ top_le_preimage_opens V
  rw [h] at key1
  have hinj : Injective
      (hom $ V.ι.appLE V ⊤ (top_le_preimage_opens V)) := by
    rw [appLE_io_eq_topIso_inv V]
    exact V.topIso.symm.commRingCatIsoToRingEquiv.injective
  refine eq_of_map_eq_of_bijective _ hinj ?_ $ st_ key1 key2
  rw [appLE_io_eq_topIso_inv V]
  exact V.topIso.symm.commRingCatIsoToRingEquiv.surjective

theorem ext_of_comap_io_eq_of_iSup_eq_top {ι : Type} (U : ι → Opn X)
    (hU : iSup U = ⊤) {I J : ISD X}
    (h : ∀ i : ι, I.comap (U i).i = J.comap (U i).i) : I = J := by
  refine ext_of_iSup_eq_top
    (ι := {W : affO X // ∃ i, W.1 ≤ U i})
    (·.1) ?_ ?_
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ iSup U := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := mp_ mem_iSup hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    isBasis_iff_nbhd.mp X.isBasis_affineOpens hi
  exact mpr_ mem_iSup ⟨⟨⟨V, hV⟩, i, hVU⟩, hxV⟩
  rintro ⟨⟨W, hW⟩, i, hWU⟩
  refine ideal_eq_of_comap_io_eq W hW ?_
  have e1 : I.comap W.i = (I.comap (U i).i).comap (X.homOfLE hWU) := by
    rw [← comap_comp, Scheme.homOfLE_ι]
  have e2 : J.comap W.i = (J.comap (U i).i).comap (X.homOfLE hWU) := by
    rw [← comap_comp, Scheme.homOfLE_ι]
  rw [e1, e2, h i]
end

section
variable {Y : Sch} {J J' : ISD Y}
theorem ideal_le_of_comap_io_le
    (V : Opn Y) (hV : IsAffineOpen V) (h : J.comap V.i ≤ J'.comap V.i) :
    J.ideal ⟨V, hV⟩ ≤ J'.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have k1 := comap_ideal_eq_map_appLE J V.i ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ $ top_le_preimage_opens V
  have k2 := comap_ideal_eq_map_appLE J' V.i ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ $ top_le_preimage_opens V
  have hle := Scheme.IdealSheafData.le_def.mp h ⟨⊤, isAffineOpen_top V.toScheme⟩
  rw [k1, k2, appLE_io_eq_topIso_inv V] at hle
  exact ideal_le_of_map_le_of_bijective _ V.topIso.symm.commRingCatIsoToRingEquiv.injective V.topIso.symm.commRingCatIsoToRingEquiv.surjective hle

theorem le_of_ideal_le_locally
    (V : ↥Y → Opn Y) (hmem : ∀ y : ↥Y, y ∈ V y)
    (hloc : ∀ y W hW, W ≤ V y →
      J.ideal ⟨W, hW⟩ ≤ J'.ideal ⟨W, hW⟩) :
    J ≤ J' := by
  refine mp_ inf_eq_left ?_
  refine ext_of_iSup_eq_top
    (ι := {W : affO Y // ∃ y, W.1 ≤ V y})
    (·.1) ?_ ?_
  rw [eq_top_iff]
  intro x _
  obtain ⟨W, hW, hxW, hWV⟩ :=
    isBasis_iff_nbhd.mp Y.isBasis_affineOpens $ hmem x
  exact mpr_ mem_iSup ⟨⟨⟨W, hW⟩, x, hWV⟩, hxW⟩
  rintro ⟨⟨W, hW⟩, y, hWV⟩
  show (J ⊓ J').ideal ⟨W, hW⟩ = J.ideal ⟨W, hW⟩
  simp [ideal_inf, Pi.inf_apply, inf_eq_left]
  exact hloc y W hW hWV
end

section
variable (D : FiniteOpenCoverWithIdeals T) {J J' : D.disjointUnion.IdealSheafData}
theorem ext_of_comap_summandio
    (h : ∀ i : D.idx, J.comap (D.summandio i) = J'.comap (D.summandio i)) : J = J' := by
  refine ext_of_comap_io_eq_of_iSup_eq_top D.summandOpen ?_ ?_
  rw [eq_top_iff]
  intro x _
  obtain ⟨i, hi⟩ := D.exists_mem_summandOpen x
  exact mpr_ mem_iSup ⟨i, hi⟩
  intro i
  have h1 := restrictIdeal_summandOpen D i J
  rw [h i] at h1
  exact tr_ h1 (restrictIdeal_summandOpen D i J').symm

theorem le_of_comap_summandio_le
    (h : ∀ i : D.idx, J.comap (D.summandio i) ≤ J'.comap (D.summandio i)) : J ≤ J' := by
  classical
  choose idxf hidxf using D.exists_mem_summandOpen
  refine le_of_ideal_le_locally (fun y => D.summandOpen $ idxf y) hidxf ?_
  intro y W hW hWle
  refine ideal_le_of_comap_io_le W hW ?_
  let _m0 := D.summandio $ idxf y
  have hrange : range W.ib ⊆ range _m0.base := by
    rwa [q1, range_summandio D $ idxf y, q1]
  have hg :=
    m115 _m0 W.i hrange
  let _a0 := m43 _m0 W.i hrange
  have e1 : J.comap W.i
      = (cmI J _m0).comap
        _a0 := by
    rw [← comap_comp, hg]
  have e2 : J'.comap W.i
      = (cmI J' _m0).comap
        _a0 := by
    rw [← comap_comp, hg]
  rw [e1, e2]
  exact comap_mono _ $ h $ idxf y
end

private theorem imageIdealSheaf_eq_ker {X Y : Sch} (f : X ⟶ Y) [QuasiCompact f]
    (I : ISD X) : imageIdealSheaf f I = ker (subschemeι I ≫ f) := rfl

theorem ideal_ker_eq_top_of_disjoint {Y Z : Sch} (g : Z ⟶ Y) [QuasiCompact g]
    (U : Y.affineOpens) (hdisj : ∀ z : ↥Z, g.base z ∉ (U.1 : Set ↥Y)) :
    (ker g).ideal U = ⊤ := by
  let _c0 := pObj Z $ m112 (⊥)
  have hempty : preU g U.1 = ⊥ := by
    refine m55 ?_
    rw [coe_bot]
    exact mpr_ eq_empty_iff_forall_notMem fun z hz => hdisj z hz
  have hsub : Subsingleton $ pObj Z $ m112 $ preU g U.1 := by
    rw [hempty]
    refine ⟨fun a b => ?_⟩
    have h := (TopCat.Sheaf.isTerminalOfEmpty Z.sheaf).hom_ext
      (ofHom $ RingHom.fst _c0
        _c0)
      (ofHom $ RingHom.snd _c0
        _c0)
    exact congrArg (fun m => (hom m) (a, b)) h
  rw [ker_apply]
  refine mpr_ (eq_top_iff_one _) ?_
  rw [m208, map_one]
  exact m111 _ _

section
variable (D : FiniteOpenCoverWithIdeals T)
theorem ideal_imageIdealSheaf_eq_top_of_ne {i j} (hij : j ≠ i)
    W (hW : IsAffineOpen W)
    (hsub : ∀ y ∈ W, y ∈ range (D.summandio i).base) :
    (imageIdealSheaf (D.summandio j) $ D.localIdeal j).ideal ⟨W, hW⟩ = ⊤ := by
  rw [imageIdealSheaf_eq_ker]
  refine ideal_ker_eq_top_of_disjoint (siI (D.localIdeal j) ≫ D.summandio j) ⟨W, hW⟩ ?_
  intro z hz
  obtain ⟨v, hv⟩ := hsub _ hz
  exact sigmaio_base_ne (fun t => oSch $ D.opens t) hij
    ((D.localIdeal j).subschemeι.base z) v $ st_ rfl hv.symm

theorem comap_iInfImageIdeal_summandio i :
    D.iInfImageIdeal.comap (D.summandio i) = D.localIdeal i := by
  have hglue : D.iInfImageIdeal
      = ⨅ j : D.idx, imageIdealSheaf (D.summandio j) (D.localIdeal j) := rfl
  refine le_antisymm ?_ ?_
  rw [hglue]
  exact le_trans (comap_mono (D.summandio i) (iInf_le _ i))
    (le_of_eq (comap_imageIdealSheaf_summandio D i))
  rw [le_def]
  intro V
  let _m0 := imU (D.summandio i) V.1
  have hW :=
    V.2.image_of_isOpenImmersion (D.summandio i)
  have hle : V.1 ≤ preU (D.summandio i) _m0 := fun x hx => ⟨x, hx, rfl⟩
  have hsub : ∀ y ∈ (_m0 : Set D.disjointUnion),
      y ∈ range (D.summandio i).base := by
    rintro y ⟨v, hv, rfl⟩
    exact ⟨v, rfl⟩
  have h1 := comap_ideal_eq_map_appLE D.iInfImageIdeal (D.summandio i)
    ⟨_, hW⟩ V hle
  let _a0 := imageIdealSheaf (D.summandio i) (D.localIdeal i)
  have h2 := comap_ideal_eq_map_appLE
    _a0 (D.summandio i) ⟨_, hW⟩ V hle
  have h3 : D.iInfImageIdeal.ideal ⟨_, hW⟩
      = _a0.ideal ⟨_, hW⟩ := by
    rw [hglue]
    simp [ideal_iInf, iInf_apply]
    refine le_antisymm (iInf_le _ i) $ le_iInf fun j => ?_
    by_cases hj : j = i
    rw [hj]
    rw [ideal_imageIdealSheaf_eq_top_of_ne D hj _ hW hsub]
    exact le_top
  have h4 : (D.iInfImageIdeal.comap (D.summandio i)).ideal V = (D.localIdeal i).ideal V := by
    rw [h1, h3, ← h2, comap_imageIdealSheaf_summandio D i]
  exact le_of_eq h4.symm

theorem restrictIdeal_iInfImageIdeal_summandOpen i :
    restrictIdeal D.iInfImageIdeal (D.summandOpen i) =
      (D.localIdeal i).comap (D.summandIso i).inv := by
  rw [restrictIdeal_summandOpen D i D.iInfImageIdeal, comap_iInfImageIdeal_summandio D i]
end

instance instEtaleTotalMap (D : FiniteOpenCoverWithIdeals T) : Etale D.disjointUnionMap := etale_sigmaOpensDesc T.scheme D.opens

theorem smooth_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap := by
  infer_instance

instance instSmoothTotalMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap :=
  smooth_disjointUnionMap D


theorem locallyOfFiniteType_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_sigmaOpensDesc T.scheme D.opens

instance instLocallyOfFiniteTypeTotalMap (D : FiniteOpenCoverWithIdeals T) : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_disjointUnionMap D

section
variable (D : FiniteOpenCoverWithIdeals T)
theorem surjective_disjointUnionMap (h : iSup D.opens = ⊤) :
    Surjective D.disjointUnionMap :=
  surjective_sigmaOpensDesc T.scheme D.opens h

theorem isSmoothDivisor_iInfImageIdeal_of_exists_etaleChart
    (h : ∀ i : D.idx, ∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n),
      D.localIdeal i = ⊤ ∨ ∃ j : Fin n, D.localIdeal i = c.coordIdeal {j}) :
    IsSmoothDivisor (D.disjointUnionMap ≫ structMap T) D.iInfImageIdeal := by
  refine isSmoothDivisor_of_locally_coordIdeal D.iInfImageIdeal ?_
  intro x
  obtain ⟨i, hi⟩ := D.exists_mem_summandOpen x
  obtain ⟨n, c, hc⟩ := h i
  refine ⟨D.summandOpen i, hi, n, D.summandEtaleChart i c, ?_⟩
  rcases hc with htop | ⟨j, hj⟩
  left
  rw [restrictIdeal_iInfImageIdeal_summandOpen D i, htop]
  simp
  right
  refine ⟨j, ?_⟩
  rw [restrictIdeal_iInfImageIdeal_summandOpen D i, hj]
  exact sy_ $ summandEtaleChart_coordIdeal D i c {j}

theorem isSmoothDivisor_iInfImageIdeal_of_forall_eq_top_or_coordIdeal
    (halt : ∀ i : D.idx, D.localIdeal i = ⊤ ∨
      ∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n) (j : Fin n),
        D.localIdeal i = c.coordIdeal {j})
    (hchart : ∀ i : D.idx, ∃ n : ℕ, Nonempty $ EtaleChart T.structMap (D.opens i) n) :
    IsSmoothDivisor (D.disjointUnionMap ≫ structMap T) D.iInfImageIdeal := by
  refine isSmoothDivisor_iInfImageIdeal_of_exists_etaleChart D ?_
  intro i
  rcases halt i with htop | ⟨n, c, j, hj⟩
  obtain ⟨m, ⟨c⟩⟩ := hchart i
  exact ⟨m, c, inl htop⟩
  exact ⟨n, c, inr ⟨j, hj⟩⟩
end

theorem subsingleton_spec (k : Type) [Field k] :
    Subsingleton ↥(Sp k) :=
  inferInstanceAs $ Subsingleton $ PrimeSpectrum k

theorem quasiCompact_disjointUnionMap_comp (D : FiniteOpenCoverWithIdeals T)
    (h : ∀ i : D.idx, IsAffineOpen $ D.opens i) :
    QuasiCompact $ D.disjointUnionMap ≫ structMap T := by
  have haff : IsAffine D.disjointUnion := by
    exact isAffine_sigmaOpens T.scheme D.opens h
  have hcs : CompactSpace D.disjointUnion := inferInstance
  have hsub := subsingleton_spec T.base
  exact AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
    (D.disjointUnionMap ≫ tMp T)

end FiniteOpenCoverWithIdeals

end MaxContactReduction

end FunctorialResolution.EmbeddedResolution

end
section
universe v w

open CategoryTheory.Limits

section

namespace FunctorialResolution.EmbeddedResolution

abbrev markedTripleOfIdeal (k : Type) [Field k] (Y : Sch)
    (q : Y ⟶ Sp k) (J : IdealSheafData Y) : MarkedIdealWithBoundary :=
  { base := k, scheme := Y, structMap := q, ideal := J, mult := 1, boundary := [] }




def HasLocalEtaleCharts {X' : Sch} {k : Type} [Field k]
    (p : X' ⟶ Sp k) : Prop :=
  ∀ x : X', ∃ (W : Opn X') (_ : x ∈ W) (n : ℕ), Nonempty $ EtaleChart p W n

theorem ofIdealTop_mono {X : Sch} {I J : Ideal Γ(X, ⊤)} (h : I ≤ J) :
    ofIdealTop I ≤
      ofIdealTop J := by
  intro U
  exact map_mono h

theorem EtaleChart.coordIdeal_mono {Y : Sch} {k : Type} [Field k]
    {p : Y ⟶ Sp k} {U : Opn Y} {m : ℕ} (ch : EtaleChart p U m)
    {S S' : FinSet m} (h : S ⊆ S') :
    ch.coordIdeal S ≤ ch.coordIdeal S' := by
  simp [coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  apply comap_mono
  apply ofIdealTop_mono
  apply span_mono
  rintro x ⟨i, hi, rfl⟩
  exact ⟨i, mpr_ mem_coe $ h $ mp_ mem_coe hi, rfl⟩

section
variable {X X' : Sch} (ta_ : X ⟶ X') [IsClosedImmersion ta_]
theorem coe_support_ker_eq_range :
    (↑(ker ta_).support : Set X') = range ta_.base := by
  let _a0 := kerSubschemeIso ta_
  have h1 : ∀ z, bsM (isoH _a0 ≫ ta_) z
      = (ker ta_).subschemeι.base z := by
    intro z
    rw [kerSubschemeIso_hom_comp ta_]
  have h2 : ∀ x, bsM (isoI _a0 ≫ siI (ker ta_)) x
      = bsM ta_ x := by
    intro x
    rw [kerSubschemeIso_inv_comp ta_]
  rw [← q5]
  apply m15
  rintro y ⟨z, rfl⟩
  exact ⟨ihB_ _a0 z, h1 z⟩
  rintro y ⟨x, rfl⟩
  exact ⟨ibM _a0 x, h2 x⟩

theorem restrictIdeal_ker_eq_top_of_not_mem U (h : ∀ x : X, ta_.base x ∉ U) :
    restrictIdeal ta_.ker U = ⊤ := by
  rw [restrictIdeal_eq_comap_io, eq_top_iff_support_eq_empty, support_comap_eq,
    coe_support_ker_eq_range ta_]
  refine mp_ subset_empty_iff ?_
  rintro y ⟨x, hx⟩
  refine absurd ?_ $ h x
  rw [hx]
  exact y.2
end

structure AdaptedEtaleChart {X X' : Sch} {k : Type} [Field k]
    (p : X' ⟶ Sp k) (ta_ : X ⟶ X') (c : ℕ) : Type where
  opens : Opn X'
  isAffine : IsAffineOpen opens
  coordCount : ℕ
  chart : EtaleChart p opens coordCount
  idxSet : FinSet coordCount
  card_idxSet : idxSet.card = c
  coord : Fin coordCount
  coord_mem : coord ∈ idxSet
  restrictIdeal_ker : restrictIdeal ta_.ker opens = chart.coordIdeal idxSet

private theorem coordIdeal_restrict {X : Sch} {k : Type} [Field k]
    {p : X ⟶ Sp k} {U V : Opn X} {m : ℕ} (ch : EtaleChart p U m)
    (h : V ≤ U) (S : FinSet m) :
    (ch.restrict h).coordIdeal S = (ch.coordIdeal S).comap (X.homOfLE h) := by
  simp only [coordIdeal_eq_comap_coordSubspaceIdeal, restrict_map]
  rw [comap_comp]

structure DisjointEtaleChart {X X' : Sch} {k : Type} [Field k]
    (p : X' ⟶ Sp k) (ta_ : X ⟶ X') : Type where
  opens : Opn X'
  isAffine : IsAffineOpen opens
  coordCount : ℕ
  chart : EtaleChart p opens coordCount
  not_mem : ∀ x : X, ta_.base x ∉ opens

def coverOpens {X X' : Sch} {k : Type} [Field k]
    {p : X' ⟶ Sp k} {ta_ : X ⟶ X'} {c : ℕ} {al_ : Type v} {be_ : Type w}
    (A : al_ → AdaptedEtaleChart p ta_ c) (B : be_ → DisjointEtaleChart p ta_) : al_ ⊕ be_ → Opn X'
  | Sum.inl a => (A a).opens
  | Sum.inr b => (B b).opens



def coverHypersurfaceIdeal {X X' : Sch} {k : Type} [Field k]
    {p : X' ⟶ Sp k} {ta_ : X ⟶ X'} {c : ℕ} {al_ : Type v} {be_ : Type w}
    (A : al_ → AdaptedEtaleChart p ta_ c) (B : be_ → DisjointEtaleChart p ta_) :
    (i : al_ ⊕ be_) → (coverOpens A B i).toScheme.IdealSheafData
  | Sum.inl a => (A a).chart.coordIdeal {(A a).coord}
  | Sum.inr _ => ⊤


structure MaximalContactCover {X X' : Sch} {k : Type} [Field k]
    (p : X' ⟶ Sp k) (ta_ : X ⟶ X') (I : ISD X) (c : ℕ) :
    Type 1 where
  toCoverData : MaxContactReduction.FiniteOpenCoverWithIdeals $ markedTripleOfIdeal k X' p $ imageIdealSheaf ta_ I
  covers : iSup toCoverData.opens = ⊤
  isAffine : ∀ i : toCoverData.idx, IsAffineOpen $ toCoverData.opens i
  hasChart : ∀ i : toCoverData.idx, ∃ n : ℕ,
    Nonempty $ EtaleChart p (toCoverData.opens i) n
  hypersurface : ∀ i : toCoverData.idx, toCoverData.localIdeal i = ⊤ ∨
    ∃ (n : ℕ) (ch : EtaleChart p (toCoverData.opens i) n) (j : Fin n),
      toCoverData.localIdeal i = ch.coordIdeal {j}
  adapted : ∀ i : toCoverData.idx,
    (toCoverData.localIdeal i = ⊤ ∧ ∀ x : X, ta_.base x ∉ toCoverData.opens i) ∨
    ∃ (n : ℕ) (ch : EtaleChart p (toCoverData.opens i) n) (S : FinSet n) (j : Fin n),
      S.card = c ∧ j ∈ S ∧
        restrictIdeal ta_.ker (toCoverData.opens i) = ch.coordIdeal S ∧
        toCoverData.localIdeal i = ch.coordIdeal {j}

theorem nonempty_maximalContactCover {X X' : Sch} {k : Type} [Field k]
    (p : X' ⟶ Sp k) [QuasiCompact p]
    (ta_ : X ⟶ X') [IsClosedImmersion ta_] (I : ISD X) (c : ℕ) (hc : 1 ≤ c)
    (hcodim : HasEtaleCoordCodim p ta_ c) (hcharts : HasLocalEtaleCharts p) :
    Nonempty $ MaximalContactCover p ta_ I c := by
  classical
  have hSpec : IsCompact (univ : Set $ Sp k) := by
    have h := (AlgebraicGeometry.isAffineOpen_top $ Sp k).isCompact
    rwa [coe_top] at h
  have hX'c : IsCompact (univ : Set X') := by
    have h := AlgebraicGeometry.QuasiCompact.isCompact_preimage (f := p) univ isOpen_univ hSpec
    rwa [preimage_univ] at h
  let _a0 := AdaptedEtaleChart p ta_ c
  let _a1 := DisjointEtaleChart p ta_
  have hcover : ∀ y : X', ∃ q : _a0 ⊕ _a1,
      y ∈ coverOpens (fun a : _a0 => a) (fun b : _a1 => b) q := by
    intro y
    by_cases hy : ∃ x, bsM ta_ x = y
    obtain ⟨x, hx⟩ := hy
    have _i34 : ∀ x, ∃ A : AdaptedEtaleChart p ta_ c, bsM ta_ x ∈ A.opens := by
      intro x
      obtain ⟨U, hxU, m, ch, S, hcard, hker⟩ := hcodim x
      obtain ⟨V, hxV, hVU⟩ := exists_affineOpens_mem_le hxU
      obtain ⟨j, hj⟩ := mp_ card_pos (by rw [hcard]; omega)
      refine ⟨⟨V, V.2, m, ch.restrict hVU, S, hcard, j, hj, ?_⟩, hxV⟩
      rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal (ker ta_) hVU, hker,
        coordIdeal_restrict ch hVU S]
    obtain ⟨A, hA⟩ := _i34 x
    refine ⟨m44 A, ?_⟩
    rwa [← hx]
    have hy' := fun x hx => hy ⟨x, hx⟩
    obtain ⟨F, hF⟩ : ∃ F : DisjointEtaleChart p ta_, y ∈ F.opens := by
      obtain ⟨W, hyW, n, ⟨ch⟩⟩ := hcharts y
      have hclosed : IsClosed $ range ta_.base := by
        rw [← coe_support_ker_eq_range ta_]
        exact (ker ta_).support.2
      have hynot : y ∉ range ta_.base := by simp_all
      set O : Opn X' := ⟨W ∩ (range ta_.base)ᶜ, W.isOpen.inter hclosed.isOpen_compl⟩
      have hyO : y ∈ O := mem_inter hyW hynot
      obtain ⟨U, hyU, hUO⟩ := exists_affineOpens_mem_le hyO
      have hUW : U ≤ W := by
        intro z hz
        exact (hUO hz).1
      refine ⟨⟨U, U.2, n, ch.restrict hUW, ?_⟩, hyU⟩
      intro x hx
      exact (hUO hx).2 ⟨x, rfl⟩
    exact ⟨m50 F, hF⟩
  have hsub : univ ⊆
      ⋃ q : _a0 ⊕ _a1,
        ((coverOpens (fun a => a) (fun b => b) q :
          Opn X') : Set X') := by
    intro y _
    obtain ⟨q, hq⟩ := hcover y
    exact mem_iUnion.2 ⟨q, hq⟩
  obtain ⟨t, ht⟩ := hX'c.elim_finite_subcover
    (fun q =>
      ((coverOpens (fun a => a) (fun b => b) q :
        Opn X') : Set X'))
    (fun q => (coverOpens (fun a => a) (fun b => b) q).isOpen)
    hsub
  refine ⟨⟨⟨{ q : _a0 ⊕ _a1 // q ∈ t }, inferInstance,
    fun q => coverOpens (fun a => a) (fun b => b) q.1,
    fun q => coverHypersurfaceIdeal (fun a => a)
      (fun b => b) q.1⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  apply m55
  rw [coe_iSup, coe_top]
  refine eq_univ_of_forall fun y => ?_
  obtain ⟨q, hqt, hq⟩ := Set.mem_iUnion₂.1 $ ht $ Set.mem_univ y
  exact mem_iUnion.2 ⟨⟨q, hqt⟩, hq⟩
  rintro ⟨A | F, _⟩
  exact A.isAffine
  exact F.isAffine
  rintro ⟨A | F, _⟩
  exact ⟨A.coordCount, ⟨A.chart⟩⟩
  exact ⟨F.coordCount, ⟨F.chart⟩⟩
  rintro ⟨A | F, _⟩
  exact inr ⟨A.coordCount, A.chart, A.coord, rfl⟩
  exact inl rfl
  rintro ⟨A | F, _⟩
  exact inr ⟨A.coordCount, A.chart, A.idxSet, A.coord, A.card_idxSet, A.coord_mem,
    A.restrictIdeal_ker, rfl⟩
  exact inl ⟨rfl, F.not_mem⟩

namespace MaximalContactCover

variable {X X' : Sch} {k : Type} [Field k] {p : X' ⟶ Sp k}
  {ta_ : X ⟶ X'} {I : ISD X} {c : ℕ}

section
variable (C : MaximalContactCover p ta_ I c)
abbrev projection : C.toCoverData.disjointUnion ⟶ X' :=
  C.toCoverData.disjointUnionMap

@[simp] theorem projection_eq :
    C.projection = C.toCoverData.disjointUnionMap := rfl



theorem quasiCompact_projection_comp :
    QuasiCompact $ C.projection ≫ p :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.quasiCompact_disjointUnionMap_comp C.toCoverData C.isAffine
end

instance instQuasiCompactProjComp (C : MaximalContactCover p ta_ I c) :
    QuasiCompact $ C.projection ≫ p :=
  C.quasiCompact_projection_comp



theorem locallyOfFiniteType_projection_comp (C : MaximalContactCover p ta_ I c)
    [LocallyOfFiniteType p] :
    LocallyOfFiniteType $ C.projection ≫ p := by
  exact MorphismProperty.comp_mem (@LocallyOfFiniteType) C.projection p (MaxContactReduction.FiniteOpenCoverWithIdeals.locallyOfFiniteType_disjointUnionMap C.toCoverData)
    inferInstance

instance instLocallyOfFiniteTypeProjComp (C : MaximalContactCover p ta_ I c)
    [LocallyOfFiniteType p] :
    LocallyOfFiniteType $ C.projection ≫ p :=
  C.locallyOfFiniteType_projection_comp

section
variable (C : MaximalContactCover p ta_ I c)
theorem isSmoothDivisor_iInfImageIdeal :
    IsSmoothDivisor (C.projection ≫ p) C.toCoverData.iInfImageIdeal :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.isSmoothDivisor_iInfImageIdeal_of_forall_eq_top_or_coordIdeal C.toCoverData C.hypersurface C.hasChart

theorem surjective_projection :
    Surjective C.projection :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.surjective_disjointUnionMap C.toCoverData C.covers

abbrev pullbackFiber : Sch :=
  Limits.pullback ta_ C.projection

abbrev pullbackFiberToTotal : C.pullbackFiber ⟶ C.toCoverData.disjointUnion :=
  snd ta_ C.projection

abbrev pullbackFiberToBase : C.pullbackFiber ⟶ X :=
  fst ta_ C.projection

theorem isPullback_pullbackFiber :
    IsPullback C.pullbackFiberToBase C.pullbackFiberToTotal ta_ C.projection :=
  m186 ta_ C.projection

end

instance instIsClosedImmersionStarEmb (C : MaximalContactCover p ta_ I c) [IsClosedImmersion ta_] :
    IsClosedImmersion C.pullbackFiberToTotal := by
  exact of_isPullback
      (P := @IsClosedImmersion) C.isPullback_pullbackFiber inferInstance



section
variable (C : MaximalContactCover p ta_ I c)
theorem smooth_pullbackFiberToBase :
    Smooth C.pullbackFiberToBase := by
  exact of_isPullback
    (P := @Smooth) C.isPullback_pullbackFiber.flip $ MaxContactReduction.FiniteOpenCoverWithIdeals.smooth_disjointUnionMap C.toCoverData


theorem surjective_pullbackFiberToBase :
    Surjective C.pullbackFiberToBase := by
  exact of_isPullback
    (P := @Surjective) C.isPullback_pullbackFiber.flip C.surjective_projection


theorem ker_pullbackFiberToTotal [IsClosedImmersion ta_] :
    ker C.pullbackFiberToTotal = ta_.ker.comap C.projection := by
  exact ker_eq_comap_ker_of_isPullback_of_flat C.isPullback_pullbackFiber

theorem exists_factor_pullbackFiberToTotal [IsClosedImmersion ta_] :
    ∃ f : C.pullbackFiber ⟶ C.toCoverData.iInfImageIdeal.subscheme,
      f ≫ C.toCoverData.iInfImageIdeal.si = C.pullbackFiberToTotal := by
  have hle : C.toCoverData.iInfImageIdeal ≤ ker C.pullbackFiberToTotal := by
    rw [C.ker_pullbackFiberToTotal]
    refine MaxContactReduction.FiniteOpenCoverWithIdeals.le_of_comap_summandio_le C.toCoverData ?_
    intro i
    have e2 : ((ker ta_).comap C.toCoverData.disjointUnionMap).comap
          (C.toCoverData.summandio i)
        = restrictIdeal (ker ta_) (C.toCoverData.opens i) := by
      rw [← comap_comp,
        MaxContactReduction.FiniteOpenCoverWithIdeals.summandio_comp_disjointUnionMap, restrictIdeal_eq_comap_io]
    rw [MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandio C.toCoverData i, e2]
    rcases C.adapted i with ⟨htop, hnot⟩ | ⟨n, ch, S, j, hcard, hjS, hrestrict, hloc⟩
    exact le_of_eq $ tr_ htop (restrictIdeal_ker_eq_top_of_not_mem ta_ _ hnot).symm
    rw [hloc, hrestrict]
    exact ch.coordIdeal_mono $ Finset.singleton_subset_iff.mpr hjS
  have hle' : ker C.toCoverData.iInfImageIdeal.si
      ≤ ker C.pullbackFiberToTotal := by
    rwa [q2]
  exact ⟨lift C.toCoverData.iInfImageIdeal.si C.pullbackFiberToTotal hle',
    lift_fac C.toCoverData.iInfImageIdeal.si C.pullbackFiberToTotal hle'⟩

def pullbackFiberToHypersurface [IsClosedImmersion ta_] :
    C.pullbackFiber ⟶ C.toCoverData.iInfImageIdeal.subscheme :=
  (C.exists_factor_pullbackFiberToTotal).choose

section
variable [hv1_0 : IsClosedImmersion ta_]
include hv1_0
theorem pullbackFiberToHypersurface_comp_subschemeio :
    C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι = C.pullbackFiberToTotal :=
  (C.exists_factor_pullbackFiberToTotal).choose_spec

theorem pullbackFiberToHypersurface_comp_subschemeio_assoc
    {Z} (h : C.toCoverData.disjointUnion ⟶ Z) :
    C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.si ≫ h = C.pullbackFiberToTotal ≫ h := by
  rw [← assoc, C.pullbackFiberToHypersurface_comp_subschemeio]

theorem isClosedImmersion_pullbackFiberToHypersurface_comp_subschemeio :
    IsClosedImmersion $ C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.si := by
  rw [C.pullbackFiberToHypersurface_comp_subschemeio]
  infer_instance

theorem isClosedImmersion_pullbackFiberToHypersurface :
    IsClosedImmersion C.pullbackFiberToHypersurface := by
  have := isClosedImmersion_pullbackFiberToHypersurface_comp_subschemeio C
  exact of_comp C.pullbackFiberToHypersurface
    C.toCoverData.iInfImageIdeal.si
end
end

instance instIsClosedImmersionStarFactor (C : MaximalContactCover p ta_ I c) [IsClosedImmersion ta_] :
    IsClosedImmersion C.pullbackFiberToHypersurface :=
  C.isClosedImmersion_pullbackFiberToHypersurface

section
variable (C : MaximalContactCover p ta_ I c)
def comapImageIdealSheaf : C.toCoverData.disjointUnion.IdealSheafData :=
  (imageIdealSheaf ta_ I).comap C.projection

theorem comapImageIdealSheaf_eq :
    C.comapImageIdealSheaf = (imageIdealSheaf ta_ I).comap C.projection := rfl

def idealOnHypersurface :
    C.toCoverData.iInfImageIdeal.subscheme.IdealSheafData :=
  C.comapImageIdealSheaf.comap C.toCoverData.iInfImageIdeal.si

theorem idealOnHypersurface_eq_comap :
    C.idealOnHypersurface = C.comapImageIdealSheaf.comap C.toCoverData.iInfImageIdeal.si := rfl

section
variable [hv1_0 : IsClosedImmersion ta_]
include hv1_0
theorem localIdeal_le_restrictIdeal_ker
    (i : C.toCoverData.idx) :
    C.toCoverData.localIdeal i ≤ restrictIdeal (ker ta_) (C.toCoverData.opens i) := by
  rcases C.adapted i with ⟨htop, hnot⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
  have h1 := restrictIdeal_ker_eq_top_of_not_mem ta_ (C.toCoverData.opens i) hnot
  rw [htop]
  exact h1.ge
  rw [hloc, hker]
  exact ch.coordIdeal_mono $ Finset.singleton_subset_iff.mpr hjS

theorem iInfImageIdeal_le_comap_ker :
    C.toCoverData.iInfImageIdeal ≤ (ker ta_).comap C.toCoverData.disjointUnionMap := by
  refine MaxContactReduction.FiniteOpenCoverWithIdeals.le_of_comap_summandio_le C.toCoverData ?_
  intro i
  rw [MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandio,
    ← comap_comp,
    MaxContactReduction.FiniteOpenCoverWithIdeals.summandio_comp_disjointUnionMap]
  exact localIdeal_le_restrictIdeal_ker C i

theorem comapImageIdealSheaf_eq_imageIdealSheaf_idealOnHypersurface :
    C.comapImageIdealSheaf = imageIdealSheaf C.toCoverData.iInfImageIdeal.si C.idealOnHypersurface := by
  have hG : ker C.toCoverData.iInfImageIdeal.si = C.toCoverData.iInfImageIdeal := by
    simp
  have hle : ker C.toCoverData.iInfImageIdeal.si ≤ C.comapImageIdealSheaf := by
    rw [hG, C.comapImageIdealSheaf_eq]
    exact le_trans (iInfImageIdeal_le_comap_ker C)
      (comap_mono C.projection $ ker_le_map_idealSheaf ta_ I)
  have h2 := ker_subschemeio_comp_eq_of_ker_le C.toCoverData.iInfImageIdeal.si C.comapImageIdealSheaf hle
    C.idealOnHypersurface C.idealOnHypersurface_eq_comap
  exact sy_ h2

theorem idealOnHypersurface_eq_imageIdealSheaf :
    C.idealOnHypersurface = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) := by
  have hqc : QuasiCompact ta_ := inferInstance
  have h1 : (imageIdealSheaf ta_ I).comap C.projection
      = imageIdealSheaf C.pullbackFiberToTotal (I.comap C.pullbackFiberToBase) :=
    comap_map_eq_map_comap_of_isPullback C.isPullback_pullbackFiber I
  let _a0 := imageIdealSheaf C.pullbackFiberToHypersurface $ I.comap C.pullbackFiberToBase
  have h2 : imageIdealSheaf C.pullbackFiberToTotal (I.comap C.pullbackFiberToBase)
      = imageIdealSheaf C.toCoverData.iInfImageIdeal.si
          _a0 := by
    have h := map_comp (I.comap C.pullbackFiberToBase) C.pullbackFiberToHypersurface
      C.toCoverData.iInfImageIdeal.si
    rwa [C.pullbackFiberToHypersurface_comp_subschemeio] at h
  have h3 : (imageIdealSheaf C.toCoverData.iInfImageIdeal.si
        _a0).comap
        C.toCoverData.iInfImageIdeal.si
      = _a0 :=
    p30
      C.toCoverData.iInfImageIdeal.si _a0
  rw [C.idealOnHypersurface_eq_comap, C.comapImageIdealSheaf_eq, h1, h2, h3]
end
end

end MaximalContactCover

end FunctorialResolution.EmbeddedResolution

end
end
section


namespace FunctorialResolution.EmbeddedResolution

namespace MaximalContactCover

variable {X X' : Sch} {k : Type} [Field k] {p : X' ⟶ Sp k}
  {ta_ : X ⟶ X'} {I : ISD X} {c : ℕ}

section
variable (C : MaximalContactCover p ta_ I c)
theorem comap_iInfImageIdeal_subschemeio_eq_bot :
    C.toCoverData.iInfImageIdeal.comap C.toCoverData.iInfImageIdeal.si = ⊥ :=
  by
  simp [Scheme.IdealSheafData.comap]

theorem ker_pullbackFiberToHypersurface [IsClosedImmersion ta_] :
    ker C.pullbackFiberToHypersurface =
      (ker C.pullbackFiberToTotal).comap C.toCoverData.iInfImageIdeal.subschemeι := by
  have h := ker_comp C.pullbackFiberToHypersurface C.toCoverData.iInfImageIdeal.si
  rw [C.pullbackFiberToHypersurface_comp_subschemeio] at h
  rw [h, p30]

theorem hasEtaleCoordCodim_pullbackFiberToHypersurface [IsClosedImmersion ta_] :
    HasEtaleCoordCodim (C.toCoverData.iInfImageIdeal.subschemeι ≫ C.projection ≫ p) C.pullbackFiberToHypersurface
      (c - 1) := by
  intro x
  obtain ⟨i, y, hy⟩ :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.exists_summandio_base_eq C.toCoverData $ C.pullbackFiberToTotal.base x
  have hmemU : C.pullbackFiberToTotal.base x ∈ C.toCoverData.summandOpen i := by
    rw [← hy]
    exact mem_range_self y
  have hprojmem : C.toCoverData.disjointUnionMap.base (C.pullbackFiberToTotal.base x) ∈ C.toCoverData.opens i := by
    rw [← hy]
    exact MaxContactReduction.FiniteOpenCoverWithIdeals.disjointUnionMap_summandio_mem C.toCoverData i y
  have h1 : bsM ta_ (C.pullbackFiberToBase.base x)
      = C.toCoverData.disjointUnionMap.base (C.pullbackFiberToTotal.base x) := by
    have h2 := congrArg (fun f : C.pullbackFiber ⟶ X' => bsM f x) condition
    simpa using h2
  rcases C.adapted i with ⟨-, hfar⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
  exfalso
  refine hfar (C.pullbackFiberToBase.base x) ?_
  rwa [h1]
  have hUaff :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.isAffineOpen_summandOpen C.toCoverData i $ C.isAffine i
  let _a0 := C.toCoverData.summandEtaleChart i ch
  have hH : restrictIdeal C.toCoverData.iInfImageIdeal (C.toCoverData.summandOpen i) =
      _a0.coordIdeal {j} := by
    rw [MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen C.toCoverData i,
      MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal C.toCoverData i ch {j}, hloc]
  have h2 := MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_comap_disjointUnionMap_summandOpen
    C.toCoverData i $ ker ta_
  have hZ : restrictIdeal (ker C.pullbackFiberToTotal) (C.toCoverData.summandOpen i) =
      _a0.coordIdeal S := by
    rw [C.ker_pullbackFiberToTotal, MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal C.toCoverData i ch S]
    exact tr_ h2 $ by rw [hker]
  have hb : C.toCoverData.iInfImageIdeal.subschemeι.base (C.pullbackFiberToHypersurface.base x)
      = C.pullbackFiberToTotal.base x := by
    have h4 := congrArg (fun f : C.pullbackFiber ⟶ C.toCoverData.disjointUnion => bsM f x)
      C.pullbackFiberToHypersurface_comp_subschemeio
    simpa using h4
  refine ⟨C.toCoverData.iInfImageIdeal.si ⁻¹ᵁ C.toCoverData.summandOpen i, ?_,
    n - ({j} : FinSet n).card,
    _a0.restrictToSubscheme hUaff C.toCoverData.iInfImageIdeal {j} hH,
    complEmbPreimage n S j, ?_, ?_⟩
  simp_all
  have _i36 : (complEmbPreimage n S j).card = S.card - 1 := by
    classical
    rw [← card_erase_of_mem hjS]
    refine card_bij (fun t _ => complOrderEmb n ({j} : FinSet n) t) ?_ ?_ ?_
    intro t ht
    rw [mem_complEmbPreimage] at ht
    refine mpr_ mem_erase ⟨?_, ht⟩
    intro hcontra
    exact (complOrderEmb_notMem n {j} t) (by rw [hcontra]; exact mem_singleton_self j)
    intro t1_ _ t2_ _ hEq
    exact (complOrderEmb n ({j} : FinSet n)).injective hEq
    intro b hb
    obtain ⟨hb1, hb2⟩ := mp_ mem_erase hb
    obtain ⟨t, ht⟩ := exists_complOrderEmb_eq n ({j} : FinSet n) $ by simpa using hb1
    exact ⟨t, mem_complEmbPreimage_of_complOrderEmb_eq n S j hb2 ht, ht⟩
  rw [_i36, hcard]
  rw [C.ker_pullbackFiberToHypersurface]
  exact restrictIdeal_comap_subschemeio_eq_coordIdeal (C.toCoverData.summandEtaleChart i ch)
    hUaff (ker C.pullbackFiberToTotal) C.toCoverData.iInfImageIdeal S j hZ hH

theorem isIso_pullbackFiberToHypersurface_of_eq_one [IsClosedImmersion ta_] (hc : c = 1) :
    IsIso C.pullbackFiberToHypersurface := by
  have hkey : ker C.pullbackFiberToTotal = C.toCoverData.iInfImageIdeal := by
    rw [C.ker_pullbackFiberToTotal]
    refine MaxContactReduction.FiniteOpenCoverWithIdeals.ext_of_comap_summandio C.toCoverData fun i => ?_
    have e2 : ((ker ta_).comap C.toCoverData.disjointUnionMap).comap
          (C.toCoverData.summandio i)
        = restrictIdeal (ker ta_) (C.toCoverData.opens i) := by
      rw [← comap_comp,
        MaxContactReduction.FiniteOpenCoverWithIdeals.summandio_comp_disjointUnionMap C.toCoverData i]
    rw [MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandio C.toCoverData i, e2]
    rcases C.adapted i with ⟨hloc, hfar⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
    rw [hloc]
    exact restrictIdeal_ker_eq_top_of_not_mem ta_ (C.toCoverData.opens i) hfar
    have hS : S = {j} := by
      have h1 : S.card = 1 := by rw [hcard, hc]
      obtain ⟨a, ha⟩ := mp_ card_eq_one h1
      subst ha
      rw [Finset.mem_singleton] at hjS
      rw [hjS]
    rw [hker, hloc, hS]
  refine IsClosedImmersion.isIso_iff_ker_eq_bot.mpr ?_
  rw [C.ker_pullbackFiberToHypersurface, hkey, C.comap_iInfImageIdeal_subschemeio_eq_bot]
end

end MaximalContactCover

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

section
variable {Y : Sch} {k : Type} [Field k] {q : Y ⟶ Sp k} {V : Opn Y} {m : ℕ} (c : EtaleChart q V m) (hEt : Etale ((⊤ : V.toScheme.Opens).i ≫ c.map))
def chartOnOpenSubscheme :
    EtaleChart (V.i ≫ q) (⊤ : V.toScheme.Opens) m where
  map := (⊤ : V.toScheme.Opens).i ≫ c.map
  comp_struct := by rw [assoc, c.comp_struct]
  isEtale := hEt

theorem restrictIdeal_top_coordIdeal
    S :
    restrictIdeal (c.coordIdeal S) (⊤ : V.toScheme.Opens) = (chartOnOpenSubscheme c hEt).coordIdeal S := by
  simp [restrictIdeal_eq_comap_io, coordIdeal_eq_comap_coordSubspaceIdeal]
  exact sy_ $ comap_comp _ _ _
end

theorem false_of_forall_mem_support_of_coordIdeal_singleton {Z : Sch} {k : Type} [Field k]
    (p : Z ⟶ Sp k) (hZ : IsAffineOpen (⊤ : Opn Z)) {m : ℕ}
    (c : EtaleChart p (⊤ : Opn Z) m) (j : Fin m) (D : ISD Z)
    (hD : restrictIdeal D (⊤ : Opn Z) = c.coordIdeal {j})
    (hsupp : ∀ y : ↥Z, y ∈ support D) (y0_ : ↥Z) : False := by
  have hno : ∀ y, y ∉ bOpn Z (c.coord j) := by
    intro y hy
    have hu := mp_ (Z.mem_basicOpen (c.coord j) y trivial) hy
    apply mp_ (mem_support_iff_stalkIdeal_ne_top D y) $ hsupp y
    rwa [stalkIdeal_eq_span_germ_coord p hZ c j D hD y trivial, span_singleton_eq_top]
  have hnil : IsNilpotent $ c.coord j := by
    rw [isNilpotent_iff_basicOpen_eq_bot_of_isCompact hZ.isCompact]
    refine le_antisymm ?_ bot_le
    intro y hy
    exact absurd hy $ hno y
  obtain ⟨n, hn⟩ := hnil
  have hone :=
    (mp_ mem_nonZeroDivisors_iff $ pow_mem (coord_mem_nonZeroDivisors hZ c j) n).2 1 $ by rw [one_mul, hn]
  apply mp_ (mem_support_iff_stalkIdeal_ne_top D y0_) $ hsupp y0_
  rw [stalkIdeal_eq_span_germ_coord p hZ c j D hD y0_ trivial, eq_top_iff_one]
  have hstalk1 : (1 : (stkX Z y0_)) = 0 := by
    have h := congrArg (hom $ pGerm Z (⊤) y0_ trivial) hone
    simp at h
  rw [hstalk1]
  exact m97 _

theorem nonzeroOnComponents_of_locally_eq_coordIdeal {Y : Sch} {k : Type} [Field k]
    (q : Y ⟶ Sp k) (K : ISD Y)
    (hfin : (irreducibleComponents ↥Y).Finite)
    (hloc : ∀ y : ↥Y, y ∈ support K → ∃ (U : Opn Y) (_ : y ∈ U) (m : ℕ)
      (ch : EtaleChart q U m) (S : FinSet m),
      S.Nonempty ∧ restrictIdeal K U = ch.coordIdeal S) :
    NonzeroOnComponents K := by
  rw [nonzeroOnComponents_iff]
  intro T hT hTsub
  have hTirr : IsIrreducible T := an1 hT
  have hOfin : (irreducibleComponents ↥Y \ {T}).Finite := hfin.subset sdiff_subset
  have hOclosed : IsClosed (⋃₀ (irreducibleComponents ↥Y \ {T})) := by
    rw [sUnion_eq_biUnion]
    exact isClosed_biUnion hOfin
      (fun s hs => isClosed_of_mem_irreducibleComponents s hs.1)
  let _a0 := ⋃₀ (irreducibleComponents ↥Y \ {T})
  have hOsub : ∀ z, z ∉ _a0 → z ∈ T := by
    intro z hz
    by_cases hEq : irreducibleComponent z = T
    rw [← hEq]
    exact mem_irreducibleComponent
    exact (hz (mpr_ mem_sUnion ⟨irreducibleComponent z,
      ⟨irreducibleComponent_mem_irreducibleComponents z,
        fun hmem => hEq $ Set.mem_singleton_iff.mp hmem⟩,
      mem_irreducibleComponent⟩)).elim
  obtain ⟨x, hxT, hxO⟩ :
      ∃ x, x ∈ T ∧ x ∉ _a0 := by
    by_contra hcon
    push Not at hcon
    have hsub : T ⊆ ⋃₀ ((hOfin.toFinset : Finset (Set ↥Y)) : Set (Set ↥Y)) := by
      intro t ht
      rw [coe_toFinset]
      exact hcon t ht
    obtain ⟨C, hCmem, hTsubC⟩ := mp_ isIrreducible_iff_sUnion_isClosed hTirr hOfin.toFinset
      (fun C hC => isClosed_of_mem_irreducibleComponents C (hOfin.mem_toFinset.mp hC).1) hsub
    have hC := hOfin.mem_toFinset.mp hCmem
    exact an2 hC $ Set.mem_singleton_iff.mpr (m15 (an2 hT hC.1.1 hTsubC) hTsubC)
  obtain ⟨U, hxU, m, ch, S, hSne, hKU⟩ := hloc x $ hTsub hxT
  obtain ⟨j, hjS⟩ := hSne
  obtain ⟨V, hVaff, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⟨U ∩ (⋃₀ (irreducibleComponents ↥Y \ {T}))ᶜ, U.isOpen.inter hOclosed.isOpen_compl⟩ : Opn Y) from
      ⟨hxU, hxO⟩)
  have hVsub := hVle
  have hVU : V ≤ U := fun z hz => an1 (hVsub hz)
  have : IsAffine V.toScheme := hVaff
  let _a2 := ch.restrict hVU
  have hEt : Etale (opI (⊤ : V.toScheme.Opens) ≫ _a2.map) := by
    have := _a2.isEtale
    infer_instance
  have hmemV : ∀ y, bsM (opI V) y ∈ V := by
    intro y
    have h : (bsM (opI V) y) ∈ (V : Set ↥Y) := by
      rw [← q1 V]
      exact ⟨y, rfl⟩
    exact h
  refine false_of_forall_mem_support_of_coordIdeal_singleton (opI V ≫ q) (isAffineOpen_top V.toScheme) (chartOnOpenSubscheme (ch.restrict hVU) hEt) j
    ((ch.restrict hVU).coordIdeal ({j} : FinSet m))
    (restrictIdeal_top_coordIdeal (ch.restrict hVU) hEt ({j} : FinSet m)) ?_ (⟨x, hxV⟩ : ↥V)
  intro y
  have hmem := hTsub (hOsub _ $ (fun z hz => an2 (hVsub hz)) _ (hmemV y))
  have h2 : y ∈ (spI (cmI K V.i) : Set ↥V.toScheme) := by
    rwa [support_comap_eq V.i K]
  have h3 : y ∈ spI (_a2.coordIdeal S) := by
    rwa [← restrictIdeal_eq_restrict_coordIdeal_of_le hVU ch K S hKU, restrictIdeal_eq_comap_io]
  rw [← one_le_orderAt_iff_mem_support] at h3 ⊢
  exact le_trans h3 (orderAt_le_of_le
    (_a2.coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)) y)

namespace MaximalContactCover

variable {X X' : Sch} {k : Type} [Field k] {p : X' ⟶ Sp k}
  {ta_ : X ⟶ X'} {I : ISD X} {c : ℕ}

section
variable (C : MaximalContactCover p ta_ I c)
abbrev hypersurfaceScheme : Sch :=
  C.toCoverData.iInfImageIdeal.subscheme

abbrev hypersurfaceStructureMap :
    C.hypersurfaceScheme ⟶ Sp k :=
  C.toCoverData.iInfImageIdeal.subschemeι ≫ C.projection ≫ p

theorem smooth_hypersurfaceStructureMap :
    Smooth C.hypersurfaceStructureMap :=
  (mp_ (isSmoothDivisor_iff (C.projection ≫ p) C.toCoverData.iInfImageIdeal)
    C.isSmoothDivisor_iInfImageIdeal).2





theorem nonzeroOnComponents_iInfImageIdeal
    [NoetherianSpace ↥C.toCoverData.disjointUnion] :
    NonzeroOnComponents C.toCoverData.iInfImageIdeal := by
  refine nonzeroOnComponents_of_locally_eq_coordIdeal (C.projection ≫ p) C.toCoverData.iInfImageIdeal
    m169 ?_
  intro y hy
  obtain ⟨i, hi⟩ := C.toCoverData.exists_mem_summandOpen y
  rcases C.hypersurface i with htop | ⟨n, ch, j, hch⟩
  exfalso
  refine notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ _ ?_ y hi hy
  rw [MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen, htop]
  simp
  refine ⟨C.toCoverData.summandOpen i, hi, n, C.toCoverData.summandEtaleChart i ch, {j},
    ⟨j, mem_singleton_self j⟩, ?_⟩
  rw [MaxContactReduction.FiniteOpenCoverWithIdeals.restrictIdeal_iInfImageIdeal_summandOpen, hch,
    MaxContactReduction.FiniteOpenCoverWithIdeals.summandEtaleChart_coordIdeal]

section
variable [hv1_0 : IsClosedImmersion ta_]
include hv1_0
theorem ker_pullbackFiberToHypersurface_le_idealOnHypersurface :
    ker C.pullbackFiberToHypersurface ≤ C.idealOnHypersurface := by
  rw [C.idealOnHypersurface_eq_imageIdealSheaf]
  exact ker_le_map_idealSheaf C.pullbackFiberToHypersurface $ cmI I C.pullbackFiberToBase

theorem support_idealOnHypersurface_subset_support_ker :
    (C.idealOnHypersurface.support : Set ↥C.hypersurfaceScheme) ⊆
      (support (ker C.pullbackFiberToHypersurface) : Set ↥C.hypersurfaceScheme) := by
  intro x hx
  have hx' : x ∈ C.idealOnHypersurface.support := hx
  rw [mem_support_iff_stalkIdeal_ne_top] at hx'
  show x ∈ spI (ker C.pullbackFiberToHypersurface)
  rw [mem_support_iff_stalkIdeal_ne_top]
  intro hker
  have h1 := stalkIdeal_mono (ker_pullbackFiberToHypersurface_le_idealOnHypersurface C) x
  rw [hker, top_le_iff] at h1
  exact hx' h1

section
variable [NoetherianSpace ↥C.hypersurfaceScheme] (hloc : ∀ x : ↥C.pullbackFiber, ∃ (W : C.hypersurfaceScheme.Opens) (_ : C.pullbackFiberToHypersurface.base x ∈ W) (m : ℕ) (ch : EtaleChart C.hypersurfaceStructureMap W m) (S : FinSet m), S.Nonempty ∧ restrictIdeal (ker C.pullbackFiberToHypersurface) W = ch.coordIdeal S)
include hloc
theorem nonzeroOnComponents_ker_pullbackFiberToHypersurface :
    NonzeroOnComponents $ ker C.pullbackFiberToHypersurface := by
  refine nonzeroOnComponents_of_locally_eq_coordIdeal C.hypersurfaceStructureMap (ker C.pullbackFiberToHypersurface)
    m169 ?_
  intro y hy
  obtain ⟨x, hx⟩ : ∃ x, C.pullbackFiberToHypersurface.base x = y := by
    have hr : (spI (ker C.pullbackFiberToHypersurface) : Set C.hypersurfaceScheme)
        = range (C.pullbackFiberToHypersurface) := by
      rw [support_ker]
      exact (isClosedEmbedding
        C.pullbackFiberToHypersurface).isClosed_range.closure_eq
    have hy' : y ∈ range (C.pullbackFiberToHypersurface) := by
      rwa [← hr]
    exact hy'
  obtain ⟨W, hW, m, ch, S, hS, hres⟩ := hloc x
  exact ⟨W, hx ▸ hW, m, ch, S, hS, hres⟩

theorem nonzeroOnComponents_idealOnHypersurface :
    NonzeroOnComponents C.idealOnHypersurface := by
  have hker := C.nonzeroOnComponents_ker_pullbackFiberToHypersurface hloc
  rw [nonzeroOnComponents_iff] at hker ⊢
  intro T hT hTsub
  exact hker T hT $ hTsub.trans $ C.support_idealOnHypersurface_subset_support_ker
end
end

theorem krullDimSucc_hypersurfaceScheme_lt
    [LocallyOfFiniteType p]
    [NoetherianSpace ↥C.toCoverData.disjointUnion]
    [Nonempty ↥C.hypersurfaceScheme] :
    krullDimSucc C.hypersurfaceScheme < krullDimSucc C.toCoverData.disjointUnion := by
  refine krullDimSucc_lt_of_isClosedImmersion_of_nonzeroOnComponents (C.projection ≫ p)
    C.toCoverData.iInfImageIdeal.si ?_
  rw [q2]
  exact C.nonzeroOnComponents_iInfImageIdeal
end

end MaximalContactCover

end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

section

variable (k : Type) [Field k] {P1 : Sch} (q)
  [LocallyOfFiniteType q]

def IsMaxContactHypersurfaceAt (A1_ : ISD P1) (m : ℕ) (H1_ : ISD P1) (x : P1) : Prop :=
  ∃ U : Opn P1, IsAffineOpen U ∧ x ∈ U ∧
    ((Disjoint (orderAtLeastLocus A1_ m) (U : Set ↥P1) ∧ restrictIdeal H1_ U = ⊤) ∨
      (∃ (n : ℕ) (c : EtaleChart q U n) (j : Fin n),
        restrictIdeal H1_ U = c.coordIdeal {j} ∧ IsMaxContactCoord k q A1_ m c j))

end

section

section
variable {X : Sch}
theorem mul_le_right_idealSheafData (I J : ISD X) :
    I * J ≤ J := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact mul_le.2 fun r _ s hs => mul_mem_left _ _ hs

theorem restrictIdeal_le_of_le_opens {I J : ISD X}
    {U V : Opn X} (hVU : V ≤ U) (h : restrictIdeal I U ≤ restrictIdeal J U) :
    restrictIdeal I V ≤ restrictIdeal J V := by
  have hI : ∀ K,
      restrictIdeal K V = (restrictIdeal K U).comap (X.homOfLE hVU) := by
    intro K
    rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
      Scheme.homOfLE_ι]
  rw [hI I, hI J]
  exact comap_mono _ h
end

theorem saturation_of_eq_top {Y : Sch} (F T : ISD Y)
    (hqc : QuasiCompact $ saturationio F T) (hF : F = ⊤) :
    saturation F T = T := by
  refine m29 $ funext fun V => ?_
  refine saturation_ideal_eq_of_isUnit F T V 1 ?_ isUnit_one
  rw [hF]
  simp

section
variable {P P1 : Sch}
section
variable {k : Type} [Field k] {p : P ⟶ Sp k} (pi_ : P1 ⟶ P) {V : Opn P} {n : ℕ} (c : EtaleChart p V n) [IsIso (pi_.mr V)]
noncomputable def etaleChartPullbackOfIsIso : EtaleChart (pi_ ≫ p) (pre pi_ V) n where
  map := (pi_.mr V) ≫ c.map
  comp_struct := by
    rw [assoc, c.comp_struct, ← assoc, morphismRestrict_ι, assoc]
  isEtale := by
    have := c.isEtale
    infer_instance

theorem pullbackChartIso_coordIdeal T :
    (etaleChartPullbackOfIsIso pi_ c).coordIdeal T = (c.coordIdeal T).comap (pi_.mr V) := by
  rw [coordIdeal_eq_comap_coordSubspaceIdeal, coordIdeal_eq_comap_coordSubspaceIdeal]
  show (coordSubspaceIdeal k n T).comap ((mrU pi_ V) ≫ c.map) = _
  rw [comap_comp]
end
end

section
variable {k : Type} [Field k] {X : Sch} (p) [LocallyOfFiniteType p] [Smooth p] (A) (mu_) (H) (hH : IsMaxContactHypersurface k p A mu_ H)
include hH
theorem exists_etaleChart_of_isMaxContactHypersurface (x : X) :
    ∃ (U : Opn X) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal H U = ⊤ ∨ ∃ j, restrictIdeal H U = c.coordIdeal {j} := by
  obtain ⟨U, hU, hxU, hcase⟩ := hH x
  rcases hcase with ⟨-, htop⟩ | ⟨n, c, j, hHU, -⟩
  obtain ⟨V, nV, hxV, hVU, hVaff, ⟨cV⟩⟩ := exists_etaleChart_le p x U hxU
  exact ⟨V, hxV, nV, cV, inl $ restrictIdeal_eq_top_of_le H hVU htop⟩
  exact ⟨U, hxU, n, c, inr ⟨j, hHU⟩⟩

end

section
variable (k : Type) [Field k] [CharZero k]
section
variable {P P1 : Sch} (p : P ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] (pi_ : P1 ⟶ P) [IsLocallyNoetherian P1] [Smooth (pi_ ≫ p)] [LocallyOfFiniteType (pi_ ≫ p)] (Z : ISD P) (E : Bdy P) (hZ : HasStrictNormalCrossingsWith p Z E) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (A : ISD P) (A1_ : ISD P1) (mu_ : ℕ) (hmu_ : 1 ≤ mu_) (hA : A ≤ Z ^ mu_) (htr : exceptionalIdeal pi_ Z ^ mu_ * A1_ = A.comap pi_)
include hZ hpi_ hmu_ hA htr
theorem comap_maxContactIdeal_le_exceptionalIdeal_mul :
    (maxContactIdeal k p A mu_).comap pi_ ≤
      exceptionalIdeal pi_ Z * maxContactIdeal k (pi_ ≫ p) A1_ mu_ := by
  have h :=
    comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p pi_ Z E hZ hpi_ A mu_ hA (mu_ - 1)
      (sub_le mu_ 1)
  rw [symm $ eq_controlledTransform_of_mul_eq_comap pi_ Z A mu_ hpi_ hA A1_ htr] at h
  have hmu1_ : mu_ - (mu_ - 1) = 1 := by omega
  rw [hmu1_, pow_one] at h
  rwa [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate]

end

section
variable {P P1 : Sch} (p : P ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] (pi_ : P1 ⟶ P) [IsLocallyNoetherian P1]
section
variable [Smooth (pi_ ≫ p)] [LocallyOfFiniteType (pi_ ≫ p)] (Z : ISD P) (E : Bdy P) (hZ : HasStrictNormalCrossingsWith p Z E) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (A : ISD P) (A1_ : ISD P1) (mu_ : ℕ) (hmu_ : 1 ≤ mu_)
include hZ hpi_ hmu_
theorem isMaxContactHypersurfaceAt_strictTransform_of_etaleChart (hA : A ≤ Z ^ mu_)
    (htr : exceptionalIdeal pi_ Z ^ mu_ * A1_ = A.comap pi_) (H : ISD P)
    [QuasiCompact $ strictTransformio pi_ Z H] {U' : Opn P} (hU' : IsAffineOpen U')
    {m : ℕ} (c : EtaleChart p U' m) (S : FinSet m) (j0_ : Fin m) (hj0_ : j0_ ∈ S)
    (hZU : restrictIdeal Z U' = c.coordIdeal S)
    (hHU : restrictIdeal H U' = c.coordIdeal {j0_})
    (hcoord : c.coord j0_ ∈ (maxContactIdeal k p A mu_).ideal ⟨U', hU'⟩)
    (x1_ : P1) (hx1_ : x1_ ∈ pre pi_ U') :
    IsMaxContactHypersurfaceAt k (pi_ ≫ p) A1_ mu_ (strictTransform pi_ Z H) x1_ := by
  let _a3 := pi_ ≫ p
  let _c0 := maxContactIdeal k _a3 A1_ mu_
  classical
  obtain ⟨s, hs, hx1D⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZU x1_ hx1_
  set B := blowupChartOfIsBlowup pi_ c S hpi_ hZU s hs with hBdef
  obtain ⟨V, _, hxV, hVD, hVaff, -⟩ :=
    exists_etaleChart_le _a3 x1_ B.domain hx1D
  have hcart : p17 $ B.chart.coordIdeal {s} := by
    exact isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal (p := B.domain.i ≫ _a3) _ fun x => ⟨⊤, trivial, m, B.chart.restrictOpens ⊤, inr ⟨s, B.chart.restrictIdeal_coordIdeal ⊤ {s}⟩⟩
  have key : restrictIdeal (cmI H pi_) B.domain ≤
      B.chart.coordIdeal {s} * restrictIdeal _c0 B.domain := by
    let _a0 := maxContactIdeal k p A mu_
    have h1 : restrictIdeal (cmI H pi_) B.domain
        ≤ restrictIdeal (cmI _a0 pi_) B.domain := by
      rw [B.restrictIdeal_comap H, B.restrictIdeal_comap _a0]
      refine comap_mono _ ?_
      rw [hHU]
      exact (coordIdeal_singleton_le_restrictIdeal_iff k p hU' c j0_
        _a0).2 hcoord
    let _a1 := restrictIdeal (p5 pi_ Z * maxContactIdeal k _a3 A1_ mu_) B.domain
    have h2 : restrictIdeal (cmI _a0 pi_) B.domain ≤
        _a1 :=
      comap_mono _
        (comap_maxContactIdeal_le_exceptionalIdeal_mul k p pi_ Z E hZ hpi_ A A1_ mu_ hmu_ hA htr)
    have hmul : _a1 =
        restrictIdeal (p5 pi_ Z) B.domain *
          restrictIdeal _c0 B.domain :=
      comap_mul _ _ _
    rw [hmul, B.restrictIdeal_exceptionalIdeal Z hs hZU] at h2
    exact h1.trans h2
  by_cases hj : j0_ = s
  have hHU' : restrictIdeal H U' = c.coordIdeal {s} := by rw [hHU, hj]
  have hcomap :=
    B.restrictIdeal_comap_coordIdeal_self H hHU'
  have hST :=
    B.restrictIdeal_strictTransform_coordIdeal_self Z H hs hZU hHU'
  have htop : restrictIdeal _c0 B.domain = ⊤ := by
    refine top_le_iff.1 $ hcart.le_of_mul_le_mul ?_
    rw [mul_top]
    exact le_trans (le_of_eq hcomap.symm) key
  refine ⟨V, hVaff, hxV, inl ⟨?_, restrictIdeal_eq_top_of_le _ hVD hST⟩⟩
  rw [disjoint_left]
  intro x hxc hxV
  exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ B.domain htop x (hVD hxV) $ mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k _a3 A1_ hmu_ hxc
  have hcomap :=
    B.restrictIdeal_comap_coordIdeal_of_mem H j0_ hj0_ hj hHU
  have hST :=
    B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZU j0_ hj0_ hj hHU
  have hmc : B.chart.coordIdeal {j0_} ≤
      restrictIdeal _c0 B.domain := by
    refine hcart.le_of_mul_le_mul ?_
    rw [mul_comm (B.chart.coordIdeal {s}) $ B.chart.coordIdeal {j0_}]
    exact le_trans (le_of_eq hcomap.symm) key
  let _a2 := p6 pi_ Z H
  have hSTV :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVD B.chart _a2 {j0_} hST
  refine ⟨V, hVaff, hxV, inr ⟨m, B.chart.restrict hVD, j0_, hSTV, ?_⟩⟩
  show (B.chart.restrict hVD).coordIdeal {j0_} ≤
    restrictIdeal _c0 V
  have h4 : restrictIdeal _a2 B.domain ≤
      restrictIdeal _c0 B.domain := by
    rwa [hST]
  have h5 := restrictIdeal_le_of_le_opens hVD h4
  rwa [← hSTV]

theorem isMaxContactHypersurfaceAt_strictTransform_of_mem_support
    (hsupp : (support Z : Set ↥P) ⊆ orderAtLeastLocus A mu_) (hA : A ≤ Z ^ mu_)
    (htr : exceptionalIdeal pi_ Z ^ mu_ * A1_ = A.comap pi_) (H : ISD P)
    [QuasiCompact $ strictTransformio pi_ Z H]
    (hH : IsMaxContactHypersurface k p A mu_ H) (x1_ : P1) (hx1_ : pi_.base x1_ ∈ support Z) :
    IsMaxContactHypersurfaceAt k (pi_ ≫ p) A1_ mu_ (strictTransform pi_ Z H) x1_ := by
  classical
  have hsm :=
    smooth_subschemeio_comp_of_hasStrictNormalCrossingsWith Z E hZ
  have hHZ : H ≤ Z := by
    have h1 :=
      hsupp.trans $ hH.orderAtLeastLocus_subset_support hmu_
    have h2 : suppI Z ⊆ orderAtLeastLocus H 1 := by
      intro x hx
      rw [mem_orderAtLeastLocus_one_iff]
      exact h1 hx
    have h3 := le_pow_of_hasStrictNormalCrossingsWith p Z H E hZ 1 h2
    rwa [pow_one] at h3
  have hsnc : InStrictNormalCrossingPosition p [H] := by
    rw [inStrictNormalCrossingPosition_iff]
    constructor
    intro D hD
    simp at hD
    subst hD
    exact isSmoothDivisor_of_locally_coordIdeal D
      (exists_etaleChart_of_isMaxContactHypersurface p A mu_ D hH)
    intro x
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ?_
    obtain ⟨U, hxU, n, c, hcase⟩ := exists_etaleChart_of_isMaxContactHypersurface p A mu_ H hH x
    rcases hcase with htop | ⟨j, hj⟩
    refine ⟨U, hxU, n, c, fun _ => none, ?_, ?_, ?_⟩
    simp_all
    simp_all
    simp_all
    refine ⟨U, hxU, n, c, fun i => match i with | 0 => some j | _ => none, ?_, ?_, ?_⟩
    simp_all
    simp_all
    simp_all
  obtain ⟨U, hU, hzU, m, c, lab, S, m', c', j0, lab', hZU, hHU, hlab, _, hlab', hj0⟩ :=
    exists_etaleCharts_of_inStrictNormalCrossingPosition_cons p Z H [] hsnc (hasStrictNormalCrossingsWith_nil_of_smooth p Z) hHZ (pi_.base x1_) hx1_
  have hSprime : ∀ i ∈ S, c.coord i ∈ (hU.primeIdealOf ⟨pi_.base x1_, hzU⟩).asIdeal := by
    intro i hi
    have h1 :=
      c.ideal_eq_span_coord hU Z S hZU
    have h2 : c.coord i ∈ Z.ideal ⟨U, hU⟩ := by
      rw [h1]
      exact subset_span ⟨i, hi, rfl⟩
    exact ideal_le_primeIdealOf Z hU hzU hx1_ h2
  obtain ⟨a, hcoeff, j, hjS, haj, -⟩ :=
    exists_coord_eq_sum_coeff_not_mem_of_le p hU hzU c lab S c' j0 lab' Z H [] hx1_ hlab hZU hHU hlab'
      hj0 hHZ
  obtain ⟨V, hV, hVU, hzV, cV, hcne, hcj, huj⟩ :=
    exists_etaleChart_update_coord p hU c hzU S a j hjS hSprime haj
  have hZV : restrictIdeal Z V = cV.coordIdeal S := by
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV cV Z S ?_
    have h1 :=
      c.ideal_eq_span_coord hU Z S hZU
    rw [ideal_eq_span_image_map_of_le Z hU hV hVU (c.coord '' (S : Set $ Fin m)) h1, image_image]
    rw [← span_image_update_sum_eq
      (fun i => (pMap P (homOfLE hVU).op).hom $ c.coord i) S
      (fun i => (pMap P (homOfLE hVU).op).hom $ a i) j hjS huj]
    congr 1
    refine image_congr ?_
    intro i hi
    by_cases hij : i = j
    simp_all
    simp_all
  have hHV : restrictIdeal H V = cV.coordIdeal {j} := by
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV cV H {j} ?_
    have h1 :=
      c'.ideal_eq_span_coord hU H {j0} hHU
    have hone : (pMap P (homOfLE hVU).op).hom (c'.coord j0) = cV.coord j := by
      rw [hcoeff, hcj]
    rw [ideal_eq_span_image_map_of_le H hU hV hVU _ h1]
    simp [coe_singleton, image_singleton, hone]
  obtain ⟨W, hW, hzW, hcase⟩ := hH $ pi_.base x1_
  let _a0 := maxContactIdeal k p A mu_
  have hHmc : restrictIdeal H W ≤ restrictIdeal _a0 W := by
    rcases hcase with ⟨hdisj, -⟩ | ⟨nW, cW, jW, hHW, hmcW⟩
    exact absurd hzW $ Set.disjoint_left.mp hdisj $ hsupp hx1_
    rwa [hHW]
  obtain ⟨V', _, hzV', hV'le, hV'aff, -⟩ :=
    exists_etaleChart_le p (pi_.base x1_) (V ⊓ W) ⟨hzV, hzW⟩
  have hV'V : V' ≤ V := fun y hy => an1 $ hV'le hy
  have hZV' :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V cV Z S hZV
  have hHV' :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V cV H {j} hHV
  have hcoordmem := by
    refine (coordIdeal_singleton_le_restrictIdeal_iff k p hV'aff (cV.restrict hV'V) j
      _a0).1 ?_
    rw [← hHV']
    exact restrictIdeal_le_of_le_opens (fun y hy => an2 $ hV'le hy) hHmc
  exact isMaxContactHypersurfaceAt_strictTransform_of_etaleChart k p pi_ Z E hZ hpi_ A A1_ mu_ hmu_ hA htr H
    hV'aff (cV.restrict hV'V) S j hjS hZV' hHV' hcoordmem x1_ hzV'

end

section
variable [LocallyOfFiniteType (pi_ ≫ p)] (Z : ISD P) (E : Bdy P) (hZ : HasStrictNormalCrossingsWith p Z E) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (A : ISD P) (A1_ : ISD P1) (mu_ : ℕ) (hmu_ : 1 ≤ mu_)
include hZ hpi_ hmu_
theorem isMaxContactHypersurface_strictTransform_of_orderAt_le
    (_hord : ∀ x : P, orderAt A x ≤ (mu_ : ENat))
    (hsupp : (Z.support : Set ↥P) ⊆ orderAtLeastLocus A mu_)
    (htr : exceptionalIdeal pi_ Z ^ mu_ * A1_ = A.comap pi_) (H : ISD P) :
    IsMaxContactHypersurface k p A mu_ H →
      IsMaxContactHypersurface k (pi_ ≫ p) A1_ mu_ (strictTransform pi_ Z H) := by
  intro hH
  have := smooth_comp_of_isBlowupAlongIdealSheaf hZ hpi_
  have hA := le_pow_of_hasStrictNormalCrossingsWith p Z A E hZ mu_ hsupp
  intro x1_
  by_cases hx : bsM pi_ x1_ ∈ Z.support
  exact isMaxContactHypersurfaceAt_strictTransform_of_mem_support k p pi_ Z E hZ hpi_ A A1_ mu_ hmu_ hsupp hA
    htr H hH x1_ hx
  let hx1_ := hx
  let _a3 := p6 pi_ Z H
  classical
  obtain ⟨U, hU, hxU, hcase⟩ := hH $ bsM pi_ x1_
  obtain ⟨V, _, hxV, hVle, hVaff, -⟩ :=
    exists_etaleChart_le p (bsM pi_ x1_) (U ⊓ (suppC Z)) ⟨hxU, hx1_⟩
  have hVU : V ≤ U := fun y hy => an1 $ hVle hy
  have hx1V := hxV
  have hrestrict : ∀ K : ISD P,
      restrictIdeal (K.comap pi_) (pre pi_ V) = (restrictIdeal K V).comap (pi_.mr V) := by
    intro K
    rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
      ← comap_comp, morphismRestrict_ι]
  let _a5 := (pre pi_ V).i ≫ pi_
  have hZtop : Z.comap _a5 = ⊤ := by
    rw [m56]
    refine p39 _ (Z.comap pi_) fun y => ?_
    show (y.1 : P1) ∉ (Z.comap pi_).support
    have hy := y.2
    rw [m19]
    exact an2 $ hVle hy
  have hST : restrictIdeal (p6 pi_ Z H) (pre pi_ V) = restrictIdeal (H.comap pi_) (pre pi_ V) := by
    let _c0 := _a5
    have hqc : QuasiCompact $ saturationio (Z.comap _c0)
        (H.comap _c0) := by
      rw [← strictTransformio_eq_saturationio]
      exact quasiCompact_strictTransformio_comp_io pi_ Z H $ pre pi_ V
    have hsat : strictTransform _c0 Z H = H.comap _c0 := by
      rw [strictTransform_eq_saturation]
      exact saturation_of_eq_top _ _ hqc hZtop
    rw [restrictIdeal_strictTransform pi_ Z H $ pre pi_ V, hsat, restrictIdeal_eq_comap_io,
      comap_comp]
  rcases hcase with ⟨hdisj, hHtop⟩ | ⟨n, c, j0_, hHU, hmc⟩
  obtain ⟨V1, _, hx1V1, hV1le, hV1aff, -⟩ :=
    exists_etaleChart_le (pi_ ≫ p) x1_ (pre pi_ V) hx1V
  refine ⟨V1, hV1aff, hx1V1, inl ⟨?_, ?_⟩⟩
  rw [disjoint_left]
  intro y hy hyV
  have h1 : bsM pi_ y ∈ orderAtLeastLocus A mu_ := by
    by_contra hcon
    have hsucc : mu_ - 1 + 1 = mu_ := by omega
    have hz := hcon
    rw [← hsucc, ← orderAt_le_iff_notMem_orderAtLeastLocus] at hz
    let _a0 := mu_ - 1
    have hA' : A ≤ Z ^ _a0 := by
      refine le_trans hA ?_
      have hpow : Z ^ mu_ = Z ^ _a0 * Z := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow, le_iff_forall_stalkIdeal_le]
      intro x
      rw [stalkIdeal_mul]
      exact mul_le.2 fun r hr s _ => mul_mem_right _ _ hr
    let _a1 := p5 pi_ Z
    have hEA : _a1 * A1_ = controlledTransform pi_ Z A (mu_ - 1) hpi_ hA' := by
      refine eq_controlledTransform_of_mul_eq_comap pi_ Z A (mu_ - 1) hpi_ hA' _ ?_
      calc _a1 ^ _a0 * (_a1 * A1_)
          = _a1 ^ (mu_ - 1 + 1) * A1_ := by rw [pow_succ, mul_assoc]
        _ = A.comap pi_ := by rw [hsucc]
                              exact htr
    have h1 := orderAt_controlledTransform_le k p pi_ Z E hZ hpi_ A (mu_ - 1) hA' (bsM pi_ y) hz y rfl
    rw [← hEA] at h1
    have h2 := le_trans (orderAt_le_of_le (mul_le_right_idealSheafData _ _) y) h1
    rw [orderAt_le_iff_notMem_orderAtLeastLocus, hsucc] at h2
    exact h2 hy
  have h2 := hV1le hyV
  exact (Set.disjoint_left.mp hdisj h1) $ hVU h2
  have h3 :=
    restrictIdeal_comap_preimage_eq_top pi_ V H $ restrictIdeal_eq_top_of_le H hVU hHtop
  have h4 : restrictIdeal _a3 (pre pi_ V) = ⊤ := by rw [hST, h3]
  exact restrictIdeal_eq_top_of_le _ hV1le h4
  have hHV :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c H {j0_} hHU
  have hZV : Z.comap V.i = ⊤ := by
    refine p39 V.i Z fun y => ?_
    show (y.1 : P) ∉ Z.support
    exact an2 $ hVle y.2
  have hbiso : IsIso $ pi_.mr V := by
    have hb := hpi_.restrict V
    rw [hZV] at hb
    exact hb.isIso_of_top
  let _a0 := etaleChartPullbackOfIsIso pi_ $ c.restrict hVU
  have hSTV : restrictIdeal _a3 (pre pi_ V) =
      _a0.coordIdeal {j0_} := by
    rw [hST, hrestrict H, hHV, pullbackChartIso_coordIdeal]
  let _a2 := maxContactIdeal k (pi_ ≫ p) A1_ mu_
  have hmcV : _a0.coordIdeal {j0_} ≤
      restrictIdeal _a2 (pre pi_ V) := by
    let _a1 := maxContactIdeal k p A mu_
    have h1 : restrictIdeal H V ≤ restrictIdeal _a1 V := by
      refine restrictIdeal_le_of_le_opens hVU ?_
      rwa [hHU]
    have h2 : _a0.coordIdeal {j0_} ≤
        restrictIdeal (_a1.comap pi_) (pre pi_ V) := by
      rw [pullbackChartIso_coordIdeal, hrestrict _a1, ← hHV]
      exact comap_mono _ h1
    refine h2.trans ?_
    refine comap_mono _ ?_
    exact le_trans (comap_maxContactIdeal_le_exceptionalIdeal_mul k p pi_ Z E hZ hpi_ A A1_ mu_ hmu_ hA htr) $ mul_le_right_idealSheafData _ _
  obtain ⟨V1, _, hx1V1, hV1le, hV1aff, -⟩ :=
    exists_etaleChart_le (pi_ ≫ p) x1_ (pre pi_ V) hx1V
  have hSTV1 :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV1le _a0
      _a3 {j0_} hSTV
  refine ⟨V1, hV1aff, hx1V1,
    inr ⟨n, _a0.restrict hV1le, j0_, hSTV1, ?_⟩⟩
  show (_a0.restrict hV1le).coordIdeal {j0_} ≤
    restrictIdeal _a2 V1
  have h4 := hmcV
  rw [← hSTV] at h4
  have h5 := restrictIdeal_le_of_le_opens hV1le h4
  rwa [← hSTV1]
end
end
end

end


section
variable {X : Sch}
theorem mul_le_mul_idealSheafData {A B C D : ISD X}
    (h1 : A ≤ B) (h2 : C ≤ D) : A * C ≤ B * D := by
  intro U
  rw [ideal_mul, ideal_mul]
  exact mul_mono (h1 U) $ h2 U

theorem idealSheafData_pow_antitone_of_le (I : ISD X) {a b : ℕ}
    (h : b ≤ a) : I ^ a ≤ I ^ b := by
  intro U
  rw [ideal_pow, ideal_pow]
  exact pow_le_pow_right h

theorem idealSheafData_pow_le_self (I : ISD X) {c : ℕ}
    (hc : 1 ≤ c) : I ^ c ≤ I := by
  intro U
  rw [ideal_pow]
  exact pow_le_self $ by omega

theorem listProd_map_le_listProd_map (f g : ℕ → ISD X) :
    ∀ L : List ℕ, (∀ j ∈ L, f j ≤ g j) → (L.map f).prod ≤ (L.map g).prod := by
  intro L
  induction L with
  | nil =>
      intro _
      exact le_rfl
  | cons a L ih =>
      intro h
      simp [map_cons, prod_cons]
      exact mul_le_mul_idealSheafData (h a $ by simp) $ ih fun j hj => h j $ by simp [hj]

theorem listProd_map_range_one (f : ℕ → ISD X) :
    ((List.range 1).map f).prod = f 0 :=by simp_all
end

section
variable (k : Type) [Field k]
section
variable [IsNoetherianRing k] {X : Sch} (p) [LocallyOfFiniteType p] (I : ISD X)
theorem prod_pow_derivIdealSheafIterate_le_tunedSheaf m s (c : ℕ → ℕ)
    (hc : s ≤ ∑ j ∈ Finset.range m, (m - j) * c j) :
    ((List.range m).map fun j => derivIdealSheafIterate k p j I ^ c j).prod ≤
      tunedSheaf k p I m s := by
  rw [tunedSheaf_eq_iSup]
  exact le_iSup (fun c : {c : ℕ → ℕ // s ≤ ∑ j ∈ m65 m, (m - j) * c j} =>
    ((m127 m).map fun j => derivIdealSheafIterate k p j I ^ (c.1 j)).prod) ⟨c, hc⟩

theorem tunedSheaf_one_one :
    tunedSheaf k p I 1 1 = I := by
  let _a0 := m127 1
  rw [tunedSheaf_eq_iSup]
  refine le_antisymm (iSup_le ?_) ?_
  rintro ⟨c, hc⟩
  have hc1 : 1 ≤ c 0 := by simpa using hc
  have key : (_a0.map fun j => derivIdealSheafIterate k p j I ^ c j).prod ≤ I := by
    rw [listProd_map_range_one]
    exact idealSheafData_pow_le_self I hc1
  exact key
  have key : I ≤ (_a0.map
      (fun j => derivIdealSheafIterate k p j I ^ ((fun _ => 1) j))).prod := by
    rw [listProd_map_range_one]
    exact le_of_eq (pow_one I).symm
  exact le_trans key $ le_iSup
    (fun c : {c : ℕ → ℕ // 1 ≤ ∑ j ∈ m65 1, (1 - j) * c j} =>
      (_a0.map fun j => derivIdealSheafIterate k p j I ^ (c.1 j)).prod)
    ⟨fun _ => 1, by simp⟩

theorem balancedTunedSheaf_one :
    balancedTunedSheaf k p I 1 = I := by
  rw [balancedTunedSheaf_eq, tuningExponent_one, tunedSheaf_one_one]
end

theorem balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty [CharZero k]
    [IsNoetherianRing k] {X : Sch} p
    [Smooth p] [LocallyOfFiniteType p] I {m}
    (hm : 1 ≤ m) (h : orderAtLeastLocus I m = (∅ : Set X)) :
    balancedTunedSheaf k p I m = ⊤ := by
  rw [balancedTunedSheaf_eq]
  let s := tuningExponent m
  classical
  have hm1 : m - 1 + 1 = m := by omega
  have htop :=
    derivIdealSheafIterate_eq_top_of_orderAtLeastLocus_eq_empty k p I (m - 1) (by rw [hm1]; exact h)
  have hmem : m - 1 ∈ m65 m := mpr_ mem_range $ by omega
  have hm2 : m - (m - 1) = 1 := by omega
  have heq : ∑ j ∈ m65 m, (m - j) * (if j = m - 1 then s else 0)
      = (m - (m - 1)) * (if m - 1 = m - 1 then s else 0) :=
    sum_eq_single (m - 1) (fun b _ hb => by rw [if_neg hb, mul_zero])
      (absurd hmem)
  have h3 : (m - (m - 1)) * (if m - 1 = m - 1 then s else 0) = s := by simp [hm2]
  let _a1 := m127 m
  have hprod : (_a1.map fun j => derivIdealSheafIterate k p j I ^
      (if j = m - 1 then s else 0)).prod = ⊤ := by
    have h1 : (_a1.map fun j => derivIdealSheafIterate k p j I ^
        (if j = m - 1 then s else 0)).prod = 1 := by
      refine prod_eq_one ?_
      intro x hx
      rw [mem_map] at hx
      obtain ⟨j, -, rfl⟩ := hx
      by_cases hj : j = m - 1
      subst hj
      rw [htop, ← Scheme.IdealSheafData.one_eq_top, one_pow]
      rw [if_neg hj, pow_zero]
    rw [h1, Scheme.IdealSheafData.one_eq_top]
  rw [tunedSheaf_eq_iSup]
  exact mp_ top_le_iff $ le_trans (le_of_eq hprod.symm)
    (le_iSup (fun c : {c : ℕ → ℕ // s ≤ ∑ j ∈ m65 m, (m - j) * c j} =>
      (_a1.map fun j => derivIdealSheafIterate k p j I ^ (c.1 j)).prod)
      ⟨fun j => if j = m - 1 then s else 0, (tr_ heq h3).ge⟩)
end

section
variable (m s : ℕ)
section
variable (t : Fin m → Fin (s + 1)) (j : ℕ)
def extendExponentsByZero : ℕ :=
  if h : j < m then (t ⟨j, h⟩ : ℕ) else 0

end

end

section
variable (k : Type) [Field k] [IsNoetherianRing k]
theorem tunedSheaf_eq_iSup_fin
    {X : Sch} (p : X ⟶ Sp k) [LocallyOfFiniteType p]
    (I : ISD X) (m s : ℕ) :
    tunedSheaf k p I m s =
      ⨆ t : {t : Fin m → Fin (s + 1) //
          s ≤ ∑ j ∈ Finset.range m, (m - j) * extendExponentsByZero m s t j},
        ((List.range m).map
          (fun j => derivIdealSheafIterate k p j I ^ extendExponentsByZero m s t.1 j)).prod := by
  let _a0 := Fin $ s + 1
  rw [tunedSheaf_eq_iSup]
  refine le_antisymm (iSup_le ?_) $ iSup_le ?_
  rintro ⟨c, hc⟩
  have hex : ∀ j, j < m →
      extendExponentsByZero m s (fun i : Fin m =>
          (⟨min (c i.1) s, lt_succ_of_le $ min_le_right _ _⟩ : _a0)) j
        = min (c j) s := fun j hj => dif_pos hj
  have hconstr : s ≤ ∑ j ∈ m65 m, (m - j) *
      extendExponentsByZero m s (fun i : Fin m =>
        (⟨min (c i.1) s, lt_succ_of_le $ min_le_right _ _⟩ : _a0)) j := by
    have _i39 : s ≤ ∑ j ∈ m65 m, (m - j) * min (c j) s := by
      by_cases h : ∀ j ∈ m65 m, c j ≤ s
      refine le_trans hc $ le_of_eq $ sum_congr rfl ?_
      intro j hj
      rw [min_eq_left $ h j hj]
      push Not at h
      obtain ⟨j, hj, hjs⟩ := h
      have hjm := mp_ mem_range hj
      have h1 : 1 ≤ m - j := by omega
      have hterm : s ≤ (m - j) * min (c j) s := by
        rw [min_eq_right $ le_of_lt hjs]
        calc s = 1 * s := sy_ (one_mul s)
          _ ≤ (m - j) * s := mul_le_mul h1 $ le_refl s
      refine le_trans hterm $ single_le_sum
        (f := fun j => (m - j) * min (c j) s) ?_ hj
      intro i _
      exact zero_le _
    refine le_trans _i39 $ le_of_eq $ sum_congr rfl ?_
    intro j hj
    rw [hex j $ mp_ mem_range hj]
  refine le_iSup_of_le ⟨_, hconstr⟩ ?_
  refine listProd_map_le_listProd_map _ _ (m127 m) fun j hj => ?_
  rw [hex j $ List.mem_range.mp hj]
  exact idealSheafData_pow_antitone_of_le _ $ min_le_left _ _
  rintro ⟨t, ht⟩
  exact le_iSup_of_le ⟨extendExponentsByZero m s t, ht⟩ le_rfl

theorem balancedTunedSheaf_comap {X Y : Sch}
    (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType $ h ≫ p]
    (I : ISD X) (m : ℕ) :
    balancedTunedSheaf k (h ≫ p) (I.comap h) m = (balancedTunedSheaf k p I m).comap h := by
  rw [balancedTunedSheaf_eq, balancedTunedSheaf_eq]
  let s := tuningExponent m
  let _a0 := h ≫ p
  rw [tunedSheaf_eq_iSup_fin k _a0 (cmI I h) m s, tunedSheaf_eq_iSup_fin k p I m s,
    comap_iSup]
  refine iSup_congr fun t => ?_
  have hfun : (fun j =>
        derivIdealSheafIterate k _a0 j (cmI I h) ^ extendExponentsByZero m s t.1 j)
      = (fun J : ISD X => cmI J h) ∘
        (fun j => derivIdealSheafIterate k p j I ^ extendExponentsByZero m s t.1 j) := by
    funext j
    show derivIdealSheafIterate k _a0 j (I.comap h) ^ extendExponentsByZero m s t.1 j
        = (derivIdealSheafIterate k p j I ^ extendExponentsByZero m s t.1 j).comap h
    rw [derivIdealSheafIterate_comap k p h j I, comap_pow]
  rw [comap_listProd, map_map]
  exact congrArg prod
    (congrArg (m39 · $ m127 m) hfun)
end


theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_pow_mul_le_pow_mul {Y : Sch}
    {F B B' : ISD Y} (hF : IsLocallyGeneratedByNonZeroDivisor F) (n : ℕ)
    (h : F ^ n * B ≤ F ^ n * B') : B ≤ B' :=
  (hF.pow n).le_of_mul_le_mul h

theorem comap_prod_map_range {X Y : Sch} (pi_ : Y ⟶ X) (f : ℕ → ISD X) (m : ℕ) :
    (((List.range m).map f).prod).comap pi_ =
      ((List.range m).map fun j => (f j).comap pi_).prod := by
  induction m with
  | zero =>
    simp
  | succ n ih =>
    rw [range_succ, map_append, prod_append, map_append, prod_append,
      comap_mul, ih]
    simp

section
variable {X : Sch}
section
variable (f g : ℕ → ISD X)
theorem prod_map_range_le :
    ∀ m, (∀ j, j < m → f j ≤ g j) →
      ((List.range m).map f).prod ≤ ((List.range m).map g).prod := fun _ h =>
  prod_le_prod' fun j hj => h j $ List.mem_range.mp hj

theorem prod_map_range_congr :
    ∀ m, (∀ j, j < m → f j = g j) →
      ((List.range m).map f).prod = ((List.range m).map g).prod := fun _ h =>
  congrArg prod $ map_congr_left fun j hj => h j $ List.mem_range.mp hj
end

theorem prod_map_pow_mul_pow_eq (F : ISD X)
    (G : ℕ → ISD X) (w c : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map fun j => (F ^ (w j) * G j) ^ (c j)).prod =
      F ^ (∑ j ∈ Finset.range n, w j * c j) *
        ((List.range n).map fun j => G j ^ (c j)).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_succ, map_append, prod_append, map_append, prod_append,
      ih, sum_range_succ, pow_add]
    simp [map_cons, map_nil, prod_cons, prod_nil, mul_one, mul_pow,
      ← pow_mul]
    rw [mul_mul_mul_comm]
end

section
variable (k : Type) [Field k] [CharZero k] [IsNoetherianRing k]
theorem comap_tunedSheaf_le_exceptionalIdeal_pow_mul {P P1 : Sch} (p : P ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p] [IsLocallyNoetherian P1]
    (pi_ : P1 ⟶ P) [LocallyOfFiniteType $ pi_ ≫ p] (p1_ : P1 ⟶ Sp k)
    [LocallyOfFiniteType p1_] (hp1_ : p1_ = pi_ ≫ p)
    (Z : ISD P) (E : Bdy P) (hZ : HasStrictNormalCrossingsWith p Z E)
    (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (A : ISD P) (m : ℕ) (hA : A ≤ Z ^ m) (u : ℕ) :
    (tunedSheaf k p A m u).comap pi_ ≤
      exceptionalIdeal pi_ Z ^ u *
        tunedSheaf k p1_ (controlledTransform pi_ Z A m hpi_ hA) m u := by
  let _a1 := pi_ ≫ p
  let _a0 := controlledTransform pi_ Z A m hpi_ hA
  subst hp1_
  refine le_trans (comap_iSup pi_
    (fun c : {c : ℕ → ℕ // u ≤ ∑ j ∈ m65 m, (m - j) * c j} =>
      ((m127 m).map fun j => derivIdealSheafIterate k p j A ^ (c.1 j)).prod)).le
    (iSup_le ?_)
  rintro ⟨c, hc⟩
  refine le_trans (le_of_eq $ comap_prod_map_range pi_
    (fun j => derivIdealSheafIterate k p j A ^ c j) m) ?_
  refine le_trans (prod_map_range_le _
    (fun j => (p5 pi_ Z ^ (m - j) *
      derivIdealSheafIterate k _a1 j _a0) ^ c j) m ?_) ?_
  intro j hj
  exact le_trans (le_of_eq $ comap_pow
    (derivIdealSheafIterate k p j A) pi_ $ c j) $ pow_le_pow_left' (comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p pi_ Z E hZ hpi_ A m hA j $ m49 hj) $ c j
  refine le_trans (le_of_eq $ prod_map_pow_mul_pow_eq (p5 pi_ Z)
    (fun j => derivIdealSheafIterate k _a1 j _a0)
    (fun j => m - j) c m) ?_
  exact mul_le_mul' (pow_le_pow_right_of_le_one' le_top hc) $ le_iSup (fun d : {c : ℕ → ℕ // u ≤ ∑ j ∈ m65 m, (m - j) * c j} => ((m127 m).map fun j => derivIdealSheafIterate k _a1 j _a0 ^ (d.1 j)).prod) ⟨c, hc⟩

theorem comap_tunedSheaf_of_smooth
    {P Y : Sch} (p : P ⟶ Sp k) [Smooth p]
    [LocallyOfFiniteType p] (h : Y ⟶ P) [Smooth h]
    (q : Y ⟶ Sp k) [LocallyOfFiniteType q] (hq : q = h ≫ p)
    (A : ISD P) (m u : ℕ) :
    (tunedSheaf k p A m u).comap h = tunedSheaf k q (A.comap h) m u := by
  let _a0 := h ≫ p
  let _a1 := m127 m
  subst hq
  refine le_antisymm ?_ ?_
  refine le_trans (comap_iSup h
    (fun c : {c : ℕ → ℕ // u ≤ ∑ j ∈ m65 m, (m - j) * c j} =>
      (_a1.map fun j => derivIdealSheafIterate k p j A ^ (c.1 j)).prod)).le
    (iSup_le ?_)
  rintro ⟨c, hc⟩
  refine le_trans (le_of_eq $ comap_prod_map_range h
    (fun j => derivIdealSheafIterate k p j A ^ c j) m) ?_
  refine le_trans (prod_map_range_le _
    (fun j => derivIdealSheafIterate k _a0 j (cmI A h) ^ c j) m ?_) $ le_iSup (fun d : {c : ℕ → ℕ // u ≤ ∑ j ∈ m65 m, (m - j) * c j} => (_a1.map fun j => derivIdealSheafIterate k _a0 j (cmI A h) ^ (d.1 j)).prod) ⟨c, hc⟩
  intro j _
  refine le_of_eq ?_
  show (derivIdealSheafIterate k p j A ^ c j).comap h
      = derivIdealSheafIterate k _a0 j (A.comap h) ^ c j
  rw [comap_pow,
    derivIdealSheafIterate_comap k p h j A]
  refine le_trans (le_of_eq $ tunedSheaf_eq_iSup k _a0 (cmI A h) m u) $ iSup_le ?_
  rintro ⟨c, hc⟩
  refine le_trans (le_of_eq ?_) $ comap_mono h
    (le_iSup (fun d : {c : ℕ → ℕ // u ≤ ∑ j ∈ m65 m, (m - j) * c j} =>
      (_a1.map fun j => derivIdealSheafIterate k p j A ^ (d.1 j)).prod) ⟨c, hc⟩)
  refine m32 (prod_map_range_congr _
    (fun j => cmI (derivIdealSheafIterate k p j A ^ c j) h) m ?_)
    (comap_prod_map_range h (fun j => derivIdealSheafIterate k p j A ^ c j) m).symm
  intro j _
  show derivIdealSheafIterate k _a0 j (A.comap h) ^ c j
      = (derivIdealSheafIterate k p j A ^ c j).comap h
  rw [comap_pow, derivIdealSheafIterate_comap k p h j A]
end

end FunctorialResolution.EmbeddedResolution
end
end
-- BEGIN_E2_PROJ_Bundle07
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
abbrev p26 := @MaxContactFunctoriality.OrderReductionHypotheses
abbrev p49 := @MaxContactFunctoriality.lowerDimensionalFamily
end
-- END_E2_PROJ_Bundle07
