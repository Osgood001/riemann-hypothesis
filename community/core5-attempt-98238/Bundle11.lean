import Mathlib
import Bundle00
import Bundle01
import Bundle02
import Bundle03
import Bundle04
import Bundle05
import Bundle06
import Bundle07
import Bundle08
import Bundle09
import Bundle10
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open Category (assoc comp_id)
open FunctorialResolution.Blowup (IsBlowupAlongIdealSheaf IsLocallyGeneratedByNonZeroDivisor StrictTransformIsBlowupOfClosedSubscheme exceptionalIdeal exceptionalIdeal_eq_comap isLocallyGeneratedByNonZeroDivisor_comap_top isLocallyGeneratedByNonZeroDivisor_top quasiCompact_sigmaio sigmaio_base_ne strictTransform)
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (IsAdmissibleCenter IsStationaryAt appendBoundary_of_le_length appendIdeal_of_le_length appendIdeal_of_length_lt appendProjectionToBase_of_le_length appendProjectionToBase_of_length_lt appendToBlowupSequenceData_center_length appendToBlowupSequenceData_center_of_length_lt appendToBlowupSequenceData_center_of_lt_length appendToBlowupSequenceData_schemeAt_length_add_length appendToBlowupSequenceData_schemeAt_of_le_length appendToBlowupSequenceData_schemeAt_of_length_lt append_boundary append_boundary_length_add_length append_dataAt_last append_dataAt_of_forall append_ideal append_ideal_length_add_length append_isomorphic_of_isomorphic append_isomorphic_of_length_eq_zero append_length append_projectionToBase append_toBlowupSequenceData blowupAtCenter blowupAtCenter_boundary_succ blowupAtCenter_eq_append blowupAtCenter_ideal_succ blowupAtCenter_length blowupAtCenter_projectionToBase_succ blowupAtCenter_schemeAt_succ blowupSequenceData_ofMarkedSequence boundarySupport_dataAt boundary_eq_comap_strictPullbackComparisonMap boundary_length centerAtLast center_support_subset_orderAtLeastLocus_appendIdeal emptyMarkedBlowupSequenceData_append_isomorphic exceptionalIdeal_pow_mul_appendIdeal_succ ideal_eq_comap_controlledTransform isMarked_toBlowupSequenceData isStationaryAt_iff_not_isAdmissibleCenter monomialBlowupIterate monomialBlowupIterate_succ monomialBlowupIterate_zero monomialBlowupStep_length monomialStallIndex_eq_zero_of_not_isAdmissibleCenter nonempty_center_and_certificate_of_hasPrincipalizationCenter ofMarkedSequence ofMarkedSequence_ideal ofMarkedSequence_length ofSingleBlowup projectionToBase_eq_toSequenceOfBlowups strictPullbackComparisonMap toBlowupSequenceData_boundary_eq_boundary_of_le toBlowupSequenceData_controlledTransform_eq toMarkedSequence_blowupMorphism toMarkedSequence_boundary toMarkedSequence_center toMarkedSequence_ideal toMarkedSequence_lastIdeal toMarkedSequence_length toMarkedSequence_projectionToSpec toMarkedSequence_schemeAt toMarkedSequence_toSequenceOfBlowups)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (IsAdmissible SameNontrivialBoundary baseChange_boundary baseChange_ideal bc bget' boundary ideal isOrderBoundedByMult_iff mk mk_eq_mk mult pullbackAlong_boundary pullbackAlong_mult pullbackAlong_structureMorphism scheme structMap transformAt_boundary transformAt_structureMorphism withBoundary withBoundary_boundary withBoundary_dim withSchemeIdealBoundary_ideal withSchemeIdealBoundary_structureMorphism)
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups (IsResolution boundaryLocus controlledMonomialTransform controlledNonMonomialTransform controlledTransform_succ isResolution_iff lastIdeal lastIdeal_eq mem_boundaryLocus_iff orderAtLeastLocus_subset_preimage_transitionMap projectionToSpec_eq projectionToSpec_succ smooth_projectionToSpec toSequenceOfBlowups)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (blowupMorphism_eq_transitionMap center isomorphic_of_isStrictPullback_same_source isomorphic_refl projectionToBase projectionToBase_def projectionToBase_zero schemeAt transitionMap transitionMapSucc transitionMap_self_eq_id transitionMap_trans)
open List (Lex append_nil drop drop_zero eraseIdx eraseIdx_append_of_lt_length eraseIdx_map foldr foldr_cons foldr_nil get getElem_append_left getElem_map getElem_mem getElem_of_eq get_eq_getElem length length_append length_eraseIdx length_map lget map_append map_congr_left map_cons map_drop map_map map_nil map_take mem_cons mem_iff_getElem mem_map mem_singleton nil_append ofFn ofFn_succ ofFn_zero prod prod_append prod_cons prod_nil prod_ofFn range' range_succ take take_append_drop take_left take_of_length_le)
open Nat (add_sub_cancel' cast_add lcm lcm_ne_zero le_add_right le_induction le_of_succ_le le_succ le_zero lt_of_succ_le lt_one_iff lt_succ_iff lt_succ_self mul_le_mul not_lt_zero one_le_iff_ne_zero sSup_mem succ_le_succ succ_lt_succ succ_ne_zero succ_pos zero_le zero_lt_succ)
open Or (inl inr)
open Scheme.Hom (appIso_hom' appLE id_base ker le_ker_comp pre support_ker)
open Scheme.IdealSheafData (comap comap_comp comap_iSup comap_id comap_ideal_eq_map_appLE comap_mono comap_mul comap_pow comap_sup comap_top eq_top_iff_support_eq_empty gc le_ofIdeals_iff mem_support_comap one_eq_top radical_ideal subschemeι support support_antitone support_eq_bot_iff support_nonempty_iff_ne_top top_mul vanishingIdeal vanishingIdeal_support)
open Set (disjoint_left disjoint_right eq_empty_of_subset_empty eq_empty_or_nonempty eq_univ_of_forall ext_iff image_eq_empty image_preimage_eq mem_empty_iff_false mem_iInter mem_iUnion mem_preimage mem_range_self nonempty_iff_ne_empty not_nonempty_iff_eq_empty preimage preimage_empty preimage_inter preimage_mono preimage_univ range range_comp sdiff_subset_sdiff_left subset_empty_iff univ)
noncomputable section
open Category (id_comp)
open ENat (add_one_le_iff natCast_ne_top ne_top_iff_exists)
open Fin (cast castSucc last lt_def prod_univ_castSucc prod_univ_succ prod_univ_zero val_injective)
open Finset (card_eq_zero card_erase_of_mem card_image_of_injective card_insert_le card_le_card card_pos erase_eq_of_notMem image mem_erase mem_image mem_insert_self mem_of_mem_erase prod_congr prod_empty prod_mul_distrib prod_pow_eq_pow_sum subset_univ sum_congr sum_empty sum_erase_add sum_insert sum_le_sum_of_subset univ_eq_empty)
open FunctorialResolution.Blowup.blowup (proj)
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData (append ofSequenceOfBlowups ofSequenceOfBlowups_blowupMorphism ofSequenceOfBlowups_length ofSequenceOfBlowups_projectionToBase ofSequenceOfBlowups_schemeAt ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic prepend prepend_blowupMorphism_succ prepend_blowupMorphism_zero prepend_center_succ prepend_center_zero prepend_isoObjZero prepend_length projectionToBase_prepend_succ toMarkedBlowupSequenceData toMarkedBlowupSequenceData_toSequenceOfBlowups toSequenceOfBlowups_isomorphic_of_iso toSequenceOfBlowups_projectionToBase toSequenceOfBlowups_schemeAt toSequenceOfBlowups_transitionMap transitionMap_comp_transitionMap transitionMap_refl transitionMap_succ)
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups (ideal_zero projectionToSpec)
open FunctorialResolution.EmbeddedResolution.MonomialCenter (IsLocallyMonomialTriple centerInvariant centerInvariant_le_iff comap_monomialCenter_eq_top lexMaxIndices_pullbackOverField_eq_image mem_sortedIndices minIndexCard_eq_of_sameNontrivialBoundary minIndexCard_ne_zero_and_le_pullbackOverField minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le monomialCenter_eq_of_sameNontrivialBoundary monomialCenter_pullbackOverField_eq_comap sameNontrivialBoundary_refl sortedIndices sortedIndices_image_of_strictMono)
open FunctorialResolution.EmbeddedResolution.MonomialCenter.CenterInvariant (Lt)
open IsPullback (id_vert of_hasPullback)
open Iso (hom inv inv_hom_id_assoc symm_hom)
open Limits.pullback (fst snd)
open MorphismProperty.IsStableUnderBaseChange (of_isPullback)
open Nat (zero_le)
open Option (some_ne_none)
open Scheme.Hom (comp_apply)
open FunctorialResolution.EmbeddedResolution (IsMaxContactInvariant NonzeroOnComponents balancedTunedSheaf balancedTunedSheaf_eq tunedSheaf tuningExponent tuningExponent_one)
open FunctorialResolution.EmbeddedResolution.MaxContactCoverData (derivedTriple_mult)
open Iff (mpr)
open Scheme (IdealSheafData)
section


namespace FunctorialResolution.EmbeddedResolution

abbrev companionTriple (T : MarkedIdealWithBoundary)
    (s : T.mbs) : MarkedIdealWithBoundary :=
  tripleAtLength T s (companionIdeal T s) $ mult T * maxOrderNonMonomialOnOrderLocus T s

section
variable (hG : PrincipalizationGeometryHypotheses)
include hG
section
variable {T : MarkedIdealWithBoundary} (hT : IsAdmissible T)
include hT
section
variable (s : T.mbs)
theorem orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus :
    ∀ x ∈ orderAtLeastLocus (s.ideal s.length) T.mult,
      orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ENat) := by
  obtain ⟨B, hB⟩ := exists_orderAt_lastNonMonomialPart_le hG hT s
  intro x hx
  exact orderAt_le_maxOrderOn (lastNonMonomialPart T s) hB
    (orderAtLeastLocus (lastI s) T.mult) hx

theorem orderAt_companionIdeal_le (hcont : CompanionIdealReductionContinues T s) :
    ∀ x : ↥(s.obj s.length),
      orderAt (companionIdeal T s) x ≤ ((mult T * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ENat) := by
  intro x
  exact an2 (isAdmissible_withIdealAndMult_pow_sup_pow (isAdmissible_tripleAtLength hG hT s) (mp_ (companionIdealReductionContinues_iff T s) hcont) $ orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s) x

theorem companionTriple_isAdmissible (hcont : CompanionIdealReductionContinues T s) :
    IsAdmissible $ companionTriple T s := by
  exact an1 $ isAdmissible_withIdealAndMult_pow_sup_pow (isAdmissible_tripleAtLength hG hT s) (mp_ (companionIdealReductionContinues_iff T s) hcont)
    (orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s)
end

section
variable (A : PrincipalizationAssignment) (s : T.mbs)
theorem isMarked_seqAtEnd_companionIdeal
    (hcont : CompanionIdealReductionContinues T s) :
    (ofMarkedSequence
          (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (mult T * maxOrderNonMonomialOnOrderLocus T s)
            (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData.IsMarked
      (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult (s.boundary s.length) := by
  exact isMarked_ofMarkedSequence_of_isMonomialSplitting hG (isAdmissible_tripleAtLength hG hT s) (isMonomialSplitting_lastNonMonomialPart hG hT s) (mp_ (companionIdealReductionContinues_iff T s) hcont) (orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s)
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (tMu T * maxOrderNonMonomialOnOrderLocus T s)
      (tripleAtLength_dim_le hG hT s _ _))

def continuationByCompanionIdeal
    (hcont : CompanionIdealReductionContinues T s) :
    MarkedBlowupSequenceData (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult
      (s.boundary s.length) :=
  toMarkedBlowupSequenceData
    (ofMarkedSequence
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (mult T * maxOrderNonMonomialOnOrderLocus T s)
          (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData
    (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult (s.boundary s.length)
    (isMarked_seqAtEnd_companionIdeal hG hT A s hcont)


noncomputable def companionIdealPrincipalizationSeq :
    MarkedSequenceOfBlowups (s.proj s.length ≫ structMap T) (companionIdeal T s)
      (mult T * maxOrderNonMonomialOnOrderLocus T s) $ s.boundary s.length :=
  principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (mult T * maxOrderNonMonomialOnOrderLocus T s)
    (tripleAtLength_dim_le hG hT s _ _)

theorem continuationByCompanionIdeal_ideal_eq
    (hcont : CompanionIdealReductionContinues T s) : ∀ i : ℕ,
    (continuationByCompanionIdeal hG hT A s hcont).ideal i
      = MarkedSequenceOfBlowups.controlledTransform (companionIdealPrincipalizationSeq hG hT A s) (s.ideal s.length)
          T.mult i := by
  intro i
  induction i with
  | zero => rfl
  | succ j ih =>
      rw [controlledTransform_succ, ← ih]
      rfl
end
end

theorem extendByCompanionIdeal_eq_append (hinv : ComapIsoInvariance)
    {T : MarkedIdealWithBoundary} (hT : IsAdmissible T) (A : PrincipalizationAssignment)
    (s : T.mbs) (hcont : CompanionIdealReductionContinues T s) :
    extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s =
      s.append (continuationByCompanionIdeal hG hT A s hcont) hinv :=
  appendRecursivePrincipalization_eq_append hinv T (principalizationOfDimLe T A) s (companionIdeal T s)
    (tMu T * maxOrderNonMonomialOnOrderLocus T s) (tripleAtLength_dim_le hG hT s _ _)
    (isMarked_seqAtEnd_companionIdeal hG hT A s hcont)
end

section
variable {k : Type} [Field k]
private theorem orderAtLeastLocus_eq_empty_of_comap_iso [CharZero k]
    {X Y : Sch} (p : X ⟶ Sp k) [Smooth p]
    (e : Y ≅ X) (J : ISD X) (c : ℕ)
    (hJ : orderAtLeastLocus (comap J e.hom) c = ∅) : orderAtLeastLocus J c = ∅ := by
  have hcomp : comap (comap J e.hom) e.inv = J := by
    rw [← comap_comp, m114, comap_id]
  have key := image_orderAtLeastLocus_comap_subset k (isoH e ≫ p) e.inv (comap J e.hom) c
  rw [hcomp, hJ] at key
  exact mp_ image_eq_empty $ mp_ subset_empty_iff key

section
variable (mu_ : ℕ) (D : MarkedSchemeWithCenter k)
noncomputable def maxOrderNonMonomialPartOnOrderAtLeastLocus : ℕ :=
  maxOrderOn (nonMonomialPart D.boundary D.ideal) $ orderAtLeastLocus D.ideal mu_

theorem maxOrderNonMonomial_transport_eqToIso {A : Sch} (h : A = D.ambient) :
    maxOrderNonMonomialPartOnOrderAtLeastLocus mu_ (D.transport $ eqToIso h) = maxOrderNonMonomialPartOnOrderAtLeastLocus mu_ D := by
  subst h
  exact congrArg (maxOrderNonMonomialPartOnOrderAtLeastLocus mu_) $ MarkedSchemeWithCenter.transport_refl D
end
end

section
variable (hG : PrincipalizationGeometryHypotheses)
include hG
section
variable (hinv : ComapIsoInvariance) {n} {A B} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary} (hT : IsAdmissible T) (hdim : T.krullDimSucc ≤ n)
include hspec hT hdim
theorem maxOrderNonMonomialOnOrderLocus_iter_add_le
    (s0_ : T.mbs) (f : ℕ)
    (h : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s0_ f)) :
    maxOrderNonMonomialOnOrderLocus T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s0_ f) + f ≤ maxOrderNonMonomialOnOrderLocus T s0_ := by
  revert h
  induction f with
  | zero =>
      intro h
      rw [companionIdealReductionIter_zero]
      omega
  | succ m ih =>
      intro h
      by_cases hc : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s0_ m)
      have hstep := companionIdealReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) s0_ m hc
      have hlt : maxOrderNonMonomialOnOrderLocus T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s0_ (m + 1)) <
          maxOrderNonMonomialOnOrderLocus T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s0_ m) := by
        rw [hstep]
        let s := companionIdealReductionIter hinv T (principalizationOfDimLe T A) s0_ m
        let _c0 := continuationByCompanionIdeal hG hT A s hc
        let _c1 := companionIdealPrincipalizationSeq hG hT A s
        let _a6 := mp_ (companionIdealReductionContinues_iff T s) hc
        have hs1 := _a6
        let _a4 := companionIdeal T s
        let _a7 := principalizationOfDimLe T A
        have ht : 0 < (principalizationSeqAtEnd T _a7 s _a4 (tMu T * maxOrderNonMonomialOnOrderLocus T s) (tripleAtLength_dim_le hG hT s _ _)).length := by
          have hv := _a6
          have hSvalid := companionTriple_isAdmissible hG hT s hc
          let _a0 := tripleAtLength_dim_le hG hT s _a4 $ tMu T * maxOrderNonMonomialOnOrderLocus T s
          have hSob : (companionTriple T s).IsOrderBoundedByMult :=
            (isOrderBoundedByMult_iff _).mpr (orderAt_companionIdeal_le hG hT s hc)
          have hcall : principalizationSeqAtEnd T _a7 s _a4 (tMu T * maxOrderNonMonomialOnOrderLocus T s)
              _a0 =
              A (companionTriple T s) := rfl
          rw [hcall]
          rcases m73 (A (companionTriple T s)).length with h0 | hpos
          exfalso
          have hcz := hT.charZero
          let _a1 := s.proj s.length ≫ tMp T
          have hsm : Smooth _a1 := hSvalid.smooth
          have hres := mp_ (isResolution_iff (A (companionTriple T s)))
            (hspec.resolves (companionTriple T s) hSvalid (le_trans _a0 hdim) hSob)
          rw [lastIdeal_eq, h0, ideal_zero] at hres
          have hempty :=
            orderAtLeastLocus_eq_empty_of_comap_iso _a1
              (A (companionTriple T s)).isoZero _a4 (tMu T * maxOrderNonMonomialOnOrderLocus T s) hres
          have hforall := mp_ (orderAtLeastLocus_pow_sup_pow_eq_empty_iff T.base _a1
            (lastNonMonomialPart T s) (s.ideal s.length) (hT.one_le_mult) hv) hempty
          obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT s
          let _a2 := orderAtLeastLocus (s.ideal s.length) T.mult
          have hlt := maxOrderOn_lt_of_forall_lt (lastNonMonomialPart T s) hBd
            _a2 hv hforall
          have hpi : maxOrderNonMonomialOnOrderLocus T s =
              maxOrderOn (lastNonMonomialPart T s) _a2 := rfl
          rw [hpi] at hlt
          exact lt_irrefl _ hlt
          exact hpos
        have hT2 := isAdmissible_tripleAtLength hG hT s
        have hsplit := isMonomialSplitting_lastNonMonomialPart hG hT s
        have hord := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s
        have hboundaryEq : _c0.boundary _c0.length
            = _c1.boundary
                _c1.length :=
          ofMarkedSequence_boundary_eq_of_le _c1
            _c1.length le_rfl
        have hideal :=
          continuationByCompanionIdeal_ideal_eq hG hT A s hc _c0.length
        have hempty : orderAtLeastLocus (_c1.ideal
            _c1.length) (tMu T * maxOrderNonMonomialOnOrderLocus T s) = ∅ := by
          have hres := hspec.resolves (companionTriple T s) (companionTriple_isAdmissible hG hT s hc)
            (le_trans (tripleAtLength_dim_le hG hT s _a4 (tMu T * maxOrderNonMonomialOnOrderLocus T s)) hdim)
            (mpr_ (isOrderBoundedByMult_iff _) (orderAt_companionIdeal_le hG hT s hc))
          have h2 := mp_ (isResolution_iff _) hres
          rwa [lastIdeal_eq] at h2
        have hlt0 := orderAt_controlledNonMonomialTransform_length_lt hG hT2 hsplit hs1 hord
          _c1 hempty
        have hsp := (isMonomialSplitting_controlledTransform_of_le_length hG hT2 hsplit hs1 hord _c1
          _c1.length le_rfl).2.1
        let _a0 := controlledNonMonomialTransform _c1 (lastNonMonomialPart T s) (maxOrderNonMonomialOnOrderLocus T s) _c1.length
        have hsp' : IsMonomialSplitting
            (_c0.boundary _c0.length)
            (_c0.ideal _c0.length)
            (controlledMonomialTransform _c1
              (monomialPart (s.boundary s.length) (s.ideal s.length)) T.mult (maxOrderNonMonomialOnOrderLocus T s)
              _c1.length)
            _a0 := by
          rwa [hboundaryEq, hideal]
        let _a1 := nonMonomialPart (_c0.boundary _c0.length) $ _c0.ideal _c0.length
        have hnonMon : _a1
            = _a0 := hG.nonMonomialPart_eq_of_isMonomialSplitting _ (isAdmissible_tripleAtLength hG hT2 _c0) _ _ hsp'
        obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT2 _c0
        have hBd3 : ∀ x : (_c1.schemeAt
              _c1.length),
            orderAt _a0 x ≤ Bd := by
          intro x
          have h0 : orderAt _a1 x
                ≤ Bd := hBd x
          rwa [hnonMon] at h0
        let _a5 := s.append _c0 hinv
        have key : maxOrderNonMonomialOnOrderLocus T _a5
            = maxOrderNonMonomialPartOnOrderAtLeastLocus T.mult
              (_c0.dataAt _c0.length) := by
          have h1 : maxOrderNonMonomialOnOrderLocus T _a5
              = maxOrderNonMonomialPartOnOrderAtLeastLocus T.mult (_a5.dataAt
                  _a5.length) := rfl
          rw [h1, append_dataAt_last s _c0 hinv ht]
          exact maxOrderNonMonomial_transport_eqToIso T.mult
            (_c0.dataAt _c0.length) _
        rw [extendByCompanionIdeal_eq_append hG hinv hT A s hc, key]
        show maxOrderOn _a1
            (orderAtLeastLocus (_c0.ideal _c0.length)
              T.mult) < maxOrderNonMonomialOnOrderLocus T s
        rw [hnonMon, hideal]
        exact maxOrderOn_lt_of_forall_lt _ hBd3 _ hs1 hlt0
      have hih := ih hc
      omega
      exfalso
      rw [companionIdealReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A) s0_ m hc] at h
      exact hc h

theorem not_companionIdealReductionContinues_companionIdealReduction :
    ¬ CompanionIdealReductionContinues T (companionIdealReduction hinv T (principalizationOfDimLe T A)) := by
  intro h
  let _a1 := principalizationOfDimLe T A
  rw [companionIdealReduction_eq hinv T _a1] at h
  let _a0 := nonMonomialOrderReduction hinv T _a1
  have hle := maxOrderNonMonomialOnOrderLocus_iter_add_le hG hinv hspec hT hdim
    _a0 (maxOrderNonMonomialOnOrderLocus T _a0 + 1) h
  omega

theorem orderAt_lastNonMonomialPart_companionIdealReduction_eq_zero :
    ∀ x ∈ orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
        (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult,
      orderAt (lastNonMonomialPart T (companionIdealReduction hinv T (principalizationOfDimLe T A))) x = 0 := by
  let _c0 := companionIdealReduction hinv T $ principalizationOfDimLe T A
  have hzero : maxOrderNonMonomialOnOrderLocus T _c0 = 0 := by
    by_contra hne
    exact (not_companionIdealReductionContinues_companionIdealReduction hG hinv hspec hT hdim) $ mpr_ (companionIdealReductionContinues_iff T _c0)
      (mpr_ one_le_iff_ne_zero hne)
  obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT _c0
  let _a0 := orderAtLeastLocus (lastI _c0) T.mult
  let _a1 := lastNonMonomialPart T _c0
  have hpi : maxOrderNonMonomialOnOrderLocus T _c0 =
      maxOrderOn _a1
        _a0 := rfl
  rw [hpi] at hzero
  exact mp_ (maxOrderOn_eq_zero_iff _a1 hBd
    _a0) hzero
end
end

theorem support_comap_iso_hom_nonempty {X Y : Sch} (e : X ≅ Y)
    (J : ISD Y) (h : (support J : Set ↥Y).Nonempty) :
    (support (comap J e.hom) : Set ↥X).Nonempty := by
  obtain ⟨y, hy⟩ := h
  refine ⟨isoI e y, ?_⟩
  refine mpr_ (mem_comap_support_iff_base_mem_support e.hom J $ isoI e y) ?_
  simp_all

theorem isInvariantUnderIso_hasPrincipalizationCenter_of_two_le {k : Type} [Field k] {mu_ : ℕ}
    (hmu_ : 2 ≤ mu_) : IsInvariantUnderIso fun D : MarkedSchemeWithCenter k => HasPrincipalizationCenter mu_ D := by
  intro D A e hD
  exact ⟨support_comap_iso_hom_nonempty e D.center hD.center_nonempty,
    PrincipalizationCertificate.of_two_le _ _ _ _ _ _ hmu_⟩

theorem companionIdealReductionContinues_of_continues_iter (hinv : ComapIsoInvariance)
    (T : MarkedIdealWithBoundary) (rc : (S : MarkedIdealWithBoundary) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s0_ : T.mbs) (f : ℕ)
    (h : CompanionIdealReductionContinues T $ companionIdealReductionIter hinv T rc s0_ f) : CompanionIdealReductionContinues T s0_ := by
  revert h
  induction f with
  | zero =>
      intro h
      rwa [companionIdealReductionIter_zero] at h
  | succ n ih =>
      intro h
      by_cases hc : CompanionIdealReductionContinues T $ companionIdealReductionIter hinv T rc s0_ n
      exact ih hc
      rw [companionIdealReductionIter_succ_of_not_continues hinv T rc s0_ n hc] at h
      exact ih h

section
variable (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance) {n} {A B} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary} (hT : IsAdmissible T) (hdim : T.krullDimSucc ≤ n)
include hG hspec hT hdim
theorem hasCenter_companionIdealReductionIter (f : ℕ) (i : ℕ)
    (hi : i <
      (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).length) :
    HasPrincipalizationCenter T.mult
      ((companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).dataAt i) := by
  let _a1 := principalizationOfDimLe T A
  let _c0 := nonMonomialOrderReduction hinv T _a1
  revert i
  induction f with
  | zero =>
      intro i hi
      rw [companionIdealReductionIter_zero] at hi ⊢
      exact hasCenter_nonMonomialOrderReduction hG hinv hspec hT hdim i hi
  | succ m ih =>
      intro i hi
      by_cases hc : CompanionIdealReductionContinues T
          (companionIdealReductionIter hinv T _a1 _c0 m)
      have hcont0 :=
        companionIdealReductionContinues_of_continues_iter hinv T _a1
          _c0 m hc
      have hm : 2 ≤ T.mult :=
        by
        have hv :=
          (companionIdealReductionContinues_iff T _c0).mp hcont0
        obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT _c0
        let _a0 := orderAtLeastLocus (_c0.ideal _c0.length) T.mult
        let _a2 := lastNonMonomialPart T _c0
        have hlt :=
          maxOrderOn_lt_of_forall_lt _a2 hBd
            _a0 hT.one_le_mult
            (fun x _ => orderAt_lastNonMonomialPart_nonMonomialOrderReduction_lt hG hinv hspec hT hdim x)
        have hpi : maxOrderNonMonomialOnOrderLocus T _c0 =
            maxOrderOn _a2
              _a0 := rfl
        rw [← hpi] at hlt
        omega
      rw [companionIdealReductionIter_succ_of_continues hinv T _a1
        _c0 m hc] at hi ⊢
      let s := companionIdealReductionIter hinv T _a1 _c0 m
      have hd :=
        le_trans (tripleAtLength_dim_le hG hT s (companionIdeal T s) $ T.mult * maxOrderNonMonomialOnOrderLocus T s) hdim
      let _a1 := companionTriple T s
      have hob :=
        (isOrderBoundedByMult_iff _a1).mpr
          (orderAt_companionIdeal_le hG hT s hc)
      let _a0 := continuationByCompanionIdeal hG hT A s hc
      have ht : ∀ j < _a0.length,
          HasPrincipalizationCenter T.mult $ _a0.dataAt j := by
        intro j hj
        exact ⟨hspec.center_nonempty _a1 (companionTriple_isAdmissible hG hT s hc) hd hob j hj,
          PrincipalizationCertificate.of_two_le _ _ _ _ _ _ hm⟩
      rw [extendByCompanionIdeal_eq_append hG hinv hT A s hc] at hi ⊢
      exact append_dataAt_of_forall s _a0 hinv
        (HasPrincipalizationCenter T.mult) (isInvariantUnderIso_hasPrincipalizationCenter_of_two_le hm) (fun j hj => ih j hj) ht i hi
      rw [companionIdealReductionIter_succ_of_not_continues hinv T _a1
        _c0 m hc] at hi ⊢
      exact ih i hi

theorem hasCenter_companionIdealReduction i
    (hi : i < (companionIdealReduction hinv T $ principalizationOfDimLe T A).length) :
    HasPrincipalizationCenter T.mult $ (companionIdealReduction hinv T $ principalizationOfDimLe T A).dataAt i := by
  let _a0 := principalizationOfDimLe T A
  rw [companionIdealReduction_eq hinv T _a0] at hi ⊢
  exact hasCenter_companionIdealReductionIter hG hinv hspec hT hdim
    (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T _a0) + 1) i hi
end

theorem foldr_ofFn_mul_eq_prod {X : Sch} (m : ℕ)
    (g : Fin m → ISD X) :
    (ofFn g).foldr (· * ·) ⊤ = ∏ i, g i := by
  induction m with
  | zero =>
      have h1 : ofFn g = [] := by simp
      rw [h1, foldr_nil, prod_univ_zero]
      exact Scheme.IdealSheafData.one_eq_top.symm
  | succ p ih =>
      rw [ofFn_succ, foldr_cons, ih, prod_univ_succ]

theorem isLocallyMonomialTriple_tripleAtLength_companionIdealReduction (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance)
    {n : ℕ} {A B : PrincipalizationAssignment} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) :
    IsLocallyMonomialTriple
      (tripleAtLength T (companionIdealReduction hinv T $ principalizationOfDimLe T A)
        ((companionIdealReduction hinv T $ principalizationOfDimLe T A).ideal (companionIdealReduction hinv T $ principalizationOfDimLe T A).length) T.mult) := by
  let _a0 := companionIdealReduction hinv T $ principalizationOfDimLe T A
  refine ⟨isAdmissible_tripleAtLength hG hT _a0, ?_⟩
  intro x hx
  obtain ⟨U, e, hxU, hU⟩ :=
    (isMonomialSplitting_lastNonMonomialPart hG hT
      _a0).exists_comap_eq_prod_pow_of_orderAt_eq_zero $ orderAt_lastNonMonomialPart_companionIdealReduction_eq_zero hG hinv hspec hT hdim x hx
  exact ⟨U, hxU, e, tr_ hU (foldr_ofFn_mul_eq_prod _ _).symm⟩

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

def OrderAtPullbackInvariant (T : MarkedIdealWithBoundary) {Y : Sch} (g : Y ⟶ scheme T) : Prop :=
  ∀ (B : Sch) (b : B ⟶ scheme T) (pB : B ⟶ Sp T.base)
    (IB : ISD B) (EB : Bdy B),
    IsAdmissible (mk T.base B pB IB T.mult EB) →
    b ≫ structMap T = pB →
    ∀ (Q : Sch) (q : Q ⟶ B) (p : Q ⟶ Y), IsPullback q p b g →
    ∀ (A : ISD B) (y : ↥Q),
      orderAt (comap A q) y = orderAt A (q.base y)

theorem orderAtPullbackInvariant_baseChange_field (hG : PrincipalizationGeometryHypotheses) (T : MarkedIdealWithBoundary)
    (_hT : IsAdmissible T) (L : Type) [Field L] [CharZero L] (f : T.base →+* L) :
    OrderAtPullbackInvariant T $ pullback.fst T.structMap $ specMapOfFieldHom T.base L f := by
  let _c0 := specMapOfFieldHom T.base L f
  intro B b pB IB EB hB hcomm Q q p hpb A y
  have hbig : IsPullback q (p ≫ pullback.snd T.structMap _c0) pB
      _c0 := by
    rw [← hcomm]
    exact hpb.paste_vert $ of_hasPullback T.structMap _c0
  have he :=
    hbig.isoPullback_hom_fst
  have : IsOpenImmersion hbig.isoPullback.hom := inferInstance
  have hkey := hG.orderAt_baseChange (mk T.base B pB IB T.mult EB) hB L f A
      (hbig.isoPullback.hom.base y)
  let _a0 := bsM (pullback.fst pB _c0) $ hbig.isoPullback.hom.base y
  have hq : _a0
      = bsM q y := congrArg (fun m : Q ⟶ B => bsM m y) he
  calc orderAt (cmI A q) y
      = orderAt (comap A $ hbig.isoPullback.hom ≫
          pullback.fst pB _c0) y := by
        rw [he]
    _ = orderAt (comap (cmI A $ pullback.fst pB _c0)
          hbig.isoPullback.hom) y := by
        rw [comap_comp]
    _ = orderAt (cmI A $ pullback.fst pB _c0)
          (hbig.isoPullback.hom.base y) :=
        orderAt_comap_of_isOpenImmersion _ _ y
    _ = orderAt A _a0 := hkey
    _ = orderAt A (bsM q y) := by rw [hq]





structure MarkedPullbackSquare (T : MarkedIdealWithBoundary) {Y : Sch} (g : Y ⟶ T.scheme) where
  baseScheme : Sch
  topScheme : Sch
  bottom : baseScheme ⟶ T.scheme
  structMap : baseScheme ⟶ Sp T.base
  ideal : ISD baseScheme
  mult : ℕ
  boundary : Bdy baseScheme
  left : topScheme ⟶ baseScheme
  top : topScheme ⟶ Y
  bottom_structMap : bottom ≫ T.structMap = structMap
  dim_le : krullDimSucc baseScheme ≤ T.krullDimSucc
  isPullback : IsPullback left top bottom g
  valid : (mk T.base baseScheme structMap ideal mult boundary).IsAdmissible

namespace MarkedPullbackSquare

variable {T : MarkedIdealWithBoundary} {Y} {g : Y ⟶ scheme T}

section
variable (S : MarkedPullbackSquare T g)
abbrev lowerTriple : MarkedIdealWithBoundary :=
  MarkedIdealWithBoundary.mk T.base S.baseScheme S.structMap S.ideal S.mult S.boundary

abbrev upperTriple (k' : Type) [Field k']
    (q : Y ⟶ Sp k') (E : List S.topScheme.IdealSheafData) :
    MarkedIdealWithBoundary :=
  withBoundary (S.lowerTriple.pbOF (S.top ≫ q) S.left) E

section
variable (hT : IsAdmissible T) (hg : OrderAtPullbackInvariant T g) (A : S.baseScheme.IdealSheafData)
include hT hg
theorem orderAt_comap_verticalMap (y : ↥S.topScheme) :
    orderAt (comap A S.left) y = orderAt A (S.left.base y) := by
  have hval :
      tAd $ MarkedIdealWithBoundary.mk T.base S.baseScheme S.structMap S.ideal T.mult S.boundary :=
    { charZero := S.valid.charZero
      locallyOfFiniteType := S.valid.locallyOfFiniteType
      nonzeroOnComponents := S.valid.nonzeroOnComponents
      one_le_mult := hT.one_le_mult
      quasiCompact := S.valid.quasiCompact
      smooth := S.valid.smooth
      snc := S.valid.snc }
  exact hg S.baseScheme S.bottom S.structMap S.ideal S.boundary hval S.bottom_structMap
    S.topScheme S.left S.top S.isPullback A y

theorem orderAt_comap_verticalMap_le c
    (hA : ∀ x : ↥S.baseScheme, orderAt A x ≤ c) y :
    orderAt (comap A S.left) y ≤ c := by
  rw [S.orderAt_comap_verticalMap hT hg A y]
  exact hA $ S.left.base y
end

theorem flat_verticalMap [Flat g] :
    Flat S.left :=
  of_isPullback
    (P := @Flat) S.isPullback.flip ‹Flat g›
end

end MarkedPullbackSquare

def NonMonomialPartBaseChange (T : MarkedIdealWithBoundary) {Y : Sch} (g : Y ⟶ scheme T)
    (k' : Type) [Field k'] (q : Y ⟶ Sp k') : Prop :=
  ∀ (S : MarkedPullbackSquare T g) (E : List S.topScheme.IdealSheafData),
    SameNontrivialBoundary (List.map (fun D => comap D S.left) S.boundary) E →
    IsAdmissible (S.upperTriple k' q E) →
      nonMonomialPart E (S.ideal.comap S.left)
        = comap (nonMonomialPart S.boundary S.ideal) S.left

def PrincipalizationBaseChange (F : PrincipalizationAssignment) (n : ℕ) (T : MarkedIdealWithBoundary) {Y : Sch}
    (g : Y ⟶ T.scheme) (k' : Type) [Field k'] (q : Y ⟶ Sp k') : Prop :=
  ∀ (S : MarkedPullbackSquare T g),
    (∀ x : ↥S.baseScheme, orderAt S.ideal x ≤ (S.mult : ENat)) →
    ∀ (E : List S.topScheme.IdealSheafData),
      SameNontrivialBoundary (List.map (fun D => comap D S.left) S.boundary) E →
      (S.upperTriple k' q E).IsAdmissible →
      krullDimSucc S.topScheme ≤ n →
        IsPullbackBlowupSequence S.left (F $ S.upperTriple k' q E).toSequenceOfBlowups (F S.lowerTriple).toSequenceOfBlowups

def MonomialPrincipalizationBaseChange (ta_ : ComapIsoInvariance) (T : MarkedIdealWithBoundary) {Y : Sch}
    (g : Y ⟶ scheme T) (k' : Type) [Field k'] (q : Y ⟶ Sp k') : Prop :=
  ∀ (S : MarkedPullbackSquare T g),
    IsLocallyMonomialTriple S.lowerTriple →
    ∀ (E : List S.topScheme.IdealSheafData),
      SameNontrivialBoundary (List.map (fun D => comap D S.left) S.boundary) E →
      IsLocallyMonomialTriple (S.upperTriple k' q E) →
        IsPullbackBlowupSequence S.left
          (monomialPrincipalization ta_ $ S.upperTriple k' q E).toSequenceOfBlowups
          (monomialPrincipalization ta_ S.lowerTriple).toSequenceOfBlowups

structure BaseChangeCompatible (ta_ : ComapIsoInvariance) (F : PrincipalizationAssignment) (n : ℕ)
    (T : MarkedIdealWithBoundary) {Y : Sch} (g : Y ⟶ scheme T) (k' : Type) [Field k']
    (q : Y ⟶ Sp k') : Prop where
  rule : PrincipalizationBaseChange F n T g k' q
  flat : Flat g
  monomialBody : MonomialPrincipalizationBaseChange ta_ T g k' q
  nonMonomial : NonMonomialPartBaseChange T g k' q
  order : OrderAtPullbackInvariant T g





structure MonomialPrincipalizationHypotheses (hinv : ComapIsoInvariance) : Prop where
  cert : ∀ T : MarkedIdealWithBoundary, IsLocallyMonomialTriple T →
    ∀ i < (monomialPrincipalization hinv T).length,
      PrincipalizationCertificate ((monomialPrincipalization hinv T).schemeAt i)
        ((monomialPrincipalization hinv T).projectionToSpec i)
        ((monomialPrincipalization hinv T).ideal i) T.mult
        ((monomialPrincipalization hinv T).boundaryLocus i)
        ((monomialPrincipalization hinv T).center i)
  center_nonempty : ∀ T : MarkedIdealWithBoundary, IsLocallyMonomialTriple T →
    ∀ i < (monomialPrincipalization hinv T).length,
      (((monomialPrincipalization hinv T).center i).support :
        Set ↥((monomialPrincipalization hinv T).schemeAt i)).Nonempty
  resolves : ∀ T : MarkedIdealWithBoundary, IsLocallyMonomialTriple T →
    IsResolution (monomialPrincipalization hinv T)
  trivial_of_coSupport_empty : ∀ T : MarkedIdealWithBoundary, IsLocallyMonomialTriple T →
    orderAtLeastLocus T.ideal T.mult = ∅ → (monomialPrincipalization hinv T).length = 0

theorem orderAtLeastLocus_comap_eqToHom_eq_empty {A B : Sch} (h : A = B) (J : ISD B)
    (c : ℕ) (hJ : orderAtLeastLocus J c = ∅) : orderAtLeastLocus (comap J $ eqToHom h) c = ∅ := by
  rw [orderAtLeastLocus_comap_eqToHom, hJ, preimage_empty]

section
variable (hinv : ComapIsoInvariance)
include hinv
theorem orderAtLeastLocus_eq_empty_of_comap_iso_hom_eq_empty {A B : Sch}
    (e : A ≅ B) (J : ISD B) c
    (h : orderAtLeastLocus (comap J e.hom) c = ∅) : orderAtLeastLocus J c = ∅ := by
  rw [hinv.coSupport_comap] at h
  have hb : ∀ y, (isoH e) ((isoI e) y) = y := by simp_all
  rw [← not_nonempty_iff_eq_empty]
  rintro ⟨y, hy⟩
  have hmem : (isoI e) y ∈ hom e ⁻¹' orderAtLeastLocus J c := by
    simp [mem_preimage, hb y]
    exact hy
  rw [h] at hmem
  simp at hmem

section
variable (T : MarkedIdealWithBoundary) (f : PrincipalizationAssignment)
theorem orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty (h : orderAtLeastLocus T.ideal T.mult = ∅) :
    (orderReductionSeq hinv T $ principalizationOfDimLe T f).length = 0 := by
  simp [orderReductionSeq, h, emptyMarkedSequenceOfBlowups_length]

abbrev orderReductionMonomialTriple : MarkedIdealWithBoundary :=
  tripleAtLength T (companionIdealReduction hinv T $ principalizationOfDimLe T f)
    ((companionIdealReduction hinv T $ principalizationOfDimLe T f).ideal (companionIdealReduction hinv T $ principalizationOfDimLe T f).length) T.mult

abbrev orderReductionMonomialSequence :
    MarkedBlowupSequenceData
      ((companionIdealReduction hinv T $ principalizationOfDimLe T f).proj (companionIdealReduction hinv T $ principalizationOfDimLe T f).length ≫ T.structMap)
      ((companionIdealReduction hinv T $ principalizationOfDimLe T f).ideal (companionIdealReduction hinv T $ principalizationOfDimLe T f).length) T.mult
      ((companionIdealReduction hinv T $ principalizationOfDimLe T f).boundary (companionIdealReduction hinv T $ principalizationOfDimLe T f).length) :=
  ofMarkedSequence $ monomialPrincipalization hinv $ orderReductionMonomialTriple hinv T f

end
end

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
section
variable (s : MarkedSequenceOfBlowups p I m E)
theorem hasPrincipalizationCenter_ofMarkedSequence i
    (hne : ((support (s.center i) : CSet $ s.schemeAt i)).Nonempty)
    (hc : PrincipalizationCertificate (s.schemeAt i) (s.projectionToSpec i) (s.ideal i) m (s.boundaryLocus i) $ s.center i) :
    HasPrincipalizationCenter m $ (ofMarkedSequence s).dataAt i := by
  constructor
  exact hne
  rwa [boundarySupport_dataAt]

theorem lt_length_of_lt_ofMarkedSequence_length i
    (hi : i < (ofMarkedSequence s).length) : i < s.length :=by simp_all
theorem orderAtLeastLocus_ofMarkedSequence_last_eq_empty c (h : orderAtLeastLocus (s.ideal s.length) c = ∅) :
    orderAtLeastLocus ((ofMarkedSequence s).ideal
      (ofMarkedSequence s).length) c = ∅ := by
  rwa [ofMarkedSequence_length, ofMarkedSequence_ideal]
end

theorem orderAtLeastLocus_ideal_congr
    (d : MarkedBlowupSequenceData p I m E) i j (h : i = j) c
    (hh : orderAtLeastLocus (d.ideal i) c = ∅) : orderAtLeastLocus (d.ideal j) c = ∅ := by
  subst h
  exact hh

theorem orderAtLeastLocus_append_last_eq_empty
    (hinv : ComapIsoInvariance) (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length)
    (ht : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus ((s.append t hinv).ideal (s.append t hinv).length) m = ∅ := by
  have hlen :=
    append_length s t hinv
  rcases m73 t.length with h0 | hpos
  refine orderAtLeastLocus_ideal_congr (s.append t hinv) s.length (s.append t hinv).length
    (by omega) m ?_
  rw [append_ideal, appendIdeal_of_le_length s t $ le_refl s.length]
  refine orderAtLeastLocus_comap_eqToHom_eq_empty _ _ _ ?_
  have ht0 :=
    orderAtLeastLocus_ideal_congr t t.length 0 h0 m ht
  rw [t.ideal_zero] at ht0
  exact orderAtLeastLocus_eq_empty_of_comap_iso_hom_eq_empty hinv t.isoZero _ _ ht0
  refine orderAtLeastLocus_ideal_congr (s.append t hinv) (s.length + t.length)
    (s.append t hinv).length hlen.symm m ?_
  rw [append_ideal_length_add_length s t hinv hpos]
  exact orderAtLeastLocus_comap_eqToHom_eq_empty _ _ _ ht
end

section
variable (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance) (hmon : MonomialPrincipalizationHypotheses hinv) {n} {A B} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
include hG hmon hspec hT hdim
section
variable (i : ℕ)
theorem hasCenter_orderReductionData (hi : i < (orderReductionData hinv T (principalizationOfDimLe T A)).length) :
    HasPrincipalizationCenter T.mult $ (orderReductionData hinv T $ principalizationOfDimLe T A).dataAt i := by
  let _a1 := principalizationOfDimLe T A
  let _c0 := companionIdealReduction hinv T _a1
  have hlocMon := isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim
  rw [orderReductionData_eq hinv T _a1] at hi ⊢
  refine append_dataAt_of_forall _ _ hinv (HasPrincipalizationCenter T.mult)
    (isInvariantUnderIso_hasPrincipalizationCenter hG.maxContactTransport T.mult)
    (hasCenter_companionIdealReduction hG hinv hspec hT hdim) ?_ i hi
  intro j hj
  let _a0 := monomialPrincipalization hinv $ tripleAtLength T _c0 (lastI _c0) T.mult
  have hj' := lt_length_of_lt_ofMarkedSequence_length
    _a0
    j hj
  exact hasPrincipalizationCenter_ofMarkedSequence
    _a0
    j
    (hmon.center_nonempty _ hlocMon j hj')
    (hmon.cert _ hlocMon j hj')

section
variable (hi : i < (orderReductionSeq hinv T (principalizationOfDimLe T A)).length)
include hi
theorem center_support_nonempty_orderReductionSeq :
    (((orderReductionSeq hinv T $ principalizationOfDimLe T A).center i).support :
      Set ↥((orderReductionSeq hinv T $ principalizationOfDimLe T A).schemeAt i)).Nonempty := by
  let _a0 := principalizationOfDimLe T A
  by_cases hne : (orderAtLeastLocus T.ideal T.mult).Nonempty
  rw [orderReductionSeq_eq_of_nonempty hinv T _a0 hne] at hi ⊢
  exact (nonempty_center_and_certificate_of_hasPrincipalizationCenter (orderReductionData hinv T _a0) T.mult
    (hasCenter_orderReductionData hG hinv hmon hspec hT hdim)).1 i hi
  exact absurd (orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A
    (mp_ not_nonempty_iff_eq_empty hne)) $ by omega

theorem certificate_orderReductionSeq :
    PrincipalizationCertificate ((orderReductionSeq hinv T $ principalizationOfDimLe T A).schemeAt i)
      ((orderReductionSeq hinv T $ principalizationOfDimLe T A).projectionToSpec i)
      ((orderReductionSeq hinv T $ principalizationOfDimLe T A).ideal i) T.mult
      ((orderReductionSeq hinv T $ principalizationOfDimLe T A).boundaryLocus i)
      ((orderReductionSeq hinv T $ principalizationOfDimLe T A).center i) := by
  let _a0 := principalizationOfDimLe T A
  by_cases hne : (orderAtLeastLocus T.ideal T.mult).Nonempty
  rw [orderReductionSeq_eq_of_nonempty hinv T _a0 hne] at hi ⊢
  exact (nonempty_center_and_certificate_of_hasPrincipalizationCenter (orderReductionData hinv T _a0) T.mult
    (hasCenter_orderReductionData hG hinv hmon hspec hT hdim)).2 i hi
  exact absurd (orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A
    (mp_ not_nonempty_iff_eq_empty hne)) $ by omega
end
end

theorem isResolution_orderReductionSeq :
    IsResolution $ orderReductionSeq hinv T $ principalizationOfDimLe T A := by
  by_cases hne : (orderAtLeastLocus T.ideal T.mult).Nonempty
  have hlocMon := isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim
  have hres := hmon.resolves _ hlocMon
  rw [isResolution_iff, lastIdeal_eq] at hres
  let _a0 := principalizationOfDimLe T A
  rw [orderReductionSeq_eq_of_nonempty hinv T _a0 hne, isResolution_iff,
    lastIdeal_eq, toMarkedSequence_length,
    toMarkedSequence_ideal, orderReductionData_eq hinv T _a0]
  exact orderAtLeastLocus_append_last_eq_empty hinv _ _ $ orderAtLeastLocus_ofMarkedSequence_last_eq_empty _ T.mult hres
  rw [isResolution_iff, lastIdeal_eq,
    orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A
      (mp_ not_nonempty_iff_eq_empty hne),
    ideal_zero, hinv.coSupport_comap,
    not_nonempty_iff_eq_empty.mp hne, preimage_empty]
end





theorem SequenceOfBlowups.isomorphic_of_length_eq_zero {X : Sch} (B B' : SequenceOfBlowups X)
    (h : B.length = 0) (h' : B'.length = 0) : B.Isomorphic B' := by
  have hl : (ofSequenceOfBlowups B).length = 0 := by simp_all
  have hl' : (ofSequenceOfBlowups B').length = 0 := by simp_all
  have hz : ∀ i, i ≤ (ofSequenceOfBlowups B).length → i = 0 := by simp_all
  have hrfl1 : ∀ p : (ofSequenceOfBlowups B).obj 0 = (ofSequenceOfBlowups B).obj 0,
      eqToIso p = Iso.refl ((ofSequenceOfBlowups B).obj 0) := fun _ => rfl
  have hrfl2 : ∀ p : (ofSequenceOfBlowups B').obj 0 = (ofSequenceOfBlowups B').obj 0,
      eqToIso p = Iso.refl ((ofSequenceOfBlowups B').obj 0) := fun _ => rfl
  have key : (ofSequenceOfBlowups B).toSequenceOfBlowups.Isomorphic (ofSequenceOfBlowups B').toSequenceOfBlowups := by
    refine toSequenceOfBlowups_isomorphic_of_iso (ofSequenceOfBlowups B) (ofSequenceOfBlowups B')
      (by rw [hl, hl'])
      (fun i hi => eqToIso (congrArg (ofSequenceOfBlowups B).obj $ hz i hi) ≪≫
        (ofSequenceOfBlowups B).isoZero ≪≫ (ofSequenceOfBlowups B').isoZero.symm ≪≫
          eqToIso (congrArg (ofSequenceOfBlowups B').obj (hz i hi).symm)) ?_ ?_ ?_
    simp_all
    simp_all
    simp_all
  exact ((ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic B).symm.trans key).trans $ ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic B'

theorem principalizationAssignment_mk_isomorphic (f : PrincipalizationAssignment) (T : MarkedIdealWithBoundary)
    (p : scheme T ⟶ Sp T.base) (I : T.scheme.IdealSheafData) (m : ℕ)
    (E : List T.scheme.IdealSheafData) (hp : p = structMap T) (hI : I = ideal T)
    (hm : m = mult T) (hE : E = boundary T) :
    (f { base := tBs T, instField := T.instField, scheme := tSch T, structMap := p,
          ideal := I, mult := m, boundary := E }).toSequenceOfBlowups.Isomorphic (f T).toSequenceOfBlowups := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact isomorphic_refl _

private theorem orderAtLeastLocus_append_eq_empty {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length)
    (hinv : ComapIsoInvariance) (ht : 0 < t.length)
    (h : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus ((s.append t hinv).ideal (s.append t hinv).length) m = ∅ := by
  rw [append_length s t hinv, append_ideal_length_add_length s t hinv ht]
  exact orderAtLeastLocus_comap_eqToHom_eq_empty _ _ _ h

theorem orderReductionSeq_isomorphic_of_boundary_nil (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance)
    (hmon : MonomialPrincipalizationHypotheses hinv) {n : ℕ} {A B : PrincipalizationAssignment}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (hE : T.boundary = [])
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ENat)) :
    (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.Isomorphic (A T).toSequenceOfBlowups := by
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  exact SequenceOfBlowups.isomorphic_of_length_eq_zero _ _
    (orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A hcs)
    (hspec.trivial_of_coSupport_empty T hT hdim hord hcs)
  obtain ⟨x1_, hx1_⟩ : (orderAtLeastLocus T.ideal T.mult).Nonempty := mpr_ nonempty_iff_ne_empty hcs
  have : Nonempty T.scheme := ⟨x1_⟩
  obtain ⟨x0_, hx0_⟩ := exists_orderAt_eq_maxOrder T.ideal hord
  have hmax : maxOrder T.ideal = T.mult := by
    refine le_antisymm ?_ ?_
    have h := hord x0_
    rw [hx0_] at h
    exact_mod_cast h
    have h1 := hx1_
    have h2 := orderAt_le_maxOrder T.ideal hord x1_
    have h3 := le_trans h1 h2
    exact_mod_cast h3
  let _a4 := lastNonMonomialPart T (T.embs)
  have hJ0 : _a4
      = T.ideal :=
    hG.nonMonomialPart_eq_ideal_of_boundary_eq_nil T hT hE
  have hmu0 : maxOrderNonMonomial T (T.embs)
      = T.mult := by
    have h := congrArg maxOrder hJ0
    exact tr_ h hmax
  have hmem : ((maxOrderNonMonomial T (T.embs) : ℕ) : ENat)
      ≤ orderAt _a4 x1_ := by
    rwa [hmu0, hJ0]
  have hcont : NonMonomialOrderReductionContinues T (T.embs) :=
    ⟨le_of_eq hmu0.symm, ⟨x1_, hmem⟩⟩
  have hlt := maxOrderNonMonomial_extendByNonMonomialPart_lt hG hinv hspec hT hdim
    (T.embs) hcont
  rw [hmu0] at hlt
  have hnot : ¬ NonMonomialOrderReductionContinues T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
      (T.embs)) := by
    intro hc
    have h1 := hc.1
    omega
  have hzero : nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) 0
      = T.embs := by
    simp only [nonMonomialOrderReductionIter]
  have hstepc : ∀ j, NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j) →
      nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (j + 1)
        = extendByNonMonomialPart hinv T (principalizationOfDimLe T A) (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j) := by
    intro j hj
    simp only [nonMonomialOrderReductionIter]
    split_ifs with h
    rfl
    exact absurd hj h
  have hstepn : ∀ j, ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j) →
      nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (j + 1) = nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j := by
    intro j hj
    simp only [nonMonomialOrderReductionIter]
    split_ifs with h
    exact absurd h hj
    rfl
  have hloop : ∀ j, nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (j + 1)
      = extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
          (T.embs) := by
    intro j
    induction j with
    | zero =>
        rw [hstepc 0 (by rw [hzero]; exact hcont), hzero]
    | succ j ih =>
        rw [hstepn (j + 1) (by rw [ih]; exact hnot), ih]
  have hnonMonomialEq : nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)
      = extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
          (T.embs) := by
    simp only [nonMonomialOrderReduction]
    exact hloop _
  have hconcat := extendByNonMonomialPart_eq_append hG hinv hspec hT hdim
    (T.embs) hcont
  have ht1pos : 0 < (continuationByNonMonomialPart hG hspec hT hdim
      (T.embs) hcont).length := by
    rw [continuationByNonMonomialPart_length hG hspec hT hdim _ hcont]
    exact seqAtEnd_lastNonMonomialPart_length_pos hG hspec hT hdim _ hcont
  have hcong : ∀ (Y : Sch) (d : BlowupSequenceData Y) (I1 I2 : ISD Y) (m1 m2 j : ℕ),
      I1 = I2 → m1 = m2 → d.controlledTransform I1 m1 j = d.controlledTransform I2 m2 j := by simp_all
  have hcs2 : ∀ (Y : Sch) (Jy : ISD Y) (m1 m2 : ℕ), m1 = m2 →
      orderAtLeastLocus Jy m1 = ∅ → orderAtLeastLocus Jy m2 = ∅ := by simp_all
  have hboundaryLast : (nonMonomialTriple T (T.embs)).IsOrderBoundedByMult := by
    rw [MarkedIdealWithBoundary.IsOrderBoundedByMult.eq_def]
    intro x
    exact orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT
      (T.embs) x
  have hlocus : orderAtLeastLocus
      ((A (nonMonomialTriple T (T.embs))).ideal
        (A (nonMonomialTriple T
          (T.embs))).length) T.mult = ∅ := by
    have h := mp_ (isResolution_iff _) (hspec.resolves _ (isAdmissible_nonMonomialTriple hG hT _ hcont) (le_trans (tripleAtLength_dim_le hG hT _ _ _) hdim) hboundaryLast)
    rw [lastIdeal_eq] at h
    exact hcs2 _ _ _ _ hmu0 h
  have hid : (continuationByNonMonomialPart hG hspec hT hdim
        (T.embs) hcont).ideal
      (continuationByNonMonomialPart hG hspec hT hdim
        (T.embs) hcont).length
      = (A (nonMonomialTriple T (T.embs))).ideal
        (A (nonMonomialTriple T
          (T.embs))).length := by
    have h1 := toBlowupSequenceData_controlledTransform_eq
      (ofMarkedSequence
        (A (nonMonomialTriple T (T.embs))))
      (A (nonMonomialTriple T (T.embs))).length
      (le_of_eq (ofMarkedSequence_length _).symm)
    have h2 := ofMarkedSequence_ideal
      (A (nonMonomialTriple T (T.embs)))
      (A (nonMonomialTriple T (T.embs))).length
    have h3 := hcong _
      (ofMarkedSequence
        (A (nonMonomialTriple T
          (T.embs)))).toBlowupSequenceData
      ((T.embs).ideal
        (T.embs).length)
      _a4
      T.mult (maxOrderNonMonomial T (T.embs))
      (A (nonMonomialTriple T (T.embs))).length
      hJ0.symm hmu0.symm
    exact tr_ h3 $ tr_ h1 h2
  have hG1 := hlocus
  rw [← hid] at hG1
  have hG2 : orderAtLeastLocus ((extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
        (T.embs)).ideal
      (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
        (T.embs)).length) T.mult = ∅ := by
    rw [hconcat]
    exact orderAtLeastLocus_append_eq_empty _ _ hinv ht1pos hG1
  have hmaxOn : ∀ (Y : Sch) (N : ISD Y),
      maxOrderOn N (∅ : Set Y) = 0 := by
    intro Y N
    rw [maxOrderOn.eq_def]
    simp
  have hnc2 : ¬ CompanionIdealReductionContinues T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
      (T.embs)) := by
    intro hc
    have h1 : 1 ≤ maxOrderOn
        (lastNonMonomialPart T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
          (T.embs)))
        (orderAtLeastLocus ((extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
          (T.embs)).ideal
          (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
            (T.embs)).length) T.mult) := hc
    rw [hG2, hmaxOn] at h1
    omega
  have hnc2' := hnc2
  rw [← hnonMonomialEq] at hnc2'
  have hcompanionStep : ∀ s j,
      ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s j) →
      companionIdealReductionIter hinv T (principalizationOfDimLe T A) s (j + 1)
        = companionIdealReductionIter hinv T (principalizationOfDimLe T A) s j := by
    intro s j hj
    simp only [companionIdealReductionIter]
    split_ifs with h
    exact absurd h hj
    rfl
  have hcompanionIter : ∀ j, companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) j
      = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) := by
    intro j
    induction j with
    | zero => simp only [companionIdealReductionIter]
    | succ j ih =>
        rw [hcompanionStep _ j (by rw [ih]; exact hnc2'), ih]
  have hcompanionEq : companionIdealReduction hinv T (principalizationOfDimLe T A) = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) := by
    simp only [companionIdealReduction]
    exact hcompanionIter _
  have hG3 := hG2
  rw [← hnonMonomialEq, ← hcompanionEq] at hG3
  have hmonomialLen : (orderReductionMonomialSequence hinv T A).length = 0 := by
    show (ofMarkedSequence
      (monomialPrincipalization hinv (orderReductionMonomialTriple hinv T A))).length = 0
    rw [ofMarkedSequence_length]
    exact hmon.trivial_of_coSupport_empty _
      (isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim) hG3
  have hAlg : orderReductionSeq hinv T (principalizationOfDimLe T A)
      = (orderReductionData hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups := by
    unfold orderReductionSeq
    rw [if_neg hcs]
  rw [hAlg]
  have e1 : ((orderReductionData hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups).toSequenceOfBlowups.Isomorphic
      ((companionIdealReduction hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups).toSequenceOfBlowups := by
    rw [orderReductionData_eq hinv T (principalizationOfDimLe T A)]
    exact append_isomorphic_of_length_eq_zero _ _ hinv hmonomialLen
  have e2 : ((companionIdealReduction hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups).toSequenceOfBlowups.Isomorphic
      ((continuationByNonMonomialPart hG hspec hT hdim
        (T.embs)
        hcont).toMarkedSequenceOfBlowups).toSequenceOfBlowups := by
    rw [hcompanionEq, hnonMonomialEq, hconcat]
    exact emptyMarkedBlowupSequenceData_append_isomorphic T.structMap T.ideal T.mult T.boundary _ hinv
  have e3 : ((continuationByNonMonomialPart hG hspec hT hdim
        (T.embs)
        hcont).toMarkedSequenceOfBlowups).toSequenceOfBlowups.Isomorphic
      (A (nonMonomialTriple T
        (T.embs))).toSequenceOfBlowups := by
    simp only [continuationByNonMonomialPart, toMarkedBlowupSequenceData_toSequenceOfBlowups,
      blowupSequenceData_ofMarkedSequence]
    exact ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _
  have e4 :=
    principalizationAssignment_mk_isomorphic A T
      ((T.embs).proj
        (T.embs).length ≫ T.structMap)
      _a4
      (maxOrderNonMonomial T (T.embs))
      ((T.embs).boundary
        (T.embs).length)
      (by rw [emptyMarkedBlowupSequenceData_projectionToBase, id_comp]) hJ0 hmu0 rfl
  exact e1.trans $ e2.trans (e3.trans e4)





namespace DivisorReduction

private theorem map_comap_id {W : Sch} l :
    List.map (fun D : ISD W => comap D $ 𝟙 W) l = l :=by simp_all
theorem residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor {X Y : Sch} (g : Y ⟶ X)
    (A F : ISD X) (F' : ISD Y) (m : ℕ) (hF' : F' = comap F g)
    (hcart : IsLocallyGeneratedByNonZeroDivisor F') (hex : ∃ B : ISD X, F ^ m * B = A) :
    residualByPow (comap A g) F' m = comap (residualByPow A F m) g := by
  have hup : F' ^ m * cmI (residualByPow A F m) g = cmI A g := by
    rw [hF', ← comap_pow, ← comap_mul, pow_mul_residualByPow A F m hex]
  exact (hcart.pow m).eq_of_mul_eq_mul $ tr_ (pow_mul_residualByPow (cmI A g) F' m ⟨_, hup⟩) hup.symm

section
variable (htwist : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T → (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) → ∀ (j : ℕ) (hj : j < T.boundary.length), ∃ B : tISD T, B * ccI hj ^ T.mult = ideal T) (hblow : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T → ∀ (j : ℕ) (hj : j < T.boundary.length), IsBlowupAlongIdealSheaf (𝟙 T.scheme) (ccI hj))
include htwist hblow
theorem lowerIdealAfterBlowup_pullbackAlong_of_smooth :
    ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
        [Smooth h], h ≫ structMap T = q →
        ∀ (E' : Bdy Y),
          SameNontrivialBoundary (T.pbA q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < length E'),
            take (j + 1) E' = take (j + 1) (T.pbA q h).boundary →
            IsAdmissible (T.pbB q h E') →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal (T.pbB q h E') j hjE = comap (ccI hj) h →
              lowerIdealAfterBlowup (T.pbB q h E') j hjE =
                comap (lI hj) h := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  have hex : ∃ B, ccI hj ^ tMu T * B = tId T := by
    obtain ⟨B, hB⟩ := htwist T hV ((isOrderBoundedByMult_iff T).1 hO) j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  let _m0 := pbBT T q h E'
  let _a0 := containedComponentsIdeal _m0 j hjE
  have hcart : p17 _a0 := by
    have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal $ hblow _m0 hV' j hjE
    rwa [p9, comap_id] at hc
  have key := residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor h T.ideal (ccI hj)
      _a0 T.mult hpre hcart hex
  simp [lI, lowerIdealAfterBlowup, p9, comap_id]
  exact key

theorem lowerIdealAfterBlowup_fieldBaseChange
    (T : MarkedIdealWithBoundary) (hV : IsAdmissible T)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    (j : ℕ) (hj : j < T.boundary.length) (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (bc T f).scheme.IdealSheafData)
    (_hBE : SameNontrivialBoundary E' (bc T f).boundary)
    (hjE : j < length E')
    (_htake : take (j + 1) E' = take (j + 1) (bc T f).boundary)
    (hV' : (withBoundary (bc T f) E').IsAdmissible)
    (hpre : containedComponentsIdeal (withBoundary (bc T f) E') j hjE =
      comap (ccI hj) (fBCP T f)) :
    lowerIdealAfterBlowup (withBoundary (bc T f) E') j hjE =
      comap (lI hj) (fBCP T f) := by
  have hex : ∃ B, ccI hj ^ tMu T * B = tId T := by
    obtain ⟨B, hB⟩ := htwist T hV hO j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  let _m0 := tWB (bcT T f) E'
  let _a0 := containedComponentsIdeal _m0 j hjE
  have hcart : p17 _a0 := by
    have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal $ hblow _m0 hV' j hjE
    rwa [p9, comap_id] at hc
  have key := residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor (fBCP T f) T.ideal
      (ccI hj)
      _a0 T.mult hpre hcart hex
  simp only [lI, lowerIdealAfterBlowup, p9, comap_id]
  exact key
end

section
variable {al_ : Type} (A : List al_)
theorem take_eraseIdx_append_singleton e j n
    (hj : j < length A) (hn : n = length A - 1) :
    take n (eraseIdx (A ++ [e]) j) = eraseIdx A j := by
  subst hn
  have hlen : length (eraseIdx A j) = lenL A - 1 := by
    rw [length_eraseIdx, if_pos hj]
  rw [eraseIdx_append_of_lt_length hj, ← hlen, take_left]

private theorem take_length_sub_one_eraseIdx j n (hj : j < length A)
    (hn : n = length A - 1) : take n (eraseIdx A j) = eraseIdx A j := by
  subst hn
  refine take_of_length_le ?_
  rw [length_eraseIdx, if_pos hj]
end

theorem sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat {X Y : Sch} g
    (hX : IsNoetherian X) (hY : IsNoetherian Y)
    (hflat : Flat g)
    (Z : ISD X) (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) Z' (hZ' : Z' = comap Z g)
    (B : Bdy X) (E : Bdy Y)
    (hBE : SameNontrivialBoundary (List.map (fun D => comap D g) B) E)
    j (hj : j < length B) (hjE : j < length E)
    (htake : take (j + 1) E = take (j + 1) (List.map (fun D => comap D g) B)) :
    SameNontrivialBoundary
      (take (length E - 1)
        ((List.map (strictTransform (𝟙 Y) Z') (List.map (fun D => comap D $ 𝟙 Y) E)
          ++ [exceptionalIdeal (𝟙 Y) Z']).eraseIdx j))
      (List.map (fun D => comap D g)
        (take (length B - 1)
          ((List.map (strictTransform (𝟙 X) Z) (List.map (fun D => comap D $ 𝟙 X) B)
            ++ [exceptionalIdeal (𝟙 X) Z]).eraseIdx j))) := by
  subst hZ'
  have hst := fun D =>
    comap_strictTransform_of_flat_of_isLocallyNoetherian (𝟙 X) g (𝟙 Y) g
      (id_vert g) Z D hZ
  let _a0 := strictTransform (𝟙 Y) $ cmI Z g
  have hcomp : List.map ((fun D : ISD X => cmI D g)
        ∘ strictTransform (𝟙 X) Z) B
      = List.map _a0
          (List.map (fun D : ISD X => cmI D g) B) := by
    rw [map_map]
    exact map_congr_left fun D _ => hst D
  rw [map_comap_id, map_comap_id,
    take_eraseIdx_append_singleton (List.map _a0 E)
      (exceptionalIdeal (𝟙 Y) $ cmI Z g) j (lenL E - 1) (by simpa using hjE) $ by simp,
    take_eraseIdx_append_singleton (List.map (strictTransform (𝟙 X) Z) B)
      (exceptionalIdeal (𝟙 X) Z) j (lenL B - 1) (by simpa using hj) $ by simp,
    ← eraseIdx_map, map_map, hcomp]
  refine sy_ $ (MarkedIdealWithBoundary.SameNontrivialBoundary.map _a0
    (strictTransform_top (𝟙 Y) $ cmI Z g) hBE).eraseIdx j ?_
  rw [← map_take, ← map_take, ← map_take, htake, map_take]

theorem top_pow {Y : Sch} m :
    (⊤ : ISD Y) ^ m = ⊤ := by
  rw [← one_eq_top, one_pow]

theorem comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup
    (htwist : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : tISD T, B * ccI hj ^ T.mult = ideal T)
    (_hblow : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      ∀ (j : ℕ) (hj : j < T.boundary.length), IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ ccI hj)
    (T : MarkedIdealWithBoundary) (hV : IsAdmissible T)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    j (hj : j < T.boundary.length) Y (h : Y ⟶ scheme T)
    (htop : comap (ccI hj) h = ⊤) :
    comap (lI hj) h = comap (lowerIdealWithoutBlowup T) h := by
  have hex : ∃ B, ccI hj ^ tMu T * B = tId T := by
    obtain ⟨B, hB⟩ := htwist T hV hO j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hup := congrArg (fun I : tISD T => cmI I h) $ pow_mul_residualByPow T.ideal (ccI hj) T.mult hex
  simp [comap_mul, comap_pow, htop,
    top_pow, top_mul] at hup
  simp [lI, lowerIdealAfterBlowup, lowerIdealWithoutBlowup, p9,
    comap_id]
  exact hup

theorem lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth
    (_htwist : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : tISD T, B * ccI hj ^ T.mult = ideal T)
    (hblow : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      ∀ (j : ℕ) (hj : j < T.boundary.length), IsBlowupAlongIdealSheaf (𝟙 T.scheme) (ccI hj)) :
    ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
        [Smooth h], h ≫ structMap T = q →
        ∀ (E' : Bdy Y),
          SameNontrivialBoundary (T.pbA q h).boundary E' →
          ∀ j (hj : j < T.boundary.length) (hjE : j < length E'),
            take (j + 1) E' = take (j + 1) (T.pbA q h).boundary →
            IsAdmissible (T.pbB q h E') →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal (T.pbB q h E') j hjE = comap (ccI hj) h →
              SameNontrivialBoundary
                (take (length E' - 1)
                  (eraseIdx (lowerBoundaryAfterBlowup (T.pbB q h E') j hjE) j))
                (List.map (fun D => comap D h)
                  (take (T.boundary.length - 1) (eraseIdx (lB hj) j))) := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  rw [pullbackAlong_boundary T Y q h] at hBE htake
  exact sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat h hV.isNoetherian hV'.isNoetherian inferInstance
    (ccI hj) (hblow T hV j hj)
    (containedComponentsIdeal (T.pbB q h E') j hjE) hpre
    T.boundary E' hBE j hj hjE htake

theorem comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top
    (_htwist : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : tISD T, B * ccI hj ^ T.mult = ideal T)
    (_hblow : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      ∀ (j : ℕ) (hj : j < T.boundary.length), IsBlowupAlongIdealSheaf (𝟙 T.scheme) (ccI hj))
    (T : MarkedIdealWithBoundary) (hV : IsAdmissible T)
    j (hj : j < T.boundary.length) Y (h : Y ⟶ scheme T)
    (htop : comap (ccI hj) h = ⊤) :
    SameNontrivialBoundary
      (List.map (fun D => comap D h)
        (take (T.boundary.length - 1) (eraseIdx (lB hj) j)))
      (List.map (fun D => comap D h)
        (take (T.boundary.length - 1) (eraseIdx (lowerBoundaryWithoutBlowup T) j))) := by
  have hnoT := hV.isNoetherian
  let _a0 := ccI hj
  have hstT : ∀ D : tISD T,
      comap (strictTransform (𝟙 T.scheme) _a0 D) h = cmI D h := by
    intro D
    have hg : comap (comap _a0 (𝟙 T.scheme)) h = ⊤ := by
      rwa [comap_id]
    rw [strictTransform_comap_of_comap_center_eq_top (𝟙 T.scheme) _a0 D h hg, comap_id]
  let _a1 := strictTransform (𝟙 T.scheme) _a0
  let _a2 := exceptionalIdeal (𝟙 T.scheme) _a0
  have hR0 : lB hj
      = List.map _a1
          (List.map (fun D : tISD T => cmI D $ 𝟙 T.scheme) T.boundary)
        ++ [_a2] := rfl
  have key : List.map (fun D : tISD T => cmI D h)
        (eraseIdx (List.map _a1 T.boundary) j)
      = List.map (fun D : tISD T => cmI D h) (T.boundary.eraseIdx j) := by
    rw [← eraseIdx_map, ← eraseIdx_map, map_map]
    congr 1
    exact map_congr_left fun D _ => hstT D
  rw [hR0, map_comap_id, lowerBoundaryWithoutBlowup_eq T,
    take_eraseIdx_append_singleton
      (List.map _a1 T.boundary)
      _a2 j (bLen T - 1)
      (by simpa using hj) (by simp),
    take_length_sub_one_eraseIdx T.boundary j (bLen T - 1) hj rfl, key]
  exact sameNontrivialBoundary_refl _

theorem lowerBoundaryAfterBlowup_fieldBaseChange
    (_htwist : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : tISD T, B * ccI hj ^ T.mult = ideal T)
    (hblow : ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      ∀ (j : ℕ) (hj : j < T.boundary.length), IsBlowupAlongIdealSheaf (𝟙 T.scheme) (ccI hj))
    (T : MarkedIdealWithBoundary) (hV : IsAdmissible T)
    (_hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    j (hj : j < T.boundary.length) (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (bc T f).scheme.IdealSheafData)
    (hBE : SameNontrivialBoundary E' (bc T f).boundary)
    (hjE : j < length E')
    (htake : take (j + 1) E' = take (j + 1) (bc T f).boundary)
    (hV' : (withBoundary (bc T f) E').IsAdmissible)
    (hpre : containedComponentsIdeal (withBoundary (bc T f) E') j hjE =
      comap (ccI hj) (fBCP T f)) :
    SameNontrivialBoundary
      (take (length E' - 1)
        (eraseIdx (lowerBoundaryAfterBlowup (withBoundary (bc T f) E') j hjE) j))
      (List.map (fun D => comap D (fBCP T f))
        (take (T.boundary.length - 1) (eraseIdx (lB hj) j))) := by
  rw [baseChange_boundary T K f] at hBE htake
  exact sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat (fBCP T f) hV.isNoetherian
    hV'.isNoetherian inferInstance
    (ccI hj) (hblow T hV j hj)
    (containedComponentsIdeal (tWB (bcT T f) E') j hjE) hpre
    T.boundary E' hBE.symm j hj hjE htake

end DivisorReduction





theorem not_natCast_add_one_le_self (n : ℕ) : ¬ ((n : ENat) + 1 ≤ (n : ENat)) := by
  rw [add_one_le_iff $ natCast_ne_top n]
  exact lt_irrefl _

section
variable {X} (d : BlowupSequenceData X) (A0 : IdealSheafData (d.obj 0)) (t : ℕ)
private def iteratedStrictTransform : IdealSheafData $ d.obj t :=
  Nat.rec (motive := fun n => IdealSheafData $ d.obj n) A0
    (fun n ih => strictTransform (d.map n) (d.center n) ih) t

end

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X} (S : MarkedSequenceOfBlowups p I m E)
theorem length_le_length_boundary n :
    n ≤ S.length → E.length ≤ (S.boundary n).length := by
  induction n with
  | zero =>
    intro _
    simp [S.boundary_zero]
  | succ n ih =>
    intro hn
    have h1 := ih $ by omega
    have h2 : (S.boundary $ n + 1).length = (S.boundary n).length + 1 := by
      rw [S.boundary_succ n $ by omega]
      simp
    omega

theorem boundary_zero_get_eq_comap j (hj : j < length E)
    (h : j < length (S.boundary 0)) :
    get (S.boundary 0) ⟨j, h⟩ = comap (E.lget j hj) S.isoZero.hom := by
  dsimp only [lget]
  rw [get_eq_getElem, get_eq_getElem, getElem_of_eq S.boundary_zero h, getElem_map]

theorem boundary_succ_get_eq_strictTransform j n (hn : n < S.length)
    (hjn : j < (S.boundary n).length) (h : j < (S.boundary $ n + 1).length) :
    get (S.boundary $ n + 1) ⟨j, h⟩ =
      strictTransform (S.transitionMapSucc n) (S.center n) (get (S.boundary n) ⟨j, hjn⟩) := by
  have hlen : j < (m39 (p6 (S.transitionMapSucc n) $ S.center n)
      (S.boundary n)).length := by simp_all
  rw [get_eq_getElem, get_eq_getElem, getElem_of_eq (S.boundary_succ n hn) h]
  simp [getElem_append_left hlen]
end

private theorem containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup (T : MarkedIdealWithBoundary) (hV : IsAdmissible T) j
    (hj : j < T.boundary.length) :
    DivisorReduction.ccI hj ^ T.mult * DivisorReduction.lI hj = ideal T := by
  obtain ⟨J, hJ⟩ := exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  have hex : exceptionalIdeal (𝟙 T.scheme) (p28 hj)
      = p28 hj := by simp_all
  have hA : comap (T.ideal.comap $ 𝟙 T.scheme) (𝟙 T.scheme) = tId T := by simp_all
  have h1 : ∃ B, exceptionalIdeal (𝟙 T.scheme) (p28 hj) ^ T.mult * B
      = comap (T.ideal.comap $ 𝟙 T.scheme) (𝟙 T.scheme) := by
    refine ⟨J, ?_⟩
    rwa [hex, hA]
  have h2 := pow_mul_residualByPow (comap (T.ideal.comap $ 𝟙 T.scheme) $ 𝟙 T.scheme)
    (exceptionalIdeal (𝟙 T.scheme) $ DivisorReduction.ccI hj) T.mult h1
  rw [hex, hA] at h2
  unfold DivisorReduction.lI DivisorReduction.lowerIdealAfterBlowup
  rwa [hex, hA]

namespace TransportedDivisor

theorem support_iteratedComap {X} (d : BlowupSequenceData X) (B : IdealSheafData (d.obj 0))
    t :
    (↑(iteratedComap d B t).support : CSet $ d.obj t) =
      ⇑(d.projectionToBase t ≫ d.isoZero.inv) ⁻¹' (↑B.support : CSet $ d.obj 0) := by
  induction t with
  | zero =>
    have h0 : d.projectionToBase 0 ≫ d.isoZero.inv = 𝟙 (d.obj 0) := by simp_all
    rw [iteratedComap_zero, h0]
    ext x
    simp [id_base]
  | succ t ih =>
    ext x
    rw [iteratedComap_succ]
    let _a0 := iteratedComap d B t
    have hmem : x ∈ (support (cmI _a0 $ d.map t) :
          Set $ d.obj $ t + 1) ↔
        d.map t x ∈ (support _a0 : CSet $ d.obj t) :=
      mem_support_comap
    rw [hmem, ih, p43, assoc]
    simp [mem_preimage]

end TransportedDivisor

namespace DivisorReduction

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian)
section
variable (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme]
section
variable (j : ℕ) (hj : j < T.boundary.length)
section
variable (I0) (E0) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups) (hpr : s.NoComp)
private theorem ambientBlowupSeq_isoObjZero_hom :
    (amb hres hno hpr).isoZero.hom = 𝟙 T.scheme :=
  congrArg hom $ ambientBlowupSequence_isoObjZero (bgetT hj).si
    s.toBsd hres hno hpr

theorem ambientBlowupSeq_isoObjZero_inv :
    (amb hres hno hpr).isoZero.inv = 𝟙 T.scheme :=
  congrArg inv $ ambientBlowupSequence_isoObjZero (bgetT hj).si
    s.toBsd hres hno hpr

theorem ambientBlowupSeq_projectionToBase_comp_isoObjZero_inv n :
    (amb hres hno hpr).projectionToBase n ≫
        (amb hres hno hpr).isoZero.inv
      = (amb hres hno hpr).projectionToBase n := by
  rw [ambientBlowupSeq_isoObjZero_inv hres hno T j hj I0 E0 s hpr]
  exact comp_id $ (amb hres hno hpr).projectionToBase n

end

section
variable (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) (ccI hj)) (s : (rTD hj).SequenceOfBlowups) (hpr : s.NoComp) (hmk : (prepend (ccI hj) hb (amb hres hno hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
include hmk
section
variable (n : ℕ)
theorem prependedAmbientSeq_blowupMorphism :
    (ppMS hres hno hmk).transitionMapSucc n =
      (prepend (ccI hj) hb
        (amb hres hno hpr)).map n :=
  toMarkedSequence_blowupMorphism
    ((prepend (ccI hj) hb
      (amb hres hno hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk) n

theorem prependedAmbientSeq_projectionToSpec_succ :
    (ppMS hres hno hmk).projectionToSpec (n + 1) =
      (amb hres hno hpr).projectionToBase n ≫
        T.structMap := by
  let _a0 := amb hres hno hpr
  let _a1 := ccI hj
  have h1 := toMarkedSequence_projectionToSpec
    ((prepend _a1 hb
      _a0).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk) $ n + 1
  have h2 := projectionToBase_prepend_succ _a1 hb
    _a0 n
  exact tr_ h1 $ congrArg (fun f => f ≫ tMp T) h2
end

theorem prependedAmbientSeq_length :
    (ppMS hres hno hmk).length = s.length + 1 := by
  have h1 : (prepend (ccI hj) hb
      (amb hres hno hpr)).length
      = s.length + 1 := by
    rw [prepend_length,
      ambientBlowupSeq_length hres hno T j hj (lI hj) (lB hj) s hpr]
  exact h1

theorem prependedAmbientSeq_blowupMorphism_zero :
    (ppMS hres hno hmk).transitionMapSucc 0 = 𝟙 T.scheme := by
  rw [prependedAmbientSeq_blowupMorphism hres hno T j hj hb s hpr hmk 0, prepend_blowupMorphism_zero]
  exact ambientBlowupSeq_isoObjZero_hom hres hno T j hj (lI hj) (lB hj) s hpr

theorem prependedAmbientSeq_isoObjZero_hom :
    (ppMS hres hno hmk).isoZero.hom = 𝟙 T.scheme :=
  congrArg hom $ prepend_isoObjZero (ccI hj) hb
    (amb hres hno hpr)

theorem prependedAmbientSeq_boundary_succ_get :
    ∀ n, n ≤ s.length →
      ∀ h : j < ((ppMS hres hno hmk).boundary $ n + 1).length,
        get ((ppMS hres hno hmk).boundary $ n + 1) ⟨j, h⟩ =
          iteratedStrictTransform
            (amb hres hno hpr)
            (strictTransform (𝟙 T.scheme) (ccI hj)
              ((T.bget j hj).comap $ 𝟙 T.scheme)) n := by
  let _a3 := (prepend (ccI hj) hb $ amb hres hno hpr).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk
  let _a1 := ccI hj
  let _a2 := amb hres hno hpr
  let _a0 := prependedAmbientSeq_length hres hno T j hj hb s hpr hmk
  let _c0 := ppMS hres hno hmk
  intro n
  induction n with
  | zero =>
    intro _ h
    have hz0 :=
      lt_of_lt_of_le hj
        (length_le_length_boundary _c0 0 $ zero_le _)
    rw [boundary_succ_get_eq_strictTransform _c0 j 0
        (by rw [_a0]; omega) hz0 h,
      boundary_zero_get_eq_comap _c0 j hj hz0,
      prependedAmbientSeq_isoObjZero_hom hres hno T j hj hb s hpr hmk,
      prependedAmbientSeq_blowupMorphism_zero hres hno T j hj hb s hpr hmk,
      (toMarkedSequence_center
    _a3 0).trans
    (prepend_center_zero _a1 hb
      _a2)]
    rfl
  | succ n ih =>
    intro hn h
    have hn1 :=
      lt_of_lt_of_le hj $ length_le_length_boundary _c0 (n + 1)
        (by rw [_a0]; omega)
    rw [boundary_succ_get_eq_strictTransform _c0 j (n + 1)
        (by rw [_a0]; omega) hn1 h,
      ih (by omega) hn1,
      (prependedAmbientSeq_blowupMorphism hres hno T j hj hb s hpr hmk $ n + 1).trans
    (prepend_blowupMorphism_succ _a1 hb
      _a2 n),
      (toMarkedSequence_center
    _a3 $ n + 1).trans
    (prepend_center_succ _a1 hb
      _a2 n)]
    rfl
end
end

end

theorem isSmoothDivisor_ker_embeddingIntoAmbient (_hgeom : OrderAtComapOffExceptionalLocus)
    (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ENat))
    j (hj : j < T.boundary.length)
    (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) (ccI hj))
    (hlow : (rTD hj).IsAdmissible)
    (s : (rTD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (prepend (ccI hj) hb
        (amb hres hno hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (hcomp : ∀ t ≤ s.length,
      embA hres hno hpr t ≫
          (amb hres hno hpr).projectionToBase t =
        (ofMarkedSequence s).proj t ≫ (T.bget j hj).si) :
    ∀ t ≤ s.length,
      IsSmoothDivisor ((ppMS hres hno hmk).projectionToSpec (t + 1))
        (ker
          (embA hres hno hpr t)) := by
  let _a6 := ppMS hres hno hmk
  let _a7 := amb hres hno hpr
  let _a8 := prependedAmbientSeq_length hres hno T j hj hb s hpr hmk
  let _a0 := lI hj
  let _a1 := lB hj
  let _a2 := bget' hj
  let _a3 := _a6
  let _a4 := _a8
  let _c0 := _a7
  classical
  have := hV.charZero
  have := hV.smooth
  have hL :=
    le_of_eq (ambientBlowupSeq_length hres hno T j hj _a0
      _a1 s hpr).symm
  have hnoeth : ∀ t, t ≤ s.length → IsLocallyNoetherian
      (_c0.obj t) := by
    intro t htt
    have : IsNoetherian
        (_c0.obj t) :=
      isNoetherian_ambientBlowupSequence_schemeAt _a2.si
        s.toBsd hres hno hpr t
        (le_of_le_of_eq htt (ofMarkedSequence_length s).symm)
    infer_instance
  have hsm : ∀ t, t ≤ s.length → Smooth
      (_c0.projectionToBase t ≫
        T.structMap) := by
    intro t htt
    have h1 := smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV
      _a3 (t + 1)
      (by rw [_a4]; omega)
    rwa [prependedAmbientSeq_projectionToSpec_succ hres hno T j hj hb s hpr hmk t] at h1
  intro t ht
  rw [prependedAmbientSeq_projectionToSpec_succ hres hno T j hj hb s hpr hmk t]
  let _a5 := ccI hj
  refine TransportedDivisor.isSmoothDivisor_strictTransform_of_disjoint_center T.structMap
    _c0
    s.length hL hnoeth hsm
    (fun n => ker
      (embA hres hno hpr n))
    (iteratedStrictTransform
      _c0
      (p6 (𝟙 tSch T) _a5
        (cmI _a2 (𝟙 T.scheme))))
    _a5 ?_ (DivisorReductionBoundary.disjoint_support_strictTransform_containedComponentsIdeal T hV j hj) ?_ ?_ ?_ ?_ ?_ t ht
  have _i14 : ker (embA hres hno hpr 0) = bget' hj := by
    have h2 := ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism hres hno T j hj hb s hpr hmk
    rw [prependedAmbientSeq_isoObjZero_hom hres hno T j hj hb s hpr hmk,
      prependedAmbientSeq_blowupMorphism_zero hres hno T j hj hb s hpr hmk] at h2
    let _a0 := bget' hj
    have h3 : cmI (cmI _a0 (𝟙 T.scheme)) (𝟙 tSch T)
        = _a0 := by simp_all
    exact tr_ h2 h3
  rw [_i14]
  exact sy_ (DivisorReductionBoundary.strictTransform_mul_containedComponentsIdeal T hV j hj)
  intro n hn
  exact ker_embeddingIntoAmbientBlowupSequence_succ _a2.si
    s.toBsd hres hno hpr n
    (by rw [ofMarkedSequence_length]; exact hn)
  intro n _
  exact rfl
  have _i13 : (amb hres hno hpr).projectionToBase 0 ≫ tMp T = tMp T := by
    have h1 :=
      (p23 _).trans (ambientBlowupSeq_isoObjZero_hom hres hno T j hj _a0 _a1 s hpr)
    rw [h1]
    exact id_comp T.structMap
  rw [_i13]
  exact DivisorReductionBoundary.isSmoothDivisor_containedComponentsIdeal T hV j hj
  intro n hn
  have hlt :=
    lt_of_lt_of_le hj (length_le_length_boundary _a3 (n + 1)
      (by rw [_a4]; omega))
  have h1 : IsSmoothDivisor (_a6.projectionToSpec (n + 1)) (get (_a6.boundary (n + 1)) ⟨j, hlt⟩) := by
    let i := n + 1
    let hi := by omega
    let _a0 := _a6
    have hvl :=
      p38 effectiveCartierSupportContainsNoComponent hV
        _a0 i
        (by rw [_a8]; omega)
    have h2 := hlt
    rw [← transformAt_boundary] at h2
    have h3 := isSmoothDivisor_boundary_get
      (T.transformAt _a0 i) hvl j h2
    rwa [transformAt_structureMorphism] at h3
  rw [prependedAmbientSeq_boundary_succ_get hres hno T j hj hb s hpr hmk n hn hlt,
    prependedAmbientSeq_projectionToSpec_succ hres hno T j hj hb s hpr hmk n] at h1
  exact h1
  intro n hn
  let _c0 := lI hj
  rw [disjoint_left]
  intro y hy1 hy2
  let _a0 := lB hj
  rw [support_ambientBlowupSeq_center_eq_image hres hno T j hj _c0
    _a0 s hpr n] at hy1
  obtain ⟨z, hz, rfl⟩ := hy1
  have hn' := hn
  rw [← ofMarkedSequence_length] at hn'
  let _a9 := ofMarkedSequence s
  have hzco := _a9.center_order n hn' hz
  rw [mem_orderAtLeastLocus_iff] at hzco
  let _a1 := _a9.ideal n
  have hz2 : (1 : ENat) ≤ orderAt _a1 z :=
    le_trans (by exact_mod_cast hlow.one_le_mult) hzco
  have hzs : z ∈ (_a1.support :
      Set (_a9.obj n)) :=
    (one_le_orderAt_iff_mem_support _ _).1 hz2
  let _a10 := ofMarkedSequence s
  let _a11 := rTD hj
  have _i11 : ∀ n, n ≤ s.length → ∀ y : (_a10.obj n), y ∈ ((_a10.ideal n).support : Set (_a10.obj n)) → _a10.proj n y ∈ (_a11.ideal.support : Set _a11.scheme) := by
    let _a0 := ofMarkedSequence s
    intro n
    induction n with
    | zero =>
      intro _ y hy
      have h1 :=
        _a0.ideal_zero
      rw [h1] at hy
      have h2 :=
        Scheme.IdealSheafData.mem_support_comap.mp hy
      rwa [_a0.proj_zero]
    | succ n ih =>
      intro hn y hy
      have hn' : n < _a0.length := by
        rw [ofMarkedSequence_length]
        omega
      have h1 :=
        (one_le_orderAt_iff_mem_support _ _).2 hy
      let _a2 := p5 (_a0.map n) (_a0.center n) ^ tMu _a11
      let _a3 := _a0.ideal $ n + 1
      have h5 : orderAt _a2 y
            + orderAt _a3 y
          ≤ orderAt (_a2
              * _a3) y := by
        apply add_orderAt_le_orderAt_mul
      rw [_a0.ideal_succ n hn'] at h5
      have h6 :=
        le_trans (le_trans h1 le_add_self) h5
      have h7 :=
        (one_le_orderAt_iff_mem_support _ _).1 h6
      have h8 :=
        Scheme.IdealSheafData.mem_support_comap.mp h7
      have h10 :=
        _a0.proj_succ n
      rw [h10]
      exact ih (by omega) _ h8
  have hw2 :=
    Scheme.IdealSheafData.mem_support_comap.mp (_i11 n (le_of_lt hn) z hzs)
  let _a2 := ccI hj
  have hsupp := TransportedDivisor.support_iteratedComap
      _a7
      _a2 n
  rw [ambientBlowupSeq_projectionToBase_comp_isoObjZero_inv hres hno T j hj _c0
    _a0 s hpr n] at hsupp
  rw [hsupp] at hy2
  have hz' : z ∈ (embA hres hno hpr n ≫
      _a7.projectionToBase n) ⁻¹'
      _a2.supp := hy2
  rw [hcomp n (le_of_lt hn)] at hz'
  have _i10 : Disjoint (spI (lI hj) : CSet T.scheme) (spI (ccI hj) : CSet T.scheme) := by
    have := hV.charZero
    have := hV.smooth
    rw [disjoint_left]
    intro x hx1 hx2
    have ha :=
      (one_le_orderAt_iff_mem_support _ _).2 hx2
    have hbb :=
      (one_le_orderAt_iff_mem_support _ _).2 hx1
    let _m0 := (tMu T : ENat)
    let _a0 := orderAt (ccI hj) x
    have hm : _m0 ≤ _m0 * _a0 := by
      calc _m0 = _m0 * 1 := sy_ (mul_one _)
        _ ≤ _m0 * _a0 := by gcongr
    have hordGe : _m0 + 1 ≤ orderAt T.ideal x := by
      rw [← containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup T hV j hj, orderAt_mul T.base T.structMap, orderAt_pow T.base T.structMap]
      exact add_le_add hm hbb
    exact not_natCast_add_one_le_self T.mult $ le_trans hordGe (hord x)
  exact (Set.disjoint_left.1
    _i10) hw2 hz'
end

end DivisorReduction





namespace MonomialCenter

variable {X : Sch}

theorem foldr_mul_ofFn_eq_prod {Z : Sch} {n : ℕ} (f : Fin n → ISD Z) :
    (ofFn f).foldr (· * ·) ⊤ = ∏ i, f i := by
  rw [← one_eq_top]
  exact prod_ofFn

section
variable (E : Bdy X)
theorem image_comap_eq_range_get (U : Opn X) :
    (fun D : ISD X => comap D U.i) '' {D | D ∈ E} =
      range fun i : Fin E.length => comap (get E i) U.i := by
  ext w
  constructor
  rintro ⟨D, hD, rfl⟩
  obtain ⟨i, hi, hEi⟩ := mp_ mem_iff_getElem hD
  exact ⟨⟨i, hi⟩, by simp [hEi]⟩
  rintro ⟨i, rfl⟩
  exact ⟨get E i, by simp, rfl⟩

section
variable (M : ISD X) (x : ↥X)
theorem isMonomialNear_iff_exists_pow_prod :
    IsMonomialNear E M x ↔ ∃ U : Opn X, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
      comap M U.i =
        (ofFn fun i : Fin E.length => comap (get E i) U.i ^ a i).foldr (· * ·) ⊤ :=
  m22

theorem isMonomialNear_iff_mem_closure :
    IsMonomialNear E M x ↔ ∃ U : Opn X, x ∈ U ∧
      comap M U.i ∈
        Submonoid.closure ((fun D : ISD X => comap D U.i) '' {D | D ∈ E}) := by
  rw [isMonomialNear_iff_exists_pow_prod]
  constructor
  rintro ⟨U, hxU, a, ha⟩
  refine ⟨U, hxU, ?_⟩
  rw [image_comap_eq_range_get, ha, foldr_mul_ofFn_eq_prod, Submonoid.mem_closure_range_iff_of_fintype]
  exact ⟨a, rfl⟩
  rintro ⟨U, hxU, hmem⟩
  rw [image_comap_eq_range_get, Submonoid.mem_closure_range_iff_of_fintype] at hmem
  obtain ⟨a, ha⟩ := hmem
  refine ⟨U, hxU, a, ?_⟩
  rw [foldr_mul_ofFn_eq_prod, ha]
end
end

section
variable {E E' : Bdy X}
theorem IsMonomialNear.mono
    (h : ∀ D ∈ E, D ≠ ⊤ → D ∈ E') {M} {x}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x := by
  obtain ⟨U, hxU, hmem⟩ := mp_ (isMonomialNear_iff_mem_closure E M x) hM
  refine mpr_ (isMonomialNear_iff_mem_closure E' M x) ⟨U, hxU, ?_⟩
  refine Submonoid.closure_le.mpr ?_ hmem
  rintro w hw
  obtain ⟨D, hD, hDw⟩ := hw
  have hDw' : cmI D U.i = w := hDw
  subst hDw'
  by_cases hDtop : D = ⊤
  have hone : cmI D U.i = 1 := by
    simp [hDtop, one_eq_top]
  rw [hone]
  exact SetLike.mem_coe.mpr $ one_mem _
  exact m175 ⟨D, h D hD hDtop, rfl⟩

theorem IsMonomialNear.congr_setOf
    (h : {D : ISD X | D ∈ E ∧ D ≠ ⊤} = {D : ISD X | D ∈ E' ∧ D ≠ ⊤})
    {M} {x} (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.mono fun D hD hne => an1 $ mp_ ((mp_ ext_iff h) D) ⟨hD, hne⟩

theorem IsMonomialNear.congr_sameNontrivialBoundary
    (h : SameNontrivialBoundary E E') {M} {x}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.congr_setOf h.setOf_mem_ne_top_eq
end

theorem isLocallyMonomialTriple_withBoundary (hG : MonomialGeometryHypotheses)
    (T : MarkedIdealWithBoundary) (hT : IsLocallyMonomialTriple T)
    E'
    (hE : SameNontrivialBoundary T.boundary E') :
    IsLocallyMonomialTriple $ withBoundary T E' :=
  { valid := hG.withBoundary_valid T hT.valid E' hE
    monomialNear := fun x hx => (hT.monomialNear x hx).congr_sameNontrivialBoundary hE }

end MonomialCenter





noncomputable abbrev blowupTripleAtCenterIdeal (T : MarkedIdealWithBoundary) : MarkedIdealWithBoundary :=
  @mk T.base T.instField
    (Blowup.blowup $ T.mc)
    (proj (T.mc) ≫ structMap T)
    (residualByPow (T.ideal.comap $ proj $ T.mc)
      (comap (T.mc)
        (proj $ T.mc)) T.mult)
    T.mult
    (transformedBoundary (proj $ T.mc)
      (T.mc) T.boundary)

noncomputable def numMaxOrderCandidates (T : MarkedIdealWithBoundary) : ℕ :=
  {p : FinSet T.boundary.length × CSet T.scheme |
      IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) p.1 p.2 ∧
        orderAlong T.ideal p.2 = maxCandidateOrder T.ideal T.mult T.boundary}.ncard

section
variable {X' X : Sch} (pi_ : X' ⟶ X) (Z : ISD X) (L : Bdy X)
theorem get_transformedBoundary_strictTransformIndex_eq_strictTransform (j : Fin L.length) :
    get (transformedBoundary pi_ Z L) (strictTransformIndex pi_ Z L j) = strictTransform pi_ Z (get L j) := by
  simp [transformedBoundary, get_eq_getElem, strictTransformIndex_val, j.isLt]

theorem image_strictTransformIndex_preimageStrictTransformIndex_eq_erase
    (J' : Finset $ Fin (transformedBoundary pi_ Z L).length) :
    image (strictTransformIndex pi_ Z L) (preimageStrictTransformIndex pi_ Z L J') = J'.erase (exceptionalIndex pi_ Z L) := by
  classical
  have hlen :=
    transformedBoundary_length pi_ Z L
  ext i
  constructor
  intro hi
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hi
  refine mem_erase.2 ⟨?_, (mem_preimageStrictTransformIndex_iff pi_ Z L J' j).1 hj⟩
  intro hc
  have h1 : ((strictTransformIndex pi_ Z L j : Fin (transformedBoundary pi_ Z L).length) : ℕ) = length L := by
    rw [hc, exceptionalIndex_val]
  rw [strictTransformIndex_val] at h1
  exact absurd h1 $ Nat.ne_of_lt j.isLt
  intro hi
  obtain ⟨hne, hmem⟩ := mem_erase.1 hi
  have h1 := i.isLt
  have h2 : i ≠ length L := by
    intro hc
    exact hne $ val_injective $ by rw [hc, exceptionalIndex_val]
  have hlt : i < length L := by omega
  have hid : strictTransformIndex pi_ Z L ⟨i, hlt⟩ = i := val_injective $ by rw [strictTransformIndex_val]
  refine mem_image.2 ⟨⟨i, hlt⟩, ?_, hid⟩
  exact (mem_preimageStrictTransformIndex_iff pi_ Z L J' ⟨i, hlt⟩).2 (by rw [hid]; exact hmem)

theorem get_transformedBoundary_exceptionalIndex_eq_comap :
    get (transformedBoundary pi_ Z L) (exceptionalIndex pi_ Z L) = comap Z pi_ := by
  have hlen :=
    transformedBoundary_length pi_ Z L
  have hg2 : get (transformedBoundary pi_ Z L) (cast hlen.symm $ last L.length)
      = exceptionalIdeal pi_ Z := by
    simp [transformedBoundary, get_eq_getElem]
  have hfin : exceptionalIndex pi_ Z L = cast hlen.symm (last L.length) := by
    apply val_injective
    simp [exceptionalIndex_val]
  rw [hfin, hg2, exceptionalIdeal_eq_comap]

theorem injective_strictTransformIndex : Function.Injective $ strictTransformIndex pi_ Z L := by
  intro i j hij
  apply val_injective
  simpa [strictTransformIndex_val] using (congrArg (fun z : Fin (transformedBoundary pi_ Z L).length => (z : ℕ)) hij)

theorem strictMono_strictTransformIndex : StrictMono $ strictTransformIndex pi_ Z L := by
  intro i j hij
  rwa [lt_def, strictTransformIndex_val, strictTransformIndex_val]

theorem sortedIndices_image_strictTransformIndex S :
    sortedIndices (image (strictTransformIndex pi_ Z L) S)
      = sortedIndices S := by
  rw [sortedIndices_image_of_strictMono (strictTransformIndex pi_ Z L)
    (strictMono_strictTransformIndex pi_ Z L) S]
  simp [strictTransformIndex_val]
  rfl
end

section
variable (hGeom : MonomialGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : IsLocallyMonomialTriple T)
include hGeom hT
section
variable {X'} (pi_ : X' ⟶ scheme T) (Z : tISD T)
theorem orderAt_controlledTransform_eq_of_notMem_support (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) I'
    (hI' : (comap Z pi_) ^ T.mult * I' = T.ideal.comap pi_) x'
    (hx' : x' ∉ support (comap Z pi_)) :
    orderAt I' x' = orderAt T.ideal (pi_ x') := by
  have h1 : stalkIdeal (cmI Z pi_) x' = 1 := by
    rw [m217]
    by_contra hc
    exact hx' $ (mem_support_iff_stalkIdeal_ne_top _ _).2 hc
  have h2 : stalkIdeal (T.ideal.comap pi_) x' = stalkIdeal I' x' := by
    rw [← hI', stalkIdeal_mul, stalkIdeal_pow, h1, one_pow, one_mul]
  rw [orderAt_eq_of_stalkIdeal_eq h2.symm]
  exact hGeom.orderAt_comap_off_exceptional T hT.valid _ pi_ Z hpi_ x'
    (by rw [p9]; exact hx') T.ideal

theorem exists_mem_intersectionComponents_orderAlong_eq
    (hZ : Z = componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (isOpen_preimage_sUnion_centerComponents hGeom hT))
    (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) I'
    (hI' : (comap Z pi_) ^ T.mult * I' = T.ideal.comap pi_)
    J'
    (hnew : exceptionalIndex pi_ Z T.boundary ∉ J') {C'}
    (hC' : C' ∈ intersectionComponents (transformedBoundary pi_ Z T.boundary) J') :
    ∃ C,
      C ∈ intersectionComponents T.boundary (preimageStrictTransformIndex pi_ Z T.boundary J') ∧
        C ∉ centerComponents T.ideal T.mult T.boundary ∧
        orderAlong I' C' = orderAlong T.ideal C := by
  classical
  have himg := tr_ (image_strictTransformIndex_preimageStrictTransformIndex_eq_erase pi_ Z T.boundary J')
    (erase_eq_of_notMem hnew)
  subst hZ
  obtain ⟨hoff, C, hC, hCnot, -, hgen⟩ :=
    hGeom.transformed_components T hT.valid (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (centerComponents_subset_intersectionComponents _ _ _)
      (isOpen_preimage_sUnion_centerComponents hGeom hT) X' pi_ hpi_
      (preimageStrictTransformIndex pi_ _ T.boundary J') C' (by rw [himg]; exact hC')
      (icGP hC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC')
  refine ⟨C, hC, hCnot, ?_⟩
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents I' hC', orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC]
  dsimp [icGP]
  rw [← hgen _ $ isGenericPoint_genericPoint_of_mem_intersectionComponents hC]
  refine orderAt_controlledTransform_eq_of_notMem_support hGeom hT pi_ _ hpi_ I' hI' _ ?_
  rwa [p9] at hoff
end

theorem sum_lt_mult_of_card_lt_minIndexCard {x : ↥T.scheme} {U : T.scheme.Opens}
    (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.i =
      (ofFn fun i : Fin T.boundary.length =>
        comap (T.boundary.get i) U.i ^ a i).foldr (· * ·) ⊤)
    (S : FinSet T.boundary.length) (hS : ∀ j ∈ S, x ∈ support (T.boundary.get j))
    (hcard : S.card < minIndexCard T.ideal T.mult T.boundary) :
    ∑ j ∈ S, a j < mult T := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨C, hxC, hC⟩ := exists_mem_intersectionComponents_of_mem_support T.boundary S x $ mem_support_intersectionIdeal T.boundary S x hS
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary S.card S C :=
    ⟨rfl, hC, by rw [orderAlong_eq_sum_of_monomial hGeom hT hC hxC U hxU a hmon]; exact_mod_cast hc⟩
  have hone : 1 ≤ S.card := by
    rcases m73 S.card with h0 | hp
    exfalso
    rw [card_eq_zero.1 h0, sum_empty] at hc
    have hm1 := hT.valid.one_le_mult
    omega
    exact hp
  have hle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨S.card, hone, S, C, hcand⟩).2.2
    S.card hone S C hcand
  omega

section
variable (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
include h
section
variable {X'} (pi_ : X' ⟶ scheme T) (q : X' ⟶ Sp T.base)
theorem minIndexCard_le_card_add_one_of_exceptionalIndex_mem
    (hpi_ : IsBlowupAlongIdealSheaf pi_ $ T.mc)
    I'
    (hI' : (comap (T.mc) pi_) ^ T.mult * I' = T.ideal.comap pi_)
    (hT' : IsLocallyMonomialTriple $ blowupTriple T pi_ q I')
    J'
    (hnew : exceptionalIndex pi_ (T.mc) T.boundary ∈ J')
    {C'}
    (hC' : C' ∈ intersectionComponents (transformedBoundary pi_ (T.mc)
      T.boundary) J')
    (hord : (mult T : ENat) ≤ orderAlong I' C') :
    minIndexCard T.ideal T.mult T.boundary
        ≤ (preimageStrictTransformIndex pi_ (T.mc) T.boundary J').card + 1 ∧
      ((preimageStrictTransformIndex pi_ (T.mc) T.boundary J').card
          < minIndexCard T.ideal T.mult T.boundary →
        orderAlong I' C' < maxCandidateOrder T.ideal T.mult T.boundary) := by
  let _a1 := T.mc
  let _a2 := pi_ $ icGP hC'
  classical
  let _a4 := icGP hC'
  have hximem : _a4 ∈ C' := by
    have h0 : _a4 ∈
        closure ({_a4} : Set X') :=
      subset_closure rfl
    rwa [isGenericPoint_genericPoint_of_mem_intersectionComponents hC'] at h0
  have hdiv : ∀ i, i ∈ J' →
      C' ⊆ (support (get (transformedBoundary pi_ _a1 T.boundary) i) : Set X') := by
    intro i hi
    exact (hGeom.components_subset_divisor_iff (blowupTriple T pi_ q I') hT'.valid J' C' hC' i).2 hi
  have hxiE : _a4 ∈
      support (cmI _a1 pi_) := by
    have h1 := hdiv _ hnew
    rw [get_transformedBoundary_exceptionalIndex_eq_comap] at h1
    exact h1 hximem
  have hpixi : _a2 ∈
      support _a1 :=
    Scheme.IdealSheafData.mem_support_comap.1 hxiE
  have hpixiset : _a2 ∈
      (support _a1 : CSet T.scheme) := hpixi
  rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents] at hpixiset
  obtain ⟨C0_, hC0opt, hmem0_⟩ := hpixiset
  obtain ⟨U, hU, a, hmon⟩ := hT.monomialNear _ $ support_monomialCenter_subset_orderAtLeastLocus hGeom hT h hpixi
  have hkey := orderAlong_transform_add_mult_of_exceptionalIndex_mem hGeom hT h pi_ q hpi_ I' hI' hT' hnew hC'
    U hU a hmon hC0opt hmem0_
  have hC0comp_ :=
    centerComponents_subset_intersectionComponents _ _ _ hC0opt
  have hordC0 :=
    orderAlong_eq_sum_of_monomial hGeom hT hC0comp_ hmem0_ U hU a hmon
  rw [hordC0] at hkey
  obtain ⟨S1, hS1⟩ : ∃ s, s = ∑ i ∈ preimageStrictTransformIndex pi_ (T.mc)
      T.boundary J', a i := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ s, s = ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j :=
    ⟨_, rfl⟩
  rw [← hS1, ← hS2] at hkey
  have hltop : orderAlong I' C' < ⊤ := by
    refine lt_of_le_of_lt ?_ $ lt_of_le_of_ne (le_top : ((S1 : ENat) + (S2 : ENat)) ≤ ⊤) ?_
    rw [← hkey]
    exact le_self_add
    intro hc
    have hcc : ((S1 + S2 : ℕ) : ENat) = ⊤ := by rw [cast_add]
                                                exact hc
    simp at hcc
  obtain ⟨n, hn⟩ := ne_top_iff_exists.1 $ ne_of_lt hltop
  have hnm : n + tMu T = S1 + S2 := by
    have hc2 : ((n + tMu T : ℕ) : ENat) = ((S1 + S2 : ℕ) : ENat) := by
      rwa [cast_add, cast_add, hn]
    exact_mod_cast hc2
  have hmn : tMu T ≤ n := by
    have hc3 : (tMu T : ENat) ≤ (n : ENat) := by rw [hn]
                                                 exact hord
    exact_mod_cast hc3
  by_cases hk : (preimageStrictTransformIndex pi_ (T.mc) T.boundary J').card
      < minIndexCard T.ideal T.mult T.boundary
  have holdsub : ∀ j ∈ preimageStrictTransformIndex pi_ (T.mc) T.boundary J',
      _a2 ∈ spI (T.boundary.get j) := by
    intro j hj
    have h1 := hdiv _ $ (mem_preimageStrictTransformIndex_iff _ _ _ _ j).1 hj
    rw [get_transformedBoundary_strictTransformIndex_eq_strictTransform] at h1
    exact Scheme.IdealSheafData.mem_support_comap.1 $ support_antitone (comap_le_strictTransform pi_ _ _) $ h1 hximem
  have hp : S1 < tMu T := by
    rw [hS1]
    exact sum_lt_mult_of_card_lt_minIndexCard hGeom hT hU a hmon _ holdsub hk
  have hcardch := card_lexMaxIndices hGeom hT h
  have hchsub : ∀ j ∈ lexMaxIndices T.ideal T.mult T.boundary,
      _a2 ∈ spI (T.boundary.get j) := by
    intro j hj
    exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC0comp_ j).2 hj hmem0_
  obtain ⟨j0_, hj0ch, hj0old⟩ : ∃ j0_ ∈ lexMaxIndices T.ideal T.mult T.boundary,
      j0_ ∉ preimageStrictTransformIndex pi_ (T.mc) T.boundary J' := by
    by_contra hc
    push Not at hc
    have hsub :=
      fun j hj => hc j hj
    have hcc := card_le_card hsub
    omega
  let _a3 := ∑ j ∈ (lexMaxIndices T.ideal T.mult T.boundary).erase j0_, a j
  have herase : _a3 < tMu T := by
    refine sum_lt_mult_of_card_lt_minIndexCard hGeom hT hU a hmon _
      (fun j hj => hchsub j $ mem_of_mem_erase hj) ?_
    have hce := card_erase_of_mem hj0ch
    omega
  have hsplit : _a3 + a j0_ = S2 := by
    rw [hS2]
    exact sum_erase_add _ _ hj0ch
  have hSge : tMu T ≤ ∑ j ∈ insert j0_ (preimageStrictTransformIndex pi_ (T.mc)
      T.boundary J'), a j := by
    rw [sum_insert hj0old, ← hS1]
    omega
  have hmemsupp : _a2 ∈
      ((intersectionIdeal T.boundary $ insert j0_ $ preimageStrictTransformIndex pi_
        (T.mc) T.boundary J').support : CSet T.scheme) := by simp_all
  obtain ⟨C, hxC, hCcomp⟩ :=
    exists_mem_intersectionComponents_of_mem_support T.boundary _ _ hmemsupp
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (insert j0_ $ preimageStrictTransformIndex pi_ (T.mc) T.boundary J').card
      (insert j0_ $ preimageStrictTransformIndex pi_ (T.mc) T.boundary J') C :=
    ⟨rfl, hCcomp, by rw [orderAlong_eq_sum_of_monomial hGeom hT hCcomp hxC U hU a hmon]; exact_mod_cast hSge⟩
  have hone : 1 ≤ (insert j0_ $ preimageStrictTransformIndex pi_ (T.mc)
      T.boundary J').card := card_pos.2 ⟨j0_, mem_insert_self _ _⟩
  have hminle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨_, hone, _, _, hcand⟩).2.2
    _ hone _ _ hcand
  have hcardS : (insert j0_ $ preimageStrictTransformIndex pi_ (T.mc)
      T.boundary J').card
      ≤ (preimageStrictTransformIndex pi_ (T.mc) T.boundary J').card + 1 :=
    card_insert_le _ _
  refine ⟨by omega, fun _ => ?_⟩
  rw [← hn, ← ((mem_centerComponents_iff _ _ _ C0_).1 hC0opt).2, hordC0, ← hS2]
  have hlt : n < S2 := by omega
  exact_mod_cast hlt
  exact ⟨by omega, fun hc => absurd hc hk⟩

theorem minIndexCard_lt_or_maxCandidateOrder_lt_of_isBlowupAlongIdealSheaf
    (hZp : T.mc =
      componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
        (centerComponents T.ideal T.mult T.boundary)
        (isOpen_preimage_sUnion_centerComponents hGeom hT))
    (hpi_ : IsBlowupAlongIdealSheaf pi_ $ T.mc)
    I'
    (hI' : (comap (T.mc) pi_) ^ T.mult * I' = T.ideal.comap pi_)
    (hT' : IsLocallyMonomialTriple $ blowupTriple T pi_ q I')
    (h' : minIndexCard I' T.mult
      (transformedBoundary pi_ (T.mc) T.boundary) ≠ 0) :
    minIndexCard T.ideal T.mult T.boundary
        < minIndexCard I' T.mult
          (transformedBoundary pi_ (T.mc) T.boundary) ∨
      (minIndexCard T.ideal T.mult T.boundary
          = minIndexCard I' T.mult
            (transformedBoundary pi_ (T.mc) T.boundary) ∧
        (maxCandidateOrder I' T.mult
              (transformedBoundary pi_ (T.mc) T.boundary)
            < maxCandidateOrder T.ideal T.mult T.boundary ∨
          (maxCandidateOrder T.ideal T.mult T.boundary
              = maxCandidateOrder I' T.mult
                (transformedBoundary pi_ (T.mc) T.boundary) ∧
            Lex (· < ·)
              (sortedIndices $ lexMaxIndices T.ideal T.mult T.boundary)
              (sortedIndices
                (lexMaxIndices I' T.mult
                  (transformedBoundary pi_ (T.mc)
                    T.boundary)))))) := by
  let _a4 := lexMaxIndices I' T.mult $ transformedBoundary pi_ (T.mc) T.boundary
  let _a5 := transformedBoundary pi_ (T.mc) T.boundary
  let _a6 := strictTransformIndex pi_ (T.mc) T.boundary
  let _a7 := injective_strictTransformIndex pi_ (T.mc) T.boundary
  let _a1 := tMu T
  let _a3 := minIndexCard T.ideal T.mult T.boundary
  classical
  have hA : ∀ (J' : Finset $ Fin _a5.length) C',
      C' ∈ intersectionComponents _a5 J' →
      _a1 ≤ orderAlong I' C' → 1 ≤ J'.card →
      _a3 ≤ J'.card := by
    intro J' C' hmem hordJ hone
    by_cases hnew : exceptionalIndex pi_ (T.mc) T.boundary ∈ J'
    have hx := minIndexCard_le_card_add_one_of_exceptionalIndex_mem hGeom hT h pi_ q hpi_ I' hI' hT' J' hnew hmem
      hordJ
    have hcarde := card_erase_of_mem hnew
    have himg := image_strictTransformIndex_preimageStrictTransformIndex_eq_erase pi_ (T.mc)
      T.boundary J'
    have hcimg : (image _a6
          (preimageStrictTransformIndex pi_ (T.mc) T.boundary J')).card
        = (preimageStrictTransformIndex pi_ (T.mc) T.boundary J').card :=
      card_image_of_injective _
        _a7
    rw [himg] at hcimg
    have h1 := hx.1
    omega
    obtain ⟨C, hC, -, hordeq⟩ :=
      exists_mem_intersectionComponents_orderAlong_eq hGeom hT pi_ (T.mc)
        hZp hpi_ I' hI' J' hnew hmem
    have himg := tr_ (image_strictTransformIndex_preimageStrictTransformIndex_eq_erase pi_ (T.mc) T.boundary
      J') $ erase_eq_of_notMem hnew
    have hcimg : (image _a6
          (preimageStrictTransformIndex pi_ (T.mc) T.boundary J')).card
        = (preimageStrictTransformIndex pi_ (T.mc) T.boundary J').card :=
      card_image_of_injective _
        _a7
    rw [himg] at hcimg
    have hcand : IsCandidateComponent T.ideal T.mult T.boundary
        (preimageStrictTransformIndex pi_ (T.mc) T.boundary J').card
        (preimageStrictTransformIndex pi_ (T.mc) T.boundary J') C :=
      ⟨rfl, hC, by rw [← hordeq]; exact hordJ⟩
    have hone' : 1 ≤ (preimageStrictTransformIndex pi_ (T.mc)
        T.boundary J').card := by omega
    have hle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨_, hone', _, _, hcand⟩).2.2
      _ hone' _ _ hcand
    omega
  obtain ⟨J1, C1_, hcand1⟩ := exists_isCandidateComponent_minIndexCard I' T.mult
    _a5 h'
  have hsplit1 : J1.card = minIndexCard I' T.mult
        _a5 ∧
      C1_ ∈ intersectionComponents _a5 J1 ∧ _a1 ≤ orderAlong I' C1_ := hcand1
  obtain ⟨hcard1_, hmem1_, hord1_⟩ := hsplit1
  have hone1 : 1 ≤ J1.card := by
    rw [hcard1_]
    exact Nat.pos_of_ne_zero h'
  have hAle := hA J1 C1_ hmem1_ hord1_ hone1
  rw [hcard1_] at hAle
  rcases lt_or_eq_of_le hAle with hlt | heq
  exact inl hlt
  refine inr ⟨heq, ?_⟩
  have hbest' : ∃ C,
      IsCandidateComponent I' T.mult
          _a5
          (minIndexCard I' T.mult
            _a5)
          _a4 C ∧
        orderAlong I' C = maxCandidateOrder I' T.mult
          _a5 :=
    (lexMaxIndices_spec hGeom hT' h').1
  obtain ⟨C', hcand', hordC'⟩ := hbest'
  have hsplit' : _a4.card
        = minIndexCard I' T.mult
          _a5 ∧
      C' ∈ intersectionComponents _a5
        _a4 ∧
      _a1 ≤ orderAlong I' C' := hcand'
  obtain ⟨hcardc', hmemc', hordc'⟩ := hsplit'
  by_cases hnew : exceptionalIndex pi_ (T.mc) T.boundary ∈
      _a4
  left
  have hx := minIndexCard_le_card_add_one_of_exceptionalIndex_mem hGeom hT h pi_ q hpi_ I' hI' hT' _ hnew hmemc'
    hordc'
  have hcarde := card_erase_of_mem hnew
  have himg := image_strictTransformIndex_preimageStrictTransformIndex_eq_erase pi_ (T.mc) T.boundary
    _a4
  have hcimg : (image _a6
        (preimageStrictTransformIndex pi_ (T.mc) T.boundary
          _a4)).card
      = (preimageStrictTransformIndex pi_ (T.mc) T.boundary
          _a4).card :=
    card_image_of_injective _
      _a7
  rw [himg] at hcimg
  have hmin' : minIndexCard I' T.mult
      _a5 ≠ 0 := h'
  have hpos : 1 ≤ _a4.card := by simp_all
  have hlt2 : (preimageStrictTransformIndex pi_ (T.mc) T.boundary
      _a4).card
      < _a3 := by omega
  rw [← hordC']
  exact hx.2 hlt2
  obtain ⟨C, hC, hCnot, hordeq⟩ :=
    exists_mem_intersectionComponents_orderAlong_eq hGeom hT pi_ (T.mc)
      hZp hpi_ I' hI' _ hnew hmemc'
  have himgc := tr_ (image_strictTransformIndex_preimageStrictTransformIndex_eq_erase pi_ (T.mc) T.boundary
    _a4)
    (erase_eq_of_notMem hnew)
  have hcimg : (image _a6
        (preimageStrictTransformIndex pi_ (T.mc) T.boundary
          _a4)).card
      = (preimageStrictTransformIndex pi_ (T.mc) T.boundary
          _a4).card :=
    card_image_of_injective _
      _a7
  rw [himgc] at hcimg
  have hcardJ := sy_ heq
  rw [← hcardc', hcimg] at hcardJ
  have hmC := hordc'
  rw [hordeq] at hmC
  have hcandJ : IsCandidateComponent T.ideal T.mult T.boundary
      _a3
      (preimageStrictTransformIndex pi_ (T.mc) T.boundary
        _a4) C :=
    ⟨hcardJ, hC, hmC⟩
  have hvle : maxCandidateOrder I' T.mult
      _a5
      ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
    rw [← hordC', hordeq]
    exact (maxCandidateOrder_spec hGeom hT h).2.1 _ _ hcandJ
  rcases lt_or_eq_of_le hvle with hv | hv
  exact inl hv
  refine inr ⟨sy_ hv, ?_⟩
  have hordC2 : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by simp_all
  have hsp : sortedIndices _a4
      = sortedIndices
        (preimageStrictTransformIndex pi_ (T.mc) T.boundary
          _a4) := by
    conv_lhs => rw [← himgc]
    exact sortedIndices_image_strictTransformIndex pi_ (T.mc)
      T.boundary _
  rcases trichotomous_of (Lex (· < ·))
      (sortedIndices $ lexMaxIndices T.ideal T.mult T.boundary)
      (sortedIndices
        (preimageStrictTransformIndex pi_ (T.mc) T.boundary
          _a4))
    with hlex | hlexeq | hlex
  rwa [hsp]
  exfalso
  have hJeq : preimageStrictTransformIndex pi_ (T.mc) T.boundary
        _a4
      = lexMaxIndices T.ideal T.mult T.boundary := by
    ext j
    constructor
    intro hj
    have h1 : (j : ℕ) ∈ sortedIndices
        (preimageStrictTransformIndex pi_ (T.mc) T.boundary
          _a4) := (mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
    rw [← hlexeq] at h1
    obtain ⟨j2, hj2, hvv⟩ := (mem_sortedIndices _ _).1 h1
    have hje : j2 = j := val_injective hvv
    rwa [hje] at hj2
    intro hj
    have h1 : (j : ℕ) ∈ sortedIndices
        (lexMaxIndices T.ideal T.mult T.boundary) :=
      (mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
    rw [hlexeq] at h1
    obtain ⟨j2, hj2, hvv⟩ := (mem_sortedIndices _ _).1 h1
    rwa [val_injective hvv] at hj2
  apply hCnot
  refine (mem_centerComponents_iff _ _ _ C).2 ⟨⟨card_lexMaxIndices hGeom hT h, ?_, hmC⟩, hordC2⟩
  simp_all
  exact absurd hlex $ (lexMaxIndices_spec hGeom hT h).2 _ ⟨C, hcandJ, hordC2⟩
end

theorem krullDimSucc_blowupTripleAtCenterIdeal_le :
    krullDimSucc (blowupTripleAtCenterIdeal T).scheme ≤ T.krullDimSucc :=
  by
    let d := ofSingleBlowup T.structMap T.ideal T.mult T.boundary
      (T.mc)
      (smooth_monomialCenter hGeom hT h) (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h)
      (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
      (exists_controlledTransform_monomialCenter hGeom hT h)
    have key := hGeom.level_schemeDim_le T hT.valid d.toMarkedSequenceOfBlowups 1
      (by rw [toMarkedSequence_length]; exact m164 1)
    rwa [toMarkedSequence_schemeAt] at key
end
end

noncomputable def monomialInvariant (D : ℕ) (T : MarkedIdealWithBoundary) :
    Lex $ ℕ × Lex (ℕ × ℕ) :=
  toLex (D - minIndexCard T.ideal T.mult T.boundary,
    toLex ((maxCandidateOrder T.ideal T.mult T.boundary).toNat, numMaxOrderCandidates T))

theorem foldr_mul_ofFn_eq_prod__b8 {Y : Sch} :
    ∀ {n : ℕ} (F : Fin n → ISD Y),
      foldr (· * ·) (⊤ : ISD Y) (ofFn F) = ∏ i, F i := by
  intro n
  induction n with
  | zero =>
      intro F
      simp only [ofFn_zero, foldr_nil, univ_eq_empty, prod_empty]
      exact Scheme.IdealSheafData.one_eq_top.symm
  | succ n ih =>
      intro F
      rw [ofFn_succ, foldr_cons, ih, prod_univ_succ]

theorem comap_prod {X Y : Sch} (f : X ⟶ Y) :
    ∀ {n : ℕ} (F : Fin n → ISD Y),
      comap (∏ i, F i) f = ∏ i, comap (F i) f := by
  intro n
  induction n with
  | zero =>
      intro F
      simp only [univ_eq_empty, prod_empty]
      rw [one_eq_top, comap_top]
      exact Scheme.IdealSheafData.one_eq_top.symm
  | succ n ih =>
      intro F
      rw [prod_univ_succ, comap_mul, ih, prod_univ_succ]

section
variable (hGeom : MonomialGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : IsLocallyMonomialTriple T)
include hGeom hT
theorem isMonomialNear_transformedBoundary_of_isBlowupAlongIdealSheaf
    {X' : Sch} (pi_ : X' ⟶ scheme T) (Z : T.scheme.IdealSheafData)
    (hblow : IsBlowupAlongIdealSheaf pi_ Z)
    (hsm : Smooth (subschemeι Z ≫ structMap T))
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (hZco : (↑Z.support : CSet T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult)
    (hZsupp : (↑Z.support : CSet T.scheme) = ⋃₀ centerComponents T.ideal T.mult T.boundary)
    (J : IdealSheafData X')
    (hJ : (comap Z pi_) ^ T.mult * J = T.ideal.comap pi_)
    (x' : ↥X') (hx' : x' ∈ orderAtLeastLocus J T.mult) :
    MonomialCenter.IsMonomialNear (transformedBoundary pi_ Z T.boundary) J x' := by
  classical
  have hmemcompl : ∀ y : scheme T, y ∈ (suppC Z : T.scheme.Opens) ↔ y ∉ support Z :=
    fun y => m22
  let _a9 := cmI Z pi_
  have hzc : pi_ x' ∈ orderAtLeastLocus T.ideal T.mult := by
    by_cases hxe : x' ∈ support _a9
    exact hZco (by exact Scheme.IdealSheafData.mem_support_comap.1 hxe)
    have h1 := (mem_orderAtLeastLocus_iff _ _ _).1 hx'
    have h2 : orderAt J x' ≤ orderAt (T.ideal.comap pi_) x' := by
      have hmul := add_orderAt_le_orderAt_mul (_a9 ^ tMu T) J x'
      rw [hJ] at hmul
      exact le_trans le_add_self hmul
    have h3 : orderAt (T.ideal.comap pi_) x' = orderAt T.ideal (pi_ x') := by
      refine hGeom.orderAt_comap_off_exceptional T hT.valid _ pi_ Z hblow x' ?_ T.ideal
      rwa [exceptionalIdeal_eq_comap]
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (by rw [← h3]; exact le_trans h1 h2)
  obtain ⟨U, hzU, a, hmon⟩ := hT.monomialNear (pi_ x') hzc
  have hbt : ∀ i : Fin (bLen T), ∃ (V : Opn X') (ep_ : ℕ),
      x' ∈ V ∧ (ep_ = 0 ∨ ep_ = 1) ∧
        (ep_ = 1 ↔ ∃ O : T.scheme.Opens, pi_ x' ∈ O ∧
          (support Z : CSet T.scheme) ∩ (O : CSet T.scheme) ⊆
            (support (T.boundary.get i) : CSet T.scheme)) ∧
        comap (cmI (T.boundary.get i) pi_) V.i =
          comap (strictTransform pi_ Z (T.boundary.get i)) V.i *
            comap (exceptionalIdeal pi_ Z) V.i ^ ep_ := by
    intro i
    exact hGeom.blowup_total_transform T hT.valid Z hsm hsnc
      _ pi_ hblow (T.boundary.get i) (getElem_mem i.isLt) x'
  choose Vf ef hxV hef01 hefiff hefeq using hbt
  set e := ∑ i : Fin (bLen T), ef i * a i with hedef
  have hme : tMu T ≤ e := by
    by_cases hxe : x' ∈ support _a9
    have hzZ := Scheme.IdealSheafData.mem_support_comap.1 hxe
    obtain ⟨C, hC, hzC⟩ : ∃ C ∈ centerComponents T.ideal T.mult T.boundary, pi_ x' ∈ C := by
      have hmem : pi_ x' ∈ ⋃₀ centerComponents T.ideal T.mult T.boundary := by
        rwa [← hZsupp]
      exact hmem
    have hmax : (tMu T : ENat) ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
      refine (maxCandidateOrder_spec hGeom hT ?_).2.2.1
      intro h0
      have : pi_ x' ∈ (∅ : CSet T.scheme) := by rw [← orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero hGeom hT h0]
                                                exact hzc
      exact this.elim
    have hsum : tMu T ≤ ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by
      have hcast : (tMu T : ENat)
          ≤ ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ENat) := by
        rwa [← orderAlong_eq_sum_of_monomial hGeom hT (centerComponents_subset_intersectionComponents _ _ _ hC) hzC U hzU a hmon, ((mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hC).2]
      exact_mod_cast hcast
    have hef1 : ∀ j ∈ lexMaxIndices T.ideal T.mult T.boundary, ef j = 1 := by
      intro j hj
      refine (hefiff j).2 ⟨⊤, trivial, ?_⟩
      intro y hy
      have hy1 := hy.1
      rw [hZsupp] at hy1
      obtain ⟨C', hC', hyC'⟩ := hy1
      exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT
        (centerComponents_subset_intersectionComponents _ _ _ hC') j).2 hj hyC'
    calc T.mult ≤ ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := hsum
      _ = ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, ef j * a j := by
          refine sum_congr rfl ?_
          intro j hj
          rw [hef1 j hj, one_mul]
      _ ≤ e := sum_le_sum_of_subset $ subset_univ _
    have hzZ : pi_ x' ∉ support Z := fun hc => hxe $ Scheme.IdealSheafData.mem_support_comap.2 hc
    have hef1 : ∀ i : Fin (bLen T), ef i = 1 := by
      intro i
      refine (hefiff i).2 ⟨suppC Z, (hmemcompl (pi_ x')).2 hzZ, ?_⟩
      intro y hy
      exact absurd hy.1 ((hmemcompl y).1 hy.2)
    have hsum : tMu T ≤ ∑ j ∈ supportIndices T.boundary (pi_ x'), a j := by
      have hcast : (tMu T : ENat)
          ≤ ((∑ j ∈ supportIndices T.boundary (pi_ x'), a j : ℕ) : ENat) := by
        rw [← orderAt_eq_sum_supportIndices hGeom hT (pi_ x') U hzU a hmon]
        exact (mem_orderAtLeastLocus_iff _ _ _).1 hzc
      exact_mod_cast hcast
    calc T.mult ≤ ∑ j ∈ supportIndices T.boundary (pi_ x'), a j := hsum
      _ ≤ ∑ j : Fin (bLen T), a j :=
          sum_le_sum_of_subset (subset_univ _)
      _ = e := by
          refine sum_congr rfl ?_
          intro j _
          rw [hef1 j, one_mul]
  set W : Opn X' :=
    ⟨(⋂ i : Fin (bLen T), ((Vf i : Opn X') : Set X'))
        ∩ ((preU pi_ U : Opn X') : Set X'),
      (isOpen_iInter_of_finite fun i => (Vf i).isOpen).inter (preU pi_ U).isOpen⟩ with hWdef
  have hWU : W ≤ preU pi_ U := fun y hy => hy.2
  let _a0 := comap _a9 W.i
  have hbi : ∀ i : Fin (bLen T),
      comap (cmI (T.boundary.get i) pi_) W.i =
        comap (strictTransform pi_ Z (T.boundary.get i)) W.i
          * _a0 ^ ef i := by
    intro i
    have hle : W ≤ Vf i := fun y hy => mem_iInter.1 hy.1 i
    simpa [comap_mul, comap_pow,
      ← restrictIdeal_eq_comap_homOfLE_restrictIdeal, exceptionalIdeal_eq_comap] using (congrArg (comap · $ X'.homOfLE hle) (hefeq i))
  let _a5 := X'.homOfLE hWU
  have hcomp : (_a5 ≫ mrU pi_ U) ≫ opI U = opI W ≫ pi_ := by
    rw [assoc, morphismRestrict_ι, ← assoc, Scheme.homOfLE_ι]
  have hg : ∀ A : tISD T,
      comap (comap A U.i) (_a5 ≫ mrU pi_ U) = comap (cmI A pi_) W.i := by
    intro A
    simp only [← comap_comp]
    rw [hcomp]
  rw [foldr_mul_ofFn_eq_prod__b8] at hmon
  let _a2 := comap (T.ideal.comap pi_) W.i
  have hmonW : _a2 =
      ∏ i : Fin (bLen T), (comap (cmI (T.boundary.get i) pi_) W.i) ^ a i := by
    calc _a2
        = comap (T.ideal.comap U.i) (_a5 ≫ mrU pi_ U) := sy_ (hg _)
      _ = comap (∏ i : Fin (bLen T), (comap (T.boundary.get i) U.i) ^ a i)
            (_a5 ≫ mrU pi_ U) := by rw [hmon]
      _ = ∏ i : Fin (bLen T),
            comap ((comap (T.boundary.get i) U.i) ^ a i)
              (_a5 ≫ mrU pi_ U) := comap_prod _ _
      _ = ∏ i : Fin (bLen T), (comap (cmI (T.boundary.get i) pi_) W.i) ^ a i := by
            refine prod_congr rfl ?_
            intro i _
            rw [comap_pow, hg]
  let _a1 := (∏ i : Fin (bLen T), (comap (strictTransform pi_ Z (T.boundary.get i)) W.i) ^ a i)
  have hprod : _a2 =
      _a1
        * _a0 ^ e := by
    rw [hmonW]
    have hterm : ∀ i : Fin (bLen T),
        (comap (cmI (T.boundary.get i) pi_) W.i) ^ a i
          = (comap (strictTransform pi_ Z (T.boundary.get i)) W.i) ^ a i
              * (_a0 ^ (ef i * a i)) := by
      intro i
      rw [hbi i, mul_pow, ← pow_mul]
    rw [prod_congr rfl fun i _ => hterm i, prod_mul_distrib,
      prod_pow_eq_pow_sum]
  have hcart : IsLocallyGeneratedByNonZeroDivisor _a0 := by
    have h0 : IsLocallyGeneratedByNonZeroDivisor (cmI Z pi_) := by
      have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hblow
      rwa [exceptionalIdeal_eq_comap] at hc
    exact h0.comap_of_isOpenImmersion W.i
  have hcomapJ : _a0 ^ tMu T * comap J W.i
      = _a2 := by
    rw [← comap_pow, ← comap_mul, hJ]
  let _a12 := e - tMu T
  have hrw : _a0 ^ tMu T *
      (_a1
        * _a0 ^ _a12)
      = _a1
        * _a0 ^ e := by
    rw [← mul_assoc, mul_comm $ _a0 ^ tMu T, mul_assoc, ← pow_add,
      add_sub_cancel' hme]
  have hfinal : comap J W.i =
      _a1
        * _a0 ^ _a12 := by
    refine eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul hcart T.mult ?_
    rw [hcomapJ, hrw, hprod]
  refine ⟨W, ⟨mem_iInter.2 hxV, hzU⟩, fun i => if hi : (i : ℕ) < bLen T then a ⟨i, hi⟩ else e - tMu T, ?_⟩
  let _a16 := transformedBoundary pi_ Z T.boundary
  have _i19 : (∏ i : Fin _a16.length, (comap (get _a16 i) W.i) ^ (if hi : (i : ℕ) < bLen T then a ⟨i, hi⟩ else _a12)) = (∏ i : Fin (bLen T), (comap (strictTransform pi_ Z (T.boundary.get i)) W.i) ^ a i) * (comap (exceptionalIdeal pi_ Z) W.i) ^ _a12 := by
    let L := boundary T
    let d := e - tMu T
    classical
    have hlen := transformedBoundary_length pi_ Z L
    have hg1 : ∀ j : Fin L.length,
        get (transformedBoundary pi_ Z L) (cast hlen.symm (castSucc j))
          = strictTransform pi_ Z (get L j) := by simp_all
    have hg2 : get (transformedBoundary pi_ Z L) (cast hlen.symm (last L.length))
        = exceptionalIdeal pi_ Z := by simp_all
    rw [Fintype.prod_equiv (finCongr hlen)
        (fun i : Fin (transformedBoundary pi_ Z L).length =>
          (comap (get (transformedBoundary pi_ Z L) i) W.i) ^
            (if hi : (i : ℕ) < length L then a ⟨i, hi⟩ else d))
        (fun j : Fin (length L + 1) =>
          (comap (get (transformedBoundary pi_ Z L) (cast hlen.symm j)) W.i) ^
            (if hj : (j : ℕ) < length L then a ⟨j, hj⟩ else d))
        (fun i => by simp)]
    rw [prod_univ_castSucc]
    congr 1
    refine prod_congr rfl ?_
    intro j _
    rw [hg1 j]
    exact congrArg (fun t : ℕ => (comap (strictTransform pi_ Z (get L j)) W.i) ^ t) (dif_pos j.isLt)
    rw [hg2, dif_neg (by simp : ¬ ((last L.length : Fin (length L + 1)) : ℕ) < length L)]
  rw [foldr_mul_ofFn_eq_prod__b8,
    _i19, exceptionalIdeal_eq_comap]
  exact hfinal

section
variable (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
include h
theorem isLocallyMonomialTriple_blowupTripleAtCenterIdeal :
    IsLocallyMonomialTriple $ blowupTripleAtCenterIdeal T := by
  let _a0 := smooth_monomialCenter hGeom hT h
  let _a1 := hasStrictNormalCrossingsWith_monomialCenter hGeom hT h
  let _a2 := support_monomialCenter_subset_orderAtLeastLocus hGeom hT h
  let _a3 := exists_controlledTransform_monomialCenter hGeom hT h
  let _c0 := T.mc
  constructor
  have key := hGeom.level_valid T hT.valid
    (ofSingleBlowup T.structMap T.ideal T.mult T.boundary
      _c0
      _a0 _a1
      _a2
      _a3).toMarkedSequenceOfBlowups 1
    (by rw [toMarkedSequence_length]; exact m164 1)
  exact key
  intro x' hx'
  refine isMonomialNear_transformedBoundary_of_isBlowupAlongIdealSheaf hGeom hT
    (p34 _c0)
    _c0
    (p46 _)
    _a0
    _a1
    _a2
    (by
      rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents])
    (residualByPow (T.ideal.comap $ p34 _c0)
      (cmI _c0
        (p34 _c0)) T.mult)
    (pow_mul_residualByPow _ _ _ _a3)
    x' hx'

theorem minIndexCard_blowupTripleAtCenterIdeal_eq_zero_or_centerInvariant_lt :
    minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
        (blowupTripleAtCenterIdeal T).boundary = 0 ∨
      Lt (centerInvariant T.ideal T.mult T.boundary)
        (centerInvariant (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
          (blowupTripleAtCenterIdeal T).boundary) := by
  classical
  by_cases h' : minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
      (blowupTripleAtCenterIdeal T).boundary = 0
  exact inl h'
  refine inr ?_
  let _a0 := p34 $ T.mc
  exact minIndexCard_lt_or_maxCandidateOrder_lt_of_isBlowupAlongIdealSheaf hGeom hT h
    _a0
    (_a0 ≫ tMp T)
    (monomialCenter_eq_componentUnionIdeal hGeom hT h) (p46 _) _ (pow_mul_residualByPow _ _ _ $ exists_controlledTransform_monomialCenter hGeom hT h) (isLocallyMonomialTriple_blowupTripleAtCenterIdeal hGeom hT h) h'
end
end

theorem toNat_lt_toNat_of_lt_of_ne_top {a b : ENat} (hab : a < b) (hb : b ≠ ⊤) :
    a.toNat < b.toNat := by
  obtain ⟨n, hn⟩ := ne_top_iff_exists.1 hb
  obtain ⟨m, hm⟩ := ne_top_iff_exists.1 $ ne_top_of_lt hab
  subst hn
  subst hm
  have hmn : m < n := by exact_mod_cast hab
  simpa using hmn

theorem monomialInvariant_lt_of_lex_lt {D} {T1 T2 : MarkedIdealWithBoundary}
    (hstep :
      D - minIndexCard T1.ideal T1.mult T1.boundary
          < D - minIndexCard T2.ideal T2.mult T2.boundary ∨
        (D - minIndexCard T1.ideal T1.mult T1.boundary
            = D - minIndexCard T2.ideal T2.mult T2.boundary ∧
          ((maxCandidateOrder T1.ideal T1.mult T1.boundary).toNat
              < (maxCandidateOrder T2.ideal T2.mult T2.boundary).toNat ∨
            ((maxCandidateOrder T1.ideal T1.mult T1.boundary).toNat
                = (maxCandidateOrder T2.ideal T2.mult T2.boundary).toNat ∧
              numMaxOrderCandidates T1 < numMaxOrderCandidates T2)))) :
    monomialInvariant D T1 < monomialInvariant D T2 := by
  have hgen : ∀ {a b c a' b' c' : ℕ},
      (a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c')))) →
      (toLex (a, toLex (b, c)) : Lex $ ℕ × Lex (ℕ × ℕ))
        < toLex (a', toLex (b', c')) := by
    intro a b c a' b' c' hh
    rcases hh with h1 | ⟨rfl, h1⟩
    exact Prod.Lex.left _ _ h1
    refine Prod.Lex.right _ ?_
    rcases h1 with h2 | ⟨rfl, h2⟩
    exact Prod.Lex.left _ _ h2
    exact Prod.Lex.right _ h2
  exact hgen hstep

theorem monomialInvariant_blowupTripleAtCenterIdeal_lt (hGeom : MonomialGeometryHypotheses) {D} {T : MarkedIdealWithBoundary}
    (hT : IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    (hD : krullDimSucc T.scheme ≤ D)
    (h' : minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
      (blowupTripleAtCenterIdeal T).boundary ≠ 0) :
    monomialInvariant D (blowupTripleAtCenterIdeal T) < monomialInvariant D T := by
  classical
  have hTstep :=
    isLocallyMonomialTriple_blowupTripleAtCenterIdeal hGeom hT h
  let _a1 := minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult (blowupTripleAtCenterIdeal T).boundary
  let _a2 := maxCandidateOrder (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult (blowupTripleAtCenterIdeal T).boundary
  have hkeyU :
      minIndexCard T.ideal T.mult T.boundary
          < _a1 ∨
        (minIndexCard T.ideal T.mult T.boundary
            = _a1 ∧
          (_a2
              < maxCandidateOrder T.ideal T.mult T.boundary ∨
            (maxCandidateOrder T.ideal T.mult T.boundary
                = _a2 ∧
              Lex (· < ·)
                (sortedIndices $ lexMaxIndices T.ideal T.mult T.boundary)
                (sortedIndices
                  (lexMaxIndices (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
                    (blowupTripleAtCenterIdeal T).boundary))))) := (minIndexCard_blowupTripleAtCenterIdeal_eq_zero_or_centerInvariant_lt hGeom hT h).resolve_left h'
  refine monomialInvariant_lt_of_lex_lt ?_
  rcases hkeyU with hrank | ⟨hrank, hrest⟩
  left
  obtain ⟨J, C, hcand⟩ :=
    exists_isCandidateComponent_minIndexCard (blowupTripleAtCenterIdeal T).ideal (blowupTripleAtCenterIdeal T).mult
      (blowupTripleAtCenterIdeal T).boundary h'
  unfold IsCandidateComponent at hcand
  obtain ⟨hcard, hCmem, -⟩ := hcand
  have hlt :=
    hGeom.card_lt_dim (blowupTripleAtCenterIdeal T) hTstep.valid J ⟨C, hCmem⟩
  have hdim :=
    le_trans (krullDimSucc_blowupTripleAtCenterIdeal_le hGeom hT h) hD
  omega
  right
  refine ⟨by rw [hrank], ?_⟩
  rcases hrest with hval | ⟨hval, hpos⟩
  left
  exact toNat_lt_toNat_of_lt_of_ne_top hval (maxCandidateOrder_spec hGeom hT h).2.2.2.ne
  right
  refine ⟨by rw [hval], ?_⟩
  let _a0 := p34 $ T.mc
  exact maxOrderCandidatePairs_ncard_lt_of_blowup hGeom hT h
    _a0
    (_a0 ≫ tMp T)
    (p46 _)
    (residualByPow (T.ideal.comap _a0)
      (cmI (T.mc)
        _a0) T.mult)
    (pow_mul_residualByPow _ _ _ $ exists_controlledTransform_monomialCenter hGeom hT h)
    hTstep h' hrank.symm hval.symm





section
variable (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
noncomputable abbrev monomialIterateFromEmpty (n : ℕ) :
    T.mbs :=
  monomialBlowupIterate hinv
    (T.embs) n

noncomputable abbrev monomialStallIndexOfTriple : ℕ :=
  monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary

theorem monomialPrincipalization_length :
    (monomialPrincipalization hinv T).length = monomialStallIndexOfTriple hinv T := by
  rw [monomialPrincipalization_apply, toMarkedSequence_length, monomialBlowupSeq_length]
end


section
variable (T : MarkedIdealWithBoundary) (s : T.mbs)
def tripleAtLastBlowup : MarkedIdealWithBoundary :=
  @mk T.base T.instField (s.obj s.length)
    (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult $ s.boundary s.length


theorem tripleAtLastBlowup_eq_mk_of_length_eq n (hn : s.length = n) :
    tripleAtLastBlowup T s =
      @mk T.base T.instField (s.obj n) (s.proj n ≫ structMap T) (s.ideal n) T.mult
        (s.boundary n) := by
  subst hn
  rfl

theorem minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter
    (h : IsAdmissibleCenter s) :
    minIndexCard (tripleAtLastBlowup T s).ideal (tripleAtLastBlowup T s).mult
      (tripleAtLastBlowup T s).boundary ≠ 0 := by
  intro h0
  exact an1 h $ monomialCenter_eq_top_of_minIndexCard_eq_zero (lastI s) T.mult
    (lastB s) h0

@[simp]
theorem tripleAtLastBlowup_scheme :
    scheme (tripleAtLastBlowup T s) = s.obj s.length := rfl
end

section
variable {A B : Sch} (h : A = B) (J : ISD B)
theorem support_comap_eqToHom_nonempty (hJ : (support J : Set ↥B).Nonempty) :
    (support (comap J $ eqToHom h) : Set ↥A).Nonempty := by
  subst h
  obtain ⟨x, hx⟩ := hJ
  exact ⟨x, Scheme.IdealSheafData.mem_support_comap.mpr $ by simpa using hx⟩

end


theorem minIndexCard_monomialIterateFromEmpty_ne_zero (hinv : ComapIsoInvariance)
    (T : MarkedIdealWithBoundary) (n : ℕ) (hn : n < monomialStallIndexOfTriple hinv T) :
    minIndexCard (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n).ideal
        (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n).mult
        (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n).boundary ≠ 0 :=
  minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T (monomialIterateFromEmpty hinv T n)
    (isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary n hn)

theorem monomialPrincipalization_length_eq_zero_of_empty (hinv : ComapIsoInvariance) :
    ∀ T : MarkedIdealWithBoundary, IsLocallyMonomialTriple T →
      orderAtLeastLocus T.ideal T.mult = ∅ → (monomialPrincipalization hinv T).length = 0 := by
  intro T hT hcs
  let _s0 := T.embs
  have hT0 : tripleAtLastBlowup T _s0 = T := by
    rw [tripleAtLastBlowup_eq_mk_of_length_eq T _s0 0
      (emptyMarkedBlowupSequenceData_length T.structMap T.ideal T.mult T.boundary)]
    exact mk_eq_mk T.scheme T.mult (id_comp T.structMap)
      (emptyMarkedBlowupSequenceData_ideal T.structMap T.ideal T.mult T.boundary 0)
      (emptyMarkedBlowupSequenceData_boundary T.structMap T.ideal T.mult T.boundary 0)
  have hns : ¬ IsAdmissibleCenter
      _s0 := by
    intro hstep
    have h := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T
      _s0 hstep
    rw [hT0] at h
    exact h $ minIndexCard_eq_zero_of_orderAtLeastLocus_eq_empty hT.valid hcs
  rw [monomialPrincipalization_length]
  exact tr_ (rfl) $ monomialStallIndex_eq_zero_of_not_isAdmissibleCenter hinv _s0 hns


theorem markedIdealWithBoundary_mk_comap_eqToHom {k : Type} [instk : Field k] {A B : Sch}
    (hAB : A = B) q (J : ISD B) m
    E :
    @mk k instk A (eqToHom hAB ≫ q) (comap J $ eqToHom hAB) m
        (List.map (fun D => comap D $ eqToHom hAB) E) =
      @mk k instk B q J m E := by
  subst hAB
  refine mk_eq_mk _ _ ?_ ?_ ?_ <;> simp

section
variable (hGeom : MonomialGeometryHypotheses)
include hGeom
theorem isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero
    (T : MarkedIdealWithBoundary) s
    (hs : IsLocallyMonomialTriple $ tripleAtLastBlowup T s)
    (h : minIndexCard (tripleAtLastBlowup T s).ideal (tripleAtLastBlowup T s).mult
      (tripleAtLastBlowup T s).boundary ≠ 0) :
    IsAdmissibleCenter s :=
  monomialCenter_spec hGeom hs h

section
variable (hinv : ComapIsoInvariance)
section
variable (T : MarkedIdealWithBoundary)
theorem isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate
    (hT : IsLocallyMonomialTriple T) (n : ℕ) :
    IsLocallyMonomialTriple $ tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n := by
  induction n with
  | zero =>
    let _a0 := T.embs
    have h0 : monomialIterateFromEmpty hinv T 0 =
        _a0 :=
      monomialBlowupIterate_zero hinv _
    rw [h0]
    have hT0 : tripleAtLastBlowup T _a0 = T := by
      rw [tripleAtLastBlowup_eq_mk_of_length_eq T _a0 0
        (emptyMarkedBlowupSequenceData_length T.structMap T.ideal T.mult T.boundary)]
      exact mk_eq_mk T.scheme T.mult (id_comp T.structMap)
        (emptyMarkedBlowupSequenceData_ideal T.structMap T.ideal T.mult T.boundary 0)
        (emptyMarkedBlowupSequenceData_boundary T.structMap T.ideal T.mult T.boundary 0)
    rwa [hT0]
  | succ n ih =>
    let _a1 := monomialIterateFromEmpty hinv T n
    have hstep : monomialIterateFromEmpty hinv T (n + 1) =
        blowupAtCenter hinv _a1 :=
      monomialBlowupIterate_succ hinv _ n
    rw [hstep]
    let s := _a1
    by_cases hstep : IsAdmissibleCenter s
    have hlen := blowupAtCenter_length hinv s hstep
    let _a2 := blowupAtCenter hinv s
    have key : tripleAtLastBlowup T _a2 =
        blowupTripleAtCenterIdeal (tripleAtLastBlowup T s) := by
      rw [tripleAtLastBlowup_eq_mk_of_length_eq T _a2 (s.length + 1)
          hlen, blowupAtCenter_projectionToBase_succ hinv s hstep, blowupAtCenter_ideal_succ hinv s hstep, blowupAtCenter_boundary_succ hinv s hstep]
      simp only [assoc]
      exact markedIdealWithBoundary_mk_comap_eqToHom (blowupAtCenter_schemeAt_succ hinv s hstep) _ _ _ _
    rw [key]
    exact isLocallyMonomialTriple_blowupTripleAtCenterIdeal hGeom ih $ minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T s hstep
    have _i20 : blowupAtCenter hinv s = s := by
      unfold blowupAtCenter
      rw [dif_neg hstep]
    rwa [_i20]

end

theorem monomialPrincipalization_center_support_nonempty :
    ∀ T : MarkedIdealWithBoundary, IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        (((monomialPrincipalization hinv T).center i).support :
          Set ↥((monomialPrincipalization hinv T).schemeAt i)).Nonempty := by
  intro T hT i hi
  rw [monomialPrincipalization_length] at hi
  have hlen := hi
  have hs := isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT i
  have hmin := minIndexCard_monomialIterateFromEmpty_ne_zero hinv T i hlen
  let _a0 := monomialIterateFromEmpty hinv T i
  let _s0 := tripleAtLastBlowup T _a0
  have hne : (spI (_s0.mc) :
      CSet _s0.scheme).Nonempty := by
    rw [support_monomialCenter hGeom hs hmin]
    exact monomialCenterSet_nonempty hGeom hs hmin
  rw [monomialPrincipalization_apply, toMarkedSequence_center,
    monomialBlowupSeq_center hinv T.structMap T.ideal T.mult T.boundary i hlen]
  exact support_comap_eqToHom_nonempty
    (monomialBlowupSeq_schemeAt hinv T.structMap T.ideal T.mult T.boundary i $ m49 hlen)
    (centerAtLast _a0) hne

theorem monomialPrincipalization_center_subset_boundaryLocus :
    ∀ T : MarkedIdealWithBoundary, IsLocallyMonomialTriple T →
      ∀ i < (monomialPrincipalization hinv T).length,
        ↑((monomialPrincipalization hinv T).center i).support ⊆
          boundaryLocus (monomialPrincipalization hinv T) i := by
  intro T hT i hi
  have hiN : i < monomialStallIndexOfTriple hinv T := by
    rwa [monomialPrincipalization_length] at hi
  rw [monomialPrincipalization_apply]
  intro x hx
  rw [toMarkedSequence_center, monomialBlowupSeq_center hinv T.structMap T.ideal T.mult T.boundary i hiN] at hx
  refine mpr_ (mem_boundaryLocus_iff _ _ _) ?_
  rw [toMarkedSequence_boundary, monomialBlowupSeq_boundary hinv T.structMap T.ideal T.mult T.boundary i $ m49 hiN]
  obtain ⟨D, hD, hxD⟩ :=
    Set.mem_iUnion₂.mp
      ((support_monomialCenter_subset_boundary hGeom
    (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT i)
    (minIndexCard_monomialIterateFromEmpty_ne_zero hinv T i hiN))
        (Scheme.IdealSheafData.mem_support_comap.mp hx))
  exact ⟨_, mpr_ mem_map ⟨D, hD, rfl⟩, Scheme.IdealSheafData.mem_support_comap.mpr hxD⟩

end
end

theorem tripleAtLastBlowup_blowupAtCenter (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (s : T.mbs)
    (hstep : IsAdmissibleCenter s) :
    tripleAtLastBlowup T (blowupAtCenter hinv s) =
      blowupTripleAtCenterIdeal (tripleAtLastBlowup T s) := by
  simp only [tripleAtLastBlowup]
  rw [blowupAtCenter_length hinv s hstep, blowupAtCenter_ideal_succ hinv s hstep, blowupAtCenter_boundary_succ hinv s hstep, blowupAtCenter_projectionToBase_succ hinv s hstep]
  simp only [assoc]
  exact @markedIdealWithBoundary_mk_comap_eqToHom T.base T.instField _ _ (blowupAtCenter_schemeAt_succ hinv s hstep) _ _ _ _

section
variable (hGeom : MonomialGeometryHypotheses) (hinv : ComapIsoInvariance)
include hGeom
section
variable (T : MarkedIdealWithBoundary) (hT : IsLocallyMonomialTriple T)
include hT
theorem exists_isStationaryAt_emptyMarkedBlowupSequenceData :
    ∃ n, IsStationaryAt hinv
      (T.embs) n := by
  let _a0 := T.embs
  let _a1 := tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T 0
  by_contra hcon
  have hstepAll : ∀ n, IsAdmissibleCenter $ monomialIterateFromEmpty hinv T n := by
    intro n
    by_contra hn
    exact hcon ⟨n, mpr_ (isStationaryAt_iff_not_isAdmissibleCenter hinv
      _a0 n) hn⟩
  have hloc :=
    fun n => isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT n
  have hmin :=
    fun n => minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T (monomialIterateFromEmpty hinv T n) $ hstepAll n
  have hmono : ∀ n, tripleAtLastBlowup T (monomialIterateFromEmpty hinv T $ n + 1) =
      blowupTripleAtCenterIdeal (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n) := by
    intro n
    have hit : monomialIterateFromEmpty hinv T (n + 1) =
        blowupAtCenter hinv (monomialIterateFromEmpty hinv T n) :=
      monomialBlowupIterate_succ hinv
        _a0 n
    rw [hit]
    exact tripleAtLastBlowup_blowupAtCenter hinv T (monomialIterateFromEmpty hinv T n) $ hstepAll n
  have hdim : ∀ n,
      krullDimSucc (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n).scheme ≤ tDim T := by
    intro n
    induction n with
    | zero =>
      have h0 : monomialIterateFromEmpty hinv T 0 = _a0 :=
        monomialBlowupIterate_zero hinv
          _a0
      have hsc : scheme _a1 = scheme T := by
        rw [tripleAtLastBlowup_scheme, h0, emptyMarkedBlowupSequenceData_schemeAt]
      exact le_of_eq $ congrArg krullDimSucc hsc
    | succ n ih =>
      rw [hmono n]
      exact le_trans (krullDimSucc_blowupTripleAtCenterIdeal_le hGeom (hloc n) $ hmin n) ih
  have hdec : ∀ n,
      monomialInvariant T.krullDimSucc (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T $ n + 1) <
        monomialInvariant T.krullDimSucc (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n) := by
    intro n
    have h' : minIndexCard (blowupTripleAtCenterIdeal $ tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n).ideal
        (blowupTripleAtCenterIdeal $ tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n).mult
        (blowupTripleAtCenterIdeal $ tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n).boundary ≠ 0 := by
      rw [← hmono n]
      exact hmin $ n + 1
    rw [hmono n]
    exact monomialInvariant_blowupTripleAtCenterIdeal_lt hGeom (hloc n) (hmin n) (hdim n) h'
  have main : ∀ a : Lex $ ℕ × Lex (ℕ × ℕ), Acc (· < ·) a → ∀ n,
      monomialInvariant T.krullDimSucc (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T n) = a → False := by
    intro a ha
    induction ha with
    | intro x hx ih =>
      intro n hn
      refine ih (monomialInvariant T.krullDimSucc
        (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T $ n + 1)) ?_ (n + 1) rfl
      rw [← hn]
      exact hdec n
  exact main (monomialInvariant T.krullDimSucc _a1)
    (wellFounded_lt.apply _) 0 rfl

theorem minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero :
    minIndexCard (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T $ monomialStallIndexOfTriple hinv T).ideal
        (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T $ monomialStallIndexOfTriple hinv T).mult
        (tripleAtLastBlowup T $ monomialIterateFromEmpty hinv T $ monomialStallIndexOfTriple hinv T).boundary = 0 := by
  by_contra hne
  have hstall := isStationaryAt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary
    (exists_isStationaryAt_emptyMarkedBlowupSequenceData hGeom hinv T hT)
  let _a0 := monomialStallIndexOfTriple hinv T
  have hnot := mp_ (isStationaryAt_iff_not_isAdmissibleCenter hinv
    (T.embs) _a0) hstall
  exact hnot $ isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero hGeom T
    (monomialIterateFromEmpty hinv T _a0)
    (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT
      _a0) hne
end

end

noncomputable abbrev MarkedIdealWithBoundary.pullbackWithBoundary (T : MarkedIdealWithBoundary) (Y : Sch)
    (k' : Type) [Field k'] (q : Y ⟶ Sp k') (g : Y ⟶ scheme T)
    (E' : List Y.IdealSheafData) : MarkedIdealWithBoundary :=
  withBoundary (T.pbOF q g) E'

theorem false_of_mem_support_top {X : Sch} y
    (h : y ∈ support (⊤ : ISD X)) : False := by
  rw [mpr_ (support_eq_bot_iff _) rfl] at h
  have h' : y ∈ ((⊥ : m182 X) : Set X) := h
  rw [TopologicalSpace.Closeds.coe_bot] at h'
  simp at h'

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
theorem isNoetherian_schemeAt_of_le_length
    (hX : IsNoetherian X) (d : MarkedBlowupSequenceData p I m E) :
    ∀ i ≤ d.length, IsNoetherian $ d.obj i := by
  have := hX
  intro i
  induction i with
  | zero =>
      intro _
      exact isNoetherian_of_iso d.toBlowupSequenceData.isoZero.symm
  | succ n ih =>
      intro hn
      have := ih $ le_of_lt hn
      exact isNoetherian_of_isBlowupAlongIdealSheaf $ d.toBlowupSequenceData.isBlowup n hn

end

theorem length_monomialIterateFromEmpty_zero (hinv : ComapIsoInvariance) T :
    (monomialIterateFromEmpty hinv T 0).length = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _

theorem nonempty_sequenceOfBlowupsPullback_of_length_eq_one {A B} ph_
    (t : BlowupSequenceData A) (t' : BlowupSequenceData B) (ht : t.length = 1) (ht' : t'.length = 1)
    ps_
    (hps_ : t'.isoZero.hom ≫ ph_ ≫ t.isoZero.inv = ps_) (hflat : Flat ps_)
    (hcen : t'.center 0 = (t.center 0).comap ps_) (hne : t'.center 0 ≠ ⊤) :
    Nonempty $ SequenceOfBlowupsPullback ph_ t'.toSequenceOfBlowups t.toSequenceOfBlowups := by
  have hlt : 0 < t.length := by rw [ht]
                                omega
  have hlt' : 0 < t'.length := by rw [ht']
                                  omega
  have hB' : p15 (t'.map 0) $ cmI (t.center 0) ps_ := by
    have h := t'.isBlowup 0 hlt'
    rwa [hcen] at h
  obtain ⟨qq, -, hqq⟩ := (t.isBlowup 0 hlt).exists_isPullback_of_flat ps_ hB'
  refine ⟨SequenceOfBlowupsPullback.ofLengthOne ph_ t t' ht ht' qq ?_ ?_ hne⟩
  simp_all
  simp_all

section
variable {k1_ k2_ : Type} [Field k1_] [Field k2_] {X1 X2 : Sch} {p1_ : X1 ⟶ Spec (CommRingCat.of k1_)} {I1 : ISD X1} {m1 : ℕ} {E1_ : Bdy X1} {p2_ : X2 ⟶ Spec (CommRingCat.of k2_)} {I2 : ISD X2} {m2 : ℕ} {E2_ : Bdy X2} (g : X2 ⟶ X1) (hg : Flat g) (hinv : ComapIsoInvariance) (S : MarkedBlowupSequenceData p1_ I1 m1 E1_) (S' : MarkedBlowupSequenceData p2_ I2 m2 E2_) (hS : IsAdmissibleCenter S)
include hg hS
theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top
    (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (htop : comap (S.centerAtLast) c.lastMap = ⊤) :
    Nonempty $ SequenceOfBlowupsPullback g S'.toSequenceOfBlowups (blowupAtCenter hinv S).toSequenceOfBlowups := by
  let _c0 := emptyMarkedBlowupSequenceData (lastP S' ≫ p2_) (lastI S') m2 $ lastB S'
  have : Flat c.lastMap := m98 c.isPullback_lastMap.flip inferInstance
  let _a0 := S.monomialBlowupStep hS
  have hmiss : ∀ i, i < mbsLen _a0 →
      ∀ z : (mbsObj _a0 i),
        z ∈ spI (mbsCtr _a0 i) →
        ∀ y : (lastO S'),
          c.lastMap.base y ≠ bsM (_a0.toBlowupSequenceData.projectionToBase i) z := by
    intro i hi z hz y heq
    have hlen : mbsLen _a0 = 1 :=
      monomialBlowupStep_length ..
    have hi0 : i = 0 := by omega
    subst hi0
    have hzz := hz
    have hz2 : c.lastMap.base y ∈ S.centerAtLast.support := by
      rwa [heq]
    have hmem := Scheme.IdealSheafData.mem_support_comap.mpr hz2
    rw [htop] at hmem
    exact false_of_mem_support_top y hmem
  have hE0 : mbsLen _c0 = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _
  have e := SequenceOfBlowupsPullback.ofCentersMissImage c.lastMap (S.monomialBlowupStep hS).toBlowupSequenceData hmiss
    _c0.toBlowupSequenceData hE0
  have c2 := SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData
    _c0.toBlowupSequenceData c e
  refine ⟨?_⟩
  rw [blowupAtCenter_eq_append hinv S hS, append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.ofConcatLengthZero g S'.toBlowupSequenceData
    (S.appendToBlowupSequenceData $ S.monomialBlowupStep hS).toSequenceOfBlowups
    _c0.toBlowupSequenceData hE0 c2

theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter
    (hS' : IsAdmissibleCenter S') (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (hcen : S'.centerAtLast = (S.centerAtLast).comap c.lastMap) :
    Nonempty (SequenceOfBlowupsPullback g (blowupAtCenter hinv S').toSequenceOfBlowups
      (blowupAtCenter hinv S).toSequenceOfBlowups) := by
  have : Flat c.lastMap := m98 c.isPullback_lastMap.flip inferInstance
  let _a0 := c.lastMap ≫ (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv
  have h1 : (S'.monomialBlowupStep hS').toBlowupSequenceData.isoZero.hom ≫ _a0
      = _a0 :=
    id_comp _
  have h2 : _a0 = c.lastMap :=
    comp_id _
  obtain ⟨e⟩ := nonempty_sequenceOfBlowupsPullback_of_length_eq_one c.lastMap
    (S.monomialBlowupStep hS).toBlowupSequenceData
    (S'.monomialBlowupStep hS').toBlowupSequenceData (monomialBlowupStep_length ..)
    (monomialBlowupStep_length ..) c.lastMap (tr_ h1 h2)
    (m98 c.isPullback_lastMap.flip inferInstance) hcen ((fun _ h => an1 h) S' hS')
  refine ⟨?_⟩
  rw [blowupAtCenter_eq_append hinv S hS,
    blowupAtCenter_eq_append hinv S' hS',
    append_toBlowupSequenceData, append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData (S'.monomialBlowupStep hS').toBlowupSequenceData c e
end

section
variable (hGeom : MonomialGeometryHypotheses)
include hGeom
theorem minIndexCard_ne_zero_and_monomialCenter_comap_of_flat
    (Tn : MarkedIdealWithBoundary)
    (Yj : Sch) (k' : Type) [instk' : Field k'] qj
    ph_ (hph : Flat ph_)
    I' E2
    (hTn : IsLocallyMonomialTriple Tn)
    (hTj : IsLocallyMonomialTriple $ @mk k' instk' Yj qj I' Tn.mult E2)
    (hI' : I' = Tn.ideal.comap ph_)
    (hE2 : SameNontrivialBoundary E2 $ Tn.boundary.map fun D => D.comap ph_)
    (hordph : ∀ A y,
      orderAt (A.comap ph_) y = orderAt A (ph_ y)) :
    (minIndexCard I' Tn.mult E2 ≠ 0 → minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0) ∧
      (minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0 →
        ((Tn.mc).comap ph_ = ⊤ ∨
          (minIndexCard I' Tn.mult E2 ≠ 0 ∧
            monomialCenter I' Tn.mult E2 = (Tn.mc).comap ph_))) := by
  let _a0 := Tn.pbOF qj ph_
  classical
  subst hI'
  have htrip : tWB (@mk k' instk' Yj qj (Tn.ideal.comap ph_) Tn.mult E2)
      (Tn.boundary.map fun D => cmI D ph_) = _a0 :=
    mk_eq_mk Yj Tn.mult rfl rfl rfl
  have hTpb : IsLocallyMonomialTriple _a0 := by
    rw [← htrip]
    exact MonomialCenter.isLocallyMonomialTriple_withBoundary hGeom _ hTj _ hE2
  have hP :=
    MonomialCenter.IsComponentCompatiblePullback.of_flat hGeom Tn hTn.valid Yj k' qj ph_ hTpb.valid hordph
  have hmin :=
    (minIndexCard_eq_of_sameNontrivialBoundary (Tn.ideal.comap ph_) Tn.mult hE2).symm
  constructor
  intro hne
  have hne' := hne
  rw [← hmin] at hne'
  exact an1 $ minIndexCard_ne_zero_and_le_pullbackOverField hGeom Tn Yj k' qj ph_ hTn hTpb hP hne'
  intro h0
  by_cases hz : minIndexCard _a0.ideal _a0.mult
      _a0.boundary = 0
  exact inl $ comap_monomialCenter_eq_top hGeom Tn Yj k' qj ph_ hTn hTpb hP h0
    (inl hz)
  have hle := (minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le hGeom Tn Yj k' qj ph_ hTn hTpb
    hP).resolve_left hz
  rw [centerInvariant_le_iff] at hle
  rcases hle with hlt | ⟨hm, hx, hs⟩
  exact inl $ comap_monomialCenter_eq_top hGeom Tn Yj k' qj ph_ hTn hTpb hP h0
    (inr hlt)
  refine inr ⟨?_, ?_⟩
  rwa [← hmin]
  rw [← (monomialCenter_eq_of_sameNontrivialBoundary (Tn.ideal.comap ph_) Tn.mult hE2).symm]
  exact monomialCenter_pullbackOverField_eq_comap hGeom Tn Yj k' qj ph_ hTn hTpb hP
    hm.symm hx.symm
    (lexMaxIndices_pullbackOverField_eq_image Tn Yj k' qj ph_ hs)

section
variable (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary) (Y : Sch) (k' : Type) [Field k'] (q : Y ⟶ Sp k') (g : Y ⟶ scheme T)
section
variable (hg : Flat g) (E' : Bdy Y) (hT : IsLocallyMonomialTriple T) (hE : SameNontrivialBoundary E' (T.boundary.map fun D => comap D g)) (hT' : IsLocallyMonomialTriple $ T.pullbackWithBoundary Y k' q g E') (hord : ∀ (B : Sch) (b : B ⟶ scheme T) (pB : B ⟶ Sp T.base), b ≫ structMap T = pB → ∀ (IB : ISD B) (EB : Bdy B), IsAdmissible (@mk T.base T.instField B pB IB T.mult EB) → ∀ (Q : Sch) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g → ∀ (A : ISD B) (z : ↥Q), orderAt (comap A a) z = orderAt A (a z))
include hg hT hE hT' hord
theorem sequenceOfBlowupsPullback_blowupAtCenter_cases
    (S : T.mbs)
    (S' : MarkedBlowupSequenceData (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary)
    (hTn : IsLocallyMonomialTriple (tripleAtLastBlowup T S))
    (hTj : IsLocallyMonomialTriple
      (tripleAtLastBlowup (T.pullbackWithBoundary Y k' q g E') S'))
    (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups) :
    (IsAdmissibleCenter S' →
        minIndexCard (tripleAtLastBlowup T S).ideal (tripleAtLastBlowup T S).mult
          (tripleAtLastBlowup T S).boundary ≠ 0) ∧
      (IsAdmissibleCenter S →
        Nonempty (SequenceOfBlowupsPullback g S'.toSequenceOfBlowups
            (blowupAtCenter hinv S).toSequenceOfBlowups) ∨
          (IsAdmissibleCenter S' ∧
            Nonempty (SequenceOfBlowupsPullback g
              (blowupAtCenter hinv S').toSequenceOfBlowups
              (blowupAtCenter hinv S).toSequenceOfBlowups))) := by
  let _a0 := T.pullbackWithBoundary Y k' q g E'
  classical
  have hfl1 : Flat g := hg
  have hfl2 : @Flat _a0.scheme T.scheme g := hg
  have hflt : Flat c.lastMap := m98 c.isPullback_lastMap.flip inferInstance
  have hN : ∀ i, i ≤ S.length → IsNoetherian (S.obj i) :=
    isNoetherian_schemeAt_of_le_length hT.valid.isNoetherian S
  obtain ⟨hIdeal, hboundary⟩ := SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap S S' c rfl hE hN (isNoetherian_schemeAt_of_le_length hT'.valid.isNoetherian S')
  have hsq : IsPullback c.lastMap (S'.proj S'.length) (S.proj S.length) g := by
    rw [projectionToBase_eq_toSequenceOfBlowups S S.length,
      projectionToBase_eq_toSequenceOfBlowups S' S'.length]
    exact c.isPullback_lastMap
  have hminCard := minIndexCard_ne_zero_and_monomialCenter_comap_of_flat hGeom (tripleAtLastBlowup T S)
    (lastO S') k' (lastP S' ≫ q) c.lastMap
    (m98 c.isPullback_lastMap.flip inferInstance) (lastI S') (lastB S')
    hTn hTj hIdeal hboundary fun A y => hord (lastO S) (lastP S) (lastP S ≫ tMp T) rfl (lastI S) (lastB S) hTn.valid (lastO S') c.lastMap (lastP S') hsq A y
  refine ⟨fun hok' => hminCard.1
    (minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter _a0 S' hok'), ?_⟩
  intro hok
  have h0 := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T S hok
  rcases hminCard.2 h0 with hmiss | ⟨hne', hcenEq⟩
  exact inl
    (nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top g hg hinv S S' hok c hmiss)
  have hok' :=
    isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero hGeom _a0 S'
      hTj hne'
  exact inr ⟨hok', nonempty_sequenceOfBlowupsPullback_blowupAtCenter g hg hinv S S' hok hok' c hcenEq⟩

theorem exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty
    n :
    n ≤ monomialStallIndexOfTriple hinv T →
    ∃ j,
      (∀ j', j' < j →
        IsAdmissibleCenter (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j')) ∧
      Nonempty (SequenceOfBlowupsPullback g
        (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j).toSequenceOfBlowups
        (monomialIterateFromEmpty hinv T n).toSequenceOfBlowups) := by
  induction n with
  | zero =>
    intro _
    refine ⟨0, fun j' hj' => absurd hj' $ not_lt_zero j', ⟨?_⟩⟩
    refine SequenceOfBlowupsPullback.ofCentersMissImage g (monomialIterateFromEmpty hinv T 0).toBlowupSequenceData ?_
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') 0).toBlowupSequenceData
      (length_monomialIterateFromEmpty_zero hinv $ T.pullbackWithBoundary Y k' q g E')
    intro i hi
    exact absurd hi (by rw [length_monomialIterateFromEmpty_zero hinv T]; exact not_lt_zero i)
  | succ n ih =>
    intro hn
    have hn' := lt_of_lt_of_le (lt_succ_self n) hn
    obtain ⟨j, hjstep, hc⟩ := ih $ le_of_lt hn'
    obtain ⟨c⟩ := hc
    rcases (sequenceOfBlowupsPullback_blowupAtCenter_cases hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T n)
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT n)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        (T.pullbackWithBoundary Y k' q g E') hT' j) c).2 (isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary n hn') with h | ⟨hok', h⟩
    exact ⟨j, hjstep, h⟩
    refine ⟨j + 1, ?_, h⟩
    intro j' hj'
    rcases lt_or_eq_of_le (mp_ lt_succ_iff hj') with h1 | h1
    exact hjstep j' h1
    simp_all
end

theorem monomialPrincipalization_isPullbackBlowupSequence_of_flat [Flat g] (E' : Bdy Y)
    (hT : IsLocallyMonomialTriple T)
    (hE : SameNontrivialBoundary E' $ T.boundary.map fun D => comap D g)
    (hT' : IsLocallyMonomialTriple $ T.pullbackWithBoundary Y k' q g E')
    (hord : ∀ B b pB,
      b ≫ structMap T = pB →
      ∀ (IB : ISD B) (EB : Bdy B),
        IsAdmissible (@mk T.base T.instField B pB IB T.mult EB) →
        ∀ (Q : Sch) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : ISD B) (z : ↥Q), orderAt (comap A a) z = orderAt A (a z)) :
    IsPullbackBlowupSequence g
      (monomialPrincipalization hinv $ T.pullbackWithBoundary Y k' q g E').toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  let _c0 := T.pullbackWithBoundary Y k' q g E'
  classical
  have hg : Flat g := inferInstance
  let _a1 := monomialStallIndexOfTriple hinv T
  obtain ⟨j, hjstep, hc⟩ := exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty hGeom hinv T Y k' q g hg E'
    hT hE hT' hord _a1 le_rfl
  obtain ⟨c⟩ := hc
  let _a0 := monomialIterateFromEmpty hinv _c0 j
  have hstall : ¬ IsAdmissibleCenter
      _a0 := by
    intro hok'
    exact (sequenceOfBlowupsPullback_blowupAtCenter_cases hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T _a1)
      _a0
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT
        _a1)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        _c0 hT' j) c).1 hok' $ minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero hGeom hinv T hT
  rw [monomialPrincipalization_apply, monomialPrincipalization_apply, monomialBlowupSeq_eq_monomialBlowupIterate,
    monomialBlowupSeq_eq_monomialBlowupIterate, monomialStallIndex_eq_of_isStationaryAt hinv _c0.structMap _c0.ideal _c0.mult _c0.boundary j (mpr_ (isStationaryAt_iff_not_isAdmissibleCenter hinv (_c0.embs) j) hstall) hjstep]
  exact SequenceOfBlowupsPullback.isPullbackSequenceOfBlowups c
end
end

private theorem smooth_fst_of_isPullback {X Y B Q : Sch} {hm : Y ⟶ X}
    [Smooth hm] {b : B ⟶ X} {a : Q ⟶ B} {b' : Q ⟶ Y}
    (hsq : IsPullback a b' b hm) : Smooth a :=
  m98 hsq.flip inferInstance

theorem monomialPrincipalization_isPullbackBlowupSequence_of_smooth
    (hGeom : MonomialGeometryHypotheses) (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (hT : IsLocallyMonomialTriple T)
    (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
    [Smooth h] (_hq : h ≫ structMap T = q) (E' : Bdy Y)
    (hE : SameNontrivialBoundary (T.pbA q h).boundary E')
    (hT' : IsLocallyMonomialTriple $ T.pbB q h E') :
    IsPullbackBlowupSequence h
      (monomialPrincipalization hinv $ T.pbB q h E').toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  have : Flat h := inferInstance
  refine monomialPrincipalization_isPullbackBlowupSequence_of_flat hGeom hinv T Y T.base q h E' hT hE.symm hT' ?_
  intro B b pB hbp IB EB hvalid Q a b' hsq A z
  have := hvalid.charZero
  have := hvalid.smooth
  have := smooth_fst_of_isPullback hsq
  exact orderAt_comap T.base pB a A z




instance instSurjectivePullbackFstSpecMapField (k L : Type) [Field k] [Field L]
    (f : k →+* L) (X : Sch) (p : X ⟶ Sp k) :
    Surjective $ pullback.fst p $ specMapOfFieldHom k L f :=
  inferInstance





theorem toMarkedSequence_projectionToBase {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
    {E : Bdy X} (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase i = s.proj i :=
  (s.projectionToBase_eq_toSequenceOfBlowups i).symm

theorem isPullbackBlowupSequence_congr (F : PrincipalizationAssignment)
    {k1_ k2_ : Type} [Field k1_] [Field k2_] {B Q : Sch}
    (pB : B ⟶ Spec (CommRingCat.of k1_)) (IB : ISD B) (mB : ℕ)
    (EB : Bdy B) (q : Q ⟶ B)
    (pQ1 pQ2 : Q ⟶ Spec (CommRingCat.of k2_)) (IQ1 IQ2 : ISD Q) (mQ1 mQ2 : ℕ)
    (EQ1 EQ2 : Bdy Q)
    (hp : pQ1 = pQ2) (hI : IQ1 = IQ2) (hm : mQ1 = mQ2) (hE : EQ1 = EQ2)
    (h : IsPullbackBlowupSequence q (F $ mk k2_ Q pQ1 IQ1 mQ1 EQ1).toSequenceOfBlowups
        (F $ mk k1_ B pB IB mB EB).toSequenceOfBlowups) :
    IsPullbackBlowupSequence q (F $ mk k2_ Q pQ2 IQ2 mQ2 EQ2).toSequenceOfBlowups
      (F $ mk k1_ B pB IB mB EB).toSequenceOfBlowups := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact h

section
variable {X : Sch}
section
variable (s : SequenceOfBlowups X)
theorem BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length :
    (ofSequenceOfBlowups s).toSequenceOfBlowups.length = s.length := by
  rw [p14]
  rfl

theorem ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt (j : ℕ) :
    (ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt j = schemeAt s j :=
  (toSequenceOfBlowups_schemeAt _ j).trans $ ofSequenceOfBlowups_schemeAt s j

theorem le_length_of_le_ofSequenceOfBlowups_length {j : ℕ}
    (hj : j ≤ (ofSequenceOfBlowups s).toSequenceOfBlowups.length) : j ≤ s.length :=by simp_all
theorem le_ofSequenceOfBlowups_length_of_le_length {j : ℕ}
    (hj : j ≤ s.length) : j ≤ (ofSequenceOfBlowups s).toSequenceOfBlowups.length :=by simp_all
end

theorem BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups (t : SequenceOfBlowups X) (j : ℕ) :
    (ofSequenceOfBlowups t).toSequenceOfBlowups.projectionToBase j = t.projectionToBase j :=
  (toSequenceOfBlowups_projectionToBase (ofSequenceOfBlowups t) j).trans $ ofSequenceOfBlowups_projectionToBase t j
end

namespace SequenceOfBlowupsPullback

variable {X X' : Sch} {ph_ : X' ⟶ X} {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}

section
variable (c : SequenceOfBlowupsPullback ph_ s' s)
def ofSequenceOfBlowupsMap (j : ℕ)
    (hj : j ≤ (ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    (ofSequenceOfBlowups s').toSequenceOfBlowups.schemeAt j ⟶ (ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt (c.idx j) :=
  eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j) ≫ c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj) ≫
    eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s $ c.idx j).symm

theorem ofSequenceOfBlowups_map_eq (j : ℕ)
    (hj : j ≤ (ofSequenceOfBlowups s').toSequenceOfBlowups.length) :
    ofSequenceOfBlowupsMap c j hj = c.map j (le_length_of_le_ofSequenceOfBlowups_length s' hj) := by
  let _a0 := c.map j $ le_length_of_le_ofSequenceOfBlowups_length s' hj
  show 𝟙 (sbAt s' j) ≫ _a0 ≫ 𝟙 (sbAt s $ c.idx j)
      = _a0
  exact tr_ (id_comp _) $ comp_id _
end

private theorem isPullback_congr {A B C D : Sch} {f f' : A ⟶ B} {g g' : A ⟶ C}
    {h h' : B ⟶ D} {k k' : C ⟶ D} (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (H : IsPullback f g h k) : IsPullback f' g' h' k' :=by simp_all
section
variable {W : Sch} (t : SequenceOfBlowups W)
section
variable {i i' : ℕ} (h : i ≤ i')
private theorem ofSequenceOfBlowups_transitionMap : (ofSequenceOfBlowups t).transitionMap h = t.transitionMap h := by
  let _a0 := ofSequenceOfBlowups t
  induction h with
  | refl =>
      have e1 : _a0.transitionMap (le_refl i) = 𝟙 (_a0.obj i) := by
        rw [transitionMap_refl]
      have e2 : t.transitionMap (le_refl i) = 𝟙 (sbAt t i) := by
        rw [transitionMap_self_eq_id]
      exact tr_ e1 e2.symm
  | @step m hm ih =>
      refine tr_ ((transitionMap_comp_transitionMap (ofSequenceOfBlowups t) hm $ le_succ m).symm) $ tr_ (congrArg (fun f : sbAt t (m + 1) ⟶ sbAt t m => f ≫ _a0.transitionMap hm) $ (transitionMap_succ (ofSequenceOfBlowups t) m).trans $ ofSequenceOfBlowups_blowupMorphism t m) $ tr_ (congrArg (fun g => transitionMapSucc t m ≫ g) ih) ?_
      rw [blowupMorphism_eq_transitionMap]
      exact transitionMap_trans t hm $ le_succ m

theorem ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap : (ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMap h = transitionMap t h :=
  (toSequenceOfBlowups_transitionMap (ofSequenceOfBlowups t) h).trans $ ofSequenceOfBlowups_transitionMap t h
end

theorem ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism (i : ℕ) :
    (ofSequenceOfBlowups t).toSequenceOfBlowups.transitionMapSucc i = t.transitionMapSucc i :=
  (blowupMorphism_eq_transitionMap ((ofSequenceOfBlowups t).toSequenceOfBlowups) i).trans
    (tr_ (ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap t $ le_succ i)
      (blowupMorphism_eq_transitionMap t i).symm)
end

theorem eqToHom_refl_comp_comp_eqToHom_refl {A B : Sch} (hA : A = A) (hB : B = B)
    (f : A ⟶ B) : eqToHom hA ≫ f ≫ eqToHom hB = f :=by simp_all
section
variable (c : SequenceOfBlowupsPullback ph_ s' s)
include c
def toBlowupDataOfSeq :
    SequenceOfBlowupsPullback ph_ (ofSequenceOfBlowups s').toSequenceOfBlowups (ofSequenceOfBlowups s).toSequenceOfBlowups where
  idx := c.idx
  map := ofSequenceOfBlowupsMap c
  idx_length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s]
    exact c.idx_length
  idx_lt := by
    intro j hj
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact c.idx_lt j hj
  idx_strictMono := by
    intro j hj
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj
    exact c.idx_strictMono j hj
  isPullback := by
    intro j hj
    exact isPullback_congr (ofSequenceOfBlowups_map_eq c j hj).symm
      (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s' j).symm
      (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s $ c.idx j).symm rfl
      (c.isPullback j $ le_length_of_le_ofSequenceOfBlowups_length s' hj)
  step := by
    intro j hj
    have hlt : j < s'.length := by simp_all
    rw [ofSequenceOfBlowups_map_eq c j $ le_of_lt hj, ofSequenceOfBlowups_map_eq c (j + 1) hj,
      ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism, ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap]
    exact c.step j hlt
  center_comap := by
    intro j hj
    have hj' := lt_of_lt_of_le hj $ le_of_eq $ BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s'
    have hmap : ofSequenceOfBlowupsMap c j (le_of_lt hj) = c.map j (le_of_lt hj') :=
      eqToHom_refl_comp_comp_eqToHom_refl (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j) (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s $ c.idx j).symm
        (c.map j $ le_length_of_le_ofSequenceOfBlowups_length s' $ le_of_lt hj)
    rw [hmap]
    exact c.center_comap j hj'
  center_ne_top := by
    intro j hj
    have hj' := lt_of_lt_of_le hj $ le_of_eq $ BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s'
    exact c.center_ne_top j hj'
  omitted := by
    intro i hi hmiss z hz x'
    have hi' : i < s.length := by simp_all
    have hmiss' : ∀ j : ℕ, j < s'.length → c.idx j ≠ i := by simp_all
    have h := c.omitted i hi' hmiss' z hz x'
    rw [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i]
    exact h
end

section
variable (c : SequenceOfBlowupsPullback ph_ (ofSequenceOfBlowups s').toSequenceOfBlowups (ofSequenceOfBlowups s).toSequenceOfBlowups)
include c
def transportedMap
    (j : ℕ) (hj : j ≤ s'.length) : s'.schemeAt j ⟶ s.schemeAt (c.idx j) :=
  eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j).symm ≫ c.map j (le_ofSequenceOfBlowups_length_of_le_length s' hj) ≫
    eqToHom (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s $ c.idx j)

theorem transportedMap_eq_map
    (j : ℕ) (hj : j ≤ s'.length) :
    transportedMap c j hj = c.map j (le_ofSequenceOfBlowups_length_of_le_length s' hj) :=
  eqToHom_refl_comp_comp_eqToHom_refl (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j).symm (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s $ c.idx j)
    (c.map j $ le_ofSequenceOfBlowups_length_of_le_length s' hj)

def ofBlowupDataOfSeq :
    SequenceOfBlowupsPullback ph_ s' s where
  idx := c.idx
  map := transportedMap c
  idx_length := by
    have h := c.idx_length
    rwa [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s', BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length s] at h
  idx_lt := by
    intro j hj
    have hj' := hj
    rw [← BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj'
    have h := c.idx_lt j hj'
    rwa [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at h
  idx_strictMono := by
    intro j hj
    refine c.idx_strictMono j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length]
    exact hj
  isPullback := by
    intro j hj
    exact isPullback_congr (transportedMap_eq_map c j hj).symm (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s' j)
      (BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s $ c.idx j) rfl
      (c.isPullback j $ le_ofSequenceOfBlowups_length_of_le_length s' hj)
  step := by
    intro j hj
    have hj' := hj
    rw [← BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj'
    have key := c.step j hj'
    rw [ofSequenceOfBlowups_toSequenceOfBlowups_blowupMorphism, ofSequenceOfBlowups_toSequenceOfBlowups_transitionMap] at key
    rw [transportedMap_eq_map c j $ le_of_lt hj, transportedMap_eq_map c (j + 1) hj]
    exact key
  center_comap := by
    intro j hj
    have hj' := hj
    rw [← BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj'
    have hmap : transportedMap c j (le_of_lt hj) = c.map j (le_of_lt hj') :=
      eqToHom_refl_comp_comp_eqToHom_refl (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s' j).symm (ofSequenceOfBlowups_toSequenceOfBlowups_schemeAt s $ c.idx j)
        (c.map j $ le_ofSequenceOfBlowups_length_of_le_length s' $ le_of_lt hj)
    rw [hmap]
    exact c.center_comap j hj'
  center_ne_top := by
    intro j hj
    have hj' := hj
    rw [← BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hj'
    exact c.center_ne_top j hj'
  omitted := by
    intro i hi hmiss z hz x'
    have hi' := hi
    rw [← BlowupSequenceData.toSequenceOfBlowups_ofSequenceOfBlowups_length] at hi'
    have hmiss' : ∀ j : ℕ, j < (ofSequenceOfBlowups s').toSequenceOfBlowups.length → c.idx j ≠ i := by simp_all
    have h := c.omitted i hi' hmiss' z hz x'
    rwa [BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups s i] at h
end

end SequenceOfBlowupsPullback





def markedPullbackSquareId {T : MarkedIdealWithBoundary} {Y : Sch} (g : Y ⟶ scheme T)
    (hT : IsAdmissible T) : MarkedPullbackSquare T g where
  baseScheme := scheme T
  topScheme := Y
  bottom := 𝟙 T.scheme
  structMap := structMap T
  ideal := ideal T
  mult := mult T
  boundary := boundary T
  left := g
  top := 𝟙 Y
  bottom_structMap := id_comp T.structMap
  dim_le := le_rfl
  isPullback := (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  valid := hT

theorem projectionToBase_mem_orderAtLeastLocus_tripleAtLength (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance)
    (T : MarkedIdealWithBoundary)
    (s : T.mbs)
    J mu_ (hJ : (tripleAtLength T s J mu_).IsAdmissible)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J mu_ $ s.boundary s.length)
    j (hj : j ≤ σ.toSequenceOfBlowups.length) z
    (hz : z ∈ orderAtLeastLocus (σ.ideal j) mu_) :
    (σ.toSequenceOfBlowups.projectionToBase j).base z ∈ orderAtLeastLocus J mu_ := by
  let _a0 := tripleAtLength T s J mu_
  have hval : ∀ l ≤ msLen σ, tAd $ _a0.transformAt σ l := by
    intro l hl
    exact hG.monomialInputs.level_valid _a0 hJ σ l hl
  have hsub := orderAtLeastLocus_subset_preimage_transitionMap
    (orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs)
    _a0 σ hval mu_ le_rfl 0 j (zero_le j) hj
  have h0 := hsub hz
  rw [σ.ideal_zero, hinv.coSupport_comap σ.toSequenceOfBlowups.isoZero J mu_] at h0
  have hcomp : bsM (σ.toSequenceOfBlowups.projectionToBase j) z
      = bsM (σ.toSequenceOfBlowups.isoZero.hom) (bsM (σ.toSequenceOfBlowups.transitionMap $ zero_le j) z) := by
    rw [projectionToBase_def]
    simp
  rwa [hcomp]

section
variable (hinv : ComapIsoInvariance)
section
variable (F) (n) (T : MarkedIdealWithBoundary) (hT : IsAdmissible T) {Y} (g : Y ⟶ scheme T) (k' : Type) [Field k'] (q) (hbc : BaseChangeCompatible hinv F n T g k' q)
include hT hbc
theorem orderAt_comap_of_baseChangeCompatible
    (A : tISD T) (y : ↥Y) :
    orderAt (comap A g) y = orderAt A (g.base y) :=
  MarkedPullbackSquare.orderAt_comap_verticalMap (markedPullbackSquareId g hT) hT hbc.order A y

theorem orderAtLeastLocus_comap_eq_empty_of_baseChangeCompatible
    (h : orderAtLeastLocus T.ideal T.mult = ∅) :
    orderAtLeastLocus (T.ideal.comap g) T.mult = ∅ := by
  refine eq_empty_of_subset_empty ?_
  intro y hy
  have hy' := (mem_orderAtLeastLocus_iff (T.ideal.comap g) T.mult y).1 hy
  rw [orderAt_comap_of_baseChangeCompatible hinv F n T hT g k' q hbc T.ideal y] at hy'
  have hmem := (mem_orderAtLeastLocus_iff T.ideal T.mult _).2 hy'
  rw [h] at hmem
  simp [mem_empty_iff_false] at hmem
end

section
variable (T : MarkedIdealWithBoundary) (rc : (S : MarkedIdealWithBoundary) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) (s : T.mbs)
section
variable (J : IdealSheafData (s.obj s.length)) (mu_ : ℕ)
section
variable (hd : (tripleAtLength T s J mu_).krullDimSucc ≤ T.krullDimSucc)
theorem appendRecursivePrincipalization_eq_append_of_eq_some
    (d : MarkedBlowupSequenceData (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult
      (s.boundary s.length))
    (h : markedDataOfSeq s J mu_ (rc (tripleAtLength T s J mu_) hd) = some d) :
    appendRecursivePrincipalization hinv T rc s J mu_ = s.append d hinv := by
  have h1 : appendRecursivePrincipalization hinv T rc s J mu_ = appendIfMarked hinv s J mu_ (rc (tripleAtLength T s J mu_) hd) := by
    unfold appendRecursivePrincipalization
    exact dif_pos hd
  rw [h1]
  unfold appendIfMarked
  rw [h]

theorem appendRecursivePrincipalization_eq_self_of_eq_none
    (h : markedDataOfSeq s J mu_ (rc (tripleAtLength T s J mu_) hd) = none) :
    appendRecursivePrincipalization hinv T rc s J mu_ = s := by
  have h1 : appendRecursivePrincipalization hinv T rc s J mu_ = appendIfMarked hinv s J mu_ (rc (tripleAtLength T s J mu_) hd) := by
    unfold appendRecursivePrincipalization
    exact dif_pos hd
  rw [h1]
  unfold appendIfMarked
  rw [h]
end

theorem appendRecursivePrincipalization_eq_self_or_append :
    appendRecursivePrincipalization hinv T rc s J mu_ = s ∨
      ∃ t : MarkedBlowupSequenceData (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult
        (s.boundary s.length), appendRecursivePrincipalization hinv T rc s J mu_ = s.append t hinv := by
  let _a0 := tripleAtLength T s J mu_
  unfold appendRecursivePrincipalization
  by_cases hd : tDim _a0 ≤ tDim T
  rw [dif_pos hd]
  unfold appendIfMarked
  cases hrem : markedDataOfSeq s J mu_ (rc _a0 hd) with
  | none => exact inl rfl
  | some d => exact inr ⟨d, rfl⟩
  rw [dif_neg hd]
  exact inl rfl
end

theorem appendRecursivePrincipalization_congr
    J K mu_ nu_ (hJK : J = K) (hmunu : mu_ = nu_) :
    appendRecursivePrincipalization hinv T rc s J mu_ = appendRecursivePrincipalization hinv T rc s K nu_ := by
  subst hJK
  subst hmunu
  rfl
end
end

section
variable {A B : Sch} (f : A ⟶ B)
theorem comap_pow_sup_pow (N J : ISD B)
    a b : comap (N ^ a ⊔ J ^ b) f = (comap N f) ^ a ⊔ (comap J f) ^ b := by
  simp [comap_sup, comap_pow]

theorem pow_sup_pow_eq_comap_pow_sup_pow
    (N1 N2 : ISD B) M1_ M2_ a a' b b'
    (h1_ : M1_ = comap N1 f) (h2_ : M2_ = comap N2 f) (ha : a = a') (hb : b = b') :
    M1_ ^ a ⊔ M2_ ^ b = comap (N1 ^ a' ⊔ N2 ^ b') f := by
  subst h1_
  subst h2_
  subst ha
  subst hb
  exact sy_ $ comap_pow_sup_pow f N1 N2 _ _
end

theorem transformAt_eq_mk (T : MarkedIdealWithBoundary) (s : T.SequenceOfBlowups) (i : ℕ) :
    T.transformAt s i =
      mk T.base (s.schemeAt i) (s.projectionToBase i ≫ T.structMap) (s.ideal i) T.mult
        (s.boundary i) := rfl

theorem isAdmissible_tripleAtLength_congr (T : MarkedIdealWithBoundary)
    (s : T.mbs)
    J K mu_ nu_ (hJK : J = K) (hmunu : mu_ = nu_)
    (h : IsAdmissible $ tripleAtLength T s J mu_) : IsAdmissible $ tripleAtLength T s K nu_ :=by simp_all
section
variable (hmg : MonomialGeometryHypotheses) (T : MarkedIdealWithBoundary) (hT : IsAdmissible T) (s : T.mbs)
include hmg hT
theorem MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim :
    krullDimSucc (s.obj s.length) ≤ T.krullDimSucc :=
  hmg.level_schemeDim_le T hT s.toMarkedSequenceOfBlowups s.length le_rfl

theorem MonomialGeometryHypotheses.isAdmissible_tripleAtLength :
    (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.proj s.length ≫ structMap T)
      (s.ideal s.length) T.mult $ s.boundary s.length).IsAdmissible := by
  have h := hmg.level_valid T hT s.toMarkedSequenceOfBlowups s.length le_rfl
  rw [transformAt_eq_mk T s.toMarkedSequenceOfBlowups s.length,
    toMarkedSequence_projectionToBase s s.length] at h
  exact h
end

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
theorem isAdmissible_mk_congr {I1 I2} {m1 m2}
    {E} (hI : I1 = I2) (hm : m1 = m2)
    (h : IsAdmissible $ mk k X p I1 m1 E) : IsAdmissible $ mk k X p I2 m2 E :=by simp_all
noncomputable def markedBlowupSequenceDataAtEndOfIsMarked {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedBlowupSequenceData p I m E) (J : IdealSheafData $ s.obj s.length) (mu_ : ℕ)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J mu_ $ s.boundary s.length)
    (hm : (ofMarkedSequence σ).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m
      (s.boundary s.length)) :
    MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length :=
  (ofMarkedSequence σ).toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m
    (s.boundary s.length) hm
end

section
variable {X : Sch} (N : ISD X)
theorem maxOrderOn_le_of_forall S
    K (h : ∀ m : ℕ, ∀ x ∈ S, (m : ENat) ≤ orderAt N x → m ≤ K) :
    maxOrderOn N S ≤ K := by
  unfold maxOrderOn
  refine csSup_le' ?_
  intro m hmem
  obtain ⟨x, hx, hmx⟩ := hmem
  exact h m x hx hmx

theorem orderAtLeastLocus_sSup_nonempty
    (x0_ : ↥X)
    (hbound : ∀ x : ↥X,
      orderAt N x ≤ ((sSup {m : ℕ | ∃ y : ↥X, (m : ENat) ≤ orderAt N y} : ℕ) : ENat)) :
    (orderAtLeastLocus N $ sSup {m : ℕ | ∃ y, (m : ENat) ≤ orderAt N y}).Nonempty := by
  have hne : {m : ℕ | ∃ y, m ≤ orderAt N y}.Nonempty := by
    refine ⟨0, x0_, ?_⟩
    simp
  have hbdd : BddAbove {m : ℕ | ∃ y, m ≤ orderAt N y} := by
    refine ⟨sSup {m : ℕ | ∃ y, m ≤ orderAt N y}, ?_⟩
    intro m hm
    obtain ⟨y, hy⟩ := hm
    exact_mod_cast (hy.trans $ hbound y)
  obtain ⟨y, hy⟩ := sSup_mem hne hbdd
  exact ⟨y, (mem_orderAtLeastLocus_iff N _ y).2 hy⟩
end

theorem exists_mem_orderAtLeastLocus_of_mem_center_append (hG : PrincipalizationGeometryHypotheses)
    (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (s : T.mbs)
    (J : (s.obj s.length).IdealSheafData) (mu_ : ℕ) (hJ : (tripleAtLength T s J mu_).IsAdmissible)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J mu_ $ s.boundary s.length)
    (hm : (ofMarkedSequence σ).IsMarked (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult $ s.boundary s.length)
    (i : ℕ) (hi0_ : s.length ≤ i)
    (hi : i < (s.append (markedBlowupSequenceDataAtEndOfIsMarked s J mu_ σ hm) hinv).length)
    (z : ↥((s.append (markedBlowupSequenceDataAtEndOfIsMarked s J mu_ σ hm) hinv).obj i))
    (hz : z ∈ ((s.append (markedBlowupSequenceDataAtEndOfIsMarked s J mu_ σ hm) hinv).center i).support) :
    ∃ x : ↥(s.obj s.length), x ∈ orderAtLeastLocus J mu_ ∧
      ((s.append (markedBlowupSequenceDataAtEndOfIsMarked s J mu_ σ hm) hinv).proj i).base z = (s.proj s.length).base x := by
  let _c0 := markedBlowupSequenceDataAtEndOfIsMarked s J mu_ σ hm
  have hdl : _c0.length = msLen σ := rfl
  rw [append_length, hdl] at hi
  have hprojd : ∀ j, _c0.proj j = msPrj σ j := by
    intro j
    exact m32 (projectionToBase_eq_toSequenceOfBlowups _c0 j) $ BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups σ.toSequenceOfBlowups j
  rcases Nat.eq_or_lt_of_le hi0_ with heq | hlt
  subst heq
  have hsg0 : 0 < msLen σ := by omega
  have hz1 : z ∈ spI ((s.appendToBlowupSequenceData _c0).center s.length) := hz
  rw [appendToBlowupSequenceData_center_length s _c0] at hz1
  have hz3 := AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 $ AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz1
  let _a0 := bsM (eqToHom $ appendToBlowupSequenceData_schemeAt_of_le_length s _c0 $ le_refl s.length) z
  have hz4 : bsM (σ.toSequenceOfBlowups.isoZero.inv)
      _a0 ∈ orderAtLeastLocus (σ.ideal 0) mu_ :=
    σ.center_order 0 hsg0 hz3
  have hx0 := projectionToBase_mem_orderAtLeastLocus_tripleAtLength hG hinv T s J mu_ hJ σ 0 (zero_le _) _ hz4
  refine ⟨_a0, ?_, ?_⟩
  rw [projectionToBase_zero] at hx0
  have hcan : ∀ u : (lastO s),
      (σ.toSequenceOfBlowups.isoZero.hom).base (bsM (σ.toSequenceOfBlowups.isoZero.inv) u) = u := by
    intro u
    simp
  rwa [hcan] at hx0
  rw [append_projectionToBase,
    appendProjectionToBase_of_le_length s _c0 $ le_refl s.length]
  exact m135 _ _ z
  have hksg : i - s.length < msLen σ := by omega
  have hz1 : z ∈ spI ((s.appendToBlowupSequenceData _c0).center i) := hz
  rw [appendToBlowupSequenceData_center_of_length_lt s _c0 hlt] at hz1
  have hx0 := projectionToBase_mem_orderAtLeastLocus_tripleAtLength hG hinv T s J mu_ hJ σ (i - s.length)
    (le_of_lt hksg) _ $ σ.center_order (i - s.length) hksg $ AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap.1 hz1
  refine ⟨_, hx0, ?_⟩
  rw [append_projectionToBase,
    appendProjectionToBase_of_length_lt s _c0 hlt, hprojd]
  exact rfl

def SequenceOfBlowupsPullback.toMarkedPullbackSquare {T T' : MarkedIdealWithBoundary} (g : scheme T' ⟶ scheme T)
    (s : T.mbs)
    (s' : T'.mbs)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hdim : krullDimSucc (s.obj s.length) ≤ T.krullDimSucc)
    (hval : (MarkedIdealWithBoundary.mk T.base (s.obj s.length) (s.proj s.length ≫ structMap T)
      (s.ideal s.length) T.mult $ s.boundary s.length).IsAdmissible) :
    MarkedPullbackSquare T g where
  baseScheme := s.obj s.length
  topScheme := s'.obj s'.length
  bottom := s.proj s.length
  structMap := s.proj s.length ≫ structMap T
  ideal := s.ideal s.length
  mult := mult T
  boundary := s.boundary s.length
  left := c.lastMap
  top := s'.proj s'.length
  bottom_structMap := rfl
  dim_le := hdim
  isPullback := by
    have h := c.isPullback_lastMap
    rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
  valid := hval

section
variable (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance)
include hG
section
variable (n : ℕ) (A : PrincipalizationAssignment) (T T' : MarkedIdealWithBoundary) (g : scheme T' ⟶ scheme T) (hT : IsAdmissible T) (hT' : IsAdmissible T')
include hT hT'
theorem lastNonMonomialPart_eq_comap_lastMap_of_pullback (_hdim : T.krullDimSucc ≤ n) (_hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (_hideal : T'.ideal = T.ideal.comap g)
    (_hbdry : SameNontrivialBoundary T'.boundary $ T.boundary.map fun D => comap D g)
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : T.mbs)
    (s' : T'.mbs)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = comap (s.ideal s.length) c.lastMap)
    (hsameBoundary : SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => comap D c.lastMap)) :
    lastNonMonomialPart T' s' = comap (lastNonMonomialPart T s) c.lastMap := by
  have hmg := hG.monomialInputs
  have hmain := hbc.nonMonomial (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c (MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s) $ MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT s)
    (s'.boundary s'.length) hsameBoundary.symm $ isAdmissible_mk_congr hlastIdeal hmult $ MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T' hT' s'
  have h0 : lastNonMonomialPart T' s' = nonMonomialPart (s'.boundary s'.length) (s'.ideal s'.length) :=
    rfl
  have h1 : lastNonMonomialPart T s = nonMonomialPart (s.boundary s.length) (s.ideal s.length) := rfl
  rwa [h0, h1, hlastIdeal]

section
variable (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n) (hmult : mult T' = mult T) (hideal : ideal T' = T.ideal.comap g) (hbdry : SameNontrivialBoundary T'.boundary (T.boundary.map fun D => comap D g)) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap) (s : T.mbs) (s' : T'.mbs) (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) (hlastIdeal : s'.ideal s'.length = comap (s.ideal s.length) c.lastMap) (hsameBoundary : SameNontrivialBoundary (s'.boundary s'.length) $ (s.boundary s.length).map fun D => comap D c.lastMap)
include hdim hdim' hmult hideal hbdry hbc hlastIdeal hsameBoundary
theorem companionIdeal_eq_comap_lastMap_of_pullback
    (hinveq : maxOrderNonMonomialOnOrderLocus T' s' = maxOrderNonMonomialOnOrderLocus T s) :
    companionIdeal T' s' = comap (companionIdeal T s) c.lastMap := by
  have hnonMon := lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim'
    hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary
  unfold companionIdeal
  exact pow_sup_pow_eq_comap_pow_sup_pow _ _ _ _ _ T'.mult T.mult (maxOrderNonMonomialOnOrderLocus T' s') (maxOrderNonMonomialOnOrderLocus T s)
    hnonMon hlastIdeal hmult hinveq

theorem orderAtLeastLocus_comap_lastNonMonomialPart_eq_empty_of_lt
    (hlt : maxOrderNonMonomial T' s' < maxOrderNonMonomial T s) :
    orderAtLeastLocus ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) = ∅ := by
  refine eq_empty_of_subset_empty ?_
  intro y hy
  have hy' := (mem_orderAtLeastLocus_iff ((lastNonMonomialPart T s).comap c.lastMap) (maxOrderNonMonomial T s) y).1 hy
  rw [← lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary] at hy'
  refine absurd ?_ $ not_le.mpr hlt
  exact_mod_cast (hy'.trans $ orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT' s' y)

theorem maxOrderNonMonomial_le_of_pullback :
    maxOrderNonMonomial T' s' ≤ maxOrderNonMonomial T s := by
  let _a1 := lastNonMonomialPart T' s'
  have hmain : ∀ y,
      orderAt _a1 y ≤ (maxOrderNonMonomial T s) := by
    intro y
    exact le_of_eq_of_le ((congrArg (orderAt · y) $ lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary).trans $ (hbc.order (lastO s) (s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.length) (s.toMarkedSequenceOfBlowups.projectionToSpec s.length) (lastI s) (lastB s) (hG.monomialInputs.level_valid T hT s.toMarkedSequenceOfBlowups s.length le_rfl) (projectionToSpec_eq s.toMarkedSequenceOfBlowups s.length).symm (lastO s') c.lastMap (s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s'.length) c.isPullback_lastMap) (lastNonMonomialPart T s) y)
      (orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s $ c.lastMap.base y)
  show sSup {m : ℕ | ∃ x, m ≤ orderAt _a1 x}
      ≤ maxOrderNonMonomial T s
  refine csSup_le' ?_
  intro m hm
  obtain ⟨y, hy⟩ := hm
  exact_mod_cast (hy.trans $ hmain y)

theorem nonMonomialOrderReductionContinues_of_pullback
    (hcont : NonMonomialOrderReductionContinues T' s') : NonMonomialOrderReductionContinues T s := by
  unfold NonMonomialOrderReductionContinues at hcont ⊢
  obtain ⟨h1, h2⟩ := hcont
  obtain ⟨x', -⟩ := h2
  rw [hmult] at h1
  refine ⟨le_trans h1 $ maxOrderNonMonomial_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary, ?_⟩
  have hbound :=
    fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  exact orderAtLeastLocus_sSup_nonempty (lastNonMonomialPart T s) (c.lastMap.base x') hbound

theorem maxOrderNonMonomialOnOrderLocus_le_of_pullback :
    maxOrderNonMonomialOnOrderLocus T' s' ≤ maxOrderNonMonomialOnOrderLocus T s := by
  have hmg := hG.monomialInputs
  have hordLast :=
    fun Aid y =>
      MarkedPullbackSquare.orderAt_comap_verticalMap (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c (MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s) $ MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT s) hT
        hbc.order Aid y
  have hmain : maxOrderNonMonomialOnOrderLocus T' s' =
      maxOrderOn (lastNonMonomialPart T' s') (orderAtLeastLocus (lastI s') T'.mult) := rfl
  rw [hmain]
  refine maxOrderOn_le_of_forall _ _ _ ?_
  intro m x' hx' hm
  have hEq2 :=
    (congrArg (orderAt · x') $ lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary).trans $ hordLast (lastNonMonomialPart T s) x'
  have hmult' : (T.mult : ENat) = (T'.mult : ENat) := by rw [hmult]
  exact_mod_cast ((hm.trans_eq hEq2).trans (orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s (c.lastMap.base x') ((mem_orderAtLeastLocus_iff _ _ _).2 (hmult'.trans_le (((mem_orderAtLeastLocus_iff _ _ _).1 hx').trans_eq ((congrArg (orderAt · x') hlastIdeal).trans $ hordLast (lastI s) x'))))))

theorem companionIdealReductionContinues_of_pullback
    (hcont : CompanionIdealReductionContinues T' s') : CompanionIdealReductionContinues T s := by
  have hle :=
    maxOrderNonMonomialOnOrderLocus_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc
      s s' c hlastIdeal hsameBoundary
  unfold CompanionIdealReductionContinues at hcont ⊢
  omega
end
end

theorem append_proj_center_ne_base_of_orderAtLeastLocus_empty
    (T T' : MarkedIdealWithBoundary) (g : T'.scheme ⟶ T.scheme) (hT : T.IsAdmissible)
    (n : ℕ) (A : PrincipalizationAssignment)
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : T.mbs)
    (s' : T'.mbs)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (J : (s.obj s.length).IdealSheafData) (mu_ : ℕ) (hJ : (tripleAtLength T s J mu_).IsAdmissible)
    (hempty : orderAtLeastLocus (J.comap c.lastMap) mu_ = ∅)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) J mu_ $ s.boundary s.length)
    (hm : (ofMarkedSequence σ).IsMarked (s.proj s.length ≫ T.structMap)
      (s.ideal s.length) T.mult $ s.boundary s.length)
    (D : T.mbs)
    (hD : D = s.append (markedBlowupSequenceDataAtEndOfIsMarked s J mu_ σ hm) hinv)
    (i : ℕ) (hi0_ : s.length ≤ i) (hi : i < D.length)
    (z : ↥(D.obj i)) (hz : z ∈ (D.center i).support) (y : ↥T'.scheme) :
    g.base y ≠ ((D.proj i).base z) := by
  subst hD
  obtain ⟨x, hx, hproj⟩ :=
    exists_mem_orderAtLeastLocus_of_mem_center_append hG hinv T s J mu_ hJ σ hm i hi0_ hi z hz
  intro hcon
  rw [hproj] at hcon
  have hsq : IsPullback c.lastMap (lastP s') (lastP s) g := by
    have h := c.isPullback_lastMap
    rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback hsq x y hcon.symm
  have hord : orderAt (cmI J c.lastMap) w = orderAt J (c.lastMap.base w) :=
    MarkedPullbackSquare.orderAt_comap_verticalMap (SequenceOfBlowupsPullback.toMarkedPullbackSquare g s s' c (MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hG.monomialInputs T hT s) $ MonomialGeometryHypotheses.isAdmissible_tripleAtLength hG.monomialInputs T hT s) hT
      hbc.order J w
  have hmem : w ∈ orderAtLeastLocus (cmI J c.lastMap) mu_ := by
    rw [mem_orderAtLeastLocus_iff, hord, hw]
    exact (mem_orderAtLeastLocus_iff J mu_ x).1 hx
  rw [hempty] at hmem
  simp only [mem_empty_iff_false] at hmem

section
variable (n : ℕ) (A B : PrincipalizationAssignment)
theorem appendRecursive_proj_center_ne_of_orderAtLeastLocus_empty (_hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (_hT' : T'.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hdim' : T'.krullDimSucc ≤ n)
    (_hmult : T'.mult = T.mult) (_hideal : T'.ideal = T.ideal.comap g)
    (_hbdry : SameNontrivialBoundary T'.boundary (T.boundary.map fun D => D.comap g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : T.mbs)
    (s' : T'.mbs)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (_htopIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (_hsameBoundary : SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (J : IdealSheafData (s.obj s.length)) mu_
    (hJ : (tripleAtLength T s J mu_).IsAdmissible)
    (hempty : orderAtLeastLocus (J.comap c.lastMap) mu_ = ∅)
    i (hi0_ : s.length ≤ i) (hi : i < (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J mu_).length)
    z
    (hz : z ∈ ((appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J mu_).center i).support) y :
    g.base y ≠ ((appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J mu_).proj i).base z := by
  let _a0 := principalizationOfDimLe T A
  let _a1 := tripleAtLength T s J mu_
  classical
  by_cases hd : tDim _a1 ≤ tDim T
  by_cases hm : (ofMarkedSequence (principalizationSeqAtEnd T _a0 s J mu_ hd)).IsMarked
      (lastP s ≫ tMp T) (lastI s) T.mult (lastB s)
  exact append_proj_center_ne_base_of_orderAtLeastLocus_empty hG hinv T T' g hT n A hbc s s' c J mu_ hJ hempty
    (principalizationSeqAtEnd T _a0 s J mu_ hd) hm (appendRecursivePrincipalization hinv T _a0 s J mu_)
    (appendRecursivePrincipalization_eq_append hinv T _a0 s J mu_ hd hm) i hi0_ hi z hz y
  exfalso
  have hrs : markedDataOfSeq s J mu_ (principalizationOfDimLe T A _a1 hd) = none := by
    unfold markedDataOfSeq
    exact dif_neg hm
  have he :=
    appendRecursivePrincipalization_eq_self_of_eq_none hinv T _a0 s J mu_ hd hrs
  rw [he] at hi
  omega
  exfalso
  have he : appendRecursivePrincipalization hinv T _a0 s J mu_ = s := by
    unfold appendRecursivePrincipalization
    exact dif_neg hd
  rw [he] at hi
  omega

theorem nonempty_sequenceOfBlowupsPullback_of_orderAtLeastLocus_empty (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : T'.mult = T.mult) (hideal : T'.ideal = T.ideal.comap g)
    (hbdry : SameNontrivialBoundary T'.boundary $ T.boundary.map fun D => D.comap g)
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : T.mbs)
    (s' : T'.mbs)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = (s.ideal s.length).comap c.lastMap)
    (hsameBoundary : SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => D.comap c.lastMap))
    (J : (s.obj s.length).IdealSheafData) (mu_ : ℕ)
    (hJ : (tripleAtLength T s J mu_).IsAdmissible)
    (hempty : orderAtLeastLocus (J.comap c.lastMap) mu_ = ∅) :
    Nonempty $ SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J mu_).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  rcases appendRecursivePrincipalization_eq_self_or_append hinv T (principalizationOfDimLe T A) s J mu_ with heq | ⟨t, heq⟩
  rw [heq]
  exact ⟨c⟩
  have hmiss := appendRecursive_proj_center_ne_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT' hdim
    hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary J mu_ hJ hempty
  let _s0 := s.append t hinv
  have hconcat : _s0.toBlowupSequenceData
      = s.toBlowupSequenceData.append t.toBlowupSequenceData := by
    rw [append_toBlowupSequenceData]
    rfl
  have hseq : _s0.toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (s.toBlowupSequenceData.append t.toBlowupSequenceData).toSequenceOfBlowups :=
    congrArg (fun D : BlowupSequenceData T.scheme => D.toSequenceOfBlowups) hconcat
  have h0 := hmiss
  rw [heq] at h0
  have h0' : ∀ i, s.length ≤ i → i < s.length + t.length →
      ∀ z : (_s0.obj i), z ∈ spI (_s0.center i) →
        ∀ y, bsM g y ≠ bsM (_s0.proj i) z := by
    intro i hi0 hi
    refine h0 i hi0 ?_
    rwa [append_length]
  have hproj : ∀ i,
      _s0.toBlowupSequenceData.projectionToBase i = _s0.proj i := by
    intro i
    rw [projectionToBase_eq_toSequenceOfBlowups]
    exact sy_ $ toSequenceOfBlowups_projectionToBase _s0.toBlowupSequenceData i
  have key : ∀ i, mbsLen s ≤ i →
      i < mbsLen s + mbsLen t →
      ∀ z : ((s.toBlowupSequenceData.append t.toBlowupSequenceData).obj i),
        z ∈ spI ((s.toBlowupSequenceData.append t.toBlowupSequenceData).center i) →
        ∀ y,
          g.base y ≠ bsM ((s.toBlowupSequenceData.append t.toBlowupSequenceData).projectionToBase i) z := by
    rw [← hconcat]
    intro i hi0 hi z hz y
    rw [hproj i]
    exact h0' i hi0 hi z hz y
  rw [heq, hseq]
  exact SequenceOfBlowupsPullback.nonempty_append_of_disjoint_centers g s'.toBlowupSequenceData s.toBlowupSequenceData
    t.toBlowupSequenceData c key
end
end

def markedPullbackSquareAtLength (T T' : MarkedIdealWithBoundary) (g : scheme T' ⟶ scheme T)
    (s : T.mbs)
    (s' : T'.mbs)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (J : IdealSheafData $ s.obj s.length) (mu_ : ℕ)
    (hdim : krullDimSucc (s.obj s.length) ≤ T.krullDimSucc)
    (hJ : IsAdmissible $ tripleAtLength T s J mu_) :
    MarkedPullbackSquare T g where
  baseScheme := s.obj s.length
  topScheme := s'.obj s'.length
  bottom := s.proj s.length
  structMap := s.proj s.length ≫ structMap T
  ideal := J
  mult := mu_
  boundary := s.boundary s.length
  left := c.lastMap
  top := s'.proj s'.length
  bottom_structMap := rfl
  dim_le := hdim
  isPullback := by
    have h := c.isPullback_lastMap
    rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
  valid := hJ

theorem nonempty_sequenceOfBlowupsPullback_of_markedDataOfSeq {k1_ k2_ : Type} [Field k1_] [Field k2_]
    {X Y : Sch} {p : X ⟶ Spec (CommRingCat.of k1_)} {q : Y ⟶ Spec (CommRingCat.of k2_)}
    {I : ISD X} {m : ℕ} {E : Bdy X}
    {I' : ISD Y} {m' : ℕ} {E' : Bdy Y}
    (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m' E')
    (J : IdealSheafData $ s.obj s.length) (mu_ : ℕ)
    (K : IdealSheafData $ s'.obj s'.length) (nu_ : ℕ)
    (f : s'.obj s'.length ⟶ s.obj s.length)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J mu_ $ s.boundary s.length)
    (σ' : MarkedSequenceOfBlowups (s'.proj s'.length ≫ q) K nu_ $ s'.boundary s'.length)
    (d : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length)
    (d' : MarkedBlowupSequenceData (s'.proj s'.length ≫ q) (s'.ideal s'.length) m' $ s'.boundary s'.length)
    (hrem : markedDataOfSeq s J mu_ σ = some d) (hrem' : markedDataOfSeq s' K nu_ σ' = some d')
    (cc : SequenceOfBlowupsPullback f σ'.toSequenceOfBlowups σ.toSequenceOfBlowups) :
    Nonempty $ SequenceOfBlowupsPullback f d'.toSequenceOfBlowups d.toSequenceOfBlowups := by
  let _a0 := lastP s ≫ p
  let _a1 := lastP s' ≫ q
  classical
  by_cases hm : (ofMarkedSequence σ).IsMarked _a0
      (lastI s) m $ lastB s
  by_cases hm' : (ofMarkedSequence σ').IsMarked _a1
      (lastI s') m' $ lastB s'
  have he : markedDataOfSeq s J mu_ σ = some ((ofMarkedSequence σ).toMarkedBlowupSequenceData
      _a0 (lastI s) m (lastB s) hm) := by
    unfold markedDataOfSeq
    exact dif_pos hm
  have he' : markedDataOfSeq s' K nu_ σ' = some ((ofMarkedSequence σ').toMarkedBlowupSequenceData
      _a1 (lastI s') m' (lastB s') hm') := by
    unfold markedDataOfSeq
    exact dif_pos hm'
  have hdd := m105 $ st_ hrem he
  have hdd' := m105 $ st_ hrem' he'
  subst hdd
  subst hdd'
  exact ⟨SequenceOfBlowupsPullback.toBlowupDataOfSeq cc⟩
  have hnone : markedDataOfSeq s' K nu_ σ' = none := by
    unfold markedDataOfSeq
    exact dif_neg hm'
  exact absurd (st_ hrem' hnone) $ some_ne_none d'
  have hnone : markedDataOfSeq s J mu_ σ = none := by
    unfold markedDataOfSeq
    exact dif_neg hm
  exact absurd (st_ hrem hnone) $ some_ne_none d

section
variable (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance) (n : ℕ) (A B : PrincipalizationAssignment)
include hG
theorem nonempty_sequenceOfBlowupsPullback_appendRecursive (_hspec : IsOrderReduction (fun d => d ≤ n) A B)
    (T T' : MarkedIdealWithBoundary) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hT' : T'.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (_hmult : T'.mult = T.mult) (_hideal : T'.ideal = T.ideal.comap g)
    (_hbdry : SameNontrivialBoundary T'.boundary (T.boundary.map fun D => comap D g))
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : T.mbs)
    (s' : T'.mbs)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (_htopIdeal : s'.ideal s'.length = comap (s.ideal s.length) c.lastMap)
    (hsameBoundary : SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => comap D c.lastMap))
    (J : IdealSheafData (s.obj s.length)) (mu_ : ℕ)
    (hJ : (tripleAtLength T s J mu_).IsAdmissible)
    (hJ' : (tripleAtLength T' s' (comap J c.lastMap) mu_).IsAdmissible)
    (hord : ∀ x : ↥(s.obj s.length), orderAt J x ≤ (mu_ : ENat))
    (hmark : ∀ (h : (tripleAtLength T s J mu_).krullDimSucc ≤ T.krullDimSucc)
      (h' : (tripleAtLength T' s' (comap J c.lastMap) mu_).krullDimSucc ≤ T'.krullDimSucc),
      markedDataOfSeq s J mu_ (principalizationOfDimLe T A (tripleAtLength T s J mu_) h) = none ↔
        markedDataOfSeq s' (comap J c.lastMap) mu_
          (principalizationOfDimLe T' A (tripleAtLength T' s' (comap J c.lastMap) mu_) h') = none) :
    Nonempty (SequenceOfBlowupsPullback g
      (appendRecursivePrincipalization hinv T' (principalizationOfDimLe T' A) s' (comap J c.lastMap) mu_).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendRecursivePrincipalization hinv T (principalizationOfDimLe T A) s J mu_).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  let _a2 := principalizationOfDimLe T A
  let _a3 := principalizationOfDimLe T' A
  let _a0 := tripleAtLength T' s' (cmI J c.lastMap) mu_
  let _a1 := tripleAtLength T s J mu_
  classical
  have hmg := hG.monomialInputs
  have hdimS :=
    MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT s
  have hdimS'T :=
    MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T' hT' s'
  have hd := hdimS
  have hd' := hdimS'T
  have hiff := hmark hd hd'
  cases hq : markedDataOfSeq s J mu_ (principalizationOfDimLe T A _a1 hd) with
  | none =>
      rw [appendRecursivePrincipalization_eq_self_of_eq_none hinv T _a2 s J mu_ hd hq,
        appendRecursivePrincipalization_eq_self_of_eq_none hinv T' _a3 s' (cmI J c.lastMap) mu_ hd' (mp_ hiff hq)]
      exact ⟨c⟩
  | some d =>
      cases hq' : markedDataOfSeq s' (cmI J c.lastMap) mu_
          (principalizationOfDimLe T' A _a0 hd') with
      | none => exact absurd (st_ hq (mpr_ hiff hq')) (some_ne_none d)
      | some d' =>
          obtain ⟨cc⟩ := (hbc.rule (markedPullbackSquareAtLength T T' g s s' c J mu_ hdimS hJ) hord (lastB s') hsameBoundary.symm hJ' (le_trans hdimS'T hdim')).nonempty_sequenceOfBlowupsPullback
          obtain ⟨e⟩ := nonempty_sequenceOfBlowupsPullback_of_markedDataOfSeq s s' J mu_ (cmI J c.lastMap) mu_
            c.lastMap (principalizationOfDimLe T A _a1 hd)
            (principalizationOfDimLe T' A _a0 hd') d d' hq hq' cc
          rw [appendRecursivePrincipalization_eq_append_of_eq_some hinv T _a2 s J mu_ hd d hq,
            appendRecursivePrincipalization_eq_append_of_eq_some hinv T' _a3 s' (cmI J c.lastMap) mu_
              hd' d' hq']
          exact (isPullbackBlowupSequence_append_of_two_fields g s d s' d' hinv c e).nonempty_sequenceOfBlowupsPullback

section
variable (hspec : IsOrderReduction (fun d => d ≤ n) A B) (T T' : MarkedIdealWithBoundary) (g) (hT : IsAdmissible T) (hT' : IsAdmissible T') (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n) (hmult : mult T' = mult T) (hideal : ideal T' = T.ideal.comap g) (hbdry : SameNontrivialBoundary T'.boundary $ T.boundary.map fun D => comap D g) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap) (s : T.mbs) (s' : T'.mbs) (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) (hlastIdeal : s'.ideal s'.length = comap (s.ideal s.length) c.lastMap) (hsameBoundary : SameNontrivialBoundary (s'.boundary s'.length) $ (s.boundary s.length).map fun D => comap D c.lastMap)
include hspec hT hT' hdim hdim' hmult hideal hbdry hbc hlastIdeal hsameBoundary
theorem nonempty_sequenceOfBlowupsPullback_extendByNonMonomialPart
    (hcont : NonMonomialOrderReductionContinues T s) (hcont' : NonMonomialOrderReductionContinues T' s')
    (hinveq : maxOrderNonMonomial T' s' = maxOrderNonMonomial T s)
    (hmark : ∀ (h : (tripleAtLength T s (lastNonMonomialPart T s) $ maxOrderNonMonomial T s).krullDimSucc ≤ T.krullDimSucc)
      (h' : (tripleAtLength T' s' (comap (lastNonMonomialPart T s) c.lastMap)
        (maxOrderNonMonomial T s)).krullDimSucc ≤ T'.krullDimSucc),
      markedDataOfSeq s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (principalizationOfDimLe T A (tripleAtLength T s (lastNonMonomialPart T s) $ maxOrderNonMonomial T s) h) = none ↔
        markedDataOfSeq s' (comap (lastNonMonomialPart T s) c.lastMap) (maxOrderNonMonomial T s)
          (principalizationOfDimLe T' A
            (tripleAtLength T' s' (comap (lastNonMonomialPart T s) c.lastMap) $ maxOrderNonMonomial T s) h')
          = none) :
    Nonempty $ SequenceOfBlowupsPullback g
      (extendByNonMonomialPart hinv T' (principalizationOfDimLe T' A) s').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hnonMon :=
    lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary
  have hJ' : tAd $ tripleAtLength T' s' (lastNonMonomialPart T' s') $ maxOrderNonMonomial T' s' :=
    isAdmissible_nonMonomialTriple hG hT' s' hcont'
  rw [hnonMon, hinveq] at hJ'
  have hord :=
    fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  let _a2 := lastNonMonomialPart T s
  let _a3 := maxOrderNonMonomial T s
  have key := nonempty_sequenceOfBlowupsPullback_appendRecursive hG hinv n A B hspec T T' g hT hT' hdim hdim'
    hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary _a2 _a3
    (isAdmissible_nonMonomialTriple hG hT s hcont) hJ' hord hmark
  let _a4 := principalizationOfDimLe T A
  have hL : extendByNonMonomialPart hinv T _a4 s
      = appendRecursivePrincipalization hinv T _a4 s _a2 _a3 := rfl
  let _a5 := principalizationOfDimLe T' A
  have hU : extendByNonMonomialPart hinv T' _a5 s'
      = appendRecursivePrincipalization hinv T' _a5 s' (lastNonMonomialPart T' s') (maxOrderNonMonomial T' s') := rfl
  rw [hnonMon, hinveq] at hU
  rwa [hL, hU]

theorem nonempty_sequenceOfBlowupsPullback_extendByCompanionIdeal
    (hcont : CompanionIdealReductionContinues T s) (hcont' : CompanionIdealReductionContinues T' s')
    (hinveq : maxOrderNonMonomialOnOrderLocus T' s' = maxOrderNonMonomialOnOrderLocus T s)
    (hmark : ∀ (h : (tripleAtLength T s (companionIdeal T s)
        (mult T * maxOrderNonMonomialOnOrderLocus T s)).krullDimSucc ≤ T.krullDimSucc)
      (h' : (tripleAtLength T' s' ((companionIdeal T s).comap c.lastMap)
        (mult T * maxOrderNonMonomialOnOrderLocus T s)).krullDimSucc ≤ T'.krullDimSucc),
      markedDataOfSeq s (companionIdeal T s) (mult T * maxOrderNonMonomialOnOrderLocus T s)
          (principalizationOfDimLe T A
            (tripleAtLength T s (companionIdeal T s) (mult T * maxOrderNonMonomialOnOrderLocus T s)) h) = none ↔
        markedDataOfSeq s' ((companionIdeal T s).comap c.lastMap) (mult T * maxOrderNonMonomialOnOrderLocus T s)
          (principalizationOfDimLe T' A
            (tripleAtLength T' s' ((companionIdeal T s).comap c.lastMap)
              (mult T * maxOrderNonMonomialOnOrderLocus T s)) h') = none) :
    Nonempty (SequenceOfBlowupsPullback g
      (extendByCompanionIdeal hinv T' (principalizationOfDimLe T' A) s').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  have hJideal :=
    companionIdeal_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
      hbdry hbc s s' c hlastIdeal hsameBoundary hinveq
  have hmu : tMu T' * maxOrderNonMonomialOnOrderLocus T' s' = tMu T * maxOrderNonMonomialOnOrderLocus T s := by simp_all
  let _a0 := cmI (companionIdeal T s) c.lastMap
  let _a1 := companionIdeal T' s'
  let _a5 := principalizationOfDimLe T A
  have hA : extendByCompanionIdeal hinv T _a5 s
      = appendRecursivePrincipalization hinv T _a5 s (companionIdeal T s) (tMu T * maxOrderNonMonomialOnOrderLocus T s) := rfl
  let _a2 := principalizationOfDimLe T' A
  have hB0 : extendByCompanionIdeal hinv T' _a2 s'
      = appendRecursivePrincipalization hinv T' _a2 s' _a1
        (tMu T' * maxOrderNonMonomialOnOrderLocus T' s') := rfl
  rw [hA, hB0.trans (appendRecursivePrincipalization_congr hinv T' _a2 s' _a1 _a0 (tMu T' * maxOrderNonMonomialOnOrderLocus T' s') (tMu T * maxOrderNonMonomialOnOrderLocus T s) hJideal hmu)]
  exact nonempty_sequenceOfBlowupsPullback_appendRecursive hG hinv n A B hspec T T' g hT hT' hdim hdim' hmult
    hideal hbdry hbc s s' c hlastIdeal hsameBoundary (companionIdeal T s) (tMu T * maxOrderNonMonomialOnOrderLocus T s)
    (companionTriple_isAdmissible hG hT s hcont) (isAdmissible_tripleAtLength_congr T' s' _a1 _a0 (tMu T' * maxOrderNonMonomialOnOrderLocus T' s') (tMu T * maxOrderNonMonomialOnOrderLocus T s) hJideal hmu (companionTriple_isAdmissible hG hT' s' hcont')) (orderAt_companionIdeal_le hG hT s hcont) hmark
end
end

theorem natCast_le_of_natCast_mul_le_mul m p (hp : 1 ≤ p) a
    (h : ((m * p : ℕ) : ENat) ≤ ((p : ℕ) : ENat) * a) : ((m : ℕ) : ENat) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  exact le_top
  obtain ⟨a0_, rfl⟩ := mp_ ne_top_iff_exists ha
  have h' : m * p ≤ p * a0_ := by exact_mod_cast h
  have h'' := h'
  rw [← Nat.mul_comm p m] at h''
  exact_mod_cast (Nat.le_of_mul_le_mul_left h'' (by omega))

theorem orderAtLeastLocus_comap_companionIdeal_eq_empty_of_lt (hG : PrincipalizationGeometryHypotheses)
    (hinv : ComapIsoInvariance) (n : ℕ) (A : PrincipalizationAssignment)
    (T T' : MarkedIdealWithBoundary) (g : scheme T' ⟶ scheme T)
    (hT : IsAdmissible T) (hT' : IsAdmissible T') (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n)
    (hmult : mult T' = mult T) (hideal : ideal T' = T.ideal.comap g)
    (hbdry : SameNontrivialBoundary T'.boundary $ T.boundary.map fun D => comap D g)
    (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (s : T.mbs)
    (s' : T'.mbs)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hlastIdeal : s'.ideal s'.length = comap (s.ideal s.length) c.lastMap)
    (hsameBoundary : SameNontrivialBoundary (s'.boundary s'.length)
      ((s.boundary s.length).map fun D => comap D c.lastMap))
    (hlt : maxOrderNonMonomialOnOrderLocus T' s' < maxOrderNonMonomialOnOrderLocus T s) :
    orderAtLeastLocus (comap (companionIdeal T s) c.lastMap) (mult T * maxOrderNonMonomialOnOrderLocus T s) = ∅ := by
  have hvalS' := MonomialGeometryHypotheses.isAdmissible_tripleAtLength (hG.monomialInputs) T' hT' s'
  have hchar := hvalS'.charZero
  have hsmooth := hvalS'.smooth
  have hp1 : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := by omega
  have hcompanion : comap (companionIdeal T s) c.lastMap
      = lastNonMonomialPart T' s' ^ T.mult ⊔ s'.ideal s'.length ^ maxOrderNonMonomialOnOrderLocus T s := by
    unfold companionIdeal
    rw [lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary, hlastIdeal]
    exact comap_pow_sup_pow c.lastMap (lastNonMonomialPart T s) (s.ideal s.length) T.mult
      (maxOrderNonMonomialOnOrderLocus T s)
  rw [hcompanion]
  refine eq_empty_of_subset_empty ?_
  intro x hx
  exfalso
  have hmin := le_trans ((mem_orderAtLeastLocus_iff _ _ _).1 hx) $ le_of_eq $ orderAt_sup _ _ x
  let _a0 := lastP s' ≫ tMp T'
  have hmultE : (mult T' : ENat) = (mult T : ENat) := by rw [hmult]
  have hxN3 := le_trans (le_trans hmin $ min_le_left _ _) $ le_of_eq $ orderAt_pow T'.base _a0 (lastNonMonomialPart T' s') T.mult x
  rw [← Nat.mul_comm (maxOrderNonMonomialOnOrderLocus T s) T.mult] at hxN3
  have hfin := le_trans (natCast_le_of_natCast_mul_le_mul (maxOrderNonMonomialOnOrderLocus T s) T.mult (hT.one_le_mult) (orderAt (lastNonMonomialPart T' s') x) hxN3) $ orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT' s' x $ (mem_orderAtLeastLocus_iff _ _ _).2 $ hmultE.trans_le $ natCast_le_of_natCast_mul_le_mul T.mult (maxOrderNonMonomialOnOrderLocus T s) hp1 (orderAt (s'.ideal s'.length) x) $ le_trans (le_trans hmin $ min_le_right _ _) $ le_of_eq $ orderAt_pow T'.base _a0 (lastI s') (maxOrderNonMonomialOnOrderLocus T s) x
  have hnat : maxOrderNonMonomialOnOrderLocus T s ≤ maxOrderNonMonomialOnOrderLocus T' s' := by exact_mod_cast hfin
  omega





theorem isNoetherian_schemeAt_of_isAdmissible (T : MarkedIdealWithBoundary) (hT : IsAdmissible T)
    (u : T.mbs) (i : ℕ) (hi : i ≤ u.length) :
    IsNoetherian $ u.obj i := by
  have h := p25 effectiveCartierSupportContainsNoComponent hT u.toMarkedSequenceOfBlowups i $ hi.trans_eq (toMarkedSequence_length u).symm
  rwa [toMarkedSequence_schemeAt] at h

theorem isLocallyMonomialTriple_tripleAtLength_congr (T : MarkedIdealWithBoundary)
    (s : T.mbs)
    J K mu_ nu_ (hJK : J = K) (hmunu : mu_ = nu_)
    (h : IsLocallyMonomialTriple $ tripleAtLength T s J mu_) :
    IsLocallyMonomialTriple $ tripleAtLength T s K nu_ :=by simp_all
private theorem projectionToBase_mem_orderAtLeastLocus (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance)
    (T : MarkedIdealWithBoundary) (hT : T.IsAdmissible) (σ : T.SequenceOfBlowups)
    (j : ℕ) (hj : j ≤ σ.toSequenceOfBlowups.length) (z : ↥(σ.toSequenceOfBlowups.schemeAt j))
    (hz : z ∈ orderAtLeastLocus (σ.ideal j) T.mult) :
    (σ.toSequenceOfBlowups.projectionToBase j).base z ∈ orderAtLeastLocus T.ideal T.mult := by
  have hval : ∀ l ≤ msLen σ, tAd $ T.transformAt σ l := by
    intro l hl
    exact hG.monomialInputs.level_valid T hT σ l hl
  have hsub := orderAtLeastLocus_subset_preimage_transitionMap
    (orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs)
    T σ hval T.mult le_rfl 0 j (zero_le j) hj
  have h0 := hsub hz
  rw [σ.ideal_zero, hinv.coSupport_comap σ.toSequenceOfBlowups.isoZero T.ideal T.mult] at h0
  have hcomp : bsM (σ.toSequenceOfBlowups.projectionToBase j) z
      = bsM (σ.toSequenceOfBlowups.isoZero.hom) (bsM (σ.toSequenceOfBlowups.transitionMap $ zero_le j) z) := by
    rw [projectionToBase_def]
    simp
  rwa [hcomp]

section
variable (hinv : ComapIsoInvariance)
theorem length_nonMonomialOrderReductionIter_zero (T : MarkedIdealWithBoundary)
    (rc : (S : MarkedIdealWithBoundary) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    (nonMonomialOrderReductionIter hinv T rc 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = 0 := by
  refine tr_ (toMarkedSequence_length $ nonMonomialOrderReductionIter hinv T rc 0) ?_
  rw [nonMonomialOrderReductionIter_zero, emptyMarkedBlowupSequenceData_length]

theorem isPullbackBlowupSequence_monomialPrincipalization_congr
    (T T' : MarkedIdealWithBoundary)
    (S : T.mbs)
    (S' : T'.mbs)
    f
    J mu_
    K1 K2 nu1 nu2
    (hK : K1 = K2) (hnu_ : nu1 = nu2)
    (h : IsPullbackBlowupSequence f (monomialPrincipalization hinv $ tripleAtLength T' S' K1 nu1).toSequenceOfBlowups
      (monomialPrincipalization hinv $ tripleAtLength T S J mu_).toSequenceOfBlowups) :
    IsPullbackBlowupSequence f (monomialPrincipalization hinv $ tripleAtLength T' S' K2 nu2).toSequenceOfBlowups
      (monomialPrincipalization hinv $ tripleAtLength T S J mu_).toSequenceOfBlowups := by
  subst hK
  subst hnu_
  exact h

theorem isPullbackSequenceOfBlowups_monomial_of_pullback
    (hmg : MonomialGeometryHypotheses)
    (n : ℕ) (A : PrincipalizationAssignment) (T T' : MarkedIdealWithBoundary) (g : T'.scheme ⟶ T.scheme)
    (hT : T.IsAdmissible) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
    (S : T.mbs)
    (S' : T'.mbs)
    (c : SequenceOfBlowupsPullback g S'.toMarkedSequenceOfBlowups.toSequenceOfBlowups S.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hmult : T'.mult = T.mult)
    (hidealLastComap : S'.ideal S'.length = comap (S.ideal S.length) c.lastMap)
    (hlastBoundary : SameNontrivialBoundary (S'.boundary S'.length)
      ((S.boundary S.length).map fun D => comap D c.lastMap))
    (hmonLow : IsLocallyMonomialTriple $ tripleAtLength T S (S.ideal S.length) T.mult)
    (hmonUp : IsLocallyMonomialTriple
      (tripleAtLength T' S' (S'.ideal S'.length) T'.mult)) :
    IsPullbackBlowupSequence c.lastMap
      (monomialPrincipalization hinv $ tripleAtLength T' S' (S'.ideal S'.length) T'.mult).toSequenceOfBlowups
      (monomialPrincipalization hinv $ tripleAtLength T S (S.ideal S.length) T.mult).toSequenceOfBlowups := by
  let _a0 := cmI (lastI S) c.lastMap
  have hmain := hbc.monomialBody (SequenceOfBlowupsPullback.toMarkedPullbackSquare g S S' c (MonomialGeometryHypotheses.krullDimSucc_schemeAt_length_le_dim hmg T hT S) $ MonomialGeometryHypotheses.isAdmissible_tripleAtLength hmg T hT S) hmonLow
    (S'.boundary S'.length) hlastBoundary.symm $ isLocallyMonomialTriple_tripleAtLength_congr T' S' (lastI S') _a0 T'.mult T.mult hidealLastComap hmult hmonUp
  exact isPullbackBlowupSequence_monomialPrincipalization_congr hinv T T' S S' c.lastMap (S.ideal S.length)
    T.mult _a0 (S'.ideal S'.length) T.mult T'.mult hidealLastComap.symm
    hmult.symm hmain
end

section
variable {X Y} (g) (hflat : Flat g) (sD : SequenceOfBlowups X) (sU : SequenceOfBlowups Y)
include hflat
theorem nonempty_sequenceOfBlowupsPullback_of_length_eq_zero
    (hD : sD.length = 0) (hU : sU.length = 0) :
    Nonempty $ SequenceOfBlowupsPullback g sU sD := by
  refine ⟨SequenceOfBlowupsPullback.ofBlowupDataOfSeq $ SequenceOfBlowupsPullback.ofCentersMissImage g (ofSequenceOfBlowups sD) ?_
    (ofSequenceOfBlowups sU) ?_⟩
  simp_all
  simp_all

end

theorem lastIdeal_and_boundary_comap_of_flat {k k' : Type} [Field k] [Field k'] {X Y : Sch}
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k'} {g : Y ⟶ X}
    {I : ISD X} {I' : ISD Y} {m m' : ℕ}
    {E : Bdy X} {E' : Bdy Y}
    (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m' E') (hm : m' = m)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hflat : Flat g)
    (hI : I' = I.comap g)
    (hE : SameNontrivialBoundary E' $ E.map fun D => D.comap g)
    (hN : ∀ i : ℕ, i ≤ s.length → IsNoetherian (s.obj i))
    (hN' : ∀ j : ℕ, j ≤ s'.length → IsNoetherian (s'.obj j)) :
    s'.ideal s'.length = (s.ideal s.length).comap c.lastMap ∧
      SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun D => D.comap c.lastMap) := by
  subst hm
  exact SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' c hI hE hN hN'

theorem lastIdeal_and_boundary_comap_of_isAdmissible (T T' : MarkedIdealWithBoundary) (g : scheme T' ⟶ scheme T)
    (hT : IsAdmissible T) (hT' : IsAdmissible T') (hflat : Flat g)
    (hmult : mult T' = mult T) (hideal : ideal T' = T.ideal.comap g)
    (hbdry : SameNontrivialBoundary T'.boundary $ T.boundary.map fun D => D.comap g)
    (s : T.mbs)
    (s' : T'.mbs)
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    s'.ideal s'.length = (s.ideal s.length).comap c.lastMap ∧
      SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun D => D.comap c.lastMap) :=
  lastIdeal_and_boundary_comap_of_flat s s' hmult c hflat hideal hbdry
    (isNoetherian_schemeAt_of_isAdmissible T hT s) $ isNoetherian_schemeAt_of_isAdmissible T' hT' s'

theorem exists_sequenceOfBlowupsPullback_congr {T T' : MarkedIdealWithBoundary} (g : T'.scheme ⟶ T.scheme)
    (S1_ S2_ : T'.mbs)
    (R1_ R2_ : T.mbs)
    (hS : S1_ = S2_) (hR : R1_ = R2_)
    (hex : ∃ c : SequenceOfBlowupsPullback g S1_.toMarkedSequenceOfBlowups.toSequenceOfBlowups R1_.toMarkedSequenceOfBlowups.toSequenceOfBlowups,
      S1_.ideal S1_.length = comap (R1_.ideal R1_.length) c.lastMap ∧
      SameNontrivialBoundary (S1_.boundary S1_.length)
        ((R1_.boundary R1_.length).map fun D => comap D c.lastMap)) :
    ∃ c : SequenceOfBlowupsPullback g S2_.toMarkedSequenceOfBlowups.toSequenceOfBlowups R2_.toMarkedSequenceOfBlowups.toSequenceOfBlowups,
      S2_.ideal S2_.length = comap (R2_.ideal R2_.length) c.lastMap ∧
      SameNontrivialBoundary (S2_.boundary S2_.length)
        ((R2_.boundary R2_.length).map fun D => comap D c.lastMap) := by
  subst hS
  subst hR
  exact hex

theorem markedDataOfSeq_ne_none_of_isMarked {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedBlowupSequenceData p I m E) (J : IdealSheafData $ s.obj s.length) (mu_ : ℕ)
    (σ : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J mu_ $ s.boundary s.length)
    (hm : (ofMarkedSequence σ).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m
      (s.boundary s.length)) :
    markedDataOfSeq s J mu_ σ ≠ none := by
  have he : markedDataOfSeq s J mu_ σ = some ((ofMarkedSequence σ).toMarkedBlowupSequenceData
      (lastP s ≫ p) (lastI s) m (lastB s) hm) := by
    unfold markedDataOfSeq
    exact dif_pos hm
  rw [he]
  exact some_ne_none _

section
variable (hG : PrincipalizationGeometryHypotheses)
include hG
section
variable (hinv : ComapIsoInvariance) (n) (A B) (hspec : IsOrderReduction (fun d => d ≤ n) A B) (T T' : MarkedIdealWithBoundary) (g) (hT : IsAdmissible T) (hT' : IsAdmissible T') (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n) (hmult : mult T' = mult T) (hideal : ideal T' = T.ideal.comap g) (hbdry : SameNontrivialBoundary T'.boundary $ T.boundary.map fun D => comap D g) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
include hspec hT hT' hdim hdim' hmult hideal hbdry hbc
theorem nonMonomialOrderReductionIter_exists_sequenceOfBlowupsPullback (f : ℕ) :
    ∃ (f' : ℕ) (c : SequenceOfBlowupsPullback g
        (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).toMarkedSequenceOfBlowups.toSequenceOfBlowups),
      (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').ideal
          (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').length =
        ((nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).ideal
          (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).length).comap c.lastMap ∧
      SameNontrivialBoundary
        ((nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').boundary
          (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f').length)
        (((nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).boundary
          (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).length).map fun D => D.comap c.lastMap) := by
  classical
  let _a1 := principalizationOfDimLe T A
  let _a2 := principalizationOfDimLe T' A
  have key : ∀ j, ∃ f', Nonempty $ SequenceOfBlowupsPullback g
      (mbSq $ nonMonomialOrderReductionIter hinv T' _a2 f')
      (mbSq $ nonMonomialOrderReductionIter hinv T _a1 j) := by
    intro j
    induction j with
    | zero =>
        exact ⟨0, nonempty_sequenceOfBlowupsPullback_of_length_eq_zero g hbc.flat _ _
          (length_nonMonomialOrderReductionIter_zero hinv T _a1)
          (length_nonMonomialOrderReductionIter_zero hinv T' _a2)⟩
    | succ j ih =>
        obtain ⟨f', hc⟩ := ih
        obtain ⟨c⟩ := hc
        by_cases hcont : NonMonomialOrderReductionContinues T $ nonMonomialOrderReductionIter hinv T _a1 j
        have _i27 : (NonMonomialOrderReductionContinues T' (nonMonomialOrderReductionIter hinv T' _a2 f') ∧ Nonempty (SequenceOfBlowupsPullback g (extendByNonMonomialPart hinv T' (principalizationOfDimLe T' A) $ nonMonomialOrderReductionIter hinv T' _a2 f').toMarkedSequenceOfBlowups.toSequenceOfBlowups $ mbSq $ extendByNonMonomialPart hinv T (principalizationOfDimLe T A) $ nonMonomialOrderReductionIter hinv T _a1 j)) ∨ Nonempty (SequenceOfBlowupsPullback g (nonMonomialOrderReductionIter hinv T' _a2 f').toMarkedSequenceOfBlowups.toSequenceOfBlowups $ mbSq $ extendByNonMonomialPart hinv T (principalizationOfDimLe T A) $ nonMonomialOrderReductionIter hinv T _a1 j) := by
          let s := nonMonomialOrderReductionIter hinv T _a1 j
          let s' := nonMonomialOrderReductionIter hinv T' _a2 f'
          let _a2 := maxOrderNonMonomial T s
          let _a3 := lastNonMonomialPart T s
          let _a0 := cmI _a3 c.lastMap
          classical
          obtain ⟨hlastIdeal, hsameBoundary⟩ :=
            lastIdeal_and_boundary_comap_of_flat s s' hmult c hbc.flat hideal hbdry
              (isNoetherian_schemeAt_of_isAdmissible T hT s) $ isNoetherian_schemeAt_of_isAdmissible T' hT' s'
          have hle :=
            maxOrderNonMonomial_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc
              s s' c hlastIdeal hsameBoundary
          have hnonMon :=
            lastNonMonomialPart_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
              hbdry hbc s s' c hlastIdeal hsameBoundary
          let _a4 := principalizationOfDimLe T A
          let _a1 := extendByNonMonomialPart hinv T _a4 s
          have hskip : orderAtLeastLocus _a0 _a2 = ∅ →
              Nonempty (SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
                _a1.toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
            intro hempty
            have hL : _a1
                = appendRecursivePrincipalization hinv T _a4 s _a3 _a2 := rfl
            rw [hL]
            exact nonempty_sequenceOfBlowupsPullback_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT' hdim hdim'
              hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary _a3 _a2
              (isAdmissible_nonMonomialTriple hG hT s hcont) hempty
          by_cases hcont' : NonMonomialOrderReductionContinues T' s'
          by_cases heq : maxOrderNonMonomial T' s' = _a2
          refine inl ⟨hcont', ?_⟩
          refine nonempty_sequenceOfBlowupsPullback_extendByNonMonomialPart hG hinv n A B hspec T T' g hT hT' hdim
            hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary hcont hcont' heq ?_
          intro h h'
          refine iff_of_false (markedDataOfSeq_ne_none_of_isMarked s _a3 _a2 _ $ isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT hdim s hcont) ?_
          have hmkU := isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT' hdim' s' hcont'
          rw [hnonMon, heq] at hmkU
          exact markedDataOfSeq_ne_none_of_isMarked s' _a0 _a2 _
            hmkU
          exact inr $ hskip $ orderAtLeastLocus_comap_lastNonMonomialPart_eq_empty_of_lt hG hinv n A T T' g hT hT' hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary $ lt_of_le_of_ne hle heq
          refine inr $ hskip ?_
          rcases lt_or_eq_of_le hle with hlt | heq
          exact orderAtLeastLocus_comap_lastNonMonomialPart_eq_empty_of_lt hG hinv n A T T' g hT hT'
            hdim hdim' hmult hideal hbdry hbc s s' c hlastIdeal hsameBoundary hlt
          have h1 : T'.mult ≤ maxOrderNonMonomial T' s' := by
            rw [hmult, heq]
            exact ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1
          have h2 := fun hx =>
            hcont' $ (nonMonomialOrderReductionContinues_iff T' s').2 ⟨h1, hx⟩
          have h3 := mp_ not_nonempty_iff_eq_empty h2
          rwa [hnonMon, heq] at h3
        rcases _i27 with ⟨hcont', hcmp⟩ | hcmp
        refine ⟨f' + 1, ?_⟩
        rw [nonMonomialOrderReductionIter_succ_of_continues hinv T _a1 j hcont,
          nonMonomialOrderReductionIter_succ_of_continues hinv T' _a2 f' hcont']
        exact hcmp
        refine ⟨f', ?_⟩
        rwa [nonMonomialOrderReductionIter_succ_of_continues hinv T _a1 j hcont]
        refine ⟨f', ?_⟩
        rw [nonMonomialOrderReductionIter_succ_of_not_continues hinv T _a1 j hcont]
        exact ⟨c⟩
  obtain ⟨f', hc⟩ := key f
  obtain ⟨c⟩ := hc
  refine ⟨f', c, ?_⟩
  let _a0 := nonMonomialOrderReductionIter hinv T _a1 f
  exact lastIdeal_and_boundary_comap_of_flat _a0
    (nonMonomialOrderReductionIter hinv T' _a2 f') hmult c hbc.flat hideal hbdry
    (isNoetherian_schemeAt_of_isAdmissible T hT _a0)
    (isNoetherian_schemeAt_of_isAdmissible T' hT' $ nonMonomialOrderReductionIter hinv T' _a2 f')

end

theorem markedDataOfSeq_companionIdeal_ne_none (T : MarkedIdealWithBoundary)
    (hT : IsAdmissible T) (A : PrincipalizationAssignment)
    (s : T.mbs)
    (hcont : CompanionIdealReductionContinues T s) (K : IdealSheafData $ s.obj s.length) (nu_ : ℕ)
    (hK : companionIdeal T s = K) (hnu_ : mult T * maxOrderNonMonomialOnOrderLocus T s = nu_)
    (h : (tripleAtLength T s K nu_).krullDimSucc ≤ T.krullDimSucc) :
    ¬ (markedDataOfSeq s K nu_ (principalizationOfDimLe T A (tripleAtLength T s K nu_) h) = none) := by
  subst hK
  subst hnu_
  let _a0 := companionIdeal T s
  exact markedDataOfSeq_ne_none_of_isMarked s _a0 (tMu T * maxOrderNonMonomialOnOrderLocus T s)
    (principalizationOfDimLe T A (tripleAtLength T s _a0 $ tMu T * maxOrderNonMonomialOnOrderLocus T s) h)
    (isMarked_seqAtEnd_companionIdeal hG hT A s hcont)

section
variable (hinv : ComapIsoInvariance) (n) (A B) (hspec : IsOrderReduction (fun d => d ≤ n) A B)
include hspec
section
variable (T T' : MarkedIdealWithBoundary) (g : scheme T' ⟶ scheme T) (hT : IsAdmissible T) (hT' : IsAdmissible T') (hdim : T.krullDimSucc ≤ n) (hdim' : T'.krullDimSucc ≤ n) (hmult : mult T' = mult T) (hideal : ideal T' = T.ideal.comap g) (hbdry : SameNontrivialBoundary T'.boundary (T.boundary.map fun D => comap D g)) (hbc : BaseChangeCompatible hinv A n T g T'.base T'.structMap)
include hT hT' hdim hdim' hmult hideal hbdry hbc
theorem companionIdealReductionIter_exists_sequenceOfBlowupsPullback (f : ℕ) :
    ∃ (f' : ℕ) (c : SequenceOfBlowupsPullback g
        (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A))
          f').toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))
          f).toMarkedSequenceOfBlowups.toSequenceOfBlowups),
      (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').ideal
          (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').length =
        ((companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).ideal
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).length).comap
            c.lastMap ∧
      SameNontrivialBoundary
        ((companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').boundary
          (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) f').length)
        (((companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).boundary
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).length).map
            fun D => D.comap c.lastMap) := by
  let _c0 := nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)
  let _c1 := principalizationOfDimLe T A
  let _c2 := nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)
  let _c3 := principalizationOfDimLe T' A
  have hflat := hbc.flat
  have key : ∀ m, ∃ f', Nonempty (SequenceOfBlowupsPullback g
      (mbSq (companionIdealReductionIter hinv T' _c3 _c2
        f'))
      (mbSq (companionIdealReductionIter hinv T _c1 _c0
        m))) := by
    intro m
    induction m with
    | zero =>
        have _i28 : Nonempty (SequenceOfBlowupsPullback g (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)).toMarkedSequenceOfBlowups.toSequenceOfBlowups (mbSq (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)))) := by
          obtain ⟨f1_, c, hI, hB⟩ := nonMonomialOrderReductionIter_exists_sequenceOfBlowupsPullback hG hinv n A B hspec T T' g hT
            hT' hdim hdim' hmult hideal hbdry hbc (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)
          have hlow :=
            (nonMonomialOrderReduction_eq hinv T (principalizationOfDimLe T A)).symm
          have hncT : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A)
              (maxOrder (nonMonomialPart T.boundary T.ideal) + 1)) := by
            rw [hlow]
            exact not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction hG hinv hspec hT hdim
          have hncT' : ¬ NonMonomialOrderReductionContinues T' (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f1_) := by
            intro hc
            exact hncT (nonMonomialOrderReductionContinues_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult hideal
              hbdry hbc
              (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (maxOrder (nonMonomialPart T.boundary T.ideal) + 1))
              (nonMonomialOrderReductionIter hinv T' (principalizationOfDimLe T' A) f1_) c hI hB hc)
          let _a1 := max f1_ (maxOrder (nonMonomialPart T'.boundary T'.ideal) + 1)
          refine ⟨?_⟩
          rwa [← (nonMonomialOrderReductionIter_eq_of_not_continues hinv T' (principalizationOfDimLe T' A) f1_ hncT' _a1 (le_max_left _ _)).symm.trans (nonMonomialOrderReductionIter_eq_of_maxOrder_lt hG hinv hspec hT' hdim' _a1 (le_max_right _ _)), ← hlow]
        exact ⟨0, _i28⟩
    | succ m ih =>
        obtain ⟨f1_, hc⟩ := ih
        obtain ⟨c⟩ := hc
        by_cases hcont : CompanionIdealReductionContinues T
            (companionIdealReductionIter hinv T _c1 _c0 m)
        obtain ⟨hI, hB⟩ := lastIdeal_and_boundary_comap_of_isAdmissible T T' g hT hT' hflat hmult hideal hbdry
          (companionIdealReductionIter hinv T _c1 _c0 m)
          (companionIdealReductionIter hinv T' _c3 _c2 f1_) c
        have hstepL := companionIdealReductionIter_succ_of_continues hinv T _c1
          _c0 m hcont
        have hle := maxOrderNonMonomialOnOrderLocus_le_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult
          hideal hbdry hbc
          (companionIdealReductionIter hinv T _c1 _c0 m)
          (companionIdealReductionIter hinv T' _c3 _c2 f1_) c hI hB
        rcases hle.lt_or_eq with hlt | heq
        have hJ := companionTriple_isAdmissible hG hT
          (companionIdealReductionIter hinv T _c1 _c0 m) hcont
        have hempty := orderAtLeastLocus_comap_companionIdeal_eq_empty_of_lt hG hinv n A
          T T' g hT hT' hdim hdim' hmult hideal hbdry hbc
          (companionIdealReductionIter hinv T _c1 _c0 m)
          (companionIdealReductionIter hinv T' _c3 _c2 f1_) c hI hB
          hlt
        refine ⟨f1_, ?_⟩
        rw [hstepL]
        exact nonempty_sequenceOfBlowupsPullback_of_orderAtLeastLocus_empty hG hinv n A B hspec T T' g hT hT'
          hdim hdim' hmult hideal hbdry hbc
          (companionIdealReductionIter hinv T _c1 _c0 m)
          (companionIdealReductionIter hinv T' _c3 _c2 f1_) c hI hB
          (companionIdeal T
            (companionIdealReductionIter hinv T _c1 _c0 m))
          (T.mult * maxOrderNonMonomialOnOrderLocus T
            (companionIdealReductionIter hinv T _c1 _c0 m)) hJ hempty
        have hcont1 := hcont
        have hcont' : CompanionIdealReductionContinues T'
            (companionIdealReductionIter hinv T' _c3 _c2 f1_) := by
          show (1 : ℕ) ≤ maxOrderNonMonomialOnOrderLocus T'
            (companionIdealReductionIter hinv T' _c3 _c2 f1_)
          exact le_trans hcont1 heq.ge
        have hid' := companionIdeal_eq_comap_lastMap_of_pullback hG hinv n A T T' g hT hT' hdim
          hdim' hmult hideal hbdry hbc
          (companionIdealReductionIter hinv T _c1 _c0 m)
          (companionIdealReductionIter hinv T' _c3 _c2 f1_) c hI hB
          heq
        have hmu' : T'.mult * maxOrderNonMonomialOnOrderLocus T'
            (companionIdealReductionIter hinv T' _c3 _c2 f1_)
            = T.mult * maxOrderNonMonomialOnOrderLocus T
              (companionIdealReductionIter hinv T _c1 _c0 m) := by
          rw [hmult, heq]
        refine ⟨f1_ + 1, ?_⟩
        rw [hstepL, companionIdealReductionIter_succ_of_continues hinv T' _c3
          _c2 f1_ hcont']
        refine nonempty_sequenceOfBlowupsPullback_extendByCompanionIdeal hG hinv n A B hspec T T' g hT hT'
          hdim hdim' hmult hideal hbdry hbc
          (companionIdealReductionIter hinv T _c1 _c0 m)
          (companionIdealReductionIter hinv T' _c3 _c2 f1_) c hI hB
          hcont hcont' heq ?_
        intro h h'
        refine iff_of_false ?_ ?_
        exact markedDataOfSeq_companionIdeal_ne_none hG T hT A
          (companionIdealReductionIter hinv T _c1 _c0 m) hcont
          (companionIdeal T
            (companionIdealReductionIter hinv T _c1 _c0 m))
          (T.mult * maxOrderNonMonomialOnOrderLocus T
            (companionIdealReductionIter hinv T _c1 _c0 m))
          rfl rfl h
        exact markedDataOfSeq_companionIdeal_ne_none hG T' hT' A
          (companionIdealReductionIter hinv T' _c3 _c2 f1_) hcont'
          ((companionIdeal T
            (companionIdealReductionIter hinv T _c1 _c0 m)).comap
              c.lastMap)
          (T.mult * maxOrderNonMonomialOnOrderLocus T
            (companionIdealReductionIter hinv T _c1 _c0 m))
          hid' hmu' h'
        refine ⟨f1_, ?_⟩
        rw [companionIdealReductionIter_succ_of_not_continues hinv T _c1
          _c0 m hcont]
        exact ⟨c⟩
  obtain ⟨f', hn⟩ := key f
  obtain ⟨c⟩ := hn
  exact ⟨f', c, lastIdeal_and_boundary_comap_of_isAdmissible T T' g hT hT' hflat hmult hideal hbdry
    (companionIdealReductionIter hinv T _c1 _c0 f)
    (companionIdealReductionIter hinv T' _c3 _c2 f') c⟩

theorem orderReductionSeq_isPullbackBlowupSequence_of_comap :
    IsPullbackBlowupSequence g (orderReductionSeq hinv T' (principalizationOfDimLe T' A)).toSequenceOfBlowups
      (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups := by
  classical
  by_cases hemp : orderAtLeastLocus T'.ideal T'.mult = ∅
  have hU :=
    orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T' A hemp
  let _s0 := orderReductionSeq hinv T $ principalizationOfDimLe T A
  have hmiss : ∀ i, i < msLen _s0 →
      ∀ z : (msAt _s0 i),
        z ∈ spI (msCtr _s0 i) →
        ∀ y,
          g.base y ≠ bsM (msPrj _s0 i) z := by
    intro i hi z hz y hcon
    have hkey := projectionToBase_mem_orderAtLeastLocus hG hinv T hT _s0 i
      (le_of_lt hi) z $ _s0.center_order i hi hz
    rw [← hcon] at hkey
    have hmem : y ∈ orderAtLeastLocus T'.ideal T'.mult := by
      rw [mem_orderAtLeastLocus_iff, hideal, hmult, orderAt_comap_of_baseChangeCompatible hinv A n T hT g T'.base T'.structMap hbc T.ideal y]
      exact (mem_orderAtLeastLocus_iff T.ideal T.mult $ bsM g y).1 hkey
    rw [hemp] at hmem
    simp [mem_empty_iff_false] at hmem
  let _a9 := orderReductionSeq hinv T' $ principalizationOfDimLe T' A
  obtain ⟨cc⟩ : Nonempty $ SequenceOfBlowupsPullback g _a9.toSequenceOfBlowups _s0.toSequenceOfBlowups := by
    let sU := _a9.toSequenceOfBlowups
    have := hbc.flat
    refine ⟨SequenceOfBlowupsPullback.ofBlowupDataOfSeq $ SequenceOfBlowupsPullback.ofCentersMissImage g (ofSequenceOfBlowups _s0.toSequenceOfBlowups) ?_
      (ofSequenceOfBlowups sU) $ tr_ (ofSequenceOfBlowups_length sU) hU⟩
    intro i hi z hz y
    rw [ofSequenceOfBlowups_length _s0.toSequenceOfBlowups] at hi
    rw [st_ (toSequenceOfBlowups_projectionToBase (ofSequenceOfBlowups _s0.toSequenceOfBlowups) i) $ BlowupSequenceData.projectionToBase_toSequenceOfBlowups_ofSequenceOfBlowups _s0.toSequenceOfBlowups i]
    exact hmiss i hi z hz y
  exact cc.isPullbackSequenceOfBlowups
  have hT'ne := nonempty_iff_ne_empty.2 hemp
  let _a6 := orderAtLeastLocus T.ideal T.mult
  have hTne : _a6.Nonempty := by
    rcases eq_empty_or_nonempty _a6 with h | h
    exfalso
    apply hemp
    rw [hideal, hmult]
    exact orderAtLeastLocus_comap_eq_empty_of_baseChangeCompatible hinv A n T hT g T'.base T'.structMap hbc h
    exact h
  let _a1 := nonMonomialOrderReduction hinv T $ principalizationOfDimLe T A
  obtain ⟨f', hc⟩ := companionIdealReductionIter_exists_sequenceOfBlowupsPullback hG hinv n A B hspec T T' g hT hT'
    hdim hdim' hmult hideal hbdry hbc $ maxOrderNonMonomialOnOrderLocus T _a1 + 1
  have hlowStop : ¬ CompanionIdealReductionContinues T
      (companionIdealReductionIter hinv T (principalizationOfDimLe T A) _a1
        (maxOrderNonMonomialOnOrderLocus T _a1 + 1)) := by
    rw [← companionIdealReduction_eq hinv T $ principalizationOfDimLe T A]
    exact not_companionIdealReductionContinues_companionIdealReduction hG hinv hspec hT hdim
  have hupStop : ¬ CompanionIdealReductionContinues T'
      (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' $ principalizationOfDimLe T' A) f') := by
    obtain ⟨c0, h1, h2⟩ := hc
    intro hcont
    exact hlowStop $ companionIdealReductionContinues_of_pullback hG hinv n A T T' g hT hT' hdim hdim' hmult
      hideal hbdry hbc _ _ c0 h1 h2 hcont
  have hstop' : ¬ CompanionIdealReductionContinues T'
      (companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' $ principalizationOfDimLe T' A)
        (maxOrderNonMonomialOnOrderLocus T' (nonMonomialOrderReduction hinv T' $ principalizationOfDimLe T' A) + 1)) := by
    rw [← companionIdealReduction_eq hinv T' $ principalizationOfDimLe T' A]
    exact not_companionIdealReductionContinues_companionIdealReduction hG hinv hspec hT' hdim'
  have hupEq : companionIdealReductionIter hinv T' (principalizationOfDimLe T' A) (nonMonomialOrderReduction hinv T' $ principalizationOfDimLe T' A) f'
      = companionIdealReduction hinv T' (principalizationOfDimLe T' A) := by
    rw [companionIdealReduction_eq hinv T' $ principalizationOfDimLe T' A]
    rcases le_total f' (maxOrderNonMonomialOnOrderLocus T' (nonMonomialOrderReduction hinv T' (principalizationOfDimLe T' A)) + 1) with h | h
    exact (companionIdealReductionIter_eq_of_not_continues hinv T' (principalizationOfDimLe T' A)
      (nonMonomialOrderReduction hinv T' $ principalizationOfDimLe T' A) f' hupStop _ h).symm
    exact companionIdealReductionIter_eq_of_not_continues hinv T' (principalizationOfDimLe T' A)
      (nonMonomialOrderReduction hinv T' $ principalizationOfDimLe T' A) _ hstop' f' h
  obtain ⟨c, hidealLastComap, hlastBoundary⟩ := exists_sequenceOfBlowupsPullback_congr g _ _ _ _ hupEq
    (companionIdealReduction_eq hinv T $ principalizationOfDimLe T A).symm hc
  let _a3 := companionIdealReduction hinv T $ principalizationOfDimLe T A
  have hIP := isPullbackSequenceOfBlowups_monomial_of_pullback hinv hG.monomialInputs n A
    T T' g hT hbc _a3 (companionIdealReduction hinv T' $ principalizationOfDimLe T' A) c hmult
    hidealLastComap hlastBoundary (isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim) $ isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT' hdim'
  obtain ⟨cc⟩ := hIP.nonempty_sequenceOfBlowupsPullback
  rw [orderReductionSeq_eq_of_nonempty hinv T (principalizationOfDimLe T A) hTne, orderReductionSeq_eq_of_nonempty hinv T' (principalizationOfDimLe T' A) hT'ne,
    (orderReductionData_eq hinv T $ principalizationOfDimLe T A), orderReductionData_eq hinv T' $ principalizationOfDimLe T' A]
  exact isPullbackBlowupSequence_append_of_two_fields g _a3 (orderReductionMonomialSequence hinv T A)
    (companionIdealReduction hinv T' $ principalizationOfDimLe T' A) (orderReductionMonomialSequence hinv T' A) hinv c
    (SequenceOfBlowupsPullback.toBlowupDataOfSeq cc)
end

theorem orderReductionSeq_isPullbackBlowupSequence_pullbackOverField
    (T : MarkedIdealWithBoundary) (hT : IsAdmissible T) (hdim : T.krullDimSucc ≤ n)
    {Y : Sch} (k' : Type) [Field k'] q
    g E'
    (hE : SameNontrivialBoundary E' $ T.boundary.map fun D => comap D g)
    (hT' : IsAdmissible $ withBoundary (T.pullbackOverField Y k' q g) E')
    (hdim' : (withBoundary (T.pullbackOverField Y k' q g) E').krullDimSucc ≤ n)
    (hbc : BaseChangeCompatible hinv A n T g k' q) :
    IsPullbackBlowupSequence g
      (orderReductionSeq hinv (withBoundary (T.pullbackOverField Y k' q g) E')
        (principalizationOfDimLe (withBoundary (T.pullbackOverField Y k' q g) E') A)).toSequenceOfBlowups
      (orderReductionSeq hinv T $ principalizationOfDimLe T A).toSequenceOfBlowups := by
  exact orderReductionSeq_isPullbackBlowupSequence_of_comap hG hinv n A B hspec T
    (mk k' Y q (T.ideal.comap g) T.mult E') g hT hT' hdim hdim' rfl rfl hE hbc
end
end





namespace MarkedPullbackSquare

variable {T : MarkedIdealWithBoundary} {Y} {g : Y ⟶ scheme T}

section
variable (S : MarkedPullbackSquare T g)
theorem smooth_verticalMap [Smooth g] :
    Smooth S.left :=
  of_isPullback
    (P := @Smooth) S.isPullback.flip ‹Smooth g›

theorem orderAt_comap_verticalMap_le_of_forall_orderAt_le (hT : IsAdmissible T)
    (hg : OrderAtPullbackInvariant T g)
    (hord : ∀ x : ↥S.baseScheme, orderAt S.ideal x ≤ (mult S : ENat)) (y : ↥S.topScheme) :
    orderAt (S.ideal.comap S.left) y ≤ (mult S : ENat) :=
  S.orderAt_comap_verticalMap_le hT hg S.ideal _ hord y

theorem verticalMap_comp_lowerStructMap (q : Y ⟶ Sp T.base)
    (hq : g ≫ T.structMap = q) :
    S.left ≫ S.structMap = S.top ≫ q := by
  rw [← S.bottom_structMap, ← hq, ← assoc, S.isPullback.w, assoc]
end

end MarkedPullbackSquare

theorem baseChangeCompatible_of_smooth (hG : PrincipalizationGeometryHypotheses) (ta_ : ComapIsoInvariance) (n : ℕ)
    (F G : PrincipalizationAssignment) (hF : IsOrderReduction (fun d => d ≤ n) F G)
    (T : MarkedIdealWithBoundary) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) {Y : Sch}
    (g : Y ⟶ T.scheme) [Smooth g]
    (q : Y ⟶ Sp T.base) (hq : g ≫ T.structMap = q) :
    BaseChangeCompatible ta_ F n T g T.base q := by
  have hgord : OrderAtPullbackInvariant T g := by
    intro B b pB IB EB hB hcomm Q q p hpb A y
    have := hB.charZero
    have := hB.smooth
    have :=
      of_isPullback
        (P := @Smooth) hpb.flip inferInstance
    exact orderAt_comap T.base pB q A y
  refine ⟨?_, inferInstance, ?_, ?_, hgord⟩
  intro S hord E hE hV hdimS
  have := MarkedPullbackSquare.smooth_verticalMap S
  exact hF.smooth_pullback S.lowerTriple S.valid (le_trans S.dim_le hdim) hord S.topScheme
    (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq) E hE hV hdimS
    (fun y => MarkedPullbackSquare.orderAt_comap_verticalMap_le_of_forall_orderAt_le S hT hgord hord y)
  intro S hmon E hE hmon'
  have := MarkedPullbackSquare.smooth_verticalMap S
  exact monomialPrincipalization_isPullbackBlowupSequence_of_smooth hG.monomialInputs ta_ S.lowerTriple hmon
    S.topScheme (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq) E hE hmon'
  intro S E hE hV
  have := MarkedPullbackSquare.smooth_verticalMap S
  exact hG.nonMonomialPart_comap_of_sameNontrivialBoundary S.lowerTriple S.valid S.topScheme
    (S.top ≫ q) S.left (MarkedPullbackSquare.verticalMap_comp_lowerStructMap S q hq)
    (hG.monomialInputs.withBoundary_valid (S.upperTriple T.base q E) hV
  (tBd (S.lowerTriple.pbOF (S.top ≫ q) S.left)) hE.symm)
    E hE hV





section
variable (T : MarkedIdealWithBoundary) (L : Type) [Field L] (f : T.base →+* L)
abbrev baseChangeProj :
    scheme (bc T f) ⟶ scheme T :=
  pullback.fst T.structMap $ specMapOfFieldHom T.base L f

abbrev baseChangeStructMap :
    scheme (bc T f) ⟶ Sp L :=
  pullback.snd T.structMap $ specMapOfFieldHom T.base L f
end

section
variable {A B : Sch} (e : A ≅ B)
include e
theorem comap_hom_comap_inv_eq_self (D : ISD A) :
    comap (comap D e.inv) e.hom = D := by
  rw [← comap_comp, e.hom_inv_id]
  simp

theorem krullDimSucc_eq_of_iso : krullDimSucc A = krullDimSucc B := by
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  congr 1
  exact ((TopCat.homeoOfIso $ Scheme.forgetToTop.mapIso e).isHomeomorph).topologicalKrullDim_eq
end

section
variable {k : Type} [Field k]
private theorem markedIdealWithBoundary_mk_congr {A : Sch}
    {p q : A ⟶ Sp k} {I J : ISD A} {m n : ℕ}
    {E F : Bdy A} (hp : p = q) (hI : I = J) (hm : m = n) (hE : E = F) :
    mk k A p I m E = mk k A q J n F :=by simp_all
theorem isAdmissible_comap_of_iso {A B : Sch} (e : A ≅ B)
    (s : B ⟶ Sp k) (J : ISD B) (m : ℕ)
    (E : Bdy B)
    (h : IsAdmissible $ mk k B s J m E) :
    (mk k A (hom e ≫ s) (comap J e.hom) m
      (E.map fun D : ISD B => comap D e.hom)).IsAdmissible := by
  have hsm := h.smooth
  have hqc := h.quasiCompact
  exact
    { charZero := h.charZero
      locallyOfFiniteType := inferInstance
      nonzeroOnComponents := nonzeroOnComponents_comap_iso_hom e J h.nonzeroOnComponents
      one_le_mult := h.one_le_mult
      quasiCompact := inferInstance
      smooth := inferInstance
      snc := inStrictNormalCrossingPosition_comap_iso s e E h.snc }
end

theorem nonMonomialPart_eq_of_isMonomialSplitting_unique {X : Sch} {E : Bdy X}
    {I M N : ISD X} (hs : IsMonomialSplitting E I M N)
    (hu : ∀ M' N' : ISD X, IsMonomialSplitting E I M' N' → M = M' ∧ N = N') :
    nonMonomialPart E I = N := by
  have hex : ∃ q : ISD X × ISD X, IsMonomialSplitting E I q.1 q.2 :=
    ⟨(M, N), hs⟩
  unfold nonMonomialPart monomialSplitting
  rw [dif_pos hex]
  exact sy_ $ an2 $ hu _ _ hex.choose_spec

theorem nonMonomialPartBaseChange_of_flat (hG : PrincipalizationGeometryHypotheses) (T : MarkedIdealWithBoundary)
    {Y : Sch} (g : Y ⟶ scheme T) [Flat g] (k' : Type) [Field k']
    (q : Y ⟶ Sp k') :
    NonMonomialPartBaseChange T g k' q := by
  intro S E hE hV
  have := S.flat_verticalMap
  obtain ⟨M, N, hMN⟩ := hG.splitting_exists S.lowerTriple S.valid
  have hu1 :=
    fun M' N' h' => hG.splitting_unique S.lowerTriple S.valid M N M' N' hMN h'
  have hMNcomap := (isMonomialSplitting_congr hE _ _ _).1 $ isMonomialSplitting_comap_of_flat S.left hMN
  have hu2 :=
    fun M' N' h' => hG.splitting_unique (S.upperTriple k' q E) hV (cmI M S.left)
      (cmI N S.left) M' N' hMNcomap h'
  rw [nonMonomialPart_eq_of_isMonomialSplitting_unique hMNcomap hu2, nonMonomialPart_eq_of_isMonomialSplitting_unique hMN hu1]

theorem isPullbackBlowupSequence_of_eq_of_heq (F : PrincipalizationAssignment) (B : MarkedIdealWithBoundary)
    {W U : MarkedIdealWithBoundary} (h : W = U) (g : W.scheme ⟶ scheme B) (g' : U.scheme ⟶ scheme B)
    (hg : HEq g g')
    (hh : IsPullbackBlowupSequence g (F W).toSequenceOfBlowups (F B).toSequenceOfBlowups) :
    IsPullbackBlowupSequence g' (F U).toSequenceOfBlowups (F B).toSequenceOfBlowups := by
  subst h
  have hgg := eq_of_heq hg
  subst hgg
  exact hh

theorem monomialPrincipalizationBaseChange_of_flat (hG : PrincipalizationGeometryHypotheses) (ta_ : ComapIsoInvariance)
    (T : MarkedIdealWithBoundary) (hT : IsAdmissible T) {Y : Sch} (g : Y ⟶ scheme T)
    [Flat g] (hg : OrderAtPullbackInvariant T g) (k' : Type) [Field k']
    (q : Y ⟶ Sp k') :
    MonomialPrincipalizationBaseChange ta_ T g k' q := by
  intro S hsmooth E hE hSm'
  have := S.flat_verticalMap
  have _i30 : OrderAtPullbackInvariant S.lowerTriple S.left := by
    intro B b pB IB EB hvalid hbp Q a b' hpb A y
    refine hg B (b ≫ S.bottom) pB IB EB ?_ ?_ Q a (b' ≫ S.top) (hpb.paste_vert S.isPullback) A y
    exact
      { charZero := hvalid.charZero
        locallyOfFiniteType := hvalid.locallyOfFiniteType
        nonzeroOnComponents := hvalid.nonzeroOnComponents
        one_le_mult := hT.one_le_mult
        quasiCompact := hvalid.quasiCompact
        smooth := hvalid.smooth
        snc := hvalid.snc }
    rwa [assoc, S.bottom_structMap]
  exact monomialPrincipalization_isPullbackBlowupSequence_of_flat hG.monomialInputs ta_ S.lowerTriple S.topScheme k'
    (S.top ≫ q) S.left E hsmooth hE.symm hSm'
    (fun B b pB hbp IB EB hv Q a b' hpb A z =>
      _i30 B b pB IB EB hv hbp Q a b' hpb A z)

namespace MarkedPullbackSquare

theorem isPullback_comp_baseChangeStructMap {T : MarkedIdealWithBoundary} {L : Type} [Field L]
    {f : T.base →+* L} (S : MarkedPullbackSquare T $ baseChangeProj T L f) :
    IsPullback S.left (S.top ≫ baseChangeStructMap T L f) S.structMap $ specMapOfFieldHom T.base L f := by
  have h := S.isPullback.paste_vert
    (of_hasPullback T.structMap $ specMapOfFieldHom T.base L f)
  rwa [S.bottom_structMap] at h

end MarkedPullbackSquare

theorem baseChangeCompatible_baseChangeProj_of_isOrderReduction (hG : PrincipalizationGeometryHypotheses) (ta_ : ComapIsoInvariance) (n : ℕ)
    (F G : PrincipalizationAssignment) (hF : IsOrderReduction (fun d => d ≤ n) F G)
    (T : MarkedIdealWithBoundary) (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (L : Type) [Field L] [CharZero L]
    (f : T.base →+* L) :
    BaseChangeCompatible ta_ F n T (baseChangeProj T L f) L (baseChangeStructMap T L f) := by
  let _a0 := baseChangeProj T L f
  have hflat : Flat _a0 :=
    inferInstanceAs
      (Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
  let _a1 := orderAtPullbackInvariant_baseChange_field hG T hT L f
  let _a2 := baseChangeStructMap T L f
  refine ⟨?_, hflat,
    monomialPrincipalizationBaseChange_of_flat hG ta_ T hT _a0
      _a1 L _a2,
    nonMonomialPartBaseChange_of_flat hG T _a0 L _a2,
    _a1⟩
  intro S hord E hE hV hd
  have hgstable :=
    orderAtPullbackInvariant_baseChange_field hG T hT L f
  have hsq := MarkedPullbackSquare.isPullback_comp_baseChangeStructMap S
  let _a0 := specMapOfFieldHom T.base L f
  let _a1 := S.top ≫ baseChangeStructMap T L f
  let _a3 := pullback.fst S.structMap _a0
  obtain ⟨e, hfst, hsnd⟩ :
      ∃ e : S.topScheme ≅ pullback S.structMap _a0,
        hom e ≫ _a3 = S.left ∧
          hom e ≫ pullback.snd S.structMap _a0 =
            _a1 :=
    ⟨hsq.isoPullback, hsq.isoPullback_hom_fst, hsq.isoPullback_hom_snd⟩
  have h2gen : ∀ A : S.baseScheme.IdealSheafData,
      comap (comap A S.left) e.inv =
        cmI A _a3 := by
    intro A
    have h : comap (comap A S.left) e.inv = cmI A (isoI e ≫ S.left) := by simp
    rw [h, ← hfst, inv_hom_id_assoc]
  have hideal : comap (S.ideal.comap _a3) e.hom
      = S.ideal.comap S.left := by
    have h : comap (S.ideal.comap _a3) e.hom
        = S.ideal.comap (isoH e ≫ _a3) := by simp
    rw [h, hfst]
  have hmapinv : ∀ l,
      List.map (fun D : S.topScheme.IdealSheafData => comap D e.inv)
          (List.map (fun D : S.baseScheme.IdealSheafData => comap D S.left) l)
        = List.map (fun D : S.baseScheme.IdealSheafData =>
            cmI D _a3) l := by simp_all
  let _a4 := pullback S.structMap _a0
  have hmapback : ∀ l,
      List.map (fun D : ISD _a4 =>
          comap D e.hom) (List.map (fun D : S.topScheme.IdealSheafData => comap D e.inv) l)
        = l := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => simp [map_cons, ih, comap_hom_comap_inv_eq_self e a]
  have hdimS := le_trans S.dim_le hdim
  have hBE : SameNontrivialBoundary (S.lowerTriple.baseChange L f).boundary
      (E.map fun D : S.topScheme.IdealSheafData => comap D e.inv) := by
    have h := MarkedIdealWithBoundary.SameNontrivialBoundary.map (·.comap e.inv) (by simp) hE
    rwa [hmapinv] at h
  have h0 := isAdmissible_comap_of_iso (k := L) e.symm _a1
    (S.ideal.comap S.left) S.mult E hV
  simp [Iso.symm_hom] at h0
  rw [← hsnd, Iso.inv_hom_id_assoc, h2gen S.ideal] at h0
  have hval' := h0
  let _a2 := S.lowerTriple.baseChange L f
  have hdim' : (_a2.withBoundary
      (E.map fun D : S.topScheme.IdealSheafData => comap D e.inv)).krullDimSucc ≤ n := by
    show krullDimSucc _a4 ≤ n
    rwa [← krullDimSucc_eq_of_iso e]
  have hOB'fun : ∀ y,
      orderAt (S.ideal.comap _a3) y
        ≤ S.mult := by
    intro y
    have hy := S.orderAt_comap_verticalMap_le_of_forall_orderAt_le hT hgstable hord $ isoI e y
    have h3 : orderAt (comap (S.ideal.comap S.left) e.symm.hom) y
        = orderAt (S.ideal.comap S.left) (e.symm.hom y) :=
      orderAt_comap_of_isOpenImmersion e.symm.hom _ y
    simp [symm_hom] at h3
    rw [h2gen S.ideal] at h3
    rwa [h3]
  have hOB' : (_a2.withBoundary
      (E.map fun D : S.topScheme.IdealSheafData => comap D e.inv)).IsOrderBoundedByMult :=
    mpr (isOrderBoundedByMult_iff _) hOB'fun
  have hpull := hF.base_change S.lowerTriple S.valid hdimS (mpr_ (isOrderBoundedByMult_iff _) hord) L f
    (E.map fun D : S.topScheme.IdealSheafData => comap D e.inv) hBE hval' hdim' hOB'
  have htri : (((_a2.withBoundary
        (E.map fun D : S.topScheme.IdealSheafData => comap D e.inv)).pullbackAlong
        S.topScheme _a1 e.hom).withBoundary E)
      = S.upperTriple L (baseChangeStructMap T L f) E :=
    markedIdealWithBoundary_mk_congr rfl hideal rfl rfl
  have hBE2 : SameNontrivialBoundary
      ((_a2.withBoundary
        (E.map fun D : S.topScheme.IdealSheafData => comap D e.inv)).pullbackAlong
        S.topScheme _a1 e.hom).boundary E := by
    show SameNontrivialBoundary
      (List.map (fun D : ISD _a4 =>
        comap D e.hom) (E.map fun D : S.topScheme.IdealSheafData => comap D e.inv)) E
    rw [hmapback]
    exact MarkedIdealWithBoundary.SameNontrivialBoundary.refl E
  have hval2 := hV
  rw [← htri] at hval2
  have hOB2 : (((_a2.withBoundary
        (E.map fun D : S.topScheme.IdealSheafData => comap D e.inv)).pullbackAlong
        S.topScheme _a1 e.hom).withBoundary E).IsOrderBoundedByMult := by
    rw [htri]
    exact mpr_ (isOrderBoundedByMult_iff _)
      (S.orderAt_comap_verticalMap_le_of_forall_orderAt_le hT hgstable hord)
  have hsmE : Smooth e.hom := inferInstance
  have hsjE : Surjective e.hom := inferInstance
  have hstrict := @IsOrderReduction.smooth_pullback_strict (· ≤ n) F G hF
    (_a2.withBoundary
      (E.map fun D : S.topScheme.IdealSheafData => comap D e.inv))
    hval' hdim' hOB' S.topScheme _a1 e.hom hsmE hsjE hsnd E hBE2
    hval2 hd hOB2
  have hres := hpull.comp_isStrictPullbackSequenceOfBlowups hstrict
  rw [hfst] at hres
  exact isPullbackBlowupSequence_of_eq_of_heq F S.lowerTriple htri S.left S.left HEq.rfl hres





namespace MaxOrderReduction

theorem isMaxOrderReduction_canonicalAlgorithmRules (hG : PrincipalizationGeometryHypotheses)
    (hres : StrictTransformIsBlowupOfClosedSubscheme) n (A B : PrincipalizationAssignment)
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) :
    IsMaxOrderReduction (fun d => d ≤ n) ((canonicalAlgorithmRules hres).maxOrderFamily A) A :=
  by
  let hinv := comapIsoInvariance
  have hmon : MonomialPrincipalizationHypotheses hinv :=
    { cert := fun T hTm i hi =>
        PrincipalizationCertificate.memory
          (monomialPrincipalization_center_subset_boundaryLocus hG.monomialInputs hinv T hTm i hi)
      center_nonempty := monomialPrincipalization_center_support_nonempty hG.monomialInputs hinv
      resolves := fun T hTm => by
        have hmon := isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hG.monomialInputs hinv T hTm $ monomialStallIndexOfTriple hinv T
        have hcs := orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero hG.monomialInputs hmon $ minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero hG.monomialInputs hinv T hTm
        refine mpr_ (isResolution_iff _) ?_
        rwa [monomialPrincipalization_apply, toMarkedSequence_lastIdeal]
      trivial_of_coSupport_empty := monomialPrincipalization_length_eq_zero_of_empty hinv }
  refine
    { cert := fun T hT hdim i hi => certificate_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      orderRed_equiv := fun T hT hdim hE hord =>
        orderReductionSeq_isomorphic_of_boundary_nil hG hinv hmon hspec hT hdim hE hord
      center_nonempty := fun T hT hdim i hi =>
        center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      resolves := fun T hT hdim => isResolution_orderReductionSeq hG hinv hmon hspec hT hdim
      trivial_of_coSupport_empty := fun T hT hdim hc =>
        orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A hc
      base_change := ?_
      base_change_strict := ?_
      smooth_pullback := ?_
      smooth_pullback_strict := ?_ }
  intro T hT hdim L _ _ f E' hE hT' hdim'
  exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
    (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
    (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
  intro T hT hdim L _ _ f E' hE hT' hdim'
  have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
    (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
    (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
  have hsurj : Surjective $ baseChangeProj T L f :=
    instSurjectivePullbackFstSpecMapField T.base L f T.scheme T.structMap
  exact hp.isStrictPullback_of_surjective fun i hi =>
    (support_nonempty_iff_ne_top _).mp
      (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)
  intro T hT hdim Y q h hsm hq E' hE hT' hdim'
  exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
    hE.symm hT' hdim' $ baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq
  intro T hT hdim Y q h hsm hsurj hq E' hE hT' hdim'
  have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
    hE.symm hT' hdim' $ baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq
  exact hp.isStrictPullback_of_surjective fun i hi =>
    (support_nonempty_iff_ne_top _).mp
      (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)

end MaxOrderReduction

end FunctorialResolution.EmbeddedResolution

end
end
noncomputable section
open Eq (trans)
open Function (Bijective Surjective comp_apply)
open FunctorialResolution.EmbeddedResolution (IsDerivBalancedTunedSheafMulLcm comap_ker_subschemeio_comp comap_strictTransform_of_flat_of_isLocallyNoetherian quasiCompact_strictTransformio_of_isLocallyNoetherian restrictIdeal_eq_top_iff_forall_notMem_support strictTransform_comap_of_comap_center_eq_top tunedSheaf_one_one)
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData (boundary_succ boundary_zero controlledTransform_zero empty_length ofSequenceOfBlowups ofSequenceOfBlowups_length ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic pow_exceptionalIdeal_mul_controlledTransform_succ toMarkedBlowupSequenceData_toSequenceOfBlowups toSequenceOfBlowups_schemeAt)
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (toMarkedSequence_projectionToBase)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (pullbackAlong withBoundary)
open FunctorialResolution.EmbeddedResolution.MaxContactCoverData (appendLowerDimReduction_eq_concatOfIsMarked appendLowerDimReduction_of_not_locallyOfFiniteType asMarkedSeq_toSequenceOfBlowups chosenCoverData concatOfIsMarked_eq_append_of_isMarked coverMap_eq_sigmaOpensDesc coverTriple derivedTriple_mult derivedTriple_scheme derivedTriple_structureMorphism exists_descendStrictPullback_eq_some flat_coverMap_of_isAdmissible isMaxContactCover_chosenCoverData isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some reduceAlongHypersurface_eq_appendLowerDimReduction reduceOrder_eq_asMarkedSeq separateBoundary_succ smooth_coverMap_of_isAdmissible tunedMult)
open FunctorialResolution.EmbeddedResolution.MaxContactReduction (FiniteOpenCoverWithIdeals IsMaxContactCover appendLowerDimReduction concatOfIsMarked dropTrivialBoundary reduceAlongHypersurface separateBoundary strictTransformAtLength strictTransformAtLength_eq)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (Isomorphic)
open IsOpenImmersion (isoOfRangeEq isoOfRangeEq_hom_fac lift_fac of_comp)
open List (append length)
open SetLike (coe_subset_coe ext')
open TopologicalSpace (IrreducibleCloseds NoetherianSpace)
section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionIndependence

theorem toSequenceOfBlowups_eq_of_heq {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I1 I2 : ISD X} {m1 m2 : ℕ}
    {E1_ E2_ : Bdy X} (s1_ : MarkedSequenceOfBlowups p I1 m1 E1_)
    (s2_ : MarkedSequenceOfBlowups p I2 m2 E2_) (hI : I1 = I2) (hm : m1 = m2) (hE : E1_ = E2_)
    (h : HEq s1_ s2_) : toSequenceOfBlowups s1_ = toSequenceOfBlowups s2_ := by
  subst hI
  subst hm
  subst hE
  rw [eq_of_heq h]

theorem subschemeio_comap_comp_comp_eq {A B C : Sch} (e : A ⟶ B) (J : ISD B)
    (f g : B ⟶ C) (h : J.subschemeι ≫ f = J.subschemeι ≫ g) :
    (J.comap e).si ≫ (e ≫ f) = (J.comap e).si ≫ (e ≫ g) := by
  let _a0 := m57 e J.si
  have : IsClosedImmersion _a0 := inferInstance
  have hker : J.comap e = ker _a0 := rfl
  have hc := Limits.pullback.condition (f := e) (g := J.si)
  let _a2 := e ≫ f
  let _a3 := e ≫ g
  have key : _a0 ≫ _a2
      = _a0 ≫ _a3 := by
    let _a1 := m47 e J.si ≫ J.si
    calc _a0 ≫ _a2
        = (_a0 ≫ e) ≫ f := by rw [assoc]
      _ = _a1 ≫ f := by rw [hc]
      _ = m47 e J.si ≫ (J.si ≫ f) := by rw [assoc]
      _ = m47 e J.si ≫ (J.si ≫ g) := by rw [h]
      _ = _a1 ≫ g := by rw [assoc]
      _ = (_a0 ≫ e) ≫ g := by rw [hc]
      _ = _a0 ≫ _a3 := by rw [assoc]
  erw [hker, ← kerSubschemeIso_hom_comp _a0, assoc,
    assoc, key]

section
variable (hin : OrderReduction.OrderReductionHypotheses)
include hin
theorem le_center_of_center_support_subset (T : MarkedIdealWithBoundary) (s : T.SequenceOfBlowups)
    (i : ℕ) (hi : i < s.length) (J : (s.schemeAt i).IdealSheafData)
    (hJ : (((s.center i).support : CSet $ s.schemeAt i)) ⊆ ((J.support : CSet $ s.schemeAt i))) :
    J ≤ s.center i :=
  hin.smooth_center_radical T.base (s.schemeAt i) (s.projectionToBase i ≫ tMp T) (s.center i)
    (s.center_smooth i hi) J hJ

section
variable (P) (hPdown : ∀ a b : ℕ, a ≤ b → P b → P a) (A B) (hspec : IsBoundaryDivisorReduction P 0 A B) (T : MarkedIdealWithBoundary) (hV : IsAdmissible T) (hP : P T.krullDimSucc) (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) (hD : ∀ hft : LocallyOfFiniteType T.structMap, T.IsBalanced hft)
include hPdown hspec hV hP hO hD
theorem isAdmissible_and_isStrictPullbackBlowupSeq_of_etale
    (hlen : 0 < T.boundary.length)
    (V : Sch) (q : V ⟶ Sp T.base) (ps_ : V ⟶ scheme T)
    (hps_ : Etale ps_) (hq : QuasiCompact q)
    (hcomp : ps_ ≫ structMap T = q)
    (hcov : orderAtLeastLocus T.ideal T.mult ⊆ range ps_.base) :
    IsAdmissible (T.pbA q ps_) ∧
      IsStrictPullbackBlowupSeq ps_ (A $ T.pbA q ps_).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  let _c0 := T.pbA q ps_
  have := hV.charZero
  have hft : LocallyOfFiniteType T.structMap := hV.locallyOfFiniteType
  have : QuasiCompact T.structMap := hV.quasiCompact
  have : Smooth T.structMap := hV.smooth
  have : Etale ps_ := hps_
  have : QuasiCompact q := hq
  have : Smooth ps_ := inferInstance
  have := hV.isNoetherian
  have : IsLocallyNoetherian T.scheme := inferInstance
  have hVal : tAd _c0 := hin.valid_pullbackAlong T hV V q ps_ hcomp
  have hftq : LocallyOfFiniteType q := hVal.locallyOfFiniteType
  have hOT : T.IsOrderBoundedByMult := (T.isOrderBoundedByMult_iff).2 hO
  have hP' : P _c0.krullDimSucc := by
    exact hPdown _ _ (hin.schemeDim_le_of_etale V T.scheme ps_ hV.topologicalKrullDim_lt_top) hP
  have hO' : _c0.IsOrderBoundedByMult := by
    rw [isOrderBoundedByMult_iff]
    intro x
    exact le_of_eq_of_le (orderAt_comap T.base T.structMap ps_ T.ideal x) $ hO _
  have hderivBal : IsDerivBalanced T.base T.structMap T.ideal T.mult := hD hft
  have hDB' : IsDerivBalanced T.base q (T.ideal.comap ps_) T.mult :=
    hin.dBalanced_comap T hV V q ps_ hcomp hderivBal
  have hD' : ∀ hft2,
      _c0.IsBalanced hft2 := fun _ => hDB'
  have hj' : 0 < _c0.boundary.length := by
    rw [pullbackAlong_boundary]
    erw [length_map]
    exact hlen
  refine ⟨hVal, hin.isStrictPullbackSeq V T.scheme ps_ _ _ (hspec.isPullbackBlowupSequence_of_smooth T hV hP hOT (hD _) hlen V q ps_ hcomp hVal hP' hO' (hD' _) hj') ?_ ?_⟩
  intro i hi
  exact hspec.center_nonempty T hV hP hOT (hD _) hlen i hi
  intro i hi x hx
  exact hcov $ hin.center_mem_coSupport T hV (A T) i hi x hx

theorem isomorphic_withBoundary_cons_of_isMaxContactHypersurface
    (hMC : ∀ [LocallyOfFiniteType T.structMap],
      IsMaxContactInvariant T.base T.structMap T.ideal T.mult)
    (N : List T.scheme.IdealSheafData) (H1_ H2_ : T.scheme.IdealSheafData)
    (hbd : T.boundary = H1_ :: N)
    (hV2_ : (T.withBoundary (H2_ :: N)).IsAdmissible)
    (hH1 : ∀ [LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult H1_)
    (hH2_ : ∀ [LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult H2_) :
    (A T).toSequenceOfBlowups.Isomorphic (A $ T.withBoundary (H2_ :: N)).toSequenceOfBlowups := by
  have := hV.charZero
  have := hV.quasiCompact
  have := hV.smooth
  have hsnc1_ : InStrictNormalCrossingPosition T.structMap (H1_ :: N) := by
    rw [← hbd]
    exact hV.snc
  obtain ⟨V, ps1, ps2, hps1, hps2_, hqc, hftq, hcompeq, hcov1, hcov2, hidl, hHH, hNN, hmax⟩ :=
    hin.etaleEqualization T.base T.scheme T.structMap T.ideal T.mult hV.one_le_mult hMC hO
      N H1_ H2_ hsnc1_ hV2_.snc hH1 hH2_
  have := hps1
  have := hps2_
  let _a0 := ps1 ≫ T.structMap
  have := hqc
  obtain ⟨hVal1, hstr1⟩ :=
    isAdmissible_and_isStrictPullbackBlowupSeq_of_etale hin P hPdown A B hspec T hV hP hO hD
      (by simp [hbd]) V _a0 ps1 hps1 hqc rfl hcov1
  obtain ⟨hVal2, hstr2⟩ :=
    isAdmissible_and_isStrictPullbackBlowupSeq_of_etale hin P hPdown A B hspec (T.withBoundary (H2_ :: N)) hV2_
      (by rw [withBoundary_dim]; exact hP) hO hD
      (by rw [withBoundary_boundary]; exact zero_lt_succ _)
      V _a0 ps2 hps2_ hqc hcompeq.symm hcov2
  have := hVal1.smooth
  have := hftq
  have hbdy : m39 (fun D : tISD T => D.comap ps1) T.boundary
      = m39 (fun D : tISD T => D.comap ps2) (H2_ :: N) := by
    rw [hbd]
    simp only [map_cons]
    rw [hHH, hNN]
  have hTT : T.pbA _a0 ps1
      = (T.withBoundary (H2_ :: N)).pullbackAlong V _a0 ps2 := by
    show mk T.base V _a0 (T.ideal.comap ps1) T.mult
        (m39 (fun D : tISD T => D.comap ps1) T.boundary)
      = mk T.base V _a0 (T.ideal.comap ps2) T.mult
        (m39 (fun D : tISD T => D.comap ps2) (H2_ :: N))
    rw [hidl, hbdy]
  rw [← toSequenceOfBlowups_eq_of_heq _ _ hidl rfl hbdy $ congr_arg_heq A hTT] at hstr2
  obtain ⟨c, hc0, hcsucc, hcle⟩ :=
    hin.maxContactChain T.base V _a0 (T.ideal.comap ps1) T.mult hV.one_le_mult
      (m39 (fun D : tISD T => D.comap ps1) T.boundary)
      (A $ T.pbA _a0 ps1)
      (fun i hi => hin.isLocallyNoetherian_obj (T.pbA _a0 ps1) hVal1
        (A $ T.pbA _a0 ps1) i hi)
      (fun i hi J hJ => le_center_of_center_support_subset hin (T.pbA _a0 ps1)
        (A $ T.pbA _a0 ps1) i hi J hJ)
  refine isomorphic_of_isStrictPullback_same_source (A T).toSequenceOfBlowups
    (A $ T.withBoundary (H2_ :: N)).toSequenceOfBlowups hin.lifting hstr1 hstr2 ?_ ?_ ?_ ?_ c ?_ hcsucc hcle
  intro i hi x hx
  exact hcov1 $ hin.center_mem_coSupport T hV (A T) i hi x hx
  intro i hi x hx
  exact hcov2 $ hin.center_mem_coSupport (T.withBoundary (H2_ :: N)) hV2_
    (A $ T.withBoundary (H2_ :: N)) i hi x hx
  intro i hi J hJ
  exact le_center_of_center_support_subset hin T (A T) i hi J $ mpr_ coe_subset_coe hJ
  intro i hi J hJ
  exact le_center_of_center_support_subset hin (T.withBoundary (H2_ :: N)) (A $ T.withBoundary (H2_ :: N)) i hi J
    (mpr_ coe_subset_coe hJ)
  rw [hc0]
  exact subschemeio_comap_comp_comp_eq _ _ ps1 ps2 hmax
end
end

end DivisorReductionIndependence


structure MaxContactCoverProperties : Prop where
  strictTransform_admissible :
    ∀ (k : Type) [Field k] [CharZero k] {P P1 : Sch}
      (p : P ⟶ Sp k) [Smooth p]
      [LocallyOfFiniteType p]
      [IsLocallyNoetherian P1]
      (pi_ : P1 ⟶ P) [LocallyOfFiniteType (pi_ ≫ p)]
      (Z : ISD P) (E : Bdy P),
      HasStrictNormalCrossingsWith p Z E → IsBlowupAlongIdealSheaf pi_ Z →
      ∀ (A : ISD P) (A1_ : ISD P1) (mu_ : ℕ), 1 ≤ mu_ →
        (∀ x : ↥P, orderAt A x ≤ (mu_ : ENat)) →
        (support Z : Set ↥P) ⊆ orderAtLeastLocus A mu_ →
        exceptionalIdeal pi_ Z ^ mu_ * A1_ = comap A pi_ →
        ∀ H : ISD P, IsMaxContactHypersurface k p A mu_ H →
          IsMaxContactHypersurface k (pi_ ≫ p) A1_ mu_ (strictTransform pi_ Z H)
  coSupport_le_preimage :
    ∀ {X X1 : Sch} (pi_ : X1 ⟶ X) (Z : ISD X), IsBlowupAlongIdealSheaf pi_ Z →
      ∀ (A : ISD X) (A1_ : ISD X1) (mu_ : ℕ),
        exceptionalIdeal pi_ Z ^ mu_ * A1_ = comap A pi_ →
        (support Z : Set ↥X) ⊆ orderAtLeastLocus A mu_ →
        orderAtLeastLocus A1_ mu_ ⊆ (⇑pi_.base) ⁻¹' orderAtLeastLocus A mu_
  schemeDim_level_le :
    ∀ T : MarkedIdealWithBoundary, IsAdmissible T → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc
  exists_goodCover :
    ∀ (T : MarkedIdealWithBoundary) (hv : IsAdmissible T),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
      ∃ D : FiniteOpenCoverWithIdeals T,
        IsMaxContactCover T D hv.locallyOfFiniteType
          (MaxContactCoverData.balancedTunedIdeal T hv) (tunedMult T)
  hasSNCWith_cons :
    ∀ (k : Type) [Field k] {P : Sch} (p : P ⟶ Sp k)
      [Smooth p] (Z H : ISD P) (N : Bdy P),
      Smooth (subschemeι Z ≫ p) →
      InStrictNormalCrossingPosition p (H :: N) → HasStrictNormalCrossingsWith p Z N → H ≤ Z →
      HasStrictNormalCrossingsWith p Z (H :: N)
  valid_level :
    ∀ (T : MarkedIdealWithBoundary), IsAdmissible T → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      IsAdmissible (T.transformAt s i)
  orderAt_level_le :
    ∀ (T : MarkedIdealWithBoundary), IsAdmissible T →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
      ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
        ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (mult T : ENat)
  coverTriple_dim_le :
    ∀ (T : MarkedIdealWithBoundary) (hv : IsAdmissible T),
      krullDimSucc (MaxContactCoverData.cT hv).scheme ≤ T.krullDimSucc
  coverTriple_valid :
    ∀ (T : MarkedIdealWithBoundary) (hv : IsAdmissible T),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) →
      IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (tunedMult T) →
      IsAdmissible (MaxContactCoverData.cT hv)
  coverContact_admissible :
    ∀ (T : MarkedIdealWithBoundary) (hv : IsAdmissible T),
      IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (tunedMult T) →
      ∀ [LocallyOfFiniteType (MaxContactCoverData.cT hv).structMap],
        IsMaxContactHypersurface (MaxContactCoverData.cT hv).base
          (MaxContactCoverData.cT hv).structMap
          (MaxContactCoverData.cT hv).ideal (tunedMult T)
          (MaxContactCoverData.cI hv)
  coverContact_snc :
    ∀ (T : MarkedIdealWithBoundary) (hv : IsAdmissible T),
      IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (tunedMult T) →
      InStrictNormalCrossingPosition (MaxContactCoverData.cT hv).structMap
        [MaxContactCoverData.cI hv]
  tuning : TunedSheafProperties

theorem MaxContactCoverProperties.krullDimSucc_schemeAt_le_dim (hf : MaxContactCoverProperties) {S : MarkedIdealWithBoundary} (hv : IsAdmissible S)
    (s : S.mbs) i (hi : i ≤ s.length) :
    krullDimSucc (s.obj i) ≤ S.krullDimSucc :=
  hf.schemeDim_level_le S hv s.toMarkedSequenceOfBlowups i $ by simpa using hi

theorem MaxContactCoverProperties.derivedTriple_dim_le (hf : MaxContactCoverProperties) {T S : MarkedIdealWithBoundary} (hv : IsAdmissible S)
    (s : S.mbs)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
    extra keep (hdim : S.krullDimSucc ≤ T.krullDimSucc) :
    (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc :=
  le_trans (hf.krullDimSucc_schemeAt_le_dim hv s s.length le_rfl) hdim

theorem isMaxContactHypersurface_of_eq {k : Type} [Field k] {X : Sch}
    {p q : X ⟶ Sp k} [LocallyOfFiniteType p]
    [LocallyOfFiniteType q] (h : p = q) {A : ISD X} {m : ℕ}
    {H : ISD X} (hH : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface k q A m H := by
  subst h
  exact hH

section
variable (hf : MaxContactCoverProperties) {T : MarkedIdealWithBoundary}
include hf
theorem MaxContactCoverProperties.isMaxContactHypersurface_strictTransform_succ
    (hv : IsAdmissible T) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [LocallyOfFiniteType (s.projectionToSpec i)]
    [LocallyOfFiniteType (s.projectionToSpec (i + 1))]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hH : IsMaxContactHypersurface T.base (s.projectionToSpec i) (s.ideal i) T.mult H) :
    IsMaxContactHypersurface T.base (s.projectionToSpec (i + 1)) (s.ideal (i + 1)) T.mult
      (strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) H) := by
  have hi' := le_of_lt hi
  have : CharZero T.base := hv.charZero
  have : Smooth (s.projectionToSpec i) := (hf.valid_level T hv s i hi').smooth
  let _a0 := msAt s $ i + 1
  have hno : IsNoetherian _a0 := (hf.valid_level T hv s (i + 1) hi).isNoetherian
  have : IsLocallyNoetherian _a0 := inferInstance
  have : LocallyOfFiniteType
      (msTrS s i ≫ s.projectionToSpec i) := by
    rw [← projectionToSpec_succ]
    infer_instance
  have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec i) (msCtr s i) (s.boundary i) := by
    rw [projectionToSpec_eq]
    exact s.center_snc i hi
  have key := hf.strictTransform_admissible T.base (s.projectionToSpec i)
    (msTrS s i) (msCtr s i) (s.boundary i) hsnc
    (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) (s.ideal i) (s.ideal (i + 1)) T.mult
    hv.one_le_mult (hf.orderAt_level_le T hv hord s i hi') (s.center_order i hi)
    (s.ideal_succ i hi) H hH
  exact isMaxContactHypersurface_of_eq (projectionToSpec_succ s i).symm key

theorem MaxContactCoverProperties.hasStrictNormalCrossingsWith_cons_of_le_center
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [Smooth (s.projectionToSpec i)]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (N : List (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hsnc : InStrictNormalCrossingPosition (s.projectionToSpec i) (H :: N))
    (hZN : HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) N)
    (hHZ : H ≤ s.toSequenceOfBlowups.center i) :
    HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) (H :: N) := by
  refine hf.hasSNCWith_cons T.base (s.projectionToSpec i) (msCtr s i) H N ?_ hsnc hZN hHZ
  rw [projectionToSpec_eq]
  exact s.center_smooth i hi
end




section
variable (k : Type)
theorem isMaxContactHypersurface_of_eq_of_eq_of_eq [Field k] {P : Sch}
    {p p' : P ⟶ Sp k}
    [LocallyOfFiniteType p]
    [LocallyOfFiniteType p']
    {A A' H H' : ISD P} {mu_ : ℕ}
    (hp : p = p') (hA : A = A') (hH : H = H')
    (h : IsMaxContactHypersurface k p A mu_ H) :
    IsMaxContactHypersurface k p' A' mu_ H' :=by simp_all
theorem isMaxContactHypersurface_comap_iso [Field k] {X Y : Sch}
    (q : Y ⟶ Sp k) [Smooth q]
    [LocallyOfFiniteType q] (e : X ≅ Y)
    [LocallyOfFiniteType $ e.hom ≫ q]
    (A : ISD Y) (m : ℕ) (H : ISD Y)
    (h : IsMaxContactHypersurface k q A m H) :
    IsMaxContactHypersurface k (e.hom ≫ q) (A.comap e.hom) m $ H.comap e.hom := by
  have : Smooth e.hom := inferInstance
  have hmax : maxContactIdeal k (isoH e ≫ q) (cmI A e.hom) m
      = cmI (maxContactIdeal k q A m) e.hom := by
    rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate]
    exact derivIdealSheafIterate_comap k q e.hom (m - 1) A
  rw [isMaxContactHypersurface_iff] at h
  rw [isMaxContactHypersurface_iff]
  intro x
  obtain ⟨U, hU, hxU, hcase⟩ := h $ ihB_ e x
  refine ⟨(m54 $ ihB_ e).obj U, hU.preimage_of_isIso e.hom, hxU, ?_⟩
  rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hHU, hmc⟩
  left
  constructor
  have hd : Disjoint (e.hom.base ⁻¹' orderAtLeastLocus A m) $ e.hom.base ⁻¹' U :=
    hdisj.preimage _
  rwa [orderAtLeastLocus_comap_iso_hom_eq_preimage]
  rw [restrictIdeal_comap, htop]
  simp
  right
  refine ⟨n, EtaleChart.ofIso q e c, j, ?_, ?_⟩
  rw [restrictIdeal_comap, hHU, EtaleChart.ofIso_coordIdeal]
  rw [isMaxContactCoord_iff] at hmc
  rw [isMaxContactCoord_iff, EtaleChart.ofIso_coordIdeal, hmax, restrictIdeal_comap]
  exact comap_mono _ hmc

private theorem isMaxContactHypersurface_congr [instk : Field k] {P : Sch}
    {p p' : P ⟶ Sp k}
    (i1 : LocallyOfFiniteType p)
    (i2 : LocallyOfFiniteType p')
    {A A' H H' : ISD P} {mu_ : ℕ}
    (hp : p = p') (hA : A = A') (hH : H = H')
    (h : @IsMaxContactHypersurface k instk P p i1 A mu_ H) :
    @IsMaxContactHypersurface k instk P p' i2 A' mu_ H' :=by simp_all
end

theorem locallyOfFiniteType_of_smooth_morphism {X Y : Sch} {f : X ⟶ Y}
    (h : Smooth f) : LocallyOfFiniteType f := by
  infer_instance

theorem isMaxContactHypersurface_iteratedStrictTransform (hstar : MaxContactCoverProperties)
    (S : MarkedIdealWithBoundary) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ENat))
    (H : tISD S)
    (hH : @IsMaxContactHypersurface S.base _ S.scheme S.structMap hv.locallyOfFiniteType
      S.ideal S.mult H)
    (u : S.mbs)
    (t : ℕ) (ht : t ≤ u.length)
    [LocallyOfFiniteType (u.proj t ≫ S.structMap)] :
    IsMaxContactHypersurface S.base (u.proj t ≫ S.structMap) (u.ideal t) S.mult
      (MaxContactReduction.iteratedStrictTransform u H t) := by
  have hlft : ∀ i, i ≤ u.length →
      LocallyOfFiniteType (u.proj i ≫ tMp S) := by
    intro i hi
    have hsm :=
      smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hv u.toMarkedSequenceOfBlowups i
        (by rw [toMarkedSequence_length]; exact hi)
    rw [toMarkedSequence_projectionToSpec] at hsm
    exact locallyOfFiniteType_of_smooth_morphism hsm
  have key : ∀ i, i ≤ u.length →
      ∀ inst : LocallyOfFiniteType $ u.proj i ≫ tMp S,
        @IsMaxContactHypersurface S.base _ _ (u.proj i ≫ tMp S) inst
          (u.ideal i) S.mult $ p42 u H i := by
    intro i
    induction i with
    | zero =>
        intro _ inst
        have hiso : LocallyOfFiniteType $ u.isoZero.hom ≫ tMp S := by
          rwa [← u.proj_zero]
        refine isMaxContactHypersurface_congr S.base hiso inst ?_ (u.ideal_zero).symm
          (MaxContactReduction.iteratedStrictTransform_zero u H).symm
          (@isMaxContactHypersurface_comap_iso S.base _ _ _ S.structMap hv.smooth
            hv.locallyOfFiniteType u.isoZero hiso S.ideal S.mult H hH)
        rw [u.proj_zero]
    | succ j ih =>
        intro hj inst
        have hjl := hj
        have instj :=
          hlft j $ le_of_lt hjl
        have instsj : LocallyOfFiniteType $ u.toMarkedSequenceOfBlowups.projectionToSpec j := by
          rwa [toMarkedSequence_projectionToSpec]
        have instsj1 : LocallyOfFiniteType
            (u.toMarkedSequenceOfBlowups.projectionToSpec $ j + 1) := by
          rwa [toMarkedSequence_projectionToSpec]
        have hlt : j < u.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
          rwa [toMarkedSequence_length]
        let _a0 := p42 u H j
        have hadm := isMaxContactHypersurface_congr S.base instj instsj
          (toMarkedSequence_projectionToSpec u j).symm
          (toMarkedSequence_ideal u j).symm
          rfl
          (ih (le_of_lt hjl) instj)
        have hstep := @MaxContactCoverProperties.isMaxContactHypersurface_strictTransform_succ hstar S hv hord u.toMarkedSequenceOfBlowups
          j hlt instsj instsj1 _a0 hadm
        have hHeq : p6 (u.toMarkedSequenceOfBlowups.transitionMapSucc j) (u.toMarkedSequenceOfBlowups.center j)
            _a0 = p42 u H (j + 1) := by
          simp [toMarkedSequence_blowupMorphism, toMarkedSequence_center,
            MaxContactReduction.iteratedStrictTransform_succ]
          rfl
        exact isMaxContactHypersurface_congr S.base instsj1 inst
          (toMarkedSequence_projectionToSpec u $ j + 1)
          (toMarkedSequence_ideal u $ j + 1) hHeq hstep
  exact key t ht $ hlft t ht

theorem radical_le_of_isReduced_subscheme {X : Sch} (I : ISD X)
    (hred : IsReduced I.subscheme) : I.radical ≤ I := by
  have hker := q2 I
  refine le_trans ?_ $ le_of_eq hker
  refine mpr_ le_ofIdeals_iff ?_
  intro U
  rw [radical_ideal]
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have hR := AlgebraicGeometry.IsReduced.component_reduced
    (X := subS I) $ siI I ⁻¹ᵁ U.1
  refine RingHom.mem_ker.mpr $ hR.eq_zero _ ⟨n, ?_⟩
  rw [← map_pow]
  exact RingHom.mem_ker.mp $ (mp_ le_ofIdeals_iff $ le_of_eq hker.symm) U hn

theorem inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop (hstar : MaxContactCoverProperties)
    (S : MarkedIdealWithBoundary) (hv : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ENat))
    (H : tISD S)
    (hH : @IsMaxContactHypersurface S.base _ S.scheme S.structMap hv.locallyOfFiniteType
      S.ideal S.mult H)
    (u : S.mbs)
    (h0 : InStrictNormalCrossingPosition (u.proj 0 ≫ S.structMap) [MaxContactReduction.iteratedStrictTransform u H 0])
    (t : ℕ) (ht : t ≤ u.length) :
    InStrictNormalCrossingPosition (u.proj t ≫ S.structMap)
      (MaxContactReduction.iteratedStrictTransform u H t :: (u.boundary t).drop S.boundary.length) := by
  have hsmooth : ∀ i, i ≤ u.length →
      Smooth (u.proj i ≫ tMp S) := by
    intro i hi
    have hsm :=
      smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hv u.toMarkedSequenceOfBlowups i
        (by rw [toMarkedSequence_length]; exact hi)
    rwa [toMarkedSequence_projectionToSpec] at hsm
  have hkey : ∀ i, i < u.length →
      p42 u H i ≤ u.center i := by
    intro i hi
    have hsmi := hsmooth i $ le_of_lt hi
    have hcz := hv.charZero
    have hadm := isMaxContactHypersurface_iteratedStrictTransform hstar S hv hord H hH u i $ le_of_lt hi
    have hcos := hadm.orderAtLeastLocus_subset_support hv.one_le_mult
    have hsupp' : spI (u.center i) ≤ spI (p42 u H i) :=
      coe_subset_coe.mp (m90 (u.center_order i hi) hcos)
    have h1 : p42 u H i ≤
        vanishingIdeal (u.center i).support :=
      (gc _ _).mp hsupp'
    rw [vanishingIdeal_support] at h1
    have hsmZ := u.center_smooth i hi
    exact le_trans h1 $ radical_le_of_isReduced_subscheme (u.center i) (isReduced_of_smooth (siI (u.center i) ≫ (u.proj i ≫ tMp S)))
  revert ht
  induction t with
  | zero =>
      intro _
      have hb : (u.boundary 0).drop (bLen S) = [] := by
        rw [u.boundary_zero]
        simp
      rwa [hb]
  | succ j ih =>
      intro hj
      have hjl : j < u.length := hj
      have hjle : j ≤ u.length := le_of_lt hjl
      let _s0 := u.proj j ≫ tMp S
      have hsmj := hsmooth j hjle
      let _a2 := u.obj $ j + 1
      have hnoeth : IsNoetherian _a2 :=
        p25 effectiveCartierSupportContainsNoComponent hv u.toMarkedSequenceOfBlowups (j + 1)
          (by rw [toMarkedSequence_length]; exact hj)
      have hnsp : NoetherianSpace _a2 := inferInstance
      have hsncj : InStrictNormalCrossingPosition _s0
          (p42 u H j :: (u.boundary j).drop (bLen S)) := ih hjle
      let _a0 := (u.boundary j).drop (bLen S)
      have hZN : HasStrictNormalCrossingsWith _s0 (u.center j)
          _a0 := by
        have hfull := u.center_snc j hjl
        rw [← take_append_drop S.boundary.length (u.boundary j)] at hfull
        exact HasStrictNormalCrossingsWith.of_append hfull
      have hcons : HasStrictNormalCrossingsWith _s0 (u.center j)
          (p42 u H j :: (u.boundary j).drop (bLen S)) := by
        have hsm' : Smooth (u.toMarkedSequenceOfBlowups.projectionToSpec j) := by
          rwa [toMarkedSequence_projectionToSpec]
        have hlt : j < u.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length := by
          rwa [toMarkedSequence_length]
        have hsnc' : InStrictNormalCrossingPosition (u.toMarkedSequenceOfBlowups.projectionToSpec j)
            (p42 u H j :: (u.boundary j).drop (bLen S)) := by
          rwa [toMarkedSequence_projectionToSpec]
        have hZN' : HasStrictNormalCrossingsWith (u.toMarkedSequenceOfBlowups.projectionToSpec j) (u.toMarkedSequenceOfBlowups.center j)
            _a0 := by
          rwa [toMarkedSequence_projectionToSpec, toMarkedSequence_center]
        have hHZ' : p42 u H j ≤ u.toMarkedSequenceOfBlowups.center j := by simp_all
        have hres := @MaxContactCoverProperties.hasStrictNormalCrossingsWith_cons_of_le_center hstar S u.toMarkedSequenceOfBlowups j hlt hsm'
          (p42 u H j) _a0
          hsnc' hZN' hHZ'
        rwa [toMarkedSequence_projectionToSpec, toMarkedSequence_center] at hres
      have hbd :=
        u.boundary_succ_drop hjl S.boundary.length
          (by rw [u.boundary_length j hjle]; omega)
      rw [hbd, MaxContactReduction.iteratedStrictTransform_succ, u.proj_succ j, assoc]
      exact inStrictNormalCrossingPosition_strictTransform_cons_append _s0 (u.map j)
        (u.center j) (p42 u H j)
        _a0 (u.isBlowup j hjl) hsncj hcons




theorem orderAt_ideal_le_mult_along_sequence (T : MarkedIdealWithBoundary) (hT : IsAdmissible T)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) (s : T.SequenceOfBlowups) :
    ∀ i, i ≤ s.toSequenceOfBlowups.length →
      ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (mult T : ENat) := by
  have := hT.charZero
  intro i
  induction i with
  | zero =>
      intro _ x
      have : IsOpenImmersion s.toSequenceOfBlowups.isoZero.hom := inferInstance
      rw [s.ideal_zero, orderAt_comap_of_isOpenImmersion]
      exact hord _
  | succ k ih =>
      intro hk x
      have hlt := hk
      have hnoeth :=
        p25 effectiveCartierSupportContainsNoComponent hT s (k + 1) hk
      have : IsLocallyNoetherian $ msAt s $ k + 1 := inferInstance
      have hsmooth :=
        smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hT s k $ le_of_lt hlt
      have hS : HasStrictNormalCrossingsWith (s.projectionToSpec k) (msCtr s k) $ s.boundary k := by
        rw [projectionToSpec_eq]
        exact s.center_snc k hlt
      have hI :=
        le_pow_of_hasStrictNormalCrossingsWith (s.projectionToSpec k) (msCtr s k) (s.ideal k)
          (s.boundary k) hS T.mult $ s.center_order k hlt
      let _a0 := s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt
      have hEq :=
        eq_controlledTransform_of_mul_eq_comap (msTrS s k) (msCtr s k)
          (s.ideal k) T.mult _a0 hI
          (s.ideal $ k + 1) $ s.ideal_succ k hlt
      rw [hEq]
      exact orderAt_controlledTransform_le_of_forall_le T.base (s.projectionToSpec k)
        (msTrS s k) (msCtr s k) (s.boundary k) hS
        _a0 (s.ideal k) T.mult hI (ih $ le_of_lt hlt) x




theorem orderAtLeastLocus_comap_iso {X Y : Sch} (e : X ≅ Y) (J : ISD Y) (n : ℕ) :
    orderAtLeastLocus (comap J e.hom) n = ⇑e.hom ⁻¹' orderAtLeastLocus J n :=
  orderAtLeastLocus_comap_iso_hom_eq_preimage e J n

namespace BlowupSequenceData

section
variable {X : Sch} (d : BlowupSequenceData X)
def iteratedStrictTransform (i : ℕ) (D : ISD X) :
    (d.obj i).IdealSheafData :=
  Nat.rec (motive := fun j => (d.obj j).IdealSheafData) (comap D d.isoZero.hom)
    (fun j J => strictTransform (d.map j) (d.center j) J) i

@[simp] theorem iteratedStrictTransform_zero (D : ISD X) :
    d.iteratedStrictTransform 0 D = comap D d.isoZero.hom := rfl

@[simp] theorem iteratedStrictTransform_succ (i : ℕ)
    (D : ISD X) :
    d.iteratedStrictTransform (i + 1) D = strictTransform (d.map i) (d.center i) (d.iteratedStrictTransform i D) := rfl

theorem boundary_cons D
    L i :
    d.boundaryFrom (D :: L) i = d.iteratedStrictTransform i D :: d.boundaryFrom L i := by
  induction i with
  | zero => simp [boundary_zero]
  | succ i ih => simp [boundary_succ, ih]

theorem boundary_append
    (L1_ L2_ : Bdy X) i :
    d.boundaryFrom (L1_ ++ L2_) i = L1_.map (d.iteratedStrictTransform i) ++ d.boundaryFrom L2_ i := by
  induction L1_ with
  | nil => simp
  | cons D L ih => simp [BlowupSequenceData.boundary_cons, ih]
end

end BlowupSequenceData

namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

private theorem isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal {Y Y' : Sch} (pi_ : Y' ⟶ Y)
    (J : ISD Y) (h : IsBlowupAlongIdealSheaf pi_ J) : IsLocallyGeneratedByNonZeroDivisor $ exceptionalIdeal pi_ J := an1 h

section
variable (s : MarkedBlowupSequenceData p I m E)
theorem eq_of_exceptionalIdeal_pow_mul_eq :
    ∀ i < s.length, ∀ A B : (s.obj $ i + 1).IdealSheafData,
      exceptionalIdeal (s.map i) (s.center i) ^ m * A = (s.ideal i).comap (s.map i) →
      exceptionalIdeal (s.map i) (s.center i) ^ m * B = (s.ideal i).comap (s.map i) → A = B := by
  intro i hi A B hA hB
  exact ((isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (s.map i) (s.center i) $ s.isBlowup i hi).pow
    m).eq_of_mul_eq_mul $ tr_ hA hB.symm

section
variable (i) (hi : i ≤ s.length)
include hi
theorem controlledTransform_eq_ideal :
    s.controlledTransform I m i = s.ideal i :=
  (s.controlledTransform_and_boundary_eq_of_cancel (eq_of_exceptionalIdeal_pow_mul_eq s) i hi).1

theorem toBlowupSequenceData_boundary_eq :
    s.boundaryFrom E i = s.boundary i := by
  revert hi
  induction i with
  | zero =>
      intro _
      simp [s.boundary_zero]
  | succ j ih =>
      intro hi
      have hj := hi
      rw [p52, ih $ le_of_lt hj, s.boundary_succ j hj]
end
end

end MarkedBlowupSequenceData

theorem foldr_lcm_consecutive_ne_zero n :
    ∀ s, s ≠ 0 → foldr lcm 1 (range' s n) ≠ 0 := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
      intro s hs
      have hr : range' s (n + 1) 1 = s :: range' (s + 1) n 1 := rfl
      rw [hr, foldr_cons]
      exact lcm_ne_zero hs $ ih (s + 1) $ by omega

theorem one_le_tuningExponent (m : ℕ) : 1 ≤ tuningExponent m := by
  rcases m63 m 2 with h | h
  have h1 : m ≤ 1 := by omega
  exact le_of_eq (tuningExponent_of_le_one h1).symm
  have hl : lcmUpTo m ≠ 0 := by
    rw [lcmUpTo_eq_foldr]
    exact foldr_lcm_consecutive_ne_zero m 1 one_ne_zero
  have hm : m - 1 ≠ 0 := by omega
  have hne : tuningExponent m ≠ 0 := by
    rw [tuningExponent_of_two_le h]
    exact Nat.mul_ne_zero hm hl
  omega

namespace LowerDimReductionPullback

section
variable (S : MarkedIdealWithBoundary) (s : S.mbs) (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
def tunedIdealAtLength :
    (s.obj s.length).IdealSheafData :=
  haveI := hft
  balancedTunedSheaf S.base (s.proj s.length ≫ structMap S) (s.ideal s.length) S.mult

section
variable (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
abbrev TunedMarkedBlowupSeq : Type 1 :=
  MarkedSequenceOfBlowups (s.proj s.length ≫ structMap S) (tunedIdealAtLength S s hft) (tuningExponent S.mult)
    (extra ++ (s.boundary s.length).drop ndrop)


theorem structureMorphism_derivedTriple :
    structMap (MaxContactCoverData.derivedTriple S s hft extra ndrop) = s.proj s.length ≫ structMap S :=
  derivedTriple_structureMorphism S s hft extra ndrop

theorem ideal_derivedTriple :
    ideal (MaxContactCoverData.derivedTriple S s hft extra ndrop) = tunedIdealAtLength S s hft :=
  rfl
end

theorem tunedIdealAtLength_eq_balancedTunedSheaf :
    tunedIdealAtLength S s hft =
      haveI := hft
      balancedTunedSheaf S.base (lastP s ≫ tMp S) (lastI s) S.mult :=
  rfl
end

section
variable (hstar : MaxContactCoverProperties)
include hstar
section
variable (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
include hV
section
variable (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat)) (s : S.mbs)
include hO
theorem orderAt_ideal_length_le :
    ∀ x : ↥(s.obj s.length), orderAt (s.ideal s.length) x ≤ (mult S : ENat) := by
  have h := hstar.orderAt_level_le S hV hO s.toMarkedSequenceOfBlowups s.length
    (le_of_eq (toMarkedSequence_length s).symm)
  intro x
  exact h x

theorem maxOrderEq_ideal_length_of_nonempty
    (hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty) :
    MaxOrderEq (s.ideal s.length) S.mult :=
  ⟨(orderLE_iff _ _).2 $ orderAt_ideal_length_le hstar S hV hO s, hne⟩
end

theorem isOrderBoundedByMult_derivedTriple
    (hm : 1 ≤ mult S) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (s : S.mbs)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hVc : IsAdmissible (MaxContactCoverData.derivedTriple S s hft extra ndrop)) :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsOrderBoundedByMult := by
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  let _m0 := lastP s ≫ tMp S
  have hsm : Smooth _m0 := by
    have h := hVc.smooth
    rwa [derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI := hft
  let _a0 := tunedIdealAtLength S s hft
  have key : ∀ y : (lastO s),
      orderAt _a0 y ≤ ((tuningExponent S.mult) : ENat) := by
    by_cases hempty : orderAtLeastLocus (lastI s) S.mult = ∅
    have htuned : _a0 = ⊤ :=
      balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base _m0
        (lastI s) hm hempty
    intro y
    rw [htuned, orderAt_top]
    exact zero_le
    have hne :=
      nonempty_iff_ne_empty.mpr hempty
    have htune := hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE S.base (lastO s)
      _m0 (lastI s) S.mult hm (maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne)
      (tuningExponent S.mult) (one_le_tuningExponent S.mult)
    have heq : _a0 =
        tunedSheaf S.base _m0 (lastI s) S.mult
          (tuningExponent S.mult) :=
      balancedTunedSheaf_eq S.base _m0 (lastI s) S.mult
    intro y
    rw [heq]
    exact (orderLE_iff _ _).1 htune.2 y
  intro x
  rw [ideal_derivedTriple S s hft extra ndrop, derivedTriple_mult S s hft extra ndrop]
  exact key x
end

section
variable {k : Type} [Field k]
section
variable {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
theorem isMarked_append_of_orderAtLeastLocus_disjoint
    {L1_ L3} L2_ {d : BlowupSequenceData X}
    (hmk : d.IsMarked p I m (L1_ ++ L3))
    (hsep : ∀ D ∈ L2_, orderAtLeastLocus I m ∩ (D.support : Set ↥X) = ∅) :
    d.IsMarked p I m (L2_ ++ L3) := by
  refine ⟨hmk.divisible, hmk.center_order, hmk.center_smooth, ?_⟩
  intro i hi
  have h1 := hmk.center_snc i hi
  rw [BlowupSequenceData.boundary_append] at h1
  rw [BlowupSequenceData.boundary_append]
  refine HasStrictNormalCrossingsWith.append_of_support_disjoint (HasStrictNormalCrossingsWith.of_append h1) ?_
  intro D hD
  obtain ⟨D0, hD0, hDeq⟩ := mp_ mem_map hD
  subst hDeq
  have _i3 : ∀ i, i ≤ d.length → orderAtLeastLocus (d.controlledTransform I m i) m ∩ (spI (d.iteratedStrictTransform i D0) : CSet $ d.obj i) = ∅ := by
    let D := D0
    intro i
    induction i with
    | zero =>
        intro _
        have hsupp : (spI (cmI D $ bdIzH d) : CSet $ d.obj 0) =
            preimage d.isoZero.hom D.support := by simp_all
        rw [controlledTransform_zero, BlowupSequenceData.iteratedStrictTransform_zero, orderAtLeastLocus_comap_iso,
          hsupp, ← preimage_inter, hsep D0 hD0, preimage_empty]
    | succ i ih =>
        intro hi
        have hilt := hi
        apply eq_empty_of_subset_empty
        rintro x ⟨hx1, hx2⟩
        let _a0 := d.controlledTransform I m i
        have hsub := hstar.coSupport_le_preimage (d.map i) (d.center i) (d.isBlowup i hilt)
          _a0 (d.controlledTransform I m $ i + 1) m (pow_exceptionalIdeal_mul_controlledTransform_succ d I m i $ hmk.divisible i hilt) $ hmk.center_order i hilt
        rw [BlowupSequenceData.iteratedStrictTransform_succ] at hx2
        let _a1 := d.iteratedStrictTransform i D
        have hmem : (d.map i) x ∈
            orderAtLeastLocus _a0 m ∩ suppI _a1 :=
          ⟨hsub hx1,
            support_strictTransform_subset_preimage (d.map i) (d.center i) _a1 hx2⟩
        rw [ih $ le_of_lt hilt] at hmem
        simp at hmem
  apply eq_empty_of_subset_empty
  rintro x ⟨hx1, hx2⟩
  have hmem : x ∈ orderAtLeastLocus (d.controlledTransform I m i) m ∩
      (spI (d.iteratedStrictTransform i D0) : CSet $ d.obj i) := ⟨hmk.center_order i hi hx2, hx1⟩
  rw [_i3 i $ le_of_lt hi] at hmem
  simp at hmem
end

theorem isMarked_and_orderAtLeastLocus_eq_of_balancedTunedSheaf
    [CharZero k] [IsNoetherianRing k] {X : Sch} (p : X ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p]
    (I : ISD X) (m : ℕ) (hm : 1 ≤ m) (hmax : MaxOrderEq I m)
    (L1_ L2_ L3 E0 : Bdy X) (hE0_ : L2_ ++ L3 = E0)
    (hsep : ∀ D ∈ L2_, orderAtLeastLocus I m ∩ (support D : Set ↥X) = ∅)
    (t : MarkedSequenceOfBlowups p (balancedTunedSheaf k p I m) (tuningExponent m) (L1_ ++ L3)) :
    ∃ _hmk : (ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked p I m E0,
      ∀ i ≤ t.toSequenceOfBlowups.length,
        orderAtLeastLocus ((ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform I m i) m =
          orderAtLeastLocus (t.ideal i) (tuningExponent m) := by
  subst hE0_
  have hmarkedIff := hstar.tuning.isMarked_tuned_iff k X p I m hm hmax (L1_ ++ L3)
    (ofSequenceOfBlowups t.toSequenceOfBlowups)
  have hmkI := hmarkedIff.1.mpr $ (ofMarkedSequence t).isMarked_toBlowupSequenceData
  refine ⟨isMarked_append_of_orderAtLeastLocus_disjoint hstar L2_ hmkI hsep, ?_⟩
  intro i hi
  have h3 :=
    toBlowupSequenceData_controlledTransform_eq (ofMarkedSequence t) i
      (by rw [ofMarkedSequence_length]; exact hi)
  exact st_ (hmarkedIff.2.1 hmkI i (by rw [ofSequenceOfBlowups_length]; exact hi)) $ congrArg (fun Z => orderAtLeastLocus Z $ tuningExponent m) h3
end
end

section
variable {k : Type} [Field k] {X : Sch}
theorem isMarked_of_length_eq_zero
    (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
    (E : Bdy X) (d : BlowupSequenceData X) (hd : d.length = 0) :
    d.IsMarked p I m E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro i hi
  all_goals rw [hd] at hi
  all_goals exact absurd hi $ not_lt_zero i

theorem orderAtLeastLocus_controlledTransform_eq_of_length_eq_zero
    {p : X ⟶ Sp k} {J : ISD X} {n : ℕ}
    {E : Bdy X} (t : MarkedSequenceOfBlowups p J n E)
    (I : ISD X) (m n' : ℕ) (hlen : t.toSequenceOfBlowups.length = 0)
    (hempty : orderAtLeastLocus I m = ∅) (hJ : J = ⊤) (hn1 : 1 ≤ n') :
    ∀ i ≤ t.toSequenceOfBlowups.length,
      orderAtLeastLocus ((ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform I m i) m =
        orderAtLeastLocus (t.ideal i) n' := by
  have hJempty : orderAtLeastLocus J n' = ∅ := by
    rw [hJ]
    exact orderAtLeastLocus_top_eq_empty n' hn1
  intro i hi
  rw [hlen, le_zero] at hi
  subst hi
  have h1 : orderAtLeastLocus ((ofSequenceOfBlowups t.toSequenceOfBlowups).controlledTransform I m 0) m = ∅ := by
    rw [controlledTransform_zero, orderAtLeastLocus_comap_iso, hempty, preimage_empty]
  have h2 : orderAtLeastLocus (t.ideal 0) n' = ∅ := by
    rw [t.ideal_zero, orderAtLeastLocus_comap_iso, hJempty, preimage_empty]
  exact tr_ h1 h2.symm
end

theorem idealSheafData_top_pow {X : Sch} n :
    (⊤ : ISD X) ^ n = ⊤ := by
  have h1 : (1 : ISD X) = ⊤ := by simp
  rw [← h1, one_pow]

section
variable (hstar : MaxContactCoverProperties)
include hstar
theorem isBalanced_derivedTriple (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
    (hm : 1 ≤ mult S) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (s : S.mbs)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hVc : IsAdmissible (MaxContactCoverData.derivedTriple S s hft extra ndrop)) :
    (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsBalanced hVc.locallyOfFiniteType := by
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  let _a0 := lastP s ≫ tMp S
  have hsm : Smooth _a0 := by
    have h := hVc.smooth
    rwa [derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI := hft
  let _a1 := tunedIdealAtLength S s hft
  have key : IsDerivBalanced S.base _a0 _a1
      (tuningExponent S.mult) := by
    rcases m63 S.mult 2 with hlt | hge
    have h1 : tuningExponent S.mult = 1 := tuningExponent_of_le_one $ by omega
    rw [h1]
    exact isDerivBalanced_one S.base _a0 _a1
    rcases eq_empty_or_nonempty (orderAtLeastLocus (lastI s) S.mult) with hempty | hne
    have htop : _a1 = ⊤ :=
      balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base _a0
        (lastI s) hm hempty
    rw [htop]
    refine isDerivBalanced_of_pow_le S.base _a0 ?_
    intro i _
    rw [idealSheafData_top_pow]
    exact le_top
    have hmax :=
      maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne
    have hexp := tuningExponent_of_two_le hge
    have hderivPow := hstar.tuning.derivIdealSheafIter_tunedSheaf_pow_le
    unfold IsDerivBalancedTunedSheafMulLcm at hderivPow
    have hderivPowAt := hderivPow S.base (lastO s) _a0
      (lastI s) S.mult hm hmax (tMu S - 1) le_rfl
    have hset : _a1 =
        tunedSheaf S.base _a0 (lastI s) S.mult
          ((tMu S - 1) * lcmUpTo S.mult) := by
      rw [← hexp]
      exact balancedTunedSheaf_eq S.base _a0 (lastI s) S.mult
    refine isDerivBalanced_of_pow_le S.base _a0 ?_
    intro i hi
    rw [hexp] at hi
    rw [hset, hexp]
    exact hderivPowAt i hi
  exact key

theorem length_eq_zero_of_orderAtLeastLocus_eq_empty (P : ℕ → Prop) (j : ℕ)
    (A B : PrincipalizationAssignment) (hspec : IsBoundaryDivisorReduction P j A B)
    (S : MarkedIdealWithBoundary) (hV : IsAdmissible S) (hm : 1 ≤ mult S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (s : S.mbs)
    (hft : LocallyOfFiniteType $ s.proj s.length ≫ structMap S)
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hP : P (MaxContactCoverData.derivedTriple S s hft extra ndrop).krullDimSucc)
    (hVc : IsAdmissible $ MaxContactCoverData.derivedTriple S s hft extra ndrop)
    (hj : j < length (extra ++ (s.boundary s.length).drop ndrop))
    (hempty : orderAtLeastLocus (s.ideal s.length) S.mult = ∅) :
    (A $ MaxContactCoverData.derivedTriple S s hft extra ndrop).toSequenceOfBlowups.length = 0 := by
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  let _a1 := lastP s ≫ tMp S
  have hsm : Smooth _a1 := by
    have h := hVc.smooth
    rwa [derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI := hft
  have htuned :=
    balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base _a1
      (lastI s) hm hempty
  have hjb := hj
  rw [← p48 S s hft extra ndrop] at hjb
  have h1 : ideal (p8 S s hft extra ndrop) = ⊤ := by
    rwa [ideal_derivedTriple S s hft extra ndrop]
  refine hspec.trivial_of_coSupport_empty _ hVc hP
    (isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hft extra ndrop hVc)
    (isBalanced_derivedTriple hstar S hV hm hO s hft extra ndrop hVc) hjb ?_
  rw [h1, derivedTriple_mult S s hft extra ndrop]
  exact orderAtLeastLocus_top_eq_empty _ $ one_le_tuningExponent S.mult

theorem appendLowerDimReduction_eq_append (hinv : ComapIsoInvariance)
    (T : MarkedIdealWithBoundary) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment)
    (B : PrincipalizationAssignment) (j : ℕ) (hspec : IsBoundaryDivisorReduction P j (A j) B)
    (reduce : (S' : MarkedIdealWithBoundary) → S'.krullDimSucc ≤ T.krullDimSucc → ℕ → S'.SequenceOfBlowups)
    (hrc : ∀ S' h i, reduce S' h i = A i S')
    (S : MarkedIdealWithBoundary) (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ENat))
    (s : S.mbs)
    (extra : List (s.obj s.length).IdealSheafData) (ndrop : ℕ)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (hdim : (MaxContactCoverData.derivedTriple S s hft extra ndrop).krullDimSucc ≤ T.krullDimSucc)
    (hP : P (MaxContactCoverData.derivedTriple S s hft extra ndrop).krullDimSucc)
    (hVc : (MaxContactCoverData.derivedTriple S s hft extra ndrop).IsAdmissible)
    (hj : j < (extra ++ (s.boundary s.length).drop ndrop).length)
    (hsep : ∀ D ∈ (s.boundary s.length).take ndrop,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (D.support : CSet (s.obj s.length)) = ∅) :
    ∃ hmk :
        (ofSequenceOfBlowups
            (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).IsMarked
          (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult (s.boundary s.length),
      appendLowerDimReduction hinv T reduce S s extra ndrop j =
          s.append
            ((ofSequenceOfBlowups
                (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).toMarkedBlowupSequenceData
              (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
              (s.boundary s.length) hmk) hinv ∧
        ∀ i ≤ (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups.length,
          orderAtLeastLocus
              ((ofSequenceOfBlowups
                  (A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).toSequenceOfBlowups).controlledTransform
                (s.ideal s.length) S.mult i) S.mult =
            orderAtLeastLocus ((A j (MaxContactCoverData.derivedTriple S s hft extra ndrop)).ideal i)
              (tuningExponent S.mult) := by
  let _a0 := lastP s ≫ tMp S
  let _c0 := p8 S s hft extra ndrop
  have happend : appendLowerDimReduction hinv T reduce S s extra ndrop j =
      concatOfIsMarked hinv s
        (ofSequenceOfBlowups (A j _c0).toSequenceOfBlowups) := by
    rw [appendLowerDimReduction_eq_concatOfIsMarked hinv T reduce S s extra ndrop j hft hdim,
      hrc _c0 hdim j]
  have := hV.charZero
  have : IsNoetherianRing S.base := inferInstance
  have hsm : Smooth _a0 := by
    have h := hVc.smooth
    rwa [derivedTriple_structureMorphism S s hft extra ndrop] at h
  have hftI := hft
  by_cases hempty : orderAtLeastLocus (lastI s) S.mult = ∅
  have hlen :=
    length_eq_zero_of_orderAtLeastLocus_eq_empty hstar P j (A j) B hspec S hV hm hO s hft extra ndrop hP hVc hj hempty
  have hJtop : _c0.ideal = ⊤ := by
    rw [ideal_derivedTriple S s hft extra ndrop]
    exact balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty S.base _a0
      (lastI s) hm hempty
  have hmk :=
    isMarked_of_length_eq_zero _a0 (s.ideal s.length)
      S.mult (s.boundary s.length) _ (tr_ (ofSequenceOfBlowups_length _) hlen)
  exact ⟨hmk, tr_ happend $ concatOfIsMarked_eq_append_of_isMarked hinv s _ hmk,
    orderAtLeastLocus_controlledTransform_eq_of_length_eq_zero
      (A j _c0)
      (lastI s) S.mult (tuningExponent S.mult) hlen hempty hJtop
      (one_le_tuningExponent S.mult)⟩
  have hne :=
    nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hmk, hcos⟩ := isMarked_and_orderAtLeastLocus_eq_of_balancedTunedSheaf hstar _a0
    (lastI s) S.mult hm (maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne) extra ((lastB s).take ndrop)
    ((lastB s).drop ndrop) (lastB s)
    (take_append_drop ndrop (lastB s)) hsep
    (A j _c0)
  exact ⟨hmk, tr_ happend $ concatOfIsMarked_eq_append_of_isMarked hinv s _ hmk, hcos⟩
end

end LowerDimReductionPullback





namespace BlowupSequenceData

section
variable {X : Sch} (d : BlowupSequenceData X)
theorem boundary_eq_map_iteratedStrictTransform_append
    (L : Bdy X) (i : ℕ) :
    d.boundaryFrom L i = L.map (d.iteratedStrictTransform i) ++ d.boundaryFrom ([] : Bdy X) i := by
  have h := d.boundary_append L ([]) i
  rwa [append_nil] at h

theorem support_iteratedStrictTransform_subset_of_strictTransform_mono
    (D : ISD X)
    (K : ∀ t : ℕ, (d.obj t).IdealSheafData) (h0 : K 0 = comap D d.isoZero.hom)
    (hstep : ∀ t, t < length d →
      K (t + 1) = strictTransform (d.map t) (d.center t) (K t) ∨
        K (t + 1) = comap (K t) (d.map t))
    (hsupp : ∀ i, i < length d → ∀ (A B : (d.obj i).IdealSheafData),
      ((support A : CSet $ d.obj i) ⊆ (support B : CSet $ d.obj i)) →
      (support (strictTransform (d.map i) (d.center i) A) : Set ↥(d.obj $ i + 1)) ⊆
        (support (strictTransform (d.map i) (d.center i) B) : Set ↥(d.obj $ i + 1)))
    (t : ℕ) (ht : t ≤ length d) :
    (support (d.iteratedStrictTransform t D) : CSet $ d.obj t) ⊆ (support (K t) : CSet $ d.obj t) := by
  have key : ∀ s, s ≤ length d →
      (spI (d.iteratedStrictTransform s D) : CSet $ d.obj s) ⊆ (spI (K s) : CSet $ d.obj s) := by
    intro s
    induction s with
    | zero =>
        intro _ x hx
        have hz : K 0 = d.iteratedStrictTransform 0 D := by rw [h0, iteratedStrictTransform_zero]
        rwa [hz]
    | succ n ih =>
        intro hn
        have hlt := hn
        have hle := ih $ m49 hlt
        rcases hstep n hlt with hh | hh
        simp_all
        rw [hh, iteratedStrictTransform_succ]
        intro y hy
        have h1 := support_strictTransform_subset_preimage (d.map n) (d.center n)
          (d.iteratedStrictTransform n D) hy
        have h2 := hle h1
        exact (one_le_orderAt_iff_mem_support (cmI (K n) $ d.map n) y).1
          (le_trans ((one_le_orderAt_iff_mem_support (K n) _).2 h2)
            (orderAt_le_orderAt_comap (d.map n) (K n) y))
  exact key t ht

theorem support_iteratedStrictTransform_subset_support
    (hN : ∀ i ≤ length d, IsLocallyNoetherian $ d.obj i)
    (D : ISD X) (K : ∀ t : ℕ, (d.obj t).IdealSheafData)
    (h0 : K 0 = comap D d.isoZero.hom)
    (hstep : ∀ t, t < length d →
      K (t + 1) = strictTransform (d.map t) (d.center t) (K t) ∨
        K (t + 1) = comap (K t) (d.map t))
    (t : ℕ) (ht : t ≤ length d) :
    (support (d.iteratedStrictTransform t D) : CSet $ d.obj t) ⊆ (support (K t) : CSet $ d.obj t) := by
  refine support_iteratedStrictTransform_subset_of_strictTransform_mono d D K h0 hstep ?_ t ht
  intro i hi A B hAB
  have := hN (i + 1) hi
  have := quasiCompact_strictTransformio_of_isLocallyNoetherian (d.map i) (d.center i) A
  have := quasiCompact_strictTransformio_of_isLocallyNoetherian (d.map i) (d.center i) B
  rw [support_strictTransform_eq_closure_preimage, support_strictTransform_eq_closure_preimage]
  exact closure_mono $ sdiff_subset_sdiff_left $ preimage_mono hAB
end

end BlowupSequenceData

namespace BoundarySeparationByMaxContact

section
variable {X : Sch}
theorem stalkIdeal_prod_eq_top (x : ↥X) :
    ∀ L : Bdy X, (∀ I ∈ L, stalkIdeal I x = ⊤) → stalkIdeal L.prod x = ⊤ := by
  intro L
  induction L with
  | nil =>
      intro _
      have h0 := stalkIdeal_pow (⊤) 0 x
      rw [pow_zero, pow_zero] at h0
      rw [prod_nil, h0, m217]
  | cons I L ih =>
      intro h
      rw [prod_cons, stalkIdeal_mul, h I $ by simp,
        ih fun J hJ => h J $ by simp [hJ]]
      simp

theorem prod_map_range_succ_eq_apply_zero (f : ℕ → ISD X)
    (hf : ∀ j, j ≠ 0 → f j = 1) (n : ℕ) :
    (List.map f $ List.range $ n + 1).prod = f 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [range_succ, map_append, prod_append, ih]
      simp [hf (m + 1) $ succ_ne_zero m]

theorem support_pow_subset_support (A : ISD X) e :
    ((A ^ e).support : Set ↥X) ⊆ (A.support : Set ↥X) := by
  intro x hx
  refine (mem_support_iff_stalkIdeal_ne_top A x).2 ?_
  intro htop
  exact ((mem_support_iff_stalkIdeal_ne_top (A ^ e) x).1 hx) $ by rw [stalkIdeal_pow, htop, ← m217, one_pow]
end

section
variable (hstar : MaxContactCoverProperties) (S : MarkedIdealWithBoundary) (hV : IsAdmissible S) (s : S.mbs) (i) (hi : i ≤ s.length)
include hstar hV hi
theorem locallyOfFiniteType_projectionToBase_comp :
    LocallyOfFiniteType (s.proj i ≫ structMap S) := by
  have h := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups i hi).locallyOfFiniteType
  simp at h
  with_unfolding_all exact h

theorem smooth_projectionToBase_comp :
    Smooth (s.proj i ≫ structMap S) := by
  have h := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups i hi).smooth
  simp at h
  with_unfolding_all exact h
end

section
variable (k : Type) [Field k] [CharZero k] {P : Sch} (p) [Smooth p] [LocallyOfFiniteType p] (A : ISD P)
theorem maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty (m : ℕ) (hm : 1 ≤ m)
    (hempty : orderAtLeastLocus A m = ∅) : maxContactIdeal k p A m = ⊤ := by
  have hlt : m - 1 < m := by omega
  have h := orderAtLeastLocus_derivIdealSheafIterate k p A (r := m - 1) (m := m) hlt
  rw [show m - (m - 1) = 1 from by omega, hempty] at h
  refine (eq_top_iff_support_eq_empty _).2 ?_
  ext y
  simp [mem_empty_iff_false, iff_false]
  intro hy
  have hy' : y ∈ orderAtLeastLocus (derivIdealSheafIterate k p (m - 1) A) 1 := by
    refine (mem_orderAtLeastLocus_one_iff _ y).2 ?_
    rwa [← maxContactIdeal_eq_derivIdealSheafIterate]
  rwa [h] at hy'

section
variable (mu_ : ℕ)
theorem prod_derivIdealSheafIter_pow_le_balancedTunedSheaf (c : ℕ → ℕ)
    (hc : tuningExponent mu_ ≤ ∑ j ∈ Finset.range mu_, (mu_ - j) * c j) :
    (List.map (fun j => derivIdealSheafIterate k p j A ^ c j) $ List.range mu_).prod ≤
      balancedTunedSheaf k p A mu_ := by
  unfold balancedTunedSheaf tunedSheaf
  exact le_iSup
    (fun d : {e : ℕ → ℕ // tuningExponent mu_ ≤ ∑ j ∈ m65 mu_, (mu_ - j) * e j} =>
      (m39 (fun j => derivIdealSheafIterate k p j A ^ d.1 j) $ m127 mu_).prod) ⟨c, hc⟩

theorem pow_tuningExponent_le_balancedTunedSheaf (hmu_ : 1 ≤ mu_) :
    A ^ tuningExponent mu_ ≤ balancedTunedSheaf k p A mu_ := by
  obtain ⟨n, rfl⟩ : ∃ n, mu_ = n + 1 := ⟨mu_ - 1, by omega⟩
  have hd0 : derivIdealSheafIterate k p 0 A = A := rfl
  let _a0 := tuningExponent $ n + 1
  let _a1 := n + 1
  have hsum : (∑ j ∈ m65 (n + 1),
      (_a1 - j) * (if j = 0 then _a0 else 0)) = _a1 * _a0 := by
    rw [Finset.sum_eq_single 0]
    simp
    simp_all
    simp_all
  have hc : _a0 ≤ ∑ j ∈ m65 (n + 1),
      (_a1 - j) * (if j = 0 then _a0 else 0) := by
    rw [hsum]
    calc _a0 = 1 * _a0 := sy_ (one_mul _)
      _ ≤ _a1 * _a0 :=
          mul_le_mul (succ_le_succ $ m67 n) $ le_refl _
  have hle := prod_derivIdealSheafIter_pow_le_balancedTunedSheaf k p A (n + 1)
    (if · = 0 then _a0 else 0) hc
  have hf : ∀ j, j ≠ 0 →
      derivIdealSheafIterate k p j A ^ (if j = 0 then _a0 else 0) = 1 := by simp_all
  have hA : A ^ _a0 ≤
      (m39 (fun j => derivIdealSheafIterate k p j A ^ (if j = 0 then _a0 else 0))
        (m127 $ n + 1)).prod := by
    rw [prod_map_range_succ_eq_apply_zero
      (fun j => derivIdealSheafIterate k p j A ^ (if j = 0 then _a0 else 0)) hf n]
    simp [hd0]
  exact le_trans hA hle
end
end

theorem isMaxContactHypersurface_balancedTunedSheaf (hstar : MaxContactCoverProperties) (k : Type) [Field k] [CharZero k]
    {P : Sch} (p : P ⟶ Sp k) [Smooth p]
    [LocallyOfFiniteType p] (A : ISD P) (mu_ : ℕ) (hmu_ : 1 ≤ mu_)
    (hord : ∀ x : ↥P, orderAt A x ≤ (mu_ : ENat)) (H : ISD P)
    (hH : IsMaxContactHypersurface k p A mu_ H) :
    IsMaxContactHypersurface k p (balancedTunedSheaf k p A mu_) (tuningExponent mu_) H := by
  let _a0 := balancedTunedSheaf k p A mu_
  by_cases hne : (orderAtLeastLocus A mu_).Nonempty
  have hmax : MaxOrderEq A mu_ := ⟨(orderLE_iff A mu_).2 hord, hne⟩
  have hcs : orderAtLeastLocus _a0 (tuningExponent mu_) = orderAtLeastLocus A mu_ :=
    (hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE k P p A mu_ hmu_ hmax (tuningExponent mu_)
      (one_le_tuningExponent mu_)).1
  have hmi : maxContactIdeal k p _a0 (tuningExponent mu_) = maxContactIdeal k p A mu_ :=
    hstar.tuning.derivIdealSheafIter_pred_tunedSheaf k P p A mu_ hmu_ hmax (tuningExponent mu_)
      (one_le_tuningExponent mu_)
  intro x
  obtain ⟨U, hUaff, hxU, hcase⟩ := hH x
  refine ⟨U, hUaff, hxU, ?_⟩
  rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmcc⟩
  refine inl ⟨?_, htop⟩
  rwa [hcs]
  refine inr ⟨n, c, j, hcoord, ?_⟩
  intro i
  rw [hmi]
  exact hmcc i
  rw [not_nonempty_iff_eq_empty] at hne
  have hcs : orderAtLeastLocus _a0 (tuningExponent mu_) = ∅ := by
    have hstalk : ∀ y, stalkIdeal (derivIdealSheafIterate k p (mu_ - 1) A) y = ⊤ := by
      intro y
      rw [← maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty k p A mu_ hmu_ hne]
      exact stalkIdeal_top y
    have hsum : (∑ j ∈ m65 mu_, (mu_ - j) * (if j = mu_ - 1 then tuningExponent mu_ else 0))
        = tuningExponent mu_ := by
      rw [Finset.sum_eq_single $ mu_ - 1]
      simp [show mu_ - (mu_ - 1) = 1 from by omega]
      intro b _ hb
      simp [hb]
      simp_all
    ext x
    simp only [mem_empty_iff_false, iff_false]
    intro hx
    have hprod : stalkIdeal (m39
        (fun j => derivIdealSheafIterate k p j A ^ (if j = mu_ - 1 then tuningExponent mu_ else 0))
        (m127 mu_)).prod x = ⊤ := by
      refine stalkIdeal_prod_eq_top x _ ?_
      intro I hI
      obtain ⟨j, _, rfl⟩ := mp_ mem_map hI
      simp only [stalkIdeal_pow]
      split_ifs with hjj
      simp_all
      simp_all
    have hmono := stalkIdeal_mono (prod_derivIdealSheafIter_pow_le_balancedTunedSheaf k p A mu_ (if · = mu_ - 1 then tuningExponent mu_ else 0) $ le_of_eq hsum.symm) x
    rw [hprod] at hmono
    have htop := mp_ top_le_iff hmono
    exact ((mem_support_iff_stalkIdeal_ne_top _ x).1 $ (mem_orderAtLeastLocus_one_iff _ x).1 $ orderAtLeastLocus_subset_of_le _a0 (one_le_tuningExponent mu_) hx) htop
  intro x
  obtain ⟨U, hUaff, hxU, hcase⟩ := hH x
  refine ⟨U, hUaff, hxU, ?_⟩
  rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmcc⟩
  refine inl ⟨?_, htop⟩
  rw [hcs]
  exact Set.disjoint_left.2 fun y hy => (mp_ (mem_empty_iff_false y) hy).elim
  refine inr ⟨n, c, j, hcoord, ?_⟩
  intro i
  rw [maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty k p _a0 (tuningExponent mu_) (one_le_tuningExponent mu_) hcs, ← maxContactIdeal_eq_top_of_orderAtLeastLocus_eq_empty k p A mu_ hmu_ hne]
  exact hmcc i

theorem isAdmissible_derivedTriple (hstar : MaxContactCoverProperties) (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
    (s : S.mbs)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hsnc : InStrictNormalCrossingPosition (s.proj s.length ≫ structMap S)
      (extra ++ (s.boundary s.length).drop keep)) :
    IsAdmissible (MaxContactCoverData.derivedTriple S s hft extra keep) := by
  let _a0 := smooth_projectionToBase_comp hstar S hV s s.length $ le_refl s.length
  have hlev := hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length $ le_refl s.length
  constructor
  case charZero => exact hV.charZero
  case locallyOfFiniteType =>
    rwa [derivedTriple_structureMorphism]
  case one_le_mult =>
    rw [derivedTriple_mult]
    exact one_le_tuningExponent S.mult
  case quasiCompact =>
    have h := hlev.quasiCompact
    rw [derivedTriple_structureMorphism]
    simp at h
    with_unfolding_all exact h
  case smooth =>
    rwa [derivedTriple_structureMorphism]
  case snc =>
    rwa [derivedTriple_structureMorphism, p48]
  case nonzeroOnComponents =>
    have hsupp : (spI (LowerDimReductionPullback.tunedIdealAtLength S s hft) : CSet $ lastO s) ⊆
        (spI (lastI s) : CSet $ lastO s) := by
      have := hV.charZero
      let _a1 := lastP s ≫ tMp S
      have :=
        _a0
      have := hft
      have hpow := pow_tuningExponent_le_balancedTunedSheaf S.base _a1
        (lastI s) S.mult hV.one_le_mult
      exact m90 (support_antitone hpow)
        (support_pow_subset_support (lastI s) $ tuningExponent S.mult)
    rw [LowerDimReductionPullback.ideal_derivedTriple]
    unfold NonzeroOnComponents
    intro T hT hsub
    exact hlev.nonzeroOnComponents T hT $ m90 hsub hsupp

theorem inStrictNormalCrossingPosition_iteratedStrictTransform_zero (S : MarkedIdealWithBoundary)
    (u : S.mbs) (H : tISD S)
    (hH : InStrictNormalCrossingPosition S.structMap [H]) :
    InStrictNormalCrossingPosition (u.proj 0 ≫ structMap S) [MaxContactReduction.iteratedStrictTransform u H 0] := by
  have h := inStrictNormalCrossingPosition_comap_iso S.structMap u.isoZero [H] hH
  rwa [MaxContactReduction.iteratedStrictTransform_zero u H, u.proj_zero]

abbrev continuationMarkedData (S : MarkedIdealWithBoundary)
    (s : S.mbs)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (u : LowerDimReductionPullback.TunedMarkedBlowupSeq S s hft extra keep)
    (hmk : (ofSequenceOfBlowups u.toSequenceOfBlowups).IsMarked (s.proj s.length ≫ structMap S)
      (s.ideal s.length) S.mult (s.boundary s.length)) :
    MarkedBlowupSequenceData (s.proj s.length ≫ structMap S) (s.ideal s.length) S.mult
      (s.boundary s.length) :=
  (ofSequenceOfBlowups u.toSequenceOfBlowups).toMarkedBlowupSequenceData (s.proj s.length ≫ structMap S)
    (s.ideal s.length) S.mult (s.boundary s.length) hmk

section
variable (hstar : MaxContactCoverProperties) (P) (T : MarkedIdealWithBoundary) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
include hstar
theorem isAdmissible_coverTriple :
    IsAdmissible (MaxContactCoverData.cT h.valid) :=
  hstar.coverTriple_valid T h.valid h.orderLE
    (isMaxContactCover_chosenCoverData T h.valid
      (hstar.exists_goodCover T h.valid h.orderLE))

theorem orderAt_coverTriple_ideal_le_mult :
    ∀ x : ↥(MaxContactCoverData.cT h.valid).scheme,
      orderAt (MaxContactCoverData.cT h.valid).ideal x ≤
        (mult (MaxContactCoverData.cT h.valid) : ENat) := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have := h.valid.charZero
  have H := hstar.tuning.coSupport_tunedSheaf_eq_and_orderLE T.base T.scheme T.structMap T.ideal
    T.mult h.valid.one_le_mult ⟨(orderLE_iff T.ideal T.mult).2 h.orderLE, h.coSupport_nonempty⟩ (tuningExponent T.mult) $ one_le_tuningExponent T.mult
  intro x
  exact (orderAt_comap T.base T.structMap (p12 T h.valid)
    (p29 T h.valid) x).trans_le $ an2 H _

theorem isMaxContactHypersurface_coverMaxContactIdeal :
    @IsMaxContactHypersurface (MaxContactCoverData.cT h.valid).base _
      (MaxContactCoverData.cT h.valid).scheme
      (MaxContactCoverData.cT h.valid).structMap
      (isAdmissible_coverTriple hstar P T h).locallyOfFiniteType
      (MaxContactCoverData.cT h.valid).ideal
      (MaxContactCoverData.cT h.valid).mult
      (MaxContactCoverData.cI h.valid) := by
  have hft :=
    (isAdmissible_coverTriple hstar P T h).locallyOfFiniteType
  have key := hstar.coverContact_admissible T h.valid
    (isMaxContactCover_chosenCoverData T h.valid
      (hstar.exists_goodCover T h.valid h.orderLE))
  rwa [MaxContactCoverData.coverTriple_mult]

theorem inStrictNormalCrossingPosition_coverMaxContactIdeal :
    InStrictNormalCrossingPosition (MaxContactCoverData.cT h.valid).structMap
      [MaxContactCoverData.cI h.valid] :=
  hstar.coverContact_snc T h.valid
    (isMaxContactCover_chosenCoverData T h.valid
      (hstar.exists_goodCover T h.valid h.orderLE))
end

theorem isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt (_hMaxContact : MaxContactCoverProperties) (S : MarkedIdealWithBoundary)
    (_hV : IsAdmissible S) (s : S.mbs)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hVc : IsAdmissible (MaxContactCoverData.derivedTriple S s hft extra keep))
    (u : LowerDimReductionPullback.TunedMarkedBlowupSeq S s hft extra keep) (i : ℕ) (hi : i ≤ u.length) :
    IsLocallyNoetherian ((ofSequenceOfBlowups u.toSequenceOfBlowups).obj i) := by
  have hN :=
    p25 effectiveCartierSupportContainsNoComponent hVc u i hi
  exact inferInstanceAs $ IsLocallyNoetherian $ msAt u i

theorem iteratedStrictTransform_eq_toBlowupSequenceData {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedBlowupSequenceData p I m E) (H : ISD X) (i : ℕ) :
    MaxContactReduction.iteratedStrictTransform s H i = s.toBlowupSequenceData.iteratedStrictTransform i H := by
  induction i with
  | zero =>
      rewrite [MaxContactReduction.iteratedStrictTransform_zero, BlowupSequenceData.iteratedStrictTransform_zero]
      rfl
  | succ n ih =>
      rewrite [MaxContactReduction.iteratedStrictTransform_succ, BlowupSequenceData.iteratedStrictTransform_succ, ih]
      rfl

end BoundarySeparationByMaxContact





namespace BoundarySeparationByMaxContact

def BoundarySeparated (S : MarkedIdealWithBoundary)
    (s : S.mbs) (n : ℕ) : Prop :=
  ∀ (i : ℕ), i < n → ∀ hi : i < length (s.boundary s.length),
    orderAtLeastLocus (s.ideal s.length) S.mult ∩
        ((support (get (s.boundary s.length) ⟨i, hi⟩) : CSet $ s.obj s.length)) = ∅

def SeparateBoundaryInvariant (S : MarkedIdealWithBoundary) (H : tISD S)
    (s : S.mbs) (n : ℕ) : Prop :=
  BoundarySeparated S s n ∧ (∀ i < s.length, s.center i ≠ ⊤) ∧
    InStrictNormalCrossingPosition (s.proj 0 ≫ S.structMap) [MaxContactReduction.iteratedStrictTransform s H 0]

section
variable {X Y : Sch} (hinv : ComapIsoInvariance)
include hinv
section
variable (e : X ≅ Y) (I D : ISD Y) (m : ℕ)
theorem orderAtLeastLocus_comap_iso_inter_support_eq_empty
    (h : orderAtLeastLocus I m ∩ (support D : Set ↥Y) = ∅) :
    orderAtLeastLocus (comap I e.hom) m ∩ (support (comap D e.hom) : Set ↥X) = ∅ := by
  ext x
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨hx1, hx2⟩
  rw [hinv.coSupport_comap e I m] at hx1
  have hmem : ihB_ e x ∈ orderAtLeastLocus I m ∩ spI D := ⟨hx1, mem_support_comap.1 hx2⟩
  rwa [h] at hmem

theorem orderAtLeastLocus_inter_support_eq_empty_of_comap_iso
    (h : orderAtLeastLocus (comap I e.hom) m ∩ (support (comap D e.hom) : Set ↥X) = ∅) :
    orderAtLeastLocus I m ∩ (support D : Set ↥Y) = ∅ := by
  ext y
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨hy1, hy2⟩
  have h2 : isoH e (isoI e y) = y := by simp
  have k1 : ibM e y ∈ orderAtLeastLocus (cmI I e.hom) m := by
    rw [hinv.coSupport_comap e I m]
    show ihB_ e (ibM e y) ∈ orderAtLeastLocus I m
    rwa [show ihB_ e (ibM e y) = y from h2]
  have k2 : ibM e y ∈ (spI (cmI D e.hom) : Set X) := by
    refine mem_support_comap.2 ?_
    rwa [show ihB_ e (ibM e y) = y from h2]
  have hmem : ibM e y ∈
      orderAtLeastLocus (cmI I e.hom) m ∩ (spI (cmI D e.hom) : Set X) := ⟨k1, k2⟩
  rwa [h] at hmem
end

theorem orderAtLeastLocus_comap_eqToHom_inter_support_eq_empty
    (h : X = Y) (I D : ISD Y) (m : ℕ)
    (hsep : orderAtLeastLocus I m ∩ (support D : Set ↥Y) = ∅) :
    orderAtLeastLocus (comap I $ eqToHom h) m ∩ (support (comap D $ eqToHom h) : Set ↥X) = ∅ :=
  orderAtLeastLocus_comap_iso_inter_support_eq_empty hinv (eqToIso h) I D m hsep
end

theorem orderAtLeastLocus_append_succ_subset_preimage (hstar : MaxContactCoverProperties) {k : Type} [Field k]
    {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance) (r : ℕ) (hr : r < (s.append t hinv).length) :
    orderAtLeastLocus ((s.append t hinv).ideal (r + 1)) m ⊆
      ⇑((s.append t hinv).map r) ⁻¹' orderAtLeastLocus ((s.append t hinv).ideal r) m := by
  have hlen := append_length s t hinv
  have hrlen : r < (s.appendToBlowupSequenceData t).length := by simp_all
  let _a0 := s.append t hinv
  exact hstar.coSupport_le_preimage (_a0.map r) (_a0.center r) (_a0.isBlowup r hr)
    (_a0.ideal r) (_a0.ideal $ r + 1) m (exceptionalIdeal_pow_mul_appendIdeal_succ s t hinv r hrlen) $ center_support_subset_orderAtLeastLocus_appendIdeal s t hinv r hrlen

section
variable (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) (hinv : ComapIsoInvariance) (A : ℕ → PrincipalizationAssignment)
abbrev separateBoundarySeq (j : ℕ) :
    MarkedBlowupSequenceData (MaxContactCoverData.cT hv).structMap
      (MaxContactCoverData.cT hv).ideal (MaxContactCoverData.cT hv).mult
      (MaxContactCoverData.cT hv).boundary :=
  separateBoundary hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
    (MaxContactCoverData.cT hv) j

abbrev separateAllBoundary :
    MarkedBlowupSequenceData (MaxContactCoverData.cT hv).structMap
      (MaxContactCoverData.cT hv).ideal (MaxContactCoverData.cT hv).mult
      (MaxContactCoverData.cT hv).boundary :=
  separateBoundarySeq T hv hinv A (MaxContactCoverData.cT hv).boundary.length

abbrev reduceAlongHypersurfaceTriple
    (hft : LocallyOfFiniteType
      ((separateAllBoundary T hv hinv A).proj (separateAllBoundary T hv hinv A).length ≫
        structMap (MaxContactCoverData.cT hv))) : MarkedIdealWithBoundary :=
  MaxContactCoverData.derivedTriple (MaxContactCoverData.cT hv) (separateAllBoundary T hv hinv A) hft
    [strictTransformAtLength (separateAllBoundary T hv hinv A) $ MaxContactCoverData.cI hv]
    (MaxContactCoverData.cT hv).boundary.length
end

section
variable {al_ be_ : Type} (f : al_ → be_)
theorem getElem_map_of_lt :
    ∀ (L : List al_) (n : ℕ) (hn : n < length L) (hn' : n < length (L.map f)),
      (L.map f)[n]'hn' = f (L[n]'hn) :=by simp_all
theorem getElem_map_append_of_lt :
    ∀ (L : List al_) (R : List be_) (n : ℕ) (hn : n < length L)
      (hn' : n < length (L.map f ++ R)), (L.map f ++ R)[n]'hn' = f (L[n]'hn) :=by simp_all
end

theorem ne_top_of_support_nonempty {X : Sch} {J : ISD X}
    (h : ((support J : Set ↥X)).Nonempty) : J ≠ ⊤ := by
  intro hc
  obtain ⟨x, hx⟩ := h
  rw [hc] at hx
  have h1 :=
    (one_le_orderAt_iff_mem_support (⊤) x).2 hx
  rw [orderAt_top] at h1
  exact absurd h1 $ by simp

theorem orderAtLeastLocus_inter_support_eq_empty_of_eq {X : Sch} {I I' D D' : ISD X}
    {m : ℕ} (hI : I = I') (hD : D = D')
    (h : orderAtLeastLocus I' m ∩ (support D' : Set ↥X) = ∅) :
    orderAtLeastLocus I m ∩ (support D : Set ↥X) = ∅ :=by simp_all
section
variable {X Y : Sch}
theorem comap_hom_ne_top_of_ne_top (e : X ≅ Y) (J : ISD Y)
    (hJ : J ≠ ⊤) : comap J e.hom ≠ ⊤ := by
  have hs : J.supp.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hc
    exact hJ $ (eq_top_iff_support_eq_empty J).2 hc
  obtain ⟨y, hy⟩ := hs
  have h2 : isoH e (isoI e y) = y := by simp
  have h3 := hy
  rw [← show ihB_ e (ibM e y) = y from h2] at h3
  exact ne_top_of_support_nonempty ⟨ibM e y, mem_support_comap.2 h3⟩

private theorem comap_eqToHom_ne_top (h : X = Y)
    (J : ISD Y) (hJ : J ≠ ⊤) : comap J (eqToHom h) ≠ ⊤ :=
  comap_hom_ne_top_of_ne_top (eqToIso h) J hJ
end

theorem getElem_eq_of_list_eq {al_ : Type} {L L' : List al_} (h : L = L') (n : ℕ)
    (hn : n < length L) (hn' : n < length L') : L[n]'hn = L'[n]'hn' := by
  subst h
  rfl

theorem forall_mem_take_of_forall_lt {al_ : Type} (Q : al_ → Prop) :
    ∀ (L : List al_) (n : ℕ),
      (∀ i : ℕ, i < n → ∀ hi : i < length L, Q (L.lget i hi)) → ∀ a ∈ L.take n, Q a := by
  intro L
  induction L with
  | nil =>
      intro n _ a ha
      simp at ha
  | cons b L ih =>
      intro n hQ a ha
      cases n with
      | zero => simp at ha
      | succ m =>
          have ha' := ha
          rcases mem_cons.mp ha' with rfl | ha''
          exact hQ 0 (succ_pos m) $ by simp
          exact ih m
            (fun i him hi => hQ (i + 1) (succ_lt_succ him) $ succ_lt_succ hi) a ha''

theorem boundary_getElem_eq_iteratedStrictTransform {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (u : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ u.length) (n : ℕ) (hn : n < E.length)
    (hn' : n < (u.boundary i).length) :
    (u.boundary i)[n]'hn' = u.iteratedStrictTransform i (E[n]'hn) := by
  let _a0 := u.boundaryFrom ([]) i
  have h1 : u.boundary i = E.map (u.iteratedStrictTransform i) ++ _a0 := by
    rw [← MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq u i hi]
    exact BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append u.toBlowupSequenceData E i
  have h2 := hn'
  rw [h1] at h2
  rw [getElem_eq_of_list_eq h1 n hn' h2]
  exact getElem_map_append_of_lt (u.iteratedStrictTransform i) E
    _a0 n hn h2

section
variable (hstar : MaxContactCoverProperties) (hinv : ComapIsoInvariance)
include hstar
theorem separateBoundaryInvariant_append
    (S : MarkedIdealWithBoundary) (H : tISD S) (hH : InStrictNormalCrossingPosition S.structMap [H])
    (s : S.mbs)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult
      (s.boundary s.length))
    (j : ℕ) (hj : j < S.boundary.length) (hbj : j < (s.boundary s.length).length)
    (hfacts : SeparateBoundaryInvariant S H s j)
    (hN : ∀ i, i ≤ t.length → IsLocallyNoetherian (t.obj i))
    (K : ∀ r : ℕ, (t.obj r).IdealSheafData)
    (h0 : K 0 = ((s.boundary s.length)[j]'hbj).comap t.isoZero.hom)
    (hstep : ∀ r, r < t.length →
      K (r + 1) = strictTransform (t.map r) (t.center r) (K r) ∨
        K (r + 1) = (K r).comap (t.map r))
    (hsepK : ∀ r, r = t.length →
      orderAtLeastLocus (t.ideal r) S.mult ∩ ((K r).support : CSet (t.obj r)) = ∅)
    (hcent : ∀ r, r < t.length → t.center r ≠ ⊤) :
    SeparateBoundaryInvariant S H (s.append t hinv) (j + 1) := by
  have hsub : ∀ r, r ≤ t.length →
      (spI (t.iteratedStrictTransform r ((lastB s)[j]'hbj)) : CSet (t.obj r)) ⊆
        (spI (K r) : CSet (t.obj r)) := by
    intro r hr
    exact BlowupSequenceData.support_iteratedStrictTransform_subset_support t.toBlowupSequenceData hN
      ((lastB s)[j]'hbj) K h0 hstep r hr
  have hsepT : ∀ r, r ≤ t.length →
      orderAtLeastLocus (t.ideal r) S.mult ∩ (spI (K r) : CSet (t.obj r)) = ∅ →
      orderAtLeastLocus (t.ideal r) S.mult ∩
        (spI (t.iteratedStrictTransform r ((lastB s)[j]'hbj)) : CSet (t.obj r)) = ∅ := by
    intro r hr hsep
    ext x
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨hx1, hx2⟩
    have hmem : x ∈ orderAtLeastLocus (t.ideal r) S.mult ∩ (spI (K r) : CSet (t.obj r)) :=
      ⟨hx1, hsub r hr hx2⟩
    rwa [hsep] at hmem
  have hulen :=
    append_length s t hinv
  have hsle : s.length ≤ (s.append t hinv).length := by omega
  have hdesc :=
    fun r hr => orderAtLeastLocus_append_succ_subset_preimage hstar s t hinv r hr
  have hblenU :=
    fun r hr => boundary_length (s.append t hinv) r hr
  have hobj0 :=
    appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.length)
  have hid0 : (s.append t hinv).ideal s.length = cmI (lastI s) (eqToHom hobj0) := by
    rw [append_ideal s t hinv s.length,
      appendIdeal_of_le_length s t (le_refl s.length)]
  have hbd0 : (s.append t hinv).boundary s.length
      = (lastB s).map (cmI · $ eqToHom hobj0) := by
    rw [append_boundary s t hinv s.length,
      appendBoundary_of_le_length s t (le_refl s.length)]
  have hstep0 : ∀ i (hiS : i < (lastB s).length)
      (hiU : i < ((s.append t hinv).boundary s.length).length),
      orderAtLeastLocus (lastI s) S.mult ∩
          (spI ((lastB s)[i]'hiS) : CSet (lastO s)) = ∅ →
        orderAtLeastLocus ((s.append t hinv).ideal s.length) S.mult ∩
          (spI (((s.append t hinv).boundary s.length)[i]'hiU) :
            Set ((s.append t hinv).obj s.length)) = ∅ := by
    intro i hiS hiU hsep
    have himap : i < ((lastB s).map
        (cmI · $ eqToHom hobj0)).length := by simpa using hiS
    have hbeli :=
      (getElem_eq_of_list_eq hbd0 i hiU himap).trans
        (getElem_map_of_lt
          (fun D : (lastO s).IdealSheafData => cmI D $ eqToHom hobj0)
          (lastB s) i hiS himap)
    exact orderAtLeastLocus_inter_support_eq_empty_of_eq hid0 hbeli
      (orderAtLeastLocus_comap_eqToHom_inter_support_eq_empty hinv hobj0 (lastI s)
        ((lastB s)[i]'hiS) S.mult hsep)
  have hmid : ∀ (hjU : j < ((s.append t hinv).boundary (s.length + t.length)).length),
      orderAtLeastLocus ((s.append t hinv).ideal (s.length + t.length)) S.mult ∩
        (spI (((s.append t hinv).boundary (s.length + t.length))[j]'hjU) :
          Set ((s.append t hinv).obj (s.length + t.length))) = ∅ := by
    intro hjU
    rcases m73 t.length with hz | hpos
    have hI0 := t.ideal_zero
    have hjun : orderAtLeastLocus (lastI s) S.mult ∩
        (spI ((lastB s)[j]'hbj) : CSet (lastO s)) = ∅ := by
      refine orderAtLeastLocus_inter_support_eq_empty_of_comap_iso hinv t.isoZero (lastI s)
        ((lastB s)[j]'hbj) S.mult ?_
      have h1 := hsepT 0 (m67 _) $ hsepK 0 hz.symm
      rw [BlowupSequenceData.iteratedStrictTransform_zero] at h1
      exact orderAtLeastLocus_inter_support_eq_empty_of_eq hI0.symm rfl h1
    refine (s.append t hinv).orderAtLeastLocus_disjoint_boundary_of_le hdesc hj hsle
      (hstep0 j hbj ?_ hjun) (s.length + t.length) (le_add_right _ _)
      (le_of_eq hulen.symm)
    have h := hblenU s.length hsle
    omega
    have hobjT :=
      appendToBlowupSequenceData_schemeAt_length_add_length s t hpos
    have hidT :=
      append_ideal_length_add_length s t hinv hpos
    have hbdT :=
      append_boundary_length_add_length s t hinv hpos
    have hjtt : j < (lastB t).length := by simp_all
    have hjmapT : j < ((lastB t).map
        (cmI · $ eqToHom hobjT)).length := by simpa using hjtt
    have hbelT :=
      (getElem_eq_of_list_eq hbdT j hjU hjmapT).trans
        (getElem_map_of_lt
          (fun D : (lastO t).IdealSheafData => cmI D $ eqToHom hobjT)
          (lastB t) j hjtt hjmapT)
    have hbel :=
      boundary_getElem_eq_iteratedStrictTransform t t.length (le_refl t.length) j hbj hjtt
    refine orderAtLeastLocus_inter_support_eq_empty_of_eq hidT hbelT ?_
    exact orderAtLeastLocus_comap_eqToHom_inter_support_eq_empty hinv hobjT (lastI t)
      ((lastB t)[j]'hjtt) S.mult (orderAtLeastLocus_inter_support_eq_empty_of_eq rfl hbel (hsepT t.length (le_refl t.length) (hsepK t.length rfl)))
  have htop : ∀ hjU,
      orderAtLeastLocus ((s.append t hinv).ideal ((s.append t hinv).length)) S.mult ∩
        (spI (((s.append t hinv).boundary ((s.append t hinv).length))[j]'hjU) :
          Set ((s.append t hinv).obj ((s.append t hinv).length))) = ∅ := by
    intro hjU
    refine (s.append t hinv).orderAtLeastLocus_disjoint_boundary_of_le hdesc hj (le_of_eq hulen.symm)
      (hmid ?_) ((s.append t hinv).length) (le_of_eq hulen.symm) (le_refl _)
    have h := hblenU (s.length + t.length) $ le_of_eq hulen.symm
    omega
  refine ⟨?_, ?_, inStrictNormalCrossingPosition_iteratedStrictTransform_zero S (s.append t hinv) H hH⟩
  intro i hi hii
  simp only [get_eq_getElem]
  rcases m63 i j with hij | hij
  have hiE := lt_trans hij hj
  have hiU0 : i < ((s.append t hinv).boundary s.length).length := by
    have h := hblenU s.length hsle
    omega
  have hiS : i < (s.boundary s.length).length := by
    have h := boundary_length s s.length $ le_refl s.length
    omega
  refine (s.append t hinv).orderAtLeastLocus_disjoint_boundary_of_le hdesc hiE hsle
    (hstep0 i hiS hiU0 ?_) ((s.append t hinv).length) hsle (le_refl _)
  have h := hfacts.1 i hij hiS
  simp only [get_eq_getElem] at h
  exact h
  have hije : i = j := by omega
  subst hije
  exact htop hii
  intro r hr
  rw [append_toBlowupSequenceData]
  rcases lt_trichotomy r s.length with h | h | h
  rw [appendToBlowupSequenceData_center_of_lt_length s t h]
  exact comap_eqToHom_ne_top _ _ $ hfacts.2.1 r h
  subst h
  rw [appendToBlowupSequenceData_center_length s t]
  refine comap_eqToHom_ne_top _ _
    (comap_hom_ne_top_of_ne_top t.isoZero.symm (t.center 0) (hcent 0 ?_))
  omega
  rw [appendToBlowupSequenceData_center_of_length_lt s t h]
  refine comap_eqToHom_ne_top _ _ $ hcent (r - s.length) ?_
  omega

section
variable (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (T : MarkedIdealWithBoundary)
include hmono hspec
theorem separateBoundaryInvariant_appendLowerDimReduction (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ENat)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : tISD S) (hH : InStrictNormalCrossingPosition S.structMap [H])
    (s : S.mbs)
    (j : ℕ) (hj : j < S.boundary.length) (hfacts : SeparateBoundaryInvariant S H s j) :
    SeparateBoundaryInvariant S H
      (appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T) S s [] 0 j) (j + 1) := by
  classical
  have hft :=
    locallyOfFiniteType_projectionToBase_comp hstar S hV s s.length $ le_refl s.length
  have hm := hV.one_le_mult
  have hbj : j < (s.boundary s.length).length := by
    have h := boundary_length s s.length $ le_refl s.length
    omega
  have hsncAll : InStrictNormalCrossingPosition (s.proj s.length ≫ tMp S) $ s.boundary s.length := by
    have h := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length $ le_refl s.length).snc
    simp at h
    with_unfolding_all exact h
  have hsnc0 : InStrictNormalCrossingPosition (s.proj s.length ≫ tMp S)
      (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0) := by
    simpa using hsncAll
  have hVc :=
    isAdmissible_derivedTriple hstar S hV s hft [] 0 hsnc0
  have hdimC : tDim (p8 S s hft [] 0) ≤ tDim T := by
    refine le_trans ?_ hdimS
    with_unfolding_all exact hstar.schemeDim_level_le S hV s.toMarkedSequenceOfBlowups s.length $ le_refl s.length
  have hPC := hmono _ _ hdimC hPdimT
  have hordBound := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  have hbalanced := LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hft [] 0 hVc
  have hbdC : (p8 S s hft [] 0).boundary = s.boundary s.length := by
    rw [p48]
    simp
  have hjC' := hbj
  rw [← hbdC] at hjC'
  have hjC : j < (([] : List (s.obj s.length).IdealSheafData)
      ++ (s.boundary s.length).drop 0).length := by simpa using hbj
  have hsepC : ∀ D ∈ (s.boundary s.length).take 0,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ D.supp = ∅ := by simp_all
  obtain ⟨hmk, hceq, hcos⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B j (hspec j)
    (p49 A T) (fun _ _ _ => rfl) S hV hm hO s [] 0 hft hdimC hPC hVc
    hjC hsepC
  obtain ⟨Dv, bv, _, hC2, _, hC4, hC5, hC6, _⟩ :=
    (hspec j).shape (p8 S s hft [] 0) hVc hPC hordBound hbalanced hjC'
  have hget : ((p8 S s hft [] 0).bget j hjC')
      = (s.boundary s.length)[j]'hbj := by simp_all
  rw [hceq]
  refine separateBoundaryInvariant_append hstar hinv S H hH s _ j hj hbj hfacts ?_ Dv ?_ ?_ ?_ ?_
  intro i hi
  exact isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar S hV s hft [] 0 hVc
    (A j $ p8 S s hft [] 0) i hi
  rw [hC2, hget]
  with_unfolding_all rfl
  intro r hr
  by_cases hb : bv = true ∧ r = 0
  obtain ⟨hb1, hb2⟩ := hb
  subst hb2
  exact inr (hC4 hb1).2.2
  exact inl $ hC5 r hr hb
  intro r hrr
  have hrr' := hrr
  subst hrr'
  ext x
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨hx1, hx2⟩
  let _s0 := (A j $ p8 S s hft [] 0).length
  have hx1' : x ∈ orderAtLeastLocus
      ((ofSequenceOfBlowups (A j $ p8 S s hft [] 0).toSequenceOfBlowups).controlledTransform
        (s.ideal s.length) S.mult _s0)
      S.mult := hx1
  rw [hcos _s0 $ le_refl _] at hx1'
  have hmem : x ∈ orderAtLeastLocus
      (lastIdeal $ A j $ p8 S s hft [] 0)
      (p8 S s hft [] 0).mult ∩
      ((spI $ Dv _s0) :
        Set $ (A j $ p8 S s hft [] 0).schemeAt
          _s0) := ⟨hx1', hx2⟩
  rwa [hC6] at hmem
  intro r hr htop
  exact ((hspec j).center_nonempty (p8 S s hft [] 0) hVc hPC hordBound hbalanced
    hjC' r hr).ne_empty
    ((eq_top_iff_support_eq_empty _).1 htop)

theorem separateBoundaryInvariant_separateBoundarySeq (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    (j : ℕ) (hj : j ≤ (MaxContactCoverData.cT h.valid).boundary.length) :
    SeparateBoundaryInvariant (MaxContactCoverData.cT h.valid)
      (MaxContactCoverData.cI h.valid) (separateBoundarySeq T h.valid hinv A j) j := by
  let _a0 := p49 A T
  let _a2 := inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h
  let _a4 := p31 h.valid
  let _c0 := p7 h.valid
  revert hj
  induction j with
  | zero =>
      intro _
      have h0 : separateBoundarySeq T h.valid hinv A 0
          = _c0.embs :=
        MaxContactCoverData.separateBoundary_zero hinv T _a0
          _c0
      refine m157 ?_ (m157 ?_ (inStrictNormalCrossingPosition_iteratedStrictTransform_zero _c0 (separateBoundarySeq T h.valid hinv A 0) _a4 _a2))
      intro i hi
      exact absurd hi $ not_lt_zero i
      rw [h0]
      intro i hi
      exact absurd hi $ not_lt_zero i
  | succ n ih =>
      intro hj
      let _a1 := separateBoundarySeq T h.valid hinv A n
      have hsucc : separateBoundarySeq T h.valid hinv A (n + 1)
          = appendLowerDimReduction hinv T _a0
              _c0 _a1 [] 0 n :=
        separateBoundary_succ hinv T _a0
          _c0 n
      rw [hsucc]
      exact separateBoundaryInvariant_appendLowerDimReduction hstar hinv P hmono A B hspec T h.dim_prop
        _c0 (isAdmissible_coverTriple hstar P T h)
        (orderAt_coverTriple_ideal_le_mult hstar P T h) (hstar.coverTriple_dim_le T h.valid)
        _a4 _a2
        _a1 n hj (ih $ le_of_succ_le hj)

theorem exists_cover_eq_separateAllBoundary_append (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∃ hft : LocallyOfFiniteType
        ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
          (MaxContactCoverData.cT h.valid).structMap),
      ∃ _hV : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).IsAdmissible,
        P (reduceAlongHypersurfaceTriple T h.valid hinv A hft).krullDimSucc ∧
        ∃ hmk : (ofSequenceOfBlowups
            (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).IsMarked
            ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
              (MaxContactCoverData.cT h.valid).structMap)
            ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
            (MaxContactCoverData.cT h.valid).mult
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length),
          MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T) =
              (separateAllBoundary T h.valid hinv A).append
                (continuationMarkedData (MaxContactCoverData.cT h.valid)
                  (separateAllBoundary T h.valid hinv A)
                  hft
                  [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
                    (MaxContactCoverData.cI h.valid)]
                  (MaxContactCoverData.cT h.valid).boundary.length
                  (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) hinv ∧
            ∀ i ≤ (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups.length,
              orderAtLeastLocus
                  ((ofSequenceOfBlowups
                      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).controlledTransform
                    ((separateAllBoundary T h.valid hinv A).ideal
                      (separateAllBoundary T h.valid hinv A).length)
                    (MaxContactCoverData.cT h.valid).mult i)
                  (MaxContactCoverData.cT h.valid).mult =
                orderAtLeastLocus ((A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).ideal i)
                  (tuningExponent (MaxContactCoverData.cT h.valid).mult) := by
  let _c0 := separateAllBoundary T h.valid hinv A
  let _c1 := p7 h.valid
  let _c2 := p31 h.valid
  have hV : tAd _c1 := isAdmissible_coverTriple hstar P T h
  have hO :=
    orderAt_coverTriple_ideal_le_mult hstar P T h
  have hft :=
    locallyOfFiniteType_projectionToBase_comp hstar _c1 hV
      _c0 _c0.length (le_refl _)
  have hzero := inStrictNormalCrossingPosition_iteratedStrictTransform_zero _c1
    _c0 _c2
    (inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
  have hsnc := inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar _c1
    hV hO _c2 (isMaxContactHypersurface_coverMaxContactIdeal hstar P T h) _c0 hzero
    _c0.length (le_refl _)
  let _m0 := reduceAlongHypersurfaceTriple T h.valid hinv A hft
  let _a1 := strictTransformAtLength _c0 _c2
  have hVc : tAd _m0 :=
    isAdmissible_derivedTriple hstar _c1 hV
      _c0 hft
      [_a1]
      _c1.boundary.length hsnc
  have hdim : tDim _m0 ≤ tDim T := by
    have h1 := hstar.schemeDim_level_le _c1 hV
      _c0.toMarkedSequenceOfBlowups _c0.length
      (le_refl _)
    refine le_trans ?_ (hstar.coverTriple_dim_le T h.valid)
    with_unfolding_all exact h1
  have hP := hmono _ _ hdim h.dim_prop
  have hj : 0 < ([_a1] ++
      (_c0.boundary
        _c0.length).drop
          (bLen _c1)).length := by simp_all
  have hfacts := separateBoundaryInvariant_separateBoundarySeq hstar hinv P hmono A B hspec T h
    _c1.boundary.length (le_refl _)
  have htop : BoundarySeparated _c1 _c0
      (bLen _c1) := And.left hfacts
  have hsep : ∀ D ∈ (_c0.boundary
        _c0.length).take
          (bLen _c1),
      orderAtLeastLocus (_c0.ideal
            _c0.length)
          _c1.mult ∩
        (spI D : Set (_c0.obj
          _c0.length)) = ∅ :=
    forall_mem_take_of_forall_lt _ _ _ htop
  let _a0 := p49 A T
  obtain ⟨hmk, heq, hcos⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B 0 (hspec 0)
    _a0 (fun _ _ _ => rfl)
    _c1 hV hV.one_le_mult hO
    _c0
    [_a1]
    _c1.boundary.length hft hdim hP hVc hj hsep
  have hcover : MaxContactCoverData.coverMarkedBlowupData T h.valid hinv _a0 =
      appendLowerDimReduction hinv T _a0
        _c1 _c0
        [_a1]
        _c1.boundary.length 0 :=
    reduceAlongHypersurface_eq_appendLowerDimReduction hinv T _a0
      _c1 _c2
  refine ⟨hft, hVc, hP, hmk, ?_, hcos⟩
  rwa [hcover]
end
end

end BoundarySeparationByMaxContact





namespace BoundarySeparationByMaxContact

theorem orderAtLeastLocus_eq_support_maxContactIdeal (k : Type) [Field k] [CharZero k]
    {P : Sch} p [Smooth p]
    [LocallyOfFiniteType p] A m (hm : 1 ≤ m) :
    orderAtLeastLocus A m = (support (maxContactIdeal k p A m) : Set ↥P) := by
  have hlt : m - 1 < m := by omega
  have hd := orderAtLeastLocus_derivIdealSheafIterate k p A (r := m - 1) (m := m) hlt
  rw [show m - (m - 1) = 1 from by omega] at hd
  ext x
  rw [← hd]
  exact mem_orderAtLeastLocus_one_iff _ x

section
variable {X Y : Sch}
section
variable (e : X ≅ Y)
section
variable (J : ISD Y) (n : ℕ)
theorem orderAtLeastLocus_comap_iso_eq_empty (hJ : orderAtLeastLocus J n = ∅) :
    orderAtLeastLocus (comap J e.hom) n = ∅ := by
  rw [orderAtLeastLocus_comap_iso e J n, hJ, preimage_empty]

private theorem orderAtLeastLocus_eq_empty_of_comap_iso__b1 (hJ : orderAtLeastLocus (J.comap e.hom) n = ∅) :
    orderAtLeastLocus J n = ∅ := by
  rw [orderAtLeastLocus_comap_iso e J n] at hJ
  have hsurj : ∀ y, ∃ x, isoH e x = y := by
    intro y
    refine ⟨isoI e y, ?_⟩
    simp
  ext y
  simp [mem_empty_iff_false, iff_false]
  intro hy
  obtain ⟨x, hx⟩ := hsurj y
  have hmem : x ∈ (e.hom ⁻¹' orderAtLeastLocus J n) := by
    simp [m163, hx]
    exact hy
  rwa [hJ] at hmem
end

theorem exists_base_iso_inv_eq x :
    ∃ y, e.inv.base y = x :=
  ⟨ihB_ e x, congrArg (fun f : X ⟶ X => bsM f x) e.hom_inv_id⟩
end

theorem comap_ne_top_of_surjective_base (f : Y ⟶ X)
    (hf : ∀ x : ↥X, ∃ y : ↥Y, f.base y = x) (J : ISD X) (hJ : J ≠ ⊤) :
    comap J f ≠ ⊤ := by
  intro htop
  refine hJ $ (eq_top_iff_support_eq_empty J).2 ?_
  ext x
  simp [mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, hy⟩ := hf x
  have h1 : 1 ≤ orderAt J (bsM f y) := by
    rw [hy]
    exact (one_le_orderAt_iff_mem_support J x).2 hx
  have h2 : y ∈ (spI (cmI J f) : Set ↥Y) :=
    (one_le_orderAt_iff_mem_support (cmI J f) y).1
      (le_trans h1 $ orderAt_le_orderAt_comap f J y)
  rw [(eq_top_iff_support_eq_empty $ cmI J f).1 htop] at h2
  exact (mem_empty_iff_false y).1 h2

theorem exists_base_eqToHom_eq (h : X = Y) x :
    ∃ y, (CategoryTheory.eqToHom h).base y = x := by
  subst h
  refine ⟨x, ?_⟩
  simp
end

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X} (s : MarkedBlowupSequenceData p I m E)
theorem mem_support_toBlowupSequenceData_iteratedStrictTransform (H : ISD X) (i : ℕ)
    (x : ↥(s.obj i))
    (hx : x ∈ (support (MaxContactReduction.iteratedStrictTransform s H i) : CSet $ s.obj i)) :
    x ∈ (support (s.toBlowupSequenceData.iteratedStrictTransform i H) : CSet $ s.obj i) := by
  rwa [← iteratedStrictTransform_eq_toBlowupSequenceData s H i]

section
variable (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)) (hinv : ComapIsoInvariance)
private theorem orderAtLeastLocus_append_eq_empty__b1 (n : ℕ)
    (ht : ∀ i : ℕ, i = t.length → orderAtLeastLocus (t.ideal i) n = ∅)
    (hs : t.length = 0 → ∀ i : ℕ, i = s.length → orderAtLeastLocus (s.ideal i) n = ∅) :
    orderAtLeastLocus ((s.append t hinv).ideal (s.append t hinv).length) n = ∅ := by
  have key : ∀ i, i = s.length + t.length →
      orderAtLeastLocus ((s.append t hinv).ideal i) n = ∅ := by
    rintro i rfl
    rw [append_ideal]
    rcases m73 t.length with hz | hpos
    have hle : s.length + t.length ≤ s.length := by omega
    rw [appendIdeal_of_le_length s t hle]
    exact orderAtLeastLocus_comap_iso_eq_empty (eqToIso $ appendToBlowupSequenceData_schemeAt_of_le_length s t hle) _ _ $ hs hz _ $ by omega
    have hgt : s.length < s.length + t.length := by omega
    rw [appendIdeal_of_length_lt s t hgt]
    exact orderAtLeastLocus_comap_iso_eq_empty (eqToIso $ appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt) _ _ $ ht _ $ by omega
  exact key _ $ append_length s t hinv

theorem center_append_ne_top
    (hs : ∀ i < s.length, s.center i ≠ ⊤)
    (ht : ∀ i < t.length, t.center i ≠ ⊤) :
    ∀ i < (s.append t hinv).length, (s.append t hinv).center i ≠ ⊤ := by
  intro i hi
  rw [append_length] at hi
  rw [append_toBlowupSequenceData]
  rcases lt_trichotomy i s.length with hlt | hmid | hgt
  rw [appendToBlowupSequenceData_center_of_lt_length s t hlt]
  exact comap_ne_top_of_surjective_base _ (exists_base_eqToHom_eq _) _ $ hs i hlt
  subst hmid
  rw [appendToBlowupSequenceData_center_length s t]
  refine comap_ne_top_of_surjective_base _ (exists_base_eqToHom_eq _) _ ?_
  refine comap_ne_top_of_surjective_base _ (exists_base_iso_inv_eq _) _ ?_
  exact ht 0 $ by omega
  rw [appendToBlowupSequenceData_center_of_length_lt s t hgt]
  exact comap_ne_top_of_surjective_base _ (exists_base_eqToHom_eq _) _ $ ht _ $ by omega
end
end

theorem restrictIdeal_eq_comap {X : Sch} (D : ISD X) (V : Opn X) :
    restrictIdeal D V = comap D V.i := rfl

theorem orderAtLeastLocus_subset_support_of_isMaxContactHypersurface (k : Type) [Field k]
    [CharZero k] {P : Sch} (p : P ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p]
    (A H : ISD P) (mu_ : ℕ) (hmu_ : 1 ≤ mu_)
    (hH : IsMaxContactHypersurface k p A mu_ H) :
    orderAtLeastLocus A mu_ ⊆ (support H : Set ↥P) := by
  let _a0 := maxContactIdeal k p A mu_
  intro x hx
  obtain ⟨U, _, hxU, hcase⟩ := hH x
  rcases hcase with ⟨hdisj, _⟩ | ⟨_, _, _, hcoord, hmcc⟩
  exact absurd hxU $ Set.disjoint_left.1 hdisj hx
  have hmc : x ∈ (spI _a0 : Set P) := by
    rwa [← orderAtLeastLocus_eq_support_maxContactIdeal k p A mu_ hmu_]
  have hbase : bsM (opI U) (⟨x, hxU⟩ : U) = x := rfl
  have h1 : (⟨x, hxU⟩ : U) ∈ spI (cmI _a0 U.i) := by
    refine mem_support_comap.2 ?_
    rwa [hbase]
  have hle : (comap H U.i) ≤ (comap _a0 U.i) := by
    rwa [← restrictIdeal_eq_comap, ← restrictIdeal_eq_comap, hcoord]
  have h3 := mem_support_comap.1 $ support_antitone hle h1
  rwa [hbase] at h3

theorem orderAtLeastLocus_coverMarkedBlowupData_eq_empty (hstar : MaxContactCoverProperties) (hinv : ComapIsoInvariance)
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment)
    (B : PrincipalizationAssignment) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    orderAtLeastLocus
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).ideal
          (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length)
        (tunedMult T) = ∅ := by
  let _a2 := p31 h.valid
  let _c0 := separateAllBoundary T h.valid hinv A
  let _c1 := p7 h.valid
  obtain ⟨hft, hVc, hPdim, hmk, heq, hcs⟩ := exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have hScV := isAdmissible_coverTriple hstar P T h
  have hScO := orderAt_coverTriple_ideal_le_mult hstar P T h
  let _m0 := ofMarkedSequence $ A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)
  have hNo : ∀ i ≤ mbsLen _m0,
      IsLocallyNoetherian
        (mbsObj _m0 i) := by
    intro i hi
    exact isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar _c1 hScV
      _c0 hft
      [strictTransformAtLength _c0
        _a2]
      _c1.boundary.length hVc
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) i hi
  let _a1 := p8 _c1 _c0 hft [strictTransformAtLength _c0 (p31 h.valid)] (bLen _c1)
  have hlow : ∀ i, i = (A 0 _a1).length → orderAtLeastLocus ((A 0 _a1).ideal i) _a1.mult = ∅ := by
    let S := _c1
    let hSV := hScV
    let hmS := hScV.one_le_mult
    let hSO := hScO
    let s := _c0
    let Hc := strictTransformAtLength _c0
      _a2
    let keep := bLen _c1
    rintro i rfl
    have := hft
    have := smooth_projectionToBase_comp hstar _c1 hScV _c0 _c0.length (le_refl _)
    have := hSV.charZero
    have hOB :=
      LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hSV hmS hSO s hft [Hc] keep hVc
    have hj : 0 < (p8 S s hft [Hc] keep).boundary.length := by
      rw [p48]
      simp
    obtain ⟨Dv, bv, _, hDvEq, _, hBoundaryOfMem, hBoundaryOfLt, hBoundaryEq, _⟩ :=
      (hspec 0).shape (p8 S s hft [Hc] keep) hVc hPdim hOB (LowerDimReductionPullback.isBalanced_derivedTriple hstar S hSV hmS hSO s hft [Hc] keep hVc) hj
    let _a3 := s.proj s.length ≫ tMp S
    have hadm2 : @IsMaxContactHypersurface (p8 S s hft [Hc] keep).base _
        (p8 S s hft [Hc] keep).scheme
        (p8 S s hft [Hc] keep).structMap hVc.locallyOfFiniteType
        (p8 S s hft [Hc] keep).ideal
        (p8 S s hft [Hc] keep).mult Hc := by
      rw [derivedTriple_mult]
      exact @isMaxContactHypersurface_of_eq_of_eq_of_eq S.base _ (s.obj s.length)
        _a3
        (p8 S s hft [Hc] keep).structMap hft hVc.locallyOfFiniteType
        (LowerDimReductionPullback.tunedIdealAtLength S s hft) (p8 S s hft [Hc] keep).ideal Hc Hc
        (tuningExponent S.mult)
        (derivedTriple_structureMorphism S s hft [Hc] keep).symm
        (LowerDimReductionPullback.ideal_derivedTriple S s hft [Hc] keep).symm rfl (isMaxContactHypersurface_balancedTunedSheaf hstar S.base _a3 (s.ideal s.length) S.mult hmS (LowerDimReductionPullback.orderAt_ideal_length_le hstar S hSV hSO s) Hc (isMaxContactHypersurface_iteratedStrictTransform hstar _c1 hScV hScO _a2 (isMaxContactHypersurface_coverMaxContactIdeal hstar P T h) _c0 _c0.length (le_refl _)))
    have := hVc.charZero
    have hftL := locallyOfFiniteType_projectionToBase_comp hstar (p8 S s hft [Hc] keep)
      hVc (ofMarkedSequence (A 0 (p8 S s hft [Hc] keep)))
      (ofMarkedSequence
        (A 0 (p8 S s hft [Hc] keep))).length (le_refl _)
    have hsmL := smooth_projectionToBase_comp hstar (p8 S s hft [Hc] keep)
      hVc (ofMarkedSequence (A 0 (p8 S s hft [Hc] keep)))
      (ofMarkedSequence
        (A 0 (p8 S s hft [Hc] keep))).length (le_refl _)
    have hadmL := isMaxContactHypersurface_iteratedStrictTransform hstar
      (p8 S s hft [Hc] keep) hVc ((isOrderBoundedByMult_iff _).1 hOB) Hc hadm2
      (ofMarkedSequence (A 0 (p8 S s hft [Hc] keep)))
      (ofMarkedSequence
        (A 0 (p8 S s hft [Hc] keep))).length (le_refl _)
    have hsub1 := @orderAtLeastLocus_subset_support_of_isMaxContactHypersurface
      (p8 S s hft [Hc] keep).base _ _ _
      ((ofMarkedSequence (A 0 (p8 S s hft [Hc] keep))).proj
          (ofMarkedSequence
            (A 0 (p8 S s hft [Hc] keep))).length ≫
        (p8 S s hft [Hc] keep).structMap) hsmL hftL
      ((ofMarkedSequence (A 0 (p8 S s hft [Hc] keep))).ideal
        (ofMarkedSequence
          (A 0 (p8 S s hft [Hc] keep))).length)
      (p42
        (ofMarkedSequence (A 0 (p8 S s hft [Hc] keep))) Hc
        (ofMarkedSequence
          (A 0 (p8 S s hft [Hc] keep))).length)
      (p8 S s hft [Hc] keep).mult hVc.one_le_mult hadmL
    have h0 : Dv 0 = cmI Hc (ofMarkedSequence
        (A 0 (p8 S s hft [Hc] keep))).toBlowupSequenceData.isoZero.hom := by
      rw [hDvEq]
      rfl
    have hstep : ∀ tt, tt < mbsLen (ofMarkedSequence
          (A 0 (p8 S s hft [Hc] keep))) →
        Dv (tt + 1) = p6
            ((ofMarkedSequence
              (A 0 (p8 S s hft [Hc] keep))).toBlowupSequenceData.map tt)
            (mbsCtr (ofMarkedSequence
              (A 0 (p8 S s hft [Hc] keep))) tt) (Dv tt) ∨
          Dv (tt + 1) = cmI (Dv tt)
            ((ofMarkedSequence
              (A 0 (p8 S s hft [Hc] keep))).toBlowupSequenceData.map tt) := by
      intro tt htt
      by_cases hb : bv = true ∧ tt = 0
      obtain ⟨hb1, hb2⟩ := hb
      subst hb2
      exact inr (hBoundaryOfMem hb1).2.2
      exact inl $ hBoundaryOfLt tt htt hb
    have hsub2raw := BlowupSequenceData.support_iteratedStrictTransform_subset_support
      (ofMarkedSequence
        (A 0 (p8 S s hft [Hc] keep))).toBlowupSequenceData hNo Hc Dv h0 hstep
      (ofMarkedSequence
        (A 0 (p8 S s hft [Hc] keep))).length (le_refl _)
    ext x
    simp [mem_empty_iff_false, iff_false]
    intro hx
    have hmem : x ∈ orderAtLeastLocus (lastIdeal
          (A 0 (p8 S s hft [Hc] keep)))
          (p8 S s hft [Hc] keep).mult ∩
        ((spI (Dv (A 0 (p8 S s hft [Hc] keep)).length)) :
          Set ((A 0 (p8 S s hft [Hc] keep)).schemeAt
            (A 0 (p8 S s hft [Hc] keep)).length)) :=
      ⟨hx, hsub2raw (mem_support_toBlowupSequenceData_iteratedStrictTransform _ _ _ _ $ hsub1 hx)⟩
    rwa [hBoundaryEq] at hmem
  rw [heq, ← MaxContactCoverData.coverTriple_mult T h.valid]
  refine orderAtLeastLocus_append_eq_empty__b1 _c0
    (continuationMarkedData _c1 _c0 hft
      [strictTransformAtLength _c0
        _a2]
      (bLen _c1)
      (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk) hinv
    _c1.mult ?_ ?_
  rintro i rfl
  refine m32 (hcs (msLen (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)))
    (le_refl _)) ?_
  rw [← derivedTriple_mult _c1
    _c0 hft
    [strictTransformAtLength _c0
      _a2]
    (bLen _c1)]
  exact hlow _ rfl
  intro hz i hi
  subst hi
  refine orderAtLeastLocus_eq_empty_of_comap_iso__b1
    (ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).isoZero
    _ _ ?_
  refine m32 (hcs 0 (m67 _)) ?_
  rw [← derivedTriple_mult _c1
    _c0 hft
    [strictTransformAtLength _c0
      _a2]
    (bLen _c1)]
  exact hlow 0 hz.symm

theorem length_pos_of_eq_cons {al_ : Type} {L : List al_} {a} {M}
    (h : L = a :: M) : 0 < length L := by
  subst h
  exact succ_pos _

theorem center_coverMarkedBlowupData_ne_top (hstar : MaxContactCoverProperties) (hinv : ComapIsoInvariance) P
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) A
    B (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    T (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∀ i < (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length,
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).center i
        ≠ ⊤ := by
  let _c0 := separateAllBoundary T h.valid hinv A
  let _c1 := p7 h.valid
  obtain ⟨hft, hVc, hP, hmk, heq, _⟩ :=
    exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have hV := isAdmissible_coverTriple hstar P T h
  have hO := orderAt_coverTriple_ideal_le_mult hstar P T h
  let _a0 := strictTransformAtLength _c0 $ p31 h.valid
  have hfacts := separateBoundaryInvariant_separateBoundarySeq hstar hinv P hmono A B hspec T h
    _c1.boundary.length $ le_refl _
  rw [heq]
  refine center_append_ne_top _ _ _ (And.left $ And.right hfacts) ?_
  intro i hi htop
  exact (((hspec 0).center_nonempty (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hVc hP (LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar _c1 hV hV.one_le_mult hO _c0 hft [_a0] _c1.boundary.length hVc) (LowerDimReductionPullback.isBalanced_derivedTriple hstar _c1 hV hV.one_le_mult hO _c0 hft [_a0] _c1.boundary.length hVc) $ length_pos_of_eq_cons $ p48 _c1 _c0 hft [_a0] $ bLen _c1) i hi).ne_empty
    ((eq_top_iff_support_eq_empty _).1 htop)

end BoundarySeparationByMaxContact





theorem strictTransform_top_eq_top {X' X : Sch} (f : X' ⟶ X) (Z : ISD X) :
    strictTransform f Z ⊤ = ⊤ := by
  have h := comap_le_strictTransform f Z (⊤)
  have h2 : (⊤) ≤ p6 f Z ⊤ := by simp_all
  exact mp_ top_le_iff h2

theorem BlowupSequenceData.iteratedStrictTransform_top {X : Sch} (d : BlowupSequenceData X) (i : ℕ) :
    d.iteratedStrictTransform i ⊤ = ⊤ := by
  induction i with
  | zero =>
      rw [BlowupSequenceData.iteratedStrictTransform_zero]
      simp
  | succ i ih =>
      rw [BlowupSequenceData.iteratedStrictTransform_succ, ih, strictTransform_top_eq_top]






theorem comap_eqToHom_of_eq {F : ℕ → Sch} (K : ∀ i : ℕ, (F i).IdealSheafData)
    {a b : ℕ} (h : a = b) : comap (K b) (eqToHom $ congrArg F h) = K a := by
  subst h
  exact comap_id _

theorem exists_lift_of_centers_comap_eq_top {A B} ph_ (c : SequenceOfBlowups B)
    (hinv : ∀ i : ℕ, i < c.length → ∀ ps_ : A ⟶ schemeAt c i,
      ps_ ≫ projectionToBase c i = ph_ → (center c i).comap ps_ = ⊤) :
    ∀ i, i ≤ c.length → ∃ ps_, ps_ ≫ projectionToBase c i = ph_ ∧
      ∀ T (v : T ⟶ A) (u : T ⟶ schemeAt c i), u ≫ projectionToBase c i = v ≫ ph_ →
        u = v ≫ ps_ := by
  intro i
  induction i with
  | zero =>
    intro _
    have : IsIso $ projectionToBase c 0 := by
      rw [projectionToBase_zero]
      infer_instance
    refine ⟨ph_ ≫ m83 (sbPrj c 0), by simp, ?_⟩
    intro T v u h
    rw [← assoc, ← h]
    simp
  | succ m ih =>
    intro hm
    obtain ⟨ps_, hps_, hu⟩ := ih $ m49 hm
    have hmlt := hm
    have htop := hinv m hmlt ps_ hps_
    have hbl := c.isBlowupAlongIdealSheaf_blowupMorphism m hmlt
    have hcart : p17 $ (sbCtr c m).comap ps_ := by
      rw [htop]
      exact isLocallyGeneratedByNonZeroDivisor_top _
    have h2 : transitionMapSucc c m ≫ projectionToBase c m = projectionToBase c (m + 1) := by
      rw [blowupMorphism_eq_transitionMap]
      exact c.transitionMap_comp_projectionToBase _
    refine ⟨hbl.lift ps_ hcart, ?_, ?_⟩
    have h1 := hbl.lift_comp ps_ hcart
    rw [← h2, ← assoc, h1, hps_]
    intro T v u h
    have hdown : u ≫ sbTrS c m = v ≫ ps_ := by
      refine hu T v (u ≫ sbTrS c m) ?_
      rwa [assoc, h2]
    have hcart2 : p17 $ (sbCtr c m).comap $ v ≫ ps_ := by
      rw [comap_comp, htop]
      exact isLocallyGeneratedByNonZeroDivisor_comap_top v
    refine hbl.hom_ext_of_comp_eq hcart2 hdown ?_
    rw [assoc, hbl.lift_comp ps_ hcart]

section
variable {X X'} {ph_} {t' : SequenceOfBlowups X'} {t : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback ph_ t' t)
theorem eq_comap_mapToEarlierScheme_of_le_of_index_ne
    (K : ∀ i : ℕ, (schemeAt t i).IdealSheafData)
    (hN : ∀ i : ℕ, i ≤ t.length → IsNoetherian (schemeAt t i))
    (hrec : ∀ i : ℕ, i < t.length → K (i + 1) = strictTransform (transitionMapSucc t i) (center t i) (K i))
    (j : ℕ) (hj : j ≤ t'.length) (L : (schemeAt t' j).IdealSheafData) (i0_ : ℕ) (hi0_ : i0_ ≤ c.idx j)
    (hmiss : ∀ i : ℕ, i0_ ≤ i → i < c.idx j → ∀ j' : ℕ, j' < t'.length → c.idx j' ≠ i)
    (h : L = (K i0_).comap (c.mapToEarlierScheme j hj i0_ hi0_)) :
    ∀ i : ℕ, i0_ ≤ i → ∀ hi : i ≤ c.idx j, L = (K i).comap (c.mapToEarlierScheme j hj i hi) := by
  intro i hii
  induction i, hii using le_induction with
  | base => intro _; exact h
  | succ p hp ih =>
    intro hi
    have hplt := hi
    let i := p
    let hi := hplt
    have hilt := lt_of_lt_of_le hi $ c.index_le_length j hj
    have := hN (i + 1) hilt
    let _a0 := c.mapToEarlierScheme j hj (i + 1) hi
    have hcenter : (cmI (sbCtr t i) $ sbTrS t i).comap _a0 = ⊤ := by
      rw [← comap_comp, ← c.mapToEarlierScheme_eq_comp_blowupMorphism j hj i hi]
      exact c.comap_center_mapToEarlierScheme_eq_top_of_unmatched j hj i hi $ hmiss p hp hplt
    rw [ih $ le_of_lt hplt, hrec i hilt,
      strictTransform_comap_of_comap_center_eq_top (sbTrS t i) (sbCtr t i) (K i)
        _a0 hcenter,
      ← comap_comp, ← c.mapToEarlierScheme_eq_comp_blowupMorphism j hj i hi]

section
variable [hv5_0 : Flat ph_] (K : ∀ i : ℕ, (schemeAt t i).IdealSheafData) (K' : ∀ j : ℕ, (schemeAt t' j).IdealSheafData) (hN : ∀ i : ℕ, i ≤ t.length → IsNoetherian (schemeAt t i)) (hN' : ∀ j : ℕ, j ≤ t'.length → IsNoetherian (schemeAt t' j))
include hv5_0 hN hN'
theorem iteratedStrictTransform_eq_comap_lastMap_of_sequence
    (hzero : K' 0 = (K 0).comap (c.mapToEarlierScheme 0 (zero_le _) 0 (zero_le _)))
    (hrec : ∀ i : ℕ, i < t.length → K (i + 1) = strictTransform (transitionMapSucc t i) (center t i) (K i))
    (hrec' : ∀ j : ℕ, j < t'.length →
      K' (j + 1) = strictTransform (transitionMapSucc t' j) (center t' j) (K' j)) :
    K' t'.length = (K t.length).comap c.lastMap := by
  have main : ∀ j (hj : j ≤ t'.length), K' j = cmI (K (c.idx j)) (c.map j hj) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hmiss : ∀ i, 0 ≤ i → i < c.idx 0 → ∀ j', j' < t'.length → c.idx j' ≠ i :=
        fun i _ h2 => c.index_ne_of_lt_index_zero i h2
      have hfin := eq_comap_mapToEarlierScheme_of_le_of_index_ne c K hN hrec 0 hj (K' 0) 0 (m67 _) hmiss hzero
        (c.idx 0) (m67 _) le_rfl
      rwa [c.mapToEarlierScheme_index 0 hj] at hfin
    | succ m ih =>
      intro hj
      let j := m
      have hidxlt := c.idx_lt j hj
      let _m0 := c.idx j + 1
      have := hN _m0 hidxlt
      have := hN' (j + 1) hj
      have := c.flat_map j $ le_of_lt hj
      have key := comap_strictTransform_of_flat_of_isLocallyNoetherian
        (sbTrS t (c.idx j)) (c.map j $ le_of_lt hj) (sbTrS t' j)
        (c.mapToEarlierScheme (j + 1) hj _m0 (c.idx_strictMono j hj)) (c.isPullback_blowupMorphism j hj)
        (sbCtr t (c.idx j)) (K (c.idx j)) (t.isBlowupAlongIdealSheaf_blowupMorphism (c.idx j) hidxlt)
      have e2 : K' (j + 1)
          = (K _m0).comap (c.mapToEarlierScheme (j + 1) hj _m0 (c.idx_strictMono j hj)) := by
        rw [hrec' j hj, hrec (c.idx j) hidxlt, key, ih $ m49 hj, c.center_comap j hj]
      have hmiss :=
        fun i h1 h2 => c.index_ne_of_index_lt_of_lt_index_succ j hj i h1 h2
      have hfin := eq_comap_mapToEarlierScheme_of_le_of_index_ne c K hN hrec (j + 1) hj (K' (j + 1)) _m0
        (c.idx_strictMono j hj) hmiss e2 (c.idx (j + 1)) (c.idx_strictMono j hj) le_rfl
      rwa [c.mapToEarlierScheme_index (j + 1) hj] at hfin
  have hLastMap : c.lastMap = c.map t'.length le_rfl ≫ eqToHom (congrArg t.schemeAt c.idx_length) := rfl
  rw [main t'.length le_rfl, hLastMap, comap_comp, comap_eqToHom_of_eq]
  exact c.idx_length
end
end

namespace SequenceOfBlowupsPullback

section

variable {X X' : Sch} {ph_ : X' ⟶ X}

theorem smooth_lastMap {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback ph_ s' s)
    [Smooth ph_] : Smooth c.lastMap :=
  by
  exact m98 (P := @Smooth) (c.isPullback_lastMap).flip inferInstance

end

section

variable {k k' : Type} [Field k] [Field k']
variable {X Y : Sch}
variable {p : X ⟶ Sp k} {q : Y ⟶ Sp k'}
variable {g : Y ⟶ X}
variable {I : ISD X} {I' : ISD Y} {m : ℕ}
variable {E : Bdy X} {E' : Bdy Y}

theorem iteratedStrictTransform_eq_comap_lastMap {s : MarkedBlowupSequenceData p I m E} {s' : MarkedBlowupSequenceData q I' m E'}
    (d : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    [Flat g]
    (K : ∀ i : ℕ, (s.obj i).IdealSheafData) (K' : ∀ j : ℕ, (s'.obj j).IdealSheafData)
    (hN : ∀ i : ℕ, i ≤ s.length → IsNoetherian (s.obj i))
    (hN' : ∀ j : ℕ, j ≤ s'.length → IsNoetherian (s'.obj j))
    (hzero : K' 0 = (K 0).comap (d.mapToEarlierScheme 0 (zero_le _) 0 $ zero_le _))
    (hrec : ∀ i : ℕ, i < s.length →
      K (i + 1) = strictTransform (s.map i) (s.center i) (K i))
    (hrec' : ∀ j : ℕ, j < s'.length →
      K' (j + 1) = strictTransform (s'.map j) (s'.center j) (K' j)) :
    K' s'.length = (K s.length).comap d.lastMap := by
  refine iteratedStrictTransform_eq_comap_lastMap_of_sequence d K K' ?_ ?_ hzero ?_ ?_
  intro i hi
  exact hN i hi
  intro j hj
  exact hN' j hj
  intro i hi
  rw [toMarkedSequence_blowupMorphism, toMarkedSequence_center]
  exact hrec i hi
  intro j hj
  rw [toMarkedSequence_blowupMorphism, toMarkedSequence_center]
  exact hrec' j hj

end

end SequenceOfBlowupsPullback

theorem isPullback_of_length_zero_of_comap_center_eq_top {A B} ph_
    (n : SequenceOfBlowups A) (c : SequenceOfBlowups B) (hn : n.length = 0)
    (hinv : ∀ i : ℕ, i < c.length → ∀ ps_ : A ⟶ schemeAt c i,
      ps_ ≫ projectionToBase c i = ph_ → (center c i).comap ps_ = ⊤) :
    IsPullbackBlowupSequence ph_ n c := by
  obtain ⟨ps_, hps_, huniq⟩ := exists_lift_of_centers_comap_eq_top ph_ c hinv c.length le_rfl
  have hlt : ∀ j, ¬ j < n.length := by simp_all
  refine SequenceOfBlowupsPullback.isPullbackSequenceOfBlowups
    { idx := fun _ => c.length
      map := fun j _ => projectionToBase n j ≫ ps_
      idx_length := rfl
      idx_lt := fun j hj => absurd hj $ hlt j
      idx_strictMono := fun j hj => absurd hj $ hlt j
      isPullback := ?_
      step := fun j hj => absurd hj $ hlt j
      center_comap := fun j hj => absurd hj $ hlt j
      center_ne_top := fun j hj => absurd hj $ hlt j
      omitted := ?_ }
  intro j hj
  have hj0 : j = 0 := by simp_all
  subst hj0
  have : IsIso $ projectionToBase n 0 := by
    rw [projectionToBase_zero]
    infer_instance
  let e := projectionToBase n 0
  have w : (e ≫ ps_) ≫ projectionToBase c c.length = e ≫ ph_ := by rw [assoc, hps_]
  refine IsPullback.of_isLimit' ⟨w⟩
    (Limits.PullbackCone.IsLimit.mk w (·.snd ≫ inv e) ?_ ?_ ?_)
  intro s
  simp [assoc, IsIso.inv_hom_id_assoc]
  exact sy_ $ huniq s.pt s.snd s.fst s.condition
  intro s
  simp
  simp_all
  intro i hi _ z hz x' hcon
  obtain ⟨psi, hpsi, huniqi⟩ := exists_lift_of_centers_comap_eq_top ph_ c hinv i $ le_of_lt hi
  obtain ⟨w, hw1, hw2⟩ :=
    m198
      (f := projectionToBase c i) (g := ph_) (x := z) (y := x') hcon.symm
  let _a0 := m47 (projectionToBase c i) ph_
  let _a1 := m57 (projectionToBase c i) ph_
  let _m0 := bsM _a0 w
  have hza : bsM psi _m0 = z := by
    rw [← hw1]
    show bsM (_a0 ≫ psi) w
      = bsM _a1 w
    rw [huniqi _ _a0 _a1 Limits.pullback.condition]
  have key : 1 ≤ orderAt ((center c i).comap psi)
      _m0 := by
    refine le_trans ?_ $ orderAt_le_orderAt_comap psi (center c i) _
    show (1 : ENat) ≤ orderAt (center c i) (bsM psi _)
    rw [hza]
    exact (one_le_orderAt_iff_mem_support _ _).2 hz
  rw [hinv i hi psi hpsi, orderAt_top] at key
  simp at key




namespace StrictPullbackBlowupSeq

end StrictPullbackBlowupSeq

namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (u : MarkedBlowupSequenceData p I m E) {i j} (h : i = j)
theorem ideal_congr_index :
    ideal u i = comap (ideal u j) (eqToHom $ congrArg (fun n => u.obj n) h) := by
  subst h
  simp

theorem boundary_congr_index :
    boundary u i =
      (boundary u j).map fun A => comap A $ eqToHom $ congrArg (fun n => u.obj n) h := by
  subst h
  simp
end

end MarkedBlowupSequenceData

theorem IsStrictPullbackBlowupSeq.of_eq {X' X : Sch} {ph_ : X' ⟶ X} {B1_ B2_ : SequenceOfBlowups X'}
    {C1_ C2_ : SequenceOfBlowups X} (h1_ : B1_ = B2_) (h2_ : C1_ = C2_)
    (hh : IsStrictPullbackBlowupSeq ph_ B1_ C1_) : IsStrictPullbackBlowupSeq ph_ B2_ C2_ :=by simp_all
namespace LowerDimReductionPullback

@[reducible] noncomputable def pullbackTriple (S : MarkedIdealWithBoundary) {Y : Sch}
    (g : Y ⟶ scheme S) : MarkedIdealWithBoundary :=
  S.pbA (g ≫ structMap S) g

variable (S : MarkedIdealWithBoundary) {Y : Sch} (g : Y ⟶ scheme S)
  (s : S.mbs)
  (t : MarkedBlowupSequenceData (pullbackTriple S g).structMap (pullbackTriple S g).ideal (pullbackTriple S g).mult
      (pullbackTriple S g).boundary)
  (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)

noncomputable def pullbackMapAtLength : t.obj t.length ⟶ s.obj s.length :=
  D.lastMap

theorem pullbackMapAtLength_eq_lastMap : pullbackMapAtLength S g s t D = D.lastMap := rfl

@[reducible] noncomputable def comapBoundaryPullback (L : List (s.obj s.length).IdealSheafData) :
    List (t.obj t.length).IdealSheafData :=
  L.map fun A => comap A $ pullbackMapAtLength S g s t D

theorem comap_eq_comap_comp_eqToHom
    (F : ℕ → Sch) (J : ∀ n : ℕ, (F n).IdealSheafData) {a b : ℕ} (hab : a = b)
    {Z : Sch} (f : Z ⟶ F a) :
    comap (J a) f = comap (J b) (f ≫ eqToHom (congrArg F hab)) := by
  subst hab
  simp

theorem smooth_comp_eqToHom {X Y Y' : Sch} (f : X ⟶ Y) (h : Y = Y')
    (hf : Smooth f) : Smooth $ f ≫ eqToHom h := by
  subst h
  simp [eqToHom_refl, comp_id]
  exact hf

private theorem smooth_lastMap {X' X : Sch} {g : X' ⟶ X}
    [Smooth g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) : Smooth D.lastMap := by
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  refine smooth_comp_eqToHom _ _ ?_
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (@Smooth) := inferInstance
  exact hbc.of_isPullback (isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero D.pullback t.length le_rfl).flip ‹Smooth g›

theorem smooth_pullbackMapAtLength [Smooth g] :
    Smooth $ pullbackMapAtLength S g s t D := by
  rw [pullbackMapAtLength_eq_lastMap]
  exact smooth_lastMap D

theorem surjective_comp_eqToHom {X Y Z : Sch} (f : X ⟶ Y)
    (hf : AlgebraicGeometry.Surjective f) (h : Y = Z) :
    AlgebraicGeometry.Surjective $ f ≫ eqToHom h := by
  subst h
  rwa [eqToHom_refl, comp_id]

theorem surjective_lastMap {X' X : Sch} {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) : AlgebraicGeometry.Surjective D.lastMap := by
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  exact surjective_comp_eqToHom _
    (surjective_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero D.pullback
      t.length le_rfl) _

theorem isStrictPullbackBlowupSeq_of_isBoundaryDivisorReduction {P : ℕ → Prop} {jj : ℕ} {A B : PrincipalizationAssignment}
    (hspec : IsBoundaryDivisorReduction P jj A B) (T : MarkedIdealWithBoundary) (hV : IsAdmissible T) (hP : P T.krullDimSucc)
    (hO : T.IsOrderBoundedByMult)
    (hft : LocallyOfFiniteType T.structMap) (hD : T.IsBalanced hft)
    (hjb : jj < T.boundary.length)
    (Yv : Sch) (q : Yv ⟶ Sp T.base) (h : Yv ⟶ scheme T)
    (hsm : AlgebraicGeometry.Smooth h) (hsu : AlgebraicGeometry.Surjective h)
    (hq : h ≫ structMap T = q) (E' : Bdy Yv)
    (hbe : SameNontrivialBoundary (T.pbA q h).boundary E')
    (htake : take (jj + 1) E' = take (jj + 1) (T.pbA q h).boundary)
    (hV2 : IsAdmissible $ T.pbB q h E')
    (hP2 : P (T.pbB q h E').krullDimSucc)
    (hO2 : (T.pbB q h E').IsOrderBoundedByMult)
    (hft2 : LocallyOfFiniteType
      (T.pbB q h E').structMap)
    (hD2 : (T.pbB q h E').IsBalanced hft2)
    (hjb2 : jj < (T.pbB q h E').boundary.length) :
    IsStrictPullbackBlowupSeq h (A $ T.pbB q h E').toSequenceOfBlowups
      (A T).toSequenceOfBlowups := by
  exact hspec.smooth_pullback_strict T hV hP hO hD hjb Yv q h hq E' hbe htake hV2 hP2 hO2 hD2 hjb2

theorem map_comap_append_drop {X1 X2 : Sch} (f : X1 ⟶ X2)
    (E Bd : Bdy X2) (Bd' : Bdy X1) (n : ℕ)
    (h : Bd' = Bd.map fun A' => comap A' f) :
    List.map (fun Dv : ISD X2 => comap Dv f) (E ++ Bd.drop n)
      = List.map (fun Dv : ISD X2 => comap Dv f) E ++ Bd'.drop n :=by simp_all
private theorem eqToHom_comp_projectionToBase {X} (s : SequenceOfBlowups X) {a b}
    (h : a = b) :
    eqToHom (congrArg (fun n => schemeAt s n) h) ≫ projectionToBase s b = projectionToBase s a := by
  subst h
  simp

private theorem lastMap_comp_projectionToBase {X' X} {g}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g t s) :
    D.lastMap ≫ projectionToBase s s.length = projectionToBase t t.length ≫ g := by
  have key := isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length D.comp D.comp_zero
    D.pullback t.length le_rfl
  rw [StrictPullbackBlowupSeq.lastMap_eq, assoc, eqToHom_comp_projectionToBase s D.length_eq]
  exact key.w

theorem boundary_eq_map_comap_strictPullbackComparisonMap {K : Type} [Field K] {XX' XX : Sch}
    {qq : XX' ⟶ Sp K} {gg : XX' ⟶ XX} [Flat gg]
    {II : ISD XX} {mm : ℕ} {EE : Bdy XX} {dd : BlowupSequenceData XX}
    (tt : MarkedBlowupSequenceData qq (II.comap gg) mm $ EE.map fun A => A.comap gg)
    (DD : StrictPullbackBlowupSeq gg tt.toMarkedSequenceOfBlowups.toSequenceOfBlowups dd.toSequenceOfBlowups)
    (hNd : ∀ i ≤ dd.length, IsLocallyNoetherian $ dd.obj i)
    (hNt : ∀ i ≤ tt.length, IsLocallyNoetherian $ tt.obj i)
    (i j : ℕ) (hi : i ≤ tt.length) (hij : i = j) :
    tt.boundary i =
      (dd.boundaryFrom EE j).map
        (fun A => A.comap $ tt.strictPullbackComparisonMap DD i hi ≫ eqToHom (congrArg (fun n => dd.obj n) hij)) := by
  subst hij
  simp [eqToHom_refl, comp_id]
  exact tt.boundary_eq_comap_strictPullbackComparisonMap DD hNd hNt i hi

private theorem balancedTunedSheaf_congr (k : Type) [CommRing k] [IsNoetherianRing k]
    {X : Sch} {p q} (hpq : p = q)
    (hp : LocallyOfFiniteType p)
    (hq : LocallyOfFiniteType q)
    {I J} (hIJ : I = J) {m n} (hmn : m = n) :
    @balancedTunedSheaf k _ _ X p hp I m = @balancedTunedSheaf k _ _ X q hq J n :=by simp_all
theorem boundary_eq_map_comap_pullbackMapAtLength [Flat g]
    (hNs : ∀ i ≤ s.length, IsLocallyNoetherian $ s.obj i)
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian $ t.obj i) :
    t.boundary t.length =
      (s.boundary s.length).map fun A => A.comap $ pullbackMapAtLength S g s t D := by
  have key := boundary_eq_map_comap_strictPullbackComparisonMap (dd := mbBd s) (II := tId S) (mm := tMu S)
    (EE := tBd S) (gg := g) t D hNs hNt t.length s.length le_rfl D.length_eq
  rwa [MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq s s.length le_rfl] at key

theorem pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism :
    pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ structMap S) =
      t.proj t.length ≫ structMap (pullbackTriple S g) := by
  have _i18 : pullbackMapAtLength S g s t D ≫ (s.proj s.length ≫ tMp S) = t.proj t.length ≫ (g ≫ tMp S) := by
    have h2 : pullbackMapAtLength S g s t D ≫ s.proj s.length = t.proj t.length ≫ g := by
      rw [projectionToBase_eq_toSequenceOfBlowups s s.length,
        projectionToBase_eq_toSequenceOfBlowups t t.length]
      exact lastMap_comp_projectionToBase D
    exact st_ (assoc _ _ _) $ tr_ (congrArg (fun ph_ => ph_ ≫ tMp S) h2) $ assoc _ _ _
  exact tr_ _i18 $ congrArg (fun f => lastP t ≫ f) $ (pullbackAlong_structureMorphism S Y (g ≫ tMp S) g).symm

section
variable [Smooth g]
section
variable (hftS : LocallyOfFiniteType (s.proj s.length ≫ structMap S)) (hftT : LocallyOfFiniteType (t.proj t.length ≫ structMap (pullbackTriple S g))) (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (hVc : IsAdmissible (MaxContactCoverData.derivedTriple S s hftS extra keep))
include hVc
theorem tunedIdealAtLength_comap_pullbackMapAtLength :
    comap (tunedIdealAtLength S s hftS) (pullbackMapAtLength S g s t D) = tunedIdealAtLength (pullbackTriple S g) t hftT := by
  have hmor := pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D
  let _a0 := pullbackMapAtLength S g s t D
  have hid : lastI t = cmI (lastI s) _a0 := by
    have hL := D.length_eq
    have key := ideal_eq_comap_controlledTransform (I := tId S) (m := tMu S) (E := tBd S)
      (d := mbBd s) t D s.isMarked.divisible t.length le_rfl
    refine tr_ key ?_
    rw [s.controlledTransform_eq_ideal t.length hL.le]
    exact comap_eq_comap_comp_eqToHom s.obj s.ideal hL _
  let _a1 := lastP s ≫ tMp S
  have hsm : Smooth _a1 := by
    have h0 := hVc.smooth
    rwa [structureMorphism_derivedTriple S s hftS extra keep] at h0
  have := hftS
  have := hftT
  have := smooth_pullbackMapAtLength S g s t D
  have : LocallyOfFiniteType
      (_a0 ≫ _a1) := by
    rwa [hmor]
  rw [tunedIdealAtLength_eq_balancedTunedSheaf, tunedIdealAtLength_eq_balancedTunedSheaf,
    ← balancedTunedSheaf_comap S.base _a1 _a0
      (lastI s) S.mult]
  exact balancedTunedSheaf_congr S.base hmor _ _ hid.symm
    (pullbackAlong_mult S Y (g ≫ tMp S) g).symm

theorem pullbackAlong_derivedTriple_eq :
    ((MaxContactCoverData.derivedTriple S s hftS extra keep).pullbackAlong (t.obj t.length)
          (pullbackMapAtLength S g s t D ≫ structMap (MaxContactCoverData.derivedTriple S s hftS extra keep))
          (pullbackMapAtLength S g s t D)).withBoundary
        (@append (t.obj t.length).IdealSheafData (comapBoundaryPullback S g s t D extra)
          ((t.boundary t.length).drop keep)) =
      MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT (comapBoundaryPullback S g s t D extra) keep := by
  have hstruct := pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D
  have hideal :=
    tunedIdealAtLength_comap_pullbackMapAtLength S g s t D hftS hftT extra keep hVc
  simp [pullbackAlong, withBoundary]
  congr 1
end

theorem nonempty_strictPullback_appendLowerDimReduction [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g]
    (hstar : MaxContactCoverProperties) (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) (j : ℕ)
    (hspec : IsBoundaryDivisorReduction P j (A j) B)
    (rc : (S' : MarkedIdealWithBoundary) → S'.krullDimSucc ≤ T.krullDimSucc → ℕ → S'.SequenceOfBlowups)
    (hrc : ∀ (S' : MarkedIdealWithBoundary) (h : S'.krullDimSucc ≤ T.krullDimSucc) (i : ℕ), rc S' h i = A i S')
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hftS : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
    (hftT : LocallyOfFiniteType (t.proj t.length ≫ structMap (pullbackTriple S g)))
    (hV : IsAdmissible S) (hm : 1 ≤ mult S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (hNs : ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i))
    (hV' : IsAdmissible (pullbackTriple S g))
    (hO' : ∀ x : ↥(pullbackTriple S g).scheme,
      orderAt (pullbackTriple S g).ideal x ≤ ((mult (pullbackTriple S g) : ℕ) : ENat))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    (hdim : (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc ≤ T.krullDimSucc)
    (hP : P (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc)
    (hVc : IsAdmissible (MaxContactCoverData.derivedTriple S s hftS extra keep))
    (hj : j < (extra ++ (s.boundary s.length).drop keep).length)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take keep,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : CSet (s.obj s.length)) = ∅)
    (hdim' : (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep).krullDimSucc ≤ T.krullDimSucc)
    (hP' : P (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep).krullDimSucc)
    (hVc' : (MaxContactCoverData.derivedTriple (pullbackTriple S g) t hftT
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap) keep).IsAdmissible)
    (hj' : j < (@append (t.obj t.length).IdealSheafData
      (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
      ((t.boundary t.length).drop keep)).length)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take keep,
      orderAtLeastLocus (t.ideal t.length) (pullbackTriple S g).mult ∩
        (Dv.support : CSet (t.obj t.length)) = ∅) :
    Nonempty (StrictPullbackBlowupSeq g
      (appendLowerDimReduction hinv T rc (pullbackTriple S g) t
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
        keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  have hsu : q10 (pullbackMapAtLength S g s t D) := by
    rw [pullbackMapAtLength_eq_lastMap]
    exact surjective_lastMap D
  have hm' := le_of_le_of_eq hm (pullbackAlong_mult S Y (g ≫ tMp S) g).symm
  let _a1 := p8 S s hftS extra keep
  have hb1 : tBd _a1
      = extra ++ (lastB s).drop keep := rfl
  let _m0 := _a1.pullbackAlong (lastO t) (pullbackMapAtLength S g s t D ≫ tMp _a1) $ pullbackMapAtLength S g s t D
  let _a4 := comapBoundaryPullback S g s t D extra
  let _a5 := (lastB t).drop keep
  have hbd : tBd _m0
      = _a4 ++ _a5 := by
    exact tr_ (pullbackAlong_boundary _a1
        (lastO t)
        (pullbackMapAtLength S g s t D ≫ tMp _a1)
        (pullbackMapAtLength S g s t D)) (map_comap_append_drop (pullbackMapAtLength S g s t D) extra (lastB s) (lastB t) keep (boundary_eq_map_comap_pullbackMapAtLength S g s t D hNs hNt))
  have hbe : SameNontrivialBoundary
      _m0.boundary
      (_a4 ++ _a5) := by
    have hrefl : ∀ L L' : List (lastO t).IdealSheafData,
        L = L' → SameNontrivialBoundary L L' := by
      rintro L L' rfl
      exact MarkedIdealWithBoundary.SameNontrivialBoundary.refl L
    exact hrefl _ _ hbd
  have hkey :=
    pullbackAlong_derivedTriple_eq S g s t D hftS hftT extra keep hVc
  have hjb1 := hj
  rw [← hb1] at hjb1
  let _a2 := ISD (lastO s)
  let _a3 := pullbackTriple S g
  have hO2' := isOrderBoundedByMult_derivedTriple hstar _a3 hV' hm' hO' t hftT
      (extra.map fun E : _a2 => cmI E D.lastMap) keep hVc'
  have hD2' := isBalanced_derivedTriple hstar _a3 hV' hm' hO' t hftT
      (extra.map fun E : _a2 => cmI E D.lastMap) keep hVc'
  have hfacts : ∀ T' : MarkedIdealWithBoundary,
      T' = p8 _a3 t hftT
        (extra.map fun E : _a2 => cmI E D.lastMap) keep →
      tAd T' ∧ P T'.krullDimSucc ∧ T'.IsOrderBoundedByMult ∧ j < bLen T' ∧
        ∀ hft, T'.IsBalanced hft := by
    rintro T' rfl
    exact ⟨hVc', hP', hO2', hj', fun _ => hD2'⟩
  obtain ⟨hV2, hP2, hO2, hjb2, hD2⟩ := hfacts _ hkey
  have h0 := isStrictPullbackBlowupSeq_of_isBoundaryDivisorReduction hspec _a1
      hVc hP (isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS extra keep hVc) _ (isBalanced_derivedTriple hstar S hV hm hO s hftS extra keep hVc) hjb1 (lastO t)
      (pullbackMapAtLength S g s t D ≫ tMp _a1)
      (pullbackMapAtLength S g s t D) (smooth_pullbackMapAtLength S g s t D) hsu rfl
      (_a4 ++ _a5) hbe (congrArg (fun l => take (j + 1) l) hbd.symm)
      hV2 hP2 hO2 hV2.locallyOfFiniteType (hD2 hV2.locallyOfFiniteType) hjb2
  have hspb : IsStrictPullbackBlowupSeq (pullbackMapAtLength S g s t D)
      (A j (p8 _a3 t hftT
        (extra.map fun E : _a2 => cmI E D.lastMap) keep)).toSequenceOfBlowups
      (A j _a1).toSequenceOfBlowups :=
    IsStrictPullbackBlowupSeq.of_eq (eq_of_heq ((A j).toSequenceOfBlowups_heq_of_eq hkey)) rfl h0
  obtain ⟨hmkS, hSeq, -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A B j hspec rc hrc S hV hm hO s
    extra keep hftS hdim hP hVc hj hsep
  obtain ⟨hmkT, hTeq, -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A B j hspec rc hrc _a3
    hV' hm' hO' t (extra.map fun E : _a2 => cmI E D.lastMap) keep
    hftT hdim' hP' hVc' hj' hsep'
  rw [hSeq, hTeq]
  refine ⟨(MarkedBlowupSequenceData.isStrictPullbackBlowupSeq_append g s _ t _ hinv D ?_).toStrictPullbackBlowupSeq⟩
  exact (IsStrictPullbackBlowupSeq.of_eq
    (toMarkedBlowupSequenceData_toSequenceOfBlowups _ _ _ _ _ hmkT).symm
    (toMarkedBlowupSequenceData_toSequenceOfBlowups _ _ _ _ _ hmkS).symm
    ((hspb.of_isomorphic_pullback (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm).of_isomorphic_base
      (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm)).toStrictPullbackBlowupSeq
end

end LowerDimReductionPullback

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

theorem list_prod_map_comap {X Y : Sch} (q : X ⟶ Y) (Ls : Bdy Y) :
    (Ls.map fun A => comap A q).prod = Ls.prod.comap q := by
  induction Ls with
  | nil => simp
  | cons a L ih => simp [comap_mul, ih]

theorem append_drop_eq_map_comap {X Y : Sch} (g : Y ⟶ X)
    (Es Bs : Bdy X) (Et Bt : Bdy Y) (keep : ℕ)
    (hE : Et = Es.map fun A => comap A g) (hB : Bt = Bs.map fun A => comap A g) :
    Et ++ Bt.drop keep = (Es ++ Bs.drop keep).map fun A => comap A g :=by simp_all
section
variable {T T' : MarkedIdealWithBoundary} (h : T = T')
include h
private theorem isAdmissible_of_eq (hv : IsAdmissible T') :
    IsAdmissible T := by
  subst h
  exact hv

private theorem isBalanced_of_eq
    (hft : LocallyOfFiniteType T.structMap)
    (hft' : LocallyOfFiniteType T'.structMap)
    (hd : T'.IsBalanced hft') : T.IsBalanced hft := by
  subst h
  exact hd

theorem lt_boundary_length_of_eq {j : ℕ}
    (hj : j < T'.boundary.length) : j < T.boundary.length := by
  subst h
  exact hj

private theorem isOrderBoundedByMult_of_eq
    (ho : T'.IsOrderBoundedByMult) : T.IsOrderBoundedByMult := by
  subst h
  exact ho
end

theorem isPullback_projectionToBase_of_index_eq {X Y Z : Sch} (b : SequenceOfBlowups X) {i j : ℕ}
    (h : i = j) {σ : Z ⟶ schemeAt b i} {v : Z ⟶ Y} {g : Y ⟶ X}
    (hp : IsPullback σ v (projectionToBase b i) g) :
    IsPullback (σ ≫ eqToHom (congrArg (fun n => schemeAt b n) h)) v (projectionToBase b j) g := by
  subst h
  simpa using hp

theorem isStrictPullback_of_morphism_eq {X' X : Sch} {g g' : X' ⟶ X} (h : g = g')
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (hd : IsStrictPullbackBlowupSeq g t s) :
    IsStrictPullbackBlowupSeq g' t s := by
  subst h
  exact hd

def castStrictPullbackBlowupSeq {X' X : Sch} {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s s' : SequenceOfBlowups X} (ht : t = t') (hs : s = s')
    (D : StrictPullbackBlowupSeq g t s) : StrictPullbackBlowupSeq g t' s' := by
  subst ht
  subst hs
  exact D

private theorem pred_dim_of_eq (P : ℕ → Prop) {T T' : MarkedIdealWithBoundary} (h : T = T')
    (hp : P T'.krullDimSucc) : P T.krullDimSucc := by
  subst h
  exact hp

theorem isStrictPullback_of_markedBlowupSequenceData_eq {k k' : Type} [Field k] [Field k']
    {X X' : Sch}
    {p : X ⟶ Sp k} {p' : X' ⟶ Sp k'}
    {I : ISD X} {I' : ISD X'} {m m' : ℕ}
    {E : Bdy X} {E' : Bdy X'} {g : X' ⟶ X}
    {a b : MarkedBlowupSequenceData p I m E} {a' b' : MarkedBlowupSequenceData p' I' m' E'}
    (ha : a = b) (ha' : a' = b')
    (H : IsStrictPullbackBlowupSeq g a'.toMarkedSequenceOfBlowups.toSequenceOfBlowups a.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g b'.toMarkedSequenceOfBlowups.toSequenceOfBlowups b.toMarkedSequenceOfBlowups.toSequenceOfBlowups :=by simp_all
theorem markedIdealWithBoundary_mk_eq_of_eq {k : Type} [Field k] {X : Sch}
    (q : X ⟶ Sp k) {I I' : ISD X} {m m' : ℕ}
    {E E' : Bdy X} (hI : I = I') (hm : m = m') (hE : E = E') :
    mk k X q I m E = mk k X q I' m' E' :=by simp_all
theorem isStrictPullback_of_markedIdealWithBoundary_eq (A : PrincipalizationAssignment)
    {T T' : MarkedIdealWithBoundary} (h : T = T')
    {X : Sch} {B : SequenceOfBlowups X} {ph_ : scheme T ⟶ X} {ph' : scheme T' ⟶ X} (hph : HEq ph_ ph')
    (hd : IsStrictPullbackBlowupSeq ph_ (A T).toSequenceOfBlowups B) :
    IsStrictPullbackBlowupSeq ph' (A T').toSequenceOfBlowups B := by
  subst h
  cases hph
  exact hd

def DerivIdealSheafIterateCommBaseChange : Prop :=
  ∀ (k L : Type) [Field k] [Field L] [CharZero k] [CharZero L] (f : k →+* L)
    (X Y : Sch) (pX : X ⟶ Sp k) (pY : Y ⟶ Sp L)
    [Smooth pX] [LocallyOfFiniteType pX]
    [Smooth pY] [LocallyOfFiniteType pY]
    (q : Y ⟶ X),
    IsPullback q pY pX (specMapOfFieldHom k L f) →
      ∀ (r : ℕ) (I : ISD X),
        derivIdealSheafIterate L pY r (comap I q) = comap (derivIdealSheafIterate k pX r I) q

theorem balancedTunedSheaf_comap_of_isPullback (hderiv : DerivIdealSheafIterateCommBaseChange)
    (k L : Type) [Field k] [Field L] [CharZero k] [CharZero L] (f : k →+* L)
    {X Y : Sch} (pX : X ⟶ Sp k) (pY : Y ⟶ Sp L)
    [Smooth pX] [LocallyOfFiniteType pX]
    [Smooth pY] [LocallyOfFiniteType pY]
    (q : Y ⟶ X) (hq : IsPullback q pY pX $ specMapOfFieldHom k L f)
    (I : ISD X) (m : ℕ) :
    balancedTunedSheaf L pY (comap I q) m = comap (balancedTunedSheaf k pX I m) q := by
  rw [balancedTunedSheaf_eq, balancedTunedSheaf_eq, tunedSheaf_eq_iSup, tunedSheaf_eq_iSup, comap_iSup]
  refine iSup_congr fun c => ?_
  rw [← list_prod_map_comap q, map_map]
  refine congrArg prod $ map_congr_left fun r _ => ?_
  simp [comp_apply, hderiv k L f X Y pX pY q hq r I,
    comap_pow]

namespace MarkedBlowupSequenceData

theorem isStrictPullbackBlowupSeq_append_of_field {k k' : Type} [Field k] [Field k']
    {X X' : Sch} {p : X ⟶ Sp k} {p' : X' ⟶ Sp k'}
    {I : ISD X} {I' : ISD X'} {m m' : ℕ}
    {E : Bdy X} {E' : Bdy X'} (g : X' ⟶ X)
    (s : MarkedBlowupSequenceData p I m E)
    (u : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length)
    (s' : MarkedBlowupSequenceData p' I' m' E')
    (u' : MarkedBlowupSequenceData (s'.proj s'.length ≫ p') (s'.ideal s'.length) m'
      (s'.boundary s'.length))
    (hinv : ComapIsoInvariance)
    (D : StrictPullbackBlowupSeq g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap u'.toMarkedSequenceOfBlowups.toSequenceOfBlowups u.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g ((append s' u' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups)
      ((append s u hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) :=
  FunctorialResolution.EmbeddedResolution.isStrictPullbackBlowupSeq_append (g := g) s.toBlowupSequenceData u.toBlowupSequenceData s'.toBlowupSequenceData
    u'.toBlowupSequenceData D D'

end MarkedBlowupSequenceData

namespace LowerDimReductionPullback

variable (S : MarkedIdealWithBoundary) (L : Type) [Field L] (f : S.base →+* L)
  (s : S.mbs)
  (t : MarkedBlowupSequenceData (bc S f).structMap (bc S f).ideal
      (bc S f).mult (bc S f).boundary)

section
variable (D : StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f)) t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
include D
theorem length_eq_of_strictPullbackBlowupSeq :
    t.length = s.length := by
  have h := D.length_eq
  rwa [toMarkedSequence_length, toMarkedSequence_length] at h

noncomputable def baseChangeMapAtLength :
    t.obj t.length ⟶ s.obj s.length :=
  D.lastMap


@[reducible] noncomputable def comapBoundaryBaseChange
    (Ls : List (s.obj s.length).IdealSheafData) : List (t.obj t.length).IdealSheafData :=
  Ls.map fun A => comap A $ baseChangeMapAtLength S L f s t D

theorem nonempty_strictPullbackSeq_appendLowerDimReduction_baseChange
    [CharZero L]
    [Flat (pullback.fst S.structMap (specMapOfFieldHom S.base L f))]
    (hderiv : DerivIdealSheafIterateCommBaseChange) (hstar : MaxContactCoverProperties) (hinv : ComapIsoInvariance)
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment) (Bp : PrincipalizationAssignment) (j : ℕ)
    (hspec : IsBoundaryDivisorReduction P j (A j) Bp)
    (T T' : MarkedIdealWithBoundary)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
    (hftS : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
    (hftT : LocallyOfFiniteType
      (t.proj t.length ≫ structMap (bc S f)))
    (hV : IsAdmissible S) (hm : 1 ≤ mult S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (hNs : ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i))
    (hV' : IsAdmissible (bc S f))
    (hO' : ∀ x : ↥(bc S f).scheme,
      orderAt (bc S f).ideal x ≤ (mult (bc S f) : ENat))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    (hdim : (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc ≤ T.krullDimSucc)
    (hP : P (MaxContactCoverData.derivedTriple S s hftS extra keep).krullDimSucc)
    (hVc : IsAdmissible (MaxContactCoverData.derivedTriple S s hftS extra keep))
    (hj : j < (extra ++ (s.boundary s.length).drop keep).length)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take keep,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : CSet (s.obj s.length)) = ∅)
    (hdim' : (MaxContactCoverData.derivedTriple (bc S f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).krullDimSucc ≤ T'.krullDimSucc)
    (hP' : P (MaxContactCoverData.derivedTriple (bc S f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).krullDimSucc)
    (hVc' : (MaxContactCoverData.derivedTriple (bc S f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).IsAdmissible)
    (hj' : j < (@append (t.obj t.length).IdealSheafData (comapBoundaryBaseChange S L f s t D extra)
      ((t.boundary t.length).drop keep)).length)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take keep,
      orderAtLeastLocus (t.ideal t.length) (bc S f).mult ∩
        (Dv.support : CSet (t.obj t.length)) = ∅)
    (hVb : IsAdmissible ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f))
    (hPb : P ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).krullDimSucc)
    (hOb : ∀ x : ↥((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).scheme,
      orderAt ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).ideal x ≤
        (mult (MaxContactCoverData.derivedTriple S s hftS extra keep) : ENat))
    (hDb : ∀ hft : LocallyOfFiniteType
        ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).structMap,
      ((MaxContactCoverData.derivedTriple S s hftS extra keep).baseChange L f).IsBalanced hft) :
    Nonempty (StrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (appendLowerDimReduction hinv T' (fun S' _ i => A i S') (bc S f) t
        (extra.map fun E : (s.obj s.length).IdealSheafData => E.comap D.lastMap)
        keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendLowerDimReduction hinv T (fun S' _ i => A i S') S s extra keep
        j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  let _a7 := p48 S s hftS extra keep
  let _c0 := p8 S s hftS extra keep
  let _a3 := comapBoundaryBaseChange S L f s t D extra
  let _c1 := p8 (bcT S f) t hftT _a3 keep
  let _c2 := _a3
  let _c3 := bcT S f
  let _c4 := specMapOfFieldHom S.base L f
  classical
  have hlen : t.length = s.length := length_eq_of_strictPullbackBlowupSeq S L f s t D
  have hm' : 1 ≤ tMu _c3 := hm
  obtain ⟨hmk1, heq1, -⟩ :=
    LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A Bp j hspec (fun S' _ i => A i S')
      (fun _ _ _ => rfl) S hV hm hO s extra keep hftS hdim hP hVc hj hsep
  obtain ⟨hmk2, heq2, -⟩ :=
    LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T' P A Bp j hspec (fun S' _ i => A i S')
      (fun _ _ _ => rfl) _c3 hV' hm' hO' t _c2 keep
      hftT hdim' hP' hVc' hj' hsep'
  have hcz : CharZero S.base := hV.charZero
  let _a5 := lastP s ≫ tMp S
  have hsmA : Smooth
      _a5 :=
    hVc.smooth
  have hsmB : Smooth
      (lastP t ≫ tMp _c3 :
        lastO t ⟶ Sp L) :=
    hVc'.smooth
  have hftA : LocallyOfFiniteType
      _a5 :=
    hftS
  have hftB : LocallyOfFiniteType
      (lastP t ≫ tMp _c3 :
        lastO t ⟶ Sp L) :=
    hftT
  let _a4 := pullback.fst S.structMap _c4
  have hbase : IsPullback (D.comp t.length le_rfl)
      (t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase t.length)
      (s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase t.length)
      _a4 :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism
      _a4
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups t.length D.comp D.comp_zero D.pullback
      t.length le_rfl
  have hbase3 := (isPullback_projectionToBase_of_index_eq s.toMarkedSequenceOfBlowups.toSequenceOfBlowups hlen hbase).paste_vert
    (m186 S.structMap _c4)
  have e1 : t.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase t.length = lastP t :=
    toMarkedSequence_projectionToBase t t.length
  have e2 : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase s.length = lastP s :=
    toMarkedSequence_projectionToBase s s.length
  have hsq := hbase3
  rw [e2, e1] at hsq
  let _a1 := specMapOfFieldHom _c0.base L f
  have hsq1 : IsPullback D.lastMap (t.proj t.length ≫ tMp _c3)
      _c0.structMap
      _a1 := hsq
  obtain ⟨ι, hfst, hsnd⟩ :
      ∃ e : lastO t ≅ pullback _c0.structMap
          _a1,
        (isoH e ≫ pullback.fst _c0.structMap
            _a1 = D.lastMap) ∧
          (isoH e ≫ pullback.snd _c0.structMap
              _a1
            = lastP t ≫ tMp _c3) :=
    ⟨hsq1.isoPullback, hsq1.isoPullback_hom_fst, hsq1.isoPullback_hom_snd⟩
  have hisoio : IsIso ι.hom := inferInstance
  have hsmio : AlgebraicGeometry.Smooth ι.hom := inferInstance
  have hsurjio : q10 ι.hom := inferInstance
  have hpi := ideal_eq_comap_controlledTransform (d := mbBd s) (I := tId S) (m := tMu S)
    (E := tBd S) (g := _a4) t D ((isMarked_toBlowupSequenceData s).divisible)
    t.length le_rfl
  have hpb := boundary_eq_comap_strictPullbackComparisonMap (d := mbBd s) (I := tId S) (m := tMu S)
    (E := tBd S) (g := _a4) t D hNs hNt
    t.length le_rfl
  have hpm : strictPullbackComparisonMap (q := tMp _c3)
      (g := _a4) (I := tId S) (m := tMu S)
      (E := tBd S) (d := mbBd s) t D t.length le_rfl ≫
        eqToHom (congrArg s.obj hlen) = D.lastMap := rfl
  have hIdealLast : lastI t = cmI (lastI s) D.lastMap := by
    refine tr_ hpi ?_
    rw [toBlowupSequenceData_controlledTransform_eq s t.length (le_of_eq hlen),
      MarkedBlowupSequenceData.ideal_congr_index s hlen, ← comap_comp]
    exact congrArg (fun q => cmI (lastI s) q) hpm
  have hBoundaryLast : lastB t
      = (lastB s).map (·.comap D.lastMap) := by
    refine tr_ hpb ?_
    rw [toBlowupSequenceData_boundary_eq_boundary_of_le s t.length (le_of_eq hlen),
      MarkedBlowupSequenceData.boundary_congr_index s hlen, map_map]
    refine map_congr_left fun A _ => ?_
    simp only [m116, ← m56]
    exact congrArg A.comap hpm
  have htuned := balancedTunedSheaf_comap_of_isPullback hderiv S.base L f
    (lastP s ≫ tMp S) (lastP t ≫ tMp _c3)
    D.lastMap hsq (lastI s) S.mult
  let _a0 := _c0.baseChange L f
  have hid : tId _c1
      = _a0.ideal.comap ι.hom := by
    have hA : _a0.ideal.comap ι.hom
        = cmI (LowerDimReductionPullback.tunedIdealAtLength S s hftS) D.lastMap := by
      refine m32 (congrArg (·.comap ι.hom)
        (baseChange_ideal _c0 L f)) ?_
      refine m32 (m56 _ _ _).symm ?_
      exact m32 (congrArg
        _c0.ideal.comap hfst) (congrArg (·.comap D.lastMap) (LowerDimReductionPullback.ideal_derivedTriple S s hftS extra keep))
    have hB : ideal _c1
        = cmI (LowerDimReductionPullback.tunedIdealAtLength S s hftS) D.lastMap := by
      rw [LowerDimReductionPullback.ideal_derivedTriple _c3 t hftT _c2 keep,
        LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf _c3 t hftT, LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf S s hftS,
        hIdealLast]
      exact htuned
    exact tr_ hB hA.symm
  have hbd : tBd _c1
      = (tBd _a0).map
          (·.comap ι.hom) := by
    let _a6 := extra ++ (lastB s).drop keep
    have r1 : (tBd _a0).map
          (·.comap ι.hom)
        = _a6.map (·.comap D.lastMap) := by
      refine m32 (congrArg (fun l => l.map (·.comap ι.hom))
        (baseChange_boundary
          _c0 L f)) ?_
      have _i19 : (_c0.boundary.map (cmI · $ pullback.fst _c0.structMap _a1)).map (·.comap ι.hom) = _c0.boundary.map (cmI · $ isoH ι ≫ pullback.fst _c0.structMap _a1) := by
        let h := pullback.fst _c0.structMap
          _a1
        rw [map_map]
        refine map_congr_left fun A _ => ?_
        simp
      refine m32 _i19 ?_
      exact m32 (congrArg (fun m =>
        _c0.boundary.map
          (·.comap m)) hfst) (congrArg (fun l => l.map (·.comap D.lastMap)) _a7)
    have r2 : tBd _c1
        = _a6.map (·.comap D.lastMap) := by
      exact trans (p48 _c3 t hftT
        _c2 keep) (append_drop_eq_map_comap D.lastMap extra (lastB s) _c2 (lastB t) keep rfl hBoundaryLast)
    exact tr_ r2 r1.symm
  have hTriple : _a0.pullbackAlong
        (t.obj t.length)
        _c1.structMap ι.hom
      = p8 _c3 t hftT _c2 keep :=
    markedIdealWithBoundary_mk_eq_of_eq _ hid.symm rfl hbd.symm
  have hO1 : _c0.IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hD1 : _c0.IsBalanced hVc.locallyOfFiniteType :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  have hj1 : j < bLen _c0 :=
    lt_of_lt_of_eq hj (congrArg length
      _a7).symm
  have hO1b : _a0.IsOrderBoundedByMult :=
    (isOrderBoundedByMult_iff _).mpr hOb
  have hlenb : bLen _a0
      = bLen _c0 :=
    (congrArg length
      (baseChange_boundary _c0 L f)).trans
      (length_map _)
  have hj1b :
      j < bLen _a0 :=
    lt_of_lt_of_eq hj1 hlenb.symm
  have hbc := hspec.isStrictPullbackBlowupSeq_baseChange _c0
    hVc hP hO1 hD1 hj1 L f hVb hPb hO1b (hDb hVb.locallyOfFiniteType) hj1b
  have hO2 : _c1.IsOrderBoundedByMult :=
    LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar _c3 hV' hm' hO' t hftT
      _c2 keep hVc'
  have hD2b : _c1.IsBalanced hVc'.locallyOfFiniteType :=
    LowerDimReductionPullback.isBalanced_derivedTriple hstar _c3 hV' hm' hO' t hftT
      _c2 keep hVc'
  have hj2 : j < bLen _c1 :=
    lt_of_lt_of_eq hj' (congrArg length
      (p48 _c3 t hftT
        _c2 keep)).symm
  have hStrictPullback := @IsBoundaryDivisorReduction.isStrictPullbackBlowupSeq_of_smooth_surjective P j (A j) Bp hspec
    _a0 hVb hPb hO1b
    (hDb hVb.locallyOfFiniteType) hj1b (t.obj t.length)
    _c1.structMap
    ι.hom hsmio hsurjio hsnd
    (isAdmissible_of_eq hTriple hVc') (pred_dim_of_eq P hTriple hP')
    (isOrderBoundedByMult_of_eq hTriple hO2)
    (isBalanced_of_eq hTriple _ _ hD2b)
    (lt_boundary_length_of_eq hTriple hj2)
  have hD'0 := ((isStrictPullback_of_morphism_eq hfst $ (isStrictPullback_of_markedIdealWithBoundary_eq (A j) hTriple (HEq.refl ι.hom) hStrictPullback).comp hbc).of_isomorphic_pullback (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm).of_isomorphic_base
    (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _).symm
  have hE1 := toMarkedBlowupSequenceData_toSequenceOfBlowups
    (ofSequenceOfBlowups (A j _c0).toSequenceOfBlowups)
    (lastP s ≫ tMp S) (lastI s) S.mult (lastB s) hmk1
  have hE2 := toMarkedBlowupSequenceData_toSequenceOfBlowups
    (ofSequenceOfBlowups (A j _c1).toSequenceOfBlowups)
    (lastP t ≫ tMp _c3) (lastI t) _c3.mult
    (lastB t) hmk2
  have main := isStrictPullback_of_markedBlowupSequenceData_eq heq1.symm heq2.symm
    (MarkedBlowupSequenceData.isStrictPullbackBlowupSeq_append_of_field
      _a4 s _ t _ hinv D (castStrictPullbackBlowupSeq hE2.symm hE1.symm hD'0.toStrictPullbackBlowupSeq))
  exact ⟨main.toStrictPullbackBlowupSeq⟩
end

end LowerDimReductionPullback





namespace MaxContactOpenCover


theorem isLocalIsomorphism_fst_of_isPullback {P X Y Z : Sch}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hsq : IsPullback fst snd f g)
    (hg : MaxContactFunctoriality.IsLocalIsomorphism g) :
    MaxContactFunctoriality.IsLocalIsomorphism fst := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hg $ bsM snd x
  exact ⟨_, hxU, (fun hsq hg => m98 hsq.flip hg)
    ((isPullback_morphismRestrict snd U).flip.paste_horiz hsq) hU⟩

section
variable (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) (i : (chosenCoverData T hv).idx)
abbrev coverPiece : Sch :=
  (((chosenCoverData T hv).opens i : T.scheme.Opens) : Sch)

abbrev coverPieceio :
    coverPiece T hv i ⟶ scheme (MaxContactCoverData.cT hv) :=
  Sigma.ι (fun j : (chosenCoverData T hv).idx =>
    (((chosenCoverData T hv).opens j : T.scheme.Opens) : Sch)) i
end

instance instIsOpenImmersionStario (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)
    (i : (chosenCoverData T hv).idx) :
    IsOpenImmersion $ coverPieceio T hv i :=
  by
  have h : IsOpenImmersion $ Sigma.ι (fun j : (chosenCoverData T hv).idx =>
      (((chosenCoverData T hv).opens j : T.scheme.Opens) : Sch)) i :=
    inferInstance
  exact h

section
variable (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)
section
variable (i : (chosenCoverData T hv).idx)
abbrev coverTripleOpen :
    (MaxContactCoverData.cT hv).scheme.Opens :=
  (coverPieceio T hv i).opensRange

abbrev coverTriplePiece : Sch :=
  ((coverTripleOpen T hv i : (MaxContactCoverData.cT hv).scheme.Opens) : Sch)

def coverPieceIso :
    coverPiece T hv i ≅ coverTriplePiece T hv i :=
  isoOfRangeEq (coverPieceio T hv i) (coverTripleOpen T hv i).i $ (((coverTripleOpen T hv i).range_ι).symm)

theorem etale_coverPieceIso_inv_comp_map {n}
    (c : EtaleChart T.structMap ((chosenCoverData T hv).opens i) n) :
    Etale $ (coverPieceIso T hv i).inv ≫ c.map := by
  have := c.isEtale
  let _a0 := coverPieceIso T hv i
  have : IsIso _a0.inv := inferInstance
  have : IsOpenImmersion _a0.inv := inferInstance
  have : Etale _a0.inv := inferInstance
  infer_instance

theorem coverPieceIso_inv_comp_coverPieceio :
    (coverPieceIso T hv i).inv ≫ coverPieceio T hv i = (coverTripleOpen T hv i).i := by
  apply lift_fac

theorem restrictIdeal_coverTripleOpen
    (J : (MaxContactCoverData.cT hv).scheme.IdealSheafData) :
    restrictIdeal J (coverTripleOpen T hv i) = (J.comap $ coverPieceio T hv i).comap (coverPieceIso T hv i).inv := by
  simp [restrictIdeal_eq_comap_io, ← coverPieceIso_inv_comp_coverPieceio T hv i,
    comap_comp]

theorem coverPieceio_comp_coverMap :
    coverPieceio T hv i ≫ MaxContactCoverData.coverMap T hv =
      ((chosenCoverData T hv).opens i).ι := by
  rw [coverMap_eq_sigmaOpensDesc]
  exact sigma_io_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens i

theorem coverTripleOpen_io_comp_coverMap :
    (coverTripleOpen T hv i).i ≫ MaxContactCoverData.coverMap T hv =
      (coverPieceIso T hv i).inv ≫ ((chosenCoverData T hv).opens i).ι := by
  let _a0 := isoI $ coverPieceIso T hv i
  calc (coverTripleOpen T hv i).i ≫ p12 T hv
      = (_a0 ≫ coverPieceio T hv i) ≫ p12 T hv := by rw [coverPieceIso_inv_comp_coverPieceio T hv i]
    _ = _a0 ≫ (coverPieceio T hv i ≫ p12 T hv) :=
        assoc _ _ _
    _ = _a0 ≫ opI ((chosenCoverData T hv).opens i) := by
        rw [coverPieceio_comp_coverMap T hv i]

section
variable {n} (c : EtaleChart T.structMap ((chosenCoverData T hv).opens i) n)
def coverEtaleChart :
    EtaleChart (MaxContactCoverData.coverMap T hv ≫ structMap T) (coverTripleOpen T hv i) n where
  map := (coverPieceIso T hv i).inv ≫ c.map
  comp_struct := by
    let _a2 := (coverTripleOpen T hv i).i
    have h1 := c.comp_struct
    have h2 := coverTripleOpen_io_comp_coverMap T hv i
    let _a0 := (coverPieceIso T hv i).inv
    let _a1 := ((chosenCoverData T hv).opens i).ι
    calc (_a0 ≫ c.map) ≫ affineSpaceFinToSpec T.base n
        = _a0 ≫ (c.map ≫ affineSpaceFinToSpec T.base n) := assoc _ _ _
      _ = _a0 ≫ (_a1 ≫ structMap T) := by
          rw [h1]
      _ = (_a0 ≫ _a1) ≫ structMap T :=
          (assoc _ _ _).symm
      _ = (_a2 ≫ MaxContactCoverData.coverMap T hv) ≫ structMap T := by rw [h2]
      _ = _a2 ≫ (MaxContactCoverData.coverMap T hv ≫ structMap T) :=
          assoc _ _ _
  isEtale := etale_coverPieceIso_inv_comp_map T hv i c

theorem coverEtaleChart_coordIdeal
    S :
    (coverEtaleChart T hv i c).coordIdeal S = (c.coordIdeal S).comap (coverPieceIso T hv i).inv := by
  let _a0 := coverPieceIso T hv i
  let _a1 := coordSubspaceIdeal T.base n S
  have key : _a1.comap (isoI _a0 ≫ c.map)
      = (_a1.comap c.map).comap _a0.inv := by
    rw [comap_comp]
  exact tr_ (p33 (coverEtaleChart T hv i c) S) $ tr_ key (congrArg (·.comap _a0.inv) $ p33 c S).symm
end
end

theorem exists_affineOpen_maxContactCoord_or_disjoint_locus
    [LocallyOfFiniteType T.structMap]
    (h : ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((tunedMult T : ℕ) : ENat))
    (x : ↥T.scheme) :
    ∃ (V : T.scheme.Opens) (J : (V : Sch).IdealSheafData),
      x ∈ V ∧ IsAffineOpen V ∧
        ((Disjoint (orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) $ tunedMult T)
              (V : CSet T.scheme) ∧ J = ⊤) ∨
          ∃ (n : ℕ) (c : EtaleChart T.structMap V n) (j : Fin n),
            J = c.coordIdeal {j} ∧
              MaxContactReduction.IsMaxContactCoord T.base T.structMap
                (MaxContactCoverData.balancedTunedIdeal T hv) (tunedMult T) c j) := by
  let _a0 := orderAtLeastLocus (p29 T hv) $ tunedMult T
  classical
  have := hv.charZero
  have := hv.smooth
  by_cases hx : x ∈ _a0
  have hord :=
    le_antisymm (h x) $ (mem_orderAtLeastLocus_iff _ _ _).1 hx
  obtain ⟨V, hVaff, hxV, n, c, j, hmc, -⟩ :=
    exists_isMaxContactCoord T.base T.structMap (p29 T hv) (one_le_tuningExponent T.mult) x hord
  exact ⟨V, c.coordIdeal {j}, hxV, hVaff, inr ⟨n, c, j, rfl, hmc⟩⟩
  have hcl : IsClosed
      _a0 :=
    isClosed_orderAtLeastLocus T.base T.structMap _ _
  obtain ⟨V, n, hxV, hVW, hVaff, -⟩ :=
    exists_etaleChart_le T.structMap x
      ⟨_a0ᶜ,
        hcl.isOpen_compl⟩ hx
  refine ⟨V, ⊤, hxV, hVaff, inl ⟨?_, rfl⟩⟩
  refine Set.disjoint_left.2 ?_
  intro y hyS hyV
  exact (hVW hyV) hyS

theorem exists_mem_coverTripleOpen
    x :
    ∃ i : (chosenCoverData T hv).idx, x ∈ coverTripleOpen T hv i := by
  let _a0 := chosenCoverData T hv
  obtain ⟨⟨i, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk
    (fun j =>
      ((_a0.opens j) : Sch))).surjective x
  refine ⟨i, ?_⟩
  show x ∈ range (Sigma.ι (fun j =>
    ((_a0.opens j) : Sch)) i).base
  refine ⟨y, ?_⟩
  rw [← hy]
  simp

section
variable (hgood : IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv) (tunedMult T))
include hgood
theorem isAffine_coverTriple_scheme :
    IsAffine (MaxContactCoverData.cT hv).scheme :=
  isAffine_sigmaOpens T.scheme (chosenCoverData T hv).opens hgood.isAffine

theorem quasiCompact_coverMap_comp_structureMorphism :
    QuasiCompact $ MaxContactCoverData.coverMap T hv ≫ structMap T := by
  have : IsAffine $ (chosenCoverData T hv).disjointUnion :=
    isAffine_coverTriple_scheme T hv hgood
  have : IsAffine (p7 hv).scheme :=
    isAffine_coverTriple_scheme T hv hgood
  have : Subsingleton $ Sp T.base := inferInstance
  constructor
  intro U _hU _hUc
  by_cases hUe : U = ∅
  subst hUe
  rw [preimage_empty]
  exact isCompact_empty
  have hUu : U = univ := by
    obtain ⟨u, hu⟩ := mpr_ nonempty_iff_ne_empty hUe
    refine eq_univ_of_forall fun z => ?_
    rwa [m111 z u]
  subst hUu
  rw [preimage_univ]
  exact isCompact_univ
end

theorem isLocalIsomorphism_coverMap :
    MaxContactFunctoriality.IsLocalIsomorphism $ MaxContactCoverData.coverMap T hv := by
  intro x
  obtain ⟨i, hxi⟩ := exists_mem_coverTripleOpen T hv x
  have hps_ : IsOpenImmersion $ opI (coverTripleOpen T hv i) ≫ p12 T hv := by
    rw [coverTripleOpen_io_comp_coverMap T hv i]
    infer_instance
  exact ⟨coverTripleOpen T hv i, hxi, hps_⟩

def tunedTriple : MarkedIdealWithBoundary where
  base := T.base
  scheme := scheme T
  structMap := structMap T
  ideal := MaxContactCoverData.balancedTunedIdeal T hv
  mult := tunedMult T
  boundary := boundary T







theorem isAdmissible_tunedTriple
    (hnz : NonzeroOnComponents $ MaxContactCoverData.balancedTunedIdeal T hv) :
    IsAdmissible $ tunedTriple T hv :=
  { charZero := hv.charZero
    locallyOfFiniteType := hv.locallyOfFiniteType
    nonzeroOnComponents := hnz
    one_le_mult := one_le_tuningExponent T.mult
    quasiCompact := hv.quasiCompact
    smooth := hv.smooth
    snc := hv.snc }

theorem coverTriple_eq_tunedTriple_pullbackAlong :
    MaxContactCoverData.cT hv =
      (tunedTriple T hv).pullbackAlong (chosenCoverData T hv).disjointUnion
        (MaxContactCoverData.coverMap T hv ≫ structMap T) (MaxContactCoverData.coverMap T hv) :=
  rfl
end

theorem topologicalKrullDim_le_of_isEmpty {C B : Type} [TopologicalSpace C]
    [TopologicalSpace B] (h : IsEmpty C) :
    topologicalKrullDim C ≤ topologicalKrullDim B := by
  have  : IsEmpty $ IrreducibleCloseds C := by
    exact ⟨fun Z => h.elim Z.2.1.choose⟩
  show Order.krullDim (IrreducibleCloseds C)
      ≤ Order.krullDim (IrreducibleCloseds B)
  exact Order.krullDim_le_of_strictMono
    isEmptyElim
    (fun a _ _ => isEmptyElim a)

theorem topologicalKrullDim_ne_bot {B : Type} [TopologicalSpace B] (b : B) :
    topologicalKrullDim B ≠ ⊥ := by
  intro hb
  exact (Order.krullDim_eq_bot_iff.mp hb).elim ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩

section
variable (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)
theorem exists_isMaxContactCover
    (h : ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((tunedMult T : ℕ) : ENat)) :
    ∃ D : FiniteOpenCoverWithIdeals T,
      IsMaxContactCover T D hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv)
        (tunedMult T) := by
  classical
  have := hv.locallyOfFiniteType
  have : CompactSpace T.scheme := by
    have := hv.quasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace T.structMap
  choose V J hxV hVaff hdich using exists_affineOpen_maxContactCoord_or_disjoint_locus T hv h
  have hcover : univ ⊆
      ⋃ x : scheme T, ((V x) : CSet T.scheme) := by
    intro y _
    exact mem_iUnion.2 ⟨y, hxV y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((V x) : CSet T.scheme))
    (fun x => (V x).isOpen) hcover
  refine ⟨{ idx := {y : scheme T // y ∈ t},
            finiteIdx := inferInstance,
            opens := fun i => V i.1,
            localIdeal := fun i => J i.1 }, ?_, fun i => hVaff i.1, ?_⟩
  refine le_antisymm le_top ?_
  intro y _
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 $ ht $ Set.mem_univ y
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩
  simp_all

theorem krullDimSucc_coverTriple_scheme_le_dim :
    krullDimSucc (MaxContactCoverData.cT hv).scheme ≤ T.krullDimSucc := by
  let _a0 := tSch $ p7 hv
  have hd := hv.topologicalKrullDim_lt_top
  by_cases hTe : IsEmpty T.scheme
  have hce : IsEmpty _a0 :=
    ⟨fun x => hTe.elim $ bsM (p12 T hv) x⟩
  exact krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _
    (topologicalKrullDim_le_of_isEmpty hce) hd
  obtain ⟨y⟩ : Nonempty T.scheme := mp_ not_isEmpty_iff hTe
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp $ topologicalKrullDim_ne_bot y
  have hmtop : m ≠ ⊤ := by
    rintro rfl
    rw [WithBot.coe_top] at hm
    rw [← hm] at hd
    exact lt_irrefl _ hd
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hmtop
  have hdeq : topologicalKrullDim T.scheme = (k : WithBot ENat) := by
    rw [← hm, ← hk]
    norm_cast
  refine krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ ?_ hd
  rw [hdeq]
  refine topologicalKrullDim_le_natCast_of_isOpenCover
    (fun i : (chosenCoverData T hv).idx =>
      ((coverTripleOpen T hv i) : Set _a0))
    (fun i => (coverTripleOpen T hv i).isOpen) ?_ k ?_
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨i, hi⟩ := exists_mem_coverTripleOpen T hv x
  exact mpr_ mem_iUnion ⟨i, hi⟩
  intro i
  have hpiece : topologicalKrullDim ((coverTripleOpen T hv i) : Set (p7 hv).scheme) ≤ topologicalKrullDim T.scheme := by
    have hps_ : IsOpenImmersion $ opI (coverTripleOpen T hv i) ≫ p12 T hv := by
      rw [coverTripleOpen_io_comp_coverMap T hv i]
      infer_instance
    exact (opI (coverTripleOpen T hv i) ≫ p12 T hv).isOpenEmbedding.isInducing.topologicalKrullDim_le
  rwa [hdeq] at hpiece
end

end MaxContactOpenCover









theorem range_io_base_subset {X : Sch} (U : Opn X) :
    range U.ib ⊆ (U : Set ↥X) :=
  (q1 U).subset

theorem comap_comap_eq_of_comp_eq {W X Y Z : Sch} (a : W ⟶ X) (b : X ⟶ Z) (a' : W ⟶ Y)
    (b' : Y ⟶ Z) (hsq : a ≫ b = a' ≫ b') (I : ISD Z) :
    comap (comap I b) a = comap (comap I b') a' := by
  have h1 : comap (cmI I b) a = cmI I (a ≫ b) := by
    simp [comap_comp]
  have h2 : comap (cmI I b') a' = cmI I (a' ≫ b') := by
    simp [comap_comp]
  rw [h1, h2, hsq]

section
variable (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)
theorem restrictIdeal_coverTripleOpen_coverMaxContactIdeal
    (hres : ∀ i : (chosenCoverData T hv).idx,
      comap (MaxContactCoverData.cI hv) (MaxContactOpenCover.coverPieceio T hv i) =
        (chosenCoverData T hv).localIdeal i)
    i :
    @restrictIdeal (MaxContactCoverData.cT hv).scheme
        (MaxContactCoverData.cI hv) (MaxContactOpenCover.coverTripleOpen T hv i) =
      comap ((chosenCoverData T hv).localIdeal i) (MaxContactOpenCover.coverPieceIso T hv i).inv :=
  (MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i $ p31 hv).trans
    (congrArg (fun J : ISD (MaxContactOpenCover.coverPiece T hv i) =>
      comap J (MaxContactOpenCover.coverPieceIso T hv i).inv) $ hres i)

section
variable (hgood : IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv) (tunedMult T)) (hres : ∀ i : (chosenCoverData T hv).idx, comap (MaxContactCoverData.cI hv) (MaxContactOpenCover.coverPieceio T hv i) = (chosenCoverData T hv).localIdeal i)
include hgood hres
theorem inStrictNormalCrossingPositionAt_coverMaxContactIdeal
    x :
    InStrictNormalCrossingPositionAt (MaxContactCoverData.cT hv).structMap
      [MaxContactCoverData.cI hv] x := by
  let _a0 := p31 hv
  obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
  have h1 := MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i _a0
  rcases hgood.dichotomy i with ⟨_hdisj, htop⟩ | ⟨n, c, j, hlocal, _hmc⟩
  have h2 : (_a0.comap $ MaxContactOpenCover.coverPieceio T hv i).comap
      (MaxContactOpenCover.coverPieceIso T hv i).inv = ⊤ := by
    rw [hres i, htop]
    exact comap_top _
  have key := tr_ h1 h2
  let _a1 := p7 hv
  have hsm : Smooth _a1.structMap := by
    have := smooth_coverMap_of_isAdmissible T hv
    have := hv.smooth
    exact (inferInstance : Smooth
      (p12 T hv ≫ tMp T))
  obtain ⟨U, m, hxU, hUle, -, ⟨ch⟩⟩ :=
    exists_etaleChart_le _a1.structMap x
      (MaxContactOpenCover.coverTripleOpen T hv i) hxi
  have keyU : restrictIdeal _a0 U = ⊤ := by
    apply restrictIdeal_eq_top_of_le <;> assumption
  refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, ch, fun _ => none, ?_, ?_, ?_⟩
  intro r _hr s _hs t hrt _hst
  simp at hrt
  intro r hr _hnone
  have hr0 := mp_ lt_one_iff hr
  subst hr0
  exact keyU
  intro r _hr t hrt
  simp at hrt
  have h2 : (_a0.comap $ MaxContactOpenCover.coverPieceio T hv i).comap
      (MaxContactOpenCover.coverPieceIso T hv i).inv = (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} := by
    rw [hres i, hlocal, MaxContactOpenCover.coverEtaleChart_coordIdeal]
  refine inStrictNormalCrossingPositionAt_of_exists_etaleChart
    ⟨MaxContactOpenCover.coverTripleOpen T hv i, hxi, n, MaxContactOpenCover.coverEtaleChart T hv i c, fun _ => some j,
      ?_, ?_, ?_⟩
  intro r hr s hs t _hrt _hst
  have hr0 := mp_ lt_one_iff hr
  have hs0 := mp_ lt_one_iff hs
  omega
  intro r _hr hnone
  simp at hnone
  intro r hr t hrt
  have hr0 := mp_ lt_one_iff hr
  subst hr0
  obtain rfl : j = t := m105 hrt
  exact tr_ h1 h2

theorem inStrictNormalCrossingPosition_coverMaxContactIdeal
    (hsm : IsSmoothDivisor (MaxContactCoverData.cT hv).structMap
      (MaxContactCoverData.cI hv)) :
    InStrictNormalCrossingPosition (MaxContactCoverData.cT hv).structMap
      [MaxContactCoverData.cI hv] := by
  refine mpr_ (inStrictNormalCrossingPosition_iff _ _)
    ⟨?_, fun x => inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood hres x⟩
  intro D hD
  have hD' := mp_ mem_singleton hD
  subst hD'
  exact hsm
end
end





namespace BoundarySeparationBaseChange

section
variable (S : MarkedIdealWithBoundary)
section
variable (s : S.mbs)
theorem orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero :
    ∀ D ∈ (s.boundary s.length).take 0,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (support D : CSet $ s.obj s.length) = ∅ :=by simp_all
theorem lt_length_nil_append_boundary_drop_zero (j : ℕ)
    (hj : j < S.boundary.length) :
    j < (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0).length := by
  have h5 : S.boundary.length ≤ (s.boundary s.length).length := by
    rw [← MarkedBlowupSequenceData.toBlowupSequenceData_boundary_eq s s.length le_rfl, BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append s.toBlowupSequenceData S.boundary s.length]
    simp only [length_append, length_map]
    omega
  simp only [nil_append, drop_zero]
  omega
end

theorem orderAt_pullbackTriple_le_mult {X' : Sch} (q : X' ⟶ scheme S)
    [Smooth q] (hV : IsAdmissible S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat)) :
    ∀ x : ↥(LowerDimReductionPullback.pullbackTriple S q).scheme,
      orderAt (LowerDimReductionPullback.pullbackTriple S q).ideal x ≤ ((mult (LowerDimReductionPullback.pullbackTriple S q) : ℕ) : ENat) := by
  have := hV.charZero
  have := hV.smooth
  intro x
  exact le_trans (le_of_eq $ orderAt_comap S.base S.structMap q S.ideal x) $ hO $ q x
end

def IsMaxContactInvariantBalancedTuned : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (P : Sch) (p : P ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p]
    (A : ISD P) (mu_ : ℕ), 1 ≤ mu_ → MaxOrderEq A mu_ →
      IsMaxContactInvariant k p (balancedTunedSheaf k p A mu_) (tuningExponent mu_)

def MaxContactHypersurfaceSmoothPullback : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (P : Sch) (p : P ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p]
    (Y : Sch) (g : Y ⟶ P) [Smooth g]
    [LocallyOfFiniteType $ g ≫ p]
    (A : ISD P) (mu_ : ℕ), 1 ≤ mu_ →
      ∀ H : ISD P, IsMaxContactHypersurface k p A mu_ H →
        IsMaxContactHypersurface k (g ≫ p) (comap A g) mu_ (comap H g)

theorem isLocallyNoetherian_schemeAt (_hMaxContact : MaxContactCoverProperties) (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
    (s : S.mbs) :
    ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i) := by
  intro i hi
  have hnoeth :=
    p25 effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i
      (s.le_toSequenceOfBlowups_length hi)
  show IsLocallyNoetherian $ s.toMarkedSequenceOfBlowups.schemeAt i
  infer_instance

section
variable (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary) (A : ℕ → PrincipalizationAssignment) (S : MarkedIdealWithBoundary)
abbrev separateBoundaryOfFamily (n : ℕ) :
    S.mbs :=
  separateBoundary hinv T (fun S' _ i => A i S') S n

theorem length_separateBoundaryOfFamily_zero :
    (separateBoundaryOfFamily hinv T A S 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = 0 := by
  exact m32 (congrArg (fun d : BlowupSequenceData S.scheme => d.length) $ m32 (congrArg (fun s : S.mbs => mbBd s) $ MaxContactCoverData.separateBoundary_zero hinv T (fun S' _ i => A i S') S) $ emptyMarkedBlowupSequenceData_toBlowupSequenceData S.structMap S.ideal S.mult S.boundary) $ empty_length S.scheme
end

section
variable (hstar : MaxContactCoverProperties)
include hstar
section
variable (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
include hV
section
variable (s : S.mbs) (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
theorem isAdmissible_derivedTriple_nil :
    IsAdmissible $ MaxContactCoverData.derivedTriple S s hft ([] : List (s.obj s.length).IdealSheafData) 0 := by
  refine BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV s hft [] 0 ?_
  have h := (p38 effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups s.length $ s.le_toSequenceOfBlowups_length $ le_refl s.length).snc
  rw [transformAt_structureMorphism, transformAt_boundary,
    projectionToSpec_eq, toMarkedSequence_projectionToBase] at h
  exact h

theorem dim_derivedTriple_le_dim
    (added : List (s.obj s.length).IdealSheafData) (nDrop : ℕ) :
    (MaxContactCoverData.derivedTriple S s hft added nDrop).krullDimSucc ≤ S.krullDimSucc := by
  have h :=
    hstar.schemeDim_level_le S hV s.toMarkedSequenceOfBlowups s.length
      (s.le_toSequenceOfBlowups_length $ le_refl s.length)
  show krullDimSucc (p8 S s hft added nDrop).scheme ≤ tDim S
  rwa [derivedTriple_scheme]
end

theorem isMaxContactHypersurface_strictTransformAtLength (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (Hs : tISD S)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult Hs)
    (s : S.mbs)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S)) :
    @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ structMap S) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult)
      (strictTransformAtLength s Hs) := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length $ le_refl s.length
  have := hft
  rw [LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf, strictTransformAtLength_eq]
  exact BoundarySeparationByMaxContact.isMaxContactHypersurface_balancedTunedSheaf hstar S.base
    (lastP s ≫ tMp S) (lastI s) S.mult hV.one_le_mult
    (LowerDimReductionPullback.orderAt_ideal_length_le hstar S hV hO s)
    (p42 s Hs s.length) $ isMaxContactHypersurface_iteratedStrictTransform hstar S hV hO Hs hH s s.length $ le_refl s.length
end

theorem separateBoundaryInvariant_separateBoundaryOfFamily (hinv : ComapIsoInvariance)
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment)
    (B : PrincipalizationAssignment) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ENat)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : tISD S) (hH : InStrictNormalCrossingPosition S.structMap [H])
    (j : ℕ) (hj : j ≤ S.boundary.length) :
    BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H (separateBoundaryOfFamily hinv T A S j) j := by
  let _a0 := separateBoundaryOfFamily hinv T A S 0
  revert hj
  induction j with
  | zero =>
      intro _
      show BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H _a0 0
      have h0 :=
        MaxContactCoverData.separateBoundary_zero hinv T (fun S' _ i => A i S') S
      have h1 :=
        m32
          (congrArg
            (fun s : S.mbs => mbBd s) h0)
          (emptyMarkedBlowupSequenceData_toBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
      have hlen : _a0.length = 0 :=
        m32 (congrArg (fun d : BlowupSequenceData S.scheme => d.length) h1)
          (empty_length S.scheme)
      refine m157 ?_ $ m157 ?_ $ BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_iteratedStrictTransform_zero S _a0 H hH
      intro i hi
      exact absurd hi $ not_lt_zero i
      intro i hi
      exact absurd hi $ by omega
  | succ n ih =>
      intro hj
      let _a1 := separateBoundaryOfFamily hinv T A S $ n + 1
      show BoundarySeparationByMaxContact.SeparateBoundaryInvariant S H _a1 $ n + 1
      let _a2 := separateBoundaryOfFamily hinv T A S n
      have key :=
        BoundarySeparationByMaxContact.separateBoundaryInvariant_appendLowerDimReduction hstar hinv P hmono A B hspec T hPdimT S hV hO
          hdimS H hH _a2 n (lt_of_succ_le hj) $ ih $ le_of_succ_le hj
      have hstep : _a1
          = appendLowerDimReduction hinv T (fun S' _ i => A i S') S
              _a2 [] 0 n :=
        separateBoundary_succ hinv T (fun S' _ i => A i S') S n
      rwa [hstep]
end

theorem boundary_pullbackAlong_eq_map_comap (U : MarkedIdealWithBoundary) {Y : Sch}
    (qq : Y ⟶ Sp U.base) (h : Y ⟶ U.scheme)
    (L : List U.scheme.IdealSheafData) (hL : boundary U = L) :
    boundary (U.pbA qq h) = L.map fun Dv => comap Dv h := by
  subst hL
  rfl

theorem isAdmissible_withBoundary_of_eq (U : MarkedIdealWithBoundary) (hU : IsAdmissible U)
    (L : List U.scheme.IdealSheafData) (hL : boundary U = L) : IsAdmissible $ withBoundary U L := by
  subst hL
  exact hU

theorem exists_index_of_mem_take {al_ : Type} :
    ∀ (L : List al_) (n : ℕ) (D : al_), D ∈ L.take n →
      ∃ i, ∃ hi, i < n ∧ L.lget i hi = D := by
  intro L
  induction L with
  | nil =>
    intro n D hD
    simp at hD
  | cons a t ih =>
    intro n D hD
    cases n with
    | zero => simp at hD
    | succ m =>
      have hD' := hD
      rcases mem_cons.mp hD' with rfl | hD''
      exact ⟨0, by simp, succ_pos m, rfl⟩
      obtain ⟨i, hi, hin, hget⟩ := ih m D hD''
      exact ⟨i + 1, succ_lt_succ hi, succ_lt_succ hin, hget⟩

theorem orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated (S : MarkedIdealWithBoundary)
    (s : S.mbs) (n : ℕ)
    (h : BoundarySeparationByMaxContact.BoundarySeparated S s n) :
    ∀ D ∈ (s.boundary s.length).take n,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (support D : CSet $ s.obj s.length) = ∅ := by
  intro D hD
  obtain ⟨i, hi, hin, hget⟩ := exists_index_of_mem_take (lastB s) n D hD
  have key := h i hin hi
  dsimp only [lget] at hget
  rwa [hget] at key

theorem isStrictPullback_of_length_eq_zero {X' X : Sch} (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsStrictPullbackBlowupSeq g t s :=
  StrictPullbackBlowupSeq.isStrictPullback
    { comp := fun i hi =>
        eqToHom (congrArg t.schemeAt (by omega : i = 0)) ≫ sbIzH t ≫ g ≫ sbIzI s ≫
          eqToHom (congrArg s.schemeAt (by omega : 0 = i))
      comp_zero := by simp
      pullback := fun i hi => absurd hi (by omega)
      length_eq := by rw [ht, hs]
      center_eq := fun i hi => absurd hi (by omega) }

theorem length_toMarkedSequence_eq_zero {k : Type} [Field k] {X : Sch}
    (p : X ⟶ Sp k) (I : ISD X) (m : ℕ) (E : Bdy X)
    (b : SequenceOfBlowups X) (h : (ofSequenceOfBlowups b).IsMarked p I m E) (hb : b.length = 0) :
    ((ofSequenceOfBlowups b).toMarkedBlowupSequenceData p I m E h).length = 0 := hb

private theorem orderAt_le_mult_of_isOrderBoundedByMult (T : MarkedIdealWithBoundary) (h : T.IsOrderBoundedByMult) :
    ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat) := h

theorem isomorphic_appendLowerDimReduction_of_isMaxContactHypersurface (hstar : MaxContactCoverProperties)
    (hin : OrderReduction.OrderReductionHypotheses) (hMC : IsMaxContactInvariantBalancedTuned)
    (hinv : ComapIsoInvariance) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment)
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (s : S.mbs)
    (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S))
    (nDrop : ℕ) (E1 E2 : (s.obj s.length).IdealSheafData)
    (hV1 : IsAdmissible (MaxContactCoverData.derivedTriple S s hft [E1] nDrop))
    (hV2 : IsAdmissible (MaxContactCoverData.derivedTriple S s hft [E2] nDrop))
    (hR1 : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ structMap S) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) E1)
    (hR2 : @IsMaxContactHypersurface S.base S.instField (s.obj s.length)
      (s.proj s.length ≫ structMap S) hft (LowerDimReductionPullback.tunedIdealAtLength S s hft) (tuningExponent S.mult) E2)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take nDrop,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : CSet (s.obj s.length)) = ∅) :
    (appendLowerDimReduction hinv T (fun S' _ i => A i S') S s [E1] nDrop
        0).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      (appendLowerDimReduction hinv T (fun S' _ i => A i S') S s [E2] nDrop
        0).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  let _a0 := p8 S s hft [E1] nDrop
  let _a1 := A 0 $ p8 S s hft [E2] nDrop
  let _a2 := (s.boundary s.length).drop nDrop
  let _a3 := s.proj s.length ≫ tMp S
  classical
  have hdim1 :=
    le_trans (dim_derivedTriple_le_dim hstar S hV s hft [E1] nDrop) hdimS
  have hdim2 :=
    le_trans (dim_derivedTriple_le_dim hstar S hV s hft [E2] nDrop) hdimS
  have hj1 : 0 < ([E1] ++ _a2).length := by simp
  have hj2 : 0 < ([E2] ++ _a2).length := by simp
  obtain ⟨hmk1, hc1, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B 0 (hspec 0)
    (fun S' _ i => A i S') (fun _ _ _ => rfl) S hV hV.one_le_mult hO s [E1] nDrop hft hdim1
    (hmono _ _ hdim1 hPdimT) hV1 hj1 hsep
  obtain ⟨hmk2, hc2, -⟩ := LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B 0 (hspec 0)
    (fun S' _ i => A i S') (fun _ _ _ => rfl) S hV hV.one_le_mult hO s [E2] nDrop hft hdim2
    (hmono _ _ hdim2 hPdimT) hV2 hj2 hsep
  rw [hc1, hc2]
  by_cases hne : (orderAtLeastLocus (s.ideal s.length) S.mult).Nonempty
  have := hV.charZero
  have := BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length $ le_refl s.length
  have := hft
  have hA1 : ∀ [inst : LocallyOfFiniteType
      _a0.structMap],
      IsMaxContactHypersurface _a0.base
        _a0.structMap
        _a0.ideal
        _a0.mult E1 := by
    intro inst
    exact hR1
  have hA2 : ∀ [inst : LocallyOfFiniteType
      _a0.structMap],
      IsMaxContactHypersurface _a0.base
        _a0.structMap
        _a0.ideal
        _a0.mult E2 := by
    intro inst
    exact hR2
  have hMCinv : ∀ [inst : LocallyOfFiniteType
      _a0.structMap],
      IsMaxContactInvariant _a0.base
        _a0.structMap
        _a0.ideal
        _a0.mult := by
    intro inst
    rw [derivedTriple_mult, LowerDimReductionPullback.ideal_derivedTriple, LowerDimReductionPullback.tunedIdealAtLength_eq_balancedTunedSheaf]
    exact hMC S.base (s.obj s.length) _a3 (s.ideal s.length)
      S.mult hV.one_le_mult (LowerDimReductionPullback.maxOrderEq_ideal_length_of_nonempty hstar S hV hO s hne)
  have hEq := DivisorReductionIndependence.isomorphic_withBoundary_cons_of_isMaxContactHypersurface hin P hmono (A 0) B (hspec 0)
    _a0 hV1 (hmono _ _ hdim1 hPdimT)
    (orderAt_le_mult_of_isOrderBoundedByMult _
      (LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hV.one_le_mult hO s hft [E1] nDrop hV1))
    (fun _ => LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hV.one_le_mult hO s hft [E1] nDrop hV1)
    hMCinv _a2 E1 E2 (p48 S s hft [E1] nDrop) hV2 hA1 hA2
  refine append_isomorphic_of_isomorphic s _ _ hinv ?_
  exact Isomorphic.trans
    (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic
      (A 0 _a0).toSequenceOfBlowups)
    (Isomorphic.trans hEq
      (Isomorphic.symm
        (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic
          _a1.toSequenceOfBlowups)))
  have hempty :=
    Set.not_nonempty_iff_eq_empty.mp hne
  have e1 := append_isomorphic_of_length_eq_zero s _ hinv
    (length_toMarkedSequence_eq_zero _a3 (s.ideal s.length) S.mult
      (s.boundary s.length) (A 0 _a0).toSequenceOfBlowups
      hmk1 (LowerDimReductionPullback.length_eq_zero_of_orderAtLeastLocus_eq_empty hstar P 0 (A 0) B (hspec 0) S hV hV.one_le_mult hO s hft [E1] nDrop (hmono _ _ hdim1 hPdimT) hV1 hj1 hempty))
  have e2 := append_isomorphic_of_length_eq_zero s _ hinv
    (length_toMarkedSequence_eq_zero _a3 (s.ideal s.length) S.mult
      (s.boundary s.length) _a1.toSequenceOfBlowups
      hmk2 (LowerDimReductionPullback.length_eq_zero_of_orderAtLeastLocus_eq_empty hstar P 0 (A 0) B (hspec 0) S hV hV.one_le_mult hO s hft [E2] nDrop (hmono _ _ hdim2 hPdimT) hV2 hj2 hempty))
  exact Isomorphic.trans e1 $ Isomorphic.symm e2

theorem isStrictPullbackBlowupSeq_reduceAlongHypersurface (hstar : MaxContactCoverProperties) (hin : OrderReduction.OrderReductionHypotheses)
    (hMC : IsMaxContactInvariantBalancedTuned) (hAdm : MaxContactHypersurfaceSmoothPullback)
    (hinv : ComapIsoInvariance) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment)
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : tISD S)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Sch} (q : X' ⟶ scheme S) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.Flat q] [AlgebraicGeometry.Surjective q]
    (hV' : IsAdmissible (LowerDimReductionPullback.pullbackTriple S q)) (hdim' : (LowerDimReductionPullback.pullbackTriple S q).krullDimSucc ≤ T.krullDimSucc)
    (H' : (LowerDimReductionPullback.pullbackTriple S q).scheme.IdealSheafData)
    (hH' : ∀ [LocallyOfFiniteType (LowerDimReductionPullback.pullbackTriple S q).structMap],
      IsMaxContactHypersurface (LowerDimReductionPullback.pullbackTriple S q).base (LowerDimReductionPullback.pullbackTriple S q).structMap
        (LowerDimReductionPullback.pullbackTriple S q).ideal (LowerDimReductionPullback.pullbackTriple S q).mult H')
    (hH'snc : InStrictNormalCrossingPosition (LowerDimReductionPullback.pullbackTriple S q).structMap [H']) :
    IsStrictPullbackBlowupSeq q
      (reduceAlongHypersurface hinv T (fun S' _ i => A i S') (LowerDimReductionPullback.pullbackTriple S q)
        H').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  classical
  have hO' := orderAt_pullbackTriple_le_mult S q hV hO
  let _a0 := LowerDimReductionPullback.pullbackTriple S q
  have hLen : _a0.boundary.length = S.boundary.length :=
    by
    let g := q
    show lenL (List.map (fun D : tISD S => cmI D g) S.boundary)
        = S.boundary.length
    simp
  have key : ∀ n, n ≤ S.boundary.length →
      IsStrictPullbackBlowupSeq q
        (separateBoundaryOfFamily hinv T A _a0 n).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (separateBoundaryOfFamily hinv T A S n).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
    intro n
    induction n with
    | zero =>
        intro _
        exact isStrictPullback_of_length_eq_zero q _ _
          (length_separateBoundaryOfFamily_zero hinv T A _a0)
          (length_separateBoundaryOfFamily_zero hinv T A S)
    | succ m ih =>
        intro hm
        have hm' := lt_of_lt_of_le (lt_succ_self m) hm
        have D := (ih (le_of_lt hm')).toStrictPullbackBlowupSeq
        let _a2 := separateBoundaryOfFamily hinv T A S m
        have hftS := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV
          _a2 _a2.length le_rfl
        have hftT := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar
          _a0 hV' (separateBoundaryOfFamily hinv T A _a0 m)
          (separateBoundaryOfFamily hinv T A _a0 m).length le_rfl
        have hdim :=
          le_trans (dim_derivedTriple_le_dim hstar S hV _a2 hftS [] 0) hdimS
        have hdimb :=
          le_trans (dim_derivedTriple_le_dim hstar _a0 hV'
            (separateBoundaryOfFamily hinv T A _a0 m) hftT [] 0) hdim'
        have hres := LowerDimReductionPullback.nonempty_strictPullback_appendLowerDimReduction S q _a2
          (separateBoundaryOfFamily hinv T A _a0 m) D hstar hinv T P A B m (hspec m)
          (fun S' _ i => A i S') (fun _ _ _ => rfl) [] 0 hftS hftT hV hV.one_le_mult hO
          (isLocallyNoetherian_schemeAt hstar S hV _a2) hV' hO'
          (isLocallyNoetherian_schemeAt hstar _a0 hV'
            (separateBoundaryOfFamily hinv T A _a0 m))
          hdim (hmono _ _ hdim hPdimT)
          (isAdmissible_derivedTriple_nil hstar S hV _a2 hftS)
          (lt_length_nil_append_boundary_drop_zero S _a2 m hm')
          (orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero S _a2)
          hdimb (hmono _ _ hdimb hPdimT)
          (isAdmissible_derivedTriple_nil hstar _a0 hV'
            (separateBoundaryOfFamily hinv T A _a0 m) hftT)
          (lt_length_nil_append_boundary_drop_zero _a0
            (separateBoundaryOfFamily hinv T A _a0 m) m (by rw [hLen]; exact hm'))
          (orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero _a0
            (separateBoundaryOfFamily hinv T A _a0 m))
        have e1 : separateBoundaryOfFamily hinv T A S (m + 1)
            = appendLowerDimReduction hinv T (fun S' _ i => A i S') S
              _a2 [] 0 m :=
          separateBoundary_succ hinv T (fun S' _ i => A i S') S m
        have e2 : separateBoundaryOfFamily hinv T A _a0 (m + 1)
            = appendLowerDimReduction hinv T (fun S' _ i => A i S') _a0
              (separateBoundaryOfFamily hinv T A _a0 m) [] 0 m :=
          separateBoundary_succ hinv T (fun S' _ i => A i S') _a0 m
        rw [e1, e2]
        exact hres.elim fun D' => D'.isStrictPullback
  let _a1 := separateBoundaryOfFamily hinv T A S S.boundary.length
  have hftS2 := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV
    _a1
    _a1.length le_rfl
  have hftT2 := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar _a0 hV'
    (separateBoundaryOfFamily hinv T A _a0 S.boundary.length)
    (separateBoundaryOfFamily hinv T A _a0 S.boundary.length).length le_rfl
  have hTS := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T hPdimT S hV hO
    hdimS H hHsnc S.boundary.length le_rfl
  have hTS' := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T hPdimT
    _a0 hV' hO' hdim' H' hH'snc _a0.boundary.length le_rfl
  rw [hLen] at hTS'
  have hsncF0 := inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H
    (@hH hV.locallyOfFiniteType) _a1 hTS.2.2
    _a1.length le_rfl
  rw [← strictTransformAtLength_eq] at hsncF0
  have hVcF := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV
    _a1 hftS2
    [strictTransformAtLength _a1 H]
    S.boundary.length hsncF0
  have hsncF0' := inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar _a0 hV' hO' H'
    (@hH' hV'.locallyOfFiniteType)
    (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) hTS'.2.2
    (separateBoundaryOfFamily hinv T A _a0 S.boundary.length).length le_rfl
  rw [← strictTransformAtLength_eq, hLen] at hsncF0'
  have hVcF' := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar _a0 hV'
    (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) hftT2
    [strictTransformAtLength
      (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) H']
    S.boundary.length hsncF0'
  rw [reduceAlongHypersurface_eq_appendLowerDimReduction, reduceAlongHypersurface_eq_appendLowerDimReduction, hLen]
  have D := (key S.boundary.length le_rfl).toStrictPullbackBlowupSeq
  have hdimF :=
    le_trans (dim_derivedTriple_le_dim hstar S hV _a1 hftS2
      [strictTransformAtLength _a1 H]
      S.boundary.length) hdimS
  have hVcF2 : tAd (MaxContactCoverData.derivedTriple (LowerDimReductionPullback.pullbackTriple S q) (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) hftT2 (LowerDimReductionPullback.comapBoundaryPullback S q _a1 (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) D [strictTransformAtLength _a1 H]) S.boundary.length) := by
    let s := _a1
    let t := separateBoundaryOfFamily hinv T A _a0 S.boundary.length
    let hNs := isLocallyNoetherian_schemeAt hstar S hV _a1
    let hNt := isLocallyNoetherian_schemeAt hstar _a0 hV'
      (separateBoundaryOfFamily hinv T A _a0 S.boundary.length)
    let added := [strictTransformAtLength _a1 H]
    let nDrop := S.boundary.length
    have hsm :=
      LowerDimReductionPullback.smooth_pullbackMapAtLength S q s t D
    have hlev :=
      MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hV' t.toMarkedSequenceOfBlowups t.length
        (t.le_toSequenceOfBlowups_length (le_refl t.length))
    have hqc0 := hlev.quasiCompact
    rw [transformAt_structureMorphism, projectionToSpec_eq,
      toMarkedSequence_projectionToBase] at hqc0
    let _a0 := LowerDimReductionPullback.pullbackMapAtLength S q s t D
    have hqcA : QuasiCompact
        (_a0 ≫ (s.proj s.length ≫ tMp S)) := by
      rwa [LowerDimReductionPullback.pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S q s t D]
    let _a1 := MaxContactCoverData.derivedTriple S s hftS2 added nDrop
    have hpb := @OrderReduction.OrderReductionHypotheses.valid_pullbackAlong hin
      _a1 hVcF (t.obj t.length)
      (_a0 ≫ tMp _a1)
      _a0 hsm hqcA rfl
    have hbd1 :=
      boundary_pullbackAlong_eq_map_comap _a1
        (_a0 ≫ tMp _a1)
        _a0 _
        (MaxContactCoverData.derivedTriple_boundary S s hftS2 added nDrop)
    have hbd2 : (added ++ (s.boundary s.length).drop nDrop).map
          (·.comap _a0)
        = LowerDimReductionPullback.comapBoundaryPullback S q s t D added ++ (t.boundary t.length).drop nDrop := by
      rw [map_append, map_drop, LowerDimReductionPullback.boundary_eq_map_comap_pullbackMapAtLength S q s t D hNs hNt]
    rw [← LowerDimReductionPullback.pullbackAlong_derivedTriple_eq S q s t D hftS2 hftT2 added nDrop hVcF]
    exact isAdmissible_withBoundary_of_eq _ hpb _ $ tr_ hbd1 hbd2
  have hdimF' : (MaxContactCoverData.derivedTriple _a0
      (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) hftT2
      (LowerDimReductionPullback.comapBoundaryPullback S q _a1
        (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) D
        [strictTransformAtLength _a1 H])
      S.boundary.length).krullDimSucc ≤ tDim T :=
    le_trans (dim_derivedTriple_le_dim hstar _a0 hV'
      (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) hftT2 _
      S.boundary.length) hdim'
  have hNonempty := LowerDimReductionPullback.nonempty_strictPullback_appendLowerDimReduction S q
      _a1
      (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) D hstar hinv T P A B 0
      (hspec 0) (fun S' _ i => A i S') (fun _ _ _ => rfl)
      [strictTransformAtLength _a1 H]
      S.boundary.length
      hftS2 hftT2 hV hV.one_le_mult hO
      (isLocallyNoetherian_schemeAt hstar S hV _a1) hV' hO'
      (isLocallyNoetherian_schemeAt hstar _a0 hV'
        (separateBoundaryOfFamily hinv T A _a0 S.boundary.length))
      hdimF (hmono _ _ hdimF hPdimT) hVcF (by simp)
      (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated S _a1 S.boundary.length hTS.1)
      hdimF' (hmono _ _ hdimF' hPdimT) hVcF2 (by simp)
      (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated _a0
        (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) S.boundary.length
        hTS'.1)
  have hMaxContactS := isMaxContactHypersurface_strictTransformAtLength hstar S hV hO H hH
    _a1 hftS2
  have hMaxContactT := isMaxContactHypersurface_strictTransformAtLength hstar _a0 hV' hO' H' hH'
    (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) hftT2
  have hMaxContactComap := by
    let g := q
    let s := _a1
    let t := separateBoundaryOfFamily hinv T A _a0 S.boundary.length
    let hftS := hftS2
    let hftT := hftT2
    let Hs := strictTransformAtLength _a1 H
    have := hV.charZero
    have := BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length $ le_refl s.length
    have := hftS
    have hsm :=
      LowerDimReductionPullback.smooth_pullbackMapAtLength S g s t D
    have hftg := hftT
    let _a4 := LowerDimReductionPullback.pullbackMapAtLength_comp_eq_pullbackTriple_structureMorphism S g s t D
    rw [← _a4] at hftg
    let _a3 := LowerDimReductionPullback.pullbackMapAtLength S g s t D
    let _a5 := s.proj s.length ≫ tMp S
    let _a6 := LowerDimReductionPullback.tunedIdealAtLength S s hftS
    have key := hAdm S.base (s.obj s.length) _a5 (t.obj t.length)
      _a3 _a6 (tuningExponent S.mult)
      (one_le_tuningExponent S.mult) Hs hMaxContactS
    let _a7 := LowerDimReductionPullback.pullbackTriple S g
    exact @isMaxContactHypersurface_of_eq_of_eq_of_eq S.base S.instField (t.obj t.length)
      (_a3 ≫ _a5)
      (t.proj t.length ≫ tMp _a7) hftg hftT
      (cmI _a6 _a3)
      (LowerDimReductionPullback.tunedIdealAtLength _a7 t hftT)
      (cmI Hs _a3) (cmI Hs _a3)
      (tuningExponent S.mult)
      _a4
      (LowerDimReductionPullback.tunedIdealAtLength_comap_pullbackMapAtLength S g s t D hftS hftT ([strictTransformAtLength _a1 H]) S.boundary.length hVcF) rfl key
  have he := isomorphic_appendLowerDimReduction_of_isMaxContactHypersurface hstar hin hMC hinv P hmono A B hspec T hPdimT
    _a0 hV' hO' hdim'
    (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) hftT2 S.boundary.length
    (cmI (strictTransformAtLength _a1 H) D.lastMap)
    (strictTransformAtLength
      (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) H')
    hVcF2 hVcF' hMaxContactComap hMaxContactT
    (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated _a0
      (separateBoundaryOfFamily hinv T A _a0 S.boundary.length) S.boundary.length hTS'.1)
  exact hNonempty.elim fun D' => IsStrictPullbackBlowupSeq.of_isomorphic_pullback D'.isStrictPullback he

end BoundarySeparationBaseChange





namespace MaxContactCoverDescent

section
variable {X Y : Sch} (g : Y ⟶ X) (Q : MorphismProperty Sch) (hQ : Q.IsStableUnderBaseChange) (hg : Q g)
include hQ hg
theorem morphismProperty_pullback_fst_self : Q $ pullback.fst g g :=
  hQ.of_isPullback (m186 g g).flip hg

theorem morphismProperty_pullback_snd_self : Q $ pullback.snd g g :=
  hQ.of_isPullback (m186 g g) hg
end

theorem morphismProperty_comp {X Y Z : Sch} (f : X ⟶ Y) (p : Y ⟶ Z)
    (Q : MorphismProperty Sch) (hQ : Q.IsStableUnderComposition) (hf : Q f) (hp : Q p) :
    Q $ f ≫ p :=
  hQ.comp_mem f p hf hp

theorem map_comap_map_comap_eq_of_comp_eq {W X Y : Sch} (a b : W ⟶ X) (g : X ⟶ Y)
    (hab : a ≫ g = b ≫ g) (L : Bdy Y) :
    List.map (fun D : ISD X => comap D a)
        (List.map (fun D : ISD Y => comap D g) L)
      = List.map (fun D : ISD X => comap D b)
        (List.map (fun D : ISD Y => comap D g) L) := by
  induction L with
  | nil => simp
  | cons D L ih =>
      simp only [map_cons, List.cons.injEq]
      refine ⟨?_, ih⟩
      have hD : cmI D (a ≫ g) = cmI D (b ≫ g) := by rw [hab]
      simpa using hD

theorem heq_reduceAlongHypersurface_of_eq (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    resolveLower
    {S1_ S2_ : MarkedIdealWithBoundary} (hS : S1_ = S2_)
    H1_ H2_ (hH : HEq H1_ H2_) :
    HEq (reduceAlongHypersurface hinv T resolveLower S1_ H1_).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (reduceAlongHypersurface hinv T resolveLower S2_ H2_).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  subst hS
  have hEq := eq_of_heq hH
  subst hEq
  rfl

theorem inStrictNormalCrossingPosition_comap_boundary (hin : OrderReduction.OrderReductionHypotheses)
    (S' : MarkedIdealWithBoundary)
    (hV : IsAdmissible S') {Y : Sch} (f : Y ⟶ scheme S')
    (hf : Smooth f)
    (hq : QuasiCompact $ f ≫ structMap S') :
    InStrictNormalCrossingPosition (f ≫ structMap S')
      (List.map (fun D : tISD S' => comap D f) S'.boundary) := by
  let _a0 := f ≫ tMp S'
  have hsnc := (hin.valid_pullbackAlong S' hV Y _a0 f rfl).snc
  rwa [pullbackAlong_structureMorphism S' Y _a0 f, pullbackAlong_boundary S' Y _a0 f] at hsnc

section
variable (hstar : MaxContactCoverProperties) (hin : OrderReduction.OrderReductionHypotheses)
include hstar hin
section
variable (hmc : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned) (hsap : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback) (hinv : ComapIsoInvariance) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (T : MarkedIdealWithBoundary) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary) (hSV : IsAdmissible S) (hSO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat)) (hSdim : S.krullDimSucc ≤ T.krullDimSucc)
include hmc hsap hmono hspec hPdimT hSV hSO hSdim
theorem isStrictPullbackBlowupSeq_reduceAlongHypersurface_pullback (H : tISD S)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Sch} (q : X' ⟶ scheme S)
    (hqsmooth : AlgebraicGeometry.Smooth q) (hqflat : AlgebraicGeometry.Flat q)
    (hqSu : AlgebraicGeometry.Surjective q) (hqEt : AlgebraicGeometry.Etale q)
    [AlgebraicGeometry.QuasiCompact $ q ≫ structMap S]
    [LocallyOfFiniteType $ q ≫ structMap S]
    (H' : ISD X')
    (hadm' : IsMaxContactHypersurface S.base (q ≫ structMap S) (S.ideal.comap q) S.mult H')
    (hsnc' : InStrictNormalCrossingPosition (q ≫ structMap S) [H']) :
    IsStrictPullbackBlowupSeq q
      (reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S q) H').toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hNS := hSV.isNoetherian
  have hLNS : IsLocallyNoetherian S.scheme := inferInstance
  refine BoundarySeparationBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hmc hsap hinv P hmono A B hspec T hPdimT
    S hSV hSO hSdim H hH hHsnc q (hin.valid_pullbackAlong S hSV X' (q ≫ tMp S) q rfl) (le_trans (hin.schemeDim_le_of_etale X' S.scheme q hSV.topologicalKrullDim_lt_top) hSdim) H' ?_ hsnc'
  intro _inst
  exact hadm'

theorem exists_isStrictPullbackBlowupSeq_reduceAlongHypersurface
    g
    (hgEt : AlgebraicGeometry.Etale g) (hgsmooth : AlgebraicGeometry.Smooth g)
    (hgflat : AlgebraicGeometry.Flat g) (hgSu : AlgebraicGeometry.Surjective g)
    ph_ (hgs : structMap S = g ≫ ph_)
    (J : tISD T) (hgi : ideal S = comap J g)
    E
    (hgb : boundary S = List.map (fun D : tISD T => comap D g) E)
    (H : tISD S)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H]) :
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq g
        (reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups
        d.toSequenceOfBlowups := by
  classical
  have := hSV.charZero
  have := hSV.smooth
  have := hSV.locallyOfFiniteType
  have := hSV.quasiCompact
  have := hgEt
  have := hgsmooth
  have := hgflat
  have := hgSu
  have hNS := hSV.isNoetherian
  have hNSp : NoetherianSpace S.scheme := inferInstance
  have hQCg : QuasiCompact g :=
    ⟨fun U _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hcolS : ∀ W (a b : W ⟶ tSch S), a ≫ g = b ≫ g →
      a ≫ structMap S = b ≫ structMap S := by
    intro W a b hab
    rw [hgs, ← assoc, ← assoc, hab]
  have hcolI : ∀ W (a b : W ⟶ tSch S), a ≫ g = b ≫ g →
      S.ideal.comap a = S.ideal.comap b := by
    intro W a b hab
    have hD : cmI J (a ≫ g) = cmI J (b ≫ g) := by rw [hab]
    rw [hgi]
    simpa using hD
  have hcolB : ∀ W (a b : W ⟶ tSch S), a ≫ g = b ≫ g →
      List.map (fun D : tISD S => cmI D a) S.boundary
        = List.map (fun D : tISD S => cmI D b) S.boundary := by
    intro W a b hab
    rw [hgb]
    exact map_comap_map_comap_eq_of_comp_eq a b g hab E
  have hcol : ∀ W (a b : W ⟶ tSch S), a ≫ g = b ≫ g →
      LowerDimReductionPullback.pullbackTriple S a = LowerDimReductionPullback.pullbackTriple S b := by
    intro W a b hab
    simp only [LowerDimReductionPullback.pullbackTriple, pullbackAlong]
    rw [hcolS W a b hab, hcolI W a b hab, hcolB W a b hab]
  have hSm1 :=
    morphismProperty_pullback_fst_self g (@Smooth : MorphismProperty Sch) inferInstance
      inferInstance
  have hSm2 :=
    morphismProperty_pullback_snd_self g (@Smooth : MorphismProperty Sch) inferInstance
      inferInstance
  have hSm1' := hSm1
  have hSm2' := hSm2
  let _a0 := pullback.fst g g
  have hQC1 :=
    morphismProperty_comp _a0 S.structMap
      (@QuasiCompact : MorphismProperty Sch) inferInstance
      inferInstance inferInstance
  let _a1 := pullback.snd g g
  have hQC2 :=
    morphismProperty_comp _a1 S.structMap
      (@QuasiCompact : MorphismProperty Sch) inferInstance
      inferInstance inferInstance
  have hLF1 :=
    morphismProperty_comp _a0 S.structMap
      (@LocallyOfFiniteType : MorphismProperty Sch) inferInstance
      inferInstance inferInstance
  have hLF2 :=
    morphismProperty_comp _a1 S.structMap
      (@LocallyOfFiniteType : MorphismProperty Sch) inferInstance
      inferInstance inferInstance
  have hcond : _a1 ≫ g = _a0 ≫ g := pullback.condition.symm
  let _a2 := pullback g g
  have hstruct :=
    hcolS _a2 _a1 _a0 hcond
  have hideal :=
    hcolI _a2 _a1 _a0 hcond
  have htriple :=
    hcol _a2 _a1 _a0 hcond
  have hadm1 :=
    hsap S.base S.scheme S.structMap _a2 _a0 S.ideal S.mult
      hSV.one_le_mult H hH
  have hadm2 :=
    isMaxContactHypersurface_of_eq_of_eq_of_eq S.base hstruct.symm hideal.symm rfl hadm1
  let _a3 := tWB S [H]
  have hVb : tAd _a3 :=
    { charZero := hSV.charZero
      locallyOfFiniteType := hSV.locallyOfFiniteType
      nonzeroOnComponents := hSV.nonzeroOnComponents
      one_le_mult := hSV.one_le_mult
      quasiCompact := hSV.quasiCompact
      smooth := hSV.smooth
      snc := hHsnc }
  have hsnc1 :=
    inStrictNormalCrossingPosition_comap_boundary hin _a3 hVb _a0 hSm1 hQC1
  have hsnc2 : InStrictNormalCrossingPosition (_a1 ≫ tMp S) [cmI H _a0] := by
    rwa [hstruct]
  have hs1 := isStrictPullbackBlowupSeq_reduceAlongHypersurface_pullback hstar hin hmc hsap hinv P hmono A B hspec T hPdimT
    S hSV hSO hSdim H hH hHsnc _a0 hSm1 (morphismProperty_pullback_fst_self g (@Flat : MorphismProperty Sch) inferInstance inferInstance) (morphismProperty_pullback_fst_self g (@AlgebraicGeometry.Surjective : MorphismProperty Sch) inferInstance inferInstance) (morphismProperty_pullback_fst_self g (@Etale : MorphismProperty Sch) inferInstance inferInstance)
    (cmI H _a0) hadm1 hsnc1
  have hs2 := isStrictPullbackBlowupSeq_reduceAlongHypersurface_pullback hstar hin hmc hsap hinv P hmono A B hspec T hPdimT
    S hSV hSO hSdim H hH hHsnc _a1 hSm2 (morphismProperty_pullback_snd_self g (@Flat : MorphismProperty Sch) inferInstance inferInstance) (morphismProperty_pullback_snd_self g (@AlgebraicGeometry.Surjective : MorphismProperty Sch) inferInstance inferInstance) (morphismProperty_pullback_snd_self g (@Etale : MorphismProperty Sch) inferInstance inferInstance)
    (cmI H _a0) hadm2 hsnc2
  have hseq :=
    eq_of_heq (heq_reduceAlongHypersurface_of_eq hinv T (fun S' _ i => A i S') htriple
      (cmI H _a0) (cmI H _a0)
      (HEq.refl (cmI H _a0)))
  have hs2' : IsStrictPullbackBlowupSeq _a1
      (reduceAlongHypersurface hinv T (fun S' _ i => A i S')
        (LowerDimReductionPullback.pullbackTriple S _a0)
        (cmI H _a0)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
    rwa [← hseq]
  obtain ⟨s, hs⟩ := exists_isStrictPullback_of_isomorphic_baseChange g
    (reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups
    (((isStrictPullbackSequenceOfBlowups_baseChange _ _).isomorphic hs1).trans ((isStrictPullbackSequenceOfBlowups_baseChange _ _).isomorphic hs2').symm)
  exact ⟨ofSequenceOfBlowups s, hs.of_isomorphic_base (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic s).symm⟩
end

theorem exists_isStrictPullback_coverMarkedSequence (hinv : ComapIsoInvariance)
    P (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    A B
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (hmc : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned)
    (hsap : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback)
    (T : MarkedIdealWithBoundary) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) :
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
        d.toSequenceOfBlowups := by
  classical
  let _a0 := p7 h.valid
  let _a1 := p31 h.valid
  obtain ⟨d, hd⟩ :=
    exists_isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hmc hsap hinv P hmono A B hspec
      T h.dim_prop
      _a0 (BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P T h)
      (BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P T h)
      (hstar.coverTriple_dim_le T h.valid)
      (p12 T h.valid)
      (MaxContactCoverData.etale_coverMap_of_isAdmissible T h.valid)
      (smooth_coverMap_of_isAdmissible T h.valid)
      (flat_coverMap_of_isAdmissible T h.valid)
      (MaxContactCoverData.surjective_coverMap T h.valid (hstar.exists_goodCover T h.valid h.orderLE))
      T.structMap rfl
      (p29 T h.valid) rfl
      T.boundary rfl
      _a1
      (by
        intro _inst
        exact BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P T h)
      (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P T h)
  have hcs : MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (p49 A T)
      = reduceAlongHypersurface hinv T (fun S' _ i => A i S')
          _a0
          _a1 := by
    with_unfolding_all rfl
  refine ⟨d, ?_⟩
  rwa [hcs, ← toMarkedSequence_toSequenceOfBlowups]
end

end MaxContactCoverDescent





theorem IsStrictPullbackBlowupSeq.congr_hom {X' X : Sch} {g g' : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s) (hg : g = g') :
    IsStrictPullbackBlowupSeq g' t s := by
  subst hg
  exact h

theorem IsStrictPullbackBlowupSeq.congr_sourceSeq {X' X : Sch} {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq g t s) (ht : t = t') :
    IsStrictPullbackBlowupSeq g t' s := by
  subst ht
  exact h

theorem IsStrictPullbackBlowupSeq.baseChange_of_comp {Q Y X : Sch} {ph_ : Q ⟶ Y} {h : Y ⟶ X}
    [Flat ph_] [Flat h]
    {u : SequenceOfBlowups Q} {s : SequenceOfBlowups X}
    (hu : IsStrictPullbackBlowupSeq (ph_ ≫ h) u s) :
    IsStrictPullbackBlowupSeq ph_ u $ s.baseChange h := by
  have hw :=
    isStrictPullbackSequenceOfBlowups_baseChange (s.baseChange h) ph_
  exact hw.of_isomorphic_pullback $ (hw.comp $ isStrictPullbackSequenceOfBlowups_baseChange s h).isomorphic hu

theorem comap_ne_top_iff_of_surjective {X Y : Sch} (f : X ⟶ Y)
    [AlgebraicGeometry.Surjective f] (J : ISD Y) :
    comap J f ≠ ⊤ ↔ J ≠ ⊤ := by
  have hsurj : Surjective f.base := AlgebraicGeometry.Surjective.surj
  have htop : comap (⊤ : ISD Y) f = ⊤ := by simp
  have hpre : (support (comap J f) : Set X) = preimage f.base J.supp := by simp
  have hbot : support J = ⊥ → J = ⊤ := by simp
  constructor
  intro h hJ
  apply h
  rw [hJ, htop]
  intro hJ h
  apply hJ
  apply hbot
  apply ext'
  have hsupp : J.supp = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ (support (comap J f) : Set X) := by
      rw [hpre]
      exact mpr_ mem_preimage hy
    rw [h] at hx
    simp at hx
  simpa using hsupp

namespace MaxContactFunctoriality

section
variable {T1_ T2_ : MarkedIdealWithBoundary} (hT : T1_ = T2_)
include hT
theorem isMaxContactHypersurface_of_triple_eq
    (hft1_ : LocallyOfFiniteType T1_.structMap)
    (hft2_ : LocallyOfFiniteType T2_.structMap)
    H1_ H2_ (hH : HEq H1_ H2_)
    (h : haveI := hft2_;
      IsMaxContactHypersurface T2_.base T2_.structMap T2_.ideal T2_.mult H2_) :
    haveI := hft1_;
      IsMaxContactHypersurface T1_.base T1_.structMap T1_.ideal T1_.mult H1_ := by
  subst hT
  have hHe := eq_of_heq hH
  subst hHe
  exact h

theorem inStrictNormalCrossingPosition_of_triple_eq
    L1_ L2_ (hL : HEq L1_ L2_)
    (h : InStrictNormalCrossingPosition T2_.structMap L2_) :
    InStrictNormalCrossingPosition T1_.structMap L1_ := by
  subst hT
  have hLe := eq_of_heq hL
  subst hLe
  exact h
end

theorem orderAtLeastLocus_comap_eq_empty (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) {Y}
    (h : Y ⟶ scheme T) [Smooth h]
    (hemp : orderAtLeastLocus T.ideal T.mult = (∅ : CSet T.scheme)) :
    orderAtLeastLocus (T.ideal.comap h) T.mult = (∅ : Set ↥Y) := by
  have hcz : CharZero T.base := by
    cases hv
    assumption
  have hsm : Smooth T.structMap := by
    cases hv
    assumption
  rw [orderAtLeastLocus_comap T.base T.structMap h T.ideal T.mult, hemp, preimage_empty]

section
variable (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties)
include hstar
private theorem derivedTriple_dim_le
    (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
    (s : S.mbs)
    (hft : LocallyOfFiniteType $ s.proj s.length ≫ structMap S)
    extra keep :
    (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ S.krullDimSucc :=
  hstar.schemeDim_level_le S hV s.toMarkedSequenceOfBlowups s.length le_rfl

section
variable (hinv : ComapIsoInvariance) (A : ℕ → PrincipalizationAssignment) (T1_ T2_ : MarkedIdealWithBoundary) (hdim : T1_.krullDimSucc ≤ T2_.krullDimSucc) (S : MarkedIdealWithBoundary) (hV : IsAdmissible S) (hS : S.krullDimSucc ≤ T1_.krullDimSucc)
include hdim hV hS
theorem appendLowerDimReduction_congr_of_dim_le
    (s : S.mbs)
    extra keep n :
    appendLowerDimReduction hinv T1_ (lowerDimensionalFamily A T1_) S s extra keep n =
      appendLowerDimReduction hinv T2_ (lowerDimensionalFamily A T2_) S s extra keep n := by
  let _a0 := lowerDimensionalFamily A T1_
  let _a1 := lowerDimensionalFamily A T2_
  by_cases hft : LocallyOfFiniteType $ lastP s ≫ tMp S
  have h1 :=
    le_trans (derivedTriple_dim_le hstar S hV s hft extra keep) hS
  exact tr_ (appendLowerDimReduction_eq_concatOfIsMarked hinv T1_ _a0 S s extra keep n
      hft h1)
    (appendLowerDimReduction_eq_concatOfIsMarked hinv T2_ _a1 S s extra keep n
      hft $ le_trans h1 hdim).symm
  exact tr_ (appendLowerDimReduction_of_not_locallyOfFiniteType hinv T1_ _a0 S s extra
      keep n hft)
    (appendLowerDimReduction_of_not_locallyOfFiniteType hinv T2_ _a1 S s extra
      keep n hft).symm

theorem separateBoundary_congr_of_dim_le j :
    separateBoundary hinv T1_ (lowerDimensionalFamily A T1_) S j =
      separateBoundary hinv T2_ (lowerDimensionalFamily A T2_) S j := by
  let _a0 := lowerDimensionalFamily A T2_
  let _a1 := lowerDimensionalFamily A T1_
  induction j with
  | zero =>
    rw [MaxContactCoverData.separateBoundary_zero hinv T1_ _a1 S,
      MaxContactCoverData.separateBoundary_zero hinv T2_ _a0 S]
  | succ n ih =>
    rw [separateBoundary_succ hinv T1_ _a1 S n,
      separateBoundary_succ hinv T2_ _a0 S n, ih]
    exact appendLowerDimReduction_congr_of_dim_le hstar hinv A T1_ T2_ hdim S hV hS
      (separateBoundary hinv T2_ _a0 S n) [] 0 n

theorem reduceAlongHypersurface_congr_of_dim_le
    H :
    reduceAlongHypersurface hinv T1_ (lowerDimensionalFamily A T1_) S H =
      reduceAlongHypersurface hinv T2_ (lowerDimensionalFamily A T2_) S H := by
  rw [reduceAlongHypersurface_eq_appendLowerDimReduction hinv T1_ (lowerDimensionalFamily A T1_) S H,
    reduceAlongHypersurface_eq_appendLowerDimReduction hinv T2_ (lowerDimensionalFamily A T2_) S H,
    separateBoundary_congr_of_dim_le hstar hinv A T1_ T2_ hdim S hV hS $ bLen S]
  exact appendLowerDimReduction_congr_of_dim_le hstar hinv A T1_ T2_ hdim S hV hS _ _ S.boundary.length 0
end
end

theorem reduceAlongHypersurface_toSequenceOfBlowups_heq (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    resolveLower
    {S1_ S2_ : MarkedIdealWithBoundary} (hS : S1_ = S2_)
    H1_ H2_ (hH : HEq H1_ H2_) :
    HEq (reduceAlongHypersurface hinv T resolveLower S1_ H1_).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (reduceAlongHypersurface hinv T resolveLower S2_ H2_).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  subst hS
  have hHe := eq_of_heq hH
  subst hHe
  exact HEq.refl _

def MarkingDescends (hinv : ComapIsoInvariance) (P : ℕ → Prop)
    (A : ℕ → PrincipalizationAssignment) : Prop :=
  ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme),
    IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).toSequenceOfBlowups d.toSequenceOfBlowups →
      d.IsMarked T.structMap T.ideal T.mult T.boundary

def CoverFaithfullyFlat (P : ℕ → Prop) : Prop :=
  ∀ (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T),
    AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid) ∧
      AlgebraicGeometry.Flat (MaxContactCoverData.coverMap T h.valid)

def DropTrivialBoundaryAdmissible : Prop :=
  ∀ T : MarkedIdealWithBoundary, IsAdmissible T → IsAdmissible (dropTrivialBoundary T)

def MarkedOfMarkedDropTrivialBoundary : Prop :=
  ∀ (T : MarkedIdealWithBoundary), IsAdmissible T → ∀ d : BlowupSequenceData T.scheme,
    d.IsMarked T.structMap T.ideal T.mult (dropTrivialBoundary T).boundary →
      d.IsMarked T.structMap T.ideal T.mult T.boundary

theorem OrderReductionHypotheses.of_dropTrivialBoundaryAdmissible {P : ℕ → Prop} {T : MarkedIdealWithBoundary} (h : OrderReductionHypotheses P T)
    (htv : DropTrivialBoundaryAdmissible) : OrderReductionHypotheses P $ MaxContactReduction.dropTrivialBoundary T := by
  exact ⟨h.dim_prop, h.orderLE, h.coSupport_nonempty, htv T h.valid⟩

theorem exists_isStrictPullback_cover_dropTrivialBoundary {hinv : ComapIsoInvariance} {P : ℕ → Prop}
    {A : ℕ → PrincipalizationAssignment} (hstar : CoverSequenceProperties hinv P A)
    (hdesc : MarkingDescends hinv P A) (htv : DropTrivialBoundaryAdmissible) (htm : MarkedOfMarkedDropTrivialBoundary)
    (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T) :
    ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq
          (MaxContactCoverData.coverMap (dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
          (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid hinv
            (lowerDimensionalFamily A $ MaxContactReduction.dropTrivialBoundary T)).toSequenceOfBlowups d.toSequenceOfBlowups ∧
        (maxContactPrincipalization hinv A T).toSequenceOfBlowups = d.toSequenceOfBlowups := by
  obtain ⟨d0, hd0⟩ := hstar.descends (p11 T) $ h.of_dropTrivialBoundaryAdmissible htv
  obtain ⟨d, hdsome⟩ :=
    exists_descendStrictPullback_eq_some
      (T := dropTrivialBoundary T)
      (S := coverTriple (dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
      (p12 (dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid)
      (MaxContactCoverData.coverMarkedBlowupData (dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv).valid hinv
        (lowerDimensionalFamily A $ dropTrivialBoundary T))
      ⟨d0, hd0⟩
  have hpb :=
    isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some _ _ hdsome
  refine ⟨d, hpb, ?_⟩
  rw [maxContactPrincipalization_apply,
    reduceOrder_eq_asMarkedSeq hinv T (lowerDimensionalFamily A T) h.valid h.orderAtLeastLocus_ne_empty
      (h.of_dropTrivialBoundaryAdmissible htv).valid d hdsome]
  exact asMarkedSeq_toSequenceOfBlowups T d $ htm T h.valid d $ hdesc (dropTrivialBoundary T) (h.of_dropTrivialBoundaryAdmissible htv) d hpb

end MaxContactFunctoriality





namespace MaxContactFunctoriality

variable (hinv : ComapIsoInvariance) (A : ℕ → PrincipalizationAssignment)
variable {P : ℕ → Prop}

theorem balancedTunedIdeal_eq_of_mult_eq_one (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) (hm : mult T = 1) :
    MaxContactCoverData.balancedTunedIdeal T hv = ideal T := by
  simp [MaxContactCoverData.balancedTunedIdeal, hm, balancedTunedSheaf_eq, tuningExponent_one,
    tunedSheaf_one_one]

theorem coverMap_flat T (h : OrderReductionHypotheses P T) :
    Flat $ MaxContactCoverData.coverMap T h.valid :=
  flat_coverMap_of_isAdmissible T h.valid

section
variable (htune : TunedSheafProperties) (T : MarkedIdealWithBoundary)
include htune
theorem orderAt_balancedTunedIdeal_le_tunedMult_of_nonempty (hv : IsAdmissible T)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    (hne : (orderAtLeastLocus T.ideal T.mult).Nonempty) :
    ∀ x,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((tunedMult T : ℕ) : ENat) := by
  have := hv.charZero
  have := hv.smooth
  have := hv.locallyOfFiniteType
  have hmax : MaxOrderEq T.ideal T.mult :=
    ⟨mpr_ (orderLE_iff T.ideal T.mult) hord, hne⟩
  have hkey := htune.coSupport_tunedSheaf_eq_and_orderLE.orderLE T.base T.scheme T.structMap
    T.ideal T.mult hv.one_le_mult hmax (tuningExponent T.mult) $ one_le_tuningExponent T.mult
  have he0 : MaxContactCoverData.balancedTunedIdeal T hv = balancedTunedSheaf T.base T.structMap T.ideal T.mult := rfl
  have hm : tunedMult T = tuningExponent T.mult := rfl
  intro x
  rw [he0, balancedTunedSheaf_eq, hm]
  exact mp_ (orderLE_iff _ _) hkey x

theorem coverMap_surjective (h : OrderReductionHypotheses P T) :
    AlgebraicGeometry.Surjective $ MaxContactCoverData.coverMap T h.valid :=
  MaxContactCoverData.surjective_coverMap T h.valid
    (MaxContactOpenCover.exists_isMaxContactCover T h.valid
      (orderAt_balancedTunedIdeal_le_tunedMult_of_nonempty htune T h.valid h.orderLE h.coSupport_nonempty))
end

section
variable {X Y Z : Sch} (f : X ⟶ Y)
theorem IsLocalIsomorphism.comp_isIso (g : Y ⟶ Z)
    [IsIso g] (hf : IsLocalIsomorphism f) :
    IsLocalIsomorphism $ f ≫ g := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hf x
  refine ⟨U, hxU, ?_⟩
  rw [← assoc]
  infer_instance

theorem IsLocalIsomorphism.isIso_comp [IsIso f]
    (g : Y ⟶ Z) (hg : IsLocalIsomorphism g) :
    IsLocalIsomorphism $ f ≫ g := by
  have hsurj : Surjective f.base := by
    intro y
    exact ⟨bsM (m83 f) y, congrArg (fun m : Y ⟶ Y => bsM m y) $ m117 f⟩
  intro x
  obtain ⟨U, hxU, hU⟩ := hg $ bsM f x
  refine ⟨preU f U, hxU, ?_⟩
  have : IsOpenImmersion f := inferInstance
  let _s0 := opI (preU f U) ≫ f
  have hrange : range _s0.base = range U.ib := by
    have h1 : range _s0.base
        = range (f.base ∘ (preU f U).ib) := rfl
    rw [h1, range_comp]
    simp [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact image_preimage_eq _ hsurj
  obtain ⟨ph_, hfac⟩ : ∃ ph_ : oSch (preU f U) ≅ oSch U,
      ph_.hom ≫ opI U = opI (preU f U) ≫ f :=
    ⟨isoOfRangeEq _s0 U.i hrange,
      isoOfRangeEq_hom_fac _ _ hrange⟩
  rw [← assoc, ← hfac, assoc]
  infer_instance
end

theorem isLocalIsomorphism_of_eq {W' W : Sch} {f f' : W' ⟶ W}
    (h : f = f') (hf : IsLocalIsomorphism f') : IsLocalIsomorphism f := by
  subst h
  exact hf

theorem isLocalIsomorphism_map_of_isLocalIsomorphism {X' X : Sch} {g : X' ⟶ X}
    (hg : IsLocalIsomorphism g) {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i ≤ t.length) :
    IsLocalIsomorphism $ D.comp i hi := by
  revert hi
  induction i with
  | zero =>
    intro hi
    exact isLocalIsomorphism_of_eq D.map_zero_eq
      (IsLocalIsomorphism.isIso_comp t.isoZero.hom (g ≫ sbIzI s)
        (IsLocalIsomorphism.comp_isIso g s.isoZero.inv hg))
  | succ n ih =>
    intro hi
    have hn : n < t.length := hi
    exact MaxContactOpenCover.isLocalIsomorphism_fst_of_isPullback (D.pullback n hn) $ ih hn.le

theorem isLocalIsomorphism_map_coverBlowupSequence (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T)
    (d : BlowupSequenceData T.scheme)
    (D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (coverBlowupSequence hinv A T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    i (hi : i ≤ (coverBlowupSequence hinv A T h.valid).length) :
    IsLocalIsomorphism
      (D.comp i $ (coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi) :=
  isLocalIsomorphism_map_of_isLocalIsomorphism
    (MaxContactOpenCover.isLocalIsomorphism_coverMap T h.valid) D i
    ((coverBlowupSequence hinv A T h.valid).le_toSequenceOfBlowups_length hi)

theorem isNoetherian_blowupSequenceData_schemeAt X [IsNoetherian X]
    (d : BlowupSequenceData X) i (hi : i ≤ d.length) :
    IsNoetherian $ d.obj i := by
  have hi' := hi
  rw [← p14] at hi'
  have h :=
    isNoetherian_schemeAt d.toSequenceOfBlowups i hi'
  rwa [toSequenceOfBlowups_schemeAt] at h

section
variable (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties) (T : MarkedIdealWithBoundary)
include hstar
theorem isLocallyNoetherian_schemeAt_coverBlowupSequence
    (h : OrderReductionHypotheses P T) (d : BlowupSequenceData T.scheme)
    (_hd : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (coverBlowupSequence hinv A T h.valid).toSequenceOfBlowups d.toSequenceOfBlowups) :
    (∀ i ≤ d.length, IsLocallyNoetherian $ d.obj i) ∧
      ∀ i ≤ (coverBlowupSequence hinv A T h.valid).length,
        IsLocallyNoetherian $ (coverBlowupSequence hinv A T h.valid).obj i := by
  let _c0 := p7 h.valid
  have := h.valid.locallyOfFiniteType
  have := h.valid.quasiCompact
  have : IsNoetherianRing $ m10 T.base := inferInstanceAs $ IsNoetherianRing T.base
  have : IsNoetherian $ Sp T.base := inferInstance
  have :=
    isNoetherian_of_locallyOfFiniteType T.structMap
  have hgood := isMaxContactCover_chosenCoverData T h.valid
    (hstar.exists_goodCover T h.valid h.orderLE)
  have hvc : tAd _c0 :=
    hstar.coverTriple_valid T h.valid h.orderLE hgood
  have := hvc.locallyOfFiniteType
  have := hvc.quasiCompact
  have : IsNoetherianRing $ m10 _c0.base :=
    inferInstanceAs $ IsNoetherianRing _c0.base
  have : IsNoetherian
      (Sp _c0.base) := inferInstance
  have :=
    isNoetherian_of_locallyOfFiniteType _c0.structMap
  constructor
  intro i hi
  have := isNoetherian_blowupSequenceData_schemeAt T.scheme d i hi
  infer_instance
  intro i hi
  have := isNoetherian_blowupSequenceData_schemeAt _c0.scheme
    (coverBlowupSequence hinv A T h.valid).toBlowupSequenceData i hi
  infer_instance

theorem orderAt_sequenceOfBlowups_ideal_le_mult
    (hv : IsAdmissible T) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    (s : T.SequenceOfBlowups) i (hi : i ≤ s.length) x :
    orderAt (s.ideal i) x ≤ (mult T : ENat) :=
  hstar.orderAt_level_le T hv hord s i hi x
end

theorem imageIdealSheaf_inv_eq_comap {X Y : Sch} (ph_ : X ≅ Y)
    (J : ISD Y) :
    imageIdealSheaf ph_.inv J = comap J ph_.hom := by
  let _a0 := cmI (imageIdealSheaf ph_.inv J) ph_.inv
  have h1 : _a0 = J :=
    p30 ph_.inv J
  have h2 : comap _a0 ph_.hom = imageIdealSheaf ph_.inv J := by
    rw [← comap_comp, m145, comap_id]
  calc imageIdealSheaf ph_.inv J = cmI _a0 ph_.hom := sy_ h2
    _ = cmI J ph_.hom := by rw [h1]

theorem isAdmissible_and_dim_eq_withSchemeIdealBoundary_ker (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) (Y : Sch)
    q (e : Y ⟶ scheme T)
    [IsClosedImmersion e] (hq : e ≫ structMap T = q)
    J (hJ : IsAdmissible $ T.withSchemeIdealBoundary Y q J [])
    ep_
    (hep : ep_ ≫ subschemeι (ker e) = e) :
    (T.withSchemeIdealBoundary (ker e).subscheme
        (subschemeι (ker e) ≫ structMap T) (imageIdealSheaf ep_ J) []).IsAdmissible ∧
      (T.withSchemeIdealBoundary (ker e).subscheme
          (subschemeι (ker e) ≫ structMap T) (imageIdealSheaf ep_ J) []).krullDimSucc
        = (T.withSchemeIdealBoundary Y q J []).krullDimSucc := by
  let _a1 := siI $ m149 e
  have : CategoryTheory.Mono _a1 := inferInstance
  have hepi : ep_ = isoI (kerSubschemeIso e) := by
    apply mp_ $ CategoryTheory.cancel_mono _a1
    rw [hep, kerSubschemeIso_inv_comp]
  subst hepi
  have hsmq : Smooth q := by
    have h := hJ.smooth
    rwa [withSchemeIdealBoundary_structureMorphism] at h
  have hftq : LocallyOfFiniteType q := by
    have h := hJ.locallyOfFiniteType
    rwa [withSchemeIdealBoundary_structureMorphism] at h
  have hqcq : QuasiCompact q := by
    have h := hJ.quasiCompact
    rwa [withSchemeIdealBoundary_structureMorphism] at h
  have hnzJ : NonzeroOnComponents J := by
    have h := hJ.nonzeroOnComponents
    rwa [withSchemeIdealBoundary_ideal] at h
  let _a0 := siI (m149 e) ≫ tMp T
  have hkey : _a0
      = isoH (kerSubschemeIso e) ≫ q := by
    rw [← hq, ← assoc, kerSubschemeIso_hom_comp]
  have hsm' : Smooth
      _a0 := by
    rw [hkey]
    infer_instance
  have hft' : LocallyOfFiniteType
      _a0 := by
    rw [hkey]
    infer_instance
  have hqc' : QuasiCompact
      _a0 := by
    rw [hkey]
    infer_instance
  have hnz : NonzeroOnComponents $ imageIdealSheaf (kerSubschemeIso e).inv J := by
    rw [imageIdealSheaf_inv_eq_comap (kerSubschemeIso e) J]
    exact nonzeroOnComponents_comap_iso_hom (kerSubschemeIso e) J hnzJ
  have hdim : krullDimSucc (subS $ m149 e) = krullDimSucc Y := by
    rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim,
      topologicalKrullDim_eq_of_homeomorph $ m207 $ kerSubschemeIso e]
  exact ⟨⟨hv.charZero, hft', hnz, hv.one_le_mult, hqc', hsm',
    inStrictNormalCrossingPosition_nil _a0⟩, hdim⟩

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution

end
section
universe v


section

namespace FunctorialResolution.EmbeddedResolution.MaxContactCoverGeometry

theorem map_iInf_of_bijective {A B : Type} [CommRing A] [CommRing B]
    (ph_ : A →+* B) (hph : Bijective ph_) {ι : Type} (K : ι → Ideal A) :
    Ideal.map ph_ (⨅ i, K i) = ⨅ i, Ideal.map ph_ (K i) :=
  (Ideal.relIsoOfBijective ph_ hph).symm.map_iInf K

theorem ideal_iInf {X : Sch} {ι : Type} [Finite ι]
    (I : ι → ISD X) (U : X.affineOpens) :
    (⨅ i, I i).ideal U = ⨅ i, (I i).ideal U :=by simp_all
section
variable {X Y : Sch} (f : X ⟶ Y) [IsOpenImmersion f]
theorem comap_iInf
    {ι : Type} [Finite ι] (J : ι → ISD Y) :
    comap (⨅ i, J i) f = ⨅ i, comap (J i) f := by
  refine m29 ?_
  funext V
  have hU := V.2.image_of_isOpenImmersion f
  have e :=
    (f.preimage_image_eq V).ge
  have hbij : Bijective $ m4 $ appLE f (imU f V) V e := by
    let g := f
    let S := V
    have : IsIso $ appLE g (imU g S) S e := by
      rw [← appIso_hom' g S]
      infer_instance
    exact m189 _
  have key := fun I =>
    comap_ideal_eq_map_appLE I f ⟨imU f V, hU⟩ V e
  rw [ideal_iInf (fun i => cmI (J i) f) V, key (⨅ i, J i), ideal_iInf J ⟨imU f V, hU⟩, map_iInf_of_bijective _ hbij]
  exact iInf_congr fun i => sy_ $ key $ J i

end

theorem ker_subschemeio_comp_comap_eq_top_of_disjoint {X X' Y : Sch} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : X' ⟶ Y) [QuasiCompact g]
    (hdisj : ∀ x x', f.base x ≠ g.base x') (J : ISD X') :
    ((J.si ≫ g).ker).comap f = ⊤ := by
  let _a0 := m149 $ siI J ≫ g
  refine p39 f _a0 ?_
  intro x hx
  have hx' : bsM f x ∈ (spI _a0 : Set Y) := hx
  rw [support_ker] at hx'
  obtain ⟨y, hy1, hy2⟩ :=
    mem_closure_iff.mp hx' (range f.base) f.isOpenEmbedding.isOpen_range $ mem_range_self x
  obtain ⟨x0_, hx0_⟩ := hy1
  obtain ⟨w, hw⟩ := hy2
  have hwe : bsM g (J.subschemeι.base w) = y := by simp_all
  exact hdisj x0_ (J.subschemeι.base w) $ tr_ hx0_ hwe.symm

variable (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)


instance instQuasiCompactStario (i : (chosenCoverData T hv).idx) :
    QuasiCompact $ MaxContactOpenCover.coverPieceio T hv i :=
  (quasiCompact_sigmaio
    (fun j : (chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv j) i)

section
variable {i j} (hij : i ≠ j)
include hij
theorem coverPieceio_base_ne_of_ne
    (x : ↥(MaxContactOpenCover.coverPiece T hv i)) (y : ↥(MaxContactOpenCover.coverPiece T hv j)) :
    (MaxContactOpenCover.coverPieceio T hv i).base x ≠ (MaxContactOpenCover.coverPieceio T hv j).base y :=
  sigmaio_base_ne
    (fun k : (chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv k) hij x y

end

section
variable (i : (chosenCoverData T hv).idx)
theorem comap_coverMaxContactIdeal_coverPieceio :
    comap (MaxContactCoverData.cI hv) (MaxContactOpenCover.coverPieceio T hv i) =
      (chosenCoverData T hv).localIdeal i := by
  let _a0 := chosenCoverData T hv
  let _a1 := MaxContactOpenCover.coverPieceio T hv i
  have key : (⨅ j : _a0.idx,
      (siI (_a0.localIdeal j) ≫
        MaxContactOpenCover.coverPieceio T hv j).ker).comap _a1 =
      _a0.localIdeal i := by
    rw [comap_iInf]
    refine le_antisymm (le_trans (iInf_le _ i) (le_of_eq (comap_ker_subschemeio_comp _ (MaxContactOpenCover.coverPieceio T hv i))))
      (le_iInf fun j => ?_)
    rcases eq_or_ne j i with rfl | h
    · exact le_of_eq (comap_ker_subschemeio_comp _ (MaxContactOpenCover.coverPieceio T hv _)).symm
    · rw [ker_subschemeio_comp_comap_eq_top_of_disjoint _a1 (MaxContactOpenCover.coverPieceio T hv j)
    (coverPieceio_base_ne_of_ne T hv h.symm) _]
      exact le_top
  exact key
end

section
variable (hgood : IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv) (tunedMult T))
include hgood
theorem inStrictNormalCrossingPositionAt_of_isMaxContactCover
    x :
    InStrictNormalCrossingPositionAt (MaxContactCoverData.cT hv).structMap
      [MaxContactCoverData.cI hv] x :=
  FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood (comap_coverMaxContactIdeal_coverPieceio T hv) x

theorem inStrictNormalCrossingPosition_of_isMaxContactCover
    (hsm : IsSmoothDivisor (MaxContactCoverData.cT hv).structMap
      (MaxContactCoverData.cI hv)) :
    InStrictNormalCrossingPosition (MaxContactCoverData.cT hv).structMap
      [MaxContactCoverData.cI hv] :=
  FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_coverMaxContactIdeal T hv hgood (comap_coverMaxContactIdeal_coverPieceio T hv) hsm
end

theorem isMaxContactHypersurface_coverMaxContactIdeal
    [LocallyOfFiniteType (MaxContactCoverData.cT hv).structMap]
    (hgood : IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) $ tunedMult T) :
    IsMaxContactHypersurface (MaxContactCoverData.cT hv).base
      (MaxContactCoverData.cT hv).structMap (MaxContactCoverData.cT hv).ideal
      (tunedMult T) $ MaxContactCoverData.cI hv :=
  by
    let hres := comap_coverMaxContactIdeal_coverPieceio T hv
    have := hv.charZero
    have := hv.smooth
    have := hv.locallyOfFiniteType
    intro x
    obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
    have hAff0 : IsAffine $ MaxContactOpenCover.coverPiece T hv i := hgood.isAffine i
    let _a6 := MaxContactOpenCover.coverPieceio T hv i
    have haffineOpen : IsAffineOpen $ MaxContactOpenCover.coverTripleOpen T hv i :=
      isAffineOpen_opensRange _a6
    refine ⟨MaxContactOpenCover.coverTripleOpen T hv i, haffineOpen, hxi, ?_⟩
    have hsub : ∀ y : scheme $ p7 hv,
        y ∈ ((MaxContactOpenCover.coverTripleOpen T hv i) :
          Set (p7 hv).scheme) →
        (p12 T hv).base y ∈
          (((chosenCoverData T hv).opens i) : CSet T.scheme) := by
      intro y hy
      obtain ⟨z, rfl⟩ := hy
      have hz : bsM (p12 T hv) (bsM _a6 z) =
          ((chosenCoverData T hv).opens i).ι.base z :=
        congrArg (bsM · z) $ sigma_io_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens i
      rw [hz]
      exact range_io_base_subset _ ⟨z, rfl⟩
    rcases hgood.dichotomy i with ⟨hdisj, htop⟩ | ⟨n, c, j, hloc, hmc⟩
    left
    constructor
    rw [disjoint_left]
    intro y hy hy2
    have hy3 : y ∈ orderAtLeastLocus
        (cmI (p29 T hv) $ p12 T hv)
        (tunedMult T) := hy
    rw [orderAtLeastLocus_comap T.base T.structMap (p12 T hv)
      (p29 T hv) $ tunedMult T] at hy3
    exact (Set.disjoint_left.mp hdisj) hy3 $ hsub y hy2
    rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, htop]
    exact comap_top _
    right
    refine ⟨n, MaxContactOpenCover.coverEtaleChart T hv i c, j, ?_, ?_⟩
    rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, hloc]
    exact sy_ $ MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}
    have hmc' : c.coordIdeal {j} ≤
        (maxContactIdeal T.base T.structMap (p29 T hv)
          (tunedMult T)).comap
          ((chosenCoverData T hv).opens i).ι := hmc
    have hmax : maxContactIdeal (p7 hv).base
          (p7 hv).structMap
          (p7 hv).ideal (tunedMult T) =
        (maxContactIdeal T.base T.structMap (p29 T hv)
          (tunedMult T)).comap (p12 T hv) :=
      derivIdealSheafIterate_comap T.base T.structMap (p12 T hv)
        (tunedMult T - 1) $ p29 T hv
    let _a5 := MaxContactOpenCover.coverPieceIso T hv i
    have h2 := comap_comap_eq_of_comp_eq (MaxContactOpenCover.coverTripleOpen T hv i).i
      (p12 T hv)
      _a5.inv ((chosenCoverData T hv).opens i).ι
      (MaxContactOpenCover.coverTripleOpen_io_comp_coverMap T hv i)
      (maxContactIdeal T.base T.structMap (p29 T hv)
        (tunedMult T))
    have h3 : comap (c.coordIdeal {j}) _a5.inv ≤
        ((maxContactIdeal T.base T.structMap (p29 T hv)
          (tunedMult T)).comap
            ((chosenCoverData T hv).opens i).ι).comap
          _a5.inv :=
      comap_mono _ hmc'
    show (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} ≤
      restrictIdeal (maxContactIdeal (p7 hv).base
        (p7 hv).structMap
        (p7 hv).ideal $ tunedMult T)
        (MaxContactOpenCover.coverTripleOpen T hv i)
    rw [hmax]
    exact (le_of_eq $ MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}).trans $ le_of_le_of_eq h3 h2.symm

end FunctorialResolution.EmbeddedResolution.MaxContactCoverGeometry

end
end
section

namespace FunctorialResolution.EmbeddedResolution

section
variable (k : Type) [Field k] [CharZero k]
theorem balancedTunedSheaf_eq_self_of_mult_eq_one {X : Sch}
    (pp : X ⟶ Sp k) [Smooth pp]
    [LocallyOfFiniteType pp] (I : ISD X) (m : ℕ) (hm : m = 1) :
    balancedTunedSheaf k pp I m = I := by
  subst hm
  exact balancedTunedSheaf_one k pp I

section
variable {P : Sch} (p) [Smooth p] [LocallyOfFiniteType p] (A : ISD P)
theorem isMaxContactInvariant_of_mult_eq_one m (hm : m = 1)
    (hord : ∀ x : ↥P, orderAt A x ≤ ((1 : ℕ) : ENat)) :
    IsMaxContactInvariant k p A m := by
  subst hm
  unfold IsMaxContactInvariant
  have _i25 : derivIdealSheaf k p A = ⊤ := by
    have hempty : orderAtLeastLocus A 2 = ∅ := by
      ext x
      simp [mem_empty_iff_false, iff_false]
      intro hx
      have h21' : 2 ≤ 1 := by exact_mod_cast (le_trans ((mem_orderAtLeastLocus_iff A 2 x).1 hx) $ hord x)
      omega
    have h := orderAtLeastLocus_derivIdealSheafIterate k p A (r := 1) (m := 2) $ by norm_num
    rw [hempty] at h
    have hiter : derivIdealSheaf k p A = derivIdealSheafIterate k p 1 A := rfl
    rw [hiter]
    refine (eq_top_iff_support_eq_empty _).2 ?_
    ext y
    simp [mem_empty_iff_false, iff_false]
    intro hy
    have hy1 :=
      (mem_orderAtLeastLocus_one_iff _ y).2 hy
    rwa [h] at hy1
  rw [_i25]
  have hmc : maxContactIdeal k p A 1 = A := rfl
  rw [hmc]
  simp
end
end

section
variable (S : MarkedIdealWithBoundary)
theorem projectionToBase_emptyMarkedBlowupSequenceData_comp :
    (S.embs).proj
        (S.embs).length ≫ structMap S
      = structMap S :=
  Category.id_comp S.structMap

theorem ideal_derivedTriple_emptyMarkedBlowupSequenceData (hcz : CharZero S.base)
    (h1 : S.mult = 1)
    (hft : LocallyOfFiniteType
      ((S.embs).proj
        (S.embs).length ≫ S.structMap))
    (hsm : Smooth
      ((S.embs).proj
        (S.embs).length ≫ S.structMap))
    (extra : List ((S.embs).obj
      (S.embs).length).IdealSheafData)
    (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S (S.embs) hft
      extra keep).ideal = S.ideal := by
  let _c0 := S.embs
  rw [LowerDimReductionPullback.ideal_derivedTriple]
  exact trans
    (balancedTunedSheaf_eq_self_of_mult_eq_one S.base
      (_c0.proj
        _c0.length ≫ tMp S)
      (_c0.ideal
        _c0.length) S.mult h1)
    (emptyMarkedBlowupSequenceData_ideal S.structMap S.ideal S.mult S.boundary
      _c0.length)

theorem mult_derivedTriple_emptyMarkedBlowupSequenceData (h1 : mult S = 1)
    (hft : LocallyOfFiniteType
      ((S.embs).proj
        (S.embs).length ≫ structMap S))
    (extra : List ((S.embs).obj
      (S.embs).length).IdealSheafData)
    (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S (S.embs) hft
      extra keep).mult = 1 := by
  rw [derivedTriple_mult, h1]
  exact tuningExponent_one

section
variable (hft : LocallyOfFiniteType ((S.embs).proj (S.embs).length ≫ structMap S)) (extra : List ((S.embs).obj (S.embs).length).IdealSheafData)
theorem structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData
    (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S (S.embs) hft
      extra keep).structMap = structMap S := by
  rw [derivedTriple_structureMorphism]
  exact projectionToBase_emptyMarkedBlowupSequenceData_comp S

theorem boundary_derivedTriple_emptyMarkedBlowupSequenceData :
    (MaxContactCoverData.derivedTriple S (S.embs) hft
      extra S.boundary.length).boundary = extra := by
  have hdrop : drop (bLen S)
      ((S.embs).boundary
        (S.embs).length) = [] := by
    rw [emptyMarkedBlowupSequenceData_boundary S.structMap S.ideal S.mult S.boundary (S.embs).length]
    simp
  rw [p48, hdrop]
  exact append_nil extra
end
end

section
variable {k : Type} [Field k]
private theorem markedIdealWithBoundary_mk_congr__b1 {X : Sch}
    {p p' : X ⟶ Sp k} {I I' : ISD X} {m m' : ℕ}
    {E E' : Bdy X}
    (hp : p = p') (hI : I = I') (hm : m = m') (hE : E = E') :
    mk k X p I m E = mk k X p' I' m' E' :=by simp_all
theorem isomorphic_of_emptyMarkedBlowupSequenceData_append {X : Sch}
    (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
    (E : Bdy X)
    (t : MarkedBlowupSequenceData
      ((emptyMarkedBlowupSequenceData p I m E).proj (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length ≫ p)
      ((emptyMarkedBlowupSequenceData p I m E).ideal (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length) m
      ((emptyMarkedBlowupSequenceData p I m E).boundary (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance) :
    ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toSequenceOfBlowups.Isomorphic t.toSequenceOfBlowups := by
  have hmain := emptyMarkedBlowupSequenceData_append_isomorphic p I m E t hinv
  rwa [toMarkedSequence_toSequenceOfBlowups $ (emptyMarkedBlowupSequenceData p I m E).append t hinv, toMarkedSequence_toSequenceOfBlowups t] at hmain

theorem isMaxContactHypersurface_one_of_etaleChart [CharZero k]
    {P : Sch} p [Smooth p]
    [LocallyOfFiniteType p] (A D : ISD P)
    (hchart : ∀ x : ↥P, x ∈ D.support →
      ∃ (U : Opn P) (n : ℕ) (c : EtaleChart p U n) (j : Fin n),
        x ∈ U ∧ restrictIdeal D U = c.coordIdeal ({j} : FinSet n))
    (hDle : D ≤ A) :
    IsMaxContactHypersurface k p A 1 D := by
  intro x
  by_cases hx : x ∈ spI D
  obtain ⟨U, n, c, j, hxU, hcoord⟩ := hchart x hx
  obtain ⟨V, hVaff, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset hxU
  refine ⟨V, hVaff, hxV, inr ⟨n, c.restrict hVU, j, restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D ({j} : FinSet n) hcoord, ?_⟩⟩
  rw [isMaxContactCoord_one_iff,
    ← restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D ({j} : FinSet n) hcoord,
    restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io]
  exact comap_mono _ hDle
  have hclosed := D.support.isClosed
  let _a0 := suppI D
  obtain ⟨V, hVaff, hxV, hVW⟩ :
      ∃ V, IsAffineOpen V ∧ x ∈ V ∧
        V ≤ (⟨_a0ᶜ, hclosed.isOpen_compl⟩ : Opn P) :=
    exists_isAffineOpen_mem_and_subset hx
  have hdisj : Disjoint _a0 $ opS V := by
    rw [disjoint_right]
    intro y hyV hyD
    exact (hVW hyV) hyD
  refine ⟨V, hVaff, hxV, inl ⟨?_, (restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr fun y hyV hyD => Set.disjoint_left.mp hdisj hyD hyV⟩⟩
  rw [disjoint_left]
  intro y hy hyV
  exact (Set.disjoint_left.mp hdisj $ (one_le_orderAt_iff_mem_support D y).1 $ le_trans ((one_le_orderAt_iff_mem_support A y).2 $ (mem_orderAtLeastLocus_one_iff A y).1 hy) $ orderAt_le_of_le hDle y) hyV
end

theorem coordIdeal_comp_map_eq_comap {X Y : Sch} {k : Type} [Field k]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {U : Opn X} {V : Opn Y} {n : ℕ} (c : EtaleChart p U n)
    (ph_ : (V : Sch) ⟶ (U : Sch))
    (hcs : (ph_ ≫ c.map) ≫ affineSpaceFinToSpec k n = V.i ≫ q)
    (he : Etale $ ph_ ≫ c.map) (S : FinSet n) :
    (⟨ph_ ≫ c.map, hcs, he⟩ : EtaleChart q V n).coordIdeal S = (c.coordIdeal S).comap ph_ := by
  rw [p33, p33]
  let _a0 := coordSubspaceIdeal k n S
  show _a0.comap (ph_ ≫ c.map)
      = (_a0.comap c.map).comap ph_
  rw [comap_comp]

theorem IsMaxContactHypersurface.comap_of_isOpenImmersionAtSource {k : Type} [Field k] [CharZero k]
    {P P' : Sch} (p : P ⟶ Sp k) [Smooth p]
    [LocallyOfFiniteType p] {A H : ISD P}
    (hH : IsMaxContactHypersurface k p A 1 H) (g : P' ⟶ P) [Smooth g]
    [LocallyOfFiniteType $ g ≫ p]
    (hg : MaxContactFunctoriality.IsLocalIsomorphism g) :
    IsMaxContactHypersurface k (g ≫ p) (A.comap g) 1 $ H.comap g := by
  let _a1 := g ≫ p
  have : Smooth _a1 := inferInstance
  intro x'
  obtain ⟨U0_, hxU0_, hoi⟩ := hg x'
  have := hoi
  obtain ⟨U, _, hxU, hcase⟩ := hH $ bsM g x'
  obtain ⟨V, hVaff, hxV, hVW⟩ :
      ∃ V, IsAffineOpen V ∧ x' ∈ V ∧ V ≤ U0_ ⊓ (pre g U) :=
    exists_isAffineOpen_mem_and_subset (⟨hxU0_, hxU⟩ : x' ∈ U0_ ⊓ (pre g U))
  have hVpre := le_trans hVW inf_le_right
  obtain ⟨ph_, hph⟩ : ∃ ph_, ph_ = P'.homOfLE hVpre ≫ (g.mr U) := ⟨_, rfl⟩
  have hfac : V.i ≫ g = ph_ ≫ U.i := by
    rw [hph, assoc, morphismRestrict_ι, ← assoc, P'.homOfLE_ι]
  have hoiV : IsOpenImmersion $ V.i ≫ g := by
    have hrw : V.i ≫ g = P'.homOfLE (le_trans hVW inf_le_left) ≫ (U0_.i ≫ g) := by
      rw [← assoc, P'.homOfLE_ι]
    rw [hrw]
    infer_instance
  have : IsOpenImmersion $ ph_ ≫ U.i := by
    rwa [← hfac]
  have :=
    of_comp ph_ U.i
  have : Etale ph_ := inferInstance
  have hcomapres : ∀ J : ISD P,
      restrictIdeal (J.comap g) V = (restrictIdeal J U).comap ph_ := by
    intro J
    rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
      ← comap_comp, hfac]
  refine ⟨V, hVaff, hxV, ?_⟩
  rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmc⟩
  refine inl ⟨?_, ?_⟩
  rw [orderAtLeastLocus_comap k p g A 1, disjoint_left]
  intro y hy hyV
  exact (Set.disjoint_left.mp hdisj hy) $ hVpre hyV
  rw [hcomapres H, htop]
  simp
  have := c.isEtale
  let _a0 := ph_ ≫ c.map
  have hcs : _a0 ≫ affineSpaceFinToSpec k n = V.i ≫ _a1 := by
    rw [assoc, c.comp_struct, ← assoc, ← hfac, assoc]
  have he : Etale _a0 := inferInstance
  refine inr ⟨n, ⟨_a0, hcs, he⟩, j, ?_, ?_⟩
  rw [hcomapres H, hcoord, coordIdeal_comp_map_eq_comap c ph_ hcs he]
  rw [isMaxContactCoord_one_iff, coordIdeal_comp_map_eq_comap c ph_ hcs he, hcomapres A]
  exact comap_mono _ $ (isMaxContactCoord_one_iff k p A c j).1 hmc

theorem isBalanced_of_eq_derivedTriple_emptyMarkedBlowupSequenceData (hstar : MaxContactCoverProperties)
    (S : MarkedIdealWithBoundary) (hSV : IsAdmissible S)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((mult S : ℕ) : ENat))
    (hft : LocallyOfFiniteType
      ((S.embs).proj
        (S.embs).length ≫ structMap S))
    (L : List ((S.embs).obj
      (S.embs).length).IdealSheafData)
    (keep : ℕ) (D : MarkedIdealWithBoundary)
    (hDeq : MaxContactCoverData.derivedTriple S
      (S.embs) hft L keep = D)
    (hVD : IsAdmissible D) :
    ∀ hft2 : LocallyOfFiniteType D.structMap, D.IsBalanced hft2 := by
  subst hDeq
  intro hft2
  exact LowerDimReductionPullback.isBalanced_derivedTriple hstar S hSV hSV.one_le_mult hord
    (S.embs) hft L keep hVD

theorem isomorphic_of_isMaxContactHypersurface_singleton_boundary (hin : OrderReduction.OrderReductionHypotheses)
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A0 B : PrincipalizationAssignment)
    (hspec0 : IsBoundaryDivisorReduction P 0 A0 B) (S : MarkedIdealWithBoundary)
    [CharZero S.base] [Smooth S.structMap]
    [LocallyOfFiniteType S.structMap]
    (hSV : IsAdmissible S) (hP : P S.krullDimSucc)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((mult S : ℕ) : ENat))
    (hm1 : mult S = 1) (H1_ H2_ : tISD S) (hbd : boundary S = [H1_])
    (hD : ∀ hft2 : LocallyOfFiniteType S.structMap, S.IsBalanced hft2)
    (hV2_ : IsAdmissible $ withBoundary S [H2_])
    (hH1 : IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H1_)
    (hH2_ : IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H2_) :
    (A0 S).toSequenceOfBlowups.Isomorphic (A0 $ withBoundary S [H2_]).toSequenceOfBlowups := by
  refine DivisorReductionIndependence.isomorphic_withBoundary_cons_of_isMaxContactHypersurface hin P hmono A0 B hspec0 S hSV hP hord hD ?_
    [] H1_ H2_ hbd hV2_ (by intro _i; exact hH1) (by intro _i; exact hH2_)
  intro _i
  refine isMaxContactInvariant_of_mult_eq_one S.base S.structMap S.ideal S.mult hm1 ?_
  intro x
  have hx := hord x
  rwa [hm1] at hx

namespace MaxContactCoverData

section
variable (hstar : MaxContactCoverProperties) (hin : OrderReduction.OrderReductionHypotheses) (hinv : ComapIsoInvariance) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (T : MarkedIdealWithBoundary) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) (hbd : boundary T = []) (hmult : mult T = 1) {Y : Sch} (e : Y ⟶ scheme T) [IsClosedImmersion e]
include hstar hin hmono hspec hbd hmult
section
variable (hadm : ∀ [LocallyOfFiniteType T.structMap], IsMaxContactHypersurface T.base T.structMap T.ideal T.mult (ker e)) (hV : IsAdmissible (withBoundary T [ker e]))
include hadm hV
theorem isStrictPullbackBlowupSeq_cover_of_eq_append
    (s : MarkedBlowupSequenceData (cT h.valid).structMap (cT h.valid).ideal
      (cT h.valid).mult (cT h.valid).boundary)
    (hs : s = emptyMarkedBlowupSequenceData (cT h.valid).structMap (cT h.valid).ideal
      (cT h.valid).mult (cT h.valid).boundary)
    (hft : LocallyOfFiniteType
      (s.proj s.length ≫ (cT h.valid).structMap))
    (hVc : (derivedTriple (cT h.valid) s hft
      [strictTransformAtLength s (cI h.valid)]
      (cT h.valid).boundary.length).IsAdmissible)
    (hmk : (ofSequenceOfBlowups (A 0 (derivedTriple (cT h.valid) s hft
        [strictTransformAtLength s (cI h.valid)]
        (cT h.valid).boundary.length)).toSequenceOfBlowups).IsMarked
      (s.proj s.length ≫ (cT h.valid).structMap) (s.ideal s.length)
      (cT h.valid).mult (s.boundary s.length))
    (heq : coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)
      = s.append ((ofSequenceOfBlowups (A 0 (derivedTriple (cT h.valid) s hft
          [strictTransformAtLength s (cI h.valid)]
          (cT h.valid).boundary.length)).toSequenceOfBlowups).toMarkedBlowupSequenceData
        (s.proj s.length ≫ (cT h.valid).structMap) (s.ideal s.length)
        (cT h.valid).mult (s.boundary s.length) hmk) hinv) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (T.withBoundary [ker e])).toSequenceOfBlowups := by
  let _c0 := emptyMarkedBlowupSequenceData (cT h.valid).structMap (cT h.valid).ideal (cT h.valid).mult (cT h.valid).boundary
  let _c1 := cT h.valid
  let _c2 := coverMap T h.valid
  let _c3 := tWB T [ker e]
  let _c4 := cI h.valid
  let _c5 := T.embs
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have : CharZero T.base := h.valid.charZero
  subst hs
  have := hft
  have hVcover :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P T h
  have hftC :=
    hVcover.locallyOfFiniteType
  have hsmC := hVcover.smooth
  have hczC := hVcover.charZero
  have hczPB : CharZero
      (_c3.pullbackAlong
        _c1.scheme _c1.structMap
        _c2).base := h.valid.charZero
  have hsmPB : Smooth
      (_c3.pullbackAlong
        _c1.scheme _c1.structMap
        _c2).structMap := hVcover.smooth
  have hftPB := hVcover.locallyOfFiniteType
  have hOcover := BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P T h
  have hsm :=
    BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar _c1 hVcover
      _c0
      _c0.length le_rfl
  have := hsm
  have htunedIdeal : balancedTunedIdeal T h.valid = T.ideal :=
    balancedTunedSheaf_eq_self_of_mult_eq_one T.base T.structMap T.ideal T.mult hmult
  have hcoverMult : _c1.mult = 1 := by
    rw [coverTriple_mult]
    show tuningExponent T.mult = 1
    rw [hmult]
    exact tuningExponent_one
  have hcoverIdeal : _c1.ideal = T.ideal.comap _c2 := by
    rw [coverTriple_ideal, htunedIdeal]
  have hftE : LocallyOfFiniteType
      (_c5.proj
        _c5.length ≫ tMp T) := by
    rw [projectionToBase_emptyMarkedBlowupSequenceData_comp T]
    exact h.valid.locallyOfFiniteType
  have hsmE : Smooth
      (_c5.proj
        _c5.length ≫ tMp T) := by
    rw [projectionToBase_emptyMarkedBlowupSequenceData_comp T]
    exact h.valid.smooth
  have hbdE : (derivedTriple T _c5 hftE
      [ker e] 0).boundary
      = [ker e] := by
    rw [derivedTriple_boundary, tr_ (congrArg (drop 0) (emptyMarkedBlowupSequenceData_boundary T.structMap T.ideal T.mult T.boundary _c5.length)) (tr_ (congrArg (drop 0) hbd) rfl)]
    exact append_nil [ker e]
  have hbalanced := isBalanced_of_eq_derivedTriple_emptyMarkedBlowupSequenceData hstar T h.valid h.orderLE hftE
    [ker e] 0
    _c3 (markedIdealWithBoundary_mk_congr__b1 (structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData T hftE [ker e] 0) (ideal_derivedTriple_emptyMarkedBlowupSequenceData T h.valid.charZero hmult hftE hsmE [ker e] 0) (tr_ (mult_derivedTriple_emptyMarkedBlowupSequenceData T hmult hftE [ker e] 0) hmult.symm) hbdE) hV
  have hpb := DivisorReductionIndependence.isAdmissible_and_isStrictPullbackBlowupSeq_of_etale hin P hmono (A 0) B (hspec 0)
    _c3 hV h.dim_prop h.orderLE hbalanced
    (succ_pos 0) _c1.scheme _c1.structMap
    _c2 (etale_coverMap_of_isAdmissible T h.valid) (hVcover.quasiCompact)
    (coverTriple_structureMorphism T h.valid).symm fun x _ => (surjective_coverMap T h.valid (hstar.exists_goodCover T h.valid h.orderLE)).1 x
  have hEqU :=
    markedIdealWithBoundary_mk_congr__b1
      (structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData _c1 hft
        [cmI (ker e) _c2]
        (bLen _c1))
      (tr_ (ideal_derivedTriple_emptyMarkedBlowupSequenceData _c1 hczC hcoverMult hft hsm
        [cmI (ker e) _c2]
        (bLen _c1)) hcoverIdeal)
      (tr_ (mult_derivedTriple_emptyMarkedBlowupSequenceData _c1 hcoverMult hft
        [cmI (ker e) _c2]
        (bLen _c1)) hmult.symm)
      (boundary_derivedTriple_emptyMarkedBlowupSequenceData _c1 hft [cmI (ker e) _c2])
  have hDU := isBalanced_of_eq_derivedTriple_emptyMarkedBlowupSequenceData hstar _c1 hVcover
    hOcover hft
    [cmI (ker e) _c2]
    (bLen _c1)
    (_c3.pullbackAlong
      _c1.scheme _c1.structMap
      _c2) hEqU hpb.1
  have htri : derivedTriple _c1
      _c0 hft
      [strictTransformAtLength
        _c0
        _c4]
      (bLen _c1)
      = tWB (_c3.pullbackAlong
          _c1.scheme _c1.structMap
          _c2)
        [strictTransformAtLength
          _c0
          _c4] :=
    markedIdealWithBoundary_mk_congr__b1
      (structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData _c1 hft
        [strictTransformAtLength
          _c0
          _c4]
        (bLen _c1))
      (tr_ (ideal_derivedTriple_emptyMarkedBlowupSequenceData _c1 hczC hcoverMult hft hsm
        [strictTransformAtLength
          _c0
          _c4]
        (bLen _c1)) hcoverIdeal)
      (tr_ (mult_derivedTriple_emptyMarkedBlowupSequenceData _c1 hcoverMult hft
        [strictTransformAtLength
          _c0
          _c4]
        (bLen _c1)) hmult.symm)
      (boundary_derivedTriple_emptyMarkedBlowupSequenceData _c1 hft [strictTransformAtLength _c0 _c4])
  have hV2_ : tAd (tWB (_c3.pullbackAlong
        _c1.scheme _c1.structMap
        _c2)
      [strictTransformAtLength
        _c0
        _c4]) := by
    rwa [← htri]
  have hcmp := hftC
  rw [coverTriple_structureMorphism T h.valid] at hcmp
  have hadm1 : IsMaxContactHypersurface T.base T.structMap T.ideal 1
      (ker e) := by simp_all
  have hkey := IsMaxContactHypersurface.comap_of_isOpenImmersionAtSource T.structMap hadm1
    _c2 (MaxContactOpenCover.isLocalIsomorphism_coverMap T h.valid)
  have hA1 : ∀ m, m = 1 →
      @IsMaxContactHypersurface T.base _ _c1.scheme
        _c1.structMap hftC
        (T.ideal.comap _c2) m
        (cmI (ker e) _c2) := by
    rintro m rfl
    exact @isMaxContactHypersurface_of_eq_of_eq_of_eq T.base _ _c1.scheme
      (coverMap T h.valid ≫ tMp T) _c1.structMap hcmp hftC
      (T.ideal.comap _c2) (T.ideal.comap _c2)
      (cmI (ker e) _c2)
      (cmI (ker e) _c2) 1
      (coverTriple_structureMorphism T h.valid).symm rfl rfl hkey
  have htrm : ∀ m, tMu _c1 = m →
      IsMaxContactHypersurface _c1.base
        (_c0.proj
          _c0.length ≫
          _c1.structMap)
        (_c0.ideal
          _c0.length) m
        (strictTransformAtLength
          _c0
          _c4) := by
    rintro m rfl
    exact isMaxContactHypersurface_iteratedStrictTransform hstar _c1 hVcover hOcover
      _c4 (BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P T h)
      _c0
      _c0.length le_rfl
  have hA2 : ∀ m, m = 1 →
      @IsMaxContactHypersurface T.base _ _c1.scheme
        _c1.structMap hftC
        (T.ideal.comap _c2) m
        (strictTransformAtLength
          _c0
          _c4) := by
    rintro m rfl
    exact @isMaxContactHypersurface_of_eq_of_eq_of_eq T.base _ _c1.scheme
      (_c0.proj
        _c0.length ≫
        _c1.structMap)
      _c1.structMap hft hftC
      (_c0.ideal
        _c0.length)
      (T.ideal.comap _c2)
      (strictTransformAtLength
        _c0
        _c4)
      (strictTransformAtLength
        _c0
        _c4) 1
      (projectionToBase_emptyMarkedBlowupSequenceData_comp _c1)
      (tr_ (emptyMarkedBlowupSequenceData_ideal _c1.structMap _c1.ideal
        _c1.mult _c1.boundary
        _c0.length)
        hcoverIdeal)
      rfl (htrm 1 hcoverMult)
  have hTO : ∀ x : (tSch (_c3.pullbackAlong
      _c1.scheme _c1.structMap
      _c2)),
      orderAt ((_c3.pullbackAlong
        _c1.scheme _c1.structMap
        _c2).ideal) x ≤
      (((tMu (_c3.pullbackAlong
        _c1.scheme _c1.structMap
        _c2)) : ℕ) : ENat) := by
    intro x
    show orderAt (T.ideal.comap _c2) x ≤ (tMu T : ENat)
    rw [orderAt_comap T.base T.structMap _c2 T.ideal x]
    exact h.orderLE _
  have hbdPB : ((_c3.pullbackAlong
      _c1.scheme _c1.structMap
      _c2).boundary)
      = [cmI (ker e) _c2] := rfl
  have hAdmEq := isomorphic_of_isMaxContactHypersurface_singleton_boundary hin P hmono (A 0) B (hspec 0)
    (_c3.pullbackAlong
      _c1.scheme _c1.structMap _c2)
    hpb.1 (hmono _ _ (hstar.coverTriple_dim_le T h.valid) h.dim_prop) hTO hmult
    (cmI (ker e) _c2)
    (strictTransformAtLength
      _c0
      _c4)
    hbdPB hDU hV2_ (hA1 T.mult hmult) (hA2 T.mult hmult)
  have hEq : (coverMarkedBlowupData T h.valid hinv (p49 A T)).toSequenceOfBlowups.Isomorphic
      (A 0 (derivedTriple _c1
        _c0 hft
        [strictTransformAtLength
          _c0
          _c4]
        (bLen _c1))).toSequenceOfBlowups := by
    rw [heq]
    exact Isomorphic.trans
      (isomorphic_of_emptyMarkedBlowupSequenceData_append _c1.structMap
        _c1.ideal _c1.mult
        _c1.boundary
        ((ofSequenceOfBlowups (A 0 (derivedTriple _c1
            _c0 hft
            [strictTransformAtLength
              _c0
              _c4]
            (bLen _c1))).toSequenceOfBlowups).toMarkedBlowupSequenceData
          (_c0.proj
            _c0.length ≫
            _c1.structMap)
          (_c0.ideal
            _c0.length)
          _c1.mult
          (_c0.boundary
            _c0.length) hmk)
        hinv) (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _)
  have hheq : HEq ((A 0 (derivedTriple _c1
        _c0 hft
        [strictTransformAtLength
          _c0
          _c4]
        (bLen _c1))).toSequenceOfBlowups)
      ((A 0 (tWB (_c3.pullbackAlong
          _c1.scheme _c1.structMap
          _c2)
        [strictTransformAtLength
          _c0
          _c4])).toSequenceOfBlowups) := by
    rw [htri]
  rw [eq_of_heq hheq] at hEq
  exact hpb.2.of_isomorphic_pullback (hAdmEq.trans hEq.symm)

theorem isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isMaxContactHypersurface :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (withBoundary T [ker e])).toSequenceOfBlowups := by
  let _a0 := cT h.valid
  let _a1 := BoundarySeparationByMaxContact.separateAllBoundary T h.valid hinv A
  have hs : _a1
      = emptyMarkedBlowupSequenceData _a0.structMap _a0.ideal
          _a0.mult _a0.boundary := by
    let _a2 := p49 A T
    show separateBoundary hinv T _a2
        _a0 (_a0.boundary.length) = _
    rw [congrArg length $ (coverTriple_boundary T h.valid).trans $ tr_ (congrArg (m39 fun D : tISD T => cmI D $ coverMap T h.valid) hbd) map_nil]
    exact separateBoundary_zero hinv T _a2 _
  obtain ⟨hft, hVc, _, hmk, heq, _⟩ :=
    BoundarySeparationByMaxContact.exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  exact isStrictPullbackBlowupSeq_cover_of_eq_append hstar hin hinv P hmono A B hspec T h hbd hmult
    e hadm hV _a1 hs hft hVc hmk heq
end

theorem isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_etaleChart
    (hchart : ∀ x : ↥T.scheme, x ∈ support (ker e) →
      ∃ (U : T.scheme.Opens) (n : ℕ) (c : EtaleChart T.structMap U n) (j : Fin n),
        x ∈ U ∧ restrictIdeal (ker e) U =
          c.coordIdeal ({j} : FinSet n))
    (hle : ker e ≤ ideal T)
    (hV : IsAdmissible $ withBoundary T [ker e]) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv $ MaxContactFunctoriality.lowerDimensionalFamily A T).toSequenceOfBlowups
      (A 0 $ withBoundary T [ker e]).toSequenceOfBlowups := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have := h.valid.charZero
  refine isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isMaxContactHypersurface hstar hin hinv P hmono A B hspec T h hbd
    hmult e ?_ hV
  intro hftinst
  have := hftinst
  rw [hmult]
  exact isMaxContactHypersurface_one_of_etaleChart T.structMap T.ideal
    (ker e) hchart hle

theorem isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isSmoothDivisor
    (hdiv : IsSmoothDivisor T.structMap $ ker e)
    J (hJ : ideal T = imageIdealSheaf e J)
    (hV : IsAdmissible $ withBoundary T [ker e]) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv $ MaxContactFunctoriality.lowerDimensionalFamily A T).toSequenceOfBlowups
      (A 0 $ withBoundary T [ker e]).toSequenceOfBlowups := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have := h.valid.charZero
  refine isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_etaleChart hstar hin hinv P hmono A B hspec T h hbd hmult
    e ?_ ?_ hV
  intro x hx
  exact exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton T.structMap
    (ker e) hdiv x hx
  rw [hJ, imageIdealSheaf_eq_ker]
  intro U
  exact le_ker_comp ..
end

end MaxContactCoverData

end FunctorialResolution.EmbeddedResolution
end
end
-- BEGIN_E2_PROJ_Bundle13
noncomputable section
open CategoryTheory AlgebraicGeometry
abbrev p16 := @FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.separateBoundaryOfFamily
end
-- END_E2_PROJ_Bundle13
end
