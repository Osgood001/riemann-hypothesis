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
noncomputable section
open CategoryTheory AlgebraicGeometry
open FunctorialResolution.Blowup (IsBlowupAlongIdealSheaf IsLocallyGeneratedByNonZeroDivisor StrictTransformIsBlowupOfClosedSubscheme blowup comap_io_support_compl_eq_top exceptionalIdeal exceptionalIdeal_eq_comap strictTransform)
open List (Lex cons_append eraseIdx filter_cons foldr_cons get getElem_append_left getElem_append_right getElem_map get_eq_getElem get_of_mem length length_cons length_eraseIdx length_map length_nil map map_append map_congr_left map_cons map_map map_nil map_ofFn mem_append mem_append_left mem_append_right mem_cons mem_cons_of_mem mem_cons_self mem_iff_getElem mem_map mem_map_of_mem mem_singleton_self ofFn prod_cons prod_nil sum_ofFn take)
open Set (InjOn MapsTo disjoint_left empty_subset exists_max_image finite_iUnion finite_range image_insert_eq image_mono image_preimage_eq_of_subset image_singleton image_subset_iff image_subset_range indicator_apply indicator_of_mem mem_empty_iff_false mem_iUnion mem_image_of_mem mem_ofPred_eq mem_range_self mem_sUnion mem_singleton mem_singleton_iff mem_union ncard_lt_ncard nonempty_iff_ne_empty preimage_compl range range_comp sUnion sUnion_eq_biUnion singleton_subset_iff subset_empty_iff)
open Finset (card_attach card_erase_of_mem card_image_of_injective card_pos coe_insert coe_singleton cons_induction eq_empty_or_nonempty finite_toSet image image_id image_image induction_on mem_biUnion mem_erase mem_filter mem_image mem_univ prod_congr prod_empty prod_eq_single prod_mul_distrib subset_univ sum_add_distrib sum_congr sum_filter sum_ite_mem sum_le_sum_of_subset sum_subset univ)
open Nat (add_sub_cancel' cast_add cast_mul cast_sum le_induction le_succ le_zero lt_of_succ_le lt_or_ge lt_succ_iff lt_succ_of_lt lt_succ_self not_lt_zero sInf_eq_zero sInf_le sInf_mem sSup_mem sub_add_cancel zero_le)
open Fin (cases_succ cases_zero cast eq_of_val_eq eq_zero_or_eq_succ last lt_def prod_univ_zero succ_lt_succ_iff succ_pos val_injective)
open Ideal (eq_top_iff_one exists_le_prime_disjoint le_comap_map mem_span_singleton_self mul_le_right quotientMap quotientMap_mk span_insert span_le)
open FunctorialResolution.EmbeddedResolution.DivisorReduction (amb ambientBlowupSeq_length comap_controlledTransform_of_containedComponentsIdeal_eq_top comap_controlledTransform_prepend_ambientBlowupSeq containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf controlledTransform_prepend_ambientBlowupSeq_one exists_isClosed_opens_goingUpInvariantOnOpen goingUpInvariant_of_le isAdmissible_restrictTwistedToDivisor isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top isMarked_prepend_ambientBlowupSeq isOpen_preimage_support_containedComponentsIdeal lowerBoundaryWithoutBlowup lowerBoundaryWithoutBlowup_eq lowerIdealWithoutBlowup orderAtLeastLocus_controlledTransform_inter_ker_support_eq_empty orderAtLeastLocus_inter_support_ker_eq_empty preimageSupportEqComponentsInOrderLocus_of_isAdmissible)
open Ideal.Quotient (eq_zero_iff_mem mk)
open FunctorialResolution.Blowup.blowup (proj)
open Submonoid (closure_induction closure_le closure_mono mem_closure)
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (append_dataAt_last append_dataAt_of_forall boundarySupport_dataAt ofMarkedSequence ofMarkedSequence_length toMarkedSequence_blowupMorphism toMarkedSequence_boundary toMarkedSequence_center toMarkedSequence_ideal toMarkedSequence_length toMarkedSequence_projectionToBase toMarkedSequence_projectionToSpec toMarkedSequence_schemeAt)
open ULift (up)
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups (exceptionalDivisor_eq ideal_zero inStrictNormalCrossingPosition_projectionToSpec_boundary isResolution_iff lastIdeal_eq mem_boundaryLocus_iff nonzeroOnComponents_ideal_of_isAdmissible projectionToSpec projectionToSpec_eq smooth_projectionToSpec)
open TopologicalSpace.Opens (coe_inf isBasis_iff_nbhd isOpen)
open Scheme.IdealSheafData (comap_comp comap_mul comap_pow comap_sup comap_top eq_top_iff_support_eq_empty ideal_mul le_def mem_support_comap mem_support_iff_of_mem mul_inf notMem_support_of_comap_ι_eq_top ofIdealTop one_eq_top subschemeι support support_antitone support_comap support_mul support_pow)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (SameNontrivialBoundary bc boundary ideal isOrderBoundedByMult_iff mc mult nontrivialPart sameNontrivialBoundary_iff scheme structMap withBoundary)
open Scheme.Hom (isClosedEmbedding ker pre preimage_mono support_ker)
open Subtype (val)
open TopologicalSpace (Closeds NoetherianSpace)
open Or (inl inr)
open Set.Finite (bddAbove isClosed_biUnion subset)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary.SameNontrivialBoundary (refl)
open TopologicalSpace.NoetherianSpace (exists_finset_irreducible finite_irreducibleComponents)
open And (left right)
open FunctorialResolution.EmbeddedResolution.MonomialCenter (IsLocallyMonomialTriple sortedIndices)
open Iff (mp)
open Scheme.Opens (ι)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (center projectionToBase schemeAt transitionMap transitionMapSucc)
open PrimeSpectrum (asIdeal)
open Scheme (IdealSheafData Opens basicOpen)
section


namespace FunctorialResolution.EmbeddedResolution

section
variable (T : MarkedIdealWithBoundary)
private theorem lowerIdealWithoutBlowup_eq_ideal :
    lowerIdealWithoutBlowup T = ideal T :=by simp_all
private theorem orderAt_le_mult_of_isOrderBoundedByMult (hOB : T.IsOrderBoundedByMult) :
    ∀ x, orderAt T.ideal x ≤ (mult T : ENat) := hOB

private theorem isDerivBalanced_of_isBalanced (hV : T.IsAdmissible)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) :
    ∀ [_inst : LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult := by
  intro _
  exact hbal
end

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian)
theorem divisorReductionProperties_of_blowupPreservesNoetherian : DivisorReductionTerminationProperties hres hno := by
  have hlift := hasStrictNormalCrossingsWith_ker_cons_of_comap
  exact
    { isBlowup_id_preIdeal := fun T hV j hj => isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV j hj
      lowerTriple_dim_lt := fun T hV hne j hj I0 E0 => dim_restrictToBoundaryDivisor_lt T hV hne j hj I0 E0
      valid_lowerTop := fun T hV hOB hbal j hj hZ => DivisorReduction.isAdmissible_restrictToDivisor T hV hOB hbal j hj hZ
      properCenters := fun T hV hm s => MarkedSequenceOfBlowups.centersContainNoComponent_ofMarkedSequence effectiveCartierSupportContainsNoComponent hV s
      isMarked_pushedTop := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr
        have := inst
        exact isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hVlow s hpr
      isMarked_pushedPre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr
        have := inst
        exact isMarked_prepend_ambientBlowupSeq hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
          s hpr
          (smooth_subschemeio_containedComponentsIdeal_comp T hV j hj)
          (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
          (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
          (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
          (isOpen_preimage_support_containedComponentsIdeal T j hj
            (preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
      valid_lowerPre := by
        intro T hV hOB hbal j hj hZ
        exact isAdmissible_restrictTwistedToDivisor T hV hOB hbal j hj hZ
      orderAt_ctrlIdeal_le_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr i hi x
        have := inst
        have := hV.charZero
        have := hV.smooth
        exact orderAt_controlledTransform_le_of_isMarked T.base T.structMap T.ideal T.mult T.boundary
          (amb hres hno hpr)
          (isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hVlow
            s hpr)
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) i
          (by rw [ambientBlowupSeq_length]; exact hi) x
      orderAt_ctrlIdeal_le_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr i hi x
        have := inst
        have := hV.charZero
        have := hV.smooth
        exact orderAt_controlledTransform_le_of_isMarked T.base T.structMap T.ideal T.mult T.boundary
          (p18 (p28 hj) hb
            (amb hres hno hpr))
          (isMarked_prepend_ambientBlowupSeq hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
            s hpr
            (smooth_subschemeio_containedComponentsIdeal_comp T hV j hj)
            (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
            (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
            (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
            (isOpen_preimage_support_containedComponentsIdeal T j hj
              (preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj)))
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) i
          (by rw [BlowupSequenceData.prepend_length, ambientBlowupSeq_length]; exact hi) x
      coSupport_inter_ker_eq_empty_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr hempty
        have := inst
        have := hV.charZero
        have := hV.smooth
        have := hV.locallyOfFiniteType
        have hgoingUp := by
          have hbalLower : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by
            rwa [lowerIdealWithoutBlowup_eq_ideal]
          have hE0_ : InStrictNormalCrossingPosition T.structMap $ lowerBoundaryWithoutBlowup T := by
            rw [lowerBoundaryWithoutBlowup_eq]
            exact hV.snc
          have hjE := hj
          rw [← lowerBoundaryWithoutBlowup_eq] at hjE
          have hget : (lowerBoundaryWithoutBlowup T)[j]'hjE = T.boundary[j]'hj := by
            simp [lowerBoundaryWithoutBlowup_eq T]
          have hlen : length (eraseIdx (lowerBoundaryWithoutBlowup T) j) = bLen T - 1 := by
            rw [lowerBoundaryWithoutBlowup_eq]
            simp [length_eraseIdx, hj]
          have htrunc : take (bLen T - 1) (eraseIdx (lowerBoundaryWithoutBlowup T) j)
              = eraseIdx (lowerBoundaryWithoutBlowup T) j := by simp_all
          exact goingUpInvariant_of_le hres hno T j hj (lowerIdealWithoutBlowup T)
            (lowerBoundaryWithoutBlowup T) s hpr hbalLower hV.one_le_mult hVlow hlift hE0_ hjE hget
            htrunc s.length le_rfl
        exact orderAtLeastLocus_inter_support_ker_eq_empty hres hno T j hj s hpr
          (fun i hi => hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform i hi) hempty
      coSupport_inter_ker_eq_empty_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr hempty
        have := inst
        have := hV.charZero
        have := hV.smooth
        have := hV.locallyOfFiniteType
        obtain ⟨U0_, hU, hsupp, hbalPre, hinv⟩ :=
          exists_isClosed_opens_goingUpInvariantOnOpen hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
            s hpr
            (smooth_subschemeio_containedComponentsIdeal_comp T hV j hj)
            (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
            (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
            (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
            (isOpen_preimage_support_containedComponentsIdeal T j hj
              (preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
        exact orderAtLeastLocus_controlledTransform_inter_ker_support_eq_empty hres hno T j hj hb s hpr
          (fun i hi => (hinv s.length le_rfl).exists_pow_mul_eq_comap_controlledTransform i hi)
          (controlledTransform_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr) hempty
      isPullbackSeq_ambientTower := by
        intro X Y S S' σ σ' ph_ ps_ _ _ _ _ _ hsq d d' hc hc' hpb
        exact isPullbackBlowupSequence_ambientBlowupSequence_of_flat hres hno σ σ' ph_ ps_ hsq d d' hc hc' hpb
      isStrictPullbackSeq_ambientTower := by
        intro X Y S S' σ σ' ph_ ps_ _ _ _ _ _ hsq d d' hc hc' hpb
        exact isStrictPullbackBlowupSeq_ambientBlowupSequence_of_flat hres hno σ σ' ph_ ps_ hsq d d' hc hc' hpb
      comap_ctrlIdeal_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr i hi
        have := inst
        exact comap_controlledTransform_of_containedComponentsIdeal_eq_top hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hVlow
          s hpr i hi
      comap_ctrlIdeal_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr i hi
        have := inst
        exact comap_controlledTransform_prepend_ambientBlowupSeq hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
          s hpr
          (smooth_subschemeio_containedComponentsIdeal_comp T hV j hj)
          (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
          (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
          (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
          (isOpen_preimage_support_containedComponentsIdeal T j hj
            (preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
          i hi
      preIdeal_baseChange := by
        intro T hV L _ _ f hV' j hj hj'
        exact containedComponentsIdeal_baseChange T hV L f hV' j hj hj'
      preIdeal_pullbackAlong := by
        intro T hV Y q h _ hq hV' j hj hj'
        exact containedComponentsIdeal_pullbackAlong_of_smooth T hV Y q h hq hV' j hj hj'
      preIdeal_eq_top_of_imageIdeal := by
        intro T hV j hj J hm hlow hpush
        exact containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf T hV j hj J hm hlow hpush }
end





namespace MarkedIdealWithBoundary

section
variable (T : MarkedIdealWithBoundary) (Y : Sch)
section
variable (k' : Type) [Field k'] (q : Y ⟶ Sp k') (h : Y ⟶ scheme T)
def pullbackOverField : MarkedIdealWithBoundary where
  base := k'
  instField := inferInstance
  scheme := Y
  structMap := q
  ideal := T.ideal.comap h
  mult := mult T
  boundary := T.boundary.map fun D => D.comap h







theorem pullbackOverField_boundary_length :
    (T.pullbackOverField Y k' q h).boundary.length = T.boundary.length :=
  length_map _
end
section
variable {Y}
abbrev pbOF {k' : Type} [Field k'] (q : Y ⟶ Sp k') (h : Y ⟶ scheme T) := T.pullbackOverField Y k' q h
end

section
variable (q : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)

end
end

end MarkedIdealWithBoundary

section
variable (T : MarkedIdealWithBoundary) (Y : Sch)
section
variable (k' : Type) [Field k'] (q : Y ⟶ Sp k') (h : Y ⟶ scheme T)
def pullbackOverFieldIndex :
    Fin T.boundary.length → Fin (T.pbOF q h).boundary.length :=
  cast (MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q h).symm

theorem pullbackOverFieldIndex_val j :
    ((pullbackOverFieldIndex T Y k' q h j : Fin (T.pbOF q h).boundary.length) : ℕ)
      = (j : ℕ) := rfl
end

section
variable (q : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
def pullbackAlongIndex :
    Fin T.boundary.length → Fin (T.pbA q h).boundary.length :=
  cast ((congrArg length $ MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h).trans $ length_map _).symm

theorem pullbackAlongIndex_val j :
    ((pullbackAlongIndex T Y q h j : Fin (T.pbA q h).boundary.length) : ℕ)
      = (j : ℕ) := rfl
end
end

section
variable {X' X : Sch} (pi_ : X' ⟶ X) (Z : ISD X) (L : Bdy X)
abbrev transformedBoundary : List X'.IdealSheafData :=
  L.map (strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z]

theorem transformedBoundary_length :
    length (transformedBoundary pi_ Z L) = length L + 1 := by
  simp [transformedBoundary]

def strictTransformIndex (j : Fin L.length) :
    Fin (transformedBoundary pi_ Z L).length :=
  cast (transformedBoundary_length pi_ Z L).symm j.castSucc

theorem strictTransformIndex_val j :
    ((strictTransformIndex pi_ Z L j : Fin (transformedBoundary pi_ Z L).length) : ℕ) = (j : ℕ) := rfl

section
variable (J' : Finset (Fin (transformedBoundary pi_ Z L).length))
def preimageStrictTransformIndex : FinSet L.length :=
  Finset.univ.filter fun j => strictTransformIndex pi_ Z L j ∈ J'

theorem mem_preimageStrictTransformIndex_iff (j : Fin L.length) :
    j ∈ preimageStrictTransformIndex pi_ Z L J' ↔ strictTransformIndex pi_ Z L j ∈ J' := by
  simp [preimageStrictTransformIndex]
end

def exceptionalIndex : Fin (transformedBoundary pi_ Z L).length :=
  cast (transformedBoundary_length pi_ Z L).symm $ last L.length

theorem exceptionalIndex_val :
    ((exceptionalIndex pi_ Z L : Fin (transformedBoundary pi_ Z L).length) : ℕ) = length L := rfl
end

section
variable {Y : Sch}
def IsIrreducibleComponentOf (C S : Set ↥Y) : Prop :=
  IsIrreducible C ∧ C ⊆ S ∧ ∀ C' : Set ↥Y, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C

section
variable (L : Bdy Y) (J : FinSet L.length)
section
variable (Cc_) (hop : IsOpen (⇑(intersectionIdeal L J).si ⁻¹' ⋃₀ Cc_))
def componentUnionOpens :
    (intersectionIdeal L J).subscheme.Opens :=
  ⟨⇑(intersectionIdeal L J).si ⁻¹' ⋃₀ Cc_, hop⟩

def componentUnionIdeal :
    IdealSheafData Y :=
  ker $ ι (componentUnionOpens L J Cc_ hop) ≫ subschemeι (intersectionIdeal L J)

theorem componentUnionIdeal_eq_ker :
    componentUnionIdeal L J Cc_ hop =
      ker (ι (componentUnionOpens L J Cc_ hop) ≫ subschemeι (intersectionIdeal L J)) := rfl
end

theorem mem_intersectionComponents_iff (C : Set ↥Y) :
    C ∈ intersectionComponents L J ↔ IsIrreducibleComponentOf C ↑(intersectionIdeal L J).support :=
  m22
end
end

structure MonomialGeometryHypotheses : Prop where
  card_lt_dim : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ J : FinSet T.boundary.length,
      (intersectionComponents T.boundary J).Nonempty → J.card < krullDimSucc T.scheme
  flat_comap_center : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (Y : Sch) (k' : Type) [Field k'] (q : Y ⟶ Sp k')
      (g : Y ⟶ scheme T) [Flat g],
      (T.pbOF q g).IsAdmissible →
      ∀ (J : FinSet T.boundary.length) (Cc_ : Set $ CSet T.scheme),
        Cc_ ⊆ intersectionComponents T.boundary J →
        ∀ hop : IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_,
          ∃ hop' : IsOpen $ ⇑(intersectionIdeal (T.pbOF q g).boundary
                  (J.image $ pullbackOverFieldIndex T Y k' q g)).subschemeι ⁻¹'
                ⋃₀ {C' : Set ↥Y | C' ∈ intersectionComponents (T.pbOF q g).boundary
                    (J.image $ pullbackOverFieldIndex T Y k' q g) ∧
                  ∃ C ∈ Cc_, MapsTo (⇑g) C' C},
            (componentUnionIdeal T.boundary J Cc_ hop).comap g =
              componentUnionIdeal (T.pbOF q g).boundary
                (J.image $ pullbackOverFieldIndex T Y k' q g)
                {C' : Set ↥Y | C' ∈ intersectionComponents (T.pbOF q g).boundary
                    (J.image $ pullbackOverFieldIndex T Y k' q g) ∧
                  ∃ C ∈ Cc_, MapsTo (⇑g) C' C} hop'
  center_smooth : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (J : FinSet T.boundary.length) (Cc_ : Set $ CSet T.scheme),
      Cc_ ⊆ intersectionComponents T.boundary J →
      ∀ hop : IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_,
        Smooth $ subschemeι (componentUnionIdeal T.boundary J Cc_ hop) ≫ structMap T
  center_snc : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (J : FinSet T.boundary.length) (Cc_ : Set $ CSet T.scheme),
      Cc_ ⊆ intersectionComponents T.boundary J →
      ∀ hop : IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_,
        HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J Cc_ hop) T.boundary
  center_support : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (J : FinSet T.boundary.length) (Cc_ : Set $ CSet T.scheme),
      Cc_ ⊆ intersectionComponents T.boundary J →
      ∀ hop : IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_,
        (↑(componentUnionIdeal T.boundary J Cc_ hop).support : CSet T.scheme) = ⋃₀ Cc_
  blowup_total_transform : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ Z : tISD T,
      Smooth (subschemeι Z ≫ structMap T) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
      ∀ (X' : Sch) (pi_ : X' ⟶ scheme T), IsBlowupAlongIdealSheaf pi_ Z →
      ∀ D ∈ boundary T, ∀ x' : ↥X',
        ∃ (U' : Opens X') (ep_ : ℕ), x' ∈ U' ∧ (ep_ = 0 ∨ ep_ = 1) ∧
          (ep_ = 1 ↔ ∃ V : T.scheme.Opens, pi_ x' ∈ V ∧
            ((↑Z.support : CSet T.scheme) ∩ (V : CSet T.scheme)) ⊆ (↑D.support : CSet T.scheme)) ∧
          (D.comap pi_).comap U'.i =
            (strictTransform pi_ Z D).comap U'.i * ((exceptionalIdeal pi_ Z).comap U'.i) ^ ep_
  flat_components_down : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (Y : Sch) (k' : Type) [Field k'] (q : Y ⟶ Sp k')
      (g : Y ⟶ scheme T) [Flat g],
      (T.pbOF q g).IsAdmissible →
      ∀ (J : FinSet T.boundary.length) (C' : Set ↥Y),
        C' ∈ intersectionComponents (T.pbOF q g).boundary
            (J.image $ pullbackOverFieldIndex T Y k' q g) →
        ∃ C ∈ intersectionComponents T.boundary J,
          MapsTo (⇑g) C' C ∧
            ∀ (xi' : ↥Y) (xi_ : ↥T.scheme), IsGenericPoint xi' C' → IsGenericPoint xi_ C → g xi' = xi_
  flat_components_up : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (Y : Sch) (k' : Type) [Field k'] (q : Y ⟶ Sp k')
      (g : Y ⟶ scheme T) [Flat g],
      (T.pbOF q g).IsAdmissible →
      ∀ (J : FinSet T.boundary.length) (C : CSet T.scheme),
        C ∈ intersectionComponents T.boundary J →
        ∀ y : ↥Y, g y ∈ C →
          ∃ C' ∈ intersectionComponents (T.pbOF q g).boundary
              (J.image $ pullbackOverFieldIndex T Y k' q g),
            y ∈ C' ∧
              ∀ (xi' : ↥Y) (xi_ : ↥T.scheme), IsGenericPoint xi' C' → IsGenericPoint xi_ C → g xi' = xi_
  components_disjoint : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ J : FinSet T.boundary.length,
      ∀ C ∈ intersectionComponents T.boundary J, ∀ C' ∈ intersectionComponents T.boundary J, C ≠ C' → Disjoint C C'
  components_finite : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ J : FinSet T.boundary.length, (intersectionComponents T.boundary J).Finite
  components_subset_divisor_iff : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (J : FinSet T.boundary.length) (C : CSet T.scheme),
      C ∈ intersectionComponents T.boundary J →
      ∀ i : Fin T.boundary.length,
        (C ⊆ (↑(T.boundary.get i).support : CSet T.scheme) ↔ i ∈ J)
  transformed_components : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (J0_ : FinSet T.boundary.length) (Cc_ : Set $ CSet T.scheme),
      Cc_ ⊆ intersectionComponents T.boundary J0_ →
      ∀ hop : IsOpen $ ⇑(intersectionIdeal T.boundary J0_).si ⁻¹' ⋃₀ Cc_,
      ∀ (X' : Sch) (pi_ : X' ⟶ scheme T),
        IsBlowupAlongIdealSheaf pi_ (componentUnionIdeal T.boundary J0_ Cc_ hop) →
        ∀ (J : FinSet T.boundary.length) (C' : Set ↥X'),
          C' ∈ intersectionComponents
              (transformedBoundary pi_ (componentUnionIdeal T.boundary J0_ Cc_ hop) T.boundary)
              (J.image $ strictTransformIndex pi_ (componentUnionIdeal T.boundary J0_ Cc_ hop) T.boundary) →
          ∀ xi' : ↥X', IsGenericPoint xi' C' →
            xi' ∉ support (exceptionalIdeal pi_ $ componentUnionIdeal T.boundary J0_ Cc_ hop) ∧
              ∃ C ∈ intersectionComponents T.boundary J, C ∉ Cc_ ∧
                C' = closure ((⇑pi_ ⁻¹' C) \
                    (↑(exceptionalIdeal pi_ $ componentUnionIdeal T.boundary J0_ Cc_ hop).support :
                      Set ↥X')) ∧
                  ∀ xi_ : ↥T.scheme, IsGenericPoint xi_ C → pi_ xi' = xi_
  level_schemeDim_le : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc
  level_valid : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length → (T.transformAt s i).IsAdmissible
  orderAt_bounded : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ I : tISD T, NonzeroOnComponents I →
      ∃ B : ℕ, ∀ x : ↥T.scheme, orderAt I x ≤ (B : ENat)
  orderAt_comap_off_exceptional : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (X' : Sch) (pi_ : X' ⟶ scheme T) (Z : tISD T), IsBlowupAlongIdealSheaf pi_ Z →
      ∀ x' : ↥X', x' ∉ support (exceptionalIdeal pi_ Z) →
        ∀ A : tISD T, orderAt (A.comap pi_) x' = orderAt A (pi_ x')
  orderAt_boundary_eq_one : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ D ∈ boundary T, ∀ x : ↥T.scheme, x ∈ support D → orderAt D x = 1
  sUnion_isOpen : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (J : FinSet T.boundary.length) (Cc_ : Set $ CSet T.scheme),
      Cc_ ⊆ intersectionComponents T.boundary J →
      IsOpen (⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_)
  withBoundary_valid : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ E' : List T.scheme.IdealSheafData, SameNontrivialBoundary T.boundary E' →
      (withBoundary T E').IsAdmissible

end FunctorialResolution.EmbeddedResolution

end
section
universe v


section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialChart

theorem comap_biSup_finset {X Y : Sch} {ι : Type v} (f : X ⟶ Y)
    (I : ι → ISD Y) (S : Finset ι) :
    (⨆ j ∈ S, I j).comap f = ⨆ j ∈ S, (I j).comap f := by
  classical
  refine induction_on S ?_ ?_
  simp
  intro a s ha ih
  rw [Finset.iSup_insert, Finset.iSup_insert, Scheme.IdealSheafData.comap_sup, ih]

theorem restrictIdeal_biSup_finset {X : Sch} {ι : Type v} (U : Opn X)
    (I : ι → ISD X) (S : Finset ι) :
    restrictIdeal (⨆ j ∈ S, I j) U = ⨆ j ∈ S, restrictIdeal (I j) U :=
  comap_biSup_finset U.i I S

private theorem ofIdealTop_sup {X : Sch} [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    ofIdealTop (I ⊔ J) =
      ofIdealTop I ⊔ ofIdealTop J := by
  ext U : 2
  simp [ofIdealTop, Ideal.map_sup]

section
variable (k : Type) [Field k] (m : ℕ)
theorem coordSubspaceIdeal_insert (j : Fin m)
    (S : FinSet m) :
    coordSubspaceIdeal k m (insert j S) =
      coordSubspaceIdeal k m {j} ⊔ coordSubspaceIdeal k m S := by
  classical
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord,
    coe_insert, image_insert_eq, span_insert, coe_singleton,
    image_singleton, ofIdealTop_sup]

theorem coordSubspaceIdeal_eq_biSup_singleton (S : FinSet m) :
    coordSubspaceIdeal k m S = ⨆ j ∈ S, coordSubspaceIdeal k m {j} := by
  classical
  refine induction_on S ?_ ?_
  simp [coordSubspaceIdeal_empty]
  intro a s _ ih
  rw [coordSubspaceIdeal_insert, ih, Finset.iSup_insert]
end

theorem coordIdeal_eq_biSup_singleton {X : Sch} {k : Type} [Field k]
    (p : X ⟶ Sp k) (U : Opn X) (m : ℕ) (c : EtaleChart p U m)
    (S : FinSet m) :
    c.coordIdeal S = ⨆ j ∈ S, c.coordIdeal {j} := by
  rw [p33, coordSubspaceIdeal_eq_biSup_singleton, comap_biSup_finset]
  exact iSup_congr fun j => iSup_congr fun _ => sy_ $ c.coordIdeal_eq_comap_coordSubspaceIdeal {j}

theorem orderAt_boundary_eq_one : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ D ∈ boundary T, ∀ x : ↥T.scheme, x ∈ support D → orderAt D x = 1 := by
  intro T hT D hD x hx
  have := hT.smooth
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  obtain ⟨i, hi, hDi⟩ := mem_iff_getElem.1 hD
  cases hai : a i with
  | none =>
      refine absurd hx $ notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ x hxU
      rw [← hDi]
      exact hnone i hi hai
  | some t =>
      obtain ⟨V, m', hxV, hVU', hV, -⟩ := exists_etaleChart_le T.structMap x U hxU
      have hDU : restrictIdeal D U = c.coordIdeal {t} := by
        rw [← hDi]
        exact hsome i hi t hai
      exact orderAt_eq_one_of_restrictIdeal_eq_coordIdeal_singleton T.structMap hV
        (c.restrict hVU') t D (restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c D {t} hDU) x hxV hx

theorem smooth_intersectionIdeal_subscheme : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ J : FinSet T.boundary.length,
      Smooth $ subschemeι (intersectionIdeal T.boundary J) ≫ structMap T := by
  classical
  intro T hT J
  refine smooth_subschemeio_comp_of_locally_eq_coordIdeal (p := tMp T) (intersectionIdeal T.boundary J) ?_
  intro x hx
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  have hle : ∀ j ∈ J, T.boundary.get j ≤ intersectionIdeal T.boundary J := by
    intro j hj
    rw [intersectionIdeal_eq_iSup]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => T.boundary.get j) j hj
  have hxj : ∀ j ∈ J, x ∈ spI (T.boundary.get j) := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro hcon
    have h2 := stalkIdeal_mono (hle j hj) x
    rw [hcon] at h2
    exact (mem_support_iff_stalkIdeal_ne_top _ _).1 hx $ top_le_iff.1 h2
  have hsomej : ∀ j ∈ J, ∃ t, a j = some t := by
    intro j hj
    cases haj : a j with
    | none =>
        refine absurd (hxj j hj)
          (notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U ?_ x hxU)
        rw [get_eq_getElem]
        exact hnone j j.isLt haj
    | some t => exact ⟨t, rfl⟩
  refine ⟨U, hxU, m, c, J.biUnion fun j => (a j).toFinset, ?_⟩
  have h1 : restrictIdeal (intersectionIdeal T.boundary J) U
      = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) U := by
    rw [intersectionIdeal_eq_iSup]
    exact restrictIdeal_biSup_finset U T.boundary.get J
  rw [h1, coordIdeal_eq_biSup_singleton T.structMap U m c _]
  refine le_antisymm ?_ ?_
  refine iSup_le fun j => iSup_le fun hj => ?_
  obtain ⟨t, ht⟩ := hsomej j hj
  have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by simp_all
  have htS : t ∈ J.biUnion fun j => (a j).toFinset :=
    mem_biUnion.2 ⟨j, hj, by simp [ht]⟩
  rw [hres]
  exact le_iSup₂
    (f := fun t (_ : t ∈ J.biUnion fun j => (a j).toFinset) =>
      c.coordIdeal ({t} : FinSet m)) t htS
  refine iSup_le fun t => iSup_le fun htS => ?_
  obtain ⟨j, hj, htj⟩ := mem_biUnion.1 htS
  have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by simp_all
  rw [← hres]
  exact le_iSup₂ (f := fun j (_ : j ∈ J) => restrictIdeal (T.boundary.get j) U) j hj

end MonomialChart

end FunctorialResolution.EmbeddedResolution

end
end
section


namespace FunctorialResolution.EmbeddedResolution

theorem mem_basicOpen_iff_notMem_asIdeal_primeIdealOf {X : Sch} {V} (hV : IsAffineOpen V)
    {x} (hx : x ∈ V) f :
    x ∈ basicOpen X f ↔ f ∉ asIdeal (hV.primeIdealOf ⟨x, hx⟩) := by
  let _a0 := hV.primeIdealOf ⟨x, hx⟩
  have h2 : _a0 ∈ hV.fromSpec ⁻¹ᵁ bOpn X f ↔ x ∈ bOpn X f := by
    show hV.fromSpec.base _a0 ∈ bOpn X f ↔ _
    rw [hV.fromSpec_primeIdealOf ⟨x, hx⟩]
  rw [← h2, hV.fromSpec_preimage_basicOpen]
  exact m209 f _

theorem mem_support_iff_ideal_le_asIdeal_primeIdealOf {X : Sch} (I : ISD X) {V : Opn X}
    (hV : IsAffineOpen V) {x : ↥X} (hx : x ∈ V) :
    x ∈ support I ↔ I.ideal ⟨V, hV⟩ ≤ asIdeal (hV.primeIdealOf ⟨x, hx⟩) := by
  rw [mem_support_iff_of_mem (U := ⟨V, hV⟩) hx, Scheme.mem_zeroLocus_iff]
  constructor
  intro h f hf
  by_contra hfP
  exact h f hf $ mpr_ (mem_basicOpen_iff_notMem_asIdeal_primeIdealOf hV hx f) hfP
  intro h f hf hb
  exact mp_ (mem_basicOpen_iff_notMem_asIdeal_primeIdealOf hV hx f) hb $ h $ SetLike.mem_coe.mp hf

section
variable {R : Type} [CommRing R] (I : Ideal R) (g : R) (hnzd : ∀ x : R, g * x ∈ I → x ∈ I)
include hnzd
theorem mem_of_mul_pow_mem :
    ∀ n u, u * g ^ n ∈ I → u ∈ I := by
  intro n
  induction n with
  | zero =>
      intro u h
      simpa using h
  | succ n ih =>
      intro u h
      refine ih u $ hnzd _ ?_
      have e : g * (u * g ^ n) = u * g ^ (n + 1) := by ring
      rwa [e]

theorem exists_isPrime_between_notMem_of_mul_mem
    (P : Ideal R) (hP : P.IsPrime) (hIP : I ≤ P) :
    ∃ Q : Ideal R, Q.IsPrime ∧ I ≤ Q ∧ Q ≤ P ∧ g ∉ Q := by
  classical
  have h1P := fun h => hP.ne_top $ mpr_ (eq_top_iff_one P) h
  let M : Submonoid R :=
    { carrier := {x : R | ∃ u n, u ∉ P ∧ x = u * g ^ n}
      mul_mem' := by
        rintro x y ⟨u, n, hu, rfl⟩ ⟨v, l, hv, rfl⟩
        refine ⟨u * v, n + l, ?_, by ring⟩
        intro h
        rcases hP.mem_or_mem h with h' | h'
        exact hu h'
        exact hv h'
      one_mem' := ⟨1, 0, h1P, by ring⟩ }
  have hdisj : Disjoint (I : Set R) (M : Set R) := by
    rw [disjoint_left]
    rintro x hxI ⟨u, n, hu, rfl⟩
    exact hu $ hIP $ mem_of_mul_pow_mem I g hnzd n u hxI
  obtain ⟨Q, hQ, hIQ, hQdisj⟩ := exists_le_prime_disjoint I M hdisj
  refine ⟨Q, hQ, hIQ, ?_, ?_⟩
  intro x hx
  by_contra hxP
  exact Set.disjoint_left.mp hQdisj hx ⟨x, 0, hxP, by ring⟩
  intro hg
  exact Set.disjoint_left.mp hQdisj hg ⟨1, 1, h1P, by ring⟩
end

theorem mem_map_of_mul_mem_of_etale_of_isSMulRegular {P A : Type} [CommRing P] [CommRing A]
    {f : P →+* A} (hf : f.Etale) (I : Ideal P) (w : P)
    (hw : ∀ a b : P ⧸ I,
      (mk I) w * a = (mk I) w * b → a = b)
    (x : A) (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  let _c0 := (mk I) w
  let _c1 := m6 f I
  let _a1 := quotientMap _c1 f le_comap_map
  let _ :=
    _a1.toAlgebra
  have : m121 (P ⧸ I) $ A ⧸ m6 f I := etale_quotientMap hf I
  have : Module.Flat (P ⧸ I) $ A ⧸ m6 f I := inferInstance
  let _a0 := (mk _c1) x
  have hy : _a1
        _c0 * _a0 = 0 := by
    rw [quotientMap_mk, ← map_mul]
    exact mpr_ eq_zero_iff_mem hx
  let _a2 := (0 : A ⧸ m6 f I)
  have hsm : _c0 • _a0
      = _a2 := by
    show _a1
        _c0 * _a0 = 0
    exact hy
  have hreg0 : IsSMulRegular (P ⧸ I) _c0 := fun a b h => hw a b h
  have hzero : _a0 = 0 := by
    refine hreg0.of_flat ?_
    show _c0 • _a0
      = _c0 • _a2
    rwa [smul_zero]
  exact mp_ eq_zero_iff_mem hzero

theorem mem_mvPolynomialCoordIdeal_of_X_mul_mem (k : Type) [Field k] (m : ℕ)
    (S : FinSet m) {s : Fin m} (hs : s ∉ S) (r : MvU m k)
    (h : MvPolynomial.X (up s) * r ∈ mvPolynomialCoordIdeal k m S) :
    r ∈ mvPolynomialCoordIdeal k m S := by
  classical
  obtain ⟨ps_, hpsC, hpsX⟩ :
      ∃ ps_ : MvU m k →+* MvU m k,
        (∀ a : k, ps_ (m8 a) = m8 a) ∧
        (∀ j : Fin m, ps_ (m7 $ up j)
          = if j ∈ S then 0 else m7 $ up j) := by
    refine ⟨MvPolynomial.eval₂Hom m8
      (fun i : UFin m =>
        if i.down ∈ S then 0
        else m7 i), ?_, ?_⟩
    intro a
    simp
    intro j
    simp
  have hker : mvPolynomialCoordIdeal k m S ≤ m41 ps_ := by
    rw [mvPolynomialCoordIdeal_eq_span, span_le]
    rintro _ ⟨j, hj, rfl⟩
    refine SetLike.mem_coe.mpr $ RingHom.mem_ker.mpr ?_
    rw [hpsX j]
    exact if_pos $ Finset.mem_coe.mp hj
  have key : (mk $ mvPolynomialCoordIdeal k m S).comp ps_
      = mk (mvPolynomialCoordIdeal k m S) := by
    apply MvPolynomial.ringHom_ext
    simp_all
    intro i
    obtain ⟨j⟩ := i
    rw [m82, hpsX j]
    by_cases hi : j ∈ S
    rw [if_pos hi, map_zero]
    exact sy_ $ mpr_ eq_zero_iff_mem $ X_mem_mvPolynomialCoordIdeal k m S hi
    rw [if_neg hi]
  have h0 :=
    RingHom.mem_ker.mp $ hker h
  rw [map_mul, hpsX s, if_neg hs] at h0
  have hpsr : ps_ r = 0 := by simp_all
  have hfin := m156 key r
  rw [m82, hpsr, map_zero] at hfin
  exact mp_ eq_zero_iff_mem hfin.symm

theorem false_of_restrictIdeal_eq_coordIdeal {X : Sch} {k : Type} [Field k]
    {p : X ⟶ Sp k} {V : Opn X} (hV : IsAffineOpen V) {m : ℕ}
    (c : EtaleChart p V m) (Z D : ISD X) (S : FinSet m) (s : Fin m)
    (hs : s ∉ S) (hZ : restrictIdeal Z V = c.coordIdeal S)
    (hD : restrictIdeal D V = c.coordIdeal {s})
    (xi_ : ↥X) (hxiV_ : xi_ ∈ V) (hxiZ_ : xi_ ∈ support Z) (_hξD : xi_ ∈ support D)
    (hmin : ∀ et_ : ↥X, et_ ∈ support Z → xi_ ∈ closure ({et_} : Set ↥X) → et_ ∈ support D) : False := by
  classical
  have hDspan : D.ideal ⟨V, hV⟩ = m17 {c.coord s} := by
    rw [← c.map_mvPolynomialCoordIdeal_eq_ideal hV D {s} hD, mvPolynomialCoordIdeal_eq_span, coe_singleton, image_singleton, m218,
      image_singleton, c.coordRingHom_X]
  have hnzd : ∀ x, c.coord s * x ∈ Z.ideal ⟨V, hV⟩ → x ∈ Z.ideal ⟨V, hV⟩ := by
    intro x hx
    rw [← c.map_mvPolynomialCoordIdeal_eq_ideal hV Z S hZ] at hx ⊢
    refine mem_map_of_mul_mem_of_etale_of_isSMulRegular (c.coordRingHom_etale hV) (mvPolynomialCoordIdeal k m S)
      (m7 $ up s) ?_ x ?_
    intro A B hAB
    obtain ⟨A', rfl⟩ := m108 A
    obtain ⟨B', rfl⟩ := m108 B
    rw [← map_mul, ← map_mul, m202, ← mul_sub] at hAB
    exact Ideal.Quotient.eq.mpr $ mem_mvPolynomialCoordIdeal_of_X_mul_mem k m S hs (A' - B') hAB
    rwa [c.coordRingHom_X]
  let _a0 := hV.primeIdealOf ⟨xi_, hxiV_⟩
  obtain ⟨Q, hQp, hIQ, hQP, hgQ⟩ :=
    exists_isPrime_between_notMem_of_mul_mem (Z.ideal ⟨V, hV⟩) (c.coord s) hnzd
      _a0.asIdeal _a0.isPrime $ mp (mem_support_iff_ideal_le_asIdeal_primeIdealOf Z hV hxiV_) hxiZ_
  obtain ⟨q, hqQ⟩ : ∃ q : PrimeSpectrum V.sec, asIdeal q = Q := ⟨⟨Q, hQp⟩, rfl⟩
  have hrange : hV.fromSpec.base q ∈ V := by
    have h0 : hV.fromSpec.base q ∈ range hV.fromSpec.base := ⟨q, rfl⟩
    rwa [hV.range_fromSpec] at h0
  have hQeq : hV.primeIdealOf ⟨hV.fromSpec.base q, hrange⟩ = q := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hV.fromSpec_primeIdealOf]
  have hetZ : hV.fromSpec.base q ∈ spI Z := by
    rwa [mem_support_iff_ideal_le_asIdeal_primeIdealOf Z hV hrange, hQeq, hqQ]
  have hspec : xi_ ∈ closure ({hV.fromSpec.base q} : Set X) := by
    have hle : asIdeal q ≤ asIdeal _a0 := by
      rwa [hqQ]
    have h2 := (mp_ (PrimeSpectrum.le_iff_specializes _ _) hle).map hV.fromSpec.base.hom.continuous
    rw [hV.fromSpec_primeIdealOf] at h2
    exact mp_ specializes_iff_mem_closure h2
  have hetD := hmin _ hetZ hspec
  rw [mem_support_iff_ideal_le_asIdeal_primeIdealOf D hV hrange, hQeq, hDspan, hqQ] at hetD
  exact hgQ $ hetD $ mem_span_singleton_self _

theorem intersectionComponents_subset_support_iff : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (J : FinSet T.boundary.length),
      ∀ C ∈ intersectionComponents T.boundary J,
        ∀ (i : Fin T.boundary.length),
          C ⊆ (support (T.boundary.get i) : CSet T.scheme) ↔ i ∈ J := by
  intro T hT J C hC i
  constructor
  intro hsub
  by_contra hi
  classical
  obtain ⟨hirr, hCsub, hmax⟩ := hC
  have hirr' := hirr
  have hclosed :=
    isClosed_of_maximal_irreducible_subset_support (intersectionIdeal T.boundary J) hirr' hCsub hmax
  have hgen : closure ({hirr'.genericPoint} : CSet T.scheme) = C := by
    rw [hirr'.genericPoint_closure_eq, hclosed.closure_eq]
  have hxiC := IsGenericPoint.mem hgen
  have hxiZ := hCsub hxiC
  have hxiD := hsub hxiC
  obtain ⟨U, hxiU, m, c, a, hinj, hnone, hsome⟩ := hT.snc.2 hirr'.genericPoint
  obtain ⟨V, hVaff, hxiV, hVU⟩ :=
    mp isBasis_iff_nbhd T.scheme.isBasis_affineOpens hxiU
  let _a2 := c.restrict hVU
  have key : ∀ j, hirr'.genericPoint ∈ spI (T.boundary.get j) →
      ∃ t, a j = some t ∧
        restrictIdeal (T.boundary.get j) V = _a2.coordIdeal {t} := by
    intro j hj
    cases hA : a j with
    | none =>
        exfalso
        have h1 := hnone j j.isLt hA
        refine notMem_support_of_mem_opens_of_restrictIdeal_eq_top (T.boundary.get j) U ?_
          hirr'.genericPoint hxiU hj
        rwa [get_eq_getElem]
    | some t =>
        refine ⟨t, rfl, ?_⟩
        have h1 :=
          hsome j j.isLt t hA
        refine restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (T.boundary.get j) {t} ?_
        rwa [get_eq_getElem]
  have hmemJ : ∀ j ∈ J, hirr'.genericPoint ∈ spI (T.boundary.get j) := by
    intro j hj
    refine support_antitone ?_ hxiZ
    rw [intersectionIdeal_eq_iSup]
    exact le_biSup T.boundary.get hj
  obtain ⟨si, hsi, hDi⟩ := key i hxiD
  obtain ⟨S, hmemS⟩ :
      ∃ S, ∀ t, t ∈ S ↔ ∃ j ∈ J, a j = some t :=
    ⟨Finset.univ.filter fun t => ∃ j ∈ J, a j = some t, by
      intro t
      simp⟩
  have hsiS : si ∉ S := by
    intro hmem
    obtain ⟨j, hj, haj⟩ := mp_ (hmemS si) hmem
    exact hi (by rw [eq_of_val_eq $ hinj i i.isLt j j.isLt si hsi haj]; exact hj)
  have hZV : restrictIdeal (intersectionIdeal T.boundary J) V = _a2.coordIdeal S := by
    have hbi : restrictIdeal (intersectionIdeal T.boundary J) V
        = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) V := by
      rw [intersectionIdeal_eq_iSup]
      exact MonomialChart.restrictIdeal_biSup_finset V T.boundary.get J
    have hcb :=
      MonomialChart.coordIdeal_eq_biSup_singleton T.structMap V m (c.restrict hVU) S
    rw [hbi, hcb]
    refine le_antisymm (iSup₂_le fun j hj => ?_) $ iSup₂_le fun t ht => ?_
    obtain ⟨t, hat, hres⟩ := key j $ hmemJ j hj
    rw [hres]
    exact le_biSup (fun t => _a2.coordIdeal {t})
      (mpr_ (hmemS t) ⟨j, hj, hat⟩)
    obtain ⟨j, hj, hat⟩ := mp_ (hmemS t) ht
    obtain ⟨t', hat', hres⟩ := key j $ hmemJ j hj
    rw [m105 $ st_ hat hat', ← hres]
    exact le_biSup (fun j => restrictIdeal (T.boundary.get j) V) hj
  refine false_of_restrictIdeal_eq_coordIdeal hVaff (c.restrict hVU) (intersectionIdeal T.boundary J) (T.boundary.get i)
    S si hsiS hZV hDi hirr'.genericPoint hxiV hxiZ hxiD ?_
  intro et_ hetZ hetxi_
  have hs1 : C ⊆ (closure ({et_} : CSet T.scheme)) := by
    rw [← hgen]
    exact closure_minimal (mpr_ singleton_subset_iff hetxi_) isClosed_closure
  have hs2 :=
    closure_minimal (mpr_ singleton_subset_iff hetZ)
      (intersectionIdeal T.boundary J).support.2
  refine hsub ?_
  rw [← hmax _ isIrreducible_singleton.closure hs1 hs2]
  exact subset_closure $ mem_singleton et_
  intro hi x hx
  refine support_antitone ?_ $ hC.2.1 hx
  rw [intersectionIdeal_eq_iSup]
  exact le_biSup T.boundary.get hi

end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCodimension

theorem lt_krullDimSucc_of_le_ringKrullDim_stalk (X : Sch) (x : ↥X) (n : ℕ)
    (hn : (n : WithBot ENat) ≤ ringKrullDim (X.presheaf.stalk x))
    (hfin : topologicalKrullDim ↥X ≠ ⊤) : n < krullDimSucc X := by
  have hle :=
    le_trans hn $ ringKrullDim_stalk_le_topologicalKrullDim X x
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  by_cases hb : topologicalKrullDim X = ⊥
  simp_all
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hb
  rw [← he] at hle hfin ⊢
  have he' : e ≠ ⊤ := by
    intro hcon
    apply hfin
    rw [hcon]
    simp
  lift e to ℕ using he' with m
  rw [withBotSuccToNat_coe]
  have hmm : (m : ENat).toNat = m := by simp
  rw [hmm]
  have hnm : n ≤ m := by exact_mod_cast hle
  omega

theorem card_lt_krullDimSucc_of_mem_intersectionComponents : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (J : FinSet T.boundary.length) (C : CSet T.scheme),
      C ∈ intersectionComponents T.boundary J → J.card < krullDimSucc T.scheme := by
  classical
  intro T hT J C hC
  obtain ⟨hirr, hsub, -⟩ := mp (mem_intersectionComponents_iff T.boundary J C) hC
  obtain ⟨x, hxC⟩ := hirr.nonempty
  have hxsupp := hsub hxC
  have hxj : ∀ j ∈ J, x ∈ spI (T.boundary.get j) := by simp_all
  obtain ⟨-, hsnc⟩ := mp_ (inStrictNormalCrossingPosition_iff T.structMap T.boundary) hT.snc
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := (hsnc x).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxU
  have hV := hVB
  have hex : ∀ j : Fin $ bLen T, j ∈ J → ∃ t, a j = some t := by
    intro j hj
    refine Option.ne_none_iff_exists'.mp ?_
    intro hj'
    have hx' := hxj j hj
    rw [get_eq_getElem] at hx'
    exact notMem_support_of_comap_ι_eq_top _ (hnone j j.isLt hj') hxU hx'
  choose F hFspec using hex
  have hGinj : m120
      (fun p : {j : Fin (bLen T) // j ∈ J} => F p.1 p.2) := by
    intro p q h
    have h1 : a q.1 = some (F p.1 p.2) := by simp_all
    exact m26 $ val_injective $ hinj p.1 p.1.isLt q.1 q.1.isLt (F p.1 p.2) (hFspec p.1 p.2) h1
  have hmem : ∀ t ∈ J.attach.image
      (fun p : {j : Fin (bLen T) // j ∈ J} => F p.1 p.2),
      (c.restrict hVU).coord t ∈ asIdeal (hV.primeIdealOf ⟨x, hxV⟩) := by
    intro t ht
    obtain ⟨p, -, hpt⟩ := Finset.mem_image.mp ht
    have hat : a p.1 = some t := by simp_all
    have hx' := hxj p.1 p.2
    rw [get_eq_getElem] at hx'
    exact coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton hV
      (c.restrict hVU) t _ (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ {t} $ hsome p.1 p.1.isLt t hat) x hxV hx'
  have hle2 := card_le_ringKrullDim_stalk hV (c.restrict hVU) x hxV
    (J.attach.image fun p : {j : Fin (bLen T) // j ∈ J} => F p.1 p.2) hmem
  have hlt := lt_krullDimSucc_of_le_ringKrullDim_stalk T.scheme x _ hle2 $ ne_of_lt hT.topologicalKrullDim_lt_top
  rwa [card_image_of_injective _ hGinj, card_attach] at hlt

theorem card_lt_krullDimSucc_of_nonempty (T : MarkedIdealWithBoundary) (hT : T.IsAdmissible)
    (J : FinSet T.boundary.length) (hJ : (intersectionComponents T.boundary J).Nonempty) :
    J.card < krullDimSucc T.scheme := by
  obtain ⟨C, hC⟩ := hJ
  exact card_lt_krullDimSucc_of_mem_intersectionComponents T hT J C hC

end MonomialCodimension




theorem mem_irreducibleComponents_iff_isIrreducible_and_maximal {al_ : Type}
    [TopologicalSpace al_] (s : Set al_) :
    s ∈ irreducibleComponents al_ ↔
      IsIrreducible s ∧ ∀ t : Set al_, IsIrreducible t → s ⊆ t → t ⊆ s :=
  ⟨fun h => ⟨an1 h, fun _ ht hst => an2 h ht hst⟩, fun h => ⟨an1 h, fun t ht hst => an2 h t ht hst⟩⟩

theorem maximal_irreducible_subset_range_iff {al_ be_ : Type} [TopologicalSpace al_]
    [TopologicalSpace be_] {f : al_ → be_} (hf : Topology.IsClosedEmbedding f) {S : Set be_}
    (hr : range f = S) (C : Set be_) :
    (IsIrreducible C ∧ C ⊆ S ∧ ∀ C' : Set be_, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C)
      ↔ ∃ D ∈ irreducibleComponents al_, f '' D = C := by
  constructor
  rintro ⟨hirr, hsub, hmax⟩
  have hCr : C ⊆ range f := by rw [hr]
                               exact hsub
  have himg := image_preimage_eq_of_subset hCr
  refine ⟨pIm f C, mpr_ (mem_irreducibleComponents_iff_isIrreducible_and_maximal _) ⟨isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hirr hCr, ?_⟩, himg⟩
  intro t ht hDt x hx
  have hCt : C ⊆ imS f t := by
    rw [← himg]
    exact image_mono hDt
  have htS : imS f t ⊆ S := by
    rw [← hr]
    exact image_subset_range _ _
  rw [← hmax _ (ht.image f hf.continuous.continuousOn) hCt htS]
  exact ⟨x, hx, rfl⟩
  rintro ⟨D, hD, rfl⟩
  obtain ⟨hDirr, hDmax⟩ := mp_ (mem_irreducibleComponents_iff_isIrreducible_and_maximal _) hD
  refine ⟨hDirr.image f hf.continuous.continuousOn, ?_, ?_⟩
  rw [← hr]
  exact image_subset_range _ _
  intro C' hC' hsub' hS'
  have hC'r : C' ⊆ range f := by rw [hr]
                                 exact hS'
  have hDD := fun x hx => hsub' ⟨x, hx, rfl⟩
  apply m15
  rw [← image_preimage_eq_of_subset hC'r]
  exact image_mono $ hDmax _ (isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hC' hC'r) hDD
  exact hsub'

section
variable {Y : Sch} (L : Bdy Y) (J : FinSet L.length) (C : Set ↥Y)
theorem mem_intersectionComponents_iff_exists_irreducibleComponent :
    C ∈ intersectionComponents L J ↔
      ∃ D ∈ irreducibleComponents ↥(intersectionIdeal L J).subscheme,
        ⇑(intersectionIdeal L J).si '' D = C := by
  exact maximal_irreducible_subset_range_iff (isClosedEmbedding (intersectionIdeal L J).si) (q5 _) C

theorem isClosed_of_mem_intersectionComponents (hC : C ∈ intersectionComponents L J) : IsClosed C := by
  obtain ⟨D, hD, rfl⟩ := mp_ (mem_intersectionComponents_iff_exists_irreducibleComponent L J C) hC
  exact (isClosedEmbedding (intersectionIdeal L J).si).isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ hD)
end

section
variable (T : MarkedIdealWithBoundary)
theorem intersectionComponents_finite (hT : T.IsAdmissible)
    J : (intersectionComponents T.boundary J).Finite := by
  have := hT.isNoetherian
  let _a0 := intersectionIdeal T.boundary J
  have : NoetherianSpace _a0.subscheme := inferInstance
  have h : intersectionComponents T.boundary J =
      (fun D => subschemeι _a0 '' D) ''
        irreducibleComponents _a0.subscheme := by
    ext C
    rw [mem_intersectionComponents_iff_exists_irreducibleComponent]
    exact m22
  rw [h]
  exact Set.Finite.image _ $ finite_irreducibleComponents ..

section
variable (J) (hsm : Smooth (subschemeι (intersectionIdeal T.boundary J) ≫ structMap T))
include hsm
theorem irreducibleComponents_eq_of_inter_nonempty_of_smooth :
    ∀ C1_ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
      ∀ C2_ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
        (C1_ ∩ C2_).Nonempty → C1_ = C2_ := by
  rintro C1_ h1_ C2_ h2_ ⟨x, hx1_, hx2_⟩
  exact irreducibleComponents_eq_of_stalk_isDomain _
    (fun z => isDomain_stalk_of_smooth (siI (intersectionIdeal T.boundary J) ≫ tMp T) z)
    h1_ h2_ hx1_ hx2_

theorem intersectionComponents_disjoint_of_smooth
    C C' (hC : C ∈ intersectionComponents T.boundary J)
    (hC' : C' ∈ intersectionComponents T.boundary J) (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨D, hD, rfl⟩ := mp_ (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _) hC
  obtain ⟨D', hD', rfl⟩ := mp_ (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _) hC'
  rw [disjoint_left]
  rintro x ⟨d, hd, rfl⟩ ⟨d', hd', he⟩
  have hdd := ((isClosedEmbedding (intersectionIdeal T.boundary J).si).injective) he
  subst hdd
  exact hne $ by rw [irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm D hD D' hD' ⟨d', hd, hd'⟩]
end

section
variable (hT : T.IsAdmissible) (J : FinSet T.boundary.length)
include hT
theorem isOpen_preimage_sUnion_intersectionComponents
    (hsm : Smooth $ subschemeι (intersectionIdeal T.boundary J) ≫ structMap T)
    Cc_ (hCc_ : Cc_ ⊆ intersectionComponents T.boundary J) :
    IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_ := by
  let _c0 := intersectionIdeal T.boundary J
  have := hT.isNoetherian
  have : NoetherianSpace _c0.subscheme := inferInstance
  have key : subschemeι _c0 ⁻¹' ⋃₀ Cc_ =
      ⋃₀ {D : CSet _c0.subscheme |
        D ∈ irreducibleComponents _c0.subscheme ∧
          subschemeι _c0 '' D ∈ Cc_} := by
    apply m15
    rintro x hx
    obtain ⟨C, hCCc, hxC⟩ := hx
    obtain ⟨D, hD, rfl⟩ := mp_ (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _) $ hCc_ hCCc
    obtain ⟨d, hd, hde⟩ := hxC
    have hdx := ((isClosedEmbedding _c0.si).injective) hde
    subst hdx
    exact ⟨D, ⟨hD, hCCc⟩, hd⟩
    rintro x ⟨D, ⟨hD, hDCc⟩, hxD⟩
    exact ⟨subschemeι _c0 '' D, hDCc, ⟨x, hxD, rfl⟩⟩
  rw [key]
  exact isOpen_sUnion_of_subset_irreducibleComponents
    (irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm) fun D hD => an1 hD

theorem componentUnionIdeal_support_eq_sUnion (Cc_ : Set (CSet T.scheme))
    (hCc_ : Cc_ ⊆ intersectionComponents T.boundary J)
    (hop : IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_) :
    (↑(componentUnionIdeal T.boundary J Cc_ hop).support : CSet T.scheme) = ⋃₀ Cc_ := by
  let _a0 := intersectionIdeal T.boundary J
  let _c0 := opI (componentUnionOpens T.boundary J Cc_ hop) ≫ siI _a0
  have := hT.isNoetherian
  have : NoetherianSpace _a0.subscheme := inferInstance
  have hqc : QuasiCompact _c0 := inferInstance
  have hsub : ⋃₀ Cc_ ⊆ range _a0.si := by
    rintro x ⟨C, hC, hxC⟩
    obtain ⟨D, hD, rfl⟩ := mp_ (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _) $ hCc_ hC
    obtain ⟨d, hd, rfl⟩ := hxC
    exact ⟨d, rfl⟩
  have h0 : _c0
      = subschemeι _a0 ∘ (componentUnionOpens T.boundary J Cc_ hop).i := rfl
  have hr2 : range (componentUnionOpens T.boundary J Cc_ hop).i
      = subschemeι _a0 ⁻¹' ⋃₀ Cc_ :=
    q1 _
  have hrange : range _c0 = ⋃₀ Cc_ := by
    rw [h0, range_comp, hr2]
    exact image_preimage_eq_of_subset hsub
  have hclosed : IsClosed $ ⋃₀ Cc_ := by
    rw [sUnion_eq_biUnion]
    exact ((intersectionComponents_finite T hT J).subset hCc_).isClosed_biUnion
      (fun C hC => isClosed_of_mem_intersectionComponents T.boundary J C $ hCc_ hC)
  have h1 : (support (componentUnionIdeal T.boundary J Cc_ hop) : CSet T.scheme)
      = closure (range _c0) :=
    support_ker _
  rw [h1, hrange]
  exact hclosed.closure_eq
end
end





namespace MonomialCenterGeometry

section
variable (T : MarkedIdealWithBoundary)
section
variable (hT : T.IsAdmissible) (J) (Cc_) (hCc_ : Cc_ ⊆ intersectionComponents T.boundary J)
include hT hCc_
theorem isClosed_componentUnionOpens
    (hop : IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_) :
    IsClosed $ (componentUnionOpens T.boundary J Cc_ hop : Set ↥(intersectionIdeal T.boundary J).subscheme) := by
  have hK : IsClosed $ ⋃₀ Cc_ := by
    classical
    rw [sUnion_eq_biUnion]
    exact (subset (intersectionComponents_finite T hT J) hCc_).isClosed_biUnion
      (fun C hC => isClosed_of_mem_intersectionComponents T.boundary J C $ hCc_ hC)
  let _a0 := intersectionIdeal T.boundary J
  have h1 : IsOpen $ (subschemeι _a0 ⁻¹' ⋃₀ Cc_)ᶜ := by
    rw [← preimage_compl]
    exact (siI _a0 ⁻¹ᵁ ⟨(⋃₀ Cc_)ᶜ, hK.isOpen_compl⟩).isOpen
  exact mp_ isOpen_compl_iff h1
end

theorem componentUnionIdeal_eq_openSubschemeKer
    (J : FinSet T.boundary.length) (Cc_ : Set $ CSet T.scheme)
    (hop : IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_) :
    componentUnionIdeal T.boundary J Cc_ hop
      = openSubschemeKer (intersectionIdeal T.boundary J) (componentUnionOpens T.boundary J Cc_ hop) := by
  rw [componentUnionIdeal_eq_ker, openSubschemeKer_eq_ker]
end

theorem smooth_componentUnionIdeal : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ J,
      ∀ Cc_ ⊆ intersectionComponents T.boundary J,
        ∀ (hop : IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_),
          Smooth
            ((componentUnionIdeal T.boundary J Cc_ hop).si ≫ structMap T) := by
  intro T hT J Cc_ hCc_ hop
  have hsm :=
    MonomialChart.smooth_intersectionIdeal_subscheme T hT J
  rw [componentUnionIdeal_eq_openSubschemeKer T J Cc_ hop]
  exact smooth_subschemeio_openSubschemeKer_comp (intersectionIdeal T.boundary J)
    (componentUnionOpens T.boundary J Cc_ hop)
    (isClosed_componentUnionOpens T hT J Cc_ hCc_ hop) T.structMap

theorem hasStrictNormalCrossingsWith_componentUnionIdeal : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (J : FinSet T.boundary.length),
      ∀ Cc_ ⊆ intersectionComponents T.boundary J,
        ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_)),
          HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J Cc_ hop) T.boundary := by
  classical
  intro T hT J Cc_ hCc_ hop
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  have hWcl :=
    isClosed_componentUnionOpens T hT J Cc_ hCc_ hop
  have hce :=
    componentUnionIdeal_eq_openSubschemeKer T J Cc_ hop
  let _a1 := intersectionIdeal T.boundary J
  have hximg : x ∈ _a1.subschemeι.base ''
      (componentUnionOpens T.boundary J Cc_ hop) := by
    rw [← support_openSubschemeKer _a1
      (componentUnionOpens T.boundary J Cc_ hop) hWcl, ← hce]
    exact hx
  obtain ⟨U1_, hxU1, hU1⟩ := exists_opens_preimage_subschemeio_le _a1
    (componentUnionOpens T.boundary J Cc_ hop) x hximg
  obtain ⟨U0_, hxU0_, m, c0_, a, ha1, ha2, ha3⟩ :=
    (an2 (mp_ (inStrictNormalCrossingPosition_iff T.structMap T.boundary) hT.snc) x).exists_etaleChart
  have hxV : x ∈ U0_ ⊓ U1_ := ⟨hxU0_, hxU1⟩
  have hxsupp : x ∈ spI _a1 := by
    have hxs : x ∈ ⋃₀ Cc_ := by
      rwa [← componentUnionIdeal_support_eq_sUnion T hT J Cc_ hCc_ hop]
    obtain ⟨C, hC, hxC⟩ := hxs
    exact (hCc_ hC).2.1 hxC
  let _a0 := restrictIdeal _a1 $ U0_ ⊓ U1_
  have hbs : _a0
      = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) (U0_ ⊓ U1_) :=
    MonomialChart.restrictIdeal_biSup_finset (U0_ ⊓ U1_) T.boundary.get J
  have h4 : restrictIdeal (componentUnionIdeal T.boundary J Cc_ hop) (U0_ ⊓ U1_)
      = _a0 := by
    rw [hce]
    exact restrictIdeal_openSubschemeKer_of_preimage_le _a1
      (componentUnionOpens T.boundary J Cc_ hop) hWcl (U0_ ⊓ U1_)
      (le_trans (preimage_mono _ inf_le_right) hU1)
  have hJsome : ∀ j ∈ J, ∃ t, a j = some t := by
    intro j hj
    by_cases hn : a j = none
    exfalso
    have hle :=
      le_iSup₂ (f := fun i (_ : i ∈ J) =>
        restrictIdeal (T.boundary.get i) (U0_ ⊓ U1_)) j hj
    rw [restrictIdeal_eq_top_of_le (T.boundary.get j) inf_le_left (ha2 j j.isLt hn)] at hle
    exact notMem_support_of_comap_ι_eq_top _a1
      (hbs.trans (mp_ top_le_iff hle)) hxV hxsupp
    exact Option.ne_none_iff_exists'.mp hn
  obtain ⟨S, hS⟩ : ∃ S, ∀ t, t ∈ S ↔ ∃ j ∈ J, a j = some t :=
    ⟨Finset.univ.filter fun t => ∃ j ∈ J, a j = some t, by intro t; simp⟩
  have key : ∀ j ∈ J, ∃ t, t ∈ S ∧
      restrictIdeal (T.boundary.get j) (U0_ ⊓ U1_)
        = (c0_.restrict inf_le_left).coordIdeal {t} := by
    intro j hj
    obtain ⟨t, hat⟩ := hJsome j hj
    exact ⟨t, mpr_ (hS t) ⟨j, hj, hat⟩,
      restrictIdeal_eq_restrict_coordIdeal_of_le inf_le_left c0_ (T.boundary.get j) {t}
        (ha3 j j.isLt t hat)⟩
  have key2 : ∀ t ∈ S, ∃ j ∈ J,
      (c0_.restrict inf_le_left).coordIdeal {t}
        = restrictIdeal (T.boundary.get j) (U0_ ⊓ U1_) := by
    intro t ht
    obtain ⟨j, hj, hat⟩ := mp_ (hS t) ht
    exact ⟨j, hj, sy_ (restrictIdeal_eq_restrict_coordIdeal_of_le inf_le_left c0_ (T.boundary.get j) {t}
      (ha3 j j.isLt t hat))⟩
  refine ⟨U0_ ⊓ U1_, hxV, m, c0_.restrict inf_le_left, a, S, ha1, ?_, ?_, ?_⟩
  intro i hi hin
  exact restrictIdeal_eq_top_of_le _ inf_le_left $ ha2 i hi hin
  intro i hi t hit
  exact restrictIdeal_eq_restrict_coordIdeal_of_le inf_le_left c0_ _ {t} (ha3 i hi t hit)
  rw [h4, hbs, MonomialChart.coordIdeal_eq_biSup_singleton T.structMap (U0_ ⊓ U1_) m
    (c0_.restrict inf_le_left) S]
  refine le_antisymm (iSup₂_le ?_) $ iSup₂_le ?_
  intro j hj
  obtain ⟨t, htS, heq⟩ := key j hj
  rw [heq]
  exact le_iSup₂ (f := fun t (_ : t ∈ S) =>
    (c0_.restrict inf_le_left).coordIdeal {t}) t htS
  intro t ht
  obtain ⟨j, hj, heq⟩ := key2 t ht
  rw [heq]
  exact le_iSup₂ (f := fun j (_ : j ∈ J) =>
    restrictIdeal (T.boundary.get j) (U0_ ⊓ U1_)) j hj

end MonomialCenterGeometry





section
variable {Y : Sch}
section
variable {L : Bdy Y} {J} {C} (hC : C ∈ intersectionComponents L J)
include hC
theorem isClosed_intersectionComponents_of_mem : IsClosed C := by
  have h :=
    (mem_intersectionComponents_iff L J C).1 hC
  exact isClosed_of_closure_subset (h.2.2 (closure C) h.1.closure subset_closure $ closure_minimal h.2.1 $ (intersectionIdeal L J).support.2).subset

theorem isIrreducible_of_mem_intersectionComponents : IsIrreducible C :=
  ((mem_intersectionComponents_iff L J C).1 hC).1

theorem isGenericPoint_genericPoint_of_mem_intersectionComponents :
    IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC).genericPoint C := by
  have h : closure {(isIrreducible_of_mem_intersectionComponents hC).genericPoint} = closure C := by
    simp
  exact tr_ h $ (isClosed_intersectionComponents_of_mem hC).closure_eq
end
noncomputable abbrev icGP {Y : Sch} {L : List Y.IdealSheafData} {J : FinSet L.length} {C : Set ↥Y} (hC : C ∈ intersectionComponents L J) := (isIrreducible_of_mem_intersectionComponents hC).genericPoint

section
variable (I : ISD Y)
section
variable (m : ℕ) (L : Bdy Y)
theorem mem_intersectionComponents_of_isCandidateComponent (r : ℕ) (J : FinSet L.length) (C : Set ↥Y)
    (h : IsCandidateComponent I m L r J C) : C ∈ intersectionComponents L J := by
  unfold IsCandidateComponent at h
  simp [mem_intersectionComponents_iff] at h ⊢
  tauto

theorem monomialCenter_eq_top_of_minIndexCard_eq_zero (h : minIndexCard I m L = 0) : monomialCenter I m L = ⊤ := by
  unfold monomialCenter
  simp [h]

theorem minIndexCard_eq_sInf :
    minIndexCard I m L =
      sInf {r : ℕ | 1 ≤ r ∧ ∃ J C,
        IsCandidateComponent I m L r J C} := rfl

theorem minIndexCard_spec
    (hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ J C,
      IsCandidateComponent I m L r J C) :
    1 ≤ minIndexCard I m L ∧
      (∃ J C,
        IsCandidateComponent I m L (minIndexCard I m L) J C) ∧
      (∀ r : ℕ, 1 ≤ r → ∀ J C,
        IsCandidateComponent I m L r J C → minIndexCard I m L ≤ r) := by
  classical
  have hmem : minIndexCard I m L ∈ {r : ℕ | 1 ≤ r ∧ ∃ J C,
      IsCandidateComponent I m L r J C} := by
    rw [minIndexCard_eq_sInf I m L]
    exact sInf_mem hex
  obtain ⟨h1, h2⟩ := hmem
  refine ⟨h1, h2, ?_⟩
  intro r hr J C hcand
  rw [minIndexCard_eq_sInf I m L]
  exact sInf_le ⟨hr, J, C, hcand⟩

theorem minIndexCard_eq_zero_iff :
    minIndexCard I m L = 0 ↔
      ¬ ∃ r : ℕ, 1 ≤ r ∧ ∃ J C,
        IsCandidateComponent I m L r J C := by
  rw [minIndexCard_eq_sInf I m L, sInf_eq_zero]
  constructor
  rintro (h0 | hempty) hex
  obtain ⟨h1, -⟩ := h0
  omega
  obtain ⟨r, hr⟩ := hex
  refine mp_ (mem_empty_iff_false r) ?_
  rwa [← hempty]
  intro hne
  refine inr ?_
  ext r
  constructor
  simp_all
  simp_all

theorem exists_isCandidateComponent_minIndexCard (h : minIndexCard I m L ≠ 0) :
    ∃ J C, IsCandidateComponent I m L (minIndexCard I m L) J C := by
  refine (minIndexCard_spec I m L ?_).2.1
  by_contra hc
  exact h $ (minIndexCard_eq_zero_iff I m L).2 hc

theorem maxCandidateOrder_eq_iSup_orderAlong :
    maxCandidateOrder I m L =
      ⨆ J : FinSet L.length, ⨆ C : Set ↥Y,
        ⨆ _ : IsCandidateComponent I m L (minIndexCard I m L) J C, orderAlong I C :=
  rfl

theorem maxBinaryCode_eq_sSup :
    maxBinaryCode I m L =
      sSup {c : ℕ | ∃ J : FinSet L.length, IsMaxOrderIndexSet I m L J ∧ binaryEncode J = c} := rfl

def centerComponents : Set $ Set ↥Y :=
  {C : Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
      orderAlong I C = maxCandidateOrder I m L}

theorem mem_centerComponents_iff (C : Set ↥Y) :
    C ∈ centerComponents I m L ↔
      IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
        orderAlong I C = maxCandidateOrder I m L :=
  m22

theorem centerComponents_subset_intersectionComponents :
    centerComponents I m L ⊆ intersectionComponents L (lexMaxIndices I m L) := by
  intro C hC
  exact mem_intersectionComponents_of_isCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C
    ((mem_centerComponents_iff I m L C).1 hC).1

theorem monomialCenterSet_eq_sUnion_centerComponents :
    monomialCenterSet I m L = ⋃₀ centerComponents I m L := by
  ext x
  simp [monomialCenterSet, centerComponents, mem_sUnion]

def maxOrderCandidatePairs : Set $ FinSet L.length × Set ↥Y :=
  {p : FinSet L.length × Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) p.1 p.2 ∧ orderAlong I p.2 = maxCandidateOrder I m L}

theorem mem_maxOrderCandidatePairs_iff (p : FinSet L.length × Set ↥Y) :
    p ∈ maxOrderCandidatePairs I m L ↔
      IsCandidateComponent I m L (minIndexCard I m L) p.1 p.2 ∧ orderAlong I p.2 = maxCandidateOrder I m L :=
  m22
end

theorem orderAlong_eq_orderAt_of_mem_intersectionComponents
    {L : Bdy Y} {J : FinSet L.length} {C : Set ↥Y}
    (hC : C ∈ intersectionComponents L J) :
    orderAlong I C = orderAt I (icGP hC) := by
  unfold orderAlong
  exact dif_pos $ isIrreducible_of_mem_intersectionComponents hC

theorem orderAlong_eq_orderAt_genericPoint
    {C} (h : IsIrreducible C) : orderAlong I C = orderAt I h.genericPoint := by
  unfold orderAlong
  exact dif_pos h

theorem orderAlong_eq_of_closure_eq {S}
    (hS : IsIrreducible S) {C} (hC : IsIrreducible C)
    (hcl : closure S = closure C) : orderAlong I S = orderAlong I C := by
  rw [orderAlong_eq_orderAt_genericPoint I hS, orderAlong_eq_orderAt_genericPoint I hC]
  have h1 : closure ({hS.genericPoint} : Set Y) = closure ({hC.genericPoint} : Set Y) := by simp_all
  rw [(mpr_ inseparable_iff_closure_eq h1).eq]
end

section
variable (L : Bdy Y)
theorem openSublocusIdeal_eq_componentUnionIdeal
    J Cc_
    S
    (hEq : S = ⇑(intersectionIdeal L J).si ⁻¹' ⋃₀ Cc_)
    (hS : IsOpen S) (hop : IsOpen $ ⇑(intersectionIdeal L J).si ⁻¹' ⋃₀ Cc_) :
    openSublocusIdeal (intersectionIdeal L J).si S hS = componentUnionIdeal L J Cc_ hop := by
  subst hEq
  rfl

def supportIndices (x : ↥Y) :
    FinSet L.length :=
  @Finset.filter _ (fun j => x ∈ support (get L j)) (Classical.decPred _) univ

theorem mem_supportIndices (x : ↥Y)
    (j : Fin L.length) : j ∈ supportIndices L x ↔ x ∈ support (get L j) := by
  simp [supportIndices]
end

theorem card_eq_minIndexCard_of_isMaxOrderIndexSet {I : ISD Y}
    {m : ℕ} {L : Bdy Y} {J : FinSet L.length} (hJ : IsMaxOrderIndexSet I m L J) :
    J.card = minIndexCard I m L := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hcand, -⟩ := hJ
  unfold IsCandidateComponent at hcand
  exact an1 hcand

theorem mem_support_intersectionIdeal (L : Bdy Y)
    (J : FinSet L.length) (x : ↥Y) (hx : ∀ j ∈ J, x ∈ support (get L j)) :
    x ∈ support (intersectionIdeal L J) :=by simp_all
theorem exists_isIrreducibleComponentOf_mem (S : Set ↥Y) (x : ↥Y) (hx : x ∈ S) :
    ∃ C : Set ↥Y, x ∈ C ∧ IsIrreducibleComponentOf C S := by
  let _m0 := (⟨x, hx⟩ : S)
  have hsing : IsPreirreducible ({_m0} : Set S) := by
    intro u v _ _ hu hv
    obtain ⟨p, hp, hpu⟩ := hu
    obtain ⟨q, hq, hqv⟩ := hv
    rw [mem_singleton_iff] at hp hq
    subst hp
    subst hq
    exact ⟨_m0, rfl, hpu, hqv⟩
  obtain ⟨t, ht, hts, hmax⟩ := exists_preirreducible ({_m0} : Set S) hsing
  have hxim : x ∈ imS val t := ⟨_m0, hts $ mem_singleton_iff.2 rfl, rfl⟩
  have hsubS : imS val t ⊆ S := by simp_all
  have hpre : IsPreirreducible $ imS val t := by
    intro u v hu hv hu' hv'
    obtain ⟨p, hpim, hpu⟩ := hu'
    obtain ⟨q, hqim, hqv⟩ := hv'
    obtain ⟨p', hp't, hp'eq⟩ := hpim
    obtain ⟨q', hq't, hq'eq⟩ := hqim
    have hp'u : p' ∈ m142 val u := by simp_all
    have hq'v : q' ∈ m142 val v := by simp_all
    obtain ⟨r, hrt, hru, hrv⟩ :=
      ht (m142 val u) (m142 val v) (hu.preimage continuous_subtype_val)
        (hv.preimage continuous_subtype_val) ⟨p', hp't, hp'u⟩ ⟨q', hq't, hq'v⟩
    exact ⟨r, ⟨r, hrt, rfl⟩, hru, hrv⟩
  have hmaxi : ∀ C', IsIrreducible C' → imS val t ⊆ C' → C' ⊆ S →
      C' = imS val t := by
    intro C' hC' hle hC'S
    have hpre' : IsPreirreducible (m142 val C' : Set S) := by
      intro u v hu hv hu' hv'
      obtain ⟨u0_, hu0, hu0e⟩ :=
        isOpen_induced_iff.1 hu
      obtain ⟨v0, hv0_, hv0e⟩ :=
        isOpen_induced_iff.1 hv
      subst hu0e
      subst hv0e
      obtain ⟨p, hp, hpu⟩ := hu'
      obtain ⟨q, hq, hqv⟩ := hv'
      obtain ⟨y, hyC', hyu, hyv⟩ :=
        an2 hC' u0_ v0 hu0 hv0_ ⟨p, hp, hpu⟩ ⟨q, hq, hqv⟩
      exact ⟨(⟨y, hC'S hyC'⟩ : S), hyC', hyu, hyv⟩
    have hsubt := fun p hp => hle ⟨p, hp, rfl⟩
    refine m15 ?_ hle
    intro y hy
    refine ⟨(⟨y, hC'S hy⟩ : S), ?_, rfl⟩
    rwa [← hmax _ hpre' hsubt]
  refine ⟨imS val t, hxim, ?_⟩
  show (IsIrreducible $ imS val t) ∧ imS val t ⊆ S ∧
    ∀ C', IsIrreducible C' → imS val t ⊆ C' → C' ⊆ S → C' = imS val t
  exact ⟨⟨⟨x, hxim⟩, hpre⟩, hsubS, hmaxi⟩

theorem exists_mem_intersectionComponents_of_mem_support
    (L : Bdy Y) (J : FinSet L.length) (x : ↥Y)
    (hx : x ∈ (↑(intersectionIdeal L J).support : Set ↥Y)) :
    ∃ C : Set ↥Y, x ∈ C ∧ C ∈ intersectionComponents L J := by
  obtain ⟨C, hxC, hcomp⟩ :=
    exists_isIrreducibleComponentOf_mem (support (intersectionIdeal L J) : Set Y) x hx
  exact ⟨C, hxC, (mem_intersectionComponents_iff L J C).2 hcomp⟩
end

section
variable (hGeom : MonomialGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : IsLocallyMonomialTriple T)
include hGeom hT
section
variable {J} {C} (hC : C ∈ intersectionComponents T.boundary J) (i : Fin T.boundary.length)
include hC
theorem subset_support_iff_mem_of_mem_intersectionComponents :
    C ⊆ (↑(T.boundary.get i).support : CSet T.scheme) ↔ i ∈ J :=
  hGeom.components_subset_divisor_iff T hT.valid J C hC i

theorem genericPoint_mem_support_iff_mem :
    (icGP hC) ∈ support (T.boundary.get i) ↔ i ∈ J := by
  have hgen :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hsub := subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC i
  constructor
  intro hx
  refine hsub.1 ?_
  have hsubc := ((T.boundary.get i).support.2).closure_subset_iff.2 $ singleton_subset_iff.2 hx
  rwa [hgen] at hsubc
  intro hi
  have hmem : (icGP hC) ∈
      closure ({(icGP hC)} : CSet T.scheme) :=
    subset_closure rfl
  rw [hgen] at hmem
  exact hsub.2 hi hmem
end

theorem finite_setOf_isCandidateComponent :
    {p : FinSet T.boundary.length × CSet T.scheme |
      ∃ r : ℕ, IsCandidateComponent T.ideal T.mult T.boundary r p.1 p.2}.Finite := by
  classical
  refine (finite_iUnion fun J => Set.Finite.image (fun C => ((J, C) : FinSet T.boundary.length × CSet T.scheme)) $ hGeom.components_finite T hT.valid J).subset ?_
  rintro ⟨J, C⟩ ⟨r, hcand⟩
  exact mem_iUnion.2 ⟨J, mem_image_of_mem _ $ mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary r J C hcand⟩

theorem isOpen_preimage_sUnion_centerComponents :
    IsOpen $ ⇑(intersectionIdeal T.boundary $ lexMaxIndices T.ideal T.mult T.boundary).subschemeι ⁻¹'
      ⋃₀ centerComponents T.ideal T.mult T.boundary :=
  hGeom.sUnion_isOpen T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)

theorem isOpen_preimage_monomialCenterSet :
    IsOpen $ ⇑(intersectionIdeal T.boundary $ lexMaxIndices T.ideal T.mult T.boundary).subschemeι ⁻¹'
      monomialCenterSet T.ideal T.mult T.boundary := by
  rw [monomialCenterSet_eq_sUnion_centerComponents]
  exact isOpen_preimage_sUnion_centerComponents hGeom hT

section
variable (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
include h
theorem monomialCenter_eq_componentUnionIdeal :
    T.mc =
      componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
        (centerComponents T.ideal T.mult T.boundary)
        (isOpen_preimage_sUnion_centerComponents hGeom hT) := by
  unfold mc monomialCenter
  rw [dif_pos ⟨h, isOpen_preimage_monomialCenterSet hGeom hT⟩]
  exact openSublocusIdeal_eq_componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
    (centerComponents T.ideal T.mult T.boundary) _
    (by rw [monomialCenterSet_eq_sUnion_centerComponents]) _ _

theorem support_monomialCenter :
    (↑(T.mc).support : CSet T.scheme) =
      monomialCenterSet T.ideal T.mult T.boundary := by
  rw [monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary,
    monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_support T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

theorem smooth_monomialCenter :
    Smooth
      (subschemeι (T.mc) ≫ structMap T) := by
  rw [monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_smooth T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

theorem hasStrictNormalCrossingsWith_monomialCenter :
    HasStrictNormalCrossingsWith T.structMap (T.mc) T.boundary := by
  rw [monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_snc T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _
end

theorem finite_maxOrderCandidatePairs :
    (maxOrderCandidatePairs T.ideal T.mult T.boundary).Finite := by
  refine (finite_setOf_isCandidateComponent hGeom hT).subset ?_
  rintro ⟨J, C⟩ ⟨hcand, -⟩
  exact ⟨minIndexCard T.ideal T.mult T.boundary, hcand⟩
end

section
variable {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible)
include hT
theorem subset_orderAtLeastLocus_of_le_orderAlong
    {J : FinSet T.boundary.length} {C : CSet T.scheme}
    (hC : C ∈ intersectionComponents T.boundary J) (c : ℕ) (hc : (c : ENat) ≤ orderAlong T.ideal C) :
    C ⊆ orderAtLeastLocus T.ideal c := by
  have := hT.charZero
  have := hT.smooth
  have hmem := hc
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC, ← mem_orderAtLeastLocus_iff] at hmem
  have hclosed :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal c
  have h2 :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hsub :=
    closure_minimal (singleton_subset_iff.2 hmem) hclosed
  rwa [← h2]

theorem minIndexCard_eq_zero_of_orderAtLeastLocus_eq_empty
    (h : orderAtLeastLocus T.ideal T.mult = (∅ : CSet T.scheme)) :
    minIndexCard T.ideal T.mult T.boundary = 0 := by
  rw [minIndexCard_eq_zero_iff]
  rintro ⟨r, hr, J, C, hcand⟩
  have hC :=
    mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary r J C hcand
  have hord : tMu T ≤ orderAlong T.ideal C := by
    unfold IsCandidateComponent at hcand
    exact hcand.2.2
  have hsub :=
    subset_orderAtLeastLocus_of_le_orderAlong hT hC T.mult hord
  obtain ⟨x, hx⟩ := an1 $ isIrreducible_of_mem_intersectionComponents hC
  rw [h] at hsub
  exact mp_ (mem_empty_iff_false x) $ hsub hx
end

section
variable (hGeom : MonomialGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : IsLocallyMonomialTriple T) (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
include hGeom hT h
theorem support_monomialCenter_subset_orderAtLeastLocus :
    (↑(T.mc).support : CSet T.scheme) ⊆
      orderAtLeastLocus T.ideal T.mult := by
  rw [support_monomialCenter hGeom hT h,
    monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  rintro x ⟨C, hC, hxC⟩
  have hcand :=
    ((mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hC).1
  refine subset_orderAtLeastLocus_of_le_orderAlong hT.valid (mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) (lexMaxIndices T.ideal T.mult T.boundary) C hcand) T.mult ?_ hxC
  have hcomp := hcand
  unfold IsCandidateComponent at hcomp
  exact hcomp.2.2

theorem exists_controlledTransform_monomialCenter :
    ∃ J : IdealSheafData $ blowup $ T.mc,
      ((T.mc).comap
            (proj $ T.mc)) ^ T.mult * J =
        T.ideal.comap (proj $ T.mc) := by
  let _c0 := T.mc
  classical
  have := hT.valid.charZero
  have := hT.valid.smooth
  have := hT.valid.isNoetherian
  have :=
    isNoetherian_of_isBlowupAlongIdealSheaf $ p46 _c0
  obtain ⟨J, hJ, -⟩ :=
    existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf
      (p34 _c0)
      _c0 T.ideal T.mult
      (p46 _c0) $ le_pow_of_hasStrictNormalCrossingsWith T.structMap _c0 T.ideal T.boundary (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h) T.mult $ support_monomialCenter_subset_orderAtLeastLocus hGeom hT h
  exact ⟨J, hJ⟩
end

theorem lt_top_of_le_natCast {a : ENat} {B : ℕ} (h : a ≤ (B : ENat)) : a < ⊤ :=
  h.trans_lt $ ENat.natCast_lt_top B

section
variable (hGeom : MonomialGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : IsLocallyMonomialTriple T)
include hGeom hT
theorem orderAlong_lt_top_of_isCandidateComponent {r : ℕ}
    {J : FinSet T.boundary.length} {C : CSet T.scheme}
    (hcand : IsCandidateComponent T.ideal T.mult T.boundary r J C) :
    orderAlong T.ideal C < ⊤ := by
  have hC : C ∈ intersectionComponents T.boundary J := by
    unfold IsCandidateComponent at hcand
    tauto
  obtain ⟨B, hB⟩ :=
    hGeom.orderAt_bounded T hT.valid T.ideal hT.valid.nonzeroOnComponents
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC]
  exact lt_top_of_le_natCast $ hB _

section
variable (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
include h
theorem maxCandidateOrder_spec :
    (∃ J C,
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) J C ∧
          orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary) ∧
      (∀ J C,
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) J C →
          orderAlong T.ideal C ≤ maxCandidateOrder T.ideal T.mult T.boundary) ∧
      ((mult T : ENat) ≤ maxCandidateOrder T.ideal T.mult T.boundary) ∧
      maxCandidateOrder T.ideal T.mult T.boundary < ⊤ := by
  classical
  obtain ⟨J1, C1_, hcand1⟩ := exists_isCandidateComponent_minIndexCard T.ideal T.mult T.boundary h
  let _a0 := FinSet $ bLen T
  let _a1 := minIndexCard T.ideal T.mult T.boundary
  have hsub : {p : _a0 × CSet T.scheme |
        IsCandidateComponent T.ideal T.mult T.boundary _a1 p.1 p.2} ⊆
      {p : _a0 × CSet T.scheme |
        ∃ r, IsCandidateComponent T.ideal T.mult T.boundary r p.1 p.2} := by
    intro p hp
    simp [mem_ofPred_eq] at hp ⊢
    exact ⟨_a1, hp⟩
  obtain ⟨p0_, hmem0_, hmax0⟩ :=
    exists_max_image _
      (fun q : _a0 × CSet T.scheme => orderAlong T.ideal q.2) ((finite_setOf_isCandidateComponent hGeom hT).subset hsub) ⟨(J1, C1_), hcand1⟩
  have hcand0 := hmem0_
  have hkey : maxCandidateOrder T.ideal T.mult T.boundary = orderAlong T.ideal p0_.2 := by
    rw [maxCandidateOrder_eq_iSup_orderAlong]
    refine le_antisymm ?_ $ le_iSup_of_le p0_.1 $ le_iSup_of_le p0_.2 $ le_iSup_of_le hcand0 le_rfl
    apply iSup_le
    intro J
    apply iSup_le
    intro C
    apply iSup_le
    intro hc
    exact hmax0 (J, C) hc
  refine ⟨⟨p0_.1, p0_.2, hcand0, sy_ hkey⟩, ?_, ?_, ?_⟩
  intro J C hc
  rw [hkey]
  exact hmax0 (J, C) hc
  rw [hkey]
  have hcomp := hcand0
  unfold IsCandidateComponent at hcomp
  exact hcomp.2.2
  rw [hkey]
  exact orderAlong_lt_top_of_isCandidateComponent hGeom hT hcand0

theorem lexMaxIndices_spec :
    IsMaxOrderIndexSet T.ideal T.mult T.boundary (lexMaxIndices T.ideal T.mult T.boundary) ∧
      ∀ J : FinSet T.boundary.length, IsMaxOrderIndexSet T.ideal T.mult T.boundary J →
        ¬ Lex (· < ·) (sortedIndices J)
            (sortedIndices $ lexMaxIndices T.ideal T.mult T.boundary) := by
  classical
  obtain ⟨J0, hJ0⟩ : ∃ J, IsMaxOrderIndexSet T.ideal T.mult T.boundary J := by
    obtain ⟨J, C, hcand, hord⟩ := an1 $ maxCandidateOrder_spec hGeom hT h
    refine ⟨J, ?_⟩
    unfold IsMaxOrderIndexSet
    exact ⟨C, hcand, hord⟩
  let _a1 := FinSet $ bLen T
  have hbdd : BddAbove {c : ℕ | ∃ J : _a1,
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c} := by
    refine bddAbove $ subset
      (finite_range fun J : _a1 => binaryEncode J) ?_
    rintro c ⟨J, -, rfl⟩
    exact mem_range_self J
  have hne : {c : ℕ | ∃ J,
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c}.Nonempty :=
    ⟨binaryEncode J0, ⟨J0, hJ0, rfl⟩⟩
  have hex : ∃ J,
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧
        binaryEncode J = maxBinaryCode T.ideal T.mult T.boundary := by
    rw [maxBinaryCode_eq_sSup]
    exact sSup_mem hne hbdd
  have hchosen : IsMaxOrderIndexSet T.ideal T.mult T.boundary (lexMaxIndices T.ideal T.mult T.boundary) ∧
      binaryEncode (lexMaxIndices T.ideal T.mult T.boundary)
        = maxBinaryCode T.ideal T.mult T.boundary := by
    unfold lexMaxIndices
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨an1 hchosen, ?_⟩
  intro J hJ hlex
  have hcard : J.card = (lexMaxIndices T.ideal T.mult T.boundary).card := by
    rw [card_eq_minIndexCard_of_isMaxOrderIndexSet hJ, card_eq_minIndexCard_of_isMaxOrderIndexSet hchosen.1]
  refine absurd ((MonomialCenter.binaryEncode_lt_iff_lex_of_card_eq J (lexMaxIndices T.ideal T.mult T.boundary) hcard).2 hlex) $ not_lt.2 ?_
  rw [hchosen.2, maxBinaryCode_eq_sSup]
  exact le_csSup hbdd ⟨J, hJ, rfl⟩

theorem card_lexMaxIndices :
    (lexMaxIndices T.ideal T.mult T.boundary).card = minIndexCard T.ideal T.mult T.boundary :=
  card_eq_minIndexCard_of_isMaxOrderIndexSet (lexMaxIndices_spec hGeom hT h).1

theorem monomialCenterSet_nonempty :
    (monomialCenterSet T.ideal T.mult T.boundary).Nonempty := by
  have hbest := an1 $ lexMaxIndices_spec hGeom hT h
  unfold IsMaxOrderIndexSet at hbest
  obtain ⟨C, hcand, hord⟩ := hbest
  obtain ⟨x, hx⟩ := an1 $ isIrreducible_of_mem_intersectionComponents $ mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) (lexMaxIndices T.ideal T.mult T.boundary) C hcand
  refine ⟨x, ?_⟩
  rw [monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  exact Set.mem_sUnion.2 ⟨C, (mem_centerComponents_iff T.ideal T.mult T.boundary C).2 ⟨hcand, hord⟩, hx⟩

theorem monomialCenter_ne_top :
    T.mc ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := monomialCenterSet_nonempty hGeom hT h
  have hxmem := hx
  rw [← support_monomialCenter hGeom hT h] at hxmem
  have hx2 : x ∈ spI (T.mc) := hxmem
  rw [mem_support_iff_stalkIdeal_ne_top, htop, stalkIdeal_top] at hx2
  exact hx2 rfl

theorem support_monomialCenter_subset_boundary :
    (↑(T.mc).support : CSet T.scheme) ⊆
      ⋃ D ∈ boundary T, (↑D.support : CSet T.scheme) := by
  rw [support_monomialCenter hGeom hT h,
    monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.1 hx
  have hne : (lexMaxIndices T.ideal T.mult T.boundary).Nonempty := by
    rw [← card_pos, card_lexMaxIndices hGeom hT h]
    exact Nat.pos_of_ne_zero h
  obtain ⟨j, hj⟩ := hne
  refine Set.mem_iUnion₂.2 ⟨T.boundary.get j, ?_, ((subset_support_iff_mem_of_mem_intersectionComponents hGeom hT (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC) j).2 hj) hxC⟩
  simp

theorem monomialCenter_spec :
    T.mc ≠ ⊤ ∧
      Smooth
        (subschemeι (T.mc) ≫ structMap T) ∧
      HasStrictNormalCrossingsWith T.structMap (T.mc) T.boundary ∧
      (↑(T.mc).support : CSet T.scheme) ⊆
        orderAtLeastLocus T.ideal T.mult ∧
      (∃ J : IdealSheafData $ blowup $ T.mc,
        ((T.mc).comap
              (proj $ T.mc)) ^ T.mult * J =
          T.ideal.comap (proj $ T.mc)) :=
  ⟨monomialCenter_ne_top hGeom hT h, smooth_monomialCenter hGeom hT h, hasStrictNormalCrossingsWith_monomialCenter hGeom hT h,
    support_monomialCenter_subset_orderAtLeastLocus hGeom hT h,
    exists_controlledTransform_monomialCenter hGeom hT h⟩
end
end

theorem orderAt_foldr_mul (k : Type) [Field k] [CharZero k] {X : Sch}
    (p : X ⟶ Sp k) [Smooth p]
    (x : ↥X) (L : Bdy X) :
    orderAt (L.foldr (· * ·) ⊤) x = (L.map fun I => orderAt I x).sum := by
  induction L with
  | nil => simp [orderAt_top]
  | cons I L ih => simp [orderAt_mul k p, ih]

section
variable (hGeom : MonomialGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : IsLocallyMonomialTriple T)
include hGeom hT
theorem orderAt_eq_sum_indicator_support (U : T.scheme.Opens)
    (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.i =
      (ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.i ^ a i).foldr (· * ·) ⊤)
    (x : ↥T.scheme) (hx : x ∈ U) :
    orderAt T.ideal x =
      ∑ j : Fin T.boundary.length,
        (a j : ENat) *
          (↑(T.boundary.get j).support : CSet T.scheme).indicator (fun _ => (1 : ENat)) x := by
  classical
  have := hT.valid.charZero
  have := hT.valid.smooth
  have : Smooth U.i := inferInstance
  have : Smooth $ opI U ≫ tMp T := inferInstance
  have h2 : orderAt (T.ideal.comap U.i) ⟨x, hx⟩
      = ∑ i : Fin $ bLen T,
          orderAt (cmI (T.boundary.get i) U.i ^ a i) ⟨x, hx⟩ := by
    rw [hmon, orderAt_foldr_mul T.base (opI U ≫ tMp T) ⟨x, hx⟩]
    simp [map_ofFn, sum_ofFn]
  have h3 : ∀ i,
      orderAt (cmI (T.boundary.get i) U.i ^ a i) ⟨x, hx⟩
        = (a i) *
            (support (T.boundary.get i) : CSet T.scheme).indicator (fun _ => 1) x := by
    intro i
    have hmemlist : T.boundary.get i ∈ tBd T := by simp
    have hcomap : orderAt (cmI (T.boundary.get i) U.i) ⟨x, hx⟩
        = orderAt (T.boundary.get i) x :=
      orderAt_comap T.base T.structMap U.i (T.boundary.get i) ⟨x, hx⟩
    rw [orderAt_pow T.base (opI U ≫ tMp T) (cmI (T.boundary.get i) U.i) (a i) ⟨x, hx⟩,
      hcomap]
    by_cases hmem : x ∈ spI (T.boundary.get i)
    have hset : x ∈ (support (T.boundary.get i) : CSet T.scheme) := hmem
    rw [hGeom.orderAt_boundary_eq_one T hT.valid (T.boundary.get i) hmemlist x hmem,
      indicator_of_mem hset]
    have hset : x ∉ (support (T.boundary.get i) : CSet T.scheme) := hmem
    rw [(orderAt_eq_zero_iff_not_mem_support (T.boundary.get i) x).2 hmem,
      indicator_apply, if_neg hset]
  calc orderAt T.ideal x = orderAt (T.ideal.comap U.i) ⟨x, hx⟩ := sy_ (orderAt_comap T.base T.structMap U.i T.ideal ⟨x, hx⟩)
    _ = ∑ i : Fin $ bLen T,
          orderAt (cmI (T.boundary.get i) U.i ^ a i) ⟨x, hx⟩ := h2
    _ = ∑ j : Fin $ bLen T,
          (a j : ENat) *
            (support (T.boundary.get j) : CSet T.scheme).indicator (fun _ => (1 : ENat)) x :=
        sum_congr rfl fun i _ => h3 i

theorem orderAlong_eq_sum_of_monomial {J : FinSet T.boundary.length}
    {C : CSet T.scheme} (hC : C ∈ intersectionComponents T.boundary J) {x : ↥T.scheme} (hxC : x ∈ C)
    (U : T.scheme.Opens) (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.i =
      (ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.i ^ a i).foldr (· * ·) ⊤) :
    orderAlong T.ideal C = ((∑ j ∈ J, a j : ℕ) : ENat) := by
  have hxiU0 : (icGP hC) ∈ U := by
    by_contra hnot
    have h2 : C ⊆ (U : CSet T.scheme)ᶜ := by
      rw [← isGenericPoint_genericPoint_of_mem_intersectionComponents hC]
      exact closure_minimal (singleton_subset_iff.2 hnot)
        (isOpen U).isClosed_compl
    exact h2 hxC hxU
  obtain ⟨xi_, hord, hxiU_, hxis⟩ :
      ∃ xi_, orderAlong T.ideal C = orderAt T.ideal xi_ ∧ xi_ ∈ U ∧
        ∀ j, (xi_ ∈ spI (T.boundary.get j) ↔ j ∈ J) :=
    ⟨icGP hC,
      orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC, hxiU0,
      fun j => genericPoint_mem_support_iff_mem hGeom hT hC j⟩
  rw [hord, orderAt_eq_sum_indicator_support hGeom hT U a hmon xi_ hxiU_]
  have hzero : ∀ j ∈ (univ : FinSet $ bLen T), j ∉ J →
      (a j : ENat) *
        (support (T.boundary.get j) : CSet T.scheme).indicator (fun _ => (1 : ENat)) xi_ = 0 := by simp_all
  have hone : ∀ j ∈ J,
      (a j : ENat) *
        (support (T.boundary.get j) : CSet T.scheme).indicator (fun _ => (1 : ENat)) xi_
        = (a j : ENat) := by simp_all
  rw [← sum_subset (subset_univ J) hzero, sum_congr rfl hone]
  exact sy_ $ cast_sum J a

theorem orderAt_eq_sum_supportIndices (x : ↥T.scheme) (U : T.scheme.Opens)
    (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.i =
      (ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.i ^ a i).foldr (· * ·) ⊤) :
    orderAt T.ideal x = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ENat) := by
  classical
  let _a0 := supportIndices T.boundary x
  have h2 : ∀ j ∈ (univ : FinSet $ bLen T),
      j ∉ _a0 →
      (a j : ENat) *
          (support (T.boundary.get j) : CSet T.scheme).indicator (fun _ => (1 : ENat)) x = 0 := by
    intro j _ hj
    have hx : x ∉ (↑(T.boundary.get j).support : CSet T.scheme) := by
      intro hmem
      exact hj $ (mem_supportIndices T.boundary x j).2 hmem
    rw [indicator_apply, if_neg hx, mul_zero]
  have h1 : ∀ j ∈ _a0,
      (a j : ENat) *
          (support (T.boundary.get j) : CSet T.scheme).indicator (fun _ => (1 : ENat)) x
        = (a j : ENat) := by
    intro j hj
    have hx : x ∈ (support (T.boundary.get j) : CSet T.scheme) :=
      (mem_supportIndices T.boundary x j).1 hj
    rw [indicator_apply, if_pos hx]
    exact mul_one _
  rw [orderAt_eq_sum_indicator_support hGeom hT U a hmon x hxU, cast_sum,
    ← sum_subset (subset_univ _a0) h2]
  exact sum_congr rfl h1

theorem orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero
    (h : minIndexCard T.ideal T.mult T.boundary = 0) :
    orderAtLeastLocus T.ideal T.mult = (∅ : CSet T.scheme) := by
  classical
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨U, hxU, a, hmon⟩ := hT.monomialNear x hx
  have hmult := hT.valid.one_le_mult
  have hmle := (mem_orderAtLeastLocus_iff _ _ _).1 hx
  have hord :=
    orderAt_eq_sum_supportIndices hGeom hT x U hxU a hmon
  let _a0 := supportIndices T.boundary x
  have hJne : _a0.Nonempty := by
    rcases eq_empty_or_nonempty (supportIndices T.boundary x) with he | hne'
    simp_all
    exact hne'
  have hxsupp :=
    mem_support_intersectionIdeal T.boundary (supportIndices T.boundary x) x
      fun j hj => (mem_supportIndices T.boundary x j).1 hj
  obtain ⟨C, hxC, hcomp⟩ :=
    exists_isIrreducibleComponentOf_mem
      (support (intersectionIdeal T.boundary $ supportIndices T.boundary x) : CSet T.scheme) x hxsupp
  have hCmem :=
    (mem_intersectionComponents_iff T.boundary (supportIndices T.boundary x) C).2 hcomp
  have hordC :=
    orderAlong_eq_sum_of_monomial hGeom hT hCmem hxC U hxU a hmon
  have hordm := hmle
  rw [hord, ← hordC] at hordm
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (supportIndices T.boundary x).card (supportIndices T.boundary x) C := by
    unfold IsCandidateComponent
    refine ⟨rfl, ?_, ?_⟩
    assumption
    assumption
  have hcontr := (minIndexCard_eq_zero_iff _ _ _).1 h
  have hcard : 1 ≤ _a0.card := by simp_all
  exact hcontr ⟨_a0.card, hcard,
    supportIndices T.boundary x, C, hcand⟩
end





section
variable (T : MarkedIdealWithBoundary) {X' : Sch} (pi_ : X' ⟶ scheme T) (q : X' ⟶ Sp T.base) (I' : ISD X')
def blowupTriple : MarkedIdealWithBoundary where
  base := T.base
  instField := inferInstance
  scheme := X'
  structMap := q
  ideal := I'
  mult := mult T
  boundary := transformedBoundary pi_ (T.mc) T.boundary






@[simp] theorem blowupTriple_boundary :
    boundary (blowupTriple T pi_ q I') =
      transformedBoundary pi_ (T.mc) T.boundary := rfl
end

section
variable (hGeom : MonomialGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : IsLocallyMonomialTriple T)
include hGeom hT
theorem orderAt_transform_eq_of_not_mem_exceptional
    {X' : Sch} (pi_ : X' ⟶ scheme T)
    (hpi_ : IsBlowupAlongIdealSheaf pi_ $ T.mc)
    (I' : ISD X')
    (hI' : (T.mc).comap pi_ ^ T.mult * I' =
      T.ideal.comap pi_)
    (x' : ↥X')
    (hx' : x' ∉ support (exceptionalIdeal pi_ $ T.mc)) :
    orderAt I' x' = orderAt T.ideal (pi_ x') := by
  have hx2 := hx'
  rw [p9] at hx2
  let _a0 := T.mc
  have htop : stalkIdeal (cmI _a0 pi_) x' = ⊤ := by
    by_contra hne
    exact hx2 $ (mem_support_iff_stalkIdeal_ne_top _ _).2 hne
  refine st_ (orderAt_eq_of_stalkIdeal_eq ?_)
    (hGeom.orderAt_comap_off_exceptional T hT.valid X' pi_
      _a0 hpi_ x' hx' T.ideal)
  rw [← hI', stalkIdeal_mul, stalkIdeal_pow, htop, ← m217, one_pow, one_mul]

theorem orderAlong_transform_eq_of_genericPoint_not_mem_exceptional
    (_h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Sch} (pi_ : X' ⟶ scheme T)
    (hpi_ : IsBlowupAlongIdealSheaf pi_ $ T.mc)
    I'
    (hI' : (T.mc).comap pi_ ^ T.mult * I' =
      T.ideal.comap pi_)
    {J : FinSet T.boundary.length} {C'}
    (hC' : C' ∈ intersectionComponents
      (transformedBoundary pi_ (T.mc) T.boundary)
      (J.image $ strictTransformIndex pi_ (T.mc) T.boundary))
    (hoff : (icGP hC') ∉
      support (exceptionalIdeal pi_ $ T.mc)) :
    orderAlong I' C' = orderAlong T.ideal (⇑pi_ '' C') := by
  have hSirr :=
    (isIrreducible_of_mem_intersectionComponents hC').image _ pi_.continuous.continuousOn
  let _a0 := pi_ $ icGP hC'
  have h2 : orderAlong T.ideal (pi_ '' C')
      = orderAt T.ideal _a0 := by
    rw [orderAlong_eq_orderAt_genericPoint T.ideal hSirr]
    have h3 : closure ({hSirr.genericPoint} : CSet T.scheme)
        = closure ({_a0} : CSet T.scheme) := by
      rw [← closure_image_genericPoint (f := pi_) pi_.continuous $ isGenericPoint_genericPoint_of_mem_intersectionComponents hC']
      simp
    rw [(mpr_ inseparable_iff_closure_eq h3).eq]
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents I' hC', h2]
  exact orderAt_transform_eq_of_not_mem_exceptional hGeom hT pi_ hpi_ I' hI' _ hoff
end

section
variable {X' X : Sch} (pi_ : X' ⟶ X) (Z : ISD X) (L : Bdy X)
theorem get_transformedBoundary_strictTransformIndex (j : Fin L.length) :
    get (transformedBoundary pi_ Z L) (strictTransformIndex pi_ Z L j) = strictTransform pi_ Z (get L j) := by
  have hlt : ((strictTransformIndex pi_ Z L j : Fin (transformedBoundary pi_ Z L).length) : ℕ)
      < lenL (L.map $ p6 pi_ Z) := by
    rw [strictTransformIndex_val]
    simp
  simp [get_eq_getElem]
  rw [getElem_append_left hlt]
  exact getElem_map _

theorem get_transformedBoundary_exceptionalIndex :
    get (transformedBoundary pi_ Z L) (exceptionalIndex pi_ Z L) = exceptionalIdeal pi_ Z := by
  have hge : lenL (L.map $ p6 pi_ Z)
      ≤ ((exceptionalIndex pi_ Z L : Fin (transformedBoundary pi_ Z L).length) : ℕ) := by
    rw [exceptionalIndex_val]
    simp
  simp [get_eq_getElem]
  rw [getElem_append_right hge]
  simp [exceptionalIndex_val]

theorem strictTransformIndex_injective : Function.Injective $ strictTransformIndex pi_ Z L := by
  intro i j hij
  have hv : ((strictTransformIndex pi_ Z L i : Fin (transformedBoundary pi_ Z L).length) : ℕ)
      = ((strictTransformIndex pi_ Z L j : Fin (transformedBoundary pi_ Z L).length) : ℕ) := by rw [hij]
  rw [strictTransformIndex_val, strictTransformIndex_val] at hv
  exact val_injective hv

theorem eq_exceptionalIndex_or_exists_strictTransformIndex
    (i : Fin (transformedBoundary pi_ Z L).length) :
    i = exceptionalIndex pi_ Z L ∨ ∃ j, strictTransformIndex pi_ Z L j = i := by
  have hlen := transformedBoundary_length pi_ Z L
  have hi := i.isLt
  have hlt : i < length L + 1 := by omega
  rcases lt_or_ge i L.length with hj | hj
  exact inr ⟨⟨i, hj⟩, val_injective $ by rw [strictTransformIndex_val]⟩
  refine inl $ val_injective ?_
  rw [exceptionalIndex_val]
  omega

section
variable (J' : Finset (Fin (transformedBoundary pi_ Z L).length))
section
variable (hnew : exceptionalIndex pi_ Z L ∉ J')
include hnew
theorem image_strictTransformIndex_preimageStrictTransformIndex :
    (preimageStrictTransformIndex pi_ Z L J').image (strictTransformIndex pi_ Z L) = J' := by
  classical
  ext i
  simp [mem_image, mem_preimageStrictTransformIndex_iff]
  constructor
  rintro ⟨j, hj, rfl⟩
  exact hj
  intro hi
  rcases eq_exceptionalIndex_or_exists_strictTransformIndex pi_ Z L i with rfl | ⟨j, rfl⟩
  exact absurd hi hnew
  exact ⟨j, hi, rfl⟩

theorem card_preimageStrictTransformIndex_of_not_mem :
    (preimageStrictTransformIndex pi_ Z L J').card = J'.card := by
  classical
  have h1 := card_image_of_injective (preimageStrictTransformIndex pi_ Z L J') $ strictTransformIndex_injective pi_ Z L
  rw [image_strictTransformIndex_preimageStrictTransformIndex pi_ Z L J' hnew] at h1
  exact sy_ h1
end

theorem card_preimageStrictTransformIndex_add_one_of_mem (hnew : exceptionalIndex pi_ Z L ∈ J') :
    (preimageStrictTransformIndex pi_ Z L J').card + 1 = J'.card := by
  classical
  have himg : (preimageStrictTransformIndex pi_ Z L J').image (strictTransformIndex pi_ Z L) = J'.erase (exceptionalIndex pi_ Z L) := by
    ext i
    simp [mem_image, mem_preimageStrictTransformIndex_iff, mem_erase]
    constructor
    rintro ⟨j, hj, rfl⟩
    refine ⟨?_, hj⟩
    intro hc
    have hval : ((strictTransformIndex pi_ Z L j : Fin (transformedBoundary pi_ Z L).length) : ℕ)
        = ((exceptionalIndex pi_ Z L : Fin (transformedBoundary pi_ Z L).length) : ℕ) := by rw [hc]
    rw [strictTransformIndex_val, exceptionalIndex_val] at hval
    exact absurd hval $ Nat.ne_of_lt j.isLt
    rintro ⟨hne, hi⟩
    rcases eq_exceptionalIndex_or_exists_strictTransformIndex pi_ Z L i with rfl | ⟨j, rfl⟩
    exact absurd rfl hne
    exact ⟨j, hi, rfl⟩
  have h1 := card_image_of_injective (preimageStrictTransformIndex pi_ Z L J') $ strictTransformIndex_injective pi_ Z L
  rw [himg, card_erase_of_mem hnew] at h1
  have h2 := card_pos.2 ⟨_, hnew⟩
  omega
end
end

theorem exists_orderAt_comap_eq_strictTransform_add_exceptional (hGeom : MonomialGeometryHypotheses)
    {T : MarkedIdealWithBoundary} (hT : IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    {X' : Sch} (pi_ : X' ⟶ scheme T) (q : X' ⟶ Sp T.base)
    (hq : Smooth q)
    (hpi_ : IsBlowupAlongIdealSheaf pi_ $ T.mc)
    (i : Fin T.boundary.length) (x' : ↥X') :
    ∃ ep_ : ℕ, (ep_ = 0 ∨ ep_ = 1) ∧
      (ep_ = 1 ↔ ∃ V : T.scheme.Opens, pi_ x' ∈ V ∧
        ((↑(T.mc).support : CSet T.scheme) ∩
            (V : CSet T.scheme)) ⊆ (↑(T.boundary.get i).support : CSet T.scheme)) ∧
      orderAt ((T.boundary.get i).comap pi_) x'
        = orderAt (strictTransform pi_ (T.mc)
            (T.boundary.get i)) x'
          + (ep_ : ENat) *
            orderAt (exceptionalIdeal pi_ $ T.mc) x' := by
  let _c0 := T.mc
  classical
  have : CharZero T.base := hT.valid.charZero
  have : Smooth q := hq
  have hmemL : T.boundary.get i ∈ tBd T := by simp
  obtain ⟨U', ep_, hx'U', hep01, hepiff, hfact⟩ :=
    hGeom.blowup_total_transform T hT.valid _c0
      (smooth_monomialCenter hGeom hT h) (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h) X' pi_ hpi_
      (T.boundary.get i) hmemL x'
  refine ⟨ep_, hep01, hepiff, ?_⟩
  have : Smooth U'.i := inferInstance
  let _a5 := opI U' ≫ q
  have : Smooth _a5 := inferInstance
  let _a0 := cmI (T.boundary.get i) pi_
  let _s0 := p6 pi_ _c0 $ T.boundary.get i
  let _a4 := orderAt (_s0.comap U'.i) ⟨x', hx'U'⟩
  have e2 : _a4
      = orderAt _s0 x' :=
    orderAt_comap T.base q U'.i
      _s0
      ⟨x', hx'U'⟩
  let _s1 := (p5 pi_ _c0).comap U'.i
  let _a1 := orderAt (p5 pi_ _c0) x'
  let _a6 := _s1 ^ ep_
  have hmul := orderAt_mul T.base _a5
      (_s0.comap U'.i)
      _a6
      ⟨x', hx'U'⟩
  have hpow := orderAt_pow T.base _a5
      _s1 ep_
      ⟨x', hx'U'⟩
  let _a2 := orderAt _a6 ⟨x', hx'U'⟩
  let _a3 := ep_
  have h4 : _a2
      = _a3 *
        _a1 :=
    hpow.trans $ congrArg (fun z : ENat => _a3 * z) $ orderAt_comap T.base q U'.i (p5 pi_ _c0) ⟨x', hx'U'⟩
  calc orderAt _a0 x'
      = orderAt (_a0.comap U'.i) ⟨x', hx'U'⟩ := sy_ $ orderAt_comap T.base q U'.i _a0 ⟨x', hx'U'⟩
    _ = orderAt (_s0.comap U'.i *
          _a6)
          ⟨x', hx'U'⟩ := by rw [hfact]
    _ = _a4
        + _a2 := hmul
    _ = orderAt _s0 x'
        + _a3 *
          _a1 := by
        rw [e2, h4]

theorem comap_foldr_mul {X Y : Sch} (f : Y ⟶ X) (l : Bdy X) :
    (l.foldr (· * ·) ⊤).comap f = (l.map fun A => A.comap f).foldr (· * ·) ⊤ := by
  induction l with
  | nil => simp
  | cons A l ih =>
    simp [foldr_cons, map_cons,
      comap_mul, ih]

section
variable (hGeom : MonomialGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : IsLocallyMonomialTriple T) (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) {X' : Sch} (pi_ : X' ⟶ scheme T) (q) (hpi_ : IsBlowupAlongIdealSheaf pi_ (T.mc)) (I') (hI' : (T.mc).comap pi_ ^ T.mult * I' = T.ideal.comap pi_) (hT' : IsLocallyMonomialTriple (blowupTriple T pi_ q I'))
include hGeom hT h hpi_ hI' hT'
theorem orderAlong_transform_add_mult_of_exceptionalIndex_mem
    {J' : Finset (Fin (transformedBoundary pi_ (T.mc)
      T.boundary).length)}
    (hJ' : exceptionalIndex pi_ (T.mc) T.boundary ∈ J')
    {C' : Set ↥X'}
    (hC' : C' ∈ intersectionComponents
      (transformedBoundary pi_ (T.mc) T.boundary) J')
    (U : T.scheme.Opens)
    (hU : pi_ (icGP hC') ∈ U)
    (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.i =
      (ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.i ^ a i).foldr (· * ·) ⊤)
    {C0_ : CSet T.scheme}
    (hC0_ : C0_ ∈ centerComponents T.ideal T.mult T.boundary)
    (hmem0_ : pi_ (icGP hC') ∈ C0_) :
    orderAlong I' C' + (mult T : ENat) =
      ((∑ i ∈ preimageStrictTransformIndex pi_ (T.mc) T.boundary J', a i : ℕ) : ENat)
        + orderAlong T.ideal C0_ := by
  let _c0 := ι (pre pi_ U) ≫ q
  classical
  have : CharZero T.base := hT.valid.charZero
  have : Smooth q := hT'.valid.smooth
  have hmemiff : ∀ i : Fin (transformedBoundary pi_
      (T.mc) T.boundary).length,
      (icGP hC' ∈
        ((transformedBoundary pi_ (T.mc)
          T.boundary).get i).support) ↔ i ∈ J' :=
    fun i => genericPoint_mem_support_iff_mem hGeom hT' hC' i
  have hEmem : (icGP hC') ∈
      support (exceptionalIdeal pi_ (T.mc)) := by
    have hx := (hmemiff (exceptionalIndex pi_ (T.mc) T.boundary)).2 hJ'
    rwa [get_transformedBoundary_exceptionalIndex] at hx
  have hstrictmem0 : exceptionalIdeal pi_ (T.mc)
      ∈ boundary (blowupTriple T pi_ q I') := by
    simp [blowupTriple_boundary]
    exact mem_append_right _ $ mem_singleton_self _
  have hEord : orderAt (exceptionalIdeal pi_ (T.mc))
      (icGP hC') = 1 :=
    hGeom.orderAt_boundary_eq_one (blowupTriple T pi_ q I') hT'.valid
      (exceptionalIdeal pi_ (T.mc)) hstrictmem0
      (icGP hC') hEmem
  have hZord := hEord
  rw [exceptionalIdeal_eq_comap] at hZord
  have h3 : orderAt (T.ideal.comap pi_) (icGP hC')
      = (mult T : ENat) + orderAt I' (icGP hC') := by
    rw [← hI', orderAt_mul T.base q, orderAt_pow T.base q, hZord, mul_one]
  have hmaxIdx : ∀ i ∈ lexMaxIndices T.ideal T.mult T.boundary,
      (support (T.mc) : CSet T.scheme)
        ⊆ (support (T.boundary.get i) : CSet T.scheme) := by
    intro i hi
    rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents]
    rintro y ⟨C, hCmem, hyC⟩
    exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT
      (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hCmem) i).2 hi hyC
  have hkeyc : ∀ i (V : T.scheme.Opens),
      pi_ (icGP hC') ∈ V →
      ((support (T.mc) : CSet T.scheme)
          ∩ (V : CSet T.scheme)) ⊆ (support (T.boundary.get i) : CSet T.scheme) →
      i ∈ lexMaxIndices T.ideal T.mult T.boundary := by
    intro i V hVmem hVsub
    have hC0comp_ : C0_ ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
      centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC0_
    have hC0Z : C0_ ⊆ (support (T.mc) : CSet T.scheme) := by
      rw [support_monomialCenter hGeom hT h, monomialCenterSet_eq_sUnion_centerComponents]
      intro y hy
      exact ⟨C0_, hC0_, hy⟩
    have hclosed : IsClosed (support (T.boundary.get i) : CSet T.scheme) :=
      (T.boundary.get i).support.2
    have hcl : closure (C0_ ∩ (V : CSet T.scheme))
        ⊆ (support (T.boundary.get i) : CSet T.scheme) :=
      closure_minimal (fun z hz => hVsub ⟨hC0Z hz.1, hz.2⟩) hclosed
    have hsub2 : C0_ ⊆ (support (T.boundary.get i) : CSet T.scheme) := by
      intro y hy
      refine hcl ?_
      rw [mem_closure_iff]
      intro W hW hyW
      obtain ⟨z, hzC, hzW, hzV⟩ :=
        (isIrreducible_of_mem_intersectionComponents hC0comp_).2 W (V : CSet T.scheme) hW V.isOpen ⟨y, hy, hyW⟩
          ⟨pi_ (icGP hC'), hmem0_, hVmem⟩
      exact ⟨z, hzW, hzC, hzV⟩
    exact (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC0comp_ i).1 hsub2
  have hxiU_ : (icGP hC') ∈ pre pi_ U := hU
  have hrestr : ∀ A : tISD T,
      (A.comap U.i).comap (pi_.mr U) = (A.comap pi_).comap (pre pi_ U).i := by
    intro A
    have h1 : A.comap ((pi_.mr U) ≫ ι U) = A.comap (ι (pre pi_ U) ≫ pi_) := by
      rw [morphismRestrict_ι]
    simpa only [comap_comp] using h1
  have hmon' : (T.ideal.comap pi_).comap (pre pi_ U).i
      = (ofFn fun i =>
          ((T.boundary.get i).comap pi_).comap (pre pi_ U).i ^ a i).foldr (· * ·) ⊤ := by
    rw [← hrestr T.ideal, hmon, comap_foldr_mul]
    congr 1
    rw [map_ofFn]
    refine congrArg ofFn $ funext fun i => ?_
    simp
    rw [comap_pow, hrestr]
  have : Smooth (pre pi_ U).i := inferInstance
  have : Smooth _c0 := inferInstance
  have e0 : orderAt ((T.ideal.comap pi_).comap (pre pi_ U).i)
      ⟨icGP hC', hxiU_⟩
      = orderAt (T.ideal.comap pi_) (icGP hC') :=
    orderAt_comap T.base q (pre pi_ U).i (T.ideal.comap pi_)
      ⟨icGP hC', hxiU_⟩
  have ecomap : ∀ i,
      orderAt (((T.boundary.get i).comap pi_).comap (pre pi_ U).i)
          ⟨icGP hC', hxiU_⟩
        = orderAt ((T.boundary.get i).comap pi_)
            (icGP hC') :=
    fun i => orderAt_comap T.base q (pre pi_ U).i ((T.boundary.get i).comap pi_)
      ⟨icGP hC', hxiU_⟩
  have e2 : orderAt ((T.ideal.comap pi_).comap (pre pi_ U).i)
      ⟨icGP hC', hxiU_⟩
      = ∑ i : Fin (bLen T),
          orderAt (((T.boundary.get i).comap pi_).comap (pre pi_ U).i ^ a i)
            ⟨icGP hC', hxiU_⟩ := by
    rw [hmon', orderAt_foldr_mul T.base _c0
      ⟨icGP hC', hxiU_⟩]
    simp [map_ofFn, sum_ofFn]
  have e3 : ∀ i,
      orderAt (((T.boundary.get i).comap pi_).comap (pre pi_ U).i ^ a i)
          ⟨icGP hC', hxiU_⟩
        = (a i : ENat) * orderAt ((T.boundary.get i).comap pi_)
            (icGP hC') := by
    intro i
    have hp := orderAt_pow T.base _c0
      (((T.boundary.get i).comap pi_).comap (pre pi_ U).i) (a i)
      ⟨icGP hC', hxiU_⟩
    exact tr_ hp $ congrArg (fun z => (a i : ENat) * z) (ecomap i)
  have h1 : orderAt (T.ideal.comap pi_) (icGP hC')
      = ∑ i : Fin (bLen T), (a i : ENat) *
          orderAt ((T.boundary.get i).comap pi_)
            (icGP hC') := by simp_all
  have hoi : ∀ i,
      orderAt ((T.boundary.get i).comap pi_)
          (icGP hC')
        = (((if strictTransformIndex pi_ (T.mc) T.boundary i ∈ J'
              then 1 else 0)
            + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0) : ℕ) : ENat) := by
    intro i
    obtain ⟨ep_, hep01, hepiff, hfact⟩ :=
      exists_orderAt_comap_eq_strictTransform_add_exceptional hGeom hT h pi_ q hT'.valid.smooth hpi_ i
        (icGP hC')
    have hstrictmem : strictTransform pi_ (T.mc)
        (T.boundary.get i) ∈ boundary (blowupTriple T pi_ q I') := by
      simp [blowupTriple_boundary]
      exact mem_append_left _
        (mem_map_of_mem
          (f := strictTransform pi_ (T.mc)) (by simp))
    let _s0 := strictTransform pi_ (T.mc) (T.boundary.get i)
    have hstrict : orderAt _s0 (icGP hC')
        = ((if strictTransformIndex pi_ (T.mc) T.boundary i ∈ J'
            then 1 else 0 : ℕ) : ENat) := by
      by_cases hi : strictTransformIndex pi_ (T.mc) T.boundary i ∈ J'
      have hmem := (hmemiff
        (strictTransformIndex pi_ (T.mc) T.boundary i)).2 hi
      rw [get_transformedBoundary_strictTransformIndex] at hmem
      have hone : orderAt _s0 (icGP hC') = 1 :=
        hGeom.orderAt_boundary_eq_one (blowupTriple T pi_ q I') hT'.valid _ hstrictmem _ hmem
      rw [hone]
      simp [hi]
      have hnot : (icGP hC') ∉
          support _s0 := by
        intro hc
        refine hi ((hmemiff
          (strictTransformIndex pi_ (T.mc) T.boundary i)).1 ?_)
        rwa [get_transformedBoundary_strictTransformIndex]
      rw [(orderAt_eq_zero_iff_not_mem_support _ _).2 hnot]
      simp [hi]
    have hepval : ep_ = (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0) := by
      by_cases hi : i ∈ lexMaxIndices T.ideal T.mult T.boundary
      rw [if_pos hi]
      exact hepiff.2 ⟨⊤, trivial, fun y hy => hmaxIdx i hi hy.1⟩
      rw [if_neg hi]
      rcases hep01 with h0 | h1
      exact h0
      exfalso
      obtain ⟨V, hVmem, hVsub⟩ := hepiff.1 h1
      exact hi $ hkeyc i V hVmem hVsub
    rw [hfact, hstrict, hEord, mul_one, hepval, cast_add]
  have hA : ∑ i : Fin (bLen T),
      a i * (if strictTransformIndex pi_ (T.mc) T.boundary i ∈ J'
        then 1 else 0 : ℕ)
      = ∑ i ∈ preimageStrictTransformIndex pi_ (T.mc) T.boundary J', a i := by
    simp [preimageStrictTransformIndex, mul_ite, mul_one, mul_zero, sum_filter]
  have hB : ∑ i : Fin (bLen T),
      a i * (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0 : ℕ)
      = ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by
    simp [mul_ite, mul_one, mul_zero, sum_ite_mem]
  have hnat : ∑ i : Fin (bLen T),
      a i * ((if strictTransformIndex pi_ (T.mc) T.boundary i ∈ J'
          then 1 else 0)
        + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0))
      = (∑ i ∈ preimageStrictTransformIndex pi_ (T.mc) T.boundary J', a i)
        + ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by
    calc ∑ i : Fin (bLen T),
        a i * ((if strictTransformIndex pi_ (T.mc) T.boundary i ∈ J'
            then 1 else 0)
          + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0))
        = ∑ i : Fin (bLen T),
            (a i * (if strictTransformIndex pi_ (T.mc) T.boundary i ∈ J'
              then 1 else 0)
              + a i * (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0)) :=
          sum_congr rfl fun i _ => mul_add _ _ _
      _ = (∑ i : Fin (bLen T),
            a i * (if strictTransformIndex pi_ (T.mc) T.boundary i ∈ J'
              then 1 else 0))
          + ∑ i : Fin (bLen T),
            a i * (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0) :=
          sum_add_distrib
      _ = (∑ i ∈ preimageStrictTransformIndex pi_ (T.mc) T.boundary J', a i)
          + ∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j := by rw [hA, hB]
  have ekey : ∑ i : Fin (bLen T), (a i : ENat) *
        orderAt ((T.boundary.get i).comap pi_)
          (icGP hC')
      = ((∑ i : Fin (bLen T),
          a i * ((if strictTransformIndex pi_ (T.mc) T.boundary i ∈ J'
              then 1 else 0)
            + (if i ∈ lexMaxIndices T.ideal T.mult T.boundary then 1 else 0)) : ℕ) : ENat) := by
    rw [cast_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [hoi i, cast_mul]
  have key : (mult T : ENat) + orderAt I' (icGP hC')
      = ((∑ i ∈ preimageStrictTransformIndex pi_ (T.mc) T.boundary J', a i : ℕ) : ENat)
        + ((∑ j ∈ lexMaxIndices T.ideal T.mult T.boundary, a j : ℕ) : ENat) := by
    rw [← h3, h1, ekey, hnat, cast_add]
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents I' hC', orderAlong_eq_sum_of_monomial hGeom hT (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC0_) hmem0_ U hU a hmon,
    add_comm (orderAt I' (icGP hC')) (mult T : ENat)]
  exact key

theorem exceptionalIndex_not_mem_of_orderAlong_eq_maxCandidateOrder
    (hr : minIndexCard I' T.mult
        (transformedBoundary pi_ (T.mc) T.boundary)
      = minIndexCard T.ideal T.mult T.boundary)
    (hv : maxCandidateOrder I' T.mult
        (transformedBoundary pi_ (T.mc) T.boundary)
      = maxCandidateOrder T.ideal T.mult T.boundary)
    {J' : Finset $ Fin (transformedBoundary pi_ (T.mc)
      T.boundary).length}
    {C' : Set ↥X'}
    (hcand : IsCandidateComponent I' T.mult
      (transformedBoundary pi_ (T.mc) T.boundary)
      (minIndexCard I' T.mult
        (transformedBoundary pi_ (T.mc) T.boundary)) J' C')
    (hordmax : orderAlong I' C'
      = maxCandidateOrder I' T.mult
        (transformedBoundary pi_ (T.mc) T.boundary)) :
    exceptionalIndex pi_ (T.mc) T.boundary ∉ J' := by
  let _c0 := T.mc
  classical
  intro hnew
  have hC'comp : C' ∈ intersectionComponents
      (transformedBoundary pi_ _c0 T.boundary) J' := by
    have hc := hcand
    unfold IsCandidateComponent at hc
    tauto
  have hmemiff : ∀ i : Fin (transformedBoundary pi_
      _c0 T.boundary).length,
      (icGP hC'comp ∈
        ((transformedBoundary pi_ _c0
          T.boundary).get i).support) ↔ i ∈ J' :=
    fun i => genericPoint_mem_support_iff_mem hGeom hT' hC'comp i
  have hEmem : (icGP hC'comp) ∈
      support (exceptionalIdeal pi_ _c0) := by
    have hx := (hmemiff $ exceptionalIndex pi_ _c0 T.boundary).2 hnew
    rwa [get_transformedBoundary_exceptionalIndex] at hx
  have hZmem := hEmem
  rw [exceptionalIdeal_eq_comap] at hZmem
  have hpiZ :=
    mp (mem_support_comap ..) hZmem
  obtain ⟨U, hU, a, hmon⟩ := hT.monomialNear _ $ support_monomialCenter_subset_orderAtLeastLocus hGeom hT h hpiZ
  have hpicenter : pi_ (icGP hC'comp) ∈
      monomialCenterSet T.ideal T.mult T.boundary := by
    rwa [← support_monomialCenter hGeom hT h]
  rw [monomialCenterSet_eq_sUnion_centerComponents] at hpicenter
  obtain ⟨C0_, hC0_, hmem0_⟩ := Set.mem_sUnion.1 hpicenter
  have hformula := orderAlong_transform_add_mult_of_exceptionalIndex_mem hGeom hT h pi_ q hpi_ I' hI' hT'
    hnew hC'comp U hU a hmon hC0_ hmem0_
  have hv0 :=
    ((mem_centerComponents_iff T.ideal T.mult T.boundary C0_).1 hC0_).2
  have hvU : orderAlong I' C' = maxCandidateOrder T.ideal T.mult T.boundary := by rw [hordmax, hv]
  rw [hvU, hv0] at hformula
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 $ ne_of_lt $ (maxCandidateOrder_spec hGeom hT h).2.2.2
  rw [← hN] at hformula
  have hnateq : N + tMu T
      = (∑ i ∈ preimageStrictTransformIndex pi_ _c0 T.boundary J', a i) + N := by
    exact_mod_cast hformula
  have hsumeq : (∑ i ∈ preimageStrictTransformIndex pi_ _c0 T.boundary J', a i)
      = tMu T := by omega
  have hmpos := hT.valid.one_le_mult
  have hcardpos :
      1 ≤ (preimageStrictTransformIndex pi_ _c0 T.boundary J').card := by
    rcases eq_empty_or_nonempty
        (preimageStrictTransformIndex pi_ _c0 T.boundary J') with he | hne
    simp_all
    exact card_pos.2 hne
  have hdiv : ∀ j ∈ preimageStrictTransformIndex pi_ _c0 T.boundary J',
      pi_ (icGP hC'comp) ∈ spI (T.boundary.get j) := by
    intro j hj
    have hj' :=
      (mem_preimageStrictTransformIndex_iff pi_ _c0 T.boundary J' j).1 hj
    have hmem := (hmemiff
      (strictTransformIndex pi_ _c0 T.boundary j)).2 hj'
    rw [get_transformedBoundary_strictTransformIndex] at hmem
    obtain ⟨ep_, hep01, hepiff, hfact⟩ :=
      exists_orderAt_comap_eq_strictTransform_add_exceptional hGeom hT h pi_ q hT'.valid.smooth hpi_ j
        (icGP hC'comp)
    have h1 :=
      (one_le_orderAt_iff_mem_support _ _).2 hmem
    have h2 : 1 ≤ orderAt (cmI (T.boundary.get j) pi_)
        (icGP hC'comp) := by
      rw [hfact]
      exact le_trans h1 le_self_add
    have h3 :=
      (one_le_orderAt_iff_mem_support _ _).1 h2
    exact mp_ (mem_support_comap ..) h3
  have hsupp :=
    mem_support_intersectionIdeal T.boundary
      (preimageStrictTransformIndex pi_ _c0 T.boundary J') _ hdiv
  obtain ⟨C1_, hxC1, hcomp1_⟩ := exists_isIrreducibleComponentOf_mem
    ((intersectionIdeal T.boundary
      (preimageStrictTransformIndex pi_ _c0 T.boundary J')).support :
        CSet T.scheme) _ hsupp
  have hC1 :=
    (mem_intersectionComponents_iff _ _ _).2 hcomp1_
  have hord1_ :=
    orderAlong_eq_sum_of_monomial hGeom hT hC1 hxC1 U hU a hmon
  have hcand1 : IsCandidateComponent T.ideal T.mult T.boundary
      (preimageStrictTransformIndex pi_ _c0 T.boundary J').card
      (preimageStrictTransformIndex pi_ _c0 T.boundary J') C1_ := by
    unfold IsCandidateComponent
    refine ⟨rfl, hC1, ?_⟩
    rw [hord1_, hsumeq]
  have hle := (minIndexCard_spec T.ideal T.mult T.boundary ⟨_, hcardpos, _, _, hcand1⟩).2.2 _ hcardpos _ _ hcand1
  have hcardJ' : J'.card = minIndexCard I' T.mult
      (transformedBoundary pi_ _c0 T.boundary) := by
    have hc := hcand
    unfold IsCandidateComponent at hc
    exact hc.1
  have hcard2 :=
    card_preimageStrictTransformIndex_add_one_of_mem pi_ _c0 T.boundary J' hnew
  rw [hr] at hcardJ'
  omega

theorem maxOrderCandidatePairs_ncard_lt_of_blowup
    (_h' : minIndexCard I' T.mult
      (transformedBoundary pi_ (T.mc) T.boundary) ≠ 0)
    (hr : minIndexCard I' T.mult
        (transformedBoundary pi_ (T.mc) T.boundary)
      = minIndexCard T.ideal T.mult T.boundary)
    (hv : maxCandidateOrder I' T.mult
        (transformedBoundary pi_ (T.mc) T.boundary)
      = maxCandidateOrder T.ideal T.mult T.boundary) :
    (maxOrderCandidatePairs I' T.mult
        (transformedBoundary pi_ (T.mc) T.boundary)).ncard
      < (maxOrderCandidatePairs T.ideal T.mult T.boundary).ncard := by
  let _c0 := T.mc
  classical
  have : CharZero T.base := hT.valid.charZero
  have : Smooth q := hT'.valid.smooth
  have hbest := (lexMaxIndices_spec hGeom hT h).1
  unfold IsMaxOrderIndexSet at hbest
  obtain ⟨C0_, hcand0, hord0⟩ := hbest
  let _a1 := centerComponents T.ideal T.mult T.boundary
  have hC0opt : C0_ ∈ _a1 :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C0_).2 ⟨hcand0, hord0⟩
  let _a2 := lexMaxIndices T.ideal T.mult T.boundary
  let _a3 := maxOrderCandidatePairs T.ideal T.mult T.boundary
  have hp0_ : (_a2, C0_)
      ∈ _a3 :=
    (mem_maxOrderCandidatePairs_iff T.ideal T.mult T.boundary _).2 ⟨hcand0, hord0⟩
  let _a5 := isOpen_preimage_sUnion_centerComponents hGeom hT
  have hpi' : p15 pi_ $ componentUnionIdeal T.boundary _a2
      _a1
      _a5 := by
    rwa [← monomialCenter_eq_componentUnionIdeal hGeom hT h]
  have htc := hGeom.transformed_components T hT.valid
    _a2
    _a1
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)
    _a5 X' pi_ hpi'
  rw [← monomialCenter_eq_componentUnionIdeal hGeom hT h] at htc
  let _a0 := transformedBoundary pi_ _c0 T.boundary
  let _a4 := maxOrderCandidatePairs I' T.mult _a0
  have hkey : ∀ p ∈ _a4,
      ((preimageStrictTransformIndex pi_ _c0 T.boundary p.1,
          closure $ pi_ '' p.2) ∈ _a3) ∧
        closure (pi_ '' p.2) ∉ _a1 ∧
        exceptionalIndex pi_ _c0 T.boundary ∉ p.1 ∧
        p.2 = closure ((pi_ ⁻¹' closure (pi_ '' p.2)) \
          (support (p5 pi_ _c0) :
            Set X')) := by
    intro p hp
    obtain ⟨hcand, hordmax⟩ := (mem_maxOrderCandidatePairs_iff I' T.mult
      _a0 p).1 hp
    have hnew := exceptionalIndex_not_mem_of_orderAlong_eq_maxCandidateOrder hGeom hT h pi_ q hpi_ I' hI' hT' hr hv
      hcand hordmax
    have hC'comp : p.2 ∈ intersectionComponents
        _a0 p.1 := by
      have hc := hcand
      unfold IsCandidateComponent at hc
      tauto
    have hC'img : p.2 ∈ intersectionComponents
        _a0
        ((preimageStrictTransformIndex pi_ _c0 T.boundary p.1).image
          (strictTransformIndex pi_ _c0 T.boundary)) := by
      rw [image_strictTransformIndex_preimageStrictTransformIndex pi_ _c0 T.boundary p.1
        hnew]
      exact hC'comp
    have hgen :=
      isGenericPoint_genericPoint_of_mem_intersectionComponents hC'img
    obtain ⟨hoff, C, hC, hCnot, hC'eq, hlast⟩ :=
      htc (preimageStrictTransformIndex pi_ _c0 T.boundary p.1) p.2 hC'img _ hgen
    have hgpC :=
      isGenericPoint_genericPoint_of_mem_intersectionComponents hC
    have hclim : closure (pi_ '' p.2) = C := by
      rw [closure_image_genericPoint (f := pi_) pi_.continuous hgen, hlast _ hgpC, hgpC]
    have hcl2 : closure (pi_ '' p.2) = closure C := by
      rw [hclim, (isClosed_intersectionComponents_of_mem hC).closure_eq]
    have hordeq : orderAlong I' p.2 = orderAlong T.ideal C := by
      rw [orderAlong_transform_eq_of_genericPoint_not_mem_exceptional hGeom hT h pi_ hpi_ I' hI' hC'img hoff]
      exact orderAlong_eq_of_closure_eq T.ideal ((isIrreducible_of_mem_intersectionComponents hC'img).image _ pi_.continuous.continuousOn) (isIrreducible_of_mem_intersectionComponents hC) hcl2
    have hordC : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by
      rw [← hordeq, hordmax, hv]
    refine ⟨?_, ?_, hnew, ?_⟩
    refine (mem_maxOrderCandidatePairs_iff T.ideal T.mult T.boundary _).2 ⟨?_, ?_⟩
    unfold IsCandidateComponent
    refine ⟨?_, ?_, ?_⟩
    rw [card_preimageStrictTransformIndex_of_not_mem pi_ _c0
      T.boundary p.1 hnew]
    have hc := hcand
    unfold IsCandidateComponent at hc
    rwa [hc.1]
    rwa [hclim]
    rw [hclim, hordC]
    exact (maxCandidateOrder_spec hGeom hT h).2.2.1
    rw [hclim, hordC]
    rwa [hclim]
    rwa [hclim]
  have hinj : InjOn
      (fun p : FinSet _a0.length × Set X' =>
        (preimageStrictTransformIndex pi_ _c0 T.boundary p.1,
          closure $ pi_ '' p.2))
      _a4 := by
    intro p hp p' hp' heq
    obtain ⟨-, -, hnew1, hrep1⟩ := hkey p hp
    obtain ⟨-, -, hnew2, hrep2⟩ := hkey p' hp'
    have hJ : preimageStrictTransformIndex pi_ _c0 T.boundary p.1
        = preimageStrictTransformIndex pi_ _c0 T.boundary p'.1 :=
      congrArg Prod.fst heq
    have hC : closure (pi_ '' p.2) = closure (pi_ '' p'.2) := congrArg Prod.snd heq
    have hfst : p.1 = p'.1 := by
      rw [← image_strictTransformIndex_preimageStrictTransformIndex pi_ _c0 T.boundary p.1
          hnew1,
        ← image_strictTransformIndex_preimageStrictTransformIndex pi_ _c0 T.boundary p'.1
          hnew2,
        hJ]
    have hsnd : p.2 = p'.2 := by
      rw [hrep1, hC]
      exact sy_ hrep2
    exact Prod.ext hfst hsnd
  have himg : (fun p : FinSet _a0.length × Set X' =>
      (preimageStrictTransformIndex pi_ _c0 T.boundary p.1,
        closure $ pi_ '' p.2)) ''
      _a4
      ⊆ _a3 := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hkey p hp).1
  have hnotin : (_a2, C0_) ∉
      (fun p : FinSet _a0.length × Set X' =>
        (preimageStrictTransformIndex pi_ _c0 T.boundary p.1,
          closure $ pi_ '' p.2)) ''
      _a4 := by
    rintro ⟨p, hp, heq⟩
    have hsnd : closure (pi_ '' p.2) = C0_ := congrArg Prod.snd heq
    refine (hkey p hp).2.1 ?_
    rwa [hsnd]
  have hss : (fun p : FinSet _a0.length × Set X' =>
      (preimageStrictTransformIndex pi_ _c0 T.boundary p.1,
        closure $ pi_ '' p.2)) ''
      _a4
      ⊂ _a3 := by
    refine Set.ssubset_iff_subset_ne.2 ⟨himg, ?_⟩
    intro hEq
    apply hnotin
    rwa [hEq]
  have hlt := ncard_lt_ncard hss $ finite_maxOrderCandidatePairs hGeom hT
  rwa [Set.InjOn.ncard_image hinj] at hlt
end




namespace MonomialCenter

structure OrderedMatchingOfNonTop {Y : Sch} (L L' : Bdy Y) where
  size : ℕ
  toFirst : Fin size → Fin L.length
  toSecond : Fin size → Fin L'.length
  strictMono_toFirst : StrictMono toFirst
  strictMono_toSecond : StrictMono toSecond
  get_eq : ∀ a : Fin size, get L (toFirst a) = get L' (toSecond a)
  exists_toFirst : ∀ i : Fin L.length, get L i ≠ ⊤ → ∃ a : Fin size, toFirst a = i
  exists_toSecond : ∀ i : Fin L'.length, get L' i ≠ ⊤ → ∃ a : Fin size, toSecond a = i

namespace OrderedMatchingOfNonTop

section
variable {Y : Sch} {L L' : Bdy Y} (h : OrderedMatchingOfNonTop L L')
def symm :
    OrderedMatchingOfNonTop L' L where
  size := h.size
  toFirst := h.toSecond
  toSecond := h.toFirst
  strictMono_toFirst := h.strictMono_toSecond
  strictMono_toSecond := h.strictMono_toFirst
  get_eq := fun a => (h.get_eq a).symm
  exists_toFirst := h.exists_toSecond
  exists_toSecond := h.exists_toFirst

section
variable (J : FinSet L.length)
def preimage : FinSet h.size :=
  Finset.filter (fun a => h.toFirst a ∈ J) univ

def transport : FinSet L'.length :=
  image h.toSecond $ h.preimage J

theorem mem_preimage (a : Fin h.size) :
    a ∈ h.preimage J ↔ h.toFirst a ∈ J := by
  constructor
  intro ha
  exact (mem_filter.1 ha).2
  intro ha
  exact mem_filter.2 ⟨mem_univ a, ha⟩

theorem mem_transport i :
    i ∈ h.transport J ↔ ∃ a, h.toSecond a = i ∧ h.toFirst a ∈ J := by
  constructor
  intro hi
  rcases Finset.mem_image.1 hi with ⟨a, ha, hai⟩
  exact ⟨a, hai, (h.mem_preimage J a).1 ha⟩
  rintro ⟨a, hai, haJ⟩
  exact Finset.mem_image.2 ⟨a, (h.mem_preimage J a).2 haJ, hai⟩
end

theorem symm_symm :
    h.symm.symm = h := rfl
end

end OrderedMatchingOfNonTop

section
variable {Y : Sch}
section
variable (L : Bdy Y)
def orderedMatchingOfNonTopRefl : OrderedMatchingOfNonTop L L where
  size := length L
  toFirst := id
  toSecond := id
  strictMono_toFirst := strictMono_id
  strictMono_toSecond := strictMono_id
  get_eq := fun _ => rfl
  exists_toFirst := fun i _ => ⟨i, rfl⟩
  exists_toSecond := fun i _ => ⟨i, rfl⟩

theorem sameNontrivialBoundary_refl :
    SameNontrivialBoundary L L :=
  refl L
end

theorem openSublocusIdeal_congr {M M' : ISD Y} {S S' : Set ↥Y}
    (hM : M = M') (hS : S = S')
    (h : IsOpen $ ⇑M.si ⁻¹' S) (h' : IsOpen $ ⇑M'.si ⁻¹' S') :
    openSublocusIdeal M.si (⇑M.si ⁻¹' S) h
      = openSublocusIdeal M'.si (⇑M'.si ⁻¹' S') h' := by
  subst hM
  subst hS
  rfl

section
variable (I : ISD Y) (m : ℕ) (L : Bdy Y)
theorem card_eq_minIndexCard_of_isMaxOrderIndexSet__b9 {J : FinSet L.length} (hJ : IsMaxOrderIndexSet I m L J) :
    J.card = minIndexCard I m L := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hc, -⟩ := hJ
  unfold IsCandidateComponent at hc
  exact an1 hc

theorem isMaxOrderIndexSet_lexMaxIndices (hex : ∃ J : FinSet L.length, IsMaxOrderIndexSet I m L J) :
    IsMaxOrderIndexSet I m L (lexMaxIndices I m L) ∧
      ∀ K, IsMaxOrderIndexSet I m L K →
        binaryEncode K ≤ binaryEncode (lexMaxIndices I m L) := by
  have hne : ({c : ℕ | ∃ J, IsMaxOrderIndexSet I m L J ∧
      binaryEncode J = c}).Nonempty := by
    obtain ⟨J, hJ⟩ := hex
    exact ⟨binaryEncode J, J, hJ, rfl⟩
  have hbdd : BddAbove {c : ℕ | ∃ J, IsMaxOrderIndexSet I m L J ∧
      binaryEncode J = c} := by
    refine ⟨∑ j : Fin L.length, 2 ^ (lenL L - 1 - j), ?_⟩
    rintro c ⟨J, -, rfl⟩
    unfold binaryEncode
    exact sum_le_sum_of_subset $ subset_univ J
  have hmem : maxBinaryCode I m L ∈ {c : ℕ | ∃ J, IsMaxOrderIndexSet I m L J ∧
      binaryEncode J = c} := by
    unfold maxBinaryCode
    exact sSup_mem hne hbdd
  obtain ⟨J0_, hJ0_, hcode⟩ := hmem
  have hdite : ∃ J, IsMaxOrderIndexSet I m L J ∧ binaryEncode J = maxBinaryCode I m L :=
    ⟨J0_, hJ0_, hcode⟩
  have hch : lexMaxIndices I m L = hdite.choose := by
    unfold lexMaxIndices
    exact dif_pos hdite
  have hspec := hdite.choose_spec
  rw [← hch] at hspec
  refine ⟨an1 hspec, fun K hK => ?_⟩
  rw [an2 hspec]
  unfold maxBinaryCode
  exact le_csSup hbdd ⟨K, hK, rfl⟩

theorem lexMaxIndices_eq_of_binaryEncode_le {J} (hJ : IsMaxOrderIndexSet I m L J)
    (hmax : ∀ K : FinSet L.length, IsMaxOrderIndexSet I m L K → binaryEncode K ≤ binaryEncode J) :
    lexMaxIndices I m L = J := by
  obtain ⟨hb, hub⟩ := isMaxOrderIndexSet_lexMaxIndices I m L ⟨J, hJ⟩
  exact binaryEncode_injective $ le_antisymm (hmax _ hb) $ hub J hJ

theorem lexMaxIndices_eq_empty (hex : ¬ ∃ J : FinSet L.length, IsMaxOrderIndexSet I m L J) :
    lexMaxIndices I m L = ∅ := by
  have hno : ¬ ∃ J, IsMaxOrderIndexSet I m L J ∧ binaryEncode J = maxBinaryCode I m L := by simp_all
  unfold lexMaxIndices
  exact dif_neg hno
end

section
variable {L L' : Bdy Y}
section
variable (rel : OrderedMatchingOfNonTop L L')
section
variable (J : FinSet L.length) (hgood : ∀ j ∈ J, get L j ≠ ⊤)
include hgood
theorem intersectionIdeal_transport :
    intersectionIdeal L J = intersectionIdeal L' (rel.transport J) := by
  rw [intersectionIdeal_eq_iSup, intersectionIdeal_eq_iSup]
  apply le_antisymm
  refine iSup₂_le fun j hj => ?_
  obtain ⟨a, ha⟩ := rel.exists_toFirst j $ hgood j hj
  have hmem :=
    (rel.mem_transport J _).2 ⟨a, rfl, by rw [ha]; exact hj⟩
  have h1 : get L j = get L' (rel.toSecond a) := by
    rw [← ha]
    exact rel.get_eq a
  rw [h1]
  exact le_iSup₂ (f := fun i (_ : i ∈ rel.transport J) => get L' i)
    (rel.toSecond a) hmem
  refine iSup₂_le fun i hi => ?_
  obtain ⟨a, hai, haJ⟩ := (rel.mem_transport J i).1 hi
  have h1 : get L' i = get L (rel.toFirst a) := by
    rw [← hai]
    exact sy_ $ rel.get_eq a
  rw [h1]
  exact le_iSup₂ (f := fun j (_ : j ∈ J) => get L j) (rel.toFirst a) haJ

theorem image_toFirst_preimage :
    image rel.toFirst (rel.preimage J) = J := by
  ext j
  constructor
  intro hj
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
  exact (rel.mem_preimage J a).1 ha
  intro hj
  obtain ⟨a, ha⟩ := rel.exists_toFirst j $ hgood j hj
  refine Finset.mem_image.2 ⟨a, ?_, ha⟩
  exact (rel.mem_preimage J a).2 (by rw [ha]; exact hj)

theorem card_transport :
    (rel.transport J).card = J.card := by
  have h1 : (rel.transport J).card = (rel.preimage J).card :=
    card_image_of_injective _ rel.strictMono_toSecond.injective
  have h2 : (image rel.toFirst $ rel.preimage J).card = (rel.preimage J).card :=
    card_image_of_injective _ rel.strictMono_toFirst.injective
  rw [image_toFirst_preimage rel J hgood] at h2
  rw [h1, ← h2]
end

theorem transport_symm_transport (K : FinSet L'.length) (hK : ∀ i ∈ K, get L' i ≠ ⊤) :
    rel.transport (rel.symm.transport K) = K := by
  ext i
  constructor
  intro hi
  obtain ⟨a, hai, haK⟩ := (rel.mem_transport _ i).1 hi
  obtain ⟨b, hb1, hb2⟩ := (OrderedMatchingOfNonTop.mem_transport rel.symm K $ rel.toFirst a).1 haK
  have hba := rel.strictMono_toFirst.injective hb1
  subst hba
  rwa [← hai]
  intro hi
  obtain ⟨a, ha⟩ := rel.exists_toSecond i $ hK i hi
  refine (rel.mem_transport _ i).2 ⟨a, ha, ?_⟩
  refine (OrderedMatchingOfNonTop.mem_transport rel.symm K $ rel.toFirst a).2 ⟨a, rfl, ?_⟩
  show rel.toSecond a ∈ K
  rwa [ha]

def orderedMatchingOfNonTopConsTopLeft : OrderedMatchingOfNonTop ((⊤ : ISD Y) :: L) L' where
  size := rel.size
  toFirst := fun a => (rel.toFirst a).succ
  toSecond := rel.toSecond
  strictMono_toFirst := fun a b hab => succ_lt_succ_iff.2 $ rel.strictMono_toFirst hab
  strictMono_toSecond := rel.strictMono_toSecond
  get_eq := fun a => rel.get_eq a
  exists_toFirst := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro h0
      exact absurd rfl h0
    · intro j hj
      obtain ⟨a, ha⟩ := rel.exists_toFirst j hj
      exact ⟨a, by rw [ha]⟩
  exists_toSecond := rel.exists_toSecond

def orderedMatchingOfNonTopConsTopRight : OrderedMatchingOfNonTop L ((⊤ : ISD Y) :: L') :=
  (orderedMatchingOfNonTopConsTopLeft rel.symm).symm
end

def orderedMatchingOfNonTopCons (D : ISD Y)
    (rel : OrderedMatchingOfNonTop L L') : OrderedMatchingOfNonTop (D :: L) (D :: L') where
  size := rel.size + 1
  toFirst := Fin.cases 0 fun b => (rel.toFirst b).succ
  toSecond := Fin.cases 0 fun b => (rel.toSecond b).succ
  strictMono_toFirst := by
    intro a b hab
    rcases eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
    · rcases eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · exact absurd hab $ lt_irrefl _
      · simp only [cases_zero, cases_succ]
        exact succ_pos _
    · rcases eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · simp at hab
      · simp only [cases_succ]
        exact succ_lt_succ_iff.2 $ rel.strictMono_toFirst $ succ_lt_succ_iff.1 hab
  strictMono_toSecond := by
    intro a b hab
    rcases eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
    · rcases eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · exact absurd hab $ lt_irrefl _
      · simp only [cases_zero, cases_succ]
        exact succ_pos _
    · rcases eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · simp at hab
      · simp only [cases_succ]
        exact succ_lt_succ_iff.2 $ rel.strictMono_toSecond $ succ_lt_succ_iff.1 hab
  get_eq := by
    intro a
    rcases eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
    · rfl
    · simp only [cases_succ]
      exact rel.get_eq a'
  exists_toFirst := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro _
      exact ⟨0, rfl⟩
    · intro j hj
      obtain ⟨a, ha⟩ := rel.exists_toFirst j hj
      refine ⟨a.succ, ?_⟩
      simp only [cases_succ]
      rw [ha]
  exists_toSecond := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro _
      exact ⟨0, rfl⟩
    · intro j hj
      obtain ⟨a, ha⟩ := rel.exists_toSecond j hj
      refine ⟨a.succ, ?_⟩
      simp only [cases_succ]
      rw [ha]
end

theorem sameNontrivialBoundary_append {L1_ L1' L2_ L2' : Bdy Y}
    (h1_ : SameNontrivialBoundary L1_ L1') (h2_ : SameNontrivialBoundary L2_ L2') :
    SameNontrivialBoundary (L1_ ++ L2_) $ L1' ++ L2' :=
  h1_.append h2_

theorem nonempty_orderedMatchingOfNonTop_of_length_add_le n :
    ∀ L L' : Bdy Y, length L + length L' ≤ n →
      nontrivialPart L = nontrivialPart L' →
      Nonempty (OrderedMatchingOfNonTop L L') := by
  induction n with
  | zero =>
      intro L L' hlen _
      cases L with
      | cons _ _ =>
          simp only [length_cons] at hlen
          omega
      | nil =>
          cases L' with
          | cons _ _ =>
              simp only [length_cons, length_nil] at hlen
              omega
          | nil => exact ⟨orderedMatchingOfNonTopRefl []⟩
  | succ n ih =>
      intro L L' hlen hfil
      cases L with
      | nil =>
          cases L' with
          | nil => exact ⟨orderedMatchingOfNonTopRefl []⟩
          | cons D' t' =>
              by_cases hD' : D' = ⊤
              subst hD'
              have hlen' : lenL ([] : Bdy Y) + lenL t' ≤ n := by simp_all
              have hfil' : nontrivialPart ([])
                  = nontrivialPart t' := by
                simpa [nontrivialPart] using hfil
              obtain ⟨r⟩ := ih [] t' hlen' hfil'
              exact ⟨orderedMatchingOfNonTopConsTopRight r⟩
              exfalso
              simp [nontrivialPart, hD'] at hfil
      | cons D t =>
          by_cases hD : D = ⊤
          subst hD
          have hlen' : length t + length L' ≤ n := by
            simp only [length_cons] at hlen
            omega
          have hfil' : nontrivialPart t = nontrivialPart L' := by
            simpa [nontrivialPart] using hfil
          obtain ⟨r⟩ := ih t L' hlen' hfil'
          exact ⟨orderedMatchingOfNonTopConsTopLeft r⟩
          cases L' with
          | nil =>
              exfalso
              simp [nontrivialPart, hD] at hfil
          | cons D' t' =>
              by_cases hD' : D' = ⊤
              subst hD'
              have hlen' : length (D :: t) + length t' ≤ n := by
                simp only [length_cons] at hlen ⊢
                omega
              have hfil' : nontrivialPart (D :: t)
                  = nontrivialPart t' := by
                simpa [nontrivialPart, hD] using hfil
              obtain ⟨r⟩ := ih (D :: t) t' hlen' hfil'
              exact ⟨orderedMatchingOfNonTopConsTopRight r⟩
              have hcons : D = D' ∧ nontrivialPart t
                  = nontrivialPart t' := by
                simpa [nontrivialPart, hD, hD'] using hfil
              obtain ⟨rfl, hfil'⟩ := hcons
              have hlen' : length t + length t' ≤ n := by
                simp only [length_cons] at hlen
                omega
              obtain ⟨r⟩ := ih t t' hlen' hfil'
              exact ⟨orderedMatchingOfNonTopCons _ r⟩

theorem nonempty_orderedMatchingOfNonTop {L L' : Bdy Y}
    (h : SameNontrivialBoundary L L') : Nonempty $ OrderedMatchingOfNonTop L L' := by
  rw [sameNontrivialBoundary_iff] at h
  exact nonempty_orderedMatchingOfNonTop_of_length_add_le (lenL L + lenL L') L L' le_rfl h

theorem get_ne_top_of_mem_intersectionComponents {L : Bdy Y}
    {J} {C} (hC : C ∈ intersectionComponents L J) :
    ∀ j ∈ J, get L j ≠ ⊤ := by
  intro j hj hg
  have h1 : intersectionIdeal L J = ⊤ := by
    rw [intersectionIdeal_eq_iSup]
    refine mp_ top_le_iff ?_
    have h2 :=
      le_iSup₂ (f := fun j' (_ : j' ∈ J) => get L j') j hj
    rwa [hg] at h2
  have h2 : C ⊆ (support (intersectionIdeal L J) : Set Y) := by
    simp only [intersectionComponents, mem_ofPred_eq] at hC
    exact hC.2.1
  rw [h1, (eq_top_iff_support_eq_empty
    (⊤)).1 rfl] at h2
  exact (isIrreducible_of_mem_intersectionComponents hC).1.ne_empty $ subset_empty_iff.1 h2

section
variable {L L' : Bdy Y} (rel : OrderedMatchingOfNonTop L L')
include rel
theorem isCandidateComponent_transport {I : ISD Y} {m r : ℕ} {J : FinSet L.length}
    {C : Set ↥Y} (hc : IsCandidateComponent I m L r J C) : IsCandidateComponent I m L' r (rel.transport J) C := by
  unfold IsCandidateComponent at hc ⊢
  obtain ⟨hcard, hC, horder⟩ := hc
  have hgood := get_ne_top_of_mem_intersectionComponents hC
  refine ⟨?_, ?_, horder⟩
  rwa [card_transport rel J hgood]
  have _i9 : intersectionComponents L J = intersectionComponents L' (rel.transport J) := by
    unfold intersectionComponents
    rw [intersectionIdeal_transport rel J hgood]
  rwa [← _i9]

section
variable (I : ISD Y)
theorem minIndexCard_eq_of_orderedMatchingOfNonTop (m : ℕ) :
    minIndexCard I m L = minIndexCard I m L' := by
  have hsets : {r : ℕ | 1 ≤ r ∧ ∃ J C,
        IsCandidateComponent I m L r J C}
      = {r : ℕ | 1 ≤ r ∧ ∃ J C,
        IsCandidateComponent I m L' r J C} := by
    ext r
    simp only [mem_ofPred_eq]
    constructor
    rintro ⟨hr, J, C, hc⟩
    exact ⟨hr, rel.transport J, C, isCandidateComponent_transport rel hc⟩
    rintro ⟨hr, J, C, hc⟩
    exact ⟨hr, rel.symm.transport J, C, isCandidateComponent_transport rel.symm hc⟩
  unfold minIndexCard
  exact congrArg sInf hsets

theorem iSup_orderAlong_le_of_orderedMatchingOfNonTop m r :
    (⨆ (J : FinSet L.length) (C : Set ↥Y) (_ : IsCandidateComponent I m L r J C), orderAlong I C) ≤
      ⨆ (J : FinSet L'.length) (C : Set ↥Y) (_ : IsCandidateComponent I m L' r J C),
        orderAlong I C := by
  exact iSup_le fun J => iSup_le fun C => iSup_le fun hc => le_iSup_of_le (rel.transport J) $ le_iSup_of_le C $ le_iSup_of_le (isCandidateComponent_transport rel hc) le_rfl

theorem maxCandidateOrder_eq_of_orderedMatchingOfNonTop (m : ℕ) :
    maxCandidateOrder I m L = maxCandidateOrder I m L' := by
  unfold maxCandidateOrder
  rw [minIndexCard_eq_of_orderedMatchingOfNonTop rel I m]
  exact le_antisymm (iSup_orderAlong_le_of_orderedMatchingOfNonTop rel I m _) $ iSup_orderAlong_le_of_orderedMatchingOfNonTop rel.symm I m _

theorem isMaxOrderIndexSet_transport m {J}
    (hJ : IsMaxOrderIndexSet I m L J) : IsMaxOrderIndexSet I m L' $ rel.transport J := by
  unfold IsMaxOrderIndexSet at hJ ⊢
  obtain ⟨C, hc, hord⟩ := hJ
  refine ⟨C, ?_, ?_⟩
  rw [← minIndexCard_eq_of_orderedMatchingOfNonTop rel I m]
  exact isCandidateComponent_transport rel hc
  rw [hord]
  exact maxCandidateOrder_eq_of_orderedMatchingOfNonTop rel I m
end
end

section
variable (I : ISD Y) (m : ℕ)
theorem get_ne_top_of_isMaxOrderIndexSet
    (L : Bdy Y) {J} (hJ : IsMaxOrderIndexSet I m L J) :
    ∀ j ∈ J, get L j ≠ ⊤ := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hc, -⟩ := hJ
  unfold IsCandidateComponent at hc
  exact get_ne_top_of_mem_intersectionComponents hc.2.1

theorem get_ne_top_of_mem_lexMaxIndices
    (L : Bdy Y) : ∀ j ∈ lexMaxIndices I m L, get L j ≠ ⊤ := by
  by_cases hex : ∃ J, IsMaxOrderIndexSet I m L J
  exact get_ne_top_of_isMaxOrderIndexSet I m L (isMaxOrderIndexSet_lexMaxIndices I m L hex).1
  rw [lexMaxIndices_eq_empty I m L hex]
  intro j hj
  exact absurd hj $ by simp

theorem minIndexCard_eq_of_sameNontrivialBoundary
    {L L'} (h : SameNontrivialBoundary L L') :
    minIndexCard I m L = minIndexCard I m L' := by
  obtain ⟨rel⟩ := nonempty_orderedMatchingOfNonTop h
  exact minIndexCard_eq_of_orderedMatchingOfNonTop rel I m
end

section
variable {L L'} (rel : OrderedMatchingOfNonTop L L') (I : ISD Y) (m : ℕ)
include rel
theorem lexMaxIndices_transport :
    lexMaxIndices I m L' = rel.transport (lexMaxIndices I m L) := by
  by_cases hex : ∃ J, IsMaxOrderIndexSet I m L J
  obtain ⟨hbest, hub⟩ := isMaxOrderIndexSet_lexMaxIndices I m L hex
  refine lexMaxIndices_eq_of_binaryEncode_le I m L' (isMaxOrderIndexSet_transport rel I m hbest) ?_
  intro K hK
  have hK0 := isMaxOrderIndexSet_transport rel.symm I m hK
  have hKeq :=
    transport_symm_transport rel K $ get_ne_top_of_isMaxOrderIndexSet I m L' hK
  let _a0 := lexMaxIndices I m L
  have hcard : (rel.symm.transport K).card = _a0.card := by
    rw [card_eq_minIndexCard_of_isMaxOrderIndexSet__b9 I m L hK0, card_eq_minIndexCard_of_isMaxOrderIndexSet__b9 I m L hbest]
  have hlt : binaryEncode (rel.transport _a0) < binaryEncode (rel.transport $ rel.symm.transport K) ↔ binaryEncode _a0 < binaryEncode (rel.symm.transport K) := by
    let J := rel.symm.transport K
    let K := _a0
    let hJ := get_ne_top_of_isMaxOrderIndexSet I m L hK0
    let hK := get_ne_top_of_isMaxOrderIndexSet I m L hbest
    have hcardT := hcard
    rw [← card_transport rel K hK, ← card_transport rel J hJ] at hcardT
    have htJ : rel.transport J = image rel.toSecond (rel.preimage J) := rfl
    have htK : rel.transport K = image rel.toSecond (rel.preimage K) := rfl
    have hA := lex_sortedIndices_image_iff rel.toSecond rel.strictMono_toSecond
      (rel.preimage J) $ rel.preimage K
    have hB := lex_sortedIndices_image_iff rel.toFirst rel.strictMono_toFirst
      (rel.preimage J) $ rel.preimage K
    rw [image_toFirst_preimage rel J hJ, image_toFirst_preimage rel K hK] at hB
    rw [binaryEncode_lt_iff_lex_of_card_eq (rel.transport J) (rel.transport K) hcardT, binaryEncode_lt_iff_lex_of_card_eq J K hcard, htJ, htK, hA, hB]
  have hnot2 := fun hc => not_lt.2 (hub _ hK0) $ hlt.1 hc
  rw [hKeq] at hnot2
  exact not_lt.1 hnot2
  have hex' : ¬ ∃ J, IsMaxOrderIndexSet I m L' J := by
    rintro ⟨J, hJ⟩
    exact hex ⟨rel.symm.transport J, isMaxOrderIndexSet_transport rel.symm I m hJ⟩
  rw [lexMaxIndices_eq_empty I m L' hex', lexMaxIndices_eq_empty I m L hex]
  symm
  ext i
  constructor
  intro hi
  obtain ⟨a, -, ha⟩ := (rel.mem_transport _ i).1 hi
  exact absurd ha $ by simp
  intro hi
  exact absurd hi $ by simp

end

theorem monomialCenter_eq_of_sameNontrivialBoundary (I : ISD Y) (m : ℕ)
    {L L' : Bdy Y} (h : SameNontrivialBoundary L L') :
    monomialCenter I m L = monomialCenter I m L' := by
  obtain ⟨rel⟩ := nonempty_orderedMatchingOfNonTop h
  have hmin := minIndexCard_eq_of_orderedMatchingOfNonTop rel I m
  have hcen : monomialCenterSet I m L = monomialCenterSet I m L' := by
    have hmin := minIndexCard_eq_of_orderedMatchingOfNonTop rel I m
    have hmax := maxCandidateOrder_eq_of_orderedMatchingOfNonTop rel I m
    have hch := lexMaxIndices_transport rel I m
    have hgood := get_ne_top_of_mem_lexMaxIndices I m L
    let _a0 := lexMaxIndices I m L
    have hback : rel.symm.transport (rel.transport _a0) = _a0 :=
      transport_symm_transport rel.symm _a0 hgood
    have hsets : {C : Set Y | IsCandidateComponent I m L (minIndexCard I m L) _a0 C ∧
          orderAlong I C = maxCandidateOrder I m L}
        = {C : Set Y | IsCandidateComponent I m L' (minIndexCard I m L') (lexMaxIndices I m L') C ∧
          orderAlong I C = maxCandidateOrder I m L'} := by
      ext C
      simp [mem_ofPred_eq]
      rw [hch, ← hmin, ← hmax]
      constructor
      rintro ⟨hc, hord⟩
      exact ⟨isCandidateComponent_transport rel hc, hord⟩
      rintro ⟨hc, hord⟩
      refine ⟨?_, hord⟩
      have h2 := isCandidateComponent_transport rel.symm hc
      rwa [hback] at h2
    unfold monomialCenterSet
    exact congrArg sUnion hsets
  have hint : intersectionIdeal L (lexMaxIndices I m L) = intersectionIdeal L' (lexMaxIndices I m L') := by
    rw [lexMaxIndices_transport rel I m]
    exact intersectionIdeal_transport rel (lexMaxIndices I m L) $ get_ne_top_of_mem_lexMaxIndices I m L
  have hiff : (minIndexCard I m L ≠ 0 ∧
        IsOpen (subschemeι (intersectionIdeal L $ lexMaxIndices I m L) ⁻¹' monomialCenterSet I m L))
      ↔ (minIndexCard I m L' ≠ 0 ∧
        IsOpen (subschemeι (intersectionIdeal L' $ lexMaxIndices I m L') ⁻¹' monomialCenterSet I m L')) := by
    rw [hmin, hint, hcen]
  unfold monomialCenter
  by_cases hc : minIndexCard I m L ≠ 0 ∧
      IsOpen (subschemeι (intersectionIdeal L $ lexMaxIndices I m L) ⁻¹' monomialCenterSet I m L)
  rw [dif_pos hc, dif_pos $ hiff.1 hc]
  exact openSublocusIdeal_congr hint hcen _ _
  rw [dif_neg hc, dif_neg fun hx => hc $ hiff.2 hx]
end

end MonomialCenter




namespace MonomialCenter

section
variable (T : MarkedIdealWithBoundary) (Y : Sch)
section
variable (k' : Type) [Field k'] (q : Y ⟶ Sp k') (g : Y ⟶ scheme T)
def pullbackIndex :
    Fin T.boundary.length → Fin (T.pbOF q g).boundary.length :=
  pullbackOverFieldIndex T Y k' q g

@[simp]
theorem pullbackIndex_val (j : Fin T.boundary.length) :
    ((pullbackIndex T Y k' q g j : Fin (T.pbOF q g).boundary.length) : ℕ) = (j : ℕ) :=
  pullbackOverFieldIndex_val T Y k' q g j

def pullbackIndexSymm :
    Fin (T.pbOF q g).boundary.length → Fin T.boundary.length :=
  cast $ MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q g

section
variable (j : Fin (T.pbOF q g).boundary.length)
@[simp]
theorem pullbackIndexSymm_val :
    ((pullbackIndexSymm T Y k' q g j : Fin T.boundary.length) : ℕ) = (j : ℕ) :=
  rfl


@[simp]
theorem pullbackIndex_pullbackIndexSymm :
    pullbackIndex T Y k' q g (pullbackIndexSymm T Y k' q g j) = j := by
  apply val_injective
  rw [pullbackIndex_val, pullbackIndexSymm_val]
end
end

section
variable (q : Y ⟶ Sp T.base) (g : Y ⟶ scheme T)
def pullbackAlongIndex :
    Fin T.boundary.length → Fin (T.pbA q g).boundary.length :=
  EmbeddedResolution.pullbackAlongIndex T Y q g

@[simp]
theorem pullbackAlongIndex_val (j : Fin T.boundary.length) :
    ((pullbackAlongIndex T Y q g j : Fin (T.pbA q g).boundary.length) : ℕ) = (j : ℕ) :=
  EmbeddedResolution.pullbackAlongIndex_val T Y q g j
end
end

structure IsComponentCompatiblePullback (T : MarkedIdealWithBoundary) (Y : Sch) (k' : Type) [Field k']
    (q : Y ⟶ Sp k') (g : Y ⟶ scheme T) : Prop where
  comapCenter : ∀ J (Cc_ : Set $ CSet T.scheme),
    Cc_ ⊆ intersectionComponents T.boundary J →
    ∀ hop : IsOpen $ ⇑(intersectionIdeal T.boundary J).si ⁻¹' ⋃₀ Cc_,
      ∃ hop' : IsOpen $ ⇑(intersectionIdeal (T.pbOF q g).boundary
          (image (pullbackIndex T Y k' q g) J)).subschemeι ⁻¹'
          ⋃₀ {C' | C' ∈ intersectionComponents (T.pbOF q g).boundary
              (image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ Cc_, MapsTo (⇑g) C' C},
        (componentUnionIdeal T.boundary J Cc_ hop).comap g =
          componentUnionIdeal (T.pbOF q g).boundary
            (image (pullbackIndex T Y k' q g) J)
            {C' | C' ∈ intersectionComponents (T.pbOF q g).boundary
              (image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ Cc_, MapsTo (⇑g) C' C} hop'
  componentsDown : ∀ J,
    ∀ C' ∈ intersectionComponents (T.pbOF q g).boundary (image (pullbackIndex T Y k' q g) J),
      ∃ C ∈ intersectionComponents T.boundary J, MapsTo (⇑g) C' C ∧
        ∀ xi' xi_, IsGenericPoint xi' C' → IsGenericPoint xi_ C → g xi' = xi_
  componentsUp : ∀ J,
    ∀ C ∈ intersectionComponents T.boundary J, ∀ y : ↥Y, g y ∈ C →
      ∃ C' ∈ intersectionComponents (T.pbOF q g).boundary (image (pullbackIndex T Y k' q g) J),
        y ∈ C' ∧
          ∀ xi' xi_, IsGenericPoint xi' C' → IsGenericPoint xi_ C → g xi' = xi_
  orderAtComap : ∀ I y, orderAt (I.comap g) y = orderAt I (g y)

section
variable (T : MarkedIdealWithBoundary) (Y) (k' : Type) [Field k'] (q : Y ⟶ Sp k') (g : Y ⟶ scheme T)
theorem orderAlong_pullbackOverField_eq_orderAlong
    (hP : IsComponentCompatiblePullback T Y k' q g) J
    C' C
    (hC' : C' ∈ intersectionComponents (T.pbOF q g).boundary
      (image (pullbackIndex T Y k' q g) J))
    (hC : C ∈ intersectionComponents T.boundary J)
    (hgen : ∀ xi' xi_, IsGenericPoint xi' C' → IsGenericPoint xi_ C → g xi' = xi_) :
    orderAlong (T.pbOF q g).ideal C' = orderAlong T.ideal C := by
  have hg := hgen (icGP hC')
      (icGP hC)
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  exact tr_ (orderAlong_eq_orderAt_of_mem_intersectionComponents (T.pbOF q g).ideal hC') $ tr_ (hP.orderAtComap T.ideal $ icGP hC') $ tr_ (congrArg (orderAt T.ideal) hg) (orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC).symm

theorem lexMaxIndices_pullbackOverField_eq_image
    (h : sortedIndices (lexMaxIndices T.ideal T.mult T.boundary) =
      sortedIndices (lexMaxIndices (T.pbOF q g).ideal
        (T.pbOF q g).mult (T.pbOF q g).boundary)) :
    lexMaxIndices (T.pbOF q g).ideal (T.pbOF q g).mult
        (T.pbOF q g).boundary =
      image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary) := by
  apply Finset.ext
  intro j'
  constructor
  intro hj'
  have hmem :=
    (mem_sortedIndices _ _).2 ⟨j', hj', rfl⟩
  rw [← h] at hmem
  obtain ⟨j, hj, hval⟩ := (mem_sortedIndices _ _).1 hmem
  refine Finset.mem_image.2 ⟨j, hj, ?_⟩
  apply val_injective
  rwa [pullbackIndex_val]
  intro hj'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hj'
  have hmem :=
    (mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
  rw [h] at hmem
  obtain ⟨j2, hj2, hval⟩ := (mem_sortedIndices _ _).1 hmem
  have hj2eq : j2 = pullbackIndex T Y k' q g j := by
    apply val_injective
    rwa [pullbackIndex_val]
  rwa [hj2eq] at hj2

theorem pullbackIndex_strictMono :
    StrictMono $ pullbackIndex T Y k' q g := by
  intro a b hab
  have h := mp_ lt_def hab
  rwa [lt_def, pullbackIndex_val, pullbackIndex_val]

theorem sortedIndices_image_pullbackIndex
    J :
    sortedIndices (image (pullbackIndex T Y k' q g) J) = sortedIndices J := by
  rw [sortedIndices_image_of_strictMono (pullbackIndex T Y k' q g)
    (pullbackIndex_strictMono T Y k' q g) J]
  simp [pullbackIndex_val]
  rfl
end

section
variable {Y Y' : Sch} (I : ISD Y) (m : ℕ) (L : Bdy Y) (I' : ISD Y') (m' : ℕ) (L' : Bdy Y')
theorem centerInvariant_le_iff :
    (centerInvariant I m L).Le (centerInvariant I' m' L') ↔
      ((centerInvariant I m L).Lt (centerInvariant I' m' L') ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧ maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
          sortedIndices (lexMaxIndices I m L) = sortedIndices (lexMaxIndices I' m' L'))) :=
  m22

theorem centerInvariant_lt_iff_lex :
    (centerInvariant I m L).Lt (centerInvariant I' m' L') ↔
      (minIndexCard I m L < minIndexCard I' m' L' ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧
          (maxCandidateOrder I' m' L' < maxCandidateOrder I m L ∨
            (maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
              Lex (· < ·) (sortedIndices $ lexMaxIndices I m L)
                (sortedIndices $ lexMaxIndices I' m' L'))))) :=
  m22
end

section
variable (hGeom : MonomialGeometryHypotheses) (T : MarkedIdealWithBoundary) (Y) (k' : Type) [Field k'] (q) (g) (hT : IsLocallyMonomialTriple T) (hT' : IsLocallyMonomialTriple (T.pbOF q g)) (hP : IsComponentCompatiblePullback T Y k' q g)
include hGeom hT hT' hP
theorem comap_monomialCenter_eq_top
    (h0 : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    (hkey : minIndexCard (T.pbOF q g).ideal (T.pbOF q g).mult
          (T.pbOF q g).boundary = 0 ∨
        (centerInvariant T.ideal T.mult T.boundary).Lt
          (centerInvariant (T.pbOF q g).ideal (T.pbOF q g).mult
            (T.pbOF q g).boundary)) :
    (T.mc).comap g = ⊤ := by
  refine p39 g (T.mc) ?_
  intro y hy
  have hmem : g y ∈ monomialCenterSet T.ideal T.mult T.boundary := by
    rwa [← support_monomialCenter hGeom hT h0]
  rw [monomialCenterSet_eq_sUnion_centerComponents, mem_sUnion] at hmem
  obtain ⟨C, hCopt, hgyC⟩ := hmem
  obtain ⟨hcandC, hordC⟩ :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hCopt
  obtain ⟨-, hmemC, hmultC⟩ := hcandC
  obtain ⟨C', hC'mem, -, hgen⟩ :=
    hP.componentsUp (lexMaxIndices T.ideal T.mult T.boundary) C hmemC y hgyC
  have hordEq :=
    orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
      (lexMaxIndices T.ideal T.mult T.boundary) C' C hC'mem hmemC hgen
  have hinj :=
    (pullbackIndex_strictMono T Y k' q g).injective
  have hcard' : (image (pullbackIndex T Y k' q g)
      (lexMaxIndices T.ideal T.mult T.boundary)).card
      = minIndexCard T.ideal T.mult T.boundary := by
    rw [card_image_of_injective _ hinj]
    exact card_lexMaxIndices hGeom hT h0
  have hmultC' := hmultC
  rw [← hordEq] at hmultC'
  have hcand' : IsCandidateComponent (T.pbOF q g).ideal (T.pbOF q g).mult
      (T.pbOF q g).boundary (minIndexCard T.ideal T.mult T.boundary)
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) C' :=
    ⟨hcard', hC'mem, hmultC'⟩
  have hone := Nat.pos_of_ne_zero h0
  have hspec := minIndexCard_spec (T.pbOF q g).ideal (T.pbOF q g).mult
      (T.pbOF q g).boundary
      ⟨minIndexCard T.ideal T.mult T.boundary, hone,
        image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary), C',
        hcand'⟩
  have hle :=
    hspec.2.2 _ hone _ _ hcand'
  have hgeone := an1 hspec
  rcases hkey with hzero | hlt
  omega
  rw [centerInvariant_lt_iff_lex] at hlt
  have h0' : minIndexCard (T.pbOF q g).ideal (T.pbOF q g).mult
      (T.pbOF q g).boundary ≠ 0 := by omega
  rcases hlt with hml | ⟨hmeq, hrest⟩
  omega
  have hcand'' := hcand'
  rw [hmeq] at hcand''
  have hordC' := hordC
  rw [← hordEq] at hordC'
  rcases hrest with hmax | ⟨hmaxeq, hlex⟩
  have hb := (maxCandidateOrder_spec hGeom hT' h0').2.1 _ _ hcand''
  rw [hordC'] at hb
  exact absurd hmax $ mpr_ not_lt hb
  have hnot := an2 (lexMaxIndices_spec hGeom hT' h0') _ ⟨C', hcand'', tr_ hordC' hmaxeq⟩
  rw [sortedIndices_image_pullbackIndex T Y k' q g (lexMaxIndices T.ideal T.mult T.boundary)] at hnot
  exact hnot hlex
end

theorem minIndexCard_ne_zero_and_le_pullbackOverField (_hGeom : MonomialGeometryHypotheses) (T : MarkedIdealWithBoundary)
    Y (k' : Type) [Field k'] q
    g (_hT : IsLocallyMonomialTriple T)
    (_hT' : IsLocallyMonomialTriple $ T.pbOF q g)
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (h0 : minIndexCard (T.pbOF q g).ideal (T.pbOF q g).mult
        (T.pbOF q g).boundary ≠ 0) :
    minIndexCard T.ideal T.mult T.boundary ≠ 0 ∧
      minIndexCard T.ideal T.mult T.boundary ≤
        minIndexCard (T.pbOF q g).ideal (T.pbOF q g).mult
          (T.pbOF q g).boundary := by
  let _a0 := T.pbOF q g
  obtain ⟨J', C', hcard', hmem', hord'⟩ :=
    exists_isCandidateComponent_minIndexCard _a0.ideal
      _a0.mult _a0.boundary h0
  have hinj : m120 $ pullbackIndexSymm T Y k' q g := by
    intro a b hab
    apply Fin.val_injective
    have h := congrArg (fun z : Fin (bLen T) => (z : ℕ)) hab
    simpa using h
  let _a1 := image (pullbackIndexSymm T Y k' q g) J'
  have hJ : image (pullbackIndex T Y k' q g)
      _a1 = J' := by
    ext x
    constructor
    intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    rwa [pullbackIndex_pullbackIndexSymm]
    intro hx
    exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g x,
      Finset.mem_image.2 ⟨x, hx, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g x⟩
  obtain ⟨C, hC, -, hgen⟩ :=
    hP.componentsDown _a1 C'
      (by rw [hJ]; exact hmem')
  have heq : orderAlong _a0.ideal C' = orderAlong T.ideal C := by
    erw [orderAlong_eq_orderAt_of_mem_intersectionComponents _ hmem', hP.orderAtComap T.ideal _, hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmem') $ isGenericPoint_genericPoint_of_mem_intersectionComponents hC, orderAlong_eq_orderAt_of_mem_intersectionComponents _ hC]
  have hord2 : tMu T ≤ orderAlong T.ideal C := by
    have hx := hord'
    rwa [heq] at hx
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (minIndexCard _a0.ideal _a0.mult
        _a0.boundary)
      _a1 C :=
    ⟨tr_ (card_image_of_injective J' hinj) hcard', hC, hord2⟩
  have hone := Nat.pos_of_ne_zero h0
  have hspec := minIndexCard_spec T.ideal T.mult T.boundary ⟨minIndexCard _a0.ideal _a0.mult _a0.boundary, hone, _a1, C, hcand⟩
  refine ⟨?_, hspec.2.2 _ hone _ _ hcand⟩
  omega

theorem componentUnionIdeal_congr {Y : Sch} (L : Bdy Y)
    J J' Cc_ Cc' (hJ : J = J') (hCc_ : Cc_ = Cc')
    (hop : IsOpen $ ⇑(intersectionIdeal L J).si ⁻¹' ⋃₀ Cc_)
    (hop' : IsOpen $ ⇑(intersectionIdeal L J').si ⁻¹' ⋃₀ Cc') :
    componentUnionIdeal L J Cc_ hop = componentUnionIdeal L J' Cc' hop' := by
  subst hJ
  subst hCc_
  rfl

section
variable (hGeom : MonomialGeometryHypotheses) (T : MarkedIdealWithBoundary) (Y) (k' : Type) [Field k'] (q) (g) (hT : IsLocallyMonomialTriple T) (hT' : IsLocallyMonomialTriple (T.pbOF q g)) (hP : IsComponentCompatiblePullback T Y k' q g)
include hGeom hT hT' hP
theorem minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le :
    minIndexCard (T.pbOF q g).ideal (T.pbOF q g).mult
        (T.pbOF q g).boundary = 0 ∨
      (centerInvariant T.ideal T.mult T.boundary).Le
        (centerInvariant (T.pbOF q g).ideal (T.pbOF q g).mult
          (T.pbOF q g).boundary) := by
  let _a2 := pullbackIndexSymm T Y k' q g
  let _c0 := T.pbOF q g
  by_cases h0' : minIndexCard _c0.ideal _c0.mult
      _c0.boundary = 0
  exact inl h0'
  refine inr ?_
  obtain ⟨h0, hle⟩ := minIndexCard_ne_zero_and_le_pullbackOverField hGeom T Y k' q g hT hT' hP h0'
  rw [centerInvariant_le_iff, centerInvariant_lt_iff_lex]
  rcases lt_or_eq_of_le hle with hlt | heq
  exact inl $ inl hlt
  have hmaxle : maxCandidateOrder (T.pbOF q g).ideal (T.pbOF q g).mult (T.pbOF q g).boundary ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
    let hmin := sy_ heq
    have h0' := h0
    rw [← hmin] at h0'
    obtain ⟨J', C', hcand', hord'⟩ := an1 $ maxCandidateOrder_spec hGeom hT' h0'
    obtain ⟨hcard', hmemC', hmult'⟩ := hcand'
    let _a0 := pullbackIndexSymm T Y k' q g
    have hback_inj : m120 _a0 := by
      intro a b hab
      apply Fin.val_injective
      have h := congrArg Fin.val hab
      rwa [pullbackIndexSymm_val, pullbackIndexSymm_val] at h
    have himg : image (pullbackIndex T Y k' q g)
        (image _a0 J') = J' := by
      apply Finset.ext
      intro j
      constructor
      intro hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      rwa [pullbackIndex_pullbackIndexSymm]
      intro hj
      exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g j,
        Finset.mem_image.2 ⟨j, hj, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g j⟩
    have hmem := hmemC'
    rw [← himg] at hmem
    obtain ⟨C, hC, _hmaps, hgen⟩ :=
      hP.componentsDown (image _a0 J') C' hmem
    let _a1 := T.pbOF q g
    have hord : orderAlong _a1.ideal C' = orderAlong T.ideal C := by
      rw [orderAlong_eq_orderAt_of_mem_intersectionComponents _a1.ideal hmemC',
        orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC]
      dsimp [icGP]
      rw [← hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmemC') $ isGenericPoint_genericPoint_of_mem_intersectionComponents hC]
      exact hP.orderAtComap T.ideal $ icGP hmemC'
    have hcardJ := hmin
    rw [← hcard', ← card_image_of_injective _ hback_inj] at hcardJ
    have hmultC : tMu T ≤ orderAlong T.ideal C := by
      have hb := hmult'
      rwa [hord] at hb
    have hmaxOrd := (maxCandidateOrder_spec hGeom hT h0).2.1 _ _ $ m157 hcardJ $ m157 hC hmultC
    rwa [← hord', hord]
  rcases lt_or_eq_of_le hmaxle with hmlt | hmeq
  simp_all
  obtain ⟨C', hcand', hordC'⟩ := left $ lexMaxIndices_spec hGeom hT' h0'
  have hmultC' := right $ right hcand'
  let _a1 := pullbackIndex T Y k' q g
  have hex : ∃ B : FinSet $ bLen T,
      image _a1 B =
          lexMaxIndices _c0.ideal _c0.mult
            _c0.boundary ∧
        B.card = (lexMaxIndices _c0.ideal
          _c0.mult _c0.boundary).card := by
    refine ⟨image _a2
      (lexMaxIndices _c0.ideal _c0.mult
        _c0.boundary), ?_, ?_⟩
    rw [image_image]
    have hcomp : _a1 ∘ _a2 = id :=
      funext $ pullbackIndex_pullbackIndexSymm T Y k' q g
    rw [hcomp, image_id]
    have _i11 : m120 $ pullbackIndexSymm T Y k' q g := by
      intro a b h
      apply Fin.val_injective
      rw [← pullbackIndexSymm_val T Y k' q g a, ← pullbackIndexSymm_val T Y k' q g b, h]
    exact card_image_of_injective _ _i11
  obtain ⟨B, hBim, hBcard⟩ := hex
  have hmemB := left $ right hcand'
  rw [← hBim] at hmemB
  obtain ⟨C, hC, -, hgenericPt⟩ := hP.componentsDown B C' hmemB
  have hordEq :=
    orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP B C' C hmemB hC hgenericPt
  have hcardB := sy_ heq
  rw [← card_lexMaxIndices hGeom hT' h0', ← hBcard] at hcardB
  have hmultC := hmultC'
  rw [hordEq] at hmultC
  have hmaxC := hmeq
  rw [← hordC', hordEq] at hmaxC
  have hnotlex := right (lexMaxIndices_spec hGeom hT h0) B $ Exists.intro C $ m157 (m157 hcardB $ m157 hC hmultC) hmaxC
  have hsp : sortedIndices (lexMaxIndices _c0.ideal
      _c0.mult _c0.boundary) =
      sortedIndices B := by
    rw [← hBim]
    exact sortedIndices_image_pullbackIndex T Y k' q g B
  rcases trichotomous_of (Lex (· < ·))
      (sortedIndices $ lexMaxIndices T.ideal T.mult T.boundary)
      (sortedIndices $ lexMaxIndices _c0.ideal
        _c0.mult _c0.boundary) with
    hlex | hlexeq | hlex
  exact inl $ inr ⟨heq, inr ⟨sy_ hmeq, hlex⟩⟩
  exact inr ⟨heq, sy_ hmeq, hlexeq⟩
  rw [hsp] at hlex
  exact absurd hlex hnotlex

theorem monomialCenter_pullbackOverField_eq_comap
    (hmin : minIndexCard (T.pbOF q g).ideal (T.pbOF q g).mult
        (T.pbOF q g).boundary = minIndexCard T.ideal T.mult T.boundary)
    (hmax : maxCandidateOrder (T.pbOF q g).ideal (T.pbOF q g).mult
        (T.pbOF q g).boundary = maxCandidateOrder T.ideal T.mult T.boundary)
    (hch : lexMaxIndices (T.pbOF q g).ideal (T.pbOF q g).mult
        (T.pbOF q g).boundary =
      image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) :
    monomialCenter (T.pbOF q g).ideal (T.pbOF q g).mult
        (T.pbOF q g).boundary =
      (T.mc).comap g := by
  let _c0 := T.pbOF q g
  let _c1 := lexMaxIndices T.ideal T.mult T.boundary
  by_cases h0 : minIndexCard T.ideal T.mult T.boundary = 0
  have h0' : minIndexCard _c0.ideal _c0.mult
      _c0.boundary = 0 := by rw [hmin]
                             exact h0
  dsimp [mc]
  rw [monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0', monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0]
  exact sy_ $ comap_top g
  have h0' : minIndexCard _c0.ideal _c0.mult
      _c0.boundary ≠ 0 := by rw [hmin]
                             exact h0
  obtain ⟨hop', heq⟩ := hP.comapCenter _c1
    (centerComponents T.ideal T.mult T.boundary)
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)
    (isOpen_preimage_sUnion_centerComponents hGeom hT)
  have hSet : centerComponents _c0.ideal
        _c0.mult _c0.boundary =
      {C' | C' ∈ intersectionComponents _c0.boundary
          (image (pullbackIndex T Y k' q g) _c1) ∧
        ∃ C ∈ centerComponents T.ideal T.mult T.boundary, MapsTo (g) C' C} := by
    ext C'
    simp [mem_ofPred_eq]
    constructor
    intro hmem
    obtain ⟨hcand, hordC'⟩ := (mem_centerComponents_iff _ _ _ C').1 hmem
    obtain ⟨hcardJ', hmemC', hmultC'⟩ := hcand
    rw [hch] at hmemC'
    refine ⟨hmemC', ?_⟩
    obtain ⟨C, hC, hmaps, hgen⟩ :=
      hP.componentsDown _c1 C' hmemC'
    have hord :=
      orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
        _c1 C' C hmemC' hC hgen
    refine ⟨C, (mem_centerComponents_iff _ _ _ C).2
      ⟨⟨card_lexMaxIndices hGeom hT h0, hC, ?_⟩, ?_⟩, hmaps⟩
    rwa [← hord]
    rwa [← hord, hordC']
    rintro ⟨hmemC', C, hCopt, hmaps⟩
    obtain ⟨hcandC, hordC⟩ := (mem_centerComponents_iff _ _ _ C).1 hCopt
    obtain ⟨hcardJ, hCmem, hmultC⟩ := hcandC
    obtain ⟨C0_, hC0_, hmaps0_, hgen⟩ :=
      hP.componentsDown _c1 C' hmemC'
    obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hmemC').nonempty
    have hCC0 : C0_ = C := by
      by_contra hne
      exact Set.disjoint_left.1
        (hGeom.components_disjoint T hT.valid _ C0_ hC0_ C hCmem hne) (hmaps0_ hx) $ hmaps hx
    have hord :=
      orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
        _c1 C' C0_ hmemC' hC0_ hgen
    refine (mem_centerComponents_iff _ _ _ C').2
      ⟨⟨card_lexMaxIndices hGeom hT' h0', ?_, ?_⟩, ?_⟩
    rwa [hch]
    rwa [hord, hCC0]
    rw [hord, hCC0, hordC]
    exact sy_ hmax
  have h1 := monomialCenter_eq_componentUnionIdeal hGeom hT' h0'
  have h2 := monomialCenter_eq_componentUnionIdeal hGeom hT h0
  dsimp [mc] at h1 h2 ⊢
  rw [h1, h2, heq]
  exact componentUnionIdeal_congr _ _ _ _ _ hch hSet _ _
end

end MonomialCenter





namespace MonomialCenter

theorem IsComponentCompatiblePullback.of_flat (hGeom : MonomialGeometryHypotheses) (T : MarkedIdealWithBoundary)
    (hT : T.IsAdmissible) (Y : Sch) (k' : Type) [Field k']
    q g [Flat g]
    (hT' : (T.pbOF q g).IsAdmissible)
    (hord : ∀ (A : tISD T) (y : ↥Y), orderAt (A.comap g) y = orderAt A (g y)) :
    IsComponentCompatiblePullback T Y k' q g :=
  ⟨fun J Cc_ hCc_ hop => hGeom.flat_comap_center T hT Y k' q g hT' J Cc_ hCc_ hop,
    fun J => hGeom.flat_components_down T hT Y k' q g hT' J,
    fun J => hGeom.flat_components_up T hT Y k' q g hT' J, hord⟩

end MonomialCenter





theorem exists_isOpen_inter_subset_of_maximal {al_ : Type} [TopologicalSpace al_]
    [NoetherianSpace al_] (A : Set al_) (hA : IsClosed A) (C : Set al_)
    (hC : IsIrreducible C) (hCA : C ⊆ A)
    (hmax : ∀ C' : Set al_, IsIrreducible C' → C ⊆ C' → C' ⊆ A → C' = C) :
    ∃ O : Set al_, IsOpen O ∧ (O ∩ A).Nonempty ∧ O ∩ A ⊆ C := by
  classical
  obtain ⟨S, hirr, hsup⟩ :=
    exists_finset_irreducible
      (⟨A, hA⟩ : Closeds al_)
  have hcoe : ∀ S' : Finset $ Closeds al_,
      ((S'.sup id : Closeds al_) : Set al_) = ⋃ k ∈ S', (k : Set al_) := by simp_all
  have hA' : A = ⋃ k ∈ S, (k : Set al_) :=
    (congrArg (fun s : Closeds al_ => (s : Set al_)) hsup).trans $ hcoe S
  obtain ⟨T, hTdef⟩ : ∃ T : Finset $ Closeds al_,
      T = S.filter fun k : Closeds al_ => ¬ ((k : Set al_) ⊆ C) := ⟨_, rfl⟩
  have hmemT : ∀ k : Closeds al_,
      k ∈ T ↔ k ∈ S ∧ ¬ ((k : Set al_) ⊆ C) := by simp_all
  refine ⟨(⋃ k ∈ T, (k : Set al_))ᶜ, (isClosed_biUnion (finite_toSet _) fun k _ => k.2).isOpen_compl, ?_, ?_⟩
  by_contra hemp
  have hAsub : A ⊆ ⋃ k ∈ T, k := by
    intro z hz
    by_contra hz'
    exact hemp ⟨z, hz', hz⟩
  obtain ⟨s, hsT, hCs⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hC
      (T.image fun k : Closeds al_ => k)
      (by
        intro z hz
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
        exact k.2)
      (by
        refine hCA.trans $ hAsub.trans ?_
        intro z hz
        obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hz
        exact Set.mem_sUnion.mpr
          ⟨k, Finset.mem_coe.mpr $ Finset.mem_image_of_mem _ hk, hzk⟩)
  obtain ⟨k, hkT, rfl⟩ := Finset.mem_image.mp hsT
  let _a0 := mp_ (hmemT k) hkT
  have hkS : k ∈ S := _a0.1
  refine _a0.2 $ le_of_eq $ hmax (k : Set al_) (hirr ⟨k, hkS⟩) hCs ?_
  rw [hA']
  exact fun z hz => Set.mem_iUnion₂.mpr ⟨k, hkS, hz⟩
  rintro z ⟨hzO, hzA⟩
  rw [hA'] at hzA
  obtain ⟨k, hkS, hzk⟩ := Set.mem_iUnion₂.mp hzA
  by_cases hk : (k : Set al_) ⊆ C
  exact hk hzk
  simp_all

theorem exists_specializes_of_homeomorph {al_ be_ : Type} [TopologicalSpace al_] [TopologicalSpace be_]
    (p : al_ → Prop) (q : be_ → Prop) (f : al_ → be_) (e : {x : al_ // p x} ≃ₜ {y : be_ // q y})
    (he : ∀ x : {x : al_ // p x}, ((e x : be_)) = f (x : al_))
    (xi_ : be_) (hxi_ : q xi_) (y : al_) (hy : p y) (hs : f y ∈ closure ({xi_} : Set be_)) :
    ∃ x : al_, p x ∧ f x = xi_ ∧ y ∈ closure ({x} : Set al_) := by
  refine ⟨((e.symm ⟨xi_, hxi_⟩ : {x : al_ // p x}) : al_), (e.symm ⟨xi_, hxi_⟩).2, ?_, ?_⟩
  have h1 := he $ e.symm ⟨xi_, hxi_⟩
  rw [← h1]
  simp
  have h2 : ((e ⟨y, hy⟩ : {z : be_ // q z}) : be_) ∈ closure ({xi_} : Set be_) := by
    rwa [he ⟨y, hy⟩]
  have h3 : (e ⟨y, hy⟩) ∈ closure ({(⟨xi_, hxi_⟩ : {z : be_ // q z})} : Set {z : be_ // q z}) := by
    rwa [closure_subtype, image_singleton]
  have h4 := mem_image_of_mem (e.symm) h3
  rw [e.symm.image_closure, image_singleton, Homeomorph.symm_apply_apply] at h4
  have h5 := mp closure_subtype h4
  rwa [image_singleton] at h5

section
variable {X X' : Sch} (pi_ : X' ⟶ X) (Z : ISD X)
theorem exists_lift_of_specializes_of_isBlowupAlongIdealSheaf (h : IsBlowupAlongIdealSheaf pi_ Z) (xi_ : ↥X) (hxi_ : xi_ ∉ support Z)
    (y : ↥X') (hy : pi_ y ∉ support Z) (hs : pi_ y ∈ closure ({xi_} : Set ↥X)) :
    ∃ x : ↥X', pi_ x = xi_ ∧ y ∈ closure ({x} : Set ↥X') := by
  have h1 := h.restrict $ suppC Z
  rw [comap_io_support_compl_eq_top Z] at h1
  have hiso := h1.isIso_of_top
  let _a0 := pre pi_ $ suppC Z
  obtain ⟨e, he⟩ : ∃ e : {a : X' // a ∈ _a0} ≃ₜ
      {b : X // b ∈ suppC Z},
      ∀ a : {a : X' // a ∈ _a0},
        (e a) = (pi_.base) a :=
    ⟨m207 $ asIso $ pi_.mr $ suppC Z,
      fun a => morphismRestrict_base_coe pi_ Z.support.compl a⟩
  obtain ⟨x, -, hx1, hx2⟩ :=
    exists_specializes_of_homeomorph (fun a => a ∈ _a0)
      (fun b => b ∈ suppC Z) (fun a => (pi_.base) a) e he xi_ hxi_ y hy hs
  exact ⟨x, hx1, hx2⟩

theorem eq_of_isBlowupAlongIdealSheaf_of_notMem_support (h : IsBlowupAlongIdealSheaf pi_ Z) x y
    (hx : pi_ x ∉ support Z) (hy : pi_ y ∉ support Z) (hxy : pi_ x = pi_ y) : x = y := by
  have h1 := h.restrict $ suppC Z
  rw [comap_io_support_compl_eq_top Z] at h1
  have hiso := h1.isIso_of_top
  obtain ⟨e, he⟩ : ∃ e : {a : X' // a ∈ pre pi_ (suppC Z)} ≃ₜ
      {b : X // b ∈ suppC Z},
      ∀ a : {a : X' // a ∈ pre pi_ (suppC Z)},
        (e a) = (pi_.base) a :=
    ⟨m207 $ asIso $ pi_.mr $ suppC Z,
      fun a => morphismRestrict_base_coe pi_ Z.support.compl a⟩
  have hx' := hx
  have hy' := hy
  have key : e ⟨x, hx'⟩ = e ⟨y, hy'⟩ := by
    apply m26
    rwa [he ⟨x, hx'⟩, he ⟨y, hy'⟩]
  exact congrArg val $ e.injective key

theorem notMem_support_exceptionalIdeal (y : ↥X') (hy : pi_ y ∉ support Z) :
    y ∉ support (exceptionalIdeal pi_ Z) := by
  have h1 : ((spI (cmI Z pi_) : Closeds X') : Set X')
      = m142 pi_.base Z.supp := by simp_all
  intro hmem
  have hmem' : y ∈ ((spI (cmI Z pi_) : Closeds X') : Set X') := hmem
  rw [h1] at hmem'
  exact hy hmem'
end

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

structure PrincipalizationGeometryHypotheses : Prop where
  maxContactTransport : OrderCertificateIsoInvariantOfMaxContact
  exceptional_components_not_subset : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ Z : tISD T,
      Smooth (subschemeι Z ≫ structMap T) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Sch) (pi_ : X' ⟶ scheme T), IsBlowupAlongIdealSheaf pi_ Z →
    ∀ (J : tISD T) (c : ℕ),
      (∀ x : ↥T.scheme, x ∈ support Z → orderAt J x = (c : ENat)) →
    ∀ J' : ISD X',
      exceptionalIdeal pi_ Z ^ c * J' = J.comap pi_ →
    ∀ C' : Set ↥X', IsIrreducibleComponentOf C' (↑(exceptionalIdeal pi_ Z).support : Set ↥X') →
      ¬ C' ⊆ (↑J'.support : Set ↥X')
  orderAt_baseChange : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
      (I : tISD T) (y : ↥(bc T f).scheme),
      orderAt (I.comap $ pullback.fst T.structMap $ specMapOfFieldHom T.base L f) y =
        orderAt I ((pullback.fst T.structMap $ specMapOfFieldHom T.base L f).base y)
  controlledTransform_orderAt_le : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ Z : tISD T,
      Smooth (subschemeι Z ≫ structMap T) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Sch) (pi_ : X' ⟶ scheme T), IsBlowupAlongIdealSheaf pi_ Z →
    ∀ (J : tISD T) (c : ℕ),
      (∀ x : ↥T.scheme, x ∈ support Z → orderAt J x = (c : ENat)) →
    ∀ J' : ISD X',
      exceptionalIdeal pi_ Z ^ c * J' = J.comap pi_ →
    ∀ x' : ↥X', x' ∈ support (exceptionalIdeal pi_ Z) → orderAt J' x' ≤ (c : ENat)
  splitting_smooth_pullback : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
      [Smooth h], h ≫ structMap T = q →
      (T.pbA q h).IsAdmissible →
    ∀ M N : tISD T,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting (T.pbA q h).boundary (T.pbA q h).ideal
        (M.comap h) (N.comap h)
  splitting_exists : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∃ M N : tISD T, IsMonomialSplitting T.boundary T.ideal M N
  splitting_unique : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ M N M' N' : tISD T,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting T.boundary T.ideal M' N' →
      M = M' ∧ N = N'
  strictTransform_components : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ Z : tISD T,
      Smooth (subschemeι Z ≫ structMap T) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Sch) (pi_ : X' ⟶ scheme T), IsBlowupAlongIdealSheaf pi_ Z →
    ∀ D ∈ boundary T,
    ∀ C' : Set ↥X', IsIrreducibleComponentOf C' (↑(strictTransform pi_ Z D).support : Set ↥X') →
      ∃ (et' : ↥X') (C : CSet T.scheme),
        C' = closure {et'} ∧
        et' ∉ support (exceptionalIdeal pi_ Z) ∧
        IsIrreducibleComponentOf C (↑D.support : CSet T.scheme) ∧
        ¬ C ⊆ (↑Z.support : CSet T.scheme) ∧
        C = closure {pi_.base et'}
  monomialInputs : MonomialGeometryHypotheses

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits Opposite


namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
private theorem sameNontrivialBoundary_append_top (L : Bdy X) :
    SameNontrivialBoundary (L ++ [⊤]) L := by
  rw [sameNontrivialBoundary_iff]
  induction L with
  | nil => simp [nontrivialPart]
  | cons D t ih =>
      simp only [nontrivialPart, cons_append, filter_cons] at ih ⊢
      rw [ih]

theorem sameNontrivialBoundary_of_eq {A B C : Bdy X}
    (h : SameNontrivialBoundary A B) (e : C = B) : SameNontrivialBoundary A C := by
  subst e
  exact h

theorem top_pow_mul (J : ISD X) (m : ℕ) :
    (⊤ : ISD X) ^ m * J = J := by
  have e : (1 : ISD X) = ⊤ := rfl
  rw [← e, one_pow, one_mul]
end

theorem comap_comp_eqToHom {F : ℕ → Sch} (G : ∀ n, IdealSheafData (F n))
    {a b : ℕ} (h : a = b) {W : Sch} (f : W ⟶ F a) :
    (G b).comap (f ≫ eqToHom (congrArg F h)) = (G a).comap f := by
  cases h
  have e : (eqToHom (congrArg F rfl) : F a ⟶ F a) = 𝟙 (F a) := rfl
  rw [e, Category.comp_id]

theorem map_comap_comp_eqToHom {F : ℕ → Sch} (G : ∀ n, List (F n).IdealSheafData)
    {a b : ℕ} (h : a = b) {W : Sch} (f : W ⟶ F a) :
    (G b).map (fun D => D.comap $ f ≫ eqToHom (congrArg F h))
      = (G a).map fun D => D.comap f := by
  cases h
  have e : (eqToHom (congrArg F rfl) : F a ⟶ F a) = 𝟙 (F a) := rfl
  rw [e]
  simp

theorem comap_ideal_boundary_succ_of_comap_center_eq_top {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedBlowupSequenceData p I m E) (n : ℕ) (hn : n < s.length)
    {W : Sch} (f : W ⟶ s.obj (n + 1))
    (hnoe : IsNoetherian $ s.obj $ n + 1)
    (hf : (s.center n).comap (f ≫ s.map n) = ⊤) :
    (s.ideal n).comap (f ≫ s.map n) = (s.ideal $ n + 1).comap f ∧
      SameNontrivialBoundary ((s.boundary $ n + 1).map fun D => D.comap f)
        ((s.boundary n).map fun D => D.comap $ f ≫ s.map n) := by
  let _a0 := IdealSheafData $ s.obj $ n + 1
  let _a1 := f ≫ s.map n
  have he := hf
  rw [comap_comp] at he
  have hST : ∀ D : ISD $ s.obj n,
      (p6 (s.map n) (s.center n) D).comap f = cmI D _a1 := by
    intro D
    rw [strictTransform_comap_of_comap_center_eq_top (s.map n) (s.center n) D f he,
      ← comap_comp]
  constructor
  have h1 := s.ideal_succ n hn
  simp [p9] at h1
  have h2 := congrArg (fun J : _a0 => J.comap f) h1
  rw [comap_mul, comap_pow, he,
    top_pow_mul] at h2
  simpa [comap_comp] using h2.symm
  have hfun : ((fun D : _a0 => cmI D f) ∘
      p6 (s.map n) (s.center n))
      = fun D => cmI D _a1 := by
    funext D
    exact hST D
  rw [s.boundary_succ n hn, map_append, map_map, map_cons, map_nil,
    p9, he, hfun]
  exact sameNontrivialBoundary_append_top _

namespace SequenceOfBlowupsPullback

variable {X X' : Sch} {ph_ : X' ⟶ X}

section
variable {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback ph_ s' s)
section
variable (j) (hj : j ≤ s'.length)
include hj
section
variable (i : ℕ)
section
variable (hi : i ≤ c.idx j)
def mapToEarlierScheme : schemeAt s' j ⟶ schemeAt s i :=
  c.map j hj ≫ transitionMap s hi

theorem mapToEarlierScheme_eq_map_comp_transitionMap :
    c.mapToEarlierScheme j hj i hi = c.map j hj ≫ transitionMap s hi := rfl

theorem mapToEarlierScheme_comp_projectionToBase :
    c.mapToEarlierScheme j hj i hi ≫ projectionToBase s i = projectionToBase s' j ≫ ph_ := by
  rw [mapToEarlierScheme_eq_map_comp_transitionMap, m146, SequenceOfBlowups.transitionMap_comp_projectionToBase]
  exact (c.isPullback j hj).w
end

theorem mapToEarlierScheme_eq_comp_blowupMorphism (hi : i < c.idx j) :
    c.mapToEarlierScheme j hj i (le_of_lt hi) = c.mapToEarlierScheme j hj (i + 1) hi ≫ transitionMapSucc s i := by
  simp [mapToEarlierScheme_eq_map_comp_transitionMap, SequenceOfBlowups.blowupMorphism_eq_transitionMap, m146, SequenceOfBlowups.transitionMap_trans]
end

theorem mapToEarlierScheme_index :
    c.mapToEarlierScheme j hj (c.idx j) le_rfl = c.map j hj := by
  rw [mapToEarlierScheme_eq_map_comp_transitionMap, SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]

theorem index_le_length : c.idx j ≤ s.length := by
  rcases m63 j s'.length with h | h
  exact le_of_lt $ c.idx_lt j h
  have hje := le_antisymm hj h
  subst hje
  exact le_of_eq c.idx_length

theorem comap_center_mapToEarlierScheme_eq_top_of_unmatched (i : ℕ) (hi : i < c.idx j)
    (hmiss : ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ i) :
    (center s i).comap (c.mapToEarlierScheme j hj i $ le_of_lt hi) = ⊤ := by
  rw [eq_top_iff_support_eq_empty]
  ext y
  simp only [mem_empty_iff_false, iff_false]
  intro hy
  rw [support_comap] at hy
  refine c.omitted i (lt_of_lt_of_le hi $ c.index_le_length j hj) hmiss _ hy (bsM (sbPrj s' j) y) ?_
  have hb : bsM (c.mapToEarlierScheme j hj i (le_of_lt hi) ≫ sbPrj s i) y
      = bsM (sbPrj s' j ≫ ph_) y := by rw [c.mapToEarlierScheme_comp_projectionToBase j hj i $ le_of_lt hi]
  simpa using sy_ hb
end

theorem flat_map
    [Flat ph_] (j : ℕ) (hj : j ≤ s'.length) :
    Flat $ c.map j hj := by
  have h : MorphismProperty.IsStableUnderBaseChange $ @Flat := inferInstance
  exact h.of_isPullback (c.isPullback j hj).flip inferInstance

theorem isPullback_blowupMorphism
    [Flat ph_] (j : ℕ) (hj : j < s'.length) :
    IsPullback (c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) $ c.idx_strictMono j hj)
      (transitionMapSucc s' j) (transitionMapSucc s $ c.idx j) $ c.map j $ le_of_lt hj := by
  have hbl :=
    s.isBlowupAlongIdealSheaf_blowupMorphism _ $ c.idx_lt j hj
  have := c.flat_map j $ le_of_lt hj
  have hbj := s'.isBlowupAlongIdealSheaf_blowupMorphism j hj
  have hbl' := hbj
  rw [c.center_comap j hj] at hbl'
  obtain ⟨q, hq, hsq⟩ := hbl.exists_isPullback_of_flat (c.map j $ le_of_lt hj) hbl'
  have hcart0 : p17 $ (center s' j).comap $ transitionMapSucc s' j := by
    unfold IsBlowupAlongIdealSheaf at hbj
    exact an1 hbj
  have hcart := hcart0
  rw [c.center_comap j hj, ← comap_comp] at hcart
  have hstep := sy_ $ c.step j hj
  rw [← mapToEarlierScheme_eq_map_comp_transitionMap, c.mapToEarlierScheme_eq_comp_blowupMorphism (j + 1) hj (c.idx j) $ c.idx_strictMono j hj] at hstep
  rwa [hbl.hom_ext_of_comp_eq hcart hstep hq]

theorem index_mono :
    ∀ b, b ≤ s'.length → ∀ a, a ≤ b → c.idx a ≤ c.idx b := by
  intro b
  induction b with
  | zero =>
      intro _ a ha
      rw [le_zero.1 ha]
  | succ n ih =>
      intro hb a ha
      rcases m63 a (n + 1) with h | h
      exact le_trans (ih (m212 hb) a $ lt_succ_iff.1 h)
        (le_of_lt $ c.idx_strictMono n hb)
      have hae := le_antisymm ha h
      subst hae
      exact le_rfl

theorem index_ne_of_index_lt_of_lt_index_succ (j : ℕ) (hj : j + 1 ≤ s'.length) (i : ℕ)
    (hlo : c.idx j < i) (hhi : i < c.idx (j + 1)) :
    ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ i := by
  intro j' hj' hEq
  rcases m63 j' (j + 1) with h | h
  have hm := index_mono c j (m212 hj) j' $ lt_succ_iff.1 h
  omega
  have hm := index_mono c j' (le_of_lt hj') (j + 1) h
  omega

theorem index_ne_of_lt_index_zero (i : ℕ) (hi : i < c.idx 0) :
    ∀ j' : ℕ, j' < s'.length → c.idx j' ≠ i := by
  intro j' hj' hEq
  have hm := index_mono c j' (le_of_lt hj') 0 $ zero_le _
  omega
end

section
variable {k k' : Type} [Field k] [Field k']
section
variable {A B : Sch} {p : A ⟶ Sp k} {q : B ⟶ Sp k'} {g : B ⟶ A} {I : ISD A} {I' : ISD B} {m : ℕ} {E : Bdy A} {E' : Bdy B} (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E') (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) (j : ℕ) (hj : j ≤ s'.length)
section
variable (i : ℕ) (hi : i ≤ c.idx j)
def markedMapToEarlierScheme : s'.obj j ⟶ s.obj i :=
  c.mapToEarlierScheme j hj i hi

theorem markedMapToEarlierScheme_comp_projectionToBase :
    markedMapToEarlierScheme s s' c j hj i hi ≫ s.proj i = s'.proj j ≫ g := by
  have h := c.mapToEarlierScheme_comp_projectionToBase j hj i hi
  rwa [toMarkedSequence_projectionToBase, toMarkedSequence_projectionToBase] at h
end

def markedMap : s'.obj j ⟶ s.obj (c.idx j) :=
  c.map j hj

theorem markedMapToEarlierScheme_index :
    markedMapToEarlierScheme s s' c j hj (c.idx j) le_rfl = markedMap s s' c j hj :=
  c.mapToEarlierScheme_index j hj
end

theorem ideal_boundary_last_eq_comap_lastMap {X Y : Sch}
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k'}
    {g : Y ⟶ X} [Flat g]
    {I : ISD X} {I' : ISD Y} {m : ℕ}
    {E : Bdy X} {E' : Bdy Y}
    (s : MarkedBlowupSequenceData p I m E) (s' : MarkedBlowupSequenceData q I' m E')
    (c : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hI : I' = I.comap g)
    (hE : SameNontrivialBoundary E' (E.map fun D => D.comap g))
    (hN : ∀ i : ℕ, i ≤ s.length → IsNoetherian (s.obj i))
    (hN' : ∀ j : ℕ, j ≤ s'.length → IsNoetherian (s'.obj j)) :
    s'.ideal s'.length = (s.ideal s.length).comap c.lastMap ∧
      SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun D => D.comap c.lastMap) := by
  subst hI
  have hrun : ∀ j (hj : j ≤ s'.length) b hb a hab,
      (∀ t, a ≤ t → t < b → ∀ j', j' < s'.length → c.idx j' ≠ t) →
        (s.ideal a).comap (markedMapToEarlierScheme s s' c j hj a (le_trans hab hb)) =
            (s.ideal b).comap (markedMapToEarlierScheme s s' c j hj b hb) ∧
          SameNontrivialBoundary
            ((s.boundary a).map fun D => D.comap $ markedMapToEarlierScheme s s' c j hj a (le_trans hab hb))
            ((s.boundary b).map fun D => D.comap $ markedMapToEarlierScheme s s' c j hj b hb) := by
    intro j hj b
    induction b with
    | zero =>
        intro hb a hab _
        have ha0 := le_zero.1 hab
        subst ha0
        exact ⟨rfl, refl _⟩
    | succ nn ihb =>
        intro hb a hab hun
        rcases m63 a (nn + 1) with h | h
        have han := lt_succ_iff.1 h
        have hnb := le_trans (le_succ nn) hb
        obtain ⟨i1, b1⟩ := ihb hnb a han fun t ht ht2 => hun t ht $ lt_succ_of_lt ht2
        have hnlt := lt_of_lt_of_le (lt_succ_self nn) hb
        have hnlen := lt_of_lt_of_le hnlt (c.index_le_length j hj)
        have hntop : (s.center nn).comap (markedMapToEarlierScheme s s' c j hj nn hnb) = ⊤ := by
          have h0 := c.comap_center_mapToEarlierScheme_eq_top_of_unmatched j hj nn hnlt $ hun nn han (lt_succ_self nn)
          rwa [toMarkedSequence_center] at h0
        have hmt : markedMapToEarlierScheme s s' c j hj nn hnb
            = markedMapToEarlierScheme s s' c j hj (nn + 1) hb ≫ s.map nn := by
          have h0 := c.mapToEarlierScheme_eq_comp_blowupMorphism j hj nn hnlt
          rwa [toMarkedSequence_blowupMorphism] at h0
        have htop2 : (s.center nn).comap
            (markedMapToEarlierScheme s s' c j hj (nn + 1) hb ≫ s.map nn) = ⊤ := by simp_all
        obtain ⟨i2, b2⟩ := comap_ideal_boundary_succ_of_comap_center_eq_top s nn hnlen (markedMapToEarlierScheme s s' c j hj (nn + 1) hb)
          (hN (nn + 1) hnlen) htop2
        constructor
        refine tr_ i1 ?_
        rwa [hmt]
        refine tr_ b1 ?_
        rw [hmt]
        exact sy_ b2
        have hae := le_antisymm hab h
        subst hae
        exact ⟨rfl, refl _⟩
  have main : ∀ j (hj : j ≤ s'.length),
      s'.ideal j = (s.ideal (c.idx j)).comap (markedMap s s' c j hj) ∧
        SameNontrivialBoundary (s'.boundary j)
          ((s.boundary (c.idx j)).map fun D => D.comap $ markedMap s s' c j hj) := by
    intro j
    induction j with
    | zero =>
        intro hj0
        have hz : 0 ≤ c.idx 0 := zero_le _
        obtain ⟨r1, r2⟩ := hrun 0 hj0 (c.idx 0) le_rfl 0 hz
          (fun t _ ht => c.index_ne_of_lt_index_zero t ht)
        have hmi :=
          markedMapToEarlierScheme_index s s' c 0 hj0
        have e1 : s'.ideal 0 = (s.ideal 0).comap (markedMapToEarlierScheme s s' c 0 hj0 0 hz) := by
          rw [s'.ideal_zero, s.ideal_zero, ← s.proj_zero, ← s'.proj_zero,
            ← comap_comp, ← comap_comp,
            markedMapToEarlierScheme_comp_projectionToBase]
        constructor
        simp_all
        have hmap : SameNontrivialBoundary
            (E'.map fun D => D.comap $ s'.proj 0)
            ((E.map (·.comap g)).map fun D => D.comap $ s'.proj 0) :=
          MarkedIdealWithBoundary.SameNontrivialBoundary.map _ (by simp) hE
        have hlist : (E.map (·.comap g)).map (fun D => D.comap $ s'.proj 0)
            = (E.map fun D => D.comap $ s.proj 0).map
              (fun D => D.comap $ markedMapToEarlierScheme s s' c 0 hj0 0 hz) := by
          simp only [map_map]
          apply map_congr_left
          intro D _
          simp only [m116]
          rw [← comap_comp, ← comap_comp,
            markedMapToEarlierScheme_comp_projectionToBase]
        have hb0 : s'.boundary 0 = E'.map fun D => D.comap $ s'.proj 0 := by
          rw [s'.boundary_zero, ← s'.proj_zero]
        have hb0s : s.boundary 0 = E.map fun D => D.comap $ s.proj 0 := by
          rw [s.boundary_zero, ← s.proj_zero]
        rw [hb0]
        refine tr_ hmap ?_
        rwa [hlist, ← hb0s, ← hmi]
    | succ n ih =>
        intro hj
        have hn := hj
        have hnle : n ≤ s'.length := le_of_lt hn
        obtain ⟨ihI, ihB⟩ := ih hnle
        have hidxlt := c.idx_lt n hn
        have hstr := c.idx_strictMono n hn
        let _s1 := markedMap s s' c n hnle
        have hcen : s'.center n = (s.center (c.idx n)).comap _s1 := by
          have h0 := c.center_comap n hn
          rwa [toMarkedSequence_center, toMarkedSequence_center] at h0
        let _s0 := markedMapToEarlierScheme s s' c (n + 1) hj (c.idx n + 1) hstr
        have hsq : IsPullback _s0 (s'.map n)
            (s.map (c.idx n)) _s1 := by
          have h0 := c.isPullback_blowupMorphism n hn
          rwa [toMarkedSequence_blowupMorphism, toMarkedSequence_blowupMorphism] at h0
        have hw := hsq.w
        have hexc : (s'.center n).comap (s'.map n)
            = ((s.center (c.idx n)).comap (s.map (c.idx n))).comap
              _s0 := by
          rw [hcen, ← comap_comp, ← comap_comp, hw]
        have hb' := s'.isBlowup n hn
        have hcart : p17 ((s'.center n).comap (s'.map n)) := by
          unfold IsBlowupAlongIdealSheaf at hb'
          exact hb'.1
        have hstepI : s'.ideal (n + 1)
            = (s.ideal (c.idx n + 1)).comap
              _s0 := by
          refine (hcart.pow m).eq_of_mul_eq_mul ?_
          have h1 := s'.ideal_succ n hn
          have h2 := s.ideal_succ (c.idx n) hidxlt
          simp only [p9] at h1 h2
          rw [h1, ihI, ← comap_comp, ← hw,
            comap_comp, ← h2, comap_mul,
            comap_pow, ← hexc]
        have : Flat _s1 := c.flat_map n hnle
        have := hN (c.idx n + 1) hidxlt
        have := hN' (n + 1) hj
        have hST : ∀ D : IdealSheafData (s.obj (c.idx n)),
            (p6 (s.map (c.idx n)) (s.center (c.idx n)) D).comap
                _s0
              = p6 (s'.map n) (s'.center n) (D.comap _s1) := by
          intro D
          rw [comap_strictTransform_of_flat_of_isLocallyNoetherian (s.map (c.idx n))
            _s1 (s'.map n)
            _s0 hsq
            (s.center (c.idx n)) D (s.isBlowup _ hidxlt), ← hcen]
        have hB2 : ((s.boundary (c.idx n)).map (·.comap _s1)).map
              (p6 (s'.map n) (s'.center n)) ++ [(s'.center n).comap (s'.map n)]
            = (s.boundary (c.idx n + 1)).map
              (·.comap _s0) := by
          rw [s.boundary_succ (c.idx n) hidxlt, map_append, map_map, map_map,
            map_cons, map_nil, p9, ← hexc]
          congr 1
          apply map_congr_left
          intro D _
          exact sy_ (hST D)
        have hB1 : SameNontrivialBoundary (s'.boundary (n + 1))
            (((s.boundary (c.idx n)).map (·.comap _s1)).map
              (p6 (s'.map n) (s'.center n)) ++
                [(s'.center n).comap (s'.map n)]) := by
          rw [s'.boundary_succ n hn, p9]
          exact MonomialCenter.sameNontrivialBoundary_append
            (MarkedIdealWithBoundary.SameNontrivialBoundary.map _ (strictTransform_top _ _) ihB)
            (refl _)
        obtain ⟨r1, r2⟩ := hrun (n + 1) hj (c.idx (n + 1)) le_rfl (c.idx n + 1) hstr
          (fun t ht ht2 => c.index_ne_of_index_lt_of_lt_index_succ n hj t (by omega) ht2)
        have hmi :=
          markedMapToEarlierScheme_index s s' c (n + 1) hj
        constructor
        refine tr_ hstepI ?_
        rwa [← hmi]
        refine tr_ hB1 ?_
        rwa [hB2, ← hmi]
  obtain ⟨hmI, hmB⟩ := main s'.length le_rfl
  exact ⟨tr_ hmI (comap_comp_eqToHom (F := s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.schemeAt) s.ideal c.idx_length (c.map s'.length le_rfl)).symm, sameNontrivialBoundary_of_eq hmB (map_comap_comp_eqToHom (F := s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.schemeAt) s.boundary c.idx_length (c.map s'.length le_rfl))⟩
end

end SequenceOfBlowupsPullback





variable {X : Sch}

theorem mem_closure_image_iff_exists_prod_pow {al_ : Type} {N : Type} [CommMonoid N]
    (E : List al_) (f : al_ → N) (y : N) :
    y ∈ Submonoid.closure (f '' {D | D ∈ E}) ↔
      ∃ a : Fin E.length → ℕ, y = ∏ i, f (get E i) ^ a i := by
  constructor
  intro hy
  induction hy using closure_induction with
  | mem z hz =>
      obtain ⟨D, hD, rfl⟩ := hz
      obtain ⟨i, hi⟩ := get_of_mem hD
      refine ⟨fun j => if j = i then 1 else 0, ?_⟩
      have h1 : (∏ j, f (get E j) ^ (if j = i then 1 else 0))
          = f (get E i) ^ (if i = i then 1 else 0) :=
        prod_eq_single i (fun j _ hj => by simp [hj])
          (fun h => absurd (mem_univ i) h)
      rw [h1, hi]
      simp
  | one => exact ⟨fun _ => 0, by simp⟩
  | mul z w hz hw ihz ihw =>
      obtain ⟨a, rfl⟩ := ihz
      obtain ⟨b, rfl⟩ := ihw
      refine ⟨a + b, ?_⟩
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun i _ => by rw [Pi.add_apply, pow_add]
  rintro ⟨a, rfl⟩
  apply Submonoid.prod_mem
  intro i _
  exact pow_mem (m175 $ mem_image_of_mem f $ by simp) _

theorem isMonomialIn_iff_forall_exists_mem_closure (E : Bdy X)
    (M : ISD X) :
    IsMonomialIn E M ↔ ∀ x : ↥X, ∃ U : Opn X, x ∈ U ∧
      M.comap U.i ∈
        Submonoid.closure ((fun D : ISD X => D.comap U.i) '' {D | D ∈ E}) := by
  unfold IsMonomialIn
  exact forall_congr' fun x => exists_congr fun U => and_congr_right fun _ => (mem_closure_image_iff_exists_prod_pow E (fun D : ISD X => cmI D U.i) $ cmI M U.i).symm

theorem mem_nontrivialPart_iff (E : Bdy X)
    (D : ISD X) :
    D ∈ nontrivialPart E ↔ D ∈ E ∧ D ≠ ⊤ := by
  classical
  simp [nontrivialPart, List.mem_filter]

section
variable {E E' : Bdy X}
theorem isMonomialIn_of_mem_of_ne_top
    (h : ∀ D ∈ E, D ≠ ⊤ → D ∈ E') {M} (hM : IsMonomialIn E M) :
    IsMonomialIn E' M := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hM ⊢
  intro x
  obtain ⟨U, hxU, hMU⟩ := hM x
  refine ⟨U, hxU, mp_ mem_closure hMU _ ?_⟩
  rintro y ⟨D, hD, rfl⟩
  by_cases hDtop : D = ⊤
  have h1 : cmI D U.i = 1 := by
    rw [hDtop]
    simp
  show cmI D U.i ∈ _
  rw [h1]
  exact Submonoid.one_mem _
  exact m175 ⟨D, h D hD hDtop, rfl⟩

section
variable (h : {D : ISD X | D ∈ E ∧ D ≠ ⊤} = {D : ISD X | D ∈ E' ∧ D ≠ ⊤})
include h
theorem isMonomialSplitting_of_setOf_mem_ne_top_eq
    {I M N} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting E' I M N := by
  have _i15 : IsMonomialIn E' M := by
    refine isMonomialIn_of_mem_of_ne_top (fun D hD hDtop => ?_) hs.monomial
    have hmem : D ∈ {D : ISD X | D ∈ E ∧ D ≠ ⊤} := ⟨hD, hDtop⟩
    rw [h] at hmem
    exact an1 hmem
  refine ⟨hs.eq_mul, ?_, _i15, ?_⟩
  intro x hx
  obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 $ hs.monomial_support hx
  have hDtop : D ≠ ⊤ := by
    intro hDt
    rw [(eq_top_iff_support_eq_empty D).1 hDt] at hxD
    simp at hxD
  have hmem : D ∈ {D : ISD X | D ∈ E ∧ D ≠ ⊤} := ⟨hD, hDtop⟩
  rw [h] at hmem
  exact Set.mem_iUnion₂.2 ⟨D, an1 hmem, hxD⟩
  intro D hD C hC hCsubD hCmax
  by_cases hDtop : D = ⊤
  exfalso
  obtain ⟨y, hy⟩ := hC.nonempty
  have hy' := hCsubD hy
  rw [(eq_top_iff_support_eq_empty D).1 hDtop] at hy'
  simp at hy'
  have hmem : D ∈ {D : ISD X | D ∈ E' ∧ D ≠ ⊤} := ⟨hD, hDtop⟩
  rw [← h] at hmem
  exact hs.transversal D hmem.1 C hC hCsubD hCmax
end

theorem MarkedIdealWithBoundary.SameNontrivialBoundary.setOf_mem_ne_top_eq
    (h : SameNontrivialBoundary E E') :
    {D : ISD X | D ∈ E ∧ D ≠ ⊤} = {D : ISD X | D ∈ E' ∧ D ≠ ⊤} := by
  have hE :=
    (sameNontrivialBoundary_iff E E').1 h
  ext D
  constructor
  intro hD
  have hD' := (mem_nontrivialPart_iff E D).2 hD
  rw [hE] at hD'
  exact (mem_nontrivialPart_iff E' D).1 hD'
  intro hD
  have hD' := (mem_nontrivialPart_iff E' D).2 hD
  rw [← hE] at hD'
  exact (mem_nontrivialPart_iff E D).1 hD'

theorem isMonomialSplitting_congr
    (h : SameNontrivialBoundary E E') I M N :
    IsMonomialSplitting E I M N ↔ IsMonomialSplitting E' I M N :=
  ⟨fun hs => isMonomialSplitting_of_setOf_mem_ne_top_eq h.setOf_mem_ne_top_eq hs,
    fun hs => isMonomialSplitting_of_setOf_mem_ne_top_eq h.symm.setOf_mem_ne_top_eq hs⟩
end

theorem coe_support_top_eq_empty {X : Sch} :
    (support (⊤ : ISD X) : Set ↥X) = ∅ :=
  (eq_top_iff_support_eq_empty
    (⊤)).1 rfl

namespace IsMonomialSplitting

variable {E : Bdy X} {I M N : ISD X}

section
variable (h : IsMonomialSplitting E I M N)
include h
theorem le_nonMonomial : I ≤ N := by
  rw [h.eq_mul, le_def]
  intro U
  rw [ideal_mul]
  exact mul_le_right

theorem support_nonMonomial_subset :
    (↑N.support : Set ↥X) ⊆ (↑I.support : Set ↥X) := by
  intro x hx
  refine (mem_support_iff_stalkIdeal_ne_top I x).2 ?_
  intro hI
  apply (mem_support_iff_stalkIdeal_ne_top N x).1 hx
  have hle := stalkIdeal_mono h.le_nonMonomial x
  rw [hI] at hle
  exact top_le_iff.1 hle

theorem nonzeroOnComponents_nonMonomial
    (hI : NonzeroOnComponents I) : NonzeroOnComponents N := by
  rw [nonzeroOnComponents_iff] at hI ⊢
  intro T hT hTsub
  exact hI T hT $ hTsub.trans h.support_nonMonomial_subset
end

theorem orderAt_eq_add {k : Type} [Field k] [CharZero k] {Y : Sch}
    (p : Y ⟶ Sp k) [Smooth p]
    {E : Bdy Y} {I M N : ISD Y}
    (h : IsMonomialSplitting E I M N) (x : ↥Y) :
    orderAt I x = orderAt M x + orderAt N x := by
  rw [h.eq_mul]
  exact orderAt_mul k p M N x

private theorem idealSheafData_comap_prod {Z W : Sch} (f : W ⟶ Z) {ka_ : Type}
    (s : Finset ka_) (J : ka_ → ISD Z) :
    (∏ i ∈ s, J i).comap f = ∏ i ∈ s, (J i).comap f := by
  induction s using cons_induction
  rw [prod_empty, prod_empty, one_eq_top,
    comap_top, one_eq_top]
  rename_i b t hb ih
  rw [Finset.prod_cons, Finset.prod_cons, comap_mul, ih]

theorem exists_comap_eq_prod_pow_of_orderAt_eq_zero (h : IsMonomialSplitting E I M N) {x : ↥X}
    (hx : orderAt N x = 0) :
    ∃ (U : Opn X) (e : Fin E.length → ℕ), x ∈ U ∧
      I.comap U.i = ∏ i : Fin E.length, ((get E i).comap U.i) ^ e i := by
  obtain ⟨U, hxU, a, haM⟩ := (h.monomial) x
  have hxN := (orderAt_eq_zero_iff_not_mem_support N x).1 hx
  let _a0 := N.supp
  obtain ⟨U0_, hU0_⟩ : ∃ U0_ : Opn X, (U0_ : Set X) = _a0ᶜ :=
    ⟨⟨_a0ᶜ, N.support.2.isOpen_compl⟩, rfl⟩
  have hx0 : x ∈ (U0_ : Set X) := by
    rwa [hU0_]
  have hxV : x ∈ U ⊓ U0_ := by
    have hmem : x ∈ ((U ⊓ U0_ : Opn X) : Set X) := by
      rw [coe_inf]
      exact ⟨hxU, hx0⟩
    exact hmem
  have hle : U ⊓ U0_ ≤ U := inf_le_left
  have hcomp : X.homOfLE hle ≫ U.i = (U ⊓ U0_).i := by simp
  have restr : ∀ J : ISD X,
      (J.comap U.i).comap (X.homOfLE hle) = J.comap (U ⊓ U0_).i := by
    intro J
    rw [← hcomp, m56]
  have hNtop : N.comap (U ⊓ U0_).i = ⊤ := by
    refine p39 _ N ?_
    intro y hy
    have hy1 : ((U ⊓ U0_).i y) ∈ ((U ⊓ U0_ : Opn X) : Set X) := y.2
    rw [coe_inf, hU0_] at hy1
    exact hy1.2 hy
  have hM : M.comap (U ⊓ U0_).i
      = ∏ i : Fin E.length, ((get E i).comap (U ⊓ U0_).i) ^ a i := by
    rw [← restr M, haM, idealSheafData_comap_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [comap_pow, restr]
  refine ⟨U ⊓ U0_, a, hxV, ?_⟩
  rw [h.eq_mul, comap_mul, hNtop,
    ← one_eq_top, mul_one, hM]

end IsMonomialSplitting

namespace PrincipalizationGeometryHypotheses

section
variable (hG : PrincipalizationGeometryHypotheses) (T : MarkedIdealWithBoundary) (hT : T.IsAdmissible)
include hG hT
theorem isMonomialSplitting_monomialPart_nonMonomialPart :
    IsMonomialSplitting T.boundary T.ideal (monomialPart T.boundary T.ideal)
      (nonMonomialPart T.boundary T.ideal) := by
  obtain ⟨M, N, h⟩ := hG.splitting_exists T hT
  exact EmbeddedResolution.isMonomialSplitting_monomialPart_nonMonomialPart T.boundary T.ideal ⟨(M, N), h⟩

theorem nonMonomialPart_eq_of_isMonomialSplitting
    (M N : tISD T) (h : IsMonomialSplitting T.boundary T.ideal M N) :
    nonMonomialPart T.boundary T.ideal = N :=
  right $ hG.splitting_unique T hT _ _ M N (hG.isMonomialSplitting_monomialPart_nonMonomialPart T hT) h

theorem nonMonomialPart_eq_ideal_of_boundary_eq_nil (hE : boundary T = []) :
    nonMonomialPart T.boundary T.ideal = ideal T := by
  refine nonMonomialPart_eq_of_isMonomialSplitting hG T hT ⊤ T.ideal ?_
  rw [hE]
  refine ⟨?_, ?_, ?_, ?_⟩
  rw [← one_eq_top, one_mul]
  rw [coe_support_top_eq_empty]
  exact empty_subset _
  intro x
  refine ⟨⊤, by simp, fun _ => 0, ?_⟩
  rw [comap_top, ← one_eq_top]
  exact sy_ $ prod_univ_zero _
  intro D hD
  exact absurd hD $ by simp

theorem nonMonomialPart_comap_of_sameNontrivialBoundary (Y : Sch) q (h : Y ⟶ scheme T)
    [Smooth h] (hq : h ≫ structMap T = q)
    (hT' : (T.pbA q h).IsAdmissible) E'
    (hE : SameNontrivialBoundary (T.pbA q h).boundary E')
    (hT'' : (T.pbB q h E').IsAdmissible) :
    nonMonomialPart E' (T.ideal.comap h) = (nonMonomialPart T.boundary T.ideal).comap h := by
  let _a0 := monomialPart T.boundary T.ideal
  let _a1 := nonMonomialPart T.boundary T.ideal
  have h3 :=
    by
    let T := T.pbA q h
    exact sy_ $ nonMonomialPart_eq_of_isMonomialSplitting hG T hT' _ _ $ (isMonomialSplitting_congr hE T.ideal (monomialPart E' T.ideal) $ nonMonomialPart E' T.ideal).mpr $ hG.isMonomialSplitting_monomialPart_nonMonomialPart (tWB T E') hT''
  exact tr_ h3 $ nonMonomialPart_eq_of_isMonomialSplitting hG (T.pbA q h) hT' (cmI _a0 h) (cmI _a1 h) $ hG.splitting_smooth_pullback T hT Y q h hq hT' _a0 _a1 $ hG.isMonomialSplitting_monomialPart_nonMonomialPart T hT
end

end PrincipalizationGeometryHypotheses

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {N : ISD X} {mu_ : ℕ} {E : Bdy X}

def MarkedSequenceOfBlowups.monomialFactor (s : MarkedSequenceOfBlowups p N mu_ E) (M : ISD X) (m : ℕ) :
    ∀ i : ℕ, IdealSheafData $ s.schemeAt i
  | 0 => M.comap s.isoZero.hom
  | i + 1 =>
      (MarkedSequenceOfBlowups.monomialFactor s M m i).comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (mu_ - m)

def MarkedSequenceOfBlowups.controlledTransform (s : MarkedSequenceOfBlowups p N mu_ E) (I : ISD X) (m : ℕ) :
    ∀ i : ℕ, IdealSheafData $ s.schemeAt i
  | 0 => I.comap s.isoZero.hom
  | i + 1 =>
      residualByPow ((MarkedSequenceOfBlowups.controlledTransform s I m i).comap $ s.transitionMapSucc i) (s.exceptionalDivisor i) m

section
variable (s : MarkedSequenceOfBlowups p N mu_ E)
@[simp]
theorem MarkedSequenceOfBlowups.monomialFactor_zero (M : ISD X)
    (m : ℕ) : MarkedSequenceOfBlowups.monomialFactor s M m 0 = M.comap s.isoZero.hom :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.monomialFactor_succ (M : ISD X)
    (m i : ℕ) :
    MarkedSequenceOfBlowups.monomialFactor s M m (i + 1) =
      (MarkedSequenceOfBlowups.monomialFactor s M m i).comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (mu_ - m) :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledTransform_zero (I : ISD X)
    (m : ℕ) : MarkedSequenceOfBlowups.controlledTransform s I m 0 = I.comap s.isoZero.hom :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledTransform_succ (I : ISD X)
    (m i : ℕ) :
    MarkedSequenceOfBlowups.controlledTransform s I m (i + 1) =
      residualByPow ((MarkedSequenceOfBlowups.controlledTransform s I m i).comap $ s.transitionMapSucc i) (s.exceptionalDivisor i) m :=
  rfl
end

end

section

variable {A B : Sch}

section
variable {A' B' : Sch} (f : A' ⟶ B')
theorem support_comap_coe (I : ISD B') :
    (↑(I.comap f).support : Set ↥A') = ⇑f.base ⁻¹' (↑I.support : Set ↥B') := by
  rw [m19]
  rfl

theorem comap_one :
    (1 : ISD B').comap f = 1 := by
  simp
end

section
variable {Y : Sch}
theorem support_mul_subset (P Q : ISD Y) :
    (↑(P * Q).support : Set ↥Y) ⊆ (↑P.support : Set ↥Y) ∪ (↑Q.support : Set ↥Y) := by
  rw [support_mul]
  exact Set.Subset.rfl

private theorem support_pow_subset (P : ISD Y) (n : ℕ) :
    (↑(P ^ n).support : Set ↥Y) ⊆ (↑P.support : Set ↥Y) := by
  rcases eq_or_ne n 0 with rfl | hn
  intro x hx
  refine absurd ?_ $ (mem_support_iff_stalkIdeal_ne_top (P ^ 0) x).1 hx
  simp_all
  rwa [support_pow]

theorem support_subset_support_mul_right (P Q : ISD Y) :
    (↑Q.support : Set ↥Y) ⊆ (↑(P * Q).support : Set ↥Y) :=by simp_all
section
variable {C S : Set ↥Y}
theorem isIrreducibleComponentOf_of_maximal (h1 : IsIrreducible C)
    (h2 : C ⊆ S) (h3 : ∀ C', IsIrreducible C' → C' ⊆ S → C ⊆ C' → C' ⊆ C) :
    IsIrreducibleComponentOf C S := by
  unfold IsIrreducibleComponentOf
  exact ⟨h1, h2, fun C' hC' hCle hC'S => m15 (h3 C' hC' hC'S hCle) hCle⟩

theorem isIrreducible_subset_maximal_of_isIrreducibleComponentOf (h : IsIrreducibleComponentOf C S) :
    IsIrreducible C ∧ C ⊆ S ∧ ∀ C', IsIrreducible C' → C' ⊆ S → C ⊆ C' → C' ⊆ C := by
  unfold IsIrreducibleComponentOf at h
  exact ⟨an1 h, h.2.1, fun C' hC' hC'S hCle => (h.2.2 C' hC' hCle hC'S).subset⟩
end

theorem comap_homOfLE {U V : Opn Y} (h : U ≤ V)
    (D : ISD Y) : (D.comap V.i).comap (Y.homOfLE h) = D.comap U.i := by
  rw [← comap_comp, Scheme.homOfLE_ι]

theorem comap_homOfLE_mem_closure_comap {E : Bdy Y}
    {U V : Opn Y} (h : U ≤ V) :
    ∀ y ∈ Submonoid.closure ((fun D : ISD Y => D.comap V.i) '' {D | D ∈ E}),
      y.comap (Y.homOfLE h) ∈
        Submonoid.closure ((fun D : ISD Y => D.comap U.i) '' {D | D ∈ E}) := by
  intro y hy
  induction hy using closure_induction with
  | mem D hD =>
      obtain ⟨D0_, hD0_, rfl⟩ := hD
      rw [comap_homOfLE]
      exact m175 ⟨D0_, hD0_, rfl⟩
  | one =>
      rw [comap_one]
      exact one_mem _
  | mul a b _ _ iha ihb =>
      rw [comap_mul]
      exact mul_mem iha ihb

theorem isMonomialIn_of_mem {E : Bdy Y}
    {D : ISD Y} (hD : D ∈ E) : IsMonomialIn E D := by
  rw [isMonomialIn_iff_forall_exists_mem_closure]
  intro x
  exact ⟨⊤, trivial, m175 ⟨D, hD, rfl⟩⟩

theorem isMonomialIn_mul (E : Bdy Y)
    {P Q : ISD Y} (hP : IsMonomialIn E P) (hQ : IsMonomialIn E Q) :
    IsMonomialIn E $ P * Q := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hP hQ ⊢
  intro x
  obtain ⟨U1, hx1, h1⟩ := hP x
  obtain ⟨U2, hx2, h2⟩ := hQ x
  refine ⟨U1 ⊓ U2, ⟨hx1, hx2⟩, ?_⟩
  have k1 := comap_homOfLE_mem_closure_comap (E := E) (inf_le_left : U1 ⊓ U2 ≤ U1) _ h1
  have k2 := comap_homOfLE_mem_closure_comap (E := E) (inf_le_right : U1 ⊓ U2 ≤ U2) _ h2
  rw [comap_homOfLE] at k1 k2
  rw [comap_mul]
  exact mul_mem k1 k2

theorem isMonomialIn_pow (E : Bdy Y)
    {P : ISD Y} (hP : IsMonomialIn E P) (n : ℕ) : IsMonomialIn E $ P ^ n := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hP ⊢
  intro x
  obtain ⟨U, hxU, h⟩ := hP x
  refine ⟨U, hxU, ?_⟩
  rw [comap_pow]
  exact pow_mem h n

theorem isMonomialIn_of_forall_mem {L1 L2 : Bdy Y}
    (h : ∀ D ∈ L1, IsMonomialIn L2 D) {P : ISD Y} (hP : IsMonomialIn L1 P) :
    IsMonomialIn L2 P := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at hP ⊢
  intro x
  obtain ⟨U, hxU, hU⟩ := hP x
  have _i16 : ∀ (L : Bdy Y), (∀ D ∈ L, IsMonomialIn L2 D) → ∀ x : Y, ∃ V : Opn Y, x ∈ V ∧ ∀ D ∈ L, cmI D V.i ∈ Submonoid.closure ((fun D' : ISD Y => cmI D' V.i) '' {D' | D' ∈ L2}) := by
    intro L
    induction L with
    | nil =>
        intro _ x
        refine ⟨⊤, trivial, ?_⟩
        intro D hD
        exact absurd hD $ by simp
    | cons D0 L ih =>
        intro hall x
        obtain ⟨Vleft, hxVleft, hV1⟩ := ih (fun D hD => hall D $ by simp [hD]) x
        obtain ⟨Vright, hxVright, hV2⟩ :=
          (isMonomialIn_iff_forall_exists_mem_closure L2 D0).1 (hall D0 $ by simp) x
        refine ⟨Vleft ⊓ Vright, ⟨hxVleft, hxVright⟩, ?_⟩
        intro D hD
        rcases mem_cons.1 hD with rfl | hD'
        have hk := comap_homOfLE_mem_closure_comap (E := L2) (inf_le_right : Vleft ⊓ Vright ≤ Vright) _ hV2
        rwa [comap_homOfLE] at hk
        have hk := comap_homOfLE_mem_closure_comap (E := L2) (inf_le_left : Vleft ⊓ Vright ≤ Vleft) _ $ hV1 D hD'
        rwa [comap_homOfLE] at hk
  obtain ⟨Vinter, hxW, hW⟩ := _i16 L1 h x
  refine ⟨U ⊓ Vinter, ⟨hxU, hxW⟩, ?_⟩
  have h1 := comap_homOfLE_mem_closure_comap (E := L1) (inf_le_left : U ⊓ Vinter ≤ U) _ hU
  rw [comap_homOfLE] at h1
  refine closure_le.2 ?_ h1
  rintro y ⟨D, hD, rfl⟩
  have h2 := comap_homOfLE_mem_closure_comap (E := L2) (inf_le_right : U ⊓ Vinter ≤ Vinter) _ $ hW D hD
  rwa [comap_homOfLE] at h2

theorem support_subset_union_of_locally_eq_mul_pow (D' A' B' : ISD Y)
    (h : ∀ x : ↥Y, ∃ (U : Opn Y) (ep_ : ℕ), x ∈ U ∧
      D'.comap U.i = A'.comap U.i * B'.comap U.i ^ ep_) :
    (↑D'.support : Set ↥Y) ⊆ (↑A'.support : Set ↥Y) ∪ (↑B'.support : Set ↥Y) := by
  intro x hx
  by_contra hcon
  rw [mem_union, not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨U, ep_, hxU, heq⟩ := h x
  have hA0 := (orderAt_eq_zero_iff_not_mem_support A' x).2 hA
  have hB0 := (orderAt_eq_zero_iff_not_mem_support B' x).2 hB
  let _m0 := (⟨x, hxU⟩ : U)
  have hAy : orderAt (cmI A' U.i) _m0 = 0 := by
    rwa [orderAt_comap_of_isOpenImmersion U.i A' _m0]
  have hBy : orderAt (cmI B' U.i) _m0 = 0 := by
    rwa [orderAt_comap_of_isOpenImmersion U.i B' _m0]
  have hDy : orderAt (D'.comap U.i) _m0 = 0 := by
    refine (orderAt_eq_zero_iff_not_mem_support (D'.comap U.i) _m0).2 ?_
    rw [heq]
    intro hmem
    rcases support_mul_subset (cmI A' U.i) (cmI B' U.i ^ ep_) hmem with h1 | h2
    exact ((orderAt_eq_zero_iff_not_mem_support (cmI A' U.i) _m0).1 hAy) h1
    exact (orderAt_eq_zero_iff_not_mem_support (cmI B' U.i) _m0).1 hBy $ support_pow_subset (cmI B' U.i) ep_ h2
  rw [orderAt_comap_of_isOpenImmersion U.i D' _m0] at hDy
  exact (orderAt_eq_zero_iff_not_mem_support D' x).1 hDy hx

theorem isMonomialIn_of_locally_eq_mul_pow (L : Bdy Y)
    (D' A' B' : ISD Y) (hA : A' ∈ L) (hB : B' ∈ L)
    (h : ∀ x : ↥Y, ∃ (U : Opn Y) (ep_ : ℕ), x ∈ U ∧
      D'.comap U.i = A'.comap U.i * B'.comap U.i ^ ep_) :
    IsMonomialIn L D' := by
  rw [isMonomialIn_iff_forall_exists_mem_closure]
  intro x
  obtain ⟨U, ep_, hxU, heq⟩ := h x
  refine ⟨U, hxU, ?_⟩
  have hA2 : cmI A' U.i ∈
      Submonoid.closure ((fun D0 : ISD Y => cmI D0 U.i) '' {D0 | D0 ∈ L}) :=
    m175 ⟨A', hA, rfl⟩
  have hB2 : cmI B' U.i ∈
      Submonoid.closure ((fun D0 : ISD Y => cmI D0 U.i) '' {D0 | D0 ∈ L}) :=
    m175 ⟨B', hB, rfl⟩
  rw [heq]
  exact mul_mem hA2 $ pow_mem hB2 ep_
end

theorem IsMonomialIn.comap (f : A ⟶ B) {E : Bdy B} {M : ISD B}
    (h : IsMonomialIn E M) :
    IsMonomialIn (map (fun D : ISD B => D.comap f) E) $ M.comap f := by
  rw [isMonomialIn_iff_forall_exists_mem_closure] at h ⊢
  intro x
  obtain ⟨U, hxU, hmem⟩ := h $ bsM f x
  refine ⟨pre f U, hxU, ?_⟩
  let _a0 := f.resLE U (pre f U) le_rfl
  have key : ∀ J : ISD B,
      (J.comap f).comap (pre f U).i = (J.comap U.i).comap _a0 := by
    intro J
    rw [← comap_comp, ← comap_comp, q4 f le_rfl]
  have main : ∀ y ∈ Submonoid.closure ((fun D : ISD B => D.comap U.i) '' {D | D ∈ E}),
      y.comap _a0 ∈
        Submonoid.closure ((fun D : ISD A => D.comap (pre f U).i) ''
          {D | D ∈ map (fun D : ISD B => D.comap f) E}) := by
    intro y hy
    induction hy using closure_induction with
    | mem D hD =>
        obtain ⟨D0_, hD0_, rfl⟩ := hD
        rw [← key D0_]
        exact m175 ⟨D0_.comap f, mem_map.2 ⟨D0_, hD0_, rfl⟩, rfl⟩
    | one =>
        rw [comap_one]
        exact one_mem _
    | mul a b _ _ iha ihb =>
        rw [comap_mul]
        exact mul_mem iha ihb
  rw [key M]
  exact main _ hmem

theorem IsMonomialSplitting.comap_iso (e : A ≅ B) {E : Bdy B}
    {I M N : ISD B} (h : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (map (fun D : ISD B => D.comap e.hom) E) (I.comap e.hom)
      (M.comap e.hom) $ N.comap e.hom := by
  have hAB : ∀ x, bsM (isoI e) (bsM (isoH e) x) = x := by
    intro x
    simp
  have hhomInv : ∀ y, bsM (isoH e) (bsM (isoI e) y) = y := by
    intro y
    simp
  refine ⟨?_, ?_, h.monomial.comap e.hom, ?_⟩
  rw [h.eq_mul, comap_mul]
  intro x hx
  rw [support_comap_coe] at hx
  obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 $ h.monomial_support hx
  refine Set.mem_iUnion₂.2 ⟨cmI D e.hom, mem_map.2 ⟨D, hD, rfl⟩, ?_⟩
  rwa [support_comap_coe]
  rintro D hD C hCirr hCsubD hCmax hCN
  obtain ⟨D0_, hD0_, rfl⟩ := mem_map.1 hD
  rw [support_comap_coe] at hCsubD
  rw [support_comap_coe] at hCN
  refine h.transversal D0_ hD0_ (e.hom.base '' C) (hCirr.image _ ((m207 e).continuous).continuousOn)
    (image_subset_iff.2 hCsubD) ?_ $ image_subset_iff.2 hCN
  intro C' hC'irr hC'D hCle
  have hsub : e.inv.base '' C' ⊆ (support (cmI D0_ e.hom) : Set A) := by
    rw [support_comap_coe]
    rintro x ⟨y, hy, rfl⟩
    simp [hhomInv]
    exact hC'D hy
  have hCsub : C ⊆ e.inv.base '' C' := by
    intro x hx
    exact ⟨bsM (isoH e) x, hCle ⟨x, hx, rfl⟩, hAB x⟩
  intro y hy
  exact ⟨bsM (isoI e) y, (hCmax (e.inv.base '' C') (hC'irr.image _ ((m207 e).symm.continuous).continuousOn) hsub hCsub) ⟨y, hy, rfl⟩, hhomInv y⟩

end

section

section
variable (T : MarkedIdealWithBoundary) (N : tISD T) (mu_ : ℕ)
def MarkedIdealWithBoundary.withIdealAndMult :
    MarkedIdealWithBoundary :=
  { base := T.base
    instField := T.instField
    scheme := scheme T
    structMap := structMap T
    ideal := N
    mult := mu_
    boundary := boundary T }

@[simp]
theorem MarkedIdealWithBoundary.withIdealAndMult_baseField : (T.withIdealAndMult N mu_).base = T.base :=
  rfl

@[simp]
theorem MarkedIdealWithBoundary.withIdealAndMult_scheme : scheme (T.withIdealAndMult N mu_) = scheme T :=
  rfl

@[simp]
theorem MarkedIdealWithBoundary.withIdealAndMult_structureMorphism : structMap (T.withIdealAndMult N mu_) = structMap T :=
  rfl

@[simp]
theorem MarkedIdealWithBoundary.withIdealAndMult_ideal : ideal (T.withIdealAndMult N mu_) = N :=
  rfl

@[simp]
theorem MarkedIdealWithBoundary.withIdealAndMult_mult : mult (T.withIdealAndMult N mu_) = mu_ :=
  rfl

@[simp]
theorem MarkedIdealWithBoundary.withIdealAndMult_boundary : boundary (T.withIdealAndMult N mu_) = boundary T :=
  rfl
end

theorem MarkedIdealWithBoundary.IsAdmissible.withIdealAndMult {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible)
    {M N : tISD T} (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {mu_ : ℕ} (hmu_ : mult T ≤ mu_) :
    (T.withIdealAndMult N mu_).IsAdmissible :=
  { charZero := hT.charZero
    locallyOfFiniteType := hT.locallyOfFiniteType
    nonzeroOnComponents := hsplit.nonzeroOnComponents_nonMonomial hT.nonzeroOnComponents
    one_le_mult := le_trans hT.one_le_mult hmu_
    quasiCompact := hT.quasiCompact
    smooth := hT.smooth
    snc := hT.snc }

end

section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {N : ISD X} {mu_ : ℕ} {E : Bdy X}

section
variable (s : MarkedSequenceOfBlowups p N mu_ E)
theorem exceptionalDivisor_eq_exceptionalIdeal (i : ℕ) :
    s.exceptionalDivisor i = exceptionalIdeal (s.transitionMapSucc i) (s.center i) := by
  rw [exceptionalDivisor_eq, p9]

theorem exceptionalDivisor_pow_mul_comap_mul_eq_comap (m : ℕ) (hm : m ≤ mu_)
    (i : ℕ) (hi : i < s.length) (Ci Mi : IdealSheafData $ s.schemeAt i)
    (h : Ci = Mi * s.ideal i) :
    s.exceptionalDivisor i ^ m *
        (Mi.comap (s.transitionMapSucc i) * s.exceptionalDivisor i ^ (mu_ - m) * s.ideal (i + 1))
      = Ci.comap (s.transitionMapSucc i) := by
  let _a1 := cmI (s.ideal i) $ s.transitionMapSucc i
  let _a2 := s.ideal $ i + 1
  have hid : s.exceptionalDivisor i ^ mu_ * _a2 = _a1 := by
    rw [exceptionalDivisor_eq_exceptionalIdeal]
    exact s.ideal_succ i hi
  let _a0 := s.exceptionalDivisor i ^ (mu_ - m)
  let _a4 := s.exceptionalDivisor i ^ m
  have hF : _a4 * _a0 = s.exceptionalDivisor i ^ mu_ := by
    rw [← pow_add, add_sub_cancel' hm]
  let _a3 := Mi.comap $ s.transitionMapSucc i
  calc _a4 *
          (_a3 * _a0 * _a2)
      = _a3 *
          ((_a4 * _a0) * _a2) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ = _a3 * _a1 := by rw [hF, hid]
    _ = Ci.comap (s.transitionMapSucc i) := by rw [h, comap_mul]

theorem orderAt_eq_of_mem_center_support
    (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (mu_ : ENat))
    (i : ℕ) (hi : i < s.length) (x : ↥(s.schemeAt i)) (hx : x ∈ (s.center i).support) :
    orderAt (s.ideal i) x = (mu_ : ENat) :=
  le_antisymm (hord i (le_of_lt hi) x) $ (mem_orderAtLeastLocus_iff _ _ _).1 $ s.center_order i hi hx

section
variable (I : ISD X) (m i : ℕ)
theorem controlledTransform_eq_sequenceData :
    MarkedSequenceOfBlowups.controlledTransform s I m i
      = (s.toBsd).controlledTransform I m i := by
  let _a0 := s.toBsd
  induction i with
  | zero =>
      exact sy_ $ p53 _a0 I m
  | succ n ih =>
      exact m32 (congrArg (fun J : ISD (s.schemeAt n) => residualByPow (cmI J $ s.transitionMapSucc n) (s.exceptionalDivisor n) m) ih) (BlowupSequenceData.controlledTransform_succ _a0 I m n).symm

theorem exceptionalDivisor_pow_mul_controlledTransform_succ
    (h : ∃ Bd, s.exceptionalDivisor i ^ m * Bd
        = (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i)) :
    s.exceptionalDivisor i ^ m * MarkedSequenceOfBlowups.controlledTransform s I m (i + 1)
      = (MarkedSequenceOfBlowups.controlledTransform s I m i).comap (s.transitionMapSucc i) := by
  obtain ⟨Bd, hBd⟩ := h
  let _a0 := congrArg (fun J : IdealSheafData (s.schemeAt i) => J.comap $ s.transitionMapSucc i)
    (controlledTransform_eq_sequenceData s I m i)
  have hd := BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ (s.toBsd)
    I m i ⟨Bd, tr_ hBd _a0⟩
  exact tr_ (congrArg (fun J : IdealSheafData (s.schemeAt $ i + 1) => s.exceptionalDivisor i ^ m * J)
      (controlledTransform_eq_sequenceData s I m $ i + 1))
    (tr_ hd _a0.symm)
end
end

theorem subset_orderAtLeastLocus_of_eq_mul {Y : Sch} (Mi Ni Ci : ISD Y)
    (h : Ci = Mi * Ni) (m : ℕ) (S : Set ↥Y) (hS : S ⊆ orderAtLeastLocus Ni m) :
    S ⊆ orderAtLeastLocus Ci m := by
  intro x hx
  have h2 := add_orderAt_le_orderAt_mul Mi Ni x
  rw [← h] at h2
  exact (mem_orderAtLeastLocus_iff _ _ _).2 $ le_trans ((mem_orderAtLeastLocus_iff _ _ _).1 $ hS hx) $ le_trans le_add_self h2

end

section

section
variable (hG : PrincipalizationGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) {M N} (hsplit : IsMonomialSplitting T.boundary T.ideal M N) {mu_} (hmu_ : T.mult ≤ mu_) (s : MarkedSequenceOfBlowups T.structMap N mu_ T.boundary) (hord : ∀ i ≤ s.length, ∀ x : ↥(s.schemeAt i), orderAt (s.ideal i) x ≤ (mu_ : ENat))
include hG hT hsplit hmu_ hord
theorem isMonomialSplitting_controlledTransform_monomialFactor
    (i : ℕ) (hi : i ≤ s.length) :
    IsMonomialSplitting (s.boundary i) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i)
        (MarkedSequenceOfBlowups.monomialFactor s M T.mult i) (s.ideal i) ∧
      (i < s.length →
        (∀ x ∈ (s.center i).support, orderAt (s.ideal i) x = (mu_ : ENat)) ∧
        (↑(s.center i).support : CSet (s.schemeAt i)) ⊆
          orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) T.mult ∧
        ∃ Bd : IdealSheafData (s.schemeAt (i + 1)),
          s.exceptionalDivisor i ^ T.mult * Bd =
            (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i).comap (s.transitionMapSucc i)) := by
  have hsplit_all : ∀ j, j ≤ s.length →
      IsMonomialSplitting (s.boundary j) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult j)
        (MarkedSequenceOfBlowups.monomialFactor s M T.mult j) (s.ideal j) := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [s.boundary_zero, s.ideal_zero]
        exact hsplit.comap_iso s.isoZero
    | succ n ih =>
        intro hn
        have hn' := hn
        have hsp := ih $ le_of_lt hn'
        have hdiv :=
          exceptionalDivisor_pow_mul_comap_mul_eq_comap s T.mult hmu_ n hn' _ _ hsp.eq_mul
        have heq : MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult (n + 1)
            = MarkedSequenceOfBlowups.monomialFactor s M T.mult (n + 1) * s.ideal (n + 1) := by
          have _i17 : p17 (s.exceptionalDivisor n) := by
            rw [exceptionalDivisor_eq_exceptionalIdeal]
            exact isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal $ s.isBlowupAlongIdealSheaf_blowupMorphism n hn'
          refine eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul _i17
            T.mult ?_
          rw [exceptionalDivisor_pow_mul_controlledTransform_succ s T.ideal T.mult n ⟨_, hdiv⟩, ← hdiv]
          simp [MarkedSequenceOfBlowups.monomialFactor_succ, mul_comm, mul_left_comm]
        have hTn := p38 effectiveCartierSupportContainsNoComponent (hT.withIdealAndMult hsplit hmu_) s n $ le_of_lt hn'
        have hsm : Smooth ((s.center n).si ≫ s.projectionToSpec n) := by
          rw [projectionToSpec_eq]
          exact s.center_smooth n hn'
        have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.center n) (s.boundary n) := by
          rw [projectionToSpec_eq]
          exact s.center_snc n hn'
        have hbl := s.isBlowupAlongIdealSheaf_blowupMorphism n hn'
        have hbnd := s.boundary_succ n hn'
        have hExcMem : p5 (s.transitionMapSucc n) (s.center n) ∈ s.boundary (n + 1) := by
          rw [hbnd]
          simp
        have hExcMem' : s.exceptionalDivisor n ∈ s.boundary (n + 1) := by
          rwa [exceptionalDivisor_eq_exceptionalIdeal]
        have hSTmem : ∀ D0_ ∈ s.boundary n,
            p6 (s.transitionMapSucc n) (s.center n) D0_ ∈ s.boundary (n + 1) := by
          intro D0_ hD0_
          rw [hbnd]
          exact mem_append_left _ (mem_map.2 ⟨D0_, hD0_, rfl⟩)
        have hfac : ∀ D0_ ∈ s.boundary n, ∀ x' : (s.schemeAt (n + 1)),
            ∃ (U : Opens (s.schemeAt (n + 1))) (ep_ : ℕ), x' ∈ U ∧
              (D0_.comap (s.transitionMapSucc n)).comap U.i =
                (p6 (s.transitionMapSucc n) (s.center n) D0_).comap U.i *
                  (p5 (s.transitionMapSucc n) (s.center n)).comap U.i ^ ep_ := by
          intro D0_ hD0_ x'
          obtain ⟨U, ep_, hxU, _, _, hEq⟩ :=
            hG.monomialInputs.blowup_total_transform _ hTn (s.center n) hsm hsnc _
              (s.transitionMapSucc n) hbl D0_ hD0_ x'
          exact ⟨U, ep_, hxU, hEq⟩
        have hmonD : ∀ D0_ ∈ s.boundary n,
            IsMonomialIn (s.boundary (n + 1)) (D0_.comap (s.transitionMapSucc n)) := by
          intro D0_ hD0_
          exact isMonomialIn_of_locally_eq_mul_pow _ _ _ _ (hSTmem D0_ hD0_) hExcMem $ hfac D0_ hD0_
        have hmonM : IsMonomialIn (s.boundary (n + 1))
            ((MarkedSequenceOfBlowups.monomialFactor s M T.mult n).comap (s.transitionMapSucc n)) := by
          refine isMonomialIn_of_forall_mem ?_ (hsp.monomial.comap (s.transitionMapSucc n))
          intro D hD
          obtain ⟨D0_, hD0_, rfl⟩ := mem_map.1 hD
          exact hmonD D0_ hD0_
        refine ⟨heq, ?_, ?_, ?_⟩
        intro x hx
        rw [MarkedSequenceOfBlowups.monomialFactor_succ] at hx
        rcases support_mul_subset _ _ hx with hx1 | hx2
        rw [support_comap_coe] at hx1
        obtain ⟨D0_, hD0_, hxD⟩ := Set.mem_iUnion₂.1 $ hsp.monomial_support hx1
        have hx' : x ∈ ((D0_.comap (s.transitionMapSucc n)).support : Set (s.schemeAt (n + 1))) := by
          rwa [support_comap_coe]
        rcases support_subset_union_of_locally_eq_mul_pow _ _ _ (hfac D0_ hD0_) hx' with h1 | h2
        exact Set.mem_iUnion₂.2 ⟨_, hSTmem D0_ hD0_, h1⟩
        exact Set.mem_iUnion₂.2 ⟨_, hExcMem, h2⟩
        exact Set.mem_iUnion₂.2 ⟨_, hExcMem', support_pow_subset _ _ hx2⟩
        rw [MarkedSequenceOfBlowups.monomialFactor_succ]
        exact isMonomialIn_mul _ hmonM $ isMonomialIn_pow _ (isMonomialIn_of_mem hExcMem') _
        intro D hD C hCirr hCsubD hCmax hCsub
        rw [hbnd] at hD
        rcases mem_append.1 hD with hD' | hD'
        obtain ⟨D0_, hD0_, rfl⟩ := mem_map.1 hD'
        obtain ⟨et', C0, hCeq, _, hC0comp, _, hC0eq⟩ :=
          hG.strictTransform_components _ hTn (s.center n) hsm hsnc _ (s.transitionMapSucc n) hbl
            D0_ hD0_ C (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax)
        obtain ⟨hc1, hc2, hc3⟩ := isIrreducible_subset_maximal_of_isIrreducibleComponentOf hC0comp
        have hetC : et' ∈ C := by
          rw [hCeq]
          exact subset_closure $ mem_singleton et'
        have h2 : et' ∈
            (((s.ideal n).comap (s.transitionMapSucc n)).support : Set (s.schemeAt (n + 1))) := by
          rw [← s.ideal_succ n hn']
          exact support_subset_support_mul_right _ _ $ hCsub hetC
        rw [support_comap_coe] at h2
        refine hsp.transversal D0_ hD0_ C0 hc1 hc2 hc3 ?_
        rw [hC0eq]
        exact closure_minimal (singleton_subset_iff.2 h2) (s.ideal n).support.2
        rw [List.mem_singleton] at hD'
        subst hD'
        exact hG.exceptional_components_not_subset _ hTn (s.center n) hsm hsnc _
          (s.transitionMapSucc n) hbl (s.ideal n) mu_ (orderAt_eq_of_mem_center_support s hord n hn')
          (s.ideal (n + 1)) (s.ideal_succ n hn') C (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax) hCsub
  refine ⟨hsplit_all i hi, ?_⟩
  intro hilt
  refine ⟨fun x hx => orderAt_eq_of_mem_center_support s hord i hilt x hx, ?_, ⟨_, exceptionalDivisor_pow_mul_comap_mul_eq_comap s T.mult hmu_ i hilt _ _ (hsplit_all i hi).eq_mul⟩⟩
  refine subset_orderAtLeastLocus_of_eq_mul _ _ _ (hsplit_all i hi).eq_mul T.mult _ ?_
  intro x hx
  exact orderAtLeastLocus_subset_of_le (s.ideal i) hmu_ $ s.center_order i hilt hx

theorem isMarked_sequenceData_of_orderAt_le :
    s.toBsd.IsMarked T.structMap T.ideal T.mult
      T.boundary := by
  have hself := (ofMarkedSequence s).isMarked_toBlowupSequenceData
  refine ⟨?_, ?_, hself.center_smooth, hself.center_snc⟩
  intro i hi
  have hi' := hi
  obtain ⟨Bd, hBd⟩ := ((isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hmu_ s hord i (le_of_lt hi')).2 hi').2.2
  exact ⟨Bd, tr_ hBd (congrArg (fun J : IdealSheafData (s.schemeAt i) => J.comap (s.transitionMapSucc i))
  (controlledTransform_eq_sequenceData s T.ideal T.mult i))⟩
  intro i hi
  have hi' := hi
  intro x hx
  exact (mem_orderAtLeastLocus_iff _ _ _).2 ((congrArg (fun J : IdealSheafData (s.schemeAt i) => orderAt J x) (controlledTransform_eq_sequenceData s T.ideal T.mult i)) ▸ (mem_orderAtLeastLocus_iff _ _ _).1 ((((isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hmu_ s hord i (le_of_lt hi')).2 hi').2.1) hx))

theorem principalizationCertificate_controlledTransform
    (hcert : ∀ i < s.length,
      OrderCertificate (s.schemeAt i) (s.projectionToSpec i) (s.ideal i) mu_ (s.boundaryLocus i) $ s.center i)
    (i : ℕ) (hi : i < s.length) :
    PrincipalizationCertificate (s.schemeAt i) (s.projectionToSpec i) (MarkedSequenceOfBlowups.controlledTransform s T.ideal T.mult i) T.mult
      (s.boundaryLocus i) $ s.center i := by
  have hsp := (isMonomialSplitting_controlledTransform_monomialFactor hG hT hsplit hmu_ s hord i $ le_of_lt hi).1
  refine PrincipalizationCertificate.toOrder (MarkedSequenceOfBlowups.monomialFactor s M T.mult i) (s.ideal i) mu_ hsp.eq_mul
    ?_ hmu_ (s.center_order i hi) $ hcert i hi
  intro x hx
  obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 $ hsp.monomial_support hx
  exact (mem_boundaryLocus_iff s i x).2 ⟨D, hD, hxD⟩
end

end

section

theorem cast_sub_le_of_cast_le_add {a : ENat} {m s : ℕ}
    (h : (m : ENat) ≤ a + (s : ENat)) : ((m - s : ℕ) : ENat) ≤ a :=by simp_all
theorem exists_exceptionalIdeal_pow_mul_eq_comap_mul_pow (_hG : PrincipalizationGeometryHypotheses) (T : MarkedIdealWithBoundary)
    (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (_hsm : Smooth $ subschemeι Z ≫ structMap T)
    (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (X' : Sch) (pi_ : X' ⟶ scheme T) (hbl : IsBlowupAlongIdealSheaf pi_ Z)
    (Bd Mon Ad : tISD T) (m sdeg : ℕ)
    (hsplit : IsMonomialSplitting T.boundary Bd Mon Ad)
    (hZsub : (↑Z.support : CSet T.scheme) ⊆ orderAtLeastLocus Bd m)
    (hordA : ∀ x ∈ support Z, orderAt Ad x = (sdeg : ENat))
    (B' : ISD X') (_hB' : exceptionalIdeal pi_ Z ^ m * B' = Bd.comap pi_)
    (A' : ISD X') (_hA' : exceptionalIdeal pi_ Z ^ sdeg * A' = Ad.comap pi_) :
    ∃ C : ISD X',
      exceptionalIdeal pi_ Z ^ m * C = Mon.comap pi_ * exceptionalIdeal pi_ Z ^ sdeg := by
  let _a1 := p5 pi_ Z
  rcases m63 sdeg m with hms | hms
  have := hT.charZero
  have := hT.smooth
  have := hT.isNoetherian
  have := isNoetherian_of_isBlowupAlongIdealSheaf hbl
  have hsub : (↑Z.support) ⊆ orderAtLeastLocus Mon (m - sdeg) := by
    intro x hx
    refine (mem_orderAtLeastLocus_iff Mon (m - sdeg) x).2 ?_
    have h1 := (mem_orderAtLeastLocus_iff Bd m x).1 $ hZsub hx
    rw [hsplit.orderAt_eq_add T.structMap x, hordA x hx] at h1
    exact cast_sub_le_of_cast_le_add h1
  obtain ⟨C, hC, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf pi_ Z Mon (m - sdeg) hbl $ le_pow_of_hasStrictNormalCrossingsWith T.structMap Z Mon T.boundary hsnc (m - sdeg) hsub
  refine ⟨C, ?_⟩
  let _a0 := _a1 ^ (m - sdeg)
  calc _a1 ^ m * C
      = _a0 * _a1 ^ sdeg * C := by
        rw [← pow_add, sub_add_cancel hms.le]
    _ = _a0 * C * _a1 ^ sdeg := by
        simp [mul_comm, mul_left_comm]
    _ = cmI Mon pi_ * _a1 ^ sdeg := by rw [hC]
  refine ⟨cmI Mon pi_ * _a1 ^ (sdeg - m), ?_⟩
  have hpow : _a1 ^ m * _a1 ^ (sdeg - m)
      = _a1 ^ sdeg := by
    rw [← pow_add, add_sub_cancel' hms]
  calc _a1 ^ m * (cmI Mon pi_ * _a1 ^ (sdeg - m))
      = cmI Mon pi_ * (_a1 ^ m * _a1 ^ (sdeg - m)) := by
        simp [mul_assoc, mul_comm]
    _ = cmI Mon pi_ * _a1 ^ sdeg := by rw [hpow]

section
variable {Y : Sch}
theorem comap_eq_one_of_forall_notMem_support (I : ISD Y)
    (U : Opn Y) (h : ∀ x : ↥Y, x ∈ U → x ∉ (↑I.support : Set ↥Y)) : I.comap U.i = 1 := by
  rw [Scheme.IdealSheafData.one_eq_top]
  exact p39 U.i I fun y => h y.1 y.2

theorem orderAt_comap_opens_io (U : Opn Y) (I : ISD Y)
    (x : ↥Y) (hx : x ∈ U) : orderAt (I.comap U.i) ⟨x, hx⟩ = orderAt I x := by
  simpa using (orderAt_comap_of_isOpenImmersion U.i I ⟨x, hx⟩)
end

section
variable {A B : Sch} (f : A ⟶ B)
theorem comap_list_prod :
    ∀ L : Bdy B,
      (L.prod).comap f = (L.map fun D : ISD B => D.comap f).prod := by
  intro L
  induction L with
  | nil =>
      rw [prod_nil, map_nil, prod_nil]
      exact comap_one f
  | cons D L ih =>
      rw [prod_cons, comap_mul, ih, map_cons, prod_cons]

theorem exists_list_prod_eq_of_mem_closure
    (E : Bdy B) {y : ISD A}
    (hy : y ∈ Submonoid.closure ((fun D : ISD B => D.comap f) '' {D | D ∈ E})) :
    ∃ L : Bdy B, (∀ D ∈ L, D ∈ E) ∧
      y = (L.map fun D : ISD B => D.comap f).prod := by
  induction hy using closure_induction with
  | mem a ha =>
      obtain ⟨D, hD, rfl⟩ := ha
      refine ⟨[D], ?_, ?_⟩
      simp_all
      simp
  | one => exact ⟨[], by simp, by simp⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨L1, h1, e1⟩ := iha
      obtain ⟨L2, h2, e2⟩ := ihb
      refine ⟨L1 ++ L2, ?_, ?_⟩
      intro D hD
      rcases mem_append.1 hD with h | h
      exact h1 D h
      exact h2 D h
      simp_all
end

theorem isIrreducible_inter_isOpen {al_ : Type} [TopologicalSpace al_] {S O : Set al_}
    (hS : IsIrreducible S) (hO : IsOpen O) (hne : (S ∩ O).Nonempty) :
    IsIrreducible $ S ∩ O := by
  refine ⟨hne, ?_⟩
  intro u v hu hv hsu hsv
  obtain ⟨a, ha, hau⟩ := hsu
  obtain ⟨b, hb, hbv⟩ := hsv
  obtain ⟨c, hcS, hc⟩ :=
    an2 hS (u ∩ O) (v ∩ O) (hu.inter hO) (hv.inter hO) ⟨a, an1 ha, hau, an2 ha⟩ ⟨b, an1 hb, hbv, an2 hb⟩
  exact ⟨c, ⟨hcS, hc.1.2⟩, hc.1.1, hc.2.1⟩

theorem exists_closure_singleton_eq_closure (X : Sch) {S : Set ↥X}
    (hS : IsIrreducible S) : ∃ et_ : ↥X, closure ({et_} : Set ↥X) = closure S := by
  obtain ⟨et_, het_⟩ := m140 hS.closure isClosed_closure
  exact ⟨et_, het_⟩

section
variable {al_ : Type} [TopologicalSpace al_] {S} {et_} (het_ : closure ({et_} : Set al_) = closure S)
include het_
theorem mem_of_isOpen_of_closure_singleton_eq {O : Set al_} (hO : IsOpen O)
    (hne : (S ∩ O).Nonempty) : et_ ∈ O := by
  by_contra hx
  have h1 :=
    closure_minimal (singleton_subset_iff.2 hx) hO.isClosed_compl
  rw [het_] at h1
  obtain ⟨a, haS, haO⟩ := hne
  exact (h1 $ subset_closure haS) haO

theorem subset_of_closure_singleton_eq_closure {F : Set al_} (hF : IsClosed F)
    (hmem : et_ ∈ F) : S ⊆ F := by
  have h1 := closure_minimal (singleton_subset_iff.2 hmem) hF
  rw [het_] at h1
  exact fun a ha => h1 $ subset_closure ha
end

section
variable (T : MarkedIdealWithBoundary) (hT : T.IsAdmissible) (Z : tISD T) (hsm : Smooth (subschemeι Z ≫ structMap T))
include hT hsm
theorem isNoetherian_subscheme_of_smooth :
    IsNoetherian Z.subscheme := by
  have := hsm
  have := hT.quasiCompact
  have : IsNoetherian $ Sp T.base :=
    by
    rw [AlgebraicGeometry.isNoetherian_Spec]
    infer_instance
  let _a0 := siI Z ≫ tMp T
  have : LocallyOfFiniteType _a0 := inferInstance
  have : QuasiCompact _a0 := inferInstance
  exact isNoetherian_of_locallyOfFiniteType _a0

theorem exists_opens_isIrreducible_support_inter
    (y : ↥T.scheme) (hy : y ∈ (↑Z.support : CSet T.scheme)) :
    ∃ V : T.scheme.Opens, y ∈ V ∧
      IsIrreducible ((↑Z.support : CSet T.scheme) ∩ (↑V : CSet T.scheme)) := by
  have : IsNoetherian Z.subscheme := isNoetherian_subscheme_of_smooth T hT Z hsm
  have : NoetherianSpace ↥Z.subscheme := inferInstance
  have hemb :=
    AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding Z.si
  have hrange : range (⇑(siI Z).base) = (↑Z.support) := by simp_all
  obtain ⟨y', hy'⟩ : ∃ y', bsM (siI Z) y' = y := by
    have h1 : y ∈ range (⇑(siI Z).base) := by rw [hrange]
                                              exact hy
    exact h1
  have hfin : (irreducibleComponents ↥Z.subscheme).Finite :=
    finite_irreducibleComponents
  have hC1 : irreducibleComponent y' ∈ irreducibleComponents ↥Z.subscheme :=
    irreducibleComponent_mem_irreducibleComponents y'
  have hy'C : y' ∈ irreducibleComponent y' := mem_irreducibleComponent
  have hRclosed : IsClosed
      (⋃ C ∈ {C : CSet Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
        C ≠ irreducibleComponent y'}, (⇑(siI Z).base) '' C) := by
    refine isClosed_biUnion (hfin.subset fun C hC => an1 hC) ?_
    intro C hC
    exact hemb.isClosedMap _ $ isClosed_of_mem_irreducibleComponents C hC.1
  have hyR : y ∉ (⋃ C ∈ {C : CSet Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
      C ≠ irreducibleComponent y'}, (⇑(siI Z).base) '' C) := by
    intro hmem
    obtain ⟨C, hC, hyC⟩ := Set.mem_iUnion₂.1 hmem
    obtain ⟨c, hcC, hceq⟩ := hyC
    have hcy : c = y' := hemb.injective $ by rw [hceq, hy']
    have hdisj := irreducibleComponentsDisjointOfSmooth T.base Z.subscheme (siI Z ≫ tMp T) hsm
      C hC.1 (irreducibleComponent y') hC1 hC.2
    exact (Set.disjoint_left.mp hdisj $ hcy ▸ hcC) hy'C
  have hSV : (↑Z.support) ∩
        (⋃ C ∈ {C : CSet Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
          C ≠ irreducibleComponent y'}, (⇑(siI Z).base) '' C)ᶜ
      = ((⇑(siI Z).base) '' (irreducibleComponent y')) ∩
        (⋃ C ∈ {C : CSet Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
          C ≠ irreducibleComponent y'}, (⇑(siI Z).base) '' C)ᶜ := by
    refine m15 ?_ ?_
    rintro a ⟨haS, haR⟩
    rw [← hrange] at haS
    obtain ⟨c, rfl⟩ := haS
    refine ⟨⟨c, ?_, rfl⟩, haR⟩
    by_contra hcc
    refine haR $ Set.mem_iUnion₂.2 ⟨irreducibleComponent c,
      ⟨irreducibleComponent_mem_irreducibleComponents c, ?_⟩,
      ⟨c, mem_irreducibleComponent, rfl⟩⟩
    intro hEq
    exact hcc $ hEq ▸ mem_irreducibleComponent
    rintro a ⟨haim, haR⟩
    refine ⟨?_, haR⟩
    rw [← hrange]
    exact image_subset_range _ _ haim
  have hfinal : IsIrreducible $ (↑Z.support) ∩
      (⋃ C ∈ {C : CSet Z.subscheme | C ∈ irreducibleComponents ↥Z.subscheme ∧
        C ≠ irreducibleComponent y'}, (⇑(siI Z).base) '' C)ᶜ := by
    rw [hSV]
    exact isIrreducible_inter_isOpen
      (isIrreducible_irreducibleComponent.image _ hemb.continuous.continuousOn)
      hRclosed.isOpen_compl ⟨y, ⟨y', hy'C, hy'⟩, hyR⟩
  exact ⟨⟨_, hRclosed.isOpen_compl⟩, hyR, hfinal⟩
end

section
variable (hG : PrincipalizationGeometryHypotheses) (T : MarkedIdealWithBoundary) (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData) (hsm : Smooth (subschemeι Z ≫ structMap T)) (hsnc : HasStrictNormalCrossingsWith T.structMap Z T.boundary) (X' : Sch) (pi_ : X' ⟶ scheme T) (hbl : IsBlowupAlongIdealSheaf pi_ Z)
include hG hT hsm hsnc hbl
theorem isMonomialIn_comap_blowup
    (Mon : tISD T) (hMon : IsMonomialIn T.boundary Mon) :
    IsMonomialIn (map (strictTransform pi_ Z) T.boundary ++ [exceptionalIdeal pi_ Z])
      (Mon.comap pi_) := by
  let _a0 := p5 pi_ Z
  let _a1 := map (p6 pi_ Z) T.boundary
  have hExcMem : _a0 ∈
      _a1 ++ [_a0] := by simp
  have hSTmem : ∀ D0_ ∈ tBd T, p6 pi_ Z D0_ ∈
      _a1 ++ [_a0] := by
    intro D0_ hD0_
    exact mem_append_left _ $ mem_map.2 ⟨D0_, hD0_, rfl⟩
  have hfac : ∀ D0_ ∈ tBd T, ∀ x',
      ∃ (U : Opn X') (ep_ : ℕ), x' ∈ U ∧
        (cmI D0_ pi_).comap U.i =
          (p6 pi_ Z D0_).comap U.i * _a0.comap U.i ^ ep_ := by
    intro D0_ hD0_ x'
    obtain ⟨U, ep_, hxU, _, _, hEq⟩ :=
      hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' pi_ hbl D0_ hD0_ x'
    exact ⟨U, ep_, hxU, hEq⟩
  have hmonD := fun D0_ hD0_ =>
    isMonomialIn_of_locally_eq_mul_pow _ _ _ _ (hSTmem D0_ hD0_) hExcMem $ hfac D0_ hD0_
  refine isMonomialIn_of_forall_mem ?_ $ hMon.comap pi_
  intro D hD
  obtain ⟨D0_, hD0_, rfl⟩ := mem_map.1 hD
  exact hmonD D0_ hD0_

theorem exists_opens_comap_list_prod_eq_mul_exceptionalIdeal_pow
    (x' : ↥X') (z : ↥T.scheme)
    (hz1 : ∀ D ∈ boundary T,
      (∃ V : T.scheme.Opens, pi_.base x' ∈ V ∧
        (↑Z.support : CSet T.scheme) ∩ (↑V : CSet T.scheme) ⊆ (↑D.support : CSet T.scheme)) →
      z ∈ support D)
    (hz0 : ∀ D ∈ boundary T,
      ¬ (∃ V : T.scheme.Opens, pi_.base x' ∈ V ∧
        (↑Z.support : CSet T.scheme) ∩ (↑V : CSet T.scheme) ⊆ (↑D.support : CSet T.scheme)) →
      z ∉ support D) :
    ∀ L : List T.scheme.IdealSheafData, (∀ D ∈ L, D ∈ boundary T) →
      ∃ (U : Opens X') (m : U.toScheme.IdealSheafData) (s : ℕ), x' ∈ U ∧
        m ∈ Submonoid.closure ((fun D : IdealSheafData X' => D.comap U.i) ''
          {D | D ∈ map (strictTransform pi_ Z) T.boundary}) ∧
        ((L.prod).comap pi_).comap U.i = m * ((exceptionalIdeal pi_ Z).comap U.i) ^ s ∧
        orderAt (L.prod) z = (s : ENat) := by
  have := hT.charZero
  have := hT.smooth
  intro L
  induction L with
  | nil =>
      intro _
      refine ⟨⊤, 1, 0, trivial, one_mem _, ?_, ?_⟩
      rw [prod_nil, comap_one, comap_one, pow_zero, mul_one]
      rw [prod_nil, one_eq_top, orderAt_top]
      simp
  | cons D L ih =>
      intro hall
      have hD := hall D mem_cons_self
      obtain ⟨U1_, m1, s1_, hx1, hm1, heq1, hord1⟩ :=
        ih fun D' hD' => hall D' $ mem_cons_of_mem _ hD'
      obtain ⟨U2_, ep_, hx2, hep01, hepiff, heq2⟩ :=
        hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' pi_ hbl D hD x'
      have hDeq : (cmI D pi_).comap (U1_ ⊓ U2_).i
          = (p6 pi_ Z D).comap (U1_ ⊓ U2_).i
            * ((p5 pi_ Z).comap (U1_ ⊓ U2_).i) ^ ep_ := by
        have h : ((cmI D pi_).comap U2_.i).comap
              (X'.homOfLE (inf_le_right : U1_ ⊓ U2_ ≤ U2_))
            = ((p6 pi_ Z D).comap U2_.i
              * ((p5 pi_ Z).comap U2_.i) ^ ep_).comap
                (X'.homOfLE (inf_le_right : U1_ ⊓ U2_ ≤ U2_)) := by
          rw [heq2]
        simp [comap_mul, comap_pow,
          comap_homOfLE] at h
        exact h
      have hLeq : (cmI (L.prod) pi_).comap (U1_ ⊓ U2_).i
          = m1.comap (X'.homOfLE (inf_le_left : U1_ ⊓ U2_ ≤ U1_))
            * ((p5 pi_ Z).comap (U1_ ⊓ U2_).i) ^ s1_ := by
        have h : ((cmI (L.prod) pi_).comap U1_.i).comap
              (X'.homOfLE (inf_le_left : U1_ ⊓ U2_ ≤ U1_))
            = (m1 * ((p5 pi_ Z).comap U1_.i) ^ s1_).comap
                (X'.homOfLE (inf_le_left : U1_ ⊓ U2_ ≤ U1_)) := by
          rw [heq1]
        simp [comap_mul, comap_pow,
          comap_homOfLE] at h
        exact h
      have hordD : orderAt D z = ep_ := by
        rcases hep01 with h0 | h1
        have hnotex : ¬ (∃ V : T.scheme.Opens, bsM pi_ x' ∈ V ∧
            suppI Z ∩ (V : CSet T.scheme)
              ⊆ suppI D) := by
          intro hex
          have h1' := hepiff.2 hex
          rw [h0] at h1'
          simp at h1'
        rw [h0, (orderAt_eq_zero_iff_not_mem_support D z).2 $ hz0 D hD hnotex]
        simp
        have hzm := hz1 D hD $ hepiff.1 h1
        rw [h1, MonomialChart.orderAt_boundary_eq_one T hT D hD z hzm]
        simp
      refine ⟨U1_ ⊓ U2_, (p6 pi_ Z D).comap (U1_ ⊓ U2_).i
        * (cmI m1 $ X'.homOfLE inf_le_left), ep_ + s1_, ⟨hx1, hx2⟩, ?_, ?_, ?_⟩
      exact mul_mem (m175 ⟨p6 pi_ Z D, mem_map.2 ⟨D, hD, rfl⟩, rfl⟩) $ comap_homOfLE_mem_closure_comap (E := map (p6 pi_ Z) T.boundary) inf_le_left m1 hm1
      rw [prod_cons, comap_mul, comap_mul,
        hDeq, hLeq, pow_add, mul_mul_mul_comm]
      rw [prod_cons, orderAt_mul T.base T.structMap D L.prod z, hordD, hord1,
        cast_add]

theorem isMonomialSplitting_of_isBlowupAlongIdealSheaf
    (Bd Mon Ad : tISD T) (m sdeg : ℕ)
    (hsplit : IsMonomialSplitting T.boundary Bd Mon Ad)
    (hZsub : (↑Z.support : CSet T.scheme) ⊆ orderAtLeastLocus Bd m)
    (hordA : ∀ x ∈ support Z, orderAt Ad x = (sdeg : ENat))
    (B' : ISD X') (hB' : exceptionalIdeal pi_ Z ^ m * B' = Bd.comap pi_)
    (A' : ISD X') (hA' : exceptionalIdeal pi_ Z ^ sdeg * A' = Ad.comap pi_)
    (C : ISD X')
    (hC : exceptionalIdeal pi_ Z ^ m * C = Mon.comap pi_ * exceptionalIdeal pi_ Z ^ sdeg) :
    IsMonomialSplitting
      (map (strictTransform pi_ Z) T.boundary ++ [exceptionalIdeal pi_ Z]) B' C A' := by
  have := hT.charZero
  have := hT.smooth
  have hEC := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl
  let _a2 := map (p6 pi_ Z) T.boundary
  have hExcMem : p5 pi_ Z ∈
      _a2 ++ [p5 pi_ Z] := by
    simp
  have hSTmem : ∀ D0_ ∈ tBd T, p6 pi_ Z D0_ ∈
      _a2 ++ [p5 pi_ Z] := by
    intro D0_ hD0_
    exact mem_append_left _ $ mem_map.2 ⟨D0_, hD0_, rfl⟩
  have hfac : ∀ D0_ ∈ tBd T, ∀ x' : X',
      ∃ (U : Opn X') (ep_ : ℕ), x' ∈ U ∧
        (cmI D0_ pi_).comap U.i =
          (p6 pi_ Z D0_).comap U.i * (p5 pi_ Z).comap U.i ^ ep_ := by
    intro D0_ hD0_ x'
    obtain ⟨U, ep_, hxU, _, _, hEq⟩ :=
      hG.monomialInputs.blowup_total_transform T hT Z hsm hsnc X' pi_ hbl D0_ hD0_ x'
    exact ⟨U, ep_, hxU, hEq⟩
  have hmonD : ∀ D0_ ∈ tBd T,
      IsMonomialIn (_a2 ++ [p5 pi_ Z])
        (cmI D0_ pi_) := by
    intro D0_ hD0_
    exact isMonomialIn_of_locally_eq_mul_pow _ _ _ _ (hSTmem D0_ hD0_) hExcMem $ hfac D0_ hD0_
  have hmonMon : IsMonomialIn (_a2 ++ [p5 pi_ Z])
      (cmI Mon pi_) := by
    refine isMonomialIn_of_forall_mem ?_ $ hsplit.monomial.comap pi_
    intro D hD
    obtain ⟨D0_, hD0_, rfl⟩ := mem_map.1 hD
    exact hmonD D0_ hD0_
  have key : p5 pi_ Z ^ m * B' = p5 pi_ Z ^ m * (C * A') := by
    rw [← mul_assoc (p5 pi_ Z ^ m) C A', hC, hB', hsplit.eq_mul,
      comap_mul,
      mul_assoc (cmI Mon pi_) (p5 pi_ Z ^ sdeg) A', hA']
  refine ⟨(hEC.pow m).eq_of_mul_eq_mul key, ?_, ?_, ?_⟩
  intro x hx
  have hx1 : x ∈ (support (p5 pi_ Z ^ m * C) : Set X') :=
    support_subset_support_mul_right _ C hx
  rw [hC] at hx1
  rcases support_mul_subset _ _ hx1 with h1 | h2
  rw [support_comap_coe] at h1
  obtain ⟨D0_, hD0_, hxD⟩ := Set.mem_iUnion₂.1 $ hsplit.monomial_support h1
  have hx' : x ∈ (support (cmI D0_ pi_) : Set X') := by simp_all
  rcases support_subset_union_of_locally_eq_mul_pow _ _ _ (hfac D0_ hD0_) hx' with h3 | h4
  exact Set.mem_iUnion₂.2 ⟨_, hSTmem D0_ hD0_, h3⟩
  exact Set.mem_iUnion₂.2 ⟨_, hExcMem, h4⟩
  exact Set.mem_iUnion₂.2 ⟨_, hExcMem, support_pow_subset _ _ h2⟩
  rcases m63 sdeg m with hms | hms
  have hsub : suppI Z ⊆ orderAtLeastLocus Mon (m - sdeg) := by
    intro x hx
    refine (mem_orderAtLeastLocus_iff Mon (m - sdeg) x).2 ?_
    have h1 := (mem_orderAtLeastLocus_iff Bd m x).1 $ hZsub hx
    rw [hsplit.orderAt_eq_add T.structMap x, hordA x hx] at h1
    exact cast_sub_le_of_cast_le_add h1
  have hle :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap Z Mon T.boundary hsnc (m - sdeg) hsub
  let _a4 := p5 pi_ Z ^ (m - sdeg)
  have hC2 : _a4 * C = cmI Mon pi_ := by
    refine (hEC.pow sdeg).eq_of_mul_eq_mul ?_
    rw [← mul_assoc (p5 pi_ Z ^ sdeg) _a4 C,
      ← pow_add, add_sub_cancel' hms.le, hC,
      mul_comm (cmI Mon pi_) $ p5 pi_ Z ^ sdeg]
  let hMon := hsplit.monomial
  let d := m - sdeg
  let hC := hC2
  let _a4 := map (p6 pi_ Z) T.boundary
  let _a7 := suppI Z
  have := hT.charZero
  have := hT.smooth
  have hEC := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl
  have hExcMem : p5 pi_ Z ∈
      _a4 ++ [p5 pi_ Z] := by simp
  have hsubimg : ∀ U : Opn X',
      ((fun D : ISD X' => D.comap U.i) ''
          {D | D ∈ _a4})
        ⊆ ((fun D : ISD X' => D.comap U.i) ''
          {D | D ∈ _a4 ++ [p5 pi_ Z]}) := by
    intro U
    exact image_mono fun D hD => mem_append_left _ hD
  rw [isMonomialIn_iff_forall_exists_mem_closure]
  intro x'
  by_cases hx'E : x' ∈ support (p5 pi_ Z)
  have hyZ : (bsM pi_ x') ∈ _a7 := by
    have h0 : (support (exceptionalIdeal pi_ Z) : Set X')
        = m142 pi_.base Z.supp := by
      rw [exceptionalIdeal_eq_comap, support_comap_coe]
    have h1 : x' ∈ (support (exceptionalIdeal pi_ Z) : Set X') := hx'E
    rwa [h0] at h1
  obtain ⟨V0, hyV0, hirr0⟩ :=
    exists_opens_isIrreducible_support_inter T hT Z hsm (bsM pi_ x') hyZ
  obtain ⟨W, hyW, hWmem⟩ :=
    (isMonomialIn_iff_forall_exists_mem_closure T.boundary Mon).1 hMon $ bsM pi_ x'
  obtain ⟨L, hLsub, hLeq⟩ := exists_list_prod_eq_of_mem_closure W.i T.boundary hWmem
  have hWeq := hLeq
  rw [← comap_list_prod W.i L] at hWeq
  have hyS0 : bsM pi_ x' ∈ (suppI Z ∩ (V0 : CSet T.scheme))
      ∩ (W : CSet T.scheme) := ⟨⟨hyZ, hyV0⟩, hyW⟩
  let _s1 := (suppI Z ∩ (V0 : CSet T.scheme)) ∩ (W : CSet T.scheme)
  have hirr : IsIrreducible _s1 := isIrreducible_inter_isOpen hirr0 W.2 ⟨_, hyS0⟩
  obtain ⟨et_, het_⟩ := exists_closure_singleton_eq_closure T.scheme hirr
  have hetZ : et_ ∈ _a7 := by
    have h1 : closure _s1 ⊆ _a7 :=
      closure_minimal (fun a ha => ha.1.1) (support Z).2
    have h2 : et_ ∈ closure _s1 := by
      rw [← het_]
      exact subset_closure rfl
    exact h1 h2
  have hetW := mem_of_isOpen_of_closure_singleton_eq het_ W.2 ⟨_, hyS0, hyW⟩
  have hz1 : ∀ D ∈ tBd T, (∃ V : T.scheme.Opens, bsM pi_ x' ∈ V ∧
      suppI Z ∩ (V : CSet T.scheme) ⊆ suppI D) →
      et_ ∈ support D := by
    rintro D hD ⟨V, hyV, hsub⟩
    exact hsub ⟨hetZ, mem_of_isOpen_of_closure_singleton_eq het_ V.2 ⟨_, hyS0, hyV⟩⟩
  have hz0 : ∀ D ∈ tBd T, ¬ (∃ V : T.scheme.Opens, bsM pi_ x' ∈ V ∧
      suppI Z ∩ (V : CSet T.scheme) ⊆ suppI D) →
      et_ ∉ support D := by
    intro D _ hnot hmem
    refine hnot ⟨V0 ⊓ W, ⟨hyV0, hyW⟩, ?_⟩
    intro a ha
    have ha2 := an2 ha
    rw [coe_inf] at ha2
    exact (subset_of_closure_singleton_eq_closure het_ (support D).2 hmem) ⟨⟨an1 ha, an1 ha2⟩, an2 ha2⟩
  obtain ⟨U2_, m, s, hx2, hmclo, hUeq, hords⟩ :=
    exists_opens_comap_list_prod_eq_mul_exceptionalIdeal_pow hG T hT Z hsm hsnc X' pi_ hbl x' et_ hz1 hz0 L hLsub
  have hMonord : ((d : ℕ) : ENat) ≤ orderAt Mon et_ := by
    have h2 := orderAtLeastLocus_subset_orderAtLeastLocus_pow Z d 1 $ (mem_orderAtLeastLocus_one_iff Z et_).2 hetZ
    rw [mul_one] at h2
    exact le_trans ((mem_orderAtLeastLocus_iff _ _ _).1 h2) $ orderAt_le_of_le hle et_
  have hMonLprod : orderAt Mon et_ = orderAt (L.prod) et_ := by
    rw [← orderAt_comap_opens_io W Mon et_ hetW, ← orderAt_comap_opens_io W (L.prod) et_ hetW, hWeq]
  have hds : d ≤ s := by
    rw [hMonLprod, hords] at hMonord
    exact_mod_cast hMonord
  refine ⟨U2_ ⊓ preU pi_ W, ⟨hx2, hyW⟩, ?_⟩
  have hkey : ∀ J : tISD T,
      (cmI J pi_).comap (U2_ ⊓ preU pi_ W).i
        = (J.comap W.i).comap (pi_.resLE W (U2_ ⊓ preU pi_ W) inf_le_right) := by
    intro J
    rw [← comap_comp, ← comap_comp,
      q4]
  have hMonL : (cmI Mon pi_).comap (U2_ ⊓ preU pi_ W).i
      = (cmI (L.prod) pi_).comap (U2_ ⊓ preU pi_ W).i := by simp_all
  have hfact : (cmI (L.prod) pi_).comap (U2_ ⊓ preU pi_ W).i
      = m.comap (X'.homOfLE (inf_le_left : U2_ ⊓ preU pi_ W ≤ U2_))
        * ((p5 pi_ Z).comap (U2_ ⊓ preU pi_ W).i) ^ s := by
    have h : ((cmI (L.prod) pi_).comap U2_.i).comap
          (X'.homOfLE (inf_le_left : U2_ ⊓ preU pi_ W ≤ U2_))
        = (m * ((p5 pi_ Z).comap U2_.i) ^ s).comap
            (X'.homOfLE (inf_le_left : U2_ ⊓ preU pi_ W ≤ U2_)) := by
      rw [hUeq]
    simp [comap_mul, comap_pow,
      comap_homOfLE] at h
    exact h
  have hm' : (m.comap $ X'.homOfLE (inf_le_left : U2_ ⊓ preU pi_ W ≤ U2_)) ∈
      Submonoid.closure ((fun D : ISD X' => D.comap (U2_ ⊓ preU pi_ W).i) ''
        {D | D ∈ _a4}) :=
    comap_homOfLE_mem_closure_comap (E := _a4)
      inf_le_left m hmclo
  have hexp := add_sub_cancel' hds
  let _a13 := s - d
  have hCmul : ((p5 pi_ Z) ^ d).comap (U2_ ⊓ preU pi_ W).i
        * (C.comap (U2_ ⊓ preU pi_ W).i)
      = ((p5 pi_ Z) ^ d).comap (U2_ ⊓ preU pi_ W).i
        * ((m.comap $ X'.homOfLE (inf_le_left : U2_ ⊓ preU pi_ W ≤ U2_))
          * ((p5 pi_ Z).comap (U2_ ⊓ preU pi_ W).i) ^ _a13) := by
    calc ((p5 pi_ Z) ^ d).comap (U2_ ⊓ preU pi_ W).i
            * (C.comap (U2_ ⊓ preU pi_ W).i)
        = (((p5 pi_ Z) ^ d) * C).comap (U2_ ⊓ preU pi_ W).i := by
          rw [comap_mul]
      _ = (cmI Mon pi_).comap (U2_ ⊓ preU pi_ W).i := by rw [hC]
      _ = (cmI (L.prod) pi_).comap (U2_ ⊓ preU pi_ W).i := hMonL
      _ = m.comap (X'.homOfLE (inf_le_left : U2_ ⊓ preU pi_ W ≤ U2_))
            * ((p5 pi_ Z).comap (U2_ ⊓ preU pi_ W).i) ^ s := hfact
      _ = m.comap (X'.homOfLE (inf_le_left : U2_ ⊓ preU pi_ W ≤ U2_))
            * ((p5 pi_ Z).comap (U2_ ⊓ preU pi_ W).i) ^ (d + _a13) := by
          rw [hexp]
      _ = ((p5 pi_ Z).comap (U2_ ⊓ preU pi_ W).i) ^ d
            * ((m.comap $ X'.homOfLE (inf_le_left : U2_ ⊓ preU pi_ W ≤ U2_))
              * ((p5 pi_ Z).comap (U2_ ⊓ preU pi_ W).i) ^ _a13) := by
          rw [pow_add]
          exact mul_left_comm _ _ _
      _ = ((p5 pi_ Z) ^ d).comap (U2_ ⊓ preU pi_ W).i
            * ((m.comap $ X'.homOfLE (inf_le_left : U2_ ⊓ preU pi_ W ≤ U2_))
              * ((p5 pi_ Z).comap (U2_ ⊓ preU pi_ W).i) ^ _a13) := by
          rw [comap_pow]
  have hCeq := (hEC.pow d).eq_of_mul_eq_mul_comap_opensio (U2_ ⊓ preU pi_ W) hCmul
  rw [hCeq]
  have hEmem : (p5 pi_ Z).comap (U2_ ⊓ preU pi_ W).i ∈
      ((fun D : ISD X' => D.comap (U2_ ⊓ preU pi_ W).i) ''
        {D | D ∈ _a4 ++ [p5 pi_ Z]}) :=
    ⟨p5 pi_ Z, hExcMem, rfl⟩
  exact mul_mem (closure_mono (hsubimg $ U2_ ⊓ preU pi_ W) hm') $ pow_mem (m175 hEmem) $ s - d
  obtain ⟨U0_, hx0, hmem0⟩ :=
    (isMonomialIn_iff_forall_exists_mem_closure _ _).1 (isMonomialIn_comap_blowup hG T hT Z hsm hsnc X' pi_ hbl Mon hMon) x'
  have hxVc :=
    (m22).2 hx'E
  refine ⟨U0_ ⊓ (suppC $ p5 pi_ Z), ⟨hx0, hxVc⟩, ?_⟩
  let _s0 := U0_ ⊓ (suppC $ p5 pi_ Z)
  have hE1 : (p5 pi_ Z).comap _s0.i = 1 := by
    refine comap_eq_one_of_forall_notMem_support _ _ ?_
    intro x hx
    exact (m22).1 hx.2
  let _a20 := (cmI Mon pi_).comap _s0.i
  have hCU : C.comap _s0.i
      = _a20 := by
    calc C.comap _s0.i
        = (1 : _s0.toScheme.IdealSheafData) ^ d
            * C.comap _s0.i := by
          rw [one_pow, one_mul]
      _ = ((p5 pi_ Z).comap _s0.i) ^ d
            * C.comap _s0.i := by rw [hE1]
      _ = (((p5 pi_ Z) ^ d) * C).comap
            _s0.i := by
          rw [comap_mul, comap_pow]
      _ = _a20 := by rw [hC]
  rw [hCU]
  have hfin := comap_homOfLE_mem_closure_comap
    (E := _a4 ++ [p5 pi_ Z])
    (inf_le_left : U0_ ⊓ (suppC $ p5 pi_ Z) ≤ U0_) _ hmem0
  rwa [comap_homOfLE] at hfin
  have hC3 : C = cmI Mon pi_ * p5 pi_ Z ^ (sdeg - m) := by
    refine (hEC.pow m).eq_of_mul_eq_mul ?_
    rw [hC,
      ← mul_assoc (p5 pi_ Z ^ m) (cmI Mon pi_)
        (p5 pi_ Z ^ (sdeg - m)),
      mul_comm (p5 pi_ Z ^ m) $ cmI Mon pi_,
      mul_assoc (cmI Mon pi_) (p5 pi_ Z ^ m)
        (p5 pi_ Z ^ (sdeg - m)),
      ← pow_add, add_sub_cancel' hms]
  rw [hC3]
  exact isMonomialIn_mul _ hmonMon $ isMonomialIn_pow _ (isMonomialIn_of_mem hExcMem) _
  rintro D hD Cs hCirr hCsubD hCmax hCA
  rcases mem_append.1 hD with hD' | hD'
  obtain ⟨D0_, hD0_, rfl⟩ := mem_map.1 hD'
  obtain ⟨et', C0, hCeq, _, hC0comp, _, hC0eq⟩ :=
    hG.strictTransform_components T hT Z hsm hsnc X' pi_ hbl D0_ hD0_ Cs
      (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax)
  obtain ⟨hc1, hc2, hc3⟩ := isIrreducible_subset_maximal_of_isIrreducibleComponentOf hC0comp
  have hetC : et' ∈ Cs := by
    rw [hCeq]
    exact subset_closure $ mem_singleton et'
  have h2 : et' ∈ (support (Ad.comap pi_) : Set X') := by
    rw [← hA']
    exact support_subset_support_mul_right _ _ $ hCA hetC
  rw [support_comap_coe] at h2
  refine hsplit.transversal D0_ hD0_ C0 hc1 hc2 hc3 ?_
  rw [hC0eq]
  exact closure_minimal (singleton_subset_iff.2 h2) Ad.support.2
  rw [List.mem_singleton] at hD'
  subst hD'
  exact hG.exceptional_components_not_subset T hT Z hsm hsnc X' pi_ hbl Ad sdeg hordA A' hA'
    Cs (isIrreducibleComponentOf_of_maximal hCirr hCsubD hCmax) hCA
end

end





section

theorem list_map_comap_id (B : Sch) E :
    map (fun D : ISD B => D.comap $ 𝟙 B) E = E :=by simp_all
theorem orderAtLeastLocus_comap_eqToHom {A B : Sch} (h : A = B) (J : ISD B) c :
    orderAtLeastLocus (J.comap $ eqToHom h) c = (eqToHom h).base ⁻¹' orderAtLeastLocus J c := by
  subst h
  simp

section
variable {k : Type} [Field k]
theorem isAdmissible_congr {A : Sch}
    {p q} {I J} {m n}
    {E F} (hp : p = q) (hI : I = J) (hm : m = n) (hE : E = F)
    (h : (MarkedIdealWithBoundary.mk k A p I m E).IsAdmissible) :
    (MarkedIdealWithBoundary.mk k A q J n F).IsAdmissible :=by simp_all
theorem ofMarkedSequence_boundary_eq_of_le {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) (hi : i ≤ s.length) :
    s.toBsd.boundaryFrom E i = s.boundary i := by
  revert hi
  induction i with
  | zero =>
      intro _
      rw [BlowupSequenceData.boundary_zero]
      exact s.boundary_zero.symm
  | succ i ih =>
      intro hi
      have hlt := hi
      rw [p52, ih $ m49 hlt]
      exact sy_ $ s.boundary_succ i hlt
end

end

section

abbrev principalizationOfDimLe (T : MarkedIdealWithBoundary) (A : PrincipalizationAssignment) :
    (S : MarkedIdealWithBoundary) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups :=
  fun S _ => A S

abbrev nonMonomialTriple (T : MarkedIdealWithBoundary)
    (s : T.mbs) : MarkedIdealWithBoundary :=
  tripleAtLength T s (lastNonMonomialPart T s) $ maxOrderNonMonomial T s

section
variable {X Y : Sch} (f : X ⟶ Y)
theorem quasiCompact_of_isNoetherian
    (h : IsNoetherian X) : QuasiCompact f := by
  infer_instance

theorem locallyOfFiniteType_of_smooth
    (h : Smooth f) : LocallyOfFiniteType f := by
  infer_instance
end

theorem isAdmissible_tripleAtLength (_hG : PrincipalizationGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible)
    (s : T.mbs) :
    (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := by
  have hlen :=
    le_of_eq (toMarkedSequence_length s).symm
  let _a0 := lastP s ≫ tMp T
  have hsm : Smooth _a0 := by
    have h := smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hT s.toMarkedSequenceOfBlowups
      s.length hlen
    rwa [toMarkedSequence_projectionToSpec] at h
  have hnz : NonzeroOnComponents $ lastI s := by
    have h := nonzeroOnComponents_ideal_of_isAdmissible effectiveCartierSupportContainsNoComponent hT
      s.toMarkedSequenceOfBlowups s.length hlen
    rwa [toMarkedSequence_ideal] at h
  have hsnc : InStrictNormalCrossingPosition _a0 $ lastB s := by
    have h := inStrictNormalCrossingPosition_projectionToSpec_boundary effectiveCartierSupportContainsNoComponent hT s.toMarkedSequenceOfBlowups
      s.length hlen
    rwa [toMarkedSequence_projectionToSpec, toMarkedSequence_boundary] at h
  refine ⟨hT.charZero, locallyOfFiniteType_of_smooth _ hsm, hnz, hT.one_le_mult,
    quasiCompact_of_isNoetherian _ ?_, hsm, hsnc⟩
  have h := p25 effectiveCartierSupportContainsNoComponent hT s.toMarkedSequenceOfBlowups
    s.length hlen
  rwa [toMarkedSequence_schemeAt] at h

section
variable (hG : PrincipalizationGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (s : T.mbs)
include hG hT
theorem tripleAtLength_dim_le
    (J : IdealSheafData $ s.obj s.length) (mu_ : ℕ) :
    (tripleAtLength T s J mu_).krullDimSucc ≤ T.krullDimSucc := by
  rw [tripleAtLength_dim]
  have h := hG.monomialInputs.level_schemeDim_le T hT s.toMarkedSequenceOfBlowups s.length $ le_of_eq (toMarkedSequence_length s).symm
  rwa [toMarkedSequence_schemeAt] at h

theorem isMonomialSplitting_lastNonMonomialPart :
    IsMonomialSplitting (s.boundary s.length) (s.ideal s.length)
      (monomialPart (s.boundary s.length) $ s.ideal s.length) $ lastNonMonomialPart T s := by
  have h := hG.isMonomialSplitting_monomialPart_nonMonomialPart (tripleAtLength T s (lastI s) T.mult)
    (isAdmissible_tripleAtLength hG hT s)
  exact h

theorem isAdmissible_nonMonomialTriple (hcont : NonMonomialOrderReductionContinues T s) :
    (nonMonomialTriple T s).IsAdmissible := by
  have hbase := isAdmissible_tripleAtLength hG hT s
  exact ⟨hbase.charZero, hbase.locallyOfFiniteType, (isMonomialSplitting_lastNonMonomialPart hG hT s).nonzeroOnComponents_nonMonomial hbase.nonzeroOnComponents, le_trans hT.one_le_mult ((nonMonomialOrderReductionContinues_iff T s).1 hcont).1, hbase.quasiCompact, hbase.smooth,
    hbase.snc⟩

theorem exists_orderAt_lastNonMonomialPart_le :
    ∃ B : ℕ, ∀ x : ↥(s.obj s.length), orderAt (lastNonMonomialPart T s) x ≤ (B : ENat) := by
  have hv := isAdmissible_tripleAtLength hG hT s
  exact hG.monomialInputs.orderAt_bounded (tripleAtLength T s (lastI s) T.mult) hv
    (lastNonMonomialPart T s) $ (isMonomialSplitting_lastNonMonomialPart hG hT s).nonzeroOnComponents_nonMonomial hv.nonzeroOnComponents

theorem orderAt_lastNonMonomialPart_le_maxOrderNonMonomial
    (x : ↥(s.obj s.length)) :
    orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomial T s : ℕ) : ENat) := by
  obtain ⟨B, hB⟩ := exists_orderAt_lastNonMonomialPart_le hG hT s
  let _a0 := lastNonMonomialPart T s
  have h : maxOrderNonMonomial T s = maxOrder _a0 := rfl
  rw [h]
  exact orderAt_le_maxOrder _a0 hB x
end

end

section

section
variable (hG : PrincipalizationGeometryHypotheses)
section
variable {n} {A B} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (s : T.mbs) (hcont : NonMonomialOrderReductionContinues T s)
include hspec hdim hcont
theorem isMarked_seqAtEnd_lastNonMonomialPart :
    (ofMarkedSequence
          (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
            (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData.IsMarked
      (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length) := by
  let _a1 := lastNonMonomialPart T s
  let _a2 := maxOrderNonMonomial T s
  let _a0 := tripleAtLength_dim_le hG hT s _a1 _a2
  let _a3 := nonMonomialTriple T s
  exact isMarked_sequenceData_of_orderAt_le hG (isAdmissible_tripleAtLength hG hT s) (isMonomialSplitting_lastNonMonomialPart hG hT s) (((nonMonomialOrderReductionContinues_iff T s).1 hcont).1)
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s _a1 _a2
      _a0) $ hspec.order_le _a3 (isAdmissible_nonMonomialTriple hG hT s hcont) (le_trans _a0 hdim) $ (isOrderBoundedByMult_iff _a3).2 fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x

def continuationByNonMonomialPart :
    MarkedBlowupSequenceData (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult
      (s.boundary s.length) :=
  BlowupSequenceData.toMarkedBlowupSequenceData
    (ofMarkedSequence
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
          (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData
    (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult (s.boundary s.length)
    (isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT hdim s hcont)

@[simp]
theorem continuationByNonMonomialPart_length :
    (continuationByNonMonomialPart hG hspec hT hdim s hcont).length =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
        (tripleAtLength_dim_le hG hT s _ _)).length := by
  exact ofMarkedSequence_length
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s _ _))

end

theorem extendByNonMonomialPart_eq_append (hinv : ComapIsoInvariance) {n : ℕ}
    {A B : PrincipalizationAssignment} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : T.mbs) (hcont : NonMonomialOrderReductionContinues T s) :
    extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s =
      s.append (continuationByNonMonomialPart hG hspec hT hdim s hcont) hinv := by
  let _a0 := lastNonMonomialPart T s
  let _a1 := maxOrderNonMonomial T s
  have h := appendRecursivePrincipalization_eq_append hinv T (principalizationOfDimLe T A) s _a0 _a1
    (tripleAtLength_dim_le hG hT s _a0 _a1)
    (isMarked_seqAtEnd_lastNonMonomialPart hG hspec hT hdim s hcont)
  exact h
end

section
variable {k : Type} [Field k]
theorem orderAtLeastLocus_comap_iso_nonempty [CharZero k]
    {X Y : Sch} (p : Y ⟶ Sp k)
    (hp : Smooth p) (e : Y ≅ X) (N : ISD X) (c : ℕ)
    (hne : (orderAtLeastLocus N c).Nonempty) :
    (orderAtLeastLocus (N.comap e.hom) c).Nonempty := by
  have : Smooth e.inv := inferInstance
  obtain ⟨x, hx⟩ := hne
  have hcomp : (N.comap e.hom).comap e.inv = N := by
    rw [← comap_comp, e.inv_hom_id]
    simp
  have hsub := image_orderAtLeastLocus_comap_subset k p e.inv (N.comap e.hom) c
  rw [hcomp] at hsub
  exact ⟨_, hsub $ mem_image_of_mem _ hx⟩

theorem controlledTransform_ofMarkedSequence {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedSequenceOfBlowups p I m E) (J : ISD X) (c : ℕ) (i : ℕ) :
    s.toBsd.controlledTransform J c i
      = MarkedSequenceOfBlowups.controlledTransform s J c i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      exact congrArg
        (fun Z : ISD (s.schemeAt i) =>
          residualByPow (cmI Z $ s.transitionMapSucc i) (s.exceptionalDivisor i) c) ih

def maxOrderNonMonomialPart (D : MarkedSchemeWithCenter k) : ℕ :=
  maxOrder $ nonMonomialPart D.boundary D.ideal

theorem nonMonomialOrder_transport_eqToIso (D : MarkedSchemeWithCenter k)
    {Y : Sch} (hY : Y = D.ambient) :
    maxOrderNonMonomialPart (D.transport $ eqToIso hY) = maxOrderNonMonomialPart D := by
  subst hY
  rw [eqToIso_refl, MarkedSchemeWithCenter.transport_refl]
end

section
variable (hG : PrincipalizationGeometryHypotheses) {n} {A B} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (s : T.mbs) (hcont : NonMonomialOrderReductionContinues T s)
include hspec hdim hcont
theorem seqAtEnd_lastNonMonomialPart_length_pos :
    0 < (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s _ _)).length := by
  let _c0 := nonMonomialTriple T s
  have hadmNonMonomial := isAdmissible_nonMonomialTriple hG hT s hcont
  let _a0 := A _c0
  have key : 0 < _a0.length := by
    by_contra hzero
    have hlen : _a0.length = 0 := by omega
    have hres := hspec.resolves _c0 hadmNonMonomial (le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) $ maxOrderNonMonomial T s) hdim) $ (isOrderBoundedByMult_iff _c0).2 fun x => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
    rw [isResolution_iff, lastIdeal_eq] at hres
    rw [hlen, ideal_zero] at hres
    have := hadmNonMonomial.charZero
    exact absurd hres $ mp_ nonempty_iff_ne_empty $ orderAtLeastLocus_comap_iso_nonempty (_a0.projectionToSpec 0) (smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hadmNonMonomial (A _c0) 0 $ zero_le _) (A _c0).isoZero _c0.ideal _c0.mult $ ((nonMonomialOrderReductionContinues_iff T s).1 hcont).2
  exact key

end

theorem isMonomialSplitting_of_boundary_eq_of_ideal_eq {X : Sch}
    {E F : List X.IdealSheafData} {I J M N : IdealSheafData X} (hE : E = F) (hI : I = J)
    (h : IsMonomialSplitting F J M N) : IsMonomialSplitting E I M N :=by simp_all
theorem maxOrderNonMonomial_extendByNonMonomialPart_lt (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance) {n : ℕ}
    {A B : PrincipalizationAssignment} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : T.mbs) (hcont : NonMonomialOrderReductionContinues T s) :
    maxOrderNonMonomial T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A) s) < maxOrderNonMonomial T s := by
  let _a2 := le_trans (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) $ maxOrderNonMonomial T s) hdim
  let _a5 := (nonMonomialOrderReductionContinues_iff T s).1 hcont
  let _c0 := continuationByNonMonomialPart hG hspec hT hdim s hcont
  let _a3 := continuationByNonMonomialPart hG hspec hT hdim s hcont
  have ht : 0 < _a3.length := by
    rw [continuationByNonMonomialPart_length hG hspec hT hdim s hcont]
    exact seqAtEnd_lastNonMonomialPart_length_pos hG hspec hT hdim s hcont
  let _a1 := s.append _c0 hinv
  have hconv : maxOrderNonMonomial T _a1
      = maxOrder (nonMonomialPart
          (_c0.boundary
            _c0.length)
          (_c0.ideal
            _c0.length)) := by
    show maxOrderNonMonomialPart (_a1.dataAt
      _a1.length) = _
    rw [append_dataAt_last s _c0 hinv ht]
    exact nonMonomialOrder_transport_eqToIso _ _
  let _a4 := nonMonomialTriple T s
  have _i21 : nonMonomialPart (_a3.boundary (continuationByNonMonomialPart hG hspec hT hdim s hcont).length) (_a3.ideal (continuationByNonMonomialPart hG hspec hT hdim s hcont).length) = (A _a4).ideal (A _a4).length := by
    have hadmLast := isAdmissible_tripleAtLength hG hT s
    have hadmNonMonomial := isAdmissible_nonMonomialTriple hG hT s hcont
    have hdim' :=
      _a2
    let _a1 := _a4
    have hob :=
      (isOrderBoundedByMult_iff _a1).2 fun x =>
        orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
    let _a0 := A _a1
    have hsp := (isMonomialSplitting_controlledTransform_monomialFactor hG hadmLast (isMonomialSplitting_lastNonMonomialPart hG hT s) (_a5.1) _a0 (hspec.order_le _a1 hadmNonMonomial hdim' hob)
        _a0.length le_rfl).1
    exact hG.nonMonomialPart_eq_of_isMonomialSplitting _ (isAdmissible_tripleAtLength hG hadmLast $ continuationByNonMonomialPart hG hspec hT hdim s hcont) _ _
      (isMonomialSplitting_of_boundary_eq_of_ideal_eq (ofMarkedSequence_boundary_eq_of_le (A _a1) (A _a1).length le_rfl)
        ((fun hG {A} _ {T} hT _ s _ => controlledTransform_ofMarkedSequence
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) $ maxOrderNonMonomial T s))
    (lastI s) T.mult
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (lastNonMonomialPart T s) (maxOrderNonMonomial T s)
      (tripleAtLength_dim_le hG hT s (lastNonMonomialPart T s) $ maxOrderNonMonomial T s)).length) hG hspec hT hdim s hcont) hsp)
  rw [extendByNonMonomialPart_eq_append hG hinv hspec hT hdim s hcont, hconv,
    _i21]
  have hadmNonMonomial := isAdmissible_nonMonomialTriple hG hT s hcont
  have hdim' :=
    _a2
  let _a0 := _a4
  have hob :=
    (isOrderBoundedByMult_iff _a0).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hres := hspec.resolves _a0 hadmNonMonomial hdim' hob
  rw [isResolution_iff, lastIdeal_eq] at hres
  let s := A _a0
  have hempty := hres
  have hmu_ := le_trans hT.one_le_mult _a5.1
  exact maxOrder_lt_of_orderAtLeastLocus_eq_empty (s.ideal s.length) ((hspec.order_le _a0 hadmNonMonomial hdim' hob) s.length le_rfl) hmu_ hempty

end

section

section
variable (hG : PrincipalizationGeometryHypotheses) (hinv : ComapIsoInvariance) {n} {A B} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
include hG hspec hT hdim
theorem maxOrderNonMonomial_iter_add_le_of_forall_le N
    (hall : ∀ f : ℕ, f ≤ N → NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f)) f :
    f ≤ N →
      maxOrderNonMonomial T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) + f ≤
        maxOrder (nonMonomialPart T.boundary T.ideal) := by
  induction f with
  | zero =>
      intro _
      have h0 : maxOrderNonMonomial T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) 0) =
          maxOrder (nonMonomialPart T.boundary T.ideal) := by
        rw [nonMonomialOrderReductionIter_zero hinv T $ principalizationOfDimLe T A]
        exact rfl
      omega
  | succ f ih =>
      intro hf
      have hf' : f ≤ N := by omega
      have hc := hall f hf'
      have hlt := maxOrderNonMonomial_extendByNonMonomialPart_lt hG hinv hspec hT hdim
        (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f) hc
      have hih := ih hf'
      rw [nonMonomialOrderReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) f hc]
      omega

theorem not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction :
    ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) := by
  intro hcont
  let _a1 := principalizationOfDimLe T A
  rw [nonMonomialOrderReduction_eq hinv T _a1] at hcont
  let _a0 := maxOrder $ nonMonomialPart T.boundary T.ideal
  have hall : ∀ f, f ≤ _a0 + 1 →
      NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T _a1 f) := by
    intro f hf
    by_contra hnc
    have he := nonMonomialOrderReductionIter_eq_of_not_continues hinv T _a1 f hnc
      (_a0 + 1) hf
    rw [he] at hcont
    exact hnc hcont
  have hfin := maxOrderNonMonomial_iter_add_le_of_forall_le hG hinv hspec hT hdim
    (_a0 + 1) hall
    (_a0 + 1) le_rfl
  omega

theorem nonMonomialOrderReductionIter_eq_of_maxOrder_lt g
    (hg : maxOrder (nonMonomialPart T.boundary T.ideal) + 1 ≤ g) :
    nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) g = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) := by
  let _a1 := principalizationOfDimLe T A
  let _a0 := nonMonomialOrderReduction_eq hinv T _a1
  let _a2 := nonMonomialPart T.boundary T.ideal
  have hnc : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T _a1
      (maxOrder _a2 + 1)) := by
    rw [← _a0]
    exact not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction hG hinv hspec hT hdim
  rw [_a0]
  exact nonMonomialOrderReductionIter_eq_of_not_continues hinv T _a1
    (maxOrder _a2 + 1) hnc g hg
end

theorem hasPrincipalizationCenter_of_principalizationCertificate {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (t : MarkedBlowupSequenceData p I m E) (mu_ i : ℕ)
    (hne : (↑(t.center i).support : CSet $ t.obj i).Nonempty)
    (hcert : PrincipalizationCertificate (t.obj i) (t.proj i ≫ p) (t.ideal i) mu_
      (t.toMarkedSequenceOfBlowups.boundaryLocus i) $ t.center i) :
    HasPrincipalizationCenter mu_ $ t.dataAt i := by
  refine ⟨hne, ?_⟩
  rwa [boundarySupport_dataAt]

section
variable (hG : PrincipalizationGeometryHypotheses)
include hG
theorem hasCenter_continuationByNonMonomialPart {n : ℕ} {A B : PrincipalizationAssignment}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : T.mbs)
    (hcont : NonMonomialOrderReductionContinues T s) (i : ℕ)
    (hi : i < (continuationByNonMonomialPart hG hspec hT hdim s hcont).length) :
    HasPrincipalizationCenter T.mult ((continuationByNonMonomialPart hG hspec hT hdim s hcont).dataAt i) := by
  let _a2 := lastNonMonomialPart T s
  let _a3 := maxOrderNonMonomial T s
  let _a0 := tripleAtLength_dim_le hG hT s _a2 _a3
  let _c0 := principalizationSeqAtEnd T (principalizationOfDimLe T A) s _a2 _a3 _a0
  let _c1 := continuationByNonMonomialPart hG hspec hT hdim s hcont
  have hadmNonMonomial := isAdmissible_nonMonomialTriple hG hT s hcont
  have hdim' :=
    le_trans _a0 hdim
  let _a1 := nonMonomialTriple T s
  have hob :=
    (isOrderBoundedByMult_iff _a1).2 fun x =>
      orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT s x
  have hne := hspec.center_nonempty _a1 hadmNonMonomial hdim' hob
  rw [continuationByNonMonomialPart_length hG hspec hT hdim s hcont] at hi
  have hprinc := principalizationCertificate_controlledTransform hG (isAdmissible_tripleAtLength hG hT s) (isMonomialSplitting_lastNonMonomialPart hG hT s) (((nonMonomialOrderReductionContinues_iff T s).1 hcont).1)
    _c0 (hspec.order_le _a1 hadmNonMonomial hdim' hob) (hspec.cert _a1 hadmNonMonomial hdim' hob) i hi
  have hidl : _c1.ideal i =
      MarkedSequenceOfBlowups.controlledTransform
        _c0
        (lastI s) T.mult i :=
    controlledTransform_ofMarkedSequence
      _c0
      (s.ideal s.length) T.mult i
  have hproj : _c1.proj i =
      _c0.projectionToBase i :=
    BlowupSequenceData.ofSequenceOfBlowups_projectionToBase
      _c0.toSequenceOfBlowups i
  have hbd : _c1.toMarkedSequenceOfBlowups.boundary i =
      _c0.boundary i := by
    rw [toMarkedSequence_boundary]
    exact ofMarkedSequence_boundary_eq_of_le
      _c0 i $ le_of_lt hi
  have hloc : _c1.toMarkedSequenceOfBlowups.boundaryLocus i =
      _c0.boundaryLocus i := by
    apply Set.ext
    intro x
    rw [mem_boundaryLocus_iff
      _c1.toMarkedSequenceOfBlowups i x]
    constructor
    intro hx
    rw [hbd] at hx
    exact (mem_boundaryLocus_iff
      _c0 i x).2 hx
    intro hx
    have hx' := (mem_boundaryLocus_iff
      _c0 i x).1 hx
    rwa [← hbd] at hx'
  refine hasPrincipalizationCenter_of_principalizationCertificate _c1 T.mult i (hne i hi) ?_
  rwa [hproj, hidl, hloc]

section
variable (hinv : ComapIsoInvariance) {n} {A B} (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
include hspec hT hdim
theorem hasCenter_nonMonomialOrderReductionIter f :
    ∀ i < (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).length,
      HasPrincipalizationCenter T.mult ((nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) f).dataAt i) := by
  let _c0 := principalizationOfDimLe T A
  induction f with
  | zero =>
      intro i hi
      rw [nonMonomialOrderReductionIter_zero hinv T _c0, emptyMarkedBlowupSequenceData_length] at hi
      exact absurd hi $ not_lt_zero i
  | succ f ih =>
      by_cases hc : NonMonomialOrderReductionContinues T $ nonMonomialOrderReductionIter hinv T _c0 f
      have he : nonMonomialOrderReductionIter hinv T _c0 (f + 1) =
          (nonMonomialOrderReductionIter hinv T _c0 f).append
            (continuationByNonMonomialPart hG hspec hT hdim (nonMonomialOrderReductionIter hinv T _c0 f) hc) hinv := by
        rw [nonMonomialOrderReductionIter_succ_of_continues hinv T _c0 f hc,
          extendByNonMonomialPart_eq_append hG hinv hspec hT hdim (nonMonomialOrderReductionIter hinv T _c0 f) hc]
      rw [he]
      intro i hi
      exact append_dataAt_of_forall _ _ hinv
        (HasPrincipalizationCenter T.mult)
        (isInvariantUnderIso_hasPrincipalizationCenter hG.maxContactTransport T.mult) ih
        (fun j hj => hasCenter_continuationByNonMonomialPart hG hspec hT hdim _ hc j hj) i hi
      rwa [nonMonomialOrderReductionIter_succ_of_not_continues hinv T _c0 f hc]

theorem hasCenter_nonMonomialOrderReduction i
    (hi : i < (nonMonomialOrderReduction hinv T $ principalizationOfDimLe T A).length) :
    HasPrincipalizationCenter T.mult $ (nonMonomialOrderReduction hinv T $ principalizationOfDimLe T A).dataAt i := by
  rw [nonMonomialOrderReduction_eq hinv T $ principalizationOfDimLe T A] at hi ⊢
  exact hasCenter_nonMonomialOrderReductionIter hG hinv hspec hT hdim _ i hi

theorem orderAt_lastNonMonomialPart_nonMonomialOrderReduction_lt
    x :
    orderAt (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) x < ((mult T : ℕ) : ENat) := by
  let _c0 := nonMonomialOrderReduction hinv T $ principalizationOfDimLe T A
  have hB :=
    fun y => orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT _c0 y
  have : Nonempty
      (lastO _c0) := ⟨x⟩
  let _a0 := lastNonMonomialPart T _c0
  have hnc :=
    not_nonMonomialOrderReductionContinues_nonMonomialOrderReduction hG hinv hspec hT hdim
  rw [nonMonomialOrderReductionContinues_iff] at hnc
  have hmax : maxOrderNonMonomial T _c0 =
      maxOrder _a0 := rfl
  refine orderAt_lt_of_maxOrder_lt _a0 hB ?_ x
  by_contra hle
  push Not at hle
  exact hnc ⟨by rw [hmax]; exact hle, by rw [hmax]; exact orderAtLeastLocus_maxOrder_nonempty _a0 hB⟩
end
end

end




def OrderAtComapOffExceptionalLocus : Prop :=
  ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (X' : Sch) (pi_ : X' ⟶ scheme T) (Z : tISD T), IsBlowupAlongIdealSheaf pi_ Z →
      ∀ x' : ↥X', x' ∉ support (exceptionalIdeal pi_ Z) →
        ∀ A : T.scheme.IdealSheafData, orderAt (A.comap pi_) x' = orderAt A (pi_ x')

theorem orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses (h : MonomialGeometryHypotheses) :
    OrderAtComapOffExceptionalLocus :=
  h.orderAt_comap_off_exceptional

theorem orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (hgeom : OrderAtComapOffExceptionalLocus)
    (T : MarkedIdealWithBoundary) (hT : T.IsAdmissible) (Z : tISD T)
    (X' : Sch) (pi_ : X' ⟶ scheme T) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
    (J : tISD T) (mu_ : ℕ)
    (hZ : (↑Z.support : CSet T.scheme) ⊆ orderAtLeastLocus J mu_)
    (J' : ISD X')
    (hJ' : exceptionalIdeal pi_ Z ^ mu_ * J' = J.comap pi_)
    (c : ℕ) (hc : c ≤ mu_) :
    orderAtLeastLocus J' c ⊆ ⇑pi_ ⁻¹' orderAtLeastLocus J c := by
  intro x' hx'
  rw [m163, mem_orderAtLeastLocus_iff]
  by_cases hE : x' ∈ support (p5 pi_ Z)
  have hmem : x' ∈ (support (Z.comap pi_) : Set X') := by
    rwa [← p9 pi_ Z]
  have hpix : pi_ x' ∈ (support Z) := by simp_all
  have h2 := (mem_orderAtLeastLocus_iff J mu_ $ pi_ x').1 $ hZ hpix
  exact le_trans (by exact_mod_cast hc) h2
  have h1 := hgeom T hT X' pi_ Z hpi_ x' hE J
  have h2 := add_orderAt_le_orderAt_mul (p5 pi_ Z ^ mu_) J' x'
  rw [hJ', h1] at h2
  exact le_trans ((mem_orderAtLeastLocus_iff J' c x').1 hx') $ le_trans le_add_self h2

section
variable {X} (s : SequenceOfBlowups X)
theorem transitionMap_refl_apply {i} (h : i ≤ i)
    x : transitionMap s h x = x :=
  congrFun (congrArg (fun f : sbAt s i ⟶ sbAt s i => (f : (sbAt s i) → sbAt s i))
    (s.transitionMap_self h)) x

theorem transitionMap_comp_apply {i j l} (hij : i ≤ j)
    (hjl : j ≤ l) x :
    transitionMap s hij (transitionMap s hjl x) = transitionMap s (hij.trans hjl) x := by
  calc s.transitionMap hij (transitionMap s hjl x) = (transitionMap s hjl ≫ transitionMap s hij) x := rfl
    _ = transitionMap s (hij.trans hjl) x := by rw [s.transitionMap_trans hij hjl]
end

namespace MarkedSequenceOfBlowups

section
variable (hgeom : OrderAtComapOffExceptionalLocus) (T : MarkedIdealWithBoundary) (s : T.SequenceOfBlowups) (hval : ∀ i ≤ s.toSequenceOfBlowups.length, (T.transformAt s i).IsAdmissible)
include hgeom hval
theorem orderAtLeastLocus_subset_preimage_transitionMap
    c (hc : c ≤ mult T) i j (hij : i ≤ j) (hj : j ≤ s.toSequenceOfBlowups.length) :
    orderAtLeastLocus (s.ideal j) c ⊆ ⇑(s.toSequenceOfBlowups.transitionMap hij) ⁻¹' orderAtLeastLocus (s.ideal i) c := by
  revert hj
  induction j, hij using le_induction with
  | base =>
      intro _ x hx
      rwa [m163, transitionMap_refl_apply]
  | succ j hij ih =>
      intro hj1
      have hjlt := lt_of_succ_le hj1
      have hstep := by
        let i := j
        let hi := hjlt
        exact orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf hgeom (T.transformAt s i) (hval i $ le_of_lt hi)
          (msCtr s i) (msAt s (i + 1)) (msTrS s i)
          (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) (s.ideal i) T.mult (s.center_order i hi)
          (s.ideal (i + 1)) (s.ideal_succ i hi) c hc
      intro x hx
      rw [m163]
      have h2 : s.toSequenceOfBlowups.transitionMap hij (s.toSequenceOfBlowups.transitionMapSucc j x) ∈
          orderAtLeastLocus (s.ideal i) c := (ih $ le_of_lt hjlt) (hstep hx)
      rwa [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap j, transitionMap_comp_apply] at h2
end

end MarkedSequenceOfBlowups




section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {J : ISD X} {mu_ : ℕ} {E : Bdy X}

def MarkedSequenceOfBlowups.controlledNonMonomialTransform (t : MarkedSequenceOfBlowups p J mu_ E) (N : ISD X) (c : ℕ) :
    ∀ i : ℕ, IdealSheafData $ t.schemeAt i
  | 0 => N.comap t.isoZero.hom
  | i + 1 =>
      residualByPow ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c i).comap $ t.transitionMapSucc i) (t.exceptionalDivisor i) c

def MarkedSequenceOfBlowups.controlledMonomialTransform (t : MarkedSequenceOfBlowups p J mu_ E) (M : ISD X) (a c : ℕ) :
    ∀ i : ℕ, IdealSheafData $ t.schemeAt i
  | 0 => M.comap t.isoZero.hom
  | i + 1 =>
      residualByPow ((MarkedSequenceOfBlowups.controlledMonomialTransform t M a c i).comap (t.transitionMapSucc i) * t.exceptionalDivisor i ^ c)
        (t.exceptionalDivisor i) a

section
variable (t : MarkedSequenceOfBlowups p J mu_ E)
@[simp]
theorem MarkedSequenceOfBlowups.controlledNonMonomialTransform_zero (N : ISD X)
    (c : ℕ) : MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c 0 = N.comap t.isoZero.hom :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledNonMonomialTransform_succ (N : ISD X)
    (c i : ℕ) :
    MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c (i + 1) =
      residualByPow ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N c i).comap $ t.transitionMapSucc i) (t.exceptionalDivisor i) c :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledMonomialTransform_zero (M : ISD X)
    (a c : ℕ) : MarkedSequenceOfBlowups.controlledMonomialTransform t M a c 0 = M.comap t.isoZero.hom :=
  rfl

@[simp]
theorem MarkedSequenceOfBlowups.controlledMonomialTransform_succ (M : ISD X)
    (a c i : ℕ) :
    MarkedSequenceOfBlowups.controlledMonomialTransform t M a c (i + 1) =
      residualByPow ((MarkedSequenceOfBlowups.controlledMonomialTransform t M a c i).comap (t.transitionMapSucc i) * t.exceptionalDivisor i ^ c)
        (t.exceptionalDivisor i) a :=
  rfl
end

end

section

theorem isAdmissible_withIdealAndMult_pow_sup_pow {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible)
    {N : tISD T} {s : ℕ} (hs : 1 ≤ s)
    (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ENat)) :
    (T.withIdealAndMult (N ^ T.mult ⊔ T.ideal ^ s) $ mult T * s).IsAdmissible ∧
      ∀ x : ↥T.scheme, orderAt (N ^ T.mult ⊔ T.ideal ^ s) x ≤ ((mult T * s : ℕ) : ENat) := by
  have hcz := hT.charZero
  have hsm := hT.smooth
  have hle := fun x =>
    orderAt_pow_sup_pow_le T.base T.structMap N T.ideal T.mult s hord x
  have hsub : (support (N ^ tMu T ⊔ T.ideal ^ s) : CSet T.scheme) ⊆
      (T.ideal.support) := by
    intro x hx
    by_contra hc
    have h1 :=
      (one_le_orderAt_iff_mem_support (N ^ tMu T ⊔ T.ideal ^ s) x).2 hx
    rw [orderAt_pow_sup_pow T.base T.structMap N T.ideal T.mult s x] at h1
    have h2 := le_trans h1 $ min_le_right _ _
    rw [(orderAt_eq_zero_iff_not_mem_support T.ideal x).2 hc, mul_zero] at h2
    simp at h2
  have hnz : NonzeroOnComponents $ N ^ tMu T ⊔ T.ideal ^ s := by
    rw [nonzeroOnComponents_iff]
    intro Z hZ hZsub
    exact (nonzeroOnComponents_iff T.ideal).1 hT.nonzeroOnComponents Z hZ $ hZsub.trans hsub
  have hmult : 1 ≤ tMu T * s := by
    simpa using (Nat.mul_le_mul hT.one_le_mult hs)
  exact ⟨{ charZero := hT.charZero
           locallyOfFiniteType := hT.locallyOfFiniteType
           nonzeroOnComponents := hnz
           one_le_mult := hmult
           quasiCompact := hT.quasiCompact
           smooth := hT.smooth
           snc := hT.snc }, hle⟩

section
variable (hG : PrincipalizationGeometryHypotheses) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) {M N : T.scheme.IdealSheafData} (hsplit : IsMonomialSplitting T.boundary T.ideal M N) {s : ℕ} (hs : 1 ≤ s) (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ENat)) (t : MarkedSequenceOfBlowups T.structMap (N ^ T.mult ⊔ T.ideal ^ s) (mult T * s) T.boundary)
include hG hT hsplit hs hord
theorem isMonomialSplitting_controlledTransform_of_le_length
    (i : ℕ) (hi : i ≤ t.length) :
    t.ideal i =
        MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i ^ T.mult ⊔
          MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i ^ s ∧
      IsMonomialSplitting (t.boundary i) (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i)
        (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s i) (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) ∧
      ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult,
        orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x ≤ (s : ENat) := by
  have := hT.charZero
  have := hT.smooth
  have hECNC := effectiveCartierSupportContainsNoComponent
  have hm := hT.one_le_mult
  have hT' := (isAdmissible_withIdealAndMult_pow_sup_pow hT hs hord).1
  let _a7 := s
  have key : ∀ j, j ≤ t.length →
      (t.ideal j = MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s j ^ T.mult ⊔
          MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult j ^ s ∧
        IsMonomialSplitting (t.boundary j) (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult j)
          (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s j) (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s j) ∧
        ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult j) T.mult,
          orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s j) x ≤ _a7) := by
    intro j
    induction j with
    | zero =>
        intro _
        refine ⟨?_, ?_, ?_⟩
        rw [t.ideal_zero, MarkedSequenceOfBlowups.controlledNonMonomialTransform_zero, MarkedSequenceOfBlowups.controlledTransform_zero,
          comap_sup, comap_pow,
          comap_pow]
        rw [t.boundary_zero, MarkedSequenceOfBlowups.controlledTransform_zero, MarkedSequenceOfBlowups.controlledMonomialTransform_zero,
          MarkedSequenceOfBlowups.controlledNonMonomialTransform_zero]
        exact hsplit.comap_iso t.isoZero
        intro x hx
        have h1 : T.mult ≤ orderAt (T.ideal.comap t.isoZero.hom) x :=
          (mem_orderAtLeastLocus_iff _ _ _).1 hx
        rw [orderAt_comap_of_isIso] at h1
        have h2 := hord _ $ (mem_orderAtLeastLocus_iff _ _ _).2 h1
        show orderAt (N.comap t.isoZero.hom) x ≤ _a7
        rwa [orderAt_comap_of_isIso]
    | succ n ih =>
        intro hn
        have hn' := hn
        obtain ⟨ih1, ih2, ih3⟩ := ih $ le_of_lt hn'
        have hbl := t.isBlowupAlongIdealSheaf_blowupMorphism n hn'
        have hexc : exceptionalIdeal (t.transitionMapSucc n) (t.center n) = t.exceptionalDivisor n := by
          rw [exceptionalDivisor_eq, exceptionalIdeal_eq_comap]
        have hFcart : IsLocallyGeneratedByNonZeroDivisor $ t.exceptionalDivisor n := by
          rw [← hexc]
          exact isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hbl
        have hTn := p38 hECNC hT' t n $ le_of_lt hn'
        have : Smooth $ projectionToSpec t n :=
          smooth_projectionToSpec hECNC hT' t n $ le_of_lt hn'
        have : Smooth $ projectionToSpec t $ n + 1 :=
          smooth_projectionToSpec hECNC hT' t (n + 1) hn
        have : IsNoetherian $ t.schemeAt $ n + 1 :=
          p25 hECNC hT' t (n + 1) hn
        have hsmn : Smooth
            ((t.center n).si ≫ projectionToSpec t n) := by
          rw [projectionToSpec_eq]
          exact t.center_smooth n hn'
        have hsncn : HasStrictNormalCrossingsWith (projectionToSpec t n) (t.center n) $ t.boundary n := by
          rw [projectionToSpec_eq]
          exact t.center_snc n hn'
        have hcos : orderAtLeastLocus (t.ideal n) (T.mult * s)
            = orderAtLeastLocus (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n) s ∩
              orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult := by
          rw [ih1]
          exact orderAtLeastLocus_pow_sup_pow T.base (projectionToSpec t n) _ _ hm hs
        have hZord : ∀ x ∈ (t.center n).support,
            orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n) x = _a7 := by
          intro x hx
          have hx1 := t.center_order n hn' hx
          rw [hcos] at hx1
          exact le_antisymm (ih3 x hx1.2) $ (mem_orderAtLeastLocus_iff _ _ _).1 hx1.1
        have hZP : (↑(t.center n).support : CSet $ t.schemeAt n)
            ⊆ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n) T.mult := by
          intro x hx
          have hx1 := t.center_order n hn' hx
          rw [hcos] at hx1
          exact hx1.2
        have hAle : MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n ≤ t.center n ^ s := by
          refine le_pow_of_hasStrictNormalCrossingsWith (projectionToSpec t n) (t.center n) _
            (t.boundary n) hsncn s ?_
          intro x hx
          exact (mem_orderAtLeastLocus_iff _ _ _).2 $ le_of_eq (hZord x hx).symm
        have hPdiv : ∃ B, t.exceptionalDivisor n ^ T.mult * B
            = (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n).comap (t.transitionMapSucc n) := by
          refine (hFcart.pow T.mult).exists_mul_eq ?_
          rw [← hexc]
          exact comap_le_exceptionalIdeal_pow (t.transitionMapSucc n) $ le_pow_of_hasStrictNormalCrossingsWith (projectionToSpec t n) (t.center n) _ (t.boundary n) hsncn T.mult hZP
        have hAdiv : ∃ B, t.exceptionalDivisor n ^ s * B
            = (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n) := by
          refine (hFcart.pow s).exists_mul_eq ?_
          rw [← hexc]
          exact comap_le_exceptionalIdeal_pow (t.transitionMapSucc n) hAle
        have hPtw : t.exceptionalDivisor n ^ T.mult *
            MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1)
            = (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n).comap (t.transitionMapSucc n) := by
          rw [MarkedSequenceOfBlowups.controlledTransform_succ]
          exact pow_mul_residualByPow _ _ _ hPdiv
        have hAtw : t.exceptionalDivisor n ^ s * MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1)
            = (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n) := by
          rw [MarkedSequenceOfBlowups.controlledNonMonomialTransform_succ]
          exact pow_mul_residualByPow _ _ _ hAdiv
        have hPtw' : p5 (t.transitionMapSucc n) (t.center n) ^ T.mult *
            MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1)
            = (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult n).comap (t.transitionMapSucc n) := by simp_all
        have hAtw' : p5 (t.transitionMapSucc n) (t.center n) ^ s *
            MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1)
            = (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap (t.transitionMapSucc n) := by simp_all
        have hCtw : t.exceptionalDivisor n ^ T.mult * MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s (n + 1)
            = (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s n).comap (t.transitionMapSucc n) *
              t.exceptionalDivisor n ^ s := by
          rw [MarkedSequenceOfBlowups.controlledMonomialTransform_succ]
          refine pow_mul_residualByPow _ _ _ ?_
          obtain ⟨Cc, hCc⟩ := exists_exceptionalIdeal_pow_mul_eq_comap_mul_pow hG _ hTn (t.center n) hsmn hsncn _ (t.transitionMapSucc n) hbl _ _ _ T.mult s ih2 hZP hZord _ hPtw' _ hAtw'
          refine ⟨Cc, ?_⟩
          rwa [← hexc]
        have hCtw' : p5 (t.transitionMapSucc n) (t.center n) ^ T.mult *
            MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s (n + 1)
            = (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s n).comap (t.transitionMapSucc n) *
              p5 (t.transitionMapSucc n) (t.center n) ^ s := by simp_all
        refine ⟨?_, ?_, ?_⟩
        have hidsucc : t.exceptionalDivisor n ^ (T.mult * s) * t.ideal (n + 1)
            = (t.ideal n).comap (t.transitionMapSucc n) := by
          rw [← hexc]
          exact t.ideal_succ n hn'
        have hcancel : t.exceptionalDivisor n ^ (T.mult * s) * t.ideal (n + 1)
            = t.exceptionalDivisor n ^ (T.mult * s) *
              (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s (n + 1) ^ T.mult ⊔
                MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult (n + 1) ^ s) := by
          rw [hidsucc, ih1, Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.comap_pow,
            Scheme.IdealSheafData.comap_pow, ← hAtw, ← hPtw, mul_pow, mul_pow, ← pow_mul,
            ← pow_mul, mul_inf, Nat.mul_comm s T.mult]
        exact (hFcart.pow $ T.mult * s).eq_of_mul_eq_mul hcancel
        rw [t.boundary_succ n hn']
        exact isMonomialSplitting_of_isBlowupAlongIdealSheaf hG _ hTn (t.center n) hsmn hsncn _
          (t.transitionMapSucc n) hbl _ _ _ T.mult s ih2 hZP hZord _ hPtw' _ hAtw' _ hCtw'
        intro x hx
        by_cases hxE : x ∈ (p5 (t.transitionMapSucc n) $ t.center n).support
        exact hG.controlledTransform_orderAt_le _ hTn (t.center n) hsmn hsncn _
          (t.transitionMapSucc n) hbl _ s hZord _ hAtw' x hxE
        have hcs :=
          orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses hG.monomialInputs) _ hTn (t.center n) _ (t.transitionMapSucc n)
            hbl _ T.mult hZP _ hPtw' T.mult le_rfl
        have hord2 := ih3 _ $ hcs hx
        have hoff := hG.monomialInputs.orderAt_comap_off_exceptional _ hTn _
          (t.transitionMapSucc n) (t.center n) hbl x hxE $ MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n
        have hoff' : orderAt ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap $ t.transitionMapSucc n) x
            = orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n) ((t.transitionMapSucc n) x) := hoff
        have hx0 : orderAt (t.exceptionalDivisor n) x = 0 := by
          rw [← hexc]
          exact (orderAt_eq_zero_iff_not_mem_support _ _).2 hxE
        have hsplit2 :
            orderAt ((MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s n).comap $ t.transitionMapSucc n) x
              = orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s $ n + 1) x := by
          rw [← hAtw, orderAt_mul T.base $ projectionToSpec t $ n + 1,
            orderAt_pow T.base $ projectionToSpec t $ n + 1, hx0, mul_zero, zero_add]
        rwa [← hsplit2, hoff']
  exact key i hi

theorem exists_exceptionalDivisor_pow_mul_eq_comap_of_lt_length
    (i : ℕ) (hi : i < t.length) :
    (∀ x ∈ (t.center i).support,
        orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i) x = (s : ENat)) ∧
      (↑(t.center i).support : CSet $ t.schemeAt i) ⊆
        orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i) T.mult ∧
      (∃ A : IdealSheafData $ t.schemeAt $ i + 1,
        t.exceptionalDivisor i ^ T.mult * A =
          (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i).comap (t.transitionMapSucc i)) ∧
      (∃ B : IdealSheafData $ t.schemeAt $ i + 1,
        t.exceptionalDivisor i ^ s * B =
          (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i).comap (t.transitionMapSucc i)) ∧
      (∃ C : IdealSheafData $ t.schemeAt $ i + 1,
        t.exceptionalDivisor i ^ T.mult * C =
          (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s i).comap (t.transitionMapSucc i) *
            t.exceptionalDivisor i ^ s) := by
  let _c0 := MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult i
  let _c1 := MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s i
  classical
  have hECNC := effectiveCartierSupportContainsNoComponent
  have hadm :=
    (isAdmissible_withIdealAndMult_pow_sup_pow hT hs hord).1
  have hlevel :=
    p38 hECNC hadm t i $ le_of_lt hi
  have hchar := hT.charZero
  have hsmooth : Smooth $ t.projectionToSpec i :=
    smooth_projectionToSpec hECNC hadm t i $ le_of_lt hi
  have hnoeth :=
    p25 hECNC hadm t (i + 1) hi
  obtain ⟨hideal_i, hsplit_i, hord_i⟩ :=
    isMonomialSplitting_controlledTransform_of_le_length hG hT hsplit hs hord t i $ le_of_lt hi
  have hexc : t.exceptionalDivisor i = exceptionalIdeal (t.transitionMapSucc i) (t.center i) := by
    rw [exceptionalDivisor_eq, exceptionalIdeal_eq_comap]
  have hbl := t.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have hsncc : HasStrictNormalCrossingsWith (t.projectionToSpec i) (t.center i) $ t.boundary i := by
    rw [projectionToSpec_eq]
    exact t.center_snc i hi
  let _a2 := t.center i
  have hsm : Smooth $ _a2.si ≫ t.projectionToSpec i := by
    rw [projectionToSpec_eq]
    exact t.center_smooth i hi
  let _a0 := (T.mult : ENat)
  let _a1 := (s : ENat)
  have key : ∀ x ∈ _a2.support,
      orderAt _c1 x = _a1 ∧
        _a0 ≤ orderAt _c0 x := by
    intro x hx
    have hx0 :=
      (mem_orderAtLeastLocus_iff _ _ _).1 $ t.center_order i hi hx
    rw [hideal_i, orderAt_pow_sup_pow T.base (t.projectionToSpec i) _ _ _ _ x, le_min_iff,
      cast_mul] at hx0
    obtain ⟨h1, h2⟩ := hx0
    have h1' :=
      (natCast_mul_le_mul_iff hT.one_le_mult s _).1 h1
    have h2' : _a0 ≤ orderAt _c0 x := by
      refine (natCast_mul_le_mul_iff hs T.mult _).1 ?_
      rwa [mul_comm _a1 _a0]
    exact ⟨le_antisymm (hord_i x $ (mem_orderAtLeastLocus_iff _ _ _).2 h2') h1', h2'⟩
  let _m0 := _a2.supp
  have hZP : _m0 ⊆
      orderAtLeastLocus _c0 T.mult := by
    intro x hx
    exact (mem_orderAtLeastLocus_iff _ _ _).2 (key x hx).2
  have hZord : _m0 ⊆
      orderAtLeastLocus _c1 s := by
    intro x hx
    exact (mem_orderAtLeastLocus_iff _ _ _).2 $ le_of_eq (key x hx).1.symm
  have hPle :=
    le_pow_of_hasStrictNormalCrossingsWith (t.projectionToSpec i) (t.center i)
      _c0 (t.boundary i) hsncc T.mult hZP
  have hAle :=
    le_pow_of_hasStrictNormalCrossingsWith (t.projectionToSpec i) (t.center i)
      _c1 (t.boundary i) hsncc s hZord
  obtain ⟨B', hB', -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (t.transitionMapSucc i) (t.center i)
    _c0 T.mult hbl hPle
  obtain ⟨A', hA', -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (t.transitionMapSucc i) (t.center i)
    _c1 s hbl hAle
  obtain ⟨C', hC'⟩ := exists_exceptionalIdeal_pow_mul_eq_comap_mul_pow hG _ hlevel
    (t.center i) hsm hsncc (t.schemeAt $ i + 1) (t.transitionMapSucc i) hbl
    _c0
    (MarkedSequenceOfBlowups.controlledMonomialTransform t M T.mult s i)
    _c1 T.mult s hsplit_i hZP
    (fun x hx => (key x hx).1) B' hB' A' hA'
  refine ⟨fun x hx => (key x hx).1, hZP, ⟨B', ?_⟩, ⟨A', ?_⟩, ⟨C', ?_⟩⟩
  rwa [hexc]
  rwa [hexc]
  rwa [hexc]

theorem orderAt_controlledNonMonomialTransform_length_lt
    (hempty : orderAtLeastLocus (t.ideal t.length) (mult T * s) = ∅) :
    ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult t.length) T.mult,
      orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s t.length) x < (s : ENat) := by
  classical
  have hchar := hT.charZero
  have hsmooth : Smooth $ t.projectionToSpec t.length :=
    smooth_projectionToSpec effectiveCartierSupportContainsNoComponent (left $ isAdmissible_withIdealAndMult_pow_sup_pow hT hs hord) t t.length le_rfl
  obtain ⟨hideal, -, -⟩ := isMonomialSplitting_controlledTransform_of_le_length hG hT hsplit hs hord t t.length le_rfl
  rw [hideal] at hempty
  exact (orderAtLeastLocus_pow_sup_pow_eq_empty_iff T.base (t.projectionToSpec t.length)
      (MarkedSequenceOfBlowups.controlledNonMonomialTransform t N s t.length)
      (MarkedSequenceOfBlowups.controlledTransform t T.ideal T.mult t.length) hT.one_le_mult hs).1 hempty
end

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {J : ISD X} {mu_ : ℕ} {E : Bdy X} (s : MarkedSequenceOfBlowups p J mu_ E) (I : ISD X) (m i : ℕ)
theorem controlledTransform_eq_ofMarkedSequence_controlledTransform :
    MarkedSequenceOfBlowups.controlledTransform s I m i
      = (s.toBsd).controlledTransform I m i := by
  let _a0 := s.toBsd
  induction i with
  | zero =>
      exact sy_ $ p53 _a0 I m
  | succ n ih =>
      exact m32 (congrArg (fun Jj : IdealSheafData (s.schemeAt n) => residualByPow (Jj.comap $ s.transitionMapSucc n) (s.exceptionalDivisor n) m) ih) (BlowupSequenceData.controlledTransform_succ _a0 I m n).symm

end

theorem isMarked_ofMarkedSequence_of_isMonomialSplitting (hG : PrincipalizationGeometryHypotheses) {T : MarkedIdealWithBoundary}
    (hT : T.IsAdmissible) {M N : T.scheme.IdealSheafData}
    (hsplit : IsMonomialSplitting T.boundary T.ideal M N)
    {s : ℕ} (hs : 1 ≤ s)
    (hord : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, orderAt N x ≤ (s : ENat))
    (t : MarkedSequenceOfBlowups T.structMap (N ^ T.mult ⊔ T.ideal ^ s) (T.mult * s) T.boundary) :
    t.toBsd.IsMarked T.structMap T.ideal T.mult
      T.boundary := by
  have hself := (ofMarkedSequence t).isMarked_toBlowupSequenceData
  refine ⟨?_, ?_, hself.center_smooth, hself.center_snc⟩
  intro i hi
  obtain ⟨A, hA⟩ := (exists_exceptionalDivisor_pow_mul_eq_comap_of_lt_length hG hT hsplit hs hord t i hi).2.2.1
  exact ⟨A, tr_ hA $ (fun s I m i => congrArg (fun Jj : (s.schemeAt i).IdealSheafData => Jj.comap $ s.transitionMapSucc i)
  (controlledTransform_eq_ofMarkedSequence_controlledTransform s I m i)) t T.ideal T.mult i⟩
  intro i hi
  intro x hx
  exact (mem_orderAtLeastLocus_iff _ _ _).2 ((congrArg (fun Jj : (t.schemeAt i).IdealSheafData => orderAt Jj x) (controlledTransform_eq_ofMarkedSequence_controlledTransform t T.ideal T.mult i)) ▸ (mem_orderAtLeastLocus_iff _ _ _).1 (((exists_exceptionalDivisor_pow_mul_eq_comap_of_lt_length hG hT hsplit hs hord t i hi).2.1) hx))

end

end FunctorialResolution.EmbeddedResolution

end
end
