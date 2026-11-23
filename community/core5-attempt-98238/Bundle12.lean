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
import Bundle11
noncomputable section
open CategoryTheory AlgebraicGeometry
open Category (assoc comp_id id_comp)
open FunctorialResolution.Blowup (BlowupIsProper IsBlowupAlongIdealSheaf StrictTransformIsBlowupOfClosedSubscheme blowupIsProper comap_io_support_compl_eq_top comap_ker_comp_of_isOpenImmersion exceptionalIdeal idealSheafData_prod_cons idealSheafData_prod_nil isBlowupAlongIdealSheaf_id_top ker_comp_coprod_inl_comap_inl ker_comp_coprod_inl_comap_inr range_coprod_inr_eq_compl smooth_coprod_desc smooth_of_isEmpty strictTransform)
open FunctorialResolution.EmbeddedResolution (BlowupSequenceData IsDerivBalanced IsMaxContactInvariant IsPullbackBlowupSequence MarkedBlowupSequenceData SequenceOfBlowupsPullback balancedTunedSheaf balancedTunedSheaf_comap balancedTunedSheaf_one componentUnionIdeal_support_eq_sUnion controlledTransform_not_subset_support derivIdealSheafIterate_comap_fieldBaseChange dimensionNonincreasingAlongBlowups effectiveCartierSupportContainsNoComponent exists_etale_equalizing_isMaxContactHypersurface exists_isMonomialSplitting exists_orderAt_le filterNeTop hasStrictNormalCrossingsWith_cons_of_le inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor instSurjectiveSpecMapOfFieldHom intersectionComponents_disjoint_of_smooth intersectionComponents_finite intersectionComponents_subset_support_iff isDerivBalanced_of_pow_le isLocallyNoetherian_of_isBlowupAlongIdealSheaf isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq isMaxContactHypersurface_strictTransform_of_orderAt_le isMaxContactInvariant_of_mul_le isMonomialSplitting_unique isOpen_preimage_sUnion_intersectionComponents isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition isSmoothDivisor_of_locally_coordIdeal isoInvariantOrderCertificateDescend krullDimSucc krullDimSucc_le_of_etale mem_comap_support_iff_base_mem_support mem_orderAtLeastLocus_iff one_le_orderAt_iff_mem_support openImmersionStability orderAtLeastLocus orderAt_comap_fieldBaseChange orderAt_ideal_le_mult_along_sequence orderCertificate_of_comap_of_isLocalIsomorphism quasiCompact_strictTransformio_of_isLocallyNoetherian restrictIdeal_eq_top_iff_forall_notMem_support support_strictTransform_subset_preimage tuningExponent tuningExponent_one)
open FunctorialResolution.EmbeddedResolution.MaxContactCoverData (balancedTunedIdeal cI cT coverMap coverMarkedBlowupData coverTriple coverTriple_boundary coverTriple_ideal coverTriple_mult coverTriple_structureMorphism derivedTriple derivedTriple_boundary derivedTriple_mult derivedTriple_structureMorphism etale_coverMap_of_isAdmissible flat_coverMap_of_isAdmissible instSmoothCoverMap isMaxContactCover_chosenCoverData isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isSmoothDivisor reduceAlongHypersurface_eq_appendLowerDimReduction separateBoundary_succ separateBoundary_zero smooth_coverMap_of_isAdmissible tunedMult)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (blowupMorphism_eq_transitionMap center isomorphic_refl lastStructMap_eq_projectionToBase projectionToBase projectionToBase_succ projectionToBase_zero schemeAt transitionMapSucc transitionMap_def withoutIsoBlowups_center_ne_top withoutIsoBlowups_centersLieOver withoutIsoBlowups_lastObj withoutIsoBlowups_lastStructMap)
open IsPullback (id_vert of_bot of_hasPullback of_horiz_isIso of_id_fst of_iso_pullback of_right)
open Nat (le_succ lt_of_succ_le lt_succ_iff lt_succ_of_lt lt_succ_self not_lt_zero sub_le succ_le_of_lt succ_le_succ succ_pred_eq_of_pos zero_le)
open Scheme.Hom (app appTop comp_appTop continuous isClosedEmbedding ker ker_comp_of_isIso le_ker_comp opensRange pre resLE resLE_comp_ι support_ker)
open Scheme.IdealSheafData (comap comap_comp comap_ideal_eq_map_appLE comap_mono comap_pow comap_top eq_top_iff_support_eq_empty ext_of_isAffine ker_fst_of_isClosedImmersion ker_subschemeι map_gc mem_support_comap mul_top range_subschemeι subscheme subschemeι support support_antitone support_mul support_sup support_top top_mul vanishingIdeal)
open Set (MapsTo disjoint_left eq_univ_iff_forall eq_univ_of_forall ext_iff image_congr image_image image_preimage_eq_inter_range image_singleton image_subset_iff mem_Iic mem_iUnion mem_ofPred_eq mem_preimage mem_range_self mem_sUnion mem_singleton mem_singleton_iff mem_univ nonempty_iff_ne_empty not_nonempty_iff_eq_empty not_subset preimage preimage_empty preimage_mono range_eq_empty_iff range_subset_iff sUnion_eq_biUnion sUnion_subset sdiff_subset singleton_subset_iff subset_empty_iff subset_inter subset_sUnion_of_mem subset_univ union_comm union_compl_self univ univ_subset_iff)
noncomputable section
open Classical (propDecidable)
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData (append_center_length append_center_of_length_lt boundary_append boundary_cons boundary_eq_map_iteratedStrictTransform_append iteratedStrictTransform_top iteratedStrictTransform_zero ofSequenceOfBlowups ofSequenceOfBlowups_center ofSequenceOfBlowups_projectionToBase projectionToBase_append_of_le_length projectionToBase_append_of_length_lt support_iteratedStrictTransform_subset_support toMarkedBlowupSequenceData_toBlowupSequenceData toSequenceOfBlowups toSequenceOfBlowups_projectionToBase)
open FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact (BoundarySeparated inStrictNormalCrossingPosition_iteratedStrictTransform_zero iteratedStrictTransform_eq_toBlowupSequenceData)
open FunctorialResolution.EmbeddedResolution.LowerDimReductionPullback (appendLowerDimReduction_eq_append baseChangeMapAtLength comapBoundaryBaseChange ideal_derivedTriple isBalanced_derivedTriple isOrderBoundedByMult_derivedTriple nonempty_strictPullbackSeq_appendLowerDimReduction_baseChange orderAt_ideal_length_le pullbackTriple structureMorphism_derivedTriple tunedIdealAtLength tunedIdealAtLength_eq_balancedTunedSheaf)
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (append_dataAt_of_forall append_toBlowupSequenceData boundarySupport_dataAt boundary_length dataAt_boundary dataAt_center dataAt_ideal dataAt_structMap ofMarkedSequence ofMarkedSequence_boundary ofMarkedSequence_controlledTransform ofMarkedSequence_length projectionToBase_eq_toBlowupSequenceData_projectionToBase toBlowupSequenceData_boundary_eq toBlowupSequenceData_boundary_eq_boundary_of_le toBlowupSequenceData_controlledTransform_eq toMarkedSequence_blowupMorphism toMarkedSequence_boundary toMarkedSequence_center toMarkedSequence_length toMarkedSequence_projectionToSpec toMarkedSequence_toSequenceOfBlowups)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (IsAdmissible SameNontrivialBoundary baseChange_boundary baseChange_ideal baseChange_structureMorphism bc bget ideal isOrderBoundedByMult_iff mk mult nontrivialPart nontrivialPart_append pullbackAlong pullbackAlong_boundary sameNontrivialBoundary_iff scheme structMap transformAt_boundary transformAt_structureMorphism validOfSameNontrivialBoundary withBoundary withBoundary_boundary withBoundary_self)
open FunctorialResolution.EmbeddedResolution.MaxContactReduction (IsMaxContactCover appendLowerDimReduction dropTrivialBoundary dropTrivialBoundary_boundary iteratedStrictTransform iteratedStrictTransform_succ reduceAlongHypersurface separateBoundary strictTransformAtLength strictTransformAtLength_eq)
open List (append get getElem_append_left getElem_map get_eq_getElem length length_cons length_map length_take lget map map_append map_congr_left map_cons map_nil mem_append mem_of_mem_drop prod_eq_one range take_append_drop)
open Or (inl inr)
open FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange (isAdmissible_derivedTriple_nil isStrictPullbackBlowupSeq_reduceAlongHypersurface orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero orderAt_pullbackTriple_le_mult separateBoundaryInvariant_separateBoundaryOfFamily separateBoundaryOfFamily)
open FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality (OrderReductionHypotheses exists_isStrictPullback_cover_dropTrivialBoundary length_eq_zero_of_orderAtLeastLocus_eq_empty lowerDimensionalFamily maxContactPrincipalization)
open TopologicalSpace (NoetherianSpace)
open Iff (mp mpr)
open Scheme.Opens (ι)
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence (strictTransformio)
open Scheme (IdealSheafData)
section


namespace FunctorialResolution.EmbeddedResolution

def HasOrderCertificateMultOne {k : Type} [Field k] (D : MarkedSchemeWithCenter k) : Prop :=
  OrderCertificate D.ambient D.structMap D.ideal 1 D.boundarySupport D.center

theorem isInvariantUnderIso_hasOrderCertificateMultOne (k : Type) [Field k] :
    IsInvariantUnderIso fun D : MarkedSchemeWithCenter k => HasOrderCertificateMultOne D := by
  intro D A e hD
  show OrderCertificate (D.transport e).ambient (D.transport e).structMap (D.transport e).ideal 1
      (D.transport e).boundarySupport (D.transport e).center
  rw [MarkedSchemeWithCenter.transport_projectionToBase, MarkedSchemeWithCenter.transport_ideal, MarkedSchemeWithCenter.transport_center,
    MarkedSchemeWithCenter.boundarySupport_transport]
  exact OrderCertificate.comap_iso_hom_comp e hD

namespace BoundarySeparationByMaxContact

def ContinuationOrderCertificate (hinv : ComapIsoInvariance) (A : ℕ → PrincipalizationAssignment) (P : ℕ → Prop)
    (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T) : Prop :=
  ∀ hft : LocallyOfFiniteType
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (cT h.valid).structMap),
    ∀ hmk : (ofSequenceOfBlowups (A 0 $ reduceAlongHypersurfaceTriple T h.valid hinv A hft).toSequenceOfBlowups).IsMarked
        ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
          (cT h.valid).structMap)
        ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
        (cT h.valid).mult
        ((separateAllBoundary T h.valid hinv A).boundary (separateAllBoundary T h.valid hinv A).length),
      ∀ i < (A 0 $ reduceAlongHypersurfaceTriple T h.valid hinv A hft).length,
        HasOrderCertificateMultOne
          ((continuationMarkedData (cT h.valid)
              (separateAllBoundary T h.valid hinv A) hft
              [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
                (cI h.valid)]
              (cT h.valid).boundary.length
              (A 0 $ reduceAlongHypersurfaceTriple T h.valid hinv A hft) hmk).dataAt i)

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X} (u : MarkedBlowupSequenceData p I m E)
theorem mem_boundary_zero_of_eq_comap (D : IdealSheafData (u.obj 0)) (C : ISD X)
    (hC : C ∈ E) (hD : D = C.comap u.toBlowupSequenceData.isoZero.hom) :
    D ∈ u.boundary 0 := by
  subst hD
  rw [u.boundary_zero]
  exact List.mem_map.2 ⟨C, hC, rfl⟩

section
variable (hN : ∀ i ≤ u.length, IsLocallyNoetherian (u.obj i))
include hN
theorem exists_mem_boundary_succ_of_map_mem_support
    {t} (ht : t < u.length) x
    (hx : ∃ J ∈ u.boundary t, (u.map t) x ∈ (J.support : CSet $ u.obj t)) :
    ∃ J ∈ u.boundary (t + 1), x ∈ (J.support : Set ↥(u.obj $ t + 1)) := by
  obtain ⟨J, hJ, hJx⟩ := hx
  have h1 : x ∈ preimage (u.map t) (⋃ C ∈ u.boundary t, suppI C) := by
    simp [mem_preimage, mem_iUnion, exists_prop]
    exact ⟨J, hJ, hJx⟩
  have h2 := u.preimage_iUnion_support_boundary_subset hN ht h1
  simp [mem_iUnion, exists_prop] at h2
  exact h2

section
variable (D : ∀ t : ℕ, IdealSheafData (u.obj t)) (hD0 : D 0 ∈ u.boundary 0) (hstep : ∀ t, t < u.length → ∀ x : ↥(u.obj (t + 1)), x ∈ ((D (t + 1)).support : Set ↥(u.obj (t + 1))) → (u.map t) x ∈ ((D t).support : CSet (u.obj t)))
include hD0 hstep
theorem exists_mem_boundary_of_mem_support_chain :
    ∀ t, t ≤ u.length → ∀ x : ↥(u.obj t), x ∈ ((D t).support : CSet $ u.obj t) →
      ∃ J ∈ u.boundary t, x ∈ (J.support : CSet $ u.obj t) := by
  intro t
  induction t with
  | zero =>
      intro _ x hx
      exact ⟨D 0, hD0, hx⟩
  | succ n ih =>
      intro hn x hx
      have hn' := hn
      exact exists_mem_boundary_succ_of_map_mem_support u hN hn' x $ ih (le_of_lt hn') _ $ hstep n hn' x hx

theorem hasOrderCertificateMultOne_dataAt_of_center_subset
    (hcen : ∀ t, t < u.length →
      ((u.center t).support : CSet $ u.obj t) ⊆ ((D t).support : CSet $ u.obj t)) :
    ∀ i < u.length, HasOrderCertificateMultOne $ u.dataAt i := by
  intro i hi
  refine OrderCertificate.memory ?_
  intro x hx
  obtain ⟨J, hJ, hJx⟩ := exists_mem_boundary_of_mem_support_chain u hN D hD0 hstep i (le_of_lt hi) x $ hcen i hi hx
  exact (MarkedSchemeWithCenter.mem_boundarySupport_iff (u.dataAt i) x).2 ⟨J, hJ, hJx⟩
end
end
end

section
variable (hstar : MaxContactCoverProperties) (hinv : ComapIsoInvariance) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment)
include hstar hmono
theorem hasOrderCertificateMultOne_appendLowerDimReduction (j : ℕ) (hspec : IsBoundaryDivisorReduction P j (A j) B)
    (T S : MarkedIdealWithBoundary) (hV : S.IsAdmissible) (hdim : S.krullDimSucc ≤ T.krullDimSucc) (hPdimT : P T.krullDimSucc)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ENat))
    (s : S.mbs)
    (hj : j < S.boundary.length)
    (hs : ∀ i < s.length, HasOrderCertificateMultOne $ s.dataAt i) :
    ∀ i < (appendLowerDimReduction hinv T (lowerDimensionalFamily A T) S s [] 0 j).length,
      HasOrderCertificateMultOne
        ((appendLowerDimReduction hinv T (lowerDimensionalFamily A T) S s [] 0
          j).dataAt i) := by
  let _a0 := lastP s ≫ tMp S
  have hft :=
    locallyOfFiniteType_projectionToBase_comp hstar S hV s s.length le_rfl
  have hsnc0 : InStrictNormalCrossingPosition _a0 $ lastB s := by
    have h0 := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length le_rfl).snc
    rw [transformAt_structureMorphism, transformAt_boundary,
      toMarkedSequence_projectionToSpec, toMarkedSequence_boundary] at h0
    exact h0
  have hsnc : InStrictNormalCrossingPosition _a0
      ([] ++ (lastB s).drop 0) := by
    rwa [List.nil_append, List.drop_zero]
  have hVc :=
    isAdmissible_derivedTriple hstar S hV s hft [] 0 hsnc
  have hdimC :=
    hstar.derivedTriple_dim_le hV s hft [] 0 hdim
  have hPC := hmono _ _ hdimC hPdimT
  have hjC : j < ([] ++ (lastB s).drop 0).length := by
    simp [List.nil_append, List.drop_zero, boundary_length s s.length le_rfl]
    omega
  have hsep : ∀ C ∈ (lastB s).take 0,
      orderAtLeastLocus (lastI s) S.mult ∩ suppI C = ∅ := by
    intro C hC
    simp at hC
  have hjS := hjC
  rw [← derivedTriple_boundary] at hjS
  obtain ⟨Dv, bv, -, hD0, hcen, hbt, hDst, -, -⟩ :=
    hspec.shape (derivedTriple S s hft [] 0) hVc hPC (isOrderBoundedByMult_derivedTriple hstar S hV hV.one_le_mult hO s hft [] 0 hVc) (isBalanced_derivedTriple hstar S hV hV.one_le_mult hO s hft [] 0 hVc) hjS
  obtain ⟨hmk, heq, -⟩ :=
    appendLowerDimReduction_eq_append hstar hinv T P A B j hspec
      (p49 A T) (fun _ _ _ => rfl) S hV hV.one_le_mult hO s [] 0 hft
      hdimC hPC hVc hjC hsep
  rw [heq]
  intro i hi
  refine append_dataAt_of_forall s _ hinv HasOrderCertificateMultOne
    (isInvariantUnderIso_hasOrderCertificateMultOne S.base) hs ?_ i hi
  have hbeq : (derivedTriple S s hft [] 0).boundary = lastB s := by
    rw [derivedTriple_boundary]
    simp
  have hmemE : (derivedTriple S s hft [] 0).boundary.lget j hjS ∈
      lastB s := by
    rw [← hbeq]
    exact List.getElem_mem hjS
  refine hasOrderCertificateMultOne_dataAt_of_center_subset _ ?_ Dv ?_ ?_ hcen
  intro n hn
  exact isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar S hV s hft [] 0 hVc
    (A j $ derivedTriple S s hft [] 0) n hn
  exact mem_boundary_zero_of_eq_comap
    ((ofSequenceOfBlowups (A j $ derivedTriple S s hft [] 0).toSequenceOfBlowups).toMarkedBlowupSequenceData
      _a0 (lastI s) S.mult (lastB s) hmk)
    (Dv 0) ((derivedTriple S s hft [] 0).boundary.lget j hjS) hmemE hD0
  intro n hn x hx
  by_cases hb0 : bv = true ∧ n = 0
  have hD1' : Dv (n + 1) = (Dv n).comap
      ((A j $ derivedTriple S s hft [] 0).transitionMapSucc n) := by
    obtain ⟨hbtrue, rfl⟩ := hb0
    exact (hbt hbtrue).2.2
  rw [hD1'] at hx
  exact (mem_comap_support_iff_base_mem_support _ _ x).1 hx
  rw [hDst n hn hb0] at hx
  exact support_strictTransform_subset_preimage _ _ _ hx

end

end BoundarySeparationByMaxContact





section
variable {k : Type} [Field k]
section
variable {W : Sch}
theorem orderCertificate_congr_morphism_ideal_center
    {p p' : W ⟶ Sp k} {N N' : ISD W} {mu_ : ℕ} {Mem : Set ↥W}
    {Z Z' : ISD W} (hp : p = p') (hN : N = N') (hZ : Z = Z')
    (h : OrderCertificate W p N mu_ Mem Z) : OrderCertificate W p' N' mu_ Mem Z' :=by simp_all
theorem orderCertificate_one_of_isSmoothDivisor
    (hin : OpenImmersionStability k) (p : W ⟶ Sp k)
    (N : ISD W) (Mem : Set ↥W) (Z : ISD W) (Dv : ISD W)
    (hDsm : IsSmoothDivisor p Dv)
    (hNsupp : (↑N.support : Set ↥W) ⊆ (↑Dv.support : Set ↥W))
    (hZH : (↑Z.support : Set ↥W) ⊆ (↑Dv.support : Set ↥W))
    (hcase : IsOpen (⇑Dv.si ⁻¹' (↑Z.support : Set ↥W)) ∨
      ∃ J : Dv.subscheme.IdealSheafData, NonzeroOnComponents J ∧
        (∀ x : ↥Dv.subscheme, Dv.si x ∉ Mem →
          ∃ V : Dv.subscheme.Opens, x ∈ V ∧
            J.comap V.i = (N.comap Dv.si).comap V.i) ∧
        PrincipalizationCertificate Dv.subscheme (Dv.si ≫ p) J 1 (⇑Dv.si ⁻¹' Mem)
          (Z.comap Dv.si)) :
    OrderCertificate W p N 1 Mem Z := by
  let _a3 := N.comap (⊤ : Opn W).i
  let _a4 := Z.comap (⊤ : Opn W).i
  have hoi : IsOpenImmersion (comapSubscheme (⊤ : Opn W).i Dv) :=
    hin.isOpenImmersion_comapSubscheme _ _
  have hkey : ∀ x : (Dv.comap (⊤ : Opn W).i).subscheme,
      (⊤ : Opn W).i ((Dv.comap (⊤ : Opn W).i).subschemeι x)
        = siI Dv ((comapSubscheme (⊤ : Opn W).i Dv) x) := by
    intro x
    have h2 := congrArg
      (fun f : (Dv.comap (⊤ : Opn W).i).subscheme ⟶ W => bsM f x) (comapSubscheme_comp (⊤ : Opn W).i Dv)
    simpa using h2.symm
  have hNH' : ∀ y, y ∈ _a3.support →
      y ∈ (Dv.comap (⊤ : Opn W).i).support := by
    intro y hy
    rw [mem_comap_support_iff_base_mem_support] at hy ⊢
    exact hNsupp hy
  have hZH' : ∀ y, y ∈ _a4.support →
      y ∈ (Dv.comap (⊤ : Opn W).i).support := by
    intro y hy
    rw [mem_comap_support_iff_base_mem_support] at hy ⊢
    exact hZH hy
  rcases hcase with hop | ⟨J, hJnz, hJloc, hJcert⟩
  refine OrderCertificate.descend (fun _ _ => ⊤) (fun _ _ => trivial)
    (fun _ _ => Dv.comap (⊤ : Opn W).i)
    (fun _ _ => hin.comap_isSmoothDivisor _ p Dv hDsm)
    (fun _ _ => hNH') (fun _ _ => hZH')
    (fun _ _ => none) ?_ ?_ ?_ ?_
  intro _ _ _
  have key : IsOpen ((comapSubscheme (⊤ : Opn W).i Dv) ⁻¹'
      (preimage Dv.si Z.supp)) :=
    ((comapSubscheme (⊤ : Opn W).i Dv) ⁻¹ᵁ
      (⟨_, hop⟩ : Dv.subscheme.Opens)).isOpen
  convert key using 1
  ext x
  simp only [mem_preimage]
  rw [← hkey x]
  exact mem_comap_support_iff_base_mem_support (⊤ : Opn W).i Z _
  simp_all
  simp_all
  simp_all
  refine OrderCertificate.descend (fun _ _ => ⊤) (fun _ _ => trivial)
    (fun _ _ => Dv.comap (⊤ : Opn W).i)
    (fun _ _ => hin.comap_isSmoothDivisor _ p Dv hDsm)
    (fun _ _ => hNH') (fun _ _ => hZH')
    (fun _ _ => some $ J.comap (comapSubscheme (⊤ : Opn W).i Dv)) ?_ ?_ ?_ ?_
  intro _ _ hcon
  exact absurd hcon (by simp)
  intro _ _ Jz hJz
  obtain rfl : Jz = J.comap (comapSubscheme (⊤ : Opn W).i Dv) := by simpa using hJz.symm
  exact hin.comap_nonzeroOnComponents _ J hJnz
  intro _ _ Jz hJz x hx
  obtain rfl : Jz = J.comap (comapSubscheme (⊤ : Opn W).i Dv) := by simpa using hJz.symm
  have hx' : siI Dv ((comapSubscheme (⊤ : Opn W).i Dv) x) ∉ Mem := by simp_all
  obtain ⟨V, hV, hVeq⟩ := hJloc _ hx'
  refine ⟨(comapSubscheme (⊤ : Opn W).i Dv) ⁻¹ᵁ V, hV, ?_⟩
  let _s0 := (comapSubscheme (⊤ : Opn W).i Dv) ⁻¹ᵁ V
  have e1 : opI _s0
        ≫ comapSubscheme (⊤ : Opn W).i Dv
      = resLE (comapSubscheme (⊤ : Opn W).i Dv) V
          _s0 le_rfl ≫ opI V :=
    (q4 _ _).symm
  let _a5 := N.comap Dv.si
  calc (J.comap (comapSubscheme (⊤ : Opn W).i Dv)).comap
          _s0.i
      = J.comap (opI _s0
          ≫ comapSubscheme (⊤ : Opn W).i Dv) :=
          (comap_comp _ _ _).symm
    _ = J.comap (resLE (comapSubscheme (⊤ : Opn W).i Dv) V
          _s0 le_rfl ≫ opI V) := by rw [e1]
    _ = (J.comap V.i).comap (resLE (comapSubscheme (⊤ : Opn W).i Dv) V
          _s0 le_rfl) :=
          comap_comp _ _ _
    _ = (_a5.comap V.i).comap
          (resLE (comapSubscheme (⊤ : Opn W).i Dv) V
            _s0 le_rfl) := by rw [hVeq]
    _ = _a5.comap
          (resLE (comapSubscheme (⊤ : Opn W).i Dv) V
            _s0 le_rfl ≫ opI V) :=
          (comap_comp _ _ _).symm
    _ = _a5.comap
          (_s0.i
            ≫ comapSubscheme (⊤ : Opn W).i Dv) := by rw [e1]
    _ = (_a5.comap (comapSubscheme (⊤ : Opn W).i Dv)).comap
          _s0.i :=
          comap_comp _ _ _
    _ = (N.comap (comapSubscheme (⊤ : Opn W).i Dv ≫ Dv.si)).comap
          _s0.i := by
          rw [comap_comp]
    _ = (N.comap ((Dv.comap (⊤ : Opn W).i).subschemeι ≫ (⊤ : Opn W).i)).comap
          _s0.i := by
          rw [comapSubscheme_comp]
    _ = (_a3.comap (Dv.comap (⊤ : Opn W).i).subschemeι).comap
          _s0.i := by
          rw [comap_comp]
  intro _ _ Jz hJz
  obtain rfl : Jz = J.comap (comapSubscheme (⊤ : Opn W).i Dv) := by simpa using hJz.symm
  have hpc := PrincipalizationCertificate.comap_of_openImmersionStability hin hJcert
    (comapSubscheme (⊤ : Opn W).i Dv)
  have e2 : comapSubscheme (⊤ : Opn W).i Dv ≫ (siI Dv ≫ p)
      = (Dv.comap (⊤ : Opn W).i).subschemeι ≫ ((⊤ : Opn W).i ≫ p) :=
    by
      rw [← assoc, comapSubscheme_comp, assoc]
  have e3 : ((comapSubscheme (⊤ : Opn W).i Dv) ⁻¹' (preimage Dv.si Mem))
      = ((Dv.comap (⊤ : Opn W).i).subschemeι ≫ (⊤ : Opn W).i) ⁻¹' Mem := by
    ext x
    simp only [mem_preimage]
    rw [← hkey x]
    simp
  have e4 : (Z.comap Dv.si).comap (comapSubscheme (⊤ : Opn W).i Dv)
      = _a4.comap (Dv.comap (⊤ : Opn W).i).subschemeι := by
    rw [← comap_comp, ← comap_comp,
      comapSubscheme_comp]
  rwa [e2, e3, e4] at hpc

theorem principalizationCertificate_congr_mult
    {p : W ⟶ Sp k} {I : ISD W} {m m' : ℕ} {Mem : Set ↥W}
    {Z : ISD W} (hm : m = m') (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p I m' Mem Z := by
  subst hm
  exact h
end

section
variable {X : Sch}
section
variable {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
theorem controlledTransform_eq_ideal_of_eq
    (s : MarkedSequenceOfBlowups p I m E) (I' : ISD X) (m' : ℕ)
    (hI : I' = I) (hm : m' = m) (i : ℕ) (hi : i ≤ s.length) :
    (ofSequenceOfBlowups s.toSequenceOfBlowups).controlledTransform I' m' i = s.ideal i := by
  subst hI
  subst hm
  exact ofMarkedSequence_controlledTransform s i hi

theorem mem_boundarySupport_of_mem_support_of_mem_boundary
    (s : MarkedBlowupSequenceData p I m E) (i : ℕ) (J : IdealSheafData $ s.obj i)
    (hJ : J ∈ s.boundary i) (x : ↥(s.obj i))
    (hx : x ∈ (support J : CSet $ s.obj i)) : x ∈ (s.dataAt i).boundarySupport := by
  refine (MarkedSchemeWithCenter.mem_boundarySupport_iff (s.dataAt i) x).2 ⟨J, ?_, hx⟩
  rwa [dataAt_boundary]
end

private theorem isMaxContactHypersurface_congr
    (p p' : X ⟶ Sp k)
    (hfp : LocallyOfFiniteType p) (hfp' : LocallyOfFiniteType p')
    {A A' H H' : ISD X} {mu_ mu' : ℕ}
    (hp : p = p') (hA : A = A') (hH : H = H') (hmu_ : mu_ = mu')
    (hyp : @IsMaxContactHypersurface k _ X p hfp A mu_ H) :
    @IsMaxContactHypersurface k _ X p' hfp' A' mu' H' :=by simp_all
end

theorem balancedTunedSheaf_eq_of_mult_eq_one [IsNoetherianRing k] {X : Sch}
    (p : X ⟶ Sp k) (hfp : LocallyOfFiniteType p)
    (I : ISD X) (m : ℕ) (hm : m = 1) :
    @balancedTunedSheaf k _ _ X p hfp I m = I := by
  subst hm
  exact balancedTunedSheaf_one k p I
end

section
variable {al_ : Type _} (l : List al_) (a) (L : List al_) (hl : l = a :: L)
include hl
theorem get_zero_of_eq_cons (h0 : 0 < length l) : l.lget 0 h0 = a := by
  subst hl
  rfl

theorem get_mem_of_eq_cons_of_ne_zero (idx : Fin l.length) (hidx : (idx : ℕ) ≠ 0) : get l idx ∈ L := by
  subst hl
  obtain ⟨n, hn⟩ := idx
  cases n with
  | zero => exact absurd rfl hidx
  | succ m =>
      have hm : m < lenL L := by simpa using hn
      show L.lget m hm ∈ L
      simp
end

theorem support_ideal_subset_iteratedStrictTransform (hstar : MaxContactCoverProperties) (S : MarkedIdealWithBoundary)
    (hv : S.IsAdmissible) [LocallyOfFiniteType S.structMap]
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ENat)) (hm1 : S.mult = 1)
    (H : tISD S)
    (hH : IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (u : S.mbs) (t : ℕ) (ht : t ≤ u.length)
    (hfti : LocallyOfFiniteType $ u.proj t ≫ S.structMap)
    (hsmt : Smooth $ u.proj t ≫ S.structMap)
    (hczs : CharZero S.base) :
    ((u.ideal t).support : CSet $ u.obj t)
      ⊆ ((u.toBlowupSequenceData.iteratedStrictTransform t H).support : CSet $ u.obj t) := by
  have hsub := (isMaxContactHypersurface_iteratedStrictTransform hstar S hv hord H hH u t ht).orderAtLeastLocus_subset_support $ le_of_eq hm1.symm
  rw [iteratedStrictTransform_eq_toBlowupSequenceData u H t] at hsub
  intro x hx
  apply hsub
  rw [mem_orderAtLeastLocus_iff]
  have hcoe : ((tMu S : ℕ) : ENat) = 1 := by simp [hm1]
  rw [hcoe]
  exact (one_le_orderAt_iff_mem_support (u.ideal t) x).2 hx

namespace BoundarySeparationByMaxContact

section
variable (hstar : MaxContactCoverProperties) (hopen : ∀ (k : Type) [Field k], OpenImmersionStability k) (hinv : ComapIsoInvariance) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T) (hmult : mult T = 1)
include hstar hopen hmono hspec hmult
theorem continuationOrderCertificate_of_mult_eq_one :
    ContinuationOrderCertificate hinv A P T h := by
  intro hft hmk i hi
  have hftI := hft
  have hSV := isAdmissible_coverTriple hstar P T h
  have hSO :=
    orderAt_coverTriple_ideal_le_mult hstar P T h
  have hS1 : (p7 h.valid).mult = 1 := by
    simp [coverTriple_mult, tunedMult, hmult, tuningExponent_one]
  have honeLe := le_of_eq hS1.symm
  have hcz := hSV.charZero
  have hsm0 :=
    smooth_projectionToBase_comp hstar (p7 h.valid) hSV
      (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length le_rfl
  have hAdmCover := isMaxContactHypersurface_coverMaxContactIdeal hstar P T h
  let _a7 := p31 h.valid
  have hAdmT := isMaxContactHypersurface_iteratedStrictTransform hstar
    (p7 h.valid) hSV hSO _a7
    hAdmCover (separateAllBoundary T h.valid hinv A) (separateAllBoundary T h.valid hinv A).length le_rfl
  let _a3 := (p7 h.valid).structMap
  have hAdm0 :=
    isMaxContactHypersurface_congr
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        _a3)
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        _a3)
      hftI hftI rfl rfl (sy_ $ strictTransformAtLength_eq _ _) rfl hAdmT
  obtain ⟨_, hV2, hP2, _, _, _⟩ := exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have hV' := hV2
  have hftT : LocallyOfFiniteType (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap := by
    rw [derivedTriple_structureMorphism]
    exact hft
  have hOB :=
    isOrderBoundedByMult_derivedTriple hstar (p7 h.valid) hSV honeLe hSO
      (separateAllBoundary T h.valid hinv A) hft
      [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        _a7]
      (p7 h.valid).boundary.length hV'
  have hbalanced :=
    isBalanced_derivedTriple hstar (p7 h.valid) hSV honeLe hSO
      (separateAllBoundary T h.valid hinv A) hft
      [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        _a7]
      (p7 h.valid).boundary.length hV'
  have hbd : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary
      = strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          _a7
        :: List.drop (bLen $ p7 h.valid)
            ((separateAllBoundary T h.valid hinv A).boundary
              (separateAllBoundary T h.valid hinv A).length) :=
    derivedTriple_boundary _ _ _ _ _
  have hjlen : 0 < (reduceAlongHypersurfaceTriple T h.valid hinv A hft).boundary.length := by simp_all
  obtain ⟨D, b, hDsm, hD0, hcenter, hbtrue, hDsucc, _hDfin, hJsh⟩ :=
    (hspec 0).shape (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV' hP2 hOB hbalanced hjlen
  have hmu : tuningExponent (p7 h.valid).mult
      = (reduceAlongHypersurfaceTriple T h.valid hinv A hft).mult :=
    (derivedTriple_mult _ _ _ _ _).symm
  have hpeq : ((separateAllBoundary T h.valid hinv A).proj
      (separateAllBoundary T h.valid hinv A).length ≫
      _a3)
      = (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap :=
    (derivedTriple_structureMorphism _ _ _ _ _).symm
  have htm : tuningExponent (p7 h.valid).mult = 1 := by
    rw [hS1]
    exact tuningExponent_one
  have hMultOne := st_ hmu htm
  have hIdeal : (reduceAlongHypersurfaceTriple T h.valid hinv A hft).ideal
      = tunedIdealAtLength (p7 h.valid)
        (separateAllBoundary T h.valid hinv A) hft :=
    ideal_derivedTriple _ _ hft _ _
  have hIdeal2 :=
    tunedIdealAtLength_eq_balancedTunedSheaf _ _ hft
  have hIdealEq :=
    (tr_ hIdeal hIdeal2).trans
      (balancedTunedSheaf_eq_of_mult_eq_one
        ((separateAllBoundary T h.valid hinv A).proj
          (separateAllBoundary T h.valid hinv A).length ≫
          _a3)
        hftI
        ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
        (p7 h.valid).mult hS1)
  have hOrderLe :=
    (isOrderBoundedByMult_iff _).1 hOB
  have hord :=
    orderAt_ideal_length_le hstar (p7 h.valid) hSV hSO
      (separateAllBoundary T h.valid hinv A)
  have key := isMaxContactHypersurface_balancedTunedSheaf hstar (p7 h.valid).base
    ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
      _a3)
    ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
    (p7 h.valid).mult honeLe hord
    (strictTransformAtLength (separateAllBoundary T h.valid hinv A)
      _a7) hAdm0
  have hMaxContactHyp :=
    isMaxContactHypersurface_congr
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        _a3)
      (reduceAlongHypersurfaceTriple T h.valid hinv A hft).structMap hftI hftT hpeq
      (tr_ hIdeal hIdeal2).symm rfl hmu key
  let _a0 := A 0 $ reduceAlongHypersurfaceTriple T h.valid hinv A hft
  have hNoe := fun t ht =>
    isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar (p7 h.valid) hSV
      (separateAllBoundary T h.valid hinv A) hft
      [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        _a7]
      (p7 h.valid).boundary.length hV'
      _a0 t ht
  have hb0 :=
    get_zero_of_eq_cons _ _ _ hbd hjlen
  have hi' : i ≤ (ofMarkedSequence
      _a0).length := by
    rw [ofMarkedSequence_length]
    exact le_of_lt hi
  have hK0 :=
    hD0.trans $ congrArg (fun J => J.comap
      _a0.isoZero.hom) hb0
  have hKstep : ∀ t < _a0.length,
      D (t + 1) = p6 (_a0.transitionMapSucc t)
          (_a0.center t) (D t)
        ∨ D (t + 1) = (D t).comap
          (_a0.transitionMapSucc t) := by
    intro t htlen
    by_cases hbc : b = true ∧ t = 0
    obtain ⟨hbt, ht0⟩ := hbc
    subst ht0
    exact inr (hbtrue hbt).2.2
    exact inl $ hDsucc t htlen hbc
  have hNsub : ((_a0.ideal i).support :
        CSet $ _a0.schemeAt i)
      ⊆ (D i).support := by
    intro x hx
    have h1 := support_ideal_subset_iteratedStrictTransform hstar (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV'
      hOrderLe hMultOne
      (strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        _a7) hMaxContactHyp
      (ofMarkedSequence _a0) i hi'
      (locallyOfFiniteType_projectionToBase_comp hstar (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV'
        (ofMarkedSequence _a0) i hi')
      (smooth_projectionToBase_comp hstar (reduceAlongHypersurfaceTriple T h.valid hinv A hft) hV'
        (ofMarkedSequence _a0) i hi')
      hV'.charZero hx
    exact support_iteratedStrictTransform_subset_support
      _a0.toBsd
      hNoe
      (strictTransformAtLength (separateAllBoundary T h.valid hinv A)
        _a7) D hK0 hKstep i hi' h1
  have hctrl :=
    controlledTransform_eq_ideal_of_eq _a0
      ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
      (p7 h.valid).mult hIdealEq.symm (tr_ hS1 hMultOne.symm) i $ le_of_lt hi
  have hidR :=
    (toBlowupSequenceData_controlledTransform_eq
      (continuationMarkedData (p7 h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          _a7]
        (bLen $ p7 h.valid)
        _a0 hmk) i $ le_of_lt hi).symm.trans hctrl
  have hid :=
    (dataAt_ideal
      (continuationMarkedData (p7 h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          _a7]
        (bLen $ p7 h.valid)
        _a0 hmk) i).trans hidR
  have hceR :=
    ofSequenceOfBlowups_center _a0.toSequenceOfBlowups i
  have hce :=
    (dataAt_center
      (continuationMarkedData (p7 h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          _a7]
        (bLen $ p7 h.valid)
        _a0 hmk) i).trans hceR
  have hprojR :=
    ofSequenceOfBlowups_projectionToBase _a0.toSequenceOfBlowups i
  have hstm :=
    ((dataAt_structMap
      (continuationMarkedData (p7 h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          _a7]
        (bLen $ p7 h.valid)
        _a0 hmk) i).trans
      (congrArg (fun f => f ≫ ((separateAllBoundary T h.valid hinv A).proj
        (separateAllBoundary T h.valid hinv A).length ≫
        _a3)) hprojR)).trans
      (tr_ (congrArg (fun g => _a0.projectionToBase i ≫ g)
            hpeq)
        (MarkedSequenceOfBlowups.projectionToSpec_eq _a0 i).symm)
  have hAb :=
    (ofMarkedSequence_boundary _a0 i
      (le_of_lt hi)).symm
  have hAb2 :=
    congrArg (fun E => (ofSequenceOfBlowups
      _a0.toSequenceOfBlowups).boundaryFrom E i) hbd
  have hAfull :=
    (tr_ hAb hAb2).trans $ tr_ (boundary_cons _ _ _ i) $ congrArg (fun l =>
      (ofSequenceOfBlowups _a0.toSequenceOfBlowups).iteratedStrictTransform i
        (strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          _a7) :: l) $ boundary_eq_map_iteratedStrictTransform_append _ _ i
  have hRb :=
    (toBlowupSequenceData_boundary_eq_boundary_of_le
      (continuationMarkedData (p7 h.valid)
        (separateAllBoundary T h.valid hinv A) hft
        [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
          _a7]
        (bLen $ p7 h.valid)
        _a0 hmk) i $ le_of_lt hi).symm.trans
      (boundary_eq_map_iteratedStrictTransform_append
        (ofSequenceOfBlowups _a0.toSequenceOfBlowups)
        ((separateAllBoundary T h.valid hinv A).boundary
          (separateAllBoundary T h.valid hinv A).length) i)
  have hOther : MarkedSequenceOfBlowups.otherBoundaryLocus
      _a0 0 i
      ⊆ ((continuationMarkedData (p7 h.valid)
          (separateAllBoundary T h.valid hinv A) hft
          [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
            _a7]
          (bLen $ p7 h.valid)
          _a0 hmk).dataAt i).boundarySupport := by
    intro x hx
    obtain ⟨idx, hidx, hxs⟩ :=
      (MarkedSequenceOfBlowups.mem_otherBoundaryLocus_iff
        _a0 0 i x).1 hx
    have hmem := get_mem_of_eq_cons_of_ne_zero _ _ _ hAfull idx hidx
    have hmem2 : (_a0.boundary i).get idx
        ∈ (continuationMarkedData (p7 h.valid)
            (separateAllBoundary T h.valid hinv A) hft
            [strictTransformAtLength (separateAllBoundary T h.valid hinv A)
              _a7]
            (bLen $ p7 h.valid)
            _a0 hmk).boundary i := by
      rw [hRb]
      rcases mem_append.1 hmem with h1 | h2
      obtain ⟨y, hy, hfy⟩ := List.mem_map.1 h1
      exact mem_append.2 $ inl $ List.mem_map.2 ⟨y, mem_of_mem_drop hy, hfy⟩
      exact mem_append.2 $ inr h2
    exact mem_boundarySupport_of_mem_support_of_mem_boundary _ i _ hmem2 x hxs
  refine orderCertificate_congr_morphism_ideal_center hstm.symm hid.symm hce.symm ?_
  refine orderCertificate_one_of_isSmoothDivisor (hopen (reduceAlongHypersurfaceTriple T h.valid hinv A hft).base) _ _ _ _ (D i)
    (hDsm i $ le_of_lt hi) hNsub (hcenter i hi) ?_
  by_cases hbc : b = true ∧ i = 0
  left
  obtain ⟨hbt, hi0⟩ := hbc
  subst hi0
  exact (hbtrue hbt).2.1
  right
  obtain ⟨J, hJnz, hJl, hJc⟩ := hJsh i hi hbc
  refine ⟨J, hJnz, ?_, principalizationCertificate_mono_of_subset (preimage_mono hOther) $ principalizationCertificate_congr_mult hMultOne hJc⟩
  intro x hxm
  exact hJl x fun hc => hxm $ hOther hc

theorem orderCertificate_coverMarkedBlowupData_of_mult_eq_one (t : ℕ)
    (ht : t <
      (coverMarkedBlowupData T h.valid hinv $ lowerDimensionalFamily A T).length) :
    OrderCertificate
      ((coverMarkedBlowupData T h.valid hinv
        (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.schemeAt t)
      ((coverMarkedBlowupData T h.valid hinv
          (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
        structMap (cT h.valid))
      ((coverMarkedBlowupData T h.valid hinv
        (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.ideal t) 1
      ((coverMarkedBlowupData T h.valid hinv
        (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.boundaryLocus t)
      ((coverMarkedBlowupData T h.valid hinv
        (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.center t) :=
  by
    have main : ∀ j, j ≤ bLen (p7 h.valid) →
        ∀ i < (separateBoundary hinv T (p49 A T)
            (p7 h.valid) j).length,
          HasOrderCertificateMultOne $ (separateBoundary hinv T (p49 A T)
            (p7 h.valid) j).dataAt i := by
      intro j
      induction j with
      | zero =>
          intro _ i hi
          rw [separateBoundary_zero] at hi
          exact absurd hi $ not_lt_zero i
      | succ n ih =>
          intro hn
          have hnlt := hn
          rw [separateBoundary_succ]
          exact hasOrderCertificateMultOne_appendLowerDimReduction hstar hinv P hmono A B n (hspec n) T
            (p7 h.valid) (isAdmissible_coverTriple hstar P T h) (hstar.coverTriple_dim_le T h.valid) h.dim_prop (orderAt_coverTriple_ideal_le_mult hstar P T h) _ hnlt
            (ih $ le_of_lt hnlt)
    obtain ⟨hft, -, -, hmk, heq, -⟩ := exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
    have key : ∀ i < (coverMarkedBlowupData T h.valid hinv
        (p49 A T)).length,
        HasOrderCertificateMultOne $ (coverMarkedBlowupData T h.valid hinv
          (p49 A T)).dataAt i := by
      rw [heq]
      intro i hi
      exact append_dataAt_of_forall _ _ hinv HasOrderCertificateMultOne
        (isInvariantUnderIso_hasOrderCertificateMultOne (p7 h.valid).base)
        (main _ le_rfl) ((continuationOrderCertificate_of_mult_eq_one hstar hopen hinv P hmono A B hspec T h hmult) hft hmk) i hi
    have hk := key t ht
    unfold HasOrderCertificateMultOne at hk
    rw [boundarySupport_dataAt] at hk
    rwa [MarkedBlowupSequenceData.toMarkedSequence_projectionToBase]
end

end BoundarySeparationByMaxContact





theorem isPullback_of_length_eq_zero_of_length_eq_zero {X' X} ph_
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsPullbackBlowupSequence ph_ t s := by
  refine isPullback_of_length_zero_of_comap_center_eq_top ph_ t s ht ?_
  intro i hi _ _
  exact absurd hi $ by omega

namespace MaxContactFunctoriality

section
variable {X : Sch}
def removeUnitIdeals (L : Bdy X) : Bdy X :=
  L.filter fun D => @decide (D ≠ ⊤) $ propDecidable _

theorem removeUnitIdeals_cons_top
    (L : Bdy X) :
    removeUnitIdeals ((⊤ : ISD X) :: L) = removeUnitIdeals L := by
  simp [removeUnitIdeals]

theorem removeUnitIdeals_cons_of_ne_top {D : ISD X}
    (hD : D ≠ ⊤) (L : Bdy X) :
    removeUnitIdeals (D :: L) = D :: removeUnitIdeals L := by
  simp [removeUnitIdeals, hD]
end

theorem removeUnitIdeals_map_comap_removeUnitIdeals {X Y : Sch} (f : Y ⟶ X) (L : Bdy X) :
    removeUnitIdeals (map (fun D => comap D f) $ removeUnitIdeals L) =
      removeUnitIdeals (map (fun D => comap D f) L) := by
  induction L with
  | nil => rfl
  | cons D L ih =>
    by_cases hD : D = ⊤
    subst hD
    rw [removeUnitIdeals_cons_top, ih]
    simp [comap_top]
    rw [removeUnitIdeals_cons_top]
    rw [removeUnitIdeals_cons_of_ne_top hD]
    simp
    by_cases hD' : comap D f = ⊤
    rw [hD', removeUnitIdeals_cons_top, removeUnitIdeals_cons_top, ih]
    rw [removeUnitIdeals_cons_of_ne_top hD', removeUnitIdeals_cons_of_ne_top hD', ih]

noncomputable abbrev smoothPullbackTriple (S : MarkedIdealWithBoundary) {X' : Sch} (q : X' ⟶ scheme S) :
    MarkedIdealWithBoundary :=
  withBoundary (S.pbA (q ≫ structMap S) q)
    (removeUnitIdeals (S.pbA (q ≫ structMap S) q).boundary)

section
variable (hinv : ComapIsoInvariance) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment)
def LoopCompatibleWithSmoothPullback : Prop :=
  ∀ (_hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties) (_hin : OrderReduction.OrderReductionHypotheses)
    (_hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned)
    (_hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback),
    (∀ a b : ℕ, a ≤ b → P b → P a) →
    ∀ B : PrincipalizationAssignment, (∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) →
      IsBoundaryPositionInvariant P A →
      ∀ T T' : MarkedIdealWithBoundary, P T.krullDimSucc → P T'.krullDimSucc →
        ∀ S : MarkedIdealWithBoundary, IsAdmissible S →
          (∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat)) →
          S.krullDimSucc ≤ T.krullDimSucc →
          ∀ H : tISD S,
            (∀ [_inst : LocallyOfFiniteType S.structMap],
                IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H) →
            InStrictNormalCrossingPosition S.structMap [H] →
            (∀ D ∈ S.boundary, D ≠ ⊤) →
            ∀ {X' : Sch} (q : X' ⟶ scheme S) [Smooth q],
              IsAdmissible (smoothPullbackTriple S q) →
              (smoothPullbackTriple S q).krullDimSucc ≤ T'.krullDimSucc →
              (∀ [_inst : LocallyOfFiniteType (smoothPullbackTriple S q).structMap],
                  IsMaxContactHypersurface (smoothPullbackTriple S q).base
                    (smoothPullbackTriple S q).structMap (smoothPullbackTriple S q).ideal
                    (smoothPullbackTriple S q).mult $ comap H q) →
              InStrictNormalCrossingPosition (smoothPullbackTriple S q).structMap [comap H q] →
              IsPullbackBlowupSequence q
                (reduceAlongHypersurface hinv T' (lowerDimensionalFamily A T') (smoothPullbackTriple S q)
                  (comap H q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
                (reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups

def TrivialOnEmptyOrderLocus : Prop :=
  ∀ T : MarkedIdealWithBoundary, OrderReductionHypotheses P T →
    ∀ {Y : Sch} (g : Y ⟶ scheme T) [Smooth g] (t : SequenceOfBlowups Y),
      t.length = 0 →
      orderAtLeastLocus (T.ideal.comap g) T.mult = (∅ : Set ↥Y) →
      IsPullbackBlowupSequence g t (maxContactPrincipalization hinv A T).toSequenceOfBlowups
end

noncomputable abbrev dropTrivialBoundaryPullback (T : MarkedIdealWithBoundary) {Y : Sch}
    (qY : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
    (E' : List Y.IdealSheafData) : MarkedIdealWithBoundary :=
  withBoundary ((dropTrivialBoundary T).pullbackAlong Y qY h) $ removeUnitIdeals E'

theorem reduceAlongHypersurface_isomorphic_of_isMaxContactHypersurface
    (hinv : ComapIsoInvariance) P (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    A B
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (_hshift : IsBoundaryPositionInvariant P A)
    (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties) (hin : OrderReduction.OrderReductionHypotheses)
    (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned)
    (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback)
    (T : MarkedIdealWithBoundary) (hP : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary) (hv : IsAdmissible S)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (hdim : S.krullDimSucc ≤ T.krullDimSucc)
    H H'
    (hH : ∀ [_inst : LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    (hH' : ∀ [_inst : LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H')
    (hH'snc : InStrictNormalCrossingPosition S.structMap [H']) :
    (reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      (reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H').toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hft2 := hv.locallyOfFiniteType
  have hpb : pullbackTriple S (𝟙 tSch S) = S := by
    simp [pullbackTriple, pullbackAlong]
  have hVpb : tAd $ pullbackTriple S $ 𝟙 tSch S := by rw [hpb]
                                                      exact hv
  have hdimpb : tDim (pullbackTriple S $ 𝟙 tSch S) ≤ tDim T := by rw [hpb]
                                                                  exact hdim
  have hHup : ∀ [inst : LocallyOfFiniteType
      (pullbackTriple S $ 𝟙 tSch S).structMap],
      IsMaxContactHypersurface (pullbackTriple S $ 𝟙 tSch S).base
        (pullbackTriple S $ 𝟙 tSch S).structMap
        (pullbackTriple S $ 𝟙 tSch S).ideal
        (pullbackTriple S $ 𝟙 tSch S).mult H := by
    intro inst
    exact isMaxContactHypersurface_of_triple_eq hpb inst hft2 H H m129 $ @hH hft2
  have hHupsnc :=
    inStrictNormalCrossingPosition_of_triple_eq hpb [H] [H] m129 hHsnc
  have hA := isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar0 hin hMC hAdm hinv P hmono A B hspec
    T hP S hv hord hdim H hH hHsnc (𝟙 tSch S) hVpb hdimpb H hHup hHupsnc
  have hB := isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar0 hin hMC hAdm hinv P hmono A B hspec
    T hP S hv hord hdim H' hH' hH'snc (𝟙 tSch S) hVpb hdimpb H hHup hHupsnc
  exact hA.isomorphic_of_isomorphic hB $ isomorphic_refl _

theorem map_comap_map_comap {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Bdy Z) :
    map (fun D => comap D f) (map (fun D => comap D g) L)
      = map (fun D => comap D $ f ≫ g) L := by
  rw [List.map_map]
  exact map_congr_left fun D _ => sy_ $ comap_comp D f g

theorem dropTrivialBoundary_boundary_eq_removeUnitIdeals (T : MarkedIdealWithBoundary) :
    (dropTrivialBoundary T).boundary = removeUnitIdeals T.boundary := by
  rw [dropTrivialBoundary_boundary]
  exact List.filter_congr fun D _ => congrArg _ $ m111 _ _

theorem removeUnitIdeals_eq_of_sameNontrivialBoundary {X : Sch} {L L' : Bdy X}
    (hL : SameNontrivialBoundary L L') : removeUnitIdeals L = removeUnitIdeals L' := by
  have hdn : ∀ D : ISD X,
      (@decide (D ≠ ⊤) $ propDecidable _)
        = !(@decide (D = ⊤) $ propDecidable _) :=
    fun D => @decide_not (D = ⊤) (propDecidable _) $ propDecidable _
  have hL' : List.filter (fun D =>
        !(@decide (D = ⊤) $ propDecidable _)) L
      = List.filter (fun D =>
        !(@decide (D = ⊤) $ propDecidable _)) L' := hL
  have h1 : removeUnitIdeals L = List.filter (fun D =>
      !(@decide (D = ⊤) $ propDecidable _)) L :=
    List.filter_congr fun D _ => hdn D
  have h2 : List.filter (fun D =>
      !(@decide (D = ⊤) $ propDecidable _)) L' = removeUnitIdeals L' :=
    List.filter_congr fun D _ => sy_ $ hdn D
  exact tr_ h1 $ tr_ hL' h2

theorem removeUnitIdeals_map_comap_congr {X Y : Sch} (g : X ⟶ Y)
    {L L' : Bdy Y}
    (hL : removeUnitIdeals L = removeUnitIdeals L') :
    removeUnitIdeals (map (fun D => comap D g) L)
      = removeUnitIdeals (map (fun D => D.comap g) L') := by
  rw [← removeUnitIdeals_map_comap_removeUnitIdeals g L, ← removeUnitIdeals_map_comap_removeUnitIdeals g L', hL]

private theorem markedIdealWithBoundary_mk_congr {k : Type} [fk : Field k] {Z : Sch}
    {p1_ p2_ : Z ⟶ Sp k} {I1 I2 : ISD Z} {m1 m2 : ℕ}
    {b1_ b2_ : Bdy Z}
    (hp : p1_ = p2_) (hI : I1 = I2) (hm : m1 = m2) (hb : b1_ = b2_) :
    ({ base := k, instField := fk, scheme := Z, structMap := p1_, ideal := I1, mult := m1,
        boundary := b1_ } : MarkedIdealWithBoundary) =
      { base := k, instField := fk, scheme := Z, structMap := p2_, ideal := I2, mult := m2,
        boundary := b2_ } :=by simp_all
theorem smoothPullbackTriple_coverTriple_eq (T : MarkedIdealWithBoundary) {Y : Sch}
    (qY : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
    [Smooth h]
    (hq : h ≫ structMap T = qY)
    (E' : Bdy Y)
    (hE : SameNontrivialBoundary (T.pbA qY h).boundary E')
    (htrimv : IsAdmissible $ dropTrivialBoundary T)
    (hpbv : IsAdmissible $ dropTrivialBoundaryPullback T qY h E')
    [Surjective $ coverMap (dropTrivialBoundaryPullback T qY h E') hpbv]
    [Surjective
      (Limits.pullback.fst (coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
        (coverMap (dropTrivialBoundary T) htrimv))] :
    smoothPullbackTriple (coverTriple (dropTrivialBoundaryPullback T qY h E') hpbv)
        (Limits.pullback.fst
          (coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (coverMap (dropTrivialBoundary T) htrimv)) =
      smoothPullbackTriple (coverTriple (dropTrivialBoundary T) htrimv)
        (Limits.pullback.snd
          (coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (coverMap (dropTrivialBoundary T) htrimv)) := by
  subst hq
  let _a8 := h ≫ tMp T
  let _a4 := dropTrivialBoundaryPullback T _a8 h E'
  let _a0 := p12 _a4 hpbv
  let _a1 := p12 (dropTrivialBoundary T) htrimv
  let _a3 := _a0 ≫ h
  let _a5 := m47 _a3 _a1 ≫ _a1
  let _a7 := m57 _a3 _a1
  have hcond :
      _a7 ≫
        _a3
      = _a5 := Limits.pullback.condition
  have hcond2 :=
    (assoc _ _ _).trans hcond
  let _a2 := p29 (dropTrivialBoundary T) htrimv
  have hti : p29 _a4 hpbv
      = cmI _a2 h := by
    have : Smooth T.structMap := htrimv.smooth
    have : LocallyOfFiniteType T.structMap := htrimv.locallyOfFiniteType
    have : LocallyOfFiniteType _a8 := hpbv.locallyOfFiniteType
    exact balancedTunedSheaf_comap T.base T.structMap h T.ideal T.mult
  have i1 := congrArg (fun J => cmI (cmI J
      _a0)
      _a7) hti
  have i3 := congrArg
      _a2.comap hcond
  have hb :=
    let _a6 := m57 _a3 _a1 ≫ _a0
    calc removeUnitIdeals (map (fun D => cmI D
          _a7)
        (map (fun D => cmI D
          _a0)
          (removeUnitIdeals E')))
        = removeUnitIdeals (map (fun D => cmI D
            _a6)
            (removeUnitIdeals E')) := congrArg removeUnitIdeals $ map_comap_map_comap _ _ _
      _ = removeUnitIdeals (map (fun D => cmI D
            _a6)
            E') := removeUnitIdeals_map_comap_removeUnitIdeals _ _
      _ = removeUnitIdeals (map (fun D => cmI D
            _a6)
            (map (·.comap h) T.boundary)) := removeUnitIdeals_map_comap_congr _ $ (removeUnitIdeals_eq_of_sameNontrivialBoundary hE).symm
      _ = removeUnitIdeals (map (fun D => cmI D
            (_a6 ≫ h))
            T.boundary) := congrArg removeUnitIdeals $ map_comap_map_comap _ h _
      _ = removeUnitIdeals (map (fun D => cmI D
            _a5)
            T.boundary) :=
          congrArg (fun ph_ => removeUnitIdeals (map (·.comap ph_) T.boundary)) hcond2
      _ = removeUnitIdeals (map (fun D => cmI D
            _a5)
            (removeUnitIdeals T.boundary)) := sy_ $ removeUnitIdeals_map_comap_removeUnitIdeals _ _
      _ = removeUnitIdeals (map (fun D => cmI D
            _a5)
            (dropTrivialBoundary T).boundary) :=
          congrArg (fun L => removeUnitIdeals $ map (fun D => cmI D
            _a5) L)
            (dropTrivialBoundary_boundary_eq_removeUnitIdeals T).symm
      _ = removeUnitIdeals (map (fun D => cmI D
            (m47
              _a3
              _a1))
          (map (fun D => cmI D
            _a1)
            (dropTrivialBoundary T).boundary)) :=
          congrArg removeUnitIdeals (map_comap_map_comap _ _ _).symm
  exact markedIdealWithBoundary_mk_congr ((st_ $ assoc _ _ _) $ st_ (assoc _ _ _) $ tr_ (congrArg (fun ph_ => ph_ ≫ tMp T) hcond2) $ assoc _ _ _) (i1.trans (tr_ ((congrArg (cmI · _a7) (comap_comp _a2 _a0 h).symm).trans (comap_comp _a2 _ _).symm) $ tr_ i3 $ comap_comp _a2 _ _)) rfl hb

theorem filter_eq_removeUnitIdeals {X : Sch}
    (p : ISD X → Bool) (hp : ∀ D : ISD X, p D = true ↔ D ≠ ⊤)
    (L : Bdy X) : L.filter p = removeUnitIdeals L := by
  induction L with
  | nil => rfl
  | cons D L ih =>
    by_cases hD : D = ⊤
    subst hD
    have hpf : p (⊤ : ISD X) = false := by
      cases hb : p (⊤ : ISD X) with
      | false => rfl
      | true => exact absurd ((hp ⊤).1 hb) fun hne => hne rfl
    rw [removeUnitIdeals_cons_top]
    simp [hpf, ih]
    have hpt := (hp D).2 hD
    rw [removeUnitIdeals_cons_of_ne_top hD]
    simp [hpt, ih]

theorem dropTrivialBoundary_eq_withBoundary_removeUnitIdeals (S : MarkedIdealWithBoundary) :
    dropTrivialBoundary S = withBoundary S (removeUnitIdeals S.boundary) := by
  rw [MaxContactReduction.dropTrivialBoundary_def]
  exact congrArg S.withBoundary
    (filter_eq_removeUnitIdeals _ (fun D => by simp) S.boundary)

theorem ne_top_of_mem_removeUnitIdeals {X : Sch} (L : Bdy X) :
    ∀ D ∈ removeUnitIdeals L, D ≠ ⊤ := by
  induction L with
  | nil =>
    intro D hD
    simp [removeUnitIdeals] at hD
  | cons C L ih =>
    intro D hD
    by_cases hC : C = ⊤
    subst hC
    rw [removeUnitIdeals_cons_top] at hD
    exact ih D hD
    rw [removeUnitIdeals_cons_of_ne_top hC] at hD
    rcases List.mem_cons.1 hD with h1 | h1
    subst h1
    exact hC
    exact ih D h1

theorem isStrictPullback_coverMarkedSequence_of_eq_of_heq (hinv : ComapIsoInvariance)
    A {S1_ S2_ : MarkedIdealWithBoundary} (hS : S1_ = S2_)
    (hv1_ : IsAdmissible S1_) (hv2_ : IsAdmissible S2_) (e1_ : BlowupSequenceData S1_.scheme) (e2_ : BlowupSequenceData S2_.scheme)
    (hee : HEq e1_ e2_)
    (hd : IsStrictPullbackBlowupSeq (coverMap S1_ hv1_)
        (coverMarkedBlowupData S1_ hv1_ hinv $ lowerDimensionalFamily A S1_).toSequenceOfBlowups e1_.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq (coverMap S2_ hv2_)
        (coverMarkedBlowupData S2_ hv2_ hinv $ lowerDimensionalFamily A S2_).toSequenceOfBlowups e2_.toSequenceOfBlowups := by
  subst hS
  cases hee
  exact hd

theorem orderReductionHypotheses_of_eq {P} {S1_ S2_}
    (hS : S1_ = S2_) (hy : OrderReductionHypotheses P S1_) : OrderReductionHypotheses P S2_ := by
  subst hS
  exact hy

section
variable {X Y : Sch} (h : Y ⟶ X)
theorem isPullback_of_faithfullyFlat_covers
    [Flat h] {C1_ C2_} c1_ c2_
    (hf1_ : Flat c1_) (hs1_ : Surjective c1_)
    (hf2_ : Flat c2_) (hs2_ : Surjective c2_)
    (t1_ : SequenceOfBlowups C1_) (t2_ : SequenceOfBlowups C2_) (s1_ : SequenceOfBlowups X) s2_
    (hd1_ : IsStrictPullbackBlowupSeq c1_ t1_ s1_) (hd2_ : IsStrictPullbackBlowupSeq c2_ t2_ s2_)
    (hne2_ : ∀ i, i < t2_.length → center t2_ i ≠ ⊤)
    (hcomp : ∀ v v' : SequenceOfBlowups $ Limits.pullback (c2_ ≫ h) c1_,
      IsStrictPullbackBlowupSeq (Limits.pullback.fst (c2_ ≫ h) c1_) v t2_ →
      IsStrictPullbackBlowupSeq (Limits.pullback.snd (c2_ ≫ h) c1_) v' t1_ →
      v.withoutIsoBlowups.Isomorphic v'.withoutIsoBlowups) :
    IsPullbackBlowupSequence h s2_ s1_ := by
  let _a2 := c2_ ≫ h
  let _c0 := m57 _a2 c1_
  refine (IsStrictPullbackBlowupSeq.isPullbackSequenceOfBlowups_withoutIsoBlowups $ isStrictPullbackSequenceOfBlowups_baseChange s1_ h).of_isomorphic ?_
  have hu :=
    isStrictPullbackSequenceOfBlowups_baseChange s1_ _a2
  let _a1 := s1_.baseChange _a2
  have hv : IsStrictPullbackBlowupSeq _c0
      (_a1.baseChange _c0)
      _a1 := isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hv2 : IsStrictPullbackBlowupSeq _c0
      (t2_.baseChange _c0) t2_ :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  let _a0 := m47 _a2 c1_
  have hv1 : IsStrictPullbackBlowupSeq _a0
      (t1_.baseChange _a0) t1_ :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  exact (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hu.baseChange_of_comp.withoutIsoBlowups hd2_.withoutIsoBlowups $ IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hv.withoutIsoBlowups hv2.withoutIsoBlowups $ ((((hv.comp hu).congr_hom Limits.pullback.condition).isomorphic $ hv1.comp hd1_).withoutIsoBlowups).trans (hcomp _ _ hv2 hv1).symm).trans $ SequenceOfBlowups.withoutIsoBlowups_isomorphic_self s2_
    (fun i hi => hd2_.center_ne_top_of_forall_center_ne_top hne2_ i hi)

theorem smooth_pullback_fst_snd_and_surjective_fst
    [Smooth h]
    {C1_ C2_ : Sch} (c1_ : C1_ ⟶ X) (c2_ : C2_ ⟶ Y)
    [Smooth c1_] [Smooth c2_]
    [Surjective c1_] :
    Smooth (Limits.pullback.fst (c2_ ≫ h) c1_) ∧
      Smooth (Limits.pullback.snd (c2_ ≫ h) c1_) ∧
        Surjective (Limits.pullback.fst (c2_ ≫ h) c1_) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end

theorem smoothPullbackTriple_eq_dropTrivialBoundary (S : MarkedIdealWithBoundary) {X' : Sch}
    (q : X' ⟶ scheme S) :
    smoothPullbackTriple S q = dropTrivialBoundary (S.pbA (q ≫ structMap S) q) :=
  (dropTrivialBoundary_eq_withBoundary_removeUnitIdeals $ pbAT S (q ≫ tMp S) q).symm

theorem boundary_ne_top_of_eq {S1_ S2_ : MarkedIdealWithBoundary} (hS : S1_ = S2_)
    (hb : ∀ D ∈ S1_.boundary, D ≠ ⊤) : ∀ D ∈ S2_.boundary, D ≠ ⊤ := by
  subst hS
  exact hb

theorem coverTriple_boundary_ne_top (S : MarkedIdealWithBoundary) (hv : IsAdmissible S)
    [Surjective $ coverMap S hv]
    (hb : ∀ D ∈ S.boundary, D ≠ ⊤) :
    ∀ D ∈ (cT hv).boundary, D ≠ ⊤ := by
  refine boundary_ne_top_of_eq (MaxContactOpenCover.coverTriple_eq_tunedTriple_pullbackAlong S hv).symm ?_
  intro D hD
  obtain ⟨D0_, hD0_, rfl⟩ := List.mem_map.1 hD
  exact (comap_ne_top_iff_of_surjective (p12 S hv) D0_).2 $ hb D0_ hD0_

theorem orderAt_coverTriple_le_mult (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties)
    (horder : CoSupportTunedSheafEqAndOrderLE) (S : MarkedIdealWithBoundary) (hv : IsAdmissible S)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (hmax : MaxOrderEq S.ideal S.mult) :
    ∀ x : ↥(cT hv).scheme,
      orderAt (cT hv).ideal x
        ≤ (mult (cT hv) : ENat) := by
  have hsm := hv.smooth
  have hft := hv.locallyOfFiniteType
  have hcz := hv.charZero
  have hnoe : IsNoetherianRing S.base := inferInstance
  intro x
  let _a0 := p29 S hv
  let _a1 := p12 S hv
  show orderAt (cmI _a0 _a1) x
      ≤ ((tunedMult S : ℕ) : ENat)
  rw [orderAt_comap S.base S.structMap _a1
    _a0 x]
  exact (horder.orderLE S.base S.scheme S.structMap S.ideal S.mult hv.one_le_mult hmax (tunedMult S) $ (hstar0.coverTriple_valid S hv hord $ isMaxContactCover_chosenCoverData S hv $ hstar0.exists_goodCover S hv hord).one_le_mult) _

section
variable (hinv : ComapIsoInvariance) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (hshift : IsBoundaryPositionInvariant P A) (hstar0 : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties) (hin : OrderReduction.OrderReductionHypotheses) (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned) (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback) (hdel : LoopCompatibleWithSmoothPullback hinv P A)
include hmono hspec hshift hstar0 hin hMC hAdm hdel
theorem withoutIsoBlowups_isomorphic_of_smoothPullbackTriple_eq (htv : DropTrivialBoundaryAdmissible)
    (S1_ S2_ : MarkedIdealWithBoundary) (hv1_ : IsAdmissible S1_) (hv2_ : IsAdmissible S2_)
    (hP1 : P S1_.krullDimSucc) (hP2_ : P S2_.krullDimSucc)
    (hord1_ : ∀ x : ↥S1_.scheme, orderAt S1_.ideal x ≤ (mult S1_ : ENat))
    (hord2_ : ∀ x : ↥S2_.scheme, orderAt S2_.ideal x ≤ (mult S2_ : ENat))
    (_hcsn₁ : (orderAtLeastLocus S1_.ideal S1_.mult).Nonempty)
    (_hcsn₂ : (orderAtLeastLocus S2_.ideal S2_.mult).Nonempty)
    (hbd1_ : ∀ D ∈ S1_.boundary, D ≠ ⊤) (hbd2_ : ∀ D ∈ S2_.boundary, D ≠ ⊤)
    (hsuc1 : Surjective $ coverMap S1_ hv1_)
    (hsuc2 : Surjective $ coverMap S2_ hv2_)
    (hcord1 : ∀ x : ↥(cT hv1_).scheme,
      orderAt (cT hv1_).ideal x
        ≤ (mult (cT hv1_) : ENat))
    (hcord2 : ∀ x : ↥(cT hv2_).scheme,
      orderAt (cT hv2_).ideal x
        ≤ (mult (cT hv2_) : ENat))
    {Q}
    pi1
    pi2
    (hsmpi1 : Smooth pi1) (hsmpi2 : Smooth pi2)
    (hdeleq : smoothPullbackTriple (cT hv2_) pi2
      = smoothPullbackTriple (cT hv1_) pi1)
    (hqc : QuasiCompact
      (pi1 ≫ structMap (cT hv1_)))
    (hdim : (smoothPullbackTriple (cT hv1_) pi1).krullDimSucc ≤ S2_.krullDimSucc)
    (v v' : SequenceOfBlowups Q)
    (hvv : IsStrictPullbackBlowupSeq pi2 v
      (coverMarkedBlowupData S2_ hv2_ hinv $ lowerDimensionalFamily A S2_).toSequenceOfBlowups)
    (hvv' : IsStrictPullbackBlowupSeq pi1 v'
      (coverMarkedBlowupData S1_ hv1_ hinv $ lowerDimensionalFamily A S1_).toSequenceOfBlowups) :
    v.withoutIsoBlowups.Isomorphic v'.withoutIsoBlowups := by
  let _c0 := p7 hv1_
  let _c1 := p7 hv2_
  let _c2 := cmI (p31 hv2_) pi2
  let _c3 := p31 hv2_
  let _c4 := p31 hv1_
  have hgood1 := isMaxContactCover_chosenCoverData S1_ hv1_ $ hstar0.exists_goodCover S1_ hv1_ hord1_
  have hgood2 := isMaxContactCover_chosenCoverData S2_ hv2_ $ hstar0.exists_goodCover S2_ hv2_ hord2_
  have hcv1 : tAd _c0 :=
    hstar0.coverTriple_valid S1_ hv1_ hord1_ hgood1
  have hcv2 : tAd _c1 :=
    hstar0.coverTriple_valid S2_ hv2_ hord2_ hgood2
  have : Smooth _c0.structMap := hcv1.smooth
  have : Smooth _c1.structMap := hcv2.smooth
  have : LocallyOfFiniteType
      _c0.structMap := hcv1.locallyOfFiniteType
  have : LocallyOfFiniteType
      _c1.structMap := hcv2.locallyOfFiniteType
  have : CharZero _c0.base := hcv1.charZero
  have : CharZero _c1.base := hcv2.charZero
  have hcdim2 : tDim _c1 ≤ tDim S2_ :=
    hstar0.coverTriple_dim_le S2_ hv2_
  have hcadm1 : ∀ [inst : LocallyOfFiniteType
      _c0.structMap],
      IsMaxContactHypersurface _c0.base
        _c0.structMap
        _c0.ideal
        _c0.mult
        _c4 := by
    intro _inst
    exact hstar0.coverContact_admissible S1_ hv1_ hgood1
  have hcadm2 : ∀ [inst : LocallyOfFiniteType
      _c1.structMap],
      IsMaxContactHypersurface _c1.base
        _c1.structMap
        _c1.ideal
        _c1.mult
        _c3 := by
    intro _inst
    exact hstar0.coverContact_admissible S2_ hv2_ hgood2
  have hcsnc1 : InStrictNormalCrossingPosition _c0.structMap
      [p31 hv1_] := hstar0.coverContact_snc S1_ hv1_ hgood1
  have hcsnc2 : InStrictNormalCrossingPosition _c1.structMap
      [p31 hv2_] := hstar0.coverContact_snc S2_ hv2_ hgood2
  have hcbd2 : ∀ D ∈ _c1.boundary, D ≠ ⊤ :=
    coverTriple_boundary_ne_top S2_ hv2_ hbd2_
  let _a2 := pi1 ≫ tMp _c0
  have hdv1 : tAd $ smoothPullbackTriple _c0 pi1 := by
    rw [smoothPullbackTriple_eq_dropTrivialBoundary]
    exact htv _ $ hin.valid_pullbackAlong _c0 hcv1 Q _a2 pi1 rfl
  have hdv2 : tAd $ smoothPullbackTriple _c1 pi2 := by
    rwa [hdeleq]
  have hdim2_ : tDim (smoothPullbackTriple _c1 pi2) ≤ tDim S2_ := by
    rwa [hdeleq]
  have hdadm1 : ∀ [inst : LocallyOfFiniteType
      (smoothPullbackTriple _c0 pi1).structMap],
      IsMaxContactHypersurface (smoothPullbackTriple _c0 pi1).base
        (smoothPullbackTriple _c0 pi1).structMap
        (smoothPullbackTriple _c0 pi1).ideal
        (smoothPullbackTriple _c0 pi1).mult
        (cmI _c4 pi1) := by
    intro inst
    have : LocallyOfFiniteType
        _a2 := inst
    exact hAdm _c0.base
      _c0.scheme _c0.structMap
      Q pi1 _c0.ideal _c0.mult
      hcv1.one_le_mult _c4 hcadm1
  have hdadm2 : ∀ [inst : LocallyOfFiniteType
      (smoothPullbackTriple _c1 pi2).structMap],
      IsMaxContactHypersurface (smoothPullbackTriple _c1 pi2).base
        (smoothPullbackTriple _c1 pi2).structMap
        (smoothPullbackTriple _c1 pi2).ideal
        (smoothPullbackTriple _c1 pi2).mult
        _c2 := by
    intro inst
    have : LocallyOfFiniteType
        (pi2 ≫ tMp _c1) := inst
    exact hAdm _c1.base
      _c1.scheme _c1.structMap
      Q pi2 _c1.ideal _c1.mult
      hcv2.one_le_mult _c3 hcadm2
  have hdsnc1 : InStrictNormalCrossingPosition (smoothPullbackTriple _c0 pi1).structMap
      [cmI _c4 pi1] :=
    inStrictNormalCrossingPosition_comap_singleton _c0.structMap pi1
      _c4 hcsnc1
  have hdsnc2 : InStrictNormalCrossingPosition (smoothPullbackTriple _c1 pi2).structMap
      [cmI _c3 pi2] :=
    inStrictNormalCrossingPosition_comap_singleton _c1.structMap pi2
      _c3 hcsnc2
  let _a3 := lowerDimensionalFamily A S2_
  have hB : IsPullbackBlowupSequence pi2
      (reduceAlongHypersurface hinv S2_ _a3
        (smoothPullbackTriple _c1 pi2)
        _c2).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (coverMarkedBlowupData S2_ hv2_ hinv _a3).toSequenceOfBlowups :=
    hdel hstar0 hin hMC hAdm hmono B hspec hshift S2_ S2_ hP2_ hP2_
      _c1 hcv2 hcord2 hcdim2
      _c3 hcadm2 hcsnc2 hcbd2 pi2 hdv2 hdim2_ hdadm2 hdsnc2
  have hdsnc2' : InStrictNormalCrossingPosition (smoothPullbackTriple _c0 pi1).structMap
      [cmI _c3 pi2] :=
    inStrictNormalCrossingPosition_of_triple_eq hdeleq.symm
      [cmI _c3 pi2]
      [cmI _c3 pi2] m129 hdsnc2
  have hdadm2' : ∀ [inst : LocallyOfFiniteType
      (smoothPullbackTriple _c0 pi1).structMap],
      IsMaxContactHypersurface (smoothPullbackTriple _c0 pi1).base
        (smoothPullbackTriple _c0 pi1).structMap
        (smoothPullbackTriple _c0 pi1).ideal
        (smoothPullbackTriple _c0 pi1).mult
        _c2 := by
    intro inst
    have hft2 := inst
    rw [← hdeleq] at hft2
    exact isMaxContactHypersurface_of_triple_eq hdeleq.symm inst hft2
      _c2
      _c2 m129 $ @hdadm2 hft2
  have e2_ := IsPullbackBlowupSequence.isomorphic hvv.isPullbackSequenceOfBlowups_withoutIsoBlowups hB
  rw [eq_of_heq $ reduceAlongHypersurface_toSequenceOfBlowups_heq hinv S2_ _a3 hdeleq _c2 _c2 m129] at e2_
  exact e2_.trans $ (reduceAlongHypersurface_isomorphic_of_isMaxContactHypersurface hinv P hmono A B hspec hshift hstar0 hin hMC hAdm S2_ hP2_ (smoothPullbackTriple _c0 pi1) hdv1 (orderAt_pullbackTriple_le_mult _c0 pi1 hcv1 hcord1) hdim _c2 (cmI _c4 pi1) hdadm2' hdsnc2' hdadm1 hdsnc1).trans (IsPullbackBlowupSequence.isomorphic hvv'.isPullbackSequenceOfBlowups_withoutIsoBlowups $ hdel hstar0 hin hMC hAdm hmono B hspec hshift S1_ S2_ hP1 hP2_ _c0 hcv1 hcord1 (hstar0.coverTriple_dim_le S1_ hv1_) _c4 hcadm1 hcsnc1 (coverTriple_boundary_ne_top S1_ hv1_ hbd1_) pi1 hdv1 hdim hdadm1 hdsnc1).symm

theorem maxContactPrincipalization_isPullbackBlowupSequence_of_smooth (hvan : TrivialOnEmptyOrderLocus hinv P A)
    (hsf : CoverSequenceProperties hinv P A) (hmd : MarkingDescends hinv P A)
    (hff : CoverFaithfullyFlat P) (htv : DropTrivialBoundaryAdmissible) (htm : MarkedOfMarkedDropTrivialBoundary)
    (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) (hP : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    {Y : Sch} qY (h : Y ⟶ scheme T)
    [Smooth h] [Flat h]
    (hq : h ≫ structMap T = qY)
    E'
    (hE : SameNontrivialBoundary (T.pbA qY h).boundary E')
    (hv' : IsAdmissible $ T.pbB qY h E')
    (hP' : P (T.pbB qY h E').krullDimSucc)
    (htrimv : IsAdmissible $ dropTrivialBoundary T)
    (hpbv : IsAdmissible $ dropTrivialBoundaryPullback T qY h E')
    (hqc : QuasiCompact
      (Limits.pullback.snd (coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (coverMap (dropTrivialBoundary T) htrimv) ≫
        structMap (coverTriple (dropTrivialBoundary T) htrimv)))
    (hdimfp : krullDimSucc
        (Limits.pullback (coverMap (dropTrivialBoundaryPullback T qY h E') hpbv ≫ h)
          (coverMap (dropTrivialBoundary T) htrimv)) ≤
      (T.pbA qY h).krullDimSucc) :
    IsPullbackBlowupSequence h
      (maxContactPrincipalization hinv A $ T.pbB qY h E').toSequenceOfBlowups
      (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  let _c0 := dropTrivialBoundaryPullback T qY h E'
  let _c1 := T.pbB qY h E'
  let _c2 := p12 (dropTrivialBoundary T) htrimv
  have horder :=
    hstar0.tuning.coSupport_tunedSheaf_eq_and_orderLE
  have hord2_ : ∀ x,
      orderAt _c1.ideal x
        ≤ ((tMu _c1 : ℕ) : ENat) :=
    fun x => orderAt_pullbackTriple_le_mult T h hv hord x
  by_cases hemp2_ : (orderAtLeastLocus (T.ideal.comap h) T.mult) = (∅ : Set Y)
  have hlen2_ :=
    length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A _ hv' hP' hord2_ hemp2_
  by_cases hemp1 : orderAtLeastLocus T.ideal T.mult = (∅ : CSet T.scheme)
  exact isPullback_of_length_eq_zero_of_length_eq_zero h _ _ hlen2_
    (length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hP hord hemp1)
  exact hvan T ⟨hP, hord, mpr_ nonempty_iff_ne_empty hemp1, hv⟩ h _ hlen2_ hemp2_
  have hcs2_ :=
    nonempty_iff_ne_empty.mpr hemp2_
  have hcs1_ : (orderAtLeastLocus T.ideal T.mult).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hzero
    exact hemp2_ $ orderAtLeastLocus_comap_eq_empty T hv h hzero
  have hypT : OrderReductionHypotheses P T := ⟨hP, hord, hcs1_, hv⟩
  have hypT2 : OrderReductionHypotheses P _c1 := ⟨hP', hord2_, hcs2_, hv'⟩
  obtain ⟨d1, hd1_, he1_⟩ := exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm T hypT
  obtain ⟨d2, hd2_, he2_⟩ := exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm
    _c1 hypT2
  have htrim2 :=
    (dropTrivialBoundary_eq_withBoundary_removeUnitIdeals _c1).trans rfl
  have hypS1 := hypT.of_dropTrivialBoundaryAdmissible htv
  have hypS2 :=
    orderReductionHypotheses_of_eq htrim2 $ hypT2.of_dropTrivialBoundaryAdmissible htv
  let _m0 := p12 _c0 hpbv
  let _a2 := hff (dropTrivialBoundary T) hypS1
  have hsu1_ :=
    _a2.1
  let _a5 := hff _c0 hypS2
  have hsu2_ :=
    _a5.1
  have hpbf := @smooth_pullback_fst_snd_and_surjective_fst T.scheme Y h ‹Smooth h› _ _
    _c2
    _m0
    (smooth_coverMap_of_isAdmissible _ htrimv) (smooth_coverMap_of_isAdmissible _ hpbv) hsu1_
  have hbdP :=
    fun D hD => ne_top_of_mem_removeUnitIdeals E' D hD
  have hcord2 := orderAt_coverTriple_le_mult hstar0 horder _c0 hpbv
    hord2_ ⟨hypS2.orderLE, hypS2.coSupport_nonempty⟩
  have hdeleq := @smoothPullbackTriple_coverTriple_eq T Y qY h ‹Smooth h› hq E' hE
    htrimv hpbv hsu2_ hpbf.2.2
  rw [he1_, he2_]
  refine isPullback_of_faithfullyFlat_covers h
    _c2
    _m0
    _a2.2 hsu1_ _a5.2 hsu2_
    (coverMarkedBlowupData (dropTrivialBoundary T) htrimv hinv $ lowerDimensionalFamily A $ dropTrivialBoundary T).toSequenceOfBlowups
    (coverMarkedBlowupData _c0 hpbv hinv $ lowerDimensionalFamily A _c0).toSequenceOfBlowups
    d1.toSequenceOfBlowups d2.toSequenceOfBlowups hd1_ (isStrictPullback_coverMarkedSequence_of_eq_of_heq hinv A htrim2 ((hypT2.of_dropTrivialBoundaryAdmissible htv).valid) hpbv d2 d2 m129 hd2_) (fun i hi => hsf.center_ne_top _c0 hypS2 i hi) ?_
  intro v v' hvv hvv'
  let _a3 := p12 _c0 hpbv ≫ h
  exact withoutIsoBlowups_isomorphic_of_smoothPullbackTriple_eq hinv P hmono A B hspec hshift hstar0 hin hMC hAdm hdel htv
    (dropTrivialBoundary T) _c0 htrimv hpbv hP hP'
    hord hord2_ hypS1.coSupport_nonempty hypS2.coSupport_nonempty (boundary_ne_top_of_eq (dropTrivialBoundary_eq_withBoundary_removeUnitIdeals T).symm fun D hD => ne_top_of_mem_removeUnitIdeals T.boundary D hD) hbdP
    hsu1_ hsu2_ (orderAt_coverTriple_le_mult hstar0 horder (dropTrivialBoundary T) htrimv hord ⟨hypS1.orderLE, hypS1.coSupport_nonempty⟩) hcord2
    (m47 _a3
      _c2)
    (m57 _a3
      _c2)
    hpbf.2.1 hpbf.1 hdeleq hqc hdimfp v v' hvv hvv'
end

end MaxContactFunctoriality





namespace NontrivialBoundary

section

variable {Y : Sch}

section
variable {L1_ L2_ L1' L2' : Bdy Y}
theorem sameNontrivialBoundary_append
    (h1_ : SameNontrivialBoundary L1_ L1')
    (h2_ : SameNontrivialBoundary L2_ L2') :
    SameNontrivialBoundary (L1_ ++ L2_) $ L1' ++ L2' :=
  h1_.append h2_

theorem sameNontrivialBoundary_cancel_left
    (h : SameNontrivialBoundary (L1_ ++ L2_) $ L1' ++ L2')
    (h1_ : SameNontrivialBoundary L1_ L1') :
    SameNontrivialBoundary L2_ L2' := by
  rw [sameNontrivialBoundary_iff] at h h1_ ⊢
  rw [nontrivialPart_append, nontrivialPart_append, h1_] at h
  exact List.append_cancel_left h
end

theorem sameNontrivialBoundary_refl (L : Bdy Y) : SameNontrivialBoundary L L :=
  MarkedIdealWithBoundary.SameNontrivialBoundary.refl L

theorem sameNontrivialBoundary_nontrivialPart (L : Bdy Y) :
    SameNontrivialBoundary (nontrivialPart L) L := by
  rw [sameNontrivialBoundary_iff]
  induction L with
  | nil => simp [nontrivialPart]
  | cons D L _ih =>
    by_cases h : D = ⊤
    simp [nontrivialPart, h]
    simp [nontrivialPart, h]

theorem nontrivialPart_top_singleton {Z : Sch} :
    nontrivialPart [(⊤ : ISD Z)] = [] := by
  simp [nontrivialPart]

section
variable {L L' : Bdy Y} (h : SameNontrivialBoundary L L')
include h
theorem sameNontrivialBoundary_symm : SameNontrivialBoundary L' L :=
  sy_ h

theorem sameNontrivialBoundary_append_top :
    SameNontrivialBoundary (L ++ [(⊤ : ISD Y)]) L' := by
  rw [sameNontrivialBoundary_iff] at h ⊢
  rw [nontrivialPart_append, h, nontrivialPart_top_singleton, List.append_nil]
end

theorem sameNontrivialBoundary_cons {D : ISD Y} {L L' : Bdy Y}
    (h : SameNontrivialBoundary L L') :
    SameNontrivialBoundary (D :: L) (D :: L') :=
  sameNontrivialBoundary_append (sameNontrivialBoundary_refl [D]) h

end

@[reducible] noncomputable def pullbackWithNontrivialBoundary (S : MarkedIdealWithBoundary) {X' : Sch}
    (q : X' ⟶ scheme S) : MarkedIdealWithBoundary :=
  @mk S.base S.instField X' (q ≫ structMap S) (S.ideal.comap q) S.mult
    $ nontrivialPart $ S.boundary.map fun D => comap D q

section

variable (R : MarkedIdealWithBoundary) (t : R.mbs)
theorem length_boundary_le_length_lastBoundary :
    R.boundary.length ≤ (t.boundary t.length).length := by
  have h3 : (t.boundary t.length).length = R.boundary.length + t.length := by
    rw [← toBlowupSequenceData_boundary_eq t t.length le_rfl]
    exact BlowupSequenceData.boundary_length _ _ _
  omega

theorem getElem_lastBoundary_eq_iteratedStrictTransform
    i (hi : i < R.boundary.length) :
    (t.boundary t.length)[i]'(lt_of_lt_of_le hi $ length_boundary_le_length_lastBoundary R t) =
      t.iteratedStrictTransform t.length (R.boundary[i]'hi) := by
  have hmap : i < length (R.boundary.map $ t.iteratedStrictTransform t.length) := by
    simpa using hi
  have h : t.boundary t.length = R.boundary.map (t.iteratedStrictTransform t.length) ++ t.boundaryFrom ([] : List $ tISD R) t.length := by
    rw [← toBlowupSequenceData_boundary_eq t t.length le_rfl, ← boundary_append,
      List.append_nil]
  rw [List.getElem_of_eq h, getElem_append_left hmap, getElem_map]

end

section

private theorem getElem_eq_getElem_of_eq.{v} {al_ : Type v} (l l' : List al_) n n'
    (hl : l = l') (hn : n = n') (h : n < length l) (h' : n' < length l') :
    l[n]'h = l'[n']'h' := by
  subst hl
  subst hn
  rfl

private theorem getElem_append_cons_length.{v} {al_ : Type v} :
    ∀ (A : List al_) (x : al_) (B : List al_) (h : length A < length (A ++ x :: B)),
      (A ++ x :: B)[length A]'h = x :=by simp_all
section
variable (S : MarkedIdealWithBoundary) {X'} (q : X' ⟶ scheme S)
noncomputable def survivingBoundaryCount
    (n : ℕ) : ℕ :=
  length $ nontrivialPart $ (S.boundary.take n).map fun D => comap D q

@[simp] theorem survivingBoundaryCount_zero :
    survivingBoundaryCount S q 0 = 0 := by
  simp [survivingBoundaryCount, nontrivialPart]

theorem survivingBoundaryCount_succ_of_eq_top
    (i : ℕ) (hi : i < S.boundary.length) (hdead : comap (S.boundary[i]'hi) q = ⊤) :
    survivingBoundaryCount S q (i + 1) = survivingBoundaryCount S q i := by
  have h : S.boundary.take (i + 1) = S.boundary.take i ++ S.boundary[i]?.toList :=
    List.take_add_one
  rw [List.getElem?_eq_getElem hi] at h
  have htake : S.boundary.take (i + 1) = S.boundary.take i ++ [S.boundary[i]'hi] := h
  unfold survivingBoundaryCount
  rw [htake]
  simp only [m144, m75, map_nil]
  rw [nontrivialPart_append, hdead, nontrivialPart_top_singleton, List.append_nil]

theorem survivingBoundaryCount_length_eq :
    survivingBoundaryCount S q S.boundary.length = (pullbackWithNontrivialBoundary S q).boundary.length := by
  have h : S.boundary.take (bLen S) = S.boundary := by simp
  show (nontrivialPart $ (S.boundary.take $ bLen S).map
      fun D => cmI D q).length = bLen (pullbackWithNontrivialBoundary S q)
  rw [h]
end

section
variable {Z : Sch} (D : ISD Z)
theorem nontrivialPart_singleton_of_ne_top
    (h : D ≠ ⊤) : nontrivialPart [D] = [D] := by
  simp [nontrivialPart, h]

theorem nontrivialPart_cons_of_ne_top (hD : D ≠ ⊤)
    L :
    nontrivialPart (D :: L) = D :: nontrivialPart L := by
  have h : nontrivialPart ([D] ++ L)
      = nontrivialPart [D] ++ nontrivialPart L := by
    rw [nontrivialPart_append]
  rw [nontrivialPart_singleton_of_ne_top D hD] at h
  simpa using h
end

section
variable (S : MarkedIdealWithBoundary) {X' : Sch} (q : X' ⟶ scheme S) (i : ℕ) (hi : i < S.boundary.length) (hlive : comap (S.boundary[i]'hi) q ≠ ⊤)
include hlive
theorem survivingBoundaryCount_succ_of_ne_top :
    survivingBoundaryCount S q (i + 1) = survivingBoundaryCount S q i + 1 := by
  have h : S.boundary.take (i + 1) = S.boundary.take i ++ S.boundary[i]?.toList :=
    List.take_add_one
  rw [List.getElem?_eq_getElem hi] at h
  have htake : S.boundary.take (i + 1) = S.boundary.take i ++ [S.boundary[i]'hi] := h
  unfold survivingBoundaryCount
  rw [htake]
  simp only [m144, m75, map_nil]
  rw [nontrivialPart_append, nontrivialPart_singleton_of_ne_top _ hlive,
    List.length_append]
  simp

theorem survivingBoundaryCount_lt_length :
    survivingBoundaryCount S q i < (pullbackWithNontrivialBoundary S q).boundary.length := by
  have hsucc := survivingBoundaryCount_succ_of_ne_top S q i hi hlive
  let _a0 := S.boundary.take $ i + 1
  let _a1 := S.boundary.drop $ i + 1
  have hmap : (S.boundary.map fun D => cmI D q) =
      (_a0.map fun D => cmI D q) ++
        (_a1.map fun D => cmI D q) := by
    rw [← m144, take_append_drop]
  have hlen : (pullbackWithNontrivialBoundary S q).boundary.length =
      length (nontrivialPart $ _a0.map fun D => cmI D q) +
        (nontrivialPart
          (_a1.map fun D => cmI D q)).length := by
    show length (nontrivialPart $ S.boundary.map fun D => cmI D q) = _
    rw [hmap, nontrivialPart_append, List.length_append]
  have hdef : survivingBoundaryCount S q (i + 1) =
      length (nontrivialPart $ _a0.map fun D => cmI D q) := rfl
  omega

end

end

section

variable (S : MarkedIdealWithBoundary) {X' : Sch} (q : X' ⟶ scheme S)
  (s : S.mbs)
  (s' : MarkedBlowupSequenceData (pullbackWithNontrivialBoundary S q).structMap (pullbackWithNontrivialBoundary S q).ideal
      (pullbackWithNontrivialBoundary S q).mult (pullbackWithNontrivialBoundary S q).boundary)
  (D : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)

theorem lastMap_comp_projectionToBase :
    D.lastMap ≫ s.proj s.length = s'.proj s'.length ≫ q := by
  have h := D.isPullback_lastMap.w
  rwa [toMarkedSequence_projectionToBase s _, toMarkedSequence_projectionToBase s' _] at h

theorem lastMap_comp_structureMorphism :
    D.lastMap ≫ (s.proj s.length ≫ structMap S) =
      s'.proj s'.length ≫ (q ≫ structMap S) := by
  exact st_ (assoc D.lastMap (lastP s) S.structMap)
    (tr_ (congrArg (CategoryStruct.comp · S.structMap) $ lastMap_comp_projectionToBase S q s s' D) $ assoc (lastP s') q S.structMap)

theorem ideal_and_boundary_comap_lastMap [Smooth q] (_hMaxContact : MaxContactCoverProperties)
    (hV : IsAdmissible S) (hV' : IsAdmissible $ pullbackWithNontrivialBoundary S q) :
    s'.ideal s'.length = (s.ideal s.length).comap D.lastMap ∧
      SameNontrivialBoundary (s'.boundary s'.length)
        ((s.boundary s.length).map fun A => A.comap D.lastMap) := by
  have hN : ∀ i, i ≤ s.length → IsNoetherian (s.obj i) := by
    intro i hi
    exact p25 effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi
  refine SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' D rfl
    (sameNontrivialBoundary_nontrivialPart $ S.boundary.map fun A => cmI A q) hN ?_
  intro j hj
  exact p25 effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj

section
variable {Y Z : Sch} (f : ISD Y → ISD Z) (L : Bdy Y) (n) (hn : n < length L)
include hn
theorem sameNontrivialBoundary_take_succ_of_eq_top (hf : f (L[n]'hn) = ⊤) (M : Bdy Z)
    (h : SameNontrivialBoundary ((L.take n).map f) M) :
    SameNontrivialBoundary ((L.take $ n + 1).map f) M := by
  rw [List.take_succ_eq_append_getElem hn, m144, m75, map_nil, hf]
  exact sameNontrivialBoundary_append_top h

theorem sameNontrivialBoundary_take_succ_of_getElem_eq (M : Bdy Z) (m : ℕ) (hm : m < length M)
    (hf : f (L[n]'hn) = M[m]'hm)
    (h : SameNontrivialBoundary ((L.take n).map f) $ M.take m) :
    SameNontrivialBoundary ((L.take $ n + 1).map f) $ M.take $ m + 1 := by
  rw [List.take_succ_eq_append_getElem hn, List.take_succ_eq_append_getElem hm, m144,
    m75, map_nil, hf]
  exact sameNontrivialBoundary_append h $ sameNontrivialBoundary_refl _
end

section
variable (k : Type) [Field k] [IsNoetherianRing k]
theorem balancedTunedSheaf_comap_of_smooth
    {X Y : Sch} (p : X ⟶ Sp k) (h : Y ⟶ X)
    (hsp : Smooth p) (hfp : LocallyOfFiniteType p)
    (hsh : Smooth h)
    (hfc : LocallyOfFiniteType $ h ≫ p)
    (I : ISD X) (m : ℕ) :
    balancedTunedSheaf k (h ≫ p) (comap I h) m = comap (balancedTunedSheaf k p I m) h := by
  exact balancedTunedSheaf_comap k p h I m

private theorem balancedTunedSheaf_congr
    {X : Sch} (p p' : X ⟶ Sp k)
    (hf : LocallyOfFiniteType p)
    (hf' : LocallyOfFiniteType p')
    (hp : p = p') (I I' : ISD X) (hI : I = I') (m : ℕ) :
    balancedTunedSheaf k p I m = balancedTunedSheaf k p' I' m := by
  subst hI
  subst hp
  rfl
end

theorem tunedIdealAtLength_comap_lastMap [Smooth q] (hstar : MaxContactCoverProperties)
    (hV : IsAdmissible S) (hV' : IsAdmissible $ pullbackWithNontrivialBoundary S q)
    (hftS : LocallyOfFiniteType $ s.proj s.length ≫ structMap S)
    (hftT : LocallyOfFiniteType
      (s'.proj s'.length ≫ structMap (pullbackWithNontrivialBoundary S q)))
    (hsm : Smooth $ s.proj s.length ≫ structMap S) :
    comap (tunedIdealAtLength S s hftS) D.lastMap = tunedIdealAtLength (pullbackWithNontrivialBoundary S q) s' hftT := by
  have hcomp := lastMap_comp_structureMorphism S q s s' D
  have hftT2 := hftT
  have hftcomp := hftT2
  rw [← hcomp] at hftcomp
  let _a0 := lastP s ≫ tMp S
  have h2 := balancedTunedSheaf_comap_of_smooth S.base _a0 D.lastMap
    hsm hftS (SequenceOfBlowupsPullback.smooth_lastMap D) hftcomp (lastI s) S.mult
  have h3 := balancedTunedSheaf_congr S.base (D.lastMap ≫ _a0)
    (lastP s' ≫ (q ≫ tMp S)) hftcomp hftT2 hcomp
    (cmI (lastI s) D.lastMap) (lastI s') ((ideal_and_boundary_comap_lastMap S q s s' D hstar hV hV').1).symm S.mult
  exact tr_ (congrArg (fun J : IdealSheafData (lastO s) => cmI J D.lastMap) $ tunedIdealAtLength_eq_balancedTunedSheaf S s hftS) $ st_ h2 $ tr_ h3 (tunedIdealAtLength_eq_balancedTunedSheaf (pullbackWithNontrivialBoundary S q) s' hftT).symm

theorem comap_eq_comap_comap_of_comp_eq {A B C : Sch} (e : A ⟶ B) (f : A ⟶ C)
    (g : B ⟶ C) (h : e ≫ g = f) (M : ISD C) :
    comap M f = comap (comap M g) e := by
  subst h
  simp [comap_comp]

section
variable [Flat q]
theorem iteratedStrictTransform_comap_lastMap (_hMaxContact : MaxContactCoverProperties)
    (hV : IsAdmissible S) (hV' : IsAdmissible $ pullbackWithNontrivialBoundary S q) (M : tISD S) :
    (s.iteratedStrictTransform s.length M).comap D.lastMap = s'.iteratedStrictTransform s'.length (M.comap q) := by
  have hz0s : s.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase 0 = s.isoZero.hom := by
    rw [toMarkedSequence_projectionToBase s 0, projectionToBase_eq_toBlowupSequenceData_projectionToBase,
      p23]
  have hz0s' : s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase 0 = s'.isoZero.hom := by
    rw [toMarkedSequence_projectionToBase s' 0, projectionToBase_eq_toBlowupSequenceData_projectionToBase,
      p23]
  have hsq := SequenceOfBlowupsPullback.mapToEarlierScheme_comp_projectionToBase D 0 (zero_le _) 0 $ zero_le _
  rw [hz0s, hz0s'] at hsq
  let _a0 := s'.isoZero.hom ≫ q
  refine (SequenceOfBlowupsPullback.iteratedStrictTransform_eq_comap_lastMap D (s.iteratedStrictTransform · M)
    (fun j => s'.iteratedStrictTransform j $ cmI M q) ?_ ?_ ((iteratedStrictTransform_zero _ $ cmI M q).trans $ tr_ ((comap_eq_comap_comap_of_comp_eq s'.isoZero.hom _a0 q rfl M).symm) $ tr_ (comap_eq_comap_comap_of_comp_eq (D.mapToEarlierScheme 0 (zero_le _) 0 $ zero_le _) _a0 s.isoZero.hom hsq M) $ congrArg (fun I : ISD (s.obj 0) => I.comap $ D.mapToEarlierScheme 0 (zero_le _) 0 $ zero_le _) (iteratedStrictTransform_zero _ M).symm) ?_ ?_).symm
  intro i hi
  exact p25 effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi
  intro j hj
  exact p25 effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj
  intro i _
  exact BlowupSequenceData.iteratedStrictTransform_succ _ i M
  simp_all

section
variable (hstar : MaxContactCoverProperties) (hV : IsAdmissible S) (hV' : IsAdmissible (pullbackWithNontrivialBoundary S q))
include hstar hV hV'
section
variable (i) (hi : i < S.boundary.length)
theorem lastBoundary_comap_lastMap_eq_top (hdead : comap (S.boundary[i]'hi) q = ⊤) :
    comap ((s.boundary s.length)[i]'(lt_of_lt_of_le hi $ length_boundary_le_length_lastBoundary S s)) D.lastMap =
      ⊤ := by
  rw [getElem_lastBoundary_eq_iteratedStrictTransform S s i hi, iteratedStrictTransform_comap_lastMap S q s s' D hstar hV hV' $ S.boundary[i]'hi, hdead, iteratedStrictTransform_top]
  rfl

theorem getElem_lastBoundary_comap_lastMap (hlive : (S.boundary[i]'hi).comap q ≠ ⊤) :
    ((s.boundary s.length)[i]'(lt_of_lt_of_le hi (length_boundary_le_length_lastBoundary S s))).comap D.lastMap =
      (s'.boundary s'.length)[survivingBoundaryCount S q i]'(lt_of_lt_of_le
        (survivingBoundaryCount_lt_length S q i hi hlive) (length_boundary_le_length_lastBoundary (pullbackWithNontrivialBoundary S q) s')) := by
  let _a3 := survivingBoundaryCount_lt_length S q i hi hlive
  let _a4 := pullbackWithNontrivialBoundary S q
  have h2 := getElem_lastBoundary_eq_iteratedStrictTransform _a4 s' (survivingBoundaryCount S q i)
    _a3
  have h3 := by
    have hsplit : S.boundary
        = S.boundary.take i ++ ((S.boundary[i]'hi) :: S.boundary.drop (i + 1)) := by simp_all
    have hmapeq : S.boundary.map (·.comap q)
        = (S.boundary.take i).map (·.comap q)
          ++ (cmI (S.boundary[i]'hi) q :: (S.boundary.drop (i + 1)).map (·.comap q)) := by
      conv_lhs => rw [hsplit]
      simp only [m144, m75]
    have hntp : nontrivialPart (S.boundary.map (·.comap q))
        = nontrivialPart ((S.boundary.take i).map (·.comap q))
          ++ (cmI (S.boundary[i]'hi) q ::
              nontrivialPart ((S.boundary.drop (i + 1)).map (·.comap q))) := by
      rw [hmapeq, nontrivialPart_append, nontrivialPart_cons_of_ne_top _ hlive]
    have hlt : (nontrivialPart ((S.boundary.take i).map (·.comap q))).length
        < (nontrivialPart (S.boundary.map (·.comap q))).length := by
      rw [hntp, List.length_append, length_cons]
      omega
    have hbound :
        (nontrivialPart ((S.boundary.take i).map (·.comap q))).length
        < (nontrivialPart ((S.boundary.take i).map (·.comap q))
            ++ (cmI (S.boundary[i]'hi) q ::
              nontrivialPart
                ((S.boundary.drop (i + 1)).map (·.comap q)))).length := by
      rw [List.length_append, length_cons]
      omega
    have htb : _a4.boundary
        = nontrivialPart (S.boundary.map (·.comap q)) := rfl
    have hsc : survivingBoundaryCount S q i
        = (nontrivialPart ((S.boundary.take i).map (·.comap q))).length := rfl
    exact tr_ (getElem_eq_getElem_of_eq _ _ _ _ htb hsc _a3 hlt) ((getElem_eq_getElem_of_eq _ _ _ _ hntp rfl hlt hbound).trans (getElem_append_cons_length _ _ _ hbound))
  rw [getElem_lastBoundary_eq_iteratedStrictTransform S s i hi, h2, h3]
  exact iteratedStrictTransform_comap_lastMap S q s s' D hstar hV hV' (S.boundary[i]'hi)
end

theorem sameNontrivialBoundary_lastBoundary_take :
    ∀ n : ℕ, n ≤ S.boundary.length →
      SameNontrivialBoundary
        (((s.boundary s.length).take n).map fun A => comap A D.lastMap)
        ((s'.boundary s'.length).take $ survivingBoundaryCount S q n) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [survivingBoundaryCount_zero]
      simp [List.take_zero]
      exact sameNontrivialBoundary_refl _
  | succ n ih =>
      intro hn
      have hi : n < S.boundary.length := by omega
      have ihn := ih $ le_of_lt hi
      have hnlt :=
        lt_of_lt_of_le hi $ length_boundary_le_length_lastBoundary S s
      by_cases hdead : cmI (S.boundary[n]'hi) q = ⊤
      have hsc :=
        survivingBoundaryCount_succ_of_eq_top S q n hi hdead
      rw [hsc]
      exact sameNontrivialBoundary_take_succ_of_eq_top (·.comap D.lastMap)
        (lastB s) n hnlt (lastBoundary_comap_lastMap_eq_top S q s s' D hstar hV hV' n hi hdead) _ ihn
      have hsc :=
        survivingBoundaryCount_succ_of_ne_top S q n hi hdead
      rw [hsc]
      exact sameNontrivialBoundary_take_succ_of_getElem_eq (·.comap D.lastMap)
        (lastB s) n hnlt (lastB s') (survivingBoundaryCount S q n) (lt_of_lt_of_le (survivingBoundaryCount_lt_length S q n hi hdead) $ length_boundary_le_length_lastBoundary (pullbackWithNontrivialBoundary S q) s') (getElem_lastBoundary_comap_lastMap S q s s' D hstar hV hV' n hi hdead) ihn
end
end

theorem sameNontrivialBoundary_congr {Z : Sch}
    {L L' M M' : Bdy Z}
    (h : SameNontrivialBoundary L M) (hL : L' = L) (hM : M' = M) :
    SameNontrivialBoundary L' M' :=by simp_all
theorem markedIdealWithBoundary_mk_congr__b3 {k : Type} [inst : Field k] {X : Sch}
    {p p'} {I I'} {m m'}
    {E E'}
    (hp : p = p') (hI : I = I') (hm : m = m') (hE : E = E') :
    mk k X p I m E = mk k X p' I' m' E' :=by simp_all
theorem sameNontrivialBoundary_lastBoundary_drop [Flat q] (hstar : MaxContactCoverProperties)
    (hV : IsAdmissible S) (hV' : IsAdmissible $ pullbackWithNontrivialBoundary S q) :
    SameNontrivialBoundary
      ((s'.boundary s'.length).drop (pullbackWithNontrivialBoundary S q).boundary.length)
      (((s.boundary s.length).drop S.boundary.length).map fun A => A.comap D.lastMap) := by
  have hN : ∀ i, i ≤ s.length → IsNoetherian (s.obj i) := by
    intro i hi
    exact p25 effectiveCartierSupportContainsNoComponent hV s.toMarkedSequenceOfBlowups i hi
  have hN' : ∀ j, j ≤ s'.length → IsNoetherian (s'.obj j) := by
    intro j hj
    exact p25 effectiveCartierSupportContainsNoComponent hV' s'.toMarkedSequenceOfBlowups j hj
  let _a0 := lastB s
  have htake := sameNontrivialBoundary_lastBoundary_take S q s s' D hstar hV hV' S.boundary.length le_rfl
  rw [survivingBoundaryCount_length_eq] at htake
  have hsplit : ((_a0.take $ bLen S).map fun A => A.comap D.lastMap) ++
      ((_a0.drop $ bLen S).map fun A => A.comap D.lastMap) =
      _a0.map fun A => A.comap D.lastMap := by
    rw [← m144, take_append_drop]
  exact sameNontrivialBoundary_cancel_left (sameNontrivialBoundary_congr ((SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap s s' D rfl (sameNontrivialBoundary_nontrivialPart $ S.boundary.map fun A => cmI A q) hN hN').2) (take_append_drop _ _) hsplit) htake.symm

theorem pullbackAlong_derivedTriple_eq [Smooth q] (hstar : MaxContactCoverProperties)
    (hV : IsAdmissible S) (hV' : IsAdmissible $ pullbackWithNontrivialBoundary S q)
    (hftS : LocallyOfFiniteType $ s.proj s.length ≫ structMap S)
    (hftT : LocallyOfFiniteType
      (s'.proj s'.length ≫ structMap (pullbackWithNontrivialBoundary S q)))
    (hsm : Smooth $ s.proj s.length ≫ structMap S)
    (extra : List (s.obj s.length).IdealSheafData) (keep keep' : ℕ) :
    ((derivedTriple S s hftS extra keep).pullbackAlong (s'.obj s'.length)
          (D.lastMap ≫ structMap (derivedTriple S s hftS extra keep))
          D.lastMap).withBoundary
        (@append (s'.obj s'.length).IdealSheafData
          (extra.map fun A => comap A D.lastMap)
          ((s'.boundary s'.length).drop keep')) =
      derivedTriple (pullbackWithNontrivialBoundary S q) s' hftT
        (extra.map fun A => comap A D.lastMap) keep' := by
  let _a0 := derivedTriple S s hftS extra keep
  let _a1 := pullbackWithNontrivialBoundary S q
  refine markedIdealWithBoundary_mk_congr__b3 (k := S.base) (inst := S.instField) (X := lastO s')
    (p := D.lastMap ≫ tMp _a0)
    (p' := tMp $ derivedTriple _a1 s' hftT
      (extra.map fun A => cmI A D.lastMap) keep')
    (I := _a0.ideal.comap D.lastMap)
    (I' := (derivedTriple _a1 s' hftT
      (extra.map fun A => cmI A D.lastMap) keep').ideal)
    (m := tMu _a0)
    (m' := tMu $ derivedTriple _a1 s' hftT
      (extra.map fun A => cmI A D.lastMap) keep')
    (E := @append (lastO s').IdealSheafData
      (extra.map fun A => cmI A D.lastMap) $ (lastB s').drop keep')
    (E' := (derivedTriple _a1 s' hftT
      (extra.map fun A => cmI A D.lastMap) keep').boundary)
    (hp := ?_) (hI := ?_) (hm := rfl) (hE := rfl)
  simp [structureMorphism_derivedTriple]
  exact lastMap_comp_structureMorphism S q s s' D
  simp [ideal_derivedTriple]
  exact tunedIdealAtLength_comap_lastMap S q s s' D hstar hV hV' hftS hftT hsm

end

end NontrivialBoundary

end FunctorialResolution.EmbeddedResolution

end
section
universe v


section

namespace FunctorialResolution.EmbeddedResolution

namespace BoundaryDeletion

theorem take_append_getElem_cons_drop {al_ : Type v} (L : List al_) (i : ℕ)
    (h : i < length L) : L.take i ++ L[i] :: L.drop (i + 1) = L :=by simp_all
theorem sameNontrivialBoundary_congr_right {X : Sch} (L1_ L2_ L2' : Bdy X)
    (h : L2_ = L2') (hbe : SameNontrivialBoundary L1_ L2') :
    SameNontrivialBoundary L1_ L2_ := by
  subst h
  exact hbe

theorem sameNontrivialBoundary_congr__b4 {X : Sch} (L1_ L1' L2_ L2' : Bdy X)
    (h1_ : L1_ = L1') (h2_ : L2_ = L2') (hbe : SameNontrivialBoundary L1' L2') :
    SameNontrivialBoundary L1_ L2_ :=by simp_all
private theorem isPullback_congr {X0 Y0 : Sch} (ph_ : Y0 ⟶ X0) (sbase : SequenceOfBlowups X0)
    {t1_ t2_ : SequenceOfBlowups Y0} (h : t1_ = t2_) (hp : IsPullbackBlowupSequence ph_ t1_ sbase) :
    IsPullbackBlowupSequence ph_ t2_ sbase := by
  subst h
  exact hp

theorem isPullback_congr_marked (F : PrincipalizationAssignment) {X0 : Sch}
    (sbase : SequenceOfBlowups X0) {T1_ T2_ : MarkedIdealWithBoundary} (h : T1_ = T2_)
    (ph1 : scheme T1_ ⟶ X0) (ph2 : scheme T2_ ⟶ X0) (hph : HEq ph1 ph2)
    (hp : IsPullbackBlowupSequence ph1 (F T1_).toSequenceOfBlowups sbase) :
    IsPullbackBlowupSequence ph2 (F T2_).toSequenceOfBlowups sbase := by
  subst h
  have hee := eq_of_heq hph
  subst hee
  exact hp

section
variable {T1_ T2_ : MarkedIdealWithBoundary} (h : T1_ = T2_)
include h
private theorem isAdmissible_of_eq (hv : IsAdmissible T2_) :
    IsAdmissible T1_ := by
  subst h
  exact hv

private theorem pred_dim_of_eq (P : ℕ → Prop)
    (hp : P T2_.krullDimSucc) : P T1_.krullDimSucc := by
  subst h
  exact hp

private theorem isOrderBoundedByMult_of_eq
    (ho : T2_.IsOrderBoundedByMult) : T1_.IsOrderBoundedByMult := by
  subst h
  exact ho

theorem locallyOfFiniteType_of_eq
    (h2_ : LocallyOfFiniteType T2_.structMap) :
    LocallyOfFiniteType T1_.structMap := by
  subst h
  exact h2_

private theorem isBalanced_of_eq
    (h1_ : LocallyOfFiniteType T1_.structMap)
    (h2_ : LocallyOfFiniteType T2_.structMap)
    (hd : T2_.IsBalanced h2_) : T1_.IsBalanced h1_ := by
  subst h
  exact hd
end

section
variable (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment)
theorem isPullback_of_sameNontrivialBoundary (j c : ℕ)
    (hshift : IsBoundaryPositionInvariant P A)
    (W : MarkedIdealWithBoundary) (hWP : P W.krullDimSucc) (hWO : W.IsOrderBoundedByMult)
    (hftW : LocallyOfFiniteType W.structMap) (hWD : W.IsBalanced hftW)
    (E1_ E2_ E1' E2' : List W.scheme.IdealSheafData) (Dv : W.scheme.IdealSheafData)
    (hBE1_ : SameNontrivialBoundary E1_ E1')
    (hBE2_ : SameNontrivialBoundary E2_ E2')
    (hlen : length E1_ = j) (hlen' : length E1' = c)
    (hV1 : IsAdmissible $ withBoundary W (E1_ ++ Dv :: E2_))
    (hV2 : IsAdmissible $ withBoundary W (E1' ++ Dv :: E2'))
    {X0 : Sch} (ph_ : scheme (withBoundary W (E1_ ++ Dv :: E2_)) ⟶ X0)
    (sbase : SequenceOfBlowups X0)
    (hpull : IsPullbackBlowupSequence ph_ (A j $ withBoundary W (E1_ ++ Dv :: E2_)).toSequenceOfBlowups sbase) :
    IsPullbackBlowupSequence ph_ (A c $ withBoundary W (E1' ++ Dv :: E2')).toSequenceOfBlowups sbase := by
  have hEq := hshift.shift W hWP hWO hftW hWD E1_ E2_ E1' E2' Dv hBE1_ hBE2_ hV1 hV2
  rw [hlen, hlen'] at hEq
  exact IsPullbackBlowupSequence.of_isomorphic hpull hEq

theorem isPullbackBlowupSequence_pullbackAlong (Bl : PrincipalizationAssignment) (j c : ℕ)
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl) (hshift : IsBoundaryPositionInvariant P A)
    (V : MarkedIdealWithBoundary) (hVv : IsAdmissible V) (hP : P V.krullDimSucc) (hO : V.IsOrderBoundedByMult)
    (hftV : LocallyOfFiniteType V.structMap) (hDb : V.IsBalanced hftV)
    (Y : Sch) (qy : Y ⟶ Sp V.base) (hmap : Y ⟶ V.scheme)
    (hsm : Smooth hmap) (hqy : hmap ≫ structMap V = qy)
    (LT : List Y.IdealSheafData)
    (hVv' : IsAdmissible (V.pbB qy hmap LT))
    (hP' : P (V.pbB qy hmap LT).krullDimSucc)
    (hO' : (V.pbB qy hmap LT).IsOrderBoundedByMult)
    (hftV' : LocallyOfFiniteType
      (V.pbB qy hmap LT).structMap)
    (hDb' : (V.pbB qy hmap LT).IsBalanced hftV')
    (Lbd : List V.scheme.IdealSheafData) (hLbd : V.boundary = Lbd)
    (hjLbd : j < Lbd.length) (hcLT : c < LT.length)
    (hget : (Lbd[j]'hjLbd).comap hmap = LT[c]'hcLT)
    (hfull : SameNontrivialBoundary (Lbd.map fun D => D.comap hmap) LT)
    (hpre : SameNontrivialBoundary ((Lbd.take j).map fun D => D.comap hmap) (LT.take c))
    (hsuf : SameNontrivialBoundary ((Lbd.drop (j + 1)).map fun D => D.comap hmap)
      (LT.drop (c + 1))) :
    IsPullbackBlowupSequence hmap (A c (V.pbB qy hmap LT)).toSequenceOfBlowups
      (A j V).toSequenceOfBlowups := by
  have hPBb :=
    (pullbackAlong_boundary V Y qy hmap).trans
      (congrArg (List.map (·.comap hmap)) hLbd)
  have hjV := hjLbd
  rw [← hLbd] at hjV
  have hmaplen : (Lbd.map (·.comap hmap)).length = Lbd.length := by simp
  have hlenPB := hmaplen
  rw [← hPBb] at hlenPB
  have hjPB := hjLbd
  rw [← hlenPB] at hjPB
  have hPW := hP'
  have hOW := hO'
  have hDW := hDb'
  let _a0 := V.pbA qy hmap
  have hLTbe :=
    sameNontrivialBoundary_congr_right LT _a0.boundary
      (Lbd.map (·.comap hmap)) hPBb hfull.symm
  have hPBV :=
    validOfSameNontrivialBoundary (tWB _a0 LT)
      _a0.boundary hVv' hLTbe
  let _a1 := Lbd.drop $ j + 1
  have hsplit : (Lbd.take j).map (·.comap hmap) ++ (LT[c]'hcLT)
        :: _a1.map (·.comap hmap) = Lbd.map (·.comap hmap) := by
    rw [← hget]
    have h := congrArg (fun L : List V.scheme.IdealSheafData => L.map (·.comap hmap))
      (take_append_getElem_cons_drop Lbd j hjLbd)
    simpa only [map_append, map_cons] using h
  have hsplitLT :=
    take_append_getElem_cons_drop LT c hcLT
  have hPBself :=
    (congrArg (withBoundary _a0)
      (tr_ hsplit hPBb.symm)).trans (withBoundary_self _)
  have hPBeq :=
    congrArg (withBoundary _a0) hsplitLT
  let _a2 := A j V
  have hpull1 :=
    isPullback_congr hmap _a2.toSequenceOfBlowups
      (eq_of_heq ((A j).toSequenceOfBlowups_heq_of_eq hPBself.symm)) (hspec.isPullbackBlowupSequence_of_smooth V hVv hP hO hDb hjV Y qy hmap hqy hPBV hPW hOW hDW hjPB)
  have hV1 : (withBoundary _a0
      ((Lbd.take j).map (·.comap hmap) ++ (LT[c]'hcLT)
        :: _a1.map (·.comap hmap))).IsAdmissible := by
    rwa [hPBself]
  have hV2 : (withBoundary _a0
      (LT.take c ++ (LT[c]'hcLT) :: LT.drop (c + 1))).IsAdmissible := by
    rwa [hPBeq]
  have hlenE1 : ((Lbd.take j).map (·.comap hmap)).length = j := by
    simp [length_map, length_take]
    omega
  have hlenE1' : (LT.take c).length = c := by
    simp [length_take]
    omega
  have hres := isPullback_of_sameNontrivialBoundary P A j c hshift _a0 hPW hOW hftV' hDW
    ((Lbd.take j).map (·.comap hmap)) (_a1.map (·.comap hmap))
    (LT.take c) (LT.drop (c + 1)) (LT[c]'hcLT) hpre hsuf hlenE1 hlenE1' hV1 hV2 hmap
    _a2.toSequenceOfBlowups hpull1
  exact isPullback_congr hmap _a2.toSequenceOfBlowups
    (eq_of_heq ((A c).toSequenceOfBlowups_heq_of_eq hPBeq)) hres
end

variable (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment) (Bl : PrincipalizationAssignment) (j : ℕ)
  (S : MarkedIdealWithBoundary) {X' : Sch} (q : X' ⟶ scheme S) [Smooth q]
  (s : S.mbs)
  (s' : MarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary)
  (Dt : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
  (hftS : LocallyOfFiniteType $ s.proj s.length ≫ structMap S)
  (hftT : LocallyOfFiniteType
    $ s'.proj s'.length ≫ structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q))

include Dt in
theorem isPullbackBlowupSequence_appendLowerDimReduction
    (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (hstar : MaxContactCoverProperties)
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl)
    (hspec' : IsBoundaryDivisorReduction P (NontrivialBoundary.survivingBoundaryCount S q j)
      (A (NontrivialBoundary.survivingBoundaryCount S q j)) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hV : IsAdmissible S) (hV' : IsAdmissible (NontrivialBoundary.pullbackWithNontrivialBoundary S q))
    (hm : 1 ≤ mult S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((mult S : ℕ) : ENat))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((mult S : ℕ) : ENat))
    (hj : j < S.boundary.length)
    (hlive : comap (S.boundary[j]'hj) q ≠ ⊤)
    (hPU : P (derivedTriple S s hftS [] 0).krullDimSucc)
    (hVU : IsAdmissible (derivedTriple S s hftS [] 0))
    (hPU' : P (derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc)
    (hVU' : IsAdmissible (derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0))
    (hdimU : (derivedTriple S s hftS [] 0).krullDimSucc ≤ T.krullDimSucc)
    (hdimU' : (derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc ≤ T.krullDimSucc) :
    IsPullbackBlowupSequence q
      (appendLowerDimReduction hinv T (fun S0 _ i => A i S0) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
        [] 0 (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendLowerDimReduction hinv T (fun S0 _ i => A i S0) S s [] 0
        j).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  let _a9 := NontrivialBoundary.survivingBoundaryCount_lt_length S q j hj hlive
  let _a0 := NontrivialBoundary.pullbackWithNontrivialBoundary S q
  classical
  have hjb : j < ((([] : List (lastO s).IdealSheafData))
      ++ List.drop 0 (lastB s)).length := by
    simpa using lt_of_lt_of_le hj (NontrivialBoundary.length_boundary_le_length_lastBoundary S s)
  let _a10 := NontrivialBoundary.survivingBoundaryCount S q j
  have hjb' : _a10 <
      ((([] : List (lastO s').IdealSheafData))
        ++ List.drop 0 (lastB s')).length := by
    simpa using lt_of_lt_of_le _a9
      (NontrivialBoundary.length_boundary_le_length_lastBoundary _a0 s')
  obtain ⟨hmk, hEq, -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A Bl j hspec
    (fun S0 _ i => A i S0) (fun _ _ _ => rfl) S hV hm hO s [] 0 hftS hdimU hPU hVU hjb (by simp)
  obtain ⟨hmk', hEq', -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A Bl
    _a10 hspec' (fun S0 _ i => A i S0) (fun _ _ _ => rfl)
    _a0 hV' hm hO' s' [] 0 hftT hdimU' hPU' hVU' hjb' (by simp)
  rw [hEq, hEq']
  refine isPullbackBlowupSequence_append_same_field q s _ s' _ hinv Dt ?_
  refine SequenceOfBlowupsPullback.toBlowupDataOfSeq
    (IsPullbackBlowupSequence.nonempty_sequenceOfBlowupsPullback
      ?_).some
  classical
  have hflatq : Flat q := inferInstance
  have hsm : Smooth (lastP s ≫ tMp S) := by
    have hsmU := hVU.smooth
    rwa [structureMorphism_derivedTriple] at hsmU
  have hpb0 := NontrivialBoundary.pullbackAlong_derivedTriple_eq S q s s' Dt hstar hV hV' hftS hftT hsm [] 0 0
  let _a6 := NontrivialBoundary.pullbackWithNontrivialBoundary S q
  have hOU' := isOrderBoundedByMult_derivedTriple hstar _a6 hV' hm hO' s'
    hftT [] 0 hVU'
  have hDU' := isBalanced_derivedTriple hstar _a6 hV' hm hO' s'
    hftT [] 0 hVU'
  have hUb : (derivedTriple S s hftS [] 0).boundary = lastB s := by
    simp
  let _a0 := _a10
  let _a3 := lastB s'
  have hfull :=
    ((NontrivialBoundary.ideal_and_boundary_comap_lastMap S q s s' Dt hstar hV hV').2).symm
  let _a5 := (lastB s).take (j + 1)
  let _a7 := _a3.take $ _a0 + 1
  have hpre1 : SameNontrivialBoundary
      (_a5.map (·.comap Dt.lastMap))
      _a7 := by
    have hh := NontrivialBoundary.sameNontrivialBoundary_lastBoundary_take S q s s' Dt hstar hV hV' (j + 1) hj
    rwa [NontrivialBoundary.survivingBoundaryCount_succ_of_ne_top S q j hj hlive] at hh
  have hmapsplit : _a5.map (·.comap Dt.lastMap)
        ++ ((lastB s).drop (j + 1)).map (·.comap Dt.lastMap)
      = (lastB s).map (·.comap Dt.lastMap) := by
    rw [← m144, take_append_drop]
  have hltsplit : _a7
        ++ _a3.drop (_a0 + 1)
      = lastB s' := take_append_drop _ _
  have hPW' := pred_dim_of_eq hpb0 P hPU'
  have hOW' := isOrderBoundedByMult_of_eq hpb0 hOU'
  have hftW' := locallyOfFiniteType_of_eq hpb0 hVU'.locallyOfFiniteType
  have hDW' := isBalanced_of_eq hpb0 hftW' hVU'.locallyOfFiniteType hDU'
  have hinner := isPullbackBlowupSequence_pullbackAlong P A Bl j _a0 hspec hshift
    (derivedTriple S s hftS [] 0) hVU hPU (isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS [] 0 hVU) hVU.locallyOfFiniteType (isBalanced_derivedTriple hstar S hV hm hO s hftS [] 0 hVU)
    (lastO s') (Dt.lastMap ≫ tMp (derivedTriple S s hftS [] 0))
    Dt.lastMap Dt.smooth_lastMap rfl (lastB s')
    (isAdmissible_of_eq hpb0 hVU') hPW' hOW' hftW' hDW'
    (lastB s) hUb (lt_of_lt_of_le hj (NontrivialBoundary.length_boundary_le_length_lastBoundary S s)) (lt_of_lt_of_le _a9 (NontrivialBoundary.length_boundary_le_length_lastBoundary _a6 s')) (NontrivialBoundary.getElem_lastBoundary_comap_lastMap S q s s' Dt hstar hV hV' j hj hlive) hfull (NontrivialBoundary.sameNontrivialBoundary_lastBoundary_take S q s s' Dt hstar hV hV' j (le_of_lt hj)) (NontrivialBoundary.sameNontrivialBoundary_cancel_left (sameNontrivialBoundary_congr__b4 _ _ _ _ hmapsplit hltsplit hfull) hpre1)
  exact isPullback_congr_marked (A _a0)
    (A j (derivedTriple S s hftS [] 0)).toSequenceOfBlowups hpb0 Dt.lastMap Dt.lastMap
    m129 hinner

include Dt in
def continuationComparison
    (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (hstar : MaxContactCoverProperties)
    (hspec : IsBoundaryDivisorReduction P j (A j) Bl)
    (hspec' : IsBoundaryDivisorReduction P (NontrivialBoundary.survivingBoundaryCount S q j)
      (A $ NontrivialBoundary.survivingBoundaryCount S q j) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hV : IsAdmissible S) (hV' : IsAdmissible $ NontrivialBoundary.pullbackWithNontrivialBoundary S q)
    (hm : 1 ≤ mult S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((mult S : ℕ) : ENat))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((mult S : ℕ) : ENat))
    (hj : j < S.boundary.length)
    (hlive : comap (S.boundary[j]'hj) q ≠ ⊤)
    (hPU : P (derivedTriple S s hftS [] 0).krullDimSucc)
    (hVU : IsAdmissible $ derivedTriple S s hftS [] 0)
    (hPU' : P (derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc)
    (hVU' : IsAdmissible $ derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0)
    (hdimU : (derivedTriple S s hftS [] 0).krullDimSucc ≤ T.krullDimSucc)
    (hdimU' : (derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT [] 0).krullDimSucc ≤ T.krullDimSucc) :
    SequenceOfBlowupsPullback q
      (appendLowerDimReduction hinv T (fun S0 _ i => A i S0) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
        [] 0 $ NontrivialBoundary.survivingBoundaryCount S q j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendLowerDimReduction hinv T (fun S0 _ i => A i S0) S s [] 0 j).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
  (IsPullbackBlowupSequence.nonempty_sequenceOfBlowupsPullback
    (isPullbackBlowupSequence_appendLowerDimReduction (P := P) (A := A) (Bl := Bl) (j := j) (S := S) (q := q)
      (s := s) (s' := s') (Dt := Dt) (hftS := hftS) (hftT := hftT)
      (hinv := hinv) (T := T) (hstar := hstar) (hspec := hspec) (hspec' := hspec')
      (hshift := hshift) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
      (hj := hj) (hlive := hlive) (hPU := hPU) (hVU := hVU) (hPU' := hPU') (hVU' := hVU')
      (hdimU := hdimU) (hdimU' := hdimU'))).some

end BoundaryDeletion

end FunctorialResolution.EmbeddedResolution

end
end
section


namespace FunctorialResolution.EmbeddedResolution

namespace StrictTransformComparison

variable (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment) (Bl : PrincipalizationAssignment)
  (S : MarkedIdealWithBoundary) {X' : Sch} (q : X' ⟶ scheme S) [Smooth q]
  (s : S.mbs)
  (s' : MarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary)
  (Dt : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
  (hftS : LocallyOfFiniteType $ s.proj s.length ≫ structMap S)
  (hftT : LocallyOfFiniteType
    $ s'.proj s'.length ≫ structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q))

theorem strictTransformAtLength_comap_lastMap
    (hstar : MaxContactCoverProperties)
    (hV : IsAdmissible S) (hV' : IsAdmissible $ NontrivialBoundary.pullbackWithNontrivialBoundary S q)
    (H : tISD S) :
    strictTransformAtLength s' (comap H q)
      = comap (strictTransformAtLength s H) Dt.lastMap := by
  have : Flat q := inferInstance
  have h1 : strictTransformAtLength s' (cmI H q) = s'.iteratedStrictTransform s'.length (cmI H q) := by
    rw [strictTransformAtLength_eq, iteratedStrictTransform_eq_toBlowupSequenceData]
  have h2 : strictTransformAtLength s H = s.iteratedStrictTransform s.length H := by
    rw [strictTransformAtLength_eq, iteratedStrictTransform_eq_toBlowupSequenceData]
  rw [h1, h2]
  exact sy_ $ NontrivialBoundary.iteratedStrictTransform_comap_lastMap S q s s' Dt hstar hV hV' H

include Dt in
theorem isPullbackBlowupSequence_appendLowerDimReduction
    (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (hstar : MaxContactCoverProperties)
    (hspec : IsBoundaryDivisorReduction P 0 (A 0) Bl)
    (H : tISD S)
    (hV : IsAdmissible S) (hV' : IsAdmissible (NontrivialBoundary.pullbackWithNontrivialBoundary S q))
    (hm : 1 ≤ mult S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((mult S : ℕ) : ENat))
    (hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((mult S : ℕ) : ENat))
    (hdimU : (derivedTriple S s hftS
        [strictTransformAtLength s H] S.boundary.length).krullDimSucc ≤ T.krullDimSucc)
    (hPU : P (derivedTriple S s hftS
        [strictTransformAtLength s H] S.boundary.length).krullDimSucc)
    (hVU : (derivedTriple S s hftS
        [strictTransformAtLength s H] S.boundary.length).IsAdmissible)
    (hdimU' : (derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [strictTransformAtLength s' (comap H q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc ≤ T.krullDimSucc)
    (hPU' : P (derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [strictTransformAtLength s' (comap H q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc)
    (hVU' : (derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s' hftT
        [strictTransformAtLength s' (comap H q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).IsAdmissible)
    (hsep : BoundarySeparated S s S.boundary.length)
    (hsep' : BoundarySeparated (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) :
    IsPullbackBlowupSequence q
      (appendLowerDimReduction hinv T (fun S0 _ i => A i S0) (NontrivialBoundary.pullbackWithNontrivialBoundary S q) s'
        [strictTransformAtLength s' (comap H q)]
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendLowerDimReduction hinv T (fun S0 _ i => A i S0) S s
        [strictTransformAtLength s H] S.boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  let _c0 := NontrivialBoundary.pullbackWithNontrivialBoundary S q
  have : Flat q := inferInstance
  have hsm :=
    BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar S hV s s.length le_rfl
  let _a2 := strictTransformAtLength s' $ cmI H q
  have hft1 : _a2
      = (cmI (strictTransformAtLength s H) Dt.lastMap) :=
    strictTransformAtLength_comap_lastMap S q s s' Dt hstar hV hV' H
  have hlist :=
    congrArg (fun Z => [Z]) hft1.symm
  have e1 : ((derivedTriple S s hftS [strictTransformAtLength s H]
        (bLen S)).pullbackAlong (s'.obj s'.length)
      (Dt.lastMap ≫ tMp (derivedTriple S s hftS [strictTransformAtLength s H]
        (bLen S))) Dt.lastMap).boundary
      = map (·.comap Dt.lastMap)
        (derivedTriple S s hftS [strictTransformAtLength s H]
          (bLen S)).boundary :=
    pullbackAlong_boundary _ _ _ _
  have e2 := derivedTriple_boundary S s hftS
    [strictTransformAtLength s H] (bLen S)
  have e3 := derivedTriple_boundary _c0 s' hftT
    [_a2] (bLen _c0)
  have hbe : SameNontrivialBoundary
      ((derivedTriple S s hftS [strictTransformAtLength s H]
          (bLen S)).pullbackAlong (s'.obj s'.length)
        (Dt.lastMap ≫ tMp (derivedTriple S s hftS [strictTransformAtLength s H]
          (bLen S))) Dt.lastMap).boundary
      (derivedTriple _c0 s' hftT
        [strictTransformAtLength s' (cmI H q)]
        (bLen _c0)).boundary := by
    rw [e1, e2, e3, hft1]
    exact NontrivialBoundary.sameNontrivialBoundary_cons $ NontrivialBoundary.sameNontrivialBoundary_symm (NontrivialBoundary.sameNontrivialBoundary_lastBoundary_drop S q s s' Dt hstar hV hV')
  have htake : List.take (0 + 1)
        (derivedTriple _c0 s' hftT
          [strictTransformAtLength s' (cmI H q)]
          (bLen _c0)).boundary
      = List.take (0 + 1)
        ((derivedTriple S s hftS [strictTransformAtLength s H]
            (bLen S)).pullbackAlong (s'.obj s'.length)
          (Dt.lastMap ≫ tMp (derivedTriple S s hftS [strictTransformAtLength s H]
            (bLen S))) Dt.lastMap).boundary := by
    have t := congrArg (fun Z => [Z]) hft1
    rwa [e1, e2, e3]
  have hjU : 0 < (derivedTriple S s hftS [strictTransformAtLength s H]
      S.boundary.length).boundary.length := by
    rw [e2]
    simp
  have hjU' : 0 < (derivedTriple _c0 s' hftT
      [strictTransformAtLength s' (cmI H q)]
      _c0.boundary.length).boundary.length := by
    rw [e3]
    simp
  have hOU := isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS
    [strictTransformAtLength s H] S.boundary.length hVU
  have hDU := isBalanced_derivedTriple hstar S hV hm hO s hftS
    [strictTransformAtLength s H] S.boundary.length hVU
  have hOU' := isOrderBoundedByMult_derivedTriple hstar _c0 hV' hm hO' s'
    hftT [_a2]
    _c0.boundary.length hVU'
  have hpb := NontrivialBoundary.pullbackAlong_derivedTriple_eq S q s s' Dt hstar hV hV' hftS hftT hsm
    [strictTransformAtLength s H] (bLen S)
    (bLen _c0)
  have hEb :=
    (congrArg (fun L => append L
      (List.drop (bLen _c0) $ s'.boundary s'.length))
      hlist).trans e3.symm
  have hEqLast :=
    ((congrArg (fun L =>
        ((derivedTriple S s hftS [strictTransformAtLength s H]
            (bLen S)).pullbackAlong (s'.obj s'.length)
          (Dt.lastMap ≫ tMp (derivedTriple S s hftS [strictTransformAtLength s H]
            (bLen S))) Dt.lastMap).withBoundary L) hEb).symm.trans hpb).trans
      (congrArg (fun E => derivedTriple _c0 s' hftT E
        (bLen _c0)) hlist)
  have hVtr : ∀ W : MarkedIdealWithBoundary,
      W = derivedTriple _c0 s' hftT
        [strictTransformAtLength s' (cmI H q)]
        (bLen _c0) → tAd W := by
    intro W hW
    subst hW
    exact hVU'
  have hPtr : ∀ W : MarkedIdealWithBoundary,
      W = derivedTriple _c0 s' hftT
        [strictTransformAtLength s' (cmI H q)]
        (bLen _c0) → P W.krullDimSucc := by
    intro W hW
    subst hW
    exact hPU'
  have hOtr : ∀ W : MarkedIdealWithBoundary,
      W = derivedTriple _c0 s' hftT
        [strictTransformAtLength s' (cmI H q)]
        (bLen _c0) → W.IsOrderBoundedByMult := by
    intro W hW
    subst hW
    exact hOU'
  have hjtr : ∀ W : MarkedIdealWithBoundary,
      W = derivedTriple _c0 s' hftT
        [strictTransformAtLength s' (cmI H q)]
        (bLen _c0) → 0 < bLen W := by
    intro W hW
    subst hW
    exact hjU'
  have hDtr : ∀ W : MarkedIdealWithBoundary,
      W = derivedTriple _c0 s' hftT
        [strictTransformAtLength s' (cmI H q)]
        (bLen _c0) →
      ∀ hft, W.IsBalanced hft := by
    intro W hW hft
    subst hW
    exact isBalanced_derivedTriple hstar _c0 hV' hm hO' s' hftT
      [_a2]
      _c0.boundary.length hVU'
  have inner0 := @IsBoundaryDivisorReduction.smooth_pullback P 0 (A 0) Bl hspec
    (derivedTriple S s hftS [strictTransformAtLength s H] (bLen S))
    hVU hPU hOU hDU hjU (s'.obj s'.length)
    (Dt.lastMap ≫ tMp (derivedTriple S s hftS [strictTransformAtLength s H]
      (bLen S))) Dt.lastMap (SequenceOfBlowupsPullback.smooth_lastMap Dt) rfl
    (derivedTriple _c0 s' hftT
      [strictTransformAtLength s' (cmI H q)]
      (bLen _c0)).boundary
    hbe htake (hVtr _ hEqLast) (hPtr _ hEqLast) (hOtr _ hEqLast) (hDtr _ hEqLast _)
    (hjtr _ hEqLast)
  have hp :=
    (congrArg (fun mm => Dt.lastMap ≫ mm)
        (derivedTriple_structureMorphism S s hftS
          [strictTransformAtLength s H] (bLen S))).trans
      (tr_ (NontrivialBoundary.lastMap_comp_structureMorphism S q s s' Dt)
        (derivedTriple_structureMorphism _c0 s' hftT
          [_a2]
          (bLen _c0)).symm)
  have hI :=
    (congrArg (·.comap Dt.lastMap)
        (ideal_derivedTriple S s hftS
          [strictTransformAtLength s H] (bLen S))).trans
      (tr_ (NontrivialBoundary.tunedIdealAtLength_comap_lastMap S q s s' Dt hstar hV hV' hftS hftT hsm)
        (ideal_derivedTriple _c0 s' hftT
          [_a2]
          (bLen _c0)).symm)
  have hm2 :=
    (derivedTriple_mult S s hftS
        [strictTransformAtLength s H] (bLen S)).trans
      (derivedTriple_mult _c0 s' hftT
        [_a2]
        (bLen _c0)).symm
  have inner :=
    isPullbackBlowupSequence_congr (A 0) _ _ _ _ Dt.lastMap _ _ _ _ _ _ _ _ hp hI hm2 rfl inner0
  have hjlist : 0 < ([strictTransformAtLength s H] ++
      (s.boundary s.length).drop (bLen S)).length := by simp
  have hjlist' : 0 < ([_a2] ++
      (s'.boundary s'.length).drop (bLen _c0)).length := by simp
  obtain ⟨hmk, heq, -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A Bl 0 hspec
    (fun S0 _ i => A i S0) (fun _ _ _ => rfl) S hV hm hO s
    [strictTransformAtLength s H] S.boundary.length hftS hdimU hPU hVU hjlist
    (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated S s S.boundary.length hsep)
  obtain ⟨hmk', heq', -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A Bl 0 hspec
    (fun S0 _ i => A i S0) (fun _ _ _ => rfl) _c0 hV' hm hO' s'
    [_a2] (bLen _c0)
    hftT hdimU' hPU' hVU' hjlist'
    (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated _c0 s'
      _c0.boundary.length hsep')
  rw [heq, heq']
  exact isPullbackBlowupSequence_append_of_two_fields q s _ s' _ hinv Dt
    (inner.nonempty_sequenceOfBlowupsPullback.some.toBlowupDataOfSeq)

end StrictTransformComparison





def IsSmoothDivisorStableUnderSmoothPullback : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (P Y : Sch)
    (p : P ⟶ Sp k) [Smooth p]
    [LocallyOfFiniteType p]
    (g : Y ⟶ P) [Smooth g]
    [LocallyOfFiniteType $ g ≫ p]
    (D : ISD P), IsSmoothDivisor p D → IsSmoothDivisor (g ≫ p) (comap D g)

section
variable {P Y : Sch} (g : Y ⟶ P)
theorem restrictIdeal_comap_eq_comap_restrictIdeal
    (I : ISD P) {U : Opn P} {V : Opn Y} {f}
    (hf : f ≫ ι U = ι V ≫ g) :
    restrictIdeal (comap I g) V = comap (restrictIdeal I U) f := by
  rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
    ← comap_comp, hf]

theorem restrictIdeal_comap_le_of_restrictIdeal_le
    {I J : ISD P} {U : Opn P}
    (hle : restrictIdeal I U ≤ restrictIdeal J U) (V : Opn Y) (hV : V ≤ pre g U) :
    restrictIdeal (comap I g) V ≤ restrictIdeal (comap J g) V := by
  have hf : (Y.homOfLE hV ≫ mrU g U) ≫ opI U = opI V ≫ g := by simp_all
  rw [restrictIdeal_comap_eq_comap_restrictIdeal g I hf,
    restrictIdeal_comap_eq_comap_restrictIdeal g J hf]
  exact comap_mono _ hle
end

section
variable {k : Type} [Field k] [CharZero k]
theorem IsMaxContactHypersurface.isSmoothDivisor
    {P : Sch} {p : P ⟶ Sp k} [Smooth p]
    [LocallyOfFiniteType p] {A : ISD P} {mu_ : ℕ}
    {H : ISD P} (h : IsMaxContactHypersurface k p A mu_ H) :
    IsSmoothDivisor p H := by
  refine isSmoothDivisor_of_locally_coordIdeal H ?_
  intro x
  obtain ⟨U, hU, hxU, hcase⟩ := h x
  rcases hcase with ⟨-, htop⟩ | ⟨n, c, j, hHU, -⟩
  obtain ⟨U', m, hxU', hU'U, -, ⟨c'⟩⟩ := exists_etaleChart_le p x U hxU
  exact ⟨U', hxU', m, c', inl $ restrictIdeal_eq_top_of_le H hU'U htop⟩
  exact ⟨U, hxU, n, c, inr ⟨j, hHU⟩⟩

section
variable {P Y : Sch} {p} [Smooth p] [LocallyOfFiniteType p] (g : Y ⟶ P) [Smooth g] [LocallyOfFiniteType (g ≫ p)] {A : ISD P} {mu_ : ℕ} {H : ISD P}
theorem IsMaxContactHypersurface.comap_of_forall_etaleChart_coordIdeal (h : IsMaxContactHypersurface k p A mu_ H) (hmu_ : 1 ≤ mu_)
    (hcharts : ∀ y : Y, y ∈ support (comap H g) →
      ∃ (V : Opn Y) (n : ℕ) (c : EtaleChart (g ≫ p) V n) (j : Fin n),
        y ∈ V ∧ restrictIdeal (comap H g) V = c.coordIdeal {j}) :
    IsMaxContactHypersurface k (g ≫ p) (comap A g) mu_ $ comap H g := by
  let _a0 := spI $ cmI H g
  intro y
  by_cases hy : y ∈ _a0
  obtain ⟨V, n, c, j, hyV, hHV⟩ := hcharts y hy
  obtain ⟨U, hU, hxU, hcase⟩ := h $ bsM g y
  have hle : restrictIdeal H U ≤ restrictIdeal (maxContactIdeal k p A mu_) U := by
    rcases hcase with ⟨-, htop⟩ | ⟨n0, c0_, j0_, hHU, hmc⟩
    exact absurd (mp_ (mem_support_comap ..) hy) $ notMem_support_of_mem_opens_of_restrictIdeal_eq_top H U htop _ hxU
    rwa [hHU]
  have hyVU : y ∈ (V ⊓ preU g U : Opn Y) := ⟨hyV, hxU⟩
  obtain ⟨V', hV'aff, hyV', hV'le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hyVU
  have hV'V := le_trans hV'le inf_le_left
  have heq :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c (cmI H g) {j} hHV
  refine ⟨V', hV'aff, hyV', inr ⟨n, c.restrict hV'V, j, heq, ?_⟩⟩
  have hgoal : (c.restrict hV'V).coordIdeal {j} ≤
      restrictIdeal (maxContactIdeal k (g ≫ p) (cmI A g) mu_) V' := by
    have _x1 : maxContactIdeal k (g ≫ p) (cmI A g) mu_ = cmI (maxContactIdeal k p A mu_) g := by
      unfold maxContactIdeal
      exact derivIdealSheafIterate_comap k p g (mu_ - 1) A
    rw [← heq, _x1]
    exact restrictIdeal_comap_le_of_restrictIdeal_le g hle V' $ le_trans hV'le inf_le_right
  exact hgoal
  have hWopen :=
    _a0.2.isOpen_compl
  obtain ⟨V, hVaff, hyV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show y ∈ (⟨(_a0 : Set Y)ᶜ, hWopen⟩ : Opn Y) from hy)
  refine ⟨V, hVaff, hyV, inl ⟨?_, ?_⟩⟩
  rw [disjoint_left]
  intro z hz hzV
  have hz2 := hz
  rw [orderAtLeastLocus_comap k p g A mu_] at hz2
  exact (hVW hzV) $ mpr (mem_support_comap ..) $ h.orderAtLeastLocus_subset_support hmu_ hz2
  refine mpr_ (restrictIdeal_eq_top_iff_forall_notMem_support _ _) ?_
  intro z hzV
  exact hVW hzV

theorem IsMaxContactHypersurface.comap_of_isSmoothDivisorStableUnderSmoothPullback
    (hdiv : IsSmoothDivisorStableUnderSmoothPullback)
    (hH : IsSmoothDivisor p H)
    (h : IsMaxContactHypersurface k p A mu_ H) (hmu_ : 1 ≤ mu_) :
    IsMaxContactHypersurface k (g ≫ p) (comap A g) mu_ $ comap H g := by
  refine IsMaxContactHypersurface.comap_of_forall_etaleChart_coordIdeal g h hmu_ ?_
  intro y hy
  obtain ⟨V, m, c, j, hyV, heq⟩ :=
    exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton (g ≫ p) (cmI H g)
      (hdiv k P Y p g H hH) y hy
  exact ⟨V, m, c, j, hyV, heq⟩
end
end





namespace OrderReduction

def ValidPullbackAlongSmooth : Prop :=
  ∀ (T : MarkedIdealWithBoundary), IsAdmissible T → ∀ (Y : Sch)
      (q : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
      [Smooth h] [QuasiCompact q],
      h ≫ structMap T = q → IsAdmissible (T.pbA q h)

theorem validPullbackAlongSmooth_iff :
    ValidPullbackAlongSmooth ↔
      ∀ (T : MarkedIdealWithBoundary), IsAdmissible T → ∀ (Y : Sch)
        (q : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
        [Smooth h] [QuasiCompact q],
        h ≫ structMap T = q → IsAdmissible (T.pbA q h) :=
  m22

end OrderReduction

namespace MaxContactCoverData

private theorem support_pow_subset {X : Sch} (I : ISD X) (s : ℕ) :
    (support (I ^ s) : Set ↥X) ⊆ (support I : Set ↥X) := by
  intro x hx
  simp [SetLike.mem_coe] at hx ⊢
  rw [mem_support_iff_stalkIdeal_ne_top] at hx ⊢
  intro hI
  apply hx
  rw [stalkIdeal_pow, hI, Ideal.top_pow]

theorem prod_map_range_pow_ite_eq_pow {X : Sch} (A : ℕ → ISD X) (n s : ℕ) :
    (map (fun j => A j ^ (if j = n then s else 0)) $ range $ n + 1).prod = A n ^ s := by
  have h1 : (map (fun j => A j ^ (if j = n then s else 0)) $ range n).prod = 1 := by
    apply prod_eq_one
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [if_neg $ Nat.ne_of_lt hj, pow_zero]
  rw [List.range_succ, m144, List.prod_append, h1, one_mul]
  simp

theorem exists_le_and_pow_le_tunedSheaf (k : Type) [Field k] [IsNoetherianRing k]
    {X : Sch} (p : X ⟶ Sp k)
    [LocallyOfFiniteType p] (I : ISD X) (m s : ℕ) (hm : 1 ≤ m) :
    ∃ J : ISD X, I ≤ J ∧ J ^ s ≤ tunedSheaf k p I m s := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨derivIdealSheafIterate k p n I, le_derivIdealSheafIterate k p n I, ?_⟩
  let _m0 := ∑ j ∈ m65 (n + 1), (n + 1 - j) * (if j = n then s else 0)
  have h0 : _m0
      = (n + 1 - n) * (if n = n then s else 0) := by
    exact Finset.sum_eq_single n (fun b _ hb => by simp [hb]) fun h => absurd (Finset.mem_range.2 $ lt_succ_self n) h
  have hsum : _m0 = s := by simp_all
  have h := prod_pow_derivIdealSheafIterate_le_tunedSheaf k p I (n + 1) s
    (if · = n then s else 0) hsum.ge
  rwa [prod_map_range_pow_ite_eq_pow] at h

section
variable (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)
theorem balancedTunedIdeal_eq_balancedTunedSheaf
    [LocallyOfFiniteType T.structMap] :
    balancedTunedIdeal T hv = balancedTunedSheaf T.base T.structMap T.ideal T.mult :=
  rfl

theorem nonzeroOnComponents_balancedTunedIdeal :
    NonzeroOnComponents $ balancedTunedIdeal T hv := by
  have := hv.locallyOfFiniteType
  obtain ⟨J, hIJ, hJ⟩ :=
    exists_le_and_pow_le_tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) hv.one_le_mult
  have hle := hJ
  rw [← balancedTunedSheaf_eq, ← balancedTunedIdeal_eq_balancedTunedSheaf T hv] at hle
  have hnz := hv.nonzeroOnComponents
  rw [nonzeroOnComponents_iff] at hnz ⊢
  intro C hC hsub
  refine hnz C hC ?_
  intro x hx
  exact SetLike.coe_subset_coe.2 (support_antitone hIJ) $ support_pow_subset J (tuningExponent T.mult) $ SetLike.coe_subset_coe.2 (support_antitone hle) $ hsub hx
end

theorem orderAt_balancedTunedIdeal_le_tunedMult (htf : TunedSheafProperties) (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat)) x :
    orderAt (balancedTunedIdeal T hv) x ≤ ((tunedMult T : ℕ) : ENat) := by
  have := hv.locallyOfFiniteType
  have := hv.charZero
  have := hv.smooth
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  have htop : balancedTunedIdeal T hv = ⊤ := by
    rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv]
    exact balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty T.base T.structMap T.ideal hv.one_le_mult hemp
  rw [htop, orderAt_top]
  simp
  have hmax : MaxOrderEq T.ideal T.mult :=
    ⟨(orderLE_iff T.ideal T.mult).2 hord, nonempty_iff_ne_empty.2 hemp⟩
  have hLE := htf.coSupport_tunedSheaf_eq_and_orderLE.orderLE T.base T.scheme T.structMap
    T.ideal T.mult hv.one_le_mult hmax (tuningExponent T.mult) $ one_le_tuningExponent T.mult
  rw [orderLE_iff] at hLE
  rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv, balancedTunedSheaf_eq]
  exact hLE x

theorem isAdmissible_coverTriple_of_validPullbackAlongSmooth (hpb : OrderReduction.ValidPullbackAlongSmooth)
    (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)
    (hgood : IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) $ tunedMult T) :
    IsAdmissible $ cT hv := by
  rw [MaxContactOpenCover.coverTriple_eq_tunedTriple_pullbackAlong T hv]
  exact @hpb (MaxContactOpenCover.tunedTriple T hv) (MaxContactOpenCover.isAdmissible_tunedTriple T hv $ nonzeroOnComponents_balancedTunedIdeal T hv) (chosenCoverData T hv).disjointUnion
    (coverMap T hv ≫ tMp T) (coverMap T hv) (instSmoothCoverMap T hv) (MaxContactOpenCover.quasiCompact_coverMap_comp_structureMorphism T hv hgood) rfl

theorem isSmoothDivisor_coverMaxContactIdeal (_hpb : OrderReduction.ValidPullbackAlongSmooth)
    (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)
    (hgood : IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) $ tunedMult T) :
    IsSmoothDivisor (cT hv).structMap $ cI hv := by
  refine isSmoothDivisor_of_locally_coordIdeal (cI hv) ?_
  intro x
  obtain ⟨U, hxU, m, c, a, _hinj, hnone, hsome⟩ :=
    (MaxContactCoverGeometry.inStrictNormalCrossingPositionAt_of_isMaxContactCover T hv hgood x).exists_etaleChart
  refine ⟨U, hxU, m, c, ?_⟩
  rcases ha : a 0 with _ | t
  exact m51 $ hnone 0 (Nat.zero_lt_one) ha
  exact m61 ⟨t, hsome 0 (Nat.zero_lt_one) t ha⟩

end MaxContactCoverData

namespace OrderReduction

end OrderReduction





namespace TrivialDivisorContinuation

theorem hom_apply_congr {A B : Sch} {f g : A ⟶ B} (h : f = g) (x : ↥A) : f x = g x := by
  subst h
  rfl

section
variable {A : Sch} {M : ISD A}
theorem mem_support_of_eq {x y : ↥A} (h : x = y)
    (hx : y ∈ support M) : x ∈ support M := by
  subst h
  exact hx

theorem notMem_support_of_eq_top (h : M = ⊤)
    (x : ↥A) : x ∉ support M := by
  intro hx
  have hx' : x ∈ (support M : Set A) := hx
  rwa [mp (eq_top_iff_support_eq_empty M) h] at hx'
end

theorem false_of_mem_support_comp_comp {X' Y W Z Z' : Sch} (q : X' ⟶ Y)
    (pr : W ⟶ Y) (M : ISD W)
    (hImageDisjoint : ∀ y : ↥W, y ∈ support M → ∀ x : ↥X', q x ≠ pr y)
    (g : Z ⟶ Z') (h : Z' ⟶ W) (z : ↥Z) (x : ↥X') (hx : q x = (g ≫ (h ≫ pr)) z)
    (hz : h (g z) ∈ support M) : False :=
  hImageDisjoint (h $ g z) hz x hx

theorem false_of_mem_support_comp {X' Y W Z : Sch} (q : X' ⟶ Y) (pr : W ⟶ Y)
    (M : ISD W)
    (hImageDisjoint : ∀ y : ↥W, y ∈ support M → ∀ x : ↥X', q x ≠ pr y)
    (g : Z ⟶ W) (z : ↥Z) (x : ↥X') (hx : q x = (g ≫ pr) z)
    (hz : g z ∈ M.support) : False :=
  hImageDisjoint (g z) hz x hx

theorem projectionToBase_zero_isoObjZero_inv_apply {W : Sch} (n : BlowupSequenceData W) (w : ↥W) :
    (n.projectionToBase 0) (n.isoZero.inv w) = w :=
  (hom_apply_congr (p23 n) $ n.isoZero.inv w).trans
    (Scheme.inv_hom_apply n.isoZero w)

theorem nonempty_pullback_appendLowerDimReduction_of_comap_eq_top
    (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) (j1 : ℕ)
    (S : MarkedIdealWithBoundary) {X' : Sch} (q : X' ⟶ S.scheme) [Smooth q]
    (s : S.mbs)
    (s' : MarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary)
    (D : SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hft : LocallyOfFiniteType $ s.proj s.length ≫ S.structMap)
    (hstar : MaxContactCoverProperties) (hspec : IsBoundaryDivisorReduction P j1 (A j1) B)
    (hV : S.IsAdmissible) (hm : 1 ≤ S.mult)
    (hO : ∀ x : S.scheme, orderAt S.ideal x ≤ (S.mult : ENat))
    (hP : P (derivedTriple S s hft [] 0).krullDimSucc)
    (hVc : (derivedTriple S s hft [] 0).IsAdmissible)
    (hj : j1 < (s.boundary s.length).length)
    (hComapTop : (get (s.boundary s.length) ⟨j1, hj⟩).comap D.lastMap = ⊤)
    (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (hdim : (derivedTriple S s hft [] 0).krullDimSucc ≤ T.krullDimSucc) :
    Nonempty $ SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendLowerDimReduction hinv T (fun S' _ i => A i S') S s [] 0
        j1).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  classical
  set Dj := get (lastB s) ⟨j1, hj⟩ with hDtopDef
  have hImageDisjoint : ∀ y : (lastO s), y ∈ spI Dj →
      ∀ x'', q x'' ≠ (s.toBlowupSequenceData.projectionToBase s.length) y := by
    intro y hy x'' hxy
    obtain ⟨w, hw1, -⟩ :=
      m198 y x'' ((hom_apply_congr (toSequenceOfBlowups_projectionToBase s.toBlowupSequenceData s.length) y).trans hxy.symm)
    exact notMem_support_of_eq_top hComapTop _ $ Scheme.IdealSheafData.mem_support_comap.mpr $ mem_support_of_eq ((hom_apply_congr D.isPullback_lastMap.isoPullback_inv_fst w).trans hw1) hy
  have hj' : j1 < (derivedTriple S s hft [] 0).boundary.length := by simp_all
  have hget : (derivedTriple S s hft [] 0).boundary.lget j1 hj' = Dj := by simp_all
  obtain ⟨Dv, bb, -, hD0, hcen, hbtrue, hstrictD, -, -⟩ :=
    hspec.shape (derivedTriple S s hft [] 0) hVc hP (isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hft [] 0 hVc) (isBalanced_derivedTriple hstar S hV hm hO s hft [] 0 hVc) hj'
  let _a0 := A j1 $ derivedTriple S s hft [] 0
  have hInduction : ∀ r,
      r ≤ _a0.length →
      ∀ z : (_a0.schemeAt r),
        z ∈ spI (Dv r) →
        (_a0.projectionToBase r) z
          ∈ spI Dj := by
    intro r
    induction r with
    | zero =>
      intro _ z hz
      rw [hD0] at hz
      dsimp only [bget, lget] at hget hz
      rw [hget] at hz
      exact mem_support_of_eq (hom_apply_congr (projectionToBase_zero _) z)
        (Scheme.IdealSheafData.mem_support_comap.mp hz)
    | succ r ih =>
      intro hr z hz
      have hrlt := hr
      have hmem : (_a0.transitionMapSucc r) z
          ∈ spI (Dv r) := by
        by_cases hc : bb = true ∧ r = 0
        obtain ⟨hb1, hb2⟩ := hc
        subst hb2
        obtain ⟨-, -, hD1⟩ := hbtrue hb1
        have hz' := hz
        rw [hD1] at hz'
        exact Scheme.IdealSheafData.mem_support_comap.mp hz'
        rw [hstrictD r hrlt hc] at hz
        exact support_strictTransform_subset_preimage _ _ _ hz
      exact mem_support_of_eq (hom_apply_congr (projectionToBase_succ _ r) z) $ ih (le_of_lt hrlt) _ hmem
  have hcent : ∀ nn : BlowupSequenceData $ lastO s,
      nn = ofSequenceOfBlowups
        _a0.toSequenceOfBlowups →
      ∀ r (z : (nn.obj r)), z ∈ spI (nn.center r) → r < nn.length →
        (nn.projectionToBase r) z ∈ spI Dj := by
    rintro nn rfl r z hz hr
    have hr' := hr
    exact mem_support_of_eq (hom_apply_congr (ofSequenceOfBlowups_projectionToBase
      _a0.toSequenceOfBlowups r) z) $ hInduction r (le_of_lt hr') z $ hcen r hr' hz
  have c : SequenceOfBlowupsPullback q s'.toSequenceOfBlowups s.toSequenceOfBlowups := by
    rw [← toMarkedSequence_toSequenceOfBlowups s,
        ← toMarkedSequence_toSequenceOfBlowups s']
    exact D
  have hcd := fun tt =>
    congrArg toSequenceOfBlowups
      (tr_ (append_toBlowupSequenceData s tt hinv) rfl)
  have main : ∀ (tt : MarkedBlowupSequenceData (lastP s ≫ tMp S)
        (lastI s) S.mult $ lastB s),
      tt.toBlowupSequenceData = ofSequenceOfBlowups
        _a0.toSequenceOfBlowups →
      Nonempty (SequenceOfBlowupsPullback q s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups
        (s.append tt hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro tt htt
    have hcn := hcent tt.toBlowupSequenceData htt
    rw [toMarkedSequence_toSequenceOfBlowups s',
        toMarkedSequence_toSequenceOfBlowups $ s.append tt hinv, hcd tt]
    refine FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPullback.nonempty_append_of_disjoint_centers q s'.toBlowupSequenceData s.toBlowupSequenceData
      tt.toBlowupSequenceData c ?_
    intro i hi1 hi2 z hz x'' hx
    rcases eq_or_lt_of_le hi1 with he | hlt
    subst he
    rw [append_center_length] at hz
    rw [projectionToBase_append_of_le_length _ _ $ le_refl _] at hx
    have hz1 := Scheme.IdealSheafData.mem_support_comap.mp hz
    have hy := hcn 0 _ (Scheme.IdealSheafData.mem_support_comap.mp hz1) $ by omega
    exact false_of_mem_support_comp q (s.toBlowupSequenceData.projectionToBase s.length) Dj hImageDisjoint _ z x'' hx
      (mem_support_of_eq (projectionToBase_zero_isoObjZero_inv_apply _ _).symm hy)
    rw [append_center_of_length_lt _ _ hlt] at hz
    rw [projectionToBase_append_of_length_lt _ _ hlt] at hx
    have hz1 := Scheme.IdealSheafData.mem_support_comap.mp hz
    have hy := hcn (i - s.toBlowupSequenceData.length) _ hz1 $ by omega
    exact false_of_mem_support_comp_comp q (s.toBlowupSequenceData.projectionToBase s.length) Dj hImageDisjoint _
      (tt.toBlowupSequenceData.projectionToBase $ i - mbsLen s) z x'' hx hy
  obtain ⟨hmk, heq, -⟩ := appendLowerDimReduction_eq_append hstar hinv T P A B j1 hspec
      (fun S' _ i => A i S') (fun _ _ _ => rfl) S hV hm hO s [] 0 hft hdim hP hVc
      (by simpa using hj) fun Dx hDx => orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero S s Dx hDx
  rw [heq]
  exact main _ $ toMarkedBlowupSequenceData_toBlowupSequenceData _ _ _ _ _ _

end TrivialDivisorContinuation





namespace NontrivialBoundary

section
variable (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment) (Bl : PrincipalizationAssignment) (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl) (hshift : IsBoundaryPositionInvariant P A) (hstar : MaxContactCoverProperties) (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary) (hPdimT : P T.krullDimSucc) (S : MarkedIdealWithBoundary) {X' : Sch} (q : X' ⟶ scheme S) [Smooth q] (hV : IsAdmissible S) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc) (hV' : IsAdmissible (NontrivialBoundary.pullbackWithNontrivialBoundary S q)) (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc) (j : ℕ) (hj : j ≤ S.boundary.length)
include hmono hspec hshift hstar hPdimT hV hO hdimS hV' hdim' hj
theorem nonempty_separateBoundaryPullbackComparison :
    Nonempty $ SequenceOfBlowupsPullback q
      (separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (separateBoundaryOfFamily hinv T A S j).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  let _c0 := NontrivialBoundary.pullbackWithNontrivialBoundary S q
  classical
  have : Flat q := inferInstance
  revert hj
  induction j with
  | zero =>
    intro _
    have e0 : separateBoundaryOfFamily hinv T A S 0
        = S.embs :=
      separateBoundary_zero hinv T (fun S0 _ i => A i S0) S
    have e0' : separateBoundaryOfFamily hinv T A _c0
          (NontrivialBoundary.survivingBoundaryCount S q 0)
        = _c0.embs := by simp_all
    rw [e0, e0']
    simp [toMarkedSequence_toSequenceOfBlowups]
    refine ⟨SequenceOfBlowupsPullback.ofCentersMissImage q _ ?_ _ ?_⟩
    simp_all
    simp
  | succ j ih =>
    intro hj1
    have hjS : j < bLen S := lt_of_succ_le hj1
    obtain ⟨D⟩ := ih $ Nat.le_of_succ_le hj1
    have hftS : AlgebraicGeometry.LocallyOfFiniteType
        ((separateBoundaryOfFamily hinv T A S j).proj
            (separateBoundaryOfFamily hinv T A S j).length ≫ tMp S) :=
      BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV _ _ le_rfl
    have hftT : LocallyOfFiniteType
        ((separateBoundaryOfFamily hinv T A _c0
              (NontrivialBoundary.survivingBoundaryCount S q j)).proj
            (separateBoundaryOfFamily hinv T A _c0
              (NontrivialBoundary.survivingBoundaryCount S q j)).length
          ≫ tMp _c0) :=
      BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar _c0 hV'
        _ _ le_rfl
    have hm := hV.one_le_mult
    have hdimU :=
      hstar.derivedTriple_dim_le (T := T) hV (separateBoundaryOfFamily hinv T A S j) hftS [] 0 hdimS
    have hPU :=
      hmono _ _ hdimU hPdimT
    have hVU := isAdmissible_derivedTriple_nil hstar S hV
      (separateBoundaryOfFamily hinv T A S j) hftS
    have hdimU' :=
      hstar.derivedTriple_dim_le (T := T) hV'
        (separateBoundaryOfFamily hinv T A _c0
          (NontrivialBoundary.survivingBoundaryCount S q j))
        hftT [] 0 hdim'
    have hPU' :=
      hmono _ _ hdimU' hPdimT
    have hVU' := isAdmissible_derivedTriple_nil hstar _c0 hV'
      (separateBoundaryOfFamily hinv T A _c0
        (NontrivialBoundary.survivingBoundaryCount S q j))
      hftT
    have hO' : ∀ x,
        orderAt _c0.ideal x ≤ ((tMu S : ℕ) : ENat) :=
      fun x => orderAt_pullbackTriple_le_mult S q hV hO x
    have eS : separateBoundaryOfFamily hinv T A S (j + 1)
        = appendLowerDimReduction hinv T (fun S0 _ i => A i S0) S
            (separateBoundaryOfFamily hinv T A S j) [] 0 j :=
      separateBoundary_succ hinv T (fun S0 _ i => A i S0) S j
    by_cases hlive : cmI (S.boundary[j]'hjS) q = ⊤
    have eT : NontrivialBoundary.survivingBoundaryCount S q (j + 1) = NontrivialBoundary.survivingBoundaryCount S q j :=
      NontrivialBoundary.survivingBoundaryCount_succ_of_eq_top S q j hjS hlive
    rw [eS, eT]
    refine TrivialDivisorContinuation.nonempty_pullback_appendLowerDimReduction_of_comap_eq_top P A Bl j S q
      (separateBoundaryOfFamily hinv T A S j)
      (separateBoundaryOfFamily hinv T A _c0
        (NontrivialBoundary.survivingBoundaryCount S q j))
      D hftS hstar (hspec j) hV hm hO hPU hVU (lt_of_lt_of_le hjS $ NontrivialBoundary.length_boundary_le_length_lastBoundary S $ separateBoundaryOfFamily hinv T A S j) ?_ hinv T hdimU
    dsimp only [lget]
    rw [get_eq_getElem]
    exact NontrivialBoundary.lastBoundary_comap_lastMap_eq_top S q
      (separateBoundaryOfFamily hinv T A S j)
      (separateBoundaryOfFamily hinv T A _c0
        (NontrivialBoundary.survivingBoundaryCount S q j)) D hstar hV hV' j hjS hlive
    have eT : separateBoundaryOfFamily hinv T A _c0
          (NontrivialBoundary.survivingBoundaryCount S q $ j + 1)
        = appendLowerDimReduction hinv T (fun S0 _ i => A i S0) _c0
            (separateBoundaryOfFamily hinv T A _c0
              (NontrivialBoundary.survivingBoundaryCount S q j)) [] 0 (NontrivialBoundary.survivingBoundaryCount S q j) := by
      rw [NontrivialBoundary.survivingBoundaryCount_succ_of_ne_top S q j hjS hlive]
      exact separateBoundary_succ hinv T (fun S0 _ i => A i S0)
        _c0 $ NontrivialBoundary.survivingBoundaryCount S q j
    rw [eS, eT]
    exact ⟨BoundaryDeletion.continuationComparison (P := P) (A := A) (Bl := Bl) (j := j) (S := S)
      (q := q) (s := separateBoundaryOfFamily hinv T A S j)
      (s' := separateBoundaryOfFamily hinv T A _c0
        (NontrivialBoundary.survivingBoundaryCount S q j))
      (Dt := D) (hftS := hftS) (hftT := hftT) (hinv := hinv) (T := T)
      (hstar := hstar) (hspec := hspec j) (hspec' := hspec $ NontrivialBoundary.survivingBoundaryCount S q j)
      (hshift := hshift) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
      (hj := hjS) (hlive := hlive) (hPU := hPU) (hVU := hVU) (hPU' := hPU') (hVU' := hVU')
      (hdimU := hdimU) (hdimU' := hdimU')⟩

def separateBoundaryPullbackComparison :
    SequenceOfBlowupsPullback q
      (separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (separateBoundaryOfFamily hinv T A S j).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
  (nonempty_separateBoundaryPullbackComparison P hmono A Bl hspec hshift hstar hinv T hPdimT S q hV hO hdimS hV' hdim'
    j hj).some
end

end NontrivialBoundary





namespace MaxContactFunctoriality

theorem isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties) (hinv : ComapIsoInvariance)
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment) (Bl : PrincipalizationAssignment)
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (T : MarkedIdealWithBoundary) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : tISD S)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Sch} (q : X' ⟶ scheme S) [Smooth q]
    (hV' : IsAdmissible (NontrivialBoundary.pullbackWithNontrivialBoundary S q))
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (hH' : ∀ [LocallyOfFiniteType (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      IsMaxContactHypersurface (NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (comap H q))
    (hH'snc : InStrictNormalCrossingPosition (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap [comap H q]) :
    IsPullbackBlowupSequence q
      (reduceAlongHypersurface hinv T (fun S0 _ i => A i S0)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (comap H q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (reduceAlongHypersurface hinv T (fun S0 _ i => A i S0) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  let _c0 := p16 hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (bLen (NontrivialBoundary.pullbackWithNontrivialBoundary S q))
  let _c1 := NontrivialBoundary.pullbackWithNontrivialBoundary S q
  let _c2 := p16 hinv T A S (bLen S)
  have Dt0 := NontrivialBoundary.separateBoundaryPullbackComparison P hmono A Bl hspec hshift hstar hinv T hPdimT S q hV hO
    hdimS hV' hdim' S.boundary.length le_rfl
  rw [NontrivialBoundary.survivingBoundaryCount_length_eq S q] at Dt0
  have hftS : LocallyOfFiniteType
      (_c2.proj
        _c2.length ≫ tMp S) :=
    BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV _ _ le_rfl
  have hftT : LocallyOfFiniteType
      (_c0.proj
        _c0.length
        ≫ tMp _c1) :=
    BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar _c1 hV' _ _
      le_rfl
  have hF := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A Bl hspec T hPdimT S
    hV hO hdimS H hHsnc S.boundary.length le_rfl
  have hF' := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A Bl hspec T hPdimT
    _c1 hV' (orderAt_pullbackTriple_le_mult S q hV hO) hdim' (cmI H q)
    hH'snc _c1.boundary.length le_rfl
  have hm : 1 ≤ tMu S := hV.one_le_mult
  have hO' : ∀ x,
      orderAt _c1.ideal x ≤ ((tMu S : ℕ) : ENat) :=
    orderAt_pullbackTriple_le_mult S q hV hO
  have hdimU : tDim (derivedTriple S
      _c2 hftS
      [strictTransformAtLength _c2 H]
      (bLen S)) ≤ tDim T :=
    hstar.derivedTriple_dim_le hV _ hftS _ _ hdimS
  have hPU : P (derivedTriple S
      _c2 hftS
      [strictTransformAtLength _c2 H]
      (bLen S)).krullDimSucc := hmono _ _ hdimU hPdimT
  have hsncU : InStrictNormalCrossingPosition
      (_c2.proj
        _c2.length ≫ tMp S)
      ([strictTransformAtLength _c2 H] ++
        List.drop (bLen S)
          (_c2.boundary
            _c2.length)) := by
    simpa [strictTransformAtLength_eq] using
      inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H (@hH hV.locallyOfFiniteType)
        _c2 hF.2.2 _ le_rfl
  have hVU := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV
    _c2 hftS
    [strictTransformAtLength _c2 H]
    S.boundary.length hsncU
  let _m0 := derivedTriple _c1 _c0 hftT [strictTransformAtLength _c0 (cmI H q)] (bLen _c1)
  have hdimU' : tDim _m0 ≤ tDim T :=
    hstar.derivedTriple_dim_le hV' _ hftT _ _ hdim'
  have hPU' : P _m0.krullDimSucc := hmono _ _ hdimU' hPdimT
  have hsncU' : InStrictNormalCrossingPosition
      (_c0.proj
        _c0.length
        ≫ tMp _c1)
      ([strictTransformAtLength _c0 (cmI H q)] ++
        List.drop (bLen _c1)
          (_c0.boundary
            _c0.length)) := by
    simpa [strictTransformAtLength_eq] using
      inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar _c1 hV'
        (orderAt_pullbackTriple_le_mult S q hV hO) (cmI H q) (@hH' hV'.locallyOfFiniteType)
        _c0 hF'.2.2 _ le_rfl
  have hVU' := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar _c1 hV'
    _c0 hftT
    [strictTransformAtLength _c0 (cmI H q)]
    _c1.boundary.length hsncU'
  have hsep := hF.1
  have hsep' := hF'.1
  simp [reduceAlongHypersurface_eq_appendLowerDimReduction]
  exact StrictTransformComparison.isPullbackBlowupSequence_appendLowerDimReduction (P := P) (A := A) (Bl := Bl) (S := S) (q := q)
    (s := p16 hinv T A S (bLen S))
    (s' := p16 hinv T A _c1
      (bLen _c1))
    (Dt := Dt0) (hftS := hftS) (hftT := hftT) (hinv := hinv) (T := T) (hstar := hstar)
    (hspec := hspec 0) (H := H) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
    (hdimU := hdimU) (hPU := hPU) (hVU := hVU) (hdimU' := hdimU') (hPU' := hPU') (hVU' := hVU')
    (hsep := hsep) (hsep' := hsep')

theorem isPullbackBlowupSequence_reduceAlongHypersurface_lowerDimensionalFamily
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties)
    (_hin : _root_.FunctorialResolution.EmbeddedResolution.OrderReduction.OrderReductionHypotheses)
    (_hMC : _root_.FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned)
    (_hAdm : _root_.FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback)
    (hinv : ComapIsoInvariance)
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment) (Bl : PrincipalizationAssignment)
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (T T' : MarkedIdealWithBoundary) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc)
    (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (_hBoundaryNeTop : ∀ D ∈ S.boundary, D ≠ ⊤)
    (H : tISD S)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Sch} (q : X' ⟶ scheme S) [Smooth q]
    (hV' : IsAdmissible $ NontrivialBoundary.pullbackWithNontrivialBoundary S q)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T'.krullDimSucc)
    (hH' : ∀ [LocallyOfFiniteType (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      IsMaxContactHypersurface (NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult $ comap H q)
    (hH'snc : InStrictNormalCrossingPosition (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap [comap H q]) :
    IsPullbackBlowupSequence q
      (reduceAlongHypersurface hinv T' (lowerDimensionalFamily A T')
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q) $ comap H q).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  rcases le_total T.krullDimSucc T'.krullDimSucc with hle | hle
  rw [reduceAlongHypersurface_congr_of_dim_le hstar hinv A T T' hle S hV hdimS H]
  exact isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth hstar hinv P hmono A Bl hspec hshift T' hPdimOther S hV hO
    (le_trans hdimS hle) H hH hHsnc q hV' hdim' hH' hH'snc
  rw [reduceAlongHypersurface_congr_of_dim_le hstar hinv A T' T hle (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hdim'
    (cmI H q)]
  exact isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth hstar hinv P hmono A Bl hspec hshift T hPdimT S hV hO hdimS
    H hH hHsnc q hV' (le_trans hdim' hle) hH' hH'snc

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

def IsBaseChangeInherited (P : ℕ → Prop) : Prop :=
  ∀ (R : MarkedIdealWithBoundary) (L : Type) [Field L] [CharZero L] (f : R.base →+* L),
    IsAdmissible R → P R.krullDimSucc →
    (∀ x : ↥R.scheme, orderAt R.ideal x ≤ (mult R : ENat)) →
    (∀ hft : LocallyOfFiniteType R.structMap, R.IsBalanced hft) →
      IsAdmissible (bc R f) ∧
      P (bc R f).krullDimSucc ∧
      (∀ x : ↥(bc R f).scheme,
        orderAt (bc R f).ideal x ≤ (mult R : ENat)) ∧
      (∀ hft : LocallyOfFiniteType (bc R f).structMap,
        (bc R f).IsBalanced hft)

theorem MarkedIdealWithBoundary.length_boundary_baseChange (S : MarkedIdealWithBoundary) (L : Type) [Field L]
    (f : S.base →+* L) :
    (bc S f).boundary.length = S.boundary.length := by
  have h : (bcT S f).boundary.length
      = (map (fun D => cmI D $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f)
          S.boundary).length :=
    congrArg List.length $ S.baseChange_boundary L f
  rw [h]
  simp

namespace BoundaryLoopFieldBaseChange

theorem lt_length_nil_append_boundary (S : MarkedIdealWithBoundary)
    (s : S.mbs) j
    (hj : j < S.boundary.length) :
    j < (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0).length := by
  have h2 : (([] : List (s.obj s.length).IdealSheafData) ++ (s.boundary s.length).drop 0).length
      = S.boundary.length + s.length := by
    simp [s.boundary_length s.length le_rfl]
  rw [h2]
  omega

theorem nonempty_strictPullback_of_length_eq_zero {X' X} g
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    Nonempty $ StrictPullbackBlowupSeq g t s :=
  ⟨{ comp := fun i hi =>
        eqToHom (congrArg t.schemeAt $ show i = 0 by omega) ≫ sbIzH t ≫ g ≫ sbIzI s ≫
          eqToHom (congrArg s.schemeAt $ show (0 : ℕ) = i by omega)
     comp_zero := by simp
     pullback := fun i hi => absurd hi $ by omega
     length_eq := by rw [ht, hs]
     center_eq := fun i hi => absurd hi $ by omega }⟩

section
variable {k k' : Type} [Field k] [Field k'] {X X' : Sch} {p : X ⟶ Sp k} {p' : X' ⟶ Sp k'} {I : ISD X} {I' : ISD X'} {m m' : ℕ} {E : Bdy X} {E' : Bdy X'} {g : X' ⟶ X} (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E') (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
include D
private theorem length_eq_of_strictPullbackBlowupSeq :
    t.length = s.length := by
  have h := D.length_eq
  rwa [toMarkedSequence_length, toMarkedSequence_length] at h

def strictPullbackMapAt
    (i : ℕ) (hi : i ≤ t.length) : t.obj i ⟶ s.obj i :=
  D.comp i $ t.le_toSequenceOfBlowups_length hi

theorem strictPullbackMapAt_zero_comp_isoObjZero_hom
    (h0 : 0 ≤ t.length) :
    strictPullbackMapAt s t D 0 h0 ≫ s.isoZero.hom = t.isoZero.hom ≫ g :=
  D.comp_zero
end

theorem iteratedStrictTransform_comap_eqToHom {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedBlowupSequenceData p I m E) (H : ISD X) (a b : ℕ) (hab : a = b)
    (hh : s.obj a = s.obj b) :
    (iteratedStrictTransform s H b).comap (eqToHom hh) = iteratedStrictTransform s H a := by
  subst hab
  simp

section
variable {k k' : Type} [Field k] [Field k'] {X X' : Sch} {p : X ⟶ Sp k} {p' : X' ⟶ Sp k'} {I : ISD X} {I' : ISD X'} {m m' : ℕ} {E : Bdy X} {E' : Bdy X'} {g : X' ⟶ X} (hflat : Flat g) (s : MarkedBlowupSequenceData p I m E) (t : MarkedBlowupSequenceData p' I' m' E') (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups) (hNs : ∀ i ≤ s.length, IsLocallyNoetherian (s.obj i)) (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i)) (H : ISD X)
include hflat hNs hNt
theorem iteratedStrictTransform_comap :
    ∀ i hi,
      iteratedStrictTransform t (H.comap g) i
        = (iteratedStrictTransform s H i).comap (strictPullbackMapAt s t D i hi) := by
  have := hflat
  have hlen := length_eq_of_strictPullbackBlowupSeq s t D
  intro i
  induction i with
  | zero =>
    intro hi
    rw [MaxContactReduction.iteratedStrictTransform_zero, MaxContactReduction.iteratedStrictTransform_zero,
      ← comap_comp, ← comap_comp,
      strictPullbackMapAt_zero_comp_isoObjZero_hom s t D hi]
  | succ i ih =>
    intro hi
    have hlt : i < t.length := hi
    have hle : i ≤ t.length := le_of_lt hlt
    have := hNs (i + 1) (by omega)
    have := hNt (i + 1) (by omega)
    let _s0 := strictPullbackMapAt s t D i hle
    have hflati : Flat _s0 :=
      D.flat_map i (t.le_toSequenceOfBlowups_length hle)
    have := hflati
    let _s1 := strictPullbackMapAt s t D (i + 1) hi
    let _a0 := IsPullback _s1 (t.map i) (s.map i) _s0
    have hsq : _a0 := by
      have key : ∀ (a : t.obj (i + 1) ⟶ t.obj i) (b : s.obj (i + 1) ⟶ s.obj i),
          a = t.map i → b = s.map i →
          IsPullback _s1 a b _s0 →
          _a0 := by
        rintro a b rfl rfl hh
        exact hh
      exact key _ _ (toMarkedSequence_blowupMorphism t i)
        (toMarkedSequence_blowupMorphism s i) (D.pullback i $ t.lt_toSequenceOfBlowups_length hlt)
    let _a1 := cmI (s.center i) _s0
    have hc : t.center i = _a1 := by
      have key : ∀ (a : ISD (t.obj i)) (b : ISD (s.obj i)),
          a = t.center i → b = s.center i →
          a = cmI b _s0 →
          t.center i = _a1 := by
        rintro a b rfl rfl hh
        exact hh
      exact key _ _ (toMarkedSequence_center t i)
        (toMarkedSequence_center s i) (D.center_eq i $ t.lt_toSequenceOfBlowups_length hlt)
    have key := comap_strictTransform_of_flat_of_isLocallyNoetherian (s.map i)
      _s0 (t.map i) _s1 hsq (s.center i)
      (iteratedStrictTransform s H i) (s.isBlowup i (by omega))
    rw [iteratedStrictTransform_succ, iteratedStrictTransform_succ, key, ih hle, hc]

theorem strictTransformAtLength_comap
    (fLast : t.obj t.length ⟶ s.obj s.length)
    (hfLast : fLast = strictPullbackMapAt s t D t.length le_rfl
      ≫ eqToHom (congrArg s.obj $ length_eq_of_strictPullbackBlowupSeq s t D)) :
    strictTransformAtLength t (H.comap g)
      = (strictTransformAtLength s H).comap fLast := by
  let _a0 := length_eq_of_strictPullbackBlowupSeq s t D
  rw [strictTransformAtLength_eq, strictTransformAtLength_eq, hfLast,
    comap_comp,
    iteratedStrictTransform_comap_eqToHom s H t.length s.length _a0
      (congrArg s.obj _a0)]
  exact iteratedStrictTransform_comap hflat s t D hNs hNt H t.length le_rfl
end

section
variable (hderiv : DerivIdealSheafIterateCommBaseChange) (hstar : MaxContactCoverProperties) (hinv : ComapIsoInvariance) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B) (T T' : MarkedIdealWithBoundary) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc) (S : MarkedIdealWithBoundary) (hV : IsAdmissible S) (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (mult S : ENat)) (hdimS : S.krullDimSucc ≤ T.krullDimSucc) (L : Type) [Field L] [CharZero L] (f : S.base →+* L) [Flat (pullback.fst S.structMap (specMapOfFieldHom S.base L f))] (hV' : IsAdmissible (S.baseChange L f)) (hO' : ∀ x : ↥(S.baseChange L f).scheme, orderAt (S.baseChange L f).ideal x ≤ (mult (S.baseChange L f) : ENat))
include hderiv hstar hmono hspec hPdimT hPdimOther hV hO hdimS hV' hO'
section
variable (hdimS' : (S.baseChange L f).krullDimSucc ≤ T'.krullDimSucc) (hbc : IsBaseChangeInherited P)
include hdimS' hbc
theorem nonempty_strictPullbackBlowupSeq_appendLowerDimReduction
    (s : S.mbs)
    (t : MarkedBlowupSequenceData (bc S f).structMap (bc S f).ideal
      (bc S f).mult (bc S f).boundary)
    (hftS : LocallyOfFiniteType $ s.proj s.length ≫ structMap S)
    (hftT : LocallyOfFiniteType
      (t.proj t.length ≫ structMap (bc S f)))
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap $ specMapOfFieldHom S.base L f)
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (extra : List (s.obj s.length).IdealSheafData)
    extra'
    (hextra' : extra' = extra.map fun E : IdealSheafData (s.obj s.length) => comap E D.lastMap)
    keep j
    (hVc : IsAdmissible $ derivedTriple S s hftS extra keep)
    (hVc' : (derivedTriple (bc S f) t hftT
      (comapBoundaryBaseChange S L f s t D extra) keep).IsAdmissible)
    (hj : j < length (extra ++ (s.boundary s.length).drop keep))
    (hj' : j < (@append (t.obj t.length).IdealSheafData (comapBoundaryBaseChange S L f s t D extra)
      ((t.boundary t.length).drop keep)).length)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take keep,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (support Dv : CSet $ s.obj s.length) = ∅)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take keep,
      orderAtLeastLocus (t.ideal t.length) (bc S f).mult ∩
        (support Dv : CSet $ t.obj t.length) = ∅) :
    Nonempty $ StrictPullbackBlowupSeq (pullback.fst S.structMap $ specMapOfFieldHom S.base L f)
      (appendLowerDimReduction hinv T' (fun S' _ i => A i S') (bc S f) t extra'
        keep j).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendLowerDimReduction hinv T (fun S' _ i => A i S') S s extra keep
        j).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  let _c0 := derivedTriple S s hftS extra keep
  subst hextra'
  have hm := hV.one_le_mult
  have hdim := hstar.derivedTriple_dim_le hV s hftS extra keep hdimS
  have hdim2 := hstar.derivedTriple_dim_le hV' t hftT (comapBoundaryBaseChange S L f s t D extra) keep hdimS'
  have hP := hmono _ _ hdim hPdimT
  have hDb0 : ∀ hft : LocallyOfFiniteType
      _c0.structMap,
      _c0.IsBalanced hft :=
    fun _ => isBalanced_derivedTriple hstar S hV hm hO s hftS extra keep hVc
  obtain ⟨hVb, hPb, hOb, hDb⟩ :=
    hbc _c0 L f hVc hP (mp (isOrderBoundedByMult_iff _) $ isOrderBoundedByMult_derivedTriple hstar S hV hm hO s hftS extra keep hVc) hDb0
  exact nonempty_strictPullbackSeq_appendLowerDimReduction_baseChange S L f s t D hderiv hstar hinv P A B j
    (hspec j) T T' extra keep hftS hftT hV hm hO
    (BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar S hV s) hV' hO'
    (BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar (bcT S f) hV' t) hdim hP hVc hj hsep
    hdim2 (hmono _ _ hdim2 hPdimOther) hVc' hj' hsep' hVb hPb hOb hDb

theorem isStrictPullbackBlowupSeq_appendLowerDimReduction_baseChange
    (H : tISD S)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    (hH' : ∀ [LocallyOfFiniteType (bc S f).structMap],
      IsMaxContactHypersurface (bc S f).base (bc S f).structMap
        (bc S f).ideal (bc S f).mult
        (H.comap $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f))
    (hH'snc : InStrictNormalCrossingPosition (bc S f).structMap
      [H.comap $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f])
    (s : S.mbs)
    (t : MarkedBlowupSequenceData (bc S f).structMap (bc S f).ideal
      (bc S f).mult (bc S f).boundary)
    (D : StrictPullbackBlowupSeq (pullback.fst S.structMap $ specMapOfFieldHom S.base L f)
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (hsep : ∀ Dv ∈ (s.boundary s.length).take S.boundary.length,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (Dv.support : CSet $ s.obj s.length) = ∅)
    (hsep' : ∀ Dv ∈ (t.boundary t.length).take S.boundary.length,
      orderAtLeastLocus (t.ideal t.length) (bc S f).mult ∩
        (Dv.support : CSet $ t.obj t.length) = ∅) :
    IsStrictPullbackBlowupSeq (pullback.fst S.structMap $ specMapOfFieldHom S.base L f)
      (appendLowerDimReduction hinv T' (fun S' _ i => A i S') (bc S f) t
        [strictTransformAtLength t
          (H.comap $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f)]
        S.boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (appendLowerDimReduction hinv T (fun S' _ i => A i S') S s
        [strictTransformAtLength s H] S.boundary.length 0).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have := hV.locallyOfFiniteType
  have := hV'.locallyOfFiniteType
  let _s0 := bcT S f
  have hftS := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV s _ le_rfl
  have hftT := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar _s0 hV' t _
    le_rfl
  let _a2 := baseChangeMapAtLength S L f s t D
  have hE : cmI (strictTransformAtLength s H) _a2
      = strictTransformAtLength t
        (cmI H $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f) :=
    (strictTransformAtLength_comap
      ‹Flat (pullback.fst S.structMap $ _root_.FunctorialResolution.EmbeddedResolution.specMapOfFieldHom S.base L f)›
      s t D (BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar S hV s) (BoundarySeparationBaseChange.isLocallyNoetherian_schemeAt hstar _s0 hV' t) H _a2 $ D.lastMap_eq).symm
  have hbcx : comapBoundaryBaseChange S L f s t D [strictTransformAtLength s H]
      = [strictTransformAtLength t
          (cmI H $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f)] := by
    show [cmI (strictTransformAtLength s H) _a2] = _
    rw [hE]
  have hsncS : InStrictNormalCrossingPosition (lastP s ≫ tMp S)
      ([strictTransformAtLength s H] ++ (lastB s).drop (bLen S)) := by
    rw [strictTransformAtLength_eq]
    exact inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H hH s
      (inStrictNormalCrossingPosition_iteratedStrictTransform_zero S s H hHsnc) s.length le_rfl
  have hsncT : InStrictNormalCrossingPosition (lastP t ≫ tMp _s0)
      (comapBoundaryBaseChange S L f s t D [strictTransformAtLength s H] ++
        (lastB t).drop S.boundary.length) := by
    rw [hbcx, strictTransformAtLength_eq, ← (MarkedIdealWithBoundary.length_boundary_baseChange S L f)]
    exact inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar _s0 hV' hO'
      (cmI H $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f) hH' t
      (inStrictNormalCrossingPosition_iteratedStrictTransform_zero _s0 t
        (cmI H $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f) hH'snc) t.length le_rfl
  have hVcS := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV s hftS
    [strictTransformAtLength s H] S.boundary.length hsncS
  have hVcT := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar _s0 hV' t hftT
    (comapBoundaryBaseChange S L f s t D [strictTransformAtLength s H]) S.boundary.length hsncT
  obtain ⟨D2⟩ := nonempty_strictPullbackBlowupSeq_appendLowerDimReduction hderiv hstar hinv P hmono A B hspec T T' hPdimT
    hPdimOther S hV hO hdimS L f hV' hO' hdimS' hbc s t hftS hftT D [strictTransformAtLength s H]
    [strictTransformAtLength t
      (cmI H $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f)]
    hbcx.symm S.boundary.length 0 hVcS hVcT (by simp) (by simp [comapBoundaryBaseChange]) hsep hsep'
  exact D2.isStrictPullback
end

theorem isStrictPullbackBlowupSeq_reduceAlongHypersurface_baseChange
    (hdim' : (bc S f).krullDimSucc ≤ T'.krullDimSucc)
    (H : tISD S)
    (hH : ∀ [LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    (hH' : ∀ [LocallyOfFiniteType (bc S f).structMap],
      IsMaxContactHypersurface (bc S f).base (bc S f).structMap
        (bc S f).ideal (bc S f).mult
        (H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))))
    (hH'snc : InStrictNormalCrossingPosition (bc S f).structMap
      [H.comap (pullback.fst S.structMap (specMapOfFieldHom S.base L f))])
    (hbc : IsBaseChangeInherited P) :
    IsStrictPullbackBlowupSeq (pullback.fst S.structMap (specMapOfFieldHom S.base L f))
      (reduceAlongHypersurface hinv T' (fun S' _ i => A i S') (bc S f)
        (H.comap (pullback.fst S.structMap
          (specMapOfFieldHom S.base L f)))).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (reduceAlongHypersurface hinv T (fun S' _ i => A i S') S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hlen :=
    MarkedIdealWithBoundary.length_boundary_baseChange S L f
  let _a1 := pullback.fst S.structMap (specMapOfFieldHom S.base L f)
  have _i12 : ∀ j, j ≤ S.boundary.length → Nonempty (StrictPullbackBlowupSeq _a1 (separateBoundary hinv T' (fun S' _ i => A i S') (bcT S f) j).toMarkedSequenceOfBlowups.toSequenceOfBlowups (separateBoundary hinv T (fun S' _ i => A i S') S j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [separateBoundary_zero, separateBoundary_zero]
      exact nonempty_strictPullback_of_length_eq_zero _ _ _
        (emptyMarkedBlowupSequenceData_toMarkedSequence_length _ _ _ _) (emptyMarkedBlowupSequenceData_toMarkedSequence_length _ _ _ _)
    | succ j ih =>
      intro hj
      obtain ⟨D⟩ := ih (by omega)
      rw [separateBoundary_succ, separateBoundary_succ]
      have hftS := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV
        (separateBoundary hinv T (fun S' _ i => A i S') S j) _ le_rfl
      let _a0 := bcT S f
      have hftT := BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar _a0 hV'
        (separateBoundary hinv T' (fun S' _ i => A i S') _a0 j) _ le_rfl
      exact nonempty_strictPullbackBlowupSeq_appendLowerDimReduction hderiv hstar hinv P hmono A B hspec T T' hPdimT hPdimOther S
        hV hO hdimS L f hV' hO' hdim' hbc _ _ hftS hftT D [] [] rfl 0 j
        (isAdmissible_derivedTriple_nil hstar S hV _ hftS)
        (isAdmissible_derivedTriple_nil hstar _a0 hV' _ hftT)
        (lt_length_nil_append_boundary S _ j (by omega))
        (lt_length_nil_append_boundary _a0 _ j
          (by rw [MarkedIdealWithBoundary.length_boundary_baseChange]; omega))
        (orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero S _) (orderAtLeastLocus_inter_support_eq_empty_of_mem_take_zero _a0 _)
  obtain ⟨D⟩ := _i12 S.boundary.length le_rfl
  have hSeparated := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T hPdimT
    S hV hO hdimS H hHsnc S.boundary.length le_rfl
  let _a0 := bcT S f
  have hSeparatedSeq := separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A B hspec T'
    hPdimOther _a0 hV' hO' hdim'
    (cmI H _a1) hH'snc
    _a0.boundary.length le_rfl
  rw [hlen] at hSeparatedSeq
  rw [reduceAlongHypersurface_eq_appendLowerDimReduction, reduceAlongHypersurface_eq_appendLowerDimReduction, hlen]
  exact isStrictPullbackBlowupSeq_appendLowerDimReduction_baseChange hderiv hstar hinv P hmono A B hspec T T' hPdimT hPdimOther S hV
    hO hdimS L f hV' hO' hdim' hbc H hH hHsnc hH' hH'snc
    (separateBoundary hinv T (fun S' _ i => A i S') S S.boundary.length)
    (separateBoundary hinv T' (fun S' _ i => A i S') _a0
      S.boundary.length)
    D (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated S _ S.boundary.length hSeparated.1)
    (orderAtLeastLocus_inter_support_eq_empty_of_boundarySeparated _a0 _ S.boundary.length hSeparatedSeq.1)
end

end BoundaryLoopFieldBaseChange





namespace OrderReductionFieldBaseChange

section
variable (T : MarkedIdealWithBoundary)
section
variable (L : Type) [Field L] (f : T.base →+* L)
def dropTrivialBoundaryBaseFieldHom :
    (dropTrivialBoundary T).base →+* L := f

theorem surjective_baseChange_fst :
    Surjective $ pullback.fst T.structMap $ specMapOfFieldHom T.base L f :=
  m98 (P := @Surjective)
    (of_hasPullback T.structMap $ specMapOfFieldHom T.base L f).flip
    (instSurjectiveSpecMapOfFieldHom T.base L f)
end

end

def coverBaseFieldHom (A : MarkedIdealWithBoundary) (hv : IsAdmissible A) (L : Type) [Field L]
    (f : A.base →+* L) : (cT hv).base →+* L := f

theorem comp_assoc_eq_of_eq_comp {X Y Z W V : Sch}
    (p : X ⟶ Y) (q : Y ⟶ W) (b : Y ⟶ Z) (c : Z ⟶ W) (r : X ⟶ V) (s : V ⟶ W)
    (hq : q = b ≫ c) (h : p ≫ q = r ≫ s) :
    (p ≫ b) ≫ c = r ≫ s :=by simp_all
section
variable (A : MarkedIdealWithBoundary) (hv : IsAdmissible A) (L : Type) [Field L] (f : A.base →+* L)

def coverBaseChangeMap :
    scheme ((cT hv).baseChange L $ coverBaseFieldHom A hv L f) ⟶
      scheme (bc A f) :=
  pullback.lift
    (pullback.fst (cT hv).structMap
        (specMapOfFieldHom (cT hv).base L $ coverBaseFieldHom A hv L f)
      ≫ coverMap A hv)
    (pullback.snd (cT hv).structMap
      (specMapOfFieldHom (cT hv).base L $ coverBaseFieldHom A hv L f))
    ((fun A hv L [Field L] f => comp_assoc_eq_of_eq_comp
    (pullback.fst (p7 hv).structMap
      (specMapOfFieldHom (p7 hv).base L $ coverBaseFieldHom A hv L f))
    (p7 hv).structMap
    (p12 A hv)
    A.structMap
    (pullback.snd (p7 hv).structMap
      (specMapOfFieldHom (p7 hv).base L $ coverBaseFieldHom A hv L f))
    (specMapOfFieldHom A.base L f)
    (coverTriple_structureMorphism A hv)
    pullback.condition) A hv L f)

abbrev coverBaseChangeFiber (hv' : IsAdmissible (bc A f)) : Sch :=
  pullback (coverMap (bc A f) hv') $ coverBaseChangeMap A hv L f
end

section
variable {W X Y Z : Sch} {fst : W ⟶ X}
section
variable {snd : W ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z} (sq : CategoryTheory.IsPullback fst snd a b)
include sq
private theorem flat_fst_of_isPullback
    (hb : Flat b) : Flat fst :=
  m98 (P := @Flat) sq.flip hb

theorem surjective_fst_of_isPullback
    (hb : Surjective b) : Surjective fst :=
  m98 (P := @Surjective) sq.flip hb

private theorem smooth_fst_of_isPullback
    (hb : Smooth b) : Smooth fst :=
  m98 (P := @Smooth) sq.flip hb
end

theorem isPullback_congr_hom {snd snd' : W ⟶ Y}
    {a a' : X ⟶ Z} {b : Y ⟶ Z} (h : CategoryTheory.IsPullback fst snd a b)
    (hs : snd' = snd) (ha : a = a') : CategoryTheory.IsPullback fst snd' a' b :=by simp_all
end

theorem comp_comp_eq_comp_comp {Q S1_ S2_ Y1 Y2 X : Sch}
    (q1_ : Q ⟶ S1_) (q2_ : Q ⟶ S2_) (c1_ : S1_ ⟶ Y1) (p1_ : Y1 ⟶ X) (cc : S2_ ⟶ Y1)
    (c2_ : S2_ ⟶ Y2) (p2_ : Y2 ⟶ X)
    (hpc : q1_ ≫ c1_ = q2_ ≫ cc) (hcf : cc ≫ p1_ = c2_ ≫ p2_) :
    q1_ ≫ c1_ ≫ p1_ = q2_ ≫ c2_ ≫ p2_ := by
  rw [← assoc, hpc, assoc, hcf]

section
variable {Q S Y X : Sch} (q : Q ⟶ S) (c : S ⟶ Y) (p : Y ⟶ X)
theorem comap_comap_comap
    (I : ISD X) : (comap (comap I p) c).comap q = comap I (q ≫ c ≫ p) := by
  simp [comap_comp]

theorem map_comap_comap_comap
    (E : Bdy X) :
    map (fun D => comap D q)
        (map (fun D => comap D c) $ map (fun D => comap D p) E)
      = map (fun D => comap D $ q ≫ c ≫ p) E :=by simp_all
end

section
variable {Q S1_ S2_ Y1 Y2 X : Sch} (q1_ : Q ⟶ S1_) (q2_ : Q ⟶ S2_) (c1_ : S1_ ⟶ Y1) (p1_ : Y1 ⟶ X) (c2_ : S2_ ⟶ Y2) (p2_ : Y2 ⟶ X)
theorem comap_eq_comap_of_comp_eq
    (I : ISD X) (I1 : ISD S1_) (I2 : ISD S2_)
    (h1_ : I1 = comap (comap I p1_) c1_) (h2_ : I2 = comap (comap I p2_) c2_)
    (hk : q1_ ≫ c1_ ≫ p1_ = q2_ ≫ c2_ ≫ p2_) :
    comap I1 q1_ = comap I2 q2_ := by
  subst h1_
  subst h2_
  rw [comap_comap_comap, comap_comap_comap, hk]

theorem map_comap_eq_map_comap_of_comp_eq
    (E : Bdy X) (E1_ : Bdy S1_) (E2_ : Bdy S2_)
    (h1_ : E1_ = map (fun D => comap D c1_) (map (fun D => comap D p1_) E))
    (h2_ : E2_ = map (fun D => comap D c2_) (map (fun D => comap D p2_) E))
    (hk : q1_ ≫ c1_ ≫ p1_ = q2_ ≫ c2_ ≫ p2_) :
    map (fun D => comap D q1_) E1_ = map (fun D => comap D q2_) E2_ := by
  subst h1_
  subst h2_
  rw [map_comap_comap_comap, map_comap_comap_comap, hk]
end

theorem filter_map_comap {X Y : Sch} (g : X ⟶ Y)
    (p : ISD Y → Bool) (q : ISD X → Bool)
    (hpq : ∀ D : ISD Y, q (comap D g) = p D) (E : Bdy Y) :
    List.filter q (map (fun D => comap D g) E)
      = map (fun D => comap D g) (List.filter p E) := by
  induction E with
  | nil => simp
  | cons D E ih =>
      cases hD : p D
      simp_all
      simp_all

section
variable (p : Prop) (i : Decidable p)
theorem decide_eq_true_iff_self :
    (@decide p i = true) ↔ p :=by simp_all
theorem not_decide_eq_true_iff_not :
    ((!(@decide p i)) = true) ↔ ¬ p :=by simp_all
end

theorem isStrictPullback_descend_of_flat_surjective_cover
    {XA XB XC XC' XCb XQ : Sch}
    (hh : XB ⟶ XA) (g : XC ⟶ XA) (g' : XC' ⟶ XB) (p : XCb ⟶ XB) (pA : XCb ⟶ XC)
    (q1_ : XQ ⟶ XC') (q2_ : XQ ⟶ XCb)
    (hfh : Flat hh) (hfq : Flat q1_)
    (hfg' : Flat g')
    (hsq : Surjective q1_) (hsg' : Surjective g')
    (hsq1 : q1_ ≫ g' = q2_ ≫ p) (hsq2 : p ≫ hh = pA ≫ g)
    (u : SequenceOfBlowups XQ) (sB : SequenceOfBlowups XC') (sCb : SequenceOfBlowups XCb) (sA : SequenceOfBlowups XC)
    (dA : SequenceOfBlowups XA) (dB : SequenceOfBlowups XB)
    (hX : IsStrictPullbackBlowupSeq q1_ u sB) (hY : IsStrictPullbackBlowupSeq q2_ u sCb)
    (hZ : IsStrictPullbackBlowupSeq pA sCb sA)
    (hdA : IsStrictPullbackBlowupSeq g sA dA) (hdB : IsStrictPullbackBlowupSeq g' sB dB) :
    IsStrictPullbackBlowupSeq hh dB dA := by
  have hcomp : (q1_ ≫ g') ≫ hh = q2_ ≫ (pA ≫ g) := by simp_all
  exact (isStrictPullbackSequenceOfBlowups_baseChange dA hh).of_isomorphic_pullback ((hX.comp hdB).isomorphic_of_isomorphic ((hY.comp $ hZ.comp hdA).congr_hom hcomp.symm).baseChange_of_comp $ isomorphic_refl u).symm

theorem comp_structureMorphism_eq_of_comp_eq {Q S1_ S2_ Y W : Sch}
    (q1_ : Q ⟶ S1_) (q2_ : Q ⟶ S2_) (c1_ : S1_ ⟶ Y) (c2_ : S2_ ⟶ Y) (sY : Y ⟶ W)
    (s1_ : S1_ ⟶ W) (s2_ : S2_ ⟶ W)
    (h1_ : s1_ = c1_ ≫ sY) (h2_ : c2_ ≫ sY = s2_) (hpc : q1_ ≫ c1_ = q2_ ≫ c2_) :
    q1_ ≫ s1_ = q2_ ≫ s2_ := by
  subst h1_
  subst h2_
  rw [← assoc, hpc, assoc]

theorem nontrivialPart_eq_filter {X : Sch}
    {q : ISD X → Bool} (hq : ∀ D : ISD X, q D = true ↔ D ≠ ⊤)
    (E : Bdy X) :
    nontrivialPart E = List.filter q E := by
  unfold nontrivialPart
  refine congrArg (List.filter · E) $ funext fun D => ?_
  refine Bool.eq_iff_iff.mpr ?_
  rw [hq D]
  exact not_decide_eq_true_iff_not _ _

theorem filter_eq_map_filter_of_nontrivialPart_eq {X Y : Sch} (g : X ⟶ Y)
    [Surjective g]
    {p : ISD Y → Bool} {q : ISD X → Bool}
    {E : Bdy Y} {E' : Bdy X}
    (hp : ∀ D : ISD Y, p D = true ↔ D ≠ ⊤)
    (hq : ∀ D : ISD X, q D = true ↔ D ≠ ⊤)
    (hEE : nontrivialPart (map (fun D => comap D g) E)
      = nontrivialPart E') :
    List.filter q E' = map (fun D => comap D g) (List.filter p E) := by
  have hpq : ∀ D : ISD Y, q (cmI D g) = p D := by
    intro D
    refine Bool.eq_iff_iff.mpr ?_
    rw [hq, hp]
    exact comap_ne_top_iff_of_surjective g D
  have h1 : List.filter q (map (·.comap g) E) = List.filter q E' := by
    rw [← nontrivialPart_eq_filter hq (map (·.comap g) E),
      ← nontrivialPart_eq_filter hq E']
    exact hEE
  rw [← h1]
  exact filter_map_comap g p q hpq E

theorem dropTrivialBoundary_withBoundary_baseChange (T : MarkedIdealWithBoundary) (L : Type) [Field L]
    (f : T.base →+* L) (E' : List (bc T f).scheme.IdealSheafData)
    (hE : SameNontrivialBoundary (bc T f).boundary E') :
    dropTrivialBoundary (withBoundary (bc T f) E')
      = (dropTrivialBoundary T).baseChange L (dropTrivialBoundaryBaseFieldHom T L f) := by
  let _a0 := pullback.fst T.structMap $ specMapOfFieldHom T.base L f
  let _a1 := bcT T f
  have hb : (dropTrivialBoundary $ tWB _a1 E').boundary
      = map (·.comap _a0)
          (dropTrivialBoundary T).boundary := by
    rw [dropTrivialBoundary_boundary, dropTrivialBoundary_boundary,
      withBoundary_boundary]
    refine filter_eq_map_filter_of_nontrivialPart_eq
      _a0 ?_ ?_ ?_
    intro _
    exact decide_eq_true_iff_self _ _
    intro _
    exact decide_eq_true_iff_self _ _
    have h := mp_ (sameNontrivialBoundary_iff (_a1.boundary) E') hE
    rwa [baseChange_boundary] at h
  exact congrArg (fun E : List (bcT T f).scheme.IdealSheafData =>
    withBoundary _a1 E) hb

theorem markedIdealWithBoundary_mk_congr__b12 (k : Type) [Field k] (Y : Sch)
    (q q' : Y ⟶ Sp k) (I I' : ISD Y) (m : ℕ)
    (E E' : Bdy Y) (hq : q = q') (hI : I = I') (hE : E = E') :
    mk k Y q I m E = mk k Y q' I' m E' :=by simp_all
theorem isPullback_coverBaseChangeMap (A : MarkedIdealWithBoundary) (hv : IsAdmissible A)
    (L : Type) [Field L] (f : A.base →+* L) :
    CategoryTheory.IsPullback
      (pullback.fst (cT hv).structMap
        (specMapOfFieldHom (cT hv).base L $ coverBaseFieldHom A hv L f))
      (coverBaseChangeMap A hv L f)
      (coverMap A hv)
      (pullback.fst A.structMap $ specMapOfFieldHom A.base L f) := by
  let _a1 := p7 hv
  exact of_bot (isPullback_congr_hom (of_hasPullback _a1.structMap $ specMapOfFieldHom _a1.base L $ coverBaseFieldHom A hv L f) (pullback.lift_snd _ _ _) $ coverTriple_structureMorphism A hv) (pullback.lift_fst _ _ _).symm
    (of_hasPullback A.structMap $ specMapOfFieldHom A.base L f)

theorem isAdmissible_withBoundary_singleton (S : MarkedIdealWithBoundary) (hV : IsAdmissible S)
    (H : tISD S) (hsnc : InStrictNormalCrossingPosition S.structMap [H]) :
    IsAdmissible $ withBoundary S [H] :=
  ⟨hV.charZero, hV.locallyOfFiniteType, hV.nonzeroOnComponents, hV.one_le_mult,
    hV.quasiCompact, hV.smooth, hsnc⟩

theorem isStrictPullback_of_eq_of_heq
    (hinv : ComapIsoInvariance) (Fam : ℕ → PrincipalizationAssignment)
    {T1_ T2_ : MarkedIdealWithBoundary} (hT : T1_ = T2_)
    (hv1_ : IsAdmissible T1_) (hv2_ : IsAdmissible T2_) (d : BlowupSequenceData T1_.scheme)
    {Z : Sch} (ps_ : scheme T1_ ⟶ Z) (ps' : scheme T2_ ⟶ Z) (hps_ : HEq ps_ ps')
    (w : SequenceOfBlowups Z)
    (hcrit : ∀ e : BlowupSequenceData T2_.scheme,
      IsStrictPullbackBlowupSeq (coverMap T2_ hv2_)
          (coverMarkedBlowupData T2_ hv2_ hinv
            (lowerDimensionalFamily Fam T2_)).toSequenceOfBlowups e.toSequenceOfBlowups →
        IsStrictPullbackBlowupSeq ps' e.toSequenceOfBlowups w)
    (hd : IsStrictPullbackBlowupSeq (coverMap T1_ hv1_)
      (coverMarkedBlowupData T1_ hv1_ hinv
        (lowerDimensionalFamily Fam T1_)).toSequenceOfBlowups d.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq ps_ d.toSequenceOfBlowups w := by
  subst hT
  have hps2 := eq_of_heq hps_
  subst hps2
  exact hcrit d hd

def ValidBaseChange : Prop :=
  ∀ (T : MarkedIdealWithBoundary) (L : Type) [Field L] [CharZero L] (f : T.base →+* L),
    IsAdmissible T → IsAdmissible (bc T f)

def OrderAtBaseChangeEq : Prop :=
  ∀ (T : MarkedIdealWithBoundary) (L : Type) [Field L] [CharZero L] (f : T.base →+* L),
    IsAdmissible T → ∀ y : ↥(bc T f).scheme,
      orderAt (bc T f).ideal y
        = orderAt T.ideal ((pullback.fst T.structMap $ specMapOfFieldHom T.base L f) y)

def MaxContactHypersurfaceBaseChange : Prop :=
  ∀ (S : MarkedIdealWithBoundary) (L : Type) [Field L] [CharZero L] (f : S.base →+* L),
    IsAdmissible S → IsAdmissible (bc S f) →
    ∀ H : tISD S,
      (∀ [LocallyOfFiniteType S.structMap],
        IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H) →
      InStrictNormalCrossingPosition S.structMap [H] →
      ((∀ [LocallyOfFiniteType (bc S f).structMap],
          IsMaxContactHypersurface (bc S f).base (bc S f).structMap
            (bc S f).ideal (bc S f).mult
            (comap H $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f)) ∧
        InStrictNormalCrossingPosition (bc S f).structMap
          [comap H $ pullback.fst S.structMap $ specMapOfFieldHom S.base L f])

section
variable (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties) (hin : OrderReduction.OrderReductionHypotheses) (hMC : BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned) (hAdm : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback) (hderiv : DerivIdealSheafIterateCommBaseChange) (hbcV : ValidBaseChange) (hbcO : OrderAtBaseChangeEq) (hbcA : MaxContactHypersurfaceBaseChange) (hinv : ComapIsoInvariance) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (Fam : ℕ → PrincipalizationAssignment) (B : PrincipalizationAssignment) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (Fam j) B) (hinherit : IsBaseChangeInherited P)
include hstar hin hMC hAdm hderiv hbcV hbcO hbcA hmono hspec hinherit
theorem isStrictPullbackBlowupSeq_baseChange_withBoundary
    (hsf : MaxContactFunctoriality.CoverSequenceProperties hinv P Fam)
    (hmd : MaxContactFunctoriality.MarkingDescends hinv P Fam)
    (hcff : MaxContactFunctoriality.CoverFaithfullyFlat P)
    (htv : MaxContactFunctoriality.DropTrivialBoundaryAdmissible)
    (htm : MaxContactFunctoriality.MarkedOfMarkedDropTrivialBoundary)
    (T : MarkedIdealWithBoundary) (hV : IsAdmissible T) (hP : P T.krullDimSucc)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
    [Flat $ pullback.fst T.structMap $ specMapOfFieldHom T.base L f]
    (E' : List (bc T f).scheme.IdealSheafData)
    (hE : SameNontrivialBoundary (bc T f).boundary E')
    (hV' : (withBoundary (bc T f) E').IsAdmissible)
    (hP' : P (withBoundary (bc T f) E').krullDimSucc)
    (hdimChart :
      ((coverTriple (dropTrivialBoundary T) $ htv T hV).baseChange L
          (coverBaseFieldHom (dropTrivialBoundary T) (htv T hV) L $ dropTrivialBoundaryBaseFieldHom T L f)).krullDimSucc
        ≤ (bc T f).krullDimSucc)
    (hqc : QuasiCompact
      (pullback.snd
          (coverMap ((dropTrivialBoundary T).baseChange L $ dropTrivialBoundaryBaseFieldHom T L f)
            (hbcV (dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) $ htv T hV))
          (coverBaseChangeMap (dropTrivialBoundary T) (htv T hV) L $ dropTrivialBoundaryBaseFieldHom T L f)
        ≫ ((coverTriple (dropTrivialBoundary T) $ htv T hV).baseChange L
            (coverBaseFieldHom (dropTrivialBoundary T) (htv T hV) L $ dropTrivialBoundaryBaseFieldHom T L f)).structMap))
    (hQdim : krullDimSucc
        (coverBaseChangeFiber (dropTrivialBoundary T) (htv T hV) L (dropTrivialBoundaryBaseFieldHom T L f)
          (hbcV (dropTrivialBoundary T) L (dropTrivialBoundaryBaseFieldHom T L f) $ htv T hV))
      ≤ (bc T f).krullDimSucc) :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap $ specMapOfFieldHom T.base L f)
      (maxContactPrincipalization hinv Fam $ withBoundary (bc T f) E').toSequenceOfBlowups
      (maxContactPrincipalization hinv Fam T).toSequenceOfBlowups := by
  let _c0 := tWB (bcT T f) E'
  let _c1 := pullback.fst T.structMap $ specMapOfFieldHom T.base L f
  have hord :=
    hbcO T L f hV
  have hord' : ∀ x,
      orderAt _c0.ideal x
        ≤ ((tMu _c0 : ℕ) : ENat) := by
    intro x
    exact (hord x).le.trans $ hO _
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = (∅ : CSet T.scheme)
  have h1 :=
    length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P Fam T hV hP hO hemp
  have hemp' :=
    by
    apply mp_ subset_empty_iff
    intro y hy
    have h1 := (mem_orderAtLeastLocus_iff (bcT T f).ideal T.mult y).1 hy
    rw [hord y] at h1
    have h2 :=
      (mem_orderAtLeastLocus_iff T.ideal T.mult _).2 h1
    rw [hemp] at h2
    simp at h2
  exact IsStrictPullbackBlowupSeq.of_length_zero
    _c1
    (maxContactPrincipalization hinv Fam _c0).toSequenceOfBlowups
    (maxContactPrincipalization hinv Fam T).toSequenceOfBlowups (length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P Fam _c0 hV' hP' hord' hemp') h1
  have hHypT : OrderReductionHypotheses P T :=
    ⟨hP, hO, mpr_ nonempty_iff_ne_empty hemp, hV⟩
  have hHypT' : OrderReductionHypotheses P _c0 := by
    refine ⟨hP', hord', ?_, hV'⟩
    by_contra hcon
    exact hemp $ orderAtLeastLocus_eq_empty_of_comap_eq_empty
      _c1 T.ideal T.mult
      (mp_ not_nonempty_iff_eq_empty hcon)
  obtain ⟨d, hd, hmain⟩ :=
    exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm T hHypT
  obtain ⟨d', hd', hmain'⟩ :=
    exists_isStrictPullback_cover_dropTrivialBoundary hsf hmd htv htm
      _c0 hHypT'
  rw [hmain, hmain']
  have hT :=
    dropTrivialBoundary_withBoundary_baseChange T L f E' hE
  let _a0 := dropTrivialBoundaryBaseFieldHom T L f
  have hHypBC : OrderReductionHypotheses P
      ((dropTrivialBoundary T).baseChange L _a0) := by
    rw [← hT]
    exact hHypT'.of_dropTrivialBoundaryAdmissible htv
  let _a13 := hbcV (dropTrivialBoundary T) L _a0 $ htv T hV
  refine isStrictPullback_of_eq_of_heq hinv Fam hT ((hHypT'.of_dropTrivialBoundaryAdmissible htv).valid)
    _a13 d'
    _c1
    _c1 HEq.rfl d.toSequenceOfBlowups ?_ hd'
  intro e he
  let A := dropTrivialBoundary T
  let hv := htv T hV
  let f := _a0
  let hv' := _a13
  let hHyp := hHypT.of_dropTrivialBoundaryAdmissible htv
  let hHyp' := hHypBC
  let _a7 := coverBaseChangeFiber A hv L f hv'
  let _s1 := specMapOfFieldHom A.base L f
  have hfA : Flat $ pullback.fst A.structMap _s1 :=
    inferInstance
  have hVCA :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P A hHyp
  have hVC1 :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P (bcT A f) hHyp'
  let _a5 := coverBaseFieldHom A hv L f
  have hVS2 :=
    hbcV (cT hv) L _a5 hVCA
  have hsqc := isPullback_coverBaseChangeMap A hv L f
  have hfg' :=
    flat_coverMap_of_isAdmissible (bcT A f) hv'
  have hsg' :=
    (hcff (bcT A f) hHyp').1
  let _a22 := coverMap (bcT A f) hv'
  let _a0 := pullback.fst _a22 $ coverBaseChangeMap A hv L f
  let _a1 := _a22
  have hbig : CategoryTheory.IsPullback
      _a0
      (pullback.snd _a1 $ coverBaseChangeMap A hv L f)
      _a1 $ coverBaseChangeMap A hv L f :=
    of_hasPullback _ _
  have hfl1 := flat_fst_of_isPullback hbig $ flat_fst_of_isPullback hsqc.flip $ flat_coverMap_of_isAdmissible A hv
  have hsu1 := surjective_fst_of_isPullback hbig $ surjective_fst_of_isPullback hsqc.flip $ (hcff A hHyp).1
  have hsm1 := smooth_fst_of_isPullback hbig $ smooth_fst_of_isPullback hsqc.flip $ smooth_coverMap_of_isAdmissible A hv
  have hsm2 := smooth_fst_of_isPullback hbig.flip $ smooth_coverMap_of_isAdmissible (bcT A f) hv'
  let _s0 := coverTriple (bcT A f) hv'
  have hT : pullbackTriple _s0
        _a0
      = pullbackTriple ((cT hv).baseChange L $ coverBaseFieldHom A hv L f)
        (pullback.snd _a1
          (coverBaseChangeMap A hv L f)) :=
    by
    have hcf : coverBaseChangeMap A hv L f ≫ pullback.fst A.structMap _s1
        = pullback.fst (cT hv).structMap
            (specMapOfFieldHom (cT hv).base L $ coverBaseFieldHom A hv L f)
          ≫ coverMap A hv := by
      unfold coverBaseChangeMap
      exact pullback.lift_fst _ _ _
    have hcs : coverBaseChangeMap A hv L f ≫ tMp (bcT A f)
        = tMp ((cT hv).baseChange L $ coverBaseFieldHom A hv L f) := by
      simp [baseChange_structureMorphism]
      unfold coverBaseChangeMap
      exact pullback.lift_snd _ _ _
    let _a14 := balancedTunedIdeal A hv
    have hT : balancedTunedIdeal (bcT A f) hv'
        = cmI _a14
          (pullback.fst A.structMap _s1) := by
      have : CharZero A.base := hv.charZero
      have : Smooth A.structMap := hv.smooth
      have : LocallyOfFiniteType A.structMap := hv.locallyOfFiniteType
      let _a15 := pullback.snd A.structMap _s1
      have : Smooth _a15 :=
        hv'.smooth
      have : LocallyOfFiniteType
          _a15 := hv'.locallyOfFiniteType
      exact balancedTunedSheaf_comap_of_isPullback hderiv A.base L f A.structMap
        _a15
        (pullback.fst A.structMap _s1)
        (of_hasPullback A.structMap _s1) A.ideal A.mult
    have hkey :
        _a0
            ≫ _a1
              ≫ pullback.fst A.structMap _s1
          = pullback.snd _a1
              (coverBaseChangeMap A hv L f)
            ≫ pullback.fst (cT hv).structMap
                (specMapOfFieldHom (cT hv).base L $ coverBaseFieldHom A hv L f)
              ≫ coverMap A hv :=
      comp_comp_eq_comp_comp _ _ _ _ (coverBaseChangeMap A hv L f) _ _ pullback.condition hcf
    have hI1 : ideal _s0
        = cmI (cmI _a14
            (pullback.fst A.structMap _s1))
          _a1 := by
      rw [coverTriple_ideal, hT]
      exact rfl
    have hI2 : ideal ((cT hv).baseChange L $ coverBaseFieldHom A hv L f)
        = cmI (cmI _a14 $ coverMap A hv)
          (pullback.fst (cT hv).structMap
            (specMapOfFieldHom (cT hv).base L $ coverBaseFieldHom A hv L f)) := by
      rw [baseChange_ideal, coverTriple_ideal]
      exact rfl
    have hE1 : _s0.boundary
        = map (·.comap _a1)
          (map (cmI · $ pullback.fst A.structMap _s1)
            A.boundary) := by
      rw [coverTriple_boundary, baseChange_boundary]
      exact rfl
    have hE2 : ((cT hv).baseChange L $ coverBaseFieldHom A hv L f).boundary
        = map (fun D => cmI D
              (pullback.fst (cT hv).structMap
                (specMapOfFieldHom (cT hv).base L $ coverBaseFieldHom A hv L f)))
          (map (cmI · $ coverMap A hv) A.boundary) := by
      rw [baseChange_boundary, coverTriple_boundary]
      exact rfl
    have hsm :=
      comp_structureMorphism_eq_of_comp_eq _ _ _ _ _ _ _
        (coverTriple_structureMorphism (bcT A f) hv') hcs pullback.condition
    have hide :=
      comap_eq_comap_of_comp_eq _ _ _ _ _ _ _ _ _ hI1 hI2 hkey
    have hbd :=
      map_comap_eq_map_comap_of_comp_eq _ _ _ _ _ _ _ _ _ hE1 hE2 hkey
    exact markedIdealWithBoundary_mk_congr__b12 L _a7 _ _ _ _
      _s0.mult _ _ hsm hide hbd
  have hVQ2 : (pullbackTriple
      ((cT hv).baseChange L $ coverBaseFieldHom A hv L f)
      (pullback.snd _a1
        (coverBaseChangeMap A hv L f))).IsAdmissible :=
    @OrderReduction.OrderReductionHypotheses.valid_pullbackAlong hin
      ((cT hv).baseChange L $ coverBaseFieldHom A hv L f) hVS2
      _a7
      (pullback.snd _a1 (coverBaseChangeMap A hv L f)
        ≫ tMp ((cT hv).baseChange L $ coverBaseFieldHom A hv L f))
      (pullback.snd _a1 $ coverBaseChangeMap A hv L f)
      hsm2 hqc rfl
  have hVQ1 := hVQ2
  rw [← hT] at hVQ1
  let _a6 := MaxContactCoverData.coverMaxContactIdeal (bcT A f) hv'
  let _a20 := BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P (bcT A f) hHyp'
  have hVb :=
    isAdmissible_withBoundary_singleton _s0
      hVC1 _a6
      _a20
  have hVQb := @OrderReduction.OrderReductionHypotheses.valid_pullbackAlong hin
    (tWB _s0
      [_a6]) hVb
    _a7
    (_a0
      ≫ tMp _s0)
    _a0
    hsm1 hVQ1.quasiCompact rfl
  have hsncQ1 := hVQb.snc
  let _a21 := BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P (bcT A f) hHyp'
  have hadmQ1 :=
    @hAdm _s0.base inferInstance hVC1.charZero
      _s0.scheme
      _s0.structMap hVC1.smooth
      hVC1.locallyOfFiniteType _a7
      _a0
      hsm1 hVQ1.locallyOfFiniteType
      _s0.ideal
      _s0.mult hVC1.one_le_mult
      _a6
      _a21
  have hadmQ2 := MaxContactFunctoriality.isMaxContactHypersurface_of_triple_eq hT.symm
    hVQ2.locallyOfFiniteType hVQ1.locallyOfFiniteType
    (cmI _a6
      _a0)
    (cmI _a6
      _a0)
    HEq.rfl hadmQ1
  have hsncQ2 := MaxContactFunctoriality.inStrictNormalCrossingPosition_of_triple_eq hT.symm
    [cmI _a6
      _a0]
    [cmI _a6
      _a0]
    HEq.rfl hsncQ1
  have hO2 : ∀ x : scheme $ (cT hv).baseChange L $ coverBaseFieldHom A hv L f,
      orderAt ((cT hv).baseChange L $ coverBaseFieldHom A hv L f).ideal x
        ≤ ((tMu ((cT hv).baseChange L
            (coverBaseFieldHom A hv L f)) : ℕ) : ENat) := by
    intro x
    rw [hbcO (cT hv) L _a5 hVCA x]
    exact BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P A hHyp _
  let _a23 := BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P A hHyp
  have hadmS2 := hbcA (cT hv) L _a5 hVCA hVS2
    (cI hv)
    _a23
    (BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P A hHyp)
  have hX :=
    @isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hMC hAdm hinv P hmono Fam B hspec
      (bcT A f) hHyp'.dim_prop
      _s0 hVC1
      (BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P (bcT A f) hHyp')
      (MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim (bcT A f) hv')
      _a6
      _a21
      _a20
      _a7
      _a0
      hsm1 hfl1 hsu1 hVQ1 hQdim
      (cmI _a6
        _a0)
      hadmQ1 hsncQ1
  have hY0 :=
    @isStrictPullbackBlowupSeq_reduceAlongHypersurface hstar hin hMC hAdm hinv P hmono Fam B hspec
      (bcT A f) hHyp'.dim_prop
      ((cT hv).baseChange L $ coverBaseFieldHom A hv L f) hVS2 hO2 hdimChart
      (cmI (cI hv)
        (pullback.fst (cT hv).structMap
          (specMapOfFieldHom (cT hv).base L $ coverBaseFieldHom A hv L f)))
      hadmS2.1 hadmS2.2
      _a7
      (pullback.snd _a1 $ coverBaseChangeMap A hv L f)
      hsm2 (flat_fst_of_isPullback hbig.flip hfg') (surjective_fst_of_isPullback hbig.flip hsg') hVQ2 hQdim
      (cmI _a6
        _a0)
      hadmQ2 hsncQ2
  have hEqSeq :=
    eq_of_heq $ MaxContactFunctoriality.reduceAlongHypersurface_toSequenceOfBlowups_heq hinv (bcT A f)
      (fun S' _ i => Fam i S') hT.symm
      (cmI _a6
        _a0)
      (cmI _a6
        _a0)
      HEq.rfl
  refine isStrictPullback_descend_of_flat_surjective_cover (pullback.fst A.structMap _s1)
    (coverMap A hv) _a1
    (coverBaseChangeMap A hv L f)
    (pullback.fst (cT hv).structMap
      (specMapOfFieldHom (cT hv).base L $ coverBaseFieldHom A hv L f))
    _a0
    (pullback.snd _a1 $ coverBaseChangeMap A hv L f)
    hfA hfl1 hfg' hsu1 hsg' pullback.condition hsqc.w.symm
    _ _ _ _ _ _ hX (hY0.congr_sourceSeq hEqSeq) ?_ hd he
  let _c0 := coverBaseFieldHom A hv L f
  let _c1 := cT hv
  have hVC :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P A hHyp
  have hVCb :=
    hbcV _c1 L _c0 hVC
  let _a0 := _a23
  let _a1 := BoundarySeparationByMaxContact.inStrictNormalCrossingPosition_coverMaxContactIdeal hstar P A hHyp
  let _a3 := cI hv
  have hadm := hbcA _c1 L _c0 hVC hVCb
    _a3
    _a0
    _a1
  refine BoundaryLoopFieldBaseChange.isStrictPullbackBlowupSeq_reduceAlongHypersurface_baseChange hderiv hstar hinv P hmono Fam B hspec
    A (bcT A f) hHyp.dim_prop hHyp'.dim_prop
    _c1 hVC
    (BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P A hHyp)
    (MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim A hv) L _c0 hVCb ?_ hdimChart
    _a3
    _a0
    _a1
    hadm.1 hadm.2 hinherit
  intro x
  rw [hbcO _c1 L _c0 hVC x]
  exact BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P A hHyp _
end

end OrderReductionFieldBaseChange

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

theorem isMaxContactHypersurface_comap_fieldBaseChange {k K : Type} [Field k] [Field K]
    [CharZero k] [CharZero K] {X : Sch} p
    [Smooth p] [LocallyOfFiniteType p]
    ph_
    [LocallyOfFiniteType $ pullback.snd p $ Spec.map ph_]
    (A : ISD X) m (H : ISD X)
    (h : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface K (pullback.snd p $ Spec.map ph_)
      (comap A $ pullback.fst p $ Spec.map ph_) m
      (comap H $ pullback.fst p $ Spec.map ph_) := by
  let _a0 := isPullback_pullback_specMap p ph_
  let _c0 := pullback.fst p $ m12 ph_
  intro y
  obtain ⟨U, hU, hxU, hcase⟩ := h $ bsM _c0 y
  have hVaff :=
    hU.preimage _c0
  refine ⟨pullback.fst p (m12 ph_) ⁻¹ᵁ U, hVaff, hxU, ?_⟩
  rcases hcase with ⟨hdisj, hHtop⟩ | ⟨n, c, j, hH, hmc⟩
  left
  constructor
  rw [orderAtLeastLocus_comap_fieldBaseChange p ph_ A m, disjoint_left]
  intro a ha ha'
  exact Set.disjoint_left.mp hdisj ha ha'
  have h1 := restrictIdeal_comap _c0 H U
  rwa [hHtop, comap_top] at h1
  right
  refine ⟨n, c.baseChange _a0, j, ?_, ?_⟩
  refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff
    (c.baseChange _a0)
    (cmI H _c0) {j} ?_
  rw [comap_ideal_eq_map_appLE H _c0
      ⟨U, hU⟩ ⟨pullback.fst p (m12 ph_) ⁻¹ᵁ U, hVaff⟩ le_rfl,
    c.ideal_eq_span_coord hU H {j} hH, m218]
  simp only [Finset.coe_singleton, image_singleton]
  rw [EtaleChart.baseChange_coord]
  refine mpr_ (isMaxContactCoord_iff_coord_mem K (pullback.snd p $ m12 ph_)
    (cmI A _c0) m hVaff
    (c.baseChange _a0) j) ?_
  rw [maxContactIdeal_comap_fieldBaseChange p ph_ m A,
    comap_ideal_eq_map_appLE (maxContactIdeal k p A m)
      _c0 ⟨U, hU⟩
      ⟨pullback.fst p (m12 ph_) ⁻¹ᵁ U, hVaff⟩ le_rfl,
    EtaleChart.baseChange_coord]
  exact Ideal.mem_map_of_mem _ $ mp_ (isMaxContactCoord_iff_coord_mem k p A m hU c j) hmc

namespace OrderReductionFieldBaseChange

section
variable (k L : Type) [Field k] [Field L]
theorem isMaxContactHypersurface_comap_specMapOfFieldHom
    [CharZero k] [CharZero L] {X : Sch} p
    [Smooth p] [LocallyOfFiniteType p] f
    [hft : LocallyOfFiniteType $ pullback.snd p $ specMapOfFieldHom k L f]
    (A : ISD X) m (H : ISD X)
    (h : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface L (pullback.snd p $ specMapOfFieldHom k L f)
      (comap A $ pullback.fst p $ specMapOfFieldHom k L f) m
      (comap H $ pullback.fst p $ specMapOfFieldHom k L f) := by
  revert hft
  rw [specMapOfFieldHom_eq k L f]
  intro hft
  exact @isMaxContactHypersurface_comap_fieldBaseChange k L _ _ _ _ X p _ _
    (CommRingCat.ofHom f) hft A m H h

theorem inStrictNormalCrossingPosition_comap_specMapOfFieldHom
    {X : Sch}
    p [Smooth p] f
    (H : ISD X) (hsnc : InStrictNormalCrossingPosition p [H]) :
    InStrictNormalCrossingPosition (pullback.snd p $ specMapOfFieldHom k L f)
      [comap H $ pullback.fst p $ specMapOfFieldHom k L f] := by
  rw [specMapOfFieldHom_eq k L f]
  exact inStrictNormalCrossingPosition_comap_pullback_specMap p (CommRingCat.ofHom f) [H] hsnc
end

theorem maxContactHypersurfaceBaseChange : MaxContactHypersurfaceBaseChange := by
  intro S L instL instCZ f hV hV' H hadm hsnc
  constructor
  rw [S.baseChange_structureMorphism L f, S.baseChange_ideal L f, S.baseChange_mult L f]
  intro hlft
  exact @isMaxContactHypersurface_comap_specMapOfFieldHom S.base L S.instField instL hV.charZero
    instCZ S.scheme S.structMap hV.smooth hV.locallyOfFiniteType f hlft S.ideal S.mult H
    (@hadm hV.locallyOfFiniteType)
  rw [S.baseChange_structureMorphism L f]
  exact @inStrictNormalCrossingPosition_comap_specMapOfFieldHom S.base L S.instField instL S.scheme S.structMap
    hV.smooth f H hsnc

end OrderReductionFieldBaseChange





def MaxContactIdealComapLeControlled : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X X1 : Sch)
      (p : X ⟶ Sp k) [Smooth p]
      [LocallyOfFiniteType p]
      (pi_ : X1 ⟶ X) (Z : ISD X) (E : Bdy X),
      HasStrictNormalCrossingsWith p Z E → IsBlowupAlongIdealSheaf pi_ Z →
      ∀ [IsLocallyNoetherian X1] [Smooth $ pi_ ≫ p]
        [LocallyOfFiniteType $ pi_ ≫ p]
        (A : ISD X) (mu_ : ℕ), 1 ≤ mu_ → A ≤ Z ^ mu_ →
      ∀ A1_ : ISD X1,
        exceptionalIdeal pi_ Z ^ mu_ * A1_ = comap A pi_ →
        comap (maxContactIdeal k p A mu_) pi_ ≤
          exceptionalIdeal pi_ Z * maxContactIdeal k (pi_ ≫ p) A1_ mu_

section
variable {k : Type} [Field k]
theorem smooth_projectionToBase_comp {V : Sch}
    {q : V ⟶ Sp k} [Smooth q] {A : ISD V}
    {mu_ : ℕ} {E : Bdy V} (u : MarkedSequenceOfBlowups q A mu_ E) (i : ℕ)
    (hi : i ≤ u.length) : Smooth $ u.projectionToBase i ≫ q := by
  revert hi
  induction i with
  | zero =>
    intro _
    rw [projectionToBase_zero]
    infer_instance
  | succ j ih =>
    intro hj1
    have hj : j < u.length := hj1
    have := ih hj.le
    rw [projectionToBase_succ, assoc]
    exact smooth_comp_of_isBlowupAlongIdealSheaf (u.center_snc j hj) $ u.isBlowupAlongIdealSheaf_blowupMorphism j hj

theorem maxContactIdeal_congr {X : Sch}
    (p p' : X ⟶ Sp k)
    [LocallyOfFiniteType p] [LocallyOfFiniteType p']
    (hp : p = p') (I J : ISD X) (hI : I = J) (m : ℕ) :
    maxContactIdeal k p I m = maxContactIdeal k p' J m := by
  subst hp
  subst hI
  rfl
end

theorem le_pow_one_of_le {X : Sch} {b Z : ISD X} (h : b ≤ Z) :
    b ≤ Z ^ 1 :=by simp_all
namespace MarkedSequenceOfBlowups

section
variable {k : Type} [Field k]
section
variable {V : Sch} {q : V ⟶ Sp k} {A : ISD V} {mu_ : ℕ} {E : Bdy V} (u : MarkedSequenceOfBlowups q A mu_ E) (hN : ∀ j : ℕ, j ≤ u.length → IsLocallyNoetherian (u.schemeAt j)) (i : ℕ) (hi : i < u.length) (b : IdealSheafData (u.schemeAt i)) (hb : b ≤ u.center i)
def weakTransform :
    IdealSheafData $ u.schemeAt $ i + 1 :=
  haveI : IsLocallyNoetherian $ u.schemeAt $ i + 1 := hN (i + 1) hi
  EmbeddedResolution.controlledTransform (u.transitionMapSucc i) (u.center i) b 1 (u.isBlowupAlongIdealSheaf_blowupMorphism i hi)
    (le_pow_one_of_le hb)

theorem weakTransform_unique
    (c : IdealSheafData $ u.schemeAt $ i + 1)
    (hc : exceptionalIdeal (u.transitionMapSucc i) (u.center i) * c = b.comap (u.transitionMapSucc i)) :
    c = u.weakTransform hN i hi b hb := by
  have := hN (i + 1) hi
  refine eq_controlledTransform_of_mul_eq_comap (u.transitionMapSucc i) (u.center i) b 1 (u.isBlowupAlongIdealSheaf_blowupMorphism i hi)
    (le_pow_one_of_le hb) c ?_
  simp_all
end

end

end MarkedSequenceOfBlowups

section
variable {k : Type} [Field k] {V : Sch} {q : V ⟶ Sp k}
section
variable [hv4_0 : LocallyOfFiniteType q] {A'} {mu_} {E'} (u : MarkedSequenceOfBlowups q A' mu_ E') (hN : ∀ i : ℕ, i ≤ u.length → IsLocallyNoetherian (u.schemeAt i))
include hv4_0
def strictTransformMaxContactIdeal :
    ∀ i : ℕ, IdealSheafData $ u.schemeAt i := fun i =>
  Nat.rec (motive := fun j => IdealSheafData $ u.schemeAt j)
    ((maxContactIdeal k q A' mu_).comap u.isoZero.hom)
    (fun j cj =>
      if h : j + 1 ≤ u.length then
        @idealSheafColon (u.schemeAt $ j + 1) (hN (j + 1) h) (cj.comap $ u.transitionMapSucc j)
          (exceptionalIdeal (u.transitionMapSucc j) $ u.center j)
      else ⊤) i

theorem strictTransformMaxContactIdeal_succ (i : ℕ) :
    strictTransformMaxContactIdeal u hN (i + 1) =
      if h : i + 1 ≤ u.length then
        @idealSheafColon (u.schemeAt $ i + 1) (hN (i + 1) h)
          ((strictTransformMaxContactIdeal u hN i).comap $ u.transitionMapSucc i)
          (exceptionalIdeal (u.transitionMapSucc i) $ u.center i)
      else ⊤ := rfl
end

def maxContactIdealAt [Smooth q]
    {A' : ISD V} {mu_ : ℕ} {E' : Bdy V}
    (u : MarkedSequenceOfBlowups q A' mu_ E') (i : ℕ) (hi : i ≤ u.length) : IdealSheafData $ u.schemeAt i :=
  haveI := smooth_projectionToBase_comp u i hi
  maxContactIdeal k (u.projectionToBase i ≫ q) (u.ideal i) mu_
end





namespace OrderReductionCorrectness

theorem blowupLiftEqOnControlledTransform : BlowupLiftEqOnControlledTransform := EmbeddedResolution.blowupLiftEqOnControlledTransform

theorem isLocallyNoetherian_schemeAt : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i ≤ s.length → AlgebraicGeometry.IsLocallyNoetherian (s.schemeAt i) := by
  intro T hT s i hi
  have :=
    p25 effectiveCartierSupportContainsNoComponent hT s i hi
  infer_instance

theorem maxContactIdealComapLeControlled : MaxContactIdealComapLeControlled := by
  intro k _ _ X X1 p _ _ pi_ Z E hZ hpi_ _ _ _ A mu_ hmu_ hA A1_ hA1_
  have key := comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p pi_ Z E hZ hpi_ A mu_ hA
    (mu_ - 1) $ sub_le mu_ 1
  have hsub : mu_ - (mu_ - 1) = 1 := by omega
  rw [hsub, pow_one] at key
  simp [maxContactIdeal_eq_derivIdealSheafIterate]
  rwa [eq_controlledTransform_of_mul_eq_comap pi_ Z A mu_ hpi_ hA A1_ hA1_]

theorem existsMaxContactControlledTransforms : ExistsMaxContactControlledTransforms :=
  by
    let h := maxContactIdealComapLeControlled
    intro k _ _ V q _ _ A' mu_ hmu_ E' u hN hcen
    have sm : ∀ i, i ≤ u.length → Smooth (u.projectionToBase i ≫ q) :=
      fun i hi => smooth_projectionToBase_comp u i hi
    have hcart : ∀ i, i < u.length →
        p17 (p5 (u.transitionMapSucc i) $ u.center i) := by
      intro i hi
      have := sm i hi.le
      exact ((isSmoothDivisor_iff (u.transitionMapSucc i ≫ (u.projectionToBase i ≫ q)) _).1
        (isSmoothDivisor_exceptionalIdeal (u.center_snc i hi) $ u.isBlowupAlongIdealSheaf_blowupMorphism i hi)).1
    have hcen' : ∀ i, (hi : i < u.length) →
        strictTransformMaxContactIdeal u hN i ≤ maxContactIdealAt u i hi.le → strictTransformMaxContactIdeal u hN i ≤ u.center i := by
      intro i hi hM
      have := sm i hi.le
      refine hcen i hi (strictTransformMaxContactIdeal u hN i) ?_
      let _a5 := u.schemeAt i
      have h1 :=
        u.center_order i hi
      let _m0 := ((maxContactIdealAt u i hi.le).support : Set _a5)
      have h2 : _m0 = orderAtLeastLocus (u.ideal i) mu_ := by
        show ((maxContactIdeal k (u.projectionToBase i ≫ q) (u.ideal i) mu_).support :
          Set _a5) = _
        rw [maxContactIdeal_eq_derivIdealSheafIterate]
        exact support_derivIdealSheafIterate_eq_orderAtLeastLocus k (u.projectionToBase i ≫ q) (u.ideal i) hmu_
      have h3 : _m0 ⊆
          ((strictTransformMaxContactIdeal u hN i).support : Set _a5) := by
        exact_mod_cast support_antitone hM
      rw [h2] at h3
      exact fun x hx => h3 $ h1 hx
    have heq' : ∀ i, i < u.length → strictTransformMaxContactIdeal u hN i ≤ u.center i →
        p5 (u.transitionMapSucc i) (u.center i) * strictTransformMaxContactIdeal u hN (i + 1) =
          (strictTransformMaxContactIdeal u hN i).comap (u.transitionMapSucc i) := by
      intro i hi hb
      have hi' : i + 1 ≤ u.length := hi
      let _a4 := u.schemeAt $ i + 1
      let _a6 := hN (i + 1) hi'
      have : IsLocallyNoetherian _a4 := _a6
      have hI :=
        comap_le_exceptionalIdeal_pow (u.transitionMapSucc i) $ le_pow_one_of_le hb
      rw [pow_one] at hI
      have hc : strictTransformMaxContactIdeal u hN (i + 1) =
          @idealSheafColon _a4 _a6
            ((strictTransformMaxContactIdeal u hN i).comap $ u.transitionMapSucc i)
            (p5 (u.transitionMapSucc i) $ u.center i) := by
        rw [strictTransformMaxContactIdeal_succ, dif_pos hi']
      rw [hc]
      exact (hcart i hi).mul_idealSheafColon hI
    have main : ∀ i, (hi : i ≤ u.length) → strictTransformMaxContactIdeal u hN i ≤ maxContactIdealAt u i hi := by
      intro i
      induction i with
      | zero =>
        intro hi
        have := sm 0 hi
        have : Smooth u.isoZero.hom := inferInstance
        have : Smooth $ u.isoZero.hom ≫ q := inferInstance
        let _a0 := maxContactIdeal k (u.projectionToBase 0 ≫ q) (u.ideal 0) mu_
        show strictTransformMaxContactIdeal u hN 0 ≤ _a0
        let _a2 := maxContactIdeal k (u.isoZero.hom ≫ q) (A'.comap u.isoZero.hom) mu_
        have e1 : _a0 =
            _a2 :=
          maxContactIdeal_congr _ _ (by rw [projectionToBase_zero]) _ _ u.ideal_zero mu_
        have e2 : _a2 =
            (maxContactIdeal k q A' mu_).comap u.isoZero.hom := by
          simp [maxContactIdeal_eq_derivIdealSheafIterate]
          exact derivIdealSheafIterate_comap k q u.isoZero.hom (mu_ - 1) A'
        rw [e1, e2]
        exact le_rfl
      | succ j ih =>
        intro hj1
        have hj : j < u.length := hj1
        have ihj := ih hj.le
        have hb := hcen' j hj ihj
        have hw : strictTransformMaxContactIdeal u hN (j + 1) = u.weakTransform hN j hj (strictTransformMaxContactIdeal u hN j) hb :=
          MarkedSequenceOfBlowups.weakTransform_unique u hN j hj (strictTransformMaxContactIdeal u hN j) hb
            (strictTransformMaxContactIdeal u hN $ j + 1) $ heq' j hj hb
        have := sm j hj.le
        have := sm (j + 1) hj1
        rw [hw]
        let b := strictTransformMaxContactIdeal u hN j
        let _a4 := u.schemeAt $ j + 1
        let _a9 := hN (j + 1) hj
        have : IsLocallyNoetherian _a4 := _a9
        have hassoc : u.transitionMapSucc j ≫ (u.projectionToBase j ≫ q) = u.projectionToBase (j + 1) ≫ q := by
          rw [← assoc, ← projectionToBase_succ]
        have : Smooth $ u.transitionMapSucc j ≫ (u.projectionToBase j ≫ q) := by
          rw [hassoc]
          infer_instance
        have : LocallyOfFiniteType $ u.transitionMapSucc j ≫ (u.projectionToBase j ≫ q) := by
          rw [hassoc]
          infer_instance
        let _a6 := u.center_snc j hj
        let _a1 := u.ideal $ j + 1
        let _a7 := u.isBlowupAlongIdealSheaf_blowupMorphism j hj
        have hstep' := h k (u.schemeAt j) _a4 (u.projectionToBase j ≫ q) (u.transitionMapSucc j)
          (u.center j) (u.boundary j) _a6 _a7
          (u.ideal j) mu_ hmu_ (le_pow_of_hasStrictNormalCrossingsWith (u.projectionToBase j ≫ q) (u.center j) (u.ideal j) (u.boundary j) _a6 mu_ $ u.center_order j hj) _a1 $ u.ideal_succ j hj
        have hM : maxContactIdeal k (u.transitionMapSucc j ≫ (u.projectionToBase j ≫ q)) _a1 mu_ =
            maxContactIdeal k (u.projectionToBase (j + 1) ≫ q) _a1 mu_ :=
          maxContactIdeal_congr _ _ hassoc _ _ rfl mu_
        rw [hM] at hstep'
        have h1 : p5 (u.transitionMapSucc j) (u.center j) * u.weakTransform hN j hj b hb = b.comap (u.transitionMapSucc j) := by
          have : IsLocallyNoetherian $ u.schemeAt $ j + 1 := _a9
          have h := exceptionalIdeal_pow_mul_controlledTransform (u.transitionMapSucc j) (u.center j) b 1
            _a7 $ le_pow_one_of_le hb
          rwa [pow_one] at h
        refine (((isSmoothDivisor_iff (u.transitionMapSucc j ≫ (u.projectionToBase j ≫ q)) _).1 $ isSmoothDivisor_exceptionalIdeal _a6 _a7).1).le_of_mul_le_mul ?_
        rw [h1]
        exact le_trans (comap_mono (u.transitionMapSucc j) ihj) hstep'
    exact ⟨strictTransformMaxContactIdeal u hN, rfl, fun i hi => heq' i hi $ hcen' i hi $ main i hi.le,
      fun i hi => hcen' i hi $ main i hi.le⟩

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_ideal :
    ∀ (T : MarkedIdealWithBoundary) (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ orderAtLeastLocus (s.ideal i) T.mult →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T s i
  induction i with
  | zero =>
      intro _ x hx
      rw [s.ideal_zero, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hx
      rwa [projectionToBase_zero]
  | succ n ih =>
      intro hn x hx
      have hn' := hn
      have h2 := ih (le_of_lt hn') _ $ OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (s.transitionMapSucc n) (s.center n) (s.isBlowupAlongIdealSheaf_blowupMorphism n hn') (s.ideal n) (s.ideal $ n + 1) T.mult (s.ideal_succ n hn') (s.center_order n hn') hx
      rwa [MarkedSequenceOfBlowups.projectionToBase_succ_apply]

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_center : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i < s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ (((s.center i).support : CSet $ s.schemeAt i)) →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T hT s i hi x hx
  exact projectionToBase_mem_orderAtLeastLocus_of_mem_ideal T s i (le_of_lt hi) x $ s.center_order i hi hx

end OrderReductionCorrectness




namespace MaxContactFunctoriality

theorem isPullback_of_orderAtLeastLocus_comap_eq_empty
    (hinv : ComapIsoInvariance) P A
    (T : MarkedIdealWithBoundary) (h : OrderReductionHypotheses P T)
    Y (ph_ : Y ⟶ T.scheme) [Smooth ph_]
    (n : SequenceOfBlowups Y) (hn : n.length = 0)
    (hempty : orderAtLeastLocus (T.ideal.comap ph_) T.mult = (∅ : Set ↥Y)) :
    IsPullbackBlowupSequence ph_ n (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have := h.valid.charZero
  have := h.valid.smooth
  let _a0 := maxContactPrincipalization hinv A T
  refine isPullback_of_length_zero_of_comap_center_eq_top ph_ n
    _a0.toSequenceOfBlowups hn ?_
  intro i hi ps_ hps_
  refine p39 ps_ (msCtr _a0 i) ?_
  intro y hy
  have hmem :=
    OrderReductionCorrectness.projectionToBase_mem_orderAtLeastLocus_of_mem_center T h.valid _a0 i hi
      (bsM ps_ y) hy
  have hfy : bsM ph_ y ∈ orderAtLeastLocus T.ideal T.mult := by
    have h1 : bsM ph_ y
        = bsM (msPrj _a0 i) (bsM ps_ y) := by
      rw [← hps_]
      rfl
    rwa [h1]
  have hcs := orderAtLeastLocus_comap T.base T.structMap ph_ T.ideal T.mult
  rw [hempty] at hcs
  have hy2 : y ∈ (∅ : Set Y) := by simp_all
  exact hy2.elim

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
end
end
noncomputable section
open CommRingCat (comp_apply ofHom)
open Equiv (symm_apply_apply ulift)
open Finset (iSup_finset_image image mem_image mem_image_of_mem notMem_empty)
open Flat (generalizingMap)
open FunctorialResolution.EmbeddedResolution (MaxOrderEq balancedTunedSheaf_eq isPullback_of_length_eq_zero_of_length_eq_zero maxContactIdeal_eq_derivIdealSheafIterate one_le_tuningExponent orderAtLeastLocus_comap_fieldBaseChange orderAtLeastLocus_eq_empty_of_comap_eq_empty orderLE_iff tuningExponent)
open FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData (embeddedInducedBlowupsWithoutIso_eq ofAffine toEmbeddedBlowupSequence_transitionsAreBlowups_iff)
open FunctorialResolution.EmbeddedResolution.BoundarySeparationByMaxContact (center_coverMarkedBlowupData_ne_top isAdmissible_coverTriple orderAtLeastLocus_coverMarkedBlowupData_eq_empty orderCertificate_coverMarkedBlowupData_of_mult_eq_one)
open FunctorialResolution.EmbeddedResolution.DivisorReduction (DivisorReductionHypotheses DivisorRestrictionFieldBaseChange EmptyPulledBackCenterCompatibility boundaryLocus_subset_preimage_otherBoundaryLocus boundaryLocus_subset_preimage_otherBoundaryLocus_succ ccI comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeio isOpen_preimage_support_containedComponentsIdeal isSmoothDivisor_boundary_comap_isoObjZero isSmoothDivisor_ker_embeddingIntoAmbient isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism lowerBoundaryAfterBlowup_fieldBaseChange lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary lowerIdealAfterBlowup_fieldBaseChange orderAtLeastLocus_comap_of_smooth preimageSupportEqComponentsInOrderLocus_of_isAdmissible projectionToSpec_eq_comp_ambientMarkedSeq projectionToSpec_eq_comp_prependedAmbientSeq support_containedComponentsIdeal_subset_support_boundary)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (SameNontrivialBoundary baseChange_boundary baseChange_ideal baseChange_mult bget' dim_baseChange isAdmissible_baseChange isAdmissible_pullbackAlong_of_smooth nontrivialPart pullbackAlong_ideal pullbackAlong_mult pullbackOverField_boundary_length sameNontrivialBoundary_iff transformAt_dim transformAt_dim_le validOfSameNontrivialBoundary withBoundary_ideal withBoundary_mult)
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups (projectionToBase_succ_apply projectionToSpec projectionToSpec_eq smooth_projectionToSpec)
open FunctorialResolution.EmbeddedResolution.MaxContactCoverData (balancedTunedIdeal_eq_balancedTunedSheaf chosenCoverData coverMap isAdmissible_coverTriple_of_validPullbackAlongSmooth isSmoothDivisor_coverMaxContactIdeal orderAt_balancedTunedIdeal_le_tunedMult tunedMult)
open FunctorialResolution.EmbeddedResolution.MaxContactFunctoriality (CoverFaithfullyFlat CoverSequenceProperties DescentHypotheses DropTrivialBoundaryAdmissible LoopCompatibleWithSmoothPullback MarkedOfMarkedDropTrivialBoundary MarkingDescends TrivialOnEmptyOrderLocus balancedTunedIdeal_eq_of_mult_eq_one coverMap_flat coverMap_surjective dropTrivialBoundaryPullback exists_isStrictPullback_cover_dropTrivialBoundary inStrictNormalCrossingPosition_of_triple_eq isAdmissible_and_dim_eq_withSchemeIdealBoundary_ker isLocalIsomorphism_map_coverBlowupSequence isLocallyNoetherian_schemeAt_coverBlowupSequence isMaxContactHypersurface_of_triple_eq isOrderReduction_maxContact_dim_le_of_descentHypotheses isPullbackBlowupSequence_reduceAlongHypersurface_lowerDimensionalFamily isPullback_of_orderAtLeastLocus_comap_eq_empty length_eq_zero_of_orderAtLeastLocus_eq_empty lowerDimensionalFamily maxContactPrincipalization maxContactPrincipalization_isPullbackBlowupSequence_of_smooth orderAtLeastLocus_comap_eq_empty orderAt_sequenceOfBlowups_ideal_le_mult reduceAlongHypersurface_toSequenceOfBlowups_heq removeUnitIdeals smoothPullbackTriple)
open FunctorialResolution.EmbeddedResolution.MaxContactOpenCover (isLocalIsomorphism_coverMap krullDimSucc_coverTriple_scheme_le_dim)
open FunctorialResolution.EmbeddedResolution.MaxContactReduction (dropTrivialBoundary dropTrivialBoundary_boundary dropTrivialBoundary_def dropTrivialBoundary_dim reduceAlongHypersurface)
open FunctorialResolution.EmbeddedResolution.NontrivialBoundary (pullbackWithNontrivialBoundary)
open FunctorialResolution.EmbeddedResolution.OrderReductionCorrectness (isLocallyNoetherian_schemeAt projectionToBase_mem_orderAtLeastLocus_of_mem_center)
open FunctorialResolution.EmbeddedResolution.OrderReductionFieldBaseChange (ValidBaseChange coverBaseChangeMap coverBaseFieldHom dropTrivialBoundaryBaseFieldHom dropTrivialBoundary_withBoundary_baseChange isStrictPullbackBlowupSeq_baseChange_withBoundary surjective_baseChange_fst)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (withoutIsoBlowups_isomorphic_self)
open Ideal (comap map_comap_of_surjective map_span mem_comap mul_mem_left span span_le)
open IsClosedImmersion (isAffine_surjective_of_isAffine lift lift_fac of_isPreimmersion of_surjective_of_isAffine)
open IsOpenImmersion (isoOfRangeEq isoOfRangeEq_hom_fac)
open Iso (inv_comp_eq inv_hom_id_assoc symm_hom trans_hom)
open Limits.pullback (condition fst snd)
open List (cons_append filter filter_cons filter_filter getElem_append_right getElem_map get_eq_getElem map map_cons mem_iff_getElem mem_singleton_self take)
open MorphismProperty (IsStableUnderBaseChange comp_mem of_isPullback)
open MvPolynomial (constantCoeff constantCoeff_C induction_on)
open Nat (le_of_succ_le)
open Opposite (op)
open QuasiSober (sober)
open Scheme (GSpecIso exists_affineOpens_mem_le preimage_basicOpen)
open Scheme.IdealSheafData (support)
open Set (mem_range range)
open Sum (elim)
open TopologicalSpace (Closeds)
open TopologicalSpace.NoetherianSpace (isCompact)
open ULift (up)
open Units (inv_mul)
section
open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution.OrderReductionProperties

theorem tunedSheafProperties : TunedSheafProperties :=
  tunedSheafProperties_of_succ_le_of_mul_le

theorem maxContactHypersurfacesEtaleEquivalent : MaxContactHypersurfacesEtaleEquivalent := by
  apply exists_etale_equalizing_isMaxContactHypersurface

theorem validPullbackAlongSmooth : OrderReduction.ValidPullbackAlongSmooth := by
  rw [OrderReduction.validPullbackAlongSmooth_iff]
  intro T hV Y q h hsm hqc hq
  exact isAdmissible_pullbackAlong_of_smooth T hV Y q h hq

theorem validBaseChange : OrderReductionFieldBaseChange.ValidBaseChange := by
  unfold ValidBaseChange
  intros
  apply isAdmissible_baseChange
  all_goals assumption

theorem orderAtBaseChangeEq : OrderReductionFieldBaseChange.OrderAtBaseChangeEq := by
  intro T L _ _ f hV y
  cases hV
  have : Smooth T.structMap := by assumption
  exact orderAt_comap_fieldBaseChange T.structMap (ofHom f) T.ideal y

theorem derivIdealSheafIter_comap_of_isPullback
    {k L : Type} [Field k] [Field L]
    {X Y : Sch} (pX : X ⟶ Sp k)
    (pY : Y ⟶ Sp L)
    [Smooth pX] [Smooth pY]
    (f : k →+* L) (q : Y ⟶ X)
    (hq : IsPullback q pY pX $ specMapOfFieldHom k L f)
    (I : ISD X) (r : ℕ) :
    derivIdealSheafIterate L pY r (I.comap q)
      = (derivIdealSheafIterate k pX r I).comap q := by
  let _c0 := m12 $ ofHom f
  have hspec : specMapOfFieldHom k L f = m12 (ofHom f) := rfl
  rw [hspec] at hq
  let _a0 := pullback.fst pX _c0
  obtain ⟨e, hfst, hsnd⟩ :
      ∃ e : Y ≅ pullback pX _c0,
        e.hom ≫ _a0 = q ∧
          e.hom ≫ pullback.snd pX _c0 = pY :=
    ⟨hq.isoPullback, hq.isoPullback_hom_fst, hq.isoPullback_hom_snd⟩
  clear hq
  subst hfst
  subst hsnd
  have : Smooth e.hom := inferInstance
  have h2 := derivIdealSheafIterate_comap L
      (pullback.snd pX _c0) e.hom r
      (I.comap _a0)
  have hc1 : I.comap (isoH e ≫ _a0)
      = (I.comap _a0).comap e.hom := by
    simp [comap_comp]
  let _a1 := derivIdealSheafIterate k pX r I
  have hc2 : _a1.comap
        (isoH e ≫ _a0)
      = (_a1.comap
          _a0).comap e.hom := by
    simp [comap_comp]
  rw [hc1, hc2, h2, derivIdealSheafIterate_comap_fieldBaseChange pX (ofHom f) r I]

section
variable {X : Sch}
section
variable (L : Bdy X)
private theorem filterNeTop_cons_top :
    filterNeTop ((⊤ : ISD X) :: L) = filterNeTop L := by
  simp [filterNeTop]

theorem removeUnitIdeals_eq_nontrivialPart :
    removeUnitIdeals L = nontrivialPart L := by
  unfold removeUnitIdeals nontrivialPart
  congr 1
  funext D
  by_cases hD : D = ⊤ <;> simp [hD]

theorem sameNontrivialBoundary_removeUnitIdeals :
    SameNontrivialBoundary (removeUnitIdeals L) L := by
  rw [sameNontrivialBoundary_iff, removeUnitIdeals_eq_nontrivialPart]
  simp [nontrivialPart, filter_filter]
end

private theorem filterNeTop_cons_of_ne_top
    {D : ISD X} (hD : D ≠ ⊤) (L : Bdy X) :
    filterNeTop (D :: L) = D :: filterNeTop L := by
  simp [filterNeTop, hD]
end

section
variable (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible)
include hV
theorem isBalanced_baseChange
    (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
    (hft : LocallyOfFiniteType (T.bc f).structMap)
    (hB : T.IsBalanced hV.locallyOfFiniteType) :
    (T.bc f).IsBalanced hft := by
  have hlft := hV.locallyOfFiniteType
  have hsm : Smooth T.structMap := by
    clear hB
    cases hV
    assumption
  have hft' := hft
  let _a0 := m12 $ ofHom f
  have hgoal : IsDerivBalanced K
      (snd T.structMap
        _a0)
      (T.ideal.comap $ fst T.structMap
        _a0) T.mult := by
    apply isDerivBalanced_of_pow_le
    intro i hi
    rw [derivIdealSheafIterate_comap_fieldBaseChange (L := K) T.structMap
        (ofHom f) i T.ideal,
      ← comap_pow,
      ← comap_pow]
    apply comap_mono
    exact FunctorialResolution.EmbeddedResolution.IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hB hi
  exact hgoal

theorem isAdmissible_withBoundary_ker_of_isSmoothDivisor
    {Y} (e : Y ⟶ T.scheme) [IsClosedImmersion e]
    (hD : IsSmoothDivisor T.structMap $ ker e) :
    (T.withBoundary [ker e]).IsAdmissible := by
  have hsm : Smooth T.structMap := by
    cases hV
    assumption
  have hcz : CharZero T.base := by
    cases hV
    assumption
  have hsnc :=
    inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor T.structMap (m149 e) hD
  cases hV
  constructor <;> assumption
end

theorem isBaseChangeInherited P : IsBaseChangeInherited P := by
  unfold FunctorialResolution.EmbeddedResolution.IsBaseChangeInherited
  intro T L _ _ f hV hP hO hB
  have := f.charZero
  refine ⟨isAdmissible_baseChange T hV L f, ?_, ?_, ?_⟩
  rwa [dim_baseChange T hV L f]
  intro y
  have hsm : Smooth T.structMap := by
    cases hV
    assumption
  have := hsm
  have key := orderAt_comap_fieldBaseChange (k := T.base) (L := L) T.structMap
    (ofHom f) T.ideal y
  exact key.trans_le $ hO _
  intro hft
  exact isBalanced_baseChange T hV L f hft $ hB _

theorem coverFaithfullyFlat P :
    CoverFaithfullyFlat P := by
  intro T h
  exact ⟨coverMap_surjective tunedSheafProperties T h,
    coverMap_flat T h⟩

section
variable {P : CategoryTheory.MorphismProperty Sch} [IsStableUnderBaseChange P] {X Y S : Sch} (f : X ⟶ S) (g : Y ⟶ S)
theorem pullback_snd_of_isStableUnderBaseChange (hf : P f) :
    P $ pullback.snd f g :=
  of_isPullback (P := P)
    (of_hasPullback f g) hf

theorem pullback_fst_of_isStableUnderBaseChange (hg : P g) :
    P $ pullback.fst f g :=
  of_isPullback (P := P)
    (of_hasPullback f g).flip hg
end

theorem isMaxContactInvariant_balancedTunedSheaf (htf : TunedSheafProperties)
    (k : Type) [Field k] [CharZero k] {X : Sch}
    (p : X ⟶ Sp k) [Smooth p]
    [LocallyOfFiniteType p] (I : ISD X) (m : ℕ)
    (hm : 1 ≤ m) (hmax : MaxOrderEq I m) :
    IsMaxContactInvariant k p (balancedTunedSheaf k p I m) $ tuningExponent m := by
  apply isMaxContactInvariant_of_mul_le
  rw [maxContactIdeal_eq_derivIdealSheafIterate, balancedTunedSheaf_eq]
  exact htf.derivIdealSheafIter_mul_derivIdealSheaf_le_tunedSheaf k X p I m hm hmax
    (tuningExponent m) $ one_le_tuningExponent m

theorem isMaxContactInvariantBalancedTuned_of_tunedSheafProperties (htf : TunedSheafProperties) :
    BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned := by
  unfold FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned
  intros
  apply isMaxContactInvariant_balancedTunedSheaf htf
  all_goals assumption

theorem filterNeTop_map_filter_append {X Y : Sch}
    (f : ISD X → ISD Y) (hf : f ⊤ = ⊤)
    (p : ISD X → Bool)
    (hp : ∀ D : ISD X, p D = false → D = ⊤)
    (R : Bdy Y) (L : Bdy X) :
    filterNeTop (map f (filter p L) ++ R)
      = filterNeTop (map f L ++ R) := by
  induction L with
  | nil => rfl
  | cons D L ih =>
      by_cases hpD : p D = true
      rw [filter_cons, if_pos hpD, map_cons, map_cons,
        cons_append, cons_append]
      by_cases hfD : f D = ⊤
      rwa [hfD, filterNeTop_cons_top, filterNeTop_cons_top]
      rw [filterNeTop_cons_of_ne_top hfD, filterNeTop_cons_of_ne_top hfD, ih]
      have hDtop := hp D $ by simpa using hpD
      rw [filter_cons, if_neg hpD, map_cons, cons_append, hDtop, hf,
        filterNeTop_cons_top]
      exact ih

theorem filterNeTop_boundary_filter {X : Sch}
    (d : BlowupSequenceData X) (p : ISD X → Bool)
    (hp : ∀ D : ISD X, p D = false → D = ⊤)
    (L : Bdy X) (i : ℕ) :
    filterNeTop (d.boundaryFrom (filter p L) i)
      = filterNeTop (d.boundaryFrom L i) := by
  rw [BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append d (filter p L) i,
    BlowupSequenceData.boundary_eq_map_iteratedStrictTransform_append d L i]
  exact filterNeTop_map_filter_append (d.iteratedStrictTransform i)
    (d.iteratedStrictTransform_top i) p hp (d.boundaryFrom [] i) L

theorem isMarked_of_isMarked_dropTrivialBoundary (T : MarkedIdealWithBoundary) (_hV : T.IsAdmissible)
    (d : BlowupSequenceData T.scheme) I m
    (h : d.IsMarked T.structMap I m (dropTrivialBoundary T).boundary) :
    d.IsMarked T.structMap I m T.boundary := by
  refine ⟨h.divisible, h.center_order, h.center_smooth, ?_⟩
  intro i hi
  refine hasStrictNormalCrossingsWith_of_filterNeTop_eq _ _ _ _ ?_ $ h.center_snc i hi
  rw [dropTrivialBoundary_boundary]
  refine filterNeTop_boundary_filter d _ ?_ T.boundary i
  intro D hD
  simpa using hD

theorem derivIdealSheafIterate_comm_baseChange : DerivIdealSheafIterateCommBaseChange := by
  unfold DerivIdealSheafIterateCommBaseChange
  intros
  apply derivIdealSheafIter_comap_of_isPullback <;> assumption

theorem forall_isAdmissible_dropTrivialBoundary : DropTrivialBoundaryAdmissible := by
  intro T hV
  have key : ∀ L,
      SameNontrivialBoundary T.boundary L → tAd (tWB T L) := by
    intro L hL
    apply validOfSameNontrivialBoundary <;> assumption
  rw [dropTrivialBoundary_def]
  apply key
  rw [sameNontrivialBoundary_iff]
  simp [nontrivialPart, filter_filter]
  congr 1
  funext D
  by_cases hD : D = ⊤ <;> simp [hD]

theorem forall_isMarked_of_isMarked_dropTrivialBoundary : MarkedOfMarkedDropTrivialBoundary := by
  intro T hV d h
  exact isMarked_of_isMarked_dropTrivialBoundary T hV d T.ideal T.mult h

theorem orderCertificateLocalToGlobal : OrderCertificateLocalToGlobal := by
  intro k _ W p N mu_ Mem Z h
  exact FunctorialResolution.EmbeddedResolution.OrderCertificate.localize (fun z _ => (h z).choose)
    (fun z _ => (h z).choose_spec.1) fun z _ => (h z).choose_spec.2

theorem isSmoothDivisorStableUnderSmoothPullback : IsSmoothDivisorStableUnderSmoothPullback := by
  unfold FunctorialResolution.EmbeddedResolution.IsSmoothDivisorStableUnderSmoothPullback
  intros
  exact isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition _ _ _
      (inStrictNormalCrossingPosition_singleton_of_isSmoothDivisor _ _ $ by assumption) _
      (mem_singleton_self _)

theorem maxContactHypersurfaceSmoothPullback : BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback :=
  by
    intro k hk hk0 P p hsp hfp Y g hsg hfg A mu_ hmu_ H hH
    exact IsMaxContactHypersurface.comap_of_isSmoothDivisorStableUnderSmoothPullback g isSmoothDivisorStableUnderSmoothPullback
      (IsMaxContactHypersurface.isSmoothDivisor hH) hH hmu_

theorem orderReductionHypotheses : OrderReduction.OrderReductionHypotheses := by
  refine ⟨EmbeddedResolution.OrderReductionCorrectness.existsMaxContactControlledTransforms, projectionToBase_mem_orderAtLeastLocus_of_mem_center, ?_, ?_, isLocallyNoetherian_schemeAt, EmbeddedResolution.OrderReductionCorrectness.blowupLiftEqOnControlledTransform, smoothSubschemeIdealIsRadical, maxContactHypersurfacesEtaleEquivalent, ?_, ?_⟩
  intro T hT Y q f _ hq _ _ hbal
  subst hq
  have := hT.smooth
  refine isDerivBalanced_of_pow_le T.base (f ≫ tMp T) ?_
  intro i hi
  rw [derivIdealSheafIterate_comap T.base T.structMap f i T.ideal,
    ← comap_pow, ← comap_pow]
  exact comap_mono f $ IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hi
  intro V W f hf hN hdim
  have := hf
  have := hN
  exact krullDimSucc_le_of_etale f hdim
  intro X' X ph_ s' s hpb hne hran
  exact hpb.isStrictPullback_of_support_comap_center_nonempty $ support_comap_center_nonempty_of_mem_range ph_ s hne hran
  intro T hV Y q h hsm hqc hq
  have := hsm
  have := hqc
  exact isAdmissible_pullbackAlong_of_smooth T hV Y q h hq

theorem maxContactCoverProperties : MaxContactCoverProperties :=
  by
    refine
      { strictTransform_admissible := ?_
        coSupport_le_preimage := ?_
        schemeDim_level_le := ?_
        exists_goodCover := ?_
        hasSNCWith_cons := ?_
        valid_level := ?_
        orderAt_level_le := ?_
        coverTriple_dim_le := ?_
        coverTriple_valid := ?_
        coverContact_admissible := ?_
        coverContact_snc := ?_
        tuning := tunedSheafProperties }
    intro k _ _ P P1 p _ _ _ pi_ _ Z E hZ hpi_ A A1_ mu_ hmu_ hordA hsupp htr H hH
    exact isMaxContactHypersurface_strictTransform_of_orderAt_le k p pi_ Z E hZ hpi_ A A1_ mu_ hmu_ hordA
      hsupp htr H hH
    intro X X1 pi_ Z hpi_ A A1_ mu_ htr hsupp
    exact FunctorialResolution.EmbeddedResolution.OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf pi_ Z hpi_ A A1_ mu_ htr hsupp
    intro T hT s i hi
    exact (EmbeddedResolution.dimensionNonincreasingAlongBlowups) T hT s i hi
    intro T hv hord
    exact MaxContactOpenCover.exists_isMaxContactCover T hv $ orderAt_balancedTunedIdeal_le_tunedMult tunedSheafProperties T hv hord
    intro k _ P p _ Z H N _hsmZ hsnc hZN hHZ
    exact hasStrictNormalCrossingsWith_cons_of_le p Z H N hsnc hZN hHZ
    intro T hT s i hi
    exact p38 effectiveCartierSupportContainsNoComponent hT s i hi
    intro T hT hord s i hi x
    exact orderAt_ideal_le_mult_along_sequence T hT hord s i hi x
    intro T hv
    exact krullDimSucc_coverTriple_scheme_le_dim T hv
    intro T hv _hord hgood
    exact isAdmissible_coverTriple_of_validPullbackAlongSmooth validPullbackAlongSmooth T hv hgood
    intro T hv hgood _
    exact MaxContactCoverGeometry.isMaxContactHypersurface_coverMaxContactIdeal T hv hgood
    intro T hv hgood
    exact MaxContactCoverGeometry.inStrictNormalCrossingPosition_of_isMaxContactCover T hv hgood
      (isSmoothDivisor_coverMaxContactIdeal validPullbackAlongSmooth T hv hgood)

section
variable (hinv : ComapIsoInvariance)
theorem coverSequenceProperties_of_isBoundaryDivisorReduction n
    A L
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L) :
    CoverSequenceProperties hinv (fun d => d ≤ n) A := by
  have hmono : ∀ a b, a ≤ b → b ≤ n → a ≤ n := fun _ _ hab hb => le_trans hab hb
  have hstar := maxContactCoverProperties
  have hin := orderReductionHypotheses
  have hopen :=
    fun k inst => @openImmersionStability k inst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  intro T h i hi
  exact center_coverMarkedBlowupData_ne_top hstar hinv (· ≤ n) hmono A L
    hdiv T h i hi
  intro T h hmult i hi
  exact orderCertificate_coverMarkedBlowupData_of_mult_eq_one hstar hopen hinv
    (· ≤ n) hmono A L hdiv T h hmult i hi
  intro T h
  exact FunctorialResolution.EmbeddedResolution.MaxContactCoverDescent.exists_isStrictPullback_coverMarkedSequence hstar hin hinv
    (· ≤ n) hmono A L hdiv
    (isMaxContactInvariantBalancedTuned_of_tunedSheafProperties tunedSheafProperties) maxContactHypersurfaceSmoothPullback T h
  intro T h hbd hmult Y q e hei _hq hD J _hJv hJ
  exact isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isSmoothDivisor hstar hin hinv
    (· ≤ n) hmono A L hdiv T h hbd hmult e hD J hJ
    (isAdmissible_withBoundary_ker_of_isSmoothDivisor T h.valid e hD)
  intro T h
  exact orderAtLeastLocus_coverMarkedBlowupData_eq_empty hstar hinv (· ≤ n) hmono
    A L hdiv T h

section
variable (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment)
theorem markingDescends :
    MarkingDescends hinv P A := by
  unfold MarkingDescends
  intro T h d hd
  have hv := h.valid
  have hcz : CharZero T.base := by
    cases hv
    assumption
  have hsm : Smooth T.structMap := by
    cases hv
    assumption
  have hlft := hv.locallyOfFiniteType
  have hsurj :=
    coverMap_surjective tunedSheafProperties T h
  have hoi :=
    isLocalIsomorphism_coverMap T hv
  have hlev := isLocallyNoetherian_schemeAt_coverBlowupSequence hinv A maxContactCoverProperties T h d hd
  have hmax : MaxOrderEq T.ideal T.mult :=
    ⟨(orderLE_iff T.ideal T.mult).2 h.orderLE, h.coSupport_nonempty⟩
  have key := isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq hinv P A T h hoi (one_le_tuningExponent T.mult) d hd hlev.1 hlev.2
    (fun D i hi =>
      isLocalIsomorphism_map_coverBlowupSequence hinv A T h d D i hi)
  have htuned :=
    balancedTunedIdeal_eq_balancedTunedSheaf T hv
  have htm : tunedMult T = tuningExponent T.mult := rfl
  have key2 := key
  rw [htm, htuned] at key2
  exact mpr_ ((tunedSheafProperties.isMarked_tuned_iff T.base T.scheme T.structMap T.ideal T.mult
    hv.one_le_mult hmax T.boundary d).1) key2
end

section
variable (n : ℕ) (A : ℕ → PrincipalizationAssignment)
section
variable (L : PrincipalizationAssignment) (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
include hdiv
theorem maxContact_isPullback_of_smooth_of_orderAt_le_mult
    (hshift : IsBoundaryPositionInvariant (fun d => d ≤ n) A)
    (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hP : T.krullDimSucc ≤ n)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ENat))
    (Y : Sch) q (h : Y ⟶ T.scheme)
    [Smooth h] (hq : h ≫ T.structMap = q)
    E'
    (hE : SameNontrivialBoundary (T.pbA q h).boundary E')
    (hV' : (T.pbB q h E').IsAdmissible)
    (hP' : (T.pbB q h E').krullDimSucc ≤ n)
    (hO' : ∀ x : ↥(T.pbB q h E').scheme,
      orderAt (T.pbB q h E').ideal x ≤ (T.mult : ENat)) :
    IsPullbackBlowupSequence h
      (maxContactPrincipalization hinv A
        (T.pbB q h E')).toSequenceOfBlowups
      (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  let _a0 := T.pbB q h E'
  have hcz : CharZero T.base := by
    cases hV
    assumption
  have hsm : Smooth T.structMap := by
    cases hV
    assumption
  have hflat : Flat h := inferInstance
  have hidS :=
    (withBoundary_ideal (T.pbA q h) E').trans
      (pullbackAlong_ideal T Y q h)
  have hmultS :=
    (withBoundary_mult (T.pbA q h) E').trans
      (pullbackAlong_mult T Y q h)
  have hordBound : ∀ x,
      orderAt _a0.ideal x
        ≤ (_a0.mult : ENat) := by
    intro x
    rw [hmultS]
    exact hO' x
  have hvan : TrivialOnEmptyOrderLocus hinv (· ≤ n) A := by
    unfold TrivialOnEmptyOrderLocus
    intros
    apply isPullback_of_orderAtLeastLocus_comap_eq_empty hinv
      (· ≤ n) A
    all_goals assumption
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  have hempS : orderAtLeastLocus _a0.ideal
      _a0.mult = ∅ := by
    rw [hidS, hmultS]
    exact orderAtLeastLocus_comap_eq_empty T hV h hemp
  refine isPullback_of_length_eq_zero_of_length_eq_zero h _ _ ?_ ?_
  exact length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (· ≤ n) A
    _a0 hV' hP' hordBound hempS
  exact length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (· ≤ n) A
    T hV hP hO hemp
  have hne := mpr_ nonempty_iff_ne_empty hemp
  have hyp : p26 (· ≤ n) T := ⟨hP, hO, hne, hV⟩
  by_cases hempS : orderAtLeastLocus (T.ideal.comap h) T.mult = ∅
  have hempS' : orderAtLeastLocus _a0.ideal
      _a0.mult = ∅ := by
    rwa [hidS, hmultS]
  have hz :=
    length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (· ≤ n) A
      _a0 hV' hP' hordBound hempS'
  exact isPullback_of_orderAtLeastLocus_comap_eq_empty hinv
    (· ≤ n) A T hyp Y h
    (maxContactPrincipalization hinv A
      _a0).toSequenceOfBlowups hz hempS
  have hneS : (orderAtLeastLocus _a0.ideal
      _a0.mult).Nonempty := by
    rw [hidS, hmultS]
    exact mpr_ nonempty_iff_ne_empty hempS
  have _hypS : p26 (· ≤ n)
      _a0 := ⟨hP', hordBound, hneS, hV'⟩
  have htrimv := forall_isAdmissible_dropTrivialBoundary T hV
  have hpbv : tAd (dropTrivialBoundaryPullback T q h E') := by
    unfold dropTrivialBoundaryPullback
    let S := T.pbA q h
    let hV := hV'
    have hEF := sy_ (sameNontrivialBoundary_removeUnitIdeals E')
    have h2 : (tWB (tWB S E') (removeUnitIdeals E')).IsAdmissible := by
      apply validOfSameNontrivialBoundary <;> assumption
    exact h2
  have hyppb : p26 (· ≤ n)
      (dropTrivialBoundaryPullback T q h E') :=
    ⟨hP', hordBound, hneS, hpbv⟩
  have hcoverAdm :=
    isAdmissible_coverTriple maxContactCoverProperties (· ≤ n) _ (hyp.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary)
  have hPv :=
    isAdmissible_coverTriple maxContactCoverProperties (· ≤ n) _ hyppb
  have hnC := hcoverAdm.isNoetherian
  have hnP :=
    hPv.isNoetherian
  have hnPt : IsNoetherian
      (chosenCoverData
        (dropTrivialBoundaryPullback T q h E') hpbv).disjointUnion :=
    hPv.isNoetherian
  have hlnPt : IsLocallyNoetherian
      (chosenCoverData
        (dropTrivialBoundaryPullback T q h E') hpbv).disjointUnion :=
    inferInstance
  let _a4 := coverTriple (dropTrivialBoundary T) htrimv
  have hqcStruct : QuasiCompact
      _a4.structMap := by
    constructor
    intro U hU hU2
    have hns : m86
        _a4.scheme := inferInstance
    exact @isCompact _ _ hns _
  let _a5 := CategoryTheory.CategoryStruct.comp (coverMap (dropTrivialBoundaryPullback T q h E') hpbv) h
  have hqcf : QuasiCompact
      _a5 := by
    constructor
    intro U hU hU2
    have hns : m86
        (coverTriple
          (dropTrivialBoundaryPullback T q h E') hpbv).scheme :=
      inferInstance
    exact @isCompact _ _ hns _
  let _a3 := coverMap (dropTrivialBoundary T) htrimv
  have hqcSnd : QuasiCompact
      (snd
        _a5
        _a3) :=
    pullback_snd_of_isStableUnderBaseChange (P := @AlgebraicGeometry.QuasiCompact.{0}) _ _
      hqcf
  have hetFst : Etale
      (fst
        _a5
        _a3) :=
    pullback_fst_of_isStableUnderBaseChange (P := @AlgebraicGeometry.Etale.{0}) _ _
      (etale_coverMap_of_isAdmissible (dropTrivialBoundary T) htrimv)
  have hdimQ := krullDimSucc_le_of_etale
    (fst
      _a5
      _a3)
    hPv.topologicalKrullDim_lt_top
  have hdimfp : krullDimSucc
      (m131
        _a5
        _a3)
      ≤ tDim (T.pbA q h) := by
    refine le_trans hdimQ ?_
    refine le_trans (krullDimSucc_coverTriple_scheme_le_dim _ hpbv) ?_
    exact le_of_eq rfl
  refine maxContactPrincipalization_isPullbackBlowupSequence_of_smooth
    hinv (· ≤ n) (fun _ _ hab hb => le_trans hab hb) A L hdiv hshift
    maxContactCoverProperties orderReductionHypotheses (isMaxContactInvariantBalancedTuned_of_tunedSheafProperties tunedSheafProperties)
    maxContactHypersurfaceSmoothPullback ?_ hvan
    (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv) (markingDescends hinv (· ≤ n) A)
    (coverFaithfullyFlat (· ≤ n)) forall_isAdmissible_dropTrivialBoundary forall_isMarked_of_isMarked_dropTrivialBoundary
    T hV hP hO q h hq E' hE hV' hP' htrimv hpbv
    (comp_mem (@AlgebraicGeometry.QuasiCompact.{0}) _ _ hqcSnd hqcStruct)
    hdimfp
  unfold LoopCompatibleWithSmoothPullback
  intro hstar hin hMC hAdm hmono B hspec hshift T T' hPdimT hPdimOther S hV hO hdimS H hH hHsnc hlive
    X' q hsm hV' hdim' hH' hH'snc
  have : Smooth q := hsm
  have heq : smoothPullbackTriple S q = pullbackWithNontrivialBoundary S q := by
    unfold smoothPullbackTriple pullbackWithNontrivialBoundary
    rw [removeUnitIdeals_eq_nontrivialPart]
    rfl
  have hV2 : tAd (pullbackWithNontrivialBoundary S q) := by simp_all
  have hdim2 : tDim (pullbackWithNontrivialBoundary S q) ≤ tDim T' := by simp_all
  have hH2 : ∀ [inst : LocallyOfFiniteType
        (pullbackWithNontrivialBoundary S q).structMap],
      FunctorialResolution.EmbeddedResolution.IsMaxContactHypersurface (pullbackWithNontrivialBoundary S q).base
        (pullbackWithNontrivialBoundary S q).structMap (pullbackWithNontrivialBoundary S q).ideal
        (pullbackWithNontrivialBoundary S q).mult (cmI H q) := by
    intro inst
    have hft2 : LocallyOfFiniteType
        (smoothPullbackTriple S q).structMap := inst
    exact isMaxContactHypersurface_of_triple_eq heq.symm inst hft2
      (cmI H q) (cmI H q) m129 hH'
  have hH2snc :=
    inStrictNormalCrossingPosition_of_triple_eq heq.symm [cmI H q] [cmI H q]
      m129 hH'snc
  have hmain := isPullbackBlowupSequence_reduceAlongHypersurface_lowerDimensionalFamily hstar
    hin hMC hAdm hinv (· ≤ n) hmono A B hspec hshift T T' hPdimT hPdimOther S hV hO hdimS hlive H hH hHsnc q hV2
    hdim2 hH2 hH2snc
  have hstep :=
    eq_of_heq (reduceAlongHypersurface_toSequenceOfBlowups_heq hinv T'
      (lowerDimensionalFamily A T') heq (cmI H q) (cmI H q) m129)
  exact Eq.mpr (congrArg (fun z => IsPullbackBlowupSequence q z
    (mbSq (reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S
      H))) hstep) hmain

section
variable (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hP : T.krullDimSucc ≤ n) (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ENat)) (K : Type) [Field K] [CharZero K] (f : T.base →+* K) (E' : List (T.baseChange K f).scheme.IdealSheafData) (hE : SameNontrivialBoundary (T.baseChange K f).boundary E') (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible) (hP' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
include hV hP hO hE hV' hP'
theorem isStrictPullbackBlowupSeq_maxContact_baseChange :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base K f))
      (maxContactPrincipalization hinv A
        ((T.bc f).withBoundary E')).toSequenceOfBlowups
      (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  let _a8 := bcT T f
  let _a0 := tWB _a8 E'
  have hcz := f.charZero
  have hsm : Smooth T.structMap := by
    cases hV
    assumption
  let _a7 := specMapOfFieldHom T.base K f
  have hflat0 : Flat _a7 := inferInstance
  let _a4 := pullback.fst T.structMap _a7
  have hflat : Flat
      _a4 :=
    pullback_fst_of_isStableUnderBaseChange (P := @AlgebraicGeometry.Flat.{0}) _ _ hflat0
  have hordS : ∀ x,
      orderAt _a0.ideal x
        = orderAt T.ideal (_a4 x) :=
    orderAt_comap_fieldBaseChange T.structMap (ofHom f) T.ideal
  have hcsS : orderAtLeastLocus _a0.ideal
      _a0.mult
      = _a4 ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    orderAtLeastLocus_comap_fieldBaseChange T.structMap (ofHom f) T.ideal T.mult
  have hordBound : ∀ x,
      orderAt _a0.ideal x
        ≤ (tMu _a0 : ENat) := by
    intro x
    rw [hordS x]
    exact hO _
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  have hempS : orderAtLeastLocus _a0.ideal
      _a0.mult = ∅ := by
    rw [hcsS, hemp]
    exact preimage_empty
  exact FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.of_length_zero _ _ _ (length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (· ≤ n) A _a0 hV' hP' hordBound hempS) (length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (· ≤ n) A T hV hP hO hemp)
  have hne := mpr_ nonempty_iff_ne_empty hemp
  have hyp : p26 (· ≤ n) T := ⟨hP, hO, hne, hV⟩
  have hneS : (orderAtLeastLocus _a0.ideal
      _a0.mult).Nonempty := by
    rw [hcsS]
    exact Set.Nonempty.preimage hne
      (surjective_baseChange_fst T K f).1
  have hypS : p26 (· ≤ n)
      _a0 := ⟨hP', hordBound, hneS, hV'⟩
  have htrimv := forall_isAdmissible_dropTrivialBoundary T hV
  have hypA : p26 (· ≤ n)
      ((dropTrivialBoundary T).baseChange K
        (dropTrivialBoundaryBaseFieldHom T K f)) := by
    rw [← dropTrivialBoundary_withBoundary_baseChange T K f E' hE]
    exact hypS.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary
  have hA'v := hypA.valid
  have hcoverAdm :=
    isAdmissible_coverTriple maxContactCoverProperties (· ≤ n) _ (hyp.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary)
  let _a6 := coverBaseFieldHom (dropTrivialBoundary T) htrimv K $ dropTrivialBoundaryBaseFieldHom T K f
  have hCbcv :=
    isAdmissible_baseChange _ hcoverAdm K
      _a6
  have hnD := (isAdmissible_coverTriple maxContactCoverProperties (· ≤ n) _ hypA).isNoetherian
  have hnC := hCbcv.isNoetherian
  have hqcCover : QuasiCompact
      (coverMap
        ((dropTrivialBoundary T).baseChange K
          (dropTrivialBoundaryBaseFieldHom T K f)) hA'v) := by
    constructor
    intro U hU hU2
    have hns : m86
        (coverTriple
          ((dropTrivialBoundary T).baseChange K
            (dropTrivialBoundaryBaseFieldHom T K f)) hA'v).scheme := inferInstance
    exact @isCompact _ _ hns _
  let _a2 := (coverTriple (dropTrivialBoundary T) htrimv).baseChange K _a6
  have hqcCbc : QuasiCompact
      _a2.structMap := by
    constructor
    intro U hU hU2
    have hns : m86
        _a2.scheme := inferInstance
    exact @isCompact _ _ hns _
  let _a3 := coverBaseChangeMap (dropTrivialBoundary T) htrimv K $ dropTrivialBoundaryBaseFieldHom T K f
  have hqcSnd : QuasiCompact
      (pullback.snd
        (coverMap
          ((dropTrivialBoundary T).baseChange K
            (dropTrivialBoundaryBaseFieldHom T K f)) hA'v)
        _a3) :=
    pullback_snd_of_isStableUnderBaseChange (P := @AlgebraicGeometry.QuasiCompact.{0}) _ _
      hqcCover
  have hetSnd : Etale
      (pullback.snd
        (coverMap
          ((dropTrivialBoundary T).baseChange K
            (dropTrivialBoundaryBaseFieldHom T K f)) hA'v)
        _a3) :=
    pullback_snd_of_isStableUnderBaseChange (P := @AlgebraicGeometry.Etale.{0}) _ _
      inferInstance
  have hdimChart : _a2.krullDimSucc ≤ _a8.krullDimSucc := by
    rw [dim_baseChange _ hcoverAdm, dim_baseChange T hV]
    have h1 := krullDimSucc_coverTriple_scheme_le_dim (dropTrivialBoundary T) htrimv
    rwa [dropTrivialBoundary_dim] at h1
  have hdimQ := krullDimSucc_le_of_etale
    (pullback.snd
      (coverMap
        ((dropTrivialBoundary T).baseChange K
          (dropTrivialBoundaryBaseFieldHom T K f)) hA'v)
      _a3)
    hCbcv.topologicalKrullDim_lt_top
  exact isStrictPullbackBlowupSeq_baseChange_withBoundary
    maxContactCoverProperties orderReductionHypotheses (isMaxContactInvariantBalancedTuned_of_tunedSheafProperties tunedSheafProperties)
    maxContactHypersurfaceSmoothPullback derivIdealSheafIterate_comm_baseChange validBaseChange orderAtBaseChangeEq
    EmbeddedResolution.OrderReductionFieldBaseChange.maxContactHypersurfaceBaseChange hinv (· ≤ n)
    (fun _ _ hab hb => le_trans hab hb) A L hdiv (isBaseChangeInherited (· ≤ n))
    (coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv) (markingDescends hinv (· ≤ n) A)
    (coverFaithfullyFlat (· ≤ n)) forall_isAdmissible_dropTrivialBoundary forall_isMarked_of_isMarked_dropTrivialBoundary
    T hV hP hO K f E' hE hV' hP' hdimChart
    (comp_mem (@AlgebraicGeometry.QuasiCompact.{0}) _ _ hqcSnd hqcCbc)
    (le_trans hdimQ hdimChart)

theorem maxContact_baseChange_isPullbackBlowupSequence
    (hO' : ∀ x : ↥((T.bc f).withBoundary E').scheme,
      orderAt ((T.bc f).withBoundary E').ideal x ≤ (T.mult : ENat)) :
    IsPullbackBlowupSequence (pullback.fst T.structMap $ specMapOfFieldHom T.base K f)
      (maxContactPrincipalization hinv A
        ((T.bc f).withBoundary E')).toSequenceOfBlowups
      (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  let _c0 := (T.bc f).withBoundary E'
  have hstrict := isStrictPullbackBlowupSeq_maxContact_baseChange hinv n A L hdiv T hV hP hO K f
    E' hE hV' hP'
  have hmult : _c0.mult = T.mult := by
    rw [withBoundary_mult, baseChange_mult]
  have hO2 : ∀ x,
      orderAt _c0.ideal x
        ≤ (_c0.mult : ENat) := by
    intro x
    rw [hmult]
    exact hO' x
  by_cases hemp : orderAtLeastLocus _c0.ideal
      _c0.mult = ∅
  have hlen' :=
    length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (· ≤ n) A
      _c0 hV' hP' hO2 hemp
  let _a0 := pullback.fst T.structMap $ specMapOfFieldHom T.base K f
  have hemp2 : orderAtLeastLocus
      (T.ideal.comap _a0) T.mult = ∅ := by
    rwa [withBoundary_ideal, baseChange_ideal, hmult] at hemp
  have :=
    surjective_baseChange_fst T K f
  exact isPullback_of_length_eq_zero_of_length_eq_zero _ _ _ hlen' (length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (· ≤ n) A T hV hP hO $ orderAtLeastLocus_eq_empty_of_comap_eq_empty _a0 T.ideal T.mult hemp2)
  have hhyp' : p26 (· ≤ n)
      _c0 :=
    ⟨hP', hO2, mpr_ nonempty_iff_ne_empty hemp, hV'⟩
  refine (hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups).of_isomorphic
    (withoutIsoBlowups_isomorphic_self _ ?_)
  let hsf := coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv
  let hS := hhyp'
  obtain ⟨d, hpb, heq⟩ :=
    exists_isStrictPullback_cover_dropTrivialBoundary hsf (markingDescends hinv (· ≤ n) A) forall_isAdmissible_dropTrivialBoundary
      forall_isMarked_of_isMarked_dropTrivialBoundary _c0 hS
  rw [heq]
  exact hpb.center_ne_top_of_forall_center_ne_top
    (hsf.center_ne_top _ $ hS.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary)
end

theorem descentProperties_of_isBoundaryDivisorReduction
    (hshift : IsBoundaryPositionInvariant (fun d => d ≤ n) A) :
    DescentHypotheses hinv (fun d => d ≤ n) A L := by
  have hstar := maxContactCoverProperties
  have hCoverSeq :=
    coverSequenceProperties_of_isBoundaryDivisorReduction hinv n A L hdiv
  have hmd :=
    markingDescends hinv (· ≤ n) A
  refine ⟨tunedSheafProperties.isMarked_tuned_iff, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, forall_isAdmissible_dropTrivialBoundary, ?_⟩
  intro k hfk W' W p g hg hsurj N mu_ Mem Z hcert
  exact @orderCertificate_of_comap_of_isLocalIsomorphism (fun K inst => @openImmersionStability K inst)
    orderCertificateLocalToGlobal k hfk W W' p g hg hsurj N mu_ Mem Z hcert
  intro T hV hP hO K hfK hcK f E' hE hV' hP' hO'
  exact @maxContact_baseChange_isPullbackBlowupSequence hinv n A L hdiv T hV hP hO K hfK hcK f E'
    hE hV' hP' hO'
  intro T hV hP hO K hfK hcK f E' hE hV' hP' _hO'
  exact @isStrictPullbackBlowupSeq_maxContact_baseChange hinv n A L hdiv T hV hP hO K hfK hcK f
    E' hE hV' hP'
  intro T h db D i hi
  exact isLocalIsomorphism_map_coverBlowupSequence hinv A T h db D i hi
  intro T h db hd
  exact isLocallyNoetherian_schemeAt_coverBlowupSequence hinv A hstar T h db hd
  intro T h db hd
  have hv := h.valid
  have hcz : CharZero T.base := by
    cases hv
    assumption
  have hsm : Smooth T.structMap := by
    cases hv
    assumption
  have hlft :=
    coverMap_surjective tunedSheafProperties T h
  have hoi :=
    isLocalIsomorphism_coverMap T hv
  have hlev := isLocallyNoetherian_schemeAt_coverBlowupSequence hinv A hstar T h db hd
  exact isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq hinv (· ≤ n) A T h hoi (one_le_tuningExponent T.mult) db hd hlev.1 hlev.2
    (fun D i hi =>
      isLocalIsomorphism_map_coverBlowupSequence hinv A T h db D i hi)
  intro T hV db I m hm
  exact isMarked_of_isMarked_dropTrivialBoundary T hV db I m hm
  intro T hV hO s i hi x
  exact orderAt_sequenceOfBlowups_ideal_le_mult hstar T hV hO s i hi x
  intro T hV hP hO Y q g hsmg hq E' hE hV' hP' hO'
  exact @maxContact_isPullback_of_smooth_of_orderAt_le_mult hinv n A L hdiv hshift T hV hP hO Y q g hsmg
    hq E' hE hV' hP' hO'
  intro T hV hP hO Y q g hsmg hsjg hq E' hE hV' hP' hO'
  have hpb := @maxContact_isPullback_of_smooth_of_orderAt_le_mult hinv n A L hdiv hshift T hV hP hO Y q g
    hsmg hq E' hE hV' hP' hO'
  refine @FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence.isStrictPullback_of_surjective _ _ _ hsjg _ _ hpb ?_
  intro i hi
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  exfalso
  have hlen :=
    length_eq_zero_of_orderAtLeastLocus_eq_empty hinv (· ≤ n) A T hV hP hO
      hemp
  omega
  have hne :=
    nonempty_iff_ne_empty.mpr hemp
  have hyp : p26 (· ≤ n) T := ⟨hP, hO, hne, hV⟩
  obtain ⟨dd, hdd, heq⟩ :=
    exists_isStrictPullback_cover_dropTrivialBoundary hCoverSeq hmd forall_isAdmissible_dropTrivialBoundary
      forall_isMarked_of_isMarked_dropTrivialBoundary T hyp
  rw [heq] at hi ⊢
  refine hdd.center_ne_top_of_forall_center_ne_top ?_ i hi
  intro l hl
  exact hCoverSeq.center_ne_top (dropTrivialBoundary T)
    (hyp.of_dropTrivialBoundaryAdmissible forall_isAdmissible_dropTrivialBoundary) l hl
  intro T h
  exact coverMap_flat T h
  intro T h
  exact coverMap_surjective tunedSheafProperties T h
  intro T hV Y q e hei hq J hJ ep_ hep
  exact @isAdmissible_and_dim_eq_withSchemeIdealBoundary_ker T hV Y q e hei hq J hJ ep_ hep
  intro T hv hm
  exact balancedTunedIdeal_eq_of_mult_eq_one T hv hm
  intro T hV _hbd Y q e hei _hq hD
  exact @isAdmissible_withBoundary_ker_of_isSmoothDivisor T hV Y e hei hD
end

end
end

theorem isOrderReduction_orderFamily_of_strictTransformIsBlowup
    (hres : StrictTransformIsBlowupOfClosedSubscheme) :
    ∀ n A L L',
      IsMaxOrderReduction (fun d => d < n) L L' →
      (∀ j, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L) →
      IsBoundaryPositionInvariant (fun d => d ≤ n) A →
      IsOrderReduction (fun d => d ≤ n) ((canonicalAlgorithmRules hres).orderFamily A) L := by
  intro n A L L' hlow hdiv hshift
  have h :=
    (isOrderReduction_maxContact_dim_le_of_descentHypotheses comapIsoInvariance n A L L' hlow hdiv
    (coverSequenceProperties_of_isBoundaryDivisorReduction comapIsoInvariance n A L hdiv)
    (descentProperties_of_isBoundaryDivisorReduction comapIsoInvariance n A L hdiv hshift))
  have heq : (canonicalAlgorithmRules hres).orderFamily A
      = maxContactPrincipalization comapIsoInvariance A := by
    funext T
    rfl
  rwa [heq]

end FunctorialResolution.EmbeddedResolution.OrderReductionProperties
end
section


namespace FunctorialResolution.EmbeddedResolution

def NilIsStrictNormalCrossingsOfSmooth : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : Sch)
    (q : A ⟶ Sp k), Smooth q → InStrictNormalCrossingPosition q []

theorem nilIsStrictNormalCrossingsOfSmooth : NilIsStrictNormalCrossingsOfSmooth := by
  intro k _ _ A q hq
  exact inStrictNormalCrossingPosition_nil q

section
variable (A) (h : TransitionsAreBlowupsForEmbeddings A)
theorem hasProperCenters_embeddedResolutionRuleOfPrincipalization :
    (embeddedResolutionRuleOfPrincipalization A h).HasProperCenters := by
  intro k _ _ Y p _ _ _ _ D i hi
  exact withoutIsoBlowups_center_ne_top _ hi

theorem toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization
    (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace)
    (hsm : AffineSpaceIsSmooth) (hw : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) :
    (embeddedResolutionRuleOfPrincipalization A h).toAffineResolutionRule (affineSpaceEmbeddingChoice hemb hsnc hsm) =
      affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw := by
  funext k _ _ Y p _ _ _ _
  rw [EmbeddedResolutionRule.toAffineResolutionRule_apply, affineSpaceEmbeddingChoice_eq_affineSpaceEmbeddingDatum]
  let _c0 := ofAffine A hemb hsnc hsm k Y p
  let _c1 := affineSpaceEmbeddingDatum hemb hsnc hsm k Y p
  have key : ∀ (T1_ T2_ : EmbeddedBlowupSequence k Y p), T1_ = T2_ →
      ∀ h1_ (h2_ : T2_.TransitionsAreBlowups),
        T1_.inducedBlowupsWithoutIso h1_ = T2_.inducedBlowupsWithoutIso h2_ := by simp_all
  let _a0 := hw k Y p
  calc embeddedResolutionRuleOfPrincipalization A h k Y p _c1
      = (_c1.toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso
          (h k Y p _c1) :=
        embeddedResolutionRuleOfPrincipalization_apply A h k Y p _c1
    _ = (_c0.toEmbeddedBlowupSequence).inducedBlowupsWithoutIso
          (mpr_ (toEmbeddedBlowupSequence_transitionsAreBlowups_iff
            _c0) _a0) :=
        key _ _ (affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence A hemb hsnc hsm k Y p) _ _
    _ = _c0.blowupSequenceWithoutIsos _a0 :=
        embeddedInducedBlowupsWithoutIso_eq _c0
          _a0
    _ = affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw k Y p := rfl
end





theorem nonzeroOnComponents_of_support_ne_univ {X : Sch} [IrreducibleSpace ↥X]
    (I : ISD X) (h : (↑I.support : Set ↥X) ≠ univ) :
    NonzeroOnComponents I := by
  intro T hT hsub
  exact h $ univ_subset_iff.mp $ (hT.2 (IrreducibleSpace.isIrreducible_univ X) $ subset_univ T).trans hsub

section
variable (k : Type) [Field k] (n m : ℕ)
def affineSpaceInl :
    affineSpaceIndexedBy k (UFin n) ⟶ affineSpaceIndexedBy k (UFS n m) :=
  AffineSpace.homOfVector (affineSpaceIndexedByToSpec k $ UFin n)
    (coordVectorInl n m $ 𝟙 $ affineSpaceIndexedBy k $ UFin n)

def affineSpaceInrEmbedding :
    affineSpaceIndexedBy k (UFin m) ⟶ affineSpaceIndexedBy k (UFS n m) :=
  AffineSpace.homOfVector (affineSpaceIndexedByToSpec k $ UFin m)
    (coordVectorInr n m $ 𝟙 $ affineSpaceIndexedBy k $ UFin m)

@[simp]
theorem affineSpaceInl_comp_affineSpaceIndexedByToSpec :
    affineSpaceInl k n m ≫ affineSpaceIndexedByToSpec k (UFS n m) =
      affineSpaceIndexedByToSpec k (UFin n) := by
  simp [affineSpaceInl]

@[simp]
theorem affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec :
    affineSpaceInrEmbedding k n m ≫ affineSpaceIndexedByToSpec k (UFS n m) =
      affineSpaceIndexedByToSpec k (UFin m) := by
  simp [affineSpaceInrEmbedding]
end

section
variable {X Y} (f : X ⟶ Y) [IsClosedImmersion f]
theorem support_ker_eq_range_of_isClosedImmersion :
    (support (ker f) : Set ↥Y) = range ⇑f.base := by
  simp [support_ker, ((isClosedEmbedding f).isClosed_range).closure_eq]
end

theorem nonzeroOnComponents_ker_comp {Y A A' : Sch} (j : Y ⟶ A) (i : A ⟶ A')
    [IsClosedImmersion j] [IsClosedImmersion i] [IrreducibleSpace ↥A']
    (h : NonzeroOnComponents $ ker j) :
    NonzeroOnComponents $ ker $ j ≫ i := by
  refine nonzeroOnComponents_of_support_ne_univ _ ?_
  rw [support_ker_eq_range_of_isClosedImmersion $ j ≫ i]
  intro hrange
  have hsurj : ∀ z, ∃ y, bsM (j ≫ i) y = z := by
    intro z
    refine mp_ mem_range ?_
    rw [hrange]
    exact mem_univ z
  obtain ⟨a'⟩ : Nonempty A' := inferInstance
  obtain ⟨y, -⟩ := hsurj a'
  have hjsurj : ∀ b, ∃ y', bsM j y' = b := by
    intro b
    obtain ⟨y', hy'⟩ := hsurj $ bsM i b
    refine ⟨y', ((isClosedEmbedding i).injective) ?_⟩
    simpa using hy'
  refine h (irreducibleComponent $ bsM j y)
    (irreducibleComponent_mem_irreducibleComponents _) ?_
  rw [support_ker_eq_range_of_isClosedImmersion j]
  intro b _
  exact mpr_ mem_range $ hjsurj b

theorem appTop_comp_apply_eq {X Y Z : Sch} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : ↑(Z.presheaf.obj $ op ⊤)) :
    (ConcreteCategory.hom $ appTop $ a ≫ b) x
      = (ConcreteCategory.hom $ appTop a)
          ((ConcreteCategory.hom $ appTop b) x) := by
  have h : appTop (a ≫ b) = appTop b ≫ appTop a := by
    simp
  rw [h]
  rfl

theorem isClosedImmersion_of_coord_surjective {R : CRC} {N M : Type}
    (f : AffineSpace N (Spec R) ⟶ AffineSpace M (Spec R))
    (hover : f ≫ (AffineSpace M (Spec R) ↘ Spec R) = (AffineSpace N (Spec R) ↘ Spec R))
    (hcoord : ∀ i : N, ∃ s : ↑((AffineSpace M $ Spec R).presheaf.obj $ op ⊤),
      (ConcreteCategory.hom $ appTop f) s = AffineSpace.coord (Spec R) i) :
    IsClosedImmersion f := by
  let _c0 := AffineSpace M (Spec R) ↘ Spec R
  choose s hs using hcoord
  have hgcoord : ∀ i,
      (m23 $ appTop
        (m52 _c0 s))
        (m9 (Spec R) i) = s i := by
    intro i
    simp
  have key : f ≫ m52 _c0 s
      = 𝟙 (AffineSpace N $ Spec R) := by
    apply m46
    simp [hover]
    intro i
    rw [appTop_comp_apply_eq, hgcoord i, hs i]
    simp
  refine of_surjective_of_isAffine f ?_
  intro x
  refine ⟨(m23 $ appTop
    (m52 _c0 s)) x, ?_⟩
  have h : (m23 $ appTop
        (f ≫ m52 _c0 s)) x
      = (m23 $ appTop $ 𝟙 $ AffineSpace N $ Spec R) x := by
    rw [key]
  rw [appTop_comp_apply_eq] at h
  simpa using h

section
variable (k : Type) [Field k] (n m : ℕ)
section
variable (i : UFS n m)
theorem pullbackCoord_affineSpaceInl :
    pullbackCoord (affineSpaceInl k n m) i =
      elim (fun a : Fin n =>
          AffineSpace.coord (Sp k) $ up a)
        (fun _ : Fin m => 0) i.down := by
  have h : pullbackCoord (affineSpaceInl k n m) i
      = coordVectorInl n m (𝟙 $ affineSpaceIndexedBy k $ UFin n) i := by
    simp [pullbackCoord_def, affineSpaceInl]
  rw [h]
  obtain ⟨j⟩ := i
  cases j with
  | inl a =>
      show pullbackCoord (𝟙 $ affineSpaceIndexedBy k $ UFin n) (up a)
          = m9 (Sp k) (up a)
      simp
  | inr _ => rfl

theorem pullbackCoord_affineSpaceInrEmbedding :
    pullbackCoord (affineSpaceInrEmbedding k n m) i =
      elim (fun _ => 0)
        (fun b =>
          AffineSpace.coord (Sp k) $ up b) i.down := by
  have h : pullbackCoord (affineSpaceInrEmbedding k n m) i
      = coordVectorInr n m (𝟙 $ affineSpaceIndexedBy k $ UFin m) i := by
    simp [pullbackCoord_def, affineSpaceInrEmbedding]
  rw [h]
  obtain ⟨j⟩ := i
  cases j with
  | inl _ => rfl
  | inr b =>
      show pullbackCoord (𝟙 $ affineSpaceIndexedBy k $ UFin m) (up b)
          = m9 (Sp k) (up b)
      simp
end

theorem pullbackCoord_affineSpaceInl_inl (a : Fin n) :
    pullbackCoord (affineSpaceInl k n m) (up $ Sum.inl a) =
      AffineSpace.coord (Sp k) (up a) :=
  pullbackCoord_affineSpaceInl k n m $ up $ m44 a

theorem pullbackCoord_affineSpaceInrEmbedding_inl (a : Fin n) :
    pullbackCoord (affineSpaceInrEmbedding k n m) (up $ Sum.inl a) = 0 :=
  pullbackCoord_affineSpaceInrEmbedding k n m $ up $ m44 a

theorem pullbackCoord_affineSpaceInl_inr (b : Fin m) :
    pullbackCoord (affineSpaceInl k n m) (up $ Sum.inr b) = 0 :=
  pullbackCoord_affineSpaceInl k n m $ up $ m50 b

theorem pullbackCoord_affineSpaceInrEmbedding_inr (b : Fin m) :
    pullbackCoord (affineSpaceInrEmbedding k n m) (up $ Sum.inr b) =
      AffineSpace.coord (Sp k) (up b) :=
  pullbackCoord_affineSpaceInrEmbedding k n m $ up $ m50 b

theorem isClosedImmersion_affineSpaceInl :
    IsClosedImmersion $ affineSpaceInl k n m := by
  refine isClosedImmersion_of_coord_surjective (affineSpaceInl k n m)
    (affineSpaceInl_comp_affineSpaceIndexedByToSpec k n m) ?_
  rintro ⟨a⟩
  exact ⟨m9 (Sp k) $ up $ m44 a, pullbackCoord_affineSpaceInl_inl k n m a⟩

theorem isClosedImmersion_affineSpaceInrEmbedding :
    IsClosedImmersion $ affineSpaceInrEmbedding k n m := by
  refine isClosedImmersion_of_coord_surjective (R := m10 k)
    (N := UFin m) (M := UFS n m)
    (affineSpaceInrEmbedding k n m) (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k n m) ?_
  intro i
  exact ⟨m9 (Sp k) $ up $ m50 i.down, pullbackCoord_affineSpaceInrEmbedding k n m $ up $ m50 i.down⟩
end

instance instIsClosedImmersionLinEmbLeft (k : Type) [Field k] (n m : ℕ) :
    IsClosedImmersion $ affineSpaceInl k n m :=
  isClosedImmersion_affineSpaceInl k n m

instance instIsClosedImmersionLinEmbRight (k : Type) [Field k] (n m : ℕ) :
    IsClosedImmersion $ affineSpaceInrEmbedding k n m :=
  isClosedImmersion_affineSpaceInrEmbedding k n m

section
variable {k : Type} [Field k] {Y} (n m : ℕ) (q : Y ⟶ Sp k)
theorem comp_affineSpaceInl (f : Y ⟶ affineSpaceIndexedBy k (UFin n))
    (hf : f ≫ affineSpaceIndexedByToSpec k (UFin n) = q) :
    f ≫ affineSpaceInl k n m = AffineSpace.homOfVector q (coordVectorInl n m f) := by
  apply m46
  simp [hf]
  intro i
  obtain ⟨j⟩ := i
  rw [appTop_comp_apply_eq, m87, ← pullbackCoord_def,
    pullbackCoord_affineSpaceInl]
  cases j with
  | inl _ => rfl
  | inr _ => exact map_zero _

theorem comp_affineSpaceInrEmbedding (f : Y ⟶ affineSpaceIndexedBy k (UFin m))
    (hf : f ≫ affineSpaceIndexedByToSpec k (UFin m) = q) :
    f ≫ affineSpaceInrEmbedding k n m = AffineSpace.homOfVector q (coordVectorInr n m f) := by
  apply m46
  simp [hf]
  rintro ⟨j⟩
  rw [appTop_comp_apply_eq, m87]
  cases j with
  | inl a =>
      have h := pullbackCoord_affineSpaceInrEmbedding_inl k n m a
      rw [pullbackCoord_def] at h
      rw [h, map_zero, coordVectorInr_inl]
  | inr b =>
      have h := pullbackCoord_affineSpaceInrEmbedding_inr k n m b
      rw [pullbackCoord_def] at h
      rw [h, coordVectorInr_inr, pullbackCoord_def]
end

theorem IsStrictPullbackBlowupSeq.id {X} (s : SequenceOfBlowups X) :
    IsStrictPullbackBlowupSeq (𝟙 X) s s := by
  refine ⟨rfl, fun i _ => 𝟙 $ sbAt s i, by simp, fun i _ => of_id_fst, fun i _ => ?_⟩
  simp

theorem isomorphic_of_isPullbackSequenceOfBlowups_id {X} (s t : SequenceOfBlowups X)
    (h : IsPullbackBlowupSequence (𝟙 X) s t) (hc : ∀ i : ℕ, i < t.length → center t i ≠ ⊤) :
    s.Isomorphic t := by
  have : Surjective $ 𝟙 X := inferInstance
  exact IsStrictPullbackBlowupSeq.isomorphic (h.isStrictPullback_of_surjective hc)
    (IsStrictPullbackBlowupSeq.id t)

section
variable (hsm : AffineSpaceIsSmooth)
include hsm
section
variable {k : Type} [Field k] [CharZero k] {Y : Sch} {p : Y ⟶ Sp k} (n : ℕ) (e : Y ⟶ affineSpaceIndexedBy k (UFin n)) [IsClosedImmersion e] (hker : NonzeroOnComponents (ker e)) (hcomp : e ≫ affineSpaceIndexedByToSpec k (UFin n) = p)
def EmbeddingDatum.ofClosedImmersionAffineSpace :
    EmbeddingDatum k Y p where
  ambient := affineSpaceIndexedBy k $ UFin n
  ambientStruct := affineSpaceIndexedByToSpec k $ UFin n
  emb := e
  isAffine_ambient := by unfold affineSpaceIndexedBy; infer_instance
  smooth_ambientStruct := (hsm k n)
  locallyOfFiniteType_ambientStruct := by unfold affineSpaceIndexedByToSpec; infer_instance
  quasiCompact_ambientStruct := by unfold affineSpaceIndexedByToSpec; infer_instance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := hker
  comp_eq := hcomp
  sncEmpty := by
    let _a0 := affineSpaceIndexedByToSpec k $ UFin n
    have : Smooth _a0 := hsm k n
    exact inStrictNormalCrossingPosition_nil _a0

@[simp]
theorem EmbeddingDatum.ofClosedImmersionAffineSpace_ambient :
    (EmbeddingDatum.ofClosedImmersionAffineSpace hsm n e hker hcomp).ambient =
      affineSpaceIndexedBy k (UFin n) :=
  rfl
end
end





section
variable (k : Type) [Field k] (m : ℕ)
def affineSpaceOrigin :
    Sp k ⟶ affineSpaceIndexedBy k (UFin m) :=
  AffineSpace.homOfVector (𝟙 $ Sp k) fun _ => 0

@[simp]
theorem affineSpaceOrigin_comp_toSpec :
    affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (UFin m) =
      𝟙 (Sp k) := by
  unfold affineSpaceOrigin
  simp


theorem pullbackCoord_affineSpaceOrigin
    (i : UFin m) :
    pullbackCoord (affineSpaceOrigin k m) i = 0 := by
  simp [pullbackCoord_def, affineSpaceOrigin]

@[simp]
theorem affineSpaceOrigin_appTop_coord
    (i : UFin m) :
    (ConcreteCategory.hom $ appTop $ affineSpaceOrigin k m)
        (AffineSpace.coord (Sp k) i) = 0 := by
  simp [affineSpaceOrigin]

theorem eq_affineSpaceOrigin_of_pullbackCoord_eq_zero
    (f : Sp k ⟶ affineSpaceIndexedBy k (UFin m))
    (hf : f ≫ affineSpaceIndexedByToSpec k (UFin m) = 𝟙 (Sp k))
    (hcoord : ∀ i : UFin m, pullbackCoord f i = 0) :
    f = affineSpaceOrigin k m := by
  refine m46 ?_ ?_
  simp_all
  simp_all
end

instance instIsClosedImmersionAffineSpaceOrigin (k : Type) [Field k] (m : ℕ) :
    IsClosedImmersion $ affineSpaceOrigin k m :=
  by
  have hsurj : Function.Surjective
      (ConcreteCategory.hom $ appTop $ affineSpaceOrigin k m) := by
    intro x
    refine ⟨(ConcreteCategory.hom
        (appTop $ affineSpaceIndexedByToSpec k $ UFin m)) x, ?_⟩
    have h1 : appTop (affineSpaceIndexedByToSpec k $ UFin m) ≫
        appTop (affineSpaceOrigin k m) =
        appTop (𝟙 $ Sp k) := by
      rw [← comp_appTop, affineSpaceOrigin_comp_toSpec]
    have h2 : (ConcreteCategory.hom $ appTop $ affineSpaceOrigin k m)
        ((ConcreteCategory.hom
          (appTop $ affineSpaceIndexedByToSpec k $ UFin m)) x) =
        (ConcreteCategory.hom
          (appTop (affineSpaceIndexedByToSpec k $ UFin m) ≫
            appTop (affineSpaceOrigin k m))) x := by
      simp
    rw [h2, h1]
    simp
  apply of_surjective_of_isAffine
  exact hsurj

theorem appTop_id (X : Sch) :
    appTop (𝟙 X) = 𝟙 (X.presheaf.obj $ op ⊤) := by
  simp [appTop]

section
variable (k : Type) [Field k]

def mvPolynomialFinToAffineSpaceGlobalSections (m : ℕ) :
    MvU m k →+*
      ↑((affineSpaceIndexedBy k $ UFin m).presheaf.obj $ op ⊤) :=
  RingHom.comp
    (CommRingCat.Hom.hom $ appTop
      (AffineSpace.SpecIso (UFin m) $ CommRingCat.of k).hom)
    (CommRingCat.Hom.hom (GSpecIso
      (CommRingCat.of (MvU m k))).inv)

theorem mvPolynomialToSections_apply m
    x :
    mvPolynomialFinToAffineSpaceGlobalSections k m x =
      CommRingCat.Hom.hom (appTop
        (AffineSpace.SpecIso (UFin m) $ CommRingCat.of k).hom)
        (CommRingCat.Hom.hom (GSpecIso
          (CommRingCat.of (MvU m k))).inv x) := rfl
end

theorem sub_C_constantCoeff_mem_span_X {σ A : Type} [CommRing A]
    p :
    p - MvPolynomial.C (constantCoeff p) ∈
      span (range (MvPolynomial.X : σ → MvPolynomial σ A)) := by
  induction p using induction_on
  rename_i a
  simp only [constantCoeff_C, sub_self]
  exact m216 _
  rename_i q r hq hr
  have hadd : q + r - m8 (constantCoeff $ q + r) =
      (q - m8 (constantCoeff q)) +
        (r - m8 (constantCoeff r)) := by
    simp only [map_add]
    ring
  rw [hadd]
  exact m128 _ hq hr
  rename_i q i hq
  have hmul : q * m7 i -
      m8 (constantCoeff $ q * m7 i) =
      q * m7 i := by
    simp
  rw [hmul]
  exact mul_mem_left _ _ $ m100 ⟨i, rfl⟩

theorem ker_eq_span_range_X {σ : Type} {K : Type} [Field K] {T : Type}
    [CommRing T] [Nontrivial T] (g : MvPolynomial σ K →+* T)
    (hg : ∀ i, g (MvPolynomial.X i) = 0) :
    RingHom.ker g = span (range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
  have hspan : span (range m7) ≤ m41 g := by
    rw [span_le]
    rintro x ⟨i, rfl⟩
    simpa [m208] using hg i
  refine le_antisymm ?_ hspan
  intro p hp
  have hsub := sub_C_constantCoeff_mem_span_X (σ := σ) (A := K) p
  have h1 :=
    RingHom.mem_ker.mp $ hspan hsub
  have hp0 := RingHom.mem_ker.mp hp
  have h0 : g (m8 $ constantCoeff p) = 0 := by
    rwa [map_sub, hp0, zero_sub, neg_eq_zero] at h1
  have hc : constantCoeff p = 0 := by
    have hinj : m120 $ g.comp m8 :=
      RingHom.injective _
    apply hinj
    simpa using h0
  have hpe : p = p - m8 (constantCoeff p) := by
    rw [hc, map_zero, sub_zero]
  rwa [hpe]

theorem ker_eq_span_image_of_surjective {A B C : Type} [CommRing A] [CommRing B]
    [CommRing C] (ps_ : A →+* B) (hsurj : Function.Surjective ps_) (g : B →+* C) (s : Set A)
    (h : RingHom.ker (g.comp ps_) = span s) :
    RingHom.ker g = span (ps_ '' s) := by
  have h1 : comap ps_ (m41 g) = span s := by
    rw [← h]
    ext x
    simp [mem_comap]
  have h2 : Ideal.map ps_ (comap ps_ $ RingHom.ker g) = RingHom.ker g :=
    map_comap_of_surjective ps_ hsurj _
  rw [← h2, h1, map_span]

private theorem appTop_hom_appTop_inv_apply {X Y : Sch} (e : X ≅ Y)
    x :
    CommRingCat.Hom.hom (appTop e.hom)
        (CommRingCat.Hom.hom (appTop e.inv) x) = x := by
  have h : appTop e.inv ≫ appTop e.hom =
      𝟙 (pObj X $ op ⊤) := by
    rw [← comp_appTop, e.hom_inv_id, appTop_id]
  simpa using (congrArg (m4 · x) h)

section
variable (k : Type) [Field k] (m : ℕ)
theorem mvPolynomialToSections_X
    (i : UFin m) :
    mvPolynomialFinToAffineSpaceGlobalSections k m (MvPolynomial.X i) =
      AffineSpace.coord (Sp k) i := by
  have hX : m4 (appTop
        (m69 (UFin m) $ m10 k).inv)
        (m9 (Sp k) i) =
      m4 (GSpecIso
        (m10 $ MvU m k)).inv (m7 i) := by
    exact AffineSpace.SpecIso_inv_appTop_coord ..
  rw [mvPolynomialToSections_apply, ← hX]
  exact appTop_hom_appTop_inv_apply _ _

theorem mvPolynomialToSections_surjective :
    Function.Surjective $ mvPolynomialFinToAffineSpaceGlobalSections k m := by
  let _c0 := UFin m
  intro x
  let _m0 := GSpecIso $ m10 $ MvPolynomial _c0 k
  let _a0 := m4 (appTop (m69 _c0 $ m10 k).inv) x
  refine ⟨m4 _m0.hom
      _a0, ?_⟩
  have hinv : m4 _m0.inv
      (m4 _m0.hom
        _a0) =
      _a0 := by
    exact CommRingCat.inv_hom_apply ..
  rw [mvPolynomialToSections_apply, hinv, appTop_hom_appTop_inv_apply]

theorem ker_appTop_affineSpaceOrigin :
    RingHom.ker (CommRingCat.Hom.hom $ appTop $ affineSpaceOrigin k m) =
      span (range fun i : Fin m =>
        AffineSpace.coord (Sp k) $ up i) := by
  let _a0 := m4 $ appTop $ affineSpaceOrigin k m
  let _a1 := mvPolynomialFinToAffineSpaceGlobalSections k m
  have hcomp : m41
      (_a0.comp
        _a1) =
      span (range
        m7) := by
    refine ker_eq_span_range_X _ ?_
    intro i
    rw [m82, mvPolynomialToSections_X k m i]
    exact affineSpaceOrigin_appTop_coord k m i
  have main := ker_eq_span_image_of_surjective _a1
    (mvPolynomialToSections_surjective k m)
    _a0 _ hcomp
  rw [main]
  congr 1
  ext y
  constructor
  rintro ⟨p, hp, rfl⟩
  obtain ⟨j, rfl⟩ := hp
  exact ⟨j.down, sy_ $ mvPolynomialToSections_X k m j⟩
  rintro ⟨i, rfl⟩
  exact ⟨m7 $ up i, mem_range_self _,
    mvPolynomialToSections_X k m $ up i⟩

theorem ker_affineSpaceOrigin :
    ker (affineSpaceOrigin k m) = coordSubspaceIdeal k m Finset.univ := by
  let _a0 := affineSpaceOrigin k m
  have : QuasiCompact _a0 := inferInstance
  have hker : m41 (m4 $ app _a0 ⊤) =
      span (range fun i =>
        m9 (Sp k) $ up i) :=
    ker_appTop_affineSpaceOrigin k m
  refine ext_of_isAffine ?_
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  simpa using hker
end

theorem pullbackCoord_comp_eq_hom_appTop_apply {k : Type} [Field k]
    {Y Z : Sch} {n : Type} (f : Y ⟶ Z) (g : Z ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord (f ≫ g) i =
      (ConcreteCategory.hom $ appTop f) (pullbackCoord g i) := by
  rw [pullbackCoord_def, pullbackCoord_def, comp_appTop]
  rfl

section
variable (k : Type) [Field k] (n m : ℕ)
@[simp]
theorem affineSpaceInl_comp_projLeft :
    affineSpaceInl k n m ≫ projLeft k n m = 𝟙 (affineSpaceIndexedBy k $ UFin n) := by
  refine m46 ?_ ?_
  rw [assoc, projLeft_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, id_comp]
  rintro ⟨a⟩
  have h : pullbackCoord (affineSpaceInl k n m ≫ projLeft k n m) (up a) =
      m9 (Sp k) (up a) := by
    rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def $ projLeft k n m,
      projLeft_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInl_inl]
  rw [← pullbackCoord_def, h]
  simp

@[simp]
theorem affineSpaceInl_comp_projLeft_assoc {Z : Sch}
    (g : affineSpaceIndexedBy k (UFin n) ⟶ Z) :
    affineSpaceInl k n m ≫ projLeft k n m ≫ g = g := by
  rw [← assoc, affineSpaceInl_comp_projLeft, id_comp]

@[simp]
theorem affineSpaceInrEmbedding_comp_projRight :
    affineSpaceInrEmbedding k n m ≫ projRight k n m = 𝟙 (affineSpaceIndexedBy k $ UFin m) := by
  refine m46 ?_ ?_
  rw [assoc, projRight_comp_affineSpaceIndexedByToSpec, affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec, id_comp]
  rintro ⟨b⟩
  have h : pullbackCoord (affineSpaceInrEmbedding k n m ≫ projRight k n m) (up b) =
      m9 (Sp k) (up b) := by
    rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def $ projRight k n m,
      projRight_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInrEmbedding_inr]
  rw [← pullbackCoord_def, h]
  simp


theorem affineSpaceInl_comp_projRight :
    affineSpaceInl k n m ≫ projRight k n m =
      affineSpaceIndexedByToSpec k (UFin n) ≫ affineSpaceOrigin k m := by
  refine m46 ?_ ?_
  rw [assoc, projRight_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, assoc,
    affineSpaceOrigin_comp_toSpec, comp_id]
  rintro ⟨b⟩
  have h : pullbackCoord (affineSpaceInl k n m ≫ projRight k n m) (up b) = 0 := by
    rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def $ projRight k n m,
      projRight_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInl_inr]
  rw [← pullbackCoord_def, ← pullbackCoord_def, h, pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_affineSpaceOrigin, map_zero]

theorem affineSpaceInrEmbedding_comp_projLeft :
    affineSpaceInrEmbedding k n m ≫ projLeft k n m =
      affineSpaceIndexedByToSpec k (UFin m) ≫ affineSpaceOrigin k n := by
  refine m46 ?_ ?_
  simp_all
  rintro ⟨a⟩
  have h : pullbackCoord (affineSpaceInrEmbedding k n m ≫ projLeft k n m) (up a) = 0 := by
    rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def $ projLeft k n m,
      projLeft_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInrEmbedding_inl]
  have h2 : pullbackCoord (affineSpaceIndexedByToSpec k (UFin m) ≫
      affineSpaceOrigin k n) (up a) = 0 := by
    rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_affineSpaceOrigin]
    simp
  rw [← pullbackCoord_def, ← pullbackCoord_def, h, h2]

theorem isPullback_affineSpaceInrEmbedding_projLeft :
    IsPullback (affineSpaceIndexedByToSpec k $ UFin m) (affineSpaceInrEmbedding k n m)
      (affineSpaceOrigin k n) $ projLeft k n m := by
  let _c0 := UFin m
  let _a0 := affineSpaceIndexedByToSpec k _c0
  have h0 : IsPullback (𝟙 $ affineSpaceIndexedBy k _c0)
      _a0
      _a0
      (𝟙 $ Sp k) :=
    of_horiz_isIso ⟨by simp⟩
  have s := h0.flip
  rw [← affineSpaceOrigin_comp_toSpec, ← affineSpaceInrEmbedding_comp_projRight] at s
  exact of_bot s (affineSpaceInrEmbedding_comp_projLeft k n m).symm
    (isPullback_projLeft_projRight k n m)
end

section
variable (hsm : AffineSpaceIsSmooth) (k : Type) [Field k] (n m : ℕ)
include hsm
theorem ker_affineSpaceInl_eq_comap :
    ker (affineSpaceInl k n m) =
      comap (ker $ affineSpaceOrigin k m) (projRight k n m) := by
  let _c0 := affineSpaceIndexedByToSpec k $ UFin n
  have hsmooth := smooth_projRight hsm k n m
  have hflat : Flat $ projRight k n m := inferInstance
  have hbig : IsPullback _c0
      ((affineSpaceInl k n m) ≫ projLeft k n m)
      (affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (UFin m))
      _c0 := by
    rw [affineSpaceInl_comp_projLeft, affineSpaceOrigin_comp_toSpec]
    exact id_vert _
  have hsq :=
    of_bot hbig (affineSpaceInl_comp_projRight k n m).symm
      (isPullback_projLeft_projRight k n m).flip
  have : QuasiCompact $ affineSpaceOrigin k m := inferInstance
  exact ker_eq_comap_ker_of_isPullback_of_flat hsq

theorem ker_affineSpaceInrEmbedding_eq_comap :
    ker (affineSpaceInrEmbedding k n m) =
      comap (ker $ affineSpaceOrigin k n) (projLeft k n m) := by
  have hsmooth := smooth_projLeft hsm k n m
  have hflat : Flat $ projLeft k n m := inferInstance
  have hq1 : QuasiCompact $ affineSpaceOrigin k n := inferInstance
  have hq2 : QuasiCompact $ affineSpaceInrEmbedding k n m := inferInstance
  exact ker_eq_comap_ker_of_isPullback_of_flat $ isPullback_affineSpaceInrEmbedding_projLeft k n m

theorem hasSmoothCoordCodim_affineSpaceInl :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFS n m)
      (affineSpaceInl k n m) m := by
  have hsp := smooth_projRight hsm k n m
  intro x
  refine ⟨⊤, ?_, opI (⊤ : (affineSpaceIndexedBy k $ UFS n m).Opens) ≫
      projRight k n m, ?_, ?_, ?_⟩
  trivial
  infer_instance
  rw [assoc, projRight_comp_affineSpaceIndexedByToSpec]
  rw [restrictIdeal_eq_comap_io, ker_affineSpaceInl_eq_comap hsm, ker_affineSpaceOrigin,
    comap_comp]

theorem hasSmoothCoordCodim_affineSpaceInrEmbedding :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFS n m)
      (affineSpaceInrEmbedding k n m) n := by
  have hsmooth := smooth_projLeft hsm k n m
  intro x
  refine ⟨⊤, by simp, opI (⊤ : (affineSpaceIndexedBy k $ UFS n m).Opens) ≫
      projLeft k n m, inferInstance, ?_, ?_⟩
  rw [assoc, projLeft_comp_affineSpaceIndexedByToSpec]
  rw [restrictIdeal_eq_comap_io, ker_affineSpaceInrEmbedding_eq_comap hsm k n m, ker_affineSpaceOrigin k n]
  simp [comap_comp]
end





section
variable {n m : Type} (e : n ≃ m) (S : Sch)
def affineSpaceIsoOfEquiv :
    AffineSpace n S ≅ AffineSpace m S where
  hom := AffineSpace.reindex (e.symm : m → n) S
  inv := AffineSpace.reindex (e : n → m) S
  hom_inv_id := by
    ext1
    · simp
    · rename_i i
      simp
      show (ConcreteCategory.hom $ appTop $ AffineSpace.reindex (e.symm : m → n) S)
          ((ConcreteCategory.hom $ appTop $ AffineSpace.reindex (e : n → m) S)
            (AffineSpace.coord S i)) = AffineSpace.coord S i
      simp
  inv_hom_id := by
    ext1
    · simp
    · rename_i i
      simp
      show (ConcreteCategory.hom $ appTop $ AffineSpace.reindex (e : n → m) S)
          ((ConcreteCategory.hom $ appTop $ AffineSpace.reindex (e.symm : m → n) S)
            (AffineSpace.coord S i)) = AffineSpace.coord S i
      simp
end

theorem affineSpaceIsoOfEquiv_hom_comp_toSpec (k : Type) [Field k] {n m : Type} (e : n ≃ m) :
    (affineSpaceIsoOfEquiv e $ Sp k).hom ≫ affineSpaceIndexedByToSpec k m =
      affineSpaceIndexedByToSpec k n := by
  simp [affineSpaceIsoOfEquiv]

def uliftFinSumOneEquiv (n : ℕ) : UFS n 1 ≃ UFin (n + 1) :=
  ulift.trans (finSumFinEquiv.trans ulift.symm)

section
variable {k : Type} [Field k] [CharZero k] {Y} {p} (G : EmbeddingDatum k Y p) (n) (ph_ : G.ambient ≅ affineSpaceIndexedBy k (UFin n))
def toAffineSpaceOfAmbientIso :
    G.ambient ⟶ affineSpaceIndexedBy k (UFin $ n + 1) :=
  ph_.hom ≫ affineSpaceInl k n 1 ≫
    (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv n) $ Sp k).hom

end

section
variable (hsm : AffineSpaceIsSmooth) {k : Type} [Field k] [CharZero k] {Y} {p} (G : EmbeddingDatum k Y p) (n) (ph_ : G.ambient ≅ affineSpaceIndexedBy k (UFin n))
include hsm
def presentationOfAmbientIso
    (hph : ph_.hom ≫ affineSpaceIndexedByToSpec k (UFin n) = G.ambientStruct) :
    ClosedEmbeddingIntoAffineSpace G where
  codimBound := 1
  dim := n + 1
  toAffine := toAffineSpaceOfAmbientIso G n ph_
  one_le_codimBound := le_rfl
  one_le_dim := succ_le_succ (zero_le n)
  isClosedImmersion_toAffine := by
    have h : IsClosedImmersion
        (ph_.hom ≫ affineSpaceInl k n 1 ≫
          (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv n) (Sp k)).hom) :=
      inferInstance
    exact h
  toAffine_comp := by
    have h : toAffineSpaceOfAmbientIso G n ph_ =
        ph_.hom ≫ affineSpaceInl k n 1 ≫
          (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv n) (Sp k)).hom := rfl
    rw [h]
    simp only [assoc]
    rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, hph]
  locallyConstCodim := by
    have h1 := hasSmoothCoordCodim_affineSpaceInl hsm k n 1
    let _a0 := affineSpaceIsoOfEquiv (uliftFinSumOneEquiv n) (Sp k)
    have h2 :=
      h1.comp_iso_hom _a0
        (affineSpaceIndexedByToSpec k (UFin (n + 1)))
        (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumOneEquiv n))
    have hdef : toAffineSpaceOfAmbientIso G n ph_ =
        ph_.hom ≫ affineSpaceInl k n 1 ≫
          _a0.hom := rfl
    rw [hdef]
    exact h2.iso_hom_comp ph_
end

def affineSpaceChartPresentation (hemb : AffineEmbedsIntoAffineSpace)
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
    (k : Type) [Field k] [CharZero k] (Y : Sch) [IsAffine Y]
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY] :
    ClosedEmbeddingIntoAffineSpace $ affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY :=
  presentationOfAmbientIso hsm (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) ((hemb k Y pY).choose)
    (Iso.refl _) $ by exact id_comp _





section
variable (k K : Type) [Field k] [Field K] [Algebra k K] (n : Type)
theorem exists_baseChangeAffineSpaceIso :
    ∃ e : baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n,
      e.hom ≫ affineSpaceIndexedByToSpec K n = baseChangeToSpec (affineSpaceIndexedByToSpec k n) K := by
  let _a0 := affineSpaceIndexedByToSpec k n
  let _a1 := specMapAlgebraMap k K
  have hA : IsPullback (baseChangeProjection _a0 K)
      (baseChangeToSpec _a0 K) _a0
      _a1 := of_hasPullback _ _
  have hB :=
    AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _a1
  exact ⟨hA.isoIsPullback _ _ hB, hA.isoIsPullback_hom_snd _ _ hB⟩

def baseChangeAffineSpaceIso :
    baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n :=
  (exists_baseChangeAffineSpaceIso k K n).choose

@[simp]
theorem baseChangeAffineSpaceIso_hom_comp_toSpec :
    (baseChangeAffineSpaceIso k K n).hom ≫ affineSpaceIndexedByToSpec K n =
      baseChangeToSpec (affineSpaceIndexedByToSpec k n) K :=
  (exists_baseChangeAffineSpaceIso k K n).choose_spec
end

section
variable (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth) (k K : Type) [Field k] [CharZero k] [Field K] [CharZero K] [Algebra k K] (Y) [IsAffine Y] (pY) [LocallyOfFiniteType pY] (hker : NonzeroOnComponents (ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K))) (hsncK : InStrictNormalCrossingPosition (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) [])
def affineSpaceChartBaseChangeAmbientIso :
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambient ≅
      affineSpaceIndexedBy K (ULift $ Fin (hemb k Y pY).choose) :=
  eqToIso (rfl) ≪≫
    baseChangeAffineSpaceIso k K (ULift $ Fin (hemb k Y pY).choose)

theorem affineSpaceChartBaseChangeAmbientIso_hom_comp :
    (affineSpaceChartBaseChangeAmbientIso hemb hsnc hsm k K Y pY hker hsncK).hom ≫
        affineSpaceIndexedByToSpec K (ULift $ Fin (hemb k Y pY).choose) =
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambientStruct := by
  let _c0 := ULift $ Fin (hemb k Y pY).choose
  let _a0 := ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambientStruct
  let _a1 := isoH $ baseChangeAffineSpaceIso k K _c0
  have hA : _a1 ≫
      affineSpaceIndexedByToSpec K _c0 =
      _a0 :=
    baseChangeAffineSpaceIso_hom_comp_toSpec k K _
  have hB : (𝟙 (baseChange (affineSpaceIndexedByToSpec k _c0) K) ≫
        _a1) ≫
      affineSpaceIndexedByToSpec K _c0 =
      _a0 := by
    rwa [id_comp]
  exact hB

def affineSpaceChartBaseChangePresentation :
    ClosedEmbeddingIntoAffineSpace
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK) :=
  presentationOfAmbientIso hsm
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK)
    (hemb k Y pY).choose
    (affineSpaceChartBaseChangeAmbientIso hemb hsnc hsm k K Y pY hker hsncK)
    (affineSpaceChartBaseChangeAmbientIso_hom_comp hemb hsnc hsm k K Y pY hker hsncK)
end





structure PresentedSelection where
  sel : EmbeddingChoice
  pres : ∀ (k : Type) [Field k] [CharZero k] Y
    p [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y], ClosedEmbeddingIntoAffineSpace $ sel k Y p
  basePres : ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (K : Type) [Field K] [CharZero K] [Algebra k K]
    (hker : NonzeroOnComponents $ ker $ (sel k Y p).baseChangeEmb K)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec (sel k Y p).ambientStruct K) []),
    ClosedEmbeddingIntoAffineSpace $ (sel k Y p).baseChange K hker hsnc

section
variable (hemb : AffineEmbedsIntoAffineSpace) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
def affineSpacePresentedSelection :
    PresentedSelection where
  sel := affineSpaceEmbeddingChoice hemb hsncE hsm
  pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
  basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
    affineSpaceChartBaseChangePresentation hemb hsncE hsm k K Y p hker hsncK

@[simp]
theorem affineSpacePresentedSelection_selection :
    (affineSpacePresentedSelection hemb hsncE hsm).sel = affineSpaceEmbeddingChoice hemb hsncE hsm :=
  rfl
end

end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

theorem mem_support_restrictIdeal_iff {Y : Sch} (K : ISD Y) (V : Opn Y)
    (v : ↥V.toScheme) :
    v ∈ (restrictIdeal K V).support ↔ V.i v ∈ K.support := by
  rw [restrictIdeal_eq_comap_io]
  exact mp_ ext_iff (support_comap_eq V.i K) v

theorem exists_opens_totalTransform_eq_of_notMem_support {X X1 : Sch}
    [IsLocallyNoetherian X1] (pi_ : X1 ⟶ X) (Z D : ISD X) (x1_ : ↥X1)
    (hx1_ : pi_ x1_ ∉ support Z) :
    ∃ V : Opn X1, x1_ ∈ V ∧
      restrictIdeal (comap D pi_) V =
        restrictIdeal (strictTransform pi_ Z D) V * restrictIdeal (exceptionalIdeal pi_ Z) V ^ 1 := by
  refine ⟨pre pi_ $ suppC Z, hx1_, ?_⟩
  rw [restrictIdeal_strictTransform_eq_comap_of_le_compl pi_ Z D _ le_rfl,
    restrictIdeal_exceptionalIdeal_eq_top_of_le_compl pi_ Z _ le_rfl, pow_one,
    mul_top]

section
variable {X : Sch} {k : Type} [Field k]
theorem inter_support_subset_support_of_mem_coordIdeal
    (p : X ⟶ Sp k) {U : Opn X} {m : ℕ} (c : EtaleChart p U m)
    (Z D : ISD X) (S : FinSet m) (j : Fin m) (hj : j ∈ S)
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    (↑Z.support : Set ↥X) ∩ (U : Set ↥X) ⊆ (↑D.support : Set ↥X) := by
  have hle : restrictIdeal D U ≤ restrictIdeal Z U := by
    rw [hD, hZ]
    exact c.coordIdeal_mono $ Finset.singleton_subset_iff.mpr hj
  intro x hx
  obtain ⟨v, hv⟩ : ∃ v, opI U v = x := ⟨⟨x, an2 hx⟩, rfl⟩
  have h1 : v ∈ spI (restrictIdeal Z U) := by
    rw [mem_support_restrictIdeal_iff, hv]
    exact an1 hx
  have h2 := support_antitone hle h1
  rwa [mem_support_restrictIdeal_iff, hv] at h2

theorem not_inter_support_subset_support_of_notMem_coordIdeal [NoetherianSpace ↥X] (p : X ⟶ Sp k) {U : Opn X}
    (hU : IsAffineOpen U) {m : ℕ} (c : EtaleChart p U m) (Z D : ISD X)
    (S : FinSet m) (j : Fin m) (hj : j ∉ S)
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hD : restrictIdeal D U = c.coordIdeal {j})
    (x : ↥X) (hxU : x ∈ U) (hxZ : x ∈ Z.support) :
    ¬ ((↑Z.support : Set ↥X) ∩ (U : Set ↥X) ⊆ (↑D.support : Set ↥X)) := by
  let _c0 := siPre Z U
  intro hsub
  obtain ⟨i, hi⟩ := exists_complOrderEmb_eq m S hj
  have hD' : restrictIdeal D U = c.coordIdeal {complOrderEmb m S i} := by simp_all
  have hG :=
    c.restrictToSubscheme_coordIdeal_singleton hU Z S hZ i D hD'
  have hcart : p17 $ restrictIdeal (cmI D Z.si) _c0 := by
    refine isLocallyGeneratedByNonZeroDivisor_of_locally_coordIdeal
      (p := opI _c0 ≫ (siI Z ≫ p)) _ ?_
    intro y
    refine ⟨⊤, trivial, m - S.card, (c.restrictToSubscheme hU Z S hZ).restrictOpens ⊤,
      m61 ⟨i, ?_⟩⟩
    rw [hG]
    exact (c.restrictToSubscheme hU Z S hZ).restrictIdeal_coordIdeal ⊤ {i}
  have hall : ∀ y : _c0.toScheme,
      y ∈ spI (restrictIdeal (cmI D Z.si) _c0) := by
    intro y
    rw [mem_support_restrictIdeal_iff]
    have hyZ : siI Z (opI _c0 y) ∈ (Z.support : Set X) := by
      rw [← q5 Z]
      exact mem_range_self _
    have hmem :=
      hsub ⟨hyZ, y.2⟩
    have h2 : (opI _c0 y) ∈
        ((cmI D Z.si).support : CSet Z.subscheme) := by
      rwa [support_comap_eq Z.si D]
    exact h2
  obtain ⟨z, hz⟩ : ∃ z, siI Z z = x := by
    have hxr : x ∈ range (Z.si) := by simp_all
    exact hxr
  have hzU : z ∈ siPre Z U := by simp_all
  obtain ⟨y0_, -⟩ : ∃ y0_, opI _c0 y0_ = z :=
    ⟨⟨z, hzU⟩, rfl⟩
  exact hcart.not_irreducibleComponent_subset_support
    (irreducibleComponent_mem_irreducibleComponents y0_) fun w _ => hall w
end

theorem comap_eq_strictTransform_mul_exceptionalIdeal_pow : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ Z : tISD T,
      Smooth (subschemeι Z ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
      ∀ (X' : Sch) (pi_ : X' ⟶ T.scheme), IsBlowupAlongIdealSheaf pi_ Z →
      ∀ D ∈ T.boundary, ∀ x' : ↥X',
        ∃ (U' : X'.Opens) (ep_ : ℕ), x' ∈ U' ∧ (ep_ = 0 ∨ ep_ = 1) ∧
          (ep_ = 1 ↔ ∃ V : T.scheme.Opens, pi_ x' ∈ V ∧
            ((↑Z.support : CSet T.scheme) ∩ (V : CSet T.scheme)) ⊆ (↑D.support : CSet T.scheme)) ∧
          comap (comap D pi_) U'.i =
            comap (strictTransform pi_ Z D) U'.i * (comap (exceptionalIdeal pi_ Z) U'.i) ^ ep_ := by
  intro T hV Z _hZsm hsnc X' pi_ hpi_ D hD x'
  have := hV.isNoetherian
  have : NoetherianSpace T.scheme := inferInstance
  have := isNoetherian_of_isBlowupAlongIdealSheaf hpi_
  have : IsLocallyNoetherian X' := inferInstance
  by_cases hx : pi_ x' ∈ spI Z
  obtain ⟨U, hxU, m, c, a, S, _hinj, hnone, hsome, hZU⟩ := hsnc.exists_etaleChart hx
  obtain ⟨i, hi, hDi⟩ := mp_ mem_iff_getElem hD
  obtain ⟨s, hs, B, hx'B⟩ :
      ∃ (s : Fin m) (_ : s ∈ S) (B : BlowupChart pi_ c S s), x' ∈ B.domain := by
    obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZU x' hxU
    exact ⟨s, hs, _, hmem⟩
  cases hai : a i with
  | none =>
    have hDtop : restrictIdeal D U = ⊤ := by
      have h1 := hnone i hi hai
      rwa [hDi] at h1
    refine ⟨B.domain, 0, hx'B, m51 rfl, ?_, ?_⟩
    refine ⟨fun h0 => absurd h0 $ by omega, fun hV' => ?_⟩
    obtain ⟨V, hxV, hsubV⟩ := hV'
    exact absurd (hsubV ⟨hx, hxV⟩)
      (notMem_support_of_restrictIdeal_eq_top D U _ hxU hDtop)
    show restrictIdeal (cmI D pi_) B.domain =
      restrictIdeal (p6 pi_ Z D) B.domain *
        restrictIdeal (p5 pi_ Z) B.domain ^ 0
    rw [B.restrictIdeal_comap_top D hDtop, B.restrictIdeal_strictTransform_of_eq_top Z D hDtop,
      pow_zero, mul_one]
  | some t =>
    have hDU : restrictIdeal D U = c.coordIdeal {t} := by
      have h1 := hsome i hi t hai
      rwa [hDi] at h1
    by_cases htS : t ∈ S
    have hcrit : ∃ V : T.scheme.Opens, pi_ x' ∈ V ∧
        (suppI Z ∩ (V : CSet T.scheme)) ⊆
          suppI D :=
      ⟨U, hxU,
        inter_support_subset_support_of_mem_coordIdeal T.structMap c Z D S t htS hZU hDU⟩
    refine ⟨B.domain, 1, hx'B, m61 rfl, ⟨fun _ => hcrit, fun _ => rfl⟩, ?_⟩
    show restrictIdeal (cmI D pi_) B.domain =
      restrictIdeal (p6 pi_ Z D) B.domain *
        restrictIdeal (p5 pi_ Z) B.domain ^ 1
    by_cases hts : t = s
    rw [hts] at hDU
    rw [B.restrictIdeal_comap_coordIdeal_self D hDU,
      B.restrictIdeal_strictTransform_coordIdeal_self Z D hs hZU hDU,
      B.restrictIdeal_exceptionalIdeal Z hs hZU, pow_one,
      top_mul]
    rw [B.restrictIdeal_comap_coordIdeal_of_mem D t htS hts hDU,
      B.restrictIdeal_strictTransform_of_mem_of_ne Z D hs hZU t htS hts hDU,
      B.restrictIdeal_exceptionalIdeal Z hs hZU, pow_one]
    refine ⟨B.domain, 0, hx'B, m51 rfl, ?_, ?_⟩
    refine ⟨fun h0 => absurd h0 $ by omega, fun hV' => ?_⟩
    exfalso
    obtain ⟨V, hxV, hsubV⟩ := hV'
    obtain ⟨W, hxW, hWle⟩ :
        ∃ W : T.scheme.affineOpens, pi_ x' ∈ W.1 ∧ W.1 ≤ U ⊓ V := by
      apply exists_affineOpens_mem_le
      exact (⟨hxU, hxV⟩ : pi_ x' ∈ U ⊓ V)
    have hWU := hWle.trans inf_le_left
    refine not_inter_support_subset_support_of_notMem_coordIdeal T.structMap W.2
      (c.restrict hWU) Z D S t htS (restrictIdeal_eq_restrict_coordIdeal_of_le hWU c Z S hZU) (restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D {t} hDU) (pi_ x') hxW hx ?_
    intro w hw
    exact hsubV ⟨hw.1, SetLike.coe_subset_coe.mpr (hWle.trans inf_le_right) hw.2⟩
    show restrictIdeal (cmI D pi_) B.domain =
      restrictIdeal (p6 pi_ Z D) B.domain *
        restrictIdeal (p5 pi_ Z) B.domain ^ 0
    rw [B.restrictIdeal_comap_coordIdeal_of_not_mem D t htS hDU,
      B.restrictIdeal_strictTransform_coordIdeal_of_notMem Z D hs hZU t htS hDU, pow_zero, mul_one]
  obtain ⟨V, hxV, hVeq⟩ := exists_opens_totalTransform_eq_of_notMem_support pi_ Z D x' hx
  refine ⟨V, 1, hxV, m61 rfl, ?_, hVeq⟩
  refine ⟨fun _ => ⟨suppC Z, hx, ?_⟩, fun _ => rfl⟩
  intro y hy
  exact absurd hy.1 hy.2





section
variable {X' X : Sch} (pi_ : X' ⟶ X) (Z : ISD X) (L : Bdy X)
theorem getElem_map_strictTransform_append_of_lt i (hi : i < L.length)
    (hi' : i < (L.map (strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z]).length) :
    (L.map (strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z])[i]'hi'
      = strictTransform pi_ Z (L[i]'hi) :=by simp_all
theorem getElem_length_map_strictTransform_append
    (hi' : L.length < (L.map (strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z]).length) :
    (L.map (strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z])[L.length]'hi'
      = exceptionalIdeal pi_ Z := by
  simp [getElem_append_right]

theorem transformedBoundary_get_strictTransformIndex (j : Fin L.length) :
    (transformedBoundary pi_ Z L).get (strictTransformIndex pi_ Z L j) = strictTransform pi_ Z (L.get j) := by
  simp [get_eq_getElem]
  exact getElem_map_strictTransform_append_of_lt pi_ Z L j j.isLt _
end

theorem mem_support_intersectionIdeal_iff {Y : Sch} (L : Bdy Y)
    J y :
    y ∈ support (intersectionIdeal L J) ↔ ∀ j ∈ J, y ∈ support (L.get j) := by
  have hsup : ∀ A B : ISD Y,
      y ∈ support (A ⊔ B) ↔ y ∈ support A ∧ y ∈ support B := by
    intro A B
    rw [support_sup]
    exact m22
  rw [intersectionIdeal_eq_iSup]
  induction J using m178 with
  | empty =>
      have hbot : (⨆ j ∈ (∅ : FinSet L.length), L.get j) = ⊥ := by simp
      rw [hbot]
      constructor
      intro _ j hj
      exact absurd hj $ notMem_empty j
      intro _
      rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_bot]
      exact bot_le
  | insert a s _ ih =>
      rw [Finset.iSup_insert, hsup, Finset.forall_mem_insert]
      exact and_congr_right fun _ => ih

section
variable {X X' : Sch} [IsLocallyNoetherian X'] (pi_ : X' ⟶ X)
theorem mem_support_strictTransform_iff_of_notMem_support (Z D : ISD X) x'
    (hx' : pi_ x' ∉ support Z) :
    x' ∈ support (strictTransform pi_ Z D) ↔ pi_ x' ∈ support D := by
  let _c0 := suppI D \ suppI Z
  have hsupp :=
    support_strictTransform_eq_closure_preimage pi_ Z D
  constructor
  intro hx
  let _a0 := closure $ preimage pi_.base _c0
  have h1 : x' ∈ _a0 := by
    have h0 : x' ∈ (spI (p6 pi_ Z D) : Set X') := hx
    rwa [hsupp] at h0
  have h2 : _a0
      ⊆ preimage pi_.base D.supp := by
    exact closure_minimal (fun y hy => hy.1) $ (support D).isClosed.preimage pi_.base.hom.continuous
  exact h2 h1
  intro hx
  have h3 : x' ∈ preimage pi_.base _c0 := ⟨hx, hx'⟩
  have h4 := subset_closure h3
  rwa [← hsupp] at h4

theorem mem_support_intersectionIdeal_transformedBoundary_iff_of_notMem (Z : ISD X) (L : Bdy X)
    (J : FinSet L.length) x' (hx' : pi_ x' ∉ support Z) :
    x' ∈ support (intersectionIdeal (transformedBoundary pi_ Z L) $ J.image $ strictTransformIndex pi_ Z L) ↔
      pi_ x' ∈ support (intersectionIdeal L J) := by
  rw [mem_support_intersectionIdeal_iff, mem_support_intersectionIdeal_iff]
  constructor
  intro h j hj
  have h1 := h (strictTransformIndex pi_ Z L j) $ mem_image_of_mem _ hj
  rw [transformedBoundary_get_strictTransformIndex] at h1
  exact mp_ (mem_support_strictTransform_iff_of_notMem_support pi_ Z (L.get j) x' hx') h1
  intro h j' hj'
  obtain ⟨j, hj, rfl⟩ := mp_ mem_image hj'
  rw [transformedBoundary_get_strictTransformIndex]
  exact mpr_ (mem_support_strictTransform_iff_of_notMem_support pi_ Z (L.get j) x' hx') $ h j hj
end

theorem genericPoint_notMem_support_exceptionalIdeal
    (T : MarkedIdealWithBoundary) (Z : tISD T)
    (hsncZ : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    X' pi_ (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
    [IsLocallyNoetherian X'] [NoetherianSpace ↥X']
    (J : FinSet T.boundary.length) C'
    (hC'irr : IsIrreducible C')
    (hC'sub : C' ⊆ (↑(intersectionIdeal (transformedBoundary pi_ Z T.boundary)
        (J.image $ strictTransformIndex pi_ Z T.boundary)).support : Set ↥X'))
    (hC'max : ∀ D : Set ↥X', IsIrreducible D → C' ⊆ D →
        D ⊆ (↑(intersectionIdeal (transformedBoundary pi_ Z T.boundary)
          (J.image $ strictTransformIndex pi_ Z T.boundary)).support : Set ↥X') → D = C')
    xi' (hxi_' : IsGenericPoint xi' C') :
    xi' ∉ (exceptionalIdeal pi_ Z).support := by
  intro hmem
  have hpixi : pi_ xi' ∈ spI Z := by
    have h0 : xi' ∈ ((cmI Z pi_).support : Set X') := hmem
    rwa [support_comap_eq pi_ Z] at h0
  have hxi'A' : xi' ∈ spI (intersectionIdeal (transformedBoundary pi_ Z T.boundary)
      (J.image $ strictTransformIndex pi_ Z T.boundary)) := hC'sub hxi_'.mem
  have hpos := inStrictNormalCrossingPositionAt_strictTransform_of_mem_support
    T.structMap pi_ Z T.boundary hpi_ hsncZ xi' hpixi
  obtain ⟨U, hxiU_, m, c, a, hinj, hnone, hsome⟩ := hpos
  let _m0 := p6 pi_ Z
  have hlen : (T.boundary.map _m0 ++ [p5 pi_ Z]).length
      = bLen T + 1 := by simp
  have hnlt : bLen T
      < (T.boundary.map _m0 ++ [p5 pi_ Z]).length := by
    rw [hlen]
    exact lt_succ_self _
  have hBlast := getElem_length_map_strictTransform_append pi_ Z T.boundary hnlt
  have hexists : ∃ t, a (bLen T) = some t := by
    cases hh : a (bLen T) with
    | none =>
        exfalso
        have h0 := hnone T.boundary.length hnlt hh
        rw [hBlast] at h0
        exact notMem_support_of_restrictIdeal_eq_top (p5 pi_ Z) U xi' hxiU_ h0 hmem
    | some t => exact ⟨t, rfl⟩
  obtain ⟨t0, hat0⟩ := hexists
  have hexcU : restrictIdeal (p5 pi_ Z) U = c.coordIdeal {t0} := by
    have h0 := hsome T.boundary.length hnlt t0 hat0
    rwa [hBlast] at h0
  have hchoice : ∀ j, ∃ t,
      j ∈ J → (a (j : ℕ) = some t ∧
        restrictIdeal (p6 pi_ Z $ T.boundary.get j) U = c.coordIdeal {t}) := by
    intro j
    by_cases hj : j ∈ J
    have hjlt : (j : ℕ)
        < (T.boundary.map _m0 ++ [p5 pi_ Z]).length := by
      rw [hlen]
      exact lt_succ_of_lt j.isLt
    have hBj : (T.boundary.map _m0
          ++ [p5 pi_ Z])[(j : ℕ)]'hjlt
        = p6 pi_ Z (T.boundary.get j) := by
      rw [get_eq_getElem]
      exact getElem_map_strictTransform_append_of_lt pi_ Z T.boundary (j : ℕ) j.isLt hjlt
    have _i11 : xi' ∈ spI (intersectionIdeal (transformedBoundary pi_ Z T.boundary) $ image (strictTransformIndex pi_ Z T.boundary) J) ↔ ∀ j ∈ J, xi' ∈ spI (p6 pi_ Z $ T.boundary.get j) := by
      rw [mem_support_intersectionIdeal_iff]
      constructor
      intro h j hj
      have h1 := h (strictTransformIndex pi_ Z T.boundary j) $ mem_image_of_mem _ hj
      rwa [transformedBoundary_get_strictTransformIndex] at h1
      intro h j' hj'
      obtain ⟨j, hj, rfl⟩ := mp_ mem_image hj'
      rw [transformedBoundary_get_strictTransformIndex]
      exact h j hj
    cases hh : a (j : ℕ) with
    | none =>
        exfalso
        have h0 := hnone (j : ℕ) hjlt hh
        rw [hBj] at h0
        exact notMem_support_of_restrictIdeal_eq_top _ U xi' hxiU_ h0 $ _i11.mp hxi'A' j hj
    | some t =>
        refine ⟨t, fun _ => ⟨rfl, ?_⟩⟩
        have h0 := hsome (j : ℕ) hjlt t hh
        rwa [hBj] at h0
    exact ⟨t0, fun h => absurd h hj⟩
  choose tfun htfun using hchoice
  have ht0notin : t0 ∉ J.image tfun := by
    intro hcon
    obtain ⟨j, hj, hjt⟩ := mp_ mem_image hcon
    have h1 : a (j : ℕ) = some t0 := by rw [(htfun j hj).1, hjt]
    have hjlt : (j : ℕ)
        < (T.boundary.map _m0 ++ [p5 pi_ Z]).length := by
      rw [hlen]
      exact lt_succ_of_lt j.isLt
    exact absurd (hinj (j : ℕ) hjlt T.boundary.length hnlt t0 h1 hat0) $ Nat.ne_of_lt j.isLt
  have hstep1 : restrictIdeal (intersectionIdeal (transformedBoundary pi_ Z T.boundary)
        (J.image $ strictTransformIndex pi_ Z T.boundary)) U
      = ⨆ j' ∈ J.image (strictTransformIndex pi_ Z T.boundary),
          restrictIdeal ((transformedBoundary pi_ Z T.boundary).get j') U := by
    rw [intersectionIdeal_eq_iSup]
    exact MonomialChart.restrictIdeal_biSup_finset U
      (fun j' => (transformedBoundary pi_ Z T.boundary).get j') _
  have hstep3 : (⨆ j ∈ J, restrictIdeal
          ((transformedBoundary pi_ Z T.boundary).get $ strictTransformIndex pi_ Z T.boundary j) U)
      = ⨆ j ∈ J, c.coordIdeal {tfun j} := by
    refine iSup_congr fun j => iSup_congr fun hj => ?_
    rw [transformedBoundary_get_strictTransformIndex]
    exact (htfun j hj).2
  have hstep4 : (⨆ j ∈ J, c.coordIdeal {tfun j}) = c.coordIdeal (J.image tfun) := by
    rw [MonomialChart.coordIdeal_eq_biSup_singleton, iSup_finset_image]
  obtain ⟨O, hOopen, hOne, hOsub⟩ := exists_isOpen_inter_subset_of_maximal
    ((intersectionIdeal (transformedBoundary pi_ Z T.boundary)
        (J.image $ strictTransformIndex pi_ Z T.boundary)).support : Set X')
    (support $ intersectionIdeal (transformedBoundary pi_ Z T.boundary)
      (J.image $ strictTransformIndex pi_ Z T.boundary)).isClosed C' hC'irr hC'sub hC'max
  have hxi'O : xi' ∈ O := by
    obtain ⟨y, hyO, hyA⟩ := hOne
    exact mpr_ (hxi_'.mem_open_set_iff hOopen) ⟨y, hOsub ⟨hyO, hyA⟩, hyO⟩
  obtain ⟨V, hxiV_, hVle⟩ :=
    exists_affineOpens_mem_le (X := X') (x := xi')
      (U := U ⊓ ⟨O, hOopen⟩) ⟨hxiU_, hxi'O⟩
  have hVU := le_trans hVle inf_le_left
  refine not_inter_support_subset_support_of_notMem_coordIdeal (pi_ ≫ tMp T) V.2
    (c.restrict hVU) _ _ (J.image tfun) t0 ht0notin (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ _ $ hstep1.trans $ tr_ iSup_finset_image $ tr_ hstep3 hstep4) (restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ _ hexcU) xi' hxiV_ hxi'A' ?_
  rintro x ⟨hxA, hxV⟩
  exact ((hxi_'.mem_closed_set_iff (support $ p5 pi_ Z).isClosed).mp hmem) $ hOsub ⟨(hVle hxV).2, hxA⟩

theorem intersectionComponents_transformedBoundary_of_isBlowupAlongIdealSheaf :
    ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
      ∀ J0_,
        ∀ Cc_ ⊆ intersectionComponents T.boundary J0_,
          ∀ (hop : IsOpen $ ⇑(intersectionIdeal T.boundary J0_).si ⁻¹' ⋃₀ Cc_) (X' : Sch)
            (pi_ : X' ⟶ T.scheme),
            IsBlowupAlongIdealSheaf pi_ (componentUnionIdeal T.boundary J0_ Cc_ hop) →
              ∀ J,
                ∀ C' ∈ intersectionComponents
                      (transformedBoundary pi_ (componentUnionIdeal T.boundary J0_ Cc_ hop) T.boundary)
                      (image
                        (strictTransformIndex pi_ (componentUnionIdeal T.boundary J0_ Cc_ hop) T.boundary) J),
                  ∀ xi', IsGenericPoint xi' C' →
                    xi' ∉ (exceptionalIdeal pi_ $ componentUnionIdeal T.boundary J0_ Cc_ hop).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ Cc_ ∧
                          C' = closure (⇑pi_ ⁻¹' C \
                              (↑(exceptionalIdeal pi_
                                  (componentUnionIdeal T.boundary J0_ Cc_ hop)).support : Set ↥X')) ∧
                            ∀ xi_, IsGenericPoint xi_ C → pi_ xi' = xi_ := by
  intro T hT J0_ Cc_ hCc_ hop X' pi_ hpi_ J C' hC' xi' hxi_'
  have := hT.isNoetherian
  have := isNoetherian_of_isBlowupAlongIdealSheaf hpi_
  have : IsLocallyNoetherian X' := inferInstance
  have : NoetherianSpace X' := inferInstance
  obtain ⟨hC'irr, hC'sub, hC'max⟩ := hC'
  have hsncZ :=
    MonomialCenterGeometry.hasStrictNormalCrossingsWith_componentUnionIdeal T hT J0_ Cc_ hCc_ hop
  let _s0 := componentUnionIdeal T.boundary J0_ Cc_ hop
  have hxi'E :=
    genericPoint_notMem_support_exceptionalIdeal T _ hsncZ X' pi_ hpi_ J C' hC'irr hC'sub hC'max xi' hxi_'
  have hpixi' : pi_ xi' ∉ spI _s0 := by
    intro hcon
    apply hxi'E
    have h0 : xi' ∈ ((cmI _s0 pi_).support : Set X') := by
      rwa [support_comap_eq]
    exact h0
  let _a0 := intersectionIdeal (transformedBoundary pi_ _s0 T.boundary) $ J.image $ strictTransformIndex pi_ _s0 T.boundary
  have hxi'A' :=
    hC'sub hxi_'.mem
  have hxiA :=
    (mem_support_intersectionIdeal_transformedBoundary_iff_of_notMem pi_ _ T.boundary J xi' hpixi').mp hxi'A'
  let _a2 := intersectionIdeal T.boundary J
  have hAclosed :=
    (support _a2).isClosed
  have hCsubA :=
    closure_minimal (mpr_ singleton_subset_iff hxiA) hAclosed
  let _s1 := ({pi_ xi'} : CSet T.scheme)
  have hmax : ∀ D, IsIrreducible D → closure _s1 ⊆ D →
      D ⊆ spI _a2 →
      D = closure _s1 := by
    intro D hDirr hCsubD hDsubA
    obtain ⟨et_, hetspec⟩ : ∃ et_, IsGenericPoint et_ $ closure D :=
      sober (IsIrreducible.closure hDirr) isClosed_closure
    have hpixi'D :=
      subset_closure $ hCsubD $ subset_closure $ mem_singleton _
    have hetnotZ : et_ ∉ spI _s0 := by
      intro hcon
      apply hpixi'
      have h1 : closure D
          ⊆ (_s0.support) := by
        rw [← hetspec]
        exact closure_minimal (mpr_ singleton_subset_iff hcon)
          (support _s0).isClosed
      exact h1 hpixi'D
    have hs : pi_ xi' ∈ closure ({et_} : CSet T.scheme) := by
      rwa [hetspec]
    obtain ⟨x, hxet, hxi'x⟩ := exists_lift_of_specializes_of_isBlowupAlongIdealSheaf pi_
      _s0 hpi_ et_ hetnotZ xi' hpixi' hs
    have hxnotZ : pi_ x ∉ spI _s0 := by
      rwa [hxet]
    have hxA' : x ∈ spI _a0 := by
      refine mpr_ (mem_support_intersectionIdeal_transformedBoundary_iff_of_notMem pi_ _ T.boundary J x hxnotZ) ?_
      have h1 : pi_ x ∈ closure D := by
        rw [hxet]
        exact hetspec.mem
      exact (closure_minimal hDsubA hAclosed) h1
    have hclxsub :=
      closure_minimal (mpr_ singleton_subset_iff hxA')
        (support _a0).isClosed
    have hC'sub_x :=
      (hxi_'.mem_closed_set_iff isClosed_closure).mp hxi'x
    have hclx :=
      hC'max _ (IsIrreducible.closure isIrreducible_singleton) hC'sub_x hclxsub
    have hxC' : x ∈ C' := by
      rw [← hclx]
      exact subset_closure $ mem_singleton x
    have hxclxi' : x ∈ closure ({xi'} : Set X') := by
      rwa [hxi_'.def]
    have hpixcl : pi_ x ∈ closure _s1 := by
      have hsub : closure ({xi'} : Set X')
          ⊆ pi_.base ⁻¹' closure _s1 := by
        refine closure_minimal (mpr_ singleton_subset_iff ?_) ?_
        exact subset_closure $ mem_singleton _
        exact isClosed_closure.preimage pi_.base.hom.continuous
      exact hsub hxclxi'
    refine m15 ?_ hCsubD
    have h2 : closure D ⊆ closure _s1 := by
      rw [← hetspec]
      refine closure_minimal (mpr_ singleton_subset_iff ?_) isClosed_closure
      rwa [← hxet]
    exact fun z hz => h2 $ subset_closure hz
  have hCnot : closure _s1 ∉ Cc_ := by
    intro hcon
    apply hpixi'
    have h1 : pi_ xi' ∈ ⋃₀ Cc_ := ⟨_, hcon, subset_closure $ mem_singleton _⟩
    rwa [← componentUnionIdeal_support_eq_sUnion T hT J0_ Cc_ hCc_ hop] at h1
  have hCeq : C' = closure ((pi_ ⁻¹' closure _s1) \
      ((p5 pi_ _s0).support : Set X')) := by
    apply m15
    rw [← hxi_'.def]
    exact closure_mono $ mpr_ singleton_subset_iff ⟨subset_closure $ mem_singleton _, hxi'E⟩
    refine closure_minimal ?_ ?_
    rintro x ⟨hx1, hx2⟩
    have hxnotZ : pi_ x ∉ spI _s0 := by
      intro hcon
      apply hx2
      have h0 : x ∈ ((cmI _s0 pi_).support
          : Set X') := by
        rwa [support_comap_eq]
      exact h0
    obtain ⟨x0_, hx0_, hxx0⟩ := exists_lift_of_specializes_of_isBlowupAlongIdealSheaf pi_
      _s0 hpi_ (pi_ xi') hpixi' x hxnotZ hx1
    have hx0eq :=
      eq_of_isBlowupAlongIdealSheaf_of_notMem_support pi_ _s0 hpi_ x0_ xi'
        (by rw [hx0_]; exact hpixi') hpixi' hx0_
    rw [hx0eq] at hxx0
    rwa [← hxi_'.def]
    rw [← hxi_'.def]
    exact isClosed_closure
  refine ⟨hxi'E, closure _s1, ⟨IsIrreducible.closure isIrreducible_singleton, hCsubA, hmax⟩, hCnot, hCeq, ?_⟩
  intro xi_ hgen
  exact IsGenericPoint.eq rfl hgen

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits TopologicalSpace Opposite


namespace FunctorialResolution.EmbeddedResolution

namespace AffineSpacePrincipalizationData

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

section
variable (i : ℕ)
def schemeAtToSpec : S.ambientLevel i ⟶ Sp k :=
  S.ambientBlowups.projectionToBase i ≫ S.ambientToSpec

@[simp] theorem schemeAtToSpec_def :
    S.schemeAtToSpec i = S.ambientBlowups.projectionToBase i ≫ S.ambientToSpec := rfl

def boundary : List (S.ambientLevel i).IdealSheafData := S.principalizationSequence.boundary i

theorem boundary_def : S.boundary i = S.principalizationSequence.boundary i := rfl

def strictTransformToZero : S.strictTransform i ⟶ S.strictTransform 0 :=
  Nat.rec (motive := fun j => S.strictTransform j ⟶ S.strictTransform 0) (𝟙 _)
    (fun j ih => S.strictTransformMap j ≫ ih) i
end

def strictTransformZeroToBase : S.strictTransform 0 ⟶ Y :=
  (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom

@[simp] theorem strictTransformToZero_zero : S.strictTransformToZero 0 = 𝟙 (S.strictTransform 0) := rfl

section
variable (i : ℕ)
@[simp] theorem strictTransformToZero_succ :
    S.strictTransformToZero (i + 1) = S.strictTransformMap i ≫ S.strictTransformToZero i := rfl

def detachedToBase : S.discardedSubscheme i ⟶ Y :=
  S.discardedio i ≫ S.strictTransformToZero i ≫ S.strictTransformZeroToBase

theorem detachedToBase_def :
    S.detachedToBase i = S.discardedio i ≫ S.strictTransformToZero i ≫ S.strictTransformZeroToBase := rfl
end

theorem strictTransformZeroToBase_def :
    S.strictTransformZeroToBase = (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom := rfl

def InducedCentersLieOverSingularLocus (h : S.TransitionsAreBlowups) : Prop :=
  (S.blowupSequence h).CentersLieOver ((smoothLocusComplement pY : Closeds ↥Y) : Set ↥Y)

theorem inl_comp_blowupSequence_projectionToBase (h : S.TransitionsAreBlowups) (j : ℕ) :
    (coprod.inl : S.strictTransform j ⟶ S.totalSpace j) ≫ projectionToBase (S.blowupSequence h) j =
      S.strictTransformToZero j ≫ S.strictTransformZeroToBase := by
  let _a2 := S.blowupSequence h
  induction j with
  | zero =>
    have h0 : projectionToBase _a2 0 = S.totalSpaceZeroIso.hom :=
      projectionToBase_zero $ S.blowupSequence h
    rw [h0, S.strictTransformToZero_zero, id_comp, S.strictTransformZeroToBase_def]
  | succ j ih =>
    have hdown : _a2.transitionMap (le_succ j) = S.transitionMap j := by
      rw [transitionMap_def]
      exact S.tower_map_succ j
    have hd := _a2.transitionMap_comp_projectionToBase $ le_succ j
    rw [hdown] at hd
    let _a1 := projectionToBase (S.blowupSequence h) j
    refine tr_ ((tr_ (assoc (coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) (S.transitionMap j) _a1) $ congrArg (fun f : S.totalSpace (j + 1) ⟶ Y => (coprod.inl : S.strictTransform (j + 1) ⟶ S.totalSpace (j + 1)) ≫ f) hd).symm) $ tr_ (congrArg (fun g : S.strictTransform (j + 1) ⟶ S.totalSpace j => g ≫ _a1) $ S.inl_comp_transitionMap j) $ tr_ (assoc _ _ _) $ tr_ (congrArg (fun g => S.strictTransformMap j ≫ g) ih) ?_
    rw [S.strictTransformToZero_succ j, assoc]

theorem strictTransformZeroToBase_comp : S.strictTransformZeroToBase ≫ pY = strictTransformio S 0 ≫ S.schemeAtToSpec 0 := by
  calc S.strictTransformZeroToBase ≫ pY
      = coprod.inl ≫ S.totalSpaceZeroIso.hom ≫ pY := by
        rw [strictTransformZeroToBase_def, assoc]
    _ = (coprod.inl ≫ S.totalSpaceZeroIso.hom ≫
          (S.emb ≫ S.ambientBlowups.isoZero.inv)) ≫
          (S.ambientBlowups.isoZero.hom ≫ S.ambientToSpec) := by
        simp [assoc, inv_hom_id_assoc, S.emb_comp]
    _ = strictTransformio S 0 ≫ S.schemeAtToSpec 0 := by
        rw [S.totalSpaceZeroIso_spec, schemeAtToSpec_def, projectionToBase_zero S.ambientBlowups]

def StrictTransformEmptyAtLast : Prop := S.strictTransformIdeal S.ambientLength = ⊤

def DetachedSmooth : Prop :=
  ∀ i, i < S.ambientLength →
    Smooth (S.discardedio i ≫ strictTransformio S i ≫ S.schemeAtToSpec i)

def SmoothLocusPreimageDenseInDetached : Prop :=
  ∀ i, i < S.ambientLength →
    Dense ((S.detachedToBase i).base ⁻¹' (pY.smoothLocus : Set ↥Y))

def DetachedClopenInCenter : Prop :=
  ∀ i, i < S.ambientLength →
    ∃ (T : (S.ambientCenter i).subscheme.Opens),
      IsClosed ((T : Set ↥((S.ambientCenter i).subscheme))) ∧
      ∃ e : S.discardedSubscheme i ≅ T.toScheme,
        e.hom ≫ T.i ≫ (S.ambientCenter i).si = S.discardedio i ≫ strictTransformio S i

def DetachedComponentsNotInBoundary : Prop :=
  ∀ i, i < S.ambientLength → ∀ (j : ℕ) (hj : j < (S.boundary i).length),
    ∀ C ∈ irreducibleComponents ↥(S.discardedSubscheme i),
      ¬ ((S.discardedio i ≫ strictTransformio S i).base '' C ⊆
        ((((S.boundary i).get ⟨j, hj⟩).support : Closeds ↥(S.ambientLevel i)) :
          Set ↥(S.ambientLevel i)))

def DetachedSingularPreimageEqBoundary : Prop :=
  ∀ i, i < S.ambientLength →
    (S.detachedToBase i).base ⁻¹' ((smoothLocusComplement pY : Closeds ↥Y) : Set ↥Y) =
      (S.discardedio i ≫ strictTransformio S i).base ⁻¹'
        (⋃ D ∈ S.boundary i,
          ((support D : Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i)))

def CentersHaveStrictNormalCrossingsWithBoundary : Prop :=
  ∀ i, i < S.ambientLength → HasStrictNormalCrossingsWith (S.schemeAtToSpec i) (S.ambientCenter i) (S.boundary i)

def AllLevelsSmooth : Prop :=
  ∀ i, i ≤ S.ambientLength → Smooth (S.schemeAtToSpec i)

def BoundaryInStrictNormalCrossingPosition : Prop :=
  ∀ i, i ≤ S.ambientLength → InStrictNormalCrossingPosition (S.schemeAtToSpec i) (S.boundary i)

end AffineSpacePrincipalizationData

section
variable (A : PrincipalizationAlgorithm) (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
def AffineStrictTransformEmptyAtLast : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).StrictTransformEmptyAtLast

def AffineDetachedSmooth : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).DetachedSmooth

def AffineSmoothLocusPreimageDenseInDetached : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).SmoothLocusPreimageDenseInDetached

def AffineCentersLieOverSingularLocus
    (hPrincipalization : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).InducedCentersLieOverSingularLocus $ hPrincipalization k Y pY

def AffineDetachedClopenInCenter : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).DetachedClopenInCenter

def AffineDetachedComponentsNotInBoundary : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).DetachedComponentsNotInBoundary

def AffineDetachedSingularPreimageEqBoundary : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).DetachedSingularPreimageEqBoundary

def AffineCentersHaveStrictNormalCrossingsWithBoundary : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).CentersHaveStrictNormalCrossingsWithBoundary

def AffineAllLevelsSmooth : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).AllLevelsSmooth

def AffineBoundaryInStrictNormalCrossingPosition : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (ofAffine A hemb hsnc hsm k Y pY).BoundaryInStrictNormalCrossingPosition
end

theorem smooth_from_initial {Z : Sch} (f : (⊥_ Sch) ⟶ Z) :
    Smooth f := by
  have hf : f = initial.to Z := initial.hom_ext _ _
  rw [hf]
  infer_instance

theorem preimage_comp_base_eq_preimage_preimage {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) (W : Set ↥C) :
    (f ≫ g).base ⁻¹' W = f.base ⁻¹' (g.base ⁻¹' W) := by
  ext x
  simp

theorem isStrictNormalCrossingsDivisor_of_isEmpty {X : Sch} (hX : IsEmpty ↥X)
    (D : ISD X) : IsStrictNormalCrossingsDivisor D := fun x => (hX.false x).elim

section
variable {X Z : Sch} {f g : X ⟶ Z} (h : f = g)
include h
private theorem smooth_of_eq
    (hg : Smooth g) : Smooth f := by
  rwa [h]

theorem dense_preimage_of_eq W
    (hg : Dense $ g.base ⁻¹' W) : Dense $ f.base ⁻¹' W := by
  rwa [h]

theorem isStrictNormalCrossingsDivisor_reducedInverseImage_of_eq
    (W : Closeds ↥Z) (hg : IsStrictNormalCrossingsDivisor $ reducedInverseImage g W) :
    IsStrictNormalCrossingsDivisor $ reducedInverseImage f W := by
  rwa [h]
end

theorem dense_of_dense_preimage_inl_inr {A B : Sch} (T : Set ↥(A ⨿ B))
    (hA : Dense $ (coprod.inl : A ⟶ A ⨿ B).base ⁻¹' T)
    (hB : Dense $ (coprod.inr : B ⟶ A ⨿ B).base ⁻¹' T) : Dense T := by
  let _c0 := (coprod.inr : B ⟶ A ⨿ B)
  let _c1 := (coprod.inl : A ⟶ A ⨿ B)
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨z, hz⟩ := hne
  by_cases hzl : z ∈ range _c1.base
  obtain ⟨a, ha⟩ := hzl
  have hopen : IsOpen $ preimage _c1.base U :=
    hU.preimage $ continuous _
  have hne2 : (preimage _c1.base U).Nonempty := by
    refine ⟨a, ?_⟩
    rwa [mem_preimage, ha]
  obtain ⟨x, hxU, hxT⟩ := (mp_ dense_iff_inter_open hA) _ hopen hne2
  exact ⟨bsM _c1 x, hxU, hxT⟩
  have hzr : z ∈ range _c0.base := by
    rwa [range_coprod_inr_eq_compl]
  obtain ⟨b, hb⟩ := hzr
  have hopen : IsOpen $ preimage _c0.base U :=
    hU.preimage $ continuous _
  have hne2 : (preimage _c0.base U).Nonempty := by
    refine ⟨b, ?_⟩
    rwa [mem_preimage, hb]
  obtain ⟨x, hxU, hxT⟩ := (mp_ dense_iff_inter_open hB) _ hopen hne2
  exact ⟨bsM _c0 x, hxU, hxT⟩

theorem dense_preimage_of_dense_preimage_inl_inr_comp {A B Z : Sch} (g : A ⨿ B ⟶ Z) (W : Set ↥Z)
    (hA : Dense $ ((coprod.inl : A ⟶ A ⨿ B) ≫ g).base ⁻¹' W)
    (hB : Dense $ ((coprod.inr : B ⟶ A ⨿ B) ≫ g).base ⁻¹' W) :
    Dense $ g.base ⁻¹' W := by
  refine dense_of_dense_preimage_inl_inr _ ?_ ?_
  rwa [preimage_comp_base_eq_preimage_preimage] at hA
  rwa [preimage_comp_base_eq_preimage_preimage] at hB

section
variable {P Q Z : Sch} (a : P ⟶ Z) (b : Q ⟶ Z)
theorem dense_preimage_coprod_desc
    (W : Set ↥Z) (ha : Dense $ a.base ⁻¹' W) (hb : Dense $ b.base ⁻¹' W) :
    Dense $ (coprod.desc a b).base ⁻¹' W := by
  refine dense_preimage_of_dense_preimage_inl_inr_comp (coprod.desc a b) W ?_ ?_
  simp_all
  simp_all

theorem isStrictNormalCrossingsDivisor_reducedInverseImage_coprod_desc
    (W : Closeds ↥Z)
    (ha : IsStrictNormalCrossingsDivisor $ reducedInverseImage a W) (hb : IsStrictNormalCrossingsDivisor $ reducedInverseImage b W) :
    IsStrictNormalCrossingsDivisor $ reducedInverseImage (coprod.desc a b) W := by
  refine IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod (coprod.desc a b) W ?_ ?_
  simp_all
  simp_all
end

section
variable {A P Z : Sch} (g : A ⨿ P ⟶ Z)
theorem smooth_of_isEmpty_left (hA : IsEmpty ↥A)
    (hP : Smooth $ (coprod.inr : P ⟶ A ⨿ P) ≫ g) :
    Smooth g := by
  have hdesc : coprod.desc (coprod.inl ≫ g)
      (coprod.inr ≫ g) = g :=
    coprod.hom_ext (by rw [coprod.inl_desc]) $ by rw [coprod.inr_desc]
  refine smooth_of_eq hdesc.symm $ smooth_coprod_desc _ _ ?_ hP
  exact smooth_of_isEmpty _

theorem dense_preimage_of_isEmpty_left (W : Set ↥Z)
    (hA : IsEmpty ↥A)
    (hP : Dense $ ((coprod.inr : P ⟶ A ⨿ P) ≫ g).base ⁻¹' W) : Dense $ g.base ⁻¹' W := by
  exact dense_preimage_of_dense_preimage_inl_inr_comp g W (isEmptyElim) hP

theorem isStrictNormalCrossingsDivisor_reducedInverseImage_of_isEmpty_left
    (W : Closeds ↥Z) (hA : IsEmpty ↥A)
    (hP : IsStrictNormalCrossingsDivisor $ reducedInverseImage ((coprod.inr : P ⟶ A ⨿ P) ≫ g) W) :
    IsStrictNormalCrossingsDivisor $ reducedInverseImage g W :=
  IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod g W (isStrictNormalCrossingsDivisor_of_isEmpty hA _) hP
end

theorem smooth_eqToHom_comp_comp {X1 X2 Z W : Sch} (e : X1 = X2) (g : X2 ⟶ Z)
    (p : Z ⟶ W) (hg : Smooth $ g ≫ p) :
    Smooth $ (eqToHom e ≫ g) ≫ p := by
  subst e
  rwa [eqToHom_refl, id_comp]

section
variable {X1 X2 Z : Sch} (e : X1 = X2) (g : X2 ⟶ Z)
theorem isProper_eqToHom_comp
    (hg : IsProper g) : IsProper $ eqToHom e ≫ g := by
  subst e
  rwa [eqToHom_refl, id_comp]

theorem dense_preimage_eqToHom_comp
    (W : Set ↥Z) (hg : Dense $ g.base ⁻¹' W) : Dense $ (eqToHom e ≫ g).base ⁻¹' W := by
  subst e
  rwa [eqToHom_refl, id_comp]

theorem isStrictNormalCrossingsDivisor_reducedInverseImage_eqToHom_comp (W : Closeds ↥Z) (hg : IsStrictNormalCrossingsDivisor (reducedInverseImage g W)) :
    IsStrictNormalCrossingsDivisor $ reducedInverseImage (eqToHom e ≫ g) W := by
  subst e
  rwa [eqToHom_refl, id_comp]
end

theorem image_mem_irreducibleComponents_of_continuous_inverse {al_ be_ : Type} [TopologicalSpace al_]
    [TopologicalSpace be_] (f : al_ → be_) (g : be_ → al_) (hf : Continuous f) (hg : Continuous g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y)
    {C : Set be_} (hC : C ∈ irreducibleComponents be_) :
    g '' C ∈ irreducibleComponents al_ := by
  obtain ⟨hirr, hmax⟩ := hC
  refine ⟨hirr.image g hg.continuousOn, ?_⟩
  intro b hb hsub
  have hCsub : C ⊆ imS f b := by
    intro y hy
    exact ⟨g y, hsub ⟨y, hy, rfl⟩, hfg y⟩
  intro x hx
  exact ⟨f x, (hmax (hb.image f hf.continuousOn) hCsub) ⟨x, hx, rfl⟩, hgf x⟩

theorem support_prod_eq_iUnion {X : Sch} (L : Bdy X) :
    ((L.prod.support : Closeds ↥X) : Set ↥X)
      = ⋃ D ∈ L, ((support D : Closeds ↥X) : Set ↥X) := by
  induction L with
  | nil =>
      rw [idealSheafData_prod_nil]
      simp [support_top]
  | cons D E ih =>
      rw [idealSheafData_prod_cons]
      simp [support_mul, ih]

theorem support_comap_eq_preimage {X Z : Sch} (f : X ⟶ Z) (I : ISD Z) :
    ((support (comap I f) : Closeds ↥X) : Set ↥X)
      = f.base ⁻¹' ((support I : Closeds ↥Z) : Set ↥Z) := by
  simp

section
variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y] {pY} [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY)
private theorem strictTransformToZero_comp_schemeAtToSpec :
    ∀ i, S.strictTransformToZero i ≫ S.strictTransformio 0 ≫ S.schemeAtToSpec 0 = S.strictTransformio i ≫ S.schemeAtToSpec i := by
  intro i
  induction i with
  | zero => rw [S.strictTransformToZero_zero, id_comp]
  | succ j ih =>
      have h2 : S.ambientBlowupMorphism j ≫ S.ambientBlowups.projectionToBase j = S.ambientBlowups.projectionToBase (j + 1) := by
        rw [show S.ambientBlowupMorphism j = S.ambientBlowups.transitionMapSucc j from rfl, blowupMorphism_eq_transitionMap]
        exact S.ambientBlowups.transitionMap_comp_projectionToBase $ le_succ j
      have h1 : S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j = S.schemeAtToSpec (j + 1) := by
        rw [S.schemeAtToSpec_def j, S.schemeAtToSpec_def $ j + 1, ← assoc, h2]
      calc S.strictTransformToZero (j + 1) ≫ S.strictTransformio 0 ≫ S.schemeAtToSpec 0
          = S.strictTransformMap j ≫ (S.strictTransformToZero j ≫ S.strictTransformio 0 ≫ S.schemeAtToSpec 0) := by
            rw [S.strictTransformToZero_succ j, assoc]
        _ = S.strictTransformMap j ≫ S.strictTransformio j ≫ S.schemeAtToSpec j := by rw [ih]
        _ = (S.strictTransformMap j ≫ S.strictTransformio j) ≫ S.schemeAtToSpec j := by rw [assoc]
        _ = (S.strictTransformio (j + 1) ≫ S.ambientBlowupMorphism j) ≫ S.schemeAtToSpec j := by rw [S.strictTransformMap_comp_strictTransformio]
        _ = S.strictTransformio (j + 1) ≫ (S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j) := by rw [assoc]
        _ = S.strictTransformio (j + 1) ≫ S.schemeAtToSpec (j + 1) := by rw [h1]

end

theorem inr_comp_eq_coprod_desc {A1_ A0_ P Q Z : Sch} (ph_ : Q ⟶ A0_)
    (ta_ : (A1_ ⨿ (P ⨿ Q)) ⟶ (A0_ ⨿ P)) (u : (A1_ ⨿ (P ⨿ Q)) ⟶ Z) (v : (A0_ ⨿ P) ⟶ Z)
    (w : Q ⟶ Z)
    (hta : (coprod.inr : (P ⨿ Q) ⟶ (A1_ ⨿ (P ⨿ Q))) ≫ ta_
        = coprod.desc (coprod.inr : P ⟶ (A0_ ⨿ P)) (ph_ ≫ (coprod.inl : A0_ ⟶ (A0_ ⨿ P))))
    (hv : ta_ ≫ v = u)
    (hw : ph_ ≫ ((coprod.inl : A0_ ⟶ (A0_ ⨿ P)) ≫ v) = w) :
    (coprod.inr : (P ⨿ Q) ⟶ (A1_ ⨿ (P ⨿ Q))) ≫ u
      = coprod.desc ((coprod.inr : P ⟶ (A0_ ⨿ P)) ≫ v) w := by
  rw [← hw, ← hv, ← assoc (coprod.inr : (P ⨿ Q) ⟶ (A1_ ⨿ (P ⨿ Q))) ta_ v, hta]
  apply coprod.hom_ext <;> simp

section
variable {k : Type} [Field k] [CharZero k] {Y : Sch} [IsAffine Y] {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY]
section
variable (S : AffineSpacePrincipalizationData k Y pY) (G : ∀ j, S.discardedUnion j ⟶ Y) (hG : ∀ j, G (j + 1) = coprod.desc (G j) (S.detachedToBase j))
include hG
theorem smooth_discardedUnion_comp
    (hSmooth : S.DetachedSmooth) :
    ∀ j, j ≤ S.ambientLength → Smooth (G j ≫ pY) := by
  intro j
  induction j with
  | zero =>
      intro _
      exact smooth_from_initial $ G 0 ≫ pY
  | succ j ih =>
      intro hj
      have hj' := hj
      refine smooth_of_eq ((congrArg (fun t : S.discardedUnion (j + 1) ⟶ Y => t ≫ pY) $ hG j).trans $ coprod.desc_comp pY (G j) $ S.detachedToBase j) ?_
      refine smooth_coprod_desc _ _ (ih $ le_of_lt hj') ?_
      have _i15 : S.detachedToBase j ≫ pY = S.discardedio j ≫ S.strictTransformio j ≫ S.schemeAtToSpec j := by
        rw [S.detachedToBase_def j, assoc, assoc, S.strictTransformZeroToBase_comp,
          strictTransformToZero_comp_schemeAtToSpec S j]
      exact smooth_of_eq _i15 $ hSmooth j hj'

theorem dense_preimage_smoothLocus_of_discardedUnion
    (hDense : S.SmoothLocusPreimageDenseInDetached) :
    ∀ j, j ≤ S.ambientLength → Dense ((G j).base ⁻¹' (pY.smoothLocus : Set ↥Y)) := by
  intro j
  induction j with
  | zero =>
      intro _
      have : IsEmpty $ S.discardedUnion 0 := (inferInstance : IsEmpty $ ⊥_ Sch)
      exact isEmptyElim
  | succ j ih =>
      intro hj
      have hj' := hj
      exact dense_preimage_of_eq (hG j) _ $ dense_preimage_coprod_desc _ _ _ (ih $ le_of_lt hj') $ hDense j hj'
end

section
variable [QuasiCompact pY] (S : AffineSpacePrincipalizationData k Y pY)
theorem isStrictNormalCrossingsDivisor_reducedInverseImage_discardedUnion (G : ∀ j, S.discardedUnion j ⟶ Y)
    (hG : ∀ j, G (j + 1) = coprod.desc (G j) (S.detachedToBase j))
    (hClopen : S.DetachedClopenInCenter) (hNotInBoundary : S.DetachedComponentsNotInBoundary)
    (hSing : S.DetachedSingularPreimageEqBoundary) (hCentersSNC : S.CentersHaveStrictNormalCrossingsWithBoundary) (hBoundarySNC : S.BoundaryInStrictNormalCrossingPosition)
    (hLevels : S.AllLevelsSmooth) (hsncClopen : StrictNormalCrossingsRestrictToClopen) :
    ∀ j, j ≤ S.ambientLength → IsStrictNormalCrossingsDivisor (reducedInverseImage (G j) $ smoothLocusComplement pY) := by
  intro j
  induction j with
  | zero =>
      intro _
      exact isStrictNormalCrossingsDivisor_of_isEmpty (inferInstance : IsEmpty $ ⊥_ Sch)
        (reducedInverseImage (G 0) $ smoothLocusComplement pY)
  | succ j ih =>
      intro hj
      have hj' := hj
      refine isStrictNormalCrossingsDivisor_reducedInverseImage_of_eq (hG j) _ ?_
      refine isStrictNormalCrossingsDivisor_reducedInverseImage_coprod_desc _ _ _ (ih $ le_of_lt hj')
        ?_
      let i := j
      obtain ⟨T, hTclosed, e, he⟩ := hClopen i hj'
      have := hLevels i $ le_of_lt hj'
      have hgf : ∀ x : (S.discardedSubscheme i), ibM e (ihB_ e x) = x := by
        intro x
        simp
      have hfg : ∀ x : (oSch T), ihB_ e (ibM e x) = x := by
        intro x
        simp
      have hmor : isoI e ≫ (S.discardedio i ≫ S.strictTransformio i) = opI T ≫ siI (S.ambientCenter i) := by
        rw [← he, ← assoc, e.inv_hom_id, id_comp]
      have hbase : ∀ x : (oSch T),
          (S.discardedio i ≫ S.strictTransformio i).base (ibM e x)
            = bsM (opI T ≫ siI (S.ambientCenter i)) x := by
        intro x
        simpa using (congrArg (fun f : oSch T ⟶ S.ambientLevel i => bsM f x) hmor)
      have hcond : ∀ D ∈ S.boundary i, ∀ C ∈ irreducibleComponents (oSch T),
          ¬ (bsM (opI T ≫ siI (S.ambientCenter i)) '' C ⊆
            suppI D) := by
        intro D hD C hC hsub
        obtain ⟨j, hj, rfl⟩ := mp_ mem_iff_getElem hD
        have himg : bsM (S.discardedio i ≫ S.strictTransformio i) '' (ibM e '' C)
            = bsM (opI T ≫ siI (S.ambientCenter i)) '' C := by
          rw [image_image]
          exact image_congr fun x _ => hbase x
        have hoff := hNotInBoundary i hj' j hj (ibM e '' C) $ image_mem_irreducibleComponents_of_continuous_inverse e.hom.base (ibM e) (continuous _) (continuous _) hgf hfg hC
        rw [get_eq_getElem] at hoff
        exact hoff (by rw [himg]; exact hsub)
      have hsnc1 := hsncClopen k (S.ambientLevel i) (S.schemeAtToSpec i) (S.boundary i) (S.ambientCenter i)
          (hBoundarySNC i $ le_of_lt hj') (hCentersSNC i hj') T hTclosed hcond
      have hpre : ∀ W,
          (opI T ≫ siI (S.ambientCenter i)).base ⁻¹' W
            = ibM e ⁻¹' (bsM (S.discardedio i ≫ S.strictTransformio i) ⁻¹' W) := by
        intro W
        ext x
        simp only [mem_preimage]
        rw [← hbase x]
      have hrp : reducedInverseImage (isoI e ≫ S.detachedToBase i) (smoothLocusComplement pY)
          = ((S.boundary i).prod.comap $ opI T ≫ siI (S.ambientCenter i)).radical := by
        refine reducedInverseImage_eq_radical _ _ _ ?_
        rw [support_comap_eq_preimage, support_prod_eq_iUnion, hpre, ← hSing i hj', preimage_comp_base_eq_preimage_preimage]
      refine IsStrictNormalCrossingsDivisor.of_isOpenImmersion_jointly_surjective (reducedInverseImage (S.detachedToBase i) $ smoothLocusComplement pY)
          (fun _ : Unit => oSch T) (fun _ => isoI e) (fun _ => inferInstance) ?_ ?_
      intro x
      exact ⟨(), ihB_ e x, hgf x⟩
      intro _
      rwa [comap_reducedInverseImage_of_isOpenImmersion e.inv (S.detachedToBase i) $ smoothLocusComplement pY, hrp]

end
end

theorem isStrongResolution_blowupSequenceWithoutIsos_ofAffine (A : PrincipalizationAlgorithm)
    (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace)
    (hsm : AffineSpaceIsSmooth) (hPrincipalization : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm)
    (hEmpty : AffineStrictTransformEmptyAtLast A hemb hsnc hsm)
    (hSmooth : AffineDetachedSmooth A hemb hsnc hsm)
    (hDense : AffineSmoothLocusPreimageDenseInDetached A hemb hsnc hsm)
    (hCenters : AffineCentersLieOverSingularLocus A hemb hsnc hsm hPrincipalization)
    (hClopen : AffineDetachedClopenInCenter A hemb hsnc hsm)
    (hNotInBoundary : AffineDetachedComponentsNotInBoundary A hemb hsnc hsm)
    (hSing : AffineDetachedSingularPreimageEqBoundary A hemb hsnc hsm)
    (hCentersSNC : AffineCentersHaveStrictNormalCrossingsWithBoundary A hemb hsnc hsm)
    (hLevels : AffineAllLevelsSmooth A hemb hsnc hsm)
    (hBoundarySNC : AffineBoundaryInStrictNormalCrossingPosition A hemb hsnc hsm)
    (hsncClopen : StrictNormalCrossingsRestrictToClopen) (hproper : BlowupIsProper) :
    ∀ (k : Type) [Field k] [CharZero k] Y
      pY [LocallyOfFiniteType pY]
      [QuasiCompact pY] [IsReduced Y]
      [IsAffine Y],
      IsStrongResolution k Y pY
        ((ofAffine A hemb hsnc hsm k Y pY).blowupSequenceWithoutIsos $ hPrincipalization k Y pY) := by
  intro k _ _ Y pY _ _ _ _
  let S := ofAffine A hemb hsnc hsm k Y pY
  let h := hPrincipalization k Y pY
  let hCenters := hCenters k Y pY
  let hSing := hSing k Y pY
  let hCentersSNC := hCentersSNC k Y pY
  let hLevels := hLevels k Y pY
  let hBoundarySNC := hBoundarySNC k Y pY
  let _a0 := S.blowupSequence h
  have : IsNoetherianRing $ m10 k := inferInstanceAs $ IsNoetherianRing k
  have : IsNoetherian $ Sp k := inferInstance
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType pY
  have hFeq : ∀ j, S.transitionMap j ≫ sbPrj _a0 j
      = sbPrj _a0 (j + 1) := by
    intro j
    have hdown : _a0.transitionMap (le_succ j) = S.transitionMap j := by
      rw [transitionMap_def]
      exact S.tower_map_succ j
    have hd := _a0.transitionMap_comp_projectionToBase $ le_succ j
    rwa [hdown] at hd
  have hWeq : ∀ j, S.discardedio j ≫ (coprod.inl ≫
      sbPrj _a0 j) = S.detachedToBase j := by
    intro j
    rw [S.inl_comp_blowupSequence_projectionToBase h j]
    exact sy_ $ S.detachedToBase_def j
  have hGeq : ∀ j,
      ((coprod.inr : S.discardedUnion (j + 1) ⟶ S.totalSpace (j + 1)) ≫
          sbPrj _a0 (j + 1))
        = coprod.desc (coprod.inr ≫
            sbPrj _a0 j) (S.detachedToBase j) := fun j =>
    inr_comp_eq_coprod_desc (S.discardedio j) (S.transitionMap j) (sbPrj _a0 $ j + 1)
      (sbPrj _a0 j) (S.detachedToBase j) (coprod.inr_desc _ _) (hFeq j) $ hWeq j
  have hStrictEmpty : IsEmpty $ S.strictTransform S.ambientLength := by
    have h2 : range (S.strictTransformio S.ambientLength)
        = ((spI (S.strictTransformIdeal S.ambientLength) : Closeds $ S.ambientLevel S.ambientLength) :
          Set $ S.ambientLevel S.ambientLength) :=
      range_subschemeι _
    have h3 : ((spI (S.strictTransformIdeal S.ambientLength) : Closeds $ S.ambientLevel S.ambientLength) :
        Set $ S.ambientLevel S.ambientLength) = ∅ := by
      have h1 : S.strictTransformIdeal S.ambientLength = ⊤ := hEmpty k Y pY
      simp [h1, support_top]
    rw [h3] at h2
    exact mp_ range_eq_empty_iff h2
  have hLastStruct : (S.blowupSequenceWithoutIsos h).lastStructMap
      = eqToHom (withoutIsoBlowups_lastObj $ S.blowupSequence h) ≫ _a0.lastStructMap :=
    withoutIsoBlowups_lastStructMap $ S.blowupSequence h
  have hLastProjection : _a0.lastStructMap = sbPrj _a0 S.ambientLength :=
    lastStructMap_eq_projectionToBase $ S.blowupSequence h
  let _a2 := sbPrj _a0 S.ambientLength ≫ pY
  have hstruct : Smooth _a2 := by
    exact smooth_of_isEmpty_left (A := S.strictTransform S.ambientLength) (P := S.discardedUnion S.ambientLength)
      _a2 hStrictEmpty $ smooth_of_eq (assoc _ _ _).symm $ smooth_discardedUnion_comp S (fun j => coprod.inr ≫ sbPrj _a0 j) hGeq (hSmooth k Y pY) S.ambientLength le_rfl
  refine ⟨?_, ?_, isIso_restrict_lastStructMap_smoothLocus pY _ $ withoutIsoBlowups_centersLieOver _ hCenters, ?_, withoutIsoBlowups_centersLieOver _ hCenters, ?_⟩
  rw [hLastStruct, hLastProjection]
  refine smooth_eqToHom_comp_comp _ _ _ ?_
  exact hstruct
  rw [hLastStruct, hLastProjection]
  have _i14 : ∀ i, i ≤ (S.blowupSequence h).length → IsProper (projectionToBase (S.blowupSequence h) i) := by
    let s := S.blowupSequence h
    intro i
    induction i with
    | zero =>
        intro _
        rw [projectionToBase_zero s]
        infer_instance
    | succ n ih =>
        intro hn
        have hlt := hn
        have : IsNoetherian $ sbAt s n :=
          isNoetherian_schemeAt s n $ le_of_lt hlt
        have : IsProper $ sbPrj s n := ih $ le_of_lt hlt
        have : IsProper $ sbTrS s n :=
          hproper _ _ _ _ $ s.isBlowupAlongIdealSheaf_blowupMorphism n hlt
        have h1 : transitionMapSucc s n ≫ projectionToBase s n = projectionToBase s (n + 1) := by
          rw [blowupMorphism_eq_transitionMap]
          exact s.transitionMap_comp_projectionToBase $ le_succ n
        rw [← h1]
        infer_instance
  exact isProper_eqToHom_comp _ _
    (_i14 S.ambientLength le_rfl)
  rw [hLastStruct, hLastProjection]
  refine dense_preimage_eqToHom_comp _ _ _ ?_
  exact dense_preimage_of_isEmpty_left (A := S.strictTransform S.ambientLength) (P := S.discardedUnion S.ambientLength)
    _ _ hStrictEmpty $ dense_preimage_smoothLocus_of_discardedUnion S (fun j => coprod.inr ≫ sbPrj _a0 j) hGeq (hDense k Y pY) S.ambientLength le_rfl
  rw [hLastStruct, hLastProjection]
  refine isStrictNormalCrossingsDivisor_reducedInverseImage_eqToHom_comp _ _ _ ?_
  exact isStrictNormalCrossingsDivisor_reducedInverseImage_of_isEmpty_left (A := S.strictTransform S.ambientLength)
    (P := S.discardedUnion S.ambientLength) _ _ hStrictEmpty $ isStrictNormalCrossingsDivisor_reducedInverseImage_discardedUnion S (fun j => coprod.inr ≫ sbPrj _a0 j) hGeq (hClopen k Y pY) (hNotInBoundary k Y pY) hSing hCentersSNC hBoundarySNC hLevels hsncClopen S.ambientLength le_rfl





theorem smooth_schemeAtToSpec {k : Type} [Field k] [CharZero k] {Y}
    [IsAffine Y] {pY}
    [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    ∀ i, i ≤ S.ambientLength → Smooth (S.schemeAtToSpec i) := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, projectionToBase_zero]
      infer_instance
  | succ n ih =>
      intro hn
      have hlt := hn
      let _a0 := S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec
      have hsm0 : Smooth _a0 :=
        ih $ m49 hlt
      have hZE : HasStrictNormalCrossingsWith _a0 (S.ambientBlowups.center n)
          (S.principalizationSequence.boundary n) := S.principalizationSequence.center_snc n hlt
      have hb : p15 (S.ambientBlowups.transitionMapSucc n) $ S.ambientBlowups.center n :=
        S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt
      have hres := smooth_comp_of_isBlowupAlongIdealSheaf hZE hb
      rwa [AffineSpacePrincipalizationData.schemeAtToSpec_def, projectionToBase_succ, assoc]

section
variable (A : PrincipalizationAlgorithm) (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
theorem affineCentersHaveStrictNormalCrossingsWithBoundary :
    AffineCentersHaveStrictNormalCrossingsWithBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact fun i hi => (ofAffine A hemb hsnc hsm k Y pY).principalizationSequence.center_snc i hi

theorem affineAllLevelsSmooth :
    AffineAllLevelsSmooth A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact smooth_schemeAtToSpec $ ofAffine A hemb hsnc hsm k Y pY

theorem affineBoundaryInStrictNormalCrossingPosition :
    AffineBoundaryInStrictNormalCrossingPosition A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  let S := ofAffine A hemb hsnc hsm k Y pY
  intro i
  induction i with
  | zero =>
      intro _
      have :=
        smooth_schemeAtToSpec S 0 (zero_le _)
      have h0 : S.boundary 0 = ([] : List (S.ambientLevel 0).IdealSheafData) := by
        rw [AffineSpacePrincipalizationData.boundary_def, IdealBlowupSequence.boundary_zero]
        rfl
      rw [h0]
      exact inStrictNormalCrossingPosition_nil $ S.schemeAtToSpec 0
  | succ n ih =>
      intro hn
      have hlt := hn
      have :=
        isNoetherian_ambientLevel S (n + 1) hn
      have : m86 (S.ambientLevel $ n + 1) := inferInstance
      have hres := inStrictNormalCrossingPosition_strictTransform_append
        (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.transitionMapSucc n)
        (S.ambientBlowups.center n) (S.principalizationSequence.boundary n) (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt) (ih $ m49 hlt) (S.principalizationSequence.center_snc n hlt)
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, projectionToBase_succ, assoc,
        AffineSpacePrincipalizationData.boundary_def, S.principalizationSequence.boundary_succ n hlt]
      exact hres
end





namespace AffineSpacePrincipalizationData

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

def CentersLieOverSingularLocus : Prop :=
  ∀ i, i < S.ambientLength → ∀ p : ↥(S.strictTransform i),
    p ∈ ((support (S.centerOffDetached i) : Closeds ↥(S.strictTransform i)) :
        Set ↥(S.strictTransform i)) →
      (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p ∈
        ((smoothLocusComplement pY : Closeds ↥Y) : Set ↥Y)

section
variable (j : ℕ)
def totalSpaceToBase : S.totalSpace j ⟶ Y :=
  Nat.rec (motive := fun j => S.totalSpace j ⟶ Y) S.totalSpaceZeroIso.hom
    (fun j ih => S.transitionMap j ≫ ih) j


@[simp] theorem totalSpaceToBase_succ :
    S.totalSpaceToBase (j + 1) = S.transitionMap j ≫ S.totalSpaceToBase j := rfl

theorem inl_comp_totalSpaceToBase :
    (coprod.inl : S.strictTransform j ⟶ S.totalSpace j) ≫ S.totalSpaceToBase j =
      S.strictTransformToZero j ≫ S.strictTransformZeroToBase := by
  induction j with
  | zero =>
      show (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom
          = 𝟙 (S.strictTransform 0) ≫ S.strictTransformZeroToBase
      rw [id_comp, strictTransformZeroToBase_def]
  | succ j ih =>
      rw [totalSpaceToBase_succ, ← assoc, S.inl_comp_transitionMap j, assoc, ih,
        strictTransformToZero_succ, assoc]
end

theorem totalSpaceToBase_eq_blowupSequence_projectionToBase (h : S.TransitionsAreBlowups) j :
    S.totalSpaceToBase j = projectionToBase (S.blowupSequence h) j := by
  let _a0 := S.blowupSequence h
  induction j with
  | zero =>
      show S.totalSpaceZeroIso.hom = projectionToBase _a0 0
      rw [_a0.projectionToBase_zero]
      rfl
  | succ j ih =>
      have hb : transitionMapSucc _a0 j = S.transitionMap j := S.tower_map_succ j
      rw [totalSpaceToBase_succ, ih, _a0.projectionToBase_succ, hb]
      rfl

theorem centersLieOverSingularLocus_of_inducedCentersLieOverSingularLocus (h : S.TransitionsAreBlowups)
    (hc : S.InducedCentersLieOverSingularLocus h) : S.CentersLieOverSingularLocus := by
  intro i hi p hp
  have : QuasiCompact (S.centerOffDetached i).si := inferInstance
  let _a0 := (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
  have : QuasiCompact
      (siI (S.centerOffDetached i) ≫ _a0) :=
    inferInstance
  have hcomap : cmI (S.centerOnTotalSpace i) coprod.inl
      = S.centerOffDetached i := by
    have hk := ker_comp_coprod_inl_comap_inl (Y := S.discardedUnion i) (S.centerOffDetached i).si
    rwa [q2] at hk
  have hp2 := hp
  rw [← hcomap] at hp2
  have hmem := hc i hi _ $ mem_support_comap.mp hp2
  have e : _a0 ≫ projectionToBase (S.blowupSequence h) i
      = S.strictTransformToZero i ≫ S.strictTransformZeroToBase := by
    rw [← S.totalSpaceToBase_eq_blowupSequence_projectionToBase h i]
    exact S.inl_comp_totalSpaceToBase i
  rwa [← congrArg (fun g : S.strictTransform i ⟶ Y => bsM g p) e]

end AffineSpacePrincipalizationData





namespace EmbeddedBlowupSequence

variable {k : Type} [Field k] [CharZero k] {Y : Sch} [IsAffine Y]
  {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY]

variable (S : EmbeddedBlowupSequence k Y pY)

theorem isNoetherian_schemeAt (i : ℕ) (hi : i ≤ length S) :
    IsNoetherian $ schemeAt S i := by
  have hring : IsNoetherianRing $ m10 k := by
    show IsNoetherianRing k
    infer_instance
  have hspec :=
    isNoetherian_of_locallyOfFiniteType S.ambientStruct
  have h0 :=
    isNoetherian_of_iso S.ambientSeq.isoZero.symm
  revert hi
  induction i with
  | zero =>
    intro _
    exact h0
  | succ n ih =>
    intro hi
    have hn :=
      ih $ le_of_succ_le hi
    exact isNoetherian_of_isBlowupAlongIdealSheaf $ S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism n hi

theorem strictTransformio_eq_subschemeio j :
    strictTransformio S j = subschemeι (S.strictTransformIdeal j) := rfl

private theorem noetherianSpace_of_isClosedImmersion
    {Z X : Sch} (f : Z ⟶ X) [IsClosedImmersion f]
    (h : NoetherianSpace ↥X) :
    NoetherianSpace ↥Z := by
  exact (isClosedEmbedding f).toIsEmbedding.toIsInducing.noetherianSpace

theorem noetherianSpace_strictTransform_of_noetherianSpace_schemeAt (j : ℕ)
    (h : NoetherianSpace ↥(schemeAt S j)) :
    NoetherianSpace ↥(S.strictTransform j) :=
  noetherianSpace_of_isClosedImmersion (S.strictTransformIdeal j).si h

section
variable (i : ℕ)
theorem quasiCompact_strictTransformio_blowdown
    (h : NoetherianSpace ↥(schemeAt S $ i + 1)) :
    QuasiCompact
      (EmbeddedResolution.strictTransformio (S.blowdown i) (S.ambientCenter i) $ S.strictTransformIdeal i) := by
  exact quasiCompact_strictTransformio_of_noetherianSpace _ _ _

section
variable (h : IsOpen (S.detachedLocus i))
def detachedOpens : (S.strictTransform i).Opens :=
  ⟨S.detachedLocus i, h⟩

theorem coe_detachedOpens :
    ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      S.detachedLocus i := rfl

theorem disjoint_detachedOpens_detachedClosureCompl
    (_hn : NoetherianSpace ↥(S.strictTransform i)) :
    Disjoint ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  rw [disjoint_left]
  intro x hx hx'
  exact hx' $ subset_closure hx

theorem union_detachedOpens_detachedClosureCompl
    (hn : NoetherianSpace ↥(S.strictTransform i)) :
    ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) ∪
        ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) = univ := by
  rw [S.coe_detachedOpens i h, S.detachedClosureCompl_coe i, S.detachedClosure_coe i]
  exact union_compl_self _
end

theorem coe_detachedClosureCompl :
    ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      ((S.detachedClosure i : Closeds ↥(S.strictTransform i)) :
        Set ↥(S.strictTransform i))ᶜ := rfl

theorem isClosed_detachedClosureCompl
    (hn : NoetherianSpace ↥(S.strictTransform i))
    (h : IsOpen $ S.detachedLocus i) :
    IsClosed ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  rw [S.coe_detachedClosureCompl i, S.detachedClosure_coe i]
  exact mpr_ isClosed_compl_iff h

theorem image_detachedLocus_subset_ambientCenter_support :
    ⇑(strictTransformio S i).base '' (S.detachedLocus i) ⊆
      (support (S.ambientCenter i) : CSet $ schemeAt S i) := by
  rintro x ⟨y, hy, rfl⟩
  rw [S.detachedLocus_eq_sUnion i, mem_sUnion] at hy
  obtain ⟨C, hC, hyC⟩ := hy
  exact (mp_ (S.mem_detachedComponents i C) hC).2 ⟨y, hyC, rfl⟩

theorem support_centerOffDetached_subset_detachedClosureCompl
    (hn : NoetherianSpace ↥(S.strictTransform i))
    (h : IsOpen $ S.detachedLocus i) :
    (support (S.centerOffDetached i) : Set ↥(S.strictTransform i)) ⊆
      ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  have hco : ((S.detachedClosureCompl i : Opn $ S.strictTransform i) : Set $ S.strictTransform i) =
      (S.detachedLocus i)ᶜ := by
    rw [S.detachedClosureCompl_coe i, S.detachedClosure_coe i]
  rw [S.centerOffDetached_eq i, support_ker, hco]
  refine closure_minimal ?_ h.isClosed_compl
  rintro y ⟨z, rfl⟩
  rw [← hco, ← (S.detachedClosureCompl i).range_ι]
  exact ⟨_, rfl⟩
end

theorem isReduced_strictTransform_of_isNoetherian [IsReduced Y]
    (hN : ∀ j ≤ length S, IsNoetherian $ schemeAt S j)
    (i : ℕ) (hi : i ≤ length S) :
    IsReduced $ S.strictTransform i := by
  revert hi
  induction i with
  | zero =>
    intro _
    have hq : QuasiCompact S.emb := inferInstance
    let _a0 := S.emb ≫ S.ambientSeq.isoZero.inv
    have hq2 : QuasiCompact _a0 :=
      inferInstance
    exact isReduced_subscheme_ker _a0
  | succ n ih =>
    intro hi
    have hred :=
      ih $ le_of_succ_le hi
    have hno := hN (n + 1) hi
    have hqc :=
      quasiCompact_strictTransformio_of_isLocallyNoetherian
        (S.blowdown n) (S.ambientCenter n) $ S.strictTransformIdeal n
    exact isReduced_subscheme_strictTransform (S.blowdown n) (S.ambientCenter n)
      (S.strictTransformIdeal n) $ S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism n hi

section
variable {A B X : Sch} (a : A ⟶ X) (b : B ⟶ X) (V W : Set ↥X) (hdisj : Disjoint V W) (ha : ∀ x : ↥A, a.base x ∈ V) (hb : ∀ y : ↥B, b.base y ∈ W)
include hdisj ha hb
theorem range_coprod_inl_eq_preimage :
    Set.range ⇑(coprod.inl : A ⟶ A ⨿ B).base = ⇑(coprod.desc a b).base ⁻¹' V := by
  apply m15
  rintro _ ⟨z, rfl⟩
  have h1 : bsM (coprod.desc a b) (bsM (coprod.inl : A ⟶ A ⨿ B) z) = bsM a z := by
    rw [← m135, coprod.inl_desc]
  rw [mem_preimage, h1]
  exact ha z
  intro z hz
  by_contra hzn
  have hz2 : z ∈ range (coprod.inr : B ⟶ A ⨿ B).base := by
    rwa [range_coprod_inr_eq_compl]
  obtain ⟨y, rfl⟩ := hz2
  rw [mem_preimage, ← m135, coprod.inr_desc] at hz
  exact mp_ disjoint_left hdisj hz $ hb y

theorem range_coprod_inr_eq_preimage :
    Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base = ⇑(coprod.desc a b).base ⁻¹' W := by
  apply m15
  rintro _ ⟨y, rfl⟩
  have h1 : bsM (coprod.desc a b) (bsM (coprod.inr : B ⟶ A ⨿ B) y) = bsM b y := by
    rw [← m135, coprod.inr_desc]
  rw [mem_preimage, h1]
  exact hb y
  intro z hz
  rw [range_coprod_inr_eq_compl]
  intro hzl
  obtain ⟨x, rfl⟩ := hzl
  rw [mem_preimage, ← m135, coprod.inl_desc] at hz
  exact mp_ disjoint_left hdisj (ha x) hz
end

theorem exists_iso_subscheme_of_eq_vanishingIdeal {X : Sch}
    [IsReduced X] (C : Opn X)
    (hC : IsClosed $ (C : Set ↥X)) (J : ISD X)
    (hJ : J = vanishingIdeal
      (⟨(C : Set ↥X), hC⟩ : Closeds ↥X)) :
    ∃ e : J.subscheme ≅ C.toScheme, e.hom ≫ C.ι = J.subschemeι := by
  subst hJ
  exact exists_iso_subscheme_vanishingIdeal_of_isClosed C hC

theorem isBlowupAlongIdealSheaf_lift_of_comp_eq {X X1 S0 : Sch} (j : S0 ⟶ X)
    [IsClosedImmersion j] [Mono j]
    [IsLocallyNoetherian X1] (pi_ : X1 ⟶ X) (Z : ISD X)
    (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (D : ISD X) (hD : ker j = D)
    (q : subscheme (Blowup.strictTransform pi_ Z D) ⟶ S0)
    (hq : q ≫ j = subschemeι (Blowup.strictTransform pi_ Z D) ≫ pi_) :
    IsBlowupAlongIdealSheaf q $ comap Z j := by
  subst hD
  have h3 : q = strictTransformLiftOfClosedImmersion j pi_ Z := by
    rw [← cancel_mono j, hq, strictTransformLiftOfClosedImmersion_comp j pi_ Z]
  rw [h3]
  exact isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion j pi_ Z hpi_

theorem isBlowupAlongIdealSheaf_coprod_desc_of_disjoint_cover {A A' F : Sch} (g : A' ⟶ A) (j : F ⟶ A)
    (I : ISD A) (V W : Opn A)
    (hdisj : Disjoint ((V : Set ↥A)) $ (W : Set ↥A))
    (hcov : (V : Set ↥A) ∪ (W : Set ↥A) = univ)
    (hgV : ∀ x : ↥A', g.base x ∈ (V : Set ↥A))
    (hjW : ∀ y : ↥F, j.base y ∈ (W : Set ↥A))
    (e : F ≅ W.toScheme) (he : e.hom ≫ W.ι = j)
    (hIW : I.comap W.ι = ⊤)
    (gV : A' ⟶ V.toScheme) (hgv : gV ≫ V.ι = g)
    (hblow : IsBlowupAlongIdealSheaf gV $ I.comap V.ι) :
    IsBlowupAlongIdealSheaf (coprod.desc g j) I := by
  let _a0 := coprod.desc g j
  have hrl : range (coprod.inl : A' ⟶ A' ⨿ F).base
      = range (coprod.desc g j ⁻¹ᵁ V).ib := by
    rw [q1]
    exact range_coprod_inl_eq_preimage g j _ _ hdisj hgV hjW
  have hrr : range (coprod.inr : F ⟶ A' ⨿ F).base
      = range (coprod.desc g j ⁻¹ᵁ W).ib := by
    rw [q1]
    exact range_coprod_inr_eq_preimage g j _ _ hdisj hgV hjW
  obtain ⟨δ, hde_⟩ : ∃ δ : A' ≅ oSch (coprod.desc g j ⁻¹ᵁ V),
      δ.hom ≫ opI (coprod.desc g j ⁻¹ᵁ V) = coprod.inl :=
    ⟨isoOfRangeEq _ _ hrl, isoOfRangeEq_hom_fac _ _ hrl⟩
  obtain ⟨ep_, hep⟩ : ∃ ep_ : F ≅ oSch (coprod.desc g j ⁻¹ᵁ W),
      ep_.hom ≫ opI (coprod.desc g j ⁻¹ᵁ W) = coprod.inr :=
    ⟨isoOfRangeEq _ _ hrr, isoOfRangeEq_hom_fac _ _ hrr⟩
  have key1 : isoH δ ≫ (coprod.desc g j ∣_ V) = gV := by
    rw [← cancel_mono V.i, assoc, morphismRestrict_ι, ← assoc, hde_,
      coprod.inl_desc, hgv]
  have key2 : isoH ep_ ≫ (coprod.desc g j ∣_ W) = isoH e := by
    rw [← cancel_mono W.i, assoc, morphismRestrict_ι, ← assoc, hep,
      coprod.inr_desc, he]
  have hV : p15 (coprod.desc g j ∣_ V) $ cmI I V.i := by
    have hb := hblow.iso_hom_comp δ.symm
    rwa [← key1, symm_hom, inv_hom_id_assoc] at hb
  have hisoW : IsIso $ coprod.desc g j ∣_ W := by
    have hw : (coprod.desc g j ∣_ W) = isoI ep_ ≫ isoH e := by
      rw [← key2, inv_hom_id_assoc]
    rw [hw]
    infer_instance
  have hW : p15 (coprod.desc g j ∣_ W) $ I.comap W.i := by
    rw [hIW]
    exact Blowup.IsBlowupAlongIdealSheaf.of_isIso _
  have hoi : ∀ b,
      IsOpenImmersion $ m190 (motive := fun b =>
        (m190 (motive := fun _ => Sch) V.toScheme W.toScheme b) ⟶ A) V.i W.i b := by
    intro b
    cases b
    exact inferInstance
    exact inferInstance
  refine Blowup.IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover _a0 I
      (fun b => m190 (motive := fun _ => Sch) V.toScheme W.toScheme b)
      (fun b => m190 (motive := fun b =>
        (m190 (motive := fun _ => Sch) V.toScheme W.toScheme b) ⟶ A) V.i W.i b) ?_ ?_
  intro x
  by_cases hx : x ∈ V
  refine ⟨false, ?_⟩
  show x ∈ range V.ib
  rwa [q1]
  refine ⟨true, ?_⟩
  show x ∈ range W.ib
  rw [q1]
  have hxu : x ∈ (V : Set A) ∪ (W : Set A) := by rw [hcov]
                                                 trivial
  exact hxu.resolve_left hx
  intro b
  cases b
  show p15 (pullback.snd _a0 V.i) $ cmI I V.i
  have hb := hV.iso_hom_comp $ pullbackRestrictIsoRestrict _a0 V
  rwa [pullbackRestrictIsoRestrict_hom_morphismRestrict] at hb
  show p15 (pullback.snd _a0 W.i) $ cmI I W.i
  have hb := hW.iso_hom_comp $ pullbackRestrictIsoRestrict _a0 W
  rwa [pullbackRestrictIsoRestrict_hom_morphismRestrict] at hb

theorem isBlowupAlongIdealSheaf_coprod_desc_centerOffDetached [IsReduced Y]
    [QuasiCompact pY] (i : ℕ) (hi : i < S.length)
    (h : IsOpen (S.detachedLocus i))
    (hN : ∀ j ≤ S.length, IsNoetherian (schemeAt S j)) :
    IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.detachedio i)) (S.centerOffDetached i) := by
  have hn0 := hN i hi.le
  let _m2 := schemeAt S $ i + 1
  have hn1 := hN (i + 1) hi
  have hns0 : m86 (schemeAt S i) := inferInstance
  have hns1 : m86 _m2 := inferInstance
  have hnsA :=
    S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i hns0
  have hnsA1 :=
    S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt (i + 1) hns1
  have hred :=
    S.isReduced_strictTransform_of_isNoetherian hN i hi.le
  have hqcst :=
    S.quasiCompact_strictTransformio_blowdown i hns1
  let _a0 := S.strictTransform i
  have hUc : IsClosed ((S.detachedOpens i h) : Set _a0) := by
    rw [S.coe_detachedOpens i h]
    exact S.isClosed_detachedLocus i
  have hdetached : S.detachedIdeal i
      = vanishingIdeal
          (⟨((S.detachedOpens i h) : Set _a0), hUc⟩ :
            Closeds _a0) := by
    rw [S.detachedIdeal_eq i]
    congr 1
    refine m134 ?_
    show ((S.detachedClosure i) :
        Set _a0) =
      ((S.detachedOpens i h) : Set _a0)
    rw [S.detachedClosure_coe i, S.coe_detachedOpens i h]
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_eq_vanishingIdeal (S.detachedOpens i h) hUc
    (S.detachedIdeal i) hdetached
  have hblowA : p15 (S.strictTransformMap i) (S.comapAmbientCenter i) := by
    exact isBlowupAlongIdealSheaf_lift_of_comp_eq (strictTransformio S i) (S.blowdown i) (S.ambientCenter i)
      (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism i hi) (S.strictTransformIdeal i) (by simp) (S.strictTransformMap i)
      (S.strictTransformMap_comp_strictTransformio i)
  let _a11 := S.detachedClosureCompl i
  have hstrict : ∀ x : (S.strictTransform (i + 1)),
      (S.strictTransformMap i).base x ∈
        (_a11 : Set _a0) := by
    have hVcl :=
      S.isClosed_detachedClosureCompl i hnsA h
    let _a7 := isClosedEmbedding $ strictTransformio S i
    have himV :=
      _a7.isClosedMap _ hVcl
    have hsub : (spI (S.strictTransformIdeal i) : CSet (schemeAt S i)) \ (spI (S.ambientCenter i) : CSet (schemeAt S i))
        ⊆ (strictTransformio S i).base ''
            (_a11 : Set _a0) := by
      rintro y ⟨hy, hy2⟩
      rw [← q5] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨z, ?_, rfl⟩
      by_contra hz
      refine absurd (S.image_detachedLocus_subset_ambientCenter_support i ⟨z, ?_, rfl⟩) hy2
      have hz' : z ∈ ((S.detachedClosure i) :
          Set _a0) := by
        by_contra hz2
        exact hz (by rw [S.detachedClosureCompl_coe i]; exact hz2)
      rwa [S.detachedClosure_coe i] at hz'
    intro x
    let _a6 := bsM (strictTransformio S (i + 1)) x
    have h1 : _a6 ∈
        (spI (S.strictTransformIdeal (i + 1)) : Set _m2) := by
      rw [← q5]
      exact ⟨x, rfl⟩
    rw [S.strictTransformIdeal_succ i,
      support_strictTransform_eq_closure_preimage (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)] at h1
    have h2 :=
      closure_minimal (preimage_mono hsub)
        (himV.preimage (S.blowdown i).base.hom.continuous)
    obtain ⟨v, hv, hveq⟩ := h2 h1
    let _a4 := bsM (strictTransformio S i) (bsM (S.strictTransformMap i) x)
    have h3 : _a4
        = bsM (S.blowdown i) _a6 := by
      have hc := congrArg (fun f : S.strictTransform (i + 1) ⟶ schemeAt S i => bsM f x)
        (S.strictTransformMap_comp_strictTransformio i)
      simpa using hc
    have h4 : bsM (strictTransformio S i) v = _a4 := by simp_all
    rwa [← _a7.injective h4]
  have hzer : range (𝟙 (S.strictTransform (i + 1))).base
      = range (opIb (S.strictTransformMap i ⁻¹ᵁ (S.detachedClosureCompl i))) := by
    rw [q1]
    have hA : range (𝟙 (S.strictTransform (i + 1))).base = univ := by simp
    rw [hA]
    symm
    rw [eq_univ_iff_forall]
    intro z
    exact hstrict z
  obtain ⟨ζ, hze⟩ : ∃ ζ : S.strictTransform (i + 1) ≅ oSch (S.strictTransformMap i ⁻¹ᵁ (S.detachedClosureCompl i)),
      ζ.hom ≫ opI (S.strictTransformMap i ⁻¹ᵁ (S.detachedClosureCompl i)) = 𝟙 (S.strictTransform (i + 1)) :=
    ⟨isoOfRangeEq _ _ hzer, isoOfRangeEq_hom_fac _ _ hzer⟩
  have hgv : (isoH ζ ≫ S.strictTransformMap i ∣_ (S.detachedClosureCompl i)) ≫ opI _a11
      = S.strictTransformMap i := by
    rw [assoc, morphismRestrict_ι, ← assoc, hze, id_comp]
  have hWeq : cmI (S.centerOffDetached i) (S.detachedClosureCompl i).i
      = cmI (S.comapAmbientCenter i) (S.detachedClosureCompl i).i := by
    rw [S.centerOffDetached_eq i]
    exact comap_ker_subschemeio_comp _ _
  have hblowV : p15 (isoH ζ ≫ S.strictTransformMap i ∣_ (S.detachedClosureCompl i))
      (cmI (S.centerOffDetached i) (S.detachedClosureCompl i).i) := by
    rw [hWeq]
    exact (hblowA.restrict (S.detachedClosureCompl i)).iso_hom_comp ζ
  have hIW : cmI (S.centerOffDetached i) (S.detachedOpens i h).i = ⊤ := by
    refine p39 _ _ ?_
    intro x hx
    have h1 :=
      S.support_centerOffDetached_subset_detachedClosureCompl i hnsA h hx
    refine mp_ disjoint_left (S.disjoint_detachedOpens_detachedClosureCompl i h hnsA) ?_ h1
    rw [← q1]
    exact ⟨x, rfl⟩
  refine isBlowupAlongIdealSheaf_coprod_desc_of_disjoint_cover (S.strictTransformMap i) (S.detachedio i) (S.centerOffDetached i)
      (S.detachedClosureCompl i) (S.detachedOpens i h) ((S.disjoint_detachedOpens_detachedClosureCompl i h hnsA).symm)
      ?_ hstrict ?_ e he hIW (isoH ζ ≫ S.strictTransformMap i ∣_ (S.detachedClosureCompl i)) hgv hblowV
  rw [union_comm]
  exact S.union_detachedOpens_detachedClosureCompl i h hnsA
  intro y
  have hy : bsM (S.detachedio i) y ∈ range (S.detachedOpens i h).ib := by
    refine ⟨ihB_ e y, ?_⟩
    simpa using (congrArg (fun f : subS (S.detachedIdeal i) ⟶ S.strictTransform i => bsM f y) he)
  rwa [q1] at hy

section
variable (A F T : Sch)
private def coprodSwapAssocHom : A ⨿ (T ⨿ F) ⟶ (A ⨿ F) ⨿ T :=
  coprod.desc ((coprod.inl : A ⟶ A ⨿ F) ≫ (coprod.inl : A ⨿ F ⟶ (A ⨿ F) ⨿ T))
    (coprod.desc (coprod.inr : T ⟶ (A ⨿ F) ⨿ T)
      ((coprod.inr : F ⟶ A ⨿ F) ≫ (coprod.inl : A ⨿ F ⟶ (A ⨿ F) ⨿ T)))

private def coprodSwapAssocInv : (A ⨿ F) ⨿ T ⟶ A ⨿ (T ⨿ F) :=
  coprod.desc
    (coprod.desc (coprod.inl : A ⟶ A ⨿ (T ⨿ F))
      ((coprod.inr : F ⟶ T ⨿ F) ≫ (coprod.inr : T ⨿ F ⟶ A ⨿ (T ⨿ F))))
    ((coprod.inl : T ⟶ T ⨿ F) ≫ (coprod.inr : T ⨿ F ⟶ A ⨿ (T ⨿ F)))

def coprodSwapAssocIso : A ⨿ (T ⨿ F) ≅ (A ⨿ F) ⨿ T where
  hom := coprodSwapAssocHom A F T
  inv := coprodSwapAssocInv A F T
  hom_inv_id := by
    refine coprod.hom_ext ?_ ?_
    · simp [coprodSwapAssocHom, coprodSwapAssocInv]
    · refine coprod.hom_ext ?_ ?_ <;>
        simp [coprodSwapAssocHom, coprodSwapAssocInv]
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · refine coprod.hom_ext ?_ ?_ <;>
        simp [coprodSwapAssocHom, coprodSwapAssocInv]
    · simp [coprodSwapAssocHom, coprodSwapAssocInv]

theorem coprodSwapAssocIso_hom :
    (coprodSwapAssocIso A F T).hom = coprodSwapAssocHom A F T := rfl
end

theorem isBlowupAlongIdealSheaf_totalTransition_of_coprod_desc i
    (h : IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) $ S.detachedio i) $ S.centerOffDetached i) :
    IsBlowupAlongIdealSheaf (S.totalTransition i) $ S.totalCenter i := by
  have hker : ker (S.centerOffDetached i).si = S.centerOffDetached i := by simp
  have hl : (S.totalCenter i).comap coprod.inl
      = S.centerOffDetached i := by
    rw [S.totalCenter_eq i,
      ker_comp_coprod_inl_comap_inl (Y := S.detachedCoprod i) (S.centerOffDetached i).si, hker]
  have hr : (S.totalCenter i).comap coprod.inr = ⊤ := by
    rw [S.totalCenter_eq i,
      ker_comp_coprod_inl_comap_inr (Y := S.detachedCoprod i) (S.centerOffDetached i).si]
  have h1_ : p15 (coprod.desc (S.strictTransformMap i) $ S.detachedio i)
      ((S.totalCenter i).comap coprod.inl) := by
    rwa [hl]
  have h2_ : p15 (𝟙 $ S.detachedCoprod i)
      ((S.totalCenter i).comap coprod.inr) := by
    rw [hr]
    exact isBlowupAlongIdealSheaf_id_top _
  have hcomp :
      (coprodSwapAssocIso (S.strictTransform $ i + 1) (S.detachedScheme i) $ S.detachedCoprod i).hom ≫
          coprod.map (coprod.desc (S.strictTransformMap i) $ S.detachedio i) (𝟙 $ S.detachedCoprod i) =
        S.totalTransition i := by
    refine coprod.hom_ext ?_ ?_
    simp [coprodSwapAssocIso_hom, coprodSwapAssocHom, EmbeddedBlowupSequence.totalTransition,
      coprod.inl_desc]
    refine coprod.hom_ext ?_ ?_ <;>
      simp [coprodSwapAssocIso_hom, coprodSwapAssocHom, EmbeddedBlowupSequence.totalTransition,
        coprod.inl_desc]
  have hfin := (Blowup.IsBlowupAlongIdealSheaf.coprod h1_ h2_).iso_hom_comp
    (coprodSwapAssocIso (S.strictTransform $ i + 1) (S.detachedScheme i) $ S.detachedCoprod i)
  rwa [hcomp] at hfin

end EmbeddedBlowupSequence

section
variable {k : Type} [Field k]
section
variable [CharZero k] {Y} [IsAffine Y]
section
variable {pY} [LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY)
def EmbeddedBlowupSequence.DetachedLocusIsOpen : Prop :=
  ∀ i < length S, IsOpen $ S.detachedLocus i

def EmbeddedBlowupSequence.AllLevelsNoetherian : Prop :=
  ∀ i ≤ length S, IsNoetherian $ schemeAt S i
end

end

section
variable {X : Sch} (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] (C : Set ↥X)
include p
theorem isClopen_of_mem_irreducibleComponents_of_smooth
    (hC : C ∈ irreducibleComponents ↥X) : IsClopen C :=
  isClopen_irreducibleComponent_of_smooth p inferInstance hC

theorem smooth_subschemeio_vanishingIdeal_comp_of_isClopen (hC : IsClopen C) :
    Smooth
      ((vanishingIdeal
        (⟨C, hC.isClosed⟩ : Closeds ↥X)).subschemeι ≫ p) := by
  have hredX := isReduced_of_smooth p
  obtain ⟨e, he⟩ := exists_iso_subscheme_vanishingIdeal_of_isClosed
    (⟨C, hC.isOpen⟩ : Opn X) hC.isClosed
  have key : Smooth
      ((isoH e ≫ p4 (⟨C, hC.isOpen⟩ : Opn X)) ≫ p) := inferInstance
  rwa [he] at key
end
end

section
variable (A : PrincipalizationAlgorithm)
def DetachedLocusIsOpenForEmbeddings : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] (D : EmbeddingDatum k Y pY),
    EmbeddedBlowupSequence.DetachedLocusIsOpen $ D.toEmbeddedBlowupSequence A

end

namespace EmbeddedBlowupSequence

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]

variable (S : EmbeddedBlowupSequence k Y pY)

section
variable (i : ℕ)
def schemeAtToSpec : schemeAt S i ⟶ Sp k :=
  S.ambientSeq.projectionToBase i ≫ S.ambientStruct

theorem schemeAtToSpec_eq :
    S.schemeAtToSpec i = S.ambientSeq.projectionToBase i ≫ S.ambientStruct := rfl

def strictTransformToSpec : S.strictTransform i ⟶ Sp k :=
  strictTransformio S i ≫ S.schemeAtToSpec i

theorem strictTransformToSpec_eq :
    S.strictTransformToSpec i = strictTransformio S i ≫ S.schemeAtToSpec i := rfl

theorem locallyOfFiniteType_schemeAtToSpec (hi : i ≤ length S) :
    LocallyOfFiniteType $ S.schemeAtToSpec i := by
  have key : ∀ j, j ≤ length S →
      LocallyOfFiniteType (S.ambientSeq.projectionToBase j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [projectionToBase_zero]
      infer_instance
    | succ n ih =>
      intro hn
      have hft :=
        ih $ le_of_succ_le hn
      have hno :=
        S.isNoetherian_schemeAt n $ le_of_succ_le hn
      have hprop :=
        blowupIsProper (schemeAt S n) (schemeAt S $ n + 1) (S.ambientSeq.transitionMapSucc n)
          (S.ambientCenter n) $ S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism n hn
      have hftb : LocallyOfFiniteType $ S.ambientSeq.transitionMapSucc n :=
        inferInstance
      rw [projectionToBase_succ]
      infer_instance
  have := key i hi
  rw [S.schemeAtToSpec_eq i]
  infer_instance

theorem locallyOfFiniteType_strictTransformToSpec (hi : i ≤ length S) :
    LocallyOfFiniteType $ S.strictTransformToSpec i := by
  have hlev :=
    S.locallyOfFiniteType_schemeAtToSpec i hi
  have hio : LocallyOfFiniteType $ strictTransformio S i := inferInstance
  rw [S.strictTransformToSpec_eq i]
  infer_instance
end

end EmbeddedBlowupSequence





theorem nonempty_inter_of_dense_of_mem_irreducibleComponents
    {X : Type} [TopologicalSpace X] [NoetherianSpace X]
    {V} (hV : Dense V) {C} (hC : C ∈ irreducibleComponents X) :
    (C ∩ V).Nonempty := by
  classical
  let _m0 := irreducibleComponents X \ {C}
  have hfin' : _m0.Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun _ h => an1 h
  have hFclosed : IsClosed $ ⋃₀ _m0 := by
    rw [sUnion_eq_biUnion]
    exact hfin'.isClosed_biUnion fun C' hC' => isClosed_of_mem_irreducibleComponents _ hC'.1
  have hnotsub : ¬ C ⊆ ⋃₀ _m0 := by
    intro hsub
    have hsub' : C ⊆ ⋃₀ (hfin'.toFinset : Set $ Set X) := by simp_all
    obtain ⟨z, hz, hCz⟩ := mp_ isIrreducible_iff_sUnion_isClosed (an1 hC) hfin'.toFinset
      (fun z hz => isClosed_of_mem_irreducibleComponents _ (hfin'.mem_toFinset.mp hz).1) hsub'
    have hz' := hfin'.mem_toFinset.mp hz
    exact an2 hz' $ Set.mem_singleton_iff.mpr $ m15 (an2 hC hz'.1.1 hCz) hCz
  obtain ⟨x, hxC, hxF⟩ := mp_ not_subset hnotsub
  have hUsub : (⋃₀ _m0)ᶜ ⊆ C := by
    intro y hy
    by_contra hyC
    have hne : irreducibleComponent y ≠ C := by
      intro h
      apply hyC
      rw [← h]
      exact mem_irreducibleComponent
    exact hy $ Set.mem_sUnion.mpr ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, fun hmm => hne $ Set.mem_singleton_iff.mp hmm⟩, mem_irreducibleComponent⟩
  obtain ⟨y, hyU, hyV⟩ := mp_ mem_closure_iff (hV x) _ hFclosed.isOpen_compl hxF
  exact ⟨y, hUsub hyU, hyV⟩

namespace EmbeddedBlowupSequence

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]

variable (S : EmbeddedBlowupSequence k Y pY)

section
variable (i : ℕ)
theorem isClosedEmbedding_strictTransformio :
    Topology.IsClosedEmbedding ⇑(strictTransformio S i).base := by
  refine ⟨(strictTransformio S i).isEmbedding, ?_⟩
  rw [range_subschemeι ..]
  exact (S.strictTransformIdeal i).support.2

theorem notMem_ambientCenter_support_of_isGenericPoint C
    (hC : C ∈ irreducibleComponents ↥(S.strictTransform i)) (hfr : C ∉ S.detachedComponents i)
    et_ (het_ : IsGenericPoint et_ C) :
    (strictTransformio S i).base et_ ∉ (support (S.ambientCenter i) : CSet $ schemeAt S i) := by
  intro hmem
  refine hfr $ mpr_ (S.mem_detachedComponents i C) ⟨hC, mpr_ image_subset_iff ?_⟩
  rw [← het_]
  exact (IsClosed.preimage (strictTransformio S i).base.hom.continuous (spI $ S.ambientCenter i).2).closure_subset_iff.mpr $ mpr_ singleton_subset_iff hmem

abbrev ambientCenterSupportCompl : (schemeAt S i).Opens := (S.ambientCenter i).support.compl

@[simp] theorem mem_ambientCenterSupportCompl (x : ↥(schemeAt S i)) :
    x ∈ S.ambientCenterSupportCompl i ↔ x ∉ (support (S.ambientCenter i) : CSet $ schemeAt S i) := m22

theorem isIso_blowdown_restrict_ambientCenterSupportCompl (hi : i < length S) :
    IsIso $ S.blowdown i ∣_ S.ambientCenterSupportCompl i := by
  have h1 := (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism i hi).restrict $ suppC $ S.ambientCenter i
  rw [comap_io_support_compl_eq_top $ S.ambientCenter i] at h1
  exact h1.isIso_of_top

def strictTransformOffCenter : (S.strictTransform i).Opens :=
  (TopologicalSpace.Opens.map (strictTransformio S i).base).obj $ S.ambientCenterSupportCompl i


abbrev strictTransformMapPreimageOffCenter : (S.strictTransform $ i + 1).Opens :=
  (TopologicalSpace.Opens.map (S.strictTransformMap i).base).obj $ S.strictTransformOffCenter i

theorem mem_strictTransformMapPreimageOffCenter x :
    x ∈ S.strictTransformMapPreimageOffCenter i ↔
      (strictTransformio S i).base ((S.strictTransformMap i).base x) ∉
        (support (S.ambientCenter i) : CSet $ schemeAt S i) := m22
end

theorem range_strictTransformio_succ [IsReduced Y]
    (hN : ∀ j ≤ length S, IsNoetherian $ schemeAt S j) i (hi : i < length S) :
    range ⇑(strictTransformio S $ i + 1).base =
      closure (⇑(S.blowdown i).base ⁻¹'
        ((support (S.strictTransformIdeal i) : CSet $ schemeAt S i) \
          (support (S.ambientCenter i) : CSet $ schemeAt S i))) := by
  let _a0 := schemeAt S $ i + 1
  have hNi : IsNoetherian _a0 := hN (i + 1) hi
  have hns : m86 _a0 := inferInstance
  have hqc := S.quasiCompact_strictTransformio_blowdown i hns
  have h1 : range (strictTransformio S $ i + 1).base
      = (spI (S.strictTransformIdeal $ i + 1) : Set _a0) :=
    range_subschemeι ..
  rw [h1]
  exact support_strictTransform_eq_closure_preimage (S.blowdown i) (S.ambientCenter i) $ S.strictTransformIdeal i

theorem noetherianSpace_strictTransform_of_isNoetherian
    (hN : ∀ j ≤ length S, IsNoetherian $ schemeAt S j) i (hi : i ≤ length S) :
    NoetherianSpace ↥(S.strictTransform i) := by
  have := hN i hi
  exact S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i inferInstance

theorem exists_irreducibleComponent_isGenericPoint_strictTransformMap [IsReduced Y]
    (hN : ∀ j ≤ S.length, IsNoetherian $ schemeAt S j) i (hi : i < S.length)
    C (hC : C ∈ irreducibleComponents ↥(S.strictTransform $ i + 1))
    et_ (het_ : IsGenericPoint et_ C) :
    ∃ C' : Set ↥(S.strictTransform i), C' ∈ irreducibleComponents ↥(S.strictTransform i) ∧
      IsGenericPoint ((S.strictTransformMap i).base et_) C' ∧ C' ∉ S.detachedComponents i := by
  let _a2 := schemeAt S i
  let _c0 := (spI (S.ambientCenter i) : Set _a2)
  let _c1 := S.strictTransform $ i + 1
  let _c2 := S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i
  let _c3 := (spI (S.strictTransformIdeal i) : Set _a2)
  let _a0 := bsM (S.strictTransformMap i) et_
  let _a4 := S.strictTransform i
  let _c4 := ({_a0} : Set _a4)
  let _c5 := strictTransformio S $ i + 1
  let _c6 := p4 $ S.ambientCenterSupportCompl i
  let _c7 := schemeAt S $ i + 1
  classical
  have hns1 :=
    S.noetherianSpace_strictTransform_of_isNoetherian hN (i + 1) hi
  have hisoG :=
    S.isIso_blowdown_restrict_ambientCenterSupportCompl i hi
  let _a3 := strictTransformio S i
  let _a5 := p4 _c2
  have hcontio' :=
    _a5.base.hom.continuous
  have hcontginv :=
    (m83 $ S.blowdown i ∣_ S.ambientCenterSupportCompl i).base.hom.continuous
  let _a1 := S.blowdown i
  have hcomm : ∀ x,
      _a3.base (bsM (S.strictTransformMap i) x)
        = bsM _a1 (bsM _c5 x) := by
    intro x
    have h2 : bsM (S.strictTransformMap i ≫ strictTransformio S i) x
        = bsM (strictTransformio S (i + 1) ≫ S.blowdown i) x := by
      rw [S.strictTransformMap_comp_strictTransformio i]
    exact h2
  have hrange0 : range (strictTransformio S i).base
      = _c3 :=
    range_subschemeι ..
  have hrange1 : range _c5.base
      = closure ((S.blowdown i).base ⁻¹'
        (_c3 \
          _c0)) :=
    S.range_strictTransformio_succ hN i hi
  have hemb1 :=
    S.isClosedEmbedding_strictTransformio $ i + 1
  let _a7 := S.ambientCenterSupportCompl i
  have hrU : range _c6.base
      = (_a7 : Set _a2) := by
    rw [q1]
  have hrU' : range (Scheme.Opens.ι _c2).base
      = ((S.blowdown i ⁻¹ᵁ S.ambientCenterSupportCompl i) :
          Set _c7) := by
    rw [q1]
  have hioopen : IsOpenMap _c6.base := by
    refine _c6.isEmbedding.toIsInducing.isOpenMap ?_
    rw [hrU]
    exact _a7.2
  have hgcomm : ∀ x : (oSch _c2),
      _c6.base
          (bsM (S.blowdown i ∣_ S.ambientCenterSupportCompl i) x)
        = bsM _a1
          (bsM _a5 x) := by
    intro x
    have h2 : bsM ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫
          p4 (S.ambientCenterSupportCompl i)) x
        = bsM (p4 _c2 ≫ S.blowdown i) x := by
      rw [morphismRestrict_ι]
    exact h2
  have hggi : ∀ y : (oSch _a7),
      (S.blowdown i ∣_ S.ambientCenterSupportCompl i).base
          (bsM (m83 $ S.blowdown i ∣_ S.ambientCenterSupportCompl i) y) = y := by
    intro y
    have h2 : bsM (m83 (S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫
        (S.blowdown i ∣_ S.ambientCenterSupportCompl i)) y = y := by
      rw [m117]
      simp
    exact h2
  have hgig : ∀ x : (oSch _c2),
      (m83 $ S.blowdown i ∣_ S.ambientCenterSupportCompl i).base
          (bsM (S.blowdown i ∣_ S.ambientCenterSupportCompl i) x) = x := by
    intro x
    have h2 : bsM ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫
        m83 (S.blowdown i ∣_ S.ambientCenterSupportCompl i)) x = x := by
      rw [m118]
      simp
    exact h2
  have hLift : ∀ c,
      c ∉ _c0 →
      ∃ c', bsM _a1 c' = c := by
    intro c hc
    have hcU : c ∈ range _c6.base := by
      rwa [hrU]
    obtain ⟨y, hy⟩ := hcU
    refine ⟨bsM _a5
      (bsM (m83 $ S.blowdown i ∣_ S.ambientCenterSupportCompl i) y), ?_⟩
    rw [← hgcomm, hggi, hy]
  have hLiftNext : ∀ c' e',
      _a1.base c' ∉ _c0 →
      _a1.base e' ∉ _c0 →
      _a1.base e'
          ∈ closure ({_a1.base c'} : Set _a2) →
      e' ∈ closure ({c'} : Set _c7) := by
    intro c' e' hc' he' hsp
    have hc'' : c' ∈ range (p4 _c2).base := by
      rwa [hrU']
    have he'' : e' ∈ range (p4 _c2).base := by
      rwa [hrU']
    obtain ⟨x, hx⟩ := hc''
    obtain ⟨w, hw⟩ := he''
    have hsp2 : bsM _c6
          (bsM (S.blowdown i ∣_ S.ambientCenterSupportCompl i) w)
        ∈ closure ({_c6.base
          (bsM (S.blowdown i ∣_ S.ambientCenterSupportCompl i) x)} : Set _a2) := by
      rwa [hgcomm w, hgcomm x, hx, hw]
    have hsp4 := mp_ specializes_iff_mem_closure
      ((mpr_ specializes_iff_mem_closure $ IsOpenMap.mem_closure_singleton_of_apply hioopen _c6.isEmbedding.injective hsp2).map hcontginv)
    rw [hgig w, hgig x] at hsp4
    have hsp5 := mp_ specializes_iff_mem_closure
      ((mpr_ specializes_iff_mem_closure hsp4).map hcontio')
    rwa [hx, hw] at hsp5
  let _a6 := S.strictTransformMapPreimageOffCenter i
  have hWsub : ((S.blowdown i).base ⁻¹'
        (_c3 \
          _c0))
      ⊆ _c5.base ''
        (_a6) := by
    intro w hw
    have hwr : w ∈ range _c5.base := by
      rw [hrange1]
      exact subset_closure hw
    obtain ⟨a, ha⟩ := hwr
    refine ⟨a, ?_, ha⟩
    refine mpr_ (S.mem_strictTransformMapPreimageOffCenter i a) ?_
    rw [hcomm a, ha]
    exact hw.2
  have hVdense : Dense (_a6 : Set _c1) := by
    intro x
    have h2 := closure_mono hWsub
    rw [← hrange1] at h2
    have h3 := h2 $ mem_range_self x
    rw [hemb1.closure_image_eq] at h3
    obtain ⟨y, hy, hyx⟩ := h3
    rwa [hemb1.injective hyx] at hy
  have hetZ : bsM _a3 _a0
      ∉ _c0 := by
    obtain ⟨y, hyC, hyV⟩ :=
      nonempty_inter_of_dense_of_mem_irreducibleComponents hVdense hC
    have hyc := hyC
    rw [← het_] at hyc
    obtain ⟨z, hzV, hzet⟩ :=
      (mp_ mem_closure_iff hyc) (_a6)
        (S.strictTransformMapPreimageOffCenter i).2 hyV
    rw [mem_singleton_iff] at hzet
    rw [hzet] at hzV
    exact mp_ (S.mem_strictTransformMapPreimageOffCenter i et_) hzV
  have hExistsPreimage : ∀ xi_,
      _a0 ∈ closure ({xi_} : Set _a4) →
      ∃ z, bsM (S.strictTransformMap i) z = xi_ ∧
        et_ ∈ closure ({z} : Set _c1) := by
    intro xi_ hmem
    have h1 :=
      specializes_iff_mem_closure.mp $ (mpr_ specializes_iff_mem_closure hmem).map $ _a3.base.hom.continuous
    have hxiZ_ : bsM _a3 xi_ ∉ _c0 := by
      obtain ⟨t, htc, hts⟩ := (mp_ mem_closure_iff h1)
        (_c0ᶜ)
        ((S.ambientCenter i).support.2).isOpen_compl hetZ
      rw [mem_singleton_iff] at hts
      rwa [hts] at htc
    obtain ⟨c', hc'⟩ := hLift (bsM _a3 xi_) hxiZ_
    have hc'W : c' ∈ (S.blowdown i).base ⁻¹'
        (_c3 \
          _c0) := by
      have h5 : bsM _a1 c' ∈ (_c3 \
          _c0) := by
        rw [hc']
        refine ⟨?_, hxiZ_⟩
        rw [← hrange0]
        exact mem_range_self xi_
      exact h5
    have hc'r : c' ∈ range _c5.base := by
      rw [hrange1]
      exact subset_closure hc'W
    obtain ⟨z, hz⟩ := hc'r
    have hfz : bsM (S.strictTransformMap i) z = xi_ := by
      apply (S.isClosedEmbedding_strictTransformio i).injective
      rw [hcomm z, hz, hc']
    refine ⟨z, hfz, ?_⟩
    have hspec : bsM _a1 (bsM _c5 et_)
        ∈ closure ({_a1.base c'} : Set _a2) := by
      rwa [hc', ← hcomm et_]
    have hstep := hLiftNext c' (bsM _c5 et_) (by rw [hc']; exact hxiZ_)
      (by rw [← hcomm et_]; exact hetZ) hspec
    rw [← hz] at hstep
    exact mp_ specializes_iff_mem_closure
      (hemb1.isInducing.specializes_iff.mp $ mpr_ specializes_iff_mem_closure hstep)
  have hmemComp : closure _c4
      ∈ irreducibleComponents _a4 := by
    refine ⟨isIrreducible_singleton.closure, ?_⟩
    intro D hD hsub
    obtain ⟨xi_, hxi_⟩ := sober hD.closure isClosed_closure
    have hxi0_ : _a0 ∈ closure ({xi_} : Set _a4) := by
      rw [hxi_]
      exact subset_closure $ hsub $ subset_closure rfl
    obtain ⟨z, hfz, hetz⟩ := hExistsPreimage xi_ hxi0_
    have hCz : C ⊆ closure ({z} : Set _c1) := by
      rw [← het_]
      exact closure_minimal (mpr_ singleton_subset_iff hetz) isClosed_closure
    have hzC :=
      hC.2 isIrreducible_singleton.closure hCz
    have hzet : z ∈ closure ({et_} : Set _c1) := by
      rw [het_]
      exact hzC $ subset_closure rfl
    have hximem : xi_ ∈ closure _c4 := by
      have hmap := mp_ specializes_iff_mem_closure
        ((mpr_ specializes_iff_mem_closure hzet).map $ (S.strictTransformMap i).base.hom.continuous)
      rwa [hfz] at hmap
    intro d hd
    refine closure_minimal (mpr_ singleton_subset_iff hximem) isClosed_closure ?_
    rw [hxi_]
    exact subset_closure hd
  refine ⟨closure _c4, hmemComp, rfl, ?_⟩
  intro hfr
  exact hetZ $ ((mp_ (S.mem_detachedComponents i _) hfr).2) ⟨_a0, subset_closure rfl, rfl⟩







end EmbeddedBlowupSequence





theorem comap_biSup_finset_fin {X Y : Sch} (f : X ⟶ Y) {n : ℕ}
    (s : FinSet n) (F : Fin n → ISD Y) :
    comap (⨆ i ∈ s, F i) f = ⨆ i ∈ s, comap (F i) f :=
  (map_gc f).l_iSup₂

section
variable (T : MarkedIdealWithBoundary) (Y) (k' : Type) [Field k'] (q : Y ⟶ Sp k') (g : Y ⟶ T.scheme)
theorem pullbackOverField_boundary_get
    (j : Fin T.boundary.length) :
    (T.pbOF q g).boundary.get (pullbackOverFieldIndex T Y k' q g j)
      = comap (T.boundary.get j) g := by
  have h : (T.pbOF q g).boundary.get (pullbackOverFieldIndex T Y k' q g j)
      = (T.boundary.map fun D => cmI D g).get
          (Fin.cast (pullbackOverField_boundary_length T Y k' q g).symm j) := rfl
  rw [h]
  simp [get_eq_getElem, getElem_map]
  rfl

section
variable (J : FinSet T.boundary.length)
theorem intersectionIdeal_pullbackOverField :
    intersectionIdeal (T.pbOF q g).boundary (J.image $ pullbackOverFieldIndex T Y k' q g) =
      comap (intersectionIdeal T.boundary J) g := by
  rw [intersectionIdeal_eq_iSup, intersectionIdeal_eq_iSup, comap_biSup_finset_fin]
  refine le_antisymm ?_ ?_
  refine iSup_le fun j' => iSup_le fun hj' => ?_
  obtain ⟨j, hj, rfl⟩ := mp_ mem_image hj'
  rw [pullbackOverField_boundary_get]
  exact le_iSup_of_le j $ le_iSup_of_le hj le_rfl
  refine iSup_le fun j => iSup_le fun hj => ?_
  rw [← pullbackOverField_boundary_get T Y k' q g j]
  exact le_iSup_of_le (pullbackOverFieldIndex T Y k' q g j)
    (le_iSup_of_le (mem_image_of_mem _ hj) le_rfl)

theorem support_intersectionIdeal_pullbackOverField :
    (↑(intersectionIdeal (T.pbOF q g).boundary
          (J.image $ pullbackOverFieldIndex T Y k' q g)).support :
        Set ↥(T.pbOF q g).scheme) =
      ⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : CSet T.scheme) := by
  have h2 :=
    support_comap g $ intersectionIdeal T.boundary J
  rwa [intersectionIdeal_pullbackOverField T Y k' q g J]

theorem mem_intersectionComponents_pullbackOverField_iff (C' : Set ↥Y) :
    C' ∈ intersectionComponents (T.pbOF q g).boundary (J.image $ pullbackOverFieldIndex T Y k' q g) ↔
      IsIrreducibleComponentOf C' (⇑g ⁻¹' (↑(intersectionIdeal T.boundary J).support : CSet T.scheme)) := by
  have h1 := mem_intersectionComponents_iff (T.pbOF q g).boundary
      (J.image $ pullbackOverFieldIndex T Y k' q g) C'
  rwa [support_intersectionIdeal_pullbackOverField T Y k' q g J] at h1
end
end

theorem IsIrreducibleComponentOf.exists_isGenericPoint {Y : Sch} {C S : Set ↥Y}
    (h : IsIrreducibleComponentOf C S) (hS : IsClosed S) :
    ∃ xi_ : ↥Y, IsGenericPoint xi_ C := by
  obtain ⟨hirr, hsub, hmax⟩ := h
  exact sober hirr $ mp_ closure_eq_iff_isClosed $ hmax (closure C) hirr.closure subset_closure $ hS.closure_subset_iff.mpr hsub

theorem isPreirreducible_sUnion_of_isChain {al_ : Type} [TopologicalSpace al_]
    (c : Set $ Set al_) (hcc : IsChain (· ⊆ ·) c)
    (hirr : ∀ t ∈ c, IsPreirreducible t) : IsPreirreducible $ ⋃₀ c := by
  intro u v hu hv hxne hyne
  obtain ⟨x, hxU, hxu⟩ := hxne
  obtain ⟨y, hyU, hyv⟩ := hyne
  obtain ⟨t1_, ht1c, hxt1⟩ := Set.mem_sUnion.mp hxU
  obtain ⟨t2_, ht2c, hyt2⟩ := Set.mem_sUnion.mp hyU
  rcases eq_or_ne t1_ t2_ with rfl | hne
  obtain ⟨z, hzt, hzuv⟩ := hirr t1_ ht1c u v hu hv ⟨x, hxt1, hxu⟩ ⟨y, hyt2, hyv⟩
  exact ⟨z, Set.mem_sUnion.mpr ⟨t1_, ht1c, hzt⟩, hzuv⟩
  rcases hcc ht1c ht2c hne with h | h
  obtain ⟨z, hzt, hzuv⟩ := hirr t2_ ht2c u v hu hv ⟨x, h hxt1, hxu⟩ ⟨y, hyt2, hyv⟩
  exact ⟨z, Set.mem_sUnion.mpr ⟨t2_, ht2c, hzt⟩, hzuv⟩
  obtain ⟨z, hzt, hzuv⟩ := hirr t1_ ht1c u v hu hv ⟨x, hxt1, hxu⟩ ⟨y, h hyt2, hyv⟩
  exact ⟨z, Set.mem_sUnion.mpr ⟨t1_, ht1c, hzt⟩, hzuv⟩

theorem exists_isIrreducibleComponentOf {Y : Sch} (S A : Set ↥Y) (hA : IsIrreducible A)
    (hAS : A ⊆ S) :
    ∃ C : Set ↥Y, IsIrreducibleComponentOf C S ∧ A ⊆ C := by
  have hchain : ∀ c ⊆ {C : Set Y | IsIrreducible C ∧ C ⊆ S}, IsChain (· ⊆ ·) c →
      c.Nonempty → ∃ ub ∈ {C : Set Y | IsIrreducible C ∧ C ⊆ S}, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hcc hcn
    obtain ⟨t, htc⟩ := hcn
    have hne : (⋃₀ c).Nonempty := by
      obtain ⟨x, hx⟩ := (hcS htc).1.1
      exact ⟨x, Set.mem_sUnion.mpr ⟨t, htc, hx⟩⟩
    refine ⟨⋃₀ c, ⟨⟨hne, isPreirreducible_sUnion_of_isChain c hcc
        fun s hs => (hcS hs).1.2⟩, sUnion_subset fun s hs => (hcS hs).2⟩,
      fun s hs => subset_sUnion_of_mem hs⟩
  obtain ⟨C, hAC, hmax⟩ :=
    zorn_subset_nonempty {C : Set Y | IsIrreducible C ∧ C ⊆ S} hchain A ⟨hA, hAS⟩
  have hmem := an1 hmax
  refine ⟨C, ⟨an1 hmem, an2 hmem, ?_⟩, hAC⟩
  intro C' hC' hCle hC'S
  exact subset_antisymm (an2 hmax ⟨hC', hC'S⟩ hCle) hCle

section
variable {X Y : Sch}
section
variable (g : Y ⟶ X) (hg : GeneralizingMap fun y : ↥Y => g y) {S : Set ↥X} (hS : IsClosed S)
include hg hS
theorem IsIrreducibleComponentOf.closure_image_genericPoint {C'}
    (hC' : IsIrreducibleComponentOf C' $ ⇑g ⁻¹' S) {xi'} (hxi_' : IsGenericPoint xi' C') :
    IsIrreducibleComponentOf (closure {g xi'}) S ∧ MapsTo (⇑g) C' (closure {g xi'}) := by
  let _c0 := ({g xi'} : Set X)
  obtain ⟨-, hsub, hmax⟩ := hC'
  have hxi'eq : closure ({xi'} : Set Y) = C' := hxi_'
  have himg : ∀ z w, z ∈ closure ({w} : Set Y) → g z ∈ closure ({g w} : Set X) := by
    intro z w hz
    have h3 : g z ∈ closure (g '' ({w} : Set Y)) := (image_closure_subset_closure_image g.continuous) ⟨z, hz, rfl⟩
    rwa [image_singleton] at h3
  have hxi'mem : xi' ∈ C' := by
    rw [← hxi'eq]
    exact subset_closure rfl
  have hmaps : MapsTo (g) C' $ closure _c0 := by
    intro y hy
    refine himg y xi' ?_
    rwa [hxi'eq]
  refine ⟨?_, hmaps⟩
  refine ⟨isIrreducible_singleton.closure, hS.closure_subset_iff.mpr $ mpr_ singleton_subset_iff $ hsub hxi'mem, ?_⟩
  intro E hE hsubE hES
  obtain ⟨et_, het_⟩ := sober hE.closure $ isClosed_closure (s := E)
  have heteq : closure ({et_} : Set X) = closure E := het_
  have hspec0 : et_ ⤳ g xi' := by
    refine mpr_ specializes_iff_mem_closure ?_
    rw [heteq]
    exact subset_closure $ hsubE $ subset_closure rfl
  obtain ⟨xi'', hspec, hget_⟩ := hg hspec0
  have hget' : g xi'' = et_ := hget_
  let _s0 := ({xi''} : Set Y)
  have hsub2 : closure _s0 ⊆ preimage g S := by
    intro z hz
    have h3 : g z ∈ closure ({g xi''} : Set X) := himg z xi'' hz
    rw [hget', heteq] at h3
    exact (hS.closure_subset_iff.mpr hES) h3
  have hsub3 : C' ⊆ closure _s0 := by
    rw [← hxi'eq]
    exact closure_minimal (mpr_ singleton_subset_iff $ mp_ specializes_iff_mem_closure hspec) isClosed_closure
  have hxi''mem : xi'' ∈ C' := by
    rw [← hmax (closure _s0) isIrreducible_singleton.closure hsub3 hsub2]
    exact subset_closure rfl
  have hetmem : et_ ∈ closure _c0 := by
    have h4 := hmaps hxi''mem
    rwa [hget'] at h4
  refine m15 (m90 subset_closure ?_) hsubE
  rw [← heteq]
  exact closure_minimal (mpr_ singleton_subset_iff hetmem) isClosed_closure

theorem exists_isIrreducibleComponentOf_preimage {C}
    (hC : IsIrreducibleComponentOf C S) y (hy : g y ∈ C) :
    ∃ C', IsIrreducibleComponentOf C' (⇑g ⁻¹' S) ∧ y ∈ C' ∧ MapsTo (⇑g) C' C ∧
      ∀ xi' xi_, IsGenericPoint xi' C' → IsGenericPoint xi_ C → g xi' = xi_ := by
  classical
  have hcont := g.continuous
  have hSY := IsClosed.preimage hcont hS
  obtain ⟨xi_, hxi_⟩ := IsIrreducibleComponentOf.exists_isGenericPoint hC hS
  have hxieq := hxi_
  obtain ⟨-, hCS, hCmax⟩ := hC
  have hmemC : g y ∈ closure ({xi_} : Set X) := by
    rwa [hxieq]
  obtain ⟨y0_, hy0spec, hy0eq⟩ := hg $ mpr_ specializes_iff_mem_closure hmemC
  have hgy0 : g y0_ = xi_ := hy0eq
  have hxiC_ : xi_ ∈ C := by
    have h0 : xi_ ∈ ({xi_} : Set X) := Set.mem_singleton_iff.mpr rfl
    have h1 := subset_closure h0
    rwa [hxieq] at h1
  have hy0S_ : y0_ ∈ preimage g S := by
    have h2 : g y0_ ∈ S := by rw [hgy0]
                              exact hCS hxiC_
    exact h2
  obtain ⟨C', hC', hAC'⟩ :=
    exists_isIrreducibleComponentOf (preimage g S) (closure ({y0_} : Set Y))
      (IsIrreducible.closure isIrreducible_singleton) $ closure_minimal (mpr_ singleton_subset_iff hy0S_) hSY
  have hy0C' : y0_ ∈ C' := by
    exact hAC' $ subset_closure $ Set.mem_singleton_iff.mpr rfl
  have key : ∀ ζ, IsGenericPoint ζ C' → closure ({g ζ} : Set X) = C := by
    intro ζ hze
    obtain ⟨hcomp, -⟩ := IsIrreducibleComponentOf.closure_image_genericPoint g hg hS hC' hze
    obtain ⟨hirr2, hsub2, -⟩ := hcomp
    let _a1 := closure ({ζ} : Set Y)
    have hzeeq : _a1 = C' := hze
    have h4 : y0_ ∈ _a1 := by rw [hzeeq]
                              exact hy0C'
    have h6 := image_closure_subset_closure_image hcont $ Set.mem_image_of_mem (g) h4
    rw [image_singleton, hgy0] at h6
    refine hCmax (closure ({g ζ} : Set X)) hirr2 ?_ hsub2
    rw [← hxieq]
    exact closure_minimal (mpr_ singleton_subset_iff h6) isClosed_closure
  obtain ⟨ze0, hze0⟩ := IsIrreducibleComponentOf.exists_isGenericPoint hC' hSY
  have hmapsC : MapsTo (g) C' C := by
    have h7 := (IsIrreducibleComponentOf.closure_image_genericPoint g hg hS hC' hze0).2
    rwa [key ze0 hze0] at h7
  refine ⟨C', hC', hAC' $ mp_ specializes_iff_mem_closure hy0spec, hmapsC, ?_⟩
  intro ζ xi2_ hgen1 hgen2
  have h8 := key ζ hgen1
  have h9 := hgen2
  have hm1 : g ζ ∈ closure ({xi2_} : Set X) := by
    rw [h9, ← h8]
    exact subset_closure $ Set.mem_singleton_iff.mpr rfl
  refine ((mpr_ specializes_iff_mem_closure ?_).antisymm
    (mpr_ specializes_iff_mem_closure hm1)).eq
  rw [h8, ← h9]
  exact subset_closure $ Set.mem_singleton_iff.mpr rfl
end

section
variable (W : ISD X) (g : Y ⟶ X)
theorem exists_isPullback_comapSubscheme :
    ∃ c : (W.comap g).subscheme ⟶ W.subscheme,
      IsPullback c (W.comap g).si W.si g := by
  obtain ⟨e, he⟩ : ∃ e : subS (cmI W g) ≅ m131 g W.si,
      e.hom ≫ fst g W.si = siI (cmI W g) :=
    ⟨W.comapIso g, W.comapIso_hom_fst g⟩
  refine ⟨isoH e ≫ snd g W.si, ?_⟩
  refine (of_iso_pullback ⟨?_⟩ e he rfl).flip
  rw [← he]
  simp [assoc, condition]

def comapSubschemeHom :
    subscheme (comap W g) ⟶ subscheme W :=
  (exists_isPullback_comapSubscheme W g).choose

theorem isPullback_comapSubschemeHom :
    IsPullback (comapSubschemeHom W g) (comap W g).subschemeι W.subschemeι g :=
  (exists_isPullback_comapSubscheme W g).choose_spec

end
end

theorem exists_intersectionComponents_mapsTo_of_flat (T : MarkedIdealWithBoundary) (_hT : T.IsAdmissible)
    (Y : Sch) (k' : Type) [Field k'] (q : Y ⟶ Sp k')
    (g : Y ⟶ T.scheme) [Flat g]
    (_hT' : (T.pbOF q g).IsAdmissible)
    (J : FinSet T.boundary.length) (C' : Set ↥Y)
    (hC' : C' ∈ intersectionComponents (T.pbOF q g).boundary
      (J.image $ pullbackOverFieldIndex T Y k' q g)) :
    ∃ C ∈ intersectionComponents T.boundary J,
      MapsTo (⇑g) C' C ∧
        ∀ xi' xi_, IsGenericPoint xi' C' → IsGenericPoint xi_ C → g xi' = xi_ := by
  have hS :=
    (intersectionIdeal T.boundary J).support.2
  have hcomp :=
    (mem_intersectionComponents_pullbackOverField_iff T Y k' q g J C').mp hC'
  obtain ⟨xi0, hxi0⟩ := IsIrreducibleComponentOf.exists_isGenericPoint hcomp $ hS.preimage g.continuous
  obtain ⟨hCmem, hmaps⟩ := IsIrreducibleComponentOf.closure_image_genericPoint g (generalizingMap (f := g)) hS hcomp hxi0
  let _m0 := ({g xi0} : CSet T.scheme)
  refine ⟨closure _m0,
    (mem_intersectionComponents_iff T.boundary J $ closure _m0).mpr hCmem, hmaps, ?_⟩
  intro xi' xi_ hxi_' hxi_
  have h2 : IsGenericPoint (g xi0) $ closure _m0 := rfl
  rw [hxi_'.eq hxi0]
  exact h2.eq hxi_

theorem exists_mem_intersectionComponents_pullbackOverField_of_flat (T : MarkedIdealWithBoundary) (_hT : T.IsAdmissible)
    (Y : Sch) (k' : Type) [Field k'] (q : Y ⟶ Sp k')
    (g : Y ⟶ T.scheme) [Flat g]
    (_hT' : (T.pbOF q g).IsAdmissible)
    (J : FinSet T.boundary.length) (C : CSet T.scheme)
    (hC : C ∈ intersectionComponents T.boundary J) (y : ↥Y) (hy : g y ∈ C) :
    ∃ C' ∈ intersectionComponents (T.pbOF q g).boundary
        (J.image $ pullbackOverFieldIndex T Y k' q g),
      y ∈ C' ∧
        ∀ xi' xi_, IsGenericPoint xi' C' → IsGenericPoint xi_ C → g xi' = xi_ := by
  classical
  have hg : GeneralizingMap g := by
    apply generalizingMap
  obtain ⟨C', hC'comp, hyC', _, hgen⟩ :=
    exists_isIrreducibleComponentOf_preimage g hg ((intersectionIdeal T.boundary J).support.2) ((mem_intersectionComponents_iff T.boundary J C).mp hC) y hy
  exact ⟨C', mpr_ (mem_intersectionComponents_pullbackOverField_iff T Y k' q g J C') hC'comp, hyC', hgen⟩

def subschemePreimageOpens {X : Sch} (W : ISD X) (A : Set ↥X)
    (h : IsOpen $ ⇑W.subschemeι ⁻¹' A) : W.subscheme.Opens :=
  ⟨⇑W.subschemeι ⁻¹' A, h⟩

theorem exists_isOpen_comap_ker_of_flat {X Y : Sch} (g : Y ⟶ X)
    [Flat g]
    (W : ISD X) (W' : ISD Y) (hW : W' = W.comap g)
    (A : Set ↥X) (A' : Set ↥Y) (hA' : A' = ⇑g ⁻¹' A)
    (hA : IsOpen $ ⇑W.subschemeι ⁻¹' A)
    (hqc : QuasiCompact $ (subschemePreimageOpens W A hA).ι ≫ W.subschemeι) :
    ∃ h' : IsOpen $ ⇑W'.subschemeι ⁻¹' A',
      (ker $ (subschemePreimageOpens W A hA).ι ≫ W.subschemeι).comap g =
        ker ((subschemePreimageOpens W' A' h').ι ≫ W'.subschemeι) := by
  let _a2 := isPullback_comapSubschemeHom W g
  subst hW
  subst hA'
  have := hqc
  have hbase : ∀ x,
      siI W (comapSubschemeHom W g x) = g (siI (cmI W g) x) := by
    intro x
    exact congrArg (fun m => m x) $ _a2.w
  let _a0 := comapSubschemeHom W g
  have hset : (cmI W g).si ⁻¹' (g ⁻¹' A)
      = _a0 ⁻¹' (W.si ⁻¹' A) := by
    ext x
    simp [mem_preimage]
    rw [hbase x]
  have hopen := hA.preimage _a0.continuous
  rw [← hset] at hopen
  refine ⟨hopen, ?_⟩
  have hV : subschemePreimageOpens (cmI W g) (preimage g A) hopen
      = comapSubschemeHom W g ⁻¹ᵁ subschemePreimageOpens W A hA := by
    apply m55
    exact hset
  rw [hV]
  have hsq2 := (m226 _a0
    (subschemePreimageOpens W A hA)).paste_vert _a2
  have := quasiCompact_of_isPullback hsq2
  exact sy_ $ ker_eq_comap_ker_of_isPullback_of_flat hsq2




namespace DivisorReduction

section
variable {A B : Sch} (g : A ⟶ B) [IsIso g]
theorem smooth_of_isIso :
    Smooth g := inferInstance

private theorem surjective_of_isIso :
    Surjective g := inferInstance
end

section
variable {X W : Sch} {a b : W ⟶ X} (h : a = b)
include h
theorem comap_congr
    (I : ISD X) : comap I a = comap I b := by
  subst h
  rfl

theorem map_comap_congr
    (M : Bdy X) :
    map (fun D : ISD X => comap D a) M
      = map (fun D : ISD X => comap D b) M := by
  subst h
  rfl
end

theorem map_comap_map_comap_eq_map_comap_comp {X Y W : Sch} (a : W ⟶ Y) (b : Y ⟶ X)
    (M : Bdy X) :
    map (fun D : ISD Y => comap D a)
        (map (fun D : ISD X => comap D b) M)
      = map (fun D : ISD X => comap D $ a ≫ b) M :=by simp_all
theorem sameNontrivialBoundary_of_eq_right {X : Sch} {A B B' : Bdy X}
    (h : SameNontrivialBoundary A B) (hB : B = B') : SameNontrivialBoundary A B' :=
  hB ▸ h

theorem exists_smooth_surjective_to_restrictToBoundaryDivisor_baseChange (T : MarkedIdealWithBoundary) (j : ℕ)
    (hj : j < T.boundary.length) (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.bc f).scheme.IdealSheafData) (hjE : j < E'.length)
    (hget : E'.lget j hjE = (T.bget j hj).comap (fBCP T f))
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData)
    (I0' : (T.bc f).scheme.IdealSheafData)
    (E0' : List (T.bc f).scheme.IdealSheafData)
    (hI0' : I0' = I0.comap (fBCP T f))
    (hE0' : SameNontrivialBoundary (take (E'.length - 1) (E0'.eraseIdx j))
      (map (fun D => D.comap (fBCP T f))
        (take (T.boundary.length - 1) (E0.eraseIdx j)))) :
    ∃ (E'' : List ((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).scheme.IdealSheafData)
      (e : (E'.lget j hjE).subscheme ⟶ ((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).scheme),
      Smooth e ∧
      Surjective e ∧
      SameNontrivialBoundary E'' ((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).boundary ∧
      e ≫ fst (restrictToBoundaryDivisor T j hj I0 E0).structMap
            (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I0 E0).base K f) =
          divisorPullbackMap T j hj I0 E0 (T.bc f).scheme (fBCP T f)
            (E'.lget j hjE) hget ∧
      e ≫ (((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).withBoundary E'').structMap =
          (E'.lget j hjE).si ≫ (T.bc f).structMap ∧
      SameNontrivialBoundary
        (map (fun D => D.comap (E'.lget j hjE).si)
          (take (E'.length - 1) (E0'.eraseIdx j)))
        (map (fun D => D.comap e) E'') ∧
      (((T.bc f).withSchemeIdealBoundary (E'.lget j hjE).subscheme
            ((E'.lget j hjE).si ≫ (T.bc f).structMap)
            (I0'.comap (E'.lget j hjE).si)
            (map (fun D => D.comap (E'.lget j hjE).si)
              (take (E'.length - 1) (E0'.eraseIdx j)))).IsAdmissible →
          (((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).withBoundary E'').IsAdmissible) ∧
      (((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).withBoundary E'').krullDimSucc =
        ((T.bc f).withSchemeIdealBoundary (E'.lget j hjE).subscheme
            ((E'.lget j hjE).si ≫ (T.bc f).structMap)
            (I0'.comap (E'.lget j hjE).si)
            (map (fun D => D.comap (E'.lget j hjE).si)
              (take (E'.length - 1) (E0'.eraseIdx j)))).krullDimSucc := by
  let _a7 := bcT T f
  let _a0 := E'.lget j hjE
  let _a1 := restrictToBoundaryDivisor T j hj I0 E0
  let _a2 := fBCP T f
  let _a3 := bget' hj
  let _a4 := take (E'.length - 1) $ E0'.eraseIdx j
  let _a5 := tMp _a7
  classical
  subst hI0'
  have hsq :=
    by
    exact (isPullback_subschemeMapOfComap _ _ _a2
      _a3 _a0 hget).paste_vert (of_hasPullback _ _)
  let _a6 := specMapOfFieldHom _a1.base K f
  let _a8 := fst _a1.structMap _a6
  let _a9 := snd _a1.structMap _a6
  have hQ : IsPullback
      _a8
      _a9
      _a1.structMap
      _a6 :=
    of_hasPullback _ _
  obtain ⟨ee, hfst, hsnd, hinv1, hinv2⟩ :
      ∃ ee : _ ≅ _,
        ee.hom ≫ _a8 =
            subschemeMapOfComap _a2 _a3
              _a0 hget ∧
          ee.hom ≫ _a9 =
            siI _a0 ≫ _a5 ∧
          ee.inv ≫ subschemeMapOfComap _a2 _a3
              _a0 hget =
            _a8 ∧
          ee.inv ≫ (siI _a0 ≫ _a5) =
            _a9 :=
    ⟨hsq.isoIsPullback _ _ hQ, hsq.isoIsPullback_hom_fst _ _ hQ,
      hsq.isoIsPullback_hom_snd _ _ hQ, hsq.isoIsPullback_inv_fst _ _ hQ,
      hsq.isoIsPullback_inv_snd _ _ hQ⟩
  have hbe := sameNontrivialBoundary_comap_subschemeio _a2 _a3
      _a0 hget (take (bLen T - 1) (E0.eraseIdx j))
      _a4 hE0'
  refine ⟨map (fun D : _a0.subscheme.IdealSheafData => cmI D ee.inv)
      (map (fun D : tISD _a7 =>
        D.comap _a0.si) _a4),
      ee.hom, smooth_of_isIso ee.hom, surjective_of_isIso ee.hom, ?_, tr_ hfst rfl.symm, hsnd, ?_, ?_,
      krullDimSucc_eq_of_iso ee.symm⟩
  exact sameNontrivialBoundary_of_eq_right (MarkedIdealWithBoundary.SameNontrivialBoundary.comap ee.inv hbe)
    (tr_ (tr_ (map_comap_map_comap_eq_map_comap_comp ee.inv (subschemeMapOfComap _a2
          _a3 _a0 hget) _)
        (map_comap_congr hinv1 _))
      (baseChange_boundary _a1 K f).symm)
  exact sameNontrivialBoundary_of_eq_right (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _)
    (tr_ (tr_ (map_comap_map_comap_eq_map_comap_comp ee.hom ee.inv _)
        (map_comap_congr ee.hom_inv_id _)) (list_map_comap_id _ _)).symm
  intro hS
  have hval := isAdmissible_comap_of_iso ee.symm
    (siI _a0 ≫ _a5)
    (cmI (cmI I0 _a2) _a0.si) T.mult
    (map (fun D : tISD _a7 =>
      D.comap _a0.si) _a4) hS
  exact isAdmissible_congr hinv2 ((congrArg (fun J : _a0.subscheme.IdealSheafData => cmI J ee.symm.hom) ((comap_subschemeMapOfComap _a2 _a3 _a0 hget I0).symm)).trans (tr_ (st_ (comap_comp _ ee.symm.hom _) (comap_congr hinv1 _)) (baseChange_ideal _a1 K f).symm)) rfl rfl hval

end DivisorReduction




theorem orderAt_comap_eq_of_notMem_exceptionalIdeal
    (T : MarkedIdealWithBoundary) (_hT : T.IsAdmissible) (Z : tISD T)
    X' (pi_ : X' ⟶ T.scheme) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
    x' (hx' : x' ∉ support (exceptionalIdeal pi_ Z))
    (A : tISD T) :
    orderAt (comap A pi_) x' = orderAt A (pi_.base x') := by
  have hx : bsM pi_ x' ∉ spI Z := by
    intro hc
    apply hx'
    rw [p9]
    exact mpr_ mem_support_comap hc
  haveI := isIso_stalkMap_of_isBlowupAlongIdealSheaf pi_ Z hpi_ x' hx
  exact orderAt_comap_of_isIso_stalkMap pi_ A x'

theorem monomialGeometryHypotheses_direct : MonomialGeometryHypotheses where
  card_lt_dim := MonomialCodimension.card_lt_krullDimSucc_of_nonempty
  flat_comap_center := by
    intro T hT Y k' hk q g hg hT' J Cc_ hCc_ hop
    classical
    have := hT.isNoetherian
    have hns : m86 T.scheme := inferInstance
    let _m0 := intersectionIdeal T.boundary J
    have hSclosed :=
      _m0.support.2
    let _a0 := J.image $ pullbackOverFieldIndex T Y k' q g
    let _a1 := T.pbOF q g
    have hU : (⋃₀ {C' : Set Y | C' ∈ intersectionComponents _a1.boundary
          _a0 ∧ ∃ C ∈ Cc_, MapsTo (g) C' C})
        = g ⁻¹' ⋃₀ Cc_ := by
      ext y
      simp [mem_sUnion, mem_ofPred_eq, mem_preimage]
      constructor
      rintro ⟨C', ⟨-, C, hCCc, hmaps⟩, hyC'⟩
      exact ⟨C, hCCc, hmaps hyC'⟩
      rintro ⟨C, hCCc, hyC⟩
      obtain ⟨C', hC'mem, hyC', hgen⟩ :=
        exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y k' q g hT' J C (hCc_ hCCc) y hyC
      obtain ⟨C0_, hC0mem, hmaps0, hgen0⟩ :=
        exists_intersectionComponents_mapsTo_of_flat T hT Y k' q g hT' J C' hC'mem
      obtain ⟨xi', hxi_'⟩ := IsIrreducibleComponentOf.exists_isGenericPoint
        (mp_ (mem_intersectionComponents_pullbackOverField_iff T Y k' q g J C') hC'mem) (hSclosed.preimage g.continuous)
      obtain ⟨xi_, hxi_⟩ := IsIrreducibleComponentOf.exists_isGenericPoint
        (mp_ (mem_intersectionComponents_iff T.boundary J C) (hCc_ hCCc)) hSclosed
      obtain ⟨xi0, hxi0⟩ := IsIrreducibleComponentOf.exists_isGenericPoint
        (mp_ (mem_intersectionComponents_iff T.boundary J C0_) hC0mem) hSclosed
      have h3 : C0_ = C := by rw [← hxi0, ← hxi_, ← hgen xi' xi_ hxi_' hxi_, ← hgen0 xi' xi0 hxi_' hxi0]
      refine ⟨C', ⟨hC'mem, C, hCCc, ?_⟩, hyC'⟩
      rwa [← h3]
    have hqc : QuasiCompact ((opI (subschemePreimageOpens _m0 (⋃₀ Cc_) hop)) ≫ siI _m0) := by
      have h := hns
      exact haveI := h
  haveI :=
    (((isClosedEmbedding (siI _m0)).toIsEmbedding.toIsInducing).comp
      (opI (subschemePreimageOpens _m0 (⋃₀ Cc_) hop)).isOpenEmbedding.toIsEmbedding.toIsInducing).noetherianSpace
  ⟨fun _ _ _ => isCompact _⟩
    obtain ⟨h', hker⟩ := exists_isOpen_comap_ker_of_flat g _m0
      (intersectionIdeal _a1.boundary _a0)
      (intersectionIdeal_pullbackOverField T Y k' q g J) (⋃₀ Cc_)
      (⋃₀ {C' : Set Y | C' ∈ intersectionComponents _a1.boundary
          _a0 ∧ ∃ C ∈ Cc_, MapsTo (g) C' C})
      hU hop hqc
    exact ⟨h', hker⟩
  center_smooth := MonomialCenterGeometry.smooth_componentUnionIdeal
  center_snc := MonomialCenterGeometry.hasStrictNormalCrossingsWith_componentUnionIdeal
  center_support := by
    intro T hT J Cc_ hCc_ hop
    exact componentUnionIdeal_support_eq_sUnion T hT J Cc_ hCc_ hop
  blowup_total_transform := _root_.FunctorialResolution.EmbeddedResolution.comap_eq_strictTransform_mul_exceptionalIdeal_pow
  flat_components_down := by
    intro T hT Y k' hk q g hg hT' J C' hC'
    exact FunctorialResolution.EmbeddedResolution.exists_intersectionComponents_mapsTo_of_flat T hT Y k' q g hT' J C' hC'
  flat_components_up := by
    intro T hT Y k' hk q g hg hT' J C hC y hy
    exact FunctorialResolution.EmbeddedResolution.exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y k' q g hT' J C hC y hy
  components_disjoint := by
    intro T hT J C hC C' hC' hne
    exact intersectionComponents_disjoint_of_smooth T J (MonomialChart.smooth_intersectionIdeal_subscheme T hT J) C C' hC hC' hne
  components_finite := by
    intro T hT J
    exact intersectionComponents_finite T hT J
  components_subset_divisor_iff := intersectionComponents_subset_support_iff
  transformed_components := intersectionComponents_transformedBoundary_of_isBlowupAlongIdealSheaf
  level_schemeDim_le := by
    intro T hT s i hi
    have h := transformAt_dim_le dimensionNonincreasingAlongBlowups hT s i hi
    rwa [transformAt_dim] at h
  level_valid := by
    intro T hT s i hi
    exact p38 effectiveCartierSupportContainsNoComponent hT s i hi
  orderAt_bounded := by
    intro T hT I hI
    exact exists_orderAt_le T hT I hI
  orderAt_comap_off_exceptional := fun T hT X' pi_ Z hpi_ x' hx' A => orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' pi_ hpi_ x' hx' A
  orderAt_boundary_eq_one := MonomialChart.orderAt_boundary_eq_one
  sUnion_isOpen := by
    intro T hT J Cc_ hCc_
    exact isOpen_preimage_sUnion_intersectionComponents T hT J (MonomialChart.smooth_intersectionIdeal_subscheme T hT J) Cc_ hCc_
  withBoundary_valid := by
    intro T hT E' hE
    apply validOfSameNontrivialBoundary <;> assumption

theorem principalizationGeometryHypotheses : PrincipalizationGeometryHypotheses where
  maxContactTransport := isoInvariantOrderCertificateDescend
  exceptional_components_not_subset := by
    intro T hT Z hZsm hZsnc X' pi_ hpi_ J c hord J' htr C' hC'
    have := hT.charZero
    have := hT.smooth
    have := hT.isNoetherian
    have := isLocallyNoetherian_of_isBlowupAlongIdealSheaf pi_ Z hpi_
    refine controlledTransform_not_subset_support T.structMap Z T.boundary hZsnc pi_ hpi_
      J c hord J' htr C' hC'.1 hC'.2.1 ?_
    intro S hirr hsub hsup
    exact hC'.2.2 S hirr hsup hsub
  orderAt_baseChange := by
    intro T hT L hL hLz f I y
    have := hT.charZero
    have := hT.smooth
    exact orderAt_comap_fieldBaseChange T.structMap (ofHom f) I y
  controlledTransform_orderAt_le := by
    intro T hT Z hZsm hZsnc X' pi_ hpi_ J c hJ J' hJ' x' hx'
    have := hT.charZero
    have := hT.smooth
    have hN := hT.isNoetherian
    have hlocNoeth : IsLocallyNoetherian T.scheme := inferInstance
    have hLN' :=
      isLocallyNoetherian_of_isBlowupAlongIdealSheaf pi_ Z hpi_
    have hsub : suppI Z ⊆ orderAtLeastLocus J c := by
      intro x hx
      exact (mem_orderAtLeastLocus_iff J c x).2 (hJ x hx).ge
    have hI :=
      le_pow_of_hasStrictNormalCrossingsWith T.structMap Z J T.boundary hZsnc c hsub
    have hJ'eq :=
      eq_controlledTransform_of_mul_eq_comap pi_ Z J c hpi_ hI J' hJ'
    rw [hJ'eq]
    refine orderAt_controlledTransform_le_of_orderAt_image_le T.base T.structMap pi_ Z T.boundary
      hZsnc hpi_ J c hI x' ?_
    have h1 :=
      mem_support_comap.1
        (by rw [← p9 pi_ Z]; exact hx')
    exact le_of_eq $ hJ _ h1
  splitting_smooth_pullback := by
    intro T hT Y q h hsm hq hV M N hs
    have : Flat h := inferInstance
    exact isMonomialSplitting_comap_of_flat h hs
  splitting_exists := by
    intro T hT
    have := hT.charZero
    have := hT.smooth
    have := hT.locallyOfFiniteType
    have := hT.quasiCompact
    have := hT.isNoetherian
    exact exists_isMonomialSplitting T.structMap T.boundary hT.snc T.ideal
      hT.nonzeroOnComponents
  splitting_unique := by
    intro T hT M N M' N' hs hs'
    have := hT.charZero
    have := hT.smooth
    have := hT.locallyOfFiniteType
    have := hT.quasiCompact
    have := hT.isNoetherian
    exact isMonomialSplitting_unique T.structMap T.boundary hT.snc
      hT.nonzeroOnComponents hs hs'
  strictTransform_components := by
    intro T hT Z _hsm _hsnc X' pi_ hpi_ D _hD C' hC'
    have hTnoeth := hT.isNoetherian
    have hX'noeth := isNoetherian_of_isBlowupAlongIdealSheaf hpi_
    have hX'loc : IsLocallyNoetherian X' := inferInstance
    have hX'top : m86 X' := inferInstance
    obtain ⟨hC'irr, hC'sub, hC'max⟩ := hC'
    have hcont := pi_.continuous
    let _a4 := spI $ p6 pi_ Z D
    let _s0 := (_a4 : Set X')
    have hSclosed :=
      _a4.2
    let _a0 := closure $ preimage pi_.base $ suppI D \ suppI Z
    have hSeq : _s0
        = _a0 :=
      support_strictTransform_eq_closure_preimage pi_ Z D
    have hC'closed : IsClosed C' := by
      have h1 :=
        hC'max (closure C') hC'irr.closure subset_closure
          (hSclosed.closure_subset_iff.mpr hC'sub)
      rw [← h1]
      exact isClosed_closure
    obtain ⟨et', hgen⟩ := sober hC'irr hC'closed
    let _s3 := ({et'} : Set X')
    have het'' := hgen
    obtain ⟨O, hOopen, hOne, hOsub⟩ :=
      exists_isOpen_inter_subset_of_maximal _s0
        hSclosed C' hC'irr hC'sub hC'max
    obtain ⟨w, hwO, hwS⟩ := hOne
    have hwA : w ∈ _a0 := by simp_all
    obtain ⟨a, haO, haA⟩ := mp_ mem_closure_iff hwA O hOopen hwO
    have haS : a ∈ _s0 := by
      rw [hSeq]
      exact subset_closure haA
    have hVopen :=
      (pi_.pre $ suppC Z).isOpen
    have het'V : et' ∈ ((pi_.pre (suppC Z) : Opn X') : Set X') := by
      have h1 : a ∈ closure _s3 := by rw [het'']
                                      exact hOsub ⟨haO, haS⟩
      obtain ⟨z, hzV, hz⟩ := mp_ mem_closure_iff h1 _ hVopen $ haA.2
      rwa [hz] at hzV
    have hpiet' := het'V
    have het'S : et' ∈ _s0 := by
      refine hC'sub ?_
      rw [← het'']
      exact subset_closure rfl
    let _a1 := suppI D
    let _a3 := (pi_.base) et'
    have hpiet'D : _a3 ∈ _a1 := by
      have h2 : et' ∈ _a0 := by
        rw [← hSeq]
        exact het'S
      exact (closure_minimal (preimage_mono sdiff_subset) $ IsClosed.preimage hcont D.support.2) h2
    let _s1 := ({_a3} : CSet T.scheme)
    have hCmax : ∀ C2_, IsIrreducible C2_ →
        closure _s1 ⊆ C2_ →
        C2_ ⊆ _a1 →
        C2_ = closure _s1 := by
      intro C2_ hC2irr hCC2 hC2D
      obtain ⟨xi_, hgen2⟩ := sober hC2irr.closure isClosed_closure
      have hxi2_ := hgen2
      have hxiD_ : xi_ ∈ _a1 := by
        refine (closure_minimal hC2D D.support.2) ?_
        rw [← hxi2_]
        exact subset_closure rfl
      have hspec : _a3 ∈ closure ({xi_} : CSet T.scheme) := by
        rw [hxi2_]
        exact subset_closure $ hCC2 $ subset_closure rfl
      have hxiZ_ : xi_ ∉ suppI Z := by
        intro hmem
        exact hpiet' $ (closure_minimal (mpr_ singleton_subset_iff hmem) Z.support.2) hspec
      obtain ⟨x, hx1, hx2⟩ :=
        exists_lift_of_specializes_of_isBlowupAlongIdealSheaf pi_ Z hpi_ xi_ hxiZ_ et' hpiet' hspec
      have hx1' := hx1
      have hxmem : (pi_.base) x
          ∈ suppI D \ suppI Z := by
        rw [hx1']
        exact ⟨hxiD_, hxiZ_⟩
      have hxS : x ∈ _s0 := by
        rw [hSeq]
        exact subset_closure hxmem
      let _m0 := ({x} : Set X')
      have hclx :=
        closure_minimal (mpr_ singleton_subset_iff hxS) hSclosed
      have hsub2 : C' ⊆ closure _m0 := by
        rw [← het'']
        exact closure_minimal (mpr_ singleton_subset_iff hx2) isClosed_closure
      have heq :=
        hC'max (closure _m0) isIrreducible_singleton.closure hsub2 hclx
      have hxC' : x ∈ closure _s3 := by
        rw [het'', ← heq]
        exact subset_closure rfl
      have himg :=
        image_closure_subset_closure_image hcont ⟨x, hxC', rfl⟩
      rw [image_singleton] at himg
      have hxiC_ : xi_ ∈ closure _s1 := by
        rw [← hx1']
        exact himg
      refine m15 ?_ hCC2
      refine subset_trans subset_closure ?_
      rw [← hxi2_]
      exact closure_minimal (mpr_ singleton_subset_iff hxiC_) isClosed_closure
    refine ⟨et', closure _s1, sy_ het'',
      notMem_support_exceptionalIdeal pi_ Z et' hpiet', ⟨isIrreducible_singleton.closure, closure_minimal (mpr_ singleton_subset_iff hpiet'D) D.support.2, hCmax⟩, ?_, rfl⟩
    intro hsub
    exact hpiet' $ hsub $ subset_closure rfl
  monomialInputs := monomialGeometryHypotheses_direct
namespace DivisorReductionEmptyOrderLocus

theorem blowupMorphism_mem_orderAtLeastLocus {k : Type} [Field k] [CharZero k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
    {E : Bdy X} (s : MarkedSequenceOfBlowups p I m E) (hm : 1 ≤ m)
    (hsm : ∀ i, i ≤ s.length → Smooth (projectionToSpec s i))
    (hno : ∀ i, i ≤ s.length → IsNoetherian (s.schemeAt i))
    (i : ℕ) (hi : i < s.length) (z : s.schemeAt $ i + 1)
    (hz : z ∈ orderAtLeastLocus (s.ideal $ i + 1) m) :
    (s.transitionMapSucc i) z ∈ orderAtLeastLocus (s.ideal i) m := by
  let _a0 := s.ideal $ i + 1
  let _c0 := p5 (s.transitionMapSucc i) (s.center i) * _a0
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (succ_pred_eq_of_pos hm).symm⟩
  have := hsm i hi.le
  have := hno (i + 1) hi
  have hsnc : HasStrictNormalCrossingsWith (projectionToSpec s i) (s.center i) $ s.boundary i := by
    rw [projectionToSpec_eq]
    exact s.center_snc i hi
  have hI :=
    le_pow_of_hasStrictNormalCrossingsWith (projectionToSpec s i) (s.center i) (s.ideal i)
      (s.boundary i) hsnc n $ (s.center_order i hi).trans $ orderAtLeastLocus_subset_of_le (s.ideal i) $ le_succ n
  have hpb := s.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have key := orderAtLeastLocus_controlledTransform_subset_preimage k
      (projectionToSpec s i) (s.transitionMapSucc i) (s.center i) (s.boundary i) hsnc hpb
      (s.ideal i) n hI
  have hmul : p5 (s.transitionMapSucc i) (s.center i) ^ n *
      _c0
      = (s.ideal i).comap (s.transitionMapSucc i) := by
    rw [← mul_assoc, ← pow_succ]
    exact s.ideal_succ i hi
  have heq := eq_controlledTransform_of_mul_eq_comap (s.transitionMapSucc i) (s.center i) (s.ideal i) n hpb hI
      _c0 hmul
  have hz' : z ∈ orderAtLeastLocus
      _c0 (n + 1) := by
    rw [mem_orderAtLeastLocus_iff] at hz ⊢
    exact hz.trans $ (self_le_add_left _ _).trans
      (add_orderAt_le_orderAt_mul (p5 (s.transitionMapSucc i) $ s.center i)
        _a0 z)
  rw [heq] at hz'
  exact key hz'

section
variable {T : MarkedIdealWithBoundary} (hV : T.IsAdmissible)
include hV
private theorem projectionToBase_mem_orderAtLeastLocus (s : T.SequenceOfBlowups) :
    ∀ i, i ≤ s.length → ∀ z : s.schemeAt i,
      z ∈ orderAtLeastLocus (s.ideal i) T.mult → (s.projectionToBase i) z ∈ orderAtLeastLocus T.ideal T.mult := by
  have := hV.charZero
  intro i
  induction i with
  | zero =>
      intro _ z hz
      rw [markedSequenceOfBlowups_ideal_zero s, MarkedSequenceOfBlowups.projectionToBase_zero s, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hz
      rwa [MarkedSequenceOfBlowups.projectionToBase_zero s]
  | succ i ih =>
      intro hi z hz
      rw [projectionToBase_succ_apply]
      refine ih (le_of_succ_le hi) _ ?_
      exact blowupMorphism_mem_orderAtLeastLocus s hV.one_le_mult
        (fun j hj => smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s j hj)
        (fun j hj => p25 effectiveCartierSupportContainsNoComponent hV s j hj)
        i (lt_of_succ_le hi) z hz

section
variable {Y} (h : Y ⟶ T.scheme)
theorem center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty
    (hempty : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) = ∅) (s : T.SequenceOfBlowups) :
    ∀ i < s.length, ∀ z, z ∈ (s.center i).support →
      ∀ y, h y ≠ (s.projectionToBase i) z := by
  intro i hi z hz y hy
  have himg := projectionToBase_mem_orderAtLeastLocus hV s i hi.le z $ s.center_order i hi hz
  rw [← hy] at himg
  have hmem : y ∈ (h ⁻¹' orderAtLeastLocus T.ideal T.mult) := himg
  rw [hempty] at hmem
  simp at hmem

end
end

theorem divisorFamily_isPullbackSequenceOfBlowups_of_orderAtLeastLocus_empty
    (hres : StrictTransformIsBlowupOfClosedSubscheme)
    L j (T : MarkedIdealWithBoundary)
    (hV : T.IsAdmissible) (_hj : j < T.boundary.length)
    (Y : Sch) q (h : Y ⟶ T.scheme)
    [Smooth h]
    (_hq : h ≫ T.structMap = q) E'
    (_hV' : (T.pbB q h E').IsAdmissible)
    (_hne : (orderAtLeastLocus T.ideal T.mult).Nonempty)
    (hempty : orderAtLeastLocus (T.pbB q h E').ideal T.mult = ∅)
    (B' : SequenceOfBlowups Y) (hB' : B'.length = 0) :
    IsPullbackBlowupSequence h B' ((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups := by
  have := hV.charZero
  have := hV.smooth
  have hsub : (h ⁻¹' orderAtLeastLocus T.ideal T.mult) ⊆ ∅ := by
    intro y hy
    have hy' : y ∈ orderAtLeastLocus (T.ideal.comap h) T.mult := by
      rwa [orderAtLeastLocus_comap T.base T.structMap h T.ideal T.mult]
    have hy2 : y ∈ orderAtLeastLocus (T.pbB q h E').ideal T.mult := hy'
    rwa [hempty] at hy2
  let s := (canonicalAlgorithmRules hres).divisorFamily L j T
  refine (SequenceOfBlowupsPullback.ofBlowupDataOfSeq
      (SequenceOfBlowupsPullback.ofCentersMissImage h (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups) ?_
        (BlowupSequenceData.ofSequenceOfBlowups B') hB')).isPullbackSequenceOfBlowups
  intro i hi z hz y
  rw [BlowupSequenceData.ofSequenceOfBlowups_projectionToBase]
  exact (center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty hV h (mp_ subset_empty_iff hsub) s) i hi z hz y

end DivisorReductionEmptyOrderLocus




theorem exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    (∀ x, orderAt T.ideal x ≤ (T.mult : ENat)) →
    ∀ j (hj : j < T.boundary.length),
      ∃ B, B * ccI hj ^ T.mult = T.ideal := by
  intro T hV _ j hj
  obtain ⟨J, hJ⟩ := exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  exact ⟨J, by rw [mul_comm]; exact hJ⟩

theorem orderAtComapOffExceptionalLocus : OrderAtComapOffExceptionalLocus := by
  delta OrderAtComapOffExceptionalLocus
  exact fun T hT X' pi_ Z hpi_ x' hx' A =>
    orderAt_comap_eq_of_notMem_exceptionalIdeal T hT Z X' pi_ hpi_ x' hx' A

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
include hfacts
theorem smoothPullbackCompatibility_of_divisorReductionTermination :
    DivisorReduction.SmoothPullbackCompatibility := by
  refine ⟨comap_ne_top_of_surjective, ?_, DivisorReduction.isPullback_subschemeMapOfComap, DivisorReduction.smooth_of_isPullback, DivisorReduction.lowerIdealAfterBlowup_pullbackAlong_of_smooth exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal, ?_, DivisorReduction.containedComponentsIdeal_pullbackAlong_of_smooth hfacts⟩
  intro T hV Y q h inst hq m
  exact orderAtLeastLocus_comap_of_smooth T hV Y q h hq m
  exact lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
    isBlowupAlongIdealSheaf_id_containedComponentsIdeal

theorem fieldBaseChangeCompatibility_of_divisorReductionTermination :
    FieldBaseChangeCompatibility := by
  refine ⟨?_, flat_fieldBaseChangeProjection, surjective_fieldBaseChangeProjection, containedComponentsIdeal_withBoundary_baseChange hfacts validOfSameNontrivialBoundary⟩
  intro T hV K inst f E' m
  exact orderAtLeastLocus_withBoundary_baseChange_eq_preimage T hV K f E' m
end

theorem divisorRestrictionFieldBaseChange : DivisorRestrictionFieldBaseChange := by
  refine ⟨comap_comap, comap_fieldBaseChangeProjection_ne_top, ?_, ?_, ?_, ?_, ?_⟩
  intro T j hj K inst1 inst2 f E' hjE hD I0 E0 I0' E0' hI hE
  obtain ⟨E'', e, hs, hsu, h1, h2, h3, h4, h5, h6⟩ :=
    DivisorReduction.exists_smooth_surjective_to_restrictToBoundaryDivisor_baseChange T j hj K f E' hjE hD I0 E0 I0' E0' hI hE
  exact ⟨E'', e, hs, hsu, sy_ h1, h2, h3, h4, h5, h6⟩
  intro T K inst1 inst2 f E'
  exact lowerIdealWithoutBlowup_withBoundary_baseChange T K f E'
  intro T j hj K inst1 inst2 f E' hBE htake hjE
  exact lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary T j hj K f E' hBE htake hjE
  intro T hV hO j hj K inst1 inst2 f E' hBE hjE htake hV' hpre
  exact lowerIdealAfterBlowup_fieldBaseChange exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV
    hO j hj K f E' hBE.symm hjE htake hV' hpre
  intro T hV hO j hj K inst1 inst2 f E' hBE hjE htake hV' hpre
  exact lowerBoundaryAfterBlowup_fieldBaseChange exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV hO
    j hj K f E' hBE.symm hjE htake hV' hpre

theorem emptyPulledBackCenterCompatibility : EmptyPulledBackCenterCompatibility := by
  constructor
  intro T hV hO j hj Y h htop
  exact comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
    isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV hO j hj Y h htop
  intro T hV j hj Y h htop
  exact comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
    isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV j hj Y h htop

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme)
theorem pushedBlowupSequenceProperties_canonicalAlgorithmRules :
    PushedBlowupSequenceProperties hres blowupPreservesNoetherian := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  intro T hV j hj
  exact isOpen_preimage_support_containedComponentsIdeal T j hj
    (preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj)
  intro T inst j hj s hpr hmk
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (bgetT hj).si
    s.toBsd hres blowupPreservesNoetherian hpr
  rwa [ker_subschemeι] at h0
  intro T inst j hj hb s hpr hmk
  exact ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism hres blowupPreservesNoetherian T j hj hb s hpr
    hmk
  intro T hV j hj S
  exact isSmoothDivisor_boundary_comap_isoObjZero T hV j hj S
  intro T inst j hj s hpr hmk t ht
  exact boundaryLocus_subset_preimage_otherBoundaryLocus hres blowupPreservesNoetherian T j hj s hpr
    hmk t ht
  intro T inst j hj hb s hpr hmk t ht
  exact boundaryLocus_subset_preimage_otherBoundaryLocus_succ hres blowupPreservesNoetherian T j hj hb s
    hpr hmk t ht
  intro T hV
  exact hV.one_le_mult
  intro T hV hOB hbal j hj hpre hlow inst s hpr hmk t ht
  exact isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top hres blowupPreservesNoetherian T hV
    hOB hbal j hj hpre hlow s hpr hmk t ht
  intro T hV hOB hbal j hj hne hb hlow inst s hpr hmk t ht
  exact isSmoothDivisor_ker_embeddingIntoAmbient hres blowupPreservesNoetherian
    orderAtComapOffExceptionalLocus T hV hOB j hj hb hlow s hpr hmk
    (fun t _ => embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeio hres
      blowupPreservesNoetherian T j hj (p21 hj)
      (p37 hj) s hpr t) t ht
  intro T inst j hj s hpr hmk t
  exact projectionToSpec_eq_comp_ambientMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk t
  intro T inst j hj hb s hpr hmk t
  exact projectionToSpec_eq_comp_prependedAmbientSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk t
  intro X Y f inst I
  intro x hx
  exact support_antitone (le_ker_comp (siI I) f) hx
  intro T hV j hj
  exact support_containedComponentsIdeal_subset_support_boundary T j hj

theorem divisorReductionHypotheses_canonicalAlgorithmRules :
    DivisorReductionHypotheses hres := by
  have hfacts := divisorReductionProperties_of_blowupPreservesNoetherian hres blowupPreservesNoetherian
  refine
    { trivial_of_coSupport_empty := ?_
      baseChange := smoothPullbackCompatibility_of_divisorReductionTermination hres hfacts
      smoothImpliesFlat := ⟨fun X Y f hf => by have := hf; infer_instance⟩
      degenerateTransversal := emptyPulledBackCenterCompatibility
      fieldBaseChangeCompatibility := fieldBaseChangeCompatibility_of_divisorReductionTermination hres hfacts
      boundaryReindexingInvariance := DivisorReduction.boundaryReindexingInvariance
      fieldLower := divisorRestrictionFieldBaseChange
      divisorReduction := hfacts
      pushedBlowupSequenceProperties := pushedBlowupSequenceProperties_canonicalAlgorithmRules hres }
  intro L j T hV hj Y q h inst hq E' hV' hne hempty B' hB'
  exact DivisorReductionEmptyOrderLocus.divisorFamily_isPullbackSequenceOfBlowups_of_orderAtLeastLocus_empty hres L j T hV hj Y q h hq E' hV'
    hne hempty B' hB'
end


theorem isCorrect_canonicalAlgorithmRules_of_hypotheses
    (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hdiv : DivisorReductionHypotheses hres)
    (hG : PrincipalizationGeometryHypotheses) :
    (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension where
  divisorSpec := isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules hres hdiv
  divisorShift := fun n L O hL =>
    isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient hres hdiv.divisorReduction hdiv.baseChange hdiv.boundaryReindexingInvariance
      n L O hL $ hdiv.divisorReductionSeqEqAmbient n L O hL
  maxOrderSpec := fun n A L hspec =>
    MaxOrderReduction.isMaxOrderReduction_canonicalAlgorithmRules hG hres n A L hspec
  orderSpec := OrderReductionProperties.isOrderReduction_orderFamily_of_strictTransformIsBlowup hres




theorem exists_iso_subscheme_of_ker_eq {Z X : Sch} (i : Z ⟶ X)
    [IsClosedImmersion i] (I : ISD X) (hI : ker i = I) :
    ∃ e : Z ≅ I.subscheme, e.hom ≫ I.si = i := by
  subst hI
  exact ⟨asIso i.toImage, i.toImage_imageι⟩

section
variable (k : Type) [Field k]
section
variable (M p : ℕ) (U : (affineSpaceIndexedBy k (UFin M)).Opens)
abbrev opensPreimageProjLeft :
    (affineSpaceIndexedBy k $ UFS M p).Opens :=
  (Opens.map (projLeft k M p).base).obj U

theorem exists_zeroSectionOverOpen :
    ∃ z, z ≫ (opensPreimageProjLeft k M p U).ι = U.ι ≫ affineSpaceInl k M p ∧
      z ≫ (projLeft k M p ∣_ U) = 𝟙 _ := by
  let _a3 := affineSpaceInl k M p
  let _a0 := opI U ≫ _a3
  let _a1 := opensPreimageProjLeft k M p U
  let _a2 : range (opI U ≫ _a3) ⊆ range (opensPreimageProjLeft k M p U).i := by
    let _a0 := opI U ≫ _a3
    let _a1 := projLeft k M p
    have hcomp : _a0 ≫ _a1 = opI U := by
      rw [assoc, affineSpaceInl_comp_projLeft, comp_id]
    rw [range_subset_iff]
    intro x
    have hx : _a1 (_a0 x) = opI U x :=
      congrArg (fun f : (U : Sch) ⟶ affineSpaceIndexedBy k (UFin M) => f x) hcomp
    refine ⟨⟨_a0 x, ?_⟩, rfl⟩
    show _a1 (_a0 x) ∈ U
    rw [hx]
    exact x.2
  have hfac :=
    m115 _a1.i _a0
      _a2
  refine ⟨m43 _a1.i _a0
      _a2, hfac, ?_⟩
  rw [← cancel_mono $ opI U, assoc, id_comp, morphismRestrict_ι,
    ← assoc, hfac, assoc, affineSpaceInl_comp_projLeft, comp_id]

def zeroSectionOverOpen :=
  (exists_zeroSectionOverOpen k M p U).choose

@[simp]
theorem zeroSectionOverOpen_comp_io :
    zeroSectionOverOpen k M p U ≫ (opensPreimageProjLeft k M p U).ι = U.ι ≫ affineSpaceInl k M p :=
  (exists_zeroSectionOverOpen k M p U).choose_spec.1

@[simp]
theorem zeroSectionOverOpen_comp_io_assoc {Z : Sch}
    (g : affineSpaceIndexedBy k (UFS M p) ⟶ Z) :
    zeroSectionOverOpen k M p U ≫ (opensPreimageProjLeft k M p U).ι ≫ g = U.ι ≫ affineSpaceInl k M p ≫ g := by
  rw [← assoc, zeroSectionOverOpen_comp_io, assoc]

@[simp]
theorem zeroSectionOverOpen_comp_restrict :
    zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U) = 𝟙 _ :=
  (exists_zeroSectionOverOpen k M p U).choose_spec.2

@[simp]
theorem zeroSectionOverOpen_comp_restrict_assoc {Z : Sch}
    (g : (U : Sch) ⟶ Z) :
    zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U) ≫ g = g := by
  rw [← assoc, zeroSectionOverOpen_comp_restrict, id_comp]
end

theorem pullbackCoord_affineSpaceIsoOfEquiv_hom {n m : Type}
    (e : n ≃ m) (i : m) :
    pullbackCoord (affineSpaceIsoOfEquiv e $ Sp k).hom i =
      AffineSpace.coord (Sp k) (e.symm i) := by
  simp [pullbackCoord, affineSpaceIsoOfEquiv]
end

theorem exists_isPullback_of_ker_eq_comap {Z X Z' X' : Sch} (i : Z ⟶ X)
    [IsClosedImmersion i] (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : X' ⟶ X)
    (h : ker i' = comap (ker i) g) :
    ∃ c : Z' ⟶ Z, IsPullback c i' i g := by
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_ker_eq i (m149 i) rfl
  let _a0 := cmI (m149 i) g
  obtain ⟨e', he'⟩ := exists_iso_subscheme_of_ker_eq i' _a0 h
  have h1 : IsPullback e'.hom i' _a0.si $ 𝟙 X' :=
    of_horiz_isIso ⟨by rw [he', comp_id]⟩
  have h3 : IsPullback e.inv (m149 i).si i $ 𝟙 X :=
    of_horiz_isIso ⟨by rw [comp_id, inv_comp_eq]; exact sy_ he⟩
  refine ⟨(isoH e' ≫ comapSubschemeHom (m149 i) g) ≫ isoI e, ?_⟩
  have h4 := (h1.paste_horiz $ isPullback_comapSubschemeHom (m149 i) g).paste_horiz h3
  rwa [id_comp, comp_id] at h4

def uliftFinSumEquiv (c p : ℕ) : UFS c p ≃ UFin (c + p) :=
  ulift.trans (finSumFinEquiv.trans ulift.symm)


theorem pullbackCoord_comp_eq_appTop {k : Type} [Field k] {T Y : Sch}
    {n : Type} (a : T ⟶ Y) (g : Y ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord (a ≫ g) i = appTop a (pullbackCoord g i) := rfl

theorem affineSpaceOrigin_comp_affineSpaceInl_affineSpaceIsoOfEquiv (k : Type) [Field k] (c p : ℕ) :
    affineSpaceOrigin k c ≫ affineSpaceInl k c p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv c p) (Sp k)).hom =
      affineSpaceOrigin k (c + p) := by
  refine eq_affineSpaceOrigin_of_pullbackCoord_eq_zero k (c + p) _ ?_ ?_
  rw [assoc, assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
  simp
  intro i
  let _a0 := uliftFinSumEquiv c p
  obtain ⟨j, rfl⟩ : ∃ j, i = uliftFinSumEquiv c p j :=
    ⟨_a0.symm i, (_a0.apply_symm_apply i).symm⟩
  have h1 : pullbackCoord (affineSpaceInl k c p ≫
      (affineSpaceIsoOfEquiv _a0 $ Sp k).hom)
        (uliftFinSumEquiv c p j) = pullbackCoord (affineSpaceInl k c p) j := by
    rw [pullbackCoord_comp_eq_appTop, pullbackCoord_affineSpaceIsoOfEquiv_hom,
      symm_apply_apply, pullbackCoord_def]
  rw [pullbackCoord_comp_eq_appTop, h1]
  obtain ⟨a | b⟩ := j
  rw [pullbackCoord_affineSpaceInl_inl]
  exact affineSpaceOrigin_appTop_coord k c $ up a
  rw [pullbackCoord_affineSpaceInl_inr]
  simp

namespace HasSmoothCoordCodim

theorem ker_eq_comap_ker_of_isPullback_closedImmersion {Z X X' W : Sch}
    (i : Z ⟶ X) [IsClosedImmersion i] (g : X' ⟶ X) (j : W ⟶ X') (a : W ⟶ Z)
    (H : IsPullback a j i g) :
    ker j = comap (ker i) g := by
  rw [← H.flip.isoPullback_hom_fst, ker_comp_of_isIso,
    ker_fst_of_isClosedImmersion]

section
variable (hsm : AffineSpaceIsSmooth) (k : Type) [Field k] {M c : ℕ} {A : Sch} (rh_ : A ⟶ affineSpaceIndexedBy k (UFin M)) [IsClosedImmersion rh_] (p : ℕ) (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (UFin M)) rh_ c)
include hsm h
theorem comp_affineSpaceInl :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (UFS M p))
      (rh_ ≫ affineSpaceInl k M p) (c + p) := by
  let _a0 := affineSpaceIsoOfEquiv (uliftFinSumEquiv c p) $ Sp k
  let _a1 := rh_ ≫ affineSpaceInl k M p
  let _a3 := projLeft k M p
  let _a4 := affineSpaceOrigin k $ c + p
  intro x
  obtain ⟨U, hxU, q, hqsm, hqcomp, hker⟩ := h x
  let _a2 := (ker rh_).comap U.i
  have hs : IsPullback (zeroSectionOverOpen k M p U ≫ projLeft k M p ∣_ U) U.i U.i
      (affineSpaceInl k M p ≫ _a3) := by
    rw [zeroSectionOverOpen_comp_restrict, affineSpaceInl_comp_projLeft]
    exact of_horiz_isIso ⟨by rw [id_comp, comp_id]⟩
  obtain ⟨a0_, hB⟩ := exists_isPullback_of_ker_eq_comap rh_
    _a2.si U.i $ q2 ..
  let _a5 := affineSpaceOrigin k c
  have hB2 : ker _a2.si =
      (ker _a5).comap q := by
    rwa [q2, ker_affineSpaceOrigin]
  obtain ⟨c1_, hC⟩ := exists_isPullback_of_ker_eq_comap _a5
    _a2.si q hB2
  have _i23 : IsPullback (zeroSectionOverOpen k M p U) q (prodMapOnPreimage k M p c U q) $ affineSpaceInl k c p := by
    have hcomm : zeroSectionOverOpen k M p U ≫ prodMapOnPreimage k M p c U q = q ≫ affineSpaceInl k c p := by
      refine (isPullback_projLeft_projRight k c p).hom_ext ?_ ?_
      rw [assoc, ← morphismRestrict_projLeft_comp k M p c U q hqcomp]
      simp
      rw [assoc, prodMapOnPreimage_comp_projRight, zeroSectionOverOpen_comp_io_assoc,
        affineSpaceInl_comp_projRight, assoc, affineSpaceInl_comp_projRight,
        ← assoc, ← assoc, hqcomp]
    refine of_right ?_ hcomm (isPullback_prodMapOnPreimage k M p c U q hqcomp).flip
    rw [zeroSectionOverOpen_comp_restrict, affineSpaceInl_comp_projLeft]
    exact of_horiz_isIso ⟨by simp⟩
  have hRsq : IsPullback (𝟙 (opensPreimageProjLeft k M p U).toScheme) (prodMapOnPreimage k M p c U q)
      (prodMapOnPreimage k M p c U q ≫
        _a0.hom)
      _a0.hom :=
    of_horiz_isIso ⟨by rw [id_comp]⟩
  have hsgR : (_a5 ≫ affineSpaceInl k c p) ≫
      _a0.hom =
      _a4 := by
    rw [assoc, affineSpaceOrigin_comp_affineSpaceInl_affineSpaceIsoOfEquiv]
  have hW3 := (hC.flip.paste_horiz _i23).paste_horiz hRsq
  rw [comp_id, hsgR] at hW3
  refine ⟨opensPreimageProjLeft k M p U, ?_, prodMapOnPreimage k M p c U q ≫
      _a0.hom, ?_, ?_, ?_⟩
  show _a3 (_a1 x) ∈ U
  have hx1 : _a3 (_a1 x) = rh_ x :=
    congrArg (fun f : A ⟶ affineSpaceIndexedBy k (UFin M) => f x)
      (show _a1 ≫ _a3 = rh_ by
        rw [assoc, affineSpaceInl_comp_projLeft, comp_id])
  rwa [hx1]
  have :=
    smooth_prodMapOnPreimage hsm k M p c U q hqcomp
  infer_instance
  rw [assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
  show (_a1.ker).comap (opensPreimageProjLeft k M p U).i =
    (coordSubspaceIdeal k (c + p) Finset.univ).comap (prodMapOnPreimage k M p c U q ≫
      _a0.hom)
  rw [← ker_eq_comap_ker_of_isPullback_closedImmersion _a1
      (opensPreimageProjLeft k M p U).i _ _ (hB.flip.paste_horiz $ of_right hs (zeroSectionOverOpen_comp_io k M p U) $ isPullback_morphismRestrict _a3 U).flip,
    ker_eq_comap_ker_of_isPullback_closedImmersion _a4
      (prodMapOnPreimage k M p c U q ≫
        _a0.hom) _ _ hW3.flip,
    ker_affineSpaceOrigin]

theorem comp_affineSpaceInl_affineSpaceIsoOfEquiv :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFin $ M + p)
      (rh_ ≫ affineSpaceInl k M p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv M p) $ Sp k).hom) $ c + p := by
  let _a0 := uliftFinSumEquiv M p
  have h2 := (comp_affineSpaceInl hsm k rh_ p h).comp_iso_hom
    (affineSpaceIsoOfEquiv _a0 $ Sp k)
    (affineSpaceIndexedByToSpec k $ UFin $ M + p)
    (affineSpaceIsoOfEquiv_hom_comp_toSpec k _a0)
  rwa [assoc] at h2
end

end HasSmoothCoordCodim





section
variable (k : Type) [Field k] (M : ℕ)
abbrev affineSpaceTimesLine : Sch :=
  affineSpaceIndexedBy k $ UFS M 1

theorem appTop_comp_projLeft_coord {T : Sch}
    (t : T ⟶ affineSpaceIndexedBy k (UFS M 1)) (j : Fin M) :
    (ConcreteCategory.hom $ appTop $ t ≫ projLeft k M 1)
        (AffineSpace.coord (Sp k) (⟨j⟩ : UFin M)) =
      (ConcreteCategory.hom $ appTop t)
        (AffineSpace.coord (Sp k)
          (⟨Sum.inl j⟩ : UFS M 1)) := by
  rw [comp_appTop, comp_apply, projLeft_appTop_coord]

section
variable (G : ↑((affineSpaceIndexedBy k (UFin M)).presheaf.obj (op ⊤)))
def pullbackAlongProjection :
    ↑((affineSpaceTimesLine k M).presheaf.obj $ op ⊤) :=
  (ConcreteCategory.hom $ appTop $ projLeft k M 1) G

def pullbackBasicOpen :
    (affineSpaceTimesLine k M).Opens :=
  (affineSpaceTimesLine k M).basicOpen $ pullbackAlongProjection k M G

theorem mem_pullbackBasicOpen_iff
    y :
    y ∈ pullbackBasicOpen k M G ↔
      (projLeft k M 1).base y ∈ (affineSpaceIndexedBy k $ UFin M).basicOpen G :=
  Iff.symm $ iff_of_eq $ congrArg (fun U : Opn (affineSpaceTimesLine k M) => y ∈ U)
    (preimage_basicOpen (projLeft k M 1) G)

theorem pullbackAlongProjection_eq :
    pullbackAlongProjection k M G = (ConcreteCategory.hom $ appTop $ projLeft k M 1) G :=
  rfl
end

def lastCoordinate :
    ↑((affineSpaceTimesLine k M).presheaf.obj $ op ⊤) :=
  AffineSpace.coord (Sp k) (⟨Sum.inr 0⟩ : UFS M 1)

section
variable (G) (s : ↑((↑(pullbackBasicOpen k M G) : Sch).presheaf.obj (op ⊤)))
theorem exists_replaceLastCoord :
    ∃ f : (↑(pullbackBasicOpen k M G) : Sch) ⟶ affineSpaceTimesLine k M,
      f ≫ affineSpaceIndexedByToSpec k (UFS M 1) =
          (pullbackBasicOpen k M G).i ≫ affineSpaceIndexedByToSpec k (UFS M 1) ∧
      (∀ a : Fin M,
          pullbackCoord f ⟨Sum.inl a⟩ = pullbackCoord (pullbackBasicOpen k M G).i ⟨Sum.inl a⟩) ∧
      (ConcreteCategory.hom $ appTop f) (lastCoordinate k M) = s ∧
      f ≫ projLeft k M 1 = (pullbackBasicOpen k M G).i ≫ projLeft k M 1 := by
  let _a0 := UFS M 1
  let _a1 := pullbackBasicOpen k M G
  let _a2 := opI _a1 ≫ affineSpaceIndexedByToSpec k _a0
  obtain ⟨f, hover, hcoord⟩ :
      ∃ f : (↑_a1) ⟶ affineSpaceTimesLine k M,
        f ≫ affineSpaceIndexedByToSpec k _a0 =
            _a2 ∧
          ∀ i,
            (m23 $ appTop f)
                (m9 (Sp k) i) =
              elim
                (fun a =>
                  pullbackCoord _a1.i (⟨m44 a⟩ : _a0))
                (fun _ => s) i.down := by
    refine ⟨m52
        _a2
        (fun i : _a0 =>
          elim
            (fun a =>
              pullbackCoord _a1.i (⟨m44 a⟩ : _a0))
            (fun _ => s) i.down), ?_, ?_⟩
    apply m179
    simp_all
  refine ⟨f, hover, ?_, hcoord (⟨m50 0⟩ : _a0), ?_⟩
  intro a
  exact tr_ (pullbackCoord_def f (⟨m44 a⟩ : _a0))
    (hcoord (⟨m44 a⟩ : _a0))
  refine m46 ?_ ?_
  have h1 : (f ≫ projLeft k M 1) ≫ affineSpaceIndexedByToSpec k (UFin M) =
      (opI _a1 ≫ projLeft k M 1) ≫
        affineSpaceIndexedByToSpec k (UFin M) := by
    rw [assoc, assoc, projLeft_comp_affineSpaceIndexedByToSpec, hover]
  exact h1
  intro i
  obtain ⟨j⟩ := i
  exact tr_ (appTop_comp_projLeft_coord k M f j)
    (tr_ (hcoord (⟨m44 j⟩ : _a0))
      (tr_ (pullbackCoord_def _a1.i
          (⟨m44 j⟩ : _a0))
        (appTop_comp_projLeft_coord k M _a1.i j).symm))

def replaceLastCoord :
    (↑(pullbackBasicOpen k M G) : Sch) ⟶ affineSpaceTimesLine k M :=
  (exists_replaceLastCoord k M G s).choose

theorem pullbackCoord_replaceLastCoord_inl (a : Fin M) :
    pullbackCoord (replaceLastCoord k M G s) ⟨Sum.inl a⟩ =
      pullbackCoord (pullbackBasicOpen k M G).ι ⟨Sum.inl a⟩ :=
  (exists_replaceLastCoord k M G s).choose_spec.2.1 a

theorem replaceLastCoord_comp_affineSpaceIndexedByToSpec :
    replaceLastCoord k M G s ≫ affineSpaceIndexedByToSpec k (UFS M 1) =
      (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (UFS M 1) :=
  (exists_replaceLastCoord k M G s).choose_spec.1

theorem replaceLastCoord_appTop_lastCoordinate :
    (ConcreteCategory.hom $ appTop $ replaceLastCoord k M G s) (lastCoordinate k M) = s :=
  (exists_replaceLastCoord k M G s).choose_spec.2.2.1
end

theorem lastCoordinate_eq_coord (j : Fin 1) :
    lastCoordinate k M =
      AffineSpace.coord (Sp k) (⟨Sum.inr j⟩ : UFS M 1) := by
  rw [m111 j 0]
  rfl

@[simp]
theorem lastCoordinate_eq :
    lastCoordinate k M =
      AffineSpace.coord (Sp k) (⟨Sum.inr 0⟩ : UFS M 1) :=
  rfl

theorem lastCoordinate_appTop_comp_affineSpaceInl {A : Sch}
    (f : A ⟶ affineSpaceIndexedBy k (UFin M)) :
    (ConcreteCategory.hom $ appTop $ f ≫ affineSpaceInl k M 1) (lastCoordinate k M) = 0 := by
  have h1 := pullbackCoord_affineSpaceInl_inr k M 1 0
  rw [pullbackCoord_def] at h1
  rw [comp_appTop, comp_apply, lastCoordinate_eq, h1, map_zero]
end

theorem isUnit_appTop_io_basicOpen {X : Sch}
    f :
    IsUnit $ (ConcreteCategory.hom $ appTop (X.basicOpen f).ι) f := by
  let _a1 := bOpn X f
  let _c0 := (_a1 : Sch)
  let _a0 := (m23 $ appTop (bOpn X f).i) f
  have h1 : _c0.basicOpen
        _a0 =
      opI _a1 ⁻¹ᵁ bOpn X f := sy_ $ preimage_basicOpen ..
  have h2 : opI _a1 ⁻¹ᵁ bOpn X f = ⊤ :=
    m55 $ eq_univ_of_forall fun x => x.2
  refine RingedSpace.isUnit_of_isUnit_germ
    (_c0.toLocallyRingedSpace.toRingedSpace) ⊤ _ ?_
  intro x hx
  refine mp_ (_c0.mem_basicOpen
    _a0 x hx) ?_
  rw [tr_ h1 h2]
  exact Opens.mem_top _

section
variable (k : Type) [Field k] (M : ℕ)
section
variable (G : ↑((affineSpaceIndexedBy k (UFin M)).presheaf.obj (op ⊤)))

def unitOnPullbackBasicOpen :
    (↑((↑(pullbackBasicOpen k M G) : Sch).presheaf.obj $ op ⊤))ˣ :=
  ((fun k [Field k] M G => isUnit_appTop_io_basicOpen $ pullbackAlongProjection k M G) k M G).unit

@[simp]
theorem unitOnPullbackBasicOpen_val :
    (unitOnPullbackBasicOpen k M G).val =
      (ConcreteCategory.hom $ appTop (pullbackBasicOpen k M G).ι) (pullbackAlongProjection k M G) :=
  IsUnit.unit_spec _

section
variable (s : ↑((↑(pullbackBasicOpen k M G) : Sch).presheaf.obj (op ⊤)))
@[simp]
theorem replaceLastCoord_comp_projLeft :
    replaceLastCoord k M G s ≫ projLeft k M 1 = (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 :=
  (exists_replaceLastCoord k M G s).choose_spec.2.2.2


theorem exists_comp_io_eq_replaceLastCoord :
    ∃ g : (↑(pullbackBasicOpen k M G) : Sch) ⟶ (↑(pullbackBasicOpen k M G) : Sch),
      g ≫ (pullbackBasicOpen k M G).i = replaceLastCoord k M G s := by
  let _c0 := pullbackBasicOpen k M G
  let _c1 := replaceLastCoord k M G s
  have hrange : range _c1.base ⊆
      range _c0.ib := by
    rintro _ ⟨x, rfl⟩
    let _a0 := projLeft k M 1
    have h1 : bsM _a0 (bsM _c1 x) =
        _a0.base (opIb _c0 x) :=
      congrArg (fun f : (↑_c0) ⟶
          affineSpaceIndexedBy k (UFin M) => bsM f x)
        (replaceLastCoord_comp_projLeft k M G s)
    have hx : opIb _c0 x ∈ pullbackBasicOpen k M G := by
      have h0 : opIb _c0 x ∈ range _c0.ib :=
        mem_range_self x
      rwa [q1] at h0
    have h2 := (mem_pullbackBasicOpen_iff k M G $ opIb _c0 x).1 hx
    rw [q1]
    refine (mem_pullbackBasicOpen_iff k M G $ bsM _c1 x).2 ?_
    rwa [h1]
  exact ⟨m43 _c0.i _c1 hrange,
    m115 _c0.i _c1 hrange⟩

def shiftLastCoord :
    (↑(pullbackBasicOpen k M G) : Sch) ⟶ (↑(pullbackBasicOpen k M G) : Sch) :=
  (exists_comp_io_eq_replaceLastCoord k M G s).choose

@[simp]
theorem shiftLastCoord_comp_io :
    shiftLastCoord k M G s ≫ (pullbackBasicOpen k M G).ι = replaceLastCoord k M G s :=
  (exists_comp_io_eq_replaceLastCoord k M G s).choose_spec

@[simp]
theorem shiftLastCoord_comp_io_assoc {Z : Sch}
    (g : affineSpaceTimesLine k M ⟶ Z) :
    shiftLastCoord k M G s ≫ (pullbackBasicOpen k M G).ι ≫ g = replaceLastCoord k M G s ≫ g := by
  rw [← assoc, shiftLastCoord_comp_io]

theorem replaceLastCoord_appTop_pullbackAlongProjection :
    (ConcreteCategory.hom $ appTop $ replaceLastCoord k M G s) (pullbackAlongProjection k M G) =
      (ConcreteCategory.hom $ appTop (pullbackBasicOpen k M G).ι) (pullbackAlongProjection k M G) := by
  rw [pullbackAlongProjection_eq, ← comp_apply, ← comp_appTop,
    ← comp_apply, ← comp_appTop, replaceLastCoord_comp_projLeft]

theorem shiftLastCoord_appTop_unitOnPullbackBasicOpen_val :
    (ConcreteCategory.hom $ appTop $ shiftLastCoord k M G s) ((unitOnPullbackBasicOpen k M G).val) =
      (unitOnPullbackBasicOpen k M G).val := by
  rw [unitOnPullbackBasicOpen_val, ← comp_apply, ← comp_appTop, shiftLastCoord_comp_io,
    replaceLastCoord_appTop_pullbackAlongProjection]

theorem shiftLastCoord_appTop_unitOnPullbackBasicOpen_inv_val :
    (ConcreteCategory.hom $ appTop $ shiftLastCoord k M G s) (((unitOnPullbackBasicOpen k M G)⁻¹).val) =
      ((unitOnPullbackBasicOpen k M G)⁻¹).val := by
  refine sy_ $ Units.inv_eq_of_mul_eq_one_left ?_
  rw [← shiftLastCoord_appTop_unitOnPullbackBasicOpen_val k M G s, ← map_mul, Units.inv_mul, map_one]
end

theorem shiftLastCoord_comp_shiftLastCoord
    s t
    (ht : (ConcreteCategory.hom $ appTop $ shiftLastCoord k M G s) t =
      (ConcreteCategory.hom $ appTop (pullbackBasicOpen k M G).i) (lastCoordinate k M)) :
    shiftLastCoord k M G s ≫ shiftLastCoord k M G t = 𝟙 _ := by
  let _a3 := replaceLastCoord k M G t
  let _a0 := UFS M 1
  let _a1 := pullbackBasicOpen k M G
  rw [← cancel_mono _a1.i, assoc, shiftLastCoord_comp_io, id_comp]
  refine m46 ?_ ?_
  have h1 : (shiftLastCoord k M G s ≫ _a3) ≫
      affineSpaceIndexedByToSpec k _a0 =
      opI _a1 ≫ affineSpaceIndexedByToSpec k _a0 := by
    rw [assoc, replaceLastCoord_comp_affineSpaceIndexedByToSpec, ← assoc, shiftLastCoord_comp_io,
      replaceLastCoord_comp_affineSpaceIndexedByToSpec]
  exact h1
  intro i
  obtain ⟨j⟩ := i
  cases j with
  | inl a =>
    let _a2 := pullbackCoord_def _a1.i (⟨m44 a⟩ : _a0)
    rw [comp_appTop, comp_apply,
      ← pullbackCoord_def _a3
        (⟨m44 a⟩ : _a0),
      pullbackCoord_replaceLastCoord_inl,
      _a2,
      ← comp_apply, ← comp_appTop, shiftLastCoord_comp_io,
      ← pullbackCoord_def (replaceLastCoord k M G s)
        (⟨m44 a⟩ : _a0),
      pullbackCoord_replaceLastCoord_inl,
      _a2]
  | inr b =>
    rw [← lastCoordinate_eq_coord k M b, comp_appTop, comp_apply,
      replaceLastCoord_appTop_lastCoordinate, ht]

theorem isIso_shiftLastCoord_lastCoordinate_add_inv :
    IsIso $ shiftLastCoord k M G
      ((ConcreteCategory.hom $ appTop (pullbackBasicOpen k M G).ι) (lastCoordinate k M) +
        ((unitOnPullbackBasicOpen k M G)⁻¹).val) := by
  refine ⟨⟨shiftLastCoord k M G
      ((m23 $ appTop (pullbackBasicOpen k M G).i) (lastCoordinate k M) -
        ((unitOnPullbackBasicOpen k M G)⁻¹).val), ?_, ?_⟩⟩
  apply shiftLastCoord_comp_shiftLastCoord
  rw [map_sub, shiftLastCoord_appTop_unitOnPullbackBasicOpen_inv_val, ← comp_apply,
    ← comp_appTop, shiftLastCoord_comp_io, replaceLastCoord_appTop_lastCoordinate]
  ring
  apply shiftLastCoord_comp_shiftLastCoord
  rw [map_add, shiftLastCoord_appTop_unitOnPullbackBasicOpen_inv_val, ← comp_apply,
    ← comp_appTop, shiftLastCoord_comp_io, replaceLastCoord_appTop_lastCoordinate]
  ring
end

theorem exists_isClosedImmersion_pullbackBasicOpen {A : Sch}
    (rh_ : A ⟶ affineSpaceIndexedBy k (UFin M)) [IsClosedImmersion rh_]
    (G : ↑((affineSpaceIndexedBy k $ UFin M).presheaf.obj $ op ⊤))
    (V : Opn A)
    (hV : V = (Opens.map (rh_ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M G)) :
    ∃ e : (↑V : Sch) ⟶ (↑(pullbackBasicOpen k M G) : Sch),
      IsClosedImmersion e ∧
      e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 = V.ι ≫ rh_ ∧
      (ConcreteCategory.hom $ appTop $ e ≫ (pullbackBasicOpen k M G).ι)
          (lastCoordinate k M * pullbackAlongProjection k M G) = 1 := by
  let _a0 := rh_ ≫ affineSpaceInl k M 1
  let _a1 := (m23 $ appTop (pullbackBasicOpen k M G).i) $ lastCoordinate k M
  subst hV
  have hci : IsClosedImmersion $ _a0 ∣_ pullbackBasicOpen k M G := by
    have hco : IsClosedImmersion _a0 := inferInstance
    infer_instance
  have hiso := isIso_shiftLastCoord_lastCoordinate_add_inv k M G
  refine ⟨(_a0 ∣_ pullbackBasicOpen k M G) ≫
      shiftLastCoord k M G (_a1 + ((unitOnPullbackBasicOpen k M G)⁻¹).val), mpr_ (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ _) hci, ?_, ?_⟩
  rw [assoc, shiftLastCoord_comp_io_assoc, replaceLastCoord_comp_projLeft, ← assoc,
    morphismRestrict_ι, assoc, assoc, affineSpaceInl_comp_projLeft,
    comp_id]
  have h0 : (m23 $ appTop
      (_a0 ∣_ pullbackBasicOpen k M G))
      _a1 = 0 := by
    rw [← comp_apply, ← comp_appTop, morphismRestrict_ι,
      ← assoc]
    exact lastCoordinate_appTop_comp_affineSpaceInl k M _
  rw [assoc, shiftLastCoord_comp_io, comp_appTop, comp_apply, map_mul,
    replaceLastCoord_appTop_lastCoordinate, replaceLastCoord_appTop_pullbackAlongProjection, ← unitOnPullbackBasicOpen_val, map_mul,
    map_add, h0, zero_add, ← map_mul, inv_mul, map_one]
end

theorem appTop_surjective_of_isAffine {X Y : Sch} (f : X ⟶ Y)
    [IsAffine Y] [IsClosedImmersion f] :
    Function.Surjective $ ConcreteCategory.hom $ appTop f :=
  (isAffine_surjective_of_isAffine ..).2

section
variable (k : Type) [Field k] (M) {A : Sch} (rh_) [IsClosedImmersion rh_] (F : ↑(A.presheaf.obj (op ⊤)))
def globalSectionLift :
    ↑((affineSpaceIndexedBy k $ UFin M).presheaf.obj $ op ⊤) :=
  ((appTop_surjective_of_isAffine rh_ F)).choose

@[simp]
theorem appTop_globalSectionLift :
    (ConcreteCategory.hom $ appTop rh_) (globalSectionLift k M rh_ F) = F :=
  (appTop_surjective_of_isAffine rh_ F).choose_spec

theorem exists_isClosedImmersion_basicOpen_pullbackBasicOpen :
    ∃ e : (↑(A.basicOpen F) : Sch) ⟶
        (↑(pullbackBasicOpen k M $ globalSectionLift k M rh_ F) : Sch),
      IsClosedImmersion e ∧
      e ≫ (pullbackBasicOpen k M $ globalSectionLift k M rh_ F).ι ≫ projLeft k M 1 = (A.basicOpen F).i ≫ rh_ ∧
      (ConcreteCategory.hom
          (appTop $ e ≫ (pullbackBasicOpen k M $ globalSectionLift k M rh_ F).ι))
          (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M rh_ F)) = 1 := by
  let _a0 := globalSectionLift k M rh_ F
  refine exists_isClosedImmersion_pullbackBasicOpen k M rh_ _a0 (bOpn A F) ?_
  let _a1 := rh_ ≫ affineSpaceInl k M 1
  have hF : (m23 $ appTop _a1)
      (pullbackAlongProjection k M _a0) = F := by
    rw [pullbackAlongProjection_eq, ← comp_apply, ← comp_appTop, assoc,
      affineSpaceInl_comp_projLeft, comp_id, appTop_globalSectionLift]
  exact st_ (congrArg (fun r : (pObj A $ op ⊤) => bOpn A r) hF)
    (preimage_basicOpen _a1
      (pullbackAlongProjection k M _a0)).symm

def basicOpenToPullbackBasicOpen :
    (↑(A.basicOpen F) : Sch) ⟶ (↑(pullbackBasicOpen k M $ globalSectionLift k M rh_ F) : Sch) :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen k M rh_ F).choose

theorem isClosedImmersion_basicOpenToPullbackBasicOpen :
    IsClosedImmersion $ basicOpenToPullbackBasicOpen k M rh_ F :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen k M rh_ F).choose_spec.1
end

instance instIsClosedImmersionPadLocalEmb (k : Type) [Field k] (M : ℕ) {A : Sch}
    (rh_ : A ⟶ affineSpaceIndexedBy k (UFin M)) [IsClosedImmersion rh_]
    (F : ↑(A.presheaf.obj $ op ⊤)) :
    IsClosedImmersion $ basicOpenToPullbackBasicOpen k M rh_ F :=
  isClosedImmersion_basicOpenToPullbackBasicOpen k M rh_ F

section
variable (k : Type) [Field k] (M) {A : Sch} (rh_) [IsClosedImmersion rh_] (F : ↑(A.presheaf.obj (op ⊤)))
theorem basicOpenToPullbackBasicOpen_comp_projLeft :
    basicOpenToPullbackBasicOpen k M rh_ F ≫ (pullbackBasicOpen k M $ globalSectionLift k M rh_ F).ι ≫ projLeft k M 1 =
      (A.basicOpen F).i ≫ rh_ :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen k M rh_ F).choose_spec.2.1

def basicOpenEmbedding :
    (↑(A.basicOpen F) : Sch) ⟶ affineSpaceTimesLine k M :=
  basicOpenToPullbackBasicOpen k M rh_ F ≫ (pullbackBasicOpen k M $ globalSectionLift k M rh_ F).ι

theorem appTop_basicOpenEmbedding_lastCoordinate_mul :
    (ConcreteCategory.hom $ appTop $ basicOpenEmbedding k M rh_ F)
        (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M rh_ F)) = 1 :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen k M rh_ F).choose_spec.2.2
end

section
variable {R S : Type} [CommRing R] [CommRing S]
theorem isUnit_map_of_not_isUnit_map_mul_sub_one
    [IsLocalRing S] (ph_ : R →+* S) (a b : R) (h : ¬ IsUnit (ph_ (a * b - 1))) : IsUnit (ph_ b) := by
  rw [map_sub, map_mul, map_one] at h
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (ph_ a * ph_ b) with h1 | h1
  exact isUnit_of_mul_isUnit_right h1
  refine absurd ?_ h
  have h2 := h1.neg
  rwa [neg_sub] at h2

theorem false_of_isUnit_map_zero
    [Nontrivial S] (ph_ : R →+* S) (h : IsUnit $ ph_ (0 : R)) : False :=by simp_all
end

theorem isClosed_image_of_isInducing {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (g : Y → X) (hg : Topology.IsInducing g) (S : Set X) (C : Set Y)
    (hSimage : S = g '' C) (hC : IsClosed C) (W : Set X) (hW : IsClosed W) (h1 : S ⊆ W)
    (h2 : W ⊆ range g) :
    IsClosed S := by
  obtain ⟨D, hD, hpreimage⟩ := hg.isClosed_iff.1 hC
  have himg : g '' C = D ∩ range g := by
    rw [← hpreimage, image_preimage_eq_inter_range]
  have hEq : S = D ∩ W := by
    refine m15 (subset_inter ?_ h1) ?_
    rw [hSimage, himg]
    exact fun x hx => an1 hx
    intro x hx
    rw [hSimage, himg]
    exact ⟨hx.1, h2 hx.2⟩
  rw [hEq]
  exact hD.inter hW

theorem isClosedImmersion_basicOpenEmbedding (k : Type) [Field k] (M : ℕ) {A : Sch}
    (rh_ : A ⟶ affineSpaceIndexedBy k (UFin M)) [IsClosedImmersion rh_]
    (F : ↑(A.presheaf.obj (op ⊤))) :
    IsClosedImmersion (basicOpenEmbedding k M rh_ F) := by
  let _a0 := globalSectionLift k M rh_ F
  let _c0 := lastCoordinate k M * pullbackAlongProjection k M _a0 - 1
  let _c1 := _a0
  let _c2 := affineSpaceTimesLine k M
  let _c3 := basicOpenEmbedding k M rh_ F
  have hpre : IsPreimmersion _c3 := by
    show IsPreimmersion $ basicOpenToPullbackBasicOpen k M rh_ F ≫ opI (pullbackBasicOpen k M _c1)
    infer_instance
  let _m0 := basicOpenToPullbackBasicOpen k M rh_ F
  have heq : range _c3.base =
      opIb (pullbackBasicOpen k M _c1) '' range _m0.base := by
    ext z
    constructor
    rintro ⟨y, rfl⟩
    exact ⟨bsM _m0 y, ⟨y, rfl⟩, rfl⟩
    rintro ⟨w, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩
  let _s0 := ((bOpn _c2 _c0) : Set _c2)ᶜ
  have h1 : range _c3.base ⊆
      _s0 := by
    rintro z ⟨y, rfl⟩
    intro hz
    have hz' : y ∈ _c3 ⁻¹ᵁ (bOpn _c2
        _c0) := hz
    rw [preimage_basicOpen] at hz'
    let _m1 := ((bOpn A F) : Sch)
    have hy : y ∈ bOpn _m1
        ((m23 $ appTop _c3)
          _c0) := hz'
    rw [map_sub, map_one, appTop_basicOpenEmbedding_lastCoordinate_mul, sub_self] at hy
    exact false_of_isUnit_map_zero _
      (mp_ (_m1.mem_basicOpen _ y $ Opens.mem_top y) hy)
  have h2 : _s0 ⊆ range (pullbackBasicOpen k M _c1).ib := by
    intro x hx
    have hx' : x ∉ bOpn _c2
        _c0 := hx
    rw [_c2.mem_basicOpen _ x $ Opens.mem_top x] at hx'
    let _a1 := pullbackAlongProjection k M _c1
    have hmem : x ∈ bOpn _c2 _a1 := by
      rw [_c2.mem_basicOpen _ x $ Opens.mem_top x]
      exact isUnit_map_of_not_isUnit_map_mul_sub_one _ (lastCoordinate k M)
        _a1 hx'
    rwa [q1]
  apply of_isPreimmersion
  exact isClosed_image_of_isInducing _ ((pullbackBasicOpen k M _c1).ι.isOpenEmbedding.toIsEmbedding.toIsInducing) _ _ heq ((isClosedEmbedding _m0).isClosed_range) _ ((bOpn _c2 _c0).isOpen.isClosed_compl) h1 h2

instance instIsClosedImmersionLocalizationEmb (k : Type) [Field k] (M : ℕ) {A : Sch}
    (rh_ : A ⟶ affineSpaceIndexedBy k (UFin M)) [IsClosedImmersion rh_]
    (F : ↑(A.presheaf.obj $ op ⊤)) :
    IsClosedImmersion $ basicOpenEmbedding k M rh_ F :=
  isClosedImmersion_basicOpenEmbedding k M rh_ F

section
variable (k : Type) [Field k] (M : ℕ)
theorem basicOpenEmbedding_comp_affineSpaceIndexedByToSpec {A : Sch}
    rh_ [IsClosedImmersion rh_]
    F p
    (hp : rh_ ≫ affineSpaceIndexedByToSpec k (UFin M) = p) :
    basicOpenEmbedding k M rh_ F ≫ affineSpaceIndexedByToSpec k (UFS M 1) =
      (A.basicOpen F).i ≫ p := by
  let _c0 := pullbackBasicOpen k M $ globalSectionLift k M rh_ F
  let _a0 := basicOpenToPullbackBasicOpen k M rh_ F
  have h2 : _a0 ≫ opI _c0 ≫ projLeft k M 1 ≫
        affineSpaceIndexedByToSpec k (UFin M) =
      opI (bOpn A F) ≫ rh_ ≫ affineSpaceIndexedByToSpec k (UFin M) := by
    rw [← assoc (opI _c0) $ projLeft k M 1,
      ← assoc _a0, basicOpenToPullbackBasicOpen_comp_projLeft k M rh_ F, assoc]
  show (_a0 ≫ opI _c0) ≫
      affineSpaceIndexedByToSpec k (UFS M 1) = opI (bOpn A F) ≫ p
  rw [assoc, ← projLeft_comp_affineSpaceIndexedByToSpec k M 1, h2, hp]

section
variable (G : ↑((affineSpaceIndexedBy k (UFin M)).presheaf.obj (op ⊤)))
noncomputable def lastCoordinateAddInvUnit :
    ↑((↑(pullbackBasicOpen k M G) : Sch).presheaf.obj $ op ⊤) :=
  (ConcreteCategory.hom $ appTop (pullbackBasicOpen k M G).ι) (lastCoordinate k M) +
    ((unitOnPullbackBasicOpen k M G)⁻¹).val

theorem shiftLastCoordSection_eq :
    lastCoordinateAddInvUnit k M G =
      (ConcreteCategory.hom $ appTop (pullbackBasicOpen k M G).ι) (lastCoordinate k M) +
        ((unitOnPullbackBasicOpen k M G)⁻¹).val :=
  rfl

theorem isIso_shiftLastCoord_shiftLastCoordSection :
    IsIso $ shiftLastCoord k M G $ lastCoordinateAddInvUnit k M G :=
  isIso_shiftLastCoord_lastCoordinate_add_inv k M G
end
end

theorem hasSmoothCoordCodim_comp_opens_io {k : Type} [Field k] {X Y : Sch}
    (s : Y ⟶ Sp k) (O : Opn Y) (g : X ⟶ (↑O : Sch)) {c : ℕ}
    (hcg : IsClosedImmersion g) (hcgo : IsClosedImmersion $ g ≫ O.ι)
    (h : HasSmoothCoordCodim (O.ι ≫ s) g c) :
    HasSmoothCoordCodim s (g ≫ O.ι) c := by
  rw [hasSmoothCoordCodim_iff]
  intro x
  obtain ⟨U, hxU, q, hq, hqs, hideal⟩ := (hasSmoothCoordCodim_iff (O.ι ≫ s) g c).1 h x
  obtain ⟨W, ps_, hpsiso, hps_, hmem⟩ :
      ∃ (W : Opn Y) (ps_ : (↑W) ⟶ (↑U)),
        IsIso ps_ ∧ ps_ ≫ (U.ι ≫ O.ι) = W.ι ∧ bsM (g ≫ O.ι) x ∈ W := by
    let _a0 := opensRange $ U.ι ≫ O.ι
    have hrange : range (U.ι ≫ O.ι).base =
        range (opIb _a0) := by
      rw [q1]
      rfl
    refine ⟨_a0,
      (isoOfRangeEq (U.ι ≫ O.ι)
        _a0.ι hrange).inv, inferInstance,
      IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hrange, ?_⟩
    have hxr : bsM g x ∈ range (opIb U) := by simp_all
    obtain ⟨y, hy⟩ := hxr
    exact ⟨y, congrArg (⇑O.ι) hy⟩
  refine ⟨W, hmem, ps_ ≫ q, ?_, ?_, ?_⟩
  infer_instance
  rw [assoc, hqs, ← hps_]
  simp [assoc]
  rw [restrictIdeal_eq_comap_io] at hideal
  have hps' : ps_ ≫ (U.i ≫ O.ι) = W.i := hps_
  rw [restrictIdeal_eq_comap_io, ← hps', comap_comp,
    comap_comp, comap_ker_comp_of_isOpenImmersion g O.ι, hideal,
    comap_comp]

section
variable (hsm : AffineSpaceIsSmooth) (k : Type) [Field k] (M c : ℕ) {A : Sch} (rh_ : A ⟶ affineSpaceIndexedBy k (UFin M)) [IsClosedImmersion rh_]
include hsm
theorem hasSmoothCoordCodim_comp_pullbackBasicOpen_io
    (G : ↑((affineSpaceIndexedBy k $ UFin M).presheaf.obj $ op ⊤))
    (V : Opn A)
    (hV : V = (Opens.map (rh_ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M G))
    (e : (↑V : Sch) ⟶ (↑(pullbackBasicOpen k M G) : Sch))
    (hce : IsClosedImmersion e)
    (hceo : IsClosedImmersion $ e ≫ (pullbackBasicOpen k M G).ι)
    (hproj : e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 = V.ι ≫ rh_)
    (hrel : (ConcreteCategory.hom $ appTop $ e ≫ (pullbackBasicOpen k M G).ι)
      (lastCoordinate k M * pullbackAlongProjection k M G) = 1)
    (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFin M) rh_ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFS M 1)
      (e ≫ (pullbackBasicOpen k M G).ι) $ c + 1 := by
  subst hV
  have := hce
  have := isIso_shiftLastCoord_shiftLastCoordSection k M G
  have hE : ((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
      (asIso $ shiftLastCoord k M G $ lastCoordinateAddInvUnit k M G).hom = e := by
    show ((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫ shiftLastCoord k M G (lastCoordinateAddInvUnit k M G) = e
    rw [← cancel_mono (pullbackBasicOpen k M G).i, assoc, shiftLastCoord_comp_io]
    have hstr : (e ≫ opI (pullbackBasicOpen k M G)) ≫
          affineSpaceIndexedByToSpec k (UFS M 1) =
        (((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
            replaceLastCoord k M G (lastCoordinateAddInvUnit k M G)) ≫
          affineSpaceIndexedByToSpec k (UFS M 1) := by
      rw [assoc, assoc, replaceLastCoord_comp_affineSpaceIndexedByToSpec,
        ← assoc $ (rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G, morphismRestrict_ι,
        ← projLeft_comp_affineSpaceIndexedByToSpec k M 1, ← assoc (pullbackBasicOpen k M G).i, ← assoc e, hproj]
      simp only [assoc]
      rw [affineSpaceInl_comp_projLeft_assoc]
    refine AffineSpace.hom_ext hstr.symm ?_
    intro i
    obtain ⟨j⟩ := i
    cases j with
    | inl a =>
      have hl : (ConcreteCategory.hom $ appTop $ e ≫ opI (pullbackBasicOpen k M G))
            (AffineSpace.coord (Sp k)
              (⟨Sum.inl a⟩ : UFS M 1)) =
          (ConcreteCategory.hom $ appTop
            (e ≫ opI (pullbackBasicOpen k M G) ≫ projLeft k M 1))
            (AffineSpace.coord (Sp k) (⟨a⟩ : UFin M)) := by
        rw [← projLeft_appTop_coord k M 1 a, ← comp_apply,
          ← comp_appTop, assoc]
      have hr : (ConcreteCategory.hom $ appTop
            (((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
              replaceLastCoord k M G (lastCoordinateAddInvUnit k M G)))
            (AffineSpace.coord (Sp k)
              (⟨Sum.inl a⟩ : UFS M 1)) =
          (ConcreteCategory.hom $ appTop
            (e ≫ opI (pullbackBasicOpen k M G) ≫ projLeft k M 1))
            (AffineSpace.coord (Sp k) (⟨a⟩ : UFin M)) := by
        rw [hproj, comp_appTop, comp_apply,
          ← pullbackCoord_def (replaceLastCoord k M G $ lastCoordinateAddInvUnit k M G)
            (⟨Sum.inl a⟩ : UFS M 1),
          pullbackCoord_replaceLastCoord_inl, pullbackCoord_def, ← comp_apply,
          ← comp_appTop, morphismRestrict_ι, ← assoc,
          comp_appTop, comp_apply,
          ← pullbackCoord_def (affineSpaceInl k M 1)
            (⟨Sum.inl a⟩ : UFS M 1),
          pullbackCoord_affineSpaceInl_inl]
      exact tr_ hr hl.symm
    | inr b =>
      have hu : (ConcreteCategory.hom $ appTop $ e ≫ opI (pullbackBasicOpen k M G))
            (lastCoordinate k M) *
          (ConcreteCategory.hom $ appTop $ e ≫ opI (pullbackBasicOpen k M G))
            (pullbackAlongProjection k M G) = 1 := by
        rwa [← map_mul]
      have hX : (ConcreteCategory.hom $ appTop $ e ≫ opI (pullbackBasicOpen k M G))
            (pullbackAlongProjection k M G) =
          (ConcreteCategory.hom $ appTop
            ((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G)) ((unitOnPullbackBasicOpen k M G).val) := by
        rw [unitOnPullbackBasicOpen_val, ← comp_apply, ← comp_appTop,
          morphismRestrict_ι, pullbackAlongProjection_eq, ← comp_apply,
          ← comp_appTop, ← comp_apply, ← comp_appTop,
          assoc, assoc, assoc, affineSpaceInl_comp_projLeft,
          comp_id, hproj]
      have hw : (ConcreteCategory.hom $ appTop
            ((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G)) (((unitOnPullbackBasicOpen k M G)⁻¹).val) *
          (ConcreteCategory.hom $ appTop
            ((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G)) ((unitOnPullbackBasicOpen k M G).val) = 1 := by
        rw [← map_mul, inv_mul, map_one]
      have hRP : (ConcreteCategory.hom $ appTop
            (((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
              replaceLastCoord k M G (lastCoordinateAddInvUnit k M G))) (lastCoordinate k M) =
          (ConcreteCategory.hom $ appTop
            ((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G)) (((unitOnPullbackBasicOpen k M G)⁻¹).val) := by
        rw [comp_appTop, comp_apply, replaceLastCoord_appTop_lastCoordinate,
          shiftLastCoordSection_eq, map_add, ← comp_apply, ← comp_appTop,
          morphismRestrict_ι, ← assoc, lastCoordinate_appTop_comp_affineSpaceInl, zero_add]
      rw [hX] at hu
      rw [← lastCoordinate_eq_coord k M b, hRP]
      exact sy_ $ inv_unique (tr_ (mul_comm _ _) hu) $ tr_ (mul_comm _ _) hw
  have H2 := (HasSmoothCoordCodim.comp_affineSpaceInl hsm k rh_ 1 h).resLE_open $ pullbackBasicOpen k M G
  have hres : resLE (rh_ ≫ affineSpaceInl k M 1) (pullbackBasicOpen k M G)
      ((Opens.map (rh_ ≫ affineSpaceInl k M 1).base).obj $ pullbackBasicOpen k M G) le_rfl =
      ((rh_ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) := by
    rw [← cancel_mono (pullbackBasicOpen k M G).i, resLE_comp_ι, morphismRestrict_ι]
  rw [hres] at H2
  have hph : isoH (asIso $ shiftLastCoord k M G $ lastCoordinateAddInvUnit k M G) ≫
        (opI (pullbackBasicOpen k M G) ≫ affineSpaceIndexedByToSpec k (UFS M 1)) =
      opI (pullbackBasicOpen k M G) ≫ affineSpaceIndexedByToSpec k (UFS M 1) := by
    show shiftLastCoord k M G (lastCoordinateAddInvUnit k M G) ≫
        (opI (pullbackBasicOpen k M G) ≫ affineSpaceIndexedByToSpec k (UFS M 1)) = _
    rw [shiftLastCoord_comp_io_assoc, replaceLastCoord_comp_affineSpaceIndexedByToSpec]
  have H3 := H2.comp_iso_hom (asIso $ shiftLastCoord k M G $ lastCoordinateAddInvUnit k M G)
    (opI (pullbackBasicOpen k M G) ≫ affineSpaceIndexedByToSpec k (UFS M 1)) hph
  rw [hE] at H3
  exact hasSmoothCoordCodim_comp_opens_io (affineSpaceIndexedByToSpec k $ UFS M 1)
    (pullbackBasicOpen k M G) e hce hceo H3

theorem hasSmoothCoordCodim_basicOpenEmbedding F
    (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (UFin M)) rh_ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (UFin (M + 1)))
      (basicOpenEmbedding k M rh_ F ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv M 1) (Sp k)).hom) (c + 1) := by
  let _a0 := globalSectionLift k M rh_ F
  let _a1 := rh_ ≫ affineSpaceInl k M 1
  have hF : (m23 (appTop _a1))
      (pullbackAlongProjection k M _a0) = F := by
    rw [pullbackAlongProjection_eq, ← comp_apply, ← comp_appTop, assoc,
      affineSpaceInl_comp_projLeft, comp_id, appTop_globalSectionLift]
  have key : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (UFS M 1))
      (basicOpenEmbedding k M rh_ F) (c + 1) :=
    hasSmoothCoordCodim_comp_pullbackBasicOpen_io hsm k M c rh_ _a0 (bOpn A F) ((st_ (congrArg (fun r : (pObj A (op ⊤)) => bOpn A r) hF)) (preimage_basicOpen _a1 (pullbackAlongProjection k M _a0)).symm)
      (basicOpenToPullbackBasicOpen k M rh_ F)
      (isClosedImmersion_basicOpenToPullbackBasicOpen k M rh_ F) (isClosedImmersion_basicOpenEmbedding k M rh_ F)
      (basicOpenToPullbackBasicOpen_comp_projLeft k M rh_ F) (appTop_basicOpenEmbedding_lastCoordinate_mul k M rh_ F) h
  let _a3 := uliftFinSumEquiv M 1
  exact key.comp_iso_hom (affineSpaceIsoOfEquiv _a3 (Sp k))
    (affineSpaceIndexedByToSpec k (UFin (M + 1)))
    (affineSpaceIsoOfEquiv_hom_comp_toSpec k _a3)
end





variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]
  {k' : Type} [Field k'] [CharZero k'] {Y'} [IsAffine Y']
  {pY'} [LocallyOfFiniteType pY']

structure ChartFlatBaseChange (S : EmbeddedBlowupSequence k Y pY) (S' : EmbeddedBlowupSequence k' Y' pY') where
  ambientMap : S'.ambient ⟶ S.ambient
  flat_ambientMap : Flat ambientMap
  baseMap : Y' ⟶ Y
  isPullback_emb : IsPullback baseMap S'.emb S.emb ambientMap
  reindex : ℕ → ℕ
  levelMap : ∀ j : ℕ, j ≤ S'.length → (S'.schemeAt j ⟶ S.schemeAt (reindex j))
  reindex_lt : ∀ j : ℕ, j < S'.length → reindex j < S.length
  reindex_lt_succ : ∀ j : ℕ, j < S'.length → reindex j < reindex (j + 1)
  reindex_len : reindex S'.length = S.length
  isPullback_level : ∀ j hj,
    IsPullback (levelMap j hj) (S'.ambientSeq.projectionToBase j)
      (S.ambientSeq.projectionToBase $ reindex j) ambientMap
  isPullback_down : ∀ j hj i hi,
    (∀ m, i ≤ m → m < reindex j → ∀ j', j' < S'.length → reindex j' ≠ m) →
    IsPullback (levelMap j hj ≫ S.ambientSeq.transitionMap hi) (S'.ambientSeq.projectionToBase j)
      (S.ambientSeq.projectionToBase i) ambientMap
  isPullback_step : ∀ j hj (hsg_ : reindex j + 1 ≤ reindex (j + 1)),
    IsPullback (levelMap (j + 1) (succ_le_of_lt hj) ≫ S.ambientSeq.transitionMap hsg_)
      (S'.blowdown j) (S.blowdown $ reindex j) $ levelMap j $ Nat.le_of_lt hj
  center_eq : ∀ j hj,
    S'.ambientCenter j = (S.ambientCenter $ reindex j).comap (levelMap j $ Nat.le_of_lt hj)
  comap_center_skipped : ∀ i, i < S.length → (∀ j, j < S'.length → reindex j ≠ i) →
    ∀ (P : Sch) (q : P ⟶ S.schemeAt i) (p : P ⟶ S'.ambient),
      IsPullback q p (S.ambientSeq.projectionToBase i) ambientMap → (S.ambientCenter i).comap q = ⊤

namespace ChartFlatBaseChange

variable {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

instance instFlatAmbientMap (F : ChartFlatBaseChange S S') :
    Flat F.ambientMap := F.flat_ambientMap

theorem apply_lt_apply_of_forall_lt_succ
    {σ : ℕ → ℕ} {N : ℕ} (h : ∀ j, j < N → σ j < σ (j + 1)) :
    ∀ j, j ≤ N → ∀ i, i < j → σ i < σ j := by
  intro j hj i hij
  exact strictMonoOn_Iic_of_lt_succ h (mpr_ mem_Iic $ le_trans (le_of_lt hij) hj)
    (mpr_ mem_Iic hj) hij

section
variable (F : ChartFlatBaseChange S S')
theorem reindex_lt_reindex_of_lt {i j : ℕ} (hij : i < j) (hj : j ≤ S'.length) :
    F.reindex i < F.reindex j :=
  apply_lt_apply_of_forall_lt_succ (σ := F.reindex) (N := S'.length)
    F.reindex_lt_succ j hj i hij

theorem reindex_ne_of_reindex_lt_of_lt_reindex_succ j (hj : j < S'.length) m
    (h1 : F.reindex j < m) (h2 : m < F.reindex (j + 1)) j' (hj' : j' < S'.length) :
    F.reindex j' ≠ m := by
  intro hEq
  rcases m63 j' (j + 1) with hlt | hge
  have hle : F.reindex j' ≤ F.reindex j := by
    rcases m63 j' j with h | h
    exact le_of_lt $ F.reindex_lt_reindex_of_lt h $ le_of_lt hj
    have hjj := le_antisymm (mp_ lt_succ_iff hlt) h
    subst hjj
    exact le_rfl
  omega
  have hle : F.reindex (j + 1) ≤ F.reindex j' := by
    rcases Nat.eq_or_lt_of_le hge with h | h
    exact le_of_eq $ congrArg F.reindex h
    exact le_of_lt $ F.reindex_lt_reindex_of_lt h $ le_of_lt hj'
  omega

theorem flat_levelMap j (hj : j ≤ S'.length) :
    Flat $ F.levelMap j hj := by
  have hst : IsStableUnderBaseChange
      (@Flat) := inferInstance
  exact hst.of_isPullback (F.isPullback_level j hj).flip F.flat_ambientMap

theorem reindex_ne_of_lt_reindex_zero m
    (hm : m < F.reindex 0) j (hj : j < S'.length) : F.reindex j ≠ m := by
  have h : F.reindex 0 ≤ F.reindex j := by
    rcases m73 j with h0 | h0
    subst h0
    exact le_rfl
    exact le_of_lt $ F.reindex_lt_reindex_of_lt h0 $ le_of_lt hj
  omega

theorem reindex_le_length {j} (hj : j ≤ S'.length) :
    F.reindex j ≤ S.length := by
  rcases eq_or_lt_of_le hj with h | h
  subst h
  exact le_of_eq F.reindex_len
  exact le_of_lt $ F.reindex_lt j h

section
variable (j) (hj : j ≤ S'.length)
theorem strictTransformIdeal_comap_transitionMap_eq :
    ∀ n i (hi : i ≤ F.reindex j), i + n = F.reindex j →
      (∀ m, i ≤ m → m < F.reindex j → ∀ j', j' < S'.length → F.reindex j' ≠ m) →
      (S.strictTransformIdeal i).comap (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi)
        = (S.strictTransformIdeal (F.reindex j)).comap (F.levelMap j hj) := by
  intro n
  induction n with
  | zero =>
      intro i hi hsum _
      have hie : i = F.reindex j := by omega
      subst hie
      rw [S.ambientSeq.transitionMap_self hi, comp_id]
  | succ n ih =>
      intro i hi hsum hskip
      have hi1 : i + 1 ≤ F.reindex j := by omega
      have hlen := F.reindex_le_length hj
      have hiS := le_trans hi1 hlen
      have := S.isNoetherian_schemeAt (i + 1) hiS
      have hIH := ih (i + 1) hi1 (by omega)
        (fun m hm hm2 j' hj' => hskip m (by omega) hm2 j' hj')
      have hdown : S.ambientSeq.transitionMap hi1 ≫ S.blowdown i = S.ambientSeq.transitionMap hi := by
        have h := S.ambientSeq.transitionMap_trans (le_succ i) hi1
        rwa [← S.ambientSeq.blowupMorphism_eq_transitionMap] at h
      have htop :=
        F.comap_center_skipped i (by omega) (fun j' hj' => hskip i le_rfl (by omega) j' hj')
          (S'.schemeAt j) (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi)
          (S'.ambientSeq.projectionToBase j) (F.isPullback_down j hj i hi hskip)
      have hg := htop
      rw [← hdown, ← assoc, comap_comp] at hg
      have hst := strictTransform_comap_of_comap_center_eq_top (S.blowdown i)
        (S.ambientCenter i) (S.strictTransformIdeal i) (F.levelMap j hj ≫ S.ambientSeq.transitionMap hi1) hg
      rw [← hIH, S.strictTransformIdeal_succ i, hst, ← comap_comp, assoc,
        hdown]

theorem strictTransformIdeal_eq_comap :
    S'.strictTransformIdeal j = (S.strictTransformIdeal (F.reindex j)).comap (F.levelMap j hj) := by
  revert hj
  induction j with
  | zero =>
      intro hj
      have h0 : 0 ≤ F.reindex 0 := zero_le _
      have hskip : ∀ m, 0 ≤ m → m < F.reindex 0 → ∀ j', j' < S'.length → F.reindex j' ≠ m :=
        fun m _ hm j' hj' => F.reindex_ne_of_lt_reindex_zero m hm j' hj'
      have hkey := strictTransformIdeal_comap_transitionMap_eq F 0 hj (F.reindex 0) 0 h0 (by omega) hskip
      have hlev :=
        F.isPullback_down 0 hj 0 h0 hskip
      have hcomm : S'.ambientSeq.isoZero.inv ≫ (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0)
          = F.ambientMap ≫ S.ambientSeq.isoZero.inv := by
        have h1 := hlev.w
        rw [S.ambientSeq.projectionToBase_zero, S'.ambientSeq.projectionToBase_zero] at h1
        have h2 : (S'.ambientSeq.isoZero.inv ≫ (F.levelMap 0 hj ≫ S.ambientSeq.transitionMap h0)) ≫
            S.ambientSeq.isoZero.hom
            = (F.ambientMap ≫ S.ambientSeq.isoZero.inv) ≫ S.ambientSeq.isoZero.hom := by
          simp [assoc] at h1 ⊢
          rw [h1]
          simp
        exact mp_ (cancel_mono S.ambientSeq.isoZero.hom) h2
      have hC :=
        F.isPullback_emb.paste_vert ((of_horiz_isIso ⟨hcomm⟩).flip)
      have : QuasiCompact (S.emb ≫ S.ambientSeq.isoZero.inv) := inferInstance
      have :=
        quasiCompact_of_isPullback hC
      have :=
        m122
          (P := @Flat) hlev.flip inferInstance
      rw [← hkey, S'.strictTransformIdeal_zero, S.strictTransformIdeal_zero]
      exact ker_eq_comap_ker_of_isPullback_of_flat hC
  | succ n ih =>
      intro hj
      have hn := lt_of_succ_le hj
      have hnle := m49 hn
      have hsg_ := F.reindex_lt_succ n hn
      have := F.flat_levelMap n hnle
      have := S.isNoetherian_schemeAt (F.reindex n + 1) $ le_trans hsg_ (F.reindex_le_length hj)
      have := S'.isNoetherian_schemeAt (n + 1) hj
      have hst := comap_strictTransform_of_flat_of_isLocallyNoetherian
        (S.blowdown (F.reindex n)) (F.levelMap n hnle) (S'.blowdown n)
        (F.levelMap (n + 1) hj ≫ S.ambientSeq.transitionMap hsg_)
        (F.isPullback_step n hn hsg_) (S.ambientCenter (F.reindex n))
        (S.strictTransformIdeal (F.reindex n))
        (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism (F.reindex n) (F.reindex_lt n hn))
      have hbet :=
        fun m h1 h2 j' hj' => F.reindex_ne_of_reindex_lt_of_lt_reindex_succ n hn m (by omega) h2 j' hj'
      have hkey := strictTransformIdeal_comap_transitionMap_eq F (n + 1) hj
        (F.reindex (n + 1) - (F.reindex n + 1)) (F.reindex n + 1) hsg_ (by omega) hbet
      rw [← hkey, S.strictTransformIdeal_succ $ F.reindex n, hst, ← ih hnle, ← F.center_eq n hn]
      exact S'.strictTransformIdeal_succ n
end
end

theorem exists_iso_of_mono_of_comp_eq
    {A Z W : Sch} (g : Z ⟶ A) (i : W ⟶ A)
    [CategoryTheory.Mono g] [CategoryTheory.Mono i] (a : W ⟶ Z) (b : Z ⟶ W)
    (ha : a ≫ g = i) (hb : b ≫ i = g) :
    ∃ u : W ≅ Z, u.hom ≫ g = i := by
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  refine mp_ (cancel_mono i) ?_
  rw [assoc, hb, ha, id_comp]
  refine mp_ (cancel_mono g) ?_
  rw [assoc, ha, hb, id_comp]

theorem exists_iso_subscheme_ker
    {A Z : Sch} (g : Z ⟶ A) [IsClosedImmersion g] :
    ∃ u : (ker g).subscheme ≅ Z, u.hom ≫ g = (ker g).si := by
  have hker : (ker (m149 g).si) = m149 g :=
    ker_subschemeι _
  exact exists_iso_of_mono_of_comp_eq g (m149 g).si
    (lift g (m149 g).si $ le_of_eq hker.symm)
    (lift (m149 g).si g $ le_of_eq hker)
    (lift_fac ..)
    (lift_fac ..)

theorem exists_isPullback_subscheme_of_ker_eq
    {A B : Sch} f (I : ISD B) (J : ISD A)
    (hJ : J = ker (pullback.fst f I.si)) :
    ∃ g,
      g ≫ I.si = J.si ≫ f ∧
        IsPullback g J.si I.si f := by
  subst hJ
  have :=
    m122
      (P := @IsClosedImmersion)
      (of_hasPullback f I.si).flip inferInstance
  obtain ⟨u, hu⟩ := exists_iso_subscheme_ker $ pullback.fst f I.si
  let _s0 := u ≪≫ pullbackSymmetry f I.si
  have hfst : _s0.hom ≫ pullback.fst I.si f
      = u.hom ≫ pullback.snd f I.si := by
    rw [trans_hom, assoc, pullbackSymmetry_hom_comp_fst]
  have hsnd : _s0.hom ≫ pullback.snd I.si f
      = siI (ker $ pullback.fst f I.si) := by
    rw [trans_hom, assoc, pullbackSymmetry_hom_comp_snd, hu]
  have hcomm : (isoH _s0 ≫ pullback.fst I.si f)
        ≫ siI I
      = siI (ker $ pullback.fst f I.si) ≫ f := by
    rw [hfst, assoc, ← pullback.condition, ← assoc, hu]
  exact ⟨isoH _s0 ≫ pullback.fst I.si f, hcomm,
    of_iso_pullback ⟨hcomm⟩ _s0 rfl hsnd⟩

section
variable (F : ChartFlatBaseChange S S') (j) (hj : j ≤ S'.length)
theorem exists_isPullback_strictTransformio :
    ∃ g : S'.strictTransform j ⟶ S.strictTransform (F.reindex j),
      g ≫ S.strictTransformio (F.reindex j) = S'.strictTransformio j ≫ F.levelMap j hj ∧
        IsPullback g (S'.strictTransformio j) (S.strictTransformio $ F.reindex j) (F.levelMap j hj) := by
  exact exists_isPullback_subscheme_of_ker_eq (F.levelMap j hj)
    (S.strictTransformIdeal $ F.reindex j) (S'.strictTransformIdeal j) $ F.strictTransformIdeal_eq_comap j hj

def strictTransformComparison :
    S'.strictTransform j ⟶ S.strictTransform (F.reindex j) :=
  (F.exists_isPullback_strictTransformio j hj).choose

theorem strictTransformComparison_comp_strictTransformio :
    F.strictTransformComparison j hj ≫ S.strictTransformio (F.reindex j) = S'.strictTransformio j ≫ F.levelMap j hj :=
  (F.exists_isPullback_strictTransformio j hj).choose_spec.1

theorem isPullback_strictTransformComparison_strictTransformio :
    IsPullback (F.strictTransformComparison j hj) (S'.strictTransformio j) (S.strictTransformio $ F.reindex j)
      (F.levelMap j hj) :=
  (F.exists_isPullback_strictTransformio j hj).choose_spec.2

theorem flat_strictTransformComparison :
    Flat $ F.strictTransformComparison j hj := by
  have hst : IsStableUnderBaseChange
      (@Flat) := inferInstance
  exact hst.of_isPullback (F.isPullback_strictTransformComparison_strictTransformio j hj).flip $ F.flat_levelMap j hj
end

end ChartFlatBaseChange

def chartFlatBaseChangeOfIsPullbackSeq (S : EmbeddedBlowupSequence k Y pY) (S' : EmbeddedBlowupSequence k' Y' pY')
    (f : S'.ambient ⟶ S.ambient) [Flat f] (b : Y' ⟶ Y)
    (hb : IsPullback b S'.emb S.emb f)
    (hpb : IsPullbackBlowupSequence f S'.ambientSeq S.ambientSeq) :
    ChartFlatBaseChange S S' where
  ambientMap := f
  flat_ambientMap := inferInstance
  baseMap := b
  isPullback_emb := hb
  reindex := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose
  levelMap := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose
  reindex_lt := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.1
  reindex_lt_succ := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.1
  reindex_len := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.1
  isPullback_level := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.1
  isPullback_down := (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.1
  isPullback_step :=
    (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.2.1
  center_eq :=
    (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.2.2.1
  comap_center_skipped :=
    (IsPullbackBlowupSequence.exists_reindexing_of_flat f hpb).choose_spec.choose_spec.2.2.2.2.2.2.2

end FunctorialResolution.EmbeddedResolution

end
end
end
