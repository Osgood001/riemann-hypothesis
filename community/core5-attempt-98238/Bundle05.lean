import Mathlib
import Bundle00
import Bundle01
import Bundle02
import Bundle03
import Bundle04
noncomputable section
open CategoryTheory AlgebraicGeometry
open FunctorialResolution.Blowup (IsBlowupAlongIdealSheaf IsLocallyGeneratedByNonZeroDivisor affineBlowup affineBlowupChart chartFraction chartRingHom chartRingHom_apply chartRingHom_coe_eq_chartFraction_mul chartRingHom_mem_nonZeroDivisors chartSectionsIso chartSectionsIso_hom_apply chartSectionsRingHom chartSectionsRingHom_apply chartSectionsRingHom_chartRingHom comap_io_support_compl_eq_top comap_ker_comp_of_isOpenImmersion comap_map_of_isClosedImmersion comap_schemeImageIdeal comap_specIdealSheaf_ideal_eq_span exceptionalIdeal exceptionalIdeal_eq_comap exists_chart_affineOpen_mem_nonZeroDivisors isBlowupAlongIdealSheaf_affineBlowup_toSpec mem_opensRange_affineBlowupChart_of_ideal_eq_span mem_reesGrading_iff_coeff mem_reesGrading_iff_monomial reesDegreeZeroEquiv reesDegreeZeroEquiv_coe_coe reesGenerator reesGrading sectionsRingHom sectionsRingHom_apply sectionsRingHom_restrict specIdealSheaf specIdealSheaf_eq_ofIdealTop strictTransform strictTransformImmersion_eq strictTransformOpens_eq strictTransform_eq_ker)
open FunctorialResolution.Blowup.AffineBlowup (toSpec)
open Set (disjoint_left eq_empty_of_subset_empty eq_univ_of_forall ext_iff image_congr image_inter_preimage image_preimage_eq_inter_range image_preimage_subset inter_subset_right mem_biUnion mem_compl_iff mem_iUnion mem_inter mem_inter_iff mem_preimage mem_range mem_range_self mem_sdiff mem_sdiff_of_mem mem_singleton_iff mem_univ preimage preimage_compl preimage_sdiff preimage_univ range range_comp range_eq_empty subset_univ univ)
open Nat (add_assoc find find_min find_min' find_spec le_induction le_of_succ_le le_succ le_zero lt_of_succ_le lt_succ_iff lt_succ_of_lt lt_succ_self not_lt_zero not_succ_le_self sInf_le sInf_mem succ_le_of_lt zero_add zero_le)
open List (cons_append length length_append length_cons length_map map_congr_left map_drop mem_append mem_cons mem_iff_getElem mem_range'_1 prod_cons)
open Ideal (comap eq_top_iff_one exists_le_maximal mapHom map_id map_le_iff_le_comap map_map mem_comap mem_inf mem_map_of_mem mem_span_singleton' mem_span_singleton_mul mem_span_singleton_self mul_le mul_le_inf mul_mem_left mul_mem_mul span span_singleton_mul_right_unit)
open Scheme.IdealSheafData (appLE_mem_comap_ideal comapIso_hom_fst comapIso_inv_subschemeι comap_comp comap_id comap_ideal_eq_map_appLE comap_mono comap_ofIdealTop comap_top equivOfIsAffine equivOfIsAffine_apply equivOfIsAffine_symm_apply exists_iso_subscheme_comap_of_isIso ideal_comap_of_isOpenImmersion ideal_mul ideal_pow ideal_top inclusion inclusion_subschemeι ker_subschemeι le_def le_map_comap map_bot map_mono mem_support_comap ofIdealTop one_eq_top range_subschemeι subscheme subschemeι subschemeι_app support support_antitone support_eq_bot_iff)
open Finset (finite_toSet mem_singleton mul_prod_erase prod_congr prod_eq_single sum_eq_single)
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData (append obj ofSequenceOfBlowups toMarkedBlowupSequenceData_toSequenceOfBlowups)
open HomogeneousLocalization (Away deg den den_mem den_mem_deg eq_num_div_den num num_mem_deg val val_injective val_mul)
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (appendBoundary_of_le_length appendToBlowupSequenceData_center_length appendToBlowupSequenceData_center_of_lt_length appendToBlowupSequenceData_schemeAt_of_le_length append_schemeAt_of_le_length monomialBlowupIterate_succ monomialBlowupIterate_zero ofMarkedSequence toMarkedSequenceOfBlowups)
open Localization (mk mk_eq_mk_iff mk_mul r_of_eq)
open Submodule (FG mul_induction_on neg_mem span_induction sub_mem subset_span)
open IsClosedImmersion (isAffine_surjective_of_isAffine isIso_of_ker_eq of_surjective_of_isAffine)
open SetLike (coe_injective mem_coe)
open Algebra (FormallyEtale FormallyUnramified)
open Scheme.Cover (hom_ext mkOfCovers)
open Scheme (GSpecIso IdealSheafData basicOpen basicOpen_one exists_isAffineOpen_mem inv_hom_apply isoSpec_hom mem_zeroLocus_iff preimage_basicOpen presheaf_map_eq_of_parallel zeroLocus_span)
open Iso (hom hom_inv_id_apply hom_inv_id_assoc inv inv_comp_eq symm_hom symm_inv trans_hom trans_inv)
open Scheme.Hom (app appIso appIso_hom' appLE appLE_comp_appLE appLE_eq_app appTop app_eq_appLE comp_app comp_appTop comp_preimage id_preimage image_preimage_eq_opensRange_inf image_top_eq_opensRange isClosedEmbedding isEmbedding ker ker_apply ker_comp ker_comp_of_isIso le_ker_comp opensFunctor opensRange pre preimage_image_eq stalkMap_comp support_ker)
open Category (assoc comp_id id_comp)
open Limits.pullback (condition fst lift_fst lift_snd snd)
open CommRingCat (comp_apply hom_comp hom_id ofHom)
open Sum (elim inl inr)
open ULift (up)
open IsOpenImmersion (bijective_appLE_of_image_eq lift lift_fac)
open IsLocalRing (maximalIdeal mem_maximalIdeal)
open RingHom (id_apply mem_ker toAlgebra)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (blowupMorphism_eq_transitionMap center projectionToBase schemeAt transitionMap transitionMapSucc transitionMap_def)
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates (partialDeriv partialDeriv_coord_self)
open Submonoid (mem_powers powers)
open IsLocalization (eq_iff_exists map_units mem_map_algebraMap_iff)
open Pi (mul_apply pow_apply)
open Classical (propDecidable)
open MorphismProperty.IsStableUnderBaseChange (of_isPullback)
open Polynomial (C_mul_monomial monomial)
open Iff (mp)
open Scheme.Opens (toScheme ι)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (IsAdmissible bc boundary ideal mult scheme structMap withBoundary)
open And (left right)
section


namespace FunctorialResolution.EmbeddedResolution


section
variable {X Y Z : Sch} (h1 : X = Y) (h2 : Y = Z)
theorem comap_eqToHom_trans
    (J : ISD Z) :
    (J.comap $ eqToHom h2).comap (eqToHom h1) = J.comap (eqToHom $ h1.trans h2) := by
  subst h1
  subst h2
  simp

theorem map_comap_eqToHom_trans
    (L : Bdy Z) :
    List.map (fun D => D.comap $ eqToHom h1) (List.map (fun D => D.comap $ eqToHom h2) L)
      = List.map (fun D => D.comap $ eqToHom $ h1.trans h2) L := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    rw [m75, m75, m75, ih, comap_eqToHom_trans]
end

namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

structure IsPrefix (s t : MarkedBlowupSequenceData p I m E) : Prop where
  length_le : s.length ≤ t.length
  obj_eq : ∀ i ≤ s.length, s.obj i = t.obj i
  proj_eq : ∀ i hi, s.proj i = eqToHom (obj_eq i hi) ≫ t.proj i
  ideal_eq : ∀ i hi,
    s.ideal i = (t.ideal i).comap (eqToHom $ obj_eq i hi)
  boundary_eq : ∀ i hi,
    s.boundary i = List.map (fun D => D.comap $ eqToHom $ obj_eq i hi) (t.boundary i)
  center_eq : ∀ i hi,
    s.center i = (t.center i).comap (eqToHom $ obj_eq i $ Nat.le_of_lt hi)
  map_eq : ∀ i hi,
    s.map i ≫ eqToHom (obj_eq i $ Nat.le_of_lt hi) =
      eqToHom (obj_eq (i + 1) $ succ_le_of_lt hi) ≫ t.map i

section
variable (s : MarkedBlowupSequenceData p I m E)
theorem IsPrefix.refl : s.IsPrefix s := by
  refine ⟨le_rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  intro i hi
  simp
  simp_all
  simp_all
  simp_all
  intro i hi
  simp

end

theorem IsPrefix.trans {s t r : MarkedBlowupSequenceData p I m E} (h : s.IsPrefix t)
    (h' : t.IsPrefix r) : s.IsPrefix r := by
  have hlen := h.length_le
  have hobj := fun i hi =>
    (h.obj_eq i hi).trans $ h'.obj_eq i $ hi.trans hlen
  refine ⟨hlen.trans h'.length_le, hobj, ?_, ?_, ?_, ?_, ?_⟩
  intro i hi
  rw [h.proj_eq i hi, h'.proj_eq i $ hi.trans hlen, ← assoc, eqToHom_trans]
  intro i hi
  rw [h.ideal_eq i hi, h'.ideal_eq i $ hi.trans hlen, comap_eqToHom_trans]
  intro i hi
  rw [h.boundary_eq i hi, h'.boundary_eq i $ hi.trans hlen, map_comap_eqToHom_trans]
  intro i hi
  rw [h.center_eq i hi, h'.center_eq i $ lt_of_lt_of_le hi hlen, comap_eqToHom_trans]
  intro i hi
  have hi' := lt_of_lt_of_le hi hlen
  rw [← eqToHom_trans (h.obj_eq i $ m49 hi) $ h'.obj_eq i $ m49 hi',
    ← eqToHom_trans (h.obj_eq (i + 1) $ succ_le_of_lt hi)
      (h'.obj_eq (i + 1) $ succ_le_of_lt hi'),
    ← assoc, h.map_eq i hi, assoc, h'.map_eq i hi', ← assoc]

end MarkedBlowupSequenceData

section

variable (T : MarkedIdealWithBoundary) (s : T.mbs)
def lastNonMonomialPart :
    IdealSheafData $ s.obj s.length :=
  nonMonomialPart (s.boundary s.length) $ s.ideal s.length

def maxOrderNonMonomial : ℕ :=
  maxOrder $ lastNonMonomialPart T s

def NonMonomialOrderReductionContinues : Prop :=
  mult T ≤ maxOrderNonMonomial T s ∧
    (orderAtLeastLocus (lastNonMonomialPart T s) $ maxOrderNonMonomial T s).Nonempty

theorem nonMonomialOrderReductionContinues_iff :
    NonMonomialOrderReductionContinues T s ↔
      mult T ≤ maxOrderNonMonomial T s ∧
        (orderAtLeastLocus (lastNonMonomialPart T s) $ maxOrderNonMonomial T s).Nonempty :=
  m22

def maxOrderNonMonomialOnOrderLocus : ℕ :=
  maxOrderOn (lastNonMonomialPart T s) $ orderAtLeastLocus (s.ideal s.length) T.mult

def CompanionIdealReductionContinues : Prop :=
  1 ≤ maxOrderNonMonomialOnOrderLocus T s

theorem companionIdealReductionContinues_iff :
    CompanionIdealReductionContinues T s ↔ 1 ≤ maxOrderNonMonomialOnOrderLocus T s :=
  m22

def companionIdeal :
    IdealSheafData $ s.obj s.length :=
  lastNonMonomialPart T s ^ T.mult ⊔ s.ideal s.length ^ maxOrderNonMonomialOnOrderLocus T s

theorem tripleAtLength_dim
    J mu_ :
    (tripleAtLength T s J mu_).krullDimSucc = krullDimSucc (s.obj s.length) :=
  rfl

end

section

def principalizationSeqAtEnd (T : MarkedIdealWithBoundary)
    (rc : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : T.mbs)
    (J : IdealSheafData $ s.obj s.length) (mu_ : ℕ)
    (hd : (tripleAtLength T s J mu_).krullDimSucc ≤ T.krullDimSucc) :
    MarkedSequenceOfBlowups (s.proj s.length ≫ structMap T) J mu_ $ s.boundary s.length :=
  rc (tripleAtLength T s J mu_) hd

section
variable (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary) (rc : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) (s : T.mbs) (J) (mu_) (hd : (tripleAtLength T s J mu_).krullDimSucc ≤ T.krullDimSucc)
theorem appendRecursivePrincipalization_eq_appendIfMarked :
    appendRecursivePrincipalization hinv T rc s J mu_ = appendIfMarked hinv s J mu_ (principalizationSeqAtEnd T rc s J mu_ hd) := by
  unfold appendRecursivePrincipalization principalizationSeqAtEnd
  rw [dif_pos hd]

theorem appendRecursivePrincipalization_eq_append
    (hm : (principalizationSeqAtEnd T rc s J mu_ hd).toBsd.IsMarked
      (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult $ s.boundary s.length) :
    appendRecursivePrincipalization hinv T rc s J mu_ =
      s.append
        ((principalizationSeqAtEnd T rc s J mu_ hd).toBsd.toMarkedBlowupSequenceData
          (s.proj s.length ≫ structMap T) (s.ideal s.length) T.mult (s.boundary s.length) hm)
        hinv := by
  let _a0 := principalizationSeqAtEnd T rc s J mu_ hd
  have hr : markedDataOfSeq s J mu_ _a0 =
      some (_a0.toBsd.toMarkedBlowupSequenceData
        (lastP s ≫ tMp T) (lastI s) T.mult (lastB s) hm) := by
    unfold markedDataOfSeq
    exact dif_pos hm
  rw [appendRecursivePrincipalization_eq_appendIfMarked hinv T rc s J mu_ hd]
  unfold appendIfMarked
  rw [hr]
end

end

section

variable (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
  (rc : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)

section
variable (s : T.mbs)
def extendByNonMonomialPart :
    T.mbs :=
  appendRecursivePrincipalization hinv T rc s (lastNonMonomialPart T s) $ maxOrderNonMonomial T s

def extendByCompanionIdeal :
    T.mbs :=
  appendRecursivePrincipalization hinv T rc s (companionIdeal T s) $ mult T * maxOrderNonMonomialOnOrderLocus T s
end

theorem nonMonomialOrderReductionIter_zero :
    nonMonomialOrderReductionIter hinv T rc 0 = T.embs :=
  rfl

section
variable (f : ℕ)
theorem nonMonomialOrderReductionIter_succ_of_continues (h : NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc f)) :
    nonMonomialOrderReductionIter hinv T rc (f + 1) = extendByNonMonomialPart hinv T rc (nonMonomialOrderReductionIter hinv T rc f) := by
  rw [nonMonomialOrderReductionIter]
  exact if_pos h

section
variable (h : ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T rc f))
include h
theorem nonMonomialOrderReductionIter_succ_of_not_continues :
    nonMonomialOrderReductionIter hinv T rc (f + 1) = nonMonomialOrderReductionIter hinv T rc f := by
  rw [nonMonomialOrderReductionIter]
  exact if_neg h

theorem nonMonomialOrderReductionIter_eq_of_not_continues :
    ∀ g, f ≤ g → nonMonomialOrderReductionIter hinv T rc g = nonMonomialOrderReductionIter hinv T rc f := by
  intro g hg
  induction g, hg using le_induction with
  | base => rfl
  | succ n hn ih =>
    have hn' := h
    rw [← ih] at hn'
    rwa [nonMonomialOrderReductionIter_succ_of_not_continues hinv T rc n hn']
end
end

theorem nonMonomialOrderReduction_eq :
    nonMonomialOrderReduction hinv T rc =
      nonMonomialOrderReductionIter hinv T rc (maxOrder (nonMonomialPart T.boundary T.ideal) + 1) :=
  rfl

section
variable (s0_ : T.mbs)
theorem companionIdealReductionIter_zero :
    companionIdealReductionIter hinv T rc s0_ 0 = s0_ :=
  rfl

section
variable (f : ℕ)
theorem companionIdealReductionIter_succ_of_continues (h : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s0_ f)) :
    companionIdealReductionIter hinv T rc s0_ (f + 1) =
      extendByCompanionIdeal hinv T rc (companionIdealReductionIter hinv T rc s0_ f) := by
  rw [companionIdealReductionIter]
  exact if_pos h

section
variable (h : ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s0_ f))
include h
theorem companionIdealReductionIter_succ_of_not_continues :
    companionIdealReductionIter hinv T rc s0_ (f + 1) = companionIdealReductionIter hinv T rc s0_ f := by
  rw [companionIdealReductionIter]
  exact if_neg h

theorem companionIdealReductionIter_eq_of_not_continues :
    ∀ g, f ≤ g → companionIdealReductionIter hinv T rc s0_ g = companionIdealReductionIter hinv T rc s0_ f := by
  intro g hg
  induction g, hg using le_induction with
  | base => rfl
  | succ n hn ih =>
    have hn' := h
    rw [← ih] at hn'
    rwa [companionIdealReductionIter_succ_of_not_continues hinv T rc s0_ n hn']
end
end
end

theorem companionIdealReduction_eq :
    companionIdealReduction hinv T rc =
      companionIdealReductionIter hinv T rc (nonMonomialOrderReduction hinv T rc)
        (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T rc) + 1) :=
  rfl

theorem orderReductionData_eq :
    orderReductionData hinv T rc =
      (companionIdealReduction hinv T rc).append
        (ofMarkedSequence
          (monomialPrincipalization hinv
            (tripleAtLength T (companionIdealReduction hinv T rc)
              ((companionIdealReduction hinv T rc).ideal (companionIdealReduction hinv T rc).length) T.mult)))
        hinv :=
  rfl

theorem orderReductionSeq_eq_of_nonempty (h : (orderAtLeastLocus T.ideal T.mult).Nonempty) :
    orderReductionSeq hinv T rc = toMarkedSequenceOfBlowups (orderReductionData hinv T rc) := by
  unfold orderReductionSeq
  rw [if_neg h.ne_empty]

end





namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (s : MarkedBlowupSequenceData p I m E)
section
variable (h : IsAdmissibleCenter s)
def monomialBlowupStep :
    MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length :=
  ofSingleBlowup (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length)
    (centerAtLast s) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_length :
    (monomialBlowupStep s h).length = 1 :=
  ofSingleBlowup_length h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

@[simp]
theorem monomialBlowupStep_schemeAt_zero :
    (monomialBlowupStep s h).obj 0 = s.obj s.length :=
  rfl

@[simp]
theorem monomialBlowupStep_schemeAt_succ (i : ℕ) :
    (monomialBlowupStep s h).obj (i + 1) = Blowup.blowup (centerAtLast s) :=
  ofSingleBlowup_schemeAt_succ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 i

@[simp]
theorem monomialBlowupStep_center_zero :
    (monomialBlowupStep s h).center 0 = centerAtLast s :=
  rfl

@[simp]
theorem monomialBlowupStep_blowupMorphism_zero :
    (monomialBlowupStep s h).map 0 = Blowup.blowup.proj (centerAtLast s) :=
  rfl

@[simp]
theorem monomialBlowupStep_projectionToBase_one :
    (monomialBlowupStep s h).proj 1 = Blowup.blowup.proj (centerAtLast s) :=
  rfl

@[simp]
theorem monomialBlowupStep_ideal_one :
    ideal (monomialBlowupStep s h) 1 =
      residualByPow ((s.ideal s.length).comap $ Blowup.blowup.proj $ centerAtLast s)
        ((centerAtLast s).comap $ Blowup.blowup.proj $ centerAtLast s) m :=
  rfl

@[simp]
theorem monomialBlowupStep_boundary_one :
    boundary (monomialBlowupStep s h) 1 =
      List.map (Blowup.strictTransform (Blowup.blowup.proj $ centerAtLast s) $ centerAtLast s)
          (s.boundary s.length) ++
        [Blowup.exceptionalIdeal (Blowup.blowup.proj $ centerAtLast s) $ centerAtLast s] :=
  rfl

theorem monomialBlowupStep_isoObjZero_inv :
    (monomialBlowupStep s h).isoZero.inv = eqToHom (monomialBlowupStep_schemeAt_zero s h).symm :=
  rfl
end

theorem appendProjectionToBase_of_lt
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length)
    i j (hi : s.length < i) (hj : i - s.length = j)
    (hobj : (s.appendToBlowupSequenceData t).obj i = t.obj j) :
    s.appendProjectionToBase t i = eqToHom hobj ≫ t.proj j ≫ s.proj s.length := by
  subst hj
  exact appendProjectionToBase_of_length_lt s t hi
end

section
variable (hinv : ComapIsoInvariance) (s : MarkedBlowupSequenceData p I m E)
section
variable (h : IsAdmissibleCenter s)
include h
theorem blowupAtCenter_eq_append :
    blowupAtCenter hinv s = append s (monomialBlowupStep s h) hinv := by
  unfold blowupAtCenter monomialBlowupStep
  rw [dif_pos h]

theorem boundary_succ_of_eq_append (d : MarkedBlowupSequenceData p I m E)
    (hd : d = append s (monomialBlowupStep s h) hinv)
    e :
    d.boundary (s.length + 1) =
      List.map (fun D => D.comap $ eqToHom e)
        (List.map (Blowup.strictTransform (Blowup.blowup.proj $ centerAtLast s) $ centerAtLast s)
            (s.boundary s.length) ++
          [Blowup.exceptionalIdeal (Blowup.blowup.proj $ centerAtLast s) $ centerAtLast s]) := by
  subst hd
  let _a0 := monomialBlowupStep s h
  refine m32 (append_boundary s _a0 hinv $ s.length + 1) ?_
  exact m32 (appendBoundary_length_succ s _a0) $ congrArg (m39 fun D : IdealSheafData (Blowup.blowup $ centerAtLast s) => cmI D $ eqToHom e) $ monomialBlowupStep_boundary_one s h

theorem blowupAtCenter_length :
    (blowupAtCenter hinv s).length = s.length + 1 := by
  rw [blowupAtCenter_eq_append hinv s h, append_length, monomialBlowupStep_length]

theorem blowupAtCenter_schemeAt_succ :
    (blowupAtCenter hinv s).obj (s.length + 1) = Blowup.blowup (centerAtLast s) := by
  rw [blowupAtCenter_eq_append hinv s h, append_schemeAt_of_length_lt s (monomialBlowupStep s h) hinv $ lt_succ_self s.length]
  have he : s.length + 1 - s.length = 0 + 1 := by omega
  rw [he, monomialBlowupStep_schemeAt_succ s h 0]

theorem blowupAtCenter_ideal_succ :
    ideal (blowupAtCenter hinv s) (s.length + 1) =
      (residualByPow ((s.ideal s.length).comap $ Blowup.blowup.proj $ centerAtLast s)
          ((centerAtLast s).comap $ Blowup.blowup.proj $ centerAtLast s) m).comap
        (eqToHom $ blowupAtCenter_schemeAt_succ hinv s h) := by
  let _a0 := p34 $ centerAtLast s
  have key : ∀ d : MarkedBlowupSequenceData p I m E, d = append s (monomialBlowupStep s h) hinv →
      ∀ hobj : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s),
        d.ideal (s.length + 1) =
          (residualByPow (cmI (lastI s) _a0)
              (cmI (centerAtLast s) _a0) m).comap (eqToHom hobj) := by
    rintro d rfl hobj
    rewrite [append_ideal, appendIdeal_length_succ, monomialBlowupStep_ideal_one]
    rfl
  exact key (blowupAtCenter hinv s) (blowupAtCenter_eq_append hinv s h)
    (blowupAtCenter_schemeAt_succ hinv s h)

theorem blowupAtCenter_boundary_succ :
    boundary (blowupAtCenter hinv s) (s.length + 1) =
      List.map (fun D => D.comap $ eqToHom $ blowupAtCenter_schemeAt_succ hinv s h)
        (List.map (Blowup.strictTransform (Blowup.blowup.proj $ centerAtLast s) $ centerAtLast s)
            (s.boundary s.length) ++
          [Blowup.exceptionalIdeal (Blowup.blowup.proj $ centerAtLast s) $ centerAtLast s]) :=
  boundary_succ_of_eq_append hinv s h (blowupAtCenter hinv s)
    (blowupAtCenter_eq_append hinv s h) $ blowupAtCenter_schemeAt_succ hinv s h

theorem blowupAtCenter_projectionToBase_succ :
    (blowupAtCenter hinv s).proj (s.length + 1) =
      eqToHom (blowupAtCenter_schemeAt_succ hinv s h) ≫ Blowup.blowup.proj (centerAtLast s) ≫ s.proj s.length := by
  let _a0 := monomialBlowupStep s h
  have key : ∀ d : MarkedBlowupSequenceData p I m E, d = append s _a0 hinv →
      ∀ hobj : d.obj (s.length + 1) = Blowup.blowup (centerAtLast s),
        d.proj (s.length + 1) =
          eqToHom hobj ≫ p34 (centerAtLast s) ≫ lastP s := by
    rintro d rfl hobj
    rewrite [append_projectionToBase,
      appendProjectionToBase_of_lt s _a0 (s.length + 1) 1 (by omega) (by omega)
        (appendToBlowupSequenceData_schemeAt_length_succ s _a0),
      monomialBlowupStep_projectionToBase_one]
    rfl
  exact key (blowupAtCenter hinv s) (blowupAtCenter_eq_append hinv s h)
    (blowupAtCenter_schemeAt_succ hinv s h)
end

theorem isStationaryAt_iff_not_isAdmissibleCenter n :
    IsStationaryAt hinv s n ↔ ¬ IsAdmissibleCenter (monomialBlowupIterate hinv s n) := by
  let _a0 := monomialBlowupIterate hinv s n
  constructor
  intro h hstep
  have h' : (blowupAtCenter hinv _a0).length
      = _a0.length := h
  rw [blowupAtCenter_length hinv _a0 hstep] at h'
  omega
  intro h
  show (blowupAtCenter hinv _a0).length
      = _a0.length
  unfold blowupAtCenter
  rw [dif_neg h]
end

end MarkedBlowupSequenceData

section

variable {k : Type} [Field k] {X : Sch}

section
variable {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
section
variable (hinv : ComapIsoInvariance)
section
variable (s : MarkedBlowupSequenceData p I m E)
theorem monomialBlowupIterate_length (n : ℕ) :
    (∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter $ MarkedBlowupSequenceData.monomialBlowupIterate hinv s j) →
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n).length = s.length + n := by
  induction n with
  | zero =>
      intro _
      rw [monomialBlowupIterate_zero, Nat.add_zero]
  | succ n ih =>
      intro hstep
      have h1 := ih fun j hj => hstep j $ lt_succ_of_lt hj
      have e1 : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s $ n + 1).length
          = (MarkedBlowupSequenceData.monomialBlowupIterate hinv s n).length + 1 := by
        rw [monomialBlowupIterate_succ,
          MarkedBlowupSequenceData.blowupAtCenter_length hinv _ $ hstep n $ lt_succ_self n]
      omega

end

section
variable (d : MarkedBlowupSequenceData p I m E)
theorem blowupAtCenter_schemeAt_of_le (i : ℕ) (hi : i ≤ d.length) :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).obj i = d.obj i := by
  by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter d
  rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h]
  exact append_schemeAt_of_le_length d (MarkedBlowupSequenceData.monomialBlowupStep d h) hinv hi
  have hs : MarkedBlowupSequenceData.blowupAtCenter hinv d = d := by
    unfold MarkedBlowupSequenceData.blowupAtCenter
    rw [dif_neg h]
  rw [hs]

theorem monomialBlowupIterate_length_le_and_schemeAt_eq j :
    d.length ≤ (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).length ∧
      ∀ i ≤ d.length, (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i := by
  induction j with
  | zero =>
      constructor
      exact le_of_eq $ by rw [monomialBlowupIterate_zero]
      intro i _
      rw [monomialBlowupIterate_zero]
  | succ j ih =>
      constructor
      refine le_trans ih.1 ?_
      rw [monomialBlowupIterate_succ]
      by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter $ MarkedBlowupSequenceData.monomialBlowupIterate hinv d j
      rw [MarkedBlowupSequenceData.blowupAtCenter_length hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) h]
      omega
      have hs : MarkedBlowupSequenceData.blowupAtCenter hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) = (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j) := by
        unfold MarkedBlowupSequenceData.blowupAtCenter
        rw [dif_neg h]
      exact le_of_eq $ by rw [hs]
      intro i hi
      rw [monomialBlowupIterate_succ,
        blowupAtCenter_schemeAt_of_le hinv (p22 hinv d j) i
          (le_trans hi ih.1)]
      exact an2 ih i hi

theorem monomialBlowupIterate_add (a b : ℕ) :
    MarkedBlowupSequenceData.monomialBlowupIterate hinv d (a + b) =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv (MarkedBlowupSequenceData.monomialBlowupIterate hinv d a) b := by
  induction b with
  | zero => rw [Nat.add_zero, monomialBlowupIterate_zero]
  | succ b ih =>
      rw [← add_assoc, monomialBlowupIterate_succ,
        monomialBlowupIterate_succ, ih]
end
end

theorem boundary_eq_map_comap_of_index_eq
    (d t : MarkedBlowupSequenceData p I m E) (n L : ℕ) (hL : L = n)
    (hb : ∀ ho : d.obj n = t.obj n,
      d.boundary n = List.map (fun D => D.comap $ eqToHom ho) (t.boundary n))
    (H : d.obj n = t.obj L) :
    d.boundary n = List.map (fun D => D.comap $ eqToHom H) (t.boundary L) := by
  subst hL
  exact hb H

end

section
variable (hinv : ComapIsoInvariance)
section
variable (p : X ⟶ Sp k) (I : ISD X) (m : ℕ) (E : Bdy X)
def monomialStallIndex : ℕ :=
  sInf {n : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n}

theorem monomialStallIndex_eq_of_isStationaryAt n
    (hstall : MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n)
    (hstep : ∀ j < n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) j)) :
    monomialStallIndex hinv p I m E = n := by
  have hne : ∃ j, MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) j := ⟨n, hstall⟩
  have h1 : monomialStallIndex hinv p I m E ≤ n := sInf_le hstall
  refine le_antisymm h1 ?_
  by_contra hlt
  exact (mp_ (MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv _ _) $ sInf_mem hne) $ hstep _ $ lt_of_not_ge hlt

theorem isAdmissibleCenter_of_lt_monomialStallIndex (n : ℕ) (hn : n < monomialStallIndex hinv p I m E) :
    MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n) := by
  let _a0 := emptyMarkedBlowupSequenceData p I m E
  have hstall : ¬ MarkedBlowupSequenceData.IsStationaryAt hinv _a0 n := by
    intro hmem
    have hle : sInf {j : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv _a0 j} ≤ n :=
      sInf_le hmem
    exact absurd hle $ mpr_ not_le hn
  by_contra hstep
  exact hstall
    (mpr_ (MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv _a0 n) hstep)

theorem isStationaryAt_monomialStallIndex
    (hex : ∃ n : ℕ, MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n) :
    MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) $ monomialStallIndex hinv p I m E := by
  exact sInf_mem hex

theorem monomialBlowupSeq_eq_monomialBlowupIterate :
    monomialBlowupSeq hinv p I m E =
      MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
        (monomialStallIndex hinv p I m E) :=
  rfl

theorem monomialBlowupSeq_schemeAt (n : ℕ)
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).obj n =
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).obj
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length := by
  let _m1 := emptyMarkedBlowupSequenceData p I m E
  let _a0 := p22 hinv _m1 n
  have hlen : _a0.length = n := by
    have h := monomialBlowupIterate_length hinv _m1 n
      (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j $ lt_of_lt_of_le hj hn)
    rwa [emptyMarkedBlowupSequenceData_length, zero_add] at h
  rw [hlen]
  let _m0 := monomialStallIndex hinv p I m E - n
  have hsplit : monomialStallIndex hinv p I m E = n + _m0 := by
    omega
  rw [monomialBlowupSeq_eq_monomialBlowupIterate, hsplit, monomialBlowupIterate_add hinv _m1 n
    _m0]
  exact an2 (monomialBlowupIterate_length_le_and_schemeAt_eq hinv
    _a0
    _m0) n $ le_of_eq hlen.symm

theorem monomialBlowupSeq_length :
    (monomialBlowupSeq hinv p I m E).length = monomialStallIndex hinv p I m E := by
  have h := monomialBlowupIterate_length hinv (emptyMarkedBlowupSequenceData p I m E)
    (monomialStallIndex hinv p I m E)
    (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j hj)
  rw [monomialBlowupSeq_eq_monomialBlowupIterate, h, emptyMarkedBlowupSequenceData_length, zero_add]
end

end

section
variable {Y : Sch} (q : Y = Y)
theorem comap_eqToHom_self__b1 (Z : ISD Y) :
    Z.comap (eqToHom q) = Z := by
  simp

theorem map_comap_eqToHom_self__b1 (L : Bdy Y) :
    List.map (fun D => D.comap $ eqToHom q) L = L :=by simp_all
end

section
variable {A B C : Sch} (hAB : A = B) (hBC : B = C) (hAC : A = C)
theorem comap_eqToHom_comp
    (D : ISD C) :
    (D.comap $ eqToHom hBC).comap (eqToHom hAB) = D.comap (eqToHom hAC) := by
  cases hAB
  cases hBC
  simp

private theorem map_comap_eqToHom_comp (L : Bdy C) :
    List.map (fun D : ISD B => D.comap $ eqToHom hAB)
        (List.map (fun D : ISD C => D.comap $ eqToHom hBC) L)
      = List.map (fun D : ISD C => D.comap $ eqToHom hAC) L := by
  induction L with
  | nil => rfl
  | cons a l ih => simp [ih, comap_eqToHom_comp hAB hBC hAC]
end

section
variable {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X} (hinv : ComapIsoInvariance) (d : MarkedBlowupSequenceData p I m E)
section
variable (i : ℕ) (hi : i < d.length)
include hi
theorem monomialBlowupIterate_center_of_lt j :
    ∀ e : (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).obj i = d.obj i,
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv d j).center i = (d.center i).comap (eqToHom e) := by
  induction j with
  | zero =>
      intro e
      exact sy_ $ comap_eqToHom_self__b1 e $ d.center i
  | succ j ih =>
      intro e
      let _a0 := monomialBlowupIterate_length_le_and_schemeAt_eq hinv d j
      have e2 :=
        right _a0 i $ le_of_lt hi
      have hij :=
        lt_of_lt_of_le hi _a0.1
      let _a1 := p22 hinv d j
      have e1 :=
        blowupAtCenter_schemeAt_of_le hinv _a1 i $ le_of_lt hij
      have _i7 : (p41 hinv _a1).center i = cmI (_a1.center i) (eqToHom e1) := by
        by_cases h : MarkedBlowupSequenceData.IsAdmissibleCenter _a1
        have key : ∀ D : MarkedBlowupSequenceData p I m E,
            D = _a1.append (MarkedBlowupSequenceData.monomialBlowupStep _a1 h) hinv →
            ∀ eD, D.center i = cmI (_a1.center i) (eqToHom eD) := by
          rintro D rfl eD
          exact m32
            (rfl) $ appendToBlowupSequenceData_center_of_lt_length _a1 (MarkedBlowupSequenceData.monomialBlowupStep _a1 h) hij
        exact key (p41 hinv _a1)
          (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv _a1 h) e1
        have hs : MarkedBlowupSequenceData.blowupAtCenter hinv _a1 = _a1 := by
          unfold MarkedBlowupSequenceData.blowupAtCenter
          rw [dif_neg h]
        have key : ∀ D : MarkedBlowupSequenceData p I m E, D = _a1 →
            ∀ eD, D.center i = cmI (_a1.center i) (eqToHom eD) := by
          rintro D rfl eD
          exact sy_ $ comap_eqToHom_self__b1 eD _
        exact key (p41 hinv _a1) hs e1
      refine m32
        _i7 ?_
      rw [ih e2]
      exact comap_eqToHom_comp e1 e2 e $ d.center i
end

theorem blowupAtCenter_center_of_eq_length (h : MarkedBlowupSequenceData.IsAdmissibleCenter d) i (hi : i = d.length)
    e :
    (MarkedBlowupSequenceData.blowupAtCenter hinv d).center i =
      (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom e) := by
  let _c0 := MarkedBlowupSequenceData.monomialBlowupStep d h
  subst hi
  have key : ∀ D : MarkedBlowupSequenceData p I m E,
      D = d.append _c0 hinv →
      ∀ eD,
        D.center d.length = cmI (MarkedBlowupSequenceData.centerAtLast d) (eqToHom eD) := by
    rintro D rfl eD
    have hc :=
      appendToBlowupSequenceData_schemeAt_of_le_length d _c0 (le_refl d.length)
    let _a0 := MarkedBlowupSequenceData.monomialBlowupStep_schemeAt_zero d h
    have e3 :=
      hc.trans _a0.symm
    have s2 : cmI (cmI (_c0.center 0)
            _c0.isoZero.inv) (eqToHom hc)
        = cmI (cmI (_c0.center 0)
            (eqToHom _a0.symm)) (eqToHom hc) := by
      rw [MarkedBlowupSequenceData.monomialBlowupStep_isoObjZero_inv]
    have s4 : cmI (_c0.center 0) (eqToHom e3)
        = cmI (MarkedBlowupSequenceData.centerAtLast d) (eqToHom eD) := by
      rw [MarkedBlowupSequenceData.monomialBlowupStep_center_zero]
      rfl
    exact tr_ (appendToBlowupSequenceData_center_length d _c0) (tr_ s2 (tr_ (comap_eqToHom_comp hc _a0.symm e3 (_c0.center 0)) s4))
  exact key (p41 hinv d)
    (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv d h) e

theorem center_monomialBlowupIterate_blowupAtCenter_eq n (hlen : d.length = n)
    (h : MarkedBlowupSequenceData.IsAdmissibleCenter d) r (D : MarkedBlowupSequenceData p I m E)
    (hD : D = MarkedBlowupSequenceData.monomialBlowupIterate hinv (MarkedBlowupSequenceData.blowupAtCenter hinv d) r)
    eD :
    D.center n = (MarkedBlowupSequenceData.centerAtLast d).comap (eqToHom eD) := by
  subst hD
  let _a0 := p41 hinv d
  have hl1 : _a0.length = n + 1 := by
    rw [MarkedBlowupSequenceData.blowupAtCenter_length hinv d h, hlen]
  have hn1 : n < _a0.length := by omega
  have e1 :=
    right (monomialBlowupIterate_length_le_and_schemeAt_eq hinv _a0 r) n
      (le_of_lt hn1)
  have ejunc :=
    (blowupAtCenter_schemeAt_of_le hinv d n $ le_of_eq hlen.symm).trans $ congrArg d.obj hlen.symm
  rw [monomialBlowupIterate_center_of_lt hinv _a0 n hn1 r e1,
    blowupAtCenter_center_of_eq_length hinv d h n hlen.symm ejunc]
  exact comap_eqToHom_comp e1 ejunc eD $ MarkedBlowupSequenceData.centerAtLast d
end

section
variable (hinv : ComapIsoInvariance)
theorem monomialBlowupIterate_boundary_of_le
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
    (s : MarkedBlowupSequenceData p I m E) (i : ℕ) (hi : i ≤ s.length) (d : ℕ) :
    (∀ j < d, MarkedBlowupSequenceData.IsAdmissibleCenter $ MarkedBlowupSequenceData.monomialBlowupIterate hinv s j) →
      ∀ ho : (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).obj i = s.obj i,
        (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).boundary i =
          List.map (fun D => D.comap $ eqToHom ho) (s.boundary i) := by
  induction d with
  | zero =>
      intro _ ho
      exact sy_ $ map_comap_eqToHom_self__b1 ho $ s.boundary i
  | succ d ih =>
      intro hstep ho
      have h2 :=
        hstep d $ lt_succ_self d
      have hlen :=
        monomialBlowupIterate_length hinv s d fun j hj => hstep j $ lt_succ_of_lt hj
      have hi' : i ≤ (MarkedBlowupSequenceData.monomialBlowupIterate hinv s d).length := by omega
      have hobj1 :=
        blowupAtCenter_schemeAt_of_le hinv (p22 hinv s d) i hi'
      have hobj2 :=
        m32 hobj1.symm ho
      have hstep1 := by
        let s := p22 hinv s d
        let h := h2
        let ho := hobj1
        let _a1 := MarkedBlowupSequenceData.monomialBlowupStep s h
        have key : ∀ d : MarkedBlowupSequenceData p I m E,
            d = s.append _a1 hinv →
            ∀ ho',
              d.boundary i = m39 (cmI · $ eqToHom ho') (s.boundary i) := by
          rintro d rfl ho'
          exact m32
            (MarkedBlowupSequenceData.append_boundary s _a1 hinv i) $ appendBoundary_of_le_length s _a1 hi'
        exact key (p41 hinv s)
          (MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv s h) ho
      exact m32 hstep1
        (m32 (congrArg (m39 (cmI · $ eqToHom hobj1)) $ ih (fun j hj => hstep j $ lt_succ_of_lt hj) hobj2)
          (map_comap_eqToHom_comp hobj1 hobj2 ho $ s.boundary i))

section
variable (p : X ⟶ Sp k) (I : ISD X) (m : ℕ) (E : Bdy X) (n : ℕ)
theorem monomialBlowupSeq_boundary
    (hn : n ≤ monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).boundary n =
      List.map (fun D => D.comap (eqToHom (monomialBlowupSeq_schemeAt hinv p I m E n hn)))
        ((MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).boundary
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n).length) := by
  let _a0 := emptyMarkedBlowupSequenceData p I m E
  let _c0 := MarkedBlowupSequenceData.monomialBlowupIterate hinv _a0 n
  let _c1 := monomialStallIndex hinv p I m E - n
  have hsteps0 :=
    fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j $ lt_of_lt_of_le hj hn
  have hlen : _c0.length = n := by
    rw [monomialBlowupIterate_length hinv _a0 n hsteps0,
      emptyMarkedBlowupSequenceData_length, zero_add]
  have h1 : n + _c1 = monomialStallIndex hinv p I m E := by omega
  let _a1 := monomialBlowupSeq hinv p I m E
  have hseq := by
    have h2 :=
      monomialBlowupIterate_add hinv _a0 n _c1
    rw [h1] at h2
    exact Eq.trans (monomialBlowupSeq_eq_monomialBlowupIterate hinv p I m E) h2
  have hstepsn : ∀ j < monomialStallIndex hinv p I m E - n, MarkedBlowupSequenceData.IsAdmissibleCenter
      (MarkedBlowupSequenceData.monomialBlowupIterate hinv
        _c0 j) := by
    intro j hj
    rw [(monomialBlowupIterate_add hinv _a0 n j).symm]
    exact isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E (n + j) (by omega)
  have key : ∀ d : MarkedBlowupSequenceData p I m E,
      d = MarkedBlowupSequenceData.monomialBlowupIterate hinv
            _c0
            _c1 →
      ∀ ho,
        d.boundary n = List.map (cmI · $ eqToHom ho)
          (_c0.boundary n) := by
    rintro d rfl ho
    exact monomialBlowupIterate_boundary_of_le hinv
      _c0 n (by omega)
      _c1 hstepsn ho
  exact boundary_eq_map_comap_of_index_eq _a1
    _c0 n
    _c0.length hlen
    (key _a1 hseq) (monomialBlowupSeq_schemeAt hinv p I m E n hn)

theorem monomialBlowupSeq_center
    (hn : n < monomialStallIndex hinv p I m E) :
    (monomialBlowupSeq hinv p I m E).center n =
      (MarkedBlowupSequenceData.centerAtLast
          (MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E) n)).comap
        (eqToHom $ monomialBlowupSeq_schemeAt hinv p I m E n $ Nat.le_of_lt hn) := by
  let _a0 := n + 1
  let _c0 := monomialStallIndex hinv p I m E - _a0
  let _c1 := emptyMarkedBlowupSequenceData p I m E
  let _a1 := MarkedBlowupSequenceData.monomialBlowupIterate hinv _c1 n
  have hlen : _a1.length = n := by
    have h := monomialBlowupIterate_length hinv _c1 n
      (fun j hj => isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E j $ lt_trans hj hn)
    rwa [emptyMarkedBlowupSequenceData_length, zero_add] at h
  have hsplit : monomialStallIndex hinv p I m E
      = _a0 + _c0 := by
    omega
  have h1 : MarkedBlowupSequenceData.monomialBlowupIterate hinv _c1
        (monomialStallIndex hinv p I m E)
      = MarkedBlowupSequenceData.monomialBlowupIterate hinv _c1
          (_a0 + _c0) := by
    rw [← hsplit]
  refine center_monomialBlowupIterate_blowupAtCenter_eq hinv
    _a1 n
    hlen (isAdmissibleCenter_of_lt_monomialStallIndex hinv p I m E n hn) _c0 (monomialBlowupSeq hinv p I m E) ?_
    (monomialBlowupSeq_schemeAt hinv p I m E n $ Nat.le_of_lt hn)
  rw [monomialBlowupSeq_eq_monomialBlowupIterate, h1,
    monomialBlowupIterate_add hinv _c1 (n + 1)
      _c0,
    monomialBlowupIterate_succ]
end
end

end

namespace MarkedBlowupSequenceData

section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (hinv : ComapIsoInvariance) (s : MarkedBlowupSequenceData p I m E)
def monomialStallIndex : ℕ :=
  sInf {n : ℕ | IsStationaryAt hinv s n}


theorem monomialStallIndex_eq_zero_of_not_isAdmissibleCenter (h : ¬ IsAdmissibleCenter s) : monomialStallIndex hinv s = 0 := by
  exact mp_ le_zero $ sInf_le $ mpr_ (isStationaryAt_iff_not_isAdmissibleCenter hinv s 0) h
end

end

end MarkedBlowupSequenceData


end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution


section

variable {B A : Type} [CommRing B] [CommRing A]

section
variable (f g : B →+* A) (J : Ideal A)
def eqModIdealSet : Set B := {b | f b - g b ∈ J}

section
variable {x y} (hx : x ∈ eqModIdealSet f g J) (hy : y ∈ eqModIdealSet f g J)
include hx hy
theorem add_mem_eqModIdealSet : x + y ∈ eqModIdealSet f g J := by
  show f (x + y) - g (x + y) ∈ J
  rw [map_add, map_add]
  have hrw : f x + f y - (g x + g y) = (f x - g x) + (f y - g y) := by ring
  rw [hrw]
  exact J.add_mem hx hy

theorem mul_mem_eqModIdealSet : x * y ∈ eqModIdealSet f g J := by
  show f (x * y) - g (x * y) ∈ J
  rw [map_mul, map_mul]
  have hrw : f x * f y - g x * g y = f x * (f y - g y) + (f x - g x) * g y := by ring
  rw [hrw]
  exact J.add_mem (J.mul_mem_left _ hy) $ J.mul_mem_right _ hx
end

theorem neg_mem_eqModIdealSet {x}
    (hx : x ∈ eqModIdealSet f g J) : -x ∈ eqModIdealSet f g J := by
  show f (-x) - g (-x) ∈ J
  rw [map_neg, map_neg]
  have hrw : -f x - -g x = -(f x - g x) := by ring
  rw [hrw]
  exact J.neg_mem hx

def eqModIdealSubring : Subring B where
  carrier := eqModIdealSet f g J
  one_mem' := by
    show f 1 - g 1 ∈ J
    rw [map_one, map_one, sub_self]
    exact J.zero_mem
  zero_mem' := by
    show f 0 - g 0 ∈ J
    rw [map_zero, map_zero, sub_self]
    exact J.zero_mem
  add_mem' := add_mem_eqModIdealSet f g J
  neg_mem' := neg_mem_eqModIdealSet f g J
  mul_mem' := mul_mem_eqModIdealSet f g J

theorem sub_mem_ideal_of_subring_closure_eq_top (S : Set B)
    (hS : Subring.closure S = ⊤) (hmem : ∀ b ∈ S, f b - g b ∈ J) (b : B) :
    f b - g b ∈ J := by
  have hsub : Subring.closure S ≤ eqModIdealSubring f g J :=
    Subring.closure_le.mpr fun x hx => hmem x hx
  rw [hS] at hsub
  exact hsub $ Subring.mem_top b
end

end

section
variable {M : Type}

theorem localization_mk_eq_mk_one_of_eq_mul [CommMonoid M] {S : Submonoid M}
    (x y d : M) (hd : d ∈ S) (h : x = d * y) :
    mk x ⟨d, hd⟩ = mk y (1 : ↥S) := by
  rw [mk_eq_mk_iff]
  refine r_of_eq ?_
  simp [h]
end

section

variable {R : Type} [CommRing R]

section
variable (I : Ideal R) (a : I)
private theorem val_chartRingHom (t : R) :
    val (chartRingHom I a t)
      = mk (↑(reesDegreeZeroEquiv I t) : ↥(reesAlgebra I))
          (1 : ↥(powers $ reesGenerator I a)) := by
  rw [chartRingHom_apply]
  rfl

theorem exists_pow_mul_eq
    (z : Away (reesGrading I) $ reesGenerator I a) :
    ∃ n r, r ∈ I ^ n ∧
      z * chartRingHom I a (a : R) ^ n = chartRingHom I a r := by
  let _a0 := reesAlgebra I
  obtain ⟨m, hm⟩ := den_mem z
  have hden := sy_ hm
  have hdencoe : ((den z : _a0) : Polynomial R)
      = monomial m ((a : R) ^ m) := by simp_all
  have hpow :=
    map_pow (p51 I a) (a : R) m
  by_cases hdeg : deg z = m
  have hnum : num z ∈ reesGrading I m := by
    rw [← hdeg]
    exact num_mem_deg z
  obtain ⟨s, hs, hseq⟩ :=
    mp (mem_reesGrading_iff_monomial I m $ num z) hnum
  refine ⟨m, s, hs, ?_⟩
  have key : (num z)
        * ((reesDegreeZeroEquiv I $ a ^ m) : _a0)
      = (den z) * ((reesDegreeZeroEquiv I s) : _a0) := by
    apply m26
    simp only [MulMemClass.coe_mul, hseq, hdencoe, reesDegreeZeroEquiv_coe_coe]
    rw [mul_comm (monomial m s) $ m141 $ (a : R) ^ m,
      C_mul_monomial,
      mul_comm (monomial m $ (a : R) ^ m) $ m141 s,
      C_mul_monomial, mul_comm ((a : R) ^ m) s]
  rw [← hpow]
  apply val_injective $ powers $ p35 I a
  rw [val_mul, val_chartRingHom, val_chartRingHom,
    eq_num_div_den z, mk_mul, mul_one]
  exact localization_mk_eq_mk_one_of_eq_mul _ _ _ _ key
  have hzero := by
    have h1 := mp_ (mem_reesGrading_iff_coeff I (deg z)
      (den z)) (den_mem_deg z) m
      (fun h => hdeg h.symm)
    rw [hdencoe] at h1
    simpa using h1
  refine ⟨m, 0, m216 _, ?_⟩
  rw [← hpow, hzero, map_zero]
  exact mul_zero z

theorem exists_mem_closure_chartRingHom_eq_mul_pow (n : ℕ) :
    ∀ r ∈ I ^ n, ∃ w ∈ Subring.closure
        (range ⇑(chartRingHom I a) ∪ range (chartFraction I a)),
      chartRingHom I a r = w * chartRingHom I a (a : R) ^ n := by
  induction n with
  | zero =>
    intro r _
    refine ⟨p51 I a r, Subring.subset_closure $ m51 ⟨r, rfl⟩, ?_⟩
    ring
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine mul_induction_on hr ?_ ?_
    intro s hs b hb
    obtain ⟨w, hw, hweq⟩ := ih s hs
    refine ⟨w * chartFraction I a ⟨b, hb⟩,
      Subring.mul_mem _ hw $ Subring.subset_closure $ m61 ⟨⟨b, hb⟩, rfl⟩, ?_⟩
    rw [map_mul, hweq, chartRingHom_coe_eq_chartFraction_mul I a ⟨b, hb⟩]
    ring
    rintro x y ⟨wx, hwx, hx⟩ ⟨wy, hwy, hy⟩
    refine ⟨wx + wy, Subring.add_mem _ hwx hwy, ?_⟩
    rw [map_add, hx, hy]
    ring

theorem closure_chartRingHom_union_chartFraction_eq_top :
    Subring.closure
        (range ⇑(chartRingHom I a) ∪ range (chartFraction I a)) = ⊤ := by
  rw [Subring.eq_top_iff']
  intro z
  obtain ⟨n, r, hr, hz⟩ := exists_pow_mul_eq I a z
  obtain ⟨w, hw, hweq⟩ := exists_mem_closure_chartRingHom_eq_mul_pow I a n r hr
  let _a0 := p51 I a a ^ n
  have e1 : (z - w) * _a0
      = z * _a0 - w * _a0 :=
    sub_mul z w _
  have h0 : (z - w) * _a0 = 0 := by
    rw [e1, hz, ← hweq]
    ring
  have hzw : z - w = 0 := an2 (mp_ mem_nonZeroDivisors_iff $ pow_mem (chartRingHom_mem_nonZeroDivisors I a) n) _ h0
  have hzeq : z = w := mp_ sub_eq_zero hzw
  rwa [hzeq]
end

theorem chartFraction_sub_mem_of_congr {A : Type} [CommRing A] (I : Ideal R) (a : I)
    (ph_ ph' : Away (reesGrading I) (reesGenerator I a) →+* A)
    (σ σ' : R →+* A) (bf_ : Ideal A)
    (hph : ∀ r : R, ph_ (chartRingHom I a r) = σ r)
    (hph' : ∀ r : R, ph' (chartRingHom I a r) = σ' r)
    (hcongr : ∀ r : R, σ r - σ' r ∈ span {σ (a : R)} * bf_)
    (hnzd : σ (a : R) ∈ nonZeroDivisors A)
    (u : A) (hu : σ' (a : R) = u * σ (a : R)) (b : I) :
    ph_ (chartFraction I a b) - ph' (chartFraction I a b) ∈ bf_ := by
  let _c0 := chartFraction I a b
  obtain ⟨c, hc, hcEq⟩ := mp_ mem_span_singleton_mul $ hcongr (a : R)
  obtain ⟨d, hd, hdEq⟩ := mp_ mem_span_singleton_mul $ hcongr (b : R)
  let _a0 := (1 : A)
  have hone : _a0 - u ∈ bf_ := by
    have h1 := sy_ hcEq
    rw [hu] at h1
    have h0 : (_a0 - u - c) * σ (a : R) = 0 := by linear_combination h1
    have h2 := an2 (mp_ mem_nonZeroDivisors_iff hnzd) _ h0
    have h3 : _a0 - u = c := by linear_combination h2
    rwa [h3]
  have hb1 : σ (b : R) = ph_ _c0 * σ (a : R) := by
    rw [← hph (b : R), ← hph (a : R), ← map_mul, chartRingHom_coe_eq_chartFraction_mul I a b]
  have hb2 : σ' (b : R) = ph' _c0 * σ' (a : R) := by
    rw [← hph' (b : R), ← hph' (a : R), ← map_mul, chartRingHom_coe_eq_chartFraction_mul I a b]
  have h2 := sy_ hdEq
  rw [hb1, hb2, hu] at h2
  have h0 : (ph_ _c0 - u * ph' _c0 - d) * σ (a : R) = 0 := by
    linear_combination h2
  have hfin : ph_ _c0 - ph' _c0
      = d - (1 - u) * ph' _c0 := by linear_combination (an2 (mp_ mem_nonZeroDivisors_iff hnzd) _ h0)
  rw [hfin]
  exact bf_.sub_mem hd $ bf_.mul_mem_right _ hone

end

section

variable {R : Type} [CommRing R]

theorem sectionsRingHom_comp {A : Type} [CommRing A] {Z W : Sch} (p : Z ⟶ W)
    (rh_ : W ⟶ Sp A) (V : Opn W) (V' : Opn Z)
    (hle : V' ≤ (Opens.map p.base).obj V) (r : A) :
    sectionsRingHom (p ≫ rh_) V' r
      = (CommRingCat.Hom.hom $ Scheme.Hom.appLE p V V' hle) (sectionsRingHom rh_ V r) := by
  rw [sectionsRingHom_apply, sectionsRingHom_apply]
  conv_rhs => rw [← m78, m91]

section
variable {W : Sch} (af_ : ISD W) (V : W.affineOpens)
theorem mem_ideal_of_app_subschemeio_eq_zero
    (x : ↥(W.presheaf.obj $ Opposite.op (V : Opn W)))
    (hx : (CommRingCat.Hom.hom $ app af_.si (V : Opn W)) x = 0) :
    x ∈ af_.ideal V := by
  rw [subschemeι_app af_ V, comp_apply] at hx
  have h2 := congrArg (m4 (af_.subschemeObjIso V).hom) hx
  rw [← comp_apply, m114] at h2
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h2

theorem app_subschemeio_eq_zero_of_mem_ideal {x : ↥(W.presheaf.obj (Opposite.op (V : Opn W)))}
    (hx : x ∈ af_.ideal V) :
    (CommRingCat.Hom.hom $ app af_.si (V : Opn W)) x = 0 := by
  rw [subschemeι_app af_ V, comp_apply]
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
end

theorem appLE_top_top {X Y : Sch} (f : X ⟶ Y)
    e :
    appLE f ⊤ ⊤ e = appTop f :=
  appLE_eq_app (f := f)

private theorem appLE_congr_hom {X Y : Sch} {f g : X ⟶ Y} (hfg : f = g)
    U V e
    e' :
    appLE f U V e = appLE g U V e' := by
  subst hfg
  rfl

theorem sectionsRingHom_sub_mem_ideal {A : Type} [CommRing A] {W : Sch}
    (rh_ rh' : W ⟶ Sp A) (af_ : ISD W)
    (hagree : subschemeι af_ ≫ rh_ = subschemeι af_ ≫ rh')
    (V : W.affineOpens) (r : A) :
    sectionsRingHom rh_ (V : Opn W) r - sectionsRingHom rh' (V : Opn W) r ∈ af_.ideal V := by
  apply mem_ideal_of_app_subschemeio_eq_zero
  let _a0 := (m54 af_.subschemeι.base).obj V
  have h1 : p47 (siI af_ ≫ rh_)
        _a0 r
      = p47 (siI af_ ≫ rh')
        _a0 r := by
    rw [hagree]
  rw [sectionsRingHom_comp af_.si rh_ V _ le_rfl r,
    sectionsRingHom_comp af_.si rh' V _ le_rfl r] at h1
  rw [app_eq_appLE, map_sub, h1]
  exact sub_self _

section
variable (I : Ideal R) {W : Sch}
theorem appTop_lift_affineBlowupChart_apply (k : W ⟶ affineBlowup I) (a : I)
    {T : Sch} (p : T ⟶ W) (V : Opn W)
    (hk : V ≤ (Opens.map k.base).obj
      ((opensFunctor $ affineBlowupChart I a).obj ⊤))
    (hps_ : (⊤ : Opn T) ≤ (Opens.map p.base).obj V)
    (hrange : range ⇑(p ≫ k).base ⊆ range ⇑(affineBlowupChart I a).base)
    (z : Away (reesGrading I) $ reesGenerator I a) :
    (CommRingCat.Hom.hom $ appTop
        (lift (affineBlowupChart I a) (p ≫ k) hrange))
      ((CommRingCat.Hom.hom (GSpecIso
        (CommRingCat.of (Away (reesGrading I) $ reesGenerator I a))).inv) z)
      = (CommRingCat.Hom.hom $ appLE p V ⊤ hps_)
          (chartSectionsRingHom I k a V hk z) := by
  let _c0 := affineBlowupChart I a
  let _m0 := m10 $ Away (reesGrading I) $ p35 I a
  have hchartle : (⊤ : Opn $ Spec _m0)
      ≤ (m54 _c0.base).obj
        ((opensFunctor _c0).obj ⊤) :=
    fun x _ => ⟨x, trivial, rfl⟩
  have hsec : (m4 $ Scheme.Hom.appLE _c0
        ((Scheme.Hom.opensFunctor _c0).obj ⊤) ⊤ hchartle)
        ((m4 (chartSectionsIso I a).hom) z)
      = (m4 (Scheme.GSpecIso _m0).inv) z := by
    rw [chartSectionsIso_hom_apply, ← comp_apply,
      show appLE _c0
          ((opensFunctor _c0).obj ⊤) ⊤ hchartle
        = isoH (appIso _c0 ⊤) from
          sy_ $ appIso_hom' _c0 ⊤,
      m114, CommRingCat.id_apply]
  let _a5 := p ≫ k
  let _a2 := lift _c0 _a5 hrange
  have etop : (⊤)
      ≤ (m54 _a2.base).obj ⊤ := by
    simp
  have hmain : appLE _c0
        ((opensFunctor _c0).obj ⊤) ⊤ hchartle
        ≫ Scheme.Hom.appLE _a2 ⊤ ⊤ etop
      = Scheme.Hom.appLE k ((Scheme.Hom.opensFunctor _c0).obj ⊤) V hk
        ≫ Scheme.Hom.appLE p V ⊤ hps_ := by
    rw [m91, m91]
    exact appLE_congr_hom (lift_fac _c0 _a5 hrange) _ _ _ _
  rw [appLE_top_top _ etop] at hmain
  have happ := congrArg (fun m =>
      (m4 m) $ (m4 (chartSectionsIso I a).hom) z) hmain
  simp at happ
  rwa [hsec, ← chartSectionsRingHom_apply] at happ

theorem comp_eq_of_chartSectionsRingHom_sub_mem
    (h h' : W ⟶ affineBlowup I) (a : I) (bf_ : ISD W) (V : W.affineOpens)
    (hV : (V : Opn W) ≤ (Opens.map h.base).obj
      ((opensFunctor $ affineBlowupChart I a).obj ⊤))
    (hV' : (V : Opn W) ≤ (Opens.map h'.base).obj
      ((opensFunctor $ affineBlowupChart I a).obj ⊤))
    (hcongr : ∀ z : Away (reesGrading I) $ reesGenerator I a,
      chartSectionsRingHom I h a (V : Opn W) hV z - chartSectionsRingHom I h' a (V : Opn W) hV' z
        ∈ bf_.ideal V) :
    Scheme.Opens.i ((Opens.map bf_.subschemeι.base).obj (V : Opn W)) ≫ subschemeι bf_ ≫ h
      = Scheme.Opens.i ((Opens.map bf_.subschemeι.base).obj (V : Opn W)) ≫ subschemeι bf_ ≫ h' := by
  let _a1 := m10 $ Away (reesGrading I) $ p35 I a
  rw [← assoc, ← assoc]
  let _m0 := (⊤ : (Scheme.Opens.toScheme $ (m54 bf_.subschemeι.base).obj V).Opens)
  have hps_ : _m0
      ≤ (m54 (p4 ((m54 bf_.subschemeι.base).obj V)
            ≫ siI bf_).base).obj V := by
    intro x _
    simp
  have hio : _m0
      ≤ (m54 (p4
          ((m54 bf_.subschemeι.base).obj V)).base).obj
        ((m54 bf_.subschemeι.base).obj V) := by
    intro x _
    simp
  let _a3 := affineBlowupChart I a
  have hrange : ∀ (k : W ⟶ affineBlowup I),
      V ≤ (m54 k.base).obj
        ((opensFunctor _a3).obj ⊤) →
      range ((p4 ((m54 bf_.subschemeι.base).obj V)
          ≫ siI bf_) ≫ k).base ⊆ range _a3.base := by
    intro k hk
    rintro y ⟨x, rfl⟩
    have h3 : bsM k (bf_.subschemeι.base x.1)
        ∈ opensRange _a3 := by
      rw [← image_top_eq_opensRange]
      exact hk x.2
    obtain ⟨q, hq⟩ := h3
    exact ⟨q, hq⟩
  have hkill : ∀ x ∈ bf_.ideal V,
      (m4 $ appLE
        (p4 ((m54 bf_.subschemeι.base).obj V) ≫ siI bf_)
        V ⊤ hps_) x = 0 := by
    intro x hx
    have hcomp : appLE bf_.si V
          ((m54 bf_.subschemeι.base).obj V) le_rfl
        ≫ appLE (p4
            ((m54 bf_.subschemeι.base).obj V))
            ((m54 bf_.subschemeι.base).obj V) ⊤ hio
        = appLE (p4
            ((m54 bf_.subschemeι.base).obj V) ≫ siI bf_)
            V ⊤ hps_ := by
      rw [appLE_comp_appLE]
    have h2 := congrArg (fun m => (m4 m) x) hcomp
    simp only [comp_apply] at h2
    rw [appLE_eq_app, app_subschemeio_eq_zero_of_mem_ideal bf_ V hx, map_zero] at h2
    exact sy_ h2
  let _a4 := hrange h hV
  let _a5 := hrange h' hV'
  have happ : appTop (lift _a3 _ _a4)
      = appTop (lift _a3 _ _a5) := by
    apply CommRingCat.hom_ext
    apply m48
    intro y
    let _s0 := GSpecIso _a1
    have hy : (m4 _s0.inv)
        ((m4 _s0.hom) y) = y := by
      rw [← comp_apply, m145, CommRingCat.id_apply]
    obtain ⟨z, rfl⟩ : ∃ z, (m4 _s0.inv) z = y :=
      ⟨_, hy⟩
    rw [appTop_lift_affineBlowupChart_apply I h a (p4 ((m54 bf_.subschemeι.base).obj V)
        ≫ siI bf_) V hV hps_ _a4 z,
      appTop_lift_affineBlowupChart_apply I h' a (p4 ((m54 bf_.subschemeι.base).obj V)
        ≫ siI bf_) V hV' hps_ _a5 z]
    have hz := hkill _ $ hcongr z
    rw [map_sub] at hz
    exact mp_ sub_eq_zero hz
  have hfin : lift _a3 _ _a4
      = lift _a3 _ _a5 := by
    have hcomp : lift _a3 _ _a4
          ≫ (Spec _a1).toSpecΓ
        = lift _a3 _ _a5
          ≫ (Spec _a1).toSpecΓ := by
      rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, happ]
    exact mp_ (cancel_mono _) hcomp
  rw [← lift_fac _a3 _ _a4,
    ← lift_fac _a3 _ _a5, hfin]

section
variable (h h' : W ⟶ affineBlowup I)
theorem chartSectionsRingHom_sub_mem (bf1 : ISD W) (a : I) (V : W.affineOpens)
    (hV : (V : Opn W) ≤ (Opens.map h.base).obj
      ((opensFunctor (affineBlowupChart I a)).obj ⊤))
    (hV' : (V : Opn W) ≤ (Opens.map h'.base).obj
      ((opensFunctor (affineBlowupChart I a)).obj ⊤))
    (hnzd : sectionsRingHom (h ≫ toSpec I) (V : Opn W) (a : R)
      ∈ nonZeroDivisors ↥(W.presheaf.obj (Opposite.op (V : Opn W))))
    (u : ↥(W.presheaf.obj (Opposite.op (V : Opn W))))
    (hu : sectionsRingHom (h' ≫ toSpec I) (V : Opn W) (a : R)
      = u * sectionsRingHom (h ≫ toSpec I) (V : Opn W) (a : R))
    (hcongr : ∀ r : R, sectionsRingHom (h ≫ toSpec I) (V : Opn W) r
        - sectionsRingHom (h' ≫ toSpec I) (V : Opn W) r
      ∈ span {sectionsRingHom (h ≫ toSpec I) (V : Opn W) (a : R)}
          * bf1.ideal V)
    (z : Away (reesGrading I) (reesGenerator I a)) :
    chartSectionsRingHom I h a (V : Opn W) hV z - chartSectionsRingHom I h' a (V : Opn W) hV' z
      ∈ bf1.ideal V := by
  let _a0 := chartSectionsRingHom I h a V hV
  let _a1 := chartSectionsRingHom I h' a V hV'
  refine sub_mem_ideal_of_subring_closure_eq_top _a0
    _a1 (bf1.ideal V)
    (range (p51 I a) ∪ range (chartFraction I a))
    (closure_chartRingHom_union_chartFraction_eq_top I a) ?_ z
  rintro b (⟨r, rfl⟩ | ⟨b0, rfl⟩)
  rw [chartSectionsRingHom_chartRingHom, chartSectionsRingHom_chartRingHom]
  exact an2 (mp_ mem_inf (Ideal.mul_le_inf (hcongr r)))
  exact chartFraction_sub_mem_of_congr I a _a0
    _a1
    (p47 (h ≫ p13 I) V)
    (p47 (h' ≫ p13 I) V) (bf1.ideal V)
    (chartSectionsRingHom_chartRingHom I h a V hV)
    (chartSectionsRingHom_chartRingHom I h' a V hV')
    hcongr hnzd u hu b0

theorem exists_common_chart_affineOpen (af_ bf1 : ISD W)
    (hagree : subschemeι af_ ≫ (h ≫ toSpec I)
      = subschemeι af_ ≫ (h' ≫ toSpec I))
    (hpull : (specIdealSheaf I).comap (h ≫ toSpec I)
      = (specIdealSheaf I).comap (h' ≫ toSpec I))
    (hcart : IsLocallyGeneratedByNonZeroDivisor $ (specIdealSheaf I).comap $ h ≫ toSpec I)
    (hfac : (specIdealSheaf I).comap (h ≫ toSpec I) * bf1 = af_)
    (w : ↥W) :
    ∃ (a : I) (V V' : W.affineOpens),
      w ∈ (V : Opn W) ∧
      (Opens.map bf1.subschemeι.base).obj (V' : Opn W)
        = (Opens.map bf1.subschemeι.base).obj (V : Opn W) ∧
      (V' : Opn W) ≤ (Opens.map h.base).obj
        ((opensFunctor $ affineBlowupChart I a).obj ⊤) ∧
      (V' : Opn W) ≤ (Opens.map h'.base).obj
        ((opensFunctor $ affineBlowupChart I a).obj ⊤) ∧
      sectionsRingHom (h ≫ toSpec I) (V' : Opn W) (a : R)
        ∈ nonZeroDivisors ↥(W.presheaf.obj $ Opposite.op (V' : Opn W)) ∧
      ((specIdealSheaf I).comap $ h ≫ toSpec I).ideal V'
        = Ideal.span {sectionsRingHom (h ≫ toSpec I) (V' : Opn W) (a : R)} := by
  obtain ⟨a, V, hwV, hVchart, hnzdV⟩ := exists_chart_affineOpen_mem_nonZeroDivisors I h hcart w
  have hspanV :=
    comap_specIdealSheaf_ideal_eq_span I h a V hVchart
  let _s0 := h ≫ p13 I
  let _a6 := h' ≫ p13 I
  have hsub := sectionsRingHom_sub_mem_ideal _s0
    _a6 af_ hagree V a
  let _a5 := specIdealSheaf I
  have hmul : (cmI _a5 _s0 * bf1).ideal V
      = (cmI _a5 _s0).ideal V * bf1.ideal V := rfl
  rw [← hfac, hmul, hspanV] at hsub
  let _a3 := pObj W $ m112 V
  obtain ⟨c, hc, hceq⟩ := mp_ mem_span_singleton_mul hsub
  set f : _a3 := 1 - c with hfdef
  have hf'' : p47 _a6 V a
      = p47 _s0 V a * f := by
    rw [hfdef]
    linear_combination hceq
  have hle := W.basicOpen_le f
  have haff := V.2.basicOpen f
  have hlechart := le_trans hle hVchart
  have hsp :=
    comap_specIdealSheaf_ideal_eq_span I h a ⟨bOpn W f, haff⟩ hlechart
  have hressg :=
    sectionsRingHom_restrict _s0 hle a
  have hressg' :=
    sectionsRingHom_restrict _a6 hle a
  have hloc :=
    V.2.isLocalization_basicOpen f
  let _a0 := pObj W $ m112 $ bOpn W f
  have hunit :=
    map_units
      (S := _a0)
      (M := powers f) ⟨f, mem_powers f⟩
  have hnzdres : algebraMap _a3
        _a0
        (p47 _s0 V a)
      ∈ nonZeroDivisors _a0 := by
    have hcomap := IsLocalization.nonZeroDivisors_le_comap (M := powers f)
      (S := _a0)
    exact hcomap hnzdV
  have hnzdfinal : p47 _s0 (bOpn W f) a
      ∈ nonZeroDivisors _a0 := by
    rwa [hressg]
  have hcart' : p17
      (_a5.comap _a6) := by
    rwa [← hpull]
  have hspanbo' : (_a5.comap _a6).ideal
        ⟨basicOpen W f, haff⟩
      = span {p47 _a6 (basicOpen W f) a} := by
    rw [← hpull, hsp, hressg, hressg', hf'', map_mul]
    exact sy_ $ span_singleton_mul_right_unit hunit _
  have hpre : (m54 bf1.subschemeι.base).obj (bOpn W f)
      = (m54 bf1.subschemeι.base).obj V := by
    rw [preimage_basicOpen]
    have happ : (m23
        (app bf1.si V)) f = 1 := by
      rw [hfdef, map_sub, map_one, app_subschemeio_eq_zero_of_mem_ideal bf1 V hc, sub_zero]
    rw [happ, basicOpen_one]
  refine ⟨a, V, ⟨bOpn W f, haff⟩, hwV, hpre, hlechart, ?_, hnzdfinal, hsp⟩
  intro x hx
  have hmemrange := mem_opensRange_affineBlowupChart_of_ideal_eq_span I h' hcart' x a
    ⟨⟨bOpn W f, haff⟩, hx, hspanbo'⟩
  rwa [← image_top_eq_opensRange] at hmemrange
end

theorem subschemeio_comp_eq_of_affineBlowup_lifts
    (rh_ rh' : W ⟶ Sp R) (af_ bf1 : ISD W)
    (h h' : W ⟶ affineBlowup I)
    (hagree : subschemeι af_ ≫ rh_ = subschemeι af_ ≫ rh')
    (hpull : (specIdealSheaf I).comap rh_ = (specIdealSheaf I).comap rh')
    (hcart : IsLocallyGeneratedByNonZeroDivisor $ (specIdealSheaf I).comap rh_)
    (hfac : (specIdealSheaf I).comap rh_ * bf1 = af_)
    (hh : h ≫ toSpec I = rh_)
    (hh' : h' ≫ toSpec I = rh') :
    subschemeι bf1 ≫ h = subschemeι bf1 ≫ h' := by
  subst hh
  subst hh'
  choose a V V' hw hpre hVh hVh' hn hs using
    exists_common_chart_affineOpen I h h' af_ bf1 hagree hpull hcart hfac
  let _a0 := m54 bf1.subschemeι.base
  have hcov : ∀ z : (subS bf1), ∃ (w : W)
      (y : (_a0.obj $ V w)),
      (p4 $ _a0.obj $ V w).base y = z := by
    intro z
    exact ⟨bf1.subschemeι.base z, ⟨z, hw $ bf1.subschemeι.base z⟩, rfl⟩
  refine hom_ext
    (mkOfCovers (W)
      (fun w => Scheme.Opens.toScheme
        (_a0.obj $ V w))
      (fun w => p4
        (_a0.obj $ V w)) hcov) _ _ ?_
  intro w
  show p4 (_a0.obj $ V w)
        ≫ (siI bf1 ≫ h)
      = p4 (_a0.obj $ V w)
        ≫ (siI bf1 ≫ h')
  rw [← hpre w]
  let a := a w
  let V := V' w
  let hV := hVh w
  let hV' := hVh' w
  let hspan := hs w
  let _a0 := h ≫ p13 I
  let _a1 := h' ≫ p13 I
  have hmem : p47 _a1 V a
      ∈ span {p47 _a0 V a} := by
    rw [← hspan, hpull, comap_specIdealSheaf_ideal_eq_span I h' a V hV']
    exact mem_span_singleton_self _
  obtain ⟨u, hu⟩ := mp_ mem_span_singleton' hmem
  refine comp_eq_of_chartSectionsRingHom_sub_mem I h h' a bf1 V hV hV' fun z => ?_
  refine chartSectionsRingHom_sub_mem I h h' bf1 a V hV hV' (hn w) u hu.symm (fun r => ?_) z
  have h1 := sectionsRingHom_sub_mem_ideal _a0 _a1 af_ hagree V r
  rw [← hfac] at h1
  rwa [← hspan]
end

end




private theorem comap_hom_comap_inv {X Y : Sch} (e : X ≅ Y) (I : ISD Y) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← comap_comp, e.inv_hom_id, comap_id]

theorem exists_subschemeio_base_eq {X : Sch} (I : ISD X) x
    (hx : x ∈ support I) : ∃ z, I.subschemeι.base z = x := by
  have hmem : x ∈ range I.si := by simp_all
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz⟩

private theorem exists_preimage_of_isPullback {X' X S : Sch} {g : X' ⟶ X} {s : S ⟶ X}
    {Q : Sch} {p : Q ⟶ S} {q : Q ⟶ X'} (h : IsPullback p q s g) (x : ↥S)
    (hx : s.base x ∈ range g.base) : ∃ y : ↥Q, p.base y = x := by
  have h1 : range p.base = range (fst s g).base := by
    rw [← h.isoPullback_hom_fst]
    let e := h.isoPullback
    apply m15
    rintro _ ⟨x, rfl⟩
    exact ⟨ihB_ e x, rfl⟩
    rintro _ ⟨y, rfl⟩
    refine ⟨ibM e y, ?_⟩
    dsimp
    rw [inv_hom_apply]
  obtain ⟨z, hz⟩ := by
    have h := Scheme.Pullback.range_fst s g
    rw [ext_iff] at h
    exact mpr_ (h x) hx
  have hmem : x ∈ range p.base := by
    rw [h1]
    exact ⟨z, hz⟩
  exact hmem

def BlowupLiftEqOnControlledTransform : Prop :=
  ∀ (X Y S T : Sch) (pi_ : Y ⟶ X) (Z : ISD X), IsBlowupAlongIdealSheaf pi_ Z →
    ∀ f g : S ⟶ X, Z.comap f = Z.comap g →
      ∀ rh_ : T ⟶ S, IsBlowupAlongIdealSheaf rh_ (Z.comap f) →
        ∀ f' g' : T ⟶ Y, f' ≫ pi_ = rh_ ≫ f → g' ≫ pi_ = rh_ ≫ g →
          ∀ a : ISD S, subschemeι a ≫ f = subschemeι a ≫ g →
            ∀ c : ISD T,
              exceptionalIdeal rh_ (Z.comap f) * c = a.comap rh_ →
              subschemeι c ≫ f' = subschemeι c ≫ g'

variable {V P : Sch}

structure BlowupSeqLevelIso (C : SequenceOfBlowups V) (B1_ B2_ : SequenceOfBlowups P) (L : ℕ)
    (sg1 : ∀ i : ℕ, i ≤ L → (schemeAt C i ⟶ schemeAt B1_ i))
    (sg2 : ∀ i : ℕ, i ≤ L → (schemeAt C i ⟶ schemeAt B2_ i))
    (a : ∀ i : ℕ, IdealSheafData $ schemeAt C i) (i : ℕ) where
  iso : schemeAt B1_ i ≅ schemeAt B2_ i
  compat : ∀ hi : i ≤ L,
    subschemeι (a i) ≫ sg1 i hi = subschemeι (a i) ≫ sg2 i hi ≫ inv iso

structure BlowupSeqComparison (f g : V ⟶ P) (C : SequenceOfBlowups V) (B1_ B2_ : SequenceOfBlowups P) (L : ℕ)
    (sg1 : ∀ i : ℕ, i ≤ L → (schemeAt C i ⟶ schemeAt B1_ i))
    (sg2 : ∀ i : ℕ, i ≤ L → (schemeAt C i ⟶ schemeAt B2_ i))
    (a : ∀ i : ℕ, IdealSheafData $ schemeAt C i) : Prop where
  zero_ideal :
    subschemeι (a 0) ≫ C.isoZero.hom ≫ f = subschemeι (a 0) ≫ C.isoZero.hom ≫ g
  isBlowup_B1 : ∀ i : ℕ, i < L → IsBlowupAlongIdealSheaf (transitionMapSucc B1_ i) (center B1_ i)
  isBlowup_B2 : ∀ i : ℕ, i < L → IsBlowupAlongIdealSheaf (transitionMapSucc B2_ i) (center B2_ i)
  isBlowup_C : ∀ i : ℕ, i < L → IsBlowupAlongIdealSheaf (transitionMapSucc C i) (center C i)
  ideal_succ : ∀ i : ℕ, i < L →
    exceptionalIdeal (transitionMapSucc C i) (center C i) * a (i + 1) = (a i).comap (transitionMapSucc C i)
  ideal_le_center : ∀ i : ℕ, i < L → a i ≤ center C i
  center_C1 : ∀ i : ℕ, ∀ hi : i < L, center C i = (center B1_ i).comap (sg1 i hi.le)
  center_C2 : ∀ i : ℕ, ∀ hi : i < L, center C i = (center B2_ i).comap (sg2 i hi.le)
  cover1 : ∀ i : ℕ, i < L → ∀ x ∈ support (center B1_ i),
    (projectionToBase B1_ i).base x ∈ range f.base
  cover2 : ∀ i : ℕ, i < L → ∀ x ∈ support (center B2_ i),
    (projectionToBase B2_ i).base x ∈ range g.base
  lifting : BlowupLiftEqOnControlledTransform
  determined1 : ∀ i : ℕ, i < L → ∀ J : IdealSheafData $ schemeAt B1_ i,
    support (center B1_ i) ≤ support J → J ≤ center B1_ i
  determined2 : ∀ i : ℕ, i < L → ∀ J : IdealSheafData $ schemeAt B2_ i,
    support (center B2_ i) ≤ support J → J ≤ center B2_ i
  pullback1 : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (sg1 (i + 1) hi) (transitionMapSucc C i) (transitionMapSucc B1_ i) $ sg1 i hi.le
  pullback2 : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (sg2 (i + 1) hi) (transitionMapSucc C i) (transitionMapSucc B2_ i) $ sg2 i hi.le
  zero1 : sg1 0 (zero_le _) ≫ B1_.isoZero.hom = C.isoZero.hom ≫ f
  zero2 : sg2 0 (zero_le _) ≫ B2_.isoZero.hom = C.isoZero.hom ≫ g

variable {f g : V ⟶ P} {C : SequenceOfBlowups V} {B1_ B2_ : SequenceOfBlowups P} {L}
  {sg1 : ∀ i : ℕ, i ≤ L → (schemeAt C i ⟶ schemeAt B1_ i)}
  {sg2 : ∀ i : ℕ, i ≤ L → (schemeAt C i ⟶ schemeAt B2_ i)}
  {a : ∀ i : ℕ, IdealSheafData $ schemeAt C i}

section
variable (hd : BlowupSeqComparison f g C B1_ B2_ L sg1 sg2 a)
include hd
section
variable (i) (hi : i < L)
theorem BlowupSeqComparison.exists_preimage_of_mem_center_support_left (x : ↥(schemeAt B1_ i)) (hx : x ∈ support (center B1_ i)) :
    ∃ y : ↥(schemeAt C i), (sg1 i hi.le).base y = x := by
  exact exists_preimage_of_isPullback (isPullback_projectionToBase_of_isPullback_blowupMorphism f C B1_ L sg1 hd.zero1 hd.pullback1 i hi.le) x $ hd.cover1 i hi x hx

theorem BlowupSeqComparison.exists_preimage_of_mem_center_support_right (x : ↥(schemeAt B2_ i)) (hx : x ∈ support (center B2_ i)) :
    ∃ y : ↥(schemeAt C i), (sg2 i hi.le).base y = x := by
  exact exists_preimage_of_isPullback (isPullback_projectionToBase_of_isPullback_blowupMorphism g C B2_ L sg2 hd.zero2 hd.pullback2 i hi.le) x $ hd.cover2 i hi x hx
end

section
variable {i} (hi : i < L) (st : BlowupSeqLevelIso C B1_ B2_ L sg1 sg2 a i)
include hi
theorem BlowupSeqLevelIso.center_comap_iso_hom_eq :
    (center B2_ i).comap st.iso.hom = center B1_ i := by
  have hkey : ∀ y : (sbAt C i), y ∈ support (sbCtr C i) →
      (sg1 i hi.le).base y = st.iso.inv.base (bsM (sg2 i hi.le) y) := by
    intro y hy
    have hy2 := support_antitone (hd.ideal_le_center i hi) hy
    obtain ⟨z, hz⟩ := exists_subschemeio_base_eq (a i) y hy2
    have e1 : bsM (siI (a i) ≫ sg1 i hi.le) z
        = bsM (siI (a i) ≫ sg2 i hi.le ≫ st.iso.inv) z := by
      rw [st.compat hi.le]
    have e2 : bsM (sg1 i hi.le) ((a i).subschemeι.base z)
        = st.iso.inv.base (bsM (sg2 i hi.le) $ (a i).subschemeι.base z) := e1
    rwa [hz] at e2
  have h1 : support (sbCtr B1_ i) ≤ support ((sbCtr B2_ i).comap st.iso.hom) := by
    intro x hx
    obtain ⟨y, hy⟩ := hd.exists_preimage_of_mem_center_support_left i hi x hx
    have hyc : y ∈ support (center C i) := by
      rwa [hd.center_C1 i hi, mem_support_comap, hy]
    have hy2 : bsM (sg2 i hi.le) y ∈ support (center B2_ i) := by
      have := hyc
      rwa [hd.center_C2 i hi, mem_support_comap] at this
    rw [mem_support_comap]
    have hx' : x = st.iso.inv.base (bsM (sg2 i hi.le) y) := by simp_all
    rwa [hx', inv_hom_apply]
  let _a3 := (sbCtr B1_ i).comap st.iso.inv
  have h2 : support (sbCtr B2_ i) ≤ support _a3 := by
    intro x hx
    obtain ⟨y, hy⟩ := hd.exists_preimage_of_mem_center_support_right i hi x hx
    have hyc : y ∈ support (center C i) := by
      rwa [hd.center_C2 i hi, mem_support_comap, hy]
    have hy1 : bsM (sg1 i hi.le) y ∈ support (center B1_ i) := by
      have := hyc
      rwa [hd.center_C1 i hi, mem_support_comap] at this
    rwa [mem_support_comap, ← hy, ← hkey y hyc]
  refine le_antisymm (hd.determined1 i hi _ h1) ?_
  have hmono : _a3.comap st.iso.hom
      ≤ (sbCtr B2_ i).comap st.iso.hom :=
    comap_mono st.iso.hom $ hd.determined2 i hi _ h2
  rwa [← comap_comp, st.iso.hom_inv_id,
    comap_id] at hmono

theorem BlowupSeqLevelIso.exists_iso_succ_comp_blowupMorphism :
    ∃ e : schemeAt B1_ (i + 1) ≅ schemeAt B2_ (i + 1),
      hom e ≫ transitionMapSucc B2_ i ≫ st.iso.inv = transitionMapSucc B1_ i := by
  have h2 :=
    (hd.isBlowup_B2 i hi).comp_iso_hom st.iso.symm
  rw [symm_hom, symm_inv, BlowupSeqLevelIso.center_comap_iso_hom_eq hd hi st] at h2
  exact (hd.isBlowup_B1 i hi).exists_iso h2

def BlowupSeqLevelIso.isoSucc :
    schemeAt B1_ (i + 1) ≅ schemeAt B2_ (i + 1) :=
  (BlowupSeqLevelIso.exists_iso_succ_comp_blowupMorphism hd hi st).choose

theorem BlowupSeqLevelIso.isoSucc_hom_comp_blowupMorphism :
    hom (BlowupSeqLevelIso.isoSucc hd hi st) ≫ transitionMapSucc B2_ i ≫ st.iso.inv = transitionMapSucc B1_ i :=
  (BlowupSeqLevelIso.exists_iso_succ_comp_blowupMorphism hd hi st).choose_spec

theorem BlowupSeqLevelIso.subschemeio_comp_eq_comp_isoSucc_inv :
    ∀ hj,
      subschemeι (a (i + 1)) ≫ sg1 (i + 1) hj =
        subschemeι (a (i + 1)) ≫ sg2 (i + 1) hj ≫ inv (BlowupSeqLevelIso.isoSucc hd hi st) := by
  intro hj
  have hcen1 := hd.center_C1 i hi
  have hinv : (center B1_ i).comap st.iso.inv = center B2_ i := by
    rw [← BlowupSeqLevelIso.center_comap_iso_hom_eq hd hi st, comap_hom_comap_inv]
  have hcen2 : (center B1_ i).comap (sg2 i hi.le ≫ st.iso.inv) = center C i := by
    rw [comap_comp, hinv, ← hd.center_C2 i hi]
  have hZeq : (center B1_ i).comap (sg1 i hi.le)
      = (center B1_ i).comap (sg2 i hi.le ≫ st.iso.inv) := by
    rw [← hcen1, hcen2]
  have hrh_ : p15 (transitionMapSucc C i) ((center B1_ i).comap (sg1 i hi.le)) := by
    rw [← hcen1]
    exact hd.isBlowup_C i hi
  let _s0 := sg2 (i + 1) hj ≫ isoI (BlowupSeqLevelIso.isoSucc hd hi st)
  have hg' : _s0 ≫ transitionMapSucc B1_ i
      = transitionMapSucc C i ≫ sg2 i hi.le ≫ st.iso.inv := by
    calc _s0 ≫ transitionMapSucc B1_ i
        = sg2 (i + 1) hj ≫ isoI (BlowupSeqLevelIso.isoSucc hd hi st) ≫ transitionMapSucc B1_ i := by
          rw [assoc]
      _ = sg2 (i + 1) hj ≫ transitionMapSucc B2_ i ≫ st.iso.inv := by
          rw [← BlowupSeqLevelIso.isoSucc_hom_comp_blowupMorphism hd hi st]
          simp
      _ = (sg2 (i + 1) hj ≫ transitionMapSucc B2_ i) ≫ st.iso.inv := by rw [assoc]
      _ = transitionMapSucc C i ≫ sg2 i hi.le ≫ st.iso.inv := by rw [(hd.pullback2 i hi).w, assoc]
  refine hd.lifting (schemeAt B1_ i) (schemeAt B1_ (i + 1)) (schemeAt C i) (schemeAt C (i + 1)) (transitionMapSucc B1_ i)
    (center B1_ i) (hd.isBlowup_B1 i hi) (sg1 i hi.le) (sg2 i hi.le ≫ st.iso.inv) hZeq
    (transitionMapSucc C i) hrh_ (sg1 (i + 1) hj)
    _s0 ((hd.pullback1 i hi).w) hg' (a i) (st.compat hi.le)
    (a (i + 1)) ?_
  rw [← hcen1]
  exact hd.ideal_succ i hi

def BlowupSeqLevelIso.succ :
    BlowupSeqLevelIso C B1_ B2_ L sg1 sg2 a $ i + 1 where
  iso := BlowupSeqLevelIso.isoSucc hd hi st
  compat := BlowupSeqLevelIso.subschemeio_comp_eq_comp_isoSucc_inv hd hi st
end

def blowupSeqLevelIsoZero :
    BlowupSeqLevelIso C B1_ B2_ L sg1 sg2 a 0 where
  iso := B1_.isoZero ≪≫ B2_.isoZero.symm
  compat := by
    intro hi
    have h1 := hd.zero1
    have h2 := hd.zero2
    rw [← cancel_mono B1_.isoZero.hom]
    simp only [assoc, trans_inv, symm_inv, Iso.inv_hom_id, comp_id]
    rw [h1, h2]
    exact hd.zero_ideal

theorem blowupSeqLevelIsoZero_iso_hom_comp_isoObjZero :
    (blowupSeqLevelIsoZero hd).iso.hom ≫ B2_.isoZero.hom = B1_.isoZero.hom := by
  show isoH (B1_.isoZero ≪≫ B2_.isoZero.symm) ≫ sbIzH B2_ = sbIzH B1_
  simp
end

theorem BlowupSeqLevelIso.hom_comp_blowupMorphism_eq_comp_iso_hom {i : ℕ} (st : BlowupSeqLevelIso C B1_ B2_ L sg1 sg2 a i)
    (e : schemeAt B1_ (i + 1) ≅ schemeAt B2_ (i + 1))
    (he : hom e ≫ transitionMapSucc B2_ i ≫ st.iso.inv = transitionMapSucc B1_ i) :
    hom e ≫ transitionMapSucc B2_ i = transitionMapSucc B1_ i ≫ st.iso.hom := by
  rw [← he]
  simp

def blowupSeqLevelIsoOfLE (hd : BlowupSeqComparison f g C B1_ B2_ L sg1 sg2 a) :
    ∀ i : ℕ, i ≤ L → BlowupSeqLevelIso C B1_ B2_ L sg1 sg2 a i
  | 0, _ => blowupSeqLevelIsoZero hd
  | (i + 1), h =>
      BlowupSeqLevelIso.succ hd (lt_of_succ_le h) $ blowupSeqLevelIsoOfLE hd i $ le_of_succ_le h

theorem SequenceOfBlowups.isomorphic_of_isStrictPullback_same_source (B B' : SequenceOfBlowups P)
    {ph_ ps_ : V ⟶ P} {D : SequenceOfBlowups V}
    (hlift : BlowupLiftEqOnControlledTransform)
    (h1_ : IsStrictPullbackBlowupSeq ph_ D B) (h2_ : IsStrictPullbackBlowupSeq ps_ D B')
    (hcov1 : ∀ i : ℕ, i < length B → ∀ x ∈ support (B.center i),
      (projectionToBase B i).base x ∈ range ph_.base)
    (hcov2 : ∀ i : ℕ, i < length B' → ∀ x ∈ support (B'.center i),
      (projectionToBase B' i).base x ∈ range ps_.base)
    (hdet1 : ∀ i : ℕ, i < length B → ∀ J : IdealSheafData $ schemeAt B i,
      support (B.center i) ≤ support J → J ≤ B.center i)
    (hdet2 : ∀ i : ℕ, i < length B' → ∀ J : IdealSheafData $ schemeAt B' i,
      support (B'.center i) ≤ support J → J ≤ B'.center i)
    (b : ∀ i : ℕ, IdealSheafData $ schemeAt D i)
    (hzero : subschemeι (b 0) ≫ D.isoZero.hom ≫ ph_ = subschemeι (b 0) ≫ D.isoZero.hom ≫ ps_)
    (hsucc : ∀ i : ℕ, i < length D →
      exceptionalIdeal (transitionMapSucc D i) (center D i) * b (i + 1) = (b i).comap (transitionMapSucc D i))
    (hle : ∀ i : ℕ, i < length D → b i ≤ center D i) :
    B.Isomorphic B' := by
  unfold IsStrictPullbackBlowupSeq at h1_ h2_
  obtain ⟨hlen1, s1_, hz1, hpb1, hc1⟩ := h1_
  obtain ⟨hlen2, s2_, hz2, hpb2, hc2⟩ := h2_
  have hd : BlowupSeqComparison ph_ ps_ D B B' D.length s1_ s2_ b :=
    { zero_ideal := hzero
      isBlowup_B1 := fun i hi => B.isBlowupAlongIdealSheaf_blowupMorphism i (by rw [← hlen1]; exact hi)
      isBlowup_B2 := fun i hi => B'.isBlowupAlongIdealSheaf_blowupMorphism i (by rw [← hlen2]; exact hi)
      isBlowup_C := fun i hi => D.isBlowupAlongIdealSheaf_blowupMorphism i hi
      ideal_succ := hsucc
      ideal_le_center := hle
      center_C1 := fun i hi => hc1 i hi
      center_C2 := fun i hi => hc2 i hi
      cover1 := fun i hi => hcov1 i (by rw [← hlen1]; exact hi)
      cover2 := fun i hi => hcov2 i (by rw [← hlen2]; exact hi)
      lifting := hlift
      determined1 := fun i hi => hdet1 i (by rw [← hlen1]; exact hi)
      determined2 := fun i hi => hdet2 i (by rw [← hlen2]; exact hi)
      pullback1 := hpb1
      pullback2 := hpb2
      zero1 := hz1
      zero2 := hz2 }
  unfold SequenceOfBlowups.Isomorphic
  refine ⟨st_ hlen1 hlen2,
    fun i hi => (blowupSeqLevelIsoOfLE hd i $ le_of_le_of_eq hi hlen1.symm).iso, blowupSeqLevelIsoZero_iso_hom_comp_isoObjZero hd, ?_, ?_⟩
  intro i hi
  have hiD : i < length D := by rw [hlen1]
                                exact hi
  exact BlowupSeqLevelIso.hom_comp_blowupMorphism_eq_comp_iso_hom (blowupSeqLevelIsoOfLE hd i hiD.le)
    (BlowupSeqLevelIso.isoSucc hd hiD $ blowupSeqLevelIsoOfLE hd i hiD.le)
    (BlowupSeqLevelIso.isoSucc_hom_comp_blowupMorphism hd hiD $ blowupSeqLevelIsoOfLE hd i hiD.le)
  intro i hi
  have hiD : i < length D := by rw [hlen1]
                                exact hi
  exact BlowupSeqLevelIso.center_comap_iso_hom_eq hd hiD $ blowupSeqLevelIsoOfLE hd i hiD.le

end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

theorem eq_of_comp_io_eq {X : Sch} (U : Opn X) {W : Sch}
    {a b : W ⟶ toScheme U} (h : a ≫ ι U = b ≫ ι U) : a = b := by
  have : Mono U.i := inferInstance
  exact mp_ (cancel_mono U.i) h

theorem hom_ext_of_comp_io_eq_of_opens_cover {X Y : Sch} {ι : Type} (W : ι → Opn X)
    (hW : ∀ x : ↥X, ∃ i, x ∈ W i) (a b : X ⟶ Y)
    (h : ∀ i, (W i).i ≫ a = (W i).i ≫ b) : a = b := by
  refine (mkOfCovers ι (fun i => oSch $ W i) (fun i => opI $ W i) ?_ ?_).hom_ext
    a b ?_
  intro x
  obtain ⟨i, hi⟩ := hW x
  have hx : x ∈ range (W i).i := by simp_all
  obtain ⟨y, hy⟩ := hx
  exact ⟨i, y, hy⟩
  intro i
  infer_instance
  intro i
  exact h i

theorem exists_isoSpec_of_isAffineOpen {P : Sch} {U : Opn P}
    (hU : IsAffineOpen U) :
    ∃ (R : Type) (_ : CommRing R), Nonempty $ toScheme U ≅ Sp R :=
  ⟨U.sec, inferInstance, ⟨hU.isoSpec⟩⟩

theorem comap_mul_of_isOpenImmersion {X U : Sch} (f : U ⟶ X) [IsOpenImmersion f]
    (I J : ISD X) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine m29 $ funext fun V => ?_
  have hV := V.2.image_of_isOpenImmersion f
  have he : V ≤ preU f (imU f V) := by
    simp [preimage_image_eq]
  simp [ideal_mul, mul_apply]
  rw [comap_ideal_eq_map_appLE I f ⟨_, hV⟩ V he,
    comap_ideal_eq_map_appLE J f ⟨_, hV⟩ V he,
    comap_ideal_eq_map_appLE (I * J) f ⟨_, hV⟩ V he]
  simp [ideal_mul, mul_apply]
  rw [m220]

theorem exists_specIdealSheaf_eq (R : Type) [CommRing R]
    (I : IdealSheafData $ Sp R) :
    ∃ J : Ideal R, specIdealSheaf J = I := by
  let _a0 := Scheme.GSpecIso $ m10 R
  refine ⟨m6 _a0.hom.hom
    (I.ideal ⟨⊤, isAffineOpen_top $ Sp R⟩), ?_⟩
  have h := (equivOfIsAffine
      (X := Sp R)).symm_apply_apply I
  rw [equivOfIsAffine_apply,
    equivOfIsAffine_symm_apply] at h
  rw [specIdealSheaf_eq_ofIdealTop, map_map, ← hom_comp,
    _a0.hom_inv_id, hom_id, map_id]
  exact h

theorem subschemeio_comap_comp_eq_of_subschemeio_comp_eq {X Y P : Sch} (f : X ⟶ Y) (u v : Y ⟶ P)
    (bf_ : ISD Y) (hagree : subschemeι bf_ ≫ u = subschemeι bf_ ≫ v) :
    subschemeι (bf_.comap f) ≫ f ≫ u = subschemeι (bf_.comap f) ≫ f ≫ v := by
  let _a0 := siI (cmI bf_ f) ≫ f
  obtain ⟨t, ht⟩ : ∃ t : subS (cmI bf_ f) ⟶ subS bf_,
      _a0 = t ≫ siI bf_ :=
    ⟨isoH (bf_.comapIso f) ≫ snd f bf_.si, by
      rw [assoc, ← condition, ← assoc,
        comapIso_hom_fst]⟩
  calc _a0 ≫ u
      = t ≫ siI bf_ ≫ u := by rw [← assoc, ht, assoc]
    _ = t ≫ siI bf_ ≫ v := by rw [hagree]
    _ = _a0 ≫ v := by rw [← assoc, ← ht, assoc]

theorem subschemeio_comp_eq_of_mul_comap {V V1 P : Sch} (f : V1 ⟶ V) (u v : V ⟶ P)
    (bf_ : ISD V) (hagree : subschemeι bf_ ≫ u = subschemeι bf_ ≫ v)
    (e bf1 : ISD V1) (hmul : e * bf1 = bf_.comap f) :
    subschemeι bf1 ≫ f ≫ u = subschemeι bf1 ≫ f ≫ v := by
  have hle : bf_.comap f ≤ bf1 := by
    rw [← hmul, le_def]
    intro V
    rw [ideal_mul]
    exact Ideal.mul_le_inf.trans inf_le_right
  let _a0 := siI $ cmI bf_ f
  obtain ⟨t, ht⟩ : ∃ t : subS bf1 ⟶ subS (cmI bf_ f),
      t ≫ _a0 = siI bf1 :=
    ⟨inclusion hle, inclusion_subschemeι hle⟩
  calc siI bf1 ≫ f ≫ u
      = (t ≫ _a0) ≫ f ≫ u := by rw [ht]
    _ = t ≫ (_a0 ≫ f ≫ u) := by rw [assoc]
    _ = t ≫ (_a0 ≫ f ≫ v) := by rw [subschemeio_comap_comp_eq_of_subschemeio_comp_eq f u v bf_ hagree]
    _ = (t ≫ _a0) ≫ f ≫ v := by rw [assoc]
    _ = siI bf1 ≫ f ≫ v := by rw [ht]

theorem subschemeio_comp_eq_of_blowup_lifts_spec {R : Type} [CommRing R] {B W : Sch}
    (p : B ⟶ Sp R) (J : IdealSheafData $ Sp R)
    (hp : IsBlowupAlongIdealSheaf p J) (rh_ rh' : W ⟶ Sp R) (af_ bf1 : ISD W)
    (hagree : subschemeι af_ ≫ rh_ = subschemeι af_ ≫ rh')
    (hpull : J.comap rh_ = J.comap rh')
    (hcart : IsLocallyGeneratedByNonZeroDivisor $ J.comap rh_)
    (hfac : J.comap rh_ * bf1 = af_)
    (h h' : W ⟶ B) (hh : h ≫ p = rh_) (hh' : h' ≫ p = rh') :
    subschemeι bf1 ≫ h = subschemeι bf1 ≫ h' := by
  obtain ⟨I, rfl⟩ := exists_specIdealSheaf_eq R J
  have hq := isBlowupAlongIdealSheaf_affineBlowup_toSpec I
  obtain ⟨be_, hbe_⟩ := hq.exists_lift p hp.1
  obtain ⟨al_, hal_⟩ := hp.exists_lift (p13 I) hq.1
  have hbeal : be_ ≫ al_ = 𝟙 B := by
    refine hp.hom_ext hp.1 ?_ ?_
    simp_all
    rw [id_comp]
  have key := subschemeio_comp_eq_of_affineBlowup_lifts I rh_ rh' af_ bf1 (h ≫ be_) (h' ≫ be_) hagree hpull hcart hfac
    (by rw [assoc, hbe_, hh]) $ by rw [assoc, hbe_, hh']
  have hfin := congrArg (fun m => m ≫ al_) key
  simp [assoc, hbeal, comp_id] at hfin
  exact hfin

theorem subschemeio_comap_io_comp_eq_of_blowup_lifts_affine {P P1 V V1 : Sch} (pi_ : P1 ⟶ P)
    (Z : ISD P) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (ps_ ps' : V ⟶ P)
    (hZ : Z.comap ps_ = Z.comap ps') (rh_ : V1 ⟶ V)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((Z.comap ps_).comap rh_))
    (ps1 ps'1 : V1 ⟶ P1) (hps1 : ps1 ≫ pi_ = rh_ ≫ ps_) (hps'1 : ps'1 ≫ pi_ = rh_ ≫ ps')
    (bf_ : ISD V) (hagree : subschemeι bf_ ≫ ps_ = subschemeι bf_ ≫ ps')
    (bf1 : ISD V1) (hfac : (Z.comap ps_).comap rh_ * bf1 = bf_.comap rh_)
    (U : Opn P) (hU : IsAffineOpen U) (O : Opn V1)
    (hO : O ≤ (Opens.map (rh_ ≫ ps_).base).obj U)
    (hO' : O ≤ (Opens.map (rh_ ≫ ps').base).obj U) :
    subschemeι (bf1.comap O.i) ≫ ι O ≫ ps1 = subschemeι (bf1.comap O.i) ≫ ι O ≫ ps'1 := by
  let _c0 := (cmI bf_ rh_).comap O.i
  obtain ⟨R, hR, ⟨e⟩⟩ := exists_isoSpec_of_isAffineOpen hU
  let _ := hR
  let _a0 := (rh_ ≫ ps_).resLE U O hO
  have hres : _a0 ≫ opI U = opI O ≫ (rh_ ≫ ps_) := by
    rw [q4]
  let _a1 := (rh_ ≫ ps').resLE U O hO'
  have hres' : _a1 ≫ opI U = opI O ≫ (rh_ ≫ ps') := by
    rw [q4]
  let _a3 := snd pi_ U.i ≫ isoH e
  have hcalc : ∀ χ (hch_ : O ≤ (m54 (rh_ ≫ χ).base).obj U),
      ((Z.comap U.i).comap e.inv).comap ((rh_ ≫ χ).resLE U O hch_ ≫ isoH e)
        = (cmI (Z.comap χ) rh_).comap O.i := by
    intro χ hch_
    simp only [← comap_comp]
    congr 1
    simp
  have hcart_W : p17 (((Z.comap U.i).comap e.inv).comap
      (_a0 ≫ isoH e)) := by
    rw [hcalc ps_ hO]
    exact hcart.comap_of_isOpenImmersion O.i
  let _a6 := _a1 ≫ isoH e
  have hpull_W : ((Z.comap U.i).comap e.inv).comap (_a0 ≫ isoH e)
      = ((Z.comap U.i).comap e.inv).comap _a6 := by
    rw [hcalc ps_ hO, hcalc ps' hO', hZ]
  have hfac_W : ((Z.comap U.i).comap e.inv).comap (_a0 ≫ isoH e)
      * bf1.comap O.i = (cmI bf_ rh_).comap O.i := by
    rw [hcalc ps_ hO, ← comap_mul_of_isOpenImmersion O.i, hfac]
  have hagree_W : siI _c0 ≫ (_a0 ≫ isoH e)
      = siI _c0 ≫ _a6 := by
    have step2 := subschemeio_comap_comp_eq_of_subschemeio_comp_eq O.i (rh_ ≫ ps_) (rh_ ≫ ps') (cmI bf_ rh_) (subschemeio_comap_comp_eq_of_subschemeio_comp_eq rh_ ps_ ps' bf_ hagree)
    have step3 : (siI _c0 ≫ _a0) ≫ opI U
        = (siI _c0 ≫ _a1) ≫ opI U := by
      rwa [assoc, assoc, hres, hres']
    rw [← assoc, ← assoc, eq_of_comp_io_eq U step3]
  let _a7 := opI O ≫ ps1
  have hcond : _a7 ≫ pi_ = _a0 ≫ opI U := by
    rw [hres, assoc, hps1]
  let _a8 := opI O ≫ ps'1
  have hcond' : _a8 ≫ pi_ = _a1 ≫ opI U := by
    rw [hres', assoc, hps'1]
  have hh : m107 _a7 _a0 hcond
      ≫ _a3 = _a0 ≫ isoH e := by
    rw [← assoc, lift_snd]
  have hh' : m107 _a8 _a1 hcond'
      ≫ _a3 = _a6 := by
    rw [← assoc, lift_snd]
  have key := subschemeio_comp_eq_of_blowup_lifts_spec (R := R)
    _a3 ((Z.comap U.i).comap e.inv) ((hpi_.pullback_snd_of_isOpenImmersion U.i).comp_iso_hom e)
    (_a0 ≫ isoH e) _a6
    _c0 (bf1.comap O.i) hagree_W hpull_W hcart_W hfac_W
    (m107 _a7 _a0 hcond)
    (m107 _a8 _a1 hcond') hh hh'
  simpa only [assoc, lift_fst] using (congrArg (fun m => m ≫ fst pi_ U.i) key)

theorem preimage_io_subschemeio_comp_eq_of_comap_io {T Y : Sch} (c : ISD T) (O : Opn T)
    (f' g' : T ⟶ Y)
    (hEqComap : subschemeι (c.comap O.i) ≫ ι O ≫ f' = subschemeι (c.comap O.i) ≫ ι O ≫ g') :
    ι (subschemeι c ⁻¹ᵁ O) ≫ subschemeι c ≫ f'
      = ι (subschemeι c ⁻¹ᵁ O) ≫ subschemeι c ≫ g' := by
  obtain ⟨k, hk⟩ : ∃ k : oSch (siPre c O) ⟶ subS (cmI c O.i), k ≫ siI (cmI c O.i) ≫ opI O = opI (preU c.si O) ≫ siI c := by
    let _c0 := siPre c O
    let _a0 := siI $ cmI c O.i
    let _a2 := fst O.i c.si
    obtain ⟨s, hs⟩ : ∃ s : m131 O.i c.si ⟶ subS (cmI c O.i),
        s ≫ _a0 = _a2 :=
      ⟨isoI $ c.comapIso O.i, comapIso_inv_subschemeι c O.i⟩
    let _a1 := c.subschemeι.resLE O _c0 le_rfl
    have hres : _a1 ≫ opI O
        = opI _c0 ≫ siI c := q4 _ _
    obtain ⟨k, hk⟩ : ∃ k,
        k ≫ _a2
          = _a1 :=
      ⟨m107 _ _ hres, lift_fst _ _ _⟩
    refine ⟨k ≫ s, ?_⟩
    calc (k ≫ s) ≫ _a0 ≫ opI O
        = k ≫ (s ≫ _a0) ≫ opI O := by simp [assoc]
      _ = k ≫ _a2 ≫ opI O := by rw [hs]
      _ = (k ≫ _a2) ≫ opI O := by rw [assoc]
      _ = _a1 ≫ opI O := by rw [hk]
      _ = opI _c0 ≫ siI c := hres
  calc (siI c ⁻¹ᵁ O).i ≫ siI c ≫ f'
      = (opI (siI c ⁻¹ᵁ O) ≫ siI c) ≫ f' := by rw [assoc]
    _ = (k ≫ siI (cmI c O.i) ≫ opI O) ≫ f' := by rw [hk]
    _ = k ≫ (siI (cmI c O.i) ≫ opI O ≫ f') := by
        rw [assoc, assoc]
    _ = k ≫ (siI (cmI c O.i) ≫ opI O ≫ g') := by rw [hEqComap]
    _ = (k ≫ siI (cmI c O.i) ≫ opI O) ≫ g' := by
        rw [assoc, assoc]
    _ = (opI (siI c ⁻¹ᵁ O) ≫ siI c) ≫ g' := by rw [hk]
    _ = opI (siI c ⁻¹ᵁ O) ≫ siI c ≫ g' := by rw [assoc]

theorem blowupLiftEqOnControlledTransform : BlowupLiftEqOnControlledTransform := by
  intro X Y S T pi_ Z hpi_ f g hfg rh_ hrh_ f' g' hf' hg' a hagree c hc
  have main : ∀ x : (subS c), ∃ O, c.subschemeι.base x ∈ O ∧
      opI (siI c ⁻¹ᵁ O) ≫ siI c ≫ f'
        = opI (siI c ⁻¹ᵁ O) ≫ siI c ≫ g' := by
    intro x
    have hpt : bsM (rh_ ≫ f) (c.subschemeι.base x)
        = bsM (rh_ ≫ g) (c.subschemeι.base x) := by
      simpa using (congrArg (fun m : subS c ⟶ X => bsM m x) $ subschemeio_comp_eq_of_mul_comap rh_ f g a hagree (cmI (cmI Z f) rh_) c hc)
    obtain ⟨U, hxU, hU⟩ := X.exists_isAffineOpen_mem $ bsM (rh_ ≫ f) $ c.subschemeι.base x
    refine ⟨(m54 (rh_ ≫ f).base).obj U ⊓ (m54 (rh_ ≫ g).base).obj U, ⟨hxU, ?_⟩, ?_⟩
    show bsM (rh_ ≫ g) (c.subschemeι.base x) ∈ U
    rwa [← hpt]
    exact preimage_io_subschemeio_comp_eq_of_comap_io c _ f' g' $ subschemeio_comap_io_comp_eq_of_blowup_lifts_affine pi_ Z hpi_ f g hfg rh_ hrh_.1 f' g' hf' hg' a hagree c hc U hU ((m54 (rh_ ≫ f).base).obj U ⊓ (m54 (rh_ ≫ g).base).obj U) inf_le_left inf_le_right
  choose Ox hOx hOeq using main
  refine hom_ext_of_comp_io_eq_of_opens_cover (fun x : (subS c) => siPre c $ Ox x) ?_ _ _ hOeq
  intro y
  exact ⟨y, hOx y⟩





def MaxContactHypersurfacesEtaleEquivalent : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (P : Sch)
      (p : P ⟶ Sp k) [Smooth p]
      [LocallyOfFiniteType p] [QuasiCompact p]
      (A : ISD P) (mu_ : ℕ), 1 ≤ mu_ →
    IsMaxContactInvariant k p A mu_ →
    (∀ x : ↥P, orderAt A x ≤ (mu_ : ENat)) →
    ∀ (N : Bdy P) (H1_ H2_ : ISD P),
      InStrictNormalCrossingPosition p (H1_ :: N) → InStrictNormalCrossingPosition p (H2_ :: N) →
      IsMaxContactHypersurface k p A mu_ H1_ → IsMaxContactHypersurface k p A mu_ H2_ →
      ∃ (V : Sch) (ps1 ps2 : V ⟶ P) (_ : Etale ps1)
        (_ : Etale ps2)
        (_ : QuasiCompact $ ps1 ≫ p)
        (hft : LocallyOfFiniteType $ ps1 ≫ p),
        ps1 ≫ p = ps2 ≫ p ∧
        orderAtLeastLocus A mu_ ⊆ range ps1.base ∧
        orderAtLeastLocus A mu_ ⊆ range ps2.base ∧
        A.comap ps1 = A.comap ps2 ∧
        H1_.comap ps1 = H2_.comap ps2 ∧
        N.map (fun D => D.comap ps1) = N.map (fun D => D.comap ps2) ∧
        subschemeι (@maxContactIdeal k _ _ V (ps1 ≫ p) hft (A.comap ps1) mu_) ≫ ps1 =
          subschemeι (@maxContactIdeal k _ _ V (ps1 ≫ p) hft (A.comap ps1) mu_) ≫ ps2

def ExistsMaxContactControlledTransforms : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (V : Sch)
      (q : V ⟶ Sp k) [Smooth q]
      [LocallyOfFiniteType q]
      (A' : ISD V) (mu_ : ℕ), 1 ≤ mu_ →
    ∀ (E' : Bdy V) (u : MarkedSequenceOfBlowups q A' mu_ E'),
      (∀ i : ℕ, i ≤ u.length → IsLocallyNoetherian (u.schemeAt i)) →
      (∀ i : ℕ, i < u.length → ∀ J : IdealSheafData $ u.schemeAt i,
        (((u.center i).support : CSet $ u.schemeAt i) ⊆ ((J.support : CSet $ u.schemeAt i))) →
        J ≤ u.center i) →
      ∃ c : ∀ i : ℕ, IdealSheafData $ u.schemeAt i,
        c 0 = (maxContactIdeal k q A' mu_).comap u.isoZero.hom ∧
        (∀ i : ℕ, i < u.length →
          exceptionalIdeal (u.transitionMapSucc i) (u.center i) * c (i + 1) =
            (c i).comap (u.transitionMapSucc i)) ∧
        (∀ i : ℕ, i < u.length → c i ≤ u.center i)

namespace OrderReduction

structure OrderReductionHypotheses : Prop where
  maxContactChain : ExistsMaxContactControlledTransforms
  center_mem_coSupport : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i < s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ (((s.center i).support : CSet $ s.schemeAt i)) →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult
  dBalanced_comap : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (Y : Sch)
      (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ [LocallyOfFiniteType T.structMap]
        [LocallyOfFiniteType q],
      IsDerivBalanced T.base T.structMap T.ideal T.mult →
      IsDerivBalanced T.base q (T.ideal.comap h) T.mult
  schemeDim_le_of_etale : ∀ (V P : Sch) (f : V ⟶ P) [Etale f]
      [IsLocallyNoetherian P],
      topologicalKrullDim ↥P < ⊤ → krullDimSucc V ≤ krullDimSucc P
  isLocallyNoetherian_obj : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i ≤ s.length → IsLocallyNoetherian (s.schemeAt i)
  lifting : BlowupLiftEqOnControlledTransform
  smooth_center_radical : ∀ (k : Type) [Field k] (X : Sch)
      (p : X ⟶ Sp k) (Z : ISD X),
      Smooth (Z.si ≫ p) →
      ∀ J : ISD X,
        (((Z.support : Set ↥X)) ⊆ ((J.support : Set ↥X))) → J ≤ Z
  etaleEqualization : MaxContactHypersurfacesEtaleEquivalent
  isStrictPullbackSeq : ∀ (X' X : Sch) (ph_ : X' ⟶ X) (s' : SequenceOfBlowups X')
      (s : SequenceOfBlowups X), IsPullbackBlowupSequence ph_ s' s →
      (∀ i : ℕ, i < s.length → (((s.center i).support : CSet $ s.schemeAt i)).Nonempty) →
      (∀ i : ℕ, i < s.length → ∀ x ∈ (((s.center i).support : CSet $ s.schemeAt i)),
        (s.projectionToBase i).base x ∈ range ph_.base) →
      IsStrictPullbackBlowupSeq ph_ s' s
  valid_pullbackAlong : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (Y : Sch)
      (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h] [QuasiCompact q],
      h ≫ T.structMap = q → (T.pbA q h).IsAdmissible

end OrderReduction




section
variable {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (f : R →+* S) (g : S →+* R) (hgf : g.comp f = RingHom.id R)
include hgf
theorem map_maximalIdeal_le_maximalIdeal_of_retraction :
    Ideal.map f (maximalIdeal R) ≤ maximalIdeal S := by
  rw [map_le_iff_le_comap]
  intro x hx
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hx
  have h3 : g (f x) = x := by
    rw [← m82, hgf, id_apply]
  have h2 := hu.map g
  rwa [h3] at h2

theorem idealOrder_map_eq_of_comp_eq_id (hfg : f.comp g = RingHom.id S) I :
    idealOrder (Ideal.map f I) = idealOrder I := by
  have h3 := idealOrder_le_idealOrder_map g (map_maximalIdeal_le_maximalIdeal_of_retraction g f hfg) $ m6 f I
  rw [map_map, hgf, map_id] at h3
  exact le_antisymm h3 $ idealOrder_le_idealOrder_map f (map_maximalIdeal_le_maximalIdeal_of_retraction f g hgf) I
end

theorem orderAt_comap_of_isIso_stalkMap {X Y : Sch} (f : X ⟶ Y) (J : ISD Y)
    x [IsIso $ f.stalkMap x] :
    orderAt (J.comap f) x = orderAt J (f.base x) := by
  let _a0 := (inv $ f.stalkMap x).hom
  let _a1 := (f.stalkMap x).hom
  have hgf : _a0.comp _a1 = RingHom.id _ := by
    have h := congrArg CommRingCat.Hom.hom $ IsIso.hom_inv_id $ f.stalkMap x
    rwa [CommRingCat.hom_comp, CommRingCat.hom_id] at h
  have hfg : _a1.comp _a0 = RingHom.id _ := by
    have h := congrArg CommRingCat.Hom.hom $ IsIso.inv_hom_id $ f.stalkMap x
    rwa [hom_comp, hom_id] at h
  simp [orderAt_eq_idealOrder]
  rw [stalkIdeal_comap]
  exact idealOrder_map_eq_of_comp_eq_id _ _ hgf hfg _

theorem isIso_stalkMap_of_isBlowupAlongIdealSheaf {X X1 : Sch} (pi_ : X1 ⟶ X) (Z : ISD X)
    (h : IsBlowupAlongIdealSheaf pi_ Z) x (hx : pi_.base x ∉ Z.support) :
    IsIso $ pi_.stalkMap x := by
  let _c0 := p4 $ pre pi_ $ suppC Z
  have h1 := h.restrict $ suppC Z
  rw [comap_io_support_compl_eq_top Z] at h1
  have hiso : IsIso $ pi_.mr $ suppC Z := h1.isIso_of_top
  have hoi : IsOpenImmersion $ pi_.mr $ suppC Z := IsOpenImmersion.of_isIso _
  let y : (oSch $ pre pi_ $ suppC Z) := ⟨x, hx⟩
  have hs2 : IsIso $ _c0.stalkMap y := inferInstance
  have hoi2 : IsOpenImmersion
      ((pi_.mr $ suppC Z) ≫ p4 (suppC Z)) := inferInstance
  have hB : IsIso $ ((pi_.mr $ suppC Z) ≫ p4 (suppC Z)).stalkMap y :=
    inferInstance
  let _a0 := p4 (pre pi_ $ suppC Z) ≫ pi_
  have hcomp : _a0
      = (pi_.mr $ suppC Z) ≫ p4 (suppC Z) :=
    (morphismRestrict_ι pi_ $ suppC Z).symm
  have hA : IsIso $ _a0.stalkMap y := by
    rwa [hcomp]
  let _a1 := pi_.stalkMap (bsM _c0 y) ≫ _c0.stalkMap y
  have e2 : _a0.stalkMap y
      = _a1 := stalkMap_comp _ _ _
  have hC : IsIso _a1 := by
    rwa [e2] at hA
  have hr : pi_.stalkMap (bsM _c0 y)
      = _a1
        ≫ inv (_c0.stalkMap y) := by
    rw [assoc, m118, comp_id]
  have hfin : IsIso $ pi_.stalkMap $ bsM _c0 y := by
    rw [hr]
    infer_instance
  exact hfin

namespace OrderLocusBlowup

theorem orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf {X X1 : Sch} (pi_ : X1 ⟶ X)
    (Z : ISD X) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (A : ISD X) A1_
    mu_ (hA : exceptionalIdeal pi_ Z ^ mu_ * A1_ = A.comap pi_)
    (hZ : (support Z : Set ↥X) ⊆ orderAtLeastLocus A mu_) :
    orderAtLeastLocus A1_ mu_ ⊆ (⇑pi_.base) ⁻¹' orderAtLeastLocus A mu_ := by
  intro x hx
  by_cases hxZ : bsM pi_ x ∈ spI Z
  exact hZ hxZ
  have := isIso_stalkMap_of_isBlowupAlongIdealSheaf pi_ Z hpi_ x hxZ
  have hle : stalkIdeal (A.comap pi_) x ≤ stalkIdeal A1_ x := by
    rw [← hA, stalkIdeal_mul]
    exact le_trans mul_le_inf inf_le_right
  calc mu_ ≤ orderAt A1_ x := hx
    _ ≤ orderAt (cmI A pi_) x := idealOrder_le_of_le hle
    _ = orderAt A (bsM pi_ x) := orderAt_comap_of_isIso_stalkMap pi_ A x

end OrderLocusBlowup

end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits Opposite

namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch} (s : SequenceOfBlowups X) (S : Set X) (U : Opn X) (hU : Disjoint (U : Set X) S) (hs : s.CentersLieOver S)
include hU hs
theorem isIso_restrict_projectionToBase_of_centersLieOver
    i (hi : i ≤ s.length) :
    IsIso $ projectionToBase s i ∣_ U := by
  revert hi
  induction i with
  | zero =>
    intro _
    have h0 : (homOfLE (zero_le 0) : 0 ⟶ 0).op = 𝟙 (op 0) := rfl
    have : IsIso $ projectionToBase s 0 := by
      rw [SequenceOfBlowups.projectionToBase_def, transitionMap_def, h0, CategoryTheory.Functor.map_id,
        id_comp]
      infer_instance
    infer_instance
  | succ i ih =>
    intro hi
    have hi' := hi
    let _a0 := sbTrS s i ≫ sbPrj s i
    have hcomp : _a0 = sbPrj s (i + 1) :=
      s.transitionMap_comp_projectionToBase $ le_succ i
    let _s0 := sbPrj s i ⁻¹ᵁ U
    have hres := (s.isBlowupAlongIdealSheaf_blowupMorphism i hi').restrict _s0
    have htop : (sbCtr s i).comap _s0.ι = ⊤ := by
      apply p39
      intro x hx
      have hxV : opIb _s0 x
          ∈ ((sbPrj s i ⁻¹ᵁ U : Opn $ sbAt s i) : Set $ sbAt s i) := by
        rw [← q1]
        exact mem_range_self x
      exact mp_ disjoint_left hU hxV $ hs i hi' (opIb _s0 x) hx
    rw [htop] at hres
    have key : IsIso $ _a0 ∣_ U :=
      by
      let g := sbPrj s i
      let V := U
      have := hres.isIso_of_top
      have := ih $ le_of_succ_le hi
      have h : IsIso $ (sbTrS s i) ∣_ (preU g V) ≫ g ∣_ V := inferInstance
      rwa [morphismRestrict_comp]
    rwa [hcomp] at key

theorem isIso_restrict_lastStructMap_of_centersLieOver :
    IsIso $ s.lastStructMap ∣_ U := by
  rw [SequenceOfBlowups.lastStructMap_eq_projectionToBase]
  exact isIso_restrict_projectionToBase_of_centersLieOver s S U hU hs s.length le_rfl
end

theorem isIso_restrict_lastStructMap_smoothLocus {k : Type} [Field k] {X}
    (f : X ⟶ Sp k) [LocallyOfFinitePresentation f] (s : SequenceOfBlowups X)
    (hs : s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X)) :
    IsIso $ s.lastStructMap.mr f.smoothLocus := by
  exact isIso_restrict_lastStructMap_of_centersLieOver s _ f.smoothLocus disjoint_compl_right hs


namespace SequenceOfBlowups

variable {X : Sch}

section
variable (s : SequenceOfBlowups X)
theorem isIso_transitionMap_refl {i} (h : i ≤ i) :
    IsIso $ s.transitionMap h := by
  have he : (homOfLE h).op = 𝟙 (m112 i) := rfl
  have hid : s.transitionMap h = 𝟙 (sbAt s i) := by
    rw [transitionMap_def, he]
    exact s.tower.map_id $ m112 i
  rw [hid]
  infer_instance

theorem isIso_transitionMap_of_center_eq_top {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ length s) (h : ∀ i, a ≤ i → i < b → center s i = ⊤) :
    IsIso $ transitionMap s hab := by
  revert hb h
  induction b, hab using le_induction with
  | base =>
    intro _ _
    exact isIso_transitionMap_refl s _
  | succ b hab ih =>
    intro hb h
    have :=
      ih (le_trans (le_succ b) hb) fun i hi hib => h i hi $ lt_succ_of_lt hib
    have hB := s.isBlowupAlongIdealSheaf_blowupMorphism b $ lt_of_lt_of_le (lt_succ_self b) hb
    rw [h b hab $ lt_succ_self b] at hB
    let _a0 := transitionMap s $ le_succ b
    have : IsIso _a0 := by
      have h4 := hB.isIso_of_top
      rwa [s.blowupMorphism_eq_transitionMap b] at h4
    have h3 : IsIso $ _a0 ≫ transitionMap s hab := inferInstance
    rwa [s.transitionMap_trans hab $ le_succ b] at h3

section
variable (a : ℕ)
theorem exists_le_center_ne_top_or_length_le :
    ∃ i, a ≤ i ∧ (center s i ≠ ⊤ ∨ length s ≤ i) :=
  ⟨max a s.length, le_max_left _ _, m61 $ le_max_right _ _⟩

noncomputable def nextNontrivialIndex : ℕ :=
  @find _ (fun _ => propDecidable _) $ s.exists_le_center_ne_top_or_length_le a

theorem nextNontrivialIndex_spec :
    a ≤ s.nextNontrivialIndex a ∧ (center s (s.nextNontrivialIndex a) ≠ ⊤ ∨ length s ≤ s.nextNontrivialIndex a) :=
  @find_spec _ (fun _ => propDecidable _) $ s.exists_le_center_ne_top_or_length_le a

theorem le_nextNontrivialIndex : a ≤ s.nextNontrivialIndex a :=
  left $ s.nextNontrivialIndex_spec a

theorem center_nextNontrivialIndex_ne_top_or_length_le :
    center s (s.nextNontrivialIndex a) ≠ ⊤ ∨ length s ≤ s.nextNontrivialIndex a :=
  right $ s.nextNontrivialIndex_spec a
end

theorem nextNontrivialIndex_le {a i} (hi : a ≤ i)
    (h : center s i ≠ ⊤ ∨ length s ≤ i) : s.nextNontrivialIndex a ≤ i :=
  @find_min' _ (fun _ => propDecidable _) (s.exists_le_center_ne_top_or_length_le a) i ⟨hi, h⟩

theorem center_eq_top_of_lt_nextNontrivialIndex {a i} (hai : a ≤ i)
    (h : i < s.nextNontrivialIndex a) : center s i = ⊤ := by
  by_contra hc
  exact absurd (s.nextNontrivialIndex_le hai $ m51 hc) $ mpr_ not_le h

theorem nextNontrivialIndex_le_length {a} (h : a ≤ length s) :
    s.nextNontrivialIndex a ≤ length s :=
  s.nextNontrivialIndex_le h $ m61 le_rfl

section
variable (j : ℕ)
noncomputable def nontrivialIndex : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (s.nextNontrivialIndex 0) (fun _ ih => s.nextNontrivialIndex $ ih + 1) j

theorem nontrivialIndex_le_length_of_forall_lt
    (h : ∀ i, i < j → s.nontrivialIndex i < length s) : s.nontrivialIndex j ≤ length s := by
  cases j with
  | zero =>
      exact s.nextNontrivialIndex_le_length $ zero_le _
  | succ j =>
      exact s.nextNontrivialIndex_le_length $ h j $ lt_succ_self j

theorem center_nontrivialIndex_ne_top_or_length_le :
    center s (s.nontrivialIndex j) ≠ ⊤ ∨ length s ≤ s.nontrivialIndex j := by
  cases j with
  | zero => exact s.center_nextNontrivialIndex_ne_top_or_length_le 0
  | succ j => exact s.center_nextNontrivialIndex_ne_top_or_length_le $ s.nontrivialIndex j + 1
end

theorem center_eq_top_of_nontrivialIndex_lt {i j : ℕ} (h1 : s.nontrivialIndex j < i)
    (h2 : i < s.nontrivialIndex (j + 1)) : center s i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex h1 h2

theorem center_eq_top_of_lt_nontrivialIndex_zero {i} (h : i < s.nontrivialIndex 0) :
    center s i = ⊤ :=
  s.center_eq_top_of_lt_nextNontrivialIndex (zero_le i) h

@[simp] theorem nontrivialIndex_zero : s.nontrivialIndex 0 = s.nextNontrivialIndex 0 := rfl

section
variable (j : ℕ)
@[simp] theorem nontrivialIndex_succ :
    s.nontrivialIndex (j + 1) = s.nextNontrivialIndex (s.nontrivialIndex j + 1) := rfl

theorem nontrivialIndex_lt_succ : s.nontrivialIndex j < s.nontrivialIndex (j + 1) := by
  have h := s.le_nextNontrivialIndex $ s.nontrivialIndex j + 1
  rwa [nontrivialIndex_succ]

theorem succ_le_nontrivialIndex_succ :
    s.nontrivialIndex j + 1 ≤ s.nontrivialIndex (j + 1) :=
  s.nontrivialIndex_lt_succ j
end

theorem nontrivialIndex_strictMono : StrictMono s.nontrivialIndex :=
  strictMono_nat_of_lt_succ s.nontrivialIndex_lt_succ

theorem le_nontrivialIndex j : j ≤ s.nontrivialIndex j :=
  s.nontrivialIndex_strictMono.le_apply

theorem nontrivialIndex_monotone : Monotone s.nontrivialIndex :=
  s.nontrivialIndex_strictMono.monotone

theorem exists_length_le_nontrivialIndex : ∃ j, length s ≤ s.nontrivialIndex j :=
  ⟨length s, s.le_nontrivialIndex s.length⟩

noncomputable def lengthWithoutIsoBlowups : ℕ :=
  @find _ (fun _ => propDecidable _) s.exists_length_le_nontrivialIndex

section
variable {j : ℕ}
theorem nontrivialIndex_lt_length (h : j < s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j < length s := by
  exact mp_ not_le $ @find_min _ (fun _ => propDecidable _) s.exists_length_le_nontrivialIndex j h

theorem center_nontrivialIndex_ne_top (h : j < s.lengthWithoutIsoBlowups) :
    center s (s.nontrivialIndex j) ≠ ⊤ := by
  rcases s.center_nontrivialIndex_ne_top_or_length_le j with hc | hc
  exact hc
  exact absurd hc $ mpr_ not_le $ s.nontrivialIndex_lt_length h

theorem nontrivialIndex_le_length (h : j ≤ s.lengthWithoutIsoBlowups) :
    s.nontrivialIndex j ≤ length s := by
  cases j with
  | zero => exact s.nextNontrivialIndex_le_length $ zero_le _
  | succ i =>
    exact s.nextNontrivialIndex_le_length $ s.nontrivialIndex_lt_length $ lt_of_lt_of_le (lt_succ_self i) h

theorem isIso_transitionMap_nontrivialIndex_succ (h : j < s.lengthWithoutIsoBlowups) :
    IsIso $ transitionMap s $ s.succ_le_nontrivialIndex_succ j := by
  refine s.isIso_transitionMap_of_center_eq_top (s.succ_le_nontrivialIndex_succ j)
    (s.nontrivialIndex_le_length $ succ_le_of_lt h) ?_
  intro i hi hib
  exact s.center_eq_top_of_nontrivialIndex_lt (lt_of_succ_le hi) hib
end

theorem length_le_nontrivialIndex_lengthWithoutIsoBlowups :
    length s ≤ s.nontrivialIndex s.lengthWithoutIsoBlowups :=
  @find_spec _ (fun _ => propDecidable _) s.exists_length_le_nontrivialIndex

theorem nontrivialIndex_lengthWithoutIsoBlowups : s.nontrivialIndex s.lengthWithoutIsoBlowups = length s := by
  refine le_antisymm (nontrivialIndex_le_length_of_forall_lt s s.lengthWithoutIsoBlowups ?_)
    s.length_le_nontrivialIndex_lengthWithoutIsoBlowups
  intro i hi
  have hmin := @find_min _ (fun _ => propDecidable _)
    s.exists_length_le_nontrivialIndex i hi
  exact mp_ not_le hmin

theorem isIso_transitionMap_nontrivialIndex_zero :
    IsIso $ transitionMap s $ zero_le $ s.nontrivialIndex 0 := by
  refine s.isIso_transitionMap_of_center_eq_top (zero_le $ s.nontrivialIndex 0) (s.nextNontrivialIndex_le_length $ zero_le _) ?_
  intro i _ hi
  exact s.center_eq_top_of_lt_nontrivialIndex_zero hi

noncomputable def objNontrivialIndexZeroIso : schemeAt s (s.nontrivialIndex 0) ≅ X :=
  haveI : IsIso $ transitionMap s $ zero_le $ s.nontrivialIndex 0 := s.isIso_transitionMap_nontrivialIndex_zero
  (asIso $ s.transitionMap $ zero_le $ s.nontrivialIndex 0).trans s.isoZero

theorem objNontrivialIndexZeroIso_hom :
    s.objNontrivialIndexZeroIso.hom = projectionToBase s (s.nontrivialIndex 0) := by
  rw [projectionToBase_def]
  rfl

noncomputable def towerWithoutIsoBlowups : ℕᵒᵖ ⥤ Sch :=
  (Monotone.functor s.nontrivialIndex_monotone).op ⋙ s.tower

theorem isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map i (hi : i < s.lengthWithoutIsoBlowups) :
    IsBlowupAlongIdealSheaf (s.towerWithoutIsoBlowups.map (homOfLE $ Nat.le_succ i).op) $ center s $ s.nontrivialIndex i := by
  let _a0 := s.transitionMap $ s.succ_le_nontrivialIndex_succ i
  have := s.isIso_transitionMap_nontrivialIndex_succ hi
  have hcomp := (s.isBlowupAlongIdealSheaf_blowupMorphism (s.nontrivialIndex i) $ s.nontrivialIndex_lt_length hi).iso_hom_comp $ asIso _a0
  let _a1 := s.transitionMap $ s.nontrivialIndex_monotone $ le_succ i
  have heq : isoH (asIso _a0) ≫ transitionMapSucc s (s.nontrivialIndex i)
      = _a1 := by
    rw [blowupMorphism_eq_transitionMap]
    exact s.transitionMap_trans (le_succ $ s.nontrivialIndex i) $ s.succ_le_nontrivialIndex_succ i
  rwa [heq] at hcomp

noncomputable def withoutIsoBlowups : SequenceOfBlowups X where
  length := s.lengthWithoutIsoBlowups
  tower := s.towerWithoutIsoBlowups
  isoZero := s.objNontrivialIndexZeroIso
  center := fun j => center s $ s.nontrivialIndex j
  isBlowup := s.isBlowupAlongIdealSheaf_towerWithoutIsoBlowups_map

theorem withoutIsoBlowups_transitionMap {j j'} (h : j ≤ j') :
    s.withoutIsoBlowups.transitionMap h = s.transitionMap (s.nontrivialIndex_monotone h) := by
  rw [transitionMap_def, transitionMap_def]
  rfl

theorem withoutIsoBlowups_center_ne_top {j : ℕ} (h : j < s.withoutIsoBlowups.length) :
    s.withoutIsoBlowups.center j ≠ ⊤ := by
  exact s.center_nontrivialIndex_ne_top h

theorem withoutIsoBlowups_blowupMorphism (j : ℕ) :
    s.withoutIsoBlowups.transitionMapSucc j = s.transitionMap (s.nontrivialIndex_monotone $ le_succ j) := by
  rw [blowupMorphism_eq_transitionMap, withoutIsoBlowups_transitionMap]

theorem withoutIsoBlowups_projectionToBase_eq_nontrivialIndex (j : ℕ) :
    s.withoutIsoBlowups.projectionToBase j = projectionToBase s (s.nontrivialIndex j) := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = sbPrj s (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  rw [projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
  exact s.transitionMap_comp_projectionToBase _

theorem withoutIsoBlowups_centersLieOver {S : Set X} (h : s.CentersLieOver S) :
    s.withoutIsoBlowups.CentersLieOver S := by
  intro j hj x hx
  have h2 := h (s.nontrivialIndex j) (s.nontrivialIndex_lt_length hj) x hx
  rwa [withoutIsoBlowups_projectionToBase_eq_nontrivialIndex]

@[simp] theorem withoutIsoBlowups_length : s.withoutIsoBlowups.length = s.lengthWithoutIsoBlowups := rfl


@[simp] theorem withoutIsoBlowups_center (j : ℕ) :
    s.withoutIsoBlowups.center j = center s (s.nontrivialIndex j) := rfl

theorem projectionToBase_eq_eqToHom_comp {a b : ℕ} (h : a = b) :
    projectionToBase s a = eqToHom (congrArg s.schemeAt h) ≫ projectionToBase s b := by
  subst h
  simp

theorem withoutIsoBlowups_isoObjZero : s.withoutIsoBlowups.isoZero = s.objNontrivialIndexZeroIso := rfl

theorem withoutIsoBlowups_lastObj : s.withoutIsoBlowups.lastObj = s.lastObj :=
  congrArg s.schemeAt s.nontrivialIndex_lengthWithoutIsoBlowups

theorem withoutIsoBlowups_lastStructMap :
    s.withoutIsoBlowups.lastStructMap = eqToHom s.withoutIsoBlowups_lastObj ≫ s.lastStructMap := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = sbPrj s (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  have h1 : s.withoutIsoBlowups.lastStructMap = sbPrj s (s.nontrivialIndex s.withoutIsoBlowups.length) := by
    rw [lastStructMap_eq_projectionToBase, projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
    exact s.transitionMap_comp_projectionToBase _
  rw [h1, lastStructMap_eq_projectionToBase]
  exact projectionToBase_eq_eqToHom_comp s s.nontrivialIndex_lengthWithoutIsoBlowups
end

end SequenceOfBlowups

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable {X X1 : Sch} (pi_ : X1 ⟶ X) (Z D : ISD X)
def strictTransformOpens :
    (subscheme $ D.comap pi_).Opens :=
  subschemeι (D.comap pi_) ⁻¹ᵁ (Z.comap pi_).support.compl

theorem coe_strictTransformOpens :
    ((strictTransformOpens pi_ Z D : (subscheme $ D.comap pi_).Opens) :
        Set $ subscheme $ D.comap pi_) =
      ⇑(D.comap pi_).subschemeι.base ⁻¹' ((Z.comap pi_).support.compl : Set X1) := rfl

def strictTransformio :
    toScheme (strictTransformOpens pi_ Z D) ⟶ X1 :=
  Scheme.Opens.i (strictTransformOpens pi_ Z D) ≫ subschemeι (D.comap pi_)

theorem strictTransformio_eq_io_comp_subschemeio :
    strictTransformio pi_ Z D =
      Scheme.Opens.i (strictTransformOpens pi_ Z D) ≫ (D.comap pi_).si := rfl


theorem strictTransform_eq_ker_strictTransformio :
    strictTransform pi_ Z D = (strictTransformio pi_ Z D).ker := rfl

theorem comap_le_strictTransform :
    D.comap pi_ ≤ strictTransform pi_ Z D := by
  rw [strictTransform_eq_ker_strictTransformio, strictTransformio_eq_io_comp_subschemeio]
  calc cmI D pi_ = (cmI D pi_).subschemeι.ker :=
        (q2 _).symm
    _ ≤ _ := le_ker_comp _ _
end

section
variable {T : Sch} (K : ISD T) (V : Opn T)
theorem ker_morphismRestrict_subschemeio :
    (subschemeι K ∣_ V).ker = K.comap (Scheme.Opens.ι V) := by
  show (siI K ∣_ V).ker = (fst (p4 V) K.si).ker
  rw [← (isPullback_morphismRestrict K.si V).isoPullback_hom_fst, ker_comp_of_isIso]

theorem exists_isIso_subschemeio_preimage_comap :
    ∃ e : toScheme (subschemeι K ⁻¹ᵁ V) ⟶ subscheme (K.comap $ Scheme.Opens.i V),
      IsIso e ∧ e ≫ subschemeι (K.comap $ Scheme.Opens.i V) = subschemeι K ∣_ V := by
  let _a0 := K.comap $ p4 V
  have hk : (K.si.mr V).ker = _a0.subschemeι.ker := by
    rw [ker_morphismRestrict_subschemeio, q2]
  exact ⟨m64 _a0.si
      (K.si.mr V) $ le_of_eq hk.symm, isIso_of_ker_eq (K.si.mr V) _a0.si _ (m154 _ _ _) hk, m154 _ _ _⟩

theorem ker_io_preimage_comp_subschemeio_eq_ker_comap :
    (Scheme.Opens.i (subschemeι K ⁻¹ᵁ V) ≫ subschemeι K).ker =
      (subschemeι (K.comap $ Scheme.Opens.i V) ≫ Scheme.Opens.i V).ker := by
  obtain ⟨e, he, hfac⟩ := exists_isIso_subschemeio_preimage_comap K V
  rw [← morphismRestrict_ι K.si V, ← hfac, assoc]
  exact ker_comp_of_isIso e _
end

section
variable {X X1 : Sch}
theorem isReduced_subscheme_strictTransform (pi_ : X1 ⟶ X)
    (Z D : ISD X) (h : IsBlowupAlongIdealSheaf pi_ Z) [IsReduced D.subscheme]
    [QuasiCompact $ strictTransformio pi_ Z D] :
    IsReduced (strictTransform pi_ Z D).subscheme := by
  have h1 := h.restrict $ suppC Z
  rw [comap_io_support_compl_eq_top Z] at h1
  have := h1.isIso_of_top
  have hsupp : (cmI Z pi_).support.compl = pre pi_ Z.support.compl := by
    rw [m19]
    rfl
  let _m0 := pre pi_ $ suppC Z
  let _a0 := cmI D $ p4 $ suppC Z
  let _a1 := cmI D pi_
  have hcc : _a1.comap (p4 _m0)
      = _a0.comap (pi_.mr $ suppC Z) := by
    rw [← comap_comp, ← comap_comp,
      morphismRestrict_ι]
  obtain ⟨e1_, he1_, -⟩ := exists_isIso_subschemeio_preimage_comap (cmI D pi_) _m0
  obtain ⟨e2_, he2_, -⟩ :=
    exists_iso_subscheme_comap_of_isIso (pi_.mr $ suppC Z)
      _a0
  obtain ⟨e3_, he3, -⟩ := exists_isIso_subschemeio_preimage_comap D $ suppC Z
  have := he1_
  have := he2_
  have := he3
  have :=
    isReduced_of_isOpenImmersion $ p4 $ D.si.pre $ suppC Z
  have :=
    isReduced_of_isOpenImmersion $ inv e3_
  have :=
    isReduced_of_isOpenImmersion e2_
  have : IsReduced (_a1.comap $ p4 _m0).subscheme := by
    rw [hcc]
    infer_instance
  have : IsReduced (strictTransformOpens pi_ Z D).toScheme := by
    have hrw : strictTransformOpens pi_ Z D
        = siPre _a1 _m0 := by
      show siI _a1 ⁻¹ᵁ (cmI Z pi_).support.compl
          = siPre _a1 _m0
      rw [hsupp]
    rw [hrw]
    exact isReduced_of_isOpenImmersion e1_
  rw [strictTransform_eq_ker_strictTransformio]
  exact isReduced_subscheme_ker _

theorem strictTransform_eq_ker_restrict (f : X1 ⟶ X)
    (W D1 : ISD X) :
    strictTransform f W D1 =
      (((D1.comap $ Scheme.Opens.i W.support.compl).comap
            (f.mr W.support.compl)).subschemeι ≫
          Scheme.Opens.i (pre f W.support.compl)).ker := by
  have hUV : (cmI W f).support.compl = pre f W.support.compl := by
    rw [m19]
    rfl
  let _a0 := cmI D1 f
  have hcomap : _a0.comap (p4 $ pre f $ suppC W)
      = (cmI D1 $ p4 $ suppC W).comap (f.mr $ suppC W) := by
    rw [← comap_comp, ← comap_comp,
      morphismRestrict_ι]
  rw [strictTransform_eq_ker_strictTransformio, strictTransformio_eq_io_comp_subschemeio]
  show (p4 (siI _a0 ⁻¹ᵁ (cmI W f).support.compl) ≫
      siI _a0).ker = _
  rw [hUV, ker_io_preimage_comp_subschemeio_eq_ker_comap, hcomap]

theorem strictTransform_congr_of_comap_io_eq (f : X1 ⟶ X)
    (W D1 D2_ : ISD X)
    (h : D1.comap (Scheme.Opens.i W.support.compl) =
      D2_.comap (Scheme.Opens.i W.support.compl)) :
    strictTransform f W D1 = strictTransform f W D2_ := by
  rw [strictTransform_eq_ker_restrict f W D1, strictTransform_eq_ker_restrict f W D2_, h]
end

theorem comap_ker_subschemeio_comp {A B : Sch} (K : ISD A) (f : A ⟶ B)
    [IsOpenImmersion f] [QuasiCompact K.si] [QuasiCompact $ subschemeι K ≫ f] :
    (subschemeι K ≫ f).ker.comap f = K := by
  rw [comap_ker_comp_of_isOpenImmersion, q2]

theorem range_comp_eq_image_range {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) :
    range ⇑(f ≫ g) = ⇑g '' range ⇑f := by
  ext x
  simp [range_comp]

section
variable {X X1 : Sch} (pi_ : X1 ⟶ X) (Z D : ISD X) [QuasiCompact (strictTransformio pi_ Z D)]
theorem support_strictTransform_eq_closure_preimage :
    (support (strictTransform pi_ Z D) : Set X1) =
      closure (⇑pi_.base ⁻¹' ((support D : Set X) \ (support Z : Set X))) := by
  have h1 : ((suppC (cmI Z pi_) : Opn X1) : Set X1) =
      (preimage pi_.base Z.support)ᶜ := by simp_all
  have h2 : ((spI (cmI D pi_) : Closeds X1) : Set X1) =
      preimage pi_.base D.support := by simp_all
  rw [strictTransform_eq_ker_strictTransformio, support_ker]
  congr 1
  rw [strictTransformio_eq_io_comp_subschemeio, range_comp_eq_image_range, q1,
    coe_strictTransformOpens, image_preimage_eq_inter_range,
    q5, h1, h2]
  ext x
  simp [mem_inter_iff, mem_compl_iff, mem_preimage, mem_sdiff]
  tauto

theorem support_strictTransform_eq_closure_sdiff :
    (support (strictTransform pi_ Z D) : Set X1) =
      closure ((support (D.comap pi_) : Set X1) \ (support (Z.comap pi_) : Set X1)) := by
  have h1 : ((spI (cmI Z pi_) : Closeds X1) : Set X1) =
      preimage pi_.base Z.support := by simp_all
  have h2 : ((spI (cmI D pi_) : Closeds X1) : Set X1) =
      preimage pi_.base D.support := by simp_all
  rw [support_strictTransform_eq_closure_preimage pi_ Z D, h1, h2, preimage_sdiff]
end

theorem ker_eq_ker_of_isIso_comp {A B T : Sch} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    [IsIso e] (h : e ≫ g = f) : f.ker = g.ker := by
  subst h
  exact ker_comp_of_isIso e g

theorem isBlowupAlongIdealSheaf_of_isIso_comp {X A B : Sch} (f : A ⟶ X) (g : B ⟶ X) (e : A ⟶ B)
    [IsIso e] (hfac : e ≫ g = f) (I : ISD X) (hg : IsBlowupAlongIdealSheaf g I) :
    IsBlowupAlongIdealSheaf f I := by
  obtain ⟨hcart, huniv⟩ := hg
  have h1 : I.comap f = (I.comap g).comap e := by
    rw [← comap_comp, hfac]
  constructor
  rw [h1]
  exact hcart.comap_of_isOpenImmersion e
  intro Y q hq
  obtain ⟨t, ht, huniq⟩ := huniv Y q hq
  refine ⟨t ≫ inv e, ?_, ?_⟩
  show (t ≫ inv e) ≫ f = q
  rwa [← hfac, assoc, IsIso.inv_hom_id_assoc]
  intro y hy
  have hye : y ≫ e = t := by simp_all
  rw [← hye, assoc, m118, comp_id]

private theorem ker_ideal_eq_ker_app {W Z : Sch} (g : W ⟶ Z) [QuasiCompact g]
    (U : Z.affineOpens) :
    (ker g).ideal U = RingHom.ker (CommRingCat.Hom.hom $ g.app U.1) := by
  simp

theorem ker_comap_io_eq_ker_morphismRestrict {W T : Sch} (m : W ⟶ T) [QuasiCompact m]
    (V : Opn T) :
    (ker m).comap (Scheme.Opens.ι V) = ker (m ∣_ V) := by
  refine m29 ?_
  funext P
  let _s0 := p4 V ''ᵁ P.1
  have hQaff :=
    P.2.image_of_isOpenImmersion $ p4 V
  have hpre :=
    (p4 V).preimage_image_eq P.1
  have e := hpre.ge
  have hpre2 : ((mrU m V) ⁻¹ᵁ P.1)
      = Scheme.Opens.ι (m ⁻¹ᵁ V) ⁻¹ᵁ (m ⁻¹ᵁ _s0) := by
    rw [← comp_preimage, ← morphismRestrict_ι, comp_preimage, hpre]
  have hle : preU m _s0 ≤ preU m V := fun x hx => (Scheme.Opens.ι_image_le V P.1) hx
  have himg : p4 (preU m V) ''ᵁ ((mrU m V) ⁻¹ᵁ P.1)
      = preU m _s0 := by
    rw [hpre2]
    refine le_antisymm ?_ ?_
    rintro x ⟨y, hy, rfl⟩
    exact hy
    intro x hx
    exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  have hbij := bijective_appLE_of_image_eq (p4 V)
    _s0 P.1 e rfl
  let _s1 := p4 $ preU m V
  have hinj := an1 $ bijective_appLE_of_image_eq _s1
    (preU m _s0) (preU (mrU m V) P.1) hpre2.le himg
  have hsq : appLE (p4 V) _s0 P.1 e ≫
        (mrU m V).app P.1
      = m.app _s0 ≫
        appLE _s1
          (preU m _s0) (preU (mrU m V) P.1) hpre2.le := by
    rw [Scheme.Hom.app_eq_appLE $ mrU m V, Scheme.Hom.app_eq_appLE m,
      m91 (mrU m V) (p4 V) _s0 P.1
        (preU (mrU m V) P.1) e le_rfl,
      m91 _s1 m _s0
        (preU m _s0) (preU (mrU m V) P.1) le_rfl hpre2.le]
    exact Scheme.Hom.appLE_congr_hom (morphismRestrict_ι m V) ..
  have hsqr : ∀ x, (m4 $ (mrU m V).app P.1)
        ((m4
          (appLE (p4 V) _s0 P.1 e)) x)
      = m4 (appLE _s1
          (preU m _s0) (preU (mrU m V) P.1) hpre2.le)
        ((m4 $ m.app _s0) x) := by
    intro x
    simpa only [hom_comp, m82] using (congrArg (fun mm => (m4 mm) x) hsq)
  rw [comap_ideal_eq_map_appLE _ (p4 V)
      ⟨p4 V ''ᵁ P.1, hQaff⟩ P e,
    ker_ideal_eq_ker_app m ⟨p4 V ''ᵁ P.1, hQaff⟩, ker_ideal_eq_ker_app (mrU m V) P]
  dsimp only
  refine le_antisymm ?_ ?_
  rw [map_le_iff_le_comap]
  intro x hx
  rw [mem_comap, mem_ker, hsqr x]
  rw [mem_ker] at hx
  rw [hx, map_zero]
  intro y hy
  rw [mem_ker] at hy
  obtain ⟨x, rfl⟩ := an2 hbij y
  refine mem_map_of_mem _ ?_
  rw [mem_ker]
  apply hinj
  rw [← hsqr x, hy, map_zero]

theorem ker_comap_io_eq_ker_of_isIso_comp {W T S : Sch} (m : W ⟶ T) [QuasiCompact m]
    (V : Opn T) (n : S ⟶ toScheme V) (e : S ⟶ toScheme (pre m V)) [IsIso e]
    (h : e ≫ (m.mr V) = n) :
    (ker m).comap (Scheme.Opens.i V) = ker n := by
  rw [ker_comap_io_eq_ker_morphismRestrict m V, ker_eq_ker_of_isIso_comp n (mrU m V) e h]

theorem strictTransform_top {X' X : Sch} (f : X' ⟶ X) (Z : ISD X) :
    strictTransform f Z (⊤ : ISD X) = ⊤ := by
  have h := comap_le_strictTransform f Z ⊤
  rw [comap_top] at h
  exact le_antisymm le_top h

theorem isCompact_of_subset_noetherianSpace {al_ : Type} [TopologicalSpace al_] (s : Set al_)
    [NoetherianSpace s] (t : Set al_) (ht : t ⊆ s) : IsCompact t := by
  let _m0 := preimage (m161 : s → al_) t
  have h1 : IsCompact _m0 := NoetherianSpace.isCompact _
  have h2 := h1.image continuous_subtype_val
  have h3 : m161 '' _m0 = t := by
    apply m15
    rintro x ⟨y, hy, rfl⟩
    exact hy
    intro x hx
    exact ⟨⟨x, ht hx⟩, hx, rfl⟩
  rwa [h3] at h2

theorem isCompact_of_subset_isCompact {B : Sch} [IsLocallyNoetherian B]
    {U : Set B} (hc : IsCompact U) {T : Set B} (hT : T ⊆ U) : IsCompact T := by
  have hcov : U ⊆ ⋃ W : affO B, (W.1 : Set B) := by
    intro x _
    have hx : x ∈ (⊤ : Opn B) := mem_univ x
    rw [← iSup_affineOpens_eq_top B] at hx
    obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hx
    exact mpr_ mem_iUnion ⟨W, hW⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : affO B => W.1) (·.1.isOpen) hcov
  have hTeq : T = ⋃ W ∈ s, (T ∩ W.1) := by
    apply m15
    intro x hx
    obtain ⟨W, hWs, hxW⟩ := Set.mem_iUnion₂.mp $ hs $ hT hx
    exact mem_biUnion (hWs) ⟨hx, hxW⟩
    intro x hx
    obtain ⟨W, -, hx'⟩ := Set.mem_iUnion₂.mp hx
    exact hx'.1
  rw [hTeq]
  refine (finite_toSet s).isCompact_biUnion ?_
  intro W _
  have : IsNoetherianRing $ pObj B $ m112 W.1 :=
    m188 W
  have : NoetherianSpace (W.1 : Set B) := noetherianSpace_of_isAffineOpen W.1 W.2
  exact isCompact_of_subset_noetherianSpace (W.1 : Set B) (T ∩ (W.1 : Set B)) inter_subset_right

theorem quasiCompact_of_isInducing {A B : Sch} [IsLocallyNoetherian B]
    (f : A ⟶ B) (hf : Topology.IsInducing ⇑f.base) : QuasiCompact f := by
  refine ⟨fun U _ hU' => ?_⟩
  exact hf.isCompact_iff.mpr $ isCompact_of_subset_isCompact hU' $ image_preimage_subset _ _

theorem quasiCompact_strictTransformio_of_isLocallyNoetherian {X X1 : Sch} (pi_ : X1 ⟶ X)
    (Z D : ISD X) [IsLocallyNoetherian X1] :
    QuasiCompact $ strictTransformio pi_ Z D := by
  refine quasiCompact_of_isInducing _ ?_
  let _a0 := p4 $ strictTransformOpens pi_ Z D
  have heq : (strictTransformio pi_ Z D).base
      = (cmI D pi_).subschemeι.base ∘
        _a0.base := rfl
  rw [heq]
  exact ((cmI D pi_).subschemeι.isEmbedding.toIsInducing).comp $ _a0.isEmbedding.toIsInducing

instance instQuasiCompactStrictTransformMorphism {X X1 : Sch} (pi_ : X1 ⟶ X)
    (Z D : ISD X) [IsLocallyNoetherian X1] :
    QuasiCompact $ strictTransformio pi_ Z D :=
  quasiCompact_strictTransformio_of_isLocallyNoetherian pi_ Z D


namespace SequenceOfBlowups

variable {X Y : Sch}

section
variable (s : SequenceOfBlowups X) (t : SequenceOfBlowups Y) (hlen : length s = length t)
include hlen
section
variable (htriv : ∀ i, i < length s → (center s i = ⊤ ↔ center t i = ⊤))
include htriv
private theorem nextNontrivialIndex_le_of_center_eq_top_iff (a : ℕ) :
    s.nextNontrivialIndex a ≤ t.nextNontrivialIndex a := by
  refine s.nextNontrivialIndex_le (t.le_nextNontrivialIndex a) ?_
  rcases m63 (t.nextNontrivialIndex a) s.length with h | h
  refine m51 ?_
  have hlt : t.nextNontrivialIndex a < length t := by rw [← hlen]
                                                      exact h
  rcases t.center_nextNontrivialIndex_ne_top_or_length_le a with hd | hd
  intro hc
  exact hd $ (htriv _ h).1 hc
  exact absurd hd $ mpr_ not_le hlt
  exact m61 h

theorem nextNontrivialIndex_congr_of_center_eq_top_iff (a : ℕ) :
    s.nextNontrivialIndex a = t.nextNontrivialIndex a := by
  refine le_antisymm (nextNontrivialIndex_le_of_center_eq_top_iff s t hlen htriv a) ?_
  refine nextNontrivialIndex_le_of_center_eq_top_iff t s hlen.symm ?_ a
  intro i hi
  refine (htriv i ?_).symm
  rwa [hlen]

theorem nontrivialIndex_congr_of_center_eq_top_iff :
    s.nontrivialIndex = t.nontrivialIndex := by
  funext j
  induction j with
  | zero =>
      rw [nontrivialIndex_zero, nontrivialIndex_zero]
      exact nextNontrivialIndex_congr_of_center_eq_top_iff s t hlen htriv 0
  | succ j ih =>
      rw [nontrivialIndex_succ, nontrivialIndex_succ, ih]
      exact nextNontrivialIndex_congr_of_center_eq_top_iff s t hlen htriv _
end

theorem lengthWithoutIsoBlowups_le_of_nontrivialIndex_eq (hret : s.nontrivialIndex = t.nontrivialIndex) :
    s.lengthWithoutIsoBlowups ≤ t.lengthWithoutIsoBlowups := by
  by_contra hc
  push Not at hc
  have h2 := t.length_le_nontrivialIndex_lengthWithoutIsoBlowups
  rw [← hret, ← hlen] at h2
  exact absurd h2 $ mpr_ not_le $ s.nontrivialIndex_lt_length hc

theorem lengthWithoutIsoBlowups_congr_of_center_eq_top_iff
    (htriv : ∀ i, i < length s → (center s i = ⊤ ↔ center t i = ⊤)) :
    s.lengthWithoutIsoBlowups = t.lengthWithoutIsoBlowups := by
  have hret := nontrivialIndex_congr_of_center_eq_top_iff s t hlen htriv
  exact le_antisymm (lengthWithoutIsoBlowups_le_of_nontrivialIndex_eq s t hlen hret)
    (lengthWithoutIsoBlowups_le_of_nontrivialIndex_eq t s hlen.symm hret.symm)
end

end SequenceOfBlowups

theorem preimage_inv_eq {P Q : Sch} (m : P ⟶ Q) [IsIso m] {V : Opn Q}
    {U : Opn P} (h : m ⁻¹ᵁ V = U) : (inv m) ⁻¹ᵁ U = V := by
  rw [← h, ← comp_preimage, m117, id_preimage]

section
variable {A B C : Sch}
section
variable (e : C ⟶ B) [IsIso e] (pi_ : B ⟶ A)
theorem exists_isIso_strictTransformOpens_of_isIso
    (Z D : ISD A) :
    ∃ ph_ : toScheme (strictTransformOpens (e ≫ pi_) Z D) ⟶
        toScheme (strictTransformOpens pi_ Z D),
      IsIso ph_ ∧ ph_ ≫ strictTransformio pi_ Z D
        = strictTransformio (e ≫ pi_) Z D ≫ e := by
  obtain ⟨mu_, hmuiso, hmufac⟩ : ∃ m : subscheme (D.comap $ e ≫ pi_) ⟶ subscheme (D.comap pi_), IsIso m ∧ m ≫ subschemeι (D.comap pi_) = subschemeι (D.comap $ e ≫ pi_) ≫ e := by
    rw [comap_comp]
    exact exists_iso_subscheme_comap_of_isIso e $ cmI D pi_
  let _a0 := cmI D $ e ≫ pi_
  have hbase : ∀ T, mu_.base ⁻¹' ((cmI D pi_).subschemeι.base ⁻¹' T)
      = _a0.subschemeι.base ⁻¹' (pIm e.base T) := by
    intro T
    simpa [Set.preimage_comp] using (congrArg (fun m : subS _a0 ⟶ B => preimage m.base T) hmufac)
  have hsupp : ((suppC (cmI Z $ e ≫ pi_) : Opn C) : Set C)
      = e.base ⁻¹' ((suppC (cmI Z pi_) : Opn B) : Set B) := by simp_all
  have hset : mu_.base ⁻¹' ((strictTransformOpens pi_ Z D :
        (subS $ cmI D pi_).Opens) : Set $ subS $ cmI D pi_)
      = ((strictTransformOpens (e ≫ pi_) Z D :
        Opn $ subS _a0) : Set $ subS _a0) := by
    rw [coe_strictTransformOpens, coe_strictTransformOpens, hbase, hsupp]
  have hopens : preU mu_ (strictTransformOpens pi_ Z D)
      = strictTransformOpens (e ≫ pi_) Z D := m55 hset
  refine ⟨mu_.resLE (strictTransformOpens pi_ Z D) (strictTransformOpens (e ≫ pi_) Z D)
      hopens.ge, ?_, ?_⟩
  refine ⟨(inv mu_).resLE (strictTransformOpens (e ≫ pi_) Z D)
    (strictTransformOpens pi_ Z D) (preimage_inv_eq mu_ hopens).ge, ?_, ?_⟩
  rw [← cancel_mono $ p4 $ strictTransformOpens (e ≫ pi_) Z D,
    assoc, q4, ← assoc, q4,
    assoc, m118, comp_id, id_comp]
  rw [← cancel_mono $ p4 $ strictTransformOpens pi_ Z D,
    assoc, q4, ← assoc, q4,
    assoc, m117, comp_id, id_comp]
  rw [strictTransformio_eq_io_comp_subschemeio, strictTransformio_eq_io_comp_subschemeio, ← assoc,
    q4, assoc, hmufac, ← assoc]
end

theorem strictTransform_isIso_comp [IsLocallyNoetherian B]
    [IsLocallyNoetherian C] (e : C ⟶ B) [IsIso e] (pi_ : B ⟶ A) (Z D : ISD A)
    (_hπ : IsBlowupAlongIdealSheaf pi_ Z) :
    strictTransform (e ≫ pi_) Z D = (strictTransform pi_ Z D).comap e := by
  let _a0 := strictTransformio (e ≫ pi_) Z D
  have : QuasiCompact _a0 := inferInstance
  have : QuasiCompact $ _a0 ≫ e := inferInstance
  obtain ⟨ph_, hphiso, hphfac⟩ := exists_isIso_strictTransformOpens_of_isIso e pi_ Z D
  rw [strictTransform_eq_ker_strictTransformio, strictTransform_eq_ker_strictTransformio, ← comap_ker_comp_of_isOpenImmersion _a0 e, ker_eq_ker_of_isIso_comp _ _ ph_ hphfac]
end

theorem strictTransform_top_eq_comap {A B : Sch} (pi_ : B ⟶ A) (D : ISD A)
    [QuasiCompact $ strictTransformio pi_ ⊤ D] :
    strictTransform pi_ ⊤ D = D.comap pi_ := by
  let _c0 := p4 $ strictTransformOpens pi_ ⊤ D
  have hc : ((suppC (cmI (⊤ : ISD A) pi_) : Opn B) : Set B) = univ := by simp_all
  have hrange : ∀ g : subS (cmI D pi_) ⟶ subS (cmI D pi_),
      range g.base
        ⊆ range _c0.base := by
    intro g
    rw [q1, coe_strictTransformOpens, hc, preimage_univ]
    exact subset_univ _
  have : IsIso _c0 := by
    refine ⟨lift _c0 (𝟙 _)
      (hrange $ 𝟙 _), ?_, lift_fac _ _ _⟩
    rw [← cancel_mono _c0, assoc,
      lift_fac, comp_id, id_comp]
  rw [strictTransform_eq_ker_strictTransformio, strictTransformio_eq_io_comp_subschemeio,
    ker_comp_of_isIso, q2]


section
variable {Y : Sch}
section
variable (F T : ISD Y)
def saturationOpens : (subscheme T).Opens :=
  subschemeι T ⁻¹ᵁ F.support.compl

theorem coe_saturationOpens :
    ((saturationOpens F T : (subscheme T).Opens) : Set $ subscheme T) =
      ⇑T.subschemeι.base ⁻¹' ((F.support.compl : Opn Y) : Set Y) := rfl

theorem mem_saturationOpens
    (z : ↥(subscheme T)) :
    z ∈ ((saturationOpens F T : (subscheme T).Opens) : CSet $ subscheme T)
      ↔ subschemeι T z ∉ ((support F : TopologicalSpace.Closeds ↥Y) : Set ↥Y) := by
  rw [coe_saturationOpens]
  exact m22

def saturationio :
    toScheme (saturationOpens F T) ⟶ Y :=
  Scheme.Opens.ι (saturationOpens F T) ≫ subschemeι T

theorem saturationio_eq_io_comp_subschemeio :
    saturationio F T = Scheme.Opens.ι (saturationOpens F T) ≫ subschemeι T := rfl

def saturation : ISD Y :=
  (saturationio F T).ker

theorem saturation_eq_ker_saturationio :
    saturation F T = (saturationio F T).ker := rfl

theorem range_saturationio :
    range ⇑(saturationio F T) = (support T : Set ↥Y) \ (support F : Set ↥Y) := by
  ext y
  constructor
  rintro ⟨p, rfl⟩
  have hp : p4 (saturationOpens F T) p ∈
      ((saturationOpens F T : Opn $ subS T) : CSet $ subS T) := by
    rw [← q1]
    exact mem_range_self p
  rw [coe_saturationOpens] at hp
  show siI T (p4 (saturationOpens F T) p) ∈
      (spI T : Set Y) \ (spI F : Set Y)
  refine ⟨?_, hp⟩
  rw [← range_subschemeι]
  exact mem_range_self _
  rintro ⟨hy1, hy2⟩
  rw [← q5] at hy1
  obtain ⟨q, rfl⟩ := hy1
  have hq : q ∈ ((saturationOpens F T : Opn $ subS T) : CSet $ subS T) := by
    rwa [coe_saturationOpens]
  rw [← q1] at hq
  obtain ⟨p, hp⟩ := hq
  refine ⟨p, ?_⟩
  show siI T (p4 (saturationOpens F T) p) = siI T q
  rw [hp]

theorem quasiCompact_saturationio_restrictIdeal
    [QuasiCompact $ saturationio F T] (V : Opn Y) :
    QuasiCompact $ saturationio (restrictIdeal F V) $ restrictIdeal T V := by
  constructor
  intro U hU hUc
  have hV := isEmbedding (f := p4 V)
  have hg := isEmbedding
    (f := p4 (saturationOpens F T) ≫ siI T)
  have hg' := isEmbedding
    (f := p4 (saturationOpens (restrictIdeal F V) $ restrictIdeal T V) ≫
      siI (restrictIdeal T V))
  have hrange' : range (saturationio (restrictIdeal F V) $ restrictIdeal T V)
      = preimage (p4 V) (spI T \ F.support) := by
    rw [range_saturationio, restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, preimage_sdiff]
    ext x
    simp [mem_sdiff, mem_preimage, mem_coe,
      mem_support_comap]
  have hUo : IsOpen $ (p4 V) '' U := by
    obtain ⟨W, hW, hWU⟩ := hV.toIsInducing.isOpen_iff.mp hU
    rw [← hWU, image_preimage_eq_inter_range, q1]
    exact hW.inter V.isOpen
  let _a1 := saturationio F T
  have himg : IsCompact $ _a1 ''
      (_a1 ⁻¹' ((p4 V) '' U)) := (QuasiCompact.isCompact_preimage _ hUo $ hUc.image hV.continuous).image hg.continuous
  rw [image_preimage_eq_inter_range, range_saturationio] at himg
  have h2 := himg
  rw [← image_inter_preimage] at h2
  have hfinal := hV.toIsInducing.isCompact_iff.mpr h2
  rw [← hrange', ← image_preimage_eq_inter_range] at hfinal
  exact hg'.toIsInducing.isCompact_iff.mpr hfinal
end


theorem quasiCompact_saturationio_congr
    {F F' T T' : ISD Y} (hF : F = F') (hT : T = T')
    (h : QuasiCompact $ saturationio F T) :
    QuasiCompact $ saturationio F' T' := by
  subst hF
  subst hT
  exact h

end

section
variable {X X1 : Sch}
section
variable (pi_ : X1 ⟶ X) (Z D : ISD X)
theorem strictTransformio_eq_saturationio :
    strictTransformio pi_ Z D = saturationio (Z.comap pi_) (D.comap pi_) := rfl

theorem quasiCompact_strictTransformio_comp_io [QuasiCompact (strictTransformio pi_ Z D)] (V : Opn X1) :
    QuasiCompact $ strictTransformio (ι V ≫ pi_) Z D := by
  have hqc : QuasiCompact $ saturationio (cmI Z pi_) $ cmI D pi_ :=
    (inferInstance : QuasiCompact $ strictTransformio pi_ Z D)
  have h2 : QuasiCompact $ saturationio (restrictIdeal (cmI Z pi_) V)
      (restrictIdeal (cmI D pi_) V) :=
    quasiCompact_saturationio_restrictIdeal (cmI Z pi_) (cmI D pi_) V
  have hZ : restrictIdeal (cmI Z pi_) V = cmI Z (opI V ≫ pi_) := by simp_all
  have hD : restrictIdeal (cmI D pi_) V = cmI D (opI V ≫ pi_) := by simp_all
  exact quasiCompact_saturationio_congr hZ hD h2

theorem strictTransform_eq_saturation :
    strictTransform pi_ Z D = saturation (Z.comap pi_) (D.comap pi_) := rfl
end

theorem quasiCompact_strictTransformio_of_noetherianSpace
    [NoetherianSpace X1] (pi_ : X1 ⟶ X) (Z D : ISD X) :
    QuasiCompact $ strictTransformio pi_ Z D := by
  let T := cmI D pi_
  have hemb := isEmbedding
    (f := p4 (saturationOpens (cmI Z pi_) T) ≫ siI T)
  have :=
    hemb.toIsInducing.noetherianSpace
  exact ⟨fun U _ _ => NoetherianSpace.isCompact _⟩
end

section
variable {S : Sch}
theorem image_preimage_io_le (W V' : Opn S) :
    Scheme.Opens.ι W ''ᵁ (Scheme.Opens.ι W ⁻¹ᵁ V') ≤ V' := by
  rw [image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_le_right

theorem map_eq_zero_congr {A B P : Opn S} (e : A = B) (hA : A ≤ P)
    (hB : B ≤ P) (z : (S.sec P)) :
    ((S.presheaf.map (homOfLE hA).op).hom z = 0) ↔
      ((S.presheaf.map (homOfLE hB).op).hom z = 0) := by
  subst e
  rfl

theorem map_basicOpen_eq_zero_iff {P : Opn S} (hP : IsAffineOpen P)
    (s y : (S.sec P)) :
    (S.presheaf.map (homOfLE $ S.basicOpen_le s).op).hom y = 0 ↔ ∃ n : ℕ, s ^ n * y = 0 := by
  have := hP.isLocalization_basicOpen s
  have halg : ∀ z, algebraMap P.sec Γ(S, bOpn S s) z
      = (pMap S (homOfLE $ S.basicOpen_le s).op).hom z := fun _ => rfl
  rw [← halg y]
  constructor
  intro hy
  have h0 : algebraMap P.sec Γ(S, bOpn S s) y
      = algebraMap P.sec Γ(S, bOpn S s) 0 := by simp_all
  obtain ⟨c, hc⟩ := mp_ (eq_iff_exists (powers s)
    Γ(S, bOpn S s)) h0
  obtain ⟨n, hn⟩ := c.2
  refine ⟨n, ?_⟩
  rw [mul_zero] at hc
  rwa [← hn] at hc
  rintro ⟨n, hn⟩
  have h2 := congrArg (algebraMap P.sec Γ(S, bOpn S s)) hn
  rw [map_mul, map_pow, map_zero] at h2
  obtain ⟨v, hv⟩ := (map_units (M := powers s) Γ(S, bOpn S s) ⟨s, mem_powers s⟩).pow n
  have h4 := h2
  rw [← hv] at h4
  let _a0 := Γ(S, bOpn S s)
  have h5 := congrArg
    (fun z => ((v⁻¹ : _a0ˣ) : _a0) * z) h4
  simpa using h5
end

section
variable {Y : Sch} (F T : ISD Y) [QuasiCompact (saturationio F T)] (V : Y.affineOpens) (t) (ht : F.ideal V = span {t})
include ht
theorem mem_saturation_ideal_iff (f : Γ(Y, V.1)) :
    f ∈ (saturation F T).ideal V ↔ ∃ n : ℕ, t ^ n * f ∈ T.ideal V := by
  let _c0 := siI T ⁻¹ᵁ V.1
  let _c1 := T.subschemeι.app V.1
  let _m0 := saturationOpens F T
  have hbasic : Scheme.Opens.ι _m0 ''ᵁ
        (Scheme.Opens.ι _m0 ⁻¹ᵁ _c0) =
      T.subscheme.basicOpen (_c1.hom t) := by
    have h1 : (siI T ⁻¹ᵁ suppC F) ⊓ _c0
        = siI T ⁻¹ᵁ (suppC F ⊓ V.1) := rfl
    rw [image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    show (siI T ⁻¹ᵁ suppC F) ⊓ _c0 = _
    have _i20 : suppC F ⊓ V.1 = bOpn Y t := by
      have key : ∀ x, x ∈ V.1 → (x ∈ spI F ↔ x ∉ bOpn Y t) := by
        intro x hx
        rw [F.mem_support_iff_of_mem hx, ht, zeroLocus_span, mem_zeroLocus_iff]
        simp [mem_singleton_iff, forall_eq]
      refine le_antisymm (fun x hx => ?_) $ le_inf (fun x hx => fun hs => ((key x $ Y.basicOpen_le t hx).mp hs) hx) $ Y.basicOpen_le t
      by_contra hb
      exact hx.1 $ (key x $ hx.2).mpr hb
    rw [h1, _i20, preimage_basicOpen]
  let _a0 := (Scheme.Opens.i _m0).app _c0
  have hcongr : ∀ z : Γ(subS T, siI T ⁻¹ᵁ V.1),
      _a0.hom z = 0 ↔
      (T.subscheme.presheaf.map (homOfLE
        (T.subscheme.basicOpen_le $ _c1.hom t)).op).hom z = 0 := by
    intro z
    have e1 : _a0.hom z
        = (T.subscheme.presheaf.map (homOfLE
            (image_preimage_io_le _m0 _c0)).op).hom z := rfl
    rw [e1]
    exact map_eq_zero_congr hbasic _ _ z
  have hS : f ∈ (saturation F T).ideal V ↔ ((saturationio F T).app V.1).hom f = 0 := by
    rw [saturation_eq_ker_saturationio, ker_apply]
    exact mem_ker
  have hT : ∀ a, a ∈ T.ideal V ↔ _c1.hom a = 0 := by
    intro a
    have _i21 : RingHom.ker (T.subschemeι.app V.1).hom = T.ideal V := by
      have : QuasiCompact T.si := inferInstance
      rw [← ker_apply, ker_subschemeι]
    rw [← _i21]
    exact mem_ker
  have hmul : ∀ n a,
      _c1.hom (t ^ n * a)
        = (_c1.hom t) ^ n * (_c1.hom a) := by
    intro n a
    rw [map_mul, map_pow]
  have main : _a0.hom
      (_c1.hom f) = 0 ↔ ∃ n, t ^ n * f ∈ T.ideal V := by
    rw [hcongr $ _c1.hom f,
      map_basicOpen_eq_zero_iff (V.2.preimage T.si) (_c1.hom t)
        (_c1.hom f)]
    constructor
    simp_all
    simp_all
  exact hS.trans main

theorem saturation_ideal_eq_of_eq_mul (J : Ideal Γ(Y, V.1))
    (hTfactor : T.ideal V = span {t} * J)
    (hJ : ∀ g : Γ(Y, V.1), t * g ∈ J → g ∈ J) :
    (saturation F T).ideal V = J := by
  have hdown : ∀ n (g : Γ(Y, V.1)), t ^ n * g ∈ J → g ∈ J := by
    intro n
    induction n with
    | zero =>
        intro g hg
        simpa using hg
    | succ m ih =>
        intro g hg
        refine hJ g $ ih (t * g) ?_
        have hrw : t ^ m * (t * g) = t ^ (m + 1) * g := by ring
        rwa [hrw]
  ext f
  rw [mem_saturation_ideal_iff F T V t ht f]
  constructor
  rintro ⟨n, hn⟩
  rw [hTfactor] at hn
  exact hdown n f $ (mul_le.2 fun r _ s hs => J.mul_mem_left r hs) hn
  intro hf
  refine ⟨1, ?_⟩
  rw [hTfactor, pow_one]
  exact mul_mem_mul (mem_span_singleton_self t) hf

theorem saturation_ideal_eq_top_of_span_pow_le (m : ℕ)
    (hm : span {t ^ m} ≤ T.ideal V) :
    (saturation F T).ideal V = ⊤ := by
  rw [eq_top_iff_one, mem_saturation_ideal_iff F T V t ht 1]
  exact ⟨m, by simpa using (hm $ mem_span_singleton_self _)⟩

theorem saturation_ideal_eq_of_isUnit (hu : IsUnit t) :
    (saturation F T).ideal V = T.ideal V := by
  ext f
  rw [mem_saturation_ideal_iff F T V t ht f]
  constructor
  rintro ⟨n, hn⟩
  exact mp_ ((T.ideal V).unit_mul_mem_iff_mem $ hu.pow n) hn
  intro hf
  exact ⟨0, by simpa using hf⟩
end

section
variable {X X1 : Sch} (pi_) (Z D : ISD X) [QuasiCompact (strictTransformio pi_ Z D)] (V : X1.affineOpens) (t) (ht : (Z.comap pi_).ideal V = span {t})
include ht
theorem mem_strictTransform_ideal_iff (f : Γ(X1, V.1)) :
    f ∈ (strictTransform pi_ Z D).ideal V ↔ ∃ n : ℕ, t ^ n * f ∈ (D.comap pi_).ideal V := by
  have hqc : QuasiCompact $ saturationio (cmI Z pi_) $ cmI D pi_ :=
    (inferInstance : QuasiCompact $ strictTransformio pi_ Z D)
  rw [strictTransform_eq_saturation pi_ Z D]
  exact mem_saturation_ideal_iff (cmI Z pi_) (cmI D pi_) V t ht f

theorem strictTransform_ideal_eq_comap_of_isUnit (hu : IsUnit t) :
    (strictTransform pi_ Z D).ideal V = (D.comap pi_).ideal V := by
  have hqc : QuasiCompact $ saturationio (cmI Z pi_) $ cmI D pi_ :=
    (inferInstance : QuasiCompact $ strictTransformio pi_ Z D)
  rw [strictTransform_eq_saturation pi_ Z D]
  exact saturation_ideal_eq_of_isUnit (cmI Z pi_) (cmI D pi_) V t ht hu
end

theorem ker_le_ker_comp {A B C : Sch} (a : A ⟶ B) (m : B ⟶ C)
    [QuasiCompact m] [QuasiCompact $ a ≫ m] : m.ker ≤ (a ≫ m).ker := by
  rw [le_def]
  intro U
  rw [ker_apply, ker_apply]
  intro x hx
  rw [mem_ker] at hx
  have key : ((a ≫ m).app U.1).hom x = (a.app $ preU m U.1).hom ((m.app U.1).hom x) :=
    congrArg (fun ph_ => (m4 ph_) x) $ comp_app a m U.1
  refine RingHom.mem_ker.mpr ?_
  rw [key, hx]
  exact map_zero _

theorem base_apply_congr {A B : Sch} {ph_ ps_ : A ⟶ B} (h : ph_ = ps_) (x : ↥A) :
    ph_ x = ps_ x := by rw [h]

theorem strictTransform_eq_of_comap_eq {X X' X1 : Sch} (pi_ : X1 ⟶ X) (pi' : X1 ⟶ X')
    (Z D : ISD X) (Z' D' : ISD X')
    (hZ : Z.comap pi_ = Z'.comap pi') (hD : D.comap pi_ = D'.comap pi') :
    strictTransform pi_ Z D = strictTransform pi' Z' D' := by
  rw [strictTransform_eq_saturation pi_ Z D, strictTransform_eq_saturation pi' Z' D', hZ, hD]

theorem quasiCompact_of_eq {A C : Sch} {f g : A ⟶ C} (h : f = g)
    (hf : QuasiCompact g) : QuasiCompact f := by
  subst h
  exact hf

theorem ker_eq_ker_of_factorizations {A B C : Sch} (u : A ⟶ C) (v : B ⟶ C)
    (hu : QuasiCompact u) (hv : QuasiCompact v) (a : A ⟶ B) (b : B ⟶ A)
    (ha : a ≫ v = u) (hb : b ≫ u = v) : u.ker = v.ker := by
  have h1 := quasiCompact_of_eq ha hu
  have h2 := quasiCompact_of_eq hb hv
  refine le_antisymm ?_ ?_
  rw [← hb]
  exact ker_le_ker_comp b u
  rw [← ha]
  exact ker_le_ker_comp a v

theorem strictTransform_comp_io {X V' : Sch} (U : Opn X) (g : V' ⟶ toScheme U)
    (Z D : ISD X) :
    strictTransform (g ≫ ι U) Z D = strictTransform g (restrictIdeal Z U) (restrictIdeal D U) := by
  refine strictTransform_eq_of_comap_eq (g ≫ opI U) g Z D (restrictIdeal Z U)
    (restrictIdeal D U) ?_ ?_
  simp_all
  simp_all

theorem ideal_comap_hom_id {R : CRC} (I : Ideal R) :
    comap (CommRingCat.Hom.hom $ 𝟙 R) I = I :=by simp_all
theorem ker_comp_map_eqToHom {A : Sch} {R : CRC}
    {P Q : Opn A} (e : P = Q) (ph_ : R ⟶ A.presheaf.obj (Opposite.op Q)) :
    RingHom.ker (CommRingCat.Hom.hom $ ph_ ≫ A.presheaf.map (eqToHom e).op)
      = RingHom.ker ph_.hom := by
  subst e
  simp

theorem ker_comap_io {A B : Sch} (m : A ⟶ B) [QuasiCompact m]
    (V : Opn B) : m.ker.comap V.ι = (m ∣_ V).ker := by
  have : QuasiCompact $ mrU m V := inferInstance
  apply m29
  funext U
  rw [ideal_comap_of_isOpenImmersion, ker_apply,
    ker_apply, morphismRestrict_app]
  refine m32 ?_ (ker_comp_map_eqToHom _ _).symm
  simp
  exact ideal_comap_hom_id _

section
variable {Y : Sch}
theorem exists_factorizations_subscheme_restrict (T : ISD Y)
    (V : Opn Y) :
    (∃ p : (subscheme $ T.comap V.ι) ⟶ toScheme (subschemeι T ⁻¹ᵁ V),
        p ≫ (subschemeι T ∣_ V) = subschemeι (T.comap V.ι)) ∧
      (∃ q : toScheme (subschemeι T ⁻¹ᵁ V) ⟶ (subscheme $ T.comap V.ι),
        q ≫ subschemeι (T.comap V.ι) = subschemeι T ∣_ V) := by
  have : IsClosedImmersion $ T.si.mr V := inferInstance
  have hker : (T.si.mr V).ker = (subschemeι $ T.comap V.i).ker := by
    rw [q2, ← ker_comap_io,
      q2]
  refine ⟨⟨m64 (T.si.mr V) (siI $ cmI T V.i) hker.le,
      by simp⟩,
    ⟨m64 (siI $ cmI T V.i) (T.si.mr V) hker.ge, by simp⟩⟩

section
variable (F T : ISD Y)
theorem restrictIdeal_saturation
    [QuasiCompact $ saturationio F T] (V : Opn Y) :
    restrictIdeal (saturation F T) V = saturation (restrictIdeal F V) (restrictIdeal T V) := by
  rw [restrictIdeal_eq_comap_io, saturation_eq_ker_saturationio, ker_comap_io, saturation_eq_ker_saturationio]
  obtain ⟨a, ha⟩ : ∃ a : oSch (saturationOpens (cmI F V.ι) $ cmI T V.ι) ⟶ oSch (saturationio F T ⁻¹ᵁ V), a ≫ (saturationio F T ∣_ V) = saturationio (cmI F V.ι) (cmI T V.ι) := by
    let _c0 := saturationOpens (cmI F V.ι) $ cmI T V.ι
    obtain ⟨⟨p, hp⟩, -⟩ := exists_factorizations_subscheme_restrict T V
    have hdT : (p4 _c0 ≫ p ≫
          p4 (preU T.si V)) ≫ siI T
        = saturationio (cmI F V.i) (cmI T V.i) ≫ opI V := by
      rw [assoc, assoc, ← morphismRestrict_ι T.si V,
        ← assoc p, hp, saturationio_eq_io_comp_subschemeio (cmI F V.i) $ cmI T V.i, assoc]
    have hrangeD : range (p4 _c0 ≫ p ≫
          p4 (siI T ⁻¹ᵁ V))
        ⊆ range (p4 $ saturationOpens F T) := by
      rintro _ ⟨x, rfl⟩
      rw [q1, mem_saturationOpens]
      let _a4 := subS $ cmI T V.i
      have hx : p4 _c0 x
          ∈ ((saturationOpens (cmI F V.i) (cmI T V.i) :
              Opn _a4) : Set _a4) := by
        rw [← q1]
        exact mem_range_self _
      have key : siI T
            ((p4 _c0 ≫ p ≫
              p4 (siI T ⁻¹ᵁ V)) x)
          = opI V (saturationio (cmI F V.i) (cmI T V.i) x) := base_apply_congr hdT x
      rw [key]
      intro hcon
      refine mp_ (mem_saturationOpens (cmI F V.i) (cmI T V.i) _) hx ?_
      rw [mem_coe, mem_support_comap]
      exact mp_ mem_coe hcon
    obtain ⟨c, hc⟩ : ∃ c : oSch _c0 ⟶
        toScheme (saturationOpens F T),
        c ≫ p4 (saturationOpens F T)
          = p4 _c0 ≫ p ≫
              p4 (siI T ⁻¹ᵁ V) :=
      ⟨lift (p4 $ saturationOpens F T)
        (p4 _c0 ≫ p ≫
          p4 (siI T ⁻¹ᵁ V)) hrangeD, by simp⟩
    have hc' : c ≫ saturationio F T
        = saturationio (cmI F V.i) (cmI T V.i) ≫ opI V := by
      have h0 : (c ≫ p4 (saturationOpens F T)) ≫ siI T
          = saturationio (cmI F V.i) (cmI T V.i) ≫ opI V := by
        rwa [hc]
      rwa [saturationio_eq_io_comp_subschemeio F T, ← assoc]
    let _a2 := Scheme.Opens.ι $ saturationio F T ⁻¹ᵁ V
    have hrangeC : range c
        ⊆ range _a2 := by
      rintro _ ⟨x, rfl⟩
      rw [q1]
      let _a8 := saturationio F T $ c x
      show _a8 ∈ (V : Set Y)
      have key : _a8
          = opI V (saturationio (cmI F V.i) (cmI T V.i) x) := base_apply_congr hc' x
      rw [key, ← q1]
      exact mem_range_self _
    obtain ⟨a, ha⟩ : ∃ a : oSch _c0 ⟶
        toScheme (saturationio F T ⁻¹ᵁ V),
        a ≫ _a2 = c :=
      ⟨lift _a2 c hrangeC, by simp⟩
    refine ⟨a, ?_⟩
    rwa [← cancel_mono V.ι, assoc, morphismRestrict_ι, ← assoc, ha]
  obtain ⟨b, hb⟩ : ∃ b : oSch (saturationio F T ⁻¹ᵁ V) ⟶ oSch (saturationOpens (cmI F V.ι) $ cmI T V.ι), b ≫ saturationio (cmI F V.ι) (cmI T V.ι) = saturationio F T ∣_ V := by
    let _c0 := saturationio F T ⁻¹ᵁ V
    let _c1 := saturationOpens F T
    let _c2 := saturationOpens (cmI F V.i) $ cmI T V.i
    let _c3 := siI T ⁻¹ᵁ V
    obtain ⟨-, ⟨q, hq⟩⟩ := exists_factorizations_subscheme_restrict T V
    let _a2 := Scheme.Opens.ι _c0 ≫ Scheme.Opens.ι _c1
    have hrangeW : range _a2
        ⊆ range (p4 _c3) := by
      rintro _ ⟨y, rfl⟩
      rw [q1]
      have hy : Scheme.Opens.ι _c0 y
          ∈ ((saturationio F T ⁻¹ᵁ V : Opn $ oSch _c1) :
              Set $ oSch _c1) := by
        rw [← q1]
        exact mem_range_self _
      exact hy
    obtain ⟨w, hw⟩ : ∃ w : oSch _c0 ⟶
        toScheme _c3,
        w ≫ p4 _c3
          = _a2 :=
      ⟨lift (Scheme.Opens.ι _c3)
        _a2 hrangeW, by simp⟩
    let _a4 := w ≫ q
    have hrangeQ : range _a4
        ⊆ range (p4 _c2) := by
      rintro _ ⟨y, rfl⟩
      rw [q1, mem_saturationOpens, mem_coe,
        mem_support_comap]
      let _a1 := Scheme.Opens.ι _c1 $ Scheme.Opens.ι _c0 y
      have hy : _a1
          ∈ ((saturationOpens F T : Opn $ subS T) : CSet $ subS T) := by
        rw [← q1]
        exact mem_range_self _
      let _a0 := siI (cmI T V.i) $ _a4 y
      have key : opI V _a0
          = siI T _a1 := by
        have e1 : _a0 = (T.si.mr V) (w y) :=
          base_apply_congr hq $ w y
        let _a3 := p4 _c3 $ w y
        have e2 : opI V ((T.si.mr V) $ w y)
            = siI T _a3 :=
          base_apply_congr (morphismRestrict_ι T.si V) $ w y
        have e3 : _a3
            = _a1 :=
          base_apply_congr hw y
        rw [e1, e2, e3]
      rw [key]
      exact mp_ (mem_saturationOpens F T _) hy
    obtain ⟨b, hb0⟩ : ∃ b : oSch _c0 ⟶
        toScheme _c2,
        b ≫ p4 _c2 = _a4 :=
      ⟨lift (p4 _c2)
        _a4 hrangeQ, by simp⟩
    have hb' : _a4 ≫ (siI (cmI T V.ι) ≫ opI V)
        = Scheme.Opens.ι _c0 ≫
            (Scheme.Opens.ι _c1 ≫ siI T) := by
      rw [assoc, ← assoc q, hq, morphismRestrict_ι, ← assoc w, hw,
        assoc]
    refine ⟨b, ?_⟩
    rw [← cancel_mono V.i, saturationio_eq_io_comp_subschemeio (cmI F V.i) $ cmI T V.i,
      ← assoc b, hb0, assoc, morphismRestrict_ι]
    exact hb'
  exact ker_eq_ker_of_factorizations _ _ inferInstance (quasiCompact_saturationio_restrictIdeal F T V) b a hb ha
end
end

theorem restrictIdeal_strictTransform {X X1 : Sch} (pi_ : X1 ⟶ X) (Z D : ISD X)
    [QuasiCompact $ strictTransformio pi_ Z D] (V : Opn X1) :
    restrictIdeal (strictTransform pi_ Z D) V = strictTransform (ι V ≫ pi_) Z D := by
  have hqc : QuasiCompact $ saturationio (cmI Z pi_) $ cmI D pi_ :=
    (inferInstance : QuasiCompact $ strictTransformio pi_ Z D)
  rw [strictTransform_eq_saturation pi_ Z D, strictTransform_eq_saturation (opI V ≫ pi_) Z D,
    restrictIdeal_saturation (cmI Z pi_) (cmI D pi_) V, restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io,
    comap_comp, comap_comp]


section
variable {X X1 : Sch}
section
variable (pi_ : X1 ⟶ X) (Z : ISD X)
def complComapSupport : Opn X1 :=
  (Z.comap pi_).support.compl

theorem complComapSupport_eq :
    complComapSupport pi_ Z = (Z.comap pi_).support.compl := rfl

theorem coe_complComapSupport :
    ((complComapSupport pi_ Z : Opn X1) : Set X1) = (support (Z.comap pi_) : Set X1)ᶜ := rfl
end

theorem strictTransform_comap_complComapSupport_io [IsNoetherian X1]
    (pi_ : X1 ⟶ X) (Z D : ISD X) :
    (strictTransform pi_ Z D).comap (Scheme.Opens.ι $ complComapSupport pi_ Z) =
      (D.comap pi_).comap (Scheme.Opens.ι $ complComapSupport pi_ Z) := by
  let _a2 := complComapSupport pi_ Z
  let _a0 := p4 _a2
  let _c0 := cmI (cmI D pi_) _a0
  have hqio : QuasiCompact _a0 := inferInstance
  have hq1 : QuasiCompact
      (siI _c0) := inferInstance
  let _a1 := (siI _c0) ≫ _a0
  have hq2 : QuasiCompact
      _a1 := inferInstance
  have h1 : strictTransform pi_ Z D =
      _a1.ker :=
    ker_io_preimage_comp_subschemeio_eq_ker_comap (cmI D pi_) _a2
  rw [h1]
  exact comap_ker_subschemeio_comp
    _c0
    _a0
end

theorem strictTransform_comap_of_comap_center_eq_top {X X1 B : Sch} [IsNoetherian X1]
    (pi_ : X1 ⟶ X) (Z D : ISD X) (g : B ⟶ X1)
    (hg : (Z.comap pi_).comap g = ⊤) :
    (strictTransform pi_ Z D).comap g = (D.comap pi_).comap g := by
  let _c0 := ((support (Z.comap pi_) : Closeds X1) : Set X1)
  have hsupp : ((support ((Z.comap pi_).comap g) : Closeds B) : Set B)
      = Set.preimage g.base _c0 := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hempty : Set.preimage g.base _c0 = ∅ := by
    rw [← hsupp, hg]
    simp
  let _a0 := complComapSupport pi_ Z
  have hbase : ∀ b, ⇑g.base b ∈ (_a0 : Set X1) := by
    intro b
    rw [coe_complComapSupport]
    simp only [mem_compl_iff]
    intro hmem
    have hb : b ∈ preimage g.base _c0 := hmem
    rw [hempty] at hb
    simp at hb
  have hrange : range ⇑g.base ⊆
      range ⇑(Scheme.Opens.i _a0).base := by
    rintro x ⟨b, rfl⟩
    simpa [Scheme.Opens.range_ι] using (hbase b)
  rw [← lift_fac (Scheme.Opens.i _a0) g hrange, comap_comp, comap_comp,
    strictTransform_comap_complComapSupport_io]


section
variable {S X : Sch} (σ : S ⟶ X)
theorem imageIdealSheaf_eq_top_iff [IsClosedImmersion σ]
    (I : ISD S) : imageIdealSheaf σ I = ⊤ ↔ I = ⊤ := by
  constructor
  intro hI
  have h2 : cmI (imageIdealSheaf σ I) σ = I := comap_schemeImageIdeal σ I
  rw [hI] at h2
  rw [← h2]
  simp
  rintro rfl
  rw [imageIdealSheaf_eq_ker, ← support_eq_bot_iff]
  have hs := support_ker $ siI (⊤ : ISD S) ≫ σ
  rw [range_eq_empty, closure_empty] at hs
  refine coe_injective ?_
  rw [hs]
  simp
end

section
variable {Sc A C} (t : SequenceOfBlowups Sc) {a b a' b'} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b') (g : C ⟶ schemeAt t b) (f : A ⟶ schemeAt t a)
theorem comp_eqToHom_comp_transitionMap (u : C ⟶ A)
    (H : g ≫ transitionMap t hab = u ≫ f) :
    (g ≫ eqToHom (congrArg t.schemeAt hb)) ≫ transitionMap t hab'
      = u ≫ (f ≫ eqToHom (congrArg t.schemeAt ha)) := by
  subst ha
  subst hb
  simpa using H

theorem ker_comp_eqToHom_eq_strictTransform
    (H : g.ker = strictTransform (transitionMap t hab) (center t a) f.ker) :
    (g ≫ eqToHom (congrArg t.schemeAt hb)).ker
      = strictTransform (transitionMap t hab') (center t a') (f ≫ eqToHom (congrArg t.schemeAt ha)).ker := by
  subst ha
  subst hb
  simpa using H
end

section
variable {Sc A : Sch} (t : SequenceOfBlowups Sc)
theorem isClosedImmersion_comp_eqToHom {a a' : ℕ}
    (ha : a = a') (f : A ⟶ schemeAt t a) (hf : IsClosedImmersion f) :
    IsClosedImmersion $ f ≫ eqToHom (congrArg t.schemeAt ha) := by
  subst ha
  simpa using hf

theorem center_eq_imageIdealSheaf_comp_eqToHom
    (I : ISD A) {a a' : ℕ} (ha : a = a') (f : A ⟶ schemeAt t a)
    (hf : center t a = imageIdealSheaf f I) :
    center t a' = imageIdealSheaf (f ≫ eqToHom (congrArg t.schemeAt ha)) I := by
  subst ha
  simpa using hf
end

theorem eqToHom_projectionToBase {Sc : Sch} (t : SequenceOfBlowups Sc) {a a' : ℕ} (ha : a = a') :
    eqToHom (congrArg t.schemeAt ha) ≫ projectionToBase t a' = projectionToBase t a := by
  subst ha
  simp

theorem isPushforwardSequenceOfBlowups_withoutIsoBlowups {S X : Sch} (j : S ⟶ X) [IsClosedImmersion j]
    (B : SequenceOfBlowups S) (t : SequenceOfBlowups X)
    (hN : ∀ i : ℕ, i ≤ t.length → IsLocallyNoetherian (schemeAt t i))
    (h : IsPushforwardBlowupSeq j B t) :
    IsPushforwardBlowupSeq j B.withoutIsoBlowups t.withoutIsoBlowups := by
  obtain ⟨hlen, σ, hci, h0, hsq, hcen, hker⟩ := h
  have htriv : ∀ i, i < B.length → (B.center i = ⊤ ↔ center t i = ⊤) := by
    intro i hi
    rw [hcen i hi]
    exact (imageIdealSheaf_eq_top_iff (σ i hi.le) $ B.center i).symm
  have hret : ∀ i, B.nontrivialIndex i = t.nontrivialIndex i := fun i => congrFun (SequenceOfBlowups.nontrivialIndex_congr_of_center_eq_top_iff B t hlen htriv) i
  have hdown : ∀ a b (hab : a ≤ b) (hb : b ≤ B.length),
      σ b hb ≫ transitionMap t hab = transitionMap B hab ≫ σ a (le_trans hab hb) := by
    intro a b hab
    induction b, hab using le_induction with
    | base =>
        intro hb
        rw [t.transitionMap_self, B.transitionMap_self, comp_id, id_comp]
    | succ b hab ih =>
        intro hb
        have hbl : b < B.length := hb
        let _a0 := le_trans hab $ le_succ b
        have e1 : transitionMapSucc t b ≫ transitionMap t hab = transitionMap t _a0 := by
          rw [blowupMorphism_eq_transitionMap]
          exact t.transitionMap_trans hab $ le_succ b
        have e2 : transitionMapSucc B b ≫ transitionMap B hab = transitionMap B _a0 := by
          rw [blowupMorphism_eq_transitionMap]
          exact B.transitionMap_trans hab $ le_succ b
        rw [← e1, ← assoc, hsq b hbl, assoc, ih hbl.le, ← assoc, e2]
  have hstruct : ∀ i (hi : i ≤ B.length),
      σ i hi ≫ projectionToBase t i = projectionToBase B i ≫ j := by
    intro i hi
    rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.projectionToBase_def, ← assoc $ σ i hi, hdown 0 i (zero_le i) hi]
    simp only [assoc, h0]
  have key : ∀ a c (hac : a + 1 ≤ c), (∀ d, a + 1 ≤ d → d < c → center t d = ⊤) →
      ∀ hc (ha : a < B.length),
      (σ c hc).ker
        = p6 (transitionMap t $ le_of_succ_le hac) (center t a) (σ a ha.le).ker := by
    intro a c hac
    induction c, hac using le_induction with
    | base =>
        intro _ hc ha
        have hk := hker a ha
        rwa [blowupMorphism_eq_transitionMap] at hk
    | succ c hac ih =>
        intro htop hc ha
        have hcl : c < B.length := hc
        have htopc : ∀ d, a + 1 ≤ d → d < c → center t d = ⊤ :=
          fun d hd1 hd2 => htop d hd1 $ lt_succ_of_lt hd2
        have hctop := htop c hac $ lt_succ_self c
        have : IsLocallyNoetherian $ schemeAt t c := hN c $ by omega
        have : IsLocallyNoetherian $ schemeAt t $ c + 1 := hN (c + 1) $ by omega
        have hk := hker c hcl
        rw [hctop, strictTransform_top_eq_comap (transitionMapSucc t c) $ (σ c hcl.le).ker, ih htopc (le_of_lt hcl) ha] at hk
        have hiso : IsIso $ sbTrS t c := by
          have hB := t.isBlowupAlongIdealSheaf_blowupMorphism c $ by omega
          rw [hctop] at hB
          exact hB.isIso_of_top
        have hbl : p15 (transitionMap t $ m212 hac) $ center t a := by
          have : IsIso $ transitionMap t hac := t.isIso_transitionMap_of_center_eq_top hac (by omega) htopc
          let _a1 := asIso $ transitionMap t hac
          have hcomp := (t.isBlowupAlongIdealSheaf_blowupMorphism a $ by omega).iso_hom_comp _a1
          have heq2 : isoH _a1 ≫ transitionMapSucc t a
              = transitionMap t (le_of_succ_le hac) := by
            rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
            exact t.transitionMap_trans (Nat.le_succ a) hac
          rwa [heq2] at hcomp
        have heq : transitionMapSucc t c ≫ transitionMap t (m212 hac)
            = transitionMap t (le_of_succ_le $ le_trans hac $ le_succ c) := by
          rw [blowupMorphism_eq_transitionMap]
          exact t.transitionMap_trans (le_of_succ_le hac) $ le_succ c
        rw [hk, ← strictTransform_isIso_comp (sbTrS t c) (transitionMap t $ le_of_succ_le hac)
          (center t a) (m149 $ σ a ha.le) hbl, heq]
  have h1 : ∀ i (hi : i ≤ B.lengthWithoutIsoBlowups),
      IsClosedImmersion $ σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi) ≫
        eqToHom (congrArg t.schemeAt $ hret i) := by
    intro i hi
    exact isClosedImmersion_comp_eqToHom t (hret i) _ $ hci _ _
  let _a2 := B.nontrivialIndex_le_length $ zero_le B.lengthWithoutIsoBlowups
  have h2 : (σ (B.nontrivialIndex 0) _a2 ≫
      eqToHom (congrArg t.schemeAt $ hret 0)) ≫ t.withoutIsoBlowups.isoZero.hom
      = B.withoutIsoBlowups.isoZero.hom ≫ j := by
    simp only [SequenceOfBlowups.withoutIsoBlowups_isoObjZero, SequenceOfBlowups.objNontrivialIndexZeroIso_hom]
    rw [assoc, eqToHom_projectionToBase t $ hret 0]
    exact hstruct (B.nontrivialIndex 0) _a2
  have h3 : ∀ i (hi : i < B.lengthWithoutIsoBlowups),
      (σ (B.nontrivialIndex $ i + 1) (B.nontrivialIndex_le_length hi) ≫
          eqToHom (congrArg t.schemeAt $ hret $ i + 1)) ≫ t.withoutIsoBlowups.transitionMapSucc i
        = B.withoutIsoBlowups.transitionMapSucc i ≫
          (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length $ le_of_lt hi) ≫
            eqToHom (congrArg t.schemeAt $ hret i)) := by
    intro i hi
    simp only [SequenceOfBlowups.withoutIsoBlowups_blowupMorphism]
    exact comp_eqToHom_comp_transitionMap t (hret i) (hret $ i + 1)
      (B.nontrivialIndex_monotone (le_succ i) : B.nontrivialIndex i ≤ B.nontrivialIndex (i + 1))
      (t.nontrivialIndex_monotone (le_succ i) : t.nontrivialIndex i ≤ t.nontrivialIndex (i + 1)) _ _ _
      (hdown (B.nontrivialIndex i) (B.nontrivialIndex $ i + 1)
        (B.nontrivialIndex_monotone (le_succ i) : B.nontrivialIndex i ≤ B.nontrivialIndex (i + 1))
        (B.nontrivialIndex_le_length hi))
  have h4 : ∀ i (hi : i < B.lengthWithoutIsoBlowups),
      t.withoutIsoBlowups.center i = imageIdealSheaf (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length $ le_of_lt hi) ≫
        eqToHom (congrArg t.schemeAt $ hret i)) (B.withoutIsoBlowups.center i) := by
    intro i hi
    simp only [SequenceOfBlowups.withoutIsoBlowups_center]
    exact center_eq_imageIdealSheaf_comp_eqToHom t (B.center $ B.nontrivialIndex i) (hret i) _
      (hcen (B.nontrivialIndex i) $ B.nontrivialIndex_lt_length hi)
  refine ⟨SequenceOfBlowups.lengthWithoutIsoBlowups_congr_of_center_eq_top_iff B t hlen htriv, fun i hi => σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi) ≫
    eqToHom (congrArg t.schemeAt $ hret i), h1, h2, h3, h4, ?_⟩
  intro i hi
  have htopd : ∀ d, B.nontrivialIndex i + 1 ≤ d → d < B.nontrivialIndex (i + 1) → center t d = ⊤ := by
    intro d hd1 hd2
    exact (htriv d $ lt_of_lt_of_le hd2 $ B.nontrivialIndex_le_length hi).1 $ B.center_eq_top_of_nontrivialIndex_lt (lt_of_succ_le hd1) hd2
  simp only [SequenceOfBlowups.withoutIsoBlowups_blowupMorphism, SequenceOfBlowups.withoutIsoBlowups_center]
  exact ker_comp_eqToHom_eq_strictTransform t (hret i) (hret $ i + 1)
    (B.nontrivialIndex_monotone $ le_succ i)
    (t.nontrivialIndex_monotone $ le_succ i) _ _
    (key (B.nontrivialIndex i) (B.nontrivialIndex $ i + 1) (B.succ_le_nontrivialIndex_succ i) htopd
      (B.nontrivialIndex_le_length hi) $ B.nontrivialIndex_lt_length hi)


section
variable {U V : Sch} (j : U ⟶ V)
theorem map_eq_ker_subschemeio_comp (K : ISD U) :
    K.map j = ker (subschemeι K ≫ j) := by
  rw [ker_comp, q2]

theorem ker_subschemeio_comp_eq_of_ker_le [IsClosedImmersion j]
    (L : ISD V) (hL : ker j ≤ L) (K : ISD U)
    (hK : K = L.comap j) :
    ker (subschemeι K ≫ j) = L := by
  have hle : j.ker ≤ ker L.si := by simp_all
  let _a0 := m64 j L.si hle
  have hfac : _a0 ≫ j = subschemeι L := by
    rw [m154]
  have hcomap : L.comap j = _a0.ker := by
    let I := L
    let lam := _a0
    let hlam := hfac
    let _a1 := fst j I.si
    have hc : I.comap j = _a1.ker := rfl
    have hcomm : lam ≫ j = 𝟙 I.subscheme ≫ subschemeι I := by rw [hlam, id_comp]
    obtain ⟨e, hefst, hesnd⟩ : ∃ e,
        e ≫ _a1 = lam ∧
          e ≫ snd j I.si = 𝟙 I.subscheme :=
      ⟨m107 lam (𝟙 I.subscheme) hcomm, lift_fst _ _ _,
        lift_snd _ _ _⟩
    have : IsIso e := by
      refine ⟨snd j I.si, hesnd, ?_⟩
      refine Limits.pullback.hom_ext ?_ ?_
      rw [assoc, hefst, ← cancel_mono j, assoc, hlam, ← condition, id_comp]
      rw [assoc, hesnd, comp_id, id_comp]
    rw [hc]
    exact sy_ $ ker_eq_ker_of_isIso_comp lam _a1 e hefst
  rw [hK, hcomap, ker_comp, q2,
    ← ker_comp, hfac, q2]
end

theorem strictTransform_eq_ker_complComapSupport {X X1 : Sch} (pi_ : X1 ⟶ X)
    (Z D : ISD X) :
    strictTransform pi_ Z D =
      ker
        (subschemeι ((D.comap pi_).comap $ Scheme.Opens.ι $ complComapSupport pi_ Z) ≫
          Scheme.Opens.ι (complComapSupport pi_ Z)) := by
  rw [strictTransform_eq_ker, strictTransformImmersion_eq, strictTransformOpens_eq,
    ← complComapSupport_eq]
  exact ker_io_preimage_comp_subschemeio_eq_ker_comap (cmI D pi_) $ complComapSupport pi_ Z

section
variable {A A' A1_ A'1 : Sch} (j : A ⟶ A') [IsClosedImmersion j]
section
variable (Z D : ISD A) (pi_) (pi') (j1 : A1_ ⟶ A'1) [IsClosedImmersion j1] [hv3_5 : IsNoetherian A1_] [hv3_6 : IsNoetherian A'1] (hsq : j1 ≫ pi' = pi_ ≫ j)
include hv3_5 hv3_6 hsq
theorem image_strictTransform_eq_strictTransform_image
    (hker : ker j1 =
      strictTransform pi' (ker $ subschemeι Z ≫ j) (ker j)) :
    ker (subschemeι (strictTransform pi_ Z D) ≫ j1) =
      strictTransform pi' (ker $ subschemeι Z ≫ j)
        (ker $ subschemeι D ≫ j) := by
  let _a2 := subschemeι Z ≫ j
  let _c0 := _a2.ker
  have : IsClosedImmersion
      (j1 ∣_ complComapSupport pi' _c0) := inferInstance
  have hDle : j.ker ≤ ker (subschemeι D ≫ j) := by
    rw [ker_comp, q2,
      ← map_bot j]
    exact map_mono j bot_le
  let _a0 := (m54 j1.base).obj $ complComapSupport pi' $ ker $ subschemeι Z ≫ j
  have hUeq : _a0 = complComapSupport pi_ Z := by
    let _c0 := (_a2.ker).comap pi'
    have key : _c0.comap j1 = Z.comap pi_ := by
      rw [← m56, hsq, m56,
        ← map_eq_ker_subschemeio_comp, p30]
    have h2 : (support (Z.comap pi_) : Set A1_)
        = ⇑j1.base ⁻¹'
          _c0.support := by
      rw [← key, m19
        _c0 j1]
      rfl
    apply m55
    have h1 : _a0
        = ⇑j1.base ⁻¹' _c0.supportᶜ := rfl
    rw [h1, coe_complComapSupport, h2, preimage_compl]
  let _a3 := complComapSupport pi' _c0
  have hkerr : ker (j1 ∣_ complComapSupport pi' _c0)
      ≤ ((ker $ subschemeι D ≫ j).comap pi').comap
          _a3.i := by
    rw [← ker_comap_io_eq_ker_morphismRestrict j1
        _a3, hker,
      strictTransform_comap_complComapSupport_io pi' _c0
        (j.ker)]
    exact comap_mono
      _a3.i
      (comap_mono pi' hDle)
  have _i26 : (ker $ subschemeι ((D.comap pi_).comap (preU j1 _a3).i) ≫ ι (preU j1 _a3)).map j1 = ker (subschemeι (((ker $ subschemeι D ≫ j).comap pi').comap _a3.i) ≫ ι _a3) := by
    have hm : (j1.mr _a3) ≫ ι _a3 ≫ pi' = ι (preU j1 _a3) ≫ pi_ ≫ j := by simp_all
    have hMcomap :
        ((((ker $ subschemeι D ≫ j).comap pi').comap _a3.i).comap $ j1.mr _a3)
          = (D.comap pi_).comap (preU j1 _a3).i := by
      calc ((((ker $ subschemeι D ≫ j).comap pi').comap _a3.i).comap $ j1.mr _a3)
          = (ker $ subschemeι D ≫ j).comap ((j1.mr _a3) ≫ ι _a3 ≫ pi') := by
            rw [comap_comp (ker $ subschemeι D ≫ j)
                (j1.mr _a3) $ ι _a3 ≫ pi',
              m56 (m149 $ subschemeι D ≫ j) _a3.i pi']
        _ = (m149 $ subschemeι D ≫ j).comap (ι (preU j1 _a3) ≫ pi_ ≫ j) := by rw [hm]
        _ = (D.comap pi_).comap (preU j1 _a3).i := by
            rw [m56 (m149 $ subschemeι D ≫ j)
                (preU j1 _a3).i $ pi_ ≫ j,
              Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker $ subschemeι D ≫ j) pi_ j,
              ← map_eq_ker_subschemeio_comp j D, comap_map_of_isClosedImmersion j D]
    let _s0 := (D.comap pi_).comap (preU j1 _a3).i
    have hmor : ((subschemeι _s0 ≫ ι (preU j1 _a3)) ≫ j1)
        = ((subschemeι _s0 ≫ j1.mr _a3) ≫ ι _a3) := by simp_all
    rw [← ker_comp, hmor,
      ker_comp (subschemeι _s0 ≫ j1.mr _a3) _a3.i,
      ker_subschemeio_comp_eq_of_ker_le (j1.mr _a3)
        (((ker $ subschemeι D ≫ j).comap pi').comap _a3.i) hkerr
        _s0 hMcomap.symm,
      ker_comp
        (subschemeι $ ((ker $ subschemeι D ≫ j).comap pi').comap _a3.i) _a3.i,
      q2]
  rw [ker_comp, q2, strictTransform_eq_ker_complComapSupport pi_ Z D, ← hUeq,
    _i26]
  exact sy_ $ strictTransform_eq_ker_complComapSupport pi' _c0
    (ker $ subschemeι D ≫ j)

theorem map_strictTransform_eq_strictTransform_map
    (hker : ker j1 = strictTransform pi' (Z.map j) (ker j)) :
    (strictTransform pi_ Z D).map j1 = strictTransform pi' (Z.map j) (D.map j) := by
  have hZ := map_eq_ker_subschemeio_comp j Z
  rw [map_eq_ker_subschemeio_comp j1 $ p6 pi_ Z D, map_eq_ker_subschemeio_comp j D, hZ]
  exact image_strictTransform_eq_strictTransform_image j Z D pi_ pi' j1 hsq $ by rw [hker, hZ]
end
end


namespace IsPushforwardBlowupSeq

private theorem ker_comp_eq_ker_subschemeio_comp {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) :
    ker (f ≫ g) = ker (subschemeι (ker f) ≫ g) :=
  (ker_comp_eq_imageIdealSheaf_ker f g).trans $ imageIdealSheaf_eq_ker g f.ker

theorem comp {Y H X : Sch} (σ : Y ⟶ H) [IsClosedImmersion σ]
    (rh_ : H ⟶ X) [IsClosedImmersion rh_]
    {s : SequenceOfBlowups Y} {t : SequenceOfBlowups H} {u : SequenceOfBlowups X}
    (hNt : ∀ i : ℕ, i ≤ t.length → IsNoetherian (schemeAt t i))
    (hNu : ∀ i : ℕ, i ≤ u.length → IsNoetherian (schemeAt u i))
    (hst : IsPushforwardBlowupSeq σ s t) (htu : IsPushforwardBlowupSeq rh_ t u) :
    IsPushforwardBlowupSeq (σ ≫ rh_) s u := by
  obtain ⟨hl1, a, haci, ha0, hasq, hac, hak⟩ := hst
  obtain ⟨hl2, b, hbci, hb0, hbsq, hbc, hbk⟩ := htu
  refine ⟨tr_ hl1 hl2, fun i hi => a i hi ≫ b i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  intro i hi
  have hit : i ≤ t.length := by omega
  have := haci i hi
  have := hbci i hit
  infer_instance
  show (a 0 (zero_le _) ≫ b 0 (zero_le _)) ≫ sbIzH u
    = sbIzH s ≫ (σ ≫ rh_)
  rw [assoc, hb0, ← assoc, ha0, assoc]
  intro i hi
  have hit : i < t.length := by omega
  rw [assoc, hbsq i hit, ← assoc, hasq i hi, assoc]
  intro i hi
  have hit : i < t.length := by omega
  have := haci i hi.le
  have := hbci i hit.le
  rw [hbc i hit, hac i hi, imageIdealSheaf_comp]
  intro i hi
  have hit : i < t.length := by omega
  have hiu : i < u.length := by omega
  have := hbci i hit.le
  have := hbci (i + 1) hit
  have := haci i hi.le
  have := haci (i + 1) hi
  have := hNt (i + 1) hit
  have := hNu (i + 1) hiu
  let _a0 := b (i + 1) hit
  let _a2 := ker $ siI (center t i) ≫ b i hit.le
  let _a3 := b i hit.le
  have hker : _a0.ker
      = p6 (sbTrS u i)
          _a2
          (_a3.ker) := by
    rw [hbk i hit, hbc i hit, imageIdealSheaf_eq_ker]
  let _a1 := ker $ a i hi.le
  have key := image_strictTransform_eq_strictTransform_image _a3 (center t i)
    _a1 (sbTrS t i) (sbTrS u i) _a0
    (hbsq i hit) hker
  have hL : ker (a (i + 1) hi ≫ _a0)
      = ker ((p6 (sbTrS t i) (center t i)
          _a1).subschemeι ≫ _a0) := by
    rw [ker_comp_eq_ker_subschemeio_comp, hak i hi]
  have hD : ker (a i hi.le ≫ _a3)
      = ker (siI _a1 ≫ _a3) :=
    ker_comp_eq_ker_subschemeio_comp _ _
  have hC : center u i = _a2 := by
    rw [hbc i hit, imageIdealSheaf_eq_ker]
  rw [hL, key, hC, hD]

theorem of_isomorphic_source {S X : Sch} (j : S ⟶ X) [IsClosedImmersion j]
    {s s' : SequenceOfBlowups S} {t : SequenceOfBlowups X}
    (hs : s.Isomorphic s') (h : IsPushforwardBlowupSeq j s t) :
    IsPushforwardBlowupSeq j s' t := by
  obtain ⟨hlen, e, h0, hsqe, hce⟩ := hs
  have hpb : IsStrictPullbackBlowupSeq (𝟙 S) s' s := by
    refine ⟨sy_ hlen, fun i hi => isoI $ e i $ by omega, ?_, ?_, ?_⟩
    show isoI (e 0 $ zero_le _) ≫ s.isoZero.hom = s'.isoZero.hom ≫ 𝟙 S
    rw [comp_id, ← h0, ← assoc, m114, id_comp]
    intro i hi
    have hi' : i < s.length := by omega
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [inv_comp_eq, ← assoc, hsqe i hi', assoc,
      m145, comp_id]
    intro i hi
    have hi' : i < s.length := by omega
    let _a1 := e i hi'.le
    have h1 : imageIdealSheaf _a1.hom ((center s' i).comap _a1.hom)
        = imageIdealSheaf _a1.hom (center s i) := by rw [hce i hi']
    rw [imageIdealSheaf_comap] at h1
    rw [h1, imageIdealSheaf_eq_comap_inv, IsIso.inv_eq_of_hom_inv_id $ m145 _a1]
  exact IsPushforwardBlowupSeq.isIso_comp (𝟙 S) j j (id_comp j).symm hpb h

end IsPushforwardBlowupSeq


structure SequenceOfBlowupsPushforward {S X : Sch} (j : S ⟶ X) (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X) where
  lengthEq : BS.length = B.length
  σ : ∀ i : ℕ, i ≤ B.length → (schemeAt BS i ⟶ schemeAt B i)
  isClosedImmersion : ∀ i hi, IsClosedImmersion $ σ i hi
  zero : σ 0 (zero_le B.length) ≫ B.isoZero.hom = BS.isoZero.hom ≫ j
  square : ∀ (i : ℕ) (hi : i < B.length),
    σ (i + 1) hi ≫ transitionMapSucc B i = transitionMapSucc BS i ≫ σ i hi.le
  center : ∀ (i : ℕ) (hi : i < B.length),
    B.center i = imageIdealSheaf (σ i hi.le) (center BS i)

theorem comap_imageIdealSheaf_of_isIso {A B : Sch} (f : A ⟶ B) [IsIso f]
    (J : ISD A) :
    (imageIdealSheaf f J).comap f = J := by
  rw [show imageIdealSheaf f J = J.map f from map_eq_imageIdealSheaf ..]
  exact p30 f J

private theorem exists_iso_succ_comp_blowupMorphism {X : Sch} (B B' : SequenceOfBlowups X) (i : ℕ)
    (hi : i < B.length) (hi' : i < B'.length) (f : schemeAt B i ≅ schemeAt B' i)
    (hf : (B'.center i).comap f.hom = B.center i) :
    ∃ g : schemeAt B (i + 1) ≅ schemeAt B' (i + 1),
      g.hom ≫ transitionMapSucc B' i = transitionMapSucc B i ≫ f.hom := by
  have hB := B.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have hB' := B'.isBlowupAlongIdealSheaf_blowupMorphism i hi'
  have cB := an1 hB
  have cB' := an1 hB'
  have hinv : (B.center i).comap f.inv = B'.center i := by
    rw [← hf, ← comap_comp, m114,
      comap_id]
  have c1 := cB
  rw [← hf, ← comap_comp] at c1
  have c2 := cB'
  rw [← hinv, ← comap_comp] at c2
  obtain ⟨a, ha⟩ := (an2 hB' _ (sbTrS B i ≫ isoH f) c1).exists
  obtain ⟨b, hb⟩ := (an2 hB _ (sbTrS B' i ≫ isoI f) c2).exists
  have hab : a ≫ b = 𝟙 _ := by
    refine (an2 hB _ (sbTrS B i) cB).unique ?_ ?_
    rw [assoc, hb, ← assoc, ha, assoc, m145,
      comp_id]
    rw [id_comp]
  refine ⟨⟨a, b, hab, ?_⟩, ha⟩
  refine (an2 hB' _ (sbTrS B' i) cB').unique ?_ ?_
  rw [assoc, ha, ← assoc, hb, assoc, m114,
    comp_id]
  rw [id_comp]

namespace SequenceOfBlowupsPushforward

section
variable {S X : Sch}
theorem nonempty_of_isPushforward (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X} (h : IsPushforwardBlowupSeq j BS B) :
    Nonempty $ SequenceOfBlowupsPushforward j BS B := by
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  refine ⟨⟨hlen, fun i hi => σ i $ by omega, fun i hi => hci i _, h0, ?_, ?_⟩⟩
  simp_all
  simp_all

theorem isomorphic {j : S ⟶ X} [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (d : SequenceOfBlowupsPushforward j BS B) (d' : SequenceOfBlowupsPushforward j BS B') :
    B.Isomorphic B' := by
  have hlength := d.lengthEq ▸ d'.lengthEq
  have hSL := d.lengthEq
  have key : ∀ n, n ≤ B.length →
      ∃ e : ∀ i, i ≤ n → (B.schemeAt i ≅ B'.schemeAt i),
        (∀ i (hi : i ≤ n) (h1 : i ≤ B.length) h2,
            d.σ i h1 ≫ (e i hi).hom = d'.σ i h2) ∧
        ((e 0 (zero_le n)).hom ≫ sbIzH B' = sbIzH B) ∧
        (∀ i (hi : i + 1 ≤ n),
            (e (i + 1) hi).hom ≫ B'.transitionMapSucc i
              = B.transitionMapSucc i ≫ (e i (le_of_succ_le hi)).hom) := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨fun i hi => eqToIso (congrArg B.schemeAt (le_zero.mp hi)) ≪≫
          (B.isoZero ≪≫ B'.isoZero.symm) ≪≫
          eqToIso (congrArg B'.schemeAt (le_zero.mp hi).symm), ?_, ?_, ?_⟩
        intro i hi h1 h2
        obtain rfl : i = 0 := le_zero.mp hi
        have hgoal : d.σ 0 h1 ≫ sbIzH B ≫ sbIzI B' = d'.σ 0 h2 := by
          rw [← assoc, d.zero.trans d'.zero.symm, assoc, m145, comp_id]
        simpa using hgoal
        simp
        simp_all
    | succ n ih =>
        intro hn1
        obtain ⟨e, hsg_, h0, hsq⟩ := ih (by omega)
        have hnB : n < B.length := by omega
        have hnB' : n < B'.length := by omega
        have hnS : n < BS.length := by omega
        let _a2 := e n le_rfl
        have hcen : (B'.center n).comap _a2.hom = B.center n := by
          rw [d'.center n hnB', ← hsg_ n le_rfl hnB.le hnB'.le, imageIdealSheaf_comp, comap_imageIdealSheaf_of_isIso, d.center n hnB]
        obtain ⟨g, hg⟩ := exists_iso_succ_comp_blowupMorphism B B' n hnB hnB' _a2 hcen
        refine ⟨fun i hi => if hin : i ≤ n then e i hin else
            eqToIso (congrArg B.schemeAt (by omega : i = n + 1)) ≪≫ g ≪≫
              eqToIso (congrArg B'.schemeAt (by omega : n + 1 = i)), ?_, ?_, ?_⟩
        intro i hi h1 h2
        by_cases hin : i ≤ n
        simp_all
        have hie : i = n + 1 := by omega
        subst hie
        simp only [dif_neg hin, trans_hom, eqToIso.hom, eqToHom_refl,
          id_comp, comp_id]
        let _a1 := d'.σ n hnB'.le
        have hBcen : (B'.center n).comap _a1 = BS.center n := by
          have := d'.isClosedImmersion n hnB'.le
          rw [d'.center n hnB', show imageIdealSheaf _a1 (BS.center n)
              = (BS.center n).map _a1 from map_eq_imageIdealSheaf ..,
            p30]
        let _a0 := BS.transitionMapSucc n ≫ _a1
        have hcart : p17
            ((B'.center n).comap _a0) := by
          rw [comap_comp, hBcen]
          exact left (BS.isBlowupAlongIdealSheaf_blowupMorphism n hnS)
        refine (right (B'.isBlowupAlongIdealSheaf_blowupMorphism n hnB') _
          _a0 hcart).unique ?_ (d'.square n hnB')
        rw [assoc, hg, ← assoc, d.square n hnB, assoc,
          hsg_ n le_rfl hnB.le hnB'.le]
        simp_all
        intro i hi
        by_cases hin : i + 1 ≤ n
        have hin' := le_of_succ_le hin
        simp only [dif_pos hin, dif_pos hin']
        exact hsq i hin
        have hien : i = n := by omega
        have hile := le_of_eq hien
        subst hien
        simp only [dif_neg hin, dif_pos hile, trans_hom, eqToIso.hom, eqToHom_refl,
          id_comp, comp_id]
        exact hg
  obtain ⟨e, hsg_, h0, hsq⟩ := key B.length le_rfl
  refine ⟨hlength, e, h0, ?_, ?_⟩
  intro i hi
  exact hsq i hi
  intro i hi
  let hi' : i < B'.length := by omega
  rw [d'.center i hi', ← hsg_ i hi.le hi.le (by omega), imageIdealSheaf_comp, comap_imageIdealSheaf_of_isIso, d.center i hi]
end

end SequenceOfBlowupsPushforward

theorem IsPushforwardBlowupSeq.isomorphic {S X : Sch} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (h' : IsPushforwardBlowupSeq j BS B') :
    B.Isomorphic B' := by
  obtain ⟨d⟩ := SequenceOfBlowupsPushforward.nonempty_of_isPushforward j h
  obtain ⟨d'⟩ := SequenceOfBlowupsPushforward.nonempty_of_isPushforward j h'
  exact d.isomorphic d'




section
variable {X X1 : Sch} (pi_ : X1 ⟶ X)
theorem support_strictTransform_subset_preimage
    (Z D : ISD X) :
    (support (strictTransform pi_ Z D) : Set ↥X1) ⊆ ⇑pi_ ⁻¹' (support D : Set ↥X) := by
  have _i28 : (spI (cmI D pi_) : Set ↥X1) ⊆ preimage pi_ D.support := by
    simp
  refine subset_trans ?_ _i28
  intro x hx
  have h2 :=
    stalkIdeal_mono (comap_le_strictTransform pi_ Z D) x
  refine mpr_ (mem_support_iff_stalkIdeal_ne_top (cmI D pi_) x) ?_
  intro htop
  rw [htop, top_le_iff] at h2
  exact (mp (mem_support_iff_stalkIdeal_ne_top (p6 pi_ Z D) x) hx) h2
end

section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}

section
variable {U} {n} (c : EtaleChart p U n) {V} (hVU : V ≤ U)
@[simp]
theorem EtaleChart.map_restrict :
    (c.restrict hVU).map = X.homOfLE hVU ≫ c.map :=
  c.restrict_map hVU

theorem EtaleChart.coordIdeal_restrict (S : FinSet n) :
    (c.restrict hVU).coordIdeal S = (c.coordIdeal S).comap (X.homOfLE hVU) := by
  rw [p33, p33, c.restrict_map hVU]
  simp [comap_comp]
end

private theorem getElemOpt_append_length_add.{v} {al_ : Type v} (L2_ : List al_) :
    ∀ L1_ i, (L1_ ++ L2_)[length L1_ + i]? = L2_[i]? := by
  intro L1_
  induction L1_ with
  | nil => intro i; simp
  | cons b L ih =>
      intro i
      have hlen : length (b :: L) + i = (length L + i) + 1 := by
        simp [length_cons]
        omega
      rw [cons_append, hlen, List.getElem?_cons_succ]
      exact ih i

private theorem getElem_append_length_add.{v} {al_ : Type v} (L1_ L2_ : List al_) (i : ℕ)
    (hi : i < length L2_) (hi' : length L1_ + i < length (L1_ ++ L2_)) :
    (L1_ ++ L2_)[length L1_ + i]'hi' = L2_[i]'hi :=by simp_all
section
variable {Z : ISD X}
theorem HasStrictNormalCrossingsWith.of_append {L1_ L2_ : Bdy X}
    (h : HasStrictNormalCrossingsWith p Z $ L1_ ++ L2_) : HasStrictNormalCrossingsWith p Z L2_ := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZ⟩ := h.exists_etaleChart hx
  refine ⟨U, hxU, m, c, fun i => a $ lenL L1_ + i, S, ?_, ?_, ?_, hZ⟩
  intro i hi j hj t hti htj
  have hi' : lenL L1_ + i < lenL (L1_ ++ L2_) := by simp_all
  have hj' : lenL L1_ + j < lenL (L1_ ++ L2_) := by simp_all
  have heq := hinj _ hi' _ hj' t hti htj
  omega
  intro i hi hni
  have hi' : lenL L1_ + i < lenL (L1_ ++ L2_) := by simp_all
  have h2 := hnone _ hi' hni
  rwa [getElem_append_length_add L1_ L2_ i hi hi'] at h2
  intro i hi t hti
  have hi' : lenL L1_ + i < lenL (L1_ ++ L2_) := by simp_all
  have h2 := hsome _ hi' t hti
  rwa [getElem_append_length_add L1_ L2_ i hi hi'] at h2

theorem hasStrictNormalCrossingsWith_cons_of_disjoint_support
    {M : Bdy X} (h : HasStrictNormalCrossingsWith p Z M) {D : ISD X}
    (hD : (support D : Set ↥X) ∩ (support Z : Set ↥X) = ∅) :
    HasStrictNormalCrossingsWith p Z (D :: M) := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZU⟩ := h.exists_etaleChart hx
  let _a0 := spI D
  have hxD : x ∉ _a0 := by
    intro hxD
    have hmem : x ∈ suppI D ∩ suppI Z := ⟨hxD, hx⟩
    rwa [hD] at hmem
  obtain ⟨V, hVU, hxV, hVD⟩ :
      ∃ V, V ≤ U ∧ x ∈ V ∧ ∀ y, y ∈ V → y ∉ spI D := by
    refine ⟨⟨U ∩ _a0ᶜ,
        U.2.inter D.support.2.isOpen_compl⟩, ?_, ⟨hxU, hxD⟩, ?_⟩
    intro y hy
    exact an1 hy
    intro y hy
    exact an2 hy
  refine ⟨V, hxV, m, c.restrict hVU, fun i => if i = 0 then none else a $ i - 1, S,
    ?_, ?_, ?_, ?_⟩
  intro i hi j hj t hti htj
  cases i with
  | zero => simp at hti
  | succ i' =>
    cases j with
    | zero => simp at htj
    | succ j' =>
      have hi' : i' < lenL M := by simp_all
      have hj' : j' < lenL M := by simp_all
      have hti' := by simpa using hti
      have htj' := by simpa using htj
      have heq := hinj i' hi' j' hj' t hti' htj'
      omega
  intro i hi hni
  cases i with
  | zero =>
    refine mpr_ (restrictIdeal_eq_top_iff_forall_notMem_support _ V) ?_
    intro y hy
    exact hVD y hy
  | succ i' =>
    have hi' : i' < lenL M := by simp_all
    have ha := by simpa using hni
    dsimp
    rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal _ hVU, hnone i' hi' ha]
    simp
  intro i hi t hti
  cases i with
  | zero => simp at hti
  | succ i' =>
    have hi' : i' < lenL M := by simp_all
    have ha := by simpa using hti
    dsimp
    rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal _ hVU, hsome i' hi' t ha, EtaleChart.coordIdeal_restrict]
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal _ hVU, hZU, EtaleChart.coordIdeal_restrict]

theorem HasStrictNormalCrossingsWith.append_of_support_disjoint {N : Bdy X}
    (h : HasStrictNormalCrossingsWith p Z N) {L : Bdy X}
    (hL : ∀ D ∈ L, (support D : Set ↥X) ∩ (support Z : Set ↥X) = ∅) :
    HasStrictNormalCrossingsWith p Z $ L ++ N := by
  revert hL
  induction L with
  | nil =>
      intro _
      exact h
  | cons D L ih =>
      intro hL
      exact hasStrictNormalCrossingsWith_cons_of_disjoint_support
        (ih fun E hE => hL E $ mpr_ mem_cons $ m61 hE)
        (hL D $ mpr_ mem_cons $ m51 rfl)
end

end

namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (u : MarkedBlowupSequenceData p I m E)
theorem boundary_length (t : ℕ) (ht : t ≤ u.length) :
    (boundary u t).length = E.length + t := by
  revert ht
  induction t with
  | zero =>
      intro _
      simp [u.boundary_zero]
  | succ j ih =>
      intro ht
      have hj := ht
      rw [u.boundary_succ j hj, length_append, length_map, ih $ le_of_lt hj]
      simp [length_cons, List.length_nil]
      omega

theorem index_lt_boundary_length {t : ℕ} (ht : t ≤ u.length)
    {i : ℕ} (hi : i < E.length) : i < (boundary u t).length := by
  rw [u.boundary_length t ht]
  omega

theorem boundary_succ_drop {t : ℕ} (ht : t < u.length)
    (n : ℕ) (hn : n ≤ (u.boundary t).length) :
    (u.boundary $ t + 1).drop n =
      ((u.boundary t).drop n).map (strictTransform (u.map t) $ u.center t) ++
        [exceptionalIdeal (u.map t) $ u.center t] := by
  have hlen := hn
  rw [← length_map] at hlen
  rw [u.boundary_succ t ht, List.drop_append_of_le_length hlen, ← map_drop]

theorem preimage_iUnion_support_boundary_subset
    (hN : ∀ i ≤ u.length, IsLocallyNoetherian $ u.obj i) {t : ℕ} (ht : t < u.length) :
    ⇑(u.map t) ⁻¹' (⋃ D ∈ u.boundary t, (D.support : CSet $ u.obj t)) ⊆
      ⋃ D ∈ u.boundary (t + 1), (D.support : Set ↥(u.obj $ t + 1)) := by
  have hlocNoeth := hN (t + 1) ht
  intro x hx
  obtain ⟨D, hD, hxD0⟩ := Set.mem_iUnion₂.mp $ Set.mem_preimage.mp hx
  by_cases hc : ⇑(u.map t) x ∈ (spI (u.center t) : CSet $ u.obj t)
  have hmem : p5 (u.map t) (u.center t) ∈ u.boundary (t + 1) := by
    rw [u.boundary_succ t ht, mem_append]
    exact m61 $ List.mem_singleton_self _
  have h2 : x ∈ (spI (exceptionalIdeal (u.map t) $ u.center t) : Set ↥(u.obj $ t + 1)) := by
    rw [exceptionalIdeal_eq_comap]
    have hEq : ((spI $ cmI (u.center t) $ u.map t) : Set ↥(u.obj $ t + 1))
        = ⇑(u.map t) ⁻¹' (spI (u.center t) : CSet $ u.obj t) := by
      simp
    rwa [hEq]
  exact Set.mem_iUnion₂.mpr ⟨_, hmem, h2⟩
  have hmem : p6 (u.map t) (u.center t) D ∈ u.boundary (t + 1) := by
    rw [u.boundary_succ t ht, mem_append]
    refine m51 ?_
    rw [List.mem_map]
    exact ⟨D, hD, rfl⟩
  have h2 : x ∈ (spI (p6 (u.map t) (u.center t) D) : Set ↥(u.obj $ t + 1)) := by
    rw [support_strictTransform_eq_closure_preimage (u.map t) (u.center t) D]
    exact subset_closure $ Set.mem_preimage.mpr $ mem_sdiff_of_mem hxD0 hc
  exact Set.mem_iUnion₂.mpr ⟨_, hmem, h2⟩

theorem projectionToBase_eq_projectionToBase_toBlowupSequenceData (i : ℕ) :
    u.proj i = u.toBlowupSequenceData.projectionToBase i := by
  induction i with
  | zero => rw [u.proj_zero, p23]
  | succ j ih => rw [u.proj_succ j, p43, ih]

theorem toBlowupSequenceData_boundary_eq_boundary :
    ∀ i, i ≤ u.length → u.toBlowupSequenceData.boundaryFrom E i = boundary u i := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [BlowupSequenceData.boundary_zero, u.boundary_zero]
  | succ j ih =>
      intro hj
      have hjlt := hj
      rw [p52, ih $ le_of_lt hjlt, u.boundary_succ j hjlt]
end

private theorem getElemOpt_map_append.{v, w} {al_ : Type v} {be_ : Type w} (f : al_ → be_) (T : List be_) :
    ∀ L i, i < length L → (List.map f L ++ T)[i]? = Option.map f (L[i]?) := by
  intro L
  induction L with
  | nil =>
      intro i hi
      simp at hi
  | cons a L ih =>
      intro i hi
      cases i with
      | zero => simp
      | succ j =>
          have hj : j < lenL L := by simp_all
          simp [m75, cons_append, List.getElem?_cons_succ]
          exact ih j hj

private theorem getElem_map_append.{v, w} {al_ : Type v} {be_ : Type w} (f : al_ → be_)
    (L : List al_) (T : List be_) (i : ℕ) (hi : i < length L)
    (hi' : i < length (List.map f L ++ T)) :
    (List.map f L ++ T)[i]'hi' = f (L[i]'hi) :=by simp_all
theorem eq_of_exceptionalIdeal_pow_mul_eq_mul {Y Y' : Sch} {pi_ : Y' ⟶ Y}
    {Z : ISD Y} (h : IsBlowupAlongIdealSheaf pi_ Z) (n : ℕ) {A B : ISD Y'}
    (e : exceptionalIdeal pi_ Z ^ n * A = exceptionalIdeal pi_ Z ^ n * B) : A = B := by
  rw [p9] at e
  exact eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul h.1 n e

section
variable (u : MarkedBlowupSequenceData p I m E)
theorem toBlowupSequenceData_controlledTransform_eq_ideal :
    ∀ i, i ≤ u.length → u.toBlowupSequenceData.controlledTransform I m i = u.ideal i := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [p53, u.ideal_zero]
  | succ j ih =>
      intro hj
      have hjlt := hj
      have hIH := ih $ le_of_lt hjlt
      have hex : ∃ B : IdealSheafData $ u.obj $ j + 1,
          p5 (u.map j) (u.center j) ^ m * B =
            cmI (u.toBlowupSequenceData.controlledTransform I m j) (u.map j) := by
        refine ⟨u.ideal $ j + 1, ?_⟩
        rw [hIH]
        exact u.ideal_succ j hjlt
      refine eq_of_exceptionalIdeal_pow_mul_eq_mul (u.isBlowup j hjlt) m ?_
      rw [u.toBlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ I m j hex, hIH]
      exact sy_ $ u.ideal_succ j hjlt

theorem orderAtLeastLocus_disjoint_boundary_of_le
    (hdesc : ∀ t < u.length,
      orderAtLeastLocus (u.ideal $ t + 1) m ⊆ ⇑(u.map t) ⁻¹' orderAtLeastLocus (u.ideal t) m)
    {i : ℕ} (hi : i < E.length) {r : ℕ} (hr : r ≤ u.length)
    (hsep : orderAtLeastLocus (u.ideal r) m ∩
        ((((u.boundary r)[i]'(u.index_lt_boundary_length hr hi)).support :
          CSet $ u.obj r)) = ∅) :
    ∀ t, r ≤ t → ∀ ht : t ≤ u.length,
      orderAtLeastLocus (u.ideal t) m ∩
        ((((u.boundary t)[i]'(u.index_lt_boundary_length ht hi)).support :
          CSet $ u.obj t)) = ∅ := by
  intro t hrt
  induction t, hrt using le_induction with
  | base =>
      intro ht
      exact hsep
  | succ t hrt ih =>
      intro ht
      have htlt := ht
      have hxl :=
        u.index_lt_boundary_length (le_of_lt htlt) hi
      let _a0 := p6 (u.map t) $ u.center t
      let _a1 := p5 (u.map t) $ u.center t
      have hlen2 : i < (m39 _a0 (u.boundary t)
          ++ [_a1]).length := by
        rw [length_append, length_map]
        omega
      have hbeq : (u.boundary $ t + 1)[i]'(u.index_lt_boundary_length ht hi)
          = p6 (u.map t) (u.center t) ((u.boundary t)[i]'hxl) := by
        exact m32 (List.getElem_of_eq (u.boundary_succ t htlt)
          (u.index_lt_boundary_length ht hi)) $ getElem_map_append _a0 (u.boundary t) [_a1] i hxl hlen2
      refine eq_empty_of_subset_empty ?_
      rintro x ⟨hx1, hx2⟩
      rw [hbeq] at hx2
      have hx1' :=
        Set.mem_preimage.mp $ hdesc t htlt hx1
      have hx2' :=
        Set.mem_preimage.mp
          (support_strictTransform_subset_preimage (u.map t) (u.center t)
            ((u.boundary t)[i]'hxl) hx2)
      have hfalse : (⇑(u.map t) x) ∈ (∅ : CSet $ u.obj t) := by
        rw [← ih $ le_of_lt htlt]
        exact mem_inter hx1' hx2'
      simp at hfalse

theorem isMarked : u.toBlowupSequenceData.IsMarked p I m E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  intro i hi
  refine ⟨ideal u $ i + 1, ?_⟩
  rw [toBlowupSequenceData_controlledTransform_eq_ideal u i $ le_of_lt hi]
  exact u.ideal_succ i hi
  intro i hi
  rw [toBlowupSequenceData_controlledTransform_eq_ideal u i $ le_of_lt hi]
  exact u.center_order i hi
  intro i hi
  have h := u.center_smooth i hi
  rwa [projectionToBase_eq_projectionToBase_toBlowupSequenceData u i] at h
  intro i hi
  have h := u.center_snc i hi
  rwa [projectionToBase_eq_projectionToBase_toBlowupSequenceData u i, ← toBlowupSequenceData_boundary_eq_boundary u i $ le_of_lt hi] at h
end

end MarkedBlowupSequenceData




structure EtaleMaxContactComparison (k : Type) [Field k] {P : Sch}
    (p : P ⟶ Sp k) [LocallyOfFiniteType p]
    (A : ISD P) (mu_ : ℕ) (N : Bdy P)
    (H1_ H2_ : ISD P) (pt : P) where
  W : Sch
  f1_ : W ⟶ P
  f2_ : W ⟶ P
  w : W
  [isAffine : IsAffine W]
  [etale_f₁ : Etale f1_]
  [etale_f₂ : Etale f2_]
  [lft_f₁ : LocallyOfFiniteType $ f1_ ≫ p]
  base_f1 : f1_.base w = pt
  base_f2 : f2_.base w = pt
  comap_A : A.comap f1_ = A.comap f2_
  comap_H : H1_.comap f1_ = H2_.comap f2_
  comap_N : ∀ J ∈ N, J.comap f1_ = J.comap f2_
  comp_p : f1_ ≫ p = f2_ ≫ p
  maxContact_comp :
    subschemeι (@maxContactIdeal k _ _ W (f1_ ≫ p) lft_f₁ (A.comap f1_) mu_) ≫ f1_ =
      subschemeι (@maxContactIdeal k _ _ W (f1_ ≫ p) lft_f₁ (A.comap f1_) mu_) ≫ f2_

theorem ideal_eq_of_map_eq_of_leftInverse {R S : Type} [CommRing R] [CommRing S]
    (σ : R →+* S) (ta_ : S →+* R) (htasg : ta_.comp σ = RingHom.id R)
    {A B : Ideal R} (hmap : Ideal.map σ A = Ideal.map σ B) : A = B := by
  have h2 := congrArg (Ideal.map ta_) hmap
  rwa [map_map, map_map, htasg, map_id, map_id] at h2

theorem idealSheafData_eq_of_forall_comap_eq {X : Sch} {ι : Type} (Y : ι → Sch)
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion $ f i]
    (hcov : (⋃ i, range ⇑(f i).base) = univ)
    (I J : ISD X) (h : ∀ i, I.comap (f i) = J.comap (f i)) : I = J := by
  have key : ∀ x, stalkIdeal I x = stalkIdeal J x := by
    intro x
    have hx : x ∈ (⋃ i, range ⇑(f i).base) := by simp_all
    obtain ⟨i, hi⟩ := mp_ mem_iUnion hx
    obtain ⟨y, hy⟩ := mp_ mem_range hi
    subst hy
    let _s0 := (f i).stalkMap y
    have hinv : (inv _s0).hom.comp _s0.hom
        = m99 (stkX X $ bsM (f i) y) := by
      rw [← m225, m118, CommRingCat.hom_id]
    refine ideal_eq_of_map_eq_of_leftInverse _ _ hinv ?_
    rw [← stalkIdeal_comap (f i) I y, ← stalkIdeal_comap (f i) J y, h i]
  exact le_antisymm (mpr_ (le_iff_forall_stalkIdeal_le I J) fun x => le_of_eq $ key x) $ mpr_ (le_iff_forall_stalkIdeal_le J I) fun x => le_of_eq (key x).symm

private theorem comap_eq_ker_pullback_fst {X Y : Sch} (f : X ⟶ Y) (I : ISD Y) :
    I.comap f = ker (fst f I.si) := rfl

open CategoryTheory.Limits in
theorem iUnion_range_sigmaio_base_eq_univ {ι : Type} (X : ι → Sch) :
    (⋃ i, range ⇑(Sigma.ι X i).base) = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk X).surjective x
  have hx' := by simpa using hx
  exact mpr_ mem_iUnion ⟨i, ⟨y, hx'⟩⟩

theorem derivIdealSheafIterate_congr_of_eq_of_eq (k : Type) [CommRing k] [IsNoetherianRing k]
    {X : Sch} (p q : X ⟶ Sp k)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] (hpq : p = q) (r : ℕ)
    (I J : ISD X) (hIJ : I = J) :
    derivIdealSheafIterate k p r I = derivIdealSheafIterate k q r J := by
  subst hpq
  subst hIJ
  rfl

theorem hom_ext_of_opens_cover {X : Sch} {ι : Type} (U : ι → Opn X)
    (hcov : ∀ x : ↥X, ∃ i, x ∈ U i) {Q : Sch} (a b : X ⟶ Q)
    (hab : ∀ i, (U i).i ≫ a = (U i).i ≫ b) : a = b := by
  refine hom_ext
    (mkOfCovers ι (fun i => oSch $ U i) (fun i => opI $ U i) ?_) a b
    hab
  intro x
  obtain ⟨i, hi⟩ := hcov x
  exact ⟨i, ⟨x, hi⟩, rfl⟩

open CategoryTheory.Limits in
theorem subschemeio_comp_eq_of_forall_sigmaio_comap {ι : Type} (Wf : ι → Sch)
    {Q : Sch} (M : IdealSheafData $ ∐ Wf) (a b : (∐ Wf) ⟶ Q)
    (h : ∀ i, (M.comap $ Sigma.ι Wf i).subschemeι ≫ Sigma.ι Wf i ≫ a
            = (M.comap $ Sigma.ι Wf i).subschemeι ≫ Sigma.ι Wf i ≫ b) :
    M.si ≫ a = M.si ≫ b := by
  refine hom_ext_of_opens_cover
    (fun i => siI M ⁻¹ᵁ (Sigma.ι Wf i).opensRange) ?_ _ _ ?_
  intro x
  have hx : M.subschemeι.base x ∈ (⋃ i, range ⇑(Sigma.ι Wf i).base) := by
    rw [iUnion_range_sigmaio_base_eq_univ]
    trivial
  obtain ⟨i, hi⟩ := mp_ mem_iUnion hx
  exact ⟨i, hi⟩
  intro i
  let _s0 := siI M ⁻¹ᵁ (Sigma.ι Wf i).opensRange
  have hrange : range ⇑(opI _s0
        ≫ siI M).base ⊆ range ⇑(Sigma.ι Wf i).base := by
    rintro y ⟨z, rfl⟩
    exact z.2
  obtain ⟨al_, hal_⟩ : ∃ al_,
      al_ ≫ Sigma.ι Wf i
        = opI _s0 ≫ siI M :=
    ⟨lift _ _ hrange, lift_fac _ _ hrange⟩
  let _a0 := pullback.fst (Sigma.ι Wf i) M.si
  obtain ⟨be_, hbe_⟩ : ∃ be_ : oSch _s0
        ⟶ pullback (Sigma.ι Wf i) M.si,
      be_ ≫ _a0 = al_ :=
    ⟨pullback.lift al_ (opI _s0) hal_,
      pullback.lift_fst _ _ _⟩
  let _m0 := cmI M $ Sigma.ι Wf i
  have hker : ker (siI _m0)
      ≤ m149 _a0 := by
    rw [q2]
    exact le_of_eq $ comap_eq_ker_pullback_fst (Sigma.ι Wf i) M
  obtain ⟨u, hu⟩ : ∃ u : pullback (Sigma.ι Wf i) M.si
        ⟶ subS _m0,
      u ≫ siI _m0
        = _a0 :=
    ⟨m64 _ _ hker, m154 _ _ hker⟩
  have keyA : opI _s0 ≫ siI M
      = (be_ ≫ u) ≫ (siI _m0 ≫ Sigma.ι Wf i) := by
    simp [assoc]
    rw [← assoc u, hu, ← assoc, hbe_, hal_]
  have e1 : (opI _s0 ≫ siI M) ≫ a
      = (opI _s0 ≫ siI M) ≫ b := by
    rw [keyA]
    simp [assoc]
    rw [h i]
  simpa only [assoc] using e1

open CategoryTheory.Limits in
theorem exists_etale_maxContactIdeal_comparison_of_finite_cover {k : Type} [Field k] [CharZero k]
    {P : Sch}
    (p : P ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (A : ISD P) (mu_ : ℕ) (N : Bdy P) (H1_ H2_ : ISD P)
    {ι : Type} [Finite ι] (pts : ι → ↥P)
    (c : ∀ i, EtaleMaxContactComparison k p A mu_ N H1_ H2_ (pts i))
    (hcov : orderAtLeastLocus A mu_ ⊆ ⋃ i, (range ⇑(c i).f1_.base ∩ range ⇑(c i).f2_.base)) :
    ∃ (V : Sch) (g1_ : V ⟶ P) (g2_ : V ⟶ P) (_ : Etale g1_) (_ : Etale g2_)
      (_ : QuasiCompact (g1_ ≫ p)) (hlft : LocallyOfFiniteType (g1_ ≫ p)),
      g1_ ≫ p = g2_ ≫ p ∧
      orderAtLeastLocus A mu_ ⊆ range ⇑g1_.base ∧
      orderAtLeastLocus A mu_ ⊆ range ⇑g2_.base ∧
      A.comap g1_ = A.comap g2_ ∧
      H1_.comap g1_ = H2_.comap g2_ ∧
      N.map (fun J => J.comap g1_) = N.map (fun J => J.comap g2_) ∧
      subschemeι (@maxContactIdeal k _ _ V (g1_ ≫ p) hlft (A.comap g1_) mu_) ≫ g1_ =
        subschemeι (@maxContactIdeal k _ _ V (g1_ ≫ p) hlft (A.comap g1_) mu_) ≫ g2_ := by
  classical
  have hWaff : ∀ i, IsAffine (c i).W := fun i => (c i).isAffine
  have hWe1 : ∀ i, Etale (c i).f1_ := fun i => (c i).etale_f₁
  have hWe2 : ∀ i, Etale (c i).f2_ := fun i => (c i).etale_f₂
  have hWlft : ∀ i, LocallyOfFiniteType ((c i).f1_ ≫ p) := fun i => (c i).lft_f₁
  have hoi : ∀ i, IsOpenImmersion (Sigma.ι (fun j => (c j).W) i) := fun i => inferInstance
  have hVaff : IsAffine (∐ fun i => (c i).W) := inferInstance
  have he1_ :=
    etale_sigmaDesc (fun i => (c i).f1_) fun i => (c i).etale_f₁
  have he2_ :=
    etale_sigmaDesc (fun i => (c i).f2_) fun i => (c i).etale_f₂
  have hlft : LocallyOfFiniteType ((Sigma.desc fun i => (c i).f1_) ≫ p) := inferInstance
  have hcsV : CompactSpace ↥(∐ fun i => (c i).W) := inferInstance
  have hss : Subsingleton ↥(Sp k) := inferInstance
  have hqc : QuasiCompact ((Sigma.desc fun i => (c i).f1_) ≫ p) := by
    apply AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
  refine ⟨∐ (fun i => (c i).W), Sigma.desc fun i => (c i).f1_, Sigma.desc fun i => (c i).f2_,
    he1_, he2_, hqc, hlft, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  refine Sigma.hom_ext _ _ fun i => ?_
  simp [← assoc, Sigma.ι_desc]
  exact (c i).comp_p
  intro y hy
  obtain ⟨i, hi⟩ := mp_ mem_iUnion $ hcov hy
  obtain ⟨w, hw⟩ := an1 hi
  refine ⟨bsM (Sigma.ι (fun j => (c j).W) i) w, ?_⟩
  show bsM (Sigma.ι (fun j => (c j).W) i ≫ Sigma.desc fun j => (c j).f1_) w = y
  rwa [Sigma.ι_desc]
  intro y hy
  obtain ⟨i, hi⟩ := mp_ mem_iUnion $ hcov hy
  obtain ⟨w, hw⟩ := an2 hi
  refine ⟨bsM (Sigma.ι (fun j => (c j).W) i) w, ?_⟩
  show bsM (Sigma.ι (fun j => (c j).W) i ≫ Sigma.desc fun j => (c j).f2_) w = y
  rwa [Sigma.ι_desc]
  refine idealSheafData_eq_of_forall_comap_eq (fun i => (c i).W)
    (fun i => Sigma.ι (fun j => (c j).W) i) (iUnion_range_sigmaio_base_eq_univ _) _ _ fun i => ?_
  rw [← comap_comp, ← comap_comp,
    Sigma.ι_desc, Sigma.ι_desc]
  exact (c i).comap_A
  refine idealSheafData_eq_of_forall_comap_eq (fun i => (c i).W)
    (fun i => Sigma.ι (fun j => (c j).W) i) (iUnion_range_sigmaio_base_eq_univ _) _ _ fun i => ?_
  rw [← comap_comp, ← comap_comp,
    Sigma.ι_desc, Sigma.ι_desc]
  exact (c i).comap_H
  refine map_congr_left fun J hJ => ?_
  refine idealSheafData_eq_of_forall_comap_eq (fun i => (c i).W)
    (fun i => Sigma.ι (fun j => (c j).W) i) (iUnion_range_sigmaio_base_eq_univ _) _ _ fun i => ?_
  rw [← comap_comp, ← comap_comp,
    Sigma.ι_desc, Sigma.ι_desc]
  exact (c i).comap_N J hJ
  have hMc : ∀ i, (@maxContactIdeal k _ _ (∐ fun j => (c j).W)
        ((Sigma.desc fun j => (c j).f1_) ≫ p) hlft
        (A.comap (Sigma.desc fun j => (c j).f1_)) mu_).comap (Sigma.ι (fun j => (c j).W) i)
      = @maxContactIdeal k _ _ (c i).W ((c i).f1_ ≫ p) (hWlft i) (A.comap (c i).f1_) mu_ := by
    intro i
    rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate,
      ← derivIdealSheafIterate_comap k ((Sigma.desc fun j => (c j).f1_) ≫ p)
        (Sigma.ι (fun j => (c j).W) i) (mu_ - 1) (A.comap (Sigma.desc fun j => (c j).f1_))]
    refine derivIdealSheafIterate_congr_of_eq_of_eq k _ _ ?_ (mu_ - 1) _ _ ?_
    rw [← assoc, Sigma.ι_desc]
    rw [← comap_comp, Sigma.ι_desc]
  refine subschemeio_comp_eq_of_forall_sigmaio_comap _ _ _ _ fun i => ?_
  rw [hMc i, Sigma.ι_desc, Sigma.ι_desc]
  exact (c i).maxContact_comp

end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable {R S : Type} [CommRing R] [CommRing S]
theorem exists_mem_mul_mem_of_map_le
    [Algebra R S] (M : Submonoid R) (hM : IsLocalization M S) (A B : Ideal R)
    (hA : FG A)
    (hAB : Ideal.map (algebraMap R S) A ≤ Ideal.map (algebraMap R S) B) :
    ∃ u : R, u ∈ M ∧ ∀ a ∈ A, u * a ∈ B := by
  classical
  obtain ⟨G, hG⟩ := hA
  have key : ∀ a, ∃ u, u ∈ M ∧ (a ∈ A → u * a ∈ B) := by
    intro a
    by_cases ha : a ∈ A
    have h1 :=
      hAB $ mem_map_of_mem _ ha
    rw [mem_map_algebraMap_iff (M := M) (S := S)] at h1
    obtain ⟨⟨b, s⟩, hEq⟩ := h1
    rw [← map_mul] at hEq
    obtain ⟨c, hc⟩ := mp_ (eq_iff_exists (M := M) (S := S)) hEq
    let _a1 := c
    refine ⟨_a1 * s, M.mul_mem c.2 s.2, fun _ => ?_⟩
    have hcalc : _a1 * s * a = _a1 * b := by linear_combination hc
    rw [hcalc]
    exact mul_mem_left B _ b.2
    exact ⟨1, M.one_mem, fun hmem => absurd hmem ha⟩
  choose u huM huB using key
  refine ⟨∏ g ∈ G, u g, Submonoid.prod_mem M fun g _ => huM g, ?_⟩
  intro a ha
  rw [← hG] at ha
  induction ha using span_induction with
  | mem z hz =>
      have hzA : z ∈ A := by rw [← hG]; exact subset_span hz
      rw [← mul_prod_erase G u $ Finset.mem_coe.mp hz]
      let _a0 := ∏ g ∈ G.erase z, u g
      have hre : u z * _a0 * z
          = _a0 * (u z * z) := by ring
      rw [hre]
      exact mul_mem_left B _ $ huB z hzA
  | zero => rw [mul_zero]; exact B.zero_mem
  | add y z _ _ hy hz => rw [mul_add]; exact B.add_mem hy hz
  | smul c y _ hy =>
      rw [smul_eq_mul, mul_left_comm]
      exact mul_mem_left B c hy

theorem map_le_map_of_isUnit_mul_mem
    (ph_ : R →+* S) (w : R) (hw : IsUnit $ ph_ w) (A B : Ideal R)
    (hAB : ∀ a ∈ A, w * a ∈ B) :
    Ideal.map ph_ A ≤ Ideal.map ph_ B := by
  rw [map_le_iff_le_comap]
  intro a ha
  obtain ⟨t, ht⟩ := hw.exists_right_inv
  have h4 : t * ph_ (w * a) ∈ m6 ph_ B := mul_mem_left _ _ $ mem_map_of_mem ph_ $ hAB a ha
  rw [map_mul, ← mul_assoc, mul_comm t $ ph_ w, ht, one_mul] at h4
  exact Ideal.mem_comap.mpr h4
end

theorem exists_opens_stalkIdeal_eq {X : Sch} [IsLocallyNoetherian X]
    (I J : ISD X) (x : X) (h : stalkIdeal I x = stalkIdeal J x) :
    ∃ W : Opn X, x ∈ W ∧ ∀ y : X, y ∈ W → stalkIdeal I y = stalkIdeal J y := by
  obtain ⟨U, hxU, hU⟩ := exists_isAffineOpen_mem x
  have hUaff := hU
  have := m188 ⟨U, hU⟩
  let _a2 := pGerm X U x hxU
  let instAlg :=
    _a2.hom.toAlgebra
  let _a3 := stkX X x
  have halg : (algebraMap U.sec ↑_a3) = _a2.hom := rfl
  have hloc := hUaff.isLocalization_stalk ⟨x, hxU⟩
  let _a0 := I.ideal ⟨U, hU⟩
  let _a1 := J.ideal ⟨U, hU⟩
  have hmapeq : m6 (algebraMap U.sec ↑_a3) _a0
      = m6 (algebraMap U.sec ↑_a3) _a1 := by
    rw [stalkIdeal_eq_map_germ I x ⟨U, hU⟩ hxU, stalkIdeal_eq_map_germ J x ⟨U, hU⟩ hxU] at h
    rwa [halg]
  obtain ⟨u1, hu1M, hu1_⟩ := exists_mem_mul_mem_of_map_le _ hloc _a0
    _a1 (m187 _) $ le_of_eq hmapeq
  obtain ⟨u2, hu2M, hu2_⟩ := exists_mem_mul_mem_of_map_le _ hloc _a1
    _a0 (m187 _) $ le_of_eq hmapeq.symm
  have hmb : ∀ z (hz : z ∈ U),
      z ∈ bOpn X (u1 * u2) ↔ IsUnit ((pGerm X U z hz).hom $ u1 * u2) := by
    intro z hz
    exact X.mem_basicOpen (u1 * u2) z hz
  have hxunit : IsUnit $ _a2.hom $ u1 * u2 := by
    have hone := map_units
      (M := (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
      (S := ↑_a3) ⟨u1 * u2, Submonoid.mul_mem _ hu1M hu2M⟩
    rwa [halg] at hone
  refine ⟨bOpn X $ u1 * u2, (hmb x hxU).mpr hxunit, ?_⟩
  intro y hy
  have hyU := X.basicOpen_le (u1 * u2) hy
  have hyunit := (hmb y hyU).mp hy
  have hv1 : ∀ a ∈ _a0, u1 * u2 * a ∈ _a1 := by
    intro a ha
    have he : u1 * u2 * a = u2 * (u1 * a) := by ring
    rw [he]
    exact mul_mem_left _ _ $ hu1_ a ha
  have hv2 : ∀ a ∈ _a1, u1 * u2 * a ∈ _a0 := by
    intro a ha
    have he : u1 * u2 * a = u1 * (u2 * a) := by ring
    rw [he]
    exact mul_mem_left _ _ $ hu2_ a ha
  rw [stalkIdeal_eq_map_germ I y ⟨U, hU⟩ hyU, stalkIdeal_eq_map_germ J y ⟨U, hU⟩ hyU]
  let _a4 := pGerm X U y hyU
  exact le_antisymm
    (map_le_map_of_isUnit_mul_mem _a4.hom (u1 * u2) hyunit _ _ hv1)
    (map_le_map_of_isUnit_mul_mem _a4.hom (u1 * u2) hyunit _ _ hv2)

section
variable {R : Type} [CommRing R]
theorem exists_notMem_mul_mem_of_map_le (S : Type) [CommRing S]
    [Algebra R S] (m : Ideal R) [hmp : m.IsPrime] [IsLocalization m.primeCompl S]
    {A B : Ideal R} (hAB : Ideal.map (algebraMap R S) A ≤ Ideal.map (algebraMap R S) B)
    {a : R} (ha : a ∈ A) : ∃ t : R, t ∉ m ∧ t * a ∈ B := by
  obtain ⟨⟨b, s⟩, hbs⟩ := mp_ (mem_map_algebraMap_iff m.primeCompl S) $ hAB $ mem_map_of_mem _ ha
  have hbs' := hbs
  rw [← map_mul] at hbs'
  obtain ⟨c, hc⟩ := mp_ (eq_iff_exists m.primeCompl S) hbs'
  refine ⟨c * s, ?_, ?_⟩
  intro hcs
  rcases hmp.mem_or_mem hcs with h1 | h1
  exact c.2 h1
  exact s.2 h1
  have hEq : (c * s) * a = c * b := by
    rw [← hc]
    ring
  rw [hEq]
  exact mul_mem_left _ _ b.2

theorem le_of_forall_isMaximal_exists_mul_mem {A B : Ideal R}
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ a ∈ A, ∃ t : R, t ∉ m ∧ t * a ∈ B) : A ≤ B := by
  intro a ha
  by_contra hab
  obtain ⟨C, hCmem⟩ : ∃ C : Ideal R, ∀ r : R, r ∈ C ↔ r * a ∈ B := by
    refine ⟨{ carrier := {r : R | r * a ∈ B}
              add_mem' := ?_
              zero_mem' := ?_
              smul_mem' := ?_ }, fun r => m22⟩
    intro x y hx hy
    show (x + y) * a ∈ B
    rw [add_mul]
    exact B.add_mem hx hy
    show (0 : R) * a ∈ B
    rw [zero_mul]
    exact B.zero_mem
    intro c x hx
    show (c • x) * a ∈ B
    rw [smul_eq_mul, mul_assoc]
    exact mul_mem_left _ _ hx
  have hCne : C ≠ ⊤ := by
    intro hCtop
    have h1 : 1 ∈ C := by
      rw [hCtop]
      exact Submodule.mem_top
    have h2 := mp_ (hCmem 1) h1
    rw [one_mul] at h2
    exact hab h2
  obtain ⟨m, hm, hCm⟩ := exists_le_maximal C hCne
  obtain ⟨t, htm, htB⟩ := h m hm a ha
  exact htm $ hCm $ mpr_ (hCmem t) htB
end

section
variable {Y : Sch} (A B : ISD Y) (W : Y.affineOpens)
theorem ideal_le_of_stalkIdeal_le (h : ∀ x : ↥Y, x ∈ W.1 → stalkIdeal A x ≤ stalkIdeal B x) :
    A.ideal W ≤ B.ideal W := by
  refine le_of_forall_isMaximal_exists_mul_mem ?_
  intro m hm a ha
  set y : PrimeSpectrum Γ(Y, W.1) := ⟨m, hm.isPrime⟩ with hydef
  set x : ↥Y := W.2.fromSpec.base y with hxdef
  have hy : x ∈ W.1 := by
    have hmem : x ∈ range (W.2.fromSpec.base) := ⟨y, rfl⟩
    rwa [W.2.range_fromSpec] at hmem
  let _a0 := pGerm Y W.1 x hy
  let algI :=
    _a0.hom.toAlgebra
  let _a1 := stkX Y x
  have hloc : IsLocalization m.primeCompl ↑_a1 :=
    W.2.isLocalization_stalk' y hy
  refine exists_notMem_mul_mem_of_map_le (↑_a1) m ?_ ha
  have halg : (algebraMap Γ(Y, W.1) ↑_a1)
      = _a0.hom := rfl
  rw [halg, ← stalkIdeal_eq_map_germ A x W hy, ← stalkIdeal_eq_map_germ B x W hy]
  exact h x hy

theorem ideal_eq_of_stalkIdeal_eq (h : ∀ x : ↥Y, x ∈ W.1 → stalkIdeal A x = stalkIdeal B x) :
    A.ideal W = B.ideal W :=
  le_antisymm (ideal_le_of_stalkIdeal_le A B W fun x hx => le_of_eq $ h x hx)
    (ideal_le_of_stalkIdeal_le B A W fun x hx => le_of_eq (h x hx).symm)
end

theorem restrictIdeal_eq_of_stalkIdeal_eq {X : Sch} (I J : ISD X) (U : Opn X)
    (h : ∀ y : X, y ∈ U → stalkIdeal I y = stalkIdeal J y) :
    restrictIdeal I U = restrictIdeal J U := by
  have key : ∀ V : U.toScheme.affineOpens,
      (restrictIdeal I U).ideal V = (restrictIdeal J U).ideal V := by
    intro V
    have hWaff := V.2.image_of_isOpenImmersion U.i
    have hWU : (opI U ''ᵁ V.1) ≤ U := by
      intro z hz
      obtain ⟨v, -, rfl⟩ := hz
      exact v.2
    have e : V.1 ≤ opPre U (imU U.i V.1) := by
      intro v hv
      have h2 : opIb U v ∈ opIb U '' (↑V.1) := ⟨v, hv, rfl⟩
      exact h2
    have hIJ := by
      refine ideal_eq_of_stalkIdeal_eq I J ⟨opI U ''ᵁ V.1, hWaff⟩ ?_
      intro z hz
      exact h z $ hWU hz
    rw [comap_ideal_eq_map_appLE I U.i ⟨opI U ''ᵁ V.1, hWaff⟩ V e,
      comap_ideal_eq_map_appLE J U.i ⟨opI U ''ᵁ V.1, hWaff⟩ V e, hIJ]
  have h1 := fun V => le_of_eq $ key V
  have h2 := fun V => le_of_eq (key V).symm
  exact le_antisymm h1 h2


section

variable {X : Sch} {k : Type} [Field k] {p : X ⟶ Sp k}
  {U : Opn X} {m : ℕ}


section
variable {X1 : Sch} (V : Opn X1)
theorem opensio_appLE_self_top_eq_topIso_inv
    (e : (⊤ : (toScheme V).Opens) ≤ ι V ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact presheaf_map_eq_of_parallel ..

theorem germ_topIso_inv_mem_maximalIdeal (y : ↥X1)
    (hy : y ∈ V) (htop : pointOfMem V y hy ∈ (⊤ : (V.toScheme).Opens)) (s : (X1.sec V))
    (hs : (X1.presheaf.germ V y hy).hom s ∈ maximalIdeal ↑(X1.presheaf.stalk y)) :
    (V.toScheme.presheaf.germ ⊤ (pointOfMem V y hy) htop).hom (V.topIso.inv.hom s) ∈
      maximalIdeal ↑(V.toScheme.presheaf.stalk (pointOfMem V y hy)) := by
  have e : (⊤ : Opn (oSch V)) ≤ opI V ⁻¹ᵁ V := fun z _ => z.2
  have hy' := hy
  have hnu : ¬ IsUnit ((pGerm X1 V y hy).hom s) := by simp_all
  have happ : V.topIso.inv = V.ι.app V ≫ V.toScheme.presheaf.map (homOfLE e).op :=
    (opensio_appLE_self_top_eq_topIso_inv V e).symm
  let _a0 := pointOfMem V y hy
  let _a2 := V.toScheme.presheaf.germ (opI V ⁻¹ᵁ V) _a0 hy'
  have h1 : V.topIso.inv ≫ V.toScheme.presheaf.germ ⊤ _a0 htop
      = V.ι.app V ≫ _a2 := by
    rw [happ, assoc, TopCat.Presheaf.germ_res]
  let _a1 := (V.ι.app V).hom s
  have h2 : (V.toScheme.presheaf.germ ⊤ _a0 htop).hom (V.topIso.inv.hom s)
      = _a2.hom
          _a1 := by
    have h := congrArg
      (fun f =>
        m4 f s) h1
    exact h
  rw [mem_maximalIdeal, mem_nonunits_iff, h2]
  intro hu
  apply hnu
  have hmem : _a0 ∈ opI V ⁻¹ᵁ (bOpn X1 s) := by
    rw [preimage_basicOpen]
    exact (V.toScheme.mem_basicOpen _a1 _a0 hy').2 hu
  exact (X1.mem_basicOpen s y hy).1 hmem
end

theorem coordIdeal_eq_of_coord_eq {n : ℕ} (hU : IsAffineOpen U) (c1_ c2_ : EtaleChart p U n)
    (S : FinSet n) (h : ∀ i ∈ S, c1_.coord i = c2_.coord i) :
    c1_.coordIdeal S = c2_.coordIdeal S := by
  have hUaff : IsAffine U.toScheme := hU
  have hcf : ∀ i ∈ S,
      (c1_.map.appTop).hom (m9 (Sp k)
          (up i))
        = (c2_.map.appTop).hom (m9 (Sp k)
          (up i)) := by
    intro i hi
    exact (st_ $ hom_inv_id_apply U.topIso $ c1_.coordTop i) $ tr_ (congrArg U.topIso.inv.hom $ h i hi) $ hom_inv_id_apply U.topIso $ c2_.coordTop i
  rw [p33, p33, coordSubspaceIdeal_eq_ofIdealTop_span_coord,
    comap_ofIdealTop, comap_ofIdealTop,
    m218, m218]
  refine congrArg ofIdealTop $ congrArg m17 ?_
  refine image_congr ?_
  rintro _ ⟨i, hi, rfl⟩
  exact hcf i $ Finset.mem_coe.mp hi

end

theorem mem_maximalIdeal_of_map_eq_zero {A C : Type} [CommRing A] [CommRing C]
    [IsLocalRing A] [Nontrivial C] (σ : A →+* C) {a : A} (ha : σ a = 0) :
    a ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := hu.map σ
  rw [ha] at h1
  exact zero_ne_one $ mp_ isUnit_zero_iff h1

section
variable {X W : Sch}
theorem eqToHom_comp_stalkMap_congr (f g : W ⟶ X) (hfg : f = g)
    (z : ↥W) (x : ↥X) (hf : f.base z = x) (hg : g.base z = x) :
    eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hf.symm) ≫ f.stalkMap z
      = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hg.symm) ≫ g.stalkMap z := by
  subst hfg
  rfl

section
variable (f : W ⟶ X)
section
variable (z) (x) (hfz : f.base z = x)
theorem eqToHom_comp_stalkMap_germ (U : Opn X) (hxU : x ∈ U) (V : Opn W) (hzV : z ∈ V)
    (e : V ≤ pre f U) (s : (X.sec U)) :
    (eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hfz.symm) ≫ f.stalkMap z).hom
        ((X.presheaf.germ U x hxU).hom s)
      = (W.presheaf.germ V z hzV).hom ((appLE f U V e).hom s) := by
  subst hfz
  have key : pGerm X U (bsM f z) hxU ≫ f.stalkMap z
      = appLE f U V e ≫ pGerm W V z hzV := by
    rw [appLE, assoc, W.presheaf.germ_res (homOfLE e) z hzV]
    simp
  rw [eqToHom_refl, id_comp]
  simpa only [hom_comp, m82] using (congrArg (m4 · s) key)

theorem eqToHom_comp_stalkMap_mem_maximalIdeal {a : ↥(X.presheaf.stalk x)}
    (ha : a ∈ maximalIdeal ↥(X.presheaf.stalk x)) :
    (eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hfz.symm) ≫ f.stalkMap z).hom a
      ∈ maximalIdeal ↥(W.presheaf.stalk z) :=by simp_all
end

theorem map_stalkMap_stalkIdeal_eq (I : ISD X)
    (z : ↥W) (x : ↥X) (hfz : f.base z = x) :
    Ideal.map ((f.stalkMap z).hom) (stalkIdeal I $ f.base z)
      = Ideal.map ((eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hfz.symm)
          ≫ f.stalkMap z).hom) (stalkIdeal I x) := by
  subst hfz
  rw [eqToHom_refl, id_comp]
end

theorem appLE_topIso_hom_eq_appTop (U : Opn X) (f : W ⟶ X)
    (g : W ⟶ U.toScheme) (hfg : f = g ≫ U.i) (e : (⊤ : Opn W) ≤ pre f U)
    (t : Γ(U.toScheme, ⊤)) :
    (appLE f U ⊤ e).hom (U.topIso.hom.hom t) = (g.appTop).hom t := by
  subst hfg
  have e0_ : (⊤) ≤ opPre U U := fun z _ => z.2
  have e' : (⊤) ≤ preU g (⊤) := fun z _ => trivial
  have hcomp : appLE (g ≫ opI U) U ⊤ e = U.ι.appLE U ⊤ e0_ ≫ appLE g ⊤ ⊤ e' :=
    (appLE_comp_appLE ..).symm
  let _a0 := W.presheaf.map (homOfLE e').op
  have hpar : _a0
      = W.presheaf.map (𝟙 $ m112 (⊤)) :=
    presheaf_map_eq_of_parallel ..
  have hmapid : _a0 = 𝟙 Γ(W, ⊤) := by
    rw [hpar, CategoryTheory.Functor.map_id]
  have happ : appLE g (⊤) (⊤) e' = hAT g := by
    show g.app ⊤ ≫ _a0 = hAT g
    rw [hmapid]
    exact comp_id _
  rw [hcomp, opensio_appLE_self_top_eq_topIso_inv U e0_, happ]
  simp only [hom_comp, m82]
  exact congrArg ((hAT g).hom) $ hom_inv_id_apply U.topIso t
end

theorem chartPullbackStalkMap_compat (k : Type) [Field k] {X : Sch}
    (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    {U : Opn X} {n : ℕ} (c1_ c2_ : EtaleChart p U n) (x : X) (hx : x ∈ U)
    (h : ChartsAgreeAt c1_ c2_ x hx) :
    (∀ i : Fin n,
        (chartPullbackFstStalkMap c1_ c2_ x hx h).hom ((X.presheaf.germ U x hx).hom $ c1_.coord i)
          = (chartPullbackSndStalkMap c1_ c2_ x hx h).hom
              ((X.presheaf.germ U x hx).hom $ c2_.coord i))
      ∧ (∀ a : k, (chartPullbackFstStalkMap c1_ c2_ x hx h).hom (stalkAlgebraMap k p x a)
          = (chartPullbackSndStalkMap c1_ c2_ x hx h).hom (stalkAlgebraMap k p x a))
      ∧ (∀ a : ↥(X.presheaf.stalk x),
          (chartPullbackSndStalkMap c1_ c2_ x hx h).hom a - (chartPullbackFstStalkMap c1_ c2_ x hx h).hom a
            ∈ maximalIdeal
                ↥((chartPullback c1_ c2_).presheaf.stalk $ chartPullbackPoint c1_ c2_ x hx h)) := by
  let _c0 := chartPullbackPoint c1_ c2_ x hx h
  let _a5 := pointOfMem U x hx
  let _c1 := specResidueFieldPoint _a5
  have hfb :=
    chartPullbackFst_base_chartPullbackPoint c1_ c2_ x hx h
  have hsb :=
    chartPullbackSnd_base_chartPullbackPoint c1_ c2_ x hx h
  let _m1 := chartPullbackFst c1_ c2_
  let _a12 := chartPullback c1_ c2_
  let _a3 := (⊤ : Opn _a12)
  let _a13 := pullback.fst c1_.map c2_.map
  have e1_ : _a3 ≤ preU _m1 U :=
    fun z _ => (bsM _a13 z).2
  let _m0 := chartPullbackSnd c1_ c2_
  let _a20 := pullback.snd c1_.map c2_.map
  have e2_ : _a3 ≤ preU _m0 U :=
    fun z _ => (bsM _a20 z).2
  have hcoordEach : ∀ i,
      (chartPullbackFstStalkMap c1_ c2_ x hx h).hom ((pGerm X U x hx).hom $ c1_.coord i)
        = (chartPullbackSndStalkMap c1_ c2_ x hx h).hom
            ((pGerm X U x hx).hom $ c2_.coord i) := by
    intro i
    rw [chartPullbackFstStalkMap_eq, chartPullbackSndStalkMap_eq,
      eqToHom_comp_stalkMap_germ _m1 _c0 x hfb U hx ⊤
        trivial e1_ $ c1_.coord i,
      eqToHom_comp_stalkMap_germ _m0 _c0 x hsb U hx ⊤
        trivial e2_ $ c2_.coord i]
    have hc1_ : c1_.coord i = U.topIso.hom.hom (c1_.coordTop i) := rfl
    have hc2_ : c2_.coord i = U.topIso.hom.hom (c2_.coordTop i) := rfl
    rw [hc1_, hc2_,
      appLE_topIso_hom_eq_appTop U _m1 _a13 rfl e1_
        (c1_.coordTop i),
      appLE_topIso_hom_eq_appTop U _m0 _a20 rfl e2_
        (c2_.coordTop i)]
    exact congrArg _ $ chartPullback_coordTop_eq c1_ c2_ i
  have hscalar : ∀ a,
      (chartPullbackFstStalkMap c1_ c2_ x hx h).hom (stalkAlgebraMap k p x a)
        = (chartPullbackSndStalkMap c1_ c2_ x hx h).hom (stalkAlgebraMap k p x a) := by
    intro a
    rw [← germ_sectionsAlgebraMap_apply k p U x hx a, chartPullbackFstStalkMap_eq,
      chartPullbackSndStalkMap_eq,
      eqToHom_comp_stalkMap_germ _m1 _c0 x hfb U hx ⊤
        trivial e1_ $ sectionsAlgebraMap k p U a,
      eqToHom_comp_stalkMap_germ _m0 _c0 x hsb U hx ⊤
        trivial e2_ $ sectionsAlgebraMap k p U a,
      sectionsAlgebraMap_appLE_apply k p _m1 U ⊤ e1_ a,
      sectionsAlgebraMap_appLE_apply k p _m0 U ⊤ e2_ a,
      chartPullbackFst_comp_eq_chartPullbackSnd_comp c1_ c2_]
  refine ⟨hcoordEach, hscalar, ?_⟩
  let _a0 := chartPullbackLift c1_ c2_ x hx h
  have hmor : _a0 ≫ chartPullbackFst c1_ c2_
      = _a0 ≫ chartPullbackSnd c1_ c2_ := by
    rw [chartPullbackLift_fst_assoc, chartPullbackLift_snd_assoc]
  have hstalkeq := eqToHom_comp_stalkMap_congr (_a0 ≫ chartPullbackFst c1_ c2_)
    (_a0 ≫ chartPullbackSnd c1_ c2_) hmor
    _c1 x hfb hsb
  obtain ⟨σ, hsg_⟩ : ∃ σ : stkX _a12 _c0 ⟶
      (stkX $ Spec $ U.toScheme.residueField _a5)
        _c1,
      σ = _a0.stalkMap _c1 :=
    ⟨_, rfl⟩
  have hcomp1 : (_a0 ≫ chartPullbackFst c1_ c2_).stalkMap
        _c1
      = _m1.stalkMap _c0 ≫ σ := by
    rw [hsg_]
    exact stalkMap_comp _ _ _
  have hcomp2 : (_a0 ≫ chartPullbackSnd c1_ c2_).stalkMap
        _c1
      = _m0.stalkMap _c0 ≫ σ := by
    rw [hsg_]
    exact stalkMap_comp _ _ _
  have hkey : chartPullbackFstStalkMap c1_ c2_ x hx h ≫ σ
      = chartPullbackSndStalkMap c1_ c2_ x hx h ≫ σ := by
    rw [chartPullbackFstStalkMap_eq, chartPullbackSndStalkMap_eq, assoc, assoc,
      ← hcomp1, ← hcomp2]
    exact hstalkeq
  intro a
  have h0 : σ.hom ((chartPullbackFstStalkMap c1_ c2_ x hx h).hom a)
      = σ.hom ((chartPullbackSndStalkMap c1_ c2_ x hx h).hom a) := m156 (congrArg m4 hkey) a
  refine mem_maximalIdeal_of_map_eq_zero σ.hom ?_
  rw [map_sub, ← h0, sub_self]

theorem spec_map_comp_fromSpecStalk_eq {X Z : Sch} (z : ↥Z) {x1_ x2_ : ↥X}
    (hx : x1_ = x2_) (al_ : X.presheaf.stalk x1_ ⟶ Z.presheaf.stalk z)
    (be_ : X.presheaf.stalk x2_ ⟶ Z.presheaf.stalk z)
    (halbe : al_ = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hx) ≫ be_) :
    Spec.map al_ ≫ X.fromSpecStalk x1_ = Spec.map be_ ≫ X.fromSpecStalk x2_ := by
  subst hx
  rw [halbe, eqToHom_refl, id_comp]

theorem fromSpecStalk_comp_eq_of_stalkMap_eq {X Y Z : Sch} (iom : Z ⟶ Y) (f g : Y ⟶ X) (z : ↥Z)
    (w : ↥Y) (hw : iom.base z = w) (x : ↥X) (hf : f.base w = x) (hg : g.base w = x)
    (ph1 ph2 : X.presheaf.stalk x ⟶ Y.presheaf.stalk w)
    (hph1 : ph1 = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hf.symm) ≫ f.stalkMap w)
    (hph2 : ph2 = eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hg.symm) ≫ g.stalkMap w)
    (rh_ : Y.presheaf.stalk w ⟶ Z.presheaf.stalk z)
    (hrh_ : rh_ = eqToHom (congrArg (fun y : ↥Y => Y.presheaf.stalk y) hw.symm) ≫ iom.stalkMap z)
    (hker : ∀ a : ↥(X.presheaf.stalk x), rh_.hom (ph1.hom a) = rh_.hom (ph2.hom a)) :
    Z.fromSpecStalk z ≫ iom ≫ f = Z.fromSpecStalk z ≫ iom ≫ g := by
  subst hph1
  subst hph2
  subst hrh_
  subst hw
  subst hf
  let _a0 := g.stalkMap (bsM iom z) ≫ iom.stalkMap z
  let _a1 := f.stalkMap (bsM iom z) ≫ iom.stalkMap z
  have hstalk : _a1
      = eqToHom (congrArg (stkX X) hg.symm)
          ≫ _a0 := by
    refine CommRingCat.hom_ext $ m48 fun a => ?_
    have ha := hker a
    simp [hom_comp, m82, eqToHom_refl,
      hom_id, id_apply] at ha ⊢
    exact ha
  have key := spec_map_comp_fromSpecStalk_eq (X := X) z hg.symm
    _a1 _a0 hstalk
  have L : ∀ u : Y ⟶ X, Z.fromSpecStalk z ≫ iom ≫ u
      = m12 (u.stalkMap (bsM iom z) ≫ iom.stalkMap z)
        ≫ X.fromSpecStalk (bsM u $ bsM iom z) := by simp_all
  rwa [L f, L g]

theorem exists_preimage_eq_of_isClosedImmersion {Y Z : Sch} (f : Z ⟶ Y) [IsClosedImmersion f]
    (W : Opn Z) : ∃ V : Opn Y, pre f V = W := by
  obtain ⟨t, ht, hteq⟩ := ((isClosedEmbedding f).toIsEmbedding.toIsInducing).isOpen_iff.mp W.2
  exact ⟨⟨t, ht⟩, m55 hteq⟩

theorem io_comp_eq_of_le {Z Y : Sch} {W0 W' : Opn Z} (hle : W0 ≤ W')
    {f g : Z ⟶ Y} (hfg : ι W' ≫ f = ι W' ≫ g) : ι W0 ≫ f = ι W0 ≫ g := by
  rw [← Scheme.homOfLE_ι _ hle, assoc, hfg, assoc]

theorem map_le_map_and_sub_mem_of_etaleCoordinates_shift (kk : Type) [Field kk] {ι : Type} {R : Type}
    [CommRing R] {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    [Algebra kk R] [Algebra (MvPolynomial ι kk) R] [IsScalarTower kk (MvPolynomial ι kk) R]
    [FormallyEtale (MvPolynomial ι kk) R]
    (ph_ ph' : R →+* B) (j : ι) (b : R)
    (hcong : ∀ f : R, ph_ f - ph' f ∈ maximalIdeal B)
    (hbe_ : ph_ b ∈ maximalIdeal B)
    (hconst : ∀ c : kk, ph_ (algebraMap (MvPolynomial ι kk) R $ MvPolynomial.C c)
      = ph' (algebraMap (MvPolynomial ι kk) R $ MvPolynomial.C c))
    (hne : ∀ i : ι, i ≠ j → ph_ (EtaleCoordinates.coord kk ι R i)
      = ph' (EtaleCoordinates.coord kk ι R i))
    (hj : ph_ (EtaleCoordinates.coord kk ι R j) + ph_ b
      = ph' (EtaleCoordinates.coord kk ι R j)) :
    (∀ M J : Ideal R, b ∈ M → M * derivIdeal kk J ≤ J → Ideal.map ph' J ≤ Ideal.map ph_ J)
      ∧ (∀ Iid : Ideal B, ph_ b ∈ Iid → ∀ f : R, ph_ f - ph' f ∈ Iid) := by
  classical
  have hD1 :=
    partialDeriv_coord_self kk ι R j
  have hD0 :=
    fun i hi => EtaleCoordinates.partialDeriv_coord_of_ne kk ι R j i $ m113 hi
  have hderivConst : ∀ c, (partialDeriv kk ι R j)
      (algebraMap (MvPolynomial ι kk) R $ m8 c) = 0 := by
    intro c
    have hmap : algebraMap (MvPolynomial ι kk) R (m8 c) = algebraMap kk R c := by
      rw [IsScalarTower.algebraMap_apply kk (MvPolynomial ι kk) R c]
      simp
    rw [hmap]
    exact Derivation.map_algebraMap _ c
  have hvar : ∀ i N, 1 ≤ N →
      TaylorExpansion.truncatedSeries ph_ (partialDeriv kk ι R j) (ph_ b) N
          (algebraMap (MvPolynomial ι kk) R $ m7 i) -
        ph' (algebraMap (MvPolynomial ι kk) R $ m7 i)
          ∈ maximalIdeal B ^ N := by
    intro i N hN
    have hco : algebraMap (MvPolynomial ι kk) R (m7 i)
        = p10 kk ι R i := rfl
    rcases m63 N 2 with h2 | h2
    have hN1 : N = 1 := by omega
    subst hN1
    rw [hco, truncatedSeries_length_one, pow_one]
    rcases eq_or_ne i j with hij | hij
    simp_all
    rw [hne i hij, sub_self]
    exact m97 _
    rcases eq_or_ne i j with hij | hij
    subst hij
    rw [hco, truncatedSeries_of_deriv_deriv_eq_zero ph_ _ (ph_ b) N h2 _
        (by rw [hD1]; simp), hD1, map_one, one_mul, hj, sub_self]
    exact m97 _
    rw [hco, truncatedSeries_of_deriv_deriv_eq_zero ph_ _ (ph_ b) N h2 _
        (by rw [hD0 i hij]; simp), hD0 i hij, map_zero, zero_mul, add_zero,
      hne i hij, sub_self]
    exact m97 _
  have hrep := isTaylorExpansionOn_mvPolynomial (k := kk) (ι := ι) ph_ ph'
    (partialDeriv kk ι R j) (ph_ b) hbe_ hconst hderivConst hvar
  have : FormallyUnramified (MvPolynomial ι kk) R := inferInstance
  refine ⟨fun M J hbM hMJ => ?_, fun Iid hbI f => sub_mem_of_isTaylorExpansionOn (MvPolynomial ι kk) ph_ ph' (partialDeriv kk ι R j) (ph_ b) hcong hbe_ hrep Iid hbI f⟩
  exact map_le_map_of_pow_mul_iterate_deriv_mem (MvPolynomial ι kk) ph_ ph'
    (partialDeriv kk ι R j) (ph_ b) b J hcong hbe_ hrep rfl
    (pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le kk M J (partialDeriv kk ι R j) b hMJ hbM)

section
variable (k : Type) [Field k] [CharZero k] {X : Sch} (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
section
variable {U : Opn X} (hU : IsAffineOpen U) {n : ℕ}
include hU
theorem map_le_map_and_sub_mem_of_etaleChart_coord_shift (c : EtaleChart p U n) (j : Fin n)
    (x : X) (hx : x ∈ U) [Algebra k ↥(X.presheaf.stalk x)]
    (halg : ∀ a : k, algebraMap k ↥(X.presheaf.stalk x) a = stalkAlgebraMap k p x a)
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (ph_ ph' : ↥(X.presheaf.stalk x) →+* B) (b : ↥(X.presheaf.stalk x))
    (hcong : ∀ f : ↥(X.presheaf.stalk x), ph_ f - ph' f ∈ maximalIdeal B)
    (hbe_ : ph_ b ∈ maximalIdeal B)
    (hconst : ∀ a : k, ph_ (stalkAlgebraMap k p x a) = ph' (stalkAlgebraMap k p x a))
    (hne : ∀ i : Fin n, i ≠ j → ph_ ((X.presheaf.germ U x hx).hom $ c.coord i)
      = ph' ((X.presheaf.germ U x hx).hom $ c.coord i))
    (hj : ph_ ((X.presheaf.germ U x hx).hom $ c.coord j) + ph_ b
      = ph' ((X.presheaf.germ U x hx).hom $ c.coord j)) :
    (∀ M J : Ideal ↥(X.presheaf.stalk x), b ∈ M → M * derivIdeal k J ≤ J →
        Ideal.map ph' J ≤ Ideal.map ph_ J)
      ∧ (∀ Iid : Ideal B, ph_ b ∈ Iid → ∀ f : ↥(X.presheaf.stalk x), ph_ f - ph' f ∈ Iid) := by
  let _s0 := UFin n
  let _c0 := MvPolynomial _s0 k
  let _c1 := pGerm X U x hx
  classical
  let instP :=
    toAlgebra $ _c1.hom.comp c.coordRingHom
  let _a0 := stkX X x
  have instScalarTower : IsScalarTower k _c0
      ↥_a0 := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [m185, halg a]
    show stalkAlgebraMap k p x a
      = _c1.hom (c.coordRingHom $ m8 a)
    rw [EtaleChart.coordRingHom_C, germ_sectionsAlgebraMap_apply]
  have instFormallyEtale : FormallyEtale _c0
      ↥_a0 := by
    let instChart := c.algebra
    let instGerm :=
      _c1.hom.toAlgebra
    have : IsScalarTower _c0 U.sec
        ↥_a0 := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : FormallyEtale _c0 U.sec :=
      c.algebra_formallyEtale hU
    let _a1 := hU.primeIdealOf ⟨x, hx⟩
    have : IsLocalization _a1.asIdeal.primeCompl
        ↥_a0 := hU.isLocalization_stalk ⟨x, hx⟩
    have : FormallyEtale U.sec ↥_a0 :=
      Algebra.FormallyEtale.of_isLocalization _a1.asIdeal.primeCompl
    exact Algebra.FormallyEtale.comp _c0 U.sec
      ↥_a0
  have hcd : ∀ i,
      p10 k _s0 ↥(stkX X x) (up i)
        = _c1.hom (c.coord i) := by
    intro i
    show _c1.hom (c.coordRingHom $ m7 $ up i) = _
    rw [EtaleChart.coordRingHom_X]
  have hconst' : ∀ a,
      ph_ (algebraMap _c0 ↥(stkX X x)
            (m8 a))
        = ph' (algebraMap _c0 ↥(stkX X x)
            (m8 a)) := by
    intro a
    have hA : algebraMap _c0 ↥(stkX X x)
        (m8 a) = stalkAlgebraMap k p x a := by
      show _c1.hom (c.coordRingHom $ m8 a) = _
      rw [EtaleChart.coordRingHom_C, germ_sectionsAlgebraMap_apply]
    rw [hA, hconst a]
  have hne' : ∀ i, i ≠ up j →
      ph_ (p10 k _s0 ↥(stkX X x) i)
        = ph' (p10 k _s0 ↥(stkX X x) i) := by
    rintro ⟨i⟩ hi
    have hij : i ≠ j := fun hc => hi $ by rw [hc]
    rw [hcd i]
    exact hne i hij
  have hj' := hj
  rw [← hcd j] at hj'
  exact map_le_map_and_sub_mem_of_etaleCoordinates_shift k ph_ ph' (up j) b hcong hbe_ hconst' hne' hj'

theorem chartPullbackFstStalkMap_eq_snd_of_coord_eq_zero (c1_ c2_ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c1_.coord i = c2_.coord i)
    (x : X) (hx : x ∈ U)
    (hg1_ : (X.presheaf.germ U x hx).hom (c1_.coord j) ∈
      maximalIdeal ↑(X.presheaf.stalk x))
    (hg2_ : (X.presheaf.germ U x hx).hom (c2_.coord j) ∈
      maximalIdeal ↑(X.presheaf.stalk x))
    [IsLocallyNoetherian $ chartPullback c1_ c2_]
    (h : ChartsAgreeAt c1_ c2_ x hx)
    (C : CRC)
    (rh_ : (chartPullback c1_ c2_).presheaf.stalk (chartPullbackPoint c1_ c2_ x hx h) ⟶ C)
    (hv1_ : rh_.hom ((chartPullbackFstStalkMap c1_ c2_ x hx h).hom
      ((X.presheaf.germ U x hx).hom $ c1_.coord j)) = 0)
    (hv2_ : rh_.hom ((chartPullbackFstStalkMap c1_ c2_ x hx h).hom
      ((X.presheaf.germ U x hx).hom $ c2_.coord j)) = 0) :
    ∀ a : ↥(X.presheaf.stalk x),
      rh_.hom ((chartPullbackFstStalkMap c1_ c2_ x hx h).hom a)
        = rh_.hom ((chartPullbackSndStalkMap c1_ c2_ x hx h).hom a) := by
  let _c0 := (pGerm X U x hx).hom (c1_.coord j) - (pGerm X U x hx).hom (c2_.coord j)
  let _c1 := pGerm X U x hx
  classical
  obtain ⟨hcoordEach, hscalar, hcong21⟩ := chartPullbackStalkMap_compat k p c1_ c2_ x hx h
  let _a0 := chartPullbackFstStalkMap c1_ c2_ x hx h
  let _a4 := chartPullbackPoint c1_ c2_ x hx h
  let _a1 := stkX (chartPullback c1_ c2_) _a4
  let _a2 := chartPullbackSndStalkMap c1_ c2_ x hx h
  have hcong12 : ∀ a : ↥(stkX X x),
      _a0.hom a - _a2.hom a
        ∈ maximalIdeal
            ↥_a1 := by
    intro a
    have hneg := neg_mem _ $ hcong21 a
    rwa [neg_sub] at hneg
  have hcoordNe : ∀ i, i ≠ j →
      _c1.hom (c1_.coord i) = _c1.hom (c2_.coord i) :=
    fun i hi => congrArg _ $ hcoord i hi
  let instRk := stalkAlgebra k p x
  have instBnoeth : IsNoetherianRing
      ↥_a1 := inferInstance
  let instAlgebraRat :=
    toAlgebra
      ((stalkAlgebraMap k (chartPullbackFst c1_ c2_ ≫ p) _a4).comp
        (algebraMap ℚ k))
  have hne : ∀ i, i ≠ j →
      _a0.hom (_c1.hom $ c2_.coord i)
        = _a2.hom
            (_c1.hom $ c2_.coord i) := by
    intro i hi
    rw [← hcoordNe i hi, hcoordEach i, hcoordNe i hi]
  let _a3 := _c1.hom $ c2_.coord j
  have hj' : _a0.hom
        _a3
      + _a0.hom
          _c0
      = _a2.hom
          _a3 := by
    rw [map_sub, ← hcoordEach j]
    ring
  have hbI : _a0.hom
      _c0 ∈ m41 rh_.hom := by
    rw [mem_ker, map_sub, map_sub, hv1_, hv2_, sub_zero]
  have hsub := an2 (map_le_map_and_sub_mem_of_etaleChart_coord_shift k p hU c2_ j x hx (fun _ => rfl)
    _a0.hom _a2.hom
    _c0
    hcong12 (eqToHom_comp_stalkMap_mem_maximalIdeal (chartPullbackFst c1_ c2_) _a4 x (chartPullbackFst_base_chartPullbackPoint c1_ c2_ x hx h) $ sub_mem _ hg1_ hg2_) hscalar hne hj') (m41 rh_.hom) hbI
  intro a
  have ha := hsub a
  rwa [mem_ker, map_sub, sub_eq_zero] at ha
end

end

theorem subschemeio_appLE_eq_zero {Y : Sch} (J : ISD Y)
    (V : Y.affineOpens) {s : Γ(Y, V.1)} (hs : s ∈ J.ideal V) :
    (J.subschemeι.appLE V.1 (J.si ⁻¹ᵁ V.1) le_rfl).hom s = 0 := by
  have h2 : s ∈ (J.subschemeι.ker).ideal V := by rw [q2 ..]
                                                 exact hs
  rw [appLE]
  simp [hom_comp, m82, RingHom.mem_ker.mp $ J.subschemeι.ideal_ker_le V h2, map_zero]

theorem stalkMap_germ_eq_zero_of_mem_ideal {X Y : Sch} (f : Y ⟶ X) (M : ISD X)
    (z : ↥((M.comap f).subscheme)) (w : ↥Y)
    (hw : (M.comap f).subschemeι.base z = w)
    (x : ↥X) (hf : f.base w = x) (U : Opn X) (hU : IsAffineOpen U) (hxU : x ∈ U)
    (V : Opn Y) (hV : IsAffineOpen V) (hwV : w ∈ V) (eV : V ≤ pre f U)
    (s : (X.sec U)) (hs : s ∈ M.ideal ⟨U, hU⟩) :
    (eqToHom (congrArg (fun y : ↥Y => Y.presheaf.stalk y) hw.symm)
        ≫ (M.comap f).subschemeι.stalkMap z).hom
      ((eqToHom (congrArg (fun y : ↥X => X.presheaf.stalk y) hf.symm) ≫ f.stalkMap w).hom
        ((X.presheaf.germ U x hxU).hom s)) = 0 := by
  rw [eqToHom_comp_stalkMap_germ f w x hf U hxU V hwV eV s]
  have hzV : z ∈ (cmI M f).si.pre V := by simp_all
  rw [eqToHom_comp_stalkMap_germ (cmI M f).si z w hw V hwV
      ((cmI M f).si.pre V) hzV le_rfl $ (appLE f U V eV).hom s]
  rw [subschemeio_appLE_eq_zero (cmI M f) ⟨V, hV⟩ $ appLE_mem_comap_ideal M f ⟨U, hU⟩ ⟨V, hV⟩ eV hs, map_zero]

section
variable (k : Type) [Field k] [CharZero k] {X : Sch} (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] (I : ISD X) {m : ℕ}
theorem exists_opens_chartPullback_eq_of_mem_maxContactIdeal (hm : 1 ≤ m)
    (hinv : IsMaxContactInvariant k p I m)
    {U : Opn X} (hU : IsAffineOpen U) {n : ℕ} (c1_ c2_ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c1_.coord i = c2_.coord i)
    (x : X) (hx : x ∈ U)
    (hmem1_ : c1_.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hmem2_ : c2_.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hg1_ : (X.presheaf.germ U x hx).hom (c1_.coord j) ∈
      maximalIdeal ↑(X.presheaf.stalk x))
    (hg2_ : (X.presheaf.germ U x hx).hom (c2_.coord j) ∈
      maximalIdeal ↑(X.presheaf.stalk x))
    (hsupp : x ∈ (maxContactIdeal k p I m).support)
    [IsLocallyNoetherian (chartPullback c1_ c2_)]
    [IsLocallyNoetherian ((maxContactIdeal k p I m).comap (chartPullbackFst c1_ c2_)).subscheme] :
    ∃ h : ChartsAgreeAt c1_ c2_ x hx,
      ∃ W : (chartPullback c1_ c2_).Opens, chartPullbackPoint c1_ c2_ x hx h ∈ W ∧
        (∀ y : ↥(chartPullback c1_ c2_), y ∈ W →
            stalkIdeal (I.comap (chartPullbackFst c1_ c2_)) y =
              stalkIdeal (I.comap (chartPullbackSnd c1_ c2_)) y) ∧
        restrictIdeal (I.comap (chartPullbackFst c1_ c2_)) W =
          restrictIdeal (I.comap (chartPullbackSnd c1_ c2_)) W ∧
        ((((maxContactIdeal k p I m).comap (chartPullbackFst c1_ c2_)).subschemeι.pre W).ι ≫
              ((maxContactIdeal k p I m).comap (chartPullbackFst c1_ c2_)).subschemeι ≫
                chartPullbackFst c1_ c2_ =
            (((maxContactIdeal k p I m).comap (chartPullbackFst c1_ c2_)).subschemeι.pre W).ι ≫
              ((maxContactIdeal k p I m).comap (chartPullbackFst c1_ c2_)).subschemeι ≫
                chartPullbackSnd c1_ c2_) ∧
        ((c1_.coordIdeal {j}).comap (pullback.fst c1_.map c2_.map) =
          (c2_.coordIdeal {j}).comap (pullback.snd c1_.map c2_.map)) ∧
        ∀ S : FinSet n, j ∉ S → c1_.coordIdeal S = c2_.coordIdeal S := by
  let _a13 := chartPullback c1_ c2_
  let _a3 := chartPullbackFst c1_ c2_
  let _c0 := cmI (maxContactIdeal k p I m) _a3
  classical
  have hagree : ChartsAgreeAt c1_ c2_ x hx := by
    refine chartsAgreeAt_of_germ_sub_mem_maximalIdeal c1_ c2_ x hx ?_
    intro i
    by_cases hij : i = j
    rw [hij]
    have e1 : U.topIso.inv.hom (c1_.coord j) = c1_.coordTop j :=
      hom_inv_id_apply U.topIso $ c1_.coordTop j
    have e2 : U.topIso.inv.hom (c2_.coord j) = c2_.coordTop j :=
      hom_inv_id_apply U.topIso $ c2_.coordTop j
    have h1 := germ_topIso_inv_mem_maximalIdeal U x hx (by trivial) (c1_.coord j) hg1_
    have h2 := germ_topIso_inv_mem_maximalIdeal U x hx (by trivial) (c2_.coord j) hg2_
    rw [e1] at h1
    rw [e2] at h2
    rw [map_sub]
    exact sub_mem _ h1 h2
    have hc := hcoord i hij
    rw [st_ (Iso.hom_inv_id_apply U.topIso $ c1_.coordTop i) ((congrArg U.topIso.inv.hom hc).trans (Iso.hom_inv_id_apply U.topIso $ c2_.coordTop i)), sub_self, map_zero]
    exact m97 _
  let _a11 := chartPullbackPoint c1_ c2_ x hx hagree
  let _a12 := chartPullbackSnd c1_ c2_
  have hst : stalkIdeal (cmI I (chartPullbackFst c1_ c2_)) _a11 = stalkIdeal (cmI I _a12) _a11 := by
    let _a9 := _a12
    let _c0 := pGerm X U x hx
    let _c1 := maxContactIdeal k p I m
    let _c2 := stalkIdeal I x
    classical
    obtain ⟨hcoordEach, hscalar, hcong21⟩ := chartPullbackStalkMap_compat k p c1_ c2_ x hx hagree
    let _a0 := chartPullbackFstStalkMap c1_ c2_ x hx hagree
    let _a1 := chartPullbackSndStalkMap c1_ c2_ x hx hagree
    let _a2 := _a11
    let _a6 := stkX _a13 _a2
    have hcong12 : ∀ a : ↥(stkX X x),
        _a0.hom a - _a1.hom a
          ∈ maximalIdeal
              ↥_a6 := by
      intro a
      have hneg := neg_mem _ $ hcong21 a
      rwa [neg_sub] at hneg
    have hfb :=
      chartPullbackFst_base_chartPullbackPoint c1_ c2_ x hx hagree
    have hsb :=
      chartPullbackSnd_base_chartPullbackPoint c1_ c2_ x hx hagree
    let instRk := stalkAlgebra k p x
    have instBnoeth : IsNoetherianRing
        ↥_a6 := inferInstance
    let _a7 := chartPullbackFst c1_ c2_
    let instAlgebraRat :=
      toAlgebra
        ((stalkAlgebraMap k (_a7 ≫ p) _a2).comp
          (algebraMap ℚ k))
    let _a8 := stalkIdeal _c1 x
    have hMJ : _a8 * derivIdeal k _c2
        ≤ stalkIdeal I x := by
      have h0 := stalkIdeal_mono hinv x
      rwa [stalkIdeal_mul, stalkIdeal_derivIdealSheaf k p I x] at h0
    let _a3 := _c0.hom $ c1_.coord j
    have hM1_ :=
      germ_mem_stalkIdeal _c1 x ⟨U, hU⟩ hx hmem1_
    let _a4 := _c0.hom $ c2_.coord j
    have hM2_ :=
      germ_mem_stalkIdeal _c1 x ⟨U, hU⟩ hx hmem2_
    have hcoordNe : ∀ i, i ≠ j →
        _c0.hom (c1_.coord i) = _c0.hom (c2_.coord i) :=
      fun i hi => congrArg _ $ hcoord i hi
    have h12 : m6 _a0.hom _c2
        ≤ m6 _a1.hom _c2 := by
      have hne : ∀ i, i ≠ j →
          _a1.hom (_c0.hom (c1_.coord i))
            = _a0.hom
                (_c0.hom (c1_.coord i)) := by
        intro i hi
        rw [hcoordNe i hi, ← hcoordEach i, hcoordNe i hi]
      have hj' : _a1.hom
            _a3
          + _a1.hom
              (_a4
                - _a3)
          = _a0.hom
              _a3 := by
        rw [map_sub, hcoordEach j]
        ring
      exact (map_le_map_and_sub_mem_of_etaleChart_coord_shift k p hU c1_ j x hx (fun _ => rfl)
        _a1.hom _a0.hom
        (_a4 - _a3)
        hcong21 (eqToHom_comp_stalkMap_mem_maximalIdeal _a9 _a2 x hsb (sub_mem _ hg2_ hg1_)) (fun a => (hscalar a).symm) hne hj').1
        _a8 _c2
        (sub_mem _ hM2_ hM1_) hMJ
    have h21 : m6 _a1.hom _c2
        ≤ m6 _a0.hom _c2 := by
      have hne : ∀ i, i ≠ j →
          _a0.hom (_c0.hom (c2_.coord i))
            = _a1.hom
                (_c0.hom (c2_.coord i)) := by
        intro i hi
        rw [← hcoordNe i hi, hcoordEach i, hcoordNe i hi]
      have hj' : _a0.hom
            _a4
          + _a0.hom
              (_a3
                - _a4)
          = _a1.hom
              _a4 := by
        rw [map_sub, ← hcoordEach j]
        ring
      exact (map_le_map_and_sub_mem_of_etaleChart_coord_shift k p hU c2_ j x hx (fun _ => rfl)
        _a0.hom _a1.hom
        (_a3 - _a4)
        hcong12 (eqToHom_comp_stalkMap_mem_maximalIdeal _a7 _a2 x hfb (sub_mem _ hg1_ hg2_)) hscalar hne hj').1
        _a8 _c2
        (sub_mem _ hM1_ hM2_) hMJ
    rw [stalkIdeal_comap, stalkIdeal_comap,
      map_stalkMap_stalkIdeal_eq _a7 I _a2 x hfb,
      map_stalkMap_stalkIdeal_eq _a9 I _a2 x hsb]
    exact le_antisymm h12 h21
  let _a0 := _a11
  let _a1 := cmI I _a3
  let _a2 := cmI I $ _a12
  obtain ⟨W1, hW1mem, hW1_⟩ :=
    exists_opens_stalkIdeal_eq _a1 _a2
      _a0 hst
  have hsupp' : _a0 ∈
      _c0.support := by
    have hz : _a3.base _a0 ∈
        (maxContactIdeal k p I m).support := by
      rwa [chartPullbackFst_base_chartPullbackPoint c1_ c2_ x hx hagree]
    rwa [m19]
  have hrange : _a0 ∈
      range (_c0.subschemeι.base) := by simp_all
  obtain ⟨z, hz⟩ := hrange
  let _a10 := cmI (maxContactIdeal k p I m) (chartPullbackFst c1_ c2_)
  have hmor : (subS _a10).fromSpecStalk z ≫ siI _a10 ≫ chartPullbackFst c1_ c2_ = (subS _a10).fromSpecStalk z ≫ siI _a10 ≫ _a12 := by
    let _a0 := chartPullbackFst_base_chartPullbackPoint c1_ c2_ x hx hagree
    let _a1 := maxContactIdeal k p I m
    let _a2 := _a13
    let _c0 := _a11
    let _c1 := chartPullbackFst c1_ c2_
    classical
    obtain ⟨V0, hwV0, hV0⟩ :=
      exists_isAffineOpen_mem _c0
    have hwpre := by
      show _c1.base _c0 ∈ U
      rwa [_a0]
    obtain ⟨t, htle, hwt⟩ := hV0.exists_basicOpen_le
      (V := (V0 ⊓ (_c1.pre U) : Opn _a2))
      ⟨_a11, ⟨hwV0, hwpre⟩⟩ hwV0
    have hVaff := hV0.basicOpen t
    have hVle : (bOpn _a2 t) ≤ _c1.pre U :=
      fun y hy => right (htle hy)
    refine fromSpecStalk_comp_eq_of_stalkMap_eq
      (cmI _a1 _c1).si
      _c1 _a12 z _c0 hz x
      _a0 (chartPullbackSnd_base_chartPullbackPoint c1_ c2_ x hx hagree)
      (chartPullbackFstStalkMap c1_ c2_ x hx hagree) (chartPullbackSndStalkMap c1_ c2_ x hx hagree)
      (chartPullbackFstStalkMap_eq c1_ c2_ x hx hagree) (chartPullbackSndStalkMap_eq c1_ c2_ x hx hagree) _ rfl ?_
    exact chartPullbackFstStalkMap_eq_snd_of_coord_eq_zero k p hU c1_ c2_ j hcoord x hx hg1_ hg2_ hagree _ _ (stalkMap_germ_eq_zero_of_mem_ideal _c1 _a1 z _c0 hz x _a0 U hU hx (bOpn _a2 t) hVaff hwt hVle (c1_.coord j) hmem1_) (stalkMap_germ_eq_zero_of_mem_ideal _c1 _a1 z _c0 hz x _a0 U hU hx (bOpn _a2 t) hVaff hwt hVle (c2_.coord j) hmem2_)
  obtain ⟨W', hzW', hW'⟩ :=
    AlgebraicGeometry.spread_out_unique_of_isGermInjective'
      (siI _c0 ≫ _a3)
      (siI _c0 ≫ _a12)
      hmor
  obtain ⟨V, hV⟩ :=
    _root_.FunctorialResolution.EmbeddedResolution.exists_preimage_eq_of_isClosedImmersion _c0.si W'
  have hptV : _a0 ∈ V := by
    have h1 : z ∈ _c0.si.pre V := by
      rwa [hV]
    have h2 : _c0.subschemeι.base z ∈ V := h1
    rwa [hz] at h2
  have hstalk : ∀ y : ↥_a13, y ∈ W1 ⊓ V →
      stalkIdeal _a1 y =
        stalkIdeal _a2 y := fun y hy => hW1_ y hy.1
  refine ⟨hagree, W1 ⊓ V, ⟨hW1mem, hptV⟩, hstalk,
    restrictIdeal_eq_of_stalkIdeal_eq _ _ (W1 ⊓ V) hstalk,
    io_comp_eq_of_le ?_ hW',
    chartPullback_comap_coordIdeal_eq c1_ c2_ {j},
    fun S hS => coordIdeal_eq_of_coord_eq hU c1_ c2_ S (by
      intro i hi
      refine hcoord i ?_
      rintro rfl
      exact hS hi)⟩
  rw [← hV]
  intro w hw
  exact right hw
end


theorem comap_comp_eq_of_comap_comap_eq {A B C : Sch} (ι : A ⟶ B) (F G : B ⟶ C)
    (I J : ISD C) (h : (I.comap F).comap ι = (J.comap G).comap ι) :
    I.comap (ι ≫ F) = J.comap (ι ≫ G) :=by simp_all
theorem comap_comp_io_eq_comap_restrictIdeal {Y Z : Sch} (J : ISD Y)
    (U : Opn Y) (g : Z ⟶ toScheme U) : J.comap (g ≫ ι U) = (restrictIdeal J U).comap g := by
  simp [comap_comp]

theorem exists_subscheme_comap_lift {A B : Sch} (f : A ⟶ B) (I : ISD B) :
    ∃ th_ : subscheme (I.comap f) ⟶ subscheme I,
      th_ ≫ subschemeι I = subschemeι (I.comap f) ≫ f := by
  have h2 : ker I.si ≤
      ker (siI (cmI I f) ≫ f) := by
    rw [ker_comp, q2,
      q2]
    exact le_map_comap I f
  exact ⟨m64 I.si _ h2,
    m154 I.si _ h2⟩

theorem range_base_subset_range_preimage_io {T W Z S : Sch} (tio : T ⟶ W) (ioZ : W ⟶ Z)
    (th_ : T ⟶ S) (σ : S ⟶ Z) (hth : th_ ≫ σ = tio ≫ ioZ) (Wop : Opn Z)
    (hsub : range ⇑ioZ.base ⊆ (Wop : Set ↥Z)) :
    range ⇑th_.base ⊆ range ⇑(ι $ σ ⁻¹ᵁ Wop).base := by
  rw [q1]
  rintro z ⟨y, rfl⟩
  show bsM σ (bsM th_ y) ∈ Wop
  have hb : bsM (th_ ≫ σ) y = bsM (tio ≫ ioZ) y := by rw [hth]
  have hb2 : bsM σ (bsM th_ y) = bsM ioZ (bsM tio y) := hb
  rw [hb2]
  exact hsub ⟨bsM tio y, rfl⟩

theorem comp_eq_of_lift_comp_eq {T W Z S S' Q : Sch}
    (tio : T ⟶ W) (ioZ : W ⟶ Z) (σ : S ⟶ Z) (j : S' ⟶ S) (th_ : T ⟶ S) (δ : T ⟶ S')
    (F G : Z ⟶ Q) (hth : th_ ≫ σ = tio ≫ ioZ) (hde_ : δ ≫ j = th_)
    (heq : j ≫ σ ≫ F = j ≫ σ ≫ G) :
    tio ≫ ioZ ≫ F = tio ≫ ioZ ≫ G := by
  have h1 : tio ≫ ioZ ≫ F = δ ≫ j ≫ σ ≫ F := by
    rw [← assoc tio ioZ F, ← hth, ← hde_]
    simp [assoc]
  have h2 : tio ≫ ioZ ≫ G = δ ≫ j ≫ σ ≫ G := by
    rw [← assoc tio ioZ G, ← hth, ← hde_]
    simp [assoc]
  rw [h1, h2, heq]

section
variable (k : Type) [Field k] [CharZero k] {P : Sch} (p) [Smooth p] [LocallyOfFiniteType p]
theorem nonempty_etaleMaxContactComparison
    (A : ISD P) {mu_ : ℕ} (hmu_ : 1 ≤ mu_) (hinv : IsMaxContactInvariant k p A mu_)
    (N : Bdy P) (H1_ H2_ : ISD P)
    (hsnc1_ : InStrictNormalCrossingPosition p (H1_ :: N)) (hsnc2_ : InStrictNormalCrossingPosition p (H2_ :: N))
    (hadm1_ : IsMaxContactHypersurface k p A mu_ H1_)
    (hadm2_ : IsMaxContactHypersurface k p A mu_ H2_)
    (pt : P) (hpt : pt ∈ orderAtLeastLocus A mu_) :
    Nonempty (EtaleMaxContactComparison k p A mu_ N H1_ H2_ pt) := by
  obtain ⟨V, hVaff, hptV, n, c1_, c2_, ga_, j0_, hH1, hH2_, hmc1, hmc2, hgm1, hgm2, hco, hNga,
      _, hgane⟩ :=
    exists_common_charts_of_isMaxContactHypersurface A hmu_ N H1_ H2_ hsnc1_ hsnc2_ hadm1_ hadm2_ pt hpt
  have hlftF : LocallyOfFiniteType (chartPullbackFst c1_ c2_ ≫ p) := inferInstance
  have hln1 :=
    LocallyOfFiniteType.isLocallyNoetherian (f := chartPullbackFst c1_ c2_ ≫ p)
  have hln2 : IsLocallyNoetherian
      (cmI (maxContactIdeal k p A mu_) (chartPullbackFst c1_ c2_)).subscheme := by
    have : LocallyOfFiniteType
        (siI (cmI (maxContactIdeal k p A mu_) (chartPullbackFst c1_ c2_)) ≫
          (chartPullbackFst c1_ c2_ ≫ p)) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian
      (f := siI (cmI (maxContactIdeal k p A mu_) (chartPullbackFst c1_ c2_)) ≫
        (chartPullbackFst c1_ c2_ ≫ p))
  obtain ⟨hagree, Wop, hptW, hstalk, _, heqmor, hHcomap, hcoordS⟩ :=
    exists_opens_chartPullback_eq_of_mem_maxContactIdeal k p A hmu_ hinv hVaff c1_ c2_ j0_
      (fun i hi => sy_ (hco i hi)) pt hptV
      (mp_ (isMaxContactCoord_iff_coord_mem k p A mu_ hVaff c1_ j0_) hmc1)
      (mp_ (isMaxContactCoord_iff_coord_mem k p A mu_ hVaff c2_ j0_) hmc2)
      hgm1 hgm2 (mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k p A hmu_ hpt)
  obtain ⟨U0, hU0⟩ : ∃ U0 : affO (chartPullback c1_ c2_),
      chartPullbackPoint c1_ c2_ pt hptV hagree ∈ U0.1 := by
    have hx : chartPullbackPoint c1_ c2_ pt hptV hagree ∈
        (⨆ U : affO (chartPullback c1_ c2_), (U : Opn (chartPullback c1_ c2_))) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top (chartPullback c1_ c2_)]
      trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U, hU⟩
  obtain ⟨g, hgle, hw0W'⟩ :=
    U0.2.exists_basicOpen_le (⟨chartPullbackPoint c1_ c2_ pt hptV hagree, hptW⟩ : Wop) hU0
  have hW'aff :=
    ((chartPullback c1_ c2_).affineBasicOpen g).2
  have hetale1 : Etale
      (opI (bOpn (chartPullback c1_ c2_) g) ≫ chartPullbackFst c1_ c2_) := inferInstance
  have hetale2 : Etale
      (opI (bOpn (chartPullback c1_ c2_) g) ≫ chartPullbackSnd c1_ c2_) := inferInstance
  have hsmooth1 : Smooth
      (opI (bOpn (chartPullback c1_ c2_) g) ≫ chartPullbackFst c1_ c2_) := inferInstance
  have hlft1 : LocallyOfFiniteType
      ((opI (bOpn (chartPullback c1_ c2_) g) ≫ chartPullbackFst c1_ c2_) ≫ p) := inferInstance
  have e1 :=
    (comap_comp_io_eq_comap_restrictIdeal H1_ V (fst c1_.map c2_.map)).trans
      (congrArg (fun K : V.toScheme.IdealSheafData =>
        cmI K (fst c1_.map c2_.map)) hH1)
  have e2 :=
    (comap_comp_io_eq_comap_restrictIdeal H2_ V (snd c1_.map c2_.map)).trans
      (congrArg (fun K : V.toScheme.IdealSheafData =>
        cmI K (snd c1_.map c2_.map)) hH2_)
  have e3 :=
    e1.trans (tr_ hHcomap e2.symm)
  refine ⟨{ W := oSch (bOpn (chartPullback c1_ c2_) g)
          , f1_ := opI (bOpn (chartPullback c1_ c2_) g) ≫ chartPullbackFst c1_ c2_
          , f2_ := opI (bOpn (chartPullback c1_ c2_) g) ≫ chartPullbackSnd c1_ c2_
          , w := ⟨chartPullbackPoint c1_ c2_ pt hptV hagree, hw0W'⟩
          , isAffine := hW'aff
          , etale_f₁ := hetale1
          , etale_f₂ := hetale2
          , lft_f₁ := hlft1
          , base_f1 := chartPullbackFst_base_chartPullbackPoint c1_ c2_ pt hptV hagree
          , base_f2 := chartPullbackSnd_base_chartPullbackPoint c1_ c2_ pt hptV hagree
          , comap_A := ?_
          , comap_H := ?_
          , comap_N := ?_
          , comp_p := ?_
          , maxContact_comp := ?_ }⟩
  refine comap_comp_eq_of_comap_comap_eq (bOpn (chartPullback c1_ c2_) g).ι (chartPullbackFst c1_ c2_)
    (chartPullbackSnd c1_ c2_) A A ?_
  exact restrictIdeal_eq_of_stalkIdeal_eq _ _ (bOpn (chartPullback c1_ c2_) g)
    (fun y hy => hstalk y (hgle hy))
  refine comap_comp_eq_of_comap_comap_eq (bOpn (chartPullback c1_ c2_) g).ι (chartPullbackFst c1_ c2_)
    (chartPullbackSnd c1_ c2_) H1_ H2_ ?_
  exact congrArg (fun J : ISD (chartPullback c1_ c2_) =>
    J.comap (bOpn (chartPullback c1_ c2_) g).ι) e3
  intro J hJ
  obtain ⟨i, hi, rfl⟩ := mp_ mem_iff_getElem hJ
  have key : (N[i]'hi).comap (chartPullbackFst c1_ c2_) = (N[i]'hi).comap (chartPullbackSnd c1_ c2_) := by
    obtain ⟨hnone, hsome⟩ := hNga i hi
    rw [comap_comp_io_eq_comap_restrictIdeal _ V _, comap_comp_io_eq_comap_restrictIdeal _ V _]
    cases hga_ : ga_ i with
    | none =>
      rw [hnone hga_, comap_top, comap_top]
    | some jj =>
      have hjj : jj ≠ j0_ := by
        intro h
        exact hgane i (by rw [hga_, h])
      have hnotmem : j0_ ∉ ({jj} : FinSet n) := by
        simp only [mem_singleton]
        exact fun h => hjj h.symm
      rw [hsome jj hga_, chartPullback_comap_coordIdeal_eq c1_ c2_ {jj}, hcoordS {jj} hnotmem]
  refine comap_comp_eq_of_comap_comap_eq (bOpn (chartPullback c1_ c2_) g).ι (chartPullbackFst c1_ c2_)
    (chartPullbackSnd c1_ c2_) (N[i]'hi) (N[i]'hi) ?_
  exact congrArg (fun J : ISD (chartPullback c1_ c2_) =>
    J.comap (bOpn (chartPullback c1_ c2_) g).ι) key
  have hcs := chartPullbackFst_comp_eq_chartPullbackSnd_comp c1_ c2_
  simp only [assoc] at hcs ⊢
  rw [hcs]
  have hNeq : maxContactIdeal k
        ((opI (bOpn (chartPullback c1_ c2_) g) ≫ chartPullbackFst c1_ c2_) ≫ p)
        (cmI A (opI (bOpn (chartPullback c1_ c2_) g) ≫ chartPullbackFst c1_ c2_)) mu_
      = cmI (cmI (maxContactIdeal k p A mu_) (chartPullbackFst c1_ c2_))
          (bOpn (chartPullback c1_ c2_) g).ι := by
    simp only [maxContactIdeal_eq_derivIdealSheafIterate]
    rw [derivIdealSheafIterate_comap k p
      (opI (bOpn (chartPullback c1_ c2_) g) ≫ chartPullbackFst c1_ c2_) (mu_ - 1) A]
    simp [comap_comp]
  rw [hNeq]
  obtain ⟨th_, hth⟩ :=
    exists_subscheme_comap_lift (bOpn (chartPullback c1_ c2_) g).ι
      (cmI (maxContactIdeal k p A mu_) (chartPullbackFst c1_ c2_))
  have hsub : range ⇑(opI (bOpn (chartPullback c1_ c2_) g)).base ⊆
      (Wop : Set ↥(chartPullback c1_ c2_)) := by simp_all
  have hrange := range_base_subset_range_preimage_io
    (siI (cmI (cmI (maxContactIdeal k p A mu_) (chartPullbackFst c1_ c2_))
      (bOpn (chartPullback c1_ c2_) g).ι))
    (bOpn (chartPullback c1_ c2_) g).ι th_
    (siI (cmI (maxContactIdeal k p A mu_) (chartPullbackFst c1_ c2_))) hth Wop hsub
  exact comp_eq_of_lift_comp_eq _ _ _
    (opI ((cmI (maxContactIdeal k p A mu_) (chartPullbackFst c1_ c2_)).subschemeι.pre Wop))
    th_ (lift _ th_ hrange) (chartPullbackFst c1_ c2_) (chartPullbackSnd c1_ c2_)
    hth (lift_fac _ th_ hrange) heqmor

theorem exists_etale_equalizing_isMaxContactHypersurface [QuasiCompact p]
    (A : ISD P) {mu_ : ℕ} (hmu_ : 1 ≤ mu_) (hinv : IsMaxContactInvariant k p A mu_)
    (_horder : ∀ x : P, orderAt A x ≤ (mu_ : ENat))
    (N : Bdy P) (H1_ H2_ : ISD P)
    (hsnc1_ : InStrictNormalCrossingPosition p (H1_ :: N)) (hsnc2_ : InStrictNormalCrossingPosition p (H2_ :: N))
    (hadm1_ : IsMaxContactHypersurface k p A mu_ H1_)
    (hadm2_ : IsMaxContactHypersurface k p A mu_ H2_) :
    ∃ (V : Sch) (g1_ : V ⟶ P) (g2_ : V ⟶ P) (_ : Etale g1_) (_ : Etale g2_)
      (_ : QuasiCompact $ g1_ ≫ p) (hlft : LocallyOfFiniteType $ g1_ ≫ p),
      g1_ ≫ p = g2_ ≫ p ∧
      orderAtLeastLocus A mu_ ⊆ range ⇑g1_.base ∧
      orderAtLeastLocus A mu_ ⊆ range ⇑g2_.base ∧
      A.comap g1_ = A.comap g2_ ∧
      H1_.comap g1_ = H2_.comap g2_ ∧
      N.map (fun J => J.comap g1_) = N.map (fun J => J.comap g2_) ∧
      subschemeι (@maxContactIdeal k _ _ V (g1_ ≫ p) hlft (A.comap g1_) mu_) ≫ g1_ =
        subschemeι (@maxContactIdeal k _ _ V (g1_ ≫ p) hlft (A.comap g1_) mu_) ≫ g2_ :=
  by
    let hloc := fun pt hpt =>
      nonempty_etaleMaxContactComparison k p A hmu_ hinv N H1_ H2_ hsnc1_ hsnc2_ hadm1_ hadm2_ pt hpt
    classical
    have hsub : Subsingleton ↥(Sp k) := inferInstance
    have hcsS : CompactSpace ↥(Sp k) := inferInstance
    have hcP : CompactSpace ↥P := by
      constructor
      have h := (‹QuasiCompact p›).isCompact_preimage univ isOpen_univ isCompact_univ
      rwa [preimage_univ] at h
    let _a1 := orderAtLeastLocus A mu_
    have c : ∀ x : ↥_a1, EtaleMaxContactComparison k p A mu_ N H1_ H2_ x.1 :=
      fun x => Classical.choice $ hloc x.1 x.2
    have hopen : ∀ x,
        IsOpen $ range ⇑(c x).f1_.base ∩ range ⇑(c x).f2_.base := by
      intro x
      have := (c x).etale_f₁
      have := (c x).etale_f₂
      exact (c x).f1_.isOpenMap.isOpen_range.inter (c x).f2_.isOpenMap.isOpen_range
    have hsub2 : orderAtLeastLocus A mu_ ⊆ ⋃ x : ↥_a1,
        (range ⇑(c x).f1_.base ∩ range ⇑(c x).f2_.base) := by
      intro y hy
      let _a0 := c ⟨y, hy⟩
      exact mpr_ mem_iUnion ⟨⟨y, hy⟩, ⟨⟨_a0.w, _a0.base_f1⟩,
        ⟨_a0.w, _a0.base_f2⟩⟩⟩
    obtain ⟨T, hT⟩ := ((isClosed_orderAtLeastLocus k p A mu_).isCompact).elim_finite_subcover
      (fun x => range ⇑(c x).f1_.base ∩ range ⇑(c x).f2_.base)
      hopen hsub2
    refine exists_etale_maxContactIdeal_comparison_of_finite_cover p A mu_ N H1_ H2_
      (fun i : {x : ↥_a1 // x ∈ T} => i.1) (fun i => c i.1) ?_
    intro y hy
    obtain ⟨x, hx⟩ := mp_ mem_iUnion $ hT hy
    obtain ⟨hxT, hmem⟩ := mp_ mem_iUnion hx
    exact mpr_ mem_iUnion ⟨⟨x, hxT⟩, hmem⟩
end


variable {X : Sch}

section
variable (I : ISD X) (m : ℕ)
def OrderLE : Prop :=
  ∀ x : X, orderAt I x ≤ (m : ENat)

theorem orderLE_iff :
    OrderLE I m ↔ ∀ x : X, orderAt I x ≤ (m : ENat) := m22
end

structure MaxOrderEq (I : ISD X) (m : ℕ) : Prop where
  orderLE : OrderLE I m
  coSupport_nonempty : (orderAtLeastLocus I m).Nonempty

section
variable (m : ℕ)
def lcmUpTo : ℕ := (List.range' 1 m).foldr Nat.lcm 1

theorem lcmUpTo_eq_foldr : lcmUpTo m = (List.range' 1 m).foldr Nat.lcm 1 := rfl

def tuningExponent : ℕ := if m ≤ 1 then 1 else (m - 1) * lcmUpTo m
end

section
variable (k : Type) [CommRing k] [IsNoetherianRing k] {X : Sch} (p) [LocallyOfFiniteType p] (I : ISD X)
noncomputable def tunedSheaf
    (m s : ℕ) : ISD X :=
  ⨆ c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j},
    ((List.range m).map fun j => derivIdealSheafIterate k p j I ^ (c.1 j)).prod

theorem tunedSheaf_eq_iSup
    (m s : ℕ) :
    tunedSheaf k p I m s =
      ⨆ c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j},
        ((List.range m).map fun j => derivIdealSheafIterate k p j I ^ (c.1 j)).prod := rfl

noncomputable def balancedTunedSheaf
    (m : ℕ) : ISD X :=
  tunedSheaf k p I m $ tuningExponent m

theorem balancedTunedSheaf_eq
    (m : ℕ) : balancedTunedSheaf k p I m = tunedSheaf k p I m (tuningExponent m) := rfl
end

theorem tuningExponent_of_le_one {m : ℕ} (h : m ≤ 1) : tuningExponent m = 1 := by
  unfold tuningExponent
  exact if_pos h

theorem tuningExponent_of_two_le {m : ℕ} (h : 2 ≤ m) : tuningExponent m = (m - 1) * lcmUpTo m := by
  unfold tuningExponent
  exact if_neg $ by omega

theorem lcmUpTo_one : lcmUpTo 1 = 1 := rfl

theorem tuningExponent_one : tuningExponent 1 = 1 := tuningExponent_of_le_one le_rfl

def DerivIdealSheafTunedSheafSucc : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [IsNoetherianRing k] (X : Sch)
    (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (I : ISD X) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, derivIdealSheaf k p (tunedSheaf k p I m $ s + 1) = tunedSheaf k p I m s

def MaxContactIdealTunedSheafEq : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [IsNoetherianRing k] (X : Sch)
    (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (I : ISD X) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s →
      derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s) =
        derivIdealSheafIterate k p (m - 1) I

def IsMaxContactInvariantTunedSheaf : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [IsNoetherianRing k] (X : Sch)
    (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (I : ISD X) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s →
      derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s) *
          derivIdealSheaf k p (tunedSheaf k p I m s) ≤ tunedSheaf k p I m s

def IsDerivBalancedTunedSheafMulLcm : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [IsNoetherianRing k] (X : Sch)
    (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (I : ISD X) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ r : ℕ, m - 1 ≤ r → ∀ i : ℕ, i < r * lcmUpTo m →
      derivIdealSheafIterate k p i (tunedSheaf k p I m $ r * lcmUpTo m) ^ (r * lcmUpTo m) ≤
        tunedSheaf k p I m (r * lcmUpTo m) ^ (r * lcmUpTo m - i)

def CoSupportTunedSheafEqAndOrderLE : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [IsNoetherianRing k] (X : Sch)
    (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (I : ISD X) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s →
      orderAtLeastLocus (tunedSheaf k p I m s) s = orderAtLeastLocus I m ∧ OrderLE (tunedSheaf k p I m s) s

theorem CoSupportTunedSheafEqAndOrderLE.orderLE (h : CoSupportTunedSheafEqAndOrderLE) (k : Type) [Field k]
    [CharZero k] [IsNoetherianRing k] (X : Sch) (p : X ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p] (I : ISD X) (m : ℕ)
    (hm : 1 ≤ m) (hmax : MaxOrderEq I m) (s : ℕ) (hs : 1 ≤ s) :
    OrderLE (tunedSheaf k p I m s) s :=
  right $ h k X p I m hm hmax s hs

def IsMarkedIffOfPowLeOfLeTunedSheaf : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [IsNoetherianRing k] (X : Sch)
    (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (I : ISD X) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s → ∀ J : ISD X, I ^ s ≤ J → J ≤ tunedSheaf k p I m (m * s) →
      ∀ (E : Bdy X) (d : BlowupSequenceData X),
        (d.IsMarked p I m E ↔ d.IsMarked p J (m * s) E) ∧
        (d.IsMarked p I m E → ∀ i : ℕ, i ≤ d.length →
          orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m)

def IsMarkedIffBalancedTunedSheaf : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [IsNoetherianRing k] (X : Sch)
    (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p]
    (I : ISD X) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ (E : Bdy X) (d : BlowupSequenceData X),
      (d.IsMarked p I m E ↔ d.IsMarked p (balancedTunedSheaf k p I m) (tuningExponent m) E) ∧
      (d.IsMarked p I m E → ∀ i : ℕ, i ≤ d.length →
        orderAtLeastLocus (d.controlledTransform (balancedTunedSheaf k p I m) (tuningExponent m) i) (tuningExponent m) =
          orderAtLeastLocus (d.controlledTransform I m i) m) ∧
      (derivIdealSheafIterate k p (tuningExponent m - 1) (balancedTunedSheaf k p I m) *
          derivIdealSheaf k p (balancedTunedSheaf k p I m) ≤ balancedTunedSheaf k p I m) ∧
      (∀ i : ℕ, i < tuningExponent m →
        derivIdealSheafIterate k p i (balancedTunedSheaf k p I m) ^ tuningExponent m ≤
          balancedTunedSheaf k p I m ^ (tuningExponent m - i))

structure TunedSheafProperties : Prop where
  isMarked_tuned_iff : IsMarkedIffBalancedTunedSheaf
  derivIdealSheafIter_pred_tunedSheaf : MaxContactIdealTunedSheafEq
  derivIdealSheafIter_mul_derivIdealSheaf_le_tunedSheaf : IsMaxContactInvariantTunedSheaf
  derivIdealSheafIter_tunedSheaf_pow_le : IsDerivBalancedTunedSheafMulLcm
  coSupport_tunedSheaf_eq_and_orderLE : CoSupportTunedSheafEqAndOrderLE

end FunctorialResolution.EmbeddedResolution
end
section

namespace FunctorialResolution.EmbeddedResolution

theorem ideal_listProd_map {X : Sch} (g : ℕ → ISD X) (l : List ℕ)
    (U : X.affineOpens) :
    ((l.map g).prod).ideal U = (l.map fun j => (g j).ideal U).prod := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, one_eq_top,
        ideal_top]
      exact Ideal.one_eq_top.symm
  | cons a t ih =>
      let _a0 := (t.map g).prod
      have hmul : ((g a) * _a0).ideal U
          = (g a).ideal U * _a0.ideal U := by simp_all
      rw [m75, prod_cons, m75, prod_cons, hmul, ih]

theorem ideal_map_prod_range {R S : Type} [CommRing R] [CommRing S] (ph_ : R →+* S)
    (g : ℕ → Ideal R) (n : ℕ) :
    Ideal.map ph_ (∏ j ∈ Finset.range n, g j) = ∏ j ∈ Finset.range n, Ideal.map ph_ (g j) :=
  map_prod (mapHom ph_) g $ m65 n

section
variable (k : Type) [CommRing k]
section
variable {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ph_ : R →+* S) (J : Ideal R)
theorem map_tuningMonomial_of_map_derivIdealIterate (m : ℕ)
    (c : ℕ → ℕ)
    (h : ∀ j : ℕ, Ideal.map ph_ (derivIdealIterate k j J) = derivIdealIterate k j (Ideal.map ph_ J)) :
    Ideal.map ph_ (tuningMonomial k J m c) = tuningMonomial k (Ideal.map ph_ J) m c := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod, ideal_map_prod_range]
  refine prod_congr rfl fun j _ => ?_
  rw [m219, h j]

theorem map_tunedIdeal_of_map_derivIdealIterate (m s : ℕ)
    (h : ∀ j : ℕ, Ideal.map ph_ (derivIdealIterate k j J) = derivIdealIterate k j (Ideal.map ph_ J)) :
    Ideal.map ph_ (tunedIdeal k J m s) = tunedIdeal k (Ideal.map ph_ J) m s := by
  let _a0 := m6 ph_ J
  refine le_antisymm ?_ ?_
  rw [map_le_iff_le_comap]
  refine mpr_ (tunedIdeal_le_iff k J m s _) ?_
  intro c hc
  rw [← map_le_iff_le_comap, map_tuningMonomial_of_map_derivIdealIterate k ph_ J m c h]
  exact tuningMonomial_le_tunedIdeal k _a0 m s c hc
  refine mpr_ (tunedIdeal_le_iff k _a0 m s _) ?_
  intro c hc
  rw [← map_tuningMonomial_of_map_derivIdealIterate k ph_ J m c h]
  exact Ideal.map_mono $ tuningMonomial_le_tunedIdeal k J m s c hc
end

theorem pow_derivIdealIterate_pred_le_tunedIdeal {S : Type}
    [CommRing S] [Algebra k S] (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    (derivIdealIterate k (m - 1) J) ^ t ≤ tunedIdeal k J m t := by
  have hmem : m - 1 ∈ m65 m := Finset.mem_range.mpr $ by omega
  have h1 : m - (m - 1) = 1 := by omega
  have hmono : tuningMonomial k J m (if · = m - 1 then t else 0)
      = (derivIdealIterate k (m - 1) J) ^ t := by
    rw [tuningMonomial_eq_prod]
    refine tr_ (prod_eq_single (m - 1) (fun b _ hb => by simp [hb])
      (absurd hmem)) ?_
    simp
  have hw : tuningWeight m (if · = m - 1 then t else 0) = t := by
    rw [tuningWeight_eq_sum]
    refine tr_ (sum_eq_single (m - 1) (fun b _ hb => by simp [hb])
      (absurd hmem)) ?_
    simp [h1]
  rw [← hmono]
  exact tuningMonomial_le_tunedIdeal k J m t _ $ le_of_eq hw.symm

section
variable [IsNoetherianRing k] {X : Sch} (p) [LocallyOfFiniteType p] (I : ISD X)
theorem ideal_prod_derivIdealSheafIterate_pow (m : ℕ) (c : ℕ → ℕ) (U : X.affineOpens) :
    (((List.range m).map fun j => derivIdealSheafIterate k p j I ^ (c j)).prod).ideal U =
      @tuningMonomial k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m c := by
  have hpow : ∀ (J : ISD X) (n : ℕ), (J ^ n).ideal U = (J.ideal U) ^ n := by simp_all
  simp [ideal_listProd_map, hpow, derivIdealSheafIterate_ideal]
  exact listProd_map_range_eq_prod _ m

section
variable (m s : ℕ)
noncomputable def tunedIdealSheafOfSections :
    IdealSheafData X where
  ideal U := @tunedIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m s
  map_ideal_basicOpen := by
    intro U f
    let algU := sectionsAlgebra k p U.1
    let algV := sectionsAlgebra k p $ basicOpen X f
    have hI := I.map_ideal_basicOpen U f
    let _a0 := X.presheaf.map (homOfLE $ X.basicOpen_le f).op
    have hd : ∀ j : ℕ,
        Ideal.map _a0.hom
            (@derivIdealIterate k _ Γ(X, U.1) _ algU j $ I.ideal U) =
          @derivIdealIterate k _ Γ(X, basicOpen X f) _ algV j
            (Ideal.map _a0.hom $ I.ideal U) := by
      intro j
      have h1 := (derivIdealSheafIterate k p j I).map_ideal_basicOpen U f
      rw [derivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal] at h1
      exact h1.trans $ congrArg (@derivIdealIterate k _ Γ(X, basicOpen X f) _ algV j) hI.symm
    have h2 := @map_tunedIdeal_of_map_derivIdealIterate k _ Γ(X, U.1) Γ(X, basicOpen X f) _ _ algU algV
      _a0.hom (I.ideal U) m s hd
    exact h2.trans $ congrArg (fun J : Ideal Γ(X, basicOpen X f) =>
      @tunedIdeal k _ Γ(X, basicOpen X f) _ algV J m s) hI

@[simp] theorem tunedSheaf_ideal (U : X.affineOpens) :
    (tunedSheaf k p I m s).ideal U =
      @tunedIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m s := by
  let _a1 := m127 m
  let _a0 := tunedIdealSheafOfSections k p I m s
  refine le_antisymm ?_ ?_
  · have hle : tunedSheaf k p I m s ≤ _a0 := by
      rw [tunedSheaf_eq_iSup]
      refine iSup_le fun c => ?_
      intro V
      rw [ideal_prod_derivIdealSheafIterate_pow k p I m c.1 V]
      exact @tuningMonomial_le_tunedIdeal k _ Γ(X, V.1) _ (sectionsAlgebra k p V.1)
        (I.ideal V) m s c.1 c.2
    exact hle U
  · refine (@tunedIdeal_le_iff k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) m s _).mpr ?_
    intro c hc
    rw [← ideal_prod_derivIdealSheafIterate_pow k p I m c U]
    have hmono : (_a1.map fun j => derivIdealSheafIterate k p j I ^ (c j)).prod ≤
        tunedSheaf k p I m s := by
      rw [tunedSheaf_eq_iSup]
      exact le_iSup (fun d : {d : ℕ → ℕ // s ≤ ∑ j ∈ m65 m, (m - j) * d j} =>
        (_a1.map fun j => derivIdealSheafIterate k p j I ^ (d.1 j)).prod) ⟨c, hc⟩
    exact hmono U
end

section
variable (m) (hm : 1 ≤ m)
include hm
theorem derivIdealSheafIterate_pow_le_tunedSheaf (t : ℕ) :
    (derivIdealSheafIterate k p (m - 1) I) ^ t ≤ tunedSheaf k p I m t := by
  let _c0 := derivIdealSheafIterate k p (m - 1) I
  let _a0 := _c0 ^ t
  intro U
  have hpow : _a0.ideal U
      = (_c0.ideal U) ^ t :=
    congrFun (show _a0.ideal
        = _c0.ideal ^ t by
      rw [ideal_pow]) U
  rw [hpow, derivIdealSheafIterate_ideal, tunedSheaf_ideal]
  exact @pow_derivIdealIterate_pred_le_tunedIdeal k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
    (I.ideal U) m hm t

theorem tunedSheaf_one_eq_derivIdealSheafIterate :
    tunedSheaf k p I m 1 = derivIdealSheafIterate k p (m - 1) I := by
  refine le_antisymm ?_ ?_
  have h : ∀ U : affO X,
      (tunedSheaf k p I m 1).ideal U ≤ (derivIdealSheafIterate k p (m - 1) I).ideal U := by
    intro U
    rw [tunedSheaf_ideal, derivIdealSheafIterate_ideal]
    exact @tunedIdeal_one_le_derivIdealIterate k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) (I.ideal U) m hm
  exact h
  have h := derivIdealSheafIterate_pow_le_tunedSheaf k p I m hm 1
  rwa [pow_one] at h
end
end
end

theorem derivIdealSheaf_tunedSheaf_succ : DerivIdealSheafTunedSheafSucc := by
  intro k _ _ _ X p _ _ I m hm hmax s
  refine le_antisymm ?_ ?_
  have h : ∀ U,
      (derivIdealSheaf k p $ tunedSheaf k p I m $ s + 1).ideal U ≤
        (tunedSheaf k p I m s).ideal U := by
    intro U
    rw [derivIdealSheaf_ideal, tunedSheaf_ideal, tunedSheaf_ideal]
    exact @derivIdeal_tunedIdeal_succ_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) m s
  exact h
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  have hord := hmax.orderLE x
  rcases eq_or_lt_of_le hord with heq | hlt
  obtain ⟨U, hU, hxU, n, c, j, hmc, -⟩ := exists_isMaxContactCoord k p I hm x heq
  have hcoord :=
    mp (isMaxContactCoord_iff_coord_mem k p I m hU c j) hmc
  rw [maxContactIdeal_ideal] at hcoord
  let _a0 := I.ideal ⟨U, hU⟩
  let _a1 := sectionsAlgebra k p U
  have hle : @tunedIdeal k _ U.sec _ _a1 _a0 m s ≤
      @derivIdeal k _ U.sec _ _a1
        (@tunedIdeal k _ U.sec _ _a1
          _a0 m $ s + 1) := by
    let algU := _a1
    let _s0 := UFin n
    let algP := c.algebra
    let _a2 := MvPolynomial _s0 k
    have := c.isScalarTower
    have :=
      c.algebra_formallyEtale hU
    let algQ :=
      toAlgebra $ (algebraMap k U.sec).comp $ algebraMap ℚ k
    have hde_ : partialDeriv k _s0 U.sec (up j)
        (c.coord j) = 1 := by
      rw [← EtaleChart.etaleCoordinates_coord c j]
      exact partialDeriv_coord_self k _s0 U.sec
        (up j)
    exact tunedIdeal_le_derivIdeal_tunedIdeal_succ k _a0 m hm hcoord
      (partialDeriv k _s0 U.sec $ up j) hde_ s
  rw [stalkIdeal_eq_map_germ (tunedSheaf k p I m s) x ⟨U, hU⟩ hxU,
    stalkIdeal_eq_map_germ (derivIdealSheaf k p $ tunedSheaf k p I m $ s + 1) x ⟨U, hU⟩ hxU]
  refine Ideal.map_mono ?_
  simp [tunedSheaf_ideal, derivIdealSheaf_ideal]
  exact hle
  have hxns : x ∉ spI (derivIdealSheafIterate k p (m - 1) I) := by
    intro hc
    refine absurd (mp_ (mem_orderAtLeastLocus_iff I m x) ?_) $ mpr_ not_le hlt
    rwa [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm]
  have h1 : stalkIdeal ((derivIdealSheafIterate k p (m - 1) I) ^ (s + 1)) x = ⊤ := by
    rw [stalkIdeal_pow, mp not_not fun hne2 => hxns $ mpr_ (mem_support_iff_stalkIdeal_ne_top _ x) hne2, ← m217, one_pow]
  refine le_trans le_top ?_
  rw [← h1]
  exact le_trans
    (stalkIdeal_mono (derivIdealSheafIterate_pow_le_tunedSheaf k p I m hm $ s + 1) x) $ stalkIdeal_mono (le_derivIdealSheaf k p $ tunedSheaf k p I m $ s + 1) x

theorem maxContactIdealTunedSheafEq : MaxContactIdealTunedSheafEq := by
  intro k _ _ _ X p _ _ I m hm hmax s hs
  have step : ∀ j t, j ≤ t →
      derivIdealSheafIterate k p j (tunedSheaf k p I m t) = tunedSheaf k p I m (t - j) := by
    intro j
    induction j with
    | zero =>
        intro t _
        rw [derivIdealSheafIterate_zero, m130]
    | succ n ih =>
        intro t ht
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        have hn : n ≤ t' := by omega
        have he : t' + 1 - (n + 1) = t' - n := by omega
        rw [he, derivIdealSheafIterate_add k p n 1 $ tunedSheaf k p I m $ t' + 1,
          derivIdealSheafIterate_one, (derivIdealSheaf_tunedSheaf_succ k X p I m hm hmax) t', ih t' hn]
  have he2 : s - (s - 1) = 1 := by omega
  rw [step (s - 1) s $ by omega, he2, tunedSheaf_one_eq_derivIdealSheafIterate k p I m hm]

theorem isMaxContactInvariantTunedSheaf :
    IsMaxContactInvariantTunedSheaf := by
  intro k _ _ _ X p _ _ I m _ _ s hs
  let _a0 := tunedSheaf k p I m s
  let _a1 := derivIdealSheafIterate k p (s - 1) _a0
  let _a2 := derivIdealSheaf k p _a0
  intro U
  have hmul : (_a1 *
        _a2).ideal U =
      _a1.ideal U *
        _a2.ideal U := by
    simp [ideal_mul, mul_apply]
  rw [hmul, derivIdealSheafIterate_ideal, derivIdealSheaf_ideal, tunedSheaf_ideal]
  exact @derivIdealIterate_mul_derivIdeal_tunedIdeal_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1) (I.ideal U) m s hs


theorem dvd_foldr_lcm : ∀ (l : List ℕ) (w : ℕ), w ∈ l → w ∣ l.foldr Nat.lcm 1
  | [], w, h => absurd h (by simp)
  | (a :: l), w, h => by
      show w ∣ Nat.lcm a (l.foldr Nat.lcm 1)
      rcases List.mem_cons.mp h with h | h
      · subst h
        exact Nat.dvd_lcm_left _ _
      · exact dvd_trans (dvd_foldr_lcm l w h) (Nat.dvd_lcm_right _ _)

theorem dvd_lcmUpTo (m w : ℕ) (hw : 1 ≤ w) (hwm : w ≤ m) : w ∣ lcmUpTo m :=
  dvd_foldr_lcm _ w $ mpr_ mem_range'_1 ⟨hw, by omega⟩

theorem foldr_lcm_consecutive_pos :
    ∀ n s, 0 < s → 0 < (List.range' s n).foldr Nat.lcm 1
  | 0, s, _ => Nat.one_pos
  | (n + 1), s, hs => by
      have h := foldr_lcm_consecutive_pos n (s + 1) $ by omega
      exact Nat.pos_of_ne_zero $ Nat.lcm_ne_zero (by omega) $ by omega

theorem lcmUpTo_pos (m : ℕ) : 0 < lcmUpTo m :=
  foldr_lcm_consecutive_pos m 1 m176

theorem le_of_not_natCast_succ_le {a : ENat} {s : ℕ}
    (h : ¬ (((s + 1 : ℕ)) : ENat) ≤ a) : a ≤ (s : ENat) := by
  rcases eq_or_ne a ⊤ with rfl | hne
  exact absurd le_top h
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hne
  have hn : ¬ (s + 1 ≤ n) := fun hh => h $ by exact_mod_cast hh
  have hns : n ≤ s := by omega
  exact_mod_cast hns

theorem isDerivBalanced_tunedSheaf_mul_lcmUpTo : IsDerivBalancedTunedSheafMulLcm := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax r hr i hi
  refine Scheme.IdealSheafData.le_def.mpr ?_
  intro U
  rw [ideal_pow, ideal_pow, pow_apply,
    pow_apply, derivIdealSheafIterate_ideal, tunedSheaf_ideal]
  exact @derivIdealIterate_tunedIdeal_pow_le k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) m
    (lcmUpTo m) (lcmUpTo_pos m) (fun w hw1 hw2 => dvd_lcmUpTo m w hw1 hw2) r hr i hi

theorem orderAtLeastLocus_tunedSheaf_eq_and_order_le : CoSupportTunedSheafEqAndOrderLE := by
  intro k hk hchar hnoeth X p hsmooth hft I m hm hmax s hs
  have hC := maxContactIdealTunedSheafEq k X p I m hm hmax s hs
  constructor
  have hA := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p (tunedSheaf k p I m s) hs
  have hB := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
  rwa [← hA, hC]
  intro x
  let _a1 := orderAtLeastLocus I $ m + 1
  have hx2 : x ∉ _a1 := by
    rw [mem_orderAtLeastLocus_iff]
    intro hcon
    have hmm : m + 1 ≤ m := by exact_mod_cast (le_trans hcon $ hmax.orderLE x)
    omega
  let _a0 := derivIdealSheafIterate k p (m - 1) I
  have hcs : orderAtLeastLocus _a0 ((m + 1) - (m - 1))
      = _a1 := orderAtLeastLocus_derivIdealSheafIterate k p I $ by omega
  have ha : ¬ (((2 : ℕ) : ENat) ≤ orderAt _a0 x) := by
    rw [← mem_orderAtLeastLocus_iff]
    have h2 : (2 : ℕ) = (m + 1) - (m - 1) := by omega
    rwa [h2, hcs]
  refine le_of_not_natCast_succ_le ?_
  intro hcon
  have he : 2 + (s - 1) = s + 1 := by omega
  have h1 := hcon
  rw [← he] at h1
  have h2 := le_orderAt_derivIdealSheafIterate k p (tunedSheaf k p I m s) x 2 (s - 1) h1
  rw [hC] at h2
  exact ha h2

end FunctorialResolution.EmbeddedResolution
end
section
universe v w


namespace FunctorialResolution.EmbeddedResolution


end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits

open scoped Classical


namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactReduction

def emptyMarkedSeq (T : MarkedIdealWithBoundary) : T.SequenceOfBlowups :=
  toMarkedSequenceOfBlowups $ T.embs

def IsMaxContactCoord (k : Type) [Field k] {X : Sch}
    (p : X ⟶ Sp k) [LocallyOfFiniteType p]
    (I : ISD X) (m : ℕ) {U : Opn X} {n : ℕ}
    (c : EtaleChart p U n) (j : Fin n) : Prop :=
  c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U

structure FiniteOpenCoverWithIdeals (T : MarkedIdealWithBoundary) : Type 1 where
  idx : Type
  finiteIdx : Finite idx
  opens : idx → T.scheme.Opens
  localIdeal : (i : idx) → (opens i).toScheme.IdealSheafData

instance instFiniteCoverIdx {T : MarkedIdealWithBoundary} (D : FiniteOpenCoverWithIdeals T) : Finite D.idx :=
  D.finiteIdx

structure IsMaxContactCover (T : MarkedIdealWithBoundary) (D : FiniteOpenCoverWithIdeals T)
    (hft : LocallyOfFiniteType T.structMap) (W : T.scheme.IdealSheafData) (mu_ : ℕ) : Prop where
  covers : iSup D.opens = ⊤
  isAffine : ∀ i : D.idx, IsAffineOpen $ D.opens i
  dichotomy : ∀ i : D.idx,
    (Disjoint (orderAtLeastLocus W mu_) ((D.opens i : T.scheme.Opens) : CSet T.scheme) ∧
      D.localIdeal i = ⊤) ∨
    (∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n) (j : Fin n),
      D.localIdeal i = c.coordIdeal {j} ∧
        @IsMaxContactCoord T.base _ T.scheme T.structMap hft W mu_ (D.opens i) n c j)

def trivialCover (T : MarkedIdealWithBoundary) : FiniteOpenCoverWithIdeals T where
  idx := PUnit.{1}
  finiteIdx := inferInstance
  opens := fun _ => ⊤
  localIdeal := fun _ => ⊤

def maxContactCover (T : MarkedIdealWithBoundary) (hft : LocallyOfFiniteType T.structMap)
    (W : T.scheme.IdealSheafData) (mu_ : ℕ) : FiniteOpenCoverWithIdeals T :=
  if h : ∃ D : FiniteOpenCoverWithIdeals T, IsMaxContactCover T D hft W mu_ then h.choose else trivialCover T

section
variable {T : MarkedIdealWithBoundary} (D : FiniteOpenCoverWithIdeals T)
def FiniteOpenCoverWithIdeals.disjointUnion : Sch :=
  sigmaOpens T.scheme D.opens

def FiniteOpenCoverWithIdeals.disjointUnionMap : D.disjointUnion ⟶ scheme T :=
  sigmaOpensDesc T.scheme D.opens

def FiniteOpenCoverWithIdeals.i (i : D.idx) :
    toScheme (D.opens i) ⟶ D.disjointUnion :=
  Sigma.ι (fun i => toScheme $ D.opens i) i

def FiniteOpenCoverWithIdeals.iInfImageIdeal : D.disjointUnion.IdealSheafData :=
  ⨅ i : D.idx, imageIdealSheaf (D.i i) (D.localIdeal i)

def FiniteOpenCoverWithIdeals.markedTriple (W : tISD T)
    (mu_ : ℕ) : MarkedIdealWithBoundary where
  base := T.base
  instField := T.instField
  scheme := D.disjointUnion
  structMap := D.disjointUnionMap ≫ structMap T
  ideal := W.comap D.disjointUnionMap
  mult := mu_
  boundary := T.boundary.map fun Dv => Dv.comap D.disjointUnionMap
end

section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

def iteratedStrictTransform (s : MarkedBlowupSequenceData p I m E) (H : ISD X) :
    (i : ℕ) → IdealSheafData (s.obj i)
  | 0 => H.comap s.isoZero.hom
  | i + 1 => strictTransform (s.map i) (s.center i) $ iteratedStrictTransform s H i

section
variable (s : MarkedBlowupSequenceData p I m E)
section
variable (H : ISD X)
theorem iteratedStrictTransform_zero :
    iteratedStrictTransform s H 0 = H.comap s.isoZero.hom := rfl

theorem iteratedStrictTransform_succ (i : ℕ) :
    iteratedStrictTransform s H (i + 1) =
      strictTransform (s.map i) (s.center i) (iteratedStrictTransform s H i) := rfl

def strictTransformAtLength :
    IdealSheafData $ s.obj s.length :=
  iteratedStrictTransform s H s.length

theorem strictTransformAtLength_eq :
    strictTransformAtLength s H = iteratedStrictTransform s H s.length := rfl
end

def asMarkedData (d : BlowupSequenceData (s.obj s.length)) :
    Option $ MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length :=
  if h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length then
    some $ d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length) h
  else
    none
end

def concatOfIsMarked (hinv : ComapIsoInvariance) (s : MarkedBlowupSequenceData p I m E)
    (d : BlowupSequenceData $ s.obj s.length) : MarkedBlowupSequenceData p I m E :=
  match asMarkedData s d with
  | some t => s.append t hinv
  | none => s

end

def tunedIdeal (S : MarkedIdealWithBoundary) (hft : LocallyOfFiniteType S.structMap) :
    tISD S :=
  @balancedTunedSheaf S.base _ _ S.scheme S.structMap hft S.ideal S.mult

def tunedTriple (S : MarkedIdealWithBoundary)
    (s : S.mbs)
    (hft : LocallyOfFiniteType $ s.proj s.length ≫ structMap S)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) : MarkedIdealWithBoundary where
  base := S.base
  instField := S.instField
  scheme := s.obj s.length
  structMap := s.proj s.length ≫ structMap S
  ideal :=
    @balancedTunedSheaf S.base _ _ (s.obj s.length) (s.proj s.length ≫ structMap S) hft
      (s.ideal s.length) S.mult
  mult := tuningExponent S.mult
  boundary := extra ++ (s.boundary s.length).drop keep

section
variable (T : MarkedIdealWithBoundary)
def asMarkedSeq (d : BlowupSequenceData T.scheme) : T.SequenceOfBlowups :=
  if h : d.IsMarked T.structMap T.ideal T.mult T.boundary then
    toMarkedSequenceOfBlowups $ d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary h
  else
    emptyMarkedSeq T

def dropTrivialBoundary : MarkedIdealWithBoundary :=
  withBoundary T $ T.boundary.filter fun D => decide (D ≠ ⊤)

theorem dropTrivialBoundary_def :
    dropTrivialBoundary T = withBoundary T (T.boundary.filter fun D => decide (D ≠ ⊤)) := rfl





@[simp] theorem dropTrivialBoundary_mult : mult (dropTrivialBoundary T) = mult T := rfl

@[simp] theorem dropTrivialBoundary_dim : (dropTrivialBoundary T).krullDimSucc = T.krullDimSucc := rfl

theorem dropTrivialBoundary_boundary :
    boundary (dropTrivialBoundary T) = T.boundary.filter fun D => decide (D ≠ ⊤) := rfl
end

def appendLowerDimReduction (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (resolveLower : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups)
    (S : MarkedIdealWithBoundary) (s : S.mbs)
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (n : ℕ) :
    S.mbs :=
  if hft : LocallyOfFiniteType $ s.proj s.length ≫ structMap S then
    if hdim : (tunedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc then
      concatOfIsMarked hinv s
        (ofSequenceOfBlowups (resolveLower (tunedTriple S s hft extra keep) hdim n).toSequenceOfBlowups)
    else s
  else s

def descendStrictPullback (T S : MarkedIdealWithBoundary) (ph_ : scheme S ⟶ scheme T)
    (s : S.mbs) :
    Option $ BlowupSequenceData T.scheme :=
  if h : ∃ d : BlowupSequenceData T.scheme,
      IsStrictPullbackBlowupSeq ph_ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups then
    some h.choose
  else
    none

def separateBoundary (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (resolveLower : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary) :
    ℕ → S.mbs
  | 0 => S.embs
  | j + 1 => appendLowerDimReduction hinv T resolveLower S (separateBoundary hinv T resolveLower S j) [] 0 j

section
variable (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary) (resolveLower : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups)
def reduceAlongHypersurface (S : MarkedIdealWithBoundary)
    (H : tISD S) : S.mbs :=
  appendLowerDimReduction hinv T resolveLower S (separateBoundary hinv T resolveLower S S.boundary.length)
    [strictTransformAtLength (separateBoundary hinv T resolveLower S S.boundary.length) H] S.boundary.length 0

def reduceOrderOfValid (hv : IsAdmissible T) : T.SequenceOfBlowups :=
  have hft : LocallyOfFiniteType (dropTrivialBoundary T).structMap := hv.locallyOfFiniteType
  let W := tunedIdeal (dropTrivialBoundary T) hft
  let mu_ := tuningExponent (dropTrivialBoundary T).mult
  let D := maxContactCover (dropTrivialBoundary T) hft W mu_
  let S := D.markedTriple W mu_
  match descendStrictPullback (dropTrivialBoundary T) S D.disjointUnionMap (reduceAlongHypersurface hinv (dropTrivialBoundary T) resolveLower S D.iInfImageIdeal) with
  | some d => asMarkedSeq T d
  | none => emptyMarkedSeq T

def reduceOrder : T.SequenceOfBlowups :=
  if hv : IsAdmissible T then
    if orderAtLeastLocus T.ideal T.mult = ∅ then emptyMarkedSeq T else reduceOrderOfValid hinv T resolveLower hv
  else
    emptyMarkedSeq T

theorem reduceOrder_of_orderAtLeastLocus_eq_empty (hv : IsAdmissible T)
    (h : orderAtLeastLocus T.ideal T.mult = ∅) : reduceOrder hinv T resolveLower = emptyMarkedSeq T := by
  unfold reduceOrder
  rw [dif_pos hv, if_pos h]
end

end MaxContactReduction

end FunctorialResolution.EmbeddedResolution

end
section

open scoped Classical

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactCoverData

section
variable (T : MarkedIdealWithBoundary)
noncomputable def balancedTunedIdeal (hv : IsAdmissible T) : tISD T :=
  @balancedTunedSheaf T.base _ _ T.scheme T.structMap hv.locallyOfFiniteType T.ideal T.mult

abbrev tunedMult : ℕ := tuningExponent T.mult

theorem isMaxContactCover_maxContactCover
    (hft : LocallyOfFiniteType T.structMap) (W : T.scheme.IdealSheafData) (mu_ : ℕ)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T, MaxContactReduction.IsMaxContactCover T D hft W mu_) :
    MaxContactReduction.IsMaxContactCover T (MaxContactReduction.maxContactCover T hft W mu_) hft W mu_ := by
  have he : MaxContactReduction.maxContactCover T hft W mu_ = h.choose := dif_pos h
  rw [he]
  exact h.choose_spec

section
variable (hv : IsAdmissible T)
noncomputable def chosenCoverData :
    MaxContactReduction.FiniteOpenCoverWithIdeals T :=
  MaxContactReduction.maxContactCover T hv.locallyOfFiniteType (balancedTunedIdeal T hv) $ tunedMult T

theorem isMaxContactCover_chosenCoverData
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (balancedTunedIdeal T hv) $ tunedMult T) :
    MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) $ tunedMult T :=
  isMaxContactCover_maxContactCover T hv.locallyOfFiniteType (balancedTunedIdeal T hv) (tunedMult T) h

@[reducible] noncomputable def coverMap :
    (chosenCoverData T hv).disjointUnion ⟶ scheme T :=
  (chosenCoverData T hv).disjointUnionMap

theorem coverMap_eq_sigmaOpensDesc :
    coverMap T hv = sigmaOpensDesc T.scheme (chosenCoverData T hv).opens := rfl

theorem etale_coverMap_of_isAdmissible :
    Etale $ coverMap T hv := by
  rw [coverMap_eq_sigmaOpensDesc]
  exact etale_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens
end
end

instance instEtaleCoverMap (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) :
    Etale $ coverMap T hv :=
  etale_coverMap_of_isAdmissible T hv

theorem smooth_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) :
    Smooth $ coverMap T hv := by
  infer_instance

instance instSmoothCoverMap (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) :
    Smooth $ coverMap T hv :=
  smooth_coverMap_of_isAdmissible T hv

theorem flat_coverMap_of_isAdmissible (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) :
    Flat $ coverMap T hv := by
  infer_instance

instance instFlatCoverMap (T : MarkedIdealWithBoundary) (hv : IsAdmissible T) :
    Flat $ coverMap T hv :=
  flat_coverMap_of_isAdmissible T hv



section
variable (T : MarkedIdealWithBoundary)
section
variable (hv : IsAdmissible T)
@[reducible] noncomputable def coverMaxContactIdeal :
    (chosenCoverData T hv).disjointUnion.IdealSheafData :=
  (chosenCoverData T hv).iInfImageIdeal

noncomputable def coverTriple : MarkedIdealWithBoundary :=
  (chosenCoverData T hv).markedTriple (balancedTunedIdeal T hv) $ tunedMult T

section
variable {T}
noncomputable abbrev cT := coverTriple T hv
noncomputable abbrev cI := coverMaxContactIdeal T hv
end



noncomputable def coverMarkedBlowupData (hinv : ComapIsoInvariance)
    (rc : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) :
    MarkedBlowupSequenceData (cT hv).structMap (cT hv).ideal
      (cT hv).mult (cT hv).boundary :=
  MaxContactReduction.reduceAlongHypersurface hinv T rc (cT hv) $ cI hv


@[simp] theorem coverTriple_structureMorphism :
    structMap (cT hv) = coverMap T hv ≫ structMap T := rfl

@[simp] theorem coverTriple_ideal :
    ideal (cT hv) = (balancedTunedIdeal T hv).comap (coverMap T hv) := rfl

@[simp] theorem coverTriple_mult :
    mult (cT hv) = tunedMult T := rfl

@[simp] theorem coverTriple_boundary :
    boundary (cT hv) = T.boundary.map fun D => D.comap $ coverMap T hv := rfl
end

section
variable (d : BlowupSequenceData T.scheme) (h : d.IsMarked T.structMap T.ideal T.mult T.boundary)
include h
theorem asMarkedSeq_eq_toMarkedSequence_of_isMarked :
    MaxContactReduction.asMarkedSeq T d =
      toMarkedSequenceOfBlowups (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary h) :=
  dif_pos h

theorem asMarkedSeq_toSequenceOfBlowups :
    (MaxContactReduction.asMarkedSeq T d).toSequenceOfBlowups = d.toSequenceOfBlowups := by
  rw [asMarkedSeq_eq_toMarkedSequence_of_isMarked T d h,
    toMarkedBlowupSequenceData_toSequenceOfBlowups]
end

@[simp] theorem emptyMarkedSeq_length :
    (MaxContactReduction.emptyMarkedSeq T).length = 0 :=
  emptyMarkedBlowupSequenceData_toMarkedSequence_length T.structMap T.ideal T.mult T.boundary
end

section
variable {T S : MarkedIdealWithBoundary} (ph_ : scheme S ⟶ scheme T) (s : S.mbs)
theorem isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some {d : BlowupSequenceData T.scheme}
    (hd : MaxContactReduction.descendStrictPullback T S ph_ s = some d) :
    IsStrictPullbackBlowupSeq ph_ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups := by
  by_cases hex : ∃ e : BlowupSequenceData T.scheme, IsStrictPullbackBlowupSeq ph_ s.toBlowupSequenceData.toSequenceOfBlowups e.toSequenceOfBlowups
  have he : MaxContactReduction.descendStrictPullback T S ph_ s = some hex.choose := dif_pos hex
  rw [he] at hd
  exact (m105 hd) ▸ hex.choose_spec
  have he : MaxContactReduction.descendStrictPullback T S ph_ s = none := dif_neg hex
  rw [he] at hd
  simp at hd

theorem exists_descendStrictPullback_eq_some
    (h : ∃ d : BlowupSequenceData T.scheme, IsStrictPullbackBlowupSeq ph_ s.toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups) :
    ∃ d : BlowupSequenceData T.scheme, MaxContactReduction.descendStrictPullback T S ph_ s = some d :=
  ⟨h.choose, dif_pos h⟩
end

section
variable (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary) (rc) (hv : IsAdmissible T) (hne : orderAtLeastLocus T.ideal T.mult ≠ ∅) (htrim : IsAdmissible (MaxContactReduction.dropTrivialBoundary T)) (d : BlowupSequenceData T.scheme) (hd : MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T) (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim) (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim) (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) = some d)
include hv hne hd
theorem reduceOrder_eq_asMarkedSeq :
    MaxContactReduction.reduceOrder hinv T rc = MaxContactReduction.asMarkedSeq T d := by
  have key : MaxContactReduction.reduceOrderOfValid hinv T rc hv = MaxContactReduction.asMarkedSeq T d := by
    show (match MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
            (coverTriple (MaxContactReduction.dropTrivialBoundary T) htrim)
            (coverMap (MaxContactReduction.dropTrivialBoundary T) htrim)
            (coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) htrim hinv rc) with
          | some e => MaxContactReduction.asMarkedSeq T e
          | none => MaxContactReduction.emptyMarkedSeq T) = MaxContactReduction.asMarkedSeq T d
    rw [hd]
  unfold MaxContactReduction.reduceOrder
  rw [dif_pos hv, if_neg hne, key]

theorem reduceOrder_eq_toMarkedSequence
    (hm : d.IsMarked T.structMap T.ideal T.mult T.boundary) :
    MaxContactReduction.reduceOrder hinv T rc =
      toMarkedSequenceOfBlowups (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm) := by
  rw [reduceOrder_eq_asMarkedSeq hinv T rc hv hne htrim d hd, asMarkedSeq_eq_toMarkedSequence_of_isMarked T d hm]
end

section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

theorem concatOfIsMarked_eq_append_of_isMarked (hinv : ComapIsoInvariance) (s : MarkedBlowupSequenceData p I m E)
    (d : BlowupSequenceData $ s.obj s.length)
    (h : d.IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length) :
    MaxContactReduction.concatOfIsMarked hinv s d =
      s.append (d.toMarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m
        (s.boundary s.length) h) hinv := by
  have hr : MaxContactReduction.asMarkedData s d =
      some (d.toMarkedBlowupSequenceData (lastP s ≫ p) (lastI s) m (lastB s) h) := by
    exact dif_pos h
  show (match MaxContactReduction.asMarkedData s d with
        | some t => s.append t hinv
        | none => s) = _
  rw [hr]

end

section
variable (S : MarkedIdealWithBoundary) (s : S.mbs) (hft : LocallyOfFiniteType (s.proj s.length ≫ structMap S)) (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ)
noncomputable def derivedTriple : MarkedIdealWithBoundary :=
  MaxContactReduction.tunedTriple S s hft extra keep

@[simp] theorem derivedTriple_scheme :
    scheme (derivedTriple S s hft extra keep) = s.obj s.length := rfl

@[simp] theorem derivedTriple_mult :
    mult (derivedTriple S s hft extra keep) = tuningExponent S.mult := rfl

@[simp] theorem derivedTriple_boundary :
    boundary (derivedTriple S s hft extra keep) = extra ++ (s.boundary s.length).drop keep := rfl

theorem derivedTriple_structureMorphism :
    structMap (derivedTriple S s hft extra keep) = s.proj s.length ≫ structMap S := rfl
end

section
variable (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary) (rc : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) (S : MarkedIdealWithBoundary)
section
variable (s : S.mbs) (extra : List (s.obj s.length).IdealSheafData) (keep n : ℕ)
theorem appendLowerDimReduction_eq_concatOfIsMarked
    (hft : LocallyOfFiniteType $ s.proj s.length ≫ structMap S)
    (hdim : (derivedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc) :
    MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep n =
      MaxContactReduction.concatOfIsMarked hinv s
        (ofSequenceOfBlowups (rc (derivedTriple S s hft extra keep) hdim n).toSequenceOfBlowups) := by
  unfold MaxContactReduction.appendLowerDimReduction
  rw [dif_pos hft]
  exact dif_pos hdim

theorem appendLowerDimReduction_of_not_locallyOfFiniteType
    (hft : ¬ LocallyOfFiniteType (s.proj s.length ≫ structMap S)) :
    MaxContactReduction.appendLowerDimReduction hinv T rc S s extra keep n = s := by
  unfold MaxContactReduction.appendLowerDimReduction
  exact dif_neg hft
end

@[simp] theorem separateBoundary_zero :
    MaxContactReduction.separateBoundary hinv T rc S 0 =
      S.embs := rfl

theorem separateBoundary_succ (j : ℕ) :
    MaxContactReduction.separateBoundary hinv T rc S (j + 1) =
      MaxContactReduction.appendLowerDimReduction hinv T rc S (MaxContactReduction.separateBoundary hinv T rc S j) [] 0 j := rfl

theorem reduceAlongHypersurface_eq_appendLowerDimReduction
    (H : tISD S) :
    MaxContactReduction.reduceAlongHypersurface hinv T rc S H =
      MaxContactReduction.appendLowerDimReduction hinv T rc S
        (MaxContactReduction.separateBoundary hinv T rc S S.boundary.length)
        [MaxContactReduction.strictTransformAtLength (MaxContactReduction.separateBoundary hinv T rc S S.boundary.length) H]
        S.boundary.length 0 := rfl
end

end MaxContactCoverData

end FunctorialResolution.EmbeddedResolution
end
section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactCoverData

theorem surjective_coverMap (T : MarkedIdealWithBoundary) (hv : IsAdmissible T)
    (h : ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (balancedTunedIdeal T hv) $ tunedMult T) :
    Surjective $ coverMap T hv := by
  rw [coverMap_eq_sigmaOpensDesc]
  exact surjective_sigmaOpensDesc T.scheme (chosenCoverData T hv).opens $ (isMaxContactCover_chosenCoverData T hv h).covers

end MaxContactCoverData

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable {n1_ n2_ n : Type} (e : n1_ ⊕ n2_ ≃ n) (S : Sch)
section
variable {X} (f : X ⟶ AffineSpace n1_ S) (g : X ⟶ AffineSpace n2_ S)
def homOfSumCoords :
    X ⟶ AffineSpace n S :=
  AffineSpace.homOfVector (f ≫ AffineSpace n1_ S ↘ S)
    (fun i =>
      elim (fun a => appTop f $ AffineSpace.coord S a)
        (fun b => appTop g $ AffineSpace.coord S b) $ e.symm i)

@[simp]
theorem homOfSumCoords_appTop_coord_inl (a : n1_) :
    appTop (homOfSumCoords e S f g) (AffineSpace.coord S $ e $ inl a) =
      appTop f (AffineSpace.coord S a) := by
  simp [homOfSumCoords]

@[simp]
theorem homOfSumCoords_appTop_coord_inr (b : n2_) :
    appTop (homOfSumCoords e S f g) (AffineSpace.coord S $ e $ inr b) =
      appTop g (AffineSpace.coord S b) := by
  simp [homOfSumCoords]

theorem homOfSumCoords_comp_reindex_inl :
    homOfSumCoords e S f g ≫ AffineSpace.reindex (S := S) (fun a : n1_ => e $ inl a) = f := by
  refine m46 ?_ fun a => ?_
  simp [homOfSumCoords]
  rw [comp_appTop, comp_apply]
  simp

theorem homOfSumCoords_comp_reindex_inr
    (hfg : f ≫ (AffineSpace n1_ S ↘ S) = g ≫ (AffineSpace n2_ S ↘ S)) :
    homOfSumCoords e S f g ≫ AffineSpace.reindex (S := S) (fun b : n2_ => e $ inr b) = g := by
  refine m46 ?_ fun b => ?_
  simpa [homOfSumCoords] using hfg
  rw [comp_appTop, comp_apply]
  simp

theorem eq_homOfSumCoords_of_comp_reindex
    (m : X ⟶ AffineSpace n S)
    (h1_ : m ≫ AffineSpace.reindex (S := S) (fun a : n1_ => e $ inl a) = f)
    (h2_ : m ≫ m159 (S := S) (fun b : n2_ => e $ inr b) = g) :
    m = homOfSumCoords e S f g := by
  refine m46 ?_ fun i => ?_
  have h : (m ≫ m159 (S := S) fun a => e $ inl a) ≫
      (AffineSpace n1_ S ↘ S) = f ≫ (AffineSpace n1_ S ↘ S) := by rw [h1_]
  simpa [homOfSumCoords] using h
  obtain ⟨j, rfl⟩ : ∃ j, e j = i := ⟨e.symm i, e.apply_symm_apply i⟩
  obtain (a | b) := j
  have h : appTop (m ≫ m159 (S := S) fun a => e $ inl a)
      (m9 S a) = appTop f (m9 S a) := by rw [h1_]
  rw [comp_appTop, comp_apply] at h
  simpa using h
  have h : appTop (m ≫ m159 (S := S) fun b => e $ inr b)
      (m9 S b) = appTop g (m9 S b) := by rw [h2_]
  rw [comp_appTop, comp_apply] at h
  simpa using h
end

theorem isPullback_reindex_of_sumEquiv :
    IsPullback
      (AffineSpace.reindex (S := S) fun a : n1_ => e $ inl a)
      (m159 (S := S) fun b : n2_ => e $ inr b)
      (AffineSpace n1_ S ↘ S) $ AffineSpace n2_ S ↘ S := by
  have hcomm : CommSq
      (m159 (S := S) fun a => e $ inl a)
      (m159 (S := S) fun b => e $ inr b)
      (AffineSpace n1_ S ↘ S) $ AffineSpace n2_ S ↘ S := ⟨by simp⟩
  let _a0 := fst (AffineSpace n1_ S ↘ S) $ AffineSpace n2_ S ↘ S
  let _a1 := snd (AffineSpace n1_ S ↘ S) $ AffineSpace n2_ S ↘ S
  let _a2 := homOfSumCoords e S _a0 _a1
  have hA : _a2 ≫
      m159 (S := S) (fun a => e $ inl a) =
      _a0 :=
    homOfSumCoords_comp_reindex_inl e S _ _
  have hB : _a2 ≫
      m159 (S := S) (fun b => e $ inr b) =
      _a1 :=
    homOfSumCoords_comp_reindex_inr e S _ _ condition
  refine IsPullback.of_iso_pullback hcomm
    { hom := m107 _ _ hcomm.w
      inv := _a2
      hom_inv_id := ?_
      inv_hom_id := ?_ }
    (lift_fst _ _ _) $ lift_snd _ _ _
  rw [eq_homOfSumCoords_of_comp_reindex e S _ _ _ (id_comp _) $ id_comp _]
  refine eq_homOfSumCoords_of_comp_reindex e S _ _ _ ?_ ?_
  rw [assoc, hA]
  exact lift_fst _ _ _
  rw [assoc, hB]
  exact lift_snd _ _ _
  refine Limits.pullback.hom_ext ?_ ?_
  rwa [assoc, lift_fst, id_comp]
  rwa [assoc, lift_snd, id_comp]
end

def sumUliftEquivUliftSum (n m : ℕ) :
    (UFin n ⊕ UFin m) ≃ UFS n m where
  toFun := elim (fun a => up $ inl a.down) fun b => up $ inr b.down
  invFun := fun i =>
    elim (fun a => inl $ up a) (fun b => inr $ up b) i.down
  left_inv := by rintro (⟨a⟩ | ⟨b⟩) <;> rfl
  right_inv := by rintro ⟨a | b⟩ <;> rfl





section
variable (k : Type) [Field k] (n m : ℕ)
def projRight :
    affineSpaceIndexedBy k (UFS n m) ⟶ affineSpaceIndexedBy k (UFin m) :=
  AffineSpace.reindex (S := Sp k)
    (fun j : UFin m => (up (inr j.down) : UFS n m))

def projLeft :
    affineSpaceIndexedBy k (UFS n m) ⟶ affineSpaceIndexedBy k (UFin n) :=
  AffineSpace.reindex (S := Sp k)
    (fun j : UFin n => (up (inl j.down) : UFS n m))

@[simp]
theorem projRight_comp_affineSpaceIndexedByToSpec :
    projRight k n m ≫ affineSpaceIndexedByToSpec k (UFin m) =
      affineSpaceIndexedByToSpec k (UFS n m) := by
  simp [projRight]

@[simp]
theorem projRight_appTop_coord (j : Fin m) :
    appTop (projRight k n m)
        (AffineSpace.coord (Sp k) $ up j) =
      AffineSpace.coord (Sp k)
        (up (inr j) : UFS n m) := by
  simp [projRight]

@[simp]
theorem projLeft_comp_affineSpaceIndexedByToSpec :
    projLeft k n m ≫ affineSpaceIndexedByToSpec k (UFin n) =
      affineSpaceIndexedByToSpec k (UFS n m) := by
  simp [projLeft]

@[simp]
theorem projLeft_appTop_coord (j : Fin n) :
    appTop (projLeft k n m)
        (AffineSpace.coord (Sp k) $ up j) =
      AffineSpace.coord (Sp k)
        (up (inl j) : UFS n m) := by
  simp [projLeft]

theorem isPullback_projLeft_projRight :
    IsPullback (projLeft k n m) (projRight k n m)
      (affineSpaceIndexedByToSpec k $ UFin n)
      (affineSpaceIndexedByToSpec k $ UFin m) :=
  isPullback_reindex_of_sumEquiv (sumUliftEquivUliftSum n m) $ Sp k
end

section
variable (hs : AffineSpaceIsSmooth) (k : Type) [Field k] (n m : ℕ)
include hs
theorem smooth_projRight :
    Smooth $ projRight k n m :=
  m98 (P := @Smooth)
    (isPullback_projLeft_projRight k n m) $ hs k n

theorem smooth_projLeft :
    Smooth $ projLeft k n m := by
  exact of_isPullback (isPullback_reindex_of_sumEquiv (sumUliftEquivUliftSum n m) $ Sp k).flip $ hs k m
end

section
variable (k : Type) [Field k] (n m c : ℕ) (U : (affineSpaceIndexedBy k (UFin n)).Opens) (ph_ : toScheme U ⟶ affineSpaceIndexedBy k (UFin c))
def prodMapOnPreimage :
    toScheme (projLeft k n m ⁻¹ᵁ U) ⟶ affineSpaceIndexedBy k (UFS c m) :=
  AffineSpace.homOfVector
    (ι (projLeft k n m ⁻¹ᵁ U) ≫ affineSpaceIndexedByToSpec k (UFS n m))
    (fun i =>
      elim
        (fun a : Fin c =>
          appTop (morphismRestrict (projLeft k n m) U ≫ ph_)
            (AffineSpace.coord (Sp k) $ up a))
        (fun b : Fin m =>
          appTop (ι $ projLeft k n m ⁻¹ᵁ U)
            (AffineSpace.coord (Sp k)
              (up (inr b) : UFS n m)))
        i.down)

theorem prodMapOnPreimage_comp_affineSpaceIndexedByToSpec :
    prodMapOnPreimage k n m c U ph_ ≫ affineSpaceIndexedByToSpec k (UFS c m) =
      ι (projLeft k n m ⁻¹ᵁ U) ≫ affineSpaceIndexedByToSpec k (UFS n m) := by
  simp [prodMapOnPreimage]

theorem prodMapOnPreimage_comp_projRight :
    prodMapOnPreimage k n m c U ph_ ≫ projRight k c m =
      ι (projLeft k n m ⁻¹ᵁ U) ≫ projRight k n m := by
  refine m46 ?_ ?_
  rw [assoc, projRight_comp_affineSpaceIndexedByToSpec, assoc, projRight_comp_affineSpaceIndexedByToSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
  rintro ⟨j⟩
  simp only [comp_appTop, comp_apply]
  rw [projRight_appTop_coord, projRight_appTop_coord]
  simp [prodMapOnPreimage]

section
variable (hph : ph_ ≫ affineSpaceIndexedByToSpec k (UFin c) = ι U ≫ affineSpaceIndexedByToSpec k (UFin n))
include hph
theorem morphismRestrict_projLeft_comp :
    morphismRestrict (projLeft k n m) U ≫ ph_ =
      prodMapOnPreimage k n m c U ph_ ≫ projLeft k c m := by
  let _a0 := opI (projLeft k n m ⁻¹ᵁ U) ≫ affineSpaceIndexedByToSpec k (UFS n m)
  let _a1 := prodMapOnPreimage k n m c U ph_ ≫ projLeft k c m
  refine m46 ?_ ?_
  have h1 : (morphismRestrict (projLeft k n m) U ≫ ph_) ≫
      affineSpaceIndexedByToSpec k (UFin c) =
      _a0 := by
    rw [assoc, hph, morphismRestrict_ι_assoc, projLeft_comp_affineSpaceIndexedByToSpec]
  have h2 : _a1 ≫
      affineSpaceIndexedByToSpec k (UFin c) =
      _a0 := by
    rw [assoc, projLeft_comp_affineSpaceIndexedByToSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
  exact tr_ h1 h2.symm
  rintro ⟨j⟩
  symm
  rw [comp_appTop, comp_apply, projLeft_appTop_coord]
  simp [prodMapOnPreimage]

theorem isPullback_prodMapOnPreimage :
    IsPullback (prodMapOnPreimage k n m c U ph_)
      (morphismRestrict (projLeft k n m) U)
      (projLeft k c m) ph_ := by
  have hstar' := (m226 (projLeft k n m) U).paste_vert $ isPullback_projLeft_projRight k n m
  rw [← hph, ← prodMapOnPreimage_comp_projRight] at hstar'
  exact (hstar'.of_bot (morphismRestrict_projLeft_comp k n m c U ph_ hph)
    (isPullback_projLeft_projRight k c m)).flip
end
end

theorem smooth_prodMapOnPreimage (_hs : AffineSpaceIsSmooth) (k : Type) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k $ UFin n).Opens)
    (ph_ : toScheme U ⟶ affineSpaceIndexedBy k (UFin c))
    [Smooth ph_]
    (hph : ph_ ≫ affineSpaceIndexedByToSpec k (UFin c) =
      ι U ≫ affineSpaceIndexedByToSpec k (UFin n)) :
    Smooth $ prodMapOnPreimage k n m c U ph_ := by
  exact m98 (P := @Smooth)
    (isPullback_prodMapOnPreimage k n m c U ph_ hph).flip $ ‹Smooth ph_›





variable {W Y : Sch}

section
variable {X1 X2 X3 X4 : Sch} {p : X1 ⟶ X2} {q : X1 ⟶ X3} {f : X2 ⟶ X4} {h : X3 ⟶ X4} (sq : IsPullback p q f h)
include sq
theorem flat_of_isPullback_of_flat
    (hh : Flat h) : Flat p :=
  of_isPullback
    (P := @Flat) sq.flip hh

theorem surjective_of_isPullback
    (hh : Surjective h) : Surjective p :=
  of_isPullback
    (P := @Surjective) sq.flip hh
end

theorem flat_and_surjective_of_isPullback_blowupMorphism (g : W ⟶ Y) [Flat g]
    [Surjective g] (t : SequenceOfBlowups W) (s : SequenceOfBlowups Y) (L : ℕ)
    (ga_ : ∀ i : ℕ, i ≤ L → (schemeAt t i ⟶ schemeAt s i))
    (hzero : ga_ 0 (zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hsq : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (ga_ (i + 1) hi) (transitionMapSucc t i) (transitionMapSucc s i) $ ga_ i hi.le) :
    ∀ i : ℕ, ∀ hi : i ≤ L,
      Flat (ga_ i hi) ∧ Surjective (ga_ i hi) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have sq0 :=
      (IsPullback.of_horiz_isIso $ CommSq.mk hzero.symm).flip
    exact ⟨flat_of_isPullback_of_flat sq0 inferInstance, surjective_of_isPullback sq0 inferInstance⟩
  | succ n ih =>
    intro hi
    have hn : n < L := hi
    obtain ⟨hf, hs⟩ := ih hn.le
    let _a0 := hsq n hn
    exact ⟨flat_of_isPullback_of_flat _a0 hf, surjective_of_isPullback _a0 hs⟩

structure CompatibleBaseIsoAt (t1_ t2_ : SequenceOfBlowups W) (s1_ s2_ : SequenceOfBlowups Y) (L : ℕ)
    (ga1 : ∀ i : ℕ, i ≤ L → (schemeAt t1_ i ⟶ schemeAt s1_ i))
    (ga2 : ∀ i : ℕ, i ≤ L → (schemeAt t2_ i ⟶ schemeAt s2_ i))
    (ph_ : ∀ i : ℕ, i ≤ L → (schemeAt t1_ i ≅ schemeAt t2_ i)) (i : ℕ) where
  iso : schemeAt s1_ i ≅ schemeAt s2_ i
  compat : ∀ hi : i ≤ L, ga1 i hi ≫ hom iso = hom (ph_ i hi) ≫ ga2 i hi

structure BlowupDescentData (g : W ⟶ Y) (t1_ t2_ : SequenceOfBlowups W) (s1_ s2_ : SequenceOfBlowups Y) (L : ℕ)
    (ga1 : ∀ i : ℕ, i ≤ L → (schemeAt t1_ i ⟶ schemeAt s1_ i))
    (ga2 : ∀ i : ℕ, i ≤ L → (schemeAt t2_ i ⟶ schemeAt s2_ i))
    (ph_ : ∀ i : ℕ, i ≤ L → (schemeAt t1_ i ≅ schemeAt t2_ i)) : Prop where
  isBlowup_s1 : ∀ i : ℕ, i < L → IsBlowupAlongIdealSheaf (transitionMapSucc s1_ i) (center s1_ i)
  isBlowup_s2 : ∀ i : ℕ, i < L → IsBlowupAlongIdealSheaf (transitionMapSucc s2_ i) (center s2_ i)
  center_t1 : ∀ i : ℕ, ∀ hi : i < L, center t1_ i = (center s1_ i).comap (ga1 i hi.le)
  center_t2 : ∀ i : ℕ, ∀ hi : i < L, center t2_ i = (center s2_ i).comap (ga2 i hi.le)
  flat_ga1 : ∀ i : ℕ, ∀ hi : i ≤ L, Flat $ ga1 i hi
  pullback_ga1 : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (ga1 (i + 1) hi) (transitionMapSucc t1_ i) (transitionMapSucc s1_ i) $ ga1 i hi.le
  pullback_ga2 : ∀ i : ℕ, ∀ hi : i < L,
    IsPullback (ga2 (i + 1) hi) (transitionMapSucc t2_ i) (transitionMapSucc s2_ i) $ ga2 i hi.le
  zero_ga1 : ga1 0 (zero_le _) ≫ s1_.isoZero.hom = t1_.isoZero.hom ≫ g
  zero_ga2 : ga2 0 (zero_le _) ≫ s2_.isoZero.hom = t2_.isoZero.hom ≫ g
  surjective_ga1 : ∀ i : ℕ, ∀ hi : i ≤ L, Surjective $ ga1 i hi
  isBlowup_t1 : ∀ i : ℕ, i < L → IsBlowupAlongIdealSheaf (transitionMapSucc t1_ i) (center t1_ i)
  center_ph : ∀ i : ℕ, ∀ hi : i < L, (center t2_ i).comap (ph_ i hi.le).hom = center t1_ i
  zero_ph : hom (ph_ 0 $ zero_le _) ≫ t2_.isoZero.hom = t1_.isoZero.hom
  step_ph : ∀ i : ℕ, ∀ hi : i < L,
    hom (ph_ (i + 1) hi) ≫ transitionMapSucc t2_ i = transitionMapSucc t1_ i ≫ hom (ph_ i hi.le)

section
variable {g} {t1_ t2_ : SequenceOfBlowups W} {s1_ s2_ : SequenceOfBlowups Y} {L} {ga1} {ga2} {ph_} (hd : BlowupDescentData g t1_ t2_ s1_ s2_ L ga1 ga2 ph_)
include hd
theorem comp_isoObjZero_trans_symm_eq :
    ∀ hi : (0 : ℕ) ≤ L,
      ga1 0 hi ≫ hom (s1_.isoZero ≪≫ s2_.isoZero.symm) = hom (ph_ 0 hi) ≫ ga2 0 hi := by
  intro hi
  refine mp_ (cancel_mono $ sbIzH s2_) ?_
  simp [trans_hom, symm_hom, assoc, m114, comp_id]
  rw [hd.zero_ga1, hd.zero_ga2, ← assoc, hd.zero_ph]

section
variable {i} (hi : i < L) (st : CompatibleBaseIsoAt t1_ t2_ s1_ s2_ L ga1 ga2 ph_ i)
include hi
theorem CompatibleBaseIsoAt.center_comap_eq :
    (center s2_ i).comap st.iso.hom = center s1_ i := by
  have := hd.flat_ga1 i hi.le
  have := hd.surjective_ga1 i hi.le
  refine FlatDescentIdealSheaf.eq_of_comap_eq (ga1 i hi.le) _ _ ?_
  rw [← comap_comp, st.compat hi.le, comap_comp,
    ← hd.center_t2 i hi, hd.center_ph i hi]
  exact hd.center_t1 i hi

theorem CompatibleBaseIsoAt.exists_iso_succ_blowupMorphism_comm :
    ∃ e : schemeAt s1_ (i + 1) ≅ schemeAt s2_ (i + 1),
      hom e ≫ transitionMapSucc s2_ i ≫ st.iso.inv = transitionMapSucc s1_ i := by
  have h2 := (hd.isBlowup_s2 i hi).comp_iso_hom st.iso.symm
  simp [symm_hom, symm_inv] at h2
  rw [CompatibleBaseIsoAt.center_comap_eq hd hi st] at h2
  exact (hd.isBlowup_s1 i hi).exists_iso h2
end
end

theorem CompatibleBaseIsoAt.blowupMorphism_square_comm {t1_ t2_ : SequenceOfBlowups W} {s1_ s2_ : SequenceOfBlowups Y}
    {L : ℕ}
    {ga1 : ∀ i : ℕ, i ≤ L → (schemeAt t1_ i ⟶ schemeAt s1_ i)}
    {ga2 : ∀ i : ℕ, i ≤ L → (schemeAt t2_ i ⟶ schemeAt s2_ i)}
    {ph_ : ∀ i : ℕ, i ≤ L → (schemeAt t1_ i ≅ schemeAt t2_ i)}
    {i : ℕ} (st : CompatibleBaseIsoAt t1_ t2_ s1_ s2_ L ga1 ga2 ph_ i)
    (e : schemeAt s1_ (i + 1) ≅ schemeAt s2_ (i + 1))
    (he : hom e ≫ transitionMapSucc s2_ i ≫ st.iso.inv = transitionMapSucc s1_ i) :
    hom e ≫ transitionMapSucc s2_ i = transitionMapSucc s1_ i ≫ st.iso.hom := by
  rw [← he]
  simp

section
variable {A B : ℕ → Sch}
section
variable (x : A 0 ≅ B 0)
def isoFamilyOfZero (i : ℕ) (hi : i ≤ 0) : A i ≅ B i :=
  Eq.mpr (congrArg (fun j : ℕ => (A j ≅ B j)) $ mp le_zero hi) x

theorem isoFamilyOfZero_zero {hi : (0 : ℕ) ≤ 0} :
    isoFamilyOfZero x 0 hi = x := rfl
end

section
variable (N) (e : ∀ i : ℕ, i ≤ N → (A i ≅ B i)) (x : A (N + 1) ≅ B (N + 1))
def extendIsoFamilySucc (i : ℕ) (hi : i ≤ N + 1) : A i ≅ B i :=
  if h : i ≤ N then e i h
  else Eq.mpr (congrArg (fun j : ℕ => (A j ≅ B j))
    (Nat.le_antisymm hi $ Nat.not_le.mp h)) x

theorem extendIsoFamilySucc_of_le {i : ℕ} {hi : i ≤ N + 1}
    (h : i ≤ N) : extendIsoFamilySucc N e x i hi = e i h := dif_pos h

theorem extendIsoFamilySucc_self {hi : N + 1 ≤ N + 1} :
    extendIsoFamilySucc N e x (N + 1) hi = x := dif_neg $ not_succ_le_self N
end
end

theorem exists_compatible_isos_of_le {g : W ⟶ Y} {t1_ t2_ : SequenceOfBlowups W} {s1_ s2_ : SequenceOfBlowups Y} {L : ℕ}
    {ga1 : ∀ i : ℕ, i ≤ L → (schemeAt t1_ i ⟶ schemeAt s1_ i)}
    {ga2 : ∀ i : ℕ, i ≤ L → (schemeAt t2_ i ⟶ schemeAt s2_ i)}
    {ph_ : ∀ i : ℕ, i ≤ L → (schemeAt t1_ i ≅ schemeAt t2_ i)}
    (hd : BlowupDescentData g t1_ t2_ s1_ s2_ L ga1 ga2 ph_) (N : ℕ) :
    ∀ hN : N ≤ L, ∃ e : ∀ i : ℕ, i ≤ N → (schemeAt s1_ i ≅ schemeAt s2_ i),
      (hom (e 0 $ zero_le _) ≫ s2_.isoZero.hom = s1_.isoZero.hom) ∧
      (∀ i : ℕ, ∀ hi : i < N,
        hom (e (i + 1) hi) ≫ transitionMapSucc s2_ i = transitionMapSucc s1_ i ≫ hom (e i hi.le)) ∧
      (∀ i : ℕ, ∀ hi : i ≤ N,
        ga1 i (hi.trans hN) ≫ hom (e i hi)
          = hom (ph_ i $ hi.trans hN) ≫ ga2 i (hi.trans hN)) := by
  induction N with
  | zero =>
    intro hN
    refine ⟨isoFamilyOfZero (A := fun i => sbAt s1_ i) (B := fun i => sbAt s2_ i)
      (s1_.isoZero ≪≫ s2_.isoZero.symm), ?_, ?_, ?_⟩
    rw [isoFamilyOfZero_zero]
    simp
    intro i hi
    exact absurd hi $ not_lt_zero i
    intro i hi
    obtain rfl : i = 0 := mp le_zero hi
    rw [isoFamilyOfZero_zero]
    exact comp_isoObjZero_trans_symm_eq hd $ hi.trans hN
  | succ N ih =>
    intro hN
    have hNlt : N < L := hN
    obtain ⟨e, h0, hsqe, hc⟩ := ih hNlt.le
    have hstN := hc N $ m164 N
    let st : CompatibleBaseIsoAt t1_ t2_ s1_ s2_ L ga1 ga2 ph_ N :=
      { iso := e N $ m164 N
        compat := fun _ => hstN }
    obtain ⟨x, hx⟩ := CompatibleBaseIsoAt.exists_iso_succ_blowupMorphism_comm hd hNlt st
    have hxsq :=
      CompatibleBaseIsoAt.blowupMorphism_square_comm st x hx
    refine ⟨extendIsoFamilySucc (A := fun i => sbAt s1_ i) (B := fun i => sbAt s2_ i) N e x,
      ?_, ?_, ?_⟩
    rwa [extendIsoFamilySucc_of_le N e x $ m67 N]
    intro i hi
    rcases m63 i N with h | h
    rw [extendIsoFamilySucc_of_le N e x $ Nat.succ_le_of_lt h, extendIsoFamilySucc_of_le N e x h.le]
    exact hsqe i h
    obtain rfl : i = N := Nat.le_antisymm (mp_ lt_succ_iff hi) h
    rwa [extendIsoFamilySucc_self, extendIsoFamilySucc_of_le _ _ _ $ m164 _]
    intro i hi
    rcases m63 i (N + 1) with h | h
    have hiN : i ≤ N := mp_ lt_succ_iff h
    rw [extendIsoFamilySucc_of_le N e x hiN]
    exact hc i hiN
    obtain rfl : i = N + 1 := Nat.le_antisymm hi h
    rw [extendIsoFamilySucc_self]
    let _a0 := sbTrS t1_ N ≫ isoH (ph_ N hNlt.le) ≫ ga2 N hNlt.le
    have ha : (ga1 (N + 1) hNlt ≫ isoH x) ≫ sbTrS s2_ N
        = _a0 := by
      rw [assoc, hxsq, ← assoc, (hd.pullback_ga1 N hNlt).w,
        assoc, hstN]
    have hb : (isoH (ph_ (N + 1) hNlt) ≫ ga2 (N + 1) hNlt) ≫ sbTrS s2_ N
        = _a0 := by
      rw [assoc, (hd.pullback_ga2 N hNlt).w, ← assoc,
        hd.step_ph N hNlt, assoc]
    have hide : (center s2_ N).comap
        _a0
        = cmI (center t1_ N) (transitionMapSucc t1_ N) := by
      rw [comap_comp, comap_comp,
        ← hd.center_t2 N hNlt, hd.center_ph N hNlt]
    refine (hd.isBlowup_s2 N hNlt).hom_ext_of_comp_eq ?_ ha hb
    rw [hide]
    exact an1 $ hd.isBlowup_t1 N hNlt

theorem IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic {g : W ⟶ Y} [Flat g]
    [Surjective g] {t1_ t2_ : SequenceOfBlowups W} {s1_ s2_ : SequenceOfBlowups Y}
    (h1_ : IsStrictPullbackBlowupSeq g t1_ s1_) (h2_ : IsStrictPullbackBlowupSeq g t2_ s2_)
    (he : t1_.Isomorphic t2_) : s1_.Isomorphic s2_ := by
  obtain ⟨hlen1_, sg1, hsg10, hsg1sq, hsg1c⟩ := h1_
  obtain ⟨hlen2_, sg2, hsg20, hsg2sq, hsg2c⟩ := h2_
  obtain ⟨hlent, ph_, hph0, hphstep, hphc⟩ := he
  have hfs := flat_and_surjective_of_isPullback_blowupMorphism g t1_ s1_ t1_.length sg1 hsg10 hsg1sq
  have hd : BlowupDescentData g t1_ t2_ s1_ s2_ t1_.length sg1
      (fun i hi => sg2 i $ le_of_le_of_eq hi hlent) ph_ := by
    refine ⟨fun i hi => s1_.isBlowupAlongIdealSheaf_blowupMorphism i $ by omega,
      fun i hi => s2_.isBlowupAlongIdealSheaf_blowupMorphism i $ by omega,
      hsg1c, fun i hi => hsg2c i $ by omega,
      fun i hi => an1 $ hfs i hi, hsg1sq, fun i hi => hsg2sq i $ by omega,
      hsg10, hsg20, fun i hi => an2 $ hfs i hi,
      fun i hi => t1_.isBlowupAlongIdealSheaf_blowupMorphism i hi, hphc, hph0, hphstep⟩
  obtain ⟨e, h0, hsqe, hc⟩ := exists_compatible_isos_of_le hd t1_.length $ m164 _
  refine ⟨by omega, fun i hi => e i $ by omega, h0, ?_, ?_⟩
  intro i hi
  exact hsqe i $ by omega
  intro i hi
  have hiT : i < t1_.length := by omega
  exact CompatibleBaseIsoAt.center_comap_eq hd hiT
    { iso := e i hiT.le, compat := fun _ => hc i hiT.le }

end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable (A : Sch) [IsAffine A] {B'} (σ : Γ(A, ⊤) ⟶ B')
def specHomOfGlobalSections : Spec B' ⟶ A :=
  Spec.map σ ≫ A.isoSpec.inv

@[simp]
theorem specHomOfGlobalSections_appTop (s : Γ(A, ⊤)) :
    appTop (specHomOfGlobalSections A σ) s = inv (GSpecIso B') (σ s) := by
  have hcomp : specHomOfGlobalSections A σ ≫ A.isoSpec.hom = m12 σ := by
    simp [specHomOfGlobalSections]
  let _a0 := GSpecIso Γ(A, ⊤)
  have h : hom _a0 ≫ appTop (specHomOfGlobalSections A σ)
      = appTop (m12 σ) := by
    rw [← Scheme.toSpecΓ_appTop, ← isoSpec_hom, ← comp_appTop, hcomp]
  have h3 : appTop (specHomOfGlobalSections A σ) = σ ≫ inv (GSpecIso B') := by
    rw [← cancel_epi _a0.hom, Scheme.ΓSpecIso_inv_naturality,
      hom_inv_id_assoc]
    exact h
  rw [h3, comp_apply]
end

section
variable (k : Type) [Field k] (A) [IsAffine A] (pA : A ⟶ Sp k) (M) (e : A ⟶ affineSpaceIndexedBy k (UFin M))
section
variable {B'} (σ : Γ(A, ⊤) ⟶ B') (n) (b : Fin n → B')
def specToAffineSpaceExtendCoords :
    Spec B' ⟶ affineSpaceIndexedBy k (UFS M n) :=
  AffineSpace.homOfVector (specHomOfGlobalSections A σ ≫ pA)
    (fun i =>
      elim
        (fun a : Fin M =>
          appTop (specHomOfGlobalSections A σ ≫ e)
            (AffineSpace.coord (Sp k) $ up a))
        (fun j : Fin n => inv (GSpecIso B') $ b j)
        i.down)

@[simp]
theorem specToAffineSpaceExtendCoords_comp_toSpec :
    specToAffineSpaceExtendCoords k A pA M e σ n b ≫ affineSpaceIndexedByToSpec k (UFS M n) =
      specHomOfGlobalSections A σ ≫ pA := by
  simp [specToAffineSpaceExtendCoords]

@[simp]
theorem specToAffineSpaceExtendCoords_appTop_coord_inl (a : Fin M) :
    appTop (specToAffineSpaceExtendCoords k A pA M e σ n b)
        (AffineSpace.coord (Sp k)
          (up (inl a) : UFS M n)) =
      appTop (specHomOfGlobalSections A σ ≫ e)
        (AffineSpace.coord (Sp k) $ up a) := by
  simp [specToAffineSpaceExtendCoords]

@[simp]
theorem specToAffineSpaceExtendCoords_appTop_coord_inr (j : Fin n) :
    appTop (specToAffineSpaceExtendCoords k A pA M e σ n b)
        (AffineSpace.coord (Sp k)
          (up (inr j) : UFS M n)) =
      inv (GSpecIso B') (b j) := by
  simp [specToAffineSpaceExtendCoords]

theorem specToAffineSpaceExtendCoords_comp_projLeft
    (he : e ≫ affineSpaceIndexedByToSpec k (UFin M) = pA) :
    specToAffineSpaceExtendCoords k A pA M e σ n b ≫ projLeft k M n = specHomOfGlobalSections A σ ≫ e := by
  refine m46 ?_ ?_
  simp [he]
  rintro ⟨a⟩
  rw [comp_appTop, comp_apply, projLeft_appTop_coord,
    specToAffineSpaceExtendCoords_appTop_coord_inl]
end

section
variable [IsClosedImmersion e] {B'} (σ : Γ(A, ⊤) ⟶ B') (n) (b) (he : e ≫ affineSpaceIndexedByToSpec k (UFin M) = pA) (hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤), MvPolynomial.eval₂ σ.hom b p = x)
include he hgen
theorem specToAffineSpaceExtendCoords_appTop_surjective :
    Function.Surjective ⇑(appTop $ specToAffineSpaceExtendCoords k A pA M e σ n b) := by
  let _a0 := specToAffineSpaceExtendCoords k A pA M e σ n b
  let _a1 := GSpecIso B'
  have hsec : ∀ s : Γ(A, ⊤), ∃ P, hAT _a0 P
      = isoI _a1 (σ s) := by
    intro s
    obtain ⟨P, hPs⟩ := (right $ isAffine_surjective_of_isAffine e) s
    refine ⟨hAT (projLeft k M n) P, ?_⟩
    have h2 := congrArg
      (fun g : Spec B' ⟶ affineSpaceIndexedBy k (UFin M) => hAT g P) $ specToAffineSpaceExtendCoords_comp_projLeft k A pA M e σ n b he
    simp only [comp_appTop, comp_apply] at h2
    rw [h2, hPs, specHomOfGlobalSections_appTop]
  have key : ∀ p : MvPolynomial (Fin n) Γ(A, ⊤), ∃ P,
      appTop _a0 P
        = isoI _a1 (MvPolynomial.eval₂ σ.hom b p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C s =>
        obtain ⟨P, hP⟩ := hsec s
        refine ⟨P, ?_⟩
        rwa [MvPolynomial.eval₂_C]
    | add p q hp hq =>
        obtain ⟨P, hP⟩ := hp
        obtain ⟨Q, hQ⟩ := hq
        refine ⟨P + Q, ?_⟩
        rw [map_add, MvPolynomial.eval₂_add, map_add, hP, hQ]
    | mul_X p j hp =>
        obtain ⟨P, hP⟩ := hp
        refine ⟨P * m9 (Sp k)
          (up (inr j) : UFS M n), ?_⟩
        rw [map_mul, hP, specToAffineSpaceExtendCoords_appTop_coord_inr, MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_X, map_mul]
  intro y
  obtain ⟨p, hp⟩ := hgen $ isoH _a1 y
  obtain ⟨P, hP⟩ := key p
  refine ⟨P, ?_⟩
  rw [hP, hp]
  simp

theorem isClosedImmersion_specToAffineSpaceExtendCoords :
    IsClosedImmersion $ specToAffineSpaceExtendCoords k A pA M e σ n b :=
  of_surjective_of_isAffine _
    (specToAffineSpaceExtendCoords_appTop_surjective k A pA M e σ n b he hgen)
end
end

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

namespace MarkedIdealWithBoundary

theorem isAdmissible_baseChange (T : MarkedIdealWithBoundary) (hV : IsAdmissible T) (L : Type) [Field L]
    [CharZero L] (f : T.base →+* L) : IsAdmissible $ bc T f := by
  let _a0 := specMapOfFieldHom T.base L f
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  refine
    { charZero := ‹CharZero L›
      locallyOfFiniteType := ?_
      nonzeroOnComponents := ?_
      one_le_mult := hV.one_le_mult
      quasiCompact := ?_
      smooth := ?_
      snc := ?_ }
  exact
    (inferInstance : LocallyOfFiniteType
      (pullback.snd T.structMap _a0))
  exact hV.nonzeroOnComponents.comap_of_flat
    (pullback.fst T.structMap _a0)
  exact
    (inferInstance : QuasiCompact
      (pullback.snd T.structMap _a0))
  exact smooth_pullbackSnd_specMap T.structMap $ ofHom f
  exact inStrictNormalCrossingPosition_comap_pullback_specMap T.structMap (ofHom f) T.boundary hV.snc

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution
end
end
-- BEGIN_E2_PROJ_Bundle05
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
abbrev p7 := @MaxContactCoverData.cT
abbrev p8 := @MaxContactCoverData.derivedTriple
abbrev p11 := @MaxContactReduction.dropTrivialBoundary
abbrev p12 := @MaxContactCoverData.coverMap
abbrev p29 := @MaxContactCoverData.balancedTunedIdeal
abbrev p31 := @MaxContactCoverData.cI
abbrev p42 := @MaxContactReduction.iteratedStrictTransform
abbrev p48 := @MaxContactCoverData.derivedTriple_boundary
end
-- END_E2_PROJ_Bundle05
