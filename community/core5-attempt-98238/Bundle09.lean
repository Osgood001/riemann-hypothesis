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
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace CategoryTheory.Limits
open Category (assoc comp_id id_comp)
open FunctorialResolution.Blowup (IsBlowupAlongIdealSheaf IsLocallyGeneratedByNonZeroDivisor StrictTransformIsBlowupOfClosedSubscheme blowupIsProper comap_map_of_isClosedImmersion comap_schemeImageIdeal exceptionalIdeal exceptionalIdeal_eq_comap isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor isOpen_connectedComponent_of_noetherianSpace noetherianSpace_subscheme strictTransform strictTransformImmersion_eq strictTransformOpens_eq strictTransform_eq_ker)
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData (boundary_length controlledTransform_succ ofSequenceOfBlowups ofSequenceOfBlowups_blowupMorphism ofSequenceOfBlowups_center ofSequenceOfBlowups_isoObjZero ofSequenceOfBlowups_projectionToBase pow_exceptionalIdeal_mul_controlledTransform_succ prepend prepend_blowupMorphism_succ prepend_blowupMorphism_zero prepend_center_succ prepend_center_zero prepend_isoObjZero prepend_length projectionToBase_succ toMarkedBlowupSequenceData_blowupMorphism toMarkedBlowupSequenceData_boundary toMarkedBlowupSequenceData_ideal toMarkedBlowupSequenceData_length toMarkedBlowupSequenceData_toSequenceOfBlowups toSequenceOfBlowups_blowupMorphism toSequenceOfBlowups_isoObjZero)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (blowupMorphism_eq_transitionMap projectionToBase projectionToBase_def schemeAt transitionMap transitionMapSucc transitionMap_comp_projectionToBase transitionMap_def transitionMap_self transitionMap_trans withoutIsoBlowups_isomorphic_self)
open List (eraseIdx_append_of_lt_length eraseIdx_map filter filter_append filter_congr filter_cons get getElem_append_left getElem_map getElem_mem getElem_of_eq get_eq_getElem length length_append length_cons length_eraseIdx length_eraseIdx_add_one length_eraseIdx_of_lt length_map length_nil length_singleton length_take map map_append map_congr_left map_cons map_map map_nil mem_append mem_eraseIdx_iff_getElem mem_map mem_of_mem_take take take_append_of_le_length take_left' take_length take_of_length_le take_succ_cons)
open Nat (cast_one iSup_le_succ leRec leRec_self leRec_succ le_add_left le_induction le_of_succ_le le_succ le_succ_of_le le_zero lt_of_succ_le lt_of_succ_lt_succ lt_succ_iff lt_succ_of_lt lt_succ_self not_lt_zero not_succ_le_zero one_le_iff_ne_zero sub_eq_zero_of_le sub_lt sub_self succ_lt_succ succ_ne_zero succ_pos)
open Scheme.Hom (isClosedEmbedding ker ker_comp ker_comp_of_isIso le_ker_comp pre support_ker toImage toImage_imageι)
open Scheme.IdealSheafData (comap_comp comap_id comap_mono comap_mul comap_pow comap_sup comap_top eq_top_iff_support_eq_empty ideal_mul ideal_pow ker_subschemeι le_def le_map_comap le_map_iff_comap_le map_comp mem_support_comap mem_support_iff_of_mem mul_top range_subschemeι subscheme subschemeMap_subschemeι subschemeι support support_antitone support_bot support_comap support_nonempty_iff_ne_top support_top top_mul)
open Set (disjoint_left disjoint_right empty_inter empty_subset eq_empty_iff_forall_notMem eq_empty_of_isEmpty ext_iff image_eq_empty image_preimage_eq_inter_range inter_eq_left mem_compl_iff mem_empty_iff_false mem_iUnion mem_inter_iff mem_ofPred_eq mem_preimage mem_range_self mem_singleton_iff nonempty_iff_ne_empty not_nonempty_iff_eq_empty preimage preimage_empty preimage_image_eq range range_comp range_eq_empty range_nonempty sUnion_eq_biUnion sdiff_subset subset_empty_iff subset_univ)
noncomputable section
open CategoryStruct (id)
open FunctorialResolution.EmbeddedResolution.DivisorReduction (containedComponentsIdeal containedComponentsIdeal_eq_ker divisorReductionSeq divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty divisorReductionSeq_eq_of_containedComponentsIdeal_eq_top divisorReductionSeq_eq_of_isBlowupAlongIdealSheaf lB lI lowerBoundaryWithoutBlowup)
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (ofMarkedSequence ofMarkedSequence_center ofMarkedSequence_length toMarkedSequence_blowupMorphism toMarkedSequence_center toMarkedSequence_ideal toMarkedSequence_length)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (AdmissibleUnderBoundaryReplacement bget' boundary ideal isOrderBoundedByMult_iff mult nontrivialPart sameNontrivialBoundary_iff scheme structMap withSchemeIdealBoundary withSchemeIdealBoundary_ideal withSchemeIdealBoundary_mult)
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups (centersContainNoComponent_ofMarkedSequence ideal_zero isResolution_iff lastIdeal_eq nonzeroOnComponents_ideal_of_isAdmissible projectionToSpec_eq toSequenceOfBlowups)
open Ideal (eq_top_of_isUnit_mem mem_map_of_mem mul_le_right mul_mono pow_right_mono)
open Iso (hom hom_inv_id inv inv_hom_id refl refl_hom)
section
open Opposite
open FunctorialResolution.EmbeddedResolution (imageIdealSheaf_eq_comap_inv orderAtLeastLocus specMapOfFieldHom)
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence (strictTransformio)
open Scheme (Opens)


namespace FunctorialResolution.EmbeddedResolution

namespace EmbeddedBlowupSequence

variable {k : Type} [Field k] [CharZero k] {Y : Sch} [IsAffine Y]
  {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY]


def detachedToCoprod (T : EmbeddedBlowupSequence k Y pY) (s : ℕ) :
    ∀ (i : ℕ), s < i → (T.detachedScheme s ⟶ T.detachedCoprod i)
  | 0, h => absurd h $ not_lt_zero s
  | (i + 1), h =>
      if hs : s = i then
        eqToHom (congrArg T.detachedScheme hs) ≫
          (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i)
      else
        detachedToCoprod T s i (by omega) ≫
          (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i)

variable (S : EmbeddedBlowupSequence k Y pY)

section
variable (i : ℕ)
def detachedCoprodInl : S.detachedCoprod i ⟶ S.detachedCoprod (i + 1) :=
  (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i)


theorem inl_totalTransition_assoc {T : Sch} (g : S.totalSpace i ⟶ T) :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.totalTransition i ≫ g =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ g := by
  rw [← assoc, S.inl_totalTransition_eq_strictTransformMap_inl i, assoc]

theorem detachedCoprodInl_inr_totalTransition :
    S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i =
      (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) :=
  S.inl_inr_totalTransition i

def detachedCoprodInr : S.detachedScheme i ⟶ S.detachedCoprod (i + 1) :=
  (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i)

theorem detachedCoprod_succ_hom_ext {T : Sch}
    {f g : S.detachedCoprod (i + 1) ⟶ T}
    (hl : S.detachedCoprodInl i ≫ f = S.detachedCoprodInl i ≫ g)
    (hr : S.detachedCoprodInr i ≫ f = S.detachedCoprodInr i ≫ g) : f = g := by
  exact coprod.hom_ext hl hr

theorem detachedCoprodInr_eq :
    S.detachedCoprodInr i = (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) :=
  rfl

theorem detachedCoprodInr_inr_totalTransition :
    S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i =
      S.detachedio i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) :=
  S.inr_inr_totalTransition i

theorem inl_totalTransition :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.totalTransition i =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) :=
  S.inl_totalTransition_eq_strictTransformMap_inl i

theorem comapAmbientCenter_le_centerOffDetached :
    S.comapAmbientCenter i ≤ S.centerOffDetached i := by
  have h : S.centerOffDetached i =
      (cmI (S.comapAmbientCenter i) (S.detachedClosureCompl i).i).map (S.detachedClosureCompl i).i := rfl
  rw [h]
  exact mpr_ le_map_iff_comap_le le_rfl
end

section
variable {a b : ℕ} (h : a ≤ b)
def strictTransformMapOfLE : S.strictTransform b ⟶ S.strictTransform a :=
  leRec (motive := fun n _ => S.strictTransform n ⟶ S.strictTransform a)
    (𝟙 $ S.strictTransform a) (fun n _ f => S.strictTransformMap n ≫ f) h

def totalMapOfLE : S.totalSpace b ⟶ S.totalSpace a :=
  leRec (motive := fun n _ => S.totalSpace n ⟶ S.totalSpace a)
    (𝟙 $ S.totalSpace a) (fun n _ f => S.totalTransition n ≫ f) h

def detachedCoprodMapOfLE : S.detachedCoprod a ⟶ S.detachedCoprod b :=
  leRec (motive := fun n _ => S.detachedCoprod a ⟶ S.detachedCoprod n)
    (𝟙 $ S.detachedCoprod a) (fun n _ f => f ≫ S.detachedCoprodInl n) h

theorem detachedCoprodMapOfLE_succ :
    S.detachedCoprodMapOfLE (h.trans $ le_succ b) = S.detachedCoprodMapOfLE h ≫ S.detachedCoprodInl b := by
  exact leRec_succ ..
end

section
variable (T : EmbeddedBlowupSequence k Y pY) {a b} (h : a ≤ b) {h' : a ≤ b + 1}
theorem strictTransformMapOfLE_succ_of_le :
    T.strictTransformMapOfLE h' = T.strictTransformMap b ≫ T.strictTransformMapOfLE h := by
  exact leRec_succ ..

theorem totalMapOfLE_succ_of_le :
    T.totalMapOfLE h' = T.totalTransition b ≫ T.totalMapOfLE h := by
  exact leRec_succ ..

theorem detachedCoprodMapOfLE_succ_of_le :
    T.detachedCoprodMapOfLE h' = T.detachedCoprodMapOfLE h ≫ T.detachedCoprodInl b := by
  exact leRec_succ ..
end

section
variable (a : ℕ)
@[simp] theorem strictTransformMapOfLE_self :
    S.strictTransformMapOfLE (le_refl a) = 𝟙 (S.strictTransform a) := by
  exact leRec_self ..

@[simp] theorem totalMapOfLE_self :
    S.totalMapOfLE (le_refl a) = 𝟙 (S.totalSpace a) := by
  exact leRec_self ..

@[simp] theorem detachedCoprodMapOfLE_self :
    S.detachedCoprodMapOfLE (le_refl a) = 𝟙 (S.detachedCoprod a) := by
  exact leRec_self ..
end

section
variable {a b : ℕ} (h : a ≤ b)
theorem strictTransformMapOfLE_strictTransformio :
    S.strictTransformMapOfLE h ≫ strictTransformio S a = strictTransformio S b ≫ S.ambientSeq.transitionMap h := by
  induction b, h using le_induction with
  | base =>
      have e1 : S.strictTransformMapOfLE (m164 a) = 𝟙 (S.strictTransform a) := by simp_all
      have e2 : S.ambientSeq.transitionMap (m164 a) = 𝟙 (S.ambientSeq.schemeAt a) := by
        simp
      simp [id_comp, comp_id]
  | succ b hb ih =>
      have e2 : S.ambientSeq.transitionMap (le_succ_of_le hb)
          = S.ambientSeq.transitionMapSucc b ≫ S.ambientSeq.transitionMap hb := by
        rw [blowupMorphism_eq_transitionMap]
        exact sy_ $ transitionMap_trans S.ambientSeq hb $ le_succ b
      rw [strictTransformMapOfLE_succ_of_le S hb, e2, assoc, ih, ← assoc, S.strictTransformMap_comp_strictTransformio b]
      simp [assoc]

theorem totalMapOfLE_succ :
    S.totalMapOfLE (h.trans $ le_succ b) = S.totalTransition b ≫ S.totalMapOfLE h := by
  simp [totalMapOfLE, leRec_succ, h]

theorem inl_totalMapOfLE :
    (coprod.inl : S.strictTransform b ⟶ S.totalSpace b) ≫ S.totalMapOfLE h =
      S.strictTransformMapOfLE h ≫ (coprod.inl : S.strictTransform a ⟶ S.totalSpace a) := by
  induction b, h using le_induction with
  | base =>
      rw [S.totalMapOfLE_self a, S.strictTransformMapOfLE_self a, comp_id, id_comp]
  | succ b hb ih =>
      rw [totalMapOfLE_succ_of_le S hb, strictTransformMapOfLE_succ_of_le S hb,
        ← assoc, S.inl_totalTransition b, assoc, ih]
      simp [assoc]
end

section
variable (i : ℕ)
section
variable {T} (g : S.totalSpace i ⟶ T)
theorem detachedCoprodInl_inr_totalTransition_assoc :
    S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g =
      (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ g := by
  let _m0 := (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1))
  calc S.detachedCoprodInl i ≫ _m0 ≫
        S.totalTransition i ≫ g
      = (S.detachedCoprodInl i ≫ _m0 ≫
          S.totalTransition i) ≫ g := by simp only [assoc]
    _ = coprod.inr ≫ g := by rw [S.detachedCoprodInl_inr_totalTransition i]

theorem detachedCoprodInr_inr_totalTransition_assoc :
    S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g =
      S.detachedio i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ g := by
  let _m0 := (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1))
  calc S.detachedCoprodInr i ≫ _m0 ≫
        S.totalTransition i ≫ g
      = (S.detachedCoprodInr i ≫ _m0 ≫
          S.totalTransition i) ≫ g := by simp only [assoc]
    _ = (S.detachedio i ≫ coprod.inl) ≫ g := by rw [S.detachedCoprodInr_inr_totalTransition i]
    _ = S.detachedio i ≫ coprod.inl ≫ g :=
        assoc _ _ _
end

theorem detachedToCoprod_self :
    S.detachedToCoprod i (i + 1) (lt_succ_self i) = S.detachedCoprodInr i := by
  rw [detachedToCoprod]
  simp [detachedCoprodInr_eq]
end

theorem detachedToCoprod_succ_of_lt (s i : ℕ) (h : s < i) :
    S.detachedToCoprod s (i + 1) (lt_succ_of_lt h) = S.detachedToCoprod s i h ≫ S.detachedCoprodInl i := by
  refine dif_neg ?_
  omega

section
variable (W : EmbeddedBlowupSequence k Y pY)
theorem detachedCoprod_hom_ext_forall :
    ∀ (i : ℕ) (Z : Sch) (f g : W.detachedCoprod i ⟶ Z),
      (∀ s (hs : s < i), W.detachedToCoprod s i hs ≫ f = W.detachedToCoprod s i hs ≫ g) → f = g := by
  intro i
  induction i with
  | zero =>
      intro Z f g _
      exact initialIsInitial.hom_ext f g
  | succ i ih =>
      intro Z f g hf
      refine W.detachedCoprod_succ_hom_ext i ?_ ?_
      refine ih Z (W.detachedCoprodInl i ≫ f) (W.detachedCoprodInl i ≫ g) ?_
      intro s hs
      have h := hf s $ lt_succ_of_lt hs
      rw [W.detachedToCoprod_succ_of_lt s i hs] at h
      simp at h
      exact h
      have h := hf i $ lt_succ_self i
      rwa [W.detachedToCoprod_self i] at h

theorem detachedToCoprod_inr_totalMapOfLE_forall :
    ∀ b a s hab has hsb,
      W.detachedToCoprod s b hsb ≫ (coprod.inr : W.detachedCoprod b ⟶ W.totalSpace b) ≫ W.totalMapOfLE hab =
        W.detachedio s ≫ W.strictTransformMapOfLE has ≫ (coprod.inl : W.strictTransform a ⟶ W.totalSpace a) := by
  intro b
  induction b with
  | zero => exact fun a s _ _ hsb => absurd hsb $ not_lt_zero s
  | succ b ih =>
      intro a s hab has hsb
      by_cases h : s = b
      subst h
      rw [W.detachedToCoprod_self s, W.totalMapOfLE_succ has, W.detachedCoprodInr_inr_totalTransition_assoc s $ W.totalMapOfLE has,
        W.inl_totalMapOfLE has]
      have hsb' := lt_of_le_of_ne (lt_succ_iff.mp hsb) h
      have hab' := has.trans hsb'.le
      rw [W.detachedToCoprod_succ_of_lt s b hsb', W.totalMapOfLE_succ hab', assoc,
        W.detachedCoprodInl_inr_totalTransition_assoc b $ W.totalMapOfLE hab']
      exact ih a s hab' has hsb'
end

theorem exists_iso_coprod_of_isInitial {A B : Sch} (hB : IsInitial B) :
    ∃ u : A ≅ A ⨿ B, hom u = (coprod.inl : A ⟶ A ⨿ B) := by
  let _c0 := (coprod.inl : A ⟶ A ⨿ B)
  let _a0 := coprod.desc (𝟙 A) $ hB.to A
  let _a1 := coprod.inl_desc (𝟙 A) $ hB.to A
  refine ⟨⟨_c0, _a0,
    _a1, ?_⟩, rfl⟩
  refine coprod.hom_ext ?_ $ hB.hom_ext _ _
  calc _c0 ≫ _a0 ≫ _c0
      = (_c0 ≫ _a0) ≫
          _c0 := sy_ $ assoc _ _ _
    _ = 𝟙 A ≫ _c0 :=
        congrArg (fun t => t ≫ _c0) _a1
    _ = _c0 := id_comp _
    _ = _c0 ≫ 𝟙 (A ⨿ B) := sy_ $ comp_id _

theorem exists_iso_of_coprodIso_of_isInitial {A B Z : Sch} (hB : IsInitial B)
    (w : A ⨿ B ≅ Z) :
    ∃ e : A ≅ Z, hom e = (coprod.inl : A ⟶ A ⨿ B) ≫ hom w := by
  obtain ⟨u, hu⟩ := exists_iso_coprod_of_isInitial (A := A) (B := B) hB
  refine ⟨u ≪≫ w, ?_⟩
  show isoH u ≫ isoH w = coprod.inl ≫ isoH w
  exact congrArg (fun t => t ≫ isoH w) hu

theorem comp_inv_comp_hom_cancel {A B C D E : Sch} (f : A ⟶ B) (g : B ⟶ C)
    (h : C ⟶ E) (i : D ≅ E) :
    (f ≫ g ≫ (h ≫ inv i)) ≫ hom i = (f ≫ g) ≫ h :=by simp_all
theorem exists_strictTransformZeroIso :
    ∃ e : S.strictTransform 0 ≅ Y, hom e ≫ S.emb = strictTransformio S 0 ≫ S.ambientSeq.isoZero.hom := by
  obtain ⟨e, he⟩ := exists_iso_of_coprodIso_of_isInitial (A := S.strictTransform 0)
    (B := S.detachedCoprod 0) (Z := Y) initialIsInitial S.totalSpaceZeroIso
  refine ⟨e, ?_⟩
  let _a0 := coprod.inl ≫ S.totalSpaceZeroIso.hom
  calc isoH e ≫ S.emb
      = _a0 ≫ S.emb :=
        congrArg (fun t => t ≫ S.emb) he
    _ = (_a0 ≫
          (S.emb ≫ S.ambientSeq.isoZero.inv)) ≫ S.ambientSeq.isoZero.hom :=
        (comp_inv_comp_hom_cancel coprod.inl
          S.totalSpaceZeroIso.hom S.emb S.ambientSeq.isoZero).symm
    _ = strictTransformio S 0 ≫ S.ambientSeq.isoZero.hom :=
        congrArg (fun t => t ≫ S.ambientSeq.isoZero.hom) S.totalSpaceZeroIso_spec

def strictTransformZeroIso : S.strictTransform 0 ≅ Y := S.exists_strictTransformZeroIso.choose

def strictTransformToBase (i : ℕ) : S.strictTransform i ⟶ Y :=
  S.strictTransformMapOfLE (Nat.zero_le i) ≫ S.strictTransformZeroIso.hom

theorem detachedCoprod_hom_ext (i : ℕ) {T : Sch} {f g : S.detachedCoprod i ⟶ T}
    (hf : ∀ s (hs : s < i), S.detachedToCoprod s i hs ≫ f = S.detachedToCoprod s i hs ≫ g) : f = g :=
  detachedCoprod_hom_ext_forall S i T f g hf

theorem strictTransformZeroIso_hom_emb :
    S.strictTransformZeroIso.hom ≫ S.emb = strictTransformio S 0 ≫ S.ambientSeq.isoZero.hom :=
  S.exists_strictTransformZeroIso.choose_spec

theorem totalSpaceZeroIso_inv_eq :
    S.totalSpaceZeroIso.inv =
      S.strictTransformZeroIso.inv ≫ (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) := by
  let _a0 := S.emb ≫ S.ambientSeq.isoZero.inv
  have h2 : S.strictTransformZeroIso.hom ≫ _a0 = strictTransformio S 0 := by
    rw [← assoc, S.strictTransformZeroIso_hom_emb, assoc, hom_inv_id,
      comp_id]
  have h3 : coprod.inl ≫ S.totalSpaceZeroIso.hom =
      S.strictTransformZeroIso.hom := by
    refine mp_ (cancel_mono _a0) ?_
    rw [assoc, S.totalSpaceZeroIso_spec, h2]
  refine mp_ (cancel_mono S.totalSpaceZeroIso.hom) ?_
  rw [inv_hom_id, assoc, h3, inv_hom_id]

theorem inl_totalSpaceZeroIso_hom :
    (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom =
      S.strictTransformZeroIso.hom := by
  have h : S.strictTransformZeroIso.hom ≫ S.totalSpaceZeroIso.inv =
      coprod.inl := by
    rw [S.totalSpaceZeroIso_inv_eq, ← assoc, hom_inv_id, id_comp]
  rw [← h, assoc, inv_hom_id, comp_id]

theorem hom_comp_base_apply {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C)
    (x : ↥A) : ⇑(f ≫ g).base x = ⇑g.base (⇑f.base x) := rfl

theorem strictTransformToBase_emb i :
    S.strictTransformToBase i ≫ S.emb = strictTransformio S i ≫ S.ambientSeq.projectionToBase i := by
  have h1 : S.strictTransformToBase i = S.strictTransformMapOfLE (m67 i) ≫ S.strictTransformZeroIso.hom := rfl
  rw [h1, assoc, S.strictTransformZeroIso_hom_emb, ← assoc,
    S.strictTransformMapOfLE_strictTransformio $ m67 i, assoc, projectionToBase_def S.ambientSeq i]

theorem support_centerOffDetached_subset_preimage (i : ℕ) :
    (support (S.centerOffDetached i) : Set ↥(S.strictTransform i)) ⊆
      ⇑(strictTransformio S i).base ⁻¹' ((S.ambientCenter i).support : CSet $ schemeAt S i) := by
  let _a2 := S.centerOffDetached i
  let _a0 := _a2.subschemeMap (S.ambientCenter i) (strictTransformio S i) (mpr_ le_map_iff_comap_le $ S.comapAmbientCenter_le_centerOffDetached i) ≫ siI (S.ambientCenter i)
  let _a1 := siI _a2 ≫ strictTransformio S i
  have hu : _a0 =
      _a1 :=
    subschemeMap_subschemeι ..
  intro x hx
  rw [← q5] at hx
  obtain ⟨z, rfl⟩ := hx
  have key : _a0.base z =
      _a1.base z := by
    rw [hu]
  rw [hom_comp_base_apply, hom_comp_base_apply] at key
  rw [← q5]
  exact ⟨_, key⟩

theorem detachedToCoprod_inr_totalMapOfLE {a b s} (hab : a ≤ b) (has : a ≤ s) (hsb : s < b) :
    S.detachedToCoprod s b hsb ≫ (coprod.inr : S.detachedCoprod b ⟶ S.totalSpace b) ≫ S.totalMapOfLE hab =
      S.detachedio s ≫ S.strictTransformMapOfLE has ≫ (coprod.inl : S.strictTransform a ⟶ S.totalSpace a) :=
  detachedToCoprod_inr_totalMapOfLE_forall S b a s hab has hsb

theorem detachedToCoprod_detachedCoprodMapOfLE {s a b} (hsa : s < a) (hab : a ≤ b) :
    S.detachedToCoprod s a hsa ≫ S.detachedCoprodMapOfLE hab = S.detachedToCoprod s b (lt_of_lt_of_le hsa hab) := by
  let _a0 := S.detachedToCoprod s a hsa
  induction b, hab using le_induction with
  | base =>
      exact m32
        (congrArg (fun t => _a0 ≫ t)
          (S.detachedCoprodMapOfLE_self a))
        (comp_id _)
  | succ b hb ih =>
      calc _a0 ≫ S.detachedCoprodMapOfLE (le_succ_of_le hb)
          = _a0 ≫ (S.detachedCoprodMapOfLE hb ≫ S.detachedCoprodInl b) :=
            congrArg
              (fun t : S.detachedCoprod a ⟶ S.detachedCoprod (b + 1) => _a0 ≫ t) $ detachedCoprodMapOfLE_succ_of_le S hb
        _ = (_a0 ≫ S.detachedCoprodMapOfLE hb) ≫ S.detachedCoprodInl b :=
            (assoc _ _ _).symm
        _ = S.detachedToCoprod s b (lt_of_lt_of_le hsa hb) ≫ S.detachedCoprodInl b :=
            congrArg (fun t => t ≫ S.detachedCoprodInl b) ih
        _ = S.detachedToCoprod s (b + 1) (lt_of_lt_of_le hsa $ le_succ_of_le hb) :=
            (S.detachedToCoprod_succ_of_lt s b $ lt_of_lt_of_le hsa hb).symm

theorem detachedCoprodMapOfLE_inr_totalMapOfLE {a b} (hab : a ≤ b) :
    S.detachedCoprodMapOfLE hab ≫ (coprod.inr : S.detachedCoprod b ⟶ S.totalSpace b) ≫ S.totalMapOfLE hab =
      (coprod.inr : S.detachedCoprod a ⟶ S.totalSpace a) := by
  induction b, hab using le_induction with
  | base =>
      rw [S.detachedCoprodMapOfLE_self a, S.totalMapOfLE_self a, id_comp, comp_id]
  | succ b hb ih =>
      rw [detachedCoprodMapOfLE_succ_of_le S hb, totalMapOfLE_succ_of_le S hb, assoc,
        S.detachedCoprodInl_inr_totalTransition_assoc b $ S.totalMapOfLE hb, ih]

end EmbeddedBlowupSequence

variable {k : Type} [Field k] [CharZero k] {Y : Sch} [IsAffine Y]
  {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY]

section
variable (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups)
theorem inducedBlowups_blowupMorphism i :
    transitionMapSucc (S.inducedBlowups h) i = S.totalTransition i := by
  rw [blowupMorphism_eq_transitionMap (S.inducedBlowups h) i, transitionMap_def (S.inducedBlowups h) $ le_succ i]
  exact S.totalTower_map_succ i

theorem inducedBlowups_transitionMap {a b}
    (hab : a ≤ b) : transitionMap (S.inducedBlowups h) hab = S.totalMapOfLE hab := by
  induction b, hab using le_induction with
  | base =>
      exact tr_ ((transitionMap_def (S.inducedBlowups h) $ m164 a).trans $ (S.inducedBlowups h).tower.map_id $ op a) (S.totalMapOfLE_self a).symm
  | succ b hb ih =>
      refine tr_ (tr_ ((transitionMap_trans (S.inducedBlowups h) hb $ le_succ b).symm) ?_) (S.totalMapOfLE_succ hb).symm
      rw [st_ (blowupMorphism_eq_transitionMap (S.inducedBlowups h) b) $ inducedBlowups_blowupMorphism S h b, ih]
      exact rfl

theorem detachedToCoprod_inr_inducedBlowups_projectionToBase
    s i (hs : s < i) :
    S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
        projectionToBase (S.inducedBlowups h) i =
      S.detachedio s ≫ S.strictTransformToBase s := by
  calc S.detachedToCoprod s i hs ≫ coprod.inr ≫
        projectionToBase (S.inducedBlowups h) i
      = (S.detachedToCoprod s i hs ≫ coprod.inr ≫
          S.totalMapOfLE (m67 i)) ≫ S.totalSpaceZeroIso.hom := by
        rw [m32 (projectionToBase_def (S.inducedBlowups h) i) $ congrArg (fun t : S.totalSpace i ⟶ S.totalSpace 0 => t ≫ S.totalSpaceZeroIso.hom) $ inducedBlowups_transitionMap S h $ m67 i]
        simp only [assoc]
    _ = (S.detachedio s ≫ S.strictTransformMapOfLE (m67 s) ≫
          coprod.inl) ≫ S.totalSpaceZeroIso.hom := by
        rw [S.detachedToCoprod_inr_totalMapOfLE (m67 i) (m67 s) hs]
    _ = S.detachedio s ≫ S.strictTransformMapOfLE (m67 s) ≫
          (coprod.inl ≫ S.totalSpaceZeroIso.hom) := by
        simp only [assoc]
    _ = S.detachedio s ≫ S.strictTransformMapOfLE (m67 s) ≫ S.strictTransformZeroIso.hom := by
        rw [S.inl_totalSpaceZeroIso_hom]
    _ = S.detachedio s ≫ S.strictTransformToBase s := rfl

theorem inl_inducedBlowups_projectionToBase i :
    (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ projectionToBase (S.inducedBlowups h) i =
      S.strictTransformToBase i := by
  let _a1 := (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)
  let _a2 := S.strictTransformMapOfLE $ m67 i
  let _a0 := (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
  calc _a0 ≫ projectionToBase (S.inducedBlowups h) i
      = (_a0 ≫ S.totalMapOfLE (m67 i)) ≫
          S.totalSpaceZeroIso.hom := by
        rw [m32 (projectionToBase_def (S.inducedBlowups h) i) $ congrArg (fun t : S.totalSpace i ⟶ S.totalSpace 0 => t ≫ S.totalSpaceZeroIso.hom) $ inducedBlowups_transitionMap S h $ m67 i]
        simp [assoc]
    _ = (_a2 ≫ _a1) ≫
          S.totalSpaceZeroIso.hom := by
        rw [S.inl_totalMapOfLE $ m67 i]
    _ = _a2 ≫
          (_a1 ≫ S.totalSpaceZeroIso.hom) :=
        assoc _ _ _
    _ = _a2 ≫ S.strictTransformZeroIso.hom := by
        rw [S.inl_totalSpaceZeroIso_hom]
    _ = S.strictTransformToBase i := rfl
end

end FunctorialResolution.EmbeddedResolution

end
section

namespace FunctorialResolution.EmbeddedResolution

theorem isNoetherian_of_locallyOfFiniteType {X Y : Sch} (f : X ⟶ Y)
    [IsNoetherian Y] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    IsNoetherian X := by
  have :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  constructor

theorem isNoetherian_of_iso {X Y : Sch} (e : X ≅ Y)
    [IsNoetherian X] :
    IsNoetherian Y := by
  have : LocallyOfFiniteType e.inv := inferInstance
  have : QuasiCompact e.inv := inferInstance
  exact isNoetherian_of_locallyOfFiniteType e.inv

theorem isNoetherian_of_isBlowupAlongIdealSheaf {X X' : Sch} [IsNoetherian X]
    {pi_ : X' ⟶ X} {I : ISD X} (h : IsBlowupAlongIdealSheaf pi_ I) :
    IsNoetherian X' := by
  have := blowupIsProper X X' pi_ I h
  have : LocallyOfFiniteType pi_ := inferInstance
  have : QuasiCompact pi_ := inferInstance
  exact isNoetherian_of_locallyOfFiniteType pi_

instance instIsNoetherianAffineSpaceIdx (k : Type) [Field k] (n : Type) [Finite n] :
    IsNoetherian $ affineSpaceIndexedBy k n := by
  have : IsNoetherianRing ↑(CommRingCat.of (MvPolynomial n k)) :=
    inferInstanceAs $ IsNoetherianRing $ MvPolynomial n k
  have : IsNoetherian
      (Spec $ CommRingCat.of (MvPolynomial n k)) := inferInstance
  exact isNoetherian_of_iso
    (AlgebraicGeometry.AffineSpace.SpecIso n $ CommRingCat.of k).symm

theorem isNoetherian_schemeAt {X : Sch} (B : SequenceOfBlowups X)
    [IsNoetherian X] (i : ℕ) (hi : i ≤ B.length) :
    IsNoetherian $ schemeAt B i := by
  revert hi
  induction i with
  | zero =>
    intro _
    exact isNoetherian_of_iso B.isoZero.symm
  | succ n ih =>
    intro hi
    have hn := hi
    exact @isNoetherian_of_isBlowupAlongIdealSheaf (sbAt B n) (sbAt B $ n + 1) (ih $ le_of_lt hn) _ _
      (B.isBlowupAlongIdealSheaf_blowupMorphism n hn)


theorem isNoetherian_ambientLevel {k : Type} [Field k] [CharZero k] {Y}
    [IsAffine Y] {pY}
    [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) i
    (hi : i ≤ S.ambientLength) :
    IsNoetherian $ S.ambientLevel i := by
  revert hi
  induction i with
  | zero =>
    intro _
    have :=
      instIsNoetherianAffineSpaceIdx k $ ULift $ Fin S.dim
    exact isNoetherian_of_iso S.ambientBlowups.isoZero.symm
  | succ n ih =>
    intro hi
    have hn := hi
    exact @isNoetherian_of_isBlowupAlongIdealSheaf (S.ambientLevel n) (S.ambientLevel $ n + 1) (ih $ le_of_lt hn) _ _
      (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

theorem embeddedPrincipalizationAmbientIsNoetherian A (hemb : AffineEmbedsIntoAffineSpace)
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth) :
    EmbeddedPrincipalizationAmbientIsNoetherian A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  exact isNoetherian_ambientLevel (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) i hi




theorem blowupPreservesNoetherian : BlowupPreservesNoetherian := by
  repeat intro _
  rename_i h
  exact isNoetherian_of_isBlowupAlongIdealSheaf h

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme)
def canonicalAlgorithmRules : PrincipalizationRules where
  divisorRed := fun T alg j =>
    divisorReductionSeq hres blowupPreservesNoetherian T alg j
  maxOrderRed := fun T rc => orderReductionSeq comapIsoInvariance T rc
  orderRed := fun T rc => MaxContactReduction.reduceOrder comapIsoInvariance T rc

def canonicalPrincipalization
    (hrad : SmoothSubschemeIdealIsRadical) : PrincipalizationAlgorithm :=
  (canonicalAlgorithmRules hres).principalization hrad

theorem isFunctorialPrincipalization_canonicalPrincipalization
    (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical)
    (hemb : CommutesWithClosedImmersion $ canonicalAlgorithmRules hres) :
    IsFunctorialPrincipalization $ canonicalPrincipalization hres hrad :=
  PrincipalizationRules.isFunctorialPrincipalization_principalization (canonicalAlgorithmRules hres) hB hrad hemb
end





section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) {X Y S S'} (ι) (io') (h : Y ⟶ X) (h' : S' ⟶ S) [IsClosedImmersion ι] [IsClosedImmersion io'] [Flat h] [IsNoetherian X] [IsNoetherian Y] (hsq : IsPullback io' h' h ι) (s : BlowupSequenceData S) (s' : BlowupSequenceData S') (hs : s.CentersContainNoComponent) (hs' : s'.CentersContainNoComponent)
include hsq
theorem isStrictPullbackBlowupSeq_ambientBlowupSequence_of_flat
    (hpb : IsStrictPullbackBlowupSeq h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq h (ambientBlowupSequence io' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  let _c0 := (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups
  have hstrict :=
    isStrictPullbackSequenceOfBlowups_baseChange _c0 h
  have hN : ∀ i, i ≤ _c0.length →
      IsLocallyNoetherian (sbAt _c0 i) := by
    intro i hi
    have : IsNoetherian $ sbAt _c0 i :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  let _a0 := _c0.baseChange h
  have hN' : ∀ i, i ≤ _a0.length →
      IsLocallyNoetherian
        (sbAt _a0 i) := by
    intro i hi
    have :=
      isNoetherian_schemeAt
        (_c0.baseChange h) i hi
    infer_instance
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback hstrict $ IsPushforwardBlowupSeq.isomorphic io' (IsPushforwardBlowupSeq.of_flat_isPullback ι io' h h' hsq s.toSequenceOfBlowups _c0 s'.toSequenceOfBlowups (_c0.baseChange h) hN hN' (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hpb hstrict) $ isPushforwardBlowupSeq_ambientBlowupSequence io' s' hres hno hs'

theorem isPullbackBlowupSequence_ambientBlowupSequence_of_flat
    (hpb : IsPullbackBlowupSequence h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsPullbackBlowupSequence h (ambientBlowupSequence io' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  let _c0 := (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups
  have : Flat h' := by
    rw [← hsq.isoPullback_hom_snd]
    infer_instance
  have hUstrict :=
    isStrictPullbackSequenceOfBlowups_baseChange s.toSequenceOfBlowups h'
  have hstrict :=
    isStrictPullbackSequenceOfBlowups_baseChange _c0 h
  have hN : ∀ i, i ≤ _c0.length →
      IsLocallyNoetherian (sbAt _c0 i) := by
    intro i hi
    have : IsNoetherian $ sbAt _c0 i :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  let _a0 := _c0.baseChange h
  have hN' : ∀ i, i ≤ _a0.length →
      IsLocallyNoetherian
        (sbAt _a0 i) := by
    intro i hi
    have :=
      isNoetherian_schemeAt
        (_c0.baseChange h) i hi
    infer_instance
  exact IsPullbackBlowupSequence.of_isomorphic hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups $ IsPushforwardBlowupSeq.isomorphic io' (IsPushforwardBlowupSeq.of_isomorphic_source io' (IsPullbackBlowupSequence.isomorphic hUstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups hpb) $ isPushforwardSequenceOfBlowups_withoutIsoBlowups io' (s.toSequenceOfBlowups.baseChange h') (_c0.baseChange h) hN' $ IsPushforwardBlowupSeq.of_flat_isPullback ι io' h h' hsq s.toSequenceOfBlowups _c0 (s.toSequenceOfBlowups.baseChange h') (_c0.baseChange h) hN hN' (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hUstrict hstrict) $ isPushforwardBlowupSeq_ambientBlowupSequence io' s' hres hno hs'
end

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution


namespace IdealBlowupSequence

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {E : Bdy X}

section
variable (s : IdealBlowupSequence p I E)
theorem structureMorphism_zero :
    s.structureMorphism 0 = s.toSequenceOfBlowups.isoZero.hom ≫ p := by
  rw [structureMorphism_def, SequenceOfBlowups.projectionToBase_zero]

theorem structureMorphism_succ i :
    s.structureMorphism (i + 1) = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.structureMorphism i := by
  rw [structureMorphism_def, structureMorphism_def, blowupMorphism_eq_transitionMap, ← assoc,
    transitionMap_comp_projectionToBase]
end

theorem smooth_structureMorphism [Smooth p] (s : IdealBlowupSequence p I E) i
    (hi : i ≤ s.toSequenceOfBlowups.length) :
    Smooth $ s.structureMorphism i := by
  revert hi
  induction i with
  | zero =>
    intro _
    rw [structureMorphism_zero]
    infer_instance
  | succ n ih =>
    intro hi
    have hn := hi
    have := ih $ le_of_lt hn
    rw [structureMorphism_succ]
    exact smooth_comp_of_isBlowupAlongIdealSheaf (s.hasStrictNormalCrossingsWith_center n hn)
      (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)


theorem isNoetherian_schemeAt [IsNoetherian X] (s : IdealBlowupSequence p I E) (i : ℕ)
    (hi : i ≤ s.toSequenceOfBlowups.length) :
    IsNoetherian $ s.toSequenceOfBlowups.schemeAt i :=
  EmbeddedResolution.isNoetherian_schemeAt s.toSequenceOfBlowups i hi


end IdealBlowupSequence





namespace MarkedSequenceOfBlowups

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (s : MarkedSequenceOfBlowups p I m E)
theorem projectionToBase_zero :
    s.toSequenceOfBlowups.projectionToBase 0 = s.toSequenceOfBlowups.isoZero.hom := by
  have h0 : s.toSequenceOfBlowups.transitionMap (le_refl 0) = 𝟙 (msAt s 0) := by simp_all
  rw [projectionToBase_def, h0, id_comp]

section
variable (i : ℕ)
theorem projectionToBase_succ_apply
    x :
    (s.toSequenceOfBlowups.projectionToBase $ i + 1).base x =
      (s.toSequenceOfBlowups.projectionToBase i).base ((s.toSequenceOfBlowups.transitionMapSucc i).base x) := by
  have h : s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i =
      s.toSequenceOfBlowups.projectionToBase (i + 1) := by
    rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i]
    exact s.toSequenceOfBlowups.transitionMap_comp_projectionToBase $ le_succ i
  rw [← h]
  rfl

theorem comap_ideal_le_ideal_succ
    (hi : i < s.toSequenceOfBlowups.length) :
    (s.ideal i).comap (s.toSequenceOfBlowups.transitionMapSucc i) ≤ s.ideal (i + 1) := by
  rw [← s.ideal_succ i hi]
  exact fun U => mul_le_right

theorem support_ideal_succ_subset_preimage
    (hi : i < s.toSequenceOfBlowups.length) :
    ((support (s.ideal $ i + 1) : Set ↥(s.toSequenceOfBlowups.schemeAt $ i + 1))) ⊆
      ⇑(s.toSequenceOfBlowups.transitionMapSucc i).base ⁻¹'
        ((support (s.ideal i) : CSet $ s.toSequenceOfBlowups.schemeAt i)) := by
  exact subset_trans (SetLike.coe_subset_coe.mpr
    (support_antitone $ s.comap_ideal_le_ideal_succ i hi)) $ (support_comap _ _).le
end
end

end MarkedSequenceOfBlowups

theorem MarkedIdealWithBoundary.IsAdmissible.isNoetherian {T : MarkedIdealWithBoundary} (hV : T.IsAdmissible) :
    IsNoetherian T.scheme := by
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have : IsNoetherian $ Sp T.base := inferInstance
  exact isNoetherian_of_locallyOfFiniteType T.structMap




theorem inStrictNormalCrossingPosition_comap_iso {k : Type} [Field k] {X Y : Sch}
    (q : Y ⟶ Sp k) (e : X ≅ Y) (L : Bdy Y)
    (h : InStrictNormalCrossingPosition q L) :
    InStrictNormalCrossingPosition (hom e ≫ q) $ L.map fun D => D.comap e.hom := by
  rw [inStrictNormalCrossingPosition_iff] at h ⊢
  constructor
  intro D hD
  rw [mem_map] at hD
  obtain ⟨D', hD', rfl⟩ := hD
  exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso q e D' $ an1 h D' hD'
  intro x
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := an2 h $ ihB_ e x
  refine ⟨(m54 $ ihB_ e).obj U, hxU, m,
    EtaleChart.ofIso q e c, a, ?_, ?_, ?_⟩
  intro i hi j hj t hti htj
  exact hinj i (by simpa using hi) j (by simpa using hj) t hti htj
  intro i hi ha
  have hi' : i < lenL L := by simpa using hi
  simp [getElem_map]
  rw [restrictIdeal_comap, hnone i hi' ha, comap_top]
  intro i hi t ht
  have hi' : i < lenL L := by simpa using hi
  simp [getElem_map]
  rw [restrictIdeal_comap, hsome i hi' t ht, EtaleChart.ofIso_coordIdeal]

namespace MarkedSequenceOfBlowups

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (s : MarkedSequenceOfBlowups p I m E)
theorem projectionToSpec_zero :
    s.projectionToSpec 0 = s.toSequenceOfBlowups.isoZero.hom ≫ p := by
  rw [projectionToSpec_eq, MarkedSequenceOfBlowups.projectionToBase_zero]

theorem projectionToSpec_succ (i : ℕ) :
    s.projectionToSpec (i + 1) = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.projectionToSpec i := by
  have h : s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i
      = s.toSequenceOfBlowups.projectionToBase (i + 1) := by
    rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i]
    exact s.toSequenceOfBlowups.transitionMap_comp_projectionToBase $ le_succ i
  rw [projectionToSpec_eq, projectionToSpec_eq, ← h, assoc]
end

theorem isNoetherian_schemeAt (_hcart : EffectiveCartierSupportContainsNoComponent) {T : MarkedIdealWithBoundary}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    IsNoetherian $ s.toSequenceOfBlowups.schemeAt i := by
  induction i with
  | zero =>
      have := hT.isNoetherian
      exact isNoetherian_of_iso s.toSequenceOfBlowups.isoZero.symm
  | succ n ih =>
      have hn := hi
      have := ih $ le_of_lt hn
      exact isNoetherian_of_isBlowupAlongIdealSheaf $ s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn

end MarkedSequenceOfBlowups

theorem smooth_and_inStrictNormalCrossingPosition_projectionToSpec (hcart : EffectiveCartierSupportContainsNoComponent) {T : MarkedIdealWithBoundary}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    ∀ i : ℕ, i ≤ s.toSequenceOfBlowups.length →
      Smooth (s.projectionToSpec i) ∧ InStrictNormalCrossingPosition (s.projectionToSpec i) (s.boundary i) := by
  intro i
  induction i with
  | zero =>
      intro _
      have := hT.smooth
      constructor
      rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
      infer_instance
      rw [MarkedSequenceOfBlowups.projectionToSpec_zero, s.boundary_zero]
      exact inStrictNormalCrossingPosition_comap_iso T.structMap s.toSequenceOfBlowups.isoZero T.boundary hT.snc
  | succ n ih =>
      intro hn
      have hn' := hn
      obtain ⟨hsm, hsnc⟩ := ih $ le_of_lt hn'
      have := hsm
      have :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s (n + 1) hn
      have : m86 $ msAt s $ n + 1 := inferInstance
      have hpi_ := s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn'
      have hZE : HasStrictNormalCrossingsWith (s.projectionToSpec n) (msCtr s n) $ s.boundary n := by
        rw [projectionToSpec_eq]
        exact s.center_snc n hn'
      constructor
      rw [MarkedSequenceOfBlowups.projectionToSpec_succ]
      exact smooth_comp_of_isBlowupAlongIdealSheaf hZE hpi_
      rw [MarkedSequenceOfBlowups.projectionToSpec_succ, s.boundary_succ n hn']
      exact inStrictNormalCrossingPosition_strictTransform_append (s.projectionToSpec n) (msTrS s n)
        (msCtr s n) (s.boundary n) hpi_ hsnc hZE

namespace MarkedSequenceOfBlowups

section
variable (hcart : EffectiveCartierSupportContainsNoComponent) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i) (hi : i ≤ s.toSequenceOfBlowups.length)
include hcart hT hi
theorem smooth_projectionToSpec :
    Smooth $ s.projectionToSpec i :=
  (smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi).1

theorem inStrictNormalCrossingPosition_projectionToSpec_boundary :
    InStrictNormalCrossingPosition (s.projectionToSpec i) $ s.boundary i :=
  (smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi).2
end

end MarkedSequenceOfBlowups

def DimensionNonincreasingAlongBlowups : Prop :=
  ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
    krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc

namespace MarkedIdealWithBoundary

section
variable (T : MarkedIdealWithBoundary) (s : T.SequenceOfBlowups) (i : ℕ)
def transformAt : MarkedIdealWithBoundary where
  base := T.base
  instField := T.instField
  scheme := s.toSequenceOfBlowups.schemeAt i
  structMap := s.projectionToSpec i
  ideal := s.ideal i
  mult := mult T
  boundary := s.boundary i

@[simp]
theorem transformAt_baseField :
    (T.transformAt s i).base = T.base := rfl

@[simp]
theorem transformAt_scheme :
    scheme (T.transformAt s i) = s.toSequenceOfBlowups.schemeAt i := rfl

@[simp]
theorem transformAt_structureMorphism :
    structMap (T.transformAt s i) = s.projectionToSpec i := rfl

@[simp]
theorem transformAt_ideal :
    ideal (T.transformAt s i) = s.ideal i := rfl

@[simp]
theorem transformAt_mult :
    mult (T.transformAt s i) = mult T := rfl

@[simp]
theorem transformAt_boundary :
    boundary (T.transformAt s i) = s.boundary i := rfl

@[simp]
theorem transformAt_dim :
    (T.transformAt s i).krullDimSucc = EmbeddedResolution.krullDimSucc (s.toSequenceOfBlowups.schemeAt i) := rfl
end

theorem IsAdmissible.transformAt (hcart : EffectiveCartierSupportContainsNoComponent) {T : MarkedIdealWithBoundary}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    (T.transformAt s i).IsAdmissible := by
  obtain ⟨hsm, hsnc⟩ := smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi
  have :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s i hi
  have : m86 $ msAt s i := inferInstance
  refine
    { charZero := hT.charZero
      locallyOfFiniteType := ?_
      nonzeroOnComponents := nonzeroOnComponents_ideal_of_isAdmissible hcart hT s i hi
      one_le_mult := hT.one_le_mult
      quasiCompact := ?_
      smooth := hsm
      snc := hsnc }
  show LocallyOfFiniteType $ s.projectionToSpec i
  infer_instance
  show QuasiCompact $ s.projectionToSpec i
  exact ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩

theorem transformAt_dim_le (hdim : DimensionNonincreasingAlongBlowups) {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible)
    (s : T.SequenceOfBlowups) i (hi : i ≤ s.toSequenceOfBlowups.length) :
    (T.transformAt s i).krullDimSucc ≤ T.krullDimSucc :=
  hdim T hT s i hi

end MarkedIdealWithBoundary





theorem krullDimSucc_eq_krullDimSucc_of_iso {X Y : Sch} (e : X ≅ Y) :
    krullDimSucc X = krullDimSucc Y := by
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, topologicalKrullDim_eq_of_homeomorph $ TopCat.homeoOfIso $ Scheme.forgetToTop.mapIso e]

theorem dimensionNonincreasingAlongBlowups : DimensionNonincreasingAlongBlowups := by
  intro T hT s i
  induction i with
  | zero =>
      intro _
      exact le_of_eq $ krullDimSucc_eq_krullDimSucc_of_iso s.toSequenceOfBlowups.isoZero
  | succ n ih =>
      intro hi
      have hlt := hi
      have hn : n ≤ msLen s := m49 hlt
      have hvalid := MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hT s n hn
      have hft : LocallyOfFiniteType $ s.projectionToSpec n :=
        hvalid.locallyOfFiniteType
      have hqc : QuasiCompact $ s.projectionToSpec n :=
        hvalid.quasiCompact
      have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec n) (msCtr s n) $ s.boundary n := by
        rw [projectionToSpec_eq]
        exact s.center_snc n hlt
      exact le_trans (krullDimSucc_le_of_blowup_strictNormalCrossings (s.projectionToSpec n) (msTrS s n) (msCtr s n) (s.boundary n) hsnc $ s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt) $ ih hn

theorem nontrivialPart_eq_filterNeTop {X : Sch} (E : Bdy X) :
    nontrivialPart E = filterNeTop E := by
  unfold nontrivialPart filterNeTop
  apply filter_congr
  intro D _
  simp

namespace MarkedIdealWithBoundary

theorem validOfSameNontrivialBoundary : AdmissibleUnderBoundaryReplacement := by
  intro T E hV hEq
  have hsm := hV.smooth
  have h : filterNeTop T.boundary = filterNeTop E := by
    rw [← nontrivialPart_eq_filterNeTop, ← nontrivialPart_eq_filterNeTop]
    exact mp_ (sameNontrivialBoundary_iff T.boundary E) hEq
  exact ⟨hV.charZero, hV.locallyOfFiniteType, hV.nonzeroOnComponents, hV.one_le_mult,
    hV.quasiCompact, hV.smooth,
    inStrictNormalCrossingPosition_of_filterNeTop_eq T.structMap T.boundary E h hV.snc⟩

end MarkedIdealWithBoundary




def AdmissibilityStableUnderSmoothPullback : Prop :=
  ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (Y : Sch)
      (q : Y ⟶ Sp T.base) (h : Y ⟶ scheme T)
      [Smooth h] [QuasiCompact q],
      h ≫ structMap T = q → (T.pbA q h).IsAdmissible

theorem isAdmissible_pullbackAlong_of_smooth : AdmissibilityStableUnderSmoothPullback := by
  intro T hV Y q h hs hqc hq
  exact MarkedIdealWithBoundary.isAdmissible_pullbackAlong_of_smooth T hV Y q h hq

theorem maxOrderReduction_outputLevelData_eq_markedBlowupSeq (rules : PrincipalizationRules) (k : Type) [Field k]
    (X : Sch) (p : X ⟶ Sp k) (I : ISD X)
    (E : Bdy X) (N : ℕ) (h : krullDimSucc X ≤ N) :
    (rules.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E) = rules.markedBlowupSeq k X p I E :=
  rules.outputLevelData_maxOrderReduction_eq_at_dim (markedTripleOrderOne k X p I E) h

section
variable {X} (s : SequenceOfBlowups X)
private theorem ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic :
    (ofSequenceOfBlowups s).toSequenceOfBlowups.Isomorphic s := by
  refine ⟨rfl, fun i _ => refl _, id_comp _, ?_, ?_⟩
  intro i hi
  simp [toSequenceOfBlowups_blowupMorphism, ofSequenceOfBlowups_blowupMorphism, refl_hom]
  exact tr_ (id_comp $ sbTrS s i) (comp_id $ sbTrS s i).symm
  intro i hi
  exact comap_id _

private theorem isLocallyNoetherian_schemeAt
    [IsNoetherian X] (i : ℕ) (hi : i ≤ s.length) :
    IsLocallyNoetherian $ schemeAt s i := by
  have := isNoetherian_schemeAt s i hi
  infer_instance
end

theorem isPushforwardSequenceOfBlowups_congr_hom {S X : Sch} {f g : S ⟶ X}
    [IsClosedImmersion f] [IsClosedImmersion g]
    (h : f = g) {BS : SequenceOfBlowups S} {Bs : SequenceOfBlowups X}
    (hp : IsPushforwardBlowupSeq f BS Bs) : IsPushforwardBlowupSeq g BS Bs := by
  subst h
  exact hp

namespace MaximalContactCover

variable {X X' : Sch} {k : Type} [Field k] {p : X' ⟶ Sp k}
  {ta_ : X ⟶ X'} {I : ISD X} {c : ℕ}

section
variable [hv0_0 : LocallyOfFiniteType p] (C : MaximalContactCover p ta_ I c)
include hv0_0
theorem isNoetherian_disjointUnion :
    IsNoetherian C.toCoverData.disjointUnion :=
  isNoetherian_of_locallyOfFiniteType $ C.projection ≫ p


theorem isNoetherian_subscheme_iInfImageIdeal :
    IsNoetherian C.toCoverData.iInfImageIdeal.subscheme := by
  have := isNoetherian_disjointUnion C
  exact isNoetherian_of_locallyOfFiniteType C.toCoverData.iInfImageIdeal.si
end

end MaximalContactCover

def IsClosedEmbeddingCompatibleInCodim (rules : PrincipalizationRules) (c : ℕ) : Prop :=
  ∀ (k : Type) [Field k], CharZero k → ∀ (X X' : Sch)
    (p : X ⟶ Sp k) (p' : X' ⟶ Sp k) (j : X ⟶ X')
    [IsClosedImmersion j],
    Smooth p → LocallyOfFiniteType p →
    QuasiCompact p → Smooth p' →
    LocallyOfFiniteType p' → QuasiCompact p' →
    j ≫ p' = p → 1 ≤ c → HasEtaleCoordCodim p' j c →
    ∀ I : ISD X, NonzeroOnComponents I → NonzeroOnComponents (imageIdealSheaf j I) →
      IsPushforwardBlowupSeq j (rules.markedBlowupSeq k X p I []).toSequenceOfBlowups
        (rules.markedBlowupSeq k X' p' (imageIdealSheaf j I) []).toSequenceOfBlowups

theorem commutesWithClosedImmersion_forall_codim (rules : PrincipalizationRules) (hB : rules.ReducesInductivelyOnDimension)
    (hpv : AdmissibilityStableUnderSmoothPullback) : ∀ c : ℕ, IsClosedEmbeddingCompatibleInCodim rules c := by
  intro c
  induction c with
  | zero =>
      intro k _ _ X X' p p' j _ _ _ _ _ _ _ _ hc
      exact absurd hc (by omega)
  | succ c' ih =>
      intro k _ hcz X X' p p' j hji hsm hft hqc hsm' hft' hqc' hjp hc hcod I hI hIim
      have hNX := isNoetherian_of_locallyOfFiniteType p
      have hNX' := isNoetherian_of_locallyOfFiniteType p'
      have hvX :=
        markedTripleOrderOne_isAdmissible k X p I hI [] (inStrictNormalCrossingPosition_nil p)
      have hvX' :=
        markedTripleOrderOne_isAdmissible k X' p' (imageIdealSheaf j I) hIim [] (inStrictNormalCrossingPosition_nil p')
      rcases isEmpty_or_nonempty X with hXe | hXne
      have hIsub := Function.isEmpty I.si
      have himg : imageIdealSheaf j I = ⊤ := by
        rw [eq_top_iff_support_eq_empty, imageIdealSheaf_eq_ker j I,
          support_ker (siI I ≫ j), range_eq_empty, closure_empty]
      have hcs1 : orderAtLeastLocus I 1 = (∅) := eq_empty_of_isEmpty _
      have hcs2 : orderAtLeastLocus (imageIdealSheaf j I) 1 = (∅) := by
        rw [himg]
        exact orderAtLeastLocus_top_eq_empty 1 le_rfl
      have hspec := rules.isMaxOrderReduction_outputLevelData hB $ krullDimSucc X + krullDimSucc X'
      have h1 := hspec.trivial_of_coSupport_empty (markedTripleOrderOne k X p I []) hvX
        (show krullDimSucc X ≤ krullDimSucc X + krullDimSucc X' by omega) hcs1
      have h2 := hspec.trivial_of_coSupport_empty
        (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX'
        (show krullDimSucc X' ≤ krullDimSucc X + krullDimSucc X' by omega) hcs2
      rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X p I [] (krullDimSucc X + krullDimSucc X')
        (show krullDimSucc X ≤ krullDimSucc X + krullDimSucc X' by omega)] at h1
      rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X' p' (imageIdealSheaf j I) [] (krullDimSucc X + krullDimSucc X')
        (show krullDimSucc X' ≤ krullDimSucc X + krullDimSucc X' by omega)] at h2
      exact IsPushforwardBlowupSeq.of_length_eq_zero j _ _ h1 h2
      have hch : HasLocalEtaleCharts p' := by
        intro y
        obtain ⟨U, mm, hyU, haff, hne⟩ := exists_etaleChart p' y
        exact ⟨U, hyU, mm, hne⟩
      obtain ⟨C⟩ := nonempty_maximalContactCover p' j I (c' + 1) hc hcod hch
      have hNW :=
        MaximalContactCover.isNoetherian_disjointUnion C
      have hnoeth :=
        MaximalContactCover.isNoetherian_subscheme_iInfImageIdeal C
      have hNSW : m86 C.toCoverData.disjointUnion := inferInstance
      have hNSH : m86 C.hypersurfaceScheme := inferInstance
      have hsmH := C.smooth_hypersurfaceStructureMap
      have hsmP : Smooth C.projection := by
        rw [C.projection_eq]
        exact C.toCoverData.smooth_disjointUnionMap
      have hsuP := C.surjective_projection
      have hsmSB := C.smooth_pullbackFiberToBase
      have hsuSB := C.surjective_pullbackFiberToBase
      have hqcH : QuasiCompact C.hypersurfaceStructureMap := inferInstance
      have hqcWp := C.quasiCompact_projection_comp
      have hCI : IsClosedImmersion C.toCoverData.iInfImageIdeal.si :=
        inferInstance
      have hstarw := C.isPullback_pullbackFiber.w
      have hcompeq : C.pullbackFiberToBase ≫ p = C.pullbackFiberToTotal ≫ (C.projection ≫ p') := by
        rw [← hjp, ← assoc, hstarw, assoc]
      have hqcS : QuasiCompact (C.pullbackFiberToBase ≫ p) := by
        rw [hcompeq]
        infer_instance
      obtain ⟨x0⟩ := hXne
      have hNEs : Nonempty C.pullbackFiber := by
        obtain ⟨y, -⟩ := AlgebraicGeometry.Surjective.surj (f := C.pullbackFiberToBase) x0
        exact ⟨y⟩
      have hNEH : Nonempty C.hypersurfaceScheme := by
        obtain ⟨y⟩ := hNEs
        exact ⟨C.pullbackFiberToHypersurface.base y⟩
      have hHW :=
        C.krullDimSucc_hypersurfaceScheme_lt
      obtain ⟨m, hm⟩ : ∃ m, m = krullDimSucc X + krullDimSucc X'
          + krullDimSucc C.toCoverData.disjointUnion + krullDimSucc C.pullbackFiber
          + krullDimSucc C.hypersurfaceScheme := ⟨_, rfl⟩
      have hsmjp : Smooth (j ≫ p') := by
        rw [hjp]
        infer_instance
      have hkerNZ : NonzeroOnComponents (m149 j) := by
        refine nonzeroOnComponents_of_locally_eq_coordIdeal p' (m149 j)
          m169 ?_
        intro y hy
        have hsupp := support_ker j
        have hy' : y ∈ closure (range (j)) := by
          rwa [← hsupp]
        have hcl :=
          (isClosedEmbedding j).isClosed_range
        rw [hcl.closure_eq] at hy'
        obtain ⟨x, rfl⟩ := hy'
        obtain ⟨U, hxU, mm, ch, S, hcard, heq⟩ := hcod x
        exact ⟨U, hxU, mm, ch, S, Finset.card_pos.mp (by omega), heq⟩
      have horder : ∀ x, orderAt (imageIdealSheaf j I) x ≤ 1 := by
        intro x
        let ta_ := j
        refine le_trans (orderAt_le_of_le (ker_le_map_idealSheaf ta_ I) x) ?_
        by_cases hx : x ∈ ta_.ker.support
        have _i30 : Smooth (ta_.ker.si ≫ p') := by
          have hinv :=
            mpr_ (IsIso.inv_comp_eq _) ta_.toImage_imageι.symm
          have hcomp : ta_.ker.si ≫ p' = inv ta_.toImage ≫ (ta_ ≫ p') := by simp_all
          rw [hcomp]
          infer_instance
        obtain ⟨U, m, c, S, hxU, hU, hD⟩ :=
          exists_chart_restrictIdeal_eq_coordIdeal p' ta_.ker x hx
        have hD' : kCm ta_ U.i = c.coordIdeal S := hD
        rcases S.eq_empty_or_nonempty with hS | ⟨j, hj⟩
        subst hS
        exfalso
        have hUsupp : (U : Set X') ⊆ ta_.ker.supp := by
          intro y hy
          have hy' : y ∈ range U.ib := by
            rwa [q1]
          obtain ⟨z, rfl⟩ := hy'
          have h1 : z ∈ (spI (kCm ta_ U.i) : Set U.toScheme) := by
            rw [hD', p33, coordSubspaceIdeal_empty, support_comap_eq]
            simp [support_bot]
          rwa [support_comap_eq] at h1
        have hCmem :=
          irreducibleComponent_mem_irreducibleComponents x
        refine hkerNZ _ hCmem ?_
        have hcl := closure_inter_open_eq (isClosed_irreducibleComponent)
          (isIrreducible_irreducibleComponent) U.2 ⟨x, mem_irreducibleComponent, hxU⟩
        rw [← hcl]
        refine closure_minimal ?_ (ta_.ker.support).2
        exact fun y hy => hUsupp hy.2
        exact orderAt_le_one_of_restrictIdeal_eq_coordIdeal p' hU c S j hj ta_.ker hD x hxU
        have h0 := mpr_ (orderAt_eq_zero_iff_not_mem_support ta_.ker x) hx
        rw [h0]
        exact zero_le
      have hfacH : C.pullbackFiberToHypersurface ≫ C.hypersurfaceStructureMap = C.pullbackFiberToBase ≫ p := by
        show C.pullbackFiberToHypersurface ≫ (C.toCoverData.iInfImageIdeal.si ≫ C.projection ≫ p')
          = C.pullbackFiberToBase ≫ p
        rw [C.pullbackFiberToHypersurface_comp_subschemeio_assoc (C.projection ≫ p'), ← assoc, ← hstarw,
          assoc, hjp]
      have hWideal : (imageIdealSheaf j I).comap C.projection
          = imageIdealSheaf C.toCoverData.iInfImageIdeal.si C.idealOnHypersurface := by
        rw [← C.comapImageIdealSheaf_eq]
        exact C.comapImageIdealSheaf_eq_imageIdealSheaf_idealOnHypersurface
      have hHideal :=
        C.idealOnHypersurface_eq_imageIdealSheaf
      have hvW :=
        @hpv (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX' C.toCoverData.disjointUnion
          (C.projection ≫ p') C.projection hsmP hqcWp rfl
      have hvS :=
        @hpv (markedTripleOrderOne k X p I []) hvX C.pullbackFiber (C.pullbackFiberToBase ≫ p)
          C.pullbackFiberToBase hsmSB hqcS rfl
      have hNZS := hvS.nonzeroOnComponents
      have hcontactNZ : NonzeroOnComponents C.idealOnHypersurface := by
        rcases m73 c' with hc0 | hc1
        have hiso := C.isIso_pullbackFiberToHypersurface_of_eq_one (by omega)
        have hinv :=
          imageIdealSheaf_eq_comap_inv C.pullbackFiberToHypersurface (cmI I C.pullbackFiberToBase)
        have h2 :=
          nonzeroOnComponents_comap_iso_hom (asIso C.pullbackFiberToHypersurface).symm
            (cmI I C.pullbackFiberToBase) hNZS
        rwa [hHideal, hinv]
        have hcc0 :=
          C.hasEtaleCoordCodim_pullbackFiberToHypersurface
        refine C.nonzeroOnComponents_idealOnHypersurface ?_
        intro x
        obtain ⟨U, hxU, mm, ch, S, hcard, heq⟩ := hcc0 x
        exact ⟨U, hxU, mm, ch, S, Finset.card_pos.mp (by omega), heq⟩
      have hvH :=
        markedTripleOrderOne_isAdmissible k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface hcontactNZ []
          (inStrictNormalCrossingPosition_nil C.hypersurfaceStructureMap)
      have hspec := rules.isMaxOrderReduction_outputLevelData hB $ m + 1
      have hordspec := rules.isOrderReduction_outputLevelData hB $ m + 1
      have hpushFiber : IsPushforwardBlowupSeq C.pullbackFiberToHypersurface
          (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (cmI I C.pullbackFiberToBase) []).toSequenceOfBlowups
          (rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []).toSequenceOfBlowups := by
        rcases m73 c' with hc0 | hc1
        have hiso := C.isIso_pullbackFiberToHypersurface_of_eq_one (by omega)
        have hsmooth : Smooth C.pullbackFiberToHypersurface := inferInstance
        have hsurj : Surjective C.pullbackFiberToHypersurface := inferInstance
        have hcomap : C.idealOnHypersurface.comap C.pullbackFiberToHypersurface = cmI I C.pullbackFiberToBase := by
          rw [hHideal]
          exact comap_imageIdealSheaf C.pullbackFiberToHypersurface $ cmI I C.pullbackFiberToBase
        have hvS' : tAd (markedTripleOrderOne k C.pullbackFiber (C.pullbackFiberToBase ≫ p)
            (C.idealOnHypersurface.comap C.pullbackFiberToHypersurface) []) := by
          rwa [hcomap]
        have hsp : IsStrictPullbackBlowupSeq C.pullbackFiberToHypersurface
            ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.pullbackFiber
              (C.pullbackFiberToBase ≫ p) (C.idealOnHypersurface.comap C.pullbackFiberToHypersurface) [])).toSequenceOfBlowups
            ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.hypersurfaceScheme
              C.hypersurfaceStructureMap C.idealOnHypersurface [])).toSequenceOfBlowups :=
          @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec
            (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []) hvH
            (show krullDimSucc C.hypersurfaceScheme ≤ m + 1 by omega)
            C.pullbackFiber (C.pullbackFiberToBase ≫ p) C.pullbackFiberToHypersurface hsmooth hsurj hfacH hvS'
            (show krullDimSucc C.pullbackFiber ≤ m + 1 by omega)
        rw [hcomap] at hsp
        rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.pullbackFiber (C.pullbackFiberToBase ≫ p)
            (cmI I C.pullbackFiberToBase) [] (m + 1) (by omega),
          maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.hypersurfaceScheme C.hypersurfaceStructureMap C.idealOnHypersurface []
            (m + 1) (by omega)] at hsp
        exact IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso C.pullbackFiberToHypersurface hsp
        have hcc0 :=
          C.hasEtaleCoordCodim_pullbackFiberToHypersurface
        rw [hHideal]
        exact ih k hcz C.pullbackFiber C.hypersurfaceScheme (C.pullbackFiberToBase ≫ p) C.hypersurfaceStructureMap
          C.pullbackFiberToHypersurface inferInstance inferInstance hqcS hsmH inferInstance hqcH
          hfacH hc1 hcc0 (cmI I C.pullbackFiberToBase) hNZS
          (by rw [← hHideal]; exact hcontactNZ)
      have hOBW : (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
          (cmI (imageIdealSheaf j I) C.projection) []).IsOrderBoundedByMult := by
        rw [isOrderBoundedByMult_iff]
        intro x
        have h1 : orderAt (cmI (imageIdealSheaf j I) C.projection) x ≤ 1 := by
          rw [orderAt_comap k p' C.projection (imageIdealSheaf j I) x]
          exact horder $ C.projection.base x
        exact le_trans h1 $ le_of_eq cast_one.symm
      have hdiv : IsSmoothDivisor (C.projection ≫ p')
          (ker C.toCoverData.iInfImageIdeal.si) := by
        rw [q2]
        exact C.isSmoothDivisor_iInfImageIdeal
      have hpushHW : IsPushforwardBlowupSeq C.toCoverData.iInfImageIdeal.si
          ((rules.inputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.hypersurfaceScheme C.hypersurfaceStructureMap
            C.idealOnHypersurface [])).toSequenceOfBlowups
          ((rules.outputLevelData (m + 1)).orderRed (markedTripleOrderOne k C.toCoverData.disjointUnion
            (C.projection ≫ p') (cmI (imageIdealSheaf j I) C.projection) [])).toSequenceOfBlowups :=
        @IsOrderReduction.pushforward _ _ _ hordspec
          (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
            (cmI (imageIdealSheaf j I) C.projection) []) hvW
          (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega) hOBW rfl rfl
          C.hypersurfaceScheme C.hypersurfaceStructureMap C.toCoverData.iInfImageIdeal.si hCI rfl hdiv
          C.idealOnHypersurface hvH hHW hWideal
      rw [rules.inputLevelData_succ m, maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.hypersurfaceScheme C.hypersurfaceStructureMap
        C.idealOnHypersurface [] m (by omega)] at hpushHW
      have hequivW :=
        hspec.orderRed_equiv (markedTripleOrderOne k C.toCoverData.disjointUnion (C.projection ≫ p')
          (cmI (imageIdealSheaf j I) C.projection) []) hvW
          (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega) rfl hOBW
      rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.toCoverData.disjointUnion (C.projection ≫ p')
        (cmI (imageIdealSheaf j I) C.projection) [] (m + 1) (by omega)] at hequivW
      have hpushSubscheme := IsPushforwardBlowupSeq.of_isomorphic C.toCoverData.iInfImageIdeal.si
        hpushHW (SequenceOfBlowups.Isomorphic.symm hequivW)
      have hNtH : ∀ i, i ≤ msLen (rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap
          C.idealOnHypersurface []) →
          IsNoetherian (msAt (rules.markedBlowupSeq k C.hypersurfaceScheme C.hypersurfaceStructureMap
            C.idealOnHypersurface []) i) :=
        fun i hi => isNoetherian_schemeAt _ i hi
      have hNtW : ∀ i, i ≤ msLen (rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p')
          (cmI (imageIdealSheaf j I) C.projection) []) →
          IsNoetherian (msAt (rules.markedBlowupSeq k C.toCoverData.disjointUnion (C.projection ≫ p')
            (cmI (imageIdealSheaf j I) C.projection) []) i) :=
        fun i hi => isNoetherian_schemeAt _ i hi
      have hcomp := IsPushforwardBlowupSeq.comp C.pullbackFiberToHypersurface C.toCoverData.iInfImageIdeal.si
        hNtH hNtW hpushFiber hpushSubscheme
      have hcomp' :=
        isPushforwardSequenceOfBlowups_congr_hom C.pullbackFiberToHypersurface_comp_subschemeio hcomp
      have hres := strictTransformIsBlowupOfClosedSubscheme
      have hcart := effectiveCartierSupportContainsNoComponent
      let _a1 := rules.markedBlowupSeq k X p I []
      have hproper := centersContainNoComponent_ofMarkedSequence hcart hvX
        _a1
      have htower := isPushforwardBlowupSeq_ambientBlowupSequence j
        (ofSequenceOfBlowups _a1.toSequenceOfBlowups) hres
        blowupPreservesNoetherian hproper
      obtain ⟨u0, hpf0⟩ : ∃ u0,
          IsPushforwardBlowupSeq j _a1.toSequenceOfBlowups u0 :=
        ⟨_, IsPushforwardBlowupSeq.of_isomorphic_source j (ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _) htower⟩
      have ht' :=
        isStrictPullbackSequenceOfBlowups_baseChange u0 C.projection
      have hsS : IsStrictPullbackBlowupSeq C.pullbackFiberToBase
          ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.pullbackFiber
            (C.pullbackFiberToBase ≫ p) (cmI I C.pullbackFiberToBase) [])).toSequenceOfBlowups
          ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k X p I [])).toSequenceOfBlowups :=
        @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec
          (markedTripleOrderOne k X p I []) hvX (show krullDimSucc X ≤ m + 1 by omega)
          C.pullbackFiber (C.pullbackFiberToBase ≫ p) C.pullbackFiberToBase hsmSB hsuSB rfl hvS
          (show krullDimSucc C.pullbackFiber ≤ m + 1 by omega)
      rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (cmI I C.pullbackFiberToBase) []
          (m + 1) (by omega),
        maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X p I [] (m + 1) (by omega)] at hsS
      have hSW : IsStrictPullbackBlowupSeq C.projection
          ((rules.outputLevelData (m + 1)).maxOrderRed (markedTripleOrderOne k C.toCoverData.disjointUnion
            (C.projection ≫ p') (cmI (imageIdealSheaf j I) C.projection) [])).toSequenceOfBlowups
          ((rules.outputLevelData (m + 1)).maxOrderRed
            (markedTripleOrderOne k X' p' (imageIdealSheaf j I) [])).toSequenceOfBlowups :=
        @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective _ _ _ hspec
          (markedTripleOrderOne k X' p' (imageIdealSheaf j I) []) hvX'
          (show krullDimSucc X' ≤ m + 1 by omega) C.toCoverData.disjointUnion (C.projection ≫ p')
          C.projection hsmP hsuP rfl hvW
          (show krullDimSucc C.toCoverData.disjointUnion ≤ m + 1 by omega)
      rw [maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k C.toCoverData.disjointUnion (C.projection ≫ p')
          (cmI (imageIdealSheaf j I) C.projection) [] (m + 1) (by omega),
        maxOrderReduction_outputLevelData_eq_markedBlowupSeq rules k X' p' (imageIdealSheaf j I) [] (m + 1) (by omega)] at hSW
      have hup := IsPushforwardBlowupSeq.of_flat_isPullback j C.pullbackFiberToTotal C.projection C.pullbackFiberToBase
        C.isPullback_pullbackFiber.flip _a1.toSequenceOfBlowups u0
        (rules.markedBlowupSeq k C.pullbackFiber (C.pullbackFiberToBase ≫ p) (cmI I C.pullbackFiberToBase) []).toSequenceOfBlowups
        (u0.baseChange C.projection)
        (fun i hi => isLocallyNoetherian_schemeAt u0 i hi)
        (fun i hi => isLocallyNoetherian_schemeAt (u0.baseChange C.projection) i hi)
        hpf0 hsS ht'
      have huniq := IsPushforwardBlowupSeq.isomorphic C.pullbackFiberToTotal hup hcomp'
      have hdesc := IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic ht' hSW huniq
      exact IsPushforwardBlowupSeq.of_isomorphic j hpf0 hdesc

theorem commutesWithClosedImmersion_of_isCorrect (B : PrincipalizationRules) (hB : B.ReducesInductivelyOnDimension) :
    CommutesWithClosedImmersion B :=
  by
  intro k ik icz X X' p ism ift iqc p' ism' ift' iqc' j ij hjp c hc hcod I hI hIim _ _
  exact commutesWithClosedImmersion_forall_codim B hB isAdmissible_pullbackAlong_of_smooth c k icz X X' p p' j ism ift iqc ism' ift' iqc' hjp hc hcod I hI hIim

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

section
variable (T : MarkedIdealWithBoundary)
section
variable (j) (hj : j < T.boundary.length)
noncomputable abbrev restrictToDivisor :
    MarkedIdealWithBoundary :=
  restrictToBoundaryDivisor T j hj (lowerIdealWithoutBlowup T) $ lowerBoundaryWithoutBlowup T

noncomputable abbrev restrictTwistedToDivisor :
    MarkedIdealWithBoundary :=
  rBD hj
end
section
variable {T}
noncomputable abbrev rD {j : ℕ} (hj : j < T.boundary.length) := restrictToDivisor T j hj
noncomputable abbrev rTD {j : ℕ} (hj : j < T.boundary.length) := restrictTwistedToDivisor T j hj
end

theorem isNoetherian_scheme_of_isAdmissible (hV : T.IsAdmissible) :
    IsNoetherian T.scheme :=
  hV.isNoetherian
end

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length) (I0) (E0) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups) (hpr : s.NoComp)
noncomputable def ambientBlowupSeq :
    BlowupSequenceData T.scheme :=
  ambientBlowupSequence (T.bget j hj).si
    s.toBsd hres hno hpr

section
variable (n : ℕ)
noncomputable def embeddingIntoAmbient :
    s.toBsd.obj n ⟶
      (ambientBlowupSeq hres hno T j hj I0 E0 s hpr).obj n :=
  embeddingIntoAmbientBlowupSequence (T.bget j hj).si
    s.toBsd hres hno hpr n

theorem ambientBlowupSeq_center_eq_imageIdealSheaf :
    (ambientBlowupSeq hres hno T j hj I0 E0 s hpr).center n =
      imageIdealSheaf (embeddingIntoAmbient hres hno T j hj I0 E0 s hpr n) (s.center n) :=
  ambientBlowupSequence_center (bgetT hj).si
    s.toBsd hres hno hpr n

theorem isClosedImmersion_embeddingIntoAmbient :
    IsClosedImmersion $ embeddingIntoAmbient hres hno T j hj I0 E0 s hpr n :=
  isClosedImmersion_embeddingIntoAmbientBlowupSequence (bgetT hj).si
    s.toBsd hres hno hpr n
end

theorem ambientBlowupSeq_length :
    (ambientBlowupSeq hres hno T j hj I0 E0 s hpr).length = s.length :=
  ambientBlowupSequence_length (bgetT hj).si
    s.toBsd hres hno hpr
end

noncomputable abbrev amb (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] {j : ℕ} {hj : j < T.boundary.length} {I0 : T.scheme.IdealSheafData} {E0 : List T.scheme.IdealSheafData} {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups} (hpr : s.NoComp) := ambientBlowupSeq hres hno T j hj I0 E0 s hpr
noncomputable abbrev embA (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] {j : ℕ} {hj : j < T.boundary.length} {I0 : T.scheme.IdealSheafData} {E0 : List T.scheme.IdealSheafData} {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups} (hpr : s.NoComp) (n : ℕ) := embeddingIntoAmbient hres hno T j hj I0 E0 s hpr n

end DivisorReduction

structure DivisorReductionTerminationProperties (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hno : BlowupPreservesNoetherian) : Prop where
  isMarked_pushedTop : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj = ⊤ → (DivisorReduction.rD hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rD hj).SequenceOfBlowups)
        (hpr : s.NoComp),
        (DivisorReduction.amb hres hno hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isMarked_pushedPre : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj ≠ ⊤ →
      ∀ (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj),
      (DivisorReduction.rTD hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rTD hj).SequenceOfBlowups)
        (hpr : s.NoComp),
        (prepend (DivisorReduction.ccI hj) hb
            (DivisorReduction.amb hres hno hpr)).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isBlowup_id_preIdeal : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj
  lowerTriple_dim_lt : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    (orderAtLeastLocus T.ideal T.mult).Nonempty →
    ∀ (j : ℕ) (hj : j < T.boundary.length) (I0 : T.scheme.IdealSheafData)
      (E0 : List T.scheme.IdealSheafData),
      (DivisorReduction.restrictToBoundaryDivisor T j hj I0 E0).krullDimSucc < T.krullDimSucc
  valid_lowerTop : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj = ⊤ → (DivisorReduction.rD hj).IsAdmissible
  valid_lowerPre : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj ≠ ⊤ → (DivisorReduction.rTD hj).IsAdmissible
  orderAt_ctrlIdeal_le_top : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj = ⊤ → (DivisorReduction.rD hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rD hj).SequenceOfBlowups)
        (hpr : s.NoComp) (i : ℕ),
        i ≤ s.length →
        ∀ x : ↥((DivisorReduction.amb hres hno hpr).obj i),
          orderAt ((DivisorReduction.amb hres hno hpr).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ENat)
  orderAt_ctrlIdeal_le_pre : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj ≠ ⊤ →
      ∀ (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj),
      (DivisorReduction.rTD hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rTD hj).SequenceOfBlowups)
        (hpr : s.NoComp) (i : ℕ),
        i ≤ s.length + 1 →
        ∀ x : ↥((prepend (DivisorReduction.ccI hj) hb
            (DivisorReduction.amb hres hno hpr)).obj i),
          orderAt ((prepend (DivisorReduction.ccI hj) hb
            (DivisorReduction.amb hres hno hpr)).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ENat)
  coSupport_inter_ker_eq_empty_top : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj = ⊤ → (DivisorReduction.rD hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rD hj).SequenceOfBlowups)
        (hpr : s.NoComp),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : CSet $ s.schemeAt s.length) →
        (orderAtLeastLocus ((DivisorReduction.amb hres hno hpr).controlledTransform T.ideal T.mult s.length) T.mult ∩
            ((ker $ DivisorReduction.embA hres hno hpr
                s.length).support :
              Set ↥((DivisorReduction.amb hres hno hpr).obj s.length))) = ∅
  coSupport_inter_ker_eq_empty_pre : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj ≠ ⊤ →
      ∀ (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj),
      (DivisorReduction.rTD hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rTD hj).SequenceOfBlowups)
        (hpr : s.NoComp),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : CSet $ s.schemeAt s.length) →
        (orderAtLeastLocus ((prepend (DivisorReduction.ccI hj) hb
                (DivisorReduction.amb hres hno hpr)).controlledTransform T.ideal T.mult
              (s.length + 1)) T.mult ∩
            ((ker $ DivisorReduction.embA hres hno hpr
                s.length).support :
              Set ↥((DivisorReduction.amb hres hno hpr).obj s.length))) = ∅
  properCenters : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → 1 ≤ T.mult → ∀ s : T.SequenceOfBlowups,
    s.NoComp
  isPullbackSeq_ambientTower : ∀ (X Y S S' : Sch) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (ph_ : Y ⟶ X) (ps_ : S' ⟶ S) [IsClosedImmersion σ]
      [IsClosedImmersion σ'] [Flat ph_]
      [IsNoetherian X] [IsNoetherian Y],
      IsPullback σ' ps_ ph_ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsPullbackBlowupSequence ps_ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsPullbackBlowupSequence ph_ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  isStrictPullbackSeq_ambientTower : ∀ (X Y S S' : Sch) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (ph_ : Y ⟶ X) (ps_ : S' ⟶ S) [IsClosedImmersion σ]
      [IsClosedImmersion σ'] [Flat ph_]
      [IsNoetherian X] [IsNoetherian Y],
      IsPullback σ' ps_ ph_ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsStrictPullbackBlowupSeq ps_ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsStrictPullbackBlowupSeq ph_ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  comap_ctrlIdeal_top : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj = ⊤ → (DivisorReduction.rD hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rD hj).SequenceOfBlowups)
        (hpr : s.NoComp) (i : ℕ),
        i ≤ s.length →
        ((DivisorReduction.amb hres hno hpr).controlledTransform T.ideal T.mult i).comap
            (DivisorReduction.embA hres hno hpr i) = s.ideal i
  comap_ctrlIdeal_pre : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.ccI hj ≠ ⊤ →
      ∀ (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj),
      (DivisorReduction.rTD hj).IsAdmissible →
      ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rTD hj).SequenceOfBlowups)
        (hpr : s.NoComp) (i : ℕ),
        i ≤ s.length →
        ((prepend (DivisorReduction.ccI hj) hb
              (DivisorReduction.amb hres hno hpr)).controlledTransform T.ideal T.mult
              (i + 1)).comap
            (DivisorReduction.embA hres hno hpr i) = s.ideal i
  preIdeal_baseChange : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L), (T.bc f).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.bc f).boundary.length),
      containedComponentsIdeal (T.bc f) j hj' =
        (DivisorReduction.ccI hj).comap
          (pullback.fst T.structMap $ specMapOfFieldHom T.base L f)
  preIdeal_pullbackAlong : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      (T.pbA q h).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.pbA q h).boundary.length),
      containedComponentsIdeal (T.pbA q h) j hj' =
        (DivisorReduction.ccI hj).comap h
  preIdeal_eq_top_of_imageIdeal : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (J : (T.bget j hj).subscheme.IdealSheafData), T.mult = 1 →
      (T.withSchemeIdealBoundary (T.bget j hj).subscheme
          ((T.bget j hj).si ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => D.comap (T.bget j hj).si))).IsAdmissible →
      T.ideal = imageIdealSheaf (T.bget j hj).si J →
      DivisorReduction.ccI hj = ⊤

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

section
variable (T : MarkedIdealWithBoundary)
theorem noetherianSpace_boundary_subscheme (hV : T.IsAdmissible) j
    (hj : j < T.boundary.length) :
    TopologicalSpace.NoetherianSpace ↥(T.bget j hj).subscheme := by
  have := hV.isNoetherian
  exact (isClosedEmbedding
    (bgetT hj).si).toIsEmbedding.toIsInducing.noetherianSpace

section
variable (j) (hj : j < T.boundary.length)
abbrev divisorComponentsInOrderLocus :
    Set ↥(T.bget j hj).subscheme :=
  {x : ↥(T.bget j hj).subscheme |
    connectedComponent x ⊆
      ⇑(T.bget j hj).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}

theorem containedComponentsIdeal_eq_openSubschemeKer
    (h : IsOpen $ divisorComponentsInOrderLocus T j hj) :
    DivisorReduction.ccI hj =
      openSubschemeKer (T.bget j hj) ⟨divisorComponentsInOrderLocus T j hj, h⟩ :=
  containedComponentsIdeal_eq_ker T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen (h : ¬ IsOpen (divisorComponentsInOrderLocus T j hj)) :
    DivisorReduction.ccI hj = ⊤ :=
  DivisorReduction.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h
end

section
variable (hV : T.IsAdmissible) (j) (hj : j < T.boundary.length)
include hV
theorem isClosed_divisorComponentsInOrderLocus :
    IsClosed $ divisorComponentsInOrderLocus T j hj := by
  have := noetherianSpace_boundary_subscheme T hV j hj
  let _a0 := bget' hj
  exact TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
    _a0.subscheme
    (subschemeι _a0 ⁻¹' orderAtLeastLocus T.ideal T.mult)

theorem exists_etaleChart_containedComponentsIdeal (x : ↥T.scheme)
    (hx : x ∈ support (DivisorReduction.ccI hj)) :
    ∃ (U : T.scheme.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart T.structMap U n)
      (a : ℕ → Option (Fin n)) (b : Fin n),
      a j = some b ∧
      (∀ i hi, a i = none →
        restrictIdeal (T.bget i hi) U = ⊤) ∧
      (∀ i hi t, a i = some t →
        restrictIdeal (T.bget i hi) U = c.coordIdeal {t}) ∧
      (∀ i i', i < T.boundary.length → i' < T.boundary.length →
        ∀ t : Fin n, a i = some t → a i' = some t → i = i') ∧
      restrictIdeal (DivisorReduction.ccI hj) U = c.coordIdeal {b} := by
  let _a1 := divisorComponentsInOrderLocus T j hj
  classical
  by_cases hopen : IsOpen _a1
  have hWclosed := isClosed_divisorComponentsInOrderLocus T hV j hj
  have hpre :=
    containedComponentsIdeal_eq_openSubschemeKer T j hj hopen
  let _a2 := (bget' hj).subscheme.Opens
  have h1 : x ∈ (spI (openSubschemeKer (bget' hj)
      (⟨_a1, hopen⟩ :
        _a2)) : CSet T.scheme) := by
    rwa [← hpre]
  rw [support_openSubschemeKer (bget' hj)
    (⟨_a1, hopen⟩ : _a2) hWclosed] at h1
  obtain ⟨U0_, hxU0_, hU0_⟩ := exists_opens_preimage_subschemeio_le (bget' hj)
    (⟨_a1, hopen⟩ : _a2) x h1
  obtain ⟨U1_, hxU1, n, c, a, hinj, hnone, hsome⟩ :=
    (((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).2 x).exists_etaleChart
  have hUle : U0_ ⊓ U1_ ≤ U1_ := inf_le_right
  have hxU : x ∈ U0_ ⊓ U1_ := ⟨hxU0_, hxU1⟩
  have hpreU : ((bgetT hj).si.pre $ U0_ ⊓ U1_) ≤
      (⟨_a1, hopen⟩ : _a2) := by
    intro y hy
    exact hU0_ hy.1
  have hrestr : restrictIdeal (DivisorReduction.ccI hj) (U0_ ⊓ U1_) =
      restrictIdeal (bget' hj) (U0_ ⊓ U1_) := by
    rw [hpre]
    exact restrictIdeal_openSubschemeKer_of_preimage_le _ _ hWclosed _ hpreU
  have hajne : a j ≠ none := by
    intro haj
    have h2 : restrictIdeal (bget' hj) U1_ = ⊤ := by
      simpa only [get_eq_getElem] using hnone j hj haj
    refine notMem_support_of_restrictIdeal_eq_top _ _ x hxU ?_ hx
    rw [hrestr]
    exact restrictIdeal_eq_top_of_le _ hUle h2
  obtain ⟨b, hb⟩ : ∃ b, a j = some b := by
    cases h : a j with
    | none => exact absurd h hajne
    | some b => exact ⟨b, rfl⟩
  refine ⟨U0_ ⊓ U1_, hxU, n, c.restrict hUle, a, b, hb, ?_, ?_, ?_, ?_⟩
  intro i hi hai
  refine restrictIdeal_eq_top_of_le _ hUle ?_
  simpa only [get_eq_getElem] using hnone i hi hai
  intro i hi t hai
  refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {t} ?_
  simpa only [get_eq_getElem] using hsome i hi t hai
  intro i i' hi hi' t h4 h5
  exact hinj i hi i' hi' t h4 h5
  rw [hrestr]
  refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {b} ?_
  simpa only [get_eq_getElem] using hsome j hj b hb
  exfalso
  rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj hopen] at hx
  exact (mem_support_iff_stalkIdeal_ne_top (⊤) x).1 hx
    (stalkIdeal_top x)

theorem isSmoothDivisor_boundary_get :
    IsSmoothDivisor T.structMap $ T.bget j hj := by
  refine ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ ?_
  simp_all

theorem support_containedComponentsIdeal_subset_orderAtLeastLocus :
    ((support (DivisorReduction.ccI hj) : CSet T.scheme)) ⊆ orderAtLeastLocus T.ideal T.mult := by
  by_cases h : IsOpen $ divisorComponentsInOrderLocus T j hj
  have hcl := isClosed_divisorComponentsInOrderLocus T hV j hj
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
    support_openSubschemeKer (bget' hj) ⟨divisorComponentsInOrderLocus T j hj, h⟩ hcl]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx
  exact hx' mem_connectedComponent
  rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
  intro x hx
  have hx' : x ∈ spI (⊤ : tISD T) := hx
  rw [mem_support_iff_stalkIdeal_ne_top] at hx'
  exact absurd (stalkIdeal_top x) hx'

theorem smooth_subschemeio_containedComponentsIdeal_comp :
    Smooth $ subschemeι (DivisorReduction.ccI hj) ≫ structMap T := by
  let _a0 := bget' hj
  have hsmp := hV.smooth
  by_cases h : IsOpen $ divisorComponentsInOrderLocus T j hj
  have hsm :=
    ((isSmoothDivisor_iff T.structMap _a0).1
      (isSmoothDivisor_boundary_get T hV j hj)).2
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
  exact smooth_subschemeio_openSubschemeKer_comp _a0
    ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj) T.structMap
  rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
  exact ((isSmoothDivisor_iff T.structMap (⊤)).1
    (isSmoothDivisor_top T.structMap)).2

theorem isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal :
    IsLocallyGeneratedByNonZeroDivisor (DivisorReduction.ccI hj) := by
  have hsmp := hV.smooth
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
  let _a0 := bget' hj
  exact isLocallyGeneratedByNonZeroDivisor_openSubschemeKer _a0
    ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj)
    (((isSmoothDivisor_iff T.structMap _a0).1
      (isSmoothDivisor_boundary_get T hV j hj)).1)
  rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
  exact ((isSmoothDivisor_iff T.structMap (⊤)).1
    (isSmoothDivisor_top T.structMap)).1

theorem hasStrictNormalCrossingsWith_containedComponentsIdeal :
    HasStrictNormalCrossingsWith T.structMap (DivisorReduction.ccI hj) T.boundary := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZ⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  refine ⟨U, hxU, n, c, a, {b}, ?_, ?_, ?_, hZ⟩
  intro i hi i' hi' t hti hti'
  exact hinj i i' hi hi' t hti hti'
  intro i hi hni
  exact hnone i hi hni
  simp_all

theorem isBlowupAlongIdealSheaf_id_containedComponentsIdeal :
    IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj :=
  isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor _ $ isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj

theorem exists_mul_pow_containedComponentsIdeal_eq_ideal :
    ∃ J,
      DivisorReduction.ccI hj ^ T.mult * J = ideal T := by
  have := hV.isNoetherian
  have := hV.charZero
  have := hV.smooth
  exact Blowup.IsLocallyGeneratedByNonZeroDivisor.exists_mul_eq
    ((isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj).pow T.mult) $ le_pow_of_hasStrictNormalCrossingsWith T.structMap (p28 hj) T.ideal T.boundary (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj) T.mult $ support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj
end
end





section
variable {S S' X X' : Sch} (i : S ⟶ X) [IsClosedImmersion i] (i' : S' ⟶ X') (p : X' ⟶ X) (q : S' ⟶ S) (hsq : i' ≫ p = q ≫ i) (Z : ISD S)
include hsq
theorem comap_exceptionalIdeal_of_closedImmersionSquare :
    (exceptionalIdeal p $ Z.map i).comap i' = exceptionalIdeal q Z := by
  rw [p9, p9, ← comap_comp, hsq,
    comap_comp, p30]

theorem comap_controlledTransform_of_closedImmersionSquare (hcart : IsLocallyGeneratedByNonZeroDivisor (exceptionalIdeal q Z))
    m (A : ISD X) (A' : ISD X') J'
    (hA : exceptionalIdeal p (Z.map i) ^ m * A' = A.comap p)
    (hJ : exceptionalIdeal q Z ^ m * J' = (A.comap i).comap q) :
    A'.comap i' = J' := by
  have h1 : (p5 p (Z.map i) ^ m * A').comap i' = (cmI A p).comap i' := by
    rw [hA]
  rw [comap_mul, comap_pow,
    comap_exceptionalIdeal_of_closedImmersionSquare i i' p q hsq Z,
    ← comap_comp, hsq, comap_comp] at h1
  refine (hcart.pow m).eq_of_mul_eq_mul ?_
  simp_all
end

namespace DivisorReduction

variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I0 : T.scheme.IdealSheafData)
    (E0 : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups)
    (hpr : s.NoComp)

theorem embeddingIntoAmbient_comp_blowupMorphism (t : ℕ) :
    embA hres hno hpr (t + 1) ≫
        (amb hres hno hpr).map t =
      s.transitionMapSucc t ≫ embA hres hno hpr t :=
  embeddingIntoAmbientBlowupSequence_succ_comp_map (bgetT hj).si
    s.toBsd hres hno hpr t

instance instIsClosedImmersionPushedEmb (t : ℕ) :
    IsClosedImmersion $ embA hres hno hpr t :=
  isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.bget j hj).si
    s.toBsd hres hno hpr t

theorem embeddingIntoAmbient_zero :
    embA hres hno hpr 0 =
      s.isoZero.hom ≫ subschemeι (T.bget j hj) :=
  embeddingIntoAmbientBlowupSequence_zero (bgetT hj).si
    s.toBsd hres hno hpr

private theorem ambientBlowupSeq_isoObjZero_hom :
    (amb hres hno hpr).isoZero.hom = 𝟙 T.scheme :=
  congrArg hom $ ambientBlowupSequence_isoObjZero (bgetT hj).si
    s.toBsd hres hno hpr

theorem comap_controlledTransform_embeddingIntoAmbient t (ht : t ≤ s.length)
    (hdiv : ∀ i < t, ∃ B : ((amb hres hno hpr).obj (i + 1)).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map i)
          ((amb hres hno hpr).center i) ^ T.mult * B =
        (((amb hres hno hpr).controlledTransform I0 T.mult i).comap
          ((amb hres hno hpr).map i))) :
    ((amb hres hno hpr).controlledTransform I0 T.mult t).comap
        (embA hres hno hpr t) = s.ideal t := by
  let _c0 := amb hres hno hpr
  revert ht hdiv
  induction t with
  | zero =>
    intro ht hdiv
    have e1 : cmI (_c0.controlledTransform I0 T.mult 0)
        (embA hres hno hpr 0) =
          I0.comap (embA hres hno hpr 0 ≫
            (bdIzH _c0)) := by
      rw [p53]
      exact sy_ (comap_comp ..)
    have e2 : embA hres hno hpr 0 ≫
        _c0.isoZero.hom =
          s.isoZero.hom ≫ siI (bgetT hj) := by
      rw [ambientBlowupSeq_isoObjZero_hom hres hno T j hj I0 E0 s hpr,
        embeddingIntoAmbient_zero hres hno T j hj I0 E0 s hpr]
      exact comp_id _
    exact tr_ e1 (tr_ (congrArg I0.comap e2) (s.ideal_zero.trans (comap_comp ..).symm).symm)
  | succ t IH =>
    intro ht hdiv
    have hts := ht
    have h0 := pow_exceptionalIdeal_mul_controlledTransform_succ _c0 I0 T.mult t
      (hdiv t (lt_succ_self t))
    rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I0 E0 s hpr t] at h0
    refine comap_controlledTransform_of_closedImmersionSquare
      (embA hres hno hpr t)
      (embA hres hno hpr (t + 1))
      (_c0.map t) (s.transitionMapSucc t)
      (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I0 E0 s hpr t) (s.center t)
      (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (s.isBlowupAlongIdealSheaf_blowupMorphism t hts)) T.mult
      (_c0.controlledTransform I0 T.mult t)
      (_c0.controlledTransform I0 T.mult (t + 1))
      (s.ideal (t + 1)) h0 ?_
    rw [IH (le_of_succ_le ht) fun i hi => hdiv i $ lt_succ_of_lt hi]
    exact s.ideal_succ t hts

end DivisorReduction





theorem iSup_le_zero_nat {Y : Sch} (G : ℕ → ISD Y) :
    (⨆ l, ⨆ _ : l ≤ 0, G l) = G 0 :=by simp_all
namespace BlowupSequenceData

section
variable {X : Sch} (d : BlowupSequenceData X)
theorem controlledTransform_congr (I I' : ISD X)
    (h : I.comap (projectionToBase d 0) = I'.comap (projectionToBase d 0)) (m t : ℕ) :
    d.controlledTransform I m t = d.controlledTransform I' m t := by
  induction t with
  | zero =>
    rwa [controlledTransform_zero, controlledTransform_zero, ← d.projectionToBase_zero]
  | succ t ih =>
    rw [controlledTransform_succ, controlledTransform_succ, ih]

theorem boundary_congr (E E' : Bdy X)
    (h : List.map (fun D => D.comap $ projectionToBase d 0) E = List.map (fun D => D.comap $ projectionToBase d 0) E')
    (t : ℕ) :
    d.boundaryFrom E t = d.boundaryFrom E' t := by
  induction t with
  | zero =>
    rwa [boundary_zero, boundary_zero, ← d.projectionToBase_zero]
  | succ t ih =>
    rw [boundary_succ, boundary_succ, ih]

end

end BlowupSequenceData

theorem orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le (k : Type) [Field k] [CharZero k]
    {Y : Sch} (p : Y ⟶ Sp k) [Smooth p]
    (K A : ISD Y) (l m : ℕ) (hlm : l < m) (h : K ^ m ≤ A ^ (m - l)) :
    orderAtLeastLocus A m ⊆ orderAtLeastLocus K (m - l) := by
  let _c0 := ((m - l) : ENat)
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx
  rw [mem_orderAtLeastLocus_iff]
  have hm : 1 ≤ m := mpr_ one_le_iff_ne_zero $ by omega
  have hml : 1 ≤ m - l := by omega
  have h1 := orderAt_le_of_le h x
  rw [orderAt_pow k p A (m - l) x, orderAt_pow k p K m x] at h1
  let _m0 := (m : ENat)
  let _a0 := orderAt K x
  refine mp_ (natCast_mul_le_mul_iff hm (m - l) _a0) ?_
  calc _m0 * _c0
      = _c0 * _m0 := mul_comm _ _
    _ ≤ _c0 * orderAt A x := (natCast_mul_le_mul_iff hml m $ orderAt A x).mpr hx
    _ ≤ _m0 * _a0 := h1

theorem comap_iSup_le_nat {Y Y' : Sch} (f : Y' ⟶ Y) (n : ℕ) (G : ℕ → ISD Y) :
    (⨆ l ≤ n, G l).comap f = ⨆ l ≤ n, (G l).comap f := by
  induction n with
  | zero => rw [iSup_le_zero_nat, iSup_le_zero_nat]
  | succ n ih =>
    rw [iSup_le_succ, iSup_le_succ, comap_sup, ih]

theorem mem_support_iSup_le_nat {Y : Sch} (n : ℕ) (G : ℕ → ISD Y) (y : Y)
    (h : ∀ l ≤ n, y ∈ support (G l)) : y ∈ support (⨆ l ≤ n, G l) :=by simp_all
namespace DivisorReduction

variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j)
    (hj : j < T.boundary.length) (I0)
    (E0) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups)
    (hpr : s.NoComp)

noncomputable abbrev divisorEmbedding : scheme (restrictToBoundaryDivisor T j hj I0 E0) ⟶ scheme T :=
  subschemeι $ T.bget j hj

noncomputable abbrev ambientBlowupSeqStructureMorphism (t : ℕ) :
    (amb hres hno hpr).obj t ⟶ Sp T.base :=
  (amb hres hno hpr).projectionToBase t ≫ T.structMap

noncomputable abbrev ambientDerivIdeal [LocallyOfFiniteType T.structMap]
    (l t : ℕ) : ((amb hres hno hpr).obj t).IdealSheafData :=
  (amb hres hno hpr).controlledTransform
    (derivIdealSheafIterate T.base T.structMap l I0) (mult T - l) t

theorem embeddingIntoAmbient_comp_projectionToBase (t : ℕ) :
    embA hres hno hpr t ≫ (amb hres hno hpr).projectionToBase t =
      s.projectionToBase t ≫ divisorEmbedding T j hj I0 E0 := by
  let _c0 := amb hres hno hpr
  induction t with
  | zero =>
    have h0 : _c0.isoZero = refl T.scheme :=
      ambientBlowupSequence_isoObjZero (bgetT hj).si
        s.toBsd hres hno hpr
    rw [p23, h0, embeddingIntoAmbient_zero, MarkedSequenceOfBlowups.projectionToBase_zero, refl_hom]
    exact comp_id _
  | succ t ih =>
    have hmap := embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I0 E0 s hpr t
    have hstruct : s.transitionMapSucc t ≫ s.projectionToBase t = s.projectionToBase (t + 1) := by
      rw [blowupMorphism_eq_transitionMap]
      exact transitionMap_comp_projectionToBase s.toSequenceOfBlowups $ le_succ t
    exact tr_ (congrArg (fun f => (embA hres hno hpr $ t + 1) ≫ f) $ projectionToBase_succ _c0 t) $ tr_ (sy_ $ assoc _ _ _) $ tr_ (congrArg (fun f => f ≫ _c0.projectionToBase t) hmap) $ tr_ (assoc _ _ _) $ tr_ (congrArg (fun f => s.transitionMapSucc t ≫ f) ih) $ tr_ (sy_ $ assoc _ _ _) $ congrArg (fun f => f ≫ divisorEmbedding T j hj I0 E0) hstruct

noncomputable abbrev ambM (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] {j : ℕ} {hj : j < T.boundary.length} {I0 : T.scheme.IdealSheafData} {E0 : List T.scheme.IdealSheafData} {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups} (hpr : s.NoComp) (t : ℕ) := ambientBlowupSeqStructureMorphism hres hno T j hj I0 E0 s hpr t

noncomputable abbrev aDI (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] [LocallyOfFiniteType T.structMap] {j : ℕ} {hj : j < T.boundary.length} {I0 : T.scheme.IdealSheafData} {E0 : List T.scheme.IdealSheafData} {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups} (hpr : s.NoComp) (l t : ℕ) := ambientDerivIdeal hres hno T j hj I0 E0 s hpr l t

end DivisorReduction




theorem imageIdealSheaf_eq_ker_subschemeio_comp {S X : Sch} (f : S ⟶ X) (Z : ISD S) :
    imageIdealSheaf f Z = ker (subschemeι Z ≫ f) :=
  rfl

theorem support_imageIdealSheaf_eq_image_support {S X : Sch} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : ISD S) :
    (↑(imageIdealSheaf ι Z).support : Set ↥X) = ⇑ι '' (↑Z.support : Set ↥S) := by
  let _a0 := siI Z ≫ ι
  have hqc : QuasiCompact _a0 := inferInstance
  have hcomp : range _a0 = ι '' (support Z) := by
    rw [← range_subschemeι Z]
    ext x
    constructor
    rintro ⟨y, rfl⟩
    exact ⟨subschemeι Z y, ⟨y, rfl⟩, rfl⟩
    rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  have hclosed : IsClosed $ ι '' (support Z) :=
    (isClosedEmbedding ι).isClosedMap _ Z.support.2
  rw [imageIdealSheaf_eq_ker_subschemeio_comp, support_ker, hcomp, hclosed.closure_eq]

private theorem exists_iso_ker_subscheme {W X : Sch} (g : W ⟶ X)
    [IsClosedImmersion g] :
    ∃ e : W ≅ subscheme (ker g),
      hom e ≫ subschemeι (ker g) = g :=
  ⟨asIso $ toImage g, toImage_imageι g⟩

private theorem smooth_of_smooth_iso_hom_comp {A A' B : Sch} (e : A ≅ A') (p : A' ⟶ B)
    (h : Smooth $ hom e ≫ p) : Smooth p := by
  have h2 : Smooth $ isoI e ≫ isoH e ≫ p := inferInstance
  simpa using h2

theorem smooth_imageIdealSheaf_subschemeio_comp {S X B : Sch} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : ISD S) (f : X ⟶ B)
    (h : Smooth $ subschemeι Z ≫ ι ≫ f) :
    Smooth $ subschemeι (imageIdealSheaf ι Z) ≫ f := by
  let _a0 := siI Z ≫ ι
  have : IsClosedImmersion _a0 := inferInstance
  obtain ⟨e, he⟩ := exists_iso_ker_subscheme _a0
  rw [imageIdealSheaf_eq_ker_subschemeio_comp ι Z]
  refine smooth_of_smooth_iso_hom_comp e _ ?_
  rwa [← assoc, he, assoc]

namespace BlowupSequenceData

section
variable {X : Sch} (Z) (hZ : IsBlowupAlongIdealSheaf (id X) Z) (d : BlowupSequenceData X)
theorem projectionToBase_prepend_succ t :
    projectionToBase (prepend Z hZ d) (t + 1) = projectionToBase d t := by
  let _a0 := prepend Z hZ d
  induction t with
  | zero =>
    rw [projectionToBase_succ _a0 0, p23 _a0, prepend_isoObjZero Z hZ d, prepend_blowupMorphism_zero Z hZ d, p23 d]
    exact comp_id _
  | succ n ih =>
    rw [projectionToBase_succ _a0 $ n + 1, prepend_blowupMorphism_succ Z hZ d n, ih]
    exact sy_ $ projectionToBase_succ d n

theorem controlledTransform_prepend_succ
    (I I1 : ISD X) m
    (h1 : (prepend Z hZ d).controlledTransform I m 1 = I1.comap d.isoZero.hom) t :
    (prepend Z hZ d).controlledTransform I m (t + 1) = d.controlledTransform I1 m t := by
  induction t with
  | zero => exact tr_ h1 (d.controlledTransform_zero I1 m).symm
  | succ n ih =>
    rewrite [controlledTransform_succ (prepend Z hZ d) I m $ n + 1,
      controlledTransform_succ d I1 m n, ih,
      prepend_blowupMorphism_succ Z hZ d n, prepend_center_succ Z hZ d n]
    rfl

theorem boundary_prepend_succ
    E E1_
    (h1 : (prepend Z hZ d).boundaryFrom E 1
      = List.map (fun D => D.comap d.isoZero.hom) E1_) t :
    (prepend Z hZ d).boundaryFrom E (t + 1) = d.boundaryFrom E1_ t := by
  induction t with
  | zero =>
      rwa [BlowupSequenceData.boundary_zero]
  | succ n ih =>
      rw [p52 (prepend Z hZ d) E $ n + 1,
        p52 d E1_ n, ih, prepend_blowupMorphism_succ Z hZ d n,
        prepend_center_succ Z hZ d n]
      all_goals rfl
end

end BlowupSequenceData

namespace DivisorReduction

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length) (I0) (E0) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups) (hpr : s.NoComp) (t : ℕ)
theorem smooth_ambientBlowupSeq_center_comp (ht : t < s.length) :
    Smooth
      (((amb hres hno hpr).center t).subschemeι ≫
        ((amb hres hno hpr).projectionToBase t ≫ T.structMap)) := by
  let _a0 := amb hres hno hpr
  let _a1 := _a0.projectionToBase t ≫ tMp T
  exact Eq.mpr
    (congrArg
      (fun Z : ISD (_a0.obj t) =>
        Smooth $ siI Z ≫
          _a1)
      (ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I0 E0 s hpr t))
    (smooth_imageIdealSheaf_subschemeio_comp (embA hres hno hpr t) (s.center t)
      _a1 $ Eq.mpr (congrArg (fun g : ((ofMarkedSequence s).obj t ⟶ Sp T.base) => Smooth $ siI (s.center t) ≫ g) $ (st_ $ assoc _ _ _) $ tr_ (congrArg (fun g : ((ofMarkedSequence s).obj t ⟶ tSch T) => g ≫ tMp T) $ embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I0 E0 s hpr t) $ assoc _ _ _) $ s.center_smooth t ht)

theorem support_ambientBlowupSeq_center_eq_image :
    (↑((amb hres hno hpr).center t).support :
        Set ↥((amb hres hno hpr).obj t)) =
      ⇑(embA hres hno hpr t) ''
        (↑((ofMarkedSequence s).center t).support :
          Set ↥((ofMarkedSequence s).obj t)) := by
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I0 E0 s hpr t, ofMarkedSequence_center s t]
  exact support_imageIdealSheaf_eq_image_support
    (embA hres hno hpr t) $ s.center t
end

end DivisorReduction



theorem imageIdealSheaf_comap_io_eq_self_of_support_subset {Y : Sch} (Z : ISD Y)
    (U : Opn Y) (_hU : IsClosed (U : Set Y))
    (hZ : (support Z : Set Y) ⊆ (U : Set Y)) :
    imageIdealSheaf U.i (Z.comap U.i) = Z := by
  let _c0 := Z.si.pre U
  have hmem : ∀ x, x ∈ _c0 := by
    intro x
    have hx : Z.subschemeι.base x ∈ (spI Z : Set Y) := by
      rw [← range_subschemeι]
      exact mem_range_self x
    exact hZ hx
  have key : ∀ y,
      y ∈ range (p4 _c0).base := by simp_all
  obtain ⟨e, he⟩ : ∃ e,
      e ≫ p4 _c0 = 𝟙 Z.subscheme := by
    exact ⟨m43 (p4 _c0) (𝟙 Z.subscheme)
      (fun y _ => key y), m115 ..⟩
  have h2 : p4 _c0 ≫ e = 𝟙 _c0.toScheme := by
    rw [← cancel_mono $ p4 _c0, assoc, he,
      comp_id, id_comp]
  have : IsIso $ p4 _c0 := ⟨⟨e, h2, he⟩⟩
  rw [imageIdealSheaf_eq_ker_subschemeio_comp, ← ker_io_preimage_comp_subschemeio_eq_ker_comap Z U,
    ker_eq_ker_of_isIso_comp (p4 _c0 ≫ siI Z) Z.si
      (p4 _c0) rfl,
    q2]

section
variable {Y Y1 : Sch}
theorem restrictIdeal_strictTransform_congr [IsLocallyNoetherian Y1]
    (f : Y1 ⟶ Y) (Z : ISD Y) (W : Opn Y) (A B : ISD Y)
    (h : restrictIdeal A W = restrictIdeal B W) :
    restrictIdeal (strictTransform f Z A) (pre f W)
      = restrictIdeal (strictTransform f Z B) (pre f W) := by
  have hcomp :=
    (morphismRestrict_ι f W).symm
  let _a0 := restrictIdeal Z W
  have hA : restrictIdeal (p6 f Z A) (preU f W)
      = p6 (mrU f W) _a0 (restrictIdeal A W) := by
    rw [restrictIdeal_strictTransform f Z A $ preU f W, hcomp,
      strictTransform_comp_io W (mrU f W) Z A]
  have hB : restrictIdeal (p6 f Z B) (preU f W)
      = p6 (mrU f W) _a0 (restrictIdeal B W) := by
    rw [restrictIdeal_strictTransform f Z B $ preU f W, hcomp,
      strictTransform_comp_io W (mrU f W) Z B]
  rw [hA, hB, h]

theorem restrictIdeal_strictTransform_preimage [IsLocallyNoetherian Y1]
    (f : Y1 ⟶ Y) (Z D : ISD Y) (W : Opn Y) :
    restrictIdeal (strictTransform f Z D) (pre f W)
      = strictTransform (f.mr W) (restrictIdeal Z W) (restrictIdeal D W) := by
  rw [restrictIdeal_strictTransform f Z D $ preU f W, (morphismRestrict_ι f W).symm,
    strictTransform_comp_io W (mrU f W) Z D]

theorem restrictIdeal_exceptionalIdeal (f : Y1 ⟶ Y)
    (Z : ISD Y) (W : Opn Y) :
    restrictIdeal (exceptionalIdeal f Z) (pre f W)
      = exceptionalIdeal (f.mr W) (restrictIdeal Z W) := by
  show (cmI Z f).comap (p4 $ preU f W)
      = (cmI Z $ p4 W).comap (mrU f W)
  rw [← comap_comp, ← comap_comp,
    morphismRestrict_ι]
end

section
variable {A B C : Sch} (a : A ⟶ B) (b : B ⟶ C)
theorem coe_base_comp :
    ⇑(a ≫ b).base = ⇑b.base ∘ ⇑a.base := by
  funext x
  simp

private theorem range_base_comp :
    range ⇑(a ≫ b).base = ⇑b.base '' range ⇑a.base := by
  rw [coe_base_comp, range_comp]
end

section
variable {S Y : Sch} (f : S ⟶ Y)
section
variable [IsClosedImmersion f] (U : Opn S) (hU : IsClosed (U : Set S))
include hU
theorem support_ker_opens_io_comp :
    ((ker $ U.i ≫ f).support : Set Y) = ⇑f.base '' (U : Set S) := by
  let _a0 := opI U ≫ f
  have hce : Topology.IsClosedEmbedding _a0.base := by
    have hUce : Topology.IsClosedEmbedding U.ib := by
      refine ⟨U.ι.isOpenEmbedding.toIsEmbedding, ?_⟩
      rwa [q1]
    rw [coe_base_comp]
    exact (isClosedEmbedding f).comp hUce
  have : QuasiCompact _a0 := by
    constructor
    intro V _ hV
    exact hce.isCompact_preimage hV
  have hrange : range _a0.base = f.base '' U := by
    rw [coe_base_comp, range_comp, q1]
  have hclosed : IsClosed $ f.base '' U := by
    rw [← hrange]
    exact hce.isClosed_range
  rw [support_ker, hrange]
  exact hclosed.closure_eq
end

end

theorem quasiCompact_of_isClosedEmbedding_base {A B : Sch} (g : A ⟶ B)
    (hg : Topology.IsClosedEmbedding ⇑g.base) : QuasiCompact g := by
  constructor
  intro V _ hV
  exact hg.isCompact_preimage hV

theorem restrictIdeal_ker_opens_io_comp_of_preimage_le {S Y : Sch} (f : S ⟶ Y) [IsClosedImmersion f]
    (U : Opn S) (hU : IsClosed (U : Set S)) (W : Opn Y)
    (hW : (pre f W : Opn S) ≤ U) :
    restrictIdeal (ker $ U.i ≫ f) W = restrictIdeal (ker f) W := by
  let _c0 := preU (opI U ≫ f) W
  have hcif := isClosedEmbedding f
  have _hciU :=
    AlgebraicGeometry.Scheme.Opens.isClosedImmersion_ι_of_isClosed U hU
  have _hqf := quasiCompact_of_isClosedEmbedding_base f hcif
  have _hqUf : QuasiCompact $ opI U ≫ f := by
    refine quasiCompact_of_isClosedEmbedding_base _ ?_
    rw [coe_base_comp]
    exact hcif.comp $ isClosedEmbedding U.i
  have _i9 : range (p4 (preU (opI U ≫ f) W) ≫ opI U).base = range (p4 $ preU f W).base := by
    have h2 : ((preU (opI U ≫ f) W : U.toScheme.Opens) : Set U.toScheme)
        = U.ib ⁻¹' ((preU f W) : Set S) := rfl
    rw [range_base_comp, q1, q1, h2,
      image_preimage_eq_inter_range, q1]
    refine mpr_ inter_eq_left ?_
    intro x hx
    exact hW hx
  have hrange :=
    sy_ _i9
  let _a0 := p4 $ preU f W
  have hfac : ∀ e : oSch (preU f W) ⟶ oSch _c0,
      e ≫ p4 _c0 ≫ opI U = _a0 →
      e ≫ (mrU (opI U ≫ f) W) = mrU f W := by
    intro e he
    have he' : (e ≫ p4 _c0) ≫ opI U = _a0 := by
      rwa [assoc]
    rw [← cancel_mono $ p4 W, assoc, morphismRestrict_ι,
      morphismRestrict_ι, ← assoc, ← assoc, he']
  let _m0 := IsOpenImmersion.isoOfRangeEq _a0 (p4 _c0 ≫ opI U) hrange
  have key : isoH _m0 ≫ (mrU (opI U ≫ f) W) = mrU f W :=
    hfac _ $ IsOpenImmersion.isoOfRangeEq_hom_fac ..
  rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ker_comap_io_eq_ker_morphismRestrict (opI U ≫ f) W,
    ker_comap_io_eq_ker_morphismRestrict f W]
  exact sy_ $ ker_eq_ker_of_isIso_comp (mrU f W) (mrU (opI U ≫ f) W)
    _m0.hom key

section
variable {S Y S1_ Y1 : Sch} [IsLocallyNoetherian Y1] (ι : S ⟶ Y) [IsClosedImmersion ι] (io1 : S1_ ⟶ Y1) [IsClosedImmersion io1] (g : S1_ ⟶ S) (f : Y1 ⟶ Y) (hsq : io1 ≫ f = g ≫ ι) (Z : ISD Y) (U : Opn S) (hU : IsClosed (U : Set S))
include hsq hU
theorem ker_preimage_io_comp_eq_strictTransform_of_cover
    (hU1 : IsClosed ((pre g U : Opn S1_) : Set S1_))
    (hker : ker io1 = strictTransform f Z (ker ι))
    (W1 W2 : Opn Y) (hcov : ∀ y : Y, y ∈ W1 ∨ y ∈ W2)
    (h1_ : (pre ι W1 : Opn S) ≤ U)
    (h2_ : ∀ x : S, x ∈ U → ι.base x ∉ W2) :
    ker ((g ⁻¹ᵁ U).i ≫ io1)
      = strictTransform f Z (ker $ U.i ≫ ι) := by
  let _c0 := ker $ opI (preU g U) ≫ io1
  let _c1 := ker $ opI U ≫ ι
  have hbase : ∀ x, bsM f (bsM io1 x) = bsM ι (bsM g x) := by
    intro x
    have hh1 : bsM (io1 ≫ f) x = bsM f (bsM io1 x) := by simp
    have hh2 : bsM (g ≫ ι) x = bsM ι (bsM g x) := by simp
    rw [← hh1, ← hh2, hsq]
  have hpre1_ : (preU io1 (preU f W1) : Opn S1_) ≤ (preU g U) := by
    intro x hx
    have hx' : bsM f (bsM io1 x) ∈ W1 := hx
    rw [hbase x] at hx'
    have hmem := hx'
    exact h1_ hmem
  refine eq_of_restrictIdeal_eq_of_iSup_eq_top _ _
    (fun b => cond b (preU f W1) $ preU f W2) ?_ ?_
  rw [eq_top_iff]
  intro y _
  refine TopologicalSpace.Opens.mem_iSup.mpr ?_
  rcases hcov (bsM f y) with hy | hy
  simp_all
  simp_all
  intro b
  cases b with
  | false =>
    let _a0 := restrictIdeal _c0 $ preU f W2
    show _a0
      = restrictIdeal (strictTransform f Z _c1) (preU f W2)
    have t1 : _a0 = ⊤ := by
      refine mpr_ (restrictIdeal_eq_top_iff_forall_notMem_support _ _) ?_
      intro y hy hmem
      have hmem' : y ∈ (spI _c0 : Set Y1) := hmem
      rw [support_ker_opens_io_comp io1 (preU g U) hU1] at hmem'
      obtain ⟨x, hxU, rfl⟩ := hmem'
      have hfy : bsM f (bsM io1 x) ∈ W2 := hy
      rw [hbase x] at hfy
      exact h2_ (bsM g x) hxU hfy
    have t2 : restrictIdeal _c1 W2 = ⊤ := by
      refine mpr_ (restrictIdeal_eq_top_iff_forall_notMem_support _ _) ?_
      intro y hy hmem
      have hmem' : y ∈ (spI _c1 : Set Y) := hmem
      rw [support_ker_opens_io_comp ι U hU] at hmem'
      obtain ⟨x, hxU, rfl⟩ := hmem'
      exact h2_ x hxU hy
    have t3 : restrictIdeal _c1 W2
        = restrictIdeal (⊤) W2 := by
      rw [t2]
      exact sy_ $ comap_top ..
    have htop : strictTransform f Z (⊤) = (⊤) := by
      refine le_antisymm le_top ?_
      have hle := Blowup.comap_le_strictTransform f Z (⊤)
      rwa [comap_top] at hle
    rw [t1, restrictIdeal_strictTransform_congr f Z W2 _ _ t3, htop]
    exact sy_ $ comap_top ..
  | true =>
    show restrictIdeal _c0 (preU f W1)
      = restrictIdeal (strictTransform f Z _c1) (preU f W1)
    rw [restrictIdeal_ker_opens_io_comp_of_preimage_le io1 (preU g U) hU1 (preU f W1) hpre1_, hker, restrictIdeal_strictTransform_congr f Z W1 _ _ $ restrictIdeal_ker_opens_io_comp_of_preimage_le ι U hU W1 h1_]

theorem ker_preimage_io_comp_eq_strictTransform_of_isClopen
    (hker : ker io1 = strictTransform f Z (ker ι)) :
    ker ((g ⁻¹ᵁ U).i ≫ io1)
      = strictTransform f Z (ker $ U.i ≫ ι) := by
  have hioemb := isClosedEmbedding ι
  refine ker_preimage_io_comp_eq_strictTransform_of_cover ι io1 g f hsq Z U hU (mp_ isOpen_compl_iff (preU g (⟨Uᶜ, hU.isOpen_compl⟩ : Opn S)).isOpen) hker
    ⟨(ι.base '' (Uᶜ))ᶜ, (hioemb.isClosedMap _ $ mpr_ isClosed_compl_iff U.isOpen).isOpen_compl⟩
    ⟨(ι.base '' U)ᶜ, (hioemb.isClosedMap _ hU).isOpen_compl⟩ ?_ ?_ ?_
  intro y
  by_cases hy : y ∈ ι.base '' U
  left
  obtain ⟨x, hxU, rfl⟩ := hy
  show bsM ι x ∈ (ι.base '' (Uᶜ))ᶜ
  rintro ⟨x', hx'V, hx'⟩
  have hx'U := hxU
  rw [← hioemb.toIsEmbedding.injective hx'] at hx'U
  exact absurd hx'U hx'V
  right
  show y ∈ (ι.base '' U)ᶜ
  exact hy
  intro x hx
  by_contra hxU
  exact absurd (show bsM ι x ∈ ι.base '' (Uᶜ) from ⟨x, hxU, rfl⟩) hx
  intro x hxU hmem
  exact absurd (show bsM ι x ∈ ι.base '' U from ⟨x, hxU, rfl⟩) hmem
end




namespace BlowupSequenceData

theorem pow_controlledTransform_le_pow_controlledTransform_of_dvd {X : Sch} (d : BlowupSequenceData X)
    K A m l (hbase : K ^ m ≤ A ^ (m - l)) t
    (ht : t ≤ length d)
    (hdivA : ∀ i < t, ∃ B : (d.obj $ i + 1).IdealSheafData,
      exceptionalIdeal (d.map i) (d.center i) ^ m * B = (d.controlledTransform A m i).comap (d.map i))
    (hdivK : ∀ i < t, ∃ B : (d.obj $ i + 1).IdealSheafData,
      exceptionalIdeal (d.map i) (d.center i) ^ (m - l) * B =
        (d.controlledTransform K (m - l) i).comap (d.map i)) :
    d.controlledTransform K (m - l) t ^ m ≤ d.controlledTransform A m t ^ (m - l) := by
  revert ht hdivA hdivK
  induction t with
  | zero =>
      intro _ _ _
      rw [p53, p53,
        ← comap_pow, ← comap_pow]
      exact comap_mono (f := bdIzH d) hbase
  | succ n ih =>
      intro ht hdivA hdivK
      have hn := lt_of_lt_of_le (lt_succ_self n) ht
      let t := n
      let hle := ih (le_of_lt hn) (fun i hi => hdivA i $ lt_succ_of_lt hi)
          (fun i hi => hdivK i $ lt_succ_of_lt hi)
      have hcomap : (d.controlledTransform K (m - l) t ^ m).comap (d.map t) ≤
          (d.controlledTransform A m t ^ (m - l)).comap (d.map t) :=
        comap_mono _ hle
      rw [comap_pow, comap_pow, ← d.pow_exceptionalIdeal_mul_controlledTransform_succ K (m - l) t $ hdivK n $ lt_succ_self n, ← d.pow_exceptionalIdeal_mul_controlledTransform_succ A m t $ hdivA n $ lt_succ_self n,
        mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (m - l) m] at hcomap
      exact ((isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal $ d.isBlowup n hn).pow $ m * (m - l)).le_of_mul_le_mul hcomap

theorem exists_pow_mul_eq_comap_controlledTransform {k : Type} [Field k] [CharZero k] {X : Sch}
    (d : BlowupSequenceData X) (p : X ⟶ Sp k) (A : ISD X) (n t : ℕ)
    (ht : t < length d) [IsLocallyNoetherian $ d.obj $ t + 1]
    [Smooth $ projectionToBase d t ≫ p]
    (E : List (d.obj t).IdealSheafData)
    (hE : HasStrictNormalCrossingsWith (projectionToBase d t ≫ p) (d.center t) E)
    (hord : ↑(d.center t).support ⊆ orderAtLeastLocus (d.controlledTransform A n t) n) :
    ∃ B : (d.obj $ t + 1).IdealSheafData,
      exceptionalIdeal (d.map t) (d.center t) ^ n * B = (d.controlledTransform A n t).comap (d.map t) := by
  let _a0 := d.controlledTransform A n t
  obtain ⟨B, hB, -⟩ :=
    existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map t) (d.center t) _a0 n
      (d.isBlowup t ht) $ le_pow_of_hasStrictNormalCrossingsWith (projectionToBase d t ≫ p) (d.center t) _a0 E hE n hord
  exact ⟨B, hB⟩

end BlowupSequenceData

namespace DivisorReduction

theorem pow_ambientDerivIdeal_le_pow_controlledTransform
    (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian)
    (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme]
    [LocallyOfFiniteType T.structMap]
    j (hj : j < T.boundary.length) I0
    E0 (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hbal : IsDerivBalanced T.base T.structMap I0 T.mult)
    l (hl : l < T.mult) t (ht : t ≤ s.length)
    (hdivA : ∀ i < t, ∃ B : ((amb hres hno hpr).obj $ i + 1).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map i)
          ((amb hres hno hpr).center i) ^ T.mult * B =
        ((amb hres hno hpr).controlledTransform I0 T.mult i).comap
          ((amb hres hno hpr).map i))
    (hdivD : ∀ i < t, ∃ B : ((amb hres hno hpr).obj $ i + 1).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map i)
          ((amb hres hno hpr).center i) ^ (T.mult - l) * B =
        (aDI hres hno hpr l i).comap
          ((amb hres hno hpr).map i)) :
    aDI hres hno hpr l t ^ T.mult ≤
      (amb hres hno hpr).controlledTransform I0 T.mult t ^ (T.mult - l) := by
  have ht' := ht
  rw [← ambientBlowupSeq_length hres hno T j hj I0 E0 s hpr] at ht'
  exact BlowupSequenceData.pow_controlledTransform_le_pow_controlledTransform_of_dvd (amb hres hno hpr)
    (derivIdealSheafIterate T.base T.structMap l I0) I0 T.mult l
    (IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hl) t ht' hdivA hdivD

end DivisorReduction




theorem exists_affineOpen_ideal_eq_top_of_not_mem_support {X : Sch}
    (I : ISD X) (y : ↥X) (hy : y ∉ support I) :
    ∃ V : X.affineOpens, y ∈ V.1 ∧ I.ideal V = ⊤ := by
  obtain ⟨U, hyU, -⟩ :=
    Scheme.exists_affineOpens_mem_le (X := X) (x := y) (U := ⊤) trivial
  have hny := hy
  rw [mem_support_iff_of_mem (I := I) (U := U) hyU,
    AlgebraicGeometry.Scheme.mem_zeroLocus_iff] at hny
  push Not at hny
  obtain ⟨s, hs, hys⟩ := hny
  refine ⟨X.affineBasicOpen s, hys, ?_⟩
  let _ :=
    (pMap X (homOfLE $ X.basicOpen_le s).op).hom.toAlgebra
  have hloc := U.2.isLocalization_basicOpen s
  have hmem : algebraMap Γ(X, U.1) Γ(X, bOpn X s) s ∈ I.ideal (X.affineBasicOpen s) := by
    rw [← I.map_ideal_basicOpen U s]
    exact mem_map_of_mem _ hs
  exact eq_top_of_isUnit_mem _ hmem $ IsLocalization.map_units (M := Submonoid.powers s) Γ(X, bOpn X s) ⟨s, Submonoid.mem_powers s⟩

theorem not_mem_support_of_mem_support_of_pow_mul {X : Sch}
    (Z I I0 : ISD X) (m : ℕ) (hfac : I = Z ^ m * I0)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ENat)) {x : ↥X} (hx : x ∈ Z.support) :
    x ∉ I0.support := by
  intro hx0
  have hIle : stalkIdeal I x ≤ m16 (stkX X x) ^ (m + 1) := by
    rw [hfac, stalkIdeal_mul, stalkIdeal_pow, pow_succ]
    exact mul_mono (pow_right_mono ((mem_support_iff_stalkIdeal_le_maximalIdeal Z x).mp hx) m) $ (mem_support_iff_stalkIdeal_le_maximalIdeal I0 x).mp hx0
  have h4 : m + 1 ≤ m := by exact_mod_cast (le_trans (mpr_ (le_orderAt_iff I x $ m + 1) hIle) $ hord x)
  omega

theorem isDerivBalanced_of_pow_mul (k : Type) [Field k] {X : Sch}
    (p : X ⟶ Sp k) [Smooth p]
    (Z I I0 : ISD X) (m : ℕ) (hfac : I = Z ^ m * I0)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ENat)) (hbal : IsDerivBalanced k p I m) :
    IsDerivBalanced k p I0 m := by
  refine mpr_ (isDerivBalanced_iff k p I0 m) ?_
  intro i hi
  refine le_of_forall_exists_affineOpen ?_
  intro y
  by_cases hyZ : y ∈ spI Z
  obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support I0 y
    (not_mem_support_of_mem_support_of_pow_mul Z I I0 m hfac hord hyZ)
  refine ⟨V, hyV, ?_⟩
  have htop : (I0 ^ (m - i)).ideal V = ⊤ := by simp_all
  rw [htop]
  exact le_top
  obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support Z y hyZ
  refine ⟨V, hyV, ?_⟩
  have hIV : I.ideal V = I0.ideal V := by
    rw [hfac, ideal_mul, ideal_pow]
    show Z.ideal V ^ m * I0.ideal V = I0.ideal V
    rw [hV, ← m217, one_pow, one_mul]
  have hder : (derivIdealSheafIterate k p i I).ideal V
      = (derivIdealSheafIterate k p i I0).ideal V := by
    rw [derivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal, hIV]
  have hb : ((derivIdealSheafIterate k p i I).ideal V) ^ m ≤ (I.ideal V) ^ (m - i) := by
    have hb0 := mp_ le_def (mp_ (isDerivBalanced_iff k p I m) hbal i hi) V
    rwa [ideal_pow, ideal_pow] at hb0
  rw [ideal_pow, ideal_pow]
  show ((derivIdealSheafIterate k p i I0).ideal V) ^ m ≤ (I0.ideal V) ^ (m - i)
  rwa [← hIV, ← hder]




section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme)
theorem divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq
    (L : PrincipalizationAssignment) (j : ℕ) (T : MarkedIdealWithBoundary) :
    (canonicalAlgorithmRules hres).divisorFamily L j T =
      divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j := by
  rw [PrincipalizationRules.divisorFamily_apply]
  rfl

section
variable (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
include hfacts
theorem DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend
    (L : PrincipalizationAssignment) (j : ℕ) (T : MarkedIdealWithBoundary)
    [IsNoetherian T.scheme]
    (hV : T.IsAdmissible) (hj : j < T.boundary.length) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType)
    (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : CSet T.scheme)) :
    (DivisorReduction.ccI hj = ⊤ ∧
        ∃ hpr : (ofMarkedSequence
            (L (DivisorReduction.rD hj))).toBlowupSequenceData.CentersContainNoComponent,
          ∃ _hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
                (L (DivisorReduction.rD hj)) hpr).IsMarked
              T.structMap T.ideal T.mult T.boundary,
            ∀ hmk : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
                (L (DivisorReduction.rD hj)) hpr).IsMarked
              T.structMap T.ideal T.mult T.boundary,
              divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
                ((DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                    (DivisorReduction.lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
                    (L (DivisorReduction.rD hj)) hpr).toMarkedBlowupSequenceData
                  T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups) ∨
      (DivisorReduction.ccI hj ≠ ⊤ ∧
        ∃ hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.ccI hj),
          ∃ hpr : (ofMarkedSequence
              (L (DivisorReduction.rTD hj))).toBlowupSequenceData.CentersContainNoComponent,
            ∃ _hmk : (prepend (DivisorReduction.ccI hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (lI hj) (lB hj)
                  (L (DivisorReduction.rTD hj)) hpr)).IsMarked
                T.structMap T.ideal T.mult T.boundary,
              ∀ hmk : (prepend (DivisorReduction.ccI hj) hb
                (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                  (lI hj) (lB hj)
                  (L (DivisorReduction.rTD hj)) hpr)).IsMarked
                T.structMap T.ideal T.mult T.boundary,
                divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
                  ((prepend (DivisorReduction.ccI hj) hb
                      (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
                        (lI hj)
                        (lB hj)
                        (L (DivisorReduction.rTD hj)) hpr)).toMarkedBlowupSequenceData
                    T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups) := by
  have hcsne := mpr_ nonempty_iff_ne_empty hcs
  by_cases hZ : p28 hj = ⊤
  have hvalid := hfacts.valid_lowerTop T hV hO hD j hj hZ
  let _a0 := DivisorReduction.rD hj
  have hpr :=
    hfacts.properCenters _a0 hvalid hvalid.one_le_mult
      (L _a0)
  refine m51 ⟨hZ, hpr,
    hfacts.isMarked_pushedTop T hV hO hD j hj hZ hvalid
      (L _a0) hpr, ?_⟩
  intro hmk
  exact divisorReductionSeq_eq_of_containedComponentsIdeal_eq_top hres
    blowupPreservesNoetherian T (fun S _ => L S) j hj hcs hZ
    ⟨hfacts.lowerTriple_dim_lt T hV hcsne j hj (p19 T)
      (p20 T), inferInstance⟩ hpr hmk
  have hb := hfacts.isBlowup_id_preIdeal T hV j hj
  have hvalid := hfacts.valid_lowerPre T hV hO hD j hj hZ
  let _a1 := DivisorReduction.rTD hj
  have hpr :=
    hfacts.properCenters _a1 hvalid hvalid.one_le_mult
      (L _a1)
  refine m61 ⟨hZ, hb, hpr,
    hfacts.isMarked_pushedPre T hV hO hD j hj hZ hb hvalid
      (L _a1) hpr, ?_⟩
  intro hmk
  exact divisorReductionSeq_eq_of_isBlowupAlongIdealSheaf hres
    blowupPreservesNoetherian T (fun S _ => L S) j hj hcs hZ hb
    ⟨hfacts.lowerTriple_dim_lt T hV hcsne j hj (p21 hj)
      (p37 hj), inferInstance⟩ hpr hmk

section
variable (n : ℕ) (L : PrincipalizationAssignment) (j : ℕ) (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible)
theorem DivisorReduction.divisorReductionSeq_orderAt_le_mult (_hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i ≤ (divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j).length,
      ∀ x : ↥((divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).schemeAt i),
        orderAt ((divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).ideal i) x ≤ (T.mult : ENat) := by
  let _a2 := bget' hj
  have := DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  rw [divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
    (fun S _ => L S) j hj hcs]
  intro i hi x
  rw [emptyMarkedSequenceOfBlowups_length] at hi
  have hi0 := mp_ le_zero hi
  subst hi0
  have hid : (emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary).ideal 0
      = tId T := by
    rw [ideal_zero]
    exact comap_id _
  rw [hid]
  exact (T.isOrderBoundedByMult_iff.mp hO) x
  rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with
    ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩
  have hvalid := hfacts.valid_lowerTop T hV hO hD j hj hZ
  let _a0 := L $ DivisorReduction.rD hj
  let _m1 := DivisorReduction.amb hres blowupPreservesNoetherian hpr
  have hlen : _m1.length
      = _a0.length := by
    have h := ambientBlowupSequence_length _a2.si
      _a0.toBsd
      hres blowupPreservesNoetherian hpr
    calc _m1.length
        = _a0.toBsd.length := h
      _ = _a0.length :=
          ofMarkedSequence_length _
  rw [heq hmk]
  intro i hi x
  rw [toMarkedSequence_length, toMarkedBlowupSequenceData_length, hlen] at hi
  simp [toMarkedSequence_ideal, toMarkedBlowupSequenceData_ideal]
  exact hfacts.orderAt_ctrlIdeal_le_top T hV hO hD j hj hZ hvalid
    _a0 hpr i hi x
  have hvalid := hfacts.valid_lowerPre T hV hO hD j hj hZ
  let _a1 := L $ DivisorReduction.rTD hj
  let _m0 := DivisorReduction.amb hres blowupPreservesNoetherian hpr
  have hlen : _m0.length
      = _a1.length := by
    have h := ambientBlowupSequence_length _a2.si
      _a1.toBsd
      hres blowupPreservesNoetherian hpr
    calc _m0.length
        = _a1.toBsd.length := h
      _ = _a1.length :=
          ofMarkedSequence_length _
  rw [heq hmk]
  intro i hi x
  rw [toMarkedSequence_length, toMarkedBlowupSequenceData_length,
    prepend_length, hlen] at hi
  simp [toMarkedSequence_ideal, toMarkedBlowupSequenceData_ideal]
  exact hfacts.orderAt_ctrlIdeal_le_pre T hV hO hD j hj hZ hb hvalid
    _a1 hpr i hi x

theorem divisorFamily_canonicalAlgorithmRules_orderAt_le_mult (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) :
    ∀ i ≤ ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
      ∀ x : ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt i),
        orderAt (((canonicalAlgorithmRules hres).divisorFamily L j T).ideal i) x ≤ (T.mult : ENat) := by
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
  exact DivisorReduction.divisorReductionSeq_orderAt_le_mult hres hfacts n L j T hV hdim hO hD hj
end
end

theorem divisorFamily_canonicalAlgorithmRules_length_eq_zero
    (n : ℕ) (L : PrincipalizationAssignment) (j : ℕ) (T : MarkedIdealWithBoundary)
    (hV : T.IsAdmissible) (_hdim : T.krullDimSucc ≤ n) (_hO : T.IsOrderBoundedByMult)
    (_hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (hcs : orderAtLeastLocus T.ideal T.mult = (∅ : CSet T.scheme)) :
    ((canonicalAlgorithmRules hres).divisorFamily L j T).length = 0 := by
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq,
    divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
  exact emptyMarkedSequenceOfBlowups_length T.structMap T.ideal T.mult T.boundary
end

theorem support_imageIdealSheaf_nonempty {X Y : Sch} (f : X ⟶ Y)
    (hf : IsClosedImmersion f) (J : ISD X)
    (h : ((support J : Set ↥X)).Nonempty) :
    (((imageIdealSheaf f J).support : Set ↥Y)).Nonempty := by
  obtain ⟨x, hx⟩ := h
  have hmem := hx
  rw [← q5] at hmem
  obtain ⟨z, -⟩ := hmem
  refine ⟨(siI J ≫ f) z, ?_⟩
  rw [imageIdealSheaf_eq_ker, support_ker]
  exact subset_closure $ mem_range_self z

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (n) (L O) (hL : IsMaxOrderReduction (fun d => d < n) L O) (j) (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
include hfacts hL hdim hO hD hj
theorem DivisorReduction.divisorReductionSeq_center_nonempty :
    ∀ i < (divisorReductionSeq hres blowupPreservesNoetherian T
        (fun S _ => L S) j).length,
      (((divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).center i).support :
        Set ↥((divisorReductionSeq hres blowupPreservesNoetherian T
          (fun S _ => L S) j).schemeAt i)).Nonempty := by
  have := DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  rw [divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
    (fun S _ => L S) j hj hcs]
  intro i hi
  rw [emptyMarkedSequenceOfBlowups_length] at hi
  exact absurd hi $ not_lt_zero i
  have hcsne := mpr_ nonempty_iff_ne_empty hcs
  rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with
    ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩
  have hvalid := hfacts.valid_lowerTop T hV hO hD j hj hZ
  let _a2 := DivisorReduction.rD hj
  let _a0 := L _a2
  let _s0 := DivisorReduction.amb hres blowupPreservesNoetherian hpr
  have hlen : _s0.length
      = _a0.length := by
    have h := ambientBlowupSequence_length (bgetT hj).si
      _a0.toBsd
      hres blowupPreservesNoetherian hpr
    calc _s0.length
        = _a0.toBsd.length := h
      _ = _a0.length :=
          ofMarkedSequence_length _
  rw [heq hmk]
  intro i hi
  rw [toMarkedSequence_length, toMarkedBlowupSequenceData_length, hlen] at hi
  have hcenter : _s0.center i
      = imageIdealSheaf (embeddingIntoAmbientBlowupSequence (bgetT hj).si
          _a0.toBsd
          hres blowupPreservesNoetherian hpr i)
        (_a0.center i) := by
    have h := ambientBlowupSequence_center (bgetT hj).si
      _a0.toBsd
      hres blowupPreservesNoetherian hpr i
    simp at h
    exact h
  simp
  exact support_imageIdealSheaf_nonempty _
    (isClosedImmersion_embeddingIntoAmbientBlowupSequence (bgetT hj).si
      _a0.toBsd
      hres blowupPreservesNoetherian hpr i) _
    (hL.center_nonempty _a2 hvalid (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcsne j hj (p19 T) (p20 T)) hdim) i hi)
  have hvalid := hfacts.valid_lowerPre T hV hO hD j hj hZ
  let _a1 := (L (DivisorReduction.rTD hj)).length
  have hlen : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
      (p21 hj) (p37 hj)
      (L (DivisorReduction.rTD hj)) hpr).length
      = _a1 := by
    have h := ambientBlowupSequence_length (bgetT hj).si
      (ofMarkedSequence (L (DivisorReduction.rTD hj))).toBlowupSequenceData
      hres blowupPreservesNoetherian hpr
    calc (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (p21 hj) (p37 hj)
          (L (DivisorReduction.rTD hj)) hpr).length
        = mbsLen (ofMarkedSequence
            (L (DivisorReduction.rTD hj))) := h
      _ = _a1 :=
          ofMarkedSequence_length _
  rw [heq hmk]
  intro i hi
  rw [toMarkedSequence_length, toMarkedBlowupSequenceData_length,
    prepend_length, hlen] at hi
  simp
  cases i with
  | zero =>
    rw [prepend_center_zero]
    refine mpr_ nonempty_iff_ne_empty ?_
    intro hE
    exact hZ $ mpr_ (eq_top_iff_support_eq_empty _) hE
  | succ k =>
    rw [prepend_center_succ]
    have hcenter : (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian T j hj
          (p21 hj) (p37 hj)
          (L (DivisorReduction.rTD hj)) hpr).center k
        = imageIdealSheaf (embeddingIntoAmbientBlowupSequence (bgetT hj).si
            (ofMarkedSequence
              (L (DivisorReduction.rTD hj))).toBlowupSequenceData
            hres blowupPreservesNoetherian hpr k)
          ((L (DivisorReduction.rTD hj)).center k) := by
      have h := ambientBlowupSequence_center (bgetT hj).si
        (ofMarkedSequence (L (DivisorReduction.rTD hj))).toBlowupSequenceData
        hres blowupPreservesNoetherian hpr k
      simp at h
      exact h
    rw [hcenter]
    exact support_imageIdealSheaf_nonempty _
      (isClosedImmersion_embeddingIntoAmbientBlowupSequence (bgetT hj).si
        (ofMarkedSequence (L (DivisorReduction.rTD hj))).toBlowupSequenceData
        hres blowupPreservesNoetherian hpr k) _
      (hL.center_nonempty (DivisorReduction.rTD hj) hvalid (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcsne j hj (p21 hj) (p37 hj)) hdim) k (lt_of_succ_lt_succ hi))

theorem divisorFamily_canonicalAlgorithmRules_center_nonempty :
    ∀ i < ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
      ((((canonicalAlgorithmRules hres).divisorFamily L j T).center i).support :
        Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt i)).Nonempty := by
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
  exact DivisorReduction.divisorReductionSeq_center_nonempty hres hfacts n L O hL j T hV hdim hO hD hj
end





section
variable {S X} (ι) [IsClosedImmersion ι]
theorem isPushforwardBlowupSeq_of_ofSequenceOfBlowups
    (B : SequenceOfBlowups S) (B' : SequenceOfBlowups X)
    (h : IsPushforwardBlowupSeq ι (ofSequenceOfBlowups B).toSequenceOfBlowups B') : IsPushforwardBlowupSeq ι B B' := by
  unfold IsPushforwardBlowupSeq at h ⊢
  simp [toSequenceOfBlowups_blowupMorphism] at h
  exact h

theorem isPushforwardSequenceOfBlowups_of_length_eq_zero (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hlenZero : BS.length = 0) (hB : B.length = 0) :
    IsPushforwardBlowupSeq ι BS B := by
  have key : ∀ i, i ≤ BS.length → i = 0 := by
    intro i hi
    omega
  unfold IsPushforwardBlowupSeq
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt $ key i hi) ≫ sbIzH BS ≫ ι ≫ sbIzI B ≫
        eqToHom (congrArg B.schemeAt $ key i hi).symm, ?_, ?_, ?_, ?_, ?_⟩
  intro i _
  infer_instance
  simp
  simp_all
  simp_all
  simp_all
end

private theorem heq_toSequenceOfBlowups_of_eq (L : PrincipalizationAssignment) {A B : MarkedIdealWithBoundary} (h : A = B) :
    HEq (toSequenceOfBlowups $ L A) $ toSequenceOfBlowups $ L B := by
  subst h
  rfl

theorem isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (T : MarkedIdealWithBoundary) (s : T.SequenceOfBlowups)
    {Y : Sch} (ι : scheme T ⟶ Y) [IsClosedImmersion ι] (B : SequenceOfBlowups Y)
    (h : IsPushforwardBlowupSeq ι s.toBsd.toSequenceOfBlowups B) :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups B := by
  exact isPushforwardBlowupSeq_of_ofSequenceOfBlowups ι s.toSequenceOfBlowups B h

namespace DivisorReduction

section
variable (T : MarkedIdealWithBoundary) (j) (hj : j < T.boundary.length)
theorem restrictToDivisor_eq_withSchemeIdealBoundary
    (J : (T.bget j hj).subscheme.IdealSheafData)
    (him : ideal T = imageIdealSheaf (T.bget j hj).si J) :
    DivisorReduction.rD hj =
      T.withSchemeIdealBoundary (T.bget j hj).subscheme
        (subschemeι (T.bget j hj) ≫ structMap T) J
        (map (fun D => D.comap (T.bget j hj).si)
          (T.boundary.eraseIdx j)) := by
  let _a0 := T.bget j hj
  have h1 : (DivisorReduction.lowerIdealWithoutBlowup T).comap _a0.si = J := by
    unfold DivisorReduction.lowerIdealWithoutBlowup
    rw [comap_id, him]
    exact comap_map_of_isClosedImmersion _ J
  have h2 : map (fun D => D.comap _a0.si) (take (bLen T - 1) $ (lowerBoundaryWithoutBlowup T).eraseIdx j) = map (fun D => D.comap _a0.si) (T.boundary.eraseIdx j) := by
    unfold lowerBoundaryWithoutBlowup
    have h1 : map (fun D : tISD T => D.comap $ 𝟙 T.scheme) T.boundary
        = tBd T := by
      simp [comap_id]
    rw [h1]
    have hlen : lenL (T.boundary.eraseIdx j) = bLen T - 1 := by
      simp [length_eraseIdx, hj]
    rw [← hlen, take_length]
  unfold rD DivisorReduction.restrictToDivisor DivisorReduction.restrictToBoundaryDivisor withSchemeIdealBoundary
  rw [h1, h2]
end

end DivisorReduction

theorem isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment)
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ)
    (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : ∀ hft : LocallyOfFiniteType T.structMap, T.IsBalanced hft)
    (hj : j < T.boundary.length) (hm : T.mult = 1)
    (J : (T.bget j hj).subscheme.IdealSheafData)
    (hVJ : (T.withSchemeIdealBoundary (T.bget j hj).subscheme
        ((T.bget j hj).si ≫ T.structMap) J
        (map (fun D => D.comap (T.bget j hj).si)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hdimJ : (T.withSchemeIdealBoundary (T.bget j hj).subscheme
        ((T.bget j hj).si ≫ T.structMap) J
        (map (fun D => D.comap (T.bget j hj).si)
          (T.boundary.eraseIdx j))).krullDimSucc < T.krullDimSucc)
    (him : T.ideal = imageIdealSheaf (T.bget j hj).si J) :
    IsPushforwardBlowupSeq (T.bget j hj).si
      (L $ T.withSchemeIdealBoundary (T.bget j hj).subscheme
          ((T.bget j hj).si ≫ T.structMap) J
          (map (fun D => D.comap (T.bget j hj).si)
            (T.boundary.eraseIdx j))).toSequenceOfBlowups
      ((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups := by
  have :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  have hsub : (↑T.ideal.support) ⊆ orderAtLeastLocus T.ideal T.mult := by
    intro x hx
    rw [hm]
    exact mpr_ (mem_orderAtLeastLocus_one_iff T.ideal x) hx
  rw [hcs] at hsub
  have hsupp := mp_ subset_empty_iff hsub
  have hJtop : J = ⊤ := by
    have h2 : cmI (imageIdealSheaf (bgetT hj).si J)
        (bgetT hj).si = J :=
      p30 (bgetT hj).si J
    rw [← him, (eq_top_iff_support_eq_empty T.ideal).mpr hsupp] at h2
    rw [← h2]
    simp
  let _a1 := bget' hj
  have h0 : orderAtLeastLocus (⊤ : _a1.subscheme.IdealSheafData) 1
      = (∅ : CSet _a1.subscheme) := by
    simp [orderAtLeastLocus_top_eq_empty]
  let _a0 := siI (bgetT hj) ≫ tMp T
  have hcsJ : orderAtLeastLocus
      (T.withSchemeIdealBoundary (bget' hj).subscheme
        _a0 J
        (map (fun D => cmI D (bgetT hj).si)
          (T.boundary.eraseIdx j))).ideal
      (T.withSchemeIdealBoundary (bget' hj).subscheme
        _a0 J
        (map (fun D => cmI D (bgetT hj).si)
          (T.boundary.eraseIdx j))).mult =
      (∅ : Set ↥(T.withSchemeIdealBoundary (bget' hj).subscheme
        _a0 J
        (map (fun D => cmI D (bgetT hj).si)
          (T.boundary.eraseIdx j))).scheme) := by
    rwa [withSchemeIdealBoundary_ideal, withSchemeIdealBoundary_mult, hJtop, hm]
  exact isPushforwardSequenceOfBlowups_of_length_eq_zero _ _ _ (hL.trivial_of_coSupport_empty _ hVJ (lt_of_lt_of_le hdimJ hdim) hcsJ) $ divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO (hD hV.locallyOfFiniteType) hj hcs
  have hpretop :=
    hfacts.preIdeal_eq_top_of_imageIdeal T hV j hj J hm hVJ him
  rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO
      (hD hV.locallyOfFiniteType) hcs with
    ⟨-, hpr, hmk0, hstep⟩ | ⟨hne, -⟩
  have hT :=
    DivisorReduction.restrictToDivisor_eq_withSchemeIdealBoundary T j hj J him
  have hHeq := heq_toSequenceOfBlowups_of_eq L hT
  have hE := eq_of_heq hHeq
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq, hstep hmk0, ← hE,
    toMarkedBlowupSequenceData_toSequenceOfBlowups]
  have inst : IsClosedImmersion (bgetT hj).si := inferInstance
  let _a2 := DivisorReduction.rD hj
  exact @isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence _a2
    (L _a2) T.scheme
    (bgetT hj).si inst _
    (isPushforwardBlowupSeq_ambientBlowupSequence (bgetT hj).si
      (L _a2).toBsd
      hres blowupPreservesNoetherian hpr)
  exact absurd hpretop hne

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

section
variable (X : Sch)
theorem one_le_krullDimSucc [Nonempty ↥X] : 1 ≤ krullDimSucc X := by
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  have _i10 : topologicalKrullDim X ≠ ⊥ := by
    intro hb
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (Order.krullDim_eq_bot_iff.mp hb).false ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp _i10
  rw [← hn, withBotSuccToNat_coe]
  exact le_add_left 1 _

theorem krullDimSucc_eq_zero_of_isEmpty [IsEmpty ↥X] : krullDimSucc X = 0 := by
  have hE : IsEmpty $ IrreducibleCloseds X := by
    constructor
    intro C
    obtain ⟨x, -⟩ := C.2.1
    exact isEmptyElim x
  have h : topologicalKrullDim X = ⊥ := Order.krullDim_eq_bot_iff.mpr hE
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, h, withBotSuccToNat_bot]
end

section
variable {X : Sch} (D : ISD X)
theorem nonempty_homeomorph_subscheme_range_subschemeio :
    Nonempty $ ↥D.subscheme ≃ₜ ↥(range ⇑D.si) :=
  ⟨(isClosedEmbedding D.si).toIsEmbedding.toHomeomorph⟩

theorem isClosed_range_subschemeio :
    IsClosed $ range ⇑D.si :=
  (isClosedEmbedding D.si).isClosed_range
end

theorem krullDimSucc_subscheme_lt_of_isLocallyGeneratedByNonZeroDivisor (X : Sch) [Nonempty ↥X]
    (hfin : topologicalKrullDim ↥X < ⊤) (D : ISD X) (hD : IsLocallyGeneratedByNonZeroDivisor D) :
    krullDimSucc D.subscheme < krullDimSucc X := by
  rcases isEmpty_or_nonempty D.subscheme with hem | hne
  rw [krullDimSucc_eq_zero_of_isEmpty D.subscheme]
  exact lt_of_lt_of_le Nat.zero_lt_one $ one_le_krullDimSucc X
  obtain ⟨e⟩ := nonempty_homeomorph_subscheme_range_subschemeio D
  refine krullDimSucc_lt_of_homeomorph_isClosed X D.subscheme (range D.si)
    (isClosed_range_subschemeio D) (range_nonempty _) ?_ hfin e
  intro C hC hsub
  rw [q5 D] at hsub
  exact hD.not_irreducibleComponent_subset_support hC hsub

theorem isOpen_setOf_connectedComponent_subset {X : Type} [TopologicalSpace X]
    [NoetherianSpace X] P : IsOpen {x : X | connectedComponent x ⊆ P} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨connectedComponent x, ?_, isOpen_connectedComponent_of_noetherianSpace X x,
    mem_connectedComponent⟩
  intro y hy
  show connectedComponent y ⊆ P
  rwa [← connectedComponent_eq hy]

section
variable (T : MarkedIdealWithBoundary)
theorem isOpen_setOf_connectedComponent_subset_orderAtLeastLocus (hV : T.IsAdmissible) j
    (hj : j < T.boundary.length) :
    IsOpen {x : ↥(T.bget j hj).subscheme |
      connectedComponent x ⊆
        ⇑(T.bget j hj).si ⁻¹' orderAtLeastLocus T.ideal T.mult} := by
  have := hV.isNoetherian
  obtain ⟨e⟩ := nonempty_homeomorph_subscheme_range_subschemeio $ bget' hj
  have :=
    noetherianSpace_of_surjective _ e.symm.continuous e.symm.surjective
  exact isOpen_setOf_connectedComponent_subset _

theorem dim_restrictToBoundaryDivisor_lt (hV : T.IsAdmissible)
    (hne : (orderAtLeastLocus T.ideal T.mult).Nonempty) j (hj : j < T.boundary.length)
    I0 E0 :
    (DivisorReduction.restrictToBoundaryDivisor T j hj I0 E0).krullDimSucc < T.krullDimSucc := by
  obtain ⟨x, -⟩ := hne
  have : Nonempty T.scheme := ⟨x⟩
  have _i13 : bget' hj ∈ tBd T := by
    simp
  exact krullDimSucc_subscheme_lt_of_isLocallyGeneratedByNonZeroDivisor T.scheme
    hV.topologicalKrullDim_lt_top (bget' hj) (hV.snc.1 _ _i13).1
end

end FunctorialResolution.EmbeddedResolution

end
section
universe v


namespace FunctorialResolution.EmbeddedResolution

section
variable {Y : Sch}
section
variable {ι : Sort v} (J : ι → ISD Y)
noncomputable def iSupIdealSheaf :
    Y.IdealSheafData where
  ideal U := ⨆ i, (J i).ideal U
  map_ideal_basicOpen := by
    intro U f
    simp only [Ideal.map_iSup]
    exact iSup_congr fun i => (J i).map_ideal_basicOpen U f

theorem pointwiseSup_ideal
    (U : Y.affineOpens) : (iSupIdealSheaf J).ideal U = ⨆ i, (J i).ideal U := rfl

end

theorem idealSheafData_mul_le_mul_left (F : ISD Y)
    {A B : ISD Y} (h : A ≤ B) : F * A ≤ F * B := by
  refine mpr_ le_def fun U => ?_
  have e1 : (F * A).ideal U = F.ideal U * A.ideal U := rfl
  have e2 : (F * B).ideal U = F.ideal U * B.ideal U := rfl
  rw [e1, e2]
  exact mul_mono le_rfl $ mp_ le_def h U
end

section
variable (k : Type)
section
variable [CommRing k] [IsNoetherianRing k] {Y : Sch} (p) [LocallyOfFiniteType p] (P : ISD Y)
theorem logDerivIdealSheaf_iSup_le
    {ι : Sort v} (J : ι → ISD Y) :
    logDerivIdealSheaf k p P (⨆ i, J i) ≤ ⨆ i, logDerivIdealSheaf k p P (J i) := by
  refine mpr_ le_def fun U => ?_
  let _a0 := ⨆ i, J i
  have _i14 : _a0.ideal U ≤ ⨆ i, (J i).ideal U := by
    have h : _a0 ≤ iSupIdealSheaf J := by
      refine iSup_le fun i => mpr_ le_def fun V => ?_
      rw [pointwiseSup_ideal J V]
      exact le_iSup (fun i' => (J i').ideal V) i
    have h2 := mp_ le_def h U
    rwa [pointwiseSup_ideal J U] at h2
  refine le_trans (@logDerivIdeal_mono k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) _ _
    _i14) ?_
  exact le_trans (@logDerivIdeal_iSup_le k _ _ _ (sectionsAlgebra k p U.1) ι (P.ideal U)
    (fun i => (J i).ideal U)) $ iSup_le fun i => mp_ le_def (le_iSup (fun i' => logDerivIdealSheaf k p P $ J i') i) U

theorem logDerivIdealSheafIterate_iSup_le (r : ℕ)
    {ι : Sort v} (J : ι → ISD Y) :
    logDerivIdealSheafIterate k p P r (⨆ i, J i) ≤ ⨆ i, logDerivIdealSheafIterate k p P r (J i) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      have h1 : logDerivIdealSheafIterate k p P (r + 1) (⨆ i, J i)
          ≤ ⨆ i, logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r (J i)) := by
        rw [logDerivIdealSheafIterate_succ]
        exact le_trans (logDerivIdealSheaf_mono k p P ih)
          (logDerivIdealSheaf_iSup_le k p P
            (fun i => logDerivIdealSheafIterate k p P r (J i)))
      exact h1.trans (iSup_le fun i => le_iSup_of_le i (le_of_eq (logDerivIdealSheafIterate_succ k p P r (J i)).symm))

theorem logDerivIdealSheafIterate_biSup_le (r n : ℕ)
    (J : ℕ → ISD Y) :
    logDerivIdealSheafIterate k p P r (⨆ l, ⨆ _ : l ≤ n, J l) ≤
      ⨆ l, ⨆ _ : l ≤ n, logDerivIdealSheafIterate k p P r (J l) := by
  refine le_trans (logDerivIdealSheafIterate_iSup_le k p P r
    (fun l => ⨆ _ : l ≤ n, J l)) ?_
  refine iSup_le fun l => ?_
  exact le_trans (logDerivIdealSheafIterate_iSup_le k p P r fun _ => J l) $ iSup_le fun h => le_iSup_of_le l $ le_iSup_of_le h le_rfl
end

theorem derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup [Field k] [CharZero k] {X X1 : Sch}
    (p : X ⟶ Sp k) [Smooth p]
    (pi_ : X1 ⟶ X) [IsLocallyNoetherian X1]
    (Z H : ISD X) (E : Bdy X)
    [QuasiCompact (strictTransformio pi_ Z H)]
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
    (m : ℕ) (K : ℕ → ISD X) (hK : ∀ l ≤ m, K l ≤ Z ^ (m - l))
    (hest : ∀ n < m,
      derivIdealSheafIterate k p n (K 0) ≤
        ⨆ l, ⨆ _ : l ≤ n, logDerivIdealSheafIterate k p H (n - l) (K l))
    (K' : ℕ → ISD X1)
    (hK' : ∀ l ≤ m, exceptionalIdeal pi_ Z ^ (m - l) * K' l = (K l).comap pi_)
    (n : ℕ) (hn : n < m) :
    haveI : Smooth (pi_ ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
    derivIdealSheafIterate k (pi_ ≫ p) n (K' 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) (n - l) (K' l) := by
  have hsm := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hpi_
  show derivIdealSheafIterate k (pi_ ≫ p) n (K' 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) (n - l) (K' l)
  have hcart : p17 (p5 pi_ Z) := an1 hpi_
  have hK0 : K 0 ≤ Z ^ m := by simpa using hK 0 $ m67 m
  have hA : ∀ l, derivIdealSheafIterate k p l (K 0) ≤ Z ^ (m - l) := fun l =>
    derivIdealSheafIterate_le_pow_of_hasStrictNormalCrossingsWith k p Z (K 0) (H :: E) hsnc m hK0 l
  obtain ⟨L, hLspec⟩ : ∃ L, ∀ l,
      p5 pi_ Z ^ (m - l) * L l = cmI (derivIdealSheafIterate k p l (K 0)) pi_ :=
    ⟨fun l => controlledTransform pi_ Z (derivIdealSheafIterate k p l (K 0)) (m - l) hpi_ (hA l),
      fun l => exceptionalIdeal_pow_mul_controlledTransform pi_ Z (derivIdealSheafIterate k p l (K 0)) (m - l) hpi_ (hA l)⟩
  have hL0 : L 0 = K' 0 := by
    refine Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul (hcart.pow (m - 0)) ?_
    rw [hLspec 0, hK' 0 $ m67 m, derivIdealSheafIterate_zero]
  have hstep : ∀ l, l ≤ n → L l ≤
      ⨆ j, ⨆ _ : j ≤ l,
        logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) (l - j) (K' j) := by
    intro l hl
    have hlm : l < m := lt_of_le_of_lt hl hn
    have key : ∀ j, j ≤ l → cmI (logDerivIdealSheafIterate k p H (l - j) (K j)) pi_ ≤
        p5 pi_ Z ^ (m - l) *
          logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) (l - j) (K' j) := by
      intro j hj
      have hjm : j ≤ m := by omega
      have ha : l - j ≤ m - j := by omega
      have h3 := comap_logDerivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p pi_ Z H E hsnc hHZ hpi_
        (K j) (m - j) (hK j hjm) (l - j) ha
      have h4 : K' j = controlledTransform pi_ Z (K j) (m - j) hpi_ (hK j hjm) :=
        eq_controlledTransform_of_mul_eq_comap pi_ Z (K j) (m - j) hpi_ (hK j hjm) (K' j) (hK' j hjm)
      have harith : m - j - (l - j) = m - l := by omega
      rwa [h4, ← harith]
    refine Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_mul_le_mul (hcart.pow (m - l)) ?_
    rw [hLspec l]
    refine le_trans (comap_mono pi_ (hest l hlm)) ?_
    refine le_trans (le_of_eq (comap_iSup_le_nat pi_ l
      (fun j => logDerivIdealSheafIterate k p H (l - j) $ K j))) ?_
    exact iSup_le fun j => iSup_le fun hj => le_trans (key j hj) (idealSheafData_mul_le_mul_left _ (le_iSup_of_le j (le_iSup_of_le hj le_rfl)))
  have hmain := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_strictTransform
    k p pi_ Z H E hsnc hHZ hpi_ (K 0) m L (fun l _ => hLspec l) n hn.le
  rw [hL0] at hmain
  refine le_trans hmain $ iSup_le fun l => iSup_le fun hl => ?_
  refine le_trans (logDerivIdealSheafIterate_mono k (pi_ ≫ p) (p6 pi_ Z H) (n - l)
    (hstep l hl)) ?_
  refine le_trans (logDerivIdealSheafIterate_biSup_le k (pi_ ≫ p) (p6 pi_ Z H)
    (n - l) l
    (fun j => logDerivIdealSheafIterate k (pi_ ≫ p) (p6 pi_ Z H) (l - j) $ K' j)) ?_
  refine iSup_le fun j => iSup_le fun hj => ?_
  rw [← logDerivIdealSheafIterate_add]
  have harith3 : n - l + (l - j) = n - j := by omega
  rw [harith3]
  exact le_iSup_of_le j $ le_iSup_of_le (le_trans hj hl) le_rfl
end

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionBoundary

theorem mem_closeds_compl {al_ : Type} [TopologicalSpace al_]
    (S : TopologicalSpace.Closeds al_) x : x ∈ S.compl ↔ x ∉ S := m22

theorem saturation_top_eq_top {Y : Sch} F :
    saturation F (⊤ : ISD Y) = ⊤ := by
  have h := comap_le_strictTransform (𝟙 Y) F (⊤)
  rw [strictTransform_eq_saturation, comap_id,
    comap_id] at h
  exact mp_ top_le_iff h

private theorem restrictIdeal_mul {X : Sch} A B (U : Opn X) :
    restrictIdeal (A * B) U = restrictIdeal A U * restrictIdeal B U :=
  comap_mul A B U.i

theorem restrictIdeal_strictTransform_id {X : Sch} [IsLocallyNoetherian X]
    Z D (U : Opn X) :
    restrictIdeal (strictTransform (𝟙 X) Z D) U =
      saturation (restrictIdeal Z U) (restrictIdeal D U) := by
  have h2 := strictTransform_comp_io U (𝟙 U.toScheme) Z D
  rw [id_comp] at h2
  rw [restrictIdeal_strictTransform (𝟙 X) Z D U, comp_id, h2, strictTransform_eq_saturation, comap_id,
    comap_id]

theorem map_eq_self_of_getElem {al_ : Type} g : ∀ l : List al_,
    (∀ i (h : i < length l), g (l[i]'h) = l[i]'h) → l.map g = l
  | [], _ => rfl
  | a :: t, h => by
      have h0 : g a = a := h 0 $ succ_pos _
      rw [m75, h0, map_eq_self_of_getElem g t fun i hi => h (i + 1) $ succ_lt_succ hi]

theorem eraseIdx_map_eq {al_ : Type} g : ∀ (l : List al_) (j : ℕ),
    (∀ i (h : i < length l), i ≠ j → g (l[i]'h) = l[i]'h) →
    (l.map g).eraseIdx j = l.eraseIdx j
  | [], _, _ => rfl
  | _ :: t, 0, h => by
      have ht : t.map g = t :=
        map_eq_self_of_getElem g t
          (fun i hi => h (i + 1) (succ_lt_succ hi) $ succ_ne_zero i)
      show t.map g = t
      exact ht
  | a :: t, m + 1, h => by
      have h0 : g a = a := h 0 (succ_pos _) (succ_ne_zero m).symm
      have ht := eraseIdx_map_eq g t m
        (fun i hi hij => h (i + 1) (succ_lt_succ hi) fun e => hij $ by omega)
      show g a :: (t.map g).eraseIdx m = a :: t.eraseIdx m
      rw [h0, ht]

section
variable (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (j) (hj : j < T.boundary.length)
include hV
theorem strictTransform_comap_boundary_of_ne i (hi : i < T.boundary.length) (hij : i ≠ j) :
    strictTransform (𝟙 T.scheme) (DivisorReduction.ccI hj)
        ((T.bget i hi).comap $ 𝟙 T.scheme) = T.bget i hi := by
  let _a0 := bget' hi
  let _c0 := p28 hj
  have := hV.isNoetherian
  rw [comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ spI _c0
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  refine ⟨U, hxU, ?_⟩
  rw [restrictIdeal_strictTransform_id, hZU]
  cases hai : a i with
  | none =>
      rw [hnone i hi hai]
      exact saturation_top_eq_top _
  | some t =>
      have htb : t ≠ b := by
        intro e
        apply hij
        refine hinj i j hi hj b ?_ hab
        rw [hai, e]
      have ht := hsome i hi t hai
      have hq2 := quasiCompact_saturationio_restrictIdeal
        _c0 _a0 U
      rw [hZU, ht] at hq2
      have := hq2
      rw [ht]
      exact c.saturation_coordIdeal_of_ne t b htb
  refine ⟨suppC _c0,
    (mem_closeds_compl _ _).mpr hx, ?_⟩
  have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
    _c0 _a0
    (suppC _c0)
    (fun y hy => by
      simpa using ((mem_closeds_compl _ y).mp hy))
  rw [hst, comap_id]

theorem isSmoothDivisor_containedComponentsIdeal :
    IsSmoothDivisor T.structMap $ DivisorReduction.ccI hj :=
  ⟨isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj, smooth_subschemeio_containedComponentsIdeal_comp T hV j hj⟩

theorem strictTransform_mul_containedComponentsIdeal :
    strictTransform (𝟙 T.scheme) (DivisorReduction.ccI hj)
          ((T.bget j hj).comap (𝟙 T.scheme)) *
        DivisorReduction.ccI hj =
      T.bget j hj := by
  let _a0 := bget' hj
  let _c0 := p28 hj
  have := hV.isNoetherian
  rw [comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ spI _c0
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  refine ⟨U, hxU, ?_⟩
  have hDj := hsome j hj b hab
  have hq2 := quasiCompact_saturationio_restrictIdeal
    _c0 _a0 U
  rw [hZU, hDj] at hq2
  have := hq2
  rw [restrictIdeal_mul, restrictIdeal_strictTransform_id, hZU, hDj,
    c.saturation_coordIdeal_self b, top_mul]
  refine ⟨suppC _c0,
    (mem_closeds_compl _ _).mpr hx, ?_⟩
  have hZtop : restrictIdeal _c0
      (suppC _c0) = ⊤ := by
    have h := restrictIdeal_exceptionalIdeal_eq_top_of_notMem_support (𝟙 T.scheme)
      _c0 (suppC _c0)
      (fun y hy => by
        simpa using ((mem_closeds_compl _ y).mp hy))
    rwa [exceptionalIdeal_id] at h
  have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
    _c0 _a0
    (suppC _c0)
    (fun y hy => by
      simpa using ((mem_closeds_compl _ y).mp hy))
  rw [restrictIdeal_mul, hst, comap_id, hZtop,
    mul_top]

theorem disjoint_support_strictTransform_containedComponentsIdeal :
    Disjoint
      ((strictTransform (𝟙 T.scheme) (DivisorReduction.ccI hj)
          ((T.bget j hj).comap $ 𝟙 T.scheme)).support : CSet T.scheme)
      ((support (DivisorReduction.ccI hj) : CSet T.scheme)) := by
  have := hV.isNoetherian
  rw [comap_id, disjoint_right]
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  have hDj := hsome j hj b hab
  have hq2 := quasiCompact_saturationio_restrictIdeal
    (p28 hj) (bget' hj) U
  rw [hZU, hDj] at hq2
  have := hq2
  refine notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U ?_ x hxU
  rw [restrictIdeal_strictTransform_id, hZU, hDj]
  exact c.saturation_coordIdeal_self b

theorem take_eraseIdx_lowerBoundaryAfterBlowup :
    ((lB hj).eraseIdx j).take (T.boundary.length - 1) =
      T.boundary.eraseIdx j := by
  let _a0 := p28 hj
  have hlist : (T.boundary.map (cmI · $ 𝟙 tSch T)).map
        (p6 (𝟙 tSch T) _a0) =
      T.boundary.map fun D =>
        p6 (𝟙 tSch T) _a0 $ cmI D $ 𝟙 T.scheme := by simp_all
  have key := eraseIdx_map_eq
    (fun D : tISD T =>
      p6 (𝟙 tSch T) _a0 $ cmI D $ 𝟙 T.scheme)
    T.boundary j
    (fun i h hij => strictTransform_comap_boundary_of_ne T hV j hj i h hij)
  have hlen : j < lenL (T.boundary.map fun D =>
      p6 (𝟙 tSch T) _a0
        (cmI D $ 𝟙 T.scheme)) := by
    simpa using hj
  show ((((T.boundary.map (cmI · $ 𝟙 tSch T)).map
        (p6 (𝟙 tSch T) _a0)) ++
      [p5 (𝟙 tSch T) _a0]).eraseIdx j).take
      (bLen T - 1) = T.boundary.eraseIdx j
  rw [hlist, eraseIdx_append_of_lt_length hlen, key]
  exact take_left' $ length_eraseIdx_of_lt hj

theorem inStrictNormalCrossingPosition_comap_lowerBoundaryAfterBlowup :
    InStrictNormalCrossingPosition (subschemeι (T.bget j hj) ≫ structMap T)
      ((((lB hj).eraseIdx j).take $ T.boundary.length - 1).map
        fun D => D.comap (T.bget j hj).si) := by
  rw [take_eraseIdx_lowerBoundaryAfterBlowup T hV j hj]
  let hD : T.boundary[j]'hj = (bget' hj) := rfl
  subst hD
  exact inStrictNormalCrossingPosition_comap_subschemeio_eraseIdx (tMp T) (tBd T) hV.snc j hj
end

end DivisorReductionBoundary




section

variable (k : Type) [Field k] [CharZero k] {X S : Sch}
    (p) [Smooth p]
    (ι : S ⟶ X) [IsClosedImmersion ι]
    [Smooth $ ι ≫ p]

theorem base_mem_orderAtLeastLocus_of_mem_comap
    (m : ℕ) (hm : 1 ≤ m) (A : ISD X) (K : ℕ → ISD X)
    (hdom : derivIdealSheafIterate k p (m - 1) A
      ≤ ⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l))
    (hbal : ∀ l < m, K l ^ m ≤ A ^ (m - l))
    (y : S) (hy : y ∈ orderAtLeastLocus (A.comap ι) m) :
    ι.base y ∈ orderAtLeastLocus A m := by
  have hsupp : bsM ι y ∈
      support (⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)) := by
    refine mem_support_iSup_le_nat (m - 1)
      (fun l => logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)) (bsM ι y) ?_
    intro l hl
    have hlm : l < m := by omega
    have hml : 1 ≤ m - l := by omega
    apply mp_ (mem_support_comap)
    refine support_antitone
      (comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate k p ι (K l) (m - 1 - l)) ?_
    let _a0 := cmI (K l) ι
    have hpow : _a0 ^ m ≤ (cmI A ι) ^ (m - l) := by
      have h1 : (K l ^ m).comap ι ≤ (A ^ (m - l)).comap ι :=
        comap_mono ι (hbal l hlm)
      rwa [comap_pow, comap_pow] at h1
    let _a1 := ι ≫ p
    have hy2 :=
      orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le k _a1 _a0 (cmI A ι) l m hlm hpow hy
    rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k _a1 _a0 hml] at hy2
    have hexp : m - 1 - l = m - l - 1 := by omega
    rwa [hexp]
  rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p A hm]
  exact support_antitone hdom hsupp

end




def StrictNormalCrossingsLiftFromDivisor : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (P : Sch)
    (p : P ⟶ Sp k) [Smooth p]
    (H : ISD P) (N : Bdy P),
    InStrictNormalCrossingPosition p (H :: N) →
    ∀ Z : H.subscheme.IdealSheafData,
      HasStrictNormalCrossingsWith (subschemeι H ≫ p) Z (N.map fun D => D.comap H.si) →
      HasStrictNormalCrossingsWith p (imageIdealSheaf H.si Z) (H :: N)

section
variable {k : Type} [Field k] {Y : Sch} (p q) [LocallyOfFiniteType p] [LocallyOfFiniteType q] (h : p = q)
include h
theorem derivIdealSheafIterate_congr (r : ℕ) (J : ISD Y) :
    derivIdealSheafIterate k p r J = derivIdealSheafIterate k q r J := by
  subst h
  rfl

theorem logDerivIdealSheafIterate_congr (P : ISD Y) (r : ℕ) (J : ISD Y) :
    logDerivIdealSheafIterate k p P r J = logDerivIdealSheafIterate k q P r J := by
  subst h
  rfl
end

theorem imageIdealSheaf_hom_eq_comap_inv {A B : Sch} (e : A ≅ B) (J : ISD A) :
    imageIdealSheaf e.hom J = J.comap e.inv := by
  rw [imageIdealSheaf_eq_comap_inv e.hom J,
    CategoryTheory.IsIso.Iso.inv_hom]

namespace DivisorReduction

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme]
section
variable (j) (hj : j < T.boundary.length) (I0) (E0) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups) (hpr : s.NoComp)
theorem structureMorphism_ambientBlowupSeq_zero :
    ambM hres hno hpr 0 = T.structMap := by
  have h0 : (amb hres hno hpr).projectionToBase 0 ≫ tMp T = tMp T := by
    rw [p23]
    exact id_comp T.structMap
  exact h0

theorem ambientBlowupSeq_boundary_zero :
    (amb hres hno hpr).boundaryFrom E0 0 = E0 := by
  rw [BlowupSequenceData.boundary_zero]
  show map (fun D : tISD T =>
      cmI D $ id T.scheme) E0 = E0
  simp

theorem ker_embeddingIntoAmbient_zero_eq_boundary_get :
    ker (embA hres hno hpr 0) = T.bget j hj := by
  rw [embeddingIntoAmbient_zero hres hno T j hj I0 E0 s hpr]
  exact tr_ (ker_comp_of_isIso s.isoZero.hom (bgetT hj).si)
    (q2 _)

section
variable (t : ℕ)
theorem le_length_imp_isNoetherian_ambientBlowupSeq_schemeAt :
    t ≤ s.length →
      IsNoetherian ((amb hres hno hpr).obj t) := by
  let _c0 := amb hres hno hpr
  induction t with
  | zero =>
      intro _
      exact isNoetherian_of_iso _c0.isoZero.symm
  | succ n ih =>
      intro ht
      have hn := ht
      have :=
        ih $ le_of_lt hn
      have hlen := hn
      rw [← ambientBlowupSeq_length hres hno T j hj I0 E0 s hpr] at hlen
      exact isNoetherian_of_isBlowupAlongIdealSheaf $ _c0.isBlowup n hlen

theorem isNoetherian_ambientBlowupSeq_schemeAt (ht : t ≤ s.length) :
    IsNoetherian $ (amb hres hno hpr).obj t :=
  le_length_imp_isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I0 E0 s hpr t ht

theorem ker_embeddingIntoAmbient_le_center :
    ker (embA hres hno hpr t) ≤
      (amb hres hno hpr).center t := by
  let _a0 := embA hres hno hpr t
  let _m0 := _a0
  have key : m149 _m0 ≤
      ker (siI (s.center t) ≫
        _a0) := by
    apply le_ker_comp
  have h2 := sy_ $ imageIdealSheaf_eq_ker_subschemeio_comp
    _m0 $ s.center t
  exact le_of_le_of_eq key $ tr_ h2 $ sy_ $ ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I0 E0 s hpr t
end
end

section
variable [Smooth T.structMap] [LocallyOfFiniteType T.structMap] (j) (hj : j < T.boundary.length) (I0) (E0) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups) (hpr : s.NoComp)
theorem ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate (l : ℕ) :
    aDI hres hno hpr l 0 =
      derivIdealSheafIterate T.base T.structMap l I0 := by
  unfold aDI ambientDerivIdeal
  rw [p53]
  let _a0 := derivIdealSheafIterate T.base T.structMap l I0
  show cmI _a0
      (id tSch T) =
    _a0
  simp

theorem ambientDerivIdeal_order_zero_eq_controlledTransform (t : ℕ) :
    aDI hres hno hpr 0 t =
      (amb hres hno hpr).controlledTransform I0 T.mult t := rfl
end
end

structure GoingUpInvariant (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary)
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length)
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups)
    (hpr : s.NoComp) (t : ℕ) : Prop where
  divDeriv : ∀ l ≤ T.mult, ∀ i < t,
    ∃ B : ((amb hres hno hpr).obj (i + 1)).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map i)
          ((amb hres hno hpr).center i) ^ (T.mult - l) * B =
        (aDI hres hno hpr l i).comap
          ((amb hres hno hpr).map i)
  idx_lt : j < length ((amb hres hno hpr).boundaryFrom E0 t)
  deriv_le : ∀ [_hsmooth : Smooth
        (ambM hres hno hpr t)]
      [_instFt : LocallyOfFiniteType
        (ambM hres hno hpr t)], ∀ n < T.mult,
      derivIdealSheafIterate T.base (ambM hres hno hpr t) n
          ((amb hres hno hpr).controlledTransform I0 T.mult t) ≤
        ⨆ l ≤ n, logDerivIdealSheafIterate T.base
          (ambM hres hno hpr t)
          (ker (embA hres hno hpr t)) (n - l)
          (aDI hres hno hpr l t)
  comap_eraseIdx :
    map (fun D => D.comap (embA hres hno hpr t))
        (((amb hres hno hpr).boundaryFrom E0 t).eraseIdx j) = s.boundary t
  snc_bdry : InStrictNormalCrossingPosition (ambM hres hno hpr t)
      ((amb hres hno hpr).boundaryFrom E0 t)
  bdry_getElem : ((amb hres hno hpr).boundaryFrom E0 t)[j]'idx_lt =
      ker (embA hres hno hpr t)
  smooth_structMap :
    Smooth (ambM hres hno hpr t)

namespace GoingUpInvariant

section
variable {hres : StrictTransformIsBlowupOfClosedSubscheme} {hno : BlowupPreservesNoetherian} {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] {j} {hj : j < T.boundary.length} {I0} {E0} {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups} {hpr : s.NoComp} {t} (hgoingUp : GoingUpInvariant hres hno T j hj I0 E0 s hpr t)
include hgoingUp
theorem exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform :
    ∀ i < t, ∃ B : ((amb hres hno hpr).obj (i + 1)).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map i)
          ((amb hres hno hpr).center i) ^ T.mult * B =
        ((amb hres hno hpr).controlledTransform I0 T.mult i).comap
          ((amb hres hno hpr).map i) := by
  intro i hi
  obtain ⟨B, hB⟩ := hgoingUp.divDeriv 0 (m67 T.mult) i hi
  refine ⟨B, ?_⟩
  rw [← ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I0 E0 s hpr i, ← hB, m130]

theorem comap_controlledTransform (ht : t ≤ s.length) :
    ((amb hres hno hpr).controlledTransform I0 T.mult t).comap
        (embA hres hno hpr t) = s.ideal t :=
  FunctorialResolution.EmbeddedResolution.DivisorReduction.comap_controlledTransform_embeddingIntoAmbient hres hno T j hj I0 E0 s hpr t ht hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform
end

private theorem smooth_of_eq {A B : Sch} {f g : A ⟶ B} (h : f = g)
    (hg : Smooth g) : Smooth f := by
  rwa [h]

theorem support_center_subset_orderAtLeastLocus {hres : StrictTransformIsBlowupOfClosedSubscheme}
    {hno : BlowupPreservesNoetherian} {T : MarkedIdealWithBoundary}
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I0 : T.scheme.IdealSheafData} {E0 : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups}
    {hpr : s.NoComp} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I0 E0 s hpr t)
    (hbal : IsDerivBalanced T.base T.structMap I0 T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible) (ht : t < s.length) :
    (↑((amb hres hno hpr).center t).support :
        Set ↥((amb hres hno hpr).obj t)) ⊆
      orderAtLeastLocus ((amb hres hno hpr).controlledTransform I0 T.mult t) T.mult := by
  have hsmP :=
    hgoingUp.smooth_structMap
  let _a2 := ambM hres hno hpr t
  have hftP : LocallyOfFiniteType
      _a2 := inferInstance
  let _a0 := amb hres hno hpr
  let _a1 := embA hres hno hpr t
  let _a3 := (_a1 ≫ _a0.projectionToBase t) ≫ tMp T
  have hstep1 : _a1 ≫
        _a2
      = _a3 :=
    (assoc _ _ _).symm
  have hstep2 : _a3
      = (s.projectionToBase t ≫ divisorEmbedding T j hj I0 E0) ≫ tMp T :=
    congrArg (fun f : (ofMarkedSequence s).obj t ⟶ tSch T => f ≫ tMp T)
      (embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I0 E0 s hpr t)
  have hstep3 :=
    (assoc _ _ _).trans (projectionToSpec_eq s t).symm
  have hsmE :=
    smooth_of_eq (tr_ hstep1 $ tr_ hstep2 hstep3)
      (MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s t $ le_of_lt ht)
  have hbal' : ∀ l < tMu T,
      aDI hres hno hpr l t ^ T.mult ≤
        _a0.controlledTransform I0 T.mult t ^ (tMu T - l) := by
    intro l hl
    exact pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I0 E0 s hpr hbal l hl t
      (le_of_lt ht) hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform fun i hi => hgoingUp.divDeriv l (le_of_lt hl) i hi
  intro x hx
  rw [support_ambientBlowupSeq_center_eq_image hres hno T j hj I0 E0 s hpr t] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : y ∈ orderAtLeastLocus (s.ideal t) T.mult := by
    exact (s.center_order t ht) hy
  have hy2 := hy1
  rw [← hgoingUp.comap_controlledTransform $ le_of_lt ht] at hy2
  exact base_mem_orderAtLeastLocus_of_mem_comap T.base
    _a2
    _a1 T.mult hm
    (_a0.controlledTransform I0 T.mult t)
    (fun l => aDI hres hno hpr l t) (hgoingUp.deriv_le (T.mult - 1) $ by omega) hbal' y hy2

theorem exists_iso_ker_subschemeio {S X : Sch} (f : S ⟶ X)
    [IsClosedImmersion f] :
    ∃ e : S ≅ subscheme (ker f),
      hom e ≫ subschemeι (ker f) = f :=
  ⟨asIso f.toImage, f.toImage_imageι⟩

private theorem imageIdealSheaf_comp {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C)
    (J : ISD A) :
    imageIdealSheaf g (imageIdealSheaf f J) = imageIdealSheaf (f ≫ g) J :=
  (map_comp J f g).symm

theorem hasStrictNormalCrossingsWith_imageIdealSheaf_of_restriction {k : Type} [Field k] [CharZero k]
    {P S : Sch}
    (p : P ⟶ Sp k) [Smooth p]
    (ι : S ⟶ P) [IsClosedImmersion ι]
    (q : S ⟶ Sp k) (hq : ι ≫ p = q)
    (Zs : ISD S) (Bs : Bdy S) (N : Bdy P)
    (hN : map (fun D : ISD P => D.comap ι) N = Bs)
    (hsnc : InStrictNormalCrossingPosition p (ker ι :: N))
    (hlow : HasStrictNormalCrossingsWith q Zs Bs)
    (hlift : StrictNormalCrossingsLiftFromDivisor) :
    HasStrictNormalCrossingsWith p (imageIdealSheaf ι Zs) (ker ι :: N) := by
  obtain ⟨e, he⟩ := exists_iso_ker_subschemeio ι
  have hinv : isoI e ≫ ι = (ker ι).si := by
    have h := congrArg (fun m => isoI e ≫ m) he.symm
    simpa using h
  have hlist : map (fun D : ISD S => D.comap e.inv) Bs
      = map (fun D : ISD P =>
          D.comap (ker ι).si) N := by
    rw [← hN, map_map]
    refine map_congr_left ?_
    intro D _
    show (D.comap ι).comap e.inv = D.comap (ker ι).si
    rw [← hinv]
    simp
  have hZ : HasStrictNormalCrossingsWith ((ker ι).si ≫ p) (Zs.comap e.inv)
      (map (fun D : ISD P =>
        D.comap (ker ι).si) N) := by
    have h := hasStrictNormalCrossingsWith_comap_iso q e.symm Zs Bs hlow
    simp [Iso.symm_hom] at h
    rwa [← hq, ← assoc, hinv, hlist] at h
  have hfin := hlift k P p (ker ι) N hsnc (Zs.comap e.inv) hZ
  rwa [← imageIdealSheaf_hom_eq_comap_inv e Zs, imageIdealSheaf_comp e.hom _ Zs, he] at hfin

section
variable {hres : StrictTransformIsBlowupOfClosedSubscheme} {hno : BlowupPreservesNoetherian} {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] [CharZero T.base] {j} {hj : j < T.boundary.length} {I0} {E0} {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups} {hpr : s.NoComp} {t} (hgoingUp : GoingUpInvariant hres hno T j hj I0 E0 s hpr t)
include hgoingUp
section
variable (hlift : StrictNormalCrossingsLiftFromDivisor) (ht : t < s.length)
include hlift ht
theorem hasStrictNormalCrossingsWith_center_ker_cons :
    HasStrictNormalCrossingsWith (ambM hres hno hpr t)
      ((amb hres hno hpr).center t)
      (ker (embA hres hno hpr t) ::
        ((amb hres hno hpr).boundaryFrom E0 t).eraseIdx j) := by
  have hsmooth :=
    hgoingUp.smooth_structMap
  let _a0 := (amb hres hno hpr).boundaryFrom E0 t
  let _a1 := ambM hres hno hpr t
  let _a2 := embA hres hno hpr t
  have hsnccons : InStrictNormalCrossingPosition _a1
      (m149 _a2 ::
        _a0.eraseIdx j) := by
    have h1 := inStrictNormalCrossingPosition_moveToFront _a1
      _a0 j hgoingUp.idx_lt hgoingUp.snc_bdry
    rwa [moveToFront_eq_cons _ _ hgoingUp.idx_lt, hgoingUp.bdry_getElem] at h1
  have hstep2 :=
    congrArg (fun f : (ofMarkedSequence s).obj t ⟶ tSch T => f ≫ tMp T)
      (embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I0 E0 s hpr t)
  have hstep3 :=
    (assoc _ _ _).trans (projectionToSpec_eq s t).symm
  have hq :=
    (sy_ (assoc _ _ _)).trans (tr_ hstep2 hstep3)
  have hlow : HasStrictNormalCrossingsWith (s.projectionToSpec t) (s.center t) (s.boundary t) := by
    rw [projectionToSpec_eq]
    exact s.center_snc t ht
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I0 E0 s hpr t]
  exact hasStrictNormalCrossingsWith_imageIdealSheaf_of_restriction _a1
    _a2 (s.projectionToSpec t) hq (s.center t)
    (s.boundary t) (_a0.eraseIdx j)
    hgoingUp.comap_eraseIdx hsnccons hlow hlift

theorem hasStrictNormalCrossingsWith_center_boundary :
    HasStrictNormalCrossingsWith (ambM hres hno hpr t)
      ((amb hres hno hpr).center t)
      ((amb hres hno hpr).boundaryFrom E0 t) := by
  have hcons := hasStrictNormalCrossingsWith_center_ker_cons hgoingUp hlift ht
  let _a0 := amb hres hno hpr
  refine hasStrictNormalCrossingsWith_of_moveToFront (ambM hres hno hpr t)
      (_a0.center t)
      (_a0.boundaryFrom E0 t) j hgoingUp.idx_lt ?_
  rwa [moveToFront_eq_cons _ j hgoingUp.idx_lt, hgoingUp.bdry_getElem]
end

section
variable (hbal : IsDerivBalanced T.base T.structMap I0 T.mult) (hm : 1 ≤ mult T) (hV : (restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor) (ht : t < s.length) (l) (hl : l ≤ mult T)
include hbal hm hV hlift ht hl
theorem exists_pow_mul_eq_comap_ambientDerivIdeal :
    ∃ B : ((amb hres hno hpr).obj (t + 1)).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map t)
          ((amb hres hno hpr).center t) ^ (T.mult - l) * B =
        (aDI hres hno hpr l t).comap
          ((amb hres hno hpr).map t) := by
  let _c0 := amb hres hno hpr
  rcases hl.lt_or_eq with hlt | h
  have hsmth := hgoingUp.smooth_structMap
  have hnoe :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I0 E0 s hpr (t + 1) ht
  have hpow := pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I0 E0 s hpr hbal l hlt t
    (le_of_lt ht) hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform $ hgoingUp.divDeriv l hl
  have hcos := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
    (_c0.projectionToBase t ≫ tMp T)
    (aDI hres hno hpr l t)
    (_c0.controlledTransform I0 T.mult t) l T.mult hlt hpow
  have hlen := ht
  rw [← ambientBlowupSeq_length hres hno T j hj I0 E0 s hpr] at hlen
  exact BlowupSequenceData.exists_pow_mul_eq_comap_controlledTransform _c0
    T.structMap (derivIdealSheafIterate T.base T.structMap l I0) (tMu T - l) t hlen
    (_c0.boundaryFrom E0 t) (hasStrictNormalCrossingsWith_center_boundary hgoingUp hlift ht) $ (support_center_subset_orderAtLeastLocus hgoingUp hbal hm hV ht).trans hcos
  simp_all

theorem ambientDerivIdeal_le_center_pow :
    aDI hres hno hpr l t ≤
      (amb hres hno hpr).center t ^ (T.mult - l) := by
  let _c0 := amb hres hno hpr
  rcases hl.lt_or_eq with hlt | h
  have hsmth := hgoingUp.smooth_structMap
  have hpow := pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I0 E0 s hpr hbal l hlt t
    (le_of_lt ht) hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform (hgoingUp.divDeriv l hl)
  let _a0 := aDI hres hno hpr l t
  let _a1 := ambM hres hno hpr t
  have hcos := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
    _a1
    _a0
    (_c0.controlledTransform I0 T.mult t) l T.mult hlt hpow
  exact le_pow_of_hasStrictNormalCrossingsWith _a1
    (_c0.center t)
    _a0
    (_c0.boundaryFrom E0 t) (hasStrictNormalCrossingsWith_center_boundary hgoingUp hlift ht)
    (tMu T - l) ((support_center_subset_orderAtLeastLocus hgoingUp hbal hm hV ht).trans hcos)
  simp_all
end
end

end GoingUpInvariant

theorem list_map_comap_map_comap_eq_map_comap_comp {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C)
    (L : Bdy C) :
    map (fun D : ISD B => D.comap f)
        (map (fun D : ISD C => D.comap g) L)
      = map (fun D : ISD C => D.comap $ f ≫ g) L :=by simp_all
end DivisorReduction





namespace DivisorReduction

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length) (I0) (E0) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups) (hpr : s.NoComp) (t : ℕ)
theorem structureMorphism_ambientBlowupSeq_succ :
    ambM hres hno hpr (t + 1) =
      (amb hres hno hpr).map t ≫
        ambM hres hno hpr t := by
  let _c0 := amb hres hno hpr
  show _c0.projectionToBase (t + 1) ≫ tMp T =
      _c0.map t ≫
        (_c0.projectionToBase t ≫ tMp T)
  rw [projectionToBase_succ, assoc]

theorem ker_embeddingIntoAmbient_succ (ht : t < s.length) :
    ker (embA hres hno hpr $ t + 1) =
      strictTransform ((amb hres hno hpr).map t)
        ((amb hres hno hpr).center t)
        (ker $ embA hres hno hpr t) :=
  ker_embeddingIntoAmbientBlowupSequence_succ (bgetT hj).si
    s.toBsd hres hno hpr t ht
end

namespace GoingUpInvariant

private theorem getElem_map_append_of_lt_length.{v, w} {al_ : Type v} {be_ : Type w} (f : al_ → be_)
    (M : List be_) (L : List al_) (i : ℕ) (hi : i < length L)
    (h : i < length (L.map f ++ M)) :
    (L.map f ++ M)[i]'h = f (L[i]'hi) :=by simp_all
theorem succ {hres : StrictTransformIsBlowupOfClosedSubscheme}
    {hno : BlowupPreservesNoetherian} {T : MarkedIdealWithBoundary}
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I0 : T.scheme.IdealSheafData} {E0 : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups}
    {hpr : s.NoComp} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I0 E0 s hpr t)
    (hbal : IsDerivBalanced T.base T.structMap I0 T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor)
    (ht : t < s.length) :
    GoingUpInvariant hres hno T j hj I0 E0 s hpr (t + 1) := by
  let _a3 := embA hres hno hpr t
  let _a4 := embA hres hno hpr $ t + 1
  have hlen :=
    ambientBlowupSeq_length hres hno T j hj I0 E0 s hpr
  have hblow :=
    (amb hres hno hpr).isBlowup t (by rw [hlen]; exact ht)
  have hNt1 :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I0 E0 s hpr (t + 1) (by omega)
  have hnoetherian : m86
      ((amb hres hno hpr).obj (t + 1)) := inferInstance
  have hLNt1 : IsLocallyNoetherian
      ((amb hres hno hpr).obj (t + 1)) := inferInstance
  let _a5 := s.toBsd.obj $ t + 1
  have hNs1 : IsNoetherian
      _a5 :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s (t + 1) (by omega)
  have hLNs1 : IsLocallyNoetherian
      _a5 := inferInstance
  have hsm : Smooth (ambM hres hno hpr t) :=
    hgoingUp.smooth_structMap
  have hsncZ :=
    hgoingUp.hasStrictNormalCrossingsWith_center_boundary hlift ht
  have hsncCons :=
    hgoingUp.hasStrictNormalCrossingsWith_center_ker_cons hlift ht
  have hkerle :=
    ker_embeddingIntoAmbient_le_center hres hno T j hj I0 E0 s hpr t
  have hkersucc :=
    ker_embeddingIntoAmbient_succ hres hno T j hj I0 E0 s hpr t ht
  have hps :=
    structureMorphism_ambientBlowupSeq_succ hres hno T j hj I0 E0 s hpr t
  have hsmc :=
    smooth_comp_of_isBlowupAlongIdealSheaf hsncZ hblow
  have hsmsucc : Smooth
      (ambM hres hno hpr (t + 1)) := by
    rw [hps]
    exact hsmc
  have hsncSucc : InStrictNormalCrossingPosition (ambM hres hno hpr (t + 1))
      ((amb hres hno hpr).boundaryFrom E0 (t + 1)) := by
    rw [hps, p52]
    exact inStrictNormalCrossingPosition_strictTransform_append
      (ambM hres hno hpr t)
      ((amb hres hno hpr).map t)
      ((amb hres hno hpr).center t)
      ((amb hres hno hpr).boundaryFrom E0 t) hblow hgoingUp.snc_bdry hsncZ
  have hidxt : j < lenL ((amb hres hno hpr).boundaryFrom E0 t) := hgoingUp.idx_lt
  have hidx : j < lenL ((amb hres hno hpr).boundaryFrom E0 (t + 1)) := by
    have h1 : lenL ((amb hres hno hpr).boundaryFrom E0 t) = lenL E0 + t :=
      boundary_length _ _ _
    have h2 : lenL ((amb hres hno hpr).boundaryFrom E0 (t + 1))
        = lenL E0 + (t + 1) := boundary_length _ _ _
    omega
  let _m0 := ((amb hres hno hpr).boundaryFrom E0 t).map (p6 ((amb hres hno hpr).map t) ((amb hres hno hpr).center t))
  have hmaplen : j < _m0.length := by
    rw [length_map]
    exact hidxt
  have hj2 : j < (_m0 ++
      [p5 ((amb hres hno hpr).map t)
        ((amb hres hno hpr).center t)]).length := by
    rw [length_append]
    omega
  have hget : ((amb hres hno hpr).boundaryFrom E0 (t + 1))[j]'hidx =
      _a4.ker := by
    rw [hkersucc, ← hgoingUp.bdry_getElem]
    refine tr_ (getElem_of_eq
      (p52 (amb hres hno hpr) E0 t) hidx) ?_
    exact getElem_map_append_of_lt_length
      (p6 ((amb hres hno hpr).map t)
        ((amb hres hno hpr).center t))
      [p5 ((amb hres hno hpr).map t)
        ((amb hres hno hpr).center t)]
      ((amb hres hno hpr).boundaryFrom E0 t) j hidxt hj2
  have hcen : ((amb hres hno hpr).center t).comap
      _a3 = s.center t := by
    rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I0 E0 s hpr t]
    exact p30
      _a3 (s.center t)
  have hB := map_comap_strictTransform_append_exceptionalIdeal
    (ambM hres hno hpr t)
    ((amb hres hno hpr).map t)
    ((amb hres hno hpr).center t)
    _a3
    _a4
    (s.transitionMapSucc t)
    (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I0 E0 s hpr t) hkersucc
    (((amb hres hno hpr).boundaryFrom E0 t).eraseIdx j) hsncCons hkerle hblow
  have hbdrysucc : map
      (·.comap _a4)
      (((amb hres hno hpr).boundaryFrom E0 (t + 1)).eraseIdx j) =
      s.boundary (t + 1) := by
    rw [p52, eraseIdx_append_of_lt_length hmaplen, eraseIdx_map, hB, hgoingUp.comap_eraseIdx, hcen]
    exact sy_ (s.boundary_succ t ht)
  have hKle : ∀ l, l ≤ tMu T →
      aDI hres hno hpr l t ≤
        (amb hres hno hpr).center t ^ (tMu T - l) :=
    fun l hl => hgoingUp.ambientDerivIdeal_le_center_pow hbal hm hV hlift ht l hl
  have hK' : ∀ l, l ≤ tMu T →
      p5 ((amb hres hno hpr).map t)
          ((amb hres hno hpr).center t) ^ (tMu T - l) *
          aDI hres hno hpr l (t + 1) =
        (aDI hres hno hpr l t).comap
          ((amb hres hno hpr).map t) := fun l hl =>
    pow_exceptionalIdeal_mul_controlledTransform_succ (amb hres hno hpr)
      (derivIdealSheafIterate T.base T.structMap l I0) (tMu T - l) t
      (hgoingUp.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift ht l hl)
  refine ⟨?_, hidx, ?_, hbdrysucc, hsncSucc, hget, hsmsucc⟩
  intro l hl i hi
  by_cases hit : i < t
  exact hgoingUp.divDeriv l hl i hit
  have hie : i = t := by omega
  rw [hie]
  exact hgoingUp.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift ht l hl
  intro hsmooth instFt n hn
  have hsmS := hsmooth
  have hftS := instFt
  have hest : ∀ m, m < tMu T →
      derivIdealSheafIterate T.base (ambM hres hno hpr t) m
          (aDI hres hno hpr 0 t) ≤
        ⨆ l ≤ m, logDerivIdealSheafIterate T.base
          (ambM hres hno hpr t)
          (_a3.ker) (m - l)
          (aDI hres hno hpr l t) := by
    intro m hm'
    rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
    exact hgoingUp.deriv_le m hm'
  have key := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
    T.base (ambM hres hno hpr t)
    ((amb hres hno hpr).map t)
    ((amb hres hno hpr).center t)
    (_a3.ker)
    (((amb hres hno hpr).boundaryFrom E0 t).eraseIdx j)
    hsncCons hkerle hblow T.mult
    (fun l => aDI hres hno hpr l t) hKle hest
    (fun l => aDI hres hno hpr l $ t + 1) hK' n hn
  have h0 : derivIdealSheafIterate T.base
        (ambM hres hno hpr (t + 1)) n
        ((amb hres hno hpr).controlledTransform I0 T.mult (t + 1)) =
      derivIdealSheafIterate T.base
        ((amb hres hno hpr).map t ≫
          ambM hres hno hpr t) n
        (aDI hres hno hpr 0 (t + 1)) := by
    rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
    exact derivIdealSheafIterate_congr
      (ambM hres hno hpr (t + 1))
      ((amb hres hno hpr).map t ≫
        ambM hres hno hpr t) hps n _
  refine le_trans (le_of_eq h0) $ le_trans key (le_of_eq ?_)
  rw [hkersucc]
  exact iSup_congr fun l => iSup_congr fun _ =>
    logDerivIdealSheafIterate_congr
      ((amb hres hno hpr).map t ≫
        ambM hres hno hpr t)
      (ambM hres hno hpr (t + 1)) hps.symm _ _ _

end GoingUpInvariant

end DivisorReduction





namespace BlowupSequenceData

theorem IsMarked.of_comap_isoObjZero_eq {k : Type} [Field k] {X : Sch}
    {d : BlowupSequenceData X} {p : X ⟶ Sp k} {m : ℕ}
    {I I' : ISD X} {E E' : Bdy X}
    (hI : I.comap d.isoZero.hom = I'.comap d.isoZero.hom)
    (hE : List.map (fun D => D.comap d.isoZero.hom) E =
      List.map (fun D => D.comap d.isoZero.hom) E')
    (h : d.IsMarked p I m E) : d.IsMarked p I' m E' := by
  have hIc := fun t =>
    d.controlledTransform_congr I I' (by rw [d.projectionToBase_zero]; exact hI) m t
  have hEc := fun t =>
    d.boundary_congr E E' (by simp [d.projectionToBase_zero]; exact hE) t
  refine ⟨?_, ?_, h.center_smooth, ?_⟩
  intro i hi
  rw [← hIc i]
  exact h.divisible i hi
  intro i hi
  rw [← hIc i]
  exact h.center_order i hi
  intro i hi
  rw [← hEc i]
  exact h.center_snc i hi

end BlowupSequenceData

namespace DivisorReduction

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] [CharZero T.base] (j) (hj : j < T.boundary.length) (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups) (hpr : s.NoComp) (hbal : IsDerivBalanced T.base T.structMap I0 T.mult) (hm : 1 ≤ mult T) (hV : (restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor) (hE0_ : InStrictNormalCrossingPosition T.structMap E0) (hjE : j < E0.length) (hget : E0[j] = T.boundary[j]) (htrunc : take (T.boundary.length - 1) (E0.eraseIdx j) = E0.eraseIdx j)
include hbal hm hV hlift hE0_ hjE hget htrunc
section
variable (t) (ht : t ≤ s.length)
include ht
theorem goingUpInvariant_of_le :
    GoingUpInvariant hres hno T j hj I0 E0 s hpr t := by
  induction t with
  | zero =>
    have hbd :=
      ambientBlowupSeq_boundary_zero hres hno T j hj I0 E0 s hpr
    have hsm :=
      structureMorphism_ambientBlowupSeq_zero hres hno T j hj I0 E0 s hpr
    have : @LocallyOfFiniteType
        ((amb hres hno hpr).obj 0)
        (Sp T.base) T.structMap :=
      ‹LocallyOfFiniteType T.structMap›
    have hctrl : (amb hres hno hpr).controlledTransform I0 T.mult 0 = I0 := by
      rw [p53]
      show cmI I0 (id T.scheme) = I0
      simp
    let _a1 := bget' hj
    refine
      { divDeriv := ?_
        idx_lt := by rw [hbd]
                     exact hjE
        deriv_le := ?_
        comap_eraseIdx := ?_
        snc_bdry := ?_
        bdry_getElem := ?_
        smooth_structMap := ?_ }
    simp_all
    intro _ _ n _
    have h1 : derivIdealSheafIterate T.base (ambM hres hno hpr 0) n
          ((amb hres hno hpr).controlledTransform I0 T.mult 0)
        = derivIdealSheafIterate T.base T.structMap n
          ((amb hres hno hpr).controlledTransform I0 T.mult 0) :=
      derivIdealSheafIterate_congr _ _ hsm n _
    have h2 : derivIdealSheafIterate T.base T.structMap n
          ((amb hres hno hpr).controlledTransform I0 T.mult 0)
        = derivIdealSheafIterate T.base T.structMap n I0 := by
      rw [hctrl]
    refine le_iSup₂_of_le n le_rfl ?_
    rw [sub_self, logDerivIdealSheafIterate_zero]
    exact le_of_eq $ tr_ h1 $ tr_ h2 $ (ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate hres hno T j hj I0 E0 s hpr n).symm
    rw [hbd, embeddingIntoAmbient_zero hres hno T j hj I0 E0 s hpr,
      MarkedSequenceOfBlowups.boundary_zero s]
    exact sy_ $ (congrArg (map fun D : tISD (restrictToBoundaryDivisor T j hj I0 E0) => D.comap s.isoZero.hom) $ rfl.trans $ congrArg (map fun D : tISD T => D.comap _a1.si) htrunc).trans $ list_map_comap_map_comap_eq_map_comap_comp s.isoZero.hom _a1.si $ E0.eraseIdx j
    rwa [hbd, hsm]
    rw [ker_embeddingIntoAmbient_zero_eq_boundary_get hres hno T j hj I0 E0 s hpr]
    simp [hbd]
    exact hget
    rw [hsm]
    exact ‹Smooth T.structMap›
  | succ n ih =>
      exact GoingUpInvariant.succ (ih $ le_of_succ_le ht) hbal hm hV hlift $ lt_of_succ_le ht

theorem comap_controlledTransform_ambientBlowupSeq :
    ((amb hres hno hpr).controlledTransform I0 T.mult t).comap
        (embA hres hno hpr t) = s.ideal t :=
  (goingUpInvariant_of_le hres hno T j hj I0 E0 s hpr hbal hm hV hlift hE0_ hjE hget htrunc
    t ht).comap_controlledTransform ht
end

end

private theorem lowerIdealWithoutBlowup_eq_ideal (T : MarkedIdealWithBoundary) :
    lowerIdealWithoutBlowup T = ideal T :=
  comap_id T.ideal

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (hlift : StrictNormalCrossingsLiftFromDivisor) (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) [IsNoetherian T.scheme]
include hlift hV
theorem isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ENat))
    (hbal : ∀ [_inst : LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult)
    (j : ℕ) (hj : j < T.boundary.length)
    (_hZ : ccI hj = ⊤)
    (hVlow : (rD hj).IsAdmissible)
    (s : (rD hj).SequenceOfBlowups)
    (hpr : s.NoComp) :
    (amb hres hno hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry := lowerBoundaryWithoutBlowup_eq T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]
                                                             exact hj
  have hE0_ : InStrictNormalCrossingPosition T.structMap $ lowerBoundaryWithoutBlowup T := by rw [hbdry]
                                                                                              exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = bLen T - 1 := by
    simp [length_eraseIdx, hj]
  have htrunc : take (bLen T - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by simp_all
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by simp_all
  have main : (amb hres hno hpr).IsMarked T.structMap (lowerIdealWithoutBlowup T) T.mult $ lowerBoundaryWithoutBlowup T := by
    let I0 := lowerIdealWithoutBlowup T
    let E0 := lowerBoundaryWithoutBlowup T
    let hget := hgetAll hjE
    have hlen :=
      ambientBlowupSeq_length hres hno T j hj I0 E0 s hpr
    refine ⟨?_, ?_, ?_, ?_⟩
    intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I0 E0 s hpr hbal' hV.one_le_mult hVlow hlift hE0_ hjE hget htrunc
      (i + 1) hi).exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform i $ lt_succ_self i
    intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I0 E0 s hpr hbal' hV.one_le_mult hVlow hlift hE0_ hjE hget htrunc
      i $ le_of_lt hi).support_center_subset_orderAtLeastLocus hbal' hV.one_le_mult hVlow hi
    intro i hi
    rw [hlen] at hi
    exact smooth_ambientBlowupSeq_center_comp hres hno T j hj I0 E0 s hpr i hi
    intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I0 E0 s hpr hbal' hV.one_le_mult hVlow hlift hE0_ hjE hget htrunc
      i $ le_of_lt hi).hasStrictNormalCrossingsWith_center_boundary hlift hi
  exact BlowupSequenceData.IsMarked.of_comap_isoObjZero_eq (by simp [lowerIdealWithoutBlowup_eq_ideal T]) (by simp [hbdry]) main

theorem comap_controlledTransform_of_containedComponentsIdeal_eq_top
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (mult T : ENat))
    (hbal : ∀ [_inst : LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult)
    j (hj : j < T.boundary.length)
    (_hZ : ccI hj = ⊤)
    (hVlow : (rD hj).IsAdmissible)
    (s : (rD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    t (ht : t ≤ s.length) :
    ((amb hres hno hpr).controlledTransform
        T.ideal T.mult t).comap
      (embA hres hno hpr t) = s.ideal t := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry := lowerBoundaryWithoutBlowup_eq T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]
                                                             exact hj
  have hE0_ : InStrictNormalCrossingPosition T.structMap $ lowerBoundaryWithoutBlowup T := by rw [hbdry]
                                                                                              exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = bLen T - 1 := by
    simp [length_eraseIdx, hj]
  have htrunc : take (bLen T - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by simp_all
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by simp_all
  have main := comap_controlledTransform_ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
    hbal' hV.one_le_mult hVlow hlift hE0_ hjE (hgetAll hjE) htrunc t ht
  have hc := BlowupSequenceData.controlledTransform_congr
    (amb hres hno hpr)
    (lowerIdealWithoutBlowup T) T.ideal (by simp [lowerIdealWithoutBlowup_eq_ideal T]) T.mult t
  rwa [← hc]
end

end DivisorReduction




namespace DivisorReduction

theorem orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    {S X : Sch} (ι : S ⟶ X) [IsClosedImmersion ι]
    (J : ISD X) m (h : orderAtLeastLocus (J.comap ι) m = ∅) :
    orderAtLeastLocus J m ∩ (↑(ker ι).support : Set ↥X) = ∅ := by
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hx hker
  have hmem : x ∈ closure (range ι.base) := by
    rwa [support_ker ι] at hker
  rw [((isClosedEmbedding ι).isClosed_range).closure_eq] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hyo : m ≤ orderAt (cmI J ι) y := by
    refine le_trans ?_ $ orderAt_le_orderAt_comap ι J y
    rwa [hy]
  have hy' : y ∈ orderAtLeastLocus (cmI J ι) m := hyo
  rwa [h] at hy'

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length)
theorem orderAtLeastLocus_inter_support_ker_eq_empty (s : (rD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hdiv : ∀ i < s.length,
      ∃ B : ((amb hres hno hpr).obj
          (i + 1)).IdealSheafData,
        exceptionalIdeal
            ((amb hres hno hpr).map i)
            ((amb hres hno hpr).center i) ^ T.mult *
            B =
          (((amb hres hno hpr).controlledTransform
              (lowerIdealWithoutBlowup T) T.mult i).comap
            ((amb hres hno hpr).map i)))
    (hempty : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
          ((amb hres hno hpr).controlledTransform
            T.ideal T.mult s.length)
          T.mult ∩
        (↑(ker
              (embA hres hno hpr
                s.length)).support :
          Set ↥((amb hres hno hpr).obj s.length)) =
      ∅ := by
  have hid : lowerIdealWithoutBlowup T = tId T := by simp_all
  have hcomap := comap_controlledTransform_embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
    s hpr s.length le_rfl hdiv
  refine orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    (embA hres hno hpr s.length) _ T.mult ?_
  rwa [congrArg (fun I => (amb hres hno hpr).controlledTransform I T.mult s.length) hid.symm, hcomap]

theorem orderAtLeastLocus_controlledTransform_inter_ker_support_eq_empty
    (hb : IsBlowupAlongIdealSheaf (id T.scheme) $ ccI hj)
    (s : (rTD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hdiv : ∀ i < s.length,
      ∃ B : ((amb hres hno hpr).obj
          (i + 1)).IdealSheafData,
        exceptionalIdeal
            ((amb hres hno hpr).map i)
            ((amb hres hno hpr).center i) ^
              T.mult * B =
          (((amb hres hno hpr).controlledTransform
              (lI hj) T.mult i).comap
            ((amb hres hno hpr).map i)))
    (hone :
      (prepend (ccI hj) hb
            (amb hres hno hpr)).controlledTransform
          T.ideal T.mult 1 =
        (lI hj).comap
          (amb hres hno hpr).isoZero.hom)
    (hempty : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
          ((prepend (ccI hj) hb
                (amb hres hno hpr)).controlledTransform
            T.ideal T.mult $ s.length + 1)
          T.mult ∩
        (↑(ker
              (embA hres hno hpr
                s.length)).support :
          Set ↥((amb hres hno hpr).obj
            s.length)) =
      ∅ := by
  let _a0 := lI hj
  have h1 := BlowupSequenceData.controlledTransform_prepend_succ (ccI hj) hb
    (amb hres hno hpr)
    T.ideal _a0 T.mult hone s.length
  have h2 := comap_controlledTransform_embeddingIntoAmbient hres hno T j hj _a0
    (lB hj) s hpr s.length le_rfl hdiv
  refine orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    (embA hres hno hpr s.length)
    _ T.mult ?_
  rwa [h1, h2]
end

end DivisorReduction




namespace DivisorReduction

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length)
abbrev pushedMarkedSeq
    (s : (rD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (amb hres hno hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    T.SequenceOfBlowups :=
  ((amb hres hno hpr).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups

abbrev prependedPushedMarkedSeq
    (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ ccI hj)
    (s : (rTD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (prepend (ccI hj) hb
        (amb hres hno hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    T.SequenceOfBlowups :=
  ((prepend (ccI hj) hb
        (amb hres hno hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups
end
noncomputable abbrev pMS (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] {j : ℕ} {hj : j < T.boundary.length} {s : (rD hj).SequenceOfBlowups} {hpr : s.NoComp} (hmk : (amb hres hno hpr).IsMarked T.structMap T.ideal T.mult T.boundary) := pushedMarkedSeq hres hno T j hj s hpr hmk
noncomputable abbrev ppMS (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] {j : ℕ} {hj : j < T.boundary.length} {hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) (ccI hj)} {s : (rTD hj).SequenceOfBlowups} {hpr : s.NoComp} (hmk : (prepend (ccI hj) hb (amb hres hno hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) := prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk

end DivisorReduction

structure PushedBlowupSequenceProperties (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hno : BlowupPreservesNoetherian) : Prop where
  isOpen_preimage_preIdeal :
    ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (j : ℕ) (hj : j < T.boundary.length),
      IsOpen $ ⇑(T.bget j hj).si ⁻¹'
        ((DivisorReduction.ccI hj).support : CSet T.scheme)
  ker_pushedEmb_zero_top :
    ∀ (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (s : (DivisorReduction.rD hj).SequenceOfBlowups)
      (hpr : s.NoComp)
      (hmk : (DivisorReduction.amb hres hno hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ker
          (DivisorReduction.embA hres hno hpr 0) =
        (T.bget j hj).comap
          (DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).isoZero.hom
  ker_pushedEmb_zero_pre :
    ∀ (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj)
      (s : (DivisorReduction.rTD hj).SequenceOfBlowups)
      (hpr : s.NoComp)
      (hmk : (prepend (DivisorReduction.ccI hj) hb
          (DivisorReduction.amb hres hno hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ker
          (DivisorReduction.embA hres hno hpr 0) =
        ((T.bget j hj).comap
            (DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom).comap
          ((DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0)
  isSmoothDivisor_boundary_comap :
    ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (j : ℕ) (hj : j < T.boundary.length) (S : T.SequenceOfBlowups),
      IsSmoothDivisor (S.projectionToSpec 0) $ (T.bget j hj).comap S.isoZero.hom
  boundaryLocus_subset_top :
    ∀ (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (s : (DivisorReduction.rD hj).SequenceOfBlowups)
      (hpr : s.NoComp)
      (hmk : (DivisorReduction.amb hres hno hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t < s.length,
        s.boundaryLocus t ⊆
          ⇑(DivisorReduction.embA hres hno hpr t) ⁻¹'
            ((DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).otherBoundaryLocus j t)
  boundaryLocus_subset_pre :
    ∀ (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj)
      (s : (DivisorReduction.rTD hj).SequenceOfBlowups)
      (hpr : s.NoComp)
      (hmk : (prepend (DivisorReduction.ccI hj) hb
          (DivisorReduction.amb hres hno hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t < s.length,
        s.boundaryLocus t ⊆
          ⇑(DivisorReduction.embA hres hno hpr t) ⁻¹'
            ((DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).otherBoundaryLocus j $ t + 1)
  one_le_mult : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → 1 ≤ T.mult
  isSmoothDivisor_ker_top :
    ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
      ∀ (j : ℕ) (hj : j < T.boundary.length), DivisorReduction.ccI hj = ⊤ →
        (DivisorReduction.rD hj).IsAdmissible →
        ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rD hj).SequenceOfBlowups)
          (hpr : s.NoComp)
          (hmk : (DivisorReduction.amb hres hno hpr).IsMarked
                T.structMap T.ideal T.mult T.boundary),
        ∀ t ≤ s.length,
          IsSmoothDivisor ((DivisorReduction.pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t)
            (ker
              (DivisorReduction.embA hres hno hpr t))
  isSmoothDivisor_ker_pre :
    ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
      ∀ (j : ℕ) (hj : j < T.boundary.length), DivisorReduction.ccI hj ≠ ⊤ →
        ∀ (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj),
        (DivisorReduction.rTD hj).IsAdmissible →
        ∀ [IsNoetherian T.scheme] (s : (DivisorReduction.rTD hj).SequenceOfBlowups)
          (hpr : s.NoComp)
          (hmk : (prepend (DivisorReduction.ccI hj) hb
              (DivisorReduction.amb hres hno hpr)).IsMarked
                T.structMap T.ideal T.mult T.boundary),
        ∀ t ≤ s.length,
          IsSmoothDivisor ((DivisorReduction.prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec $ t + 1)
            (ker
              (DivisorReduction.embA hres hno hpr t))
  compositeMap_eq_restrictedEmptyCenter :
    ∀ (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (s : (DivisorReduction.rD hj).SequenceOfBlowups)
      (hpr : s.NoComp)
      (hmk : (DivisorReduction.amb hres hno hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t : ℕ,
        s.projectionToSpec t =
          DivisorReduction.embA hres hno hpr t ≫
            (DivisorReduction.pMS hres hno hmk).projectionToSpec t
  compositeMap_eq_restricted :
    ∀ (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j : ℕ)
      (hj : j < T.boundary.length) (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ DivisorReduction.ccI hj)
      (s : (DivisorReduction.rTD hj).SequenceOfBlowups)
      (hpr : s.NoComp)
      (hmk : (prepend (DivisorReduction.ccI hj) hb
          (DivisorReduction.amb hres hno hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
      ∀ t : ℕ,
        s.projectionToSpec t =
          DivisorReduction.embA hres hno hpr t ≫
            (DivisorReduction.ppMS hres hno hmk).projectionToSpec (t + 1)
  support_imageIdeal_subset_ker :
    ∀ (X Y : Sch) (f : X ⟶ Y) [IsClosedImmersion f]
      (I : ISD X),
      ((imageIdealSheaf f I).support : Set ↥Y) ⊆
        ((ker f).support : Set ↥Y)
  support_preIdeal_subset_boundary :
    ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (j : ℕ) (hj : j < T.boundary.length),
      ((DivisorReduction.ccI hj).support : CSet T.scheme) ⊆
        ((T.bget j hj).support : CSet T.scheme)

def HasSmoothDivisorTransforms (T : MarkedIdealWithBoundary) (j : ℕ) (hj : j < T.boundary.length)
    (S : T.SequenceOfBlowups) : Prop :=
  ∃ (D : (t : ℕ) → (S.schemeAt t).IdealSheafData) (b : Bool),
    (∀ t ≤ S.length, IsSmoothDivisor (S.projectionToSpec t) $ D t) ∧
    D 0 = (T.bget j hj).comap S.isoZero.hom ∧
    (∀ t < S.length,
        ((S.center t).support : CSet $ S.schemeAt t) ⊆ ((D t).support : CSet $ S.schemeAt t)) ∧
    (b = true →
      0 < S.length ∧
      IsOpen (⇑(D 0).si ⁻¹' (((S.center 0).support : CSet $ S.schemeAt 0))) ∧
      D 1 = (D 0).comap (S.transitionMapSucc 0)) ∧
    (∀ t < S.length, (b = true → t ≠ 0) →
        D (t + 1) = strictTransform (S.transitionMapSucc t) (S.center t) (D t)) ∧
    (orderAtLeastLocus S.lastIdeal T.mult ∩ ((D S.length).support : CSet $ S.schemeAt S.length) = ∅) ∧
    (∀ t < S.length, (b = true → t ≠ 0) →
      ∃ J : (D t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(D t).subscheme,
            (D t).si x ∉ S.otherBoundaryLocus j t →
              ∃ V : (D t).subscheme.Opens, x ∈ V ∧
                J.comap V.i = ((S.ideal t).comap (D t).si).comap V.i) ∧
        PrincipalizationCertificate (D t).subscheme ((D t).si ≫ S.projectionToSpec t) J T.mult
          (⇑(D t).si ⁻¹' S.otherBoundaryLocus j t)
          ((S.center t).comap (D t).si))

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme)
section
variable (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length)
section
variable (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.ccI hj)) (s : (DivisorReduction.rTD hj).SequenceOfBlowups) (hpr : s.NoComp)
section
variable (hmk : (prepend (DivisorReduction.ccI hj) hb (DivisorReduction.amb hres blowupPreservesNoetherian hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
def divisorIdealAfterBlowup (t : ℕ) :
    ((DivisorReduction.ppMS hres blowupPreservesNoetherian hmk).schemeAt
      (t + 1)).IdealSheafData :=
  ker
    (DivisorReduction.embA hres blowupPreservesNoetherian hpr t)

theorem center_prependedAmbientSeq_succ_eq_imageIdealSheaf (t : ℕ) :
    (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
        hmk).center (t + 1) =
      imageIdealSheaf (DivisorReduction.embA hres blowupPreservesNoetherian hpr t)
        (s.center t) :=
  DivisorReduction.ambientBlowupSeq_center_eq_imageIdealSheaf hres blowupPreservesNoetherian
    T j hj (p21 hj) (p37 hj) s hpr t

theorem center_prependedAmbientSeq_zero :
    (DivisorReduction.ppMS hres blowupPreservesNoetherian hmk).center 0 =
      DivisorReduction.ccI hj :=
  prepend_center_zero (p28 hj) hb
    (DivisorReduction.amb hres blowupPreservesNoetherian hpr)

theorem comap_boundary_isoObjZero_prependedAmbientSeq :
    (T.bget j hj).comap
        (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).isoZero.hom = T.bget j hj :=
  (congrArg (fun e => cmI (bget' hj) $ hom e)
      (prepend_isoObjZero (p28 hj) hb
    (DivisorReduction.amb hres blowupPreservesNoetherian hpr))).trans
    (comap_id _)
end

theorem prependedDivisorTransform_succ_eq_strictTransform
    (hmk : (prepend (DivisorReduction.ccI hj) hb
        (DivisorReduction.amb hres blowupPreservesNoetherian hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    ∀ t < s.length,
      divisorIdealAfterBlowup hres T j hj hb s hpr hmk (t + 1) =
        strictTransform
          (((prepend (DivisorReduction.ccI hj) hb
                (DivisorReduction.amb hres blowupPreservesNoetherian hpr)).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.transitionMapSucc $ t + 1)
          (((prepend (DivisorReduction.ccI hj) hb
                (DivisorReduction.amb hres blowupPreservesNoetherian hpr)).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.center $ t + 1)
          (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t) := by
  intro t ht
  rw [toMarkedSequence_blowupMorphism, toMarkedSequence_center]
  let _a0 := prepend (p28 hj) hb $ DivisorReduction.amb hres blowupPreservesNoetherian hpr
  have _i20 : ∀ t < s.length, ker (DivisorReduction.embA hres blowupPreservesNoetherian hpr $ t + 1) = p6 (_a0.map $ t + 1) (_a0.center $ t + 1) (ker $ DivisorReduction.embA hres blowupPreservesNoetherian hpr t) := by
    intro t ht
    rw [prepend_blowupMorphism_succ, prepend_center_succ]
    refine ker_embeddingIntoAmbientBlowupSequence_succ (bgetT hj).si
      s.toBsd hres blowupPreservesNoetherian hpr t ?_
    simp_all
  exact _i20 t ht
end

section
variable (s : (DivisorReduction.rD hj).SequenceOfBlowups) (hpr : s.NoComp) (hmk : (DivisorReduction.amb hres blowupPreservesNoetherian hpr).IsMarked T.structMap T.ideal T.mult T.boundary)
def divisorIdealWithoutBlowup (t : ℕ) :
    ((DivisorReduction.pMS hres blowupPreservesNoetherian hmk).schemeAt
      t).IdealSheafData :=
  ker
    (DivisorReduction.embA hres blowupPreservesNoetherian hpr t)

theorem center_ambientMarkedSeq_eq_imageIdealSheaf (t : ℕ) :
    (DivisorReduction.pMS hres blowupPreservesNoetherian hmk).center t =
      imageIdealSheaf (DivisorReduction.embA hres blowupPreservesNoetherian hpr t)
        (s.center t) :=
  DivisorReduction.ambientBlowupSeq_center_eq_imageIdealSheaf hres blowupPreservesNoetherian
    T j hj (p19 T) (p20 T) s hpr t

theorem divisorTransform_succ_eq_strictTransform :
    ∀ t < s.length,
      divisorIdealWithoutBlowup hres T j hj s hpr hmk (t + 1) =
        strictTransform
          (((DivisorReduction.amb hres blowupPreservesNoetherian hpr).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
              hmk).toMarkedSequenceOfBlowups.transitionMapSucc t)
          (((DivisorReduction.amb hres blowupPreservesNoetherian hpr).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
              hmk).toMarkedSequenceOfBlowups.center t)
          (divisorIdealWithoutBlowup hres T j hj s hpr hmk t) := by
  intro t ht
  rw [toMarkedSequence_blowupMorphism, toMarkedSequence_center]
  refine ker_embeddingIntoAmbientBlowupSequence_succ (bgetT hj).si
    s.toBsd hres blowupPreservesNoetherian hpr t ?_
  simp_all
end
end

section
variable (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme]
include hshape
section
variable (hV : T.IsAdmissible)
include hV
section
variable (j) (hj : j < T.boundary.length) (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.ccI hj)) (s : (DivisorReduction.rTD hj).SequenceOfBlowups) (hpr : s.NoComp) (hmk : (prepend (DivisorReduction.ccI hj) hb (DivisorReduction.amb hres blowupPreservesNoetherian hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
theorem support_center_zero_prependedAmbientBlowupSeq_subset :
    (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).center 0).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt 0)) ⊆
      ((((T.bget j hj).comap
          (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
            hmk).isoZero.hom).support) :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt 0)) := by
  rw [center_prependedAmbientSeq_zero hres T j hj hb s hpr hmk,
    comap_boundary_isoObjZero_prependedAmbientSeq hres T j hj hb s hpr hmk]
  exact hshape.support_preIdeal_subset_boundary T hV j hj

theorem isOpen_preimage_support_center_zero_prependedAmbientSeq :
    IsOpen $ ⇑((T.bget j hj).comap
        (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).isoZero.hom).subschemeι ⁻¹'
      ((((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).center 0).support) :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt 0)) := by
  rw [center_prependedAmbientSeq_zero hres T j hj hb s hpr hmk,
    comap_boundary_isoObjZero_prependedAmbientSeq hres T j hj hb s hpr hmk]
  exact hshape.isOpen_preimage_preIdeal T hV j hj
end
end

section
variable (j) (hj : j < T.boundary.length)
section
variable (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.ccI hj)) (s : (DivisorReduction.rTD hj).SequenceOfBlowups) (hpr : s.NoComp) (hmk : (prepend (DivisorReduction.ccI hj) hb (DivisorReduction.amb hres blowupPreservesNoetherian hpr)).IsMarked T.structMap T.ideal T.mult T.boundary)
theorem support_center_succ_prependedAmbientBlowupSeq_subset (t : ℕ) :
    (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).center (t + 1)).support :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt (t + 1))) ⊆
      (support (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t) :
        Set ↥((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
          hmk).schemeAt (t + 1))) := by
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (p21 hj)
    (p37 hj) s hpr t
  rw [center_prependedAmbientSeq_succ_eq_imageIdealSheaf hres T j hj hb s hpr hmk t]
  exact hshape.support_imageIdeal_subset_ker _ _
    (DivisorReduction.embA hres blowupPreservesNoetherian hpr t)
    (s.center t)

end

section
variable (s : (DivisorReduction.rD hj).SequenceOfBlowups) (hpr : s.NoComp) (hmk : (DivisorReduction.amb hres blowupPreservesNoetherian hpr).IsMarked T.structMap T.ideal T.mult T.boundary)
theorem support_center_ambientBlowupSeq_subset (t : ℕ) :
    (((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).center t).support :
        Set ↥((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).schemeAt t)) ⊆
      (support (divisorIdealWithoutBlowup hres T j hj s hpr hmk t) :
        Set ↥((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
          hmk).schemeAt t)) := by
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (p19 T)
    (p20 T) s hpr t
  rw [center_ambientMarkedSeq_eq_imageIdealSheaf hres T j hj s hpr hmk t]
  exact hshape.support_imageIdeal_subset_ker _ _
    (DivisorReduction.embA hres blowupPreservesNoetherian hpr t) (s.center t)

end
end
end
end

section
variable {T : MarkedIdealWithBoundary} (j) (hj : j < T.boundary.length) (S : T.SequenceOfBlowups)
theorem divisorReductionShape_of_strictTransforms (len : ℕ) (D : (t : ℕ) → (S.schemeAt t).IdealSheafData) (hlen : S.length = len)
    (h1 : ∀ t ≤ len, IsSmoothDivisor (S.projectionToSpec t) $ D t)
    (h2 : D 0 = (T.bget j hj).comap S.isoZero.hom)
    (h3 : ∀ t < len, ((S.center t).support : CSet $ S.schemeAt t) ⊆ ((D t).support : CSet $ S.schemeAt t))
    (h5 : ∀ t < len, D (t + 1) = strictTransform (S.transitionMapSucc t) (S.center t) (D t))
    (h6 : orderAtLeastLocus (S.ideal len) T.mult ∩ ((D len).support : CSet $ S.schemeAt len) = ∅)
    (h7 : ∀ t < len, ∃ J : (D t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(D t).subscheme,
            (D t).si x ∉ S.otherBoundaryLocus j t →
              ∃ V : (D t).subscheme.Opens, x ∈ V ∧
                J.comap V.i = ((S.ideal t).comap (D t).si).comap V.i) ∧
        PrincipalizationCertificate (D t).subscheme ((D t).si ≫ S.projectionToSpec t) J T.mult
          (⇑(D t).si ⁻¹' S.otherBoundaryLocus j t)
          ((S.center t).comap (D t).si)) :
    HasSmoothDivisorTransforms T j hj S := by
  subst hlen
  refine ⟨D, false, h1, h2, h3, Bool.noConfusion, fun t ht _ => h5 t ht, ?_,
    fun t ht _ => h7 t ht⟩
  rwa [lastIdeal_eq]

theorem divisorReductionShape_of_pullback_then_strictTransforms (len : ℕ) (hlen : S.length = len + 1)
    (D0 : (S.schemeAt 0).IdealSheafData) (Dd : (t : ℕ) → (S.schemeAt $ t + 1).IdealSheafData)
    (h1a : IsSmoothDivisor (S.projectionToSpec 0) D0)
    (h1b : ∀ t ≤ len, IsSmoothDivisor (S.projectionToSpec $ t + 1) $ Dd t)
    (h2 : D0 = (T.bget j hj).comap S.isoZero.hom)
    (h3a : ((S.center 0).support : CSet $ S.schemeAt 0) ⊆ (D0.support : CSet $ S.schemeAt 0))
    (h3b : ∀ t < len, ((S.center $ t + 1).support : Set ↥(S.schemeAt $ t + 1)) ⊆
        ((Dd t).support : Set ↥(S.schemeAt $ t + 1)))
    (h4 : IsOpen $ ⇑D0.si ⁻¹' ((S.center 0).support : CSet $ S.schemeAt 0))
    (h4' : Dd 0 = D0.comap (S.transitionMapSucc 0))
    (h5 : ∀ t < len, Dd (t + 1) =
        strictTransform (S.transitionMapSucc $ t + 1) (S.center $ t + 1) (Dd t))
    (h6 : orderAtLeastLocus (S.ideal $ len + 1) T.mult ∩
        ((Dd len).support : Set ↥(S.schemeAt $ len + 1)) = ∅)
    (h7 : ∀ t < len, ∃ J : (Dd t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(Dd t).subscheme,
            (Dd t).si x ∉ S.otherBoundaryLocus j (t + 1) →
              ∃ V : (Dd t).subscheme.Opens, x ∈ V ∧
                J.comap V.i = ((S.ideal $ t + 1).comap (Dd t).si).comap V.i) ∧
        PrincipalizationCertificate (Dd t).subscheme ((Dd t).si ≫ S.projectionToSpec (t + 1)) J T.mult
          (⇑(Dd t).si ⁻¹' S.otherBoundaryLocus j (t + 1))
          ((S.center $ t + 1).comap (Dd t).si)) :
    HasSmoothDivisorTransforms T j hj S := by
  refine ⟨fun t => Nat.rec (motive := fun t => ISD $ S.schemeAt t) D0
      (fun t' _ => Dd t') t, true, ?_, h2, ?_, ?_, ?_, ?_, ?_⟩
  rintro (_ | t) ht
  exact h1a
  simp_all
  rintro (_ | t) ht
  exact h3a
  simp_all
  simp_all
  rintro (_ | t) ht hbz
  exact absurd rfl $ hbz rfl
  rw [hlen] at ht
  exact h5 t $ by omega
  rwa [lastIdeal_eq, hlen]
  rintro (_ | t) ht hbz
  simp_all
  simp_all

end

theorem comap_imageIdealSheaf_eq_self_of_isClosedImmersion {X Y : Sch} (f : X ⟶ Y)
    [IsClosedImmersion f] (I : ISD X) :
    (imageIdealSheaf f I).comap f = I :=
  p30 f I

theorem exists_principalizationCertificate_ker_of_isClosedImmersion {k : Type} [Field k]
    {X Y : Sch}
    (f : X ⟶ Y) [IsClosedImmersion f]
    (pX : X ⟶ Sp k) (pY : Y ⟶ Sp k)
    (I Z : ISD X) (m : ℕ) (Mem : Set ↥X) (MemY : Set ↥Y)
    (IY ZY : ISD Y)
    (hp : pX = f ≫ pY)
    (hMem : Mem ⊆ ⇑f ⁻¹' MemY)
    (hIY : IY.comap f = I)
    (hZY : ZY = imageIdealSheaf f Z)
    (hnz : NonzeroOnComponents I)
    (hcert : PrincipalizationCertificate X pX I m Mem Z) :
    ∃ J : (ker f).subscheme.IdealSheafData,
      NonzeroOnComponents J ∧
      (∀ x : ↥(ker f).subscheme,
          (ker f).subschemeι x ∉ MemY →
            ∃ V : (ker f).subscheme.Opens, x ∈ V ∧
              J.comap V.ι =
                (IY.comap (ker f).subschemeι).comap V.ι) ∧
      PrincipalizationCertificate (ker f).subscheme
        ((ker f).subschemeι ≫ pY) J m
        (⇑(ker f).subschemeι ⁻¹' MemY)
        (ZY.comap (ker f).subschemeι) := by
  have hpe : siI (ker f) ≫ pY =
      (kerSubschemeIso f).hom ≫ pX := by
    rw [hp, ← assoc, kerSubschemeIso_hom_comp]
  have hid : I.comap (kerSubschemeIso f).hom =
      IY.comap (ker f).si := by
    rw [← hIY, ← kerSubschemeIso_hom_comp f, comap_comp]
  refine ⟨I.comap (kerSubschemeIso f).hom,
    nonzeroOnComponents_comap_iso_hom (kerSubschemeIso f) I hnz, ?_, ?_⟩
  intro x _
  refine ⟨⊤, trivial, ?_⟩
  exact congrArg
    (fun J => J.comap (⊤ : (ker f).subscheme.Opens).ι) hid
  have hcert1 := PrincipalizationCertificate.comap_iso_of_eq_iso_hom_comp (kerSubschemeIso f) hpe hcert
  have hsub : (kerSubschemeIso f).hom ⁻¹' Mem ⊆
      (ker f).si ⁻¹' MemY := by
    intro x hx
    rw [mem_preimage] at hx
    have h2 := hMem hx
    rw [mem_preimage] at h2
    have hb0 : (ker f).si x
        = f ((kerSubschemeIso f).hom x) := by
      rw [← kerSubschemeIso_hom_comp f]
      simp
    rwa [mem_preimage, hb0]
  have hZe : ZY.comap (ker f).si
      = Z.comap (kerSubschemeIso f).hom := by
    rw [hZY, ← kerSubschemeIso_hom_comp f, comap_comp,
      comap_imageIdealSheaf_eq_self_of_isClosedImmersion f Z]
  rw [hZe]
  exact principalizationCertificate_mono_of_subset hsub hcert1

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (hshape : PushedBlowupSequenceProperties hres blowupPreservesNoetherian)
include hfacts hshape
section
variable (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (hV : T.IsAdmissible) (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType) (j) (hj : j < T.boundary.length)
include hO hD
section
variable (htop : DivisorReduction.ccI hj = ⊤) (hvl : (DivisorReduction.rD hj).IsAdmissible) (s : (DivisorReduction.rD hj).SequenceOfBlowups) (hpr : s.NoComp) (hmk : (DivisorReduction.amb hres blowupPreservesNoetherian hpr).IsMarked T.structMap T.ideal T.mult T.boundary) (hcert : ∀ t < s.length, PrincipalizationCertificate (s.schemeAt t) (s.projectionToSpec t) (s.ideal t) T.mult (s.boundaryLocus t) (s.center t))
include htop hvl hcert
theorem exists_nonzeroOnComponents_certificate_ambientMarkedSeq :
    ∀ t < s.length,
      ∃ J : (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subscheme,
            (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).si x ∉
                (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
                  hmk).otherBoundaryLocus j t →
              ∃ V : (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subscheme.Opens, x ∈ V ∧
                J.comap V.i =
                  (((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
                      hmk).ideal t).comap
                    (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).si).comap V.i) ∧
        PrincipalizationCertificate (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).subscheme
          ((divisorIdealWithoutBlowup hres T j hj s hpr hmk t).si ≫
            (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
              hmk).projectionToSpec t) J T.mult
          (⇑(divisorIdealWithoutBlowup hres T j hj s hpr hmk t).si ⁻¹'
            (DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
              hmk).otherBoundaryLocus j t)
          (((DivisorReduction.pushedMarkedSeq hres blowupPreservesNoetherian T j hj s hpr
            hmk).center t).comap (divisorIdealWithoutBlowup hres T j hj s hpr hmk t).si) := by
  let _c0 := DivisorReduction.pMS hres blowupPreservesNoetherian hmk
  intro t ht
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (p19 T)
    (p20 T) s hpr t
  exact exists_principalizationCertificate_ker_of_isClosedImmersion
    (DivisorReduction.embA hres blowupPreservesNoetherian hpr t)
    (s.projectionToSpec t)
    (_c0.projectionToSpec t)
    (s.ideal t) (s.center t) T.mult (s.boundaryLocus t)
    (_c0.otherBoundaryLocus j t)
    (_c0.ideal t)
    (_c0.center t)
    (hshape.compositeMap_eq_restrictedEmptyCenter T j hj s hpr hmk t)
    (hshape.boundaryLocus_subset_top T j hj s hpr hmk t ht)
    (hfacts.comap_ctrlIdeal_top T hV hO hD j hj htop hvl s hpr t (le_of_lt ht))
    (center_ambientMarkedSeq_eq_imageIdealSheaf hres T j hj s hpr hmk t)
    (nonzeroOnComponents_ideal_of_isAdmissible effectiveCartierSupportContainsNoComponent hvl s t (le_of_lt ht))
    (hcert t ht)

theorem divisorReductionShape_ambientBlowupSeq
    (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    HasSmoothDivisorTransforms T j hj
      (DivisorReduction.pMS hres blowupPreservesNoetherian hmk) :=
  divisorReductionShape_of_strictTransforms j hj _ s.length (divisorIdealWithoutBlowup hres T j hj s hpr hmk)
    (DivisorReduction.ambientBlowupSeq_length hres blowupPreservesNoetherian T j hj
    (p19 T) (p20 T) s hpr)
    (hshape.isSmoothDivisor_ker_top T hV hO hD j hj htop hvl s hpr hmk)
    (hshape.ker_pushedEmb_zero_top T j hj s hpr hmk)
    (fun t _ => support_center_ambientBlowupSeq_subset hres hshape T j hj s hpr hmk t)
    (divisorTransform_succ_eq_strictTransform hres T j hj s hpr hmk)
    (hfacts.coSupport_inter_ker_eq_empty_top T hV hO hD j hj htop hvl s hpr hfin)
    (exists_nonzeroOnComponents_certificate_ambientMarkedSeq hres hfacts hshape T hV hO hD j hj htop hvl s hpr hmk hcert)
end

section
variable (hne : DivisorReduction.ccI hj ≠ ⊤) (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.ccI hj)) (hvl : (DivisorReduction.rTD hj).IsAdmissible) (s : (DivisorReduction.rTD hj).SequenceOfBlowups) (hpr : s.NoComp) (hmk : (prepend (DivisorReduction.ccI hj) hb (DivisorReduction.amb hres blowupPreservesNoetherian hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) (hcert : ∀ t < s.length, PrincipalizationCertificate (s.schemeAt t) (s.projectionToSpec t) (s.ideal t) T.mult (s.boundaryLocus t) (s.center t))
include hne hvl hcert
theorem exists_nonzeroOnComponents_certificate_prependedAmbientSeq :
    ∀ t < s.length,
      ∃ J : (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subscheme.IdealSheafData,
        NonzeroOnComponents J ∧
        (∀ x : ↥(divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subscheme,
            (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).si x ∉
                (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
                  hmk).otherBoundaryLocus j (t + 1) →
              ∃ V : (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subscheme.Opens, x ∈ V ∧
                J.comap V.i =
                  (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
                      hmk).ideal (t + 1)).comap
                    (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).si).comap V.i) ∧
        PrincipalizationCertificate (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).subscheme
          ((divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).si ≫
            (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
              hmk).projectionToSpec (t + 1)) J T.mult
          (⇑(divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).si ⁻¹'
            (DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
              hmk).otherBoundaryLocus j (t + 1))
          (((DivisorReduction.prependedPushedMarkedSeq hres blowupPreservesNoetherian T j hj hb s hpr
            hmk).center (t + 1)).comap
              (divisorIdealAfterBlowup hres T j hj hb s hpr hmk t).si) := by
  let _c0 := DivisorReduction.ppMS hres blowupPreservesNoetherian hmk
  intro t ht
  have := DivisorReduction.isClosedImmersion_embeddingIntoAmbient hres
    blowupPreservesNoetherian T j hj (p21 hj)
    (p37 hj) s hpr t
  exact exists_principalizationCertificate_ker_of_isClosedImmersion
    (DivisorReduction.embA hres blowupPreservesNoetherian hpr t)
    (s.projectionToSpec t)
    (_c0.projectionToSpec (t + 1))
    (s.ideal t) (s.center t) T.mult (s.boundaryLocus t)
    (_c0.otherBoundaryLocus j (t + 1))
    (_c0.ideal (t + 1))
    (_c0.center (t + 1))
    (hshape.compositeMap_eq_restricted T j hj hb s hpr hmk t)
    (hshape.boundaryLocus_subset_pre T j hj hb s hpr hmk t ht)
    (hfacts.comap_ctrlIdeal_pre T hV hO hD j hj hne hb hvl s hpr t (le_of_lt ht))
    (center_prependedAmbientSeq_succ_eq_imageIdealSheaf hres T j hj hb s hpr hmk t)
    (nonzeroOnComponents_ideal_of_isAdmissible effectiveCartierSupportContainsNoComponent hvl s t (le_of_lt ht))
    (hcert t ht)

theorem divisorReductionShape_prependedAmbientBlowupSeq
    (hfin : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    HasSmoothDivisorTransforms T j hj
      (DivisorReduction.ppMS hres blowupPreservesNoetherian hmk) :=
  divisorReductionShape_of_pullback_then_strictTransforms j hj _ s.length (congrArg (· + 1)
    (DivisorReduction.ambientBlowupSeq_length hres blowupPreservesNoetherian T j hj
      (p21 hj) (p37 hj) s hpr))
    (cmI (bget' hj)
      (DivisorReduction.ppMS hres blowupPreservesNoetherian hmk).isoZero.hom)
    (divisorIdealAfterBlowup hres T j hj hb s hpr hmk)
    (hshape.isSmoothDivisor_boundary_comap T hV j hj
      (DivisorReduction.ppMS hres blowupPreservesNoetherian hmk))
    (hshape.isSmoothDivisor_ker_pre T hV hO hD j hj hne hb hvl s hpr hmk)
    rfl
    (support_center_zero_prependedAmbientBlowupSeq_subset hres hshape T hV j hj hb s hpr hmk)
    (fun t _ => support_center_succ_prependedAmbientBlowupSeq_subset hres hshape T j hj hb s hpr hmk t)
    (isOpen_preimage_support_center_zero_prependedAmbientSeq hres hshape T hV j hj hb s hpr hmk)
    (hshape.ker_pushedEmb_zero_pre T j hj hb s hpr hmk)
    (prependedDivisorTransform_succ_eq_strictTransform hres T j hj hb s hpr hmk)
    (hfacts.coSupport_inter_ker_eq_empty_pre T hV hO hD j hj hne hb hvl s hpr hfin)
    (exists_nonzeroOnComponents_certificate_prependedAmbientSeq hres hfacts hshape T hV hO hD j hj hne hb hvl s hpr hmk hcert)
end
end

theorem exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules
    (n : ℕ) (L O : PrincipalizationAssignment)
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType → ∀ hj : j < T.boundary.length,
        ∃ (D : (t : ℕ) → (((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt t).IdealSheafData)
          (b : Bool),
          (∀ t ≤ ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
              IsSmoothDivisor (((canonicalAlgorithmRules hres).divisorFamily L j T).projectionToSpec t) $ D t) ∧
          D 0 = (T.bget j hj).comap
              ((canonicalAlgorithmRules hres).divisorFamily L j T).isoZero.hom ∧
          (∀ t < ((canonicalAlgorithmRules hres).divisorFamily L j T).length,
              ((((canonicalAlgorithmRules hres).divisorFamily L j T).center t).support :
                  Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt t)) ⊆
                ((D t).support : Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt t))) ∧
          (b = true →
            0 < ((canonicalAlgorithmRules hres).divisorFamily L j T).length ∧
            IsOpen (⇑(D 0).si ⁻¹'
              (((((canonicalAlgorithmRules hres).divisorFamily L j T).center 0).support :
                Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt 0)))) ∧
            D 1 = (D 0).comap (((canonicalAlgorithmRules hres).divisorFamily L j T).transitionMapSucc 0)) ∧
          (∀ t < ((canonicalAlgorithmRules hres).divisorFamily L j T).length, (b = true → t ≠ 0) →
              D (t + 1) =
                strictTransform (((canonicalAlgorithmRules hres).divisorFamily L j T).transitionMapSucc t)
                  (((canonicalAlgorithmRules hres).divisorFamily L j T).center t) (D t)) ∧
          (orderAtLeastLocus ((canonicalAlgorithmRules hres).divisorFamily L j T).lastIdeal T.mult ∩
              ((D ((canonicalAlgorithmRules hres).divisorFamily L j T).length).support :
                Set ↥(((canonicalAlgorithmRules hres).divisorFamily L j T).schemeAt
                  ((canonicalAlgorithmRules hres).divisorFamily L j T).length)) = ∅) ∧
          (∀ t < ((canonicalAlgorithmRules hres).divisorFamily L j T).length, (b = true → t ≠ 0) →
            ∃ J : (D t).subscheme.IdealSheafData,
              NonzeroOnComponents J ∧
              (∀ x : ↥(D t).subscheme,
                  (D t).si x ∉
                      ((canonicalAlgorithmRules hres).divisorFamily L j T).otherBoundaryLocus j t →
                    ∃ V : (D t).subscheme.Opens, x ∈ V ∧
                      J.comap V.i =
                        ((((canonicalAlgorithmRules hres).divisorFamily L j T).ideal t).comap
                          (D t).si).comap V.i) ∧
              PrincipalizationCertificate (D t).subscheme
                ((D t).si ≫ ((canonicalAlgorithmRules hres).divisorFamily L j T).projectionToSpec t) J T.mult
                (⇑(D t).si ⁻¹'
                  ((canonicalAlgorithmRules hres).divisorFamily L j T).otherBoundaryLocus j t)
                ((((canonicalAlgorithmRules hres).divisorFamily L j T).center t).comap (D t).si)) := by
  intro T hV hdim hO hD hj
  have hNoe :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  show HasSmoothDivisorTransforms T j hj $ (canonicalAlgorithmRules hres).divisorFamily L j T
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T]
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  rw [divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
    (fun S _ => L S) j hj hcs]
  let _a0 := emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  let S := _a0
  let hsm := hshape.isSmoothDivisor_boundary_comap T hV j hj
      _a0
  refine divisorReductionShape_of_strictTransforms j hj S 0
    (fun t => Nat.rec (motive := fun t => ISD $ S.schemeAt t)
      (cmI (bget' hj) S.isoZero.hom) (fun _ _ => ⊤) t) (emptyMarkedSequenceOfBlowups_length T.structMap T.ideal T.mult T.boundary) ?_ rfl ?_ ?_ ?_ ?_
  intro t ht
  obtain rfl : t = 0 := mp_ le_zero ht
  exact hsm
  intro t ht
  exact absurd ht $ not_lt_zero t
  intro t ht
  exact absurd ht $ not_lt_zero t
  have hz : orderAtLeastLocus (S.ideal 0) T.mult = (∅ : CSet $ S.schemeAt 0) := by
    rw [ideal_zero]
    rw [orderAtLeastLocus_comap_iso_hom_eq_preimage, hcs, preimage_empty]
  rw [hz, empty_inter]
  intro t ht
  exact absurd ht $ not_lt_zero t
  have hcoNE := mpr_ nonempty_iff_ne_empty hcs
  rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hD hcs with
    ⟨htop, hpr, hmk0, heq⟩ | ⟨hne, hb, hpr, hmk0, heq⟩
  have hvl :=
    hfacts.valid_lowerTop T hV hO hD j hj htop
  have hdimlow :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcoNE j hj
      (p19 T) $ p20 T) hdim
  let _m1 := DivisorReduction.rD hj
  have hfin : orderAtLeastLocus ((L _m1).ideal
      (L _m1).length) T.mult = ∅ := by
    have hr := hL.resolves _m1 hvl hdimlow
    rwa [isResolution_iff, lastIdeal_eq] at hr
  rw [heq hmk0]
  exact divisorReductionShape_ambientBlowupSeq hres hfacts hshape T hV hO hD j hj htop hvl
    (L _m1) hpr hmk0
    (fun t ht => hL.cert _m1 hvl hdimlow t ht) hfin
  have hvl :=
    hfacts.valid_lowerPre T hV hO hD j hj hne
  have hdimlow :=
    lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcoNE j hj
      (p21 hj) $ p37 hj) hdim
  let _m0 := DivisorReduction.rTD hj
  have hfin : orderAtLeastLocus ((L _m0).ideal
      (L _m0).length) T.mult = ∅ := by
    have hr := hL.resolves _m0 hvl hdimlow
    rwa [isResolution_iff, lastIdeal_eq] at hr
  rw [heq hmk0]
  exact divisorReductionShape_prependedAmbientBlowupSeq hres hfacts hshape T hV hO hD j hj hne hb hvl
    (L _m0) hpr hmk0
    (fun t ht => hL.cert _m0 hvl hdimlow t ht) hfin
end





namespace DivisorReduction

private theorem le_ker_comp_subschemeio {X : Sch} (D : ISD X) {W : Sch}
    (g : W ⟶ subscheme D) : D ≤ ker (g ≫ subschemeι D) :=
  (ker_subschemeι D).ge.trans
    (le_ker_comp g _)

section
variable (T : MarkedIdealWithBoundary)
section
variable (j) (hj : j < T.boundary.length)
abbrev boundaryComponentsInOrderLocus :
    Set ↥(T.bget j hj).subscheme :=
  {x | connectedComponent x ⊆
    ⇑(T.bget j hj).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}

section
variable (h : IsOpen (boundaryComponentsInOrderLocus T j hj))
abbrev boundaryComponentsInOrderLocusOpens :
    (T.bget j hj).subscheme.Opens :=
  ⟨boundaryComponentsInOrderLocus T j hj, h⟩

end

theorem support_containedComponentsIdeal_subset_support_boundary :
    (support (ccI hj) : CSet T.scheme) ⊆
      (support (T.bget j hj) : CSet T.scheme) := by
  by_cases h : IsOpen $ boundaryComponentsInOrderLocus T j hj
  rw [containedComponentsIdeal_eq_ker_io_comp_subschemeio_of_isOpen T j hj h]
  exact SetLike.coe_subset_coe.mpr
    (support_antitone
      (le_ker_comp_subschemeio (bget' hj) (boundaryComponentsInOrderLocusOpens T j hj h).i))
  rw [containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent T j hj h,
    support_top, TopologicalSpace.Closeds.coe_bot]
  exact empty_subset _

def PreimageSupportEqComponentsInOrderLocus : Prop :=
  ∀ h : IsOpen $ boundaryComponentsInOrderLocus T j hj,
    ⇑(T.bget j hj).si ⁻¹'
        ((ker
            ((boundaryComponentsInOrderLocusOpens T j hj h).i ≫
              (T.bget j hj).si)).support : CSet T.scheme) =
      boundaryComponentsInOrderLocus T j hj

theorem isOpen_preimage_support_containedComponentsIdeal (hc : PreimageSupportEqComponentsInOrderLocus T j hj) :
    IsOpen $ ⇑(T.bget j hj).si ⁻¹'
      (support (ccI hj) : CSet T.scheme) := by
  by_cases h : IsOpen $ boundaryComponentsInOrderLocus T j hj
  rwa [containedComponentsIdeal_eq_ker_io_comp_subschemeio_of_isOpen T j hj h, hc h]
  rw [containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent T j hj h,
    support_top, TopologicalSpace.Closeds.coe_bot,
    preimage_empty]
  exact isOpen_empty
end

theorem isSmoothDivisor_boundary_comap_isoObjZero (hV : T.IsAdmissible) j
    (hj : j < T.boundary.length) (s : T.SequenceOfBlowups) :
    IsSmoothDivisor (s.projectionToSpec 0) $ (T.bget j hj).comap s.isoZero.hom := by
  have hmem : bget' hj ∈ T.boundary := by simp_all
  rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
  exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso T.structMap s.toSequenceOfBlowups.isoZero _ $ ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem

end

end DivisorReduction





section
variable {S X : Sch} (ι : S ⟶ X) [IsClosedImmersion ι] [IsNoetherian X] (s : BlowupSequenceData S) (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)
theorem ker_embeddingIntoAmbientBlowupSequence_zero :
    ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0) =
      (ker ι).comap
        (ambientBlowupSequence ι s hres hno hcen).isoZero.hom := by
  have h2 : (ker ι).comap
      (ambientBlowupSequence ι s hres hno hcen).isoZero.hom
      = ker ι := by
    rw [ambientBlowupSequence_isoObjZero]
    exact comap_id _
  rw [embeddingIntoAmbientBlowupSequence_zero ι s hres hno hcen, h2]
  exact ker_comp_of_isIso s.isoZero.hom ι

section
variable (E : Bdy X) (j : ℕ) (hj : j < E.length) (hE : E.lget j hj = ker ι)
include hE
theorem forall_le_ker_embeddingIntoAmbient_eq_boundary_get :
    ∀ t, t ≤ s.length →
      ∀ hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length,
        ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
          get ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t) ⟨j, hjt⟩ := by
  intro t
  induction t with
  | zero =>
      intro _ hjt
      simp [get_eq_getElem] at hE ⊢
      rw [ker_embeddingIntoAmbientBlowupSequence_zero]
      simp [hE]
  | succ n ih =>
      intro hn hjt
      have hn' := hn
      have hjn : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E n).length := by
        rw [boundary_length]
        omega
      rw [ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen n hn', ih (le_of_lt hn') hjn]
      simp [get_eq_getElem]
      rw [getElem_append_left $ by simpa using hjn, getElem_map]

theorem ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get
    t (ht : t ≤ s.length)
    (hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length) :
    ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
      get ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t) ⟨j, hjt⟩ :=
  forall_le_ker_embeddingIntoAmbient_eq_boundary_get ι s hres hno hcen E j hj hE t ht hjt
end
end

namespace DivisorReduction

variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian)

section
variable (T : MarkedIdealWithBoundary)
section
variable [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
theorem ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism
    (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ ccI hj)
    (s : (rTD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (prepend (ccI hj) hb
        (amb hres hno hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    ker
        (embA hres hno hpr 0) =
      ((T.bget j hj).comap
          (ppMS hres hno hmk).isoZero.hom).comap
        ((ppMS hres hno hmk).transitionMapSucc 0) := by
  let _a0 := bget' hj
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero _a0.si
    s.toBsd hres hno hpr
  rw [ker_subschemeι] at h0
  let _a1 := ppMS hres hno hmk
  have hA : _a0.comap
      _a1.isoZero.hom = _a0 :=
    comap_id _
  have hB : _a1.transitionMapSucc 0
      = bdIzH (ambientBlowupSequence _a0.si
          s.toBsd hres hno hpr) := by
    rw [toMarkedSequence_blowupMorphism, toMarkedBlowupSequenceData_blowupMorphism,
      prepend_blowupMorphism_zero]
    exact rfl
  rwa [hA, hB]
end

theorem isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top (hV : T.IsAdmissible)
    (_hob : T.IsOrderBoundedByMult) (_hbal : T.IsBalanced hV.locallyOfFiniteType)
    j (hj : j < T.boundary.length) (_hpre : ccI hj = ⊤)
    (_hlow : (rD hj).IsAdmissible)
    [IsNoetherian T.scheme] (s : (rD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (amb hres hno hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    t (ht : t ≤ s.length) :
    IsSmoothDivisor ((pMS hres hno hmk).projectionToSpec t)
      (ker
        (embA hres hno hpr t)) := by
  let _s0 := bget' hj
  let _c1 := pMS hres hno hmk
  let _a1 := (ambientBlowupSequence _s0.si s.toBsd hres hno hpr).boundaryFrom T.boundary t
  have hjt : j < _a1.length := by
    rw [boundary_length]
    omega
  have htS : t ≤ s.toBsd.length := by
    rw [ofMarkedSequence_length]
    exact ht
  have hbd : _c1.boundary t =
      _a1 := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_boundary, toMarkedBlowupSequenceData_boundary]
    exact rfl
  have hpl : (amb hres hno hpr).length =
      msLen s := by
    have hh := ambientBlowupSequence_length _s0.si
      s.toBsd hres hno hpr
    rwa [ofMarkedSequence_length] at hh
  have htlen : t ≤ _c1.toSequenceOfBlowups.length := by
    rwa [toMarkedSequence_length, toMarkedBlowupSequenceData_length, hpl]
  have hsnc := MarkedSequenceOfBlowups.inStrictNormalCrossingPosition_projectionToSpec_boundary effectiveCartierSupportContainsNoComponent hV
    _c1 t htlen
  have key : ker
      (embeddingIntoAmbientBlowupSequence _s0.si s.toBsd hres hno hpr t) ∈
      _a1 := by
    rw [ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get _s0.si s.toBsd hres hno hpr T.boundary j hj (ker_subschemeι _).symm t htS hjt]
    exact getElem_mem _
  refine an1 (mp_ (inStrictNormalCrossingPosition_iff _ _) hsnc) _ ?_
  rwa [hbd]
end

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end
-- BEGIN_E2_PROJ_Bundle09
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
abbrev p25 := @MarkedSequenceOfBlowups.isNoetherian_schemeAt
abbrev p38 := @MarkedIdealWithBoundary.IsAdmissible.transformAt
end
-- END_E2_PROJ_Bundle09
noncomputable section
open CategoryStruct (comp)
open FunctorialResolution.EmbeddedResolution (orderAtLeastLocus_comap quasiCompact_strictTransformio_of_isLocallyNoetherian restrictIdeal_eq_top_iff_forall_notMem_support strictTransform_top)
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData (boundary_prepend_succ boundary_succ boundary_zero controlledTransform_prepend_succ controlledTransform_succ controlledTransform_zero projectionToBase_prepend_succ projectionToBase_zero)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (SameNontrivialBoundary baseChange_boundary baseChange_ideal baseChange_mult bget' mk nontrivialPart pullbackAlong_boundary pullbackAlong_ideal sameNontrivialBoundary_iff validOfSameNontrivialBoundary withBoundary_boundary withBoundary_ideal withBoundary_mult withBoundary_self)
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups (boundaryLocus otherBoundaryLocus projectionToSpec projectionToSpec_eq smooth_projectionToSpec)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (Isomorphic)
open HEq (refl)
open Limits.pullback (condition fst hom_ext lift lift_fst lift_snd snd)
open List (length)
open List.cons (injEq)
open Scheme.Hom (continuous)
section


namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

variable (T : MarkedIdealWithBoundary) (j) (hj : j < T.boundary.length)
    (I0) (E0)
    (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups)

def iteratedPreimage (U0_ : Opens (s.toSequenceOfBlowups.schemeAt 0)) :
    (t : ℕ) → (s.toSequenceOfBlowups.schemeAt t).Opens
  | 0 => U0_
  | t + 1 => s.toSequenceOfBlowups.transitionMapSucc t ⁻¹ᵁ iteratedPreimage U0_ t

section
variable {T} {j} {hj} {I0} {E0} {s}
noncomputable abbrev iPre (U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) := iteratedPreimage T j hj I0 E0 s U0_ t
end


section
variable (U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
section
variable (t : ℕ)
theorem iteratedPreimage_succ :
    iPre U0_ (t + 1) =
      s.toSequenceOfBlowups.transitionMapSucc t ⁻¹ᵁ iPre U0_ t := rfl

def restrictedBlowupMorphism :
    (↑(iPre U0_ $ t + 1) : Sch) ⟶
      (↑(iPre U0_ t) : Sch) :=
  s.toSequenceOfBlowups.transitionMapSucc t ∣_ iPre U0_ t

end

section
variable (hV : (restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible) (t : ℕ)
include hV
theorem smooth_iteratedPreimage_io_comp_projectionToSpec (ht : t ≤ s.toSequenceOfBlowups.length) :
    Smooth $ (iPre U0_ t).i ≫ s.projectionToSpec t := by
  have :=
    smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s t ht
  infer_instance

theorem boundary_comap_iteratedPreimage_succ (ht : t < s.toSequenceOfBlowups.length) :
    map (fun D => D.comap (iPre U0_ $ t + 1).ι) (s.boundary $ t + 1) =
      map
          (strictTransform (restrictedBlowupMorphism T j hj I0 E0 s U0_ t)
            ((s.toSequenceOfBlowups.center t).comap (iPre U0_ t).ι))
          (map (fun D => D.comap (iPre U0_ t).ι) $ s.boundary t) ++
        [exceptionalIdeal (restrictedBlowupMorphism T j hj I0 E0 s U0_ t)
            ((s.toSequenceOfBlowups.center t).comap (iPre U0_ t).ι)] := by
  let _c0 := iPre U0_ t
  have : IsNoetherian $ msAt s $ t + 1 :=
    p25 effectiveCartierSupportContainsNoComponent hV s (t + 1) ht
  have : IsLocallyNoetherian $ msAt s $ t + 1 := inferInstance
  have hex : cmI (p5 (msTrS s t) $ msCtr s t)
        (iPre U0_ $ t + 1).ι =
      p5 (restrictedBlowupMorphism T j hj I0 E0 s U0_ t)
        (cmI (msCtr s t) _c0.i) :=
    restrictIdeal_exceptionalIdeal (msTrS s t) (msCtr s t)
      _c0
  have hst : ∀ D : ISD $ msAt s t,
      (p6 (msTrS s t) (msCtr s t) D).comap
          (iPre U0_ $ t + 1).ι =
        p6 (restrictedBlowupMorphism T j hj I0 E0 s U0_ t)
          (cmI (msCtr s t) _c0.i)
          (cmI D _c0.i) := fun D =>
    restrictIdeal_strictTransform_preimage (msTrS s t) (msCtr s t) D
      _c0
  rw [s.boundary_succ t ht]
  simp only [map_append, map_map, map_cons, map_nil, hex]
  congr 1
  exact map_congr_left fun D _ => hst D
end

theorem isClosed_iteratedPreimage
    (hU : IsClosed $ (U0_ : CSet $ s.toSequenceOfBlowups.schemeAt 0)) (t : ℕ) :
    IsClosed $ (iPre U0_ t : CSet $ s.toSequenceOfBlowups.schemeAt t) := by
  induction t with
  | zero => exact hU
  | succ n ih =>
      have h2 : IsOpen
          (((msTrS s n ⁻¹ᵁ
              (⟨(iPre U0_ n : CSet $ msAt s n)ᶜ, ih.isOpen_compl⟩ :
                Opn $ msAt s n)) : (msAt s $ n + 1).Opens) :
            Set $ msAt s $ n + 1) :=
        TopologicalSpace.Opens.isOpen _
      exact mp_ isOpen_compl_iff h2

end

section

variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian)

section
variable [IsNoetherian T.scheme] (hpr : s.NoComp) (U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
section
variable (t : ℕ)
def restrictedEmbedding :
    (↑(iPre U0_ t) : Sch) ⟶ (amb hres hno hpr).obj t :=
  (iPre U0_ t).ι ≫ embA hres hno hpr t

section
variable {T} {j} {hj} {I0} {E0} {s}
noncomputable abbrev rEmb := restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t
end

theorem restrictedEmbedding_eq_io_comp_embeddingIntoAmbient :
    restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t =
      (iPre U0_ t).ι ≫ embA hres hno hpr t := rfl

theorem restrictedEmbedding_comp_blowupMorphism :
    restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ (t + 1) ≫
        (amb hres hno hpr).map t =
      restrictedBlowupMorphism T j hj I0 E0 s U0_ t ≫ restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t := by
  let _c0 := iteratedPreimage T j hj I0 E0 s U0_ $ t + 1
  have h1 := embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I0 E0 s hpr t
  let _a1 := (amb hres hno hpr).map t
  have e1 : restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ (t + 1) ≫
        _a1 =
      opI _c0 ≫
        (embA hres hno hpr (t + 1) ≫
          _a1) := by
    rw [restrictedEmbedding_eq_io_comp_embeddingIntoAmbient]
    exact assoc _ _ _
  refine tr_ e1 $ tr_ (congrArg (fun g => opI _c0 ≫ g) h1) $ tr_ (sy_ $ assoc _ _ _) $ tr_ (congrArg (fun f => f ≫ embA hres hno hpr t) (morphismRestrict_ι (msTrS s t) $ iteratedPreimage T j hj I0 E0 s U0_ t).symm) ?_
  rw [restrictedEmbedding_eq_io_comp_embeddingIntoAmbient]
  exact assoc _ _ _

theorem restrictedEmbedding_comp_structureMorphism_ambientBlowupSeq :
    restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t ≫
        ambM hres hno hpr t =
      (iteratedPreimage T j hj I0 E0 s U0_ t).i ≫ s.projectionToSpec t := by
  have h3 := (assoc (msPrj s t) (divisorEmbedding T j hj I0 E0) T.structMap).trans (projectionToSpec_eq s t).symm
  rw [← embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I0 E0 s hpr t] at h3
  let _a1 := embA hres hno hpr t
  let _a0 := opI $ iteratedPreimage T j hj I0 E0 s U0_ t
  let _a2 := ambM hres hno hpr t
  have e1 : restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t ≫
        _a2 =
      _a0 ≫
        (_a1 ≫
          _a2) := by
    rw [restrictedEmbedding_eq_io_comp_embeddingIntoAmbient]
    exact assoc _ _ _
  exact tr_ e1 $ congrArg (fun g => _a0 ≫ g) $ (assoc _a1 ((amb hres hno hpr).projectionToBase t) T.structMap).symm.trans h3
end

section
variable (hU : IsClosed ((U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0)))) (t : ℕ)
include hU
theorem isClosedImmersion_restrictedEmbedding :
    IsClosedImmersion $ restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t := by
  rw [restrictedEmbedding_eq_io_comp_embeddingIntoAmbient]
  exact @IsClosedImmersion.comp _ _ _ _ _ (Scheme.Opens.isClosedImmersion_ι_of_isClosed (iteratedPreimage T j hj I0 E0 s U0_ t) $ isClosed_iteratedPreimage T j hj I0 E0 s U0_ hU t) $ isClosedImmersion_embeddingIntoAmbient hres hno T j hj I0 E0 s hpr t
end
end

section
variable (U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
theorem support_ideal_subset_iteratedPreimage
    (hsupp : ((support (s.ideal 0) : CSet $ s.toSequenceOfBlowups.schemeAt 0)) ⊆
      (U0_ : CSet $ s.toSequenceOfBlowups.schemeAt 0)) :
    ∀ t, t ≤ s.toSequenceOfBlowups.length →
      ((support (s.ideal t) : CSet $ s.toSequenceOfBlowups.schemeAt t)) ⊆
        ((iPre U0_ t : CSet $ s.toSequenceOfBlowups.schemeAt t)) := by
  intro t
  induction t with
  | zero =>
      intro _
      exact hsupp
  | succ n ih =>
      intro hn
      have hn' := hn
      intro x hx
      exact (ih $ le_of_lt hn') $ (s.support_ideal_succ_subset_preimage n hn') hx

theorem support_center_subset_iteratedPreimage (hm : 1 ≤ T.mult)
    (hsupp : ((support (s.ideal 0) : CSet $ s.toSequenceOfBlowups.schemeAt 0)) ⊆
      (U0_ : CSet $ s.toSequenceOfBlowups.schemeAt 0))
    (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    ((support (s.toSequenceOfBlowups.center t) : CSet $ s.toSequenceOfBlowups.schemeAt t)) ⊆
      ((iPre U0_ t : CSet $ s.toSequenceOfBlowups.schemeAt t)) := by
  intro x hx
  exact support_ideal_subset_iteratedPreimage T j hj I0 E0 s U0_ hsupp t (le_of_lt ht) $ (mem_orderAtLeastLocus_one_iff _ _).1 $ orderAtLeastLocus_subset_of_le (s.ideal t) hm $ s.center_order t ht hx
end

theorem imageIdealSheaf_comp_of_eq {S X P : Sch} (ι : S ⟶ X) (emb : X ⟶ P)
    (J : ISD S) (Z : ISD X) (hJ : imageIdealSheaf ι J = Z) :
    imageIdealSheaf (ι ≫ emb) J = imageIdealSheaf emb Z := by
  subst hJ
  exact map_comp J ι emb

theorem center_ambientBlowupSeq_eq_imageIdealSheaf [IsNoetherian T.scheme]
    (hpr : s.NoComp)
    (U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hU : IsClosed $ (U0_ : CSet $ s.toSequenceOfBlowups.schemeAt 0)) (hm : 1 ≤ T.mult)
    (hsupp : ((support (s.ideal 0) : CSet $ s.toSequenceOfBlowups.schemeAt 0)) ⊆
      (U0_ : CSet $ s.toSequenceOfBlowups.schemeAt 0))
    (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    (amb hres hno hpr).center t =
      imageIdealSheaf (restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t)
        ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I0 E0 s U0_ t).ι) := by
  let _c0 := iteratedPreimage T j hj I0 E0 s U0_ t
  have hcl :=
    isClosed_iteratedPreimage T j hj I0 E0 s U0_ hU t
  have :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed _ hcl
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf, restrictedEmbedding_eq_io_comp_embeddingIntoAmbient]
  exact sy_ $ imageIdealSheaf_comp_of_eq _c0.i
    (embA hres hno hpr t)
    (cmI (msCtr s t) _c0.i)
    (msCtr s t) $ imageIdealSheaf_comap_io_eq_self_of_support_subset (msCtr s t) _c0 hcl $ support_center_subset_iteratedPreimage T j hj I0 E0 s U0_ hm hsupp t ht

end

end DivisorReduction





section
variable {X : Sch} {D : ISD X}
theorem filterNeTop_cons_of_eq_top
    (h : D = ⊤) (E : Bdy X) :
    filterNeTop (D :: E) = filterNeTop E := by
  subst h
  simp [filterNeTop]

private theorem filterNeTop_cons_of_ne_top
    (h : D ≠ ⊤) (E : Bdy X) :
    filterNeTop (D :: E) = D :: filterNeTop E := by
  simp [filterNeTop, h]
end

theorem filterNeTop_append {Y : Sch} (A B : Bdy Y) :
    filterNeTop (A ++ B) = filterNeTop A ++ filterNeTop B := by
  simp [filterNeTop, filter_append]

theorem filterNeTop_cons_congr {Y : Sch} (a : ISD Y)
    {L L' : Bdy Y} (h : filterNeTop L = filterNeTop L') :
    filterNeTop (a :: L) = filterNeTop (a :: L') := by
  by_cases ha : a = ⊤
  rwa [filterNeTop_cons_of_eq_top ha L, filterNeTop_cons_of_eq_top ha L']
  rw [filterNeTop_cons_of_ne_top ha L, filterNeTop_cons_of_ne_top ha L', h]

section
variable {X Y : Sch} (f : ISD X → ISD Y) (hf : f ⊤ = ⊤)
include hf
theorem filterNeTop_map_filterNeTop (E : Bdy X) :
    filterNeTop (map f E) = filterNeTop (map f $ filterNeTop E) := by
  induction E with
  | nil => simp [filterNeTop]
  | cons a E ih =>
    by_cases ha : a = ⊤
    have h1 := filterNeTop_cons_of_eq_top ha E
    have h2 : f a = ⊤ := by rw [ha]
                            exact hf
    have h3 : filterNeTop (map f (a :: E)) = filterNeTop (map f E) := by
      rw [map_cons]
      exact filterNeTop_cons_of_eq_top h2 $ map f E
    rwa [h1, h3]
    have h1 := filterNeTop_cons_of_ne_top ha E
    rw [h1]
    simp [map_cons]
    exact filterNeTop_cons_congr (f a) ih

theorem filterNeTop_map_append_congr (D : ISD Y)
    (E E' : Bdy X) (h : filterNeTop E = filterNeTop E') :
    filterNeTop (map f E ++ [D]) = filterNeTop (map f E' ++ [D]) := by
  rw [filterNeTop_append (map f E) [D], filterNeTop_append (map f E') [D],
    filterNeTop_map_filterNeTop f hf E, filterNeTop_map_filterNeTop f hf E', h]
end

namespace DivisorReduction

structure GoingUpInvariantOnOpen (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary)
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length)
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups)
    (hpr : s.NoComp)
    (U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) : Prop where
  divDeriv : ∀ l ≤ T.mult, ∀ i < t,
    ∃ B : ((amb hres hno hpr).obj (i + 1)).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map i)
          ((amb hres hno hpr).center i) ^ (T.mult - l) * B =
        (aDI hres hno hpr l i).comap
          ((amb hres hno hpr).map i)
  idx_lt : j < length ((amb hres hno hpr).boundaryFrom E0 t)
  deriv_le : ∀ [_instFt : LocallyOfFiniteType
        (ambM hres hno hpr t)], ∀ n < T.mult,
      derivIdealSheafIterate T.base (ambM hres hno hpr t) n
          ((amb hres hno hpr).controlledTransform I0 T.mult t) ≤
        ⨆ l ≤ n, logDerivIdealSheafIterate T.base
          (ambM hres hno hpr t)
          (ker (rEmb hres hno hpr U0_ t)) (n - l)
          (aDI hres hno hpr l t)
  comap_eraseIdx :
    filterNeTop (map (fun D => D.comap (rEmb hres hno hpr U0_ t))
        (((amb hres hno hpr).boundaryFrom E0 t).eraseIdx j)) =
      filterNeTop (map (fun D => D.comap (iPre U0_ t).ι) (s.boundary t))
  snc_bdry : InStrictNormalCrossingPosition (ambM hres hno hpr t)
      ((amb hres hno hpr).boundaryFrom E0 t)
  bdry_getElem : ((amb hres hno hpr).boundaryFrom E0 t)[j]'idx_lt =
      ker (rEmb hres hno hpr U0_ t)
  smooth_structMap :
    Smooth (ambM hres hno hpr t)

namespace GoingUpInvariantOnOpen

theorem exists_pow_mul_eq_comap_controlledTransform {hres : StrictTransformIsBlowupOfClosedSubscheme}
    {hno : BlowupPreservesNoetherian} {T : MarkedIdealWithBoundary}
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap]
    {j : ℕ} {hj : j < T.boundary.length}
    {I0 : T.scheme.IdealSheafData} {E0 : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups}
    {hpr : s.NoComp}
    {U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I0 E0 s hpr U0_ t) :
    ∀ i < t, ∃ B : ((amb hres hno hpr).obj (i + 1)).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map i)
          ((amb hres hno hpr).center i) ^ T.mult * B =
        ((amb hres hno hpr).controlledTransform I0 T.mult i).comap
          ((amb hres hno hpr).map i) := by
  intro i hi
  obtain ⟨B, hB⟩ := hinv.divDeriv 0 (m67 _) i hi
  refine ⟨B, ?_⟩
  simp at hB
  rw [hB, ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I0 E0 s hpr i]

private theorem ker_comp_eq_ker_subschemeio_comp {A S P : Sch} (g : A ⟶ S)
    [IsClosedImmersion g] (f : S ⟶ P) :
    ker (g ≫ f) = ker ((ker g).si ≫ f) := by
  symm
  rw [← kerSubschemeIso_hom_comp g, assoc, ker_comp_of_isIso]

section
variable {hres : StrictTransformIsBlowupOfClosedSubscheme} {hno : BlowupPreservesNoetherian} {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap] [CharZero T.base] {j} {hj : j < T.boundary.length} {I0} {E0} {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups} {hpr : s.NoComp} {U0_} {t} (hinv : GoingUpInvariantOnOpen hres hno T j hj I0 E0 s hpr U0_ t) (hlift : StrictNormalCrossingsLiftFromDivisor) (hm : 1 ≤ T.mult) (hV : (restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible) (hU : IsClosed ((U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0)))) (hsupp : (((s.ideal 0).support : CSet (s.toSequenceOfBlowups.schemeAt 0))) ⊆ (U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0))) (ht : t < s.length)
include hinv hlift hm hV hU hsupp ht
theorem hasStrictNormalCrossingsWith_center_cons :
    HasStrictNormalCrossingsWith (ambM hres hno hpr t)
      ((amb hres hno hpr).center t)
      (ker (rEmb hres hno hpr U0_ t) ::
        ((amb hres hno hpr).boundaryFrom E0 t).eraseIdx j) := by
  have ht' := ht
  have hsm :=
    hinv.smooth_structMap
  have hci :=
    isClosedImmersion_restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ hU t
  let _a0 := rEmb hres hno hpr U0_ t
  obtain ⟨e, he⟩ :
      ∃ e : _ ≅ subS (ker
          _a0),
        e.hom ≫ siI (m149 _a0) =
          _a0 :=
    ⟨(kerSubschemeIso _a0).symm,
      kerSubschemeIso_inv_comp _a0⟩
  have hcomp : isoI e ≫ _a0 =
      siI (m149 _a0) := by
    calc e.inv ≫ _a0
        = isoI e ≫ (isoH e ≫
            siI (m149 _a0)) := by
          rw [he]
      _ = siI (m149 _a0) := by
          rw [m213]
  let _a1 := (amb hres hno hpr).boundaryFrom E0 t
  let _a3 := ambM hres hno hpr t
  have hsncE : InStrictNormalCrossingPosition _a3
      (m149 _a0 ::
        _a1.eraseIdx j) := by
    have h1 := inStrictNormalCrossingPosition_moveToFront _a3
      _a1 j hinv.idx_lt hinv.snc_bdry
    rwa [moveToFront_eq_cons _ _ hinv.idx_lt, hinv.bdry_getElem] at h1
  let _a2 := cmI (msCtr s t) (iPre U0_ t).i
  have hsncErase : HasStrictNormalCrossingsWith
      (_a0 ≫
        _a3)
      _a2
      (map (·.comap _a0)
        (_a1.eraseIdx j)) := by
    rw [restrictedEmbedding_comp_structureMorphism_ambientBlowupSeq T j hj I0 E0 s hres hno hpr U0_ t]
    refine hasStrictNormalCrossingsWith_of_filterNeTop_eq _ _ _ _ hinv.comap_eraseIdx.symm
      ?_
    have :=
      smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s t $ le_of_lt ht'
    refine hasStrictNormalCrossingsWith_comap (s.projectionToSpec t) (iPre U0_ t).i
      (msCtr s t) (s.boundary t) ?_
    rw [projectionToSpec_eq]
    exact s.center_snc t ht'
  have hq : isoI e ≫ (_a0 ≫
        _a3)
      = siI (m149 _a0) ≫
        _a3 := by
    rw [← assoc, hcomp]
  have hlistEq : map (·.comap e.inv)
        (map (·.comap _a0)
          (_a1.eraseIdx j))
      = map (fun D => cmI D
          (m149 _a0).si)
          (_a1.eraseIdx j) := by
    rw [map_map]
    refine map_congr_left ?_
    intro D _
    simp
    rw [← comap_comp, hcomp]
  have hsncCenter : HasStrictNormalCrossingsWith
      (siI (m149 _a0) ≫
        _a3)
      (cmI _a2 e.inv)
      (map (fun D => cmI D
          (m149 _a0).si)
        (_a1.eraseIdx j)) := by
    have h2 := hasStrictNormalCrossingsWith_comap_iso
      (_a0 ≫
        _a3) e.symm
      _a2
      (map (·.comap _a0)
        (_a1.eraseIdx j)) hsncErase
    rwa [← hq, ← hlistEq]
  have hmain := hlift T.base ((amb hres hno hpr).obj t)
      _a3
      (m149 _a0)
      (_a1.eraseIdx j) hsncE
      (cmI _a2 e.inv) hsncCenter
  have himg : imageIdealSheaf (isoH e ≫ siI (m149 _a0)) _a2 = imageIdealSheaf (m149 _a0).si (cmI _a2 e.inv) := by
    let C := _a2
    have : IsClosedImmersion $ siI C ≫ isoH e := inferInstance
    have hker : ker (siI C ≫ isoH e) = cmI C e.inv := by
      rw [← imageIdealSheaf_eq_ker_subschemeio_comp]
      exact imageIdealSheaf_hom_eq_comap_inv e C
    rw [imageIdealSheaf_eq_ker_subschemeio_comp, imageIdealSheaf_eq_ker_subschemeio_comp, ← assoc,
      ker_comp_eq_ker_subschemeio_comp (siI C ≫ isoH e) $ siI $ m149 _a0, hker]
  rw [he] at himg
  rw [← himg, ← center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I0 E0 s hres hno hpr U0_ hU hm
    hsupp t ht'] at hmain
  exact hmain

theorem hasStrictNormalCrossingsWith_center :
    HasStrictNormalCrossingsWith (ambM hres hno hpr t)
      ((amb hres hno hpr).center t)
      ((amb hres hno hpr).boundaryFrom E0 t) := by
  refine hasStrictNormalCrossingsWith_of_moveToFront _ _ _ j hinv.idx_lt ?_
  rw [moveToFront_eq_cons _ j hinv.idx_lt, hinv.bdry_getElem]
  exact hasStrictNormalCrossingsWith_center_cons hinv hlift hm hV hU hsupp ht
end

theorem comap_comap_of_commSq {X A A' B : Sch} (ι : A' ⟶ A) (p : A ⟶ X)
    (q : A' ⟶ B) (e : B ⟶ X) (I : ISD X) (hsq : ι ≫ p = q ≫ e) :
    (I.comap p).comap ι = (I.comap e).comap q := by
  rw [← comap_comp, hsq, comap_comp]

theorem comap_eq_of_pow_mul_comap_eq {A A' B B' : Sch} (m : ℕ)
    (pi_ : B ⟶ A) (ioA : A' ⟶ A) (ioB : B' ⟶ B) (rh_ : B' ⟶ A')
    (C J : ISD A) (J' : ISD B)
    (c jt : ISD A') (jt' : ISD B')
    (hsq : ioB ≫ pi_ = rh_ ≫ ioA)
    (hcen : C.comap ioA = c)
    (hprev : J.comap ioA = jt)
    (hpow : exceptionalIdeal pi_ C ^ m * J' = J.comap pi_)
    (hsucc : exceptionalIdeal rh_ c ^ m * jt' = jt.comap rh_)
    (hcart : IsLocallyGeneratedByNonZeroDivisor $ exceptionalIdeal rh_ c) :
    J'.comap ioB = jt' := by
  have hexc : (exceptionalIdeal pi_ C).comap ioB = exceptionalIdeal rh_ c := by
    rw [exceptionalIdeal_eq_comap, exceptionalIdeal_eq_comap, ← comap_comp, hsq,
      comap_comp, hcen]
  refine (hcart.pow m).eq_of_mul_eq_mul ?_
  rw [hsucc, ← hexc, ← comap_pow, ← comap_mul,
    hpow, ← comap_comp, hsq, comap_comp, hprev]

private theorem comap_controlledTransform_embeddingIntoAmbient
    (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary)
    [IsNoetherian T.scheme]
    j (hj : j < T.boundary.length)
    I0 E0
    (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups)
    (hpr : s.NoComp) t :
    t ≤ s.length →
    (∀ i < t, ∃ B : ((amb hres hno hpr).obj (i + 1)).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map i)
          ((amb hres hno hpr).center i) ^ T.mult * B =
        ((amb hres hno hpr).controlledTransform I0 T.mult i).comap
          ((amb hres hno hpr).map i)) →
    ((amb hres hno hpr).controlledTransform I0 T.mult t).comap
        (embA hres hno hpr t) = s.ideal t := by
  let _c0 := amb hres hno hpr
  induction t with
  | zero =>
      intro _ _
      have hs0 : s.projectionToBase 0 = s.isoZero.hom := by
        rw [← ofSequenceOfBlowups_projectionToBase s.toSequenceOfBlowups 0, projectionToBase_zero,
          ofSequenceOfBlowups_isoObjZero]
      let _a1 := divisorEmbedding T j hj I0 E0
      have hsq := tr_ (embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I0 E0 s hpr 0)
        (congrArg (fun f => f ≫ _a1) hs0)
      have hb := comap_comap_of_commSq (embA hres hno hpr 0)
        (_c0.projectionToBase 0) s.isoZero.hom
        _a1 I0 hsq
      rw [projectionToBase_zero] at hb
      rw [controlledTransform_zero]
      exact tr_ hb s.ideal_zero.symm
  | succ t ih =>
      intro ht hdiv
      have htlt := lt_of_succ_le ht
      let _a0 := embA hres hno hpr t
      have hcen : cmI (_c0.center t)
            _a0 = s.center t := by
        rw [ambientBlowupSeq_center_eq_imageIdealSheaf]
        exact p30 _ _
      have hblow :=
        s.toBsd.isBlowup t
          (by rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact htlt)
      exact comap_eq_of_pow_mul_comap_eq T.mult (_c0.map t)
        _a0
        (embA hres hno hpr (t + 1)) (s.transitionMapSucc t)
        (_c0.center t)
        (_c0.controlledTransform I0 T.mult t)
        (_c0.controlledTransform I0 T.mult (t + 1))
        (s.center t) (s.ideal t) (s.ideal (t + 1))
        (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I0 E0 s hpr t) hcen (ih (m49 htlt) fun i hi => hdiv i $ lt_succ_of_lt hi) (pow_exceptionalIdeal_mul_controlledTransform_succ _c0 I0 T.mult t (hdiv t (lt_succ_self t)))
        (s.ideal_succ t htlt) (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hblow)

section
variable {hres : StrictTransformIsBlowupOfClosedSubscheme} {hno : BlowupPreservesNoetherian} {T : MarkedIdealWithBoundary} [IsNoetherian T.scheme] [Smooth T.structMap] [LocallyOfFiniteType T.structMap]
section
variable {j} {hj : j < T.boundary.length} {I0} {E0} {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups} {hpr : s.NoComp} {U0_} {t} (hinv : GoingUpInvariantOnOpen hres hno T j hj I0 E0 s hpr U0_ t) (ht : t ≤ s.length)
include hinv ht
theorem comap_controlledTransform :
    ((amb hres hno hpr).controlledTransform I0 T.mult t).comap
        (embA hres hno hpr t) = s.ideal t :=
  comap_controlledTransform_embeddingIntoAmbient hres hno T j hj I0 E0 s hpr t ht hinv.exists_pow_mul_eq_comap_controlledTransform

end

section
variable [CharZero T.base] {j} {hj : j < T.boundary.length} {I0} {E0} {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups} {hpr : s.NoComp} {U0_} {t} (hinv : GoingUpInvariantOnOpen hres hno T j hj I0 E0 s hpr U0_ t) (hbal : IsDerivBalanced T.base T.structMap I0 T.mult) (hm : 1 ≤ T.mult) (hV : (restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible)
include hinv hbal hm hV
theorem support_center_subset_orderAtLeastLocus
    (hU : IsClosed ((U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : CSet (s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) :
    (↑((amb hres hno hpr).center t).support :
        Set ↥((amb hres hno hpr).obj t)) ⊆
      orderAtLeastLocus ((amb hres hno hpr).controlledTransform I0 T.mult t) T.mult := by
  have ht' := ht
  have htle := le_of_lt ht
  let _a1 := ambM hres hno hpr t
  have :=
    hinv.smooth_structMap
  let _a0 := rEmb hres hno hpr U0_ t
  have :=
    isClosedImmersion_restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ hU t
  have : Smooth
      (_a0 ≫
        _a1) := by
    rw [restrictedEmbedding_comp_structureMorphism_ambientBlowupSeq T j hj I0 E0 s hres hno hpr U0_ t]
    exact smooth_iteratedPreimage_io_comp_projectionToSpec T j hj I0 E0 s U0_ hV t $ le_of_lt ht'
  have hdom := hinv.deriv_le (tMu T - 1) $ sub_lt hm m176
  have hbal' : ∀ l < tMu T,
      aDI hres hno hpr l t ^ tMu T ≤
        (amb hres hno hpr).controlledTransform I0 T.mult t ^ (tMu T - l) := by
    intro l hl
    exact pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I0 E0 s hpr hbal l hl t htle
      (hinv.exists_pow_mul_eq_comap_controlledTransform) $ hinv.divDeriv l $ le_of_lt hl
  have hc :=
    center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I0 E0 s hres hno hpr U0_ hU hm hsupp t ht'
  have hkey : cmI ((amb hres hno hpr).controlledTransform I0 T.mult t) (rEmb hres hno hpr U0_ t) = cmI (s.ideal t) (iPre U0_ t).i := by
    exact m32 (comap_comp ..) $ congrArg (fun I : (msAt s t).IdealSheafData => cmI I (iPre U0_ t).i) $ comap_controlledTransform hinv htle
  intro x hx
  rw [hc, support_imageIdealSheaf_eq_image_support] at hx
  obtain ⟨y, hy0, rfl⟩ := hx
  have _i2 : (spI (cmI (msCtr s t) (iPre U0_ t).i) : Set _) ⊆ orderAtLeastLocus (cmI (s.ideal t) (iPre U0_ t).i) T.mult := by
    intro y hy
    have hy0 := hy
    have hy1 : opIb (iPre U0_ t) y ∈ spI (msCtr s t) := by simp_all
    have hy2 := hy1
    have hc :=
      s.center_order t ht' hy2
    have hord :=
      (mem_orderAtLeastLocus_iff _ _ _).1 hc
    refine (mem_orderAtLeastLocus_iff _ _ _).2 ?_
    rwa [orderAt_comap_of_isOpenImmersion]
  have hy1 :=
    _i2 hy0
  have hy2 := hy1
  rw [← hkey] at hy2
  exact base_mem_orderAtLeastLocus_of_mem_comap T.base
    _a1
    _a0 T.mult hm
    ((amb hres hno hpr).controlledTransform I0 T.mult t)
    (fun l => aDI hres hno hpr l t) hdom hbal' y hy2

section
variable (hlift : StrictNormalCrossingsLiftFromDivisor) (hU : IsClosed ((U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0)))) (hsupp : (((s.ideal 0).support : CSet (s.toSequenceOfBlowups.schemeAt 0))) ⊆ (U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0))) (ht : t < s.length) (l) (hl : l ≤ T.mult)
include hlift hU hsupp ht hl
theorem exists_pow_mul_eq_comap_ambientDerivIdeal :
    ∃ B : ((amb hres hno hpr).obj (t + 1)).IdealSheafData,
      exceptionalIdeal ((amb hres hno hpr).map t)
          ((amb hres hno hpr).center t) ^ (T.mult - l) * B =
        (aDI hres hno hpr l t).comap
          ((amb hres hno hpr).map t) := by
  let _c0 := amb hres hno hpr
  let _c1 := aDI hres hno hpr l t
  by_cases hlm : l < tMu T
  have hnoe :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I0 E0 s hpr (t + 1) (by omega)
  have hsm :=
    hinv.smooth_structMap
  have hpow :=
    pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I0 E0 s hpr hbal l hlm t (le_of_lt ht)
      hinv.exists_pow_mul_eq_comap_controlledTransform (hinv.divDeriv l hl)
  let _a0 := ambM hres hno hpr t
  have hcs := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
    _a0
    _c1
    (_c0.controlledTransform I0 T.mult t) l T.mult hlm hpow
  have hle :=
    le_pow_of_hasStrictNormalCrossingsWith _a0
      (_c0.center t)
      _c1
      (_c0.boundaryFrom E0 t)
      (hasStrictNormalCrossingsWith_center hinv hlift hm hV hU hsupp ht) (tMu T - l)
      (fun x hx => hcs $ (support_center_subset_orderAtLeastLocus hinv hbal hm hV hU hsupp ht) hx)
  have hlen := ht
  rw [← ambientBlowupSeq_length hres hno T j hj I0 E0 s hpr] at hlen
  obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf
    (_c0.map t)
    (_c0.center t)
    _c1 (tMu T - l)
    (_c0.isBlowup t hlen) hle
  exact ⟨B, hB⟩
  simp_all

theorem ambientDerivIdeal_le_center_pow :
    aDI hres hno hpr l t ≤
      (amb hres hno hpr).center t ^ (T.mult - l) := by
  let _a0 := aDI hres hno hpr l t
  let _a1 := ambM hres hno hpr t
  let _c0 := amb hres hno hpr
  have hsm :=
    hinv.smooth_structMap
  refine le_pow_of_hasStrictNormalCrossingsWith _a1
    (_c0.center t)
    _a0
    (_c0.boundaryFrom E0 t)
    (hasStrictNormalCrossingsWith_center hinv hlift hm hV hU hsupp ht) (tMu T - l) ?_
  by_cases hlm : l < tMu T
  have htle := le_of_lt ht
  have hpow :=
    pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I0 E0 s hpr hbal l hlm t htle
      hinv.exists_pow_mul_eq_comap_controlledTransform $ hinv.divDeriv l hl
  have hcs := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
    _a1
    _a0
    (_c0.controlledTransform I0 T.mult t) l T.mult hlm hpow
  exact fun x hx => hcs $ (support_center_subset_orderAtLeastLocus hinv hbal hm hV hU hsupp ht) hx
  have h0 := sub_eq_zero_of_le $ mp_ not_lt hlm
  rw [h0, orderAtLeastLocus_zero]
  exact subset_univ _
end
end
end

end GoingUpInvariantOnOpen

theorem goingUpInvariantOnOpen_zero (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary)
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups)
    (hpr : s.NoComp)
    (U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hE0_ : InStrictNormalCrossingPosition T.structMap E0) (hjE : j < length E0)
    (hget : E0[j]'hjE = ker (rEmb hres hno hpr U0_ 0))
    (hcmp : filterNeTop (map
          (fun D => D.comap (rEmb hres hno hpr U0_ 0))
          (E0.eraseIdx j)) =
        filterNeTop (map (fun D => D.comap U0_.ι) (s.boundary 0))) :
    GoingUpInvariantOnOpen hres hno T j hj I0 E0 s hpr U0_ 0 := by
  let _c0 := amb hres hno hpr
  have hsmT : Smooth T.structMap := inferInstance
  have hftT : LocallyOfFiniteType T.structMap := inferInstance
  have hps :=
    structureMorphism_ambientBlowupSeq_zero hres hno T j hj I0 E0 s hpr
  have hbd :=
    ambientBlowupSeq_boundary_zero hres hno T j hj I0 E0 s hpr
  have hidx : j < lenL (_c0.boundaryFrom E0 0) := by
    rwa [hbd]
  have hd0 : derivIdealSheafIterate T.base T.structMap 0 I0 = I0 := by
    have h2 := maxContactIdeal_one T.base T.structMap I0
    rwa [maxContactIdeal_eq_derivIdealSheafIterate T.base T.structMap I0 1, sub_self] at h2
  have hctrl : _c0.controlledTransform I0 T.mult 0 = I0 := by
    have e1 := ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I0 E0 s hpr 0
    rw [ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate hres hno T j hj I0 E0 s hpr 0, hd0] at e1
    exact sy_ e1
  refine
    { divDeriv := ?_
      idx_lt := hidx
      deriv_le := ?_
      comap_eraseIdx := ?_
      snc_bdry := ?_
      bdry_getElem := ?_
      smooth_structMap := ?_ }
  simp_all
  intro instFt n _
  let _a0 := ambM hres hno hpr 0
  have hcongr := @derivIdealSheafIterate_congr T.base _ _
    _a0 T.structMap instFt hftT hps n I0
  have key : derivIdealSheafIterate T.base _a0 n
      (_c0.controlledTransform I0 T.mult 0) =
      aDI hres hno hpr n 0 := by
    rw [hctrl]
    exact tr_ hcongr (ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate hres hno T j hj I0 E0 s hpr n).symm
  refine le_trans (le_of_eq key) $ le_iSup_of_le n $ le_iSup_of_le le_rfl $ le_of_eq ?_
  simp [logDerivIdealSheafIterate_zero]
  rwa [hbd]
  rwa [hps, hbd]
  revert hidx
  rw [hbd]
  intro h
  exact hget
  rwa [hps]

end DivisorReduction





namespace DivisorReduction

namespace GoingUpInvariantOnOpen

theorem getElem_of_eq_map_append {al_ be_ : Type} f (L : List al_) Lx
    (L' : List be_) (hL : L' = L.map f ++ Lx) i (hi : i < length L) (hi' : i < length L') :
    L'[i]'hi' = f (L[i]'hi) :=by simp_all
theorem succ {hres : StrictTransformIsBlowupOfClosedSubscheme}
    {hno : BlowupPreservesNoetherian} {T : MarkedIdealWithBoundary}
    [IsNoetherian T.scheme] [Smooth T.structMap]
    [LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I0 : T.scheme.IdealSheafData} {E0 : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups}
    {hpr : s.NoComp}
    {U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I0 E0 s hpr U0_ t)
    (hbal : IsDerivBalanced T.base T.structMap I0 T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor)
    (hU : IsClosed ((U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : CSet (s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) :
    GoingUpInvariantOnOpen hres hno T j hj I0 E0 s hpr U0_ (t + 1) := by
  let _c0 := amb hres hno hpr
  let _c1 := restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t
  let _c2 := ambM hres hno hpr t
  have hsmT :=
    hinv.smooth_structMap
  have hNt :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I0 E0 s hpr t (by omega)
  have hNt1 :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I0 E0 s hpr (t + 1) (by omega)
  have hNs1 :=
    p25 effectiveCartierSupportContainsNoComponent hV s (t + 1) (by omega)
  have hNs :=
    p25 effectiveCartierSupportContainsNoComponent hV s t (by omega)
  have hci :=
    isClosedImmersion_restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ hU t
  have hci1 :=
    isClosedImmersion_restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ hU (t + 1)
  have htd : t < _c0.length := by
    rw [ambientBlowupSeq_length]
    exact ht
  have hpi_ := _c0.isBlowup t htd
  have hHZ : ker (restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t) ≤ (amb hres hno hpr).center t := by
    rw [center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I0 E0 s hres hno hpr U0_ hU hm hsupp t ht, imageIdealSheaf_eq_ker_subschemeio_comp]
    exact le_ker_comp _ _
  have hsncC := hinv.hasStrictNormalCrossingsWith_center_cons hlift hm hV hU hsupp ht
  have hsmT1 :=
    smooth_comp_of_isBlowupAlongIdealSheaf hsncC hpi_
  have hps :=
    structureMorphism_ambientBlowupSeq_succ hres hno T j hj I0 E0 s hpr t
  have hker1 : ker (restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ (t + 1)) = p6 ((amb hres hno hpr).map t) ((amb hres hno hpr).center t) (ker (restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ t)) := by
    let _c0 := amb hres hno hpr
    have htlt : t < s.toBsd.length := by simp_all
    let _a1 := bget' hj
    have :=
      isNoetherian_ambientBlowupSequence_schemeAt _a1.si
        s.toBsd hres hno hpr (t + 1) htlt
    have : IsLocallyNoetherian
        (_c0.obj $ t + 1) := inferInstance
    have hker :=
      ker_embeddingIntoAmbientBlowupSequence_succ _a1.si
        s.toBsd hres hno hpr t htlt
    have h := ker_preimage_io_comp_eq_strictTransform_of_isClopen
        (embA hres hno hpr t)
        (embA hres hno hpr (t + 1))
        (msTrS s t)
        (_c0.map t)
        (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I0 E0 s hpr t)
        (_c0.center t)
        (iteratedPreimage T j hj I0 E0 s U0_ t) (isClosed_iteratedPreimage T j hj I0 E0 s U0_ hU t) hker
    rwa [restrictedEmbedding_eq_io_comp_embeddingIntoAmbient, restrictedEmbedding_eq_io_comp_embeddingIntoAmbient, iteratedPreimage_succ]
  have hidx : j < (_c0.boundaryFrom E0 (t + 1)).length := by
    have h := hinv.idx_lt
    rw [boundary_length] at h ⊢
    omega
  refine ⟨?_, hidx, ?_, ?_, ?_, ?_, ?_⟩
  intro l hl i hi
  rcases lt_or_eq_of_le (mp_ lt_succ_iff hi) with h | h
  exact hinv.divDeriv l hl i h
  subst h
  exact hinv.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift hU hsupp ht l hl
  intro instFt n hn
  have hest : ∀ m, m < tMu T →
      derivIdealSheafIterate T.base _c2 m
          (aDI hres hno hpr 0 t) ≤
        ⨆ l, ⨆ _ : l ≤ m, logDerivIdealSheafIterate T.base
          _c2
          (_c1.ker) (m - l)
          (ambientDerivIdeal hres hno T j hj I0 E0 s hpr l t) := by
    intro m hmlt
    rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
    exact hinv.deriv_le m hmlt
  have hK := fun l hl =>
    hinv.ambientDerivIdeal_le_center_pow hbal hm hV hlift hU hsupp ht l hl
  have hK' : ∀ l, l ≤ tMu T →
      p5 (_c0.map t)
            (_c0.center t) ^ (tMu T - l) *
          ambientDerivIdeal hres hno T j hj I0 E0 s hpr l (t + 1) =
        (ambientDerivIdeal hres hno T j hj I0 E0 s hpr l t).comap
          (_c0.map t) := by
    intro l hl
    exact pow_exceptionalIdeal_mul_controlledTransform_succ _ _ _ _
      (hinv.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift hU hsupp ht l hl)
  have hqc : QuasiCompact
      (strictTransformio (_c0.map t)
        (_c0.center t)
        (_c1.ker)) :=
    quasiCompact_strictTransformio_of_isLocallyNoetherian _ _ _
  have key := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
    T.base _c2
    (_c0.map t)
    (_c0.center t)
    (_c1.ker)
    ((_c0.boundaryFrom E0 t).eraseIdx j) hsncC hHZ hpi_ T.mult
    (fun l => ambientDerivIdeal hres hno T j hj I0 E0 s hpr l t) hK hest
    (fun l => ambientDerivIdeal hres hno T j hj I0 E0 s hpr l $ t + 1) hK' n hn
  have e2 : ∀ l,
      logDerivIdealSheafIterate T.base (ambM hres hno hpr (t + 1))
          (ker (restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ (t + 1))) (n - l)
          (ambientDerivIdeal hres hno T j hj I0 E0 s hpr l (t + 1)) =
        logDerivIdealSheafIterate T.base
          (_c0.map t ≫
            ambM hres hno hpr t)
          (p6 (_c0.map t)
            (_c0.center t)
            (_c1.ker)) (n - l)
          (ambientDerivIdeal hres hno T j hj I0 E0 s hpr l (t + 1)) := by
    intro l
    rw [hker1]
    exact logDerivIdealSheafIterate_congr _ _ hps _ _ _
  rw [derivIdealSheafIterate_congr _ _ hps _ _]
  simp only [e2]
  have h0 :=
    (ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I0 E0 s hpr (t + 1)).symm
  rwa [h0]
  have hbs := boundary_succ _c0 E0 t
  have hlen : j < lenL (map (p6 (_c0.map t)
      (_c0.center t))
      (_c0.boundaryFrom E0 t)) := by
    simpa using hinv.idx_lt
  have hZio : (_c0.center t).comap
      _c1 =
      (s.center t).comap (iteratedPreimage T j hj I0 E0 s U0_ t).i := by
    rw [center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I0 E0 s hres hno hpr U0_ hU hm hsupp t ht]
    exact p30 _ _
  rw [hbs, eraseIdx_append_of_lt_length hlen _, eraseIdx_map,
    map_comap_strictTransform_append_exceptionalIdeal _c2
      (_c0.map t)
      (_c0.center t)
      _c1
      (restrictedEmbedding T j hj I0 E0 s hres hno hpr U0_ (t + 1))
      (restrictedBlowupMorphism T j hj I0 E0 s U0_ t)
      (restrictedEmbedding_comp_blowupMorphism T j hj I0 E0 s hres hno hpr U0_ t) hker1
      ((_c0.boundaryFrom E0 t).eraseIdx j) hsncC hHZ hpi_,
    boundary_comap_iteratedPreimage_succ T j hj I0 E0 s U0_ hV t ht, hZio]
  exact filterNeTop_map_append_congr _ (strictTransform_top _ _) _ _ _ hinv.comap_eraseIdx
  rw [hps, boundary_succ]
  exact inStrictNormalCrossingPosition_strictTransform_append _ _ _ _ hpi_ hinv.snc_bdry (hinv.hasStrictNormalCrossingsWith_center hlift hm hV hU hsupp ht)
  rw [hker1, ← hinv.bdry_getElem]
  exact getElem_of_eq_map_append
    (p6 (_c0.map t)
      (_c0.center t))
    (_c0.boundaryFrom E0 t)
    [p5 (_c0.map t)
      (_c0.center t)]
    (_c0.boundaryFrom E0 (t + 1))
    (boundary_succ _ E0 t) j hinv.idx_lt hidx
  rwa [hps]

end GoingUpInvariantOnOpen

end DivisorReduction





namespace DivisorReduction

section
variable {X : Sch}
theorem filterNeTop_append_top (L : Bdy X)
    (D : ISD X) (hD : D = ⊤) : filterNeTop (L ++ [D]) = filterNeTop L := by
  subst hD
  unfold filterNeTop
  simp [filter_append]

private theorem list_map_comap_id (L : Bdy X) :
    map (fun D => D.comap $ CategoryTheory.CategoryStruct.id X) L = L :=by simp_all
theorem exceptionalIdeal_pow_mul_eq_comap_of_eq_id (I Z J : ISD X)
    m (hJ : Z ^ m * J = I) f g
    (hf : f = CategoryTheory.CategoryStruct.id X)
    (hg : g = CategoryTheory.CategoryStruct.id X) :
    exceptionalIdeal f Z ^ m * J = (I.comap g).comap f :=by simp_all
theorem support_subset_orderAtLeastLocus_comap_of_eq_id (I Z : ISD X)
    m (h : ((support Z : Set ↥X)) ⊆ orderAtLeastLocus I m) g
    (hg : g = CategoryTheory.CategoryStruct.id X) :
    ((support Z : Set ↥X)) ⊆ orderAtLeastLocus (I.comap g) m :=by simp_all
theorem ker_opensio_comp_subschemeio_congr (Z J Z' J' : ISD X)
    (hZ : Z' = Z) (hJ : J' = J) :
    ker (comp
        (Scheme.Opens.ι $ (TopologicalSpace.Opens.map J'.subschemeι.base).obj Z'.support.compl)
        J'.subschemeι)
      = ker (comp
        (Scheme.Opens.ι $ (TopologicalSpace.Opens.map J.subschemeι.base).obj Z.support.compl)
        J.subschemeι) := by
  subst hZ
  subst hJ
  rfl
end

section
variable (T : MarkedIdealWithBoundary)
section
variable (j) (hj : j < T.boundary.length)
def boundaryDivisorEmbedding :
    (rTD hj).scheme ⟶ T.scheme :=
  subschemeι $ T.bget j hj

theorem lowerIdealAfterBlowup_eq_residualByPow_exceptionalIdeal :
    lI hj =
      residualByPow ((T.ideal.comap $ CategoryTheory.CategoryStruct.id T.scheme).comap
          (CategoryTheory.CategoryStruct.id T.scheme))
        (exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) $ ccI hj) T.mult :=
  rfl

theorem lowerBoundaryAfterBlowup_eq_map_comap_id_append :
    lB hj =
      map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme) $ ccI hj)
          (map (fun D => D.comap $ CategoryTheory.CategoryStruct.id T.scheme) T.boundary) ++
        [exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) $ ccI hj] :=
  rfl

theorem restrictTwistedToDivisor_boundary :
    (rTD hj).boundary =
      map (fun D => D.comap $ boundaryDivisorEmbedding T j hj)
        (take (T.boundary.length - 1) $ (lB hj).eraseIdx j) :=
  rfl

theorem lowerIdealAfterBlowup_eq_residualByPow :
    lI hj = residualByPow T.ideal (ccI hj) T.mult := by
  have h1 : (T.ideal.comap $ m74 T.scheme).comap
      (m74 T.scheme) = tId T := by simp_all
  let _a0 := ccI hj
  have h2 : exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) _a0
      = _a0 := by simp_all
  rw [lowerIdealAfterBlowup_eq_residualByPow_exceptionalIdeal, h1, h2]

theorem pow_mul_lowerIdealAfterBlowup_eq_ideal
    (hfac : ∃ J, ccI hj ^ T.mult * J = T.ideal) :
    ccI hj ^ T.mult * lI hj = T.ideal := by
  rw [lowerIdealAfterBlowup_eq_residualByPow]
  exact pow_mul_residualByPow T.ideal (ccI hj) T.mult hfac

def complContainedComponentsOnDivisor :
    ((rTD hj).scheme).Opens :=
  (TopologicalSpace.Opens.map (boundaryDivisorEmbedding T j hj).base).obj (ccI hj).support.compl

section
variable (s : (rTD hj).SequenceOfBlowups)
def complContainedComponentsAtSchemeZero : (s.toSequenceOfBlowups.schemeAt 0).Opens :=
  s.isoZero.hom ⁻¹ᵁ complContainedComponentsOnDivisor T j hj

theorem support_ideal_zero_subset_complOpens
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hfac : ∃ J, ccI hj ^ T.mult * J = T.ideal) :
    ((support (s.ideal 0) : CSet $ s.toSequenceOfBlowups.schemeAt 0)) ⊆
      ((complContainedComponentsAtSchemeZero T j hj s : CSet $ s.toSequenceOfBlowups.schemeAt 0)) := by
  intro x hx
  rw [s.ideal_zero] at hx
  refine mpr_ (m22) ?_
  intro hmem
  exact not_mem_support_of_mem_support_of_pow_mul (ccI hj) T.ideal
    (lI hj) T.mult ((pow_mul_lowerIdealAfterBlowup_eq_ideal T j hj hfac).symm) hord hmem $ (mem_support_comap ..).1 $ (mem_support_comap ..).1 hx

theorem isClosed_complOpens_of_isOpen
    (hopen : IsOpen $ ⇑(T.bget j hj).subschemeι ⁻¹'
      (support (ccI hj) : CSet T.scheme)) :
    IsClosed $ (complContainedComponentsAtSchemeZero T j hj s : CSet $ s.toSequenceOfBlowups.schemeAt 0) := by
  have h1 : (complContainedComponentsAtSchemeZero T j hj s : CSet $ msAt s 0)
      = (s.isoZero.hom ⁻¹' ((boundaryDivisorEmbedding T j hj) ⁻¹'
          (spI (ccI hj) : CSet T.scheme)))ᶜ := rfl
  rw [h1]
  exact (hopen.preimage $ continuous s.isoZero.hom).isClosed_compl
end

theorem lt_length_lowerBoundaryAfterBlowup :
    j < length (lB hj) := by
  rw [lowerBoundaryAfterBlowup_eq_map_comap_id_append, length_append, length_map, length_map,
    length_singleton]
  omega

theorem lowerBoundaryAfterBlowup_eq_map_strictTransform_append :
    lB hj =
      map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme) $ ccI hj)
          T.boundary ++
        [exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) $ ccI hj] :=by simp_all
theorem lt_length_map_strictTransform_boundary :
    j < (map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
      (ccI hj)) T.boundary).length := by
  rwa [length_map]
end

end

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme]
section
variable (j) (hj : j < T.boundary.length)
theorem structureMorphism_ambientBlowupSeq_eq_projectionToBase_comp
    I0 E0
    (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups)
    (hpr : s.NoComp) t :
    ambM hres hno hpr t =
      comp ((amb hres hno hpr).projectionToBase t)
        T.structMap :=
  rfl

section
variable (hb : IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme) (ccI hj)) (s : (rTD hj).SequenceOfBlowups) (hpr : s.NoComp)
theorem controlledTransform_prepend_ambientBlowupSeq_one :
    (prepend (ccI hj) hb
          (amb hres hno hpr)).controlledTransform
        T.ideal T.mult 1 =
      (lI hj).comap
        (amb hres hno hpr).isoZero.hom := by
  rw [controlledTransform_succ, controlledTransform_zero, prepend_isoObjZero,
    prepend_blowupMorphism_zero, prepend_center_zero]
  exact sy_ $ comap_id $ lI hj

theorem boundary_prepend_ambientBlowupSeq_one :
    (prepend (ccI hj) hb
          (amb hres hno hpr)).boundaryFrom
        T.boundary 1 =
      map
        (fun D => D.comap
          (amb hres hno hpr).isoZero.hom)
        (lB hj) := by
  rw [boundary_succ, boundary_zero, prepend_isoObjZero,
    prepend_blowupMorphism_zero, prepend_center_zero]
  exact sy_ $ list_map_comap_id $ lB hj
end

theorem restrictedEmbedding_zero_eq
    (s : (rTD hj).SequenceOfBlowups)
    (hpr : s.NoComp) :
    restrictedEmbedding T j hj (lI hj) (lB hj) s hres hno hpr
        (complContainedComponentsAtSchemeZero T j hj s) 0 =
      comp (Scheme.Opens.ι $ complContainedComponentsAtSchemeZero T j hj s)
        (comp s.isoZero.hom $ boundaryDivisorEmbedding T j hj) := by
  rw [restrictedEmbedding_eq_io_comp_embeddingIntoAmbient]
  exact congrArg (fun g => comp
    (p4 $ complContainedComponentsAtSchemeZero T j hj s) g) $ embeddingIntoAmbient_zero hres hno T j hj (lI hj) (lB hj) s hpr
end

end

section
variable {A B C E : Sch} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ E)
theorem comap_comp_comp
    (D : ISD E) :
    D.comap (comp f $ comp g h)
      = ((D.comap h).comap g).comap f :=by simp_all
theorem map_comap_comp_comp
    (L : Bdy E) :
    map (fun D => D.comap f)
        (map (fun D => D.comap g) $ map (fun D => D.comap h) L)
      = map (fun D => ((D.comap h).comap g).comap f) L :=by simp_all
end

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length) (s : (rTD hj).SequenceOfBlowups) (hpr : s.NoComp)
theorem comap_restrictedEmbedding_zero
    (D : tISD T) :
    D.comap (restrictedEmbedding T j hj (lI hj) (lB hj) s hres hno hpr
        (complContainedComponentsAtSchemeZero T j hj s) 0) =
      ((D.comap $ boundaryDivisorEmbedding T j hj).comap s.isoZero.hom).comap
        (Scheme.Opens.ι $ complContainedComponentsAtSchemeZero T j hj s) := by
  exact m32 (congrArg D.comap
    (restrictedEmbedding_zero_eq hres hno T j hj s hpr)) $ comap_comp_comp (p4 $ complContainedComponentsAtSchemeZero T j hj s) s.isoZero.hom (boundaryDivisorEmbedding T j hj) D

end

theorem ker_opensio_preimage_iso_comp {A B C : Sch} (e : A ≅ B) (V : Opn B)
    (g : B ⟶ C) :
    ker (comp (Scheme.Opens.ι $ e.hom ⁻¹ᵁ V)
        (comp e.hom g))
      = ker (comp (Scheme.Opens.ι V) g) := by
  have : IsIso $ e.hom.mr V := inferInstance
  have h1 : comp (p4 $ e.hom.pre V)
      (comp e.hom g)
      = comp (e.hom.mr V)
        (comp (p4 V) g) := by simp_all
  rw [h1]
  exact ker_comp_of_isIso ..

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian)
theorem lowerBoundaryAfterBlowup_getElem_eq_ker_restrictedEmbedding (T : MarkedIdealWithBoundary)
    [IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (rTD hj).SequenceOfBlowups)
    (hpr : s.NoComp) :
    (lB hj)[j]'(lt_length_lowerBoundaryAfterBlowup T j hj) =
      ker (restrictedEmbedding T j hj (lI hj) (lB hj) s hres hno
        hpr (complContainedComponentsAtSchemeZero T j hj s) 0) := by
  have hL : (lB hj)[j]'(lt_length_lowerBoundaryAfterBlowup T j hj)
      = strictTransform (CategoryTheory.CategoryStruct.id tSch T) (ccI hj)
          (bget' hj) := by simp_all
  have hA : strictTransform (CategoryTheory.CategoryStruct.id tSch T) (ccI hj)
        (bget' hj)
      = ker (comp
          (p4 $ complContainedComponentsOnDivisor T j hj) $ boundaryDivisorEmbedding T j hj) := by
    rw [strictTransform_eq_ker, strictTransformImmersion_eq, strictTransformOpens_eq]
    exact ker_opensio_comp_subschemeio_congr (ccI hj) (bget' hj)
      (cmI (ccI hj) $ CategoryTheory.CategoryStruct.id tSch T)
      (cmI (bget' hj) $ CategoryTheory.CategoryStruct.id tSch T)
      (comap_id _) $ comap_id _
  have hker : ker (restrictedEmbedding T j hj (lI hj) (lB hj) s
        hres hno hpr (complContainedComponentsAtSchemeZero T j hj s) 0)
      = ker (comp
          (p4 $ complContainedComponentsOnDivisor T j hj) $ boundaryDivisorEmbedding T j hj) := by
    exact m32 (congrArg ker
      (restrictedEmbedding_zero_eq hres hno T j hj s hpr)) $ ker_opensio_preimage_iso_comp s.isoZero (complContainedComponentsOnDivisor T j hj) $ boundaryDivisorEmbedding T j hj
  rw [hL, hA]
  exact sy_ hker

section
variable (hlift : StrictNormalCrossingsLiftFromDivisor) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (hV : T.IsAdmissible) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ENat)) (hbal : ∀ [_inst : LocallyOfFiniteType T.structMap], IsDerivBalanced T.base T.structMap T.ideal T.mult) (j) (hj : j < T.boundary.length)
include hlift hV hord hbal
theorem exists_isClosed_opens_goingUpInvariantOnOpen
    (_hZ : ccI hj ≠ ⊤)
    (hb : IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme) (ccI hj))
    (hVlow : (rTD hj).IsAdmissible)
    (s : (rTD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (_hsm : Smooth
      (comp (ccI hj).subschemeι T.structMap))
    (hsnc : HasStrictNormalCrossingsWith T.structMap (ccI hj) T.boundary)
    (_hsup : ((ccI hj).support : CSet T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult)
    (hfac : ∃ J, ccI hj ^ T.mult * J = T.ideal)
    (hopen : IsOpen (⇑(T.bget j hj).subschemeι ⁻¹'
      ((ccI hj).support : CSet T.scheme))) :
    ∃ U0_ : (s.toSequenceOfBlowups.schemeAt 0).Opens,
      IsClosed ((U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0))) ∧
      (((s.ideal 0).support : CSet (s.toSequenceOfBlowups.schemeAt 0)) ⊆
        (U0_ : CSet (s.toSequenceOfBlowups.schemeAt 0))) ∧
      (∀ [_inst : LocallyOfFiniteType T.structMap],
        IsDerivBalanced T.base T.structMap (lI hj) T.mult) ∧
      (∀ [_hsmooth : Smooth T.structMap]
         [_instFt : LocallyOfFiniteType T.structMap]
         [_instCh : CharZero T.base],
        ∀ t ≤ s.length,
          GoingUpInvariantOnOpen hres hno T j hj (lI hj) (lB hj) s hpr U0_ t) := by
  obtain ⟨_, _, _, hm, _, hsmT, hsncT⟩ := id hV
  refine ⟨complContainedComponentsAtSchemeZero T j hj s, isClosed_complOpens_of_isOpen T j hj s hopen,
    support_ideal_zero_subset_complOpens T j hj s hord hfac, ?_, ?_⟩
  intro instFt
  exact (isDerivBalanced_of_pow_mul T.base T.structMap (ccI hj) T.ideal (lI hj) T.mult
  (pow_mul_lowerIdealAfterBlowup_eq_ideal T j hj hfac).symm hord hbal)
  intro hsmooth instFt instCh t ht
  let hbal := (isDerivBalanced_of_pow_mul T.base T.structMap (ccI hj) T.ideal (lI hj) T.mult
  (pow_mul_lowerIdealAfterBlowup_eq_ideal T j hj hfac).symm hord hbal)
  let hE0_ : InStrictNormalCrossingPosition T.structMap $ lB hj := by
    have hE : InStrictNormalCrossingPosition T.structMap
        (map (cmI · $ CategoryTheory.CategoryStruct.id T.scheme) T.boundary) := by simp_all
    let _a0 := ccI hj
    have hZE : HasStrictNormalCrossingsWith T.structMap _a0
        (map (cmI · $ CategoryTheory.CategoryStruct.id T.scheme) T.boundary) := by
      rwa [list_map_comap_id]
    have h := inStrictNormalCrossingPosition_strictTransform_append T.structMap
      (CategoryTheory.CategoryStruct.id T.scheme) _a0
      (map (cmI · $ CategoryTheory.CategoryStruct.id T.scheme) T.boundary) hb hE hZE
    rw [id_comp] at h
    rwa [lowerBoundaryAfterBlowup_eq_map_comap_id_append]
  let hjE := lt_length_lowerBoundaryAfterBlowup T j hj
  let hget := lowerBoundaryAfterBlowup_getElem_eq_ker_restrictedEmbedding hres hno T j hj s hpr
  let hcmp : filterNeTop (map (fun D => cmI D $ restrictedEmbedding T j hj (lI hj) (lB hj) s hres hno hpr (complContainedComponentsAtSchemeZero T j hj s) 0) $ (lB hj).eraseIdx j) = filterNeTop (map (fun D => cmI D $ p4 $ complContainedComponentsAtSchemeZero T j hj s) $ s.boundary 0) := by
    have hsplit : (lB hj).eraseIdx j
        = (map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
              (ccI hj)) T.boundary).eraseIdx j ++
          [exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme) $ ccI hj] := by
      rw [lowerBoundaryAfterBlowup_eq_map_strictTransform_append T j hj,
        eraseIdx_append_of_lt_length $ lt_length_map_strictTransform_boundary T j hj]
    have hlen : ((map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
        (ccI hj)) T.boundary).eraseIdx j).length = bLen T - 1 := by
      rw [length_eraseIdx_of_lt $ lt_length_map_strictTransform_boundary T j hj, length_map]
    have htake : take (bLen T - 1) ((lB hj).eraseIdx j)
        = (map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
            (ccI hj)) T.boundary).eraseIdx j := by simp_all
    have hb : (rTD hj).boundary =
        map (cmI · $ boundaryDivisorEmbedding T j hj)
          ((map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
            (ccI hj)) T.boundary).eraseIdx j) := by
      rw [restrictTwistedToDivisor_boundary, htake]
    have hB0 : s.boundary 0 = map (·.comap s.isoZero.hom)
        (map (cmI · $ boundaryDivisorEmbedding T j hj)
          ((map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
            (ccI hj)) T.boundary).eraseIdx j)) := by
      rw [s.boundary_zero]
      exact congrArg (fun L => map (·.comap s.isoZero.hom) L) hb
    have hB0' : map (fun D => cmI D $ p4 $ complContainedComponentsAtSchemeZero T j hj s)
          (s.boundary 0)
        = map (fun D : tISD T =>
            (cmI (cmI D $ boundaryDivisorEmbedding T j hj) s.isoZero.hom).comap
              (p4 $ complContainedComponentsAtSchemeZero T j hj s))
            ((map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
              (ccI hj)) T.boundary).eraseIdx j) := by
      rw [hB0]
      exact map_comap_comp_comp (p4 $ complContainedComponentsAtSchemeZero T j hj s) s.isoZero.hom
        (boundaryDivisorEmbedding T j hj) _
    have htop' : (cmI (cmI (exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme)
          (ccI hj)) $ boundaryDivisorEmbedding T j hj) s.isoZero.hom).comap
          (p4 $ complContainedComponentsAtSchemeZero T j hj s) = ⊤ := by
      rw [exceptionalIdeal_eq_comap, comap_id]
      exact (restrictIdeal_eq_top_iff_forall_notMem_support
        (cmI (cmI (ccI hj) $ boundaryDivisorEmbedding T j hj) s.isoZero.hom)
        (complContainedComponentsAtSchemeZero T j hj s)).mpr
        (fun x hx hmem => (mp_ (m22) hx)
          ((mem_support_comap ..).1
            ((mem_support_comap ..).1 hmem)))
    have key : filterNeTop (map (fun D : tISD T =>
          (cmI (cmI D $ boundaryDivisorEmbedding T j hj) s.isoZero.hom).comap
            (p4 $ complContainedComponentsAtSchemeZero T j hj s))
          ((lB hj).eraseIdx j))
        = filterNeTop (map (fun D => cmI D $ p4 $ complContainedComponentsAtSchemeZero T j hj s)
            (s.boundary 0)) := by
      have h1 : map (fun D : tISD T =>
            (cmI (cmI D $ boundaryDivisorEmbedding T j hj) s.isoZero.hom).comap
              (p4 $ complContainedComponentsAtSchemeZero T j hj s))
            ((lB hj).eraseIdx j)
          = map (fun D : tISD T =>
              cmI (cmI (cmI D $ boundaryDivisorEmbedding T j hj) s.isoZero.hom)
                (p4 $ complContainedComponentsAtSchemeZero T j hj s))
              ((map (strictTransform (CategoryTheory.CategoryStruct.id T.scheme)
                (ccI hj)) T.boundary).eraseIdx j)
            ++ [(cmI (cmI (exceptionalIdeal (CategoryTheory.CategoryStruct.id T.scheme)
                (ccI hj)) $ boundaryDivisorEmbedding T j hj) s.isoZero.hom).comap
                (p4 $ complContainedComponentsAtSchemeZero T j hj s)] := by
        simp [hsplit, map_append, map_cons, map_nil]
      rw [h1, filterNeTop_append_top _ _ htop']
      exact congrArg filterNeTop hB0'.symm
    exact m32 (congrArg (fun f => filterNeTop
      (map f $ (lB hj).eraseIdx j)) $ funext $ comap_restrictedEmbedding_zero hres hno T j hj s hpr) key
  induction t with
  | zero => exact goingUpInvariantOnOpen_zero hres hno T j hj (lI hj) (lB hj) s hpr (complContainedComponentsAtSchemeZero T j hj s) hE0_ hjE hget hcmp
  | succ n ih =>
      exact GoingUpInvariantOnOpen.succ (ih $ le_of_succ_le ht) hbal hm hVlow hlift (isClosed_complOpens_of_isOpen T j hj s hopen) (support_ideal_zero_subset_complOpens T j hj s hord hfac)
        (lt_of_succ_le ht)

section
variable (hZ : ccI hj ≠ ⊤) (hb : IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme) (ccI hj)) (hVlow : (rTD hj).IsAdmissible) (s : (rTD hj).SequenceOfBlowups) (hpr : s.NoComp) (hsm : Smooth (comp (ccI hj).si T.structMap)) (hsnc : HasStrictNormalCrossingsWith T.structMap (ccI hj) T.boundary) (hsup : (support (ccI hj) : CSet T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult) (hfac : ∃ J, ccI hj ^ T.mult * J = T.ideal) (hopen : IsOpen (⇑(T.bget j hj).si ⁻¹' (support (ccI hj) : CSet T.scheme)))
include hZ hVlow hsm hsnc hsup hfac hopen
theorem comap_controlledTransform_prepend_ambientBlowupSeq
    t (ht : t ≤ s.length) :
    ((prepend (ccI hj) hb
            (amb hres hno hpr)).controlledTransform T.ideal T.mult $ t + 1).comap
        (embA hres hno hpr t) =
      s.ideal t := by
  obtain ⟨_, _, _, _, hinv⟩ :=
    exists_isClosed_opens_goingUpInvariantOnOpen hres hno hlift T hV hord hbal j hj hZ hb hVlow s hpr hsm hsnc
      hsup hfac hopen
  obtain ⟨hch, hft, _, _, _, hsmT, _⟩ := id hV
  rw [controlledTransform_prepend_succ (ccI hj) hb
      (amb hres hno hpr)
      T.ideal (lI hj) T.mult
      (controlledTransform_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr) t]
  exact (hinv t ht).comap_controlledTransform ht

theorem isMarked_prepend_ambientBlowupSeq :
    (prepend (ccI hj) hb
        (amb hres hno hpr)).IsMarked T.structMap T.ideal T.mult T.boundary := by
  let _a0 := lI hj
  let _a1 := lB hj
  let _c0 := amb hres hno hpr
  let _c1 := ccI hj
  obtain ⟨U0_, hUcl, hUsupp, hbalLow, hinv⟩ :=
    exists_isClosed_opens_goingUpInvariantOnOpen hres hno hlift T hV hord hbal j hj hZ hb hVlow s hpr hsm hsnc
      hsup hfac hopen
  obtain ⟨hch, hft, _, hm, _, hsmT, _⟩ := id hV
  obtain ⟨Jfac, hJfac⟩ := hfac
  have hctrl1 := controlledTransform_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr
  have h0 : comp
      ((prepend _c1 hb
        _c0).projectionToBase 0)
      T.structMap = tMp T := by simp_all
  have hlen : (prepend _c1 hb
      _c0).length
      = s.length + 1 := by
    rw [prepend_length, ambientBlowupSeq_length]
  refine ⟨?_, ?_, ?_, ?_⟩
  intro i hi
  rw [hlen] at hi
  cases i with
  | zero =>
      refine ⟨Jfac, ?_⟩
      rw [prepend_blowupMorphism_zero, prepend_center_zero,
        controlledTransform_zero, prepend_isoObjZero]
      exact exceptionalIdeal_pow_mul_eq_comap_of_eq_id T.ideal _c1 Jfac T.mult hJfac _ _
        rfl rfl
  | succ n =>
      have hn := lt_of_succ_lt_succ hi
      rw [prepend_blowupMorphism_succ, prepend_center_succ,
        controlledTransform_prepend_succ _c1 hb
          _c0
          T.ideal _a0 T.mult hctrl1 n]
      exact (hinv (n + 1) hn).exists_pow_mul_eq_comap_controlledTransform n $ lt_succ_self n
  intro i hi
  rw [hlen] at hi
  cases i with
  | zero =>
      rw [prepend_center_zero, controlledTransform_zero,
        prepend_isoObjZero]
      exact support_subset_orderAtLeastLocus_comap_of_eq_id T.ideal _c1 T.mult hsup _ rfl
  | succ n =>
      have hn := lt_of_succ_lt_succ hi
      rw [prepend_center_succ,
        controlledTransform_prepend_succ _c1 hb
          _c0
          T.ideal _a0 T.mult hctrl1 n]
      exact (hinv n $ m49 hn).support_center_subset_orderAtLeastLocus hbalLow hm hVlow hUcl
        hUsupp hn
  intro i hi
  rw [hlen] at hi
  cases i with
  | zero =>
      rwa [h0]
  | succ n =>
      have hn := lt_of_succ_lt_succ hi
      rw [prepend_center_succ, projectionToBase_prepend_succ]
      exact smooth_ambientBlowupSeq_center_comp hres hno T j hj _a0
        _a1 s hpr n hn
  intro i hi
  rw [hlen] at hi
  cases i with
  | zero =>
      have hb0 : (prepend _c1 hb
          _c0).boundaryFrom
          T.boundary 0 = tBd T := by simp_all
      rwa [h0, hb0]
  | succ n =>
      have hn := lt_of_succ_lt_succ hi
      have h4 := (hinv n $ m49 hn).hasStrictNormalCrossingsWith_center hlift hm hVlow hUcl hUsupp hn
      rw [structureMorphism_ambientBlowupSeq_eq_projectionToBase_comp] at h4
      rw [prepend_center_succ, projectionToBase_prepend_succ,
        boundary_prepend_succ _c1 hb
          _c0
          T.boundary _a1 (boundary_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr) n]
      exact h4
end
end
end

end DivisorReduction





namespace DivisorReduction

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
theorem toMarkedSequence_projectionToBase_eq (d : BlowupSequenceData X) (h : d.IsMarked p I m E) n :
    ((d.toMarkedBlowupSequenceData p I m E h).toMarkedSequenceOfBlowups).projectionToBase n = d.projectionToBase n :=
  p36 d n

private theorem mem_boundaryLocus_iff (s : MarkedSequenceOfBlowups p I m E) (t : ℕ) (x : ↥(s.schemeAt t)) :
    x ∈ boundaryLocus s t ↔
      ∃ D ∈ s.boundary t, x ∈ ((support D : CSet $ s.schemeAt t)) := by
  constructor
  intro hx
  unfold boundaryLocus at hx
  obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 hx
  exact ⟨D, hD, hxD⟩
  rintro ⟨D, hD, hxD⟩
  unfold boundaryLocus
  exact Set.mem_iUnion₂.2 ⟨D, hD, hxD⟩
end

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length)
section
variable (I0) (E0) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups) (hpr : s.NoComp) (t : ℕ)
theorem comap_embeddingIntoAmbient_center_ambientBlowupSeq :
    ((amb hres hno hpr).center t).comap
        (embA hres hno hpr t) = s.center t := by
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf]
  exact comap_schemeImageIdeal (embA hres hno hpr t) $ s.center t

end

section
variable (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) (ccI hj)) (s : (rTD hj).SequenceOfBlowups) (hpr : s.NoComp)
theorem prependedAmbientSeq_boundary
    (hmk : (prepend (ccI hj) hb
        (amb hres hno hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (ppMS hres hno hmk).boundary t =
      (prepend (ccI hj) hb
        (amb hres hno hpr)).boundaryFrom T.boundary t :=
  toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t

theorem prepend_boundary_succ_eq (t : ℕ) :
    (prepend (ccI hj) hb
        (amb hres hno hpr)).boundaryFrom T.boundary (t + 1) =
      (amb hres hno hpr).boundaryFrom (lB hj) t := by
  induction t with
  | zero =>
      rw [boundary_prepend_ambientBlowupSeq_one, boundary_zero]
  | succ m ih =>
      rw [boundary_succ, ih, boundary_succ, prepend_blowupMorphism_succ,
        prepend_center_succ]
      rfl
end

theorem ambientMarkedSeq_boundary
    (s : (rD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (amb hres hno hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (pMS hres hno hmk).boundary t =
      (amb hres hno hpr).boundaryFrom T.boundary t :=
  toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t
end

section
variable {Y : Sch}
section
variable (L : Bdy Y)
section
variable (j : ℕ)
def unionSupportsExcept : Set ↥Y :=
  ⋃ i : Fin L.length, ⋃ (_ : (i : ℕ) ≠ j), (support (L.get i) : Set ↥Y)

theorem exists_mem_support_of_mem_otherLocusOfList
    {x : ↥Y} (hx : x ∈ unionSupportsExcept L j) :
    ∃ i : ℕ, ∃ h : i < length L, i ≠ j ∧ x ∈ ((L[i].support : Set ↥Y)) := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  obtain ⟨h1, h2⟩ := mem_iUnion.1 hi
  exact ⟨i.1, i.2, h1, h2⟩

theorem isClosed_otherLocusOfList :
    IsClosed $ unionSupportsExcept L j := by
  refine isClosed_iUnion_of_finite ?_
  intro i
  exact isClosed_iUnion_of_finite fun _ => (spI $ L.get i).2
end

theorem support_subset_otherLocusOfList (j i : ℕ)
    (hi : i < length L) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept L j := by
  intro x hx
  exact mem_iUnion.2 ⟨⟨i, hi⟩, mem_iUnion.2 ⟨hij, hx⟩⟩

theorem support_subset_otherLocusOfList_append_singleton
    (e : ISD Y) (j : ℕ) (hj : j < length L) :
    ((support e : Set ↥Y)) ⊆ unionSupportsExcept (L ++ [e]) j := by
  have h1 : lenL L < length (L ++ [e]) := by
    rw [length_append]
    simp
  have h2 := support_subset_otherLocusOfList (L ++ [e]) j L.length h1 $ by omega
  have h3 : (L ++ [e])[lenL L]'h1 = e := by simp
  rwa [h3] at h2
end

theorem support_subset_otherLocusOfList_append_left (L M : Bdy Y)
    (j i : ℕ) (hi : i < length L) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept (L ++ M) j := by
  have h1 : i < length (L ++ M) := by
    rw [length_append]
    omega
  have h2 := support_subset_otherLocusOfList (L ++ M) j i h1 hij
  rwa [getElem_append_left hi] at h2
end

section
variable (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length)
theorem isNoetherian_boundary_subscheme :
    IsNoetherian (T.bget j hj).subscheme := by
  let _a0 := bget' hj
  have : LocallyOfFiniteType _a0.si :=
    inferInstance
  have : QuasiCompact _a0.si := inferInstance
  exact isNoetherian_of_locallyOfFiniteType _a0.si

end

theorem apply_eq_apply_of_comp_eq {A B C D : Sch} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ D) (g' : D ⟶ C) (e : f ≫ g = f' ≫ g') (x : ↥A) : ⇑g (⇑f x) = ⇑g' (⇑f' x) :=
  congrArg (fun m => m x) e

theorem embeddingIntoAmbientBlowupSequence_comp_projectionToBase {S X : Sch} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsNoetherian X]
    (d : BlowupSequenceData S) (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hno : BlowupPreservesNoetherian)
    (hcen : ∀ i < d.length, ∀ W ∈ irreducibleComponents ↥(d.obj i), ¬W ⊆ ↑(d.center i).support)
    (n : ℕ) :
    embeddingIntoAmbientBlowupSequence ι d hres hno hcen n ≫ (ambientBlowupSequence ι d hres hno hcen).projectionToBase n =
      d.projectionToBase n ≫ ι := by
  induction n with
  | zero =>
    rw [projectionToBase_zero, projectionToBase_zero, embeddingIntoAmbientBlowupSequence_zero, congrArg Iso.hom $ ambientBlowupSequence_isoObjZero ι d hres hno hcen]
    exact comp_id _
  | succ m ih =>
    rw [projectionToBase_succ, projectionToBase_succ, ← assoc,
      embeddingIntoAmbientBlowupSequence_succ_comp_map ι d hres hno hcen m, assoc, ih, ← assoc]

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length)
section
variable (I0) (E0 : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I0 E0).SequenceOfBlowups) (hpr : s.NoComp)
theorem embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeio (t : ℕ) :
    embA hres hno hpr t ≫
        (amb hres hno hpr).projectionToBase t =
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj t ≫ (T.bget j hj).si := by
  have h := embeddingIntoAmbientBlowupSequence_comp_projectionToBase (bgetT hj).si
    s.toBsd hres hno hpr t
  rwa [MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase (p54 s) t]

theorem boundaryLocus_subset_preimage_otherLocus
    (hjE : j < E0.length) :
    ∀ t, t ≤ s.length →
      boundaryLocus s t ⊆
        ⇑(embA hres hno hpr t) ⁻¹'
          unionSupportsExcept ((amb hres hno hpr).boundaryFrom E0 t) j := by
  let _c0 := amb hres hno hpr
  let _c1 := embA hres hno hpr 0
  intro t
  induction t with
  | zero =>
      intro _ x hx
      obtain ⟨D, hD, hxD⟩ := (mem_boundaryLocus_iff s 0 x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_zero] at hD
      obtain ⟨D0_, hD0_, rfl⟩ := mem_map.1 hD
      obtain ⟨D1, hD1_, rfl⟩ := mem_map.1 hD0_
      obtain ⟨i, hi, hij, hget⟩ := mem_eraseIdx_iff_getElem.1 $ mem_of_mem_take hD1_
      subst hget
      have hlen0 : i < (_c0.boundaryFrom E0 0).length := by
        rw [boundary_length]
        omega
      have hentry0 : (_c0.boundaryFrom E0 0)[i]'hlen0
          = (E0[i]'hi).comap (bdIzH _c0) := by
        simp [boundary_zero]
      have hmem2 := Scheme.IdealSheafData.mem_support_comap.mp $ Scheme.IdealSheafData.mem_support_comap.mp hxD
      have _i10 : embA hres hno hpr 0 ≫ (amb hres hno hpr).isoZero.hom = s.isoZero.hom ≫ (bgetT hj).si := by
        have h := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeio hres hno T j hj I0 E0 s hpr 0
        rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase, MarkedSequenceOfBlowups.projectionToBase_zero,
          projectionToBase_zero] at h
        exact h
      have hkey := apply_eq_apply_of_comp_eq _c1
        _c0.isoZero.hom s.isoZero.hom
        (bgetT hj).si
        _i10 x
      have hmem3 : (bdIzH _c0)
          (_c1 x) ∈ (E0[i]'hi).support := by
        rwa [hkey]
      show _c1 x ∈
        unionSupportsExcept (_c0.boundaryFrom E0 0) j
      refine support_subset_otherLocusOfList _ j i hlen0 hij ?_
      rw [hentry0]
      exact Scheme.IdealSheafData.mem_support_comap.mpr hmem3
  | succ n ih =>
      intro ht x hx
      have hn := ht
      have :=
        (@isNoetherian_schemeAt _ s.toSequenceOfBlowups (isNoetherian_boundary_subscheme T j hj) (n + 1) hn)
      have :=
        isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I0 E0 s hpr (n + 1) hn
      have hmapeq : ∀ y,
          (_c0.map n)
              ((embA hres hno hpr $ n + 1) y)
            = (embA hres hno hpr n) ((s.transitionMapSucc n) y) := by
        intro y
        exact apply_eq_apply_of_comp_eq _ _ _ _
          (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I0 E0 s hpr n) y
      have hcenter : (embA hres hno hpr n) ⁻¹' (((amb hres hno hpr).center n).support : Set _) = ((s.center n).support : CSet $ s.schemeAt n) := by
        ext x
        let _a0 := (amb hres hno hpr).center n
        let _a1 := embA hres hno hpr n
        have h : x ∈ (_a0.comap
              _a1).support ↔
            _a1 x ∈
              ((_a0.support) : Set _) :=
          mem_support_comap ..
        rw [comap_embeddingIntoAmbient_center_ambientBlowupSeq] at h
        exact h.symm
      obtain ⟨D, hD, hxD⟩ := (mem_boundaryLocus_iff s (n + 1) x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_succ s n hn] at hD
      rcases mem_append.1 hD with hD' | hD'
      obtain ⟨D0_, hD0_, rfl⟩ := mem_map.1 hD'
      rw [support_strictTransform_eq_closure_sdiff (s.transitionMapSucc n) (s.center n) D0_] at hxD
      refine ((isClosed_otherLocusOfList _ _).preimage (embA hres hno hpr $ n + 1).continuous).closure_subset_iff.2 ?_ hxD
      intro y hy
      have hy2 := fun hcon =>
        hy.2 $ (mem_support_comap ..).2 hcon
      obtain ⟨i, hi, hij, hmem⟩ :=
        exists_mem_support_of_mem_otherLocusOfList (_c0.boundaryFrom E0 n) j $ (ih $ m49 hn) $ (mem_boundaryLocus_iff s n _).2 ⟨D0_, hD0_, (mem_support_comap ..).1 hy.1⟩
      have hnotZ : (embA hres hno hpr n) ((s.transitionMapSucc n) y)
          ∉ ((_c0.center n).support : Set _) := by
        intro hcon
        exact hy2 $ (ext_iff.1 hcenter $ ⇑(s.transitionMapSucc n) y).1 hcon
      have hstep : (embA hres hno hpr $ n + 1) y ∈
          ((strictTransform (_c0.map n)
              (_c0.center n)
              ((_c0.boundaryFrom E0 n)[i]'hi)).support : Set _) := by
        rw [support_strictTransform_eq_closure_sdiff]
        refine subset_closure ?_
        constructor
        refine (mem_support_comap ..).2 ?_
        rwa [hmapeq y]
        intro hcon
        have hcon' := (mem_support_comap ..).1 hcon
        rw [hmapeq y] at hcon'
        exact hnotZ hcon'
      have hlen := hi
      rw [← length_map] at hlen
      have hentry : (map
            (strictTransform (_c0.map n)
              (_c0.center n))
            (_c0.boundaryFrom E0 n))[i]'hlen
          = strictTransform (_c0.map n)
              (_c0.center n)
              ((_c0.boundaryFrom E0 n)[i]'hi) := by
        simp
      have hfin := support_subset_otherLocusOfList_append_left
        (map (strictTransform (_c0.map n)
          (_c0.center n))
          (_c0.boundaryFrom E0 n))
        [exceptionalIdeal (_c0.map n)
          (_c0.center n)] j i hlen hij
      rw [hentry] at hfin
      show (embA hres hno hpr $ n + 1) y ∈
        unionSupportsExcept (_c0.boundaryFrom E0 $ n + 1) j
      rw [boundary_succ]
      exact hfin hstep
      have hDe : D = exceptionalIdeal (s.transitionMapSucc n) (s.center n) := by
        simpa using hD'
      subst hDe
      rw [exceptionalIdeal_eq_comap] at hxD
      have hjlen : j < (map
          (strictTransform (_c0.map n)
            (_c0.center n))
          (_c0.boundaryFrom E0 n)).length := by
        rw [length_map, boundary_length]
        omega
      have hmem : (embA hres hno hpr $ n + 1) x ∈
          ((exceptionalIdeal (_c0.map n)
            (_c0.center n)).support : Set _) := by
        rw [exceptionalIdeal_eq_comap]
        refine (mem_support_comap ..).2 ?_
        rw [hmapeq x]
        exact (ext_iff.1 hcenter $ (s.transitionMapSucc n) x).2 $ (mem_support_comap ..).1 hxD
      show (embA hres hno hpr $ n + 1) x ∈
        unionSupportsExcept (_c0.boundaryFrom E0 $ n + 1) j
      rw [boundary_succ]
      exact support_subset_otherLocusOfList_append_singleton _ _ j hjlen hmem
end

theorem projectionToSpec_eq_comp_prependedAmbientSeq
    (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ ccI hj)
    (s : (rTD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (prepend (ccI hj) hb
        (amb hres hno hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) t :
    projectionToSpec s t =
      embA hres hno hpr t ≫
        projectionToSpec (ppMS hres hno hmk) (t + 1) := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeio hres hno T j hj
    (lI hj) (lB hj) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hstruct := congrArg (fun f => f ≫ tMp T) $ (toMarkedSequence_projectionToBase_eq _ hmk $ t + 1).trans $ projectionToBase_prepend_succ (ccI hj) hb (amb hres hno hpr) t
  rw [← projectionToSpec_eq] at hstruct
  rw [hstruct, projectionToSpec_eq]
  exact ((tr_ (sy_ $ assoc _ _ _) $ congrArg (fun f => f ≫ tMp T) h6).trans $ assoc _ _ _).symm

theorem projectionToSpec_eq_comp_ambientMarkedSeq
    (s : (rD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (amb hres hno hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) t :
    projectionToSpec s t =
      embA hres hno hpr t ≫
        projectionToSpec (pMS hres hno hmk) t := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeio hres hno T j hj
    (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hstruct := congrArg (fun f => f ≫ tMp T) $ toMarkedSequence_projectionToBase_eq _ hmk t
  rw [← projectionToSpec_eq] at hstruct
  rw [hstruct, projectionToSpec_eq]
  exact ((tr_ (sy_ $ assoc _ _ _) $ congrArg (fun f => f ≫ tMp T) h6).trans $ assoc _ _ _).symm
end

theorem otherBoundaryLocus_eq_otherLocusOfList {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
    {E : Bdy X} (S : MarkedSequenceOfBlowups p I m E) (j t : ℕ) :
    otherBoundaryLocus S j t = unionSupportsExcept (S.boundary t) j := rfl

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) [IsNoetherian T.scheme] (j) (hj : j < T.boundary.length)
theorem boundaryLocus_subset_preimage_otherBoundaryLocus
    (s : (rD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (amb hres hno hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    boundaryLocus s t ⊆
      ⇑(embA hres hno hpr t) ⁻¹'
        otherBoundaryLocus (pMS hres hno hmk) j t := by
  have hlowerEq : lowerBoundaryWithoutBlowup T = T.boundary := by simp [lowerBoundaryWithoutBlowup_eq]
  have hjE := hj
  rw [← hlowerEq] at hjE
  have hmain := boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
    s hpr hjE t $ le_of_lt ht
  let _a0 := amb hres hno hpr
  have h1 : (pMS hres hno hmk).boundary t =
      _a0.boundaryFrom
        (lowerBoundaryWithoutBlowup T) t := by
    rw [ambientMarkedSeq_boundary]
    exact congrArg
      (_a0.boundaryFrom · t)
      hlowerEq.symm
  rwa [tr_ (otherBoundaryLocus_eq_otherLocusOfList _ j t) (congrArg (unionSupportsExcept · j) h1)]

theorem boundaryLocus_subset_preimage_otherBoundaryLocus_succ
    (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ ccI hj)
    (s : (rTD hj).SequenceOfBlowups)
    (hpr : s.NoComp)
    (hmk : (prepend (ccI hj) hb
        (amb hres hno hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    boundaryLocus s t ⊆
      ⇑(embA hres hno hpr t) ⁻¹'
        otherBoundaryLocus (ppMS hres hno hmk) j (t + 1) := by
  let _a0 := lB hj
  have hjE : j < lenL _a0 := by
    let _a1 := ccI hj
    show j < lenL (map (p6 (𝟙 tSch T) _a1)
      (map (cmI · $ 𝟙 tSch T) T.boundary) ++
      [p5 (𝟙 tSch T) _a1])
    simp [length_append, length_map, length_cons, length_nil]
    omega
  have hmain := boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lI hj)
    _a0 s hpr hjE t $ le_of_lt ht
  have h1 : (ppMS hres hno hmk).boundary (t + 1) =
      (amb hres hno hpr).boundaryFrom
        _a0 t := by
    rw [prependedAmbientSeq_boundary, prepend_boundary_succ_eq]
  rwa [tr_ (otherBoundaryLocus_eq_otherLocusOfList _ j $ t + 1) (congrArg (unionSupportsExcept · j) h1)]
end

end DivisorReduction





section
variable {al_ : Type}
theorem cons_take_succ_inj (j : ℕ) (a b : al_) (t1_ t2_ : List al_)
    (h : take (j + 1) (a :: t1_) = take (j + 1) (b :: t2_)) :
    a = b ∧ take j t1_ = take j t2_ :=
  Eq.mp (injEq a (take j t1_) b $ take j t2_) h

theorem get_eq_get_of_take_add_one_eq :
    ∀ (j : ℕ) (l1_ l2_ : List al_), take (j + 1) l1_ = take (j + 1) l2_ →
      ∀ (h1_ : j < length l1_) (h2_ : j < length l2_), l1_.lget j h1_ = l2_.lget j h2_ := by
  intro j
  induction j with
  | zero =>
    intro l1_ l2_ htake h1_ h2_
    cases l1_ with
    | nil => exact absurd h1_ $ not_lt_zero 0
    | cons a t1_ =>
      cases l2_ with
      | nil => exact absurd h2_ $ not_lt_zero 0
      | cons b t2_ => exact an1 $ cons_take_succ_inj 0 a b t1_ t2_ htake
  | succ j ih =>
    intro l1_ l2_ htake h1_ h2_
    cases l1_ with
    | nil => exact absurd h1_ $ not_lt_zero $ j + 1
    | cons a t1_ =>
      cases l2_ with
      | nil => exact absurd h2_ $ not_lt_zero $ j + 1
      | cons b t2_ =>
        exact ih t1_ t2_ (cons_take_succ_inj (j + 1) a b t1_ t2_ htake).2
          (lt_of_succ_lt_succ h1_) $ lt_of_succ_lt_succ h2_

theorem get_eq_get_of_take_succ_eq (l1_ l2_ : List al_) j
    (htake : take (j + 1) l1_ = take (j + 1) l2_)
    (h1_ : j < length l1_) (h2_ : j < length l2_) :
    l1_.lget j h1_ = l2_.lget j h2_ :=
  get_eq_get_of_take_add_one_eq j l1_ l2_ htake h1_ h2_
end

section
variable {X Y : Sch} (f : Y ⟶ X)
theorem nontrivialPart_map_comap
    (l : Bdy X) :
    nontrivialPart (l.map fun D => D.comap f) =
      nontrivialPart ((nontrivialPart l).map fun D => D.comap f) := by
  unfold nontrivialPart
  induction l with
  | nil => simp
  | cons D l ih =>
    by_cases hD : D = ⊤
    subst hD
    simp [comap_top, ih]
    simp [filter_cons, hD, ih]

theorem MarkedIdealWithBoundary.SameNontrivialBoundary.comap
    {E E' : Bdy X} (h : SameNontrivialBoundary E E') :
    SameNontrivialBoundary (E.map fun D => D.comap f) $ E'.map fun D => D.comap f := by
  rw [sameNontrivialBoundary_iff] at h ⊢
  rw [nontrivialPart_map_comap f E, nontrivialPart_map_comap f E', h]
end

section
variable {X : Sch}
section
variable {a : ISD X} {s t : Bdy X}
theorem nontrivialPart_cons_congr
    (h : nontrivialPart s = nontrivialPart t) :
    nontrivialPart (a :: s) = nontrivialPart (a :: t) := by
  simp [nontrivialPart] at h
  simp [nontrivialPart]
  rw [filter_cons, filter_cons, h]

theorem nontrivialPart_eq_of_cons_eq
    (h : nontrivialPart (a :: s) = nontrivialPart (a :: t)) :
    nontrivialPart s = nontrivialPart t := by
  simp [nontrivialPart] at h
  simp [nontrivialPart]
  rw [filter_cons, filter_cons] at h
  split_ifs at h with hp
  simpa using h
  exact h
end

theorem nontrivialPart_eraseIdx_eq_of_take_succ_eq j :
    ∀ E E' : Bdy X,
      nontrivialPart E = nontrivialPart E' →
      take (j + 1) E = take (j + 1) E' →
      nontrivialPart (E.eraseIdx j) = nontrivialPart (E'.eraseIdx j) := by
  induction j with
  | zero =>
    intro E E' h htake
    cases E with
    | nil =>
      cases E' with
      | nil => rfl
      | cons b t => simp at htake
    | cons a s =>
      cases E' with
      | nil => simp at htake
      | cons b t =>
        rw [take_succ_cons, take_succ_cons, injEq] at htake
        obtain ⟨hab, -⟩ := htake
        subst hab
        exact nontrivialPart_eq_of_cons_eq h
  | succ j ih =>
    intro E E' h htake
    cases E with
    | nil =>
      cases E' with
      | nil => rfl
      | cons b t => simp at htake
    | cons a s =>
      cases E' with
      | nil => simp at htake
      | cons b t =>
        rw [take_succ_cons, take_succ_cons, injEq] at htake
        obtain ⟨hab, htl⟩ := htake
        subst hab
        exact nontrivialPart_cons_congr $ ih s t (nontrivialPart_eq_of_cons_eq h) htl

theorem MarkedIdealWithBoundary.SameNontrivialBoundary.eraseIdx {E E' : Bdy X}
    (h : SameNontrivialBoundary E E') (j : ℕ)
    (htake : take (j + 1) E = take (j + 1) E') :
    SameNontrivialBoundary (E.eraseIdx j) $ E'.eraseIdx j :=
  (sameNontrivialBoundary_iff _ _).2
    (nontrivialPart_eraseIdx_eq_of_take_succ_eq j E E' ((sameNontrivialBoundary_iff _ _).1 h) htake)
end

theorem surjective_snd_of_isPullback_of_surjective {X Y S S' : Sch} (σ : S ⟶ X) (σ' : S' ⟶ Y) (ph_ : Y ⟶ X)
    (ps_ : S' ⟶ S) [Surjective ph_] (hpb : IsPullback σ' ps_ ph_ σ) :
    Surjective ps_ := by
  exact m122 hpb inferInstance

namespace DivisorReduction

section
variable {X Y : Sch} (h : Y ⟶ X) (D : ISD X) (D' : ISD Y) (hD : D' = D.comap h)
include hD
theorem ker_subschemeio_le_ker_comp :
    ker D.si ≤ ker (subschemeι D' ≫ h) := by
  subst hD
  rw [ker_subschemeι, ker_comp,
    ker_subschemeι]
  exact le_map_comap D h

theorem exists_subscheme_hom_comp_subschemeio_eq :
    ∃ g,
      g ≫ subschemeι D = subschemeι D' ≫ h ∧
        ∀ I0 : ISD X,
          (I0.comap D.si).comap g = (I0.comap h).comap D'.si := by
  let _a0 := m64 D.si (siI D' ≫ h) $ ker_subschemeio_le_ker_comp h D D' hD
  have hsq : _a0 ≫ siI D = siI D' ≫ h :=
    m154 ..
  refine ⟨_a0, hsq, fun I0 => ?_⟩
  rw [← comap_comp, hsq,
    comap_comp]

def subschemeMapOfComap : subscheme D' ⟶ subscheme D :=
  (exists_subscheme_hom_comp_subschemeio_eq h D D' hD).choose

theorem subschemeMapOfComap_comp :
    subschemeMapOfComap h D D' hD ≫ subschemeι D = subschemeι D' ≫ h :=
  (exists_subscheme_hom_comp_subschemeio_eq h D D' hD).choose_spec.1

theorem comap_subschemeMapOfComap (I0 : ISD X) :
    (I0.comap D.si).comap (subschemeMapOfComap h D D' hD) = (I0.comap h).comap D'.si :=
  (exists_subscheme_hom_comp_subschemeio_eq h D D' hD).choose_spec.2 I0

theorem map_comap_comap_subschemeio
    (M : Bdy X) :
    ((M.map fun I => I.comap h).map fun I => I.comap D'.si)
      = (M.map fun I => I.comap D.si).map fun I => I.comap $ subschemeMapOfComap h D D' hD := by
  induction M with
  | nil => rfl
  | cons I t ih =>
    simp only [map_cons]
    rw [comap_subschemeMapOfComap h D D' hD I, ih]

theorem sameNontrivialBoundary_comap_subschemeio (M : Bdy X)
    (M' : Bdy Y)
    (hM : SameNontrivialBoundary M' $ M.map fun I => I.comap h) :
    SameNontrivialBoundary (M'.map fun I => I.comap D'.si)
      ((M.map fun I => I.comap D.si).map fun I => I.comap $ subschemeMapOfComap h D D' hD) := by
  rw [← map_comap_comap_subschemeio h D D' hD M]
  exact hM.comap D'.si
end

def componentsInOrderLocusIdeal {X : Sch} (I : ISD X) (m : ℕ) (D : ISD X) :
    X.IdealSheafData :=
  @dite X.IdealSheafData
    (IsOpen {x : ↥D.subscheme | connectedComponent x ⊆ ⇑D.si ⁻¹' orderAtLeastLocus I m})
    (Classical.propDecidable _)
    (fun hop =>
      ker
        (Scheme.Opens.i
            ({ carrier := {x : ↥D.subscheme |
                  connectedComponent x ⊆ ⇑D.si ⁻¹' orderAtLeastLocus I m},
                is_open' := hop } : D.subscheme.Opens) ≫
          subschemeι D))
    (fun _ => ⊤)

theorem containedComponentsIdeal_eq_componentsInOrderLocusIdeal (T : MarkedIdealWithBoundary) j
    (hj : j < T.boundary.length) :
    ccI hj = componentsInOrderLocusIdeal T.ideal T.mult (T.bget j hj) := by
  unfold componentsInOrderLocusIdeal
  split_ifs with h
  exact containedComponentsIdeal_eq_ker T j hj h
  exact containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

structure SmoothPullbackCompatibility : Prop where
  comap_ne_top : ∀ (X Y : Sch) (h : Y ⟶ X) [Surjective h]
    (Z : ISD X), Z ≠ ⊤ → Z.comap h ≠ ⊤
  coSupport_comap : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ m : ℕ, orderAtLeastLocus (T.ideal.comap h) m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m
  isPullback_inducedHom : ∀ (X Y : Sch) (h : Y ⟶ X) (D : ISD X)
    D' hD,
      IsPullback (subschemeMapOfComap h D D' hD) D'.si D.si h
  smooth_of_isPullback : ∀ (X Y S S' : Sch) (σ : S ⟶ X) (σ' : S' ⟶ Y) (ph_ : Y ⟶ X)
    (ps_ : S' ⟶ S), IsPullback σ' ps_ ph_ σ → Smooth ph_ → Smooth ps_
  lowerIdealPre_comap : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ (E' : Bdy Y),
        SameNontrivialBoundary (T.pbA q h).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < length E'),
          take (j + 1) E' = take (j + 1) (T.pbA q h).boundary →
          (T.pbB q h E').IsAdmissible →
          T.IsOrderBoundedByMult →
          containedComponentsIdeal (T.pbB q h E') j hjE = (ccI hj).comap h →
            lowerIdealAfterBlowup (T.pbB q h E') j hjE =
              (lI hj).comap h
  boundaryEquiv_restrictedBoundary_comap : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ (E' : Bdy Y),
        SameNontrivialBoundary (T.pbA q h).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < length E'),
          take (j + 1) E' = take (j + 1) (T.pbA q h).boundary →
          (T.pbB q h E').IsAdmissible →
          T.IsOrderBoundedByMult →
          containedComponentsIdeal (T.pbB q h E') j hjE = (ccI hj).comap h →
            SameNontrivialBoundary
              (take (length E' - 1)
                ((lowerBoundaryAfterBlowup (T.pbB q h E') j hjE).eraseIdx j))
              (map (fun D => D.comap h)
                (take (T.boundary.length - 1) $ (lB hj).eraseIdx j))
  preIdeal_comap : ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ (E' : Bdy Y),
        SameNontrivialBoundary (T.pbA q h).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < length E'),
          take (j + 1) E' = take (j + 1) (T.pbA q h).boundary →
          (T.pbB q h E').IsAdmissible →
            containedComponentsIdeal (T.pbB q h E') j hjE = (ccI hj).comap h

section
variable (T : MarkedIdealWithBoundary)
section
variable (j) (hj : j < T.boundary.length)
def divisorPullbackMap
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData) (Y : Sch)
    (h : Y ⟶ T.scheme) (D' : Y.IdealSheafData) (hD : D' = (T.bget j hj).comap h) :
    subscheme D' ⟶ (restrictToBoundaryDivisor T j hj I0 E0).scheme :=
  subschemeMapOfComap h (T.bget j hj) D' hD

theorem get_eq_comap_get_boundary (Y : Sch)
    (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme) (E' : Bdy Y)
    (hjE : j < length E')
    (htake : take (j + 1) E' = take (j + 1) (T.pbA q h).boundary) :
    E'.lget j hjE = (T.bget j hj).comap h := by
  have htake' : take (j + 1) E' =
      take (j + 1) (map (fun D : tISD T => cmI D h) T.boundary) := by
    rw [htake, pullbackAlong_boundary T Y q h]
    rfl
  have hlen : j < lenL (map (fun D : tISD T => cmI D h) T.boundary) := by
    simpa using hj
  rw [get_eq_get_of_take_succ_eq E'
    (map (fun D : tISD T => cmI D h) T.boundary) j htake' hjE hlen]
  simp
end

theorem lowerIdealWithoutBlowup_withBoundary (Y : Sch)
    (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme) (E' : Bdy Y) :
    lowerIdealWithoutBlowup (T.pbB q h E') = (lowerIdealWithoutBlowup T).comap h := by
  simp [lowerIdealWithoutBlowup, withBoundary_ideal (pbAT T q h) E', pullbackAlong_ideal T Y q h]
  exact comap_id ..
end

section
variable (hbc : SmoothPullbackCompatibility)
include hbc
theorem isPullback_divisorPullbackMap (T : MarkedIdealWithBoundary) (j : ℕ)
    (hj : j < T.boundary.length) (I0 : T.scheme.IdealSheafData)
    (E0 : List T.scheme.IdealSheafData) (Y : Sch) (h : Y ⟶ T.scheme)
    (D' : Y.IdealSheafData) (hD : D' = (T.bget j hj).comap h) :
    IsPullback (divisorPullbackMap T j hj I0 E0 Y h D' hD) D'.si
      (T.bget j hj).si h :=
  hbc.isPullback_inducedHom _ _ h _ D' hD

theorem orderAtLeastLocus_withBoundary_pullbackAlong (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible)
    (Y : Sch) q (h : Y ⟶ T.scheme)
    [Smooth h] (hq : h ≫ T.structMap = q) E'
    m :
    orderAtLeastLocus (T.pbB q h E').ideal m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m :=
  hbc.coSupport_comap T hV Y q h hq m

theorem comap_ne_top_of_surjective {X Y : Sch} (h : Y ⟶ X)
    [Surjective h] (Z : ISD X) (hZ : Z ≠ ⊤) : Z.comap h ≠ ⊤ :=
  hbc.comap_ne_top _ _ h Z hZ
end

theorem componentsInOrderLocusIdeal_congr {X : Sch} (I : ISD X) (m : ℕ)
    {D D' : ISD X} (hD : D = D') :
    componentsInOrderLocusIdeal I m D = componentsInOrderLocusIdeal I m D' := by
  rw [hD]

private theorem take_length_sub_one_eraseIdx {al_ : Type} (l : List al_) j (hj : j < length l) :
    take (length l - 1) (l.eraseIdx j) = l.eraseIdx j := by
  refine take_of_length_le ?_
  have h2 := length_eraseIdx_add_one hj
  omega

theorem sameNontrivialBoundary_lowerBoundaryWithoutBlowup (T : MarkedIdealWithBoundary) (j : ℕ) (hj : j < T.boundary.length)
    (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
    (E' : Bdy Y)
    (hBE : SameNontrivialBoundary (T.pbA q h).boundary E')
    (htake : take (j + 1) E' = take (j + 1) (T.pbA q h).boundary)
    (hjE : j < length E') :
    SameNontrivialBoundary
      (take (length E' - 1)
        ((lowerBoundaryWithoutBlowup $ T.pbB q h E').eraseIdx j))
      (map (fun D => D.comap h)
        (take (T.boundary.length - 1) $ (lowerBoundaryWithoutBlowup T).eraseIdx j)) := by
  have hpb :=
    (pullbackAlong_boundary T Y q h).symm
  let _a0 := T.pbA q h
  exact (sameNontrivialBoundary_iff _ _).2
    (tr_ (tr_ (congrArg nontrivialPart $ (congrArg (fun l : Bdy Y => take (length E' - 1) $ l.eraseIdx j) $ (lowerBoundaryWithoutBlowup_eq $ tWB _a0 E').trans $ withBoundary_boundary _a0 E').trans $ take_length_sub_one_eraseIdx E' j hjE)
        (tr_ ((sameNontrivialBoundary_iff _ _).1 $ ((sameNontrivialBoundary_iff _ _).2 $ tr_ (congrArg nontrivialPart hpb) $ (sameNontrivialBoundary_iff _ _).1 hBE).symm.eraseIdx j $ htake.trans $ congrArg (fun l => take (j + 1) l) hpb.symm)
          (congrArg nontrivialPart $ eraseIdx_map (fun D : tISD T => cmI D h) T.boundary j)))
      (congrArg (fun l =>
          nontrivialPart
            (map (fun D : tISD T => cmI D h) l)) ((congrArg (fun l : List (tISD T) => take (bLen T - 1) $ l.eraseIdx j) $ lowerBoundaryWithoutBlowup_eq T).trans $ take_length_sub_one_eraseIdx T.boundary j hj).symm))

private theorem heq_toSequenceOfBlowups_of_eq__b1 (L : PrincipalizationAssignment) {S1_ S2_ : MarkedIdealWithBoundary}
    (hS : S1_ = S2_) : HEq (L S1_).toSequenceOfBlowups (L S2_).toSequenceOfBlowups := by
  cases hS
  exact refl _

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (n) (L O) (hL : IsMaxOrderReduction (fun d => d < n) L O) (j) (hbc : SmoothPullbackCompatibility) (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty) (Y : Sch) (q) (h : Y ⟶ T.scheme) [Smooth h] [Surjective h] (hq : h ≫ T.structMap = q) (E' : Bdy Y) (hBE : SameNontrivialBoundary (T.pbA q h).boundary E') (htake : take (j + 1) E' = take (j + 1) (T.pbA q h).boundary) (hV' : (T.pbB q h E').IsAdmissible) (hdim' : (T.pbB q h E').krullDimSucc ≤ n) (hO' : (T.pbB q h E').IsOrderBoundedByMult) (hDB' : (T.pbB q h E').IsBalanced hV'.locallyOfFiniteType) (hjE : j < length E') (hcs' : (orderAtLeastLocus (T.pbB q h E').ideal T.mult).Nonempty)
include hfacts hL hbc hdim hO hbal hcs hq hBE hdim' hO' hDB' hcs'
theorem isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top
    (hZ : containedComponentsIdeal T j hj = ⊤)
    (hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = ⊤) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h (E'.lget j hjE)
        (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
      (L (restrictToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
      (L (restrictToDivisor T j hj)).toSequenceOfBlowups := by
  let _c0 := E'.lget j hjE
  let _c1 := tWB (T.pbA q h) E'
  let _c2 := bget' hj
  let _c3 := restrictToDivisor T j hj
  have hD : E'.lget j hjE = cmI _c2 h :=
    get_eq_comap_get_boundary T j hj Y q h E' hjE htake
  let _a0 := divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h _c0 hD
  have hpb : IsPullback
      _a0
      _c0.si _c2.si h :=
    isPullback_divisorPullbackMap hbc T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
      _c0 hD
  have hsm : Smooth
      _a0 :=
    hbc.smooth_of_isPullback T.scheme Y _c2.subscheme
      _c0.subscheme _c2.si
      _c0.si h
      _a0
      hpb.flip inferInstance
  have hsj : Surjective
      _a0 :=
    surjective_snd_of_isPullback_of_surjective _c2.si _c0.si h
      _a0
      hpb.flip
  have hq0_ : _a0 ≫ tMp _c3
      = siI _c0 ≫ q := by
    have key : subschemeMapOfComap h _c2 _c0 hD ≫
        (siI _c2 ≫ tMp T)
          = siI _c0 ≫ q := by
      rw [← assoc, subschemeMapOfComap_comp, assoc, hq]
    exact key
  have hideal : cmI (tId _c3)
        _a0
      = cmI (lowerIdealWithoutBlowup _c1)
          _c0.si := by
    rw [lowerIdealWithoutBlowup_withBoundary T Y q h E']
    exact comap_subschemeMapOfComap h _c2 _c0 hD $ lowerIdealWithoutBlowup T
  let _a1 := tBd (restrictToDivisor _c1 j hjE)
  have hTriple : tWB (_c3.pullbackAlong _c0.subscheme
        (siI _c0 ≫ q)
        _a0)
        _a1
      = restrictToDivisor _c1 j hjE :=
    congrArg
      (fun J => T.withSchemeIdealBoundary _c0.subscheme (siI _c0 ≫ q) J
        _a1) hideal
  have hBE0 : SameNontrivialBoundary
      ((_c3.pullbackAlong _c0.subscheme
          (siI _c0 ≫ q)
          _a0).boundary)
      _a1 := by
    rw [pullbackAlong_boundary]
    exact (sameNontrivialBoundary_comap_subschemeio h _c2 _c0 hD
      (take (bLen T - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))
      (take (lenL E' - 1)
        ((lowerBoundaryWithoutBlowup _c1).eraseIdx j))
      (sameNontrivialBoundary_lowerBoundaryWithoutBlowup T j hj Y q h E' hBE htake hjE)).symm
  have hValid0 : (tWB (_c3.pullbackAlong _c0.subscheme
        (siI _c0 ≫ q)
        _a0)
        _a1).IsAdmissible := by
    rw [hTriple]
    exact hfacts.valid_lowerTop _c1 hV' hO' hDB' j hjE hZ'
  have hdim0 : (tWB (_c3.pullbackAlong _c0.subscheme
        (siI _c0 ≫ q)
        _a0)
        _a1).krullDimSucc < n := by
    rw [hTriple]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt _c1 hV' hcs' j hjE
        (lowerIdealWithoutBlowup _c1)
        (lowerBoundaryWithoutBlowup _c1)) hdim'
  have hmain := hL.smooth_pullback_strict _c3
    (hfacts.valid_lowerTop T hV hO hbal j hj hZ)
    (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T))
      hdim)
    _c0.subscheme (siI _c0 ≫ q)
    _a0
    hq0_ _a1 hBE0 hValid0 hdim0
  let hB := heq_toSequenceOfBlowups_of_eq__b1 L hTriple
  rwa [← eq_of_heq hB]

theorem isStrictPullbackBlowupSeq_restrictTwistedToDivisor
    (hZ : containedComponentsIdeal T j hj ≠ ⊤)
    (hZ' : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
      (containedComponentsIdeal T j hj).comap h) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h (E'.lget j hjE)
        (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
      (L (restrictTwistedToDivisor ((T.pullbackAlong Y q h).withBoundary E') j hjE)).toSequenceOfBlowups
      (L (restrictTwistedToDivisor T j hj)).toSequenceOfBlowups := by
  let _c0 := E'.lget j hjE
  let _c1 := tWB (T.pbA q h) E'
  let _c2 := lowerIdealAfterBlowup T j hj
  let _c3 := lowerBoundaryAfterBlowup T j hj
  let _c4 := bget' hj
  let _c5 := restrictTwistedToDivisor T j hj
  have hD : E'.lget j hjE = cmI _c4 h :=
    get_eq_comap_get_boundary T j hj Y q h E' hjE htake
  have hZ'ne : containedComponentsIdeal _c1 j hjE ≠ ⊤ := by
    rw [hZ']
    exact comap_ne_top_of_surjective hbc h (containedComponentsIdeal T j hj) hZ
  let _a0 := divisorPullbackMap T j hj _c2 _c3 Y h _c0 hD
  have hpb : IsPullback
      _a0
      _c0.si _c4.si h :=
    isPullback_divisorPullbackMap hbc T j hj _c2 _c3 Y h
      _c0 hD
  have hsm : Smooth
      _a0 :=
    hbc.smooth_of_isPullback T.scheme Y _c4.subscheme
      _c0.subscheme _c4.si
      _c0.si h
      _a0
      hpb.flip inferInstance
  have hsj : Surjective
      _a0 :=
    surjective_snd_of_isPullback_of_surjective _c4.si _c0.si h
      _a0
      hpb.flip
  have hq0_ : _a0 ≫ tMp _c5
      = siI _c0 ≫ q := by
    have key : subschemeMapOfComap h _c4 _c0 hD ≫
        (siI _c4 ≫ tMp T)
          = siI _c0 ≫ q := by
      rw [← assoc, subschemeMapOfComap_comp, assoc, hq]
    exact key
  have hideal : cmI (tId _c5)
        _a0
      = cmI (lowerIdealAfterBlowup _c1 j hjE)
          _c0.si := by
    rw [hbc.lowerIdealPre_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ']
    exact comap_subschemeMapOfComap h _c4 _c0 hD _c2
  have hTriple : tWB (_c5.pullbackAlong _c0.subscheme
        (siI _c0 ≫ q)
        _a0)
        (tBd (restrictTwistedToDivisor _c1 j hjE))
      = restrictTwistedToDivisor _c1 j hjE :=
    congrArg
      (fun J => T.withSchemeIdealBoundary _c0.subscheme (siI _c0 ≫ q) J
        ((restrictTwistedToDivisor _c1 j hjE).boundary)) hideal
  have hBE0 : SameNontrivialBoundary
      ((_c5.pullbackAlong _c0.subscheme
          (siI _c0 ≫ q)
          _a0).boundary)
      ((restrictTwistedToDivisor _c1 j hjE).boundary) := by
    rw [pullbackAlong_boundary]
    exact (sameNontrivialBoundary_comap_subschemeio h _c4 _c0 hD
      (take (bLen T - 1) (_c3.eraseIdx j))
      (take (lenL E' - 1)
        ((lowerBoundaryAfterBlowup _c1 j hjE).eraseIdx j))
      (hbc.boundaryEquiv_restrictedBoundary_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZ')).symm
  have hValid0 : (tWB (_c5.pullbackAlong _c0.subscheme
        (siI _c0 ≫ q)
        _a0)
        (tBd (restrictTwistedToDivisor _c1 j hjE))).IsAdmissible := by
    rw [hTriple]
    exact hfacts.valid_lowerPre _c1 hV' hO' hDB' j hjE hZ'ne
  have hdim0 : (tWB (_c5.pullbackAlong _c0.subscheme
        (siI _c0 ≫ q)
        _a0)
        (tBd (restrictTwistedToDivisor _c1 j hjE))).krullDimSucc < n := by
    rw [hTriple]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt _c1 hV' hcs' j hjE
        (lowerIdealAfterBlowup _c1 j hjE)
        (lowerBoundaryAfterBlowup _c1 j hjE)) hdim'
  have hmain := hL.smooth_pullback_strict _c5
    (hfacts.valid_lowerPre T hV hO hbal j hj hZ)
    (lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt T hV hcs j hj _c2 _c3)
      hdim)
    _c0.subscheme (siI _c0 ≫ q)
    _a0
    hq0_ (tBd (restrictTwistedToDivisor _c1 j hjE)) hBE0 hValid0 hdim0
  let hB := heq_toSequenceOfBlowups_of_eq__b1 L hTriple
  rwa [← eq_of_heq hB]
end

end DivisorReduction




namespace DivisorReduction

theorem smooth_of_isPullback (X Y S S' : Sch) (σ : S ⟶ X) (σ' : S' ⟶ Y) (ph_ : Y ⟶ X)
    (ps_ : S' ⟶ S) (hpb : IsPullback σ' ps_ ph_ σ) (hph : Smooth ph_) :
    Smooth ps_ :=
  m122
    (P := @Smooth) hpb hph

theorem orderAtLeastLocus_comap_of_smooth (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) Y
    q (h : Y ⟶ T.scheme) [Smooth h]
    (_hq : h ≫ T.structMap = q) m :
    orderAtLeastLocus (T.ideal.comap h) m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m := by
  have := hV.charZero
  have := hV.smooth
  exact orderAtLeastLocus_comap T.base T.structMap h T.ideal m

theorem withBoundary_withBoundary (T : MarkedIdealWithBoundary)
    (E F : List T.scheme.IdealSheafData) :
    (T.withBoundary E).withBoundary F = T.withBoundary F := rfl

private theorem isAdmissible_of_withBoundary_isAdmissible (S : MarkedIdealWithBoundary)
    (E : List S.scheme.IdealSheafData) (hBE : SameNontrivialBoundary S.boundary E)
    (hV : (S.withBoundary E).IsAdmissible) : S.IsAdmissible := by
  have h1 :=
    validOfSameNontrivialBoundary _ _ hV hBE.symm
  rwa [withBoundary_withBoundary, withBoundary_self] at h1

theorem isAdmissible_pullbackAlong_of_withBoundary_isAdmissible :
    ∀ (T : MarkedIdealWithBoundary) (Y : Sch) (q : Y ⟶ Sp T.base)
      (h : Y ⟶ T.scheme) (E' : Bdy Y),
      SameNontrivialBoundary (T.pbA q h).boundary E' →
        (T.pbB q h E').IsAdmissible → (T.pbA q h).IsAdmissible := by
  intro T Y q h E' hBE hV
  exact isAdmissible_of_withBoundary_isAdmissible (pbAT T q h) E' hBE hV

section
variable {hres : StrictTransformIsBlowupOfClosedSubscheme} {hno : BlowupPreservesNoetherian} (hfacts : DivisorReductionTerminationProperties hres hno)
include hfacts
theorem containedComponentsIdeal_pullbackAlong_of_smooth :
    ∀ T, T.IsAdmissible →
      ∀ Y q h
        [Smooth h], h ≫ T.structMap = q →
        ∀ E',
          SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ j hj hjE,
            take (j + 1) E' = take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
              containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (containedComponentsIdeal T j hj).comap h :=
  by
    intro T hV Y q h hsm hq E' hBE j hj hjE htake hV'
    have hj' : j < (T.pbA q h).boundary.length := by
      rw [pullbackAlong_boundary]
      erw [length_map]
      exact hj
    have _i13 : containedComponentsIdeal (T.pbB q h E') j hjE = containedComponentsIdeal (T.pbA q h) j hj' := by
      let _a0 := T.pullbackAlong Y q h
      exact tr_ (containedComponentsIdeal_eq_componentsInOrderLocusIdeal (tWB _a0 E') j hjE) $
        (componentsInOrderLocusIdeal_congr _ _ $ get_eq_get_of_take_succ_eq E' (tBd _a0) j htake hjE hj').trans
          (containedComponentsIdeal_eq_componentsInOrderLocusIdeal _a0 j hj').symm
    rw [_i13]
    exact hfacts.preIdeal_pullbackAlong T hV Y q h hq (isAdmissible_pullbackAlong_of_withBoundary_isAdmissible T Y q h E' hBE hV') j hj hj'
end

end DivisorReduction




namespace DivisorReduction

theorem isPullback_subschemeMapOfComap (X Y : Sch) (h : Y ⟶ X) (D : ISD X)
    (D' : ISD Y) (hD : D' = D.comap h) :
    IsPullback (subschemeMapOfComap h D D' hD) D'.si D.si h := by
  have hcomm :=
    subschemeMapOfComap_comp h D D' hD
  obtain ⟨ps_, hps_⟩ : ∃ ps_, ps_ ≫ siI D' = fst h D.si := by
    have hle : D'.subschemeι.ker ≤ m149 (fst h D.si) := by
      rw [q2, hD]
      exact le_rfl
    exact ⟨m64 D'.si
        (fst h D.si) hle, by simp⟩
  let _a0 := subschemeMapOfComap h D D' hD
  have h1 : lift D'.si _a0 hcomm.symm ≫ ps_ = 𝟙 _ := by
    rw [← cancel_mono D'.si, assoc, hps_, id_comp]
    exact lift_fst _ _ _
  have h2 : ps_ ≫ lift D'.si _a0 hcomm.symm = 𝟙 _ := by
    apply hom_ext
    rwa [assoc, lift_fst, id_comp]
    rw [assoc, lift_snd, id_comp,
      ← cancel_mono D.si, assoc, hcomm, ← assoc, hps_]
    exact condition
  exact (IsPullback.of_iso_pullback ⟨sy_ hcomm⟩
    { hom := lift D'.si _a0 hcomm.symm
      inv := ps_
      hom_inv_id := h1
      inv_hom_id := h2 } (lift_fst _ _ _) $ lift_snd _ _ _).flip

end DivisorReduction





theorem isStrictPullbackBlowupSeq_ofSequenceOfBlowups {X X'} ph_ (B' : SequenceOfBlowups X')
    (B : SequenceOfBlowups X) (h : IsStrictPullbackBlowupSeq ph_ B' B) :
    IsStrictPullbackBlowupSeq ph_ (ofSequenceOfBlowups B').toSequenceOfBlowups (ofSequenceOfBlowups B).toSequenceOfBlowups := by
  obtain ⟨hlen, σ, h0, hpb, hc⟩ := h
  have hlA : (ofSequenceOfBlowups B').toSequenceOfBlowups.length = B'.length := by simp_all
  have hlB : (ofSequenceOfBlowups B).toSequenceOfBlowups.length = B.length := by simp_all
  refine ⟨by rw [hlA, hlB, hlen], fun i hi => σ i $ hi.trans_eq hlA, ?_, ?_, ?_⟩
  simp [toSequenceOfBlowups_isoObjZero, ofSequenceOfBlowups_isoObjZero]
  exact h0
  intro i hi
  simp [toSequenceOfBlowups_blowupMorphism, ofSequenceOfBlowups_blowupMorphism]
  exact hpb i $ hi.trans_eq hlA
  intro i hi
  simp [ofSequenceOfBlowups_center]
  exact hc i $ hi.trans_eq hlA

theorem IsStrictPullbackBlowupSeq.ofMarkedSequence {A B : MarkedIdealWithBoundary} (ph_ : A.scheme ⟶ B.scheme)
    (sA : A.SequenceOfBlowups) (sB : B.SequenceOfBlowups)
    (h : IsStrictPullbackBlowupSeq ph_ sA.toSequenceOfBlowups sB.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq ph_ sA.toBsd.toSequenceOfBlowups
      sB.toBsd.toSequenceOfBlowups := by
  exact isStrictPullbackBlowupSeq_ofSequenceOfBlowups ph_ sA.toSequenceOfBlowups sB.toSequenceOfBlowups h

theorem BlowupSequenceData.prepend_toSequenceOfBlowups_congr {X : Sch} {Z Z'} (hZZ : Z = Z')
    (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : IsBlowupAlongIdealSheaf (𝟙 X) Z') d :
    toSequenceOfBlowups (prepend Z hZ d) = toSequenceOfBlowups (prepend Z' hZ' d) := by
  subst hZZ
  rfl

structure FlatOfSmooth : Prop where
  flat_of_smooth : ∀ (X Y : Sch) (f : Y ⟶ X), Smooth f →
    Flat f

namespace DivisorReduction

def DivisorReductionSeqEqAmbient (hres : StrictTransformIsBlowupOfClosedSubscheme) (L : PrincipalizationAssignment) (j : ℕ)
    (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hj : j < T.boundary.length) : Prop :=
  letI : IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  (ccI hj = ⊤ ∧
      ∃ (hpr : (MarkedBlowupSequenceData.ofMarkedSequence $ L $ rD hj).CentersContainNoComponent)
        (hmk : (ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealWithoutBlowup T)
            (lowerBoundaryWithoutBlowup T) (L $ rD hj) hpr).IsMarked
            T.structMap T.ideal T.mult T.boundary),
        divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
          ((ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lowerIdealWithoutBlowup T)
              (lowerBoundaryWithoutBlowup T) (L $ rD hj) hpr).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups) ∨
    (ccI hj ≠ ⊤ ∧
      ∃ (hb : IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ ccI hj)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence $ L $ rTD hj).CentersContainNoComponent)
        (hmk : (prepend (ccI hj) hb
            (ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lI hj)
              (lB hj) (L $ rTD hj) hpr)).IsMarked
            T.structMap T.ideal T.mult T.boundary),
        divisorReductionSeq hres blowupPreservesNoetherian T (fun S _ => L S) j =
          ((prepend (ccI hj) hb
              (ambientBlowupSeq hres blowupPreservesNoetherian T j hj (lI hj)
                (lB hj) (L $ rTD hj) hpr)).toMarkedBlowupSequenceData
              T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups)

end DivisorReduction





theorem map_comap_id (X : Sch) (E : Bdy X) :
    E.map (fun D => D.comap $ 𝟙 X) = E :=by simp_all
section
variable {X : Sch}
theorem get_eq_comap_id (E1_ E2_ : Bdy X) (j1 j2_ : ℕ)
    (hj1_ : j1 < length E1_) (hj2_ : j2_ < length E2_)
    (heq : E1_.lget j1 hj1_ = E2_.lget j2_ hj2_) :
    E2_.lget j2_ hj2_ = (E1_.lget j1 hj1_).comap (𝟙 X) :=by simp_all
theorem eq_comap_id_of_eq {A B : ISD X} (h : A = B) :
    A = B.comap (𝟙 X) := by
  rwa [comap_id]

theorem sameNontrivialBoundary_map_comap_id {A B : Bdy X}
    (h : SameNontrivialBoundary A B) :
    SameNontrivialBoundary A $ B.map fun D => D.comap $ 𝟙 X := by
  rwa [map_comap_id]

section
variable (E1_ : Bdy X) (D : ISD X) (E2_ : Bdy X)
theorem get_append_cons_length
    (h : length E1_ < length (E1_ ++ D :: E2_)) :
    (E1_ ++ D :: E2_).get ⟨length E1_, h⟩ = D := by
  induction E1_ with
  | nil => rfl
  | cons a l ih => exact ih _

theorem eraseIdx_append_cons_length :
    (E1_ ++ D :: E2_).eraseIdx E1_.length = E1_ ++ E2_ := by
  induction E1_ with
  | nil => rfl
  | cons a l ih => simp [ih]
end

theorem isomorphic_of_isStrictPullbackAlongId (A B : SequenceOfBlowups X)
    (h : IsStrictPullbackBlowupSeq (𝟙 X) A B) : A.Isomorphic B := by
  unfold IsStrictPullbackBlowupSeq at h
  obtain ⟨hlen, σ, h0, hpb, hc⟩ := h
  have hiso : ∀ i (hi : i ≤ A.length), IsIso $ σ i hi := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hh : σ 0 hi = sbIzH A ≫ sbIzI B := by
          rw [Iso.eq_comp_inv]
          simpa using h0
        rw [hh]
        infer_instance
    | succ k ih =>
        intro hi
        have hk := hi
        exact (hpb k hk).isIso_fst_of_isIso $ ih $ le_of_lt hk
  unfold Isomorphic
  exact ⟨hlen, fun i hi => @asIso Sch _ _ _ (σ i hi) $ hiso i hi, by simpa using h0,
    fun i hi => (hpb i hi).w, fun i hi => sy_ $ hc i hi⟩
end

namespace DivisorReduction

theorem containedComponentsIdeal_withBoundary_congr (T : MarkedIdealWithBoundary)
    (L1_ L2_ : List T.scheme.IdealSheafData) j1 (hj1_ : j1 < length L1_) j2_
    (hj2_ : j2_ < length L2_) (heq : L1_.lget j1 hj1_ = L2_.lget j2_ hj2_) :
    containedComponentsIdeal (T.withBoundary L1_) j1 hj1_ = containedComponentsIdeal (T.withBoundary L2_) j2_ hj2_ := by
  exact tr_ (containedComponentsIdeal_eq_componentsInOrderLocusIdeal (tWB T L1_) j1 hj1_) $
    (congrArg (componentsInOrderLocusIdeal T.ideal T.mult) heq).trans
      (containedComponentsIdeal_eq_componentsInOrderLocusIdeal (tWB T L2_) j2_ hj2_).symm

structure BoundaryReindexingInvariance : Prop where
  smooth_id : ∀ X : Sch, Smooth $ 𝟙 X
  surjective_id : ∀ X : Sch, Surjective $ 𝟙 X
  lowerIdealPre_shift :
    ∀ (T : MarkedIdealWithBoundary) (L1_ L2_ : List T.scheme.IdealSheafData) (j1 : ℕ)
      (hj1_ : j1 < length L1_) (j2_ : ℕ) (hj2_ : j2_ < length L2_),
      L1_.lget j1 hj1_ = L2_.lget j2_ hj2_ →
      lowerIdealAfterBlowup (T.withBoundary L2_) j2_ hj2_ = lowerIdealAfterBlowup (T.withBoundary L1_) j1 hj1_
  boundaryEquiv_restrictedBoundary_reindex :
    ∀ (T : MarkedIdealWithBoundary) (L1_ L2_ : List T.scheme.IdealSheafData) (j1 : ℕ)
      (hj1_ : j1 < length L1_) (j2_ : ℕ) (hj2_ : j2_ < length L2_),
      L1_.lget j1 hj1_ = L2_.lget j2_ hj2_ →
      SameNontrivialBoundary (L2_.eraseIdx j2_) (L1_.eraseIdx j1) →
      SameNontrivialBoundary
        (take (length L2_ - 1) $ (lowerBoundaryAfterBlowup (T.withBoundary L2_) j2_ hj2_).eraseIdx j2_)
        (take (length L1_ - 1) $ (lowerBoundaryAfterBlowup (T.withBoundary L1_) j1 hj1_).eraseIdx j1)

theorem isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_smooth (n : ℕ) (L O : PrincipalizationAssignment)
    (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (S : MarkedIdealWithBoundary) (j : ℕ) (hj : j < S.boundary.length)
    (I0 : S.scheme.IdealSheafData) (E0 : List S.scheme.IdealSheafData)
    (D' : S.scheme.IdealSheafData)
    (ps_ : subscheme D' ⟶ (restrictToBoundaryDivisor S j hj I0 E0).scheme)
    [Smooth ps_] [Surjective ps_]
    (hq : ps_ ≫ (restrictToBoundaryDivisor S j hj I0 E0).structMap = subschemeι D' ≫ S.structMap)
    (I0' : S.scheme.IdealSheafData) (F : List S.scheme.IdealSheafData)
    (hid : (I0.comap (S.bget j hj).si).comap ps_ = I0'.comap D'.si)
    (hBE : SameNontrivialBoundary
      (map (fun Dd => Dd.comap ps_)
        (map (fun Dd => Dd.comap (S.bget j hj).si)
          (take (S.boundary.length - 1) $ E0.eraseIdx j)))
      (map (fun Dd => Dd.comap D'.si) F))
    (hV1_ : (restrictToBoundaryDivisor S j hj I0 E0).IsAdmissible)
    (hd1_ : (restrictToBoundaryDivisor S j hj I0 E0).krullDimSucc < n)
    (hV2_ : (S.withSchemeIdealBoundary D'.subscheme (subschemeι D' ≫ S.structMap) (I0'.comap D'.si)
      (map (fun Dd => Dd.comap D'.si) F)).IsAdmissible)
    (hd2_ : (S.withSchemeIdealBoundary D'.subscheme (subschemeι D' ≫ S.structMap) (I0'.comap D'.si)
      (map (fun Dd => Dd.comap D'.si) F)).krullDimSucc < n) :
    IsStrictPullbackBlowupSeq ps_
      (L $ S.withSchemeIdealBoundary D'.subscheme (subschemeι D' ≫ S.structMap) (I0'.comap D'.si)
        (map (fun Dd => Dd.comap D'.si) F)).toSequenceOfBlowups
      (L $ restrictToBoundaryDivisor S j hj I0 E0).toSequenceOfBlowups := by
  let _c0 := (restrictToBoundaryDivisor S j hj I0 E0).pullbackAlong D'.subscheme (siI D' ≫ tMp S) ps_
  rw [← hid] at hV2_ hd2_ ⊢
  have hBE' : SameNontrivialBoundary
      _c0.boundary
      (map (·.comap D'.si) F) := hBE
  have hVp : tAd (tWB _c0
      (map (·.comap D'.si) F)) := hV2_
  have hdp : tDim (tWB _c0
      (map (·.comap D'.si) F)) < n := hd2_
  exact hL.smooth_pullback_strict (restrictToBoundaryDivisor S j hj I0 E0) hV1_ hd1_ D'.subscheme
    (siI D' ≫ tMp S) ps_ hq (map (·.comap D'.si) F)
    hBE' hVp hdp

theorem isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_get_eq
    (hbc : SmoothPullbackCompatibility) (hsh : BoundaryReindexingInvariance)
    (n : ℕ) (L O : PrincipalizationAssignment) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (T : MarkedIdealWithBoundary) (L1_ L2_ : List T.scheme.IdealSheafData)
    (j1 : ℕ) (hj1_ : j1 < length L1_) (j2_ : ℕ) (hj2_ : j2_ < length L2_)
    (heq : L1_.lget j1 hj1_ = L2_.lget j2_ hj2_)
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData)
    (I0' : T.scheme.IdealSheafData) (E0' : List T.scheme.IdealSheafData)
    (hI : I0' = I0.comap (𝟙 T.scheme))
    (hE : SameNontrivialBoundary
      (take (length L2_ - 1) $ E0'.eraseIdx j2_)
      (map (fun D => D.comap $ 𝟙 T.scheme)
        (take (length L1_ - 1) $ E0.eraseIdx j1)))
    (hV1_ : (restrictToBoundaryDivisor (T.withBoundary L1_) j1 hj1_ I0 E0).IsAdmissible)
    (hd1_ : (restrictToBoundaryDivisor (T.withBoundary L1_) j1 hj1_ I0 E0).krullDimSucc < n)
    (hV2_ : (restrictToBoundaryDivisor (T.withBoundary L2_) j2_ hj2_ I0' E0').IsAdmissible)
    (hd2_ : (restrictToBoundaryDivisor (T.withBoundary L2_) j2_ hj2_ I0' E0').krullDimSucc < n) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap (T.withBoundary L1_) j1 hj1_ I0 E0 T.scheme (𝟙 T.scheme)
        (L2_.lget j2_ hj2_) $ get_eq_comap_id L1_ L2_ j1 j2_ hj1_ hj2_ heq)
      (L $ restrictToBoundaryDivisor (T.withBoundary L2_) j2_ hj2_ I0' E0').toSequenceOfBlowups
      (L $ restrictToBoundaryDivisor (T.withBoundary L1_) j1 hj1_ I0 E0).toSequenceOfBlowups := by
  let _a1 := take (lenL L2_ - 1) $ E0'.eraseIdx j2_
  let _c0 := L2_.lget j2_ hj2_
  let _c1 := (tWB T L1_).boundary.lget j1 hj1_
  have hD :=
    get_eq_comap_id L1_ L2_ j1 j2_ hj1_ hj2_ heq
  have hsq := isPullback_divisorPullbackMap hbc (tWB T L1_) j1 hj1_ I0 E0 T.scheme
    (𝟙 tSch T) _c0 hD
  let _a0 := divisorPullbackMap (tWB T L1_) j1 hj1_ I0 E0 T.scheme (𝟙 tSch T) _c0 hD
  refine @isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_smooth n L O hL (tWB T L1_) j1 hj1_ I0 E0
    _c0
    _a0 (hbc.smooth_of_isPullback T.scheme T.scheme _c1.subscheme _c0.subscheme _c1.si _c0.si (𝟙 tSch T) _a0 hsq.flip $ hsh.smooth_id T.scheme) (@surjective_snd_of_isPullback_of_surjective T.scheme T.scheme _c1.subscheme _c0.subscheme _c1.si _c0.si (𝟙 tSch T) _a0 (hsh.surjective_id T.scheme) hsq.flip) ((assoc _ _ _).symm.trans $ congrArg (fun f => f ≫ tMp (tWB T L1_)) $ hsq.w.trans $ comp_id _) I0'
    _a1 ?_ (sy_ $ sameNontrivialBoundary_comap_subschemeio (𝟙 tSch T) _c1 _c0 hD (take (lenL L1_ - 1) $ E0.eraseIdx j1) _a1 hE) hV1_ hd1_ hV2_ hd2_
  rw [hI]
  exact comap_subschemeMapOfComap (𝟙 tSch T) _c1
    _c0 hD I0

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (n) (L O) (hL : IsMaxOrderReduction (fun d => d < n) L O) (hbc : SmoothPullbackCompatibility) (hsh : BoundaryReindexingInvariance) (T : MarkedIdealWithBoundary) (L1_ L2_ : List T.scheme.IdealSheafData) (j1) (hj1_ : j1 < length L1_) (j2_) (hj2_ : j2_ < length L2_) (heq : L1_.lget j1 hj1_ = L2_.lget j2_ hj2_) (hBE : SameNontrivialBoundary (L2_.eraseIdx j2_) $ L1_.eraseIdx j1) (hV1_ : (T.withBoundary L1_).IsAdmissible) (hdim1_ : (T.withBoundary L1_).krullDimSucc ≤ n) (hO1_ : (T.withBoundary L1_).IsOrderBoundedByMult) (hDB1 : (T.withBoundary L1_).IsBalanced hV1_.locallyOfFiniteType) (hcs1_ : (orderAtLeastLocus (T.withBoundary L1_).ideal (T.withBoundary L1_).mult).Nonempty) (hV2_ : (T.withBoundary L2_).IsAdmissible) (hdim2_ : (T.withBoundary L2_).krullDimSucc ≤ n) (hO2_ : (T.withBoundary L2_).IsOrderBoundedByMult) (hDB2 : (T.withBoundary L2_).IsBalanced hV2_.locallyOfFiniteType) (hcs2_ : (orderAtLeastLocus (T.withBoundary L2_).ideal (T.withBoundary L2_).mult).Nonempty)
include hfacts hL hbc hsh hBE hdim1_ hO1_ hDB1 hcs1_ hdim2_ hO2_ hDB2 hcs2_
theorem isStrictPullbackBlowupSeq_restrictToDivisor_of_get_eq_of_eq_top
    (hZ : containedComponentsIdeal (T.withBoundary L1_) j1 hj1_ = ⊤) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap (T.withBoundary L1_) j1 hj1_ (lowerIdealWithoutBlowup (T.withBoundary L1_))
        (lowerBoundaryWithoutBlowup (T.withBoundary L1_)) T.scheme (𝟙 T.scheme) (L2_.lget j2_ hj2_)
        (get_eq_comap_id L1_ L2_ j1 j2_ hj1_ hj2_ heq))
      (L (restrictToDivisor (T.withBoundary L2_) j2_ hj2_)).toSequenceOfBlowups
      (L (restrictToDivisor (T.withBoundary L1_) j1 hj1_)).toSequenceOfBlowups := by
  have hZ2_ : containedComponentsIdeal (tWB T L2_) j2_ hj2_ = ⊤ := by
    rwa [← containedComponentsIdeal_withBoundary_congr T L1_ L2_ j1 hj1_ j2_ hj2_ heq]
  have hlen1_ : lenL (L1_.eraseIdx j1) = lenL L1_ - 1 := by
    simp [length_eraseIdx, hj1_]
  have hlen2_ : lenL (L2_.eraseIdx j2_) = lenL L2_ - 1 := by
    simp [length_eraseIdx, hj2_]
  have ht1_ : take (lenL L1_ - 1) (L1_.eraseIdx j1) = L1_.eraseIdx j1 := by
    rw [← hlen1_]
    simp
  have ht2_ : take (lenL L2_ - 1) (L2_.eraseIdx j2_) = L2_.eraseIdx j2_ := by simp_all
  have hI : lowerIdealWithoutBlowup (tWB T L2_)
      = cmI (lowerIdealWithoutBlowup (tWB T L1_)) (𝟙 tSch T) :=
    (comap_id _).symm
  have hE : SameNontrivialBoundary
      (take (lenL L2_ - 1) ((lowerBoundaryWithoutBlowup (tWB T L2_)).eraseIdx j2_))
      (map (cmI · $ 𝟙 tSch T)
        (take (lenL L1_ - 1) ((lowerBoundaryWithoutBlowup (tWB T L1_)).eraseIdx j1))) := by
    rw [lowerBoundaryWithoutBlowup_eq (tWB T L2_), lowerBoundaryWithoutBlowup_eq (tWB T L1_)]
    show SameNontrivialBoundary (take (lenL L2_ - 1) (L2_.eraseIdx j2_))
        (map (cmI · $ 𝟙 T.scheme) (take (lenL L1_ - 1) (L1_.eraseIdx j1)))
    rwa [ht1_, ht2_, map_comap_id]
  exact isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_get_eq hbc hsh n L O hL T L1_ L2_ j1 hj1_ j2_ hj2_ heq
    (lowerIdealWithoutBlowup (tWB T L1_)) (lowerBoundaryWithoutBlowup (tWB T L1_))
    (lowerIdealWithoutBlowup (tWB T L2_)) (lowerBoundaryWithoutBlowup (tWB T L2_))
    hI hE (hfacts.valid_lowerTop (tWB T L1_) hV1_ hO1_ hDB1 j1 hj1_ hZ) (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (tWB T L1_) hV1_ hcs1_ j1 hj1_ (lowerIdealWithoutBlowup (tWB T L1_)) (lowerBoundaryWithoutBlowup (tWB T L1_))) hdim1_) (hfacts.valid_lowerTop (tWB T L2_) hV2_ hO2_ hDB2 j2_ hj2_ hZ2_) (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (tWB T L2_) hV2_ hcs2_ j2_ hj2_ (lowerIdealWithoutBlowup (tWB T L2_)) (lowerBoundaryWithoutBlowup (tWB T L2_))) hdim2_)

theorem isStrictPullbackBlowupSeq_restrictTwistedToDivisor_of_get_eq
    (hZ : containedComponentsIdeal (T.withBoundary L1_) j1 hj1_ ≠ ⊤) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap (T.withBoundary L1_) j1 hj1_ (lowerIdealAfterBlowup (T.withBoundary L1_) j1 hj1_)
        (lowerBoundaryAfterBlowup (T.withBoundary L1_) j1 hj1_) T.scheme (𝟙 T.scheme) (L2_.lget j2_ hj2_)
        (get_eq_comap_id L1_ L2_ j1 j2_ hj1_ hj2_ heq))
      (L (restrictTwistedToDivisor (T.withBoundary L2_) j2_ hj2_)).toSequenceOfBlowups
      (L (restrictTwistedToDivisor (T.withBoundary L1_) j1 hj1_)).toSequenceOfBlowups := by
  have hZ2_ : containedComponentsIdeal (tWB T L2_) j2_ hj2_ ≠ ⊤ := by
    rwa [← containedComponentsIdeal_withBoundary_congr T L1_ L2_ j1 hj1_ j2_ hj2_ heq]
  let _a0 := lowerIdealAfterBlowup (tWB T L1_) j1 hj1_
  let _a1 := lowerBoundaryAfterBlowup (tWB T L1_) j1 hj1_
  let _a2 := lowerIdealAfterBlowup (tWB T L2_) j2_ hj2_
  let _a3 := lowerBoundaryAfterBlowup (tWB T L2_) j2_ hj2_
  exact isStrictPullbackBlowupSeq_restrictToBoundaryDivisor_of_get_eq hbc hsh n L O hL T L1_ L2_ j1 hj1_ j2_ hj2_ heq
    _a0 _a1
    _a2 _a3
    (eq_comap_id_of_eq $ hsh.lowerIdealPre_shift T L1_ L2_ j1 hj1_ j2_ hj2_ heq) (sameNontrivialBoundary_map_comap_id $ hsh.boundaryEquiv_restrictedBoundary_reindex T L1_ L2_ j1 hj1_ j2_ hj2_ heq hBE) (hfacts.valid_lowerPre (tWB T L1_) hV1_ hO1_ hDB1 j1 hj1_ hZ) (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (tWB T L1_) hV1_ hcs1_ j1 hj1_ _a0 _a1) hdim1_) (hfacts.valid_lowerPre (tWB T L2_) hV2_ hO2_ hDB2 j2_ hj2_ hZ2_) $ lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (tWB T L2_) hV2_ hcs2_ j2_ hj2_ _a2 _a3) hdim2_
end

end DivisorReduction





section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) (hbc : DivisorReduction.SmoothPullbackCompatibility) (hsh : DivisorReduction.BoundaryReindexingInvariance) (n) (L O) (hL : IsMaxOrderReduction (fun d => d < n) L O) (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hj : j < T.boundary.length), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType → (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
include hfacts hbc hsh hL hshape
theorem isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq
    (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (L1_ L2_ : List T.scheme.IdealSheafData)
    j1 (hj1_ : j1 < length L1_) j2_ (hj2_ : j2_ < length L2_)
    (heq : L1_.lget j1 hj1_ = L2_.lget j2_ hj2_)
    (hBE : SameNontrivialBoundary (L2_.eraseIdx j2_) (L1_.eraseIdx j1))
    (hV1_ : (T.withBoundary L1_).IsAdmissible) (hV2_ : (T.withBoundary L2_).IsAdmissible) :
    IsStrictPullbackBlowupSeq (𝟙 T.scheme)
      (((canonicalAlgorithmRules hres).divisorFamily L j2_ (T.withBoundary L2_)).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j1 (T.withBoundary L1_)).toSequenceOfBlowups) := by
  let _a0 := L1_.lget j1 hj1_
  let _a2 := get_eq_comap_id L1_ L2_ j1 j2_ hj1_ hj2_ heq
  let _c0 := L2_.lget j2_ hj2_
  classical
  by_cases hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty
  have hN :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  have hN1_ :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV1_
  have hN2 :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV2_
  have hflat : Flat (𝟙 tSch T) := inferInstance
  have hjb1_ := hj1_
  have hjb2_ := hj2_
  have hpre :=
    DivisorReduction.containedComponentsIdeal_withBoundary_congr T L1_ L2_ j1 hj1_ j2_ hj2_ heq
  have hs1_ := hshape j1 (T.withBoundary L1_) hV1_ hjb1_ hdim hO hbal hcs
  have hs2_ := hshape j2_ (T.withBoundary L2_) hV2_ hjb2_ hdim hO hbal hcs
  simp only [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
  rcases hs1_ with ⟨hZ1_, hpr1, hmk1_, he1_⟩ | ⟨hZ1_, hb1_, hpr1, hmk1_, he1_⟩
  rcases hs2_ with ⟨hZ2_, hpr2_, hmk2_, he2_⟩ | ⟨hZ2_, hb2_, hpr2_, hmk2_, he2_⟩
  have hstep :=
    hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
      (subS _a0) (subS _c0)
      (siI _a0) (siI _c0)
      (𝟙 tSch T) _
      ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L1_) j1 hjb1_
        (p19 (T.withBoundary L1_))
        (p20 (T.withBoundary L1_)) T.scheme (𝟙 tSch T)
        _c0 _a2).flip)
      _ _ hpr1 hpr2_
      (IsStrictPullbackBlowupSeq.ofMarkedSequence
        (A := DivisorReduction.restrictToDivisor (T.withBoundary L2_) j2_ hjb2_)
        (B := DivisorReduction.restrictToDivisor (T.withBoundary L1_) j1 hjb1_) _ _ _
        (DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_get_eq_of_eq_top hres hfacts n L O hL hbc hsh
          T L1_ L2_ j1 hj1_ j2_ hj2_ heq hBE hV1_ hdim hO hbal hcs hV2_ hdim hO hbal hcs hZ1_))
  rw [he1_, he2_]
  simp only [toMarkedBlowupSequenceData_toSequenceOfBlowups]
  exact hstep
  exact absurd (st_ hpre hZ1_) hZ2_
  rcases hs2_ with ⟨hZ2_, hpr2_, hmk2_, he2_⟩ | ⟨hZ2_, hb2_, hpr2_, hmk2_, he2_⟩
  exact absurd (tr_ hpre hZ2_) hZ1_
  have hcomap : (p44 (T.withBoundary L1_) j1 hjb1_).comap
      (𝟙 (T.withBoundary L1_).scheme) =
      p44 (T.withBoundary L1_) j1 hjb1_ := by
    rw [comap_id]
  have hZZ := st_ hpre hcomap.symm
  have hb1' : p15 (𝟙 tSch (T.withBoundary L1_))
      ((p44 (T.withBoundary L1_) j1 hjb1_).comap
        (𝟙 tSch (T.withBoundary L1_))) := by simp_all
  let _a1 := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L2_) j2_ hjb2_
  let _a3 := DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L1_) j1 hjb1_
  let _a4 := DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L1_) j1 hjb1_
  let _a7 := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L1_) j1 hjb1_
  have hstep :=
    hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
      (subS _a0) (subS _c0)
      (siI _a0) (siI _c0)
      (𝟙 tSch T) _
      ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L1_) j1 hjb1_
        _a3
        _a4 T.scheme (𝟙 tSch T)
        _c0 _a2).flip)
      _ _ hpr1 hpr2_
      (IsStrictPullbackBlowupSeq.ofMarkedSequence
        (A := _a1)
        (B := _a7) _ _ _
        (DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor_of_get_eq hres hfacts n L O hL hbc hsh
          T L1_ L2_ j1 hj1_ j2_ hj2_ heq hBE hV1_ hdim hO hbal hcs hV2_ hdim hO hbal hcs hZ1_))
  let _a5 := DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L2_) j2_ hjb2_
  let _a6 := DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L2_) j2_ hjb2_
  have hfin : IsStrictPullbackBlowupSeq (𝟙 tSch T)
      (prepend (p44 (T.withBoundary L2_) j2_ hjb2_) hb2_
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L2_) j2_
          hjb2_ _a5
          _a6
          (L _a1) hpr2_)).toSequenceOfBlowups
      (prepend (p44 (T.withBoundary L1_) j1 hjb1_) hb1_
        (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L1_) j1
          hjb1_ _a3
          _a4
          (L _a7) hpr1)).toSequenceOfBlowups := by
    rw [BlowupSequenceData.prepend_toSequenceOfBlowups_congr hZZ hb2_ hb1'
      (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L2_) j2_ hjb2_
        _a5
        _a6
        (L _a1) hpr2_)]
    exact IsStrictPullbackBlowupSeq.prepend hstep _ hb1_ hb1'
  rw [he1_, he2_]
  simp only [toMarkedBlowupSequenceData_toSequenceOfBlowups]
  exact hfin
  have hcs0 := mp_ not_nonempty_iff_eq_empty hcs
  exact IsStrictPullbackBlowupSeq.of_length_zero _ _ _
    (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j2_ (T.withBoundary L2_) hV2_ hdim hO hbal
      hj2_ hcs0)
    (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j1 (T.withBoundary L1_) hV1_ hdim hO hbal
      hj1_ hcs0)

theorem isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient :
    IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j := by
  refine ⟨?_⟩
  intro T hdim hO hft hbal E1_ E2_ E1' E2' D hBE1 hBE2 hV1 hV2
  have hlen1 : lenL E1_ < lenL (E1_ ++ D :: E2_) := by simp
  have hlen2 : lenL E1' < lenL (E1' ++ D :: E2') := by simp
  have hget : (E1' ++ D :: E2').get ⟨lenL E1', hlen2⟩
      = (E1_ ++ D :: E2_).get ⟨lenL E1_, hlen1⟩ := by
    rw [get_append_cons_length, get_append_cons_length]
  have hbe : SameNontrivialBoundary ((E1_ ++ D :: E2_).eraseIdx E1_.length)
      ((E1' ++ D :: E2').eraseIdx E1'.length) := by
    rw [eraseIdx_append_cons_length, eraseIdx_append_cons_length]
    exact hBE1.append hBE2
  exact isomorphic_of_isStrictPullbackAlongId _ _
    (isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq hres hfacts hbc hsh n L O hL hshape
      (tWB T (E1' ++ D :: E2')) hV2 hdim hO hbal (E1' ++ D :: E2') (E1_ ++ D :: E2_)
      E1'.length hlen2 E1_.length hlen1 hget hbe hV2 hV1)
end





namespace DivisorReduction

structure EmptyPulledBackCenterCompatibility : Prop where
  lowerIdealPre_comap_eq_lowerIdealTop_comap :
    ∀ (T : MarkedIdealWithBoundary) (_hV : T.IsAdmissible) (_hO : T.IsOrderBoundedByMult) (j : ℕ)
      (hj : j < T.boundary.length) (Y : Sch) (h : Y ⟶ T.scheme),
      (ccI hj).comap h = ⊤ →
      (lI hj).comap h = (lowerIdealWithoutBlowup T).comap h
  boundaryEquiv_restrictedBoundary_comap_of_center_comap_eq_top :
    ∀ (T : MarkedIdealWithBoundary) (_hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
      (Y : Sch) (h : Y ⟶ T.scheme),
      (ccI hj).comap h = ⊤ →
      SameNontrivialBoundary
        (map (fun D => D.comap h)
          (take (T.boundary.length - 1) $ (lB hj).eraseIdx j))
        (map (fun D => D.comap h)
          (take (T.boundary.length - 1) $ (lowerBoundaryWithoutBlowup T).eraseIdx j))

end DivisorReduction




noncomputable abbrev fieldBaseChangeProjection (T : MarkedIdealWithBoundary) (K : Type) [Field K]
    (f : T.base →+* K) :=
  fst T.structMap $ specMapOfFieldHom T.base K f

noncomputable abbrev fBCP (T : MarkedIdealWithBoundary) {K : Type} [Field K] (f : T.base →+* K) := fieldBaseChangeProjection T K f

theorem get_eq_comap_fieldBaseChangeProjection (T : MarkedIdealWithBoundary) j (hj : j < T.boundary.length)
    (K : Type) [Field K] f
    (E' : List (T.bc f).scheme.IdealSheafData) (hjE : j < length E')
    (htake : take (j + 1) E' = take (j + 1) (T.bc f).boundary) :
    E'.lget j hjE = (T.bget j hj).comap (fieldBaseChangeProjection T K f) := by
  have hj' : j < (T.bc f).boundary.length := by
    have h := congrArg length htake
    simp [length_take] at h
    omega
  let _a0 := fieldBaseChangeProjection T K f
  have key : ∀ (hh :
      j < length (map (·.comap _a0) T.boundary)),
      (map (·.comap _a0) T.boundary)[j]'hh
        = cmI (T.boundary[j]'hj) _a0 := by
    intro hh
    simp
  exact tr_ (get_eq_get_of_take_succ_eq E' (T.bc f).boundary j htake hjE hj') $ key hj'

structure FieldBaseChangeCompatibility : Prop where
  coSupport_baseChange :
    ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (K : Type) [Field K] (f : T.base →+* K)
      (E' : List (T.bc f).scheme.IdealSheafData) (m : ℕ),
      orderAtLeastLocus ((T.bc f).withBoundary E').ideal m =
        (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal m
  flat_proj :
    ∀ (T : MarkedIdealWithBoundary) (K : Type) [Field K] (f : T.base →+* K),
      Flat $ fieldBaseChangeProjection T K f
  surjective_proj :
    ∀ (T : MarkedIdealWithBoundary) (K : Type) [Field K] (f : T.base →+* K),
      Surjective $ fieldBaseChangeProjection T K f
  withBoundary_preIdeal :
    ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → ∀ (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.bc f).scheme.IdealSheafData),
      SameNontrivialBoundary (T.bc f).boundary E' →
      ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < length E'),
        take (j + 1) E' = take (j + 1) (T.bc f).boundary →
        ((T.bc f).withBoundary E').IsAdmissible →
        DivisorReduction.containedComponentsIdeal ((T.bc f).withBoundary E') j hjE =
          (DivisorReduction.ccI hj).comap (fieldBaseChangeProjection T K f)

namespace DivisorReduction

section
variable (n : ℕ)
def StrictPullbackFieldBaseChangeOfDimLT (L : PrincipalizationAssignment) : Prop :=
  ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → T.krullDimSucc < n →
    ∀ (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.bc f).scheme.IdealSheafData),
      SameNontrivialBoundary (T.bc f).boundary E' →
      ((T.bc f).withBoundary E').IsAdmissible →
      ((T.bc f).withBoundary E').krullDimSucc < n →
      IsStrictPullbackBlowupSeq (fBCP T f)
        (L $ (T.bc f).withBoundary E').toSequenceOfBlowups (L T).toSequenceOfBlowups

def StrictPullbackSmoothSurjectiveOfDimLT (L : PrincipalizationAssignment) : Prop :=
  ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → T.krullDimSucc < n →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h] [Surjective h],
      h ≫ T.structMap = q →
      ∀ (E' : Bdy Y),
        SameNontrivialBoundary (T.pbA q h).boundary E' →
        (T.pbB q h E').IsAdmissible →
        (T.pbB q h E').krullDimSucc < n →
        IsStrictPullbackBlowupSeq h
          (L $ T.pbB q h E').toSequenceOfBlowups (L T).toSequenceOfBlowups

end

private theorem toSequenceOfBlowups_heq_of_eq (L : PrincipalizationAssignment) {A B : MarkedIdealWithBoundary} (h : A = B) :
    HEq (L A).toSequenceOfBlowups (L B).toSequenceOfBlowups := by
  subst h
  rfl

structure DivisorRestrictionFieldBaseChange : Prop where
  comap_comap :
    ∀ (X Y Z : Sch) (f : X ⟶ Y) (g : Y ⟶ Z) (I : Z.IdealSheafData),
      (I.comap g).comap f = I.comap (f ≫ g)
  comap_baseChangeFieldProj_ne_top :
    ∀ (T : MarkedIdealWithBoundary) (K : Type) [Field K] (f : T.base →+* K)
      (I : T.scheme.IdealSheafData), I ≠ ⊤ → I.comap (fBCP T f) ≠ ⊤
  lowerTriple_baseChange_comparison :
    ∀ (T : MarkedIdealWithBoundary) (j : ℕ) (hj : j < T.boundary.length) (K : Type) [Field K]
      [CharZero K] (f : T.base →+* K) (E' : List (T.bc f).scheme.IdealSheafData)
      (hjE : j < length E')
      (hD : E'.lget j hjE = (T.bget j hj).comap (fBCP T f))
      (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData)
      (I0' : (T.bc f).scheme.IdealSheafData)
      (E0' : List (T.bc f).scheme.IdealSheafData)
      (_hI : I0' = I0.comap (fBCP T f))
      (_hE : SameNontrivialBoundary
        (take (length E' - 1) $ E0'.eraseIdx j)
        (map (fun D => D.comap $ fBCP T f)
          (take (T.boundary.length - 1) $ E0.eraseIdx j))),
      ∃ (E'' : List ((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).scheme.IdealSheafData)
        (e : subscheme (E'.lget j hjE) ⟶ ((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).scheme)
        (_ : Smooth e) (_ : Surjective e),
        SameNontrivialBoundary ((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).boundary E'' ∧
        e ≫ fieldBaseChangeProjection (restrictToBoundaryDivisor T j hj I0 E0) K f =
          divisorPullbackMap T j hj I0 E0 (T.bc f).scheme (fBCP T f)
            (E'.lget j hjE) hD ∧
        e ≫ (((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).withBoundary E'').structMap =
          subschemeι (E'.lget j hjE) ≫ (T.bc f).structMap ∧
        SameNontrivialBoundary
          (map (fun D => D.comap (E'.lget j hjE).si)
            (take (length E' - 1) $ E0'.eraseIdx j))
          (map (fun D => D.comap e) E'') ∧
        (((T.bc f).withSchemeIdealBoundary (E'.lget j hjE).subscheme
              (subschemeι (E'.lget j hjE) ≫ (T.bc f).structMap)
              (I0'.comap (E'.lget j hjE).si)
              (map (fun D => D.comap (E'.lget j hjE).si)
                (take (length E' - 1) $ E0'.eraseIdx j))).IsAdmissible →
          (((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).withBoundary E'').IsAdmissible) ∧
        (((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).withBoundary E'').krullDimSucc =
          ((T.bc f).withSchemeIdealBoundary (E'.lget j hjE).subscheme
              (subschemeι (E'.lget j hjE) ≫ (T.bc f).structMap)
              (I0'.comap (E'.lget j hjE).si)
              (map (fun D => D.comap (E'.lget j hjE).si)
                (take (length E' - 1) $ E0'.eraseIdx j))).krullDimSucc
  lowerIdealTop_baseChange :
    ∀ (T : MarkedIdealWithBoundary) (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.bc f).scheme.IdealSheafData),
      lowerIdealWithoutBlowup ((T.bc f).withBoundary E') =
        (lowerIdealWithoutBlowup T).comap (fBCP T f)
  restrictedBoundaryEmptyCenter_baseChange :
    ∀ (T : MarkedIdealWithBoundary) (j : ℕ) (_hj : j < T.boundary.length) (K : Type) [Field K]
      [CharZero K] (f : T.base →+* K) (E' : List (T.bc f).scheme.IdealSheafData),
      SameNontrivialBoundary (T.bc f).boundary E' →
      take (j + 1) E' = take (j + 1) (T.bc f).boundary →
      j < length E' →
      SameNontrivialBoundary
        (take (length E' - 1)
          ((lowerBoundaryWithoutBlowup $ (T.bc f).withBoundary E').eraseIdx j))
        (map (fun D => D.comap $ fBCP T f)
          (take (T.boundary.length - 1) $ (lowerBoundaryWithoutBlowup T).eraseIdx j))
  lowerIdealPre_baseChange :
    ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → T.IsOrderBoundedByMult →
      ∀ (j : ℕ) (hj : j < T.boundary.length) (K : Type) [Field K] [CharZero K]
        (f : T.base →+* K) (E' : List (T.bc f).scheme.IdealSheafData),
        SameNontrivialBoundary (T.bc f).boundary E' →
        ∀ (hjE : j < length E'),
          take (j + 1) E' = take (j + 1) (T.bc f).boundary →
          ((T.bc f).withBoundary E').IsAdmissible →
          containedComponentsIdeal ((T.bc f).withBoundary E') j hjE =
            (ccI hj).comap (fBCP T f) →
          lowerIdealAfterBlowup ((T.bc f).withBoundary E') j hjE =
            (lI hj).comap (fBCP T f)
  restrictedBoundary_baseChange :
    ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → T.IsOrderBoundedByMult →
      ∀ (j : ℕ) (hj : j < T.boundary.length) (K : Type) [Field K] [CharZero K]
        (f : T.base →+* K) (E' : List (T.bc f).scheme.IdealSheafData),
        SameNontrivialBoundary (T.bc f).boundary E' →
        ∀ (hjE : j < length E'),
          take (j + 1) E' = take (j + 1) (T.bc f).boundary →
          ((T.bc f).withBoundary E').IsAdmissible →
          containedComponentsIdeal ((T.bc f).withBoundary E') j hjE =
            (ccI hj).comap (fBCP T f) →
          SameNontrivialBoundary
            (take (length E' - 1)
              ((lowerBoundaryAfterBlowup ((T.bc f).withBoundary E') j hjE).eraseIdx j))
            (map (fun D => D.comap $ fBCP T f)
              (take (T.boundary.length - 1) $ (lB hj).eraseIdx j))

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
include hfacts
section
variable (hflf : DivisorRestrictionFieldBaseChange) (n) (L) (hfe : StrictPullbackFieldBaseChangeOfDimLT n L) (hsm : StrictPullbackSmoothSurjectiveOfDimLT n L) (j : ℕ)
include hflf hfe hsm
theorem restrictToBoundaryDivisor_isStrictPullbackBlowupSeq_baseChange
    (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (hj : j < T.boundary.length) (hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty)
    (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.bc f).scheme.IdealSheafData)
    (hV' : ((T.bc f).withBoundary E').IsAdmissible)
    (hdim' : ((T.bc f).withBoundary E').krullDimSucc ≤ n)
    (hjE : j < length E')
    (hcs' : (orderAtLeastLocus ((T.bc f).withBoundary E').ideal T.mult).Nonempty)
    (hD : E'.lget j hjE = (T.bget j hj).comap (fBCP T f))
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData)
    (I0' : (T.bc f).scheme.IdealSheafData)
    (E0' : List (T.bc f).scheme.IdealSheafData)
    (hI : I0' = I0.comap (fBCP T f))
    (hE : SameNontrivialBoundary (take (length E' - 1) $ E0'.eraseIdx j)
      (map (fun D => D.comap $ fBCP T f)
        (take (T.boundary.length - 1) $ E0.eraseIdx j)))
    (hvT : (restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible)
    (hvS : (restrictToBoundaryDivisor ((T.bc f).withBoundary E') j hjE I0' E0').IsAdmissible) :
    IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj I0 E0 (T.bc f).scheme (fBCP T f)
        (E'.lget j hjE) hD)
      (L $ restrictToBoundaryDivisor ((T.bc f).withBoundary E') j hjE I0' E0').toSequenceOfBlowups
      (L $ restrictToBoundaryDivisor T j hj I0 E0).toSequenceOfBlowups := by
  let _a3 := bcT T f
  obtain ⟨E'', e, hsme, hsue, ha, hb, hc, hdbe, heV, hfd⟩ :=
    hflf.lowerTriple_baseChange_comparison T j hj K f E' hjE hD I0 E0 I0' E0' hI hE
  have hMV := heV hvS
  let _a1 := ((restrictToBoundaryDivisor T j hj I0 E0).baseChange K f).withBoundary E''
  have hMd : _a1.krullDimSucc < n := by
    rw [hfd]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt (tWB _a3 E') hV' hcs' j hjE I0' E0')
      hdim'
  let _a0 := E'.lget j hjE
  let _a4 := bget' hj
  let _a5 := fBCP T f
  have hid : _a1.ideal.comap e
      = cmI I0' _a0.si := by
    have k1 := hflf.comap_comap _ _ _ e
      (fieldBaseChangeProjection (restrictToBoundaryDivisor T j hj I0 E0) K f)
      (cmI I0 _a4.si)
    have k2 := congrArg
      (fun (ph_ : subS _a0 ⟶ tSch (restrictToBoundaryDivisor T j hj I0 E0)) =>
        (cmI I0 _a4.si).comap ph_) hb
    have k3 := hflf.comap_comap _ _ _
      (divisorPullbackMap T j hj I0 E0 (bcT T f).scheme _a5
        _a0 hD)
      _a4.si I0
    have k4 := congrArg
      (cmI I0) $ subschemeMapOfComap_comp _a5 _a4 _a0 hD
    have k5 := hflf.comap_comap _ _ _ _a0.si
      _a5 I0
    have k6 := congrArg
      (fun (I : tISD _a3) =>
        I.comap _a0.si) hI
    exact tr_ k1 $ tr_ k2 $ tr_ k3 $ tr_ k4 $ st_ k5 k6.symm
  let _a2 := take (lenL E' - 1) $ E0'.eraseIdx j
  have htriple : tWB (_a1.pullbackAlong
        _a0.subscheme
        (siI _a0 ≫ tMp _a3) e)
        (map (·.comap _a0.si)
          _a2)
      = restrictToBoundaryDivisor (tWB _a3 E') j hjE I0' E0' :=
    congrArg (fun I => _a3.withSchemeIdealBoundary _a0.subscheme
        (siI _a0 ≫ tMp _a3) I
        (map (fun (D : tISD _a3) =>
            D.comap _a0.si)
          _a2)) hid
  have hbe : SameNontrivialBoundary
      (_a1.pullbackAlong
        _a0.subscheme
        (siI _a0 ≫ tMp _a3) e).boundary
      (map (·.comap _a0.si)
        _a2) := sy_ hdbe
  have hva : (tWB (_a1.pullbackAlong
        _a0.subscheme
        (siI _a0 ≫ tMp _a3) e)
        (map (·.comap _a0.si)
          _a2)).IsAdmissible := by
    rw [htriple]
    exact hvS
  have hdd : (tWB (_a1.pullbackAlong
        _a0.subscheme
        (siI _a0 ≫ tMp _a3) e)
        (map (·.comap _a0.si)
          _a2)).krullDimSucc < n := by
    rw [htriple]
    exact lt_of_lt_of_le
      (hfacts.lowerTriple_dim_lt (tWB _a3 E') hV' hcs' j hjE I0' E0')
      hdim'
  have h2 := @hsm _a1 hMV hMd
      _a0.subscheme
      (siI _a0 ≫ tMp _a3) e hsme hsue hc
      (map (·.comap _a0.si)
        _a2) hbe hva hdd
  let _a6 := L $ restrictToBoundaryDivisor T j hj I0 E0
  have h4 : IsStrictPullbackBlowupSeq
      (divisorPullbackMap T j hj I0 E0 (bcT T f).scheme _a5
        _a0 hD)
      (L (tWB (_a1.pullbackAlong
          _a0.subscheme
          (siI _a0 ≫ tMp _a3) e)
          (map (·.comap _a0.si)
            _a2))).toSequenceOfBlowups
      _a6.toSequenceOfBlowups := by
    rw [← hb]
    exact h2.comp $ hfe (restrictToBoundaryDivisor T j hj I0 E0) hvT (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj I0 E0) hdim) K f E'' ha hMV hMd
  exact (congrArg (fun t =>
      IsStrictPullbackBlowupSeq
        (divisorPullbackMap T j hj I0 E0 (bcT T f).scheme _a5
          _a0 hD) t _a6.toSequenceOfBlowups) $ eq_of_heq $ toSequenceOfBlowups_heq_of_eq L htriple).mp h4

theorem divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange (hbc : DivisorReduction.SmoothPullbackCompatibility) (hfbc : FieldBaseChangeCompatibility)
    (_hshape : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
    (K : Type) [Field K] [CharZero K] f
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : take (j + 1) E' = take (j + 1) (T.baseChange K f).boundary)
    (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible)
    (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n)
    (hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult)
    (hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsStrictPullbackBlowupSeq (fieldBaseChangeProjection T K f)
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.baseChange K f).withBoundary E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  have : IsNoetherian T.scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  have hNTb :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV'
  have : IsNoetherian (bcT T f).scheme := hNTb
  have : IsNoetherian
      (m131 T.structMap (specMapOfFieldHom T.base K f)) := hNTb
  have : Flat (fieldBaseChangeProjection T K f) := hfbc.flat_proj T K f
  have : Flat
      (show tSch (bcT T f) ⟶ tSch T from fieldBaseChangeProjection T K f) :=
    hfbc.flat_proj T K f
  let _a2 := tWB (bcT T f) E'
  have : Flat
      (show tSch _a2 ⟶ tSch T from
        fieldBaseChangeProjection T K f) := hfbc.flat_proj T K f
  have : Surjective
      (show tSch (bcT T f) ⟶ tSch T from fieldBaseChangeProjection T K f) :=
    hfbc.surjective_proj T K f
  have : Surjective
      (show tSch _a2 ⟶ tSch T from
        fieldBaseChangeProjection T K f) := hfbc.surjective_proj T K f
  have hmult : _a2.mult = T.mult := by
    rw [withBoundary_mult, baseChange_mult]
  have hcsEq :=
    hfbc.coSupport_baseChange T hV K f E' T.mult
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  have hcs'' : orderAtLeastLocus ((T.bc f).withBoundary E').ideal
      ((T.bc f).withBoundary E').mult = ∅ := by
    rw [hmult, hcsEq, hcs]
    exact preimage_empty
  exact IsStrictPullbackBlowupSeq.of_length_zero _ _ _
    (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j _ hV' hdim' hO' hDB' hjE hcs'')
    (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs)
  have hcsne := nonempty_iff_ne_empty.2 hcs
  have hcsne' := hcsne.preimage (hfbc.surjective_proj T K f).surj
  rw [← hcsEq] at hcsne'
  have hcs' : orderAtLeastLocus ((T.bc f).withBoundary E').ideal
      ((T.bc f).withBoundary E').mult ≠ ∅ := by
    rw [hmult]
    exact nonempty_iff_ne_empty.1 hcsne'
  have hpre :=
    hfbc.withBoundary_preIdeal T hV K f E' hBE j hj hjE htake hV'
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j (tWB (bcT T f) E'),
    divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T]
  rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO hbal hcs with
    ⟨hZ, hpr, hmk0, heq⟩ | ⟨hZ, hb, hpr, hmk0, heq⟩
  have hZ' : DivisorReduction.containedComponentsIdeal (tWB (bcT T f) E') j hjE = ⊤ := by
    rw [hpre, hZ]
    simp
    rfl
  rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j (tWB (bcT T f) E')
      hV' hjE hO' hDB' hcs' with ⟨-, hpr2, hmk2, heq2⟩ | ⟨hZ2, -⟩
  have hlower := restrictToBoundaryDivisor_isStrictPullbackBlowupSeq_baseChange hres hfacts hflf n L hfe hsm j T hV hdim hj hcsne K f E' hV' hdim' hjE hcsne' (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake) (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) (lowerIdealWithoutBlowup (tWB (bcT T f) E')) (lowerBoundaryWithoutBlowup (tWB (bcT T f) E')) (hflf.lowerIdealTop_baseChange T K f E') (hflf.restrictedBoundaryEmptyCenter_baseChange T j hj K f E' hBE htake hjE) (hfacts.valid_lowerTop T hV hO hbal j hj hZ) (hfacts.valid_lowerTop (tWB (bcT T f) E') hV' hO' hDB' j hjE hZ')
  let _a1 := L $ DivisorReduction.restrictToDivisor (tWB (bcT T f) E') j hjE
  let _a5 := L $ DivisorReduction.restrictToDivisor T j hj
  have hlower2 := IsStrictPullbackBlowupSeq.ofMarkedSequence
    (DivisorReduction.divisorPullbackMap T j hj (p19 T)
      (p20 T) (bcT T f).scheme
      (fieldBaseChangeProjection T K f) (E'.lget j hjE)
      (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
    _a1
    _a5 hlower
  rw [heq hmk0, heq2 hmk2, toMarkedBlowupSequenceData_toSequenceOfBlowups,
    toMarkedBlowupSequenceData_toSequenceOfBlowups]
  exact hfacts.isStrictPullbackSeq_ambientTower T.scheme (bcT T f).scheme
    (bget' hj).subscheme (E'.lget j hjE).subscheme
    (T.bget j hj).si (E'.lget j hjE).si
    (fieldBaseChangeProjection T K f)
    (DivisorReduction.divisorPullbackMap T j hj (p19 T)
      (p20 T) (bcT T f).scheme
      (fieldBaseChangeProjection T K f) (E'.lget j hjE)
      (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
    ((DivisorReduction.isPullback_divisorPullbackMap hbc T j hj (p19 T)
      (p20 T) (bcT T f).scheme
      (fieldBaseChangeProjection T K f) (E'.lget j hjE)
      (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)).flip)
    _a5.toBsd
    _a1.toBsd
    hpr hpr2 hlower2
  exact absurd hZ' hZ2
  have hZ' : DivisorReduction.containedComponentsIdeal (tWB (bcT T f) E') j hjE ≠ ⊤ := by
    rw [hpre]
    exact DivisorReduction.comap_ne_top_of_surjective hbc (fieldBaseChangeProjection T K f)
      (p44 T j hj) hZ
  rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j (tWB (bcT T f) E')
      hV' hjE hO' hDB' hcs' with ⟨hZ2, -⟩ | ⟨-, hb2, hpr2, hmk2, heq2⟩
  exact absurd hZ2 hZ'
  have hlower := restrictToBoundaryDivisor_isStrictPullbackBlowupSeq_baseChange hres hfacts hflf n L hfe hsm j T hV hdim hj hcsne K f E' hV' hdim' hjE hcsne' (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake) (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) (lowerIdealAfterBlowup (tWB (bcT T f) E') j hjE) (lowerBoundaryAfterBlowup (tWB (bcT T f) E') j hjE) (hflf.lowerIdealPre_baseChange T hV hO j hj K f E' hBE hjE htake hV' hpre) (hflf.restrictedBoundary_baseChange T hV hO j hj K f E' hBE hjE htake hV' hpre) (hfacts.valid_lowerPre T hV hO hbal j hj hZ) (hfacts.valid_lowerPre (tWB (bcT T f) E') hV' hO' hDB' j hjE fun hc => hflf.comap_baseChangeFieldProj_ne_top T K f (containedComponentsIdeal T j hj) hZ (st_ hpre hc))
  let _a0 := L $ DivisorReduction.restrictTwistedToDivisor (tWB (bcT T f) E') j hjE
  let _a3 := DivisorReduction.lowerIdealAfterBlowup T j hj
  let _a4 := DivisorReduction.lowerBoundaryAfterBlowup T j hj
  let _a6 := L $ DivisorReduction.restrictTwistedToDivisor T j hj
  have hlower2 := IsStrictPullbackBlowupSeq.ofMarkedSequence
    (DivisorReduction.divisorPullbackMap T j hj _a3
      _a4 (bcT T f).scheme
      (fieldBaseChangeProjection T K f) (E'.lget j hjE)
      (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
    _a0
    _a6 hlower
  have key :=
    hfacts.isStrictPullbackSeq_ambientTower T.scheme (bcT T f).scheme
      (bget' hj).subscheme (E'.lget j hjE).subscheme
      (T.bget j hj).si (E'.lget j hjE).si
      (fieldBaseChangeProjection T K f)
      (DivisorReduction.divisorPullbackMap T j hj _a3
        _a4 (bcT T f).scheme
        (fieldBaseChangeProjection T K f) (E'.lget j hjE)
        (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake))
      ((DivisorReduction.isPullback_divisorPullbackMap hbc T j hj
        _a3 _a4
        (bcT T f).scheme (fieldBaseChangeProjection T K f) (E'.lget j hjE)
        (get_eq_comap_fieldBaseChangeProjection T j hj K f E' hjE htake)).flip)
      _a6.toBsd
      _a0.toBsd
      hpr hpr2 hlower2
  have hb2' := (congrArg (p15 (𝟙 _)) hpre).mp hb2
  rw [heq hmk0, heq2 hmk2, toMarkedBlowupSequenceData_toSequenceOfBlowups,
    toMarkedBlowupSequenceData_toSequenceOfBlowups,
    BlowupSequenceData.prepend_toSequenceOfBlowups_congr hpre hb2 hb2'
      (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian
        (tWB (bcT T f) E') j hjE
        (DivisorReduction.lowerIdealAfterBlowup (tWB (bcT T f) E') j hjE)
        (DivisorReduction.lowerBoundaryAfterBlowup (tWB (bcT T f) E') j hjE)
        _a0 hpr2)]
  exact key.prepend (p44 T j hj) hb hb2'


end

section
variable (hbc : DivisorReduction.SmoothPullbackCompatibility) (hfbc : FieldBaseChangeCompatibility) (hflf : DivisorRestrictionFieldBaseChange) (n) (L O) (hL : IsMaxOrderReduction (fun d => d < n) L O) (j) (hshape : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hj : j < T.boundary.length), T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType → orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj) (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (K : Type) [Field K] [CharZero K] (f) (E' : List (T.baseChange K f).scheme.IdealSheafData) (hBE : SameNontrivialBoundary (T.baseChange K f).boundary E') (htake : take (j + 1) E' = take (j + 1) (T.baseChange K f).boundary) (hV' : ((T.baseChange K f).withBoundary E').IsAdmissible) (hdim' : ((T.baseChange K f).withBoundary E').krullDimSucc ≤ n) (hO' : ((T.baseChange K f).withBoundary E').IsOrderBoundedByMult) (hDB' : ((T.baseChange K f).withBoundary E').IsBalanced hV'.locallyOfFiniteType) (hjE : j < length E')
include hbc hfbc hflf hL hshape hdim hO hbal hj hBE htake hdim' hO' hDB' hjE
theorem divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction :
    IsStrictPullbackBlowupSeq (fBCP T f)
      (((canonicalAlgorithmRules hres).divisorFamily L j $ (T.bc f).withBoundary E').toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) :=
  divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange hres hfacts hflf n L
    hL.base_change_strict hL.smooth_pullback_strict j hbc hfbc
    hshape T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB' hjE

theorem divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction :
    IsPullbackBlowupSequence (fBCP T f)
      (((canonicalAlgorithmRules hres).divisorFamily L j $ (T.bc f).withBoundary E').toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) :=
  by
    have hstrict := divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction hres hfacts hbc hfbc hflf n L O hL j hshape
      T hV hdim hO hbal hj K f E' hBE htake hV' hdim' hO' hDB' hjE
    refine hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups.of_isomorphic $ withoutIsoBlowups_isomorphic_self _ fun i hi => mp_ (support_nonempty_iff_ne_top _) $ divisorFamily_canonicalAlgorithmRules_center_nonempty hres hfacts n L O hL j _ hV' hdim' hO' hDB' hjE i hi
end
end

end DivisorReduction


theorem smooth_id :
    ∀ X, Smooth $ CategoryTheory.CategoryStruct.id X := by
  intro X
  infer_instance

theorem surjective_id :
    ∀ X, Surjective $ CategoryTheory.CategoryStruct.id X := by
  intro X
  constructor
  intro x
  exact ⟨x, rfl⟩

theorem comap_comap :
    ∀ (X Y Z : Sch) (f : X ⟶ Y) (g : Y ⟶ Z) (I : ISD Z),
      (I.comap g).comap f = I.comap (f ≫ g) :=by simp_all
theorem comap_ne_top_of_surjective :
    ∀ (X Y : Sch) (h : Y ⟶ X) [Surjective h] (Z : ISD X),
      Z ≠ ⊤ → Z.comap h ≠ ⊤ := by
  intro X Y h hsurj Z hZ
  have hne : Z.supp.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro he
    exact hZ $ mpr_ (eq_top_iff_support_eq_empty Z) he
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hsurj.1 x
  subst hy
  refine mp_ (support_nonempty_iff_ne_top _) ⟨y, ?_⟩
  simpa [support_comap] using hx

theorem flat_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary) (K : Type) [Field K] (f : T.base →+* K),
      Flat $ fBCP T f := by
  intro T K _ f
  exact m98
    ((m186 T.structMap $ specMapOfFieldHom T.base K f).flip)
    (instFlatSpecMapOfFieldHom ..)

theorem surjective_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary) (K : Type) [Field K] (f : T.base →+* K),
      Surjective (fBCP T f) := by
  intro T K _ f
  let _a0 := specMapOfFieldHom T.base K f
  exact surjective_snd_of_isPullback_of_surjective T.structMap
    (snd T.structMap _a0)
    _a0 (fBCP T f)
    (m186 T.structMap _a0).flip

theorem comap_fieldBaseChangeProjection_ne_top :
    ∀ (T : MarkedIdealWithBoundary) (K : Type) [Field K] (f : T.base →+* K)
      (I : tISD T), I ≠ ⊤ → I.comap (fBCP T f) ≠ ⊤ := by
  intro T K _ f I hI
  have :=
    surjective_fieldBaseChangeProjection T K f
  exact comap_ne_top_of_surjective _ _ (fBCP T f) I hI


theorem isAdmissible_of_withBoundary_isAdmissible
    (hvbr : ∀ (S : MarkedIdealWithBoundary) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible)
    (T : MarkedIdealWithBoundary) (E' : List T.scheme.IdealSheafData)
    (hBE : SameNontrivialBoundary T.boundary E')
    (hV : (T.withBoundary E').IsAdmissible) : T.IsAdmissible := by
  have h := hvbr (T.withBoundary E') T.boundary hV $ sy_ hBE
  have he : (T.withBoundary E').withBoundary T.boundary = T := withBoundary_self T
  rwa [he] at h

private theorem lowerIdealWithoutBlowup_eq_ideal__b1 (S : MarkedIdealWithBoundary) :
    DivisorReduction.lowerIdealWithoutBlowup S = S.ideal :=by simp_all
theorem containedComponentsIdeal_withBoundary_baseChange
    {hres : StrictTransformIsBlowupOfClosedSubscheme} {hno : BlowupPreservesNoetherian}
    (hfacts : DivisorReductionTerminationProperties hres hno)
    (hvbr : ∀ (S : MarkedIdealWithBoundary) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible →
      ∀ (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
        (E' : List (T.baseChange K f).scheme.IdealSheafData),
        SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ j (hj : j < T.boundary.length) (hjE : j < length E'),
          take (j + 1) E' = take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
            DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
              (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) := by
  intro T hV K iK iCZ f E' hBE j hj hjE htake hV'
  have hj' : j < (T.baseChange K f).boundary.length := by
    have h := congrArg length htake
    rw [length_take, length_take] at h
    omega
  have _i14 : DivisorReduction.containedComponentsIdeal (tWB (T.baseChange K f) E') j hjE = DivisorReduction.containedComponentsIdeal (T.baseChange K f) j hj' := by
    let S := T.baseChange K f
    exact tr_ (DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal (tWB S E') j hjE) $
      (congrArg (DivisorReduction.componentsInOrderLocusIdeal S.ideal S.mult) $ get_eq_get_of_take_succ_eq E' (T.baseChange K f).boundary j htake hjE hj').trans
        (DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal S j hj').symm
  rw [_i14]
  exact hfacts.preIdeal_baseChange T hV K f (isAdmissible_of_withBoundary_isAdmissible hvbr (T.baseChange K f) E' hBE hV') j hj hj'

theorem lowerIdealWithoutBlowup_withBoundary_baseChange :
    ∀ (T : MarkedIdealWithBoundary) (K : Type) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.bc f).scheme.IdealSheafData),
      DivisorReduction.lowerIdealWithoutBlowup ((T.bc f).withBoundary E') =
        (DivisorReduction.lowerIdealWithoutBlowup T).comap (fBCP T f) := by
  intro T K iK iCZ f E'
  rw [lowerIdealWithoutBlowup_eq_ideal__b1, lowerIdealWithoutBlowup_eq_ideal__b1, withBoundary_ideal]
  exact baseChange_ideal T K f


namespace DivisorReduction

theorem sameNontrivialBoundary_take_eraseIdx_comap {X Y : Sch} p
    (B : Bdy X) (E' : Bdy Y) j
    (hBE : SameNontrivialBoundary (map (fun D => D.comap p) B) E')
    (htake : take (j + 1) E' = take (j + 1) (map (fun D => D.comap p) B))
    (hj : j < length B) (hjE : j < length E') :
    SameNontrivialBoundary (take (length E' - 1) $ E'.eraseIdx j)
      (map (fun D => D.comap p) $ take (length B - 1) $ B.eraseIdx j) := by
  rw [take_of_length_le $ le_of_eq $ length_eraseIdx_of_lt hjE, take_of_length_le $ le_of_eq $ length_eraseIdx_of_lt hj, ← eraseIdx_map]
  exact hBE.symm.eraseIdx j htake

private theorem isClosed_setOf_connectedComponent_subset {X : Type} [TopologicalSpace X]
    (hop : ∀ x : X, IsOpen $ connectedComponent x) (P : Set X) :
    IsClosed {x : X | connectedComponent x ⊆ P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨connectedComponent x, ?_, hop x, mem_connectedComponent⟩
  intro y hy
  simp [mem_compl_iff, mem_ofPred_eq] at hx ⊢
  intro hsub
  apply hx
  rwa [connectedComponent_eq hy]

theorem lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary (T : MarkedIdealWithBoundary) j
    (hj : j < T.boundary.length) (K : Type) [Field K] [CharZero K] f
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : take (j + 1) E' = take (j + 1) (T.baseChange K f).boundary)
    (hjE : j < length E') :
    SameNontrivialBoundary
      (take (length E' - 1)
        ((lowerBoundaryWithoutBlowup $ (T.baseChange K f).withBoundary E').eraseIdx j))
      (map (fun D => D.comap $ fieldBaseChangeProjection T K f)
        (take (T.boundary.length - 1) $ (lowerBoundaryWithoutBlowup T).eraseIdx j)) := by
  rw [lowerBoundaryWithoutBlowup_eq $ tWB (bcT T f) E', lowerBoundaryWithoutBlowup_eq T]
  exact sameNontrivialBoundary_take_eraseIdx_comap (fieldBaseChangeProjection T K f) T.boundary E' j hBE htake hj hjE

theorem preimageSupportEqComponentsInOrderLocus_of_isAdmissible (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) j
    (hj : j < T.boundary.length) : PreimageSupportEqComponentsInOrderLocus T j hj := by
  let _c0 := bget' hj
  intro h
  have := hV.isNoetherian
  have := noetherianSpace_subscheme _c0
  let _a2 := boundaryComponentsInOrderLocus T j hj
  have hnsU : m86
      (oSch $ boundaryComponentsInOrderLocusOpens T j hj h) :=
    inferInstanceAs $ m86 _a2
  have hqc : QuasiCompact
      (opI (boundaryComponentsInOrderLocusOpens T j hj h) ≫ siI _c0) := by
    constructor
    intro V _ _
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have hU : range (boundaryComponentsInOrderLocusOpens T j hj h).i = _a2 :=
    q1 _
  have hcomp : (opI (boundaryComponentsInOrderLocusOpens T j hj h) ≫ siI _c0)
      = subschemeι _c0 ∘ (boundaryComponentsInOrderLocusOpens T j hj h).i := by
    funext x
    simp
  have hrange :
      range (opI (boundaryComponentsInOrderLocusOpens T j hj h) ≫ siI _c0)
        = subschemeι _c0 '' boundaryComponentsInOrderLocus T j hj := by
    rw [hcomp, range_comp, hU]
  have hsupp : (spI (ker
        (opI (boundaryComponentsInOrderLocusOpens T j hj h) ≫
          siI _c0)) : CSet T.scheme)
      = closure (range
          (opI (boundaryComponentsInOrderLocusOpens T j hj h) ≫ siI _c0)) := by
    rw [support_ker]
  rw [hsupp, hrange, ((isClosedEmbedding _c0.si).isClosedMap _ $ isClosed_setOf_connectedComponent_subset (isOpen_connectedComponent_of_noetherianSpace _) _).closure_eq]
  exact preimage_image_eq _ (isClosedEmbedding _c0.si).injective

end DivisorReduction


def PullbackSmoothOfDimLT (n : ℕ) (L : PrincipalizationAssignment) : Prop :=
  ∀ (T : MarkedIdealWithBoundary), T.IsAdmissible → T.krullDimSucc < n →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
      ∀ (E' : Bdy Y),
        SameNontrivialBoundary (T.pbA q h).boundary E' →
        (T.pbB q h E').IsAdmissible →
        (T.pbB q h E').krullDimSucc < n →
        IsPullbackBlowupSequence h (L $ T.pbB q h E').toSequenceOfBlowups
          (L T).toSequenceOfBlowups

theorem isPullbackSequenceOfBlowups_of_length_eq_zero X X' ph_ (B' : SequenceOfBlowups X')
    (B : SequenceOfBlowups X) (hB' : B'.length = 0) (hB : B.length = 0) : IsPullbackBlowupSequence ph_ B' B := by
  let _a0 := fst ph_ $ sbPrj B 0
  unfold IsPullbackBlowupSequence
  refine ⟨fun _ => 0, ?_, ?_, ?_, sy_ hB, ?_, ?_, ?_, ?_⟩
  intro i hi
  cases i with
  | zero => exact B'.isoZero ≪≫ (asIso _a0).symm
  | succ k => exact absurd hi (by rw [hB']; exact not_succ_le_zero k)
  intro i hi
  rw [hB'] at hi
  exact absurd hi $ not_lt_zero i
  simp_all
  intro i hi
  rw [hB] at hi
  exact absurd hi $ not_lt_zero i
  rintro (_ | k) hi
  show (B'.isoZero ≪≫ (asIso _a0).symm).hom ≫
      _a0 = sbPrj B' 0
  simp [SequenceOfBlowups.projectionToBase_zero]
  exact absurd hi (by rw [hB']; exact not_succ_le_zero k)
  intro i hi _
  exact absurd hi (by rw [hB']; exact not_lt_zero i)
  simp_all

section
variable {X : Sch}
section
variable (s : SequenceOfBlowups X)
theorem forall_ofSequenceOfBlowups_transitionMap_eq :
    ∀ j i (h : i ≤ j), (ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap h = s.transitionMap h := by
  intro j
  induction j with
  | zero =>
    intro i h
    have hi := mp_ le_zero h
    subst hi
    exact tr_ (transitionMap_self _ h) (transitionMap_self s h).symm
  | succ k ih =>
    intro i h
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    subst heq
    exact tr_ (transitionMap_self _ h) (transitionMap_self s h).symm
    have hik := mp_ lt_succ_iff hlt
    let _a0 := ofSequenceOfBlowups s
    let _a1 := s.transitionMap $ le_succ k
    have hb : _a0.toSequenceOfBlowups.transitionMap (le_succ k) = _a1 := by
      have e1 : _a0.toSequenceOfBlowups.transitionMapSucc k = sbTrS s k :=
        (toSequenceOfBlowups_blowupMorphism (ofSequenceOfBlowups s) k).trans $ ofSequenceOfBlowups_blowupMorphism s k
      exact tr_ (st_ (blowupMorphism_eq_transitionMap _ k) e1)
        (blowupMorphism_eq_transitionMap s k)
    have E1 : _a0.toSequenceOfBlowups.transitionMap h
        = _a0.toSequenceOfBlowups.transitionMap (le_succ k) ≫
          _a0.toSequenceOfBlowups.transitionMap hik :=
      (transitionMap_trans _ hik $ le_succ k).symm
    have E2 : s.transitionMap h = _a1 ≫ s.transitionMap hik :=
      (transitionMap_trans s hik $ le_succ k).symm
    have c1 := congrArg (fun g => g ≫ _a0.toSequenceOfBlowups.transitionMap hik) hb
    have c2 := congrArg (fun g => _a1 ≫ g) $ ih i hik
    exact tr_ E1 $ tr_ (tr_ c1 c2) E2.symm

private theorem ofSequenceOfBlowups_transitionMap {i j} (h : i ≤ j) :
    (ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap h = s.transitionMap h :=
  forall_ofSequenceOfBlowups_transitionMap_eq s j i h

theorem ofSequenceOfBlowups_tower :
    (ofSequenceOfBlowups s).toSequenceOfBlowups.tower = s.tower := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  have hf : (homOfLE $ leOfHom f.unop).op = f :=
    congrArg Quiver.Hom.op $ homOfLE_leOfHom f.unop
  have h1 : (ofSequenceOfBlowups s).toSequenceOfBlowups.tower.map f
      = (ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMap (leOfHom f.unop) := by
    rw [transitionMap_def, hf]
  have h2 : s.tower.map f = s.transitionMap (leOfHom f.unop) := by
    rw [transitionMap_def, hf]
  have hid : s.tower.map f
      = 𝟙 (s.tower.obj a) ≫ s.tower.map f ≫ 𝟙 (s.tower.obj b) := by
    simp
  exact tr_ (h1.trans $ tr_ (ofSequenceOfBlowups_transitionMap s $ leOfHom f.unop) h2.symm) hid
end

theorem sequenceOfBlowups_eq_of_tower_eq (s t : SequenceOfBlowups X)
    (ht : s.tower = t.tower) (hl : s.length = t.length)
    (hiso : HEq s.isoZero t.isoZero) (hc : HEq s.center t.center) : s = t := by
  obtain ⟨l1_, F, i1_, c1_, b1_⟩ := s
  obtain ⟨l2_, G, i2_, c2_, b2_⟩ := t
  have hl' := hl
  have ht' := ht
  subst hl'
  subst ht'
  obtain rfl := eq_of_heq hiso
  obtain rfl := eq_of_heq hc
  rfl

theorem ofSequenceOfBlowups_toSequenceOfBlowups (s : SequenceOfBlowups X) :
    (ofSequenceOfBlowups s).toSequenceOfBlowups = s :=
  sequenceOfBlowups_eq_of_tower_eq _ _ (ofSequenceOfBlowups_tower s) rfl (refl _) $ refl _
end

theorem isPullbackBlowupSequence_ofMarkedSequence (A B : MarkedIdealWithBoundary)
    (ph_ : A.scheme ⟶ B.scheme) (sA : A.SequenceOfBlowups) (sB : B.SequenceOfBlowups)
    (hs : IsPullbackBlowupSequence ph_ sA.toSequenceOfBlowups sB.toSequenceOfBlowups) :
    IsPullbackBlowupSequence ph_ sA.toBsd.toSequenceOfBlowups
      sB.toBsd.toSequenceOfBlowups := by
  have hA : sA.toBsd.toSequenceOfBlowups = sA.toSequenceOfBlowups :=
    ofSequenceOfBlowups_toSequenceOfBlowups _
  have hB : sB.toBsd.toSequenceOfBlowups = sB.toSequenceOfBlowups :=
    ofSequenceOfBlowups_toSequenceOfBlowups _
  rwa [hA, hB]

theorem markedIdealWithBoundary_mk_ideal_congr {k : Type} [inst : Field k] {X : Sch}
    {p : X ⟶ Sp k} {m : ℕ} {E : Bdy X}
    {I1 I2 : ISD X} (hI : I1 = I2) :
    (@mk k inst X p I1 m E) = (@mk k inst X p I2 m E) := by
  rw [hI]

theorem isPullbackSequenceOfBlowups_apply_congr (L : PrincipalizationAssignment)
    {X : Sch} (B : SequenceOfBlowups X) (S S' : MarkedIdealWithBoundary) (hS : S = S')
    (ph_ : S.scheme ⟶ X) (ph' : S'.scheme ⟶ X) (hph : HEq ph_ ph')
    (hpb : IsPullbackBlowupSequence ph_ (L S).toSequenceOfBlowups B) :
    IsPullbackBlowupSequence ph' (L S').toSequenceOfBlowups B := by
  subst hS
  have hee := eq_of_heq hph
  subst hee
  exact hpb

theorem isPullbackBlowupSequence_restrictToBoundaryDivisor (n : ℕ) (L : PrincipalizationAssignment)
    (hL : PullbackSmoothOfDimLT n L) (hbc : DivisorReduction.SmoothPullbackCompatibility)
    (T : MarkedIdealWithBoundary) (j : ℕ) (hj : j < T.boundary.length)
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData)
    (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
    (hsm : Smooth h) (hq : h ≫ T.structMap = q)
    (E' : List Y.IdealSheafData) (hjE : j < length E')
    (hD : E'.lget j hjE = (T.bget j hj).comap h)
    (I0' : Y.IdealSheafData) (E0' : List Y.IdealSheafData)
    (hI : I0' = I0.comap h)
    (hEq : SameNontrivialBoundary
      (take (length E' - 1) (E0'.eraseIdx j))
      (map (fun D => D.comap h)
        (take (T.boundary.length - 1) (E0.eraseIdx j))))
    (hadmissible : (DivisorReduction.restrictToBoundaryDivisor T j hj I0 E0).IsAdmissible)
    (hdS : (DivisorReduction.restrictToBoundaryDivisor T j hj I0 E0).krullDimSucc < n)
    (hVS' : (DivisorReduction.restrictToBoundaryDivisor (T.pbB q h E') j hjE
      I0' E0').IsAdmissible)
    (hdS' : (DivisorReduction.restrictToBoundaryDivisor (T.pbB q h E') j hjE
      I0' E0').krullDimSucc < n) :
    IsPullbackBlowupSequence (DivisorReduction.divisorPullbackMap T j hj I0 E0 Y h (E'.lget j hjE) hD)
      (L (DivisorReduction.restrictToBoundaryDivisor (T.pbB q h E') j hjE
        I0' E0')).toSequenceOfBlowups
      (L (DivisorReduction.restrictToBoundaryDivisor T j hj I0 E0)).toSequenceOfBlowups := by
  let _c0 := E'.lget j hjE
  let _c1 := bget' hj
  let _c2 := take (lenL E' - 1) $ E0'.eraseIdx j
  let _c3 := DivisorReduction.restrictToBoundaryDivisor T j hj I0 E0
  let _a0 := DivisorReduction.divisorPullbackMap T j hj I0 E0 Y h _c0 hD
  have hsm0 : Smooth
      _a0 :=
    hbc.smooth_of_isPullback T.scheme Y _c1.subscheme
      _c0.subscheme _c1.si
      _c0.si h
      _a0
      ((hbc.isPullback_inducedHom T.scheme Y h _c1
        _c0 hD).flip) hsm
  have hic : _a0 ≫
      subschemeι _c1 = siI _c0 ≫ h :=
    DivisorReduction.subschemeMapOfComap_comp h _c1 _c0 hD
  have hq0_ : _a0 ≫
      _c3.structMap
      = siI _c0 ≫ q :=
    (sy_ (assoc _ _ _)).trans (tr_ (congrArg (fun g => g ≫ tMp T) hic) (tr_ (assoc _ _ _) (congrArg (fun g => siI _c0 ≫ g) hq)))
  have hIdeal : cmI (tId _c3)
      _a0
      = cmI I0' _c0.si := by
    rw [hI]
    exact DivisorReduction.comap_subschemeMapOfComap h _c1 _c0 hD I0
  have heq : (tWB (_c3.pullbackAlong
        _c0.subscheme (siI _c0 ≫ q)
        _a0)
        (map (·.comap _c0.si)
          _c2))
      = DivisorReduction.restrictToBoundaryDivisor (T.pbB q h E') j hjE I0' E0' :=
    markedIdealWithBoundary_mk_ideal_congr hIdeal
  have hBE0 : SameNontrivialBoundary
      (tBd (_c3.pullbackAlong
        _c0.subscheme (siI _c0 ≫ q)
        _a0))
      (map (·.comap _c0.si)
        _c2) :=
    (DivisorReduction.sameNontrivialBoundary_comap_subschemeio h _c1
      _c0 hD (take (bLen T - 1) (E0.eraseIdx j))
      _c2 hEq).symm
  have hV0 : (tWB (_c3.pullbackAlong
        _c0.subscheme (siI _c0 ≫ q)
        _a0)
        (map (·.comap _c0.si)
          _c2)).IsAdmissible := by simp_all
  have hd0_ : (tWB (_c3.pullbackAlong
        _c0.subscheme (siI _c0 ≫ q)
        _a0)
        (map (·.comap _c0.si)
          _c2)).krullDimSucc < n := by simp_all
  have hmain := hL _c3 hadmissible hdS
    _c0.subscheme (siI _c0 ≫ q)
    _a0 hq0_
    (map (·.comap _c0.si)
      _c2) hBE0 hV0 hd0_
  exact isPullbackSequenceOfBlowups_apply_congr L
    (L _c3).toSequenceOfBlowups _ _ heq _ _
    (refl _a0) hmain

namespace DivisorReduction

structure DivisorReductionHypotheses (hres : StrictTransformIsBlowupOfClosedSubscheme) : Prop where
  trivial_of_coSupport_empty :
    ∀ (L : PrincipalizationAssignment) (j : ℕ) (T : MarkedIdealWithBoundary), T.IsAdmissible →
      j < T.boundary.length →
      ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
        [Smooth h],
        h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          (T.pbB q h E').IsAdmissible →
          (orderAtLeastLocus T.ideal T.mult).Nonempty →
          orderAtLeastLocus (T.pbB q h E').ideal T.mult = ∅ →
          ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
            IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)
  baseChange : SmoothPullbackCompatibility
  smoothImpliesFlat : FlatOfSmooth
  degenerateTransversal : EmptyPulledBackCenterCompatibility
  fieldBaseChangeCompatibility : FieldBaseChangeCompatibility
  boundaryReindexingInvariance : BoundaryReindexingInvariance
  fieldLower : DivisorRestrictionFieldBaseChange
  divisorReduction : DivisorReductionTerminationProperties hres blowupPreservesNoetherian
  pushedBlowupSequenceProperties : PushedBlowupSequenceProperties hres blowupPreservesNoetherian

section
variable {hres : StrictTransformIsBlowupOfClosedSubscheme} (hin : DivisorReductionHypotheses hres)
include hin
theorem DivisorReductionHypotheses.divisorReductionSeqEqAmbient n L O
    (_hL : IsMaxOrderReduction (fun d => d < n) L O) :
    ∀ j T hV hj,
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj := by
  intro j T hV hj _hdim hO hD hcs
  have := isNoetherian_scheme_of_isAdmissible T hV
  have h := divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hin.divisorReduction L j T hV hj hO hD hcs.ne_empty
  rcases h with ⟨hZ, hpr, hmk, hstep⟩ | ⟨hZ, hb, hpr, hmk, hstep⟩
  exact m51 ⟨hZ, hpr, hmk, hstep hmk⟩
  exact m61 ⟨hZ, hb, hpr, hmk, hstep hmk⟩
end

end DivisorReduction

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme)
namespace DivisorReduction
theorem divisorFamily_isPullbackBlowupSequence (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : SmoothPullbackCompatibility) (hsf : FlatOfSmooth) n L
    j (hin : DivisorReductionHypotheses hres)
    (hdt : EmptyPulledBackCenterCompatibility) O (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (Y : Sch)
    q (h : Y ⟶ T.scheme)
    [Smooth h]
    (hq : h ≫ T.structMap = q) (E' : Bdy Y)
    (hBE : SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : take (j + 1) E' = take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hV' : (T.pbB q h E').IsAdmissible)
    (hdim' : (T.pbB q h E').krullDimSucc ≤ n)
    (hO' : (T.pbB q h E').IsOrderBoundedByMult)
    (hDB' : (T.pbB q h E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < E'.length) :
    IsPullbackBlowupSequence h
      (((canonicalAlgorithmRules hres).divisorFamily L j (T.pbB q h E')).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  let hL' : PullbackSmoothOfDimLT n L := by
    intro T hV hdim Y q h hsm hq E' hBE hV' hdim'
    exact hL.smooth_pullback T hV hdim Y q h hq E' hBE hV' hdim'
  let _a0 := E'.lget j hjE
  classical
  have hmult : (T.pbB q h E').mult = tMu T := rfl
  by_cases hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty
  by_cases hcs' : (orderAtLeastLocus (T.pbB q h E').ideal T.mult).Nonempty
  have hZeq : containedComponentsIdeal (T.pbB q h E') j hjE
      = cmI (containedComponentsIdeal T j hj) h :=
    hbc.preIdeal_comap T hV Y q h hq E' hBE j hj hjE htake hV'
  have _hNT : IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  have _hNY : IsNoetherian Y :=
    isNoetherian_scheme_of_isAdmissible (T.pbB q h E') hV'
  have _hfl : Flat h := hsf.flat_of_smooth T.scheme Y h inferInstance
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T,
    divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j (T.pbB q h E')]
  rcases hshape T hV hj hdim hO hbal hcs with ⟨hZ, hpr, hmk, heq⟩ | ⟨hZ, hb, hpr, hmk, heq⟩
  rcases hshape (T.pbB q h E') hV' hjE hdim' hO' hDB' hcs' with
    ⟨hZ', hpr', hmk', heq'⟩ | ⟨hZ', hb', hpr', hmk', heq'⟩
  rw [heq, heq', toMarkedBlowupSequenceData_toSequenceOfBlowups,
    toMarkedBlowupSequenceData_toSequenceOfBlowups]
  let _a2 := restrictToDivisor T j hj
  exact hfacts.isPullbackSeq_ambientTower T.scheme Y
    (bget' hj).subscheme _a0.subscheme
    (T.bget j hj).si _a0.si h
    (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h _a0
      (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
    ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
      _a0 (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
    (p54 (L _a2)).toBlowupSequenceData
    (p54
      (L (restrictToDivisor (T.pbB q h E') j hjE))).toBlowupSequenceData
    hpr hpr'
    (isPullbackBlowupSequence_ofMarkedSequence
      (restrictToDivisor (T.pbB q h E') j hjE) _a2
      (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h _a0
        (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
      (L (restrictToDivisor (T.pbB q h E') j hjE))
      (L _a2)
      (isPullbackBlowupSequence_restrictToBoundaryDivisor n L hL' hbc T j hj (p19 T) (p20 T) Y q h inferInstance hq E' hjE (get_eq_comap_get_boundary T j hj Y q h E' hjE htake) (p19 (pbBT T q h E')) (p20 (pbBT T q h E')) (lowerIdealWithoutBlowup_withBoundary T Y q h E') (sameNontrivialBoundary_lowerBoundaryWithoutBlowup T j hj Y q h E' hBE htake hjE) (hfacts.valid_lowerTop T hV hO hbal j hj hZ) (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj (p19 T) (p20 T)) hdim) (hfacts.valid_lowerTop (pbBT T q h E') hV' hO' hDB' j hjE hZ') (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (pbBT T q h E') hV' hcs' j hjE (p19 (pbBT T q h E')) (p20 (pbBT T q h E'))) hdim')))
  exact absurd (tr_ hZeq $ tr_ (congrArg (cmI · h) hZ) (comap_top ..)) hZ'
  rcases hshape (T.pbB q h E') hV' hjE hdim' hO' hDB' hcs' with
    ⟨hZ', hpr', hmk', heq'⟩ | ⟨hZ', hb', hpr', hmk', heq'⟩
  have htop : cmI (containedComponentsIdeal T j hj) h = ⊤ := st_ hZeq hZ'
  rw [heq, heq', toMarkedBlowupSequenceData_toSequenceOfBlowups,
    toMarkedBlowupSequenceData_toSequenceOfBlowups]
  refine IsPullbackBlowupSequence.prepend_of_comap_eq_top ?_ (containedComponentsIdeal T j hj) hb htop
  exact hfacts.isPullbackSeq_ambientTower T.scheme Y
    (bget' hj).subscheme _a0.subscheme
    (T.bget j hj).si _a0.si h
    (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
      _a0 (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
    ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
      Y h _a0 (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
    (p54 (L (restrictTwistedToDivisor T j hj))).toBlowupSequenceData
    (p54
      (L (restrictToDivisor (T.pbB q h E') j hjE))).toBlowupSequenceData
    hpr hpr'
    (isPullbackBlowupSequence_ofMarkedSequence
      (restrictToDivisor (T.pbB q h E') j hjE) (restrictTwistedToDivisor T j hj)
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        _a0 (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
      (L (restrictToDivisor (T.pbB q h E') j hjE))
      (L (restrictTwistedToDivisor T j hj))
      (isPullbackBlowupSequence_restrictToBoundaryDivisor n L hL' hbc T j hj (p21 hj) (p37 hj) Y q h inferInstance hq E' hjE (get_eq_comap_get_boundary T j hj Y q h E' hjE htake) (p19 (pbBT T q h E')) (p20 (pbBT T q h E')) (tr_ (lowerIdealWithoutBlowup_withBoundary T Y q h E') (hdt.lowerIdealPre_comap_eq_lowerIdealTop_comap T hV hO j hj Y h htop).symm) (tr_ (sameNontrivialBoundary_lowerBoundaryWithoutBlowup T j hj Y q h E' hBE htake hjE) (hdt.boundaryEquiv_restrictedBoundary_comap_of_center_comap_eq_top T hV j hj Y h htop).symm) (hfacts.valid_lowerPre T hV hO hbal j hj hZ) (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj (p21 hj) (p37 hj)) hdim) (hfacts.valid_lowerTop (pbBT T q h E') hV' hO' hDB' j hjE hZ') (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (pbBT T q h E') hV' hcs' j hjE (p19 (pbBT T q h E')) (p20 (pbBT T q h E'))) hdim')))
  have hne : cmI (containedComponentsIdeal T j hj) h ≠ ⊤ := fun hcc => hZ' $ tr_ hZeq hcc
  have hbb : p15 (𝟙 Y) (cmI (containedComponentsIdeal T j hj) h) :=
    by
      rw [← hZeq]
      exact hfacts.isBlowup_id_preIdeal _ hV' j hjE
  rw [heq, heq', toMarkedBlowupSequenceData_toSequenceOfBlowups,
    toMarkedBlowupSequenceData_toSequenceOfBlowups,
    BlowupSequenceData.prepend_toSequenceOfBlowups_congr hZeq hb' hbb]
  refine IsPullbackBlowupSequence.prepend_of_comap_ne_top ?_ (containedComponentsIdeal T j hj) hb hbb hne
  let _a1 := restrictTwistedToDivisor (T.pbB q h E') j hjE
  exact hfacts.isPullbackSeq_ambientTower T.scheme Y
    (bget' hj).subscheme _a0.subscheme
    (T.bget j hj).si _a0.si h
    (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
      _a0 (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
    ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
      Y h _a0 (get_eq_comap_get_boundary T j hj Y q h E' hjE htake)).flip)
    (p54 (L (restrictTwistedToDivisor T j hj))).toBlowupSequenceData
    (p54
      (L _a1)).toBlowupSequenceData
    hpr hpr'
    (isPullbackBlowupSequence_ofMarkedSequence
      _a1 (restrictTwistedToDivisor T j hj)
      (divisorPullbackMap T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) Y h
        _a0 (get_eq_comap_get_boundary T j hj Y q h E' hjE htake))
      (L _a1)
      (L (restrictTwistedToDivisor T j hj))
      (isPullbackBlowupSequence_restrictToBoundaryDivisor n L hL' hbc T j hj (lI hj) (p37 hj) Y q h inferInstance hq E' hjE (get_eq_comap_get_boundary T j hj Y q h E' hjE htake) (lowerIdealAfterBlowup (pbBT T q h E') j hjE) (lowerBoundaryAfterBlowup (pbBT T q h E') j hjE) (hbc.lowerIdealPre_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZeq) (hbc.boundaryEquiv_restrictedBoundary_comap T hV Y q h hq E' hBE j hj hjE htake hV' hO hZeq) (hfacts.valid_lowerPre T hV hO hbal j hj hZ) (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt T hV hcs j hj (p21 hj) (p37 hj)) hdim) (hfacts.valid_lowerPre (pbBT T q h E') hV' hO' hDB' j hjE hZ') (lt_of_lt_of_le (hfacts.lowerTriple_dim_lt (pbBT T q h E') hV' hcs' j hjE (lowerIdealAfterBlowup (pbBT T q h E') j hjE) (lowerBoundaryAfterBlowup (pbBT T q h E') j hjE)) hdim')))
  have hempty : orderAtLeastLocus (T.pbB q h E').ideal T.mult = ∅ :=
    not_nonempty_iff_eq_empty.mp hcs'
  refine hin.trivial_of_coSupport_empty L j T hV hj Y q h hq E' hV' hcs hempty _ ?_
  refine divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j _ hV' hdim' hO' hDB' hjE ?_
  rwa [hmult]
  have hempty : orderAtLeastLocus T.ideal T.mult = ∅ := mp_ not_nonempty_iff_eq_empty hcs
  have hempty' : orderAtLeastLocus (T.pbB q h E').ideal T.mult = ∅ := by
    rw [orderAtLeastLocus_withBoundary_pullbackAlong hbc T hV Y q h hq E' T.mult, hempty]
    exact preimage_empty
  refine isPullbackSequenceOfBlowups_of_length_eq_zero T.scheme Y h _ _ ?_ (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hempty)
  refine divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j _ hV' hdim' hO' hDB' hjE ?_
  rwa [hmult]


theorem divisorFamily_isStrictPullbackBlowupSeq_of_smooth (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : SmoothPullbackCompatibility) (hsf : FlatOfSmooth) n L
    j O (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ T hV hj,
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length) (Y : Sch)
    q (h : Y ⟶ T.scheme)
    [Smooth h] [Surjective h]
    (hq : h ≫ T.structMap = q) (E' : Bdy Y)
    (hBE : SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (htake : take (j + 1) E' = take (j + 1) (T.pullbackAlong Y q h).boundary)
    (hV' : (T.pbB q h E').IsAdmissible)
    (hdim' : (T.pbB q h E').krullDimSucc ≤ n)
    (hO' : (T.pbB q h E').IsOrderBoundedByMult)
    (hDB' : (T.pbB q h E').IsBalanced hV'.locallyOfFiniteType)
    (hjE : j < length E') :
    IsStrictPullbackBlowupSeq h
      (((canonicalAlgorithmRules hres).divisorFamily L j $ T.pbB q h E').toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  let _a2 := orderAtLeastLocus_withBoundary_pullbackAlong hbc T hV Y q h hq E' T.mult
  let _a3 := bget' hj
  let _c0 := tWB (T.pbA q h) E'
  let _c1 := E'.lget j hjE
  let _c2 := get_eq_comap_get_boundary T j hj Y q h E' hjE htake
  classical
  have : IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  have : IsNoetherian
      _c0.scheme :=
    isNoetherian_scheme_of_isAdmissible _ hV'
  have : IsNoetherian Y := isNoetherian_scheme_of_isAdmissible _ hV'
  have : Flat h := hsf.flat_of_smooth T.scheme Y h inferInstance
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j _c0,
    divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j T]
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  have hcs2 : orderAtLeastLocus _c0.ideal T.mult = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    rwa [_a2, hcs] at hx
  rw [divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian
      _c0 (fun S _ => L S) j hjE hcs2,
    divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty hres blowupPreservesNoetherian T
      (fun S _ => L S) j hj hcs]
  exact IsStrictPullbackBlowupSeq.of_length_zero h _ _ rfl rfl
  have hcsne := mpr_ nonempty_iff_ne_empty hcs
  have hcsne' : (orderAtLeastLocus _c0.ideal T.mult).Nonempty := by
    obtain ⟨x, hx⟩ := hcsne
    obtain ⟨y, rfl⟩ := h.surjective x
    refine ⟨y, ?_⟩
    rwa [_a2]
  have hpre :=
    hbc.preIdeal_comap T hV Y q h hq E' hBE j hj hjE htake hV'
  have hsT := hshape T hV hj hdim hO hbal hcsne
  have hsT' := hshape _c0 hV' hjE hdim' hO' hDB' hcsne'
  unfold DivisorReductionSeqEqAmbient at hsT hsT'
  rcases hsT with ⟨hZ, hpr, _hmk, hstep⟩ | ⟨hZ, hb, hpr, _hmk, hstep⟩
  rcases hsT' with ⟨hZ', hpr', _hmk', hstep'⟩ | ⟨hZ', _hb', _hpr', _hmk', _hstep'⟩
  rw [hstep, hstep', toMarkedBlowupSequenceData_toSequenceOfBlowups,
    toMarkedBlowupSequenceData_toSequenceOfBlowups]
  exact hfacts.isStrictPullbackSeq_ambientTower _ _ _ _
    _a3.si _c1.si h
    (divisorPullbackMap T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h _c1
      _c2)
    ((isPullback_divisorPullbackMap hbc T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) Y h
      _c1 _c2).flip)
    (p54 $ L $ restrictToDivisor T j hj).toBlowupSequenceData
    (p54
      (L $ restrictToDivisor _c0 j hjE)).toBlowupSequenceData
    hpr hpr'
    (IsStrictPullbackBlowupSeq.ofMarkedSequence _ _ _
      (isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top hres hfacts n L O hL j hbc T hV hdim hO hbal hj hcsne Y q h hq E' hBE htake
        hV' hdim' hO' hDB' hjE hcsne' hZ hZ'))
  exfalso
  have htc : cmI (ccI hj) h = ⊤ := by
    rw [hZ]
    simp
  exact hZ' $ tr_ hpre htc
  rcases hsT' with ⟨hZ', _hpr', _hmk', _hstep'⟩ | ⟨_hZ', hb', hpr', _hmk', hstep'⟩
  have hcontra : (ccI hj).comap h = ⊤ := by rw [← hpre]
                                            exact hZ'
  exact absurd hcontra $ comap_ne_top_of_surjective hbc h (ccI hj) hZ
  rw [hstep, hstep', toMarkedBlowupSequenceData_toSequenceOfBlowups,
    toMarkedBlowupSequenceData_toSequenceOfBlowups]
  have hb'' : p15 (𝟙 Y) $ (containedComponentsIdeal T j hj).comap h := by
    rw [← hpre]
    exact hfacts.isBlowup_id_preIdeal _ hV' j hjE
  let _a4 := lowerIdealAfterBlowup T j hj
  let _a5 := lowerBoundaryAfterBlowup T j hj
  have hamb := hfacts.isStrictPullbackSeq_ambientTower _ _ _ _
    _a3.si _c1.si h
    (divisorPullbackMap T j hj _a4 _a5 Y h
      _c1 _c2)
    ((isPullback_divisorPullbackMap hbc T j hj _a4 _a5 Y h
      _c1 _c2).flip)
    (p54 $ L $ restrictTwistedToDivisor T j hj).toBlowupSequenceData
    (L $ restrictTwistedToDivisor _c0 j hjE).toBsd
    hpr hpr'
    (IsStrictPullbackBlowupSeq.ofMarkedSequence _ _ _
      (isStrictPullbackBlowupSeq_restrictTwistedToDivisor hres hfacts n L O hL j hbc T hV hdim hO hbal hj hcsne Y q h hq E' hBE htake
        hV' hdim' hO' hDB' hjE hcsne' hZ hpre))
  rw [BlowupSequenceData.prepend_toSequenceOfBlowups_congr hpre hb' hb''
    (amb hres blowupPreservesNoetherian hpr')]
  exact hamb.prepend (containedComponentsIdeal T j hj) hb hb''


end DivisorReduction

theorem isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ n (L O : PrincipalizationAssignment),
      IsMaxOrderReduction (fun d => d < n) L O →
      ∀ j,
        IsBoundaryDivisorReduction (fun d => d ≤ n) j ((canonicalAlgorithmRules hres).divisorFamily L j) L := by
  intro n L O hL j
  have hshapeN :=
    fun T hV hj hdim hO hbal hcs => hin.divisorReductionSeqEqAmbient n L O hL j T hV hj hdim hO hbal hcs
  have hshapeE :=
    fun T hV hj hdim hO hbal hcs =>
      hshapeN T hV hj hdim hO hbal $ mpr_ nonempty_iff_ne_empty hcs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
  exact DivisorReduction.divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReduction hin.baseChange
    hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E' hBE htake
    hV' hdim' hO' hDB' hjE
  intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
  exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReduction
    hin.baseChange hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E'
    hBE htake hV' hdim' hO' hDB' hjE
  intro T hV hdim hO hbal hj i hi x
  exact divisorFamily_canonicalAlgorithmRules_orderAt_le_mult hres hin.divisorReduction n L j T hV hdim hO hbal hj i hi x
  intro T hV hdim hO hbal hj i hi
  exact divisorFamily_canonicalAlgorithmRules_center_nonempty hres hin.divisorReduction n L O hL j T hV hdim hO hbal
    hj i hi
  intro T hV hdim hO hbal hj hm J hVJ hdimJ him
  exact isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReduction n L O hL j T hV hdim hO
    (fun _ => hbal) hj hm J hVJ hdimJ him
  intro T hV hdim hO hbal hj
  obtain ⟨D, b, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReduction hin.pushedBlowupSequenceProperties n L O hL j T hV hdim hO
      hbal hj
  refine ⟨D, b, h1, h2, h3, h4, ?_, h6, ?_⟩
  intro t ht hb
  exact h5 t ht fun hbt h0 => hb ⟨hbt, h0⟩
  intro t ht hb
  exact h7 t ht fun hbt h0 => hb ⟨hbt, h0⟩
  intro T hV hdim hO hbal hj Y q h _ hq E' hBE htake hV' hdim' hO' hDB' hjE
  exact DivisorReduction.divisorFamily_isPullbackBlowupSequence hres hin.divisorReduction hin.baseChange
    hin.smoothImpliesFlat n L j hin
    hin.degenerateTransversal O hL
    hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE
  intro T hV hdim hO hbal hj Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE
  exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_of_smooth hres hin.divisorReduction hin.baseChange
    hin.smoothImpliesFlat n L j O hL
    hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE
  intro T hV hdim hO hbal hj hcs
  exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs

end





namespace DivisorReduction

theorem filter_map_eq_of_filter_eq {al_ : Type} (p : al_ → Bool) (g : al_ → al_)
    (hpg : ∀ a, p a = false → p (g a) = false) {A B : List al_}
    (hAB : filter p A = filter p B) :
    filter p (A.map g) = filter p (B.map g) := by
  have key : ∀ L : List al_,
      filter p (L.map g) = filter p ((filter p L).map g) := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih =>
      by_cases ha : p a = true
      simp [filter_cons, ha, ih]
      have ha' : p a = false := by simpa using ha
      simp [ha', hpg a ha', ih]
  rw [key A, key B, hAB]

theorem sameNontrivialBoundary_map {X : Sch} (g : ISD X → ISD X)
    (hg : g ⊤ = ⊤) {A B : Bdy X} (h : SameNontrivialBoundary A B) :
    SameNontrivialBoundary (A.map g) $ B.map g := by
  rw [sameNontrivialBoundary_iff] at h ⊢
  unfold nontrivialPart at h ⊢
  refine filter_map_eq_of_filter_eq _ g ?_ h
  intro a ha
  have ha' : a = ⊤ := by simpa using ha
  subst ha'
  simp [hg]

theorem sameNontrivialBoundary_take_eraseIdx_strictTransform {X : Sch} Z
    (A B : Bdy X) a b (ha : a < length A) (hb : b < length B)
    (h : SameNontrivialBoundary (A.eraseIdx a) $ B.eraseIdx b) :
    SameNontrivialBoundary
      (take (length A - 1)
        ((map (strictTransform (𝟙 X) Z) (map (fun D => D.comap $ 𝟙 X) A)
          ++ [exceptionalIdeal (𝟙 X) Z]).eraseIdx a))
      (take (length B - 1)
        ((map (strictTransform (𝟙 X) Z) (map (fun D => D.comap $ 𝟙 X) B)
          ++ [exceptionalIdeal (𝟙 X) Z]).eraseIdx b)) := by
  have hcomap : ∀ I : ISD X, I.comap (𝟙 X) = I := by
    intro I
    simp
  have hgtop : (fun D : ISD X => p6 (𝟙 X) Z $ D.comap $ 𝟙 X) ⊤
      = (⊤ : ISD X) := by
    show p6 (𝟙 X) Z ((⊤ : ISD X).comap $ 𝟙 X) = ⊤
    rw [hcomap]
    have h1 := comap_le_strictTransform (𝟙 X) Z (⊤)
    rw [hcomap] at h1
    exact le_antisymm le_top h1
  have key : ∀ C c, c < lenL C →
      take (lenL C - 1)
        ((map (p6 (𝟙 X) Z) (map (fun D => D.comap $ 𝟙 X) C)
          ++ [p5 (𝟙 X) Z]).eraseIdx c)
        = map (fun D : ISD X => p6 (𝟙 X) Z $ D.comap $ 𝟙 X)
            (C.eraseIdx c) := by
    intro C c hc
    have hlen : (map (fun D : ISD X =>
        p6 (𝟙 X) Z $ D.comap $ 𝟙 X) $ C.eraseIdx c).length = length C - 1 := by
      rw [length_map]
      exact length_eraseIdx_of_lt hc
    have hmap : ∀ f : ISD X → ISD X, c < lenL (C.map f) := by simp_all
    simp only [map_map, Function.comp_def]
    rw [eraseIdx_append_of_lt_length $ hmap _]
    rw [eraseIdx_map, ← hlen, take_append_of_le_length $ m164 _,
      take_length]
  rw [key A a ha, key B b hb]
  exact sameNontrivialBoundary_map (fun D : ISD X => p6 (𝟙 X) Z $ D.comap $ 𝟙 X)
    hgtop h

section
variable (T : MarkedIdealWithBoundary) (L1_ L2_ : List T.scheme.IdealSheafData) (j1) (hj1_ : j1 < length L1_) (j2_) (hj2_ : j2_ < length L2_) (heq : L1_.lget j1 hj1_ = L2_.lget j2_ hj2_)
include heq
theorem lowerIdealAfterBlowup_withBoundary_eq_of_get_eq :
    lowerIdealAfterBlowup (T.withBoundary L2_) j2_ hj2_ = lowerIdealAfterBlowup (T.withBoundary L1_) j1 hj1_ := by
  unfold lowerIdealAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L1_ L2_ j1 hj1_ j2_ hj2_ heq]
  rfl

theorem sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq
    (hBE : SameNontrivialBoundary (L2_.eraseIdx j2_) $ L1_.eraseIdx j1) :
    SameNontrivialBoundary
      (take (length L2_ - 1) $ (lowerBoundaryAfterBlowup (T.withBoundary L2_) j2_ hj2_).eraseIdx j2_)
      (take (length L1_ - 1) $ (lowerBoundaryAfterBlowup (T.withBoundary L1_) j1 hj1_).eraseIdx j1) := by
  unfold lowerBoundaryAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L1_ L2_ j1 hj1_ j2_ hj2_ heq]
  exact sameNontrivialBoundary_take_eraseIdx_strictTransform
    (containedComponentsIdeal (tWB T L2_) j2_ hj2_) L2_ L1_ j2_ j1 hj2_ hj1_ hBE
end

theorem boundaryReindexingInvariance : BoundaryReindexingInvariance :=
  ⟨smooth_id, surjective_id, lowerIdealAfterBlowup_withBoundary_eq_of_get_eq, sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq⟩

end DivisorReduction




theorem orderAtLeastLocus_withBoundary_baseChange_eq_preimage (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible)
    (K : Type) [Field K] (f : T.base →+* K)
    E' m :
    orderAtLeastLocus ((T.bc f).withBoundary E').ideal m =
      (fBCP T f) ⁻¹' orderAtLeastLocus T.ideal m := by
  haveI := hV.charZero
  haveI := mp_ (RingHom.charZero_iff f.injective) hV.charZero
  haveI := hV.smooth
  exact orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal m




section
variable {S : Type} [TopologicalSpace S] [NoetherianSpace S] (hsep : ∀ C1_ ∈ irreducibleComponents S, ∀ C2_ ∈ irreducibleComponents S, C1_ ≠ C2_ → Disjoint C1_ C2_) {K} (hK : K ∈ irreducibleComponents S)
include hsep hK
theorem isClopen_of_pairwise_disjoint_irreducibleComponents : IsClopen K := by
  have hcompl : Kᶜ = ⋃₀ (irreducibleComponents S \ {K}) := by
    ext x
    constructor
    intro hx
    refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩, (irreducibleComponent_property x).2.1 rfl⟩
    simp [mem_singleton_iff]
    intro h
    exact hx (by rw [← h]; exact (irreducibleComponent_property x).2.1 rfl)
    rintro ⟨C, ⟨hC, hCK⟩, hxC⟩ hxK
    refine mp_ disjoint_left (hsep C hC K hK ?_) hxC hxK
    intro h
    exact hCK $ by simp [h]
  refine ⟨isClosed_of_mem_irreducibleComponents K hK, ?_⟩
  rw [← isClosed_compl_iff, hcompl, sUnion_eq_biUnion]
  exact (m197 m169 sdiff_subset).isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

theorem connectedComponent_subset_of_mem_irreducibleComponents {x : S} (hx : x ∈ K) :
    connectedComponent x ⊆ K :=
  (isClopen_of_pairwise_disjoint_irreducibleComponents hsep hK).connectedComponent_subset hx
end

namespace DivisorReduction

theorem smooth_subschemeio_comp_structureMorphism (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) j
    (hj : j < T.boundary.length) :
    Smooth $ subschemeι (T.bget j hj) ≫ T.structMap := by
  exact an2 $ mp_ (isSmoothDivisor_iff _ _) $ (mp_ (inStrictNormalCrossingPosition_iff T.structMap T.boundary) hV.snc).1 _ $ getElem_mem hj

theorem ker_io_comp_ne_top {X Z : Sch} (hX : NoetherianSpace ↥X) (V : Opn X)
    (g : X ⟶ Z) (x : ↥X) (hx : x ∈ V) :
    ker (V.i ≫ g) ≠ ⊤ := by
  have : NoetherianSpace V.toScheme := inferInstanceAs $ NoetherianSpace (V : Set X)
  intro h
  have : QuasiCompact $ opI V ≫ g := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hx' : x ∈ range V.i := by simpa using hx
  obtain ⟨y, hy⟩ := hx'
  have h3 : g x ∈ (spI (ker $ opI V ≫ g) : Set Z) := by
    rw [support_ker]
    exact subset_closure ⟨y, by simp [hy]⟩
  rw [h] at h3
  simp at h3

section
variable (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible)
theorem isAdmissible_restrictToDivisor
    (_hOB : T.IsOrderBoundedByMult) (hBalanced : T.IsBalanced hV.locallyOfFiniteType) j
    (hj : j < T.boundary.length) (hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤) :
    (DivisorReduction.restrictToDivisor T j hj).IsAdmissible := by
  let _c0 := siI (bgetT hj) ≫ tMp T
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hsm :=
    smooth_subschemeio_comp_structureMorphism T hV j hj
  have := hsm
  have hlft : LocallyOfFiniteType
      _c0 := inferInstance
  have hqc : QuasiCompact
      _c0 := inferInstance
  have hsnc0 :=
    inStrictNormalCrossingPosition_comap_subschemeio_eraseIdx T.structMap T.boundary hV.snc j hj
  have hbd : p20 T = tBd T := by simp_all
  have hsnc : InStrictNormalCrossingPosition _c0
      (map (fun D => cmI D (bgetT hj).si)
        (take (bLen T - 1) $ (p20 T).eraseIdx j)) := by
    rwa [hbd, take_of_length_le $ le_of_eq $ length_eraseIdx_of_lt hj]
  have _i16 : NonzeroOnComponents $ cmI (p19 T) (bgetT hj).si := by
    let _c0 := bget' hj
    classical
    have := hV.charZero
    have := hV.smooth
    have := hV.locallyOfFiniteType
    have hsm :=
      smooth_subschemeio_comp_structureMorphism T hV j hj
    have hNoe : NoetherianSpace _c0.subscheme :=
      by
      have := hV.isNoetherian
      have : NoetherianSpace T.scheme := inferInstance
      exact (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
        _c0.si).isInducing.noetherianSpace
    have := hNoe
    have hcs :=
      orderAtLeastLocus_eq_support_of_isDerivBalanced T.base T.structMap T.ideal T.mult hBalanced hV.one_le_mult
    have hdisj :=
      irreducibleComponentsDisjointOfSmooth T.base _c0.subscheme
        (siI _c0 ≫ tMp T) hsm
    have hI : p19 T = tId T := by simp_all
    rw [hI, nonzeroOnComponents_iff]
    intro C hC hsub
    obtain ⟨x, hxC⟩ := hC.1.nonempty
    have hCsub : C ⊆ _c0.si ⁻¹' orderAtLeastLocus T.ideal T.mult := by
      intro y hy
      have h1 : y ∈ (spI (T.ideal.comap _c0.si) :
          CSet _c0.subscheme) := hsub hy
      rw [m163, hcs]
      simpa [support_comap] using h1
    have hxV : connectedComponent x ⊆
        _c0.si ⁻¹' orderAtLeastLocus T.ideal T.mult :=
      fun z hz => hCsub $ connectedComponent_subset_of_mem_irreducibleComponents hdisj hC hxC hz
    exact absurd (st_ (containedComponentsIdeal_eq_ker T j hj $ isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj) hZ) $ ker_io_comp_ne_top hNoe _ _ x hxV
  exact ⟨hV.charZero, hlft,
    _i16, hV.one_le_mult, hqc, hsm, hsnc⟩
end

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

theorem isIrreducible_connectedComponent_boundary_subscheme (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (z : ↥(T.bget j hj).subscheme) :
    IsIrreducible $ connectedComponent z := by
  let _a0 := bget' hj
  have :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hsep := irreducibleComponentsDisjointOfSmooth T.base _a0.subscheme
    (siI _a0 ≫ tMp T) $ (mp_ (isSmoothDivisor_iff T.structMap _a0) $ isSmoothDivisor_boundary_get T hV j hj).2
  rw [m15 (connectedComponent_subset_of_mem_irreducibleComponents hsep (irreducibleComponent_mem_irreducibleComponents z) mem_irreducibleComponent) $ (isIrreducible_irreducibleComponent (x := z)).2.isPreconnected.subset_connectedComponent mem_irreducibleComponent]
  exact isIrreducible_irreducibleComponent

section
variable {X Y : Sch} (g : Y ⟶ X)
theorem get_eq_comap_get_of_eq_map (E : Bdy X)
    (F : Bdy Y) (hF : F = E.map fun D => D.comap g) j
    (hj : j < length E) (hj' : j < length F) :
    F.lget j hj' = (E.lget j hj).comap g :=by simp_all
end

theorem containedComponentsIdeal_comap_of_flat (T T' : MarkedIdealWithBoundary) (hV : T.IsAdmissible)
    (hV' : T'.IsAdmissible) (g : T'.scheme ⟶ T.scheme) (hflat : Flat g) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < T'.boundary.length)
    (hD : T'.bget j hj' = (T.bget j hj).comap g)
    (hcs : orderAtLeastLocus T'.ideal T'.mult = ⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)
    (hcl : IsClosed $ orderAtLeastLocus T.ideal T.mult) :
    DivisorReduction.ccI hj' = (DivisorReduction.ccI hj).comap g := by
  have := hflat
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  have hopen' := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T' hV' j hj'
  have hirr :=
    fun w => isIrreducible_connectedComponent_boundary_subscheme T hV j hj w
  have hN' :=
    noetherianSpace_boundary_subscheme T' hV' j hj'
  let _a0 := bget' hj
  have key : ∀ (D' : tISD T'), D' = cmI _a0 g →
      ∀ S',
        S' = {w : subscheme D' | connectedComponent w ⊆
            preimage D'.subschemeι.base (g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} →
        ∀ hop', m86 D'.subscheme →
          openSubschemeKer D' ⟨S', hop'⟩ =
            cmI (openSubschemeKer _a0 ⟨divisorComponentsInOrderLocus T j hj, hopen⟩) g := by
    rintro D' rfl S' rfl hop' hNN
    let D := _a0
    let A := orderAtLeastLocus T.ideal T.mult
    let hN' := hNN
    let hopen' := hop'
    have := noetherianSpace_boundary_subscheme T hV j hj
    have := hN'
    exact openSubschemeKer_comap g D A hcl ⟨_, hopen⟩ ⟨_, hopen'⟩ rfl rfl
      (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset D.subscheme
        (D.subschemeι.base ⁻¹' A))
      (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
        (cmI D g).subscheme
        ((cmI D g).subschemeι.base ⁻¹' (pIm g.base A))) hirr
  have hset :=
    let _a1 := bget' hj'
    congrArg (fun A =>
      {w : subscheme _a1 | connectedComponent w ⊆
        preimage _a1.subschemeι.base A}) hcs
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen, containedComponentsIdeal_eq_openSubschemeKer T' j hj' hopen']
  exact key _ hD _ hset hopen' hN'

section
variable (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible)
include hV
theorem containedComponentsIdeal_pullbackAlong_of_smooth Y
    q (h : Y ⟶ T.scheme) [Smooth h]
    (hq : h ≫ T.structMap = q) (hV' : (T.pbA q h).IsAdmissible) j
    (hj : j < T.boundary.length) (hj' : j < (T.pbA q h).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.pbA q h) j hj' =
      (DivisorReduction.ccI hj).comap h := by
  have := hV.charZero
  have := hV.smooth
  have hfl : Flat h := inferInstance
  let _a0 := T.pbA q h
  exact containedComponentsIdeal_comap_of_flat T _a0 hV hV' h hfl j hj hj' (get_eq_comap_get_of_eq_map h T.boundary _a0.boundary (pullbackAlong_boundary T Y q h) j hj hj') (DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq T.mult) $ isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult

theorem containedComponentsIdeal_baseChange (L : Type) [Field L]
    [CharZero L] f (hV' : (T.bc f).IsAdmissible) j
    (hj : j < T.boundary.length) (hj' : j < (T.bc f).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.bc f) j hj' =
      (DivisorReduction.ccI hj).comap
        (pullback.fst T.structMap $ specMapOfFieldHom T.base L f) := by
  have := hV.charZero
  have := hV.smooth
  let _a0 := pullback.fst T.structMap $ specMapOfFieldHom T.base L f
  exact containedComponentsIdeal_comap_of_flat T (bcT T f) hV hV'
    _a0 (flat_fieldBaseChangeProjection T L f) j hj hj' (get_eq_comap_get_of_eq_map _a0 T.boundary (bcT T f).boundary (baseChange_boundary T L f) j hj hj') (orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal T.mult) $ isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
end





namespace DivisorReduction

theorem containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf
    (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) j (hj : j < T.boundary.length)
    (J : (T.bget j hj).subscheme.IdealSheafData)
    (hm : T.mult = 1)
    (hlow : (T.withSchemeIdealBoundary (T.bget j hj).subscheme
        (subschemeι (T.bget j hj) ≫ T.structMap) J
        (map (fun D => D.comap (T.bget j hj).si)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hpush : T.ideal = imageIdealSheaf (T.bget j hj).si J) :
    DivisorReduction.ccI hj = ⊤ := by
  let _a0 := divisorComponentsInOrderLocus T j hj
  let _c0 := bget' hj
  by_cases h : IsOpen _a0
  have hnz := hlow.nonzeroOnComponents
  have hcomap : T.ideal.comap _c0.si = J := by
    rw [hpush]
    exact p30 _ J
  have hsub : ∀ y,
      siI _c0 y ∈ T.ideal.support →
      y ∈ spI J := by
    intro y hy
    have h1 := mpr_ (one_le_orderAt_iff_mem_support T.ideal
      (siI _c0 y)) hy
    have h2 := orderAt_le_orderAt_comap _c0.si T.ideal y
    rw [hcomap] at h2
    exact mp_ (one_le_orderAt_iff_mem_support J y) $ le_trans h1 h2
  have hempty : _a0 = ∅ := by
    ext x
    refine ⟨fun hx => ?_, fun hx => (mp_ (mem_empty_iff_false x) hx).elim⟩
    exfalso
    obtain ⟨C, hCpre, hxC, hCmax⟩ :=
      exists_preirreducible ({x} : CSet _c0.subscheme)
        isIrreducible_singleton.2
    have hxC' := hxC rfl
    refine hnz C ⟨⟨⟨x, hxC'⟩, hCpre⟩, fun u hu hCu => le_of_eq $ hCmax u hu.2 hCu⟩ ?_
    intro y hyC
    have h1 := hx $ hCpre.isPreconnected.subset_connectedComponent hxC' hyC
    rw [hm] at h1
    exact hsub y $ mp_ (mem_orderAtLeastLocus_one_iff T.ideal _) h1
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
    eq_top_iff_support_eq_empty,
    support_openSubschemeKer _c0 ⟨_a0, h⟩
      (isClosed_divisorComponentsInOrderLocus T hV j hj), image_eq_empty]
  exact hempty
  exact EmbeddedResolution.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

end DivisorReduction





namespace DivisorReduction

private theorem isDerivBalanced_of_isBalanced (T : MarkedIdealWithBoundary)
    (h : LocallyOfFiniteType T.structMap) (hbal : T.IsBalanced h) :
    IsDerivBalanced T.base T.structMap T.ideal T.mult := hbal

private theorem mem_support_of_mem_support_comap {X Y : Sch} (f : Y ⟶ X)
    (I : ISD X) {y : ↥Y} (hy : y ∈ support (I.comap f)) : f y ∈ support I := by
  rwa [m19] at hy

section
variable (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible)
include hV
section
variable (j) (hj : j < T.boundary.length)
theorem disjoint_irreducibleComponents_boundary_subscheme :
    ∀ C1_ ∈ irreducibleComponents ↥(T.bget j hj).subscheme,
      ∀ C2_ ∈ irreducibleComponents ↥(T.bget j hj).subscheme,
        C1_ ≠ C2_ → Disjoint C1_ C2_ := by
  have h := irreducibleComponentsDisjointOfSmooth
  unfold IrreducibleComponentsDisjointOfSmooth at h
  exact h T.base _ _ $ (mp_ (isSmoothDivisor_iff T.structMap $ bget' hj) $ isSmoothDivisor_boundary_get T hV j hj).2

private theorem containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup :
    DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * DivisorReduction.lowerIdealAfterBlowup T j hj = T.ideal := by
  simpa [DivisorReduction.lowerIdealAfterBlowup, exceptionalIdeal_id,
    comap_id] using (pow_mul_residualByPow T.ideal (p44 T j hj) T.mult $ exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
end

section
variable (hOB : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (j) (hj : j < T.boundary.length)
include hOB hbal
theorem nonzeroOnComponents_comap_lowerIdealAfterBlowup :
    NonzeroOnComponents
      ((lI hj).comap (T.bget j hj).si) := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have :=
    EmbeddedResolution.noetherianSpace_boundary_subscheme T hV j hj
  have horder : ∀ x, orderAt T.ideal x =
      tMu T * orderAt (p28 hj) x +
        orderAt (p21 hj) x := by
    intro x
    rw [← containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup T hV j hj, orderAt_mul T.base T.structMap, orderAt_pow T.base T.structMap]
  rw [nonzeroOnComponents_iff]
  intro C hC hsub
  obtain ⟨x, hx⟩ := hC.1.1
  by_cases hcase : ∀ y ∈ C, siI (bgetT hj) y ∈ orderAtLeastLocus T.ideal T.mult
  have hsep := disjoint_irreducibleComponents_boundary_subscheme T hV j hj
  have hcc :=
    connectedComponent_subset_of_mem_irreducibleComponents hsep hC hx
  have hxrel : x ∈ divisorComponentsInOrderLocus T j hj := by
    intro z hz
    exact hcase z $ hcc hz
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  let _a0 := siI (bgetT hj) x
  have hZsupp : _a0 ∈
      (DivisorReduction.ccI hj).support := by
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen]
    have hmem : _a0 ∈
        (spI (openSubschemeKer (bget' hj)
          ⟨divisorComponentsInOrderLocus T j hj, hopen⟩) : CSet T.scheme) := by
      rw [support_openSubschemeKer _ _ $ isClosed_divisorComponentsInOrderLocus T hV j hj]
      exact ⟨x, hxrel, rfl⟩
    exact hmem
  have hxsupp :=
    mem_support_of_mem_support_comap _ _ $ hsub hx
  have h1 :=
    (one_le_orderAt_iff_mem_support _ _).mpr hxsupp
  have h2 :=
    (one_le_orderAt_iff_mem_support _ _).mpr hZsupp
  have h3 : (tMu T : ENat) + 1 ≤ orderAt T.ideal _a0 := by
    calc (tMu T : ENat) + 1 = (tMu T : ENat) * 1 + 1 := by rw [mul_one]
      _ ≤ (tMu T : ENat) * orderAt (p28 hj)
            _a0 +
          orderAt (p21 hj)
            _a0 := by
        gcongr
      _ = orderAt T.ideal _a0 := sy_ $ horder _
  have h4 : orderAt T.ideal _a0 ≤ tMu T :=
    (hOB _)
  have h6 : tMu T + 1 ≤ tMu T := by exact_mod_cast (le_trans h3 h4)
  omega
  push Not at hcase
  obtain ⟨y, hyC, hy⟩ := hcase
  have hy0 : orderAt T.ideal (siI (bgetT hj) y) = 0 := by
    rcases orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced T.base T.structMap T.ideal T.mult
      (isDerivBalanced_of_isBalanced T hV.locallyOfFiniteType hbal)
      (siI (bgetT hj) y) with h | h
    exact h
    exact absurd (mpr_ (mem_orderAtLeastLocus_iff T.ideal T.mult _) h) hy
  have hle : orderAt (p21 hj)
      (siI (bgetT hj) y) ≤ 0 := by simp_all
  have hmem :=
    mem_support_of_mem_support_comap _ _ $ hsub hyC
  rw [← one_le_orderAt_iff_mem_support, le_antisymm hle zero_le] at hmem
  simp at hmem

theorem isAdmissible_restrictTwistedToDivisor (_hZ : DivisorReduction.ccI hj ≠ ⊤) :
    (DivisorReduction.rTD hj).IsAdmissible := by
  let _c0 := siI (bgetT hj) ≫ tMp T
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have := hV.smooth
  have hsm :=
    (mp_ (isSmoothDivisor_iff T.structMap $ bget' hj)
      (isSmoothDivisor_boundary_get T hV j hj)).2
  have := hsm
  have hlft : LocallyOfFiniteType
      _c0 := inferInstance
  have hqc : QuasiCompact
      _c0 := inferInstance
  exact
    { charZero := hV.charZero
      locallyOfFiniteType := hlft
      nonzeroOnComponents := nonzeroOnComponents_comap_lowerIdealAfterBlowup T hV hOB hbal j hj
      one_le_mult := hV.one_le_mult
      quasiCompact := hqc
      smooth := hsm
      snc := DivisorReductionBoundary.inStrictNormalCrossingPosition_comap_lowerBoundaryAfterBlowup T hV j hj }
end
end

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end
end
