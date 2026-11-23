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
import Bundle12
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace CategoryTheory.Limits
open Category (assoc comp_id id_comp)
open FunctorialResolution.Blowup (StrictTransformIsBlowupOfClosedSubscheme comap_eq_top_of_notMem_support comap_ker_comp_of_isOpenImmersion exceptionalIdeal_eq_comap idealSheafData_ext_coprod ker_comp_coprod_inl_comap_inl ker_comp_coprod_inl_comap_inr noetherianSpace_toScheme strictTransformImmersion strictTransformImmersion_eq strictTransform_eq_ker)
open FunctorialResolution.EmbeddedResolution (apply_mem_irreducibleComponent_iff_of_flat closedPreimage comap_io_eq_top_of_disjoint comap_ker_subschemeio_comp comap_le_strictTransform comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq effectiveCartierSupportContainsNoComponent inducedBlowups_transitionMap irreducibleComponentsDisjointOfSmooth isClopen_of_mem_irreducibleComponents_of_smooth isOpen_sUnion_of_subset_irreducibleComponents nonzeroOnComponents_comap_iso_hom nonzeroOnComponents_iff nonzeroOnComponents_of_pow_mul_eq_comap orderAt_comap_of_isOpenImmersion orderAt_vanishingIdeal_eq_one_of_not_isField smooth_subschemeio_vanishingIdeal_comp_of_isClopen strictTransform_eq_ker_restrict support_comap support_strictTransform_eq_closure_preimage)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (blowupMorphism_eq_transitionMap center isomorphic_refl projectionToBase projectionToBase_succ projectionToBase_zero pullbackTransitionMap_comp_fst pullbackTransitionMap_comp_snd schemeAt transitionMap_comp_projectionToBase withoutIsoBlowups_center_ne_top withoutIsoBlowups_length)
open IsClosedImmersion (isIso_iff_ker_eq_bot isIso_lift isIso_of_ker_eq lift lift_fac of_isPreimmersion of_surjective_of_isAffine)
open Nat (cast_injective le_induction le_of_succ_le le_succ_of_le lt_of_succ_le lt_succ_iff_lt_or_eq lt_succ_of_lt lt_succ_self succ_le_of_lt zero_le)
open QuasiSober (sober)
open Scheme.IdealSheafData (coe_support_vanishingIdeal comap_comp comap_id comap_mono comap_ofIdealTop comap_sup comap_ι_comp_eq_of_comap_ι_eq eq_top_iff_support_eq_empty equivOfIsAffine equivOfIsAffine_apply equivOfIsAffine_symm_apply ideal_comap_of_isOpenImmersion ideal_mul ideal_ofIdeals_le ideal_sup isReduced_subscheme_vanishingIdeal ker_subschemeι le_map_iff_comap_le le_ofIdeals_iff le_radical ofIdealTop ofIdeals range_subschemeι subschemeMap_subschemeι support support_antitone support_eq_bot_iff support_eq_top_iff vanishingIdeal vanishingIdeal_support)
open Set (disjoint_left eq_univ_of_univ_subset image_mono image_preimage_eq image_preimage_eq_inter_range image_preimage_eq_of_subset image_singleton image_subset_iff image_subset_range image_univ inter_eq_self_of_subset_left mem_biUnion mem_empty_iff_false mem_iUnion mem_image mem_image_of_mem mem_preimage mem_range mem_range_self mem_sUnion mem_sdiff_of_mem mem_union preimage preimage_compl preimage_image_eq range range_comp range_eq_empty sUnion_eq_biUnion sUnion_insert sdiff_subset singleton_subset_iff)
open TopologicalSpace (Closeds)
noncomputable section
open CommRingCat (hom_comp id_apply)
open Equiv (apply_symm_apply symm_apply_apply ulift)
open Finset (coe_insert coe_univ induction_on le_sup mem_coe mem_erase mem_insert_of_mem mem_insert_self mem_univ prod_congr prod_eq_zero prod_ne_zero_iff sum_eq_single_of_mem univ)
open Function (Injective Surjective)
open FunctorialResolution.Blowup (exceptionalIdeal strictTransform)
open FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData (centersLieOverSingularLocus_of_inducedCentersLieOverSingularLocus coe_discardedLocusClosure detachedToBase_def discardedIdeal_eq_vanishingIdeal discardedLocus_eq_sUnion_discardedComponents ofAffine schemeAtToSpec_def strictTransformToZero_succ strictTransformToZero_zero strictTransformZeroToBase_comp strictTransformZeroToBase_def)
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence (DetachedLocusIsOpen comapAmbientCenter_eq detachedLocus_eq_sUnion exists_irreducibleComponent_isGenericPoint_strictTransformMap inducedBlowups_center inducedBlowups_length isBlowupAlongIdealSheaf_coprod_desc_centerOffDetached isBlowupAlongIdealSheaf_totalTransition_of_coprod_desc mem_detachedComponents noetherianSpace_strictTransform_of_isNoetherian strictTransformIdeal_succ strictTransformIdeal_zero strictTransformMap_comp_strictTransformio strictTransformio)
open Ideal (comap radical_mono span span_union)
open IsOpenImmersion (isoOfRangeEq isoOfRangeEq_hom_fac)
open IsPullback (isoPullback_hom_fst isoPullback_hom_snd of_hasPullback of_horiz_isIso of_isLimit of_iso_pullback)
open IsZariskiLocalAtSource (mk' sigmaDesc)
open Limits.Sigma (desc hom_ext map)
open List (get get_mem length mem_append mem_cons mem_map mem_singleton)
open MorphismProperty (RespectsIso RespectsLeft RespectsRight comp_mem isomorphisms)
open Nat (le_succ lt_succ_iff not_lt_zero)
open Opposite (op)
open Or (inr)
open Scheme (GSpecIso IdealSheafData basicOpen_of_isUnit basicOpen_zero hom_inv_apply homeoOfIso inv_hom_apply preimage_basicOpen range_fromSpecStalk)
open Scheme.Hom (app appLE appTop comp_appTop comp_apply id_appTop isClosedEmbedding isOpenEmbedding ker ker_comp mem_smoothLocus pre range_comp_base smoothLocus_eq_top_iff stalkMap stalkMap_comp support_ker toImage toImage_imageι)
open Set (mem_singleton_iff subset_sUnion_of_mem)
open Set.Finite (isClosed_biUnion mem_toFinset)
open SmoothOfRelativeDimension (smooth)
open Sum (elim inl)
open TopologicalSpace (NoetherianSpace)
open TopologicalSpace.NoetherianSpace (finite_irreducibleComponents isCompact)
open TopologicalSpace.Opens (coe_bot coe_iSup coe_top isBasis_iff_nbhd mem_iSup)
open Topology (IsClosedEmbedding IsOpenEmbedding)
open ULift (up up_down)
section
open AlgebraicGeometry (Etale IsAffine IsReduced LocallyOfFiniteType QuasiCompact SmoothOfRelativeDimension isAffineOpen_top)
open Eq (symm)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (boundary)


namespace FunctorialResolution.EmbeddedResolution


variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]

structure ChartPushforward (S S' : EmbeddedBlowupSequence k Y pY) where
  ambientMap : S.ambient ⟶ S'.ambient
  emb_ambientMap : S.emb ≫ ambientMap = S'.emb
  len_eq : S.length = S'.length
  levelMap : ∀ i : ℕ, i ≤ S'.length → (S.schemeAt i ⟶ S'.schemeAt i)
  isClosedImmersion_levelMap :
    ∀ i hi, IsClosedImmersion $ levelMap i hi
  levelMap_zero :
    levelMap 0 (zero_le _) ≫ S'.ambientSeq.isoZero.hom =
      S.ambientSeq.isoZero.hom ≫ ambientMap
  levelMap_blowdown :
    ∀ (i : ℕ) (hi : i < S'.length),
      levelMap (i + 1) hi ≫ S'.blowdown i = S.blowdown i ≫ levelMap i hi.le
  ambientCenter_eq :
    ∀ (i : ℕ) (hi : i < S'.length),
      S'.ambientCenter i = imageIdealSheaf (levelMap i hi.le) (S.ambientCenter i)
  ker_levelMap_succ :
    ∀ (i : ℕ) (hi : i < S'.length),
      (levelMap (i + 1) hi).ker =
        strictTransform (S'.blowdown i) (S'.ambientCenter i) (levelMap i hi.le).ker

namespace ChartPushforward

section

variable {S S' : EmbeddedBlowupSequence k Y pY}


instance instIsClosedImmersionLevelMap (P : ChartPushforward S S') (i : ℕ) (hi : i ≤ S'.length) :
    IsClosedImmersion $ P.levelMap i hi :=
  P.isClosedImmersion_levelMap i hi

theorem le_length (P : ChartPushforward S S') {i} (hi : i ≤ S'.length) : i ≤ S.length :=
  hi.trans_eq P.len_eq.symm

end

section

variable (S S' : EmbeddedBlowupSequence k Y pY) (f)
  [IsClosedImmersion f]

def ofIsPushforwardSeq (hemb : S.emb ≫ f = S'.emb)
    (h : IsPushforwardBlowupSeq f S.ambientSeq S'.ambientSeq) : ChartPushforward S S' where
  ambientMap := f
  emb_ambientMap := hemb
  len_eq := h.1
  levelMap := fun i hi => h.2.choose i $ hi.trans_eq h.1.symm
  isClosedImmersion_levelMap := fun i hi => (h.2.choose_spec.1 i $ hi.trans_eq h.1.symm)
  levelMap_zero := by
    exact h.2.choose_spec.2.1
  levelMap_blowdown := fun i hi => (h.2.choose_spec.2.2.1 i $ hi.trans_eq h.1.symm)
  ambientCenter_eq := fun i hi => (h.2.choose_spec.2.2.2.1 i $ hi.trans_eq h.1.symm)
  ker_levelMap_succ := fun i hi => (h.2.choose_spec.2.2.2.2 i $ hi.trans_eq h.1.symm)


end

section

variable {S S' : EmbeddedBlowupSequence k Y pY}

theorem map_strictTransformIdeal_levelMap {T T' : EmbeddedBlowupSequence k Y pY}
    (P : ChartPushforward T T') i :
    ∀ hi, (T.strictTransformIdeal i).map (P.levelMap i hi) = T'.strictTransformIdeal i := by
  induction i with
  | zero =>
    intro hi
    have key : T.ambientSeq.isoZero.inv ≫ P.levelMap 0 hi
        = P.ambientMap ≫ T'.ambientSeq.isoZero.inv := by
      rw [Iso.inv_comp_eq, ← assoc, ← P.levelMap_zero, assoc,
        m145, comp_id]
    rw [strictTransformIdeal_zero, strictTransformIdeal_zero, ← ker_comp, assoc, key, ← assoc, P.emb_ambientMap]
  | succ n ih =>
    intro hi
    have hn := lt_of_succ_le hi
    have :=
      T.isNoetherian_schemeAt (n + 1) (P.le_length hi)
    have :=
      T'.isNoetherian_schemeAt (n + 1) hi
    let _a0 := P.levelMap n hn.le
    have hcenter : (T.ambientCenter n).map _a0 = T'.ambientCenter n := by
      rw [map_eq_ker_subschemeio_comp, P.ambientCenter_eq n hn, imageIdealSheaf_eq_ker]
    let _a1 := P.levelMap (n + 1) hi
    have hker : m149 _a1
        = p6 (T'.blowdown n) ((T.ambientCenter n).map _a0)
            (m149 _a0) := by
      rw [hcenter]
      exact P.ker_levelMap_succ n hn
    have hmain := map_strictTransform_eq_strictTransform_map _a0
      (T.ambientCenter n) (T.strictTransformIdeal n) (T.blowdown n) (T'.blowdown n)
      _a1 (P.levelMap_blowdown n hn) hker
    rw [strictTransformIdeal_succ, strictTransformIdeal_succ, hmain, ih hn.le, hcenter]

section
variable (P : ChartPushforward S S')
section
variable (i : ℕ)
section
variable (hi : i ≤ S'.length)
theorem exists_strictTransform_iso :
    ∃ e : S.strictTransform i ≅ S'.strictTransform i,
      e.hom ≫ S'.strictTransformio i = S.strictTransformio i ≫ P.levelMap i hi := by
  have hA : ker (S.strictTransformio i) = S.strictTransformIdeal i := by simp_all
  have hA' : ker (S'.strictTransformio i) = S'.strictTransformIdeal i := by simp_all
  let _m0 := S.strictTransformio i ≫ P.levelMap i hi
  have : IsClosedImmersion _m0 := inferInstance
  have hker : ker (S'.strictTransformio i) = _m0.ker := by
    rw [ker_comp, hA, hA', map_strictTransformIdeal_levelMap P i hi]
  have := isIso_lift (S'.strictTransformio i)
    _m0 hker
  refine ⟨asIso $ lift (S'.strictTransformio i)
    _m0 $ le_of_eq hker, ?_⟩
  rw [asIso_hom, lift_fac]

def strictTransformIso :
    S.strictTransform i ≅ S'.strictTransform i :=
  (P.exists_strictTransform_iso i hi).choose

@[reassoc (attr := simp)]
theorem strictTransformIso_hom_comp_strictTransformio :
    (P.strictTransformIso i hi).hom ≫ S'.strictTransformio i = S.strictTransformio i ≫ P.levelMap i hi :=
  (P.exists_strictTransform_iso i hi).choose_spec
end

@[reassoc]
theorem strictTransformIso_hom_comp_strictTransformMap (hi : i < S'.length) :
    (P.strictTransformIso (i + 1) hi).hom ≫ S'.strictTransformMap i =
      S.strictTransformMap i ≫ (P.strictTransformIso i hi.le).hom := by
  rw [← cancel_mono $ S'.strictTransformio i]
  simp only [assoc]
  rw [strictTransformIso_hom_comp_strictTransformio P i hi.le, strictTransformMap_comp_strictTransformio S' i, ← assoc,
    strictTransformIso_hom_comp_strictTransformio P (i + 1) hi, assoc, P.levelMap_blowdown i hi,
    ← assoc, ← strictTransformMap_comp_strictTransformio S i, assoc]
end

theorem strictTransformIso_zero_hom_comp_strictTransformZeroIso_hom :
    (P.strictTransformIso 0 $ zero_le _).hom ≫ S'.strictTransformZeroIso.hom = S.strictTransformZeroIso.hom := by
  refine mp_ (cancel_mono S'.emb) ?_
  calc (isoH (P.strictTransformIso 0 $ zero_le _) ≫ S'.strictTransformZeroIso.hom) ≫ S'.emb
      = isoH (P.strictTransformIso 0 $ zero_le _) ≫ (S'.strictTransformZeroIso.hom ≫ S'.emb) := by
        rw [assoc]
    _ = isoH (P.strictTransformIso 0 $ zero_le _) ≫ (S'.strictTransformio 0 ≫ S'.ambientSeq.isoZero.hom) := by
        rw [S'.strictTransformZeroIso_hom_emb]
    _ = (isoH (P.strictTransformIso 0 $ zero_le _) ≫ S'.strictTransformio 0) ≫ S'.ambientSeq.isoZero.hom := by
        rw [assoc]
    _ = (S.strictTransformio 0 ≫ P.levelMap 0 (zero_le _)) ≫ S'.ambientSeq.isoZero.hom := by
        rw [P.strictTransformIso_hom_comp_strictTransformio 0 $ zero_le _]
    _ = S.strictTransformio 0 ≫ (P.levelMap 0 (zero_le _) ≫ S'.ambientSeq.isoZero.hom) := by
        rw [assoc]
    _ = S.strictTransformio 0 ≫ (S.ambientSeq.isoZero.hom ≫ P.ambientMap) := by
        rw [P.levelMap_zero]
    _ = (S.strictTransformio 0 ≫ S.ambientSeq.isoZero.hom) ≫ P.ambientMap := by
        rw [assoc]
    _ = (S.strictTransformZeroIso.hom ≫ S.emb) ≫ P.ambientMap := by
        rw [S.strictTransformZeroIso_hom_emb]
    _ = S.strictTransformZeroIso.hom ≫ (S.emb ≫ P.ambientMap) := by
        rw [assoc]
    _ = S.strictTransformZeroIso.hom ≫ S'.emb := by
        rw [P.emb_ambientMap]
end

theorem range_subset_range_of_ker_le {U V W : Sch} (f : U ⟶ W) (g : V ⟶ W)
    [IsClosedImmersion f] [IsClosedImmersion g]
    (hle : ker g ≤ ker f) :
    range ⇑f ⊆ range ⇑g := by
  obtain ⟨e, he⟩ : ∃ e : U ⟶ V, e ≫ g = f :=
    ⟨lift g f hle, by rw [lift_fac]⟩
  rintro y ⟨x, rfl⟩
  refine ⟨bsM e x, ?_⟩
  have hx : (e ≫ g) x = f x := by rw [he]
  exact hx

theorem support_ker_eq_range {U W : Sch} (h : U ⟶ W)
    [IsClosedImmersion h] :
    (support (ker h) : Set ↥W) = range ⇑h := by
  have hker : m149 (siI $ m149 h) = m149 h :=
    q2 _
  rw [← (q5 _)]
  exact m15 (range_subset_range_of_ker_le _ h $ le_of_eq hker.symm)
    (range_subset_range_of_ker_le h _ $ le_of_eq hker)

theorem support_ambientCenter_eq_image (P : ChartPushforward S S') i (hi : i < S'.length) :
    ((S'.ambientCenter i).support : CSet $ S'.schemeAt i) =
      ⇑(P.levelMap i hi.le) '' ((S.ambientCenter i).support : CSet $ S.schemeAt i) := by
  have hJ := P.ambientCenter_eq i hi
  rw [imageIdealSheaf_eq_ker] at hJ
  let _a0 := siI $ S.ambientCenter i
  have hI : (spI (S.ambientCenter i) : CSet $ S.schemeAt i)
      = range _a0 := by
    have h2 := support_ker_eq_range _a0
    rwa [q2] at h2
  have hcomp : (_a0 ≫ P.levelMap i hi.le)
      = (P.levelMap i hi.le) ∘ _a0 := rfl
  rw [hJ, support_ker_eq_range, hI, hcomp, range_comp]

end

end ChartPushforward

end FunctorialResolution.EmbeddedResolution

end
section
open Opposite


namespace FunctorialResolution.EmbeddedResolution

theorem exists_isPullback_subschemeio_comap {X X' : Sch} (f : X' ⟶ X)
    (I : ISD X) :
    ∃ g : (I.comap f).subscheme ⟶ I.subscheme,
      g ≫ I.si = (I.comap f).si ≫ f ∧
        IsPullback g (I.comap f).si I.si f := by
  let _a1 := pullback.fst f I.si
  have hker : ker (cmI I f).si
      = m149 _a1 :=
    (q2 _).trans rfl
  let _a0 := cmI I f
  obtain ⟨u, hufac⟩ : ∃ u,
      u ≫ _a1 = siI _a0 :=
    ⟨lift _ _ hker.ge, lift_fac _ _ hker.ge⟩
  obtain ⟨v, hvfac⟩ : ∃ v : pullback f I.si ⟶ subS (cmI I f),
      v ≫ siI _a0 = _a1 :=
    ⟨lift _ _ hker.le, lift_fac _ _ hker.le⟩
  have huv : u ≫ v = 𝟙 _ := by
    apply (cancel_mono (cmI I f).si).1
    rw [assoc, hvfac, hufac, id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply (cancel_mono _a1).1
    rw [assoc, hufac, hvfac, id_comp]
  let _a2 := u ≫ pullback.snd f I.si
  have hw : siI _a0 ≫ f
      = _a2 ≫ siI I := by
    rw [assoc, ← pullback.condition, ← assoc, hufac]
  exact ⟨_a2, sy_ hw, (of_iso_pullback ⟨hw⟩ (⟨u, v, huv, hvu⟩ : subS _a0 ≅ pullback f I.si) hufac rfl).flip⟩

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]
  {k' : Type} [Field k'] [CharZero k'] {Y'} [IsAffine Y']
  {pY'} [LocallyOfFiniteType pY']

namespace EmbeddedBlowupSequence

section
variable (S : EmbeddedBlowupSequence k Y pY)
theorem noetherianSpace_strictTransform (i : ℕ) (hi : i ≤ length S) :
    NoetherianSpace ↥(S.strictTransform i) := by
  have := S.isNoetherian_schemeAt i hi
  exact S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i inferInstance

theorem isReduced_strictTransform [IsReduced Y]
    (i : ℕ) (hi : i ≤ S.length) : IsReduced $ S.strictTransform i :=
  S.isReduced_strictTransform_of_isNoetherian (fun j hj => S.isNoetherian_schemeAt j hj) i hi
end

end EmbeddedBlowupSequence

namespace ChartFlatBaseChange

variable {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

section
variable (F : ChartFlatBaseChange S S')
section
variable (j) (hj : j < S'.length)
theorem mem_support_ambientCenter_iff
    y :
    (S'.strictTransformio j) y ∈ (↑(S'.ambientCenter j).support : CSet $ S'.schemeAt j) ↔
      (S.strictTransformio $ F.reindex j) ((F.strictTransformComparison j hj.le) y) ∈
        (↑(S.ambientCenter $ F.reindex j).support : Set ↥(S.schemeAt $ F.reindex j)) := by
  have hcomp : (S.strictTransformio $ F.reindex j) ((F.strictTransformComparison j hj.le) y)
      = (F.levelMap j hj.le) ((S'.strictTransformio j) y) :=
    congrArg (fun f : S'.strictTransform j ⟶ S.schemeAt (F.reindex j) => f y)
      (F.strictTransformComparison_comp_strictTransformio j hj.le)
  rw [F.center_eq j hj, support_comap, mem_preimage, hcomp]

theorem detachedLocus_eq_preimage :
    S'.detachedLocus j =
      (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        S.detachedLocus (F.reindex j) := by
  let _a2 := F.strictTransformComparison j hj.le
  have := F.flat_strictTransformComparison j hj.le
  have himg := F.mem_support_ambientCenter_iff j hj
  let _a0 := S.strictTransformio $ F.reindex j
  let _a1 := S.ambientCenter $ F.reindex j
  have hclosed : IsClosed
      ((fun z : (S.strictTransform $ F.reindex j) => _a0 z) ⁻¹'
        (_a1.support : Set $ S.schemeAt $ F.reindex j)) := by
    rw [← support_comap]
    exact (cmI _a1 _a0).support.2
  refine Set.ext fun x => ?_
  simp [mem_preimage, S'.detachedLocus_eq_sUnion j, S.detachedLocus_eq_sUnion $ F.reindex j, mem_sUnion]
  constructor
  rintro ⟨C', hC', hxC'⟩
  rw [S'.mem_detachedComponents] at hC'
  obtain ⟨hirr, hsub⟩ := hC'
  refine ⟨closure $ (fun z : (S'.strictTransform j) => _a2 z) '' C', ?_, subset_closure ⟨x, hxC', rfl⟩⟩
  rw [S.mem_detachedComponents]
  refine ⟨closure_image_mem_irreducibleComponents_of_generalizingMap _ (AlgebraicGeometry.Flat.generalizingMap _) hirr, ?_⟩
  rw [image_subset_iff]
  refine closure_minimal ?_ hclosed
  rintro _ ⟨y, hy, rfl⟩
  exact (himg y).1 $ hsub ⟨y, hy, rfl⟩
  rintro ⟨C, hC, hxC⟩
  rw [S.mem_detachedComponents] at hC
  obtain ⟨hirr, hsub⟩ := hC
  obtain ⟨C', hC'irr, hxC', hcl⟩ :=
    (apply_mem_irreducibleComponent_iff_of_flat _a2 hirr x).1 hxC
  refine ⟨C', ?_, hxC'⟩
  rw [S'.mem_detachedComponents]
  refine ⟨hC'irr, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  refine (himg y).2 ?_
  refine hsub ⟨_, ?_, rfl⟩
  rw [← hcl]
  exact subset_closure ⟨y, hy, rfl⟩

theorem coe_detachedClosure_eq_preimage :
    (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j)) =
      (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        (↑(S.detachedClosure $ F.reindex j) : Set ↥(S.strictTransform $ F.reindex j)) := by
  have :=
    S'.noetherianSpace_strictTransform j hj.le
  have :=
    S.noetherianSpace_strictTransform (F.reindex j) $ F.reindex_le_length hj.le
  rw [S'.detachedClosure_coe j, S.detachedClosure_coe $ F.reindex j, F.detachedLocus_eq_preimage j hj]

theorem detachedClosureCompl_eq_preimage :
    S'.detachedClosureCompl j = (F.strictTransformComparison j hj.le) ⁻¹ᵁ (S.detachedClosureCompl $ F.reindex j) := by
  refine m55 ?_
  let _a0 := S.detachedClosureCompl $ F.reindex j
  let _a1 := F.strictTransformComparison j hj.le
  have h2 : ((preU _a1 _a0)
        : Set $ S'.strictTransform j)
      = (fun x : (S'.strictTransform j) => _a1 x) ⁻¹'
        (_a0 : Set $ S.strictTransform $ F.reindex j) := rfl
  rw [S'.detachedClosureCompl_coe j, h2, S.detachedClosureCompl_coe $ F.reindex j, preimage_compl,
    F.coe_detachedClosure_eq_preimage j hj]
end

theorem isEmpty_of_forall_reindex_ne (s : ℕ) (hs : s < S.length)
    (hskip : ∀ j, j < S'.length → F.reindex j ≠ s) (P : Sch)
    (q : P ⟶ S.detachedScheme s) (p : P ⟶ S'.ambient)
    (hcomm : q ≫ S.detachedio s ≫ S.strictTransformio s ≫ S.ambientSeq.projectionToBase s = p ≫ F.ambientMap) :
    IsEmpty ↥P := by
  have : NoetherianSpace $ S.strictTransform s :=
    S.noetherianSpace_strictTransform s hs.le
  constructor
  intro x
  have hcsq : (q ≫ S.detachedio s ≫ S.strictTransformio s) ≫ S.ambientSeq.projectionToBase s = p ≫ F.ambientMap := by simp_all
  have hpb := of_hasPullback (S.ambientSeq.projectionToBase s) F.ambientMap
  let _a1 := pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap
  have hcomap := F.comap_center_skipped s hs hskip
    (pullback (S.ambientSeq.projectionToBase s) F.ambientMap)
    _a1
    (pullback.snd (S.ambientSeq.projectionToBase s) F.ambientMap) hpb
  let _a0 := (S.detachedio s) $ q x
  have hpt : _a1 ((hpb.lift _ _ hcsq) x)
      = (S.strictTransformio s) _a0 :=
    congrArg (fun f => f x) $ hpb.lift_fst _ _ hcsq
  have hfl : _a0 ∈ S.detachedLocus s := by
    have h1 : _a0 ∈ ((S.detachedIdeal s).support : Set $ S.strictTransform s) := by
      rw [← q5]
      exact ⟨q x, rfl⟩
    rw [S.detachedIdeal_eq s] at h1
    have h2 := (coe_support_vanishingIdeal $ S.detachedClosure s).le h1
    rwa [S.detachedClosure_coe s] at h2
  have hmem : (S.strictTransformio s) _a0 ∈
      ((S.ambientCenter s).support : CSet $ S.schemeAt s) :=
    S.image_detachedLocus_subset_ambientCenter_support s ⟨_, hfl, rfl⟩
  have hmem2 := hmem
  rw [← hpt, ← mem_preimage, ← support_comap, hcomap] at hmem2
  simp at hmem2

theorem detachedIdeal_eq_comap [IsReduced Y]
    [IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    S'.detachedIdeal j = (S.detachedIdeal (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have :=
    S'.noetherianSpace_strictTransform j hj.le
  have :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have := S'.isReduced_strictTransform j hj.le
  have := S.isReduced_strictTransform (F.reindex j) $ F.reindex_le_length hj.le
  have := F.flat_strictTransformComparison j hj.le
  have hS :=
    fun C hC => ((S.mem_detachedComponents (F.reindex j) C).1 hC).1
  let _a1 := S.detachedClosure $ F.reindex j
  have hZ : (_a1)
      = ⋃₀ S.detachedComponents (F.reindex j) := by
    rw [S.detachedClosure_coe (F.reindex j)]
    exact S.detachedLocus_eq_sUnion $ F.reindex j
  let _a2 := F.strictTransformComparison j hj.le
  have hZ' : ((S'.detachedClosure j) : Set (S'.strictTransform j))
      = _a2.base ⁻¹' (⋃₀ S.detachedComponents (F.reindex j)) := by
    have h := F.coe_detachedClosure_eq_preimage j hj
    rwa [S.detachedClosure_coe (F.reindex j), S.detachedLocus_eq_sUnion (F.reindex j)] at h
  rw [S'.detachedIdeal_eq j, S.detachedIdeal_eq (F.reindex j)]
  exact sy_ (comap_vanishingIdeal_sUnion _a2
    (S := S.detachedComponents $ F.reindex j) (Z := _a1)
    (Z' := S'.detachedClosure j) hS hZ hZ')

theorem exists_isPullback_detachedScheme [IsReduced Y]
    [IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    ∃ g : S'.detachedScheme j ⟶ S.detachedScheme (F.reindex j),
      g ≫ S.detachedio (F.reindex j) = S'.detachedio j ≫ F.strictTransformComparison j hj.le ∧
        IsPullback g (S'.detachedio j) (S.detachedio $ F.reindex j) (F.strictTransformComparison j hj.le) := by
  let _a0 := S.detachedIdeal $ F.reindex j
  let _a1 := F.strictTransformComparison j hj.le
  have key : ∀ J : ISD $ S'.strictTransform j,
      J = cmI _a0 _a1 →
      ∃ g,
        g ≫ siI _a0 =
            siI J ≫ _a1 ∧
          IsPullback g J.si _a0.si
            _a1 := by
    rintro J rfl
    exact exists_isPullback_subschemeio_comap _ _
  exact key (S'.detachedIdeal j) $ F.detachedIdeal_eq_comap j hj

def detachedSchemeComparison [IsReduced Y]
    [IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    S'.detachedScheme j ⟶ S.detachedScheme (F.reindex j) :=
  (F.exists_isPullback_detachedScheme j hj).choose

section
variable [hv1_0 : IsReduced Y] [hv1_1 : IsReduced Y'] (j) (hj : j < S'.length)
include hv1_0 hv1_1
theorem detachedSchemeComparison_comp_detachedio :
    F.detachedSchemeComparison j hj ≫ S.detachedio (F.reindex j) =
      S'.detachedio j ≫ F.strictTransformComparison j hj.le :=
  (F.exists_isPullback_detachedScheme j hj).choose_spec.1

theorem detachedSchemeComparison_comp_detachedio_assoc {Z : Sch}
    (h : S.strictTransform (F.reindex j) ⟶ Z) :
    F.detachedSchemeComparison j hj ≫ S.detachedio (F.reindex j) ≫ h =
      S'.detachedio j ≫ F.strictTransformComparison j hj.le ≫ h := by
  rw [← assoc, F.detachedSchemeComparison_comp_detachedio j hj, assoc]

theorem isPullback_detachedSchemeComparison :
    IsPullback (F.detachedSchemeComparison j hj) (S'.detachedio j) (S.detachedio $ F.reindex j)
      (F.strictTransformComparison j hj.le) :=
  (F.exists_isPullback_detachedScheme j hj).choose_spec.2
end
end

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
section
open Opposite


namespace FunctorialResolution.EmbeddedResolution

namespace ChartFlatBaseChange

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]
  {k' : Type} [Field k'] [CharZero k'] {Y'} [IsAffine Y']
  {pY'} [LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

private theorem map_eq_ker_subschemeio_comp {X Y : Sch} (f : X ⟶ Y) (I : ISD X) :
    I.map f = ker (I.subschemeι ≫ f) := rfl

section
variable (F : ChartFlatBaseChange S S') (j) (hj : j < S'.length)
theorem comapAmbientCenter_eq_comap :
    S'.comapAmbientCenter j =
      (S.comapAmbientCenter $ F.reindex j).comap (F.strictTransformComparison j hj.le) := by
  let _a1 := F.strictTransformComparison j hj.le
  let _a2 := S.strictTransformio $ F.reindex j
  let _a0 := S.ambientCenter $ F.reindex j
  calc S'.comapAmbientCenter j = cmI (S'.ambientCenter j) (S'.strictTransformio j) := rfl
    _ = cmI (cmI _a0 $ F.levelMap j hj.le) (S'.strictTransformio j) := by
        rw [F.center_eq j hj]
    _ = cmI _a0 (S'.strictTransformio j ≫ F.levelMap j hj.le) := by
        simp [comap_comp]
    _ = cmI _a0
          (_a1 ≫ _a2) := by rw [F.strictTransformComparison_comp_strictTransformio j hj.le]
    _ = cmI (cmI _a0 _a2)
          _a1 := by simp [comap_comp]
    _ = cmI (S.comapAmbientCenter $ F.reindex j) _a1 := rfl

theorem centerOffDetached_eq_comap :
    S'.centerOffDetached j =
      (S.centerOffDetached (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  let _c0 := S.detachedClosureCompl $ F.reindex j
  have hflat := F.flat_strictTransformComparison j hj.le
  have hnoe : NoetherianSpace (S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have hqc : QuasiCompact _c0.ι :=
    ⟨fun _ _ _ => isCompact _⟩
  let _a0 := opI (F.strictTransformComparison j hj.le ⁻¹ᵁ S.detachedClosureCompl (F.reindex j))
  have hpb : IsPullback (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j))
      _a0
      _c0.i (F.strictTransformComparison j hj.le) :=
    m226 _ _
  let _a1 := cmI (S.comapAmbientCenter (F.reindex j)) _c0.i
  have key := comap_map_eq_map_comap_of_isPullback hpb
      _a1
  have hcomap :
      _a1.comap
          (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j))
        = (S'.comapAmbientCenter j).comap
            _a0 := by
    rw [F.comapAmbientCenter_eq_comap j hj, ← comap_comp, ← comap_comp, hpb.w]
  rw [S'.centerOffDetached_eq j, S.centerOffDetached_eq $ F.reindex j,
    ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subschemeio_comp (S'.detachedClosureCompl j).i, ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subschemeio_comp _c0.i,
    F.detachedClosureCompl_eq_preimage j hj, key, hcomap]
end

end ChartFlatBaseChange





namespace ChartPushforward

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]
  {S S' : EmbeddedBlowupSequence k Y pY}

theorem mem_irreducibleComponents_iff_image {al_ be_ : Type} [TopologicalSpace al_]
    [TopologicalSpace be_] f g (hf : Continuous f) (hg : Continuous g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) C :
    C ∈ irreducibleComponents al_ ↔ f '' C ∈ irreducibleComponents be_ := by
  have hinj : Injective f := by
    intro a b hab
    have h := congrArg g hab
    rwa [hgf, hgf] at h
  have hirrf : ∀ s, IsIrreducible s → IsIrreducible (imS f s) := fun s hs =>
    hs.image f hf.continuousOn
  have hirrg : ∀ t, IsIrreducible t → IsIrreducible (imS g t) := fun t ht =>
    ht.image g hg.continuousOn
  have himg : imS g (f '' C) = C := by
    apply m15
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rwa [hgf]
    intro x hx
    exact ⟨f x, ⟨x, hx, rfl⟩, hgf x⟩
  constructor
  intro hC0
  have hC := hC0
  show IsIrreducible (imS f C) ∧ ∀ ⦃b : Set be_⦄, IsIrreducible b → imS f C ≤ b → b ≤ imS f C
  refine ⟨hirrf C hC.1, ?_⟩
  intro t ht hsub
  intro y hy
  exact ⟨g y, (an2 hC (hirrg t ht) fun x hx => ⟨f x, hsub ⟨x, hx, rfl⟩, hgf x⟩) ⟨y, hy, rfl⟩, hfg y⟩
  intro hC0
  have hC := hC0
  show IsIrreducible C ∧ ∀ ⦃b : Set al_⦄, IsIrreducible b → C ≤ b → b ≤ C
  constructor
  have h1 := hirrg _ hC.1
  rwa [himg] at h1
  intro t ht hsub
  have himt : imS f C ⊆ imS f t := by simp_all
  intro x hx
  obtain ⟨x', hx', hxx⟩ := (an2 hC (hirrf t ht) himt) ⟨x, hx, rfl⟩
  rwa [← hinj hxx]

theorem sUnion_eq_image_sUnion {al_ be_ : Type} (f : al_ → be_)
    (hf : Surjective f) (A : Set $ Set al_) (B : Set $ Set be_)
    (h : ∀ C : Set al_, C ∈ A ↔ f '' C ∈ B) :
    ⋃₀ B = f '' (⋃₀ A) := by
  apply m15
  rintro x ⟨D, hD, hxD⟩
  obtain ⟨y, rfl⟩ := hf x
  refine ⟨y, ⟨preimage f D, ?_, hxD⟩, rfl⟩
  refine mpr_ (h $ preimage f D) ?_
  rwa [image_preimage_eq D hf]
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨C, hC, hyC⟩ := hy
  exact ⟨imS f C, mp_ (h C) hC, ⟨y, hyC, rfl⟩⟩

section
variable (P : ChartPushforward S S')
section
variable (i) (hi : i < S'.length)
theorem mem_detachedComponents_iff
    (C : Set ↥(S.strictTransform i)) :
    C ∈ S.detachedComponents i ↔
      ⇑((P.strictTransformIso i hi.le).hom) '' C ∈ S'.detachedComponents i := by
  let _a0 := isoH $ P.strictTransformIso i hi.le
  have hgf := fun x =>
    hom_inv_apply (P.strictTransformIso i hi.le) x
  have hfg := fun y =>
    inv_hom_apply (P.strictTransformIso i hi.le) y
  have hcomm := fun x =>
    congrArg (fun g : S.strictTransform i ⟶ S'.schemeAt i => bsM g x)
      (P.strictTransformIso_hom_comp_strictTransformio i hi.le)
  have hsupp := P.support_ambientCenter_eq_image i hi
  simp only [mem_detachedComponents]
  refine and_congr (mem_irreducibleComponents_iff_image (_a0)
    (isoI $ P.strictTransformIso i hi.le) (P.strictTransformIso i hi.le).hom.base.hom.continuous
    (P.strictTransformIso i hi.le).inv.base.hom.continuous hgf hfg C) ?_
  constructor
  intro h z hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨x, hxC, rfl⟩ := hy
  rw [hsupp]
  exact ⟨bsM (S.strictTransformio i) x, h ⟨x, hxC, rfl⟩, sy_ $ hcomm x⟩
  intro h z hz
  obtain ⟨x, hxC, rfl⟩ := hz
  have hmem :=
    h ⟨bsM _a0 x, ⟨x, hxC, rfl⟩, rfl⟩
  rw [hsupp] at hmem
  obtain ⟨w, hw, hweq⟩ := hmem
  rwa [((isClosedEmbedding $ P.levelMap i hi.le).injective) $ tr_ hweq $ hcomm x] at hw

theorem detachedLocus_eq_image :
    S'.detachedLocus i = ⇑((P.strictTransformIso i hi.le).hom) '' S.detachedLocus i := by
  rw [S'.detachedLocus_eq_sUnion i, S.detachedLocus_eq_sUnion i]
  exact sUnion_eq_image_sUnion _ ((homeoOfIso $ P.strictTransformIso i hi.le).surjective) _ _
    (P.mem_detachedComponents_iff i hi)

theorem coe_detachedClosure_eq_image :
    (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      ⇑((P.strictTransformIso i hi.le).hom) '' (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  have h1 : ((S'.detachedClosure i) : Set $ S'.strictTransform i) = closure (S'.detachedLocus i) := rfl
  have h2 : ((S.detachedClosure i) : Set $ S.strictTransform i) = closure (S.detachedLocus i) := rfl
  rw [h1, h2, P.detachedLocus_eq_image i hi]
  exact sy_ $ (homeoOfIso $ P.strictTransformIso i hi.le).image_closure $ S.detachedLocus i

theorem preimage_coe_detachedClosure :
    ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  rw [P.coe_detachedClosure_eq_image i hi]
  exact preimage_image_eq _ (homeoOfIso $ P.strictTransformIso i hi.le).injective
end

theorem comap_detachedIdeal [IsReduced Y] i
    (hi : i < S'.length) :
    (S'.detachedIdeal i).comap (P.strictTransformIso i hi.le).hom = S.detachedIdeal i := by
  have hn' :=
    S'.noetherianSpace_strictTransform i hi.le
  have hn :=
    S.noetherianSpace_strictTransform i (P.le_length hi.le)
  have hr' :=
    S'.isReduced_strictTransform i hi.le
  have hr :=
    S.isReduced_strictTransform i (P.le_length hi.le)
  let _a0 := P.strictTransformIso i hi.le
  have hfl : Flat _a0.hom := inferInstance
  have hS : S'.detachedComponents i ⊆ irreducibleComponents (S'.strictTransform i) :=
    fun C hC => an1 (mp_ (S'.mem_detachedComponents i C) hC)
  have hZ :=
    (S'.detachedClosure_coe i).trans (S'.detachedLocus_eq_sUnion i)
  have hZ' : ((S.detachedClosure i) : Set (S.strictTransform i)) =
      (isoH _a0).base ⁻¹' (⋃₀ (S'.detachedComponents i)) := by
    rw [← hZ]
    exact sy_ (P.preimage_coe_detachedClosure i hi)
  rw [S'.detachedIdeal_eq i, S.detachedIdeal_eq i]
  exact comap_vanishingIdeal_sUnion _a0.hom hS hZ hZ'
end

theorem exists_subschemeIso_of_comap_eq {X Z : Sch} (e : X ≅ Z)
    (I : ISD X) (J : ISD Z) (h : J.comap e.hom = I) :
    ∃ u : I.subscheme ≅ J.subscheme, u.hom ≫ J.si = I.si ≫ e.hom := by
  have h1 :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr $ le_of_eq h
  have hcomp : I.comap e.inv = J := by
    rw [← h, ← comap_comp, e.inv_hom_id,
      comap_id]
  have h2 :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr $ le_of_eq hcomp
  obtain ⟨a, ha⟩ : ∃ a,
      a ≫ siI J = siI I ≫ isoH e :=
    ⟨I.subschemeMap J e.hom h1, subschemeMap_subschemeι I J e.hom h1⟩
  obtain ⟨b, hb⟩ : ∃ b,
      b ≫ siI I = siI J ≫ isoI e :=
    ⟨J.subschemeMap I e.inv h2, subschemeMap_subschemeι J I e.inv h2⟩
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  refine mp_ (cancel_mono I.si) ?_
  rw [assoc, hb, ← assoc, ha, assoc, e.hom_inv_id,
    comp_id, id_comp]
  refine mp_ (cancel_mono J.si) ?_
  rw [assoc, ha, ← assoc, hb, assoc, e.inv_hom_id,
    comp_id, id_comp]

section
variable (P : ChartPushforward S S')
theorem exists_iso_detachedScheme [IsReduced Y] i
    (hi : i < S'.length) :
    ∃ e : S.detachedScheme i ≅ S'.detachedScheme i,
      e.hom ≫ S'.detachedio i = S.detachedio i ≫ (P.strictTransformIso i hi.le).hom := by
  exact exists_subschemeIso_of_comap_eq (P.strictTransformIso i hi.le) (S.detachedIdeal i)
    (S'.detachedIdeal i) $ P.comap_detachedIdeal i hi

def detachedSchemeIso [IsReduced Y] (i : ℕ)
    (hi : i < S'.length) : S.detachedScheme i ≅ S'.detachedScheme i :=
  (P.exists_iso_detachedScheme i hi).choose

@[reassoc]
theorem detachedSchemeIso_hom_comp_detachedio [IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (P.detachedSchemeIso i hi).hom ≫ S'.detachedio i = S.detachedio i ≫ (P.strictTransformIso i hi.le).hom :=
  (P.exists_iso_detachedScheme i hi).choose_spec

section
variable (i) (hi : i < S'.length)
theorem preimage_detachedClosureCompl :
    (P.strictTransformIso i hi.le).hom.pre (S'.detachedClosureCompl i) = S.detachedClosureCompl i := by
  have h := P.preimage_coe_detachedClosure i hi
  have h2 : (isoH $ P.strictTransformIso i hi.le) ⁻¹'
      (((S'.detachedClosure i) : Set $ S'.strictTransform i)ᶜ) =
      (((S.detachedClosure i) : Set $ S.strictTransform i)ᶜ) := by simp_all
  exact m55 h2

theorem comap_comapAmbientCenter :
    (S'.comapAmbientCenter i).comap (P.strictTransformIso i hi.le).hom = S.comapAmbientCenter i := by
  have hmap : S'.ambientCenter i = (S.ambientCenter i).map (P.levelMap i hi.le) := by
    rw [P.ambientCenter_eq i hi, map_eq_imageIdealSheaf]
  simp [comapAmbientCenter_eq]
  rw [← comap_comp, P.strictTransformIso_hom_comp_strictTransformio i hi.le,
    comap_comp, hmap, p30]
end
end

theorem exists_isIso_of_preimage_opens_eq {X Z : Sch} (e : X ≅ Z) (U : Opn X)
    (U' : Opn Z) (hU : e.hom ⁻¹ᵁ U' = U) :
    ∃ ps_, IsIso ps_ ∧ ps_ ≫ U'.ι = U.ι ≫ e.hom := by
  let _a4 := opI U' ≫ isoI e
  let _a0 := U
  let _a1 := U'
  have hfwd : ∀ y, y ∈ _a0 → e.hom.base y ∈ _a1 := by
    intro y hy
    have h : y ∈ ((isoH e ⁻¹ᵁ U') : Set X) := by rw [hU]
                                                 exact hy
    exact h
  have hbwd : ∀ y, e.hom.base y ∈ _a1 → y ∈ _a0 := by
    intro y hy
    have h : y ∈ ((isoH e ⁻¹ᵁ U') : Set X) := hy
    rwa [hU] at h
  let _a2 := opI U ≫ isoH e
  have h1 : range _a2.base ⊆ range U'.ib := by
    rw [q1]
    rintro _ ⟨x, rfl⟩
    show e.hom.base (U.ib x) ∈ _a1
    exact hfwd _ x.2
  have h2 : range _a4.base ⊆ range U.ib := by
    rw [q1]
    rintro _ ⟨y, rfl⟩
    show e.inv.base (U'.ib y) ∈ _a0
    refine hbwd _ ?_
    rw [inv_hom_apply e $ U'.ib y]
    exact y.2
  refine ⟨m43 U'.i _a2 h1, ?_, ?_⟩
  refine ⟨⟨m43 U.i _a4 h2, ?_, ?_⟩⟩
  rw [← cancel_mono U.i, assoc, m115, ← assoc,
    m115, assoc, e.hom_inv_id, comp_id,
    id_comp]
  rw [← cancel_mono U'.i, assoc, m115, ← assoc,
    m115, assoc, e.inv_hom_id, comp_id,
    id_comp]
  rw [m115]

theorem comap_centerOffDetached (P : ChartPushforward S S') i (hi : i < S'.length) :
    (S'.centerOffDetached i).comap (P.strictTransformIso i hi.le).hom = S.centerOffDetached i := by
  let _c0 := (S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).i
  have hns' :=
    S'.noetherianSpace_strictTransform i hi.le
  have hnU :=
    noetherianSpace_toScheme (S'.strictTransform i) $ S'.detachedClosureCompl i
  have hqc : QuasiCompact (S'.detachedClosureCompl i).i :=
    ⟨fun _ _ _ => isCompact _⟩
  let _a0 := P.strictTransformIso i hi.le
  have hfl : Flat _a0.hom := inferInstance
  obtain ⟨ps_, hps_, hpsc⟩ := exists_isIso_of_preimage_opens_eq _a0 (S.detachedClosureCompl i)
    (S'.detachedClosureCompl i) $ P.preimage_detachedClosureCompl i hi
  have H :=
    of_horiz_isIso ⟨hpsc⟩
  have key := comap_map_eq_map_comap_of_isPullback H
    _c0
  have hW : _c0.comap ps_
      = (S.comapAmbientCenter i).comap (S.detachedClosureCompl i).i := by
    rw [← comap_comp, hpsc, comap_comp,
      P.comap_comapAmbientCenter i hi]
  rw [hW] at key
  have hS' :=
    (S'.centerOffDetached_eq i).trans (map_eq_ker_subschemeio_comp _ _).symm
  have hS :=
    (S.centerOffDetached_eq i).trans (map_eq_ker_subschemeio_comp _ _).symm
  rwa [hS', hS]

end ChartPushforward





section
variable {Z : Sch}
theorem ker_subschemeι_app (I : ISD Z)
    (V : Z.affineOpens) :
    RingHom.ker (app I.si (V : Opn Z)).hom = I.ideal V := by
  have hinj : Injective $ (I.subschemeObjIso V).inv.hom := by
    intro a b hab
    have h1 : ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom a
        = ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom b := by
      simp only [hom_comp, RingHom.coe_comp, m116, hab]
    simpa using h1
  rw [Scheme.IdealSheafData.subschemeι_app]
  ext x
  simp only [hom_comp, m208, RingHom.coe_comp, m116,
    CommRingCat.hom_ofHom]
  rw [← map_zero $ (I.subschemeObjIso V).inv.hom, hinj.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

section
variable [IsAffine Z]
theorem eq_of_ideal_top_eq {I J : ISD Z}
    (h : I.ideal ⟨⊤, isAffineOpen_top Z⟩ = J.ideal ⟨⊤, isAffineOpen_top Z⟩) : I = J := by
  have hI := (equivOfIsAffine (X := Z)).symm_apply_apply I
  have hJ := (equivOfIsAffine (X := Z)).symm_apply_apply J
  rw [equivOfIsAffine_apply,
    equivOfIsAffine_symm_apply] at hI hJ
  rw [← hI, ← hJ, h]

theorem ideal_top_ofIdealTop_eq
    (J : Ideal Γ(Z, ⊤)) :
    (ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J :=by simp_all
private theorem ofIdealTop_sup (I J : Ideal Γ(Z, ⊤)) :
    ofIdealTop (I ⊔ J) =
      ofIdealTop I ⊔ ofIdealTop J := by
  refine eq_of_ideal_top_eq ?_
  simp [ideal_sup, Pi.sup_apply]
end
end

section
variable {X Y Z : Sch} (f : X ⟶ Y)
private theorem appTop_comp_hom_apply (g : Y ⟶ Z)
    (s : ↑(Z.presheaf.obj $ op ⊤)) :
    (ConcreteCategory.hom $ appTop $ f ≫ g) s
      = (ConcreteCategory.hom $ appTop f)
        ((ConcreteCategory.hom $ appTop g) s) := by
  have h : appTop (f ≫ g) = appTop g ≫ appTop f := by
    simp [appTop]
  rw [h]
  rfl

theorem smooth_of_smooth_comp_isOpenImmersion
    (i : Y ⟶ Z) [IsOpenImmersion i] (h : Smooth $ f ≫ i) : Smooth f := by
  let _a0 := f ≫ i
  have hsq : _a0 = 𝟙 X ≫ _a0 := by simp
  have hp : IsPullback f (𝟙 X) i _a0 := by
    refine of_isLimit (c := Limits.PullbackCone.mk f (𝟙 X) hsq) ?_
    refine Limits.PullbackCone.IsLimit.mk _ (·.snd) (fun s => ?_) (fun s => ?_)
      (fun s m h1_ h2_ => ?_)
    have hc : s.fst ≫ i = (s.snd ≫ f) ≫ i := by
      rw [assoc]
      exact s.condition
    exact sy_ $ mp_ (cancel_mono i) hc
    simp
    simpa using h2_
  exact m122 hp.flip h
end

section
variable {X Y : Sch} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
theorem comap_ofIdealTop_span (s : Set Γ(Y, ⊤)) :
    (ofIdealTop $ span s).comap f =
      ofIdealTop
        (span $ ⇑(CommRingCat.Hom.hom $ appTop f) '' s) := by
  rw [comap_ofIdealTop, m218]

theorem ker_eq_ofIdealTop_ker_appTop [IsClosedImmersion f] :
    ker f =
      ofIdealTop
        (RingHom.ker $ CommRingCat.Hom.hom $ appTop f) := by
  have : IsIso $ toImage f := inferInstance
  let _a0 := m4 $ appTop $ toImage f
  let _a2 := inv $ toImage f
  have h2 : ∀ z, (m4 $ appTop _a2)
      (_a0 z) = z := by
    intro z
    have hz := sy_ $ appTop_comp_hom_apply _a2
      (toImage f) z
    rw [m117] at hz
    simpa using hz
  have hinj : Injective
      _a0 := by
    intro a b hab
    have ha := h2 a
    rw [hab, h2 b] at ha
    exact sy_ ha
  have happ : ∀ z, (m4 $ appTop f) z
      = _a0
        ((m4 $ appTop $ siI $ m149 f) z) := by
    intro z
    conv_lhs => rw [← toImage_imageι f]
    rw [appTop_comp_hom_apply]
  have hkers : m41 (m4 $ appTop f) =
      m41 (m4
        (appTop $ siI $ m149 f)) := by
    ext z
    simp
    rw [happ z]
    constructor
    intro hz
    apply hinj
    rw [hz, map_zero]
    intro hz
    rw [hz, map_zero]
  refine eq_of_ideal_top_eq ?_
  rw [ideal_top_ofIdealTop_eq,
    ← ker_subschemeι_app (m149 f) ⟨⊤, isAffineOpen_top Y⟩]
  exact sy_ hkers
end

section
variable (k : Type) [Field k]
theorem graphMorphismToAffineSpace_comp_projLeft (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k $ UFS M n).presheaf.obj $ op ⊤))
    (D : (affineSpaceIndexedBy k $ UFS M n).Opens) :
    graphMorphismToAffineSpace k M n q F D ≫ projLeft k M q = D.ι ≫ projLeft k M n := by
  refine m46 ?_ ?_
  rw [assoc, projLeft_comp_affineSpaceIndexedByToSpec, assoc, projLeft_comp_affineSpaceIndexedByToSpec, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec]
  intro i
  obtain ⟨a⟩ := i
  let _a0 := m9 (Sp k) $ up a
  show (m23 $ appTop $ graphMorphismToAffineSpace k M n q F D ≫ projLeft k M q)
        _a0
      = m23 (appTop $ opI D ≫ projLeft k M n)
        _a0
  rw [appTop_comp_hom_apply, appTop_comp_hom_apply, projLeft_appTop_coord, projLeft_appTop_coord,
    graphMorphismToAffineSpace_appTop_coord_inl]

theorem coordSubspaceIdeal_univ_eq_ofIdealTop (m : ℕ) :
    coordSubspaceIdeal k m univ =
      ofIdealTop
        (span $ range fun i : Fin m =>
          AffineSpace.coord (Sp k) $ up i) := by
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, coe_univ, image_univ]

theorem coordSubspaceIdeal_univ_comap_affineSpaceIsoOfEquiv (c q : ℕ) :
    (coordSubspaceIdeal k (c + q) univ).comap
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv c q) $ Sp k).hom
      = (coordSubspaceIdeal k c univ).comap (projLeft k c q)
        ⊔ (coordSubspaceIdeal k q univ).comap (projRight k c q) := by
  have h1 : ∀ i : UFin $ c + q,
      (m4 $ appTop
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv c q) $ Sp k).hom)
          (m9 (Sp k) i)
        = m9 (Sp k) ((uliftFinSumEquiv c q).symm i) := by
    intro i
    simp [affineSpaceIsoOfEquiv]
  have h2 : ∀ a,
      (m4 $ appTop $ projLeft k c q)
          (m9 (Sp k) $ up a)
        = m9 (Sp k)
            (up (inl a) : UFS c q) := by
    intro a
    simp
  have h3 : ∀ b,
      (m4 $ appTop $ projRight k c q)
          (m9 (Sp k) $ up b)
        = m9 (Sp k)
            (up (m50 b) : UFS c q) := by
    intro b
    simp
  have hset :
      (m4 $ appTop
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv c q) $ Sp k).hom) ''
        range (fun i : Fin (c + q) =>
          m9 (Sp k) $ up i)
      = (m4 $ appTop $ projLeft k c q) ''
          range (fun a =>
            m9 (Sp k) $ up a)
        ∪ ((m4 $ appTop $ projRight k c q) ''
          range (fun b =>
            m9 (Sp k) $ up b)) := by
    ext x
    simp only [mem_image, mem_range, mem_union]
    constructor
    rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    rw [h1]
    rcases hcase : ((uliftFinSumEquiv c q).symm $ up i).down with a | b
    refine m51 ⟨_, ⟨a, rfl⟩, ?_⟩
    rw [h2]
    have hEq : up (inl a)
        = (uliftFinSumEquiv c q).symm (up i) := by
      rw [← hcase]
    rw [hEq]
    refine inr ⟨_, ⟨b, rfl⟩, ?_⟩
    rw [h3]
    have hEq : up (Sum.inr b)
        = (uliftFinSumEquiv c q).symm (up i) := by
      rw [← hcase]
    rw [hEq]
    rintro (⟨y, ⟨a, rfl⟩, rfl⟩ | ⟨y, ⟨b, rfl⟩, rfl⟩)
    refine ⟨_, ⟨((uliftFinSumEquiv c q) $ up $ inl a).down, rfl⟩, ?_⟩
    rw [h1, h2]
    congr 1
    rw [up_down, symm_apply_apply]
    refine ⟨_, ⟨((uliftFinSumEquiv c q) $ up $ m50 b).down, rfl⟩, ?_⟩
    rw [h1, h3]
    congr 1
    rw [up_down, symm_apply_apply]
  rw [coordSubspaceIdeal_univ_eq_ofIdealTop, coordSubspaceIdeal_univ_eq_ofIdealTop,
    coordSubspaceIdeal_univ_eq_ofIdealTop, comap_ofIdealTop_span, comap_ofIdealTop_span,
    comap_ofIdealTop_span, ← ofIdealTop_sup, ← span_union, hset]
end





variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]

namespace EmbeddedBlowupSequence

section
variable (S : EmbeddedBlowupSequence k Y pY)
theorem detachedToCoprod_detachedCoprodInl_detachedCoprodMapOfLE s a b
    (hsa : s < a) (hab : a + 1 ≤ b) :
    S.detachedToCoprod s a hsa ≫ S.detachedCoprodInl a ≫ S.detachedCoprodMapOfLE hab =
      S.detachedToCoprod s b (lt_of_lt_of_le hsa $ le_trans (le_succ a) hab) := by
  rw [← assoc, ← S.detachedToCoprod_succ_of_lt s a hsa, S.detachedToCoprod_detachedCoprodMapOfLE]

theorem detachedCoprodInr_detachedCoprodMapOfLE a b (hab : a + 1 ≤ b) :
    S.detachedCoprodInr a ≫ S.detachedCoprodMapOfLE hab =
      S.detachedToCoprod a b (lt_of_lt_of_le (lt_succ_self a) hab) := by
  rw [← S.detachedToCoprod_self a, S.detachedToCoprod_detachedCoprodMapOfLE]

section
variable (h : S.TransitionsAreBlowups)
def inactiveTotalToBase (i : ℕ) :
    S.detachedCoprod i ⟶ Y :=
  (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ projectionToBase (S.inducedBlowups h) i

theorem detachedToCoprod_inactiveTotalToBase (s i : ℕ)
    (hs : s < i) :
    S.detachedToCoprod s i hs ≫ S.inactiveTotalToBase h i = S.detachedio s ≫ S.strictTransformToBase s :=
  detachedToCoprod_inr_inducedBlowups_projectionToBase S h s i hs

theorem coprodDesc_strictTransformToBase_inactiveTotalToBase i :
    coprod.desc (S.strictTransformToBase i) (S.inactiveTotalToBase h i) = projectionToBase (S.inducedBlowups h) i := by
  apply coprod.hom_ext
  rw [coprod.inl_desc]
  exact sy_ $ inl_inducedBlowups_projectionToBase S h i
  rw [coprod.inr_desc]
  rfl
end
end

end EmbeddedBlowupSequence

namespace ChartFlatBaseChange

variable {k' : Type} [Field k'] [CharZero k'] {Y'} [IsAffine Y']
  {pY'} [LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

section
variable (F : ChartFlatBaseChange S S')
theorem reindex_lt_reindex {s j} (hsj : s < j)
    (hj : j ≤ S'.length) : F.reindex s < F.reindex j :=
  F.reindex_lt_reindex_of_lt hsj hj

section
variable (j : ℕ)
theorem reindex_le_reindex_succ (hj : j + 1 ≤ S'.length) :
    F.reindex j ≤ F.reindex (j + 1) :=
  (F.reindex_lt_succ j $ by omega).le

theorem reindex_lt_reindex_succ (hj : j + 1 ≤ S'.length) :
    F.reindex j < F.reindex (j + 1) :=
  F.reindex_lt_succ j $ by omega

theorem strictTransformComparison_comp_strictTransformToBase (hj : j ≤ S'.length) :
    F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j) = S'.strictTransformToBase j ≫ F.baseMap := by
  have : CategoryTheory.Mono S.emb := inferInstance
  refine mp_ (cancel_mono S.emb) ?_
  let _a1 := S.ambientSeq.projectionToBase $ F.reindex j
  calc ((F.strictTransformComparison j hj ≫ S.strictTransformToBase (F.reindex j)) ≫ S.emb)
      = F.strictTransformComparison j hj ≫ (S.strictTransformToBase (F.reindex j) ≫ S.emb) := assoc _ _ _
    _ = F.strictTransformComparison j hj ≫
          (S.strictTransformio (F.reindex j) ≫ _a1) := by
          rw [S.strictTransformToBase_emb $ F.reindex j]
    _ = (F.strictTransformComparison j hj ≫ S.strictTransformio (F.reindex j)) ≫
          _a1 := sy_ $ assoc _ _ _
    _ = (S'.strictTransformio j ≫ F.levelMap j hj) ≫ _a1 := by
          rw [F.strictTransformComparison_comp_strictTransformio j hj]
    _ = S'.strictTransformio j ≫ (F.levelMap j hj ≫ _a1) :=
          assoc _ _ _
    _ = S'.strictTransformio j ≫ (S'.ambientSeq.projectionToBase j ≫ F.ambientMap) := by
          rw [(F.isPullback_level j hj).w]
    _ = (S'.strictTransformio j ≫ S'.ambientSeq.projectionToBase j) ≫ F.ambientMap :=
          (assoc _ _ _).symm
    _ = (S'.strictTransformToBase j ≫ S'.emb) ≫ F.ambientMap := by rw [S'.strictTransformToBase_emb j]
    _ = S'.strictTransformToBase j ≫ (S'.emb ≫ F.ambientMap) := assoc _ _ _
    _ = S'.strictTransformToBase j ≫ (F.baseMap ≫ S.emb) := by rw [F.isPullback_emb.w]
    _ = ((S'.strictTransformToBase j ≫ F.baseMap) ≫ S.emb) := sy_ $ assoc _ _ _

theorem isPullback_strictTransformComparison_strictTransformToBase (hj : j ≤ S'.length) :
    IsPullback (F.strictTransformComparison j hj) (S'.strictTransformToBase j) (S.strictTransformToBase $ F.reindex j)
      F.baseMap := by
  have h2 := (F.isPullback_strictTransformComparison_strictTransformio j hj).paste_vert $ F.isPullback_level j hj
  rw [← S.strictTransformToBase_emb $ F.reindex j, ← S'.strictTransformToBase_emb j] at h2
  exact h2.of_bot (F.strictTransformComparison_comp_strictTransformToBase j hj) F.isPullback_emb
end

theorem isEmpty_of_comm_detachedScheme_of_not_mem_range (s : ℕ) (hs : s < S.length)
    (hskip : ∀ j, j < S'.length → F.reindex j ≠ s) (Q : Sch) (q : Q ⟶ S.detachedScheme s)
    (p : Q ⟶ Y') (hcomm : q ≫ S.detachedio s ≫ S.strictTransformToBase s = p ≫ F.baseMap) :
    IsEmpty ↥Q := by
  let _a1 := p ≫ S'.emb
  refine F.isEmpty_of_forall_reindex_ne s hs hskip Q q _a1 ?_
  calc q ≫ S.detachedio s ≫ S.strictTransformio s ≫ S.ambientSeq.projectionToBase s
      = q ≫ S.detachedio s ≫ S.strictTransformToBase s ≫ S.emb := by rw [S.strictTransformToBase_emb s]
    _ = (q ≫ S.detachedio s ≫ S.strictTransformToBase s) ≫ S.emb := by simp [assoc]
    _ = (p ≫ F.baseMap) ≫ S.emb := by rw [hcomm]
    _ = p ≫ (F.baseMap ≫ S.emb) := assoc _ _ _
    _ = p ≫ (S'.emb ≫ F.ambientMap) := by rw [F.isPullback_emb.w]
    _ = _a1 ≫ F.ambientMap := sy_ $ assoc _ _ _
end

theorem isEmpty_of_hom_to_initial {P : Sch}
    (f : P ⟶ ⊥_ Sch) : IsEmpty ↥P :=
  Function.isEmpty f.base

theorem inactiveTotalToBase_succ_eq_desc (T : EmbeddedBlowupSequence k Y pY)
    (hT : T.TransitionsAreBlowups) (i : ℕ) :
    T.inactiveTotalToBase hT (i + 1) =
      coprod.desc (T.inactiveTotalToBase hT i) (T.detachedio i ≫ T.strictTransformToBase i) := by
  let _a0 := T.inactiveTotalToBase hT $ i + 1
  have hl : T.detachedCoprodInl i ≫ _a0 = T.inactiveTotalToBase hT i := by
    refine T.detachedCoprod_hom_ext i ?_
    intro s hs
    let _a1 := T.detachedToCoprod s i hs ≫ T.detachedCoprodInl i
    calc _a1 ≫ _a0
        = _a1 ≫ _a0 :=
          symm $ assoc _ _ _
      _ = T.detachedToCoprod s (i + 1) (lt_succ_of_lt hs) ≫ _a0 := by
          rw [T.detachedToCoprod_succ_of_lt s i hs]
      _ = T.detachedio s ≫ T.strictTransformToBase s :=
          T.detachedToCoprod_inactiveTotalToBase hT s (i + 1) $ lt_succ_of_lt hs
      _ = T.detachedToCoprod s i hs ≫ T.inactiveTotalToBase hT i :=
          symm $ T.detachedToCoprod_inactiveTotalToBase hT s i hs
  have hr : T.detachedCoprodInr i ≫ _a0 = T.detachedio i ≫ T.strictTransformToBase i := by
    calc T.detachedCoprodInr i ≫ _a0
        = T.detachedToCoprod i (i + 1) (lt_succ_self i) ≫ _a0 := by
          rw [T.detachedToCoprod_self i]
      _ = T.detachedio i ≫ T.strictTransformToBase i :=
          T.detachedToCoprod_inactiveTotalToBase hT i (i + 1) $ lt_succ_self i
  exact T.detachedCoprod_succ_hom_ext i (tr_ hl (coprod.inl_desc _ _).symm) $ tr_ hr (coprod.inr_desc _ _).symm

section
variable (F : ChartFlatBaseChange S S')
section
variable (h : S.TransitionsAreBlowups)
theorem forall_isEmpty_of_comm_inactiveTotalToBase :
    ∀ i, (∀ s, s < i → s < S.length) →
      (∀ s, s < i → ∀ j, j < S'.length → F.reindex j ≠ s) →
      ∀ (P : Sch) (q : P ⟶ S.detachedCoprod i) (p : P ⟶ Y'),
        q ≫ S.inactiveTotalToBase h i = p ≫ F.baseMap → IsEmpty ↥P := by
  intro i
  induction i with
  | zero =>
      intro _ _ P q _ _
      exact isEmpty_of_hom_to_initial q
  | succ n ih =>
      intro hlt hskip P q p hcomm
      let _a1 := S.inactiveTotalToBase h n
      let _a0 := S.detachedio n ≫ S.strictTransformToBase n
      have h3 := isPullback_coprodMap_coprodDesc (initial.to (S.detachedCoprod n))
        (initial.to (S.detachedScheme n)) (initial.to Y') (initial.to Y')
        _a1 _a0 F.baseMap (isPullback_initial_of_isEmpty _a1 F.baseMap fun Q a b hab => ih (fun s hs => hlt s $ lt_succ_of_lt hs) (fun s hs => hskip s $ lt_succ_of_lt hs) Q a b hab) (isPullback_initial_of_isEmpty _a0 F.baseMap fun Q c d hcd => F.isEmpty_of_comm_detachedScheme_of_not_mem_range n (hlt n (lt_succ_self n)) (hskip n (lt_succ_self n)) Q c d hcd)
      exact isEmpty_of_hom_to_initial
        (h3.lift q p ((congrArg (fun t : S.detachedCoprod (n + 1) ⟶ Y => q ≫ t) (inactiveTotalToBase_succ_eq_desc S h n)).symm.trans hcomm) ≫ coprod.desc (𝟙 (⊥_ Sch)) (𝟙 (⊥_ Sch)))

theorem isEmpty_of_comm_inactiveTotalToBase_of_not_mem_range
    (i : ℕ) (hlt : ∀ s, s < i → s < S.length)
    (hskip : ∀ s, s < i → ∀ j, j < S'.length → F.reindex j ≠ s) (P : Sch)
    (q : P ⟶ S.detachedCoprod i) (p : P ⟶ Y')
    (hcomm : q ≫ S.inactiveTotalToBase h i = p ≫ F.baseMap) : IsEmpty ↥P :=
  forall_isEmpty_of_comm_inactiveTotalToBase F h i hlt hskip P q p hcomm

theorem isPullback_detachedCoprodMapOfLE_inactiveTotalToBase
    {a b : ℕ} (hab : a ≤ b) (hlt : ∀ s, a ≤ s → s < b → s < S.length)
    (hskip : ∀ s, a ≤ s → s < b → ∀ j, j < S'.length → F.reindex j ≠ s) {P : Sch}
    (q : P ⟶ S.detachedCoprod a) (p : P ⟶ Y')
    (hsq : IsPullback q p (S.inactiveTotalToBase h a) F.baseMap) :
    IsPullback (q ≫ S.detachedCoprodMapOfLE hab) p (S.inactiveTotalToBase h b) F.baseMap := by
  have main : ∀ c (hac : a ≤ c),
      (∀ s, a ≤ s → s < c → s < S.length) →
      (∀ s, a ≤ s → s < c → ∀ j, j < S'.length → F.reindex j ≠ s) →
      IsPullback (q ≫ S.detachedCoprodMapOfLE hac) p (S.inactiveTotalToBase h c) F.baseMap := by
    intro c hac
    induction c, hac using le_induction with
    | base =>
        intro _ _
        have hpbRefl : IsPullback (q ≫ S.detachedCoprodMapOfLE (m164 a)) p
            (S.inactiveTotalToBase h a) F.baseMap := by
          rwa [S.detachedCoprodMapOfLE_self a, comp_id]
        exact hpbRefl
    | succ c hac ih =>
        intro hlt1 hskip1
        have ih' := ih (fun s h1 h2 => hlt1 s h1 $ lt_succ_of_lt h2)
          (fun s h1 h2 => hskip1 s h1 $ lt_succ_of_lt h2)
        have hF :=
          fun Q cc d hcomm => F.isEmpty_of_comm_detachedScheme_of_not_mem_range c (hlt1 c hac $ lt_succ_self c) (hskip1 c hac $ lt_succ_self c) Q cc d hcomm
        let _a0 := S.inactiveTotalToBase h $ c + 1
        have hinl : S.detachedCoprodInl c ≫ _a0 = S.inactiveTotalToBase h c := by
          show S.detachedCoprodInl c ≫ (coprod.inr : S.detachedCoprod (c + 1) ⟶ S.totalSpace (c + 1)) ≫
              projectionToBase (S.inducedBlowups h) (c + 1) = S.inactiveTotalToBase h c
          rw [projectionToBase_succ, inducedBlowups_blowupMorphism]
          exact S.detachedCoprodInl_inr_totalTransition_assoc c $ projectionToBase (S.inducedBlowups h) c
        let _a1 := S.detachedio c ≫ S.strictTransformToBase c
        have hinr : S.detachedCoprodInr c ≫ _a0 =
            _a1 := by
          have hkey := S.detachedToCoprod_inactiveTotalToBase h c (c + 1) $ lt_succ_self c
          rwa [S.detachedToCoprod_self c] at hkey
        have hdesc : (coprod.desc (S.inactiveTotalToBase h c) _a1 :
            S.detachedCoprod c ⨿ S.detachedScheme c ⟶ Y) = _a0 := by
          apply coprod.hom_ext
          rw [coprod.inl_desc]
          exact sy_ hinl
          rw [coprod.inr_desc]
          exact sy_ hinr
        have key1 : IsPullback ((q ≫ S.detachedCoprodMapOfLE hac) ≫ S.detachedCoprodInl c) p
            _a0 F.baseMap := by
          have key0 := isPullback_comp_inl_coprodDesc (q ≫ S.detachedCoprodMapOfLE hac) p
            (S.inactiveTotalToBase h c) F.baseMap _a1 ih' hF
          rwa [hdesc] at key0
        have hpbSucc : IsPullback (q ≫ S.detachedCoprodMapOfLE (le_succ_of_le hac)) p
            _a0 F.baseMap := by
          rwa [S.detachedCoprodMapOfLE_succ hac, ← assoc]
        exact hpbSucc
  exact main b hab hlt hskip
end

theorem isPullback_inactiveSchemeMap_baseMap
    [IsReduced Y] [IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    IsPullback (F.detachedSchemeComparison j hj) (S'.detachedio j ≫ S'.strictTransformToBase j)
      (S.detachedio (F.reindex j) ≫ S.strictTransformToBase (F.reindex j)) F.baseMap :=
  (F.isPullback_detachedSchemeComparison j hj).paste_vert $ F.isPullback_strictTransformComparison_strictTransformToBase j hj.le
end

def inactiveTotalMap (F : ChartFlatBaseChange S S') [IsReduced Y]
    [IsReduced Y'] :
    ∀ (j : ℕ), j ≤ S'.length → (S'.detachedCoprod j ⟶ S.detachedCoprod (F.reindex j))
  | 0, _ => eqToHom S'.detachedCoprod_zero ≫ initial.to (S.detachedCoprod $ F.reindex 0)
  | (j + 1), hj =>
      eqToHom (S'.detachedCoprod_succ j) ≫
        coprod.desc
          (inactiveTotalMap F j (le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ j hj))
          (F.detachedSchemeComparison j (by omega) ≫
            S.detachedToCoprod (F.reindex j) (F.reindex $ j + 1) (F.reindex_lt_reindex_succ j hj))

section
variable (F : ChartFlatBaseChange S S') [hv0_1 : IsReduced Y] [hv0_2 : IsReduced Y']
include hv0_1 hv0_2
section
variable (n) (hj : n + 1 ≤ S'.length)
theorem inactiveTotalMap_succ_eq_desc :
    F.inactiveTotalMap (n + 1) hj =
      coprod.desc
        (F.inactiveTotalMap n (le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ n hj))
        (F.detachedSchemeComparison n (lt_of_lt_of_le (lt_succ_self n) hj) ≫
          S.detachedToCoprod (F.reindex n) (F.reindex $ n + 1) (F.reindex_lt_reindex_succ n hj)) := by
  have h0 : F.inactiveTotalMap (n + 1) hj =
      eqToHom (S'.detachedCoprod_succ n) ≫
        coprod.desc
          (F.inactiveTotalMap n (le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ n hj))
          (F.detachedSchemeComparison n (lt_of_lt_of_le (lt_succ_self n) hj) ≫
            S.detachedToCoprod (F.reindex n) (F.reindex $ n + 1) (F.reindex_lt_reindex_succ n hj)) := rfl
  have hid : eqToHom (S'.detachedCoprod_succ n) = 𝟙 (S'.detachedCoprod $ n + 1) := eqToHom_refl _ _
  rw [h0, hid]
  exact id_comp _

theorem detachedCoprodInl_inactiveTotalMap :
    S'.detachedCoprodInl n ≫ F.inactiveTotalMap (n + 1) hj =
      F.inactiveTotalMap n (le_of_succ_le hj) ≫ S.detachedCoprodMapOfLE (F.reindex_le_reindex_succ n hj) := by
  rw [inactiveTotalMap_succ_eq_desc F n hj]
  exact coprod.inl_desc _ _

theorem detachedCoprodInr_inactiveTotalMap :
    S'.detachedCoprodInr n ≫ F.inactiveTotalMap (n + 1) hj =
      F.detachedSchemeComparison n (lt_of_lt_of_le (lt_succ_self n) hj) ≫
        S.detachedToCoprod (F.reindex n) (F.reindex $ n + 1) (F.reindex_lt_reindex_succ n hj) := by
  rw [inactiveTotalMap_succ_eq_desc F n hj]
  exact coprod.inr_desc _ _
end

theorem forall_detachedToCoprod_inactiveTotalMap :
    ∀ j hj s hs,
      S'.detachedToCoprod s j hs ≫ F.inactiveTotalMap j hj =
        F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
          S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) := by
  intro j
  induction j with
  | zero =>
      intro hj s hs
      exact absurd hs $ not_lt_zero s
  | succ n ih =>
      intro hj s hs
      rcases lt_or_eq_of_le (mp_ lt_succ_iff hs) with hlt | heq
      rw [S'.detachedToCoprod_succ_of_lt s n hlt, assoc,
        detachedCoprodInl_inactiveTotalMap F n hj, ← assoc,
        ih (le_of_succ_le hj) s hlt, assoc, S.detachedToCoprod_detachedCoprodMapOfLE]
      subst heq
      rw [S'.detachedToCoprod_self s, detachedCoprodInr_inactiveTotalMap F s hj]

theorem detachedToCoprod_inactiveTotalMap j (hj : j ≤ S'.length)
    s (hs : s < j) :
    S'.detachedToCoprod s j hs ≫ F.inactiveTotalMap j hj =
      F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
        S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) :=
  forall_detachedToCoprod_inactiveTotalMap F j hj s hs
end

section
variable (T : EmbeddedBlowupSequence k Y pY) {c b} (hcb : c + 1 ≤ b)
theorem inl_detachedCoprodMapOfLE :
    (coprod.inl : T.detachedCoprod c ⟶ T.detachedCoprod c ⨿ T.detachedScheme c) ≫ T.detachedCoprodMapOfLE hcb =
      T.detachedCoprodMapOfLE (le_of_succ_le hcb) := by
  refine T.detachedCoprod_hom_ext c fun s hs => ?_
  exact tr_ (T.detachedToCoprod_detachedCoprodInl_detachedCoprodMapOfLE s c b hs hcb) (T.detachedToCoprod_detachedCoprodMapOfLE hs $ le_of_succ_le hcb).symm

theorem inr_detachedCoprodMapOfLE :
    (coprod.inr : T.detachedScheme c ⟶ T.detachedCoprod c ⨿ T.detachedScheme c) ≫ T.detachedCoprodMapOfLE hcb =
      T.detachedToCoprod c b hcb :=
  T.detachedCoprodInr_detachedCoprodMapOfLE c b hcb
end

section
variable {P X Z W : Sch}
section
variable {f f' : P ⟶ X}
theorem isPullback_of_fst_eq {g : P ⟶ Z}
    {q : X ⟶ W} {u : Z ⟶ W} (hf : f = f') (hp : IsPullback f' g q u) : IsPullback f g q u := by
  subst hf
  exact hp

theorem isPullback_of_fst_eq_of_snd_eq
    {g g' : P ⟶ Z} {q : X ⟶ W} {u : Z ⟶ W} (hf : f = f') (hg : g = g')
    (hp : IsPullback f' g' q u) : IsPullback f g q u :=by simp_all
end

theorem isPullback_of_snd_eq_of_map_eq {f : P ⟶ X} {g g' : P ⟶ Z}
    {q q' : X ⟶ W} {u : Z ⟶ W} (hg : g = g') (hq : q = q')
    (hp : IsPullback f g' q' u) : IsPullback f g q u :=by simp_all
end

section
variable (F : ChartFlatBaseChange S S')
theorem isPullback_inactiveTotalMap
    [IsReduced Y] [IsReduced Y']
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) (j : ℕ) (hj : j ≤ S'.length) :
    IsPullback (F.inactiveTotalMap j hj) (S'.inactiveTotalToBase h' j)
      (S.inactiveTotalToBase h (F.reindex j)) F.baseMap := by
  have main : ∀ m (hm : m ≤ S'.length),
      IsPullback (F.inactiveTotalMap m hm) (S'.inactiveTotalToBase h' m)
        (S.inactiveTotalToBase h (F.reindex m)) F.baseMap := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hI : IsInitial (S'.detachedCoprod 0) := initialIsInitial
        let _a1 := S.inactiveTotalToBase h $ F.reindex 0
        have hempty : ∀ P (a : P ⟶ S.detachedCoprod (F.reindex 0)) b,
            a ≫ _a1 = b ≫ F.baseMap → IsEmpty P := by
          intro P a b hcomm
          exact F.isEmpty_of_comm_inactiveTotalToBase_of_not_mem_range h (F.reindex 0)
            (fun s hs => lt_of_lt_of_le hs (F.reindex_le_length $ zero_le S'.length))
            (fun s hs j' hj' => F.reindex_ne_of_lt_reindex_zero s hs j' hj') P a b hcomm
        have e1 : F.inactiveTotalMap 0 hm = initial.to (S.detachedCoprod (F.reindex 0)) :=
          hI.hom_ext _ _
        have e2 : S'.inactiveTotalToBase h' 0 = initial.to Y' := hI.hom_ext _ _
        exact isPullback_of_fst_eq_of_snd_eq e1 e2 (isPullback_initial_of_isEmpty _a1 F.baseMap hempty)
    | succ n ih =>
        intro hm
        have hn := le_of_succ_le hm
        have hnlt := hm
        have hab := F.reindex_lt_succ n hnlt
        let _a2 := F.inactiveTotalMap n hn
        let _a3 := F.detachedSchemeComparison n hnlt
        have hcop := isPullback_coprodMap_coprodDesc _a2
          _a3 (S'.inactiveTotalToBase h' n) (S'.detachedio n ≫ S'.strictTransformToBase n)
          (S.inactiveTotalToBase h (F.reindex n))
          (S.detachedio (F.reindex n) ≫ S.strictTransformToBase (F.reindex n)) F.baseMap (ih hn)
          (F.isPullback_inactiveSchemeMap_baseMap n hnlt)
        let _a0 := coprod.map _a2 _a3
        have hstep := F.isPullback_detachedCoprodMapOfLE_inactiveTotalToBase h hab
          (fun s _ hs2 => lt_of_lt_of_le hs2 (F.reindex_le_length hm))
          (fun s hs1 hs2 j' hj' => F.reindex_ne_of_reindex_lt_of_lt_reindex_succ n hnlt s (by omega) hs2 j' hj')
          _a0
          (S'.inactiveTotalToBase h' (n + 1)) (isPullback_of_snd_eq_of_map_eq (inactiveTotalToBase_succ_eq_desc S' h' n) (inactiveTotalToBase_succ_eq_desc S h (F.reindex n)) hcop)
        have hE : F.inactiveTotalMap (n + 1) hm =
            _a0 ≫
              S.detachedCoprodMapOfLE hab := by
          refine S'.detachedCoprod_succ_hom_ext n ?_ ?_
          exact tr_ (detachedCoprodInl_inactiveTotalMap F n hm)
            (tr_ (coprod.inl_map_assoc _a2
                _a3 (S.detachedCoprodMapOfLE hab))
              (congrArg
                (fun t : (S.detachedCoprod (F.reindex n) ⟶ S.detachedCoprod (F.reindex (n + 1))) =>
                  _a2 ≫ t)
                (inl_detachedCoprodMapOfLE S hab))).symm
          exact tr_ (detachedCoprodInr_inactiveTotalMap F n hm)
            (tr_ (coprod.inr_map_assoc _a2
                _a3 (S.detachedCoprodMapOfLE hab))
              (congrArg
                (fun t : (S.detachedScheme (F.reindex n) ⟶ S.detachedCoprod (F.reindex (n + 1))) =>
                  _a3 ≫ t)
                (inr_detachedCoprodMapOfLE S hab))).symm
        exact isPullback_of_fst_eq hE hstep
  exact main j hj

def totalSpaceMap [IsReduced Y]
    [IsReduced Y'] (j : ℕ) (hj : j ≤ S'.length) :
    S'.totalSpace j ⟶ S.totalSpace (F.reindex j) :=
  coprod.map (F.strictTransformComparison j hj) $ F.inactiveTotalMap j hj

section
variable [hv1_0 : IsReduced Y] [hv1_1 : IsReduced Y']
include hv1_0 hv1_1
section
variable (j) (hj : j ≤ S'.length)
theorem totalSpaceMap_eq_coprodMap :
    F.totalSpaceMap j hj = coprod.map (F.strictTransformComparison j hj) (F.inactiveTotalMap j hj) := rfl

theorem inl_totalSpaceMap :
    (coprod.inl : S'.strictTransform j ⟶ S'.totalSpace j) ≫ F.totalSpaceMap j hj =
      F.strictTransformComparison j hj ≫
        (coprod.inl : S.strictTransform (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  simp [ChartFlatBaseChange.totalSpaceMap]

theorem detachedToCoprod_inr_totalSpaceMap
    s (hs : s < j) :
    S'.detachedToCoprod s j hs ≫ (coprod.inr : S'.detachedCoprod j ⟶ S'.totalSpace j) ≫
        F.totalSpaceMap j hj =
      F.detachedSchemeComparison s (lt_of_lt_of_le hs hj) ≫
        S.detachedToCoprod (F.reindex s) (F.reindex j) (F.reindex_lt_reindex hs hj) ≫
          (coprod.inr : S.detachedCoprod (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  rw [F.totalSpaceMap_eq_coprodMap j hj, coprod.inr_map, ← assoc,
    F.detachedToCoprod_inactiveTotalMap j hj s hs, assoc]
end

theorem isPullback_totalSpaceMap (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    j (hj : j ≤ S'.length) :
    IsPullback (F.totalSpaceMap j hj) (projectionToBase (S'.inducedBlowups h') j)
      (projectionToBase (S.inducedBlowups h) (F.reindex j)) F.baseMap := by
  have key := isPullback_coprodMap_coprodDesc (F.strictTransformComparison j hj)
    (F.inactiveTotalMap j hj) (S'.strictTransformToBase j) (S'.inactiveTotalToBase h' j)
    (S.strictTransformToBase (F.reindex j)) (S.inactiveTotalToBase h (F.reindex j)) F.baseMap
    (F.isPullback_strictTransformComparison_strictTransformToBase j hj) (F.isPullback_inactiveTotalMap h h' j hj)
  rw [S'.coprodDesc_strictTransformToBase_inactiveTotalToBase h' j, S.coprodDesc_strictTransformToBase_inactiveTotalToBase h (F.reindex j)] at key
  rwa [F.totalSpaceMap_eq_coprodMap j hj]
end
end

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

namespace ChartPushforward

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]
  {S S' : EmbeddedBlowupSequence k Y pY}

section
variable (P : ChartPushforward S S')
include P
theorem le_length_of_le_length {i} (hi : i ≤ S.length) : i ≤ S'.length := by
  rwa [← P.len_eq]

theorem lt_length_of_lt_length {i} (hi : i < S.length) : i < S'.length := by
  rwa [← P.len_eq]

def detachedCoprodIsoOfLE [IsReduced Y] :
    ∀ i : ℕ, i ≤ S'.length → (S.detachedCoprod i ≅ S'.detachedCoprod i) := fun i =>
  Nat.rec (motive := fun n => n ≤ S'.length → (S.detachedCoprod n ≅ S'.detachedCoprod n))
    (fun _ => eqToIso $ S.detachedCoprod_zero.trans S'.detachedCoprod_zero.symm)
    (fun n ih hn => coprod.mapIso (ih $ le_of_succ_le hn)
      (P.detachedSchemeIso n $ lt_of_lt_of_le (lt_succ_self n) hn)) i

theorem exists_iso_detachedCoprod_compatible
    [IsReduced Y] :
    ∃ e : ∀ i, i ≤ S'.length → (S.detachedCoprod i ≅ S'.detachedCoprod i),
      (∀ h : (0 : ℕ) ≤ S'.length,
          (e 0 h).hom = eqToHom (S.detachedCoprod_zero.trans S'.detachedCoprod_zero.symm)) ∧
      (∀ i (hi : i < S'.length),
          S.detachedCoprodInl i ≫ (e (i + 1) hi).hom = (e i hi.le).hom ≫ S'.detachedCoprodInl i) ∧
      (∀ i (hi : i < S'.length),
          S.detachedCoprodInr i ≫ (e (i + 1) hi).hom =
            (P.detachedSchemeIso i hi).hom ≫ S'.detachedCoprodInr i) := by
  refine ⟨detachedCoprodIsoOfLE P, fun _ => rfl, ?_, ?_⟩
  intro i hi
  show (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) ≫
      coprod.map (detachedCoprodIsoOfLE P i hi.le).hom (P.detachedSchemeIso i hi).hom =
    (detachedCoprodIsoOfLE P i hi.le).hom ≫
      coprod.inl
  simp
  intro i hi
  show (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) ≫
      coprod.map (detachedCoprodIsoOfLE P i hi.le).hom (P.detachedSchemeIso i hi).hom =
    (P.detachedSchemeIso i hi).hom ≫
      coprod.inr
  simp

def inactiveTotalIso [IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) : S.detachedCoprod i ≅ S'.detachedCoprod i :=
  P.exists_iso_detachedCoprod_compatible.choose i hi

@[reassoc]
theorem detachedCoprodInl_inactiveTotalIso_hom
    [IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    S.detachedCoprodInl i ≫ (P.inactiveTotalIso (i + 1) hi).hom =
      (P.inactiveTotalIso i hi.le).hom ≫ S'.detachedCoprodInl i :=
  P.exists_iso_detachedCoprod_compatible.choose_spec.2.1 i hi

@[reassoc]
theorem detachedCoprodInr_inactiveTotalIso_hom
    [IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    S.detachedCoprodInr i ≫ (P.inactiveTotalIso (i + 1) hi).hom =
      (P.detachedSchemeIso i hi).hom ≫ S'.detachedCoprodInr i :=
  P.exists_iso_detachedCoprod_compatible.choose_spec.2.2 i hi

def totalSpaceIso [IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) : S.totalSpace i ≅ S'.totalSpace i :=
  coprod.mapIso (P.strictTransformIso i hi) $ P.inactiveTotalIso i hi

section
variable [hv1_0 : IsReduced Y] (i) (hi : i ≤ S'.length)
include hv1_0
theorem totalSpaceIso_hom_eq_coprodMap :
    (P.totalSpaceIso i hi).hom =
      coprod.map (P.strictTransformIso i hi).hom (P.inactiveTotalIso i hi).hom := rfl

@[reassoc]
theorem inl_totalSpaceIso_hom :
    (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (P.totalSpaceIso i hi).hom =
      (P.strictTransformIso i hi).hom ≫ (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i) := by
  rw [P.totalSpaceIso_hom_eq_coprodMap i hi]
  simp

@[reassoc]
theorem inr_totalSpaceIso_hom :
    (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ (P.totalSpaceIso i hi).hom =
      (P.inactiveTotalIso i hi).hom ≫ (coprod.inr : S'.detachedCoprod i ⟶ S'.totalSpace i) := by
  rw [P.totalSpaceIso_hom_eq_coprodMap i hi]
  simp
end
end

section
variable {A B : Sch} (e : A ≅ B)
private theorem comap_hom_comap_inv (I : ISD B) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← comap_comp, e.inv_hom_id, comap_id]

private theorem comap_inv_comap_hom (I : ISD A) :
    (I.comap e.inv).comap e.hom = I := by
  rw [← comap_comp, e.hom_inv_id, comap_id]
end

section
variable (P : ChartPushforward S S') [hv0_1 : IsReduced Y]
include P hv0_1
section
variable (i) (hi : i < S'.length)
theorem comap_totalCenter :
    (S'.totalCenter i).comap (P.totalSpaceIso i hi.le).hom = S.totalCenter i := by
  have h : ((S'.centerOffDetached i).map coprod.inl).comap (P.totalSpaceIso i hi.le).hom = ((S'.centerOffDetached i).comap (P.strictTransformIso i hi.le).hom).map coprod.inl := by
    let eA := P.strictTransformIso i hi.le
    let eB := P.totalSpaceIso i hi.le
    let u := (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
    let u' := (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i)
    let hcomm := P.inl_totalSpaceIso_hom i hi.le
    let J := S'.centerOffDetached i
    let _a0 := (J.comap eA.hom).map u
    have hcomm' : u' ≫ isoI eB = isoI eA ≫ u := by
      rw [Iso.eq_inv_comp, ← assoc, ← hcomm, assoc, eB.hom_inv_id,
        comp_id]
    refine le_antisymm ?_ ?_
    rw [le_map_iff_comap_le, ← comap_comp, hcomm,
      comap_comp]
    exact comap_mono _
      (Scheme.IdealSheafData.le_map_iff_comap_le.mp le_rfl)
    have key : _a0.comap eB.inv ≤ J.map u' := by
      rw [le_map_iff_comap_le, ← comap_comp, hcomm',
        comap_comp]
      have h2 : (cmI _a0 u).comap eA.inv ≤
          (J.comap eA.hom).comap eA.inv :=
        comap_mono eA.inv
          (Scheme.IdealSheafData.le_map_iff_comap_le.mp
            le_rfl)
      rwa [comap_hom_comap_inv eA J] at h2
    have h3 : (_a0.comap eB.inv).comap eB.hom ≤
        (J.map u').comap eB.hom :=
      comap_mono eB.hom key
    rwa [comap_inv_comap_hom eB] at h3
  rwa [P.comap_centerOffDetached i hi] at h

theorem totalSpaceIso_hom_totalTransition :
    (P.totalSpaceIso (i + 1) hi).hom ≫ S'.totalTransition i
      = S.totalTransition i ≫ (P.totalSpaceIso i hi.le).hom := by
  refine coprod.hom_ext ?_ ?_
  rw [P.inl_totalSpaceIso_hom_assoc (i + 1) hi, S'.inl_totalTransition_eq_strictTransformMap_inl i, S.inl_totalTransition_assoc i,
    P.inl_totalSpaceIso_hom i hi.le]
  exact P.strictTransformIso_hom_comp_strictTransformMap_assoc i hi _
  refine S.detachedCoprod_succ_hom_ext i ?_ ?_
  rw [P.inr_totalSpaceIso_hom_assoc (i + 1) hi, P.detachedCoprodInl_inactiveTotalIso_hom_assoc i hi,
    S'.detachedCoprodInl_inr_totalTransition i, S.detachedCoprodInl_inr_totalTransition_assoc i,
    P.inr_totalSpaceIso_hom i hi.le]
  rw [P.inr_totalSpaceIso_hom_assoc (i + 1) hi, P.detachedCoprodInr_inactiveTotalIso_hom_assoc i hi,
    S'.detachedCoprodInr_inr_totalTransition i, S.detachedCoprodInr_inr_totalTransition_assoc i,
    P.inl_totalSpaceIso_hom i hi.le]
  exact P.detachedSchemeIso_hom_comp_detachedio_assoc i hi _
end

section
variable (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
theorem inducedBlowups_isomorphic :
    (S.inducedBlowups h).Isomorphic $ S'.inducedBlowups h' := by
  refine ⟨P.len_eq, fun i hi => P.totalSpaceIso i $ P.le_length_of_le_length hi, ?_, ?_, ?_⟩
  show isoH (P.totalSpaceIso 0 $ zero_le _) ≫ S'.totalSpaceZeroIso.hom = S.totalSpaceZeroIso.hom
  refine coprod.hom_ext ?_ ?_
  rw [P.inl_totalSpaceIso_hom_assoc 0 $ zero_le _, S'.inl_totalSpaceZeroIso_hom,
    S.inl_totalSpaceZeroIso_hom]
  exact P.strictTransformIso_zero_hom_comp_strictTransformZeroIso_hom
  have hB : IsInitial $ S.detachedCoprod 0 := initialIsInitial
  exact hB.hom_ext _ _
  intro i hi
  rw [inducedBlowups_blowupMorphism S' h' i, inducedBlowups_blowupMorphism S h i]
  exact P.totalSpaceIso_hom_totalTransition i $ P.lt_length_of_lt_length hi
  intro i hi
  exact P.comap_totalCenter i $ P.lt_length_of_lt_length hi

theorem inducedBlowupsWithoutIso_isomorphic :
    (S.inducedBlowupsWithoutIso h).Isomorphic $ S'.inducedBlowupsWithoutIso h' :=
  (P.inducedBlowups_isomorphic h h').withoutIsoBlowups
end
end

end ChartPushforward





namespace EmbeddingDatum

variable {k : Type} [Field k] [CharZero k] {Y}
  {p : Y ⟶ Sp k}

section
variable (G : EmbeddingDatum k Y p)
theorem emb_comp_comp_eq_of_comp_eq {A' : Sch}
    (q : A' ⟶ Sp k) (ta_ : G.ambient ⟶ A')
    (hta : ta_ ≫ q = G.ambientStruct) :
    (G.emb ≫ ta_) ≫ q = p := by
  rw [assoc, hta, G.comp_eq]

section
variable (A' : Sch) [IsAffine A'] (q) [Smooth q] [LocallyOfFiniteType q] [QuasiCompact q] (ta_) [IsClosedImmersion ta_] (hta : ta_ ≫ q = G.ambientStruct) (hker : NonzeroOnComponents (G.emb ≫ ta_).ker) (hsnc : InStrictNormalCrossingPosition q ([] : Bdy A'))
def enlargeAmbient :
    EmbeddingDatum k Y p :=
  embeddingDatumOfClosedImmersion A' q (G.emb ≫ ta_) hker (emb_comp_comp_eq_of_comp_eq G q ta_ hta) hsnc

@[simp]
theorem enlargeAmbient_ambient :
    (G.enlargeAmbient A' q ta_ hta hker hsnc).ambient = A' := rfl

@[simp]
theorem enlargeAmbient_ambientToSpec :
    (G.enlargeAmbient A' q ta_ hta hker hsnc).ambientStruct = q := rfl

@[simp]
theorem enlargeAmbient_emb :
    (G.enlargeAmbient A' q ta_ hta hker hsnc).emb = G.emb ≫ ta_ := rfl
end
end

theorem imageIdealSheaf_ker_eq_ker_comp {Yc A A' : Sch} (e : Yc ⟶ A)
    [IsClosedImmersion e] (σ : A ⟶ A') :
    imageIdealSheaf σ (ker e) = ker (e ≫ σ) :=
  symm $ ker_comp e σ

theorem isomorphic_embeddedResolutionRule_enlargeAmbient [IsAffine Y]
    [IsReduced Y] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (G : EmbeddingDatum k Y p) (Alg : PrincipalizationAlgorithm) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg)
    (A' : Sch) [IsAffine A']
    (q : A' ⟶ Sp k) [Smooth q]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (ta_ : G.ambient ⟶ A') [IsClosedImmersion ta_]
    (hta : ta_ ≫ q = G.ambientStruct)
    (hker : NonzeroOnComponents (G.emb ≫ ta_).ker)
    (hsnc : InStrictNormalCrossingPosition q ([] : Bdy A'))
    (c : ℕ) (hc : 1 ≤ c) (hcodim : HasEtaleCoordCodim q ta_ c) :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p G).Isomorphic
      (embeddedResolutionRuleOfPrincipalization Alg hw k Y p $ G.enlargeAmbient A' q ta_ hta hker hsnc) := by
  let _a0 := G.enlargeAmbient A' q ta_ hta hker hsnc
  let _a1 := IsPushforwardBlowupSeq ta_ (G.toEmbeddedBlowupSequence Alg).ambientSeq ((G.enlargeAmbient A' q ta_ hta hker hsnc).toEmbeddedBlowupSequence Alg).ambientSeq
  have _i5 : _a1 := by
    have himg :=
      imageIdealSheaf_ker_eq_ker_comp G.emb ta_
    have hJ : NonzeroOnComponents $ imageIdealSheaf ta_ $ ker G.emb := by simp_all
    have key : ∀ J (hJ' : NonzeroOnComponents J),
        J = ker (G.emb ≫ ta_) →
        IsPushforwardBlowupSeq ta_ (G.toEmbeddedBlowupSequence Alg).ambientSeq
          (Alg k A' q J hJ' ([]) hsnc).toSequenceOfBlowups →
        _a1 := by
      rintro J hJ' rfl h
      exact h
    exact key _ hJ himg
      (hAlg.pushforward k G.ambient A' G.ambientStruct q ta_ hta c hc hcodim
        (ker G.emb) G.nonzeroOnComponents_ker hJ G.sncEmpty hsnc)
  have P :=
    @ChartPushforward.ofIsPushforwardSeq k _ _ Y _ p _ (G.toEmbeddedBlowupSequence Alg)
      (_a0.toEmbeddedBlowupSequence Alg) ta_
      (inferInstanceAs $ IsClosedImmersion ta_) rfl
      _i5
  exact P.inducedBlowupsWithoutIso_isomorphic (hw k Y p G) $ hw k Y p _a0


end EmbeddingDatum





namespace ChartFlatBaseChange

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]
  {k' : Type} [Field k'] [CharZero k'] {Y'} [IsAffine Y']
  {pY'} [LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

theorem congr_hom_apply {A B : Sch} {f g : A ⟶ B} (e : f = g) (a : A) :
    f a = g a := by
  subst e
  rfl

section
variable (F : ChartFlatBaseChange S S')
section
variable (j) (hj : j < S'.length) (hsg_ : F.reindex j ≤ F.reindex (j + 1))
@[reassoc]
theorem levelMap_succ_comp_transitionMap :
    F.levelMap (j + 1) (succ_le_of_lt hj) ≫ S.ambientSeq.transitionMap hsg_ =
      S'.blowdown j ≫ F.levelMap j (le_of_lt hj) := by
  have hsg_' := F.reindex_lt_succ j hj
  have key : S.ambientSeq.transitionMap hsg_' ≫ S.blowdown (F.reindex j) = S.ambientSeq.transitionMap hsg_ := by
    rw [show S.blowdown (F.reindex j) = S.ambientSeq.transitionMap (le_succ $ F.reindex j) from
        S.ambientSeq.blowupMorphism_eq_transitionMap _, S.ambientSeq.transitionMap_trans]
  have hw := (F.isPullback_step j hj hsg_').w
  rwa [assoc, key] at hw

@[reassoc]
theorem strictTransformComparison_succ_comp_strictTransformMapOfLE :
    F.strictTransformComparison (j + 1) (succ_le_of_lt hj) ≫ S.strictTransformMapOfLE hsg_ =
      S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) := by
  let _a1 := S.strictTransformio $ F.reindex j
  have : Mono _a1 := inferInstance
  rw [← cancel_mono _a1]
  let _a0 := S'.strictTransformio (j + 1) ≫ (S'.blowdown j ≫ F.levelMap j (le_of_lt hj))
  have e1 : (F.strictTransformComparison (j + 1) (succ_le_of_lt hj) ≫ S.strictTransformMapOfLE hsg_) ≫
        _a1
      = _a0 := by
    rw [assoc, S.strictTransformMapOfLE_strictTransformio, ← assoc, F.strictTransformComparison_comp_strictTransformio,
      assoc, F.levelMap_succ_comp_transitionMap j hj hsg_]
  have e2 : (S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj)) ≫ _a1
      = _a0 := by
    rw [assoc, F.strictTransformComparison_comp_strictTransformio, ← assoc, S'.strictTransformMap_comp_strictTransformio, assoc]
  rw [e1, e2]
end

section
variable [hv1_0 : IsReduced Y] [hv1_1 : IsReduced Y']
include hv1_0 hv1_1
@[reassoc]
theorem inr_totalSpaceMap (j : ℕ) (hj : j ≤ S'.length) :
    (coprod.inr : S'.detachedCoprod j ⟶ S'.totalSpace j) ≫ F.totalSpaceMap j hj =
      F.inactiveTotalMap j hj ≫
        (coprod.inr : S.detachedCoprod (F.reindex j) ⟶ S.totalSpace (F.reindex j)) := by
  simp [ChartFlatBaseChange.totalSpaceMap]

theorem totalTransition_comp_totalSpaceMap j (hj : j < S'.length)
    (hsg_ : F.reindex j ≤ F.reindex (j + 1)) :
    S'.totalTransition j ≫ F.totalSpaceMap j (le_of_lt hj) =
      F.totalSpaceMap (j + 1) (succ_le_of_lt hj) ≫ S.totalMapOfLE hsg_ := by
  apply coprod.hom_ext
  have e1 : (coprod.inl : S'.strictTransform (j + 1) ⟶ S'.totalSpace (j + 1)) ≫
        (S'.totalTransition j ≫ F.totalSpaceMap j (le_of_lt hj))
      = S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) ≫ coprod.inl := by
    rw [← assoc, S'.inl_totalTransition, assoc, F.inl_totalSpaceMap]
  have e2 : (coprod.inl : S'.strictTransform (j + 1) ⟶ S'.totalSpace (j + 1)) ≫
        (F.totalSpaceMap (j + 1) (succ_le_of_lt hj) ≫ S.totalMapOfLE hsg_)
      = S'.strictTransformMap j ≫ F.strictTransformComparison j (le_of_lt hj) ≫ coprod.inl := by
    rw [← assoc, F.inl_totalSpaceMap, assoc, S.inl_totalMapOfLE,
      ← assoc, F.strictTransformComparison_succ_comp_strictTransformMapOfLE j hj hsg_, assoc]
  rw [e1, e2]
  apply S'.detachedCoprod_hom_ext $ j + 1
  intro s hs
  rcases lt_succ_iff_lt_or_eq.mp hs with hlt | heq
  have h1 := F.detachedToCoprod_inr_totalSpaceMap (j + 1) (succ_le_of_lt hj) s hs
  rw [reassoc_of% h1, ← S.detachedToCoprod_detachedCoprodMapOfLE (F.reindex_lt_reindex hlt $ le_of_lt hj) hsg_, S'.detachedToCoprod_succ_of_lt s j hlt]
  simp only [assoc]
  rw [S'.detachedCoprodInl_inr_totalTransition_assoc j $ F.totalSpaceMap j $ le_of_lt hj, F.detachedToCoprod_inr_totalSpaceMap j (le_of_lt hj) s hlt, S.detachedCoprodMapOfLE_inr_totalMapOfLE hsg_]
  subst heq
  rw [reassoc_of% (F.detachedToCoprod_inr_totalSpaceMap (s + 1) (succ_le_of_lt hj) s hs), S.detachedToCoprod_inr_totalMapOfLE hsg_ (le_refl $ F.reindex s)
      (F.reindex_lt_succ s hj), S.strictTransformMapOfLE_self]
  rw [S'.detachedToCoprod_self s]
  simp only [id_comp]
  rw [S'.detachedCoprodInr_inr_totalTransition_assoc s $ F.totalSpaceMap s $ le_of_lt hj,
    F.inl_totalSpaceMap, F.detachedSchemeComparison_comp_detachedio_assoc s hj coprod.inl]

theorem totalCenter_eq_comap i (hi : i < S'.length) :
    S'.totalCenter i = (S.totalCenter $ F.reindex i).comap (F.totalSpaceMap i hi.le) := by
  apply idealSheafData_ext_coprod
  have l1 : (S'.totalCenter i).comap
      coprod.inl = S'.centerOffDetached i := by
    rw [S'.totalCenter_eq, ker_comp_coprod_inl_comap_inl,
      q2]
  have l2 : (S.totalCenter $ F.reindex i).comap
      (coprod.inl : S.strictTransform (F.reindex i) ⟶ S.totalSpace (F.reindex i))
      = S.centerOffDetached (F.reindex i) := by
    rw [S.totalCenter_eq, ker_comp_coprod_inl_comap_inl,
      q2]
  rw [l1, ← comap_comp, F.inl_totalSpaceMap,
    comap_comp, l2, ← F.centerOffDetached_eq_comap i hi]
  have r1 : (S'.totalCenter i).comap
      coprod.inr = ⊤ := by
    rw [S'.totalCenter_eq]
    exact ker_comp_coprod_inl_comap_inr _
  rw [r1, ← comap_comp, F.inr_totalSpaceMap,
    comap_comp, S.totalCenter_eq,
    ker_comp_coprod_inl_comap_inr]
  simp
end

theorem comap_center_eq_top_of_not_mem_range_reindex (h : S.TransitionsAreBlowups) (i : ℕ)
    (hi : i < S.length) (hskip : ∀ j, j < S'.length → F.reindex j ≠ i) :
    (center (S.inducedBlowups h) i).comap (pullback.snd F.baseMap $ projectionToBase (S.inducedBlowups h) i) = ⊤ := by
  let _c0 := (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
  rw [inducedBlowups_center]
  apply comap_eq_top_of_notMem_support
  intro x hx
  rw [S.totalCenter_eq] at hx
  let _a0 := projectionToBase (S.inducedBlowups h) i
  let _a4 := S.centerOffDetached i
  let _a2 := range $ ⇑(siI _a4 ≫ _c0)
  have hmem : (pullback.snd F.baseMap _a0) x ∈
      closure _a2 := by
    rwa [← support_ker]
  have hrange : _a2
      ⊆ (⇑_c0) ''
        (↑_a4.support : Set $ S.strictTransform i) := by
    rintro y ⟨t, rfl⟩
    refine ⟨siI _a4 t, ?_, sy_ $ m135 _ _ t⟩
    rw [← q5]
    exact mem_range_self t
  have hce :=
    AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
      _c0
  have hclosed :=
    hce.isClosedMap _ _a4.support.2
  obtain ⟨a, ha, hax⟩ := (closure_minimal hrange hclosed) hmem
  have ha2 :=
    S.support_centerOffDetached_subset_preimage i ha
  set b := (pullback.fst F.baseMap _a0) x with hb
  have hcond := congr_hom_apply (pullback.condition (f := F.baseMap)
    (g := _a0)) x
  rw [m135, m135] at hcond
  have hstr : _a0 (_c0 a)
      = (S.strictTransformToBase i) a :=
    congr_hom_apply (FunctorialResolution.EmbeddedResolution.inl_inducedBlowups_projectionToBase S h i) a
  have hemb := congr_hom_apply F.isPullback_emb.w b
  rw [comp_apply, comp_apply] at hemb
  have hae := congr_hom_apply (S.strictTransformToBase_emb i) a
  rw [comp_apply, comp_apply] at hae
  let _a3 := (S.strictTransformio i) a
  have hcompat : F.ambientMap (S'.emb b) = (S.ambientSeq.projectionToBase i) _a3 := by
    rw [← hemb, ← hae, ← hstr, hax, ← hcond]
  obtain ⟨z, hz1, hz2⟩ :=
    m198 (S'.emb b) _a3 hcompat
  let _a1 := pullback.snd F.ambientMap $ S.ambientSeq.projectionToBase i
  have hcs := F.comap_center_skipped i hi (fun j hj => hskip j hj)
    (pullback F.ambientMap $ S.ambientSeq.projectionToBase i)
    _a1
    (pullback.fst F.ambientMap $ S.ambientSeq.projectionToBase i)
    ((of_hasPullback F.ambientMap $ S.ambientSeq.projectionToBase i).flip)
  have hz0 : _a1 z ∈
      (S.ambientCenter i).support := by
    rwa [hz2]
  have hz : z ∈ ((S.ambientCenter i).comap
      _a1).support := by
    rwa [m19]
  rw [hcs] at hz
  simp at hz
  exact hz

def inducedBlowupsSchemeAtIsoPullback [IsReduced Y]
    [IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
    (i : ℕ) (hi : i ≤ (S'.inducedBlowups h').length) :
    schemeAt (S'.inducedBlowups h') i ≅ pullback F.baseMap (projectionToBase (S.inducedBlowups h) $ F.reindex i) :=
  ((F.isPullback_totalSpaceMap h h' i
    (by rwa [inducedBlowups_length] at hi)).flip).isoPullback

section
variable [hv1_0 : IsReduced Y] [hv1_1 : IsReduced Y'] (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups)
include hv1_0 hv1_1
section
variable (i) (hi : i ≤ (S'.inducedBlowups h').length)
theorem inducedBlowupsIso_hom_fst :
    (F.inducedBlowupsSchemeAtIsoPullback h h' i hi).hom ≫ pullback.fst F.baseMap (projectionToBase (S.inducedBlowups h) $ F.reindex i)
      = projectionToBase (S'.inducedBlowups h') i :=
  isoPullback_hom_fst _

theorem inducedBlowupsIso_hom_snd :
    (F.inducedBlowupsSchemeAtIsoPullback h h' i hi).hom ≫ pullback.snd F.baseMap (projectionToBase (S.inducedBlowups h) $ F.reindex i)
      = F.totalSpaceMap i (by rwa [inducedBlowups_length] at hi) :=
  isoPullback_hom_snd _
end

theorem isPullbackUpToEmptyCenters_inducedBlowups :
    IsPullbackUpToEmptyCenters F.baseMap (S'.inducedBlowups h') $ S.inducedBlowups h := by
  refine ⟨F.reindex, fun i hi => F.inducedBlowupsSchemeAtIsoPullback h h' i hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  intro i hi
  rw [inducedBlowups_length] at hi ⊢
  exact F.reindex_lt i hi
  intro i j hj hij
  rw [inducedBlowups_length] at hj
  exact F.reindex_lt_reindex_of_lt hij hj
  rw [inducedBlowups_length, inducedBlowups_length]
  exact F.reindex_len
  intro i hi hns
  have hi' : i < S.length := by rwa [inducedBlowups_length] at hi
  have hskip : ∀ j, j < S'.length → F.reindex j ≠ i := by simp_all
  rintro ⟨x, hx⟩
  rw [F.comap_center_eq_top_of_not_mem_range_reindex h i hi' hskip] at hx
  simp at hx
  exact hx
  intro i hi
  exact F.inducedBlowupsIso_hom_fst h h' i hi
  intro i hi hr
  have hi' : i < S'.length := by rwa [inducedBlowups_length] at hi
  apply pullback.hom_ext
  rw [assoc, F.inducedBlowupsIso_hom_fst, assoc,
    pullbackTransitionMap_comp_fst, F.inducedBlowupsIso_hom_fst,
    blowupMorphism_eq_transitionMap, transitionMap_comp_projectionToBase]
  rw [assoc, F.inducedBlowupsIso_hom_snd, assoc,
    pullbackTransitionMap_comp_snd, ← assoc, F.inducedBlowupsIso_hom_snd,
    FunctorialResolution.EmbeddedResolution.inducedBlowups_blowupMorphism, inducedBlowups_transitionMap]
  exact F.totalTransition_comp_totalSpaceMap i hi' hr
  intro i hi
  have hi' : i < S'.length := by rwa [inducedBlowups_length] at hi
  rw [F.inducedBlowupsIso_hom_snd, inducedBlowups_center, inducedBlowups_center]
  exact F.totalCenter_eq_comap i hi'

theorem isPullbackBlowupSequence_inducedBlowupsWithoutIso :
    IsPullbackBlowupSequence F.baseMap (S'.inducedBlowupsWithoutIso h') $ S.inducedBlowupsWithoutIso h :=
  (F.isPullbackUpToEmptyCenters_inducedBlowups h h').isPullbackSequenceOfBlowups_withoutIsoBlowups
end
end

end ChartFlatBaseChange




theorem principalizationAlgorithm_toSequenceOfBlowups_congr_ideal (A : PrincipalizationAlgorithm) (k : Type) [Field k] [CharZero k]
    (X : Sch) (p : X ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (I J : ISD X) (hIJ : I = J)
    (hI : NonzeroOnComponents I) (hJ : NonzeroOnComponents J)
    (E : Bdy X) (hE hE' : InStrictNormalCrossingPosition p E) :
    (A k X p I hI E hE).toSequenceOfBlowups = (A k X p J hJ E hE').toSequenceOfBlowups := by
  subst hIJ
  rfl

theorem isPullbackSequenceOfBlowups_congr_left {X X' : Sch} {ph_ : X' ⟶ X}
    {s1 s2 : SequenceOfBlowups X'} {t : SequenceOfBlowups X} (h : s1 = s2) (H : IsPullbackBlowupSequence ph_ s1 t) :
    IsPullbackBlowupSequence ph_ s2 t := by
  subst h
  exact H

section
variable (A) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
include hA hw
section
variable (k : Type) [Field k] [CharZero k]
theorem embeddedResolutionRule_isPullbackBlowupSequence_of_smooth (Y Y' : Sch)
    (p : Y ⟶ Sp k) (p' : Y' ⟶ Sp k)
    [LocallyOfFiniteType p] [QuasiCompact p]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType p'] [QuasiCompact p']
    [IsReduced Y'] [IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (ph_ : D'.ambient ⟶ D.ambient) [Smooth ph_] (ps_ : Y' ⟶ Y)
    (hph : ph_ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ps_ ph_ D.emb) :
    IsPullbackBlowupSequence ps_ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have : Flat ph_ := inferInstance
  have : QuasiCompact D.emb := inferInstance
  have : QuasiCompact D'.emb := inferInstance
  have hker :=
    ker_eq_comap_ker_of_isPullback_of_flat hsq.flip
  have hI' := hker ▸ D'.nonzeroOnComponents_ker
  have hE' := D'.sncEmpty
  have h0 := hA.smooth_pullback k D.ambient D.ambientStruct D.emb.ker
      D.nonzeroOnComponents_ker [] D.sncEmpty D'.ambient D'.ambientStruct ph_ hph hI' hE'
  have hpb : IsPullbackBlowupSequence ph_ (D'.toEmbeddedBlowupSequence A).ambientSeq (D.toEmbeddedBlowupSequence A).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups]
    exact isPullbackSequenceOfBlowups_congr_left
      (principalizationAlgorithm_toSequenceOfBlowups_congr_ideal A k D'.ambient D'.ambientStruct
        (D.emb.ker.comap ph_) D'.emb.ker hker.symm hI' _ [] hE' _) h0
  have hflat2 : Flat
      (show (D'.toEmbeddedBlowupSequence A).ambient ⟶ (D.toEmbeddedBlowupSequence A).ambient from ph_) :=
    (inferInstance : Flat ph_)
  rw [embeddedResolutionRuleOfPrincipalization_apply, embeddedResolutionRuleOfPrincipalization_apply]
  exact (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence A) (D'.toEmbeddedBlowupSequence A) ph_ ps_
    hsq.flip hpb).isPullbackBlowupSequence_inducedBlowupsWithoutIso _ _

theorem embeddedResolutionRule_isStrictPullbackBlowupSeq_baseChange (Y : Sch)
    (p : Y ⟶ Sp k)
    [LocallyOfFiniteType p] [QuasiCompact p]
    [IsReduced Y] [IsAffine Y]
    (D : EmbeddingDatum k Y p) (K : Type) [Field K] [CharZero K] [Algebra k K]
    [IsReduced (baseChange p K)]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (baseChange D.ambientStruct K).IdealSheafData)) :
    haveI : IsAffine (baseChange p K) := isAffine_baseChange p K
    haveI :=
      locallyOfFiniteType_baseChangeToSpec p K
    haveI :=
      quasiCompact_baseChangeToSpec p K
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (embeddedResolutionRuleOfPrincipalization A hw K (baseChange p K) (baseChangeToSpec p K)
        (D.baseChange K hker hsnc))
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have :=
    locallyOfFiniteType_baseChangeToSpec p K
  have :=
    quasiCompact_baseChangeToSpec p K
  have :=
    EmbeddingDatum.isAffine_baseChange_ambientToSpec D K
  have :=
    EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec D K
  have :=
    EmbeddingDatum.locallyOfFiniteType_baseChangeToSpec_ambientToSpec D K
  have :=
    EmbeddingDatum.quasiCompact_baseChangeToSpec_ambientToSpec D K
  have : AlgebraicGeometry.Flat (baseChangeProjection D.ambientStruct K) := inferInstance
  have : q10 (baseChangeProjection p K) := inferInstance
  have : QuasiCompact D.emb := inferInstance
  have : QuasiCompact (D.baseChangeEmb K) := inferInstance
  show IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (embeddedResolutionRuleOfPrincipalization A hw K (baseChange p K) (baseChangeToSpec p K)
        (D.baseChange K hker hsnc))
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D)
  have hkerbc :=
    ker_eq_comap_ker_of_isPullback_of_flat (D.isPullback_baseChangeEmb K).flip
  have hI' :=
    hkerbc ▸ hker
  have hE' := hsnc
  have h0 := hA.base_change k D.ambient D.ambientStruct D.emb.ker D.nonzeroOnComponents_ker
      [] D.sncEmpty K (algebraMap k K) hI' hE'
  have hpb : IsPullbackBlowupSequence (baseChangeProjection D.ambientStruct K)
      ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A).ambientSeq
      (D.toEmbeddedBlowupSequence A).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups]
    exact isPullbackSequenceOfBlowups_congr_left
      (principalizationAlgorithm_toSequenceOfBlowups_congr_ideal A K (baseChange D.ambientStruct K)
        (baseChangeToSpec D.ambientStruct K)
        (D.emb.ker.comap (baseChangeProjection D.ambientStruct K)) (D.baseChangeEmb K).ker
        hkerbc.symm hI' _ [] hE' _) h0
  have hflat2 : Flat
      (show ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A).ambient ⟶
          (D.toEmbeddedBlowupSequence A).ambient from baseChangeProjection D.ambientStruct K) :=
    (inferInstance : Flat (baseChangeProjection D.ambientStruct K))
  rw [embeddedResolutionRuleOfPrincipalization_apply, embeddedResolutionRuleOfPrincipalization_apply]
  refine IsPullbackBlowupSequence.isStrictPullback_of_surjective ?_ ?_
  exact (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence A)
    ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A) (baseChangeProjection D.ambientStruct K)
    (baseChangeProjection p K) (D.isPullback_baseChangeEmb K).flip hpb).isPullbackBlowupSequence_inducedBlowupsWithoutIso _ _
  intro i hi
  exact withoutIsoBlowups_center_ne_top ((D.toEmbeddedBlowupSequence A).inducedBlowups _) hi
end

theorem embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps :
    EmbeddedResolutionRule.IsCompatibleWithSmoothAmbientMaps $ embeddedResolutionRuleOfPrincipalization A hw := by
  intro k _ _ Y Y' p p' _ _ _ _ _ _ _ _ D D' ph_ _ ps_ hph hsq
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' ph_ ps_ hph hsq

theorem embeddedResolutionRule_isCompatibleWithFieldBaseChange :
    EmbeddedResolutionRule.IsCompatibleWithFieldBaseChange $ embeddedResolutionRuleOfPrincipalization A hw := by
  intro k _ _ Y p _ _ _ _ D K _ _ _ _ hker hsnc
  exact embeddedResolutionRule_isStrictPullbackBlowupSeq_baseChange A hA hw k Y p D K hker hsnc
end




section
variable (k : Type) [Field k]
def affineSpaceIndexedByIsoOfEquiv {N M : Type} (σ : N ≃ M) :
    affineSpaceIndexedBy k M ≅ affineSpaceIndexedBy k N where
  hom := AffineSpace.reindex σ $ Sp k
  inv := AffineSpace.reindex σ.symm $ Sp k
  hom_inv_id := by
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      rw [comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord, apply_symm_apply]
      simp
  inv_hom_id := by
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      rw [comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord, symm_apply_apply]
      simp

section
variable (N : Type)


end
end

def LocallyConstCodimImpliesConstantCodim : Prop :=
  ∀ (k : Type) [Field k] (X X' : Sch) (q : X' ⟶ Sp k)
    [Smooth q] (ta_ : X ⟶ X') [IsClosedImmersion ta_] (c : ℕ),
    HasSmoothCoordCodim q ta_ c → HasEtaleCoordCodim q ta_ c

def LinearEmbeddingsHaveLocallyConstCodim : Prop :=
  ∀ (k : Type) [Field k] (n m : ℕ),
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFS n m)
        (affineSpaceInl k n m) m ∧
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFS n m)
        (affineSpaceInrEmbedding k n m) n

theorem principalizationAlgorithm_toSequenceOfBlowups_congr (Alg : PrincipalizationAlgorithm) (k : Type) [Field k]
    [CharZero k] (X : Sch) (q : X ⟶ Sp k)
    [Smooth q] [LocallyOfFiniteType q]
    [QuasiCompact q] (I J : ISD X) (hI : NonzeroOnComponents I)
    (hJ : NonzeroOnComponents J) (E F : Bdy X) (hE : InStrictNormalCrossingPosition q E)
    (hF : InStrictNormalCrossingPosition q F) (hIJ : I = J) (hEF : E = F) :
    (Alg k X q I hI E hE).toSequenceOfBlowups = (Alg k X q J hJ F hF).toSequenceOfBlowups := by
  subst hIJ
  subst hEF
  rfl

def uliftFinAddEquivUliftSum (n m : ℕ) :
    UFin (n + m) ≃ UFS n m :=
  ulift.trans $ finSumFinEquiv.symm.trans ulift.symm

theorem flat_of_isIso {X Y : Sch} (f : X ⟶ Y) (hf : IsIso f) :
    Flat f := by
  have : IsOpenImmersion f := inferInstance
  infer_instance

section
variable (Alg) (hAlg : IsFunctorialPrincipalization Alg) (hw : TransitionsAreBlowupsForEmbeddings Alg)
include hAlg
theorem isomorphic_embeddedResolutionRuleOfPrincipalization_of_iso (k : Type) [Field k] [CharZero k] (Y : Sch)
    [IsAffine Y] [IsReduced Y]
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] (D D' : EmbeddingDatum k Y p)
    (Ph_ : D.ambient ≅ D'.ambient) (hPh : Ph_.hom ≫ D'.ambientStruct = D.ambientStruct)
    (hemb : D.emb ≫ Ph_.hom = D'.emb) :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D).Isomorphic $ embeddedResolutionRuleOfPrincipalization Alg hw k Y p D' := by
  have : QuasiCompact D.emb := inferInstance
  have : QuasiCompact D'.emb := inferInstance
  have : Flat Ph_.inv := flat_of_isIso Ph_.inv ⟨Ph_.hom, Ph_.inv_hom_id, Ph_.hom_inv_id⟩
  have : Smooth Ph_.inv := inferInstance
  have hsq : D'.emb ≫ Ph_.inv = D.emb := by
    rw [← hemb, assoc, Ph_.hom_inv_id, comp_id]
  have hpbk : IsPullback (𝟙 Y) D'.emb D.emb Ph_.inv :=
    of_horiz_isIso ⟨by rw [id_comp, hsq]⟩
  have hker : D'.emb.ker = D.emb.ker.comap Ph_.inv := ker_eq_comap_ker_of_isPullback_of_flat hpbk
  have hphp : Ph_.inv ≫ D.ambientStruct = D'.ambientStruct := by
    rw [← hPh, ← assoc, Ph_.inv_hom_id, id_comp]
  have hI' : NonzeroOnComponents $ D.emb.ker.comap Ph_.inv := by
    rw [← hker]
    exact D'.nonzeroOnComponents_ker
  have hpbseq := hAlg.smooth_pullback k D.ambient D.ambientStruct D.emb.ker
    D.nonzeroOnComponents_ker ([]) D.sncEmpty
    D'.ambient D'.ambientStruct Ph_.inv hphp hI' D'.sncEmpty
  have hseq : (Alg k D'.ambient D'.ambientStruct D'.emb.ker D'.nonzeroOnComponents_ker
        ([] : List D'.ambient.IdealSheafData) D'.sncEmpty).toSequenceOfBlowups =
      (Alg k D'.ambient D'.ambientStruct (D.emb.ker.comap Ph_.inv) hI'
        (m39 (·.comap Ph_.inv) ([] : List D.ambient.IdealSheafData))
        D'.sncEmpty).toSequenceOfBlowups :=
    principalizationAlgorithm_toSequenceOfBlowups_congr Alg k D'.ambient D'.ambientStruct _ _ _ _ _ _ _ _ hker rfl
  have hpb2 := hpbseq
  rw [← hseq, ← EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, ← EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups] at hpb2
  have hpbemb :=
    hpbk
  have hisoC : IsIso
      (show (D'.toEmbeddedBlowupSequence Alg).ambient ⟶ (D.toEmbeddedBlowupSequence Alg).ambient from Ph_.inv) :=
    ⟨Ph_.hom, Ph_.inv_hom_id, Ph_.hom_inv_id⟩
  have hflatC :=
    flat_of_isIso _ hisoC
  have hres :=
    ChartFlatBaseChange.isPullbackBlowupSequence_inducedBlowupsWithoutIso
      (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence Alg) (D'.toEmbeddedBlowupSequence Alg) Ph_.inv (𝟙 Y)
        hpbemb hpb2) (hw k Y p D) $ hw k Y p D'
  exact (isomorphic_of_isPullbackSequenceOfBlowups_id _ _ hres
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization Alg hw k Y p D)).symm

end





theorem locallyConstCodimImpliesConstantCodim : LocallyConstCodimImpliesConstantCodim := by
  intro k _ X X' q _ ta_ _ c h
  exact hasEtaleCoordCodim_of_locally_smooth_over_affineSpace q ta_ c h

theorem isIndependentOfPresentedEmbedding_embeddedResolutionRule (Alg : PrincipalizationAlgorithm)
    (hAlg : IsFunctorialPrincipalization Alg) (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism) :
    (embeddedResolutionRuleOfPrincipalization Alg hw).IsIndependentOfPresentedEmbedding :=
  by
    let hcod := locallyConstCodimImpliesConstantCodim
    let hlin : LinearEmbeddingsHaveLocallyConstCodim := by
      intro k _ n m
      exact ⟨hasSmoothCoordCodim_affineSpaceInl hsm k n m, hasSmoothCoordCodim_affineSpaceInrEmbedding hsm k n m⟩
    intro k _ _ Y p _ _ _ _ D D' P P'
    let _s0 := ULift $ Fin P.dim
    have hsA : Smooth $ affineSpaceIndexedByToSpec k _s0 :=
      hsm k P.dim
    let _s1 := ULift $ Fin P'.dim
    have hsA' : Smooth $ affineSpaceIndexedByToSpec k _s1 :=
      hsm k P'.dim
    let _a0 := UFS P.dim P'.dim
    have hsB : Smooth
        (affineSpaceIndexedByToSpec k _a0) :=
      by
      let n := P.dim
      let m := P'.dim
      have hs : Smooth $ affineSpaceIndexedByToSpec k $ UFin $ n + m :=
        hsm k $ n + m
      have h : AffineSpace.reindex (uliftFinAddEquivUliftSum n m) (Sp k) ≫
          affineSpaceIndexedByToSpec k (UFin $ n + m) =
          affineSpaceIndexedByToSpec k (UFS n m) := by
        simp [affineSpaceIndexedByToSpec]
      have : IsIso $ AffineSpace.reindex (uliftFinAddEquivUliftSum n m) $ Sp k :=
        ⟨AffineSpace.reindex (uliftFinAddEquivUliftSum n m).symm $ Sp k,
          (affineSpaceIndexedByIsoOfEquiv k $ uliftFinAddEquivUliftSum n m).hom_inv_id,
          (affineSpaceIndexedByIsoOfEquiv k $ uliftFinAddEquivUliftSum n m).inv_hom_id⟩
      have hiso : Smooth
          (AffineSpace.reindex (uliftFinAddEquivUliftSum n m) $ Sp k) :=
        inferInstance
      rw [← h]
      exact comp_mem (@Smooth) _ _ hiso hs
    let _s5 := affineSpaceInl k P.dim P'.dim
    have hciL : IsClosedImmersion _s5 :=
      isClosedImmersion_affineSpaceInl k P.dim P'.dim
    let _s4 := affineSpaceInrEmbedding k P.dim P'.dim
    have hciR : IsClosedImmersion _s4 :=
      isClosedImmersion_affineSpaceInrEmbedding k P.dim P'.dim
    let _s2 := D.emb ≫ P.toAffine
    have : IsClosedImmersion _s2 := inferInstance
    let _s3 := D'.emb ≫ P'.toAffine
    have : IsClosedImmersion _s3 := inferInstance
    have hker1 : NonzeroOnComponents $ m149 _s2 :=
      nonzeroOnComponents_ker_comp D.emb P.toAffine D.nonzeroOnComponents_ker
    have hker1' : NonzeroOnComponents $ m149 _s3 :=
      nonzeroOnComponents_ker_comp D'.emb P'.toAffine D'.nonzeroOnComponents_ker
    have hsnc1 : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k _s0)
        ([] : List (affineSpaceIndexedBy k _s0).IdealSheafData) :=
      inStrictNormalCrossingPosition_nil $ affineSpaceIndexedByToSpec k _s0
    have hsnc1' : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k _s1)
        ([] : List (affineSpaceIndexedBy k _s1).IdealSheafData) :=
      inStrictNormalCrossingPosition_nil $ affineSpaceIndexedByToSpec k _s1
    have hsncB : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k _a0)
        ([] : List
          (affineSpaceIndexedBy k _a0).IdealSheafData) :=
      inStrictNormalCrossingPosition_nil $ affineSpaceIndexedByToSpec k _a0
    have hcd1 : HasEtaleCoordCodim (affineSpaceIndexedByToSpec k _s0)
        P.toAffine P.codimBound :=
      hcod k D.ambient (affineSpaceIndexedBy k _s0)
        (affineSpaceIndexedByToSpec k _s0) P.toAffine P.codimBound
        P.locallyConstCodim
    have hcd1' : HasEtaleCoordCodim (affineSpaceIndexedByToSpec k _s1)
        P'.toAffine P'.codimBound :=
      hcod k D'.ambient (affineSpaceIndexedBy k _s1)
        (affineSpaceIndexedByToSpec k _s1) P'.toAffine P'.codimBound
        P'.locallyConstCodim
    let _a6 := _s2 ≫ affineSpaceInl k P.dim P'.dim
    have hker2 : NonzeroOnComponents
        (m149 _a6) :=
      nonzeroOnComponents_ker_comp _s2 _s5 hker1
    let _a7 := _s3 ≫ affineSpaceInrEmbedding k P.dim P'.dim
    have hker2' : NonzeroOnComponents
        (m149 _a7) :=
      nonzeroOnComponents_ker_comp _s3 _s4 hker1'
    have hcd2 : HasEtaleCoordCodim
        (affineSpaceIndexedByToSpec k _a0)
        _s5 P'.dim :=
      hcod k (affineSpaceIndexedBy k _s0)
        (affineSpaceIndexedBy k _a0)
        (affineSpaceIndexedByToSpec k _a0)
        _s5 P'.dim (hlin k P.dim P'.dim).1
    have hcd2' : HasEtaleCoordCodim
        (affineSpaceIndexedByToSpec k _a0)
        _s4 P.dim :=
      hcod k (affineSpaceIndexedBy k _s1)
        (affineSpaceIndexedBy k _a0)
        (affineSpaceIndexedByToSpec k _a0)
        _s4 P.dim (hlin k P.dim P'.dim).2
    let _a1 := D.enlargeAmbient (affineSpaceIndexedBy k _s0) (affineSpaceIndexedByToSpec k _s0) P.toAffine P.toAffine_comp hker1 hsnc1
    have hciL2 : IsClosedImmersion
        (show _a1.ambient ⟶
            affineSpaceIndexedBy k _a0 from
          affineSpaceInl k P.dim P'.dim) :=
      isClosedImmersion_affineSpaceInl k P.dim P'.dim
    let _a2 := D'.enlargeAmbient (affineSpaceIndexedBy k _s1) (affineSpaceIndexedByToSpec k _s1) P'.toAffine P'.toAffine_comp hker1' hsnc1'
    have hciR2 : IsClosedImmersion
        (show _a2.ambient ⟶
            affineSpaceIndexedBy k _a0 from
          affineSpaceInrEmbedding k P.dim P'.dim) :=
      isClosedImmersion_affineSpaceInrEmbedding k P.dim P'.dim
    have e1 := D.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
      (affineSpaceIndexedBy k _s0)
      (affineSpaceIndexedByToSpec k _s0) P.toAffine P.toAffine_comp hker1 hsnc1
      P.codimBound P.one_le_codimBound hcd1
    have e2 := _a1.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
        (affineSpaceIndexedBy k _a0)
        (affineSpaceIndexedByToSpec k _a0)
        _s5 (affineSpaceInl_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2 hsncB
        P'.dim P'.one_le_dim hcd2
    have e1' := D'.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
      (affineSpaceIndexedBy k _s1)
      (affineSpaceIndexedByToSpec k _s1) P'.toAffine P'.toAffine_comp hker1'
      hsnc1' P'.codimBound P'.one_le_codimBound hcd1'
    have e2' := _a2.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
        (affineSpaceIndexedBy k _a0)
        (affineSpaceIndexedByToSpec k _a0)
        _s4 (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2' hsncB
        P.dim P.one_le_dim hcd2'
    have hc1 : _s2 ≫ affineSpaceIndexedByToSpec k _s0 = p := by
      rw [assoc, P.toAffine_comp, D.comp_eq]
    have hc2 : _s3 ≫ affineSpaceIndexedByToSpec k _s1 = p := by
      rw [assoc, P'.toAffine_comp, D'.comp_eq]
    obtain ⟨Ph_, hPh1, hPh2⟩ :=
      hcmp k Y p P.dim P'.dim _s2 _s3 hc1 hc2
    have hembL : _a6 =
        AffineSpace.homOfVector p (coordVectorInl P.dim P'.dim _s2) :=
      comp_affineSpaceInl P.dim P'.dim p _s2 hc1
    have hembR : _a7 =
        AffineSpace.homOfVector p (coordVectorInr P.dim P'.dim _s3) :=
      comp_affineSpaceInrEmbedding P.dim P'.dim p _s3 hc2
    have hfin := hPh2
    rw [← hembR, ← hembL] at hfin
    have e3 := isomorphic_embeddedResolutionRuleOfPrincipalization_of_iso Alg hAlg hw k Y p
      (_a1.enlargeAmbient (affineSpaceIndexedBy k _a0)
          (affineSpaceIndexedByToSpec k _a0)
          _s5 (affineSpaceInl_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2 hsncB)
      (_a2.enlargeAmbient (affineSpaceIndexedBy k _a0)
          (affineSpaceIndexedByToSpec k _a0)
          _s4 (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2' hsncB)
      Ph_ hPh1 hfin
    exact e1.trans $ e2.trans $ e3.trans (e1'.trans e2').symm

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

def baseFieldToGlobalSections {X : Sch} (k : Type) [Field k]
    (p : X ⟶ Sp k) : k →+* ↑(X.presheaf.obj $ op ⊤) :=
  RingHom.comp (appTop p).hom (GSpecIso $ CommRingCat.of k).inv.hom

section
variable (k : Type) [Field k]
section
variable (M : ℕ) (a : k)
theorem exists_translateLastCoord :
    ∃ f,
      f ≫ affineSpaceIndexedByToSpec k (UFS M 1) =
          affineSpaceIndexedByToSpec k (UFS M 1) ∧
        (∀ b, pullbackCoord f (⟨inl b⟩ : UFS M 1) =
          AffineSpace.coord (Sp k)
            (⟨inl b⟩ : UFS M 1)) ∧
        (ConcreteCategory.hom $ appTop f) (lastCoordinate k M) =
          lastCoordinate k M +
            baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1) a := by
  refine ⟨m52 (affineSpaceIndexedByToSpec k $ UFS M 1)
      (fun i =>
        elim
          (fun b =>
            m9 (Sp k)
              (⟨inl b⟩ : UFS M 1))
          (fun j =>
            m9 (Sp k)
                (⟨m50 j⟩ : UFS M 1) +
              baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1) a)
          i.down),
    ?_, ?_, ?_⟩
  simp
  simp_all
  simp

def translateLastCoord : affineSpaceTimesLine k M ⟶ affineSpaceTimesLine k M :=
  (exists_translateLastCoord k M a).choose

@[simp]
theorem translateLastCoord_comp_affineSpaceIndexedByToSpec :
    translateLastCoord k M a ≫ affineSpaceIndexedByToSpec k (UFS M 1) =
      affineSpaceIndexedByToSpec k (UFS M 1) :=
  (exists_translateLastCoord k M a).choose_spec.1

theorem pullbackCoord_translateLastCoord_inl (b : Fin M) :
    pullbackCoord (translateLastCoord k M a) (⟨inl b⟩ : UFS M 1) =
      AffineSpace.coord (Sp k)
        (⟨inl b⟩ : UFS M 1) :=
  (exists_translateLastCoord k M a).choose_spec.2.1 b

theorem translateLastCoord_appTop_lastCoordinate :
    (ConcreteCategory.hom $ appTop $ translateLastCoord k M a) (lastCoordinate k M) =
      lastCoordinate k M +
        baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1) a :=
  (exists_translateLastCoord k M a).choose_spec.2.2
end

theorem baseFieldToGlobalSections_apply {X : Sch}
    (p : X ⟶ Sp k) (a : k) :
    baseFieldToGlobalSections k p a =
      (ConcreteCategory.hom $ appTop p)
        ((ConcreteCategory.hom (GSpecIso $ CommRingCat.of k).inv) a) :=
  rfl

theorem appTop_baseFieldToGlobalSections {X Y : Sch}
    (f : X ⟶ Y) (p : Y ⟶ Sp k) (a : k) :
    (ConcreteCategory.hom $ appTop f) (baseFieldToGlobalSections k p a) =
      baseFieldToGlobalSections k (f ≫ p) a := by
  rw [baseFieldToGlobalSections_apply, baseFieldToGlobalSections_apply, comp_appTop,
    m78]


section
variable (M : ℕ) (a : k)
theorem translateLastCoord_comp_translateLastCoord_neg :
    translateLastCoord k M a ≫ translateLastCoord k M (-a) = 𝟙 (affineSpaceTimesLine k M) := by
  have hstruct := translateLastCoord_comp_affineSpaceIndexedByToSpec k M
  let _a0 := affineSpaceIndexedByToSpec k $ UFS M 1
  have hconst : ∀ b c,
      (ConcreteCategory.hom $ appTop $ translateLastCoord k M b)
          (baseFieldToGlobalSections k _a0 c) =
        baseFieldToGlobalSections k _a0 c := by
    intro b c
    rw [appTop_baseFieldToGlobalSections, hstruct b]
  let _m0 := translateLastCoord k M a ≫ translateLastCoord k M (-a)
  let _a1 := affineSpaceTimesLine k M
  have H0 : _m0 ≫
      _a0 =
      𝟙 _a1 ≫ _a0 := by
    rw [assoc, hstruct, hstruct, id_comp]
  have H : ∀ i,
      (ConcreteCategory.hom $ appTop _m0)
          (AffineSpace.coord (Sp k) i) =
        (ConcreteCategory.hom $ appTop $ 𝟙 _a1)
          (AffineSpace.coord (Sp k) i) := by
    rintro ⟨b | j⟩
    have h1 := pullbackCoord_translateLastCoord_inl k M a b
    have h2 := pullbackCoord_translateLastCoord_inl k M (-a) b
    rw [pullbackCoord_def] at h1 h2
    rw [comp_appTop, CommRingCat.comp_apply, h2, h1, id_appTop,
      id_apply]
    have h1 := translateLastCoord_appTop_lastCoordinate k M a
    rw [← lastCoordinate_eq_coord k M j, comp_appTop, CommRingCat.comp_apply, translateLastCoord_appTop_lastCoordinate k M $ -a,
      map_add, h1, hconst, map_neg, id_appTop, id_apply,
      add_neg_cancel_right]
  apply AffineSpace.hom_ext
  exact H0
  exact H

def translateLastCoordIso : affineSpaceTimesLine k M ≅ affineSpaceTimesLine k M where
  hom := translateLastCoord k M a
  inv := translateLastCoord k M $ -a
  hom_inv_id := translateLastCoord_comp_translateLastCoord_neg k M a
  inv_hom_id := by
    have h := translateLastCoord_comp_translateLastCoord_neg k M $ -a
    rwa [neg_neg] at h

@[simp]
theorem translateLastCoordIso_hom :
    (translateLastCoordIso k M a).hom = translateLastCoord k M a := rfl


theorem exists_sliceAtLastCoord :
    ∃ f : affineSpaceIndexedBy k (UFin M) ⟶ affineSpaceTimesLine k M,
      f ≫ affineSpaceIndexedByToSpec k (UFS M 1) =
          affineSpaceIndexedByToSpec k (UFin M) ∧
        IsClosedImmersion f ∧
        f ≫ projLeft k M 1 = 𝟙 (affineSpaceIndexedBy k $ UFin M) ∧
        (ConcreteCategory.hom $ appTop f) (lastCoordinate k M) =
          baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFin M) a := by
  refine ⟨m52 (affineSpaceIndexedByToSpec k $ UFin M)
      (fun i =>
        elim
          (fun b =>
            m9 (Sp k) (⟨b⟩ : UFin M))
          (fun _ =>
            baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFin M) a)
          i.down),
    ?_, ?_, ?_, ?_⟩
  simp
  refine isClosedImmersion_of_coord_surjective _ ?_ ?_
  simp
  rintro ⟨b⟩
  exact ⟨m9 (Sp k)
    (⟨inl b⟩ : UFS M 1), by simp⟩
  apply m46
  rw [assoc, projLeft_comp_affineSpaceIndexedByToSpec]
  simp
  rintro ⟨b⟩
  rw [comp_appTop, m78, projLeft_appTop_coord]
  simp
  simp

def sliceAtLastCoord :
    affineSpaceIndexedBy k (UFin M) ⟶ affineSpaceTimesLine k M :=
  (exists_sliceAtLastCoord k M a).choose

@[simp]
theorem sliceAtLastCoord_comp_affineSpaceIndexedByToSpec :
    sliceAtLastCoord k M a ≫ affineSpaceIndexedByToSpec k (UFS M 1) =
      affineSpaceIndexedByToSpec k (UFin M) :=
  (exists_sliceAtLastCoord k M a).choose_spec.1
end
end

instance instIsClosedImmersionHeightSlice (k : Type) [Field k] (M : ℕ) (a : k) :
    IsClosedImmersion $ sliceAtLastCoord k M a :=
  by
  exact (exists_sliceAtLastCoord k M a).choose_spec.2.1

section
variable (k : Type) [Field k]
section
variable (M : ℕ)
section
variable (a : k)
@[simp]
theorem sliceAtLastCoord_comp_projLeft :
    sliceAtLastCoord k M a ≫ projLeft k M 1 = 𝟙 (affineSpaceIndexedBy k $ UFin M) :=
  (exists_sliceAtLastCoord k M a).choose_spec.2.2.1


theorem sliceAtLastCoord_appTop_pullbackAlongProjection
    (G : ↑((affineSpaceIndexedBy k $ UFin M).presheaf.obj $ op ⊤)) :
    (ConcreteCategory.hom $ appTop $ sliceAtLastCoord k M a) (pullbackAlongProjection k M G) = G := by
  have hp : pullbackAlongProjection k M G =
      (m23 $ appTop $ projLeft k M 1) G := rfl
  rw [hp, ← m78, ← comp_appTop, sliceAtLastCoord_comp_projLeft,
    id_appTop, id_apply]

theorem sliceAtLastCoord_appTop_lastCoordinate :
    (ConcreteCategory.hom $ appTop $ sliceAtLastCoord k M a) (lastCoordinate k M) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFin M) a :=
  (exists_sliceAtLastCoord k M a).choose_spec.2.2.2
end

section
variable {ι : Type}
section
variable [Fintype ι] [DecidableEq ι] (e : ι → k)
def sliceSeparatingFunction (i : ι) : ↑((affineSpaceTimesLine k M).presheaf.obj $ op ⊤) :=
  ∏ j ∈ Finset.univ.erase i,
    (lastCoordinate k M -
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1) (e j))

def sliceSeparatingOpen (i : ι) : (affineSpaceTimesLine k M).Opens :=
  (affineSpaceTimesLine k M).basicOpen $ sliceSeparatingFunction k M e i

def lagrangeBasisSection (j : ι) : ↑((affineSpaceTimesLine k M).presheaf.obj $ op ⊤) :=
  baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1)
      ((∏ l ∈ Finset.univ.erase j, (e j - e l))⁻¹) *
    ∏ l ∈ Finset.univ.erase j,
      (lastCoordinate k M -
        baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1) (e l))

theorem sliceAtLastCoord_appTop_sliceSeparatingFunction_eq_prod_sub (i j : ι) :
    (ConcreteCategory.hom $ appTop $ sliceAtLastCoord k M $ e j) (sliceSeparatingFunction k M e i) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFin M)
        (∏ l ∈ Finset.univ.erase i, (e j - e l)) := by
  have hdef : sliceSeparatingFunction k M e i =
      ∏ l ∈ Finset.univ.erase i,
        (lastCoordinate k M -
          baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1) (e l)) := rfl
  rw [hdef, map_prod, map_prod]
  refine prod_congr rfl fun l _ => ?_
  rw [map_sub, map_sub, sliceAtLastCoord_appTop_lastCoordinate, appTop_baseFieldToGlobalSections,
    sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]

theorem comp_sliceAtLastCoord_appTop_sliceSeparatingFunction (A : ι → Sch)
    (rh_ : ∀ i, A i ⟶ affineSpaceIndexedBy k (UFin M)) (i j : ι) :
    (ConcreteCategory.hom $ appTop $ rh_ j ≫ sliceAtLastCoord k M (e j))
        (sliceSeparatingFunction k M e i) =
      baseFieldToGlobalSections k (rh_ j ≫ affineSpaceIndexedByToSpec k (UFin M))
        (∏ l ∈ Finset.univ.erase i, (e j - e l)) := by
  rw [comp_appTop, m78, sliceAtLastCoord_appTop_sliceSeparatingFunction_eq_prod_sub,
    appTop_baseFieldToGlobalSections]

end

section
variable (e : ι → k) (A : ι → Sch) (rh_ : ∀ i, A i ⟶ affineSpaceIndexedBy k (UFin M))
def coproductSliceMap : (∐ A) ⟶ affineSpaceTimesLine k M :=
  Sigma.desc fun i => rh_ i ≫ sliceAtLastCoord k M (e i)

@[simp]
theorem sigma_io_coproductSliceMap (i : ι) :
    Sigma.ι A i ≫ coproductSliceMap k M e A rh_ = rh_ i ≫ sliceAtLastCoord k M (e i) := by
  simp [coproductSliceMap]

@[simp]
theorem sigma_io_coproductSliceMap_assoc (i : ι)
    {Z : Sch} (g : affineSpaceTimesLine k M ⟶ Z) :
    Sigma.ι A i ≫ coproductSliceMap k M e A rh_ ≫ g = rh_ i ≫ sliceAtLastCoord k M (e i) ≫ g := by
  rw [← assoc, sigma_io_coproductSliceMap, assoc]

theorem coproductSliceMap_base_sigma_io (j : ι)
    (b : ↥(A j)) :
    (coproductSliceMap k M e A rh_).base ((Sigma.ι A j).base b) =
      (rh_ j ≫ sliceAtLastCoord k M (e j)).base b := by
  show bsM (Sigma.ι A j ≫ coproductSliceMap k M e A rh_) b = bsM (rh_ j ≫ sliceAtLastCoord k M (e j)) b
  rw [sigma_io_coproductSliceMap]

abbrev coproductSliceMapReindexed :
    (∐ A) ⟶ affineSpaceIndexedBy k (UFin $ M + 1) :=
  coproductSliceMap k M e A rh_ ≫
    (affineSpaceIsoOfEquiv (uliftFinSumEquiv M 1) $ Sp k).hom

theorem coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec
    (q : (∐ A) ⟶ Sp k)
    (hq : ∀ i, Sigma.ι A i ≫ q = rh_ i ≫ affineSpaceIndexedByToSpec k (UFin M)) :
    coproductSliceMapReindexed k M e A rh_ ≫ affineSpaceIndexedByToSpec k (UFin $ M + 1) = q := by
  rw [assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
  refine hom_ext _ _ fun i => ?_
  rw [sigma_io_coproductSliceMap_assoc, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec, hq i]
end

section
variable [Fintype ι] [DecidableEq ι] (e : ι → k)
section
variable (A : ι → Sch) (rh_ : ∀ i, A i ⟶ affineSpaceIndexedBy k (UFin M))
section
variable (i j : ι)
theorem not_mem_sliceSeparatingOpen_of_ne (hne : j ≠ i)
    (b : ↥(A j)) :
    (rh_ j ≫ sliceAtLastCoord k M (e j)).base b ∉ sliceSeparatingOpen k M e i := by
  let _c0 := rh_ j ≫ sliceAtLastCoord k M (e j)
  have hzero : (∏ l ∈ Finset.univ.erase i, (e j - e l)) = 0 :=
    prod_eq_zero (mem_erase.2 ⟨hne, mem_univ j⟩) $ sub_self _
  let _a0 := (m54 _c0.base).obj $ sliceSeparatingOpen k M e i
  have hbasic : _a0 =
      (A j).basicOpen ((m23 $ appTop
        _c0) $ sliceSeparatingFunction k M e i) :=
    preimage_basicOpen _ _
  have hpre : _a0 = ⊥ := by
    rw [hbasic, comp_sliceAtLastCoord_appTop_sliceSeparatingFunction, hzero, map_zero, basicOpen_zero]
  intro hmem
  have hmem' : b ∈ _a0 :=
    hmem
  rw [hpre] at hmem'
  simp at hmem'

theorem sigma_io_comp_coproductSliceMap_appTop_sliceSeparatingFunction :
    (ConcreteCategory.hom $ appTop $ Sigma.ι A j ≫ coproductSliceMap k M e A rh_)
        (sliceSeparatingFunction k M e i) =
      baseFieldToGlobalSections k (rh_ j ≫ affineSpaceIndexedByToSpec k (UFin M))
        (∏ l ∈ Finset.univ.erase i, (e j - e l)) := by
  rw [sigma_io_coproductSliceMap]
  exact comp_sliceAtLastCoord_appTop_sliceSeparatingFunction k M e A rh_ i j

end

def componentSliceOpen
    (i : ι) : (∐ A).Opens :=
  (Opens.map (coproductSliceMap k M e A rh_).base).obj $ sliceSeparatingOpen k M e i
end

end
end

theorem sliceAtLastCoord_appTop_baseFieldToGlobalSections a x :
    (ConcreteCategory.hom $ appTop $ sliceAtLastCoord k M a)
        (baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1) x) =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFin M) x := by
  rw [appTop_baseFieldToGlobalSections, sliceAtLastCoord_comp_affineSpaceIndexedByToSpec]

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] (e) (he : Injective e)
include he
theorem sliceAtLastCoord_appTop_lagrangeSection (i j : ι) :
    (ConcreteCategory.hom $ appTop $ sliceAtLastCoord k M $ e i)
        (lagrangeBasisSection k M e j) = if j = i then 1 else 0 := by
  let _c0 := affineSpaceIndexedByToSpec k $ UFin M
  have hlag : lagrangeBasisSection k M e j =
      baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1)
          ((∏ l ∈ Finset.univ.erase j, (e j - e l))⁻¹) *
        ∏ l ∈ Finset.univ.erase j,
          (lastCoordinate k M -
            baseFieldToGlobalSections k (affineSpaceIndexedByToSpec k $ UFS M 1)
              (e l)) := rfl
  rw [hlag, map_mul, map_prod]
  simp only [map_sub, sliceAtLastCoord_appTop_baseFieldToGlobalSections, sliceAtLastCoord_appTop_lastCoordinate]
  have hprod : (∏ l ∈ Finset.univ.erase j,
        (baseFieldToGlobalSections k _c0 (e i) -
          baseFieldToGlobalSections k _c0 (e l))) =
      baseFieldToGlobalSections k _c0
        (∏ l ∈ Finset.univ.erase j, (e i - e l)) := by simp_all
  rw [hprod, ← map_mul]
  by_cases hji : j = i
  rw [if_pos hji, ← hji]
  have hne : (∏ l ∈ Finset.univ.erase j, (e j - e l)) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro l hl
    exact sub_ne_zero_of_ne fun hcon => an1 (mp_ mem_erase hl) (he hcon).symm
  rw [inv_mul_cancel₀ hne, map_one]
  have hz : (∏ l ∈ Finset.univ.erase j, (e i - e l)) = 0 :=
    prod_eq_zero (mpr_ mem_erase ⟨fun hc => hji hc.symm, mem_univ i⟩)
      (sub_self $ e i)
  rw [if_neg hji, hz, mul_zero, map_zero]

theorem sliceAtLastCoord_appTop_sum_mul_lagrangeSection
    (G : ι → ↑((affineSpaceIndexedBy k $ UFin M).presheaf.obj $ op ⊤)) (i : ι) :
    (ConcreteCategory.hom $ appTop $ sliceAtLastCoord k M $ e i)
        (∑ j : ι, pullbackAlongProjection k M (G j) * lagrangeBasisSection k M e j) = G i := by
  rw [map_sum, sum_eq_single_of_mem i $ mem_univ i]
  simp only [map_mul, sliceAtLastCoord_appTop_pullbackAlongProjection,
    sliceAtLastCoord_appTop_lagrangeSection k M e he i i]
  simp
  intro j _ hj
  simp only [map_mul, sliceAtLastCoord_appTop_lagrangeSection k M e he i j]
  rw [if_neg hj, mul_zero]
end

theorem sliceAtLastCoord_eq_affineSpaceInl_comp_translateLastCoord (a : k) :
    sliceAtLastCoord k M a = affineSpaceInl k M 1 ≫ translateLastCoord k M a := by
  apply m46
  simp_all
  rintro ⟨b | j⟩
  have h0 := sliceAtLastCoord_comp_projLeft k M a
  have h1 := congrArg
    (fun m : affineSpaceIndexedBy k (UFin M) ⟶
        affineSpaceIndexedBy k (UFin M) =>
      (m23 $ appTop m)
        (m9 (Sp k) (⟨b⟩ : UFin M))) h0
  simp only [comp_appTop, m78, projLeft_appTop_coord,
    id_appTop, id_apply] at h1
  rw [h1, comp_appTop, m78]
  have h2 := pullbackCoord_translateLastCoord_inl k M a b
  rw [pullbackCoord_def] at h2
  rw [h2]
  have h3 := pullbackCoord_affineSpaceInl_inl k M 1 b
  rw [pullbackCoord_def] at h3
  rw [h3]
  rw [← lastCoordinate_eq_coord k M j, sliceAtLastCoord_appTop_lastCoordinate, comp_appTop,
    m78, translateLastCoord_appTop_lastCoordinate, map_add, appTop_baseFieldToGlobalSections,
    affineSpaceInl_comp_affineSpaceIndexedByToSpec]
  have h4 := pullbackCoord_affineSpaceInl_inr k M 1 0
  rw [pullbackCoord_def] at h4
  rw [lastCoordinate_eq, h4, zero_add]
end

theorem coproduct_globalSections_ext {ι : Type} (A : ι → Sch)
    (q : (∐ A) ⟶ Sp k)
    (s t : ↑((∐ A).presheaf.obj $ op ⊤))
    (h : ∀ i : ι, (ConcreteCategory.hom $ appTop $ Sigma.ι A i) s =
      (ConcreteCategory.hom $ appTop $ Sigma.ι A i) t) : s = t := by
  have hv : ∀ (v : ↑(pObj (∐ A) $ op ⊤)) c,
      (m23 $ appTop
        (m52 q fun _ : UFin 1 => v))
          (m9 (Sp k) c) = v := by
    intro v c
    simp
  have hfg : m52 q (fun _ : UFin 1 => s) =
      m52 q fun _ : UFin 1 => t := by
    refine hom_ext _ _ fun i => ?_
    refine m46 ?_ ?_
    simp
    intro c
    simp only [comp_appTop, m78]
    rw [hv s c, hv t c]
    exact h i
  let _a0 := m9 (Sp k) (⟨0⟩ : UFin 1)
  calc s = m23 (appTop
        (m52 q fun _ : UFin 1 => s))
          _a0 :=
        symm $ hv s ⟨0⟩
    _ = m23 (appTop
        (m52 q fun _ : UFin 1 => t))
          _a0 := by
        rw [hfg]
    _ = t := hv t ⟨0⟩

theorem isClosedImmersion_coproductSliceMap (M : ℕ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (e : ι → k) (he : Injective e) (A : ι → Sch)
    [∀ i, IsAffine $ A i] (rh_ : ∀ i, A i ⟶ affineSpaceIndexedBy k (UFin M))
    [∀ i, IsClosedImmersion $ rh_ i] : IsClosedImmersion $ coproductSliceMap k M e A rh_ := by
  refine of_surjective_of_isAffine (coproductSliceMap k M e A rh_) ?_
  intro F
  refine ⟨∑ j : ι, pullbackAlongProjection k M (globalSectionLift k M (rh_ j)
      ((m23 $ appTop $ Sigma.ι A j) F)) *
        lagrangeBasisSection k M e j, ?_⟩
  refine coproduct_globalSections_ext k A
    (Sigma.desc fun j => rh_ j ≫ affineSpaceIndexedByToSpec k (UFin M)) _ _ fun i => ?_
  rw [← m78, ← comp_appTop, sigma_io_coproductSliceMap, comp_appTop,
    m78,
    sliceAtLastCoord_appTop_sum_mul_lagrangeSection k M e he
      (fun j => globalSectionLift k M (rh_ j)
        ((m23 $ appTop $ Sigma.ι A j) F)) i,
    appTop_globalSectionLift]
end

theorem sigma_io_base_jointly_surjective {ι : Type} (A : ι → Sch) (x : ↥(∐ A)) :
    ∃ (j : ι) (b : ↥(A j)), (Sigma.ι A j).base b = x := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk A).surjective x
  exact ⟨i, y, sy_ $ sigmaMk_mk A i y⟩

section
variable (k : Type) [Field k] (M : ℕ) {ι : Type} [Fintype ι]
section
variable [DecidableEq ι] (e : ι → k)
theorem comap_ker_coproductSliceMap_eq_of_le_sliceSeparatingOpen (A : ι → Sch)
    (rh_ : ∀ i, A i ⟶ affineSpaceIndexedBy k (UFin M)) [∀ i, IsClosedImmersion $ rh_ i]
    (i : ι) (U : (affineSpaceTimesLine k M).Opens) (hU : U ≤ sliceSeparatingOpen k M e i) :
    (ker $ coproductSliceMap k M e A rh_).comap U.i =
      (ker $ rh_ i ≫ sliceAtLastCoord k M (e i)).comap U.i := by
  let _c0 := coproductSliceMap k M e A rh_
  have : QuasiCompact _c0 := by
    have hqcj : ∀ j, QuasiCompact $ rh_ j ≫ sliceAtLastCoord k M (e j) := fun j => inferInstance
    refine ⟨fun V hV1 hV2 => ?_⟩
    let _a0 := coproductSliceMap k M e A rh_
    have hset : ⇑_a0.base ⁻¹' V =
        ⋃ j, ⇑(Sigma.ι A j).base '' (⇑(rh_ j ≫ sliceAtLastCoord k M (e j)).base ⁻¹' V) := by
      apply m15
      intro y hy
      obtain ⟨j, b, rfl⟩ := sigma_io_base_jointly_surjective A y
      refine mem_iUnion.2 ⟨j, b, ?_, rfl⟩
      show bsM (rh_ j ≫ sliceAtLastCoord k M (e j)) b ∈ V
      rwa [← coproductSliceMap_base_sigma_io k M e A rh_ j b]
      intro y hy
      obtain ⟨j, hj⟩ := mem_iUnion.1 hy
      obtain ⟨b, hb, rfl⟩ := hj
      show bsM _a0 (bsM (Sigma.ι A j) b) ∈ V
      rwa [coproductSliceMap_base_sigma_io]
    rw [hset]
    exact isCompact_iUnion fun j => (QuasiCompact.isCompact_preimage (f := rh_ j ≫ sliceAtLastCoord k M (e j)) V hV1 hV2).image (Sigma.ι A j).continuous
  let _a0 := rh_ i ≫ sliceAtLastCoord k M (e i)
  have : QuasiCompact _a0 := inferInstance
  let _a2 := (m54 _a0.base).obj U
  let _a3 := Sigma.ι A i
  have hfun : ⇑(p4 (X := A i)
        _a2 ≫ _a3).base =
      ⇑_a3.base ∘
        ⇑(p4 (X := A i)
          _a2).base :=
    funext fun _ => rfl
  have hrange :
      range ⇑(p4 (X := A i)
          _a2 ≫ _a3).base =
        range ⇑(p4 (X := ∐ A)
          ((m54 _c0.base).obj U)).base := by
    rw [hfun, range_comp, q1, q1]
    show ⇑_a3.base '' (⇑_a0.base ⁻¹'
        U) =
      m142 _c0.base U
    apply m15
    rintro _ ⟨b, hb, rfl⟩
    show bsM _c0 (bsM _a3 b) ∈ U
    rwa [coproductSliceMap_base_sigma_io]
    intro y hy
    obtain ⟨j, b, rfl⟩ := sigma_io_base_jointly_surjective A y
    have hb : bsM (rh_ j ≫ sliceAtLastCoord k M (e j)) b ∈ U := by
      have hy' : bsM _c0 (bsM (Sigma.ι A j) b) ∈
          U := hy
      rwa [coproductSliceMap_base_sigma_io] at hy'
    rcases eq_or_ne j i with rfl | hne
    exact ⟨b, hb, rfl⟩
    exact absurd (hU hb) $ not_mem_sliceSeparatingOpen_of_ne k M e A rh_ i j hne b
  refine tr_ (ker_comap_io_eq_ker_of_isIso_comp _c0 U
      (mrU _a0 U)
      (isoOfRangeEq _ _ hrange).hom ?_)
    (ker_comap_io_eq_ker_morphismRestrict _a0 U).symm
  rw [← cancel_mono U.i, assoc, morphismRestrict_ι, ← assoc,
    isoOfRangeEq_hom_fac, assoc, sigma_io_coproductSliceMap, morphismRestrict_ι]

section
variable (he : Injective e) (A : ι → Sch) (rh_ : ∀ i, A i ⟶ affineSpaceIndexedBy k (UFin M)) (i : ι)
include he
theorem exists_iso_componentSliceOpen :
    ∃ ph_ : A i ≅ (↑(componentSliceOpen k M e A rh_ i) : Sch),
      ph_.hom ≫ (componentSliceOpen k M e A rh_ i).i = Sigma.ι A i := by
  let _a3 := coproductSliceMap k M e A rh_
  let _a4 := sliceSeparatingOpen k M e i
  let _a5 := sliceSeparatingFunction k M e i
  let _a1 := componentSliceOpen k M e A rh_ i
  let _a2 := Sigma.ι A i
  have hrange : range _a2.base = range _a1.ib := by
    let _a0 := _a4
    rw [q1]
    refine m15 ?_ ?_
    rintro x ⟨y, rfl⟩
    have hy : y ∈ (m54 (_a2 ≫ _a3).base).obj
        _a0 := by
      have _i12 : (m54 (Sigma.ι A i ≫ _a3).base).obj _a4 = ⊤ := by
        let _a0 := Sigma.ι A i ≫ _a3
        have hpre : (m54 _a0.base).obj _a4 =
            (A i).basicOpen ((m23 $ appTop
              _a0) _a5) :=
          preimage_basicOpen _ _
        rw [hpre, sigma_io_comp_coproductSliceMap_appTop_sliceSeparatingFunction k M e A rh_ i i]
        have hne : (∏ l ∈ Finset.univ.erase i, (e i - e l)) ≠ 0 := by
          exact Finset.prod_ne_zero_iff.mpr fun l hl => sub_ne_zero_of_ne fun hcon => an1 (mp_ mem_erase hl) (he hcon).symm
        apply basicOpen_of_isUnit
        exact IsUnit.map (baseFieldToGlobalSections k $ rh_ i ≫ affineSpaceIndexedByToSpec k (UFin M))
          (mpr_ isUnit_iff_ne_zero hne)
      rw [_i12]
      simp
    exact hy
    intro x hx
    obtain ⟨j, y, rfl⟩ := sigma_io_base_jointly_surjective A x
    by_cases hij : j = i
    subst hij
    exact mem_range_self y
    exfalso
    have hy : y ∈ (m54 (Sigma.ι A j ≫ _a3).base).obj
        _a0 := hx
    have _i11 : (m54 (Sigma.ι A j ≫ _a3).base).obj _a4 = ⊥ := by
      let _a0 := Sigma.ι A j ≫ _a3
      have hpre : (m54 _a0.base).obj _a4 =
          (A j).basicOpen ((m23 $ appTop
            _a0) _a5) :=
        preimage_basicOpen _ _
      have hzero : (∏ l ∈ Finset.univ.erase i, (e j - e l)) = 0 :=
        prod_eq_zero (mpr_ mem_erase ⟨hij, mem_univ j⟩) $ sub_self $ e j
      rw [hpre, sigma_io_comp_coproductSliceMap_appTop_sliceSeparatingFunction k M e A rh_ i j, hzero, map_zero]
      simp
    rw [_i11] at hy
    have hy' : y ∈ ((⊥ : Opn $ A j) : Set ↥(A j)) := hy
    rw [coe_bot] at hy'
    exact mp_ (mem_empty_iff_false y) hy'
  refine ⟨isoOfRangeEq _a2 _a1.i hrange, ?_⟩
  apply isoOfRangeEq_hom_fac

def componentIsoSliceOpen :
    A i ≅ (↑(componentSliceOpen k M e A rh_ i) : Sch) :=
  (exists_iso_componentSliceOpen k M e he A rh_ i).choose

@[simp]
theorem componentIsoSliceOpen_hom_comp_io :
    (componentIsoSliceOpen k M e he A rh_ i).hom ≫ (componentSliceOpen k M e A rh_ i).i = Sigma.ι A i :=
  (exists_iso_componentSliceOpen k M e he A rh_ i).choose_spec
end
end
end

section
variable (hsm : AffineSpaceIsSmooth) (k : Type) [Field k] (M c : ℕ)
include hsm
section
variable {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → k) (he : Injective e) (A : ι → Sch) [∀ i, IsAffine (A i)] (rh_ : ∀ i, A i ⟶ affineSpaceIndexedBy k (UFin M)) [∀ i, IsClosedImmersion (rh_ i)] (h : ∀ i, HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (UFin M)) (rh_ i) c)
include he h
theorem hasSmoothCoordCodim_coproductSliceMap :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFS M 1)
      (coproductSliceMap k M e A rh_) $ c + 1 := by
  rw [hasSmoothCoordCodim_iff]
  intro x
  obtain ⟨i, a, rfl⟩ := sigma_io_base_jointly_surjective A x
  have hpiece : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFS M 1) ((rh_ i) ≫ sliceAtLastCoord k M (e i)) $ c + 1 := by
    let a := e i
    let σ := rh_ i
    have h2 := (HasSmoothCoordCodim.comp_affineSpaceInl hsm k σ 1 $ h i).comp_iso_hom (translateLastCoordIso k M a)
        (affineSpaceIndexedByToSpec k $ UFS M 1) $ by simp
    rwa [sliceAtLastCoord_eq_affineSpaceInl_comp_translateLastCoord, ← assoc]
  rw [hasSmoothCoordCodim_iff] at hpiece
  obtain ⟨W, hW, q, hqS, hqstruct, hkerW⟩ := hpiece a
  refine ⟨W ⊓ sliceSeparatingOpen k M e i, ?_,
    (affineSpaceTimesLine k M).homOfLE (inf_le_left) ≫ q, inferInstance, ?_, ?_⟩
  show bsM (coproductSliceMap k M e A rh_) (bsM (Sigma.ι A i) a) ∈ W ⊓ sliceSeparatingOpen k M e i
  rw [coproductSliceMap_base_sigma_io]
  let _a2 := rh_ i ≫ sliceAtLastCoord k M (e i)
  have _i9 : bsM _a2 a ∈ sliceSeparatingOpen k M e i := by
    let _c0 := _a2
    have hne0 : (∏ l ∈ Finset.univ.erase i, (e i - e l)) ≠ 0 := by
      rw [prod_ne_zero_iff]
      intro l hl
      exact sub_ne_zero.2 fun hx => (mem_erase.1 hl).1 (he hx).symm
    have hunit : IsUnit $ (m23 $ appTop _c0)
        (sliceSeparatingFunction k M e i) := by
      rw [comp_sliceAtLastCoord_appTop_sliceSeparatingFunction]
      exact IsUnit.map _ $ isUnit_iff_ne_zero.2 hne0
    have hbasic : (m54 _c0.base).obj (sliceSeparatingOpen k M e i) =
        (A i).basicOpen ((m23 $ appTop
          _c0) $ sliceSeparatingFunction k M e i) :=
      preimage_basicOpen _ _
    have hpre : (m54 _c0.base).obj (sliceSeparatingOpen k M e i) = ⊤ := by
      rw [hbasic]
      exact (A i).basicOpen_of_isUnit hunit
    have hmem : a ∈ (m54 _c0.base).obj (sliceSeparatingOpen k M e i) := by
      rw [hpre]
      trivial
    exact hmem
  exact ⟨hW, _i9⟩
  rw [assoc, hqstruct, ← assoc, Scheme.homOfLE_ι]
  have hcrux := comap_ker_coproductSliceMap_eq_of_le_sliceSeparatingOpen k M e A rh_ i (W ⊓ sliceSeparatingOpen k M e i)
    inf_le_right
  rw [comap_comp, ← hkerW, restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io,
    ← comap_comp, Scheme.homOfLE_ι]
  exact hcrux

theorem hasSmoothCoordCodim_coproductSliceMapReindexed :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFin $ M + 1)
      (coproductSliceMapReindexed k M e A rh_) $ c + 1 := by
  have := isClosedImmersion_coproductSliceMap k M e he A rh_
  let _a0 := uliftFinSumEquiv M 1
  exact (hasSmoothCoordCodim_coproductSliceMap hsm k M c e he A rh_ h).comp_iso_hom
    (affineSpaceIsoOfEquiv _a0 $ Sp k)
    (affineSpaceIndexedByToSpec k $ UFin $ M + 1)
    (affineSpaceIsoOfEquiv_hom_comp_toSpec k _a0)
end
end





structure PresentedLocalChart {k : Type} [Field k] [CharZero k] {Y V : Sch}
    {pY : Y ⟶ Sp k} {pV : V ⟶ Sp k}
    {G : EmbeddingDatum k Y pY} (P : ClosedEmbeddingIntoAffineSpace G) (H : EmbeddingDatum k V pV)
    (u : V ⟶ Y) (r : ℕ) (y : ↥V) extends SmoothLocalChart G H u y where
  threshold : ℕ
  presentation : ∀ N : ℕ, threshold ≤ N →
    ∃ σ : ambient ⟶ affineSpaceIndexedBy k (UFin $ P.dim + N + 1),
      IsClosedImmersion σ ∧
      σ ≫ affineSpaceIndexedByToSpec k (UFin $ P.dim + N + 1) = ambientStruct ∧
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFin $ P.dim + N + 1) σ
        (P.codimBound + (N - r) + 1)

theorem nonempty_presentedLocalChart (hS : SmoothPullbackHasLocalAmbientEmbedding)
    (hsm : AffineSpaceIsSmooth) (k : Type) [Field k] [CharZero k] (Y V : Sch)
    [IsAffine Y] [IsAffine V]
    (pY : Y ⟶ Sp k) (pV : V ⟶ Sp k)
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G) (H : EmbeddingDatum k V pV)
    (u : V ⟶ Y) (r : ℕ) [SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) (y : ↥V) :
    Nonempty $ PresentedLocalChart P H u r y := by
  classical
  obtain ⟨V0, hyV0, hV0aff_, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, gg, hgsm, hgp, jj, hjci,
      hjpb, N0, hrN0, hpres⟩ :=
    hS k Y V G.ambient pY pV G.ambientStruct G.emb G.comp_eq P.dim P.codimBound P.toAffine
      P.toAffine_comp P.locallyConstCodim r u hu y
  obtain ⟨sg0, hsg0ci, hsg0comp, hsg0codim⟩ := hpres N0 le_rfl
  have hembCI : IsClosedImmersion H.emb := H.isClosedImmersion_emb
  obtain ⟨Ω, hOm, hOmeq⟩ := (H.emb.isClosedEmbedding.toIsEmbedding.toIsInducing).isOpen_iff.mp V0.isOpen
  have hyOm : H.emb.base y ∈ Ω := by
    have h0 : y ∈ preimage H.emb.base Ω := by rw [hOmeq]
                                              exact hyV0
    exact h0
  obtain ⟨Ubase, hUmem, hyU, hUOm⟩ :=
    isBasis_iff_nbhd.mp (isBasis_basicOpen H.ambient)
      (U := (⟨Ω, hOm⟩ : H.ambient.Opens)) (x := H.emb.base y) hyOm
  obtain ⟨func, rfl⟩ := hUmem
  let _s0 := H.emb ⁻¹ᵁ H.ambient.basicOpen func
  have hsub : _s0 ≤ V0 := by
    intro x hx
    have hx2 : x ∈ preimage H.emb.base Ω := hUOm hx
    rwa [hOmeq] at hx2
  let _s1 := UFin $ P.dim + N0
  let _a10 := opI V0 ≫ H.emb
  let _a4 := (m23 $ appTop _a10) func
  let _a9 := jj ≫ sg0
  let _a5 := m23 $ appTop _a9
  obtain ⟨L, hL⟩ : ∃ L : Γ(affineSpaceIndexedBy k _s1, ⊤),
      _a5 L
        = _a4 :=
    ⟨_, appTop_globalSectionLift k (P.dim + N0) _a9 _⟩
  obtain ⟨Fsec, hopen⟩ : ∃ Fsec : Γ(A', ⊤),
      jj ⁻¹ᵁ (bOpn A' Fsec) = opI V0 ⁻¹ᵁ _s0 := by
    let _a6 := (m23 $ appTop sg0) L
    refine ⟨_a6, ?_⟩
    let _a1 := bOpn (affineSpaceIndexedBy k _s1) L
    have eA : bOpn A' _a6
        = sg0 ⁻¹ᵁ _a1 :=
      (preimage_basicOpen sg0 L).symm
    have e1 : jj ⁻¹ᵁ
          (sg0 ⁻¹ᵁ _a1)
        = _a9 ⁻¹ᵁ
          _a1 := rfl
    have eB : _a9 ⁻¹ᵁ
          _a1
        = bOpn (↑V0 : Sch)
            (_a5 L) :=
      preimage_basicOpen _ _
    have e2 : opI V0 ⁻¹ᵁ _s0
        = _a10 ⁻¹ᵁ (H.ambient.basicOpen func) := rfl
    have eC : _a10 ⁻¹ᵁ (H.ambient.basicOpen func)
        = bOpn (↑V0 : Sch)
            _a4 :=
      preimage_basicOpen _ _
    rw [eA, e1, eB, hL, e2, eC]
  obtain ⟨th_, hth⟩ : ∃ th_ : oSch _s0 ≅
      (jj ⁻¹ᵁ bOpn A' Fsec).toScheme,
      isoH th_ ≫ (opI (jj ⁻¹ᵁ bOpn A' Fsec) ≫ opI V0)
        = opI _s0 := by
    have hrange : range ⇑(opIb _s0)
        = range ⇑(opI (jj ⁻¹ᵁ bOpn A' Fsec) ≫ opI V0).base := by
      have hcomp : range ⇑(opI (jj ⁻¹ᵁ bOpn A' Fsec) ≫ opI V0).base
          = ⇑V0.ι.base '' range ⇑(opIb $ jj ⁻¹ᵁ bOpn A' Fsec) := by
        simp [range_comp]
      rw [hcomp, hopen, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      have h4 : (↑(opI V0 ⁻¹ᵁ _s0) : Set ↥V0.toScheme)
          = preimage V0.ι.base (↑_s0) := rfl
      rw [h4, image_preimage_eq_inter_range, Scheme.Opens.range_ι]
      exact sy_ $ inter_eq_self_of_subset_left fun x hx => hsub hx
    exact ⟨isoOfRangeEq _ _ hrange,
      isoOfRangeEq_hom_fac _ _ hrange⟩
  have hth' : (isoH th_ ≫ opI (jj ⁻¹ᵁ bOpn A' Fsec)) ≫ opI V0
      = opI _s0 := by simp_all
  let _a2 := morphismRestrict jj $ bOpn A' Fsec
  let _a3 := opI (bOpn A' Fsec) ≫ gg
  let _a11 := opI _s0 ≫ u
  have hcomm : CategoryTheory.CommSq th_.hom
      _a11
      (opI (jj ⁻¹ᵁ bOpn A' Fsec) ≫ (opI V0 ≫ u)) $ 𝟙 Y := by
    constructor
    rw [comp_id, ← assoc, ← assoc, hth']
  have hpb : CategoryTheory.IsPullback
      (isoH th_ ≫ _a2)
      _a11
      _a3 G.emb := by
    have h5 := (of_horiz_isIso hcomm).paste_horiz $ (m226 jj $ bOpn A' Fsec).paste_vert hjpb
    rwa [id_comp] at h5
  refine ⟨{
    func := func
    mem_domain := hyU
    ambient := (bOpn A' Fsec).toScheme
    ambientStruct := (bOpn A' Fsec).ι ≫ pA'
    isAffine_ambient := (isAffineOpen_top A').basicOpen Fsec
    smooth_ambientStruct := by infer_instance
    locallyOfFiniteType_ambientStruct := by infer_instance
    quasiCompact_ambientStruct := by infer_instance
    toAmbient := _a3
    smooth_toAmbient := by infer_instance
    comp_eq := by rw [assoc, hgp]
    imm := isoH th_ ≫ _a2
    isPullback := hpb
    threshold := N0
    presentation := by
      intro N hN
      obtain ⟨σ, hsgci, hsgcomp, hsgcodim⟩ := hpres N hN
      refine ⟨basicOpenEmbedding k (P.dim + N) σ Fsec ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv (P.dim + N) 1)
            (Sp k)).hom, by infer_instance, ?_, ?_⟩
      rw [assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
      exact basicOpenEmbedding_comp_affineSpaceIndexedByToSpec k (P.dim + N) σ Fsec pA' hsgcomp
      exact hasSmoothCoordCodim_basicOpenEmbedding hsm k (P.dim + N)
        (P.codimBound + (N - r)) σ Fsec hsgcodim }⟩





theorem isZariskiLocalAtSource_locallyOfFiniteType :
    IsZariskiLocalAtSource $ @LocallyOfFiniteType.{0} := by
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@LocallyOfFiniteType.{0}) _ inferInstance

theorem isZariskiLocalAtSource_flat :
    IsZariskiLocalAtSource $ @Flat.{0} := by
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Flat.{0}) _ inferInstance

section
variable {ι : Type} {X : ι → Sch} {Z : Sch} (f : ∀ i, X i ⟶ Z)
theorem locallyOfFiniteType_sigmaDesc (hf : ∀ i, LocallyOfFiniteType (f i)) :
    LocallyOfFiniteType $ desc f := by
  have := isZariskiLocalAtSource_locallyOfFiniteType
  exact sigmaDesc hf

theorem flat_sigmaDesc (hf : ∀ i, Flat (f i)) : Flat $ desc f := by
  have := isZariskiLocalAtSource_flat
  exact sigmaDesc hf
end

theorem exists_etaleCover_closedEmbeddingIntoAffineSpace_of_localCharts (hsm : AffineSpaceIsSmooth)
    (k : Type) [Field k] [CharZero k]
    (hsnc : ∀ (A : Sch) (q : A ⟶ Sp k),
      Smooth q → InStrictNormalCrossingPosition q [])
    (Y V : Sch) (pY : Y ⟶ Sp k)
    (pV : V ⟶ Sp k)
    [IsAffine Y] [IsAffine V]
    [IsReduced Y] [IsReduced V]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G)
    (H : EmbeddingDatum k V pV) (Q : ClosedEmbeddingIntoAffineSpace H)
    (u : V ⟶ Y) (r : ℕ) (hu : u ≫ pY = pV)
    (ι : Type) [Fintype ι] [DecidableEq ι] (pt : ι → ↥V)
    (ch : ∀ i, PresentedLocalChart P H u r (pt i))
    (N : ℕ) (hN : ∀ i, (ch i).threshold ≤ N)
    (hcov : (⨆ i, (ch i).chartDomain) = ⊤) :
    ∃ (V'' : Sch) (pV'' : V'' ⟶ Sp k) (c : V'' ⟶ V),
      IsAffine V'' ∧ IsReduced V'' ∧
      LocallyOfFiniteType pV'' ∧ QuasiCompact pV'' ∧
      Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ pV = pV'' ∧
      (∃ (G' : EmbeddingDatum k V'' pV'') (f : G'.ambient ⟶ G.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace G') ∧
        Smooth f ∧ f ≫ G.ambientStruct = G'.ambientStruct ∧
        CategoryTheory.IsPullback G'.emb (c ≫ u) f G.emb) ∧
      (∃ (H' : EmbeddingDatum k V'' pV'') (g : H'.ambient ⟶ H.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace H') ∧
        Smooth g ∧ g ≫ H.ambientStruct = H'.ambientStruct ∧
        CategoryTheory.IsPullback H'.emb c g H.emb) := by
  let _a0 := isoH (affineSpaceIsoOfEquiv (uliftFinSumEquiv Q.dim 1) (Sp k))
  let _a1 := affineSpaceIndexedByToSpec k $ UFin (Q.dim + 1)
  classical
  have hsubs : Subsingleton ↥(Sp k) := inferInstance
  have hDaff := fun i =>
    (ch i).isAffineOpen_chartDomain
  have hambaff := fun i => (ch i).isAffine_ambient
  have hBaff := fun i =>
    (isAffineOpen_top H.ambient).basicOpen ((ch i).func)
  have hVaff :=
    isAffine_sigmaOpens V _ fun i => (ch i).isAffineOpen_chartDomain
  have hVcs : CompactSpace ↥(sigmaOpens V fun i => (ch i).chartDomain) := inferInstance
  obtain ⟨e, he⟩ : ∃ e, m120 e := by
    refine ⟨fun i => ((Fintype.equivFin ι i) : k), fun a b hab => ?_⟩
    exact (Fintype.equivFin ι).injective (Fin.eq_of_val_eq (cast_injective hab))
  refine ⟨sigmaOpens V (fun i => (ch i).chartDomain),
    (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV,
    sigmaOpensDesc V (fun i => (ch i).chartDomain),
    hVaff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton .., inferInstance,
    surjective_sigmaOpensDesc V _ hcov, rfl, ?_, ?_⟩
  have hpullbackG : IsPullback (map fun i => (ch i).imm)
      ((sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ u)
      (desc fun i => (ch i).toAmbient) G.emb := by
    have h0 :=
      isPullback_sigmaMap_sigmaDesc G.emb (fun i => (ch i).ambient)
        (fun i => oSch ((ch i).chartDomain)) (fun i => (ch i).imm)
        (fun i => opI ((ch i).chartDomain) ≫ u) (fun i => (ch i).toAmbient)
        (fun i => (ch i).isPullback)
    have hdescu : (desc fun i => opI ((ch i).chartDomain) ≫ u)
        = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ u := by
      refine hom_ext _ _ fun i => ?_
      simp
    rwa [hdescu] at h0
  have hsmfG :=
    smooth_sigmaDesc _ fun i => (ch i).smooth_toAmbient
  have hstructeq : (desc fun i => (ch i).toAmbient) ≫ G.ambientStruct
      = desc fun i => (ch i).ambientStruct := by
    refine hom_ext _ _ fun i => ?_
    simp [(ch i).comp_eq]
  have hsmstructG :
      Smooth ((desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) := by
    rw [hstructeq]
    exact smooth_sigmaDesc _ fun i => (ch i).smooth_ambientStruct
  have hlftstructG :
      LocallyOfFiniteType ((desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) := by
    rw [hstructeq]
    exact locallyOfFiniteType_sigmaDesc _ fun i => (ch i).locallyOfFiniteType_ambientStruct
  have hGaff : IsAffine (∐ fun i => (ch i).ambient) := inferInstance
  have hGcs : CompactSpace ↥(∐ fun i => (ch i).ambient) := inferInstance
  have hqcstructG :
      QuasiCompact ((desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) :=
    quasiCompact_of_compactSpace_of_subsingleton ..
  have hCIembG :=
    m98 (P := @IsClosedImmersion)
      hpullbackG.flip G.isClosedImmersion_emb
  have hqcGemb : QuasiCompact G.emb := inferInstance
  have hqcembG :=
    quasiCompact_of_isPullback hpullbackG.flip
  have hflatfG : Flat (desc fun i => (ch i).toAmbient) :=
    flat_sigmaDesc _ fun i => inferInstance
  have hkerG :=
    ker_eq_comap_ker_of_isPullback_of_flat hpullbackG.flip
  have hnzG : NonzeroOnComponents (map fun i => (ch i).imm).ker := by
    rw [hkerG]
    exact NonzeroOnComponents.comap_of_flat G.nonzeroOnComponents_ker _
  have hcompG : (map fun i => (ch i).imm) ≫
      ((desc fun i => (ch i).toAmbient) ≫ G.ambientStruct)
      = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV := by
    rw [← assoc, hpullbackG.w, assoc, G.comp_eq, assoc, hu]
  refine ⟨embeddingDatumOfClosedImmersion (∐ fun i => (ch i).ambient)
      ((desc fun i => (ch i).toAmbient) ≫ G.ambientStruct)
      (map fun i => (ch i).imm) hnzG hcompG (hsnc _ _ hsmstructG),
    desc fun i => (ch i).toAmbient, ⟨?_⟩, hsmfG, rfl, hpullbackG⟩
  have hpres := fun i => (ch i).presentation N (hN i)
  choose σ hsgCI hsgcomp hsgcod using hpres
  have hsgCI' : ∀ i, IsClosedImmersion (σ i) := hsgCI
  have hCIunionG :=
    isClosedImmersion_coproductSliceMap k (P.dim + N + 1) e he (fun i => (ch i).ambient) σ
  have hCIfinG :
      IsClosedImmersion (coproductSliceMapReindexed k (P.dim + N + 1) e (fun i => (ch i).ambient) σ) :=
    inferInstance
  refine ⟨P.codimBound + (N - r) + 1 + 1, P.dim + N + 1 + 1,
    coproductSliceMapReindexed k (P.dim + N + 1) e (fun i => (ch i).ambient) σ, by omega, by omega,
    hCIfinG, ?_, ?_⟩
  refine coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec k (P.dim + N + 1) e (fun i => (ch i).ambient) σ _ ?_
  intro i
  show Limits.Sigma.ι (fun j => (ch j).ambient) i ≫
      ((desc fun j => (ch j).toAmbient) ≫ G.ambientStruct) =
      σ i ≫ affineSpaceIndexedByToSpec k (UFin (P.dim + N + 1))
  simp [(ch i).comp_eq, hsgcomp i]
  exact hasSmoothCoordCodim_coproductSliceMapReindexed hsm k (P.dim + N + 1)
    (P.codimBound + (N - r) + 1) e he (fun i => (ch i).ambient) σ hsgcod
  have hpullbackH :=
    isPullback_sigmaMap_sigmaDesc H.emb
      (fun i => oSch (H.ambient.basicOpen ((ch i).func)))
      (fun i => oSch ((ch i).chartDomain))
      (fun i => H.emb ∣_ H.ambient.basicOpen ((ch i).func))
      (fun i => opI ((ch i).chartDomain))
      (fun i => opI (H.ambient.basicOpen ((ch i).func)))
      (fun i => (ch i).isPullback_morphismRestrict_basicOpen)
  have hlftg : LocallyOfFiniteType
      (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen $ (ch i).func) :=
    inferInstance
  have hflatg : Flat (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen $ (ch i).func) :=
    flat_sigmaDesc _ fun i => inferInstance
  have hHaff :=
    isAffine_sigmaOpens H.ambient _ fun i =>
      (isAffineOpen_top H.ambient).basicOpen ((ch i).func)
  have hHcs :
      CompactSpace ↥(sigmaOpens H.ambient fun i => H.ambient.basicOpen $ (ch i).func) :=
    inferInstance
  have hlftq : LocallyOfFiniteType
      ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen $ (ch i).func) ≫
        H.ambientStruct) := inferInstance
  have hqcq : QuasiCompact
      ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen $ (ch i).func) ≫
        H.ambientStruct) := quasiCompact_of_compactSpace_of_subsingleton ..
  have hCIembH :=
    m98 (P := @IsClosedImmersion)
      hpullbackH.flip H.isClosedImmersion_emb
  have hqcHemb : QuasiCompact H.emb := inferInstance
  have hqcembH :=
    quasiCompact_of_isPullback hpullbackH.flip
  have hkerH :=
    ker_eq_comap_ker_of_isPullback_of_flat hpullbackH.flip
  have hnzH : NonzeroOnComponents
      (map fun i => H.emb ∣_ H.ambient.basicOpen ((ch i).func)).ker := by
    rw [hkerH]
    exact NonzeroOnComponents.comap_of_flat H.nonzeroOnComponents_ker _
  have hcompH :
      (map fun i => H.emb ∣_ H.ambient.basicOpen ((ch i).func)) ≫
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen $ (ch i).func) ≫
          H.ambientStruct)
        = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV := by
    rw [← assoc, hpullbackH.w, assoc, H.comp_eq]
  refine ⟨embeddingDatumOfClosedImmersion
      (sigmaOpens H.ambient fun i => H.ambient.basicOpen $ (ch i).func)
      ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen $ (ch i).func) ≫ H.ambientStruct)
      (map fun i => H.emb ∣_ H.ambient.basicOpen ((ch i).func))
      hnzH hcompH (hsnc _ _ inferInstance),
    sigmaOpensDesc H.ambient (fun i => H.ambient.basicOpen $ (ch i).func), ⟨?_⟩, smooth_sigmaDesc _ fun i => inferInstance, rfl,
    hpullbackH⟩
  have hCIrho : ∀ i, IsClosedImmersion
      (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
        _a0) :=
    fun i => inferInstance
  have hrhocomp : ∀ i,
      (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
        _a0) ≫
          _a1
        = opI (H.ambient.basicOpen ((ch i).func)) ≫ H.ambientStruct := by
    intro i
    rw [assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
    exact basicOpenEmbedding_comp_affineSpaceIndexedByToSpec k Q.dim Q.toAffine ((ch i).func) H.ambientStruct
      Q.toAffine_comp
  have hrhocod :=
    fun i => hasSmoothCoordCodim_basicOpenEmbedding hsm k Q.dim Q.codimBound Q.toAffine
      ((ch i).func) Q.locallyConstCodim
  have hCIunionH :=
    isClosedImmersion_coproductSliceMap k (Q.dim + 1) e he
      (fun i => oSch (H.ambient.basicOpen ((ch i).func)))
      (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
        _a0)
  have hCIfinH : IsClosedImmersion
      (coproductSliceMapReindexed k (Q.dim + 1) e (fun i => oSch (H.ambient.basicOpen ((ch i).func)))
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          _a0)) :=
    inferInstance
  refine ⟨Q.codimBound + 1 + 1, Q.dim + 1 + 1,
    coproductSliceMapReindexed k (Q.dim + 1) e (fun i => oSch (H.ambient.basicOpen ((ch i).func)))
      (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
        _a0),
    by omega, by omega, hCIfinH, ?_, ?_⟩
  refine coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec k (Q.dim + 1) e
    (fun i => oSch (H.ambient.basicOpen ((ch i).func)))
    (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
      _a0) _ ?_
  intro i
  show Limits.Sigma.ι (fun j => oSch (H.ambient.basicOpen ((ch j).func))) i ≫
      ((sigmaOpensDesc H.ambient fun j => H.ambient.basicOpen $ (ch j).func) ≫
        H.ambientStruct) =
      (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
        _a0) ≫
        _a1
  rw [hrhocomp i]
  simp
  exact hasSmoothCoordCodim_coproductSliceMapReindexed hsm k (Q.dim + 1) (Q.codimBound + 1) e he
    (fun i => oSch (H.ambient.basicOpen ((ch i).func)))
    (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
      _a0)
    hrhocod

theorem exists_etaleCover_closedEmbeddingIntoAffineSpace_of_smooth
    (hS : SmoothPullbackHasLocalAmbientEmbedding) (hsm : AffineSpaceIsSmooth)
    (k : Type) [Field k] [CharZero k]
    (hsnc : ∀ (A : Sch) (q : A ⟶ Sp k),
      Smooth q → InStrictNormalCrossingPosition q [])
    (Y V : Sch) (pY : Y ⟶ Sp k)
    (pV : V ⟶ Sp k)
    [IsAffine Y] [IsAffine V]
    [IsReduced Y] [IsReduced V]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G)
    (H : EmbeddingDatum k V pV) (Q : ClosedEmbeddingIntoAffineSpace H)
    (u : V ⟶ Y) (r : ℕ) [SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    ∃ (V'' : Sch) (pV'' : V'' ⟶ Sp k) (c : V'' ⟶ V),
      IsAffine V'' ∧ IsReduced V'' ∧
      LocallyOfFiniteType pV'' ∧ QuasiCompact pV'' ∧
      Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ pV = pV'' ∧
      (∃ (G' : EmbeddingDatum k V'' pV'') (f : G'.ambient ⟶ G.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace G') ∧
        Smooth f ∧ f ≫ G.ambientStruct = G'.ambientStruct ∧
        CategoryTheory.IsPullback G'.emb (c ≫ u) f G.emb) ∧
      (∃ (H' : EmbeddingDatum k V'' pV'') (g : H'.ambient ⟶ H.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace H') ∧
        Smooth g ∧ g ≫ H.ambientStruct = H'.ambientStruct ∧
        CategoryTheory.IsPullback H'.emb c g H.emb) := by
  classical
  have hch := fun y =>
    nonempty_presentedLocalChart hS hsm k Y V pY pV G P H u r hu y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y => ((((hch y).some.chartDomain) : Opn V) : Set ↥V))
    (fun y => ((hch y).some.chartDomain).isOpen)
    (by intro x _; exact mpr_ mem_iUnion ⟨x, (hch x).some.mem_domain⟩)
  obtain ⟨N, hN⟩ : ∃ N, ∀ i : { y : ↥V // y ∈ t }, ((hch i.1).some).threshold ≤ N :=
    ⟨Finset.univ.sup fun i : { y : ↥V // y ∈ t } => ((hch i.1).some).threshold,
      fun i => le_sup
        (f := fun i : { y : ↥V // y ∈ t } => ((hch i.1).some).threshold) $ mem_univ i⟩
  refine exists_etaleCover_closedEmbeddingIntoAffineSpace_of_localCharts hsm k hsnc Y V pY pV G P H Q u r hu
    { y : ↥V // y ∈ t } (·.1) (fun i => (hch i.1).some) N hN ?_
  refine m55 ?_
  rw [coe_iSup, coe_top]
  refine eq_univ_of_univ_subset fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp $ ht $ Set.mem_univ x
  exact mpr_ mem_iUnion ⟨⟨y, hy⟩, hxy⟩





section
variable (E : EmbeddedResolutionRule) (C : PresentedSelection) (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps) (hprop : E.HasProperCenters) (hS : SmoothPullbackHasLocalAmbientEmbedding) (hsm : AffineSpaceIsSmooth) (hsnc : ∀ (k : Type) [Field k] [CharZero k] (A : Sch) (q : A ⟶ Sp k), Smooth q → InStrictNormalCrossingPosition q [])
include hinv hsbc hprop hS hsm hsnc
theorem isPullbackBlowupSequence_presentedSelection_of_smooth
    (k : Type) [Field k] [CharZero k] (Y V : Sch)
    (pY : Y ⟶ Sp k) (pV : V ⟶ Sp k)
    [IsAffine Y] [IsAffine V]
    [IsReduced Y] [IsReduced V]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    IsPullbackBlowupSequence u (E k V pV $ C.sel k V pV) $ E k Y pY $ C.sel k Y pY := by
  let _a0 := C.sel k Y pY
  let _a1 := C.sel k V pV
  obtain ⟨V'', pV'', c, hV''aff, hV''red, hV''ft, hV''qc, hcet, hcsurj, hcpV,
      ⟨G', f, hG'pres, hfsm, hfcomp, hfpb⟩, ⟨H', g, hH'pres, hgsm, hgcomp, hgpb⟩⟩ :=
    exists_etaleCover_closedEmbeddingIntoAffineSpace_of_smooth hS hsm k (fun A q hq => hsnc k A q hq)
      Y V pY pV _a0 (C.pres k Y pY) _a1 (C.pres k V pV) u r hu
  have := hV''aff
  have := hV''red
  have := hV''ft
  have := hV''qc
  have := hcet
  have := hcsurj
  have := hfsm
  have := hgsm
  have := smooth r u
  have : Flat u := inferInstance
  have : Flat c := inferInstance
  let _a2 := E k Y pY _a0
  have hB' := (isStrictPullbackSequenceOfBlowups_baseChange _a2 u).isPullbackSequenceOfBlowups_withoutIsoBlowups
  have hCc :=
    isStrictPullbackSequenceOfBlowups_baseChange
      ((_a2.baseChange u).withoutIsoBlowups) c
  exact hB'.of_isomorphic (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic ((hsbc k V V'' pV pV'' _a1 H' g c hgcomp hgpb).isStrictPullback_of_surjective fun i hi => hprop k V pV _a1 i hi) hCc $ (hinv k V'' pV'' G' H' hG'pres.some hH'pres.some).symm.trans $ (hsbc k Y V'' pY pV'' _a0 G' f (c ≫ u) hfcomp hfpb).isomorphic $ hB'.comp_isStrictPullbackSequenceOfBlowups hCc).symm

theorem isCompatibleWithOpenImmersions_toAffineResolutionRule :
    IsCompatibleWithOpenImmersions $ E.toAffineResolutionRule C.sel := by
  intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ ph_ _ hph
  have : m158 0 ph_ := inferInstance
  exact isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y V pY pV
    ph_ 0 hph

theorem isCompatibleWithEtaleCovers_toAffineResolutionRule :
    IsCompatibleWithEtaleCovers $ E.toAffineResolutionRule C.sel := by
  intro k _ _ Y W pY pW _ _ _ _ _ _ _ _ ph_ _ hph hsurj
  have : m158 0 ph_ := inferInstance
  have : q10 ph_ := ⟨hsurj⟩
  exact (isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y W pY pW ph_ 0 hph).isStrictPullback_of_surjective
    (fun i hi => hprop k Y pY (C.sel k Y pY) i hi)
end




theorem smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth (hsm : AffineSpaceIsSmooth) :
    SmoothPullbackHasLocalAmbientEmbedding :=
  by
    intro k _ _ X Y A pX pY pA _ _ _ _ i _ hi M c rh_ _ hrh_ hrhc r h _ hh y
    obtain ⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci,
      hjpb, n, q, hnqr, σ, hsgci, hsgcomm, F, De_, hkersg, hDtop, hgrsm⟩ :=
        smoothPullbackHasGraphChart k X Y A pX pY pA i hi M rh_ hrh_ r h hh y
    have := hA'aff
    have := hsgci
    refine ⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci, hjpb,
      n, by omega, ?_⟩
    intro N hN
    obtain ⟨p, rfl⟩ : ∃ p, N = n + p := ⟨N - n, by omega⟩
    rw [show M + (n + p) = M + n + p from by omega,
      show c + (n + p - r) = c + q + p from by omega]
    have hcc : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k $ UFS M n) σ $ c + q := by
      let hrh_ := hrhc
      let rh' := σ
      classical
      have hker' : ker rh' =
          (ker rh_).comap (projLeft k M n) ⊔
            ofIdealTop (span $ range F) := by
        rw [ker_eq_ofIdealTop_ker_appTop rh', hkersg, ofIdealTop_sup,
          ker_eq_ofIdealTop_ker_appTop rh_, comap_ofIdealTop]
      let _a0 := (affineSpaceIndexedBy k $ UFS M n).basicOpen De_
      have hcomapEq : (coordSubspaceIdeal k q univ).comap
            (graphMorphismToAffineSpace k M n q F _a0
              ≫ projRight k M q)
          = (ofIdealTop $ span $ range F).comap
              _a0.i := by
        have hset :
            ⇑(m4 $ appTop
                (graphMorphismToAffineSpace k M n q F
                  _a0
                  ≫ projRight k M q)) ''
              range (fun j =>
                m9 (Sp k) $ up j)
            = ⇑(m4 $ appTop
                _a0.i) ''
              range F := by
          rw [← range_comp, ← range_comp]
          refine congrArg range $ funext fun j => ?_
          show (m23 $ appTop
                (graphMorphismToAffineSpace k M n q F
                  _a0
                  ≫ projRight k M q))
                (m9 (Sp k) $ up j)
              = (m23 $ appTop
                  _a0.i) (F j)
          rw [appTop_comp_hom_apply, projRight_appTop_coord, graphMorphismToAffineSpace_appTop_coord_inr]
        rw [coordSubspaceIdeal_univ_eq_ofIdealTop, comap_ofIdealTop_span,
          comap_ofIdealTop_span, hset]
      intro x
      obtain ⟨U0_, hU0_, q0, hq0s, hq0o, hq0k⟩ := hrh_ $ bsM g x
      have := hq0s
      have hmem1 : bsM (projLeft k M n) (bsM rh' x) ∈ U0_ := by
        have hb : bsM (rh' ≫ projLeft k M n) x = bsM (g ≫ rh_) x := by rw [hsgcomm]
        simpa using (hb ▸ hU0_)
      have hmem2 : bsM rh' x ∈
          _a0 := by
        have hx : x ∈ rh' ⁻¹ᵁ _a0 := by
          rw [hDtop]
          trivial
        exact hx
      set U : (affineSpaceIndexedBy k $ UFS M n).Opens :=
        (projLeft k M n ⁻¹ᵁ U0_) ⊓
          _a0 with hUdef
      have hUD : U ≤ _a0 := by simp_all
      set G : U.toScheme ⟶ affineSpaceIndexedBy k (UFS M q) :=
        (affineSpaceIndexedBy k $ UFS M n).homOfLE hUD ≫
          graphMorphismToAffineSpace k M n q F _a0
        with hGdef
      let _a4 := projLeft k M q
      have hGproj : G ≫ _a4 = U.ι ≫ projLeft k M n := by
        rw [hGdef, assoc, graphMorphismToAffineSpace_comp_projLeft, ← assoc, Scheme.homOfLE_ι]
      let _s0 := projLeft k M q ⁻¹ᵁ U0_
      have hsub : range ⇑G.base ⊆ range ⇑(opIb _s0) := by
        rw [Scheme.Opens.range_ι]
        rintro y ⟨z, rfl⟩
        have hz : bsM (G ≫ _a4) z = bsM (U.i ≫ projLeft k M n) z := by rw [hGproj]
        have hz' : bsM _a4 (bsM G z) = bsM (projLeft k M n) (U.ib z) := by
          simpa using hz
        show bsM _a4 (bsM G z) ∈ U0_
        rw [hz']
        exact an1 $ z.2
      set L : U.toScheme ⟶ _s0.toScheme :=
        m43 _s0.i G hsub with hLdef
      have hLfac :=
        m115 _ _ hsub
      have hGsmooth : Smooth G := by
        rw [hGdef]
        have := hgrsm
        infer_instance
      have hLsmooth : Smooth L := by
        refine smooth_of_smooth_comp_isOpenImmersion L _s0.i ?_
        rwa [hLfac]
      set P : _s0.toScheme ⟶ affineSpaceIndexedBy k (UFS c q) :=
        prodMapOnPreimage k M q c U0_ q0 with hPdef
      set chart : U.toScheme ⟶ affineSpaceIndexedBy k (UFin $ c + q) :=
        L ≫ P ≫ isoH (affineSpaceIsoOfEquiv (uliftFinSumEquiv c q) $ Sp k)
        with hchartdef
      refine ⟨U, ⟨hmem1, hmem2⟩, chart, ?_, ?_, ?_⟩
      have := hLsmooth
      have := smooth_prodMapOnPreimage hsm k M q c U0_ q0 hq0o
      rw [hchartdef]
      infer_instance
      rw [hchartdef, assoc, assoc,
        affineSpaceIsoOfEquiv_hom_comp_toSpec, hPdef, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec, ← assoc,
        hLfac, hGdef, assoc, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec, ← assoc, Scheme.homOfLE_ι]
      have hA : (coordSubspaceIdeal k c univ).comap (L ≫ P ≫ projLeft k c q)
          = (ker rh_).comap (U.i ≫ projLeft k M n) := by
        rw [hPdef, ← morphismRestrict_projLeft_comp k M q c U0_ q0 hq0o,
          comap_comp, comap_comp, ← hq0k,
          restrictIdeal_eq_comap_io, ← comap_comp,
          ← comap_comp, assoc, morphismRestrict_ι,
          ← assoc, hLfac, hGproj]
      have hB : (coordSubspaceIdeal k q univ).comap (L ≫ P ≫ projRight k c q)
          = (ofIdealTop $ span $ range F).comap U.i := by
        rw [hPdef, prodMapOnPreimage_comp_projRight, ← assoc, hLfac, hGdef, assoc,
          comap_comp, hcomapEq, ← comap_comp,
          Scheme.homOfLE_ι]
      have key : (coordSubspaceIdeal k (c + q) univ).comap chart
          = (coordSubspaceIdeal k c univ).comap (L ≫ P ≫ projLeft k c q)
            ⊔ (coordSubspaceIdeal k q univ).comap (L ≫ P ≫ projRight k c q) := by
        rw [hchartdef, comap_comp, comap_comp,
          coordSubspaceIdeal_univ_comap_affineSpaceIsoOfEquiv, comap_sup,
          comap_sup]
        simp [← comap_comp]
      have key2 : restrictIdeal (ker rh') U
          = (ker rh_).comap (U.i ≫ projLeft k M n)
            ⊔ (ofIdealTop $ span $ range F).comap U.i := by simp_all
      rw [key2, key, hA, hB]
    have : IsClosedImmersion
        (σ ≫ isoH (affineSpaceIsoOfEquiv (uliftFinSumEquiv M n) $ Sp k)) :=
      inferInstance
    have hpad := HasSmoothCoordCodim.comp_affineSpaceInl_affineSpaceIsoOfEquiv hsm k
        (σ ≫ isoH (affineSpaceIsoOfEquiv (uliftFinSumEquiv M n) $ Sp k)) p $ HasSmoothCoordCodim.comp_iso_hom hcc (affineSpaceIsoOfEquiv (uliftFinSumEquiv M n) $ Sp k) (affineSpaceIndexedByToSpec k $ UFin $ M + n) $ affineSpaceIsoOfEquiv_hom_comp_toSpec k $ uliftFinSumEquiv M n
    refine ⟨(σ ≫ isoH (affineSpaceIsoOfEquiv (uliftFinSumEquiv M n) $ Sp k)) ≫
        affineSpaceInl k (M + n) p ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv (M + n) p) $ Sp k).hom,
      inferInstance, ?_, hpad⟩
    simp [assoc]
    rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, affineSpaceIsoOfEquiv_hom_comp_toSpec, ← projLeft_comp_affineSpaceIndexedByToSpec, ← assoc,
      hsgcomm, assoc, hrh_, hgpA]

section
variable (A) (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A) (hemb : AffineEmbedsIntoAffineSpace) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm) (hcmp : ClosedEmbeddingsRelatedByAutomorphism)
include hAlg hw hcmp
theorem isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization :
    IsCompatibleWithOpenImmersions $ affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex :=
  by
    have key := isCompatibleWithOpenImmersions_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
      (affineSpacePresentedSelection hemb hsncE hsm)
      (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
      (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
      (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm) hsm nilIsStrictNormalCrossingsOfSmooth
    rw [affineSpacePresentedSelection_selection,
      toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
    exact key

theorem isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization :
    IsCompatibleWithEtaleCovers $ affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex :=
  by
    have key := isCompatibleWithEtaleCovers_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
      (affineSpacePresentedSelection hemb hsncE hsm)
      (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
      (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
      (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm) hsm nilIsStrictNormalCrossingsOfSmooth
    rw [affineSpacePresentedSelection_selection,
      toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
    exact key

end




namespace OpenImmersionRestriction

abbrev principalizationOfEmbedding (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm) :
    IdealBlowupSequence D.ambientStruct (ker D.emb) [] :=
  A k D.ambient D.ambientStruct (ker D.emb)
    D.nonzeroOnComponents_ker [] D.sncEmpty


section
variable {V} (hV : IdealSheafGeometryHypotheses V)
include hV
theorem disjoint_detachedComponent_of_principalizationCertificate
    {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
    {pY} [LocallyOfFiniteType pY]
    (S : EmbeddedBlowupSequence k Y pY) i
    [NoetherianSpace ↥(S.strictTransform i)]
    I Mem
    (hcl : IsClosedEmbedding ⇑(S.strictTransformio i).base)
    (hmem : ∀ C ∈ irreducibleComponents ↥(S.strictTransform i),
      ∀ xi_ : ↥(S.strictTransform i), IsGenericPoint xi_ C → ((S.strictTransformio i).base xi_) ∉ Mem)
    (hagree : ∀ C ∈ irreducibleComponents ↥(S.strictTransform i),
      ∀ xi_ : ↥(S.strictTransform i), IsGenericPoint xi_ C →
      ∀ hC : IsClosed $ ⇑(S.strictTransformio i).base '' C,
        AgreeNear I (V (S.schemeAt i) ⟨⇑(S.strictTransformio i).base '' C, hC⟩) ((S.strictTransformio i).base xi_) ∧
          orderAt I ((S.strictTransformio i).base xi_) = 1)
    (hcert : ∃ q : S.schemeAt i ⟶ Sp k,
      PrincipalizationCertificate (S.schemeAt i) q I 1 Mem $ S.ambientCenter i)
    {C1_ C2_}
    (h1_ : C1_ ∈ S.detachedComponents i)
    (h2_ : C2_ ∈ irreducibleComponents ↥(S.strictTransform i))
    (h2_' : C2_ ∉ S.detachedComponents i) :
    Disjoint C1_ C2_ := by
  obtain ⟨q, hq⟩ := hcert
  let _a1 := (S.mem_detachedComponents i C1_).1 h1_
  have hC1comp := _a1.1
  have hcl1_ := isClosed_of_mem_irreducibleComponents _ hC1comp
  have hcl2_ := isClosed_of_mem_irreducibleComponents _ h2_
  obtain ⟨xi1_, hxi1⟩ := sober hC1comp.1 hcl1_
  obtain ⟨xi2_, hxi2⟩ := sober h2_.1 hcl2_
  have him1 := hcl.isClosedMap _ hcl1_
  have him2 := hcl.isClosedMap _ hcl2_
  have hg2 :=
    isGenericPoint_image_of_isClosedEmbedding hcl hxi2
  obtain ⟨hag1, hord1⟩ := hagree C1_ hC1comp xi1_ hxi1 him1
  obtain ⟨hag2, hord2⟩ := hagree C2_ h2_ xi2_ hxi2 him2
  let _a0 := bsM (S.strictTransformio i) xi2_
  have hnotcenter :
      _a0 ∉ (spI (S.ambientCenter i) : CSet $ S.schemeAt i) := by
    intro hmem2
    apply h2_'
    rw [S.mem_detachedComponents i C2_]
    exact ⟨h2_, mp_ (hg2.mem_closed_set_iff
      (hV.isClosed_support (S.schemeAt i) $ S.ambientCenter i)) hmem2⟩
  rw [disjoint_left]
  intro x hx1 hx2
  exact orderOneCentersIsolated_of_principalizationCertificate (V := V) hV hq
    ⟨⇑(S.strictTransformio i).base '' C1_, ⇑(S.strictTransformio i).base '' C2_,
      (S.strictTransformio i).base xi1_, _a0, bsM (S.strictTransformio i) x,
      him1, him2, isGenericPoint_image_of_isClosedEmbedding hcl hxi1, hg2, ⟨x, hx1, rfl⟩, ⟨x, hx2, rfl⟩⟩
    rfl _a1.2 hnotcenter (hmem C1_ hC1comp xi1_ hxi1) (hmem C2_ h2_ xi2_ hxi2) hag1 hord1
    ((one_le_orderAt_iff_mem_support I _a0).1 $ le_of_eq hord2.symm)


end

end OpenImmersionRestriction





private theorem comp_base_apply {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A) :
    (f ≫ g).base x = g.base (f.base x) := by simp

namespace EmbeddedBlowupSequence

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]

def AvoidsCenters (S : EmbeddedBlowupSequence k Y pY) : ∀ (i : ℕ), ↥(schemeAt S i) → Prop
  | 0 => fun _ => True
  | (i + 1) => fun x =>
      (S.blowdown i).base x ∉ (support (S.ambientCenter i) : CSet $ schemeAt S i) ∧
        AvoidsCenters S i ((S.blowdown i).base x)

section
variable (S : EmbeddedBlowupSequence k Y pY)
@[simp] theorem avoidsCenters_zero (x : ↥(schemeAt S 0)) : S.AvoidsCenters 0 x := trivial

section
variable (i : ℕ)
theorem isOpenImmersion_io_comp_blowdown (hi : i < S.length)
    (U : (schemeAt S $ i + 1).Opens)
    (hU : (U : Set ↥(schemeAt S $ i + 1)) ⊆
      ⇑(S.blowdown i).base ⁻¹' ((S.ambientCenterSupportCompl i : (schemeAt S i).Opens) : CSet $ schemeAt S i)) :
    IsOpenImmersion $ U.ι ≫ S.blowdown i := by
  have :=
    S.isIso_blowdown_restrict_ambientCenterSupportCompl i hi
  have : IsOpenImmersion $ S.blowdown i ∣_ S.ambientCenterSupportCompl i := inferInstance
  have hle : U ≤ (m54 (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) := by
    intro x hx
    exact hU hx
  have key : (schemeAt S $ i + 1).homOfLE hle ≫
      ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫ opI (S.ambientCenterSupportCompl i)) = opI U ≫ S.blowdown i := by simp_all
  rw [← key]
  infer_instance

@[simp] theorem avoidsCenters_succ_iff (x : ↥(schemeAt S $ i + 1)) :
    S.AvoidsCenters (i + 1) x ↔
      ((S.blowdown i).base x ∉ (support (S.ambientCenter i) : CSet $ schemeAt S i) ∧
        S.AvoidsCenters i ((S.blowdown i).base x)) :=
  m22

theorem mem_image_strictTransformio_of_mem_image_succ
    C et_ (het_ : IsGenericPoint et_ C)
    C' (het' : IsGenericPoint ((S.strictTransformMap i).base et_) C')
    x (hx : x ∈ ⇑(strictTransformio S $ i + 1).base '' C) :
    (S.blowdown i).base x ∈ ⇑(strictTransformio S i).base '' C' := by
  obtain ⟨c, hc, rfl⟩ := hx
  let _a0 := S.strictTransformMap i
  have hetC' := het'
  have hclosed : IsClosed $ ⇑(S.strictTransformMap i).base ⁻¹' C' := by
    rw [← hetC']
    exact isClosed_closure.preimage _a0.base.hom.continuous
  have hsub : C ⊆ ⇑(S.strictTransformMap i).base ⁻¹' C' := by
    rw [← het_]
    refine closure_minimal ?_ hclosed
    intro z hz
    have hz' := hz
    subst hz'
    rw [mem_preimage, ← hetC']
    exact subset_closure rfl
  refine ⟨bsM _a0 c, hsub hc, ?_⟩
  have key : bsM (_a0 ≫ strictTransformio S i) c
      = bsM ((strictTransformio S $ i + 1) ≫ S.blowdown i) c := by
    rw [S.strictTransformMap_comp_strictTransformio i]
  simpa using key
end
end

section
variable [hv0_0 : IsReduced Y] (S : EmbeddedBlowupSequence k Y pY) (hN : ∀ j ≤ length S, IsNoetherian (schemeAt S j))
include hv0_0 hN
theorem forall_avoidsCenters_strictTransformio_of_isGenericPoint :
    ∀ i, i ≤ length S → ∀ C : Set ↥(S.strictTransform i),
      C ∈ irreducibleComponents ↥(S.strictTransform i) →
      ∀ xi_ : ↥(S.strictTransform i), IsGenericPoint xi_ C →
      S.AvoidsCenters i ((strictTransformio S i).base xi_) := by
  intro i
  induction i with
  | zero =>
    intro _ _ _ _ _
    exact S.avoidsCenters_zero _
  | succ i ih =>
    intro hi C hC xi_ hxi_
    obtain ⟨C', hC', het', hfr⟩ := S.exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i (lt_of_succ_le hi) C hC xi_ hxi_
    let _a0 := strictTransformio S $ i + 1
    have key : bsM (strictTransformio S i) (bsM (S.strictTransformMap i) xi_)
        = bsM (S.blowdown i) (bsM _a0 xi_) := by
      have h : bsM (S.strictTransformMap i ≫ strictTransformio S i) xi_
          = bsM (_a0 ≫ S.blowdown i) xi_ := by
        rw [S.strictTransformMap_comp_strictTransformio i]
      simpa using h
    refine mpr_ (S.avoidsCenters_succ_iff i _) ⟨?_, ?_⟩
    rw [← key]
    exact S.notMem_ambientCenter_support_of_isGenericPoint i C' hC' hfr _ het'
    rw [← key]
    exact ih (le_of_succ_le hi) C' hC' _ het'

theorem avoidsCenters_strictTransformio_of_isGenericPoint i (hi : i ≤ length S)
    C (hC : C ∈ irreducibleComponents ↥(S.strictTransform i))
    xi_ (hxi_ : IsGenericPoint xi_ C) :
    S.AvoidsCenters i $ (strictTransformio S i).base xi_ :=
  forall_avoidsCenters_strictTransformio_of_isGenericPoint S hN i hi C hC xi_ hxi_
end

theorem mem_closure_singleton_of_base_mem {X0 X1 : Sch}
    (pi_ : X1 ⟶ X0) (V : Opn X1)
    (hoe : IsOpenEmbedding ⇑(V.i ≫ pi_).base)
    {x y : ↥X1} (hx : x ∈ V) (hy : y ∈ V)
    (h : pi_.base x ∈ closure ({pi_.base y} : Set ↥X0)) :
    x ∈ closure ({y} : Set ↥X1) := by
  let _m1 := (⟨x, hx⟩ : ↥V)
  have hvx : opIb V _m1 = x := rfl
  let _m0 := (⟨y, hy⟩ : ↥V)
  have hvy : opIb V _m0 = y := rfl
  let _a0 := opI V ≫ pi_
  have h' : bsM _a0 _m0 ⤳ _a0.base _m1 := by
    rw [comp_base_apply V.i pi_ _m1, comp_base_apply V.i pi_ _m0, hvx, hvy]
    exact mpr_ specializes_iff_mem_closure h
  have hfin := (hoe.isInducing.specializes_iff.mp h').map V.ib.hom.continuous
  rw [hvx, hvy] at hfin
  exact mp_ specializes_iff_mem_closure hfin

section
variable [hv0_0 : IsReduced Y] (S : EmbeddedBlowupSequence k Y pY)
include hv0_0
theorem mem_image_strictTransformio_succ_of_mem_image (i : ℕ) (hi : i < S.length)
    (C : Set ↥(S.strictTransform $ i + 1)) (et_ : ↥(S.strictTransform $ i + 1)) (het_ : IsGenericPoint et_ C)
    (C' : Set ↥(S.strictTransform i)) (het' : IsGenericPoint ((S.strictTransformMap i).base et_) C')
    (x : ↥(schemeAt S $ i + 1))
    (hx : (S.blowdown i).base x ∉ ((S.ambientCenter i).support : CSet $ schemeAt S i))
    (hmem : (S.blowdown i).base x ∈ ⇑(strictTransformio S i).base '' C') :
    x ∈ ⇑(strictTransformio S $ i + 1).base '' C := by
  have hgenericImage :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding (S.isClosedEmbedding_strictTransformio $ i + 1) het_
  have hgenericImagePrev :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding (S.isClosedEmbedding_strictTransformio i) het'
  let _a0 := bsM (strictTransformio S $ i + 1) et_
  let _a3 := bsM (S.blowdown i) _a0
  have key : bsM (strictTransformio S i) (bsM (S.strictTransformMap i) et_)
      = _a3 := by
    have h : bsM (S.strictTransformMap i ≫ strictTransformio S i) et_
        = bsM (strictTransformio S (i + 1) ≫ S.blowdown i) et_ := by
      rw [S.strictTransformMap_comp_strictTransformio i]
    simpa using h
  have hclosure := hmem
  rw [← hgenericImagePrev, key] at hclosure
  let _a2 := spI $ S.ambientCenter i
  have hy0_ : _a3 ∉
      (_a2 : CSet $ schemeAt S i) := by
    intro hmemc
    exact hx $ closure_minimal (mpr_ singleton_subset_iff hmemc)
      _a2.2 hclosure
  let _a1 := schemeAt S $ i + 1
  obtain ⟨V, hVdef⟩ : ∃ V : Opn _a1,
      V = (m54 (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) := ⟨_, rfl⟩
  have hVsub : (V : Set ↥_a1) ⊆
      ⇑(S.blowdown i).base ⁻¹'
        ((S.ambientCenterSupportCompl i : (schemeAt S i).Opens) : CSet $ schemeAt S i) := by simp_all
  have hoi :=
    S.isOpenImmersion_io_comp_blowdown i hi V hVsub
  have hxV : x ∈ V := by
    rwa [hVdef]
  have hyV : _a0 ∈ V := by
    rwa [hVdef]
  have hmain := mem_closure_singleton_of_base_mem (S.blowdown i) V
    (opI V ≫ S.blowdown i).isOpenEmbedding hxV hyV hclosure
  rwa [← hgenericImage]

theorem mem_image_strictTransformio_iff_of_notMem_ambientCenter
    (_hN : ∀ j ≤ length S, IsNoetherian $ schemeAt S j) (i : ℕ) (hi : i < length S)
    (C : Set ↥(S.strictTransform $ i + 1)) (et_ : ↥(S.strictTransform $ i + 1)) (het_ : IsGenericPoint et_ C)
    (C' : Set ↥(S.strictTransform i)) (het' : IsGenericPoint ((S.strictTransformMap i).base et_) C')
    (x : ↥(schemeAt S $ i + 1))
    (hx : (S.blowdown i).base x ∉ (support (S.ambientCenter i) : CSet $ schemeAt S i)) :
    ((S.blowdown i).base x ∈ ⇑(strictTransformio S i).base '' C') ↔ (x ∈ ⇑(strictTransformio S $ i + 1).base '' C) :=
  ⟨fun hmem => mem_image_strictTransformio_succ_of_mem_image S i hi C et_ het_ C' het' x hx hmem,
    fun hxC => mem_image_strictTransformio_of_mem_image_succ S i C et_ het_ C' het' x hxC⟩
end

end EmbeddedBlowupSequence

namespace OpenImmersionRestriction


section
variable {W : Sch}
theorem preimage_congr_of_inter_eq {Z1 Z2 : Closeds ↥W}
    {U : Opn W} (h : (Z1 : Set ↥W) ∩ (U : Set ↥W) = (Z2 : Set ↥W) ∩ (U : Set ↥W))
    {A : Type} (g : A → ↥W) (hg : ∀ a, g a ∈ (U : Set ↥W)) :
    g ⁻¹' (Z1 : Set ↥W) = g ⁻¹' (Z2 : Set ↥W) := by
  ext a
  constructor
  intro ha
  have h2 : g a ∈ (Z1 : Set ↥W) ∩ (U : Set ↥W) := ⟨ha, hg a⟩
  rw [h] at h2
  exact an1 h2
  intro ha
  have h2 : g a ∈ (Z2 : Set ↥W) ∩ (U : Set ↥W) := ⟨ha, hg a⟩
  rw [← h] at h2
  exact an1 h2

section
variable (Z1 Z2 : Closeds ↥W) (U : Opn W)
theorem vanishingIdeal_ideal_eq_of_inter_eq
    (h : (Z1 : Set ↥W) ∩ (U : Set ↥W) = (Z2 : Set ↥W) ∩ (U : Set ↥W))
    (V : W.affineOpens) (hV : (V.1 : Set ↥W) ⊆ (U : Set ↥W)) :
    (vanishingIdeal Z1).ideal V
      = (vanishingIdeal Z2).ideal V := by
  refine congrArg m184
    (preimage_congr_of_inter_eq h (V.2.fromSpec).base ?_)
  intro a
  refine hV ?_
  rw [← IsAffineOpen.range_fromSpec V.2]
  exact mem_range_self a

theorem agreeNear_vanishingIdeal_of_inter_eq (x : ↥W) (hx : x ∈ (U : Set ↥W))
    (h : (Z1 : Set ↥W) ∩ (U : Set ↥W) = (Z2 : Set ↥W) ∩ (U : Set ↥W)) :
    AgreeNear (vanishingIdeal Z1)
      (vanishingIdeal Z2) x := by
  refine mpr_ (agreeNear_iff _ _ _) ⟨U, hx, ?_⟩
  refine m29 $ funext fun V => ?_
  rw [ideal_comap_of_isOpenImmersion,
    ideal_comap_of_isOpenImmersion]
  refine congrArg _ ?_
  refine vanishingIdeal_ideal_eq_of_inter_eq Z1 Z2 U h _ ?_
  intro y hy
  obtain ⟨z, -, rfl⟩ := hy
  exact z.2
end
end

theorem comap_eq_comap_mul_of_comap_eq_top {A B : Type} [CommRing A] [CommRing B]
    (ph_ : A →+* B) (P Q : Ideal B) (hP : comap ph_ P = ⊤) :
    comap ph_ Q = comap ph_ (P * Q) :=by simp_all
section
variable {X Z : Sch} (f : X ⟶ Z)
theorem mem_support_of_mem_support_comap (I : ISD Z)
    (x : ↥X) (hx : x ∈ (support (I.comap f) : Set ↥X)) :
    f.base x ∈ (support I : Set ↥Z) :=by simp_all
theorem comap_eq_comap_comp_of_mul_eq (U : Opn X)
    (I J : ISD X) (K : ISD Z)
    (hmul : I * J = K.comap f) (hI : I.comap U.i = ⊤) :
    J.comap U.i = K.comap (U.i ≫ f) := by
  have hcomp : K.comap (U.i ≫ f) = (K.comap f).comap U.i := by
    simp [comap_comp]
  rw [hcomp, ← hmul]
  refine m29 $ funext fun V => ?_
  rw [ideal_comap_of_isOpenImmersion J U.i V,
    ideal_comap_of_isOpenImmersion (I * J) U.i V]
  simp only [ideal_mul, Pi.mul_apply]
  refine comap_eq_comap_mul_of_comap_eq_top _ _ _ ?_
  rw [← ideal_comap_of_isOpenImmersion I U.i V, hI]
  simp
end

variable {k : Type} [Field k] [CharZero k] {Y : Sch} [IsAffine Y]
  {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY]
  [QuasiCompact pY]

omit [QuasiCompact pY] in
theorem isNoetherian_schemeAt_toEmbeddedBlowupSequence (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm) :
    ∀ i ≤ (D.toEmbeddedBlowupSequence A).length,
      IsNoetherian $ (D.toEmbeddedBlowupSequence A).schemeAt i :=
  fun i hi => (D.toEmbeddedBlowupSequence A).isNoetherian_schemeAt i hi

section
variable (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm)
theorem forall_not_avoidsCenters_of_mem_boundary_support :
    ∀ i, i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ E : IdealSheafData $ (principalizationOfEmbedding k Y pY D A).schemeAt i,
        E ∈ (principalizationOfEmbedding k Y pY D A).boundary i →
        ∀ x : ↥((D.toEmbeddedBlowupSequence A).schemeAt i),
          x ∈ (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) →
          ¬ (D.toEmbeddedBlowupSequence A).AvoidsCenters i x := by
  let _c0 := principalizationOfEmbedding k Y pY D A
  intro i
  induction i with
  | zero =>
      intro _ E hE x hx hcl
      rw [_c0.boundary_zero] at hE
      simp at hE
  | succ i ih =>
      intro hi E hE x hx hcl
      rw [_c0.boundary_succ_eq_map_strictTransform_append i hi, mem_append] at hE
      have hcl' := mp_ ((D.toEmbeddedBlowupSequence A).avoidsCenters_succ_iff i x) hcl
      rcases hE with hE | hE
      obtain ⟨E', hE', rfl⟩ := mp_ mem_map hE
      exact ih (le_of_succ_le hi) E' hE' _ (mem_support_of_mem_support_comap (_c0.transitionMapSucc i) E' x $ support_antitone (comap_le_strictTransform (_c0.transitionMapSucc i) (_c0.center i) E') hx) hcl'.2
      rw [mem_singleton] at hE
      subst hE
      rw [_c0.exceptionalIdeal_eq i] at hx
      exact an1 hcl' $ mem_support_of_mem_support_comap (_c0.transitionMapSucc i) (_c0.center i) x hx

theorem not_avoidsCenters_of_mem_boundary_support
    i (hi : i ≤ (D.toEmbeddedBlowupSequence A).length)
    (E : IdealSheafData $ (principalizationOfEmbedding k Y pY D A).schemeAt i)
    (hE : E ∈ (principalizationOfEmbedding k Y pY D A).boundary i)
    x
    (hx : x ∈ (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))) :
    ¬ (D.toEmbeddedBlowupSequence A).AvoidsCenters i x :=
  forall_not_avoidsCenters_of_mem_boundary_support D A i hi E hE x hx
end

theorem ker_congr {A B : Sch} {f g : A ⟶ B}
    [QuasiCompact f] [QuasiCompact g] (h : f = g) :
    ker f = ker g := by
  subst h
  rfl

theorem ker_comap_iso_hom_eq_ker_comp_inv {W B X : Sch} (j : W ⟶ B) (e : X ≅ B)
    [QuasiCompact j] [QuasiCompact $ j ≫ e.inv] :
    (ker j).comap e.hom
      = ker (j ≫ e.inv) := by
  have h2 : (j ≫ isoI e) ≫ isoH e = j := by simp
  have : QuasiCompact $ (j ≫ isoI e) ≫ isoH e := by
    rw [h2]
    infer_instance
  rw [ker_congr h2.symm]
  exact comap_ker_comp_of_isOpenImmersion (j ≫ isoI e) e.hom

theorem radical_eq_of_eq_ker {Z W : Sch} [IsReduced W]
    (I : ISD Z) (f : W ⟶ Z)
    (h : I = ker f) : I.radical = I := by
  subst h
  let _a0 := ker f
  have hle : _a0.radical
      ≤ ker f := by
    show _a0.radical ≤
      ofIdeals
        (fun U : affO Z =>
          m41 $ m4 $ app f U.1)
    rw [le_ofIdeals_iff]
    intro U
    refine le_trans (radical_mono $ ideal_ofIdeals_le _ U) ?_
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.isRadical_bot.comap _
  exact le_antisymm hle $ le_radical _

theorem principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal [IsReduced Y]
    (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm)
    (hcl : IsClosed $ range ⇑((D.toEmbeddedBlowupSequence A).strictTransformio 0).base) :
    (principalizationOfEmbedding k Y pY D A).ideal 0 =
      vanishingIdeal
        (⟨range ⇑((D.toEmbeddedBlowupSequence A).strictTransformio 0).base, hcl⟩ :
          Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0)) := by
  have hB :=
    strictTransformIdeal_zero $ D.toEmbeddedBlowupSequence A
  let _a0 := principalizationOfEmbedding k Y pY D A
  let _a2 := D.emb ≫ _a0.isoZero.inv
  have hA : _a0.ideal 0
      = ker
          _a2 := by
    rw [IdealBlowupSequence.ideal_zero, projectionToBase_zero]
    exact ker_comap_iso_hom_eq_ker_comp_inv D.emb _a0.isoZero
  let _a1 := (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0
  have hsupp : (⟨range ⇑((D.toEmbeddedBlowupSequence A).strictTransformio 0).base, hcl⟩ :
      Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0))
      = _a1.support :=
    m134
      (q5 _a1)
  have key := radical_eq_of_eq_ker _a1 _a2 hB
  rw [← vanishingIdeal_support, ← hsupp] at key
  exact tr_ hA $ hB.symm.trans key.symm

def AgreesWithComponentsOrderOne (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm) (i : ℕ) : Prop :=
  ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
  ∀ xi_ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint xi_ C →
  ∀ hC : IsClosed $ ⇑((D.toEmbeddedBlowupSequence A).strictTransformio i).base '' C,
    AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal i)
        (vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformio i).base '' C, hC⟩ :
            Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i)))
        (((D.toEmbeddedBlowupSequence A).strictTransformio i).base xi_) ∧
      orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
        (((D.toEmbeddedBlowupSequence A).strictTransformio i).base xi_) = 1

section
variable {X : Sch} (x : ↥X)
theorem eq_of_specializes_of_isField_stalk
    (hfield : IsField ↑(X.presheaf.stalk x)) (y : ↥X) (hy : y ⤳ x) : y = x := by
  have hrange : range ⇑(X.fromSpecStalk x).base = {z : ↥X | z ⤳ x} := by
    rw [range_fromSpecStalk]
  have hy' : y ∈ range ⇑(X.fromSpecStalk x).base := by
    rwa [hrange]
  have hx' : x ∈ range ⇑(X.fromSpecStalk x).base := by
    rw [hrange]
    exact specializes_refl x
  obtain ⟨a, ha⟩ := hy'
  obtain ⟨b, hb⟩ := hx'
  have hab : a = b := by
    let := hfield.toField
    have key : ∀ p q : PrimeSpectrum ↑(stkX X x), p = q := fun p q =>
      m111 p q
    exact key a b
  exact st_ ha $ tr_ (congrArg (fun t => bsM (X.fromSpecStalk x) t) hab) hb

theorem closure_singleton_mem_irreducibleComponents
    (h : ∀ y : ↥X, y ⤳ x → y = x) :
    closure ({x} : Set ↥X) ∈ irreducibleComponents ↥X := by
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro S hS hsub
  obtain ⟨y, hy⟩ := sober hS.closure isClosed_closure
  have hy2 := hy
  have hyx : y = x := by
    refine h y $ mpr_ specializes_iff_mem_closure ?_
    rw [hy2]
    exact subset_closure $ hsub $ subset_closure rfl
  rw [hyx] at hy2
  rw [hy2]
  exact subset_closure
end

theorem eq_of_specializes_iso_hom {X B : Sch} (e : X ≅ B) (x : ↥X)
    (h : ∀ y : ↥X, y ⤳ x → y = x) (w : ↥B) (hw : w ⤳ e.hom.base x) :
    w = e.hom.base x := by
  have h1 := hw.map e.inv.base.hom.continuous
  have h2 : ibM e (ihB_ e x) = x := by simp_all
  rw [h2] at h1
  have h4 : ihB_ e (ibM e w) = w := by
    rw [← comp_base_apply e.inv e.hom w, e.inv_hom_id]
    simp
  rw [← h4, h _ h1]

section
variable {k : Type} [Field k] [CharZero k] {Y : Sch} [IsAffine Y] [IsReduced Y] {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY] [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm)
theorem agreesWithComponentsOrderOne_zero :
    AgreesWithComponentsOrderOne D A 0 := by
  let _c0 := (D.toEmbeddedBlowupSequence A).strictTransformio 0
  classical
  intro C hC xi_ hxi_ hCcl
  let _a4 := principalizationOfEmbedding k Y pY D A
  have : IsLocallyNoetherian $ _a4.schemeAt 0 :=
    ((D.toEmbeddedBlowupSequence A).isNoetherian_schemeAt 0 $ zero_le _).toIsLocallyNoetherian
  let _a0 := (D.toEmbeddedBlowupSequence A).strictTransform 0
  have : NoetherianSpace ↥_a0 :=
    (D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) 0
      (zero_le _)
  have hemb := (D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformio 0
  let _a2 := (D.toEmbeddedBlowupSequence A).schemeAt 0
  have hid0 := principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D A hemb.isClosed_range
  set Bad : Set ↥_a2 :=
    ⋃ C'' ∈ irreducibleComponents ↥_a0 \ {C},
      ⇑_c0.base '' C'' with hBaddef
  have hBadcl : IsClosed Bad := by
    rw [hBaddef]
    exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset sdiff_subset).isClosed_biUnion fun C'' hC'' =>
      hemb.isClosedMap _ $ isClosed_of_mem_irreducibleComponents C'' hC''.1
  have hxU : bsM _c0 xi_ ∈ Badᶜ := by
    intro hmem
    rw [hBaddef] at hmem
    obtain ⟨C'', hC''D, hxim⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨z, hzC'', hz⟩ := hxim
    have hzxi := hemb.injective hz
    subst hzxi
    have hsub : C ⊆ C'' := by
      rw [← hxi_.def]
      exact closure_minimal (mpr_ singleton_subset_iff hzC'')
        (isClosed_of_mem_irreducibleComponents C'' hC''D.1)
    exact an2 hC''D $ subset_antisymm (an2 hC hC''D.1.1 hsub) hsub
  have hinter : (range ⇑_c0.base) ∩ Badᶜ
      = (⇑_c0.base '' C) ∩ Badᶜ := by
    ext y
    constructor
    rintro ⟨⟨z, rfl⟩, hy⟩
    refine ⟨?_, hy⟩
    by_cases hz : z ∈ C
    exact ⟨z, hz, rfl⟩
    refine absurd ?_ hy
    rw [hBaddef]
    refine mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩
      ⟨z, mem_irreducibleComponent, rfl⟩
    intro h
    exact hz $ h ▸ mem_irreducibleComponent
    rintro ⟨⟨z, hzC, rfl⟩, hy⟩
    exact ⟨⟨z, rfl⟩, hy⟩
  have hmax : Maximal (fun s => IsIrreducible s ∧
      s ⊆ range ⇑_c0.base)
      (⇑_c0.base '' C) := by
    constructor
    exact ⟨hC.1.image _ hemb.continuous.continuousOn, image_subset_range _ _⟩
    rintro b ⟨hbirr, hbr⟩ hsub y hy
    have hCsub :=
      fun z hz => hsub ⟨z, hz, rfl⟩
    obtain ⟨z, rfl⟩ := hbr hy
    exact ⟨z, (an2 hC (FunctorialResolution.EmbeddedResolution.isIrreducible_preimage_of_isEmbedding hemb.isEmbedding hbirr hbr) hCsub) hy, rfl⟩
  let _a1 := bsM ((D.toEmbeddedBlowupSequence A).strictTransformio 0) xi_
  have hfield : ¬ IsField ↑(stkX _a2 _a1) := by
    let _c0 := _a4
    let _c1 := _a1
    intro hfield
    let _a0 := (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0
    let _a5 := D.emb ≫ _c0.isoZero.inv
    have hB : _a0
        = ker
            _a5 :=
      strictTransformIdeal_zero $ D.toEmbeddedBlowupSequence A
    have hcomap : (ker D.emb).comap
          _c0.isoZero.hom
        = ker
            _a5 :=
      ker_comap_iso_hom_eq_ker_comp_inv D.emb _c0.isoZero
    have hxsupp : _a1 ∈
        ((_a0.support) : Set ↥_a2) := by
      rw [← q5 _a0]
      exact ⟨xi_, rfl⟩
    have hz : _c0.isoZero.hom.base
          _c1
        ∈ ((ker D.emb).support : CSet D.ambient) := by
      refine mem_support_of_mem_support_comap _c0.isoZero.hom
        (ker D.emb) _ ?_
      rwa [hcomap, ← hB]
    have hnogen :=
      fun y hy => eq_of_specializes_of_isField_stalk _ hfield y hy
    have hcomp := closure_singleton_mem_irreducibleComponents
      (_c0.isoZero.hom.base _c1)
      (eq_of_specializes_iso_hom _c0.isoZero
        _c1 hnogen)
    exact D.nonzeroOnComponents_ker _ hcomp
      (closure_minimal (mpr_ singleton_subset_iff hz)
        (ker D.emb).support.2)
  constructor
  rw [hid0]
  exact agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter
  rw [hid0]
  exact orderAt_vanishingIdeal_eq_one_of_not_isField _ _ _ hmax (FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding hemb hxi_) hfield

theorem agreesWithComponentsOrderOne_succ
    (i : ℕ) (hi : i + 1 ≤ (D.toEmbeddedBlowupSequence A).length) (ih : AgreesWithComponentsOrderOne D A i) :
    AgreesWithComponentsOrderOne D A (i + 1) := by
  let _a0 := D.toEmbeddedBlowupSequence A
  let _c0 := _a0.strictTransformio $ i + 1
  let _c1 := principalizationOfEmbedding k Y pY D A
  let _c2 := _a0.strictTransformio i
  let _c3 := _a0.blowdown i
  let _c4 := _a0.schemeAt i
  let _c5 := _a0.schemeAt $ i + 1
  let _c6 := _a0.strictTransformMap i
  classical
  intro C hC et_ hetgen hCcl
  have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D A
  have hi' := lt_of_succ_le hi
  obtain ⟨C', hC'm, het', hfr⟩ :=
    _a0.exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC et_ hetgen
  have hC'cl :=
    (_a0.isClosedEmbedding_strictTransformio i).isClosedMap _
      (isClosed_of_mem_irreducibleComponents C' hC'm)
  obtain ⟨hag, hord⟩ := ih C' hC'm _ het' hC'cl
  obtain ⟨V, hxV, hVeq⟩ := mp_ (agreeNear_iff _ _ _) hag
  obtain ⟨V', hV'⟩ : ∃ V' : Opn _c4, V' = V := ⟨V, rfl⟩
  let _a2 := bsM _c3 $ bsM _c0 et_
  have hkey : bsM _c2 (bsM _c6 et_)
      = _a2 := by
    have h : bsM (_a0.strictTransformMap i ≫ _a0.strictTransformio i) et_
        = bsM (_a0.strictTransformio (i + 1) ≫ _a0.blowdown i) et_ := by
      rw [_a0.strictTransformMap_comp_strictTransformio i]
    simpa using h
  have hnot :=
    _a0.notMem_ambientCenter_support_of_isGenericPoint i C' hC'm hfr _ het'
  have hxV' : bsM _c2 (bsM _c6 et_)
      ∈ V' := by
    rwa [hV']
  let _a1 := vanishingIdeal (⟨⇑_c2.base '' C', hC'cl⟩ : Closeds ↥_c4)
  have hV'eq : (_c1.ideal i).comap V'.i
      = _a1.comap V'.i := by
    rwa [hV']
  obtain ⟨U, hUdef⟩ : ∃ U : Opn _c5,
      U = (m54 _c3.base).obj
        (V' ⊓ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i) := ⟨_, rfl⟩
  have hUsub : (U : Set ↥_c5) ⊆
      ⇑_c3.base ⁻¹'
        ((_a0.ambientCenterSupportCompl i : Opn _c4) :
          Set ↥_c4) := by
    rw [hUdef]
    intro y hy
    exact hy.2
  have hmemU : ∀ y : ↥U, bsM _c3 (opIb U y) ∉
      ((_a0.ambientCenter i).support :
        Set ↥_c4) := by
    intro y
    exact hUsub y.2
  have hxU : bsM _c0 et_ ∈ U := by
    rw [hUdef]
    have h1 : _a2 ∈ V' := by
      rwa [← hkey]
    have h2 : _a2
        ∈ _a0.ambientCenterSupportCompl i := by
      rwa [← hkey]
    exact ⟨h1, h2⟩
  have : IsOpenImmersion (opI U ≫ _a0.blowdown i) :=
    EmbeddedBlowupSequence.isOpenImmersion_io_comp_blowdown (D.toEmbeddedBlowupSequence A) i hi' U hUsub
  have hexc : (_c1.exceptionalIdeal i).comap U.i = ⊤ := by
    refine comap_io_eq_top_of_disjoint _ _ ?_
    rw [disjoint_left]
    intro y hy hmem
    rw [_c1.exceptionalIdeal_eq i] at hmem
    exact absurd (mem_support_of_mem_support_comap
      (_c1.transitionMapSucc i) _ y hmem) (hUsub hy)
  have hJ : (_c1.ideal (i + 1)).comap U.i
      = (_c1.ideal i).comap
          (opI U ≫ _a0.blowdown i) :=
    comap_eq_comap_comp_of_mul_eq _ U _ _ _
      (_c1.ideal_succ i hi') hexc
  have hle : U ≤ (m54 _c3.base).obj V' := by
    rw [hUdef]
    intro y hy
    exact hy.1
  have hcomapph :=
    comap_ι_comp_eq_of_comap_ι_eq
      _c3 V' U hle _ _ hV'eq
  have hLHS : _a1.comap
        (opI U ≫ _a0.blowdown i)
      = vanishingIdeal
          (closedPreimage U.i
            (⟨⇑_c0.base '' C, hCcl⟩ :
              Closeds ↥_c5)) := by
    refine comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
      (opI U ≫ _a0.blowdown i) _ _ ?_
    ext y
    have hcb := comp_base_apply U.i _c3 y
    have hiff := EmbeddedBlowupSequence.mem_image_strictTransformio_iff_of_notMem_ambientCenter
      (D.toEmbeddedBlowupSequence A) hN i hi' C et_ hetgen C' het' (opIb U y) (hmemU y)
    constructor
    intro hy
    have hy1 := hy
    have hy2 := mpr_ hiff hy1
    have hy3 : bsM (opI U ≫ _a0.blowdown i) y
        ∈ ⇑_c2.base '' C' := by
      rwa [hcb]
    exact hy3
    intro hy
    have hy1 := hy
    have hy2 : bsM _c3 (opIb U y)
        ∈ ⇑_c2.base '' C' := by
      rwa [← hcb]
    exact mp_ hiff hy2
  refine ⟨mpr_ (agreeNear_iff _ _ _) ⟨U, hxU, ?_⟩, ?_⟩
  exact tr_ hJ (tr_ hcomapph (tr_ hLHS
    (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.i
      (⟨⇑_c0.base '' C, hCcl⟩ :
        m182 ↥_c5)).symm))
  have e1 := FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion U.i
    (_c1.ideal (i + 1))
    (⟨bsM _c0 et_, hxU⟩ : ↥U)
  have e2 := orderAt_comap_of_isOpenImmersion
    (opI U ≫ _a0.blowdown i) (_c1.ideal i)
    (⟨bsM _c0 et_, hxU⟩ : ↥U)
  have hphp : bsM (opI U ≫ _a0.blowdown i)
      (⟨bsM _c0 et_, hxU⟩ : ↥U)
      = bsM _c2 (bsM _c6 et_) := by
    rw [comp_base_apply U.i _c3
      (⟨bsM _c0 et_, hxU⟩ : ↥U)]
    exact sy_ hkey
  calc p55 (_c1.ideal (i + 1))
        (bsM _c0 et_)
      = p55 ((_c1.ideal (i + 1)).comap U.i)
          (⟨bsM _c0 et_, hxU⟩ : ↥U) := sy_ e1
    _ = p55 ((_c1.ideal i).comap
          (opI U ≫ _a0.blowdown i))
          (⟨bsM _c0 et_, hxU⟩ : ↥U) := by rw [hJ]
    _ = p55 (_c1.ideal i)
          (bsM (opI U ≫ _a0.blowdown i)
            (⟨bsM _c0 et_, hxU⟩ : ↥U)) := e2
    _ = p55 (_c1.ideal i)
          (bsM _c2
            (bsM _c6 et_)) := by rw [hphp]
    _ = 1 := hord

theorem forall_agreesWithComponentsOrderOne :
    ∀ i, i ≤ (D.toEmbeddedBlowupSequence A).length → AgreesWithComponentsOrderOne D A i := by
  intro i
  induction i with
  | zero => intro _; exact agreesWithComponentsOrderOne_zero D A
  | succ i ih => intro hi; exact agreesWithComponentsOrderOne_succ D A i hi $ ih $ le_of_succ_le hi
end

theorem agreesWithComponentsOrderOne_of_le [IsReduced Y] (D : EmbeddingDatum k Y pY)
    A i (hi : i ≤ (D.toEmbeddedBlowupSequence A).length) :
    AgreesWithComponentsOrderOne D A i :=
  forall_agreesWithComponentsOrderOne D A i hi

section
variable (A : PrincipalizationAlgorithm)
theorem genericPoint_notMem_boundary_support :
    ∀ (k : Type) [Field k] [CharZero k] Y
      [IsAffine Y] [IsReduced Y]
      pY [LocallyOfFiniteType pY]
      [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
      ∀ xi_ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint xi_ C →
      ∀ E ∈ (principalizationOfEmbedding k Y pY D A).boundary i,
        ((D.toEmbeddedBlowupSequence A).strictTransformio i).base xi_ ∉
          (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) := by
  intro k _ _ Y _ _ pY _ _ D i hi C hC xi_ hxi_ E hE hx
  exact not_avoidsCenters_of_mem_boundary_support D A i hi E hE _ hx
    (EmbeddedBlowupSequence.avoidsCenters_strictTransformio_of_isGenericPoint (D.toEmbeddedBlowupSequence A)
      (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) i hi C hC xi_ hxi_)

end

theorem not_image_irreducibleComponent_subset_boundary_support [IsReduced Y]
    (D : EmbeddingDatum k Y pY) A i (hi : i ≤ (D.toEmbeddedBlowupSequence A).length)
    C
    (hC : C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i))
    (E : IdealSheafData $ (principalizationOfEmbedding k Y pY D A).schemeAt i)
    (hE : E ∈ (principalizationOfEmbedding k Y pY D A).boundary i) :
    ¬ (⇑((D.toEmbeddedBlowupSequence A).strictTransformio i).base '' C ⊆
        (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))) := by
  intro hsub
  obtain ⟨xi_, hxi_⟩ := sober hC.1 $ isClosed_of_mem_irreducibleComponents C hC
  exact genericPoint_notMem_boundary_support A k Y pY D i hi C hC xi_ hxi_ E hE
    (hsub ⟨xi_, hxi_.mem, rfl⟩)

end OpenImmersionRestriction

namespace OpenImmersionRestriction
section
variable (hV : IdealSheafGeometryHypotheses vanishingIdealAssignment)
  (hres : StrictTransformIsBlowupOfClosedSubscheme)
  (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
  (hrad : SmoothSubschemeIdealIsRadical)
include hV hB
section
variable (k : Type) [Field k] [CharZero k] (Y) [IsAffine Y] [IsReduced Y] (pY) [LocallyOfFiniteType pY] [QuasiCompact pY] (D : EmbeddingDatum k Y pY)
theorem disjoint_detachedComponent_canonicalPrincipalization i
    (hi : i < (D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).length)
    {C1_ C2_}
    (h1_ : C1_ ∈ (D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).detachedComponents i)
    (h2_ : C2_ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransform i))
    (h2_' : C2_ ∉ (D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).detachedComponents i) :
    Disjoint C1_ C2_ := by
  let _a0 := canonicalPrincipalization hres hrad
  let _c0 := principalizationOfEmbedding k Y pY D _a0
  have := (D.toEmbeddedBlowupSequence _a0).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D _a0) i $ le_of_lt hi
  have hspec := (PrincipalizationRules.isMaxOrderReduction_outputLevelData (canonicalAlgorithmRules hres) hB
      (krullDimSucc D.ambient)).cert
      (markedTripleOrderOne k D.ambient D.ambientStruct (ker D.emb) [])
      (markedTripleOrderOne_isAdmissible k D.ambient D.ambientStruct
        (ker D.emb) D.nonzeroOnComponents_ker [] D.sncEmpty)
      (le_of_eq $ markedTripleOrderOne_dim k D.ambient D.ambientStruct
        (ker D.emb) [])
      i hi
  refine disjoint_detachedComponent_of_principalizationCertificate hV
    (D.toEmbeddedBlowupSequence _a0) i
    (_c0.ideal i)
    (⋃ E ∈ _c0.boundary i,
      suppI E)
    ((D.toEmbeddedBlowupSequence _a0).isClosedEmbedding_strictTransformio i) ?_ (agreesWithComponentsOrderOne_of_le D _a0 i $ le_of_lt hi) ⟨_, hspec⟩ h1_ h2_ h2_'
  intro C hC xi_ hxi_ hx
  obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
  exact genericPoint_notMem_boundary_support _a0 k Y pY D i (le_of_lt hi) C hC xi_ hxi_ E hE hxE

theorem detachedLocusIsOpen_toEmbeddedBlowupSequence :
    DetachedLocusIsOpen $ D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad := by
  intro i hi
  have := (D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D $ canonicalPrincipalization hres hrad) i $ le_of_lt hi
  rw [detachedLocus_eq_sUnion]
  exact isOpen_sUnion_of_irreducibleComponents _
    (fun C1_ hC1 C2_ hC2_ hC2' =>
      disjoint_detachedComponent_canonicalPrincipalization hV hres hB hrad k Y pY D i hi hC1 hC2_ hC2')
end

theorem detachedLocusIsOpenForEmbeddings_canonicalPrincipalization :
    DetachedLocusIsOpenForEmbeddings $ canonicalPrincipalization hres hrad := by
  intro k _ _ Y pY _ _ _ _ D
  exact detachedLocusIsOpen_toEmbeddedBlowupSequence hV hres hB hrad k Y pY D
end
end OpenImmersionRestriction

theorem range_base_subschemeio {X : Sch} (I : ISD X) :
    range ⇑I.subschemeι.base = ((support I : Closeds ↥X) : Set ↥X) := by
  rw [q5]

theorem mem_of_mem_support_vanishingIdeal {W : Sch} (Z : Closeds ↥W)
    (x : ↥W) (hx : x ∈ support (vanishingIdeal Z)) : x ∈ (Z : Set ↥W) := by
  have h2 : x ∈ ((spI (vanishingIdeal Z) :
      Closeds ↥W) : Set ↥W) := hx
  rwa [coe_support_vanishingIdeal] at h2

theorem exists_iso_subscheme_vanishingIdeal_of_closure_range {A W : Sch} (f : A ⟶ W)
    [IsClosedImmersion f] [IsReduced A]
    (K : Closeds ↥W)
    (hK : (K : Set ↥W) = closure (range ⇑f.base))
    (hle : ker f ≤ vanishingIdeal K) :
    ∃ e : (vanishingIdeal K).subscheme ≅ A,
      e.hom ≫ f = (vanishingIdeal K).si := by
  have hrange : range ⇑(vanishingIdeal K).subschemeι.base
      = K := by simp_all
  have hle' : m149 f
      ≤ ker (vanishingIdeal K).si := by simp_all
  let _a0 := vanishingIdeal K
  obtain ⟨ps_, hps_⟩ : ∃ ps_ : subS _a0 ⟶ A,
      ps_ ≫ f = siI _a0 :=
    ⟨lift f (vanishingIdeal K).si hle',
      lift_fac _ _ hle'⟩
  have hpsbase : ∀ x, bsM f (bsM ps_ x)
      = _a0.subschemeι.base x := by
    intro x
    show bsM (ps_ ≫ f) x = _a0.subschemeι.base x
    rw [hps_]
  have hsurj : Surjective ⇑ps_.base := by
    intro a
    have h1 : bsM f a ∈ (K : Set ↥W) := by
      rw [hK]
      exact subset_closure $ mem_range_self a
    rw [← hrange] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, f.isEmbedding.injective (by rw [hpsbase y]; exact hy)⟩
  have hru := hsurj.range_eq
  have : IsPreimmersion $ ps_ ≫ f := by rw [hps_]
                                        infer_instance
  have := IsPreimmersion.of_comp ps_ f
  have :=
    of_isPreimmersion ps_ (by rw [hru]; exact isClosed_univ)
  have hker : ker ps_ = ⊥ := by
    rw [← support_eq_top_iff]
    refine m134 ?_
    rw [support_ker, hru, closure_univ]
    simp
  have := mpr_ isIso_iff_ker_eq_bot hker
  exact ⟨asIso ps_, hps_⟩

theorem exists_iso_of_range_base_eq {A B W : Sch} (f : A ⟶ W) (g : B ⟶ W)
    [IsClosedImmersion f] [IsClosedImmersion g]
    [IsReduced A] [IsReduced B]
    (h : range ⇑f.base = range ⇑g.base) :
    ∃ e : A ≅ B, e.hom ≫ g = f := by
  have hA :=
    support_ker f
  have hB : ((f.ker).support : Set ↥W) = closure (range ⇑g.base) := by simp_all
  have hKeq : (g.ker).support = (f.ker).support :=
    m134 $ by rw [support_ker g, hB]
  obtain ⟨e1_, he1_⟩ := exists_iso_subscheme_vanishingIdeal_of_closure_range f (f.ker).support hA
    (by rw [vanishingIdeal_support]
        exact le_radical _)
  obtain ⟨e2_, he2_⟩ := exists_iso_subscheme_vanishingIdeal_of_closure_range g (f.ker).support hB
    (by rw [← hKeq, vanishingIdeal_support]
        exact le_radical _)
  refine ⟨e1_.symm ≪≫ e2_, ?_⟩
  have hcomp : (e1_.symm ≪≫ e2_).hom = e1_.inv ≫ e2_.hom := rfl
  rw [hcomp, assoc, he2_, ← he1_, ← assoc, m114, id_comp]

theorem isNoetherian_ambientLevel_ofAffine A
    (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace)
    (hsm : AffineSpaceIsSmooth) (k : Type) [Field k] [CharZero k] Y
    [IsAffine Y] pY
    [LocallyOfFiniteType pY] :
    ∀ i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength,
      AlgebraicGeometry.IsNoetherian $ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i := by
  intro i hi
  have h := EmbeddedBlowupSequence.isNoetherian_schemeAt
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence i hi
  rwa [AffineSpacePrincipalizationData.toEmbeddedBlowupSequence_schemeAt] at h

theorem mem_support_of_le {X : Sch} {I J : ISD X} (h : I ≤ J)
    x (hx : x ∈ J.support) : x ∈ I.support :=
  (mem_orderAtLeastLocus_one_iff I x).mp
    (orderAtLeastLocus_subset_of_le_ideal h 1 $ mpr_ (mem_orderAtLeastLocus_one_iff J x) hx)

theorem mem_support_mul {X : Sch} (I J : ISD X) x :
    x ∈ support (I * J) ↔ x ∈ support I ∨ x ∈ support J := by
  have h : ((spI (I * J) : Closeds ↥X) : Set ↥X)
      = suppI I
        ∪ suppI J := by
    simp
  constructor
  intro hx
  have h2 : x ∈ ((spI (I * J) : Closeds ↥X) : Set ↥X) := hx
  rwa [h] at h2
  intro hx
  have h2 : x ∈ ((spI (I * J) : Closeds ↥X) : Set ↥X) := by simp_all
  exact h2

private theorem mem_support_comap {X Z : Sch} (f : X ⟶ Z) (I : ISD Z) (x : ↥X) :
    x ∈ support (I.comap f) ↔ ⇑f.base x ∈ support I := by
  constructor
  intro hx
  have h : x ∈ ((spI (cmI I f) : Closeds ↥X) : Set ↥X) := hx
  rwa [support_comap_eq] at h
  intro hx
  have h : x ∈ ((spI (cmI I f) : Closeds ↥X) : Set ↥X) := by simp_all
  exact h

theorem exists_mem_list_subset_of_isIrreducible {al_ : Type} [TopologicalSpace al_] {ι : Type}
    {s : Set al_} (hs : IsIrreducible s) (g : ι → Set al_) :
    ∀ L : List ι, (∀ t ∈ L, IsClosed $ g t) → s ⊆ (⋃ t ∈ L, g t) → ∃ t ∈ L, s ⊆ g t := by
  intro L
  induction L with
  | nil =>
      intro _ hsub
      obtain ⟨x, hx⟩ := hs.nonempty
      obtain ⟨t, ht, -⟩ := Set.mem_iUnion₂.mp $ hsub hx
      simp at ht
  | cons a L ih =>
      intro hcl hsub
      have hsub' : s ⊆ g a ∪ ⋃ t ∈ L, g t := by simp_all
      have hacl := hcl a $ mpr_ mem_cons $ m51 rfl
      have hUcl :=
        isClosed_biUnion L.finite_toSet
          (fun t ht => hcl t $ mpr_ mem_cons $ inr ht)
      rcases isPreirreducible_iff_isClosed_union_isClosed.mp hs.2 _ _ hacl hUcl hsub' with h | h
      simp_all
      simp_all

theorem quasiCompact_strictTransformImmersion {X' X : Sch}
    [NoetherianSpace ↥X'] (pi_ : X' ⟶ X) (Z J : ISD X) :
    QuasiCompact $ strictTransformImmersion pi_ Z J := by
  have : AlgebraicGeometry.IsPreimmersion $ strictTransformImmersion pi_ Z J := by
    rw [strictTransformImmersion_eq]
    infer_instance
  refine ⟨fun U _ _ => ?_⟩
  exact mpr_ ((strictTransformImmersion pi_ Z J).isEmbedding.isInducing.isCompact_iff) $ isCompact _

theorem mem_support_strictTransform {X' X : Sch} (pi_ : X' ⟶ X)
    (Z J : ISD X)
    (hqc : QuasiCompact $ strictTransformImmersion pi_ Z J) x
    (h1 : ⇑pi_.base x ∈ support J) (h2 : ⇑pi_.base x ∉ support Z) :
    x ∈ support (strictTransform pi_ Z J) := by
  have hxr : x ∈ range ⇑(cmI J pi_).subschemeι.base := by
    rw [range_base_subschemeio]
    exact mpr_ (mem_support_comap pi_ J x) h1
  obtain ⟨y, hy⟩ := hxr
  have h3 : ⇑(cmI J pi_).subschemeι.base y ∉ spI (cmI Z pi_) := by
    intro hc
    have h5 := mp_ (mem_support_comap pi_ Z _) hc
    rw [hy] at h5
    exact h2 h5
  have hyo : y ∈ Blowup.strictTransformOpens pi_ Z J := by
    rwa [Blowup.strictTransformOpens_eq]
  have hyr : y ∈ Set.range ⇑(Blowup.strictTransformOpens pi_ Z J).ib := by
    have hrio := (Blowup.strictTransformOpens pi_ Z J).range_ι
    rwa [hrio]
  obtain ⟨y', hy'⟩ := hyr
  have hcomp : ⇑(strictTransformImmersion pi_ Z J).base y' = x := by
    rw [Blowup.strictTransformImmersion_eq]
    show ⇑(cmI J pi_).subschemeι.base (⇑(Blowup.strictTransformOpens pi_ Z J).ib y') = x
    rw [hy', hy]
  have hfin : x ∈ ((spI (Blowup.strictTransform pi_ Z J) : Closeds ↥X')
      : Set ↥X') := by
    rw [strictTransform_eq_ker, support_ker]
    exact subset_closure ⟨y', hcomp⟩
  exact hfin

section
variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y] {pY} [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY)
section
variable (j : ℕ)
def principalizationSequenceIdeal :
    IdealSheafData $ S.ambientLevel j :=
  S.principalizationSequence.ideal j

section
variable (hj : j < S.ambientLength)
include hj
theorem exceptionalIdeal_mul_weakTransform_succ :
    exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j) * principalizationSequenceIdeal S (j + 1)
      = (principalizationSequenceIdeal S j).comap (S.ambientBlowupMorphism j) :=
  S.principalizationSequence.ideal_succ j hj

theorem weakTransform_le_ambientCenter : principalizationSequenceIdeal S j ≤ S.ambientCenter j :=
  (vanishesAlong_iff_le _ _).mp $ S.principalizationSequence.ideal_vanishes j hj

theorem boundary_succ_eq :
    S.boundary (j + 1)
      = List.map (strictTransform (S.ambientBlowupMorphism j) $ S.ambientCenter j) (S.boundary j)
        ++ [exceptionalIdeal (S.ambientBlowupMorphism j) $ S.ambientCenter j] :=
  S.principalizationSequence.boundary_succ j hj
end

theorem mem_range_strictTransformio_iff
    x :
    x ∈ range ⇑(S.strictTransformio j).base ↔ x ∈ support (S.strictTransformIdeal j) := by
  let _a0 := ((spI (S.strictTransformIdeal j) : Closeds ↥(S.ambientLevel j)) : Set ↥(S.ambientLevel j))
  have h : range ⇑(S.strictTransformio j).base
      = _a0 := by
    rw [S.strictTransformio_eq_subschemeio j]
    exact range_base_subschemeio _
  constructor
  intro hx
  have h2 := hx
  rwa [h] at h2
  intro hx
  have h2 : x ∈ _a0 := hx
  rwa [← h] at h2
end

section
variable (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j))
include hN
theorem support_weakTransform_subset_range_or_boundary
    (hbase : ∀ x : ↥(S.ambientLevel 0), x ∈ (principalizationSequenceIdeal S 0).support →
      x ∈ range ⇑(S.strictTransformio 0).base) :
    ∀ j ≤ S.ambientLength, ∀ x : ↥(S.ambientLevel j), x ∈ (principalizationSequenceIdeal S j).support →
      x ∈ range ⇑(S.strictTransformio j).base ∨ ∃ E ∈ S.boundary j, x ∈ E.support := by
  intro j
  induction j with
  | zero =>
      intro _ x hx
      exact m51 $ hbase x hx
  | succ j ih =>
      intro hj x hx
      have hjlt := hj
      have hNs := hN (j + 1) hj
      have hNSs : m86 ↥(S.ambientLevel $ j + 1) := inferInstance
      have hxp :=
        (mem_support_mul (exceptionalIdeal (S.ambientBlowupMorphism j) $ S.ambientCenter j)
          (principalizationSequenceIdeal S $ j + 1) x).mpr $ m61 hx
      rw [exceptionalIdeal_mul_weakTransform_succ S j hjlt] at hxp
      have hx1 :=
        (mem_support_comap (S.ambientBlowupMorphism j) (principalizationSequenceIdeal S j) x).mp hxp
      by_cases hexc : x ∈ spI (exceptionalIdeal (S.ambientBlowupMorphism j) $ S.ambientCenter j)
      have hmem1 : exceptionalIdeal (S.ambientBlowupMorphism j) (S.ambientCenter j) ∈ S.boundary (j + 1) := by
        rw [boundary_succ_eq S j hjlt]
        simp
      exact inr ⟨_, hmem1, hexc⟩
      have hnc : ⇑(S.ambientBlowupMorphism j).base x ∉ spI (S.ambientCenter j) := by
        intro hc
        apply hexc
        have h6 :=
          (mem_support_comap (S.ambientBlowupMorphism j) (S.ambientCenter j) x).mpr hc
        rwa [exceptionalIdeal_eq_comap]
      rcases ih (le_of_lt hjlt) (⇑(S.ambientBlowupMorphism j).base x) hx1 with hA | ⟨E, hE, hxE⟩
      refine m51 ?_
      have h1 :=
        (mem_range_strictTransformio_iff S j _).mp hA
      have h2 := mem_support_strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j)
        (S.strictTransformIdeal j)
        (quasiCompact_strictTransformImmersion (S.ambientBlowupMorphism j) (S.ambientCenter j)
          (S.strictTransformIdeal j)) x h1 hnc
      refine mpr_ (mem_range_strictTransformio_iff S (j + 1) x) ?_
      rwa [S.strictTransformIdeal_succ_eq_strictTransform j]
      have hmem1 : strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j) E
          ∈ S.boundary (j + 1) := by
        rw [boundary_succ_eq S j hjlt]
        simp [mem_append, mem_map]
        exact m51 ⟨E, hE, rfl⟩
      have hmem2 := mem_support_strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j) E
        (quasiCompact_strictTransformImmersion (S.ambientBlowupMorphism j) (S.ambientCenter j) E) x hxE hnc
      exact inr ⟨_, hmem1, hmem2⟩

theorem detachedClopenInCenter_of_isNoetherian_of_support
    (hsupp : ∀ j ≤ S.ambientLength, ∀ x : ↥(S.ambientLevel j), x ∈ (principalizationSequenceIdeal S j).support →
      x ∈ range ⇑(S.strictTransformio j).base ∨ ∃ E ∈ S.boundary j, x ∈ E.support)
    (hmk : ∀ j ≤ S.ambientLength, ∀ C ∈ irreducibleComponents ↥(S.strictTransform j), ∀ E ∈ S.boundary j,
      ¬ (⇑(S.strictTransformio j).base '' C ⊆
        ((E.support : Closeds ↥(S.ambientLevel j)) : Set ↥(S.ambientLevel j)))) :
    S.DetachedClopenInCenter := by
  intro i hi
  have hNi := hN i hi.le
  let _a1 := S.ambientLevel i
  have hNSi : NoetherianSpace ↥_a1 := inferInstance
  have hnoeth :=
    S.noetherianSpace_strictTransform_of_ambientLevel i hNSi
  have hsmW := S.principalizationSequence.smooth_center_subschemeio i hi
  let _a0 := siI $ S.ambientCenter i
  let _a8 := _a0 ≫ S.schemeAtToSpec i
  have hredW :=
    smooth_isReduced _a8 hsmW
  let _a3 := subS $ S.ambientCenter i
  have hNW : NoetherianSpace ↥_a3 := inferInstance
  let _a2 := spI $ S.strictTransformIdeal i
  have hrangeA : range ⇑(S.strictTransformio i).base
      = (_a2
          : Set ↥_a1) := by
    rw [S.strictTransformio_eq_subschemeio i]
    exact range_base_subschemeio _
  let _a4 := spI $ S.ambientCenter i
  let _a7 := (_a4 : Set ↥_a1)
  have hrangeC : range ⇑_a0.base
      = _a7 :=
    range_base_subschemeio _
  have hdom := fun x =>
    smooth_isDomain_stalk _a8 hsmW x
  have hsubr : ⇑(S.strictTransformio i).base '' S.discardedLocus i
      ⊆ range ⇑_a0.base := by
    rw [hrangeC]
    exact S.image_discardedLocus_subset_support i
  have hRcl : IsClosed (range ⇑(S.strictTransformio i).base ∪
      ⋃ E ∈ S.boundary i,
        suppI E) := by
    refine IsClosed.union ?_ $ isClosed_biUnion (S.boundary i).finite_toSet fun E _ => (spI E).2
    rw [hrangeA]
    exact _a2.2
  have hcomp : ∀ C ∈ S.discardedComponents i,
      ⇑_a0.base ⁻¹' (⇑(S.strictTransformio i).base '' C)
        ∈ irreducibleComponents ↥_a3 := by
    intro C hC
    obtain ⟨hCcomp, hCsub⟩ := mp_ (S.mem_discardedComponents_iff i C) hC
    have himg :=
      hCcomp.1.image _ ((S.strictTransformio i).continuous).continuousOn
    have hsubrC : ⇑(S.strictTransformio i).base '' C
        ⊆ range ⇑_a0.base := by
      rwa [hrangeC]
    refine ⟨isIrreducible_preimage_of_isEmbedding
      ((S.ambientCenter i).subschemeι.isEmbedding) himg hsubrC, ?_⟩
    intro s hs hKle
    have hcimg := image_preimage_eq_of_subset hsubrC
    have hFirr :=
      (hs.image _ (_a0.continuous).continuousOn).closure
    have hCsubF : ⇑(S.strictTransformio i).base '' C
        ⊆ closure (⇑_a0.base '' s) := by
      rw [← hcimg]
      exact (image_mono hKle).trans subset_closure
    have hcsI : ⇑_a0.base '' s
        ⊆ range ⇑(S.strictTransformio i).base ∪
          ⋃ E ∈ S.boundary i,
            suppI E := by
      intro z hz
      obtain ⟨w, -, rfl⟩ := hz
      have h1 : ⇑_a0.base w ∈ _a4 := by
        have h0 : ⇑_a0.base w
            ∈ _a7 := by
          rw [← hrangeC]
          exact mem_range_self w
        exact h0
      have h2 :=
        mem_support_of_le (weakTransform_le_ambientCenter S i hi) _ h1
      rcases hsupp i hi.le _ h2 with hA | ⟨E, hE, hxE⟩
      exact m51 hA
      exact inr $ mem_biUnion hE hxE
    have hFsub :=
      (IsClosed.closure_subset_iff hRcl).mpr hcsI
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp hFirr.2 _ _
        (by rw [hrangeA]; exact _a2.2)
        (isClosed_biUnion (S.boundary i).finite_toSet fun E _ => (spI E).2)
        hFsub with hcase | hcase
    have hG := hCcomp.2
      (isIrreducible_preimage_of_isEmbedding ((S.strictTransformio i).isEmbedding) hFirr hcase)
      (fun z hz => hCsubF $ mem_image_of_mem _ hz)
    have hclosure : closure (⇑_a0.base '' s)
        ⊆ ⇑(S.strictTransformio i).base '' C := by
      rw [← image_preimage_eq_of_subset hcase]
      exact image_mono hG
    intro z hz
    exact hclosure $ subset_closure $ mem_image_of_mem _ hz
    obtain ⟨E, hE, hFsubE⟩ := exists_mem_list_subset_of_isIrreducible hFirr
      (fun E : ISD _a1 =>
        suppI E)
      (S.boundary i) (fun E _ => (spI E).2) hcase
    exact ((hmk i hi.le C hCcomp E hE) $ hCsubF.trans hFsubE).elim
  have hPreimageDiscarded : ⇑_a0.base ⁻¹'
      (⇑(S.strictTransformio i).base '' S.discardedLocus i)
      = ⋃₀ ((fun C =>
          ⇑_a0.base ⁻¹' (⇑(S.strictTransformio i).base '' C))
            '' S.discardedComponents i) := by
    ext z
    constructor
    intro hz
    obtain ⟨w, hw, hwz⟩ := hz
    rw [S.discardedLocus_eq_sUnion_discardedComponents i] at hw
    obtain ⟨C, hC, hwC⟩ := hw
    exact ⟨_, ⟨C, hC, rfl⟩, ⟨w, hwC, hwz⟩⟩
    intro hz
    obtain ⟨t, ⟨C, hC, rfl⟩, hzt⟩ := hz
    obtain ⟨w, hwC, hwz⟩ := hzt
    refine ⟨w, ?_, hwz⟩
    rw [S.discardedLocus_eq_sUnion_discardedComponents i]
    exact ⟨C, hC, hwC⟩
  have hopenU : IsOpen $ ⇑_a0.base ⁻¹'
      (⇑(S.strictTransformio i).base '' S.discardedLocus i) := by
    rw [hPreimageDiscarded]
    refine isOpen_sUnion_of_irreducibleComponents _ ?_
    intro Zs hZs W hW hWnot
    obtain ⟨C, hC, rfl⟩ := hZs
    rw [disjoint_left]
    intro z hz1 hz2
    have heqq := irreducibleComponents_eq_of_stalk_isDomain _ hdom (hcomp C hC) hW hz1 hz2
    refine hWnot ?_
    rw [← heqq]
    exact ⟨C, hC, rfl⟩
  have hembA : IsClosedEmbedding ⇑(S.strictTransformio i).base := by
    refine ⟨(S.strictTransformio i).isEmbedding, ?_⟩
    rw [hrangeA]
    exact _a2.2
  have hclosedU :=
    (hembA.isClosedMap _ $ S.isClosed_discardedLocus i).preimage
      _a0.continuous
  obtain ⟨U, hUcoe⟩ : ∃ U : Opn _a3,
      U
        = ⇑_a0.base ⁻¹'
          (⇑(S.strictTransformio i).base '' S.discardedLocus i) :=
    ⟨⟨_, hopenU⟩, rfl⟩
  have hUcl := hclosedU
  rw [← hUcoe] at hUcl
  have :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed U hUcl
  have : IsReduced (S.discardedIdeal i).subscheme := by
    rw [S.discardedIdeal_eq_vanishingIdeal i]
    exact isReduced_subscheme_vanishingIdeal _ _
  have hRangeDiscarded : range ⇑(S.discardedio i).base = S.discardedLocus i := by
    rw [range_base_subschemeio _, S.discardedIdeal_eq_vanishingIdeal i, coe_support_vanishingIdeal,
      S.coe_discardedLocusClosure i]
  let _a5 := S.discardedio i ≫ S.strictTransformio i
  have hrf : range ⇑_a5.base
      = ⇑(S.strictTransformio i).base '' S.discardedLocus i := by
    rw [range_comp_base, hRangeDiscarded]
  have hrU := U.range_ι
  let _a10 := opI U ≫ _a0
  have hrg : range ⇑_a10.base
      = ⇑(S.strictTransformio i).base '' S.discardedLocus i := by
    rw [range_comp_base, hrU, hUcoe]
    exact image_preimage_eq_of_subset hsubr
  obtain ⟨e, he⟩ := exists_iso_of_range_base_eq _a5
    _a10 $ tr_ hrf hrg.symm
  exact ⟨U, hUcl, e, he⟩
end
end

section
variable (A : PrincipalizationAlgorithm) (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
theorem detachedClopenInCenter_ofAffine (k : Type) [Field k] [CharZero k] Y
    [IsAffine Y] [IsReduced Y]
    pY [LocallyOfFiniteType pY]
    [QuasiCompact pY] :
    (ofAffine A hemb hsnc hsm k Y pY).DetachedClopenInCenter := by
  let _c0 := ofAffine A hemb hsnc hsm k Y pY
  have hN := isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY
  have hcl0 :
      IsClosed $ range ⇑(_c0.strictTransformio 0).base := by
    rw [_c0.strictTransformio_eq_subschemeio 0, range_base_subschemeio]
    exact (spI $ _c0.strictTransformIdeal 0).2
  let _a0 := affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY
  have heq : principalizationSequenceIdeal _c0 0
      = vanishingIdeal
        (⟨range ⇑(_c0.strictTransformio 0).base, hcl0⟩ :
          Closeds ↥(_c0.ambientLevel 0)) :=
    OpenImmersionRestriction.principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal
      _a0 A hcl0
  have hbase : ∀ x : ↥(_c0.ambientLevel 0),
      x ∈ spI (principalizationSequenceIdeal _c0 0) →
        x ∈ range ⇑(_c0.strictTransformio 0).base := by
    intro x hx
    rw [heq] at hx
    exact mem_of_mem_support_vanishingIdeal _ x hx
  refine detachedClopenInCenter_of_isNoetherian_of_support _ hN (support_weakTransform_subset_range_or_boundary _ hN hbase) ?_
  intro j hj C hC E hE
  exact OpenImmersionRestriction.not_image_irreducibleComponent_subset_boundary_support
    _a0 A j hj C hC E hE

theorem affineDetachedSmooth :
    AffineDetachedSmooth A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  obtain ⟨T, hTcl, e, he⟩ := detachedClopenInCenter_ofAffine A hemb hsnc hsm k Y pY i hi
  let _a0 := ofAffine A hemb hsnc hsm k Y pY
  have hsmC : Smooth
      (siI (_a0.ambientCenter i)
        ≫ _a0.schemeAtToSpec i) :=
    _a0.principalizationSequence.smooth_center_subschemeio i hi
  have : IsClosedImmersion T.i :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed T hTcl
  have key := congrArg
    (fun m => m ≫ _a0.schemeAtToSpec i) he
  simp only [assoc] at key
  rw [← key]
  infer_instance

theorem affineDetachedClopenInCenter :
    AffineDetachedClopenInCenter A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact detachedClopenInCenter_ofAffine A hemb hsnc hsm k Y pY
end





section
variable {W : Type} [TopologicalSpace W]
theorem subset_or_subset_of_isIrreducible {s a b : Set W}
    (hs : IsIrreducible s) (ha : IsClosed a) (hb : IsClosed b) (h : s ⊆ a ∪ b) :
    s ⊆ a ∨ s ⊆ b :=
  isPreirreducible_iff_isClosed_union_isClosed.mp hs.2 a b ha hb h

section
variable {s : Set W} (hs : IsIrreducible s)
include hs
theorem exists_mem_finset_subset_of_isIrreducible (F : Finset (Set W))
    (hcl : ∀ Z ∈ F, IsClosed Z) (hsub : s ⊆ ⋃₀ (F : Set $ Set W)) :
    ∃ Z ∈ F, s ⊆ Z := by
  classical
  revert hcl hsub
  refine induction_on F ?_ ?_
  intro _ hsub'
  obtain ⟨x, hx⟩ := an1 hs
  have hx' := hsub' hx
  simp at hx'
  intro a G _ ih hcl' hsub'
  have hcla := hcl' a $ mem_insert_self a G
  have hclG := fun Z hZ => hcl' Z $ mem_insert_of_mem hZ
  let _m0 := ((G : Finset $ Set W) : Set $ Set W)
  have hclU : IsClosed $ ⋃₀ _m0 := by
    rw [sUnion_eq_biUnion]
    exact isClosed_biUnion G.finite_toSet fun Z hZ => hclG Z hZ
  have hsub2 : s ⊆ a ∪ ⋃₀ _m0 := by
    intro y hy
    have hy' := hsub' hy
    rwa [coe_insert, sUnion_insert] at hy'
  rcases subset_or_subset_of_isIrreducible hs hcla hclU hsub2 with hh | hh
  exact ⟨a, mem_insert_self a G, hh⟩
  obtain ⟨Z, hZ, hZs⟩ := ih hclG hh
  exact ⟨Z, mem_insert_of_mem hZ, hZs⟩

theorem exists_mem_of_isIrreducible_subset_sUnion {F : Set (Set W)} (hF : F.Finite)
    (hcl : ∀ Z ∈ F, IsClosed Z) (hsub : s ⊆ ⋃₀ F) :
    ∃ Z ∈ F, s ⊆ Z := by
  classical
  obtain ⟨Z, hZ, hsZ⟩ :=
    exists_mem_finset_subset_of_isIrreducible hs hF.toFinset
      (fun Z hZ => hcl Z $ hF.mem_toFinset.mp hZ)
      (by
        intro y hy
        obtain ⟨Z, hZF, hyZ⟩ := hsub hy
        refine ⟨Z, ?_, hyZ⟩
        simpa only [mem_coe, mem_toFinset] using hZF)
  exact ⟨Z, hF.mem_toFinset.mp hZ, hsZ⟩
end
end

section
variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] {f : X → Z} (hf : IsClosedEmbedding f)
include hf
section
variable {t : Set Z} (hran : t ⊆ range f)
include hran
theorem isPreirreducible_preimage_of_isClosedEmbedding (ht : IsPreirreducible t) :
    IsPreirreducible $ f ⁻¹' t := by
  intro u v hu hv hsu hsv
  obtain ⟨U, hU, hUeq⟩ := hf.isInducing.isOpen_iff.mp hu
  obtain ⟨V, hV, hVeq⟩ := hf.isInducing.isOpen_iff.mp hv
  obtain ⟨x, hxt, hxu⟩ := hsu
  obtain ⟨y, hyt, hyv⟩ := hsv
  have hxU : f x ∈ U := by
    have hx' : x ∈ preimage f U := by rw [hUeq]
                                      exact hxu
    exact hx'
  have hyV : f y ∈ V := by
    have hy' : y ∈ preimage f V := by rw [hVeq]
                                      exact hyv
    exact hy'
  obtain ⟨z, hzt, hzU, hzV⟩ := ht U V hU hV ⟨f x, hxt, hxU⟩ ⟨f y, hyt, hyV⟩
  obtain ⟨w, rfl⟩ := hran hzt
  refine ⟨w, hzt, ?_, ?_⟩
  have hw : w ∈ preimage f U := hzU
  rwa [hUeq] at hw
  have hw : w ∈ preimage f V := hzV
  rwa [hVeq] at hw

theorem isIrreducible_preimage_of_isClosedEmbedding (ht : IsIrreducible t) :
    IsIrreducible $ f ⁻¹' t := by
  refine ⟨?_, isPreirreducible_preimage_of_isClosedEmbedding hf hran ht.2⟩
  obtain ⟨z, hz⟩ := an1 ht
  obtain ⟨w, rfl⟩ := hran hz
  exact ⟨w, hz⟩
end
end

section
variable (A : PrincipalizationAlgorithm)
section
variable (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth) (k : Type) [Field k] [CharZero k] (Y) (pY) [LocallyOfFiniteType pY] [QuasiCompact pY] [IsReduced Y] [IsAffine Y] (i : ℕ)
theorem discardedComponents_subset_irreducibleComponents :
    (ofAffine A hemb hsnc hsm k Y pY).discardedComponents i ⊆
      irreducibleComponents ↥((ofAffine A hemb hsnc hsm k Y pY).strictTransform i) := by
  intro C hC
  exact an1 $ mp_ ((ofAffine A hemb hsnc hsm k Y pY).mem_discardedComponents_iff i C) hC

theorem range_discardedio_eq_sUnion_discardedComponents
    (hi : i < (ofAffine A hemb hsnc hsm k Y pY).ambientLength) :
    range ⇑((ofAffine A hemb hsnc hsm k Y pY).discardedio i).base =
      ⋃₀ ((ofAffine A hemb hsnc hsm k Y pY).discardedComponents i) := by
  let _c0 := ofAffine A hemb hsnc hsm k Y pY
  let _a0 := affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY
  have hNoeth : NoetherianSpace
      ↥(_c0.strictTransform i) :=
    noetherianSpace_strictTransform_of_isNoetherian (_a0.toEmbeddedBlowupSequence A)
      (OpenImmersionRestriction.isNoetherian_schemeAt_toEmbeddedBlowupSequence _a0 A) i
      (le_of_lt hi)
  have h1 : range ⇑(_c0.discardedio i).base =
      (spI (_c0.discardedIdeal i) :
        Set ↥(_c0.strictTransform i)) :=
    range_subschemeι
      (_c0.discardedIdeal i)
  rw [h1, discardedIdeal_eq_vanishingIdeal, coe_support_vanishingIdeal,
    coe_discardedLocusClosure, discardedLocus_eq_sUnion_discardedComponents]
end

theorem affineStrictTransformEmptyAtLast_of_isFunctorialPrincipalization (hA : IsFunctorialPrincipalization A)
    (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace)
    (hsm : AffineSpaceIsSmooth) :
    AffineStrictTransformEmptyAtLast A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  let _s0 := ofAffine A hemb hsnc hsm k Y pY
  show _s0.strictTransformIdeal
      _s0.ambientLength = ⊤
  let _s1 := affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY
  have htop : (OpenImmersionRestriction.principalizationOfEmbedding k Y pY _s1 A).ideal
      (_s1.toEmbeddedBlowupSequence A).length = ⊤ := by
    have h := hA.lastIdeal_eq_top k _s1.ambient
      _s1.ambientStruct
      (ker _s1.emb)
      _s1.nonzeroOnComponents_ker
      ([])
      _s1.sncEmpty
    rwa [IdealBlowupSequence.lastIdeal_eq] at h
  let _a0 := _s0.strictTransform _s0.ambientLength
  have hno : ∀ C,
      C ∉ irreducibleComponents ↥_a0 := by
    intro C hC
    obtain ⟨xi_, hxi_⟩ := sober hC.1 $ isClosed_of_mem_irreducibleComponents _ hC
    obtain ⟨-, hord⟩ := OpenImmersionRestriction.agreesWithComponentsOrderOne_of_le _s1 A
      (_s1.toEmbeddedBlowupSequence A).length le_rfl C hC xi_ hxi_ $ (EmbeddedBlowupSequence.isClosedEmbedding_strictTransformio (_s1.toEmbeddedBlowupSequence A) _).isClosedMap _ $ isClosed_of_mem_irreducibleComponents _ hC
    rw [htop] at hord
    have h01 := st_ (orderAt_top _) hord
    simp at h01
  have : IsEmpty ↥_a0 := by
    constructor
    intro x
    exact hno (irreducibleComponent x) $ irreducibleComponent_mem_irreducibleComponents x
  refine mpr_ (eq_top_iff_support_eq_empty _) ?_
  rw [← range_subschemeι]
  exact range_eq_empty _

theorem affineDetachedComponentsNotInBoundary
    (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace)
    (hsm : AffineSpaceIsSmooth) :
    AffineDetachedComponentsNotInBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi j hj C hC hsubset
  let _s0 := ofAffine A hemb hsnc hsm k Y pY
  have hle : i ≤ _s0.ambientLength := le_of_lt hi
  let _a0 := affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY
  let _a2 := _s0.strictTransform i
  let _a3 := OpenImmersionRestriction.isNoetherian_schemeAt_toEmbeddedBlowupSequence _a0 A
  have hNoeth : NoetherianSpace
      ↥_a2 :=
    noetherianSpace_strictTransform_of_isNoetherian (_a0.toEmbeddedBlowupSequence A)
      _a3 i hle
  have hfemb : IsClosedEmbedding
      ⇑(_s0.discardedio i).base :=
    (isClosedEmbedding
    ((ofAffine A hemb hsnc hsm k Y pY).discardedIdeal i).subschemeι)
  have hrange : range ⇑(_s0.discardedio i).base =
      ⋃₀ (_s0.discardedComponents i) :=
    range_discardedio_eq_sUnion_discardedComponents A hemb hsnc hsm k Y pY i hi
  have hsubComp : _s0.discardedComponents i ⊆
      irreducibleComponents ↥_a2 :=
    discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i
  have hfin : (_s0.discardedComponents i).Finite :=
    (finite_irreducibleComponents).subset hsubComp
  have hCirr : IsIrreducible C := an1 hC
  have himgIrr :
      IsIrreducible $ ⇑(_s0.discardedio i).base '' C :=
    hCirr.image _ hfemb.continuous.continuousOn
  obtain ⟨C0_, hC0mem, hC0sub⟩ :=
    exists_mem_of_isIrreducible_subset_sUnion himgIrr hfin
      (fun Z hZ => isClosed_of_mem_irreducibleComponents _ $ hsubComp hZ)
      (by rw [← hrange]; exact image_subset_range _ _)
  have hC0ic : C0_ ∈ irreducibleComponents
      ↥_a2 := hsubComp hC0mem
  have hC0range :
      C0_ ⊆ range ⇑(_s0.discardedio i).base := by
    rw [hrange]
    exact subset_sUnion_of_mem hC0mem
  have hCeq : ⇑(_s0.discardedio i).base ⁻¹' C0_ ⊆ C :=
    hC.2 (isIrreducible_preimage_of_isClosedEmbedding hfemb hC0range hC0ic.1) fun z hz => hC0sub ⟨z, hz, rfl⟩
  have himg : ⇑(_s0.discardedio i).base '' C = C0_ := by
    refine m15 hC0sub ?_
    intro z hz
    obtain ⟨w, rfl⟩ := hC0range hz
    exact ⟨w, hCeq hz, rfl⟩
  obtain ⟨xi_, hxi_⟩ := sober hC0ic.1 $ isClosed_of_mem_irreducibleComponents _ hC0ic
  have hximem : xi_ ∈ ⇑(_s0.discardedio i).base '' C := by
    rw [himg]
    exact hxi_.mem
  obtain ⟨w, hwC, hw⟩ := hximem
  let _a1 := bsM (_s0.strictTransformio i) xi_
  have hmem : _a1 ∈
      ⇑(_s0.discardedio i ≫
        _s0.strictTransformio i).base '' C := by
    refine ⟨w, hwC, ?_⟩
    show bsM (_s0.strictTransformio i)
        (bsM (_s0.discardedio i) w) =
      _a1
    rw [hw]
  have hx := hsubset hmem
  have hclear := EmbeddedBlowupSequence.avoidsCenters_strictTransformio_of_isGenericPoint
    (_a0.toEmbeddedBlowupSequence A)
    _a3 i hle
    C0_ hC0ic xi_ hxi_
  exact OpenImmersionRestriction.not_avoidsCenters_of_mem_boundary_support _a0 A i hle
    (get (_s0.boundary i) ⟨j, hj⟩)
    (get_mem ..) _ hx hclear
end





def IsCompatibleWithSmoothOfRelativeDimension (B : AffineResolutionRule) : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y V : Sch)
    (pY : Y ⟶ Sp k) (pV : V ⟶ Sp k)
    [IsAffine Y] [IsAffine V]
    [IsReduced Y] [IsReduced V]
    [LocallyOfFiniteType pY] [QuasiCompact pY]
    [LocallyOfFiniteType pV] [QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [SmoothOfRelativeDimension r u],
    u ≫ pY = pV → IsPullbackBlowupSequence u (B k V pV) (B k Y pY)

section
variable {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) (r : ℕ)
theorem smoothOfRelativeDimension_comp_zero [SmoothOfRelativeDimension r f]
    [SmoothOfRelativeDimension 0 g] :
    SmoothOfRelativeDimension r $ f ≫ g := by
  have h : m158 (r + 0) $ f ≫ g := inferInstance
  simpa using h

theorem smoothOfRelativeDimension_zero_comp [SmoothOfRelativeDimension 0 f]
    [SmoothOfRelativeDimension r g] :
    SmoothOfRelativeDimension r $ f ≫ g := by
  have h : m158 (0 + r) $ f ≫ g := inferInstance
  simpa using h
end

theorem respectsIso_smoothOfRelativeDimension (r : ℕ) :
    RespectsIso
      (@SmoothOfRelativeDimension r : MorphismProperty Sch) := by
  have hL : RespectsLeft
      (@m158 r)
      (isomorphisms Sch) := by
    constructor
    intro X Y Z i hi f hf
    have : IsOpenImmersion i := inferInstance
    have : m158 0 i := inferInstance
    exact smoothOfRelativeDimension_zero_comp i f r
  have hR : RespectsRight
      (@m158 r)
      (isomorphisms Sch) := by
    constructor
    intro X Y Z i hi f hf
    have : IsOpenImmersion i := inferInstance
    have : m158 0 i := inferInstance
    exact smoothOfRelativeDimension_comp_zero f i r
  exact ⟨⟩

theorem isZariskiLocalAtSource_smoothOfRelativeDimension (r : ℕ) :
    AlgebraicGeometry.IsZariskiLocalAtSource
      (@SmoothOfRelativeDimension r : MorphismProperty Sch) := by
  have := respectsIso_smoothOfRelativeDimension r
  refine mk' ?_ ?_
  intro X Y f U hf
  have := hf
  have : m158 0 U.i := inferInstance
  exact smoothOfRelativeDimension_zero_comp U.i f r
  intro X Y f ι U hU H
  refine ⟨fun x => ?_⟩
  have htop : x ∈ (⊤ : Opn X) := trivial
  rw [← hU] at htop
  obtain ⟨i, hi⟩ := mp_ mem_iSup htop
  obtain ⟨H'⟩ := H i
  obtain ⟨U0_, hU0_, W, hW, hxW, e, hsm⟩ := H' ⟨x, hi⟩
  have e' : (U i).i.im W ≤ preU f U0_ := by
    rintro x ⟨w, hw, rfl⟩
    simpa using e hw
  let _a0 := U i
  let _m0 := _a0.i.im W
  have hle : W ≤ opPre _a0 _m0 := by
    intro w hw
    exact ⟨w, hw, rfl⟩
  refine ⟨U0_, hU0_, _a0.i.im W, hW.image_of_isOpenImmersion (U i).i,
    ⟨⟨x, hi⟩, hxW, rfl⟩, e', ?_⟩
  have h1 := m91 (U i).i f U0_ _m0 W e' hle
  have h2 := Scheme.Opens.ι_appLE (U i) _m0 W hle
  have h3 : pMap X (homOfLE $ le_refl _m0).op
      = 𝟙 (pObj X $ op _m0) := by
    simp
  have h23 := tr_ h2 h3
  exact Eq.mp (congrArg (fun m =>
    RingHom.IsStandardSmoothOfRelativeDimension r $ m4 m) $ h1.symm.trans $ tr_ (congrArg (fun m => appLE f U0_ _m0 e' ≫ m) h23) $ comp_id _) hsm

theorem smoothOfRelativeDimension_opensCoprodMapOfRefinement {X' X : Sch} (ph_ : X' ⟶ X) (r : ℕ)
    [SmoothOfRelativeDimension r ph_] {ι ka_ : Type}
    (U : ι → Opn X) (V : ka_ → Opn X') (be_ : ka_ → ι)
    (hbe_ : ∀ a, V a ≤ ph_ ⁻¹ᵁ (U $ be_ a)) :
    SmoothOfRelativeDimension r $ opensCoprodMapOfRefinement ph_ U V be_ hbe_ := by
  have := isZariskiLocalAtSource_smoothOfRelativeDimension r
  refine sigmaDesc ?_
  intro a
  have : m158 0
      (Sigma.ι (fun i => oSch $ U i) $ be_ a) := inferInstance
  exact smoothOfRelativeDimension_comp_zero _ _ r

theorem exists_affine_etale_cover_of_smoothOfRelativeDimension {k : Type} [Field k]
    {X X' : Sch}
    (f : X ⟶ Sp k) (f' : X' ⟶ Sp k)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced X]
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsReduced X']
    (ph_ : X' ⟶ X) (r : ℕ) [SmoothOfRelativeDimension r ph_]
    (hph : ph_ ≫ f = f') :
    ∃ (W : Sch) (q : W ⟶ Sp k) (c : W ⟶ X)
      (W' : Sch) (q' : W' ⟶ Sp k) (c' : W' ⟶ X') (ps_ : W' ⟶ W),
      IsAffine W ∧ IsReduced W ∧
        LocallyOfFiniteType q ∧ QuasiCompact q ∧
        Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ f = q ∧
      IsAffine W' ∧ IsReduced W' ∧
        LocallyOfFiniteType q' ∧ QuasiCompact q' ∧
        Etale c' ∧ AlgebraicGeometry.Surjective c' ∧ c' ≫ f' = q' ∧
      SmoothOfRelativeDimension r ps_ ∧ ps_ ≫ c = c' ≫ ph_ ∧ ps_ ≫ q = q' := by
  have hcX := QuasiCompact.compactSpace_of_compactSpace f
  have hcX' := QuasiCompact.compactSpace_of_compactSpace f'
  obtain ⟨ι, hio, U, hUaff, hUtop⟩ := exists_finite_affine_cover X
  obtain ⟨ka_, hka_, V, be_, hVaff, hbe_, hVtop⟩ := exists_finite_affine_cover_subordinate ph_ U hUtop
  have hWaff := isAffine_sigmaOpens X U hUaff
  have hW'aff := isAffine_sigmaOpens X' V hVaff
  let _a0 := sigmaOpensDesc X U ≫ f
  let _a1 := sigmaOpensDesc X' V ≫ f'
  exact ⟨sigmaOpens X U, _a0, sigmaOpensDesc X U,
    sigmaOpens X' V, _a1, sigmaOpensDesc X' V,
    opensCoprodMapOfRefinement ph_ U V be_ hbe_,
    hWaff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton _a0, inferInstance,
    surjective_sigmaOpensDesc X U hUtop, rfl,
    hW'aff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton _a1, inferInstance,
    surjective_sigmaOpensDesc X' V hVtop, rfl,
    smoothOfRelativeDimension_opensCoprodMapOfRefinement ph_ r U V be_ hbe_,
    opensCoprodMapOfRefinement_comp_sigmaOpensDesc ph_ U V be_ hbe_,
    (by rw [← assoc, opensCoprodMapOfRefinement_comp_sigmaOpensDesc, assoc, hph])⟩

section
variable (B : AffineResolutionRule)
theorem isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule
    (hB : IsCompatibleWithSmoothOfRelativeDimension B) (R : ResolutionRule)
    (hR : ∀ (k : Type) [Field k] [CharZero k] Y
      p
      [LocallyOfFiniteType p] [QuasiCompact p]
      [IsReduced Y], IsInducedByAffineRule B k Y p $ R k Y p) :
    IsCompatibleWithSmoothMorphisms R := by
  intro k _ _ X X' f f' _ _ _ _ _ _ ph_ r _ hph
  obtain ⟨W, q, c, W', q', c', ps_, hWaff, hWred, hqlft, hqqc, hcet, hcsurj, hcq,
    hW'aff, hW'red, hq'lft, hq'qc, hc'et, hc'surj, hc'q', hpssm, hpsc, hpsq⟩ :=
    exists_affine_etale_cover_of_smoothOfRelativeDimension f f' ph_ r hph
  have hsmph :=
    smooth r ph_
  have hsmps :=
    smooth r ps_
  have hflatph : Flat ph_ := inferInstance
  have hflatps : Flat ps_ := inferInstance
  have hflatc' : Flat c' := inferInstance
  have hcs := hcsurj.surj
  have hc's := hc'surj.surj
  have hA := hR k X f W q c hcq hcs
  have hA' := hR k X' f' W' q' c' hc'q' hc's
  have hC := hB k W W' q q' ps_ r hpsq
  have h1 :=
    isStrictPullbackSequenceOfBlowups_baseChange (R k X f) ph_
  have h2 :=
    isStrictPullbackSequenceOfBlowups_baseChange ((R k X f).baseChange ph_) c'
  have h3 := h2.comp h1
  have h4 :=
    isStrictPullbackSequenceOfBlowups_baseChange (B k W q) ps_
  have h5 : IsStrictPullbackBlowupSeq (c' ≫ ph_) ((B k W q).baseChange ps_) $ R k X f := by
    have h5' := h4.comp hA
    rwa [hpsc] at h5'
  have h6 := h3.isomorphic h5
  have h9 := hC.isomorphic h4.isPullbackSequenceOfBlowups_withoutIsoBlowups
  have h10 := h9.trans h6.withoutIsoBlowups.symm
  have h12 := hA'.isomorphic_of_isomorphic h2.withoutIsoBlowups h10
  exact h1.isPullbackSequenceOfBlowups_withoutIsoBlowups.of_isomorphic h12.symm

end

theorem strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm A
    (hemb : AffineEmbedsIntoAffineSpace) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace)
    (hsm : AffineSpaceIsSmooth) (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm) (hcmp : ClosedEmbeddingsRelatedByAutomorphism)
    (haff : ∀ (k : Type) [Field k] [CharZero k] Y
      p
      [IsAffine Y] [IsReduced Y]
      [LocallyOfFiniteType p] [QuasiCompact p],
      IsStrongResolution k Y p $ affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k Y p) :
    StrongResolutionOfSingularitiesCharZero :=
  by
    let B := affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex
    let hetale := isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp
    let hopen := isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization A hAlg hw hemb hsncE hsm hex hcmp
    let hfield : IsCompatibleWithFieldBaseChange $ affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex := by
      have key : IsCompatibleWithFieldBaseChange $ (embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule (affineSpacePresentedSelection hemb hsncE hsm).sel := by
        let R := embeddedResolutionRuleOfPrincipalization A hw
        let C := affineSpacePresentedSelection hemb hsncE hsm
        let hfield := embeddedResolutionRule_isCompatibleWithFieldBaseChange A hAlg hw
        intro k _ _ Y p _ _ _ _ K _ _ _ _ _
        let _a0 := C.sel k Y p
        have hsncK :=
          nilIsStrictNormalCrossingsOfSmooth K (baseChange _a0.ambientStruct K)
            (baseChangeToSpec _a0.ambientStruct K)
            (EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec _a0 K)
        have hkerK : NonzeroOnComponents $ (_a0.baseChangeEmb K).ker := by
          rw [ker_eq_comap_ker_of_isPullback_of_flat $ (EmbeddingDatum.isPullback_baseChangeEmb _a0 K).flip]
          exact NonzeroOnComponents.comap_of_flat _a0.nonzeroOnComponents_ker _
        let _a1 := baseChange p K
        let _a2 := baseChangeToSpec p K
        exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback (hfield k Y p _a0 K hkerK hsncK)
          ((isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp) K _a1 _a2
            (_a0.baseChange K hkerK hsncK)
            (C.sel K _a1 _a2)
            (C.basePres k Y p K hkerK hsncK)
            (C.pres K _a1 _a2))
      rw [affineSpacePresentedSelection_selection,
        toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
      exact key
    let hsmooth : IsCompatibleWithSmoothOfRelativeDimension $ affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex := by
      intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ u r _ hu
      have key := isPullbackBlowupSequence_presentedSelection_of_smooth (embeddedResolutionRuleOfPrincipalization A hw)
        (affineSpacePresentedSelection hemb hsncE hsm)
        (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
        (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
        (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw)
        (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm) hsm nilIsStrictNormalCrossingsOfSmooth
        k Y V pY pV u r hu
      rw [affineSpacePresentedSelection_selection] at key
      rw [← toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex,
        EmbeddedResolutionRule.toAffineResolutionRule_apply, EmbeddedResolutionRule.toAffineResolutionRule_apply]
      exact key
    have hcen : ∀ (k : Type) [Field k] [CharZero k] Y
        p [LocallyOfFiniteType p]
        [QuasiCompact p] [IsReduced Y]
        [IsAffine Y] i,
        i < (B k Y p).length → center (B k Y p) i ≠ ⊤ := by
      intro k _ _ Y p _ _ _ _ i hi
      exact AffineResolutionRule.center_ne_top B hopen k Y p i hi
    have H := existsGluedBlowupSequence_of_center_ne_top B hcen hetale
    obtain ⟨R, hcomes⟩ : ∃ R : ResolutionRule,
        ∀ (k : Type) [Field k] [CharZero k] Y
          p [LocallyOfFiniteType p]
          [QuasiCompact p] [IsReduced Y],
          IsInducedByAffineRule B k Y p $ R k Y p :=
      ⟨fun k _ _ Y p _ _ _ => (H k Y p).choose,
        fun k _ _ Y p _ _ _ => (H k Y p).choose_spec.2⟩
    have hsmF :=
      isCompatibleWithSmoothMorphisms_of_isInducedByAffineRule B hsmooth R hcomes
    refine ⟨R, ?_, hsmF, inducedRuleCompatibleWithFieldExtension B hopen hfield R hcomes⟩
    refine mpr_ (isStrongResolutionRule_iff R) ?_
    intro k _ _ X f _ _ _
    have hOI : ∀ i : X.affineCover.I₀,
        IsOpenImmersion $ X.affineCover.f i := fun _ => inferInstance
    have hA : ∀ i : X.affineCover.I₀,
        IsAffine $ X.affineCover.X i := fun _ => inferInstance
    have hRed : ∀ i : X.affineCover.I₀,
        IsReduced $ X.affineCover.X i := by
      intro i
      exact inferInstance
    have hLFT : ∀ i : X.affineCover.I₀,
        LocallyOfFiniteType $ X.affineCover.f i ≫ f := by
      intro i
      exact inferInstance
    have hqc : ∀ i : X.affineCover.I₀,
        QuasiCompact $ X.affineCover.f i ≫ f := by
      intro i
      have : CompactSpace ↥(X.affineCover.X i) := inferInstance
      exact quasiCompact_of_compactSpace_of_subsingleton $ X.affineCover.f i ≫ f
    have hCharts : ∀ i : X.affineCover.I₀,
        m158 0 $ X.affineCover.f i := by
      intro i
      exact inferInstance
    have d : LocalResolutionData k f $ R k X f := by
      refine
        { cover := X.affineCover
          seq := fun i =>
            R k (X.affineCover.X i) $ X.affineCover.f i ≫ f
          isPullback := ?_
          finiteType := hLFT
          isResolution := ?_ }
      intro i
      exact hsmF k X (X.affineCover.X i) f (X.affineCover.f i ≫ f)
        (X.affineCover.f i) 0 rfl
      intro i
      let Y := X.affineCover.X i
      let p := X.affineCover.f i ≫ f
      obtain ⟨W, q, g, hWaff, hWred, hqlft, hqqc, hget, hgsurj, hgq⟩ :=
        exists_affine_etale_cover_of_isReduced Y p
      have : Flat g := inferInstance
      have hsurj := hgsurj.surj
      have h1 := (hcomes k (X.affineCover.X i) $ X.affineCover.f i ≫ f) W q g hgq hsurj
      have h2 := hetale k Y W p q g hgq hsurj
      exact IsStrongResolution.of_isomorphic k Y p (h2.isomorphic_of_isomorphic h1 $ isomorphic_refl _) $ haff k Y p
    exact ⟨d.smooth_lastStructMap_comp, d.isProper_lastStructMap, d.isIso_lastStructMap_restrict_smoothLocus, d.dense_preimage_smoothLocus,
      d.centersLieOver_smoothLocusComplement, d.isStrictNormalCrossingsDivisor_reducedInverseImage⟩





theorem canonicalAlgorithmRules_isCorrect :
    (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme).ReducesInductivelyOnDimension :=
  (isCorrect_canonicalAlgorithmRules_of_hypotheses strictTransformIsBlowupOfClosedSubscheme
    (divisorReductionHypotheses_canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme)
    principalizationGeometryHypotheses)

noncomputable abbrev principalizationWithRadicalCenters : PrincipalizationAlgorithm :=
  canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme smoothSubschemeIdealIsRadical

theorem embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen A (h : DetachedLocusIsOpenForEmbeddings A) :
    EmbeddedPrincipalizationDiscardedLocusIsOpen A affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth := by
  intro k _ _ Y pY _ _ _ _ i hi
  exact h k Y pY
    (affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth k Y pY) i hi

theorem detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters :
    DetachedLocusIsOpenForEmbeddings principalizationWithRadicalCenters :=
  OpenImmersionRestriction.detachedLocusIsOpenForEmbeddings_canonicalPrincipalization OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment
    strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical

theorem transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters :
    TransitionsAreBlowupsForEmbeddings principalizationWithRadicalCenters :=
  by
    intro k _ _ Y pY _ _ _ _ D
    let S := D.toEmbeddedBlowupSequence principalizationWithRadicalCenters
    let hnoeth : EmbeddedBlowupSequence.AllLevelsNoetherian $ D.toEmbeddedBlowupSequence principalizationWithRadicalCenters := by
      intro i hi
      exact EmbeddedBlowupSequence.isNoetherian_schemeAt (D.toEmbeddedBlowupSequence principalizationWithRadicalCenters) i hi
    intro i hi
    rw [S.totalTower_map_succ i]
    exact isBlowupAlongIdealSheaf_totalTransition_of_coprod_desc S i
      (isBlowupAlongIdealSheaf_coprod_desc_centerOffDetached S i hi ((detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters k Y pY D) i hi) hnoeth)

theorem embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :
    EmbeddedPrincipalizationYieldsBlowups principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
  embeddedPrincipalizationYieldsBlowups_of_discardedLocusIsOpen principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    (embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters)
    (embeddedPrincipalizationAmbientIsNoetherian principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictTransformIsBlowupOfClosedSubscheme

theorem isFunctorialPrincipalization_principalizationWithRadicalCenters : IsFunctorialPrincipalization principalizationWithRadicalCenters :=
  isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
    smoothSubschemeIdealIsRadical
    (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect)

noncomputable def canonicalAffineResolutionRule : AffineResolutionRule :=
  affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters




section
variable {X : Type} [TopologicalSpace X]
theorem dense_of_forall_mem_of_isGenericPoint [QuasiSober X]
    {V} (h : ∀ C ∈ irreducibleComponents X, ∀ et_ : X, IsGenericPoint et_ C → et_ ∈ V) :
    Dense V := by
  intro x
  obtain ⟨et_, het_⟩ := sober (isIrreducible_irreducibleComponent (x := x))
    isClosed_irreducibleComponent
  have hmem := h _ (irreducibleComponent_mem_irreducibleComponents x) et_ het_
  refine closure_mono (mpr_ singleton_subset_iff hmem) ?_
  rw [het_]
  exact mem_irreducibleComponent

theorem mem_of_isGenericPoint_of_isOpen_of_dense
    [NoetherianSpace X] {U} (hUo : IsOpen U) (hUd : Dense U)
    {C} (hC : C ∈ irreducibleComponents X) {et_} (het_ : IsGenericPoint et_ C) :
    et_ ∈ U := by
  obtain ⟨y, hyC, hyU⟩ := nonempty_inter_of_dense_of_mem_irreducibleComponents hUd hC
  have hy : y ∈ closure ({et_} : Set X) := by
    rwa [het_]
  obtain ⟨z, hzU, hz⟩ := mp_ mem_closure_iff hy U hUo hyU
  rw [mem_singleton_iff] at hz
  exact hz ▸ hzU
end

section
variable {X W : Type} [TopologicalSpace X] [TopologicalSpace W] {f : X → W}
theorem isGenericPoint_image_of_isClosed (hf : Continuous f) {C : Set X} {et_ : X} (het_ : IsGenericPoint et_ C)
    (hcl : IsClosed $ f '' C) :
    IsGenericPoint (f et_) $ f '' C := by
  have het' := het_
  have hetC : et_ ∈ C := by
    rw [← het']
    exact subset_closure $ mpr_ mem_singleton_iff rfl
  show closure ({f et_} : Set W) = f '' C
  apply m15
  exact hcl.closure_subset_iff.mpr $ mpr_ singleton_subset_iff ⟨et_, hetC, rfl⟩
  have hcont : f '' closure ({et_} : Set X) ⊆ closure (f '' ({et_} : Set X)) :=
    image_closure_subset_closure_image hf
  rw [image_singleton] at hcont
  rwa [← het']

theorem exists_isGenericPoint_image_of_isClosedEmbedding (hf : IsClosedEmbedding f) {F : Set (Set W)}
    (hF : ∀ Z ∈ F, Z ∈ irreducibleComponents W) (hun : ⋃₀ F = range f)
    {C : Set X} (hC : C ∈ irreducibleComponents X) {et_ : X} (het_ : IsGenericPoint et_ C) :
    ∃ Z ∈ F, IsGenericPoint (f et_) Z := by
  have hmem : f et_ ∈ ⋃₀ F := by simp_all
  obtain ⟨Z, hZF, hZ⟩ := hmem
  refine ⟨Z, hZF, ?_⟩
  have hZcomp := hF Z hZF
  have hZcl := isClosed_of_mem_irreducibleComponents Z hZcomp
  have hZran : Z ⊆ range f := by
    intro w hw
    rw [← hun]
    exact ⟨Z, hZF, hw⟩
  have hsub : C ⊆ preimage f Z := by
    rw [← het_]
    exact (hZcl.preimage hf.continuous).closure_subset_iff.mpr
      (mpr_ singleton_subset_iff hZ)
  have heq := m15 (an2 hC (isIrreducible_preimage_of_isClosedEmbedding hf hZran hZcomp.1) hsub) hsub
  have himg : f '' C = Z := by
    rw [← heq, image_preimage_eq_of_subset hZran]
  have hgen :=
    isGenericPoint_image_of_isClosed hf.continuous het_ (by rw [himg]; exact hZcl)
  rwa [himg] at hgen

theorem exists_isGenericPoint_image_of_isOpenEmbedding (hf : IsOpenEmbedding f)
    {C} (hC : C ∈ irreducibleComponents X) {et_} (het_ : IsGenericPoint et_ C) :
    ∃ D ∈ irreducibleComponents W, IsGenericPoint (f et_) D := by
  let _c0 := ({f et_} : Set W)
  have het' := het_
  have hmax : ∀ E, IsIrreducible E → closure _c0 ⊆ E →
      E ⊆ closure _c0 := by
    intro E hE hsub
    have hfetE := hsub $ subset_closure $ mpr_ mem_singleton_iff rfl
    have hne : (E ∩ range f).Nonempty := ⟨f et_, hfetE, ⟨et_, rfl⟩⟩
    have hpre := hE.2.preimage hf
    have hetpre := hfetE
    let _a0 := closure $ preimage f E
    have hirrcl : IsIrreducible _a0 :=
      ⟨⟨et_, subset_closure hetpre⟩, hpre.closure⟩
    have hCsub : C ⊆ _a0 := by
      rw [← het']
      exact closure_mono $ mpr_ singleton_subset_iff hetpre
    have hback := an2 hC hirrcl hCsub
    have h1 : E ∩ range f ⊆ f '' C := by
      rintro w ⟨hwE, x, rfl⟩
      exact ⟨x, hback $ subset_closure hwE, rfl⟩
    have h2 : f '' C ⊆ closure _c0 := by
      have hcont : f '' closure ({et_} : Set X) ⊆ closure (f '' ({et_} : Set X)) :=
        image_closure_subset_closure_image hf.continuous
      rw [image_singleton] at hcont
      rwa [← het']
    calc E ⊆ closure (E ∩ range f) := subset_closure_inter_of_isPreirreducible_of_isOpen hE.2 hf.isOpen_range hne
      _ ⊆ closure (f '' C) := closure_mono h1
      _ ⊆ closure (closure _c0) := closure_mono h2
      _ = closure _c0 := closure_closure
  exact ⟨closure _c0,
    ⟨isIrreducible_singleton.closure, fun E hE hsub => hmax E hE hsub⟩, rfl⟩
end

section
variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y] {pY} [LocallyOfFiniteType pY]
theorem isOpenImmersion_strictTransformZeroToBase (S : AffineSpacePrincipalizationData k Y pY) :
    IsOpenImmersion S.strictTransformZeroToBase := by
  have h0 : IsIso
      (Limits.coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) :=
    (Limits.coprod.rightUnitor $ S.strictTransform 0).isIso_inv
  have hiso : IsIso S.strictTransformZeroToBase := by
    rw [strictTransformZeroToBase_def]
    infer_instance
  infer_instance

theorem exists_isGenericPoint_strictTransformToZero [IsReduced Y]
    (S : AffineSpacePrincipalizationData k Y pY)
    (hN : ∀ j ≤ S.ambientLength, IsNoetherian $ S.ambientLevel j) n :
    n ≤ S.ambientLength → ∀ (C : Set ↥(S.strictTransform n)),
      C ∈ irreducibleComponents ↥(S.strictTransform n) → ∀ et_ : ↥(S.strictTransform n),
      IsGenericPoint et_ C →
      ∃ D ∈ irreducibleComponents ↥(S.strictTransform 0),
        IsGenericPoint ((S.strictTransformToZero n).base et_) D := by
  induction n with
  | zero =>
    intro _ C hC et_ het_
    exact ⟨C, hC, het_⟩
  | succ m ih =>
    intro hn C hC et_ het_
    have hm := hn
    obtain ⟨C', hC', hgen', -⟩ :=
      exists_irreducibleComponent_isGenericPoint_strictTransformMap S.toEmbeddedBlowupSequence (fun j hj => hN j hj) m hm C hC et_ het_
    obtain ⟨D, hD, hDgen⟩ := ih (le_of_lt hm) C' hC' (bsM (S.strictTransformMap m) et_) hgen'
    exact ⟨D, hD, hDgen⟩
end

theorem affineSmoothLocusPreimageDenseInDetached A (hemb : AffineEmbedsIntoAffineSpace)
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth) :
    AffineSmoothLocusPreimageDenseInDetached A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  have hY := isNoetherian_of_locallyOfFiniteType pY
  apply dense_of_forall_mem_of_isGenericPoint
  intro C hC et_ het_
  let _a1 := ofAffine A hemb hsnc hsm k Y pY
  obtain ⟨Z, hZ, hZgen⟩ :=
    exists_isGenericPoint_image_of_isClosedEmbedding
      (isClosedEmbedding
    (_a1.discardedIdeal i).si)
      (discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i)
      (range_discardedio_eq_sUnion_discardedComponents A hemb hsnc hsm k Y pY i hi).symm hC het_
  have hZc := discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i hZ
  let _a0 := _a1
  obtain ⟨D, hD, hDgen⟩ :=
    exists_isGenericPoint_strictTransformToZero _a0
      (fun j hj =>
        isNoetherian_ambientLevel _a0 j hj)
      i (le_of_lt hi) Z hZc _ hZgen
  have := isOpenImmersion_strictTransformZeroToBase _a0
  obtain ⟨E, hE, hEgen⟩ :=
    exists_isGenericPoint_image_of_isOpenEmbedding
      (isOpenEmbedding
        _a0.strictTransformZeroToBase)
      hD hDgen
  have hdense := pY.dense_smoothLocus_of_perfectField
  have hmem := mem_of_isGenericPoint_of_isOpen_of_dense
    (U := pY.smoothLocus) (pY.smoothLocus).isOpen hdense hE hEgen
  rwa [mem_preimage, detachedToBase_def]





private theorem base_comp_apply {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A) :
    (f ≫ g).base x = g.base (f.base x) := by simp

theorem isIso_stalkMap_of_isOpenImmersion {A B : Sch} (f : A ⟶ B)
    [IsOpenImmersion f] (x : ↥A) :
    IsIso $ stalkMap f x := by
  infer_instance

namespace AffineSpacePrincipalizationData

variable {k : Type} [Field k] [CharZero k] {Y : Sch} [IsAffine Y]
  {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

section
variable {P Q R : CRC} (u : P ⟶ Q) (v : Q ⟶ R)
theorem isIso_comp_of_isIso_commRingCat
    (hu : IsIso u) (hv : IsIso v) :
    IsIso $ u ≫ v :=by simp_all
theorem isIso_of_isIso_comp_right
    (hv : IsIso v) (huv : IsIso $ u ≫ v) :
    IsIso u :=by simp_all
end

section
variable {X X1 : Sch} (pi_ : X1 ⟶ X)
theorem mem_support_strictTransform_of_mem_support_of_notMem_support
    [IsLocallyNoetherian X1] (Z D : ISD X) x
    (hD : pi_.base x ∈ ((support D : Closeds ↥X) : Set ↥X))
    (hZ : pi_.base x ∉ ((support Z : Closeds ↥X) : Set ↥X)) :
    x ∈ ((support (FunctorialResolution.Blowup.strictTransform pi_ Z D) :
      Closeds ↥X1) : Set ↥X1) := by
  rw [support_strictTransform_eq_closure_preimage pi_ Z D]
  exact subset_closure $ Set.mem_preimage.mpr $ mem_sdiff_of_mem hD hZ

theorem strictTransform_comap_io_eq_comap_restrict
    (Z D : ISD X) [NoetherianSpace ↥X1] :
    (FunctorialResolution.Blowup.strictTransform pi_ Z D).comap (Scheme.Opens.ι $ pi_ ⁻¹ᵁ Z.support.compl)
      = (D.comap $ Scheme.Opens.ι Z.support.compl).comap (pi_ ∣_ Z.support.compl) := by
  rw [strictTransform_eq_ker_restrict pi_ Z D]
  exact comap_ker_subschemeio_comp _ _
end

section
variable (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j))
include hN
theorem avoidsCenters_of_forall_notMem_support_boundary :
    ∀ i, i ≤ S.principalizationSequence.length → ∀ x : ↥(S.principalizationSequence.schemeAt i),
      (∀ E ∈ S.principalizationSequence.boundary i,
        x ∉ ((support E : Closeds ↥(S.principalizationSequence.schemeAt i)) :
          CSet (S.principalizationSequence.schemeAt i))) →
      S.toEmbeddedBlowupSequence.AvoidsCenters i x := by
  intro i
  induction i with
  | zero =>
      intro _ x _
      exact S.toEmbeddedBlowupSequence.avoidsCenters_zero x
  | succ i ih =>
      intro hi x hx
      have hbnd := S.principalizationSequence.boundary_succ_eq_map_strictTransform_append i hi
      have hexc : S.principalizationSequence.exceptionalIdeal i ∈ S.principalizationSequence.boundary (i + 1) := by simp_all
      let _a0 := bsM (S.principalizationSequence.transitionMapSucc i) x
      have hnc : _a0 ∉
          ((spI (S.principalizationSequence.center i) :
            Closeds ↥(S.principalizationSequence.schemeAt i)) : CSet $ S.principalizationSequence.schemeAt i) := by
        intro hmem
        refine hx _ hexc ?_
        rw [S.principalizationSequence.exceptionalIdeal_eq i]
        exact Scheme.IdealSheafData.mem_support_comap.mpr hmem
      refine mpr_ (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff i x) ⟨hnc, ?_⟩
      refine ih (le_of_succ_le hi) _a0 ?_
      intro E hE hmem
      refine hx (p6 (S.principalizationSequence.transitionMapSucc i) (S.principalizationSequence.center i) E)
        ?_ ?_
      rw [hbnd]
      exact List.mem_append.mpr $ m51 $ mpr_ mem_map ⟨E, hE, rfl⟩
      exact @_root_.FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.mem_support_strictTransform_of_mem_support_of_notMem_support (S.principalizationSequence.schemeAt i) (S.principalizationSequence.schemeAt $ i + 1)
        (S.principalizationSequence.transitionMapSucc i) ((hN (i + 1) hi).toIsLocallyNoetherian) (S.principalizationSequence.center i) E x hmem hnc

theorem avoidsCenters_of_forall_notMem_boundary
    (i : ℕ) (hi : i ≤ S.ambientLength) (x : ↥(S.ambientLevel i))
    (hx : ∀ E ∈ boundary S i, x ∉ ((support E : Closeds ↥(S.ambientLevel i)) :
      Set ↥(S.ambientLevel i))) :
    S.toEmbeddedBlowupSequence.AvoidsCenters i x :=
  avoidsCenters_of_forall_notMem_support_boundary S hN i hi x hx
end

theorem base_apply_mem_support_ker {W Z : Sch} (g : W ⟶ Z) (q : ↥W) :
    g.base q ∈ (support (ker g) : Set ↥Z) := by
  rw [← range_subschemeι]
  exact ⟨bsM (lift (ker g).si g $ le_of_eq $ ker_subschemeι _) q, by
    rw [← base_comp_apply, lift_fac _ _ _]⟩

theorem mem_support_centerOffDetached_of_mem_support_ambientCenter (i : ℕ) (p : ↥(S.strictTransform i))
    (hp : p ∈ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)))
    (hmem : (strictTransformio S i).base p ∈ (support (S.ambientCenter i) : Set ↥(S.ambientLevel i))) :
    p ∈ ((support (S.centerOffDetached i) : Closeds ↥(S.strictTransform i)) :
      Set ↥(S.strictTransform i)) := by
  have htrace : p ∈ (spI (S.comapAmbientCenter i) : Set ↥(S.strictTransform i)) := by
    rw [S.comapAmbientCenter_eq i]
    exact Scheme.IdealSheafData.mem_support_comap.mpr hmem
  let _a0 := cmI (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i
  let _a1 := S.discardedLocusClosureCompl i
  have hq0 : (⟨p, hp⟩ : ↥_a1) ∈
      ((spI _a0 :
        Closeds ↥_a1.toScheme) :
        Set ↥_a1.toScheme) :=
    Scheme.IdealSheafData.mem_support_comap.mpr htrace
  rw [← range_subschemeι] at hq0
  obtain ⟨q, hq⟩ := hq0
  have hmain := base_apply_mem_support_ker
    (siI _a0 ≫ opI _a1) q
  rw [base_comp_apply, hq] at hmain
  rwa [S.centerOffDetached_eq i]

theorem forall_mem_smoothLocusComplement_of_not_avoidsCenters
    (hN : ∀ j ≤ S.ambientLength, IsNoetherian $ S.ambientLevel j)
    (hopen : ∀ j < S.ambientLength, IsOpen $ S.discardedLocus j)
    (hcent : S.CentersLieOverSingularLocus) :
    ∀ i, i ≤ S.ambientLength → ∀ p : ↥(S.strictTransform i),
      ¬ S.toEmbeddedBlowupSequence.AvoidsCenters i ((strictTransformio S i).base p) →
      (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p ∈
        ((smoothLocusComplement pY : Closeds ↥Y) : Set ↥Y) := by
  have hNl : ∀ m, m ≤ S.ambientLength → NoetherianSpace ↥(S.ambientLevel m) := by
    intro m hm
    have := hN m hm
    infer_instance
  intro i
  induction i with
  | zero =>
      intro _ p hp
      exact absurd (S.toEmbeddedBlowupSequence.avoidsCenters_zero _) hp
  | succ j ih =>
      intro hj p hp
      have hjlt := lt_of_succ_le hj
      have hjle := m49 hjlt
      have hnj := hNl j hjle
      have hNl' := hNl (j + 1) hj
      let _a0 := bsM (S.ambientBlowupMorphism j) $ bsM (strictTransformio S $ j + 1) p
      have key : bsM (strictTransformio S j) (bsM (S.strictTransformMap j) p)
          = _a0 := by
        have h : bsM (S.strictTransformMap j ≫ strictTransformio S j) p
            = bsM (strictTransformio S (j + 1) ≫ S.ambientBlowupMorphism j) p := by
          rw [S.strictTransformMap_comp_strictTransformio j]
        simpa using h
      have hdown : bsM (S.strictTransformToZero (j + 1) ≫ S.strictTransformZeroToBase) p
          = bsM (S.strictTransformToZero j ≫ S.strictTransformZeroToBase) (bsM (S.strictTransformMap j) p) := by
        simp
      rw [hdown]
      by_cases hc : _a0 ∈
          (spI (S.ambientCenter j) : Set ↥(S.ambientLevel j))
      have hfc :=
        S.range_strictTransformMap_subset_discardedLocusClosureCompl j hjlt (S.noetherianSpace_strictTransform j) hNl' (hopen j hjlt) ⟨p, rfl⟩
      have hmem := hc
      rw [← key] at hmem
      exact hcent j hjlt (bsM (S.strictTransformMap j) p)
        (S.mem_support_centerOffDetached_of_mem_support_ambientCenter j (bsM (S.strictTransformMap j) p)
          hfc hmem)
      refine ih hjle (bsM (S.strictTransformMap j) p) ?_
      intro hcl
      have hcl' := hcl
      rw [key] at hcl'
      exact hp $ mpr_ (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff j $ bsM (strictTransformio S $ j + 1) p) ⟨hc, hcl'⟩

theorem isIso_stalkMap_of_isIso_stalkMap_comp {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A)
    (hf : IsIso $ stalkMap f x)
    (hfg : IsIso $ stalkMap (f ≫ g) x) :
    IsIso $ stalkMap g $ f.base x := by
  rw [stalkMap_comp] at hfg
  exact isIso_of_isIso_comp_right _ _ hf hfg

theorem idealSheafData_comap_injective_of_isIso {A B : Sch} (ph_ : A ⟶ B)
    [IsIso ph_] (I J : ISD B)
    (h : I.comap ph_ = J.comap ph_) : I = J := by
  have h2 : (I.comap ph_).comap (m83 ph_)
      = (J.comap ph_).comap (m83 ph_) := by rw [h]
  rwa [← comap_comp,
    ← comap_comp,
    m117,
    comap_id,
    comap_id] at h2

theorem isOpenImmersion_preimage_io_comp_of_ker_comap_eq {X X1 A0_ A1_ : Sch} (pi_ : X1 ⟶ X)
    (io0 : A0_ ⟶ X) (io1 : A1_ ⟶ X1) (m : A1_ ⟶ A0_) (V : Opn X)
    [IsClosedImmersion io0] [IsClosedImmersion io1]
    [IsIso (pi_ ∣_ V)]
    (hm : m ≫ io0 = io1 ≫ pi_)
    (hker : (ker io1).comap (Scheme.Opens.ι (pi_ ⁻¹ᵁ V))
      = ((ker io0).comap (Scheme.Opens.ι V)).comap (pi_ ∣_ V)) :
    IsOpenImmersion (Scheme.Opens.ι (io1 ⁻¹ᵁ (pi_ ⁻¹ᵁ V)) ≫ m) := by
  let _c0 := preU io1 $ preU pi_ V
  have hcial : IsClosedImmersion $ (mrU io1 $ preU pi_ V) ≫ mrU pi_ V :=
    inferInstance
  have hk1 := FunctorialResolution.EmbeddedResolution.ker_comap_io_eq_ker_morphismRestrict io1 $ preU pi_ V
  have hk0 := FunctorialResolution.EmbeddedResolution.ker_comap_io_eq_ker_morphismRestrict io0 V
  have hcomp := comap_ker_comp_of_isOpenImmersion (mrU io1 $ preU pi_ V) $ mrU pi_ V
  have hkereq : ker ((mrU io1 $ preU pi_ V) ≫ mrU pi_ V)
      = ker (mrU io0 V) := by
    refine idealSheafData_comap_injective_of_isIso (mrU pi_ V) _ _ ?_
    rw [hcomp, ← hk1, hker, hk0]
  have hle := le_of_eq hkereq.symm
  have hfac := lift_fac (mrU io0 V)
    ((mrU io1 $ preU pi_ V) ≫ mrU pi_ V) hle
  have hIso :=
    isIso_of_ker_eq _ _ _ hfac hkereq
  let _a0 := p4 $ preU io0 V
  let _a1 := (p4 _c0 ≫ m) ≫ io0
  have hmono : _a1
      = ((lift (mrU io0 V)
          ((mrU io1 $ preU pi_ V) ≫ mrU pi_ V) hle) ≫ _a0) ≫ io0 := by
    let _a2 := p4 $ preU pi_ V
    calc _a1
        = p4 _c0 ≫ (m ≫ io0) := assoc _ _ _
      _ = p4 _c0 ≫ (io1 ≫ pi_) := by rw [hm]
      _ = (p4 _c0 ≫ io1) ≫ pi_ :=
          symm $ assoc _ _ _
      _ = ((mrU io1 $ preU pi_ V) ≫ _a2) ≫ pi_ := by
          rw [morphismRestrict_ι]
      _ = (mrU io1 $ preU pi_ V) ≫ (_a2 ≫ pi_) :=
          assoc _ _ _
      _ = (mrU io1 $ preU pi_ V) ≫ ((mrU pi_ V) ≫ p4 V) := by
          rw [morphismRestrict_ι]
      _ = ((mrU io1 $ preU pi_ V) ≫ mrU pi_ V) ≫ p4 V :=
          symm $ assoc _ _ _
      _ = ((lift (mrU io0 V)
            ((mrU io1 $ preU pi_ V) ≫ mrU pi_ V) hle) ≫ mrU io0 V) ≫ p4 V := by
          rw [hfac]
      _ = (lift (mrU io0 V)
            ((mrU io1 $ preU pi_ V) ≫ mrU pi_ V) hle) ≫ ((mrU io0 V) ≫ p4 V) :=
          assoc _ _ _
      _ = (lift (mrU io0 V)
            ((mrU io1 $ preU pi_ V) ≫ mrU pi_ V) hle) ≫ (_a0 ≫ io0) := by
          rw [morphismRestrict_ι]
      _ = ((lift (mrU io0 V)
            ((mrU io1 $ preU pi_ V) ≫ mrU pi_ V) hle) ≫ _a0) ≫ io0 :=
          symm $ assoc _ _ _
  have hfin := mp_ (CategoryTheory.cancel_mono io0) hmono
  rw [hfin]
  infer_instance

private theorem strictTransformToZero_comp_schemeAtToSpec (i : ℕ) :
    S.strictTransformToZero i ≫ strictTransformio S 0 ≫ S.schemeAtToSpec 0 = strictTransformio S i ≫ S.schemeAtToSpec i := by
  induction i with
  | zero => rw [strictTransformToZero_zero, id_comp]
  | succ j ih =>
      have _i25 : S.ambientBlowupMorphism j ≫ S.schemeAtToSpec j = S.schemeAtToSpec (j + 1) := by
        have h := projectionToBase_succ S.ambientBlowups j
        rw [schemeAtToSpec_def, schemeAtToSpec_def, h,
          assoc]
      rw [strictTransformToZero_succ, assoc, ih,
        ← assoc, S.strictTransformMap_comp_strictTransformio j, assoc,
        _i25]

theorem isIso_stalkMap_strictTransformToZero_of_avoidsCenters
    (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j)) (j : ℕ) :
    j ≤ S.ambientLength → ∀ a : ↥(S.strictTransform j),
      S.toEmbeddedBlowupSequence.AvoidsCenters j ((strictTransformio S j).base a) →
      IsIso (stalkMap (S.strictTransformToZero j) a) := by
  induction j with
  | zero =>
      intro _ a _
      rw [strictTransformToZero_zero]
      exact isIso_stalkMap_of_isOpenImmersion
        (m74 (S.strictTransform 0)) a
  | succ j ih =>
      intro hj a ha
      have hjlt := lt_of_succ_le hj
      have hNoe := hN (j + 1) hj
      have hNs : NoetherianSpace ↥(S.ambientLevel (j + 1)) := inferInstance
      let _m0 := strictTransformio S $ j + 1
      obtain ⟨hnc, hcl⟩ := mp_ (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff j (bsM _m0 a)) ha
      have haO := hnc
      let _a0 := suppC (S.ambientCenter j)
      have hiso : IsIso
          (S.ambientBlowupMorphism j ∣_ _a0) :=
        S.toEmbeddedBlowupSequence.isIso_blowdown_restrict_ambientCenterSupportCompl j hjlt
      have hker : cmI (ker _m0)
            (p4 (S.ambientBlowupMorphism j ⁻¹ᵁ (suppC (S.ambientCenter j))))
          = cmI (cmI (ker (strictTransformio S j))
              (p4 _a0))
              (S.ambientBlowupMorphism j ∣_ _a0) := by
        rw [ker_subschemeι,
          ker_subschemeι, S.strictTransformIdeal_succ j]
        exact strictTransform_comap_io_eq_comap_restrict (S.ambientBlowupMorphism j) (S.ambientCenter j) $ S.strictTransformIdeal j
      have hoi :=
        isOpenImmersion_preimage_io_comp_of_ker_comap_eq (S.ambientBlowupMorphism j) (strictTransformio S j) _m0
          (S.strictTransformMap j) _a0 (S.strictTransformMap_comp_strictTransformio j) hker
      have h2 :=
        isIso_stalkMap_of_isIso_stalkMap_comp
          (p4 (strictTransformio S (j + 1) ⁻¹ᵁ
            (S.ambientBlowupMorphism j ⁻¹ᵁ (suppC (S.ambientCenter j))))) (S.strictTransformMap j)
          ⟨a, haO⟩ (isIso_stalkMap_of_isOpenImmersion _ _) (isIso_stalkMap_of_isOpenImmersion _ _)
      let _a1 := bsM (S.strictTransformMap j) a
      let _a2 := bsM (strictTransformio S j) _a1
      have hb : _a2
          = bsM (S.ambientBlowupMorphism j) (bsM _m0 a) := by
        have h := congrArg (fun f : S.strictTransform (j + 1) ⟶ S.ambientLevel j => bsM f a)
          (S.strictTransformMap_comp_strictTransformio j)
        simpa using h
      have hclj : S.toEmbeddedBlowupSequence.AvoidsCenters j _a2 := by
        rwa [hb]
      have hih := ih (le_of_succ_le hj) _a1 hclj
      rw [strictTransformToZero_succ, stalkMap_comp]
      exact isIso_comp_of_isIso_commRingCat _ _ hih h2

theorem formallySmooth_of_isIso {A B : CRC} (ps_ : A ⟶ B)
    [IsIso ps_] : (CommRingCat.Hom.hom ps_).FormallySmooth := by
  exact RingHom.FormallySmooth.of_bijective $ m189 ps_

theorem formallySmooth_of_formallySmooth_comp_isIso {R A B : CRC} (ph_ : R ⟶ A) (ps_ : A ⟶ B)
    [IsIso ps_]
    (h : (CommRingCat.Hom.hom $ ph_ ≫ ps_).FormallySmooth) :
    (CommRingCat.Hom.hom ph_).FormallySmooth := by
  have h1 : (ph_ ≫ ps_) ≫ m83 ps_ = ph_ := by simp_all
  rw [← h1, hom_comp]
  exact RingHom.FormallySmooth.comp h $ formallySmooth_of_isIso $ m83 ps_

section
variable [IsReduced Y] (hN : ∀ j ≤ S.ambientLength, IsNoetherian (S.ambientLevel j)) (hopen : ∀ j < S.ambientLength, IsOpen (S.discardedLocus j))
include hN hopen
theorem mem_smoothLocusComplement_of_not_avoidsCenters
    (hcent : S.CentersLieOverSingularLocus)
    (i : ℕ) (hi : i ≤ S.ambientLength) (p : ↥(S.strictTransform i))
    (hp : ¬ S.toEmbeddedBlowupSequence.AvoidsCenters i ((strictTransformio S i).base p)) :
    (S.strictTransformToZero i ≫ S.strictTransformZeroToBase).base p ∈
      ((smoothLocusComplement pY : Closeds ↥Y) : Set ↥Y) :=
  forall_mem_smoothLocusComplement_of_not_avoidsCenters S hN hopen hcent i hi p hp

section
variable (hsmooth : S.DetachedSmooth) (i : ℕ) (hi : i < S.ambientLength) (q : ↥(S.discardedSubscheme i))
include hsmooth hi
theorem notMem_smoothLocusComplement_detachedToBase_of_notMem_boundary
    (hq : ∀ E ∈ boundary S i,
      (strictTransformio S i).base ((S.discardedio i).base q) ∉
        ((E.support : Closeds ↥(S.ambientLevel i)) : Set ↥(S.ambientLevel i))) :
    (S.detachedToBase i).base q ∉
      ((smoothLocusComplement pY : Closeds ↥Y) : Set ↥Y) := by
  let _a1 := bsM (S.discardedio i) q
  have hclear :=
    avoidsCenters_of_forall_notMem_boundary S hN i (le_of_lt hi)
      (bsM (strictTransformio S i) _a1) hq
  intro hmem
  have hred :=
    S.isReduced_strictTransform hN i $ le_of_lt hi
  have hnl : NoetherianSpace ↥(S.ambientLevel i) := by
    have := hN i $ le_of_lt hi
    infer_instance
  have hna :=
    S.noetherianSpace_strictTransform i
  obtain ⟨e, he⟩ := S.exists_iso_discardedSubscheme_discardedLocusOpens i hna $ hopen i hi
  have hfi : IsOpenImmersion $ S.discardedio i := by
    rw [← he]
    infer_instance
  have hab :=
    FunctorialResolution.EmbeddedResolution.isOpenImmersion_strictTransformZeroToBase S
  let _a0 := _a1
  have hchain := isIso_stalkMap_strictTransformToZero_of_avoidsCenters S hN i (le_of_lt hi) _a0 hclear
  have hsm := hsmooth i hi
  have _i26 : S.detachedToBase i ≫ pY = S.discardedio i ≫ strictTransformio S i ≫ S.schemeAtToSpec i := by
    rw [detachedToBase_def, assoc,
      assoc, strictTransformZeroToBase_comp,
      ← strictTransformToZero_comp_schemeAtToSpec S i]
  rw [← _i26] at hsm
  have hstq : IsIso
      (stalkMap (S.detachedToBase i) q) := by
    have h1 : IsIso $ stalkMap S.strictTransformZeroToBase
        (bsM (S.strictTransformToZero i) _a0) := isIso_stalkMap_of_isOpenImmersion _ _
    have h2 : IsIso
        (stalkMap (S.discardedio i) q) :=
      isIso_stalkMap_of_isOpenImmersion _ _
    rw [detachedToBase_def, stalkMap_comp,
      stalkMap_comp]
    exact isIso_comp_of_isIso_commRingCat _ _ (isIso_comp_of_isIso_commRingCat _ _ h1 hchain) h2
  have htop :=
    smoothLocus_eq_top_iff.mpr hsm
  have hmemq : q ∈ (S.detachedToBase i ≫ pY).smoothLocus := by simp_all
  have hfs := mp_ mem_smoothLocus hmemq
  rw [stalkMap_comp] at hfs
  have hfs2 :=
    formallySmooth_of_formallySmooth_comp_isIso _ _ hfs
  have hin :=
    mem_smoothLocus.mpr hfs2
  exact hmem hin
end
end

end AffineSpacePrincipalizationData

theorem principalizationSequence_not_avoidsCenters_of_mem_boundary {k : Type} [Field k] [CharZero k]
    {Y} [IsAffine Y] {pY}
    [LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    ∀ i, i ≤ S.principalizationSequence.length →
      ∀ E : IdealSheafData $ S.principalizationSequence.schemeAt i, E ∈ S.principalizationSequence.boundary i →
        ∀ x : ↥(S.principalizationSequence.schemeAt i), x ∈ (support E : CSet $ S.principalizationSequence.schemeAt i) →
          ¬ S.toEmbeddedBlowupSequence.AvoidsCenters i x := by
  intro i
  induction i with
  | zero =>
      intro _ E hE x _ _
      rw [S.principalizationSequence.boundary_zero] at hE
      simp at hE
  | succ i ih =>
      intro hi E hE x hx hcl
      rw [S.principalizationSequence.boundary_succ_eq_map_strictTransform_append i hi, mem_append] at hE
      have hcl' := mp_ (S.toEmbeddedBlowupSequence.avoidsCenters_succ_iff i x) hcl
      rcases hE with hE | hE
      obtain ⟨E', hE', rfl⟩ := mp_ mem_map hE
      exact ih (le_of_succ_le hi) E' hE' _ (OpenImmersionRestriction.mem_support_of_mem_support_comap (S.principalizationSequence.transitionMapSucc i) E' x $ support_antitone (comap_le_strictTransform (S.principalizationSequence.transitionMapSucc i) (S.principalizationSequence.center i) E') hx) hcl'.2
      rw [mem_singleton] at hE
      subst hE
      rw [S.principalizationSequence.exceptionalIdeal_eq i] at hx
      exact an1 hcl' $ OpenImmersionRestriction.mem_support_of_mem_support_comap (S.principalizationSequence.transitionMapSucc i) (S.principalizationSequence.center i) x hx

section
variable (A : PrincipalizationAlgorithm) (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
section
variable (k : Type) [Field k] [CharZero k] (Y) [IsAffine Y]

section
variable [IsReduced Y] (pY) [LocallyOfFiniteType pY] [QuasiCompact pY] (hopen : ∀ j < (ofAffine A hemb hsnc hsm k Y pY).ambientLength, IsOpen ((ofAffine A hemb hsnc hsm k Y pY).discardedLocus j))
include hopen
theorem detachedSingularPreimageEqBoundary_ofAffine
    (hsmooth : (ofAffine A hemb hsnc hsm k Y pY).DetachedSmooth)
    (hcent : (ofAffine A hemb hsnc hsm k Y pY).CentersLieOverSingularLocus) :
    (ofAffine A hemb hsnc hsm k Y pY).DetachedSingularPreimageEqBoundary := by
  let _a3 := isNoetherian_ambientLevel_ofAffine A hemb hsnc hsm k Y pY
  let _c0 := ofAffine A hemb hsnc hsm k Y pY
  intro i hi
  let _a2 := ofAffine A hemb hsnc hsm k Y pY
  have _i28 : ⇑(_a2.discardedio i ≫ _a2.strictTransformio i).base ⁻¹' (⋃ E ∈ _a2.boundary i, ((spI E : Closeds ↥(_a2.ambientLevel i)) : Set ↥(_a2.ambientLevel i))) ⊆ ⇑(_a2.detachedToBase i).base ⁻¹' ((smoothLocusComplement pY) : Set ↥Y) := by
    let _c0 := ofAffine A hemb hsnc hsm k Y pY
    intro q hq
    have hq' := hq
    obtain ⟨E, hE, hmem⟩ := Set.mem_iUnion₂.mp hq'
    let _a0 := bsM (_c0.discardedio i) q
    rw [base_comp_apply _ _ q] at hmem
    have hnc := (fun A hemb hsnc hsm k [Field k] [CharZero k] Y [IsAffine Y] pY [LocallyOfFiniteType pY] i hi E hE x hx => principalizationSequence_not_avoidsCenters_of_mem_boundary (ofAffine A hemb hsnc hsm k Y pY) i hi E hE
    x hx) A hemb hsnc hsm k Y pY i (le_of_lt hi) E hE
      (bsM (_c0.strictTransformio i) _a0) hmem
    have hsing := _c0.mem_smoothLocusComplement_of_not_avoidsCenters
      _a3 hopen hcent i (le_of_lt hi)
      _a0 hnc
    show bsM (_c0.detachedToBase i) q ∈
      ((smoothLocusComplement pY) : Set ↥Y)
    rwa [AffineSpacePrincipalizationData.detachedToBase_def, base_comp_apply]
  refine m15 ?_
    _i28
  intro q hq
  by_contra hcon
  refine _c0.notMem_smoothLocusComplement_detachedToBase_of_notMem_boundary
    _a3 hopen hsmooth i hi q ?_ hq
  intro E hE hmem
  refine hcon ?_
  have hb := base_comp_apply
    (_c0.discardedio i)
    (_c0.strictTransformio i) q
  simp only [mem_preimage]
  exact Set.mem_iUnion₂.mpr ⟨E, hE, hmem⟩
end
end

theorem affineDetachedSingularPreimageEqBoundary_of_centersLieOverSing
    (hiso : EmbeddedPrincipalizationDiscardedLocusIsOpen A hemb hsnc hsm)
    (hsmooth : AffineDetachedSmooth A hemb hsnc hsm)
    (hPrincipalization : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm)
    (hcent : AffineCentersLieOverSingularLocus A hemb hsnc hsm hPrincipalization) :
    AffineDetachedSingularPreimageEqBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact detachedSingularPreimageEqBoundary_ofAffine A hemb hsnc hsm k Y pY (hiso k Y pY)
    (hsmooth k Y pY) $ centersLieOverSingularLocus_of_inducedCentersLieOverSingularLocus (ofAffine A hemb hsnc hsm k Y pY) (hPrincipalization k Y pY) $ hcent k Y pY
end

end FunctorialResolution.EmbeddedResolution

end
end
noncomputable section
open CommRingCat.Hom (hom)
open FunctorialResolution.EmbeddedResolution (NonzeroOnComponents PrincipalizationCertificate exists_iso_of_range_base_eq isGenericPoint_image_of_isClosedEmbedding ker_eq_comap_ker_of_isPullback_of_flat quasiCompact_of_isPullback range_base_subschemeio)
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence (isOpenImmersion_io_comp_blowdown isReduced_strictTransform_of_isNoetherian mem_image_strictTransformio_iff_of_notMem_ambientCenter mem_image_strictTransformio_of_mem_image_succ range_strictTransformio_succ schemeAtToSpec_eq strictTransformToSpec_eq strictTransformio_eq_subschemeio)
open IsClosedImmersion (isClosedEmbedding of_comp)
open RingHom.FormallySmooth (comp of_bijective)
open Scheme.Hom (app ker range_comp_base smoothLocus smoothLocus_eq_top_iff stalkMap stalkMap_comp)
open TopologicalSpace.Opens (map)
section


namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

section
variable (k : Type) [Field k] [CharZero k] (Y) [IsAffine Y] (pY) [LocallyOfFiniteType pY] [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm) (t : ℕ)
def chartLevelStructureMorphism :
    (principalizationOfEmbedding k Y pY D A).schemeAt t ⟶ Sp k :=
  (principalizationOfEmbedding k Y pY D A).structureMorphism t

theorem chartLevelStructureMorphism_eq_structureMorphism :
    chartLevelStructureMorphism k Y pY D A t = (principalizationOfEmbedding k Y pY D A).structureMorphism t :=
  rfl
end

theorem subset_detachedLocus_of_mem_detachedComponents {k : Type} [Field k] [CharZero k]
    {Y : Sch} [IsAffine Y] {pY : Y ⟶ Sp k}
    [LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY) (t : ℕ)
    {C : Set ↥(S.strictTransform t)} (hC : C ∈ S.detachedComponents t) :
    C ⊆ S.detachedLocus t := by
  rw [EmbeddedBlowupSequence.detachedLocus_eq_sUnion]
  exact Set.subset_sUnion_of_mem hC

theorem exists_iso_of_ker_eq {X X' W : Sch} (f : X ⟶ W) (g : X' ⟶ W)
    [IsClosedImmersion f] [IsClosedImmersion g]
    (h : ker f = ker g) :
    ∃ e : X ≅ X', e.hom ≫ g = f := by
  have hgf :=
    le_of_eq h
  have hfg :=
    le_of_eq h.symm
  obtain ⟨ps_, hpsg⟩ : ∃ ps_, ps_ ≫ g = f :=
    ⟨lift g f hfg,
      lift_fac g f hfg⟩
  obtain ⟨ph_, hphf⟩ : ∃ ph_, ph_ ≫ f = g :=
    ⟨lift f g hgf,
      lift_fac f g hgf⟩
  have : CategoryTheory.Mono f := inferInstance
  have : CategoryTheory.Mono g := inferInstance
  have h1 : ps_ ≫ ph_ = 𝟙 X := by
    apply (CategoryTheory.cancel_mono f).1
    rw [assoc, hphf, hpsg, id_comp]
  refine ⟨⟨ps_, ph_, h1, ?_⟩, hpsg⟩
  apply (CategoryTheory.cancel_mono g).1
  rw [assoc, hpsg, hphf, id_comp]

theorem ker_eq_comap_ker_of_isPullback_isOpenImmersion {X1 Y1 U V : Sch}
    (f : X1 ⟶ Y1) [QuasiCompact f] (g : V ⟶ Y1)
    [IsOpenImmersion g] (f' : U ⟶ V) (g' : U ⟶ X1)
    (H : CategoryTheory.IsPullback g' f' f g) :
    ker f' =
      (ker f).comap g := by
  have := quasiCompact_of_isPullback H
  exact ker_eq_comap_ker_of_isPullback_of_flat H

private theorem smooth_of_smooth_iso_hom_comp {X X' Sc : Sch} (e : X ≅ X') (g : X' ⟶ Sc)
    (h : Smooth $ e.hom ≫ g) : Smooth g := by
  have hg : Smooth $ isoI e ≫ (isoH e ≫ g) := inferInstance
  rwa [← assoc, e.inv_hom_id, id_comp] at hg

theorem smooth_comp_of_iso_hom_eq {A B V W Sc : Sch} (e : A ≅ B)
    (io0 : A ⟶ V) (a : V ⟶ W) (g : B ⟶ W) (q : W ⟶ Sc)
    (he : e.hom ≫ g = io0 ≫ a)
    (h : Smooth $ io0 ≫ a ≫ q) :
    Smooth $ g ≫ q := by
  refine smooth_of_smooth_iso_hom_comp e (g ≫ q) ?_
  rwa [← assoc, he, assoc]

theorem radical_ker_eq_ker {W Z : Sch} [IsReduced W]
    (f : W ⟶ Z) :
    (ker f).radical = ker f := by
  refine le_antisymm ?_ $ le_radical _
  show (ker f).radical ≤
    ofIdeals
      (fun U : affO Z =>
        m41 $ hom $ app f U.1)
  rw [le_ofIdeals_iff]
  intro U
  exact le_trans (Ideal.radical_mono $ ideal_ofIdeals_le _ U) $ Ideal.isRadical_bot.comap _

section
variable {k : Type} [Field k]
theorem nonzeroOnComponents_ideal {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {E : Bdy X}
    (s : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence p I E) (hI : NonzeroOnComponents I) :
    ∀ i : ℕ, i ≤ s.toSequenceOfBlowups.length → NonzeroOnComponents (s.ideal i) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [s.ideal_zero, projectionToBase_zero]
    exact nonzeroOnComponents_comap_iso_hom s.toSequenceOfBlowups.isoZero I hI
  | succ i ih =>
    intro hi
    have hi' := hi
    refine nonzeroOnComponents_of_pow_mul_eq_comap effectiveCartierSupportContainsNoComponent
      (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)
      (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi') 1 (s.ideal i) (s.ideal $ i + 1) ?_
      (ih (le_of_succ_le hi))
    have h2 := s.ideal_succ i hi'
    rw [exceptionalIdeal_eq_comap] at h2
    rwa [pow_one]

section
variable [CharZero k]
theorem false_of_mem_support_center {W : Sch}
    (p : W ⟶ Sp k) (hp : Smooth p)
    (I Z : ISD W) (Mem : Set ↥W)
    (hcert : PrincipalizationCertificate W p I 1 Mem Z)
    (T : Set ↥W) (hTcl : IsClosed T) (hTirr : IsIrreducible T)
    (xi_ x : ↥W) (hxi_ : IsGenericPoint xi_ T) (hx : x ∈ T)
    (hsmT : Smooth
      ((vanishingIdeal
        (⟨T, hTcl⟩ : Closeds ↥W)).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ T)
    (hxi : xi_ ∉ (support Z : Set ↥W))
    (hdisj : Disjoint T Mem)
    (hagree : ∀ z ∈ T, AgreeNear I
      (vanishingIdeal (⟨T, hTcl⟩ : Closeds ↥W)) z)
    (hpt : x ∈ (support Z : Set ↥W)) : False := by
  have hIso := smoothOrderOneCentersIsolated_vanishingIdealAssignment_of_principalizationCertificate
    (hcert.comap_of_isOpenImmersion (⊤ : Opn W).i)
  refine false_of_smoothOrderOneCentersIsolated_opens idealSheafGeometryHypotheses_vanishingIdealAssignment smoothVanishingHypotheses_vanishingIdealAssignment p I Z 1 Mem
    ⟨T, xi_, x, hTcl, hTirr, hxi_, hx⟩ ⊤ ?_ hIso hp rfl ?_ hcomp hxi hdisj ?_ hpt
  simp
  rwa [vanishingIdealAssignment_apply]
  intro z hz
  rw [vanishingIdealAssignment_apply]
  exact hagree z hz

section
variable {Y} [IsAffine Y] [IsReduced Y] {pY} [LocallyOfFiniteType pY]
section
variable (S : EmbeddedBlowupSequence k Y pY)
theorem smooth_strictTransformio_comp_schemeAtToSpec_succ
    (hN : ∀ j ≤ S.length, IsNoetherian $ S.schemeAt j)
    (i : ℕ) (hi' : i < S.length)
    (ih' : Smooth $ S.strictTransformio i ≫ S.schemeAtToSpec i)
    (hcl : ∀ y : ↥(S.strictTransform $ i + 1),
      (S.blowdown i).base ((S.strictTransformio $ i + 1).base y) ∉
        ((S.ambientCenter i).support : CSet $ S.schemeAt i)) :
    Smooth $ S.strictTransformio (i + 1) ≫ S.schemeAtToSpec (i + 1) := by
  let _a4 := (S.strictTransformIdeal i).support
  have hredi :=
    isReduced_strictTransform_of_isNoetherian S hN i $ m49 hi'
  let _a5 := S.schemeAt $ i + 1
  have hredi1 :=
    isReduced_strictTransform_of_isNoetherian S hN (i + 1) hi'
  set U : Opn _a5 :=
    (map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) with _hU
  let _a3 := S.schemeAt i
  have hUsub : (U : Set ↥_a5) ⊆
      ⇑(S.blowdown i).base ⁻¹'
        ((S.ambientCenterSupportCompl i : Opn _a3) : Set ↥_a3) := fun _ hx => hx
  have hgi :=
    isOpenImmersion_io_comp_blowdown S i hi' U hUsub
  have hrangeA : range ⇑(S.strictTransformio $ i + 1).base ⊆ range ⇑U.ib := by
    rw [q1]
    rintro z ⟨y, rfl⟩
    exact mpr_ (S.mem_ambientCenterSupportCompl i _) $ hcl y
  set j := m43 U.i (S.strictTransformio $ i + 1) hrangeA with _hjdef
  have hj : j ≫ U.i = S.strictTransformio (i + 1) :=
    m115 _ _ _
  have hjc : IsClosedImmersion $ j ≫ U.i := by
    rw [hj]
    infer_instance
  have :=
    of_comp j U.i
  have hbase : ∀ y,
      U.ib (bsM j y) = bsM (S.strictTransformio $ i + 1) y := by
    intro y
    rw [show U.ib (bsM j y) = bsM (j ≫ U.i) y from rfl, hj]
  have hkeymap : ∀ y,
      (S.blowdown i).base (bsM (S.strictTransformio $ i + 1) y)
        = bsM (S.strictTransformio i) (bsM (S.strictTransformMap i) y) := by
    intro y
    have h : bsM (S.strictTransformMap i ≫ S.strictTransformio i) y
        = bsM (S.strictTransformio (i + 1) ≫ S.blowdown i) y := by
      rw [S.strictTransformMap_comp_strictTransformio i]
    exact sy_ h
  set pre : Set ↥(U.toScheme) := ⇑(U.i ≫ S.blowdown i).base ⁻¹'
      (_a4 :
        Set ↥_a3) with hpre
  have hsuppcl : IsClosed pre := by
    rw [hpre]
    exact _a4.2.preimage
      (U.i ≫ S.blowdown i).base.hom.continuous
  have hker_eq : S.strictTransformIdeal i = ker (S.strictTransformio i) := by
    rw [strictTransformio_eq_subschemeio, q2]
  have h1 : vanishingIdeal
      _a4 = S.strictTransformIdeal i := by
    rw [vanishingIdeal_support, hker_eq]
    exact radical_ker_eq_ker $ S.strictTransformio i
  have hKvan : (S.strictTransformIdeal i).comap (U.i ≫ S.blowdown i)
      = vanishingIdeal
          (⟨pre, hsuppcl⟩ : Closeds ↥(U.toScheme)) := by
    calc (S.strictTransformIdeal i).comap (U.i ≫ S.blowdown i)
        = (vanishingIdeal
            _a4).comap (U.i ≫ S.blowdown i) := by rw [h1]
      _ = vanishingIdeal
            (⟨pre, hsuppcl⟩ : Closeds ↥(U.toScheme)) :=
          comap_vanishingIdeal_of_isOpenImmersion (U.i ≫ S.blowdown i) _ _ rfl
  have hrange1 : range ⇑j.base = pre := by
    rw [hpre]
    ext z
    simp only [mem_range, mem_preimage]
    constructor
    rintro ⟨y, rfl⟩
    rw [show bsM (U.i ≫ S.blowdown i) (bsM j y)
        = bsM (S.blowdown i) (U.ib $ bsM j y) from rfl, hbase y, hkeymap y,
      ← q5 $ S.strictTransformIdeal i]
    exact ⟨bsM (S.strictTransformMap i) y, rfl⟩
    intro hz
    have hzU : U.ib z ∈ (U :
        Set ↥_a5) := by
      rw [← q1 U]
      exact ⟨z, rfl⟩
    have hrr :=
      range_strictTransformio_succ S hN i hi'
    have hx : U.ib z ∈ range ⇑(S.strictTransformio $ i + 1).base := by
      rw [hrr]
      exact subset_closure ⟨hz, mp_ (S.mem_ambientCenterSupportCompl i _) $ hUsub hzU⟩
    obtain ⟨w, hw⟩ := hx
    refine ⟨w, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    rw [hbase w, hw]
  have hrange2 : range ⇑(vanishingIdeal
      (⟨pre, hsuppcl⟩ : Closeds ↥(U.toScheme))).subschemeι.base
        = pre := by simp_all
  have : IsReduced
      (vanishingIdeal
        (⟨pre, hsuppcl⟩ : Closeds ↥(U.toScheme))).subscheme :=
    isReduced_subscheme_vanishingIdeal _ _
  obtain ⟨e, he⟩ := exists_iso_of_range_base_eq j
    (vanishingIdeal
      (⟨pre, hsuppcl⟩ : Closeds ↥(U.toScheme))).subschemeι
    (tr_ hrange1 hrange2.symm)
  have ihsub := ih'
  rw [strictTransformio_eq_subschemeio] at ihsub
  have hsm2 := smooth_comap_subschemeio_of_isOpenImmersion
    (U.i ≫ S.blowdown i) (S.strictTransformIdeal i) (S.schemeAtToSpec i) ihsub
  rw [hKvan] at hsm2
  have hlev : S.blowdown i ≫ S.schemeAtToSpec i = S.schemeAtToSpec (i + 1) := by
    rw [schemeAtToSpec_eq, schemeAtToSpec_eq, ← assoc,
      ← projectionToBase_succ]
  have hgoal : S.strictTransformio (i + 1) ≫ S.schemeAtToSpec (i + 1)
      = isoH e ≫ ((vanishingIdeal
          (⟨pre, hsuppcl⟩ : Closeds ↥(U.toScheme))).subschemeι
          ≫ ((U.i ≫ S.blowdown i) ≫ S.schemeAtToSpec i)) := by
    rw [← hj, ← hlev, ← he]
    simp only [assoc]
  rw [hgoal]
  infer_instance
end

end
end
end

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical) {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y] [IsReduced Y] {pY} [LocallyOfFiniteType pY] [QuasiCompact pY] (D : EmbeddingDatum k Y pY)
include hB
theorem notMem_ambientCenter_support_of_notMem_detachedComponents
    (t : ℕ) (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (hsmq : Smooth
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformio t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t))
    (hcl : ∀ s, s ≤ t →
      ∀ y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform s),
      (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters s
        (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformio s).base y))
    (hDisj0 : ∀ C1_ C2_ :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0),
      C1_ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C2_ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform 0) →
      C1_ ≠ C2_ → Disjoint C1_ C2_)
    (C : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hfr : C ∉ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedComponents t)
    (z : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)) (hz : z ∈ C) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformio t).base z ∉
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)) := by
  let _c0 := canonicalPrincipalization hres hrad
  classical
  intro hmem
  let _a2 := D.toEmbeddedBlowupSequence _c0
  have hemb := _a2.isClosedEmbedding_strictTransformio t
  have hCcl :=
    hemb.isClosedMap _ $ isClosed_of_mem_irreducibleComponents _ hC
  obtain ⟨et_, het_⟩ := sober hC.1 $ isClosed_of_mem_irreducibleComponents _ hC
  let _a9 := D.toEmbeddedBlowupSequence _c0
  have _i1 : ∀ (t : ℕ), (∀ s, s ≤ t → ∀ y : ↥(_a9.strictTransform s), _a9.AvoidsCenters s $ bsM (_a9.strictTransformio s) y) → t ≤ _a9.length → ∀ C : Set ↥(_a9.strictTransform t), C ∈ irreducibleComponents ↥(_a9.strictTransform t) → ∀ hCcl : IsClosed $ ⇑(_a9.strictTransformio t).base '' C, ∀ x : ↥(_a9.schemeAt t), x ∈ ⇑(_a9.strictTransformio t).base '' C → AgreeNear ((principalizationOfEmbedding k Y pY D _c0).ideal t) (vanishingIdeal (⟨⇑(_a9.strictTransformio t).base '' C, hCcl⟩ : Closeds ↥(_a9.schemeAt t))) x := by
    let _a0 := D.toEmbeddedBlowupSequence _c0
    intro t
    induction t with
    | zero =>
      intro _ _ C hC hCcl x hx
      classical
      have hNoeth :=
        _a0.noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D _c0) 0
          (zero_le _)
      have hemb := _a0.isClosedEmbedding_strictTransformio 0
      have hid0 := principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D _c0 hemb.isClosed_range
      let _a2 := irreducibleComponents ↥(_a0.strictTransform 0) \ {C}
      obtain ⟨Bad, hBaddef⟩ : ∃ B : CSet $ _a0.schemeAt 0,
          B = ⋃ C'' ∈ _a2,
            ⇑(_a0.strictTransformio 0).base '' C'' := ⟨_, rfl⟩
      have hfin : _a2.Finite :=
        TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset sdiff_subset
      have hBadcl : IsClosed Bad := by
        rw [hBaddef]
        exact hfin.isClosed_biUnion fun C'' hC'' =>
          hemb.isClosedMap _ $ isClosed_of_mem_irreducibleComponents _ hC''.1
      have hxU : x ∈ Badᶜ := by
        intro hmem
        rw [hBaddef] at hmem
        obtain ⟨C'', hC''D, hxim⟩ := Set.mem_iUnion₂.mp hmem
        obtain ⟨z, hzC'', hz⟩ := hxim
        obtain ⟨w, hwC, hw⟩ := hx
        have hzw := hemb.injective $ tr_ hz hw.symm
        rw [hzw] at hzC''
        have hne := fun h => hC''D.2 $ Set.mem_singleton_iff.mpr h
        exact Set.disjoint_left.mp (hDisj0 C'' C hC''D.1 hC hne) hzC'' hwC
      have hinter : (range ⇑(_a0.strictTransformio 0).base) ∩ Badᶜ
          = (⇑(_a0.strictTransformio 0).base '' C) ∩ Badᶜ := by
        ext z
        constructor
        rintro ⟨⟨w, rfl⟩, hz⟩
        refine ⟨?_, hz⟩
        by_cases hw : w ∈ C
        exact ⟨w, hw, rfl⟩
        refine absurd ?_ hz
        rw [hBaddef]
        refine mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents w, ?_⟩
          ⟨w, mem_irreducibleComponent, rfl⟩
        intro h
        exact hw $ h ▸ mem_irreducibleComponent
        rintro ⟨⟨w, hwC, rfl⟩, hz⟩
        exact ⟨⟨w, rfl⟩, hz⟩
      rw [hid0]
      exact agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter
    | succ i ih =>
      intro hcl hi C hC hCcl x hx
      classical
      have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D _c0
      have hi' := lt_of_succ_le hi
      obtain ⟨et_, hetgen⟩ := sober hC.1 $ isClosed_of_mem_irreducibleComponents _ hC
      obtain ⟨C', hC'm, het', _⟩ :=
        _a0.exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC et_ hetgen
      have hC'cl :=
        (_a0.isClosedEmbedding_strictTransformio i).isClosedMap _
          (isClosed_of_mem_irreducibleComponents _ hC'm)
      obtain ⟨y, hyC, hxy⟩ := hx
      have hclx : _a0.AvoidsCenters (i + 1) x := by
        rw [← hxy]
        exact hcl (i + 1) le_rfl y
      have hnot := (mp_ (_a0.avoidsCenters_succ_iff i x) hclx).1
      have hblow :=
        mem_image_strictTransformio_of_mem_image_succ (D.toEmbeddedBlowupSequence _c0) i C et_ hetgen
          C' het' x ⟨y, hyC, hxy⟩
      obtain ⟨V, hxV, hVeq⟩ := mp_ (agreeNear_iff _ _ _)
        (ih (fun s hs => hcl s $ le_trans hs $ Nat.le_succ i) (le_of_succ_le hi)
          C' hC'm hC'cl _ hblow)
      let _s2 := _a0.schemeAt i
      obtain ⟨V', hV'⟩ : ∃ V' : Opn _s2, V' = V := ⟨V, rfl⟩
      let _s1 := _a0.blowdown i
      have hxV' : bsM _s1 x ∈ V' := by
        rwa [hV']
      let _s4 := principalizationOfEmbedding k Y pY D _c0
      let _a1 := vanishingIdeal (⟨⇑(_a0.strictTransformio i).base '' C', hC'cl⟩ : Closeds ↥_s2)
      have hV'eq : (_s4.ideal i).comap V'.i
          = _a1.comap V'.i := by
        rwa [hV']
      let _s3 := _a0.schemeAt $ i + 1
      obtain ⟨U, hUdef⟩ : ∃ U : Opn _s3,
          U = (map _s1.base).obj
            (V' ⊓ (D.toEmbeddedBlowupSequence _c0).ambientCenterSupportCompl i) := ⟨_, rfl⟩
      have hUsub : (U : Set ↥_s3) ⊆
          ⇑_s1.base ⁻¹'
            ((_a0.ambientCenterSupportCompl i : Opn _s2) :
              Set ↥_s2) := by
        rw [hUdef]
        intro z hz
        exact hz.2
      have hmemU : ∀ z : ↥U, bsM _s1 (U.ib z) ∉
          ((_a0.ambientCenter i).support :
            Set ↥_s2) := by
        intro z
        exact hUsub z.2
      have hxU : x ∈ U := by
        rw [hUdef]
        exact ⟨hxV', mpr_ (_a0.mem_ambientCenterSupportCompl i _) hnot⟩
      let _s0 := U.i ≫ _a0.blowdown i
      have :=
        isOpenImmersion_io_comp_blowdown (D.toEmbeddedBlowupSequence _c0) i hi' U hUsub
      have hexc : (_s4.exceptionalIdeal i).comap U.i = ⊤ := by
        refine comap_io_eq_top_of_disjoint _ _ ?_
        rw [disjoint_left]
        intro z hz hmem
        rw [_s4.exceptionalIdeal_eq i] at hmem
        exact absurd (mem_support_of_mem_support_comap
          (_s4.transitionMapSucc i) _ z hmem) $ hUsub hz
      have hJ :=
        comap_eq_comap_comp_of_mul_eq _ U _ _ _
          (_s4.ideal_succ i hi') hexc
      have hle : U ≤ (map
          _s1.base).obj V' := by
        rw [hUdef]
        intro z hz
        exact hz.1
      have hcomapph :=
        comap_ι_comp_eq_of_comap_ι_eq
          _s1 V' U hle _ _ hV'eq
      let _a3 := _a0.strictTransformio $ i + 1
      have hLHS : _a1.comap
            _s0
          = vanishingIdeal
              (closedPreimage U.i
                (⟨⇑_a3.base '' C, hCcl⟩ :
                  Closeds ↥_s3)) := by
        refine comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
          _s0 _ _ ?_
        ext z
        have hcb : bsM _s0 z
            = bsM _s1 (U.ib z) := rfl
        have hiff := mem_image_strictTransformio_iff_of_notMem_ambientCenter
          (D.toEmbeddedBlowupSequence _c0) hN i hi' C et_ hetgen C' het' (U.ib z) $ hmemU z
        constructor
        intro hz
        have hz1 := hz
        have hz2 := mpr_ hiff hz1
        have hz3 : bsM _s0 z
            ∈ ⇑(_a0.strictTransformio i).base '' C' := by
          rwa [hcb]
        exact hz3
        intro hz
        have hz1 := hz
        have hz2 : bsM _s1 (U.ib z)
            ∈ ⇑(_a0.strictTransformio i).base '' C' := by
          rwa [← hcb]
        exact mp_ hiff hz2
      exact mpr_ (agreeNear_iff _ _ _) ⟨U, hxU, tr_ hJ $ tr_ hcomapph $ tr_ hLHS (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.i (⟨⇑_a3.base '' C, hCcl⟩ : Closeds ↥_s3)).symm⟩
  have hagree := _i1 t hcl
    (le_of_lt ht) C hC hCcl
  let _a6 := _a9.strictTransformio t
  have hsmV : Smooth $ (vanishingIdeal (⟨⇑_a6.base '' C, hCcl⟩ : Closeds ↥(_a9.schemeAt t))).subschemeι ≫ chartLevelStructureMorphism k Y pY D _c0 t := by
    let A := _c0
    let ht := le_of_lt ht
    let _c0 := (D.toEmbeddedBlowupSequence A).strictTransformio t ≫ chartLevelStructureMorphism k Y pY D A t
    have hclopen :=
      isClopen_of_mem_irreducibleComponents_of_smooth
        _c0 C hC
    have hsub := smooth_subschemeio_vanishingIdeal_comp_of_isClopen
        _c0 C hclopen
    let _a0 := vanishingIdeal (⟨C, hclopen.isClosed⟩ : Closeds ↥((D.toEmbeddedBlowupSequence A).strictTransform t))
    have : IsReduced
        _a0.subscheme :=
      isReduced_subscheme_vanishingIdeal _ _
    let _a1 := (D.toEmbeddedBlowupSequence A).schemeAt t
    let _a3 := vanishingIdeal (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformio t).base '' C, hCcl⟩ : Closeds ↥_a1)
    have : IsReduced
        _a3.subscheme :=
      isReduced_subscheme_vanishingIdeal _ _
    have hrange :
        range ⇑(_a0.si ≫
            (D.toEmbeddedBlowupSequence A).strictTransformio t).base
          = range ⇑_a3.subschemeι.base := by
      rw [range_comp_base, range_base_subschemeio,
        range_base_subschemeio,
        coe_support_vanishingIdeal,
        coe_support_vanishingIdeal]
      rfl
    obtain ⟨e, he⟩ := exists_iso_of_range_base_eq _ _ hrange
    exact smooth_comp_of_iso_hom_eq e _ _ _ _ he hsub
  have hsmp : Smooth
      (chartLevelStructureMorphism k Y pY D _c0 t) := by
    rw [chartLevelStructureMorphism_eq_structureMorphism]
    exact IdealBlowupSequence.smooth_structureMorphism
      (principalizationOfEmbedding k Y pY D _c0) t $ le_of_lt ht
  have hspec := (PrincipalizationRules.isMaxOrderReduction_outputLevelData (canonicalAlgorithmRules hres) hB
      (krullDimSucc D.ambient)).cert
      (markedTripleOrderOne k D.ambient D.ambientStruct (ker D.emb) [])
      (markedTripleOrderOne_isAdmissible k D.ambient D.ambientStruct
        (ker D.emb) D.nonzeroOnComponents_ker [] D.sncEmpty)
      (le_of_eq $ markedTripleOrderOne_dim k D.ambient D.ambientStruct
        (ker D.emb) [])
      t ht
  have hgen :=
    isGenericPoint_image_of_isClosedEmbedding hemb het_
  have hirr :=
    hC.1.image _ hemb.continuous.continuousOn
  let _a0 := principalizationOfEmbedding k Y pY D _c0
  let _a1 := _a6
  let _a8 := ⇑_a1.base '' C
  have hIsupp :
      _a8 ⊆
      (((_a0.ideal t).support) :
        CSet $ _a0.schemeAt t) := by
    refine subset_support_of_agreeNear idealSheafGeometryHypotheses_vanishingIdealAssignment _ _ _ hCcl ?_
    intro x hx
    rw [vanishingIdealAssignment_apply]
    exact hagree x hx
  have hnz :=
    nonzeroOnComponents_ideal (principalizationOfEmbedding k Y pY D _c0)
      D.nonzeroOnComponents_ker t $ le_of_lt ht
  have hcomp : ∀ E ∈ irreducibleComponents
      ↥(_a2.schemeAt t),
      ¬ E ⊆ _a8 := by
    intro E hE hEsub
    exact (nonzeroOnComponents_iff _).1 hnz E hE $ hEsub.trans hIsupp
  have hxi :=
    _a2.notMem_ambientCenter_support_of_isGenericPoint t
      C hC hfr et_ het_
  refine false_of_mem_support_center
    (chartLevelStructureMorphism k Y pY D _c0 t) hsmp
    (_a0.ideal t)
    (_a2.ambientCenter t)
    (⋃ E ∈ _a0.boundary t,
      (E.support :
        CSet $ _a0.schemeAt t))
    hspec
    (⇑_a1.base '' C) hCcl hirr
    (bsM _a1 et_)
    (bsM _a1 z)
    hgen ⟨z, hz, rfl⟩ hsmV hcomp hxi ?_ hagree hmem
  rw [disjoint_left]
  rintro a ⟨w, hwC, rfl⟩ ha
  obtain ⟨E, hE, haE⟩ := Set.mem_iUnion₂.mp ha
  exact not_avoidsCenters_of_mem_boundary_support D _c0 t
    (le_of_lt ht) E hE _ haE $ hcl t le_rfl w

section
variable (hsm : Smooth pY) (t) (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) (y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
include hsm ht
theorem avoidsCenters_strictTransformio_of_smooth :
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).AvoidsCenters t
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformio t).base y) := by
  let _a5 := canonicalPrincipalization hres hrad
  let _c0 := D.toEmbeddedBlowupSequence _a5
  classical
  have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D _a5
  have hsm0 : Smooth $ _c0.strictTransformio 0 ≫ _c0.schemeAtToSpec 0 := by
    let S := _c0
    have hker : ker (S.strictTransformio 0)
        = ker (S.emb ≫ S.ambientSeq.isoZero.inv) := by simp_all
    obtain ⟨e, he⟩ :=
      exists_iso_of_ker_eq (S.strictTransformio 0) (S.emb ≫ S.ambientSeq.isoZero.inv) hker
    have hstruct : S.ambientSeq.isoZero.inv ≫ S.schemeAtToSpec 0 = S.ambientStruct := by
      rw [schemeAtToSpec_eq, projectionToBase_zero,
        ← assoc, m114, id_comp]
    have key : isoH e ≫ pY = S.strictTransformio 0 ≫ S.schemeAtToSpec 0 := by
      rw [← he]
      simp [assoc]
      rw [hstruct, S.emb_comp]
    rw [← key]
    infer_instance
  let _a4 := _c0.strictTransform 0
  have hDisj0 : ∀ C1_ C2_ :
        Set ↥_a4,
      C1_ ∈ irreducibleComponents
        ↥_a4 →
      C2_ ∈ irreducibleComponents
        ↥_a4 →
      C1_ ≠ C2_ → Disjoint C1_ C2_ := by
    intro C1_ C2_ h1_ h2_ hne
    exact irreducibleComponentsDisjointOfSmooth k _ _ hsm0 C1_ h1_ C2_ h2_ hne
  have main : ∀ s, s ≤ _c0.length →
      Smooth
        (_c0.strictTransformio s ≫
          _c0.schemeAtToSpec s) ∧
      ∀ r, r ≤ s →
        ∀ w : ↥(_c0.strictTransform r),
        _c0.AvoidsCenters r
          (bsM (_c0.strictTransformio r) w) := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨hsm0, ?_⟩
      intro r hr w
      obtain rfl : r = 0 := Nat.le_zero.mp hr
      exact _c0.avoidsCenters_zero _
    | succ i ih =>
      intro hi
      have hi' :=
        lt_of_succ_le hi
      obtain ⟨ihsm, ihcl⟩ := ih $ le_of_succ_le hi
      have hsmq' := ihsm
      let _a1 := _c0.strictTransformio $ i + 1
      have hclear : ∀ w :
          ↥(_c0.strictTransform $ i + 1),
          _c0.AvoidsCenters (i + 1)
            (bsM _a1 w) := by
        intro w
        have hCw :=
          irreducibleComponent_mem_irreducibleComponents w
        obtain ⟨et1, het1⟩ :=
          sober hCw.1 $ isClosed_of_mem_irreducibleComponents _ hCw
        obtain ⟨C', hC'm, het', hfr⟩ :=
          _c0.exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi'
            (irreducibleComponent w) hCw et1 het1
        have hsubcl : closure ({et1} :
            Set ↥(_c0.strictTransform $ i + 1)) ⊆
            ⇑(_c0.strictTransformMap i).base ⁻¹'
              closure ({(_c0.strictTransformMap i).base et1} :
                Set ↥(_c0.strictTransform i)) := by
          refine closure_minimal ?_ $ isClosed_closure.preimage $ (_c0.strictTransformMap i).base.hom.continuous
          intro v hv
          have hv' := hv
          subst hv'
          exact subset_closure rfl
        have hwC : w ∈ closure ({et1} :
            Set ↥(_c0.strictTransform $ i + 1)) := by
          rw [het1]
          exact mem_irreducibleComponent
        have hzC' : bsM (_c0.strictTransformMap i) w
            ∈ C' := by
          have hmm := hsubcl hwC
          rwa [mem_preimage, het'] at hmm
        have hkey : bsM (_c0.strictTransformio i)
            (bsM (_c0.strictTransformMap i) w)
            = bsM (_c0.blowdown i)
                (bsM _a1 w) := by
          have h : bsM ((_c0.strictTransformMap i) ≫
              (_c0.strictTransformio i)) w
              = bsM (_a1 ≫
                (_c0.blowdown i)) w := by
            rw [_c0.strictTransformMap_comp_strictTransformio i]
          simpa using h
        refine mpr_ (_c0.avoidsCenters_succ_iff i _)
          ⟨?_, ?_⟩
        rw [← hkey]
        exact notMem_ambientCenter_support_of_notMem_detachedComponents hres hB hrad D i hi'
          hsmq' ihcl hDisj0 C' hC'm hfr _ hzC'
        rw [← hkey]
        exact ihcl i le_rfl _
      refine ⟨smooth_strictTransformio_comp_schemeAtToSpec_succ _c0 hN i hi'
        ihsm ?_, ?_⟩
      intro w
      exact an1 $ mp_ (_c0.avoidsCenters_succ_iff i _)
        (hclear w)
      intro r hr w
      rcases m63 r (i + 1) with hlt | hge
      exact ihcl r (Nat.lt_succ_iff.mp hlt) w
      obtain rfl : r = i + 1 := le_antisymm hr hge
      exact hclear w
  exact an2 (main t ht) t le_rfl y

theorem strictTransformio_notMem_support_of_mem_boundary
    (E : ((principalizationOfEmbedding k Y pY D $ canonicalPrincipalization hres hrad).schemeAt t).IdealSheafData)
    (hE : E ∈ (principalizationOfEmbedding k Y pY D $ canonicalPrincipalization hres hrad).boundary t) :
    ((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransformio t).base y ∉
      (E.support :
        Set ↥((principalizationOfEmbedding k Y pY D $ canonicalPrincipalization hres hrad).schemeAt t)) := by
  intro hx
  exact not_avoidsCenters_of_mem_boundary_support D (canonicalPrincipalization hres hrad) t ht E hE _ hx
    (avoidsCenters_strictTransformio_of_smooth hres hB hrad D hsm t ht y)
end
end

end OpenImmersionRestriction





namespace OpenImmersionRestriction

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical) {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y] [IsReduced Y] {pY} [LocallyOfFiniteType pY] [QuasiCompact pY] (D : EmbeddingDatum k Y pY) (hsm : Smooth pY)
include hB hsm
theorem smooth_strictTransformio_comp_schemeAtToSpec :
    ∀ i, i ≤ (D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).length →
      Smooth
        ((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransformio i ≫
          (D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).schemeAtToSpec i) := by
  have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D $ canonicalPrincipalization hres hrad
  intro i
  induction i with
  | zero =>
      intro _
      set S := D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad) with _hS
      have hker : ker (S.strictTransformio 0)
          = ker (S.emb ≫ S.ambientSeq.isoZero.inv) := by simp_all
      obtain ⟨e, he⟩ :=
        exists_iso_of_ker_eq (S.strictTransformio 0) (S.emb ≫ S.ambientSeq.isoZero.inv) hker
      have hstruct : S.ambientSeq.isoZero.inv ≫ S.schemeAtToSpec 0 = S.ambientStruct := by
        rw [schemeAtToSpec_eq, projectionToBase_zero,
          ← assoc, m114, id_comp]
      have key : isoH e ≫ pY = S.strictTransformio 0 ≫ S.schemeAtToSpec 0 := by
        rw [← he]
        simp only [assoc]
        rw [hstruct, S.emb_comp]
      rw [← key]
      infer_instance
  | succ i ih =>
      intro hi
      set S := D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad) with _hS
      have hi' := hi
      have ih' := ih $ le_of_succ_le hi
      have hredi :=
        isReduced_strictTransform_of_isNoetherian S hN i $ m49 hi'
      let _a1 := S.schemeAt $ i + 1
      have hredi1 :=
        isReduced_strictTransform_of_isNoetherian S hN (i + 1) hi
      set U : Opn _a1 :=
        (map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) with _hU
      let _a5 := S.schemeAt i
      have hUsub : (U : Set ↥_a1) ⊆
          ⇑(S.blowdown i).base ⁻¹'
            ((S.ambientCenterSupportCompl i : Opn _a5) : Set ↥_a5) := fun _ hx => hx
      have hgi :=
        isOpenImmersion_io_comp_blowdown S i hi' U hUsub
      let _s1 := S.strictTransformio $ i + 1
      have hrangeA : range ⇑_s1.base ⊆ range ⇑U.ib := by
        rw [q1]
        rintro z ⟨y, rfl⟩
        exact mpr_ (S.mem_ambientCenterSupportCompl i _)
          (mp_ (S.avoidsCenters_succ_iff i _) $ avoidsCenters_strictTransformio_of_smooth hres hB hrad D hsm (i + 1) hi y).1
      set j := m43 U.i _s1 hrangeA with _hjdef
      have hj : j ≫ U.i = S.strictTransformio (i + 1) :=
        m115 _ _ _
      have hjc : IsClosedImmersion $ j ≫ U.i := by
        rw [hj]
        infer_instance
      have :=
        of_comp j U.i
      have hbase : ∀ y,
          U.ib (bsM j y) = bsM _s1 y := by
        intro y
        rw [show U.ib (bsM j y) = bsM (j ≫ U.i) y from rfl, hj]
      have hkeymap : ∀ y,
          (S.blowdown i).base (bsM _s1 y)
            = bsM (S.strictTransformio i) (bsM (S.strictTransformMap i) y) := by
        intro y
        have h : bsM (S.strictTransformMap i ≫ S.strictTransformio i) y
            = bsM (S.strictTransformio (i + 1) ≫ S.blowdown i) y := by
          rw [S.strictTransformMap_comp_strictTransformio i]
        exact sy_ h
      set pre : Set ↥(U.toScheme) := ⇑(U.i ≫ S.blowdown i).base ⁻¹'
          (((S.strictTransformIdeal i).support : Closeds ↥_a5) :
            Set ↥_a5) with hpre
      have hsuppcl : IsClosed pre := by
        rw [hpre]
        exact (S.strictTransformIdeal i).support.2.preimage
          (U.i ≫ S.blowdown i).base.hom.continuous
      have hker_eq : S.strictTransformIdeal i = ker (S.strictTransformio i) := by
        rw [strictTransformio_eq_subschemeio, q2]
      have h1 : vanishingIdeal
          ((S.strictTransformIdeal i).support) = S.strictTransformIdeal i := by
        rw [vanishingIdeal_support, hker_eq]
        exact radical_ker_eq_ker $ S.strictTransformio i
      have hKvan : (S.strictTransformIdeal i).comap (U.i ≫ S.blowdown i)
          = vanishingIdeal
              (⟨pre, hsuppcl⟩ : Closeds ↥(U.toScheme)) := by
        calc (S.strictTransformIdeal i).comap (U.i ≫ S.blowdown i)
            = (vanishingIdeal
                ((S.strictTransformIdeal i).support)).comap (U.i ≫ S.blowdown i) := by rw [h1]
          _ = vanishingIdeal
                (⟨pre, hsuppcl⟩ : Closeds ↥(U.toScheme)) :=
              comap_vanishingIdeal_of_isOpenImmersion (U.i ≫ S.blowdown i) _ _ rfl
      have hrange1 : range ⇑j.base = pre := by
        rw [hpre]
        ext z
        simp only [mem_range, mem_preimage]
        constructor
        rintro ⟨y, rfl⟩
        rw [show bsM (U.i ≫ S.blowdown i) (bsM j y)
            = bsM (S.blowdown i) (U.ib $ bsM j y) from rfl, hbase y, hkeymap y,
          ← q5 $ S.strictTransformIdeal i]
        exact ⟨bsM (S.strictTransformMap i) y, rfl⟩
        intro hz
        have hzU : U.ib z ∈ (U :
            Set ↥_a1) := by
          rw [← q1 U]
          exact ⟨z, rfl⟩
        have hrr :=
          range_strictTransformio_succ S hN i hi'
        have hx : U.ib z ∈ range ⇑_s1.base := by
          rw [hrr]
          exact subset_closure ⟨hz, mp_ (S.mem_ambientCenterSupportCompl i _) $ hUsub hzU⟩
        obtain ⟨w, hw⟩ := hx
        refine ⟨w, ?_⟩
        apply U.ι.isOpenEmbedding.injective
        rw [hbase w, hw]
      let _s0 := vanishingIdeal (⟨pre, hsuppcl⟩ : Closeds ↥(U.toScheme))
      have hrange2 : range ⇑_s0.subschemeι.base
            = pre := by
        rw [range_base_subschemeio,
          coe_support_vanishingIdeal]
        rfl
      have : IsReduced
          _s0.subscheme :=
        isReduced_subscheme_vanishingIdeal _ _
      obtain ⟨e, he⟩ := exists_iso_of_range_base_eq j
        _s0.si
        (tr_ hrange1 hrange2.symm)
      have ihsub := ih'
      rw [strictTransformio_eq_subschemeio] at ihsub
      have hsm2 := smooth_comap_subschemeio_of_isOpenImmersion
        (U.i ≫ S.blowdown i) (S.strictTransformIdeal i) (S.schemeAtToSpec i) ihsub
      rw [hKvan] at hsm2
      have hlev : S.blowdown i ≫ S.schemeAtToSpec i = S.schemeAtToSpec (i + 1) := by
        rw [schemeAtToSpec_eq, schemeAtToSpec_eq, ← assoc,
          ← projectionToBase_succ]
      have hgoal : S.strictTransformio (i + 1) ≫ S.schemeAtToSpec (i + 1)
          = isoH e ≫ (_s0.si
              ≫ ((U.i ≫ S.blowdown i) ≫ S.schemeAtToSpec i)) := by
        rw [← hj, ← hlev, ← he]
        simp only [assoc]
      rw [hgoal]
      infer_instance

section
variable (t) (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
include ht
theorem smooth_strictTransformio_comp_chartLevelStructureMorphism :
    Smooth
      ((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransformio t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
  let _a0 := canonicalPrincipalization hres hrad
  have hP : (D.toEmbeddedBlowupSequence _a0).schemeAtToSpec t
      = chartLevelStructureMorphism k Y pY D _a0 t := rfl
  rw [← hP]
  exact smooth_strictTransformio_comp_schemeAtToSpec hres hB hrad D hsm t ht

theorem disjoint_irreducibleComponents_strictTransform
    {C1_ C2_ : Set ↥((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransform t)}
    (h1_ : C1_ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransform t))
    (h2_ : C2_ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransform t))
    (hne : C1_ ≠ C2_) :
    Disjoint C1_ C2_ :=
  irreducibleComponentsDisjointOfSmooth k _ _
    (smooth_strictTransformio_comp_chartLevelStructureMorphism hres hB hrad D hsm t ht) C1_ h1_ C2_ h2_ hne

theorem smooth_vanishingIdeal_image_comp_chartLevelStructureMorphism
    (C : Set ↥((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransform t))
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransform t))
    (hCcl : IsClosed
      (⇑((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransformio t).base '' C)) :
    Smooth
      ((vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).strictTransformio t).base '' C, hCcl⟩ :
            Closeds
              ↥((D.toEmbeddedBlowupSequence
                (canonicalPrincipalization hres hrad)).schemeAt t))).subschemeι ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
  let _a3 := canonicalPrincipalization hres hrad
  let _c0 := D.toEmbeddedBlowupSequence _a3
  have hclopen : IsClopen C := by
    let _a0 := D.toEmbeddedBlowupSequence _a3
    have hNoeth :=
      _a0.noetherianSpace_strictTransform_of_isNoetherian
        (isNoetherian_schemeAt_toEmbeddedBlowupSequence D _a3) t ht
    have hsep : ∀ C1_ ∈ irreducibleComponents
        ↥(_a0.strictTransform t),
        ∀ C2_ ∈ irreducibleComponents
          ↥(_a0.strictTransform t),
        (C1_ ∩ C2_).Nonempty → C1_ = C2_ := by
      intro C1_ h1_ C2_ h2_ hx
      by_contra hne
      obtain ⟨x, hx1_, hx2_⟩ := hx
      exact Set.disjoint_left.mp
        (disjoint_irreducibleComponents_strictTransform hres hB hrad D hsm t ht h1_ h2_ hne) hx1_ hx2_
    have hopen :=
      isOpen_sUnion_of_subset_irreducibleComponents hsep $ by
        intro C' hC'
        obtain rfl : C' = C := Set.mem_singleton_iff.mp hC'
        exact hC
    rw [Set.sUnion_singleton] at hopen
    exact ⟨isClosed_of_mem_irreducibleComponents _ hC, hopen⟩
  have hsmq :=
    smooth_strictTransformio_comp_chartLevelStructureMorphism hres hB hrad D hsm t ht
  let _a1 := chartLevelStructureMorphism k Y pY D _a3 t
  have hPlevel : _c0.schemeAtToSpec t
      = _a1 := rfl
  let _a4 := _c0.strictTransformio t ≫ _a1
  have hftq : LocallyOfFiniteType
      _a4 := by
    have h1 :=
      _c0.locallyOfFiniteType_strictTransformToSpec t ht
    rwa [strictTransformToSpec_eq, hPlevel] at h1
  have hsub := smooth_subschemeio_vanishingIdeal_comp_of_isClopen
      _a4 C hclopen
  let _a2 := vanishingIdeal (⟨C, hclopen.isClosed⟩ : Closeds ↥(_c0.strictTransform t))
  have : IsReduced
      _a2.subscheme :=
    isReduced_subscheme_vanishingIdeal _ _
  let _a0 := vanishingIdeal (⟨⇑(_c0.strictTransformio t).base '' C, hCcl⟩ : Closeds ↥(_c0.schemeAt t))
  have : IsReduced
      _a0.subscheme :=
    isReduced_subscheme_vanishingIdeal _ _
  have hrange :
      range ⇑(siI _a2 ≫
          _c0.strictTransformio t).base
        = range ⇑_a0.subschemeι.base := by
    rw [range_comp_base, range_base_subschemeio,
      range_base_subschemeio,
      coe_support_vanishingIdeal,
      coe_support_vanishingIdeal]
    rfl
  obtain ⟨e, he⟩ := exists_iso_of_range_base_eq _ _ hrange
  exact smooth_comp_of_iso_hom_eq e _ _ _ _ he hsub
end
end

theorem agreeNear_vanishingIdeal_image_of_forall_avoidsCenters_of_disjoint
    {k : Type} [Field k] [CharZero k]
    {Y} [IsAffine Y] [IsReduced Y]
    {pY} [LocallyOfFiniteType pY]
    [QuasiCompact pY] (D : EmbeddingDatum k Y pY) A
    (hClearAll : ∀ s, s ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ y : ↥((D.toEmbeddedBlowupSequence A).strictTransform s),
        (D.toEmbeddedBlowupSequence A).AvoidsCenters s $ ((D.toEmbeddedBlowupSequence A).strictTransformio s).base y)
    (hDisjAll : ∀ s, s ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C1_ C2_ : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform s),
        C1_ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform s) →
        C2_ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform s) →
        C1_ ≠ C2_ → Disjoint C1_ C2_) :
    ∀ t, t ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform t),
        C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform t) →
        ∀ hCcl : IsClosed $ ⇑((D.toEmbeddedBlowupSequence A).strictTransformio t).base '' C,
        ∀ x : ↥((D.toEmbeddedBlowupSequence A).schemeAt t),
          x ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformio t).base '' C →
          AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal t)
            (vanishingIdeal
              (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformio t).base '' C, hCcl⟩ :
                Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))) x := by
  let _a0 := D.toEmbeddedBlowupSequence A
  intro t
  induction t with
  | zero =>
    intro _ C hC hCcl x hx
    classical
    have hNoeth :=
      _a0.noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) 0
        (zero_le _)
    have hemb := _a0.isClosedEmbedding_strictTransformio 0
    have hid0 := principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D A hemb.isClosed_range
    let _a2 := irreducibleComponents ↥(_a0.strictTransform 0) \ {C}
    obtain ⟨Bad, hBaddef⟩ : ∃ B : CSet $ _a0.schemeAt 0,
        B = ⋃ C'' ∈ _a2,
          ⇑(_a0.strictTransformio 0).base '' C'' := ⟨_, rfl⟩
    have hfin : _a2.Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset sdiff_subset
    have hBadcl : IsClosed Bad := by
      rw [hBaddef]
      exact hfin.isClosed_biUnion fun C'' hC'' =>
        hemb.isClosedMap _ $ isClosed_of_mem_irreducibleComponents _ hC''.1
    have hxU : x ∈ Badᶜ := by
      intro hmem
      rw [hBaddef] at hmem
      obtain ⟨C'', hC''D, hxim⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨z, hzC'', hz⟩ := hxim
      obtain ⟨w, hwC, hw⟩ := hx
      have hzw := hemb.injective $ tr_ hz hw.symm
      rw [hzw] at hzC''
      have hne := fun h => an2 hC''D $ Set.mem_singleton_iff.mpr h
      exact Set.disjoint_left.mp
        (hDisjAll 0 (zero_le _) C'' C hC''D.1 hC hne) hzC'' hwC
    have hinter : (range ⇑(_a0.strictTransformio 0).base) ∩ Badᶜ
        = (⇑(_a0.strictTransformio 0).base '' C) ∩ Badᶜ := by
      ext z
      constructor
      rintro ⟨⟨w, rfl⟩, hz⟩
      refine ⟨?_, hz⟩
      by_cases hw : w ∈ C
      exact ⟨w, hw, rfl⟩
      refine absurd ?_ hz
      rw [hBaddef]
      refine mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents w, ?_⟩
        ⟨w, mem_irreducibleComponent, rfl⟩
      intro h
      exact hw $ h ▸ mem_irreducibleComponent
      rintro ⟨⟨w, hwC, rfl⟩, hz⟩
      exact ⟨⟨w, rfl⟩, hz⟩
    rw [hid0]
    exact agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter
  | succ i ih =>
    intro hi C hC hCcl x hx
    classical
    have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D A
    have hi' := lt_of_succ_le hi
    obtain ⟨et_, hetgen⟩ := sober hC.1 $ isClosed_of_mem_irreducibleComponents _ hC
    obtain ⟨C', hC'm, het', _⟩ :=
      _a0.exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC et_ hetgen
    have hC'cl :=
      (_a0.isClosedEmbedding_strictTransformio i).isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ hC'm)
    obtain ⟨y, hyC, hxy⟩ := hx
    have hclx := hClearAll (i + 1) hi y
    rw [hxy] at hclx
    have hnot := an1 $ mp_ (_a0.avoidsCenters_succ_iff i x) hclx
    have hblow :=
      mem_image_strictTransformio_of_mem_image_succ (D.toEmbeddedBlowupSequence A) i C et_ hetgen
        C' het' x ⟨y, hyC, hxy⟩
    obtain ⟨V, hxV, hVeq⟩ := mp_ (agreeNear_iff _ _ _)
      (ih (le_of_succ_le hi) C' hC'm hC'cl _ hblow)
    let _s2 := _a0.schemeAt i
    obtain ⟨V', hV'⟩ : ∃ V' : Opn _s2, V' = V := ⟨V, rfl⟩
    let _s1 := _a0.blowdown i
    have hxV' : bsM _s1 x ∈ V' := by
      rwa [hV']
    let _s4 := principalizationOfEmbedding k Y pY D A
    let _a1 := vanishingIdeal (⟨⇑(_a0.strictTransformio i).base '' C', hC'cl⟩ : Closeds ↥_s2)
    have hV'eq : (_s4.ideal i).comap V'.i
        = _a1.comap V'.i := by
      rwa [hV']
    let _s3 := _a0.schemeAt $ i + 1
    obtain ⟨U, hUdef⟩ : ∃ U : Opn _s3,
        U = (map _s1.base).obj
          (V' ⊓ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i) := ⟨_, rfl⟩
    have hUsub : (U : Set ↥_s3) ⊆
        ⇑_s1.base ⁻¹'
          ((_a0.ambientCenterSupportCompl i : Opn _s2) :
            Set ↥_s2) := by
      rw [hUdef]
      intro z hz
      exact an2 hz
    have hmemU : ∀ z : ↥U, bsM _s1 (U.ib z) ∉
        ((_a0.ambientCenter i).support :
          Set ↥_s2) := by
      intro z
      exact hUsub z.2
    have hxU : x ∈ U := by
      rw [hUdef]
      exact ⟨hxV', mpr_ (_a0.mem_ambientCenterSupportCompl i _) hnot⟩
    let _s0 := U.i ≫ _a0.blowdown i
    have :=
      isOpenImmersion_io_comp_blowdown (D.toEmbeddedBlowupSequence A) i hi' U hUsub
    have hexc : (_s4.exceptionalIdeal i).comap U.i = ⊤ := by
      refine comap_io_eq_top_of_disjoint _ _ ?_
      rw [disjoint_left]
      intro z hz hmem
      rw [_s4.exceptionalIdeal_eq i] at hmem
      exact absurd (mem_support_of_mem_support_comap
        (_s4.transitionMapSucc i) _ z hmem) $ hUsub hz
    have hJ :=
      comap_eq_comap_comp_of_mul_eq _ U _ _ _
        (_s4.ideal_succ i hi') hexc
    have hle : U ≤ (map
        _s1.base).obj V' := by
      rw [hUdef]
      intro z hz
      exact an1 hz
    have hcomapph :=
      comap_ι_comp_eq_of_comap_ι_eq
        _s1 V' U hle _ _ hV'eq
    let _a3 := _a0.strictTransformio $ i + 1
    have hLHS : _a1.comap
          _s0
        = vanishingIdeal
            (closedPreimage U.i
              (⟨⇑_a3.base '' C, hCcl⟩ :
                Closeds ↥_s3)) := by
      refine comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
        _s0 _ _ ?_
      ext z
      have hcb : bsM _s0 z
          = bsM _s1 (U.ib z) := rfl
      have hiff := mem_image_strictTransformio_iff_of_notMem_ambientCenter
        (D.toEmbeddedBlowupSequence A) hN i hi' C et_ hetgen C' het' (U.ib z) $ hmemU z
      constructor
      intro hz
      have hz1 := hz
      have hz2 := mpr_ hiff hz1
      have hz3 : bsM _s0 z
          ∈ ⇑(_a0.strictTransformio i).base '' C' := by
        rwa [hcb]
      exact hz3
      intro hz
      have hz1 := hz
      have hz2 : bsM _s1 (U.ib z)
          ∈ ⇑(_a0.strictTransformio i).base '' C' := by simp_all
      exact mp_ hiff hz2
    exact mpr_ (agreeNear_iff _ _ _) ⟨U, hxU, tr_ hJ $ tr_ hcomapph $ tr_ hLHS (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.i (⟨⇑_a3.base '' C, hCcl⟩ : Closeds ↥_s3)).symm⟩

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical) {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y] [IsReduced Y] {pY} [LocallyOfFiniteType pY]
include hB

theorem mem_detachedLocus_of_mem_support_ambientCenter (D : EmbeddingDatum k Y pY)
    (hsm : Smooth pY) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hy : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformio t).base y ∈
      ((((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support) :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t))) :
    y ∈ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t := by
  let _c0 := D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad
  let _c1 := canonicalPrincipalization hres hrad
  classical
  refine subset_detachedLocus_of_mem_detachedComponents
    _c0 t ?_ mem_irreducibleComponent
  rw [EmbeddedBlowupSequence.mem_detachedComponents]
  refine ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩
  by_contra hsub
  have hCmem :=
    irreducibleComponent_mem_irreducibleComponents y
  have hCfr : irreducibleComponent y ∉
      _c0.detachedComponents t := by
    intro hmem
    exact hsub
      ((_c0.mem_detachedComponents t
        (irreducibleComponent y)).1 hmem).2
  have hCcl :=
    isClosed_of_mem_irreducibleComponents _ hCmem
  obtain ⟨xi_, hxi_⟩ := sober hCmem.1 hCcl
  have hemb :=
    _c0.isClosedEmbedding_strictTransformio t
  let _s0 := ⇑(_c0.strictTransformio t).base '' irreducibleComponent y
  have himcl := hemb.isClosedMap _ hCcl
  have himirr := hCmem.1.image _ hemb.continuous.continuousOn
  let _a3 := principalizationOfEmbedding k Y pY D _c1
  have hagreeId : ∀ x ∈
        _s0,
      AgreeNear (_a3.ideal t)
        (vanishingIdeal
          (⟨⇑(_c0.strictTransformio t).base ''
              irreducibleComponent y, himcl⟩ :
            Closeds
              ↥(_c0.schemeAt t))) x := by
    intro x hx
    exact (fun hres hB hrad D hsm t ht C hC hCcl x hx => agreeNear_vanishingIdeal_image_of_forall_avoidsCenters_of_disjoint D (canonicalPrincipalization hres hrad)
    (fun s hs y => avoidsCenters_strictTransformio_of_smooth hres hB hrad D hsm s hs y)
    (fun s hs _C₁ _C₂ h1_ h2_ hne =>
      disjoint_irreducibleComponents_strictTransform hres hB hrad D hsm s hs h1_ h2_ hne)
    t ht C hC hCcl x hx) hres hB hrad D hsm t (le_of_lt ht)
      (irreducibleComponent y) hCmem himcl x hx
  have hsubsupp : _s0 ⊆
      ((spI (_a3.ideal t)) :
        Set ↥(_a3.schemeAt t)) := by
    refine subset_support_of_agreeNear idealSheafGeometryHypotheses_vanishingIdealAssignment _ _ _ himcl ?_
    intro x hx
    rw [vanishingIdealAssignment_apply]
    exact hagreeId x hx
  have hcomp : ∀ E ∈ irreducibleComponents
      ↥(_c0.schemeAt t),
      ¬ E ⊆ _s0 := by
    intro E hE hEsub
    exact (nonzeroOnComponents_iff _).1 (nonzeroOnComponents_ideal _a3 D.nonzeroOnComponents_ker t (le_of_lt ht)) E hE (hEsub.trans hsubsupp)
  have hdisj : Disjoint
      _s0
      (⋃ E ∈ _a3.boundary t,
        (spI E :
          Set ↥(_a3.schemeAt t))) := by
    rw [disjoint_left]
    rintro a ⟨z, hz, rfl⟩ ha
    obtain ⟨E, hE, haE⟩ := Set.mem_iUnion₂.mp ha
    exact strictTransformio_notMem_support_of_mem_boundary hres hB hrad D hsm t (le_of_lt ht) z E hE haE
  have hspec := (PrincipalizationRules.isMaxOrderReduction_outputLevelData (canonicalAlgorithmRules hres) hB
      (krullDimSucc D.ambient)).cert
      (markedTripleOrderOne k D.ambient D.ambientStruct (ker D.emb) [])
      (markedTripleOrderOne_isAdmissible k D.ambient D.ambientStruct
        (ker D.emb) D.nonzeroOnComponents_ker [] D.sncEmpty)
      (le_of_eq (markedTripleOrderOne_dim k D.ambient D.ambientStruct
        (ker D.emb) []))
      t ht
  refine false_of_mem_support_center
    (chartLevelStructureMorphism k Y pY D _c1 t) ?_
    (_a3.ideal t)
    (_c0.ambientCenter t)
    (⋃ E ∈ _a3.boundary t,
      (spI E :
        Set ↥(_a3.schemeAt t)))
    hspec
    _s0
    himcl himirr
    (bsM (_c0.strictTransformio t) xi_)
    (bsM (_c0.strictTransformio t) y)
    (isGenericPoint_image_of_isClosedEmbedding hemb hxi_) ⟨y, mem_irreducibleComponent, rfl⟩
    (smooth_vanishingIdeal_image_comp_chartLevelStructureMorphism hres hB hrad D hsm t (le_of_lt ht)
      (irreducibleComponent y) hCmem himcl)
    hcomp (_c0.notMem_ambientCenter_support_of_isGenericPoint t (irreducibleComponent y) hCmem hCfr xi_ hxi_) hdisj hagreeId hy
  rw [chartLevelStructureMorphism_eq_structureMorphism]
  exact IdealBlowupSequence.smooth_structureMorphism
    _a3 t (le_of_lt ht)
end

end OpenImmersionRestriction




theorem smooth_opens_io {X : Sch} (U : Opn X) :
    Smooth U.ι := by
  rw [← smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  exact (of_bijective (m189 _) :
    (hom $ stalkMap U.i x).FormallySmooth)

section
variable {X Z : Sch} (f : X ⟶ Z) [LocallyOfFinitePresentation f]
theorem smooth_io_comp_of_le_smoothLocus (U : Opn X)
    (hU : U ≤ smoothLocus f) :
    Smooth $ U.ι ≫ f := by
  rw [← smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  have hx := hU x.2
  have hg : (hom
      (stalkMap U.i x)).FormallySmooth :=
    of_bijective $ m189 _
  exact Eq.mpr (congrArg (fun ph_ => (hom ph_).FormallySmooth) $ stalkMap_comp U.i f x) $ comp hx hg

end

theorem ker_morphismRestrict {X W : Sch} (f : X ⟶ W)
    [IsClosedImmersion f] (V : Opn W) :
    ker (f ∣_ V) =
      (ker f).comap V.ι :=
  OpenImmersionRestriction.ker_eq_comap_ker_of_isPullback_isOpenImmersion f V.i (mrU f V) (opI $ preU f V)
    (m226 f V).flip

section
variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y] {pY} [LocallyOfFiniteType pY]
theorem inducedBlowupsWithoutIso_eq_withoutIsoBlowups (S : EmbeddedBlowupSequence k Y pY)
    (h : S.TransitionsAreBlowups) : S.inducedBlowupsWithoutIso h = (S.inducedBlowups h).withoutIsoBlowups := rfl

noncomputable def restrictEmbeddingDatumBasicOpen (D : EmbeddingDatum k Y pY)
    (hsnc : NilIsStrictNormalCrossingsOfSmooth) (r : Γ(D.ambient, ⊤)) :
    EmbeddingDatum k (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) where
  ambient := (D.ambient.basicOpen r).toScheme
  ambientStruct := (D.ambient.basicOpen r).ι ≫ D.ambientStruct
  emb := D.emb ∣_ D.ambient.basicOpen r
  isAffine_ambient := (isAffineOpen_top D.ambient).basicOpen r
  smooth_ambientStruct := by
    have := D.smooth_ambientStruct
    have := smooth_opens_io $ D.ambient.basicOpen r
    infer_instance
  locallyOfFiniteType_ambientStruct := inferInstance
  quasiCompact_ambientStruct := by
    have : IsAffine (D.ambient.basicOpen r).toScheme :=
      (isAffineOpen_top D.ambient).basicOpen r
    exact inferInstance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := by
    rw [ker_morphismRestrict]
    exact D.nonzeroOnComponents_ker.comap_of_isOpenImmersion _
  comp_eq := by
    rw [← assoc, morphismRestrict_ι, assoc, D.comp_eq]
  sncEmpty := by
    have := D.smooth_ambientStruct
    have := smooth_opens_io $ D.ambient.basicOpen r
    exact hsnc k _ _ inferInstance
end

theorem isPullbackSeq_of_smooth
    A (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type) [Field k] [CharZero k] Y Y'
    p p'
    [LocallyOfFiniteType p] [QuasiCompact p]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType p'] [QuasiCompact p']
    [IsReduced Y'] [IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    ph_ (hsmph : Smooth ph_) ps_
    (hph : ph_ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ps_ ph_ D.emb) :
    IsPullbackBlowupSequence ps_ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' ph_ ps_ hph hsq

theorem centersLieOver_of_withoutIsoBlowups {X} (s : SequenceOfBlowups X) Z
    (h : s.withoutIsoBlowups.CentersLieOver Z) : s.CentersLieOver Z := by
  intro i hi x hx
  have hne : sbCtr s i ≠ ⊤ := by
    intro h0
    have h1 :=
      (support_eq_bot_iff _).mpr h0
    have h2 : x ∈ ((⊥ : Closeds ↥(sbAt s i)) : CSet $ sbAt s i) := by
      rwa [← h1]
    exact h2
  obtain ⟨j, hj, hji⟩ := s.exists_nontrivialIndex_eq_of_center_ne_top hi hne
  subst hji
  have h1 := h j (by rw [withoutIsoBlowups_length]; exact hj) x
    (by rw [SequenceOfBlowups.withoutIsoBlowups_center]; exact hx)
  rwa [SequenceOfBlowups.withoutIsoBlowups_projectionToBase] at h1

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension) (hrad : SmoothSubschemeIdealIsRadical)
include hB
section
variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y] [IsReduced Y] {pY} [LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY) (hsm : Smooth pY)
include hsm
theorem centerOffDetached_eq_top_of_smooth t
    (ht : t < (D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).length) :
    (D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).centerOffDetached t = ⊤ := by
  have : QuasiCompact pY := by
    rw [← D.comp_eq]
    infer_instance
  have hiso := OpenImmersionRestriction.detachedLocusIsOpen_toEmbeddedBlowupSequence OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment hres hB hrad k Y pY D
  let _a0 := D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad
  have hnoe :=
    EmbeddedBlowupSequence.noetherianSpace_strictTransform_of_isNoetherian _
      (EmbeddedBlowupSequence.isNoetherian_schemeAt _a0) t
      (le_of_lt ht)
  have hopen :=
    hiso t ht
  apply mpr_ $ eq_top_iff_support_eq_empty _
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have h1 := EmbeddedBlowupSequence.support_centerOffDetached_subset_preimage
    _a0 t hy
  have h2 :=
    OpenImmersionRestriction.mem_detachedLocus_of_mem_support_ambientCenter hres hB hrad D hsm t ht y h1
  have h3 := EmbeddedBlowupSequence.support_centerOffDetached_subset_detachedClosureCompl
    _a0 t hnoe hopen hy
  rw [EmbeddedBlowupSequence.detachedClosureCompl_coe, EmbeddedBlowupSequence.detachedClosure_coe] at h3
  exact h3 h2

section
variable (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups)
theorem toEmbeddedBlowupSequence_center_eq_top_of_smooth t
    (ht : t < (D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).length) :
    center ((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).inducedBlowups hbl) t = ⊤ := by
  rw [EmbeddedBlowupSequence.inducedBlowups_center, EmbeddedBlowupSequence.totalCenter_eq,
    centerOffDetached_eq_top_of_smooth hres hB hrad D hsm t ht]
  exact AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty ..

theorem withoutIsoBlowups_length_eq_zero_of_smooth :
    ((D.toEmbeddedBlowupSequence $ canonicalPrincipalization hres hrad).inducedBlowups hbl).lengthWithoutIsoBlowups = 0 := by
  by_contra hne
  have h0 :=
    Nat.pos_of_ne_zero hne
  have h1 := SequenceOfBlowups.nontrivialIndex_lt_length _ h0
  have h2 := SequenceOfBlowups.center_nontrivialIndex_ne_top _ h0
  rw [EmbeddedBlowupSequence.inducedBlowups_length] at h1
  exact h2 $ toEmbeddedBlowupSequence_center_eq_top_of_smooth hres hB hrad D hsm hbl _ h1
end
end

section
variable (hA : IsFunctorialPrincipalization (canonicalPrincipalization hres hrad)) (hw : TransitionsAreBlowupsForEmbeddings (canonicalPrincipalization hres hrad)) (hsnc : NilIsStrictNormalCrossingsOfSmooth) {k : Type} [Field k] [CharZero k] {Y : Sch} [IsAffine Y] [IsReduced Y] {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY] [QuasiCompact pY] [LocallyOfFinitePresentation pY] (D : EmbeddingDatum k Y pY)
include hA hw hsnc
theorem centersLieOver_embeddedResolutionRuleOfPrincipalization :
    (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).CentersLieOver
      (↑(smoothLocusComplement pY) : Set ↥Y) := by
  let _a4 := canonicalPrincipalization hres hrad
  let _c0 := embeddedResolutionRuleOfPrincipalization _a4 hw k Y pY D
  intro i hi x hx
  by_contra hns
  let _a5 := sbPrj _c0 i x
  have hy : _a5 ∈
      (↑(smoothLocus pY) : Set ↥Y) := by
    by_contra h
    exact hns $ mpr_ (m22) h
  obtain ⟨W, hWopen, hW⟩ :=
    ((isClosedEmbedding D.emb).isInducing).isOpen_iff.mp
      (smoothLocus pY).isOpen
  let _a2 := D.emb _a5
  have hWy :
      _a2
        ∈ W := by
    have h2 :
        _a5 ∈
          preimage D.emb W := by
      rwa [hW]
    exact h2
  obtain ⟨U', hU'mem, hxU', hU'le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_basicOpen D.ambient)
      (show _a2
          ∈ (⟨W, hWopen⟩ : D.ambient.Opens) from hWy)
  obtain ⟨r, hr⟩ := hU'mem
  have hyV : _a5 ∈
      D.emb ⁻¹ᵁ D.ambient.basicOpen r := by
    have h3 :
        _a2
          ∈ D.ambient.basicOpen r := by
      rwa [hr]
    exact h3
  let _s0 := D.emb ⁻¹ᵁ D.ambient.basicOpen r
  have hVle : _s0 ≤
      smoothLocus pY := by
    intro z hz
    have h3 : D.emb z ∈ D.ambient.basicOpen r := hz
    rw [hr] at h3
    have h5 : z ∈ preimage D.emb W := hU'le h3
    rwa [hW] at h5
  have hVaff : IsAffine _s0.toScheme :=
    ((isAffineOpen_top D.ambient).basicOpen r).preimage D.emb
  let _a3 := opI _s0 ≫ pY
  have hsmV : Smooth _a3 :=
    smooth_io_comp_of_le_smoothLocus pY _ hVle
  have hqcV : QuasiCompact _a3 :=
    inferInstance
  let _a1 := restrictEmbeddingDatumBasicOpen D hsnc r
  have hlen0 : (embeddedResolutionRuleOfPrincipalization _a4 hw k
      _s0.toScheme
      _a3 _a1).length = 0 := by
    rw [embeddedResolutionRuleOfPrincipalization_apply, inducedBlowupsWithoutIso_eq_withoutIsoBlowups, withoutIsoBlowups_length]
    exact withoutIsoBlowups_length_eq_zero_of_smooth hres hB hrad _a1 hsmV _
  have hps := isPullbackSeq_of_smooth _a4 hA hw k Y
      _s0.toScheme pY
      _a3 D _a1
      (D.ambient.basicOpen r).i (smooth_opens_io (D.ambient.basicOpen r))
      _s0.i rfl
      (m226 D.emb (D.ambient.basicOpen r))
  obtain ⟨rh_, e, h1, h2, h3, h4, h5, h6, h7⟩ := hps
  have hmemrange :
      _a5 ∈
        range ⇑_s0.i := by
    rwa [AlgebraicGeometry.Scheme.Opens.range_ι]
  obtain ⟨x', hx'eq⟩ := hmemrange
  obtain ⟨z, hz1, hz2⟩ :=
    m198
      (f := opI _s0)
      (g := sbPrj _c0 i)
      x' x hx'eq
  let _a6 := m47 _s0.i $ sbPrj _c0 i
  let _a0 := spI (cmI (center _c0 i) _a6)
  have hex : ∃ w, w ∈
      _a0 := by
    refine ⟨z, ?_⟩
    have hmem : z ∈
        (↑_a0 : Set _) := by
      rw [support_comap]
      show _a6 z
          ∈ (↑(sbCtr _c0
                i).support : Set _)
      rwa [hz2]
    exact hmem
  obtain ⟨j, hj, -⟩ := mp_ (h4 i hi) hex
  rw [hlen0] at hj
  exact absurd hj $ Nat.not_lt_zero j

end
end

theorem affineCentersLieOverSingularLocus_principalizationWithRadicalCenters :
    AffineCentersLieOverSingularLocus principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters := by
  intro k _ _ Y pY _ _ _ _
  unfold FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.InducedCentersLieOverSingularLocus
  let _a0 := affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth k Y pY
  have key : ((_a0.toEmbeddedBlowupSequence $ canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme smoothSubschemeIdealIsRadical).inducedBlowups $ transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters k Y pY _).CentersLieOver (↑(smoothLocusComplement pY) : Set ↥Y) := by
    let hA := isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
      smoothSubschemeIdealIsRadical
      (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect)
    apply centersLieOver_of_withoutIsoBlowups
    have h := centersLieOver_embeddedResolutionRuleOfPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical hA transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters nilIsStrictNormalCrossingsOfSmooth _a0
    rwa [embeddedResolutionRuleOfPrincipalization_apply] at h
  rw [← AffineSpacePrincipalizationData.embeddedInducedBlowups_eq]
  let e := affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth k Y pY
  subst e
  exact key


theorem isStrongResolution_canonicalAffineResolutionRule (k : Type) [Field k] [CharZero k] Y
    p [IsAffine Y]
    [IsReduced Y] [LocallyOfFiniteType p]
    [QuasiCompact p] :
    IsStrongResolution k Y p $ canonicalAffineResolutionRule k Y p := by
  have hsmooth :=
    affineDetachedSmooth principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
  have hCen :=
    affineCentersLieOverSingularLocus_principalizationWithRadicalCenters
  show IsStrongResolution k Y p
    (affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters k Y p)
  exact isStrongResolution_blowupSequenceWithoutIsos_ofAffine principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    (affineStrictTransformEmptyAtLast_of_isFunctorialPrincipalization principalizationWithRadicalCenters
      isFunctorialPrincipalization_principalizationWithRadicalCenters affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth)
    hsmooth
    (affineSmoothLocusPreimageDenseInDetached principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    hCen
    (affineDetachedClopenInCenter principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedComponentsNotInBoundary principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedSingularPreimageEqBoundary_of_centersLieOverSing principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth (embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters) hsmooth
      embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters hCen)
    (affineCentersHaveStrictNormalCrossingsWithBoundary principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineAllLevelsSmooth principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineBoundaryInStrictNormalCrossingPosition principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictNormalCrossingsRestrictToClopen Blowup.blowupIsProper k Y p

theorem strongResolutionOfSingularitiesCharZero :
    StrongResolutionOfSingularitiesCharZero :=
  strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm principalizationWithRadicalCenters
    affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    isFunctorialPrincipalization_principalizationWithRadicalCenters
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters
    embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    closedEmbeddingsRelatedByAutomorphism
    isStrongResolution_canonicalAffineResolutionRule

end FunctorialResolution.EmbeddedResolution
end
end
end
