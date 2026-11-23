import Mathlib
import Bundle00
import Bundle01
import Bundle02
import Bundle03
import Bundle04
import Bundle05
import Bundle06
import Bundle07
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace CategoryTheory.Limits
open FunctorialResolution.Blowup (IsBlowupAlongIdealSheaf IsLocallyGeneratedByNonZeroDivisor StrictTransformIsBlowupOfClosedSubscheme blowup comap_le_strictTransform exceptionalIdeal exists_iso_pullback_coprod_desc_left exists_iso_pullback_coprod_desc_right isBlowupAlongIdealSheaf_id_top isLocallyGeneratedByNonZeroDivisor_comap_top isLocallyGeneratedByNonZeroDivisor_top ker_comp_coprod_inl_comap_inl ker_comp_coprod_inl_comap_inr noetherianSpace_subscheme)
open FunctorialResolution.EmbeddedResolution.BlowupSequenceData (append prepend_isoObjZero projectionToBase_congr projectionToBase_succ projectionToBase_zero toSequenceOfBlowups_blowupMorphism toSequenceOfBlowups_center toSequenceOfBlowups_isoObjZero toSequenceOfBlowups_schemeAt)
open Scheme.IdealSheafData (comap comapIso_hom_fst comap_comp comap_ideal_eq_map_appLE comap_mono comap_pow comap_top gc ker_subschemeι le_map_comap le_map_iff_comap_le le_radical map_mono mem_support_comap ne_top_of_mem_support radical_ideal subscheme subschemeMap_subschemeι subschemeι support support_comap support_eq_bot_iff support_top vanishingIdeal vanishingIdeal_ideal vanishingIdeal_support)
open FunctorialResolution.Blowup.blowup (isBlowupAlongIdealSheaf_proj proj)
open Set (compl_inter_self compl_union_self eq_univ_of_univ_subset image_preimage_eq_inter_range image_univ inter_eq_self_of_subset_left mem_image_of_mem mem_range_self mem_sUnion mem_univ nonempty_iff_ne_empty not_subset preimage preimage_mono range range_comp sUnion_eq_biUnion singleton_subset_iff subset_sUnion_of_mem subset_univ univ)
open List (map_nil prod_append prod_cons prod_nil range_succ sum_append sum_cons sum_nil)
open Ideal (gc_map_comap isPrime_bot isRadical_iff_quotient_reduced map_radical_of_surjective mem_bot radical_eq_iff)
open MvPolynomial (aeval aeval_rename aeval_unique algebraMap_eq rename)
open PrimeSpectrum (asIdeal isClosed_zeroLocus isRadical_vanishingIdeal mem_zeroLocus)
open Nat (add_le_add_left add_le_add_right add_zero exists_eq_add_of_le le_add_right le_induction le_of_succ_le le_succ le_succ_of_le lt_of_succ_le lt_succ_self mul_pos mul_zero not_lt_zero succ_le_of_lt succ_pos zero_le)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (blowupMorphism_eq_transitionMap center iso_hom_comp_projectionToBase projectionToBase projectionToBase_def transitionMapSucc transitionMap_comp_projectionToBase transitionMap_def transitionMap_self transitionMap_trans withoutIsoBlowups_isomorphic_self)
open TopologicalSpace.Opens (coe_bot coe_inf coe_sup coe_top mem_iSup)
open Iso (hom hom_inv_id inv inv_comp_eq inv_hom_id refl refl_hom symm_hom trans_hom)
open IsPullback (isoPullback_hom_fst isoPullback_hom_snd of_bot of_hasPullback of_horiz_isIso of_iso_pullback)
open Limits.pullback (condition hom_ext lift_fst lift_snd)
open Category (assoc comp_id id_comp)
open Scheme.Hom (app appIso_hom' appLE appTop isClosedEmbedding ker support_ker toImage_imageι)
open ULift (up)
open Sum (elim inl inr)
open FunctorialResolution.EmbeddedResolution (affineSpaceFin coordSubspaceIdeal_empty exists_chart_restrictIdeal_eq_coordIdeal one_le_orderAt_iff_mem_support orderAt orderAt_bot orderAt_comap_of_isOpenImmersion orderAt_eq_of_stalkIdeal_eq orderAt_eq_one_of_restrictIdeal_eq_coordIdeal restrictIdeal restrictIdeal_eq_comap_io stalkIdeal stalkIdeal_bot stalkIdeal_comap)
open TopologicalSpace (Closeds NoetherianSpace)
open IsClosedImmersion (isAffine_surjective_of_isAffine lift lift_fac of_isPreimmersion)
open Surjective (surj)
open Scheme (GSpecIso IdealSheafData exists_isAffineOpen_mem homeoOfIso)
open Scheme.Pullback (exists_preimage_pullback)
open Function (Surjective)
open LocallyOfFiniteType (isLocallyNoetherian)
open Fin (last lastCases)
open CommRingCat (ofHom)
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (toBlowupSequenceData toMarkedSequence_toSequenceOfBlowups)
open Iff (mp mpr)
open Scheme.Opens (toScheme ι)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (IsAdmissible boundary ideal scheme structMap)
section

namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
private theorem exists_affineOpen_mem (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1.1 := by
  have hx : x ∈ (⨆ U : affO X, (U : Opn X)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := mp_ mem_iSup hx
  exact ⟨U, hU⟩

theorem mem_orderAtLeastLocus_prod_map_of_forall (x : X)
    (g : ℕ → ISD X) (w : ℕ → ℕ) (h : ∀ j, x ∈ orderAtLeastLocus (g j) (w j)) (l : List ℕ) :
    x ∈ orderAtLeastLocus ((l.map g).prod) ((l.map w).sum) := by
  induction l with
  | nil =>
      simp [map_nil, prod_nil, sum_nil]
      rw [orderAtLeastLocus_zero]
      exact mem_univ x
  | cons a t ih =>
      simp [prod_cons, sum_cons]
      exact inter_orderAtLeastLocus_subset_orderAtLeastLocus_mul _ _ _ _ ⟨h a, ih⟩

theorem stalkIdeal_iSup_le_of_forall {ι : Type}
    (F : ι → ISD X) (x : X) (Jd : Ideal $ X.presheaf.stalk x)
    (h : ∀ i, stalkIdeal (F i) x ≤ Jd) : stalkIdeal (iSup F) x ≤ Jd := by
  obtain ⟨U, hxU0⟩ := exists_affineOpen_mem x
  have hxU := hxU0
  have hUeq : (iSup F).ideal U = ⨆ i, (F i).ideal U := by simp_all
  rw [stalkIdeal_eq_map_germ _ x U hxU, hUeq, (gc_map_comap _).l_iSup]
  refine iSup_le fun i => ?_
  rw [← stalkIdeal_eq_map_germ (F i) x U hxU]
  exact h i

theorem prod_map_range_pow_ite_eq (f : ℕ → ISD X) (s n : ℕ) :
    ((List.range $ n + 1).map fun j => f j ^ (if j = 0 then s else 0)).prod = f 0 ^ s := by
  induction n with
  | zero => simp
  | succ t ih =>
      rw [range_succ, m144, prod_append, ih]
      simp
end

section
variable (k : Type) [Field k]
theorem pow_le_and_le_tunedSheaf_of_isBlowupAlongIdealSheaf [CharZero k]
    [IsNoetherianRing k] {P P1 : Sch} (p : P ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p] (pi_ : P1 ⟶ P)
    (p1_ : P1 ⟶ Sp k) [LocallyOfFiniteType p1_] (hp1_ : p1_ = pi_ ≫ p)
    (Z : ISD P) (E : Bdy P) (hZ : HasStrictNormalCrossingsWith p Z E)
    (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (m s : ℕ) (A B : ISD P) (A' B' : ISD P1)
    (hA : A ≤ Z ^ m)
    (hA' : exceptionalIdeal pi_ Z ^ m * A' = comap A pi_)
    (hB' : exceptionalIdeal pi_ Z ^ (m * s) * B' = comap B pi_)
    (h1 : A ^ s ≤ B) (h2 : B ≤ tunedSheaf k p A m (m * s)) :
    A' ^ s ≤ B' ∧ B' ≤ tunedSheaf k p1_ A' m (m * s) := by
  let _a0 := p5 pi_ Z ^ (m * s)
  have := isLocallyNoetherian p1_
  have : LocallyOfFiniteType $ pi_ ≫ p := by simp_all
  have hF := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hpi_
  constructor
  refine hF.le_of_pow_mul_le_pow_mul (m * s) ?_
  have hcm : (cmI A pi_) ^ s ≤ cmI B pi_ := by
    rw [← comap_pow]
    exact comap_mono pi_ h1
  calc _a0 * A' ^ s
      = (p5 pi_ Z ^ m * A') ^ s := by rw [mul_pow, ← pow_mul]
    _ = (cmI A pi_) ^ s := by rw [hA']
    _ ≤ cmI B pi_ := hcm
    _ = _a0 * B' := sy_ hB'
  refine hF.le_of_pow_mul_le_pow_mul (m * s) ?_
  calc _a0 * B' = cmI B pi_ := hB'
    _ ≤ cmI (tunedSheaf k p A m $ m * s) pi_ := comap_mono pi_ h2
    _ ≤ _a0 *
          tunedSheaf k p1_ (controlledTransform pi_ Z A m hpi_ hA) m (m * s) :=
        comap_tunedSheaf_le_exceptionalIdeal_pow_mul k p pi_ p1_ hp1_ Z E hZ hpi_ A m hA $ m * s
    _ = _a0 * tunedSheaf k p1_ A' m (m * s) := by rw [eq_controlledTransform_of_mul_eq_comap pi_ Z A m hpi_ hA A' hA']

section
variable {X : Sch} (p : X ⟶ Sp k) [Smooth p] (E : Bdy X) (d : BlowupSequenceData X) (hiso : Smooth d.isoZero.hom) (hsnc : ∀ i, i < d.length → HasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) (d.boundaryFrom E i))
include hiso hsnc
theorem smooth_projectionToBase_comp_of_snc :
    ∀ i, i ≤ d.length → Smooth (d.projectionToBase i ≫ p) := by
  intro i
  induction i with
  | zero =>
      intro _
      have := hiso
      rw [p23]
      infer_instance
  | succ j ih =>
      intro hj
      have := ih $ le_of_succ_le hj
      have hb := smooth_comp_of_isBlowupAlongIdealSheaf (hsnc j hj) $ d.isBlowup j hj
      rwa [p43, assoc]

theorem locallyOfFiniteType_projectionToBase_comp_of_snc :
    ∀ i, i ≤ d.length → LocallyOfFiniteType (d.projectionToBase i ≫ p) := by
  intro i hi
  have := smooth_projectionToBase_comp_of_snc k p E d hiso hsnc i hi
  infer_instance
end
end

theorem sum_map_range_eq_sum_range (w : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map w).sum = ∑ j ∈ Finset.range n, w j := by
  induction n with
  | zero => simp
  | succ t ih =>
      rw [range_succ, m144, sum_append, ih, Finset.sum_range_succ]
      simp

section
variable (k : Type) [Field k]
section
variable [CharZero k] [IsNoetherianRing k] {X : Sch} (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] (I J : ISD X)
theorem orderAtLeastLocus_eq_of_pow_le_of_le_tunedSheaf m
    {s} (hs : 1 ≤ s) (h1 : I ^ s ≤ J) (h2 : J ≤ tunedSheaf k p I m (m * s)) :
    orderAtLeastLocus J (m * s) = orderAtLeastLocus I m := by
  refine m15 ?_ ?_
  have _i1 : orderAtLeastLocus (I ^ s) (m * s) = orderAtLeastLocus I m := by
    let A := I
    rw [mul_comm]
    exact orderAtLeastLocus_pow_mul k p A hs m
  rw [← _i1]
  exact orderAtLeastLocus_subset_of_le_ideal h1 $ m * s
  have _i3 : orderAtLeastLocus I m ⊆ orderAtLeastLocus (tunedSheaf k p I m $ m * s) (m * s) := by
    let A := I
    intro x hx
    rw [mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow, tunedSheaf_eq_iSup]
    refine stalkIdeal_iSup_le_of_forall _ x _ ?_
    rintro ⟨c, hc⟩
    refine mp_ (mem_orderAtLeastLocus_iff_stalkIdeal_le_maximalIdeal_pow _ (m * s) x) ?_
    have key := mem_orderAtLeastLocus_prod_map_of_forall x (fun j => derivIdealSheafIterate k p j A ^ c j)
        (fun j => c j * (m - j))
        (fun j => orderAtLeastLocus_subset_orderAtLeastLocus_pow _ _ _
          (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p A j m hx)) $ m127 m
    refine orderAtLeastLocus_subset_of_le _ ?_ key
    rw [sum_map_range_eq_sum_range]
    exact le_trans hc $ le_of_eq $ Finset.sum_congr rfl fun j _ => Nat.mul_comm _ _
  exact fun x hx => orderAtLeastLocus_subset_of_le_ideal h2 (m * s)
    (_i3 hx)

theorem orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence m s
    (hs : 1 ≤ s) (h1 : I ^ s ≤ J) (h2 : J ≤ tunedSheaf k p I m (m * s))
    E (d : BlowupSequenceData X)
    (hiso : Smooth d.isoZero.hom)
    (hft : ∀ i, i ≤ d.length → LocallyOfFiniteType (d.projectionToBase i ≫ p))
    (hsnc : ∀ i, i < d.length → HasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) (d.boundaryFrom E i))
    (hord : ∀ i, i < d.length →
      orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m →
      (support (d.center i) : CSet (d.obj i)) ⊆ orderAtLeastLocus (d.controlledTransform I m i) m) :
    (∀ i, i ≤ d.length →
        orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m) ∧
    (∀ i, i < d.length → ∃ B : IdealSheafData (d.obj (i + 1)),
        exceptionalIdeal (d.map i) (d.center i) ^ m * B = comap (d.controlledTransform I m i) (d.map i)) ∧
    (∀ i, i < d.length → ∃ B : IdealSheafData (d.obj (i + 1)),
        exceptionalIdeal (d.map i) (d.center i) ^ (m * s) * B =
          comap (d.controlledTransform J (m * s) i) (d.map i)) := by
  let _a4 := m * s
  have hsm :=
    smooth_projectionToBase_comp_of_snc k p E d hiso hsnc
  have key : ∀ i, i ≤ d.length →
      (d.controlledTransform I m i) ^ s ≤ d.controlledTransform J (m * s) i ∧
      ∀ [_hq : LocallyOfFiniteType (d.projectionToBase i ≫ p)],
        d.controlledTransform J (m * s) i ≤
          tunedSheaf k (d.projectionToBase i ≫ p) (d.controlledTransform I m i) m (m * s) := by
    intro i
    induction i with
    | zero =>
        intro _
        constructor
        simp only [p53]
        rw [← comap_pow]
        exact comap_mono _ h1
        intro hq0
        have := hq0
        have := hiso
        simp only [p53]
        rw [← comap_tunedSheaf_of_smooth k p d.isoZero.hom (d.projectionToBase 0 ≫ p) rfl I m (m * s)]
        exact comap_mono _ h2
    | succ j ih =>
        intro hj
        have hj' := hj
        have hjle := le_of_succ_le hj
        obtain ⟨ih1, ih2⟩ := ih hjle
        have := hsm j hjle
        have := hft j hjle
        have := hft (j + 1) hj
        have hcosj :=
          orderAtLeastLocus_eq_of_pow_le_of_le_tunedSheaf k (d.projectionToBase j ≫ p) _ _ m hs ih1 ih2
        have hordj := hord j hj' hcosj
        let _a8 := d.boundaryFrom E j
        let _a9 := hsnc j hj'
        have hAZ :=
          le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase j ≫ p) (d.center j) _ _a8 _a9 m hordj
        let _a0 := d.controlledTransform J (m * s) j
        have hBZ : _a0 ≤ d.center j ^ _a4 := by
          refine le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase j ≫ p) (d.center j) _ _a8
            _a9 (m * s) ?_
          rwa [hcosj]
        have :=
          isLocallyNoetherian (d.projectionToBase (j + 1) ≫ p)
        let _a5 := d.controlledTransform I m j
        let _a10 := d.isBlowup j hj'
        obtain ⟨A1, hA1, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map j) (d.center j)
          _a5 m _a10 hAZ
        obtain ⟨B1, hB1, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map j) (d.center j)
          _a0 (m * s) _a10 hBZ
        have hp1 : d.projectionToBase (j + 1) ≫ p = d.map j ≫ (d.projectionToBase j ≫ p) := by simp_all
        obtain ⟨r1, r2⟩ := pow_le_and_le_tunedSheaf_of_isBlowupAlongIdealSheaf k (d.projectionToBase j ≫ p) (d.map j)
          (d.projectionToBase (j + 1) ≫ p) hp1
          (d.center j) _a8 _a9 _a10 m s
          _a5 _a0 (d.controlledTransform I m (j + 1))
          (d.controlledTransform J (m * s) $ j + 1) hAZ (d.pow_exceptionalIdeal_mul_controlledTransform_succ I m j ⟨A1, hA1⟩) (d.pow_exceptionalIdeal_mul_controlledTransform_succ J (m * s) j ⟨B1, hB1⟩) ih1 ih2
        refine ⟨r1, ?_⟩
        intro _
        exact r2
  have hcos : ∀ i, i ≤ d.length →
      orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m := by
    intro i hi
    have := hsm i hi
    have := hft i hi
    let _a11 := key i hi
    exact orderAtLeastLocus_eq_of_pow_le_of_le_tunedSheaf k (d.projectionToBase i ≫ p) _ _ m hs
      _a11.1 _a11.2
  have hdiv : ∀ i, i < d.length →
      (d.controlledTransform I m i ≤ d.center i ^ m) ∧
        (d.controlledTransform J (m * s) i ≤ d.center i ^ _a4) := by
    intro i hi
    have := hsm i $ le_of_succ_le hi
    have hordi := hord i hi $ hcos i (le_of_succ_le hi)
    constructor
    exact le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) _ (d.boundaryFrom E i) (hsnc i hi) m hordi
    refine le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) _ (d.boundaryFrom E i)
      (hsnc i hi) (m * s) ?_
    rwa [hcos i (le_of_succ_le hi)]
  refine ⟨hcos, ?_, ?_⟩
  intro i hi
  have := hft (i + 1) hi
  have :=
    isLocallyNoetherian (d.projectionToBase (i + 1) ≫ p)
  obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map i) (d.center i)
    (d.controlledTransform I m i) m (d.isBlowup i hi) (hdiv i hi).1
  exact ⟨B, hB⟩
  intro i hi
  have := hft (i + 1) hi
  have :=
    isLocallyNoetherian (d.projectionToBase (i + 1) ≫ p)
  obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map i) (d.center i)
    (d.controlledTransform J (m * s) i) (m * s) (d.isBlowup i hi) (hdiv i hi).2
  exact ⟨B, hB⟩
end
end

theorem isMarked_iff_of_pow_le_of_le_tunedSheaf : IsMarkedIffOfPowLeOfLeTunedSheaf := by
  intro k hk1 hk2 hk3 X p hp1 hp2 I m _hm _hmax s hs J h1 h2 E d
  have hiso : Smooth $ bdIzH d := inferInstance
  constructor
  constructor
  intro hI
  obtain ⟨hc, -, hdivJ⟩ := orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence k p I J m s hs h1 h2 E d
    hiso (locallyOfFiniteType_projectionToBase_comp_of_snc k p E d hiso hI.center_snc) hI.center_snc fun i hi _ => hI.center_order i hi
  exact { divisible := hdivJ
          center_order := fun i hi => by
            rw [hc i $ le_of_succ_le hi]
            exact hI.center_order i hi
          center_smooth := hI.center_smooth
          center_snc := hI.center_snc }
  intro hJ
  obtain ⟨hc, hdivI, -⟩ := orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence k p I J m s hs h1 h2 E d
    hiso (locallyOfFiniteType_projectionToBase_comp_of_snc k p E d hiso hJ.center_snc) hJ.center_snc
    (fun i hi heq => by
      rw [← heq]
      exact hJ.center_order i hi)
  exact { divisible := hdivI
          center_order := fun i hi => by
            rw [← hc i $ le_of_succ_le hi]
            exact hJ.center_order i hi
          center_smooth := hJ.center_smooth
          center_snc := hJ.center_snc }
  intro hI i hi
  obtain ⟨hc, -, -⟩ := orderAtLeastLocus_eq_and_exceptionalIdeal_dvd_of_blowupSequence k p I J m s hs h1 h2 E d
    hiso (locallyOfFiniteType_projectionToBase_comp_of_snc k p E d hiso hI.center_snc) hI.center_snc fun i hi _ => hI.center_order i hi
  exact hc i hi

theorem isMarked_iff_balanced_tunedSheaf : IsMarkedIffBalancedTunedSheaf := by
  intro k hk1 hk2 hk3 X p hp1 hp2 I m hm hmax E d
  obtain ⟨r, s, hr, hre, hs, hms⟩ : ∃ r s, m - 1 ≤ r ∧ tuningExponent m = r * lcmUpTo m ∧ 1 ≤ s ∧ tuningExponent m = m * s := by
    rcases m63 m 2 with h | h
    have hm1 : m = 1 := by omega
    subst hm1
    refine ⟨1, 1, by omega, ?_, le_rfl, ?_⟩
    rw [tuningExponent_one, lcmUpTo_one]
    rw [tuningExponent_one]
    obtain ⟨t, ht⟩ := dvd_lcmUpTo m m (by omega) le_rfl
    have htpos : 0 < t := by
      rcases m73 t with h0 | h0
      rw [h0, mul_zero] at ht
      have hpos := lcmUpTo_pos m
      omega
      exact h0
    refine ⟨m - 1, (m - 1) * t, le_rfl, tuningExponent_of_two_le h, ?_, ?_⟩
    have : 0 < (m - 1) * t := Nat.mul_pos (by omega) htpos
    omega
    rw [tuningExponent_of_two_le h, ht]
    ring
  have hWe : balancedTunedSheaf k p I m = tunedSheaf k p I m (m * s) := by rw [balancedTunedSheaf_eq, hms]
  have h1 : I ^ s ≤ balancedTunedSheaf k p I m := by
    rw [hWe]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    let _a0 := m65 $ m' + 1
    have hsum : (m' + 1) * s ≤
        ∑ j ∈ _a0, (m' + 1 - j) * (if j = 0 then s else 0) := by
      have h := Finset.sum_eq_single_of_mem (s := _a0)
        (f := fun j => (m' + 1 - j) * (if j = 0 then s else 0)) 0
        (Finset.mem_range.mpr $ succ_pos m')
        (fun b _ hb => by simp [hb])
      rw [h]
      simp
    have hle := le_iSup
      (fun c : {c : ℕ → ℕ // (m' + 1) * s ≤ ∑ j ∈ _a0, (m' + 1 - j) * c j} =>
        ((m127 $ m' + 1).map fun j => derivIdealSheafIterate k p j I ^ (c.1 j)).prod)
      ⟨fun j => if j = 0 then s else 0, hsum⟩
    rw [tunedSheaf_eq_iSup]
    refine le_trans (le_of_eq ?_) hle
    have := prod_map_range_pow_ite_eq (fun j => derivIdealSheafIterate k p j I) s m'
    rw [this]
    simp
  have hmarked := isMarked_iff_of_pow_le_of_le_tunedSheaf k X p I m hm hmax s hs
    (balancedTunedSheaf k p I m) h1 (le_of_eq hWe) E d
  rw [← hms] at hmarked
  have he1 : 1 ≤ tuningExponent m := by
    rw [hms]
    exact mul_pos hm hs
  refine ⟨an1 hmarked, an2 hmarked, ?_, ?_⟩
  have h5 := isMaxContactInvariantTunedSheaf k X p I m hm hmax
    (tuningExponent m) he1
  rwa [balancedTunedSheaf_eq]
  have h8 := isDerivBalanced_tunedSheaf_mul_lcmUpTo k X p I m hm hmax r hr
  rw [← hre] at h8
  rwa [balancedTunedSheaf_eq]

theorem tunedSheafProperties_of_succ_le_of_mul_le : TunedSheafProperties where
  isMarked_tuned_iff := isMarked_iff_balanced_tunedSheaf
  derivIdealSheafIter_pred_tunedSheaf := maxContactIdealTunedSheafEq
  derivIdealSheafIter_mul_derivIdealSheaf_le_tunedSheaf := isMaxContactInvariantTunedSheaf
  derivIdealSheafIter_tunedSheaf_pow_le := isDerivBalanced_tunedSheaf_mul_lcmUpTo
  coSupport_tunedSheaf_eq_and_orderLE := orderAtLeastLocus_tunedSheaf_eq_and_order_le

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

section
variable {W Y} (g : W ⟶ Y) (t : SequenceOfBlowups W) (i : ℕ)
abbrev pullbackFstSchemeAt : Sch :=
  pullback (pullback.fst g g) $ projectionToBase t i

abbrev pullbackSndSchemeAt : Sch :=
  pullback (pullback.snd g g) $ projectionToBase t i
end

private theorem flat_fst_of_isPullback {A B C D : Sch} {p : A ⟶ B} {q : A ⟶ C}
    {f : B ⟶ D} {h : C ⟶ D} (H : IsPullback p q f h) [Flat h] :
    Flat p :=
  m122
    (P := @Flat) H.flip inferInstance

theorem isPullback_iso_hom_comp {P P' A B C : Sch} {pf : P' ⟶ A} {ps : P' ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (H : IsPullback pf ps f g) (e : P ≅ P') :
    IsPullback (hom e ≫ pf) (hom e ≫ ps) f g := by
  have E : IsPullback e.hom (isoH e ≫ ps) ps $ 𝟙 B :=
    of_horiz_isIso ⟨by simp⟩
  have h := E.paste_horiz H
  rwa [id_comp] at h

section
variable {W X : Sch} {t : SequenceOfBlowups W} {n : ℕ} (hn : n < t.length) {ga_ : t.schemeAt n ⟶ X} (hflat : Flat ga_) (hc : comap ((center t n).map ga_) ga_ = center t n)
include hn hflat hc
theorem exists_isPullback_blowup_proj_map_center :
    ∃ q : t.schemeAt (n + 1) ⟶ blowup ((center t n).map ga_),
      q ≫ proj ((center t n).map ga_) = transitionMapSucc t n ≫ ga_ ∧
        IsPullback q (transitionMapSucc t n) (proj $ (center t n).map ga_) ga_ := by
  refine (p46 $ (center t n).map ga_).exists_isPullback_of_flat ga_ ?_
  rw [hc]
  exact t.isBlowupAlongIdealSheaf_blowupMorphism n hn

def toBlowupOfMapCenter :
    t.schemeAt (n + 1) ⟶ blowup ((center t n).map ga_) :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose

theorem toBlowupOfMapCenter_comp_proj :
    toBlowupOfMapCenter hn hflat hc ≫ proj ((center t n).map ga_) = transitionMapSucc t n ≫ ga_ :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose_spec.1

theorem isPullback_toBlowupOfMapCenter :
    IsPullback (toBlowupOfMapCenter hn hflat hc) (transitionMapSucc t n)
      (proj $ (center t n).map ga_) ga_ :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose_spec.2
end

structure DescendedBlowupData {W Y : Sch} (g : W ⟶ Y) (t : SequenceOfBlowups W) (n : ℕ)
    {X : Sch} (pi_ : X ⟶ Y) (ga_ : t.schemeAt n ⟶ X)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1)) where
  total : Sch
  totalStruct : total ⟶ Y
  down : total ⟶ X
  totalCenter : ISD X
  totalComparison : t.schemeAt (n + 1) ⟶ total
  center_comap : comap totalCenter ga_ = center t n
  isBlowup_down : IsBlowupAlongIdealSheaf down totalCenter
  isPullback_sq : IsPullback totalComparison (transitionMapSucc t n) down ga_
  isPullback_base : IsPullback totalComparison (projectionToBase t $ n + 1) totalStruct g
  hom_comparison :
    hom e' ≫ pullback.snd (pullback.snd g g) (projectionToBase t $ n + 1) ≫ totalComparison
      = pullback.snd (pullback.fst g g) (projectionToBase t $ n + 1) ≫ totalComparison

def descendedBlowupData {W Y : Sch} (g : W ⟶ Y) [Flat g]
    [QuasiCompact g] (t : SequenceOfBlowups W) {n : ℕ} (hn : n < t.length)
    {X : Sch} (pi_ : X ⟶ Y) (ga_ : t.schemeAt n ⟶ X)
    (hsq : IsPullback ga_ (projectionToBase t n) pi_ g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1))
    (hee : e'.hom ≫ t.pullbackTransitionMap (pullback.snd g g) (le_succ n)
      = t.pullbackTransitionMap (pullback.fst g g) (le_succ n) ≫ e.hom)
    (hcenter : ((center t n).comap $ pullback.snd (pullback.snd g g) $ projectionToBase t n).comap e.hom
      = (center t n).comap (pullback.snd (pullback.fst g g) $ projectionToBase t n))
    (hbase : e.hom ≫ pullback.fst (pullback.snd g g) (projectionToBase t n)
      = pullback.fst (pullback.fst g g) (projectionToBase t n))
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (projectionToBase t n) ≫ ga_
      = pullback.snd (pullback.fst g g) (projectionToBase t n) ≫ ga_) :
    DescendedBlowupData g t n pi_ ga_ e' :=
  haveI hfl : Flat ga_ := flat_fst_of_isPullback hsq
  haveI _hqc : QuasiCompact ga_ := quasiCompact_of_isPullback hsq.flip
  have hc : ((center t n).map ga_).comap ga_ = center t n :=
    by
      let _a0 := pullback.fst (pullback.fst g g) $ projectionToBase t n
      have hpbSnd : IsPullback (e.hom ≫ pullback.snd (pullback.snd g g) (projectionToBase t n))
          _a0 (projectionToBase t n) $ pullback.snd g g := by
        have h := isPullback_iso_hom_comp
          (of_hasPullback (pullback.snd g g) $ projectionToBase t n).flip e
        rwa [hbase] at h
      have Big := hpbSnd.paste_vert (of_hasPullback g g).flip
      have hcond : _a0 ≫ pullback.fst g g
          = pullback.snd (pullback.fst g g) (projectionToBase t n) ≫ projectionToBase t n := pullback.condition
      rw [hcond, ← hsq.w] at Big
      have comm := hgamma
      rw [← assoc] at comm
      have key :=
        of_bot Big comm hsq
      refine comap_map_eq_self_of_isPullback ga_ key (center t n) ?_
      rw [comap_comp]
      exact hcenter
  { total := blowup ((center t n).map ga_)
    totalStruct := proj ((center t n).map ga_) ≫ pi_
    down := proj $ (center t n).map ga_
    totalCenter := (center t n).map ga_
    totalComparison := toBlowupOfMapCenter hn hfl hc
    center_comap := hc
    isBlowup_down := isBlowupAlongIdealSheaf_proj $ (center t n).map ga_
    isPullback_sq := isPullback_toBlowupOfMapCenter hn hfl hc
    isPullback_base := by
      let hflat := hfl
      have h := (isPullback_toBlowupOfMapCenter hn hflat hc).paste_vert hsq
      rwa [← t.projectionToBase_succ n] at h
    hom_comparison := by
      let hflat := hfl
      let _hsq := hsq
      let _c0 := projectionToBase t $ n + 1
      let _c1 := pullback.fst g g
      let _c2 := pullback.snd g g
      let _c3 := (center t n).map ga_
      have := hflat
      have hfst :=
        flat_fst_of_isPullback $ of_hasPullback g g
      have hdc :=
        flat_fst_of_isPullback $ isPullback_toBlowupOfMapCenter hn hflat hc
      have hsnd1 : pullback.snd _c1 _c0 ≫ transitionMapSucc t n
          = t.pullbackTransitionMap _c1 (le_succ n)
            ≫ pullback.snd _c1 (projectionToBase t n) :=
        (t.pullbackTransitionMap_snd _c1 $ le_succ n).symm
      have hsnd2 : pullback.snd _c2 _c0 ≫ transitionMapSucc t n
          = t.pullbackTransitionMap _c2 (le_succ n)
            ≫ pullback.snd _c2 (projectionToBase t n) :=
        (t.pullbackTransitionMap_snd _c2 $ le_succ n).symm
      have hsnd1' : pullback.snd _c1 _c0 ≫ transitionMapSucc t n ≫ ga_
          = t.pullbackTransitionMap _c1 (le_succ n)
            ≫ pullback.snd _c1 (projectionToBase t n) ≫ ga_ := by
        rw [← assoc, ← assoc, hsnd1]
      have hsnd2' : pullback.snd _c2 _c0 ≫ transitionMapSucc t n ≫ ga_
          = t.pullbackTransitionMap _c2 (le_succ n)
            ≫ pullback.snd _c2 (projectionToBase t n) ≫ ga_ := by
        rw [← assoc, ← assoc, hsnd2]
      have hk : IsLocallyGeneratedByNonZeroDivisor $ _c3.comap
          (pullback.snd _c1 _c0 ≫
            toBlowupOfMapCenter hn hflat hc ≫ proj _c3) := by
        rw [comap_comp, comap_comp]
        exact Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat
          (Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat (isBlowupAlongIdealSheaf_proj _c3).1
            (toBlowupOfMapCenter hn hflat hc)) _
      refine Blowup.IsBlowupAlongIdealSheaf.hom_ext_of_comp_eq (isBlowupAlongIdealSheaf_proj _c3) hk ?_ ?_
      · simp only [assoc]
        rw [toBlowupOfMapCenter_comp_proj hn hflat hc, hsnd2', hsnd1', ← assoc, hee,
          assoc, hgamma]
      · rw [assoc] }

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite


namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowups

variable {X : Sch}

@[simp]
theorem transitionMap_self_eq_id (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i) :
    s.transitionMap h = 𝟙 (s.schemeAt i) := by
  rw [s.transitionMap_def, show ((homOfLE h).op : op i ⟶ op i) = 𝟙 (op i) from rfl, s.tower.map_id]

instance instIsIsoStructMapZero (s : SequenceOfBlowups X) : IsIso $ projectionToBase s 0 := by
  rw [s.projectionToBase_zero]
  infer_instance

section
variable (s : SequenceOfBlowups X) {X' : Sch} (ph_ : X' ⟶ X)
section
variable {i i' : ℕ} (h : i ≤ i')
@[reassoc, simp]
theorem pullbackTransitionMap_comp_fst :
    s.pullbackTransitionMap ph_ h ≫ pullback.fst ph_ (projectionToBase s i) = pullback.fst ph_ (projectionToBase s i') :=
  s.pullbackTransitionMap_fst ph_ h

@[reassoc, simp]
theorem pullbackTransitionMap_comp_snd :
    s.pullbackTransitionMap ph_ h ≫ pullback.snd ph_ (projectionToBase s i) =
      pullback.snd ph_ (projectionToBase s i') ≫ s.transitionMap h :=
  s.pullbackTransitionMap_snd ph_ h
end

def baseChangeTower : ℕᵒᵖ ⥤ Sch where
  obj i := pullback ph_ $ projectionToBase s i.unop
  map {_ _} f := s.pullbackTransitionMap ph_ $ leOfHom f.unop
  map_id i := by
    let h := leOfHom (𝟙 i).unop
    refine pullback.hom_ext ?_ ?_
    · rw [s.pullbackTransitionMap_fst, id_comp]
    · rw [s.pullbackTransitionMap_snd, s.transitionMap_self_eq_id, comp_id, id_comp]
  map_comp {_ _ _} f g :=
    by
      let hba := leOfHom f.unop
      let hcb := leOfHom g.unop
      let hca := leOfHom (f ≫ g).unop
      refine pullback.hom_ext ?_ ?_
      · rw [s.pullbackTransitionMap_fst, assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
      · rw [s.pullbackTransitionMap_snd, assoc, s.pullbackTransitionMap_snd, ← assoc,
          s.pullbackTransitionMap_snd, assoc, s.transitionMap_trans]

@[simp]
theorem baseChangeTower_obj (i : ℕ) :
    (s.baseChangeTower ph_).obj (op i) = pullback ph_ (projectionToBase s i) := rfl

@[simp]
theorem baseChangeTower_map {i i' : ℕ}
    (h : i ≤ i') :
    (s.baseChangeTower ph_).map (homOfLE h).op = s.pullbackTransitionMap ph_ h := rfl

theorem isIso_pullback_fst_projectionToBase_zero :
    IsIso $ pullback.fst ph_ $ projectionToBase s 0 := by
  have hcomm : (𝟙 X') ≫ ph_ = (ph_ ≫ inv (sbPrj s 0)) ≫ sbPrj s 0 := by
    simp
  refine ⟨pullback.lift (𝟙 X') (ph_ ≫ inv (sbPrj s 0)) hcomm, ?_, ?_⟩
  refine pullback.hom_ext ?_ ?_
  rw [assoc, pullback.lift_fst, comp_id, id_comp]
  rw [assoc, pullback.lift_snd, id_comp, ← assoc,
    pullback.condition, assoc, m118, comp_id]
  rw [pullback.lift_fst]
end

instance instIsIsoPullbackFstStructMapZero (s : SequenceOfBlowups X) {X' : Sch} (ph_ : X' ⟶ X) :
    IsIso $ pullback.fst ph_ $ projectionToBase s 0 :=
  s.isIso_pullback_fst_projectionToBase_zero ph_

section
variable (s : SequenceOfBlowups X) {X'} (ph_ : X' ⟶ X)
def baseChangeTowerObjZeroIso :
    (s.baseChangeTower ph_).obj (op 0) ≅ X' :=
  @asIso Sch _ _ _ (pullback.fst ph_ $ projectionToBase s 0) $ s.isIso_pullback_fst_projectionToBase_zero ph_

@[simp]
theorem baseChangeTowerObjZeroIso_hom :
    hom (s.baseChangeTowerObjZeroIso ph_) = pullback.fst ph_ (projectionToBase s 0) := rfl

theorem isPullback_pullbackTransitionMap (i : ℕ) :
    IsPullback (pullback.snd ph_ $ projectionToBase s $ i + 1) (s.pullbackTransitionMap ph_ $ le_succ i)
      (transitionMapSucc s i) $ pullback.snd ph_ $ projectionToBase s i := by
  let _a0 := sbPrj s $ i + 1
  have hsnd : pullback.snd ph_ _a0 ≫ transitionMapSucc s i
      = s.pullbackTransitionMap ph_ (le_succ i) ≫ pullback.snd ph_ (projectionToBase s i) := by
    rw [s.pullbackTransitionMap_snd, s.blowupMorphism_eq_transitionMap]
  have sq : IsPullback (pullback.snd ph_ _a0)
      (s.pullbackTransitionMap ph_ (le_succ i) ≫ pullback.fst ph_ (projectionToBase s i))
      (transitionMapSucc s i ≫ projectionToBase s i) ph_ := by
    rw [s.pullbackTransitionMap_fst ph_ $ le_succ i, s.blowupMorphism_eq_transitionMap, s.transitionMap_comp_projectionToBase]
    exact (of_hasPullback ph_ _a0).flip
  exact sq.of_bot hsnd $ (of_hasPullback ph_ $ sbPrj s i).flip

section
variable [Flat ph_]
def baseChange :
    SequenceOfBlowups X' where
  length := s.length
  tower := s.baseChangeTower ph_
  isoZero := s.baseChangeTowerObjZeroIso ph_
  center i := comap (center s i) $ pullback.snd ph_ $ projectionToBase s i
  isBlowup i hi := (s.isBlowupAlongIdealSheaf_blowupMorphism i hi).of_isPullback_of_flat (pullback.snd ph_ $ projectionToBase s i)
    (s.isPullback_pullbackTransitionMap ph_ i)

@[simp]
theorem baseChange_length : (s.baseChange ph_).length = s.length := rfl

@[simp]
theorem baseChange_schemeAt (i : ℕ) :
    (s.baseChange ph_).schemeAt i = pullback ph_ (projectionToBase s i) := rfl

@[simp]
theorem baseChange_blowupMorphism (i : ℕ) :
    transitionMapSucc (s.baseChange ph_) i = s.pullbackTransitionMap ph_ (le_succ i) := rfl

@[simp]
theorem baseChange_isoObjZero_hom :
    (s.baseChange ph_).isoZero.hom = pullback.fst ph_ (projectionToBase s 0) := rfl

@[simp]
theorem baseChange_center (i : ℕ) :
    center (s.baseChange ph_) i = comap (center s i) (pullback.snd ph_ $ projectionToBase s i) := rfl
end
end

end SequenceOfBlowups

theorem isStrictPullbackSequenceOfBlowups_baseChange {X X' : Sch} (s : SequenceOfBlowups X) (ph_ : X' ⟶ X)
    [Flat ph_] : IsStrictPullbackBlowupSeq ph_ (s.baseChange ph_) s := by
  refine ⟨rfl, fun i _ => pullback.snd ph_ $ sbPrj s i, ?_, ?_, ?_⟩
  show pullback.snd ph_ (sbPrj s 0) ≫ s.isoZero.hom
    = pullback.fst ph_ (sbPrj s 0) ≫ ph_
  rw [← s.projectionToBase_zero, pullback.condition]
  intro i _
  exact s.isPullback_pullbackTransitionMap ph_ i
  intro i _
  rfl


theorem baseChange_projectionToBase_eq_fst {X X' : Sch} (s : SequenceOfBlowups X)
    (ph_ : X' ⟶ X) [Flat ph_] (i : ℕ) :
    projectionToBase (s.baseChange ph_) i = pullback.fst ph_ (projectionToBase s i) := by
  induction i with
  | zero =>
    rw [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.baseChange_isoObjZero_hom]
  | succ n ih =>
    let _a0 := s.baseChange ph_
    have hb : transitionMapSucc _a0 n ≫ projectionToBase _a0 n
        = projectionToBase _a0 (n + 1) := by
      rw [blowupMorphism_eq_transitionMap]
      exact transitionMap_comp_projectionToBase _ _
    rw [← hb, ih, SequenceOfBlowups.baseChange_blowupMorphism]
    exact SequenceOfBlowups.pullbackTransitionMap_comp_fst s ph_ _

structure SequenceOfBlowupsDescentDatum {W Y : Sch} (g : W ⟶ Y) (t : SequenceOfBlowups W) where
  iso : ∀ i : ℕ, i ≤ t.length → (pullbackFstSchemeAt g t i ≅ pullbackSndSchemeAt g t i)
  comp_fst : ∀ i hi,
    hom (iso i hi) ≫ pullback.fst (pullback.snd g g) (projectionToBase t i)
      = pullback.fst (pullback.fst g g) (projectionToBase t i)
  center_comap : ∀ (i : ℕ) (hi : i < t.length),
    comap (comap (center t i) $ pullback.snd (pullback.snd g g) $ projectionToBase t i)
        (iso i hi.le).hom
      = comap (center t i) (pullback.snd (pullback.fst g g) $ projectionToBase t i)
  comp_step : ∀ i hi,
    hom (iso (i + 1) $ succ_le_of_lt hi) ≫ t.pullbackTransitionMap (pullback.snd g g) (le_succ i)
      = t.pullbackTransitionMap (pullback.fst g g) (le_succ i) ≫ hom (iso i hi.le)

structure DescendedSchemeData {W Y : Sch} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) (n : ℕ) where
  X : Sch
  str : X ⟶ Y
  gam : t.schemeAt n ⟶ X
  hsq : n ≤ t.length → IsPullback gam (projectionToBase t n) str g
  hgam : ∀ hn : n ≤ t.length,
    hom (D.iso n hn) ≫ pullback.snd (pullback.snd g g) (projectionToBase t n) ≫ gam
      = pullback.snd (pullback.fst g g) (projectionToBase t n) ≫ gam

structure DescendedBlowupOfSchemeData {W Y : Sch} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) (n : ℕ) (P : DescendedSchemeData g t D n) where
  next : DescendedSchemeData g t D $ n + 1
  down : next.X ⟶ P.X
  cen : P.X.IdealSheafData
  hblow : n < t.length → IsBlowupAlongIdealSheaf down cen
  hpb : n < t.length → IsPullback next.gam (transitionMapSucc t n) down P.gam
  hcen : n < t.length → center t n = comap cen P.gam

section
variable {W Y : Sch} (g : W ⟶ Y)
def descendedSchemeDataZero (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) : DescendedSchemeData g t D 0 where
  X := Y
  str := 𝟙 Y
  gam := projectionToBase t 0 ≫ g
  hsq := fun _ => (of_horiz_isIso ⟨by simp⟩).flip
  hgam := fun h0 => by
    have c1 : pullback.fst (pullback.fst g g) (projectionToBase t 0) ≫ pullback.fst g g
        = pullback.snd (pullback.fst g g) (projectionToBase t 0) ≫ projectionToBase t 0 := pullback.condition
    have c2 : pullback.fst (pullback.snd g g) (projectionToBase t 0) ≫ pullback.snd g g
        = pullback.snd (pullback.snd g g) (projectionToBase t 0) ≫ projectionToBase t 0 := pullback.condition
    have c3 : pullback.fst g g ≫ g = pullback.snd g g ≫ g := pullback.condition
    have hf := D.comp_fst 0 h0
    calc (D.iso 0 h0).hom ≫ pullback.snd (pullback.snd g g) (projectionToBase t 0) ≫
          (projectionToBase t 0 ≫ g)
        = (hom (D.iso 0 h0) ≫ pullback.snd (pullback.snd g g) (projectionToBase t 0) ≫
            projectionToBase t 0) ≫ g := by
          simp only [assoc]
      _ = (pullback.fst (pullback.fst g g) (projectionToBase t 0) ≫ pullback.snd g g) ≫ g := by
          rw [← c2, ← assoc, hf]
      _ = (pullback.fst (pullback.fst g g) (projectionToBase t 0) ≫ pullback.fst g g) ≫ g := by
          rw [assoc, assoc, c3]
      _ = pullback.snd (pullback.fst g g) (projectionToBase t 0) ≫ (projectionToBase t 0 ≫ g) := by
          rw [c1, assoc]

section
variable [Flat g] [QuasiCompact g] (t : SequenceOfBlowups W)
section
variable (D : SequenceOfBlowupsDescentDatum g t)
include D
section
variable (n : ℕ)
def descendedBlowupAt (P : DescendedSchemeData g t D n) : DescendedBlowupOfSchemeData g t D n P :=
  if hn : n < t.length then
    let S := descendedBlowupData g t hn P.str P.gam (P.hsq hn.le) (D.iso n hn.le)
      (D.iso (n + 1) (succ_le_of_lt hn)) (D.comp_step n hn) (D.center_comap n hn)
      (D.comp_fst n hn.le) (P.hgam hn.le)
    { next :=
        { X := S.total
          str := S.totalStruct
          gam := S.totalComparison
          hsq := fun _ => S.isPullback_base
          hgam := fun _ => S.hom_comparison }
      down := S.down
      cen := S.totalCenter
      hblow := fun _ => S.isBlowup_down
      hpb := fun _ => S.isPullback_sq
      hcen := fun _ => S.center_comap.symm }
  else
    { next :=
        { X := t.schemeAt (n + 1)
          str := projectionToBase t (n + 1) ≫ g
          gam := 𝟙 (t.schemeAt (n + 1))
          hsq := fun hle => absurd (lt_of_succ_le hle) hn
          hgam := fun hle => absurd (lt_of_succ_le hle) hn }
      down := transitionMapSucc t n ≫ P.gam
      cen := ⊤
      hblow := fun hlt => absurd hlt hn
      hpb := fun hlt => absurd hlt hn
      hcen := fun hlt => absurd hlt hn }

def descendedSchemeDataAt : DescendedSchemeData g t D n :=
  Nat.rec (motive := fun m => DescendedSchemeData g t D m) (descendedSchemeDataZero g t D)
    (fun m P => (descendedBlowupAt g t D m P).next) n

def descendedSchemeAt : Sch :=
  (descendedSchemeDataAt g t D n).X

def descendedBlowupMorphism : descendedSchemeAt g t D (n + 1) ⟶ descendedSchemeAt g t D n :=
  (descendedBlowupAt g t D n $ descendedSchemeDataAt g t D n).down
end

def descendedTower :
    ℕᵒᵖ ⥤ Sch :=
  Functor.ofOpSequence $ descendedBlowupMorphism g t D

def descendedSequenceOfBlowups :
    SequenceOfBlowups Y where
  length := t.length
  tower := descendedTower g t D
  isoZero := refl Y
  center := fun i => (descendedBlowupAt g t D i $ descendedSchemeDataAt g t D i).cen
  isBlowup := fun i hi => by
    have hmap : (descendedTower g t D).map (homOfLE $ le_succ i).op = descendedBlowupMorphism g t D i :=
      Functor.ofOpSequence_map_homOfLE_succ (descendedBlowupMorphism g t D) i
    rw [hmap]
    exact (descendedBlowupAt g t D i $ descendedSchemeDataAt g t D i).hblow hi

theorem exists_isStrictPullbackSequenceOfBlowups_of_descentDatum : ∃ s : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t s := by
  let _a0 := descendedSequenceOfBlowups g t D
  let _a1 := (descendedSchemeDataAt g t D 0).gam
  refine ⟨_a0, rfl, fun i _ => (descendedSchemeDataAt g t D i).gam, ?_, ?_, ?_⟩
  show _a1 ≫ sbIzH _a0 = sbIzH t ≫ g
  have h0 : _a1 = projectionToBase t 0 ≫ g := rfl
  rw [h0, SequenceOfBlowups.projectionToBase_zero]
  exact comp_id _
  intro i hi
  have hmap : transitionMapSucc _a0 i = descendedBlowupMorphism g t D i := by
    rw [blowupMorphism_eq_transitionMap, transitionMap_def]
    exact Functor.ofOpSequence_map_homOfLE_succ (descendedBlowupMorphism g t D) i
  rw [hmap]
  exact (descendedBlowupAt g t D i $ descendedSchemeDataAt g t D i).hpb hi
  intro i hi
  exact (descendedBlowupAt g t D i $ descendedSchemeDataAt g t D i).hcen hi
end

theorem exists_isStrictPullback_of_isomorphic_baseChange
    (h : (t.baseChange $ pullback.fst g g).Isomorphic $ t.baseChange $ pullback.snd g g) :
    ∃ s : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t s := by
  let _a0 := pullback.fst g g
  obtain ⟨-, e, hzero, hstep, hcen⟩ := h
  have hlp :=
    t.baseChange_length _a0
  refine exists_isStrictPullbackSequenceOfBlowups_of_descentDatum g t
    { iso := fun i hi => e i (by rw [hlp]; exact hi)
      comp_fst := ?_
      center_comap := ?_
      comp_step := ?_ }
  intro i hi
  have key := iso_hom_comp_projectionToBase (t.baseChange _a0)
    (t.baseChange $ pullback.snd g g) _ e hstep hzero i (by rw [hlp]; exact hi)
  rwa [baseChange_projectionToBase_eq_fst, baseChange_projectionToBase_eq_fst] at key
  intro i hi
  have key := hcen i (by rw [hlp]; exact hi)
  rwa [SequenceOfBlowups.baseChange_center, SequenceOfBlowups.baseChange_center] at key
  intro i hi
  have key := hstep i (by rw [hlp]; exact hi)
  rwa [SequenceOfBlowups.baseChange_blowupMorphism, SequenceOfBlowups.baseChange_blowupMorphism] at key
end
end




theorem existsGluedBlowupSequence_of_center_ne_top (R : AffineResolutionRule)
    (hR : ∀ (k : Type) [Field k] [CharZero k] Y
      p [LocallyOfFiniteType p]
      [QuasiCompact p] [IsReduced Y]
      [IsAffine Y] i,
      i < (R k Y p).length → center (R k Y p) i ≠ ⊤) :
    ExistsGluedBlowupSequence R := by
  intro hcover k hk hk0 Y p hpft hpqc hpred
  have := isLocallyNoetherian p
  have : CompactSpace $ Sp k := inferInstance
  have := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨ι, hio, U, hUaff, hUtop⟩ := exists_finite_affine_cover Y
  let _s1 := sigmaOpens Y U
  have := isAffine_sigmaOpens Y U hUaff
  have : CompactSpace _s1 := inferInstance
  let _s0 := sigmaOpensDesc Y U
  have :=
    surjective_sigmaOpensDesc Y U hUtop
  let _a0 := sigmaOpensDesc Y U ≫ p
  obtain ⟨V, sV, r, hVaff, hVred, hsft, hsqc, hret, hrsurj, hrq⟩ :=
    exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff _s1
      _a0 _s0 rfl
  have :=
    etale_comp_fst_pullback_sigmaOpensDesc Y U _s1 _s0 V r
  let _a3 := r ≫ pullback.snd _s0 _s0
  have :=
    etale_comp_snd_pullback_sigmaOpensDesc Y U _s1 _s0 V r
  have :=
    surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop _s1
      _s0 V r
  have :=
    surjective_comp_snd_pullback_sigmaOpensDesc Y U _s1
      _s0 V r
  have hq1 := hrq
  rw [← assoc] at hq1
  have hq2 : _a3 ≫
      _a0 = sV := by
    have h := comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U _s1
      _s0 V r
    have h3 := congrArg (fun m => m ≫ p) h
    simp [assoc] at h3
    rwa [assoc, ← h3]
  have ht1 := hcover k _s1 V _a0 sV
    (r ≫ pullback.fst _s0 _s0) hq1
    surj
  have ht2 := hcover k _s1 V _a0 sV
    _a3 hq2
    surj
  obtain ⟨B, hB⟩ := by
    let g := _s0
    let t := R k _s1 _a0
    let _a7 := pullback.fst g g
    let _a8 := pullback.snd g g
    have hAr :=
      isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange _a7) r
    have hCr :=
      isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange _a8) r
    exact exists_isStrictPullback_of_isomorphic_baseChange g t
      (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hAr hCr $ (ht1.isomorphic $ hAr.comp $ isStrictPullbackSequenceOfBlowups_baseChange t _a7).symm.trans $ ht2.isomorphic $ hCr.comp $ isStrictPullbackSequenceOfBlowups_baseChange t _a8)
  refine ⟨B, hB.center_ne_top_of_forall_center_ne_top
    (fun i hi => hR k _s1 _a0 i hi), ?_⟩
  intro W' q' hq'ft hq'qc hW'red hW'aff ph_ hphet hphq hphsurj
  have : q10 ph_ := ⟨hphsurj⟩
  obtain ⟨V', sV', r', hV'aff, hV'red, hs'ft, hs'qc, hr'et, hr'surj, hr'q⟩ :=
    exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff W' q' ph_ hphq
  have :=
    etale_comp_fst_pullback_sigmaOpensDesc Y U W' ph_ V' r'
  have :=
    etale_comp_snd_pullback_sigmaOpensDesc Y U W' ph_ V' r'
  have :=
    surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop W' ph_ V' r'
  have :=
    surjective_comp_snd_pullback_sigmaOpensDesc Y U W' ph_ V' r'
  have hal_ : (r' ≫ pullback.fst ph_ _s0) ≫ q' = sV' := by
    rwa [assoc]
  have hbe_ : (r' ≫ pullback.snd ph_ _s0) ≫ _a0 = sV' := by
    have h3 := congrArg (fun m => m ≫ p) $ comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' ph_ V' r'
    simp [assoc] at h3
    rwa [assoc, ← h3, hphq]
  have hu1 := hcover k W' V' q' sV' (r' ≫ pullback.fst ph_ _s0) hal_
    surj
  have hu2 := hcover k _s1 V' _a0 sV'
    (r' ≫ pullback.snd ph_ _s0) hbe_
    surj
  have halph : (r' ≫ pullback.fst ph_ _s0) ≫ ph_
      = (r' ≫ pullback.snd ph_ _s0) ≫ sigmaOpensDesc Y U := by
    simp [assoc]
    exact comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' ph_ V' r'
  have hfin := hu2.comp hB
  rw [← halph] at hfin
  have hbc := isStrictPullbackSequenceOfBlowups_baseChange B ph_
  have hbcal :=
    isStrictPullbackSequenceOfBlowups_baseChange (B.baseChange ph_) $ r' ≫ pullback.fst ph_ _s0
  exact hbc.of_isomorphic_pullback (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hu1 hbcal $ hfin.isomorphic $ hbcal.comp hbc).symm





theorem notMem_support_comap_top {A C : Sch} (h : A ⟶ C) x :
    x ∉ support (comap (⊤ : ISD C) h) := by
  rw [comap_top, support_top]
  intro hx
  have hx' : x ∈ ((⊥) : Set A) := hx
  simp at hx'

theorem center_ne_top_of_isPullbackSequenceOfBlowups_id {X} (s : SequenceOfBlowups X)
    (h : IsPullbackBlowupSequence (𝟙 X) s s) :
    ∀ i, i < s.length → center s i ≠ ⊤ := by
  obtain ⟨r, _e, _hlt, hmono, htop, hsupp, -⟩ := h
  have hgeid : ∀ i, i ≤ s.length → i ≤ r i := by
    intro i
    induction i with
    | zero => intro _; exact zero_le _
    | succ n ih =>
      intro hn
      have h1 := hmono n (n + 1) hn $ lt_succ_self n
      have h2 := ih $ le_of_succ_le hn
      omega
  have hleid : ∀ d i, i + d = s.length → r i + d ≤ s.length := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hii : i = s.length := by omega
      subst hii
      rw [htop]
      omega
    | succ m ih =>
      intro i hi
      have hi1 : (i + 1) + m = s.length := by omega
      have h2 := ih (i + 1) hi1
      have h3 := hmono i (i + 1) (by omega) $ lt_succ_self i
      omega
  have hrid : ∀ i, i ≤ s.length → r i = i := by
    intro i hi
    have h1 := hgeid i hi
    have h2 := hleid (s.length - i) i $ by omega
    omega
  intro i hi hc
  obtain ⟨x, hx⟩ := mpr_ (hsupp i hi) ⟨i, hi, hrid i hi.le⟩
  rw [hc] at hx
  exact notMem_support_comap_top _ x hx

theorem AffineResolutionRule.center_ne_top (B : AffineResolutionRule) (hB : IsCompatibleWithOpenImmersions B)
    (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] :
    ∀ i : ℕ, i < (B k Y p).length → center (B k Y p) i ≠ ⊤ :=
  center_ne_top_of_isPullbackSequenceOfBlowups_id (B k Y p) $ hB k Y Y p p (𝟙 Y) $ id_comp p

theorem inducedRuleCompatibleWithFieldExtension (B : AffineResolutionRule) : InducedRuleCompatibleWithFieldExtension B := by
  intro hoi hfe F hF k _ _ X f _ _ _ K _ _ _ _
  obtain ⟨W, c, g, hWaff, hWred, hqlft, hqqc, hcet, hcsur, hYaff, hYred, hglft, hgqc, hget,
    hgsur, hgstruct, hgproj⟩ := exists_etale_surjective_affine_cover_baseChange X f K
  let _a4 := baseChangeProjection f K
  let _a0 := (F k X f).baseChange _a4
  have h0 : IsStrictPullbackBlowupSeq _a4
      _a0 $ F k X f :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hw : IsStrictPullbackBlowupSeq g
      (_a0.baseChange g)
      _a0 :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hcomp := hw.comp h0
  rw [hgproj] at hcomp
  let _a3 := c ≫ f
  let _a1 := baseChange _a3 K
  let _a2 := baseChangeToSpec _a3 K
  have hntop := AffineResolutionRule.center_ne_top B hoi K _a1
      _a2
  exact h0.isPullbackSequenceOfBlowups_withoutIsoBlowups.of_isomorphic $ IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hw.withoutIsoBlowups (hF K (baseChange f K) (baseChangeToSpec f K) _a1 _a2 g hgstruct surj) $ (SequenceOfBlowups.Isomorphic.withoutIsoBlowups $ hcomp.isomorphic $ (hfe k W _a3 K).comp $ hF k X f W _a3 c rfl surj).trans $ withoutIsoBlowups_isomorphic_self _ hntop




namespace SequenceOfBlowups

variable {X : Sch}

section
variable (s : SequenceOfBlowups X) {X'} (ph_ : X' ⟶ X)
theorem pullbackTransitionMap_self_eq_id {i} (h : i ≤ i) :
    s.pullbackTransitionMap ph_ h = 𝟙 (pullback ph_ $ projectionToBase s i) := by
  refine pullback.hom_ext ?_ ?_
  simp_all
  simp_all

theorem pullbackTransitionMap_trans {i j l}
    (hij : i ≤ j) (hjl : j ≤ l) :
    s.pullbackTransitionMap ph_ hjl ≫ s.pullbackTransitionMap ph_ hij = s.pullbackTransitionMap ph_ (hij.trans hjl) := by
  refine pullback.hom_ext ?_ ?_
  rw [assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
  rw [assoc, s.pullbackTransitionMap_snd, ← assoc, s.pullbackTransitionMap_snd, assoc,
    s.transitionMap_trans, s.pullbackTransitionMap_snd]

theorem isIso_pullbackTransitionMap {n n' : ℕ}
    (h : n ≤ n') (hstep : ∀ m, n ≤ m → m < n' → IsIso (s.pullbackTransitionMap ph_ $ le_succ m)) :
    IsIso $ s.pullbackTransitionMap ph_ h := by
  obtain ⟨k, rfl⟩ := exists_eq_add_of_le h
  have _i4 : ∀ k (h : n ≤ n + k), (∀ m, n ≤ m → m < n + k → IsIso (s.pullbackTransitionMap ph_ $ le_succ m)) → IsIso (s.pullbackTransitionMap ph_ h) := by
    intro k
    induction k with
    | zero =>
        intro h _
        rw [s.pullbackTransitionMap_self_eq_id ph_ h]
        infer_instance
    | succ k ih =>
        intro h hstep
        let _a1 := le_add_right n k
        have h1 :=
          ih _a1 fun m hm hmk => hstep m hm $ by omega
        have h2 :=
          hstep (n + k) _a1 $ by omega
        let _a0 := le_succ $ n + k
        have key : IsIso $ s.pullbackTransitionMap ph_ _a0 ≫
            s.pullbackTransitionMap ph_ _a1 := inferInstance
        rwa [s.pullbackTransitionMap_trans ph_ _a1 _a0] at key
  exact _i4 k h hstep
end

end SequenceOfBlowups

theorem idealSheafData_eq_top_of_support_empty {X : Sch} (I : ISD X)
    (h : ∀ x : X, x ∉ support I) : I = ⊤ := by
  rw [← support_eq_bot_iff]
  ext x
  simp [h x]

theorem isPullback_of_iso_pullback {P Z A A' : Sch} (f : A' ⟶ A) (h : Z ⟶ A)
    (ep_ : P ≅ pullback f h) {a : P ⟶ Z} {b : P ⟶ A'}
    (ha : hom ep_ ≫ pullback.snd f h = a) (hb : hom ep_ ≫ pullback.fst f h = b) :
    IsPullback a b h f := by
  refine (of_iso_pullback ⟨?_⟩ ep_ hb ha).flip
  rw [← ha, ← hb, assoc, assoc, pullback.condition]

theorem IsPullbackBlowupSequence.exists_reindexing_of_flat {A A' : Sch} (f : A' ⟶ A)
    [Flat f] {t' : SequenceOfBlowups A'} {t : SequenceOfBlowups A}
    (hpb : IsPullbackBlowupSequence f t' t) :
    ∃ (σ : ℕ → ℕ) (g : ∀ j, j ≤ t'.length → (t'.schemeAt j ⟶ t.schemeAt (σ j))),
      (∀ j, j < t'.length → σ j < t.length) ∧
      (∀ j, j < t'.length → σ j < σ (j + 1)) ∧
      σ t'.length = t.length ∧
      (∀ j hj,
        IsPullback (g j hj) (projectionToBase t' j) (projectionToBase t (σ j)) f) ∧
      (∀ j hj i hi,
        (∀ m, i ≤ m → m < σ j → ∀ j', j' < t'.length → σ j' ≠ m) →
        IsPullback (g j hj ≫ t.transitionMap hi) (projectionToBase t' j) (projectionToBase t i) f) ∧
      (∀ j hj (hsg_ : σ j + 1 ≤ σ (j + 1)),
        IsPullback (g (j + 1) (succ_le_of_lt hj) ≫ t.transitionMap hsg_) (transitionMapSucc t' j)
          (transitionMapSucc t (σ j)) (g j (Nat.le_of_lt hj))) ∧
      (∀ j hj,
        center t' j = (center t (σ j)).comap (g j (Nat.le_of_lt hj))) ∧
      (∀ i, i < t.length → (∀ j, j < t'.length → σ j ≠ i) →
        ∀ (P : Sch) (q : P ⟶ t.schemeAt i) (p : P ⟶ A'),
          IsPullback q p (projectionToBase t i) f → (center t i).comap q = ⊤) := by
  obtain ⟨r, e, hrlt, hrmono, hrlen, hsupp, hfst, hblow, hcen⟩ := hpb
  have hmono : ∀ i j, j ≤ t'.length → i ≤ j → r i ≤ r j := by
    intro i j hj hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    exact le_rfl
    exact ltLe (hrmono i j hj hlt)
  have hrle : ∀ j, j ≤ t'.length → r j ≤ t.length := by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hlt
    exact le_of_eq hrlen
    exact ltLe (hrlt j hlt)
  have htop : ∀ m, m < t.length → (∀ j', j' < t'.length → r j' ≠ m) →
      (center t m).comap (pullback.snd f (projectionToBase t m)) = ⊤ := by
    intro m hm hskip
    refine idealSheafData_eq_top_of_support_empty _ ?_
    intro x hx
    obtain ⟨j', hj', hrj'⟩ := mp_ (hsupp m hm) ⟨x, hx⟩
    exact hskip j' hj' hrj'
  have hiso : ∀ m, m < t.length → (∀ j', j' < t'.length → r j' ≠ m) →
      IsIso (t.pullbackTransitionMap f (le_succ m)) := by
    intro m hm hskip
    have hb := (t.baseChange f).isBlowupAlongIdealSheaf_blowupMorphism m hm
    rw [SequenceOfBlowups.baseChange_blowupMorphism, SequenceOfBlowups.baseChange_center,
      htop m hm hskip] at hb
    exact hb.isIso_of_top
  have hD := fun j hj =>
    isPullback_of_iso_pullback f (projectionToBase t (r j)) (e j hj) rfl (hfst j hj)
  have hE : ∀ j (hj : j ≤ t'.length) i hi,
      (∀ m, i ≤ m → m < r j → ∀ j', j' < t'.length → r j' ≠ m) →
      IsPullback ((isoH (e j hj) ≫ pullback.snd f (projectionToBase t (r j))) ≫ t.transitionMap hi)
        (projectionToBase t' j) (projectionToBase t i) f := by
    intro j hj i hi hskip
    have hiso' : IsIso (t.pullbackTransitionMap f hi) := by
      refine SequenceOfBlowups.isIso_pullbackTransitionMap t f hi ?_
      intro m him hmrj
      exact hiso m (lt_of_lt_of_le hmrj (hrle j hj)) fun j' hj' => hskip m him hmrj j' hj'
    refine isPullback_of_iso_pullback f (projectionToBase t i) ((e j hj) ≪≫ asIso (t.pullbackTransitionMap f hi)) ?_ ?_
    simp_all
    simp_all
  have hF : ∀ j (hj : j < t'.length) (hsig : r j + 1 ≤ r (j + 1)),
      IsPullback
        ((isoH (e (j + 1) (succ_le_of_lt hj)) ≫ pullback.snd f (projectionToBase t (r (j + 1))))
          ≫ t.transitionMap hsig)
        (transitionMapSucc t' j) (transitionMapSucc t (r j))
        (isoH (e j (m49 hj)) ≫ pullback.snd f (projectionToBase t (r j))) := by
    intro j hj hsig
    have hskip : ∀ m, r j + 1 ≤ m → m < r (j + 1) → ∀ j', j' < t'.length → r j' ≠ m := by
      intro m hm1 hm2 j' hj' hrj'
      rcases m63 j j' with hlt | hle
      have h1 := hmono (j + 1) j' (le_of_lt hj') $ Nat.succ_le_of_lt hlt
      omega
      have h1 := hmono j' j (le_of_lt hj) hle
      omega
    have s0 := hE (j + 1) (succ_le_of_lt hj) (r j + 1) hsig hskip
    rw [t'.projectionToBase_succ j, t.projectionToBase_succ (r j)] at s0
    let _a0 := le_succ $ r j
    have hdown : t.transitionMap hsig ≫ transitionMapSucc t (r j) = t.transitionMap (_a0.trans hsig) :=
      t.transitionMap_trans _a0 hsig
    refine of_bot s0 ?_ (hD j (m49 hj))
    simp [assoc]
    rw [hdown, ← assoc (transitionMapSucc t' j),
      hblow j hj (_a0.trans hsig), assoc, t.pullbackTransitionMap_snd]
  refine ⟨r, fun j hj => isoH (e j hj) ≫ pullback.snd f (projectionToBase t (r j)),
    hrlt, fun j hj => hrmono j (j + 1) hj $ lt_succ_self j, hrlen, hD, hE, hF, hcen, ?_⟩
  intro i hi hskip P q p hsq
  let u := pullback.lift p q (hsq.w.symm)
  let _a1 := pullback.snd f (projectionToBase t i)
  have hu2 : u ≫ _a1 = q := pullback.lift_snd _ _ _
  have hcomp : (center t i).comap q
      = ((center t i).comap _a1).comap u := by
    rw [← hu2]
    simp [comap_comp]
  rw [hcomp, htop i hi hskip]
  exact comap_top u


namespace MarkedIdealWithBoundary

theorem isAdmissible_pullbackAlong_of_smooth (T : MarkedIdealWithBoundary) (hV : IsAdmissible T) Y
    q (h : Y ⟶ scheme T)
    [Smooth h] [QuasiCompact q]
    (hq : h ≫ structMap T = q) :
    IsAdmissible $ T.pbA q h := by
  let _a0 := h ≫ tMp T
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have hqc : QuasiCompact q := inferInstance
  subst hq
  have : Smooth _a0 := inferInstance
  have : Flat h := inferInstance
  refine ⟨hV.charZero, ?_, hV.nonzeroOnComponents.comap_of_flat h, hV.one_le_mult, hqc, ?_, inStrictNormalCrossingPosition_comap T.structMap h T.boundary hV.snc⟩
  show LocallyOfFiniteType _a0
  infer_instance
  show Smooth _a0
  infer_instance

end MarkedIdealWithBoundary


theorem isPullback_pullbackTransitionMap_comp_transitionMap {X X' : Sch} (s : SequenceOfBlowups X)
    (ph_ : X' ⟶ X) (i j j' : ℕ) (hj : j = i) (hj' : j' = i + 1) (hjj' : j ≤ j')
    (hij : i ≤ j) (hij' : i + 1 ≤ j') :
    IsPullback (pullback.snd ph_ (projectionToBase s j') ≫ s.transitionMap hij')
      (s.pullbackTransitionMap ph_ hjj') (transitionMapSucc s i)
      (pullback.snd ph_ (projectionToBase s j) ≫ s.transitionMap hij) := by
  subst hj
  subst hj'
  simp [SequenceOfBlowups.transitionMap_self_eq_id, comp_id]
  exact s.isPullback_pullbackTransitionMap ph_ _

theorem center_comap_eq_comap_comp_transitionMap_of_eq {X W V : Sch} (s : SequenceOfBlowups X) {i j : ℕ}
    (hij : i ≤ j) (hji : j = i) (f : W ⟶ V) (g : V ⟶ s.schemeAt j) :
    comap (center s j) (f ≫ g) = comap (center s i) (f ≫ g ≫ s.transitionMap hij) := by
  subst hji
  rw [SequenceOfBlowups.transitionMap_self_eq_id, comp_id]

theorem support_nonempty_of_ne_top {Y : Sch} (I : ISD Y) (h : I ≠ ⊤) :
    ((support I : Set ↥Y)).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro he
  apply h
  have hbot : spI I = ⊥ := SetLike.ext' (by rw [he]; rfl)
  exact mp_ (support_eq_bot_iff I) hbot

section
variable {X X' : Sch}
theorem support_comap_center_nonempty_of_mem_range (ph_ : X' ⟶ X) (s : SequenceOfBlowups X)
    (hne : ∀ i : ℕ, i < s.length → ((support (center s i) : CSet $ s.schemeAt i)).Nonempty)
    (hran : ∀ i : ℕ, i < s.length → ∀ x ∈ (support (center s i) : CSet $ s.schemeAt i),
      (projectionToBase s i).base x ∈ range (⇑ph_.base)) :
    ∀ i, i < s.length →
      ((support (comap (center s i) $ pullback.snd ph_ $ projectionToBase s i) :
        Set ↥(pullback ph_ $ projectionToBase s i))).Nonempty := by
  intro i hi
  obtain ⟨x, hx⟩ := hne i hi
  obtain ⟨y, hy⟩ := hran i hi x hx
  obtain ⟨z, hz1, hz2⟩ :=
    exists_preimage_pullback (f := ph_) (g := sbPrj s i) y x hy
  refine ⟨z, ?_⟩
  have hmem : (pullback.snd ph_ $ sbPrj s i) z ∈ (spI (center s i) : CSet $ sbAt s i) := by simp_all
  rwa [support_comap]

theorem IsPullbackBlowupSequence.isStrictPullback_of_support_comap_center_nonempty {ph_ : X' ⟶ X} {s' : SequenceOfBlowups X'}
    {s : SequenceOfBlowups X} (h : IsPullbackBlowupSequence ph_ s' s)
    (hhit : ∀ i : ℕ, i < s.length →
      ((support (comap (center s i) (pullback.snd ph_ (projectionToBase s i))) :
        Set ↥(pullback ph_ (projectionToBase s i)))).Nonempty) :
    IsStrictPullbackBlowupSeq ph_ s' s := by
  obtain ⟨r, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hsurj : ∀ i, i < s.length → ∃ j, j < s'.length ∧ r j = i := by
    intro i hi
    obtain ⟨x, hx⟩ := hhit i hi
    exact mp_ (h4 i hi) ⟨x, hx⟩
  have hid : ∀ i, i ≤ s'.length → r i = i := by
    let L' := s'.length
    have hA : ∀ i, i ≤ L' → i ≤ r i := by
      intro i
      induction i with
      | zero => intro _; exact zero_le _
      | succ n ih =>
        intro hn
        have hstep := h2 n (n + 1) hn $ lt_succ_self n
        have hprev := ih $ le_of_succ_le hn
        omega
    have key : ∀ i, (∀ j, j < i → j ≤ L' → r j ≤ j) → i ≤ L' → r i ≤ i := by
      intro i ih hi
      by_contra hcon
      have hlt : i < r i := by omega
      have hle : r i ≤ s.length := by
        rcases m63 i L' with hc | hc
        exact le_of_lt $ h1 i hc
        have hEq := le_antisymm hi hc
        subst hEq
        exact le_of_eq h3
      obtain ⟨j, hjL, hrj⟩ := hsurj i $ by omega
      have hjle := hA j $ le_of_lt hjL
      rcases m63 j i with hji | hji
      have hij := ih j hji $ le_of_lt hjL
      omega
      have hEq : j = i := by omega
      subst hEq
      omega
    have hB' : ∀ n i, i ≤ n → i ≤ L' → r i ≤ i := by
      intro n
      induction n with
      | zero =>
        intro i hi hiL
        exact key i (fun j hj _ => by omega) hiL
      | succ n ih =>
        intro i hi hiL
        exact key i (fun j _ hjL => ih j (by omega) hjL) hiL
    intro i hi
    exact le_antisymm (hB' i i le_rfl hi) $ hA i hi
  have hlen : s'.length = s.length := by simp_all
  refine ⟨hlen, fun i hi => isoH (e i hi) ≫ pullback.snd ph_ (sbPrj s $ r i) ≫
      s.transitionMap (le_of_eq (hid i hi).symm), ?_, ?_, ?_⟩
  have h0 := h5 0 $ zero_le s'.length
  simp [assoc]
  rw [← s.projectionToBase_zero, s.transitionMap_comp_projectionToBase, ← pullback.condition,
    ← assoc, h0, s'.projectionToBase_zero]
  intro i hi
  have hile := le_of_lt hi
  have hi1 := hi
  have hrle := le_of_lt $ h2 i (i + 1) hi1 $ lt_succ_self i
  have sq1 : IsPullback (e (i + 1) hi).hom (sbTrS s' i) (s.pullbackTransitionMap ph_ hrle)
      (e i hile).hom := by
    exact of_horiz_isIso ⟨sy_ $ h6 i hi hrle⟩
  let _a0 := hid (i + 1) hi1
  exact sq1.paste_horiz $ isPullback_pullbackTransitionMap_comp_transitionMap s ph_ i (r i) (r $ i + 1) (hid i hile) _a0 hrle (le_of_eq (hid i hile).symm) $ le_of_eq _a0.symm
  intro i hi
  have hile := le_of_lt hi
  rw [h7 i hi]
  exact center_comap_eq_comap_comp_transitionMap_of_eq s (le_of_eq (hid i hile).symm) (hid i hile) (e i hile).hom
    (pullback.snd ph_ $ sbPrj s $ r i)

theorem IsPullbackBlowupSequence.isStrictPullback_of_surjective {ph_ : X' ⟶ X}
    [AlgebraicGeometry.Surjective ph_] {s'} {s : SequenceOfBlowups X}
    (h : IsPullbackBlowupSequence ph_ s' s) (hc : ∀ i : ℕ, i < s.length → center s i ≠ ⊤) :
    IsStrictPullbackBlowupSeq ph_ s' s := by
  refine h.isStrictPullback_of_support_comap_center_nonempty ?_
  refine support_comap_center_nonempty_of_mem_range ph_ s
    (fun i hi => support_nonempty_of_ne_top (center s i) $ hc i hi) ?_
  intro i _ x _
  exact ph_.surjective _
end




namespace BlowupSequenceData

theorem toSequenceOfBlowups_isomorphic_of_iso {X : Sch} (d d' : BlowupSequenceData X)
    (hlen : d.length = d'.length)
    (e : ∀ i : ℕ, i ≤ d.length → (d.obj i ≅ d'.obj i))
    (hzero : hom (e 0 $ zero_le _) ≫ d'.isoZero.hom = d.isoZero.hom)
    (hmap : ∀ (i : ℕ) (hi : i < d.length),
      hom (e (i + 1) hi) ≫ d'.map i = d.map i ≫ hom (e i hi.le))
    (hcenter : ∀ (i : ℕ) (hi : i < d.length),
      comap (d'.center i) (e i hi.le).hom = d.center i) :
    d.toSequenceOfBlowups.Isomorphic d'.toSequenceOfBlowups := by
  refine ⟨?_, fun i hi => e i $ hi.trans_eq d.toSequenceOfBlowups_length, ?_, ?_, ?_⟩
  rwa [d.toSequenceOfBlowups_length, d'.toSequenceOfBlowups_length]
  rwa [d'.toSequenceOfBlowups_isoObjZero, d.toSequenceOfBlowups_isoObjZero]
  intro i hi
  rw [d'.toSequenceOfBlowups_blowupMorphism, d.toSequenceOfBlowups_blowupMorphism]
  exact hmap i $ lt_of_lt_of_eq hi d.toSequenceOfBlowups_length
  intro i hi
  rw [d'.toSequenceOfBlowups_center, d.toSequenceOfBlowups_center]
  exact hcenter i $ lt_of_lt_of_eq hi d.toSequenceOfBlowups_length

theorem ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic {X} (s : SequenceOfBlowups X) :
    (ofSequenceOfBlowups s).toSequenceOfBlowups.Isomorphic s := by
  refine ⟨tr_ (toSequenceOfBlowups_length $ ofSequenceOfBlowups s) $ ofSequenceOfBlowups_length s, fun i _ => refl _, ?_, ?_, ?_⟩
  have hz0 :=
    (toSequenceOfBlowups_isoObjZero $ ofSequenceOfBlowups s).trans $ ofSequenceOfBlowups_isoObjZero s
  exact tr_ (id_comp $ sbIzH s) (congrArg (fun e : (ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt 0 ≅ X => isoH e) hz0).symm
  intro i _
  exact tr_ (id_comp $ sbTrS s i)
    (tr_ (comp_id $ (ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMapSucc i) $ (toSequenceOfBlowups_blowupMorphism (ofSequenceOfBlowups s) i).trans $ ofSequenceOfBlowups_blowupMorphism s i).symm
  intro i _
  rw [(toSequenceOfBlowups_center (ofSequenceOfBlowups s) i).trans $ ofSequenceOfBlowups_center s i]
  show cmI (s.center i) (𝟙 $ sbAt s i) = s.center i
  simp

section
variable (X : Sch)
@[reducible]
def empty : BlowupSequenceData X := emptyBlowupSequenceData X

@[simp]
theorem empty_length : (empty X).length = 0 :=
  emptyBlowupSequenceData_length X

@[simp]
theorem empty_schemeAt (i : ℕ) : (empty X).obj i = X :=
  emptyBlowupSequenceData_schemeAt X i

@[simp]
theorem empty_isoObjZero : (empty X).isoZero = refl X :=
  emptyBlowupSequenceData_isoObjZero X
end

section
variable {X' X : Sch}
def toSeqComparisonMap (d' : BlowupSequenceData X') (d : BlowupSequenceData X)
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i)) (i : ℕ)
    (hi : i ≤ d'.toSequenceOfBlowups.length) : d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i :=
  eqToHom (toSequenceOfBlowups_schemeAt d' i) ≫ c i (hi.trans_eq $ toSequenceOfBlowups_length d') ≫
    eqToHom (toSequenceOfBlowups_schemeAt d i).symm

section
variable {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
theorem isPullback_toSeqComparisonMap
    c
    (hpb : ∀ (i : ℕ) (hi : i < d'.length),
      IsPullback (c (i + 1) hi) (d'.map i) (d.map i) $ c i hi.le)
    i (hi : i < d'.toSequenceOfBlowups.length) :
    IsPullback (toSeqComparisonMap d' d c (i + 1) hi) (d'.toSequenceOfBlowups.transitionMapSucc i) (d.toSequenceOfBlowups.transitionMapSucc i)
      (toSeqComparisonMap d' d c i hi.le) := by
  have hi' := hi.trans_eq $ toSequenceOfBlowups_length d'
  let _a0 := c (i + 1) hi'
  have h1 : toSeqComparisonMap d' d c (i + 1) hi = _a0 := by
    show 𝟙 (d'.obj $ i + 1) ≫ _a0 ≫ 𝟙 (d.obj $ i + 1) = _a0
    rw [id_comp, comp_id]
  have h2 : toSeqComparisonMap d' d c i hi.le = c i hi'.le := by
    show 𝟙 (d'.obj i) ≫ c i hi'.le ≫ 𝟙 (d.obj i) = c i hi'.le
    rw [id_comp, comp_id]
  rw [h1, h2, toSequenceOfBlowups_blowupMorphism, toSequenceOfBlowups_blowupMorphism]
  exact hpb i hi'

end

end

section
variable {X} (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
theorem append_schemeAt_eq_last_of_eq_length {j : ℕ} (h : j = s.length) :
    (append s t).obj j = s.obj s.length := by
  subst h
  exact append_schemeAt_of_le_length s t le_rfl

theorem append_schemeAt_eq_right_of_pos {i j : ℕ} (hi : 0 < i) (h : j = s.length + i) :
    (append s t).obj j = t.obj i := by
  have h2 : j - s.length = i := by omega
  rw [append_schemeAt_of_length_lt s t $ by omega, h2]

section
variable (i j : ℕ)
def concatObjIsoRight (h : j = s.length + i) : (append s t).obj j ≅ t.obj i :=
  if hi : 0 < i then eqToIso $ append_schemeAt_eq_right_of_pos s t hi h
  else
    eqToIso (append_schemeAt_eq_last_of_eq_length s t $ by omega) ≪≫ t.isoZero.symm ≪≫
      eqToIso (congrArg (fun n => t.obj n) $ show (0 : ℕ) = i by omega)

theorem concatObjIsoRight_hom_of_pos (hi : 0 < i) (h : j = s.length + i) :
    (s.concatObjIsoRight t i j h).hom = eqToHom (append_schemeAt_eq_right_of_pos s t hi h) := by
  unfold concatObjIsoRight
  rw [dif_pos hi, eqToIso.hom]

end

theorem concatObjIsoRight_hom_zero (j : ℕ) (h : j = s.length + 0) :
    hom (s.concatObjIsoRight t 0 j h) =
      eqToHom (append_schemeAt_eq_last_of_eq_length s t $ show j = s.length by omega) ≫ t.isoZero.inv := by
  unfold concatObjIsoRight
  rw [dif_neg $ Nat.lt_irrefl 0]
  simp
end

theorem blowupMorphism_eq_eqToHom_conj {Y} (d : BlowupSequenceData Y) {a b}
    (hab : a = b) :
    d.map a = eqToHom (congrArg d.obj $ congrArg (fun n => n + 1) hab) ≫ d.map b ≫
      eqToHom (congrArg d.obj hab.symm) := by
  subst hab
  simp

theorem center_comap_eqToHom_congr {Z Y : Sch} (t : BlowupSequenceData Z)
    {a b : ℕ} (e : a = b) (h1 : Y = t.obj a) (h2 : Y = t.obj b) :
    comap (center t a) (eqToHom h1) = comap (center t b) (eqToIso h2).hom := by
  subst e
  rfl

theorem comap_eqToHom_comap_eq {A B C : Sch} (e : A = B)
    (f : B ⟶ C) (I : ISD C) (e' : A = B) :
    comap (comap I f) (eqToHom e') = comap I (eqToHom e ≫ f) := by
  subst e
  simp

section
variable {X} (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (i j) (h : j = s.length + i)
theorem concatObjIsoRight_hom_comm_blowupMorphism :
    (append s t).map j ≫ hom (s.concatObjIsoRight t i j h) =
      hom (s.concatObjIsoRight t (i + 1) (j + 1) $ by omega) ≫ t.map i := by
  by_cases hi : 0 < i
  have hgt : s.length < j := by omega
  rw [concatObjIsoRight_hom_of_pos s t i j hi h,
    (concatObjIsoRight_hom_of_pos s t (i + 1) (j + 1) (succ_pos i) $ by omega),
    append_blowupMorphism_of_length_lt s t hgt,
    blowupMorphism_eq_eqToHom_conj t $ show j - s.length = i by omega]
  simp
  have hi0 : i = 0 := by omega
  subst hi0
  have hj : j = s.length := by omega
  subst hj
  rw [concatObjIsoRight_hom_zero s t s.length h,
    (concatObjIsoRight_hom_of_pos s t (0 + 1) (s.length + 1) (succ_pos 0) $ by omega),
    append_blowupMorphism_length s t]
  simp

theorem append_center_eq_comap_concatObjIsoRight :
    center (append s t) j = comap (center t i) (s.concatObjIsoRight t i j h).hom := by
  rcases m73 i with hi | hi
  subst hi
  obtain rfl : j = s.length := by omega
  have hiso : hom (s.concatObjIsoRight t 0 s.length h) =
      eqToHom (append_schemeAt_eq_last_of_eq_length s t rfl) ≫ t.isoZero.inv := by
    unfold concatObjIsoRight
    rw [dif_neg $ Nat.lt_irrefl 0]
    simp
  rw [append_center_length, hiso]
  exact comap_eqToHom_comap_eq _ _ _ _
  have hj : s.length < j := by omega
  have hiso : s.concatObjIsoRight t i j h = eqToIso (append_schemeAt_eq_right_of_pos s t hi h) := by
    unfold concatObjIsoRight
    exact dif_pos hi
  rw [append_center_of_length_lt s t hj, hiso]
  exact center_comap_eqToHom_congr t (show j - s.length = i by omega) _ _
end

theorem eq_comap_eqToHom_conj_of_heq {A A' B B' : Sch} (e1 : A = A') (e2 : B = B')
    (f : A' ⟶ B') (I : ISD B) (I' : ISD B')
    (J : ISD A) (J' : ISD A')
    (hI : HEq I I') (hJ : HEq J J') (h : J' = comap I' f) :
    J = comap I (eqToHom e1 ≫ f ≫ eqToHom e2.symm) := by
  subst e1
  subst e2
  rw [eq_of_heq hI, eq_of_heq hJ, h]
  simp

theorem toSequenceOfBlowups_center_eq_comap_toSeqComparisonMap {X' X : Sch} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hc : ∀ (i : ℕ) (hi : i < d'.length), d'.center i = comap (d.center i) (c i hi.le))
    (i : ℕ) (hi : i < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.center i = comap (d.toSequenceOfBlowups.center i) (toSeqComparisonMap d' d c i hi.le) := by
  have h1 := lt_of_lt_of_eq hi (toSequenceOfBlowups_length d')
  exact eq_comap_eqToHom_conj_of_heq (toSequenceOfBlowups_schemeAt d' i) (toSequenceOfBlowups_schemeAt d i) (c i h1.le)
    (d.toSequenceOfBlowups.center i) (d.center i) (d'.toSequenceOfBlowups.center i) (d'.center i)
    (heq_of_eq (toSequenceOfBlowups_center d i)) (heq_of_eq (toSequenceOfBlowups_center d' i)) (hc i h1)

def toStrictPullbackSeq {X' X : Sch} (g : X' ⟶ X) (d' : BlowupSequenceData X')
    (d : BlowupSequenceData X) (hlen : d'.length = d.length)
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hzero : c 0 (zero_le _) ≫ d.isoZero.hom = d'.isoZero.hom ≫ g)
    (hpb : ∀ (i : ℕ) (hi : i < d'.length),
      IsPullback (c (i + 1) hi) (d'.map i) (d.map i) $ c i hi.le)
    (hc : ∀ (i : ℕ) (hi : i < d'.length), d'.center i = comap (d.center i) (c i hi.le)) :
    StrictPullbackBlowupSeq g d'.toSequenceOfBlowups d.toSequenceOfBlowups where
  comp := toSeqComparisonMap d' d c
  comp_zero := by
    have hp : toSeqComparisonMap d' d c 0 (zero_le _) = c 0 (zero_le _) :=
      (id_comp $ c 0 (zero_le _) ≫ 𝟙 (d.obj 0)).trans $ comp_id _
    have hz : d.toSequenceOfBlowups.isoZero.hom = d.isoZero.hom :=
      congrArg (fun e : d.toSequenceOfBlowups.schemeAt 0 ≅ X => hom e) $ toSequenceOfBlowups_isoObjZero d
    have hz' : d'.toSequenceOfBlowups.isoZero.hom = d'.isoZero.hom :=
      congrArg (fun e : d'.toSequenceOfBlowups.schemeAt 0 ≅ X' => hom e) $ toSequenceOfBlowups_isoObjZero d'
    rw [hp, hz, hz']
    exact hzero
  pullback := isPullback_toSeqComparisonMap c hpb
  length_eq := by
    rw [toSequenceOfBlowups_length, toSequenceOfBlowups_length]
    exact hlen
  center_eq := toSequenceOfBlowups_center_eq_comap_toSeqComparisonMap c hc

end BlowupSequenceData

namespace StrictPullbackBlowupSeq

section
variable {X' X} {g} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g t s)
def lastMap : t.schemeAt t.length ⟶ s.schemeAt s.length :=
  D.comp t.length le_rfl ≫ eqToHom (congrArg (fun n => s.schemeAt n) D.length_eq)

theorem lastMap_eq :
    D.lastMap = D.comp t.length le_rfl ≫ eqToHom (congrArg (fun n => s.schemeAt n) D.length_eq) :=
  rfl
end

end StrictPullbackBlowupSeq

namespace BlowupSequenceData

section
variable {X' X : Sch}
section
variable (g) (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups) (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
include D'
section
variable (i) (hi : i ≤ (append s' t').length)
def concatComparisonMap :
    (append s' t').obj i ⟶ (append s t).obj i :=
  have hlen : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans $ D.length_eq.trans $ toSequenceOfBlowups_length s
  have hi2 : i ≤ s'.length + t'.length := hi
  if h : i ≤ s'.length then
    eqToHom (append_schemeAt_of_le_length s' t' h) ≫ eqToHom (toSequenceOfBlowups_schemeAt s' i).symm ≫
      D.comp i (h.trans_eq (toSequenceOfBlowups_length s').symm) ≫ eqToHom (toSequenceOfBlowups_schemeAt s i) ≫
        eqToHom (append_schemeAt_of_le_length s t $ show i ≤ s.length by omega).symm
  else
    hom (s'.concatObjIsoRight t' (i - s'.length) i $ by omega) ≫
      eqToHom (toSequenceOfBlowups_schemeAt t' $ i - s'.length).symm ≫
        D'.comp (i - s'.length)
            ((show i - s'.length ≤ t'.length by omega).trans_eq (toSequenceOfBlowups_length t').symm) ≫
          eqToHom (toSequenceOfBlowups_schemeAt t $ i - s'.length) ≫
            inv (s.concatObjIsoRight t (i - s'.length) i $ by omega)

theorem concatComparisonMap_of_le (h : i ≤ s'.length) (h2 : i ≤ s.length)
    (h3 : i ≤ s'.toSequenceOfBlowups.length) :
    concatComparisonMap g s t s' t' D D' i hi =
      eqToHom (append_schemeAt_of_le_length s' t' h) ≫ eqToHom (toSequenceOfBlowups_schemeAt s' i).symm ≫
        D.comp i h3 ≫ eqToHom (toSequenceOfBlowups_schemeAt s i) ≫ eqToHom (append_schemeAt_of_le_length s t h2).symm := by
  unfold concatComparisonMap
  exact dif_pos h

theorem concatComparisonMap_eq_dite
    (hlen : s'.length = s.length) (hi2 : i ≤ s'.length + t'.length) :
    concatComparisonMap g s t s' t' D D' i hi =
      (if h : i ≤ s'.length then
        eqToHom (append_schemeAt_of_le_length s' t' h) ≫ eqToHom (toSequenceOfBlowups_schemeAt s' i).symm ≫
          D.comp i (h.trans_eq (toSequenceOfBlowups_length s').symm) ≫ eqToHom (toSequenceOfBlowups_schemeAt s i) ≫
            eqToHom (append_schemeAt_of_le_length s t $ show i ≤ s.length by omega).symm
      else
        hom (s'.concatObjIsoRight t' (i - s'.length) i $ by omega) ≫
          eqToHom (toSequenceOfBlowups_schemeAt t' $ i - s'.length).symm ≫
            D'.comp (i - s'.length)
                ((show i - s'.length ≤ t'.length by omega).trans_eq (toSequenceOfBlowups_length t').symm) ≫
              eqToHom (toSequenceOfBlowups_schemeAt t $ i - s'.length) ≫
                inv (s.concatObjIsoRight t (i - s'.length) i $ by omega)) :=
  rfl
end

theorem concatComparisonMap_of_not_le
    (i a : ℕ) (hi : i ≤ (append s' t').length) (h : ¬ i ≤ s'.length)
    (ha : i - s'.length = a) (pf1 : i = s'.length + a) (pf2 : a ≤ t'.toSequenceOfBlowups.length)
    (pf3 : i = s.length + a) :
    concatComparisonMap g s t s' t' D D' i hi =
      hom (s'.concatObjIsoRight t' a i pf1) ≫ eqToHom (toSequenceOfBlowups_schemeAt t' a).symm ≫
        D'.comp a pf2 ≫ eqToHom (toSequenceOfBlowups_schemeAt t a) ≫ inv (s.concatObjIsoRight t a i pf3) := by
  subst ha
  unfold concatComparisonMap
  exact dif_neg h

theorem append_length_eq_of_strictPullbackBlowupSeq :
    (append s' t').length = (append s t).length := by
  have h1 :=
    (toSequenceOfBlowups_length s').symm.trans $ D.length_eq.trans $ toSequenceOfBlowups_length s
  have h2 :=
    (toSequenceOfBlowups_length t').symm.trans $ D'.length_eq.trans $ toSequenceOfBlowups_length t
  show s'.length + t'.length = s.length + t.length
  omega
end

section
variable {g} {u : SequenceOfBlowups X'} {v : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g u v)
theorem strictPullback_map_eqToHom_congr {a b : ℕ} (hab : a = b)
    (ha : a ≤ u.length) (hb : b ≤ u.length)
    {A A2 B2 B : Sch} (e1 : A = A2) (e2 : A2 = u.schemeAt a) (e3 : v.schemeAt a = B2) (e4 : B2 = B)
    (f1 : A = u.schemeAt b) (f2 : v.schemeAt b = B) :
    eqToHom e1 ≫ eqToHom e2 ≫ D.comp a ha ≫ eqToHom e3 ≫ eqToHom e4
      = eqToHom f1 ≫ D.comp b hb ≫ eqToHom f2 := by
  subst hab
  subst e1
  subst e2
  subst e3
  subst e4
  simp

theorem strictPullback_map_eq_lastMap_of_eq (a : ℕ) (ha : a ≤ u.length)
    (h : a = u.length) :
    D.comp a ha = eqToHom (congrArg u.schemeAt h) ≫ D.lastMap ≫
      eqToHom (congrArg v.schemeAt $ h.trans D.length_eq).symm := by
  subst h
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  simp
end
end

section
variable {Pa Xa Ya Za Pb Xb Yb Z2 : Sch} {fst : Pa ⟶ Xa} {snd : Pa ⟶ Ya} {f : Xa ⟶ Za} {gg : Ya ⟶ Za} (h : IsPullback fst snd f gg)
include h
theorem isPullback_of_conj_iso
    (eP : Pa ≅ Pb) (eA : Xa ≅ Xb) (eB : Ya ≅ Yb) (eC : Za ≅ Z2)
    {fst'} {snd'} {f'} {gg'}
    (h1 : fst' = inv eP ≫ fst ≫ hom eA) (h2 : snd' = inv eP ≫ snd ≫ hom eB)
    (h3 : f' = inv eA ≫ f ≫ hom eC) (h4 : gg' = inv eB ≫ gg ≫ hom eC) :
    IsPullback fst' snd' f' gg' := by
  subst h1
  subst h2
  subst h3
  subst h4
  refine h.of_iso eP eA eB eC ?_ ?_ ?_ ?_ <;> simp

section
variable (ep : Pb = Pa) (ex : Xa = Xb)
theorem isPullback_of_conj_eqToHom (ey : Ya = Yb) (ez : Za = Z2)
    {fst' : Pb ⟶ Xb} {snd' : Pb ⟶ Yb} {f' : Xb ⟶ Z2} {gg' : Yb ⟶ Z2}
    (h1 : fst' = eqToHom ep ≫ fst ≫ eqToHom ex)
    (h2 : snd' = eqToHom ep ≫ snd ≫ eqToHom ey)
    (h3 : f' = eqToHom ex.symm ≫ f ≫ eqToHom ez)
    (h4 : gg' = eqToHom ey.symm ≫ gg ≫ eqToHom ez) :
    IsPullback fst' snd' f' gg' := by
  subst ep
  subst ex
  subst ey
  subst ez
  subst h1
  subst h2
  subst h3
  subst h4
  simpa using h

theorem isPullback_of_conj_eqToHom_iso (ey : Ya ≅ Yb) (ez : Za ≅ Z2)
    {fst' : Pb ⟶ Xb} {snd' : Pb ⟶ Yb} {f' : Xb ⟶ Z2} {gg' : Yb ⟶ Z2}
    (h1 : fst' = eqToHom ep ≫ fst ≫ eqToHom ex)
    (h2 : snd' = eqToHom ep ≫ snd ≫ hom ey)
    (h3 : f' = eqToHom ex.symm ≫ f ≫ hom ez)
    (h4 : gg' = inv ey ≫ gg ≫ hom ez) :
    IsPullback fst' snd' f' gg' := by
  subst ep
  subst ex
  subst h1
  subst h2
  subst h3
  subst h4
  refine isPullback_of_conj_iso h (refl _) (refl _) ey ez ?_ ?_ ?_ ?_
  simp
  simp
  simp
  simp
end
end

section
variable {A A1_ B B1_ : Sch}
theorem comap_eqToHom_eq_comap_of_eq_comap (e1 : A = A1_) (e2 : B = B1_)
    (c : A1_ ⟶ B1_) (f : A ⟶ B) (hf : f = eqToHom e1 ≫ c ≫ eqToHom e2.symm)
    (J : ISD A1_) (K : ISD B1_) (hJ : J = comap K c) :
    comap J (eqToHom e1) = comap (comap K $ eqToHom e2) f := by
  subst hf
  subst hJ
  subst e1
  subst e2
  simp

theorem comap_eq_comap_iso_hom_of_eq_comap (u : A ⟶ A1_) (be_ : B ≅ B1_)
    (c : A1_ ⟶ B1_) (J : ISD A1_) (K : ISD B1_) (hJ : J = comap K c)
    (p1 : A1_ = A1_) (p2 : B1_ = B1_) :
    comap J u = comap (comap K be_.hom) (u ≫ eqToHom p1 ≫ c ≫ eqToHom p2 ≫ inv be_) := by
  subst hJ
  have hb : u ≫ eqToHom p1 ≫ c ≫ eqToHom p2 ≫ isoI be_ = u ≫ c ≫ isoI be_ := by simp
  have hb2 : (u ≫ c ≫ isoI be_) ≫ isoH be_ = u ≫ c := by simp
  rw [hb, ← comap_comp, ← comap_comp, hb2]
end

section
variable {X} (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
theorem concatObjIsoRight_inv_of_pos (i j : ℕ) (hi : 0 < i) (h : j = s.length + i) :
    (s.concatObjIsoRight t i j h).inv = eqToHom (append_schemeAt_eq_right_of_pos s t hi h).symm := by
  unfold concatObjIsoRight
  rw [dif_pos hi, eqToIso.inv]

section
variable (j) (hj : j = s.length)
include hj
theorem append_blowupMorphism_of_eq_length
    (f1 : (append s t).obj (j + 1) = t.obj 1) (f2 : s.obj s.length = (append s t).obj j) :
    (append s t).map j = eqToHom f1 ≫ t.map 0 ≫ t.isoZero.hom ≫ eqToHom f2 := by
  subst hj
  exact append_blowupMorphism_length s t

theorem append_center_of_eq_length :
    center (append s t) j =
      comap (comap (center t 0) t.isoZero.inv) (eqToHom $ append_schemeAt_eq_last_of_eq_length s t hj) := by
  subst hj
  exact append_center_length s t
end
end

section
variable {Y' Y} {gg} {d' : BlowupSequenceData Y'} {d : BlowupSequenceData Y} (E : StrictPullbackBlowupSeq gg d'.toSequenceOfBlowups d.toSequenceOfBlowups)
theorem isPullback_blowupMorphism_of_strictPullbackBlowupSeq (i : ℕ)
    (hi : i < d'.toSequenceOfBlowups.length) (h1 : i + 1 ≤ d'.toSequenceOfBlowups.length) (h2 : i ≤ d'.toSequenceOfBlowups.length) :
    IsPullback ((E.comp (i + 1) h1 : d'.obj (i + 1) ⟶ d.obj (i + 1))) (d'.map i) (d.map i)
      ((E.comp i h2 : d'.obj i ⟶ d.obj i)) := by
  rw [← toSequenceOfBlowups_blowupMorphism d' i, ← toSequenceOfBlowups_blowupMorphism d i]
  exact E.pullback i hi

end

theorem eqToHom_conj_comp_eq_comp_of_heq {P Q Q' R R' S X' X : Sch}
    (a1_ : P = Q) (a2_ : Q = Q') (a3 : R' = R) (a4 : R = S) (a5 : S = R)
    (u : Q' ⟶ R') (izs : R ⟶ X) (izsT : R' ⟶ X) (izs' : Q ⟶ X') (izs'T : Q' ⟶ X')
    (g : X' ⟶ X) (h1 : HEq izsT izs) (h2 : HEq izs'T izs')
    (key : u ≫ izsT = izs'T ≫ g) :
    (eqToHom a1_ ≫ eqToHom a2_ ≫ u ≫ eqToHom a3 ≫ eqToHom a4) ≫ eqToHom a5 ≫ izs =
      (eqToHom a1_ ≫ izs') ≫ g := by
  subst a4
  subst a3
  subst a2_
  subst a1_
  have e1 := eq_of_heq h1
  have e2 := eq_of_heq h2
  subst e1
  subst e2
  simp [eqToHom_refl, id_comp, comp_id]
  exact key

theorem eqToHom_comp_eqToHom_conj_eq {A B R1 R1' R2 R2' C Dd : Sch} (f : R1 ⟶ R2)
    (a1 : A = B) (a2 : B = R1') (e1 : R1' = R1) (e2 : R2 = R2') (b1 : R2' = C) (b2 : C = Dd)
    (c1 : A = R1) (c2 : R2 = Dd) :
    eqToHom a1 ≫ eqToHom a2 ≫ (eqToHom e1 ≫ f ≫ eqToHom e2) ≫ eqToHom b1 ≫ eqToHom b2
      = eqToHom c1 ≫ f ≫ eqToHom c2 :=by simp_all
theorem eq_iso_inv_comp_comp_hom_of_comm_sq {P Q R1 R2 S1 S2 : Sch}
    (tm : R1 ⟶ R2) (z1 : S1 ≅ R1) (z2 : S2 ≅ R2) (u : S1 ⟶ S2)
    (hz : u ≫ z2.hom = z1.hom ≫ tm)
    (c1 : R1 = P) (c2 : R2 = Q) (lhs : P ⟶ Q)
    (hl : lhs = eqToHom c1.symm ≫ tm ≫ eqToHom c2) :
    lhs = (z1 ≪≫ eqToIso c1).inv ≫ u ≫ (z2 ≪≫ eqToIso c2).hom := by
  subst c1
  subst c2
  subst hl
  simp [eqToHom_refl,
    id_comp, comp_id]
  rw [hz]
  simp

theorem blowupMorphism_eqToHom_congr {Y : Sch} (d : BlowupSequenceData Y) {a b : ℕ} (hab : a = b)
    {A B : Sch} (e1 : A = d.obj (a + 1)) (e2 : d.obj a = B)
    (f1 : A = d.obj (b + 1)) (f2 : d.obj b = B) :
    eqToHom e1 ≫ d.map a ≫ eqToHom e2 = eqToHom f1 ≫ d.map b ≫ eqToHom f2 := by
  subst hab
  rfl

section
variable {X' X : Sch} (g : X' ⟶ X) (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups) (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
theorem concatComparisonMap_zero_comp_isoObjZero :
    concatComparisonMap g s t s' t' D D' 0 (zero_le _) ≫ (append s t).isoZero.hom =
      (append s' t').isoZero.hom ≫ g := by
  rw [append_isoObjZero_hom s t, append_isoObjZero_hom s' t']
  exact eqToHom_conj_comp_eq_comp_of_heq (append_schemeAt_of_le_length s' t' $ zero_le _)
    (toSequenceOfBlowups_schemeAt s' 0).symm (toSequenceOfBlowups_schemeAt s 0) (append_schemeAt_of_le_length s t $ zero_le _).symm
    (append_schemeAt_zero s t) (D.comp 0 $ zero_le _) s.isoZero.hom s.toSequenceOfBlowups.isoZero.hom
    s'.isoZero.hom s'.toSequenceOfBlowups.isoZero.hom g (heq_of_eq $ congrArg (fun e : s.toSequenceOfBlowups.schemeAt 0 ≅ X => isoH e) $ toSequenceOfBlowups_isoObjZero s) (heq_of_eq $ congrArg (fun e : s'.toSequenceOfBlowups.schemeAt 0 ≅ X' => isoH e) $ toSequenceOfBlowups_isoObjZero s') D.comp_zero

theorem isPullback_concatComparisonMap
    (i : ℕ) (hi : i < (append s' t').length) :
    IsPullback (concatComparisonMap g s t s' t' D D' (i + 1) hi) ((append s' t').map i)
      ((append s t).map i) $ concatComparisonMap g s t s' t' D D' i hi.le := by
  have hlen : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans $ D.length_eq.trans $ toSequenceOfBlowups_length s
  have hsl : s'.toSequenceOfBlowups.length = s'.length := toSequenceOfBlowups_length s'
  have htl : t'.toSequenceOfBlowups.length = t'.length := toSequenceOfBlowups_length t'
  have hlt : i < s'.length + t'.length := hi
  rcases lt_trichotomy i s'.length with hc | hc | hc
  have hiS : i < s.length := by omega
  have h1le : i + 1 ≤ s'.length := hc
  have h1leS : i + 1 ≤ s.length := by omega
  have h0le : i ≤ s'.length := ltLe hc
  have h0leS : i ≤ s.length := by omega
  have h1ts : i + 1 ≤ s'.toSequenceOfBlowups.length := by omega
  have h0ts : i ≤ s'.toSequenceOfBlowups.length := by omega
  have hlt' : i < s'.toSequenceOfBlowups.length := by omega
  refine isPullback_of_conj_eqToHom (isPullback_blowupMorphism_of_strictPullbackBlowupSeq D i hlt' h1ts h0ts) (append_schemeAt_of_le_length s' t' h1le)
    (append_schemeAt_of_le_length s t h1leS).symm (append_schemeAt_of_le_length s' t' h0le).symm
    (append_schemeAt_of_le_length s t h0leS).symm ?_ (append_blowupMorphism_of_lt_length s' t' hc) (append_blowupMorphism_of_lt_length s t hiS) ?_
  rw [concatComparisonMap_of_le g s t s' t' D D' (i + 1) hi h1le h1leS h1ts]
  exact strictPullback_map_eqToHom_congr D rfl h1ts h1ts _ _ _ _ _ _
  rw [concatComparisonMap_of_le g s t s' t' D D' i hi.le h0le h0leS h0ts]
  exact strictPullback_map_eqToHom_congr D rfl h0ts h0ts _ _ _ _ _ _
  have ht0 : 0 < t'.length := by omega
  have hup : ¬ (i + 1 ≤ s'.length) := by omega
  have ha1 : i + 1 - s'.length = 1 := by omega
  have pfA : i + 1 = s'.length + 1 := by omega
  have pfB : i + 1 = s.length + 1 := by omega
  have pf2' : 1 ≤ t'.toSequenceOfBlowups.length := by omega
  have h00 : 0 ≤ t'.toSequenceOfBlowups.length := zero_le _
  have h0lt : 0 < t'.toSequenceOfBlowups.length := by omega
  have hts0 : i ≤ s'.toSequenceOfBlowups.length := by omega
  have hileS : i ≤ s.length := by omega
  have hz : D'.comp 0 h00 ≫ bdIzH t = bdIzH t' ≫ D.lastMap :=
    by
    let hp := congrArg (fun e : t.toSequenceOfBlowups.schemeAt 0 ≅ s.obj s.length => isoH e) $ toSequenceOfBlowups_isoObjZero t
    let hq := congrArg (fun x => x ≫ D.lastMap) $ congrArg (fun e : t'.toSequenceOfBlowups.schemeAt 0 ≅ s'.obj s'.length => isoH e) $ toSequenceOfBlowups_isoObjZero t'
    subst hp
    subst hq
    exact D'.comp_zero
  refine isPullback_of_conj_eqToHom_iso (isPullback_blowupMorphism_of_strictPullbackBlowupSeq D' 0 h0lt pf2' h00)
    (append_schemeAt_eq_right_of_pos s' t' m176 pfA)
    (append_schemeAt_eq_right_of_pos s t m176 pfB).symm
    (t'.isoZero ≪≫ eqToIso (append_schemeAt_eq_last_of_eq_length s' t' hc).symm)
    (t.isoZero ≪≫ eqToIso (append_schemeAt_eq_last_of_eq_length s t $ tr_ hc hlen).symm) ?_ ?_ ?_ ?_
  rw [concatComparisonMap_of_not_le g s t s' t' D D' (i + 1) 1 hi hup ha1 pfA pf2' pfB,
    concatObjIsoRight_hom_of_pos s' t' 1 (i + 1) m176 pfA,
    concatObjIsoRight_inv_of_pos s t 1 (i + 1) m176 pfB]
  exact strictPullback_map_eqToHom_congr D' (rfl : 1 = 1) pf2' pf2' _ _ _ _ _ _
  rw [trans_hom, eqToIso.hom]
  exact append_blowupMorphism_of_eq_length s' t' i hc _ _
  rw [trans_hom, eqToIso.hom]
  exact append_blowupMorphism_of_eq_length s t i (tr_ hc hlen) _ _
  have hl : concatComparisonMap g s t s' t' D D' i hi.le =
      eqToHom (append_schemeAt_eq_last_of_eq_length s' t' hc) ≫ D.lastMap ≫
        eqToHom (append_schemeAt_eq_last_of_eq_length s t $ tr_ hc hlen).symm := by
    rw [concatComparisonMap_of_le g s t s' t' D D' i hi.le hc.le hileS hts0, strictPullback_map_eq_lastMap_of_eq D i hts0 $ tr_ hc hsl.symm]
    exact eqToHom_comp_eqToHom_conj_eq D.lastMap _ _ _ _ _ _ _ _
  exact eq_iso_inv_comp_comp_hom_of_comm_sq D.lastMap t'.isoZero t.isoZero (D'.comp 0 h00) hz
    (append_schemeAt_eq_last_of_eq_length s' t' hc).symm (append_schemeAt_eq_last_of_eq_length s t $ tr_ hc hlen).symm _ hl
  obtain ⟨a, rfl⟩ : ∃ a, i = s'.length + (a + 1) := ⟨i - s'.length - 1, by omega⟩
  have hgt' : s'.length < s'.length + (a + 1) := by omega
  have hgtS : s.length < s'.length + (a + 1) := by omega
  have hne : ¬ (s'.length + (a + 1) ≤ s'.length) := by omega
  have hne1 : ¬ (s'.length + (a + 1) + 1 ≤ s'.length) := by omega
  have hA : s'.length + (a + 1) - s'.length = a + 1 := by omega
  have hA2 : s'.length + (a + 1) + 1 - s'.length = a + 1 + 1 := by omega
  have hB : s'.length + (a + 1) - s.length = a + 1 := by omega
  have pfU1 : s'.length + (a + 1) = s'.length + (a + 1) := rfl
  let _a0 := a + 1 + 1
  have pfU1' : s'.length + (a + 1) + 1 = s'.length + _a0 := by omega
  have pfU3 : s'.length + (a + 1) = s.length + (a + 1) := by omega
  have pfU3' : s'.length + (a + 1) + 1 = s.length + _a0 := by omega
  have pfT : a + 1 ≤ t'.toSequenceOfBlowups.length := by omega
  have pfT' : a + 1 + 1 ≤ t'.toSequenceOfBlowups.length := by omega
  have halt : a + 1 < t'.toSequenceOfBlowups.length := by omega
  refine isPullback_of_conj_eqToHom (isPullback_blowupMorphism_of_strictPullbackBlowupSeq D' (a + 1) halt pfT' pfT)
    (append_schemeAt_eq_right_of_pos s' t' (succ_pos $ a + 1) pfU1')
    (append_schemeAt_eq_right_of_pos s t (succ_pos $ a + 1) pfU3').symm
    (append_schemeAt_eq_right_of_pos s' t' (succ_pos a) pfU1).symm
    (append_schemeAt_eq_right_of_pos s t (succ_pos a) pfU3).symm ?_ ?_ ?_ ?_
  rw [concatComparisonMap_of_not_le g s t s' t' D D' (s'.length + (a + 1) + 1) (a + 1 + 1) hi hne1
      hA2 pfU1' pfT' pfU3',
    concatObjIsoRight_hom_of_pos s' t' (a + 1 + 1) (s'.length + (a + 1) + 1)
      (succ_pos $ a + 1) pfU1',
    concatObjIsoRight_inv_of_pos s t (a + 1 + 1) (s'.length + (a + 1) + 1)
      (succ_pos $ a + 1) pfU3']
  exact strictPullback_map_eqToHom_congr D' rfl pfT' pfT' _ _ _ _ _ _
  rw [append_blowupMorphism_of_length_lt s' t' hgt']
  exact blowupMorphism_eqToHom_congr t' hA _ _ _ _
  rw [append_blowupMorphism_of_length_lt s t hgtS]
  exact blowupMorphism_eqToHom_congr t hB _ _ _ _
  rw [concatComparisonMap_of_not_le g s t s' t' D D' (s'.length + (a + 1)) (a + 1) hi.le hne hA pfU1
      pfT pfU3,
    concatObjIsoRight_hom_of_pos s' t' (a + 1) (s'.length + (a + 1)) (succ_pos a) pfU1,
    concatObjIsoRight_inv_of_pos s t (a + 1) (s'.length + (a + 1)) (succ_pos a) pfU3]
  exact strictPullback_map_eqToHom_congr D' rfl pfT pfT _ _ _ _ _ _
end

theorem eqToHom_trans_comp_comp_eqToHom_trans {A A1_ A2_ B2_ B1_ B : Sch}
    (a1 : A = A1_) (a2 : A1_ = A2_) (b1 : B2_ = B1_) (b2 : B1_ = B)
    (a : A = A2_) (b : B2_ = B) (c : A2_ ⟶ B2_) :
    eqToHom a1 ≫ eqToHom a2 ≫ c ≫ eqToHom b1 ≫ eqToHom b2 =
      eqToHom a ≫ c ≫ eqToHom b :=by simp_all
theorem eqToHom_trans_comp_comp_eqToHom_trans_eq_assoc {A A1_ A2_ B2_ B3 B1_ B : Sch}
    (a1 : A = A1_) (a2 : A1_ = A2_) (b1 : B2_ = B1_) (b2 : B1_ = B)
    (a : A = A2_) (b3 : B2_ = B3) (b4 : B3 = B) (c : A2_ ⟶ B2_) :
    eqToHom a1 ≫ eqToHom a2 ≫ c ≫ eqToHom b1 ≫ eqToHom b2 =
      eqToHom a ≫ (c ≫ eqToHom b3) ≫ eqToHom b4 :=by simp_all
theorem comap_iso_inv_eq_comap_of_comm_sq {P Q A B : Sch} (u : P ⟶ Q)
    (al_ : P ≅ A) (be_ : Q ≅ B) (G : A ⟶ B)
    (hz : u ≫ hom be_ = hom al_ ≫ G)
    (J : ISD P) (K : ISD Q) (hJ : J = comap K u) :
    comap J al_.inv = comap (comap K be_.inv) G := by
  have h1 : isoI al_ ≫ u ≫ isoH be_ = G := by simp_all
  subst hJ
  rw [← comap_comp, ← comap_comp, ← h1, assoc, assoc, hom_inv_id, comp_id]

theorem append_center_eq_comap_concatComparisonMap {X' X : Sch} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData $ s.obj s.length) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData $ s'.obj s'.length)
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
    (i : ℕ) (hi : i < (append s' t').length) :
    center (append s' t') i =
      comap (center (append s t) i) (concatComparisonMap g s t s' t' D D' i hi.le) := by
  have hlen : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans $ D.length_eq.trans $ toSequenceOfBlowups_length s
  have hilt : i < s'.length + t'.length := hi
  rw [concatComparisonMap_eq_dite g s t s' t' D D' i hi.le hlen hilt.le]
  by_cases h : i ≤ s'.length
  rw [dif_pos h]
  rcases h.lt_or_eq with hlt | heq
  have hs : i < s.length := hlt.trans_eq hlen
  have hlt' : i < s'.toSequenceOfBlowups.length := hlt.trans_eq (toSequenceOfBlowups_length s').symm
  let _a3 := D.comp i hlt'.le
  have hJ : center s' i = cmI (center s i) _a3 :=
    (toSequenceOfBlowups_center s' i).symm.trans
      (tr_ (D.center_eq i hlt')
        (congrArg (fun I : IdealSheafData (s.toSequenceOfBlowups.schemeAt i) => cmI I _a3)
          (toSequenceOfBlowups_center s i)))
  rw [append_center_of_lt_length s' t' hlt, append_center_of_lt_length s t hs]
  exact comap_eqToHom_eq_comap_of_eq_comap (append_schemeAt_of_le_length s' t' hlt.le)
    (append_schemeAt_of_le_length s t hs.le) _a3 _ (eqToHom_trans_comp_comp_eqToHom_trans _ _ _ _ _ _ _) _ _ hJ
  subst heq
  have h0 : 0 < t'.toSequenceOfBlowups.length := by
    rw [toSequenceOfBlowups_length]
    omega
  have hz1 : t.toSequenceOfBlowups.isoZero.hom = bdIzH t :=
    congrArg (fun e : t.toSequenceOfBlowups.schemeAt 0 ≅ s.obj s.length => isoH e) $ toSequenceOfBlowups_isoObjZero t
  have hz2 : t'.toSequenceOfBlowups.isoZero.hom = bdIzH t' :=
    congrArg (fun e : t'.toSequenceOfBlowups.schemeAt 0 ≅ s'.obj s'.length => isoH e) $ toSequenceOfBlowups_isoObjZero t'
  let _a4 := D'.comp 0 h0.le
  have hz : _a4 ≫ bdIzH t = bdIzH t' ≫ D.lastMap := by
    rw [← hz1, ← hz2]
    exact D'.comp_zero
  let _a5 := center t 0
  have hc0 : center t' 0 = cmI _a5 _a4 :=
    (toSequenceOfBlowups_center t' 0).symm.trans
      (tr_ (D'.center_eq 0 h0)
        (congrArg (fun I : IdealSheafData (t.toSequenceOfBlowups.schemeAt 0) => cmI I _a4)
          (toSequenceOfBlowups_center t 0)))
  obtain ⟨u, hzu, hcu⟩ : ∃ u,
      u ≫ bdIzH t = bdIzH t' ≫ D.lastMap ∧
        center t' 0 = cmI _a5 u :=
    ⟨_a4, hz, hc0⟩
  have hJ : cmI (center t' 0) t'.isoZero.inv =
      comap (cmI _a5 t.isoZero.inv) D.lastMap :=
    comap_iso_inv_eq_comap_of_comm_sq u t'.isoZero t.isoZero D.lastMap hzu (center t' 0)
      (center t 0) hcu
  rw [append_center_of_eq_length s' t' s'.length rfl,
    append_center_of_eq_length s t s'.length hlen]
  refine comap_eqToHom_eq_comap_of_eq_comap (append_schemeAt_eq_last_of_eq_length s' t' rfl)
    (append_schemeAt_eq_last_of_eq_length s t hlen) D.lastMap _ ?_ _ _ hJ
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  exact eqToHom_trans_comp_comp_eqToHom_trans_eq_assoc _ _ _ _ _ _ _ _
  rw [dif_neg h]
  have hk1 : i = s'.length + (i - s'.length) := by omega
  have hk2 : i = s.length + (i - s'.length) := by omega
  have hk : i - s'.length < t'.toSequenceOfBlowups.length := by
    rw [toSequenceOfBlowups_length]
    omega
  let _a0 := D'.comp (i - s'.length) hk.le
  let _a1 := center t $ i - s'.length
  let _a2 := center t' $ i - s'.length
  have hJ : _a2 =
      comap _a1 _a0 :=
    (toSequenceOfBlowups_center t' $ i - s'.length).symm.trans
      (tr_ (D'.center_eq (i - s'.length) hk)
        (congrArg
          (fun I : IdealSheafData (t.toSequenceOfBlowups.schemeAt $ i - s'.length) =>
            comap I _a0)
          (toSequenceOfBlowups_center t $ i - s'.length)))
  rw [append_center_eq_comap_concatObjIsoRight s' t' (i - s'.length) i hk1,
    append_center_eq_comap_concatObjIsoRight s t (i - s'.length) i hk2]
  exact comap_eq_comap_iso_hom_of_eq_comap (s'.concatObjIsoRight t' (i - s'.length) i hk1).hom
    (s.concatObjIsoRight t (i - s'.length) i hk2) _a0
    _a2 _a1 hJ
    (toSequenceOfBlowups_schemeAt t' $ i - s'.length).symm $ toSequenceOfBlowups_schemeAt t $ i - s'.length

end BlowupSequenceData

namespace StrictPullbackBlowupSeq

def concat {X' X : Sch} {g : X' ⟶ X} (s : BlowupSequenceData X)
    (t : BlowupSequenceData $ s.obj s.length) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData $ s'.obj s'.length)
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    StrictPullbackBlowupSeq g (append s' t').toSequenceOfBlowups (append s t).toSequenceOfBlowups :=
  BlowupSequenceData.toStrictPullbackSeq g (append s' t') (append s t)
    (BlowupSequenceData.append_length_eq_of_strictPullbackBlowupSeq g s t s' t' D D')
    (BlowupSequenceData.concatComparisonMap g s t s' t' D D')
    (BlowupSequenceData.concatComparisonMap_zero_comp_isoObjZero g s t s' t' D D')
    (BlowupSequenceData.isPullback_concatComparisonMap g s t s' t' D D')
    (BlowupSequenceData.append_center_eq_comap_concatComparisonMap g s t s' t' D D')

end StrictPullbackBlowupSeq

theorem isStrictPullbackBlowupSeq_append {X' X : Sch} {g : X' ⟶ X} (s : BlowupSequenceData X)
    (t : BlowupSequenceData $ s.obj s.length) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData $ s'.obj s'.length)
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g (append s' t').toSequenceOfBlowups (append s t).toSequenceOfBlowups :=
  (StrictPullbackBlowupSeq.concat s t s' t' D D').isStrictPullback

theorem emptyMarkedBlowupSequenceData_toBlowupSequenceData {k : Type} [Field k] {X : Sch}
    (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
    (E : Bdy X) :
    toBlowupSequenceData (emptyMarkedBlowupSequenceData p I m E) = BlowupSequenceData.empty X :=
  emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq p I m E

namespace MarkedBlowupSequenceData

section
variable {k : Type} [Field k]
theorem emptyMarkedBlowupSequenceData_append_isomorphic {X : Sch}
    (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
    (E : Bdy X)
    (t : MarkedBlowupSequenceData
      ((emptyMarkedBlowupSequenceData p I m E).proj (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length ≫ p)
      (ideal (emptyMarkedBlowupSequenceData p I m E) (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length) m
      (boundary (emptyMarkedBlowupSequenceData p I m E) (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance) :
    (append (emptyMarkedBlowupSequenceData p I m E) t hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have h0 :=
    emptyMarkedBlowupSequenceData_length p I m E
  have hpf : ∀ i, i = (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length + i := by
    intro i
    omega
  let _s0 := append (emptyMarkedBlowupSequenceData p I m E) t hinv
  have hlen : mbsLen _s0
      = mbsLen t := by
    have h1 : mbsLen _s0
        = (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length + mbsLen t :=
      MarkedBlowupSequenceData.append_length _ _ hinv
    omega
  have hzero : ((emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.concatObjIsoRight t.toBlowupSequenceData 0 0
        (hpf 0)).hom ≫ t.toBlowupSequenceData.isoZero.hom
      = eqToHom (BlowupSequenceData.append_schemeAt_eq_last_of_eq_length (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData
          t.toBlowupSequenceData h0.symm) := by
    rw [BlowupSequenceData.concatObjIsoRight_hom_zero, assoc, inv_hom_id]
    exact comp_id _
  refine BlowupSequenceData.toSequenceOfBlowups_isomorphic_of_iso
    _s0.toBlowupSequenceData t.toBlowupSequenceData hlen
    (fun i _ => (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.concatObjIsoRight t.toBlowupSequenceData i i
      (hpf i)) (hzero.trans (comp_id _).symm) ?_ ?_
  intro i _
  exact (BlowupSequenceData.concatObjIsoRight_hom_comm_blowupMorphism (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData t.toBlowupSequenceData
    i i $ hpf i).symm
  intro i _
  exact (BlowupSequenceData.append_center_eq_comap_concatObjIsoRight (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData
    t.toBlowupSequenceData i i $ hpf i).symm

theorem append_isomorphic_of_length_eq_zero {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
    {E : Bdy X} (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (ideal S S.toBlowupSequenceData.length) m
      (boundary S S.toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance) (h : T.toBlowupSequenceData.length = 0) :
    ((append S T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups).Isomorphic S.toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hlen : (S.toBlowupSequenceData.append T.toBlowupSequenceData).length = mbsLen S := by simp_all
  have key : (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups.Isomorphic S.toBlowupSequenceData.toSequenceOfBlowups := by
    refine BlowupSequenceData.toSequenceOfBlowups_isomorphic_of_iso (S.toBlowupSequenceData.append T.toBlowupSequenceData) S.toBlowupSequenceData
      hlen
      (fun i hi => eqToIso $ p40 S.toBlowupSequenceData T.toBlowupSequenceData
        (hi.trans_eq hlen)) ?_ ?_ ?_
    simp [eqToIso.hom]
    rw [BlowupSequenceData.append_isoObjZero_hom]
    intro i hi
    simp [eqToIso.hom]
    rw [BlowupSequenceData.append_blowupMorphism_of_lt_length S.toBlowupSequenceData T.toBlowupSequenceData $ lt_of_lt_of_eq hi hlen]
    simp
    intro i hi
    simp [eqToIso.hom]
    rw [BlowupSequenceData.append_center_of_lt_length S.toBlowupSequenceData T.toBlowupSequenceData $ lt_of_lt_of_eq hi hlen]
  rwa [toMarkedSequence_toSequenceOfBlowups $ append S T hinv, toMarkedSequence_toSequenceOfBlowups S]

theorem isStrictPullbackBlowupSeq_append {X' X : Sch}
    {p : X ⟶ Sp k} {p' : X' ⟶ Sp k}
    {I : ISD X} {I' : ISD X'} {m : ℕ}
    {E : Bdy X} {E' : Bdy X'} (g : X' ⟶ X)
    (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (ideal S S.toBlowupSequenceData.length) m
      (boundary S S.toBlowupSequenceData.length))
    (S' : MarkedBlowupSequenceData p' I' m E')
    (T' : MarkedBlowupSequenceData (S'.proj S'.toBlowupSequenceData.length ≫ p')
      (ideal S' S'.toBlowupSequenceData.length) m $ boundary S' S'.toBlowupSequenceData.length)
    (hinv : ComapIsoInvariance)
    (D : StrictPullbackBlowupSeq g S'.toMarkedSequenceOfBlowups.toSequenceOfBlowups S.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap T'.toMarkedSequenceOfBlowups.toSequenceOfBlowups T.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g ((append S' T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups)
      ((append S T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := _root_.FunctorialResolution.EmbeddedResolution.isStrictPullbackBlowupSeq_append (g := g) S.toBlowupSequenceData T.toBlowupSequenceData
    S'.toBlowupSequenceData T'.toBlowupSequenceData D D'
end

end MarkedBlowupSequenceData




namespace BlowupSequenceData

section
variable {X} (s : BlowupSequenceData X) (t1_ t2_ : BlowupSequenceData (s.obj s.length))
section
variable (e : ∀ i : ℕ, i ≤ t1_.length → (t1_.obj i ≅ t2_.obj i))
section
variable (j i) (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t1_.length)
noncomputable def appendSchemeAtIsoOfLengthLt :
    (append s t1_).obj i ≅ (append s t2_).obj i :=
  eqToIso (append_schemeAt_eq_right_of_pos s t1_ hj hij) ≪≫ e j hjl ≪≫
    (eqToIso $ append_schemeAt_eq_right_of_pos s t2_ hj hij).symm

theorem appendObjIsoRight_hom :
    (appendSchemeAtIsoOfLengthLt s t1_ t2_ e j i hij hj hjl).hom =
      eqToHom (append_schemeAt_eq_right_of_pos s t1_ hj hij) ≫ (e j hjl).hom ≫
        eqToHom (append_schemeAt_eq_right_of_pos s t2_ hj hij).symm := rfl
end

theorem appendObjIsoRight_congr
    j j' i (h : j = j')
    (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t1_.length)
    (hij' : i = s.length + j') (hj' : 0 < j') (hjl' : j' ≤ t1_.length) :
    appendSchemeAtIsoOfLengthLt s t1_ t2_ e j i hij hj hjl = appendSchemeAtIsoOfLengthLt s t1_ t2_ e j' i hij' hj' hjl' := by
  subst h
  rfl

noncomputable def appendSchemeAtIso
    (i : ℕ) (hi : i ≤ s.length + t1_.length) :
    (append s t1_).obj i ≅ (append s t2_).obj i :=
  if h : i ≤ s.length then
    eqToIso $ (append_schemeAt_of_le_length s t1_ h).trans (append_schemeAt_of_le_length s t2_ h).symm
  else
    appendSchemeAtIsoOfLengthLt s t1_ t2_ e (i - s.length) i (by omega) (by omega) $ by omega

theorem appendObjIso_hom_of_le
    (i : ℕ) (h : i ≤ s.length) (hi : i ≤ s.length + t1_.length) :
    (appendSchemeAtIso s t1_ t2_ e i hi).hom =
      eqToHom ((append_schemeAt_of_le_length s t1_ h).trans (append_schemeAt_of_le_length s t2_ h).symm) := by
  unfold appendSchemeAtIso
  simp [dif_pos h, eqToIso.hom]

theorem appendObjIso_eq_right_of_pos
    (i j : ℕ) (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t1_.length)
    (hi : i ≤ s.length + t1_.length) :
    appendSchemeAtIso s t1_ t2_ e i hi = appendSchemeAtIsoOfLengthLt s t1_ t2_ e j i hij hj hjl := by
  have hne : ¬ i ≤ s.length := by omega
  unfold appendSchemeAtIso
  rw [dif_neg hne]
  exact appendObjIsoRight_congr s t1_ t2_ e (i - s.length) j i (by omega) (by omega) (by omega)
    (by omega) hij hj hjl
end

theorem append_isomorphic_of_iso (hlen : t1_.length = t2_.length)
    (e : ∀ i : ℕ, i ≤ t1_.length → (t1_.obj i ≅ t2_.obj i))
    (hzero : (e 0 $ zero_le _).hom ≫ t2_.isoZero.hom = t1_.isoZero.hom)
    (hmap : ∀ (i : ℕ) (hi : i < t1_.length),
      (e (i + 1) hi).hom ≫ t2_.map i = t1_.map i ≫ (e i hi.le).hom)
    (hcenter : ∀ (i : ℕ) (hi : i < t1_.length),
      (center t2_ i).comap (e i hi.le).hom = center t1_ i) :
    (append s t1_).toSequenceOfBlowups.Isomorphic (append s t2_).toSequenceOfBlowups := by
  have hlenc : (append s t1_).length = (append s t2_).length := by simp_all
  refine toSequenceOfBlowups_isomorphic_of_iso (append s t1_) (append s t2_) hlenc
    (fun i hi => appendSchemeAtIso s t1_ t2_ e i $ hi.trans_eq $ append_length s t1_) ?_ ?_ ?_
  simp [appendObjIso_hom_of_le s t1_ t2_ e 0 $ zero_le s.length, append_isoObjZero_hom,
    eqToHom_trans_assoc]
  intro i hi
  have hi' := hi.trans_eq $ append_length s t1_
  rcases lt_trichotomy i s.length with hlt | heq | hgt
  have h1 : i + 1 ≤ s.length := by omega
  simp [appendObjIso_hom_of_le s t1_ t2_ e (i + 1) h1, appendObjIso_hom_of_le s t1_ t2_ e i hlt.le,
    append_blowupMorphism_of_lt_length s t2_ hlt, append_blowupMorphism_of_lt_length s t1_ hlt,
    assoc, eqToHom_trans, eqToHom_trans_assoc]
  subst heq
  have h0lt : 0 < t1_.length := by omega
  have h1le : 1 ≤ t1_.length := by omega
  simp [appendObjIso_eq_right_of_pos s t1_ t2_ e (s.length + 1) 1 rfl m176 h1le, appendObjIsoRight_hom,
    appendObjIso_hom_of_le s t1_ t2_ e s.length le_rfl, append_blowupMorphism_length,
    m146, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% (hmap 0 h0lt), reassoc_of% hzero]
  have hj1 : 0 < i - s.length := by omega
  have hj2 : i - s.length ≤ t1_.length := by omega
  have hj3 : i - s.length < t1_.length := by omega
  simp [appendObjIso_eq_right_of_pos s t1_ t2_ e (i + 1) (i - s.length + 1) (by omega) (by omega) $ by omega,
    appendObjIso_eq_right_of_pos s t1_ t2_ e i (i - s.length) (by omega) hj1 hj2, appendObjIsoRight_hom,
    append_blowupMorphism_of_length_lt s t2_ hgt, append_blowupMorphism_of_length_lt s t1_ hgt,
    assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp]
  rw [reassoc_of% (hmap (i - s.length) hj3)]
  intro i hi
  have hi' := hi.trans_eq $ append_length s t1_
  rcases lt_trichotomy i s.length with hlt | heq | hgt
  simp [appendObjIso_hom_of_le s t1_ t2_ e i hlt.le, append_center_of_lt_length s t2_ hlt,
    append_center_of_lt_length s t1_ hlt, ← comap_comp, eqToHom_trans]
  subst heq
  have h0lt : 0 < t1_.length := by omega
  have hz2 : t1_.isoZero.inv ≫ isoH (e 0 $ zero_le _) = t2_.isoZero.inv := by
    rw [inv_comp_eq, ← hzero, assoc, hom_inv_id, comp_id]
  simp [appendObjIso_hom_of_le s t1_ t2_ e s.length le_rfl, append_center_length,
    ← comap_comp, eqToHom_trans_assoc]
  rw [← hcenter 0 h0lt]
  simp [← comap_comp, assoc, hz2]
  have hj1 : 0 < i - s.length := by omega
  have hj2 : i - s.length ≤ t1_.length := by omega
  have hj3 : i - s.length < t1_.length := by omega
  simp [appendObjIso_eq_right_of_pos s t1_ t2_ e i (i - s.length) (by omega) hj1 hj2, appendObjIsoRight_hom,
    append_center_of_length_lt s t2_ hgt, append_center_of_length_lt s t1_ hgt,
    ← comap_comp,
    assoc, eqToHom_trans, eqToHom_refl, comp_id]
  rw [← hcenter (i - s.length) hj3]
  simp [← comap_comp]

theorem append_isomorphic_of_isomorphic (h : t1_.toSequenceOfBlowups.Isomorphic t2_.toSequenceOfBlowups) :
    (append s t1_).toSequenceOfBlowups.Isomorphic (append s t2_).toSequenceOfBlowups := by
  obtain ⟨hlen, e, hzero, hmap, hcenter⟩ := h
  have hl1 := toSequenceOfBlowups_length t1_
  have hl2 := toSequenceOfBlowups_length t2_
  refine append_isomorphic_of_iso s t1_ t2_ (by omega) (fun i hi => e i $ by omega) ?_ ?_ ?_
  rwa [← toSequenceOfBlowups_isoObjZero t2_, ← toSequenceOfBlowups_isoObjZero t1_]
  intro i hi
  rw [← toSequenceOfBlowups_blowupMorphism t2_ i, ← toSequenceOfBlowups_blowupMorphism t1_ i]
  exact hmap i $ by omega
  intro i hi
  rw [← toSequenceOfBlowups_center t2_ i, ← toSequenceOfBlowups_center t1_ i]
  exact hcenter i $ by omega
end

end BlowupSequenceData

namespace MarkedBlowupSequenceData

theorem append_isomorphic_of_isomorphic {k : Type} [Field k] {X : Sch}
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
    {E : Bdy X} (S : MarkedBlowupSequenceData p I m E)
    (T1_ T2_ : MarkedBlowupSequenceData (S.proj S.length ≫ p) (ideal S S.length) m $ boundary S S.length)
    (hinv : ComapIsoInvariance)
    (h : T1_.toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic T2_.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    ((append S T1_ hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups).Isomorphic
      ((append S T2_ hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  rw [toMarkedSequence_toSequenceOfBlowups, toMarkedSequence_toSequenceOfBlowups] at h
  have key := BlowupSequenceData.append_isomorphic_of_isomorphic S.toBlowupSequenceData T1_.toBlowupSequenceData
    T2_.toBlowupSequenceData h
  rw [toMarkedSequence_toSequenceOfBlowups, toMarkedSequence_toSequenceOfBlowups, append_toBlowupSequenceData,
    append_toBlowupSequenceData]
  exact key

end MarkedBlowupSequenceData




namespace BlowupSequenceData

variable {X : Sch}

section
variable (d : BlowupSequenceData X)
section
variable {i i' : ℕ} (h : i ≤ i')
def transitionMap : d.obj i' ⟶ d.obj i :=
  d.toSequenceOfBlowups.transitionMap h

theorem toSequenceOfBlowups_transitionMap :
    d.toSequenceOfBlowups.transitionMap h = d.transitionMap h := rfl
end

theorem transitionMap_comp_transitionMap {i j l} (hij : i ≤ j) (hjl : j ≤ l) :
    d.transitionMap hjl ≫ d.transitionMap hij = d.transitionMap (hij.trans hjl) :=
  d.toSequenceOfBlowups.transitionMap_trans hij hjl

theorem transitionMap_refl i : d.transitionMap (le_refl i) = 𝟙 (d.obj i) := d.toSequenceOfBlowups.transitionMap_self_eq_id $ le_refl i

theorem transitionMap_succ i : d.transitionMap (le_succ i) = d.map i := by
  exact st_ (d.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i) $ d.toSequenceOfBlowups_blowupMorphism i

@[reassoc]
theorem transitionMap_zero_comp_isoObjZero_hom (n : ℕ) :
    d.transitionMap (zero_le n) ≫ d.isoZero.hom = projectionToBase d n := by
  have h := d.toSequenceOfBlowups.projectionToBase_def n
  rw [p36, BlowupSequenceData.toSequenceOfBlowups_transitionMap, toSequenceOfBlowups_isoObjZero] at h
  exact sy_ h
end

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
theorem append_schemeAt_length_add_zero :
    (append s t).obj (s.length + 0) = s.obj s.length := by
  exact tr_ (append_schemeAt_of_le_length s t $ le_of_eq $ Nat.add_zero _) $ congrArg s.obj $ Nat.add_zero _

theorem append_schemeAt_length_add_succ
    i : (append s t).obj (s.length + (i + 1)) = t.obj (i + 1) := by
  have h : s.length < s.length + (i + 1) := by omega
  have h2 : s.length + (i + 1) - s.length = i + 1 := by omega
  rw [append_schemeAt_of_length_lt s t h, h2]
end

def concatObjAddIso (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) :
    ∀ i : ℕ, (append s t).obj (s.length + i) ≅ t.obj i
  | 0 => eqToIso (append_schemeAt_length_add_zero s t) ≪≫ t.isoZero.symm
  | (i + 1) => eqToIso $ append_schemeAt_length_add_succ s t i

section
variable {Y} (d : BlowupSequenceData Y)
theorem eqToHom_comp_blowupMorphism_zero_isoObjZero_cancel {U V}
    (h1 : U = d.obj 1) (h2 : Y = V) (h3 : V = Y) (h4 : U = d.obj 1) :
    (eqToHom h1 ≫ d.map 0 ≫ d.isoZero.hom ≫ eqToHom h2) ≫ eqToHom h3 ≫ d.isoZero.inv =
      eqToHom h4 ≫ d.map 0 := by
  subst h2
  simp

theorem eqToHom_comp_blowupMorphism_congr {a b} (hab : a = b)
    {U V} (hU : U = d.obj (a + 1)) (hV : V = d.obj a)
    e1 e2 :
    (eqToHom hU ≫ d.map a ≫ eqToHom hV.symm) ≫ eqToHom e1 = eqToHom e2 ≫ d.map b :=by simp_all
end

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
theorem append_blowupMorphism_zero_comp_concatObjAddIso :
    (append s t).map s.length ≫ hom (concatObjAddIso s t 0) =
      hom (concatObjAddIso s t 1) ≫ t.map 0 := by
  rw [append_blowupMorphism_length s t]
  exact eqToHom_comp_blowupMorphism_zero_isoObjZero_cancel t (append_schemeAt_length_succ s t)
    (append_schemeAt_of_le_length s t (le_refl s.length)).symm (append_schemeAt_length_add_zero s t)
    (append_schemeAt_length_add_succ s t 0)

theorem append_blowupMorphism_succ_comp_concatObjAddIso k :
    (append s t).map (s.length + (k + 1)) ≫ hom (concatObjAddIso s t $ k + 1) =
      hom (concatObjAddIso s t $ k + 1 + 1) ≫ t.map (k + 1) := by
  have hgt : s.length < s.length + (k + 1) := by omega
  have hab : s.length + (k + 1) - s.length = k + 1 := by omega
  rw [append_blowupMorphism_of_length_lt s t hgt]
  exact eqToHom_comp_blowupMorphism_congr t hab (append_schemeAt_succ_of_length_lt s t hgt) (append_schemeAt_of_length_lt s t hgt)
    (append_schemeAt_length_add_succ s t k) $ append_schemeAt_length_add_succ s t $ k + 1

@[reassoc]
theorem append_blowupMorphism_comp_concatObjAddIso (i : ℕ) :
    (append s t).map (s.length + i) ≫ hom (concatObjAddIso s t i) =
      hom (concatObjAddIso s t $ i + 1) ≫ t.map i := by
  cases i with
  | zero => exact append_blowupMorphism_zero_comp_concatObjAddIso s t
  | succ k => exact append_blowupMorphism_succ_comp_concatObjAddIso s t k

@[reassoc]
theorem append_transitionMap_comp_concatObjAddIso {i i' : ℕ}
    (h : i ≤ i') :
    (append s t).transitionMap (Nat.add_le_add_left h s.length) ≫ (concatObjAddIso s t i).hom =
      (concatObjAddIso s t i').hom ≫ t.transitionMap h := by
  induction i', h using le_induction with
  | base =>
      rw [transitionMap_refl, transitionMap_refl, id_comp, comp_id]
  | succ n hn ih =>
      calc (append s t).transitionMap (Nat.add_le_add_left (Nat.le_succ_of_le hn) s.length) ≫
            (concatObjAddIso s t i).hom
          = ((append s t).map (s.length + n) ≫
              (append s t).transitionMap (Nat.add_le_add_left hn s.length)) ≫
              (concatObjAddIso s t i).hom := by
            rw [← (append s t).transitionMap_succ $ s.length + n, (append s t).transitionMap_comp_transitionMap (Nat.add_le_add_left hn s.length) $ Nat.le_succ $ s.length + n]
        _ = (append s t).map (s.length + n) ≫
              ((append s t).transitionMap (add_le_add_left hn s.length) ≫ isoH (concatObjAddIso s t i)) :=
            assoc _ _ _
        _ = (append s t).map (s.length + n) ≫ (isoH (concatObjAddIso s t n) ≫ t.transitionMap hn) := by
            rw [ih]
        _ = ((append s t).map (s.length + n) ≫ isoH (concatObjAddIso s t n)) ≫ t.transitionMap hn :=
            (assoc _ _ _).symm
        _ = (isoH (concatObjAddIso s t $ n + 1) ≫ t.map n) ≫ t.transitionMap hn := by
            rw [append_blowupMorphism_comp_concatObjAddIso]
        _ = isoH (concatObjAddIso s t $ n + 1) ≫ (t.map n ≫ t.transitionMap hn) := assoc _ _ _
        _ = isoH (concatObjAddIso s t $ n + 1) ≫ t.transitionMap (le_succ_of_le hn) := by
            rw [← t.transitionMap_succ n, t.transitionMap_comp_transitionMap hn $ Nat.le_succ n]
end

end BlowupSequenceData

structure SequenceOfBlowupsPullback {X X' : Sch} (ph_ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) where
  idx : ℕ → ℕ
  map : ∀ j : ℕ, j ≤ s'.length → (s'.schemeAt j ⟶ s.schemeAt (idx j))
  idx_length : idx s'.length = s.length
  idx_lt : ∀ j : ℕ, j < s'.length → idx j < s.length
  idx_strictMono : ∀ j : ℕ, j < s'.length → idx j < idx (j + 1)
  isPullback : ∀ j hj,
    IsPullback (map j hj) (projectionToBase s' j) (projectionToBase s $ idx j) ph_
  step : ∀ j hj,
    transitionMapSucc s' j ≫ map j (le_of_lt hj) =
      map (j + 1) hj ≫ s.transitionMap (le_of_lt $ idx_strictMono j hj)
  center_comap : ∀ j hj,
    center s' j = comap (center s $ idx j) (map j $ le_of_lt hj)
  center_ne_top : ∀ j : ℕ, j < s'.length → center s' j ≠ ⊤
  omitted : ∀ i, i < s.length → (∀ j : ℕ, j < s'.length → idx j ≠ i) →
    ∀ z : ↥(s.schemeAt i), z ∈ support (center s i) → ∀ x' : ↥X',
      ph_.base x' ≠ (projectionToBase s i).base z

namespace SequenceOfBlowupsPullback

variable {X X' : Sch} {ph_ : X' ⟶ X}

section
variable {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback ph_ s' s)
def lastMap :
    s'.schemeAt s'.length ⟶ s.schemeAt s.length :=
  c.map s'.length le_rfl ≫ eqToHom (congrArg s.schemeAt c.idx_length)

section
variable (i : ℕ) (hi : i ≤ s'.length)
def isoPullback : s'.schemeAt i ≅ pullback ph_ (projectionToBase s $ c.idx i) :=
  ((c.isPullback i hi).flip).isoPullback

theorem pullbackIso_hom_fst :
    hom (isoPullback c i hi) ≫ pullback.fst ph_ (projectionToBase s $ c.idx i) = projectionToBase s' i :=
  isoPullback_hom_fst _

theorem pullbackIso_hom_snd :
    hom (isoPullback c i hi) ≫ pullback.snd ph_ (projectionToBase s $ c.idx i) = c.map i hi :=
  isoPullback_hom_snd _
end

theorem index_lt_index_of_lt :
    ∀ i j, j ≤ s'.length → i < j → c.idx i < c.idx j := by
  intro i j
  induction j with
  | zero => intro _ h; exact absurd h $ not_lt_zero i
  | succ n ih =>
      intro hn hij
      have hn' := lt_of_succ_le hn
      have hstep := c.idx_strictMono n hn'
      by_cases hcase : i < n
      exact lt_trans (ih (le_of_lt hn') hcase) hstep
      have hie : i = n := by omega
      subst hie
      exact hstep
end

section
variable {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback ph_ d'.toSequenceOfBlowups d.toSequenceOfBlowups)
section
variable (j : ℕ) (hj : j < d'.length)
include hj
theorem blowupSequenceData_index_lt_length :
    c.idx j < d.length := by
  have h := hj
  rw [← p14] at h
  have h2 := c.idx_lt j h
  rwa [p14] at h2

theorem blowupSequenceData_index_lt_index_succ :
    c.idx j < c.idx (j + 1) :=
  c.idx_strictMono j (by rw [p14]; exact hj)

@[reassoc]
theorem blowupSequenceData_blowupMorphism_comp_map :
    d'.map j ≫ c.map j (le_of_lt hj) =
      c.map (j + 1) hj ≫ d.transitionMap (le_of_lt $ c.blowupSequenceData_index_lt_index_succ j hj) := by
  have hj' := hj
  rw [← p14] at hj'
  have h := c.step j hj'
  rwa [p50] at h
end

theorem index_length_eq_length : c.idx d'.length = d.length := by
  simpa only [p14] using c.idx_length
end

theorem isPullback_comp_eqToHom {A B Y : Sch} {ps_ : B ⟶ A} {t : SequenceOfBlowups A}
    {n m : ℕ} (hn : n = m) (f : Y ⟶ t.schemeAt n) (g : Y ⟶ B)
    (h : IsPullback f g (projectionToBase t n) ps_) :
    IsPullback (f ≫ eqToHom (congrArg t.schemeAt hn)) g (projectionToBase t m) ps_ := by
  subst hn
  rwa [eqToHom_refl, comp_id]

theorem exists_mem_support_of_ne_top {Y : Sch} (J : ISD Y) (h : J ≠ ⊤) :
    ∃ x, x ∈ support J := by
  by_contra hc
  push Not at hc
  refine h $ mp_ (support_eq_bot_iff J) ?_
  ext y
  simpa using hc y

section
variable {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback ph_ s' s)
include c
theorem isPullback_lastMap :
    IsPullback c.lastMap (projectionToBase s' s'.length) (projectionToBase s s.length) ph_ := by
  show IsPullback (c.map s'.length le_rfl ≫ eqToHom (congrArg s.schemeAt c.idx_length))
      (sbPrj s' s'.length) (sbPrj s s.length) ph_
  exact isPullback_comp_eqToHom c.idx_length _ _ $ c.isPullback s'.length le_rfl

theorem isPullbackSequenceOfBlowups : IsPullbackBlowupSequence ph_ s' s := by
  refine ⟨c.idx, fun i hi => isoPullback c i hi, c.idx_lt, index_lt_index_of_lt c, c.idx_length,
    ?_, ?_, ?_, ?_⟩
  intro i hi
  constructor
  rintro ⟨x, hx⟩
  by_contra hcon
  push Not at hcon
  have _i9 : bsM ph_ (bsM (pullback.fst ph_ $ sbPrj s i) x) = bsM (sbPrj s i) (bsM (pullback.snd ph_ $ sbPrj s i) x) := by
    let g := sbPrj s i
    have h : bsM (pullback.fst ph_ g ≫ ph_) x = bsM (pullback.snd ph_ g ≫ g) x := by
      rw [pullback.condition]
    simpa using h
  exact c.omitted i hi hcon _ (mp_ mem_support_comap hx) _
    _i9
  rintro ⟨j, hj, rfl⟩
  refine exists_mem_support_of_ne_top _ ?_
  intro htop
  refine c.center_ne_top j hj ?_
  rw [c.center_comap j hj, ← pullbackIso_hom_snd c j $ le_of_lt hj,
    comap_comp, htop,
    comap_top]
  intro i hi
  exact pullbackIso_hom_fst c i hi
  intro i hi hr
  refine pullback.hom_ext ?_ ?_
  rw [assoc, pullbackIso_hom_fst, assoc, SequenceOfBlowups.pullbackTransitionMap_comp_fst,
    pullbackIso_hom_fst, blowupMorphism_eq_transitionMap, transitionMap_comp_projectionToBase]
  rw [assoc, pullbackIso_hom_snd, assoc, SequenceOfBlowups.pullbackTransitionMap_comp_snd,
    ← assoc, pullbackIso_hom_snd]
  exact c.step i hi
  intro i hi
  rw [pullbackIso_hom_snd]
  exact c.center_comap i hi
end

section

section
variable {Y : Sch}
section
variable (a : BlowupSequenceData Y) (b : BlowupSequenceData (a.obj a.length))
theorem append_projectionToBase_eq_of_le_length {n i : ℕ} (hni : n = i) (hi : i ≤ a.length)
    (hobj : a.obj i = (append a b).obj n) :
    (append a b).toSequenceOfBlowups.projectionToBase n = eqToHom hobj.symm ≫ a.toSequenceOfBlowups.projectionToBase i := by
  subst hni
  simp [BlowupSequenceData.projectionToBase_append_of_le_length a b hi]
  rfl

theorem append_projectionToBase_length_add i :
    (append a b).projectionToBase (a.length + i) =
      hom (BlowupSequenceData.concatObjAddIso a b i) ≫ b.projectionToBase i ≫ a.projectionToBase a.length := by
  cases i with
  | zero =>
    let _a0 := isoH $ BlowupSequenceData.concatObjAddIso a b 0
    have h2 : _a0 =
        eqToHom (BlowupSequenceData.append_schemeAt_length_add_zero a b) ≫ b.isoZero.inv := rfl
    show (append a b).projectionToBase a.length =
        _a0 ≫ b.projectionToBase 0 ≫ a.projectionToBase a.length
    rw [BlowupSequenceData.projectionToBase_append_of_le_length a b $ le_refl a.length, h2, b.projectionToBase_zero]
    simp
  | succ n =>
    have hgt : a.length < a.length + (n + 1) := by omega
    have hsub : a.length + (n + 1) - a.length = n + 1 := by omega
    have h3 : hom (BlowupSequenceData.concatObjAddIso a b $ n + 1) =
        eqToHom (BlowupSequenceData.append_schemeAt_length_add_succ a b n) := rfl
    rw [BlowupSequenceData.projectionToBase_append_of_length_lt a b hgt, projectionToBase_congr b hsub, h3]
    simp

theorem append_projectionToBase_eq_of_eq_length_add {n i : ℕ} (hni : n = a.length + i)
    (hobj : (append a b).obj n = (append a b).obj (a.length + i)) :
    (append a b).toSequenceOfBlowups.projectionToBase n =
      (eqToHom hobj ≫ hom (BlowupSequenceData.concatObjAddIso a b i)) ≫
        b.toSequenceOfBlowups.projectionToBase i ≫ a.toSequenceOfBlowups.projectionToBase a.length := by
  subst hni
  simp [append_projectionToBase_length_add a b i, eqToHom_refl, id_comp]
  rfl
end

section
variable (d : BlowupSequenceData Y)
theorem transitionMap_congr {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b')
    (E1 : d.obj b = d.obj b') (E2 : d.obj a' = d.obj a) :
    d.transitionMap h = eqToHom E1 ≫ d.transitionMap h' ≫ eqToHom E2 := by
  subst ha
  subst hb
  simp

section
variable {a b : ℕ}
theorem center_comap_comp_eqToHom_congr
    (hab : a = b) {Z Z' W : Sch} (p : Z ⟶ Z') (f : Z' ⟶ W)
    (hW : W = d.obj a) (hW' : W = d.obj b) :
    comap (d.center a) (p ≫ f ≫ eqToHom hW) = comap (d.center b) (p ≫ f ≫ eqToHom hW') := by
  subst hab
  rfl

theorem center_comap_eqToHom_congr__b11
    (hab : a = b) {W} (hW : W = d.obj a) (hW' : W = d.obj b) :
    comap (d.center a) (eqToHom hW) = comap (d.center b) (eqToHom hW') := by
  subst hab
  rfl

theorem center_comap_comp_eqToHom
    (hab : b = a) {Z : Sch} (v : Z ⟶ d.obj b) (q : d.obj b = d.obj a) :
    comap (d.center a) (v ≫ eqToHom q) = comap (d.center b) v := by
  subst hab
  simp
end

end

section
variable (s : BlowupSequenceData Y) (t : BlowupSequenceData (s.obj s.length))
section
variable {a b : ℕ}
theorem append_transitionMap_of_le_length (hab : a ≤ b) (hb : b ≤ s.length) :
    (append s t).transitionMap hab =
      eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hb) ≫ s.transitionMap hab ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t $ le_trans hab hb).symm := by
  revert hb
  induction b, hab using le_induction with
  | base =>
      intro hb
      rw [BlowupSequenceData.transitionMap_refl, BlowupSequenceData.transitionMap_refl]
      simp
  | succ m hm ih =>
      intro hb
      have hmlt := hb
      rw [← BlowupSequenceData.transitionMap_comp_transitionMap (append s t) hm $ le_succ m, BlowupSequenceData.transitionMap_succ,
        BlowupSequenceData.append_blowupMorphism_of_lt_length s t hmlt, ih $ le_of_lt hmlt, ← BlowupSequenceData.transitionMap_comp_transitionMap s hm $ le_succ m,
        ← BlowupSequenceData.transitionMap_succ s m]
      simp

section
variable (h : a ≤ b) (hd : s.length + a ≤ s.length + b)
theorem concatObjAddIso_inv_comp_transitionMap :
    inv (BlowupSequenceData.concatObjAddIso s t b) ≫ (append s t).transitionMap hd =
      t.transitionMap h ≫ inv (BlowupSequenceData.concatObjAddIso s t a) := by
  let _a0 := BlowupSequenceData.concatObjAddIso s t b
  let _a1 := BlowupSequenceData.concatObjAddIso s t a
  let _a2 := (append s t).transitionMap hd
  calc _a0.inv ≫ _a2
      = isoI _a0 ≫
          (_a2 ≫ isoH _a1) ≫
            inv _a1 := by simp
    _ = isoI _a0 ≫
          (isoH _a0 ≫ t.transitionMap h) ≫
            inv _a1 := by rw [BlowupSequenceData.append_transitionMap_comp_concatObjAddIso s t h]
    _ = t.transitionMap h ≫ isoI _a1 := by simp

theorem concatObjAddIso_inv_comp_transitionMap_assoc
    {W : Sch} (g : (append s t).obj (s.length + a) ⟶ W) :
    inv (BlowupSequenceData.concatObjAddIso s t b) ≫ (append s t).transitionMap hd ≫ g =
      t.transitionMap h ≫ inv (BlowupSequenceData.concatObjAddIso s t a) ≫ g := by
  rw [← assoc, concatObjAddIso_inv_comp_transitionMap s t h hd, assoc]
end
end

section
variable {m i} (hm : m ≤ s.length) (h : m ≤ s.length + i)
theorem concatObjAddIso_inv_comp_transitionMap_of_le_length :
    inv (BlowupSequenceData.concatObjAddIso s t i) ≫ (append s t).transitionMap h =
      t.transitionMap (zero_le i) ≫ t.isoZero.hom ≫ s.transitionMap hm ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm := by
  let _a1 := isoI $ BlowupSequenceData.concatObjAddIso s t 0
  have h2 : _a1 =
      (bdIzH t) ≫ eqToHom (p40 s t $ le_refl s.length).symm := rfl
  let _a3 := le_add_right s.length i
  let _a0 := append s t
  let _a2 := isoI $ BlowupSequenceData.concatObjAddIso s t i
  calc _a2 ≫ _a0.transitionMap h
      = _a2 ≫
          _a0.transitionMap _a3 ≫ _a0.transitionMap hm := by
        rw [BlowupSequenceData.transitionMap_comp_transitionMap]
    _ = (t.transitionMap (zero_le i) ≫ _a1) ≫
          _a0.transitionMap hm := by
        rw [← assoc, concatObjAddIso_inv_comp_transitionMap s t (zero_le i) _a3]
    _ = t.transitionMap (zero_le i) ≫ bdIzH t ≫ s.transitionMap hm ≫
          eqToHom (p40 s t hm).symm := by
        rw [h2, append_transitionMap_of_le_length s t hm $ le_refl s.length]
        simp

theorem concatObjAddIso_inv_comp_transitionMap_of_le_length_assoc
    {W : Sch} (g : (append s t).obj m ⟶ W) :
    inv (BlowupSequenceData.concatObjAddIso s t i) ≫ (append s t).transitionMap h ≫ g =
      t.transitionMap (zero_le i) ≫ t.isoZero.hom ≫ s.transitionMap hm ≫
        eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s t hm).symm ≫ g := by
  rw [← assoc, concatObjAddIso_inv_comp_transitionMap_of_le_length s t hm h]
  simp
end

theorem concatObjAddIso_zero_hom :
    hom (BlowupSequenceData.concatObjAddIso s t 0) =
      eqToHom (BlowupSequenceData.append_schemeAt_length_add_zero s t) ≫ t.isoZero.inv := rfl

theorem projectionToBase_append_length_add (n : ℕ) :
    (append s t).projectionToBase (s.length + n) =
      hom (BlowupSequenceData.concatObjAddIso s t n) ≫ t.projectionToBase n ≫ s.projectionToBase s.length := by
  induction n with
  | zero =>
      have hA : hom (BlowupSequenceData.concatObjAddIso s t 0) ≫ t.projectionToBase 0 ≫ s.projectionToBase s.length =
          eqToHom (BlowupSequenceData.append_schemeAt_length_add_zero s t) ≫ s.projectionToBase s.length := by
        rw [concatObjAddIso_zero_hom, p23, m146, m213]
      exact tr_ (tr_ (BlowupSequenceData.projectionToBase_append_of_le_length s t $ le_of_eq $ Nat.add_zero s.length)
        (rfl)) hA.symm
  | succ n ih =>
      let _a0 := append s t
      have hs : _a0.projectionToBase (s.length + (n + 1)) =
          _a0.map (s.length + n) ≫ _a0.projectionToBase (s.length + n) :=
        p43 (append s t) $ s.length + n
      rw [hs, ih, BlowupSequenceData.append_blowupMorphism_comp_concatObjAddIso_assoc, ← assoc $ t.map n,
        ← p43]
end
end

section
variable {A B C D E F : Sch}
theorem comp_assoc_outer (p : A ⟶ B) (q : B ⟶ C)
    (f : C ⟶ D) (g : D ⟶ E) (w : E ⟶ F) :
    p ≫ (q ≫ f ≫ g) ≫ w = (p ≫ q) ≫ f ≫ g ≫ w := by
  simp

theorem comp_assoc_inner_pair
    (f1 : A ⟶ B) (f2 : B ⟶ C) (f3 : C ⟶ D) (f4 : D ⟶ E) (f5 : E ⟶ F) :
    f1 ≫ f2 ≫ f3 ≫ f4 ≫ f5 = f1 ≫ (f2 ≫ f3) ≫ f4 ≫ f5 := by
  rw [assoc]
end

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
section
variable (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (c : SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
section
variable (j : ℕ)
def concatIndex : ℕ :=
  if j < s'.length then c.idx j else s.length + e.idx (j - s'.length)

section
variable (h : j < s'.length)
include h
theorem concatIndex_of_lt :
    concatIndex s t s' t' c e j = c.idx j := if_pos h

theorem append_schemeAt_concatIndex_of_lt :
    s.obj (c.idx j) = (append s t).obj (concatIndex s t s' t' c e j) := by
  rw [concatIndex_of_lt s t s' t' c e j h]
  exact sy_ $ p40 s t $ le_of_lt $ c.blowupSequenceData_index_lt_length j h

def concatMapOfLtLength :
    (append s' t').obj j ⟶ (append s t).obj (concatIndex s t s' t' c e j) :=
  eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' $ le_of_lt h) ≫ c.map j (le_of_lt h) ≫
    eqToHom (append_schemeAt_concatIndex_of_lt s t s' t' c e j h)
end

theorem concatIndex_of_ge (h : s'.length ≤ j) :
    concatIndex s t s' t' c e j = s.length + e.idx (j - s'.length) := if_neg $ not_lt.2 h

theorem append_schemeAt_concatIndex_of_le (h : s'.length ≤ j) :
    (append s t).obj (s.length + e.idx (j - s'.length)) =
      (append s t).obj (concatIndex s t s' t' c e j) := by
  rw [concatIndex_of_ge s t s' t' c e j h]

theorem concatIndex_lt_length_add_length
    (hj : j < s'.length + t'.length) :
    concatIndex s t s' t' c e j < s.length + t.length := by
  by_cases h : j < s'.length
  rw [concatIndex_of_lt s t s' t' c e j h]
  have hc := c.blowupSequenceData_index_lt_length j h
  omega
  have hge := not_lt.1 h
  rw [concatIndex_of_ge s t s' t' c e j hge]
  have hlt : j - s'.length < t'.length := by omega
  have he := e.blowupSequenceData_index_lt_length (j - s'.length) hlt
  omega

theorem concatIndex_lt_concatIndex_succ
    (hj : j < s'.length + t'.length) :
    concatIndex s t s' t' c e j < concatIndex s t s' t' c e (j + 1) := by
  by_cases h : j < s'.length
  rw [concatIndex_of_lt s t s' t' c e j h]
  by_cases h2 : j + 1 < s'.length
  rw [concatIndex_of_lt s t s' t' c e (j + 1) h2]
  exact c.blowupSequenceData_index_lt_index_succ j h
  rw [concatIndex_of_ge s t s' t' c e (j + 1) $ by omega]
  have hlt := c.blowupSequenceData_index_lt_length j h
  omega
  have hge : s'.length ≤ j := by omega
  rw [concatIndex_of_ge s t s' t' c e j hge,
    concatIndex_of_ge s t s' t' c e (j + 1) $ by omega]
  have hsub : j + 1 - s'.length = (j - s'.length) + 1 := by omega
  rw [hsub]
  have hlt : j - s'.length < t'.length := by omega
  have hstep :=
    e.blowupSequenceData_index_lt_index_succ (j - s'.length) hlt
  omega
end

def concatMapAddLength (i : ℕ) (hi : i ≤ t'.length) :
    (append s' t').obj (s'.length + i) ⟶ (append s t).obj (s.length + e.idx i) :=
  hom (BlowupSequenceData.concatObjAddIso s' t' i) ≫ e.map i hi ≫ inv (BlowupSequenceData.concatObjAddIso s t $ e.idx i)

theorem concatMapAddLength_congr {a b} (hab : a = b)
    (ha : a ≤ t'.length) (hb : b ≤ t'.length) {W}
    (h1 : (append s' t').obj (s'.length + b) = (append s' t').obj (s'.length + a))
    (h2 : (append s t).obj (s.length + e.idx a) = W)
    (h2' : (append s t).obj (s.length + e.idx b) = W) :
    eqToHom h1 ≫ concatMapAddLength s t s' t' c e a ha ≫ eqToHom h2 =
      concatMapAddLength s t s' t' c e b hb ≫ eqToHom h2' := by
  subst hab
  rw [eqToHom_refl, id_comp]

theorem concatIndex_length_add_length :
    concatIndex s t s' t' c e (s'.length + t'.length) = s.length + t.length := by
  rw [concatIndex_of_ge s t s' t' c e (s'.length + t'.length) $ le_add_right _ _]
  have h : s'.length + t'.length - s'.length = t'.length := by omega
  rw [h, e.index_length_eq_length]
end

theorem append_center_length_add
    (n : ℕ) :
    (append s t).center (s.length + n) =
      comap (t.center n) (BlowupSequenceData.concatObjAddIso s t n).hom := by
  cases n with
  | zero =>
    exact m32 (BlowupSequenceData.append_center_length s t) $ sy_ $ m56 (t.center 0) (eqToHom $ p40 s t $ le_refl s.length) t.isoZero.inv
  | succ k =>
    have hlt : s.length < s.length + (k + 1) := by omega
    have hsub : s.length + (k + 1) - s.length = k + 1 := by omega
    exact m32 (BlowupSequenceData.append_center_of_length_lt s t hlt) $ center_comap_eqToHom_congr__b11 t hsub (BlowupSequenceData.append_schemeAt_of_length_lt s t hlt) $ BlowupSequenceData.append_schemeAt_length_add_succ s t k
end

section
variable {A B C D : Sch} (g : A ⟶ B)
theorem comp_comp_inv_comp_hom m (ι : D ≅ C) :
    (g ≫ m ≫ inv ι) ≫ hom ι = g ≫ m :=by simp_all
theorem comp_comp_eqToHom_comp_eqToHom f
    (h1 : C = D) (h2 : D = C) :
    (g ≫ f ≫ eqToHom h1) ≫ eqToHom h2 = g ≫ f :=by simp_all
end

section
variable {s' : BlowupSequenceData X'} {s : BlowupSequenceData X}
section
variable (c : SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
section
variable (j : ℕ)
def mapOfToSequenceOfBlowups (hj : j ≤ s'.length) :
    s'.obj j ⟶ s.obj (c.idx j) := c.map j hj

theorem blowupMorphism_comp_lowerMap (hj : j < s'.length) :
    s'.map j ≫ mapOfToSequenceOfBlowups c j (le_of_lt hj) =
      mapOfToSequenceOfBlowups c (j + 1) hj ≫ s.transitionMap (le_of_lt $ c.blowupSequenceData_index_lt_index_succ j hj) :=
  c.blowupSequenceData_blowupMorphism_comp_map j hj

theorem blowupMorphism_comp_lowerMap_assoc (hj : j < s'.length)
    {W : Sch} (g : s.obj (c.idx j) ⟶ W) :
    s'.map j ≫ mapOfToSequenceOfBlowups c j (le_of_lt hj) ≫ g =
      mapOfToSequenceOfBlowups c (j + 1) hj ≫ s.transitionMap (le_of_lt $ c.blowupSequenceData_index_lt_index_succ j hj) ≫ g := by
  rw [← assoc, blowupMorphism_comp_lowerMap, assoc]
end

theorem lowerMap_congr {a b : ℕ} (hab : a = b)
    (ha : a ≤ s'.length) (hb : b ≤ s'.length)
    (E1 : s'.obj a = s'.obj b) (E2 : s.obj (c.idx b) = s.obj (c.idx a)) :
    mapOfToSequenceOfBlowups c a ha = eqToHom E1 ≫ mapOfToSequenceOfBlowups c b hb ≫ eqToHom E2 := by
  subst hab
  simp

theorem lastMap_eq_lowerMap
    (E : s.obj (c.idx s'.length) = s.obj s.length) :
    c.lastMap = mapOfToSequenceOfBlowups c s'.length le_rfl ≫ eqToHom E := rfl
end

section
variable {t' : BlowupSequenceData (s'.obj s'.length)} {t : BlowupSequenceData (s.obj s.length)} {c : SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s.toSequenceOfBlowups} (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
section
variable (i : ℕ)
def mapOverLastMap (hi : i ≤ t'.length) :
    t'.obj i ⟶ t.obj (e.idx i) := e.map i hi

theorem blowupMorphism_comp_upperMap (hi : i < t'.length) :
    t'.map i ≫ mapOverLastMap e i (le_of_lt hi) =
      mapOverLastMap e (i + 1) hi ≫ t.transitionMap (le_of_lt $ e.blowupSequenceData_index_lt_index_succ i hi) :=
  e.blowupSequenceData_blowupMorphism_comp_map i hi

theorem blowupMorphism_comp_upperMap_assoc (hi : i < t'.length)
    {W : Sch} (g : t.obj (e.idx i) ⟶ W) :
    t'.map i ≫ mapOverLastMap e i (le_of_lt hi) ≫ g =
      mapOverLastMap e (i + 1) hi ≫ t.transitionMap (le_of_lt $ e.blowupSequenceData_index_lt_index_succ i hi) ≫ g := by
  rw [← assoc, blowupMorphism_comp_upperMap, assoc]
end

theorem upperMap_zero_comp_isoObjZero_assoc {W : Sch}
    (g : s.obj s.length ⟶ W) :
    mapOverLastMap e 0 (zero_le _) ≫ t.transitionMap (zero_le $ e.idx 0) ≫ t.isoZero.hom ≫ g =
      t'.isoZero.hom ≫ c.lastMap ≫ g := by
  have h := by
    exact tr_ (congrArg (fun g => e.map 0 (zero_le _) ≫ g) $ (BlowupSequenceData.transitionMap_zero_comp_isoObjZero_hom t $ e.idx 0).trans (p36 t $ e.idx 0).symm) $ tr_ ((e.isPullback 0 $ zero_le _).w) $ congrArg (fun g => g ≫ c.lastMap) $ (p36 t' 0).trans $ p23 t'
  let _a0 := t.transitionMap (zero_le $ e.idx 0) ≫ bdIzH t
  calc mapOverLastMap e 0 (zero_le _) ≫ _a0 ≫ g
      = (mapOverLastMap e 0 (zero_le _) ≫ _a0) ≫ g := by
        simp [assoc]
    _ = (bdIzH t' ≫ c.lastMap) ≫ g := congrArg (fun m => m ≫ g) h
    _ = bdIzH t' ≫ c.lastMap ≫ g := assoc _ _ _
end
end

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (c : SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
section
variable (i) (hi : i ≤ t'.length)
def appendMapAdd :
    (append s' t').obj (s'.length + i) ⟶ (append s t).obj (s.length + e.idx i) :=
  hom (BlowupSequenceData.concatObjAddIso s' t' i) ≫ mapOverLastMap e i hi ≫
    inv (BlowupSequenceData.concatObjAddIso s t $ e.idx i)

theorem concatMapAddLength_comp_concatObjAddIso_hom :
    concatMapAddLength s t s' t' c e i hi ≫ hom (BlowupSequenceData.concatObjAddIso s t $ e.idx i) =
      hom (BlowupSequenceData.concatObjAddIso s' t' i) ≫ e.map i hi :=
  comp_comp_inv_comp_hom (BlowupSequenceData.concatObjAddIso s' t' i).hom (e.map i hi)
    (BlowupSequenceData.concatObjAddIso s t $ e.idx i)
end

theorem upperConcatMap_congr {j r q : ℕ} (hr : r = q)
    (hrle : r ≤ t'.length) (hq : q ≤ t'.length)
    (A : (append s' t').obj j = (append s' t').obj (s'.length + r))
    (B : (append s t).obj (s.length + e.idx r) = (append s t).obj (concatIndex s t s' t' c e j))
    (E1 : (append s' t').obj j = (append s' t').obj (s'.length + q))
    (E2 : (append s t).obj (s.length + e.idx q) =
      (append s t).obj (concatIndex s t s' t' c e j)) :
    eqToHom A ≫ appendMapAdd s t s' t' c e r hrle ≫ eqToHom B =
      eqToHom E1 ≫ appendMapAdd s t s' t' c e q hq ≫ eqToHom E2 := by
  subst hr
  rfl
end

section
variable (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (j : ℕ)
theorem append_schemeAt_eq_length_add_sub (h : s'.length ≤ j) :
    (append s' t').obj j = (append s' t').obj (s'.length + (j - s'.length)) :=by simp_all
theorem sub_length_le_of_le_length_add (hj : j ≤ s'.length + t'.length) : j - s'.length ≤ t'.length := by
  omega
end

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (c : SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
section
variable (j : ℕ)
section
variable (hj : j ≤ s'.length + t'.length)
def concatMap :
    (append s' t').obj j ⟶ (append s t).obj (concatIndex s t s' t' c e j) :=
  if h : j < s'.length then concatMapOfLtLength s t s' t' c e j h
  else
    eqToHom (append_schemeAt_eq_length_add_sub s' t' j $ not_lt.1 h) ≫
      concatMapAddLength s t s' t' c e (j - s'.length) (sub_length_le_of_le_length_add s' t' j hj) ≫
      eqToHom (append_schemeAt_concatIndex_of_le s t s' t' c e j $ not_lt.1 h)

theorem concatMap_eq_lowerMap_of_lt (h : j < s'.length)
    (A : (append s' t').obj j = s'.obj j)
    (B : s.obj (c.idx j) = (append s t).obj (concatIndex s t s' t' c e j)) :
    concatMap s t s' t' c e j hj = eqToHom A ≫ mapOfToSequenceOfBlowups c j (le_of_lt h) ≫ eqToHom B :=
  dif_pos h

theorem concatMap_eq_map_of_lt (h : j < s'.length) :
    concatMap s t s' t' c e j hj =
      eqToHom (BlowupSequenceData.append_schemeAt_of_le_length s' t' $ le_of_lt h) ≫ c.map j (le_of_lt h) ≫
        eqToHom (append_schemeAt_concatIndex_of_lt s t s' t' c e j h) := dif_pos h
end

theorem append_center_eq_comap_concatMap
    (hj : j < s'.length + t'.length) :
    (append s' t').toSequenceOfBlowups.center j =
      comap ((append s t).toSequenceOfBlowups.center $ concatIndex s t s' t' c e j)
        (concatMap s t s' t' c e j $ le_of_lt hj) := by
  show (append s' t').center j =
      comap ((append s t).center $ concatIndex s t s' t' c e j)
        (concatMap s t s' t' c e j $ le_of_lt hj)
  by_cases h : j < s'.length
  have hci := c.blowupSequenceData_index_lt_length j h
  let _a1 := c.map j $ le_of_lt h
  have hc : s'.center j = cmI (s.center $ c.idx j) _a1 :=
    c.center_comap j (by rw [p14]; exact h)
  let _a0 := eqToHom $ p40 s' t' $ le_of_lt h
  let _a2 := p40 s t $ le_of_lt hci
  have hmA : (_a0 ≫ _a1 ≫
        eqToHom _a2.symm) ≫
        eqToHom _a2 =
      _a0 ≫ _a1 :=
    comp_comp_eqToHom_comp_eqToHom _ _ _ _
  rw [concatMap_eq_map_of_lt s t s' t' c e j (le_of_lt hj) h,
    center_comap_comp_eqToHom_congr (append s t) (concatIndex_of_lt s t s' t' c e j h)
      _a0 _a1
      (append_schemeAt_concatIndex_of_lt s t s' t' c e j h)
      _a2.symm,
    BlowupSequenceData.append_center_of_lt_length s t hci, ← comap_comp, hmA,
    BlowupSequenceData.append_center_of_lt_length s' t' h, hc]
  exact sy_ $ comap_comp _ _ _
  have hge := not_lt.1 h
  obtain ⟨i, rfl⟩ : ∃ i, j = s'.length + i := ⟨j - s'.length, by omega⟩
  have hit : i < t'.length := by omega
  have hile := le_of_lt hit
  have hsub : s'.length + i - s'.length = i := by omega
  let _m0 := s'.length + i
  have hidx : concatIndex s t s' t' c e _m0 = s.length + e.idx i := by
    rw [concatIndex_of_ge s t s' t' c e _m0 hge, hsub]
  let _a3 := append_schemeAt_concatIndex_of_le s t s' t' c e _m0 hge
  let _a4 := sub_length_le_of_le_length_add s' t' _m0 $ le_of_lt hj
  let _a6 := append_schemeAt_eq_length_add_sub s' t' _m0 hge
  have hmapGe : concatMap s t s' t' c e _m0 (le_of_lt hj) =
      eqToHom _a6 ≫
        concatMapAddLength s t s' t' c e (s'.length + i - s'.length)
          _a4 ≫
        eqToHom _a3 :=
    dif_neg $ not_lt.2 hge
  let _a5 := congrArg (append s t).obj hidx.symm
  have hshift := concatMapAddLength_congr s t s' t' c e hsub
    _a4 hile
    _a6
    _a3
    _a5
  have hcen : t'.center i = cmI (t.center $ e.idx i) (e.map i hile) :=
    e.center_comap i (by rw [p14]; exact hit)
  rw [hmapGe, hshift,
    center_comap_comp_eqToHom (append s t) hidx.symm (concatMapAddLength s t s' t' c e i hile)
      _a5,
    append_center_length_add s t $ e.idx i, ← comap_comp, concatMapAddLength_comp_concatObjAddIso_hom s t s' t' c e i hile,
    append_center_length_add s' t' i, hcen]
  exact sy_ $ comap_comp _ _ _
end

theorem concatMap_eq_upperConcatMap_of_le (j q : ℕ)
    (hj : j ≤ s'.length + t'.length) (hge : s'.length ≤ j) (hjq : j - s'.length = q)
    (hq : q ≤ t'.length)
    (E1 : (append s' t').obj j = (append s' t').obj (s'.length + q))
    (E2 : (append s t).obj (s.length + e.idx q) =
      (append s t).obj (concatIndex s t s' t' c e j)) :
    concatMap s t s' t' c e j hj =
      eqToHom E1 ≫ appendMapAdd s t s' t' c e q hq ≫ eqToHom E2 := by
  exact tr_ (dif_neg $ not_lt.2 hge) $ upperConcatMap_congr s t s' t' c e hjq (sub_length_le_of_le_length_add s' t' j hj) hq
    (append_schemeAt_eq_length_add_sub s' t' j hge) (append_schemeAt_concatIndex_of_le s t s' t' c e j hge) E1 E2

section
variable (j) (hj : j < s'.length + t'.length)
theorem blowupMorphism_comp_concatMap
    (hd : concatIndex s t s' t' c e j ≤ concatIndex s t s' t' c e (j + 1)) :
    (append s' t').map j ≫ concatMap s t s' t' c e j (le_of_lt hj) =
      concatMap s t s' t' c e (j + 1) hj ≫ (append s t).transitionMap hd := by
  by_cases hlt : j < s'.length
  · by_cases h1 : j + 1 < s'.length
    · have hcj := c.blowupSequenceData_index_lt_length j hlt
      have hc1 := c.blowupSequenceData_index_lt_length (j + 1) h1
      have hmono := le_of_lt $ c.blowupSequenceData_index_lt_index_succ j hlt
      let _a1 := concatIndex_of_lt s t s' t' c e (j + 1) h1
      rw [BlowupSequenceData.append_blowupMorphism_of_lt_length s' t' hlt,
        concatMap_eq_lowerMap_of_lt s t s' t' c e j (le_of_lt hj) hlt
          (p40 s' t' (le_of_lt hlt))
          (append_schemeAt_concatIndex_of_lt s t s' t' c e j hlt),
        concatMap_eq_lowerMap_of_lt s t s' t' c e (j + 1) hj h1
          (p40 s' t' (le_of_lt h1))
          (append_schemeAt_concatIndex_of_lt s t s' t' c e (j + 1) h1),
        transitionMap_congr (append s t) (concatIndex_of_lt s t s' t' c e j hlt)
          _a1 hd hmono
          (congrArg (append s t).obj _a1)
          (congrArg (append s t).obj (concatIndex_of_lt s t s' t' c e j hlt)).symm,
        append_transitionMap_of_le_length s t hmono (le_of_lt hc1)]
      simp [blowupMorphism_comp_lowerMap_assoc c j hlt]
    · have hjn : j + 1 = s'.length := by omega
      have hcj := c.blowupSequenceData_index_lt_length j hlt
      have hidxlen' := c.index_length_eq_length
      have hidxlen : c.idx (j + 1) = s.length := by rw [hjn]
                                                    exact hidxlen'
      have hidx0 := concatIndex_of_lt s t s' t' c e j hlt
      have hidx1 : concatIndex s t s' t' c e (j + 1) = s.length + e.idx 0 := by
        rw [concatIndex_of_ge s t s' t' c e (j + 1) (le_of_eq hjn.symm),
          show j + 1 - s'.length = 0 by omega]
      have hdle : c.idx j ≤ s.length + e.idx 0 :=
        le_trans (le_of_lt hcj) (le_add_right _ _)
      rw [BlowupSequenceData.append_blowupMorphism_of_lt_length s' t' hlt,
        concatMap_eq_lowerMap_of_lt s t s' t' c e j (le_of_lt hj) hlt
          (p40 s' t' (le_of_lt hlt))
          (append_schemeAt_concatIndex_of_lt s t s' t' c e j hlt),
        concatMap_eq_upperConcatMap_of_le s t s' t' c e (j + 1) 0 hj (le_of_eq hjn.symm)
          (show j + 1 - s'.length = 0 by omega) (zero_le _)
          (congrArg (append s' t').obj (show j + 1 = s'.length + 0 by omega))
          (congrArg (append s t).obj hidx1.symm),
        transitionMap_congr (append s t) hidx0 hidx1 hd hdle
          (congrArg (append s t).obj hidx1)
          (congrArg (append s t).obj hidx0).symm]
      simp [appendMapAdd, concatObjAddIso_zero_hom, assoc, eqToHom_trans_assoc,
        eqToHom_refl, id_comp]
      rw [concatObjAddIso_inv_comp_transitionMap_of_le_length_assoc s t (le_of_lt hcj) hdle, upperMap_zero_comp_isoObjZero_assoc e,
        blowupMorphism_comp_lowerMap_assoc c j hlt,
        lowerMap_congr c hjn hlt le_rfl (congrArg s'.obj hjn)
          (congrArg (fun n => s.obj $ c.idx n) hjn.symm),
        transitionMap_congr s rfl hidxlen
          (le_of_lt (c.blowupSequenceData_index_lt_index_succ j hlt)) (le_of_lt hcj)
          (congrArg s.obj hidxlen) rfl,
        lastMap_eq_lowerMap c (congrArg s.obj hidxlen')]
      simp
      all_goals exact comp_assoc_inner_pair _ _ _ _ _
  · have hge := not_lt.1 hlt
    obtain ⟨q, rfl⟩ : ∃ q, j = s'.length + q := ⟨j - s'.length, by omega⟩
    have hq1 : q < t'.length := by omega
    have hmono := e.blowupSequenceData_index_lt_index_succ q hq1
    have hidxj : concatIndex s t s' t' c e (s'.length + q) = s.length + e.idx q := by
      rw [concatIndex_of_ge s t s' t' c e (s'.length + q) (le_add_right _ _),
        show s'.length + q - s'.length = q by omega]
    have hidxj1 : concatIndex s t s' t' c e (s'.length + q + 1) = s.length + e.idx (q + 1) := by
      rw [concatIndex_of_ge s t s' t' c e (s'.length + q + 1) (by omega),
        show s'.length + q + 1 - s'.length = q + 1 by omega]
    rw [concatMap_eq_upperConcatMap_of_le s t s' t' c e (s'.length + q) q (le_of_lt hj)
        (le_add_right _ _)
        (show s'.length + q - s'.length = q by omega) (le_of_lt hq1) rfl
        (congrArg (append s t).obj hidxj.symm),
      concatMap_eq_upperConcatMap_of_le s t s' t' c e (s'.length + q + 1) (q + 1) hj (by omega)
        (show s'.length + q + 1 - s'.length = q + 1 by omega) hq1 rfl
        (congrArg (append s t).obj hidxj1.symm),
      transitionMap_congr (append s t) hidxj hidxj1 hd
        (show s.length + e.idx q ≤ s.length + e.idx (q + 1) by omega)
        (congrArg (append s t).obj hidxj1) (congrArg (append s t).obj hidxj).symm]
    simp [appendMapAdd, assoc, eqToHom_trans_assoc, eqToHom_refl,
      id_comp]
    rw [BlowupSequenceData.append_blowupMorphism_comp_concatObjAddIso_assoc, blowupMorphism_comp_upperMap_assoc e q hq1,
      concatObjAddIso_inv_comp_transitionMap_assoc s t (le_of_lt hmono)]

theorem toSequenceOfBlowups_blowupMorphism_comp_concatMap :
    (append s' t').toSequenceOfBlowups.transitionMapSucc j ≫ concatMap s t s' t' c e j (le_of_lt hj) =
      concatMap s t s' t' c e (j + 1) hj ≫
        (append s t).toSequenceOfBlowups.transitionMap (le_of_lt $ concatIndex_lt_concatIndex_succ s t s' t' c e j hj) := by
  rw [p50]
  exact blowupMorphism_comp_concatMap s t s' t' c e j hj _
end
end

private theorem comap_iso_hom_ne_top {Y Z : Sch} (g : Y ≅ Z) (J : ISD Z)
    (hJ : J ≠ ⊤) : comap J g.hom ≠ ⊤ := by
  obtain ⟨x, hx⟩ := exists_mem_support_of_ne_top J hJ
  have h1 : bsM (isoI g ≫ isoH g) x ∈ spI J := by simp_all
  refine ne_top_of_mem_support (cmI J g.hom)
    (ibM g x) $ mpr_ mem_support_comap ?_
  simpa using h1

private theorem comap_eqToHom_ne_top {Y Z : Sch} (h : Y = Z) (J : ISD Z)
    (hJ : J ≠ ⊤) : comap J (eqToHom h) ≠ ⊤ :=
  comap_iso_hom_ne_top (eqToIso h) J hJ

theorem append_center_ne_top (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData $ s'.obj s'.length)
    (c : SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) j
    (hj : j < s'.length + t'.length) : (append s' t').toSequenceOfBlowups.center j ≠ ⊤ := by
  show (append s' t').center j ≠ ⊤
  rcases lt_trichotomy j s'.length with h | h | h
  have hne :=
    c.center_ne_top j (by rw [p14]; exact h)
  rw [BlowupSequenceData.append_center_of_lt_length s' t' h]
  exact comap_eqToHom_ne_top _ _ hne
  subst h
  have ht : 0 < t'.length := by omega
  have h0 :=
    e.center_ne_top 0 (by rw [p14]; exact ht)
  rw [BlowupSequenceData.append_center_length s' t']
  exact comap_eqToHom_ne_top _ _ $ comap_iso_hom_ne_top t'.isoZero.symm (t'.center 0) h0
  have hsub : j - s'.length < t'.length := by omega
  have hne :=
    e.center_ne_top (j - s'.length) (by rw [p14]; exact hsub)
  rw [BlowupSequenceData.append_center_of_length_lt s' t' h]
  exact comap_eqToHom_ne_top _ _ hne

theorem isPullback_iso_hom_comp__b11 {A A' B Y Z : Sch} (u : A' ≅ A)
    {f : A ⟶ B} {g : A ⟶ Y} {k : B ⟶ Z} {ps_ : Y ⟶ Z} (h : IsPullback f g k ps_) :
    IsPullback (hom u ≫ f) (hom u ≫ g) k ps_ := by
  have h1 : IsPullback u.hom (isoH u ≫ g) g $ 𝟙 Y := of_horiz_isIso ⟨by simp⟩
  simpa using (h1.paste_horiz h)

theorem isPullback_of_iso {A A' B B' Y Z : Sch} (u : A' ≅ A) (v : B ≅ B')
    {f : A ⟶ B} {g : A ⟶ Y} {k : B ⟶ Z} {ps_ : Y ⟶ Z}
    {F : A' ⟶ B'} {G : A' ⟶ Y} {K : B' ⟶ Z} (h : IsPullback f g k ps_)
    (hF : F = hom u ≫ f ≫ hom v) (hG : G = hom u ≫ g) (hK : K = inv v ≫ k) :
    IsPullback F G K ps_ := by
  subst hF
  subst hG
  subst hK
  refine isPullback_iso_hom_comp__b11 u ?_
  have h1 : IsPullback v.hom k (isoI v ≫ k) $ 𝟙 Z := of_horiz_isIso ⟨by simp⟩
  simpa using (h.paste_horiz h1)

theorem isPullback_concatMap (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (s' : BlowupSequenceData X') (t' : BlowupSequenceData $ s'.obj s'.length)
    (c : SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) (j : ℕ)
    (hj : j ≤ s'.length + t'.length) :
    IsPullback (concatMap s t s' t' c e j hj) ((append s' t').toSequenceOfBlowups.projectionToBase j)
      ((append s t).toSequenceOfBlowups.projectionToBase $ concatIndex s t s' t' c e j) ph_ := by
  by_cases h : j < s'.length
  have hmap : concatMap s t s' t' c e j hj = concatMapOfLtLength s t s' t' c e j h := dif_pos h
  have hidx := concatIndex_of_lt s t s' t' c e j h
  have hobj :=
    append_schemeAt_concatIndex_of_lt s t s' t' c e j h
  exact isPullback_of_iso (eqToIso $ p40 s' t' $ le_of_lt h)
    (eqToIso hobj) (c.isPullback j $ le_of_lt h) hmap (append_projectionToBase_eq_of_le_length s' t' (rfl) (le_of_lt h) (p40 s' t' $ le_of_lt h).symm) $ append_projectionToBase_eq_of_le_length s t hidx (le_of_lt $ c.blowupSequenceData_index_lt_length j h) hobj
  have hge := not_lt.1 h
  have hji : j = s'.length + (j - s'.length) := by omega
  let _a4 := sub_length_le_of_le_length_add s' t' j hj
  have hmap : concatMap s t s' t' c e j hj =
      eqToHom (append_schemeAt_eq_length_add_sub s' t' j hge) ≫
        concatMapAddLength s t s' t' c e (j - s'.length) _a4 ≫
        eqToHom (append_schemeAt_concatIndex_of_le s t s' t' c e j hge) := dif_neg h
  refine isPullback_of_iso
    (eqToIso (append_schemeAt_eq_length_add_sub s' t' j hge) ≪≫
      BlowupSequenceData.concatObjAddIso s' t' (j - s'.length))
    ((BlowupSequenceData.concatObjAddIso s t $ e.idx $ j - s'.length).symm ≪≫
      eqToIso (append_schemeAt_concatIndex_of_le s t s' t' c e j hge))
    ((e.isPullback (j - s'.length) _a4).paste_vert
      c.isPullback_lastMap) ?_ (append_projectionToBase_eq_of_eq_length_add s' t' hji $ append_schemeAt_eq_length_add_sub s' t' j hge) $ append_projectionToBase_eq_of_eq_length_add s t (concatIndex_of_ge s t s' t' c e j hge) (append_schemeAt_concatIndex_of_le s t s' t' c e j hge).symm
  rw [hmap]
  simp [trans_hom, symm_hom, eqToIso.hom]
  exact comp_assoc_outer _ _ _ _ _

private theorem exists_preimage_of_isPullback {A A' Z Z' : Sch} {p : A' ⟶ A} {q : A' ⟶ Z'}
    {f : A ⟶ Z} {g : Z' ⟶ Z} (h : IsPullback p q f g) (a : ↥A) (b : ↥Z')
    (hab : f.base a = g.base b) : ∃ a' : ↥A', p.base a' = a := by
  obtain ⟨w, hw1, _hw2⟩ := exists_preimage_pullback a b hab
  refine ⟨h.isoPullback.inv.base w, ?_⟩
  have key : h.isoPullback.inv ≫ p = pullback.fst f g := by simp_all
  calc p.base (h.isoPullback.inv.base w)
      = bsM (h.isoPullback.inv ≫ p) w := rfl
    _ = bsM (pullback.fst f g) w := by rw [key]
    _ = a := hw1

section
variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X') (t' : BlowupSequenceData (s'.obj s'.length)) (c : SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (e : SequenceOfBlowupsPullback c.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
theorem append_projectionToBase_ne_of_forall_concatIndex_ne (i : ℕ)
    (hi : i < s.length + t.length)
    (hmiss : ∀ j : ℕ, j < s'.length + t'.length → concatIndex s t s' t' c e j ≠ i)
    (z : ↥((append s t).toSequenceOfBlowups.schemeAt i)) (hz : z ∈ ((append s t).toSequenceOfBlowups.center i).support)
    (x' : ↥X') :
    ph_.base x' ≠ ((append s t).toSequenceOfBlowups.projectionToBase i).base z := by
  intro heq
  have hzc : z ∈ spI ((append s t).center i) := by
    rwa [p24] at hz
  have heqp :=
    heq.trans $ congrArg (fun m : (append s t).toSequenceOfBlowups.schemeAt i ⟶ X => bsM m z)
      (p36 (append s t) i)
  by_cases hlt : i < s.length
  have hobj := p40 s t $ le_of_lt hlt
  rw [BlowupSequenceData.append_center_of_lt_length s t hlt] at hzc
  have hzs :=
    mem_support_comap.mp hzc
  have heq2 :=
    (tr_ heqp $ congrArg (fun m : (append s t).obj i ⟶ X => bsM m z)
        (BlowupSequenceData.projectionToBase_append_of_le_length s t $ le_of_lt hlt)).trans rfl
  refine c.omitted i ?_ ?_ (bsM (eqToHom hobj) z) ?_ x' $ tr_ heq2 (congrArg (fun m : s.obj i ⟶ X => bsM m $ bsM (eqToHom hobj) z) $ p36 s i).symm
  rwa [p14]
  intro j hj hji
  rw [p14] at hj
  exact hmiss j (by omega) $ tr_ (concatIndex_of_lt s t s' t' c e j hj) hji
  rwa [p24]
  have hge := not_lt.1 hlt
  obtain ⟨n, rfl⟩ : ∃ n, i = s.length + n := ⟨i - s.length, by omega⟩
  have hn : n < t.length := by omega
  rw [append_center_length_add s t n] at hzc
  have hzt :=
    mem_support_comap.mp hzc
  have heq2 :=
    (tr_ heqp $ congrArg (fun m : (append s t).obj (s.length + n) ⟶ X => bsM m z)
        (projectionToBase_append_length_add s t n)).trans rfl
  let _a0 := bsM (t.projectionToBase n) $ bsM (isoH $ BlowupSequenceData.concatObjAddIso s t n) z
  have hsm :=
    (congrArg (fun m : s.obj s.length ⟶ X =>
        m.base _a0)
      (p36 s s.toSequenceOfBlowups.length)).trans heq2.symm
  obtain ⟨a', ha'⟩ := exists_preimage_of_isPullback c.isPullback_lastMap
    _a0 x' hsm
  refine e.omitted n ?_ ?_ (bsM (isoH $ BlowupSequenceData.concatObjAddIso s t n) z) ?_ a' ?_
  rwa [p14]
  intro m hm hmn
  rw [p14] at hm
  refine hmiss (s'.length + m) (by omega) ?_
  rw [concatIndex_of_ge s t s' t' c e (s'.length + m) $ le_add_right _ _,
    show s'.length + m - s'.length = m by omega, hmn]
  rwa [p24]
  exact tr_ ha' (congrArg (fun m : t.obj n ⟶ s.obj s.length =>
    m.base $ bsM (isoH $ BlowupSequenceData.concatObjAddIso s t n) z)
    (p36 t n)).symm

def concat :
    SequenceOfBlowupsPullback ph_ (append s' t').toSequenceOfBlowups (append s t).toSequenceOfBlowups where
  idx := concatIndex s t s' t' c e
  map := concatMap s t s' t' c e
  idx_length := concatIndex_length_add_length s t s' t' c e
  idx_lt := concatIndex_lt_length_add_length s t s' t' c e
  idx_strictMono := concatIndex_lt_concatIndex_succ s t s' t' c e
  isPullback := isPullback_concatMap s t s' t' c e
  step := toSequenceOfBlowups_blowupMorphism_comp_concatMap s t s' t' c e
  center_comap := append_center_eq_comap_concatMap s t s' t' c e
  center_ne_top := append_center_ne_top s t s' t' c e
  omitted := append_projectionToBase_ne_of_forall_concatIndex_ne s t s' t' c e
end

end

end SequenceOfBlowupsPullback

theorem IsPullbackBlowupSequence.nonempty_sequenceOfBlowupsPullback {X X' : Sch} {ph_ : X' ⟶ X}
    {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (h : IsPullbackBlowupSequence ph_ s' s) :
    Nonempty $ SequenceOfBlowupsPullback ph_ s' s := by
  obtain ⟨idx, e, hlt, hmono, hlen, hsup, hfst, hstep, hcen⟩ := h
  refine ⟨{
    idx := idx
    map := fun j hj => isoH (e j hj) ≫ pullback.snd ph_ (sbPrj s $ idx j)
    idx_length := hlen
    idx_lt := hlt
    idx_strictMono := fun j hj => hmono j (j + 1) hj $ lt_succ_self j
    isPullback := ?_
    step := ?_
    center_comap := hcen
    center_ne_top := ?_
    omitted := ?_ }⟩
  intro j hj
  have hp :=
    SequenceOfBlowupsPullback.isPullback_iso_hom_comp__b11 (e j hj)
      (of_hasPullback ph_ $ sbPrj s $ idx j).flip
  rwa [hfst j hj] at hp
  intro j hj
  have hr := le_of_lt $ hmono j (j + 1) hj $ lt_succ_self j
  let _a0 := isoH $ e (j + 1) hj
  let _a1 := pullback.snd ph_ $ sbPrj s $ idx $ j + 1
  calc s'.transitionMapSucc j ≫ (isoH (e j $ le_of_lt hj) ≫ pullback.snd ph_ (sbPrj s $ idx j))
      = (sbTrS s' j ≫ isoH (e j $ le_of_lt hj)) ≫
          pullback.snd ph_ (sbPrj s $ idx j) := sy_ $ assoc _ _ _
    _ = (_a0 ≫ s.pullbackTransitionMap ph_ hr) ≫
          pullback.snd ph_ (sbPrj s $ idx j) := congrArg (fun m => m ≫ pullback.snd ph_ (sbPrj s $ idx j)) $ hstep j hj hr
    _ = _a0 ≫
          (s.pullbackTransitionMap ph_ hr ≫ pullback.snd ph_ (sbPrj s $ idx j)) := assoc _ _ _
    _ = _a0 ≫
          (_a1 ≫ s.transitionMap hr) := by
            rw [SequenceOfBlowups.pullbackTransitionMap_comp_snd]
    _ = (_a0 ≫ _a1) ≫
          s.transitionMap hr := sy_ $ assoc _ _ _
  intro j hj htop
  obtain ⟨x, hx⟩ := mpr_ (hsup (idx j) $ hlt j hj) ⟨j, hj, rfl⟩
  refine ne_top_of_mem_support _ x hx ?_
  have h2 : (comap (center s $ idx j)
        (isoH (e j $ le_of_lt hj) ≫ pullback.snd ph_ (sbPrj s $ idx j))).comap
        (e j $ le_of_lt hj).inv =
      comap (⊤ : ISD $ s'.schemeAt j) (e j $ le_of_lt hj).inv := by
    rw [(hcen j hj).symm.trans htop]
  rw [← comap_comp, m213,
    comap_top] at h2
  exact h2
  intro i hi hmiss z hz x' heq
  obtain ⟨w, _, hw2⟩ :=
    exists_preimage_pullback x' z heq
  have hmem : w ∈ support (cmI (center s i) $ pullback.snd ph_ $ sbPrj s i) := by
    refine mpr_ mem_support_comap ?_
    rwa [hw2]
  obtain ⟨j, hj, hji⟩ := mp_ (hsup i hi) ⟨w, hmem⟩
  exact hmiss j hj hji

theorem isPullbackBlowupSequence_append_same_field {k : Type} [Field k] {X X' : Sch} (ph_ : X' ⟶ X)
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
    {E : Bdy X}
    {p' : X' ⟶ Sp k} {I' : ISD X'} {m' : ℕ}
    {E' : Bdy X'}
    (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (S' : MarkedBlowupSequenceData p' I' m' E')
    (T' : MarkedBlowupSequenceData (S'.proj S'.toBlowupSequenceData.length ≫ p') (S'.ideal S'.toBlowupSequenceData.length)
      m' $ S'.boundary S'.toBlowupSequenceData.length)
    (hinv : ComapIsoInvariance)
    (c : SequenceOfBlowupsPullback ph_ S'.toBlowupSequenceData.toSequenceOfBlowups S.toBlowupSequenceData.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap T'.toBlowupSequenceData.toSequenceOfBlowups T.toBlowupSequenceData.toSequenceOfBlowups) :
    IsPullbackBlowupSequence ph_ (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  rw [toMarkedSequence_toSequenceOfBlowups $ S.append T hinv, toMarkedSequence_toSequenceOfBlowups $ S'.append T' hinv]
  exact (SequenceOfBlowupsPullback.concat S.toBlowupSequenceData T.toBlowupSequenceData S'.toBlowupSequenceData T'.toBlowupSequenceData c e).isPullbackSequenceOfBlowups

theorem isPullbackBlowupSequence_append_of_two_fields {k k' : Type} [Field k] [Field k']
    {X X' : Sch} (ph_ : X' ⟶ X)
    {p : X ⟶ Sp k} {I : ISD X} {m : ℕ}
    {E : Bdy X}
    {p' : X' ⟶ Sp k'} {I' : ISD X'} {m' : ℕ}
    {E' : Bdy X'}
    (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (S' : MarkedBlowupSequenceData p' I' m' E')
    (T' : MarkedBlowupSequenceData (S'.proj S'.toBlowupSequenceData.length ≫ p') (S'.ideal S'.toBlowupSequenceData.length)
      m' $ S'.boundary S'.toBlowupSequenceData.length)
    (hinv : ComapIsoInvariance)
    (c : SequenceOfBlowupsPullback ph_ S'.toBlowupSequenceData.toSequenceOfBlowups S.toBlowupSequenceData.toSequenceOfBlowups)
    (e : SequenceOfBlowupsPullback c.lastMap T'.toBlowupSequenceData.toSequenceOfBlowups T.toBlowupSequenceData.toSequenceOfBlowups) :
    IsPullbackBlowupSequence ph_ (S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  rw [toMarkedSequence_toSequenceOfBlowups $ S.append T hinv, toMarkedSequence_toSequenceOfBlowups $ S'.append T' hinv]
  exact (SequenceOfBlowupsPullback.concat S.toBlowupSequenceData T.toBlowupSequenceData S'.toBlowupSequenceData T'.toBlowupSequenceData c e).isPullbackSequenceOfBlowups





namespace SequenceOfBlowupsPullback

private theorem base_comp_apply {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A) :
    (f ≫ g).base x = g.base (f.base x) := by
  simp

theorem eqToHom_base_trans {A B C : Sch} (h : A = B) (h' : B = C)
    (x : ↥A) : (eqToHom h').base ((eqToHom h).base x) = (eqToHom $ h.trans h').base x := by
  subst h
  subst h'
  simp

theorem eqToHom_base_self {A : Sch} (h : A = A) (x : ↥A) :
    (eqToHom h).base x = x := by
  simp

theorem inv_base_hom_base {A B : Sch} (e : A ≅ B) (x : ↥A) :
    e.inv.base (e.hom.base x) = x := by
  simp

section
variable {X} (d : BlowupSequenceData X) {a b} (hab : a = b) (h : d.obj a = d.obj b) (z : ↥(d.obj a))
include hab
theorem eqToHom_base_mem_support_center
    (hz : z ∈ support (d.center a)) : (eqToHom h).base z ∈ support (d.center b) := by
  subst hab
  simpa using hz

theorem projectionToBase_base_eqToHom_base :
    (d.projectionToBase b).base ((eqToHom h).base z) = (d.projectionToBase a).base z := by
  subst hab
  simp
end

section

section
variable {X Y : Sch}
section
variable (t : BlowupSequenceData X) (t' : BlowupSequenceData Y) (ht : t.length = 1) (ht' : t'.length = 1)
include ht ht'
theorem length_eq_of_length_eq_one : t'.toSequenceOfBlowups.length = t.toSequenceOfBlowups.length :=by simp_all
end

end

def mapOfLengthEqOne {X Y : Sch} (g : Y ⟶ X) (t : BlowupSequenceData X) (t' : BlowupSequenceData Y)
    (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1) :
    (j : ℕ) → j ≤ t'.toSequenceOfBlowups.length → (t'.toSequenceOfBlowups.schemeAt j ⟶ t.toSequenceOfBlowups.schemeAt j)
  | 0, _ =>
      eqToHom (t'.toSequenceOfBlowups_schemeAt 0) ≫ (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫
        eqToHom (t.toSequenceOfBlowups_schemeAt 0).symm
  | 1, _ => eqToHom (t'.toSequenceOfBlowups_schemeAt 1) ≫ q ≫ eqToHom (t.toSequenceOfBlowups_schemeAt 1).symm
  | (_ + 2), h => absurd h (by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']; omega)

section
variable {X Y} (g : Y ⟶ X) (t : BlowupSequenceData X) (t' : BlowupSequenceData Y)
def ofLengthOne
    (ht : t.length = 1) (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1)
    (hq : IsPullback q (t'.map 0) (t.map 0) $ t'.isoZero.hom ≫ g ≫ t.isoZero.inv)
    (hcen : t'.center 0 = comap (t.center 0) (t'.isoZero.hom ≫ g ≫ t.isoZero.inv))
    (hne : t'.center 0 ≠ ⊤) :
    SequenceOfBlowupsPullback g t'.toSequenceOfBlowups t.toSequenceOfBlowups where
  idx := fun j => j
  map := mapOfLengthEqOne g t t' ht' q
  idx_length := length_eq_of_length_eq_one t t' ht ht'
  idx_lt := by
    intro j hj
    rwa [length_eq_of_length_eq_one t t' ht ht'] at hj
  idx_strictMono := fun j _ => lt_succ_self j
  isPullback := by
    let _ht := ht
    have hlen : t'.toSequenceOfBlowups.length = 1 := by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']
    have hzero : IsPullback (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) t'.isoZero.hom
        t.isoZero.hom g := by
      have hsq : CommSq t'.isoZero.hom (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) g t.isoZero.hom := by
        constructor
        simp
      exact (of_horiz_isIso hsq).flip
    have hs0' : t'.toSequenceOfBlowups.projectionToBase 0 = t'.isoZero.hom := by
      rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, projectionToBase_zero]
    have hs0 : t.toSequenceOfBlowups.projectionToBase 0 = t.isoZero.hom := by
      rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, projectionToBase_zero]
    have hs1' : t'.toSequenceOfBlowups.projectionToBase 1 = t'.map 0 ≫ t'.isoZero.hom := by
      rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase]
      show t'.projectionToBase (0 + 1) = t'.map 0 ≫ t'.isoZero.hom
      rw [projectionToBase_succ, projectionToBase_zero]
    have hs1 : t.toSequenceOfBlowups.projectionToBase 1 = t.map 0 ≫ t.isoZero.hom := by
      rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase]
      show t.projectionToBase (0 + 1) = t.map 0 ≫ t.isoZero.hom
      rw [projectionToBase_succ, projectionToBase_zero]
    intro j hj
    have hj1 : j = 0 ∨ j = 1 := by omega
    rcases hj1 with rfl | rfl
    · have hmap : mapOfLengthEqOne g t t' ht' q 0 hj = t'.isoZero.hom ≫ g ≫ t.isoZero.inv :=
        (id_comp $ (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫
            eqToHom (t.toSequenceOfBlowups_schemeAt 0).symm).trans
          (comp_id $ t'.isoZero.hom ≫ g ≫ t.isoZero.inv)
      rw [hmap, hs0, hs0']
      exact hzero
    · have hmap : mapOfLengthEqOne g t t' ht' q 1 hj = q :=
        (id_comp $ q ≫ eqToHom (t.toSequenceOfBlowups_schemeAt 1).symm).trans $ comp_id q
      rw [hmap, hs1, hs1']
      exact hq.paste_vert hzero
  step := by
    let _ht := ht
    intro j hj
    have hlen := t'.toSequenceOfBlowups_length
    have hj0 : j = 0 := by omega
    subst hj0
    have h1 := t'.toSequenceOfBlowups_blowupMorphism 0
    have h2 :=
      (t.toSequenceOfBlowups.blowupMorphism_eq_transitionMap 0).symm.trans $ t.toSequenceOfBlowups_blowupMorphism 0
    rw [h1, h2]
    show t'.map 0 ≫ (𝟙 (t'.obj 0) ≫ (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫ 𝟙 (t.obj 0)) =
      (𝟙 (t'.obj 1) ≫ q ≫ 𝟙 (t.obj 1)) ≫ t.map 0
    simp only [id_comp, comp_id]
    exact hq.w.symm
  center_comap := by
    let _ht := ht
    have hlen : t'.toSequenceOfBlowups.length = 1 := by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    let _a0 := t'.isoZero.hom ≫ g ≫ t.isoZero.inv
    have hmap : mapOfLengthEqOne g t t' ht' q 0 (le_of_lt hj) =
        _a0 :=
      (id_comp $ _a0 ≫
          eqToHom (t.toSequenceOfBlowups_schemeAt 0).symm).trans
        (comp_id _a0)
    rw [hmap, toSequenceOfBlowups_center, toSequenceOfBlowups_center]
    exact hcen
  center_ne_top := by
    have hlen : t'.toSequenceOfBlowups.length = 1 := by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']
    intro j hj
    rw [hlen] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    rw [toSequenceOfBlowups_center]
    exact hne
  omitted := by
    have hlen := t.toSequenceOfBlowups_length.trans ht
    have hlen' := t'.toSequenceOfBlowups_length.trans ht'
    intro i hi hmiss
    have hi0 : i = 0 := by omega
    have h0 : (0 : ℕ) < t'.toSequenceOfBlowups.length := by omega
    exact absurd hi0.symm $ hmiss 0 h0
end

end

theorem comap_eq_top_of_forall_support_not_mem_range {X Y T : Sch} (g : Y ⟶ X) (pi_ : T ⟶ X)
    (I : ISD T)
    (hmiss : ∀ z : ↥T, z ∈ support I → ∀ y : ↥Y, g.base y ≠ pi_.base z)
    (u : Y ⟶ T) (hu : IsPullback u (𝟙 Y) pi_ g) : comap I u = ⊤ := by
  have hcomm : u ≫ pi_ = g := by
    have h := hu.w
    rwa [id_comp] at h
  have hb : ∀ y, bsM pi_ (bsM u y) = bsM g y := by
    intro y
    have h1 : bsM (u ≫ pi_) y = bsM g y := by rw [hcomm]
    simpa using h1
  refine mp_ (Scheme.IdealSheafData.support_eq_bot_iff _) ?_
  rw [m19]
  refine le_antisymm ?_ bot_le
  intro y hy
  exact absurd (hb y).symm $ hmiss (bsM u y) hy y

section

section
variable {X Y : Sch}
section
variable (g : Y ⟶ X)
section
variable (t : BlowupSequenceData X)
def IsDisjointFromCenters : Prop :=
  ∀ i : ℕ, i < t.length → ∀ z : ↥(t.obj i), z ∈ support (t.center i) →
    ∀ y : ↥Y, g.base y ≠ (t.projectionToBase i).base z

theorem disjoint_omitted_centers_of_disjoint_centers
    (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (_he : e.length = 0) :
    ∀ i, i < t.toSequenceOfBlowups.length → (∀ j, j < e.toSequenceOfBlowups.length → t.length ≠ i) →
      ∀ z : ↥(t.toSequenceOfBlowups.schemeAt i), z ∈ support (t.toSequenceOfBlowups.center i) →
        ∀ x', g.base x' ≠ (t.toSequenceOfBlowups.projectionToBase i).base z := by
  intro i hi _hmiss z hz x'
  have hi' : i < t.length := by
    rwa [p14] at hi
  have hz' : z ∈ spI (t.center i) := by
    rwa [p24] at hz
  have hne := hmiss i hi' z hz' x'
  rwa [p36]

theorem isPullback_comp_isoObjZero_inv :
    IsPullback (g ≫ t.isoZero.inv) (𝟙 Y) (t.projectionToBase 0) g := by
  have hiso : IsIso $ t.projectionToBase 0 := by
    rw [t.projectionToBase_zero]
    infer_instance
  have hsq : CommSq (𝟙 Y) (g ≫ t.isoZero.inv) g $ t.projectionToBase 0 := by
    constructor
    simp [t.projectionToBase_zero]
  exact (of_horiz_isIso hsq).flip
end

section
variable [hv2_0 : Flat g] (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) (i) (hi : i < t.length) (u) (hu : IsPullback u (𝟙 Y) (t.projectionToBase i) g)
include hv2_0 hmiss hi hu
theorem isIso_pullbackSnd_of_flat_of_disjoint : IsIso $ pullback.snd (t.map i) u := by
  have hB := t.isBlowup i hi
  have htop :=
    comap_eq_top_of_forall_support_not_mem_range g (t.projectionToBase i) (t.center i) (hmiss i hi) u hu
  have hEC : p17 $ comap (t.center i) u := by
    rw [htop]
    exact isLocallyGeneratedByNonZeroDivisor_top Y
  obtain ⟨k, hk, -⟩ := hB.existsUnique_lift Y u hEC
  have hw : k ≫ t.map i = 𝟙 Y ≫ u := by rw [hk, id_comp]
  have hEC2 : p17 $ cmI (t.center i) $ pullback.snd (t.map i) u ≫ u := by
    have hc : cmI (t.center i) (pullback.snd (t.map i) u ≫ u) =
        comap (comap (t.center i) u) (pullback.snd (t.map i) u) := by
      simp
    rw [hc, htop]
    exact isLocallyGeneratedByNonZeroDivisor_comap_top _
  refine ⟨⟨pullback.lift k (𝟙 Y) hw, ?_, ?_⟩⟩
  apply pullback.hom_ext
  rw [assoc, pullback.lift_fst, id_comp]
  refine hB.hom_ext_of_comp_eq hEC2 ?_ pullback.condition
  rw [assoc, hk]
  rw [assoc, pullback.lift_snd, comp_id, id_comp]
  rw [pullback.lift_snd]

noncomputable def liftSuccOfIsDisjointFromCenters : Y ⟶ t.obj (i + 1) :=
  letI := isIso_pullbackSnd_of_flat_of_disjoint g t hmiss i hi u hu
  inv (pullback.snd (t.map i) u) ≫ pullback.fst (t.map i) u

theorem isPullback_liftSuccOfIsDisjointFromCenters :
    IsPullback (liftSuccOfIsDisjointFromCenters g t hmiss i hi u hu) (𝟙 Y) (t.projectionToBase $ i + 1) g := by
  have hiso := isIso_pullbackSnd_of_flat_of_disjoint g t hmiss i hi u hu
  let _a0 := pullback.snd (t.map i) u
  have hsq : IsPullback (inv _a0 ≫ pullback.fst (t.map i) u) (𝟙 Y)
      (t.map i) u := by
    refine of_iso_pullback ⟨?_⟩ (asIso _a0).symm ?_ ?_
    rw [assoc, pullback.condition, IsIso.inv_hom_id_assoc, id_comp]
    simp
    simp
  have hpaste := hsq.paste_vert hu
  simp [comp_id] at hpaste
  rwa [p43]
end
end

section
variable (t : BlowupSequenceData X) (e : BlowupSequenceData Y) (he : e.length = 0)
include he
theorem length_lt_toSequenceOfBlowups_length_of_lt : ∀ j, j < e.toSequenceOfBlowups.length → t.length < t.toSequenceOfBlowups.length :=by simp_all
theorem length_lt_length_of_lt_length_of_eq_zero : ∀ j, j < e.toSequenceOfBlowups.length → t.length < t.length :=by simp_all
end
end

section
variable {Y} (e : BlowupSequenceData Y) (he : e.length = 0)
include he
theorem schemeAt_eq_schemeAt_zero_of_length_eq_zero j
    (hj : j ≤ e.toSequenceOfBlowups.length) : e.toSequenceOfBlowups.schemeAt j = e.obj 0 := by
  have hlen := e.toSequenceOfBlowups_length.trans he
  have hj0 : j = 0 := by omega
  subst hj0
  exact e.toSequenceOfBlowups_schemeAt 0

theorem center_ne_top_of_length_eq_zero :
    ∀ j, j < e.toSequenceOfBlowups.length → e.toSequenceOfBlowups.center j ≠ ⊤ :=by simp_all
end

noncomputable def liftOfIsDisjointFromCenters {X Y : Sch} (g : Y ⟶ X) [Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) :
    (i : ℕ) → i ≤ t.length → {u : Y ⟶ t.obj i // IsPullback u (𝟙 Y) (t.projectionToBase i) g}
  | 0, _ => ⟨g ≫ t.isoZero.inv, isPullback_comp_isoObjZero_inv g t⟩
  | (i + 1), h =>
      let hi : i < t.length := by omega
      let prev := liftOfIsDisjointFromCenters g t hmiss i hi.le
      ⟨liftSuccOfIsDisjointFromCenters g t hmiss i hi prev.1 prev.2, isPullback_liftSuccOfIsDisjointFromCenters g t hmiss i hi prev.1 prev.2⟩

section
variable {X Y} (g : Y ⟶ X) [Flat g] (t : BlowupSequenceData X)
section
variable (hmiss : IsDisjointFromCenters g t)
noncomputable def liftToLastOfFlatOfIsDisjointFromCenters : Y ⟶ t.obj t.length :=
  (liftOfIsDisjointFromCenters g t hmiss t.length le_rfl).1

section
variable (e : BlowupSequenceData Y) (he : e.length = 0)
noncomputable def mapToLastOfFlatOfLengthEqZero
    (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length) : e.toSequenceOfBlowups.schemeAt j ⟶ t.toSequenceOfBlowups.schemeAt t.length :=
  eqToHom (schemeAt_eq_schemeAt_zero_of_length_eq_zero e he j hj) ≫ e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss ≫
    eqToHom (t.toSequenceOfBlowups_schemeAt t.length).symm

end
end

noncomputable def ofCentersMissImage
    (hmiss : ∀ i : ℕ, i < t.length → ∀ z : ↥(t.obj i), z ∈ (t.center i).support →
      ∀ y : ↥Y, g.base y ≠ (t.projectionToBase i).base z)
    (e : BlowupSequenceData Y) (he : e.length = 0) :
    SequenceOfBlowupsPullback g e.toSequenceOfBlowups t.toSequenceOfBlowups where
  idx := fun _ => t.length
  map := mapToLastOfFlatOfLengthEqZero g t hmiss e he
  idx_length := (t.toSequenceOfBlowups_length).symm
  idx_lt := length_lt_toSequenceOfBlowups_length_of_lt t e he
  idx_strictMono := length_lt_length_of_lt_length_of_eq_zero t e he
  isPullback := by
    have hlen := e.toSequenceOfBlowups_length.trans he
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    have hpb :=
      (liftOfIsDisjointFromCenters g t hmiss t.length le_rfl).2
    have hiso : IsPullback e.isoZero.hom e.isoZero.hom (𝟙 Y) $ 𝟙 Y :=
      of_horiz_isIso ⟨rfl⟩
    have hcomp := hiso.paste_horiz hpb
    simp only [id_comp] at hcomp
    let _a0 := e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss
    have hmap : mapToLastOfFlatOfLengthEqZero g t hmiss e he 0 hj = _a0 := by
      show 𝟙 (e.obj 0) ≫ _a0 ≫ 𝟙 (t.obj t.length) =
        _a0
      simp
    have hs :=
      (e.toSequenceOfBlowups_projectionToBase 0).trans e.projectionToBase_zero
    have hf := t.toSequenceOfBlowups_projectionToBase t.length
    rw [hmap, hs, hf]
    exact hcomp
  step := by
    intro j hj
    have hlen := e.toSequenceOfBlowups_length.trans he
    exact absurd hj (by rw [hlen]; exact not_lt_zero j)
  center_comap := by
    have hlen := e.toSequenceOfBlowups_length.trans he
    intro j hj
    exact absurd hj $ by omega
  center_ne_top := center_ne_top_of_length_eq_zero e he
  omitted := disjoint_omitted_centers_of_disjoint_centers g t hmiss e he
end

end

section

section
variable {X'} (s' : BlowupSequenceData X') (n : BlowupSequenceData (s'.obj s'.length))
theorem schemeAt_eq_schemeAt_append (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    s'.toSequenceOfBlowups.schemeAt j = (append s' n).toSequenceOfBlowups.schemeAt j := by
  rw [p14] at hj
  rw [toSequenceOfBlowups_schemeAt s' j, toSequenceOfBlowups_schemeAt (append s' n) j,
    p40 s' n hj]

theorem le_length_append_of_length_eq_zero (hn : n.length = 0) (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    j ≤ (append s' n).toSequenceOfBlowups.length :=by simp_all
end

section
variable {X X'} (ph_) (s' : BlowupSequenceData X') (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0) (c : SequenceOfBlowupsPullback ph_ (append s' n).toSequenceOfBlowups s)
include hn c
noncomputable def mapOfAppendLengthEqZero (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    s'.toSequenceOfBlowups.schemeAt j ⟶ s.schemeAt (c.idx j) :=
  eqToHom (schemeAt_eq_schemeAt_append s' n j hj) ≫ c.map j (le_length_append_of_length_eq_zero s' n hn j hj)

theorem index_lt_index_succ_of_append_length_eq_zero :
    ∀ j : ℕ, j < s'.toSequenceOfBlowups.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  rw [p14] at hj
  refine c.idx_strictMono j ?_
  rw [p14, BlowupSequenceData.append_length, hn]
  omega

end

theorem comp_eqToHom_eq_eqToHom_comp {A B A' B' : Sch} (f : A ⟶ B) (f' : A' ⟶ B')
    (hA : A = A') (hB : B = B') (h : f' = eqToHom hA.symm ≫ f ≫ eqToHom hB) :
    f ≫ eqToHom hB = eqToHom hA ≫ f' :=by simp_all
theorem eqToHom_comp_eqToHom_comp_eq {A B C : Sch} (h : A = B) (h' : B = A)
    (g : A ⟶ C) : eqToHom h ≫ eqToHom h' ≫ g = g := by
  subst h
  simp

theorem comap_eqToHom_comap_eqToHom {A B : Sch} (h : A = B) (h' : B = A)
    (I : ISD A) : comap (comap I $ eqToHom h') (eqToHom h) = I := by
  subst h
  simp

section
variable {X X'} (ph_) (s' : BlowupSequenceData X') (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0) (c : SequenceOfBlowupsPullback ph_ (append s' n).toSequenceOfBlowups s)
noncomputable def ofConcatLengthZero :
    SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s where
  idx := c.idx
  map := mapOfAppendLengthEqZero ph_ s' s n hn c
  idx_length := by
    have h1 : (append s' n).toSequenceOfBlowups.length = s'.toSequenceOfBlowups.length := by simp_all
    rw [← h1]
    exact c.idx_length
  idx_lt := by
    intro j hj
    rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
    have h : j < (append s' n).toSequenceOfBlowups.length := by simp_all
    exact c.idx_lt j h
  idx_strictMono := index_lt_index_succ_of_append_length_eq_zero ph_ s' s n hn c
  isPullback := by
    intro j hj
    have hc := c.isPullback j $ le_length_append_of_length_eq_zero s' n hn j hj
    have hsq : CommSq (eqToHom $ schemeAt_eq_schemeAt_append s' n j hj) (s'.toSequenceOfBlowups.projectionToBase j)
        ((append s' n).toSequenceOfBlowups.projectionToBase j) $ 𝟙 X' := by
      constructor
      rw [comp_id]
      have hjl : j ≤ s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
      have h1 :=
        BlowupSequenceData.toSequenceOfBlowups_projectionToBase (append s' n) j
      have h2 := BlowupSequenceData.toSequenceOfBlowups_projectionToBase s' j
      rw [h1, h2, BlowupSequenceData.projectionToBase_append_of_le_length s' n hjl]
      exact eqToHom_comp_eqToHom_comp_eq _ _ _
    have hiso := of_horiz_isIso hsq
    have hpaste := hiso.paste_horiz hc
    rwa [id_comp] at hpaste
  step := by
    intro j hj
    have hjl : j < s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
    have hjc : j < (append s' n).toSequenceOfBlowups.length := by simp_all
    let _m0 := schemeAt_eq_schemeAt_append s' n j $ le_of_lt hj
    have hkey : s'.toSequenceOfBlowups.transitionMapSucc j ≫ eqToHom _m0 =
        eqToHom (schemeAt_eq_schemeAt_append s' n (j + 1) hj) ≫ (append s' n).toSequenceOfBlowups.transitionMapSucc j := by
      refine comp_eqToHom_eq_eqToHom_comp (s'.toSequenceOfBlowups.transitionMapSucc j) ((append s' n).toSequenceOfBlowups.transitionMapSucc j)
        (schemeAt_eq_schemeAt_append s' n (j + 1) hj) _m0 ?_
      rw [toSequenceOfBlowups_blowupMorphism, toSequenceOfBlowups_blowupMorphism]
      exact BlowupSequenceData.append_blowupMorphism_of_lt_length s' n hjl
    have hstep := c.step j hjc
    show s'.toSequenceOfBlowups.transitionMapSucc j ≫
        eqToHom _m0 ≫ c.map j (le_length_append_of_length_eq_zero s' n hn j $ le_of_lt hj) =
      (eqToHom (schemeAt_eq_schemeAt_append s' n (j + 1) hj) ≫ c.map (j + 1) (le_length_append_of_length_eq_zero s' n hn (j + 1) hj)) ≫
        s.transitionMap (le_of_lt $ index_lt_index_succ_of_append_length_eq_zero ph_ s' s n hn c j hj)
    rw [← assoc, hkey, assoc, hstep, assoc]
  center_comap := by
    intro j hj
    have hjl : j < s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
    have hj' : j < (append s' n).toSequenceOfBlowups.length := by simp_all
    have hc :=
      c.center_comap j hj'
    show s'.toSequenceOfBlowups.center j =
        (center s $ c.idx j).comap
          (eqToHom (schemeAt_eq_schemeAt_append s' n j $ le_of_lt hj) ≫ c.map j (le_length_append_of_length_eq_zero s' n hn j $ le_of_lt hj))
    rw [comap_comp, ← hc, toSequenceOfBlowups_center s' j,
      toSequenceOfBlowups_center (append s' n) j, BlowupSequenceData.append_center_of_lt_length s' n hjl]
    exact (comap_eqToHom_comap_eqToHom _ _ _).symm
  center_ne_top := by
    intro j hj
    have hjl : j < s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
    have hjc : j < (append s' n).toSequenceOfBlowups.length := by simp_all
    have hne := c.center_ne_top j hjc
    rw [toSequenceOfBlowups_center, BlowupSequenceData.append_center_of_lt_length s' n hjl] at hne
    rw [toSequenceOfBlowups_center]
    intro htop
    rw [htop] at hne
    exact hne $ comap_top _
  omitted := by
    intro i hi hmiss
    refine c.omitted i hi ?_
    intro j hj
    refine hmiss j ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn] at hj
    rw [BlowupSequenceData.toSequenceOfBlowups_length]
    omega
end

end

section

section
variable {Y T T' : Sch} {pi_ : T' ⟶ T} {I : ISD T} (hB : IsBlowupAlongIdealSheaf pi_ I) (u : Y ⟶ T) (htop : comap I u = ⊤)
include hB htop
theorem exists_lift_of_comap_eq_top :
    ∃ v, IsPullback v (𝟙 Y) pi_ u ∧ v ≫ pi_ = u := by
  let _a0 := pullback.snd pi_ u
  have hiso : IsIso _a0 := by
    have hEC : p17 $ comap I u := by
      rw [htop]
      exact isLocallyGeneratedByNonZeroDivisor_top Y
    obtain ⟨k, hk, -⟩ := hB.existsUnique_lift Y u hEC
    have hw : k ≫ pi_ = 𝟙 Y ≫ u := by rw [hk, id_comp]
    have hEC2 : p17 $ cmI I $ _a0 ≫ u := by
      have hc : cmI I (_a0 ≫ u) = cmI (comap I u) _a0 := by
        simp
      rw [hc, htop]
      exact isLocallyGeneratedByNonZeroDivisor_comap_top _
    refine ⟨⟨pullback.lift k (𝟙 Y) hw, ?_, ?_⟩⟩
    apply pullback.hom_ext
    rw [assoc, pullback.lift_fst, id_comp]
    refine hB.hom_ext_of_comp_eq hEC2 ?_ pullback.condition
    rw [assoc, hk]
    rw [assoc, pullback.lift_snd, comp_id, id_comp]
    rw [pullback.lift_snd]
  refine ⟨inv _a0 ≫ pullback.fst pi_ u, ?_, ?_⟩
  refine of_iso_pullback ⟨?_⟩ (asIso _a0).symm ?_ ?_
  rw [assoc, pullback.condition, IsIso.inv_hom_id_assoc, id_comp]
  simp
  simp
  rw [assoc, pullback.condition, IsIso.inv_hom_id_assoc]
end

section
variable {X Y : Sch} (g : Y ⟶ X) (t : BlowupSequenceData X)
theorem exists_lift_of_forall_comap_eq_top
    (h : ∀ i : ℕ, i < t.length → ∀ u : Y ⟶ t.obj i, IsPullback u (𝟙 Y) (t.projectionToBase i) g →
      comap (t.center i) u = ⊤) :
    ∀ i, i ≤ t.length → ∃ u, IsPullback u (𝟙 Y) (t.projectionToBase i) g := by
  intro i
  induction i with
  | zero =>
      intro _
      exact ⟨g ≫ t.isoZero.inv, isPullback_comp_isoObjZero_inv g t⟩
  | succ i ih =>
      intro hi
      have hi' : i < t.length := by omega
      obtain ⟨u, hu⟩ := ih $ le_of_lt hi'
      obtain ⟨v, hv, -⟩ : ∃ v : Y ⟶ t.obj (i + 1), IsPullback v (𝟙 Y) (t.projectionToBase $ i + 1) g ∧ v ≫ t.map i = u := by
        obtain ⟨v, hv, hvc⟩ := exists_lift_of_comap_eq_top (t.isBlowup i hi') u $ h i hi' u hu
        refine ⟨v, ?_, hvc⟩
        have hpaste := hv.paste_vert hu
        simp [comp_id] at hpaste
        rwa [p43]
      exact ⟨v, hv⟩
end

end

section

theorem exists_mem_support_center_append {X : Sch} (s : BlowupSequenceData X)
    (n : BlowupSequenceData $ s.obj s.length) :
    ∀ i (z : ↥(n.obj i)), z ∈ support (n.center i) →
      ∃ z' : ↥((append s n).obj $ s.length + i),
        z' ∈ support ((append s n).center $ s.length + i) ∧
          ((append s n).projectionToBase $ s.length + i).base z' =
            (s.projectionToBase s.length).base ((n.projectionToBase i).base z) := by
  intro i
  rcases m73 i with rfl | hipos
  intro z hz
  simp only [add_zero]
  refine ⟨bsM (eqToHom (p40 s n $ le_refl s.length).symm) $ n.isoZero.hom.base z, ?_, ?_⟩
  rw [BlowupSequenceData.append_center_length]
  refine mpr_ mem_support_comap ?_
  rw [eqToHom_base_trans, eqToHom_base_self]
  refine mpr_ mem_support_comap ?_
  rwa [inv_base_hom_base]
  rw [BlowupSequenceData.projectionToBase_append_of_le_length s n $ le_refl s.length, base_comp_apply,
    eqToHom_base_trans, eqToHom_base_self, p23]
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  intro z hz
  let _a0 := k + 1
  have hgt : s.length < s.length + _a0 := by omega
  have h1 := BlowupSequenceData.append_schemeAt_of_length_lt s n hgt
  have hsub : s.length + _a0 - s.length = k + 1 := by omega
  have hobj : n.obj (k + 1) = (append s n).obj (s.length + _a0) := by simp_all
  refine ⟨bsM (eqToHom hobj) z, ?_, ?_⟩
  rw [BlowupSequenceData.append_center_of_length_lt s n hgt]
  refine mpr_ mem_support_comap ?_
  rw [eqToHom_base_trans]
  exact eqToHom_base_mem_support_center n hsub.symm _ z hz
  rw [BlowupSequenceData.projectionToBase_append_of_length_lt s n hgt, base_comp_apply, base_comp_apply,
    eqToHom_base_trans, projectionToBase_base_eqToHom_base n hsub.symm]

section
variable {X Y} (g) (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t)
include hmiss
theorem exists_lift_schemeAt_length_of_disjoint_centers :
    ∃ u : Y ⟶ t.obj t.length, IsPullback u (𝟙 Y) (t.projectionToBase t.length) g :=
  exists_lift_of_forall_comap_eq_top g t
    (fun i hi u hu => comap_eq_top_of_forall_support_not_mem_range g (t.projectionToBase i) (t.center i) (hmiss i hi) u hu)
    t.length le_rfl

noncomputable def chosenLiftToLastOfIsDisjointFromCenters : Y ⟶ t.obj t.length :=
  (exists_lift_schemeAt_length_of_disjoint_centers g t hmiss).choose

section
variable (e : BlowupSequenceData Y) (he : e.length = 0)
noncomputable def mapToLastOfLengthEqZero
    (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length) : e.toSequenceOfBlowups.schemeAt j ⟶ t.toSequenceOfBlowups.schemeAt t.length :=
  eqToHom (schemeAt_eq_schemeAt_zero_of_length_eq_zero e he j hj) ≫ e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss ≫
    eqToHom (t.toSequenceOfBlowups_schemeAt t.length).symm

noncomputable def ofIsDisjointFromCenters :
    SequenceOfBlowupsPullback g e.toSequenceOfBlowups t.toSequenceOfBlowups where
  idx := fun _ => t.length
  map := mapToLastOfLengthEqZero g t hmiss e he
  idx_length := (t.toSequenceOfBlowups_length).symm
  idx_lt := length_lt_toSequenceOfBlowups_length_of_lt t e he
  idx_strictMono := length_lt_length_of_lt_length_of_eq_zero t e he
  isPullback := by
    have hlen := e.toSequenceOfBlowups_length.trans he
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    have hpb :=
      by
      exact (exists_lift_schemeAt_length_of_disjoint_centers g t hmiss).choose_spec
    have hiso : IsPullback e.isoZero.hom e.isoZero.hom (𝟙 Y) $ 𝟙 Y :=
      of_horiz_isIso ⟨rfl⟩
    have hcomp := hiso.paste_horiz hpb
    simp only [id_comp] at hcomp
    let _a0 := e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss
    have hmap : mapToLastOfLengthEqZero g t hmiss e he 0 hj =
        _a0 := by
      show 𝟙 (e.obj 0) ≫ _a0 ≫ 𝟙 (t.obj t.length) =
        _a0
      simp
    have hs :=
      (e.toSequenceOfBlowups_projectionToBase 0).trans e.projectionToBase_zero
    have hf := t.toSequenceOfBlowups_projectionToBase t.length
    rw [hmap, hs, hf]
    exact hcomp
  step := by
    intro j hj
    have hlen := e.toSequenceOfBlowups_length.trans he
    exact absurd hj (by rw [hlen]; exact not_lt_zero j)
  center_comap := by
    have hlen := e.toSequenceOfBlowups_length.trans he
    intro j hj
    exact absurd hj $ by omega
  center_ne_top := center_ne_top_of_length_eq_zero e he
  omitted := disjoint_omitted_centers_of_disjoint_centers g t hmiss e he
end
end

section
variable {X X'} (ph_ : X' ⟶ X) (s' : BlowupSequenceData X') (s : BlowupSequenceData X) (n : BlowupSequenceData (s.obj s.length)) (c : SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups s.toSequenceOfBlowups) (hmiss : ∀ i : ℕ, s.length ≤ i → i < s.length + n.length → ∀ z : ↥((append s n).obj i), z ∈ support ((append s n).center i) → ∀ x' : ↥X', ph_.base x' ≠ ((append s n).projectionToBase i).base z)
include c hmiss
theorem nonempty_append_of_disjoint_centers :
    Nonempty $ SequenceOfBlowupsPullback ph_ s'.toSequenceOfBlowups (append s n).toSequenceOfBlowups := by
  have hmiss : IsDisjointFromCenters c.lastMap n := by
    intro i hi z hz y hyeq
    obtain ⟨z', hz', hp⟩ := exists_mem_support_center_append s n i z hz
    refine hmiss (s.length + i) (le_add_right _ _) (by omega) z' hz'
        (bsM (s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length) y) ?_
    exact tr_ (st_ ((base_comp_apply c.lastMap (s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length) y).symm.trans $ tr_ (congrArg (fun f : s'.toSequenceOfBlowups.schemeAt s'.toSequenceOfBlowups.length ⟶ X => bsM f y) c.isPullback_lastMap.w) $ base_comp_apply (s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length) ph_ y) $ congrArg (fun f : s.obj s.length ⟶ X => bsM f $ c.lastMap.base y) $ p36 s s.length)
      (tr_ (congrArg (fun w : (s.obj s.length) => bsM (s.projectionToBase s.length) w) hyeq) hp.symm)
  have hE :=
    emptyBlowupSequenceData_length $ s'.obj s'.length
  let _m0 := emptyBlowupSequenceData $ s'.obj s'.length
  exact ⟨ofConcatLengthZero ph_ s' (append s n).toSequenceOfBlowups _m0 hE
    (SequenceOfBlowupsPullback.concat s n s' _m0 c $ ofIsDisjointFromCenters c.lastMap n hmiss _m0 hE)⟩
end

end

end SequenceOfBlowupsPullback





namespace SequenceOfBlowupsPullback

variable {X X' : Sch}

def prependIndex (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) => f n + 1

section
variable (f : ℕ → ℕ)
@[simp] theorem prependIndex_zero : prependIndex f 0 = 0 := rfl

@[simp] theorem prependIndex_succ (n : ℕ) : prependIndex f (n + 1) = f n + 1 := rfl

def succIndex : ℕ → ℕ := fun j => f j + 1

@[simp] theorem succIndex_apply (j : ℕ) : succIndex f j = f j + 1 := rfl
end

section
variable {ph_} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback ph_ d'.toSequenceOfBlowups d.toSequenceOfBlowups)
include c
theorem succIndex_lt_succIndex_succ (Z : ISD X)
    (_hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    succIndex c.idx j < succIndex c.idx (j + 1) := by
  have h := c.idx_strictMono j hj
  simp [succIndex_apply]
  omega

theorem center_ne_top_of_prepend_comap_eq_top (_Z : ISD X)
    (_hZ : IsBlowupAlongIdealSheaf (𝟙 X) _Z) (j : ℕ) (hj : j < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.center j ≠ ⊤ := c.center_ne_top j hj
end

section
variable {Y : Sch} (Z) (hZ : IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y)
section
variable (n : ℕ)
theorem prepend_projectionToBase_succ :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1) = d.projectionToBase n := by
  let _a0 := p18 Z hZ d
  induction n with
  | zero =>
      rw [p43 _a0 0,
        BlowupSequenceData.prepend_blowupMorphism_zero Z hZ d,
        p23 _a0]
      exact tr_ (comp_id _) (p23 d).symm
  | succ m ih =>
      rw [p43 _a0 $ m + 1,
        BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d m, ih]
      exact sy_ $ p43 d m

theorem prepend_toSequenceOfBlowups_projectionToBase_succ :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase (n + 1) = d.toSequenceOfBlowups.projectionToBase n :=
  (p36 (p18 Z hZ d) $ n + 1).trans
    (tr_ (prepend_projectionToBase_succ Z hZ d n) (p36 d n).symm)

private theorem prepend_blowupMorphism_succ :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMapSucc (n + 1) = d.toSequenceOfBlowups.transitionMapSucc n := by
  rw [p50, p50, BlowupSequenceData.prepend_blowupMorphism_succ]

theorem prepend_transitionMap_succ_self (h : n + 1 ≤ n + 1 + 1)
    (h' : n ≤ n + 1) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h = d.toSequenceOfBlowups.transitionMap h' :=
  (st_ (blowupMorphism_eq_transitionMap (p18 Z hZ d).toSequenceOfBlowups $ n + 1)
      (prepend_blowupMorphism_succ Z hZ d n)).trans
    (blowupMorphism_eq_transitionMap d.toSequenceOfBlowups n)

private theorem prepend_center_succ :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (n + 1) = d.toSequenceOfBlowups.center n :=
  (p24 (p18 Z hZ d) $ n + 1).trans
    (tr_ (BlowupSequenceData.prepend_center_succ Z hZ d n) (p24 d n).symm)
end

theorem prepend_transitionMap_succ_succ {a b : ℕ} (hab : a ≤ b)
    (h : a + 1 ≤ b + 1) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h = d.toSequenceOfBlowups.transitionMap hab := by
  let _a1 := p18 Z hZ d
  revert h
  induction b, hab using le_induction with
  | base =>
      intro h
      exact tr_ (transitionMap_self _a1.toSequenceOfBlowups h)
        (transitionMap_self d.toSequenceOfBlowups $ le_refl a).symm
  | succ m hm ih =>
      intro h
      let _a2 := Nat.add_le_add_right hm 1
      let _a0 := le_succ $ m + 1
      rw [(transitionMap_trans _a1.toSequenceOfBlowups _a2 _a0).symm, ih _a2, prepend_transitionMap_succ_self Z hZ d m _a0 $ le_succ m]
      exact transitionMap_trans d.toSequenceOfBlowups hm $ le_succ m

theorem prepend_transitionMap_zero (m : ℕ) (h : 0 ≤ m) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap h =
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase m := by
  rw [projectionToBase_def, toSequenceOfBlowups_isoObjZero, prepend_isoObjZero,
    refl_hom]
  exact sy_ $ comp_id _

theorem prepend_toSequenceOfBlowups_projectionToBase_zero :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase 0 = 𝟙 Y :=
  (p36 (p18 Z hZ d) 0).trans
    (tr_ (p23 $ p18 Z hZ d) rfl)

theorem prepend_blowupMorphism_zero_eq_projectionToBase :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMapSucc 0 = d.toSequenceOfBlowups.projectionToBase 0 := by
  rw [p50, BlowupSequenceData.prepend_blowupMorphism_zero, SequenceOfBlowups.projectionToBase_zero,
    toSequenceOfBlowups_isoObjZero]
end

section
variable (Z) (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X)
private theorem prepend_schemeAt_zero : (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt 0 = X :=
  (toSequenceOfBlowups_schemeAt (p18 Z hZ d) 0).trans
    (BlowupSequenceData.prepend_schemeAt_zero Z hZ d)

private theorem prepend_schemeAt_succ (n : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt (n + 1) = d.toSequenceOfBlowups.schemeAt n :=
  (toSequenceOfBlowups_schemeAt (p18 Z hZ d) $ n + 1).trans
    (tr_ (BlowupSequenceData.prepend_schemeAt_succ Z hZ d n) (toSequenceOfBlowups_schemeAt d n).symm)

private theorem prepend_length :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length = d.toSequenceOfBlowups.length + 1 :=by simp_all
theorem le_length_of_succ_le_prepend_length (n : ℕ)
    (h : n + 1 ≤ (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length) : n ≤ d.toSequenceOfBlowups.length :=by simp_all
end

section
variable {ph_ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback ph_ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : ISD X)
include c
section
variable (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : IsBlowupAlongIdealSheaf (𝟙 X') (comap Z ph_))
theorem ne_projectionToBase_of_forall_prependIndex_ne (i : ℕ)
    (hi : i < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length)
    (hmiss : ∀ j : ℕ, j < (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length →
      prependIndex c.idx j ≠ i)
    (z : ↥((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt i))
    (hz : z ∈ support ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center i)) (x' : ↥X') :
    ph_.base x' ≠ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase i).base z := by
  have hlen' :=
    prepend_length (comap Z ph_) hZ' d'
  have hlen :=
    prepend_length Z hZ d
  have h0 := hmiss 0 $ by omega
  rw [prependIndex_zero] at h0
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hn : n < d.toSequenceOfBlowups.length := by omega
  have hmiss' : ∀ m, m < d'.toSequenceOfBlowups.length → c.idx m ≠ n := by
    intro m hm hmn
    exact hmiss (m + 1) (by omega) $ by rw [prependIndex_succ, hmn]
  have hzc : z ∈ support (d.toSequenceOfBlowups.center n) := by
    have hz2 := hz
    rwa [prepend_center_succ Z hZ d n] at hz2
  intro heq
  refine c.omitted n hn hmiss' z hzc x' ?_
  rwa [← prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d n]

theorem prependIndex_lt_prepend_length (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length) :
    prependIndex c.idx j < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  rw [prepend_length (cmI Z ph_) hZ' d'] at hj
  rw [prepend_length Z hZ d]
  cases j with
  | zero =>
      simp only [prependIndex_zero]
      omega
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by omega
      have hc := c.idx_lt n hn
      simp only [prependIndex_succ]
      omega
end

theorem prependIndex_lt_prependIndex_succ
    (_hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : IsBlowupAlongIdealSheaf (𝟙 X') $ comap Z ph_) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length) :
    prependIndex c.idx j < prependIndex c.idx (j + 1) := by
  cases j with
  | zero =>
      simp only [prependIndex_zero, prependIndex_succ]
      omega
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by simp_all
      have hstep := c.idx_strictMono n hn
      simp only [prependIndex_succ]
      omega

theorem prepend_center_ne_top
    (_hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : IsBlowupAlongIdealSheaf (𝟙 X') $ comap Z ph_) (hne : comap Z ph_ ≠ ⊤) (j : ℕ)
    (hj : j < (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length) :
    (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.center j ≠ ⊤ := by
  let _a0 := p18 (comap Z ph_) hZ' d'
  have hlen :=
    prepend_length (comap Z ph_) hZ' d'
  cases j with
  | zero =>
      have h0 :=
        (p24 _a0 0).trans
          (BlowupSequenceData.prepend_center_zero (comap Z ph_) hZ' d')
      intro htop
      exact hne $ h0.symm.trans htop
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by omega
      have h1 :=
        (p24 _a0 $ n + 1).trans
          (tr_ (BlowupSequenceData.prepend_center_succ (comap Z ph_) hZ' d' n)
            (p24 d' n).symm)
      intro htop
      exact c.center_ne_top n hn $ st_ h1 htop
end

section
variable {A B : Sch} (f : A ⟶ B)
theorem eqToHom_comp_comp_eqToHom_refl (h1 : A = A)
    (h2 : B = B) : eqToHom h1 ≫ f ≫ eqToHom h2 = f :=by simp_all
theorem comp_eqToHom_refl (h : B = B) :
    f ≫ eqToHom h = f :=by simp_all
end

theorem comp_eq_comp_of_heq {A' B' A B Y' Y V' V : Sch}
    (e0' : A' = Y') (e1' : B' = V') (e0 : A = Y) (e1 : B = V)
    {s' : V' ⟶ Y'} {ps_ : Y' ⟶ Y} {m : V' ⟶ V} {s : V ⟶ Y}
    (hw : m ≫ s = s' ≫ ps_)
    {L1 : B' ⟶ A'} {L2 : A' ⟶ A} {R1 : B' ⟶ B} {R2 : B ⟶ A}
    (hL1 : HEq L1 s') (hL2 : HEq L2 ps_) (hR1 : HEq R1 m) (hR2 : HEq R2 s) :
    L1 ≫ L2 = R1 ≫ R2 := by
  subst e0'
  subst e1'
  subst e0
  subst e1
  rw [eq_of_heq hL1, eq_of_heq hL2, eq_of_heq hR1, eq_of_heq hR2, hw]

theorem comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq {A A' B B' : Sch} (hA : A' = A) (hB : B = B')
    (g : A ⟶ B) (J : ISD B) (K : ISD A) (hK : K = comap J g)
    (J' : ISD A') (Jb : ISD B')
    (hJb : HEq Jb J) (hJ' : HEq J' K) :
    J' = comap Jb (eqToHom hA ≫ g ≫ eqToHom hB) := by
  subst hA
  subst hB
  rw [eq_of_heq hJb, eq_of_heq hJ', hK]
  simp

theorem comap_eq_comap_comp_eqToHom_of_heq {A B B' : Sch} (hB : B = B') (g : A ⟶ B)
    (J : ISD B) (J' : ISD B') (K : ISD A)
    (hK : K = comap J g) (hJ : HEq J' J) :
    K = comap J' (g ≫ eqToHom hB) := by
  subst hB
  have h1 := eq_of_heq hJ
  subst h1
  rw [hK]
  simp

def prependMapOfLELength {ph_ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : SequenceOfBlowupsPullback ph_ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : ISD X)
    (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : IsBlowupAlongIdealSheaf (𝟙 X') $ comap Z ph_) :
    ∀ j : ℕ, j ≤ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length →
      ((BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.schemeAt j ⟶
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt (prependIndex c.idx j))
  | 0, _ =>
      eqToHom (prepend_schemeAt_zero (comap Z ph_) hZ' d') ≫ ph_ ≫
        eqToHom (prepend_schemeAt_zero Z hZ d).symm
  | (n + 1), h =>
      eqToHom (prepend_schemeAt_succ (comap Z ph_) hZ' d' n) ≫
        c.map n (le_length_of_succ_le_prepend_length (comap Z ph_) hZ' d' n h) ≫
        eqToHom (prepend_schemeAt_succ Z hZ d $ c.idx n).symm

section
variable {ph_ : X' ⟶ X} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (c : SequenceOfBlowupsPullback ph_ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : ISD X) (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z)
section
variable (hZ' : IsBlowupAlongIdealSheaf (𝟙 X') (comap Z ph_))
section
variable (hj : 0 ≤ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length)
theorem prependComparisonMap_zero :
    prependMapOfLELength c Z hZ hZ' 0 hj = ph_ := by
  show 𝟙 X' ≫ ph_ ≫ 𝟙 X = ph_
  simp

theorem isPullback_prependComparisonMap_zero :
    IsPullback (prependMapOfLELength c Z hZ hZ' 0 hj)
      ((BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.projectionToBase 0)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase $ prependIndex c.idx 0) ph_ := by
  have key : IsPullback ph_ (𝟙 X') (𝟙 X) ph_ := (of_horiz_isIso ⟨by simp⟩).flip
  have h1 : prependMapOfLELength c Z hZ hZ' 0 hj = ph_ := prependComparisonMap_zero c Z hZ hZ' hj
  have h2 : (p18 (cmI Z ph_) hZ' d').toSequenceOfBlowups.projectionToBase 0 = 𝟙 X' :=
    prepend_toSequenceOfBlowups_projectionToBase_zero (cmI Z ph_) hZ' d'
  have h3 : (p18 Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx 0) = 𝟙 X :=
    prepend_toSequenceOfBlowups_projectionToBase_zero Z hZ d
  rwa [h1, h2, h3]
end

theorem prependComparisonMap_succ (n : ℕ)
    (h : n + 1 ≤ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length)
    (hn : n ≤ d'.toSequenceOfBlowups.length) :
    prependMapOfLELength c Z hZ hZ' (n + 1) h = c.map n hn := by
  let _a0 := prepend_schemeAt_succ (cmI Z ph_) hZ' d' n
  let _a1 := prepend_schemeAt_succ Z hZ d $ c.idx n
  show eqToHom _a0 ≫
      c.map n (le_length_of_succ_le_prepend_length (cmI Z ph_) hZ' d' n h) ≫
      eqToHom _a1.symm = c.map n hn
  exact eqToHom_comp_comp_eqToHom_refl (c.map n hn) _a0
    _a1.symm

theorem isPullback_prependComparisonMap_succ (n : ℕ)
    (hj : n + 1 ≤ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length) :
    IsPullback (prependMapOfLELength c Z hZ hZ' (n + 1) hj)
      ((BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.projectionToBase $ n + 1)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase $ prependIndex c.idx $ n + 1) ph_ := by
  let _a0 := le_length_of_succ_le_prepend_length (cmI Z ph_) hZ' d' n hj
  have h3 : (p18 Z hZ d).toSequenceOfBlowups.projectionToBase (prependIndex c.idx $ n + 1) =
      d.toSequenceOfBlowups.projectionToBase (c.idx n) := prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d $ c.idx n
  rw [prependComparisonMap_succ c Z hZ hZ' n hj _a0, prepend_toSequenceOfBlowups_projectionToBase_succ (cmI Z ph_) hZ' d' n, h3]
  exact c.isPullback n _a0

section
variable (j : ℕ)
theorem isPullback_prependComparisonMap
    (hj : j ≤ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length) :
    IsPullback (prependMapOfLELength c Z hZ hZ' j hj)
      ((BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.projectionToBase j)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase $ prependIndex c.idx j) ph_ := by
  cases j with
  | zero => exact isPullback_prependComparisonMap_zero c Z hZ hZ' _
  | succ n => exact isPullback_prependComparisonMap_succ c Z hZ hZ' n _

section
variable (hj : j < (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length)
theorem blowupMorphism_comp_prependComparisonMap :
    (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.transitionMapSucc j ≫
        prependMapOfLELength c Z hZ hZ' j (le_of_lt hj) =
      prependMapOfLELength c Z hZ hZ' (j + 1) hj ≫
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap
          (le_of_lt $ prependIndex_lt_prependIndex_succ c Z hZ hZ' j hj) := by
  cases j with
  | zero =>
      have hlen : 0 ≤ d'.toSequenceOfBlowups.length := zero_le _
      exact comp_eq_comp_of_heq (prepend_schemeAt_zero (cmI Z ph_) hZ' d')
        (prepend_schemeAt_succ (cmI Z ph_) hZ' d' 0)
        (prepend_schemeAt_zero Z hZ d)
        (prepend_schemeAt_succ Z hZ d $ c.idx 0)
        ((c.isPullback 0 hlen).w) (heq_of_eq $ prepend_blowupMorphism_zero_eq_projectionToBase (cmI Z ph_) hZ' d') (heq_of_eq $ prependComparisonMap_zero c Z hZ hZ' $ le_of_lt hj) (heq_of_eq $ prependComparisonMap_succ c Z hZ hZ' 0 hj hlen) $ heq_of_eq $ tr_ (prepend_transitionMap_zero Z hZ d (c.idx 0 + 1) $ zero_le _) $ prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d $ c.idx 0
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by simp_all
      exact comp_eq_comp_of_heq (prepend_schemeAt_succ (cmI Z ph_) hZ' d' n)
        (prepend_schemeAt_succ (cmI Z ph_) hZ' d' $ n + 1)
        (prepend_schemeAt_succ Z hZ d $ c.idx n)
        (prepend_schemeAt_succ Z hZ d $ c.idx $ n + 1)
        (sy_ $ c.step n hn) (heq_of_eq $ prepend_blowupMorphism_succ (cmI Z ph_) hZ' d' n) (heq_of_eq $ prependComparisonMap_succ c Z hZ hZ' n (le_of_lt hj) $ le_of_lt hn) (heq_of_eq $ prependComparisonMap_succ c Z hZ hZ' (n + 1) hj hn) $ heq_of_eq $ prepend_transitionMap_succ_succ Z hZ d (le_of_lt $ c.idx_strictMono n hn) $ add_le_add_right (le_of_lt $ c.idx_strictMono n hn) 1

theorem prepend_center_eq_comap_prependIndex :
    (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.center j =
      comap ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (prependIndex c.idx j))
        (prependMapOfLELength c Z hZ hZ' j (le_of_lt hj)) := by
  let _a0 := p18 Z hZ d
  let _c0 := p18 (cmI Z ph_) hZ' d'
  cases j with
  | zero =>
      exact comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq (prepend_schemeAt_zero (cmI Z ph_) hZ' d')
        (prepend_schemeAt_zero Z hZ d).symm ph_ Z (cmI Z ph_) rfl
        (_c0.toSequenceOfBlowups.center 0)
        (_a0.toSequenceOfBlowups.center 0) (heq_of_eq (tr_ (p24 _a0 0) (BlowupSequenceData.prepend_center_zero Z hZ d))) (heq_of_eq (tr_ (p24 _c0 0) (BlowupSequenceData.prepend_center_zero (cmI Z ph_) hZ' d')))
  | succ n =>
      have hlen := prepend_length (comap Z ph_) hZ' d'
      have hn' : n < d'.toSequenceOfBlowups.length := by omega
      refine comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq (prepend_schemeAt_succ (cmI Z ph_) hZ' d' n)
        (prepend_schemeAt_succ Z hZ d (c.idx n)).symm (c.map n (le_of_lt hn'))
        (d.toSequenceOfBlowups.center (c.idx n)) (d'.toSequenceOfBlowups.center n) (c.center_comap n hn')
        (_c0.toSequenceOfBlowups.center (n + 1))
        (_a0.toSequenceOfBlowups.center (c.idx n + 1)) ?_ ?_
      exact heq_of_eq
        (tr_ (p24 _a0 (c.idx n + 1))
          (tr_ (BlowupSequenceData.prepend_center_succ Z hZ d (c.idx n))
            (p24 d (c.idx n)).symm))
      exact heq_of_eq
        (tr_ (p24 _c0 (n + 1))
          (tr_ (BlowupSequenceData.prepend_center_succ (cmI Z ph_) hZ' d' n)
            (p24 d' n).symm))
end
end

def prepend (hne : comap Z ph_ ≠ ⊤) :
    SequenceOfBlowupsPullback ph_ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups where
  idx := prependIndex c.idx
  map := prependMapOfLELength c Z hZ hZ'
  idx_length := by
    rw [prepend_length, prepend_length, prependIndex_succ, c.idx_length]
  idx_lt := prependIndex_lt_prepend_length c Z hZ hZ'
  idx_strictMono := prependIndex_lt_prependIndex_succ c Z hZ hZ'
  isPullback := isPullback_prependComparisonMap c Z hZ hZ'
  step := blowupMorphism_comp_prependComparisonMap c Z hZ hZ'
  center_comap := prepend_center_eq_comap_prependIndex c Z hZ hZ'
  center_ne_top := prepend_center_ne_top c Z hZ hZ' hne
  omitted := ne_projectionToBase_of_forall_prependIndex_ne c Z hZ hZ'
end

theorem ne_projectionToBase_of_forall_succIndex_ne (htop : comap Z ph_ = ⊤) (i : ℕ)
    (hi : i < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length)
    (hmiss : ∀ j : ℕ, j < d'.toSequenceOfBlowups.length → succIndex c.idx j ≠ i)
    (z : ↥((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt i))
    (hz : z ∈ support ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center i)) (x' : ↥X') :
    ph_.base x' ≠ ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase i).base z := by
  have hlen :=
    prepend_length Z hZ d
  cases i with
  | zero =>
      intro heq
      have hzZ : z ∈ spI Z := by
        rwa [tr_ (p24 (p18 Z hZ d) 0) $ BlowupSequenceData.prepend_center_zero Z hZ d] at hz
      have hst :=
        prepend_toSequenceOfBlowups_projectionToBase_zero Z hZ d
      have hb : bsM ph_ x' ∈ spI Z := by
        rwa [heq, hst]
      have hmem :=
        mpr mem_support_comap hb
      exact ne_top_of_mem_support
        (cmI Z ph_) x' hmem htop
  | succ n =>
      have hn : n < d.toSequenceOfBlowups.length := by omega
      have hmiss' : ∀ m, m < d'.toSequenceOfBlowups.length → c.idx m ≠ n := by
        intro m hm hmn
        exact hmiss m hm $ by rw [succIndex_apply, hmn]
      have hzc : z ∈ spI (d.toSequenceOfBlowups.center n) := by
        have hz2 := hz
        rwa [prepend_center_succ Z hZ d n] at hz2
      intro heq
      refine c.omitted n hn hmiss' z hzc x' ?_
      rwa [← prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d n]

section
variable (j : ℕ)
section
variable (hj : j ≤ d'.toSequenceOfBlowups.length)
def mapToPrependSuccIndex :
    d'.toSequenceOfBlowups.schemeAt j ⟶ (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt (succIndex c.idx j) :=
  c.map j hj ≫ eqToHom (prepend_schemeAt_succ Z hZ d $ c.idx j).symm

theorem isPullback_comparisonMapOfComapEqTop :
    IsPullback (mapToPrependSuccIndex c Z hZ j hj) (d'.toSequenceOfBlowups.projectionToBase j)
      ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.projectionToBase $ succIndex c.idx j) ph_ := by
  have h1 : mapToPrependSuccIndex c Z hZ j hj = c.map j hj := by
    show c.map j hj ≫ 𝟙 (d.toSequenceOfBlowups.schemeAt $ c.idx j) = c.map j hj
    simp
  have h2 : (p18 Z hZ d).toSequenceOfBlowups.projectionToBase (succIndex c.idx j) =
      d.toSequenceOfBlowups.projectionToBase (c.idx j) := prepend_toSequenceOfBlowups_projectionToBase_succ Z hZ d $ c.idx j
  rw [h1, h2]
  exact c.isPullback j hj

theorem comparisonMapOfComapEqTop_eq_map :
    mapToPrependSuccIndex c Z hZ j hj = c.map j hj :=
  comp_eqToHom_refl (c.map j hj) (prepend_schemeAt_succ Z hZ d $ c.idx j).symm
end

section
variable (hj : j < d'.toSequenceOfBlowups.length)
include hj
theorem succIndex_lt_prepend_length :
    succIndex c.idx j < (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.length := by
  have hc := c.idx_lt j hj
  rw [prepend_length Z hZ d, succIndex_apply]
  omega

theorem blowupMorphism_comp_comparisonMapOfComapEqTop :
    d'.toSequenceOfBlowups.transitionMapSucc j ≫ mapToPrependSuccIndex c Z hZ j (le_of_lt hj) =
      mapToPrependSuccIndex c Z hZ (j + 1) hj ≫
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMap
          (le_of_lt $ succIndex_lt_succIndex_succ c Z hZ j hj) := by
  let _a0 := le_of_lt $ succIndex_lt_succIndex_succ c Z hZ j hj
  let _a1 := le_of_lt $ c.idx_strictMono j hj
  have hdown : (p18 Z hZ d).toSequenceOfBlowups.transitionMap
        _a0 =
      d.toSequenceOfBlowups.transitionMap _a1 :=
    prepend_transitionMap_succ_succ Z hZ d _a1
      _a0
  rw [comparisonMapOfComapEqTop_eq_map c Z hZ j $ le_of_lt hj, comparisonMapOfComapEqTop_eq_map c Z hZ (j + 1) hj, hdown]
  exact c.step j hj

theorem center_eq_comap_prepend_center_succIndex :
    d'.toSequenceOfBlowups.center j =
      comap ((BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center (succIndex c.idx j))
        (mapToPrependSuccIndex c Z hZ j (le_of_lt hj)) := by
  let _a3 := p18 Z hZ d
  let _a0 := _a3.toSequenceOfBlowups.center $ c.idx j + 1
  let _a1 := prepend_schemeAt_succ Z hZ d $ c.idx j
  let _a2 := c.map j $ le_of_lt hj
  show d'.toSequenceOfBlowups.center j =
      comap _a0
        (_a2 ≫ eqToHom _a1.symm)
  exact comap_eq_comap_comp_eqToHom_of_heq _a1.symm
    _a2 (d.toSequenceOfBlowups.center (c.idx j))
    _a0
    (d'.toSequenceOfBlowups.center j) (c.center_comap j hj) (heq_of_eq ((p24 _a3 (c.idx j + 1)).trans (tr_ (BlowupSequenceData.prepend_center_succ Z hZ d (c.idx j)) (p24 d (c.idx j)).symm)))
end
end

def prependOfComapEqTop (htop : comap Z ph_ = ⊤) :
    SequenceOfBlowupsPullback ph_ d'.toSequenceOfBlowups (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups where
  idx := succIndex c.idx
  map := mapToPrependSuccIndex c Z hZ
  idx_length := by
    rw [succIndex_apply, prepend_length, c.idx_length]
  idx_lt := succIndex_lt_prepend_length c Z hZ
  idx_strictMono := succIndex_lt_succIndex_succ c Z hZ
  isPullback := isPullback_comparisonMapOfComapEqTop c Z hZ
  step := blowupMorphism_comp_comparisonMapOfComapEqTop c Z hZ
  center_comap := center_eq_comap_prepend_center_succIndex c Z hZ
  center_ne_top := center_ne_top_of_prepend_comap_eq_top c Z hZ
  omitted := ne_projectionToBase_of_forall_succIndex_ne c Z hZ htop
end

end SequenceOfBlowupsPullback

section
variable {X X' : Sch} {ph_} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (h : IsPullbackBlowupSequence ph_ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : ISD X) (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z)
include h
theorem IsPullbackBlowupSequence.prepend_of_comap_ne_top (hZ' : IsBlowupAlongIdealSheaf (𝟙 X') (comap Z ph_)) (hne : comap Z ph_ ≠ ⊤) :
    IsPullbackBlowupSequence ph_ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups := by
  obtain ⟨c⟩ := h.nonempty_sequenceOfBlowupsPullback
  exact (c.prepend Z hZ hZ' hne).isPullbackSequenceOfBlowups

theorem IsPullbackBlowupSequence.prepend_of_comap_eq_top (htop : comap Z ph_ = ⊤) :
    IsPullbackBlowupSequence ph_ d'.toSequenceOfBlowups (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups := by
  obtain ⟨c⟩ := h.nonempty_sequenceOfBlowupsPullback
  exact (c.prependOfComapEqTop Z hZ htop).isPullbackSequenceOfBlowups
end

section
variable {Y : Sch} (Z) (hZ : IsBlowupAlongIdealSheaf (𝟙 Y) Z) (d : BlowupSequenceData Y)
theorem prepend_isoObjZero_hom :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.isoZero.hom = 𝟙 Y := by
  rw [toSequenceOfBlowups_isoObjZero, prepend_isoObjZero, refl_hom]

private theorem prepend_blowupMorphism_zero :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.transitionMapSucc 0 = d.toSequenceOfBlowups.isoZero.hom := by
  rw [p50, BlowupSequenceData.prepend_blowupMorphism_zero, toSequenceOfBlowups_isoObjZero]

private theorem prepend_center_zero :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.center 0 = Z :=
  (p24 (p18 Z hZ d) 0).trans
    (BlowupSequenceData.prepend_center_zero Z hZ d)
end

theorem eqToHom_conj_comp_eq_comp_of_heq_id {A B P Q : Sch} (eP : P = A) (eQ : Q = B)
    (ps_ : A ⟶ B) (I : Q ⟶ B) (J : P ⟶ A) (hI : HEq I $ 𝟙 B) (hJ : HEq J $ 𝟙 A) :
    (eqToHom eP ≫ ps_ ≫ eqToHom eQ.symm) ≫ I = J ≫ ps_ := by
  subst eP
  subst eQ
  rw [eq_of_heq hI, eq_of_heq hJ]
  simp

private theorem isPullback_congr {P Q R S : Sch} {f f' : P ⟶ Q} {g g' : P ⟶ R}
    {h h' : Q ⟶ S} {k k' : R ⟶ S} (hf : f = f') (hg : g = g') (hh : h = h') (hk : k = k')
    (H : IsPullback f' g' h' k') : IsPullback f g h k :=by simp_all
def prependMapOfLevelwise {X X' : Sch} (ph_ : X' ⟶ X) {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (Z : ISD X) (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (hZ' : IsBlowupAlongIdealSheaf (𝟙 X') $ comap Z ph_)
    (σ : ∀ i : ℕ, i ≤ d'.toSequenceOfBlowups.length → (d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i)) :
    ∀ i : ℕ, i ≤ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length →
      ((BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.schemeAt i ⟶
        (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups.schemeAt i)
  | 0, _ =>
      eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_zero (comap Z ph_) hZ' d') ≫ ph_ ≫
        eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_zero Z hZ d).symm
  | (n + 1), h =>
      eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_succ (comap Z ph_) hZ' d' n) ≫
        σ n (SequenceOfBlowupsPullback.le_length_of_succ_le_prepend_length (comap Z ph_) hZ' d' n h) ≫
        eqToHom (SequenceOfBlowupsPullback.prepend_schemeAt_succ Z hZ d n).symm

section
variable {X X' : Sch}
section
variable (ph_) {d' : BlowupSequenceData X'} {d : BlowupSequenceData X} (Z : ISD X) (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : IsBlowupAlongIdealSheaf (𝟙 X') (comap Z ph_)) (σ : ∀ i : ℕ, i ≤ d'.toSequenceOfBlowups.length → (d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i))
theorem strictPrependComparisonMap_succ (n : ℕ)
    (h : n + 1 ≤ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups.length)
    (hn : n ≤ d'.toSequenceOfBlowups.length) :
    prependMapOfLevelwise ph_ Z hZ hZ' σ (n + 1) h = σ n hn := by
  show 𝟙 (d'.toSequenceOfBlowups.schemeAt n) ≫ σ n hn ≫ 𝟙 (d.toSequenceOfBlowups.schemeAt n) = σ n hn
  simp
end

theorem IsStrictPullbackBlowupSeq.prepend {ph_ : X' ⟶ X} {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (h : IsStrictPullbackBlowupSeq ph_ d'.toSequenceOfBlowups d.toSequenceOfBlowups) (Z : ISD X)
    (hZ : IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : IsBlowupAlongIdealSheaf (𝟙 X') (comap Z ph_)) :
    IsStrictPullbackBlowupSeq ph_ (BlowupSequenceData.prepend (comap Z ph_) hZ' d').toSequenceOfBlowups
      (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups := by
  let _a0 := p18 (comap Z ph_) hZ' d'
  let _a1 := SequenceOfBlowupsPullback.prepend_length (comap Z ph_) hZ' d'
  let _a2 := p18 Z hZ d
  let _a3 := SequenceOfBlowupsPullback.prepend_schemeAt_zero (comap Z ph_) hZ' d'
  let _a4 := SequenceOfBlowupsPullback.prepend_schemeAt_zero Z hZ d
  obtain ⟨hlen, σ, h0, hpb, hcen⟩ := h
  refine ⟨?_, prependMapOfLevelwise ph_ Z hZ hZ' σ, ?_, ?_, ?_⟩
  rw [_a1,
    SequenceOfBlowupsPullback.prepend_length Z hZ d, hlen]
  exact eqToHom_conj_comp_eq_comp_of_heq_id
    _a3
    _a4 ph_
    (_a2.toSequenceOfBlowups.isoZero.hom)
    (_a0.toSequenceOfBlowups.isoZero.hom)
    (heq_of_eq (prepend_isoObjZero_hom Z hZ d))
    (heq_of_eq (prepend_isoObjZero_hom (comap Z ph_) hZ' d'))
  intro i hi
  cases i with
  | zero =>
      refine isPullback_congr (strictPrependComparisonMap_succ ph_ Z hZ hZ' σ 0 hi (zero_le _))
        (prepend_blowupMorphism_zero (comap Z ph_) hZ' d') (prepend_blowupMorphism_zero Z hZ d)
        ?_ ((of_horiz_isIso ⟨sy_ h0⟩).flip)
      show 𝟙 X' ≫ ph_ ≫ 𝟙 X = ph_
      simp
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by omega
      exact isPullback_congr (strictPrependComparisonMap_succ ph_ Z hZ hZ' σ (n + 1) hi hn)
        (SequenceOfBlowupsPullback.prepend_blowupMorphism_succ (comap Z ph_) hZ' d' n)
        (SequenceOfBlowupsPullback.prepend_blowupMorphism_succ Z hZ d n)
        (strictPrependComparisonMap_succ ph_ Z hZ hZ' σ n hi.le hn.le) (hpb n hn)
  intro i hi
  cases i with
  | zero =>
      exact SequenceOfBlowupsPullback.comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq
        _a3
        _a4.symm ph_ Z (comap Z ph_) rfl
        (_a0.toSequenceOfBlowups.center 0)
        (_a2.toSequenceOfBlowups.center 0)
        (heq_of_eq (prepend_center_zero Z hZ d))
        (heq_of_eq (prepend_center_zero (comap Z ph_) hZ' d'))
  | succ n =>
      have hn : n < d'.toSequenceOfBlowups.length := by omega
      exact SequenceOfBlowupsPullback.comap_eq_comap_eqToHom_comp_comp_eqToHom_of_heq
        (SequenceOfBlowupsPullback.prepend_schemeAt_succ (comap Z ph_) hZ' d' n)
        (SequenceOfBlowupsPullback.prepend_schemeAt_succ Z hZ d n).symm (σ n hn.le)
        (d.toSequenceOfBlowups.center n) (d'.toSequenceOfBlowups.center n) (hcen n hn)
        (_a0.toSequenceOfBlowups.center (n + 1))
        (_a2.toSequenceOfBlowups.center (n + 1))
        (heq_of_eq (SequenceOfBlowupsPullback.prepend_center_succ Z hZ d n))
        (heq_of_eq (SequenceOfBlowupsPullback.prepend_center_succ (comap Z ph_) hZ' d' n))
end

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

section
variable {X : Sch}
theorem le_of_ideal_le {I J : ISD X}
    (h : ∀ V : X.affineOpens, I.ideal V ≤ J.ideal V) : I ≤ J := h

theorem le_vanishingIdeal_of_subset (I : ISD X)
    (Z : Closeds ↥X) (h : (Z : Set ↥X) ⊆ (support I : Set ↥X)) :
    I ≤ vanishingIdeal Z := by
  exact mp_ (gc I Z) h

theorem isIso_pullback_snd_of_le (H J : ISD X)
    (h : H ≤ J) : IsIso $ Limits.pullback.snd H.si J.si := by
  have hker : ker H.si ≤ ker J.si := by simp_all
  have hcond : lift H.si J.si hker
      ≫ siI H = 𝟙 J.subscheme ≫ siI J := by simp_all
  refine ⟨m107 _ _ hcond, ?_, lift_snd _ _ hcond⟩
  apply hom_ext
  rw [assoc, lift_fst, id_comp]
  have hmono : Mono H.si := inferInstance
  apply hmono.right_cancellation
  rw [assoc, lift_fac _ _ hker, condition]
  rw [assoc, lift_snd, comp_id, id_comp]

theorem support_vanishingIdeal_eq_self (Z : Closeds ↥X) :
    support (vanishingIdeal Z) = Z := rfl

theorem radical_vanishingIdeal_eq_self (Z : Closeds ↥X) :
    (vanishingIdeal Z).radical
      = vanishingIdeal Z := by
  rw [← vanishingIdeal_support]
  exact Scheme.IdealSheafData.gc.u_l_u_eq_u Z
end

section
variable {A B : CRC} (e : A ≅ B)
theorem injective_hom_of_iso :
    Function.Injective e.hom.hom :=
  e.commRingCatIsoToRingEquiv.injective

theorem ker_hom_of_iso_le (I : Ideal A) :
    RingHom.ker e.hom.hom ≤ I := by
  intro x hx
  have hx0 : e.hom.hom x = e.hom.hom 0 := by simp_all
  simp [injective_hom_of_iso e hx0]

theorem surjective_hom_of_iso :
    Surjective e.hom.hom :=
  e.commRingCatIsoToRingEquiv.surjective
end

section
variable {X Y : Sch} (f : X ⟶ Y)
theorem radical_comap_eq_of_isOpenImmersion
    [IsOpenImmersion f] (I : ISD Y) (hI : I.radical = I) :
    (comap I f).radical = comap I f := by
  refine le_antisymm (le_of_ideal_le ?_) $ le_radical _
  intro V
  let _s0 := imU f V
  have hV := V.2.image_of_isOpenImmersion f
  have e : V ≤ preU f _s0 := fun x hx => ⟨x, hx, rfl⟩
  have hmap := comap_ideal_eq_map_appLE I f
    ⟨imU f V, hV⟩ V e
  let _a0 := appLE f _s0 V e
  have hiso : _a0
      = isoH (f.appIso V) := sy_ $ appIso_hom' f V
  have hsurj : Surjective
      _a0.hom := by
    rw [hiso]
    exact surjective_hom_of_iso _
  have hker : m41 _a0.hom
      ≤ I.ideal ⟨imU f V, hV⟩ := by
    rw [hiso]
    exact ker_hom_of_iso_le _ _
  refine le_of_eq $ tr_ (radical_ideal (cmI I f) V) ?_
  rw [hmap, ← map_radical_of_surjective hsurj hker, ← radical_ideal, hI]

theorem comap_vanishingIdeal_of_isOpenImmersion
    [IsOpenImmersion f] (T : Closeds ↥Y) (S : Closeds ↥X)
    (hS : (S : Set ↥X) = f.base ⁻¹' (T : Set ↥Y)) :
    comap (vanishingIdeal T) f =
      vanishingIdeal S := by
  have hrad := radical_comap_eq_of_isOpenImmersion f
    (vanishingIdeal T) $ radical_vanishingIdeal_eq_self T
  let _a0 := cmI (vanishingIdeal T) f
  have hsupp : spI _a0 = S := by
    apply SetLike.coe_injective
    rw [support_comap]
    show f ⁻¹' (support (vanishingIdeal T) : Set Y) = S
    rw [support_vanishingIdeal_eq_self, hS]
  calc _a0
      = _a0.radical := sy_ hrad
    _ = vanishingIdeal
          (spI _a0) :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = vanishingIdeal S := by rw [hsupp]

theorem exists_isIso_pullback_lift_comap_subschemeio (I : ISD Y) :
    ∃ al_ : subscheme (comap I f) ⟶ Limits.pullback f I.si,
      IsIso al_ ∧ al_ ≫ Limits.pullback.fst f I.si = subschemeι (comap I f) :=
  ⟨isoH $ I.comapIso f, inferInstance, comapIso_hom_fst I f⟩
end

section
variable {W : Sch} (U : Opn W)
theorem support_comap_opens_vanishingIdeal (T : Closeds ↥W) :
    ((support $ comap (vanishingIdeal T) U.i) : Set ↥(toScheme U))
      = U.ib ⁻¹' (T : Set ↥W) :=by simp_all
theorem comap_opens_vanishingIdeal_eq_vanishingIdeal_support
    (T : Closeds ↥W) :
    comap (vanishingIdeal T) U.i
      = vanishingIdeal
          (support $ comap (vanishingIdeal T) U.i) := by
  rw [vanishingIdeal_support]
  exact sy_ $ radical_comap_eq_of_isOpenImmersion U.i _ $ radical_vanishingIdeal_eq_self T

end

section
variable {X Y S : Sch} (f : X ⟶ Y)
theorem smooth_comap_subschemeio_comp_of_smooth_pullback_snd
    (I : ISD Y) (g : Y ⟶ S)
    (hsm : Smooth $ subschemeι I ≫ g)
    (hsnd : Smooth $ Limits.pullback.snd f I.si) :
    Smooth $ subschemeι (comap I f) ≫ f ≫ g := by
  obtain ⟨al_, hal_, halfac⟩ := exists_isIso_pullback_lift_comap_subschemeio f I
  have key : siI (cmI I f) ≫ f ≫ g
      = al_ ≫ (m47 f I.si ≫ siI I ≫ g) := by
    calc (cmI I f).si ≫ f ≫ g
        = (al_ ≫ m57 f I.si) ≫ f ≫ g := by rw [halfac]
      _ = al_ ≫ ((m57 f I.si ≫ f) ≫ g) := by simp
      _ = al_ ≫ ((m47 f I.si ≫ siI I) ≫ g) := by
            rw [condition]
      _ = al_ ≫ (m47 f I.si ≫ siI I ≫ g) := by simp
  rw [key]
  infer_instance

theorem smooth_comap_subschemeio_of_isOpenImmersion
    [IsOpenImmersion f] (I : ISD Y) (g : Y ⟶ S)
    (hsm : Smooth $ subschemeι I ≫ g) :
    Smooth $ subschemeι (comap I f) ≫ f ≫ g := by
  have : Smooth $ m47 f I.si := inferInstance
  exact smooth_comap_subschemeio_comp_of_smooth_pullback_snd f I g hsm inferInstance
end

theorem isReduced_of_isLocalization {R S : Type} [CommRing R] [CommRing S]
    (alg : Algebra R S) (M : Submonoid R) (hloc : @IsLocalization R _ M S _ alg)
    (hred : _root_.IsReduced R) : _root_.IsReduced S :=
  @isReduced_localizationPreserves R _ M S _ alg hloc hred

theorem isReduced_subscheme_of_radical_eq {X : Sch} (J : ISD X)
    (hJ : ∀ U : X.affineOpens, (J.ideal U).radical = J.ideal U) :
    IsReduced J.subscheme := by
  let _a0 := subS J
  have hst : ∀ y, _root_.IsReduced $ stkX _a0 y := by
    intro y
    obtain ⟨U, hyU, hU⟩ :=
      exists_isAffineOpen_mem $ J.subschemeι.base y
    have hV := hU.preimage J.si
    have hy := hyU
    have hsec : _root_.IsReduced Γ(subS J, siPre J U) := by
      refine ⟨fun z hz => ?_⟩
      obtain ⟨n, hn⟩ := hz
      apply injective_hom_of_iso $ J.subschemeObjIso ⟨U, hU⟩
      rw [map_zero]
      refine (mp (isRadical_iff_quotient_reduced _) $ mp_ radical_eq_iff $ hJ ⟨U, hU⟩).eq_zero _ ⟨n, ?_⟩
      rw [← map_pow, hn, map_zero]
    show _root_.IsReduced
      (stkX _a0 ((⟨y, hy⟩ : (siPre J U)) : _a0))
    exact isReduced_of_isLocalization _ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (hV.isLocalization_stalk ⟨y, hy⟩) hsec
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

theorem radical_ker_eq_of_isReduced {A B : Sch} (g : A ⟶ B)
    [AlgebraicGeometry.IsAffineHom g] [IsReduced A] :
    (ker g).radical = ker g := by
  refine le_antisymm (le_of_ideal_le ?_) $ le_radical _
  intro V
  have key : ∀ y, y ∈ (m149 g).ideal V ↔
      (app g V).hom y = 0 := by simp_all
  rw [radical_ideal]
  intro y hy
  obtain ⟨n, hn⟩ := hy
  refine (key y).2 ?_
  have : _root_.IsReduced Γ(A, preU g V) := inferInstance
  refine IsNilpotent.eq_zero ⟨n, ?_⟩
  rw [← map_pow]
  exact (key _).1 hn

theorem comap_vanishingIdeal_subschemeio {X : Sch} (H : ISD X)
    (Z : Closeds ↥X) (hZH : (Z : Set ↥X) ⊆ (support H : Set ↥X))
    (S : Closeds ↥(subscheme H))
    (hS : (S : CSet $ subscheme H) = H.subschemeι.base ⁻¹' (Z : Set ↥X)) :
    comap (vanishingIdeal Z) H.si =
      vanishingIdeal S := by
  have hred : IsReduced (vanishingIdeal Z).subscheme := by
    refine isReduced_subscheme_of_radical_eq _ fun U => ?_
    rw [vanishingIdeal_ideal]
    exact (isRadical_vanishingIdeal _).radical
  let _m0 := m47 H.si (vanishingIdeal Z).si
  have :=
    isIso_pullback_snd_of_le H _ $ le_vanishingIdeal_of_subset H Z hZH
  have : IsOpenImmersion _m0 := inferInstance
  have :=
    AlgebraicGeometry.isReduced_of_isOpenImmersion _m0
  let _a0 := cmI (vanishingIdeal Z) H.si
  have hsupp : spI _a0 = S := by
    apply SetLike.coe_injective
    rw [support_comap]
    show subschemeι H ⁻¹'
      (support (vanishingIdeal Z) : Set X) = (S : CSet $ subS H)
    rw [support_vanishingIdeal_eq_self, hS]
  calc _a0
      = _a0.radical := sy_ $ radical_ker_eq_of_isReduced $ m57 H.si (vanishingIdeal Z).si
    _ = vanishingIdeal
          (spI _a0) :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = vanishingIdeal S := by rw [hsupp]

theorem comap_subschemeio_comap_vanishingIdeal {W : Sch} (U : Opn W)
    (H : IdealSheafData $ toScheme U)
    (T : Closeds ↥W) (S : Closeds ↥(subscheme H))
    (hS : (S : CSet $ subscheme H) = (subschemeι H ≫ ι U).base ⁻¹' (T : Set ↥W))
    (hTsubH : (U.ib ⁻¹' (T : Set ↥W)) ⊆ (support H : Set ↥(toScheme U))) :
    comap (comap (vanishingIdeal T) U.i) H.si =
      vanishingIdeal S := by
  rw [comap_opens_vanishingIdeal_eq_vanishingIdeal_support U T]
  refine comap_vanishingIdeal_subschemeio H _ ?_ S ?_
  rwa [support_comap_opens_vanishingIdeal]
  rw [hS, support_comap_opens_vanishingIdeal, ← Set.preimage_comp]
  rfl

theorem agreeNearVanishingComapSubscheme : AgreeNearVanishingComapSubscheme := by
  intro W N U H T S x hS hTsubH hN
  simp [vanishingIdealAssignment_apply] at hN ⊢
  obtain ⟨V, hxV, hVeq⟩ := (agreeNear_iff _ _ _).1 hN
  let _s0 := (subschemeι H ≫ ι U).pre V
  have hrange : range (ι _s0 ≫ subschemeι H ≫ ι U)
      ⊆ range V.i := by
    rw [q1]
    rintro z ⟨y, rfl⟩
    have hy : ι _s0 y
        ∈ (((subschemeι H ≫ ι U).pre V : (subscheme H).Opens) : CSet $ subscheme H) := by
      rw [← q1 _s0]
      exact ⟨y, rfl⟩
    exact hy
  obtain ⟨g, hg⟩ : ∃ g,
      g ≫ ι V = ι _s0 ≫ subschemeι H ≫ ι U :=
    ⟨m43 V.i _ hrange,
      m115 _ _ hrange⟩
  refine (agreeNear_iff _ _ _).2 ⟨(subschemeι H ≫ ι U).pre V, hxV, ?_⟩
  have e : ∀ I : ISD W,
      (comap (comap I U.i) H.si).comap _s0.i
        = comap (comap I V.i) g := by
    intro I
    rw [← comap_comp, ← comap_comp, assoc,
      ← hg, ← comap_comp]
  rw [e N, hVeq, ← e, comap_subschemeio_comap_vanishingIdeal U H T S hS hTsubH]

theorem exists_irreducibleComponent_mem (al_ : Type) [TopologicalSpace al_] (x : al_) :
    ∃ C ∈ irreducibleComponents al_, x ∈ C :=
  ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
    mem_irreducibleComponent⟩

theorem smooth_subschemeio_comp_of_eq {X S : Sch} (f : X ⟶ S) {K K' : ISD X}
    (h : K = K') (hsm : Smooth $ subschemeι K' ≫ f) :
    Smooth $ subschemeι K ≫ f := by
  subst h
  exact hsm

section
variable {k : Type} [Field k]
theorem orderAt_vanishingIdeal_eq_one [CharZero k] {W : Sch}
    (p : W ⟶ Sp k) (hp : Smooth p) (T : Closeds ↥W)
    (_hirr : IsIrreducible (T : Set ↥W))
    (hsm : Smooth $ subschemeι (vanishingIdeal T) ≫ p)
    (hcomp : ∀ C ∈ irreducibleComponents ↥W, ¬ C ⊆ (T : Set ↥W))
    (x : ↥W) (hx : x ∈ (T : Set ↥W)) :
    orderAt (vanishingIdeal T) x = 1 := by
  have hZs :=
    support_vanishingIdeal_eq_self T
  have hxZ : x ∈ spI (vanishingIdeal T) := by simp_all
  obtain ⟨U, m, c, S, hxU, hU, hD⟩ :=
    exists_chart_restrictIdeal_eq_coordIdeal p
      (vanishingIdeal T) x hxZ
  rcases S.eq_empty_or_nonempty with hSe | ⟨j, hj⟩
  exfalso
  have key : ∀ y : (oSch U),
      orderAt (vanishingIdeal T) (opIb U y) = ⊤ := by
    intro y
    have h1 : restrictIdeal (vanishingIdeal T) U
        = c.coordIdeal (∅) := by rw [hD, hSe]
    have h2 : comap (vanishingIdeal T) U.i
        = comap (⊥ : ISD $ affineSpaceFin k m) c.map := by
      rw [← restrictIdeal_eq_comap_io, h1, p33,
        coordSubspaceIdeal_empty]
    have h3 : stalkIdeal (comap (vanishingIdeal T) U.i) y
        = stalkIdeal (⊥ : ISD $ toScheme U) y := by
      rw [h2, stalkIdeal_comap, stalkIdeal_bot, Ideal.map_bot,
        stalkIdeal_bot]
    refine st_ (orderAt_comap_of_isOpenImmersion U.i
      (vanishingIdeal T) y) ?_
    rw [orderAt_eq_of_stalkIdeal_eq h3, orderAt_bot]
  have hUsubT : (U : Set W) ⊆ (T : Set W) := by
    intro z hz
    have hrange : range U.ib = (U : Set W) := by simp
    obtain ⟨y, rfl⟩ : z ∈ range U.ib := by rw [hrange]
                                           exact hz
    have h6 : 1 ≤ orderAt (vanishingIdeal T)
        (opIb U y) := by
      rw [key y]
      exact le_top
    have h7 := (one_le_orderAt_iff_mem_support _ _).1 h6
    rwa [hZs] at h7
  obtain ⟨C, hC, hxC⟩ := exists_irreducibleComponent_mem (W) x
  refine hcomp C hC ?_
  intro z hzC
  by_contra hzT
  obtain ⟨w, hwC, hwU, hwT⟩ := hC.1.2 U (Tᶜ) U.isOpen
    T.2.isOpen_compl ⟨x, hxC, hxU⟩ ⟨z, hzC, hzT⟩
  exact hwT $ hUsubT hwU
  exact orderAt_eq_one_of_restrictIdeal_eq_coordIdeal p hU c S j hj
    (vanishingIdeal T) hD x hxU hxZ
end

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

end
section


namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

theorem vanishingComapOpens : VanishingComapOpens := by
  intro W T U T' hT'
  simp [vanishingIdealAssignment_apply]
  exact comap_vanishingIdeal_of_isOpenImmersion U.i T T' hT'

theorem idealSheafGeometryHypotheses_vanishingIdealAssignment : IdealSheafGeometryHypotheses (vanishingIdealAssignment) :=
  idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor vanishingOrderOneOnSmoothDivisor agreeNearVanishingComapSubscheme vanishingComapOpens

theorem smoothVanishingHypotheses_vanishingIdealAssignment : SmoothVanishingHypotheses (vanishingIdealAssignment) where
  orderAt_vanishing_eq_one := by
    intro k _ _ W p hp T hirr hsm hcomp x hx
    rw [vanishingIdealAssignment_apply] at hsm ⊢
    exact orderAt_vanishingIdeal_eq_one p hp T hirr hsm hcomp x hx
  smooth_opens_io_comp := by
    intro k _ _ W p U hp
    infer_instance
  smooth_vanishing_hypersurface := by
    intro k _ _ W p U H hH T S hS hTsubH hT
    rw [vanishingIdealAssignment_apply] at hT ⊢
    refine smooth_subschemeio_comp_of_eq (siI H ≫ opI U ≫ p) (comap_subschemeio_comap_vanishingIdeal U H T S hS hTsubH).symm ?_
    have _i22 : H ≤ comap (vanishingIdeal T) U.i := by
      rw [comap_opens_vanishingIdeal_eq_vanishingIdeal_support U T]
      refine le_vanishingIdeal_of_subset H _ ?_
      rwa [support_comap_opens_vanishingIdeal]
    have :=
      isIso_pullback_snd_of_le H _ _i22
    exact smooth_comap_subschemeio_comp_of_smooth_pullback_snd H.si
      (cmI (vanishingIdeal T) U.i) (opI U ≫ p) (smooth_comap_subschemeio_of_isOpenImmersion U.i (vanishingIdeal T) p hT) inferInstance
  smooth_vanishing_opens := by
    intro k _ _ W p U T S hS hT
    rw [vanishingIdealAssignment_apply] at hT ⊢
    exact smooth_subschemeio_comp_of_eq (opI U ≫ p)
      (comap_vanishingIdeal_of_isOpenImmersion U.i T S hS).symm
      (smooth_comap_subschemeio_of_isOpenImmersion U.i
        (vanishingIdeal T) p hT)

theorem smoothOrderOneCentersIsolated_vanishingIdealAssignment_of_principalizationCertificate {k : Type} [Field k] [CharZero k]
    {W : Sch} {p : W ⟶ Sp k} {I : ISD W} {m : ℕ}
    {Mem : Set ↥W} {Z : ISD W} (h : PrincipalizationCertificate W p I m Mem Z) :
    SmoothOrderOneCentersIsolated (vanishingIdealAssignment) W p I m Mem Z :=
  smoothOrderOneCentersIsolated_of_principalizationCertificate idealSheafGeometryHypotheses_vanishingIdealAssignment smoothVanishingHypotheses_vanishingIdealAssignment h

end OpenImmersionRestriction

theorem openImmersionStability (k : Type) [Field k] : OpenImmersionStability k := by
  refine ⟨?_, ?_, ?_⟩
  intro V W f hf J hJ
  exact NonzeroOnComponents.comap_of_isOpenImmersion hJ f
  intro V W f hf D
  exact OpenImmersionRestriction.isOpenImmersion_subschemeMap f D (comapSubscheme f D) $ comapSubscheme_comp f D
  intro V W f hf p D hD
  exact OpenImmersionRestriction.isSmoothDivisor_comap f p D hD

theorem PrincipalizationCertificate.comap_of_isOpenImmersion {k : Type} [Field k] {W : Sch}
    {p : W ⟶ Sp k} {I : ISD W} {m : ℕ} {Mem : Set ↥W}
    {Z : ISD W} (h : PrincipalizationCertificate W p I m Mem Z) {V : Sch} (f : V ⟶ W)
    [IsOpenImmersion f] :
    PrincipalizationCertificate V (f ≫ p) (comap I f) m (f.base ⁻¹' Mem) $ comap Z f :=
  h.comap_of_openImmersionStability (openImmersionStability k) f




section
variable {k : Type} [Field k]
section
variable {A : Type} [CommRing A] [hv2_2 : Algebra k A] {n} (f : MvPolynomial (Fin n) k →ₐ[k] A)
include hv2_2
noncomputable def extendAlgHomLastVarZero :
    MvPolynomial (UFin $ n + 1) k →ₐ[k] A :=
  aeval fun i : UFin (n + 1) =>
    lastCases (motive := fun _ => A) 0 (fun j => f $ MvPolynomial.X j) i.down

theorem extension_surjective (hf : Surjective f) :
    Surjective $ extendAlgHomLastVarZero f := by
  intro a
  obtain ⟨q, rfl⟩ := hf a
  let _a0 := UFin $ n + 1
  refine ⟨rename
    (fun j : Fin n => up j.castSucc) q, ?_⟩
  show m165 (fun i : _a0 =>
      lastCases (motive := fun _ => A) 0 (fun j => f $ m7 j) i.down)
      (rename (fun j : Fin n => up j.castSucc) q)
      = f q
  rw [aeval_rename]
  have h : ((fun i : _a0 =>
      lastCases (motive := fun _ => A) 0 (fun j => f $ m7 j) i.down) ∘
      fun j : Fin n => up j.castSucc)
      = fun j => f $ m7 j := by
    funext j
    simp
  rw [h]
  exact m156 (aeval_unique f).symm q

theorem extension_X_last_eq_zero :
    extendAlgHomLastVarZero f (MvPolynomial.X $ up $ last n) = 0 := by
  simp [extendAlgHomLastVarZero]
end

section
variable (Y : Sch) [IsAffine Y] {m : Type} [Algebra k ↥Γ(Y, ⊤)]
section
variable (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤))
noncomputable def toAffineSpaceOfAlgHom :
    Y ⟶ affineSpaceIndexedBy k m :=
  Y.isoSpec.hom ≫ Spec.map (ofHom g.toRingHom) ≫
    inv (AffineSpace.SpecIso m $ CommRingCat.of k)

theorem support_ker_ne_univ_of_map_X_eq_zero
    (x0_ : m) (hx0_ : g (MvPolynomial.X x0_) = 0) [QuasiCompact $ toAffineSpaceOfAlgHom Y g] :
    ((toAffineSpaceOfAlgHom Y g).ker.support : Set ↥(affineSpaceIndexedBy k m)) ≠ univ := by
  intro hcon
  let _a0 := m69 m $ m10 k
  let _a2 := m12 $ ofHom g.toRingHom
  let _a7 := toAffineSpaceOfAlgHom Y g
  have hcomp : _a7 ≫ isoH _a0
      = Y.isoSpec.hom ≫ _a2 := by
    show (Y.isoSpec.hom ≫ _a2 ≫
      inv _a0) ≫
      hom _a0 = _
    rw [assoc, assoc, inv_hom_id, comp_id]
  have hmem0 : ∀ w : PrimeSpectrum Γ(Y, ⊤),
      (m7 x0_) ∈
        asIdeal (bsM _a2 w) := by
    intro w
    show g (m7 x0_) ∈ asIdeal w
    rw [hx0_]
    exact m216 _
  let _a3 := _a7
  let _a8 := MvPolynomial m k
  obtain ⟨v, hv, hvcont, hvsurj⟩ :
      ∃ v : (affineSpaceIndexedBy k m) → PrimeSpectrum _a8,
        (∀ y, v (bsM _a3 y)
            = bsM _a2 (Y.isoSpec.hom.base y)) ∧
          Continuous v ∧ Surjective v := by
    refine ⟨fun x => (homeoOfIso _a0) x, ?_, (homeoOfIso _a0).continuous, (homeoOfIso _a0).surjective⟩
    intro y
    exact congrArg
      (fun ph_ : Y ⟶ Spec (m10 _a8) => bsM ph_ y) hcomp
  have hrange : ∀ y,
      (m7 x0_) ∈ asIdeal (v $ bsM _a3 y) := by
    intro y
    rw [hv y]
    exact hmem0 _
  have hsub : (m30 _a7.base) ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(m7 x0_)} := by
    rintro _ ⟨y, rfl⟩
    have : v (bsM _a3 y) ∈
        PrimeSpectrum.zeroLocus {(m7 x0_)} := by
      rw [PrimeSpectrum.mem_zeroLocus, singleton_subset_iff]
      exact hrange y
    exact this
  have huniv : univ ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(m7 x0_)} := by
    rw [← hcon, Scheme.Hom.support_ker _]
    exact closure_minimal hsub $ (isClosed_zeroLocus _).preimage hvcont
  obtain ⟨xi_, hxi_⟩ := hvsurj ⟨⊥, isPrime_bot⟩
  have hmem :=
    huniv $ mem_univ xi_
  rw [m163, hxi_, mem_zeroLocus, singleton_subset_iff] at hmem
  have h6 := mp_ mem_bot hmem
  have h7 : 1 = 0 := by simp_all
  exact one_ne_zero h7
end

theorem isClosedImmersion_embedding_and_comp_eq (p : Y ⟶ Sp k)
    (halg : algebraMap k ↥Γ(Y, ⊤)
      = (((GSpecIso $ CommRingCat.of k).inv ≫ p.appTop).hom))
    (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤)) (hg : Surjective g) :
    IsClosedImmersion (toAffineSpaceOfAlgHom Y g) ∧
      toAffineSpaceOfAlgHom Y g ≫ (affineSpaceIndexedBy k m ↘ Sp k) = p := by
  let _a1 := m12 $ ofHom g.toRingHom
  let _a0 := Y.isoSpec.hom ≫ _a1 ≫ isoI (m69 m $ m10 k)
  have : IsClosedImmersion _a1 :=
    IsClosedImmersion.spec_of_surjective _ hg
  constructor
  show IsClosedImmersion _a0
  infer_instance
  show _a0 ≫
    (affineSpaceIndexedBy k m ↘ Sp k) = p
  rw [assoc, assoc, AffineSpace.SpecIso_inv_over, ← m183]
  have h2 : ofHom m8 ≫
      ofHom g.toRingHom
      = isoI (GSpecIso $ m10 k) ≫ hAT p := by
    refine CommRingCat.hom_ext $ RingHom.ext fun a => ?_
    show g (MvPolynomial.C a) = _
    rw [← algebraMap_eq, AlgHom.commutes, halg]
  rw [h2]
  have h2 : Y.isoSpec.hom = Y.toSpecΓ := rfl
  rw [h2, m183, ← assoc, ← Scheme.toSpecΓ_naturality p,
    ← SpecMap_ΓSpecIso_hom, assoc, ← m183, inv_hom_id, Spec.map_id,
    comp_id]
end
end

theorem affineEmbedsIntoAffineSpace : AffineEmbedsIntoAffineSpace := by
  intro k _ Y _ p _
  let _s1 := GSpecIso $ m10 k
  have hiso : Surjective $ _s1.inv := by
    intro x
    exact ⟨_s1.hom x, by simp⟩
  have hph : RingHom.FiniteType
      ((_s1.inv ≫ hAT p).hom) := by
    rw [m225]
    exact ((HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := p)).mp inferInstance).comp $ RingHom.FiniteType.of_surjective _ hiso
  let _ :=
    ((_s1.inv ≫ hAT p).hom).toAlgebra
  have halg : algebraMap k Γ(Y, ⊤)
      = ((_s1.inv ≫ hAT p).hom) := rfl
  have hfta := hph
  obtain ⟨n, f, hfsurj⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hfta
  obtain ⟨hci, hover⟩ := isClosedImmersion_embedding_and_comp_eq Y p halg (extendAlgHomLastVarZero f) $ extension_surjective f hfsurj
  let _a1 := toAffineSpaceOfAlgHom Y $ extendAlgHomLastVarZero f
  refine ⟨n + 1, _a1, hci, ?_, hover⟩
  have hne := support_ker_ne_univ_of_map_X_eq_zero Y (extendAlgHomLastVarZero f) (up $ last n) $ extension_X_last_eq_zero f
  let _s0 := UFin $ n + 1
  have hirr : IsIrreducible (univ : Set $ affineSpaceIndexedBy k _s0) := by
    let _a1 := MvPolynomial _s0 k
    have h0 : IsIrreducible (univ : Set $ Spec $ m10 _a1) :=
      IrreducibleSpace.isIrreducible_univ $ PrimeSpectrum _a1
    let _a0 := homeoOfIso (m69 _s0 $ m10 k).symm
    have h1 := h0.image _a0
      _a0.continuous.continuousOn
    rwa [image_univ,
      _a0.surjective.range_eq] at h1
  intro T hT hsubT
  refine hne $ eq_univ_of_univ_subset ?_
  rwa [← (eq_univ_of_univ_subset $ an2 hT hirr $ subset_univ T)]


private theorem comp_appTop_apply {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    appTop (f ≫ g) x = appTop f (appTop g x) := by
  simp
  rfl

section
variable {X Y : Sch} (f : X ⟶ Y) (a b : Γ(Y, ⊤))
theorem appTop_add :
    appTop f (a + b) = appTop f a + appTop f b :=
  map_add (m4 f.appTop) a b

theorem appTop_sub :
    appTop f (a - b) = appTop f a - appTop f b :=
  map_sub (m4 f.appTop) a b
end

theorem appTop_id_apply {X : Sch} (x : Γ(X, ⊤)) :
    appTop (𝟙 X : X ⟶ X) x = x := by
  simp

theorem exists_iso_affineSpace_sum_comp_eq_of_coord {S : Sch} (n m : ℕ)
    {Y : Sch}
    (p : Y ⟶ S)
    (e1_ : Y ⟶ AffineSpace (UFin n) S)
    (e2_ : Y ⟶ AffineSpace (UFin m) S)
    (h1_ : e1_ ≫ (AffineSpace (UFin n) S ↘ S) = p)
    (h2_ : e2_ ≫ (AffineSpace (UFin m) S ↘ S) = p)
    (F : Fin m → Γ(AffineSpace (UFin n) S, ⊤))
    (hF : ∀ b : Fin m, appTop e1_ (F b)
      = appTop e2_ (AffineSpace.coord S (up b : UFin m)))
    (G : Fin n → Γ(AffineSpace (UFin m) S, ⊤))
    (hG : ∀ a : Fin n, appTop e2_ (G a)
      = appTop e1_ (AffineSpace.coord S (up a : UFin n)))
    (L R : Y ⟶ AffineSpace (UFS n m) S)
    (hLover : L ≫ (AffineSpace (UFS n m) S ↘ S) = p)
    (hRover : R ≫ (AffineSpace (UFS n m) S ↘ S) = p)
    (hLinl : ∀ a : Fin n, appTop L (AffineSpace.coord S
        (up (inl a) : UFS n m))
      = appTop e1_ (AffineSpace.coord S (up a : UFin n)))
    (hLinr : ∀ b : Fin m, appTop L (AffineSpace.coord S
        (up (inr b) : UFS n m)) = 0)
    (hRinl : ∀ a : Fin n, appTop R (AffineSpace.coord S
        (up (inl a) : UFS n m)) = 0)
    (hRinr : ∀ b : Fin m, appTop R (AffineSpace.coord S
        (up (inr b) : UFS n m))
      = appTop e2_ (AffineSpace.coord S (up b : UFin m))) :
    ∃ Ph_ : AffineSpace (UFS n m) S ≅ AffineSpace (UFS n m) S,
      hom Ph_ ≫ (AffineSpace (UFS n m) S ↘ S)
          = (AffineSpace (UFS n m) S ↘ S) ∧ L ≫ hom Ph_ = R := by
  let _a0 := UFS n m
  let _a1 := AffineSpace _a0 S ↘ S
  obtain ⟨pr1, hpr1, hpr1c⟩ :
      ∃ q : AffineSpace _a0 S ⟶ AffineSpace (UFin n) S,
        q ≫ AffineSpace (UFin n) S ↘ S
            = _a1 ∧
          ∀ a : Fin n, hAT q (m9 S $ up a)
            = m9 S (up (inl a) : _a0) :=
    ⟨m52 (AffineSpace _a0 S ↘ S)
        (fun a : UFin n =>
          m9 S (up (inl a.down) : _a0)),
      m179 _ _, fun a => m87 _ _ _⟩
  obtain ⟨pr2, hpr2_, hpr2c⟩ :
      ∃ q : AffineSpace _a0 S ⟶ AffineSpace (UFin m) S,
        q ≫ AffineSpace (UFin m) S ↘ S
            = _a1 ∧
          ∀ b : Fin m, hAT q (m9 S $ up b)
            = m9 S (up (inr b) : _a0) :=
    ⟨m52 (AffineSpace _a0 S ↘ S)
        (fun b : UFin m =>
          m9 S (up (inr b.down) : _a0)),
      m179 _ _, fun b => m87 _ _ _⟩
  have mkHom : ∀ v : _a0 → Γ(AffineSpace _a0 S, ⊤),
      ∃ w : AffineSpace _a0 S
            ⟶ AffineSpace _a0 S,
        w ≫ _a1
            = _a1 ∧
          ∀ i, hAT w (m9 S i) = v i :=
    fun v => ⟨m52 (AffineSpace _a0 S ↘ S) v,
      m179 _ _, fun i => m87 _ _ _⟩
  obtain ⟨σ, hsg_, hsgc⟩ := mkHom fun i : _a0 => elim
    (fun a => m9 S (up (inl a) : _a0))
    (fun b =>
      m9 S (up (inr b) : _a0)
        + hAT pr1 (F b)) i.down
  obtain ⟨σ', hsg_', hsg'c⟩ := mkHom fun i : _a0 => elim
    (fun a => m9 S (up (inl a) : _a0))
    (fun b =>
      m9 S (up (inr b) : _a0)
        - hAT pr1 (F b)) i.down
  obtain ⟨ta_, hta, htac⟩ := mkHom fun i : _a0 => elim
    (fun a =>
      m9 S (up (inl a) : _a0)
        - hAT pr2 (G a))
    (fun b =>
      m9 S (up (inr b) : _a0)) i.down
  obtain ⟨ta', hta', hta'c⟩ := mkHom fun i : _a0 => elim
    (fun a =>
      m9 S (up (inl a) : _a0)
        + hAT pr2 (G a))
    (fun b =>
      m9 S (up (inr b) : _a0)) i.down
  have hsginl : ∀ a,
      appTop σ (m9 S (up (inl a) : _a0))
        = m9 S (up (inl a) : _a0) :=
    fun a => hsgc _
  have hsginr : ∀ b,
      appTop σ (m9 S (up (inr b) : _a0))
        = m9 S (up (inr b) : _a0)
            + hAT pr1 (F b) := fun b => hsgc _
  have hsg'inl : ∀ a,
      appTop σ' (m9 S (up (inl a) : _a0))
        = m9 S (up (inl a) : _a0) :=
    fun a => hsg'c _
  have hsg'inr : ∀ b,
      appTop σ' (m9 S (up (inr b) : _a0))
        = m9 S (up (inr b) : _a0)
            - hAT pr1 (F b) := fun b => hsg'c _
  have htainl : ∀ a,
      appTop ta_ (m9 S (up (inl a) : _a0))
        = m9 S (up (inl a) : _a0)
            - hAT pr2 (G a) := fun a => htac _
  have htainr : ∀ b,
      appTop ta_ (m9 S (up (inr b) : _a0))
        = m9 S (up (inr b) : _a0) :=
    fun b => htac _
  have hta'inl : ∀ a,
      appTop ta' (m9 S (up (inl a) : _a0))
        = m9 S (up (inl a) : _a0)
            + hAT pr2 (G a) := fun a => hta'c _
  have hta'inr : ∀ b,
      appTop ta' (m9 S (up (inr b) : _a0))
        = m9 S (up (inr b) : _a0) :=
    fun b => hta'c _
  have hfix1 : ∀ w : AffineSpace _a0 S
        ⟶ AffineSpace _a0 S,
      w ≫ _a1
          = _a1 →
      (∀ a,
        appTop w (m9 S (up (inl a) : _a0))
          = m9 S (up (inl a) : _a0)) →
      ∀ x : Γ(AffineSpace (UFin n) S, ⊤),
        appTop w (hAT pr1 x) = hAT pr1 x := by
    intro w hw hwc x
    have hcomp : w ≫ pr1 = pr1 := by
      refine m46 ?_ ?_
      rw [assoc, hpr1, hw]
      rintro ⟨a⟩
      rw [comp_appTop_apply, hpr1c a, hwc a]
    rw [← comp_appTop_apply, hcomp]
  have hfix2 : ∀ w : AffineSpace _a0 S
        ⟶ AffineSpace _a0 S,
      w ≫ _a1
          = _a1 →
      (∀ b,
        appTop w (m9 S (up (inr b) : _a0))
          = m9 S (up (inr b) : _a0)) →
      ∀ x : Γ(AffineSpace (UFin m) S, ⊤),
        appTop w (hAT pr2 x) = hAT pr2 x := by
    intro w hw hwc x
    have hcomp : w ≫ pr2 = pr2 := by
      refine m46 ?_ ?_
      rw [assoc, hpr2_, hw]
      rintro ⟨b⟩
      rw [comp_appTop_apply, hpr2c b, hwc b]
    rw [← comp_appTop_apply, hcomp]
  have hsgsg' : σ ≫ σ' = 𝟙 _ := by
    refine m46 ?_ ?_
    rw [assoc, hsg_', hsg_, id_comp]
    rintro ⟨a | b⟩
    rw [comp_appTop_apply, hsg'inl a, hsginl a, appTop_id_apply]
    rw [comp_appTop_apply, hsg'inr b, appTop_sub, hsginr b,
      hfix1 σ hsg_ hsginl $ F b, appTop_id_apply]
    ring
  have hsg'sg : σ' ≫ σ = 𝟙 _ := by
    refine m46 ?_ ?_
    rw [assoc, hsg_, hsg_', id_comp]
    rintro ⟨a | b⟩
    rw [comp_appTop_apply, hsginl a, hsg'inl a, appTop_id_apply]
    rw [comp_appTop_apply, hsginr b, appTop_add, hsg'inr b,
      hfix1 σ' hsg_' hsg'inl $ F b, appTop_id_apply]
    ring
  have htata' : ta_ ≫ ta' = 𝟙 _ := by
    refine m46 ?_ ?_
    rw [assoc, hta', hta, id_comp]
    rintro ⟨a | b⟩
    rw [comp_appTop_apply, hta'inl a, appTop_add, htainl a,
      hfix2 ta_ hta htainr $ G a, appTop_id_apply]
    ring
    rw [comp_appTop_apply, hta'inr b, htainr b, appTop_id_apply]
  have hta'ta : ta' ≫ ta_ = 𝟙 _ := by
    refine m46 ?_ ?_
    rw [assoc, hta, hta', id_comp]
    rintro ⟨a | b⟩
    rw [comp_appTop_apply, htainl a, appTop_sub, hta'inl a,
      hfix2 ta' hta' hta'inr $ G a, appTop_id_apply]
    ring
    rw [comp_appTop_apply, htainr b, hta'inr b, appTop_id_apply]
  obtain ⟨D, hDover, hcoordEq⟩ :
      ∃ d : Y ⟶ AffineSpace _a0 S,
        d ≫ _a1 = p ∧
          ∀ i, hAT d (m9 S i)
            = elim
                (fun a =>
                  hAT e1_ $ m9 S $ up a)
                (fun b =>
                  hAT e2_ $ m9 S $ up b) i.down :=
    ⟨m52 p fun i : _a0 => elim
        (fun a => hAT e1_ $ m9 S $ up a)
        (fun b => hAT e2_ $ m9 S $ up b)
        i.down,
      m179 _ _, fun i => m87 _ _ _⟩
  have hDinl : ∀ a,
      appTop D (m9 S (up (inl a) : _a0))
        = hAT e1_ (m9 S $ up a) := fun a => hcoordEq _
  have hDinr : ∀ b,
      appTop D (m9 S (up (inr b) : _a0))
        = hAT e2_ (m9 S $ up b) := fun b => hcoordEq _
  have hLpr1 : L ≫ pr1 = e1_ := by
    refine m46 ?_ ?_
    rw [assoc, hpr1, hLover, h1_]
    rintro ⟨a⟩
    rw [comp_appTop_apply, hpr1c a, hLinl a]
  have hLF : ∀ b, hAT L (hAT pr1 $ F b)
      = hAT e2_ (m9 S $ up b) := by
    intro b
    rw [← comp_appTop_apply, hLpr1, hF b]
  have hDpr2 : D ≫ pr2 = e2_ := by
    refine m46 ?_ ?_
    rw [assoc, hpr2_, hDover, h2_]
    rintro ⟨b⟩
    rw [comp_appTop_apply, hpr2c b, hDinr b]
  have hcompG : ∀ a, hAT D (hAT pr2 $ G a)
      = hAT e1_ (m9 S $ up a) := by
    intro a
    rw [← comp_appTop_apply, hDpr2, hG a]
  have hA : L ≫ σ = D := by
    refine m46 ?_ ?_
    rw [assoc, hsg_, hLover, hDover]
    rintro ⟨a | b⟩
    rw [comp_appTop_apply, hsginl a, hLinl a, hDinl a]
    rw [comp_appTop_apply, hsginr b, appTop_add, hLinr b, hLF b, hDinr b, zero_add]
  have hB : D ≫ ta_ = R := by
    refine m46 ?_ ?_
    rw [assoc, hta, hDover, hRover]
    rintro ⟨a | b⟩
    rw [comp_appTop_apply, htainl a, appTop_sub, hDinl a, hcompG a, hRinl a, sub_self]
    rw [comp_appTop_apply, htainr b, hDinr b, hRinr b]
  refine ⟨⟨σ ≫ ta_, ta' ≫ σ', ?_, ?_⟩, ?_, ?_⟩
  rw [assoc, ← assoc ta_ ta' σ', htata', id_comp, hsgsg']
  rw [assoc, ← assoc σ' σ ta_, hsg'sg, id_comp, hta'ta]
  show (σ ≫ ta_) ≫ _ = _
  rw [assoc, hta, hsg_]
  show L ≫ (σ ≫ ta_) = R
  rw [← assoc, hA, hB]

theorem closedEmbeddingsRelatedByAutomorphism : ClosedEmbeddingsRelatedByAutomorphism := by
  intro k hk Y hY p hp n m e1_ he1_ e2_ he2_ h1_ h2_
  have : IsAffine (affineSpaceIndexedBy k (UFin n)) := by
    unfold affineSpaceIndexedBy
    infer_instance
  have : IsAffine (affineSpaceIndexedBy k (UFin m)) := by
    unfold affineSpaceIndexedBy
    infer_instance
  choose F hF using fun b =>
    (isAffine_surjective_of_isAffine e1_).2
      (hAT e2_ (m9 (Sp k)
        (up b)))
  choose G hG using fun a =>
    (isAffine_surjective_of_isAffine e2_).2
      (hAT e1_ (m9 (Sp k)
        (up a)))
  exact exists_iso_affineSpace_sum_comp_eq_of_coord n m p e1_ e2_ h1_ h2_ F hF G hG
    (m52 p (coordVectorInl n m e1_))
    (m52 p (coordVectorInr n m e2_))
    (m179 _ _) (m179 _ _)
    (fun a => m87 _ _ _)
    (fun b => m87 _ _ _)
    (fun a => m87 _ _ _)
    (fun b => m87 _ _ _)

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite


namespace FunctorialResolution.EmbeddedResolution

structure AffineSpacePrincipalizationData (k : Type) [Field k] [CharZero k] (Y : Sch)
    [IsAffine Y] (pY : Y ⟶ Sp k)
    [LocallyOfFiniteType pY] : Type 1 where
  princ : PrincipalizationAlgorithm
  dim : ℕ
  emb : Y ⟶ affineSpaceIndexedBy k (UFin dim)
  emb_closedImmersion : IsClosedImmersion emb
  emb_nonzeroOnComponents : NonzeroOnComponents $ ker emb
  emb_comp : emb ≫ affineSpaceIndexedByToSpec k (UFin dim) = pY
  ambient_smooth : Smooth $ affineSpaceIndexedByToSpec k $ UFin dim
  ambient_snc : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k $ UFin dim)
      ([] : List (affineSpaceIndexedBy k $ UFin dim).IdealSheafData)

namespace AffineSpacePrincipalizationData

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

abbrev ambient : Sch := affineSpaceIndexedBy k $ ULift $ Fin S.dim

abbrev ambientToSpec : S.ambient ⟶ Sp k :=
  affineSpaceIndexedByToSpec k $ ULift $ Fin S.dim

def principalizationSequence : IdealBlowupSequence S.ambientToSpec (ker S.emb)
    ([] : List S.ambient.IdealSheafData) :=
  haveI := S.ambient_smooth
  S.princ k S.ambient S.ambientToSpec (ker S.emb) S.emb_nonzeroOnComponents []
    S.ambient_snc

def ambientBlowups : SequenceOfBlowups S.ambient := S.principalizationSequence.toSequenceOfBlowups

abbrev ambientLength : ℕ := S.ambientBlowups.length

section
variable (i : ℕ)
abbrev ambientLevel : Sch := S.ambientBlowups.schemeAt i

abbrev ambientBlowupMorphism : S.ambientLevel (i + 1) ⟶ S.ambientLevel i := S.ambientBlowups.transitionMapSucc i

abbrev ambientCenter : IdealSheafData $ S.ambientLevel i := S.ambientBlowups.center i

def strictTransformIdeal : IdealSheafData $ S.ambientLevel i :=
  Nat.rec (motive := fun j => IdealSheafData $ S.ambientLevel j)
    (ker $ S.emb ≫ S.ambientBlowups.isoZero.inv)
    (fun j ih => Blowup.strictTransform (S.ambientBlowupMorphism j) (S.ambientCenter j) ih) i

abbrev strictTransform : Sch := subscheme $ S.strictTransformIdeal i

abbrev strictTransformio : S.strictTransform i ⟶ S.ambientLevel i := subschemeι $ S.strictTransformIdeal i

theorem noetherianSpace_strictTransform
    [NoetherianSpace ↥(S.ambientLevel i)] :
    NoetherianSpace ↥(S.strictTransform i) :=
  noetherianSpace_subscheme $ S.strictTransformIdeal i

theorem exists_strictTransformMap :
    ∃ f : S.strictTransform (i + 1) ⟶ S.strictTransform i,
      f ≫ S.strictTransformio i = S.strictTransformio (i + 1) ≫ S.ambientBlowupMorphism i := by
  let _a0 := S.strictTransformIdeal $ i + 1
  have hle : S.strictTransformIdeal i ≤ _a0.map (S.ambientBlowupMorphism i) := by
    exact le_trans (le_map_comap (S.strictTransformIdeal i) $ S.ambientBlowupMorphism i) $ map_mono (S.ambientBlowupMorphism i) $ comap_le_strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i) $ S.strictTransformIdeal i
  exact ⟨_a0.subschemeMap (S.strictTransformIdeal i) (S.ambientBlowupMorphism i) hle,
    subschemeMap_subschemeι _ _ _ hle⟩

def strictTransformMap : S.strictTransform (i + 1) ⟶ S.strictTransform i := (S.exists_strictTransformMap i).choose

theorem strictTransformMap_comp_strictTransformio :
    S.strictTransformMap i ≫ S.strictTransformio i = S.strictTransformio (i + 1) ≫ S.ambientBlowupMorphism i :=
  (S.exists_strictTransformMap i).choose_spec

def discardedComponents : Set $ Set ↥(S.strictTransform i) :=
  {C | C ∈ irreducibleComponents ↥(S.strictTransform i) ∧
    (S.strictTransformio i).base '' C ⊆ (support (S.ambientCenter i) : Set ↥(S.ambientLevel i))}

theorem mem_discardedComponents_iff (C : Set ↥(S.strictTransform i)) :
    C ∈ S.discardedComponents i ↔
      C ∈ irreducibleComponents ↥(S.strictTransform i) ∧
        (S.strictTransformio i).base '' C ⊆ (support (S.ambientCenter i) : Set ↥(S.ambientLevel i)) := m22

def discardedLocus : Set ↥(S.strictTransform i) := ⋃₀ (S.discardedComponents i)

theorem isClosed_discardedLocus
    [NoetherianSpace ↥(S.strictTransform i)] :
    IsClosed (S.discardedLocus i) := by
  have hsub : S.discardedComponents i ⊆ irreducibleComponents (S.strictTransform i) := fun C hC =>
    (mp_ (S.mem_discardedComponents_iff i C) hC).1
  show IsClosed (⋃₀ (S.discardedComponents i))
  rw [sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion (m197 m169 hsub)
    (fun C hC => isClosed_of_mem_irreducibleComponents C $ hsub hC)

theorem discardedLocus_eq_sUnion_discardedComponents : S.discardedLocus i = ⋃₀ (S.discardedComponents i) := rfl

def discardedLocusClosure : Closeds ↥(S.strictTransform i) :=
  ⟨closure $ S.discardedLocus i, isClosed_closure⟩

theorem coe_discardedLocusClosure
    [NoetherianSpace ↥(S.strictTransform i)] :
    (S.discardedLocusClosure i : Set ↥(S.strictTransform i)) = S.discardedLocus i := by
  show closure (S.discardedLocus i) = S.discardedLocus i
  exact (S.isClosed_discardedLocus i).closure_eq

def discardedIdeal : (S.strictTransform i).IdealSheafData :=
  vanishingIdeal $ S.discardedLocusClosure i

theorem discardedIdeal_eq_vanishingIdeal :
    S.discardedIdeal i = vanishingIdeal (S.discardedLocusClosure i) := rfl

abbrev discardedSubscheme : Sch := subscheme $ S.discardedIdeal i

abbrev discardedio : S.discardedSubscheme i ⟶ S.strictTransform i := subschemeι $ S.discardedIdeal i

def discardedLocusClosureCompl : (S.strictTransform i).Opens := (S.discardedLocusClosure i).compl

theorem coe_discardedLocusClosureCompl :
    ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      (S.discardedLocusClosure i : Set ↥(S.strictTransform i))ᶜ := rfl

def comapAmbientCenter : (S.strictTransform i).IdealSheafData :=
  comap (S.ambientCenter i) $ S.strictTransformio i

theorem comapAmbientCenter_eq :
    S.comapAmbientCenter i = comap (S.ambientCenter i) (S.strictTransformio i) := rfl

def centerOffDetached : (S.strictTransform i).IdealSheafData :=
  ker
    (subschemeι (comap (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i) ≫ ι (S.discardedLocusClosureCompl i))

theorem centerOffDetached_eq :
    S.centerOffDetached i =
      ker
        (subschemeι (comap (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i) ≫
          ι (S.discardedLocusClosureCompl i)) := rfl

def discardedUnion : Sch :=
  Nat.rec (motive := fun _ => Sch) (⊥_ Sch)
    (fun j ih => ih ⨿ S.discardedSubscheme j) i



abbrev totalSpace : Sch := S.strictTransform i ⨿ S.discardedUnion i

def transitionMap : S.totalSpace (i + 1) ⟶ S.totalSpace i :=
  coprod.desc (S.strictTransformMap i ≫ coprod.inl)
    (coprod.desc (coprod.inr : S.discardedUnion i ⟶ S.totalSpace i)
        (S.discardedio i ≫ coprod.inl) :
      S.discardedUnion i ⨿ S.discardedSubscheme i ⟶ S.totalSpace i)

theorem inl_comp_transitionMap :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.transitionMap i =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) := by
  exact coprod.inl_desc _ _

def centerOnTotalSpace : IdealSheafData $ S.totalSpace i :=
  ker
    (subschemeι (S.centerOffDetached i) ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i))

theorem centerOnTotalSpace_eq_ker :
    S.centerOnTotalSpace i =
      ker
        (subschemeι (S.centerOffDetached i) ≫
          (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) := rfl
end

theorem exists_coprodInitialIso_inl_comp_eq_subschemeio {Z W : Sch} (I : ISD Z)
    (g : W ⟶ Z) (e0 : W ≅ I.subscheme) (he0 : e0.hom ≫ I.si = g) :
    ∃ e : (I.subscheme ⨿ (⊥_ Sch)) ≅ W,
      (coprod.inl : I.subscheme ⟶ I.subscheme ⨿ (⊥_ Sch)) ≫ e.hom ≫ g =
        I.si := by
  refine ⟨(coprod.rightUnitor I.subscheme).trans e0.symm, ?_⟩
  have hunit : (coprod.inl : subS I ⟶ subS I ⨿ (⊥_ Sch)) ≫
      (coprod.rightUnitor I.subscheme).hom = 𝟙 I.subscheme := coprod.inl_desc _ _
  rw [← assoc, trans_hom, ← assoc, hunit, id_comp, symm_hom, ← he0, ← assoc, e0.inv_hom_id, id_comp]

private theorem exists_iso_ker_subscheme {W V : Sch} (f : W ⟶ V)
    [IsClosedImmersion f] :
    ∃ e : W ≅ subscheme (ker f),
      hom e ≫ subschemeι (ker f) = f := by
  have hk : ker (m149 f).si = m149 f :=
    q2 _
  let _a0 := lift (m149 f).si f $ le_of_eq hk
  have hal_ : _a0 ≫ siI (m149 f) = f :=
    lift_fac _ _ _
  let _a1 := lift f (m149 f).si $ le_of_eq hk.symm
  have hbe_ : _a1 ≫ f = siI (m149 f) :=
    lift_fac _ _ _
  refine ⟨⟨_a0,
      _a1,
      ?_, ?_⟩, hal_⟩
  rw [← cancel_mono f, assoc, hbe_, hal_, id_comp]
  rw [← cancel_mono (m149 f).si, assoc, hal_, hbe_, id_comp]

@[simp] theorem strictTransformIdeal_zero :
    S.strictTransformIdeal 0 = ker (S.emb ≫ S.ambientBlowups.isoZero.inv) := rfl

@[simp] theorem strictTransformIdeal_succ (i : ℕ) :
    S.strictTransformIdeal (i + 1) =
      Blowup.strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i) (S.strictTransformIdeal i) := rfl

theorem exists_totalSpaceZeroIso :
    ∃ e : S.totalSpace 0 ≅ Y,
      (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ hom e ≫
          (S.emb ≫ S.ambientBlowups.isoZero.inv) = S.strictTransformio 0 := by
  have := S.emb_closedImmersion
  let _a0 := S.emb ≫ S.ambientBlowups.isoZero.inv
  obtain ⟨e0, he0⟩ := exists_iso_ker_subscheme _a0
  exact exists_coprodInitialIso_inl_comp_eq_subschemeio (m149 _a0)
    _a0 e0 he0

def totalSpaceZeroIso : S.totalSpace 0 ≅ Y := S.exists_totalSpaceZeroIso.choose

theorem totalSpaceZeroIso_spec :
    (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫
        (S.emb ≫ S.ambientBlowups.isoZero.inv) = S.strictTransformio 0 :=
  S.exists_totalSpaceZeroIso.choose_spec

def tower : ℕᵒᵖ ⥤ Sch :=
  (Functor.ofSequence fun i => (S.transitionMap i).op).leftOp

theorem tower_obj (i : ℕ) : S.tower.obj (Opposite.op i) = S.totalSpace i := rfl

theorem tower_map_succ (i : ℕ) :
    S.tower.map (homOfLE $ Nat.le_succ i).op = S.transitionMap i := by
  show ((Functor.ofSequence fun j => (S.transitionMap j).op).map $ homOfLE $ Nat.le_succ i).unop
      = S.transitionMap i
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

def TransitionsAreBlowups : Prop :=
  ∀ i, i < S.ambientLength → IsBlowupAlongIdealSheaf (S.tower.map (homOfLE $ Nat.le_succ i).op) (S.centerOnTotalSpace i)

def blowupSequence (h : S.TransitionsAreBlowups) : SequenceOfBlowups Y where
  length := S.ambientLength
  tower := S.tower
  isoZero := S.totalSpaceZeroIso
  center := S.centerOnTotalSpace
  isBlowup := h





def blowupSequenceWithoutIsos (h : S.TransitionsAreBlowups) : SequenceOfBlowups Y := (S.blowupSequence h).withoutIsoBlowups

end AffineSpacePrincipalizationData

section
variable (A : PrincipalizationAlgorithm) (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
def AffineSpacePrincipalizationData.ofAffine
    (k : Type) [Field k] [CharZero k] (Y : Sch) [IsAffine Y]
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY] :
    AffineSpacePrincipalizationData k Y pY where
  princ := A
  dim := (hemb k Y pY).choose
  emb := (hemb k Y pY).choose_spec.choose
  emb_closedImmersion := (hemb k Y pY).choose_spec.choose_spec.1
  emb_nonzeroOnComponents := (hemb k Y pY).choose_spec.choose_spec.2.1
  emb_comp := (hemb k Y pY).choose_spec.choose_spec.2.2
  ambient_smooth := hsm k $ (hemb k Y pY).choose
  ambient_snc := hsnc k $ (hemb k Y pY).choose

def EmbeddedPrincipalizationYieldsBlowups : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y],
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).TransitionsAreBlowups

def affineResolutionRuleOfPrincipalization
    (h : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm) : AffineResolutionRule := by
  intro k _ _ Y pY _ _ _ _
  exact (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).blowupSequenceWithoutIsos $ h k Y pY
end





section
variable {A B : Sch} (f : A ⟶ B)
private theorem noetherianSpace_of_isClosedImmersion
    [IsClosedImmersion f]
    (h : NoetherianSpace ↥B) : NoetherianSpace ↥A := by
  exact (isClosedEmbedding f).toIsEmbedding.toIsInducing.noetherianSpace

theorem noetherianSpace_of_isOpenImmersion
    [IsOpenImmersion f]
    (h : NoetherianSpace ↥B) : NoetherianSpace ↥A := by
  exact f.isOpenEmbedding.toIsEmbedding.toIsInducing.noetherianSpace
end

private theorem range_comp_base {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) :
    range ⇑(f ≫ g).base = ⇑g.base '' range ⇑f.base := by
  ext x
  simp [range_comp]

theorem quasiCompact_strictTransformio_of_noetherianSpace_source {X X1 : Sch}
    (pi_ : X1 ⟶ X) (Z D : ISD X) (h : NoetherianSpace ↥X1) :
    QuasiCompact $ strictTransformio pi_ Z D := by
  have := noetherianSpace_of_isOpenImmersion (p4 $ strictTransformOpens pi_ Z D)
    (noetherianSpace_of_isClosedImmersion (cmI D pi_).si h)
  infer_instance

theorem ker_eq_ker_of_iso_hom_comp {A B T : Sch} (f : A ⟶ T) (g : B ⟶ T)
    (e : A ≅ B) (h : hom e ≫ g = f) : ker f = ker g := by
  have : IsIso e.hom := ⟨⟨isoI e, e.hom_inv_id, e.inv_hom_id⟩⟩
  exact ker_eq_ker_of_isIso_comp f g e.hom h

theorem ker_comp_comap_io_eq_of_preimage_subset {A X : Sch} (a : A ⟶ X)
    (U : Opn X) (V : Opn A)
    (hle : ((a ⁻¹ᵁ U : Opn A) : Set ↥A) ⊆ ((V : Opn A) : Set ↥A))
    [QuasiCompact a]
    [QuasiCompact (Scheme.Opens.ι V ≫ a)] :
    comap (ker (Scheme.Opens.ι V ≫ a)) (Scheme.Opens.ι U)
      = comap (ker a) (Scheme.Opens.ι U) := by
  let _c0 := Scheme.Opens.ι (Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U)) ≫ Scheme.Opens.ι V
  have hcoePre : ((Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U) : Opn (oSch V)) :
        Set (oSch V))
      = (p4 V).base ⁻¹' ((preU a U) : Set A) := rfl
  let _a0 := p4 $ preU a U
  have hrange : range
        _c0.base
      = range _a0.base := by
    rw [range_comp_base, q1, q1, hcoePre,
      image_preimage_eq_inter_range, q1 V, inter_eq_self_of_subset_left hle]
  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
      _c0
      _a0 hrange
  let _a1 := p4 V ≫ a
  have hcomm : isoH (IsOpenImmersion.isoOfRangeEq
        _c0
        _a0 hrange) ≫ mrU a U
      = mrU _a1 U := by
    refine mp_ (cancel_mono (p4 U)) ?_
    rw [assoc, morphismRestrict_ι, ← assoc, hfac]
    exact tr_ (assoc _ _ _) (morphismRestrict_ι _a1 U).symm
  rw [ker_comap_io_eq_ker_morphismRestrict _a1 U,
    ker_comap_io_eq_ker_morphismRestrict a U]
  exact ker_eq_ker_of_iso_hom_comp _ _ _ hcomm

theorem exists_iso_subscheme_of_ideal_eq {X : Sch} {J J' : ISD X} (h : J = J')
    {T : Sch} (f : T ⟶ X)
    (he : ∃ e : subscheme J' ≅ T, hom e ≫ f = subschemeι J') :
    ∃ e : subscheme J ≅ T, hom e ≫ f = subschemeι J := by
  subst h
  exact he

theorem image_mem_irreducibleComponents_of_isOpenEmbedding {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (f : A → B) (hf : Topology.IsOpenEmbedding f)
    (hcl : IsClosed $ range f) {T : Set A} (hT : T ∈ irreducibleComponents A) :
    f '' T ∈ irreducibleComponents B := by
  have hTirr := an1 hT
  refine ⟨hTirr.image f hf.continuous.continuousOn, ?_⟩
  intro D hD hsubD
  have hDr : D ⊆ range f := by
    by_contra hcon
    obtain ⟨z, hzD, hz⟩ := mp_ not_subset hcon
    obtain ⟨a0, ha0⟩ := an1 hTirr
    obtain ⟨y, -, hy1, hy2⟩ :=
      hD.2 (range f) (range f)ᶜ hf.isOpen_range hcl.isOpen_compl ⟨f a0, hsubD ⟨a0, ha0, rfl⟩, ⟨a0, rfl⟩⟩ ⟨z, hzD, hz⟩
    exact hy2 hy1
  have hpre : IsIrreducible $ preimage f D := by
    constructor
    obtain ⟨b, hb⟩ := an1 hD
    obtain ⟨a, rfl⟩ := hDr hb
    exact ⟨a, hb⟩
    intro O1 O2 hO1_ hO2_ h1_ h2_
    obtain ⟨x1_, hx1D, hx1O⟩ := h1_
    obtain ⟨x2_, hx2D, hx2O⟩ := h2_
    obtain ⟨y, hyD, hy1, hy2⟩ :=
      hD.2 (imS f O1) (imS f O2) (hf.isOpenMap _ hO1_) (hf.isOpenMap _ hO2_)
        ⟨f x1_, hx1D, ⟨x1_, hx1O, rfl⟩⟩ ⟨f x2_, hx2D, ⟨x2_, hx2O, rfl⟩⟩
    obtain ⟨a1_, ha1_, ha1e⟩ := hy1
    obtain ⟨a2_, ha2_, ha2e⟩ := hy2
    refine ⟨a2_, ?_, ?_, ha2_⟩
    show f a2_ ∈ D
    rwa [ha2e]
    have hEq := hf.injective $ tr_ ha2e ha1e.symm
    rwa [hEq]
  have hTle := fun x hx => hsubD ⟨x, hx, rfl⟩
  intro y hy
  obtain ⟨a, rfl⟩ := hDr hy
  exact ⟨a, an2 hT hpre hTle hy, rfl⟩

section
variable (A F G : Sch)
private def coprodSwapAssocHom : (A ⨿ (F ⨿ G)) ⟶ ((A ⨿ G) ⨿ F) :=
  coprod.desc (coprod.inl ≫ coprod.inl) $ coprod.desc coprod.inr $ coprod.inr ≫ coprod.inl

private def coprodSwapAssocInv : ((A ⨿ G) ⨿ F) ⟶ (A ⨿ (F ⨿ G)) :=
  coprod.desc (coprod.desc coprod.inl $ coprod.inr ≫ coprod.inr) $ coprod.inl ≫ coprod.inr

theorem isIso_coprodSwapAssocHom :
    IsIso $ coprodSwapAssocHom A F G := by
  refine ⟨⟨coprodSwapAssocInv A F G, ?_, ?_⟩⟩
  refine coprod.hom_ext ?_ (coprod.hom_ext ?_ ?_) <;>
    simp [coprodSwapAssocHom, coprodSwapAssocInv, assoc, coprod.inl_desc,
      coprod.inr_desc, comp_id]
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) ?_ <;>
    simp [coprodSwapAssocHom, coprodSwapAssocInv, assoc, coprod.inl_desc,
      coprod.inr_desc, comp_id]
end

theorem isBlowupAlongIdealSheaf_coprodDesc_coprod {A B F G : Sch} (a : A ⟶ B) (g : G ⟶ B)
    (K : ISD B) (J : IdealSheafData $ B ⨿ F)
    (hinl : comap J (coprod.inl : B ⟶ B ⨿ F) = K)
    (hinr : comap J (coprod.inr : F ⟶ B ⨿ F) = ⊤)
    (h : IsBlowupAlongIdealSheaf (coprod.desc a g) K) :
    IsBlowupAlongIdealSheaf (coprod.desc (a ≫ (coprod.inl : B ⟶ B ⨿ F))
      (coprod.desc (coprod.inr : F ⟶ B ⨿ F) $ g ≫ (coprod.inl : B ⟶ B ⨿ F))) J := by
  have hmap : p15 (coprod.map (coprod.desc a g) $ 𝟙 F) J := by
    refine Blowup.IsBlowupAlongIdealSheaf.coprod ?_ ?_
    rwa [hinl]
    rw [hinr]
    exact isBlowupAlongIdealSheaf_id_top _
  have := isIso_coprodSwapAssocHom A F G
  refine isBlowupAlongIdealSheaf_of_isIso_comp _ _ (coprodSwapAssocHom A F G) ?_ _ hmap
  refine coprod.hom_ext ?_ (coprod.hom_ext ?_ ?_) <;>
    simp [coprodSwapAssocHom, assoc,
      coprod.inl_desc_assoc, coprod.inl_map, coprod.inr_map,
      id_comp]

namespace AffineSpacePrincipalizationData

variable {k : Type} [Field k] [CharZero k] {Y : Sch} [IsAffine Y]
  {pY : Y ⟶ Sp k} [LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)

section
variable (i : ℕ)
theorem strictTransformIdeal_succ_eq_strictTransform :
    S.strictTransformIdeal (i + 1) =
      Blowup.strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i) (S.strictTransformIdeal i) :=
  S.strictTransformIdeal_succ i

def discardedLocusOpens (h : IsOpen (S.discardedLocus i)) : (S.strictTransform i).Opens :=
  ⟨S.discardedLocus i, h⟩


section
variable [IsReduced (S.strictTransform i)] (hN : NoetherianSpace ↥(S.strictTransform i)) (hopen : IsOpen (S.discardedLocus i))
include hN hopen
theorem exists_iso_discardedSubscheme_discardedLocusOpens :
    ∃ e : S.discardedSubscheme i ≅ Scheme.Opens.toScheme (S.discardedLocusOpens i hopen),
      hom e ≫ Scheme.Opens.i (S.discardedLocusOpens i hopen) = S.discardedio i := by
  refine exists_iso_subscheme_of_ideal_eq ?_ _
    (exists_iso_subscheme_vanishingIdeal_of_isClosed (S.discardedLocusOpens i hopen) $ S.isClosed_discardedLocus i)
  rw [S.discardedIdeal_eq_vanishingIdeal i]
  congr 1
  exact m134 $ S.coe_discardedLocusClosure i

end

theorem isBlowupAlongIdealSheaf_transitionMap_of_coprodDesc
    (h : IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) $ S.discardedio i) $ S.centerOffDetached i) :
    IsBlowupAlongIdealSheaf (S.transitionMap i) $ S.centerOnTotalSpace i := by
  have hinl : comap (S.centerOnTotalSpace i) coprod.inl
      = S.centerOffDetached i := by
    rw [S.centerOnTotalSpace_eq_ker i, ker_comp_coprod_inl_comap_inl,
      q2]
  refine isBlowupAlongIdealSheaf_coprodDesc_coprod (S.strictTransformMap i) (S.discardedio i) (S.centerOffDetached i) (S.centerOnTotalSpace i)
    hinl ?_ h
  rw [S.centerOnTotalSpace_eq_ker i]
  exact ker_comp_coprod_inl_comap_inr _

theorem image_discardedLocus_subset_support :
    ⇑(S.strictTransformio i).base '' (S.discardedLocus i) ⊆
      (support (S.ambientCenter i) : Set ↥(S.ambientLevel i)) := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨C, hC, hxC⟩ := mp_ mem_sUnion hx
  exact an2 (mp_ (S.mem_discardedComponents_iff i C) hC) $ mem_image_of_mem _ hxC

theorem range_strictTransformMap_subset_discardedLocusClosureCompl (_hi : i < S.ambientLength)
    (hN : NoetherianSpace ↥(S.strictTransform i))
    (hN' : NoetherianSpace ↥(S.ambientLevel (i + 1)))
    (hopen : IsOpen (S.discardedLocus i)) :
    range ⇑(S.strictTransformMap i).base ⊆
      ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  have hqc : QuasiCompact
      (EmbeddedResolution.strictTransformio (S.ambientBlowupMorphism i) (S.ambientCenter i) $ S.strictTransformIdeal i) :=
    quasiCompact_strictTransformio_of_noetherianSpace_source _ _ _ hN'
  have hioemb : Topology.IsClosedEmbedding (S.strictTransformio i).base :=
    isClosedEmbedding $ S.strictTransformio i
  let _a0 := (S.discardedLocusClosureCompl i : Opn $ S.strictTransform i)
  have hUcoe : _a0
      = (S.discardedLocus i)ᶜ := by
    rw [S.coe_discardedLocusClosureCompl i, S.coe_discardedLocusClosure i]
  have hRclosed : IsClosed $ (S.strictTransformio i).base '' _a0 := by
    refine hioemb.isClosedMap _ ?_
    rw [hUcoe]
    exact hopen.isClosed_compl
  have hsub : (spI (S.strictTransformIdeal i) : Set $ S.ambientLevel i) \ (spI (S.ambientCenter i) : Set $ S.ambientLevel i)
      ⊆ (S.strictTransformio i).base ''
        _a0 := by
    rintro w ⟨hw, hw'⟩
    have hw2 : w ∈ range (S.strictTransformio i).base := by simp_all
    obtain ⟨z, rfl⟩ := hw2
    refine ⟨z, ?_, rfl⟩
    rw [hUcoe]
    intro hz
    exact hw' $ S.image_discardedLocus_subset_support i ⟨z, hz, rfl⟩
  rintro _ ⟨x, rfl⟩
  let _a2 := S.strictTransformio $ i + 1
  have h1 : _a2.base x ∈
      (spI (S.strictTransformIdeal $ i + 1) : Set $ S.ambientLevel $ i + 1) := by
    rw [← q5 $ S.strictTransformIdeal $ i + 1]
    exact mem_range_self x
  rw [S.strictTransformIdeal_succ i, support_strictTransform_eq_closure_preimage] at h1
  have h2 := (closure_minimal (preimage_mono hsub) $ hRclosed.preimage (S.ambientBlowupMorphism i).base.hom.continuous) h1
  have he : (S.strictTransformio i).base ((S.strictTransformMap i).base x)
      = (S.ambientBlowupMorphism i).base (_a2.base x) := by
    simpa using (congrArg (fun m : S.strictTransform (i + 1) ⟶ S.ambientLevel i => m.base x) $ S.strictTransformMap_comp_strictTransformio i)
  have h3 : (S.strictTransformio i).base ((S.strictTransformMap i).base x) ∈
      (S.strictTransformio i).base ''
        _a0 := by simp_all
  obtain ⟨z, hz, hzeq⟩ := h3
  rwa [← hioemb.injective hzeq]
end

theorem strictTransformio_eq_subschemeio (j : ℕ) : S.strictTransformio j = subschemeι (S.strictTransformIdeal j) := rfl

theorem noetherianSpace_strictTransform_of_ambientLevel (j : ℕ)
    (h : NoetherianSpace ↥(S.ambientLevel j)) :
    NoetherianSpace ↥(S.strictTransform j) :=
  noetherianSpace_of_isClosedImmersion (S.strictTransformio j) h

theorem isBlowupAlongIdealSheaf_lift_discardedLocusClosureCompl (hres : StrictTransformIsBlowupOfClosedSubscheme)
    (i : ℕ)
    (hi : i < S.ambientLength) (hNlev : IsNoetherian (S.ambientLevel i))
    (hNoetherian : NoetherianSpace ↥(S.strictTransform i))
    (hopen : IsOpen (S.discardedLocus i))
    (hf : range ⇑(S.strictTransformMap i).base ⊆ range ⇑(S.discardedLocusClosureCompl i).ib) :
    IsBlowupAlongIdealSheaf (IsOpenImmersion.lift (S.discardedLocusClosureCompl i).i (S.strictTransformMap i) hf)
      (comap (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i) := by
  have hUcoe : ((S.discardedLocusClosureCompl i : Opn (S.strictTransform i)) : Set (S.strictTransform i))
      = (S.discardedLocus i)ᶜ := by
    rw [S.coe_discardedLocusClosureCompl i, S.coe_discardedLocusClosure i]
  have hUclosed : IsClosed ((S.discardedLocusClosureCompl i : Opn (S.strictTransform i)) :
      Set (S.strictTransform i)) := by simp_all
  have hrangeU : range (S.discardedLocusClosureCompl i).ib
      = ((S.discardedLocusClosureCompl i : Opn (S.strictTransform i)) : Set (S.strictTransform i)) :=
    Scheme.Opens.range_ι _
  have hclos : IsClosedImmersion (opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i) := by
    refine of_isPreimmersion _ ?_
    have hcl2 :=
      (isClosedEmbedding (S.strictTransformio i)).isClosedMap _ hUclosed
    have hr : range (opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i).base
        = (S.strictTransformio i).base ''
          ((S.discardedLocusClosureCompl i : Opn (S.strictTransform i)) : Set (S.strictTransform i)) := by
      rw [range_comp_base, hrangeU]
    have hfin : IsClosed (range (opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i).base) := by
      rwa [hr]
    exact hfin
  have hIcomp : ∀ T ∈ irreducibleComponents (oSch (S.discardedLocusClosureCompl i)),
      ¬ ((opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i).base '' T
        ⊆ (spI (S.ambientCenter i) : Set (S.ambientLevel i))) := by
    intro T hT hsub
    have hCmem : (S.discardedLocusClosureCompl i).ib '' T
        ∈ irreducibleComponents (S.strictTransform i) := by
      refine image_mem_irreducibleComponents_of_isOpenEmbedding _ (S.discardedLocusClosureCompl i).ι.isOpenEmbedding ?_ hT
      rwa [hrangeU]
    have himg : (opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i).base '' T
        = (S.strictTransformio i).base '' ((S.discardedLocusClosureCompl i).ib '' T) := by
      ext y
      constructor
      simp_all
      simp_all
    rw [himg] at hsub
    have hDiscarded : (S.discardedLocusClosureCompl i).ib '' T ∈ S.discardedComponents i := ⟨hCmem, hsub⟩
    obtain ⟨t, ht⟩ := hT.1.1
    have h1 :=
      subset_sUnion_of_mem hDiscarded ⟨t, ht, rfl⟩
    have h2 : (S.discardedLocusClosureCompl i).ib t
        ∈ ((S.discardedLocusClosureCompl i : Opn (S.strictTransform i)) : Set (S.strictTransform i)) := by
      rw [← hrangeU]
      exact mem_range_self t
    rw [hUcoe] at h2
    exact h2 h1
  have hqio : QuasiCompact (S.strictTransformio i) := inferInstance
  have hqj : QuasiCompact (opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i) := inferInstance
  have hOU : ((S.strictTransformio i ⁻¹ᵁ (suppC (S.ambientCenter i)) :
        Opn (S.strictTransform i)) : Set (S.strictTransform i))
      ⊆ ((S.discardedLocusClosureCompl i : Opn (S.strictTransform i)) : Set (S.strictTransform i)) := by
    intro x hx
    rw [hUcoe]
    intro hDisc
    exact hx (S.image_discardedLocus_subset_support i ⟨x, hDisc, rfl⟩)
  have hkerRestr := ker_comp_comap_io_eq_of_preimage_subset (S.strictTransformio i) (suppC (S.ambientCenter i))
    (S.discardedLocusClosureCompl i) hOU
  have hKerStrict :=
    ker_subschemeι (S.strictTransformIdeal i)
  have hST : Blowup.strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i)
      (ker (opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i)) = S.strictTransformIdeal (i + 1) := by
    rw [S.strictTransformIdeal_succ i]
    refine strictTransform_congr_of_comap_io_eq (S.ambientBlowupMorphism i) (S.ambientCenter i) _ _ ?_
    rw [hkerRestr, hKerStrict]
  have hstat := hres (S.ambientLevel i) (S.ambientLevel (i + 1)) (oSch (S.discardedLocusClosureCompl i))
      (opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i) (S.ambientBlowupMorphism i) (S.ambientCenter i)
      (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) hIcomp
  rw [hST] at hstat
  obtain ⟨ps_, hpsfac, hpsbl⟩ := hstat
  have : Mono (opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i) := inferInstance
  have hps_ : ps_ = IsOpenImmersion.lift (S.discardedLocusClosureCompl i).i (S.strictTransformMap i) hf := by
    refine mp_ (cancel_mono (opI (S.discardedLocusClosureCompl i) ≫ S.strictTransformio i)) ?_
    rw [hpsfac, ← assoc, IsOpenImmersion.lift_fac]
    exact sy_ (S.strictTransformMap_comp_strictTransformio i)
  rwa [hps_, comap_comp] at hpsbl

theorem isReduced_strictTransform [IsReduced Y]
    (hN : ∀ j, j ≤ S.ambientLength → IsNoetherian (S.ambientLevel j))
    (j : ℕ) (hj : j ≤ S.ambientLength) :
    IsReduced $ S.strictTransform j := by
  revert hj
  induction j with
  | zero =>
    intro _
    exact isReduced_subscheme_ker $ S.emb ≫ S.ambientBlowups.isoZero.inv
  | succ n ih =>
    intro hj
    have hn := lt_of_succ_le hj
    have : IsReduced (S.strictTransformIdeal n).subscheme := ih $ le_of_lt hn
    let _a0 := S.ambientLevel $ n + 1
    have hNoeth : NoetherianSpace _a0 := by
      have : IsNoetherian _a0 := hN (n + 1) hj
      infer_instance
    have : QuasiCompact
        (EmbeddedResolution.strictTransformio (S.ambientBlowupMorphism n) (S.ambientCenter n) $ S.strictTransformIdeal n) :=
      quasiCompact_strictTransformio_of_noetherianSpace_source _ _ _ hNoeth
    exact isReduced_subscheme_strictTransform (S.ambientBlowupMorphism n) (S.ambientCenter n)
      (S.strictTransformIdeal n) $ S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn

end AffineSpacePrincipalizationData

section
variable (A : PrincipalizationAlgorithm) (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
def EmbeddedPrincipalizationDiscardedLocusIsOpen : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] (i : ℕ),
    i < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength →
      IsOpen ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedLocus i)

def EmbeddedPrincipalizationAmbientIsNoetherian : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] (i : ℕ),
    i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength →
      IsNoetherian ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel i)

theorem embeddedPrincipalizationYieldsBlowups_of_discardedLocusIsOpen
    (hiso : EmbeddedPrincipalizationDiscardedLocusIsOpen A hemb hsnc hsm)
    (hnoeth : EmbeddedPrincipalizationAmbientIsNoetherian A hemb hsnc hsm)
    (hres : StrictTransformIsBlowupOfClosedSubscheme) :
    EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  set S := AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY with hSdef
  intro i hi
  have hopen := hiso k Y pY i hi
  have hNlev : ∀ j, j ≤ S.ambientLength → NoetherianSpace (S.ambientLevel j) := by
    intro j hj
    have := hnoeth k Y pY j hj
    infer_instance
  have hNoetherian :=
    S.noetherianSpace_strictTransform_of_ambientLevel i $ hNlev i $ le_of_lt hi
  have hRed :=
    S.isReduced_strictTransform (fun j hj => hnoeth k Y pY j hj) i $ le_of_lt hi
  have hf : range (S.strictTransformMap i).base ⊆ range (S.discardedLocusClosureCompl i).ib := by
    rw [q1]
    exact S.range_strictTransformMap_subset_discardedLocusClosureCompl i hi hNoetherian (hNlev (i + 1) hi) hopen
  have hkey := S.isBlowupAlongIdealSheaf_lift_discardedLocusClosureCompl hres i hi (hnoeth k Y pY i $ le_of_lt hi)
    hNoetherian hopen hf
  rw [S.tower_map_succ i]
  have _i25 : p15 (coprod.desc (S.strictTransformMap i) $ S.discardedio i) $ S.centerOffDetached i := by
    have := hNoetherian
    have hUcoe : ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set $ S.strictTransform i)
        = (S.discardedLocus i)ᶜ := by
      rw [S.coe_discardedLocusClosureCompl i, S.coe_discardedLocusClosure i]
    have hVcoe : ((S.discardedLocusOpens i hopen : (S.strictTransform i).Opens) : Set $ S.strictTransform i)
        = S.discardedLocus i := rfl
    have hcompl : IsCompl (S.discardedLocusClosureCompl i) $ S.discardedLocusOpens i hopen := by
      constructor
      rw [disjoint_iff]
      refine m55 ?_
      rw [coe_inf, hUcoe, hVcoe, coe_bot]
      exact compl_inter_self _
      rw [codisjoint_iff]
      refine m55 ?_
      rw [coe_sup, hUcoe, hVcoe, coe_top]
      exact compl_union_self _
    obtain ⟨e', he'⟩ := S.exists_iso_discardedSubscheme_discardedLocusOpens i hNoetherian hopen
    have hg : range (S.discardedio i).base ⊆ range (S.discardedLocusOpens i hopen).ib := by
      rw [← he']
      rintro _ ⟨z, rfl⟩
      exact ⟨e'.hom.base z, by simp⟩
    have hliftV : m43 (S.discardedLocusOpens i hopen).i (S.discardedio i) hg = isoH e' := by
      refine mp_ (cancel_mono (S.discardedLocusOpens i hopen).i) ?_
      rw [m115, he']
    have : IsIso
        (m43 (S.discardedLocusOpens i hopen).i (S.discardedio i) hg) := by
      rw [hliftV]
      infer_instance
    have hNU :=
      noetherianSpace_of_isOpenImmersion (S.discardedLocusClosureCompl i).i hNoetherian
    have hNsub :=
      noetherianSpace_of_isClosedImmersion
        (cmI (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i).subschemeι hNU
    have hq1 : QuasiCompact
        (cmI (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i).subschemeι := inferInstance
    have hq2 : QuasiCompact
        (siI (cmI (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i) ≫
          ι (S.discardedLocusClosureCompl i)) := inferInstance
    have hJU : cmI (S.centerOffDetached i) (S.discardedLocusClosureCompl i).i
        = cmI (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i := by
      rw [S.centerOffDetached_eq i]
      exact comap_ker_subschemeio_comp _ _
    have hJV : cmI (S.centerOffDetached i) (S.discardedLocusOpens i hopen).i = ⊤ := by
      rw [S.centerOffDetached_eq i]
      refine p39 _ _ ?_
      intro x hx
      have hx' : (S.discardedLocusOpens i hopen).ib x ∈
          ((ker $ siI (cmI (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i) ≫
            ι (S.discardedLocusClosureCompl i)).support : Set $ S.strictTransform i) := hx
      rw [support_ker $ siI (cmI (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i) ≫
        ι (S.discardedLocusClosureCompl i)] at hx'
      have hsubU : range (siI (cmI (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i) ≫
          ι (S.discardedLocusClosureCompl i)).base
          ⊆ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set $ S.strictTransform i) := by
        rw [← q1 $ S.discardedLocusClosureCompl i]
        rintro _ ⟨z, rfl⟩
        exact ⟨(siI $ cmI (S.comapAmbientCenter i) (S.discardedLocusClosureCompl i).i).base z, by simp⟩
      have hclosedU : IsClosed
          ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set $ S.strictTransform i) := by
        rw [hUcoe]
        exact hopen.isClosed_compl
      have hmem := closure_minimal hsubU hclosedU hx'
      rw [hUcoe] at hmem
      refine hmem ?_
      have h0 : (S.discardedLocusOpens i hopen).ib x ∈
          range (S.discardedLocusOpens i hopen).ib := mem_range_self x
      rwa [q1] at h0
    have hoi : ∀ b, IsOpenImmersion
        (m190 (motive := fun b =>
            (cond b (S.discardedLocusClosureCompl i).toScheme (S.discardedLocusOpens i hopen).toScheme) ⟶ S.strictTransform i)
          (S.discardedLocusOpens i hopen).i (S.discardedLocusClosureCompl i).i b) := by
      intro b
      cases b
      exact inferInstanceAs
        (IsOpenImmersion (S.discardedLocusOpens i hopen).i)
      exact inferInstanceAs $ IsOpenImmersion (S.discardedLocusClosureCompl i).i
    refine Blowup.IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover _ _
      (fun b => cond b (S.discardedLocusClosureCompl i).toScheme (S.discardedLocusOpens i hopen).toScheme)
      (m190 (motive := fun b =>
          (cond b (S.discardedLocusClosureCompl i).toScheme (S.discardedLocusOpens i hopen).toScheme) ⟶ S.strictTransform i)
        (S.discardedLocusOpens i hopen).i (S.discardedLocusClosureCompl i).i) ?_ ?_
    intro x
    by_cases hx : x ∈ S.discardedLocus i
    refine ⟨false, ?_⟩
    show x ∈ range (S.discardedLocusOpens i hopen).ib
    rwa [q1]
    refine ⟨true, ?_⟩
    show x ∈ range (S.discardedLocusClosureCompl i).ib
    rwa [q1, hUcoe]
    intro b
    cases b
    show p15 (pullback.snd (coprod.desc (S.strictTransformMap i) $ S.discardedio i)
      (S.discardedLocusOpens i hopen).i) $ cmI (S.centerOffDetached i) (S.discardedLocusOpens i hopen).i
    rw [hJV]
    obtain ⟨e, he1, _⟩ :=
      exists_iso_pullback_coprod_desc_right (S.strictTransformMap i) (S.discardedio i) hcompl hf hg
    have : IsIso $ pullback.snd (coprod.desc (S.strictTransformMap i) $ S.discardedio i)
        (S.discardedLocusOpens i hopen).i := by
      rw [← he1]
      infer_instance
    exact Blowup.IsBlowupAlongIdealSheaf.of_isIso _
    show p15 (pullback.snd (coprod.desc (S.strictTransformMap i) $ S.discardedio i)
      (S.discardedLocusClosureCompl i).i) $ cmI (S.centerOffDetached i) (S.discardedLocusClosureCompl i).i
    rw [hJU]
    obtain ⟨e, he1, _⟩ :=
      exists_iso_pullback_coprod_desc_left (S.strictTransformMap i) (S.discardedio i) hcompl hf hg
    exact isBlowupAlongIdealSheaf_of_isIso_comp _ _ e.hom he1 _ hkey
  exact S.isBlowupAlongIdealSheaf_transitionMap_of_coprodDesc i
    _i25
end





structure EmbeddedBlowupSequence (k : Type) [Field k] [CharZero k] (Y : Sch)
    [IsAffine Y] (pY : Y ⟶ Sp k)
    [LocallyOfFiniteType pY] : Type 1 where
  ambient : Sch
  ambientStruct : ambient ⟶ Sp k
  isAffine_ambient : IsAffine ambient
  smooth_ambientStruct : Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : QuasiCompact ambientStruct
  emb : Y ⟶ ambient
  isClosedImmersion_emb : IsClosedImmersion emb
  emb_comp : emb ≫ ambientStruct = pY
  ambientSeq : SequenceOfBlowups ambient

namespace EmbeddedBlowupSequence

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]

instance instIsAffineAmbient (T : EmbeddedBlowupSequence k Y pY) :
    IsAffine T.ambient := T.isAffine_ambient

instance instSmoothAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    Smooth T.ambientStruct := T.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    LocallyOfFiniteType T.ambientStruct :=
  T.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    QuasiCompact T.ambientStruct := T.quasiCompact_ambientStruct

instance instIsClosedImmersionEmb (T : EmbeddedBlowupSequence k Y pY) :
    IsClosedImmersion T.emb := T.isClosedImmersion_emb

variable (T : EmbeddedBlowupSequence k Y pY)

abbrev length : ℕ := T.ambientSeq.length

section
variable (i : ℕ)
abbrev schemeAt : Sch := T.ambientSeq.schemeAt i

abbrev blowdown : T.schemeAt (i + 1) ⟶ T.schemeAt i := T.ambientSeq.transitionMapSucc i

abbrev ambientCenter : IdealSheafData $ T.schemeAt i := T.ambientSeq.center i

def strictTransformIdeal : IdealSheafData $ T.schemeAt i :=
  Nat.rec (motive := fun j => IdealSheafData $ T.schemeAt j)
    (ker $ T.emb ≫ T.ambientSeq.isoZero.inv)
    (fun j ih => Blowup.strictTransform (T.blowdown j) (T.ambientCenter j) ih) i

abbrev strictTransform : Sch := subscheme $ T.strictTransformIdeal i

abbrev strictTransformio : T.strictTransform i ⟶ T.schemeAt i := subschemeι $ T.strictTransformIdeal i

theorem comap_strictTransformIdeal_le :
    comap (T.strictTransformIdeal i) (T.blowdown i) ≤ T.strictTransformIdeal (i + 1) :=
  comap_le_strictTransform _ _ _

theorem exists_strictTransformMap :
    ∃ f : T.strictTransform (i + 1) ⟶ T.strictTransform i,
      f ≫ T.strictTransformio i = T.strictTransformio (i + 1) ≫ T.blowdown i := by
  have hle :=
    mpr le_map_iff_comap_le $ T.comap_strictTransformIdeal_le i
  let _a0 := T.strictTransformIdeal $ i + 1
  exact ⟨_a0.subschemeMap (T.strictTransformIdeal i) (T.blowdown i) hle,
    subschemeMap_subschemeι _a0 (T.strictTransformIdeal i)
      (T.blowdown i) hle⟩

def strictTransformMap : T.strictTransform (i + 1) ⟶ T.strictTransform i := (T.exists_strictTransformMap i).choose

theorem strictTransformMap_comp_strictTransformio :
    T.strictTransformMap i ≫ T.strictTransformio i = T.strictTransformio (i + 1) ≫ T.blowdown i :=
  (T.exists_strictTransformMap i).choose_spec

def detachedComponents : Set (Set ↥(T.strictTransform i)) :=
  {C | C ∈ irreducibleComponents ↥(T.strictTransform i) ∧
    (T.strictTransformio i).base '' C ⊆ (support (T.ambientCenter i) : CSet (T.schemeAt i))}

theorem mem_detachedComponents (C : Set ↥(T.strictTransform i)) :
    C ∈ T.detachedComponents i ↔
      C ∈ irreducibleComponents ↥(T.strictTransform i) ∧
        (T.strictTransformio i).base '' C ⊆ (support (T.ambientCenter i) : CSet $ T.schemeAt i) := m22

def detachedLocus : Set ↥(T.strictTransform i) := ⋃₀ (T.detachedComponents i)

theorem detachedLocus_eq_sUnion : T.detachedLocus i = ⋃₀ (T.detachedComponents i) := rfl

theorem isClosed_detachedLocus
    [NoetherianSpace ↥(T.strictTransform i)] :
    IsClosed $ T.detachedLocus i := by
  have hsub : T.detachedComponents i ⊆ irreducibleComponents (T.strictTransform i) :=
    fun C hC => an1 $ mp_ (T.mem_detachedComponents i C) hC
  rw [T.detachedLocus_eq_sUnion i, sUnion_eq_biUnion]
  exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset hsub).isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents _ $ hsub hC

def detachedClosure : Closeds ↥(T.strictTransform i) :=
  ⟨closure $ T.detachedLocus i, isClosed_closure⟩

theorem detachedClosure_coe
    [NoetherianSpace ↥(T.strictTransform i)] :
    (T.detachedClosure i : Set ↥(T.strictTransform i)) = T.detachedLocus i := by
  show closure (T.detachedLocus i) = T.detachedLocus i
  exact (T.isClosed_detachedLocus i).closure_eq

def detachedIdeal : (T.strictTransform i).IdealSheafData :=
  vanishingIdeal $ T.detachedClosure i

theorem detachedIdeal_eq :
    T.detachedIdeal i = vanishingIdeal (T.detachedClosure i) := rfl

abbrev detachedScheme : Sch := subscheme $ T.detachedIdeal i

abbrev detachedio : T.detachedScheme i ⟶ T.strictTransform i := subschemeι $ T.detachedIdeal i

def detachedClosureCompl : (T.strictTransform i).Opens := (T.detachedClosure i).compl

theorem detachedClosureCompl_coe :
    ((T.detachedClosureCompl i : (T.strictTransform i).Opens) : Set ↥(T.strictTransform i)) =
      (T.detachedClosure i : Set ↥(T.strictTransform i))ᶜ := rfl

def comapAmbientCenter : (T.strictTransform i).IdealSheafData :=
  comap (T.ambientCenter i) $ T.strictTransformio i

theorem comapAmbientCenter_eq :
    T.comapAmbientCenter i = comap (T.ambientCenter i) (T.strictTransformio i) := rfl

def centerOffDetached : (T.strictTransform i).IdealSheafData :=
  ker
    (subschemeι (comap (T.comapAmbientCenter i) (T.detachedClosureCompl i).i) ≫ ι (T.detachedClosureCompl i))

theorem centerOffDetached_eq :
    T.centerOffDetached i =
      ker
        (subschemeι (comap (T.comapAmbientCenter i) (T.detachedClosureCompl i).i) ≫
          ι (T.detachedClosureCompl i)) := rfl

def detachedCoprod : Sch :=
  Nat.rec (motive := fun _ => Sch) (⊥_ Sch)
    (fun j ih => ih ⨿ T.detachedScheme j) i

abbrev totalSpace : Sch := T.strictTransform i ⨿ T.detachedCoprod i

def totalTransition : T.totalSpace (i + 1) ⟶ T.totalSpace i :=
  coprod.desc (T.strictTransformMap i ≫ coprod.inl)
    (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
        (T.detachedio i ≫ coprod.inl) :
      T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i)

theorem inl_totalTransition_eq_strictTransformMap_inl :
    (coprod.inl : T.strictTransform (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      T.strictTransformMap i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) := by
  let _a0 := (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)
  exact coprod.inl_desc (T.strictTransformMap i ≫ _a0)
    (coprod.desc coprod.inr
      (T.detachedio i ≫ _a0) :
      T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i)

theorem inl_inr_totalTransition :
    (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod (i + 1)) ≫
        (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i) := by
  exact m32
    (congrArg
      (fun f : T.detachedCoprod (i + 1) ⟶ T.totalSpace i =>
        (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod (i + 1)) ≫ f) $ coprod.inr_desc _ _)
    (coprod.inl_desc coprod.inr
      (T.detachedio i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)))

theorem inr_inr_totalTransition :
    (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod (i + 1)) ≫
        (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      T.detachedio i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) := by
  exact m32
    (congrArg
      (fun f : T.detachedCoprod (i + 1) ⟶ T.totalSpace i =>
        (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod (i + 1)) ≫ f) $ coprod.inr_desc _ _)
    (coprod.inr_desc _ _)

def totalCenter : IdealSheafData $ T.totalSpace i :=
  ker
    (subschemeι (T.centerOffDetached i) ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i))

theorem totalCenter_eq :
    T.totalCenter i =
      ker
        (subschemeι (T.centerOffDetached i) ≫
          (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) := rfl
end

theorem exists_coprodIso_of_isInitial {A B Z : Sch}
    (hB : IsInitial B) (u : A ≅ Z) :
    ∃ e : (A ⨿ B) ≅ Z, (coprod.inl : A ⟶ A ⨿ B) ≫ hom e = hom u := by
  let _a0 := coprod.desc u.hom $ hB.to Z
  let _c0 := (coprod.inl : A ⟶ A ⨿ B)
  refine ⟨⟨_a0, isoI u ≫ coprod.inl, ?_, ?_⟩, coprod.inl_desc _ _⟩
  refine coprod.hom_ext ?_ $ hB.hom_ext _ _
  calc _c0 ≫ (_a0 ≫ (isoI u ≫ coprod.inl))
      = (_c0 ≫ _a0) ≫
          (isoI u ≫ _c0) := sy_ $ assoc _ _ _
    _ = isoH u ≫ (isoI u ≫ _c0) :=
        congrArg (fun t => t ≫ (isoI u ≫ _c0)) $ coprod.inl_desc _ _
    _ = (isoH u ≫ isoI u) ≫ _c0 := sy_ $ assoc _ _ _
    _ = 𝟙 A ≫ _c0 :=
        congrArg (fun t => t ≫ _c0) u.hom_inv_id
    _ = _c0 := id_comp _
    _ = _c0 ≫ 𝟙 (A ⨿ B) := sy_ $ comp_id _
  calc (isoI u ≫ _c0) ≫ _a0
      = isoI u ≫ (_c0 ≫ _a0) :=
        assoc _ _ _
    _ = isoI u ≫ isoH u := congrArg (fun t => isoI u ≫ t) $ coprod.inl_desc _ _
    _ = 𝟙 Z := u.inv_hom_id

theorem exists_kerSubschemeIso_of_isClosedImmersion {X Z : Sch} (g : Z ⟶ X)
    [IsClosedImmersion g] :
    ∃ u : (ker g).subscheme ≅ Z, u.hom ≫ g = (ker g).si :=
  ⟨(asIso g.toImage).symm, by
    rw [symm_hom, asIso_inv, IsIso.inv_comp_eq, toImage_imageι]⟩

@[simp] theorem strictTransformIdeal_zero :
    T.strictTransformIdeal 0 = ker (T.emb ≫ T.ambientSeq.isoZero.inv) := rfl

@[simp] theorem strictTransformIdeal_succ (i : ℕ) :
    T.strictTransformIdeal (i + 1) =
      Blowup.strictTransform (T.blowdown i) (T.ambientCenter i) (T.strictTransformIdeal i) := rfl

@[simp] theorem detachedCoprod_zero : T.detachedCoprod 0 = ⊥_ Sch := rfl

@[simp] theorem detachedCoprod_succ (i : ℕ) :
    T.detachedCoprod (i + 1) = (T.detachedCoprod i ⨿ T.detachedScheme i) := rfl

theorem exists_totalSpaceZeroIso :
    ∃ e : T.totalSpace 0 ≅ Y,
      (coprod.inl : T.strictTransform 0 ⟶ T.totalSpace 0) ≫ hom e ≫
          (T.emb ≫ T.ambientSeq.isoZero.inv) = T.strictTransformio 0 := by
  let _a0 := T.emb ≫ T.ambientSeq.isoZero.inv
  have : IsClosedImmersion _a0 := inferInstance
  obtain ⟨u, hu⟩ := exists_kerSubschemeIso_of_isClosedImmersion
    _a0
  obtain ⟨e, he⟩ :=
    exists_coprodIso_of_isInitial (A := T.strictTransform 0) (B := T.detachedCoprod 0) (Z := Y) initialIsInitial u
  refine ⟨e, ?_⟩
  refine m32 ?_ hu
  exact m32 (m146 _ _ _).symm $ congrArg (fun t => t ≫ _a0) he

def totalSpaceZeroIso : T.totalSpace 0 ≅ Y := T.exists_totalSpaceZeroIso.choose

theorem totalSpaceZeroIso_spec :
    (coprod.inl : T.strictTransform 0 ⟶ T.totalSpace 0) ≫ T.totalSpaceZeroIso.hom ≫
        (T.emb ≫ T.ambientSeq.isoZero.inv) = T.strictTransformio 0 :=
  T.exists_totalSpaceZeroIso.choose_spec

def totalTower : ℕᵒᵖ ⥤ Sch :=
  (Functor.ofSequence fun i => (T.totalTransition i).op).leftOp


theorem totalTower_map_succ (i : ℕ) :
    T.totalTower.map (homOfLE $ Nat.le_succ i).op = T.totalTransition i := by
  show ((Functor.ofSequence fun j => (T.totalTransition j).op).map
      (homOfLE $ Nat.le_succ i)).unop = T.totalTransition i
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

def TransitionsAreBlowups : Prop :=
  ∀ i, i < T.length → IsBlowupAlongIdealSheaf (T.totalTower.map (homOfLE $ Nat.le_succ i).op) (T.totalCenter i)

section
variable (h : T.TransitionsAreBlowups)
def inducedBlowups : SequenceOfBlowups Y where
  length := T.length
  tower := T.totalTower
  isoZero := T.totalSpaceZeroIso
  center := T.totalCenter
  isBlowup := h

@[simp] theorem inducedBlowups_length : (T.inducedBlowups h).length = T.length := rfl



@[simp] theorem inducedBlowups_center (i : ℕ) :
    center (T.inducedBlowups h) i = T.totalCenter i := rfl

def inducedBlowupsWithoutIso : SequenceOfBlowups Y := (T.inducedBlowups h).withoutIsoBlowups
end

end EmbeddedBlowupSequence

section
variable (k : Type) [Field k] (n : ℕ)
theorem locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift :
    LocallyOfFiniteType $ affineSpaceIndexedByToSpec k $ UFin n := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

theorem quasiCompact_affineSpaceIndexedByToSpec_ulift :
    QuasiCompact $ affineSpaceIndexedByToSpec k $ UFin n := by
  unfold affineSpaceIndexedByToSpec
  infer_instance
end

namespace AffineSpacePrincipalizationData

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]

section
variable (S : AffineSpacePrincipalizationData k Y pY)
def toEmbeddedBlowupSequence : EmbeddedBlowupSequence k Y pY where
  ambient := S.ambient
  ambientStruct := S.ambientToSpec
  isAffine_ambient := inferInstance
  smooth_ambientStruct := S.ambient_smooth
  locallyOfFiniteType_ambientStruct := locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift k S.dim
  quasiCompact_ambientStruct := quasiCompact_affineSpaceIndexedByToSpec_ulift k S.dim
  emb := S.emb
  isClosedImmersion_emb := S.emb_closedImmersion
  emb_comp := S.emb_comp
  ambientSeq := S.ambientBlowups


theorem toEmbeddedBlowupSequence_schemeAt (i : ℕ) :
    S.toEmbeddedBlowupSequence.schemeAt i = S.ambientLevel i := rfl


theorem toEmbeddedBlowupSequence_transitionsAreBlowups_iff :
    S.toEmbeddedBlowupSequence.TransitionsAreBlowups ↔ S.TransitionsAreBlowups := m22

theorem embeddedInducedBlowups_eq (h : S.TransitionsAreBlowups) :
    S.toEmbeddedBlowupSequence.inducedBlowups (mpr (toEmbeddedBlowupSequence_transitionsAreBlowups_iff S) h) = S.blowupSequence h := rfl

theorem embeddedInducedBlowupsWithoutIso_eq (h : S.TransitionsAreBlowups) :
    S.toEmbeddedBlowupSequence.inducedBlowupsWithoutIso (mpr (toEmbeddedBlowupSequence_transitionsAreBlowups_iff S) h) = S.blowupSequenceWithoutIsos h := by
  show (S.toEmbeddedBlowupSequence.inducedBlowups $ mpr_ (toEmbeddedBlowupSequence_transitionsAreBlowups_iff S) h).withoutIsoBlowups
      = (S.blowupSequence h).withoutIsoBlowups
  exact congrArg SequenceOfBlowups.withoutIsoBlowups $ embeddedInducedBlowups_eq S h
end

end AffineSpacePrincipalizationData

namespace EmbeddingDatum

variable {k : Type} [Field k] [CharZero k] {Y} [IsAffine Y]
  {pY} [LocallyOfFiniteType pY]

section
variable (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm)
def toEmbeddedBlowupSequence : EmbeddedBlowupSequence k Y pY where
  ambient := D.ambient
  ambientStruct := D.ambientStruct
  isAffine_ambient := D.isAffine_ambient
  smooth_ambientStruct := D.smooth_ambientStruct
  locallyOfFiniteType_ambientStruct := D.locallyOfFiniteType_ambientStruct
  quasiCompact_ambientStruct := D.quasiCompact_ambientStruct
  emb := D.emb
  isClosedImmersion_emb := D.isClosedImmersion_emb
  emb_comp := D.comp_eq
  ambientSeq :=
    (A k D.ambient D.ambientStruct (ker D.emb) D.nonzeroOnComponents_ker
      ([] : List D.ambient.IdealSheafData) D.sncEmpty).toSequenceOfBlowups


theorem ambientBlowups_eq_toSequenceOfBlowups :
    (D.toEmbeddedBlowupSequence A).ambientSeq =
      (A k D.ambient D.ambientStruct (ker D.emb) D.nonzeroOnComponents_ker
        ([] : List D.ambient.IdealSheafData) D.sncEmpty).toSequenceOfBlowups := rfl
end

end EmbeddingDatum

section
variable (hemb : AffineEmbedsIntoAffineSpace) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
def affineSpaceEmbeddingDatum
    (k : Type) [Field k] [CharZero k] (Y : Sch) [IsAffine Y]
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY] :
    EmbeddingDatum k Y pY where
  ambient := affineSpaceIndexedBy k $ ULift $ Fin (hemb k Y pY).choose
  ambientStruct := affineSpaceIndexedByToSpec k $ ULift $ Fin (hemb k Y pY).choose
  emb := (hemb k Y pY).choose_spec.choose
  isAffine_ambient := inferInstance
  smooth_ambientStruct := hsm k $ (hemb k Y pY).choose
  locallyOfFiniteType_ambientStruct :=
    locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift k $ (hemb k Y pY).choose
  quasiCompact_ambientStruct :=
    quasiCompact_affineSpaceIndexedByToSpec_ulift k $ (hemb k Y pY).choose
  isClosedImmersion_emb := (hemb k Y pY).choose_spec.choose_spec.1
  nonzeroOnComponents_ker := (hemb k Y pY).choose_spec.choose_spec.2.1
  comp_eq := (hemb k Y pY).choose_spec.choose_spec.2.2
  sncEmpty := hsnc k $ (hemb k Y pY).choose

def affineSpaceEmbeddingChoice :
    EmbeddingChoice := by
  intro k _ _ Y pY _ _ _ _
  exact affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY

theorem affineSpaceEmbeddingChoice_eq_affineSpaceEmbeddingDatum
    (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] :
    affineSpaceEmbeddingChoice hemb hsnc hsm k Y pY = affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY := rfl
end

section
variable (A : PrincipalizationAlgorithm)
def TransitionsAreBlowupsForEmbeddings : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [QuasiCompact pY] [IsReduced Y]
    [IsAffine Y] (D : EmbeddingDatum k Y pY),
    (D.toEmbeddedBlowupSequence A).TransitionsAreBlowups

theorem affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence (hemb : AffineEmbedsIntoAffineSpace)
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace) (hsm : AffineSpaceIsSmooth)
    (k : Type) [Field k] [CharZero k] (Y : Sch) [IsAffine Y]
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY] :
    (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A =
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence := rfl

section
variable (h : TransitionsAreBlowupsForEmbeddings A)
def embeddedResolutionRuleOfPrincipalization : EmbeddedResolutionRule := by
  intro k _ _ Y pY _ _ _ _ D
  exact (D.toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso $ h k Y pY D

theorem embeddedResolutionRuleOfPrincipalization_apply
    (k : Type) [Field k] [CharZero k] (Y : Sch)
    (pY : Y ⟶ Sp k) [LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D : EmbeddingDatum k Y pY) :
    embeddedResolutionRuleOfPrincipalization A h k Y pY D = (D.toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso (h k Y pY D) := rfl

end
end

end FunctorialResolution.EmbeddedResolution

end
end
