import Mathlib
import Bundle00
import Bundle01
import Bundle02
noncomputable section
open CategoryTheory AlgebraicGeometry
open Set (InjOn disjoint_iff_inter_eq_empty disjoint_left eq_empty_of_subset_empty eq_univ_of_forall eq_univ_of_univ_subset image_congr image_empty image_image image_injective image_mono image_singleton inter_subset_right mem_compl_iff mem_iInter mem_iUnion mem_image_of_mem mem_range mem_range_self mem_singleton mem_singleton_iff mem_union mem_univ not_nonempty_iff_eq_empty not_subset preimage preimage_mono range sUnion_eq_biUnion sdiff_subset singleton_subset_iff univ)
open TopologicalSpace.Opens (coe_top isBasis_iff_nbhd isOpen mem_iSup)
open Finset (card_empty card_image_of_injective card_le_card_of_injOn card_univ coe_empty coe_image coe_map coe_singleton eq_empty_or_nonempty le_sup map_singleton mem_coe sum_add_distrib sum_congr sum_eq_zero)
open Ideal (eq_top_iff_one eq_top_of_isUnit_mem map_le_iff_le_comap map_map map_span mem_bot mem_comap mem_map_of_mem mem_span_singleton' mem_span_singleton_self mul_mem_left mul_mem_mul mul_mem_right radical_mono span span_empty span_eq span_le span_singleton_mul_span_singleton span_singleton_one sub_mem subset_span toCotangent toCotangent_eq_zero)
open WithBot (bot_add coe_add coe_le_coe coe_lt_coe coe_mul coe_natCast coe_ne_bot mul_bot ne_bot_iff_exists recBotCoe)
open FunctorialResolution.Blowup (exceptionalIdeal strictTransform)
open Nat (add_sub_cancel' cast_one cast_zero le_succ lt_one_iff lt_succ_iff lt_succ_self mono_cast not_lt_zero sub_le succ_le_succ)
open List (eraseIdx filter_append get getElem_cons_zero getElem_eraseIdx getElem_map length length_cons length_eraseIdx_add_one length_map map_nil mem_iff_getElem mem_map)
open Scheme.IdealSheafData (comap comap_comp comap_id comap_ideal_eq_map_appLE comap_map_le comap_mono comap_mul comap_ofIdealTop eq_top_iff_support_eq_empty gc ideal_ofIdeals_le le_def le_map_comap le_ofIdeals_iff le_radical map_bot map_ideal_basicOpen map_mono mem_support_iff_of_mem notMem_support_of_comap_ι_eq_top ofIdealTop ofIdealTop_ideal ofIdealTop_ideal_top ofIdealTop_mul ofIdeals radical_ideal subscheme subschemeMap subschemeι support support_mul support_top vanishingIdeal vanishingIdeal_support)
open MvPolynomial (X_injective aeval aeval_C aeval_X algebraMap_eq finSuccEquiv isEmptyRingEquiv renameEquiv renameEquiv_apply ringHom_ext)
open TensorProduct (add_tmul induction_on rid rid_tmul smul_tmul smul_tmul' tmul_sum tmul_zero zero_tmul)
open Algebra.FiniteType (iff_quotient_mvPolynomial'' of_restrictScalars_finiteType)
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates (algebraMap_X_inl algebraMap_coord algebraMap_eq_sumEval basisKaehler basisKaehler_apply eq_sum_smul_partialDeriv formallyEtale_aeval_of_isUnit_det formallyEtale_trans partialDeriv partialDeriv_apply partialDeriv_coord_of_ne partialDeriv_coord_self sumEval sumEvalAlgebra)
open Fintype (card_fin ofFinite sum_bijective)
open KaehlerDifferential (map_D)
open Equiv (sumCongr ulift)
open IsOpenImmersion (isoOfRangeEq isoOfRangeEq_hom_fac)
open ENat (natCast_toNat ne_top_iff_exists)
open Submodule (ker_mkQ liftQ liftQ_apply mem_top mkQ_apply range_subtype subtype)
open Classical (choose_spec propDecidable)
open Function (Bijective Exact Injective update update_apply update_of_ne update_self)
open Scheme (GSpecIso IdealSheafData basicOpen isBasis_affineOpens mem_zeroLocus_iff preimage_basicOpen presheaf_map_eq_of_parallel)
open LinearMap (exact_iff lTensor lTensor_tmul lsmul toSpanSingleton toSpanSingleton_apply)
open FunctorialResolution.EmbeddedResolution.EtaleChart (coordIdeal_eq_comap_coordSubspaceIdeal coordRingHom_C coordRingHom_X coord_def coord_restrict ideal_eq_span_coord ofCoords ofCoords_map)
open IsLocalRing (ResidueField maximalIdeal mem_maximalIdeal residue residue_eq_zero_iff)
open CommRingCat (hom_comp hom_id hom_ofHom ofHom)
open ULift (down up)
open Limits.pullback (fst snd)
open Scheme.Hom (appIso_hom' appLE appLE_comp_appLE appLE_map imageι isClosedEmbedding ker ker_comp map_appLE pre preimage_top support_ker toImage toImage_imageι)
open Category (assoc comp_id id_comp)
open Algebra (FinitePresentation FiniteType FormallyEtale FormallySmooth smul_def)
open Fin (castAdd castAddEmb castAddEmb_apply)
open FunctorialResolution.EmbeddedResolution (closure_inter_open_eq comap_io_eq_top_of_disjoint isGenericPoint_preimage_of_isInducing isIrreducible_inter_open isIrreducible_preimage_of_isEmbedding mem_orderAtLeastLocus_iff orderAt orderAt_comap_of_isOpenImmersion orderAt_vanishingIdeal_eq_one sectionsAlgebraMap_restrict_apply)
open RingHom (Flat coe_coe coe_comp comp_apply mem_ker)
open Option.some (inj)
open IsPullback (of_hasPullback of_right)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (blowupMorphism_eq_transitionMap projectionToBase_def transitionMap_comp_projectionToBase transitionMap_def)
open Module.Basis (det_apply repr_self repr_sum_self sum_repr toMatrix_apply)
open MorphismProperty.IsStableUnderBaseChange (of_isPullback)
open IsScalarTower (of_algebraMap_eq)
open Submonoid (mem_powers powers)
open Subtype (val)
open SetLike (coe_injective coe_subset_coe)
open Set.Finite (isOpen_biInter subset)
open HomogeneousLocalization (Away)
section
open Opposite TopologicalSpace
open Limits (pullback)
open PrimeSpectrum (asIdeal)


namespace FunctorialResolution.EmbeddedResolution

theorem formallySmooth_of_etaleChart {X1 : Sch} {k1_ : Type} [Field k1_]
    {p1_} {U1_} {m1}
    [Algebra k1_ (X1.sec U1_)]
    (hk : algebraMap k1_ (X1.sec U1_) = sectionsAlgebraMap k1_ p1_ U1_)
    (hU : IsAffineOpen U1_) (c : EtaleChart p1_ U1_ m1) :
    FormallySmooth k1_ (X1.sec U1_) := by
  let _c0 := MvPolynomial (ULift $ Fin m1) k1_
  let instc := c.algebra
  have instT : IsScalarTower k1_ _c0 U1_.sec :=
    of_algebraMap_eq fun a => by
      rw [hk, algebraMap_eq]
      exact sy_ $ c.coordRingHom_C a
  have instFormallyEtale :=
    c.algebra_formallyEtale hU
  exact m139 k1_ _c0 $ xSec X1 U1_

theorem notMem_support_of_restrictIdeal_eq_top_of_mem {Y : Sch} (I : ISD Y)
    {U : Opn Y} (h : restrictIdeal I U = ⊤) {y} (hyU : y ∈ U) : y ∉ support I := by
  intro hy
  let _a0 := (⟨y, hyU⟩ : ↥U)
  have h1 : _a0 ∈ support (comap I U.i) := by
    rwa [m19]
  rw [← restrictIdeal_eq_comap_io, h, support_top] at h1
  have h2 : _a0 ∈ ((⊥) : Set ↥U) := h1
  simp at h2

theorem exists_isUnit_mul_of_span_singleton_eq {R : Type} [CommRing R] {y z}
    (hy : y ∈ nonZeroDivisors R) (hsp : span {z} = span {y}) :
    ∃ u, IsUnit u ∧ z = u * y := by
  have hz : z ∈ span {y} := by
    rw [← hsp]
    exact mem_span_singleton_self z
  have hy' : y ∈ span {z} := by
    rw [hsp]
    exact mem_span_singleton_self y
  obtain ⟨u, hu⟩ := mp_ mem_span_singleton' hz
  obtain ⟨b, hb⟩ := mp_ mem_span_singleton' hy'
  have hsub : (b * u - 1) * y = 0 := by
    rw [sub_mul, one_mul, mul_assoc, hu, hb, sub_self]
  have h1 := (an2 $ mp_ mem_nonZeroDivisors_iff hy) _ hsub
  have h2 : b * u = 1 := by
    rwa [sub_eq_zero] at h1
  have h3 := h2
  rw [← mul_comm] at h3
  exact ⟨u, ⟨⟨u, b, h3, h2⟩, rfl⟩, sy_ hu⟩

theorem basisKaehler_repr_kaehlerMap (k0 : Type) [CommRing k0] (io0 : Type) [Fintype io0]
    [DecidableEq io0] (S : Type) [CommRing S] (S' : Type) [CommRing S']
    [Algebra k0 S] [Algebra k0 S'] [Algebra (MvPolynomial io0 k0) S]
    [Algebra (MvPolynomial io0 k0) S'] [Algebra S S']
    [IsScalarTower k0 (MvPolynomial io0 k0) S] [IsScalarTower k0 (MvPolynomial io0 k0) S']
    [IsScalarTower k0 S S'] [IsScalarTower (MvPolynomial io0 k0) S S']
    [FormallyEtale (MvPolynomial io0 k0) S]
    [FormallyEtale (MvPolynomial io0 k0) S']
    om_ i :
    (basisKaehler k0 io0 S').repr (KaehlerDifferential.map k0 k0 S S' om_) i
      = algebraMap S S' ((basisKaehler k0 io0 S).repr om_ i) := by
  have hb : ∀ j,
      m132 k0 k0 S S' (basisKaehler k0 io0 S j)
        = basisKaehler k0 io0 S' j := by
    intro j
    simp [basisKaehler_apply, map_D,
      algebraMap_coord]
  let _m0 := basisKaehler k0 io0 S
  have key : m132 k0 k0 S S' om_
      = ∑ j : io0, algebraMap S S' (_m0.repr om_ j) •
        basisKaehler k0 io0 S' j := by
    conv_lhs => rw [(_m0.sum_repr om_).symm]
    rw [map_sum]
    refine sum_congr rfl ?_
    intro j _
    rw [map_smul, hb j]
    exact algebra_compatible_smul S' (_m0.repr om_ j)
      (basisKaehler k0 io0 S' j)
  rw [key, repr_sum_self]

variable {X : Sch} {k : Type} [Field k] {p : X ⟶ Sp k}
  [Smooth p] {V : Opn X} {n : ℕ}

section
variable (hV : IsAffineOpen V) (c : EtaleChart p V n)
include hV c
theorem exists_etaleChart_coord_eq_of_isUnit_jacobianDet (w : UFin n → (X.sec V)) :
    letI : Algebra k (X.sec V) := sectionsAlgebra k p V
    letI := c.algebra
    haveI := c.isScalarTower
    haveI :=
      c.algebra_formallyEtale hV
    IsUnit ((basisKaehler k (UFin n) V.sec).det
        fun i => m13 k V.sec $ w i) →
      ∃ c' : EtaleChart p V n, ∀ j, c'.coord j = w (up j) := by
  intro hdet0
  let instk := sectionsAlgebra k p V
  let instc := c.algebra
  have instT := c.isScalarTower
  have instFormallyEtale :=
    c.algebra_formallyEtale hV
  have hk := algebraMap_sectionsAlgebra k p V
  have instFS := formallySmooth_of_etaleChart hk hV c
  obtain ⟨f, hfC, hfX, hfEtale⟩ :
      ∃ f : MvU n k →+* opSec V,
        (∀ a, f (m8 a) = sectionsAlgebraMap k p V a) ∧
        (∀ i, f (m7 i) = w i) ∧
        @FormallyEtale (MvU n k) V.sec _ _
          f.toAlgebra := by
    refine ⟨(aeval (R := k) w).toRingHom, fun a => ?_, fun i => ?_, formallyEtale_aeval_of_isUnit_det (basisKaehler k (UFin n) V.sec) w hdet0⟩
    show aeval w (m8 a) = sectionsAlgebraMap k p V a
    rw [aeval_C, hk]
    show aeval w (m7 i) = w i
    rw [aeval_X]
  exact exists_etaleChart_coord_eq p hV w f hfC hfX
    (ringHom_etale_of_formallyEtale p hV f hfC hfEtale)

section
variable {x : X} (hx : x ∈ V)
include hx
theorem exists_etaleChart_restrict_coord_eq_of_jacobianDet_notMem
    (w : UFin n → (X.sec V)) :
    letI : Algebra k (X.sec V) := sectionsAlgebra k p V
    letI := c.algebra
    haveI := c.isScalarTower
    haveI :=
      c.algebra_formallyEtale hV
    ((basisKaehler k (UFin n) V.sec).det
        fun i : UFin n => m13 k V.sec $ w i) ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal →
      ∃ (V' : Opn X) (_ : IsAffineOpen V') (hV'V : V' ≤ V) (_ : x ∈ V')
        (c' : EtaleChart p V' n),
        ∀ j,
          c'.coord j = (pMap X (homOfLE hV'V).op).hom (w $ up j) := by
  intro hg0
  let instk := sectionsAlgebra k p V
  let instc := c.algebra
  have instT := c.isScalarTower
  have instFormallyEtale :=
    c.algebra_formallyEtale hV
  obtain ⟨g, hgd⟩ : ∃ g,
      g = (basisKaehler k (UFin n) V.sec).det
        fun i => m13 k V.sec $ w i := ⟨_, rfl⟩
  have hg := hg0
  rw [← hgd] at hg
  have hle := X.basicOpen_le g
  have hVg := hV.basicOpen g
  let instk' := sectionsAlgebra k p $ bOpn X g
  let instAlg :=
    (pMap X (homOfLE hle).op).hom.toAlgebra
  have halg : ∀ z,
      algebraMap V.sec Γ(X, bOpn X g) z =
        (pMap X (homOfLE hle).op).hom z := fun _ => rfl
  have instScalarTower : IsScalarTower k V.sec Γ(X, bOpn X g) :=
    of_algebraMap_eq fun a => by
      rw [halg]
      exact sy_ $ sectionsAlgebraMap_restrict_apply k p hle a
  have instLoc : IsLocalization (powers g) Γ(X, bOpn X g) :=
    hV.isLocalization_basicOpen g
  have hunit : IsUnit $ algebraMap V.sec Γ(X, bOpn X g)
      ((basisKaehler k (UFin n) V.sec).det
        fun i => m13 k V.sec $ w i) := by
    rw [← hgd]
    exact IsLocalization.map_units (M := powers g) Γ(X, bOpn X g)
      ⟨g, mem_powers g⟩
  obtain ⟨e, he⟩ := exists_basis_isUnit_det_of_isLocalization (k := k)
    (S' := Γ(X, bOpn X g)) (powers g) w hunit
  have instFS :=
    formallySmooth_of_etaleChart (algebraMap_sectionsAlgebra k p $ bOpn X g) hVg
      (c.restrict hle)
  obtain ⟨f, hfC, hfX, hfEtale⟩ :
      ∃ f : MvU n k →+* Γ(X, bOpn X g),
        (∀ a, f (m8 a) = sectionsAlgebraMap k p (bOpn X g) a) ∧
        (∀ i, f (m7 i) =
          algebraMap V.sec Γ(X, bOpn X g) (w i)) ∧
        @FormallyEtale (MvU n k) Γ(X, bOpn X g) _ _
          f.toAlgebra := by
    refine ⟨(aeval (R := k)
      (fun i =>
        algebraMap V.sec Γ(X, bOpn X g) $ w i)).toRingHom,
      fun a => ?_, fun i => ?_, formallyEtale_aeval_of_isUnit_det e (fun i => algebraMap V.sec Γ(X, bOpn X g) $ w i) he⟩
    show aeval
      (fun i => algebraMap V.sec Γ(X, bOpn X g) $ w i)
      (m8 a) = sectionsAlgebraMap k p (bOpn X g) a
    rw [aeval_C, algebraMap_sectionsAlgebra k p $ bOpn X g]
    show aeval
      (fun i => algebraMap V.sec Γ(X, bOpn X g) $ w i)
      (m7 i) = algebraMap V.sec Γ(X, bOpn X g) (w i)
    rw [aeval_X]
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p hVg
    (fun i => algebraMap V.sec Γ(X, bOpn X g) $ w i) f hfC hfX
    (ringHom_etale_of_formallyEtale p hVg f hfC hfEtale)
  exact ⟨bOpn X g, hVg, hle, mem_basicOpen_of_notMem_primeIdealOf hV hx g hg, c', fun j => tr_ (hc' j) $ halg _⟩

theorem exists_etaleChart_update_coord_of_partialDeriv_notMem (j1 : Fin n)
    (x' : (X.sec V)) :
    letI : Algebra k (X.sec V) := sectionsAlgebra k p V
    letI := c.algebra
    haveI := c.isScalarTower
    haveI :=
      c.algebra_formallyEtale hV
    partialDeriv k (UFin n) V.sec (up j1) x' ∉
        asIdeal (hV.primeIdealOf ⟨x, hx⟩) →
      ∃ (V' : Opn X) (_ : IsAffineOpen V') (hV'V : V' ≤ V) (_ : x ∈ V')
        (c' : EtaleChart p V' n),
        c'.coord j1 = (pMap X (homOfLE hV'V).op).hom x' ∧
          ∀ j : Fin n, j ≠ j1 →
            c'.coord j = (pMap X (homOfLE hV'V).op).hom (c.coord j) := by
  intro hpd0
  let instk := sectionsAlgebra k p V
  let instc := c.algebra
  have instT := c.isScalarTower
  have instFormallyEtale :=
    c.algebra_formallyEtale hV
  obtain ⟨w, hwj, hwne, hwupd⟩ : ∃ w : UFin n → xSec X V,
      w (up j1) = x' ∧
      (∀ j : Fin n, j ≠ j1 → w (up j) = c.coord j) ∧
      (fun i : UFin n => m13 k V.sec $ w i) =
        update (basisKaehler k (UFin n) V.sec)
          (up j1) (m13 k V.sec x') := by
    refine ⟨update (fun i : UFin n => c.coord i.down) (up j1) x',
      ?_, fun j hjne => ?_, ?_⟩
    rw [update_apply]
    exact if_pos rfl
    rw [update_apply]
    exact if_neg fun hcon : up j = up j1 => hjne $ congrArg down hcon
    funext i
    rw [update_apply, update_apply]
    by_cases hi : i = up j1
    rw [if_pos hi, if_pos hi]
    rw [if_neg hi, if_neg hi]
    exact sy_ $ basisKaehler_apply_eq_D_coord c (algebraMap_sectionsAlgebra k p V) (c.algebraMap_eq_coordRingHom) i.down
  have hdet := hpd0
  rw [partialDeriv_apply, ← det_update_eq_repr, ← hwupd] at hdet
  obtain ⟨V', hV'aff, hle, hxV', c', hc'⟩ :=
    exists_etaleChart_restrict_coord_eq_of_jacobianDet_notMem hV c hx w hdet
  refine ⟨V', hV'aff, hle, hxV', c', ?_, fun j hjne => ?_⟩
  rw [hc' j1, hwj]
  rw [hc' j, hwne j hjne]
end

def chartPartialDeriv (j : Fin n)
    (f : (X.sec V)) : (X.sec V) :=
  letI _instk : Algebra k (X.sec V) := sectionsAlgebra k p V
  letI _instc : Algebra (MvU n k) (X.sec V) := c.algebra
  haveI _instT : IsScalarTower k (MvU n k) (X.sec V) := c.isScalarTower
  haveI _instFormallyEtale : FormallyEtale (MvU n k) (X.sec V) :=
    c.algebra_formallyEtale hV
  partialDeriv k (UFin n) (X.sec V) (up j) f
end

private theorem derivation_sum_apply {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type} [DecidableEq ι] (s : Finset ι) (D : ι → Derivation R A A) (a : A) :
    (∑ i ∈ s, D i) a = ∑ i ∈ s, D i a :=by simp_all
omit [Smooth p] in
theorem chartPartialDeriv_chainRule {W} (hW : IsAffineOpen W) {n1_ n2_}
    (c1_ : EtaleChart p W n1_) (c2_ : EtaleChart p W n2_) j (f : (X.sec W)) :
    chartPartialDeriv hW c2_ j f =
      ∑ i : Fin n1_, chartPartialDeriv hW c2_ j (c1_.coord i) * chartPartialDeriv hW c1_ i f := by
  classical
  let instk := sectionsAlgebra k p W
  obtain ⟨D, hD⟩ : ∃ D : Derivation k W.sec W.sec,
      ∀ z, D z = chartPartialDeriv hW c2_ j z := by
    let instc2 := c2_.algebra
    have instT2 :=
      c2_.isScalarTower
    have instFE2_ :=
      c2_.algebra_formallyEtale hW
    exact ⟨partialDeriv k (ULift $ Fin n2_) W.sec $ up j,
      fun _ => rfl⟩
  let _s0 := ULift $ Fin n1_
  let instc1 := c1_.algebra
  have instT1_ :=
    c1_.isScalarTower
  have instFE1_ :=
    c1_.algebra_formallyEtale hW
  let _a0 := ULift $ Fin n1_
  have hcoord : ∀ i : _a0,
      p10 k _s0 W.sec i = c1_.coord i.down := by
    rintro ⟨i⟩
    exact c1_.etaleCoordinates_coord i
  have hpd : ∀ i : _a0,
      partialDeriv k _s0 W.sec i f =
        chartPartialDeriv hW c1_ i.down f := by
    rintro ⟨i⟩
    rfl
  have happ : D f = ∑ i : _a0,
      D (p10 k _s0 W.sec i) *
        partialDeriv k _s0 W.sec i f := by
    conv_lhs => rw [eq_sum_smul_partialDeriv k _s0 W.sec D]
    rw [derivation_sum_apply]
    refine sum_congr rfl fun i _ => ?_
    simp
  have hbij : Bijective fun i : _a0 => i.down := by
    constructor
    rintro ⟨a⟩ ⟨b⟩ hab
    exact congrArg up hab
    intro b
    exact ⟨up b, rfl⟩
  rw [← hD f, happ]
  refine sum_bijective (fun i : _a0 => i.down) hbij _ _ ?_
  intro i
  rw [hcoord i, hpd i, hD]

omit [Smooth p] in
theorem chartPartialDeriv_coord_self (hV : IsAffineOpen V) (c : EtaleChart p V n)
    j : chartPartialDeriv hV c j (c.coord j) = 1 := by
  let instk := sectionsAlgebra k p V
  let instc := c.algebra
  have instT := c.isScalarTower
  have instFormallyEtale :=
    c.algebra_formallyEtale hV
  show partialDeriv k (UFin n) V.sec (up j) (c.coord j) = 1
  rw [← c.etaleCoordinates_coord j]
  exact partialDeriv_coord_self k (UFin n) V.sec $ up j

omit [Smooth p] in
theorem chartPartialDeriv_coord_of_ne (hV : IsAffineOpen V) (c : EtaleChart p V n)
    j i (h : j ≠ i) : chartPartialDeriv hV c j (c.coord i) = 0 := by
  let instk := sectionsAlgebra k p V
  let instc := c.algebra
  have instT := c.isScalarTower
  have instFormallyEtale :=
    c.algebra_formallyEtale hV
  show partialDeriv k (UFin n) V.sec (up j) (c.coord i) = 0
  rw [← c.etaleCoordinates_coord i]
  refine partialDeriv_coord_of_ne k (UFin n) V.sec
    (up j) (up i) ?_
  intro hcon
  exact h $ congrArg down hcon

omit [Smooth p] in
theorem chartPartialDeriv_coord (hV : IsAffineOpen V) (c : EtaleChart p V n)
    j i :
    chartPartialDeriv hV c j (c.coord i) = if i = j then (1 : (X.sec V)) else 0 := by
  by_cases h : i = j
  rw [if_pos h, ← h]
  exact chartPartialDeriv_coord_self hV c i
  rw [if_neg h]
  exact chartPartialDeriv_coord_of_ne hV c j i fun hc => h hc.symm

omit [Smooth p] in
theorem chartPartialDeriv_add_algebraMap_mul (hV : IsAffineOpen V) (c : EtaleChart p V n)
    j a b t :
    chartPartialDeriv hV c j (a + sectionsAlgebraMap k p V t * b) =
      chartPartialDeriv hV c j a + sectionsAlgebraMap k p V t * chartPartialDeriv hV c j b := by
  let _c0 := UFin n
  let instk := sectionsAlgebra k p V
  let instc := c.algebra
  have instT := c.isScalarTower
  have instFormallyEtale :=
    c.algebra_formallyEtale hV
  have h3 : partialDeriv k _c0 V.sec (up j)
      (sectionsAlgebraMap k p V t) = 0 := by
    rw [← algebraMap_sectionsAlgebra k p V]
    simp
  show partialDeriv k _c0 V.sec (up j)
      (a + sectionsAlgebraMap k p V t * b)
    = partialDeriv k _c0 V.sec (up j) a
      + sectionsAlgebraMap k p V t *
        partialDeriv k _c0 V.sec (up j) b
  simp [Derivation.leibniz, h3]

omit [Smooth p] in
theorem chartPartialDeriv_mul (hV : IsAffineOpen V) (c : EtaleChart p V n) j
    a b :
    chartPartialDeriv hV c j (a * b) =
      a * chartPartialDeriv hV c j b + b * chartPartialDeriv hV c j a := by
  let _c0 := UFin n
  let instk := sectionsAlgebra k p V
  let instc := c.algebra
  have instT := c.isScalarTower
  have instFormallyEtale :=
    c.algebra_formallyEtale hV
  show partialDeriv k _c0 V.sec (up j) (a * b)
    = a * partialDeriv k _c0 V.sec (up j) b
      + b * partialDeriv k _c0 V.sec (up j) a
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

omit [Smooth p] in
theorem chartPartialDeriv_chainRule_of_same_rank (hV : IsAffineOpen V)
    (c c' : EtaleChart p V n) j f :
    chartPartialDeriv hV c' j f =
      ∑ i : Fin n, chartPartialDeriv hV c' j (c.coord i) * chartPartialDeriv hV c i f :=
  chartPartialDeriv_chainRule hV c c' j f

theorem exists_etaleChart_coord_add_smul_chartPartialDeriv (hV : IsAffineOpen V)
    (c : EtaleChart p V n) j1 j2_ (hj : j1 ≠ j2_) t :
    ∃ c' : EtaleChart p V n,
      c'.coord j2_ = c.coord j2_ + sectionsAlgebraMap k p V t * c.coord j1 ∧
      (∀ j, j ≠ j2_ → c'.coord j = c.coord j) ∧
      (∀ f : (X.sec V),
        chartPartialDeriv hV c' j1 f =
          chartPartialDeriv hV c j1 f -
            sectionsAlgebraMap k p V t * chartPartialDeriv hV c j2_ f) ∧
      (∀ j (f : (X.sec V)), j ≠ j1 →
        chartPartialDeriv hV c' j f = chartPartialDeriv hV c j f) := by
  classical
  obtain ⟨c', h1, h2⟩ : ∃ c' : EtaleChart p V n, c'.coord j2_ = c.coord j2_ + sectionsAlgebraMap k p V t * c.coord j1 ∧ ∀ j, j ≠ j2_ → c'.coord j = c.coord j := by
    let instk := sectionsAlgebra k p V
    let instc := c.algebra
    have instT := c.isScalarTower
    have instFormallyEtale :=
      c.algebra_formallyEtale hV
    have hk := algebraMap_sectionsAlgebra k p V
    have hcoord :=
      c.etaleCoordinates_coord
    have h1 : partialDeriv k (UFin n) V.sec (up j2_)
        (c.coord j2_) = 1 := by
      rw [← hcoord j2_]
      exact partialDeriv_coord_self k (UFin n) V.sec $ up j2_
    have h2 : partialDeriv k (UFin n) V.sec (up j2_)
        (c.coord j1) = 0 := by
      rw [← hcoord j1]
      refine partialDeriv_coord_of_ne k (UFin n) V.sec
        (up j2_) (up j1) ?_
      intro hcon
      exact hj (congrArg down hcon).symm
    have h3 : partialDeriv k (UFin n) V.sec (up j2_)
        (sectionsAlgebraMap k p V t) = 0 := by
      rw [← hk]
      simp
    have hpd : partialDeriv k (UFin n) V.sec (up j2_)
        (c.coord j2_ + sectionsAlgebraMap k p V t * c.coord j1) = 1 := by simp_all
    let _a1 := basisKaehler k (UFin n) $ xSec X V
    obtain ⟨w, hwj, hwne, hwupd⟩ : ∃ w : UFin n → xSec X V,
        w (up j2_) = c.coord j2_ + sectionsAlgebraMap k p V t * c.coord j1 ∧
        (∀ j : Fin n, j ≠ j2_ → w (up j) = c.coord j) ∧
        (fun i : UFin n => m13 k V.sec $ w i) =
          update (_a1)
            (up j2_)
            (m13 k V.sec
              (c.coord j2_ + sectionsAlgebraMap k p V t * c.coord j1)) := by
      refine ⟨update (fun i : UFin n => c.coord i.down) (up j2_)
        (c.coord j2_ + sectionsAlgebraMap k p V t * c.coord j1), ?_, fun j hjne => ?_, ?_⟩
      simp_all
      simp_all
      funext i
      rw [update_apply, update_apply]
      by_cases hi : i = up j2_
      rw [if_pos hi, if_pos hi]
      rw [if_neg hi, if_neg hi]
      exact sy_ $ basisKaehler_apply_eq_D_coord c hk (c.algebraMap_eq_coordRingHom) i.down
    have hdet : IsUnit $ _a1.det
        fun i => m13 k V.sec $ w i := by
      rw [hwupd, det_update_eq_repr, ← partialDeriv_apply, hpd]
      exact isUnit_one
    obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq_of_isUnit_jacobianDet hV c w hdet
    refine ⟨c', ?_, fun j hjne => ?_⟩
    simp_all
    simp_all
  have hB : ∀ j, chartPartialDeriv hV c' j (c.coord j2_) =
      chartPartialDeriv hV c' j (c'.coord j2_) -
        sectionsAlgebraMap k p V t * chartPartialDeriv hV c' j (c.coord j1) := by
    intro j
    have happ : chartPartialDeriv hV c' j (c'.coord j2_) =
        chartPartialDeriv hV c' j (c.coord j2_) +
          sectionsAlgebraMap k p V t * chartPartialDeriv hV c' j (c.coord j1) := by
      rw [h1]
      exact chartPartialDeriv_add_algebraMap_mul hV c' j (c.coord j2_) (c.coord j1) t
    exact eq_sub_of_add_eq happ.symm
  have hgen : ∀ j i, chartPartialDeriv hV c' j (c.coord i) =
      (if i = j then 1 else 0) -
        (if i = j2_ then (if j = j1 then sectionsAlgebraMap k p V t else 0) else 0) := by
    intro j i
    by_cases hi : i = j2_
    rw [hi, hB j, ← h2 j1 hj, chartPartialDeriv_coord hV c' j j2_, chartPartialDeriv_coord hV c' j j1]
    by_cases hjj : j = j1
    simp [hjj]
    simp [hjj, m113 hjj]
    rw [← h2 i hi, chartPartialDeriv_coord hV c' j i, if_neg hi, sub_zero]
  refine ⟨c', h1, h2, ?_, ?_⟩
  intro f
  rw [chartPartialDeriv_chainRule_of_same_rank hV c c' j1 f]
  have hterm : ∀ i,
      chartPartialDeriv hV c' j1 (c.coord i) * chartPartialDeriv hV c i f =
        (if i = j1 then chartPartialDeriv hV c j1 f else 0) +
          (if i = j2_ then
            -(sectionsAlgebraMap k p V t * chartPartialDeriv hV c j2_ f) else 0) := by
    intro i
    rw [hgen j1 i]
    by_cases hi1 : i = j1
    simp_all
    by_cases hi2 : i = j2_
    simp_all
    simp_all
  simp only [hterm]
  simp [sum_add_distrib, sub_eq_add_neg]
  intro j f hjne
  rw [chartPartialDeriv_chainRule_of_same_rank hV c c' j f]
  have hterm : ∀ i,
      chartPartialDeriv hV c' j (c.coord i) * chartPartialDeriv hV c i f =
        (if i = j then chartPartialDeriv hV c j f else 0) := by simp_all
  simp only [hterm]
  simp

omit [Smooth p] in
theorem etaleChart_restrict_coordRingHom (c : EtaleChart p V n) {W}
    (hWV : W ≤ V) :
    (c.restrict hWV).coordRingHom =
      ((X.presheaf.map (homOfLE hWV).op).hom).comp c.coordRingHom := by
  refine ringHom_ext (fun a => ?_) fun i => ?_
  rw [comp_apply, coordRingHom_C, coordRingHom_C,
    sectionsAlgebraMap_restrict_apply]
  obtain ⟨i⟩ := i
  rw [comp_apply, coordRingHom_X, coordRingHom_X]
  exact coord_restrict c hWV i

omit [Smooth p] in
theorem map_chartPartialDeriv_restrict (hV : IsAffineOpen V) (c : EtaleChart p V n)
    {W} (hW : IsAffineOpen W) (hWV : W ≤ V) j f :
    (X.presheaf.map (homOfLE hWV).op).hom (chartPartialDeriv hV c j f)
      = chartPartialDeriv hW (c.restrict hWV) j
          ((X.presheaf.map (homOfLE hWV).op).hom f) := by
  let _c0 := UFin n
  let _c1 := pMap X (homOfLE hWV).op
  let instkV := sectionsAlgebra k p V
  let instkW := sectionsAlgebra k p W
  let instcV := c.algebra
  let _a2 := c.restrict hWV
  let instcW :=
    _a2.algebra
  let instVW :=
    _c1.hom.toAlgebra
  have instScalarTowerMvPolynomial :=
    c.isScalarTower
  have instTW :=
    _a2.isScalarTower
  have instFEV :=
    c.algebra_formallyEtale hV
  have instFEW :=
    _a2.algebra_formallyEtale hW
  have halg : ∀ z,
      algebraMap V.sec W.sec z = _c1.hom z := fun _ => rfl
  have instTkVW : IsScalarTower k V.sec W.sec :=
    of_algebraMap_eq fun a => by
      rw [halg]
      exact sy_ $ sectionsAlgebraMap_restrict_apply k p hWV a
  have instTPVW : IsScalarTower (MvPolynomial _c0 k) V.sec W.sec :=
    of_algebraMap_eq fun z => by
      rw [halg]
      show _a2.coordRingHom z
        = _c1.hom (c.coordRingHom z)
      rw [etaleChart_restrict_coordRingHom c hWV]
      rfl
  let _a3 := m13 k V.sec f
  let _a0 := (basisKaehler k _c0 V.sec).repr _a3 $ up j
  let _a1 := basisKaehler k _c0 $ X.sec W
  have key : algebraMap V.sec W.sec
      _a0
      = _a1.repr
        (m13 k W.sec $ algebraMap V.sec W.sec f) (up j) := by
    rw [← map_D k k V.sec W.sec]
    exact sy_ $ basisKaehler_repr_kaehlerMap k _c0 V.sec W.sec
      _a3 $ up j
  have hl : chartPartialDeriv hV c j f
      = _a0 := rfl
  have hr : chartPartialDeriv hW (c.restrict hWV) j
      (_c1.hom f)
      = _a1.repr
        (m13 k W.sec $ _c1.hom f)
        (up j) := rfl
  rwa [hl, hr, ← halg]

theorem map_mem_primeIdealOf_of_mem_of_le {V1 W1} (hV1_ : IsAffineOpen V1)
    (hW1_ : IsAffineOpen W1) (hle : W1 ≤ V1) {y} (hyV : y ∈ V1) (hyW : y ∈ W1)
    f (hf : f ∈ asIdeal (hV1_.primeIdealOf ⟨y, hyV⟩)) :
    (X.presheaf.map (homOfLE hle).op).hom f ∈ asIdeal (hW1_.primeIdealOf ⟨y, hyW⟩) := by
  by_contra hcon
  have h1 :=
    mem_basicOpen_of_notMem_primeIdealOf hW1_ hyW _ hcon
  have hgerm : (pGerm X W1 y hyW).hom ((pMap X (homOfLE hle).op).hom f)
      = (pGerm X V1 y hyV).hom f := by
    simp
  have h2 : y ∈ bOpn X f := by simp_all
  exact notMem_basicOpen_of_mem_primeIdealOf hV1_ hyV f hf h2

omit [Smooth p] in
theorem exists_unlabeled_index_partialDeriv_notMem_primeIdealOf
    (hV : IsAffineOpen V) (c : EtaleChart p V n) {x} (hx : x ∈ V)
    (N : Bdy X) ga_ (H : ISD X)
    g (hga_ : IsCoordLabeling c ga_ N) (_hinj : LabelingInjective ga_ N.length)
    (hsnc : InStrictNormalCrossingPositionAt p (H :: N) x) (hg : H.ideal ⟨V, hV⟩ = span {g})
    (hxH : x ∈ H.support)
    (hxN : ∀ i : ℕ, ∀ hi : i < N.length, ∀ j : Fin n,
      ga_ i = some j → x ∈ (N[i]'hi).support) :
    letI : Algebra k (X.sec V) := sectionsAlgebra k p V
    letI := c.algebra
    haveI := c.isScalarTower
    haveI :=
      c.algebra_formallyEtale hV
    ∃ j, (∀ i, i < N.length → ga_ i ≠ some j) ∧
      partialDeriv k (UFin n) V.sec (up j) g ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  classical
  show ∃ j, (∀ i, i < N.length → ga_ i ≠ some j) ∧
      chartPartialDeriv hV c j g ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  by_contra hcon
  have hall : ∀ j, (∀ i, i < N.length → ga_ i ≠ some j) →
      chartPartialDeriv hV c j g ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by simp_all
  obtain ⟨U, hxU, m, c2_, alab, hainj, hanone, hasome⟩ := hsnc.exists_etaleChart
  have hlen0 : 0 < (H :: N).length := by
    rw [length_cons]
    omega
  have hHget : (H :: N)[0]'hlen0 = H := rfl
  obtain ⟨t, hat⟩ : ∃ t, alab 0 = some t := by
    rcases hopt : alab 0 with _ | t
    exfalso
    have htop := hanone 0 hlen0 hopt
    rw [hHget] at htop
    exact (notMem_support_of_restrictIdeal_eq_top_of_mem H htop hxU) hxH
    exact ⟨t, rfl⟩
  have hHU : restrictIdeal H U = c2_.coordIdeal {t} := by
    have h1 := hasome 0 hlen0 t hat
    rwa [hHget] at h1
  have hxUV : x ∈ (U ⊓ V : Opn X) := ⟨hxU, hx⟩
  obtain ⟨fW, hfWle, hxfW⟩ := hV.exists_basicOpen_le (⟨x, hxUV⟩ : (U ⊓ V : Opn X)) hx
  obtain ⟨W, hWaff, hWV, hWU, hxW⟩ :
      ∃ W, IsAffineOpen W ∧ W ≤ V ∧ W ≤ U ∧ x ∈ W :=
    ⟨bOpn X fW, hV.basicOpen fW, X.basicOpen_le fW,
      le_trans hfWle inf_le_left, hxfW⟩
  have hHidW : H.ideal ⟨W, hWaff⟩ = span {(c2_.restrict hWU).coord t} := by
    have h1 := (c2_.restrict hWU).ideal_eq_span_coord hWaff H {t} $ restrictIdeal_eq_restrict_coordIdeal_of_le hWU c2_ H {t} hHU
    rwa [coe_singleton, image_singleton] at h1
  have hgW : H.ideal ⟨W, hWaff⟩
      = span {(pMap X (homOfLE hWV).op).hom g} := by
    have h1 := ideal_eq_span_image_map_of_le H hV hWaff hWV {g} hg
    rwa [image_singleton] at h1
  obtain ⟨u, hu, hgu⟩ := exists_isUnit_mul_of_span_singleton_eq
    (coord_mem_nonZeroDivisors hWaff (c2_.restrict hWU) t) $ st_ hgW hHidW
  have hyq : (c2_.restrict hWU).coord t ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    refine ideal_le_primeIdealOf H hWaff hxW hxH ?_
    rw [hHidW]
    exact mem_span_singleton_self _
  have hlabel : ∀ j, (∃ i, i < N.length ∧ ga_ i = some j) →
      chartPartialDeriv hWaff (c2_.restrict hWU) t ((c.restrict hWV).coord j) ∈
        (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    rintro j ⟨i, hi, hgai⟩
    have hNidW : (N[i]'hi).ideal ⟨W, hWaff⟩
        = span {(c.restrict hWV).coord j} := by
      have h1 := (c.restrict hWV).ideal_eq_span_coord hWaff (N[i]'hi) {j} $ restrictIdeal_eq_restrict_coordIdeal_of_le hWV c (N[i]'hi) {j} $ (hga_ i hi).2 j hgai
      rwa [coe_singleton, image_singleton] at h1
    have hilen : i + 1 < (H :: N).length := by
      rw [length_cons]
      omega
    have hNget : (H :: N)[i + 1]'hilen = N[i]'hi := rfl
    obtain ⟨s, has⟩ : ∃ s, alab (i + 1) = some s := by
      rcases hopt : alab (i + 1) with _ | s
      exfalso
      have htop := hanone (i + 1) hilen hopt
      rw [hNget] at htop
      exact (notMem_support_of_restrictIdeal_eq_top_of_mem (N[i]'hi) htop hxU) $ hxN i hi j hgai
      exact ⟨s, rfl⟩
    have hst : s ≠ t := by
      intro heq
      have h0 :=
        hainj 0 hlen0 (i + 1) hilen t hat $ by rw [has, heq]
      omega
    have hNU : restrictIdeal (N[i]'hi) U = c2_.coordIdeal {s} := by
      have h1 := hasome (i + 1) hilen s has
      rwa [hNget] at h1
    have hNidW2 : (N[i]'hi).ideal ⟨W, hWaff⟩
        = span {(c2_.restrict hWU).coord s} := by
      have h1 := (c2_.restrict hWU).ideal_eq_span_coord hWaff (N[i]'hi) {s} $ restrictIdeal_eq_restrict_coordIdeal_of_le hWU c2_ (N[i]'hi) {s} hNU
      rwa [coe_singleton, image_singleton] at h1
    obtain ⟨v, _, hvj⟩ := exists_isUnit_mul_of_span_singleton_eq
      (coord_mem_nonZeroDivisors hWaff (c2_.restrict hWU) s) $ st_ hNidW hNidW2
    have hsq : (c2_.restrict hWU).coord s ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      refine ideal_le_primeIdealOf (N[i]'hi) hWaff hxW (hxN i hi j hgai) ?_
      rw [hNidW2]
      exact mem_span_singleton_self _
    rw [hvj, chartPartialDeriv_mul,
      chartPartialDeriv_coord_of_ne hWaff (c2_.restrict hWU) t s $ m113 hst,
      mul_zero, zero_add]
    exact mul_mem_right _ _ hsq
  have hdecomp := chartPartialDeriv_chainRule hWaff (c.restrict hWV) (c2_.restrict hWU) t
    ((pMap X (homOfLE hWV).op).hom g)
  have hsum : chartPartialDeriv hWaff (c2_.restrict hWU) t
      ((pMap X (homOfLE hWV).op).hom g)
      ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    rw [hdecomp]
    refine m133 _ fun i _ => ?_
    by_cases hlab : ∃ l, l < N.length ∧ ga_ l = some i
    exact mul_mem_right _ _ $ hlabel i hlab
    refine mul_mem_left _ _ ?_
    have hunlab : ∀ l, l < N.length → ga_ l ≠ some i := by
      intro l hl hcon2
      exact hlab ⟨l, hl, hcon2⟩
    have h2 := map_mem_primeIdealOf_of_mem_of_le hV hWaff hWV hx hxW _ $ hall i hunlab
    rwa [map_chartPartialDeriv_restrict hV c hWaff hWV i g] at h2
  rw [hgu, chartPartialDeriv_mul, chartPartialDeriv_coord_self] at hsum
  have huq : u ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    have h2 : (c2_.restrict hWU).coord t *
        chartPartialDeriv hWaff (c2_.restrict hWU) t u
        ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := mul_mem_right _ _ hyq
    have h3 := sub_mem _ hsum h2
    rwa [add_sub_cancel_right, mul_one] at h3
  exact (hWaff.primeIdealOf ⟨x, hxW⟩).isPrime.ne_top
    (eq_top_of_isUnit_mem _ huq hu)

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace Opposite

namespace FunctorialResolution.EmbeddedResolution

variable {k : Type} [Field k] {X Y : Sch}

section
variable (p : X ⟶ Sp k)
theorem finiteType_sectionsAlgebra_of_isAffineOpen [Smooth p] (h : Y ⟶ X)
    [Smooth h] {V} (hV : IsAffineOpen V) :
    @FiniteType k (Y.sec V) _ _ (sectionsAlgebra k (h ≫ p) V) :=
  @finiteType_sections k _ Y (h ≫ p) _ ⟨V, hV⟩ (sectionsAlgebra k (h ≫ p) V)
    (algebraMap_sectionsAlgebra k (h ≫ p) V)

theorem strictNormalCrossings_chart_conditions_comap (h : Y ⟶ X)
    (E : Bdy X) {U : Opn X} {m : ℕ} (c : EtaleChart p U m)
    (a : ℕ → Option (Fin m))
    (hinj : ∀ i < length E, ∀ j < length E, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ i hi, a i = none → restrictIdeal E[i] U = ⊤)
    (hsome : ∀ i hi t, a i = some t →
      restrictIdeal E[i] U = c.coordIdeal {t})
    {V : Opn Y} {d} (c' : EtaleChart (h ≫ p) V (m + d))
    (htop : ∀ D : ISD X, restrictIdeal D U = ⊤ → restrictIdeal (comap D h) V = ⊤)
    (hcid : ∀ D S, restrictIdeal D U = c.coordIdeal S →
      restrictIdeal (comap D h) V = c'.coordIdeal (S.map (castAddEmb d))) :
    (∀ i < length (E.map fun D => comap D h), ∀ j < length (E.map fun D => comap D h),
        ∀ t : Fin (m + d), Option.map (castAdd d) (a i) = some t →
          Option.map (castAdd d) (a j) = some t → i = j) ∧
      (∀ i (hi : i < length (E.map fun D => comap D h)),
          Option.map (castAdd d) (a i) = none →
          restrictIdeal (E.map fun D => comap D h)[i] V = ⊤) ∧
      (∀ i (hi : i < length (E.map fun D => comap D h)) (t : Fin (m + d)),
          Option.map (castAdd d) (a i) = some t →
          restrictIdeal (E.map fun D => comap D h)[i] V = c'.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  intro i hi j hj t h1 h2
  have hi' := by simpa using hi
  have hj' := by simpa using hj
  cases hai : a i with
  | none => rw [hai] at h1; simp at h1
  | some t1_ =>
    cases haj : a j with
    | none => rw [haj] at h2; simp at h2
    | some t2_ =>
      rw [hai] at h1
      rw [haj] at h2
      have ht : t1_ = t2_ := (castAddEmb d).injective $ by
        rw [castAddEmb_apply, castAddEmb_apply, inj h1, inj h2]
      exact hinj i hi' j hj' t1_ hai $ by rw [haj, ht]
  intro i hi hni
  have hi' := by simpa using hi
  have hgi : (E.map (·.comap h))[i]'hi = cmI (E[i]'hi') h := by simp
  rw [hgi]
  cases hai : a i with
  | none => exact htop _ $ hnone i hi' hai
  | some _ => rw [hai] at hni; simp at hni
  intro i hi t h1
  have hi' := by simpa using hi
  have hgi : (E.map (·.comap h))[i]'hi = cmI (E[i]'hi') h := by simp
  rw [hgi]
  cases hai : a i with
  | none => rw [hai] at h1; simp at h1
  | some t1_ =>
    rw [hai] at h1
    have h2 := hcid _ {t1_} $ hsome i hi' t1_ hai
    rwa [map_singleton, castAddEmb_apply, inj h1] at h2
end

section
variable {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
theorem etale_of_formallyEtale_of_finitePresentation
    (h1 : @FormallyEtale A B _ _ f.toAlgebra)
    (h2 : @FinitePresentation A B _ _ f.toAlgebra) : f.Etale :=
  @Algebra.Etale.mk A B _ _ f.toAlgebra h1 h2

theorem ideal_eq_top_of_map_eq_top_of_leftInverse
    (g : B →+* A) (hgf : ∀ x, g (f x) = x) I (hI : Ideal.map f I = ⊤) : I = ⊤ := by
  have h2 : Ideal.map g (Ideal.map f I) = I := by
    rw [map_map]
    have hc : g.comp f = RingHom.id A := RingHom.ext hgf
    rw [hc, Ideal.map_id]
  rw [hI, Ideal.map_top] at h2
  exact sy_ h2
end

section
variable {Z : Sch}
theorem topIso_hom_inv_apply (V : Opn Z) x :
    V.topIso.hom.hom (V.topIso.inv.hom x) = x :=
  V.topIso.commRingCatIsoToRingEquiv.right_inv x

private theorem io_appLE_self_top_eq_topIso_inv (V : Opn Z) :
    V.ι.appLE V ⊤ (by simp) = V.topIso.inv := by
  simp
  apply presheaf_map_eq_of_parallel

private theorem ideal_affineOpen_eq_top_of_restrictIdeal_eq_top {V : Opn Z}
    (hV : IsAffineOpen V) (D : ISD Z) (hD : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤) ≤ opPre V V := by simp
  have h1 : Ideal.map (V.ι.appLE V ⊤ e1).hom (D.ideal ⟨V, hV⟩) = ⊤ := by
    rw [← comap_ideal_eq_map_appLE D V.i ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, ← restrictIdeal_eq_comap_io, hD]
    simp
  rw [io_appLE_self_top_eq_topIso_inv] at h1
  exact ideal_eq_top_of_map_eq_top_of_leftInverse _ V.topIso.hom.hom (topIso_hom_inv_apply V) _ h1
end

def uliftFinAddEquivSum (m d : ℕ) :
    UFin (m + d) ≃ UFin m ⊕ UFin d :=
  ulift.trans (finSumFinEquiv.symm.trans (sumCongr ulift.symm ulift.symm))

theorem sumEquiv_castAdd_eq_inl m d j :
    uliftFinAddEquivSum m d (up (castAdd d j)) = Sum.inl (up j) := by
  simp [uliftFinAddEquivSum]

theorem etale_comp_ringEquiv {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : B →+* C) (e : A ≃+* B) (hf : f.Etale) : (f.comp e.toRingHom).Etale :=
  RingHom.Etale.respectsIso.2 f e hf

section
variable (p : X ⟶ Sp k) [Smooth p] (h : Y ⟶ X) [Smooth h]
section
variable {U : Opn X} {m : ℕ} (c : EtaleChart p U m) (y : Y) (hy : h.base y ∈ U)
include hy
theorem exists_etaleChart_comap_restrictIdeal_eq_coordIdeal :
    ∃ (V : Opn Y) (d : ℕ) (c' : EtaleChart (h ≫ p) V (m + d)) (hVU : V ≤ pre h U),
      IsAffineOpen V ∧ y ∈ V ∧
      (∀ j, c'.coord (castAdd d j) = (appLE h U V hVU).hom (c.coord j)) ∧
      (∀ D : ISD X, restrictIdeal D U = ⊤ → restrictIdeal (D.comap h) V = ⊤) ∧
      (∀ D S, restrictIdeal D U = c.coordIdeal S →
        restrictIdeal (D.comap h) V = c'.coordIdeal (S.map (castAddEmb d))) := by
  let _a0 := h ≫ p
  obtain ⟨W, V, d, e, hW, hV, hyV, hWU, -, g, hgE, hgc⟩ :=
    SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le h y U hy ⊤ (by trivial)
  obtain ⟨ps_, hpsE, hpsC, hpsX⟩ : ∃ ps_ : MvPolynomial (UFin $ m + d) k →+* V.sec, ps_.Etale ∧ (∀ a, ps_ (MvPolynomial.C a) = sectionsAlgebraMap k (h ≫ p) V a) ∧ ∀ j, ps_ (MvPolynomial.X $ up $ castAdd d j) = (appLE h W V e).hom ((c.restrict hWU).coord j) := by
    let cW := c.restrict hWU
    let _c0 := MvPolynomial (UFin m ⊕ UFin d) k
    let _c1 := UFin m
    let _c2 := UFin d
    have := hgE
    let _ := sectionsAlgebra k p W
    let _ := cW.algebra
    have := cW.isScalarTower
    have :=
      cW.algebra_formallyEtale hW
    let _ := chartAlgebra hW g
    have :=
      chartAlgebra_formallyEtale hW hV g
    set χ : MvPolynomial (UFin m ⊕ UFin d) k →+* V.sec :=
      (chartEvalHom hW g).comp
        (sumEval k _c1 _c2 W.sec).toRingHom
      with hchdef
    let _ := χ.toAlgebra
    let _ := sumEvalAlgebra k _c1 _c2 $ X.sec W
    have : IsScalarTower _c0
        (MvPolynomial _c2 W.sec) V.sec :=
      of_algebraMap_eq fun x => by
        rw [algebraMap_eq_sumEval]
        rfl
    have : FormallyEtale _c0
        V.sec :=
      formallyEtale_trans k _c1 _c2 W.sec
        V.sec
    have hCval : ∀ a, χ (MvPolynomial.C a) = sectionsAlgebraMap k (h ≫ p) V a := by
      intro a
      have hc := (sumEval k _c1 _c2
        W.sec).commutes a
      rw [algebraMap_eq] at hc
      have h1 : sumEval k _c1 _c2 W.sec
          (MvPolynomial.C a) = MvPolynomial.C (sectionsAlgebraMap k p W a) := by
        rw [hc, MvPolynomial.algebraMap_apply, algebraMap_sectionsAlgebra]
      rw [hchdef]
      simp only [comp_apply, AlgHom.toRingHom_eq_coe, coe_coe]
      rw [h1, chartEvalHom_C hW h e g hgc, sectionsAlgebraMap_appLE_apply]
    have hXval : ∀ j, χ (MvPolynomial.X $ Sum.inl $ up j)
        = (appLE h W V e).hom (cW.coord j) := by
      intro j
      have h1 : sumEval k _c1 _c2 W.sec
          (MvPolynomial.X $ Sum.inl $ up j)
          = MvPolynomial.C (EtaleCoordinates.coord k _c1 W.sec
              (up j)) := by
        rw [← algebraMap_eq_sumEval]
        exact algebraMap_X_inl k _c1 _c2
          W.sec $ up j
      rw [hchdef]
      simp only [comp_apply, AlgHom.toRingHom_eq_coe, coe_coe]
      rw [h1, cW.etaleCoordinates_coord j, chartEvalHom_C hW h e g hgc]
    let _ := sectionsAlgebra k (h ≫ p) V
    have : FiniteType k V.sec := finiteType_sectionsAlgebra_of_isAffineOpen p h hV
    have : IsScalarTower k _c0 V.sec :=
      of_algebraMap_eq fun a => by
        rw [algebraMap_sectionsAlgebra, algebraMap_eq]
        exact (hCval a).symm
    have : FiniteType _c0 V.sec :=
      of_restrictScalars_finiteType k
        _c0 V.sec
    have : IsNoetherianRing _c0 :=
      inferInstance
    have : FinitePresentation _c0
        V.sec := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    refine ⟨χ.comp (renameEquiv k $ uliftFinAddEquivSum m d).toRingEquiv.toRingHom,
      etale_comp_ringEquiv χ (renameEquiv k $ uliftFinAddEquivSum m d).toRingEquiv $ etale_of_formallyEtale_of_finitePresentation χ inferInstance inferInstance,
      ?_, ?_⟩
    intro a
    simp only [comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv, renameEquiv_apply, MvPolynomial.rename_C]
    exact hCval a
    intro j
    simp only [comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv, renameEquiv_apply, MvPolynomial.rename_X]
    rw [sumEquiv_castAdd_eq_inl]
    exact hXval j
  have hVU : V ≤ preU h U := fun z hz => hWU $ e hz
  set v : UFin (m + d) → Γ(oSch V, ⊤) :=
    fun i => V.topIso.inv.hom (ps_ $ MvPolynomial.X i) with hvdef
  have hEt :=
    etale_homOfVector_of_ringHom_etale _a0 hV ps_ hpsC hpsE
      (y := fun i => ps_ $ MvPolynomial.X i) (hX := fun _ => rfl)
  have hcoordEq : ∀ j,
      (ofCoords _a0 V v hEt).coord (castAdd d j)
        = ps_ (MvPolynomial.X $ up $ castAdd d j) := by
    intro j
    rw [coord_def, ofCoords_map,
      show (AffineSpace.homOfVector (opI V ≫ _a0) v).appTop.hom
          (AffineSpace.coord (Sp k) $ up $ castAdd d j)
          = v (up $ castAdd d j) from
        AffineSpace.homOfVector_appTop_coord _ _ _]
    rw [hvdef]
    exact topIso_hom_inv_apply V _
  refine ⟨V, d, ofCoords _a0 V v hEt, hVU, hV, hyV, ?_, ?_, ?_⟩
  intro j
  refine (hcoordEq j).trans $ (hpsX j).trans ?_
  rw [coord_restrict c hWU j]
  have _i2 : appLE h U V hVU = pMap X (homOfLE hWU).op ≫ appLE h W V e := by
    rw [map_appLE]
  have h5 := congrArg (fun ph_ : X.sec U ⟶ Y.sec V => ph_.hom $ c.coord j)
    _i2
  simp only [hom_comp, coe_comp, Function.comp_apply] at h5
  exact h5.symm
  intro D hD
  have h1 := restrictIdeal_eq_top_of_le D hWU hD
  have h2 := ideal_affineOpen_eq_top_of_restrictIdeal_eq_top hW D h1
  have h3 : (cmI D h).ideal ⟨V, hV⟩ = ⊤ := by
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE D h ⟨W, hW⟩ ⟨V, hV⟩ e, h2, Ideal.map_top]
  let D := cmI D h
  let hD := h3
  have : IsAffine V.toScheme := hV
  have e1 : (⊤) ≤ opPre V V := by simp
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [restrictIdeal_eq_comap_io,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.i ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1,
    hD, Ideal.map_top]
  simp
  intro D S hD
  apply restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV
  rw [comap_ideal_eq_map_appLE D h ⟨W, hW⟩ ⟨V, hV⟩ e, ideal_eq_span_coord (c.restrict hWU) hW D S $ restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D S hD, map_span]
  congr 1
  rw [coe_map, image_image, image_image]
  have hEq : ∀ i, (appLE h W V e).hom ((c.restrict hWU).coord i)
      = (ofCoords _a0 V v hEt).coord (castAddEmb d i) := by simp_all
  exact image_congr fun i _ => hEq i

theorem exists_etaleChart_comap_coord_eq :
    ∃ (V : Opn Y) (hVU : V ≤ pre h U) (d : ℕ) (c' : EtaleChart (h ≫ p) V (m + d)),
      IsAffineOpen V ∧ y ∈ V ∧
        ∀ j,
          c'.coord (castAdd d j) = (appLE h U V hVU).hom (c.coord j) := by
  obtain ⟨V, d, c', hVU, hV, hyV, hcoord, -, -⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal p h c y hy
  exact ⟨V, hVU, d, c', hV, hyV, hcoord⟩
end

section
variable (E : Bdy X) (hE : InStrictNormalCrossingPosition p E)
include hE
theorem isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition
    (D : ISD X) (hD : D ∈ E) :
    IsSmoothDivisor (h ≫ p) (comap D h) := by
  obtain ⟨i, hi, hEi⟩ := mem_iff_getElem.1 hD
  refine isSmoothDivisor_of_locally_coordIdeal (cmI D h) ?_
  intro y
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := ((inStrictNormalCrossingPosition_iff p E).1 hE).2 $ bsM h y
  obtain ⟨V, d, c', _, _, hyV, _, htop, hcid⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal p h c y hxU
  refine ⟨V, hyV, m + d, c', ?_⟩
  cases hai : a i with
  | none =>
      left
      have h1 := hnone i hi hai
      rw [hEi] at h1
      exact htop D h1
  | some t =>
      right
      refine ⟨castAdd d t, ?_⟩
      have h1 := hsome i hi t hai
      rw [hEi] at h1
      have h2 := hcid D {t} h1
      rwa [map_singleton, castAddEmb_apply] at h2

theorem inStrictNormalCrossingPosition_comap :
    InStrictNormalCrossingPosition (h ≫ p) (E.map fun D => comap D h) := by
  rw [inStrictNormalCrossingPosition_iff]
  constructor
  intro D hD
  rw [mem_map] at hD
  obtain ⟨D0_, hD0_, rfl⟩ := hD
  exact isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition p h E hE D0_ hD0_
  intro y
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := ((inStrictNormalCrossingPosition_iff p E).1 hE).2 $ bsM h y
  obtain ⟨V, d, c', _, _, hyV, _, htop, hcid⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal p h c y hxU
  have hL := strictNormalCrossings_chart_conditions_comap p h E c a hinj hnone hsome c' htop hcid
  exact ⟨V, hyV, m + d, c', fun i => Option.map (castAdd d) $ a i,
    an1 hL, hL.2.1, hL.2.2⟩
end

theorem hasStrictNormalCrossingsWith_comap
    (Z : ISD X) (E : Bdy X) (hZ : HasStrictNormalCrossingsWith p Z E) :
    HasStrictNormalCrossingsWith (h ≫ p) (comap Z h) (E.map fun D => comap D h) := by
  intro y hy
  have hxZ : bsM h y ∈ spI Z := by
    rwa [m19] at hy
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZU⟩ := hZ (bsM h y) hxZ
  obtain ⟨V, d, c', _, _, hyV, _, htop, hcid⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal p h c y hxU
  have hL := strictNormalCrossings_chart_conditions_comap p h E c a hinj hnone hsome c' htop hcid
  exact ⟨V, hyV, m + d, c', fun i => Option.map (castAdd d) $ a i, S.map $ castAddEmb d,
    an1 hL, hL.2.1, hL.2.2, hcid Z S hZU⟩

theorem inStrictNormalCrossingPosition_comap_singleton (H : ISD X) (hH : InStrictNormalCrossingPosition p [H]) :
    InStrictNormalCrossingPosition (h ≫ p) [comap H h] := by
  have hcomp := inStrictNormalCrossingPosition_comap p h [H] hH
  rwa [m75, map_nil] at hcomp
end

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable (c d : ℕ)
def castAddImage : Finset (Fin (c + d)) :=
  (Finset.univ : FinSet c).image (castAdd d)

theorem castAddImage_eq_image_castAdd :
    castAddImage c d = (Finset.univ : FinSet c).image (Fin.castAdd d) := rfl

theorem card_castAddImage : (castAddImage c d).card = c := by
  have hinj : m120 (Fin.castAdd d : Fin c → Fin (c + d)) := by
    intro a b hab
    exact Fin.ext (congrArg (fun z : Fin (c + d) => (z : ℕ)) hab)
  rw [castAddImage_eq_image_castAdd, card_image_of_injective _ hinj, card_univ,
    card_fin]
end

section
variable {X' : Sch}
section
variable (U : Opn X') (V : U.toScheme.Opens)
theorem range_io_comp_io_eq_image :
    range ((V.i ≫ U.i).base) = (↑(U.i ''ᵁ V) : Set ↥X') := by
  ext z
  constructor
  rintro ⟨w, rfl⟩
  exact ⟨_, w.2, rfl⟩
  rintro ⟨a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩
end

end

section
variable (k : Type) [Field k] (c : ℕ)
def etaleChartTop :
    EtaleChart (affineSpaceFinToSpec k c) (⊤ : (affineSpaceFin k c).Opens) c where
  map := (⊤ : (affineSpaceFin k c).Opens).ι
  comp_struct := rfl
  isEtale := inferInstance

theorem etaleChartTop_map :
    (etaleChartTop k c).map = (⊤ : (affineSpaceFin k c).Opens).ι := rfl

theorem restrictIdeal_top_coordSubspaceIdeal_univ :
    restrictIdeal (coordSubspaceIdeal k c (Finset.univ : FinSet c))
      (⊤ : (affineSpaceFin k c).Opens) = (etaleChartTop k c).coordIdeal Finset.univ := by
  rw [restrictIdeal_eq_comap_io, coordIdeal_eq_comap_coordSubspaceIdeal, etaleChartTop_map]
end

section
variable {X X' : Sch} {k : Type} [Field k] (p : X' ⟶ Sp k)
theorem hasEtaleCoordCodim_of_locally_smooth_over_affineSpace [Smooth p] (ta_ : X ⟶ X') (c : ℕ)
    (h : ∀ x : X, ∃ (U : Opn X') (_ : ta_.base x ∈ U) (q : U.toScheme ⟶ affineSpaceFin k c),
      Smooth q ∧ q ≫ affineSpaceFinToSpec k c = U.i ≫ p ∧
        restrictIdeal ta_.ker U =
          (coordSubspaceIdeal k c (Finset.univ : FinSet c)).comap q) :
    HasEtaleCoordCodim p ta_ c := by
  intro x
  obtain ⟨U, hxU, q, hqsm, hqc, hker⟩ := h x
  have := hqsm
  obtain ⟨V, hVaff, hxV, d, ch, hch⟩ : ∃ (V : U.toScheme.Opens) (_ : IsAffineOpen V) (_ : (⟨bsM ta_ x, hxU⟩ : U) ∈ V) (d : ℕ) (ch : EtaleChart (opI U ≫ p) V $ c + d), restrictIdeal (restrictIdeal ta_.ker U) V = ch.coordIdeal (castAddImage c d) := by
    let _a2 := affineSpaceFinToSpec k c
    have : Smooth _a2 := affineSpaceIsSmooth ..
    let _a3 := etaleChartTop k c
    obtain ⟨V, hVU, d, ch, hVaff, hyV, hcoord⟩ :=
      exists_etaleChart_comap_coord_eq _a2 q _a3
        (⟨bsM ta_ x, hxU⟩ : U) $ by trivial
    let _a0 := coordSubspaceIdeal k c Finset.univ
    let _a1 := isAffineOpen_top $ affineSpaceFin k c
    have hspanV : (restrictIdeal ta_.ker U).ideal ⟨V, hVaff⟩
        = span (ch.coord ''
            ((castAddImage c d : Finset $ Fin $ c + d) : Set $ Fin $ c + d)) := by
      rw [hker,
        comap_ideal_eq_map_appLE
          _a0 q
          ⟨⊤, _a1⟩ ⟨V, hVaff⟩ hVU,
        (ideal_eq_span_coord _a3 _a1 _a0 Finset.univ $ restrictIdeal_top_coordSubspaceIdeal_univ k c), map_span]
      congr 1
      rw [image_image, castAddImage_eq_image_castAdd, coe_image, image_image]
      exact image_congr fun j _ => sy_ $ hcoord j
    have hcs : ch.map ≫ affineSpaceFinToSpec k (c + d) = opI V ≫ (opI U ≫ p) := by
      rw [ch.comp_struct, hqc]
    exact ⟨V, hVaff, hyV, d, ⟨ch.map, hcs, ch.isEtale⟩, restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff _ _ (castAddImage c d) hspanV⟩
  obtain ⟨ch', hch'⟩ : ∃ ch' : EtaleChart p (U.i.im V) $ c + d, restrictIdeal ta_.ker (U.i.im V) = ch'.coordIdeal (castAddImage c d) := by
    let n := c + d
    let S := castAddImage c d
    have hr : range ((opI U ''ᵁ V).i).base = range (bsM $ opI V ≫ opI U) := by
      rw [q1, ← range_io_comp_io_eq_image]
    let ph_ :=
      isoOfRangeEq ((opI U ''ᵁ V).i) (opI V ≫ opI U) hr
    have hfac :=
      isoOfRangeEq_hom_fac _ _ hr
    let _a2 := (isoH ph_ ≫ ch.map) ≫ affineSpaceFinToSpec k n
    have hcs : _a2 = (opI U ''ᵁ V).i ≫ p := by
      calc _a2
          = isoH ph_ ≫ (ch.map ≫ affineSpaceFinToSpec k n) := assoc _ _ _
        _ = isoH ph_ ≫ (opI V ≫ (opI U ≫ p)) := by rw [ch.comp_struct]
        _ = (isoH ph_ ≫ (opI V ≫ opI U)) ≫ p := by simp [assoc]
        _ = (U.ι ''ᵁ V).i ≫ p := by rw [hfac]
    have := ch.isEtale
    have hkey : (ta_.ker.comap U.i).comap V.i = (coordSubspaceIdeal k n S).comap ch.map := by
      rw [← restrictIdeal_eq_comap_io, ← restrictIdeal_eq_comap_io, hch, coordIdeal_eq_comap_coordSubspaceIdeal]
    refine ⟨⟨isoH ph_ ≫ ch.map, hcs, inferInstance⟩, ?_⟩
    rw [restrictIdeal_eq_comap_io, coordIdeal_eq_comap_coordSubspaceIdeal]
    calc ta_.ker.comap (imU U.i V).i
        = ((kCm ta_ U.i).comap V.i).comap ph_.hom := by
          rw [← hfac, comap_comp, comap_comp]
      _ = ((coordSubspaceIdeal k n S).comap ch.map).comap ph_.hom := by rw [hkey]
      _ = (coordSubspaceIdeal k n S).comap (isoH ph_ ≫ ch.map) := by
          rw [comap_comp]
  exact ⟨U.i.im V, ⟨⟨bsM ta_ x, hxU⟩, hxV, rfl⟩, c + d, ch',
    castAddImage c d, card_castAddImage c d, hch'⟩
end

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

def withBotSuccToNat : WithBot ENat → ℕ
  | ⊥ => 0
  | (n : ENat) => n.toNat + 1

theorem withBotSuccToNat_bot : withBotSuccToNat ⊥ = 0 := rfl

theorem withBotSuccToNat_coe (n : ENat) : withBotSuccToNat (n : WithBot ENat) = n.toNat + 1 := rfl

def krullDimSucc (X : Sch) : ℕ := withBotSuccToNat (topologicalKrullDim ↥X)

theorem krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim X : krullDimSucc X = withBotSuccToNat (topologicalKrullDim ↥X) := rfl

theorem krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le (X Y : Sch)
    (h : topologicalKrullDim ↥X ≤ topologicalKrullDim ↥Y)
    (hY : topologicalKrullDim ↥Y < ⊤) :
    krullDimSucc X ≤ krullDimSucc Y := by
  rcases eq_or_ne (topologicalKrullDim X) ⊥ with hX | hX
  simp [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, hX, withBotSuccToNat_bot]
  obtain ⟨a, ha⟩ := mp_ ne_bot_iff_exists hX
  have hYne : topologicalKrullDim Y ≠ ⊥ := by
    intro hb0
    rw [hb0, le_bot_iff] at h
    exact hX h
  obtain ⟨b, hb⟩ := mp_ ne_bot_iff_exists hYne
  have hab : a ≤ b := by
    rw [← ha, ← hb] at h
    exact_mod_cast h
  have hbtop : b ≠ ⊤ := by
    intro hbt
    rw [← hb, hbt] at hY
    exact lt_irrefl _ hY
  have hatop : a ≠ ⊤ := by
    intro hat
    rw [hat, top_le_iff] at hab
    exact hbtop hab
  have hle : a.toNat ≤ b.toNat := by
    lift a to ℕ using hatop
    lift b to ℕ using hbtop
    simpa using hab
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim X, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim Y, ← ha, ← hb, withBotSuccToNat_coe, withBotSuccToNat_coe]
  omega

structure MarkedIdealWithBoundary : Type 1 where
  base : Type
  [instField : Field base]
  scheme : Sch
  structMap : scheme ⟶ Sp base
  ideal : ISD scheme
  mult : ℕ
  boundary : Bdy scheme

attribute [instance] MarkedIdealWithBoundary.instField

theorem MarkedIdealWithBoundary.mk_eq_mk {k : Type} [instk : Field k] X m
    {p p'} {I I'}
    {E E'} (hp : p = p') (hI : I = I') (hE : E = E') :
    @MarkedIdealWithBoundary.mk k instk X p I m E = @MarkedIdealWithBoundary.mk k instk X p' I' m E' :=by simp_all
abbrev MarkedIdealWithBoundary.krullDimSucc (T : MarkedIdealWithBoundary) : ℕ := EmbeddedResolution.krullDimSucc T.scheme
abbrev MarkedIdealWithBoundary.bget (T : MarkedIdealWithBoundary) (j : ℕ) (hj : j < T.boundary.length) := T.boundary.lget j hj
abbrev MarkedIdealWithBoundary.bsup (T : MarkedIdealWithBoundary) (j : ℕ) (hj : j < T.boundary.length) : CSet T.scheme := support (T.boundary.lget j hj)
abbrev MarkedIdealWithBoundary.bget' {T : MarkedIdealWithBoundary} {j : ℕ} (hj : j < T.boundary.length) := T.boundary.get ⟨j, hj⟩


structure MarkedIdealWithBoundary.IsAdmissible (T : MarkedIdealWithBoundary) : Prop where
  charZero : CharZero T.base
  locallyOfFiniteType : LocallyOfFiniteType T.structMap
  nonzeroOnComponents : NonzeroOnComponents T.ideal
  one_le_mult : 1 ≤ T.mult
  quasiCompact : QuasiCompact T.structMap
  smooth : Smooth T.structMap
  snc : InStrictNormalCrossingPosition T.structMap T.boundary

structure MarkedSequenceOfBlowups {k : Type} [Field k] {X : Sch}
    (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
    (E : Bdy X) extends SequenceOfBlowups X where
  ideal : ∀ i : ℕ, IdealSheafData (toSequenceOfBlowups.schemeAt i)
  boundary : ∀ i : ℕ, List (toSequenceOfBlowups.schemeAt i).IdealSheafData
  ideal_zero : ideal 0 = I.comap toSequenceOfBlowups.isoZero.hom
  boundary_zero : boundary 0 = E.map fun D => D.comap toSequenceOfBlowups.isoZero.hom
  center_smooth : ∀ i, i < toSequenceOfBlowups.length →
    Smooth
      ((toSequenceOfBlowups.center i).si ≫ toSequenceOfBlowups.projectionToBase i ≫ p)
  center_snc : ∀ i, i < toSequenceOfBlowups.length →
    HasStrictNormalCrossingsWith (toSequenceOfBlowups.projectionToBase i ≫ p) (toSequenceOfBlowups.center i) (boundary i)
  center_order : ∀ i, i < toSequenceOfBlowups.length →
    ((toSequenceOfBlowups.center i).support : CSet (toSequenceOfBlowups.schemeAt i)) ⊆ orderAtLeastLocus (ideal i) m
  ideal_succ : ∀ i, i < toSequenceOfBlowups.length →
    exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i) ^ m * ideal (i + 1) =
      (ideal i).comap (toSequenceOfBlowups.transitionMapSucc i)
  boundary_succ : ∀ i, i < toSequenceOfBlowups.length →
    boundary (i + 1) =
      (boundary i).map (strictTransform (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)) ++
        [exceptionalIdeal (toSequenceOfBlowups.transitionMapSucc i) (toSequenceOfBlowups.center i)]

namespace MarkedSequenceOfBlowups

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (s : MarkedSequenceOfBlowups p I m E)
section
variable (i : ℕ)
def projectionToSpec :
    s.toSequenceOfBlowups.schemeAt i ⟶ Sp k :=
  s.toSequenceOfBlowups.projectionToBase i ≫ p

theorem projectionToSpec_eq :
    s.projectionToSpec i = s.toSequenceOfBlowups.projectionToBase i ≫ p := rfl

def exceptionalDivisor :
    IdealSheafData (s.toSequenceOfBlowups.schemeAt (i + 1)) :=
  exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)

theorem exceptionalDivisor_eq :
    s.exceptionalDivisor i = comap (s.toSequenceOfBlowups.center i) (s.toSequenceOfBlowups.transitionMapSucc i) := rfl
end

def lastIdeal :
    IdealSheafData (s.toSequenceOfBlowups.schemeAt s.toSequenceOfBlowups.length) :=
  s.ideal s.toSequenceOfBlowups.length

theorem lastIdeal_eq :
    s.lastIdeal = s.ideal s.toSequenceOfBlowups.length := rfl


def IsResolution : Prop :=
  orderAtLeastLocus s.lastIdeal m = ∅

theorem isResolution_iff :
    s.IsResolution ↔ orderAtLeastLocus s.lastIdeal m = ∅ := m22
end

end MarkedSequenceOfBlowups

def emptySequenceOfBlowups (X : Sch) : SequenceOfBlowups X where
  length := 0
  tower := (CategoryTheory.Functor.const ℕᵒᵖ).obj X
  isoZero := Iso.refl X
  center := fun _ => ⊥
  isBlowup := fun i hi => absurd hi (not_lt_zero i)


section
variable {k : Type} [Field k] {X : Sch} (p : X ⟶ Sp k) (I : ISD X) (m : ℕ) (E : Bdy X)
def emptyMarkedSequenceOfBlowups : MarkedSequenceOfBlowups p I m E where
  toSequenceOfBlowups := emptySequenceOfBlowups X
  ideal := fun _ => comap I (emptySequenceOfBlowups X).isoZero.hom
  boundary := fun _ => E.map fun D => comap D (emptySequenceOfBlowups X).isoZero.hom
  ideal_zero := rfl
  boundary_zero := rfl
  center_smooth := fun i hi => absurd hi (not_lt_zero i)
  center_snc := fun i hi => absurd hi (not_lt_zero i)
  center_order := fun i hi => absurd hi (not_lt_zero i)
  ideal_succ := fun i hi => absurd hi (not_lt_zero i)
  boundary_succ := fun i hi => absurd hi (not_lt_zero i)

theorem emptyMarkedSequenceOfBlowups_length :
    (emptyMarkedSequenceOfBlowups p I m E).toSequenceOfBlowups.length = 0 := rfl
end

abbrev MarkedIdealWithBoundary.SequenceOfBlowups (T : MarkedIdealWithBoundary) : Type 1 :=
  MarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

def PrincipalizationAssignment : Type 1 := ∀ T : MarkedIdealWithBoundary, T.SequenceOfBlowups

theorem PrincipalizationAssignment.toSequenceOfBlowups_heq_of_eq (L : PrincipalizationAssignment)
    {T T' : MarkedIdealWithBoundary} (h : T = T') :
    HEq (L T).toSequenceOfBlowups (L T').toSequenceOfBlowups := by
  subst h
  rfl

def trivialPrincipalizationAssignment : PrincipalizationAssignment :=
  fun (T : MarkedIdealWithBoundary) => emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

structure OrderReductionData : Type 1 where
  maxOrderRed : PrincipalizationAssignment
  orderRed : PrincipalizationAssignment

def trivialOrderReductionData : OrderReductionData where
  maxOrderRed := trivialPrincipalizationAssignment
  orderRed := trivialPrincipalizationAssignment

section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (s : MarkedSequenceOfBlowups p I m E)
def HasReducedCenters : Prop :=
  ∀ i, i < s.toSequenceOfBlowups.length → ∀ J : IdealSheafData (s.toSequenceOfBlowups.schemeAt i),
    (support (s.toSequenceOfBlowups.center i) : CSet (s.toSequenceOfBlowups.schemeAt i)) ⊆
        (support J : CSet (s.toSequenceOfBlowups.schemeAt i)) →
      J ≤ s.toSequenceOfBlowups.center i

theorem markedSequenceOfBlowups_ideal_zero :
    s.ideal 0 = comap I (s.toSequenceOfBlowups.projectionToBase 0) := by
  rw [s.ideal_zero, s.toSequenceOfBlowups.projectionToBase_zero]

end

section
variable (s : MarkedSequenceOfBlowups p I 1 E)
theorem markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ i
    (h : i < s.toSequenceOfBlowups.length) :
    exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) * s.ideal (i + 1) =
      comap (s.ideal i) (s.toSequenceOfBlowups.transitionMapSucc i) := by
  have hs := s.ideal_succ i h
  rwa [pow_one] at hs

section
variable (hmax : HasReducedCenters s)
include hmax
theorem markedSequenceOfBlowups_ideal_vanishesAlong_center i (h : i < s.toSequenceOfBlowups.length) :
    VanishesAlong (s.ideal i) (s.toSequenceOfBlowups.center i) := by
  rw [vanishesAlong_iff_le]
  refine hmax i h (s.ideal i) ?_
  intro x hx
  have hx' := s.center_order i h hx
  rwa [mem_orderAtLeastLocus_one_iff] at hx'

def MarkedSequenceOfBlowups.toIdealBlowupSequence :
    IdealBlowupSequence p I E where
  toSequenceOfBlowups := s.toSequenceOfBlowups
  ideal := s.ideal
  boundary := s.boundary
  ideal_zero := markedSequenceOfBlowups_ideal_zero s
  boundary_zero := by
    rw [s.boundary_zero, s.toSequenceOfBlowups.projectionToBase_zero]
  center_smooth := s.center_smooth
  center_snc := s.center_snc
  ideal_vanishes := fun i h => markedSequenceOfBlowups_ideal_vanishesAlong_center s hmax i h
  ideal_succ := fun i h => markedSequenceOfBlowups_exceptionalIdeal_mul_ideal_succ s i h
  boundary_succ := s.boundary_succ

@[simp]
theorem MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups :
    (s.toIdealBlowupSequence hmax).toSequenceOfBlowups = s.toSequenceOfBlowups := rfl

@[simp]
theorem MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal :
    (s.toIdealBlowupSequence hmax).lastIdeal = s.lastIdeal := rfl
end
end

end

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite


namespace FunctorialResolution.EmbeddedResolution

structure BlowupSequenceData (X : Sch) : Type 1 where
  length : ℕ
  obj : ℕ → Sch
  map : ∀ i : ℕ, obj (i + 1) ⟶ obj i
  isoZero : obj 0 ≅ X
  center : ∀ i : ℕ, IdealSheafData (obj i)
  isBlowup : ∀ i, i < length → Blowup.IsBlowupAlongIdealSheaf (map i) (center i)

namespace BlowupSequenceData

variable {X : Sch}

def projectionToBase (d : BlowupSequenceData X) : ∀ i : ℕ, d.obj i ⟶ X
  | 0 => d.isoZero.hom
  | (i + 1) => d.map i ≫ projectionToBase d i

section
variable (d : BlowupSequenceData X)
@[simp]
theorem projectionToBase_zero : projectionToBase d 0 = d.isoZero.hom := rfl

@[simp]
theorem projectionToBase_succ (i : ℕ) :
    projectionToBase d (i + 1) = d.map i ≫ projectionToBase d i := rfl

theorem blowupMorphism_comp_eqToHom {n m} (h : n = m) :
    d.map n ≫ eqToHom (congrArg d.obj h) =
      eqToHom (show d.obj (n + 1) = d.obj (m + 1) by rw [h]) ≫ d.map m := by
  subst h
  simp
end

def ofSequenceOfBlowups (s : SequenceOfBlowups X) : BlowupSequenceData X where
  length := s.length
  obj := s.schemeAt
  map := s.transitionMapSucc
  isoZero := s.isoZero
  center := s.center
  isBlowup := fun i hi => s.isBlowupAlongIdealSheaf_blowupMorphism i hi

def homAdd (d : BlowupSequenceData X) (i : ℕ) : ∀ k : ℕ, d.obj (i + k) ⟶ d.obj i
  | 0 => 𝟙 (d.obj i)
  | (k + 1) => d.map (i + k) ≫ homAdd d i k

section
variable (d : BlowupSequenceData X)
def homOfLE {i j : ℕ} (h : i ≤ j) : d.obj j ⟶ d.obj i :=
  eqToHom (congrArg d.obj (add_sub_cancel' h).symm) ≫ homAdd d i (j - i)

theorem eqToHom_comp_iteratedBlowupMorphism_of_eq_zero i k
    (h : d.obj i = d.obj (i + k)) (hk : k = 0) :
    eqToHom h ≫ homAdd d i k = 𝟙 (d.obj i) := by
  subst hk
  have h1 : homAdd d i 0 = 𝟙 (d.obj i) := rfl
  have h2 : eqToHom h = 𝟙 (d.obj i) := rfl
  rw [h1, h2]
  exact id_comp $ 𝟙 $ d.obj i

theorem iteratedBlowupMorphism_succ i k :
    homAdd d i (k + 1) = d.map (i + k) ≫ homAdd d i k := rfl

section
variable (i : ℕ)
theorem iteratedBlowupMorphism_congr_length {k k'} (h : k = k') :
    homAdd d i k =
      eqToHom (show d.obj (i + k) = d.obj (i + k') by rw [h]) ≫ homAdd d i k' := by
  subst h
  simp

theorem towerMorphism_refl :
    homOfLE d (le_refl i) = 𝟙 (d.obj i) :=
  eqToHom_comp_iteratedBlowupMorphism_of_eq_zero d i (i - i)
    (congrArg d.obj (add_sub_cancel' $ le_refl i).symm) $ Nat.sub_self i

theorem iteratedBlowupMorphism_zero :
    homAdd d i 0 = 𝟙 (d.obj i) := rfl
end

theorem towerMorphism_eq_iteratedBlowupMorphism {i j} (h : i ≤ j) k
    (hk : j = i + k) :
    homOfLE d h = eqToHom (congrArg d.obj hk) ≫ homAdd d i k := by
  subst hk
  unfold homOfLE
  rw [iteratedBlowupMorphism_congr_length d i $ show i + k - i = k by omega]
  simp

theorem iteratedBlowupMorphism_congr_start {i i'} (h : i = i') k :
    homAdd d i k =
      eqToHom (show d.obj (i + k) = d.obj (i' + k) by rw [h]) ≫ homAdd d i' k ≫
        eqToHom (show d.obj i' = d.obj i by rw [h]) := by
  subst h
  simp

theorem iteratedBlowupMorphism_comp_iteratedBlowupMorphism i a b :
    homAdd d (i + a) b ≫ homAdd d i a =
      eqToHom (congrArg d.obj (Nat.add_assoc i a b)) ≫ homAdd d i (a + b) := by
  induction b with
  | zero =>
      show homAdd d (i + a) 0 ≫ homAdd d i a
          = eqToHom (rfl : d.obj (i + a) = d.obj (i + a)) ≫ homAdd d i a
      rw [iteratedBlowupMorphism_zero, eqToHom_refl, id_comp]
      exact id_comp _
  | succ b ih =>
      rw [iteratedBlowupMorphism_succ, m146, ih, ← m146,
        blowupMorphism_comp_eqToHom d $ Nat.add_assoc i a b, m146]
      rfl

theorem towerMorphism_comp {i j l} (hij : i ≤ j) (hjl : j ≤ l) :
    homOfLE d hjl ≫ homOfLE d hij = homOfLE d (hij.trans hjl) := by
  rw [towerMorphism_eq_iteratedBlowupMorphism d hjl (l - j) $ by omega, towerMorphism_eq_iteratedBlowupMorphism d hij (j - i) $ by omega,
    towerMorphism_eq_iteratedBlowupMorphism d (hij.trans hjl) ((j - i) + (l - j)) $ by omega,
    iteratedBlowupMorphism_congr_start d (show j = i + (j - i) by omega) $ l - j]
  simp [assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp]
  rw [iteratedBlowupMorphism_comp_iteratedBlowupMorphism d i (j - i) $ l - j]
  simp

def tower : ℕᵒᵖ ⥤ Sch where
  obj n := d.obj n.unop
  map f := homOfLE d (leOfHom f.unop)
  map_id n := towerMorphism_refl d n.unop
  map_comp f g := (towerMorphism_comp d (leOfHom g.unop) (leOfHom f.unop)).symm

section
variable (i : ℕ)
@[simp]
theorem tower_obj : d.tower.obj (op i) = d.obj i := rfl

theorem eqToHom_comp_iteratedBlowupMorphism {k k'} (h : k = k')
    (hobj : d.obj (i + k) = d.obj (i + k')) :
    eqToHom hobj ≫ homAdd d i k' = homAdd d i k := by
  subst h
  simp

theorem towerMorphism_succ (h : i ≤ i + 1) :
    homOfLE d h = d.map i := by
  have h1 : i + 1 - i = 1 := by omega
  have h2 := eqToHom_comp_iteratedBlowupMorphism d i h1
    (show d.obj (i + (i + 1 - i)) = d.obj (i + 1) by rw [h1])
  unfold homOfLE
  rw [← h2, ← assoc, eqToHom_trans, eqToHom_refl, id_comp]
  show d.map (i + 0) ≫ homAdd d i 0 = d.map i
  exact comp_id _

@[simp]
theorem tower_map_succ :
    d.tower.map (CategoryTheory.homOfLE (le_succ i)).op = d.map i :=
  towerMorphism_succ d i $ le_succ i

theorem isBlowupAlongIdealSheaf_tower_map (hi : i < length d) :
    Blowup.IsBlowupAlongIdealSheaf (d.tower.map (CategoryTheory.homOfLE (le_succ i)).op) (d.center i) := by
  have h := d.isBlowup i hi
  rwa [tower_map_succ]
end

def toSequenceOfBlowups : SequenceOfBlowups X where
  length := length d
  tower := d.tower
  isoZero := d.isoZero
  center := d.center
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_tower_map d i hi

theorem toSequenceOfBlowups_schemeAt i : d.toSequenceOfBlowups.schemeAt i = d.obj i := rfl

@[simp]
theorem toSequenceOfBlowups_length : d.toSequenceOfBlowups.length = length d := rfl

@[simp]
theorem toSequenceOfBlowups_tower : d.toSequenceOfBlowups.tower = d.tower := rfl

@[simp]
theorem toSequenceOfBlowups_center (i : ℕ) : d.toSequenceOfBlowups.center i = d.center i := rfl

@[simp]
theorem toSequenceOfBlowups_isoObjZero : d.toSequenceOfBlowups.isoZero = d.isoZero := rfl

@[simp]
theorem toSequenceOfBlowups_blowupMorphism (i : ℕ) : d.toSequenceOfBlowups.transitionMapSucc i = d.map i :=
  tower_map_succ d i

@[simp]
theorem toSequenceOfBlowups_projectionToBase (i : ℕ) : d.toSequenceOfBlowups.projectionToBase i = projectionToBase d i := by
  induction i with
  | zero =>
      have h0 : d.toSequenceOfBlowups.transitionMap (m67 0) = 𝟙 (d.toSequenceOfBlowups.schemeAt 0) :=
        d.toSequenceOfBlowups.tower.map_id $ op 0
      have h1 : d.toSequenceOfBlowups.projectionToBase 0 = d.toSequenceOfBlowups.transitionMap (m67 0) ≫ d.toSequenceOfBlowups.isoZero.hom :=
        projectionToBase_def d.toSequenceOfBlowups 0
      have h2 : d.toSequenceOfBlowups.projectionToBase 0 = d.toSequenceOfBlowups.isoZero.hom := by
        rw [h1, h0, id_comp]
      exact h2
  | succ j ih =>
      refine st_ (transitionMap_comp_projectionToBase d.toSequenceOfBlowups $ le_succ j) ?_
      rw [tr_ (transitionMap_def d.toSequenceOfBlowups $ le_succ j) $ tower_map_succ d j, ih]
      exact rfl
end

section
variable (s : SequenceOfBlowups X)
@[simp]
theorem ofSequenceOfBlowups_length : (ofSequenceOfBlowups s).length = s.length := rfl

section
variable (i : ℕ)
@[simp]
theorem ofSequenceOfBlowups_schemeAt : (ofSequenceOfBlowups s).obj i = s.schemeAt i := rfl

@[simp]
theorem ofSequenceOfBlowups_blowupMorphism : (ofSequenceOfBlowups s).map i = s.transitionMapSucc i := rfl

@[simp]
theorem ofSequenceOfBlowups_center : (ofSequenceOfBlowups s).center i = s.center i := rfl

theorem ofSequenceOfBlowups_projectionToBase : projectionToBase (ofSequenceOfBlowups s) i = s.projectionToBase i := by
  induction i with
  | zero =>
    have h1 : s.tower.map (CategoryTheory.homOfLE $ le_refl 0).op = 𝟙 (s.tower.obj $ m112 0) :=
      s.tower.map_id $ m112 0
    have h2 : s.projectionToBase 0 = sbIzH s := by
      rw [projectionToBase_def, transitionMap_def, h1, id_comp]
    exact sy_ h2
  | succ i ih =>
    show (ofSequenceOfBlowups s).map i ≫ projectionToBase (ofSequenceOfBlowups s) i = sbPrj s (i + 1)
    rw [ih]
    show s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1)
    rw [blowupMorphism_eq_transitionMap, transitionMap_comp_projectionToBase]
end

@[simp]
theorem ofSequenceOfBlowups_isoObjZero : (ofSequenceOfBlowups s).isoZero = s.isoZero := rfl
end

end BlowupSequenceData

section
variable (X : Sch)
def emptyBlowupSequenceData : BlowupSequenceData X where
  length := 0
  obj := fun _ => X
  map := fun _ => 𝟙 X
  isoZero := Iso.refl X
  center := fun _ => ⊤
  isBlowup := fun i hi => absurd hi (not_lt_zero i)

@[simp]
theorem emptyBlowupSequenceData_length : (emptyBlowupSequenceData X).length = 0 := rfl

@[simp]
theorem emptyBlowupSequenceData_schemeAt (i : ℕ) : (emptyBlowupSequenceData X).obj i = X := rfl



@[simp]
theorem emptyBlowupSequenceData_isoObjZero :
    (emptyBlowupSequenceData X).isoZero = Iso.refl X := rfl
end

structure MarkedBlowupSequenceData {k : Type} [Field k] {X : Sch}
    (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
    (E : Bdy X) extends BlowupSequenceData X where
  proj : ∀ i : ℕ, toBlowupSequenceData.obj i ⟶ X
  proj_zero : proj 0 = toBlowupSequenceData.isoZero.hom
  proj_succ : ∀ i : ℕ, proj (i + 1) = toBlowupSequenceData.map i ≫ proj i
  ideal : ∀ i : ℕ, IdealSheafData (toBlowupSequenceData.obj i)
  boundary : ∀ i : ℕ, List (toBlowupSequenceData.obj i).IdealSheafData
  ideal_zero : ideal 0 = I.comap toBlowupSequenceData.isoZero.hom
  boundary_zero : boundary 0 = E.map fun D => D.comap toBlowupSequenceData.isoZero.hom
  center_order : ∀ i, i < toBlowupSequenceData.length →
    ((toBlowupSequenceData.center i).support : CSet (toBlowupSequenceData.obj i)) ⊆ orderAtLeastLocus (ideal i) m
  center_smooth : ∀ i, i < toBlowupSequenceData.length →
    Smooth ((toBlowupSequenceData.center i).si ≫ proj i ≫ p)
  center_snc : ∀ i, i < toBlowupSequenceData.length →
    HasStrictNormalCrossingsWith (proj i ≫ p) (toBlowupSequenceData.center i) (boundary i)
  ideal_succ : ∀ i, i < toBlowupSequenceData.length →
    exceptionalIdeal (toBlowupSequenceData.map i) (toBlowupSequenceData.center i) ^ m * ideal (i + 1) =
      (ideal i).comap (toBlowupSequenceData.map i)
  boundary_succ : ∀ i, i < toBlowupSequenceData.length →
    boundary (i + 1) =
      (boundary i).map (strictTransform (toBlowupSequenceData.map i) (toBlowupSequenceData.center i)) ++
        [exceptionalIdeal (toBlowupSequenceData.map i) (toBlowupSequenceData.center i)]

namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (d : MarkedBlowupSequenceData p I m E)
section
variable (i : ℕ)
theorem projectionToBase_eq :
    d.proj i = BlowupSequenceData.projectionToBase d.toBlowupSequenceData i := by
  induction i with
  | zero =>
      rw [BlowupSequenceData.projectionToBase_zero]
      exact d.proj_zero
  | succ i ih =>
      rw [d.proj_succ i, BlowupSequenceData.projectionToBase_succ, ih]

theorem projectionToBase_eq_toSequenceOfBlowups :
    d.proj i = d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i :=
  (d.projectionToBase_eq i).trans (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d.toBlowupSequenceData i).symm

section
variable (hi : i < d.toBlowupSequenceData.length)
include hi
theorem smooth_center_comp_projection :
    Smooth
      (subschemeι (d.toBlowupSequenceData.center i) ≫ d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i ≫ p) := by
  have h := d.center_smooth i hi
  rwa [projectionToBase_eq_toSequenceOfBlowups d i] at h

private theorem hasStrictNormalCrossingsWith_center_boundary :
    HasStrictNormalCrossingsWith (d.toBlowupSequenceData.toSequenceOfBlowups.projectionToBase i ≫ p) (d.toBlowupSequenceData.center i)
      (d.boundary i) := by
  have h := d.center_snc i hi
  rwa [d.projectionToBase_eq_toSequenceOfBlowups i] at h

theorem exceptionalIdeal_pow_mul_ideal_succ_eq_comap :
    exceptionalIdeal (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i)
          (show IdealSheafData (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt i) from d.toBlowupSequenceData.center i) ^ m *
        (show IdealSheafData (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt (i + 1)) from d.ideal (i + 1)) =
      comap (show IdealSheafData (d.toBlowupSequenceData.toSequenceOfBlowups.schemeAt i) from d.ideal i)
        (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) := by
  have key := d.ideal_succ i hi
  rwa [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i]

private theorem boundary_succ_eq_map_strictTransform_append :
    d.boundary (i + 1) =
      (d.boundary i).map
          (strictTransform (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) (d.toBlowupSequenceData.center i)) ++
        [exceptionalIdeal (d.toBlowupSequenceData.toSequenceOfBlowups.transitionMapSucc i) (d.toBlowupSequenceData.center i)] := by
  have key := d.boundary_succ i hi
  rwa [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i]
end
end

def toMarkedSequenceOfBlowups : MarkedSequenceOfBlowups p I m E where
  toSequenceOfBlowups := d.toBlowupSequenceData.toSequenceOfBlowups
  ideal := d.ideal
  boundary := d.boundary
  ideal_zero := d.ideal_zero
  boundary_zero := d.boundary_zero
  center_smooth := fun i hi => smooth_center_comp_projection d i hi
  center_snc := fun i hi => hasStrictNormalCrossingsWith_center_boundary d i hi
  center_order := fun i hi => (d.center_order i hi)
  ideal_succ := fun i hi => exceptionalIdeal_pow_mul_ideal_succ_eq_comap d i hi
  boundary_succ := fun i hi => boundary_succ_eq_map_strictTransform_append d i hi

@[simp]
theorem toMarkedSequence_toSequenceOfBlowups :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups = d.toBlowupSequenceData.toSequenceOfBlowups := rfl

@[simp]
theorem toMarkedSequence_length :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = d.toBlowupSequenceData.length := rfl

section
variable (i : ℕ)
theorem toMarkedSequence_schemeAt :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.schemeAt i = d.toBlowupSequenceData.obj i := rfl

@[simp]
theorem toMarkedSequence_ideal :
    d.toMarkedSequenceOfBlowups.ideal i = d.ideal i := rfl

@[simp]
theorem toMarkedSequence_boundary :
    d.toMarkedSequenceOfBlowups.boundary i = d.boundary i := rfl

@[simp]
theorem toMarkedSequence_center :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.center i = d.toBlowupSequenceData.center i := rfl

theorem toMarkedSequence_blowupMorphism :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i :=
  BlowupSequenceData.toSequenceOfBlowups_blowupMorphism d.toBlowupSequenceData i

theorem toMarkedSequence_projectionToBase :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.projectionToBase i = d.proj i :=
  (BlowupSequenceData.toSequenceOfBlowups_projectionToBase d.toBlowupSequenceData i).trans (d.projectionToBase_eq i).symm

@[simp]
theorem toMarkedSequence_projectionToSpec :
    d.toMarkedSequenceOfBlowups.projectionToSpec i = d.proj i ≫ p := by
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, toMarkedSequence_projectionToBase]
  rfl
end

@[simp]
theorem toMarkedSequence_lastIdeal :
    d.toMarkedSequenceOfBlowups.lastIdeal = d.ideal d.toBlowupSequenceData.length := rfl
end

section
variable (s : MarkedSequenceOfBlowups p I m E)
theorem toSequenceOfBlowups_projectionToBase_succ i :
    s.toSequenceOfBlowups.projectionToBase (i + 1) =
      (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups).map i ≫ s.toSequenceOfBlowups.projectionToBase i := by
  show s.toSequenceOfBlowups.projectionToBase (i + 1)
      = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i
  rw [blowupMorphism_eq_transitionMap, transitionMap_comp_projectionToBase]

def ofMarkedSequence : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups
  proj := fun i => s.toSequenceOfBlowups.projectionToBase i
  proj_zero := by
    have h1 : s.toSequenceOfBlowups.tower.map (homOfLE (le_refl (0 : ℕ))).op
        = 𝟙 (s.toSequenceOfBlowups.tower.obj (Opposite.op 0)) :=
      s.toSequenceOfBlowups.tower.map_id (Opposite.op 0)
    show s.toSequenceOfBlowups.projectionToBase 0 = s.toSequenceOfBlowups.isoZero.hom
    rw [projectionToBase_def, transitionMap_def, h1, id_comp]
  proj_succ := fun i => toSequenceOfBlowups_projectionToBase_succ s i
  ideal := s.ideal
  boundary := s.boundary
  ideal_zero := s.ideal_zero
  boundary_zero := s.boundary_zero
  center_order := fun i hi => s.center_order i hi
  center_smooth := fun i hi => s.center_smooth i hi
  center_snc := fun i hi => s.center_snc i hi
  ideal_succ := fun i hi => s.ideal_succ i hi
  boundary_succ := fun i hi => s.boundary_succ i hi

@[simp]
theorem blowupSequenceData_ofMarkedSequence :
    (ofMarkedSequence s).toBlowupSequenceData = BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups := rfl

@[simp]
theorem ofMarkedSequence_length :
    (ofMarkedSequence s).toBlowupSequenceData.length = s.toSequenceOfBlowups.length := rfl

section
variable (i : ℕ)
@[simp]
theorem ofMarkedSequence_projectionToBase :
    (ofMarkedSequence s).proj i = s.toSequenceOfBlowups.projectionToBase i := rfl

@[simp]
theorem ofMarkedSequence_blowupMorphism :
    (ofMarkedSequence s).toBlowupSequenceData.map i = s.toSequenceOfBlowups.transitionMapSucc i := rfl

@[simp]
theorem ofMarkedSequence_ideal :
    (ofMarkedSequence s).ideal i = s.ideal i := rfl

@[simp]
theorem ofMarkedSequence_boundary_apply :
    (ofMarkedSequence s).boundary i = s.boundary i := rfl

@[simp]
theorem ofMarkedSequence_center :
    (ofMarkedSequence s).toBlowupSequenceData.center i = s.toSequenceOfBlowups.center i := rfl
end
end

end MarkedBlowupSequenceData
abbrev MarkedSequenceOfBlowups.toBsd {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : IdealSheafData X} {m : ℕ} {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) := (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData

section
variable {k : Type} [Field k] {X : Sch} (p : X ⟶ Sp k) (I : ISD X) (m : ℕ) (E : Bdy X)
def emptyMarkedBlowupSequenceData : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := emptyBlowupSequenceData X
  proj := fun _ => 𝟙 X
  proj_zero := rfl
  proj_succ := fun _ => (id_comp _).symm
  ideal := fun _ => I
  boundary := fun _ => E
  ideal_zero := (comap_id I).symm
  boundary_zero := by simp [comap_id]
  center_order := fun i hi => absurd hi (not_lt_zero i)
  center_smooth := fun i hi => absurd hi (not_lt_zero i)
  center_snc := fun i hi => absurd hi (not_lt_zero i)
  ideal_succ := fun i hi => absurd hi (not_lt_zero i)
  boundary_succ := fun i hi => absurd hi (not_lt_zero i)

@[simp]
theorem emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData = emptyBlowupSequenceData X := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_length :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length = 0 := rfl

section
variable (i : ℕ)
@[simp]
theorem emptyMarkedBlowupSequenceData_schemeAt :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.obj i = X := rfl


@[simp]
theorem emptyMarkedBlowupSequenceData_projectionToBase :
    (emptyMarkedBlowupSequenceData p I m E).proj i = 𝟙 X := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_ideal :
    (emptyMarkedBlowupSequenceData p I m E).ideal i = I := rfl

@[simp]
theorem emptyMarkedBlowupSequenceData_boundary :
    (emptyMarkedBlowupSequenceData p I m E).boundary i = E := rfl
end
abbrev MarkedIdealWithBoundary.mbs (T : MarkedIdealWithBoundary) := MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary
abbrev MarkedIdealWithBoundary.embs (T : MarkedIdealWithBoundary) := emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary

@[simp]
theorem emptyMarkedBlowupSequenceData_toMarkedSequence_length :
    (emptyMarkedBlowupSequenceData p I m E).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length = 0 := rfl
end


def IrreducibleComponentsDisjointOfSmooth : Prop :=
  ∀ (k : Type) [Field k] (X : Sch) (p : X ⟶ Sp k),
    Smooth p →
    ∀ C1_ ∈ irreducibleComponents ↥X, ∀ C2_ ∈ irreducibleComponents ↥X,
      C1_ ≠ C2_ → Disjoint C1_ C2_

theorem irreducibleComponentsDisjointOfSmooth : IrreducibleComponentsDisjointOfSmooth := by
  intro k _ X p hp C1_ h1_ C2_ h2_ hne
  rw [disjoint_left]
  intro x hx1_ hx2_
  exact hne
    (irreducibleComponents_eq_of_stalk_isDomain X
      (isDomain_stalk_of_smooth p) h1_ h2_ hx1_ hx2_)

end FunctorialResolution.EmbeddedResolution
end
section
universe v

open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

open Order in
theorem topologicalKrullDim_eq_iSup_length {Z : Type} [TopologicalSpace Z] :
    topologicalKrullDim Z =
      ⨆ p : LTSeries (IrreducibleCloseds Z), (p.length : WithBot ENat) := rfl

section
variable {X : Type} [TopologicalSpace X]
section
variable {Y : Set X} (hY : IsClosed Y)
def irreducibleClosedsImageSubtypeVal
    (a : IrreducibleCloseds ↥Y) : IrreducibleCloseds X :=
  ⟨val '' a.1, a.2.image _ continuous_subtype_val.continuousOn,
    hY.isClosedMap_subtype_val _ a.3⟩

theorem coe_irreducibleClosedsImageVal
    a :
    ((irreducibleClosedsImageSubtypeVal hY a : IrreducibleCloseds X) : Set X) = val '' (a : Set ↥Y) := rfl

theorem strictMono_irreducibleClosedsImageVal : StrictMono (irreducibleClosedsImageSubtypeVal hY) := by
  intro a b hab
  refine lt_of_le_of_ne ?_ ?_
  rw [← coe_subset_coe, coe_irreducibleClosedsImageVal, coe_irreducibleClosedsImageVal]
  exact image_mono $ SetLike.coe_subset_coe.mpr hab.le
  intro h
  refine hab.ne $ coe_injective $ mpr_ image_injective Subtype.val_injective ?_
  rw [← coe_irreducibleClosedsImageVal hY a, ← coe_irreducibleClosedsImageVal hY b, h]
end

theorem exists_mem_irreducibleComponents_superset_of_isIrreducible {s}
    (hs : IsIrreducible s) :
    ∃ C, C ∈ irreducibleComponents X ∧ IsIrreducible C ∧ IsClosed C ∧ s ⊆ C := by
  obtain ⟨t, ht, hst, hmax⟩ := exists_preirreducible s hs.2
  have htirr : IsIrreducible t := ⟨hs.1.mono hst, ht⟩
  exact ⟨t, ⟨htirr, fun u hu htu => le_of_eq $ hmax u hu.2 htu⟩, htirr,
    closure_eq_iff_isClosed.mp $ hmax (closure t) ht.closure subset_closure, hst⟩
end

theorem nonempty_irreducibleCloseds {Z : Type} [TopologicalSpace Z] (z : Z) :
    Nonempty (IrreducibleCloseds Z) :=
  ⟨⟨closure {z}, ⟨⟨z, subset_closure rfl⟩, isPreirreducible_singleton.closure⟩,
    isClosed_closure⟩⟩

open Order in
theorem topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents
    {X : Type} [TopologicalSpace X] (Y : Set X) (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim X < ⊤) :
    topologicalKrullDim ↥Y < topologicalKrullDim X := by
  have key : ∀ p : LTSeries $ IrreducibleCloseds Y,
      (((p.length + 1 : ℕ) : ENat) : WithBot ENat) ≤ topologicalKrullDim X := by
    intro p
    let _a3 := LTSeries $ IrreducibleCloseds X
    obtain ⟨q, hqlen, hqlast⟩ :
        ∃ q : _a3,
          q.length = p.length ∧ q.last = irreducibleClosedsImageSubtypeVal hY p.last :=
      ⟨p.map (irreducibleClosedsImageSubtypeVal hY) $ strictMono_irreducibleClosedsImageVal hY, rfl, rfl⟩
    obtain ⟨C, hCmem, hCirr, hCcl, hsub⟩ := exists_mem_irreducibleComponents_superset_of_isIrreducible q.last.2
    let _s0 := (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X)
    have hlt : q.last < _s0 := by
      refine lt_of_le_of_ne (SetLike.coe_subset_coe.mp hsub) ?_
      intro h
      refine hcomp C hCmem ?_
      have hc : (_s0 : Set X) ⊆ Y := by
        rw [← h, hqlast]
        rw [coe_irreducibleClosedsImageVal]
        rintro x ⟨y, -, rfl⟩
        exact y.2
      exact hc
    let _a1 := (q.snoc _s0 hlt).length
    have hs1 : _a1 = q.length + 1 := rfl
    have hs2 : _a1 = p.length + 1 := by
      omega
    have h1 : (_a1 : WithBot ENat)
        ≤ ⨆ r : _a3, (r.length : WithBot ENat) :=
      le_iSup (fun r : _a3 => (r.length : WithBot ENat)) _
    rw [hs2] at h1
    rwa [topologicalKrullDim_eq_iSup_length, coe_natCast]
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨a0⟩ := nonempty_irreducibleCloseds (⟨y0, hy0⟩ : Y)
  have hp0 :=
    key ⟨0, fun _ => a0, fun i => i.elim0⟩
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    intro hb
    rw [hb] at hp0
    exact coe_ne_bot $ mp_ le_bot_iff hp0
  obtain ⟨e, he⟩ := mp_ ne_bot_iff_exists hbot
  have hetop : e ≠ ⊤ := by
    rintro rfl
    rw [← he] at hfin
    exact lt_irrefl _ hfin
  obtain ⟨N, hN⟩ := mp_ ne_top_iff_exists hetop
  have hD : topologicalKrullDim X = (((N : ℕ) : ENat) : WithBot ENat) := by
    rw [← he, ← hN]
  rw [hD] at hp0
  have hN1 : 1 ≤ N := by
    exact_mod_cast (mp_ coe_le_coe hp0)
  have hbound : (⨆ p : LTSeries $ IrreducibleCloseds Y, (p.length : WithBot ENat))
      ≤ (((N - 1 : ℕ) : ENat) : WithBot ENat) := by
    refine iSup_le fun p => ?_
    show ((p.length : ℕ) : WithBot ENat) ≤ (((N - 1 : ℕ) : ENat) : WithBot ENat)
    have hk := key p
    rw [hD] at hk
    have h3 : p.length + 1 ≤ N := by
      exact_mod_cast (mp_ coe_le_coe hk)
    have h4 : p.length ≤ N - 1 := by omega
    rw [← coe_natCast]
    exact mpr_ coe_le_coe $ by exact_mod_cast h4
  have h5 : N - 1 < N := by omega
  have h6 : (((N - 1 : ℕ)) : ENat) < ((N : ℕ) : ENat) := by exact_mod_cast h5
  rw [topologicalKrullDim_eq_iSup_length (Z := Y), hD]
  exact lt_of_le_of_lt hbound $ mpr_ coe_lt_coe h6

section
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
def irreducibleClosedsMapHomeomorph (a : IrreducibleCloseds X) : IrreducibleCloseds Y :=
  ⟨e '' a.1, a.2.image e e.continuous.continuousOn, e.isClosedMap _ a.3⟩

theorem coe_irreducibleClosedsMapOfHomeomorph a :
    ((irreducibleClosedsMapHomeomorph e a : IrreducibleCloseds Y) : Set Y) = e '' (a : Set X) := rfl

theorem strictMono_irreducibleClosedsMapOfHomeomorph : StrictMono (irreducibleClosedsMapHomeomorph e) := by
  intro a b hab
  refine lt_of_le_of_ne ?_ ?_
  rw [← coe_subset_coe, coe_irreducibleClosedsMapOfHomeomorph, coe_irreducibleClosedsMapOfHomeomorph]
  exact image_mono $ SetLike.coe_subset_coe.mpr hab.le
  intro h
  refine hab.ne $ coe_injective $ mpr_ image_injective e.injective ?_
  rw [← coe_irreducibleClosedsMapOfHomeomorph e a, ← coe_irreducibleClosedsMapOfHomeomorph e b, h]
end

open Order in
theorem topologicalKrullDim_le_of_homeomorph {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_length (Z := X), topologicalKrullDim_eq_iSup_length (Z := Y)]
  refine iSup_le fun p => ?_
  have h := le_iSup (fun r : LTSeries (IrreducibleCloseds Y) => (r.length : WithBot ENat))
    (p.map (irreducibleClosedsMapHomeomorph e) $ strictMono_irreducibleClosedsMapOfHomeomorph e)
  exact h

theorem topologicalKrullDim_eq_of_homeomorph {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm (topologicalKrullDim_le_of_homeomorph e) $ topologicalKrullDim_le_of_homeomorph e.symm

theorem withBotSuccToNat_lt_withBotSuccToNat {a b} (h : a < b) (hb : b < ⊤) :
    withBotSuccToNat a < withBotSuccToNat b := by
  induction b using recBotCoe with
  | bot => exact absurd h not_lt_bot
  | coe n =>
    have hn : n ≠ ⊤ := by
      rintro rfl
      exact lt_irrefl _ hb
    induction a using recBotCoe with
    | bot =>
      rw [withBotSuccToNat_bot, withBotSuccToNat_coe]
      omega
    | coe m =>
      have hmn := mp_ coe_lt_coe h
      obtain ⟨M, hM⟩ := mp_ ne_top_iff_exists $ ne_top_of_lt hmn
      obtain ⟨N, hN⟩ := mp_ ne_top_iff_exists hn
      subst hM
      subst hN
      rw [withBotSuccToNat_coe, withBotSuccToNat_coe]
      have hMN : M < N := by exact_mod_cast hmn
      have e1 : (M : ENat).toNat = M := by simp
      have e2 : (N : ENat).toNat = N := by simp
      omega


theorem krullDimSucc_lt_of_homeomorph_isClosed (X Z : Sch) (Y : Set ↥X)
    (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents ↥X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim ↥X < ⊤)
    (e : ↥Z ≃ₜ ↥Y) :
    krullDimSucc Z < krullDimSucc X := by
  have h := topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents Y hY hne hcomp
    hfin
  refine (fun _ _ h hfin => withBotSuccToNat_lt_withBotSuccToNat h hfin) Z X ?_ hfin
  rwa [topologicalKrullDim_eq_of_homeomorph e]

end FunctorialResolution.EmbeddedResolution
end
section
universe v

open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem topologicalKrullDim_lt_top_of_homeomorph {A B : Type}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (h : topologicalKrullDim B < ⊤) :
    topologicalKrullDim A < ⊤ := by
  rwa [topologicalKrullDim_eq_of_homeomorph e]

section
variable {X : Type} [TopologicalSpace X]
theorem subset_closure_inter_of_isPreirreducible
    {S V : Set X} (hS : IsPreirreducible S) (hV : IsOpen V) (hne : (S ∩ V).Nonempty) :
    S ⊆ closure (S ∩ V) := by
  intro s hs
  rw [mem_closure_iff]
  intro W hW hsW
  obtain ⟨y, hyS, hyW, hyV⟩ := hS W V hW hV ⟨s, hs, hsW⟩ hne
  exact ⟨y, hyW, hyS, hyV⟩

theorem eq_of_preimage_val_eq {W : Set X}
    (hW : IsOpen W) {C D : Set X} (hC : IsClosed C) (hD : IsIrreducible D) (hCsubD : C ⊆ D)
    (hne : (C ∩ W).Nonempty)
    (heq : (val ⁻¹' C : Set ↥W) = (val ⁻¹' D : Set ↥W)) : C = D := by
  refine subset_antisymm hCsubD ?_
  have h1 : D ∩ W ⊆ C := by
    rintro y ⟨hyD, hyW⟩
    have hy : (⟨y, hyW⟩ : W) ∈ (preimage val D) := hyD
    rwa [← heq] at hy
  obtain ⟨z, hzC, hzW⟩ := hne
  calc D ⊆ closure (D ∩ W) := subset_closure_inter_of_isPreirreducible hD.2 hW ⟨z, hCsubD hzC, hzW⟩
    _ ⊆ closure C := closure_mono h1
    _ = C := hC.closure_eq

section
variable {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ)
include hU hcov
theorem topologicalKrullDim_le_natCast_of_isOpenCover (n : ℕ)
    (h : ∀ i, topologicalKrullDim ↥(U i) ≤ (n : WithBot ENat)) :
    topologicalKrullDim X ≤ (n : WithBot ENat) :=
  by
    refine iSup_le ?_
    intro p
    obtain ⟨x, hx⟩ := (p 0).isIrreducible.1
    have hxU : x ∈ ⋃ i, U i := by rw [hcov]
                                  trivial
    obtain ⟨i, hi⟩ := mp_ mem_iUnion hxU
    have hsub :=
      fun j => SetLike.coe_subset_coe.mpr $ LTSeries.monotone p $ Fin.zero_le j
    let _a0 := U i
    let V : Fin (p.length + 1) → IrreducibleCloseds _a0 := fun j =>
      ⟨val ⁻¹' ((p j : IrreducibleCloseds X) : Set X),
        ⟨⟨⟨x, hi⟩, hsub j hx⟩, (p j).isIrreducible.2.preimage $ (hU i).isOpenEmbedding_subtypeVal⟩,
        (p j).isClosed.preimage continuous_subtype_val⟩
    have hstep : ∀ j : Fin p.length, V j.castSucc < V j.succ := by
      intro j
      have hlt := p.step j
      have hsubset : ((p j.castSucc : IrreducibleCloseds X) : Set X)
          ⊆ ((p j.succ : IrreducibleCloseds X) : Set X) :=
        SetLike.coe_subset_coe.mpr hlt.le
      have hle : V j.castSucc ≤ V j.succ := by
        refine SetLike.coe_subset_coe.mp ?_
        intro z hz
        exact hsubset hz
      refine lt_of_le_of_ne hle ?_
      intro hEq
      exact absurd (IrreducibleCloseds.ext (eq_of_preimage_val_eq (hU i) (p j.castSucc).isClosed (p j.succ).isIrreducible hsubset ⟨x, hsub _ hx, hi⟩ $ congrArg (fun s : IrreducibleCloseds _a0 => (s : Set _a0)) hEq)) hlt.ne
    let q : LTSeries $ IrreducibleCloseds _a0 := ⟨p.length, V, hstep⟩
    exact le_trans (Order.LTSeries.length_le_krullDim q) $ h i
end
end

theorem natCast_withBot_ne_top n : ((n : ℕ) : WithBot ENat) ≠ ⊤ := by
  intro hcontra
  have h2 := hcontra
  rw [← coe_natCast] at h2
  have h3 := WithBot.coe_injective h2
  simp at h3

theorem natCast_withBot_lt_top n : ((n : ℕ) : WithBot ENat) < ⊤ :=
  mpr_ lt_top_iff_ne_top $ natCast_withBot_ne_top n

theorem exists_le_natCast_of_lt_top {a} (h : a < ⊤) :
    ∃ n, a ≤ ((n : ℕ) : WithBot ENat) := by
  induction a using recBotCoe with
  | bot => exact ⟨0, bot_le⟩
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd h $ lt_irrefl _
    | coe n => exact ⟨n, le_rfl⟩

theorem topologicalKrullDim_lt_top_of_finite_isOpenCover {X : Type} [TopologicalSpace X]
    {ι : Type v} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) (h : ∀ i, topologicalKrullDim ↥(U i) < ⊤) :
    topologicalKrullDim X < ⊤ := by
  classical
  choose N hN using fun i => exists_le_natCast_of_lt_top $ h i
  have := ofFinite ι
  have hle : topologicalKrullDim X ≤ (((Finset.univ.sup N) : ℕ) : WithBot ENat) := by
    refine topologicalKrullDim_le_natCast_of_isOpenCover U hU hcov _ ?_
    intro i
    exact le_trans (hN i) $ mono_cast $ le_sup $ Finset.mem_univ i
  exact lt_of_le_of_lt hle $ natCast_withBot_lt_top _

theorem two_ne_zero_withBotENat : (2 : WithBot ENat) ≠ 0 := by
  intro h
  have h2 := WithBot.coe_injective h
  simp at h2

theorem two_mul_natCast_add_one (m : ℕ) :
    (2 : WithBot ENat) * ((m : ENat) : WithBot ENat) + 1 = (((2 * m + 1 : ℕ) : ENat) : WithBot ENat) := by
  have e2 : (2 : WithBot ENat) = ((2 : ENat) : WithBot ENat) := rfl
  have e1 : (1 : WithBot ENat) = ((1 : ENat) : WithBot ENat) := rfl
  rw [e2, e1, ← coe_mul, ← coe_add]
  congr 1

theorem two_mul_add_one_lt_top {a : WithBot ENat} (h : a ≠ ⊤) : 2 * a + 1 < ⊤ := by
  induction a using recBotCoe with
  | bot =>
    rw [mul_bot two_ne_zero_withBotENat, bot_add]
    exact bot_lt_top
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd rfl h
    | coe m =>
      exact lt_of_eq_of_lt (two_mul_natCast_add_one m) $ natCast_withBot_lt_top $ 2 * m + 1

section
variable (k : Type) [Field k]
theorem ringKrullDim_mvPolynomial_lt_top (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) < ⊤ := by
  induction n with
  | zero =>
    rw [ringKrullDim_eq_of_ringEquiv $ isEmptyRingEquiv k $ Fin 0,
      ringKrullDim_eq_zero_of_field k, ← cast_zero]
    exact natCast_withBot_lt_top 0
  | succ m ih =>
    rw [ringKrullDim_eq_of_ringEquiv (finSuccEquiv k m).toRingEquiv]
    exact lt_of_le_of_lt Polynomial.ringKrullDim_le $ two_mul_add_one_lt_top $ ne_of_lt ih

theorem topologicalKrullDim_primeSpectrum_lt_top (A : Type) [CommRing A]
    [Algebra k A] [FiniteType k A] : topologicalKrullDim (PrimeSpectrum A) < ⊤ := by
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  obtain ⟨n, ph_, hph⟩ :=
    iff_quotient_mvPolynomial''.mp ‹FiniteType k A›
  exact lt_of_le_of_lt (ringKrullDim_le_of_surjective ph_.toRingHom hph) $ ringKrullDim_mvPolynomial_lt_top k n

theorem topologicalKrullDim_spec_lt_top (R : CRC)
    [Algebra k R] [FiniteType k R] : topologicalKrullDim ↥(Spec R) < ⊤ :=
  topologicalKrullDim_primeSpectrum_lt_top k R
end

section
variable {k : Type} [Field k] {X : Sch} (f : X ⟶ Sp k) (hft : LocallyOfFiniteType f)
include hft
theorem topologicalKrullDim_affineOpen_lt_top {U : Opn X}
    (hU : IsAffineOpen U) : topologicalKrullDim ↥((U : Set ↥X)) < ⊤ := by
  have hle : U ≤ f ⁻¹ᵁ (⊤ : Opn $ Sp k) := le_top
  let _a0 := GSpecIso $ m10 k
  have hsurj : Function.Surjective (isoI _a0).hom := by
    intro y
    exact ⟨(isoH _a0).hom y, congrArg (fun ph_ => (m4 ph_) y) _a0.hom_inv_id⟩
  let _ :=
    RingHom.toAlgebra $ ((appLE f ⊤ U hle).hom).comp
      (_a0.inv).hom
  have : FiniteType k U.sec :=
    (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f hft ⟨⊤, isAffineOpen_top $ Sp k⟩ ⟨U, hU⟩ hle).comp $ RingHom.FiniteType.of_surjective _ hsurj
  exact topologicalKrullDim_lt_top_of_homeomorph (m207 hU.isoSpec) $ topologicalKrullDim_spec_lt_top k U.sec

theorem topologicalKrullDim_lt_top_of_finiteType (hqc : QuasiCompact f) :
    topologicalKrullDim ↥X < ⊤ := by
  classical
  have hcompact : IsCompact (univ : Set $ Sp k) := by
    simp
  have : CompactSpace X := by
    constructor
    simpa using (hqc.isCompact_preimage univ isOpen_univ hcompact)
  have hcov : ⋃ i : affO X, (i : Set X) = univ := by
    rw [← Opens.coe_iSup, iSup_affineOpens_eq_top X, coe_top]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : affO X => ((i : Opn X) : Set X))
    (fun i => (i : Opn X).isOpen) hcov.ge
  refine topologicalKrullDim_lt_top_of_finite_isOpenCover
    (ι := {i : affO X // i ∈ t})
    (fun i => ((i.1 : Opn X) : Set X)) (fun i => (i.1 : Opn X).isOpen) ?_ ?_
  refine eq_univ_of_univ_subset ?_
  intro x _
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp $ ht $ mem_univ x
  exact mpr_ mem_iUnion ⟨⟨i, hi⟩, hx⟩
  intro i
  exact topologicalKrullDim_affineOpen_lt_top f hft i.1.2
end

theorem MarkedIdealWithBoundary.IsAdmissible.topologicalKrullDim_lt_top {T : MarkedIdealWithBoundary} (hT : T.IsAdmissible) :
    topologicalKrullDim ↥T.scheme < ⊤ :=
  topologicalKrullDim_lt_top_of_finiteType T.structMap hT.locallyOfFiniteType hT.quasiCompact

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

mutual

inductive PrincipalizationCertificate {k : Type} [Field k] :
    ∀ (W : Sch), (W ⟶ Sp k) → IdealSheafData W → ℕ →
      Set ↥W → IdealSheafData W → Prop
  | memory {W : Sch} {p : W ⟶ Sp k} {I : IdealSheafData W} {m : ℕ}
      {Mem : Set ↥W} {Z : IdealSheafData W}
      (h : (support Z : Set ↥W) ⊆ Mem) :
      PrincipalizationCertificate W p I m Mem Z
  | large {W : Sch} {p : W ⟶ Sp k} {I : IdealSheafData W} {m : ℕ}
      {Mem : Set ↥W} {Z : IdealSheafData W}
      (hm : 2 ≤ m) :
      PrincipalizationCertificate W p I m Mem Z
  | toOrder {W : Sch} {p : W ⟶ Sp k} {I : IdealSheafData W} {m : ℕ}
      {Mem : Set ↥W} {Z : IdealSheafData W}
      (M N : IdealSheafData W) (mu_ : ℕ)
      (hI : I = M * N)
      (hM : (support M : Set ↥W) ⊆ Mem)
      (hmu : m ≤ mu_)
      (hZ : (support Z : Set ↥W) ⊆ orderAtLeastLocus N mu_)
      (hcert : OrderCertificate W p N mu_ Mem Z) :
      PrincipalizationCertificate W p I m Mem Z
  | localize {W : Sch} {p : W ⟶ Sp k} {I : IdealSheafData W} {m : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ support Z → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ support Z), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ support Z),
        PrincipalizationCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
          ((U z hz).ι.base ⁻¹' Mem) (comap Z (U z hz).ι)) :
      PrincipalizationCertificate W p I m Mem Z

inductive OrderCertificate {k : Type} [Field k] :
    ∀ (W : Sch), (W ⟶ Sp k) → IdealSheafData W → ℕ →
      Set ↥W → IdealSheafData W → Prop
  | memory {W : Sch} {p : W ⟶ Sp k} {N : IdealSheafData W} {mu_ : ℕ}
      {Mem : Set ↥W} {Z : IdealSheafData W}
      (h : (support Z : Set ↥W) ⊆ Mem) :
      OrderCertificate W p N mu_ Mem Z
  | large {W : Sch} {p : W ⟶ Sp k} {N : IdealSheafData W} {mu_ : ℕ}
      {Mem : Set ↥W} {Z : IdealSheafData W}
      (hmu : 2 ≤ mu_) :
      OrderCertificate W p N mu_ Mem Z
  | localize {W : Sch} {p : W ⟶ Sp k} {N : IdealSheafData W} {mu_ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ support Z → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ support Z), z ∈ U z hz)
      (hcert : ∀ (z : ↥W) (hz : z ∈ support Z),
        OrderCertificate (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) mu_
          ((U z hz).ι.base ⁻¹' Mem) (comap Z (U z hz).ι)) :
      OrderCertificate W p N mu_ Mem Z
  | descend {W : Sch} {p : W ⟶ Sp k} {N : IdealSheafData W} {mu_ : ℕ}
      {Mem : Set ↥W} {Z : W.IdealSheafData}
      (U : ∀ z : ↥W, z ∈ support Z → W.Opens)
      (hU : ∀ (z : ↥W) (hz : z ∈ support Z), z ∈ U z hz)
      (H : ∀ (z : ↥W) (hz : z ∈ support Z), (U z hz).toScheme.IdealSheafData)
      (hH : ∀ (z : ↥W) (hz : z ∈ support Z),
        IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
      (hNsubH : ∀ (z : ↥W) (hz : z ∈ support Z),
        ((support (comap N (U z hz).ι) : Set ↥(U z hz).toScheme)) ⊆
          (support (H z hz) : Set ↥(U z hz).toScheme))
      (hZH : ∀ (z : ↥W) (hz : z ∈ support Z),
        ((support (comap Z (U z hz).ι) : Set ↥(U z hz).toScheme)) ⊆
          (support (H z hz) : Set ↥(U z hz).toScheme))
      (J : ∀ (z : ↥W) (hz : z ∈ support Z), Option ((H z hz).subscheme.IdealSheafData))
      (hJnone : ∀ (z : ↥W) (hz : z ∈ support Z), J z hz = none →
        IsOpen ((H z hz).subschemeι.base ⁻¹'
          ((support (comap Z (U z hz).ι) : Set ↥(U z hz).toScheme))))
      (hJcomp : ∀ (z : ↥W) (hz : z ∈ support Z) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz → NonzeroOnComponents Jz)
      (hJloc : ∀ (z : ↥W) (hz : z ∈ support Z) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        ∀ x : ↥(H z hz).subscheme,
          ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
          ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
            comap Jz V.ι =
              ((comap (comap N (U z hz).ι) (H z hz).subschemeι)).comap V.ι)
      (hJcert : ∀ (z : ↥W) (hz : z ∈ support Z) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = some Jz →
        PrincipalizationCertificate (H z hz).subscheme ((H z hz).subschemeι ≫ (U z hz).ι ≫ p) Jz mu_
          (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
          (comap (comap Z (U z hz).ι) (H z hz).subschemeι)) :
      OrderCertificate W p N mu_ Mem Z

end

section
variable {k : Type} [Field k] (W) (p : W ⟶ Sp k)
theorem PrincipalizationCertificate.of_two_le I m Mem
    Z (hm : 2 ≤ m) :
    PrincipalizationCertificate W p I m Mem Z :=
  PrincipalizationCertificate.large hm

theorem OrderCertificate.of_two_le N mu_ Mem
    Z (hmu : 2 ≤ mu_) :
    OrderCertificate W p N mu_ Mem Z :=
  OrderCertificate.large hmu
end



section
variable {V W : Sch} (f : V ⟶ W) (D : ISD W)
noncomputable def comapSubscheme :
    subscheme (comap D f) ⟶ subscheme D :=
  subschemeMap (comap D f) D f (D.le_map_comap f)

theorem comapSubscheme_comp :
    comapSubscheme f D ≫ subschemeι D = subschemeι (comap D f) ≫ f := by
  simp [comapSubscheme]
end

structure OpenImmersionStability (k : Type) [Field k] : Prop where
  comap_nonzeroOnComponents :
    ∀ {V W : Sch} (f : V ⟶ W) [IsOpenImmersion f] (J : ISD W),
      NonzeroOnComponents J → NonzeroOnComponents (comap J f)
  isOpenImmersion_comapSubscheme :
    ∀ {V W : Sch} (f : V ⟶ W) [IsOpenImmersion f] (D : ISD W),
      IsOpenImmersion (comapSubscheme f D)
  comap_isSmoothDivisor :
    ∀ {V W : Sch} (f : V ⟶ W) [IsOpenImmersion f]
      (p : W ⟶ Sp k) (D : ISD W),
      IsSmoothDivisor p D → IsSmoothDivisor (f ≫ p) (comap D f)

section
variable {V W : Sch} (f : V ⟶ W)
theorem coe_support_comap (Z : ISD W) :
    (support (comap Z f) : Set ↥V) = ⇑f.base ⁻¹' ((support Z : Set ↥W)) :=by simp_all
section
variable (U' : Opn W) (Hd : U'.toScheme.IdealSheafData)
theorem support_comap_morphismRestrict_subset (K : ISD W)
    (h : (support (comap K U'.ι) : Set ↥U'.toScheme) ⊆ ((support Hd : Set ↥U'.toScheme))) :
    (((comap (comap K f) (f ⁻¹ᵁ U').ι).support : Set ↥(f ⁻¹ᵁ U').toScheme)) ⊆
      ((support (comap Hd (f ∣_ U')) : Set ↥(f ⁻¹ᵁ U').toScheme)) := by
  have e5 : comap (comap K f) (preU f U').i = comap (comap K U'.i) (f.mr U') := by
    rw [← comap_comp, ← comap_comp, morphismRestrict_ι ..]
  rw [e5, coe_support_comap (f.mr U') $ comap K U'.i, coe_support_comap (f.mr U') Hd]
  exact preimage_mono h
end
end

section
variable {k : Type} [Field k]
section
variable {A} {p1_ p2_ : A ⟶ Sp k}
private theorem principalizationCertificate_congr {I1 I2} {m}
    {Mem1 Mem2} {Z1 Z2}
    (h : PrincipalizationCertificate A p1_ I1 m Mem1 Z1) (hp : p1_ = p2_) (hI : I1 = I2) (hM : Mem1 = Mem2)
    (hZ : Z1 = Z2) : PrincipalizationCertificate A p2_ I2 m Mem2 Z2 :=by simp_all
private theorem orderCertificate_congr {N1 N2} {mu_}
    {Mem1 Mem2} {Z1 Z2}
    (h : OrderCertificate A p1_ N1 mu_ Mem1 Z1) (hp : p1_ = p2_) (hN : N1 = N2) (hM : Mem1 = Mem2)
    (hZ : Z1 = Z2) : OrderCertificate A p2_ N2 mu_ Mem2 Z2 :=by simp_all
end

section
variable (hin : OpenImmersionStability k) {V W : Sch}
include hin
theorem isSmoothDivisor_comap_morphismRestrict {p : W ⟶ Sp k} (f : V ⟶ W) [IsOpenImmersion f]
    (U' : Opn W) (Hd : U'.toScheme.IdealSheafData)
    (h : IsSmoothDivisor (U'.ι ≫ p) Hd) :
    IsSmoothDivisor ((f ⁻¹ᵁ U').ι ≫ (f ≫ p)) (Hd.comap (f ∣_ U')) := by
  have h2 := hin.comap_isSmoothDivisor (mrU f U') (opI U' ≫ p) Hd h
  rwa [← assoc, morphismRestrict_ι .., assoc] at h2

end

section
variable (W : Sch) (p : W ⟶ Sp k)
def IsPrincipalizationCertificateOnOpens (I : ISD W) (m : ℕ) (Mem : Set ↥W)
    (Z : ISD W) : Prop :=
  ∀ (V : Sch) (f : V ⟶ W), IsOpenImmersion f →
    PrincipalizationCertificate V (f ≫ p) (comap I f) m (⇑f.base ⁻¹' Mem) (comap Z f)

def IsOrderCertificateOnOpens (N : ISD W) (mu_ : ℕ) (Mem : Set ↥W)
    (Z : ISD W) : Prop :=
  ∀ (V : Sch) (f : V ⟶ W), IsOpenImmersion f →
    OrderCertificate V (f ≫ p) (comap N f) mu_ (⇑f.base ⁻¹' Mem) (comap Z f)
end

section
variable {W : Sch} {p : W ⟶ Sp k}
section
variable {I : ISD W} {m : ℕ} {Mem : Set ↥W} {Z : ISD W}
theorem comapPrincipalizationCertificate_of_mul_of_order (M N : ISD W) mu_ (hI : I = M * N)
    (hM : ((support M : Set ↥W)) ⊆ Mem) (hmu : m ≤ mu_)
    (hZ : ((support Z : Set ↥W)) ⊆ orderAtLeastLocus N mu_) (ih : IsOrderCertificateOnOpens W p N mu_ Mem Z) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f hf
  refine PrincipalizationCertificate.toOrder (cmI M f) (cmI N f) mu_ ?_ ?_ hmu ?_ $ ih V f hf
  rw [hI, comap_mul]
  rw [coe_support_comap]
  exact preimage_mono hM
  rw [coe_support_comap]
  intro y hy
  rw [mem_orderAtLeastLocus_iff]
  exact le_trans (mp_ (mem_orderAtLeastLocus_iff N mu_ $ bsM f y) $ hZ hy)
    (orderAt_le_orderAt_comap f N y)

theorem comapPrincipalizationCertificate_of_support_subset (h : ((support Z : Set ↥W)) ⊆ Mem) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f _hf
  refine PrincipalizationCertificate.memory ?_
  rw [coe_support_comap]
  exact preimage_mono h

theorem comapPrincipalizationCertificate_of_two_le (hm : 2 ≤ m) : IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f _hf
  exact PrincipalizationCertificate.large hm
end

section
variable {N : ISD W} {mu_ : ℕ} {Mem : Set ↥W} {Z : ISD W}
theorem comapOrderCertificate_of_support_subset (h : ((support Z : Set ↥W)) ⊆ Mem) :
    IsOrderCertificateOnOpens W p N mu_ Mem Z := by
  intro V f _hf
  refine OrderCertificate.memory ?_
  rw [coe_support_comap]
  exact preimage_mono h

theorem comapOrderCertificate_of_two_le (hmu : 2 ≤ mu_) : IsOrderCertificateOnOpens W p N mu_ Mem Z := by
  intro V f _hf
  exact OrderCertificate.large hmu
end
end
end

private theorem preimage_base_comp {A B C : Sch} (a : A ⟶ B) (b : B ⟶ C) (S : Set ↥C) :
    ⇑(a ≫ b).base ⁻¹' S = ⇑a.base ⁻¹' (⇑b.base ⁻¹' S) := by
  ext w
  exact m22

theorem preimage_base_preimage_base_of_comp_eq {A B C D : Sch} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (e : a ≫ b = c ≫ d) (S : Set ↥D) :
    ⇑a.base ⁻¹' (⇑b.base ⁻¹' S) = ⇑c.base ⁻¹' (⇑d.base ⁻¹' S) := by
  rw [← preimage_base_comp, ← preimage_base_comp, e]

section
variable {k : Type} [Field k]
section
variable {W : Sch} {p : W ⟶ Sp k}
theorem comapPrincipalizationCertificate_of_open_cover {I : ISD W} {m : ℕ} {Mem : Set ↥W}
    {Z : ISD W} (U : ∀ z : ↥W, z ∈ Z.support → Opn W)
    (hU : ∀ z hz, z ∈ U z hz)
    (ih : ∀ z hz,
      IsPrincipalizationCertificateOnOpens (U z hz).toScheme ((U z hz).ι ≫ p) (I.comap (U z hz).ι) m
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ y, y ∈ spI (cmI Z f) → bsM f y ∈ spI Z := by
    intro y hy
    have h1 : y ∈ (spI (cmI Z f) : Set V) := hy
    rwa [coe_support_comap] at h1
  refine PrincipalizationCertificate.localize (fun y hy => f ⁻¹ᵁ U (bsM f y) (hsup y hy))
    (fun y hy => hU _ _) ?_
  intro y hy
  have e1 : (f ∣_ U (bsM f y) (hsup y hy)) ≫ opI (U (bsM f y) (hsup y hy))
      = opI (f ⁻¹ᵁ U (bsM f y) (hsup y hy)) ≫ f := morphismRestrict_ι ..
  refine principalizationCertificate_congr (ih (bsM f y) (hsup y hy) _ (f ∣_ U (bsM f y) (hsup y hy))
    inferInstance) ?_ ?_ (preimage_base_preimage_base_of_comp_eq e1 Mem) ?_
  rw [← assoc, e1, assoc]
  rw [← comap_comp, ← comap_comp, e1]
  rw [← comap_comp, ← comap_comp, e1]

theorem comapOrderCertificate_of_open_cover {N : ISD W} {mu_ : ℕ} {Mem : Set ↥W}
    {Z : ISD W} (U : ∀ z : ↥W, z ∈ Z.support → Opn W)
    (hU : ∀ z hz, z ∈ U z hz)
    (ih : ∀ z hz,
      IsOrderCertificateOnOpens (U z hz).toScheme ((U z hz).ι ≫ p) (N.comap (U z hz).ι) mu_
        (⇑(U z hz).ι.base ⁻¹' Mem) (Z.comap (U z hz).ι)) :
    IsOrderCertificateOnOpens W p N mu_ Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ y, y ∈ spI (cmI Z f) → bsM f y ∈ spI Z := by
    intro y hy
    have h1 : y ∈ (spI (cmI Z f) : Set V) := hy
    rwa [coe_support_comap] at h1
  refine OrderCertificate.localize (fun y hy => f ⁻¹ᵁ U (bsM f y) (hsup y hy))
    (fun y hy => hU _ _) ?_
  intro y hy
  have e1 : (f ∣_ U (bsM f y) (hsup y hy)) ≫ opI (U (bsM f y) (hsup y hy))
      = opI (f ⁻¹ᵁ U (bsM f y) (hsup y hy)) ≫ f := morphismRestrict_ι ..
  refine orderCertificate_congr (ih (bsM f y) (hsup y hy) _ (f ∣_ U (bsM f y) (hsup y hy))
    inferInstance) ?_ ?_ (preimage_base_preimage_base_of_comp_eq e1 Mem) ?_
  rw [← assoc, e1, assoc]
  rw [← comap_comp, ← comap_comp, e1]
  rw [← comap_comp, ← comap_comp, e1]
end

end

section
variable {k : Type} [Field k]
section
variable (hin : OpenImmersionStability k) {W : Sch} {p : W ⟶ Sp k}
include hin
section
variable {N : ISD W} {mu_ : ℕ} {Mem : Set ↥W} {Z : ISD W}
theorem comapOrderCertificate_of_smoothDivisor_cover
    (U : ∀ z : ↥W, z ∈ Z.support → Opn W)
    (hU : ∀ z hz, z ∈ U z hz)
    (H : ∀ z hz, (U z hz).toScheme.IdealSheafData)
    (hH : ∀ z hz, IsSmoothDivisor ((U z hz).ι ≫ p) (H z hz))
    (hNsubH : ∀ z hz,
      (((N.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        (((H z hz).support : Set ↥(U z hz).toScheme)))
    (hZH : ∀ z hz,
      (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme)) ⊆
        (((H z hz).support : Set ↥(U z hz).toScheme)))
    (J : ∀ z hz, Option (H z hz).subscheme.IdealSheafData)
    (hJnone : ∀ z hz, J z hz = none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        (((Z.comap (U z hz).ι).support : Set ↥(U z hz).toScheme))))
    (hJcomp : ∀ z hz (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ z hz (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz → ∀ x : ↥(H z hz).subscheme,
        ((H z hz).subschemeι ≫ (U z hz).ι).base x ∉ Mem →
        ∃ V0 : (H z hz).subscheme.Opens, x ∈ V0 ∧
          Jz.comap V0.ι = ((N.comap (U z hz).ι).comap (H z hz).subschemeι).comap V0.ι)
    (ih : ∀ z hz (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = some Jz →
      IsPrincipalizationCertificateOnOpens (H z hz).subscheme ((H z hz).subschemeι ≫ ((U z hz).ι ≫ p)) Jz mu_
        (⇑((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem)
        ((Z.comap (U z hz).ι).comap (H z hz).subschemeι)) :
    IsOrderCertificateOnOpens W p N mu_ Mem Z := by
  intro V f hf
  have : IsOpenImmersion f := hf
  have hsup : ∀ y, y ∈ spI (cmI Z f) → bsM f y ∈ spI Z := by
    intro y hy
    have h1 : y ∈ (spI (cmI Z f) : Set V) := hy
    rwa [coe_support_comap] at h1
  refine OrderCertificate.descend (fun y hy => f ⁻¹ᵁ U (bsM f y) (hsup y hy))
    (fun y hy => hU _ _)
    (fun y hy => cmI (H (bsM f y) (hsup y hy)) (f ∣_ U (bsM f y) (hsup y hy)))
    (fun y hy => isSmoothDivisor_comap_morphismRestrict hin f (U (bsM f y) (hsup y hy))
      (H (bsM f y) (hsup y hy)) (hH _ _))
    (fun y hy => support_comap_morphismRestrict_subset f (U (bsM f y) (hsup y hy)) (H (bsM f y) (hsup y hy)) N
      (hNsubH _ _))
    (fun y hy => support_comap_morphismRestrict_subset f (U (bsM f y) (hsup y hy)) (H (bsM f y) (hsup y hy)) Z
      (hZH _ _))
    (fun y hy => (J (bsM f y) (hsup y hy)).map fun Jz =>
      Jz.comap (comapSubscheme (f ∣_ U (bsM f y) (hsup y hy)) (H (bsM f y) (hsup y hy))))
    ?_ ?_ ?_ ?_
  intro y hy hnone
  have hJn : J (bsM f y) (hsup y hy) = none := by simp_all
  let U' := U (bsM f y) $ hsup y hy
  let Hd := H (bsM f y) $ hsup y hy
  let K := Z
  have e1 : (f.mr U') ≫ U'.i = (preU f U').i ≫ f := morphismRestrict_ι ..
  have e5 : (K.comap f).comap (preU f U').i = (K.comap U'.i).comap (f.mr U') := by
    rw [← comap_comp, ← comap_comp, e1]
  rw [e5, coe_support_comap (f.mr U') $ K.comap U'.i,
    preimage_base_preimage_base_of_comp_eq (comapSubscheme_comp (mrU f U') Hd).symm
      (spI (cmI K U'.i) : Set U'.toScheme)]
  exact (hJnone _ _ hJn).preimage (comapSubscheme (mrU f U') Hd).base.hom.continuous
  intro y hy Jz' hsome
  cases hJ : J (bsM f y) (hsup y hy) with
  | none =>
      rw [hJ] at hsome
      simp at hsome
  | some Jz =>
      rw [hJ] at hsome
      have hJz := inj hsome
      subst hJz
      let U' := U (bsM f y) $ hsup y hy
      let Hd := H (bsM f y) $ hsup y hy
      have : IsOpenImmersion (comapSubscheme (mrU f U') Hd) :=
        hin.isOpenImmersion_comapSubscheme (mrU f U') Hd
      exact hin.comap_nonzeroOnComponents (comapSubscheme (mrU f U') Hd) Jz (hJcomp _ _ Jz hJ)
  intro y hy Jz' hsome x hx
  cases hJ : J (bsM f y) (hsup y hy) with
  | none =>
      rw [hJ] at hsome
      simp at hsome
  | some Jz =>
      rw [hJ] at hsome
      have hJz := inj hsome
      subst hJz
      let U' := U (bsM f y) $ hsup y hy
      let Hd := H (bsM f y) $ hsup y hy
      let _a0 := opI (preU f U')
      have e3 : comapSubscheme (mrU f U') Hd ≫ siI Hd ≫ opI U'
          = siI (cmI Hd (f.mr U')) ≫ _a0 ≫ f := by
        rw [← assoc, comapSubscheme_comp .., assoc, morphismRestrict_ι ..]
      have h9 : bsM (siI Hd ≫ opI U') (bsM (comapSubscheme (mrU f U') Hd) x)
          = bsM f (bsM (siI (cmI Hd (f.mr U')) ≫ _a0) x) :=
        congrArg (fun t : subS (cmI Hd (f.mr U')) ⟶ W => bsM t x) e3
      have hx' : bsM (siI Hd ≫ opI U') (bsM (comapSubscheme (mrU f U') Hd) x) ∉ Mem := by
        intro hmem
        apply hx
        show bsM f (bsM (siI (cmI Hd (f.mr U')) ≫ _a0) x) ∈ Mem
        rwa [← h9]
      obtain ⟨V0, hxV0, hV0⟩ := (hJloc _ _ Jz hJ) _ hx'
      refine ⟨(comapSubscheme (mrU f U') Hd) ⁻¹ᵁ V0, hxV0, ?_⟩
      have hc := congrArg (fun K => Scheme.IdealSheafData.comap K
          ((comapSubscheme (mrU f U') Hd) ∣_ V0)) hV0
      have e7 : opI ((comapSubscheme (mrU f U') Hd) ⁻¹ᵁ V0) ≫ comapSubscheme (mrU f U') Hd
          = ((comapSubscheme (mrU f U') Hd) ∣_ V0) ≫ opI V0 := sy_ (morphismRestrict_ι ..)
      simp only [← comap_comp] at hc ⊢
      rwa [e7, ← e3, ← assoc, e7, assoc]
  intro y hy Jz' hsome
  cases hJ : J (bsM f y) (hsup y hy) with
  | none =>
      rw [hJ] at hsome
      simp at hsome
  | some Jz =>
      rw [hJ] at hsome
      have hJz := inj hsome
      subst hJz
      let U' := U (bsM f y) $ hsup y hy
      let Hd := H (bsM f y) $ hsup y hy
      let _a0 := opI (preU f U')
      have e3 : comapSubscheme (mrU f U') Hd ≫ siI Hd ≫ opI U'
          = siI (cmI Hd (f.mr U')) ≫ _a0 ≫ f := by
        rw [← assoc, comapSubscheme_comp .., assoc, morphismRestrict_ι ..]
      have e3' : comapSubscheme (mrU f U') Hd ≫ (siI Hd ≫ opI U')
          = (siI (cmI Hd (f.mr U')) ≫ _a0) ≫ f := by simp_all
      refine principalizationCertificate_congr ((ih _ _ Jz hJ) _ (comapSubscheme (mrU f U') Hd) (hin.isOpenImmersion_comapSubscheme (mrU f U') Hd)) ?_ rfl (preimage_base_preimage_base_of_comp_eq e3' Mem) ?_
      have h5 := congrArg (fun t : subS (cmI Hd (mrU f U')) ⟶ W => t ≫ p) e3
      simpa only [assoc] using h5
      simp only [← comap_comp]
      rw [e3]

section
variable (h : OrderCertificate W p N mu_ Mem Z)
include h
theorem comapOrderCertificate_of_orderCertificate :
    IsOrderCertificateOnOpens W p N mu_ Mem Z :=
  OrderCertificate.rec (motive_1 := fun W p I m Mem Z _ => IsPrincipalizationCertificateOnOpens W p I m Mem Z)
    (motive_2 := fun W p N mu_ Mem Z _ => IsOrderCertificateOnOpens W p N mu_ Mem Z)
    comapPrincipalizationCertificate_of_support_subset
    comapPrincipalizationCertificate_of_two_le
    (fun M N mu_ hI hM hmu hZ _ ih => comapPrincipalizationCertificate_of_mul_of_order M N mu_ hI hM hmu hZ ih)
    (fun U hU _ ih => comapPrincipalizationCertificate_of_open_cover U hU ih)
    comapOrderCertificate_of_support_subset
    comapOrderCertificate_of_two_le
    (fun U hU _ ih => comapOrderCertificate_of_open_cover U hU ih)
    (fun U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih =>
      comapOrderCertificate_of_smoothDivisor_cover hin U hU H hH hNsubH hZH J hJnone hJcomp hJloc ih)
    h

theorem OrderCertificate.comap_of_isOpenImmersion
    {V} (f : V ⟶ W) [IsOpenImmersion f] :
    OrderCertificate V (f ≫ p) (comap N f) mu_ (f.base ⁻¹' Mem) (comap Z f) :=
  comapOrderCertificate_of_orderCertificate hin h V f inferInstance
end
end

section
variable {I : ISD W} {m} {Mem} {Z : ISD W} (h : PrincipalizationCertificate W p I m Mem Z)
include h
theorem comapPrincipalizationCertificate_of_principalizationCertificate :
    IsPrincipalizationCertificateOnOpens W p I m Mem Z :=
  PrincipalizationCertificate.rec (motive_1 := fun W p I m Mem Z _ => IsPrincipalizationCertificateOnOpens W p I m Mem Z)
    (motive_2 := fun W p N mu_ Mem Z _ => IsOrderCertificateOnOpens W p N mu_ Mem Z)
    comapPrincipalizationCertificate_of_support_subset
    comapPrincipalizationCertificate_of_two_le
    (fun M N mu_ hI hM hmu hZ _ ih => comapPrincipalizationCertificate_of_mul_of_order M N mu_ hI hM hmu hZ ih)
    (fun U hU _ ih => comapPrincipalizationCertificate_of_open_cover U hU ih)
    comapOrderCertificate_of_support_subset
    comapOrderCertificate_of_two_le
    (fun U hU _ ih => comapOrderCertificate_of_open_cover U hU ih)
    (fun U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih =>
      comapOrderCertificate_of_smoothDivisor_cover hin U hU H hH hNsubH hZH J hJnone hJcomp hJloc ih)
    h

theorem PrincipalizationCertificate.comap_of_openImmersionStability
    {V} (f : V ⟶ W) [IsOpenImmersion f] :
    PrincipalizationCertificate V (f ≫ p) (comap I f) m (f.base ⁻¹' Mem) (comap Z f) :=
  comapPrincipalizationCertificate_of_principalizationCertificate hin h V f inferInstance
end
end

theorem OrderCertificate.restrict {W : Sch}
    {p : W ⟶ Sp k} {N : ISD W} {mu_ : ℕ}
    {Mem : Set ↥W} {Z : ISD W} (h : OrderCertificate W p N mu_ Mem Z)
    (hin : OpenImmersionStability k) (U : Opn W) :
    OrderCertificate U.toScheme (U.i ≫ p) (N.comap U.i) mu_ (U.ib ⁻¹' Mem) (Z.comap U.i) :=
  h.comap_of_isOpenImmersion hin U.i
end


section
variable {k : Type} [Field k] {W : Sch} {p : W ⟶ Sp k}
section
variable {I : ISD W} {m : ℕ}
theorem forall_principalizationCertificate_of_subset
    {Mem} {Z} (h : PrincipalizationCertificate W p I m Mem Z) :
    ∀ Mem', Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W p I m Mem Z _ =>
      ∀ Mem', Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (motive_2 := fun W p N mu_ Mem Z _ =>
      ∀ Mem', Mem ⊆ Mem' → OrderCertificate W p N mu_ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  intro W p I m Mem Z hmem Mem' hsub
  exact PrincipalizationCertificate.memory $ m90 hmem hsub
  intro W p I m Mem Z hm Mem' _
  exact PrincipalizationCertificate.large hm
  intro W p I m Mem Z M N mu_ hI hM hmu hZ _ ih Mem' hsub
  exact PrincipalizationCertificate.toOrder M N mu_ hI (m90 hM hsub) hmu hZ $ ih Mem' hsub
  intro W p I m Mem Z U hU _ ih Mem' hsub
  refine PrincipalizationCertificate.localize U hU ?_
  intro z hz
  exact ih z hz (opIb (U z hz) ⁻¹' Mem') $ preimage_mono hsub
  intro W p N mu_ Mem Z hmem Mem' hsub
  exact OrderCertificate.memory $ m90 hmem hsub
  intro W p N mu_ Mem Z hmu Mem' _
  exact OrderCertificate.large hmu
  intro W p N mu_ Mem Z U hU _ ih Mem' hsub
  refine OrderCertificate.localize U hU ?_
  intro z hz
  exact ih z hz (opIb (U z hz) ⁻¹' Mem') $ preimage_mono hsub
  intro W p N mu_ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hsub
  refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
  intro z hz Jz hJz x hx
  exact hJloc z hz Jz hJz x fun hmem => hx $ hsub hmem
  intro z hz Jz hJz
  exact ih z hz Jz hJz (bsM (siI (H z hz) ≫ opI (U z hz)) ⁻¹' Mem')
    (preimage_mono hsub)

theorem principalizationCertificate_mono_of_subset
    {Mem Mem'} {Z} (hsub : Mem ⊆ Mem')
    (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p I m Mem' Z :=
  forall_principalizationCertificate_of_subset h Mem' hsub
end

section
variable {N : ISD W} {mu_ : ℕ}
theorem forall_orderCertificate_of_subset
    {Mem} {Z} (h : OrderCertificate W p N mu_ Mem Z) :
    ∀ Mem', Mem ⊆ Mem' → OrderCertificate W p N mu_ Mem' Z := by
  refine @OrderCertificate.rec k ‹Field k›
    (fun W p I m Mem Z _ => ∀ Mem', Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (fun W p N mu_ Mem Z _ => ∀ Mem', Mem ⊆ Mem' → OrderCertificate W p N mu_ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ W p N mu_ Mem Z h
  intro W p I m Mem Z hmem Mem' hs
  exact PrincipalizationCertificate.memory $ m90 hmem hs
  intro W p I m Mem Z hm Mem' _
  exact PrincipalizationCertificate.large hm
  intro W p I m Mem Z M N mu_ hI hM hmu hZ _ ih Mem' hs
  exact PrincipalizationCertificate.toOrder M N mu_ hI (m90 hM hs) hmu hZ $ ih Mem' hs
  intro W p I m Mem Z U hU _ ih Mem' hs
  exact PrincipalizationCertificate.localize U hU fun z hz =>
    ih z hz (opIb (U z hz) ⁻¹' Mem') $ preimage_mono hs
  intro W p N mu_ Mem Z hmem Mem' hs
  exact OrderCertificate.memory $ m90 hmem hs
  intro W p N mu_ Mem Z hmu Mem' _
  exact OrderCertificate.large hmu
  intro W p N mu_ Mem Z U hU _ ih Mem' hs
  exact OrderCertificate.localize U hU fun z hz =>
    ih z hz (opIb (U z hz) ⁻¹' Mem') $ preimage_mono hs
  intro W p N mu_ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hs
  refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
  intro z hz Jz hJ x hx
  exact hJloc z hz Jz hJ x fun hm => hx $ hs hm
  intro z hz Jz hJ
  exact ih z hz Jz hJ (bsM (siI (H z hz) ≫ opI (U z hz)) ⁻¹' Mem')
    (preimage_mono hs)

theorem orderCertificate_mono_of_subset
    {Mem Mem'} {Z} (hsub : Mem ⊆ Mem')
    (h : OrderCertificate W p N mu_ Mem Z) :
    OrderCertificate W p N mu_ Mem' Z :=
  forall_orderCertificate_of_subset h Mem' hsub
end
end


theorem isOpen_setOf_stalkIdeal_eq_bot {X : Sch} [IsLocallyNoetherian X]
    (J : ISD X) :
    IsOpen {x : ↥X | stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x))} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU⟩ : ∃ U : affO X, x ∈ (U : Opn X) := by
    refine mem_iSup.mp ?_
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  have :=
    m188 U
  obtain ⟨s, hs⟩ : (J.ideal U).FG := m187 $ J.ideal U
  have hzero : ∀ g ∈ s, (pGerm X U x hxU).hom g = 0 := by
    intro g hg
    have hgI : g ∈ J.ideal U := by
      rw [← hs]
      exact Submodule.subset_span $ mem_coe.mpr hg
    have hmem := germ_mem_stalkIdeal J x U hxU hgI
    rw [hx] at hmem
    simpa using hmem
  have hWex : ∀ g : (xSec X U), ∃ (W : Opn X) (i : W ⟶ U),
      x ∈ W ∧ (g ∈ s → (pMap X i.op).hom g = 0) := by
    intro g
    by_cases hg : g ∈ s
    obtain ⟨V, iV, hxV, hi⟩ :=
      X.toLocallyRingedSpace.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero
        U g ⟨x, hxU⟩ $ hzero g hg
    exact ⟨V, iV, hxV, fun _ => hi⟩
    exact ⟨U, 𝟙 _, hxU, fun h => absurd h hg⟩
  choose W i hxW hres using hWex
  refine ⟨opS U ∩
      ⋂ g ∈ s, ((W g) : Set X), ?_, (isOpen U).inter $ isOpen_biInter s.finite_toSet fun g _ => isOpen $ W g, ⟨hxU, Set.mem_iInter₂.mpr fun g _ => hxW g⟩⟩
  rintro y ⟨hyU, hyW⟩
  have hyW' := fun g hg =>
    Set.mem_iInter₂.mp hyW g $ mem_coe.mpr hg
  let _a0 := pGerm X U y hyU
  have hmain : ∀ g ∈ s, _a0.hom g = 0 := by
    intro g hg
    refine st_ (X.presheaf.germ_res_apply (i g) y (hyW' g hg) g) ?_
    rw [hres g hg, map_zero]
  show stalkIdeal J y = ⊥
  rw [stalkIdeal_eq_map_germ J y U hyU, ← le_bot_iff, map_le_iff_le_comap, ← hs,
    Submodule.span_le]
  intro g hg
  have hmem : _a0.hom g ∈
      (⊥ : Ideal $ stkX X y) := by simp_all
  simpa using hmem

section
variable (T : MarkedIdealWithBoundary) (hT : T.IsAdmissible)
include hT
theorem isLocallyNoetherian_of_isAdmissible :
    IsLocallyNoetherian T.scheme := by
  have := hT.locallyOfFiniteType
  have : IsNoetherianRing T.base := inferInstance
  constructor
  intro U
  exact @isNoetherianRing_sections T.base _ _ T.scheme T.structMap _ U
    (sectionsAlgebra T.base T.structMap U.1)
    (algebraMap_sectionsAlgebra T.base T.structMap U.1)

section
variable (J : T.scheme.IdealSheafData) (hJ : NonzeroOnComponents J)
include hJ
theorem stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents x :
    stalkIdeal J x ≠ ⊥ := by
  have := isLocallyNoetherian_of_isAdmissible T hT
  intro hbot
  obtain ⟨y, hyC, hyJ⟩ := mp_ not_subset
    (hJ (irreducibleComponent x) $ irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨z, hzC, hz1, hz2⟩ :=
    an2 isIrreducible_irreducibleComponent {w : T.scheme | stalkIdeal J w = ⊥} (J.supportᶜ)
      (isOpen_setOf_stalkIdeal_eq_bot J) J.support.2.isOpen_compl
      ⟨x, mem_irreducibleComponent, hbot⟩ ⟨y, hyC, hyJ⟩
  have hztop : stalkIdeal J z = ⊤ := by
    by_contra hne
    exact hz2 $ (mem_support_iff_stalkIdeal_ne_top J z).2 hne
  have h1 : 1 ∈ (⊥ : Ideal $ T.scheme.presheaf.stalk z) := by
    rw [← hz1, hztop]
    exact mem_top
  rw [mem_bot] at h1
  exact one_ne_zero h1

theorem exists_orderAt_le :
    ∃ B : ℕ, ∀ x : ↥T.scheme, orderAt J x ≤ (B : ENat) := by
  have := hT.charZero
  have := hT.smooth
  have := hT.locallyOfFiniteType
  have := isLocallyNoetherian_of_isAdmissible T hT
  have hfin := fun x =>
    orderAt_ne_top_of_stalkIdeal_ne_bot J x
      (stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents T hT J hJ x)
  have hclosed := fun m =>
    isClosed_orderAtLeastLocus T.base T.structMap J m
  have hspec : IsCompact (univ : Set $ Sp T.base) := by
    simp
  have hcpt := by
    simpa using (hT.quasiCompact.isCompact_preimage univ isOpen_univ hspec)
  have hempty : (univ : CSet T.scheme) ∩ (⋂ m : ℕ, orderAtLeastLocus J m) = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    rintro ⟨x, -, hx⟩
    have h1 := fun m => (mem_orderAtLeastLocus_iff J m x).1 $ (mp_ mem_iInter hx) m
    obtain ⟨n, hn⟩ : ∃ n : ℕ, orderAt J x = n :=
      ⟨(orderAt J x).toNat, sy_ $ natCast_toNat $ hfin x⟩
    have h3 : ((n + 1 : ℕ) : ENat) ≤ ((n : ℕ) : ENat) := by
      rw [← hn]
      exact h1 $ n + 1
    have h4 : n + 1 ≤ n := by exact_mod_cast h3
    omega
  obtain ⟨u, hu⟩ := hcpt.elim_finite_subfamily_closed (fun m : ℕ => orderAtLeastLocus J m) hclosed
    (mpr_ disjoint_iff_inter_eq_empty hempty)
  have hMempty : ¬ (univ ∩ ⋂ i ∈ u, orderAtLeastLocus J i).Nonempty := by
    rw [not_nonempty_iff_eq_empty]
    exact mp_ disjoint_iff_inter_eq_empty hu
  refine ⟨u.sup id, fun x => ?_⟩
  have hxnot : x ∉ orderAtLeastLocus J (u.sup id) := by
    intro hx
    refine hMempty ⟨x, mem_univ x, ?_⟩
    simp [mem_iInter]
    intro i hi
    exact orderAtLeastLocus_subset_of_le J (le_sup (f := id) hi) hx
  rw [mem_orderAtLeastLocus_iff] at hxnot
  exact le_of_lt $ mp_ not_le hxnot
end
end


variable (k : Type) [CommRing k] [IsNoetherianRing k] {X : Sch}
  (p) [LocallyOfFiniteType p]

section
variable (I : ISD X)
section
variable (m : ℕ)
def IsDerivBalanced : Prop :=
  ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)

theorem isDerivBalanced_iff :
    IsDerivBalanced k p I m ↔ ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  m22

noncomputable def maxContactIdeal : ISD X :=
  derivIdealSheafIterate k p (m - 1) I

theorem maxContactIdeal_ideal (U : X.affineOpens) :
    (maxContactIdeal k p I m).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (m - 1) (I.ideal U) :=
  derivIdealSheafIterate_ideal k p (m - 1) I U

@[simp] theorem maxContactIdeal_eq_derivIdealSheafIterate :
    maxContactIdeal k p I m = derivIdealSheafIterate k p (m - 1) I :=
  rfl

def IsMaxContactInvariant : Prop :=
  maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I
end

theorem isDerivBalanced_one : IsDerivBalanced k p I 1 := by
  intro i hi
  obtain rfl : i = 0 := mp_ lt_one_iff hi
  exact le_of_eq $ by rw [derivIdealSheafIterate_zero k p I, m130]

theorem maxContactIdeal_one : maxContactIdeal k p I 1 = I :=
  rfl
end

section
variable {I : ISD X} {m : ℕ}
theorem IsDerivBalanced.derivIdealSheafIterate_pow_le (h : IsDerivBalanced k p I m)
    {i} (hi : i < m) : derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  h i hi

theorem isDerivBalanced_of_pow_le
    (h : ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)) : IsDerivBalanced k p I m :=
  h

theorem isMaxContactInvariant_of_mul_le
    (h : maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I) : IsMaxContactInvariant k p I m :=
  h
end

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace

open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
theorem presheaf_map_op_eq_map_op {A B} (f g : B ⟶ A) :
    X.presheaf.map f.op = X.presheaf.map g.op := by
  rw [m111 f g]

section
variable (U : Opn X)
theorem topIso_inv_comp_hom :
    (U.topIso.inv.hom).comp (U.topIso.hom.hom) = RingHom.id _ := by
  rw [← hom_comp, m145, hom_id]

section
variable (h : (⊤ : (↑U : Sch).Opens) ≤ U.i ⁻¹ᵁ U)
theorem appLE_opensio_top_eq_topIso_inv :
    appLE U.i U ⊤ h = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  exact presheaf_map_op_eq_map_op _ _

theorem topIso_hom_comp_appLE_io :
    (U.topIso.hom.hom).comp ((appLE U.i U ⊤ h).hom) = RingHom.id _ := by
  rw [appLE_opensio_top_eq_topIso_inv, ← hom_comp, m114, hom_id]
end
end
end

theorem basis_det_D_update_eq_coeff {k S : Type} [CommRing k] [CommRing S] [Algebra k S]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S (KaehlerDifferential k S))
    (y : ι → S) (hb : ∀ i, b i = KaehlerDifferential.D k S (y i))
    (i0 : ι) (z : S) (a : ι → S)
    (hz : KaehlerDifferential.D k S z = ∑ i, a i • b i) :
    b.det (fun i => KaehlerDifferential.D k S (update y i0 z i)) = a i0 := by
  have hmat : b.toMatrix (fun i => m13 k S $ update y i0 z i)
      = Matrix.updateCol 1 i0 a := by
    ext i j
    rw [toMatrix_apply, Matrix.updateCol_apply]
    by_cases hj : j = i0
    subst hj
    rw [if_pos rfl, update_self, hz]
    simp [Finsupp.single_apply]
    rw [if_neg hj, update_of_ne hj, ← hb, Matrix.one_apply]
    simp [repr_self, Finsupp.single_apply, eq_comm]
  rw [det_apply, hmat, ← Matrix.cramer_apply]
  simp [Matrix.cramer_one]

section

theorem one_tmul_ne_zero_of_notMem_maximalIdeal_sq {A : Type} [CommRing A] [IsLocalRing A]
    a (ha : a ∈ maximalIdeal A)
    (ha2 : a ∉ maximalIdeal A ^ 2) :
    (1 : ResidueField A) ⊗ₜ[A]
      (⟨a, ha⟩ : ↥(maximalIdeal A)) ≠ 0 := by
  intro h
  apply ha2
  let _a3 := maximalIdeal A
  let _a0 := toSpanSingleton A (_a3 →ₗ[A] (maximalIdeal A).Cotangent) $ toCotangent $ maximalIdeal A
  have hker : maximalIdeal A ≤ m177
      _a0 := by
    intro b hb
    rw [LinearMap.mem_ker]
    ext y
    have hy : ((b • y) : A) ∈
        maximalIdeal A ^ 2 := by
      rw [pow_two]
      exact mul_mem_mul hb y.2
    have h0 :=
      (toCotangent_eq_zero (maximalIdeal A) $ b • y).mpr hy
    rw [map_smul] at h0
    show b • (toCotangent $ maximalIdeal A) y = 0
    exact h0
  have h' : (1 : A ⧸ maximalIdeal A) ⊗ₜ[A]
      (⟨a, ha⟩ : _a3) = 0 := h
  have key := congrArg (TensorProduct.lift
      (liftQ (maximalIdeal A) _ hker)) h'
  rw [TensorProduct.lift.tmul, map_zero] at key
  have h1 : (liftQ (maximalIdeal A)
      _a0 hker)
      (1 : A ⧸ maximalIdeal A)
      = toCotangent (maximalIdeal A) := by
    have e1 : (1 : A ⧸ maximalIdeal A) = Submodule.Quotient.mk (1 : A) := rfl
    rw [e1, liftQ_apply, toSpanSingleton_apply, one_smul]
  rw [h1] at key
  exact mp_ (toCotangent_eq_zero (maximalIdeal A) ⟨a, ha⟩) key

end

section

variable (k : Type) [Field k] {X : Sch} (p : X ⟶ Sp k)

theorem coordIdeal_singleton_le_restrictIdeal_iff {U : Opn X} (hU : IsAffineOpen U) {n}
    (c : EtaleChart p U n) j (J : ISD X) :
    c.coordIdeal {j} ≤ restrictIdeal J U ↔ c.coord j ∈ J.ideal ⟨U, hU⟩ := by
  let _c0 := (U : Sch)
  have : IsAffine _c0 := hU
  have htop : IsAffineOpen (⊤ : Opn _c0) := isAffineOpen_top _
  obtain ⟨t, htdef⟩ : ∃ t : Γ(_c0, ⊤), t = (c.map.appTop).hom
      (m9 (Sp k) $ up j) := ⟨_, rfl⟩
  have hcoord : c.coord j = U.topIso.hom.hom t := by rw [htdef]
                                                     rfl
  rw [coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord, restrictIdeal_eq_comap_io,
    comap_ofIdealTop]
  simp [map_span, image_singleton, coe_singleton]
  rw [← htdef]
  constructor
  intro h
  have h2 := h ⟨⊤, htop⟩
  rw [comap_ideal_eq_map_appLE J U.i ⟨U, hU⟩ ⟨⊤, htop⟩ $ by simp,
    ofIdealTop_ideal_top] at h2
  have hmem2 := mem_map_of_mem (U.topIso.hom.hom) $ h2 $ mem_span_singleton_self t
  rw [map_map, topIso_hom_comp_appLE_io U $ by simp, m167] at hmem2
  rwa [hcoord]
  intro h V
  rw [comap_ideal_eq_map_appLE J U.i ⟨U, hU⟩ V $ by simp,
    ofIdealTop_ideal, map_span, image_singleton,
    span_le, singleton_subset_iff]
  have hmorph : appLE U.i U (V : Opn _c0) (by simp)
      = U.topIso.inv ≫ pMap _c0
        (homOfLE (le_top : (V : Opn _c0) ≤ ⊤)).op := by
    rw [← appLE_opensio_top_eq_topIso_inv U $ by simp, appLE_map]
  rw [hmorph, hom_comp, ← map_map]
  refine mem_map_of_mem _ ?_
  have e2 : U.topIso.inv.hom (c.coord j) = t := by
    rw [hcoord]
    exact m156 (topIso_inv_comp_hom U) t
  rw [← e2]
  exact mem_map_of_mem _ h

variable [LocallyOfFiniteType p]

section
variable (I : ISD X)
section
variable (m : ℕ) {U : Opn X}
section
variable {n} (c : EtaleChart p U n) (j : Fin n)
def IsMaxContactCoord : Prop :=
  c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U

theorem isMaxContactCoord_iff :
    IsMaxContactCoord k p I m c j ↔
      c.coordIdeal {j} ≤ restrictIdeal (maxContactIdeal k p I m) U :=
  m22
end

theorem isMaxContactCoord_iff_coord_mem
    (hU : IsAffineOpen U) {n} (c : EtaleChart p U n) j :
    IsMaxContactCoord k p I m c j ↔ c.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩ :=
  coordIdeal_singleton_le_restrictIdeal_iff k p hU c j $ maxContactIdeal k p I m
end

theorem isMaxContactCoord_one_iff {U} {n}
    (c : EtaleChart p U n) j :
    IsMaxContactCoord k p I 1 c j ↔ c.coordIdeal {j} ≤ restrictIdeal I U := by
  rw [isMaxContactCoord_iff, maxContactIdeal_one k p I]
end

variable [CharZero k] [Smooth p]

section
variable (I : ISD X) {m : ℕ} (hm : 1 ≤ m)
include hm
section
variable {x : X}
theorem mem_support_maxContactIdeal_of_mem_orderAtLeastLocus (hx : x ∈ orderAtLeastLocus I m) :
    x ∈ support (maxContactIdeal k p I m) := by
  have h := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm
  have hx' : x ∈ (spI (derivIdealSheafIterate k p (m - 1) I) : Set X) := by simp_all
  exact hx'

section
variable (hx : orderAt I x = (m : ENat))
include hx
theorem orderAt_maxContactIdeal_eq_one :
    orderAt (maxContactIdeal k p I m) x = (1 : ENat) := by
  rw [maxContactIdeal_eq_derivIdealSheafIterate, orderAt_derivIdealSheafIterate_eq_sub k p I x hx $ sub_le m 1, show m - (m - 1) = 1 from by omega, cast_one]

theorem stalkIdeal_maxContactIdeal_le_maximalIdeal :
    stalkIdeal (maxContactIdeal k p I m) x ≤
      maximalIdeal ↑(X.presheaf.stalk x) := by
  have h2 := mp_ (le_orderAt_iff (maxContactIdeal k p I m) x 1) $ by rw [cast_one, orderAt_maxContactIdeal_eq_one k p I hm hx]
  rwa [pow_one] at h2

end
end

theorem exists_isMaxContactCoord (x : X)
    (hx : orderAt I x = (m : ENat)) :
    ∃ (U : Opn X) (_ : IsAffineOpen U) (hxU : x ∈ U) (n : ℕ) (c : EtaleChart p U n)
      (j : Fin n),
      IsMaxContactCoord k p I m c j ∧
        (X.presheaf.germ U x hxU).hom (c.coord j) ∈
          maximalIdeal ↑(X.presheaf.stalk x) := by
  let _a17 := maxContactIdeal k p I m
  classical
  obtain ⟨U, n, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  obtain ⟨s, hs, hs1, hs2⟩ : ∃ s ∈ _a17.ideal ⟨U, hU⟩, (pGerm X U x hxU).hom s ∈ maximalIdeal ↑(stkX X x) ∧ (pGerm X U x hxU).hom s ∉ maximalIdeal ↑(stkX X x) ^ 2 := by
    let _c0 := _a17
    have h1 : orderAt _c0 x = 1 :=
      orderAt_maxContactIdeal_eq_one k p I hm hx
    by_contra hno
    push Not at hno
    have h2 : stalkIdeal _c0 x ≤
        maximalIdeal ↑(stkX X x) ^ 2 := by
      rw [stalkIdeal_eq_map_germ _ x ⟨U, hU⟩ hxU, map_le_iff_le_comap]
      intro s hs
      simp [mem_comap]
      exact hno s hs $ (stalkIdeal_maxContactIdeal_le_maximalIdeal k p I hm hx) $ germ_mem_stalkIdeal _ x ⟨U, hU⟩ hxU hs
    have h3 := (le_orderAt_iff _c0 x 2).mpr h2
    rw [h1] at h3
    simp at h3
  let _instSections := sectionsAlgebra k p U
  let _s0 := UFin n
  let _instChart := c.algebra
  let _a9 := MvPolynomial _s0 k
  have : IsScalarTower k _a9 U.sec := c.isScalarTower
  have : FormallyEtale _a9 U.sec :=
    c.algebra_formallyEtale hU
  let _instStalk := stalkAlgebra k p x
  let _instGerm :=
    (pGerm X U x hxU).hom.toAlgebra
  let _a13 := algebraMap_sectionsAlgebra k p U
  have : IsScalarTower k U.sec ↑(stkX X x) :=
    isScalarTower_stalk k p U x hxU _a13
      (algebraMap_stalkAlgebra k p x) rfl
  have : IsNoetherianRing ↑(stkX X x) := isNoetherianRing_stalk k p x
  have : FormallySmooth k ↑(stkX X x) := formallySmooth_stalk k p x
  have : Module.Finite ↑(stkX X x) $ KaehlerDifferential k ↑(stkX X x) :=
    finite_kaehlerDifferential_stalk k p x
  have : Module.Free ↑(stkX X x) $ KaehlerDifferential k ↑(stkX X x) :=
    free_kaehlerDifferential_stalk k p x
  let _instResidue :=
    ((residue ↑(stkX X x)).comp $ stalkAlgebraMap k p x).toAlgebra
  have : IsScalarTower k ↑(stkX X x)
      (ResidueField ↑(stkX X x)) :=
    of_algebraMap_eq fun _ => rfl
  have : FormallySmooth k $ ResidueField ↑(stkX X x) :=
    formallySmooth_residueField k p x rfl
  have hli : LinearIndependent (ResidueField ↑(stkX X x)) fun _ : Fin 1 => (1 : ResidueField ↑(stkX X x)) ⊗ₜ[↑(stkX X x)] m13 k ↑(stkX X x) ((pGerm X U x hxU).hom s) := by
    let A := ↑(stkX X x)
    let a := (pGerm X U x hxU).hom s
    refine linearIndependent_tensor_D_of_maximalIdeal k A
      (fun _ : Fin 1 => (⟨a, hs1⟩ : ↥(maximalIdeal A))) ?_
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_one] at hg
    rcases smul_eq_zero.mp hg with hzero | hzero
    rwa [m111 i 0]
    exact absurd hzero $ one_tmul_ne_zero_of_notMem_maximalIdeal_sq a hs1 hs2
  let _a0 := basisKaehler k _s0 $ X.sec U
  obtain ⟨a, ha⟩ : ∃ a : UFin n → X.sec U, ∀ i,
      a i = _a0.repr
        (m13 k U.sec s) i := ⟨_, fun i => rfl⟩
  have hrepr : m13 k U.sec s
      = ∑ i, a i • (basisKaehler k _s0 U.sec i) := by
    have h := (sum_repr
      _a0
      (m13 k U.sec s)).symm
    simpa only [← ha] using h
  have hex : ∃ i : UFin n, IsUnit $ (pGerm X U x hxU).hom $ a i := by
    by_contra hcon
    push Not at hcon
    apply hli.ne_zero 0
    show (1 : ResidueField ↑(stkX X x)) ⊗ₜ[↑(stkX X x)]
      m13 k ↑(stkX X x)
        (algebraMap U.sec ↑(stkX X x) s) = 0
    have h0 : m13 k ↑(stkX X x)
        (algebraMap U.sec ↑(stkX X x) s)
        = ∑ i, (m132 k k U.sec ↑(stkX X x))
            (a i • (basisKaehler k _s0 U.sec i)) := by
      rw [← map_D k k U.sec ↑(stkX X x) s, hrepr, map_sum]
    rw [h0, tmul_sum]
    refine sum_eq_zero fun i _ => ?_
    let _a6 := (pGerm X U x hxU).hom $ a i
    have h1 : (m132 k k U.sec ↑(stkX X x))
        (a i • (basisKaehler k _s0 U.sec i))
        = _a6 •
          (m132 k k U.sec ↑(stkX X x))
            (basisKaehler k _s0 U.sec i) := by
      rw [map_smul]
      exact (algebraMap_smul (↑(stkX X x)) (a i) _).symm
    rw [h1, ← smul_tmul]
    have h2 : _a6 •
        (1 : ResidueField ↑(stkX X x)) = 0 := by
      rw [smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq,
        residue_eq_zero_iff]
      exact (mem_maximalIdeal _).mpr $ mem_nonunits_iff.mpr $ hcon i
    rw [h2, zero_tmul]
  obtain ⟨i0, hunit⟩ := hex
  have hV := hU.basicOpen $ a i0
  have hxV :=
    (X.toLocallyRingedSpace.toRingedSpace.mem_basicOpen (a i0) x hxU).mpr hunit
  let _instBasicOpen :=
    sectionsAlgebra k p $ bOpn X $ a i0
  let _instRestrict :=
    (pMap X (homOfLE $ X.basicOpen_le $ a i0).op).hom.toAlgebra
  let _a2 := algebraMap_sectionsAlgebra k p $ bOpn X $ a i0
  have : IsScalarTower k U.sec Γ(X, bOpn X $ a i0) :=
    isScalarTower_sections k p U (a i0) _a13
      _a2 rfl
  have : m215 (a i0) Γ(X, bOpn X $ a i0) :=
    hU.isLocalization_basicOpen $ a i0
  let _a14 := powers $ a i0
  have : FormallyEtale U.sec Γ(X, bOpn X $ a i0) :=
    Algebra.FormallyEtale.of_isLocalization _a14
  have : FormallySmooth k Γ(X, bOpn X $ a i0) :=
    formallySmooth_sections k p (bOpn X $ a i0) hV
      _a2
  obtain ⟨e, he⟩ : ∃ e : Module.Basis _s0 Γ(X, bOpn X $ a i0)
      (KaehlerDifferential k Γ(X, bOpn X $ a i0)),
      e = JacobianCriterion.inducedBasis k _s0 U.sec
        Γ(X, bOpn X $ a i0)
        _a0 := ⟨_, rfl⟩
  have he_apply : ∀ i, e i = m132 k k U.sec Γ(X, bOpn X $ a i0)
      (basisKaehler k _s0 U.sec i) := by
    intro i
    rw [he]
    exact JacobianCriterion.inducedBasis_apply k _s0 U.sec
      Γ(X, bOpn X $ a i0)
      _a0 i
  have hbT : ∀ i, e i = m13 k Γ(X, bOpn X $ a i0)
      (algebraMap U.sec Γ(X, bOpn X $ a i0)
        (p10 k _s0 U.sec i)) := by
    intro i
    rw [he]
    exact JacobianCriterion.inducedBasis_apply_D k _s0 U.sec
      Γ(X, bOpn X $ a i0)
      _a0
      (p10 k _s0 U.sec)
      (basisKaehler_apply k _s0 U.sec) i
  have hz : m13 k Γ(X, bOpn X $ a i0)
      (algebraMap U.sec Γ(X, bOpn X $ a i0) s)
      = ∑ i, (algebraMap U.sec Γ(X, bOpn X $ a i0) $ a i) • e i := by
    rw [← map_D k k U.sec Γ(X, bOpn X $ a i0) s, hrepr, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [map_smul, he_apply i, algebraMap_smul]
  let _a7 := Γ(X, bOpn X $ a i0)
  obtain ⟨w, hw⟩ : ∃ w : UFin n → _a7,
      w = update (fun i => algebraMap U.sec Γ(X, bOpn X $ a i0)
        (p10 k _s0 U.sec i)) i0
        (algebraMap U.sec Γ(X, bOpn X $ a i0) s) := ⟨_, rfl⟩
  have hdet0 : (e.det fun i => m13 k Γ(X, bOpn X $ a i0) $ w i)
      = algebraMap U.sec Γ(X, bOpn X $ a i0) (a i0) := by
    rw [hw]
    exact basis_det_D_update_eq_coeff e _ hbT i0 _
      (fun i => algebraMap U.sec Γ(X, bOpn X $ a i0) $ a i) hz
  have hdet : IsUnit $ e.det fun i => m13 k Γ(X, bOpn X $ a i0) $ w i := by
    rw [hdet0]
    exact IsLocalization.map_units Γ(X, bOpn X $ a i0)
      (⟨a i0, mem_powers _⟩ : _a14)
  let _a3 := (aeval w : _a9 →ₐ[k] Γ(X, bOpn X $ a i0))
  obtain ⟨f, hf⟩ : ∃ f : RingHom _a9 _a7,
      f = _a3.toRingHom := ⟨_, rfl⟩
  have hC : ∀ b : k, f (m8 b) = sectionsAlgebraMap k p (bOpn X $ a i0) b := by
    intro b
    rw [hf]
    show aeval w (m8 b) = _
    rw [aeval_C, algebraMap_sectionsAlgebra]
  have hXc : ∀ i : UFin n, f (m7 i) = w i := by
    intro i
    rw [hf]
    show aeval w (m7 i) = _
    rw [aeval_X]
  have hfet : f.Etale := by
    subst hf
    let inst :=
      _a3.toRingHom.toAlgebra
    have : @FormallyEtale _a9
        Γ(X, bOpn X $ a i0) _ _ inst :=
      formallyEtale_aeval_of_isUnit_det e w hdet
    have : IsScalarTower k _a9
        Γ(X, bOpn X $ a i0) :=
      of_algebraMap_eq fun r => (hC r).symm
    have : FiniteType k Γ(X, bOpn X $ a i0) :=
      finiteType_sections k p ⟨bOpn X $ a i0, hV⟩
        _a2
    have : FiniteType _a9
        Γ(X, bOpn X $ a i0) :=
      of_restrictScalars_finiteType k
        _a9 Γ(X, bOpn X $ a i0)
    have : FinitePresentation _a9
        Γ(X, bOpn X $ a i0) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ :
      m121 _a9 Γ(X, bOpn X $ a i0))
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p hV w f hC hXc hfet
  have hwi : w (up i0.down) = algebraMap U.sec Γ(X, bOpn X $ a i0) s := by
    rw [ULift.up_down, hw, update_self]
  refine ⟨bOpn X $ a i0, hV, hxV, n, c', i0.down, ?_, ?_⟩
  rw [isMaxContactCoord_iff_coord_mem k p I m hV c' i0.down, hc' i0.down, hwi]
  let _a12 := _a17
  have h2 : m6 ((pMap X (homOfLE $ X.basicOpen_le $ a i0).op).hom)
      (_a12.ideal ⟨U, hU⟩)
      = _a12.ideal ⟨bOpn X $ a i0, hV⟩ :=
    map_ideal_basicOpen _ ⟨U, hU⟩ $ a i0
  rw [← h2]
  exact mem_map_of_mem _ hs
  rw [hc' i0.down, hwi]
  have h3 := m156 (congrArg m4
    (X.presheaf.germ_res (homOfLE $ X.basicOpen_le $ a i0) x hxV)) s
  simp [hom_comp, coe_comp] at h3
  have h4 : (pGerm X (bOpn X $ a i0) x hxV).hom
      (algebraMap U.sec Γ(X, bOpn X $ a i0) s)
      = (pGerm X U x hxU).hom s := h3
  rwa [h4]
end

end

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

section

variable (k : Type) [Field k] {X : Sch} (p)
  [LocallyOfFiniteType p]

section
variable (A : ISD X) (m : ℕ) (H : ISD X)
def IsMaxContactHypersurface : Prop :=
  ∀ x : X, ∃ U : Opn X, IsAffineOpen U ∧ x ∈ U ∧
    ((Disjoint (orderAtLeastLocus A m) (U : Set ↥X) ∧ restrictIdeal H U = ⊤) ∨
      (∃ (n : ℕ) (c : EtaleChart p U n) (j : Fin n),
        restrictIdeal H U = c.coordIdeal {j} ∧ IsMaxContactCoord k p A m c j))

theorem isMaxContactHypersurface_iff :
    IsMaxContactHypersurface k p A m H ↔
      ∀ x : X, ∃ U : Opn X, IsAffineOpen U ∧ x ∈ U ∧
        ((Disjoint (orderAtLeastLocus A m) (U : Set ↥X) ∧ restrictIdeal H U = ⊤) ∨
          (∃ (n : ℕ) (c : EtaleChart p U n) (j : Fin n),
            restrictIdeal H U = c.coordIdeal {j} ∧ IsMaxContactCoord k p A m c j)) :=
  m22
end

end

section

variable {k : Type} [Field k] [CharZero k] {X : Sch}
  {p} [LocallyOfFiniteType p] [Smooth p]

theorem IsMaxContactHypersurface.orderAtLeastLocus_subset_support {A} {m}
    {H : ISD X} (h : IsMaxContactHypersurface k p A m H) (hm : 1 ≤ m) :
    orderAtLeastLocus A m ⊆ (H.support : Set ↥X) := by
  intro x hx
  obtain ⟨U, hU, hxU, hcase⟩ := h x
  rcases hcase with ⟨hdisj, -⟩ | ⟨n, c, j, hH, hmc⟩
  exact absurd hxU $ Set.disjoint_left.mp hdisj hx
  have hmem :=
    (isMaxContactCoord_iff_coord_mem k p A m hU c j).mp hmc
  let _a0 := maxContactIdeal k p A m
  have hle : H.ideal ⟨U, hU⟩ ≤ _a0.ideal ⟨U, hU⟩ := by
    rw [c.ideal_eq_span_coord hU H {j} hH, coe_singleton, image_singleton, span_le,
      singleton_subset_iff]
    exact hmem
  have hst : stalkIdeal H x ≤ stalkIdeal _a0 x := by
    rw [stalkIdeal_eq_map_germ H x ⟨U, hU⟩ hxU,
      stalkIdeal_eq_map_germ _a0 x ⟨U, hU⟩ hxU]
    exact Ideal.map_mono hle
  have hx' :=
    mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k p A hm hx
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal] at hx'
  have hfin := hst.trans hx'
  rwa [← mem_support_iff_stalkIdeal_le_maximalIdeal] at hfin

end

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section

variable {k : Type} [Field k] [CharZero k] {X : Sch}
  {p : X ⟶ Sp k} [LocallyOfFiniteType p] [Smooth p]

theorem ideal_le_of_ideal_le_of_le (k : Type) [Field k] {X : Sch}
    (p : X ⟶ Sp k) [LocallyOfFiniteType p] (D E : ISD X)
    {U V : Opn X} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (hDleE : D.ideal ⟨U, hU⟩ ≤ E.ideal ⟨U, hU⟩) : D.ideal ⟨V, hV⟩ ≤ E.ideal ⟨V, hV⟩ := by
  let _ := sectionsAlgebra k p U
  have :=
    isNoetherianRing_sections k p ⟨U, hU⟩ $ algebraMap_sectionsAlgebra k p U
  let _a0 := D.ideal ⟨U, hU⟩
  obtain ⟨s, hs⟩ : _a0.FG := m187 _
  have hs' := hs
  rw [ideal_eq_span_image_map_of_le D hU hV h (s : Set U.sec) hs'.symm, span_le]
  rintro _ ⟨y, hy, rfl⟩
  have hyD : y ∈ _a0 := by
    rw [← hs']
    exact subset_span hy
  exact (E.ideal_le_comap_ideal h) $ hDleE hyD

theorem restrictIdeal_eq_coordIdeal_of_coord_eq {X : Sch} {k : Type} [Field k]
    {p : X ⟶ Sp k} {V : Opn X} (hV : IsAffineOpen V) {n : ℕ}
    (c c' : EtaleChart p V n) (j : Fin n) (hcoord : c'.coord j = c.coord j)
    (D : ISD X) (hD : restrictIdeal D V = c.coordIdeal {j}) :
    restrictIdeal D V = c'.coordIdeal {j} := by
  refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV c' D {j} ?_
  rw [c.ideal_eq_span_coord hV D {j} hD, coe_singleton, image_singleton, image_singleton, hcoord]

theorem exists_common_charts_of_isMaxContactHypersurface (A : ISD X) {mu_}
    (hmu_ : 1 ≤ mu_) (N : Bdy X) (H1_ H2_ : ISD X)
    (hsnc1_ : InStrictNormalCrossingPosition p (H1_ :: N)) (hsnc2_ : InStrictNormalCrossingPosition p (H2_ :: N))
    (hadm1_ : IsMaxContactHypersurface k p A mu_ H1_)
    (hadm2_ : IsMaxContactHypersurface k p A mu_ H2_)
    (x : X) (hx : x ∈ orderAtLeastLocus A mu_) :
    ∃ (V : Opn X) (_ : IsAffineOpen V) (hxV : x ∈ V) (n : ℕ) (c1_ : EtaleChart p V n)
      (c2_ : EtaleChart p V n) (ga_ : ℕ → Option (Fin n)) (j0_ : Fin n),
      restrictIdeal H1_ V = c1_.coordIdeal {j0_} ∧
      restrictIdeal H2_ V = c2_.coordIdeal {j0_} ∧
      IsMaxContactCoord k p A mu_ c1_ j0_ ∧
      IsMaxContactCoord k p A mu_ c2_ j0_ ∧
      (X.presheaf.germ V x hxV).hom (c1_.coord j0_) ∈
        maximalIdeal ↑(X.presheaf.stalk x) ∧
      (X.presheaf.germ V x hxV).hom (c2_.coord j0_) ∈
        maximalIdeal ↑(X.presheaf.stalk x) ∧
      (∀ j, j ≠ j0_ → c2_.coord j = c1_.coord j) ∧
      (∀ i, ∀ hi,
        (ga_ i = none → restrictIdeal (N[i]'hi) V = ⊤) ∧
          ∀ j, ga_ i = some j → restrictIdeal (N[i]'hi) V = c1_.coordIdeal {j}) ∧
      (∀ i i', i < N.length → i' < N.length → ∀ j,
        ga_ i = some j → ga_ i' = some j → i = i') ∧
      (∀ i, ga_ i ≠ some j0_) := by
  classical
  have hxH1 := hadm1_.orderAtLeastLocus_subset_support hmu_ hx
  have hxH2 : x ∈ spI H2_ := hadm2_.orderAtLeastLocus_subset_support hmu_ hx
  obtain ⟨U1_, hU1, hxU1, hcase1⟩ := (isMaxContactHypersurface_iff k p A mu_ H1_).mp hadm1_ x
  obtain ⟨n1_, d1, i1_, hH1U1, hmc1⟩ :
      ∃ (n : ℕ) (c : EtaleChart p U1_ n) (j : Fin n),
        restrictIdeal H1_ U1_ = c.coordIdeal {j} ∧ IsMaxContactCoord k p A mu_ c j := by
    rcases hcase1 with ⟨hdisj, -⟩ | hc
    exact absurd hxU1 $ Set.disjoint_left.mp hdisj hx
    exact hc
  obtain ⟨U2_, hU2_, hxU2, hcase2⟩ := (isMaxContactHypersurface_iff k p A mu_ H2_).mp hadm2_ x
  obtain ⟨n2_, d2, i2_, hH2U2, hmc2⟩ :
      ∃ (n : ℕ) (c : EtaleChart p U2_ n) (j : Fin n),
        restrictIdeal H2_ U2_ = c.coordIdeal {j} ∧ IsMaxContactCoord k p A mu_ c j := by
    rcases hcase2 with ⟨hdisj, -⟩ | hc
    exact absurd hxU2 $ Set.disjoint_left.mp hdisj hx
    exact hc
  let _m0 := maxContactIdeal k p A mu_
  have hM1_ : H1_.ideal ⟨U1_, hU1⟩ ≤ _m0.ideal ⟨U1_, hU1⟩ := by
    have h1 :=
      d1.ideal_eq_span_coord hU1 H1_ {i1_} hH1U1
    rw [h1, coe_singleton, image_singleton, span_le, singleton_subset_iff]
    exact (isMaxContactCoord_iff_coord_mem k p A mu_ hU1 d1 i1_).mp hmc1
  have hM2_ : H2_.ideal ⟨U2_, hU2_⟩ ≤ _m0.ideal ⟨U2_, hU2_⟩ := by
    have h1 :=
      d2.ideal_eq_span_coord hU2_ H2_ {i2_} hH2U2
    rw [h1, coe_singleton, image_singleton, span_le, singleton_subset_iff]
    exact (isMaxContactCoord_iff_coord_mem k p A mu_ hU2_ d2 i2_).mp hmc2
  have hsnc2' := (inStrictNormalCrossingPosition_iff p (H2_ :: N)).mp hsnc2_
  have hcart2_ : p17 H2_ :=
    ((isSmoothDivisor_iff p H2_).mp $ hsnc2'.1 H2_ $ by simp).1
  obtain ⟨⟨W2, hW2_⟩, f2_, hxW2, -, hf2span⟩ := hcart2_ x
  obtain ⟨W, hxW, m0, c0_, a, hainj, hanone, hasome⟩ := (((inStrictNormalCrossingPosition_iff p (H1_ :: N)).mp hsnc1_).2 x).exists_etaleChart
  obtain ⟨V0, hV0b, hxV0, hV0W⟩ :=
    isBasis_iff_nbhd.mp X.isBasis_affineOpens hxW
  have hdesc0 : ∀ i : ℕ, ∀ hi : i < (H1_ :: N).length,
      (a i = none → restrictIdeal ((H1_ :: N)[i]'hi) V0 = ⊤) ∧
        ∀ j : Fin m0, a i = some j →
          restrictIdeal ((H1_ :: N)[i]'hi) V0 = (c0_.restrict hV0W).coordIdeal {j} := by
    intro i hi
    refine ⟨fun hn => restrictIdeal_eq_top_of_le _ hV0W $ hanone i hi hn, ?_⟩
    intro j hj
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hV0W c0_ _ {j} $ hasome i hi j hj
  have hinj0 : ∀ i i' : ℕ, i < (H1_ :: N).length → i' < (H1_ :: N).length →
      ∀ j : Fin m0, a i = some j → a i' = some j → i = i' := by
    intro i i' hi hi' j h1 h2
    exact hainj i hi i' hi' j h1 h2
  obtain ⟨U', hU', hxU', n', c', a', hdesc', hinj', hprime'⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf (H1_ :: N) x V0 hV0b hxV0 (c0_.restrict hV0W) a hdesc0 hinj0
  have hlt0 : 0 < (H1_ :: N).length := by simp
  obtain ⟨j0_, hj0_⟩ : ∃ t : Fin n', a' 0 = some t := by
    cases h0 : a' 0 with
    | none =>
      exfalso
      have htop := (hdesc' 0 hlt0).1 h0
      simp [getElem_cons_zero] at htop
      exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top H1_ U' htop x hxU' hxH1
    | some t => exact ⟨t, rfl⟩
  have hH1U' : restrictIdeal H1_ U' = c'.coordIdeal {j0_} := by
    have h1 := (hdesc' 0 hlt0).2 j0_ hj0_
    simpa only [getElem_cons_zero] using h1
  obtain ⟨ga_, hgaval, hganone⟩ :
      ∃ ga_ : ℕ → Option (Fin n'),
        (∀ i : ℕ, i < N.length → ga_ i = a' (i + 1)) ∧
        (∀ i : ℕ, ¬ i < N.length → ga_ i = none) :=
    ⟨fun i => if i < N.length then a' $ i + 1 else none, fun i hi => if_pos hi,
      fun i hi => if_neg hi⟩
  have hgainj : LabelingInjective ga_ N.length := by
    intro i i' hi hi' j hj hj'
    rw [hgaval i hi] at hj
    rw [hgaval i' hi'] at hj'
    have h1 : i + 1 < (H1_ :: N).length := by
      simp [length_cons]
      omega
    have h2 : i' + 1 < (H1_ :: N).length := by
      simp [length_cons]
      omega
    have h3 := hinj' (i + 1) (i' + 1) h1 h2 j hj hj'
    omega
  have hgaj0 : ∀ i : ℕ, ga_ i ≠ some j0_ := by
    intro i hcon
    by_cases hi : i < N.length
    rw [hgaval i hi] at hcon
    have h1 : i + 1 < (H1_ :: N).length := by
      simp [length_cons]
      omega
    have h3 := hinj' (i + 1) 0 h1 hlt0 j0_ hcon hj0_
    omega
    rw [hganone i hi] at hcon
    exact Option.some_ne_none j0_ hcon.symm
  have hlabU' : IsCoordLabeling c' ga_ N := by
    intro i hi
    have hiE : i + 1 < (H1_ :: N).length := by
      simp [length_cons]
      omega
    have hget : (H1_ :: N)[i + 1]'hiE = N[i]'hi := by simp
    constructor
    intro hnone
    have ha' : a' (i + 1) = none := by
      rwa [← hgaval i hi]
    have htop := (hdesc' (i + 1) hiE).1 ha'
    rwa [hget] at htop
    intro j hj
    have ha' : a' (i + 1) = some j := by
      rwa [← hgaval i hi]
    have h2 := (hdesc' (i + 1) hiE).2 j ha'
    rwa [hget] at h2
  have hxN : ∀ i : ℕ, ∀ hi : i < N.length, ∀ j : Fin n',
      ga_ i = some j → x ∈ spI (N[i]'hi) := by
    intro i hi j hj
    have hiE : i + 1 < (H1_ :: N).length := by
      simp [length_cons]
      omega
    have ha' : a' (i + 1) = some j := by
      rwa [← hgaval i hi]
    have h2 := (hlabU' i hi).2 j hj
    have hideal : (N[i]'hi).ideal ⟨U', hU'⟩ = span {c'.coord j} := by
      have h3 := c'.ideal_eq_span_coord hU' (N[i]'hi) {j} h2
      rwa [coe_singleton, image_singleton] at h3
    refine mem_support_of_ideal_le_primeIdealOf (N[i]'hi) hU' hxU' ?_
    rw [hideal, span_le, singleton_subset_iff]
    exact hprime' (i + 1) hiE j ha'
  obtain ⟨V, hVb, hxV, hVOm⟩ :=
    isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U' ⊓ U1_ ⊓ U2_ ⊓ W2 from ⟨⟨⟨hxU', hxU1⟩, hxU2⟩, hxW2⟩)
  have hV := hVb
  have hVU' := le_trans hVOm $ le_trans inf_le_left $ le_trans inf_le_left inf_le_left
  have hVW2 := le_trans hVOm inf_le_right
  have hlab : IsCoordLabeling (c'.restrict hVU') ga_ N := by
    intro i hi
    constructor
    intro hnone
    exact restrictIdeal_eq_top_of_le (N[i]'hi) hVU' $ (hlabU' i hi).1 hnone
    intro j hj
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c' (N[i]'hi) {j} $ (hlabU' i hi).2 j hj
  obtain ⟨g, hg⟩ : ∃ g : X.sec V, H2_.ideal ⟨V, hV⟩ = span {g} := by
    refine ⟨(pMap X (homOfLE hVW2).op).hom f2_, ?_⟩
    have h2 := ideal_eq_span_image_map_of_le H2_ hW2_ hV hVW2 ({f2_} : Set W2.sec) hf2span
    rwa [image_singleton] at h2
  obtain ⟨jd, hjdlab, hjdpd⟩ :=
    exists_unlabeled_index_partialDeriv_notMem_primeIdealOf hV (c'.restrict hVU') hxV N ga_
      H2_ g hlab hgainj (hsnc2'.2 x) hg hxH2 hxN
  have hjdpd' :
      chartPartialDeriv hV (c'.restrict hVU') jd g ∉ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hjdpd
  obtain ⟨c'', hcj0, hclab, hpd⟩ : ∃ c'' : EtaleChart p V n',
      c''.coord j0_ = (c'.restrict hVU').coord j0_ ∧
      (∀ j : Fin n', (∃ i : ℕ, i < N.length ∧ ga_ i = some j) →
        c''.coord j = (c'.restrict hVU').coord j) ∧
      chartPartialDeriv hV c'' j0_ g ∉ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    by_cases h0 : chartPartialDeriv hV (c'.restrict hVU') j0_ g ∈
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
    have hne : j0_ ≠ jd := by
      intro hh
      rw [hh] at h0
      exact hjdpd' h0
    obtain ⟨c'', -, hcother, hderiv, -⟩ :=
      exists_etaleChart_coord_add_smul_chartPartialDeriv hV (c'.restrict hVU') j0_ jd hne (1 : k)
    refine ⟨c'', hcother j0_ hne, ?_, ?_⟩
    rintro j ⟨i, hi, hgai⟩
    refine hcother j ?_
    intro hjd
    exact hjdlab i hi $ by rw [hgai, hjd]
    rw [hderiv g, map_one, one_mul]
    intro hmem
    apply hjdpd'
    have heq : chartPartialDeriv hV (c'.restrict hVU') jd g
        = chartPartialDeriv hV (c'.restrict hVU') j0_ g
          - (chartPartialDeriv hV (c'.restrict hVU') j0_ g
             - chartPartialDeriv hV (c'.restrict hVU') jd g) := by ring
    rw [heq]
    exact m162 _ h0 hmem
    exact ⟨c'.restrict hVU', rfl, fun j _ => rfl, h0⟩
  have hlab'' : IsCoordLabeling c'' ga_ N := by
    intro i hi
    refine ⟨(hlab i hi).1, ?_⟩
    intro j hj
    exact restrictIdeal_eq_coordIdeal_of_coord_eq hV (c'.restrict hVU') c'' j
      (hclab j ⟨i, hi, hj⟩) (N[i]'hi) ((hlab i hi).2 j hj)
  obtain ⟨V', hV', hV'V, hxV', c2_, hc2j0, hc2other⟩ :=
    exists_etaleChart_update_coord_of_partialDeriv_notMem hV c'' hxV j0_ g hpd
  have hH1V' :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c'' H1_ {j0_} (restrictIdeal_eq_coordIdeal_of_coord_eq hV (c'.restrict hVU') c'' j0_ hcj0 H1_ (restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c' H1_ {j0_} hH1U'))
  have hH1id : H1_.ideal ⟨V', hV'⟩ = span {(c''.restrict hV'V).coord j0_} := by
    have h1 := (c''.restrict hV'V).ideal_eq_span_coord hV' H1_ {j0_} hH1V'
    rwa [coe_singleton, image_singleton] at h1
  have hgV' : H2_.ideal ⟨V', hV'⟩ = span {c2_.coord j0_} := by
    have h2 := ideal_eq_span_image_map_of_le H2_ hV hV' hV'V ({g} : Set $ X.sec V) hg
    rw [image_singleton] at h2
    rw [h2, hc2j0]
  have hH2V' : restrictIdeal H2_ V' = c2_.coordIdeal {j0_} := by
    refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV' c2_ H2_ {j0_} ?_
    rw [hgV', coe_singleton, image_singleton]
  have hmcc1 : IsMaxContactCoord k p A mu_ (c''.restrict hV'V) j0_ := by
    rw [isMaxContactCoord_iff_coord_mem k p A mu_ hV' (c''.restrict hV'V) j0_]
    refine (ideal_le_of_ideal_le_of_le k p H1_ _m0 hU1 hV' (le_trans hV'V $ le_trans hVOm $ le_trans inf_le_left $ le_trans inf_le_left inf_le_right) hM1_) ?_
    rw [hH1id]
    exact mem_span_singleton_self _
  have hmcc2 : IsMaxContactCoord k p A mu_ c2_ j0_ := by
    rw [isMaxContactCoord_iff_coord_mem k p A mu_ hV' c2_ j0_]
    refine (ideal_le_of_ideal_le_of_le k p H2_ _m0 hU2_ hV' (le_trans hV'V $ le_trans hVOm $ le_trans inf_le_left inf_le_right) hM2_) ?_
    rw [hgV']
    exact mem_span_singleton_self _
  have hgerm1 : (pGerm X V' x hxV').hom ((c''.restrict hV'V).coord j0_)
      ∈ maximalIdeal (stkX X x) := by
    have hmem : (c''.restrict hV'V).coord j0_ ∈ H1_.ideal ⟨V', hV'⟩ := by
      rw [hH1id]
      exact mem_span_singleton_self _
    exact (mem_support_iff_stalkIdeal_le_maximalIdeal H1_ x).mp hxH1 $ germ_mem_stalkIdeal H1_ x ⟨V', hV'⟩ hxV' hmem
  have hgerm2 : (pGerm X V' x hxV').hom (c2_.coord j0_)
      ∈ maximalIdeal (stkX X x) := by
    have hmem : c2_.coord j0_ ∈ H2_.ideal ⟨V', hV'⟩ := by
      rw [hgV']
      exact mem_span_singleton_self _
    exact (mem_support_iff_stalkIdeal_le_maximalIdeal H2_ x).mp hxH2 $ germ_mem_stalkIdeal H2_ x ⟨V', hV'⟩ hxV' hmem
  have hcoords : ∀ j : Fin n', j ≠ j0_ → c2_.coord j = (c''.restrict hV'V).coord j := by
    intro j hj
    rw [hc2other j hj, coord_restrict c'' hV'V j]
  refine ⟨V', hV', hxV', n', c''.restrict hV'V, c2_, ga_, j0_, hH1V', hH2V', hmcc1, hmcc2,
    hgerm1, hgerm2, hcoords, ?_, hgainj, hgaj0⟩
  intro i hi
  refine ⟨fun hn => restrictIdeal_eq_top_of_le (N[i]'hi) hV'V $ (hlab'' i hi).1 hn, ?_⟩
  intro j hj
  exact restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c'' (N[i]'hi) {j} ((hlab'' i hi).2 j hj)

end


variable (k : Type) [Field k] [CharZero k] {X : Sch}
  (p : X ⟶ Sp k) [Smooth p]
  (I : ISD X) (m : ℕ)

theorem orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
    (h : IsDerivBalanced k p I m) x :
    orderAt I x = 0 ∨ (m : ENat) ≤ orderAt I x := by
  rcases m73 m with rfl | hpos
  right
  simp
  by_cases h0 : orderAt I x = 0
  exact m51 h0
  right
  have hlt : m - 1 < m := by omega
  have hle :=
    IsDerivBalanced.derivIdealSheafIterate_pow_le k p h hlt
  have hsub : m - (m - 1) = 1 := by omega
  rw [hsub, pow_one] at hle
  have hord :=
    orderAt_le_of_le hle x
  let _m0 := derivIdealSheafIterate k p (m - 1) I
  rw [orderAt_pow k p _m0 m x] at hord
  have hne : orderAt _m0 x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hord
    exact h0 $ le_antisymm hord $ by exact zero_le
  have hmem : x ∈ spI _m0 := by
    by_contra hc
    exact hne $ mpr_ (orderAt_eq_zero_iff_not_mem_support _ x) hc
  refine mp_ (mem_orderAtLeastLocus_iff I m x) ?_
  rwa [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hpos]

theorem orderAtLeastLocus_eq_support_of_isDerivBalanced
    (h : IsDerivBalanced k p I m) (hm : 1 ≤ m) :
    orderAtLeastLocus I m = (I.support : Set X) := by
  ext x
  rw [mem_orderAtLeastLocus_iff]
  constructor
  intro hx
  have h1 : 1 ≤ orderAt I x := le_trans (by exact_mod_cast hm) hx
  exact mp_ (one_le_orderAt_iff_mem_support I x) h1
  intro hx
  have hne := fun h0 =>
    (orderAt_eq_zero_iff_not_mem_support I x).mp h0 hx
  rcases orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced k p I m h x with h0 | h0
  exact absurd h0 hne
  exact h0

end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

section
variable {X Y : Sch} (f : X ⟶ Y) [IsClosedImmersion f]
def kerSubschemeIso : subscheme (ker f) ≅ X :=
  (asIso (toImage f)).symm

theorem kerSubschemeIso_hom_comp :
    (kerSubschemeIso f).hom ≫ f = (ker f).si := by
  have key := IsIso.inv_hom_id_assoc (toImage f) $ imageι f
  rwa [toImage_imageι] at key

theorem kerSubschemeIso_inv_comp :
    (kerSubschemeIso f).inv ≫ (ker f).si = f := by
  rw [← kerSubschemeIso_hom_comp f, m213]
end

namespace MarkedIdealWithBoundary

section
variable (T : MarkedIdealWithBoundary)
section
variable (Y) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
def pullbackAlong : MarkedIdealWithBoundary where
  base := T.base
  instField := T.instField
  scheme := Y
  structMap := q
  ideal := T.ideal.comap h
  mult := T.mult
  boundary := T.boundary.map fun D => comap D h



@[simp] theorem pullbackAlong_mult :
    (T.pullbackAlong Y q h).mult = T.mult := rfl

theorem pullbackAlong_structureMorphism :
    (T.pullbackAlong Y q h).structMap = q := rfl

theorem pullbackAlong_ideal :
    (T.pullbackAlong Y q h).ideal = T.ideal.comap h := rfl

theorem pullbackAlong_boundary :
    (T.pullbackAlong Y q h).boundary = T.boundary.map fun D => comap D h := rfl
end

section
variable (L : Type) [Field L] (f : T.base →+* L)
def baseChange :
    MarkedIdealWithBoundary where
  base := L
  scheme := pullback T.structMap (specMapOfFieldHom T.base L f)
  structMap := pullback.snd T.structMap (specMapOfFieldHom T.base L f)
  ideal := T.ideal.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  mult := T.mult
  boundary :=
    T.boundary.map fun D => comap D (pullback.fst T.structMap (specMapOfFieldHom T.base L f))


@[simp] theorem baseChange_mult : (T.baseChange L f).mult = T.mult := rfl


theorem baseChange_structureMorphism :
    (T.baseChange L f).structMap = pullback.snd T.structMap (specMapOfFieldHom T.base L f) := rfl

theorem baseChange_ideal :
    (T.baseChange L f).ideal =
      T.ideal.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := rfl

theorem baseChange_boundary :
    (T.baseChange L f).boundary =
      T.boundary.map
        (fun D => comap D (pullback.fst T.structMap (specMapOfFieldHom T.base L f))) := rfl
end
abbrev bc {L : Type} [Field L] (f : T.base →+* L) := T.baseChange L f

section
variable (Y : Sch) (q : Y ⟶ Sp T.base) (J : ISD Y) (E : Bdy Y)
def withSchemeIdealBoundary : MarkedIdealWithBoundary where
  base := T.base
  instField := T.instField
  scheme := Y
  structMap := q
  ideal := J
  mult := T.mult
  boundary := E



@[simp] theorem withSchemeIdealBoundary_mult : (T.withSchemeIdealBoundary Y q J E).mult = T.mult := rfl

theorem withSchemeIdealBoundary_structureMorphism : (T.withSchemeIdealBoundary Y q J E).structMap = q := rfl

theorem withSchemeIdealBoundary_ideal : (T.withSchemeIdealBoundary Y q J E).ideal = J := rfl
end

section
variable (E : List T.scheme.IdealSheafData)
def withBoundary :
    MarkedIdealWithBoundary where
  base := T.base
  instField := T.instField
  scheme := T.scheme
  structMap := T.structMap
  ideal := T.ideal
  mult := T.mult
  boundary := E




@[simp] theorem withBoundary_ideal :
    (T.withBoundary E).ideal = T.ideal := rfl

@[simp] theorem withBoundary_mult :
    (T.withBoundary E).mult = T.mult := rfl

@[simp] theorem withBoundary_boundary : (T.withBoundary E).boundary = E := rfl

@[simp] theorem withBoundary_dim :
    (T.withBoundary E).krullDimSucc = T.krullDimSucc := rfl
end
abbrev pbA {Y : Sch} (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme) := T.pullbackAlong Y q h
abbrev pbB {Y : Sch} (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme) (E : List Y.IdealSheafData) := (T.pullbackAlong Y q h).withBoundary E

@[simp] theorem withBoundary_self :
    T.withBoundary T.boundary = T := rfl
end

section
variable {X : Sch}
def nontrivialPart (E : Bdy X) : Bdy X :=
  E.filter fun D => !(@decide (D = ⊤) (propDecidable _))

def SameNontrivialBoundary (E E' : Bdy X) : Prop :=
  nontrivialPart E = nontrivialPart E'

theorem sameNontrivialBoundary_iff (E E' : Bdy X) :
    SameNontrivialBoundary E E' ↔ nontrivialPart E = nontrivialPart E' := m22

theorem SameNontrivialBoundary.refl (E : Bdy X) :
    SameNontrivialBoundary E E := rfl

theorem SameNontrivialBoundary.symm {E E' : Bdy X}
    (h : SameNontrivialBoundary E E') : SameNontrivialBoundary E' E := Eq.symm h

theorem SameNontrivialBoundary.trans {E E' E'' : Bdy X}
    (h : SameNontrivialBoundary E E') (h' : SameNontrivialBoundary E' E'') : SameNontrivialBoundary E E'' := m32 h h'

theorem nontrivialPart_append (A B : Bdy X) :
    nontrivialPart (A ++ B) = nontrivialPart A ++ nontrivialPart B := by
  simp [nontrivialPart, filter_append]

theorem SameNontrivialBoundary.append {L1_ L1' L2_ L2' : Bdy X}
    (h1_ : SameNontrivialBoundary L1_ L1') (h2_ : SameNontrivialBoundary L2_ L2') :
    SameNontrivialBoundary (L1_ ++ L2_) (L1' ++ L2') := by
  show nontrivialPart (L1_ ++ L2_) = nontrivialPart (L1' ++ L2')
  rw [nontrivialPart_append, nontrivialPart_append, h1_, h2_]
end

section
variable {X Y : Sch} (f : ISD X → ISD Y) (hf : f ⊤ = ⊤)
include hf
theorem nontrivialPart_map_nontrivialPart (L : Bdy X) :
    nontrivialPart ((nontrivialPart L).map f) = nontrivialPart (L.map f) := by
  have hcons_top : ∀ {Z : Sch} {a : ISD Z}, a = ⊤ →
      ∀ M, nontrivialPart (a :: M) = nontrivialPart M := by
    intro Z a ha M
    have hb : (@decide (a = ⊤) $ propDecidable $ a = ⊤) = true := by simp [ha]
    simp [nontrivialPart, hb]
  have hcons_ne : ∀ {Z : Sch} {a : ISD Z}, ¬ a = ⊤ →
      ∀ M, nontrivialPart (a :: M) = a :: nontrivialPart M := by
    intro Z a ha M
    have hb : (@decide (a = ⊤) $ propDecidable $ a = ⊤) = false := by simp [ha]
    simp [nontrivialPart, hb]
  induction L with
  | nil => simp [nontrivialPart]
  | cons a L ih =>
    by_cases ha : a = ⊤
    simp_all
    by_cases hfa : f a = ⊤
    simp_all
    simp_all

theorem SameNontrivialBoundary.map {L L' : Bdy X} (h : SameNontrivialBoundary L L') :
    SameNontrivialBoundary (L.map f) (L'.map f) := by
  show nontrivialPart (L.map f) = nontrivialPart (L'.map f)
  rw [← nontrivialPart_map_nontrivialPart f hf L, ← nontrivialPart_map_nontrivialPart f hf L', h]
end

def AdmissibleUnderBoundaryReplacement : Prop :=
  ∀ (T : MarkedIdealWithBoundary) (E' : List T.scheme.IdealSheafData), T.IsAdmissible →
    SameNontrivialBoundary T.boundary E' → (T.withBoundary E').IsAdmissible

section
variable (T : MarkedIdealWithBoundary)
def IsOrderBoundedByMult : Prop :=
  ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ENat)

theorem isOrderBoundedByMult_iff :
    T.IsOrderBoundedByMult ↔ ∀ x, orderAt T.ideal x ≤ (T.mult : ENat) := m22

def IsBalanced
    (hft : LocallyOfFiniteType T.structMap) : Prop :=
  haveI : LocallyOfFiniteType T.structMap := hft
  haveI : IsNoetherianRing T.base := inferInstance
  IsDerivBalanced T.base T.structMap T.ideal T.mult
end

end MarkedIdealWithBoundary

namespace MarkedSequenceOfBlowups

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (s : MarkedSequenceOfBlowups p I m E)
def boundaryLocus (t : ℕ) : CSet (s.toSequenceOfBlowups.schemeAt t) :=
  ⋃ D ∈ s.boundary t, ((support D : CSet (s.toSequenceOfBlowups.schemeAt t)))

theorem mem_boundaryLocus_iff t
    x :
    x ∈ s.boundaryLocus t ↔
      ∃ D ∈ s.boundary t, x ∈ ((support D : CSet (s.toSequenceOfBlowups.schemeAt t))) := by
  constructor
  intro hx
  obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.mp hx
  exact ⟨D, hD, hxD⟩
  rintro ⟨D, hD, hxD⟩
  exact Set.mem_iUnion₂.mpr ⟨D, hD, hxD⟩

def otherBoundaryLocus (j t : ℕ) :
    CSet (s.toSequenceOfBlowups.schemeAt t) :=
  ⋃ (i : Fin (s.boundary t).length) (_ : (i : ℕ) ≠ j),
    (support (get (s.boundary t) i) : CSet (s.toSequenceOfBlowups.schemeAt t))

theorem mem_otherBoundaryLocus_iff j t
    x :
    x ∈ s.otherBoundaryLocus j t ↔
      ∃ i : Fin (s.boundary t).length, (i : ℕ) ≠ j ∧
        x ∈ (support ((s.boundary t).get i) : CSet (s.toSequenceOfBlowups.schemeAt t)) := by
  constructor
  intro hx
  have hx' := hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx'
  exact ⟨i, hi, hxi⟩
  rintro ⟨i, hi, hxi⟩
  exact Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩
end

end MarkedSequenceOfBlowups

structure IsMaxOrderReduction (P : ℕ → Prop) (A B : PrincipalizationAssignment) : Prop where
  cert : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      PrincipalizationCertificate ((A T).toSequenceOfBlowups.schemeAt i) ((A T).projectionToSpec i) ((A T).ideal i) T.mult
        ((A T).boundaryLocus i) ((A T).toSequenceOfBlowups.center i)
  orderRed_equiv : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc →
    T.boundary = [] → T.IsOrderBoundedByMult →
    (A T).toSequenceOfBlowups.Isomorphic (B T).toSequenceOfBlowups
  base_change : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.bc f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.bc f).boundary E' →
      ((T.bc f).withBoundary E').IsAdmissible →
      P ((T.bc f).withBoundary E').krullDimSucc →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.bc f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  base_change_strict : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.bc f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.bc f).boundary E' →
      ((T.bc f).withBoundary E').IsAdmissible →
      P ((T.bc f).withBoundary E').krullDimSucc →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.bc f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  center_nonempty : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      (support ((A T).toSequenceOfBlowups.center i) : Set ↥((A T).toSequenceOfBlowups.schemeAt i)).Nonempty
  resolves : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → (A T).IsResolution
  smooth_pullback : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
    ∀ E' : Bdy Y,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pbA q h).boundary E' →
      (T.pbB q h E').IsAdmissible →
      P (T.pbB q h E').krullDimSucc →
      IsPullbackBlowupSequence h (A (T.pbB q h E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h] [Surjective h], h ≫ T.structMap = q →
    ∀ E' : Bdy Y,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pbA q h).boundary E' →
      (T.pbB q h E').IsAdmissible →
      P (T.pbB q h E').krullDimSucc →
      IsStrictPullbackBlowupSeq h (A (T.pbB q h E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  trivial_of_coSupport_empty : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc →
    orderAtLeastLocus T.ideal T.mult = ∅ → (A T).toSequenceOfBlowups.length = 0

theorem isMaxOrderReduction_of_forall_not P (hP : ∀ n, ¬ P n)
    A B : IsMaxOrderReduction P A B := by
  constructor <;> exact fun T _ hd => absurd hd $ hP T.krullDimSucc

section
variable {P} {A B} (hs : IsMaxOrderReduction P A B)
include hs
theorem IsMaxOrderReduction.mono Q (hQP : ∀ n, Q n → P n) :
    IsMaxOrderReduction Q A B := by
  constructor
  intro T hV hQ
  exact hs.cert T hV $ hQP _ hQ
  intro T hV hQ
  exact hs.orderRed_equiv T hV $ hQP _ hQ
  intro T hV hQ L _ _ f E' hBE hV' hQ'
  exact hs.base_change T hV (hQP _ hQ) L f E' hBE hV' $ hQP _ hQ'
  intro T hV hQ L _ _ f E' hBE hV' hQ'
  exact hs.base_change_strict T hV (hQP _ hQ) L f E' hBE hV' $ hQP _ hQ'
  intro T hV hQ
  exact hs.center_nonempty T hV $ hQP _ hQ
  intro T hV hQ
  exact hs.resolves T hV $ hQP _ hQ
  intro T hV hQ Y q h _ hq E' hBE hV' hQ'
  exact hs.smooth_pullback T hV (hQP _ hQ) Y q h hq E' hBE hV' $ hQP _ hQ'
  intro T hV hQ Y q h _ _ hq E' hBE hV' hQ'
  exact hs.smooth_pullback_strict T hV (hQP _ hQ) Y q h hq E' hBE hV' $ hQP _ hQ'
  intro T hV hQ
  exact hs.trivial_of_coSupport_empty T hV $ hQP _ hQ

section
variable (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hP : P T.krullDimSucc)
include hV hP
section
variable (Y) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme) [Smooth h]
theorem IsMaxOrderReduction.isPullbackBlowupSequence_of_smooth (hq : h ≫ T.structMap = q)
    (hV' : (T.pbA q h).IsAdmissible) (hP' : P (T.pbA q h).krullDimSucc) :
    IsPullbackBlowupSequence h (A (T.pbA q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups :=
  hs.smooth_pullback T hV hP Y q h hq (T.pbA q h).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'

theorem IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective [Surjective h] (hq : h ≫ T.structMap = q)
    (hV' : (T.pbA q h).IsAdmissible) (hP' : P (T.pbA q h).krullDimSucc) :
    IsStrictPullbackBlowupSeq h (A (T.pbA q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.smooth_pullback_strict T hV hP Y q h hq (T.pbA q h).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'
end

section
variable (L : Type) [Field L] [CharZero L] (f) (hV' : (T.baseChange L f).IsAdmissible) (hP' : P (T.baseChange L f).krullDimSucc)
include hV' hP'
theorem IsMaxOrderReduction.isPullbackBlowupSequence_baseChange :
    IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (A (T.bc f)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.base_change T hV hP L f (T.bc f).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'

theorem IsMaxOrderReduction.isStrictPullbackBlowupSeq_baseChange :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (A (T.bc f)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.base_change_strict T hV hP L f (T.bc f).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) hV' hP'
end
end
end

structure IsOrderReduction (P : ℕ → Prop) (A B : PrincipalizationAssignment) : Prop where
  cert : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      OrderCertificate ((A T).toSequenceOfBlowups.schemeAt i) ((A T).projectionToSpec i) ((A T).ideal i) T.mult
        ((A T).boundaryLocus i) ((A T).toSequenceOfBlowups.center i)
  base_change : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.bc f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.bc f).boundary E' →
      ((T.bc f).withBoundary E').IsAdmissible →
      P ((T.bc f).withBoundary E').krullDimSucc →
      ((T.bc f).withBoundary E').IsOrderBoundedByMult →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.bc f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  base_change_strict : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.bc f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.bc f).boundary E' →
      ((T.bc f).withBoundary E').IsAdmissible →
      P ((T.bc f).withBoundary E').krullDimSucc →
      ((T.bc f).withBoundary E').IsOrderBoundedByMult →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.bc f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  pushforward : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.boundary = [] → T.mult = 1 →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (e : Y ⟶ T.scheme)
      [IsClosedImmersion e], e ≫ T.structMap = q →
      IsSmoothDivisor T.structMap (ker e) →
    ∀ J : ISD Y,
      (T.withSchemeIdealBoundary Y q J ([] : Bdy Y)).IsAdmissible →
      (T.withSchemeIdealBoundary Y q J ([] : Bdy Y)).krullDimSucc < T.krullDimSucc →
      T.ideal = imageIdealSheaf e J →
      IsPushforwardBlowupSeq e (B (T.withSchemeIdealBoundary Y q J ([] : Bdy Y))).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  order_le : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ i, i ≤ (A T).toSequenceOfBlowups.length →
      ∀ x : ↥((A T).toSequenceOfBlowups.schemeAt i), orderAt ((A T).ideal i) x ≤ (T.mult : ENat)
  center_nonempty : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      (support ((A T).toSequenceOfBlowups.center i) : Set ↥((A T).toSequenceOfBlowups.schemeAt i)).Nonempty
  resolves : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult → (A T).IsResolution
  smooth_pullback : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
    ∀ E' : Bdy Y,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pbA q h).boundary E' →
      (T.pbB q h E').IsAdmissible →
      P (T.pbB q h E').krullDimSucc →
      (T.pbB q h E').IsOrderBoundedByMult →
      IsPullbackBlowupSequence h (A (T.pbB q h E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h] [Surjective h], h ≫ T.structMap = q →
    ∀ E' : Bdy Y,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pbA q h).boundary E' →
      (T.pbB q h E').IsAdmissible →
      P (T.pbB q h E').krullDimSucc →
      (T.pbB q h E').IsOrderBoundedByMult →
      IsStrictPullbackBlowupSeq h (A (T.pbB q h E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  trivial_of_coSupport_empty : ∀ T : MarkedIdealWithBoundary, T.IsAdmissible → P T.krullDimSucc → T.IsOrderBoundedByMult →
    orderAtLeastLocus T.ideal T.mult = ∅ → (A T).toSequenceOfBlowups.length = 0

structure IsBoundaryDivisorReduction (P : ℕ → Prop) (j : ℕ) (A B : PrincipalizationAssignment) : Prop where
  base_change : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.bc f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.bc f).boundary E' →
      E'.take (j + 1) = (T.bc f).boundary.take (j + 1) →
    ∀ hV' : ((T.bc f).withBoundary E').IsAdmissible,
      P ((T.bc f).withBoundary E').krullDimSucc →
      ((T.bc f).withBoundary E').IsOrderBoundedByMult →
      ((T.bc f).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.bc f).withBoundary E').boundary.length →
      IsPullbackBlowupSequence (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.bc f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  base_change_strict : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (L : Type) [Field L] [CharZero L] (f : T.base →+* L)
      (E' : List (T.bc f).scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.bc f).boundary E' →
      E'.take (j + 1) = (T.bc f).boundary.take (j + 1) →
    ∀ hV' : ((T.bc f).withBoundary E').IsAdmissible,
      P ((T.bc f).withBoundary E').krullDimSucc →
      ((T.bc f).withBoundary E').IsOrderBoundedByMult →
      ((T.bc f).withBoundary E').IsBalanced hV'.locallyOfFiniteType →
      j < ((T.bc f).withBoundary E').boundary.length →
      IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
        (A ((T.bc f).withBoundary E')).toSequenceOfBlowups (A T).toSequenceOfBlowups
  order_le : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ i, i ≤ (A T).toSequenceOfBlowups.length →
      ∀ x : ↥((A T).toSequenceOfBlowups.schemeAt i), orderAt ((A T).ideal i) x ≤ (T.mult : ENat)
  center_nonempty : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ i, i < (A T).toSequenceOfBlowups.length →
      (support ((A T).toSequenceOfBlowups.center i) : Set ↥((A T).toSequenceOfBlowups.schemeAt i)).Nonempty
  pushforward : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ hj : j < T.boundary.length, T.mult = 1 →
    ∀ J : (T.bget j hj).subscheme.IdealSheafData,
      (T.withSchemeIdealBoundary (T.bget j hj).subscheme
          (subschemeι (T.bget j hj) ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => comap D (T.bget j hj).si))).IsAdmissible →
      (T.withSchemeIdealBoundary (T.bget j hj).subscheme
          (subschemeι (T.bget j hj) ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => comap D (T.bget j hj).si))).krullDimSucc < T.krullDimSucc →
      T.ideal = imageIdealSheaf (T.bget j hj).si J →
      IsPushforwardBlowupSeq (T.bget j hj).si
        (B (T.withSchemeIdealBoundary (T.bget j hj).subscheme
            (subschemeι (T.bget j hj) ≫ T.structMap) J
            ((T.boundary.eraseIdx j).map
              (fun D => comap D (T.bget j hj).si)))).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  shape : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ hj : j < T.boundary.length,
    ∃ (D : ∀ t : ℕ, ((A T).toSequenceOfBlowups.schemeAt t).IdealSheafData) (b : Bool),
      (∀ t ≤ (A T).toSequenceOfBlowups.length, IsSmoothDivisor ((A T).projectionToSpec t) (D t)) ∧
      D 0 = comap (T.bget j hj) (A T).toSequenceOfBlowups.isoZero.hom ∧
      (∀ t < (A T).toSequenceOfBlowups.length,
        (support ((A T).toSequenceOfBlowups.center t) : Set ↥((A T).toSequenceOfBlowups.schemeAt t)) ⊆
          ((support (D t) : Set ↥((A T).toSequenceOfBlowups.schemeAt t)))) ∧
      (b = true →
        0 < (A T).toSequenceOfBlowups.length ∧
        IsOpen ((D 0).subschemeι.base ⁻¹'
          ((support ((A T).toSequenceOfBlowups.center 0) : Set ↥((A T).toSequenceOfBlowups.schemeAt 0)))) ∧
        D 1 = comap (D 0) ((A T).toSequenceOfBlowups.transitionMapSucc 0)) ∧
      (∀ t < (A T).toSequenceOfBlowups.length, ¬ (b = true ∧ t = 0) →
        D (t + 1) = strictTransform ((A T).toSequenceOfBlowups.transitionMapSucc t)
          ((A T).toSequenceOfBlowups.center t) (D t)) ∧
      (orderAtLeastLocus (A T).lastIdeal T.mult ∩
        ((support (D (A T).toSequenceOfBlowups.length) :
          Set ↥((A T).toSequenceOfBlowups.schemeAt (A T).toSequenceOfBlowups.length)))) = ∅ ∧
      (∀ t < (A T).toSequenceOfBlowups.length, ¬ (b = true ∧ t = 0) →
        ∃ J : (D t).subscheme.IdealSheafData,
          NonzeroOnComponents J ∧
          (∀ x : ↥(D t).subscheme,
            (D t).subschemeι.base x ∉ (A T).otherBoundaryLocus j t →
            ∃ V : (D t).subscheme.Opens, x ∈ V ∧
              comap J V.i = comap (comap ((A T).ideal t) (D t).si) V.i) ∧
          PrincipalizationCertificate (D t).subscheme (subschemeι (D t) ≫ (A T).projectionToSpec t) J T.mult
            ((D t).subschemeι.base ⁻¹' (A T).otherBoundaryLocus j t)
            (comap ((A T).toSequenceOfBlowups.center t) (D t).si))
  smooth_pullback : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h], h ≫ T.structMap = q →
    ∀ E' : Bdy Y,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pbA q h).boundary E' →
      E'.take (j + 1) = (T.pbA q h).boundary.take (j + 1) →
    ∀ hV' : (T.pbB q h E').IsAdmissible,
      P (T.pbB q h E').krullDimSucc →
      (T.pbB q h E').IsOrderBoundedByMult →
      (T.pbB q h E').IsBalanced hV'.locallyOfFiniteType →
      j < (T.pbB q h E').boundary.length →
      IsPullbackBlowupSequence h (A (T.pbB q h E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  smooth_pullback_strict : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), P T.krullDimSucc → T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    ∀ (Y : Sch) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme)
      [Smooth h] [Surjective h], h ≫ T.structMap = q →
    ∀ E' : Bdy Y,
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pbA q h).boundary E' →
      E'.take (j + 1) = (T.pbA q h).boundary.take (j + 1) →
    ∀ hV' : (T.pbB q h E').IsAdmissible,
      P (T.pbB q h E').krullDimSucc →
      (T.pbB q h E').IsOrderBoundedByMult →
      (T.pbB q h E').IsBalanced hV'.locallyOfFiniteType →
      j < (T.pbB q h E').boundary.length →
      IsStrictPullbackBlowupSeq h (A (T.pbB q h E')).toSequenceOfBlowups
        (A T).toSequenceOfBlowups
  trivial_of_coSupport_empty : ∀ (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible), P T.krullDimSucc →
    T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType → j < T.boundary.length →
    orderAtLeastLocus T.ideal T.mult = ∅ → (A T).toSequenceOfBlowups.length = 0

section
variable {P} {j} {A B} (hs : IsBoundaryDivisorReduction P j A B) (T : MarkedIdealWithBoundary) (hV : T.IsAdmissible) (hP : P T.krullDimSucc) (hO : T.IsOrderBoundedByMult) (hD : T.IsBalanced hV.locallyOfFiniteType) (hj : j < T.boundary.length)
include hs hP hO hD hj
section
variable (Y) (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme) [Smooth h]
theorem IsBoundaryDivisorReduction.isPullbackBlowupSequence_of_smooth (hq : h ≫ T.structMap = q)
    (hV' : (T.pbA q h).IsAdmissible) (hP' : P (T.pbA q h).krullDimSucc)
    (hO' : (T.pbA q h).IsOrderBoundedByMult)
    (hD' : (T.pbA q h).IsBalanced hV'.locallyOfFiniteType)
    (hj' : j < (T.pbA q h).boundary.length) :
    IsPullbackBlowupSequence h (A (T.pbA q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.smooth_pullback T hV hP hO hD hj Y q h hq (T.pbA q h).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) rfl hV' hP' hO' hD' hj'

theorem IsBoundaryDivisorReduction.isStrictPullbackBlowupSeq_of_smooth_surjective [Surjective h] (hq : h ≫ T.structMap = q)
    (hV' : (T.pbA q h).IsAdmissible) (hP' : P (T.pbA q h).krullDimSucc)
    (hO' : (T.pbA q h).IsOrderBoundedByMult)
    (hD' : (T.pbA q h).IsBalanced hV'.locallyOfFiniteType)
    (hj' : j < (T.pbA q h).boundary.length) :
    IsStrictPullbackBlowupSeq h (A (T.pbA q h)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.smooth_pullback_strict T hV hP hO hD hj Y q h hq (T.pbA q h).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) rfl hV' hP' hO' hD' hj'
end

theorem IsBoundaryDivisorReduction.isStrictPullbackBlowupSeq_baseChange
    (L : Type) [Field L] [CharZero L] f
    (hV' : (T.bc f).IsAdmissible) (hP' : P (T.bc f).krullDimSucc)
    (hO' : (T.bc f).IsOrderBoundedByMult)
    (hD' : (T.bc f).IsBalanced hV'.locallyOfFiniteType)
    (hj' : j < (T.bc f).boundary.length) :
    IsStrictPullbackBlowupSeq (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
      (A (T.bc f)).toSequenceOfBlowups (A T).toSequenceOfBlowups := by
  exact hs.base_change_strict T hV hP hO hD hj L f (T.bc f).boundary
    (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _) rfl hV' hP' hO' hD' hj'
end

structure IsBoundaryPositionInvariant (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment) : Prop where
  shift : ∀ (T : MarkedIdealWithBoundary), P T.krullDimSucc → T.IsOrderBoundedByMult →
    ∀ hft : LocallyOfFiniteType T.structMap, T.IsBalanced hft →
    ∀ (E1_ E2_ E1' E2' : List T.scheme.IdealSheafData) (D : T.scheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary E1_ E1' → MarkedIdealWithBoundary.SameNontrivialBoundary E2_ E2' →
      (T.withBoundary (E1_ ++ D :: E2_)).IsAdmissible →
      (T.withBoundary (E1' ++ D :: E2')).IsAdmissible →
      ((A E1_.length) (T.withBoundary (E1_ ++ D :: E2_))).toSequenceOfBlowups.Isomorphic
        ((A E1'.length) (T.withBoundary (E1' ++ D :: E2'))).toSequenceOfBlowups


structure PrincipalizationRules where
  divisorRed : ∀ T : MarkedIdealWithBoundary,
    (∀ S : MarkedIdealWithBoundary, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) → ℕ → T.SequenceOfBlowups
  maxOrderRed : ∀ T : MarkedIdealWithBoundary,
    (∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) → T.SequenceOfBlowups
  orderRed : ∀ T : MarkedIdealWithBoundary,
    (∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) → T.SequenceOfBlowups

namespace PrincipalizationRules

section
variable (B : PrincipalizationRules)
section
variable (L : PrincipalizationAssignment) (j : ℕ)
def divisorFamily :
    PrincipalizationAssignment :=
  fun T => B.divisorRed T (fun S _ => L S) j

theorem divisorFamily_apply
    T :
    B.divisorFamily L j T = B.divisorRed T (fun S _ => L S) j := rfl
end

def orderFamily (D : ℕ → PrincipalizationAssignment) :
    PrincipalizationAssignment :=
  fun T => B.orderRed T fun S _ j => D j S


def maxOrderFamily (A : PrincipalizationAssignment) :
    PrincipalizationAssignment :=
  fun T => B.maxOrderRed T fun S _ => A S


def nextLevel (L : OrderReductionData) : OrderReductionData where
  maxOrderRed := B.maxOrderFamily (B.orderFamily fun j => B.divisorFamily L.maxOrderRed j)
  orderRed := B.orderFamily fun j => B.divisorFamily L.maxOrderRed j
end

def inputLevelData (B : PrincipalizationRules) : ℕ → OrderReductionData
  | 0 => trivialOrderReductionData
  | n + 1 => B.nextLevel (B.inputLevelData n)

section
variable (B : PrincipalizationRules) (n : ℕ)
def outputLevelData : OrderReductionData := B.nextLevel (B.inputLevelData n)



@[simp] theorem inputLevelData_succ :
    B.inputLevelData (n + 1) = B.outputLevelData n := rfl
end

structure ReducesInductivelyOnDimension (B : PrincipalizationRules) : Prop where
  divisorSpec : ∀ (n : ℕ) (L O : PrincipalizationAssignment),
    IsMaxOrderReduction (fun d => d < n) L O →
    ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (B.divisorFamily L j) L
  divisorShift : ∀ (n : ℕ) (L O : PrincipalizationAssignment),
    IsMaxOrderReduction (fun d => d < n) L O →
    IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => B.divisorFamily L j
  maxOrderSpec : ∀ (n : ℕ) (A L : PrincipalizationAssignment),
    IsOrderReduction (fun d => d ≤ n) A L →
    IsMaxOrderReduction (fun d => d ≤ n) (B.maxOrderFamily A) A
  orderSpec : ∀ (n : ℕ) (D : ℕ → PrincipalizationAssignment) (L O : PrincipalizationAssignment),
    IsMaxOrderReduction (fun d => d < n) L O →
    (∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (D j) L) →
    IsBoundaryPositionInvariant (fun d => d ≤ n) D →
    IsOrderReduction (fun d => d ≤ n) (B.orderFamily D) L

section
variable (B : PrincipalizationRules)
section
variable (L L' : OrderReductionData) (T : MarkedIdealWithBoundary) (h : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc < T.krullDimSucc → L.maxOrderRed S = L'.maxOrderRed S)
include h
theorem nextLevel_orderReduction_congr :
    (B.nextLevel L).orderRed T = (B.nextLevel L').orderRed T := by
  have hfun : (fun S (_ : S.krullDimSucc ≤ T.krullDimSucc) j =>
        B.divisorFamily L.maxOrderRed j S)
      = fun S (_ : S.krullDimSucc ≤ T.krullDimSucc) j =>
        B.divisorFamily L'.maxOrderRed j S := by
    funext S hS j
    have hinner : (fun S' (_ : S'.krullDimSucc < S.krullDimSucc) => L.maxOrderRed S')
        = fun S' (_ : S'.krullDimSucc < S.krullDimSucc) => L'.maxOrderRed S' := by
      funext S' h'
      exact h S' $ lt_of_lt_of_le h' hS
    show B.divisorRed S (fun S' _ => L.maxOrderRed S') j
        = B.divisorRed S (fun S' _ => L'.maxOrderRed S') j
    exact congrArg (fun f => B.divisorRed S f j) hinner
  show B.orderRed T (fun S _ j => B.divisorFamily L.maxOrderRed j S)
      = B.orderRed T fun S _ j => B.divisorFamily L'.maxOrderRed j S
  exact congrArg (B.orderRed T) hfun

theorem nextLevel_maxOrderReduction_congr :
    (B.nextLevel L).maxOrderRed T = (B.nextLevel L').maxOrderRed T := by
  have hfun := by
    funext S hS
    exact nextLevel_orderReduction_congr B L L' S fun S' h' => h S' $ lt_of_lt_of_le h' hS
  show B.maxOrderRed T (fun S _ => (B.nextLevel L).orderRed S)
      = B.maxOrderRed T fun S _ => (B.nextLevel L').orderRed S
  exact congrArg (B.maxOrderRed T) hfun
end

theorem inputLevelData_reductions_eq_of_dim_lt :
    ∀ d T, T.krullDimSucc ≤ d → ∀ m M, d < m → m ≤ M →
      (B.inputLevelData m).maxOrderRed T = (B.inputLevelData M).maxOrderRed T ∧
        (B.inputLevelData m).orderRed T = (B.inputLevelData M).orderRed T := by
  intro d
  induction d with
  | zero =>
      intro T hT m M hm hmM
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have h0 : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc < T.krullDimSucc →
          (B.inputLevelData m').maxOrderRed S = (B.inputLevelData M').maxOrderRed S := by simp_all
      exact ⟨nextLevel_maxOrderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0,
        nextLevel_orderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0⟩
  | succ d ih =>
      intro T hT m M hm hmM
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have h0 : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc < T.krullDimSucc →
          (B.inputLevelData m').maxOrderRed S = (B.inputLevelData M').maxOrderRed S := by
        intro S hS
        exact an1 $ ih S (by omega) m' M' (by omega) $ by omega
      exact ⟨nextLevel_maxOrderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0,
        nextLevel_orderReduction_congr B (B.inputLevelData m') (B.inputLevelData M') T h0⟩

section
variable (hB : B.ReducesInductivelyOnDimension) (n : ℕ)
include hB
theorem inputLevelData_isMaxOrderReduction :
    IsMaxOrderReduction (fun d => d < n) (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed := by
  induction n with
  | zero => exact isMaxOrderReduction_of_forall_not _ not_lt_zero _ _
  | succ n ih =>
      exact (hB.maxOrderSpec n (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed $ hB.orderSpec n (fun j => B.divisorFamily (B.inputLevelData n).maxOrderRed j) (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih (fun j => hB.divisorSpec n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih j) $ hB.divisorShift n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih).mono (· < n + 1) fun m hm => mp_ lt_succ_iff hm

theorem isOrderReduction_outputLevelData :
    IsOrderReduction (fun d => d ≤ n) (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed :=
  hB.orderSpec n (fun j => B.divisorFamily (B.inputLevelData n).maxOrderRed j)
    (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
    (inputLevelData_isMaxOrderReduction B hB n)
    (fun j => hB.divisorSpec n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
      (inputLevelData_isMaxOrderReduction B hB n) j)
    (hB.divisorShift n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
      (inputLevelData_isMaxOrderReduction B hB n))

theorem isMaxOrderReduction_outputLevelData :
    IsMaxOrderReduction (fun d => d ≤ n) (B.outputLevelData n).maxOrderRed (B.outputLevelData n).orderRed :=
  hB.maxOrderSpec n (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed
    (isOrderReduction_outputLevelData B hB n)
end

theorem outputLevelData_maxOrderReduction_eq_of_le {n N} (hnN : n ≤ N)
    (T : MarkedIdealWithBoundary) (hT : T.krullDimSucc ≤ n) :
    (B.outputLevelData N).maxOrderRed T = (B.outputLevelData n).maxOrderRed T :=
  (inputLevelData_reductions_eq_of_dim_lt B n T hT (n + 1) (N + 1) (lt_succ_self n)
    (succ_le_succ hnN)).1.symm

theorem outputLevelData_maxOrderReduction_eq_at_dim (T : MarkedIdealWithBoundary) {N}
    (hT : T.krullDimSucc ≤ N) :
    (B.outputLevelData N).maxOrderRed T = (B.outputLevelData T.krullDimSucc).maxOrderRed T :=
  outputLevelData_maxOrderReduction_eq_of_le B hT T le_rfl
end

end PrincipalizationRules


section
variable (k : Type) [Field k]
section
variable (X : Sch) (p : X ⟶ Sp k) (I : ISD X) (E : Bdy X)
def markedTripleOrderOne : MarkedIdealWithBoundary :=
  MarkedIdealWithBoundary.mk k X p I 1 E







@[simp] theorem markedTripleOrderOne_dim :
    (markedTripleOrderOne k X p I E).krullDimSucc = krullDimSucc X := rfl
end

theorem markedTripleOrderOne_isAdmissible [CharZero k] X
    p
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    I (hI : NonzeroOnComponents I)
    E (hE : InStrictNormalCrossingPosition p E) :
    (markedTripleOrderOne k X p I E).IsAdmissible where
  charZero := inferInstanceAs (CharZero k)
  locallyOfFiniteType := inferInstanceAs $ LocallyOfFiniteType p
  nonzeroOnComponents := hI
  one_le_mult := le_refl 1
  quasiCompact := inferInstanceAs $ QuasiCompact p
  smooth := inferInstanceAs $ Smooth p
  snc := hE
end

def SmoothSubschemeIdealIsRadical : Prop :=
  ∀ (k : Type) [Field k] (X : Sch) (p : X ⟶ Sp k)
    (Z : ISD X)
    [Smooth (subschemeι Z ≫ p)] (J : ISD X),
    (↑Z.support : Set ↥X) ⊆ (↑J.support : Set ↥X) → J ≤ Z

namespace PrincipalizationRules

def markedBlowupSeq (B : PrincipalizationRules) (k : Type) [Field k] (X : Sch)
    (p : X ⟶ Sp k) (I : ISD X)
    (E : Bdy X) : MarkedSequenceOfBlowups p I 1 E :=
  (B.outputLevelData (krullDimSucc X)).maxOrderRed (markedTripleOrderOne k X p I E)


end PrincipalizationRules

def CommutesWithClosedImmersion (B : PrincipalizationRules) : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X X' : Sch)
    (p : X ⟶ Sp k)
    [Smooth p] [LocallyOfFiniteType p]
    [QuasiCompact p]
    (p' : X' ⟶ Sp k)
    [Smooth p'] [LocallyOfFiniteType p']
    [QuasiCompact p']
    (j : X ⟶ X') [IsClosedImmersion j],
    j ≫ p' = p →
    ∀ (c : ℕ), 1 ≤ c → HasEtaleCoordCodim p' j c →
    ∀ (I : ISD X), NonzeroOnComponents I →
      NonzeroOnComponents (imageIdealSheaf j I) →
      InStrictNormalCrossingPosition p ([] : Bdy X) →
      InStrictNormalCrossingPosition p' ([] : Bdy X') →
      IsPushforwardBlowupSeq j (B.markedBlowupSeq k X p I []).toSequenceOfBlowups
        (B.markedBlowupSeq k X' p' (imageIdealSheaf j I) []).toSequenceOfBlowups

namespace PrincipalizationRules

section
variable (B : PrincipalizationRules)
theorem markedBlowupSeq_toSequenceOfBlowups_eq_of_le (k : Type) [Field k] X
    p I
    E {N} (h : krullDimSucc X ≤ N) :
    (B.markedBlowupSeq k X p I E).toSequenceOfBlowups
      = ((B.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E)).toSequenceOfBlowups := by
  let _a0 := markedTripleOrderOne k X p I E
  exact congrArg (fun s : _a0.SequenceOfBlowups => s.toSequenceOfBlowups) $ (B.outputLevelData_maxOrderReduction_eq_of_le h _a0 $ le_of_eq $ markedTripleOrderOne_dim k X p I E).symm

section
variable (hrad : SmoothSubschemeIdealIsRadical)
include hrad
section
variable (k : Type) [Field k] [CharZero k] (X : Sch) (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] (I : ISD X)
theorem hasReducedCenters_markedBlowupSeq (_hI : NonzeroOnComponents I)
    E (_hE : InStrictNormalCrossingPosition p E) :
    HasReducedCenters (B.markedBlowupSeq k X p I E) := by
  let _c0 := B.markedBlowupSeq k X p I E
  intro i hi J hJ
  have hsm : Smooth
      (siI (_c0.center i) ≫ _c0.projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact _c0.center_smooth i hi
  exact hrad k (_c0.schemeAt i) (_c0.projectionToSpec i)
    (_c0.center i) J hJ

def principalizationSeq (hI : NonzeroOnComponents I)
    (E : Bdy X) (hE : InStrictNormalCrossingPosition p E) : IdealBlowupSequence p I E :=
  (B.markedBlowupSeq k X p I E).toIdealBlowupSequence (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)
end

def principalization :
    PrincipalizationAlgorithm :=
  fun k ik icz X p ism ift iqc I hI E hE =>
    @principalizationSeq B hrad k ik icz X p ism ift iqc I hI E hE

section
variable (k : Type) [Field k] [CharZero k] (X : Sch) (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] (I : ISD X) (hI : NonzeroOnComponents I) (E : Bdy X) (hE : InStrictNormalCrossingPosition p E)
theorem principalization_toSequenceOfBlowups :
    (B.principalization hrad k X p I hI E hE).toSequenceOfBlowups
      = (B.markedBlowupSeq k X p I E).toSequenceOfBlowups :=
  MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups (B.markedBlowupSeq k X p I E)
    (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)

theorem principalization_lastIdeal :
    (B.principalization hrad k X p I hI E hE).lastIdeal
      = (B.markedBlowupSeq k X p I E).lastIdeal :=
  MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal (B.markedBlowupSeq k X p I E)
    (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)
end
end

section
variable (hB : B.ReducesInductivelyOnDimension)
include hB
section
variable (k : Type) [Field k] [CharZero k] (X : Sch) (p : X ⟶ Sp k) [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] (I : ISD X) (hI : NonzeroOnComponents I) (E : Bdy X) (hE : InStrictNormalCrossingPosition p E)
include hI hE
section
variable (X' : Sch) (p' : X' ⟶ Sp k) [Smooth p'] [LocallyOfFiniteType p'] [QuasiCompact p'] (ph_ : X' ⟶ X) [Smooth ph_]
theorem markedBlowupSeq_smoothPullback_isPullback (hph : ph_ ≫ p = p')
    (hI' : NonzeroOnComponents (comap I ph_))
    (hE' : InStrictNormalCrossingPosition p' (E.map fun D => comap D ph_)) :
    IsPullbackBlowupSequence ph_
      (B.markedBlowupSeq k X' p' (comap I ph_) (E.map fun D => comap D ph_)).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible k X' p' (cmI I ph_) hI' (E.map fun D => cmI D ph_) hE'
  let _a0 := max (krullDimSucc X) $ krullDimSucc X'
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E $ le_max_left (krullDimSucc X) $ krullDimSucc X',
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X' p' (cmI I ph_) (E.map fun D => cmI D ph_)
      (le_max_right (krullDimSucc X) $ krullDimSucc X')]
  exact @IsMaxOrderReduction.isPullbackBlowupSequence_of_smooth
    (· ≤ _a0)
    ((B.outputLevelData _a0).maxOrderRed)
    ((B.outputLevelData _a0).orderRed)
    (B.isMaxOrderReduction_outputLevelData hB _a0)
    (markedTripleOrderOne k X p I E) hV (le_max_left _ _) X' p' ph_
    (inferInstanceAs $ Smooth ph_) hph hV' $ le_max_right _ _

theorem markedBlowupSeq_smoothPullback_isStrictPullback [Surjective ph_]
    (hph : ph_ ≫ p = p')
    (hI' : NonzeroOnComponents (comap I ph_))
    (hE' : InStrictNormalCrossingPosition p' (E.map fun D => comap D ph_)) :
    IsStrictPullbackBlowupSeq ph_
      (B.markedBlowupSeq k X' p' (comap I ph_) (E.map fun D => comap D ph_)).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible k X' p' (cmI I ph_) hI' (E.map fun D => cmI D ph_) hE'
  let _a0 := max (krullDimSucc X) $ krullDimSucc X'
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E $ le_max_left (krullDimSucc X) $ krullDimSucc X',
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X' p' (cmI I ph_) (E.map fun D => cmI D ph_)
      (le_max_right (krullDimSucc X) $ krullDimSucc X')]
  exact @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective
    (· ≤ _a0)
    ((B.outputLevelData _a0).maxOrderRed)
    ((B.outputLevelData _a0).orderRed)
    (B.isMaxOrderReduction_outputLevelData hB _a0)
    (markedTripleOrderOne k X p I E) hV (le_max_left _ _) X' p' ph_
    (inferInstanceAs $ Smooth ph_)
    (inferInstanceAs $ Surjective ph_) hph hV' $ le_max_right _ _
end

section
variable (K : Type) [Field K] [CharZero K] (f) [Smooth (snd p (specMapOfFieldHom k K f))] [LocallyOfFiniteType (snd p (specMapOfFieldHom k K f))] [QuasiCompact (snd p (specMapOfFieldHom k K f))] (hI' : NonzeroOnComponents (comap I (fst p (specMapOfFieldHom k K f)))) (hE' : InStrictNormalCrossingPosition (snd p (specMapOfFieldHom k K f)) (E.map fun D => comap D (fst p (specMapOfFieldHom k K f))))
include hI' hE'
theorem markedBlowupSeq_baseChange_isPullback :
    IsPullbackBlowupSequence (fst p (specMapOfFieldHom k K f))
      (B.markedBlowupSeq K (pullback p (specMapOfFieldHom k K f))
        (snd p (specMapOfFieldHom k K f))
        (comap I (fst p (specMapOfFieldHom k K f)))
        (E.map fun D =>
          comap D (fst p (specMapOfFieldHom k K f)))).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  let _c0 := specMapOfFieldHom k K f
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  let _s0 := m131 p _c0
  let _a3 := fst p _c0
  let _a1 := cmI I _a3
  let _a4 := snd p _c0
  have hV' := markedTripleOrderOne_isAdmissible K _s0
    _a4
    _a1 hI'
    (E.map fun D => cmI D _a3) hE'
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E
      (le_max_left (krullDimSucc X)
        (krullDimSucc _s0)),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le K _s0
      _a4
      _a1
      (E.map fun D => cmI D _a3)
      (le_max_right (krullDimSucc X)
        (krullDimSucc _s0))]
  exact (B.isMaxOrderReduction_outputLevelData hB
      (max (krullDimSucc X) $ krullDimSucc _s0)).isPullbackBlowupSequence_baseChange
    (markedTripleOrderOne k X p I E) hV (le_max_left _ _) K f hV' $ le_max_right _ _

theorem markedBlowupSeq_baseChange_isStrictPullback :
    IsStrictPullbackBlowupSeq (fst p (specMapOfFieldHom k K f))
      (B.markedBlowupSeq K (pullback p (specMapOfFieldHom k K f))
        (snd p (specMapOfFieldHom k K f))
        (comap I (fst p (specMapOfFieldHom k K f)))
        (E.map fun D =>
          comap D (fst p (specMapOfFieldHom k K f)))).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  let _c0 := specMapOfFieldHom k K f
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  let _s0 := m131 p _c0
  let _a3 := fst p _c0
  let _a1 := cmI I _a3
  let _a4 := snd p _c0
  have hV' := markedTripleOrderOne_isAdmissible K _s0
    _a4
    _a1 hI'
    (E.map fun D => cmI D _a3) hE'
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E
      (le_max_left (krullDimSucc X)
        (krullDimSucc _s0)),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le K _s0
      _a4
      _a1
      (E.map fun D => cmI D _a3)
      (le_max_right (krullDimSucc X)
        (krullDimSucc _s0))]
  exact (B.isMaxOrderReduction_outputLevelData hB
      (max (krullDimSucc X) $ krullDimSucc _s0)).isStrictPullbackBlowupSeq_baseChange
    (markedTripleOrderOne k X p I E) hV (le_max_left _ _) K f hV' $ le_max_right _ _
end

theorem markedBlowupSeq_lastIdeal_eq_top :
    (B.markedBlowupSeq k X p I E).lastIdeal = ⊤ := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  let _a1 := B.markedBlowupSeq k X p I E
  apply mpr_ $ eq_top_iff_support_eq_empty _
  apply eq_empty_of_subset_empty
  intro x hx
  have hx' :=
    (mem_orderAtLeastLocus_one_iff _a1.lastIdeal x).mpr hx
  rwa [(MarkedSequenceOfBlowups.isResolution_iff _a1).mp $ (B.isMaxOrderReduction_outputLevelData hB $ krullDimSucc X).resolves (markedTripleOrderOne k X p I E) hV $ le_refl _] at hx'
end

theorem isFunctorialPrincipalization_principalization
    (hrad : SmoothSubschemeIdealIsRadical) (hemb : CommutesWithClosedImmersion B) :
    IsFunctorialPrincipalization (B.principalization hrad) where
  pushforward := by
    intro k _ _ S X pS p _ _ _ _ _ _ j _ hjp c hc hcc I hI hIX hES hEX
    rw [B.principalization_toSequenceOfBlowups hrad k S pS I hI [] hES,
      B.principalization_toSequenceOfBlowups hrad k X p (imageIdealSheaf j I) hIX [] hEX]
    exact hemb k S X pS p j hjp c hc hcc I hI hIX hES hEX
  base_change := by
    intro k _ _ X p _ _ _ I hI E hE K _ _ f _ _ _ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad K
        (m131 p $ specMapOfFieldHom k K f)
        (snd p $ specMapOfFieldHom k K f)
        (cmI I $ fst p $ specMapOfFieldHom k K f) hI'
        (E.map fun D => cmI D $ fst p $ specMapOfFieldHom k K f) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_baseChange_isPullback hB k X p I hI E hE K f hI' hE'
  base_change_strict := by
    intro k _ _ X p _ _ _ I hI E hE K _ _ f _ _ _ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad K
        (m131 p $ specMapOfFieldHom k K f)
        (snd p $ specMapOfFieldHom k K f)
        (cmI I $ fst p $ specMapOfFieldHom k K f) hI'
        (E.map fun D => cmI D $ fst p $ specMapOfFieldHom k K f) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_baseChange_isStrictPullback hB k X p I hI E hE K f hI' hE'
  lastIdeal_eq_top := by
    intro k _ _ X p _ _ _ I hI E hE
    rw [B.principalization_lastIdeal hrad k X p I hI E hE]
    exact B.markedBlowupSeq_lastIdeal_eq_top hB k X p I hI E hE
  smooth_pullback := by
    intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ ph_ _ hph hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad k X' p' (cmI I ph_) hI'
        (E.map fun D => cmI D ph_) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_smoothPullback_isPullback hB k X p I hI E hE X' p' ph_ hph hI' hE'
  smooth_pullback_strict := by
    intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ ph_ _ _ hph hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad k X' p' (cmI I ph_) hI'
        (E.map fun D => cmI D ph_) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_smoothPullback_isStrictPullback hB k X p I hI E hE X' p' ph_ hph hI' hE'
end
end

end PrincipalizationRules


theorem smoothSubschemeIdealIsRadical : SmoothSubschemeIdealIsRadical := by
  intro k ik X p Z ism J hsub
  have hstalk : ∀ x, _root_.IsReduced $ Z.subscheme.presheaf.stalk x := by
    intro x
    have := isDomain_stalk_of_smooth (siI Z ≫ p) x
    infer_instance
  have hred :=
    isReduced_of_isReduced_stalk Z.subscheme
  have hcomp : ∀ U,
      _root_.IsReduced $ Z.subscheme.presheaf.obj $ m112 U :=
    AlgebraicGeometry.IsReduced.component_reduced
  have hZrad : ∀ U, (Z.ideal U).radical ≤ Z.ideal U := by
    intro U
    rw [← Z.ker_subschemeι_app U]
    intro x hx
    obtain ⟨n, hn⟩ := hx
    rw [mem_ker, map_pow] at hn
    rw [mem_ker]
    exact IsNilpotent.eq_zero ⟨n, hn⟩
  have hle := SetLike.coe_subset_coe.mp hsub
  have hJv : J ≤ vanishingIdeal Z.support := by
    apply mp_ $ gc J Z.support
    exact hle
  rw [vanishingIdeal_support] at hJv
  refine le_trans hJv ?_
  rw [le_def]
  intro U
  rw [radical_ideal]
  exact hZrad U


section

variable {k : Type} [Field k] {X W : Sch}

section
variable (f : X ⟶ Sp k) (c : W ⟶ X) (K : Type) [Field K]
theorem pullbackCondition_baseChangeMap [Algebra k K] :
    (baseChangeProjection (c ≫ f) K ≫ c) ≫ f = baseChangeToSpec (c ≫ f) K ≫ specMapAlgebraMap k K := by
  rw [assoc]
  exact pullback.condition

def baseChangeMap [Algebra k K] :
    baseChange (c ≫ f) K ⟶ baseChange f K :=
  pullback.lift (baseChangeProjection (c ≫ f) K ≫ c) (baseChangeToSpec (c ≫ f) K)
    (pullbackCondition_baseChangeMap f c K)

@[simp]
theorem baseChangeMap_comp_baseChangeProjection [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c :=
  pullback.lift_fst _ _ _

@[simp]
theorem baseChangeMap_comp_baseChangeToSpec [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K :=
  pullback.lift_snd _ _ _

theorem isPullback_baseChangeMap [Algebra k K] :
    IsPullback (baseChangeMap f c K) (baseChangeProjection (c ≫ f) K) (baseChangeProjection f K) c := by
  let _a0 := specMapAlgebraMap k K
  have h1 := (of_hasPullback (c ≫ f) _a0).flip
  refine of_right ?_ (baseChangeMap_comp_baseChangeProjection f c K) $ (of_hasPullback f _a0).flip
  rwa [baseChangeMap_comp_baseChangeToSpec]
end

theorem morphismProperty_of_isPullback {P : MorphismProperty Sch}
    [P.IsStableUnderBaseChange] {A B C' D : Sch} {h : A ⟶ B} {v : A ⟶ C'} {v' : B ⟶ D}
    {b : C' ⟶ D} (sq : IsPullback h v v' b) (hb : P b) : P h :=
  of_isPullback sq.flip hb

instance instEtaleBaseChangeMap (f : X ⟶ Sp k) (c : W ⟶ X) [Etale c]
    (K : Type) [Field K] [Algebra k K] : Etale (baseChangeMap f c K) :=
  by
  exact morphismProperty_of_isPullback (P := @Etale) (isPullback_baseChangeMap f c K) ‹Etale c›

instance instSurjectiveBaseChangeMap (f : X ⟶ Sp k) (c : W ⟶ X) [Surjective c]
    (K : Type) [Field K] [Algebra k K] : Surjective (baseChangeMap f c K) :=
  by
  exact morphismProperty_of_isPullback (P := @Surjective) (isPullback_baseChangeMap f c K) ‹Surjective c›

theorem isAffine_baseChange (p : W ⟶ Sp k) [IsAffine W]
    (K : Type) [Field K] [Algebra k K] : IsAffine (baseChange p K) := by
  have :=
    morphismProperty_of_isPullback (P := @IsAffineHom) (of_hasPullback p $ specMapAlgebraMap k K)
      inferInstance
  exact isAffine_of_isAffineHom (f := baseChangeProjection p K)

theorem isReduced_of_isReduced_stalk (Y : Sch)
    (h : ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y)) : IsReduced Y := by
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk Y

theorem isReduced_stalk_of_isOpenImmersion {A B : Sch} (w : A ⟶ B)
    [IsOpenImmersion w] [IsReduced B] a : _root_.IsReduced (A.presheaf.stalk a) :=
  isReduced_of_injective (m83 $ w.stalkMap a).hom
    (m189 $ m83 $ w.stalkMap a).1

theorem isReduced_of_isReduced_stalk_of_cover {Y : Sch} {ι : Type} {Z : ι → Sch}
    (j : ∀ i, Z i ⟶ Y) (hj : ∀ i, IsOpenImmersion (j i))
    (hZ : ∀ (i : ι) (z : ↥(Z i)), _root_.IsReduced ((Z i).presheaf.stalk z))
    (hcov : ∀ y : ↥Y, ∃ (i : ι) (z : ↥(Z i)), (j i).base z = y) : IsReduced Y := by
  refine isReduced_of_isReduced_stalk Y ?_
  intro y
  obtain ⟨i, z, rfl⟩ := hcov y
  let _a0 := (j i).stalkMap z
  exact isReduced_of_injective _a0.hom
    (m189 _a0).1

theorem sigma_jointly_surjective {ι : Type} (Z : ι → Sch) (x : ↥(∐ Z)) :
    ∃ (i : ι) (y : ↥(Z i)), (Sigma.ι Z i).base y = x := by
  obtain ⟨y, hy⟩ := (sigmaOpenCover Z).covers x
  exact ⟨_, y, hy⟩

theorem exists_pullback_snd_base_eq {A B C' : Sch} (g1 : A ⟶ C') (g2 : B ⟶ C')
    (a : ↥A) (b : ↥B) (h : g1.base a = g2.base b) :
    ∃ z : ↥(pullback g1 g2), (pullback.snd g1 g2).base z = b := by
  obtain ⟨z, _, hz2⟩ := m198 (f := g1) (g := g2) a b h
  exact ⟨z, hz2⟩

theorem exists_etale_surjective_affine_cover_baseChange (X : Sch) (f : X ⟶ Sp k)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (K : Type) [Field K] [Algebra k K] [IsReduced (baseChange f K)] :
    ∃ (W : Sch) (c : W ⟶ X) (g : baseChange (c ≫ f) K ⟶ baseChange f K),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType (c ≫ f) ∧ QuasiCompact (c ≫ f) ∧
        Etale c ∧ Surjective c ∧
        IsAffine (baseChange (c ≫ f) K) ∧ IsReduced (baseChange (c ≫ f) K) ∧
        LocallyOfFiniteType (baseChangeToSpec (c ≫ f) K) ∧
        QuasiCompact (baseChangeToSpec (c ≫ f) K) ∧
        Etale g ∧ Surjective g ∧
        g ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K ∧
        g ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c := by
  let _a0 := specMapAlgebraMap k K
  have := QuasiCompact.compactSpace_of_compactSpace (f := f)
  obtain ⟨ι, hio, U, hUaff, hUtop⟩ := exists_finite_affine_cover X
  have := hio
  have hWaff := isAffine_sigmaOpens X U hUaff
  have hsurj := surjective_sigmaOpensDesc X U hUtop
  have hbcaff :=
    by
    exact isAffine_baseChange (sigmaOpensDesc X U ≫ f) K
  have _i20 : IsReduced $ baseChange (sigmaOpensDesc X U ≫ f) K := by
    let _a1 := sigmaOpensDesc X U
    let _a0 := baseChangeMap f _a1 K
    let _c0 := baseChangeProjection (_a1 ≫ f) K
    have hsq : ∀ i, IsPullback
        (pullback.snd (Sigma.ι (fun i => oSch $ U i) i)
            _c0 ≫
          _a0)
        (pullback.fst (Sigma.ι (fun i => oSch $ U i) i)
          _c0)
        (baseChangeProjection f K) $ opI $ U i := by
      intro i
      have h := IsPullback.paste_horiz
        (of_hasPullback (Sigma.ι (fun i => oSch $ U i) i)
          _c0).flip
        (isPullback_baseChangeMap f _a1 K)
      rwa [sigma_io_sigmaOpensDesc X U i] at h
    refine isReduced_of_isReduced_stalk_of_cover
      (Z := fun i => pullback (Sigma.ι (fun i => oSch $ U i) i)
        _c0)
      (fun i => pullback.snd (Sigma.ι (fun i => oSch $ U i) i)
        _c0)
      (fun i => inferInstance) (fun i z => ?_) ?_
    have :=
      morphismProperty_of_isPullback (P := @IsOpenImmersion) (hsq i) inferInstance
    exact isReduced_stalk_of_isOpenImmersion
      (pullback.snd (Sigma.ι (fun i => oSch $ U i) i)
        _c0 ≫
        _a0) z
    intro p
    obtain ⟨i, y, hy⟩ := sigma_jointly_surjective (fun i => oSch $ U i)
      (bsM _c0 p)
    obtain ⟨z, hz⟩ := exists_pullback_snd_base_eq (Sigma.ι (fun i => oSch $ U i) i)
      _c0 y p hy
    exact ⟨i, z, hz⟩
  exact ⟨sigmaOpens X U, sigmaOpensDesc X U, baseChangeMap f (sigmaOpensDesc X U) K,
    hWaff, inferInstance, inferInstance, inferInstance, inferInstance, hsurj, hbcaff,
    _i20, morphismProperty_of_isPullback (P := @LocallyOfFiniteType) (of_hasPullback (sigmaOpensDesc X U ≫ f) _a0).flip inferInstance, morphismProperty_of_isPullback (P := @QuasiCompact) (of_hasPullback (sigmaOpensDesc X U ≫ f) _a0).flip inferInstance, inferInstance, inferInstance,
    baseChangeMap_comp_baseChangeToSpec f (sigmaOpensDesc X U) K,
    baseChangeMap_comp_baseChangeProjection f (sigmaOpensDesc X U) K⟩

end




section
variable {X} {k : Type} [Field k] (p : X ⟶ Sp k)
theorem locallyOfFiniteType_baseChangeToSpec [LocallyOfFiniteType p]
    (K : Type) [Field K] [Algebra k K] :
    LocallyOfFiniteType (baseChangeToSpec p K) :=
  of_isPullback
    (of_hasPullback p $ specMapAlgebraMap k K)
    (inferInstanceAs $ LocallyOfFiniteType p)

theorem quasiCompact_baseChangeToSpec [QuasiCompact p]
    (K : Type) [Field K] [Algebra k K] :
    QuasiCompact (baseChangeToSpec p K) :=
  of_isPullback
    (of_hasPullback p $ specMapAlgebraMap k K)
    (inferInstanceAs $ QuasiCompact p)
end

structure EmbeddingDatum (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) where
  ambient : Sch
  ambientStruct : ambient ⟶ Sp k
  emb : Y ⟶ ambient
  isAffine_ambient : IsAffine ambient
  smooth_ambientStruct : Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : QuasiCompact ambientStruct
  isClosedImmersion_emb : IsClosedImmersion emb
  nonzeroOnComponents_ker : NonzeroOnComponents emb.ker
  comp_eq : emb ≫ ambientStruct = p
  sncEmpty : InStrictNormalCrossingPosition ambientStruct ([] : Bdy ambient)

namespace EmbeddingDatum

variable {k : Type} [Field k] [CharZero k] {Y}
  {p : Y ⟶ Sp k}

instance instIsAffineAmbient (D : EmbeddingDatum k Y p) :
    IsAffine D.ambient := D.isAffine_ambient

instance instSmoothAmbientStruct (D : EmbeddingDatum k Y p) :
    Smooth D.ambientStruct := D.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (D : EmbeddingDatum k Y p) :
    LocallyOfFiniteType D.ambientStruct :=
  D.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (D : EmbeddingDatum k Y p) :
    QuasiCompact D.ambientStruct := D.quasiCompact_ambientStruct

instance instIsClosedImmersionEmb (D : EmbeddingDatum k Y p) :
    IsClosedImmersion D.emb := D.isClosedImmersion_emb

end EmbeddingDatum

def embeddingDatumOfClosedImmersion {k : Type} [Field k] [CharZero k] {Y : Sch}
    {p : Y ⟶ Sp k} (A : Sch) [IsAffine A]
    (q : A ⟶ Sp k) [Smooth q]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (e : Y ⟶ A) [IsClosedImmersion e]
    (hker : NonzeroOnComponents e.ker) (hcomp : e ≫ q = p)
    (hsnc : InStrictNormalCrossingPosition q ([] : Bdy A)) :
    EmbeddingDatum k Y p where
  ambient := A
  ambientStruct := q
  emb := e
  isAffine_ambient := inferInstance
  smooth_ambientStruct := inferInstance
  locallyOfFiniteType_ambientStruct := inferInstance
  quasiCompact_ambientStruct := inferInstance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := hker
  comp_eq := hcomp
  sncEmpty := hsnc

namespace EmbeddingDatum

variable {k : Type} [Field k] [CharZero k] {Y}
  {p : Y ⟶ Sp k}

section
variable (D : EmbeddingDatum k Y p) (K : Type) [Field K]
theorem pullbackCondition_baseChangeEmb
    [Algebra k K] :
    (baseChangeProjection p K ≫ D.emb) ≫ D.ambientStruct =
      baseChangeToSpec p K ≫ specMapAlgebraMap k K := by
  rw [assoc, D.comp_eq]
  exact pullback.condition

def baseChangeEmb [Algebra k K] :
    baseChange p K ⟶ baseChange D.ambientStruct K :=
  pullback.lift (baseChangeProjection p K ≫ D.emb) (baseChangeToSpec p K)
    (pullbackCondition_baseChangeEmb D K)

section
variable [hv3_0 : Algebra k K]
include hv3_0
@[simp]
theorem baseChangeEmb_comp_baseChangeProjection :
    D.baseChangeEmb K ≫ baseChangeProjection D.ambientStruct K = baseChangeProjection p K ≫ D.emb :=
  pullback.lift_fst _ _ _

@[simp]
theorem baseChangeEmb_comp_baseChangeToSpec :
    D.baseChangeEmb K ≫ baseChangeToSpec D.ambientStruct K = baseChangeToSpec p K :=
  pullback.lift_snd _ _ _

theorem isPullback_baseChangeEmb :
    IsPullback (D.baseChangeEmb K) (baseChangeProjection p K) (baseChangeProjection D.ambientStruct K)
      D.emb := by
  let _a0 := specMapAlgebraMap k K
  refine of_right ?_ (baseChangeEmb_comp_baseChangeProjection D K)
    (of_hasPullback D.ambientStruct _a0).flip
  rw [baseChangeEmb_comp_baseChangeToSpec D K, D.comp_eq]
  exact (of_hasPullback p _a0).flip

theorem isClosedImmersion_baseChangeEmb : IsClosedImmersion (D.baseChangeEmb K) :=
  of_isPullback
    (isPullback_baseChangeEmb D K).flip D.isClosedImmersion_emb
end
end

instance instIsClosedImmersionBaseChangeEmb (D : EmbeddingDatum k Y p) (K : Type) [Field K]
    [Algebra k K] : IsClosedImmersion (D.baseChangeEmb K) :=
  isClosedImmersion_baseChangeEmb D K

section
variable (D : EmbeddingDatum k Y p) (K : Type) [Field K]
section
variable [hv3_0 : Algebra k K]
include hv3_0
theorem isAffine_baseChange_ambientToSpec : IsAffine (baseChange D.ambientStruct K) :=
  isAffine_baseChange D.ambientStruct K

theorem smooth_baseChangeToSpec_ambientToSpec :
    Smooth (baseChangeToSpec D.ambientStruct K) :=
  by
  let p := D.ambientStruct
  exact of_isPullback
    (of_hasPullback p $ specMapAlgebraMap k K)
    (inferInstanceAs $ Smooth p)

theorem locallyOfFiniteType_baseChangeToSpec_ambientToSpec :
    LocallyOfFiniteType (baseChangeToSpec D.ambientStruct K) :=
  locallyOfFiniteType_baseChangeToSpec D.ambientStruct K

theorem quasiCompact_baseChangeToSpec_ambientToSpec :
    QuasiCompact (baseChangeToSpec D.ambientStruct K) :=
  quasiCompact_baseChangeToSpec D.ambientStruct K
end

def baseChange [CharZero K]
    [Algebra k K]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (EmbeddedResolution.baseChange D.ambientStruct K).IdealSheafData)) :
    EmbeddingDatum K (EmbeddedResolution.baseChange p K) (baseChangeToSpec p K) where
  ambient := EmbeddedResolution.baseChange D.ambientStruct K
  ambientStruct := baseChangeToSpec D.ambientStruct K
  emb := D.baseChangeEmb K
  isAffine_ambient := isAffine_baseChange_ambientToSpec D K
  smooth_ambientStruct := smooth_baseChangeToSpec_ambientToSpec D K
  locallyOfFiniteType_ambientStruct := locallyOfFiniteType_baseChangeToSpec_ambientToSpec D K
  quasiCompact_ambientStruct := quasiCompact_baseChangeToSpec_ambientToSpec D K
  isClosedImmersion_emb := isClosedImmersion_baseChangeEmb D K
  nonzeroOnComponents_ker := hker
  comp_eq := baseChangeEmb_comp_baseChangeToSpec D K
  sncEmpty := hsnc
end

end EmbeddingDatum

abbrev EmbeddedResolutionRule : Type 1 :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y], EmbeddingDatum k Y p → SequenceOfBlowups Y

abbrev EmbeddingChoice : Type 1 :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y], EmbeddingDatum k Y p

section
variable (R : EmbeddedResolutionRule)
def EmbeddedResolutionRule.toAffineResolutionRule (S : EmbeddingChoice) :
    AffineResolutionRule :=
  fun k _ _ Y p _ _ _ _ => R k Y p (S k Y p)

@[simp]
theorem EmbeddedResolutionRule.toAffineResolutionRule_apply (S : EmbeddingChoice)
    (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] :
    R.toAffineResolutionRule S k Y p = R k Y p (S k Y p) := rfl

def EmbeddedResolutionRule.HasProperCenters : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (D : EmbeddingDatum k Y p) (i : ℕ),
    i < (R k Y p D).length → (R k Y p D).center i ≠ ⊤

def EmbeddedResolutionRule.IsCompatibleWithSmoothAmbientMaps : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y Y' : Sch)
    (p : Y ⟶ Sp k) (p' : Y' ⟶ Sp k)
    [LocallyOfFiniteType p] [QuasiCompact p]
    [IsReduced Y] [IsAffine Y]
    [LocallyOfFiniteType p'] [QuasiCompact p']
    [IsReduced Y'] [IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (ph_ : D'.ambient ⟶ D.ambient) [Smooth ph_] (ps_ : Y' ⟶ Y),
    ph_ ≫ D.ambientStruct = D'.ambientStruct →
    IsPullback D'.emb ps_ ph_ D.emb →
    IsPullbackBlowupSequence ps_ (R k Y' p' D') (R k Y p D)

def EmbeddedResolutionRule.IsCompatibleWithFieldBaseChange : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (D : EmbeddingDatum k Y p) (K : Type) [Field K]
    [CharZero K] [Algebra k K] [IsReduced (baseChange p K)]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (baseChange D.ambientStruct K).IdealSheafData)),
    haveI : IsAffine (baseChange p K) := isAffine_baseChange p K
    haveI : LocallyOfFiniteType (baseChangeToSpec p K) :=
      locallyOfFiniteType_baseChangeToSpec p K
    haveI : QuasiCompact (baseChangeToSpec p K) :=
      quasiCompact_baseChangeToSpec p K
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) (baseChangeToSpec p K) (D.baseChange K hker hsnc))
      (R k Y p D)
end





structure ClosedEmbeddingIntoAffineSpace {k : Type} [Field k] [CharZero k] {Y : Sch}
    {p : Y ⟶ Sp k} (G : EmbeddingDatum k Y p) where
  codimBound : ℕ
  dim : ℕ
  toAffine : G.ambient ⟶ affineSpaceIndexedBy k (UFin dim)
  one_le_codimBound : 1 ≤ codimBound
  one_le_dim : 1 ≤ dim
  isClosedImmersion_toAffine : IsClosedImmersion toAffine
  toAffine_comp : toAffine ≫ affineSpaceIndexedByToSpec k (UFin dim) = G.ambientStruct
  locallyConstCodim :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (UFin dim)) toAffine codimBound

namespace ClosedEmbeddingIntoAffineSpace

variable {k : Type} [Field k] [CharZero k] {Y}
  {p} {G : EmbeddingDatum k Y p}

instance instIsClosedImmersionToAffine (P : ClosedEmbeddingIntoAffineSpace G) :
    IsClosedImmersion P.toAffine :=
  P.isClosedImmersion_toAffine

end ClosedEmbeddingIntoAffineSpace

def EmbeddedResolutionRule.IsIndependentOfPresentedEmbedding (R : EmbeddedResolutionRule) : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (Y : Sch)
    (p : Y ⟶ Sp k) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsReduced Y]
    [IsAffine Y] (D D' : EmbeddingDatum k Y p),
    ClosedEmbeddingIntoAffineSpace D → ClosedEmbeddingIntoAffineSpace D' →
    (R k Y p D).Isomorphic (R k Y p D')

end FunctorialResolution.EmbeddedResolution

end
section
open TensorProduct

namespace FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf

variable {W Y : Sch}

theorem one_mem_map_colon_of_mem_map {R S : Type} [CommRing R] [CommRing S] (ph_ : R →+* S)
    (hph : Flat ph_) (L : Ideal R) a (h : ph_ a ∈ L.map ph_) :
    (1 : S) ∈ Ideal.map ph_ (Submodule.comap (lsmul R R a) L) := by
  let _c0 := L.mkQ (1 : R)
  let _a2 := lsmul R R a
  let _c1 := Submodule.comap _a2 L
  let _ := ph_.toAlgebra
  have : Module.Flat R S := hph
  have halg : (algebraMap R S) = ph_ := rfl
  let _a0 := (L.mkQ).comp _a2
  have hex : Exact (subtype _c1)
      _a0 := by
    rw [exact_iff, LinearMap.ker_comp, ker_mkQ, range_subtype]
  have hex2 := Module.Flat.lTensor_exact (M := S) hex
  have key : ∀ s, s ∈ L.map ph_ → s ⊗ₜ[R] _c0 = 0 := by
    intro s hs
    let ps_ : S →ₗ[S] S ⊗[R] (R ⧸ L) :=
      { toFun := fun t => t ⊗ₜ[R] _c0
        map_add' := fun x y => add_tmul x y _
        map_smul' := fun c x => smul_tmul' c x _ }
    have hps_ : ∀ t, ps_ t = t ⊗ₜ[R] _c0 := fun _ => rfl
    have hsub : L.map ph_ ≤ m177 ps_ := by
      rw [map_le_iff_le_comap]
      intro l hl
      have h0 : l • _c0 = 0 := by
        rw [← map_smul]
        simp only [mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one]
        exact hl
      simp only [mem_comap, LinearMap.mem_ker, hps_]
      rw [show ph_ l = l • (1 : S) from by rw [smul_def, halg, mul_one],
        smul_tmul, h0, tmul_zero]
    have hker := LinearMap.mem_ker.mp $ hsub hs
    rwa [hps_] at hker
  let _a1 := (1 : S)
  have hzero : (lTensor S _a0)
      (_a1 ⊗ₜ[R] (1 : R)) = 0 := by
    rw [lTensor_tmul]
    show _a1 ⊗ₜ[R] (L.mkQ (a * (1 : R))) = 0
    rw [mul_one]
    have h1 : (L.mkQ a) = a • _c0 := by
      rw [← map_smul]
      simp
    rw [h1, ← smul_tmul,
      show a • _a1 = ph_ a from by rw [smul_def, halg, mul_one]]
    exact key _ h
  obtain ⟨v, hv⟩ := mp_ (hex2 (_a1 ⊗ₜ[R] (1 : R))) hzero
  have hrange : ∀ u : S ⊗[R] _c1,
      (rid R S) (lTensor S
        (subtype _c1) u)
      ∈ m6 ph_ _c1 := by
    intro u
    induction u using induction_on with
    | zero => simp
    | tmul s c =>
        rw [lTensor_tmul, rid_tmul, smul_def, halg]
        exact mul_mem_right _ _ $ mem_map_of_mem ph_ c.2
    | add u1 u2 h1_ h2_ =>
        rw [map_add, map_add]
        exact m60 _ h1_ h2_
  have hfin := hrange v
  rwa [hv, rid_tmul, one_smul] at hfin

section
variable {X : Sch} {U} (hU : IsAffineOpen U)
include hU
theorem exists_not_mem_basicOpen_of_ne_top
    (C : Ideal (X.sec U)) (hC : C ≠ ⊤) :
    ∃ x ∈ U, ∀ c ∈ C, x ∉ basicOpen X c := by
  obtain ⟨m, hm, hCm⟩ := C.exists_le_maximal hC
  let p : PrimeSpectrum U.sec := ⟨m, hm.isPrime⟩
  refine ⟨hU.fromSpec.base p, ?_, ?_⟩
  have hr : hU.fromSpec.base p ∈ range hU.fromSpec.base := ⟨p, rfl⟩
  rwa [hU.range_fromSpec] at hr
  intro c hc hmem
  have h1 : p ∈ hU.fromSpec ⁻¹ᵁ bOpn X c := hmem
  rw [hU.fromSpec_preimage_basicOpen] at h1
  exact h1 $ hCm hc

private theorem exists_mem_basicOpen_of_span_eq_top
    (s : Set (X.sec U)) (hs : span s = ⊤) (x : X) (hx : x ∈ U) :
    ∃ c ∈ s, x ∈ X.basicOpen c := by
  have hxr : x ∈ range hU.fromSpec.base := by simp_all
  obtain ⟨p, hp⟩ := hxr
  by_contra hcon
  push Not at hcon
  have hsub : s ⊆ (p.asIdeal : Set $ xSec X U) := by
    intro c hcs
    have h1 : ¬ (p ∈ hU.fromSpec ⁻¹ᵁ bOpn X c) := by
      intro hmem
      exact hcon c hcs (by rw [← hp]; exact hmem)
    rw [hU.fromSpec_preimage_basicOpen] at h1
    have h2 : c ∈ p.asIdeal := by
      by_contra hcc
      exact h1 hcc
    simpa using h2
  have hle := Ideal.span_le.mpr hsub
  rw [hs] at hle
  exact p.2.ne_top $ mp_ top_le_iff hle
end

section
variable (g : W ⟶ Y) [Flat g]
theorem flat_appLE (U : Y.affineOpens)
    (V : W.affineOpens) (e : (V : Opn W) ≤ g ⁻¹ᵁ (U : Opn Y)) :
    Flat (appLE g (U : Opn Y) (V : Opn W) e).hom := by
  apply AlgebraicGeometry.HasRingHomProperty.appLE (P := @Flat)
  all_goals assumption

section
variable [Surjective g] (I J : ISD Y)
theorem colon_eq_top_of_comap_le
    (h : I.comap g ≤ J.comap g) (U : Y.affineOpens) (a : (Y.sec (U : Opn Y)))
    (ha : a ∈ I.ideal U) (C : Ideal (Y.sec (U : Opn Y)))
    (hCdef : C = Submodule.comap
      (lsmul (Y.sec (U : Opn Y)) (Y.sec (U : Opn Y)) a) (J.ideal U)) :
    C = ⊤ := by
  by_contra hCtop
  obtain ⟨x, hxU, hx⟩ := exists_not_mem_basicOpen_of_ne_top U.2 C hCtop
  obtain ⟨w, hw⟩ := AlgebraicGeometry.Surjective.surj (f := g) x
  have hwU : w ∈ preU g U := by simp_all
  obtain ⟨V, hV, hwV, hVU⟩ :=
    (isBasis_iff_nbhd.mp W.isBasis_affineOpens) hwU
  have hV' := hV
  have hcomap0 := Scheme.IdealSheafData.le_def.mp h ⟨V, hV'⟩
  rw [comap_ideal_eq_map_appLE I g U ⟨V, hV'⟩ hVU,
    comap_ideal_eq_map_appLE J g U ⟨V, hV'⟩ hVU] at hcomap0
  have hflat := flat_appLE g U ⟨V, hV'⟩ hVU
  have hone := one_mem_map_colon_of_mem_map (appLE g U V hVU).hom hflat (J.ideal U) a
    (hcomap0 $ mem_map_of_mem _ ha)
  rw [← hCdef] at hone
  have htop :=
    (eq_top_iff_one _).mpr hone
  have hspan : span (((appLE g U V hVU).hom) ''
      (C : Set $ xSec Y U)) = ⊤ := by
    rwa [← map_span, span_eq]
  obtain ⟨f, hf, hwf⟩ := exists_mem_basicOpen_of_span_eq_top hV' _ hspan w hwV
  obtain ⟨c, hc, hcf⟩ := hf
  have hwb : w ∈ bOpn W ((appLE g U V hVU).hom c) := by
    rwa [hcf]
  have hbeta : bOpn W ((appLE g U V hVU).hom c) ≤ g ⁻¹ᵁ (bOpn Y c) := by
    rw [preimage_basicOpen]
    simp [appLE]
  have hmem := hbeta hwb
  exact hx c hc (by rw [← hw]; exact hmem)

theorem le_of_comap_le
    (h : comap I g ≤ comap J g) : I ≤ J := by
  rw [le_def]
  intro U a ha
  have hC := colon_eq_top_of_comap_le g I J h U a ha _ rfl
  let _m0 := xSec Y U
  have h1 : 1 ∈ Submodule.comap
      (lsmul _m0 _m0 a) (J.ideal U) := by
    rw [hC]
    exact mem_top
  simpa using h1

theorem eq_of_comap_eq
    (h : comap I g = comap J g) : I = J :=
  le_antisymm (le_of_comap_le g I J $ le_of_eq h) $ le_of_comap_le g J I $ le_of_eq h.symm
end
end

end FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
end
section
open Limits

namespace FunctorialResolution.EmbeddedResolution

theorem map_eq_ker {X Y : Sch} (I : ISD X) (f : X ⟶ Y) :
    I.map f = (subschemeι I ≫ f).ker := rfl

private theorem comap_eq_ker_pullback_fst {X Y : Sch} (I : ISD Y) (f : X ⟶ Y) :
    comap I f = (pullback.fst f I.si).ker := rfl

theorem comap_map_eq_map_comap_of_isPullback {W X X' W' : Sch} {f : W ⟶ X} {g : X' ⟶ X}
    {g' : W' ⟶ W} {f' : W' ⟶ X'} (H : IsPullback g' f' f g)
    [QuasiCompact f] [Flat g] (I : ISD W) :
    comap (I.map f) g = (comap I g').map f' := by
  have hqc : QuasiCompact $ siI I ≫ f := inferInstance
  have S := (of_hasPullback g' I.si).flip.paste_vert H
  have hqc' := quasiCompact_of_isPullback S
  have h1 := ker_eq_comap_ker_of_isPullback_of_flat S
  rw [map_eq_ker, ← h1, ker_comp, comap_eq_ker_pullback_fst]

theorem comap_map_eq_self_of_isPullback {W X Q : Sch} (ga_ : W ⟶ X)
    [QuasiCompact ga_] [Flat ga_] {p q : Q ⟶ W} (H : IsPullback p q ga_ ga_)
    (I : ISD W) (hI : comap I p = comap I q) :
    comap (I.map ga_) ga_ = I := by
  have key := comap_map_eq_map_comap_of_isPullback H I
  rw [hI] at key
  rw [key]
  obtain ⟨s, hsq⟩ : ∃ s, s ≫ q = 𝟙 W :=
    ⟨H.lift (𝟙 W) (𝟙 W) rfl, H.lift_snd _ _ _⟩
  refine le_antisymm ?_ $ le_map_comap I q
  have h1 := comap_map_le (cmI I q) q
  have h2 : comap (comap ((cmI I q).map q) q) s ≤ (comap (cmI I q) s) :=
    comap_mono s h1
  rwa [← comap_comp, ← comap_comp, hsq,
    comap_id, comap_id] at h2




structure SmoothLocalChart {k : Type} [Field k] [CharZero k] {Y V : Sch}
    {pY : Y ⟶ Sp k} {pV : V ⟶ Sp k}
    (G : EmbeddingDatum k Y pY) (H : EmbeddingDatum k V pV) (u : V ⟶ Y) (y : ↥V) where
  func : Γ(H.ambient, ⊤)
  mem_domain : y ∈ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)
  ambient : Sch
  ambientStruct : ambient ⟶ Sp k
  isAffine_ambient : IsAffine ambient
  smooth_ambientStruct : Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : QuasiCompact ambientStruct
  toAmbient : ambient ⟶ G.ambient
  smooth_toAmbient : Smooth toAmbient
  comp_eq : toAmbient ≫ G.ambientStruct = ambientStruct
  imm : (H.emb ⁻¹ᵁ H.ambient.basicOpen func).toScheme ⟶ ambient
  isPullback :
    CategoryTheory.IsPullback imm ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u) toAmbient
      G.emb

namespace SmoothLocalChart

variable {k : Type} [Field k] [CharZero k] {Y V : Sch}
  {pY} {pV}
  {G : EmbeddingDatum k Y pY} {H : EmbeddingDatum k V pV} {u : V ⟶ Y} {y : ↥V}

abbrev chartDomain (C : SmoothLocalChart G H u y) : V.Opens :=
  H.emb ⁻¹ᵁ H.ambient.basicOpen C.func

instance instIsAffineAmbient (C : SmoothLocalChart G H u y) :
    IsAffine C.ambient := C.isAffine_ambient

instance instSmoothAmbientStruct (C : SmoothLocalChart G H u y) :
    Smooth C.ambientStruct := C.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (C : SmoothLocalChart G H u y) :
    LocallyOfFiniteType C.ambientStruct :=
  C.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (C : SmoothLocalChart G H u y) :
    QuasiCompact C.ambientStruct := C.quasiCompact_ambientStruct

instance instSmoothToAmbient (C : SmoothLocalChart G H u y) :
    Smooth C.toAmbient := C.smooth_toAmbient


theorem isAffineOpen_chartDomain [IsAffine V]
    (C : SmoothLocalChart G H u y) :
    IsAffineOpen C.chartDomain := by
  show IsAffineOpen $ H.emb ⁻¹ᵁ H.ambient.basicOpen C.func
  rw [preimage_basicOpen H.emb C.func]
  exact (isAffineOpen_top V).basicOpen _

theorem isPullback_morphismRestrict_basicOpen (C : SmoothLocalChart G H u y) :
    CategoryTheory.IsPullback
      (morphismRestrict H.emb (H.ambient.basicOpen C.func))
      C.chartDomain.ι (H.ambient.basicOpen C.func).ι H.emb :=
  m226 H.emb $ H.ambient.basicOpen C.func

end SmoothLocalChart

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution


section
variable {X' X : Sch}
section
variable (ph_ : X' ⟶ X)
section
variable {ι : Type} (U : ι → Opn X)
def affineOpensLePreimageCover : Set X'.Opens :=
  {W : Opn X' | IsAffineOpen W ∧ ∃ i, W ≤ pre ph_ (U i)}

end

section
variable {ι ka_ : Type} (U : ι → Opn X) (V : ka_ → Opn X') (be_ : ka_ → ι) (hbe_ : ∀ a, V a ≤ ph_ ⁻¹ᵁ (U (be_ a)))
noncomputable def opensCoprodMapOfRefinement :
    sigmaOpens X' V ⟶ sigmaOpens X U :=
  Sigma.desc fun a =>
    ph_.resLE (U (be_ a)) (V a) (hbe_ a) ≫ Sigma.ι (fun i => (U i).toScheme) (be_ a)

@[simp]
theorem sigmaio_opensCoprodMapOfRefinement (a : ka_) :
    Sigma.ι (fun a => (V a).toScheme) a ≫ opensCoprodMapOfRefinement ph_ U V be_ hbe_ =
      ph_.resLE (U (be_ a)) (V a) (hbe_ a) ≫ Sigma.ι (fun i => (U i).toScheme) (be_ a) := by
  simp [opensCoprodMapOfRefinement]

theorem opensCoprodMapOfRefinement_comp_sigmaOpensDesc :
    opensCoprodMapOfRefinement ph_ U V be_ hbe_ ≫ sigmaOpensDesc X U = sigmaOpensDesc X' V ≫ ph_ := by
  refine Limits.Sigma.hom_ext _ _ fun a => ?_
  rw [← assoc, sigmaio_opensCoprodMapOfRefinement, assoc, sigma_io_sigmaOpensDesc,
    sigma_io_sigmaOpensDesc_assoc]
  simp
end
end

theorem exists_finite_affine_cover_subordinate [CompactSpace X']
    (ph_ : X' ⟶ X) {ι : Type} U (hU : iSup U = ⊤) :
    ∃ (ka_ : Type) (_ : Finite ka_) (V : ka_ → Opn X') (be_ : ka_ → ι),
      (∀ a, IsAffineOpen (V a)) ∧ (∀ a, V a ≤ ph_ ⁻¹ᵁ (U (be_ a))) ∧ iSup V = ⊤ := by
  classical
  let _a0 := affineOpensLePreimageCover ph_ U
  have hSmem : ∀ W : _a0,
      IsAffineOpen (W : Opn X') ∧ ∃ i, (W : Opn X') ≤ preU ph_ (U i) :=
    fun W => mp_ (m22) W.2
  have hcov : ∀ x : X', ∃ W : _a0, x ∈ ((W : Opn X') : Set X') := by
    intro x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ (preU ph_ (U i) : Opn X') := by
      have hx : bsM ph_ x ∈ (⊤ : Opn X) := by simp
      rw [← hU] at hx
      obtain ⟨i, hi⟩ := mp_ mem_iSup hx
      exact ⟨i, hi⟩
    obtain ⟨W, hW, hxW, hWle⟩ :=
      isBasis_iff_nbhd.mp (isBasis_affineOpens X') hi
    exact ⟨⟨W, mpr_ (m22) ⟨hW, i, hWle⟩⟩, hxW⟩
  have hcomp : IsCompact (univ : Set X') := isCompact_univ
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover
      (fun W : _a0 => ((W : Opn X') : Set X'))
      (fun W => (W : Opn X').isOpen) fun x _ => mpr_ mem_iUnion $ hcov x
  refine ⟨{W : _a0 // W ∈ t}, inferInstance, fun a => (a.1 : Opn X'),
    fun a => (hSmem a.1).2.choose, fun a => (hSmem a.1).1,
    fun a => (hSmem a.1).2.choose_spec, ?_⟩
  refine coe_injective ?_
  rw [coe_top]
  refine eq_univ_of_forall fun x => ?_
  have hx := ht $ mem_univ x
  simp only [mem_iUnion, exists_prop] at hx
  obtain ⟨W, hWt, hxW⟩ := hx
  exact mpr_ mem_iSup ⟨⟨W, hWt⟩, hxW⟩
end

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {al_ : Type} [TopologicalSpace al_]

theorem radical_ringHom_ker_eq {R S : Type} [CommRing R] [CommRing S] [_root_.IsReduced S]
    (ph_ : R →+* S) : (RingHom.ker ph_).radical = RingHom.ker ph_ := by
  refine le_antisymm ?_ Ideal.le_radical
  rintro x ⟨n, hn⟩
  rw [mem_ker] at hn ⊢
  refine IsNilpotent.eq_zero ⟨n, ?_⟩
  rwa [← map_pow]

theorem isClosed_sUnion_irreducibleComponents [NoetherianSpace al_]
    {S} (hS : S ⊆ irreducibleComponents al_) :
    IsClosed (⋃₀ S) := by
  have hfin :=
    subset (by apply m169) hS
  rw [sUnion_eq_biUnion]
  refine hfin.isClosed_biUnion ?_
  intro s hs
  apply isClosed_of_mem_irreducibleComponents
  exact hS hs

theorem compl_sUnion_irreducibleComponents_sdiff_subset S :
    (⋃₀ (irreducibleComponents al_ \ S))ᶜ ⊆ ⋃₀ S := by
  intro x hx
  rw [mem_compl_iff] at hx
  have hmem : x ∈ irreducibleComponent x := by apply mem_irreducibleComponent
  have hcomp : irreducibleComponent x ∈ irreducibleComponents al_ := by
    apply irreducibleComponent_mem_irreducibleComponents
  by_cases hC : irreducibleComponent x ∈ S
  exact ⟨irreducibleComponent x, hC, hmem⟩
  exact (hx ⟨irreducibleComponent x, ⟨hcomp, hC⟩, hmem⟩).elim

theorem closure_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace al_]
    {S} (hS : S ⊆ irreducibleComponents al_) :
    closure ((⋃₀ (irreducibleComponents al_ \ S))ᶜ) = ⋃₀ S := by
  apply m15
  exact closure_minimal (compl_sUnion_irreducibleComponents_sdiff_subset S)
    (isClosed_sUnion_irreducibleComponents hS)
  rintro x ⟨C, hCS, hxC⟩
  have hCcomp := hS hCS
  have hCirr := an1 hCcomp
  have hnot : ¬ C ⊆ ⋃₀ (irreducibleComponents al_ \ S) := by
    intro hsub
    have hfin : (irreducibleComponents al_ \ S).Finite :=
      subset (by apply m169)
        sdiff_subset
    obtain ⟨D, hD, hCsubD⟩ := mp_ isIrreducible_iff_sUnion_isClosed hCirr hfin.toFinset
      (fun z hz => isClosed_of_mem_irreducibleComponents z (hfin.mem_toFinset.mp hz).1)
      (by rwa [hfin.coe_toFinset])
    have hD' := hfin.mem_toFinset.mp hD
    have hDsubC := an2 hCcomp hD'.1.1 hCsubD
    exact an2 hD' (by rw [m15 hDsubC hCsubD]; exact hCS)
  obtain ⟨y, hyC, hyZ⟩ := mp_ not_subset hnot
  rw [mem_closure_iff]
  intro o ho hxo
  obtain ⟨z, hz, hzo, hzZ⟩ := an2 hCirr o (⋃₀ (irreducibleComponents al_ \ S))ᶜ ho
    (isClosed_sUnion_irreducibleComponents sdiff_subset).isOpen_compl ⟨x, hxC, hxo⟩ ⟨y, hyC, hyZ⟩
  exact ⟨z, hzo, hzZ⟩

theorem vanishingIdeal_congr {X : Sch} {Z1 Z2 : Closeds ↥X}
    (h : (Z1 : Set ↥X) = (Z2 : Set ↥X)) :
    vanishingIdeal Z1 = vanishingIdeal Z2 := by
  rw [coe_injective h]

section
variable (X : Sch) [NoetherianSpace ↥X] (S : Set (Set ↥X))
def complSUnionOtherComponents : Opn X :=
  ⟨(⋃₀ (irreducibleComponents ↥X \ S))ᶜ,
    ((isClosed_sUnion_irreducibleComponents sdiff_subset).isOpen_compl)⟩

@[simp]
theorem coe_complSUnionOtherComponents :
    (complSUnionOtherComponents X S : Set ↥X) = (⋃₀ (irreducibleComponents ↥X \ S))ᶜ :=
  rfl
end

section
variable {X Y : Sch} (g : X ⟶ Y) [IsReduced X]
theorem radical_scheme_ker_eq :
    (ker g).radical = ker g := by
  refine le_antisymm ?_ $ le_radical _
  show (m149 g).radical ≤
    ofIdeals fun U => m41 $ m4 $ g.app U.1
  refine mpr_ le_ofIdeals_iff ?_
  intro U
  have hle : (g.ker).ideal U ≤ m41 (m4 $ g.app U.1) := by
    unfold ker
    exact ideal_ofIdeals_le _ U
  rw [radical_ideal]
  calc ((m149 g).ideal U).radical
      ≤ (m41 $ m4 $ g.app U.1).radical := radical_mono hle
    _ = m41 (m4 $ g.app U.1) := radical_ringHom_ker_eq _

theorem ker_eq_vanishingIdeal_of_support {Z : Closeds ↥Y}
    (hZ : (support (ker g) : Set ↥Y) = (Z : Set ↥Y)) :
    ker g = vanishingIdeal Z := by
  rw [← vanishingIdeal_congr hZ, vanishingIdeal_support,
    radical_scheme_ker_eq g]
end

theorem comap_vanishingIdeal_sUnion {X X' : Sch} (f : X' ⟶ X)
    [IsReduced X] [IsReduced X']
    [NoetherianSpace ↥X] [NoetherianSpace ↥X'] [Flat f]
    {S} (hS : S ⊆ irreducibleComponents ↥X)
    {Z : Closeds ↥X} (hZ : (Z : Set ↥X) = ⋃₀ S)
    {Z' : Closeds ↥X'} (hZ' : (Z' : Set ↥X') = f.base ⁻¹' (⋃₀ S)) :
    comap (vanishingIdeal Z) f =
      vanishingIdeal Z' := by
  let _c0 := ⋃₀ (irreducibleComponents X \ S)
  let _a0 := complSUnionOtherComponents X S
  have hq1 : QuasiCompact _a0.i :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hq2 : QuasiCompact (f ⁻¹ᵁ complSUnionOtherComponents X S).i :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hclU : closure (_a0 : Set X) = Z := by
    rw [coe_complSUnionOtherComponents, hZ]
    exact closure_compl_sUnion_irreducibleComponents_sdiff hS
  have h1 : _a0.ι.ker = vanishingIdeal Z := by
    apply ker_eq_vanishingIdeal_of_support
    rw [support_ker, ← hclU]
    congr 1
    exact q1 _
  let _a1 := f ⁻¹ᵁ complSUnionOtherComponents X S
  have hclU' :
      closure (_a1 : Set X') = Z' := by
    have hcl : IsClosed (preimage f.base (⋃₀ S)) := by
      rw [← hZ']
      exact Z'.2
    rw [hZ']
    show closure (m142 f.base (_c0ᶜ))
        = m142 f.base (⋃₀ S)
    apply m15
    exact closure_minimal
      (preimage_mono (compl_sUnion_irreducibleComponents_sdiff_subset S)) hcl
    intro x' hx'
    have hx'' := hx'
    obtain ⟨C, hCS, hfx⟩ := hx''
    have hCcomp := hS hCS
    obtain ⟨et_, het_⟩ :=
      m140 hCcomp.1 (isClosed_of_mem_irreducibleComponents C hCcomp)
    have hetU : et_ ∈ _c0ᶜ := by
      rintro ⟨D, ⟨hDcomp, hDS⟩, hetD⟩
      have hCsubD : C ⊆ D := by
        rw [← het_]
        exact (isClosed_of_mem_irreducibleComponents D hDcomp).closure_subset_iff.mpr
          (Set.singleton_subset_iff.mpr hetD)
      have hDsubC := an2 hCcomp hDcomp.1 hCsubD
      exact hDS $ m15 hCsubD hDsubC ▸ hCS
    have hspec : et_ ⤳ f.base x' := by
      rwa [specializes_iff_mem_closure, het_]
    obtain ⟨y', hy'spec, hy'eq⟩ := AlgebraicGeometry.Flat.generalizingMap f hspec
    have hy'mem : bsM f y' ∈ (_c0ᶜ) := by simp_all
    have hy'mem2 : y' ∈ (preimage f.base (_c0ᶜ)) := hy'mem
    exact closure_mono (Set.singleton_subset_iff.mpr hy'mem2)
      (mp_ specializes_iff_mem_closure hy'spec)
  have h2 : _a1.ι.ker = vanishingIdeal Z' := by
    apply ker_eq_vanishingIdeal_of_support
    rw [support_ker, ← hclU']
    congr 1
    exact q1 _
  have hpb := isPullback_morphismRestrict f _a0
  have h4 := ker_eq_comap_ker_of_isPullback_of_flat hpb
  rw [← h1, ← h2, h4]

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

variable {X : Sch} {k : Type} [Field k] {p : X ⟶ Sp k}
  {U : Opn X} {m : ℕ}

section
variable (hU : IsAffineOpen U) (c : EtaleChart p U m)
include hU
section
variable (x) (hx : x ∈ U)
include hx
theorem coord_injective : Injective c.coord := by
  let inst := c.algebra
  let _a1 := MvPolynomial (UFin m) k
  have := c.algebra_etale hU
  have : Nontrivial U.sec := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    have := hs
    let _a0 := hU.primeIdealOf ⟨x, hx⟩
    have h1 : 1 ∈ _a0.asIdeal := by
      rw [m111 1 0]
      exact m216 _
    exact _a0.isPrime.ne_top $ mpr_ (eq_top_iff_one _) h1
  have : Module.Flat _a1 U.sec := inferInstance
  have := Module.Flat.isTorsionFree (R := _a1) (M := X.sec U)
  have hinj0 : Injective
      (algebraMap _a1 U.sec) :=
    FaithfulSMul.algebraMap_injective _ _
  have hinj : Injective c.coordRingHom := hinj0
  intro a b hab
  have h1 : (m7 (up a) : _a1)
      = m7 (up b) := by
    apply hinj
    rw [coordRingHom_X, coordRingHom_X, hab]
  have h2 := X_injective h1
  exact congrArg down h2

theorem card_le_ringKrullDim_stalk (J : FinSet m)
    (hJ : ∀ j ∈ J, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    (J.card : WithBot ENat) ≤ ringKrullDim (X.presheaf.stalk x) := by
  classical
  obtain ⟨d, f, -, hf2, -, hd⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J
      (fun j hj => mpr_ (germ_mem_maximalIdeal_iff hU x hx $ c.coord j) $ hJ j hj)
  rw [← hd]
  rcases eq_empty_or_nonempty J with rfl | hJne
  simp only [card_empty]
  exact_mod_cast m67 d
  obtain ⟨j0_, hj0_⟩ := hJne
  obtain ⟨i0_, -⟩ := hf2 j0_ hj0_
  have hch : ∀ j, ∃ i, j ∈ J → f i = c.coord j := by
    intro j
    by_cases hj : j ∈ J
    obtain ⟨i, hi⟩ := hf2 j hj
    exact ⟨i, fun _ => hi⟩
    exact ⟨i0_, fun h => absurd h hj⟩
  choose g hg using hch
  have hmap : ∀ a ∈ J, g a ∈ Finset.univ := fun a _ => Finset.mem_univ _
  have hinjOn : InjOn g (J : Set $ Fin m) := by
    intro a ha b hb hab
    refine coord_injective hU c x hx ?_
    rw [← hg a $ mp_ mem_coe ha, ← hg b $ mp_ mem_coe hb, hab]
  have hcard :=
    card_le_card_of_injOn g hmap hinjOn
  rw [card_univ, card_fin] at hcard
  exact_mod_cast hcard
end

theorem coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton
    j (D : ISD X) (hD : restrictIdeal D U = c.coordIdeal {j})
    x (hx : x ∈ U) (hxD : x ∈ support D) :
    c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 :=
    ideal_eq_span_coord c hU D {j} hD
  have h2 : D.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    let I := D
    have h1 := mp_ (mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hx) hxD
    rw [mem_zeroLocus_iff] at h1
    intro f hf
    rw [← germ_mem_maximalIdeal_iff hU x hx f, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact h1 f hf $ mpr_ (X.mem_basicOpen f x hx) hu
  refine h2 ?_
  rw [h1]
  exact subset_span ⟨j, by simp, rfl⟩
end

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite


namespace FunctorialResolution.EmbeddedResolution

section
variable (k : Type) [Field k] (m : ℕ)
theorem coordSubspaceIdeal_empty :
    coordSubspaceIdeal k m (∅ : FinSet m) = ⊥ := by
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  simp [coe_empty, image_empty, span_empty]
  ext U
  simp [Ideal.map_bot]

theorem coordSubspaceIdeal_singleton j :
    coordSubspaceIdeal k m {j} =
      ofIdealTop
        (span {AffineSpace.coord (Sp k) (up j)}) := by
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, coe_singleton, image_singleton]

section
variable (S : FinSet m) (s : Fin m)
def coordBlowupSubstMap :
    affineSpaceFin k m ⟶ affineSpaceFin k m :=
  AffineSpace.homOfVector (affineSpaceFinToSpec k m)
    (fun i : UFin m =>
      if i.down ∈ S ∧ i.down ≠ s then
        AffineSpace.coord (Sp k) i *
          AffineSpace.coord (Sp k) (up s)
      else AffineSpace.coord (Sp k) i)

@[simp]
theorem coordBlowupSubstMap_comp_affineSpaceFinToSpec :
    coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m = affineSpaceFinToSpec k m := by
  apply m179

@[simp]
theorem coordBlowupSubstMap_appTop_coord
    (i : UFin m) :
    (coordBlowupSubstMap k m S s).appTop.hom (AffineSpace.coord (Sp k) i) =
      if i.down ∈ S ∧ i.down ≠ s then
        AffineSpace.coord (Sp k) i *
          AffineSpace.coord (Sp k) (up s)
      else AffineSpace.coord (Sp k) i := by
  exact m87 ..

theorem coordBlowupSubstMap_appTop_coord_of_mem j (hj : j ∈ S) (hjs : j ≠ s) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Sp k) (up j)) =
      AffineSpace.coord (Sp k) (up j) *
        AffineSpace.coord (Sp k) (up s) :=by simp_all
theorem coordBlowupSubstMap_appTop_coord_self :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Sp k) (up s)) =
      AffineSpace.coord (Sp k) (up s) :=by simp_all
theorem coordBlowupSubstMap_appTop_coord_of_notMem j (hj : j ∉ S) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Sp k) (up j)) =
      AffineSpace.coord (Sp k) (up j) := by
  rw [coordBlowupSubstMap_appTop_coord k m S s $ up j, if_neg fun h => hj h.1]

theorem comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self :
    comap (coordSubspaceIdeal k m {s}) (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {s} := by
  rw [coordSubspaceIdeal_singleton, comap_ofIdealTop,
    map_span, image_singleton, coordBlowupSubstMap_appTop_coord_self k m S s]

end
end

section
variable {X X1 : Sch} {k : Type} [Field k] {p} {p1_} {U : Opn X} {V : Opn X1} {m} {S} {s} (c : EtaleChart p U m) (c1_ : EtaleChart p1_ V m) (g) (hg : c1_.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map)
include hg
theorem comap_coordIdeal_of_coordBlowupSubstMap T :
    comap (c.coordIdeal T) g =
      comap (comap (coordSubspaceIdeal k m T) (coordBlowupSubstMap k m S s)) c1_.map := by
  rw [coordIdeal_eq_comap_coordSubspaceIdeal, ← comap_comp, ← hg,
    comap_comp]

theorem comap_coordIdeal_singleton_of_mem
    j (hj : j ∈ S) (hjs : j ≠ s) :
    comap (c.coordIdeal {j}) g = c1_.coordIdeal {j} * c1_.coordIdeal {s} := by
  have _i23 : comap (coordSubspaceIdeal k m {j}) (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {j} * coordSubspaceIdeal k m {s} := by
    rw [coordSubspaceIdeal_singleton, coordSubspaceIdeal_singleton,
      comap_ofIdealTop,
      ← ofIdealTop_mul, map_span, image_singleton,
      coordBlowupSubstMap_appTop_coord_of_mem k m S s j hj hjs,
      span_singleton_mul_span_singleton]
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c1_ g hg {j},
    _i23,
    comap_mul]
  rfl

theorem comap_coordIdeal_singleton_self :
    comap (c.coordIdeal {s}) g = c1_.coordIdeal {s} := by
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c1_ g hg {s},
    comap_coordBlowupSubstMap_coordSubspaceIdeal_singleton_self k m S s]
  rfl

theorem comap_coordIdeal_singleton_of_notMem
    j (hj : j ∉ S) :
    comap (c.coordIdeal {j}) g = c1_.coordIdeal {j} := by
  have _i25 : comap (coordSubspaceIdeal k m {j}) (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {j} := by
    rw [coordSubspaceIdeal_singleton, comap_ofIdealTop,
      map_span, image_singleton, coordBlowupSubstMap_appTop_coord_of_notMem k m S s j hj]
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c1_ g hg {j},
    _i25]
  rfl

theorem comap_coordIdeal_center (hs : s ∈ S) :
    comap (c.coordIdeal S) g = c1_.coordIdeal {s} := by
  let _a2 := coordBlowupSubstMap k m S s
  have _i26 : comap (coordSubspaceIdeal k m S) _a2 = coordSubspaceIdeal k m {s} := by
    let _c0 := Sp k
    let _a0 := _a2
    let _a1 := AffineSpace.coord _c0 $ up s
    have key : Ideal.map (_a0.appTop.hom)
        (span
          ((fun i => AffineSpace.coord _c0 $ up i) ''
            (S : Set $ Fin m))) =
        span {_a1} := by
      rw [map_span]
      apply le_antisymm
      rw [span_le]
      rintro y ⟨z, ⟨i, hi, rfl⟩, rfl⟩
      have hiS := mp_ mem_coe hi
      show _a0.appTop.hom
          (AffineSpace.coord _c0 $ up i) ∈
          span {_a1}
      by_cases h : i = s
      have h2 : _a0.appTop.hom
          (AffineSpace.coord _c0 $ up i) =
          _a1 := by
        rw [h]
        exact coordBlowupSubstMap_appTop_coord_self k m S s
      rw [h2]
      exact mem_span_singleton_self _
      rw [coordBlowupSubstMap_appTop_coord_of_mem k m S s i hiS h]
      exact mul_mem_left _ _ $ mem_span_singleton_self _
      rw [span_le, singleton_subset_iff]
      have hmem : _a0.appTop.hom
          _a1 ∈
          (_a0.appTop.hom ''
            ((fun i => AffineSpace.coord _c0 $ up i) ''
              (S : Set $ Fin m))) :=
        mem_image_of_mem _ $ mem_image_of_mem _ $ mpr_ mem_coe hs
      rw [coordBlowupSubstMap_appTop_coord_self k m S s] at hmem
      exact subset_span hmem
    rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, comap_ofIdealTop, key,
      coordSubspaceIdeal_singleton]
  rw [comap_coordIdeal_of_coordBlowupSubstMap c c1_ g hg S,
    _i26]
  rfl
end





def natSuccAbove (j i : ℕ) : ℕ := if i < j then i else i + 1

theorem getElem_eraseIdx_natSuccAbove {al_ : Type} (l : List al_) j i
    (hi : i < length (eraseIdx l j)) (hs : natSuccAbove j i < length l) :
    (eraseIdx l j)[i]'hi = l[natSuccAbove j i]'hs := by
  unfold natSuccAbove at hs ⊢
  rw [getElem_eraseIdx]
  split <;> simp [*]

section
variable (m) (S : FinSet m) (s : Fin m)
def complOrderEmbPreimage : Option (Fin (m - S.card)) :=
  if hs : s ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S hs))

end

section
variable {m} (S : FinSet m) (j : ℕ) (a : ℕ → Option (Fin m)) (i : ℕ)
def transportSuccAboveToCompl : Option (Fin (m - S.card)) :=
  (a (natSuccAbove j i)).bind (complOrderEmbPreimage m S)

theorem transportSuccAboveToCompl_eq_some u
    (h : transportSuccAboveToCompl S j a i = some u) : a (natSuccAbove j i) = some (complOrderEmb m S u) := by
  rcases hs : a (natSuccAbove j i) with _ | s
  exfalso
  unfold transportSuccAboveToCompl at h
  rw [hs] at h
  simp at h
  have h' : complOrderEmbPreimage m S s = some u := by
    unfold transportSuccAboveToCompl at h
    rwa [hs] at h
  have _i28 : complOrderEmb m S u = s := by
    by_cases hs : s ∈ S
    exfalso
    unfold complOrderEmbPreimage at h'
    rw [dif_pos hs] at h'
    simp at h'
    unfold complOrderEmbPreimage at h'
    rw [dif_neg hs] at h'
    rw [← inj h']
    exact choose_spec $ exists_complOrderEmb_eq m S hs
  rw [_i28]

theorem transportSuccAboveToCompl_eq_none (h : transportSuccAboveToCompl S j a i = none) :
    a (natSuccAbove j i) = none ∨ ∃ s, a (natSuccAbove j i) = some s ∧ s ∈ S := by
  rcases hs : a (natSuccAbove j i) with _ | s
  exact m51 rfl
  refine m61 ⟨s, rfl, ?_⟩
  have h' : complOrderEmbPreimage m S s = none := by
    unfold transportSuccAboveToCompl at h
    rwa [hs] at h
  let h := h'
  by_contra hs
  unfold complOrderEmbPreimage at h
  rw [dif_neg hs] at h
  simp at h
end

section
variable {X : Sch} {k : Type} [Field k] (p : X ⟶ Sp k) (E : Bdy X) (hE : InStrictNormalCrossingPosition p E) (j : ℕ) (hj : j < length E)
include hE hj
theorem exists_etaleChart_comap_subschemeio_eraseIdx (z : ↥((E[j]'hj).subscheme)) :
    ∃ (U : ((E[j]'hj).subscheme).Opens) (_ : z ∈ U) (m : ℕ)
      (c : EtaleChart ((E[j]'hj).si ≫ p) U m) (a : ℕ → Option (Fin m)),
      (∀ i < ((eraseIdx E j).map fun D => D.comap (E[j]'hj).si).length,
        ∀ i' < ((eraseIdx E j).map fun D => D.comap (E[j]'hj).si).length,
        ∀ t, a i = some t → a i' = some t → i = i') ∧
      (∀ i (hi : i < ((eraseIdx E j).map fun D => D.comap (E[j]'hj).si).length),
        a i = none →
          restrictIdeal (((eraseIdx E j).map fun D => D.comap (E[j]'hj).si)[i]) U = ⊤) ∧
      (∀ i (hi : i < ((eraseIdx E j).map fun D => D.comap (E[j]'hj).si).length)
        (t : Fin m), a i = some t →
          restrictIdeal (((eraseIdx E j).map fun D => D.comap (E[j]'hj).si)[i]) U =
            c.coordIdeal {t}) := by
  classical
  obtain ⟨-, hpos⟩ := mp_ (inStrictNormalCrossingPosition_iff p E) hE
  let _a0 := (E[j]'hj).subschemeι.base z
  have hx : _a0 ∈ spI (E[j]'hj) := by
    have hmem : _a0 ∈ range (E[j]'hj).subschemeι.base :=
      mem_range_self z
    simpa using hmem
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := (hpos _a0).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU
  have hV := hVB
  rcases haj : a j with _ | t
  refine absurd hx ?_
  refine notMem_support_of_comap_ι_eq_top _ ?_ hxU
  rw [← restrictIdeal_eq_comap_io]
  exact h2 j hj haj
  have hzmem := hxV
  have h2V :=
    fun i hi hn => restrictIdeal_eq_top_of_le _ hVU $ h2 i hi hn
  have h3V :=
    fun i hi s hsm => restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {s} (h3 i hi s hsm)
  have hZV := h3V j hj t haj
  have hlen : ∀ i, i < ((eraseIdx E j).map fun D => cmI D (E[j]'hj).si).length →
      natSuccAbove j i < E.length := by
    intro i hi
    rw [length_map] at hi
    have h0 := length_eraseIdx_add_one hj
    unfold natSuccAbove
    split_ifs with hc <;> omega
  have helem : ∀ (i : ℕ)
      (hi : i < ((eraseIdx E j).map fun D => D.comap (E[j]'hj).si).length),
      ((eraseIdx E j).map fun D => D.comap (E[j]'hj).si)[i]'hi =
        (E[natSuccAbove j i]'(hlen i hi)).comap (E[j]'hj).si := by
    intro i hi
    have hi' : i < (eraseIdx E j).length := by simp_all
    rw [getElem_map]
    exact congrArg (fun D => D.comap (E[j]'hj).si) (getElem_eraseIdx_natSuccAbove E j i hi' (hlen i hi))
  refine ⟨(E[j]'hj).si.pre V, hzmem, m - ({t} : FinSet m).card,
    (c.restrict hVU).restrictToSubscheme hV (E[j]'hj) {t} hZV,
    transportSuccAboveToCompl {t} j a, ?_, ?_, ?_⟩
  intro i hi i' hi' u hu hu'
  let h := h1 (natSuccAbove j i) (hlen i hi) (natSuccAbove j i') (hlen i' hi')
      (complOrderEmb m {t} u) (transportSuccAboveToCompl_eq_some {t} j a i u hu)
      (transportSuccAboveToCompl_eq_some {t} j a i' u hu')
  unfold natSuccAbove at h
  split_ifs at h <;> omega
  intro i hi hn
  rw [helem i hi]
  rcases transportSuccAboveToCompl_eq_none {t} j a i hn with hnone | ⟨s, hsome, hsmem⟩
  exact restrictIdeal_comap_subschemeio_eq_top (E[j]'hj) V _
    (h2V (natSuccAbove j i) (hlen i hi) hnone)
  exfalso
  have h0 : a (natSuccAbove j i) = some t := by simp_all
  have _i27 : natSuccAbove j i ≠ j := by
    unfold natSuccAbove
    split_ifs with h <;> omega
  exact _i27 $ h1 (natSuccAbove j i) (hlen i hi) j hj t h0 haj
  intro i hi u hu
  rw [helem i hi]
  exact (c.restrict hVU).restrictToSubscheme_coordIdeal_singleton hV (E[j]'hj) {t} hZV u
    (E[natSuccAbove j i]'(hlen i hi))
    (h3V (natSuccAbove j i) (hlen i hi) (complOrderEmb m {t} u)
      (transportSuccAboveToCompl_eq_some {t} j a i u hu))

theorem inStrictNormalCrossingPosition_comap_subschemeio_eraseIdx :
    InStrictNormalCrossingPosition (subschemeι (E[j]'hj) ≫ p)
      ((eraseIdx E j).map fun D => comap D (E[j]'hj).si) :=
  by
    let h := exists_etaleChart_comap_subschemeio_eraseIdx p E hE j hj
    refine mpr_ (inStrictNormalCrossingPosition_iff (siI (E[j]'hj) ≫ p) $ (eraseIdx E j).map fun D => cmI D (E[j]'hj).si) ⟨?_, fun x => inStrictNormalCrossingPositionAt_of_exists_etaleChart $ h x⟩
    intro D hD
    obtain ⟨i, hi, rfl⟩ := mp_ mem_iff_getElem hD
    refine isSmoothDivisor_of_locally_coordIdeal _ ?_
    intro x
    obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := h x
    refine ⟨U, hxU, m, c, ?_⟩
    rcases hai : a i with _ | t
    exact m51 $ h2 i hi hai
    exact m61 ⟨t, h3 i hi t hai⟩

end

end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

section
variable {k : Type} [Field k] {X X' : Sch} (p : X' ⟶ Sp k)
theorem krullDimSucc_lt_of_isClosedImmersion_of_nonzeroOnComponents
    [LocallyOfFiniteType p] [QuasiCompact p]
    (ta_ : X ⟶ X') [IsClosedImmersion ta_] [Nonempty ↥X]
    (hker : NonzeroOnComponents ta_.ker) :
    krullDimSucc X < krullDimSucc X' := by
  have hemb :=
    isClosedEmbedding ta_
  obtain ⟨z⟩ := ‹Nonempty X›
  refine krullDimSucc_lt_of_homeomorph_isClosed X' X (range ta_.base) hemb.isClosed_range
    ⟨bsM ta_ z, z, rfl⟩ ?_ (topologicalKrullDim_lt_top_of_finiteType p ‹LocallyOfFiniteType p› ‹QuasiCompact p›) hemb.toIsEmbedding.toHomeomorph
  intro C hC hsub
  exact hker C hC $ hsub.trans ta_.range_subset_ker_support
end

theorem ker_le_map_idealSheaf {X X' : Sch} (f : X ⟶ X') (I : ISD X) :
    f.ker ≤ I.map f := by
  have hle : (⊥ : ISD X).map f ≤ I.map f :=
    map_mono f bot_le
  rwa [map_bot] at hle

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

abbrev VanishingAssignment := ∀ X : Sch, Closeds ↥X → IdealSheafData X

structure IrreducibleClosedPair (W : Sch) where
  S1 : Set ↥W
  S2 : Set ↥W
  xi1 : ↥W
  xi2 : ↥W
  pt : ↥W
  closed1 : IsClosed S1
  closed2 : IsClosed S2
  generic1 : IsGenericPoint xi1 S1
  generic2 : IsGenericPoint xi2 S2
  mem_first_closed : pt ∈ S1
  mem_second_closed : pt ∈ S2

section
variable {W : Sch}
section
variable (I J : ISD W) (x : ↥W)
def AgreeNear : Prop :=
  ∃ U : Opn W, x ∈ U ∧ comap I U.i = comap J U.i

theorem agreeNear_iff :
    AgreeNear I J x ↔ ∃ U : Opn W, x ∈ U ∧ comap I U.i = comap J U.i := m22
end

theorem agreeNear_symm {I J : ISD W} {x : ↥W}
    (h : AgreeNear I J x) : AgreeNear J I x := by
  obtain ⟨U, hU, hEq⟩ := h
  exact ⟨U, hU, sy_ hEq⟩
end

structure IdealSheafGeometryHypotheses (V : VanishingAssignment) : Prop where
  agreeNear_comap : ∀ (W : Sch) (U : Opn W) (I J : ISD W)
      (y : ↥(U.toScheme)), AgreeNear I J (U.ib y) →
      AgreeNear (I.comap U.i) (J.comap U.i) y
  agreeNear_trans : ∀ (W : Sch) (I J K : ISD W) (x : ↥W),
      AgreeNear I J x → AgreeNear J K x → AgreeNear I K x
  comap_mul : ∀ (W X : Sch) (f : X ⟶ W) (I J : ISD W),
      (I * J).comap f = I.comap f * J.comap f
  base_comp : ∀ (X Y Z : Sch) (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X),
      (f ≫ g).base x = g.base (f.base x)
  isClosed_support : ∀ (W : Sch) (I : ISD W),
      IsClosed (I.support : Set ↥W)
  isClosedEmbedding_subschemeι : ∀ (W : Sch) (I : ISD W),
      Topology.IsClosedEmbedding ⇑I.subschemeι.base
  isEmbedding_ι : ∀ (W : Sch) (U : Opn W), Topology.IsEmbedding ⇑U.ib
  isOpen_opens : ∀ (W : Sch) (U : Opn W), IsOpen (U : Set ↥W)
  orderAt_comap : ∀ (W : Sch) (U : Opn W) (I : ISD W)
      (y : ↥(U.toScheme)), orderAt (I.comap U.i) y = orderAt I (U.ib y)
  orderAt_congr : ∀ (W : Sch) (I J : ISD W) (x : ↥W),
      AgreeNear I J x → orderAt I x = orderAt J x
  orderAt_vanishing_eq_one : ∀ (k : Type) [Field k] (W : Sch)
      (p : W ⟶ Sp k) (U : Opn W) (D : IdealSheafData (U.toScheme)),
      IsSmoothDivisor (U.i ≫ p) D →
      ∀ (T : Closeds ↥(D.subscheme)) (y : ↥(D.subscheme)),
        IsGenericPoint y (T : CSet (D.subscheme)) →
        (T : CSet (D.subscheme)) ∉ irreducibleComponents ↥(D.subscheme) →
        orderAt (V D.subscheme T) y = 1
  range_ι : ∀ (W : Sch) (U : Opn W), range ⇑U.ib = (U : Set ↥W)
  range_subschemeι : ∀ (W : Sch) (I : ISD W),
      range ⇑I.subschemeι.base = (I.support : Set ↥W)
  support_mul : ∀ (W : Sch) (I J : ISD W),
      ((I * J).support : Set ↥W) = (I.support : Set ↥W) ∪ (J.support : Set ↥W)
  not_subset_support_of_nonzeroOnComponents : ∀ (W : Sch) (I : ISD W),
      NonzeroOnComponents I →
      ∀ T ∈ irreducibleComponents ↥W, ¬ T ⊆ (I.support : Set ↥W)
  support_vanishing : ∀ (W : Sch) (T : Closeds ↥W),
      ((V W T).support : Set ↥W) = (T : Set ↥W)
  top_mul : ∀ (W : Sch) (I : ISD W), (⊤ : ISD W) * I = I
  agreeNear_vanishing_restrict : ∀ (W : Sch) (I : ISD W) (U : Opn W)
      (D : IdealSheafData (U.toScheme)) (T : Closeds ↥W) (T' : Closeds ↥(D.subscheme))
      (y : ↥(D.subscheme)),
      (T' : CSet (D.subscheme)) = (D.si ≫ U.i).base ⁻¹' (T : Set ↥W) →
      (U.ib ⁻¹' (T : Set ↥W)) ⊆ (D.support : Set ↥(U.toScheme)) →
      AgreeNear I (V W T) ((D.si ≫ U.i).base y) →
      AgreeNear ((I.comap U.i).comap D.si) (V D.subscheme T') y
  comap_vanishing : ∀ (W : Sch) (T : Closeds ↥W) (U : Opn W)
      (T' : Closeds ↥(U.toScheme)),
      (T' : Set ↥(U.toScheme)) = U.ib ⁻¹' (T : Set ↥W) →
      (V W T).comap U.i = V U.toScheme T'

section
variable {V} (hV : IdealSheafGeometryHypotheses V)
include hV
theorem mem_support_iff_of_agreeNear
    {W : Sch} {I J : ISD W} {x} (h : AgreeNear I J x) :
    x ∈ (I.support : Set ↥W) ↔ x ∈ (J.support : Set ↥W) := by
  let _a0 := one_le_orderAt_iff_mem_support I x
  let _a1 := one_le_orderAt_iff_mem_support J x
  have h1 := hV.orderAt_congr W I J x h
  constructor
  intro hx
  have hx' := _a0.2 hx
  refine _a1.1 ?_
  rwa [← h1]
  intro hx
  have hx' := _a1.2 hx
  refine _a0.1 ?_
  rwa [h1]

section
variable (W : Sch)
section
variable (U : Opn W) (D : IdealSheafData (U.toScheme))
theorem exists_subschemeio_comp_io_apply_eq_of_mem T
    (hT : U.ib ⁻¹' T ⊆ (D.support : Set ↥(U.toScheme)))
    x (hxU : x ∈ (U : Set ↥W)) (hxT : x ∈ T) :
    ∃ y : ↥(D.subscheme), (D.si ≫ U.i).base y = x := by
  have hx := hxU
  rw [← hV.range_ι W U] at hx
  obtain ⟨y0_, hy0_⟩ := hx
  have hy0T : y0_ ∈ suppI D := by
    refine hT ?_
    have h' := hxT
    rwa [← hy0_] at h'
  have hy0r : y0_ ∈ range D.subschemeι.base := by
    rwa [hV.range_subschemeι U.toScheme D]
  obtain ⟨y, hy⟩ := hy0r
  refine ⟨y, ?_⟩
  rw [hV.base_comp _ _ _ D.si U.i y, hy, hy0_]

theorem isInducing_subschemeio_comp_io :
    Topology.IsInducing ⇑(D.si ≫ U.i).base := by
  have h2 := (hV.isEmbedding_ι W U).toIsInducing
  have hfun : (siI D ≫ opI U).base = U.ib ∘ D.subschemeι.base := by simp_all
  rw [hfun]
  exact h2.comp $ (hV.isClosedEmbedding_subschemeι U.toScheme D).toIsEmbedding.toIsInducing

theorem isGenericPoint_preimage_subschemeio_comp_io T
    xi_ (hxi_ : IsGenericPoint xi_ T) y
    (hy : (D.si ≫ U.i).base y = xi_) :
    IsGenericPoint y ((D.si ≫ U.i).base ⁻¹' T) :=
  isGenericPoint_preimage_of_isInducing (isInducing_subschemeio_comp_io hV W U D) hxi_ hy

theorem isClosed_preimage_subschemeio_comp_io T
    (hT : IsClosed T) :
    IsClosed ((D.si ≫ U.i).base ⁻¹' T) :=
  hT.preimage (isInducing_subschemeio_comp_io hV W U D).continuous
end

theorem false_of_isOpen_preimage_support (N Z : ISD W) (C : IrreducibleClosedPair W) (U : Opn W)
    (H : IdealSheafData (U.toScheme))
    (hptU : C.pt ∈ (U : Set ↥W)) (hptZ : C.pt ∈ (Z.support : Set ↥W))
    (hZH : ((Z.comap U.i).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hNsubH : ((N.comap U.i).support : Set ↥(U.toScheme)) ⊆ (H.support : Set ↥(U.toScheme)))
    (hopen : IsOpen (H.subschemeι.base ⁻¹' ((Z.comap U.i).support : Set ↥(U.toScheme))))
    (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi2N : C.xi2 ∈ (N.support : Set ↥W)) : False := by
  let _a1 := spI Z
  have hopenU := hV.isOpen_opens W U
  have hZsub := hZH
  rw [support_comap_eq] at hZsub
  have hNsub := hNsubH
  rw [support_comap_eq] at hNsub
  obtain ⟨y0, hy0⟩ := exists_subschemeio_comp_io_apply_eq_of_mem hV W U H Z.support hZsub C.pt hptU hptZ
  obtain ⟨y2, hy2⟩ := exists_subschemeio_comp_io_apply_eq_of_mem hV W U H N.support hNsub C.xi2 ((C.generic2.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_second_closed, hptU⟩) hxi2N
  have hgen2 :=
    isGenericPoint_preimage_subschemeio_comp_io hV W U H C.S2 C.xi2 C.generic2 y2 hy2
  let _a0 := siI H ≫ opI U
  have hirr : IsIrreducible $ preimage _a0.base C.S2 := by
    rw [← hgen2.def]
    exact isIrreducible_singleton.closure
  have hy0A : y0 ∈ H.subschemeι.base ⁻¹' (spI (cmI Z U.i) : Set $ oSch U) := by
    rw [support_comap_eq]
    show opIb U (H.subschemeι.base y0) ∈ _a1
    rwa [← hV.base_comp _ _ _ H.si U.i y0, hy0]
  have hy0S := by
    show bsM _a0 y0 ∈ C.S2
    rw [hy0]
    exact C.mem_second_closed
  have hsub := hirr.isPreirreducible.isPreconnected.subset_isClopen ⟨(hV.isClosed_support U.toScheme $ cmI Z U.i).preimage (hV.isClosedEmbedding_subschemeι U.toScheme H).continuous, hopen⟩ ⟨y0, hy0S, hy0A⟩
  have hy2A :=
    hsub hgen2.mem
  apply hxi2Z
  rw [support_comap_eq] at hy2A
  have h' : opIb U (H.subschemeι.base y2) ∈ _a1 := hy2A
  rwa [← hV.base_comp _ _ _ H.si U.i y2, hy2] at h'
end
end

def OrderOneCentersIsolated (V : VanishingAssignment) {k : Type} [Field k] (W : Sch)
    (_p : W ⟶ Sp k) (I : ISD W) (m : ℕ) (Mem : Set ↥W)
    (Z : ISD W) : Prop :=
  ∀ C : IrreducibleClosedPair W, m = 1 → C.S1 ⊆ (support Z : Set ↥W) →
    C.xi2 ∉ (support Z : Set ↥W) → C.xi1 ∉ Mem → C.xi2 ∉ Mem →
    AgreeNear I (V W ⟨C.S1, C.closed1⟩) C.xi1 → orderAt I C.xi1 = 1 →
    C.xi2 ∈ (I.support : Set ↥W) → False

section
variable {V : VanishingAssignment}

section
variable (hV : IdealSheafGeometryHypotheses V) {k : Type} [Field k] {W : Sch} {p : W ⟶ Sp k}
include hV
section
variable {N : ISD W} {mu_ : ℕ} {Mem : Set ↥W} {Z : ISD W}
theorem false_of_isSmoothDivisor_of_orderOneCentersIsolated
    (C : IrreducibleClosedPair W) (U0_ : Opn W) (H0_ : IdealSheafData (U0_.toScheme))
    (Jz : IdealSheafData (H0_.subscheme))
    (hptU : C.pt ∈ (U0_ : Set ↥W))
    (hH : IsSmoothDivisor (U0_.i ≫ p) H0_)
    (hNsubH : ((N.comap U0_.i).support : Set ↥(U0_.toScheme)) ⊆
      (H0_.support : Set ↥(U0_.toScheme)))
    (hZH : ((Z.comap U0_.i).support : Set ↥(U0_.toScheme)) ⊆
      (H0_.support : Set ↥(U0_.toScheme)))
    (hcomp : NonzeroOnComponents Jz)
    (hloc : ∀ x : ↥(H0_.subscheme), (H0_.si ≫ U0_.i).base x ∉ Mem →
      ∃ V' : (H0_.subscheme).Opens, x ∈ V' ∧
        Jz.comap V'.i = ((N.comap U0_.i).comap H0_.si).comap V'.i)
    (key : OrderOneCentersIsolated V H0_.subscheme (H0_.si ≫ (U0_.i ≫ p)) Jz mu_
      (⇑(H0_.si ≫ U0_.i).base ⁻¹' Mem) ((Z.comap U0_.i).comap H0_.si))
    (hm1 : mu_ = 1) (hS1 : C.S1 ⊆ (Z.support : Set ↥W)) (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi1M : C.xi1 ∉ Mem) (hxi2M : C.xi2 ∉ Mem)
    (hagree : AgreeNear N (V W ⟨C.S1, C.closed1⟩) C.xi1) (_hord : orderAt N C.xi1 = 1)
    (hxi2N : C.xi2 ∈ (N.support : Set ↥W)) : False := by
  let _a2 := spI Z
  let _c0 := siI H0_ ≫ opI U0_
  have hptZ := hS1 C.mem_first_closed
  have hopenU := hV.isOpen_opens W U0_
  have hxi1U :=
    (C.generic1.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_first_closed, hptU⟩
  have hxi2U :=
    (C.generic2.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_second_closed, hptU⟩
  have hZsub := hZH
  rw [support_comap_eq] at hZsub
  have hNsub := hNsubH
  rw [support_comap_eq] at hNsub
  obtain ⟨y1, hy1⟩ := exists_subschemeio_comp_io_apply_eq_of_mem hV W U0_ H0_ Z.support hZsub C.xi1 hxi1U
    (hS1 C.generic1.mem)
  obtain ⟨y0, hy0⟩ := exists_subschemeio_comp_io_apply_eq_of_mem hV W U0_ H0_ Z.support hZsub C.pt hptU hptZ
  obtain ⟨y2, hy2⟩ := exists_subschemeio_comp_io_apply_eq_of_mem hV W U0_ H0_ N.support hNsub C.xi2 hxi2U
    hxi2N
  have hgen1 :=
    isGenericPoint_preimage_subschemeio_comp_io hV W U0_ H0_ C.S1 C.xi1 C.generic1 y1 hy1
  have hgen2 :=
    isGenericPoint_preimage_subschemeio_comp_io hV W U0_ H0_ C.S2 C.xi2 C.generic2 y2 hy2
  have hcl1 :=
    isClosed_preimage_subschemeio_comp_io hV W U0_ H0_ C.S1 C.closed1
  have hcl2 :=
    isClosed_preimage_subschemeio_comp_io hV W U0_ H0_ C.S2 C.closed2
  have hA1 := by
    refine hloc y1 ?_
    rwa [hy1]
  let _a0 := V H0_.subscheme ⟨preimage _c0.base C.S1, hcl1⟩
  have hA2 := by
    refine hV.agreeNear_vanishing_restrict W N U0_ H0_ ⟨C.S1, C.closed1⟩
      ⟨pIm _c0.base C.S1, hcl1⟩ y1 rfl (fun a ha => hZsub $ preimage_mono hS1 ha) ?_
    rwa [hy1]
  have hA3 :=
    hV.agreeNear_trans H0_.subscheme Jz (cmI (cmI N U0_.i) H0_.si)
      _a0 y1 hA1 hA2
  have hy1mem := by
    refine (mem_support_iff_of_agreeNear hV hA3).2 ?_
    rw [hV.support_vanishing]
    exact hgen1.mem
  have hnotcomp : (preimage _c0.base C.S1) ∉
      irreducibleComponents (subS H0_) := by
    intro hmem
    refine hV.not_subset_support_of_nonzeroOnComponents H0_.subscheme Jz hcomp _ hmem ?_
    rw [← hgen1.def]
    exact (hV.isClosed_support H0_.subscheme Jz).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hy1mem)
  have hordV :=
    hV.orderAt_vanishing_eq_one k W p U0_ H0_ hH
      ⟨preimage _c0.base C.S1, hcl1⟩ y1 hgen1 hnotcomp
  have hordJ : orderAt Jz y1 = 1 := by
    rw [hV.orderAt_congr H0_.subscheme Jz
      _a0 y1 hA3]
    exact hordV
  have hA2' := by
    refine hloc y2 ?_
    rwa [hy2]
  have hy2mem := by
    refine (mem_support_iff_of_agreeNear hV hA2').2 ?_
    rw [support_comap_eq, support_comap_eq]
    show opIb U0_ (H0_.subschemeι.base y2) ∈ spI N
    rwa [← hV.base_comp _ _ _ H0_.si U0_.i y2, hy2]
  refine key
    { S1 := pIm _c0.base C.S1
      S2 := pIm _c0.base C.S2
      xi1 := y1
      xi2 := y2
      pt := y0
      closed1 := hcl1
      closed2 := hcl2
      generic1 := hgen1
      generic2 := hgen2
      mem_first_closed := by
        show bsM _c0 y0 ∈ C.S1
        rw [hy0]
        exact C.mem_first_closed
      mem_second_closed := by
        show bsM _c0 y0 ∈ C.S2
        rw [hy0]
        exact C.mem_second_closed }
    hm1 ?_ ?_ ?_ ?_ hA3 hordJ hy2mem
  rw [support_comap_eq, support_comap_eq]
  intro a ha
  show opIb U0_ (H0_.subschemeι.base a) ∈ _a2
  rw [← hV.base_comp _ _ _ H0_.si U0_.i a]
  exact hS1 ha
  rw [support_comap_eq, support_comap_eq]
  intro hcon
  apply hxi2Z
  have h' : opIb U0_ (H0_.subschemeι.base y2) ∈ _a2 := hcon
  rwa [← hV.base_comp _ _ _ H0_.si U0_.i y2, hy2] at h'
  simp_all
  simp_all

theorem orderOneCentersIsolated_of_isSmoothDivisor
    (U : ∀ z : ↥W, z ∈ Z.support → Opn W)
    (hU : ∀ z hz, z ∈ U z hz)
    (H : ∀ z hz, IdealSheafData ((U z hz).toScheme))
    (hH : ∀ z hz, IsSmoothDivisor ((U z hz).i ≫ p) (H z hz))
    (hNsubH : ∀ z hz,
      ((N.comap (U z hz).i).support : Set ↥((U z hz).toScheme)) ⊆
        ((H z hz).support : Set ↥((U z hz).toScheme)))
    (hZH : ∀ z hz,
      ((Z.comap (U z hz).i).support : Set ↥((U z hz).toScheme)) ⊆
        ((H z hz).support : Set ↥((U z hz).toScheme)))
    (J : ∀ z hz, Option (((H z hz)).subscheme).IdealSheafData)
    (hJnone : ∀ z hz, J z hz = none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        ((Z.comap (U z hz).i).support : Set ↥((U z hz).toScheme))))
    (hJcomp : ∀ z hz (Jz : IdealSheafData ((H z hz).subscheme)),
      J z hz = some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ z hz (Jz : IdealSheafData ((H z hz).subscheme)),
      J z hz = some Jz → ∀ x : ↥((H z hz).subscheme),
        ((H z hz).si ≫ (U z hz).i).base x ∉ Mem →
        ∃ V' : ((H z hz).subscheme).Opens, x ∈ V' ∧
          Jz.comap V'.i = ((N.comap (U z hz).i).comap (H z hz).si).comap V'.i)
    (ih : ∀ z hz (Jz : IdealSheafData ((H z hz).subscheme)),
      J z hz = some Jz →
      OrderOneCentersIsolated V ((H z hz).subscheme) ((H z hz).si ≫ ((U z hz).i ≫ p)) Jz mu_
        (⇑((H z hz).si ≫ (U z hz).i).base ⁻¹' Mem)
        ((Z.comap (U z hz).i).comap (H z hz).si)) :
    OrderOneCentersIsolated V W p N mu_ Mem Z := by
  intro C hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2N
  have hz := hS1 C.mem_first_closed
  have hptZ := hS1 C.mem_first_closed
  rcases hJJ : J C.pt hz with _ | Jz
  exact false_of_isOpen_preimage_support hV W N Z C (U C.pt hz) (H C.pt hz) (hU C.pt hz) hptZ
    (hZH C.pt hz) (hNsubH C.pt hz) (hJnone C.pt hz hJJ) hxi2Z hxi2N
  exact false_of_isSmoothDivisor_of_orderOneCentersIsolated hV C (U C.pt hz) (H C.pt hz) Jz (hU C.pt hz) (hH C.pt hz)
    (hNsubH C.pt hz) (hZH C.pt hz) (hJcomp C.pt hz Jz hJJ) (hJloc C.pt hz Jz hJJ)
    (ih C.pt hz Jz hJJ) hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2N
end

section
variable {I : ISD W} {m : ℕ} {Mem : Set ↥W} {Z : ISD W}
theorem false_of_orderOneCentersIsolated_comap_opens
    (U0_ : Opn W) (C : IrreducibleClosedPair W) (hptU : C.pt ∈ (U0_ : Set ↥W))
    (key : OrderOneCentersIsolated V U0_.toScheme (U0_.i ≫ p) (I.comap U0_.i) m (⇑U0_.ib ⁻¹' Mem)
      (Z.comap U0_.i))
    (hm1 : m = 1) (hS1 : C.S1 ⊆ (Z.support : Set ↥W)) (hxi2Z : C.xi2 ∉ (Z.support : Set ↥W))
    (hxi1M : C.xi1 ∉ Mem) (hxi2M : C.xi2 ∉ Mem)
    (hagree : AgreeNear I (V W ⟨C.S1, C.closed1⟩) C.xi1) (hord : orderAt I C.xi1 = 1)
    (hxi2I : C.xi2 ∈ (I.support : Set ↥W)) : False := by
  let _a0 := V W ⟨C.S1, C.closed1⟩
  have hopenU := hV.isOpen_opens W U0_
  have hrange := hV.range_ι W U0_
  obtain ⟨x1, hx1⟩ : ∃ y, opIb U0_ y = C.xi1 := by
    rw [← mem_range, hrange]
    exact (C.generic1.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_first_closed, hptU⟩
  obtain ⟨x2, hx2⟩ : ∃ y, opIb U0_ y = C.xi2 := by
    rw [← mem_range, hrange]
    exact (C.generic2.mem_open_set_iff hopenU).mpr ⟨C.pt, C.mem_second_closed, hptU⟩
  obtain ⟨x0, hx0⟩ : ∃ y, opIb U0_ y = C.pt := by
    rwa [← mem_range, hrange]
  let _a1 := hV.isEmbedding_ι W U0_
  have hcont := _a1.continuous
  refine key
    { S1 := preimage U0_.ib C.S1
      S2 := preimage U0_.ib C.S2
      xi1 := x1
      xi2 := x2
      pt := x0
      closed1 := C.closed1.preimage hcont
      closed2 := C.closed2.preimage hcont
      generic1 := isGenericPoint_preimage_of_isInducing _a1.toIsInducing C.generic1 hx1
      generic2 := isGenericPoint_preimage_of_isInducing _a1.toIsInducing C.generic2 hx2
      mem_first_closed := by
        show opIb U0_ x0 ∈ C.S1
        rw [hx0]
        exact C.mem_first_closed
      mem_second_closed := by
        show opIb U0_ x0 ∈ C.S2
        rw [hx0]
        exact C.mem_second_closed }
    hm1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  rw [support_comap_eq]
  exact preimage_mono hS1
  rw [support_comap_eq]
  intro hcon
  apply hxi2Z
  have h' : opIb U0_ x2 ∈ spI Z := hcon
  rwa [hx2] at h'
  intro hcon
  apply hxi1M
  have h' : opIb U0_ x1 ∈ Mem := hcon
  rwa [hx1] at h'
  intro hcon
  apply hxi2M
  have h' : opIb U0_ x2 ∈ Mem := hcon
  rwa [hx2] at h'
  have h1 : AgreeNear I _a0 $ opIb U0_ x1 := by
    rwa [hx1]
  have h2 := hV.agreeNear_comap W U0_ I _a0 x1 h1
  rw [hV.comap_vanishing W ⟨C.S1, C.closed1⟩ U0_
    ⟨preimage U0_.ib C.S1, C.closed1.preimage hcont⟩ rfl] at h2
  exact h2
  show orderAt (cmI I U0_.i) x1 = 1
  rwa [hV.orderAt_comap W U0_ I x1, hx1]
  show x2 ∈ (spI (cmI I U0_.i) : Set $ oSch U0_)
  rw [support_comap_eq]
  show opIb U0_ x2 ∈ spI I
  rwa [hx2]

theorem orderOneCentersIsolated_of_eq_mul_of_subset_orderAtLeastLocus
    (M N : ISD W) mu_ (hI : I = M * N)
    (hM : (M.support : Set ↥W) ⊆ Mem) (hmu : m ≤ mu_)
    (hZ : (Z.support : Set ↥W) ⊆ orderAtLeastLocus N mu_)
    (ih : OrderOneCentersIsolated V W p N mu_ Mem Z) : OrderOneCentersIsolated V W p I m Mem Z := by
  intro C hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2I
  have hxi1S := C.generic1.mem
  have hM1 := fun hh => hxi1M $ hM hh
  have hM2 := fun hh => hxi2M $ hM hh
  obtain ⟨Uc, hUcmem, hUctop⟩ : ∃ Uc : Opn W, C.xi1 ∈ Uc ∧ M.comap Uc.i = ⊤ :=
    ⟨⟨M.supportᶜ, (hV.isClosed_support W M).isOpen_compl⟩, hM1,
      comap_io_eq_top_of_disjoint M _ disjoint_compl_left⟩
  have hAIN : AgreeNear I N C.xi1 :=
    ⟨Uc, hUcmem, by rw [hI, hV.comap_mul, hUctop, hV.top_mul]⟩
  have hM0 := (orderAt_eq_zero_iff_not_mem_support M C.xi1).2 hM1
  have hle : orderAt N C.xi1 ≤ 1 := by
    have h2 := add_orderAt_le_orderAt_mul M N C.xi1
    rwa [hM0, zero_add, ← hI, hord] at h2
  have hmu1 := (mem_orderAtLeastLocus_iff N mu_ C.xi1).1 $ hZ $ hS1 hxi1S
  have hmule : mu_ ≤ 1 := by exact_mod_cast le_trans hmu1 hle
  have hmu1_ : mu_ = 1 := by omega
  have hordN : orderAt N C.xi1 = 1 := by
    refine le_antisymm hle ?_
    rw [hmu1_] at hmu1
    exact_mod_cast hmu1
  refine ih C hmu1_ hS1 hxi2Z hxi1M hxi2M (hV.agreeNear_trans W N I (V W ⟨C.S1, C.closed1⟩) C.xi1 (agreeNear_symm hAIN) hagree) hordN ?_
  rw [hI, hV.support_mul] at hxi2I
  rcases (mem_union _ _ _).1 hxi2I with h' | h'
  exact absurd h' hM2
  exact h'

theorem orderOneCentersIsolated_of_forall_opens
    (U : ∀ z : ↥W, z ∈ Z.support → Opn W)
    (hU : ∀ z hz, z ∈ U z hz)
    (ih : ∀ z hz,
      OrderOneCentersIsolated V (U z hz).toScheme ((U z hz).i ≫ p) (I.comap (U z hz).i) m
        (⇑(U z hz).ib ⁻¹' Mem) (Z.comap (U z hz).i)) :
    OrderOneCentersIsolated V W p I m Mem Z := by
  intro C hm1 hS1 hxi2Z hxi1M hxi2M hagree hord hxi2I
  have hz := hS1 C.mem_first_closed
  exact false_of_orderOneCentersIsolated_comap_opens hV (U C.pt hz) C (hU C.pt hz) (ih C.pt hz) hm1 hS1 hxi2Z
    hxi1M hxi2M hagree hord hxi2I

theorem orderOneCentersIsolated_of_principalizationCertificate
    (h : PrincipalizationCertificate W p I m Mem Z) : OrderOneCentersIsolated V W p I m Mem Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W' p' I' m' Mem' Z' _ => OrderOneCentersIsolated V W' p' I' m' Mem' Z')
    (motive_2 := fun W' p' N' mu' Mem' Z' _ => OrderOneCentersIsolated V W' p' N' mu' Mem' Z')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  intro W' p' I' m' Mem' Z' hmem
  intro C _ hS1 _ hxi1M _ _ _ _
  exact hxi1M $ hmem $ hS1 C.generic1.mem
  intro W' p' I' m' Mem' Z' hm
  intro _ hm1 _ _ _ _ _ _ _
  omega
  intro W' p' I' m' Mem' Z' M' N' mu' hI' hM' hmu' hZ' hcert' ihc
  exact orderOneCentersIsolated_of_eq_mul_of_subset_orderAtLeastLocus hV M' N' mu' hI' hM' hmu' hZ' ihc
  intro W' p' I' m' Mem' Z' U' hU' hcert' ihc
  exact orderOneCentersIsolated_of_forall_opens hV U' hU' ihc
  intro W' p' N' mu' Mem' Z' hmem
  intro C _ hS1 _ hxi1M _ _ _ _
  exact hxi1M $ hmem $ hS1 C.generic1.mem
  intro W' p' N' mu' Mem' Z' hmu
  intro _ hm1 _ _ _ _ _ _ _
  omega
  intro W' p' N' mu' Mem' Z' U' hU' hcert' ihc
  exact orderOneCentersIsolated_of_forall_opens hV U' hU' ihc
  intro W' p' N' mu' Mem' Z' U' hU' H' hH' hNH' hZH' J' hJnone' hJcomp' hJloc' hJcert' ihc
  exact orderOneCentersIsolated_of_isSmoothDivisor hV U' hU' H' hH' hNH' hZH' J' hJnone' hJcomp' hJloc' ihc
end
end
end



structure PointedIrreducibleClosed (W : Sch) where
  S : Set ↥W
  xi : ↥W
  pt : ↥W
  closedS : IsClosed S
  irredS : IsIrreducible S
  genericXi : IsGenericPoint xi S
  memPt : pt ∈ S

structure SmoothVanishingHypotheses (V : VanishingAssignment) : Prop where
  orderAt_vanishing_eq_one : ∀ (k : Type) [Field k] [CharZero k] (W : Sch)
      (p : W ⟶ Sp k), Smooth p →
      ∀ T : Closeds ↥W, IsIrreducible (T : Set ↥W) →
      Smooth ((V W T).si ≫ p) →
      (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ (T : Set ↥W)) →
      ∀ x ∈ (T : Set ↥W), orderAt (V W T) x = 1
  smooth_opens_io_comp : ∀ (k : Type) [Field k] [CharZero k] (W : Sch)
      (p : W ⟶ Sp k) (U : Opn W), Smooth p → Smooth (U.i ≫ p)
  smooth_vanishing_hypersurface : ∀ (k : Type) [Field k] [CharZero k] (W : Sch)
      (p : W ⟶ Sp k) (U : Opn W) (H : IdealSheafData (U.toScheme)),
      IsSmoothDivisor (U.i ≫ p) H →
      ∀ (T : Closeds ↥W) (S : Closeds ↥(H.subscheme)),
        (S : CSet (H.subscheme)) = (H.si ≫ U.i).base ⁻¹' (T : Set ↥W) →
        (U.ib ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
        Smooth ((V W T).si ≫ p) →
        Smooth ((V H.subscheme S).si ≫ (H.si ≫ (U.i ≫ p)))
  smooth_vanishing_opens : ∀ (k : Type) [Field k] [CharZero k] (W : Sch)
      (p : W ⟶ Sp k) (U : Opn W) (T : Closeds ↥W)
      (S : Closeds ↥(U.toScheme)),
      (S : Set ↥(U.toScheme)) = U.ib ⁻¹' (T : Set ↥W) →
      Smooth ((V W T).si ≫ p) →
      Smooth ((V U.toScheme S).si ≫ (U.i ≫ p))

def SmoothOrderOneCentersIsolated (V : VanishingAssignment) {k : Type} [Field k] [CharZero k]
    (W : Sch) (p : W ⟶ Sp k) (I : ISD W) (m : ℕ)
    (Mem : Set ↥W) (Z : ISD W) : Prop :=
  ∀ C : PointedIrreducibleClosed W, Smooth p → m = 1 →
    Smooth (subschemeι (V W ⟨C.S, C.closedS⟩) ≫ p) →
    (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S) →
    C.xi ∉ (support Z : Set ↥W) →
    Disjoint C.S Mem →
    (∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x) →
    C.pt ∈ (support Z : Set ↥W) → False

section
variable {V} (hV : IdealSheafGeometryHypotheses V)
include hV
theorem subset_support_of_agreeNear
    (W : Sch) (N : ISD W) T (hT : IsClosed T)
    (hagree : ∀ x ∈ T, AgreeNear N (V W ⟨T, hT⟩) x) :
    T ⊆ (N.support : Set ↥W) := by
  intro x hx
  rwa [mem_support_iff_of_agreeNear hV $ hagree x hx, hV.support_vanishing W ⟨T, hT⟩]

section
variable (hG : SmoothVanishingHypotheses V) {k : Type} [Field k] [CharZero k] {W : Sch}
include hG
theorem orderAt_eq_one_of_agreeNear
    {p : W ⟶ Sp k} {I : ISD W} (C : PointedIrreducibleClosed W)
    (hp : Smooth p)
    (hsm : Smooth (subschemeι (V W ⟨C.S, C.closedS⟩) ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hagree : ∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x)
    {x : ↥W} (hx : x ∈ C.S) : orderAt I x = 1 := by
  rw [hV.orderAt_congr W I (V W ⟨C.S, C.closedS⟩) x $ hagree x hx]
  exact hG.orderAt_vanishing_eq_one k W p hp ⟨C.S, C.closedS⟩ C.irredS hsm hcomp x hx

section
variable (p : W ⟶ Sp k)
theorem false_of_smoothOrderOneCentersIsolated_opens (I Z : ISD W) m Mem
    (C : PointedIrreducibleClosed W) (U : Opn W) (hptU : C.pt ∈ (U : Set ↥W))
    (hIso : SmoothOrderOneCentersIsolated V U.toScheme (U.i ≫ p) (I.comap U.i) m
      (U.ib ⁻¹' Mem) (Z.comap U.i))
    (hp : Smooth p) (hm : m = 1)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).si ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hxi : C.xi ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint C.S Mem)
    (hagree : ∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x)
    (hpt : C.pt ∈ (Z.support : Set ↥W)) : False := by
  let _a0 := hV.isEmbedding_ι W U
  have hrange := hV.range_ι W U
  have hxiR := (C.genericXi.mem_open_set_iff $ hV.isOpen_opens W U).mpr ⟨C.pt, C.memPt, hptU⟩
  rw [← hrange] at hxiR
  have hptR := hptU
  rw [← hrange] at hptR
  obtain ⟨y0, hy0⟩ := hxiR
  obtain ⟨y1, hy1⟩ := hptR
  have hS'closed := C.closedS.preimage _a0.continuous
  have hgen' :=
    isGenericPoint_preimage_of_isInducing _a0.toIsInducing
      C.genericXi hy0
  have hirr' : IsIrreducible $ preimage U.ib C.S := by
    rw [← hgen']
    exact isIrreducible_singleton.closure
  have hmemPt := by
    show opIb U y1 ∈ C.S
    rw [hy1]
    exact C.memPt
  have _i31 : ∀ E ∈ irreducibleComponents (oSch U), ¬ E ⊆ preimage U.ib C.S := by
    intro E hE hsub
    have hEirr := an1 hE
    have hrange := hV.range_ι W U
    let _a0 := hV.isEmbedding_ι W U
    have hmemU : ∀ y : (oSch U), opIb U y ∈ (U : Set W) := by
      intro y
      rw [← hrange]
      exact mem_range_self y
    obtain ⟨y0, hy0⟩ := hEirr.nonempty
    have himg := hEirr.image _ _a0.continuous.continuousOn
    obtain ⟨Zc, hZpre, hAZ, hZmax⟩ :=
      exists_preirreducible (closure $ opIb U '' E) himg.closure.2
    have hZirr : IsIrreducible Zc := ⟨himg.closure.1.mono hAZ, hZpre⟩
    have hZmem : Zc ∈ irreducibleComponents W :=
      ⟨hZirr, fun u hu hZu => (hZmax u hu.2 hZu).le⟩
    have hEZ : E ⊆ preimage U.ib Zc := by
      intro y hy
      exact hAZ $ subset_closure ⟨y, hy, rfl⟩
    let _m0 := Zc ∩ U
    have hZU : _m0.Nonempty := ⟨opIb U y0, hEZ hy0, hmemU y0⟩
    let _a1 := hV.isOpen_opens W U
    have hsubr : _m0 ⊆ range U.ib := by
      rw [hrange]
      exact inter_subset_right
    have hPirr :=
      isIrreducible_preimage_of_isEmbedding _a0 (isIrreducible_inter_open hZirr _a1 hZU) hsubr
    have hPeq : preimage U.ib _m0 = preimage U.ib Zc := by
      ext y
      constructor
      intro hy
      exact an1 hy
      intro hy
      exact ⟨hy, hmemU y⟩
    rw [hPeq] at hPirr
    have hpreimageSub := an2 hE hPirr hEZ
    have hZT : Zc ∩ U ⊆ C.S := by
      rintro x ⟨hxZ, hxU⟩
      rw [← hrange] at hxU
      obtain ⟨y, rfl⟩ := hxU
      exact hsub $ hpreimageSub hxZ
    have hZcl := isClosed_of_mem_irreducibleComponents Zc hZmem
    refine hcomp Zc hZmem ?_
    rw [← closure_inter_open_eq hZcl hZirr _a1 hZU]
    exact closure_minimal hZT C.closedS
  refine hIso ⟨preimage U.ib C.S, y0, y1, hS'closed, hirr', hgen', hmemPt⟩
    (hG.smooth_opens_io_comp k W p U hp) hm
    (hG.smooth_vanishing_opens k W p U ⟨C.S, C.closedS⟩ ⟨preimage U.ib C.S, hS'closed⟩ rfl hsm)
    _i31 ?_ ?_ ?_ ?_
  intro hmem
  apply hxi
  have h1 :=
    (one_le_orderAt_iff_mem_support (cmI Z U.i) y0).mpr hmem
  rw [hV.orderAt_comap W U Z y0, hy0] at h1
  exact mp_ (one_le_orderAt_iff_mem_support Z C.xi) h1
  rw [disjoint_left]
  intro y hy hy2
  exact (Set.disjoint_left.mp hdisj hy) hy2
  intro y hy
  have h1 := hV.agreeNear_comap W U I (V W ⟨C.S, C.closedS⟩) y $ hagree _ hy
  rwa [hV.comap_vanishing W ⟨C.S, C.closedS⟩ U ⟨preimage U.ib C.S, hS'closed⟩ rfl] at h1
  have h1 := mpr_ (one_le_orderAt_iff_mem_support Z C.pt) hpt
  rw [← hy1, ← hV.orderAt_comap W U Z y1] at h1
  exact mp_ (one_le_orderAt_iff_mem_support (cmI Z U.i) y1) h1

end

theorem smoothOrderOneCentersIsolated_of_principalizationCertificate
    {p : W ⟶ Sp k} {I : ISD W} {m : ℕ} {Mem : Set ↥W}
    {Z : ISD W} (h : PrincipalizationCertificate W p I m Mem Z) :
    SmoothOrderOneCentersIsolated V W p I m Mem Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W p I m Mem Z _ => SmoothOrderOneCentersIsolated V W p I m Mem Z)
    (motive_2 := fun W p N mu_ Mem Z _ => SmoothOrderOneCentersIsolated V W p N mu_ Mem Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  intro W p I m Mem Z hZM C hp hm hsm hcomp hxi hdisj hagree hpt
  exact (Set.disjoint_left.mp hdisj C.memPt) $ hZM hpt
  intro W p I m Mem Z hm2 C hp hm hsm hcomp hxi hdisj hagree hpt
  omega
  intro W p I m Mem Z M N mu_ hI hM hmu hZc hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
  have hIN : ∀ x ∈ C.S, AgreeNear I N x := by
    intro x hx
    have hxM := fun hmm =>
      (Set.disjoint_left.mp hdisj hx) $ hM hmm
    obtain ⟨Uc, hUcx, hUcdisj⟩ :
        ∃ Uc : Opn W, x ∈ Uc ∧ Disjoint (Uc : Set W) M.supp :=
      ⟨⟨M.suppᶜ, (hV.isClosed_support W M).isOpen_compl⟩, hxM,
        disjoint_compl_left⟩
    refine ⟨Uc, hUcx, ?_⟩
    have hMtop := comap_io_eq_top_of_disjoint M Uc hUcdisj
    rw [hI, hV.comap_mul W Uc.toScheme Uc.i M N, hMtop, hV.top_mul]
  have hagreeN := fun x hx =>
    hV.agreeNear_trans W N I (V W ⟨C.S, C.closedS⟩) x (agreeNear_symm $ hIN x hx) $ hagree x hx
  rcases m63 mu_ 2 with h2 | h2
  have hmu1 : mu_ = 1 := by omega
  exact ih C hp hmu1 hsm hcomp hxi hdisj hagreeN hpt
  have hord :=
    orderAt_eq_one_of_agreeNear hV hG C hp hsm hcomp hagreeN C.memPt
  have hmem := hZc hpt
  rw [mem_orderAtLeastLocus_iff, hord] at hmem
  have hle : mu_ ≤ 1 := by exact_mod_cast hmem
  omega
  intro W p I m Mem Z U hU hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
  have hz := hpt
  exact false_of_smoothOrderOneCentersIsolated_opens hV hG p I Z m Mem C (U C.pt hz) (hU C.pt hz)
    (ih C.pt hz) hp hm hsm hcomp hxi hdisj hagree hpt
  intro W p N mu_ Mem Z hZM C hp hm hsm hcomp hxi hdisj hagree hpt
  exact (Set.disjoint_left.mp hdisj C.memPt) $ hZM hpt
  intro W p N mu_ Mem Z hmu2 C hp hm hsm hcomp hxi hdisj hagree hpt
  omega
  intro W p N mu_ Mem Z U hU hcert ih C hp hm hsm hcomp hxi hdisj hagree hpt
  have hz := hpt
  exact false_of_smoothOrderOneCentersIsolated_opens hV hG p N Z mu_ Mem C (U C.pt hz) (hU C.pt hz)
    (ih C.pt hz) hp hm hsm hcomp hxi hdisj hagree hpt
  intro W p N mu_ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih C hp hm hsm hcomp hxi
    hdisj hagree hpt
  have hz := hpt
  let U := U C.pt hz
  let H := H C.pt hz
  let hptU := hU C.pt hz
  let hH := hH C.pt hz
  let hNsubH := hNsubH C.pt hz
  let J := J C.pt hz
  let ih := fun Jz hJ => ih C.pt hz Jz hJ
  have hxiS := C.genericXi.mem
  cases hJ : J with
  | none =>
    exact false_of_isOpen_preimage_support hV W N Z
      ⟨C.S, C.S, C.xi, C.xi, C.pt, C.closedS, C.closedS, C.genericXi,
        C.genericXi, C.memPt, C.memPt⟩ U H hptU hpt (hZH C.pt hz) hNsubH ((hJnone C.pt hz) hJ) hxi $ (one_le_orderAt_iff_mem_support N C.xi).mp $ le_of_eq (orderAt_eq_one_of_agreeNear hV hG C hp hsm hcomp hagree hxiS).symm
  | some Jz =>
    have hIH := ih Jz hJ
    have hsubH : (preimage U.ib C.S) ⊆ suppI H := by
      intro y hy
      apply hNsubH
      rw [p45]
      exact (subset_support_of_agreeNear hV W N C.S C.closedS hagree) hy
    obtain ⟨y0, hy0⟩ := exists_subschemeio_comp_io_apply_eq_of_mem hV W U H C.S hsubH C.xi ((C.genericXi.mem_open_set_iff $ hV.isOpen_opens W U).mpr ⟨C.pt, C.memPt, hptU⟩) hxiS
    obtain ⟨y1, hy1⟩ := exists_subschemeio_comp_io_apply_eq_of_mem hV W U H C.S hsubH C.pt hptU C.memPt
    have hS'closed :=
      isClosed_preimage_subschemeio_comp_io hV W U H C.S C.closedS
    have hgen' :=
      isGenericPoint_preimage_subschemeio_comp_io hV W U H C.S C.xi C.genericXi y0 hy0
    let _s0 := siI H ≫ opI U
    have hirr' : IsIrreducible $ preimage _s0.base C.S := by
      rw [← hgen']
      exact isIrreducible_singleton.closure
    have hmemPt : y1 ∈ preimage _s0.base C.S := by
      show bsM _s0 y1 ∈ C.S
      rw [hy1]
      exact C.memPt
    let _a1 := V H.subscheme ⟨preimage _s0.base C.S, hS'closed⟩
    have hagree' : ∀ x ∈ preimage _s0.base C.S,
        AgreeNear Jz _a1 x := by
      intro x hx
      have h1 :=
        hV.agreeNear_vanishing_restrict W N U H ⟨C.S, C.closedS⟩
          ⟨preimage _s0.base C.S, hS'closed⟩ x rfl hsubH $ hagree _ hx
      have h2 :=
        (hJloc C.pt hz) Jz hJ x $ Set.disjoint_left.mp hdisj hx
      exact hV.agreeNear_trans H.subscheme Jz (cmI (cmI N U.i) H.si)
        _a1 x h2 h1
    have hcomp' : ∀ E ∈ irreducibleComponents (subS H),
        ¬ E ⊆ preimage _s0.base C.S := by
      intro E hE hEsub
      exact hV.not_subset_support_of_nonzeroOnComponents H.subscheme Jz ((hJcomp C.pt hz) Jz hJ) E hE
        (hEsub.trans $ subset_support_of_agreeNear hV H.subscheme Jz (preimage _s0.base C.S) hS'closed hagree')
    have hsupp : ∀ x : (subS H),
        x ∈ ((cmI (cmI Z U.i) H.si).support : CSet $ subS H) ↔
          _s0.base x ∈ spI Z := by
      intro x
      constructor
      intro hx
      have h1 : (H.subschemeι.base x) ∈ (spI (cmI Z U.i) : Set $ oSch U) := by simp_all
      have h2 : (opIb U $ H.subschemeι.base x) ∈ spI Z := by simp_all
      rwa [hV.base_comp]
      intro hx
      rw [hV.base_comp] at hx
      have h1 : (H.subschemeι.base x) ∈ (spI (cmI Z U.i) : Set $ oSch U) := by
        rwa [p45]
      rwa [p45]
    have hxi' : y0 ∉ ((cmI (cmI Z U.i) H.si).support : CSet $ subS H) := by simp_all
    have hpt' : y1 ∈ ((cmI (cmI Z U.i) H.si).support : CSet $ subS H) := by simp_all
    have hdisj' : Disjoint (preimage _s0.base C.S)
        (preimage _s0.base Mem) := by
      rw [disjoint_left]
      intro x hx hx2
      exact (Set.disjoint_left.mp hdisj hx) hx2
    exact hIH ⟨preimage _s0.base C.S, y0, y1, hS'closed, hirr', hgen', hmemPt⟩
      ((mp_ (isSmoothDivisor_iff (opI U ≫ p) H) hH).2) hm (hG.smooth_vanishing_hypersurface k W p U H hH ⟨C.S, C.closedS⟩ ⟨preimage _s0.base C.S, hS'closed⟩ rfl hsubH hsm) hcomp' hxi' hdisj' hagree' hpt'
end
end



noncomputable def vanishingIdealAssignment : VanishingAssignment :=
  fun _ T => vanishingIdeal T

theorem vanishingIdealAssignment_apply X T :
    vanishingIdealAssignment X T = vanishingIdeal T := rfl

def VanishingOrderOneOnSmoothDivisor : Prop :=
  ∀ (k : Type) [Field k] (W : Sch) (p : W ⟶ Sp k)
    (U : Opn W) (D : IdealSheafData (U.toScheme)),
    IsSmoothDivisor (U.i ≫ p) D →
    ∀ (T : Closeds ↥(D.subscheme)) (y : ↥(D.subscheme)),
      IsGenericPoint y (T : CSet (D.subscheme)) →
      (T : CSet (D.subscheme)) ∉ irreducibleComponents ↥(D.subscheme) →
      orderAt (vanishingIdealAssignment D.subscheme T) y = 1

def AgreeNearVanishingComapSubscheme : Prop :=
  ∀ (W : Sch) (N : ISD W) (U : Opn W)
    (H : IdealSheafData (U.toScheme)) (T : Closeds ↥W) (S : Closeds ↥(H.subscheme))
    (x : ↥(H.subscheme)),
    (S : CSet (H.subscheme)) = (H.si ≫ U.i).base ⁻¹' (T : Set ↥W) →
    (U.ib ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
    AgreeNear N (vanishingIdealAssignment W T) ((H.si ≫ U.i).base x) →
    AgreeNear ((N.comap U.i).comap H.si) (vanishingIdealAssignment H.subscheme S) x

def VanishingComapOpens : Prop :=
  ∀ (W : Sch) (T : Closeds ↥W) (V : Opn W) (S : Closeds ↥(V.toScheme)),
    (S : Set ↥(V.toScheme)) = V.ib ⁻¹' (T : Set ↥W) →
    (vanishingIdealAssignment W T).comap V.i = vanishingIdealAssignment V.toScheme S

def OrderAtEqOfAgreeNear : Prop :=
  ∀ (W : Sch) (I J : ISD W) (x : ↥W),
    AgreeNear I J x → orderAt I x = orderAt J x

theorem comap_opens_eq_of_le {W : Sch} {I J : ISD W} {U U' : Opn W}
    (h : U' ≤ U) (hEq : I.comap U.i = J.comap U.i) :
    I.comap U'.i = J.comap U'.i := by
  have hio : W.homOfLE h ≫ U.i = U'.i := by simp
  rw [← hio, comap_comp, comap_comp, hEq]

section
variable (W : Sch) (V : Opn W)
theorem agreeNear_comap_io (I J : ISD W)
    y (h : AgreeNear I J (V.ib y)) :
    AgreeNear (comap I V.i) (comap J V.i) y := by
  obtain ⟨U, hU, hEq⟩ := mp_ (agreeNear_iff I J $ V.ib y) h
  refine mpr_ (agreeNear_iff _ _ _) ⟨V.i.pre U, hU, ?_⟩
  rw [← comap_comp, ← comap_comp,
    ← morphismRestrict_ι V.i U, comap_comp,
    comap_comp, hEq]

theorem orderAt_comap_io (I : ISD W)
    y :
    orderAt (I.comap V.i) y = orderAt I (V.ib y) :=
  orderAt_comap_of_isOpenImmersion V.i I y
end

theorem orderAtEqOfAgreeNear : OrderAtEqOfAgreeNear := by
  intro W I J x h
  obtain ⟨U, hxU, hEq⟩ := mp_ (agreeNear_iff I J x) h
  obtain ⟨y, hy⟩ : ∃ y : (oSch U), opIb U y = x := by
    have hx : x ∈ range U.ib := by simpa using hxU
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy⟩
  rw [← hy, ← orderAt_comap_io W U I y, ← orderAt_comap_io W U J y, hEq]

section
variable (h1 : VanishingOrderOneOnSmoothDivisor) (h2 : AgreeNearVanishingComapSubscheme) (h3 : VanishingComapOpens)
include h1 h2 h3
theorem idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear (h4 : OrderAtEqOfAgreeNear) :
    IdealSheafGeometryHypotheses vanishingIdealAssignment :=
  { agreeNear_comap := agreeNear_comap_io
    agreeNear_trans := by
      intro W I J K x hIJ hJK
      obtain ⟨U1, hx1, e1⟩ := mp_ (agreeNear_iff I J x) hIJ
      obtain ⟨U2, hx2, e2⟩ := mp_ (agreeNear_iff J K x) hJK
      exact mpr_ (agreeNear_iff I K x)
        ⟨U1 ⊓ U2, ⟨hx1, hx2⟩,
          (comap_opens_eq_of_le inf_le_left e1).trans $ comap_opens_eq_of_le inf_le_right e2⟩
    comap_mul := fun W X f I J => comap_mul I J f
    base_comp := fun X Y Z f g x => by simp
    isClosed_support := fun W I => I.support.isClosed
    isClosedEmbedding_subschemeι := fun W I =>
      IsClosedImmersion.isClosedEmbedding (f := siI I)
    isEmbedding_ι := fun W U => U.ι.isOpenEmbedding.toIsEmbedding
    isOpen_opens := fun W U => U.2
    orderAt_comap := orderAt_comap_io
    orderAt_congr := h4
    orderAt_vanishing_eq_one := h1
    range_ι := fun W U => by simp
    range_subschemeι := fun W I => by simp
    support_mul := fun W I J => by
      rw [support_mul, TopologicalSpace.Closeds.coe_sup]
    not_subset_support_of_nonzeroOnComponents := fun W I h => mp_ (nonzeroOnComponents_iff I) h
    support_vanishing := fun W T => by simp [vanishingIdealAssignment]
    top_mul := fun W I => by simp
    agreeNear_vanishing_restrict := h2
    comap_vanishing := h3 }

theorem idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor :
    IdealSheafGeometryHypotheses vanishingIdealAssignment :=
  idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear h1 h2 h3 orderAtEqOfAgreeNear
end



section
variable (X : Sch)
private theorem exists_affineOpens_mem x :
    ∃ U : X.affineOpens, x ∈ U.1.1 := by
  have hx : x ∈ (⨆ U : affO X, (U : Opn X)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := mp_ mem_iSup hx
  exact ⟨U, hU⟩

theorem maximalIdeal_stalk_ne_bot_of_specializes x y (h : y ⤳ x) (hne : y ≠ x) :
    maximalIdeal ↑(X.presheaf.stalk x) ≠ ⊥ := by
  intro hbot
  obtain ⟨U, hxU0⟩ := exists_affineOpens_mem X x
  have hxU : x ∈ U.1 := hxU0
  have hU : IsAffineOpen U.1 := U.2
  have hmem : x ∈ closure ({y} : Set X) := mp_ specializes_iff_mem_closure h
  have hyU : y ∈ U.1 := by
    let _m0 := (U.1 : Set X)
    have hopen : IsOpen _m0 := U.1.2
    obtain ⟨z, hzU, hzy⟩ := (mp_ mem_closure_iff hmem) _m0 hopen hxU
    rw [mem_singleton_iff] at hzy
    rwa [← hzy]
  let _s1 := hU.primeIdealOf ⟨x, hxU⟩
  have e1 : (hU.fromSpec) _s1 = x :=
    hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  let _a0 := hU.primeIdealOf ⟨y, hyU⟩
  have e2 : (hU.fromSpec) _a0 = y :=
    hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hspec : hU.primeIdealOf ⟨y, hyU⟩ ⤳ hU.primeIdealOf ⟨x, hxU⟩ := by
    apply ((hU.fromSpec).isOpenEmbedding.toIsEmbedding.toIsInducing).specializes_iff.mp
    rwa [e1, e2]
  have hqp : _a0.asIdeal ≤ _s1.asIdeal := by
    have h2 := mp_ specializes_iff_mem_closure hspec
    rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus] at h2
    exact fun z hz => h2 hz
  have hne' : _a0.asIdeal ≠ _s1.asIdeal := by
    intro heq
    apply hne
    exact st_ e2 (by rw [m210 heq]; exact e1)
  obtain ⟨a, hap, haq⟩ := SetLike.exists_of_lt $ lt_of_le_of_ne hqp hne'
  let _ := (pGerm X U.1 x hxU).hom.toAlgebra
  let _a2 := stkX X x
  have hloc : IsLocalization _s1.asIdeal.primeCompl
      _a2 := hU.isLocalization_stalk ⟨x, hxU⟩
  let _s0 := algebraMap Γ(X, U.1) _a2
  have hmax : m6 _s0
      _s1.asIdeal
      = maximalIdeal _a2 :=
    IsLocalization.AtPrime.map_eq_maximalIdeal ..
  have hmapmem : _s0 a
      ∈ maximalIdeal _a2 := by
    rw [← hmax]
    exact mem_map_of_mem _ hap
  have h0 : _s0 a = 0 := by
    rw [hbot] at hmapmem
    simpa using hmapmem
  have h1 : _s0 a
      = _s0 0 := by simp_all
  obtain ⟨c, hc⟩ := mp_ (IsLocalization.eq_iff_exists
    _s1.asIdeal.primeCompl _a2) h1
  let _a1 := (c : Γ(X, U.1))
  have hca : _a1 * a = 0 := by
    rwa [mul_zero] at hc
  have hcp : _a1 ∉ _s1.asIdeal := c.2
  have hcq : _a1 ∉ _a0.asIdeal := fun hc0 => hcp $ hqp hc0
  have hmem0 : _a1 * a ∈ _a0.asIdeal := by simp_all
  rcases _a0.isPrime.mem_or_mem hmem0 with hcc | haa
  exact hcq hcc
  exact haq haa

theorem orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents [IsLocallyNoetherian X] (S : Closeds ↥X) (x : ↥X)
    (hx : IsGenericPoint x (S : Set ↥X))
    (hS : (S : Set ↥X) ∉ irreducibleComponents ↥X) :
    orderAt (vanishingIdeal S) x = 1 := by
  have hx' := hx
  have hSirr : IsIrreducible (S : Set X) := by
    rw [← hx']
    exact isIrreducible_singleton.closure
  have hxS : x ∈ (S : Set X) := by
    rw [← hx']
    exact subset_closure $ mem_singleton x
  have hMax : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ S) S := by
    constructor
    simp_all
    simp_all
  obtain ⟨t, htpre, hSt, hmaxt⟩ := exists_preirreducible (S : Set X) hSirr.2
  have htirr : IsIrreducible t := ⟨⟨x, hSt hxS⟩, htpre⟩
  have htclosed : IsClosed t := by
    have h1 := hmaxt (closure t) htpre.closure subset_closure
    rw [← h1]
    exact isClosed_closure
  have htmem : t ∈ irreducibleComponents X := by
    constructor
    exact htirr
    intro u hu htu
    exact (hmaxt u hu.2 htu).le
  have hSnet : S ≠ t := by
    intro hEq
    exact hS $ hEq ▸ htmem
  obtain ⟨y, hy⟩ := m140 htirr htclosed
  have hy' := hy
  have hyx := hSt hxS
  rw [← hy', ← specializes_iff_mem_closure] at hyx
  have hyne : y ≠ x := by
    intro hEq
    apply hSnet
    rwa [← hx', ← hEq]
  exact orderAt_vanishingIdeal_eq_one S x S hMax hx $ maximalIdeal_stalk_ne_bot_of_specializes X x y hyx hyne
end

theorem vanishingOrderOneOnSmoothDivisor : VanishingOrderOneOnSmoothDivisor := by
  intro k hk W p U D hD T y hy hT
  have : IsLocallyNoetherian D.subscheme :=
    by
    obtain ⟨_, hsm⟩ := hD
    let _a0 := siI D ≫ opI U ≫ p
    have : Smooth _a0 := hsm
    have : LocallyOfFiniteType _a0 := inferInstance
    have : IsNoetherianRing $ m10 k := inferInstanceAs $ IsNoetherianRing k
    exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian _a0
  rw [vanishingIdealAssignment_apply]
  exact orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents D.subscheme T y hy hT

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end
section
open Opposite

namespace FunctorialResolution.Blowup

theorem map_mem_nonZeroDivisors_of_iso {A B : CRC} (e : A ≅ B) {x : A}
    (hx : x ∈ nonZeroDivisors A) : e.hom.hom x ∈ nonZeroDivisors B := by
  obtain ⟨hx1, hx2⟩ := mp_ mem_nonZeroDivisors_iff hx
  have h2 : ∀ z, e.inv.hom (e.hom.hom z) = z := by
    intro z
    simp
  have h3 : ∀ y, e.hom.hom (e.inv.hom y) = y := by
    intro y
    simp
  have key : ∀ y, e.hom.hom x * y = 0 → y = 0 := by
    intro y hy
    have h1 : e.inv.hom (e.hom.hom x * y) = 0 := by rw [hy, map_zero]
    rw [map_mul, h2 x] at h1
    have h4 := hx1 _ h1
    rw [← h3 y, h4, map_zero]
  rw [mem_nonZeroDivisors_iff]
  refine ⟨key, fun y hy => key y ?_⟩
  rwa [mul_comm]

private theorem exists_affineOpen_le (X : Sch) (x : X) (W : Opn X) (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ (U : Opn X) ∧ (U : Opn X) ≤ W := by
  obtain ⟨V, hV, hxV, hVW⟩ :=
    isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

theorem appLE_eq_id_of_eq_id {Z : Sch} (g : Z ⟶ Z) (hg : g = 𝟙 Z) U
    (h : U ≤ pre g U) : appLE g U U h = 𝟙 _ := by
  subst hg
  simp [appLE]
  exact tr_ (id_comp _) $ Z.presheaf.map_id _

section
variable {A B : Sch} (e : A ≅ B) (U : Opn B)
theorem le_preimage_inv_preimage_hom :
    U ≤ e.inv.pre (e.hom ⁻¹ᵁ U) := by
  intro y hy
  show ihB_ e (ibM e y) ∈ U
  have hb : ihB_ e (ibM e y) = y := by simp
  rwa [hb]

noncomputable def sectionsIsoPreimage :
    (B.sec U) ≅ Γ(A, e.hom.pre U) where
  hom := e.hom.appLE U (e.hom.pre U) le_rfl
  inv := e.inv.appLE (e.hom.pre U) U (le_preimage_inv_preimage_hom e U)
  hom_inv_id := by
    rw [appLE_comp_appLE]
    exact appLE_eq_id_of_eq_id _ e.inv_hom_id U _
  inv_hom_id := by
    rw [appLE_comp_appLE]
    exact appLE_eq_id_of_eq_id _ e.hom_inv_id _ _
end

theorem isLocallyGeneratedByNonZeroDivisor_top (X : Sch) :
    IsLocallyGeneratedByNonZeroDivisor (⊤ : ISD X) := by
  intro x
  obtain ⟨U, hxU, -⟩ := exists_affineOpen_le X x ⊤ trivial
  refine ⟨U, 1, hxU, one_mem _, ?_⟩
  simp

theorem isLocallyGeneratedByNonZeroDivisor_comap_top {X X' : Sch} (f : X' ⟶ X) :
    IsLocallyGeneratedByNonZeroDivisor (comap (⊤ : ISD X) f) := by
  intro x
  obtain ⟨U, hU, -⟩ := exists_affineOpen_le X (bsM f x) ⊤ trivial
  obtain ⟨V, hV, hVU⟩ := exists_affineOpen_le X' x (preU f (U : Opn X)) hU
  refine ⟨V, 1, hV, one_mem _, ?_⟩
  have h1 : ((⊤ : ISD X).ideal U) = ⊤ := by simp
  rw [p32 (⊤ : ISD X) f U V hVU, h1,
    m166, span_singleton_one]

theorem IsLocallyGeneratedByNonZeroDivisor.comap_iso {X' X'' : Sch} {J : ISD X'}
    (hJ : IsLocallyGeneratedByNonZeroDivisor J) (e : X'' ≅ X') :
    IsLocallyGeneratedByNonZeroDivisor (J.comap e.hom) := by
  intro x
  obtain ⟨U, f, hxU, hf, hJU⟩ := hJ $ ihB_ e x
  refine ⟨⟨e.hom.pre U, IsAffineOpen.preimage_of_isIso U.2 e.hom⟩,
    (e.hom.appLE U (e.hom.pre U) le_rfl).hom f, hxU, FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso (sectionsIsoPreimage e U) hf, ?_⟩
  rw [comap_ideal_eq_map_appLE J e.hom U
    ⟨e.hom.pre U, IsAffineOpen.preimage_of_isIso U.2 e.hom⟩ le_rfl, hJU,
    map_span, image_singleton]

section
variable {X X' : Sch} {pi_ : X' ⟶ X}
section
variable {I : ISD X} (h : IsBlowupAlongIdealSheaf pi_ I)
include h
theorem IsBlowupAlongIdealSheaf.isLocallyGeneratedByNonZeroDivisor_comap : IsLocallyGeneratedByNonZeroDivisor (comap I pi_) :=
  an1 h

theorem IsBlowupAlongIdealSheaf.existsUnique_lift W g (hg : IsLocallyGeneratedByNonZeroDivisor (comap I g)) :
    ∃! k : W ⟶ X', k ≫ pi_ = g :=
  an2 h W g hg

theorem IsBlowupAlongIdealSheaf.hom_ext_of_comp_eq {W : Sch} {g : W ⟶ X} (hg : IsLocallyGeneratedByNonZeroDivisor (comap I g))
    {a b : W ⟶ X'} (ha : a ≫ pi_ = g) (hb : b ≫ pi_ = g) : a = b :=
  (an2 h W g hg).unique ha hb

theorem IsBlowupAlongIdealSheaf.isIso_of_isLocallyGeneratedByNonZeroDivisor (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsIso pi_ := by
  have _i32 : IsLocallyGeneratedByNonZeroDivisor $ cmI I $ 𝟙 X := by simp_all
  obtain ⟨s, hs, -⟩ := an2 h X (𝟙 X) _i32
  refine ⟨⟨s, ?_, hs⟩⟩
  exact h.hom_ext_of_comp_eq h.1 (by rw [assoc, hs, comp_id]) $ id_comp pi_
end

theorem IsBlowupAlongIdealSheaf.isIso_of_top
    (h : IsBlowupAlongIdealSheaf pi_ (⊤ : ISD X)) : IsIso pi_ :=
  h.isIso_of_isLocallyGeneratedByNonZeroDivisor $ isLocallyGeneratedByNonZeroDivisor_top X
end

theorem isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor {X : Sch} I
    (hI : IsLocallyGeneratedByNonZeroDivisor I) : IsBlowupAlongIdealSheaf (𝟙 X) I := by
  constructor
  rwa [comap_id]
  simp_all


theorem IsBlowupAlongIdealSheaf.exists_iso {X X1 X2 : Sch} {pi1 : X1 ⟶ X} {pi2 : X2 ⟶ X}
    {I : ISD X} (h1_ : IsBlowupAlongIdealSheaf pi1 I) (h2_ : IsBlowupAlongIdealSheaf pi2 I) :
    ∃ e : X1 ≅ X2, e.hom ≫ pi2 = pi1 := by
  obtain ⟨a, ha, -⟩ := an2 h2_ X1 pi1 h1_.1
  obtain ⟨b, hb, -⟩ := an2 h1_ X2 pi2 h2_.1
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  exact h1_.hom_ext_of_comp_eq h1_.1 (by rw [assoc, hb, ha]) $ id_comp pi1
  exact h2_.hom_ext_of_comp_eq h2_.1 (by rw [assoc, ha, hb]) $ id_comp pi2

theorem IsBlowupAlongIdealSheaf.iso_hom_comp {X X' X'' : Sch} {pi_} {I : ISD X}
    (h : IsBlowupAlongIdealSheaf pi_ I) (e : X'' ≅ X') : IsBlowupAlongIdealSheaf (e.hom ≫ pi_) I := by
  have hcomp : I.comap (isoH e ≫ pi_) = (I.comap pi_).comap e.hom := by
    simp [comap_comp]
  constructor
  rw [hcomp]
  exact h.1.comap_iso e
  intro W g hg
  obtain ⟨k, hk, hk'⟩ := an2 h W g hg
  refine ⟨k ≫ isoI e, ?_, ?_⟩
  show (k ≫ isoI e) ≫ isoH e ≫ pi_ = g
  rw [assoc, ← assoc e.inv e.hom pi_, e.inv_hom_id, id_comp, hk]
  intro m hm
  have hme := hk' _ $ tr_ (assoc m e.hom pi_) hm
  rw [← hme, assoc, e.hom_inv_id, comp_id]





variable {R : Type} [CommRing R]

section
variable (I : Ideal R)
def specIdealSheaf : IdealSheafData (Sp R) :=
  ofIdealTop
    (Ideal.map (GSpecIso (CommRingCat.of R)).inv.hom I)

theorem specIdealSheaf_eq_ofIdealTop :
    specIdealSheaf I =
      ofIdealTop
        (Ideal.map (GSpecIso (CommRingCat.of R)).inv.hom I) := rfl

theorem specIdealSheaf_ideal_top :
    (specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top (Sp R)⟩ =
      Ideal.map (GSpecIso (CommRingCat.of R)).inv.hom I :=
  ofIdealTop_ideal_top _

section
variable (a : ↥I)
def chartSectionsIso :
    CommRingCat.of (Away (reesGrading I) (reesGenerator I a)) ≅
      Γ(affineBlowup I, affineBlowupChart I a ''ᵁ ⊤) :=
  (GSpecIso
      (CommRingCat.of (Away (reesGrading I) (reesGenerator I a)))).symm ≪≫
    ((affineBlowupChart I a).appIso ⊤).symm

theorem chartSectionsIso_hom :
    (chartSectionsIso I a).hom =
      (GSpecIso
          (CommRingCat.of
            (Away (reesGrading I) (reesGenerator I a)))).inv ≫
        ((affineBlowupChart I a).appIso ⊤).inv := rfl

theorem chartSectionsIso_hom_apply
    x :
    (chartSectionsIso I a).hom.hom x =
      ((affineBlowupChart I a).appIso ⊤).inv.hom
        ((GSpecIso
            (CommRingCat.of
              (Away (reesGrading I) (reesGenerator I a)))).inv.hom x) := rfl
end
end

theorem comp_presheaf_map_eq_of_heq {Z : Sch} {A : CRC} (U : Opn Z) (hU : U = ⊤)
    (ph_ : A ⟶ (Z.sec U)) (h : (⊤ : Opn Z) ≤ U) (ps_ : A ⟶ (Z.sec (⊤ : Opn Z)))
    (hph : HEq ph_ ps_) : ph_ ≫ Z.presheaf.map (homOfLE h).op = ps_ := by
  subst hU
  obtain rfl : ph_ = ps_ := eq_of_heq hph
  rw [show (homOfLE h : (⊤) ⟶ ⊤) = 𝟙 (⊤) from rfl]
  simp


theorem appLE_image_top_comp_appIso_hom {Z X S : Sch} (g : Z ⟶ X)
    [IsOpenImmersion g] (p : X ⟶ S)
    e :
    appLE p ⊤ (g ''ᵁ ⊤) e ≫ (g.appIso ⊤).hom = (g ≫ p).appTop := by
  rw [appIso_hom', appLE_comp_appLE]
  exact (fun f h => comp_presheaf_map_eq_of_heq (preU f (⊤)) (le_antisymm le_top h) (f.app ⊤) h f.appTop m129) (g ≫ p) _

section
variable (I : Ideal R)
theorem chartRingHom_comp_chartSectionsIso_hom a :
    ofHom (chartRingHom I a) ≫ (chartSectionsIso I a).hom =
      (GSpecIso (CommRingCat.of R)).inv ≫
        appLE (AffineBlowup.toSpec I) ⊤ (affineBlowupChart I a ''ᵁ ⊤)
          (le_top.trans_eq (preimage_top (AffineBlowup.toSpec I)).symm) := by
  rw [chartSectionsIso_hom, ← assoc, Iso.comp_inv_eq, assoc,
    appLE_image_top_comp_appIso_hom, affineBlowupChart_comp_toSpec, algebraMap_chart_eq_chartRingHom]
  exact Scheme.ΓSpecIso_inv_naturality _

theorem isLocallyGeneratedByNonZeroDivisor_comap_toSpec :
    IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (AffineBlowup.toSpec I)) := by
  intro x
  obtain ⟨a, hx⟩ : ∃ a, x ∈ range (affineBlowupChart I a).base :=
    ⟨(affineBlowupAffineOpenCover I).idx x, (affineBlowupAffineOpenCover I).covers x⟩
  have hW := (isAffineOpen_top $ Spec $ m10
      (Away (reesGrading I) $ reesGenerator I a)).image_of_isOpenImmersion
      (affineBlowupChart I a)
  let _a0 := (chartSectionsIso I a).hom.hom $ chartRingHom I a a
  have _i33 : (cmI (specIdealSheaf I) $ AffineBlowup.toSpec I).ideal ⟨_, hW⟩ = span {_a0} := by
    have hcomp := congrArg CommRingCat.Hom.hom $ chartRingHom_comp_chartSectionsIso_hom I a
    rw [hom_comp, hom_comp, hom_ofHom] at hcomp
    have key : Ideal.map (appLE (AffineBlowup.toSpec I) ⊤ (affineBlowupChart I a ''ᵁ ⊤)
          (le_top.trans_eq (preimage_top $ p13 I).symm)).hom
          (m6 (GSpecIso $ m10 R).inv.hom I)
        = span {_a0} := by
      rw [map_map, ← hcomp, ← map_map, map_chartRingHom_eq_span_singleton, map_span,
        image_singleton]
    rw [comap_ideal_eq_map_appLE (specIdealSheaf I) (p13 I)
        ⟨⊤, isAffineOpen_top $ Sp R⟩ ⟨_, hW⟩
        (le_top.trans_eq (preimage_top $ p13 I).symm)]
    rwa [specIdealSheaf_ideal_top]
  refine ⟨⟨_, hW⟩, _a0, ?_, map_mem_nonZeroDivisors_of_iso (chartSectionsIso I a) $ chartRingHom_mem_nonZeroDivisors I a,
    _i33⟩
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, trivial, hy⟩
end

end FunctorialResolution.Blowup
end
end
-- BEGIN_E2_B03_RECV
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
abbrev tSch (T : MarkedIdealWithBoundary) := T.scheme
abbrev tId (T : MarkedIdealWithBoundary) := T.ideal
abbrev tMu (T : MarkedIdealWithBoundary) := T.mult
abbrev tBd (T : MarkedIdealWithBoundary) := T.boundary
abbrev tMp (T : MarkedIdealWithBoundary) := T.structMap
abbrev tAd (T : MarkedIdealWithBoundary) := T.IsAdmissible
abbrev bLen (T : MarkedIdealWithBoundary) := T.boundary.length
abbrev tISD (T : MarkedIdealWithBoundary) := T.scheme.IdealSheafData
abbrev bcT (T : MarkedIdealWithBoundary) {L : Type} [Field L] (f : T.base →+* L) := T.bc f
abbrev bgetT {T : MarkedIdealWithBoundary} {j : ℕ} (hj : j < T.boundary.length) := T.boundary.get ⟨j, hj⟩
abbrev pbAT (T : MarkedIdealWithBoundary) {Y : Sch} (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme) := T.pbA q h
abbrev pbBT (T : MarkedIdealWithBoundary) {Y : Sch} (q : Y ⟶ Sp T.base) (h : Y ⟶ T.scheme) (E : List Y.IdealSheafData) := T.pbB q h E
section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
abbrev msLen (s : MarkedSequenceOfBlowups p I m E) := s.toSequenceOfBlowups.length
abbrev msAt (s : MarkedSequenceOfBlowups p I m E) := s.toSequenceOfBlowups.schemeAt
abbrev msCtr (s : MarkedSequenceOfBlowups p I m E) := s.toSequenceOfBlowups.center
abbrev msTrS (s : MarkedSequenceOfBlowups p I m E) := s.toSequenceOfBlowups.transitionMapSucc
abbrev mbsLen (s : MarkedBlowupSequenceData p I m E) := s.toBlowupSequenceData.length
abbrev mbsObj (s : MarkedBlowupSequenceData p I m E) := s.toBlowupSequenceData.obj
abbrev mbsCtr (s : MarkedBlowupSequenceData p I m E) := s.toBlowupSequenceData.center
abbrev lastO (s : MarkedBlowupSequenceData p I m E) := s.obj s.length
abbrev lastI (s : MarkedBlowupSequenceData p I m E) := s.ideal s.length
abbrev lastB (s : MarkedBlowupSequenceData p I m E) := s.boundary s.length
abbrev lastP (s : MarkedBlowupSequenceData p I m E) := s.proj s.length
end
end
-- END_E2_B03_RECV
-- BEGIN_E2_PROJ_Bundle03
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
abbrev p14 := @BlowupSequenceData.toSequenceOfBlowups_length
abbrev p23 := @BlowupSequenceData.projectionToBase_zero
abbrev p24 := @BlowupSequenceData.toSequenceOfBlowups_center
abbrev p36 := @BlowupSequenceData.toSequenceOfBlowups_projectionToBase
abbrev p43 := @BlowupSequenceData.projectionToBase_succ
abbrev p50 := @BlowupSequenceData.toSequenceOfBlowups_blowupMorphism
abbrev p54 := @MarkedBlowupSequenceData.ofMarkedSequence
end
-- END_E2_PROJ_Bundle03
-- BEGIN_F2_B03_RECV
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
abbrev tDim (T : MarkedIdealWithBoundary) := T.krullDimSucc
abbrev tWB (T : MarkedIdealWithBoundary) (E' : List T.scheme.IdealSheafData) := T.withBoundary E'
abbrev tBs (T : MarkedIdealWithBoundary) := T.base
abbrev bdIzH {X : Sch} (s : BlowupSequenceData X) := s.isoZero.hom
abbrev msId (s : MarkedSequenceOfBlowups p I m E) := s.ideal
abbrev msBd (s : MarkedSequenceOfBlowups p I m E) := s.boundary
abbrev msPrj (s : MarkedSequenceOfBlowups p I m E) := s.toSequenceOfBlowups.projectionToBase
abbrev mbBd (s : MarkedBlowupSequenceData p I m E) := s.toBlowupSequenceData
abbrev mbMs (s : MarkedBlowupSequenceData p I m E) := s.toMarkedSequenceOfBlowups
abbrev mbSq (s : MarkedBlowupSequenceData p I m E) := s.toMarkedSequenceOfBlowups.toSequenceOfBlowups
abbrev mbId (s : MarkedBlowupSequenceData p I m E) := s.ideal
abbrev mbBy (s : MarkedBlowupSequenceData p I m E) := s.boundary
abbrev mbOb (s : MarkedBlowupSequenceData p I m E) := s.obj
end
-- END_F2_B03_RECV
