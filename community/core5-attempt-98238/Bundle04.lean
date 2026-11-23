import Mathlib
import Bundle00
import Bundle01
import Bundle02
import Bundle03
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace CategoryTheory.Limits Opposite
open FunctorialResolution.Blowup (StrictTransformIsBlowupOfClosedSubscheme affineBlowup exceptionalIdeal exceptionalIdeal_eq_comap isProper_affineBlowup_toSpec specIdealSheaf specIdealSheaf_eq_ofIdealTop strictTransform strictTransformImmersion_eq strictTransformOpens_eq strictTransform_eq_ker)
open TopologicalSpace.Opens (coe_inf isOpen mem_iSup mem_inf)
open Ideal (comap_comap comap_mono eq_of_localization_maximal eq_top_iff_one exists_le_maximal le_radical map_comap_of_surjective map_id map_isPrime_of_surjective map_map map_span mem_bot mem_map_iff_of_surjective mem_map_of_mem mem_quotient_iff_mem mem_radical_iff mem_span_singleton' mem_span_singleton_mul mem_span_singleton_self mk_ker mul_le_inf mul_mem_left mul_mem_mul mul_mem_right span span_eq span_le span_singleton_mul_left_unit span_singleton_pow)
open List (Lex Pairwise cons_lex_cons_iff eraseIdx get length length_append length_cons length_map length_nil map_cons map_nil mem_cons mem_iff_getElem mem_map ofFn pairwise_cons)
open Finset (geomSum_injective geomSum_lt_geomSum_iff_toColex_lt_toColex image_injective mem_image mem_image_of_mem mem_sort sortedLT_sort sum_congr sum_mul)
open Nat (cast_mul le_of_not_lt lt_of_succ_le lt_one_iff lt_succ_self sSup_mem zero_le)
open Set (disjoint_left ext_iff image_congr image_image image_preimage_subset image_singleton image_subset_iff mem_compl_iff mem_inter_iff mem_preimage mem_range_self mem_univ not_subset preimage preimage_mono preimage_univ range range_comp univ)
open IsLocalization (eq_iff_exists isDomain_of_le_nonZeroDivisors isPrime_of_isPrime_disjoint lift_eq map_eq_map_of_map_eq_map map_eq_zero_iff map_nonZeroDivisors_le mem_map_algebraMap_iff nonZeroDivisors_le_comap)
open Fin (lt_def val val_strictMono)
open Polynomial (C_pow monomial monomial_mul_monomial monomial_pow monomial_zero_left)
open SetLike (coe_subset_coe ext' mem_coe)
open Scheme (GSpecIso GlueData IdealSheafData basicOpen basicOpen_appLE basicOpen_le basicOpen_res exists_isAffineOpen_mem isBasis_affineOpens mem_zeroLocus_iff preimage_basicOpen presheaf_map_eq_of_parallel)
open IsPullback (of_horiz_isIso of_isLimit')
open ENat (eq_of_forall_natCast_le_iff ne_top_iff_exists)
open IsAffineOpen (SpecMap_appLE_fromSpec fromSpec isLocalization_stalk isLocalization_stalk' primeIdealOf range_fromSpec)
open Scheme.Hom (appIso_hom appIso_hom' appLE appTop comp_appTop image_top_eq_opensRange ker ker_comp ker_comp_of_isIso ker_eq_bot_of_isIso map_appLE pre preimage_image_eq preimage_top resLE_eq_morphismRestrict stalkMap support_ker surjective)
open RingHom (algebraMap_toAlgebra comp_apply ker_eq_comap_bot mem_ker toAlgebra)
open Algebra (EssFiniteType FiniteType FormallyEtale FormallyUnramified IsIntegral IsSeparable)
open Function (Bijective Surjective comp_def)
open CommRingCat (hom_comp hom_id hom_inv_apply inv_hom_apply ofHom)
open Scheme.IdealSheafData (comap comapIso_hom_fst comap_comp comap_id comap_ideal_eq_map_appLE comap_ideal_eq_span_image comap_mul comap_top ext_of_iSup_eq_top ideal_ofIdeals_le ideal_pow ker_fst_of_isClosedImmersion le_map_comap mem_supportSet_iff mem_support_comap radical_ideal subscheme subschemeι support support_comap support_eq_bot_iff vanishingIdeal vanishingIdeal_support)
open Category (assoc comp_id id_comp)
open CommRingCat.Hom (hom)
open Ideal.Quotient (eq_zero_iff_mem isDomain lift_mk mk mk_surjective)
open Iso (commRingCatIsoToRingEquiv hom_inv_id inv inv_comp_eq inv_hom_id inv_hom_id_assoc refl symm_hom)
open IsOpenImmersion (lift_fac)
open Submonoid (mem_powers mem_powers_iff powers)
open Algebra.FormallyUnramified (iff_isSeparable localization_base of_isLocalization of_restrictScalars of_surjective)
open HomogeneousLocalization (Away val_injective val_mul val_pow)
open Algebra.EssFiniteType (comp of_comp)
open Scheme.Cover (glueMorphisms mkOfCovers)
open TopologicalSpace (Closeds)
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData (ofMarkedSequence toMarkedSequenceOfBlowups)
open Localization (mk_eq_mk_iff mk_mul mk_one_eq_algebraMap r_iff_exists)
open TopCat.Presheaf (algebra_section_stalk germ_res_apply section_ext)
open IsScalarTower (algebraMap_apply of_algebraMap_eq)
open Limits.pullback (condition)
open MorphismProperty.IsStableUnderBaseChange (of_isPullback)
open Iff (mp mpr)
open Scheme.Opens (toScheme ι)
open FunctorialResolution.EmbeddedResolution.MarkedIdealWithBoundary (IsAdmissible bc boundary ideal structMap)
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups (toSequenceOfBlowups)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (center projectionToBase)
section


namespace FunctorialResolution.Blowup


section
variable {A : Type} [CommRing A]
section
variable {W : Sch} (g : W ⟶ Sp A)
def sectionsRingHom (V : Opn W) : A →+* ↥(W.sec V) :=
  ((GSpecIso $ CommRingCat.of A).inv ≫
    appLE g ⊤ V (le_top.trans (preimage_top g).ge)).hom

theorem sectionsRingHom_apply V r :
    sectionsRingHom g V r =
      (appLE g ⊤ V $ le_top.trans (preimage_top g).ge).hom
        ((GSpecIso $ CommRingCat.of A).inv.hom r) := rfl

theorem sectionsRingHom_restrict {V V' : Opn W} (hV : V' ≤ V) (r : A) :
    sectionsRingHom g V' r =
      (W.presheaf.map (homOfLE hV).op).hom (sectionsRingHom g V r) := by
  have key : appLE g ⊤ V' (le_top.trans (preimage_top g).ge) =
      appLE g ⊤ V (le_top.trans (preimage_top g).ge) ≫
        W.presheaf.map (homOfLE hV).op := by simp_all
  exact congrArg
    (fun ph_ : Γ(Sp A, (⊤ : Opn $ Sp A)) ⟶ W.sec V' =>
      ph_.hom $ (GSpecIso $ m10 A).inv.hom r) key
end

theorem localization_mk_one_pow (S : Submonoid A) (x : A)
    (n : ℕ) :
    Localization.mk x (1 : S) ^ n = Localization.mk (x ^ n) (1 : S) := by
  rw [mk_one_eq_algebraMap, mk_one_eq_algebraMap, map_pow]
end

section
variable {R : Type} [CommRing R] (I : Ideal R)
section
variable {W : Sch}
section
variable (g : W ⟶ Sp R)
theorem comap_specIdealSheaf_ideal (V : W.affineOpens) :
    ((specIdealSheaf I).comap g).ideal V = Ideal.map (sectionsRingHom g (V : Opn W)) I := by
  have h1 := comap_ideal_eq_map_appLE (specIdealSheaf I) g
      ⟨⊤, isAffineOpen_top $ Sp R⟩ V
      (le_top.trans (preimage_top g).ge)
  rwa [specIdealSheaf_ideal_top, map_map] at h1

theorem map_sectionsRingHom_restrict {V V' : Opn W} (hV : V' ≤ V) :
    Ideal.map (sectionsRingHom g V') I
      = Ideal.map (W.presheaf.map (homOfLE hV).op).hom (Ideal.map (sectionsRingHom g V) I) := by
  have e : (pMap W (homOfLE hV).op).hom.comp (sectionsRingHom g V) = sectionsRingHom g V' :=
    m48 fun x => sy_ $ sectionsRingHom_restrict g hV x
  rw [map_map, e]
end

section
variable (h : W ⟶ affineBlowup I)
section
variable (b) (V) (hV : V ≤ pre h (affineBlowupChart I b ''ᵁ ⊤))
def chartSectionsRingHom :
    Away (reesGrading I) (reesGenerator I b) →+* ↥(W.sec V) :=
  ((chartSectionsIso I b).hom ≫ appLE h (affineBlowupChart I b ''ᵁ ⊤) V hV).hom

theorem chartSectionsRingHom_apply
    z :
    chartSectionsRingHom I h b V hV z =
      (appLE h (affineBlowupChart I b ''ᵁ ⊤) V hV).hom ((chartSectionsIso I b).hom.hom z) :=
  rfl

theorem chartSectionsRingHom_chartRingHom (r : R) :
    chartSectionsRingHom I h b V hV (chartRingHom I b r) =
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) V r := by
  let _a0 := h ≫ p13 I
  have key : ofHom (chartRingHom I b) ≫ (isoH (chartSectionsIso I b) ≫
        appLE h (affineBlowupChart I b ''ᵁ ⊤) V hV)
      = (GSpecIso $ m10 R).inv ≫
        appLE _a0 ⊤ V
          (le_top.trans (preimage_top _a0).ge) := by
    rw [← assoc, chartRingHom_comp_chartSectionsIso_hom, assoc,
      m91]
  exact congrArg (fun ph_ : m10 R ⟶ W.sec V => ph_.hom r) key
end

theorem chartSectionsRingHom_mul_pow_eq (a : ↥I) (V : Opn W)
    (hV : V ≤ pre h (affineBlowupChart I a ''ᵁ ⊤))
    (z : Away (reesGrading I) $ reesGenerator I a) (n : ℕ) (r : R)
    (hnr : z * chartRingHom I a (a : R) ^ n = chartRingHom I a r) :
    chartSectionsRingHom I h a V hV z * sectionsRingHom (h ≫ AffineBlowup.toSpec I) V (a : R) ^ n
      = sectionsRingHom (h ≫ AffineBlowup.toSpec I) V r := by
  let _a0 := chartRingHom I a a
  have h0 : chartSectionsRingHom I h a V hV (z * _a0 ^ n)
      = chartSectionsRingHom I h a V hV (chartRingHom I a r) := by rw [hnr]
  rwa [map_mul, map_pow (chartSectionsRingHom I h a V hV) _a0 n, chartSectionsRingHom_chartRingHom, chartSectionsRingHom_chartRingHom] at h0

theorem comap_specIdealSheaf_ideal_eq_span (a : ↥I) (V : W.affineOpens)
    (hV : (V : Opn W) ≤ pre h (affineBlowupChart I a ''ᵁ ⊤)) :
    (comap (specIdealSheaf I) $ h ≫ AffineBlowup.toSpec I).ideal V =
      span
        {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : Opn W) (a : R)} := by
  let _a1 := h ≫ AffineBlowup.toSpec I
  let _a0 := sectionsRingHom _a1 V
  have hfac : _a0
      = RingHom.comp (chartSectionsRingHom I h a V hV) (chartRingHom I a) := by
    ext r
    exact sy_ $ chartSectionsRingHom_chartRingHom I h a V hV r
  have h2 : Ideal.map _a0 I
      = span
          {chartSectionsRingHom I h a V hV $ chartRingHom I a a} := by
    rw [hfac, ← map_map, map_chartRingHom_eq_span_singleton I a, map_span, image_singleton]
  rw [comap_specIdealSheaf_ideal I _a1 V, h2,
    chartSectionsRingHom_chartRingHom I h a V hV a]

theorem basicOpen_chartSectionsRingHom (c : ↥I) (V : Opn W)
    (hV : V ≤ pre h (affineBlowupChart I c ''ᵁ ⊤))
    (z : Away (reesGrading I) $ reesGenerator I c) :
    basicOpen W (chartSectionsRingHom I h c V hV z)
      = V ⊓ h ⁻¹ᵁ (basicOpen (affineBlowup I) $ (chartSectionsIso I c).hom.hom z) := by
  rw [chartSectionsRingHom_apply]
  exact basicOpen_appLE h V (affineBlowupChart I c ''ᵁ ⊤) hV
    ((chartSectionsIso I c).hom.hom z)
end
end

private theorem val_chartRingHom (a : ↥I) (r : R) :
    (chartRingHom I a r).val =
      Localization.mk ((reesDegreeZeroEquiv I r : ↥(reesGrading I 0)) : ↥(reesAlgebra I))
        (1 : ↥(powers $ reesGenerator I a)) := by
  rw [chartRingHom_apply]
  rfl

theorem exists_mul_pow_eq_chartRingHom (a : ↥I)
    (z : Away (reesGrading I) $ reesGenerator I a) :
    ∃ n r, z * chartRingHom I a (a : R) ^ n = chartRingHom I a r := by
  obtain ⟨k, hk⟩ := z.den_mem
  obtain ⟨s, hs, hnum⟩ := mp_ (mem_reesGrading_iff_monomial I z.deg z.num) z.num_mem_deg
  have hdencoe : ((z.den : (reesAlgebra I)) : Polynomial R)
      = monomial k ((a : R) ^ k) := by
    rw [← hk]
    simp [reesGenerator_coe, monomial_pow]
  by_cases hik : z.deg = k
  refine ⟨k, s, ?_⟩
  apply val_injective
  let _a0 := reesGrading I 0
  have key : z.num * ((reesDegreeZeroEquiv I (a : R) : _a0) : (reesAlgebra I)) ^ k
      = z.den * ((reesDegreeZeroEquiv I s : _a0) : (reesAlgebra I)) := by
    apply m26
    push_cast
    rw [hnum, hdencoe, hik, reesDegreeZeroEquiv_coe_coe, reesDegreeZeroEquiv_coe_coe,
      ← C_pow, ← monomial_zero_left, ← monomial_zero_left,
      monomial_mul_monomial, monomial_mul_monomial, mul_comm]
  simp only [val_mul, val_pow,
    z.eq_num_div_den, val_chartRingHom, localization_mk_one_pow, mk_mul, mul_one]
  rw [mk_eq_mk_iff, r_iff_exists]
  exact ⟨1, by simpa using key⟩
  refine ⟨0, 0, ?_⟩
  apply val_injective
  have hak := by
    have h0 := mp_ (mem_reesGrading_iff_coeff I z.deg z.den) z.den_mem_deg k $ m113 hik
    rw [hdencoe] at h0
    simpa using h0
  have hden0 : (z.den : (reesAlgebra I)) = 0 := by
    apply m26
    rw [hdencoe, hak]
    simp
  simp only [val_mul, val_pow,
    z.eq_num_div_den, val_chartRingHom, localization_mk_one_pow, mk_mul, mul_one]
  rw [mk_eq_mk_iff, r_iff_exists]
  exact ⟨⟨0, ⟨k, tr_ hk hden0⟩⟩, by simp [hden0]⟩

theorem affineBlowupChart_preimage_basicOpen
    c z :
    affineBlowupChart I c ⁻¹ᵁ
        (basicOpen (affineBlowup I) $ (chartSectionsIso I c).hom.hom z)
      = PrimeSpectrum.basicOpen z := by
  let _a1 := Away (reesGrading I) $ reesGenerator I c
  let _c0 := m10 _a1
  have e : (⊤ : Opn $ Spec _c0)
      ≤ affineBlowupChart I c ⁻¹ᵁ (affineBlowupChart I c ''ᵁ ⊤) := by simp_all
  have happ : appLE (affineBlowupChart I c) (affineBlowupChart I c ''ᵁ ⊤) ⊤ e
      = ((affineBlowupChart I c).appIso ⊤).hom := by
    rw [appIso_hom]
    rfl
  have hiso : (((affineBlowupChart I c).appIso ⊤).hom).hom ((chartSectionsIso I c).hom.hom z)
      = (GSpecIso _c0).inv.hom z := by
    rw [chartSectionsIso_hom_apply]
    exact congrArg
      (fun ph_ : Γ(Spec _c0, ⊤) ⟶
          Γ(Spec _c0, ⊤) =>
        ph_.hom $ (GSpecIso _c0).inv.hom z)
      ((affineBlowupChart I c).appIso ⊤).inv_hom_id
  have h1 :=
    basicOpen_appLE (affineBlowupChart I c) ⊤ (affineBlowupChart I c ''ᵁ ⊤) e
      ((chartSectionsIso I c).hom.hom z)
  rw [happ, hiso, basicOpen_eq_of_affine (R := m10 _a1) z, top_inf_eq] at h1
  exact sy_ h1

theorem exists_mem_opensRange_affineBlowupChart
    (p : ↥(affineBlowup I)) :
    ∃ c : ↥I, p ∈ (affineBlowupChart I c).opensRange := by
  have hcov : (⨆ c : I, (affineBlowupChart I c).opensRange) = ⊤ := by
    simp [opensRange_affineBlowupChart_eq_basicOpen]
    exact iSup_proj_basicOpen_reesGenerator_eq_top I
  have hp : p ∈ (⨆ c : I, (affineBlowupChart I c).opensRange) := by
    rw [hcov]
    trivial
  simpa using hp

theorem exists_chart_affineOpen_mem_nonZeroDivisors
    {W : Sch} (h : W ⟶ affineBlowup I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor $ comap (specIdealSheaf I) $ h ≫ AffineBlowup.toSpec I)
    (w : ↥W) :
    ∃ (a : ↥I) (V : W.affineOpens), w ∈ (V : Opn W) ∧
      (V : Opn W) ≤ h.pre (affineBlowupChart I a ''ᵁ ⊤) ∧
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : Opn W) (a : R) ∈
        nonZeroDivisors ↥(W.sec (V : Opn W)) := by
  let _c0 := h ≫ p13 I
  obtain ⟨a, ha⟩ := exists_mem_opensRange_affineBlowupChart I $ bsM h w
  have hwU0 : w ∈ preU h (affineBlowupChart I a ''ᵁ ⊤) := by simp_all
  obtain ⟨U, c, hwU, hcnzd, hideal⟩ := hcart w
  have hUaff := U.2
  obtain ⟨t, htle, hwt⟩ :=
    hUaff.exists_basicOpen_le (V := preU h $ affineBlowupChart I a ''ᵁ ⊤) ⟨w, hwU0⟩ hwU
  let _m0 := Γ(W, bOpn W t)
  have := hUaff.isLocalization_basicOpen t
  let _a2 := sectionsRingHom _c0 $ bOpn W t
  let _a3 := xSec W U
  have hres : _a2
      = RingHom.comp (algebraMap (_a3) (_m0))
          (sectionsRingHom _c0 U) := by
    ext r
    exact sectionsRingHom_restrict _c0 (W.basicOpen_le t) r
  have hmapU := hideal
  rw [comap_specIdealSheaf_ideal I _c0 U] at hmapU
  let _a0 := algebraMap (_a3) (_m0) c
  have hmapV : Ideal.map _a2 I
      = span {_a0} := by
    rw [hres, ← map_map, hmapU, map_span, image_singleton]
  have e1 :=
    comap_specIdealSheaf_ideal I _c0 ⟨bOpn W t, hUaff.basicOpen t⟩
  have e2 :=
    comap_specIdealSheaf_ideal_eq_span I h a ⟨bOpn W t, hUaff.basicOpen t⟩ htle
  have hspan :=
    st_ hmapV $ st_ e1 e2
  let _a1 := sectionsRingHom _c0 (bOpn W t) a
  have hmem2 : _a0
      ∈ span {_a1} := by
    rw [← hspan]
    exact mem_span_singleton_self _
  obtain ⟨d, hd⟩ := mp_ mem_span_singleton' hmem2
  have hcnzd' :=
    nonZeroDivisors_le_comap (powers t)
      _m0 hcnzd
  have hdnzd : d * _a1
      ∈ nonZeroDivisors _m0 := by
    rwa [hd]
  exact ⟨a, ⟨bOpn W t, hUaff.basicOpen t⟩, hwt, htle,
    (mp_ mul_mem_nonZeroDivisors hdnzd).2⟩

theorem isLocalizationElem_eq_chartFraction
    c a :
    HomogeneousLocalization.Away.isLocalizationElem
        (reesGenerator_mem_reesGrading I c) (reesGenerator_mem_reesGrading I a)
      = chartFraction I c a := by
  apply val_injective
  rw [chartFraction_eq_mk]
  simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.val_mk, pow_one]

theorem basicOpen_chartFraction_le_opensRange
    (c a : ↥I) :
    basicOpen (affineBlowup I) ((chartSectionsIso I c).hom.hom (chartFraction I c a))
      ≤ (affineBlowupChart I a).opensRange := by
  have hpre : affineBlowupChart I c ⁻¹ᵁ (affineBlowupChart I a).opensRange
      = PrimeSpectrum.basicOpen (chartFraction I c a) := by
    rw [opensRange_affineBlowupChart_eq_basicOpen, affineBlowupChart_eq_awayio, ← isLocalizationElem_eq_chartFraction I c a]
    exact Proj.awayι_preimage_basicOpen (reesGrading I) (reesGenerator_mem_reesGrading I c) m176
      (reesGenerator_mem_reesGrading I a) m176
  intro p hp
  let _a0 := bOpn (affineBlowup I) $ (chartSectionsIso I c).hom.hom $ chartFraction I c a
  have hsub : _a0
      ≤ affineBlowupChart I c ''ᵁ ⊤ := basicOpen_le _ _
  obtain ⟨q, -, hq⟩ := hsub hp
  rw [← hq] at hp
  have hq2 : q ∈ affineBlowupChart I c ⁻¹ᵁ
      _a0 := hp
  rw [affineBlowupChart_preimage_basicOpen, ← hpre] at hq2
  rwa [← hq]
end

private theorem restrict_basicOpen_mem_nonZeroDivisors {W : Sch} {U : Opn W}
    (hU : IsAffineOpen U) (r : ↥(W.sec U)) {s : ↥(W.sec U)} (hs : s ∈ nonZeroDivisors ↥(W.sec U))
    (hle : basicOpen W r ≤ U) :
    (W.presheaf.map (homOfLE hle).op).hom s ∈ nonZeroDivisors ↥Γ(W, basicOpen W r) := by
  have := hU.isLocalization_basicOpen r
  exact nonZeroDivisors_le_comap (powers r)
    Γ(W, bOpn W r) hs

def openCoverBySpecOfIsAffineOpen {W : Sch} (VV : ↥W → Opn W)
    (hVaff : ∀ w : ↥W, IsAffineOpen $ VV w) (hmem : ∀ w : ↥W, w ∈ VV w) : W.OpenCover :=
  mkOfCovers ↥W (fun w => Spec Γ(W, VV w)) (fun w => (hVaff w).fromSpec)
    (fun x => by
      have hx : x ∈ range ((hVaff x).fromSpec).base := by
        rw [(hVaff x).range_fromSpec]
        exact hmem x
      obtain ⟨y, hy⟩ := hx
      exact ⟨x, y, hy⟩)
    (fun w => inferInstance)

theorem mem_nonZeroDivisors_of_span_singleton_eq {B : Type} [CommRing B] {s t : B}
    (hs : s ∈ nonZeroDivisors B)
    (hst : span ({s} : Set B) = span ({t} : Set B)) :
    t ∈ nonZeroDivisors B := by
  obtain ⟨hs1, hs2⟩ := mp_ mem_nonZeroDivisors_iff hs
  have h1 : t ∈ span ({s} : Set B) := by
    rw [hst]
    exact mem_span_singleton_self t
  have h2 : s ∈ span ({t} : Set B) := by
    rw [← hst]
    exact mem_span_singleton_self s
  obtain ⟨u, hu⟩ := mp_ mem_span_singleton' h1
  obtain ⟨v, hv⟩ := mp_ mem_span_singleton' h2
  have h3 : v * (u * s) = s := by rw [hu, hv]
  have hss : s * (1 - v * u) = 0 := by linear_combination -h3
  have hvu : v * u = 1 := by linear_combination -hs1 _ hss
  have key : ∀ y, t * y = 0 → y = 0 := by
    intro y hy
    have h5 : s * (u * y) = 0 := by linear_combination hy + y * hu
    linear_combination v * hs1 _ h5 - y * hvu
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun y hy => key y (by rw [mul_comm]; exact hy)⟩

section
variable {R : Type} [CommRing R]
section
variable (I : Ideal R) {W : Sch} (h : W ⟶ affineBlowup I) (hcart : IsLocallyGeneratedByNonZeroDivisor (comap (specIdealSheaf I) (h ≫ AffineBlowup.toSpec I)))
include hcart
theorem mem_opensRange_affineBlowupChart_of_ideal_eq_span
    (w : ↥W) (a : ↥I)
    (hex : ∃ V : W.affineOpens, w ∈ (V : Opn W) ∧
      (comap (specIdealSheaf I) $ h ≫ AffineBlowup.toSpec I).ideal V =
        span
          {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : Opn W) (a : R)}) :
    h.base w ∈ (affineBlowupChart I a).opensRange := by
  let _c0 := h ≫ AffineBlowup.toSpec I
  obtain ⟨V, hwV, hVspan⟩ := hex
  obtain ⟨c, hc⟩ := exists_mem_opensRange_affineBlowupChart I $ bsM h w
  obtain ⟨Uaff, g, hwU, hgnzd, hUspan⟩ := hcart w
  let _m0 := (V ⊓ preU h (affineBlowupChart I c ''ᵁ ⊤) : Opn W)
  have hwpre : w ∈ _m0 := by
    refine ⟨hwV, ?_⟩
    rwa [image_top_eq_opensRange]
  obtain ⟨r, hrle, hwr⟩ := Uaff.2.exists_basicOpen_le
    (⟨w, hwpre⟩ : _m0) hwU
  have hbaff := Uaff.2.basicOpen r
  have hVV := le_trans hrle inf_le_left
  have hVc := le_trans hrle inf_le_right
  have hVU := W.basicOpen_le r
  have hmapSpan : Ideal.map (sectionsRingHom _c0 $ bOpn W r) I
      = span {sectionsRingHom _c0 (bOpn W r) c} := by
    have e1 := comap_specIdealSheaf_ideal I _c0
      (⟨bOpn W r, hbaff⟩ : affO W)
    have e2 := comap_specIdealSheaf_ideal_eq_span I h c
      (⟨bOpn W r, hbaff⟩ : affO W) hVc
    exact st_ e1 e2
  have hmapPow : Ideal.map (sectionsRingHom _c0 $ bOpn W r) I
      = span {sectionsRingHom _c0 (bOpn W r) a} := by
    rw [map_sectionsRingHom_restrict I _c0 hVV, (comap_specIdealSheaf_ideal I _c0 V).symm.trans hVspan, map_span,
      image_singleton, ← sectionsRingHom_restrict _c0 hVV a]
  have hmapEq : Ideal.map (sectionsRingHom _c0 $ bOpn W r) I
      = span {(pMap W (homOfLE hVU).op).hom g} := by
    rw [map_sectionsRingHom_restrict I _c0 hVU, (comap_specIdealSheaf_ideal I _c0 Uaff).symm.trans hUspan, map_span,
      image_singleton]
  have hkey : sectionsRingHom _c0 (bOpn W r) a
      = chartSectionsRingHom I h c (bOpn W r) hVc (chartFraction I c a) *
        sectionsRingHom _c0 (bOpn W r) c := by
    rw [← chartSectionsRingHom_chartRingHom I h c (bOpn W r) hVc a,
      ← chartSectionsRingHom_chartRingHom I h c (bOpn W r) hVc c, ← map_mul,
      chartRingHom_coe_eq_chartFraction_mul I c a]
  have hcmem : sectionsRingHom _c0 (bOpn W r) c
      ∈ span {sectionsRingHom _c0 (bOpn W r) a} := by simp_all
  obtain ⟨d, hd⟩ := mp_ mem_span_singleton' hcmem
  have h1 : sectionsRingHom _c0 (bOpn W r) c *
      (1 - d * chartSectionsRingHom I h c (bOpn W r) hVc (chartFraction I c a)) = 0 := by
    linear_combination -hd + d * hkey
  have h2 := an1 (mp_ mem_nonZeroDivisors_iff $ mem_nonZeroDivisors_of_span_singleton_eq (restrict_basicOpen_mem_nonZeroDivisors Uaff.2 r hgnzd hVU) $ st_ hmapEq hmapSpan) _ h1
  let _m1 := chartSectionsRingHom I h c (bOpn W r) hVc $ chartFraction I c a
  have hunit : IsUnit _m1 :=
    ⟨⟨chartSectionsRingHom I h c (bOpn W r) hVc $ chartFraction I c a, d,
      by linear_combination -h2, by linear_combination -h2⟩, rfl⟩
  have hmem : w ∈ basicOpen W _m1 := by
    rwa [W.basicOpen_of_isUnit hunit]
  let hw := hmem
  rw [basicOpen_chartSectionsRingHom I h c (basicOpen W r) hVc $ chartFraction I c a] at hw
  exact basicOpen_chartFraction_le_opensRange I c a hw.2

theorem mem_preimage_affineBlowupChart_iff
    (a : ↥I) (w : ↥W) :
    w ∈ pre h (affineBlowupChart I a ''ᵁ ⊤) ↔
      ∃ V : W.affineOpens, w ∈ (V : Opn W) ∧
        (comap (specIdealSheaf I) $ h ≫ AffineBlowup.toSpec I).ideal V =
          span {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : Opn W) (a : R)} := by
  constructor
  intro hw
  obtain ⟨v, hv, hwV, hVle⟩ :=
    (W.isBasis_affineOpens).exists_subset_of_mem_open hw
      (isOpen $ preU h $ affineBlowupChart I a ''ᵁ ⊤)
  obtain ⟨V, hVmem, rfl⟩ := hv
  exact ⟨⟨V, hVmem⟩, hwV, comap_specIdealSheaf_ideal_eq_span I h a ⟨V, hVmem⟩ $ mp_ coe_subset_coe hVle⟩
  intro hex
  have hmem := mem_opensRange_affineBlowupChart_of_ideal_eq_span I h hcart w a hex
  rwa [image_top_eq_opensRange]
end

section
variable {I : Ideal R} {W : Sch} (h1_ h2_ : W ⟶ affineBlowup I) (he : h1_ ≫ AffineBlowup.toSpec I = h2_ ≫ AffineBlowup.toSpec I) (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h1_ ≫ AffineBlowup.toSpec I)))
include he hcart
theorem preimage_affineBlowupChart_eq_of_toSpec_eq
    (a : ↥I) :
    pre h1_ (affineBlowupChart I a ''ᵁ ⊤) = pre h2_ (affineBlowupChart I a ''ᵁ ⊤) := by
  have hcart2_ : IsLocallyGeneratedByNonZeroDivisor $ cmI (specIdealSheaf I) $ h2_ ≫ p13 I := by simp_all
  apply m55
  apply Set.ext
  intro w
  have e1 := mem_preimage_affineBlowupChart_iff I h1_ hcart a w
  rw [he] at e1
  exact e1.trans (mem_preimage_affineBlowupChart_iff I h2_ hcart2_ a w).symm

theorem fromSpec_comp_eq_of_toSpec_eq
    (a : ↥I) (V : Opn W) (hVaff : IsAffineOpen V)
    (hle : V ≤ pre h1_ (affineBlowupChart I a ''ᵁ ⊤))
    (hnzd : sectionsRingHom (h1_ ≫ AffineBlowup.toSpec I) V (a : R) ∈
      nonZeroDivisors ↥(W.sec V)) :
    hVaff.fromSpec ≫ h1_ = hVaff.fromSpec ≫ h2_ := by
  let _c0 := affineBlowupChart I a ''ᵁ ⊤
  have hle2_ : V ≤ pre h2_ _c0 := by
    rwa [← preimage_affineBlowupChart_eq_of_toSpec_eq h1_ h2_ he hcart a]
  have hTaff :=
    (isAffineOpen_top _).image_of_isOpenImmersion $ affineBlowupChart I a
  have hcp : chartSectionsRingHom I h1_ a V hle = chartSectionsRingHom I h2_ a V hle2_ := by
    refine m48 fun z => ?_
    obtain ⟨n, r, hnr⟩ := exists_mul_pow_eq_chartRingHom I a z
    have k2 := chartSectionsRingHom_mul_pow_eq I h2_ a V hle2_ z n r hnr
    rw [← he] at k2
    exact mp_ (mul_cancel_right_mem_nonZeroDivisors $ pow_mem hnzd n) $ tr_ (chartSectionsRingHom_mul_pow_eq I h1_ a V hle z n r hnr) k2.symm
  have happ : appLE h1_ _c0 V hle
      = appLE h2_ _c0 V hle2_ := by
    calc h1_.appLE _c0 V hle
        = isoI (chartSectionsIso I a) ≫ isoH (chartSectionsIso I a) ≫
            appLE h1_ _c0 V hle := by
          rw [← assoc, inv_hom_id, id_comp]
      _ = isoI (chartSectionsIso I a) ≫ isoH (chartSectionsIso I a) ≫
            appLE h2_ _c0 V hle2_ := by rw [CommRingCat.hom_ext hcp]
      _ = appLE h2_ _c0 V hle2_ := by
          rw [← assoc, inv_hom_id, id_comp]
  rw [← SpecMap_appLE_fromSpec h1_ hTaff hVaff hle, ← SpecMap_appLE_fromSpec h2_ hTaff hVaff hle2_, happ]

theorem affineBlowup_hom_ext :
    h1_ = h2_ := by
  classical
  choose aa VV hmem hle hnzd using exists_chart_affineOpen_mem_nonZeroDivisors I h1_ hcart
  exact (openCoverBySpecOfIsAffineOpen (fun w => VV w) (fun w => (VV w).2) hmem).hom_ext
    h1_ h2_ fun w => fromSpec_comp_eq_of_toSpec_eq h1_ h2_ he hcart (aa w) (VV w) (VV w).2 (hle w) $ hnzd w
end
end

end FunctorialResolution.Blowup
end
section
universe v


namespace FunctorialResolution.Blowup

theorem eq_span_inv_of_map_eq_span {R S : CRC} (ph_ : R ⟶ S) [IsIso ph_]
    (J : Ideal R) (s : S) (h : J.map ph_.hom = span {s}) :
    J = span {(CategoryTheory.inv ph_).hom s} := by
  have hcomp : (m83 ph_).hom.comp ph_.hom = m99 R := by
    ext x
    simp
  calc J = (J.map ph_.hom).map (m83 ph_).hom := by
        rw [map_map, hcomp, map_id]
    _ = (span {s}).map (m83 ph_).hom := by rw [h]
    _ = span {(m83 ph_).hom s} := by rw [map_span, image_singleton]

theorem isIso_appLE_of_image_eq {X Y : Sch} (f : X ⟶ Y) [IsOpenImmersion f]
    {W : Opn X} {V : Opn Y} (hV : f.im W = V) (e : W ≤ pre f V) :
    IsIso $ appLE f V W e := by
  subst hV
  rw [← appIso_hom']
  infer_instance

private theorem exists_affineOpen_mem_le {X : Sch} (x : X) (W : Opn X) (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ (V : Opn X) ∧ (V : Opn X) ≤ W := by
  obtain ⟨Vs, hVs, hxV, hVW⟩ :=
    (isBasis_affineOpens X).exists_subset_of_mem_open
      (show x ∈ W from hx) W.isOpen
  obtain ⟨V, hVmem, rfl⟩ := hVs
  exact ⟨⟨V, hVmem⟩, hxV, fun y hy => hVW hy⟩

theorem IsLocallyGeneratedByNonZeroDivisor.comap_of_isOpenImmersion {X U : Sch}
    {I : ISD X} (hI : IsLocallyGeneratedByNonZeroDivisor I) (f : U ⟶ X) [IsOpenImmersion f] :
    IsLocallyGeneratedByNonZeroDivisor $ I.comap f := by
  intro x
  obtain ⟨V, g, hxV, hg, hVg⟩ := hI $ f.base x
  have hVa := V.2
  obtain ⟨W, hxW, hWle⟩ := exists_affineOpen_mem_le x (f.pre V) hxV
  let _a1 := f.im W
  have hximg : f.base x ∈ _a1 := ⟨x, hxW, rfl⟩
  obtain ⟨r, hr1, hr2⟩ := hVa.exists_basicOpen_le (⟨f.base x, hximg⟩ : _a1) hxV
  have hW'le : f.pre (X.basicOpen r) ≤ W := by
    rw [← preimage_image_eq f W]
    exact fun y hy => hr1 hy
  let _m0 := f.appLE V W hWle
  have hbas : U.basicOpen (_m0.hom r)
      = f.pre (X.basicOpen r) := by
    rw [show _m0.hom r
          = (pMap U (homOfLE hWle).op).hom ((f.app V).hom r) from rfl,
      basicOpen_res, ← preimage_basicOpen]
    exact inf_eq_right.mpr hW'le
  have hW'aff : IsAffineOpen $ f.pre $ X.basicOpen r := by
    rw [← hbas]
    exact W.2.basicOpen _
  have hBrange : X.basicOpen r ≤ f.opensRange := by
    intro y hy
    obtain ⟨z, _, hz⟩ := hr1 hy
    exact ⟨z, hz⟩
  have :=
    isIso_appLE_of_image_eq f ((f.image_preimage_eq_opensRange_inf $ X.basicOpen r).trans $ inf_eq_right.mpr hBrange) le_rfl
  let _a0 := pMap X (homOfLE $ X.basicOpen_le r).op
  have e1 : (I.ideal V).map _a0.hom
      = I.ideal ⟨X.basicOpen r, hVa.basicOpen r⟩ := I.map_ideal_basicOpen V r
  rw [hVg, map_span, image_singleton] at e1
  refine ⟨⟨f.pre $ X.basicOpen r, hW'aff⟩,
    (f.appLE (X.basicOpen r) (f.pre $ X.basicOpen r) le_rfl).hom
      (_a0.hom g), hr2, ?_, ?_⟩
  refine map_mem_nonZeroDivisors_of_iso
    (asIso $ f.appLE (X.basicOpen r) (f.pre $ X.basicOpen r) le_rfl) ?_
  have := hVa.isLocalization_basicOpen r
  exact nonZeroDivisors_le_comap (powers r) Γ(X, X.basicOpen r) hg
  have hmap := I.comap_ideal_eq_map_appLE f ⟨X.basicOpen r, hVa.basicOpen r⟩
    ⟨f.pre $ X.basicOpen r, hW'aff⟩ le_rfl
  rwa [← e1, map_span, image_singleton] at hmap

theorem IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover {X : Sch} (I : ISD X)
    {ι : Type v} (U : ι → Sch) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion $ f i]
    (hcover : ∀ x : X, ∃ i, x ∈ range ⇑(f i).base)
    (h : ∀ i, IsLocallyGeneratedByNonZeroDivisor $ comap I $ f i) :
    IsLocallyGeneratedByNonZeroDivisor I := by
  intro x
  obtain ⟨i, u, hu⟩ := hcover x
  obtain ⟨W, s, hxW, hs, hWs⟩ := h i u
  have hVaff : IsAffineOpen $ f i ''ᵁ (W : Opn $ U i) := W.2.image_of_isOpenImmersion $ f i
  have e : (W : Opn $ U i) ≤ (f i) ⁻¹ᵁ (f i ''ᵁ (W : Opn $ U i)) := (preimage_image_eq (f i) _).ge
  have :=
    isIso_appLE_of_image_eq (f i) rfl e
  have key := I.comap_ideal_eq_map_appLE (f i) ⟨f i ''ᵁ (W : Opn $ U i), hVaff⟩ W e
  rw [hWs] at key
  exact ⟨⟨f i ''ᵁ (W : Opn $ U i), hVaff⟩,
    (m83 $ appLE (f i) (f i ''ᵁ (W : Opn $ U i)) (W : Opn $ U i) e).hom s,
    ⟨u, hxW, hu⟩, map_mem_nonZeroDivisors_of_iso (asIso $ m83 $ appLE (f i) (f i ''ᵁ (W : Opn $ U i)) (W : Opn $ U i) e) hs, eq_span_inv_of_map_eq_span _ _ _ key.symm⟩

theorem IsBlowupAlongIdealSheaf.restrict {X X' : Sch} {pi_ : X' ⟶ X} {I : ISD X}
    (h : IsBlowupAlongIdealSheaf pi_ I) (U : Opn X) :
    IsBlowupAlongIdealSheaf (pi_.mr U) $ comap I U.i := by
  have key : ∀ {W : Sch} (g : W ⟶ oSch U),
      comap (comap I U.i) g = comap I (g ≫ ι U) := by simp_all
  constructor
  rw [key $ mrU pi_ U, morphismRestrict_ι, comap_comp]
  exact h.1.comap_of_isOpenImmersion (preU pi_ U).i
  intro W g hg
  rw [key g] at hg
  obtain ⟨k, hk, hk'⟩ := an2 h W (g ≫ opI U) hg
  have hrange : range k.base ⊆ range (preU pi_ U).ib := by
    rw [q1]
    rintro _ ⟨w, rfl⟩
    show bsM pi_ (bsM k w) ∈ U
    have h1 : bsM (k ≫ pi_) w = bsM (g ≫ opI U) w := by rw [hk]
    have h2 : bsM pi_ (bsM k w) = opIb U (bsM g w) := h1
    rw [h2]
    exact (bsM g w).2
  refine ⟨m43 (preU pi_ U).i k hrange, ?_, ?_⟩
  show m43 (preU pi_ U).i k hrange ≫ mrU pi_ U = g
  rw [← cancel_mono U.i, assoc, morphismRestrict_ι, ← assoc,
    lift_fac]
  exact hk
  intro y hy
  rw [← cancel_mono (preU pi_ U).i, lift_fac]
  refine hk' _ ?_
  show (y ≫ opI (preU pi_ U)) ≫ pi_ = g ≫ opI U
  rw [assoc, ← morphismRestrict_ι, ← assoc, hy]

theorem exists_pullback_fst_base_eq {W U X : Sch} (g : W ⟶ X) (f : U ⟶ X)
    [IsOpenImmersion f] (w : W) (hw : g.base w ∈ range ⇑f.base) :
    ∃ z : ↥(pullback g f), (pullback.fst g f).base z = w := by
  let _m0 := pre g f.opensRange
  let _a1 := opI _m0 ≫ g
  have hrange : range _a1.base ⊆ range f.base := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  let _a0 := m43 f _a1 hrange
  have hl : _a0 ≫ f
      = _a1 := lift_fac _ _ _
  have hm := pullback.lift_fst _m0.i
    _a0 hl.symm
  refine ⟨bsM (pullback.lift _m0.i
    _a0 hl.symm)
      ⟨w, show w ∈ pre g f.opensRange from hw⟩, ?_⟩
  have h3 := congrArg (fun t : oSch _m0 ⟶ W => bsM t
    ⟨w, show w ∈ pre g f.opensRange from hw⟩) hm
  exact h3

noncomputable def pullbackOpenCoverOfCovers {X W : Sch} {ι : Type v} (U : ι → Sch)
    (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion $ f i]
    (hcover : ∀ x : X, ∃ i, x ∈ range ⇑(f i).base) (g : W ⟶ X) : W.OpenCover :=
  mkOfCovers ι (fun i => pullback g $ f i) (fun i => pullback.fst g $ f i)
    (fun w => by
      obtain ⟨i, hi⟩ := hcover $ g.base w
      obtain ⟨z, hz⟩ := exists_pullback_fst_base_eq g (f i) w hi
      exact ⟨i, z, hz⟩)
    (fun i => inferInstance)

section
variable {X W T : Sch} {ι : Type v} (U : ι → Sch) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hcover : ∀ x : X, ∃ i, x ∈ range ⇑(f i).base) (g : W ⟶ X)
include hcover
theorem hom_ext_of_isOpenImmersion_cover {a b : W ⟶ T}
    (h : ∀ i, pullback.fst g (f i) ≫ a = pullback.fst g (f i) ≫ b) : a = b := by
  exact Scheme.Cover.hom_ext (pullbackOpenCoverOfCovers U f hcover g) a b h

theorem exists_hom_of_isOpenImmersion_cover
    (k : ∀ i, pullback g (f i) ⟶ T)
    (hk : ∀ i j, pullback.fst (pullback.fst g $ f i) (pullback.fst g $ f j) ≫ k i
        = pullback.snd (pullback.fst g $ f i) (pullback.fst g $ f j) ≫ k j) :
    ∃ ph_ : W ⟶ T, ∀ i, pullback.fst g (f i) ≫ ph_ = k i := by
  have hk' :=
    fun i j => hk i j
  let _a0 := pullbackOpenCoverOfCovers U f hcover g
  exact ⟨glueMorphisms _a0 k hk', fun i => Scheme.Cover.ι_glueMorphisms _a0 k hk' i⟩
end

theorem eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover {X X' T : Sch} (pi_ : X' ⟶ X)
    (I : ISD X)
    {ι : Type v} (U : ι → Sch) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion $ f i]
    (hcover : ∀ x : X, ∃ i, x ∈ range ⇑(f i).base)
    (h : ∀ i, IsBlowupAlongIdealSheaf (pullback.snd pi_ $ f i) $ comap I $ f i)
    {a b : T ⟶ X'} (hab : a ≫ pi_ = b ≫ pi_) (hc : IsLocallyGeneratedByNonZeroDivisor $ comap I $ a ≫ pi_) :
    a = b := by
  let _a2 := a ≫ pi_
  refine hom_ext_of_isOpenImmersion_cover U f hcover _a2 fun i => ?_
  let _a0 := pullback.snd _a2 $ f i
  let _a1 := pullback.fst _a2 $ f i
  have hcond : _a1 ≫ _a2 = _a0 ≫ f i :=
    pullback.condition
  have ha' : (_a1 ≫ a) ≫ pi_ = _a0 ≫ f i := by
    rwa [assoc]
  have hb' : (_a1 ≫ b) ≫ pi_ = _a0 ≫ f i := by
    rwa [assoc, ← hab]
  have hEC : IsLocallyGeneratedByNonZeroDivisor $ comap (cmI I $ f i) _a0 := by
    rw [← comap_comp, ← hcond, comap_comp]
    exact hc.comap_of_isOpenImmersion _
  rw [← pullback.lift_fst (_a1 ≫ a) _a0 ha', ← pullback.lift_fst (_a1 ≫ b) _a0 hb', (h i).hom_ext_of_comp_eq hEC (pullback.lift_snd (_a1 ≫ a) _a0 ha') $ pullback.lift_snd (_a1 ≫ b) _a0 hb']

theorem IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover {X X' : Sch} (pi_ : X' ⟶ X)
    (I : ISD X) {ι : Type v} (U : ι → Sch) (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion $ f i]
    (hcover : ∀ x : X, ∃ i, x ∈ range ⇑(f i).base)
    (h : ∀ i, IsBlowupAlongIdealSheaf (pullback.snd pi_ $ f i) $ comap I $ f i) :
    IsBlowupAlongIdealSheaf pi_ I := by
  constructor
  refine IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover (cmI I pi_) (fun i => pullback pi_ $ f i)
    (fun i => pullback.fst pi_ $ f i) (fun x' => ?_) ?_
  obtain ⟨i, hi⟩ := hcover $ bsM pi_ x'
  obtain ⟨z, hz⟩ := exists_pullback_fst_base_eq pi_ (f i) x' hi
  exact ⟨i, z, hz⟩
  intro i
  have hq : comap (cmI I pi_) (pullback.fst pi_ $ f i)
      = comap (cmI I $ f i) (pullback.snd pi_ $ f i) := by
    rw [← comap_comp, ← comap_comp,
      pullback.condition]
  rw [hq]
  exact an1 $ h i
  intro W g hg
  have hEC : ∀ i, IsLocallyGeneratedByNonZeroDivisor $ comap (cmI I $ f i) $ pullback.snd g $ f i := by
    intro i
    have hq : comap (cmI I $ f i) (pullback.snd g $ f i)
        = comap (cmI I g) (pullback.fst g $ f i) := by
      rw [← comap_comp, ← comap_comp,
        pullback.condition]
    rw [hq]
    exact hg.comap_of_isOpenImmersion _
  choose k hk1 _ using fun i => an2 (h i) (pullback g $ f i) (pullback.snd g $ f i) $ hEC i
  have hapi : ∀ i, k i ≫ pullback.fst pi_ (f i) ≫ pi_ = pullback.fst g (f i) ≫ g := by
    intro i
    rw [pullback.condition, ← assoc, hk1 i, ← pullback.condition]
  have hglue : ∀ i j, pullback.fst (pullback.fst g $ f i) (pullback.fst g $ f j) ≫
        (k i ≫ pullback.fst pi_ (f i))
      = pullback.snd (pullback.fst g $ f i) (pullback.fst g $ f j) ≫
        (k j ≫ pullback.fst pi_ (f j)) := by
    intro i j
    refine eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover pi_ I U f hcover h ?_ ?_
    simp [assoc]
    rw [hapi i, hapi j, ← assoc, ← assoc, pullback.condition]
    have heq : (pullback.fst (pullback.fst g $ f i) (pullback.fst g $ f j) ≫
          (k i ≫ pullback.fst pi_ (f i))) ≫ pi_
        = (pullback.fst (pullback.fst g $ f i) (pullback.fst g $ f j) ≫
          pullback.fst g (f i)) ≫ g := by
      rw [assoc, assoc, hapi i, ← assoc]
    rw [heq, comap_comp]
    exact hg.comap_of_isOpenImmersion _
  obtain ⟨ph_, hph⟩ :=
    exists_hom_of_isOpenImmersion_cover U f hcover g
      (fun i => k i ≫ pullback.fst pi_ (f i)) hglue
  have hphpi : ph_ ≫ pi_ = g := by
    refine hom_ext_of_isOpenImmersion_cover U f hcover g fun i => ?_
    rw [← assoc, hph i, assoc, hapi i]
  refine ⟨ph_, hphpi, fun y hy => ?_⟩
  have hy' := hy
  refine eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover pi_ I U f hcover h (by rw [hy', hphpi]) ?_
  rwa [hy']

end FunctorialResolution.Blowup
end
section


namespace FunctorialResolution.Blowup



def openCoverOfForallMem {W : Sch} (U : ↥W → Opn W) (hU : ∀ w, w ∈ U w) :
    W.OpenCover :=
  mkOfCovers (↥W) (fun w => toScheme $ U w) (fun w => ι $ U w)
    (fun x => ⟨x, ⟨x, hU x⟩, rfl⟩)

theorem exists_sum_mul_eq_one_of_map_eq_span {R A : Type} [CommRing R] [CommRing A]
    (I : Ideal R) (ph_ : R →+* A) (s : A) (hmap : Ideal.map ph_ I = span {s})
    (hs : s ∈ nonZeroDivisors A) :
    ∃ (n : ℕ) (a : Fin n → ↥I) (c d : Fin n → A),
      (∀ i, ph_ (a i : R) = d i * s) ∧ ∑ i, c i * d i = 1 := by
  have hsmem : s ∈ Ideal.map ph_ I := by simp_all
  rw [← span_eq I, map_span] at hsmem
  obtain ⟨n, c, gg, hsum⟩ := Submodule.mem_span_set'.mp hsmem
  choose a ha hpha using fun i => (gg i).2
  have hdex : ∀ i, ∃ e, ph_ (a i) = e * s := by
    intro i
    have hmem : ph_ (a i) ∈ span {s} := by
      rw [← hmap]
      exact mem_map_of_mem _ $ ha i
    obtain ⟨e, he⟩ := mp_ mem_span_singleton' hmem
    exact ⟨e, sy_ he⟩
  choose d hdd using hdex
  refine ⟨n, fun i => ⟨a i, ha i⟩, c, d, hdd, ?_⟩
  let _a0 := ∑ i, c i * d i
  have hss : _a0 * s = s := by
    rw [sum_mul]
    conv_rhs => rw [← hsum]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hpha i, hdd i, mul_assoc]
  have h1 : (_a0 - 1) * s = 0 := by
    rw [sub_mul, hss, one_mul, sub_self]
  linear_combination (mp_ mem_nonZeroDivisors_iff_right hs _ h1)

theorem exists_mem_basicOpen_of_sum_mul_eq_one {X : Sch} {V : Opn X} {n : ℕ}
    (c d : Fin n → ↥(X.sec V)) (hsum : ∑ i, c i * d i = 1) (w : ↥X) (hw : w ∈ V) :
    ∃ i, w ∈ basicOpen X (d i) := by
  by_contra hcon
  push Not at hcon
  let _a0 := stkX X w
  let _a1 := pGerm X V w hw
  have hmem : ∀ i, _a1.hom (d i)
      ∈ m16 _a0 := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hcon i $ mpr (X.mem_basicOpen (d i) w hw) hu
  have h1 : 1 ∈ m16 _a0 := by
    have hone : _a1.hom (1 : V.sec) = 1 := map_one _
    rw [← hone, ← hsum, map_sum]
    refine m133 _ fun i _ => ?_
    rw [map_mul]
    exact mul_mem_left _ _ $ hmem i
  exact (IsLocalRing.maximalIdeal.isMaximal _a0).ne_top
    (mpr (eq_top_iff_one _) h1)

private theorem appLE_top_top_eq_appTop {X Y : Sch} (f : X ⟶ Y)
    (h : (⊤ : Opn X) ≤ pre f (⊤ : Opn Y)) : appLE f ⊤ ⊤ h = appTop f := by
  have h2 : pMap X (homOfLE h).op = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  simp only [appLE, h2]
  rfl

theorem appLE_comp {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z) U
    V V' e1_ e2_
    e :
    (f ≫ g).appLE U V' e = g.appLE U V e1_ ≫ f.appLE V V' e2_ := by
  rw [m91]

section
variable {R : Type} [CommRing R]
section
variable {W : Sch} (U : Opn W) (g : W ⟶ Sp R)
theorem appTop_io_comp_eq_appLE_comp (hle : (⊤ : U.toScheme.Opens) ≤ ι U ⁻¹ᵁ U)
    (hle' : U ≤ g ⁻¹ᵁ (⊤ : (Sp R).Opens)) :
    appTop (ι U ≫ g) = g.appLE ⊤ U hle' ≫ U.ι.appLE U ⊤ hle := by
  rw [← appLE_top_top_eq_appTop (opI U ≫ g) $ by simp]
  exact appLE_comp U.i g ⊤ U ⊤ hle' hle $ by simp

theorem exists_sections_iso_globalSectionsRingHom :
    ∃ e : (W.sec U) ≅ Γ(toScheme U, ⊤),
      ∀ r : R, globalSectionsRingHom (ι U ≫ g) r
        = (hom e.hom) (sectionsRingHom g U r) := by
  have hle : (⊤) ≤ opPre U U := by simp
  have hle' : U ≤ g ⁻¹ᵁ (⊤ : Opn $ Sp R) := by simp
  refine ⟨asIso $ U.ι.appLE U ⊤ hle, fun r => ?_⟩
  simp only [globalSectionsRingHom_eq, appTop_io_comp_eq_appLE_comp U g hle hle', asIso_hom, hom_comp, comp_apply,
    sectionsRingHom_apply]
end

section
variable (I : Ideal R)
section
variable {W : Sch} (g : W ⟶ Sp R) (hcart : IsLocallyGeneratedByNonZeroDivisor (comap (specIdealSheaf I) g))
include hcart
theorem exists_local_lift_toSpec_of_isLocallyGeneratedByNonZeroDivisor (w : ↥W) :
    ∃ (U : Opn W) (_ : w ∈ U) (h : U.toScheme ⟶ affineBlowup I),
      h ≫ AffineBlowup.toSpec I = U.i ≫ g := by
  obtain ⟨V, s, hwV, hs, hspan⟩ := hcart w
  have hmap :=
    (comap_specIdealSheaf_ideal I g V).symm.trans hspan
  obtain ⟨n, a, c, d, hd, hsum⟩ :=
    exists_sum_mul_eq_one_of_map_eq_span I (sectionsRingHom g V) s hmap hs
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_of_sum_mul_eq_one c d hsum w hwV
  have hLoc :=
    V.2.isLocalization_basicOpen $ d i
  have hUV := W.basicOpen_le $ d i
  let _m0 := bOpn W $ d i
  have : IsAffine _m0.toScheme := V.2.basicOpen $ d i
  let _m1 := pMap W (homOfLE hUV).op
  have hunit : IsUnit $ _m1.hom $ d i :=
    IsLocalization.map_units (M := powers $ d i) _ ⟨d i, mem_powers _⟩
  have hrs : _m1.hom s
      ∈ nonZeroDivisors Γ(W, bOpn W $ d i) :=
    nonZeroDivisors_le_comap (powers $ d i) _ hs
  have hres :=
    fun r => sectionsRingHom_restrict g hUV r
  have hcomp : sectionsRingHom g _m0
      = _m1.hom.comp (sectionsRingHom g V) :=
    RingHom.ext hres
  have hmapSpan : Ideal.map (sectionsRingHom g _m0) I
      = span {sectionsRingHom g _m0 $ a i} := by
    have h1 : Ideal.map (sectionsRingHom g _m0) I
        = span {_m1.hom (d i)
            * _m1.hom s} := by
      rw [hcomp, ← map_map, hmap, map_span, image_singleton]
      exact (span_singleton_mul_left_unit hunit _).symm
    rw [h1, hres $ a i, hd i, map_mul]
  have hnonZeroDivU : sectionsRingHom g _m0 (a i)
      ∈ nonZeroDivisors Γ(W, bOpn W $ d i) := by
    rw [hres, hd i, map_mul]
    exact mul_mem hunit.mem_nonZeroDivisors hrs
  obtain ⟨e, he⟩ := exists_sections_iso_globalSectionsRingHom _m0 g
  have hgen' : Ideal.map (globalSectionsRingHom $ opI _m0 ≫ g) I
      = span {globalSectionsRingHom (opI _m0 ≫ g) $ a i} := by
    have e1 : Ideal.map (globalSectionsRingHom $ opI _m0 ≫ g) I
        = Ideal.map (hom e.hom)
            (Ideal.map (sectionsRingHom g _m0) I) := by
      rw [map_map]
      exact congrArg (fun ϕ => Ideal.map ϕ I) $ RingHom.ext he
    rw [e1, hmapSpan, map_span, image_singleton, he]
  have hnonZeroDiv' : globalSectionsRingHom (opI _m0 ≫ g) (a i)
      ∈ nonZeroDivisors Γ(oSch _m0, ⊤) := by
    rw [he]
    exact map_mem_nonZeroDivisors_of_iso e hnonZeroDivU
  obtain ⟨h, hh, -⟩ :=
    exists_lift_affineBlowup I (opI _m0 ≫ g) (a i) hgen' hnonZeroDiv'
  exact ⟨bOpn W $ d i, hi, h, hh⟩

theorem exists_lift_toSpec_of_isLocallyGeneratedByNonZeroDivisor :
    ∃ h, h ≫ AffineBlowup.toSpec I = g := by
  choose U hU h hh using fun w => exists_local_lift_toSpec_of_isLocallyGeneratedByNonZeroDivisor I g hcart w
  have hcompat : ∀ x y,
      m57 (opI $ U x) (opI $ U y) ≫ h x
        = m47 (opI $ U x) (opI $ U y) ≫ h y := by
    intro x y
    refine affineBlowup_hom_ext _ _ ?_ ?_
    rw [assoc, assoc, hh x, hh y, ← assoc, ← assoc,
      condition]
    have h1 : (m57 (opI $ U x) (opI $ U y) ≫ h x) ≫ p13 I
        = (m57 (opI $ U x) (opI $ U y) ≫ opI (U x)) ≫ g := by
      rw [assoc, hh x, ← assoc]
    have h2 : comap (specIdealSheaf I)
          ((m57 (opI $ U x) (opI $ U y) ≫ opI (U x)) ≫ g)
        = comap (cmI (specIdealSheaf I) g)
            (m57 (opI $ U x) (opI $ U y) ≫ opI (U x)) := by
      simp [comap_comp]
    rw [h1, h2]
    exact IsLocallyGeneratedByNonZeroDivisor.comap_of_isOpenImmersion hcart _
  let _a0 := openCoverOfForallMem U hU
  refine ⟨_a0.glueMorphisms h fun x y => hcompat x y, ?_⟩
  refine _a0.hom_ext _ _ fun x => ?_
  rw [← assoc, _a0.ι_glueMorphisms h (fun x y => hcompat x y) x]
  exact hh x
end

theorem isBlowupAlongIdealSheaf_affineBlowup_toSpec :
    IsBlowupAlongIdealSheaf (AffineBlowup.toSpec I) $ specIdealSheaf I := by
  refine m157 (isLocallyGeneratedByNonZeroDivisor_comap_toSpec I) ?_
  intro W g hg
  obtain ⟨h, hh⟩ := exists_lift_toSpec_of_isLocallyGeneratedByNonZeroDivisor I g hg
  refine ⟨h, hh, fun h' hh' => ?_⟩
  refine affineBlowup_hom_ext h' h (by rw [hh', hh]) ?_
  rwa [hh']
end
end

end FunctorialResolution.Blowup
end
section

namespace FunctorialResolution.Blowup

section
variable {X X' : Sch} (f : X' ⟶ X)
theorem IsBlowupAlongIdealSheaf.of_isIso [IsIso f] :
    IsBlowupAlongIdealSheaf f (⊤ : ISD X) := by
  refine m157 (isLocallyGeneratedByNonZeroDivisor_comap_top f) ?_
  intro W g _
  refine ExistsUnique.intro (g ≫ inv f) ?_ ?_
  simp
  simp_all

theorem comap_eq_top_of_notMem_support
    (I : ISD X) (h : ∀ x : X', f.base x ∉ support I) :
    comap I f = ⊤ := by
  refine mp_ (support_eq_bot_iff _) ?_
  rw [support_comap]
  exact SetLike.ext fun x => ⟨fun hx => absurd (show bsM f x ∈ spI I from hx) $ h x, fun hx => (show False from hx).elim⟩
end

section
variable {W Z : Sch} (g : W ⟶ Z) [IsOpenImmersion g] (V : Opn W)
theorem isAffineOpen_image (hV : IsAffineOpen V) : IsAffineOpen $ g.im V :=
  hV.image_of_isOpenImmersion g

theorem preimage_image_opens : pre g (g ''ᵁ V) = V :=by simp_all
end

section
variable {X : Sch}
section
variable {U V : Opn X} (h : IsCompl U V) (x : ↥X)
include h
theorem range_io_disjoint (hU : x ∈ range ⇑U.ib) (hV : x ∈ range ⇑V.ib) : False := by
  rw [q1] at hU
  rw [q1] at hV
  have h2 : x ∈ ((U ⊓ V : Opn X) : Set X) := by
    simp [coe_inf, mem_inter_iff]
    exact ⟨hU, hV⟩
  rw [h.inf_eq_bot] at h2
  simp at h2

theorem notMem_of_isCompl (hU : x ∈ (U : Set ↥X)) (hV : x ∈ (V : Set ↥X)) : False := by
  have h2 : ((U ⊓ V : Opn X) : Set X) = ((⊥ : Opn X) : Set X) := by rw [h.inf_eq_bot]
  have hd := by simpa using h2
  have hx : x ∈ (∅ : Set X) := by
    rw [← hd]
    exact ⟨hU, hV⟩
  simp at hx
end

theorem subsingleton_presheaf_of_isEmpty [IsEmpty ↥X] {V : Opn X}
    (hV : IsAffineOpen V) : Subsingleton ↥(X.presheaf.obj $ Opposite.op V) := by
  by_contra hcon
  have :=
    mp_ not_subsingleton_iff_nontrivial hcon
  obtain ⟨p⟩ : Nonempty $ PrimeSpectrum $ pObj X $ m112 V := inferInstance
  exact IsEmpty.false $ hV.fromSpec.base p

theorem range_opens_io (U : Opn X) :
    range ⇑U.ib = (U : Set ↥X) := by
  simp
end

section
variable {X Y Z : Sch} (f : Z ⟶ X)
theorem range_comp_coprod_inl_subset :
    range ⇑(f ≫ (coprod.inl : X ⟶ X ⨿ Y)).base
      ⊆ range ⇑(coprod.inl : X ⟶ X ⨿ Y).base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨bsM f z, by simp⟩

theorem ker_comp_coprod_inl_comap_inr
    [QuasiCompact $ f ≫ (coprod.inl : X ⟶ X ⨿ Y)] :
    (f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.comap (coprod.inr : Y ⟶ X ⨿ Y) = ⊤ := by
  let _c0 := f ≫ (coprod.inl : X ⟶ X ⨿ Y)
  let _c1 := (coprod.inr : Y ⟶ X ⨿ Y)
  refine comap_eq_top_of_notMem_support _c1
    (m149 _c0) ?_
  intro y hy
  have hy' : bsM _c1 y ∈
      (_c0.ker.support : Set ↥(X ⨿ Y)) := hy
  rw [support_ker] at hy'
  have h2 : bsM _c1 y ∈ range _c1.base :=
    mem_range_self y
  rw [range_coprod_inr_eq_compl X Y] at h2
  exact h2 $ (closure_minimal (range_comp_coprod_inl_subset f) $ isClosed_range_coprod_inl X Y) hy'
end

section
variable {A B : CRC} (ph_ : A ⟶ B)
private theorem surjective_of_isIso (hph : IsIso ph_) :
    Surjective $ hom ph_ := by
  intro y
  exact ⟨hom (inv ph_) y,
    congrArg (hom · y) $ m117 ph_⟩

theorem bijective_of_isIso [IsIso ph_] :
    Bijective $ hom ph_ := by
  have h3 : ∀ c, hom (inv ph_) (hom ph_ c) = c := fun c =>
    congrArg (hom · c) $ m118 ph_
  constructor
  intro a a' h
  have h2 : hom (inv ph_) (hom ph_ a)
      = hom (inv ph_) (hom ph_ a') := by rw [h]
  simp [h3] at h2
  exact h2
  intro b
  exact ⟨hom (inv ph_) b,
    congrArg (hom · b) $ m117 ph_⟩
end

theorem appLE_image_bijective_of_isOpenImmersion {W Z : Sch} (g : W ⟶ Z)
    [IsOpenImmersion g] (V : Opn W) (e : V ≤ pre g (g ''ᵁ V)) :
    Bijective $ hom $ appLE g (g.im V) V e := by
  have : IsIso $ homOfLE e := ⟨homOfLE (preimage_image_opens g V).le, rfl, rfl⟩
  let _a0 := appLE g (imU g V) V e
  have : IsIso _a0 := by
    show IsIso $ g.app (imU g V) ≫ pMap W (homOfLE e).op
    infer_instance
  exact bijective_of_isIso _a0

theorem isBlowupAlongIdealSheaf_id_top (X : Sch) : IsBlowupAlongIdealSheaf (𝟙 X) (⊤ : ISD X) :=
  IsBlowupAlongIdealSheaf.of_isIso $ 𝟙 X


private theorem exists_affineOpen_mem (X : Sch) x :
    ∃ V : ↥(X.affineOpens), x ∈ ((V : Opn X) : Set ↥X) := by
  have h : x ∈ (⨆ V : (affO X), (V : Opn X)) := by
    rw [iSup_affineOpens_eq_top X]
    exact trivial
  obtain ⟨V, hV⟩ := mp_ mem_iSup h
  exact ⟨V, mpr_ mem_coe hV⟩

theorem map_ker_comp_of_surjective {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (ph_ : A →+* B) (ps_ : B →+* C) (hph : Surjective ph_) :
    Ideal.map ph_ (RingHom.ker $ ps_.comp ph_) = RingHom.ker ps_ := by
  rw [ker_eq_comap_bot $ ps_.comp ph_, ← comap_comap, ← ker_eq_comap_bot]
  exact map_comap_of_surjective ph_ hph _

theorem map_appLE_ker_comp {T W Z : Sch} (f : T ⟶ W) (g : W ⟶ Z)
    (U : Opn Z) (V : Opn W) (hUV : g.pre U = V) (e : V ≤ g.pre U)
    (hsurj : Surjective $ hom $ g.app U) :
    Ideal.map (hom $ g.appLE U V e)
        (RingHom.ker $ hom $ (f ≫ g).app U)
      = RingHom.ker (hom $ f.app V) := by
  subst hUV
  have hid : g.appLE U (preU g U) e = g.app U := by
    show g.app U ≫ W.presheaf.map (homOfLE e).op = g.app U
    have h1 : (homOfLE e).op = 𝟙 (m112 $ preU g U) := rfl
    rw [h1, W.presheaf.map_id, comp_id]
  have hcomp : hom ((f ≫ g).app U)
      = RingHom.comp (hom $ f.app $ preU g U)
          (hom $ g.app U) := rfl
  rw [hid, hcomp]
  exact map_ker_comp_of_surjective _ _ hsurj

private theorem base_comp_apply {U V W : Sch} (f : U ⟶ V) (g : V ⟶ W) (x : U) :
    (f ≫ g).base x = g.base (f.base x) := by simp

section
variable {A B A' B' : Sch} (p : A' ⟶ A) (q : B' ⟶ B)
theorem range_fst_subset_range_inl
    (s : PullbackCone (coprod.map p q) (coprod.inl : A ⟶ A ⨿ B)) :
    range ⇑(PullbackCone.fst s).base ⊆ range ⇑(coprod.inl : A' ⟶ A' ⨿ B').base := by
  rintro _ ⟨t, rfl⟩
  by_contra hmem
  have hy := hmem
  rw [← mem_compl_iff, ← range_coprod_inr_eq_compl A' B'] at hy
  obtain ⟨b, hb⟩ := hy
  have e1 := by
    simpa using (congrArg (fun m : s.pt ⟶ A ⨿ B => bsM m t) s.condition)
  have hmapr : ((coprod.inr : B' ⟶ A' ⨿ B') ≫ coprod.map p q)
      = q ≫ (coprod.inr : B ⟶ A ⨿ B) := by simp
  have e2 : bsM (coprod.map p q) (bsM (coprod.inr : B' ⟶ A' ⨿ B') b)
      = bsM (coprod.inr : B ⟶ A ⨿ B) (bsM q b) := by
    rw [← base_comp_apply, hmapr, base_comp_apply]
  have key : bsM (coprod.map p q) (bsM (PullbackCone.fst s) t)
      = bsM (coprod.map p q) (bsM (coprod.inr : B' ⟶ A' ⨿ B') b) := by rw [hb]
  have hfin : bsM (coprod.inl : A ⟶ A ⨿ B) (bsM (PullbackCone.snd s) t)
      = bsM (coprod.inr : B ⟶ A ⨿ B) (bsM q b) := by rw [← e1, key, e2]
  have hmem2 : bsM (coprod.inl : A ⟶ A ⨿ B) (bsM (PullbackCone.snd s) t)
      ∈ range (coprod.inr : B ⟶ A ⨿ B).base := ⟨bsM q b, sy_ hfin⟩
  rw [range_coprod_inr_eq_compl A B] at hmem2
  exact hmem2 ⟨bsM (PullbackCone.snd s) t, rfl⟩

theorem range_fst_subset_range_inr
    (s : PullbackCone (coprod.map p q) (coprod.inr : B ⟶ A ⨿ B)) :
    range ⇑(PullbackCone.fst s).base ⊆ range ⇑(coprod.inr : B' ⟶ A' ⨿ B').base := by
  rintro _ ⟨t, rfl⟩
  rw [range_coprod_inr_eq_compl A' B', mem_compl_iff]
  intro hy
  obtain ⟨a, ha⟩ := hy
  have e1 := by
    simpa using (congrArg (fun m : s.pt ⟶ A ⨿ B => bsM m t) s.condition)
  have hmapl : ((coprod.inl : A' ⟶ A' ⨿ B') ≫ coprod.map p q)
      = p ≫ (coprod.inl : A ⟶ A ⨿ B) := by simp
  have e2 : bsM (coprod.map p q) (bsM (coprod.inl : A' ⟶ A' ⨿ B') a)
      = bsM (coprod.inl : A ⟶ A ⨿ B) (bsM p a) := by
    rw [← base_comp_apply, hmapl, base_comp_apply]
  have key : bsM (coprod.map p q) (bsM (PullbackCone.fst s) t)
      = bsM (coprod.map p q) (bsM (coprod.inl : A' ⟶ A' ⨿ B') a) := by rw [ha]
  have hfin : bsM (coprod.inr : B ⟶ A ⨿ B) (bsM (PullbackCone.snd s) t)
      = bsM (coprod.inl : A ⟶ A ⨿ B) (bsM p a) := by rw [← e1, key, e2]
  have hmem2 : bsM (coprod.inr : B ⟶ A ⨿ B) (bsM (PullbackCone.snd s) t)
      ∈ range (coprod.inr : B ⟶ A ⨿ B).base := ⟨bsM (PullbackCone.snd s) t, rfl⟩
  rw [range_coprod_inr_eq_compl A B, hfin] at hmem2
  exact hmem2 ⟨bsM p a, rfl⟩

theorem isPullback_coprod_inl_map :
    IsPullback (coprod.inl : A' ⟶ A' ⨿ B') p (coprod.map p q) (coprod.inl : A ⟶ A ⨿ B) := by
  have hw : coprod.inl ≫ coprod.map p q
      = p ≫ coprod.inl := by simp
  refine of_isLimit' ⟨hw⟩ $ PullbackCone.IsLimit.mk hw
    (fun s => m43 coprod.inl (PullbackCone.fst s)
      (range_fst_subset_range_inl p q s)) ?_ ?_ ?_
  intro s
  simp [lift_fac]
  intro s
  have hl : m43 coprod.inl (PullbackCone.fst s)
      (range_fst_subset_range_inl p q s) ≫ coprod.inl
      = PullbackCone.fst s := by
    simp [lift_fac]
  have h2 := s.condition
  rw [← hl, assoc, hw, ← assoc] at h2
  exact mp_ (cancel_mono _) h2
  intro s m hm _
  have hl : m43 coprod.inl (PullbackCone.fst s)
      (range_fst_subset_range_inl p q s) ≫ coprod.inl
      = PullbackCone.fst s := by
    simp [lift_fac]
  have h2 : m ≫ (coprod.inl : A' ⟶ A' ⨿ B')
      = m43 (coprod.inl : A' ⟶ A' ⨿ B') (PullbackCone.fst s)
          (range_fst_subset_range_inl p q s) ≫ coprod.inl := by simp_all
  exact mp_ (cancel_mono _) h2

theorem isPullback_coprod_inr_map :
    IsPullback (coprod.inr : B' ⟶ A' ⨿ B') q (coprod.map p q) (coprod.inr : B ⟶ A ⨿ B) := by
  have hw : coprod.inr ≫ coprod.map p q
      = q ≫ coprod.inr := by simp
  refine of_isLimit' ⟨hw⟩ $ PullbackCone.IsLimit.mk hw
    (fun s => m43 coprod.inr (PullbackCone.fst s)
      (range_fst_subset_range_inr p q s)) ?_ ?_ ?_
  intro s
  simp [lift_fac]
  intro s
  have hl : m43 coprod.inr (PullbackCone.fst s)
      (range_fst_subset_range_inr p q s) ≫ coprod.inr
      = PullbackCone.fst s := by
    simp [lift_fac]
  have h2 := s.condition
  rw [← hl, assoc, hw, ← assoc] at h2
  exact mp_ (cancel_mono _) h2
  intro s m hm _
  have hl : m43 coprod.inr (PullbackCone.fst s)
      (range_fst_subset_range_inr p q s) ≫ coprod.inr
      = PullbackCone.fst s := by
    simp [lift_fac]
  have h2 : m ≫ (coprod.inr : B' ⟶ A' ⨿ B')
      = m43 (coprod.inr : B' ⟶ A' ⨿ B') (PullbackCone.fst s)
          (range_fst_subset_range_inr p q s) ≫ coprod.inr := by simp_all
  exact mp_ (cancel_mono _) h2
end

private theorem ker_ideal_eq_ker_app {T W : Sch} (f : T ⟶ W) [QuasiCompact f]
    U :
    f.ker.ideal U = RingHom.ker (hom $ f.app (U : Opn W)) := by
  simp

theorem ker_comap_of_isOpenImmersion {T W Z : Sch} (f : T ⟶ W) (g : W ⟶ Z)
    [IsOpenImmersion g] [QuasiCompact f] [QuasiCompact $ f ≫ g] :
    (f ≫ g).ker.comap g = f.ker := by
  let _a0 := f ≫ g
  have key : ∀ V : affO W, (kCm _a0 g).ideal V = f.ker.ideal V := by
    intro V
    have hU := isAffineOpen_image g V V.2
    have hpre :=
      preimage_image_opens g V
    have e := hpre.ge
    rw [comap_ideal_eq_map_appLE (m149 _a0) g ⟨imU g V, hU⟩ V e, ker_ideal_eq_ker_app _a0 ⟨imU g V, hU⟩, ker_ideal_eq_ker_app f V]
    exact map_appLE_ker_comp f g (imU g V) V hpre e
      (surjective_of_isIso (g.app $ imU g V) inferInstance)
  ext V
  rw [key V]

theorem ker_comp_coprod_inl_comap_inl {X Y Z} (f : Z ⟶ X)
    [QuasiCompact f] [QuasiCompact $ f ≫ (coprod.inl : X ⟶ X ⨿ Y)] :
    (f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.comap (coprod.inl : X ⟶ X ⨿ Y) = f.ker :=
  ker_comap_of_isOpenImmersion f coprod.inl

theorem ideal_eq_of_map_eq_of_bijective {A B : Type} [CommRing A] [CommRing B]
    (ph_ : A →+* B) (hph : Bijective ph_) {K L : Ideal A}
    (h : Ideal.map ph_ K = Ideal.map ph_ L) : K = L := by
  have key : ∀ K' L', m6 ph_ K' = m6 ph_ L' → K' ≤ L' := by
    intro K' L' h' x hx
    have hx' : ph_ x ∈ m6 ph_ L' := by
      rw [← h']
      exact mem_map_of_mem ph_ hx
    obtain ⟨y, hy, hxy⟩ := mp_ (mem_map_iff_of_surjective ph_ hph.2) hx'
    rwa [← an1 hph hxy]
  exact le_antisymm (key K L h) $ key L K h.symm

theorem ideal_image_eq_of_comap_eq {W Z : Sch} (g : W ⟶ Z) [IsOpenImmersion g]
    {I J : ISD Z} (h : comap I g = comap J g) (V : ↥(W.affineOpens)) :
    I.ideal ⟨g.im (V : Opn W), isAffineOpen_image g (V : Opn W) V.2⟩
      = J.ideal ⟨g.im (V : Opn W), isAffineOpen_image g (V : Opn W) V.2⟩ := by
  have e :=
    (preimage_image_opens g V).ge
  have h1 := comap_ideal_eq_map_appLE I g
    ⟨imU g V, isAffineOpen_image g V V.2⟩ V e
  have h2 := comap_ideal_eq_map_appLE J g
    ⟨g.im V, isAffineOpen_image g V V.2⟩ V e
  have h3 : (comap I g).ideal V = (comap J g).ideal V := by rw [h]
  rw [h1, h2] at h3
  exact ideal_eq_of_map_eq_of_bijective _ (appLE_image_bijective_of_isOpenImmersion g V e) h3

theorem idealSheafData_ext_coprod {X Y : Sch} (I J : IdealSheafData (X ⨿ Y))
    (hl : comap I (coprod.inl : X ⟶ X ⨿ Y) = comap J (coprod.inl : X ⟶ X ⨿ Y))
    (hr : comap I (coprod.inr : Y ⟶ X ⨿ Y) = comap J (coprod.inr : Y ⟶ X ⨿ Y)) :
    I = J := by
  let _a0 := affO $ X ⨿ Y
  refine ext_of_iSup_eq_top
    (Sum.elim
      (fun V : (affO X) =>
        (⟨(coprod.inl : X ⟶ X ⨿ Y).im (V : Opn X),
          isAffineOpen_image (coprod.inl : X ⟶ X ⨿ Y) (V : Opn X) V.2⟩ :
            _a0))
      (fun V : (affO Y) =>
        (⟨(coprod.inr : Y ⟶ X ⨿ Y).im (V : Opn Y),
          isAffineOpen_image (coprod.inr : Y ⟶ X ⨿ Y) (V : Opn Y) V.2⟩ :
            _a0))) ?_ ?_
  rw [eq_top_iff]
  intro z _
  by_cases hz : z ∈ range (coprod.inl : X ⟶ X ⨿ Y).base
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨V, hV⟩ := exists_affineOpen_mem X x
  exact mpr_ mem_iSup ⟨m44 V, mp_ mem_coe $ Set.mem_image_of_mem _ hV⟩
  have hz' : z ∈ range (coprod.inr : Y ⟶ X ⨿ Y).base := by
    rwa [range_coprod_inr_eq_compl X Y]
  obtain ⟨y, rfl⟩ := hz'
  obtain ⟨V, hV⟩ := exists_affineOpen_mem Y y
  exact mpr_ mem_iSup ⟨m50 V, mp_ mem_coe $ Set.mem_image_of_mem _ hV⟩
  rintro (V | V)
  exact ideal_image_eq_of_comap_eq coprod.inl hl V
  exact ideal_image_eq_of_comap_eq coprod.inr hr V

theorem algebra_smooth_of_subsingleton (R S : Type) [CommRing R] [CommRing S]
    [Algebra R S] [Subsingleton S] : Algebra.Smooth R S := by
  have hloc : m215 (0 : R) S :=
    { map_units := fun y => ⟨1, m111 _ _⟩
      surj := fun z => ⟨⟨0, 1⟩, m111 _ _⟩
      exists_of_eq := fun _ => ⟨⟨0, mem_powers 0⟩, by simp⟩ }
  exact ⟨Algebra.FormallySmooth.of_isLocalization $ powers (0 : R),
    IsLocalization.Away.finitePresentation (0 : R)⟩

theorem ringHom_smooth_of_subsingleton {R S : Type} [CommRing R] [CommRing S]
    (hS : Subsingleton S) (ph_ : R →+* S) : RingHom.Smooth ph_ :=
  @algebra_smooth_of_subsingleton R S _ _ ph_.toAlgebra hS

theorem smooth_of_isEmpty {X Y : Sch} (f : X ⟶ Y) [IsEmpty ↥X] : Smooth f := by
  constructor
  intro U _ V hV e
  exact ringHom_smooth_of_subsingleton (subsingleton_presheaf_of_isEmpty hV)
    (hom $ appLE f U V e)

theorem IsBlowupAlongIdealSheaf.coprod {X1 X2 X1' X2' : Sch} {pi1 : X1' ⟶ X1} {pi2 : X2' ⟶ X2}
    {I : IdealSheafData $ X1 ⨿ X2}
    (h1_ : IsBlowupAlongIdealSheaf pi1 $ comap I (coprod.inl : X1 ⟶ X1 ⨿ X2))
    (h2_ : IsBlowupAlongIdealSheaf pi2 $ comap I (coprod.inr : X2 ⟶ X1 ⨿ X2)) :
    IsBlowupAlongIdealSheaf (coprod.map pi1 pi2) I := by
  let _c0 := (coprod.inr : X2 ⟶ X1 ⨿ X2)
  let _c1 := (coprod.inl : X1 ⟶ X1 ⨿ X2)
  let _a2 := coprod.map pi1 pi2
  let _a0 := pullback.snd _a2 _c1
  have hb1_ : IsBlowupAlongIdealSheaf _a0
      (cmI I _c1) := by
    have hpb := isPullback_coprod_inl_map pi1 pi2
    have hfac : hpb.isoPullback.symm.hom ≫ pi1
        = _a0 := by
      rw [symm_hom, inv_comp_eq]
      exact hpb.isoPullback_hom_snd.symm
    have hbl := h1_.iso_hom_comp hpb.isoPullback.symm
    rwa [hfac] at hbl
  let _a1 := pullback.snd _a2 _c0
  have hb2_ : IsBlowupAlongIdealSheaf _a1
      (cmI I _c0) := by
    have hpb := isPullback_coprod_inr_map pi1 pi2
    have hfac : hpb.isoPullback.symm.hom ≫ pi2
        = _a1 := by
      rw [symm_hom, inv_comp_eq]
      exact hpb.isoPullback_hom_snd.symm
    have hbl := h2_.iso_hom_comp hpb.isoPullback.symm
    rwa [hfac] at hbl
  have hoi : ∀ b, IsOpenImmersion
      (m190 (motive := fun b => (cond b X1 X2) ⟶ X1 ⨿ X2)
        _c0 _c1 b) := by
    intro b
    cases b
    exact inferInstance
    exact inferInstance
  refine IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover _a2 I
    (cond · X1 X2)
    (m190 (motive := fun b => (cond b X1 X2) ⟶ X1 ⨿ X2)
      _c0 _c1) ?_ ?_
  intro x
  by_cases hx : x ∈ range _c1.base
  exact ⟨true, hx⟩
  refine ⟨false, ?_⟩
  rwa [range_coprod_inr_eq_compl X1 X2]
  intro b
  cases b
  exact hb2_
  exact hb1_

section
variable {X A F : Sch} (f : A ⟶ X) (g : F ⟶ X) {U V : Opn X} (h : IsCompl U V)
include h
theorem range_fst_subset_range_inl_of_isCompl
    (hg : range ⇑g.base ⊆ range ⇑V.ib)
    (s : PullbackCone (coprod.desc f g) U.i) :
    range ⇑(PullbackCone.fst s).base ⊆ range ⇑(coprod.inl : A ⟶ A ⨿ F).base := by
  rintro _ ⟨t, rfl⟩
  by_contra hmem
  have hy := hmem
  rw [← mem_compl_iff, ← range_coprod_inr_eq_compl A F] at hy
  obtain ⟨b, hb⟩ := hy
  let _a0 := opIb U $ bsM (PullbackCone.snd s) t
  let _a1 := coprod.desc f g
  have e1 : bsM _a1 (bsM (PullbackCone.fst s) t)
      = _a0 := by
    simpa using (congrArg (fun m : s.pt ⟶ X => bsM m t) s.condition)
  have e2 : bsM _a1 (bsM (coprod.inr : F ⟶ A ⨿ F) b) = bsM g b := by
    rw [← base_comp_apply, coprod.inr_desc]
  have hfin := e2
  rw [hb, e1] at hfin
  refine range_io_disjoint h _a0
    (mem_range_self _) ?_
  rw [hfin]
  exact hg $ mem_range_self b

section
variable (hf : range ⇑f.base ⊆ range ⇑U.ib)
include hf
section
variable (hg : range ⇑g.base ⊆ range ⇑V.ib)
include hg
theorem isPullback_inl_coprod_desc :
    IsPullback (coprod.inl : A ⟶ A ⨿ F) (IsOpenImmersion.lift U.i f hf)
      (coprod.desc f g) U.i := by
  let _c0 := (coprod.inl : A ⟶ A ⨿ F)
  have hw : _c0 ≫ coprod.desc f g
      = m43 U.i f hf ≫ opI U := by
    rw [coprod.inl_desc, lift_fac]
  refine of_isLimit' ⟨hw⟩ $ PullbackCone.IsLimit.mk hw
    (fun s => m43 _c0 (PullbackCone.fst s)
      (range_fst_subset_range_inl_of_isCompl f g h hg s)) ?_ ?_ ?_
  intro s
  simp [lift_fac]
  intro s
  have hl : m43 _c0 (PullbackCone.fst s)
      (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ _c0
      = PullbackCone.fst s := by
    simp [lift_fac]
  have h2 := s.condition
  rw [← hl, assoc, hw, ← assoc] at h2
  exact mp_ (cancel_mono _) h2
  intro s m hm _
  have hl : m43 _c0 (PullbackCone.fst s)
      (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ _c0
      = PullbackCone.fst s := by
    simp [lift_fac]
  have h2 : m ≫ _c0
      = m43 _c0 (PullbackCone.fst s)
          (range_fst_subset_range_inl_of_isCompl f g h hg s) ≫ _c0 := by simp_all
  exact mp_ (cancel_mono _) h2

theorem exists_iso_pullback_coprod_desc_left :
    ∃ e : pullback (coprod.desc f g) U.i ≅ A,
      e.hom ≫ IsOpenImmersion.lift U.i f hf
          = pullback.snd (coprod.desc f g) U.i ∧
        inv e ≫ pullback.fst (coprod.desc f g) U.i = (coprod.inl : A ⟶ A ⨿ F) := by
  refine ⟨(isPullback_inl_coprod_desc f g h hf hg).isoPullback.symm, ?_, ?_⟩
  simp_all
  simp_all
end

theorem range_fst_subset_range_inr_of_isCompl
    (s : PullbackCone (coprod.desc f g) V.i) :
    range ⇑(PullbackCone.fst s).base ⊆ range ⇑(coprod.inr : F ⟶ A ⨿ F).base := by
  rintro _ ⟨t, rfl⟩
  rw [range_coprod_inr_eq_compl A F, mem_compl_iff]
  rintro ⟨a, ha⟩
  have e1 := congrArg (fun m : s.pt ⟶ X => bsM m t) s.condition
  rw [base_comp_apply, base_comp_apply] at e1
  have e2 : bsM (coprod.desc f g) (bsM (coprod.inl : A ⟶ A ⨿ F) a) = bsM f a := by
    rw [← base_comp_apply, coprod.inl_desc f g]
  refine notMem_of_isCompl h (bsM f a) ?_ ?_
  rw [← range_opens_io U]
  exact hf $ mem_range_self a
  rw [← e2, ha, e1, ← range_opens_io V]
  exact mem_range_self _

section
variable (hg : range ⇑g.base ⊆ range ⇑V.ib)
theorem isPullback_inr_coprod_desc :
    IsPullback (coprod.inr : F ⟶ A ⨿ F) (IsOpenImmersion.lift V.i g hg)
      (coprod.desc f g) V.i := by
  have hw := tr_ (coprod.inr_desc f g) (lift_fac V.i g hg).symm
  refine of_isLimit' ⟨hw⟩ $ PullbackCone.IsLimit.mk hw
    (fun s => m43 coprod.inr (PullbackCone.fst s)
      (range_fst_subset_range_inr_of_isCompl f g h hf s)) ?_ ?_ ?_
  intro s
  simp [lift_fac]
  intro s
  have hl : m43 coprod.inr (PullbackCone.fst s)
      (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ coprod.inr
      = PullbackCone.fst s := by
    simp [lift_fac]
  have h2 := s.condition
  rw [← hl, assoc, hw, ← assoc] at h2
  exact mp_ (cancel_mono _) h2
  intro s m hm _
  have hl : m43 coprod.inr (PullbackCone.fst s)
      (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ coprod.inr
      = PullbackCone.fst s := by
    simp [lift_fac]
  have h2 : m ≫ (coprod.inr : F ⟶ A ⨿ F)
      = m43 (coprod.inr : F ⟶ A ⨿ F) (PullbackCone.fst s)
          (range_fst_subset_range_inr_of_isCompl f g h hf s) ≫ coprod.inr := by simp_all
  exact mp_ (cancel_mono _) h2

theorem exists_iso_pullback_coprod_desc_right :
    ∃ e : pullback (coprod.desc f g) V.i ≅ F,
      e.hom ≫ IsOpenImmersion.lift V.i g hg
          = pullback.snd (coprod.desc f g) V.i ∧
        inv e ≫ pullback.fst (coprod.desc f g) V.i = (coprod.inr : F ⟶ A ⨿ F) := by
  refine ⟨(isPullback_inr_coprod_desc f g h hf hg).isoPullback.symm, ?_, ?_⟩
  simp_all
  simp_all
end
end
end

theorem isZariskiLocalAtSource_smooth : IsZariskiLocalAtSource $ @Smooth.{0} :=
  @HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{0}) RingHom.Smooth inferInstance

theorem smooth_coprod_desc {X A B : Sch} (f : A ⟶ X) (g : B ⟶ X)
    (hf : Smooth f) (hg : Smooth g) : Smooth $ coprod.desc f g := by
  refine isZariskiLocalAtSource_smooth.of_openCover (coprodOpenCover.{0, 0} A B) ?_
  intro i
  cases i with
  | inl _ =>
      show Smooth $ coprod.inl ≫ coprod.desc f g
      rwa [coprod.inl_desc]
  | inr _ =>
      show Smooth $ coprod.inr ≫ coprod.desc f g
      rwa [coprod.inr_desc]



theorem ideal_map_inv_map_hom {A B : CRC} (e : A ≅ B) (K : Ideal A) :
    Ideal.map e.inv.hom (Ideal.map e.hom.hom K) = K := by
  rw [map_map, ← hom_comp, e.hom_inv_id, hom_id, map_id]

theorem IsBlowupAlongIdealSheaf.exists_lift {X X' : Sch} {pi_ : X' ⟶ X} {I : ISD X}
    (h : IsBlowupAlongIdealSheaf pi_ I) {W : Sch} (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor $ comap I g) :
    ∃ a : W ⟶ X', a ≫ pi_ = g :=
  (an2 h W g hg).exists

section

variable {X X' : Sch} {pi_ : X' ⟶ X} {I : ISD X} (h : IsBlowupAlongIdealSheaf pi_ I) {W : Sch} (g : W ⟶ X) (hg : IsLocallyGeneratedByNonZeroDivisor (comap I g))
noncomputable def IsBlowupAlongIdealSheaf.lift : W ⟶ X' :=
  (h.exists_lift g hg).choose

theorem IsBlowupAlongIdealSheaf.lift_comp :
    h.lift g hg ≫ pi_ = g :=
  (h.exists_lift g hg).choose_spec

end

theorem IsBlowupAlongIdealSheaf.hom_ext {X X' : Sch} {pi_ : X' ⟶ X} {I : ISD X}
    (h : IsBlowupAlongIdealSheaf pi_ I) {W : Sch} {g : W ⟶ X}
    (hg : IsLocallyGeneratedByNonZeroDivisor $ comap I g) {a b : W ⟶ X'}
    (ha : a ≫ pi_ = g) (hb : b ≫ pi_ = g) : a = b :=
  h.hom_ext_of_comp_eq hg ha hb

theorem IsBlowupAlongIdealSheaf.comp_iso_hom {X X' Y : Sch} {pi_ : X' ⟶ X} {I : ISD X}
    (h : IsBlowupAlongIdealSheaf pi_ I) (e : X ≅ Y) :
    IsBlowupAlongIdealSheaf (pi_ ≫ e.hom) $ comap I e.inv := by
  constructor
  rw [← comap_comp, assoc, e.hom_inv_id, comp_id]
  exact an1 h
  intro W g hg
  rw [← comap_comp] at hg
  obtain ⟨a, ha, hu⟩ := an2 h W (g ≫ isoI e) hg
  refine ⟨a, ?_, ?_⟩
  show a ≫ pi_ ≫ isoH e = g
  rw [← assoc, ha, assoc, e.inv_hom_id, comp_id]
  intro b hb
  refine hu b ?_
  rw [← hb]
  simp

theorem IsBlowupAlongIdealSheaf.pullback_snd_of_isOpenImmersion {X X' U : Sch} {pi_ : X' ⟶ X} {I : ISD X}
    (h : IsBlowupAlongIdealSheaf pi_ I) (f : U ⟶ X) [IsOpenImmersion f] :
    IsBlowupAlongIdealSheaf (pullback.snd pi_ f) $ comap I f := by
  let _a0 := pullback.fst pi_ f
  constructor
  have h1 : comap (cmI I f) (pullback.snd pi_ f)
      = comap (cmI I pi_) _a0 := by
    rw [← comap_comp, ← comap_comp,
      pullback.condition]
  rw [h1]
  exact h.1.comap_of_isOpenImmersion _a0
  intro W g hg
  rw [← comap_comp] at hg
  obtain ⟨a, ha, hu⟩ := an2 h W (g ≫ f) hg
  refine ⟨pullback.lift a g ha, pullback.lift_snd _ _ _, ?_⟩
  intro b hb
  have hb' := hb
  refine pullback.hom_ext ?_ ?_
  rw [pullback.lift_fst]
  refine hu _ ?_
  dsimp
  rw [assoc, pullback.condition, ← assoc, hb']
  rw [pullback.lift_snd, hb']

theorem exists_isBlowupAlongIdealSheaf_spec_of_commRing (R : Type) [CommRing R]
    (I : IdealSheafData $ Sp R) :
    ∃ (Y : Sch) (pi_ : Y ⟶ Sp R), IsBlowupAlongIdealSheaf pi_ I := by
  obtain ⟨J, hJ⟩ : ∃ J, specIdealSheaf J = I := by
    refine ⟨m6 (GSpecIso $ m10 R).hom.hom
      (I.ideal ⟨⊤, isAffineOpen_top _⟩), ?_⟩
    refine m170 ?_
    rw [specIdealSheaf_ideal_top, ideal_map_inv_map_hom]
  refine ⟨affineBlowup J, p13 J, ?_⟩
  rw [← hJ]
  exact isBlowupAlongIdealSheaf_affineBlowup_toSpec J

theorem exists_isBlowupAlongIdealSheaf_spec (R : CRC) (I : IdealSheafData (Spec R)) :
    ∃ (Y : Sch) (pi_ : Y ⟶ Spec R), IsBlowupAlongIdealSheaf pi_ I :=
  exists_isBlowupAlongIdealSheaf_spec_of_commRing R I

theorem exists_isBlowupAlongIdealSheaf_of_isAffine (X : Sch) [IsAffine X] (I : ISD X) :
    ∃ (Y : Sch) (pi_ : Y ⟶ X), IsBlowupAlongIdealSheaf pi_ I := by
  obtain ⟨Y, pi_, hpi_⟩ := exists_isBlowupAlongIdealSheaf_spec Γ(X, ⊤) $ cmI I X.isoSpec.inv
  refine ⟨Y, pi_ ≫ X.isoSpec.inv, ?_⟩
  have h2 := hpi_.comp_iso_hom X.isoSpec.symm
  simp [symm_hom, Iso.symm_inv] at h2
  rwa [← comap_comp, hom_inv_id,
    comap_id] at h2

private theorem comp_base_apply {A B C : Sch} (u : A ⟶ B) (z : B ⟶ C) (p : A) :
    (u ≫ z).base p = z.base (u.base p) := by simp

theorem isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp {X P Z : Sch} (I : ISD X)
    (u : P ⟶ Z) [IsOpenImmersion u] (z : Z ⟶ X) (hz : IsLocallyGeneratedByNonZeroDivisor $ comap I z) :
    IsLocallyGeneratedByNonZeroDivisor $ comap I $ u ≫ z := by
  rw [comap_comp]
  exact hz.comap_of_isOpenImmersion u

theorem range_id_base (Z : Sch) :
    range ⇑(𝟙 Z : Z ⟶ Z).base = univ :=by simp_all
theorem pullback_hom_ext_of_mono {Z A B : Sch} (a : A ⟶ Z) (b : B ⟶ Z)
    [Mono a] [Mono b] {P : Sch} {u v : P ⟶ pullback a b}
    (h : u ≫ pullback.fst a b ≫ a = v ≫ pullback.fst a b ≫ a) : u = v := by
  have h1 := h
  rw [← assoc, ← assoc, cancel_mono a] at h1
  have h2 := h
  rw [pullback.condition, ← assoc, ← assoc, cancel_mono b] at h2
  exact pullback.hom_ext h1 h2

def IsBlowupAlongIdealSheafOver {X : Sch} (I : ISD X) (S : Opn X) {Z : Sch}
    (z : Z ⟶ X) : Prop :=
  range ⇑z.base ⊆ (S : Set X) ∧ IsLocallyGeneratedByNonZeroDivisor (comap I z) ∧
    ∀ {Y : Sch} (y : Y ⟶ X), IsLocallyGeneratedByNonZeroDivisor (comap I y) →
      range ⇑y.base ⊆ (S : Set X) → ∃! a : Y ⟶ Z, a ≫ z = y

section
variable {X Z : Sch} {I : ISD X}
section
variable {S : Opn X} {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver I S z) {Y : Sch} (y : Y ⟶ X) (hy : IsLocallyGeneratedByNonZeroDivisor (comap I y)) (hr : range ⇑y.base ⊆ (S : Set X))
include hz hy hr
theorem blowupOver_hom_ext
    {a b : Y ⟶ Z} (ha : a ≫ z = y) (hb : b ≫ z = y) : a = b := by
  obtain ⟨c, -, hu⟩ := hz.2.2 y hy hr
  rw [hu a ha, hu b hb]

noncomputable def liftOfIsBlowupAlongIdealSheafOver : Y ⟶ Z :=
  (hz.2.2 y hy hr).choose

theorem blowupOverLift_comp :
    liftOfIsBlowupAlongIdealSheafOver hz y hy hr ≫ z = y :=
  (hz.2.2 y hy hr).choose_spec.1
end

theorem blowupOver_of_isBlowupAlongIdealSheaf {W : Opn X}
    {p : Z ⟶ toScheme W} (h : IsBlowupAlongIdealSheaf p $ comap I W.i) : IsBlowupAlongIdealSheafOver I W $ p ≫ ι W := by
  have hrange := W.range_ι
  refine ⟨?_, ?_, ?_⟩
  rw [← hrange]
  rintro _ ⟨v, rfl⟩
  exact ⟨bsM p v, by simp⟩
  rw [comap_comp]
  exact an1 h
  intro Y y hy hry
  have hr : range y.base ⊆ range W.ib := by
    rwa [hrange]
  have hfac := lift_fac W.i y hr
  have hy2 : IsLocallyGeneratedByNonZeroDivisor $ comap (comap I W.i) $ m43 W.i y hr := by
    rwa [← comap_comp, hfac]
  obtain ⟨a, ha, hu⟩ := an2 h Y (m43 W.i y hr) hy2
  refine ⟨a, ?_, ?_⟩
  show a ≫ p ≫ opI W = y
  rw [← assoc, ha, hfac]
  intro b hb
  refine hu b ?_
  refine mp_ (cancel_mono W.i) ?_
  simp_all

theorem blowupOver_inf_preimage {S : Opn X}
    {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver I S z) (T : Opn X) :
    IsBlowupAlongIdealSheafOver I (S ⊓ T) $ ι (z ⁻¹ᵁ T) ≫ z := by
  let _a0 := opI $ preU z T
  refine ⟨?_, isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp I _ z hz.2.1, ?_⟩
  rintro _ ⟨p, rfl⟩
  rw [comp_base_apply]
  refine mpr_ mem_inf ⟨an1 hz $ mem_range_self _, ?_⟩
  let U := preU z T
  have h : opIb U p ∈ range U.ib := mem_range_self p
  rwa [q1] at h
  intro Y y hy hr
  have hrS : range y.base ⊆ S := fun p hp =>
    (mp_ mem_inf $ hr hp).1
  obtain ⟨a, ha, hu⟩ := hz.2.2 y hy hrS
  have hra : range a.base ⊆ range (preU z T).ib := by
    rw [q1]
    rintro _ ⟨p, rfl⟩
    show bsM z (bsM a p) ∈ T
    rw [← comp_base_apply, ha]
    exact an2 $ mp_ mem_inf $ hr $ mem_range_self p
  refine ⟨m43 _ a hra, ?_, ?_⟩
  show m43 (preU z T).i a hra ≫ (_a0 ≫ z) = y
  rw [← assoc, lift_fac, ha]
  intro b hb
  have hb' : (b ≫ _a0) ≫ z = y := by rw [assoc]
                                     exact hb
  exact mp_ (cancel_mono (preU z T).i) $ by rw [hu _ hb', lift_fac _ _ _]
end

section
variable {X : Sch} (I : ISD X)
section
variable (U : X.affineOpens)
theorem exists_isBlowupAlongIdealSheaf_affineOpen :
    ∃ (Z : Sch) (p : Z ⟶ toScheme (U : Opn X)),
      IsBlowupAlongIdealSheaf p $ comap I (U : Opn X).i := by
  exact exists_isBlowupAlongIdealSheaf_of_isAffine _ _

noncomputable def localBlowup :
    Sch :=
  (exists_isBlowupAlongIdealSheaf_affineOpen I U).choose

noncomputable def localBlowupProjection :
    localBlowup I U ⟶ toScheme (U : Opn X) :=
  (exists_isBlowupAlongIdealSheaf_affineOpen I U).choose_spec.choose

theorem isBlowupAlongIdealSheaf_localBlowupProj :
    IsBlowupAlongIdealSheaf (localBlowupProjection I U) $ comap I (U : Opn X).i :=
  (exists_isBlowupAlongIdealSheaf_affineOpen I U).choose_spec.choose_spec

noncomputable def localBlowupToBase :
    localBlowup I U ⟶ X :=
  localBlowupProjection I U ≫ ι (U : Opn X)

theorem blowupOver_localBlowupMap :
    IsBlowupAlongIdealSheafOver I (U : Opn X) $ localBlowupToBase I U :=
  blowupOver_of_isBlowupAlongIdealSheaf $ isBlowupAlongIdealSheaf_localBlowupProj I U
end

section
variable (i j : X.affineOpens)
noncomputable def overlap : (localBlowup I i).Opens :=
  (localBlowupToBase I i).pre (j : Opn X)

noncomputable def overlapInclusion : toScheme (overlap I i j) ⟶ localBlowup I i :=
  ι $ overlap I i j

theorem overlapIncl_eq :
    overlapInclusion I i j = ι (overlap I i j) := rfl

theorem isOpenImmersion_overlapIncl : IsOpenImmersion $ overlapInclusion I i j := by
  rw [overlapIncl_eq]
  infer_instance

noncomputable def overlapToBase : toScheme (overlap I i j) ⟶ X :=
  overlapInclusion I i j ≫ localBlowupToBase I i

theorem overlapMap_eq :
    overlapToBase I i j = overlapInclusion I i j ≫ localBlowupToBase I i := rfl

theorem blowupOver_overlapMap :
    IsBlowupAlongIdealSheafOver I ((i : Opn X) ⊓ (j : Opn X)) $ overlapToBase I i j :=
  blowupOver_inf_preimage (blowupOver_localBlowupMap I i) j

theorem range_overlapMap_subset_inf_swap :
    range ⇑(overlapToBase I i j).base ⊆ (((j : Opn X) ⊓ (i : Opn X)) : Set X) := by
  rintro _ ⟨p, rfl⟩
  let _a0 := mp_ mem_inf $ an1 (blowupOver_overlapMap I i j) $ mem_range_self p
  exact mpr_ mem_inf
    ⟨an2 _a0,
      an1 _a0⟩

noncomputable def overlapTransition : toScheme (overlap I i j) ⟶ toScheme (overlap I j i) :=
  liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap I j i) (overlapToBase I i j)
    (blowupOver_overlapMap I i j).2.1 $ range_overlapMap_subset_inf_swap I i j

theorem overlapTrans_comp_overlapMap :
    overlapTransition I i j ≫ overlapToBase I j i = overlapToBase I i j :=
  blowupOverLift_comp _ _ _ _
end

theorem isIso_overlapIncl_self
    (i : X.affineOpens) : IsIso $ overlapInclusion I i i := by
  have := isOpenImmersion_overlapIncl I i i
  have e2 : ((overlap I i i : Opn $ localBlowup I i) : Set $ localBlowup I i) = univ := by
    ext v
    simp [mem_univ, iff_true]
    exact an1 (blowupOver_localBlowupMap I i) $ mem_range_self v
  have h1 : range (overlapInclusion I i i).base
      = range (𝟙 (localBlowup I i) : localBlowup I i ⟶ localBlowup I i).base := by
    rw [overlapIncl_eq, q1, e2, range_id_base]
  have h2 := IsOpenImmersion.isoOfRangeEq_hom_fac (overlapInclusion I i i) (𝟙 $ localBlowup I i) h1
  rw [comp_id] at h2
  rw [← h2]
  infer_instance

theorem overlapTrans_self (i : X.affineOpens) :
    overlapTransition I i i = 𝟙 (toScheme $ overlap I i i) := by
  let _a0 := blowupOver_overlapMap I i i
  have := isOpenImmersion_overlapIncl I i i
  rw [← cancel_mono $ overlapInclusion I i i]
  refine blowupOver_hom_ext (blowupOver_localBlowupMap I i) (overlapToBase I i i)
    _a0.2.1 ?_ ?_ ?_
  rintro _ ⟨p, rfl⟩
  exact an1 $ mp_ mem_inf $ an1 _a0 $ mem_range_self p
  rw [assoc, ← overlapMap_eq, overlapTrans_comp_overlapMap]
  rw [id_comp, ← overlapMap_eq]

section
variable (i j k : X.affineOpens)
noncomputable def tripleOverlapToBase : pullback (overlapInclusion I i j) (overlapInclusion I i k) ⟶ X :=
  pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapToBase I i j

theorem overlapPullbackMap_eq :
    tripleOverlapToBase I i j k
      = pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapToBase I i j := rfl

theorem isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap :
    IsLocallyGeneratedByNonZeroDivisor $ comap I $ tripleOverlapToBase I i j k := by
  have := isOpenImmersion_overlapIncl I i j
  have := isOpenImmersion_overlapIncl I i k
  have h : tripleOverlapToBase I i j k
      = (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapInclusion I i j)
        ≫ localBlowupToBase I i := by
    rw [overlapPullbackMap_eq, overlapMap_eq, assoc]
  rw [h]
  exact isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp I _ (localBlowupToBase I i) (blowupOver_localBlowupMap I i).2.1

section
variable (p : ↥(pullback (overlapInclusion I i j) (overlapInclusion I i k)))
theorem overlapPullbackMap_base_mem_inf_left :
    (tripleOverlapToBase I i j k).base p ∈ ((i : Opn X) ⊓ (j : Opn X)) := by
  rw [overlapPullbackMap_eq, comp_base_apply]
  exact an1 (blowupOver_overlapMap I i j) $ mem_range_self _

theorem overlapPullbackMap_base_mem_inf_right :
    (tripleOverlapToBase I i j k).base p ∈ ((i : Opn X) ⊓ (k : Opn X)) := by
  have h : tripleOverlapToBase I i j k
      = pullback.snd (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapToBase I i k := by
    rw [overlapPullbackMap_eq, overlapMap_eq, overlapMap_eq, ← assoc,
      ← assoc, pullback.condition]
  rw [h, comp_base_apply]
  exact an1 (blowupOver_overlapMap I i k) $ mem_range_self _
end

theorem range_overlapPullbackMap_subset_source :
    range ⇑(tripleOverlapToBase I i j k).base ⊆ ((i : Opn X) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact an1 $ mp_ mem_inf $ overlapPullbackMap_base_mem_inf_left I i j k p

theorem range_overlapPullbackMap_subset_target :
    range ⇑(tripleOverlapToBase I i j k).base ⊆ ((j : Opn X) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact an2 $ mp_ mem_inf $ overlapPullbackMap_base_mem_inf_left I i j k p

theorem range_overlapPullbackMap_subset_inf :
    range ⇑(tripleOverlapToBase I i j k).base
      ⊆ (((j : Opn X) ⊓ (k : Opn X)) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact mpr_ mem_inf
    ⟨an2 $ mp_ mem_inf $ overlapPullbackMap_base_mem_inf_left I i j k p,
      (mp_ mem_inf $ overlapPullbackMap_base_mem_inf_right I i j k p).2⟩

noncomputable def tripleOverlapLift :
    pullback (overlapInclusion I i j) (overlapInclusion I i k) ⟶ toScheme (overlap I j k) :=
  liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap I j k) (tripleOverlapToBase I i j k)
    (isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap I i j k) $ range_overlapPullbackMap_subset_inf I i j k

theorem overlapPullbackLift_comp_overlapMap :
    tripleOverlapLift I i j k ≫ overlapToBase I j k = tripleOverlapToBase I i j k :=
  blowupOverLift_comp _ _ _ _

theorem overlapPullbackLift_comp_overlapIncl :
    tripleOverlapLift I i j k ≫ overlapInclusion I j k
      = (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j)
        ≫ overlapInclusion I j i := by
  refine blowupOver_hom_ext (blowupOver_localBlowupMap I j) (tripleOverlapToBase I i j k)
    (isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap I i j k) (range_overlapPullbackMap_subset_target I i j k) ?_ ?_
  rw [assoc, ← overlapMap_eq, overlapPullbackLift_comp_overlapMap]
  rw [assoc, ← overlapMap_eq, assoc, overlapTrans_comp_overlapMap,
    overlapPullbackMap_eq]

noncomputable def tripleOverlapTransition :
    pullback (overlapInclusion I i j) (overlapInclusion I i k)
      ⟶ pullback (overlapInclusion I j k) (overlapInclusion I j i) :=
  pullback.lift (tripleOverlapLift I i j k)
    (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j)
    (overlapPullbackLift_comp_overlapIncl I i j k)

theorem overlapTransPullback_eq :
    tripleOverlapTransition I i j k
      = pullback.lift (tripleOverlapLift I i j k)
          (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j)
          (overlapPullbackLift_comp_overlapIncl I i j k) := rfl

theorem overlapTransPullback_comp_snd :
    tripleOverlapTransition I i j k ≫ pullback.snd (overlapInclusion I j k) (overlapInclusion I j i)
      = pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j := by
  rw [overlapTransPullback_eq]
  exact pullback.lift_snd _ _ _

theorem overlapTransPullback_comp_overlapPullbackMap :
    tripleOverlapTransition I i j k ≫ tripleOverlapToBase I j k i
      = tripleOverlapToBase I i j k := by
  rw [overlapPullbackMap_eq, overlapTransPullback_eq, ← assoc, pullback.lift_fst,
    overlapPullbackLift_comp_overlapMap]

theorem overlapTransPullback_cocycle :
    tripleOverlapTransition I i j k ≫ tripleOverlapTransition I j k i ≫ tripleOverlapTransition I k i j
      = 𝟙 (pullback (overlapInclusion I i j) $ overlapInclusion I i k) := by
  have := isOpenImmersion_overlapIncl I i j
  have := isOpenImmersion_overlapIncl I i k
  refine pullback_hom_ext_of_mono (overlapInclusion I i j) (overlapInclusion I i k) ?_
  refine blowupOver_hom_ext (blowupOver_localBlowupMap I i) (tripleOverlapToBase I i j k)
    (isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap I i j k) (range_overlapPullbackMap_subset_source I i j k) ?_ ?_
  simp [assoc]
  rw [← overlapMap_eq, ← overlapPullbackMap_eq, overlapTransPullback_comp_overlapPullbackMap,
    overlapTransPullback_comp_overlapPullbackMap, overlapTransPullback_comp_overlapPullbackMap]
  simp [id_comp, assoc]
  rw [← overlapMap_eq, ← overlapPullbackMap_eq]
end

noncomputable def blowupGlueData : GlueData where
  toGlueData :=
    { J := X.affineOpens
      U := fun i => localBlowup I i
      V := fun p => (overlap I p.1 p.2).toScheme
      f := fun i j => overlapInclusion I i j
      f_mono := fun i j => by
        have := isOpenImmersion_overlapIncl I i j
        infer_instance
      f_hasPullback := fun i j k => by
        have := isOpenImmersion_overlapIncl I i j
        have := isOpenImmersion_overlapIncl I i k
        infer_instance
      f_id := fun i => isIso_overlapIncl_self I i
      t := fun i j => overlapTransition I i j
      t_id := fun i => overlapTrans_self I i
      t' := fun i j k => tripleOverlapTransition I i j k
      t_fac := fun i j k => overlapTransPullback_comp_snd I i j k
      cocycle := fun i j k => overlapTransPullback_cocycle I i j k }
  f_open := fun i j => isOpenImmersion_overlapIncl I i j

noncomputable def gluedBlowup : Sch :=
  (blowupGlueData I).glued

noncomputable def localBlowupToGlued
    (i : X.affineOpens) : localBlowup I i ⟶ gluedBlowup I :=
  (blowupGlueData I).ι i

theorem isOpenImmersion_gluedIncl
    (i : X.affineOpens) : IsOpenImmersion $ localBlowupToGlued I i :=
  (blowupGlueData I).ι_isOpenImmersion i

theorem overlapTrans_comp_gluedIncl (i j : X.affineOpens) :
    overlapTransition I i j ≫ overlapInclusion I j i ≫ localBlowupToGlued I j
      = overlapInclusion I i j ≫ localBlowupToGlued I i :=
  (blowupGlueData I).glue_condition i j

theorem gluedIncl_jointly_surjective
    (p : gluedBlowup I) :
    ∃ j y, (localBlowupToGlued I j).base y = p := by
  obtain ⟨j, y, hy⟩ := (blowupGlueData I).ι_jointly_surjective p
  exact ⟨j, y, hy⟩

theorem pullback_fst_comp_localBlowupMap_eq
    x y :
    pullback.fst (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I x
      = pullback.snd (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I y := by
  let _a1 := localBlowupToGlued I x
  let _a2 := localBlowupToGlued I y
  obtain ⟨m, hm1, hm2⟩ := PullbackCone.IsLimit.lift' ((blowupGlueData I).vPullbackConeIsLimit x y)
    (pullback.fst _a1 _a2)
    (pullback.snd _a1 _a2) pullback.condition
  let _a0 := overlapTransition I x y ≫ overlapInclusion I y x
  let _a3 := localBlowupToBase I x
  let _a4 := localBlowupToBase I y
  have key : overlapInclusion I x y ≫ _a3
      = _a0 ≫ _a4 := by
    rw [assoc]
    exact sy_ $ overlapTrans_comp_overlapMap I x y
  exact tr_ ((st_ $ congrArg (fun t => t ≫ _a3) hm1) $ assoc m (overlapInclusion I x y) _a3) $ tr_ (congrArg (fun t => m ≫ t) key) ((st_ $ congrArg (fun t => t ≫ _a4) hm2) $ assoc m _a0 _a4).symm

noncomputable def gluedBlowupProjection :
    gluedBlowup I ⟶ X :=
  (blowupGlueData I).openCover.glueMorphisms (fun i => localBlowupToBase I i)
    (fun x y => pullback_fst_comp_localBlowupMap_eq I x y)

section
variable (i : X.affineOpens)
theorem gluedIncl_comp_gluedProj : localBlowupToGlued I i ≫ gluedBlowupProjection I = localBlowupToBase I i :=
  (blowupGlueData I).openCover.ι_glueMorphisms _ _ i

theorem gluedProj_base_gluedIncl (v : localBlowup I i) :
    (gluedBlowupProjection I).base ((localBlowupToGlued I i).base v) = (localBlowupToBase I i).base v := by
  rw [← comp_base_apply, gluedIncl_comp_gluedProj]

theorem mem_range_gluedIncl_of_mem
    (p : gluedBlowup I) (hp : (gluedBlowupProjection I).base p ∈ (i : Opn X)) :
    p ∈ range ⇑(localBlowupToGlued I i).base := by
  obtain ⟨j, y, hy⟩ := gluedIncl_jointly_surjective I p
  have h1 := hp
  rw [← hy, gluedProj_base_gluedIncl I j y] at h1
  have h2 : y ∈ range ⇑(overlapInclusion I j i).base := by
    rwa [overlapIncl_eq, q1]
  obtain ⟨v, hv⟩ := h2
  have hcb : bsM (overlapTransition I j i ≫ overlapInclusion I i j ≫ localBlowupToGlued I i) v
      = bsM (overlapInclusion I j i ≫ localBlowupToGlued I j) v := by
    rw [overlapTrans_comp_gluedIncl I j i]
  rw [comp_base_apply, comp_base_apply, comp_base_apply] at hcb
  refine ⟨bsM (overlapInclusion I i j) $ bsM (overlapTransition I j i) v, ?_⟩
  rwa [hcb, hv]
end
end

theorem comp_gluedIncl_eq_of_comp_localBlowupMap {X P : Sch} (I : ISD X)
    (x y : X.affineOpens) (q : P ⟶ X) (hq : IsLocallyGeneratedByNonZeroDivisor $ comap I q)
    (hx : range ⇑q.base ⊆ ((x : Opn X) : Set X))
    (hy : range ⇑q.base ⊆ ((y : Opn X) : Set X))
    {ax : P ⟶ localBlowup I x} {ay : P ⟶ localBlowup I y}
    (hax : ax ≫ localBlowupToBase I x = q) (hay : ay ≫ localBlowupToBase I y = q) :
    ax ≫ localBlowupToGlued I x = ay ≫ localBlowupToGlued I y := by
  let _a0 := liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap I x y) q hq fun w hw => mpr_ mem_inf ⟨hx hw, hy hw⟩
  have hb1 : _a0 ≫ overlapToBase I x y = q :=
    blowupOverLift_comp _ _ _ _
  have e1 : ax = _a0 ≫ overlapInclusion I x y := by
    refine blowupOver_hom_ext (blowupOver_localBlowupMap I x) q hq hx hax ?_
    rw [assoc, ← overlapMap_eq, hb1]
  have e2 : ay = (_a0 ≫ overlapTransition I x y)
      ≫ overlapInclusion I y x := by
    refine blowupOver_hom_ext (blowupOver_localBlowupMap I y) q hq hy hay ?_
    rw [assoc, ← overlapMap_eq, assoc, overlapTrans_comp_overlapMap, hb1]
  rw [e1, e2]
  simp [assoc, ← overlapTrans_comp_gluedIncl I x y]

section
variable {X W : Sch}
section
variable (g : W ⟶ X) (i : X.affineOpens)
noncomputable def preimageAffineOpen :
    W.Opens :=
  g.pre (i : Opn X)

noncomputable def preimageAffineOpenToBase :
    toScheme (preimageAffineOpen g i) ⟶ X :=
  ι (preimageAffineOpen g i) ≫ g

theorem preimageAffineOpenToBase_eq :
    preimageAffineOpenToBase g i = ι (preimageAffineOpen g i) ≫ g := rfl
end

theorem range_preimageAffineOpenToBase_subset (g : W ⟶ X) (i : X.affineOpens) :
    range ⇑(preimageAffineOpenToBase g i).base ⊆ ((i : Opn X) : Set X) := by
  rintro _ ⟨p, rfl⟩
  rw [preimageAffineOpenToBase_eq, comp_base_apply]
  let U := preimageAffineOpen g i
  have h : opIb U p ∈ range ⇑U.ib := mem_range_self p
  rwa [q1] at h

section
variable (I : ISD X) (g : W ⟶ X) (hg : IsLocallyGeneratedByNonZeroDivisor (comap I g)) (i : X.affineOpens)
noncomputable def localBlowupLift :
    toScheme (preimageAffineOpen g i) ⟶ localBlowup I i :=
  liftOfIsBlowupAlongIdealSheafOver (blowupOver_localBlowupMap I i) (preimageAffineOpenToBase g i) ((isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp I _ g hg))
    (range_preimageAffineOpenToBase_subset g i)

theorem liftChart_comp_localBlowupMap :
    localBlowupLift I g hg i ≫ localBlowupToBase I i = preimageAffineOpenToBase g i :=
  blowupOverLift_comp _ _ _ _
end

noncomputable def preimageAffineOpensCover (g : W ⟶ X) : W.OpenCover :=
  mkOfCovers X.affineOpens (fun i => toScheme $ preimageAffineOpen g i)
    (fun i => ι $ preimageAffineOpen g i)
    (fun w => by
      obtain ⟨i, hi⟩ := X.exists_affineOpens_mem $ g.base w
      have hw : w ∈ range ⇑(preimageAffineOpen g i).ib := by
        rw [Scheme.Opens.range_ι]
        exact hi
      obtain ⟨v, hv⟩ := hw
      exact ⟨i, v, hv⟩)

theorem hom_ext_of_preimageAffineOpen_io_comp (g : W ⟶ X) {Z : Sch} (a b : W ⟶ Z)
    (h : ∀ i : X.affineOpens, ι (preimageAffineOpen g i) ≫ a = ι (preimageAffineOpen g i) ≫ b) : a = b := by
  exact (preimageAffineOpensCover g).hom_ext a b h

section
variable (I : ISD X) (g : W ⟶ X) (hg : IsLocallyGeneratedByNonZeroDivisor (comap I g))
theorem liftChart_pullback_condition (x y : X.affineOpens) :
    pullback.fst (preimageAffineOpen g x).i (preimageAffineOpen g y).i ≫ (localBlowupLift I g hg x ≫ localBlowupToGlued I x)
      = pullback.snd (preimageAffineOpen g x).i (preimageAffineOpen g y).i
        ≫ (localBlowupLift I g hg y ≫ localBlowupToGlued I y) := by
  let _m0 := preimageAffineOpen g x
  let _m1 := preimageAffineOpen g y
  have hxy : pullback.fst _m0.i _m1.i ≫ preimageAffineOpenToBase g x
      = pullback.snd _m0.i _m1.i ≫ preimageAffineOpenToBase g y := by
    rw [preimageAffineOpenToBase_eq, preimageAffineOpenToBase_eq, ← assoc, ← assoc, pullback.condition]
  have hcart : IsLocallyGeneratedByNonZeroDivisor $ cmI I
      (pullback.fst _m0.i _m1.i ≫ preimageAffineOpenToBase g x) := by
    have h : pullback.fst _m0.i _m1.i ≫ preimageAffineOpenToBase g x
        = (pullback.fst _m0.i _m1.i ≫ opI _m0) ≫ g := by
      rw [preimageAffineOpenToBase_eq, assoc]
    rw [h]
    exact isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp I _ g hg
  have hrx : range ⇑(pullback.fst _m0.i _m1.i ≫ preimageAffineOpenToBase g x).base
      ⊆ (x : Set X) := by
    rintro _ ⟨p, rfl⟩
    rw [comp_base_apply]
    exact range_preimageAffineOpenToBase_subset g x $ mem_range_self _
  have hry : range ⇑(pullback.fst _m0.i _m1.i ≫ preimageAffineOpenToBase g x).base
      ⊆ (y : Set X) := by
    rw [hxy]
    rintro _ ⟨p, rfl⟩
    rw [comp_base_apply]
    exact range_preimageAffineOpenToBase_subset g y $ mem_range_self _
  rw [← assoc, ← assoc]
  refine comp_gluedIncl_eq_of_comp_localBlowupMap I x y
    (pullback.fst _m0.i _m1.i ≫ preimageAffineOpenToBase g x) hcart hrx hry ?_ ?_
  rw [assoc, liftChart_comp_localBlowupMap]
  rw [assoc, liftChart_comp_localBlowupMap, hxy]

noncomputable def gluedBlowupLift : W ⟶ gluedBlowup I :=
  (preimageAffineOpensCover g).glueMorphisms (fun i => localBlowupLift I g hg i ≫ localBlowupToGlued I i)
    (fun x y => liftChart_pullback_condition I g hg x y)

theorem io_comp_liftGlued (i : X.affineOpens) :
    ι (preimageAffineOpen g i) ≫ gluedBlowupLift I g hg = localBlowupLift I g hg i ≫ localBlowupToGlued I i :=
  (preimageAffineOpensCover g).ι_glueMorphisms _ _ i

theorem liftGlued_comp_gluedProj : gluedBlowupLift I g hg ≫ gluedBlowupProjection I = g := by
  refine hom_ext_of_preimageAffineOpen_io_comp g (gluedBlowupLift I g hg ≫ gluedBlowupProjection I) g fun i => ?_
  rw [← assoc, io_comp_liftGlued, assoc, gluedIncl_comp_gluedProj, liftChart_comp_localBlowupMap,
    preimageAffineOpenToBase_eq]

theorem eq_liftGlued_of_comp_eq (b : W ⟶ gluedBlowup I)
    (hb : b ≫ gluedBlowupProjection I = g) : b = gluedBlowupLift I g hg := by
  refine hom_ext_of_preimageAffineOpen_io_comp g b (gluedBlowupLift I g hg) fun i => ?_
  rw [io_comp_liftGlued]
  let _m0 := opI (preimageAffineOpen g i) ≫ b
  let _a3 := localBlowupToGlued I i
  have hr : range ⇑_m0.base ⊆ range ⇑_a3.base := by
    rintro _ ⟨p, rfl⟩
    refine mem_range_gluedIncl_of_mem I i _ ?_
    rw [← comp_base_apply, assoc, hb]
    exact range_preimageAffineOpenToBase_subset g i $ mem_range_self p
  have := isOpenImmersion_gluedIncl I i
  let _a1 := m43 _a3 _m0 hr
  have hc : _a1 ≫ _a3
      = opI (preimageAffineOpen g i) ≫ b := lift_fac _ _ _
  have hc2 : _a1 ≫ localBlowupToBase I i
      = preimageAffineOpenToBase g i := by
    rw [← gluedIncl_comp_gluedProj I i, ← assoc, hc, assoc, hb, preimageAffineOpenToBase_eq]
  rw [← hc, blowupOver_hom_ext (blowupOver_localBlowupMap I i) (preimageAffineOpenToBase g i) (isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp I _ g hg) (range_preimageAffineOpenToBase_subset g i) hc2 $ liftChart_comp_localBlowupMap I g hg i]
end
end

theorem isBlowupAlongIdealSheaf_gluedProj {X : Sch} (I : ISD X) :
    IsBlowupAlongIdealSheaf (gluedBlowupProjection I) I := by
  constructor
  have : ∀ i, IsOpenImmersion $ localBlowupToGlued I i := fun i =>
    isOpenImmersion_gluedIncl I i
  refine IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover (cmI I $ gluedBlowupProjection I)
    (localBlowup I) (localBlowupToGlued I) ?_ ?_
  intro p
  obtain ⟨j, y, hy⟩ := gluedIncl_jointly_surjective I p
  exact ⟨j, y, hy⟩
  intro i
  rw [← comap_comp, gluedIncl_comp_gluedProj]
  exact (blowupOver_localBlowupMap I i).2.1
  intro W g hg
  exact ⟨gluedBlowupLift I g hg, liftGlued_comp_gluedProj I g hg,
    fun b hb => eq_liftGlued_of_comp_eq I g hg b hb⟩

theorem exists_isBlowupAlongIdealSheaf (X : Sch) (I : ISD X) :
    ∃ (Y : Sch) (pi_ : Y ⟶ X), IsBlowupAlongIdealSheaf pi_ I :=
  ⟨gluedBlowup I, gluedBlowupProjection I, isBlowupAlongIdealSheaf_gluedProj I⟩

section

variable {X : Sch} (I : ISD X)
noncomputable def blowup : Sch :=
  (exists_isBlowupAlongIdealSheaf X I).choose

noncomputable def blowup.proj : blowup I ⟶ X :=
  (exists_isBlowupAlongIdealSheaf X I).choose_spec.choose

end

theorem blowup.isBlowupAlongIdealSheaf_proj {X : Sch} (I : ISD X) :
    IsBlowupAlongIdealSheaf (blowup.proj I) I :=
  (exists_isBlowupAlongIdealSheaf X I).choose_spec.choose_spec

end FunctorialResolution.Blowup
end
section

namespace FunctorialResolution.Blowup

theorem comap_io_support_compl_eq_top {X : Sch} (Z : ISD X) :
    comap Z (Scheme.Opens.i Z.support.compl) = ⊤ := by
  exact comap_eq_top_of_notMem_support _ Z fun x => x.2

theorem blowupIsIsoOffCenter : BlowupIsIsoOffCenter := by
  intro X X' pi_ Z h
  have h1 := h.restrict $ suppC Z
  rw [comap_io_support_compl_eq_top Z] at h1
  exact h1.isIso_of_top

end FunctorialResolution.Blowup
end
section

namespace FunctorialResolution.Blowup

theorem map_inv_map_hom_eq_self {A B : CRC} (e : A ≅ B) (K : Ideal ↑A) :
    Ideal.map (hom e.inv) (Ideal.map (hom e.hom) K) = K := by
  rw [map_map, ← hom_comp, e.hom_inv_id, hom_id, map_id]

theorem exists_isBlowupAlongIdealSheaf_isProper_spec_of_isNoetherianRing (A : Type) [CommRing A]
    [IsNoetherianRing A] (I : IdealSheafData $ Sp A) :
    ∃ (Y : Sch) (pi_ : Y ⟶ Sp A),
      IsBlowupAlongIdealSheaf pi_ I ∧ IsProper pi_ := by
  obtain ⟨J, hJ⟩ : ∃ J, specIdealSheaf J = I := by
    let _a0 := GSpecIso $ m10 A
    refine ⟨m6 (hom _a0.hom)
      (I.ideal ⟨⊤, isAffineOpen_top $ Sp A⟩), ?_⟩
    rw [specIdealSheaf_eq_ofIdealTop, map_inv_map_hom_eq_self _a0]
    exact m170 $ by simp
  refine ⟨affineBlowup J, p13 J, ?_,
    isProper_affineBlowup_toSpec J⟩
  rw [← hJ]
  exact FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec J

theorem isProper_of_isBlowupAlongIdealSheaf_of_isAffine {Y B : Sch} [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : ISD Y) {p : B ⟶ Y} (h : IsBlowupAlongIdealSheaf p J) :
    IsProper p := by
  obtain ⟨Y', pi_, hpi_, hproper⟩ :=
    by
    exact exists_isBlowupAlongIdealSheaf_isProper_spec_of_isNoetherianRing (↑(Γ(Y, ⊤))) $ cmI J Y.isoSpec.inv
  have hq := h.comp_iso_hom Y.isoSpec
  obtain ⟨b, hb⟩ := hpi_.exists_lift (p ≫ Y.isoSpec.hom) hq.1
  obtain ⟨a, ha⟩ := hq.exists_lift pi_ hpi_.1
  have hab : a ≫ b = 𝟙 Y' := by
    refine hpi_.hom_ext hpi_.1 ?_ ?_
    simp_all
    rw [id_comp]
  have hba : b ≫ a = 𝟙 B := by
    refine hq.hom_ext hq.1 ?_ ?_
    simp_all
    rw [id_comp]
  have : IsIso b := ⟨a, hba, hab⟩
  have hp : b ≫ pi_ ≫ Y.isoSpec.inv = p := by
    rw [← assoc, hb, assoc, hom_inv_id, comp_id]
  rw [← hp]
  infer_instance

theorem isProper_morphismRestrict_of_isProper_pullbackSnd {X X' : Sch} (f : X' ⟶ X)
    (U : Opn X) (h : IsProper $ pullback.snd f U.i) :
    IsProper $ morphismRestrict f U := by
  refine mp_ (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
    (AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom
    (morphismRestrict f U)) ?_
  simp_all

theorem isNoetherianRing_sections_top_of_affineOpen {X : Sch}
    [IsLocallyNoetherian X] (U : X.affineOpens) :
    IsNoetherianRing Γ(toScheme (U : Opn X), ⊤) := by
  have :=
    m188 U
  exact isNoetherianRing_of_ringEquiv _
    (commRingCatIsoToRingEquiv $ (U : Opn X).topIso).symm

theorem blowupIsProper : BlowupIsProper := by
  intro X X' hX pi_ Z hZ
  have := hX
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper)
    (fun U : affO X => U) (AlgebraicGeometry.iSup_affineOpens_eq_top X) ?_
  intro U
  have := U.2
  have := isNoetherianRing_sections_top_of_affineOpen U
  exact isProper_morphismRestrict_of_isProper_pullbackSnd pi_ (U : Opn X)
    (isProper_of_isBlowupAlongIdealSheaf_of_isAffine (cmI Z (U : Opn X).i)
      (hZ.pullback_snd_of_isOpenImmersion (U : Opn X).i))


end FunctorialResolution.Blowup
end
section


namespace FunctorialResolution.EmbeddedResolution

section

variable {k K : Type} [Field k] [Field K] {ph_ : CommRingCat.of k ⟶ CommRingCat.of K}
  {X Y : Sch} {p : X ⟶ Sp k} {q : Y ⟶ Sp K}
  {f : Y ⟶ X}

theorem presheafMap_eq_id {Z : Sch} {A : (Z.Opens)ᵒᵖ} (g : A ⟶ A) :
    Z.presheaf.map g = 𝟙 _ := by
  obtain rfl : g = 𝟙 A := m111 g $ 𝟙 A
  exact Z.presheaf.map_id A

private theorem io_appLE_eq_topIso_inv {Z : Sch} (A : Opn Z)
    e : A.ι.appLE A ⊤ e = A.topIso.inv := by
  simp
  exact presheaf_map_eq_of_parallel _ _ _

section
variable {Z W : Sch} (g : Z ⟶ W)
private theorem appLE_top_eq_appTop
    e : appLE g ⊤ ⊤ e = appTop g := by
  let _a0 := pMap Z (homOfLE e).op
  have h1 : _a0 = 𝟙 Γ(Z, ⊤) := presheafMap_eq_id _
  calc g.appLE ⊤ ⊤ e = g.app ⊤ ≫ _a0 := rfl
    _ = hAT g := by rw [h1]
                    exact comp_id _

theorem appLE_of_le_eq_appLE_comp_presheaf_map (A : Opn W)
    (B C : Opn Z) (e : B ≤ g.pre A) (hCB : C ≤ B) (hCA : C ≤ g.pre A) :
    g.appLE A C hCA = g.appLE A B e ≫ Z.presheaf.map (homOfLE hCB).op := by
  let _a0 := Z.presheaf.map (homOfLE hCA).op
  have hL : g.appLE A C hCA = g.app A ≫ _a0 := rfl
  have hR : g.appLE A B e = g.app A ≫ Z.presheaf.map (homOfLE e).op := rfl
  have hmap : Z.presheaf.map ((homOfLE e).op ≫ (homOfLE hCB).op)
      = _a0 :=
    presheaf_map_eq_of_parallel _ _ _
  rw [hL, hR, assoc, ← m222, hmap]
end

section
variable (g : Y ⟶ X) {U} {m} (c : EtaleChart p U m)
def baseChangeCoords :
    UFin m → Γ(↑(pre g U), ⊤) :=
  fun i => (pre g U).topIso.inv.hom $ (appLE g U (pre g U) le_rfl).hom $ c.coord i.down

theorem baseChangeCoords_apply
    (i : UFin m) :
    baseChangeCoords g c i =
      (pre g U).topIso.inv.hom ((appLE g U (pre g U) le_rfl).hom $ c.coord i.down) :=
  rfl
end

theorem appLE_comp_appLE {X1 X2 X3 : Sch} (a : X1 ⟶ X2) (b : X2 ⟶ X3)
    {A} {B} {C} e1_ e2_
    e3_ :
    appLE b A B e1_ ≫ appLE a B C e2_ = appLE (a ≫ b) A C e3_ := by
  rw [m91]

theorem appTop_topIso_inv_of_comp_eq {Z W : Sch} (g : Z ⟶ W) {A : Opn W}
    {B : Opn Z} e (r : toScheme B ⟶ toScheme A) (hr : r ≫ ι A = ι B ≫ g)
    x :
    r.appTop.hom (A.topIso.inv.hom x) = B.topIso.inv.hom ((appLE g A B e).hom x) := by
  have eA : (⊤ : A.toScheme.Opens) ≤ opPre A A := by intro z _
                                                     exact z.2
  let _m0 := (⊤ : B.toScheme.Opens)
  have eB : _m0 ≤ opPre B B := by intro z _
                                  exact z.2
  have eTop : _m0 ≤ preU r (⊤) := by simp
  have e4 : _m0 ≤ preU (opI B ≫ g) A := by intro z _
                                           exact e z.2
  have e3 : _m0 ≤ preU (r ≫ opI A) A := by rw [hr]
                                           exact e4
  have hgen : ∀ m1 m2 : oSch B ⟶ W, m1 = m2 →
      ∀ k1_ k2_,
        appLE m1 A ⊤ k1_ = appLE m2 A ⊤ k2_ := by
    rintro m1 m2 rfl _ _
    rfl
  have key : A.topIso.inv ≫ appTop r = appLE g A B e ≫ B.topIso.inv := by
    rw [← io_appLE_eq_topIso_inv A eA, ← io_appLE_eq_topIso_inv B eB,
      ← appLE_top_eq_appTop r eTop, appLE_comp_appLE r A.i eA eTop e3,
      appLE_comp_appLE B.i g e eB e4]
    exact hgen _ _ hr e3 e4
  have h2 := congrArg (fun ps_ : W.sec A ⟶ Γ(toScheme B, ⊤) => ps_.hom x) key
  simp only [hom_comp, comp_apply] at h2
  exact h2

theorem etale_homOfVector_baseChangeCoords (hsq : IsPullback q f (Spec.map ph_) p)
    {U : Opn X} {m} (c : EtaleChart p U m) :
    Etale
      (AffineSpace.homOfVector (ι (f ⁻¹ᵁ U) ≫ q) $ baseChangeCoords f c) := by
  let _a1 := opI $ preU f U
  have hrio : (mrU f U) ≫ opI U = _a1 ≫ f := morphismRestrict_ι f U
  have hover : m52 (opI (preU f U) ≫ q) (baseChangeCoords f c)
      ≫ affineSpaceFinToSpec K m = opI (preU f U) ≫ q := m179 _ _
  have hmo : m228 (UFin m) (m12 ph_) ≫ affineSpaceFinToSpec k m
      = affineSpaceFinToSpec K m ≫ m12 ph_ := by simp
  have hL2 : (m52 (opI (preU f U) ≫ q) (baseChangeCoords f c)
        ≫ m228 (UFin m) (m12 ph_)) ≫ affineSpaceFinToSpec k m
      = opI (preU f U) ≫ q ≫ m12 ph_ := by
    rw [assoc, hmo, ← assoc, hover, assoc]
  have hR2 : ((mrU f U) ≫ c.map) ≫ affineSpaceFinToSpec k m = _a1 ≫ f ≫ p := by
    rw [assoc, c.comp_struct, ← assoc, hrio, assoc]
  have ecomm : m52 (opI (preU f U) ≫ q) (baseChangeCoords f c)
      ≫ m228 (UFin m) (m12 ph_) = (mrU f U) ≫ c.map := by
    refine m46 ?_ ?_
    refine tr_ hL2 ?_
    rw [hsq.w]
    exact sy_ hR2
    intro i
    have hmc : (m228 (UFin m) $ m12 ph_).appTop.hom
          (m9 (Sp k) i)
        = m9 (Sp K) i := by simp
    have hc : c.map.appTop.hom (m9 (Sp k) i)
        = U.topIso.inv.hom (c.coord i.down) := by
      rw [EtaleChart.coord_def]
      exact sy_ $ inv_hom_apply ..
    simp only [comp_appTop, m225,
      m82]
    rw [hmc, m87 _ _ i, hc, baseChangeCoords_apply]
    exact sy_ $ appTop_topIso_inv_of_comp_eq (A := U) (B := preU f U) f le_rfl (mrU f U) hrio
      (c.coord i.down)
  have sqBig := (isPullback_morphismRestrict f U).flip.paste_horiz hsq
  rw [← c.comp_struct, ← hover] at sqBig
  exact of_isPullback
    (P := @Etale) (sqBig.of_right ecomm $ (AffineSpace.isPullback_map (n := UFin m) $ m12 ph_).flip).flip c.isEtale

section
variable {U} {m} (c : EtaleChart p U m) (hsq : IsPullback q f (Spec.map ph_) p)
def EtaleChart.baseChange : EtaleChart q (pre f U) m :=
  EtaleChart.ofCoords q (pre f U) (baseChangeCoords f c)
    (etale_homOfVector_baseChangeCoords hsq c)

theorem EtaleChart.baseChange_map :
    (c.baseChange hsq).map =
      AffineSpace.homOfVector (ι (f ⁻¹ᵁ U) ≫ q) (baseChangeCoords f c) :=
  EtaleChart.ofCoords_map q (preU f U) (baseChangeCoords f c)
    (etale_homOfVector_baseChangeCoords hsq c)

@[simp] theorem EtaleChart.baseChange_coord (j : Fin m) :
    (c.baseChange hsq).coord j = (appLE f U (pre f U) le_rfl).hom (c.coord j) := by
  have h1 := m87 (opI (preU f U) ≫ q) (baseChangeCoords f c)
    $ ULift.up j
  rw [EtaleChart.coord_def, EtaleChart.baseChange_map, h1,
    baseChangeCoords_apply f c $ ULift.up j]
  exact hom_inv_apply ..
end

section
variable {Z : Sch} {V : Opn Z} (hV : IsAffineOpen V) (D : ISD Z)
theorem restrictIdeal_eq_top_of_ideal_eq_top (hD : D.ideal ⟨V, hV⟩ = ⊤) :
    restrictIdeal D V = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤) ≤ opPre V V := by simp_all
  apply m170
  rw [restrictIdeal_eq_comap_io,
    p32 D V.i ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, hD, m166]
  simp

private theorem ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top (hD : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤) ≤ opPre V V := by simp_all
  have hD' := hD
  rw [restrictIdeal_eq_comap_io] at hD'
  let _a0 := D.ideal ⟨V, hV⟩
  have h1 : Ideal.map (V.ι.appLE V ⊤ e1).hom _a0 = ⊤ := by
    rw [← comap_ideal_eq_map_appLE D V.i ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, hD']
    simp
  rw [io_appLE_eq_topIso_inv] at h1
  have h2 : Ideal.map V.topIso.hom.hom (Ideal.map V.topIso.inv.hom _a0)
      = _a0 := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]
  rw [h1, Ideal.map_top] at h2
  exact sy_ h2
end

section
variable (hsq : IsPullback q f (Spec.map ph_) p)
include hsq
theorem exists_etaleChart_of_isPullback
    {U : Opn X} {m : ℕ} (c : EtaleChart p U m) (y : ↥Y) (hy : f.base y ∈ U) :
    ∃ (V : Opn Y) (hV : V ≤ pre f U) (c' : EtaleChart q V m),
      IsAffineOpen V ∧ y ∈ V ∧
        ∀ j : Fin m, c'.coord j = (appLE f U V hV).hom (c.coord j) := by
  have hymem : y ∈ (preU f U) := hy
  obtain ⟨V, hVaff, hyV, hVsub⟩ := m227 hymem
  have hV : V ≤ preU f U := hVsub
  refine ⟨V, hV, (c.baseChange hsq).restrict hV, hVaff, hyV, fun j => ?_⟩
  let _a0 := appLE f U (preU f U) le_rfl
  let _a1 := pMap Y (homOfLE hV).op
  have happ : appLE f U V hV
      = _a0 ≫ _a1 :=
    appLE_of_le_eq_appLE_comp_presheaf_map f U (preU f U) V le_rfl hV hV
  have h2 : (appLE f U V hV).hom (c.coord j)
      = _a1.hom
          (_a0.hom $ c.coord j) := by simp_all
  rw [EtaleChart.coord_restrict (c.baseChange hsq) hV j,
    EtaleChart.baseChange_coord c hsq j]
  exact sy_ h2

theorem inStrictNormalCrossingPositionAt_comap_of_isPullback
    (E : Bdy X) (y : ↥Y) (hy : InStrictNormalCrossingPositionAt p E $ f.base y) :
    InStrictNormalCrossingPositionAt q (E.map fun D => comap D f) y := by
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := hy.exists_etaleChart
  obtain ⟨W, hW, hxW, hWU⟩ := m227 hxU
  obtain ⟨V, hVW, c', hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_of_isPullback hsq (c.restrict hWU) y hxW
  refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨V, hyV, m, c', a, ?_, ?_, ?_⟩
  intro i hi j hj t h1 h2
  simp [length_map] at hi hj
  exact hinj i hi j hj t h1 h2
  intro i hi hai
  have hiE := by simpa using hi
  have hgi : (E.map fun D => cmI D f)[i]'hi = cmI (E[i]'hiE) f := by simp
  rw [hgi]
  refine restrictIdeal_eq_top_of_ideal_eq_top hVaff (cmI (E[i]'hiE) f) ?_
  rw [p32 (E[i]'hiE) f
    ⟨W, hW⟩ ⟨V, hVaff⟩ hVW, ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top hW (E[i]'hiE) $ restrictIdeal_eq_top_of_le (E[i]'hiE) hWU $ hnone i hiE hai, m166]
  intro i hi t hai
  have hiE := by simpa using hi
  have hgi : (E.map fun D => cmI D f)[i]'hi = cmI (E[i]'hiE) f := by simp
  rw [hgi]
  refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff c' (cmI (E[i]'hiE) f) {t} ?_
  rw [comap_ideal_eq_span_image (E[i]'hiE) f
    ⟨W, hW⟩ ⟨V, hVaff⟩ hVW _ $ EtaleChart.ideal_eq_span_coord (c.restrict hWU) hW (E[i]'hiE) {t} $ restrictIdeal_eq_restrict_coordIdeal_of_le hWU c (E[i]'hiE) {t} $ hsome i hiE t hai]
  congr 1
  rw [image_image]
  exact image_congr fun j _ => sy_ $ hcoord j
end

theorem inStrictNormalCrossingPosition_comap_of_isPullback [Smooth p]
    (hsq : IsPullback q f (Spec.map ph_) p) (E : Bdy X) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition q $ E.map fun D => comap D f := by
  let _a0 := (inStrictNormalCrossingPosition_iff p E).1 hE
  rw [inStrictNormalCrossingPosition_iff]
  constructor
  intro D hD
  rw [mem_map] at hD
  obtain ⟨D0_, hD0_, rfl⟩ := hD
  let D := D0_
  obtain ⟨i, hi, hEi⟩ := mem_iff_getElem.1 hD0_
  refine isSmoothDivisor_of_locally_coordIdeal (cmI D f) ?_
  intro y
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ :=
    (an2 _a0 $ bsM f y).exists_etaleChart
  obtain ⟨W, hWaff, hxW, hWU⟩ := m227 hxU
  obtain ⟨V, hVW, c', hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_of_isPullback hsq (c.restrict hWU) y hxW
  have hcomap :=
    comap_ideal_eq_map_appLE D f ⟨W, hWaff⟩
      ⟨V, hVaff⟩ hVW
  refine ⟨V, hyV, m, c', ?_⟩
  cases hai : a i with
  | none =>
      left
      have h1 := hnone i hi hai
      rw [hEi] at h1
      have h2 := restrictIdeal_eq_top_of_le D hWU h1
      have h3 := ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top hWaff D h2
      rw [h3, m166] at hcomap
      exact restrictIdeal_eq_top_of_ideal_eq_top hVaff (cmI D f) hcomap
  | some t =>
      right
      refine ⟨t, ?_⟩
      have h1 := hsome i hi t hai
      rw [hEi] at h1
      refine restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff c' (cmI D f) {t} ?_
      rw [hcomap, EtaleChart.ideal_eq_span_coord (c.restrict hWU) hWaff D {t} $ restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D {t} h1, m218, Set.image_image]
      exact congrArg m17 $ Set.image_congr fun j _ => sy_ $ hcoord j
  intro y
  exact inStrictNormalCrossingPositionAt_comap_of_isPullback hsq E y
    (an2 _a0 $ bsM f y)

end

section

variable {k K : Type} [Field k] [Field K] {X : Sch} (p : X ⟶ Sp k)
section
variable (ph_ : CommRingCat.of k ⟶ CommRingCat.of K)
theorem isPullback_pullback_specMap :
    IsPullback (pullback.snd p $ Spec.map ph_) (pullback.fst p $ Spec.map ph_) (Spec.map ph_) p :=
  (m186 p $ m12 ph_).flip

end

section
variable [Smooth p] (ph_ : CommRingCat.of k ⟶ CommRingCat.of K)
theorem inStrictNormalCrossingPosition_comap_pullback_specMap
    (E : Bdy X) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition (pullback.snd p $ Spec.map ph_)
      (E.map fun D => comap D $ pullback.fst p $ Spec.map ph_) :=
  inStrictNormalCrossingPosition_comap_of_isPullback (isPullback_pullback_specMap p ph_) E hE

theorem smooth_pullbackSnd_specMap :
    Smooth $ pullback.snd p $ Spec.map ph_ :=
  by
  have hp : Smooth p := inferInstance
  exact of_isPullback (P := @Smooth)
    (isPullback_pullback_specMap p ph_).flip hp
end

end


namespace OpenImmersionRestriction

section
variable {V W : Sch}
section
variable (f : V ⟶ W) [IsOpenImmersion f] (D : ISD W)
theorem exists_subschemeMap_isOpenImmersion :
    ∃ g : subscheme (comap D f) ⟶ subscheme D,
      IsOpenImmersion g ∧ g ≫ subschemeι D = subschemeι (comap D f) ≫ f := by
  refine ⟨isoH (D.comapIso f) ≫ m47 f D.si, inferInstance, ?_⟩
  rw [assoc, ← condition, ← assoc,
    comapIso_hom_fst]

theorem isOpenImmersion_subschemeMap g
    (hg : g ≫ subschemeι D = subschemeι (comap D f) ≫ f) :
    IsOpenImmersion g := by
  obtain ⟨g', hg', hg'fac⟩ := exists_subschemeMap_isOpenImmersion f D
  have : Mono D.si := inferInstance
  have heq : g = g' := by
    refine mp_ (cancel_mono D.si) ?_
    rw [hg, hg'fac]
  rwa [heq]
end

theorem isSmoothDivisor_comap {k : Type} [Field k]
    (f : V ⟶ W) [IsOpenImmersion f] (p : W ⟶ Sp k)
    (D : ISD W) (hD : IsSmoothDivisor p D) :
    IsSmoothDivisor (f ≫ p) $ comap D f := by
  obtain ⟨g, hg, hgfac⟩ := exists_subschemeMap_isOpenImmersion f D
  refine ⟨hD.1.comap_of_isOpenImmersion f, ?_⟩
  have : Smooth g := inferInstance
  have hsm := an2 hD
  rw [← assoc, ← hgfac, assoc]
  infer_instance
end

end OpenImmersionRestriction




namespace HasSmoothCoordCodim

variable {k : Type} [Field k]

section
variable {X Y : Sch} (f : X ⟶ Y)
private theorem smooth_resLE [Smooth f]
    (U : Opn Y) : Smooth $ f.resLE U (pre f U) le_rfl := by
  rw [resLE_eq_morphismRestrict]
  exact m98 (P := @Smooth)
    (isPullback_morphismRestrict f U).flip ‹Smooth f›

theorem resLE_comp_ι (U : Opn Y) :
    f.resLE U (pre f U) le_rfl ≫ ι U = ι (f ⁻¹ᵁ U) ≫ f :=by simp_all
end

theorem ker_eq_comap_of_isPullback {X X' X'' X2} {ta_ : X ⟶ X'} [IsClosedImmersion ta_]
    {g} {ta'' : X2 ⟶ X''} {p} (H : IsPullback p ta'' ta_ g) :
    ta''.ker = ta_.ker.comap g := by
  rw [← ker_fst_of_isClosedImmersion ta_ g, ← H.flip.isoPullback_hom_fst,
    ker_comp_of_isIso]

theorem ker_resLE {X Y : Sch} (f : X ⟶ Y) [IsClosedImmersion f] (U : Opn Y) :
    (f.resLE U (pre f U) le_rfl).ker = f.ker.comap U.i := by
  rw [resLE_eq_morphismRestrict]
  exact ker_eq_comap_of_isPullback $ (isPullback_morphismRestrict f U).flip

theorem ker_comp_iso {X Y Z} (f : X ⟶ Y) [IsClosedImmersion f] (ph_ : Y ≅ Z) :
    (f ≫ ph_.hom).ker = f.ker.comap ph_.inv :=
  ker_eq_comap_of_isPullback (p := 𝟙 X) $ of_horiz_isIso ⟨by simp⟩

theorem resLE_open {X X' : Sch}
    {s : X' ⟶ Sp k} {ta_ : X ⟶ X'} [IsClosedImmersion ta_] {c : ℕ}
    (h : HasSmoothCoordCodim s ta_ c) (O : Opn X') :
    HasSmoothCoordCodim (ι O ≫ s) (ta_.resLE O (pre ta_ O) le_rfl) c := by
  let _a0 := ta_.resLE O (preU ta_ O) le_rfl
  let _a2 := coordSubspaceIdeal k c Finset.univ
  intro x
  let _a1 := opIb (preU ta_ O) x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h _a1
  have : Smooth O.i := inferInstance
  have : Smooth $ O.ι.resLE U (opPre O U) le_rfl := smooth_resLE O.i U
  have hw : opIb O (bsM _a0 x) = bsM ta_ _a1 :=
    congrArg (fun m : oSch (preU ta_ O) ⟶ X' => bsM m x) $ resLE_comp_ι ta_ O
  refine ⟨opPre O U, ?_, O.ι.resLE U (opPre O U) le_rfl ≫ q, inferInstance, ?_, ?_⟩
  show O.ib (bsM _a0 x) ∈ U
  rwa [hw]
  rw [assoc, hqs, ← assoc, resLE_comp_ι O.i U, assoc]
  calc restrictIdeal _a0.ker (O.i.pre U)
      = cmI (ta_.ker.comap O.i) (preU O.i U).i := by
        rw [restrictIdeal_eq_comap_io, ker_resLE]
    _ = ta_.ker.comap (opI (opI O ⁻¹ᵁ U) ≫ opI O) := by rw [comap_comp]
    _ = ta_.ker.comap (O.ι.resLE U (preU O.i U) le_rfl ≫ opI U) := by rw [resLE_comp_ι O.i U]
    _ = cmI (ta_.ker.comap U.i) (O.ι.resLE U (O.i.pre U) le_rfl) := by
        rw [comap_comp]
    _ = cmI (cmI _a2 q)
          (O.ι.resLE U (opI O ⁻¹ᵁ U) le_rfl) := by rw [← restrictIdeal_eq_comap_io, hker]
    _ = comap _a2
          (O.ι.resLE U (opI O ⁻¹ᵁ U) le_rfl ≫ q) := by rw [comap_comp]

theorem comp_iso_hom {X X' X'' : Sch}
    {s : X' ⟶ Sp k} {ta_ : X ⟶ X'} [IsClosedImmersion ta_] {c : ℕ}
    (h : HasSmoothCoordCodim s ta_ c) (ph_ : X' ≅ X'')
    (s' : X'' ⟶ Sp k) (hph : ph_.hom ≫ s' = s) :
    HasSmoothCoordCodim s' (ta_ ≫ ph_.hom) c := by
  let _a1 := coordSubspaceIdeal k c Finset.univ
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h x
  have : Smooth ph_.inv := inferInstance
  have hs' : isoI ph_ ≫ s = s' := by rw [← hph, inv_hom_id_assoc]
  refine ⟨ph_.inv.pre U, ?_, ph_.inv.resLE U (ph_.inv.pre U) le_rfl ≫ q, inferInstance, ?_, ?_⟩
  simp_all
  simp_all
  calc restrictIdeal (ta_ ≫ isoH ph_).ker (ph_.inv.pre U)
      = cmI (ta_.ker.comap ph_.inv) (ph_.inv.pre U).i := by
        rw [restrictIdeal_eq_comap_io, ker_comp_iso]
    _ = ta_.ker.comap (opI (preU ph_.inv U) ≫ isoI ph_) := by rw [comap_comp]
    _ = ta_.ker.comap (ph_.inv.resLE U (ph_.inv.pre U) le_rfl ≫ opI U) := by
        rw [resLE_comp_ι ph_.inv U]
    _ = cmI (ta_.ker.comap U.i) (ph_.inv.resLE U (ph_.inv.pre U) le_rfl) := by
        rw [comap_comp]
    _ = cmI (cmI _a1 q)
          (ph_.inv.resLE U (ph_.inv.pre U) le_rfl) := by rw [← restrictIdeal_eq_comap_io, hker]
    _ = comap _a1
          (ph_.inv.resLE U (ph_.inv.pre U) le_rfl ≫ q) := by rw [comap_comp]

theorem iso_hom_comp {X X' X0 : Sch}
    {s : X' ⟶ Sp k} {ta_ : X ⟶ X'} {c : ℕ}
    (h : HasSmoothCoordCodim s ta_ c) (e : X0 ≅ X) :
    HasSmoothCoordCodim s (e.hom ≫ ta_) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h $ ihB_ e x
  refine ⟨U, hU, q, hq, hqs, ?_⟩
  rw [restrictIdeal_eq_comap_io, ker_comp_of_isIso, ← restrictIdeal_eq_comap_io, hker]

end HasSmoothCoordCodim

end FunctorialResolution.EmbeddedResolution

end
section
universe v



namespace FunctorialResolution.EmbeddedResolution

section
variable {X X' : Sch} (f : X' ⟶ X) (S : Closeds X)
def closedPreimage :
    Closeds X' :=
  ⟨f.base ⁻¹' (S : Set X), S.isClosed.preimage f.continuous⟩

theorem closedPreimage_coe :
    (closedPreimage f S : Set X') = f.base ⁻¹' (S : Set X) := rfl

theorem reducedInverseImage_eq_vanishingIdeal_closedPreimage :
    reducedInverseImage f S = vanishingIdeal (closedPreimage f S) := rfl
end

theorem support_vanishingIdeal {X : Sch} (Z : Closeds X) :
    support (vanishingIdeal Z) = Z := rfl

section
variable {R S : Type} [CommRing R] [CommRing S]
section
variable (ph_ : R →+* S)
theorem isRadical_map_of_bijective
    (hph : Bijective ph_) {I : Ideal R} (hI : I.radical = I) :
    (Ideal.map ph_ I).radical = Ideal.map ph_ I := by
  refine le_antisymm ?_ le_radical
  intro y hy
  obtain ⟨m, hm⟩ := mp_ mem_radical_iff hy
  obtain ⟨z, rfl⟩ := an2 hph y
  rw [← map_pow] at hm
  obtain ⟨w, hw, hw2⟩ := mp_ (mem_map_iff_of_surjective ph_ hph.2) hm
  have hz : z ^ m ∈ I := by
    rwa [an1 hph hw2] at hw
  refine mem_map_of_mem _ ?_
  rw [← hI]
  exact mpr_ mem_radical_iff ⟨m, hz⟩

theorem ideal_eq_span_of_map_eq_span
    (ps_ : S →+* R) (hpsph : ∀ r, ps_ (ph_ r) = r) I b
    (hb : Ideal.map ph_ I = span {b}) : I = span {ps_ b} := by
  have h2 : Ideal.map ps_ (Ideal.map ph_ I) = I := by
    rw [map_map, show ps_.comp ph_ = RingHom.id R from RingHom.ext hpsph, map_id]
  rw [← h2, hb, map_span, image_singleton]
end

theorem isRegularParameterSystem_of_ringEquiv
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (v : Fin n → R) (w : Fin n → S)
    (hvw : ∀ i, e (v i) = w i) (hv : IsRegularParameterSystem R n v) :
    IsRegularParameterSystem S n w := by
  constructor
  have hw := funext fun i => sy_ $ hvw i
  rw [hw, show (range fun i => e $ v i) = e '' range v from
    range_comp _ _, ← map_span, an1 hv]
  exact IsLocalRing.map_ringEquiv_maximalIdeal e
  rw [an2 hv]
  exact ringKrullDim_eq_of_ringEquiv e
end

theorem isIso_appLE_image {X Y : Sch} (h : X ⟶ Y) [IsOpenImmersion h] U
    e :
    IsIso $ appLE h (h.im U) U e := by
  rw [show appLE h (imU h U) U e = isoH (h.appIso U) from sy_ $ appIso_hom' h U]
  infer_instance

theorem stalkMap_germ_eq_germ_appLE {X Y : Sch} (f : X ⟶ Y) U V
    e x (hx : x ∈ V)
    (hfx : f.base x ∈ U) s :
    f.stalkMap x (Y.presheaf.germ U (f.base x) hfx s)
      = X.presheaf.germ V x hx (appLE f U V e s) := by
  have key : pGerm Y U (bsM f x) hfx ≫ f.stalkMap x
      = f.app U ≫ pGerm X ((m54 f.base).obj U) x hfx := by
    simp
  have h1 : appLE f U V e s = pMap X (homOfLE e).op (f.app U s) := rfl
  rw [← m78, key, m78, h1, germ_res_apply]

section
variable {X' Y' : Sch} (h : X' ⟶ Y') [IsOpenImmersion h]
theorem comap_ideal_radical_eq_of_isOpenImmersion
    (I : ISD Y') (hI : I.radical = I) (V : X'.affineOpens) :
    ((comap I h).ideal V).radical = (comap I h).ideal V := by
  have he :=
    le_of_eq (preimage_image_eq h V.1).symm
  have := isIso_appLE_image h V.1 he
  rw [comap_ideal_eq_map_appLE I h ⟨imU h V.1, V.2.image_of_isOpenImmersion h⟩ V he]
  refine isRadical_map_of_bijective _
    (m189 $ appLE h (imU h V.1) V.1 he) ?_
  rw [← radical_ideal, hI]

theorem comap_vanishingIdeal_of_isOpenImmersion (Z : Closeds Y') :
    comap (vanishingIdeal Z) h
      = vanishingIdeal (closedPreimage h Z) := by
  have hZrad : (vanishingIdeal Z).radical
      = vanishingIdeal Z := by
    rw [← vanishingIdeal_support, support_vanishingIdeal]
  have hrad : (cmI (vanishingIdeal Z) h).radical
      = cmI (vanishingIdeal Z) h := by
    refine m29 $ funext fun V => ?_
    rw [radical_ideal]
    exact comap_ideal_radical_eq_of_isOpenImmersion h _ hZrad V
  have hsupp : support (cmI (vanishingIdeal Z) h)
      = closedPreimage h Z := by
    refine SetLike.ext fun x => ?_
    simp
    exact m22
  calc (vanishingIdeal Z).comap h
      = (cmI (vanishingIdeal Z) h).radical := sy_ hrad
    _ = vanishingIdeal
          (cmI (vanishingIdeal Z) h).support := by
        rw [vanishingIdeal_support]
    _ = vanishingIdeal (closedPreimage h Z) := by rw [hsupp]

theorem comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq (Z : Closeds Y') (Z' : Closeds X')
    (hZ' : (Z' : Set X') = h.base ⁻¹' (Z : Set Y')) :
    comap (vanishingIdeal Z) h
      = vanishingIdeal Z' := by
  have h1 : closedPreimage h Z = Z' := ext' $ by rw [closedPreimage_coe, hZ']
  rw [comap_vanishingIdeal_of_isOpenImmersion, h1]

theorem isStrictNormalCrossingsAt_base_of_comap
    (E : ISD Y') (hE : IsStrictNormalCrossingsDivisor (E.comap h)) (x : X') :
    IsRegularLocalRing (Y'.presheaf.stalk (h.base x)) ∧
      ∃ (U : Y'.affineOpens) (hy : h.base x ∈ U.1) (n : ℕ) (f : Fin n → Γ(Y', U.1))
        (J : FinSet n),
        IsRegularParameterSystem (Y'.presheaf.stalk (h.base x)) n
            (fun i => Y'.presheaf.germ U.1 (h.base x) hy (f i)) ∧
          E.ideal U = span {∏ i ∈ J, f i} := by
  obtain ⟨hreg, U', hx, n, g, J, hparams, hideal⟩ := hE x
  have := hreg
  have hU := U'.2.image_of_isOpenImmersion h
  have he :=
    le_of_eq (preimage_image_eq h U'.1).symm
  have hy : h.base x ∈ imU h U'.1 := ⟨x, hx, rfl⟩
  have := isIso_appLE_image h U'.1 he
  have : IsIso (h.stalkMap x) := inferInstance
  let ep_ :=
    (asIso (appLE h (imU h U'.1) U'.1 he)).commRingCatIsoToRingEquiv
  let ta_ :=
    (asIso (h.stalkMap x)).commRingCatIsoToRingEquiv
  have hgerm : ∀ i, ta_ (pGerm Y' (imU h U'.1) (h.base x) hy (ep_.symm (g i)))
      = pGerm X' U'.1 x hx (g i) := by
    intro i
    have h1 := stalkMap_germ_eq_germ_appLE h (imU h U'.1) U'.1 he x hx hy $ ep_.symm (g i)
    have h2 : (appLE h (imU h U'.1) U'.1 he) (ep_.symm (g i)) = g i := ep_.apply_symm_apply (g i)
    rwa [h2] at h1
  refine ⟨IsRegularLocalRing.of_ringEquiv ta_.symm, ⟨imU h U'.1, hU⟩, hy, n,
    fun i => ep_.symm (g i), J, ?_, ?_⟩
  refine isRegularParameterSystem_of_ringEquiv ta_.symm n
    (fun i => pGerm X' U'.1 x hx $ g i)
    (fun i => pGerm Y' (imU h U'.1) (h.base x) hy $ ep_.symm (g i)) ?_ hparams
  intro i
  rw [← hgerm i, ta_.symm_apply_apply]
  have hmap := comap_ideal_eq_map_appLE E h ⟨imU h U'.1, hU⟩ U' he
  rw [hideal] at hmap
  let _m0 := (ep_.symm : Γ(X', U'.1) →+* Γ(Y', imU h U'.1))
  have hprod : _m0 (∏ i ∈ J, g i)
      = ∏ i ∈ J, ep_.symm (g i) := map_prod _ _ _
  rw [ideal_eq_span_of_map_eq_span ((appLE h (imU h U'.1) U'.1 he).hom)
    _m0 ep_.symm_apply_apply
    (E.ideal ⟨imU h U'.1, hU⟩) (∏ i ∈ J, g i) hmap.symm, hprod]
end

theorem reducedInverseImage_comp {A B Z : Sch} (g : A ⟶ B) (f : B ⟶ Z)
    (W : Closeds Z) :
    reducedInverseImage (g ≫ f) W
      = vanishingIdeal (closedPreimage g $ closedPreimage f W) := by
  have h : closedPreimage (g ≫ f) W = closedPreimage g (closedPreimage f W) := by
    apply ext'
    show bsM (g ≫ f) ⁻¹' W = bsM g ⁻¹' (bsM f ⁻¹' W)
    ext p
    simp
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, h]

theorem comap_reducedInverseImage_of_isOpenImmersion {A B Z : Sch} (h : A ⟶ B)
    [IsOpenImmersion h] (f : B ⟶ Z) (W : Closeds Z) :
    comap (reducedInverseImage f W) h = reducedInverseImage (h ≫ f) W := by
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, comap_vanishingIdeal_of_isOpenImmersion,
    reducedInverseImage_comp]

theorem reducedInverseImage_eq_radical {T Y : Sch} (f : T ⟶ Y)
    (W : Closeds Y) (J : ISD T)
    (hJ : (support J : Set T) = f.base ⁻¹' (W : Set Y)) :
    reducedInverseImage f W = J.radical := by
  have h : spI J = closedPreimage f W := ext' hJ
  rw [reducedInverseImage_eq_vanishingIdeal_closedPreimage, ← h,
    vanishingIdeal_support]

theorem IsStrictNormalCrossingsDivisor.of_isOpenImmersion_jointly_surjective {X : Sch} (D : ISD X) {ι : Type v}
    (Y : ι → Sch) (p : ∀ i, Y i ⟶ X) (hp : ∀ i, IsOpenImmersion $ p i)
    (hsurj : ∀ x : X, ∃ (i : ι) (y : Y i), (p i).base y = x)
    (hD : ∀ i, IsStrictNormalCrossingsDivisor $ comap D $ p i) : IsStrictNormalCrossingsDivisor D := by
  intro x
  obtain ⟨i, y, hy⟩ := hsurj x
  subst hy
  exact isStrictNormalCrossingsAt_base_of_comap (p i) D (hD i) y

theorem IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod {A B Z : Sch} (g : (A ⨿ B) ⟶ Z)
    (W : Closeds Z)
    (hA : IsStrictNormalCrossingsDivisor $ reducedInverseImage ((coprod.inl : A ⟶ A ⨿ B) ≫ g) W)
    (hB : IsStrictNormalCrossingsDivisor $ reducedInverseImage ((coprod.inr : B ⟶ A ⨿ B) ≫ g) W) :
    IsStrictNormalCrossingsDivisor $ reducedInverseImage g W := by
  let _a0 := reducedInverseImage g W
  let _c0 := (coprod.inr : B ⟶ A ⨿ B)
  let _c1 := (coprod.inl : A ⟶ A ⨿ B)
  intro z
  by_cases hz : z ∈ range ⇑_c1.base
  obtain ⟨a, rfl⟩ := hz
  refine isStrictNormalCrossingsAt_base_of_comap _c1 _a0 ?_ a
  rwa [comap_reducedInverseImage_of_isOpenImmersion _ g W]
  have hz' : z ∈ range ⇑_c0.base := by
    rwa [Blowup.range_coprod_inr_eq_compl]
  obtain ⟨b, rfl⟩ := hz'
  refine isStrictNormalCrossingsAt_base_of_comap _c0 _a0 ?_ b
  rwa [comap_reducedInverseImage_of_isOpenImmersion _ g W]

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
theorem span_eq_top_of_isAffineOpen_of_forall_mem_basicOpen {U : Opn X}
    (hU : IsAffineOpen U) (s : Set $ X.sec U) (hcov : ∀ x ∈ U, ∃ g ∈ s, x ∈ basicOpen X g) :
    span s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := exists_le_maximal _ hne
  let _m0 := (⟨m, hm.isPrime⟩ : PrimeSpectrum U.sec)
  have hx : hU.fromSpec.base _m0 ∈ U := by
    have hr : hU.fromSpec.base _m0
        ∈ range hU.fromSpec.base := ⟨_, rfl⟩
    rwa [hU.range_fromSpec] at hr
  obtain ⟨g, hgs, hg⟩ := hcov _ hx
  have hmem : _m0 ∈ hU.fromSpec ⁻¹ᵁ bOpn X g := hg
  rw [hU.fromSpec_preimage_basicOpen] at hmem
  exact hmem $ hle $ m100 hgs

theorem exists_pow_mul_mem_of_map_mem (U : X.affineOpens)
    (g : Γ(X, U.1)) (Jid : Ideal Γ(X, U.1)) (s : Γ(X, U.1))
    (hs : (X.presheaf.map (homOfLE $ X.basicOpen_le g).op).hom s ∈
        Ideal.map (X.presheaf.map (homOfLE $ X.basicOpen_le g).op).hom Jid) :
    ∃ n : ℕ, g ^ n * s ∈ Jid := by
  let algUV :=
    (pMap X (homOfLE $ X.basicOpen_le g).op).hom.toAlgebra
  have hloc := U.2.isLocalization_basicOpen g
  obtain ⟨⟨⟨y, hy⟩, mm⟩, hEq⟩ :=
    (mem_map_algebraMap_iff (M := powers g)
      (S := Γ(X, bOpn X g))).mp hs
  let _a0 := Γ(X, U.1)
  let _m0 := s * mm
  have hEq' : algebraMap Γ(X, U.1) Γ(X, bOpn X g) _m0
      = algebraMap Γ(X, U.1) Γ(X, bOpn X g) y := by
    rwa [map_mul]
  obtain ⟨cc, hcc⟩ :=
    mp (eq_iff_exists (powers g) Γ(X, bOpn X g)) hEq'
  obtain ⟨n1_, hn1_⟩ := mp_ (mem_powers_iff (cc : _a0) g) cc.2
  obtain ⟨n2_, hn2_⟩ := mp_ (mem_powers_iff (mm : _a0) g) mm.2
  refine ⟨n1_ + n2_, ?_⟩
  have hrw : g ^ (n1_ + n2_) * s = cc * _m0 := by
    rw [pow_add, hn1_, hn2_]
    ring
  rw [hrw, hcc]
  exact mul_mem_left _ _ hy

section
variable (I J : ISD X)
theorem ideal_eq_of_le
    (V W : X.affineOpens) (h : (W : Opn X) ≤ (V : Opn X)) (hIJ : I.ideal V = J.ideal V) :
    I.ideal W = J.ideal W := by
  have e := by simpa using h
  have h1 := comap_ideal_eq_map_appLE I (𝟙 X) V W e
  have h2 := comap_ideal_eq_map_appLE J (𝟙 X) V W e
  rw [comap_id] at h1 h2
  rw [h1, h2, hIJ]

section
variable (h : ∀ x : ↥X, ∃ V : X.affineOpens, x ∈ (V : Opn X) ∧ I.ideal V = J.ideal V)
include h
theorem ideal_le_of_locally_eq
    (U : X.affineOpens) : I.ideal U ≤ J.ideal U := by
  intro s hs
  have hspan : span {g : Γ(X, U.1) | ∃ n, g ^ n * s ∈ J.ideal U} = ⊤ := by
    refine span_eq_top_of_isAffineOpen_of_forall_mem_basicOpen U.2 _ ?_
    intro x hx
    obtain ⟨V, hxV, hIJ⟩ := h x
    obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le (⟨x, hxV⟩ : ↥(V : Opn X)) hx
    let _a1 := pMap X (homOfLE $ X.basicOpen_le g).op
    have hres : _a1.hom s ∈
        Ideal.map _a1.hom (J.ideal U) := by
      rw [J.map_ideal_basicOpen U g, ← ideal_eq_of_le I J V (X.affineBasicOpen g) hgV hIJ, ← I.map_ideal_basicOpen U g]
      exact mem_map_of_mem _ hs
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_map_mem U g (J.ideal U) s hres
    exact ⟨g, ⟨n, hn⟩, hxg⟩
  obtain ⟨K, hK⟩ : ∃ K : Ideal Γ(X, U.1), ∀ a : Γ(X, U.1), a ∈ K ↔ a * s ∈ J.ideal U := by
    refine ⟨Submodule.comap (LinearMap.toSpanSingleton Γ(X, U.1) Γ(X, U.1) s) $ J.ideal U,
      fun a => ?_⟩
    simp [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hsub : span {g : Γ(X, U.1) | ∃ n, g ^ n * s ∈ J.ideal U} ≤ K.radical := by
    refine mpr_ span_le ?_
    rintro g ⟨n, hn⟩
    exact mpr_ mem_radical_iff ⟨n, mpr_ (hK _) hn⟩
  have htop := hsub
  rw [hspan, ← eq_top_iff] at htop
  have h1 : (1 : Γ(X, U.1)) ∈ K.radical := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨n, hn⟩ := mp_ mem_radical_iff h1
  have hone := by simpa using hn
  simpa using (hK 1).mp hone

private theorem idealSheafData_eq_of_locally_eq : I = J := by
  have h1 := fun U =>
    ideal_le_of_locally_eq I J h U
  refine le_antisymm h1 ?_
  refine fun U => ideal_le_of_locally_eq J I (fun x => ?_) U
  obtain ⟨V, hV, hIJ⟩ := h x
  exact ⟨V, hV, sy_ hIJ⟩
end
end
end

theorem sectionsAlgebraMap_comp_specMap (k L : Type) [Field k] [Field L]
    {Y : Sch} (q : Y ⟶ Sp L)
    (ph_ : CommRingCat.of k ⟶ CommRingCat.of L) (W : Opn Y) :
    sectionsAlgebraMap k (q ≫ Spec.map ph_) W = (sectionsAlgebraMap L q W).comp ph_.hom := by
  let _a0 := (hAT (m12 ph_) ≫ hAT q) ≫ pMap Y (homOfLE $ le_preimage_top L q W).op
  let _a1 := q ≫ m12 ph_
  let _a2 := le_preimage_top L q W
  let _a3 := le_preimage_top k _a1 W
  have h1 : appLE _a1 ⊤ W _a3
      = _a0 := rfl
  have h2 : hAT (m12 ph_) ≫ appLE q ⊤ W _a2
      = _a0 :=
    (assoc _ _ _).symm
  have happ := tr_ h1 h2.symm
  have key : isoI (GSpecIso $ m10 k) ≫
        appLE _a1 ⊤ W _a3
      = ph_ ≫ (isoI (GSpecIso $ m10 L) ≫
          appLE q ⊤ W _a2) := by simp_all
  ext a
  exact m156 (congrArg hom key) a

section
variable {k L : Type} [Field k] [Field L]
theorem exists_affineOpen_derivIdealSheaf_comap_eq
    {X Y : Sch} {p : X ⟶ Sp k} [Smooth p]
    {q : Y ⟶ Sp L} [Smooth q] {f : Y ⟶ X}
    {ph_ : CommRingCat.of k ⟶ CommRingCat.of L} (hsq : IsPullback q f (Spec.map ph_) p)
    (I : ISD X) (y : ↥Y) :
    ∃ V : Y.affineOpens, y ∈ (V : Opn Y) ∧
      (derivIdealSheaf L q $ comap I f).ideal V
        = (comap (derivIdealSheaf k p I) f).ideal V := by
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p $ bsM f y
  obtain ⟨V, hVU, c', hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_of_isPullback hsq c y hxU
  refine ⟨⟨V, hVaff⟩, hyV, ?_⟩
  have hdec : DecidableEq $ UFin m := Classical.decEq _
  let instkL := ph_.hom.toAlgebra
  let instA := sectionsAlgebra k p U
  let instPA := c.algebra
  let instB := sectionsAlgebra L q V
  let instPB := c'.algebra
  let instAlgebra := ((sectionsAlgebraMap L q V).comp ph_.hom).toAlgebra
  have tA := c.isScalarTower
  have tB := c'.isScalarTower
  have feA : FormallyEtale (MvU m k) U.sec :=
    c.algebra_formallyEtale hU
  have feB : FormallyEtale (MvU m L) V.sec :=
    c'.algebra_formallyEtale hVaff
  have tkL : IsScalarTower k L V.sec := of_algebraMap_eq fun _ => rfl
  let _a0 := appLE f U V hVU
  have hcommutes : ∀ a, _a0.hom (algebraMap k U.sec a)
      = algebraMap k V.sec a := by
    intro a
    show _a0.hom (sectionsAlgebraMap k p U a)
      = sectionsAlgebraMap L q V (ph_.hom a)
    rw [sectionsAlgebraMap_appLE_apply k p f U V hVU a, ← hsq.w,
      sectionsAlgebraMap_comp_specMap k L q ph_ V]
    rfl
  let ps_ := AlgHom.mk _a0.hom hcommutes
  have hps_ : ∀ i,
      ps_ (EtaleCoordinates.coord k (UFin m) U.sec i)
        = EtaleCoordinates.coord L (UFin m) V.sec i := by
    rintro ⟨j⟩
    rw [c.etaleCoordinates_coord j, c'.etaleCoordinates_coord j]
    show _a0.hom (c.coord j) = c'.coord j
    exact sy_ $ hcoord j
  have key := DerivIdealBaseChange.map_derivIdeal k L (UFin m) U.sec V.sec ps_ hps_
      (I.ideal ⟨U, hU⟩)
  rw [derivIdealSheaf_ideal, comap_ideal_eq_map_appLE I f ⟨U, hU⟩ ⟨V, hVaff⟩ hVU, comap_ideal_eq_map_appLE (derivIdealSheaf k p I) f ⟨U, hU⟩ ⟨V, hVaff⟩ hVU, derivIdealSheaf_ideal]
  exact sy_ key

section
variable {X : Sch} (p) [Smooth p] (ph_ : CommRingCat.of k ⟶ CommRingCat.of L)
theorem derivIdealSheaf_comap_fieldBaseChange (I : ISD X) :
    derivIdealSheaf L (pullback.snd p $ Spec.map ph_)
        (comap I $ pullback.fst p $ Spec.map ph_) =
      comap (derivIdealSheaf k p I) (pullback.fst p $ Spec.map ph_) :=
  idealSheafData_eq_of_locally_eq _ _ fun y =>
    exists_affineOpen_derivIdealSheaf_comap_eq (isPullback_pullback_specMap p ph_) I y

theorem derivIdealSheafIterate_comap_fieldBaseChange r (I : ISD X) :
    derivIdealSheafIterate L (pullback.snd p $ Spec.map ph_) r
        (comap I $ pullback.fst p $ Spec.map ph_) =
      comap (derivIdealSheafIterate k p r I) (pullback.fst p $ Spec.map ph_) := by
  induction r with
  | zero => rfl
  | succ n ih =>
      rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih,
        derivIdealSheaf_comap_fieldBaseChange p ph_ $ derivIdealSheafIterate k p n I]

theorem maxContactIdeal_comap_fieldBaseChange m (I : ISD X) :
    maxContactIdeal L (pullback.snd p $ Spec.map ph_)
        (comap I $ pullback.fst p $ Spec.map ph_) m =
      comap (maxContactIdeal k p I m) (pullback.fst p $ Spec.map ph_) := by
  rw [maxContactIdeal_eq_derivIdealSheafIterate, maxContactIdeal_eq_derivIdealSheafIterate, derivIdealSheafIterate_comap_fieldBaseChange]
end

section
variable [hv3_0 : CharZero k] [hv3_1 : CharZero L] {X : Sch} (p) [Smooth p] (ph_ : CommRingCat.of k ⟶ CommRingCat.of L) (I : ISD X)
include hv3_0 hv3_1
theorem orderAtLeastLocus_comap_fieldBaseChange m :
    orderAtLeastLocus (comap I $ pullback.fst p $ Spec.map ph_) m =
      (pullback.fst p $ Spec.map ph_).base ⁻¹' orderAtLeastLocus I m := by
  rcases m73 m with rfl | hm
  rw [orderAtLeastLocus_zero, orderAtLeastLocus_zero, preimage_univ]
  rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus L (pullback.snd p $ m12 ph_)
      (cmI I $ pullback.fst p $ m12 ph_) hm,
    ← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm,
    derivIdealSheafIterate_comap_fieldBaseChange p ph_ (m - 1) I]
  ext y
  simp

theorem orderAt_comap_fieldBaseChange y :
    orderAt (comap I $ pullback.fst p $ Spec.map ph_) y =
      orderAt I ((pullback.fst p $ Spec.map ph_).base y) := by
  refine eq_of_forall_natCast_le_iff ?_
  intro n
  simpa [mem_orderAtLeastLocus_iff, mem_preimage] using (mp_ ext_iff (orderAtLeastLocus_comap_fieldBaseChange p ph_ I n) y)
end
end

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

theorem isIso_subschemeio_comap_bot {X X' : Sch} (pi_ : X' ⟶ X) :
    IsIso (comap (⊥ : ISD X) pi_).subschemeι := by
  rw [show comap (⊥ : ISD X) pi_ = ⊥ from by simp]
  infer_instance

theorem ker_preimage_io_comp_of_isIso {X Y : Sch} (f : X ⟶ Y) [IsIso f] (U : Opn Y) :
    ((f ⁻¹ᵁ U).i ≫ f).ker = U.ι.ker := by
  have : IsIso $ morphismRestrict f U := inferInstance
  rw [← (isPullback_morphismRestrict f U).w]
  exact ker_comp_of_isIso ..

section
variable {X : Sch}
theorem section_eq_zero_of_locally_zero U
    s
    (h : ∀ x ∈ U, ∃ V : Opn X, ∃ hV : V ≤ U, x ∈ V ∧
      X.presheaf.map (homOfLE hV).op s = 0) :
    s = 0 := by
  apply section_ext X.sheaf U
  intro x hx
  obtain ⟨V, hV, hxV, hs⟩ := h x hx
  have h1 := X.presheaf.germ_res_apply (homOfLE hV) x hxV s
  rw [hs, map_zero] at h1
  show pGerm X U x hx s = pGerm X U x hx 0
  rw [map_zero]
  exact sy_ h1

theorem map_homOfLE_map_homOfLE {V V' V'' : Opn X} (h1 : V' ≤ V) (h2 : V'' ≤ V')
    (s : (X.sec V)) :
    X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op s)
      = X.presheaf.map (homOfLE $ h2.trans h1).op s := by
  have hcomp : pMap X (homOfLE h1).op ≫ pMap X (homOfLE h2).op
      = pMap X (homOfLE $ h2.trans h1).op := by
    rw [← m222]
    rfl
  exact congrArg (fun ph_ => (m23 ph_) s) hcomp

theorem map_eq_zero_of_app_io_eq_zero (W V V' : Opn X) (s : (X.sec V))
    (hs : (W.ι.app V).hom s = 0) (h1 : V' ≤ V) (h2 : ∀ y : ↥X, y ∈ V' → y ∈ W) :
    X.presheaf.map (homOfLE h1).op s = 0 := by
  have hT : opI W ''ᵁ opPre W V ≤ V := by
    rintro y ⟨z, hz, rfl⟩
    exact hz
  have hle : V' ≤ opI W ''ᵁ opPre W V := by
    intro y hy
    exact ⟨⟨y, h2 y hy⟩, h1 hy, rfl⟩
  have hzero : pMap X (homOfLE hT).op s = 0 := by
    rwa [Scheme.Opens.ι_app] at hs
  rw [← map_homOfLE_map_homOfLE hT hle s, hzero, map_zero]

theorem algebraMap_basicOpen {U : Opn X} (f : (X.sec U)) (t : (X.sec U)) :
    algebraMap (X.sec U) Γ(X, basicOpen X f) t
      = X.presheaf.map (homOfLE $ X.basicOpen_le f).op t := rfl

theorem notMem_support_of_mem_basicOpen (I : ISD X) (U : X.affineOpens)
    f (hf : f ∈ I.ideal U) y (hy : y ∈ basicOpen X f) :
    y ∉ I.support := by
  intro hmem
  have h1 : y ∈ I.supportSet := hmem
  rw [mem_supportSet_iff] at h1
  have h2 := h1 U
  rw [mem_zeroLocus_iff] at h2
  exact h2 f hf hy

theorem map_basicOpen_eq_zero_of_app_io_eq_zero (W V U0_ : Opn X)
    (hU0_ : IsAffineOpen U0_)
    (s : (X.sec V)) (hs : (W.ι.app V).hom s = 0)
    (f : (X.sec U0_)) (hf : f ∈ nonZeroDivisors (X.sec U0_))
    (hWf : ∀ y : ↥X, y ∈ X.basicOpen f → y ∈ W)
    (b : (X.sec U0_)) (hbV : X.basicOpen b ≤ V) :
    X.presheaf.map (homOfLE hbV).op s = 0 := by
  have := hU0_.isLocalization_basicOpen b
  let _m1 := Γ(X, X.basicOpen b)
  let _a1 := pMap X (homOfLE $ X.basicOpen_le b).op f
  have hgnzd : _a1 ∈ nonZeroDivisors _m1 := by
    have hq : _a1
        = algebraMap U0_.sec _m1 f := rfl
    rw [hq]
    exact nonZeroDivisors_le_comap (powers b) _m1 hf
  let _m0 := _a1
  have hgV : X.basicOpen _m0 ≤ V :=
    (X.basicOpen_le _).trans hbV
  have hres : pMap X (homOfLE hgV).op s = 0 := by
    refine map_eq_zero_of_app_io_eq_zero W V _ s hs hgV ?_
    intro y hy
    rw [basicOpen_res] at hy
    exact hWf y hy.2
  have := (hU0_.basicOpen b).isLocalization_basicOpen _m0
  let _a0 := pMap X (homOfLE hbV).op s
  have hres' : algebraMap _m1
      Γ(X, X.basicOpen _m0)
      _a0 = 0 := by
    rwa [algebraMap_basicOpen, map_homOfLE_map_homOfLE]
  obtain ⟨m, hm⟩ := mp_ (map_eq_zero_iff
    (powers _m0)
    Γ(X, X.basicOpen _m0)
    _a0) hres'
  obtain ⟨n, hn⟩ := m.2
  have hmem : (m : _m1) ∈ nonZeroDivisors _m1 := by
    rw [← hn]
    exact pow_mem hgnzd n
  exact an1 (mp_ mem_nonZeroDivisors_iff hmem) _a0 hm

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.ker_supportCompl_io_eq_bot {I : ISD X}
    (h : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor I) :
    (Scheme.Opens.i (X := X) $ suppC I).ker = ⊥ := by
  refine le_antisymm (fun U => ?_) bot_le
  intro s hs
  rw [show (⊥ : ISD X).ideal U = ⊥ from by simp, mem_bot]
  refine EmbeddedResolution.section_eq_zero_of_locally_zero U.1 s ?_
  intro x hx
  obtain ⟨U0_, f, hxU0_, hfnzd, hIf⟩ := h x
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter U.2 U0_.2 x ⟨hx, hxU0_⟩
  have hbV := hab ▸ X.basicOpen_le a
  refine ⟨basicOpen X b, hbV, hab ▸ hxa, ?_⟩
  refine _root_.FunctorialResolution.EmbeddedResolution.map_basicOpen_eq_zero_of_app_io_eq_zero I.support.compl U.1 U0_.1 U0_.2 s
    (mp_ mem_ker $ ideal_ofIdeals_le _ U hs) f hfnzd ?_ b hbV
  intro y hy
  refine _root_.FunctorialResolution.EmbeddedResolution.notMem_support_of_mem_basicOpen I U0_ f ?_ y hy
  rw [hIf]
  exact mem_span_singleton_self f
end

theorem strictTransform_bot_of_isBlowupAlongIdealSheaf {X X' : Sch} {pi_}
    {I} (h : Blowup.IsBlowupAlongIdealSheaf pi_ I) :
    strictTransform pi_ I (⊥ : ISD X) = (⊥ : ISD X') := by
  have := isIso_subschemeio_comap_bot pi_
  rw [strictTransform_eq_ker, strictTransformImmersion_eq, strictTransformOpens_eq]
  exact tr_ (ker_preimage_io_comp_of_isIso _ _) h.1.ker_supportCompl_io_eq_bot

theorem IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso {X' X} ph_
    [IsIso ph_] [IsClosedImmersion ph_] {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq ph_ B' B) : IsPushforwardBlowupSeq ph_ B' B := by
  obtain ⟨hlen, σ, hsg0, hsq, hc⟩ := h
  have hiso : ∀ i (hi : i ≤ B'.length), IsIso $ σ i hi := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hz : σ 0 hi = sbIzH B' ≫ ph_ ≫ sbIzI B := by
          rw [← assoc, ← hsg0]
          simp
        rw [hz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < B'.length := hi
        exact (hsq n hn).isIso_fst_of_isIso
  refine ⟨hlen, σ, ?_, hsg0, fun i hi => (hsq i hi).w, ?_, ?_⟩
  intro i hi
  infer_instance
  intro i hi
  rw [hc i hi, imageIdealSheaf_comap]
  intro i hi
  rw [ker_eq_bot_of_isIso, ker_eq_bot_of_isIso,
    strictTransform_bot_of_isBlowupAlongIdealSheaf $ B.isBlowupAlongIdealSheaf_blowupMorphism i $ hlen ▸ hi]

end FunctorialResolution.EmbeddedResolution
end
section
universe v w


namespace FunctorialResolution.EmbeddedResolution

theorem ringKrullDim_stalk_opens (X : Sch) (U : Opn X) x :
    ringKrullDim (U.toScheme.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk $ U.ib x) := by
  let _a0 := stalkMap U.i x
  have : IsIso _a0 := inferInstance
  exact sy_ $ ringKrullDim_eq_of_ringEquiv
    (asIso _a0).commRingCatIsoToRingEquiv

theorem isNoetherianRing_stalk_of_opens {X : Sch} (U : Opn X)
    y (h : IsNoetherianRing $ X.presheaf.stalk $ U.ib y) :
    IsNoetherianRing $ U.toScheme.presheaf.stalk y := by
  let _a0 := stalkMap U.i y
  have : IsIso _a0 := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (asIso _a0).commRingCatIsoToRingEquiv

section
variable {k : Type} [Field k]
section
variable {X : Sch} (p : X ⟶ Sp k) [IsLocallyNoetherian X] {U : Opn X} {m : ℕ} (c : EtaleChart p U m)
include c
theorem ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) ≤ ((m : ENat) : WithBot ENat) := by
  have := c.isEtale
  have : IsNoetherianRing $ U.toScheme.presheaf.stalk (⟨x, hx⟩ : oSch U) :=
    isNoetherianRing_stalk_of_opens U _ inferInstance
  have h1 :=
    ringKrullDim_stalk_le_of_etale_affineSpace c.map (⟨x, hx⟩ : oSch U)
  rwa [ringKrullDim_stalk_opens X U (⟨x, hx⟩ : oSch U)] at h1

theorem etaleChart_dim_le_topologicalKrullDim (hU : IsAffineOpen U)
    (hne : (U : Set ↥X).Nonempty) :
    ((m : ENat) : WithBot ENat) ≤ topologicalKrullDim ↥X := by
  obtain ⟨x, hx, hcl⟩ := exists_mem_isClosed_singleton_of_isAffineOpen U hU hne
  have : IsAffine U.toScheme := hU
  have := c.isEtale
  let _m0 := (⟨x, hx⟩ : oSch U)
  have : IsNoetherianRing $ U.toScheme.presheaf.stalk _m0 :=
    isNoetherianRing_stalk_of_opens U _ inferInstance
  calc (m : WithBot ENat)
      = ringKrullDim (U.toScheme.presheaf.stalk _m0) := sy_ $ ringKrullDim_stalk_eq_of_etale_affineSpace c.map _m0 hcl
    _ = ringKrullDim (stkX X $ opIb U _m0) := ringKrullDim_stalk_opens X U _m0
    _ ≤ topologicalKrullDim ↥X := ringKrullDim_stalk_le_topologicalKrullDim X $ opIb U _m0
end

theorem isLocallyNoetherian_of_smooth_over_field
    {P : Sch} (pP : P ⟶ Sp k) [Smooth pP] :
    IsLocallyNoetherian P := by
  exact ⟨fun U => @isNoetherianRing_sections k _ _ P pP _ U (sectionsAlgebra k pP U.1) $ algebraMap_sectionsAlgebra k pP U.1⟩
end

section
variable {k K : Type} [Field k] [Field K] {X : Sch} (p : X ⟶ Sp k)
theorem surjective_base_pullback_fst_specMapOfFieldHom (f : k →+* K) :
    Surjective (pullback.fst p $ specMapOfFieldHom k K f).base := by
  have :=
    of_isPullback
      (P := @Surjective) (isPullback_pullback_specMap p $ ofHom f) $ FunctorialResolution.EmbeddedResolution.instSurjectiveSpecMapOfFieldHom k K f
  exact surjective _

theorem topologicalKrullDim_pullback_spec_map_of_surjective [Smooth p]
    (ph_ : CommRingCat.of k ⟶ CommRingCat.of K)
    (hsurj : Surjective (pullback.fst p $ Spec.map ph_).base) :
    topologicalKrullDim ↥(pullback p $ Spec.map ph_) = topologicalKrullDim ↥X := by
  let _a2 := isPullback_pullback_specMap p ph_
  let _a0 := pullback.snd p $ m12 ph_
  have :=
    isLocallyNoetherian_of_smooth_over_field p
  have :=
    isLocallyNoetherian_of_smooth_over_field _a0
  refine le_antisymm ?_ ?_
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ _ ?_
  intro y
  let _a1 := bsM (pullback.fst p $ m12 ph_) y
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p _a1
  obtain ⟨V, -, c', -, hyV, -⟩ := exists_etaleChart_of_isPullback _a2 c y hxU
  exact le_trans
    (ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian _a0 c' y hyV)
    (etaleChart_dim_le_topologicalKrullDim p c hU
      ⟨_a1, hxU⟩)
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le _ _ ?_
  intro x
  obtain ⟨U, m, hxU, hU, ⟨c⟩⟩ := exists_etaleChart p x
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨V, -, c', hVaff, hyV, -⟩ := exists_etaleChart_of_isPullback _a2 c y hxU
  exact le_trans (ringKrullDim_stalk_le_of_etaleChart_of_isLocallyNoetherian p c _ hxU)
    (etaleChart_dim_le_topologicalKrullDim _a0 c' hVaff ⟨y, hyV⟩)

theorem topologicalKrullDim_pullback_specMapOfFieldHom [Smooth p]
    (f : k →+* K) :
    topologicalKrullDim ↥(pullback p $ specMapOfFieldHom k K f) = topologicalKrullDim ↥X :=
  topologicalKrullDim_pullback_spec_map_of_surjective p (ofHom f)
    (surjective_base_pullback_fst_specMapOfFieldHom p f)
end

theorem krullDimSucc_eq_of_topologicalKrullDim_eq {V P : Sch}
    (h : topologicalKrullDim ↥V = topologicalKrullDim ↥P) :
    krullDimSucc V = krullDimSucc P := by
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim, h]

section
variable (R : Type v)
theorem eq_bot_of_formallyUnramified_of_comap_le (D : Type w) [CommRing R]
    [CommRing D] [IsDomain D] [Algebra R D] [EssFiniteType R D]
    [FormallyUnramified R D]
    (p : Ideal R) (hp : p.IsPrime) (hker : ∀ r : R, algebraMap R D r = 0 ↔ r ∈ p)
    (Q : Ideal D) (hQ : Q.IsPrime) (hQc : ∀ r : R, algebraMap R D r ∈ Q → r ∈ p) :
    Q = ⊥ := by
  let _c0 := FractionRing $ R ⧸ p
  have : IsDomain $ R ⧸ p := isDomain p
  obtain ⟨M, hMdef⟩ : ∃ M, M = Submonoid.map (algebraMap R D) p.primeCompl :=
    ⟨_, rfl⟩
  have hmemM : ∀ r, r ∈ p.primeCompl → algebraMap R D r ∈ M := by
    intro r hr
    rw [hMdef]
    exact Submonoid.mem_map.mpr ⟨r, hr, rfl⟩
  have hMle : M ≤ nonZeroDivisors D := by
    intro z hz
    rw [hMdef] at hz
    obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp hz
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    exact hr $ mp_ (hker r) h0
  have : IsDomain $ Localization M :=
    isDomain_of_le_nonZeroDivisors (Localization M) hMle
  have : FormallyUnramified D $ Localization M :=
    of_isLocalization M
  have : EssFiniteType D $ Localization M :=
    Algebra.EssFiniteType.of_isLocalization (Localization M) M
  have : FormallyUnramified R $ Localization M :=
    Algebra.FormallyUnramified.comp R D $ Localization M
  have : EssFiniteType R $ Localization M :=
    comp R D $ Localization M
  have hzero : ∀ a, a ∈ p → algebraMap R (Localization M) a = 0 := by
    intro a ha
    rw [algebraMap_apply R D (Localization M) a, mpr_ (hker a) ha, map_zero]
  let _a1 := algebraMap R $ Localization M
  have hunits : ∀ z : nonZeroDivisors $ R ⧸ p,
      IsUnit $ m201 p _a1 hzero z := by
    rintro ⟨z, hz⟩
    obtain ⟨r, rfl⟩ := mk_surjective z
    have hne := nonZeroDivisors.ne_zero hz
    have h1 : m201 p _a1 hzero
        (mk p r) = algebraMap D (Localization M) (algebraMap R D r) := by
      rw [lift_mk, algebraMap_apply R D (Localization M) r]
    rw [h1]
    exact IsLocalization.map_units (Localization M) ⟨algebraMap R D r, hmemM r fun hmem => hne $ Ideal.Quotient.eq_zero_iff_mem.mpr hmem⟩
  let _ :=
    toAlgebra (IsLocalization.lift hunits : FractionRing (R ⧸ p) →+* Localization M)
  have : IsScalarTower R _c0 $ Localization M := by
    refine of_algebraMap_eq fun r => ?_
    have h3 : algebraMap R _c0 r
        = algebraMap (R ⧸ p) _c0 (mk p r) :=
      algebraMap_apply R (R ⧸ p) _c0 r
    rw [h3, algebraMap_toAlgebra, lift_eq, lift_mk]
  have : EssFiniteType _c0 $ Localization M :=
    of_comp R _c0 $ Localization M
  have : FormallyUnramified _c0 $ Localization M := by
    apply of_restrictScalars (R := R)
  have hfield : IsField $ Localization M :=
    by
    let K := _c0
    let D := Localization M
    have : FormallyUnramified D $ FractionRing D :=
      of_isLocalization $ nonZeroDivisors D
    have : EssFiniteType D $ FractionRing D :=
      Algebra.EssFiniteType.of_isLocalization (FractionRing D) $ nonZeroDivisors D
    have : FormallyUnramified K $ FractionRing D :=
      Algebra.FormallyUnramified.comp K D $ FractionRing D
    have : EssFiniteType K $ FractionRing D :=
      comp K D $ FractionRing D
    have : IsSeparable K $ FractionRing D :=
      mp (iff_isSeparable K $ FractionRing D) inferInstance
    have : IsIntegral K D :=
      ⟨fun y => (Algebra.IsSeparable.isIntegral K $ algebraMap D (FractionRing D) y).tower_bot
        (IsFractionRing.injective D $ FractionRing D)⟩
    exact isField_of_isIntegral_of_isField' $ Field.toIsField K
  by_contra hQne
  obtain ⟨y, hyQ, hy0⟩ : ∃ y ∈ Q, y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQne $ mpr_ (Submodule.eq_bot_iff Q) hcon
  have hdisj : Disjoint (M : Set D) (Q : Set D) := by
    rw [disjoint_left]
    intro z hzM hzQ
    rw [hMdef] at hzM
    obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp hzM
    exact hr $ hQc r hzQ
  have hyL : algebraMap D (Localization M) y ≠ 0 := by simp_all
  obtain ⟨z, hz⟩ := hfield.mul_inv_cancel hyL
  refine (isPrime_of_isPrime_disjoint M (Localization M) Q hQ hdisj).ne_top $ mpr_ (eq_top_iff_one _) ?_
  rw [← hz]
  exact mul_mem_right z _ $ mem_map_of_mem _ hyQ

section
variable (S : Type w) [CommRing R] [CommRing S] [Algebra R S] [EssFiniteType R S] [FormallyUnramified R S]
theorem eq_of_le_of_comap_eq
    (q q' : Ideal S) (hq : q.IsPrime) (hq' : q'.IsPrime) (hle : q ≤ q')
    (hc : q.comap (algebraMap R S) = q'.comap (algebraMap R S)) : q = q' := by
  have :=
    of_surjective (Ideal.Quotient.mkₐ R q) mk_surjective
  have :=
    Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ S q) mk_surjective
  have hmk : ∀ r, algebraMap R (S ⧸ q) r = mk q (algebraMap R S r) :=
    fun r => algebraMap_apply R S (S ⧸ q) r
  let _a0 := q'.map $ mk q
  have hQ : _a0.IsPrime := by
    refine map_isPrime_of_surjective mk_surjective ?_
    rwa [mk_ker]
  have hbot := by
    refine eq_bot_of_formallyUnramified_of_comap_le R (S ⧸ q) (q.comap $ algebraMap R S)
      inferInstance ?_ _a0 hQ ?_
    intro r
    rw [hmk r, eq_zero_iff_mem]
    exact m22
    intro r hr
    rw [hmk r] at hr
    have hmem := mp_ (mem_quotient_iff_mem hle) hr
    rwa [hc]
  refine le_antisymm hle ?_
  intro z hz
  have hzz : mk q z ∈ _a0 := mem_map_of_mem _ hz
  rw [hbot] at hzz
  exact Ideal.Quotient.eq_zero_iff_mem.mp $ mp_ mem_bot hzz

theorem strictMono_comap_of_formallyUnramified :
    StrictMono $ PrimeSpectrum.comap $ algebraMap R S := by
  intro a b hab
  have hle := ltLe hab
  refine lt_of_le_of_ne (comap_mono hle) ?_
  intro heq
  refine absurd ?_ $ ne_of_lt hab
  exact m210 $ eq_of_le_of_comap_eq R S a.asIdeal b.asIdeal a.isPrime b.isPrime hle
    (congrArg PrimeSpectrum.asIdeal heq)
end
end

theorem ringKrullDim_le_of_isLocalization_etale {A B R S : Type} [CommRing A]
    [CommRing B] [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] (ph_ : A →+* B) (gA : A →+* R) (gB : B →+* S) (ps_ : R →+* S)
    MA MB (hph : RingHom.Etale ph_)
    (hlocA : @IsLocalization A _ MA R _ gA.toAlgebra)
    (hlocB : @IsLocalization B _ MB S _ gB.toAlgebra)
    (hcomm : ∀ a : A, ps_ (gA a) = gB (ph_ a)) (hlocal : IsLocalHom ps_) :
    ringKrullDim S ≤ ringKrullDim R := by
  let _ := ph_.toAlgebra
  let _ := gA.toAlgebra
  let _ := gB.toAlgebra
  let _ := ps_.toAlgebra
  let _ := (gB.comp ph_).toAlgebra
  have : IsLocalization MA R := hlocA
  have : IsLocalization MB S := hlocB
  have : m121 A B := hph
  have : IsLocalHom $ algebraMap R S := hlocal
  have : IsScalarTower A B S := of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A R S := of_algebraMap_eq fun a => sy_ $ hcomm a
  have : FormallyUnramified A B := inferInstance
  have : FiniteType A B := inferInstance
  have : EssFiniteType A B := inferInstance
  have : FormallyUnramified B S := of_isLocalization (M := MB)
  have : EssFiniteType B S := Algebra.EssFiniteType.of_isLocalization S MB
  have : FormallyUnramified A S := Algebra.FormallyUnramified.comp A B S
  have : EssFiniteType A S := comp A B S
  have : FormallyUnramified R S := localization_base MA
  have : EssFiniteType R S := of_comp A R S
  exact Order.krullDim_le_of_strictMono _ $ strictMono_comap_of_formallyUnramified R S

theorem ringKrullDim_stalk_le_of_etale_of_isNoetherianRing {Y W : Sch} (f : Y ⟶ W)
    [Etale f] y [IsNoetherianRing (Y.presheaf.stalk y)]
    [IsNoetherianRing (W.presheaf.stalk (f.base y))] :
    ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (W.presheaf.stalk (f.base y)) := by
  obtain ⟨U, hxU, hU⟩ := exists_isAffineOpen_mem (X := W) $ bsM f y
  obtain ⟨V0, hyV0, hV0⟩ := exists_isAffineOpen_mem (X := Y) y
  obtain ⟨g, hgle, hyg⟩ :=
    hV0.exists_basicOpen_le (⟨y, ⟨hyV0, hxU⟩⟩ : (V0 ⊓ f.pre U : Opn Y)) hyV0
  have hV := hV0.basicOpen g
  have hVU := le_trans hgle inf_le_right
  have hyV := hyg
  have hgerm : f.appLE U (bOpn Y g) hVU ≫ pGerm Y (bOpn Y g) y hyV
      = pGerm W U (bsM f y) hxU ≫ f.stalkMap y := by
    simp [appLE]
  exact ringKrullDim_le_of_isLocalization_etale (f.appLE U (bOpn Y g) hVU).hom
    (pGerm W U (bsM f y) hxU).hom
    (pGerm Y (bOpn Y g) y hyV).hom (f.stalkMap y).hom
    (hU.primeIdealOf ⟨bsM f y, hxU⟩).asIdeal.primeCompl
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl (AlgebraicGeometry.HasRingHomProperty.appLE (P := @Etale) f inferInstance ⟨U, hU⟩ ⟨bOpn Y g, hV⟩ hVU)
    (hU.isLocalization_stalk ⟨f.base y, hxU⟩)
    (hV.isLocalization_stalk ⟨y, hyV⟩) (fun a => congrArg (fun t : W.sec U ⟶ stkX Y y => t.hom a) hgerm.symm) inferInstance

section
variable {V P : Sch} (f : V ⟶ P) [Etale f] [IsLocallyNoetherian P]
include f
theorem topologicalKrullDim_le_of_etale :
    topologicalKrullDim ↥V ≤ topologicalKrullDim ↥P := by
  have :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le V
    (topologicalKrullDim ↥P) ?_
  intro y
  have : IsNoetherianRing $ stkX V y := inferInstance
  have : IsNoetherianRing $ stkX P $ bsM f y := inferInstance
  exact le_trans (ringKrullDim_stalk_le_of_etale_of_isNoetherianRing f y)
    (ringKrullDim_stalk_le_topologicalKrullDim P $ bsM f y)

theorem krullDimSucc_le_of_etale
    (hP : topologicalKrullDim ↥P < ⊤) :
    krullDimSucc V ≤ krullDimSucc P :=
  krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ (topologicalKrullDim_le_of_etale f) hP
end

theorem MarkedIdealWithBoundary.dim_baseChange (T : MarkedIdealWithBoundary) (hT : IsAdmissible T) (L : Type) [Field L]
    [CharZero L] (f : T.base →+* L) :
    (bc T f).krullDimSucc = T.krullDimSucc := by
  have := hT.smooth
  exact krullDimSucc_eq_of_topologicalKrullDim_eq $ topologicalKrullDim_pullback_specMapOfFieldHom T.structMap f

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

def BlowupPreservesNoetherian : Prop :=
  ∀ (X X' : Sch) [IsNoetherian X] (pi_ : X' ⟶ X)
    (Z : ISD X), Blowup.IsBlowupAlongIdealSheaf pi_ Z → IsNoetherian X'

structure AmbientEmbedding {S : Sch} (s : BlowupSequenceData S) (n : ℕ) : Type 1 where
  ambient : Sch
  emb : s.obj n ⟶ ambient
  emb_isClosedImmersion : IsClosedImmersion emb
  isNoetherian_ambient_of_le_length : n ≤ s.length → IsNoetherian ambient

section
variable {S X : Sch} (ι : S ⟶ X) [IsClosedImmersion ι]
theorem isClosedImmersion_isoObjZero_hom_comp (s : BlowupSequenceData S) :
    IsClosedImmersion $ s.isoZero.hom ≫ ι := by
  have : IsClosedImmersion $ bdIzH s := inferInstance
  infer_instance

def ambientEmbeddingZero [IsNoetherian X]
    (s : BlowupSequenceData S) : AmbientEmbedding s 0 where
  ambient := X
  emb := s.isoZero.hom ≫ ι
  emb_isClosedImmersion := isClosedImmersion_isoObjZero_hom_comp ι s
  isNoetherian_ambient_of_le_length := fun _ => inferInstance
end

section
variable {S' A : Sch} (σ : S' ⟶ A)
theorem comap_imageIdealSheaf_of_isClosedImmersion
    [IsClosedImmersion σ] (J : ISD S') :
    comap (imageIdealSheaf σ J) σ = J := by
  have h : imageIdealSheaf σ J = J.map σ := rfl
  rw [h]
  exact p30 σ J

theorem preimage_support_subset_support_comap (Z : ISD A) :
    σ.base ⁻¹' (support Z : Set ↥A) ⊆ (support (comap Z σ) : Set ↥S') := by
  simp
end

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme)
include hres
theorem exists_closedImmersion_blowup_of_isBlowupAlongIdealSheaf
    {S' A : Sch} [IsLocallyNoetherian A] (σ : S' ⟶ A)
    [IsClosedImmersion σ] (J : ISD S') {S''}
    f (hf : Blowup.IsBlowupAlongIdealSheaf f J)
    (hc : ∀ T ∈ irreducibleComponents ↥S', ¬ T ⊆ (J.support : Set ↥S')) :
    ∃ ta_ : S'' ⟶ Blowup.blowup (imageIdealSheaf σ J),
      IsClosedImmersion ta_ ∧
      ta_ ≫ Blowup.blowup.proj (imageIdealSheaf σ J) = f ≫ σ ∧
      ta_.ker = strictTransform (Blowup.blowup.proj $ imageIdealSheaf σ J) (imageIdealSheaf σ J) σ.ker := by
  let _c0 := imageIdealSheaf σ J
  have hcomap := comap_imageIdealSheaf_of_isClosedImmersion σ J
  have hsupp : ∀ T ∈ irreducibleComponents ↥S',
      ¬ (bsM σ '' T) ⊆ spI _c0 := by
    intro T hT hsub
    refine hc T hT ?_
    have h2 := (image_subset_iff.mp hsub).trans $ preimage_support_subset_support_comap σ _c0
    rwa [hcomap] at h2
  obtain ⟨ps_, hps1_, hps2⟩ := hres A (Blowup.blowup _c0) S' σ
    (Blowup.blowup.proj _c0) _c0 (Blowup.blowup.isBlowupAlongIdealSheaf_proj _) hsupp
  rw [hcomap] at hps2
  have hab := hps2.lift_comp f hf.1
  have hba := hf.lift_comp ps_ hps2.1
  have hid1 : hps2.lift f hf.1 ≫ hf.lift ps_ hps2.1 = 𝟙 S'' := by
    refine hf.hom_ext hf.1 ?_ $ id_comp f
    rw [assoc, hba, hab]
  have hid2 : hf.lift ps_ hps2.1 ≫ hps2.lift f hf.1 = 𝟙 _ := by
    refine hps2.hom_ext hps2.1 ?_ $ id_comp ps_
    rw [assoc, hab, hba]
  have : IsIso $ hps2.lift f hf.1 := ⟨⟨hf.lift ps_ hps2.1, hid1, hid2⟩⟩
  refine ⟨hps2.lift f hf.1 ≫
      (p6 (Blowup.blowup.proj _c0) _c0 σ.ker).subschemeι,
    inferInstance, ?_, ?_⟩
  rw [assoc, ← hps1_, ← assoc, hab]
  rw [ker_comp_of_isIso]
  exact q2 _

theorem exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length
    (_hno : BlowupPreservesNoetherian) {S : Sch} (s : BlowupSequenceData S)
    (n : ℕ) (hn : n < s.length) (A : Sch) (σ : s.obj n ⟶ A)
    (hsg_ : IsClosedImmersion σ) (hA : IsNoetherian A)
    (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n),
        ¬ T ⊆ ((s.center n).support : CSet $ s.obj n)) :
    ∃ ta_ : s.obj (n + 1) ⟶ Blowup.blowup (imageIdealSheaf σ $ s.center n),
      IsClosedImmersion ta_ ∧
      ta_ ≫ Blowup.blowup.proj (imageIdealSheaf σ $ s.center n) = s.map n ≫ σ ∧
      ta_.ker = strictTransform (Blowup.blowup.proj $ imageIdealSheaf σ $ s.center n)
          (imageIdealSheaf σ $ s.center n) σ.ker := by
  have : IsLocallyNoetherian A := inferInstance
  exact exists_closedImmersion_blowup_of_isBlowupAlongIdealSheaf hres σ (s.center n) (s.map n) (s.isBlowup n hn) hc

section
variable (hno : BlowupPreservesNoetherian) {S} (s : BlowupSequenceData S) (n) (hn : n < s.length) (A) (σ : s.obj n ⟶ A) (hsg_ : IsClosedImmersion σ) (hA : IsNoetherian A) (hc : ∀ T ∈ irreducibleComponents ↥(s.obj n), ¬ T ⊆ ((s.center n).support : CSet (s.obj n)))
def embeddingIntoAmbientBlowup :
    s.obj (n + 1) ⟶ Blowup.blowup (imageIdealSheaf σ $ s.center n) :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hsg_ hA hc).choose

theorem isClosedImmersion_embeddingIntoBlowupImageIdealSheaf :
    IsClosedImmersion $ embeddingIntoAmbientBlowup hres hno s n hn A σ hsg_ hA hc :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hsg_ hA hc).choose_spec.1

theorem embeddingIntoBlowupImageIdealSheaf_comp_proj :
    embeddingIntoAmbientBlowup hres hno s n hn A σ hsg_ hA hc ≫ Blowup.blowup.proj (imageIdealSheaf σ $ s.center n) =
      s.map n ≫ σ :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hsg_ hA hc).choose_spec.2.1

theorem ker_embeddingIntoBlowupImageIdealSheaf :
    (embeddingIntoAmbientBlowup hres hno s n hn A σ hsg_ hA hc).ker =
      strictTransform (Blowup.blowup.proj $ imageIdealSheaf σ $ s.center n)
        (imageIdealSheaf σ $ s.center n) σ.ker :=
  (exists_closedImmersion_blowup_imageIdealSheaf_of_lt_length hres hno s n hn A σ hsg_ hA hc).choose_spec.2.2
end
end

theorem isNoetherian_blowup_of_isNoetherian (hno : BlowupPreservesNoetherian)
    {A : Sch} (hA : IsNoetherian A) (Z : ISD A) :
    IsNoetherian $ Blowup.blowup Z := by
  exact hno A (Blowup.blowup Z) (Blowup.blowup.proj Z) Z $ Blowup.blowup.isBlowupAlongIdealSheaf_proj Z

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) {S} (s : BlowupSequenceData S) (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬ T ⊆ ((s.center i).support : CSet (s.obj i))) (n) (st : AmbientEmbedding s n)
def ambientEmbeddingSucc :
    Σ t : AmbientEmbedding s $ n + 1, (t.ambient ⟶ st.ambient) :=
  if h : n < s.length then
    ⟨{ ambient := Blowup.blowup (imageIdealSheaf st.emb $ s.center n)
       emb := embeddingIntoAmbientBlowup hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
         (st.isNoetherian_ambient_of_le_length $ Nat.le_of_lt h) $ hcen n h
       emb_isClosedImmersion := isClosedImmersion_embeddingIntoBlowupImageIdealSheaf hres hno s n h st.ambient st.emb
         st.emb_isClosedImmersion (st.isNoetherian_ambient_of_le_length $ Nat.le_of_lt h) $ hcen n h
       isNoetherian_ambient_of_le_length := fun _ =>
         isNoetherian_blowup_of_isNoetherian hno (st.isNoetherian_ambient_of_le_length $ Nat.le_of_lt h)
           (imageIdealSheaf st.emb $ s.center n) },
     Blowup.blowup.proj $ imageIdealSheaf st.emb $ s.center n⟩
  else
    ⟨{ ambient := s.obj (n + 1)
       emb := 𝟙 $ s.obj $ n + 1
       emb_isClosedImmersion := inferInstance
       isNoetherian_ambient_of_le_length := fun hle => absurd (lt_of_succ_le hle) h },
     s.map n ≫ st.emb⟩

theorem isBlowupAlongIdealSheaf_succAmbientEmbeddingMorphism (h : n < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (ambientEmbeddingSucc hres hno s hcen n st).2 $ imageIdealSheaf st.emb $ s.center n := by
  unfold ambientEmbeddingSucc
  rw [dif_pos h]
  exact Blowup.blowup.isBlowupAlongIdealSheaf_proj _

theorem ker_succAmbientEmbedding_eq_strictTransform (h : n < s.length) :
    (ambientEmbeddingSucc hres hno s hcen n st).1.emb.ker =
      strictTransform (ambientEmbeddingSucc hres hno s hcen n st).2
        (imageIdealSheaf st.emb $ s.center n) st.emb.ker := by
  unfold ambientEmbeddingSucc
  rw [dif_pos h]
  exact ker_embeddingIntoBlowupImageIdealSheaf hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
    (st.isNoetherian_ambient_of_le_length $ m49 h) $ hcen n h

theorem succAmbientEmbedding_comp_blowupMorphism :
    (ambientEmbeddingSucc hres hno s hcen n st).1.emb ≫ (ambientEmbeddingSucc hres hno s hcen n st).2 =
      s.map n ≫ st.emb := by
  unfold ambientEmbeddingSucc
  by_cases h : n < s.length
  rw [dif_pos h]
  exact embeddingIntoBlowupImageIdealSheaf_comp_proj hres hno s n h st.ambient st.emb st.emb_isClosedImmersion
    (st.isNoetherian_ambient_of_le_length $ m49 h) $ hcen n h
  rw [dif_neg h]
  exact id_comp _
end

section
variable {S X : Sch} (ι : S ⟶ X) [IsClosedImmersion ι] [IsNoetherian X] (s : BlowupSequenceData S) (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (hcen : ∀ i, i < s.length → ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬ T ⊆ ((s.center i).support : CSet (s.obj i)))
def ambientEmbedding :
    ∀ n : ℕ, AmbientEmbedding s n := fun n =>
  Nat.rec (motive := fun n => AmbientEmbedding s n) (ambientEmbeddingZero ι s)
    (fun m st => (ambientEmbeddingSucc hres hno s hcen m st).1) n

def ambientEmbeddingSuccMap (n : ℕ) :
    (ambientEmbedding ι s hres hno hcen $ n + 1).ambient ⟶ (ambientEmbedding ι s hres hno hcen n).ambient :=
  (ambientEmbeddingSucc hres hno s hcen n $ ambientEmbedding ι s hres hno hcen n).2

theorem isBlowupAlongIdealSheaf_ambientBlowupMorphism (n : ℕ) (hn : n < s.length) :
    Blowup.IsBlowupAlongIdealSheaf (ambientEmbeddingSuccMap ι s hres hno hcen n)
      (imageIdealSheaf (ambientEmbedding ι s hres hno hcen n).emb $ s.center n) :=
  isBlowupAlongIdealSheaf_succAmbientEmbeddingMorphism hres hno s hcen n (ambientEmbedding ι s hres hno hcen n) hn

def ambientBlowupSequence : BlowupSequenceData X where
  length := s.length
  obj := fun n => (ambientEmbedding ι s hres hno hcen n).ambient
  map := fun n => ambientEmbeddingSuccMap ι s hres hno hcen n
  isoZero := refl X
  center := fun n => imageIdealSheaf (ambientEmbedding ι s hres hno hcen n).emb $ s.center n
  isBlowup := fun n hn => isBlowupAlongIdealSheaf_ambientBlowupMorphism ι s hres hno hcen n hn

section
variable (n : ℕ)
theorem isNoetherian_ambientBlowupSequence_schemeAt (hn : n ≤ s.length) :
    IsNoetherian $ (ambientBlowupSequence ι s hres hno hcen).obj n :=
  (ambientEmbedding ι s hres hno hcen n).isNoetherian_ambient_of_le_length hn

def embeddingIntoAmbientBlowupSequence :
    s.obj n ⟶ (ambientBlowupSequence ι s hres hno hcen).obj n :=
  (ambientEmbedding ι s hres hno hcen n).emb

theorem ker_embeddingIntoAmbientBlowupSequence_succ (hn : n < s.length) :
    (embeddingIntoAmbientBlowupSequence ι s hres hno hcen $ n + 1).ker =
      strictTransform ((ambientBlowupSequence ι s hres hno hcen).map n)
        ((ambientBlowupSequence ι s hres hno hcen).center n)
        (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n).ker :=
  ker_succAmbientEmbedding_eq_strictTransform hres hno s hcen n (ambientEmbedding ι s hres hno hcen n) hn

theorem isClosedImmersion_embeddingIntoAmbientBlowupSequence :
    IsClosedImmersion $ embeddingIntoAmbientBlowupSequence ι s hres hno hcen n :=
  (ambientEmbedding ι s hres hno hcen n).emb_isClosedImmersion

theorem embeddingIntoAmbientBlowupSequence_succ_comp_map :
    embeddingIntoAmbientBlowupSequence ι s hres hno hcen (n + 1) ≫ (ambientBlowupSequence ι s hres hno hcen).map n =
      s.map n ≫ embeddingIntoAmbientBlowupSequence ι s hres hno hcen n :=
  succAmbientEmbedding_comp_blowupMorphism hres hno s hcen n $ ambientEmbedding ι s hres hno hcen n
end

@[simp]
theorem ambientBlowupSequence_length :
    (ambientBlowupSequence ι s hres hno hcen).length = s.length := rfl


@[simp]
theorem ambientBlowupSequence_center (n : ℕ) :
    (ambientBlowupSequence ι s hres hno hcen).center n =
      imageIdealSheaf (embeddingIntoAmbientBlowupSequence ι s hres hno hcen n) (s.center n) := rfl

theorem ambientBlowupSequence_isoObjZero :
    (ambientBlowupSequence ι s hres hno hcen).isoZero = refl X := rfl

theorem embeddingIntoAmbientBlowupSequence_zero :
    embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0 = s.isoZero.hom ≫ ι := rfl

theorem isPushforwardBlowupSeq_ambientBlowupSequence :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups (ambientBlowupSequence ι s hres hno hcen).toSequenceOfBlowups := by
  refine ⟨rfl, ⟨fun i _ => embeddingIntoAmbientBlowupSequence ι s hres hno hcen i,
    fun i _ => isClosedImmersion_embeddingIntoAmbientBlowupSequence ι s hres hno hcen i, ?_, ?_, ?_, ?_⟩⟩
  show (bdIzH s ≫ ι) ≫ 𝟙 X = bdIzH s ≫ ι
  exact comp_id _
  intro i hi
  rw [p50, p50]
  exact embeddingIntoAmbientBlowupSequence_succ_comp_map ι s hres hno hcen i
  intro i _
  rfl
  intro i hi
  rw [p50]
  exact ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen i hi
end




theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_eq {A A' B B' : Sch} {pi_ : A ⟶ B} {J : ISD B}
    (h : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf pi_ J) (hA : A = A') (hB : B = B') :
    FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf (eqToHom hA.symm ≫ pi_ ≫ eqToHom hB) $ comap J $ eqToHom hB.symm := by
  subst hA
  subst hB
  simpa only [eqToHom_refl, id_comp, comp_id,
    comap_id] using h

namespace BlowupSequenceData

variable {X : Sch}

theorem projectionToBase_congr (d : BlowupSequenceData X) {n n' : ℕ} (h : n = n') :
    projectionToBase d n = eqToHom (congrArg d.obj h) ≫ projectionToBase d n' := by
  subst h
  rw [eqToHom_refl, id_comp]

variable (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))

def appendSchemeAt (i : ℕ) : Sch :=
  if i ≤ length s then s.obj i else t.obj $ i - length s

section
variable {i : ℕ}
theorem appendSchemeAt_of_le_length (h : i ≤ length s) : appendSchemeAt s t i = s.obj i := if_pos h

theorem appendSchemeAt_of_length_lt (h : length s < i) :
    appendSchemeAt s t i = t.obj (i - length s) := if_neg $ not_le.2 h

theorem appendSchemeAt_succ_of_length_lt (h : length s < i) :
    appendSchemeAt s t (i + 1) = t.obj (i - length s + 1) := by
  have h2 : i + 1 - length s = i - length s + 1 := by omega
  rw [appendSchemeAt_of_length_lt s t $ by omega, h2]

theorem appendSchemeAt_succ_of_lt_length (h : i < length s) :
    appendSchemeAt s t (i + 1) = s.obj (i + 1) :=
  appendSchemeAt_of_le_length s t $ by omega

theorem appendSchemeAt_of_eq_length (h : i = length s) : appendSchemeAt s t i = s.obj s.length := by
  subst h
  exact appendSchemeAt_of_le_length s t le_rfl

theorem appendSchemeAt_succ_of_eq_length (h : i = length s) :
    appendSchemeAt s t (i + 1) = t.obj 1 := by
  subst h
  have h2 : length s + 1 - length s = 1 := by omega
  rw [appendSchemeAt_of_length_lt s t $ by omega, h2]
end

section
variable (i : ℕ)
def appendBlowupMorphism : appendSchemeAt s t (i + 1) ⟶ appendSchemeAt s t i :=
  if h : i < length s then
    eqToHom (appendSchemeAt_succ_of_lt_length s t h) ≫ s.map i ≫ eqToHom (appendSchemeAt_of_le_length s t $ le_of_lt h).symm
  else if h2 : length s < i then
    eqToHom (appendSchemeAt_succ_of_length_lt s t h2) ≫ t.map (i - length s) ≫
      eqToHom (appendSchemeAt_of_length_lt s t h2).symm
  else
    eqToHom (appendSchemeAt_succ_of_eq_length s t $ by omega) ≫ t.map 0 ≫ t.isoZero.hom ≫
      eqToHom (appendSchemeAt_of_eq_length s t $ by omega).symm

def appendCenter : IdealSheafData $ appendSchemeAt s t i :=
  if h : i < length s then comap (center s i) $ eqToHom $ appendSchemeAt_of_le_length s t $ le_of_lt h
  else if h2 : length s < i then comap (center t $ i - length s) $ eqToHom $ appendSchemeAt_of_length_lt s t h2
  else comap (comap (center t 0) t.isoZero.inv) $ eqToHom $ appendSchemeAt_of_eq_length s t $ by omega

theorem isBlowupAlongIdealSheaf_appendBlowupMorphism (hi : i < length s + length t) :
    Blowup.IsBlowupAlongIdealSheaf (appendBlowupMorphism s t i) $ appendCenter s t i := by
  rcases lt_trichotomy i s.length with h | h | h
  have hmap : appendBlowupMorphism s t i =
      eqToHom (appendSchemeAt_succ_of_lt_length s t h) ≫ s.map i ≫
        eqToHom (appendSchemeAt_of_le_length s t $ le_of_lt h).symm := dif_pos h
  have hcen : appendCenter s t i =
      comap (center s i) (eqToHom $ appendSchemeAt_of_le_length s t $ le_of_lt h) := dif_pos h
  rw [hmap, hcen]
  exact Blowup.IsBlowupAlongIdealSheaf.of_eq (s.isBlowup i h) (appendSchemeAt_succ_of_lt_length s t h).symm
    (appendSchemeAt_of_le_length s t $ le_of_lt h).symm
  subst h
  have ht : 0 < length t := by omega
  have hmap : appendBlowupMorphism s t s.length =
      eqToHom (appendSchemeAt_succ_of_eq_length s t rfl) ≫ t.map 0 ≫
        (bdIzH t) ≫
          eqToHom (appendSchemeAt_of_eq_length s t rfl).symm :=
    (dif_neg $ lt_irrefl s.length).trans $ dif_neg $ lt_irrefl s.length
  have hcen : appendCenter s t s.length =
      comap (cmI (center t 0) t.isoZero.inv)
        (eqToHom $ appendSchemeAt_of_eq_length s t rfl) :=
    (dif_neg $ lt_irrefl s.length).trans $ dif_neg $ lt_irrefl s.length
  rw [hmap, hcen, ← assoc (t.map 0) $ bdIzH t]
  exact Blowup.IsBlowupAlongIdealSheaf.of_eq (Blowup.IsBlowupAlongIdealSheaf.comp_iso_hom (t.isBlowup 0 ht) t.isoZero)
    (appendSchemeAt_succ_of_eq_length s t rfl).symm
    (appendSchemeAt_of_eq_length s t rfl).symm
  have hlt : i - length s < length t := by omega
  have hmap : appendBlowupMorphism s t i =
      eqToHom (appendSchemeAt_succ_of_length_lt s t h) ≫ t.map (i - length s) ≫
        eqToHom (appendSchemeAt_of_length_lt s t h).symm :=
    (dif_neg $ not_lt.2 $ le_of_lt h).trans $ dif_pos h
  have hcen : appendCenter s t i =
      comap (center t $ i - length s) (eqToHom $ appendSchemeAt_of_length_lt s t h) :=
    (dif_neg $ not_lt.2 $ le_of_lt h).trans $ dif_pos h
  rw [hmap, hcen]
  exact Blowup.IsBlowupAlongIdealSheaf.of_eq (t.isBlowup (i - length s) hlt)
    (appendSchemeAt_succ_of_length_lt s t h).symm (appendSchemeAt_of_length_lt s t h).symm
end

theorem appendSchemeAt_zero : appendSchemeAt s t 0 = s.obj 0 := appendSchemeAt_of_le_length s t $ zero_le _

def append : BlowupSequenceData X where
  length := length s + length t
  obj := appendSchemeAt s t
  map := appendBlowupMorphism s t
  isoZero := eqToIso (appendSchemeAt_zero s t) ≪≫ s.isoZero
  center := appendCenter s t
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_appendBlowupMorphism s t i hi

@[simp]
theorem append_length : length (s.append t) = length s + length t := rfl

section
variable {i : ℕ}
theorem append_schemeAt_of_le_length (h : i ≤ length s) : (s.append t).obj i = s.obj i :=
  appendSchemeAt_of_le_length s t h

section
variable (h : length s < i)
include h
theorem append_schemeAt_of_length_lt :
    (s.append t).obj i = t.obj (i - length s) :=
  appendSchemeAt_of_length_lt s t h

theorem append_schemeAt_succ_of_length_lt :
    (s.append t).obj (i + 1) = t.obj (i - length s + 1) :=
  appendSchemeAt_succ_of_length_lt s t h

theorem append_blowupMorphism_of_length_lt :
    (s.append t).map i =
      eqToHom (append_schemeAt_succ_of_length_lt s t h) ≫ t.map (i - length s) ≫
        eqToHom (append_schemeAt_of_length_lt s t h).symm := tr_ (dif_neg $ not_lt.2 $ le_of_lt h) $ dif_pos h

theorem append_center_of_length_lt :
    center (s.append t) i =
      comap (center t $ i - length s) (eqToHom $ append_schemeAt_of_length_lt s t h) := tr_ (dif_neg $ not_lt.2 $ le_of_lt h) $ dif_pos h
end

section
variable (h : i < length s)
include h
theorem append_schemeAt_succ_of_lt_length :
    (s.append t).obj (i + 1) = s.obj (i + 1) :=
  appendSchemeAt_succ_of_lt_length s t h

theorem append_blowupMorphism_of_lt_length :
    (s.append t).map i =
      eqToHom (append_schemeAt_succ_of_lt_length s t h) ≫ s.map i ≫
        eqToHom (append_schemeAt_of_le_length s t $ le_of_lt h).symm := dif_pos h

theorem append_center_of_lt_length :
    center (s.append t) i = comap (center s i) (eqToHom $ append_schemeAt_of_le_length s t $ le_of_lt h) := dif_pos h
end

theorem projectionToBase_append_of_le_length (h : i ≤ length s) :
    projectionToBase (s.append t) i = eqToHom (append_schemeAt_of_le_length s t h) ≫ projectionToBase s i := by
  revert h
  induction i with
  | zero =>
    intro _
    rfl
  | succ n ih =>
    intro h
    have hn := h
    rw [projectionToBase_succ, ih $ le_of_lt hn, append_blowupMorphism_of_lt_length s t hn, projectionToBase_succ]
    simp
end

section
variable {Y : Sch}
theorem blowupMorphism_eq_eqToHom_comp_of_eq (d : BlowupSequenceData Y) {n n' : ℕ} (h : n = n')
    (e1 : d.obj (n + 1) = d.obj (n' + 1)) (e2 : d.obj n' = d.obj n) :
    d.map n = eqToHom e1 ≫ d.map n' ≫ eqToHom e2 := by
  subst h
  simp

section
variable (a : BlowupSequenceData Y) (b : BlowupSequenceData (a.obj a.length)) (i j) (h : i = length a + j + 1)
include h
theorem append_blowupMorphism_of_eq_length_add_succ
    (e1 : (a.append b).obj (i + 1) = b.obj (j + 1 + 1))
    (e2 : b.obj (j + 1) = (a.append b).obj i) :
    (a.append b).map i = eqToHom e1 ≫ b.map (j + 1) ≫ eqToHom e2 := by
  subst h
  have hgt : length a < length a + j + 1 := by omega
  have hsub : length a + j + 1 - length a = j + 1 := by omega
  rw [append_blowupMorphism_of_length_lt a b hgt, blowupMorphism_eq_eqToHom_comp_of_eq b hsub (by rw [hsub]) $ by rw [hsub]]
  simp

theorem append_schemeAt_of_eq_length_add_succ :
    (a.append b).obj i = b.obj (j + 1) := by
  subst h
  have hgt : length a < length a + j + 1 := by omega
  have hsub : length a + j + 1 - length a = j + 1 := by omega
  rw [append_schemeAt_of_length_lt a b hgt, hsub]
end
end

theorem append_schemeAt_length_add_length (h : 0 < length t) :
    (s.append t).obj (length s + length t) = t.obj t.length := by
  have h2 : length s + length t - length s = length t := by omega
  show appendSchemeAt s t (length s + length t) = t.obj t.length
  rw [appendSchemeAt_of_length_lt s t $ by omega, h2]

theorem append_schemeAt_zero : (s.append t).obj 0 = s.obj 0 := appendSchemeAt_zero s t

theorem append_schemeAt_length_succ : (s.append t).obj (length s + 1) = t.obj 1 :=
  appendSchemeAt_succ_of_eq_length s t rfl

theorem append_isoObjZero_hom :
    (s.append t).isoZero.hom = eqToHom (append_schemeAt_zero s t) ≫ s.isoZero.hom := rfl

theorem append_blowupMorphism_length :
    (s.append t).map s.length =
      eqToHom (append_schemeAt_length_succ s t) ≫ t.map 0 ≫ t.isoZero.hom ≫
        eqToHom (append_schemeAt_of_le_length s t $ le_refl s.length).symm := tr_ (dif_neg $ lt_irrefl s.length) $ dif_neg $ lt_irrefl s.length

theorem append_center_length :
    center (s.append t) s.length =
      comap (comap (center t 0) t.isoZero.inv)
        (eqToHom $ append_schemeAt_of_le_length s t $ le_refl s.length) := tr_ (dif_neg $ lt_irrefl s.length) $ dif_neg $ lt_irrefl s.length

theorem projectionToBase_append_of_eq_length_add_succ {Y : Sch} (a : BlowupSequenceData Y)
    (b : BlowupSequenceData $ a.obj a.length) :
    ∀ j i, i = length a + j + 1 → ∀ (e : (a.append b).obj i = b.obj (j + 1)),
      projectionToBase (a.append b) i = eqToHom e ≫ projectionToBase b (j + 1) ≫ projectionToBase a a.length := by
  intro j
  induction j with
  | zero =>
      intro i hi e
      have hi' : i = length a + 1 := by omega
      subst hi'
      rw [projectionToBase_succ (a.append b) a.length, append_blowupMorphism_length a b,
        projectionToBase_append_of_le_length a b le_rfl, projectionToBase_succ b 0, projectionToBase_zero b]
      simp
  | succ n ih =>
      intro i hi e
      have hi' : i = length a + n + 1 + 1 := by omega
      subst hi'
      let _m0 := length a + n + 1
      rw [projectionToBase_succ (a.append b) _m0,
        append_blowupMorphism_of_eq_length_add_succ a b _m0 n rfl
          (append_schemeAt_of_eq_length_add_succ a b (length a + n + 1 + 1) (n + 1) $ by omega)
          (append_schemeAt_of_eq_length_add_succ a b _m0 n rfl).symm,
        ih _m0 rfl (append_schemeAt_of_eq_length_add_succ a b _m0 n rfl),
        projectionToBase_succ b $ n + 1]
      simp

theorem projectionToBase_append_of_length_lt {i : ℕ} (h : length s < i) :
    projectionToBase (s.append t) i =
      eqToHom (append_schemeAt_of_length_lt s t h) ≫ projectionToBase t (i - length s) ≫ projectionToBase s s.length := by
  obtain ⟨j, rfl⟩ : ∃ j, i = length s + j + 1 := ⟨i - length s - 1, by omega⟩
  have hsub : length s + j + 1 - length s = j + 1 := by omega
  rw [projectionToBase_congr t hsub,
    projectionToBase_append_of_eq_length_add_succ s t j (length s + j + 1) rfl
      (append_schemeAt_of_eq_length_add_succ s t (length s + j + 1) j rfl)]
  simp

end BlowupSequenceData

structure ComapIsoInvariance : Prop where
  coSupport_comap : ∀ {X Y : Sch} (e : X ≅ Y) (J : ISD Y) (n : ℕ),
    orderAtLeastLocus (comap J e.hom) n = ⇑e.hom.base ⁻¹' orderAtLeastLocus J n
  hasSNCWith_comap : ∀ {k : Type} [Field k] {X Y : Sch}
    (q : Y ⟶ Sp k) (e : X ≅ Y) (Z : ISD Y)
    (F : Bdy Y), HasStrictNormalCrossingsWith q Z F →
      HasStrictNormalCrossingsWith (e.hom ≫ q) (comap Z e.hom) (F.map fun D => comap D e.hom)
  smooth_comap : ∀ {k : Type} [Field k] {X Y : Sch}
    (q : Y ⟶ Sp k) (e : X ≅ Y) (Z : ISD Y),
    Smooth (subschemeι Z ≫ q) →
      Smooth (subschemeι (comap Z e.hom) ≫ e.hom ≫ q)
  strictTransform_comap : ∀ {X X1 Y : Sch} (pi_ : X1 ⟶ X) (e : X ≅ Y)
    (Z D : ISD Y),
    strictTransform (pi_ ≫ e.hom) Z D = strictTransform pi_ (comap Z e.hom) (comap D e.hom)

namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

variable (s : MarkedBlowupSequenceData p I m E)
  (t : MarkedBlowupSequenceData (s.proj s.toBlowupSequenceData.length ≫ p) (s.ideal s.toBlowupSequenceData.length) m
    $ s.boundary s.toBlowupSequenceData.length)

def appendToBlowupSequenceData : BlowupSequenceData X := s.toBlowupSequenceData.append t.toBlowupSequenceData

@[simp]
theorem appendToBlowupSequenceData_length :
    (s.appendToBlowupSequenceData t).length = s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := rfl

section
variable {i : ℕ}
theorem appendToBlowupSequenceData_schemeAt_of_le_length (h : i ≤ s.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).obj i = s.toBlowupSequenceData.obj i :=
  BlowupSequenceData.append_schemeAt_of_le_length s.toBlowupSequenceData t.toBlowupSequenceData h

section
variable (h : s.toBlowupSequenceData.length < i)
include h
theorem appendToBlowupSequenceData_schemeAt_of_length_lt :
    (s.appendToBlowupSequenceData t).obj i = t.toBlowupSequenceData.obj (i - s.toBlowupSequenceData.length) :=
  BlowupSequenceData.append_schemeAt_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_schemeAt_succ_of_length_lt :
    (s.appendToBlowupSequenceData t).obj (i + 1) =
      t.toBlowupSequenceData.obj (i - s.toBlowupSequenceData.length + 1) :=
  BlowupSequenceData.append_schemeAt_succ_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_blowupMorphism_of_length_lt :
    (s.appendToBlowupSequenceData t).map i =
      eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h) ≫
        t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length) ≫
        eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h).symm :=
  BlowupSequenceData.append_blowupMorphism_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_center_of_length_lt :
    (s.appendToBlowupSequenceData t).center i =
      comap (t.toBlowupSequenceData.center $ i - s.toBlowupSequenceData.length)
        (eqToHom $ appendToBlowupSequenceData_schemeAt_of_length_lt s t h) :=
  BlowupSequenceData.append_center_of_length_lt s.toBlowupSequenceData t.toBlowupSequenceData h
end

section
variable (h : i < s.toBlowupSequenceData.length)
include h
theorem appendToBlowupSequenceData_schemeAt_succ_of_lt_length :
    (s.appendToBlowupSequenceData t).obj (i + 1) = s.toBlowupSequenceData.obj (i + 1) :=
  BlowupSequenceData.append_schemeAt_succ_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_blowupMorphism_of_lt_length :
    (s.appendToBlowupSequenceData t).map i =
      eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h) ≫ s.toBlowupSequenceData.map i ≫
        eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_of_lt h).symm :=
  BlowupSequenceData.append_blowupMorphism_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h

theorem appendToBlowupSequenceData_center_of_lt_length :
    (s.appendToBlowupSequenceData t).center i =
      comap (s.toBlowupSequenceData.center i) (eqToHom $ appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_of_lt h) :=
  BlowupSequenceData.append_center_of_lt_length s.toBlowupSequenceData t.toBlowupSequenceData h
end
end

theorem map_strictTransform_comp_iso_hom (hinv : ComapIsoInvariance) {A B C : Sch}
    (f : A ⟶ B) (e : B ≅ C) (Z : ISD B) (Lst : Bdy C)
    (Lst1 : Bdy A)
    (hL1 : Lst1 = (Lst.map fun D => comap D e.hom).map (strictTransform f Z) ++
      [exceptionalIdeal f Z]) :
    Lst1 = Lst.map (strictTransform (f ≫ e.hom) $ comap Z e.inv) ++
      [exceptionalIdeal (f ≫ e.hom) $ comap Z e.inv] := by
  have hZ : comap (comap Z e.inv) e.hom = Z := by
    rw [← comap_comp, e.hom_inv_id,
      comap_id]
  let _a0 := f ≫ isoH e
  have hfun : (strictTransform f Z) ∘ (fun D : ISD C => cmI D e.hom) =
      strictTransform _a0 (cmI Z e.inv) := by
    funext D
    dsimp
    rw [hinv.strictTransform_comap f e (comap Z e.inv) D, hZ]
  have hexc : exceptionalIdeal _a0 (comap Z e.inv) = exceptionalIdeal f Z := by
    rw [exceptionalIdeal_eq_comap, exceptionalIdeal_eq_comap,
      comap_comp, hZ]
  rw [hL1, List.map_map, hfun, hexc]

section
variable (i : ℕ)
def appendProjectionToBase : (s.appendToBlowupSequenceData t).obj i ⟶ X :=
  if h : i ≤ s.toBlowupSequenceData.length then
    eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h) ≫ s.proj i
  else
    eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t $ not_le.1 h) ≫ t.proj (i - s.toBlowupSequenceData.length) ≫
      s.proj s.toBlowupSequenceData.length

def appendIdeal : IdealSheafData $ (s.appendToBlowupSequenceData t).obj i :=
  if h : i ≤ s.toBlowupSequenceData.length then
    comap (s.ideal i) $ eqToHom $ appendToBlowupSequenceData_schemeAt_of_le_length s t h
  else
    comap (t.ideal $ i - s.toBlowupSequenceData.length) $ eqToHom $ appendToBlowupSequenceData_schemeAt_of_length_lt s t $ not_le.1 h

def appendBoundary : List ((s.appendToBlowupSequenceData t).obj i).IdealSheafData :=
  if h : i ≤ s.toBlowupSequenceData.length then
    (s.boundary i).map fun D => comap D $ eqToHom $ appendToBlowupSequenceData_schemeAt_of_le_length s t h
  else
    (t.boundary $ i - s.toBlowupSequenceData.length).map
      (fun D => comap D $ eqToHom $ appendToBlowupSequenceData_schemeAt_of_length_lt s t $ not_le.1 h)
end

section
variable {i : ℕ}
section
variable (h : i ≤ s.toBlowupSequenceData.length)
theorem appendProjectionToBase_of_le_length :
    s.appendProjectionToBase t i = eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t h) ≫ s.proj i :=
  dif_pos h

theorem appendIdeal_of_le_length :
    s.appendIdeal t i = comap (s.ideal i) (eqToHom $ appendToBlowupSequenceData_schemeAt_of_le_length s t h) :=
  dif_pos h

theorem appendBoundary_of_le_length :
    s.appendBoundary t i =
      (s.boundary i).map fun D => comap D $ eqToHom $ appendToBlowupSequenceData_schemeAt_of_le_length s t h :=
  dif_pos h
end

section
variable (h : s.toBlowupSequenceData.length < i)
theorem appendProjectionToBase_of_length_lt :
    s.appendProjectionToBase t i =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) ≫ t.proj (i - s.toBlowupSequenceData.length) ≫
        s.proj s.toBlowupSequenceData.length :=
  dif_neg $ not_le.2 h

theorem appendIdeal_of_length_lt :
    s.appendIdeal t i =
      comap (t.ideal $ i - s.toBlowupSequenceData.length) (eqToHom $ appendToBlowupSequenceData_schemeAt_of_length_lt s t h) :=
  dif_neg $ not_le.2 h

theorem appendBoundary_of_length_lt :
    s.appendBoundary t i =
      (t.boundary $ i - s.toBlowupSequenceData.length).map
        (fun D => comap D $ eqToHom $ appendToBlowupSequenceData_schemeAt_of_length_lt s t h) :=
  dif_neg $ not_le.2 h
end
end

section
variable {A B : Sch} (e : A ≅ B)
theorem comap_comap_hom_inv
    (D : ISD B) : comap (comap D e.hom) e.inv = D := by
  rw [← comap_comp, e.inv_hom_id,
    comap_id]

theorem map_comap_hom_map_comap_inv
    (F : Bdy B) :
    ((F.map fun D => comap D e.hom).map fun D => comap D e.inv) = F := by
  induction F with
  | nil => rfl
  | cons D L ih => simp [map_cons, ih, comap_comap_hom_inv]

theorem comap_comap_inv_hom (D : ISD A) :
    comap (comap D e.inv) e.hom = D := by
  rw [← comap_comp, e.hom_inv_id,
    comap_id]
end

section
variable {A A' B B' : Sch}
theorem exceptionalIdeal_pow_mul_comap_eqToHom (eA : A = A')
    (eB : B = B') (g : A' ⟶ B') (Z J : ISD B') (J' : ISD A') (n : ℕ)
    (h : exceptionalIdeal g Z ^ n * J' = comap J g) :
    exceptionalIdeal (eqToHom eA ≫ g ≫ eqToHom eB.symm) (comap Z $ eqToHom eB) ^ n *
        comap J' (eqToHom eA) =
      comap (comap J $ eqToHom eB) (eqToHom eA ≫ g ≫ eqToHom eB.symm) := by
  subst eA
  subst eB
  simp [eqToHom_refl, id_comp, comp_id,
    comap_id]
  exact h

theorem map_strictTransform_comap_eqToHom
    (hA : A = A') (hB : B = B') (f : A' ⟶ B') (Z : ISD B')
    (Lst : Bdy B') (Lst1 : Bdy A')
    (hL : Lst1 = Lst.map (strictTransform f Z) ++ [exceptionalIdeal f Z]) :
    Lst1.map (fun D => comap D $ eqToHom hA) =
      (Lst.map fun D => comap D $ eqToHom hB).map
          (strictTransform (eqToHom hA ≫ f ≫ eqToHom hB.symm) $ comap Z $ eqToHom hB) ++
        [exceptionalIdeal (eqToHom hA ≫ f ≫ eqToHom hB.symm) $ comap Z $ eqToHom hB] := by
  subst hA
  subst hB
  subst hL
  simp [comap_id]
end

theorem comap_eqToHom_congr {A : Sch} (F : ℕ → Sch)
    (G : ∀ n : ℕ, IdealSheafData $ F n) {i j : ℕ} (hij : i = j)
    (hi : A = F i) (hj : A = F j) :
    comap (G i) (eqToHom hi) = comap (G j) (eqToHom hj) := by
  subst hij
  rfl

theorem map_comap_eqToHom_congr {A : Sch}
    {F : ℕ → Sch} (B : ∀ n : ℕ, List (F n).IdealSheafData) (i j : ℕ) (hij : i = j)
    (e : A = F i) (e' : A = F j) :
    (B i).map (fun D => comap D $ eqToHom e) = (B j).map fun D => comap D $ eqToHom e' := by
  subst hij
  rfl

section
variable {K : Type} [Field K] {A B : Sch}
theorem hasStrictNormalCrossingsWith_comap_eqToHom
    (h : A = B) (q : B ⟶ Sp K) (Z : ISD B)
    (F : Bdy B) (hZ : HasStrictNormalCrossingsWith q Z F) :
    HasStrictNormalCrossingsWith (eqToHom h ≫ q) (comap Z $ eqToHom h)
      (F.map fun D => comap D $ eqToHom h) := by
  subst h
  simpa [comap_id] using hZ

theorem hasStrictNormalCrossingsWith_comap_iso_inv
    (hinv : ComapIsoInvariance) (e : A ≅ B) (q : B ⟶ Sp K)
    (Z : ISD A) (F : Bdy B)
    (hZ : HasStrictNormalCrossingsWith (e.hom ≫ q) Z $ F.map fun D => comap D e.hom) :
    HasStrictNormalCrossingsWith q (comap Z e.inv) F := by
  have h2 := hinv.hasSNCWith_comap (isoH e ≫ q) e.symm Z (F.map fun D => cmI D e.hom) hZ
  rwa [symm_hom, inv_hom_id_assoc, map_comap_hom_map_comap_inv e F] at h2
end

private theorem projectionToBase_congr (d : MarkedBlowupSequenceData p I m E) {i j : ℕ} (h : i = j) :
    d.proj i = eqToHom (congrArg d.toBlowupSequenceData.obj h) ≫ d.proj j := by
  subst h
  simp

theorem appendToBlowupSequenceData_schemeAt_length_add_length (h : 0 < t.toBlowupSequenceData.length) :
    (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      t.toBlowupSequenceData.obj t.toBlowupSequenceData.length :=
  BlowupSequenceData.append_schemeAt_length_add_length s.toBlowupSequenceData t.toBlowupSequenceData h

private theorem map_comap_eqToHom_comp {A B C : Sch} (h : A = B) (g : B ⟶ C)
    (L : Bdy C) :
    (L.map fun D => comap D g).map (fun D => comap D $ eqToHom h) =
      L.map fun D => comap D $ eqToHom h ≫ g :=by simp_all
theorem appendToBlowupSequenceData_schemeAt_zero : (s.appendToBlowupSequenceData t).obj 0 = s.toBlowupSequenceData.obj 0 :=
  BlowupSequenceData.append_schemeAt_zero s.toBlowupSequenceData t.toBlowupSequenceData

theorem appendToBlowupSequenceData_schemeAt_length_succ :
    (s.appendToBlowupSequenceData t).obj (s.toBlowupSequenceData.length + 1) = t.toBlowupSequenceData.obj 1 :=
  BlowupSequenceData.append_schemeAt_length_succ s.toBlowupSequenceData t.toBlowupSequenceData

theorem appendToBlowupSequenceData_isoObjZero_hom :
    (s.appendToBlowupSequenceData t).isoZero.hom =
      eqToHom (appendToBlowupSequenceData_schemeAt_zero s t) ≫ s.toBlowupSequenceData.isoZero.hom := rfl

theorem appendToBlowupSequenceData_blowupMorphism_length :
    (s.appendToBlowupSequenceData t).map s.toBlowupSequenceData.length =
      eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t) ≫ t.toBlowupSequenceData.map 0 ≫
        t.toBlowupSequenceData.isoZero.hom ≫
        eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_refl s.toBlowupSequenceData.length).symm :=
  BlowupSequenceData.append_blowupMorphism_length s.toBlowupSequenceData t.toBlowupSequenceData

theorem appendToBlowupSequenceData_center_length :
    (s.appendToBlowupSequenceData t).center s.toBlowupSequenceData.length =
      comap (comap (t.toBlowupSequenceData.center 0) t.toBlowupSequenceData.isoZero.inv)
        (eqToHom $ appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_refl s.toBlowupSequenceData.length) :=
  BlowupSequenceData.append_center_length s.toBlowupSequenceData t.toBlowupSequenceData

theorem appendIdeal_length_succ :
    s.appendIdeal t (s.toBlowupSequenceData.length + 1) =
      comap (t.ideal 1) (eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t)) := by
  have hlt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + 1 := lt_succ_self _
  refine tr_ (appendIdeal_of_length_lt s t hlt) ?_
  exact comap_eqToHom_congr t.toBlowupSequenceData.obj
    t.ideal (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t hlt)
    (appendToBlowupSequenceData_schemeAt_length_succ s t)

theorem appendBoundary_length_succ :
    s.appendBoundary t (s.toBlowupSequenceData.length + 1) =
      (t.boundary 1).map fun D => comap D (eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t)) := by
  have hlt : mbsLen s < mbsLen s + 1 := lt_succ_self _
  refine tr_ (appendBoundary_of_length_lt s t hlt) ?_
  exact map_comap_eqToHom_congr
    (A := (s.appendToBlowupSequenceData t).obj (mbsLen s + 1))
    (F := mbsObj t) t.boundary
    (mbsLen s + 1 - mbsLen s) 1 (by omega)
    (appendToBlowupSequenceData_schemeAt_of_length_lt s t hlt) (appendToBlowupSequenceData_schemeAt_length_succ s t)

theorem appendProjectionToBase_zero : s.appendProjectionToBase t 0 = (s.appendToBlowupSequenceData t).isoZero.hom := by
  rw [appendProjectionToBase_of_le_length s t $ zero_le _, appendToBlowupSequenceData_isoObjZero_hom, s.proj_zero]

theorem appendProjectionToBase_succ (i : ℕ) :
    s.appendProjectionToBase t (i + 1) = (s.appendToBlowupSequenceData t).map i ≫ s.appendProjectionToBase t i := by
  rcases lt_trichotomy i (mbsLen s) with h | h | h
  have h1 : i + 1 ≤ mbsLen s := by omega
  rw [appendProjectionToBase_of_le_length s t h1, appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendProjectionToBase_of_le_length s t $ le_of_lt h,
    s.proj_succ i]
  simp
  subst h
  have hlt : mbsLen s < mbsLen s + 1 := by omega
  have hsub : mbsLen s + 1 - mbsLen s = 1 := by omega
  rw [appendProjectionToBase_of_length_lt s t hlt, appendToBlowupSequenceData_blowupMorphism_length s t,
    appendProjectionToBase_of_le_length s t $ le_refl $ mbsLen s,
    projectionToBase_congr t hsub, t.proj_succ 0, t.proj_zero]
  simp
  have h1 : mbsLen s < i + 1 := by omega
  have hsub : i + 1 - mbsLen s = (i - mbsLen s) + 1 := by omega
  rw [appendProjectionToBase_of_length_lt s t h1, appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendProjectionToBase_of_length_lt s t h,
    projectionToBase_congr t hsub, t.proj_succ _]
  simp

section
variable (hinv : ComapIsoInvariance) (i) (hi : i < (s.appendToBlowupSequenceData t).length)
include hinv hi
theorem center_support_subset_orderAtLeastLocus_appendIdeal :
    (((s.appendToBlowupSequenceData t).center i).support : Set ↥((s.appendToBlowupSequenceData t).obj i)) ⊆
      orderAtLeastLocus (s.appendIdeal t i) m := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  have hcomp : ∀ (V W T : Sch) (f : V ⟶ W) (g : W ⟶ T) (J : ISD T),
      J.comap (f ≫ g) = cmI (cmI J g) f := by simp_all
  have key : ∀ (A B : Sch) (hAB : A = B) (C K : ISD B),
      (C.supp ⊆ orderAtLeastLocus K m) →
      ((spI (cmI C $ eqToHom hAB) : Set ↥A) ⊆ orderAtLeastLocus (cmI K $ eqToHom hAB) m) := by
    intro A B hAB C K h
    subst hAB
    simpa only [eqToHom_refl, comap_id] using h
  have keyIso : ∀ (A B : Sch) (e : A ≅ B) (C : ISD A) (K : ISD B),
      (C.supp ⊆ orderAtLeastLocus (cmI K e.hom) m) →
      ((spI (cmI C e.inv) : Set ↥B) ⊆ orderAtLeastLocus K m) := by
    intro A B e C K h
    have hK : cmI (cmI K e.hom) e.inv = K := by
      rw [← hcomp, e.inv_hom_id, comap_id]
    have h2 : orderAtLeastLocus (cmI (cmI K e.hom) e.inv) m
        = ⇑e.inv.base ⁻¹' orderAtLeastLocus (cmI K e.hom) m :=
      hinv.coSupport_comap e.symm (cmI K e.hom) m
    rw [hK] at h2
    have hsupp : (spI (cmI C e.inv) : Set ↥B) = preimage e.inv.base C.support := by
      simp
    rw [hsupp, h2]
    exact preimage_mono h
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  rw [appendToBlowupSequenceData_center_of_lt_length s t h, appendIdeal_of_le_length s t $ le_of_lt h]
  exact key _ _ (appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_of_lt h) (s.toBlowupSequenceData.center i) (s.ideal i)
    (s.center_order i h)
  subst h
  have ht0 : 0 < t.toBlowupSequenceData.length := by omega
  have hb := t.center_order 0 ht0
  rw [t.ideal_zero] at hb
  have hbase := keyIso _ _ t.toBlowupSequenceData.isoZero (t.toBlowupSequenceData.center 0)
    (s.ideal s.toBlowupSequenceData.length) hb
  rw [appendToBlowupSequenceData_center_length s t,
    appendIdeal_of_le_length s t $ le_refl s.toBlowupSequenceData.length]
  exact key _ _ (appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_refl s.toBlowupSequenceData.length)
    (cmI (t.toBlowupSequenceData.center 0) t.toBlowupSequenceData.isoZero.inv)
    (s.ideal s.toBlowupSequenceData.length) hbase
  have hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
  rw [appendToBlowupSequenceData_center_of_length_lt s t h, appendIdeal_of_length_lt s t h]
  exact key _ _ (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)
    (t.toBlowupSequenceData.center $ i - s.toBlowupSequenceData.length)
    (t.ideal $ i - s.toBlowupSequenceData.length)
    (t.center_order (i - s.toBlowupSequenceData.length) hsub)

theorem smooth_center_comp_appendProjectionToBase :
    Smooth
      (((s.appendToBlowupSequenceData t).center i).subschemeι ≫ s.appendProjectionToBase t i ≫ p) := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  rw [appendProjectionToBase_of_le_length s t (le_of_lt h), appendToBlowupSequenceData_center_of_lt_length s t h]
  have hA := hinv.smooth_comap (s.proj i ≫ p)
    (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h))) (s.toBlowupSequenceData.center i)
    (s.center_smooth i h)
  simpa only [eqToIso.hom, assoc] using hA
  subst h
  have ht0 : 0 < t.toBlowupSequenceData.length := by omega
  have hsm := t.center_smooth 0 ht0
  rw [t.proj_zero] at hsm
  have hT := hinv.smooth_comap
    (t.toBlowupSequenceData.isoZero.hom ≫ s.proj s.toBlowupSequenceData.length ≫ p)
    t.toBlowupSequenceData.isoZero.symm (t.toBlowupSequenceData.center 0) hsm
  simp [symm_hom, inv_hom_id_assoc] at hT
  rw [appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), appendToBlowupSequenceData_center_length s t]
  have hB := hinv.smooth_comap (s.proj s.toBlowupSequenceData.length ≫ p)
    (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)))
    (cmI (t.toBlowupSequenceData.center 0) t.toBlowupSequenceData.isoZero.inv) hT
  simpa only [eqToIso.hom, assoc] using hB
  rw [appendProjectionToBase_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h]
  have hC := hinv.smooth_comap
    (t.proj (i - s.toBlowupSequenceData.length) ≫ s.proj s.toBlowupSequenceData.length ≫ p)
    (eqToIso (appendToBlowupSequenceData_schemeAt_of_length_lt s t h))
    (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
    (t.center_smooth (i - s.toBlowupSequenceData.length) (by omega))
  simpa only [eqToIso.hom, assoc] using hC

theorem hasStrictNormalCrossingsWith_appendBoundary :
    HasStrictNormalCrossingsWith (s.appendProjectionToBase t i ≫ p) ((s.appendToBlowupSequenceData t).center i)
      (s.appendBoundary t i) := by
  have hlen : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  rw [appendProjectionToBase_of_le_length s t (le_of_lt h), appendToBlowupSequenceData_center_of_lt_length s t h,
    appendBoundary_of_le_length s t (le_of_lt h)]
  simp [assoc]
  exact hasStrictNormalCrossingsWith_comap_eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.proj i ≫ p)
    (s.toBlowupSequenceData.center i) (s.boundary i) (s.center_snc i h)
  subst h
  have ht : 0 < t.toBlowupSequenceData.length := by omega
  have H0 := t.center_snc 0 ht
  rw [t.proj_zero, t.boundary_zero] at H0
  have H1 := hasStrictNormalCrossingsWith_comap_iso_inv hinv t.toBlowupSequenceData.isoZero
    (s.proj s.toBlowupSequenceData.length ≫ p) (t.toBlowupSequenceData.center 0)
    (s.boundary s.toBlowupSequenceData.length) H0
  rw [appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), appendToBlowupSequenceData_center_length s t,
    appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length)]
  simp [assoc]
  exact hasStrictNormalCrossingsWith_comap_eqToHom
    (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
    (s.proj s.toBlowupSequenceData.length ≫ p)
    (cmI (t.toBlowupSequenceData.center 0) t.toBlowupSequenceData.isoZero.inv)
    (s.boundary s.toBlowupSequenceData.length) H1
  have hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
  rw [appendProjectionToBase_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h, appendBoundary_of_length_lt s t h]
  simp [assoc]
  exact hasStrictNormalCrossingsWith_comap_eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)
    (t.proj (i - s.toBlowupSequenceData.length) ≫ s.proj s.toBlowupSequenceData.length ≫ p)
    (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
    (t.boundary (i - s.toBlowupSequenceData.length))
    (t.center_snc (i - s.toBlowupSequenceData.length) hsub)

theorem appendBoundary_succ :
    s.appendBoundary t (i + 1) =
      (s.appendBoundary t i).map
          (strictTransform ((s.appendToBlowupSequenceData t).map i) ((s.appendToBlowupSequenceData t).center i)) ++
        [exceptionalIdeal ((s.appendToBlowupSequenceData t).map i) ((s.appendToBlowupSequenceData t).center i)] := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  have h1 : i + 1 ≤ s.toBlowupSequenceData.length := by omega
  rw [appendBoundary_of_le_length s t h1, appendBoundary_of_le_length s t (le_of_lt h),
    appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendToBlowupSequenceData_center_of_lt_length s t h]
  exact map_strictTransform_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h)
    (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.map i) (mbsCtr s i)
    (s.boundary i) (s.boundary (i + 1)) (s.boundary_succ i h)
  subst h
  have ht0 : 0 < t.toBlowupSequenceData.length := by omega
  have hL1 : t.boundary 1 =
      ((s.boundary s.toBlowupSequenceData.length).map
          (·.comap t.toBlowupSequenceData.isoZero.hom)).map
          (p6 (t.toBlowupSequenceData.map 0) $ t.toBlowupSequenceData.center 0) ++
        [p5 (t.toBlowupSequenceData.map 0) $ mbsCtr t 0] := by
    rw [t.boundary_succ 0 ht0, t.boundary_zero]
  have hb1 := map_strictTransform_comp_iso_hom hinv (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero
    (mbsCtr t 0) (s.boundary s.toBlowupSequenceData.length) (t.boundary 1) hL1
  rw [appendBoundary_length_succ s t,
    appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length),
    appendToBlowupSequenceData_blowupMorphism_length s t, appendToBlowupSequenceData_center_length s t,
    ← assoc (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero.hom]
  exact map_strictTransform_comap_eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t)
    (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
    (t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom)
    (cmI (t.toBlowupSequenceData.center 0) t.toBlowupSequenceData.isoZero.inv)
    (s.boundary s.toBlowupSequenceData.length) (t.boundary 1) hb1
  have hlt : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
  have hsucc : s.toBlowupSequenceData.length < i + 1 := by omega
  have hidx : i + 1 - s.toBlowupSequenceData.length = i - s.toBlowupSequenceData.length + 1 := by omega
  let _a2 := appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h
  rw [appendBoundary_of_length_lt s t hsucc, appendBoundary_of_length_lt s t h,
    appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h,
    map_comap_eqToHom_congr (A := (s.appendToBlowupSequenceData t).obj (i + 1))
      (F := mbsObj t) t.boundary
      (i + 1 - mbsLen s) (i - mbsLen s + 1) hidx
      (appendToBlowupSequenceData_schemeAt_of_length_lt s t hsucc) _a2]
  exact map_strictTransform_comap_eqToHom _a2
    (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) (t.toBlowupSequenceData.map (i - mbsLen s))
    (mbsCtr t (i - mbsLen s))
    (t.boundary (i - mbsLen s))
    (t.boundary (i - mbsLen s + 1))
    (t.boundary_succ (i - mbsLen s) hlt)
end

theorem appendIdeal_zero : s.appendIdeal t 0 = comap I (s.appendToBlowupSequenceData t).isoZero.hom := by
  rw [appendIdeal_of_le_length s t $ zero_le _, s.ideal_zero, appendToBlowupSequenceData_isoObjZero_hom]
  exact sy_ $ comap_comp ..

theorem appendBoundary_zero :
    s.appendBoundary t 0 = E.map fun D => comap D (s.appendToBlowupSequenceData t).isoZero.hom := by
  rw [appendBoundary_of_le_length s t $ zero_le _, appendToBlowupSequenceData_isoObjZero_hom, s.boundary_zero]
  exact map_comap_eqToHom_comp (appendToBlowupSequenceData_schemeAt_of_le_length s t $ zero_le _)
    s.toBlowupSequenceData.isoZero.hom E

theorem exceptionalIdeal_pow_mul_appendIdeal_succ (_hinv : ComapIsoInvariance) (i : ℕ)
    (hi : i < (s.appendToBlowupSequenceData t).length) :
    exceptionalIdeal ((s.appendToBlowupSequenceData t).map i) ((s.appendToBlowupSequenceData t).center i) ^ m *
        s.appendIdeal t (i + 1) =
      (s.appendIdeal t i).comap ((s.appendToBlowupSequenceData t).map i) := by
  have hi' : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with h | h | h
  have h1 : i + 1 ≤ s.toBlowupSequenceData.length := h
  rw [appendToBlowupSequenceData_blowupMorphism_of_lt_length s t h, appendToBlowupSequenceData_center_of_lt_length s t h, appendIdeal_of_le_length s t h1,
    appendIdeal_of_le_length s t (le_of_lt h)]
  exact exceptionalIdeal_pow_mul_comap_eqToHom (appendToBlowupSequenceData_schemeAt_succ_of_lt_length s t h)
    (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h)) (s.toBlowupSequenceData.map i) (s.toBlowupSequenceData.center i)
    (s.ideal i) (s.ideal (i + 1)) m (s.ideal_succ i h)
  subst h
  have ht0 : 0 < t.toBlowupSequenceData.length := by omega
  let _a0 := t.toBlowupSequenceData.map 0 ≫ t.toBlowupSequenceData.isoZero.hom
  let _a3 := cmI (t.toBlowupSequenceData.center 0) t.toBlowupSequenceData.isoZero.inv
  have hExceptional : exceptionalIdeal _a0
      _a3 ^ m * t.ideal 1 =
      (s.ideal s.toBlowupSequenceData.length).comap
        _a0 := by
    rw [exceptionalIdeal_eq_comap,
      comap_comp,
      comap_comp,
      comap_comap_inv_hom t.toBlowupSequenceData.isoZero (t.toBlowupSequenceData.center 0),
      ← t.ideal_zero]
    simpa only [exceptionalIdeal_eq_comap, zero_add] using t.ideal_succ 0 ht0
  rw [appendToBlowupSequenceData_blowupMorphism_length s t, appendToBlowupSequenceData_center_length s t,
    appendIdeal_length_succ s t, appendIdeal_of_le_length s t (le_refl s.toBlowupSequenceData.length),
    ← assoc (t.toBlowupSequenceData.map 0) t.toBlowupSequenceData.isoZero.hom]
  exact exceptionalIdeal_pow_mul_comap_eqToHom (appendToBlowupSequenceData_schemeAt_length_succ s t)
    (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))
    _a0
    _a3
    (s.ideal s.toBlowupSequenceData.length) (t.ideal 1) m hExceptional
  have h1 : s.toBlowupSequenceData.length < i + 1 := by omega
  have hsub : i - s.toBlowupSequenceData.length < t.toBlowupSequenceData.length := by omega
  let _a1 := appendToBlowupSequenceData_schemeAt_succ_of_length_lt s t h
  let _a2 := t.ideal $ i - s.toBlowupSequenceData.length + 1
  have hidx : s.appendIdeal t (i + 1) =
      _a2.comap
        (eqToHom _a1) := by
    rw [appendIdeal_of_length_lt s t h1]
    exact comap_eqToHom_congr t.toBlowupSequenceData.obj
      t.ideal (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t h1)
      _a1
  rw [appendToBlowupSequenceData_blowupMorphism_of_length_lt s t h, appendToBlowupSequenceData_center_of_length_lt s t h, hidx, appendIdeal_of_length_lt s t h]
  exact exceptionalIdeal_pow_mul_comap_eqToHom _a1
    (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)
    (t.toBlowupSequenceData.map (i - s.toBlowupSequenceData.length))
    (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length))
    (t.ideal (i - s.toBlowupSequenceData.length))
    _a2 m
    (t.ideal_succ (i - s.toBlowupSequenceData.length) hsub)

section
variable (hinv : ComapIsoInvariance)
def append : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := s.appendToBlowupSequenceData t
  proj := s.appendProjectionToBase t
  proj_zero := appendProjectionToBase_zero s t
  proj_succ := appendProjectionToBase_succ s t
  ideal := s.appendIdeal t
  boundary := s.appendBoundary t
  ideal_zero := appendIdeal_zero s t
  boundary_zero := appendBoundary_zero s t
  center_order := fun i hi => center_support_subset_orderAtLeastLocus_appendIdeal s t hinv i hi
  center_smooth := fun i hi => smooth_center_comp_appendProjectionToBase s t hinv i hi
  center_snc := fun i hi => hasStrictNormalCrossingsWith_appendBoundary s t hinv i hi
  ideal_succ := fun i hi => exceptionalIdeal_pow_mul_appendIdeal_succ s t hinv i hi
  boundary_succ := fun i hi => appendBoundary_succ s t hinv i hi

theorem append_schemeAt_of_le_length {i : ℕ} (h : i ≤ s.toBlowupSequenceData.length) :
    (s.append t hinv).toBlowupSequenceData.obj i = s.toBlowupSequenceData.obj i :=
  appendToBlowupSequenceData_schemeAt_of_le_length s t h

theorem append_schemeAt_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    (s.append t hinv).toBlowupSequenceData.obj i =
      t.toBlowupSequenceData.obj (i - s.toBlowupSequenceData.length) :=
  appendToBlowupSequenceData_schemeAt_of_length_lt s t h

section
variable (i : ℕ)
theorem append_projectionToBase :
    (s.append t hinv).proj i = s.appendProjectionToBase t i := rfl

theorem append_ideal :
    (s.append t hinv).ideal i = s.appendIdeal t i := rfl

theorem append_boundary :
    (s.append t hinv).boundary i = s.appendBoundary t i := rfl
end

theorem append_ideal_length_add_length (h : 0 < t.toBlowupSequenceData.length) :
    (s.append t hinv).ideal (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.ideal t.toBlowupSequenceData.length).comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h)) := by
  have hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := by omega
  let _a0 := appendToBlowupSequenceData_schemeAt_length_add_length s t h
  have key : s.appendIdeal t (mbsLen s + mbsLen t) =
      cmI (t.ideal (mbsLen t)) (eqToHom _a0) := by
    rw [appendIdeal_of_length_lt s t hgt]
    exact comap_eqToHom_congr t.toBlowupSequenceData.obj
      t.ideal (by omega) (appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt)
      _a0
  exact key

theorem append_boundary_length_add_length (h : 0 < t.toBlowupSequenceData.length) :
    (s.append t hinv).boundary (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.boundary t.toBlowupSequenceData.length).map
        (fun D => D.comap (eqToHom (appendToBlowupSequenceData_schemeAt_length_add_length s t h))) := by
  have hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := by omega
  refine tr_ (appendBoundary_of_length_lt s t hgt) ?_
  exact map_comap_eqToHom_congr
    (A := (s.appendToBlowupSequenceData t).obj (mbsLen s + mbsLen t))
    (F := t.toBlowupSequenceData.obj) t.boundary
    (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length - s.toBlowupSequenceData.length)
    t.toBlowupSequenceData.length (by omega)
    (appendToBlowupSequenceData_schemeAt_of_length_lt s t hgt) (appendToBlowupSequenceData_schemeAt_length_add_length s t h)

@[simp]
theorem append_toBlowupSequenceData :
    (s.append t hinv).toBlowupSequenceData = s.appendToBlowupSequenceData t := rfl

@[simp]
theorem append_length :
    (s.append t hinv).toBlowupSequenceData.length =
      s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := rfl

@[simp]
theorem append_toMarkedSequence_length :
    (s.append t hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length =
      s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := rfl
end

end MarkedBlowupSequenceData





section
variable {X Y : Sch}
section
variable (e : X ≅ Y)
theorem iso_inv_base_hom_base_apply (x : X) :
    e.inv.base (e.hom.base x) = x := by
  simp

theorem orderAtLeastLocus_comap_iso_hom_eq_preimage (J : ISD Y) (n : ℕ) :
    orderAtLeastLocus (comap J e.hom) n = ⇑e.hom.base ⁻¹' orderAtLeastLocus J n := by
  ext x
  have h2 := orderAt_le_orderAt_comap e.inv (cmI J e.hom) $ ihB_ e x
  rw [iso_inv_base_hom_base_apply e x, ← comap_comp, e.inv_hom_id, comap_id] at h2
  simp [mem_preimage, mem_orderAtLeastLocus_iff]
  exact ⟨fun hm => le_trans hm h2, fun hm => le_trans hm $ orderAt_le_orderAt_comap e.hom J x⟩

theorem iso_hom_base_inv_base_apply (y : Y) :
    e.hom.base (e.inv.base y) = y := by
  simp

theorem isIso_resLE_iso_hom (U : Opn Y) :
    IsIso $ e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl := by
  let _a0 := (m54 $ ihB_ e).obj U
  have h1 : U ≤ (m54 $ ibM e).obj _a0 := by
    intro y hy
    show ihB_ e (ibM e y) ∈ U
    rwa [iso_hom_base_inv_base_apply e y]
  refine ⟨e.inv.resLE _a0 U h1, ?_, ?_⟩
  rw [← cancel_mono $ p4 _a0, assoc,
    q4, ← assoc, q4, assoc,
    e.hom_inv_id, comp_id, id_comp]
  rw [← cancel_mono $ p4 U, assoc,
    q4, ← assoc, q4, assoc,
    e.inv_hom_id, comp_id, id_comp]
end

theorem restrictIdeal_comap (f : X ⟶ Y) (J : ISD Y) (U : Opn Y) :
    restrictIdeal (comap J f) ((Opens.map f.base).obj U) =
      comap (restrictIdeal J U) (f.resLE U ((Opens.map f.base).obj U) le_rfl) := by
  rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
    ← comap_comp, q4]
end

section
variable {k : Type} [Field k] {X Y : Sch} (q : Y ⟶ Sp k) (e : X ≅ Y)
section
variable {U} {m} (c : EtaleChart q U m)
theorem etale_resLE_comp_map_of_iso :
    Etale
      (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map) := by
  have := isIso_resLE_iso_hom e U
  have : Etale $ e.hom.resLE U ((m54 $ ihB_ e).obj U) le_rfl :=
    inferInstance
  have := c.isEtale
  infer_instance

def EtaleChart.ofIso : EtaleChart (e.hom ≫ q) ((Opens.map e.hom.base).obj U) m where
  map := e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl ≫ c.map
  comp_struct := by
    rw [assoc, c.comp_struct, ← assoc, Scheme.Hom.resLE_comp_ι, assoc]
  isEtale := etale_resLE_comp_map_of_iso q e c

theorem EtaleChart.ofIso_coordIdeal (S : FinSet m) :
    (EtaleChart.ofIso q e c).coordIdeal S =
      comap (c.coordIdeal S) (e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl) := by
  rw [p33, p33]
  show comap (coordSubspaceIdeal k m S)
      (e.hom.resLE U ((m54 $ ihB_ e).obj U) le_rfl ≫ c.map) = _
  rw [comap_comp]
end

theorem hasStrictNormalCrossingsWith_comap_iso (Z : ISD Y)
    (F : Bdy Y) (h : HasStrictNormalCrossingsWith q Z F) :
    HasStrictNormalCrossingsWith (e.hom ≫ q) (comap Z e.hom) $ F.map fun D => comap D e.hom := by
  unfold HasStrictNormalCrossingsWith at h ⊢
  intro x hx
  have hx1 := (mem_orderAtLeastLocus_one_iff _ _).2 hx
  rw [orderAtLeastLocus_comap_iso_hom_eq_preimage e Z 1] at hx1
  obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := h (ihB_ e x) $ (mem_orderAtLeastLocus_one_iff _ _).1 hx1
  refine ⟨(m54 $ ihB_ e).obj U, hU, m, EtaleChart.ofIso q e c, a, S, ?_, ?_, ?_, ?_⟩
  simpa using h1
  intro i hi hai
  have hi' := by simpa using hi
  have hmap : (m39 (·.comap e.hom) F)[i] = cmI (F[i]'hi') e.hom := by
    simp
  rw [hmap, restrictIdeal_comap, h2 i hi' hai]
  exact comap_top _
  intro i hi t hai
  have hi' := by simpa using hi
  have hmap : (m39 (·.comap e.hom) F)[i] = cmI (F[i]'hi') e.hom := by
    simp
  rw [hmap, restrictIdeal_comap, h3 i hi' t hai, EtaleChart.ofIso_coordIdeal]
  rw [restrictIdeal_comap, h4, EtaleChart.ofIso_coordIdeal]
end

theorem exists_isIso_subschemeio_eq_comp_of_eq_ker {A X : Sch} (g : A ⟶ X)
    [IsClosedImmersion g] (I : ISD X) (hI : I = g.ker) :
    ∃ ph_ : subscheme I ⟶ A, IsIso ph_ ∧ subschemeι I = ph_ ≫ g := by
  subst hI
  have : Mono g := inferInstance
  have : Mono (m149 g).si := inferInstance
  let _a2 := ker (m149 g).si
  have h1 : m149 g ≤ _a2 :=
    le_of_eq (q2 _).symm
  have h2 : _a2 ≤ m149 g :=
    le_of_eq $ q2 _
  have hph : m64 g (m149 g).si h1 ≫ g
      = siI (m149 g) := by simp
  have hps_ : m64 (m149 g).si g h2
      ≫ siI (m149 g) = g := by simp
  refine ⟨m64 g (m149 g).si h1,
    ⟨⟨m64 (m149 g).si g h2, ?_, ?_⟩⟩, sy_ hph⟩
  rw [← cancel_mono (m149 g).si, assoc, hps_, hph, id_comp]
  rw [← cancel_mono g, assoc, hph, hps_, id_comp]

theorem strictTransform_comp_iso_hom {X X1 Y : Sch} (pi_ : X1 ⟶ X) (e : X ≅ Y)
    (Z D : ISD Y) :
    strictTransform (pi_ ≫ e.hom) Z D = strictTransform pi_ (comap Z e.hom) (comap D e.hom) := by
  let _a0 := pi_ ≫ isoH e
  have hZ : comap Z _a0 = comap (comap Z e.hom) pi_ := by
    rw [comap_comp]
  have hD : comap D _a0 = comap (comap D e.hom) pi_ := by
    rw [comap_comp]
  rw [strictTransform_eq_ker, strictTransform_eq_ker, strictTransformImmersion_eq,
    strictTransformImmersion_eq, strictTransformOpens_eq, strictTransformOpens_eq, hZ, hD]

theorem smooth_comap_iso {k : Type} [Field k] {X Y : Sch}
    (q : Y ⟶ Sp k) (e : X ≅ Y) (Z : ISD Y)
    (h : Smooth $ subschemeι Z ≫ q) :
    Smooth $ subschemeι (comap Z e.hom) ≫ e.hom ≫ q := by
  obtain ⟨ph_, hph, hcomm⟩ :=
    exists_isIso_subschemeio_eq_comp_of_eq_ker (m57 e.hom Z.si)
      (cmI Z e.hom) rfl
  let _a0 := ph_ ≫ m47 e.hom Z.si
  have hc2 : subschemeι (comap Z e.hom) ≫ isoH e =
      _a0 ≫ subschemeι Z := by
    rw [hcomm, assoc, assoc, condition]
  rw [← assoc, hc2, assoc]
  have : IsIso _a0 := inferInstance
  infer_instance

theorem comapIsoInvariance : ComapIsoInvariance where
  coSupport_comap := fun e J n => orderAtLeastLocus_comap_iso_hom_eq_preimage e J n
  hasSNCWith_comap := fun q e Z F h => hasStrictNormalCrossingsWith_comap_iso q e Z F h
  smooth_comap := fun q e Z h => smooth_comap_iso q e Z h
  strictTransform_comap := fun pi_ e Z D => strictTransform_comp_iso_hom pi_ e Z D





open Classical in
noncomputable def residualByPow {Y : Sch} (A F : ISD Y) (m : ℕ) : ISD Y :=
  if h : ∃ B : ISD Y, F ^ m * B = A then h.choose else ⊤

theorem pow_mul_residualByPow {Y : Sch} (A F : ISD Y) (m : ℕ)
    (h : ∃ B : ISD Y, F ^ m * B = A) : F ^ m * residualByPow A F m = A := by
  have hx : residualByPow A F m = h.choose := dif_pos h
  rw [hx]
  exact h.choose_spec

theorem map_comap_id_list_idealSheafData {X : Sch} (E : Bdy X) :
    E.map (fun D => comap D $ 𝟙 X) = E :=by simp_all
@[simp]
theorem exceptionalIdeal_id {X : Sch} (Z : ISD X) :
    exceptionalIdeal (𝟙 X) Z = Z := by
  rw [p9, comap_id]

def singleBlowupScheme {X : Sch} (Z : ISD X) : ℕ → Sch
  | 0 => X
  | (_ + 1) => Blowup.blowup Z

def singleBlowupMap {X : Sch} (Z : ISD X) :
    ∀ i : ℕ, singleBlowupScheme Z (i + 1) ⟶ singleBlowupScheme Z i
  | 0 => Blowup.blowup.proj Z
  | (_ + 1) => 𝟙 $ Blowup.blowup Z

def singleBlowupCenter {X : Sch} (Z : ISD X) :
    ∀ i : ℕ, IdealSheafData $ singleBlowupScheme Z i
  | 0 => Z
  | (_ + 1) => ⊤

def singleBlowupProj {X : Sch} (Z : ISD X) : ∀ i : ℕ, singleBlowupScheme Z i ⟶ X
  | 0 => 𝟙 X
  | (_ + 1) => Blowup.blowup.proj Z

def singleBlowupResidualIdeal {X : Sch} (I Z : ISD X) (m : ℕ) :
    ∀ i : ℕ, IdealSheafData $ singleBlowupScheme Z i
  | 0 => comap I $ 𝟙 X
  | (_ + 1) => residualByPow (comap I $ Blowup.blowup.proj Z) (comap Z $ Blowup.blowup.proj Z) m

def singleBlowupBoundary {X : Sch} (Z : ISD X) (E : Bdy X) :
    ∀ i : ℕ, List (singleBlowupScheme Z i).IdealSheafData
  | 0 => E.map fun D => comap D $ 𝟙 X
  | (_ + 1) =>
      E.map (strictTransform (Blowup.blowup.proj Z) Z) ++ [exceptionalIdeal (Blowup.blowup.proj Z) Z]

section
variable {X : Sch}
section
variable (Z : ISD X)
theorem isBlowupAlongIdealSheaf_singleBlowupMap (i : ℕ) (hi : i < 1) :
    Blowup.IsBlowupAlongIdealSheaf (singleBlowupMap Z i) $ singleBlowupCenter Z i := by
  obtain rfl : i = 0 := mp_ lt_one_iff hi
  exact Blowup.blowup.isBlowupAlongIdealSheaf_proj Z

theorem singleBlowupProj_succ (i : ℕ) :
    singleBlowupProj Z (i + 1) = singleBlowupMap Z i ≫ singleBlowupProj Z i := by
  cases i with
  | zero =>
      exact sy_ $ comp_id _
  | succ j =>
      exact sy_ $ id_comp _

theorem singleBlowupBoundary_succ
    (E : Bdy X) :
    ∀ i : ℕ, i < 1 →
      singleBlowupBoundary Z E (i + 1) =
        (singleBlowupBoundary Z E i).map (strictTransform (singleBlowupMap Z i) $ singleBlowupCenter Z i) ++
          [exceptionalIdeal (singleBlowupMap Z i) $ singleBlowupCenter Z i] := by
  intro i hi
  obtain rfl : i = 0 := mp_ lt_one_iff hi
  let _a0 := p6 (Blowup.blowup.proj Z) Z
  show E.map _a0 ++ [p5 (Blowup.blowup.proj Z) Z] =
      (E.map (cmI · $ 𝟙 X)).map _a0 ++
        [p5 (Blowup.blowup.proj Z) Z]
  rw [map_comap_id_list_idealSheafData E]

def singleBlowupSequenceData : BlowupSequenceData X where
  length := 1
  obj := singleBlowupScheme Z
  map := singleBlowupMap Z
  isoZero := refl X
  center := singleBlowupCenter Z
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_singleBlowupMap Z i hi
end

section
variable (I Z : ISD X) (m : ℕ)
theorem singleBlowupCenter_support_subset_orderAtLeastLocus
    (hord : (support Z : Set ↥X) ⊆ orderAtLeastLocus I m) :
    ∀ i : ℕ, i < 1 →
      (support (singleBlowupCenter Z i) : Set ↥(singleBlowupScheme Z i)) ⊆ orderAtLeastLocus (singleBlowupResidualIdeal I Z m i) m := by
  intro i hi
  obtain rfl : i = 0 := mp_ lt_one_iff hi
  show Z.supp ⊆ orderAtLeastLocus (comap I $ 𝟙 X) m
  rwa [comap_id]

theorem exceptionalIdeal_pow_mul_singleBlowupResidualIdeal_succ
    (hdiv : ∃ B : IdealSheafData $ Blowup.blowup Z,
      (comap Z $ Blowup.blowup.proj Z) ^ m * B = comap I (Blowup.blowup.proj Z)) :
    ∀ i : ℕ, i < 1 →
      exceptionalIdeal (singleBlowupMap Z i) (singleBlowupCenter Z i) ^ m * singleBlowupResidualIdeal I Z m (i + 1) =
        comap (singleBlowupResidualIdeal I Z m i) (singleBlowupMap Z i) := by
  intro i hi
  obtain rfl : i = 0 := mp_ lt_one_iff hi
  show exceptionalIdeal (Blowup.blowup.proj Z) Z ^ m *
      residualByPow (comap I $ Blowup.blowup.proj Z) (comap Z $ Blowup.blowup.proj Z) m =
    comap (comap I $ 𝟙 X) (Blowup.blowup.proj Z)
  rw [exceptionalIdeal_eq_comap, comap_id]
  exact pow_mul_residualByPow _ _ _ hdiv
end
end

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} (Z : ISD X)
theorem smooth_singleBlowupCenter_of_smooth
    (hsm : Smooth $ subschemeι Z ≫ p) :
    ∀ i : ℕ, i < 1 →
      Smooth (subschemeι (singleBlowupCenter Z i) ≫ singleBlowupProj Z i ≫ p) := by
  intro i hi
  obtain rfl : i = 0 := mp_ lt_one_iff hi
  show Smooth $ siI Z ≫ 𝟙 X ≫ p
  rwa [id_comp]

theorem hasStrictNormalCrossingsWith_singleBlowupCenter (E : Bdy X)
    (hsnc : HasStrictNormalCrossingsWith p Z E) :
    ∀ i : ℕ, i < 1 →
      HasStrictNormalCrossingsWith (singleBlowupProj Z i ≫ p) (singleBlowupCenter Z i) (singleBlowupBoundary Z E i) := by
  intro i hi
  obtain rfl : i = 0 := mp_ lt_one_iff hi
  show HasStrictNormalCrossingsWith (𝟙 X ≫ p) Z (E.map (cmI · $ 𝟙 X))
  rwa [map_comap_id_list_idealSheafData E, id_comp]
end

namespace MarkedBlowupSequenceData

def ofSingleBlowup {k : Type} [Field k] {X : Sch}
    (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
    (E : Bdy X) (Z : ISD X)
    (hsm : Smooth $ subschemeι Z ≫ p)
    (hsnc : HasStrictNormalCrossingsWith p Z E)
    (hord : (support Z : Set ↥X) ⊆ orderAtLeastLocus I m)
    (hdiv : ∃ B : IdealSheafData $ Blowup.blowup Z,
      (comap Z $ Blowup.blowup.proj Z) ^ m * B = comap I (Blowup.blowup.proj Z)) :
    MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := singleBlowupSequenceData Z
  proj := singleBlowupProj Z
  proj_zero := rfl
  proj_succ := fun i => singleBlowupProj_succ Z i
  ideal := singleBlowupResidualIdeal I Z m
  boundary := singleBlowupBoundary Z E
  ideal_zero := rfl
  boundary_zero := rfl
  center_order := singleBlowupCenter_support_subset_orderAtLeastLocus I Z m hord
  center_smooth := smooth_singleBlowupCenter_of_smooth Z hsm
  center_snc := hasStrictNormalCrossingsWith_singleBlowupCenter Z E hsnc
  ideal_succ := exceptionalIdeal_pow_mul_singleBlowupResidualIdeal_succ I Z m hdiv
  boundary_succ := singleBlowupBoundary_succ Z E

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X} {Z : ISD X}
  (hsm : Smooth $ subschemeι Z ≫ p) (hsnc : HasStrictNormalCrossingsWith p Z E)
  (hord : (support Z : Set ↥X) ⊆ orderAtLeastLocus I m)
  (hdiv : ∃ B : IdealSheafData $ Blowup.blowup Z,
    (comap Z $ Blowup.blowup.proj Z) ^ m * B = comap I (Blowup.blowup.proj Z))

@[simp]
theorem ofSingleBlowup_length :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.length = 1 := rfl

@[simp]
theorem ofSingleBlowup_schemeAt_succ (i : ℕ) :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.obj (i + 1) = Blowup.blowup Z := rfl

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

noncomputable def BlowupSequenceData.controlledTransform {X : Sch} (d : BlowupSequenceData X)
    (I : ISD X) (m : ℕ) : ∀ i : ℕ, IdealSheafData $ d.obj i
  | 0 => comap I d.isoZero.hom
  | (i + 1) =>
      residualByPow (comap (d.controlledTransform I m i) $ d.map i)
        (exceptionalIdeal (d.map i) $ d.center i) m

noncomputable def BlowupSequenceData.boundaryFrom {X : Sch} (d : BlowupSequenceData X)
    (E : Bdy X) : ∀ i : ℕ, List (d.obj i).IdealSheafData
  | 0 => E.map fun D => comap D d.isoZero.hom
  | (i + 1) =>
      (d.boundaryFrom E i).map (strictTransform (d.map i) $ d.center i) ++
        [exceptionalIdeal (d.map i) $ d.center i]

section
variable {X : Sch} (d : BlowupSequenceData X)
section
variable (I : ISD X) (m : ℕ)
@[simp]
theorem BlowupSequenceData.controlledTransform_zero :
    d.controlledTransform I m 0 = comap I d.isoZero.hom := rfl

@[simp]
theorem BlowupSequenceData.controlledTransform_succ (i : ℕ) :
    d.controlledTransform I m (i + 1) =
      residualByPow (comap (d.controlledTransform I m i) $ d.map i)
        (exceptionalIdeal (d.map i) $ d.center i) m := rfl

theorem BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ (i : ℕ)
    (h : ∃ B : IdealSheafData $ d.obj $ i + 1,
      exceptionalIdeal (d.map i) (d.center i) ^ m * B =
        comap (d.controlledTransform I m i) (d.map i)) :
    exceptionalIdeal (d.map i) (d.center i) ^ m * d.controlledTransform I m (i + 1) =
      comap (d.controlledTransform I m i) (d.map i) := by
  rw [d.controlledTransform_succ I m i]
  exact pow_mul_residualByPow _ _ m h
end

section
variable (E : Bdy X)
@[simp]
theorem BlowupSequenceData.boundary_zero :
    d.boundaryFrom E 0 = E.map fun D => comap D d.isoZero.hom := rfl

@[simp]
theorem BlowupSequenceData.boundary_succ (i : ℕ) :
    d.boundaryFrom E (i + 1) =
      (d.boundaryFrom E i).map (strictTransform (d.map i) $ d.center i) ++
        [exceptionalIdeal (d.map i) $ d.center i] := rfl

theorem BlowupSequenceData.boundary_length (i : ℕ) :
    (d.boundaryFrom E i).length = E.length + i := by
  induction i with
  | zero =>
      rw [d.boundary_zero E, length_map]
      omega
  | succ j ih =>
      rw [d.boundary_succ E j, length_append, length_map, ih,
        length_cons, length_nil]
      omega
end
end

structure BlowupSequenceData.IsMarked {k : Type} [Field k] {X : Sch} (d : BlowupSequenceData X)
    (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
    (E : Bdy X) : Prop where
  divisible : ∀ i < length d, ∃ B : IdealSheafData $ d.obj $ i + 1,
    exceptionalIdeal (d.map i) (d.center i) ^ m * B =
      comap (d.controlledTransform I m i) (d.map i)
  center_order : ∀ i < length d,
    (support (d.center i) : CSet $ d.obj i) ⊆ orderAtLeastLocus (d.controlledTransform I m i) m
  center_smooth : ∀ i < length d,
    Smooth $ subschemeι (d.center i) ≫ projectionToBase d i ≫ p
  center_snc : ∀ i < length d,
    HasStrictNormalCrossingsWith (projectionToBase d i ≫ p) (d.center i) $ d.boundaryFrom E i

noncomputable def BlowupSequenceData.toMarkedBlowupSequenceData {k : Type} [Field k] {X : Sch}
    (d : BlowupSequenceData X) (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
    (E : Bdy X) (h : d.IsMarked p I m E) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := d
  proj := projectionToBase d
  proj_zero := d.projectionToBase_zero
  proj_succ := d.projectionToBase_succ
  ideal := d.controlledTransform I m
  boundary := d.boundaryFrom E
  ideal_zero := rfl
  boundary_zero := rfl
  center_order := h.center_order
  center_smooth := h.center_smooth
  center_snc := h.center_snc
  ideal_succ := fun i hi => d.pow_exceptionalIdeal_mul_controlledTransform_succ I m i $ h.divisible i hi
  boundary_succ := fun i _ => d.boundary_succ E i

section

variable {k : Type} [Field k] {X : Sch} (d : BlowupSequenceData X)
  (p : X ⟶ Sp k) (I : ISD X) (m : ℕ)
  (E : Bdy X) (h : d.IsMarked p I m E)

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_toBlowupSequenceData :
    (d.toMarkedBlowupSequenceData p I m E h).toBlowupSequenceData = d := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_length :
    (d.toMarkedBlowupSequenceData p I m E h).length = d.length := rfl


section
variable (i : ℕ)
@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_center :
    (d.toMarkedBlowupSequenceData p I m E h).center i = d.center i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_blowupMorphism :
    (d.toMarkedBlowupSequenceData p I m E h).map i = d.map i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_projectionToBase :
    (d.toMarkedBlowupSequenceData p I m E h).proj i = projectionToBase d i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_ideal :
    (d.toMarkedBlowupSequenceData p I m E h).ideal i = d.controlledTransform I m i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_boundary :
    (d.toMarkedBlowupSequenceData p I m E h).boundary i = d.boundaryFrom E i := rfl
end

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups :
    (d.toMarkedBlowupSequenceData p I m E h).toMarkedSequenceOfBlowups.toSequenceOfBlowups = toSequenceOfBlowups d :=
  MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups _

end

theorem isLocallyGeneratedByNonZeroDivisor_pow {Y : Sch} {F : ISD Y}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (m : ℕ) : Blowup.IsLocallyGeneratedByNonZeroDivisor $ F ^ m := by
  intro x
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  refine ⟨U, f ^ m, hxU, pow_mem hf m, ?_⟩
  rw [ideal_pow]
  dsimp
  rw [hFU, span_singleton_pow]

theorem le_of_span_singleton_mul_eq_mul {R : Type} [CommRing R] {f : R}
    (hf : f ∈ nonZeroDivisors R) {I J : Ideal R}
    (h : span ({f} : Set R) * I = span ({f} : Set R) * J) : I ≤ J := by
  intro a ha
  have h1 : f * a ∈ span ({f} : Set R) * J := by
    rw [← h]
    exact mul_mem_mul (mem_span_singleton_self f) ha
  obtain ⟨z, hz, hfz⟩ := mp_ mem_span_singleton_mul h1
  rwa [sy_ $ mp_ (mul_cancel_left_mem_nonZeroDivisors hf) hfz]

section
variable {Y : Sch} {F A B : ISD Y} (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F)
include hF
theorem stalkIdeal_eq_of_mul_eq_mul (h : F * A = F * B) (x : ↥Y) :
    stalkIdeal A x = stalkIdeal B x := by
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  let _a0 := (U : Opn Y)
  let _ :=
    algebra_section_stalk Y.presheaf (⟨x, hxU⟩ : ↥_a0)
  have :=
    isLocalization_stalk U.2 (⟨x, hxU⟩ : ↥_a0)
  have hmul : stalkIdeal F x * stalkIdeal A x = stalkIdeal F x * stalkIdeal B x := by
    rw [← stalkIdeal_mul, ← stalkIdeal_mul, h]
  rw [stalkIdeal_eq_map_germ F x U hxU, hFU, map_span, image_singleton] at hmul
  let hf := map_nonZeroDivisors_le (primeIdealOf U.2 (⟨x, hxU⟩ : ↥_a0)).asIdeal.primeCompl ↑(stkX Y x) ⟨f, hf, rfl⟩
  let h := hmul
  exact le_antisymm (le_of_span_singleton_mul_eq_mul hf h) $ le_of_span_singleton_mul_eq_mul hf h.symm

theorem eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul (m : ℕ) (h : F ^ m * A = F ^ m * B) : A = B :=
  by
  apply m29
  funext V
  apply eq_of_localization_maximal
  intro P hP
  have : P.IsPrime := hP.isPrime
  have hx : fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _) ∈ (V : Opn Y) := by
    have hr : fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _) ∈
        range (fromSpec V.2) := mem_range_self _
    rwa [range_fromSpec V.2] at hr
  let _ :=
    algebra_section_stalk Y.presheaf
      (⟨fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _), hx⟩ : ↥(V : Opn Y))
  have : IsLocalization P.primeCompl
      ↑(stkX Y $ fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _)) :=
    isLocalization_stalk' V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _) hx
  have key := stalkIdeal_eq_of_mul_eq_mul (isLocallyGeneratedByNonZeroDivisor_pow hF m) h $ fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _)
  rw [stalkIdeal_eq_map_germ A _ V hx, stalkIdeal_eq_map_germ B _ V hx] at key
  exact map_eq_map_of_map_eq_map P.primeCompl key
end

theorem isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal {X' X : Sch} {f : X' ⟶ X}
    {Z : ISD X} (h : Blowup.IsBlowupAlongIdealSheaf f Z) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor $ exceptionalIdeal f Z := by
  rw [p9]
  exact Blowup.IsBlowupAlongIdealSheaf.isLocallyGeneratedByNonZeroDivisor_comap h

theorem BlowupSequenceData.eq_of_pow_exceptionalIdeal_mul_eq_mul {X : Sch} (d : BlowupSequenceData X)
    {i : ℕ} (hi : i < length d) (m : ℕ) (A B : IdealSheafData $ d.obj $ i + 1)
    (h : exceptionalIdeal (d.map i) (d.center i) ^ m * A =
      exceptionalIdeal (d.map i) (d.center i) ^ m * B) : A = B :=
  eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul
    (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal $ d.isBlowup i hi) m h

namespace MarkedBlowupSequenceData

section
variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : ISD X} {m : ℕ} {E : Bdy X}
section
variable (s : MarkedBlowupSequenceData p I m E)
theorem projectionToBase_eq_toBlowupSequenceData_projectionToBase (i : ℕ) :
    s.proj i = s.toBlowupSequenceData.projectionToBase i := by
  induction i with
  | zero => rw [s.proj_zero, s.toBlowupSequenceData.projectionToBase_zero]
  | succ j ih => rw [s.proj_succ j, s.toBlowupSequenceData.projectionToBase_succ j, ih]

theorem controlledTransform_and_boundary_eq_of_cancel
    (huniq : ∀ i < s.length, ∀ A B : IdealSheafData $ s.obj $ i + 1,
      exceptionalIdeal (s.map i) (s.center i) ^ m * A = (s.ideal i).comap (s.map i) →
      exceptionalIdeal (s.map i) (s.center i) ^ m * B = (s.ideal i).comap (s.map i) →
      A = B)
    (i : ℕ) (hi : i ≤ s.length) :
    s.toBlowupSequenceData.controlledTransform I m i = s.ideal i ∧
      s.toBlowupSequenceData.boundaryFrom E i = s.boundary i := by
  revert hi
  induction i with
  | zero =>
      intro _
      constructor
      rw [BlowupSequenceData.controlledTransform_zero]
      exact s.ideal_zero.symm
      rw [BlowupSequenceData.boundary_zero]
      exact s.boundary_zero.symm
  | succ j ih =>
      intro hi
      have hj := hi
      obtain ⟨ih1, ih2⟩ := ih $ le_of_lt hj
      constructor
      rw [BlowupSequenceData.controlledTransform_succ, ih1]
      exact huniq j hj _ _ (pow_mul_residualByPow _ _ m ⟨s.ideal $ j + 1, s.ideal_succ j hj⟩) $ s.ideal_succ j hj
      rw [BlowupSequenceData.boundary_succ, ih2]
      exact sy_ $ s.boundary_succ j hj

section
variable (i) (hi : i ≤ s.length)
include hi
theorem controlledTransform_and_boundary_eq :
    s.toBlowupSequenceData.controlledTransform I m i = s.ideal i ∧
      s.toBlowupSequenceData.boundaryFrom E i = s.boundary i :=
  s.controlledTransform_and_boundary_eq_of_cancel
    (fun _j hj A B hA hB =>
      s.toBlowupSequenceData.eq_of_pow_exceptionalIdeal_mul_eq_mul hj m A B $ tr_ hA hB.symm)
    i hi

theorem toBlowupSequenceData_controlledTransform_eq :
    s.toBlowupSequenceData.controlledTransform I m i = s.ideal i :=
  (s.controlledTransform_and_boundary_eq i hi).1

theorem toBlowupSequenceData_boundary_eq_boundary_of_le :
    s.toBlowupSequenceData.boundaryFrom E i = s.boundary i :=
  (s.controlledTransform_and_boundary_eq i hi).2
end

theorem isMarked_toBlowupSequenceData :
    s.toBlowupSequenceData.IsMarked p I m E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  intro i hi
  refine ⟨s.ideal $ i + 1, ?_⟩
  rw [s.toBlowupSequenceData_controlledTransform_eq i $ le_of_lt hi]
  exact s.ideal_succ i hi
  intro i hi
  rw [s.toBlowupSequenceData_controlledTransform_eq i $ le_of_lt hi]
  exact s.center_order i hi
  intro i hi
  have h := s.center_smooth i hi
  rwa [s.projectionToBase_eq_toBlowupSequenceData_projectionToBase i] at h
  intro i hi
  have h := s.center_snc i hi
  rw [s.projectionToBase_eq_toBlowupSequenceData_projectionToBase i] at h
  rwa [s.toBlowupSequenceData_boundary_eq_boundary_of_le i $ le_of_lt hi]
end

section
variable (s : MarkedSequenceOfBlowups p I m E) (i) (hi : i ≤ s.toSequenceOfBlowups.length)
include hi
theorem ofMarkedSequence_controlledTransform :
    s.toBsd.controlledTransform I m i = s.ideal i :=
  (ofMarkedSequence s).toBlowupSequenceData_controlledTransform_eq i hi

theorem ofMarkedSequence_boundary :
    s.toBsd.boundaryFrom E i = s.boundary i :=
  (ofMarkedSequence s).toBlowupSequenceData_boundary_eq_boundary_of_le i hi
end
end

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution
end
section

open scoped Classical


namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

def prependSchemeAt {X : Sch} (d : BlowupSequenceData X) : ℕ → Sch
  | 0 => X
  | (n + 1) => d.obj n

def prependMap {X : Sch} (d : BlowupSequenceData X) :
    (i : ℕ) → d.prependSchemeAt (i + 1) ⟶ d.prependSchemeAt i
  | 0 => d.isoZero.hom
  | (n + 1) => d.map n

def prependCenter {X : Sch} (d : BlowupSequenceData X) (Z : ISD X) :
    (i : ℕ) → IdealSheafData (d.prependSchemeAt i)
  | 0 => Z
  | (n + 1) => d.center n

section
variable {X : Sch} (Z) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X)
include hZ
theorem isBlowupAlongIdealSheaf_prependMap (i : ℕ) (hi : i < length d + 1) :
    Blowup.IsBlowupAlongIdealSheaf (d.prependMap i) $ d.prependCenter Z i := by
  cases i with
  | zero =>
      have h := hZ.iso_hom_comp d.isoZero
      rwa [comp_id] at h
  | succ n =>
      exact d.isBlowup n $ by omega

def prepend : BlowupSequenceData X where
  length := length d + 1
  obj := d.prependSchemeAt
  map := d.prependMap
  isoZero := refl X
  center := d.prependCenter Z
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_prependMap Z hZ d i hi
end

section
variable {X : Sch} (Z) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X)
@[simp] theorem prepend_length : length (prepend Z hZ d) = length d + 1 := rfl
@[simp] theorem prepend_schemeAt_zero : (prepend Z hZ d).obj 0 = X := rfl
@[simp] theorem prepend_schemeAt_succ (n : ℕ) : (prepend Z hZ d).obj (n + 1) = d.obj n := rfl
@[simp] theorem prepend_blowupMorphism_zero : (prepend Z hZ d).map 0 = d.isoZero.hom := rfl
@[simp] theorem prepend_blowupMorphism_succ (n : ℕ) : (prepend Z hZ d).map (n + 1) = d.map n := rfl
@[simp] theorem prepend_isoObjZero : (prepend Z hZ d).isoZero = refl X := rfl
@[simp] theorem prepend_center_zero : center (prepend Z hZ d) 0 = Z := rfl
@[simp] theorem prepend_center_succ (n : ℕ) : center (prepend Z hZ d) (n + 1) = d.center n := rfl
end

def CentersContainNoComponent {S : Sch} (d : BlowupSequenceData S) : Prop :=
  ∀ i, i < length d → ∀ W ∈ irreducibleComponents ↥(d.obj i),
    ¬ W ⊆ (support (d.center i) : CSet $ d.obj i)

end BlowupSequenceData
abbrev MarkedSequenceOfBlowups.NoComp {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k} {I : IdealSheafData X} {m : ℕ} {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) := s.toBsd.CentersContainNoComponent

namespace DivisorReduction

section
variable (T : MarkedIdealWithBoundary) (j) (hj : j < T.boundary.length)
noncomputable def containedComponentsIdeal :
    tISD T :=
  if h : IsOpen {x : ↥(T.bget j hj).subscheme |
      connectedComponent x ⊆
        ⇑(T.bget j hj).si ⁻¹' orderAtLeastLocus T.ideal T.mult} then
    ker
      (@AlgebraicGeometry.Scheme.Opens.i (T.bget j hj).subscheme
          ⟨{x : ↥(T.bget j hj).subscheme |
              connectedComponent x ⊆
                ⇑(T.bget j hj).si ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
        subschemeι (T.bget j hj))
  else ⊤

theorem containedComponentsIdeal_eq_ker
    (h : IsOpen {x : ↥(T.bget j hj).subscheme |
      connectedComponent x ⊆
        ⇑(T.bget j hj).si ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj =
      ker
        (@AlgebraicGeometry.Scheme.Opens.i (T.bget j hj).subscheme
            ⟨{x : ↥(T.bget j hj).subscheme |
                connectedComponent x ⊆
                  ⇑(T.bget j hj).si ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
          subschemeι (T.bget j hj)) := dif_pos h

theorem containedComponentsIdeal_eq_top_of_not_isOpen
    (h : ¬ IsOpen {x : ↥(T.bget j hj).subscheme |
      connectedComponent x ⊆
        ⇑(T.bget j hj).si ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj = ⊤ := by
  exact dif_neg h

noncomputable def restrictToBoundaryDivisor
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData) : MarkedIdealWithBoundary :=
  T.withSchemeIdealBoundary (T.bget j hj).subscheme
    (subschemeι (T.bget j hj) ≫ structMap T)
    (comap I0 (T.bget j hj).si)
    (((eraseIdx E0 j).take $ T.boundary.length - 1).map
      (fun D => comap D (T.bget j hj).si))
end

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) (alg : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ)
section
variable (hj : j < T.boundary.length) (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData) (pre : BlowupSequenceData T.scheme → BlowupSequenceData T.scheme)
noncomputable def liftSeqFromDivisor : T.SequenceOfBlowups :=
  if hdn : (restrictToBoundaryDivisor T j hj I0 E0).krullDimSucc < T.krullDimSucc ∧
      IsNoetherian T.scheme then
    letI := hdn.2
    if hpr : (ofMarkedSequence
        (alg (restrictToBoundaryDivisor T j hj I0 E0) hdn.1)).toBlowupSequenceData.CentersContainNoComponent then
      if hmk : (pre $ ambientBlowupSequence (T.bget j hj).si
          (ofMarkedSequence $ alg (restrictToBoundaryDivisor T j hj I0 E0) hdn.1).toBlowupSequenceData
          hres hno hpr).IsMarked T.structMap T.ideal T.mult T.boundary then
        ((pre $ ambientBlowupSequence (T.bget j hj).si
            (ofMarkedSequence $ alg (restrictToBoundaryDivisor T j hj I0 E0) hdn.1).toBlowupSequenceData
            hres hno hpr).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups
      else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
    else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

end

noncomputable def divisorReductionSeq : T.SequenceOfBlowups :=
  if hj : j < T.boundary.length then
    if orderAtLeastLocus T.ideal T.mult = (∅ : CSet T.scheme) then
      emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
    else
      if containedComponentsIdeal T j hj = ⊤ then
        liftSeqFromDivisor hres hno T alg j hj (T.ideal.comap $ 𝟙 T.scheme)
          (T.boundary.map fun D => comap D $ 𝟙 T.scheme) id
      else
        if hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ containedComponentsIdeal T j hj then
          liftSeqFromDivisor hres hno T alg j hj
            (residualByPow (comap (T.ideal.comap $ 𝟙 T.scheme) $ 𝟙 T.scheme)
              (exceptionalIdeal (𝟙 T.scheme) $ containedComponentsIdeal T j hj) T.mult)
            ((T.boundary.map fun D => comap D $ 𝟙 T.scheme).map
                (strictTransform (𝟙 T.scheme) $ containedComponentsIdeal T j hj) ++
              [exceptionalIdeal (𝟙 T.scheme) $ containedComponentsIdeal T j hj])
            (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb)
        else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

section
variable (hj : j < T.boundary.length)
include hj
theorem divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty (hcs : orderAtLeastLocus T.ideal T.mult = (∅ : CSet T.scheme)) :
    divisorReductionSeq hres hno T alg j = emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_pos hcs]

section
variable (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : CSet T.scheme))
include hcs
theorem divisorReductionSeq_eq_liftSeqFromDivisor_of_eq_top
    (hZ : containedComponentsIdeal T j hj = ⊤) :
    divisorReductionSeq hres hno T alg j =
      liftSeqFromDivisor hres hno T alg j hj (T.ideal.comap $ 𝟙 T.scheme)
        (T.boundary.map fun D => comap D $ 𝟙 T.scheme) id := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_neg hcs, if_pos hZ]

theorem divisorReductionSeq_eq_liftSeqFromDivisor_prepend
    (hZ : containedComponentsIdeal T j hj ≠ ⊤) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ containedComponentsIdeal T j hj) :
    divisorReductionSeq hres hno T alg j =
      liftSeqFromDivisor hres hno T alg j hj
        (residualByPow (comap (T.ideal.comap $ 𝟙 T.scheme) $ 𝟙 T.scheme)
          (exceptionalIdeal (𝟙 T.scheme) $ containedComponentsIdeal T j hj) T.mult)
        ((T.boundary.map fun D => comap D $ 𝟙 T.scheme).map
            (strictTransform (𝟙 T.scheme) $ containedComponentsIdeal T j hj) ++
          [exceptionalIdeal (𝟙 T.scheme) $ containedComponentsIdeal T j hj])
        (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb) := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_neg hcs, if_neg hZ, dif_pos hb]
end
end
end

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end
section

open scoped Classical


namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

section
variable (T : MarkedIdealWithBoundary)
noncomputable abbrev lowerIdealWithoutBlowup : T.scheme.IdealSheafData :=
  T.ideal.comap $ 𝟙 T.scheme

noncomputable abbrev lowerBoundaryWithoutBlowup : List T.scheme.IdealSheafData :=
  T.boundary.map fun D => comap D $ 𝟙 T.scheme

section
variable (j) (hj : j < T.boundary.length)
noncomputable abbrev lowerIdealAfterBlowup :
    T.scheme.IdealSheafData :=
  residualByPow (comap (T.ideal.comap $ 𝟙 T.scheme) $ 𝟙 T.scheme)
    (exceptionalIdeal (𝟙 T.scheme) $ containedComponentsIdeal T j hj) T.mult

noncomputable abbrev lowerBoundaryAfterBlowup :
    List T.scheme.IdealSheafData :=
  (T.boundary.map fun D => comap D $ 𝟙 T.scheme).map
      (strictTransform (𝟙 T.scheme) $ containedComponentsIdeal T j hj) ++
    [exceptionalIdeal (𝟙 T.scheme) $ containedComponentsIdeal T j hj]

section
variable {T} {j}
noncomputable abbrev ccI := containedComponentsIdeal T j hj
noncomputable abbrev lI := lowerIdealAfterBlowup T j hj
noncomputable abbrev lB := lowerBoundaryAfterBlowup T j hj
noncomputable abbrev rBD := restrictToBoundaryDivisor T j hj (lowerIdealAfterBlowup T j hj) $ lowerBoundaryAfterBlowup T j hj
end

theorem containedComponentsIdeal_eq_ker_io_comp_subschemeio_of_isOpen
    (h : IsOpen {x : ↥(T.bget j hj).subscheme |
      connectedComponent x ⊆
        ⇑(T.bget j hj).si ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    ccI hj =
      ker
        (@AlgebraicGeometry.Scheme.Opens.i (T.bget j hj).subscheme
            ⟨{x : ↥(T.bget j hj).subscheme |
                connectedComponent x ⊆
                  ⇑(T.bget j hj).si ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
          subschemeι (T.bget j hj)) :=
  containedComponentsIdeal_eq_ker T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent
    (h : ¬ IsOpen {x : ↥(T.bget j hj).subscheme |
      connectedComponent x ⊆
        ⇑(T.bget j hj).si ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    ccI hj = ⊤ :=
  containedComponentsIdeal_eq_top_of_not_isOpen T j hj h
end

@[simp]
theorem lowerBoundaryWithoutBlowup_eq : lowerBoundaryWithoutBlowup T = boundary T := by
  simp [lowerBoundaryWithoutBlowup]
end

section
variable (hres : StrictTransformIsBlowupOfClosedSubscheme) (hno : BlowupPreservesNoetherian) (T : MarkedIdealWithBoundary) (alg : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j) (hj : j < T.boundary.length)
noncomputable def ambientTowerOfLowerResolution
    (I0 : T.scheme.IdealSheafData) (E0 : List T.scheme.IdealSheafData)
    (hdn : (restrictToBoundaryDivisor T j hj I0 E0).krullDimSucc < T.krullDimSucc ∧ IsNoetherian T.scheme)
    (hpr : (ofMarkedSequence
      (alg (restrictToBoundaryDivisor T j hj I0 E0) hdn.1)).toBlowupSequenceData.CentersContainNoComponent) :
    BlowupSequenceData T.scheme :=
  letI := hdn.2
  ambientBlowupSequence (T.bget j hj).si
    (ofMarkedSequence $ alg (restrictToBoundaryDivisor T j hj I0 E0) hdn.1).toBlowupSequenceData
    hres hno hpr

section
variable (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : CSet T.scheme))
include hcs
theorem divisorReductionSeq_eq_of_isBlowupAlongIdealSheaf
    (hZ : ccI hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) $ ccI hj)
    (hdn : (rBD hj).krullDimSucc < T.krullDimSucc ∧
      IsNoetherian T.scheme)
    (hpr : (ofMarkedSequence
      (alg (rBD hj)
        hdn.1)).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (ccI hj) hb
        (ambientTowerOfLowerResolution hres hno T alg j hj (lI hj) (lB hj)
          hdn hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    divisorReductionSeq hres hno T alg j =
      ((BlowupSequenceData.prepend (ccI hj) hb
          (ambientTowerOfLowerResolution hres hno T alg j hj (lI hj) (lB hj)
            hdn hpr)).toMarkedBlowupSequenceData
        T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups := by
  have := an2 hdn
  refine tr_ (divisorReductionSeq_eq_liftSeqFromDivisor_prepend hres hno T alg j hj hcs hZ hb) ?_
  exact tr_ (dif_pos ⟨an1 hdn, inferInstance⟩) $ tr_ (dif_pos hpr) $ dif_pos hmk

theorem divisorReductionSeq_eq_of_containedComponentsIdeal_eq_top
    (hZ : ccI hj = ⊤)
    (hdn : (restrictToBoundaryDivisor T j hj (lowerIdealWithoutBlowup T) $ lowerBoundaryWithoutBlowup T).krullDimSucc < T.krullDimSucc ∧
      IsNoetherian T.scheme)
    (hpr : (ofMarkedSequence $ alg (restrictToBoundaryDivisor T j hj (lowerIdealWithoutBlowup T)
      (lowerBoundaryWithoutBlowup T)) hdn.1).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) hdn hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    divisorReductionSeq hres hno T alg j =
      ((ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) hdn hpr).toMarkedBlowupSequenceData
        T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups := by
  have := an2 hdn
  refine tr_ (divisorReductionSeq_eq_liftSeqFromDivisor_of_eq_top hres hno T alg j hj hcs hZ) ?_
  exact tr_ (dif_pos ⟨an1 hdn, inferInstance⟩) $ tr_ (dif_pos hpr) $ dif_pos hmk
end
end

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end
section


namespace FunctorialResolution.EmbeddedResolution

section
variable {X Y : Sch} (e : X ≅ Y) (U : Opn Y)
theorem isIso_resLE_of_iso :
    IsIso $ e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl := by
  rw [resLE_eq_morphismRestrict]
  infer_instance

def preimageOpensIso :
    Scheme.Opens.toScheme ((Opens.map e.hom.base).obj U) ≅ Scheme.Opens.toScheme U :=
  letI := isIso_resLE_of_iso e U
  asIso $ e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl

@[simp]
theorem preimageOpensIso_hom :
    (preimageOpensIso e U).hom = e.hom.resLE U ((Opens.map e.hom.base).obj U) le_rfl :=
  rfl
end

def OrderCertificateIsoInvariantOfMaxContact : Prop :=
  ∀ (k : Type) [Field k] (W : Sch) (p : W ⟶ Sp k)
      (N : ISD W) (mu_ : ℕ) (Mem : Set ↥W) (Z : ISD W)
      (U : ∀ z : ↥W, z ∈ support Z → Opn W)
      (_hU : ∀ (z : ↥W) (hz : z ∈ support Z), z ∈ U z hz)
      (H : ∀ (z : ↥W) (hz : z ∈ support Z), (U z hz).toScheme.IdealSheafData)
      (_hH : ∀ (z : ↥W) (hz : z ∈ support Z),
        IsSmoothDivisor (ι (U z hz) ≫ p) $ H z hz)
      (_hNsubH : ∀ (z : ↥W) (hz : z ∈ support Z),
        (support (comap N (U z hz).i) : Set ↥(U z hz).toScheme) ⊆
          (support (H z hz) : Set ↥(U z hz).toScheme))
      (_hZH : ∀ (z : ↥W) (hz : z ∈ support Z),
        (support (comap Z (U z hz).i) : Set ↥(U z hz).toScheme) ⊆
          (support (H z hz) : Set ↥(U z hz).toScheme))
      (J : ∀ (z : ↥W) (hz : z ∈ support Z), Option (H z hz).subscheme.IdealSheafData)
      (_hJnone : ∀ (z : ↥W) (hz : z ∈ support Z), J z hz = Option.none →
        IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
          (support (comap Z (U z hz).i) : Set ↥(U z hz).toScheme)))
      (_hJcomp : ∀ (z : ↥W) (hz : z ∈ support Z) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz → NonzeroOnComponents Jz)
      (_hJloc : ∀ (z : ↥W) (hz : z ∈ support Z) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz →
          ∀ x : ↥(H z hz).subscheme,
            (subschemeι (H z hz) ≫ ι (U z hz)).base x ∉ Mem →
              ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
                comap Jz V.i = (comap (comap N (U z hz).i) (H z hz).si).comap V.i)
      (_hJcert : ∀ (z : ↥W) (hz : z ∈ support Z) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz →
          PrincipalizationCertificate (H z hz).subscheme (subschemeι (H z hz) ≫ ι (U z hz) ≫ p) Jz mu_
            (⇑(subschemeι (H z hz) ≫ ι (U z hz)).base ⁻¹' Mem)
            (comap (comap Z (U z hz).i) (H z hz).si))
      (_hJtrans : ∀ (z : ↥W) (hz : z ∈ support Z) (Jz : (H z hz).subscheme.IdealSheafData),
        J z hz = Option.some Jz →
          ∀ (X : Sch) (f : X ≅ subscheme (H z hz)),
            PrincipalizationCertificate X (f.hom ≫ subschemeι (H z hz) ≫ ι (U z hz) ≫ p) (comap Jz f.hom) mu_
              (⇑f.hom.base ⁻¹' (⇑(subschemeι (H z hz) ≫ ι (U z hz)).base ⁻¹' Mem))
              ((comap (comap Z (U z hz).i) (H z hz).si).comap f.hom))
      (W' : Sch) (e : W' ≅ W),
    OrderCertificate W' (e.hom ≫ p) (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom

theorem coe_support_comap_iso_hom {X Y : Sch} (e : X ≅ Y) (Z : ISD Y) :
    (support (comap Z e.hom) : Set ↥X) = ⇑e.hom.base ⁻¹' (support Z : Set ↥Y) := by
  ext x
  simp

theorem preimage_comp_base {A B C : Sch} (f : A ⟶ B) (g : B ⟶ C) (S : Set ↥C) :
    ⇑f.base ⁻¹' (⇑g.base ⁻¹' S) = ⇑(f ≫ g).base ⁻¹' S := by
  ext x
  simp

theorem preimageOpensIso_hom_comp_io {X Y : Sch} (e : X ≅ Y) (U : Opn Y) :
    (preimageOpensIso e U).hom ≫ ι U = Scheme.Opens.i ((Opens.map e.hom.base).obj U) ≫ e.hom :=by simp_all
theorem preimageOpensIso_hom_comp_io_comp {k : Type} [Field k] {X Y : Sch}
    (q : Y ⟶ Sp k) (e : X ≅ Y) (U : Opn Y) :
    (preimageOpensIso e U).hom ≫ (ι U ≫ q) =
      Scheme.Opens.i ((Opens.map e.hom.base).obj U) ≫ (e.hom ≫ q) :=by simp_all
section
variable {X Y : Sch} (e : X ≅ Y) (U : Opn Y)
theorem comap_preimageOpensIso_hom (I : ISD Y) :
    comap (comap I U.i) (preimageOpensIso e U).hom =
      comap (comap I e.hom) (Scheme.Opens.i $ (Opens.map e.hom.base).obj U) := by
  rw [← comap_comp, ← comap_comp, preimageOpensIso_hom_comp_io]

theorem preimage_preimageOpensIso_hom (Mem : Set ↥Y) :
    ⇑(preimageOpensIso e U).hom.base ⁻¹' (⇑U.ib ⁻¹' Mem) =
      ⇑(Scheme.Opens.i $ (Opens.map e.hom.base).obj U).base ⁻¹' (⇑e.hom.base ⁻¹' Mem) := by
  rw [preimage_comp_base, preimage_comp_base, preimageOpensIso_hom_comp_io]
end

section
variable {k : Type} [Field k]
section
variable {W : Sch} {p p' : W ⟶ Sp k}
private theorem principalizationCertificate_congr {I I' : ISD W} {m : ℕ}
    {Mem Mem' : Set ↥W} {Z Z' : ISD W} (hp : p = p') (hI : I = I')
    (hMem : Mem = Mem') (hZ : Z = Z') (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p' I' m Mem' Z' :=by simp_all
private theorem orderCertificate_congr {N N' : ISD W} {mu_ : ℕ}
    {Mem Mem' : Set ↥W} {Z Z' : ISD W} (hp : p = p') (hN : N = N')
    (hMem : Mem = Mem') (hZ : Z = Z') (h : OrderCertificate W p N mu_ Mem Z) :
    OrderCertificate W p' N' mu_ Mem' Z' :=by simp_all
end

section
variable (W : Sch) (p : W ⟶ Sp k)
section
variable (I : ISD W) (m : ℕ) (Mem : Set ↥W) (Z : ISD W)
theorem principalizationCertificate_comap_iso_of_support_subset (h : (support Z : Set ↥W) ⊆ Mem) (W' : Sch) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (comap I e.hom) m (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom := by
  refine PrincipalizationCertificate.memory ?_
  rw [coe_support_comap_iso_hom e Z]
  exact preimage_mono h

theorem principalizationCertificate_comap_iso_of_two_le (hm : 2 ≤ m) (W' : Sch) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (comap I e.hom) m (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom :=
  PrincipalizationCertificate.large hm

theorem principalizationCertificate_comap_iso_of_orderCertificate (M N : ISD W) (mu_ : ℕ) (hI : I = M * N)
    (hM : (support M : Set ↥W) ⊆ Mem) (hmu : m ≤ mu_)
    (hZ : (support Z : Set ↥W) ⊆ orderAtLeastLocus N mu_) (_hcert : OrderCertificate W p N mu_ Mem Z)
    (ih : ∀ (W' : Sch) (e : W' ≅ W),
      OrderCertificate W' (e.hom ≫ p) (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom)
    (W' : Sch) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (comap I e.hom) m (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom := by
  refine PrincipalizationCertificate.toOrder (cmI M e.hom) (cmI N e.hom) mu_ ?_ ?_ hmu ?_ $ ih W' e
  rw [hI, comap_mul]
  rw [coe_support_comap_iso_hom e M]
  exact preimage_mono hM
  rw [coe_support_comap_iso_hom e Z, orderAtLeastLocus_comap_iso_hom_eq_preimage e N mu_]
  exact preimage_mono hZ

theorem principalizationCertificate_comap_iso_of_opens_cover (U : ∀ z : ↥W, z ∈ support Z → Opn W)
    (hU : ∀ z hz, z ∈ U z hz)
    (_hcert : ∀ z hz,
      PrincipalizationCertificate (U z hz).toScheme (ι (U z hz) ≫ p) (comap I (U z hz).i) m
        (⇑(U z hz).ib ⁻¹' Mem) $ comap Z (U z hz).i)
    (ih : ∀ z hz X (f : X ≅ toScheme (U z hz)),
      PrincipalizationCertificate X (f.hom ≫ (ι (U z hz) ≫ p)) (comap (comap I (U z hz).i) f.hom) m
        (⇑f.hom.base ⁻¹' (⇑(U z hz).ib ⁻¹' Mem)) $ comap (comap Z (U z hz).i) f.hom)
    (W' : Sch) (e : W' ≅ W) :
    PrincipalizationCertificate W' (e.hom ≫ p) (comap I e.hom) m (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom := by
  refine PrincipalizationCertificate.localize
    (fun z' hz' =>
      (m54 $ ihB_ e).obj
        (U (ihB_ e z') $ by rwa [mem_support_comap] at hz'))
    (fun z' hz' => ?_) ?_
  exact hU (ihB_ e z') $ by rwa [mem_support_comap] at hz'
  intro z' hz'
  have hz : ihB_ e z' ∈ spI Z := by
    rwa [mem_support_comap] at hz'
  let _m0 := U (ihB_ e z') hz
  exact principalizationCertificate_congr (preimageOpensIso_hom_comp_io_comp p e _m0)
    (comap_preimageOpensIso_hom e _m0 I)
    (preimage_preimageOpensIso_hom e _m0 Mem)
    (comap_preimageOpensIso_hom e _m0 Z)
    (ih (ihB_ e z') hz _ $ preimageOpensIso e _m0)
end

section
variable (N : ISD W) (mu_ : ℕ) (Mem : Set ↥W) (Z : ISD W)
theorem orderCertificate_comap_iso_of_support_subset (h : (support Z : Set ↥W) ⊆ Mem) (W' : Sch) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom := by
  refine OrderCertificate.memory ?_
  rw [coe_support_comap_iso_hom e Z]
  exact preimage_mono h

theorem orderCertificate_comap_iso_of_two_le (hmu : 2 ≤ mu_) (W' : Sch) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom :=
  OrderCertificate.large hmu

theorem orderCertificate_comap_iso_of_opens_cover (U : ∀ z : ↥W, z ∈ support Z → Opn W)
    (hU : ∀ z hz, z ∈ U z hz)
    (_hcert : ∀ z hz,
      OrderCertificate (U z hz).toScheme (ι (U z hz) ≫ p) (comap N (U z hz).i) mu_
        (⇑(U z hz).ib ⁻¹' Mem) $ comap Z (U z hz).i)
    (ih : ∀ z hz X (f : X ≅ toScheme (U z hz)),
      OrderCertificate X (f.hom ≫ (ι (U z hz) ≫ p)) (comap (comap N (U z hz).i) f.hom) mu_
        (⇑f.hom.base ⁻¹' (⇑(U z hz).ib ⁻¹' Mem)) $ comap (comap Z (U z hz).i) f.hom)
    (W' : Sch) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom := by
  refine OrderCertificate.localize
    (fun z' hz' =>
      (m54 $ ihB_ e).obj
        (U (ihB_ e z') $ by rwa [mem_support_comap] at hz'))
    (fun z' hz' => ?_) ?_
  exact hU (ihB_ e z') $ by rwa [mem_support_comap] at hz'
  intro z' hz'
  have hz : ihB_ e z' ∈ spI Z := by
    rwa [mem_support_comap] at hz'
  let _m0 := U (ihB_ e z') hz
  exact orderCertificate_congr (preimageOpensIso_hom_comp_io_comp p e _m0)
    (comap_preimageOpensIso_hom e _m0 N)
    (preimage_preimageOpensIso_hom e _m0 Mem)
    (comap_preimageOpensIso_hom e _m0 Z)
    (ih (ihB_ e z') hz _ $ preimageOpensIso e _m0)
end
end
end

section
variable (hT : OrderCertificateIsoInvariantOfMaxContact) {k : Type} [Field k]
include hT
section
variable (W : Sch) (p : W ⟶ Sp k)
theorem orderCertificate_comap_iso_of_smoothDivisor_cover (N : ISD W) (mu_ : ℕ) (Mem : Set ↥W)
    (Z : ISD W)
    (U : ∀ z : ↥W, z ∈ support Z → Opn W)
    (hU : ∀ z hz, z ∈ U z hz)
    (H : ∀ z hz, (U z hz).toScheme.IdealSheafData)
    (hH : ∀ z hz, IsSmoothDivisor (ι (U z hz) ≫ p) $ H z hz)
    (hNsubH : ∀ z hz,
      (support (comap N (U z hz).i) : Set ↥(U z hz).toScheme) ⊆
        (support (H z hz) : Set ↥(U z hz).toScheme))
    (hZH : ∀ z hz,
      (support (comap Z (U z hz).i) : Set ↥(U z hz).toScheme) ⊆
        (support (H z hz) : Set ↥(U z hz).toScheme))
    (J : ∀ z hz, Option (H z hz).subscheme.IdealSheafData)
    (hJnone : ∀ z hz, J z hz = Option.none →
      IsOpen (⇑(H z hz).subschemeι.base ⁻¹'
        (support (comap Z (U z hz).i) : Set ↥(U z hz).toScheme)))
    (hJcomp : ∀ z hz (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz → NonzeroOnComponents Jz)
    (hJloc : ∀ z hz (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz →
        ∀ x : ↥(H z hz).subscheme,
          (subschemeι (H z hz) ≫ ι (U z hz)).base x ∉ Mem →
            ∃ V : (H z hz).subscheme.Opens, x ∈ V ∧
              comap Jz V.i = (comap (comap N (U z hz).i) (H z hz).si).comap V.i)
    (hJcert : ∀ z hz (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz →
        PrincipalizationCertificate (H z hz).subscheme (subschemeι (H z hz) ≫ ι (U z hz) ≫ p) Jz mu_
          (⇑(subschemeι (H z hz) ≫ ι (U z hz)).base ⁻¹' Mem)
          (comap (comap Z (U z hz).i) (H z hz).si))
    (ih : ∀ z hz (Jz : (H z hz).subscheme.IdealSheafData),
      J z hz = Option.some Jz →
        ∀ X (f : X ≅ subscheme (H z hz)),
          PrincipalizationCertificate X (f.hom ≫ subschemeι (H z hz) ≫ ι (U z hz) ≫ p) (comap Jz f.hom) mu_
            (⇑f.hom.base ⁻¹' (⇑(subschemeι (H z hz) ≫ ι (U z hz)).base ⁻¹' Mem))
            ((comap (comap Z (U z hz).i) (H z hz).si).comap f.hom))
    (W' : Sch) (e : W' ≅ W) :
    OrderCertificate W' (e.hom ≫ p) (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom :=
  hT k W p N mu_ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ih W' e


end

section
variable {W W' : Sch} {p : W ⟶ Sp k}
theorem PrincipalizationCertificate.comap_iso {I : ISD W} {m : ℕ}
    {Mem : Set ↥W} {Z : ISD W} (e : W' ≅ W) (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W' (e.hom ≫ p) (comap I e.hom) m (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom :=
  (fun hT {k} [Field k] W p I m Mem Z h => @PrincipalizationCertificate.rec k _
    (fun W p I m Mem Z _ => ∀ W' (e : W' ≅ W),
      PrincipalizationCertificate W' (isoH e ≫ p) (cmI I e.hom) m (preimage e.hom.base Mem) $ cmI Z e.hom)
    (fun W p N mu_ Mem Z _ => ∀ W' (e : W' ≅ W),
      OrderCertificate W' (isoH e ≫ p) (cmI N e.hom) mu_ (preimage e.hom.base Mem) $ cmI Z e.hom)
    (fun {W p I m Mem Z} h => principalizationCertificate_comap_iso_of_support_subset W p I m Mem Z h)
    (fun {W p I m Mem Z} hm => principalizationCertificate_comap_iso_of_two_le W p I m Mem Z hm)
    (fun {W p I m Mem Z} M N mu_ hI hM hmu hZ hcert ihc =>
      principalizationCertificate_comap_iso_of_orderCertificate W p I m Mem Z M N mu_ hI hM hmu hZ hcert ihc)
    (fun {W p I m Mem Z} U hU hcert ihc =>
      principalizationCertificate_comap_iso_of_opens_cover W p I m Mem Z U hU hcert ihc)
    (fun {W p N mu_ Mem Z} h => orderCertificate_comap_iso_of_support_subset W p N mu_ Mem Z h)
    (fun {W p N mu_ Mem Z} hmu => orderCertificate_comap_iso_of_two_le W p N mu_ Mem Z hmu)
    (fun {W p N mu_ Mem Z} U hU hcert ihc =>
      orderCertificate_comap_iso_of_opens_cover W p N mu_ Mem Z U hU hcert ihc)
    (fun {W p N mu_ Mem Z} U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ihc =>
      orderCertificate_comap_iso_of_smoothDivisor_cover hT W p N mu_ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc
        hJcert ihc)
    W p I m Mem Z h) hT W p I m Mem Z h W' e

theorem OrderCertificate.comap_iso {N : ISD W} {mu_ : ℕ}
    {Mem : Set ↥W} {Z : ISD W} (e : W' ≅ W) (h : OrderCertificate W p N mu_ Mem Z) :
    OrderCertificate W' (e.hom ≫ p) (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom :=
  (fun hT {k} [Field k] W p N mu_ Mem Z h => @OrderCertificate.rec k _
    (fun W p I m Mem Z _ => ∀ W' (e : W' ≅ W),
      PrincipalizationCertificate W' (isoH e ≫ p) (cmI I e.hom) m (preimage e.hom.base Mem) $ cmI Z e.hom)
    (fun W p N mu_ Mem Z _ => ∀ W' (e : W' ≅ W),
      OrderCertificate W' (isoH e ≫ p) (cmI N e.hom) mu_ (preimage e.hom.base Mem) $ cmI Z e.hom)
    (fun {W p I m Mem Z} h => principalizationCertificate_comap_iso_of_support_subset W p I m Mem Z h)
    (fun {W p I m Mem Z} hm => principalizationCertificate_comap_iso_of_two_le W p I m Mem Z hm)
    (fun {W p I m Mem Z} M N mu_ hI hM hmu hZ hcert ihc =>
      principalizationCertificate_comap_iso_of_orderCertificate W p I m Mem Z M N mu_ hI hM hmu hZ hcert ihc)
    (fun {W p I m Mem Z} U hU hcert ihc =>
      principalizationCertificate_comap_iso_of_opens_cover W p I m Mem Z U hU hcert ihc)
    (fun {W p N mu_ Mem Z} h => orderCertificate_comap_iso_of_support_subset W p N mu_ Mem Z h)
    (fun {W p N mu_ Mem Z} hmu => orderCertificate_comap_iso_of_two_le W p N mu_ Mem Z hmu)
    (fun {W p N mu_ Mem Z} U hU hcert ihc =>
      orderCertificate_comap_iso_of_opens_cover W p N mu_ Mem Z U hU hcert ihc)
    (fun {W p N mu_ Mem Z} U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert ihc =>
      orderCertificate_comap_iso_of_smoothDivisor_cover hT W p N mu_ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc
        hJcert ihc)
    W p N mu_ Mem Z h) hT W p N mu_ Mem Z h W' e

section
variable {p' : W' ⟶ Sp k}
theorem PrincipalizationCertificate.comap_iso_of_eq {I : ISD W} {m : ℕ}
    {Mem : Set ↥W} {Z : ISD W} (e : W' ≅ W) (hp : p' = e.hom ≫ p)
    (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W' p' (comap I e.hom) m (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom := by
  subst hp
  exact PrincipalizationCertificate.comap_iso hT e h

theorem OrderCertificate.comap_iso_of_eq {N : ISD W} {mu_ : ℕ}
    {Mem : Set ↥W} {Z : ISD W} (e : W' ≅ W) (hp : p' = e.hom ≫ p)
    (h : OrderCertificate W p N mu_ Mem Z) :
    OrderCertificate W' p' (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom := by
  subst hp
  exact OrderCertificate.comap_iso hT e h
end
end
end





namespace PrincipalizationIsoTransport

section
variable {X Y : Sch}
section
variable (e : X ≅ Y) (U : Opn Y)
abbrev preimageOpens : X.Opens :=
  (Opens.map e.hom.base).obj U

theorem preimageOpens_io_comp_hom :
    ι (preimageOpens e U) ≫ e.hom = (preimageOpensIso e U).hom ≫ ι U :=by simp_all
end

section
variable (f : X ≅ Y) (I : ISD Y)
theorem ker_subschemeio_le_ker_comap_subschemeio_comp_hom :
    ker I.si
      ≤ ker (subschemeι (comap I f.hom) ≫ f.hom) := by
  rw [ker_comp, q2,
    q2]
  exact le_map_comap I f.hom

theorem ker_comap_subschemeio_le_ker_subschemeio_comp_inv :
    ker (comap I f.hom).si
      ≤ ker (subschemeι I ≫ inv f) := by
  rw [ker_comp, q2,
    q2]
  have h2 := le_map_comap (cmI I f.hom) f.inv
  rwa [← comap_comp, inv_hom_id, comap_id] at h2

theorem exists_iso_subscheme_comap_comm :
    ∃ g : subscheme (comap I f.hom) ≅ subscheme I,
      g.hom ≫ subschemeι I = subschemeι (comap I f.hom) ≫ f.hom := by
  let _a0 := siI (cmI I f.hom) ≫ isoH f
  let _a1 := ker_subschemeio_le_ker_comap_subschemeio_comp_hom f I
  have hc := m154 I.si
    _a0 _a1
  let _a2 := siI I ≫ isoI f
  let _a3 := ker_comap_subschemeio_le_ker_subschemeio_comp_inv f I
  have hd := m154 (cmI I f.hom).si
    _a2 _a3
  set c := m64 I.si _a0
    _a1
  set d := m64 (cmI I f.hom).si _a2
    _a3
  refine ⟨⟨c, d, ?_, ?_⟩, hc⟩
  rw [← cancel_mono (cmI I f.hom).si, assoc, hd, ← assoc, hc,
    assoc, hom_inv_id, comp_id, id_comp]
  rw [← cancel_mono I.si, assoc, hc, ← assoc, hd,
    assoc, inv_hom_id, comp_id, id_comp]

def comapSubschemeIso :
    subscheme (comap I f.hom) ≅ subscheme I :=
  (exists_iso_subscheme_comap_comm f I).choose

theorem comapSubschemeIso_hom_comp :
    (comapSubschemeIso f I).hom ≫ subschemeι I = subschemeι (comap I f.hom) ≫ f.hom :=
  (exists_iso_subscheme_comap_comm f I).choose_spec
end
end

@[reassoc]
theorem subschemeio_comp_preimageOpens_io_comp_hom {W W' : Sch} (e : W' ≅ W) (U : Opn W)
    (H : U.toScheme.IdealSheafData) :
    subschemeι (comap H (preimageOpensIso e U).hom) ≫ ι (preimageOpens e U) ≫ e.hom
      = (comapSubschemeIso (preimageOpensIso e U) H).hom ≫ subschemeι H ≫ ι U := by
  rw [preimageOpens_io_comp_hom, ← assoc, ← comapSubschemeIso_hom_comp, assoc]

section
variable {X Y : Sch}
section
variable (g : X ≅ Y)
theorem coe_support_comap_iso (J : ISD Y) :
    (support (comap J g.hom) : Set ↥X) = ⇑g.hom.base ⁻¹' (support J : Set ↥Y) :=by simp_all
theorem exists_eq_some_of_map_comap_eq_some
    {o : Option Y.IdealSheafData} {b : ISD X}
    (h : o.map (fun J => comap J g.hom) = Option.some b) :
    ∃ a, o = Option.some a ∧ comap a g.hom = b :=by simp_all
theorem eq_none_of_map_comap_eq_none
    {o : Option Y.IdealSheafData} (h : o.map (fun J => comap J g.hom) = Option.none) :
    o = Option.none :=by simp_all
end

section
variable (e : X ≅ Y) (V : Opn Y) (A : ISD Y)
theorem comap_preimageOpens_io_comap_iso :
    comap (comap A e.hom) (preimageOpens e V).i = comap (comap A V.i) (preimageOpensIso e V).hom := by
  rw [← comap_comp, ← comap_comp, preimageOpens_io_comp_hom]

theorem support_comap_preimageOpens_subset (B : V.toScheme.IdealSheafData)
    (h : (support (comap A V.i) : Set ↥V.toScheme) ⊆ (support B : Set ↥V.toScheme)) :
    ((comap (comap A e.hom) (preimageOpens e V).i).support :
        Set ↥(preimageOpens e V).toScheme)
      ⊆ (support (comap B (preimageOpensIso e V).hom) : Set ↥(preimageOpens e V).toScheme) := by
  rw [comap_preimageOpens_io_comap_iso, coe_support_comap_iso, coe_support_comap_iso]
  exact preimage_mono h
end

theorem comap_subschemeio_comap_iso (r : X ≅ Y) (B : ISD Y)
    (A : ISD Y) :
    comap (comap A r.hom) (comap B r.hom).si
      = comap (comap A B.si) (comapSubschemeIso r B).hom := by
  rw [← comap_comp, ← comap_comp,
    comapSubschemeIso_hom_comp]
end

private theorem preimage_base_comp {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z) (S : Set ↥Z) :
    ⇑(f ≫ g).base ⁻¹' S = ⇑f.base ⁻¹' (⇑g.base ⁻¹' S) := by
  ext x
  simp

section
variable {X Y : Sch} (e : X ≅ Y) (V : Opn Y)
theorem isOpen_preimage_support_comap_preimageOpensIso
    (A : ISD Y) (B : V.toScheme.IdealSheafData)
    (h : IsOpen $ ⇑B.subschemeι.base ⁻¹' (support (comap A V.i) : Set ↥V.toScheme)) :
    IsOpen $ ⇑(comap B (preimageOpensIso e V).hom).subschemeι.base ⁻¹'
      ((comap (comap A e.hom) (preimageOpens e V).i).support :
        Set ↥(preimageOpens e V).toScheme) := by
  let _a0 := preimageOpensIso e V
  rw [comap_preimageOpens_io_comap_iso, coe_support_comap_iso _a0 $ cmI A V.i, ← _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp,
    ← comapSubschemeIso_hom_comp, _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp]
  exact h.preimage (comapSubschemeIso _a0 B).hom.continuous

theorem preimage_comap_subschemeio_preimageOpens_comp
    (B : V.toScheme.IdealSheafData) (Mem : Set ↥Y) :
    ⇑(subschemeι (comap B (preimageOpensIso e V).hom) ≫ ι (preimageOpens e V)).base ⁻¹'
        (⇑e.hom.base ⁻¹' Mem)
      = ⇑(comapSubschemeIso (preimageOpensIso e V) B).hom.base ⁻¹'
        (⇑(subschemeι B ≫ ι V).base ⁻¹' Mem) := by
  rw [← _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp, ← _root_.FunctorialResolution.EmbeddedResolution.PrincipalizationIsoTransport.preimage_base_comp, assoc, subschemeio_comp_preimageOpens_io_comp_hom]
end

section
variable {k : Type} [Field k]
theorem principalizationCertificate_comap_preimageOpensIso {W W' : Sch}
    (p : W ⟶ Sp k) (e : W' ≅ W) (Z : ISD W) (mu_ : ℕ)
    (Mem : Set ↥W) (V : Opn W) (B : V.toScheme.IdealSheafData)
    (Jz : B.subscheme.IdealSheafData)
    (h : ∀ (T : Sch) (f : T ≅ subscheme B),
      PrincipalizationCertificate T (f.hom ≫ subschemeι B ≫ ι V ≫ p) (comap Jz f.hom) mu_
        (⇑f.hom.base ⁻¹' (⇑(subschemeι B ≫ ι V).base ⁻¹' Mem))
        ((comap (comap Z V.i) B.si).comap f.hom)) :
    PrincipalizationCertificate (comap B (preimageOpensIso e V).hom).subscheme
      (subschemeι (comap B (preimageOpensIso e V).hom) ≫ ι (preimageOpens e V) ≫ e.hom ≫ p)
      (comap Jz (comapSubschemeIso (preimageOpensIso e V) B).hom) mu_
      (⇑(subschemeι (comap B (preimageOpensIso e V).hom) ≫ ι (preimageOpens e V)).base ⁻¹'
        (⇑e.hom.base ⁻¹' Mem))
      ((comap (comap Z e.hom) (preimageOpens e V).i).comap
        (comap B (preimageOpensIso e V).hom).subschemeι) := by
  let _a0 := preimageOpensIso e V
  have ht := h (cmI B _a0.hom).subscheme $ comapSubschemeIso _a0 B
  rw [← subschemeio_comp_preimageOpens_io_comp_hom_assoc, ← preimage_comap_subschemeio_preimageOpens_comp, ← comap_subschemeio_comap_iso,
    ← comap_preimageOpens_io_comap_iso] at ht
  exact ht

theorem isSmoothDivisor_comap_iso {X Y : Sch}
    (q : Y ⟶ Sp k) (e : X ≅ Y) (D : ISD Y)
    (h : IsSmoothDivisor q D) : IsSmoothDivisor (e.hom ≫ q) $ comap D e.hom := by
  rw [isSmoothDivisor_iff] at h ⊢
  exact ⟨h.1.comap_iso e, smooth_comap_iso q e D h.2⟩

theorem isSmoothDivisor_comap_preimageOpensIso {W W' : Sch}
    (p : W ⟶ Sp k) (e : W' ≅ W) (U : Opn W)
    (H : U.toScheme.IdealSheafData) (h : IsSmoothDivisor (ι U ≫ p) H) :
    IsSmoothDivisor (ι (preimageOpens e U) ≫ e.hom ≫ p) $ comap H (preimageOpensIso e U).hom := by
  have h' := isSmoothDivisor_comap_iso (opI U ≫ p) (preimageOpensIso e U) H h
  rwa [← assoc, ← preimageOpens_io_comp_hom, assoc] at h'
end

theorem image_mem_irreducibleComponents_of_homeomorph {al_ be_ : Type} [TopologicalSpace al_]
    [TopologicalSpace be_] (h : al_ ≃ₜ be_) {T : Set al_} (hT : T ∈ irreducibleComponents al_) :
    ⇑h '' T ∈ irreducibleComponents be_ := by
  refine ⟨hT.1.image _ h.continuous.continuousOn, ?_⟩
  intro S hS hsub
  have h2 : ⇑h.symm '' S = preimage h S := by
    ext y
    constructor
    rintro ⟨z, hz, rfl⟩
    simpa using hz
    intro hy
    exact ⟨h y, hy, by simp⟩
  have hpre : IsIrreducible $ preimage h S := by
    rw [← h2]
    exact hS.image _ h.symm.continuous.continuousOn
  have hTsub := fun y hy => hsub ⟨y, hy, rfl⟩
  intro y hy
  refine ⟨h.symm y, (an2 hT hpre hTsub) ?_, by simp⟩
  simpa using hy

theorem exists_isOpen_comap_eq_comap_preimageOpensIso {W W' : Sch} (e : W' ≅ W) (N : ISD W)
    (Mem : Set ↥W) (V : Opn W) (B : V.toScheme.IdealSheafData)
    (Jz : B.subscheme.IdealSheafData)
    (h : ∀ x : ↥B.subscheme, (subschemeι B ≫ ι V).base x ∉ Mem →
      ∃ O : B.subscheme.Opens, x ∈ O ∧
        comap Jz O.i = (comap (comap N V.i) B.si).comap O.i)
    (x : ↥(comap B (preimageOpensIso e V).hom).subscheme)
    (hx : (subschemeι (comap B (preimageOpensIso e V).hom) ≫ ι (preimageOpens e V)).base x
      ∉ ⇑e.hom.base ⁻¹' Mem) :
    ∃ O : (comap B (preimageOpensIso e V).hom).subscheme.Opens, x ∈ O ∧
      comap (comap Jz (comapSubschemeIso (preimageOpensIso e V) B).hom) O.i =
        ((comap (comap N e.hom) (preimageOpens e V).i).comap
          (comap B (preimageOpensIso e V).hom).subschemeι).comap O.i := by
  let _c0 := comapSubschemeIso (preimageOpensIso e V) B
  let _a0 := siI B ≫ opI V
  have hx' : bsM _a0
      (ihB_ _c0 x) ∉ Mem := by
    intro hmem
    apply hx
    have hmem2 : x ∈ ⇑_c0.hom.base ⁻¹'
        (preimage _a0.base Mem) := hmem
    rwa [← preimage_comap_subschemeio_preimageOpens_comp e V B Mem] at hmem2
  obtain ⟨O, hxO, hO⟩ := h (ihB_ _c0 x) hx'
  refine ⟨preimageOpens _c0 O, hxO, ?_⟩
  rw [comap_preimageOpens_io_comap_iso, comap_preimageOpens_io_comap_iso, comap_subschemeio_comap_iso, comap_preimageOpens_io_comap_iso, hO]

theorem nonzeroOnComponents_comap_iso {X Y : Sch} (f : X ≅ Y) (I : ISD Y)
    (h : NonzeroOnComponents I) : NonzeroOnComponents $ comap I f.hom := by
  rw [nonzeroOnComponents_iff] at h ⊢
  intro T hT hsub
  refine h (⇑f.hom.base '' T) (image_mem_irreducibleComponents_of_homeomorph (m207 f) hT) ?_
  rintro y ⟨x, hx, rfl⟩
  have hx' := hsub hx
  rwa [coe_support_comap_iso f I] at hx'

end PrincipalizationIsoTransport

theorem isoInvariantOrderCertificateDescend : OrderCertificateIsoInvariantOfMaxContact := by
  intro k inst W p N mu_ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc hJcert hJtrans W' e
  have hsupp : ∀ z', z' ∈ spI (cmI Z e.hom) → ihB_ e z' ∈ spI Z := by
    intro z' hz'
    have h1 : z' ∈ (spI (cmI Z e.hom) : Set ↥W') := hz'
    rwa [PrincipalizationIsoTransport.coe_support_comap_iso e Z] at h1
  refine OrderCertificate.descend
    (fun z' hz' => PrincipalizationIsoTransport.preimageOpens e $ U (ihB_ e z') (hsupp z' hz'))
    (fun z' hz' => hU (ihB_ e z') $ hsupp z' hz')
    (fun z' hz' => cmI (H (ihB_ e z') (hsupp z' hz'))
      (preimageOpensIso e (U (ihB_ e z') (hsupp z' hz'))).hom)
    (fun z' hz' => PrincipalizationIsoTransport.isSmoothDivisor_comap_preimageOpensIso p e
      (U (ihB_ e z') (hsupp z' hz')) (H (ihB_ e z') (hsupp z' hz'))
      (hH (ihB_ e z') (hsupp z' hz')))
    (fun z' hz' => PrincipalizationIsoTransport.support_comap_preimageOpens_subset e
      (U (ihB_ e z') (hsupp z' hz')) N (H (ihB_ e z') (hsupp z' hz'))
      (hNsubH (ihB_ e z') (hsupp z' hz')))
    (fun z' hz' => PrincipalizationIsoTransport.support_comap_preimageOpens_subset e
      (U (ihB_ e z') (hsupp z' hz')) Z (H (ihB_ e z') (hsupp z' hz'))
      (hZH (ihB_ e z') (hsupp z' hz')))
    (fun z' hz' => (J (ihB_ e z') (hsupp z' hz')).map
      (fun Jz => cmI Jz (PrincipalizationIsoTransport.comapSubschemeIso
        (preimageOpensIso e (U (ihB_ e z') (hsupp z' hz')))
        (H (ihB_ e z') (hsupp z' hz'))).hom))
    ?_ ?_ ?_ ?_
  intro z' hz' hnone
  exact PrincipalizationIsoTransport.isOpen_preimage_support_comap_preimageOpensIso e (U (ihB_ e z') (hsupp z' hz')) Z
    (H (ihB_ e z') (hsupp z' hz'))
    (hJnone (ihB_ e z') (hsupp z' hz') (PrincipalizationIsoTransport.eq_none_of_map_comap_eq_none _ hnone))
  intro z' hz' Jz' heq
  obtain ⟨Jz, hJz, rfl⟩ := PrincipalizationIsoTransport.exists_eq_some_of_map_comap_eq_some _ heq
  exact PrincipalizationIsoTransport.nonzeroOnComponents_comap_iso _ Jz
    (hJcomp (ihB_ e z') (hsupp z' hz') Jz hJz)
  intro z' hz' Jz' heq x hx
  obtain ⟨Jz, hJz, rfl⟩ := PrincipalizationIsoTransport.exists_eq_some_of_map_comap_eq_some _ heq
  exact PrincipalizationIsoTransport.exists_isOpen_comap_eq_comap_preimageOpensIso e N Mem (U (ihB_ e z') (hsupp z' hz'))
    (H (ihB_ e z') (hsupp z' hz')) Jz
    (hJloc (ihB_ e z') (hsupp z' hz') Jz hJz) x hx
  intro z' hz' Jz' heq
  obtain ⟨Jz, hJz, rfl⟩ := PrincipalizationIsoTransport.exists_eq_some_of_map_comap_eq_some _ heq
  exact PrincipalizationIsoTransport.principalizationCertificate_comap_preimageOpensIso p e Z mu_ Mem (U (ihB_ e z') (hsupp z' hz'))
    (H (ihB_ e z') (hsupp z' hz')) Jz
    (hJtrans (ihB_ e z') (hsupp z' hz') Jz hJz)

section
variable {k : Type} [Field k] {W W' : Sch} {p : W ⟶ Sp k}
theorem OrderCertificate.comap_iso_hom_comp {N : ISD W} {mu_ : ℕ}
    {Mem : Set ↥W} {Z : ISD W} (e : W' ≅ W) (h : OrderCertificate W p N mu_ Mem Z) :
    OrderCertificate W' (e.hom ≫ p) (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom :=
  OrderCertificate.comap_iso isoInvariantOrderCertificateDescend e h

section
variable {p' : W' ⟶ Sp k}
theorem PrincipalizationCertificate.comap_iso_of_eq_iso_hom_comp
    {I : ISD W} {m : ℕ} {Mem : Set ↥W} {Z : ISD W}
    (e : W' ≅ W) (hp : p' = e.hom ≫ p) (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W' p' (comap I e.hom) m (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom :=
  PrincipalizationCertificate.comap_iso_of_eq isoInvariantOrderCertificateDescend e hp h

theorem OrderCertificate.comap_iso_of_eq_iso_hom_comp
    {N : ISD W} {mu_ : ℕ} {Mem : Set ↥W} {Z : ISD W}
    (e : W' ≅ W) (hp : p' = e.hom ≫ p) (h : OrderCertificate W p N mu_ Mem Z) :
    OrderCertificate W' p' (comap N e.hom) mu_ (⇑e.hom.base ⁻¹' Mem) $ comap Z e.hom :=
  OrderCertificate.comap_iso_of_eq isoInvariantOrderCertificateDescend e hp h
end
end





def EffectiveCartierSupportContainsNoComponent : Prop :=
  ∀ (X : Sch) (D : ISD X), Blowup.IsLocallyGeneratedByNonZeroDivisor D →
    ∀ C ∈ irreducibleComponents (X : Type), ¬ C ⊆ (support D : Set (X : Type))

theorem effectiveCartierSupportContainsNoComponent : EffectiveCartierSupportContainsNoComponent :=
  fun _ _ hD _ hC => hD.not_irreducibleComponent_subset_support hC

theorem nonzeroOnComponents_comap_iso_hom {X Y : Sch} (f : X ≅ Y) (I : ISD Y)
    (h : NonzeroOnComponents I) : NonzeroOnComponents $ comap I f.hom :=
  PrincipalizationIsoTransport.nonzeroOnComponents_comap_iso f I h

section
variable {al_ : Type}
theorem isPreirreducible_inter_of_isOpen [TopologicalSpace al_] {T U : Set al_}
    (hT : IsPreirreducible T) (hU : IsOpen U) : IsPreirreducible $ T ∩ U := by
  intro V W hV hW hVne hWne
  obtain ⟨a, haTU, haV⟩ := hVne
  obtain ⟨b, hbTU, hbW⟩ := hWne
  obtain ⟨x, hxT, hx1, hx2⟩ :=
    hT (V ∩ U) (W ∩ U) (hV.inter hU) (hW.inter hU)
      ⟨a, an1 haTU, haV, an2 haTU⟩ ⟨b, an1 hbTU, hbW, an2 hbTU⟩
  exact ⟨x, ⟨hxT, an2 hx1⟩, an1 hx1, an1 hx2⟩

theorem isPreirreducible_preimage_val [TopologicalSpace al_] {U V : Set al_}
    (hVU : V ⊆ U) (hV : IsPreirreducible V) :
    IsPreirreducible $ (Subtype.val : U → al_) ⁻¹' V := by
  intro O1 O2 hO1_ hO2_ h1_ h2_
  obtain ⟨G1, hG1_, rfl⟩ := mp_ isOpen_induced_iff hO1_
  obtain ⟨G2, hG2_, rfl⟩ := mp_ isOpen_induced_iff hO2_
  obtain ⟨a, ha⟩ := h1_
  obtain ⟨b, hb⟩ := h2_
  obtain ⟨x, hxV, hx1, hx2⟩ := hV G1 G2 hG1_ hG2_ ⟨a.1, ha.1, ha.2⟩ ⟨b.1, hb.1, hb.2⟩
  exact ⟨⟨x, hVU hxV⟩, hxV, hx1, hx2⟩

theorem exists_irreducibleComponent_subset_of_section {be_ : Type}
    [TopologicalSpace al_] [TopologicalSpace be_]
    (f : al_ → be_) (hf : Continuous f) (Uc : Set be_) (hUc : IsOpen Uc)
    (g : ↥Uc → al_) (hgc : Continuous g) (hgf : ∀ y, f (g y) = (y : be_))
    (hgs : ∀ x, f x ∈ Uc → ∃ y, g y = x)
    (C : Set al_) (hC : C ∈ irreducibleComponents al_) (x0_ : al_) (hx0_ : x0_ ∈ C) (hx0U : f x0_ ∈ Uc)
    (K : Set be_) (hK : IsClosed K) (hCK : C ⊆ f ⁻¹' K) :
    ∃ T ∈ irreducibleComponents be_, T ⊆ K := by
  have hCirr := an1 hC
  have hVcOpen := hUc.preimage hf
  let _m0 := C ∩ preimage f Uc
  have hWne : _m0.Nonempty := ⟨x0_, hx0_, hx0U⟩
  have hWirr : IsIrreducible _m0 :=
    ⟨hWne, isPreirreducible_inter_of_isOpen hCirr.2 hVcOpen⟩
  obtain ⟨T, hT, hTsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ $ hWirr.image f hf.continuousOn
  have hTirr := an1 hT
  have hy0T := hTsub ⟨x0_, ⟨hx0_, hx0U⟩, rfl⟩
  have hSne : (T ∩ Uc).Nonempty := ⟨f x0_, hy0T, hx0U⟩
  have hSirr : IsIrreducible $ T ∩ Uc := ⟨hSne, isPreirreducible_inter_of_isOpen hTirr.2 hUc⟩
  let _m1 := preimage (m161 : ↥Uc → be_) $ T ∩ Uc
  have hpre : IsIrreducible _m1 :=
    ⟨⟨⟨f x0_, hx0U⟩, hy0T, hx0U⟩, isPreirreducible_preimage_val (fun y hy => an2 hy) hSirr.2⟩
  have hVeq : preimage f (T ∩ Uc) = g '' _m1 := by
    ext x
    constructor
    intro hx
    obtain ⟨y, hy⟩ := hgs x hx.2
    refine ⟨y, ?_, hy⟩
    have h3 := hgf y
    rw [hy] at h3
    show (y : be_) ∈ T ∩ Uc
    rwa [← h3]
    rintro ⟨y, hy, rfl⟩
    show f (g y) ∈ T ∩ Uc
    rwa [hgf y]
  have hVirr := hpre.image g hgc.continuousOn
  rw [← hVeq] at hVirr
  have hVW : preimage f (T ∩ Uc) ⊆ C ∩ preimage f Uc := fun x hx => ⟨(subset_closure.trans $ an2 hC hVirr.closure $ (subset_closure_inter_of_isPreirreducible_of_isOpen hCirr.2 hVcOpen hWne).trans $ closure_mono fun x hx => ⟨hTsub ⟨x, hx, rfl⟩, an2 hx⟩) hx, an2 hx⟩
  have hTUK : T ∩ Uc ⊆ K := by
    intro y hy
    let _a0 := g ⟨y, an2 hy⟩
    have hx : _a0 ∈ C ∩ preimage f Uc := by
      refine hVW ?_
      show f _a0 ∈ T ∩ Uc
      rwa [hgf ⟨y, an2 hy⟩]
    have h5 : f _a0 ∈ K := hCK hx.1
    rwa [hgf ⟨y, an2 hy⟩] at h5
  refine ⟨T, hT, ?_⟩
  exact (subset_closure_inter_of_isPreirreducible_of_isOpen hTirr.2 hUc hSne).trans $ closure_minimal hTUK hK
end

theorem coe_support_comap_eq_preimage {X Y : Sch} (f : X ⟶ Y) (I : ISD Y) :
    (support (comap I f) : Set ↥X) = ⇑f.base ⁻¹' (support I : Set ↥Y) :=by simp_all
theorem exists_section_off_center {X X' : Sch} (pi_ : X' ⟶ X) (Z : ISD X)
    (hpi_ : Blowup.IsBlowupAlongIdealSheaf pi_ Z) :
    ∃ g : ↥(((support Z : Set ↥X))ᶜ) → ↥X', Continuous g ∧
      (∀ y, ⇑pi_.base (g y) = (y : ↥X)) ∧
      (∀ x : ↥X', ⇑pi_.base x ∈ ((support Z : Set ↥X))ᶜ → ∃ y, g y = x) := by
  have := Blowup.blowupIsIsoOffCenter X X' pi_ Z hpi_
  have hinvhom : ∀ (A B : Sch) (f : A ≅ B) (z : ↥B), ihB_ f (ibM f z) = z := by simp_all
  have hhominv : ∀ (A B : Sch) (f : A ≅ B) (z : ↥A), ibM f (ihB_ f z) = z := by simp_all
  let e := asIso $ pi_.mr $ suppC Z
  have hmem : ∀ y : ↥((suppI Z)ᶜ), (y : ↥X) ∈ suppC Z := fun y => y.2
  refine ⟨fun y => (ibM e ⟨(y : ↥X), hmem y⟩).1, continuous_subtype_val.comp $ e.inv.continuous.comp $ continuous_subtype_val.subtype_mk hmem, ?_, ?_⟩
  intro y
  rw [← morphismRestrict_base_coe pi_ Z.support.compl $ ibM e ⟨y, hmem y⟩]
  exact congrArg m161 $ hinvhom _ _ e _
  intro x hx
  have hx' : x ∈ pre pi_ (suppC Z) := hx
  refine ⟨⟨⇑pi_.base x, hx⟩, ?_⟩
  let _a0 := ihB_ e (⟨x, hx'⟩ : ↥(pre pi_ $ suppC Z).toScheme)
  have hb : _a0
      = ⟨⇑pi_.base x, hmem ⟨⇑pi_.base x, hx⟩⟩ :=
    m26 $ morphismRestrict_base_coe pi_ Z.support.compl ⟨x, hx'⟩
  have hc : ibM e _a0
      = ⟨x, hx'⟩ := hhominv _ _ e _
  rw [hb] at hc
  exact congrArg m161 hc

theorem nonzeroOnComponents_of_pow_mul_eq_comap (hcart : EffectiveCartierSupportContainsNoComponent)
    {X X' : Sch} (pi_ : X' ⟶ X) (Z : ISD X) (hpi_ : Blowup.IsBlowupAlongIdealSheaf pi_ Z) (m : ℕ)
    (I : ISD X) (I' : ISD X')
    (htr : (comap Z pi_) ^ m * I' = comap I pi_)
    (hI : NonzeroOnComponents I) : NonzeroOnComponents I' := by
  rw [nonzeroOnComponents_iff] at hI ⊢
  intro C hC hsub
  have hsub2 : C ⊆ (spI (cmI I pi_) : Set ↥X') := by
    intro x hx
    refine mpr_ (mem_support_iff_stalkIdeal_ne_top (comap I pi_) x) ?_
    rw [← htr, stalkIdeal_mul]
    intro hcon
    have hle : stalkIdeal ((cmI Z pi_) ^ m) x * stalkIdeal I' x ≤ stalkIdeal I' x :=
      le_trans mul_le_inf inf_le_right
    rw [hcon] at hle
    exact mp_ (mem_support_iff_stalkIdeal_ne_top I' x) (hsub hx) $ mp_ top_le_iff hle
  obtain ⟨x0_, hx0C, hx0E⟩ := mp_ not_subset $ hcart X' (cmI Z pi_) hpi_.1 C hC
  let _a0 := suppI Z
  have hx0U : ⇑pi_.base x0_ ∈ _a0ᶜ := by
    intro hmem
    refine hx0E ?_
    rwa [coe_support_comap_eq_preimage pi_ Z]
  have hCK := hsub2
  rw [coe_support_comap_eq_preimage pi_ I] at hCK
  obtain ⟨g, hgc, hgf, hgs⟩ := exists_section_off_center pi_ Z hpi_
  obtain ⟨T, hTcomp, hTK⟩ :=
    exists_irreducibleComponent_subset_of_section (⇑pi_.base) pi_.continuous (_a0ᶜ)
      (Z.support.2.isOpen_compl) g hgc hgf hgs C hC x0_ hx0C hx0U
      I.support I.support.2 hCK
  exact hI T hTcomp hTK

namespace MarkedSequenceOfBlowups

section
variable (hcart : EffectiveCartierSupportContainsNoComponent) {T : MarkedIdealWithBoundary} (hT : IsAdmissible T) (s : T.SequenceOfBlowups)
include hcart hT
theorem nonzeroOnComponents_ideal_of_isAdmissible :
    ∀ t : ℕ, t ≤ s.toSequenceOfBlowups.length → NonzeroOnComponents (s.ideal t) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [s.ideal_zero]
    exact nonzeroOnComponents_comap_iso_hom s.toSequenceOfBlowups.isoZero T.ideal hT.nonzeroOnComponents
  | succ n ih =>
    intro hn
    have hlt := hn
    refine nonzeroOnComponents_of_pow_mul_eq_comap hcart (msTrS s n)
      (msCtr s n) (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt) T.mult
      (s.ideal n) (s.ideal $ n + 1) ?_ $ ih $ m49 hlt
    rw [← s.exceptionalDivisor_eq n]
    exact s.ideal_succ n hlt

theorem centersContainNoComponent_ofMarkedSequence :
    s.NoComp := by
  intro i hi W hW hsub
  have hlt := hi
  have hnz := nonzeroOnComponents_ideal_of_isAdmissible hcart hT s i $ m49 hlt
  rw [nonzeroOnComponents_iff] at hnz
  refine hnz W hW $ hsub.trans ?_
  intro x hx
  exact mp (mem_orderAtLeastLocus_one_iff (s.ideal i) x)
    (orderAtLeastLocus_subset_of_le (s.ideal i) hT.one_le_mult $ s.center_order i hlt hx)
end

end MarkedSequenceOfBlowups





structure MarkedSchemeWithCenter (k : Type) [Field k] where
  ambient : Sch
  ideal : ISD ambient
  boundary : Bdy ambient
  structMap : ambient ⟶ Sp k
  center : ISD ambient

private theorem comap_inv_comap_hom {X Y : Sch} (e : X ≅ Y) (I : ISD Y) :
    comap (comap I e.hom) e.inv = I := by
  rw [← comap_comp, e.inv_hom_id]
  simp

namespace MarkedSchemeWithCenter

variable {k : Type} [Field k]

section
variable (D : MarkedSchemeWithCenter k) {A} (e : A ≅ D.ambient)
def transport : MarkedSchemeWithCenter k where
  ambient := A
  ideal := D.ideal.comap e.hom
  boundary := D.boundary.map fun J => comap J e.hom
  structMap := e.hom ≫ structMap D
  center := D.center.comap e.hom

@[simp]
theorem transport_ambient :
    (D.transport e).ambient = A := rfl

@[simp]
theorem transport_ideal :
    ideal (D.transport e) = D.ideal.comap e.hom := rfl

@[simp]
theorem transport_boundary :
    boundary (D.transport e) = D.boundary.map fun J => comap J e.hom := rfl

@[simp]
theorem transport_projectionToBase :
    structMap (D.transport e) = e.hom ≫ structMap D := rfl

@[simp]
theorem transport_center :
    center (D.transport e) = D.center.comap e.hom := rfl
end

theorem mk_congr {K : Type} [Field K] (A : Sch)
    (I I' : ISD A) (B B' : Bdy A)
    (f f' : A ⟶ Sp K) (C C' : ISD A)
    (h1 : I = I') (h2 : B = B') (h3 : f = f') (h4 : C = C') :
    (MarkedSchemeWithCenter.mk A I B f C : MarkedSchemeWithCenter K) = MarkedSchemeWithCenter.mk A I' B' f' C' := by
  subst h1 h2 h3 h4
  rfl

theorem transport_refl (D : MarkedSchemeWithCenter k) : D.transport (refl D.ambient) = D := by
  obtain ⟨A, I, B, f, C⟩ := D
  have h1 : cmI I (𝟙 A) = I := by simp
  have h2 : B.map (cmI · $ 𝟙 A) = B := by simp
  refine mk_congr _ _ _ _ _ _ _ _ _ h1 h2 (id_comp f) ?_
  simp

end MarkedSchemeWithCenter

def IsInvariantUnderIso {k : Type} [Field k] (P : MarkedSchemeWithCenter k → Prop) : Prop :=
  ∀ (D : MarkedSchemeWithCenter k) (A : Sch) (e : A ≅ D.ambient), P D → P (D.transport e)

namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (s : MarkedBlowupSequenceData p I m E) (i : ℕ)
def dataAt : MarkedSchemeWithCenter k where
  ambient := s.toBlowupSequenceData.obj i
  ideal := s.ideal i
  boundary := s.boundary i
  structMap := s.proj i ≫ p
  center := s.toBlowupSequenceData.center i

@[simp]
theorem dataAt_ambient :
    (s.dataAt i).ambient = s.toBlowupSequenceData.obj i := rfl

@[simp]
theorem dataAt_ideal :
    (s.dataAt i).ideal = s.ideal i := rfl

@[simp]
theorem dataAt_boundary :
    (s.dataAt i).boundary = s.boundary i := rfl

@[simp]
theorem dataAt_structMap :
    (s.dataAt i).structMap = s.proj i ≫ p := rfl

@[simp]
theorem dataAt_center :
    (s.dataAt i).center = s.toBlowupSequenceData.center i := rfl
end

theorem transport_dataAt_congr {K : Type} [Field K] {Y : Sch}
    {q : Y ⟶ Sp K} {J : ISD Y} {n : ℕ}
    {F : Bdy Y} (d : MarkedBlowupSequenceData q J n F) {a b : ℕ} (hab : a = b)
    {Z : Sch} (h1 : Z = d.toBlowupSequenceData.obj a) (h2 : Z = d.toBlowupSequenceData.obj b) :
    (d.dataAt a).transport (eqToIso h1) = (d.dataAt b).transport (eqToIso h2) := by
  subst hab
  rfl

variable (s : MarkedBlowupSequenceData p I m E)
  (t : MarkedBlowupSequenceData (s.proj s.toBlowupSequenceData.length ≫ p) (s.ideal s.toBlowupSequenceData.length) m
    $ s.boundary s.toBlowupSequenceData.length)

section
variable (hinv : ComapIsoInvariance)
theorem append_dataAt_of_lt_length {i : ℕ} (h : i < s.toBlowupSequenceData.length) :
    (s.append t hinv).dataAt i =
      (s.dataAt i).transport (eqToIso $ appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_of_lt h) := by
  have hle := le_of_lt h
  have h3 : s.appendProjectionToBase t i ≫ p =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t hle) ≫ (s.proj i ≫ p) := by
    rw [appendProjectionToBase_of_le_length s t hle, assoc]
  exact MarkedSchemeWithCenter.mk_congr _ _ _ _ _ _ _ _ _ (appendIdeal_of_le_length s t hle) (appendBoundary_of_le_length s t hle) h3 $ appendToBlowupSequenceData_center_of_lt_length s t h

theorem append_dataAt_length :
    (s.append t hinv).dataAt s.toBlowupSequenceData.length =
      ((t.dataAt 0).transport t.toBlowupSequenceData.isoZero.symm).transport
        (eqToIso $ appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_refl s.toBlowupSequenceData.length) := by
  have h1 : s.appendIdeal t (mbsLen s) =
      ((t.ideal 0).comap t.toBlowupSequenceData.isoZero.inv).comap
        (eqToHom $ appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_refl $ mbsLen s) := by
    rw [appendIdeal_of_le_length s t $ le_refl $ mbsLen s, t.ideal_zero, comap_inv_comap_hom]
  have h2 : s.appendBoundary t (mbsLen s) =
      ((t.boundary 0).map (·.comap t.toBlowupSequenceData.isoZero.inv)).map
        (fun J => cmI J $ eqToHom $ appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_refl $ mbsLen s) := by
    rw [appendBoundary_of_le_length s t $ le_refl $ mbsLen s, t.boundary_zero]
    simp [List.map_map, comp_def, comap_inv_comap_hom]
  have h3 : s.appendProjectionToBase t (mbsLen s) ≫ p =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t $ le_refl $ mbsLen s) ≫
        (t.toBlowupSequenceData.isoZero.inv ≫
          (t.proj 0 ≫ (s.proj (mbsLen s) ≫ p))) := by
    rw [appendProjectionToBase_of_le_length s t $ le_refl $ mbsLen s, t.proj_zero]
    simp
  exact MarkedSchemeWithCenter.mk_congr _ _ _ _ _ _ _ _ _ h1 h2 h3 $ appendToBlowupSequenceData_center_length s t

theorem append_dataAt_of_length_lt {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    (s.append t hinv).dataAt i =
      (t.dataAt $ i - s.toBlowupSequenceData.length).transport
        (eqToIso $ appendToBlowupSequenceData_schemeAt_of_length_lt s t h) := by
  have h3 : s.appendProjectionToBase t i ≫ p =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) ≫
        (t.proj (i - mbsLen s) ≫ (s.proj (mbsLen s) ≫ p)) := by
    rw [appendProjectionToBase_of_length_lt s t h]
    simp [assoc]
  exact MarkedSchemeWithCenter.mk_congr _ _ _ _ _ _ _ _ _ (appendIdeal_of_length_lt s t h) (appendBoundary_of_length_lt s t h) h3 $ appendToBlowupSequenceData_center_of_length_lt s t h

theorem append_dataAt_last (h : 0 < t.toBlowupSequenceData.length) :
    (s.append t hinv).dataAt ((s.append t hinv).toBlowupSequenceData.length) =
      (t.dataAt t.toBlowupSequenceData.length).transport
        (eqToIso $ appendToBlowupSequenceData_schemeAt_length_add_length s t h) := by
  have hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := by omega
  have key : (s.append t hinv).dataAt (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.dataAt t.toBlowupSequenceData.length).transport
        (eqToIso $ appendToBlowupSequenceData_schemeAt_length_add_length s t h) := by
    rw [append_dataAt_of_length_lt s t hinv hgt]
    exact transport_dataAt_congr t (by omega) _ _
  exact key

theorem append_dataAt_of_forall (P : MarkedSchemeWithCenter k → Prop)
    (hP : IsInvariantUnderIso P)
    (hs : ∀ i < s.toBlowupSequenceData.length, P $ s.dataAt i)
    (ht : ∀ i < t.toBlowupSequenceData.length, P $ t.dataAt i)
    (i : ℕ) (hi : i < (s.append t hinv).toBlowupSequenceData.length) :
    P $ (s.append t hinv).dataAt i := by
  have hN : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with hlt | heq | hgt
  rw [append_dataAt_of_lt_length s t hinv hlt]
  exact hP (s.dataAt i) _ _ $ hs i hlt
  subst heq
  rw [append_dataAt_length s t hinv]
  exact hP _ _ _ $ hP (t.dataAt 0) _ _ $ ht 0 $ by omega
  rw [append_dataAt_of_length_lt s t hinv hgt]
  exact hP (t.dataAt $ i - s.toBlowupSequenceData.length) _ _
    (ht (i - s.toBlowupSequenceData.length) $ by omega)
end

end MarkedBlowupSequenceData





namespace MarkedSchemeWithCenter

variable {k : Type} [Field k]

def boundarySupport (D : MarkedSchemeWithCenter k) : CSet D.ambient :=
  {x : ↥D.ambient | ∃ J ∈ boundary D, x ∈ (↑J.support : CSet D.ambient)}

theorem mem_boundarySupport_iff (D : MarkedSchemeWithCenter k) (x : ↥D.ambient) :
    x ∈ D.boundarySupport ↔ ∃ J ∈ boundary D, x ∈ (↑J.support : CSet D.ambient) :=
  m22

end MarkedSchemeWithCenter

theorem mem_comap_support_iff_base_mem_support {X Y : Sch} (f : X ⟶ Y)
    (J : ISD Y) (x : ↥X) :
    x ∈ support (comap J f) ↔ f.base x ∈ support J := by
  simp
  exact m22

namespace MarkedSchemeWithCenter

variable {k : Type} [Field k]

theorem boundarySupport_transport (D : MarkedSchemeWithCenter k) {A : Sch} (e : A ≅ D.ambient) :
    (D.transport e).boundarySupport = e.hom.base ⁻¹' D.boundarySupport := by
  ext x
  constructor
  rintro ⟨J, hJ, hx⟩
  obtain ⟨K, hK, rfl⟩ := List.mem_map.1 hJ
  exact ⟨K, hK, (mem_comap_support_iff_base_mem_support e.hom K x).1 hx⟩
  rintro ⟨K, hK, hx⟩
  exact ⟨cmI K e.hom, List.mem_map.2 ⟨K, hK, rfl⟩,
    (mem_comap_support_iff_base_mem_support e.hom K x).2 hx⟩

end MarkedSchemeWithCenter

namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

theorem boundarySupport_dataAt (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).boundarySupport = s.toMarkedSequenceOfBlowups.boundaryLocus i := by
  ext x
  exact Iff.trans (MarkedSchemeWithCenter.mem_boundarySupport_iff (s.dataAt i) x) $ (MarkedSequenceOfBlowups.mem_boundaryLocus_iff s.toMarkedSequenceOfBlowups i x).symm

end MarkedBlowupSequenceData

structure HasPrincipalizationCenter {k : Type} [Field k] (mu_ : ℕ) (D : MarkedSchemeWithCenter k) : Prop where
  center_nonempty : (↑D.center.support : CSet D.ambient).Nonempty
  cert : PrincipalizationCertificate D.ambient D.structMap D.ideal mu_ D.boundarySupport D.center

theorem isInvariantUnderIso_hasPrincipalizationCenter {k : Type} [Field k] (hT : OrderCertificateIsoInvariantOfMaxContact) (mu_ : ℕ) :
    IsInvariantUnderIso fun D : MarkedSchemeWithCenter k => HasPrincipalizationCenter mu_ D := by
  intro D A e hD
  constructor
  obtain ⟨x, hx⟩ := hD.center_nonempty
  refine ⟨ibM e x, ?_⟩
  refine (mem_comap_support_iff_base_mem_support e.hom D.center $ ibM e x).2 ?_
  simp_all
  have hcert := PrincipalizationCertificate.comap_iso hT e hD.cert
  rwa [MarkedSchemeWithCenter.boundarySupport_transport]

namespace MarkedBlowupSequenceData

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

theorem nonempty_center_and_certificate_of_hasPrincipalizationCenter (s : MarkedBlowupSequenceData p I m E) (mu_ : ℕ)
    (hs : ∀ i < s.toBlowupSequenceData.length, HasPrincipalizationCenter mu_ $ s.dataAt i) :
    (∀ i < s.toMarkedSequenceOfBlowups.length,
        (↑(s.toMarkedSequenceOfBlowups.center i).support : CSet $ s.toMarkedSequenceOfBlowups.schemeAt i).Nonempty) ∧
      (∀ i < s.toMarkedSequenceOfBlowups.length,
        PrincipalizationCertificate (s.toMarkedSequenceOfBlowups.schemeAt i) (s.toMarkedSequenceOfBlowups.projectionToSpec i) (s.toMarkedSequenceOfBlowups.ideal i) mu_
          (s.toMarkedSequenceOfBlowups.boundaryLocus i) $ s.toMarkedSequenceOfBlowups.center i) := by
  constructor
  intro i hi
  have hi' : i < mbsLen s := by simp_all
  exact (hs i hi').center_nonempty
  intro i hi
  have hi' : i < mbsLen s := by simp_all
  have h := (hs i hi').cert
  rw [s.boundarySupport_dataAt i] at h
  rwa [toMarkedSequence_projectionToSpec]

end MarkedBlowupSequenceData





section

variable {Y : Sch}

section
variable (L : Bdy Y) (J : FinSet L.length)
def intersectionIdeal : ISD Y :=
  ⨆ j ∈ J, get L j

@[simp]
theorem intersectionIdeal_eq_iSup :
    intersectionIdeal L J = ⨆ j ∈ J, get L j := rfl

def intersectionComponents : Set $ Set ↥Y :=
  {C | IsIrreducible C ∧ C ⊆ (support (intersectionIdeal L J) : Set ↥Y) ∧
    ∀ C' : Set ↥Y, IsIrreducible C' → C ⊆ C' → C' ⊆ (support (intersectionIdeal L J) : Set ↥Y) → C' = C}
end

open Classical in
def orderAlong (I : ISD Y) (C : Set ↥Y) : ENat :=
  if h : IsIrreducible C then orderAt I h.genericPoint else 0

section
variable (I : ISD Y) (m : ℕ) (L : Bdy Y)
def IsCandidateComponent (r : ℕ)
    (J : FinSet L.length) (C : Set ↥Y) : Prop :=
  J.card = r ∧ C ∈ intersectionComponents L J ∧ (m : ENat) ≤ orderAlong I C

def minIndexCard : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ ∃ (J : FinSet L.length) (C : Set ↥Y), IsCandidateComponent I m L r J C}

def maxCandidateOrder : ENat :=
  ⨆ (J : FinSet L.length) (C : Set ↥Y)
    (_ : IsCandidateComponent I m L (minIndexCard I m L) J C), orderAlong I C

def IsMaxOrderIndexSet
    (J : FinSet L.length) : Prop :=
  ∃ C : Set ↥Y, IsCandidateComponent I m L (minIndexCard I m L) J C ∧ orderAlong I C = maxCandidateOrder I m L
end

def binaryEncode {n : ℕ} (J : FinSet n) : ℕ :=
  ∑ j ∈ J, 2 ^ (n - 1 - (j : ℕ))

def maxBinaryCode (I : ISD Y) (m : ℕ) (L : Bdy Y) : ℕ :=
  sSup {c : ℕ | ∃ J : FinSet L.length, IsMaxOrderIndexSet I m L J ∧ binaryEncode J = c}

open Classical in
def lexMaxIndices (I : ISD Y) (m : ℕ) (L : Bdy Y) :
    FinSet L.length :=
  if h : ∃ J : FinSet L.length, IsMaxOrderIndexSet I m L J ∧ binaryEncode J = maxBinaryCode I m L then
    h.choose
  else ∅

def monomialCenterSet (I : ISD Y) (m : ℕ) (L : Bdy Y) : Set ↥Y :=
  ⋃₀ {C : Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧ orderAlong I C = maxCandidateOrder I m L}

def openSublocusIdeal {V : Sch} (ι : V ⟶ Y) (S : Set ↥V) (hS : IsOpen S) : ISD Y :=
  ker
    (AlgebraicGeometry.Scheme.Opens.i (X := V) ⟨S, hS⟩ ≫ ι)

open Classical in
def monomialCenter (I : ISD Y) (m : ℕ) (L : Bdy Y) : ISD Y :=
  if h : minIndexCard I m L ≠ 0 ∧
      IsOpen (⇑(intersectionIdeal L $ lexMaxIndices I m L).subschemeι.base ⁻¹' monomialCenterSet I m L) then
    openSublocusIdeal (intersectionIdeal L $ lexMaxIndices I m L).subschemeι
      (⇑(intersectionIdeal L $ lexMaxIndices I m L).subschemeι.base ⁻¹' monomialCenterSet I m L) h.2
  else ⊤

end
abbrev MarkedIdealWithBoundary.mc (T : MarkedIdealWithBoundary) := monomialCenter T.ideal T.mult T.boundary

namespace MarkedBlowupSequenceData

section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

section
variable (d : MarkedBlowupSequenceData p I m E)
def centerAtLast : IdealSheafData $ d.obj d.length :=
  monomialCenter (d.ideal d.length) m $ d.boundary d.length

def IsAdmissibleCenter : Prop :=
  centerAtLast d ≠ ⊤ ∧
  Smooth (subschemeι (centerAtLast d) ≫ d.proj d.length ≫ p) ∧
  HasStrictNormalCrossingsWith (d.proj d.length ≫ p) (centerAtLast d) (d.boundary d.length) ∧
  ((support (centerAtLast d) : CSet $ d.obj d.length) ⊆ orderAtLeastLocus (d.ideal d.length) m) ∧
  (∃ B : IdealSheafData $ Blowup.blowup $ centerAtLast d,
    (comap (centerAtLast d) $ Blowup.blowup.proj $ centerAtLast d) ^ m * B =
      (d.ideal d.length).comap (Blowup.blowup.proj $ centerAtLast d))
end

open Classical in
def blowupAtCenter (hinv : ComapIsoInvariance) (d : MarkedBlowupSequenceData p I m E) :
    MarkedBlowupSequenceData p I m E :=
  if h : IsAdmissibleCenter d then
    d.append
      (ofSingleBlowup (d.proj d.length ≫ p) (d.ideal d.length) m (d.boundary d.length)
        (centerAtLast d) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) hinv
  else d

def monomialBlowupIterate (hinv : ComapIsoInvariance) (d : MarkedBlowupSequenceData p I m E) :
    ℕ → MarkedBlowupSequenceData p I m E
  | 0 => d
  | (n + 1) => blowupAtCenter hinv $ monomialBlowupIterate hinv d n

section
variable (hinv : ComapIsoInvariance) (d : MarkedBlowupSequenceData p I m E)
theorem monomialBlowupIterate_zero :
    monomialBlowupIterate hinv d 0 = d := rfl

theorem monomialBlowupIterate_succ (n : ℕ) :
    monomialBlowupIterate hinv d (n + 1) = blowupAtCenter hinv (monomialBlowupIterate hinv d n) := rfl

def IsStationaryAt (n : ℕ) : Prop :=
  (monomialBlowupIterate hinv d $ n + 1).length = (monomialBlowupIterate hinv d n).length
end

end

end MarkedBlowupSequenceData

section

variable {k : Type} [Field k] {X : Sch}

def monomialBlowupSeq (hinv : ComapIsoInvariance) (p : X ⟶ Sp k)
    (I : ISD X) (m : ℕ) (E : Bdy X) : MarkedBlowupSequenceData p I m E :=
  MarkedBlowupSequenceData.monomialBlowupIterate hinv (emptyMarkedBlowupSequenceData p I m E)
    (sInf {n : ℕ | MarkedBlowupSequenceData.IsStationaryAt hinv (emptyMarkedBlowupSequenceData p I m E) n})

end

def monomialPrincipalization (hinv : ComapIsoInvariance) : PrincipalizationAssignment :=
  fun T => toMarkedSequenceOfBlowups $ monomialBlowupSeq hinv T.structMap T.ideal T.mult T.boundary

theorem monomialPrincipalization_apply (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary) :
    monomialPrincipalization hinv T =
      toMarkedSequenceOfBlowups (monomialBlowupSeq hinv T.structMap T.ideal T.mult T.boundary) := rfl





namespace MonomialCenter

section
variable {n} (J : FinSet n)
def sortedIndices : List ℕ :=
  (J.sort (· ≤ ·)).map val

theorem sortedIndices_eq_map_sort :
    sortedIndices J = (J.sort (· ≤ ·)).map val := rfl

theorem mem_sortedIndices (a : ℕ) :
    a ∈ sortedIndices J ↔ ∃ j ∈ J, (j : ℕ) = a := by
  simp [sortedIndices, mem_map, mem_sort]
end

structure CenterInvariant (n : ℕ) : Type where
  positions : FinSet n
  rank : ℕ
  value : ENat

def CenterInvariant.sortedIndices {n : ℕ} (K : CenterInvariant n) : List ℕ :=
  _root_.FunctorialResolution.EmbeddedResolution.MonomialCenter.sortedIndices K.positions

section
variable {n n'} (K : CenterInvariant n) (K' : CenterInvariant n')
def CenterInvariant.Lt : Prop :=
  K.rank < K'.rank ∨
    (K.rank = K'.rank ∧
      (K'.value < K.value ∨
        (K.value = K'.value ∧
          Lex (· < ·) K.sortedIndices K'.sortedIndices)))

def CenterInvariant.Le : Prop :=
  K.Lt K' ∨
    (K.rank = K'.rank ∧ K.value = K'.value ∧ K.sortedIndices = K'.sortedIndices)
end

def centerInvariant {Y : Sch} (I : ISD Y) (m : ℕ) (L : Bdy Y) :
    CenterInvariant L.length where
  positions := lexMaxIndices I m L
  rank := minIndexCard I m L
  value := maxCandidateOrder I m L





end MonomialCenter



namespace MonomialCenter

section
variable {al_ be_ : Type} [LinearOrder al_] [LinearOrder be_]
theorem sort_image_of_strictMono
    [DecidableEq be_] (f : al_ → be_) (hf : StrictMono f) (s : Finset al_) :
    (s.image f).sort (· ≤ ·) = (s.sort (· ≤ ·)).map f := by
  refine List.Pairwise.eq_of_mem_iff ((sortedLT_sort $ s.image f).pairwise) ((sortedLT_sort s).pairwise.map f fun _ _ hab => hf hab) ?_
  intro b
  simp [mem_sort]

theorem lex_map_iff_of_strictMono
    (f : al_ → be_) (hf : StrictMono f) (l l' : List al_) :
    Lex (· < ·) (l.map f) (l'.map f) ↔ Lex (· < ·) l l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil =>
      simp only [map_nil]
      exact iff_of_false (by rintro ⟨⟩) $ by rintro ⟨⟩
    | cons b t =>
      simp only [map_nil, map_cons]
      exact iff_of_true List.Lex.nil List.Lex.nil
  | cons a s ih =>
    cases l' with
    | nil =>
      simp only [map_nil, map_cons]
      exact iff_of_false (by rintro ⟨⟩) $ by rintro ⟨⟩
    | cons b t =>
      simp only [map_cons, cons_lex_cons_iff]
      constructor
      rintro (h | ⟨h, h2⟩)
      exact m51 $ hf.lt_iff_lt.mp h
      exact m61 ⟨hf.injective h, mp_ (ih t) h2⟩
      rintro (h | ⟨rfl, h2⟩)
      exact m51 $ hf h
      simp_all
end

section
variable {n n' : ℕ} [DecidableEq (Fin n')] (ph_ : Fin n → Fin n') (hph : StrictMono ph_)
include hph
theorem sortedIndices_image_of_strictMono (J : FinSet n) :
    sortedIndices (J.image ph_) = (J.sort (· ≤ ·)).map fun j => ((ph_ j : Fin n') : ℕ) := by
  rw [sortedIndices_eq_map_sort, sort_image_of_strictMono ph_ hph J, List.map_map]
  rfl

theorem lex_sortedIndices_image_iff (J J' : FinSet n) :
    Lex (· < ·) (sortedIndices $ J.image ph_) (sortedIndices $ J'.image ph_) ↔
      Lex (· < ·) (sortedIndices J) (sortedIndices J') := by
  have h2 := lex_map_iff_of_strictMono val val_strictMono
    (J.sort (· ≤ ·)) (J'.sort (· ≤ ·))
  rw [sortedIndices_image_of_strictMono ph_ hph J, sortedIndices_image_of_strictMono ph_ hph J',
    sortedIndices_eq_map_sort, sortedIndices_eq_map_sort]
  exact (lex_map_iff_of_strictMono _ (fun a b h => val_strictMono $ hph h) (J.sort (· ≤ ·)) (J'.sort (· ≤ ·))).trans h2.symm
end

def reversedIndex (n : ℕ) (j : Fin n) : ℕ := n - 1 - (j : ℕ)

section
variable {n : ℕ}
theorem reversedIndex_lt_reversedIndex_iff (j j' : Fin n) :
    reversedIndex n j < reversedIndex n j' ↔ j' < j := by
  simp only [reversedIndex, lt_def]
  omega

theorem reversedIndex_injective : Function.Injective $ reversedIndex n := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have h' : n - 1 - a = n - 1 - b := h
  exact Fin.val_injective $ by omega

theorem binaryEncode_eq_sum_image (J : FinSet n) :
    _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J = ∑ e ∈ J.image (reversedIndex n), 2 ^ e := by
  rw [Finset.sum_image fun a _ b _ h => reversedIndex_injective h]
  rfl

theorem binaryEncode_lt_iff (J J' : FinSet n) :
    _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J' < _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J ↔
      (∃ a ∈ J, a ∉ J' ∧ ∀ b ∈ J', b ∉ J → a < b) := by
  simp [binaryEncode_eq_sum_image]
  rw [(geomSum_lt_geomSum_iff_toColex_lt_toColex $ le_refl 2).trans
    Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt]
  constructor
  rintro ⟨e, he, he', hmax⟩
  obtain ⟨a, haJ, rfl⟩ := mp mem_image he
  refine ⟨a, haJ, ?_, ?_⟩
  intro haJ'
  exact he' $ mem_image_of_mem _ haJ'
  intro b hb hbJ
  refine mp (reversedIndex_lt_reversedIndex_iff b a) $ hmax _ (mem_image_of_mem _ hb) ?_
  intro hmem
  obtain ⟨c, hc, hceq⟩ := Finset.mem_image.mp hmem
  rw [reversedIndex_injective hceq] at hc
  exact hbJ hc
  rintro ⟨a, haJ, haJ', hmin⟩
  refine ⟨reversedIndex n a, mem_image_of_mem _ haJ, ?_, ?_⟩
  intro hmem
  obtain ⟨c, hc, hceq⟩ := mp mem_image hmem
  rw [reversedIndex_injective hceq] at hc
  exact haJ' hc
  rintro f hf hfnot
  obtain ⟨b, hb, rfl⟩ := mp mem_image hf
  have hbJ := fun hbJ => hfnot $ mem_image_of_mem _ hbJ
  exact mpr (reversedIndex_lt_reversedIndex_iff b a) $ hmin b hb hbJ

theorem binaryEncode_injective :
    Function.Injective fun J : FinSet n => _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J := by
  intro J J' h
  have hJ := binaryEncode_eq_sum_image J
  have hJ' := binaryEncode_eq_sum_image J'
  have h1 : (∑ e ∈ J.image (reversedIndex n), 2 ^ e) = (∑ e ∈ J'.image (reversedIndex n), 2 ^ e) := by simp_all
  exact image_injective reversedIndex_injective $ geomSum_injective (le_refl 2) h1
end

theorem lex_iff_exists_min_mem {al_ : Type} [LinearOrder al_] :
    ∀ (L L' : List al_), length L = length L' → Pairwise (· < ·) L →
      Pairwise (· < ·) L' →
      (Lex (· < ·) L L' ↔ ∃ a ∈ L, a ∉ L' ∧ ∀ b ∈ L', b ∉ L → a < b) := by
  intro L
  induction L with
  | nil =>
    intro L' hlen _ _
    cases L' with
    | nil =>
      constructor
      intro h
      cases h
      simp_all
    | cons b t => simp at hlen
  | cons a s ih =>
    intro L' hlen hs hL'
    cases L' with
    | nil => simp at hlen
    | cons b t =>
      rw [pairwise_cons] at hs hL'
      have hlen' := by simpa using hlen
      rw [cons_lex_cons_iff]
      rcases lt_trichotomy a b with hab | hab | hab
      constructor
      intro _
      refine ⟨a, by simp, ?_, ?_⟩
      intro hmem
      rcases mem_cons.mp hmem with h | h
      rw [h] at hab
      exact absurd hab $ lt_irrefl b
      exact absurd (an1 hL' a h) $ mpr_ not_lt hab.le
      intro y hy _
      rcases mem_cons.mp hy with h | h
      rwa [h]
      exact lt_trans hab $ an1 hL' y h
      intro _
      exact m51 hab
      subst hab
      have ihst := ih t hlen' hs.2 hL'.2
      constructor
      rintro (h | ⟨-, h⟩)
      simp_all
      obtain ⟨x, hxs, hxt, hmin⟩ := mp_ ihst h
      refine ⟨x, mpr_ mem_cons $ m61 hxs, ?_, ?_⟩
      intro hx
      rcases mem_cons.mp hx with heq | hx
      rw [heq] at hxs
      exact absurd (an1 hs _ hxs) $ lt_irrefl _
      exact hxt hx
      intro y hy hyn
      rcases mem_cons.mp hy with heq | hy
      simp_all
      simp_all
      rintro ⟨x, hx, hxn, hmin⟩
      refine m61 ⟨rfl, mpr_ ihst ?_⟩
      have hxs : x ∈ s := by simp_all
      refine ⟨x, hxs, ?_, ?_⟩
      simp_all
      intro y hy hys
      refine hmin y (mpr_ mem_cons $ m61 hy) ?_
      intro hy'
      rcases mem_cons.mp hy' with h | h
      rw [h] at hy
      exact absurd (an1 hL' _ hy) $ lt_irrefl _
      exact hys h
      constructor
      rintro (h | ⟨h, -⟩)
      exact absurd h $ mpr_ not_lt hab.le
      rw [h] at hab
      exact absurd hab $ lt_irrefl b
      rintro ⟨x, hx, hxn, hmin⟩
      have hbs : b ∉ a :: s := by
        intro hb
        rcases mem_cons.mp hb with h | h
        rw [h] at hab
        exact absurd hab $ lt_irrefl a
        exact absurd (an1 hs b h) $ mpr_ not_lt hab.le
      refine absurd (hmin b (by simp) hbs) $ mpr_ not_lt $ le_trans hab.le ?_
      rcases mem_cons.mp hx with h | h
      exact le_of_eq h.symm
      exact le_of_lt $ an1 hs x h

theorem binaryEncode_lt_iff_lex_of_card_eq {n : ℕ} (J J' : FinSet n) (hcard : J.card = J'.card) :
    _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J' < _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J ↔
      Lex (· < ·) (sortedIndices J) (sortedIndices J') := by
  have hlen : lenL (J.sort (· ≤ ·)) = lenL (J'.sort (· ≤ ·)) := by simp_all
  have hmap := lex_map_iff_of_strictMono val val_strictMono
    (J.sort (· ≤ ·)) (J'.sort (· ≤ ·))
  have hfin : (∃ a ∈ J.sort (· ≤ ·), a ∉ J'.sort (· ≤ ·) ∧
      ∀ b ∈ J'.sort (· ≤ ·), b ∉ J.sort (· ≤ ·) → a < b) ↔
      (∃ a ∈ J, a ∉ J' ∧ ∀ b ∈ J', b ∉ J → a < b) := by
    simp [mem_sort]
  rw [sortedIndices_eq_map_sort, sortedIndices_eq_map_sort]
  exact (binaryEncode_lt_iff J J').trans (hfin.symm.trans ((lex_iff_exists_min_mem (J.sort (· ≤ ·)) (J'.sort (· ≤ ·)) hlen ((sortedLT_sort J).pairwise) $ (sortedLT_sort J').pairwise).symm.trans hmap.symm))

end MonomialCenter




namespace MonomialCenter

def IsMonomialNear {X : Sch} (E : Bdy X) (M : ISD X)
    (x : ↥X) : Prop :=
  ∃ U : Opn X, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
    comap M U.i =
      (ofFn fun i : Fin E.length => comap (get E i) U.i ^ a i).foldr (· * ·) ⊤

structure IsLocallyMonomialTriple (T : MarkedIdealWithBoundary) : Prop where
  valid : IsAdmissible T
  monomialNear : ∀ x ∈ orderAtLeastLocus T.ideal T.mult, IsMonomialNear T.boundary T.ideal x


end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
section

open scoped Classical


namespace FunctorialResolution.EmbeddedResolution

section

variable {X : Sch}

section
variable (E : Bdy X) (I : ISD X)
def monomialSplitting :
    IdealSheafData X × X.IdealSheafData :=
  if h : ∃ q : ISD X × X.IdealSheafData, IsMonomialSplitting E I q.1 q.2 then
    h.choose
  else (⊤, I)

def monomialPart : ISD X :=
  (monomialSplitting E I).1

def nonMonomialPart : ISD X :=
  (monomialSplitting E I).2

theorem isMonomialSplitting_monomialPart_nonMonomialPart
    (h : ∃ q : ISD X × X.IdealSheafData, IsMonomialSplitting E I q.1 q.2) :
    IsMonomialSplitting E I (monomialPart E I) $ nonMonomialPart E I := by
  unfold monomialPart nonMonomialPart monomialSplitting
  rw [dif_pos h]
  exact h.choose_spec
end

end

section

variable {X : Sch}

def maxOrder (N : ISD X) : ℕ :=
  sSup {n : ℕ | ∃ x : ↥X, (n : ENat) ≤ orderAt N x}

def maxOrderOn (N : ISD X) (S : Set ↥X) : ℕ :=
  sSup {n : ℕ | ∃ x ∈ S, (n : ENat) ≤ orderAt N x}

end

section

variable {k : Type} [Field k] {X : Sch} {p : X ⟶ Sp k}
  {I : ISD X} {m : ℕ} {E : Bdy X}

def markedDataOfSeq (s : MarkedBlowupSequenceData p I m E) (J : IdealSheafData (s.obj s.length)) (mu_ : ℕ)
    (t : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J mu_ $ s.boundary s.length) :
    Option $ MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m $ s.boundary s.length :=
  if h : (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).IsMarked (s.proj s.length ≫ p) (s.ideal s.length) m
      (s.boundary s.length) then
    some $ (BlowupSequenceData.ofSequenceOfBlowups t.toSequenceOfBlowups).toMarkedBlowupSequenceData (s.proj s.length ≫ p)
      (s.ideal s.length) m (s.boundary s.length) h
  else
    none

def appendIfMarked (hinv : ComapIsoInvariance) (s : MarkedBlowupSequenceData p I m E)
    (J : IdealSheafData $ s.obj s.length) (mu_ : ℕ)
    (t : MarkedSequenceOfBlowups (s.proj s.length ≫ p) J mu_ $ s.boundary s.length) :
    MarkedBlowupSequenceData p I m E :=
  match markedDataOfSeq s J mu_ t with
  | some d => s.append d hinv
  | none => s

end

section

def tripleAtLength (T : MarkedIdealWithBoundary)
    (s : T.mbs)
    (J : IdealSheafData $ s.obj s.length) (mu_ : ℕ) : MarkedIdealWithBoundary where
  base := T.base
  instField := T.instField
  scheme := s.obj s.length
  structMap := s.proj s.length ≫ structMap T
  ideal := J
  mult := mu_
  boundary := s.boundary s.length

def appendRecursivePrincipalization (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (rc : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s : T.mbs)
    (J : IdealSheafData $ s.obj s.length) (mu_ : ℕ) :
    T.mbs :=
  if h : (tripleAtLength T s J mu_).krullDimSucc ≤ T.krullDimSucc then
    appendIfMarked hinv s J mu_ $ rc (tripleAtLength T s J mu_) h
  else s

def nonMonomialOrderReductionIter (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (rc : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) :
    ℕ → T.mbs
  | 0 => T.embs
  | n + 1 =>
    if T.mult ≤
          maxOrder (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
            (nonMonomialOrderReductionIter hinv T rc n).length)
            ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length)) ∧
        (orderAtLeastLocus
            (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
              (nonMonomialOrderReductionIter hinv T rc n).length)
              ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length))
            (maxOrder $ nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
              (nonMonomialOrderReductionIter hinv T rc n).length)
              ((nonMonomialOrderReductionIter hinv T rc n).ideal
                (nonMonomialOrderReductionIter hinv T rc n).length))).Nonempty then
      appendRecursivePrincipalization hinv T rc (nonMonomialOrderReductionIter hinv T rc n)
        (nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
          (nonMonomialOrderReductionIter hinv T rc n).length)
          ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length))
        (maxOrder $ nonMonomialPart ((nonMonomialOrderReductionIter hinv T rc n).boundary
          (nonMonomialOrderReductionIter hinv T rc n).length)
          ((nonMonomialOrderReductionIter hinv T rc n).ideal (nonMonomialOrderReductionIter hinv T rc n).length))
    else nonMonomialOrderReductionIter hinv T rc n

def companionIdealReductionIter (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary)
    (rc : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s0_ : T.mbs) :
    ℕ → T.mbs
  | 0 => s0_
  | n + 1 =>
    if 1 ≤
        maxOrderOn
          (nonMonomialPart ((companionIdealReductionIter hinv T rc s0_ n).boundary
            (companionIdealReductionIter hinv T rc s0_ n).length)
            ((companionIdealReductionIter hinv T rc s0_ n).ideal (companionIdealReductionIter hinv T rc s0_ n).length))
          (orderAtLeastLocus ((companionIdealReductionIter hinv T rc s0_ n).ideal
            (companionIdealReductionIter hinv T rc s0_ n).length) T.mult) then
      appendRecursivePrincipalization hinv T rc (companionIdealReductionIter hinv T rc s0_ n)
        (nonMonomialPart ((companionIdealReductionIter hinv T rc s0_ n).boundary
            (companionIdealReductionIter hinv T rc s0_ n).length)
            ((companionIdealReductionIter hinv T rc s0_ n).ideal (companionIdealReductionIter hinv T rc s0_ n).length) ^ T.mult ⊔
          (companionIdealReductionIter hinv T rc s0_ n).ideal (companionIdealReductionIter hinv T rc s0_ n).length ^
            maxOrderOn
              (nonMonomialPart ((companionIdealReductionIter hinv T rc s0_ n).boundary
                (companionIdealReductionIter hinv T rc s0_ n).length)
                ((companionIdealReductionIter hinv T rc s0_ n).ideal (companionIdealReductionIter hinv T rc s0_ n).length))
              (orderAtLeastLocus ((companionIdealReductionIter hinv T rc s0_ n).ideal
                (companionIdealReductionIter hinv T rc s0_ n).length) T.mult))
        (T.mult *
          maxOrderOn
            (nonMonomialPart ((companionIdealReductionIter hinv T rc s0_ n).boundary
              (companionIdealReductionIter hinv T rc s0_ n).length)
              ((companionIdealReductionIter hinv T rc s0_ n).ideal (companionIdealReductionIter hinv T rc s0_ n).length))
            (orderAtLeastLocus ((companionIdealReductionIter hinv T rc s0_ n).ideal
              (companionIdealReductionIter hinv T rc s0_ n).length) T.mult))
    else companionIdealReductionIter hinv T rc s0_ n

section
variable (hinv : ComapIsoInvariance) (T : MarkedIdealWithBoundary) (rc : ∀ S : MarkedIdealWithBoundary, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
def nonMonomialOrderReduction :
    T.mbs :=
  nonMonomialOrderReductionIter hinv T rc $ maxOrder (nonMonomialPart T.boundary T.ideal) + 1

def companionIdealReduction :
    T.mbs :=
  companionIdealReductionIter hinv T rc (nonMonomialOrderReduction hinv T rc)
    (maxOrderOn
      (nonMonomialPart ((nonMonomialOrderReduction hinv T rc).boundary (nonMonomialOrderReduction hinv T rc).length)
        ((nonMonomialOrderReduction hinv T rc).ideal (nonMonomialOrderReduction hinv T rc).length))
      (orderAtLeastLocus ((nonMonomialOrderReduction hinv T rc).ideal (nonMonomialOrderReduction hinv T rc).length) T.mult) + 1)

def orderReductionData :
    T.mbs :=
  (companionIdealReduction hinv T rc).append
    (ofMarkedSequence
      (monomialPrincipalization hinv
        (tripleAtLength T (companionIdealReduction hinv T rc)
          ((companionIdealReduction hinv T rc).ideal (companionIdealReduction hinv T rc).length) T.mult)))
    hinv

def orderReductionSeq : T.SequenceOfBlowups :=
  if orderAtLeastLocus T.ideal T.mult = ∅ then
    emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else
    toMarkedSequenceOfBlowups $ orderReductionData hinv T rc
end

end

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

section

variable {X : Sch}

section
variable (N : ISD X) {B : ℕ}
section
variable (hB : ∀ x : ↥X, orderAt N x ≤ (B : ENat))
include hB
theorem bddAbove_setOf_le_orderAt :
    BddAbove {n : ℕ | ∃ x : ↥X, (n : ENat) ≤ orderAt N x} := by
  refine ⟨B, ?_⟩
  intro n hn
  obtain ⟨x, hx⟩ := hn
  exact_mod_cast (le_trans hx $ hB x)

theorem orderAt_le_maxOrder (x : ↥X) :
    orderAt N x ≤ ((maxOrder N : ℕ) : ENat) := by
  have hxB := hB x
  have hBtop : (B : ENat) ≠ ⊤ := by simp
  have hne : orderAt N x ≠ ⊤ := by
    intro h
    rw [h] at hxB
    exact hBtop $ mp_ top_le_iff hxB
  obtain ⟨m, hm⟩ := mp ne_top_iff_exists hne
  rw [← hm]
  exact_mod_cast (le_csSup (bddAbove_setOf_le_orderAt N hB) ⟨x, hm.le⟩)

theorem orderAt_lt_of_maxOrder_lt {c : ℕ} (hc : maxOrder N < c) (x : ↥X) :
    orderAt N x < (c : ENat) := by
  refine lt_of_le_of_lt (orderAt_le_maxOrder N hB x) ?_
  exact_mod_cast hc
end

theorem maxOrder_lt_of_orderAtLeastLocus_eq_empty
    (_hB : ∀ x : ↥X, orderAt N x ≤ (B : ENat)) {c : ℕ} (hc : 1 ≤ c)
    (h : orderAtLeastLocus N c = ∅) :
    maxOrder N < c := by
  have key : maxOrder N ≤ c - 1 := by
    refine csSup_le' ?_
    intro n hn
    obtain ⟨x, hx⟩ := hn
    have hlt : ¬ (c ≤ orderAt N x) := by
      intro hcon
      have hmem := mpr_ (mem_orderAtLeastLocus_iff N c x) hcon
      rw [h] at hmem
      simp at hmem
    have hnc : n < c := by
      by_contra hcon
      have hcast : (c : ENat) ≤ (n : ENat) := by exact_mod_cast (le_of_not_lt hcon)
      exact hlt $ le_trans hcast hx
    omega
  omega
end

section
variable [hv0_0 : Nonempty ↥X] (N : ISD X) {B : ℕ} (hB : ∀ x : ↥X, orderAt N x ≤ (B : ENat))
include hv0_0 hB
theorem exists_orderAt_eq_maxOrder :
    ∃ x : ↥X, orderAt N x = ((maxOrder N : ℕ) : ENat) := by
  have hbdd := bddAbove_setOf_le_orderAt N hB
  have hnonempty : {n : ℕ | ∃ x, n ≤ orderAt N x}.Nonempty := by
    obtain ⟨x0_⟩ := ‹Nonempty ↥X›
    exact ⟨0, x0_, by simp⟩
  obtain ⟨x, hx⟩ := sSup_mem hnonempty hbdd
  have hdef : maxOrder N = sSup {n : ℕ | ∃ x, n ≤ orderAt N x} := rfl
  refine ⟨x, ?_⟩
  rw [hdef]
  refine le_antisymm ?_ hx
  have hordle := hB x
  have hne_top : orderAt N x ≠ ⊤ := by
    intro h
    rw [h] at hordle
    simp at hordle
  obtain ⟨n, hn⟩ := mp_ ne_top_iff_exists hne_top
  calc orderAt N x = n := sy_ hn
    _ ≤ ((sSup {n : ℕ | ∃ x, n ≤ orderAt N x} : ℕ) : ENat) := by exact_mod_cast (le_csSup hbdd ⟨x, le_of_eq hn⟩)

theorem orderAtLeastLocus_maxOrder_nonempty :
    (orderAtLeastLocus N $ maxOrder N).Nonempty := by
  obtain ⟨x, hx⟩ := exists_orderAt_eq_maxOrder N hB
  exact ⟨x, mpr_ (mem_orderAtLeastLocus_iff N (maxOrder N) x) hx.ge⟩
end

end

section

variable {X : Sch}

section
variable (N : ISD X) {B : ℕ}
section
variable (hB : ∀ x : ↥X, orderAt N x ≤ (B : ENat)) (S : Set ↥X)
include hB
theorem bddAbove_setOf_le_orderAt_of_mem :
    BddAbove {n : ℕ | ∃ x ∈ S, (n : ENat) ≤ orderAt N x} := by
  refine ⟨B, ?_⟩
  intro n hn
  obtain ⟨x, _, hx⟩ := hn
  exact_mod_cast (le_trans hx $ hB x)

theorem orderAt_le_maxOrderOn {x : ↥X} (hx : x ∈ S) :
    orderAt N x ≤ ((maxOrderOn N S : ℕ) : ENat) := by
  have hxB := hB x
  have hne : orderAt N x ≠ ⊤ := by
    intro h
    rw [h] at hxB
    simp at hxB
  obtain ⟨m, hm⟩ := mp ne_top_iff_exists hne
  rw [← hm]
  exact_mod_cast (le_csSup (bddAbove_setOf_le_orderAt_of_mem N hB S) ⟨x, hx, hm.le⟩)

theorem maxOrderOn_eq_zero_iff :
    maxOrderOn N S = 0 ↔ ∀ x ∈ S, orderAt N x = 0 := by
  constructor
  intro h x hx
  have h1 :=
    orderAt_le_maxOrderOn N hB S hx
  rw [h] at h1
  refine mp_ nonpos_iff_eq_zero ?_
  exact_mod_cast h1
  intro h
  have hub : 0 ∈ upperBounds {n : ℕ | ∃ x ∈ S, n ≤ orderAt N x} := by
    intro n hn
    obtain ⟨x, hxS, hx⟩ := hn
    rw [h x hxS] at hx
    have hn1 : n = 0 := by exact_mod_cast (mp_ nonpos_iff_eq_zero hx)
    omega
  have key : maxOrderOn N S ≤ 0 := by
    exact csSup_le' hub
  omega
end

theorem maxOrderOn_lt_of_forall_lt
    (_hB : ∀ x : ↥X, orderAt N x ≤ (B : ENat)) (S : Set ↥X) {c : ℕ} (hc : 1 ≤ c)
    (h : ∀ x ∈ S, orderAt N x < (c : ENat)) :
    maxOrderOn N S < c := by
  have key : maxOrderOn N S ≤ c - 1 := by
    refine csSup_le' ?_
    intro n hn
    obtain ⟨x, hxS, hx⟩ := hn
    have hnc : n < c := by exact_mod_cast (lt_of_le_of_lt hx $ h x hxS)
    omega
  omega
end

end

section

variable {X : Sch}

theorem orderAtLeastLocus_sup (A J : ISD X) (c : ℕ) :
    orderAtLeastLocus (A ⊔ J) c = orderAtLeastLocus A c ∩ orderAtLeastLocus J c := by
  ext x
  simp [mem_inter_iff, mem_orderAtLeastLocus_iff, orderAt_sup]

section
variable (k : Type) [Field k] [CharZero k] (p : X ⟶ Sp k) [Smooth p] (N I : ISD X)
include p
theorem orderAt_pow_sup_pow (m s : ℕ) (x : ↥X) :
    orderAt (N ^ m ⊔ I ^ s) x
      = min ((m : ENat) * orderAt N x) ((s : ENat) * orderAt I x) := by
  rw [orderAt_sup, orderAt_pow k p, orderAt_pow k p]

theorem orderAt_pow_sup_pow_le (m s : ℕ)
    (h : ∀ x ∈ orderAtLeastLocus I m, orderAt N x ≤ (s : ENat)) (x : ↥X) :
    orderAt (N ^ m ⊔ I ^ s) x ≤ ((m * s : ℕ) : ENat) := by
  rw [orderAt_pow_sup_pow k p N I m s x]
  by_cases hx : x ∈ orderAtLeastLocus I m
  refine le_trans (min_le_left _ _) ?_
  have h1 := h x hx
  calc (m : ENat) * orderAt N x ≤ (m : ENat) * (s : ENat) := by gcongr
    _ = ((m * s : ℕ) : ENat) := by rw [cast_mul]
  refine le_trans (min_le_right _ _) ?_
  have hle :=
    le_of_lt $ mp_ not_le fun hc => hx $ mpr_ (mem_orderAtLeastLocus_iff I m x) hc
  calc (s : ENat) * orderAt I x ≤ (s : ENat) * (m : ENat) := by gcongr
    _ = ((m * s : ℕ) : ENat) := by rw [cast_mul]
                                   exact mul_comm _ _

section
variable {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s)
include hm hs
theorem orderAtLeastLocus_pow_sup_pow :
    orderAtLeastLocus (N ^ m ⊔ I ^ s) (m * s) = orderAtLeastLocus N s ∩ orderAtLeastLocus I m := by
  rw [orderAtLeastLocus_sup, orderAtLeastLocus_pow_mul k p N hm s, mul_comm m s,
    orderAtLeastLocus_pow_mul k p I hs m]

theorem orderAtLeastLocus_pow_sup_pow_eq_empty_iff :
    orderAtLeastLocus (N ^ m ⊔ I ^ s) (m * s) = ∅ ↔ ∀ x ∈ orderAtLeastLocus I m, orderAt N x < (s : ENat) := by
  rw [orderAtLeastLocus_pow_sup_pow k p N I hm hs]
  constructor
  intro h x hx
  by_contra hcon
  have hmem : x ∈ orderAtLeastLocus N s ∩ orderAtLeastLocus I m :=
    ⟨mpr_ (mem_orderAtLeastLocus_iff N s x) $ mp_ not_lt hcon, hx⟩
  rw [h] at hmem
  exact hmem.elim
  intro h
  ext x
  constructor
  intro hx
  exact absurd (mp_ (mem_orderAtLeastLocus_iff N s x) hx.1) $ mpr_ not_le $ h x hx.2
  intro hx
  exact hx.elim
end
end

end

section

variable {X Y : Sch}

theorem image_orderAtLeastLocus_comap_subset (k : Type) [Field k] [CharZero k]
    (p : X ⟶ Sp k) [Smooth p]
    (h : Y ⟶ X) [Smooth h] (N : ISD X) (c : ℕ) :
    ⇑h.base '' orderAtLeastLocus (comap N h) c ⊆ orderAtLeastLocus N c := by
  rw [orderAtLeastLocus_comap k p h N c]
  exact image_preimage_subset _ _

end

end FunctorialResolution.EmbeddedResolution

end
end
-- BEGIN_E2_PROJ_Bundle04
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
abbrev p18 := @BlowupSequenceData.prepend
abbrev p19 := @DivisorReduction.lowerIdealWithoutBlowup
abbrev p20 := @DivisorReduction.lowerBoundaryWithoutBlowup
abbrev p21 := @DivisorReduction.lI
abbrev p22 := @MarkedBlowupSequenceData.monomialBlowupIterate
abbrev p28 := @DivisorReduction.ccI
abbrev p34 := @FunctorialResolution.Blowup.blowup.proj
abbrev p37 := @DivisorReduction.lB
abbrev p39 := @FunctorialResolution.Blowup.comap_eq_top_of_notMem_support
abbrev p40 := @BlowupSequenceData.append_schemeAt_of_le_length
abbrev p41 := @MarkedBlowupSequenceData.blowupAtCenter
abbrev p44 := @DivisorReduction.containedComponentsIdeal
abbrev p46 := @FunctorialResolution.Blowup.blowup.isBlowupAlongIdealSheaf_proj
abbrev p47 := @FunctorialResolution.Blowup.sectionsRingHom
abbrev p52 := @BlowupSequenceData.boundary_succ
abbrev p53 := @BlowupSequenceData.controlledTransform_zero
end
-- END_E2_PROJ_Bundle04
