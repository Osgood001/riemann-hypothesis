import Mathlib
import Bundle00
import Bundle01
import Bundle02
import Bundle03
import Bundle04
import Bundle05
noncomputable section
open CategoryTheory AlgebraicGeometry
open FunctorialResolution.Blowup (IsBlowupAlongIdealSheaf IsLocallyGeneratedByNonZeroDivisor StrictTransformIsBlowupOfClosedSubscheme affineBlowup affineBlowupChart affineBlowupChart_comp_toSpec algebraMap_chart_eq_chartRingHom blowupIsIsoOffCenter blowupIsProper chartFraction chartRingHom chartRingHom_coe_eq_chartFraction_mul chartRingHom_mem_nonZeroDivisors exceptionalIdeal exists_mul_pow_eq_chartRingHom iSup_proj_basicOpen_reesGenerator_eq_top instIsOpenImmersionAffineBlowupChart isBlowupAlongIdealSheaf_affineBlowup_toSpec map_mem_nonZeroDivisors_of_iso opensRange_affineBlowupChart_eq_basicOpen reesAlgebraLift reesAlgebraLift_algebraMap reesAlgebraLift_reesGenerator reesDegreeZeroEquiv reesDegreeZeroEquiv_coe_coe reesGenerator reesGenerator_coe reesGrading specIdealSheaf specIdealSheaf_eq_ofIdealTop)
open Finset (coe_singleton filter le_sup mem_erase mem_map mem_of_mem_erase mem_singleton mul_sum prod_insert sum_congr sum_eq_single_of_mem sum_eq_zero sum_insert univ)
open TopologicalSpace.Opens (isBasis_iff_nbhd mem_iSup)
open Scheme.IdealSheafData (comap_comp comap_id comap_ideal_eq_map_appLE comap_ideal_eq_span_image comap_ideal_top_eq_map_appTop comap_mono comap_mul comap_ofIdealTop comap_pow comap_top comap_ι_eq_top_iff_ideal_eq_top equivOfIsAffine ideal_mul ideal_pow ideal_top ker_subschemeι le_def le_map_iff_comap_le le_ofIdeals_iff map_ideal_basicOpen mul_top notMem_support_of_comap_ι_eq_top ofIdealTop_ideal_top ofIdeals range_subschemeι subscheme subschemeι subschemeι_app support support_eq_bot_iff support_top)
open Ideal (comap_isPrime comap_map_of_surjective eq_top_iff_one exists_le_maximal map_comap_of_surjective map_le_iff_le_comap map_map map_mono map_span mem_comap mem_map_iff_of_surjective mem_map_of_mem mem_span_singleton mem_span_singleton' mem_span_singleton_mul mem_span_singleton_self mk_ker mul_le mul_mem_left mul_mem_mul mul_mem_right mul_mono ne_top_iff_one pow_mem_pow pow_right_mono quotEquivOfEq quotEquivOfEq_mk span span_le span_singleton_pow subset_span)
open Set (disjoint_left image_comp image_congr image_preimage_eq_inter_range image_singleton inter_eq_self_of_subset_left mem_image_of_mem mem_range_self preimage range range_comp singleton_subset_iff)
open MvPolynomial (aeval aeval_X aeval_def algebraMap_eq coeff_monomial coeff_sum constantCoeff eval₂ eval₂Hom eval₂Hom_C eval₂Hom_X' eval₂_X eval₂_add eval₂_mul eval₂_rename induction_on ker_map mapEquiv map_C map_X map_surjective mem_map_C_iff monomial monomial_eq pderiv pderiv_X_self pderiv_map pderiv_mul pderiv_rename rename rename_rename ringHom_ext)
open Nat (card card_le_card_of_injective exists_eq_add_of_le find find_le find_min find_spec le_induction le_succ lt_succ_self not_lt_zero sub_add_cancel succ_le_of_lt succ_pos zero_le)
open Submodule (mem_colon mem_of_span_eq_top_of_smul_pow_mem mem_span_set mem_span_set' mem_top mkQ_apply span_induction)
open IsAffineOpen (exists_basicOpen_le fromSpec fromSpec_preimage_basicOpen range_fromSpec self_le_iSup_basicOpen_iff)
open Finsupp (induction_linear prod_add_index' prod_single_index single sum_add_index' sum_single_index)
open RingHom (IsStandardSmoothOfRelativeDimension algebraMap_toAlgebra coe_coe coe_comp comp_apply congr_fun id_apply injective_iff_ker_eq_bot isStandardSmoothOfRelativeDimension_algebraMap isStandardSmoothOfRelativeDimension_localizationPreserves isStandardSmoothOfRelativeDimension_respectsIso isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway ker mapMatrix_apply map_det mem_ker)
open Scheme.Opens (range_ι toScheme topIso topIso_hom ι ι_appTop ι_preimage_self)
open Equiv (self_comp_symm ulift)
open Matrix (det det_one det_submatrix_equiv_self fromBlocks map_apply of_apply one_apply_eq one_apply_ne submatrix_apply)
open Limits (PushoutCocone)
open Classical (decEq)
open LinearMap (lTensor lTensor_tmul lsmul lsmul_apply mulLeft mulLeft_apply mulRight mulRight_apply rTensor_tmul)
open IsLocalization (eq_iff_exists lift_eq map_units mem_map_algebraMap_iff mk'_one nonZeroDivisors_le_comap surj)
open Scheme (GSpecIso IdealSheafData basicOpen_of_isUnit basicOpen_pow basicOpen_res hom_inv_apply inv_hom_apply isoSpec_hom isoSpec_hom_naturality preimage_basicOpen)
open TensorProduct (lid lid_tmul rid smul_tmul sum_tmul tmul_zero)
open FunctorialResolution.EmbeddedResolution.EtaleChart (coordIdeal_eq_comap_coordSubspaceIdeal coordRingHom_C coord_def coord_restrict ideal_eq_span_coord restrictToSubscheme_coord restrictToSubscheme_coordIdeal_singleton restrict_map)
open Sum (elim elim_inr inl inl_injective inr)
open Iso (eq_comp_inv hom hom_inv_id_apply hom_inv_id_assoc inv inv_hom_id_assoc refl symm_hom trans_hom)
open RingEquiv (apply_symm_apply ofBijective symm_apply_apply symm_symm toRingHom_eq_coe)
open IsPullback (of_horiz_isIso of_iso_pullback of_right of_vert_isIso)
open Function (Bijective Exact Injective LeftInverse Surjective)
open PrimeSpectrum (asIdeal basicOpen le_iff_mem_closure)
open List (getElem_cons_succ getElem_cons_zero length length_cons mem_iff_getElem)
open Scheme.Hom (appIso_hom' appLE appLE_congr_hom appLE_eq_app appLE_map appTop comp_appTop flat_appLE ideal_ker_le ker_comp le_ker_comp map_appLE opensRange pre resLE_comp_ι resLE_eq_morphismRestrict)
open Ideal.Quotient (eq_zero_iff_mem lift lift_mk mk_surjective)
open Category (assoc comp_id id_comp)
open ULift (down ext_iff up)
open CommRingCat (hom_comp hom_ext hom_id hom_ofHom ofHom ofHom_comp)
open Submonoid (powers)
open IsClosedImmersion (isAffine_surjective_of_isAffine lift_fac spec_of_surjective)
open HomogeneousLocalization (Away val)
open Spec (map_comp map_id)
open LocallyOfFiniteType (isLocallyNoetherian)
open Quiver.Hom (unop_inj)
open IsOpenImmersion (isoOfRangeEq isoOfRangeEq_hom_fac)
open IsScalarTower (of_algebraMap_eq toAlgHom)
open SetLike (mem_coe)
open Algebra (smul_def)
section
open TopologicalSpace
open FunctorialResolution.EmbeddedResolution (exists_lift_of_isStandardSmoothOfRelativeDimension quasiCompact_strictTransformio_of_isLocallyNoetherian)
open Eq (symm)
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups (center projectionToBase schemeAt transitionMap transitionMapSucc)


namespace FunctorialResolution.EmbeddedResolution

section
variable (k : Type) [Field k] (M n q) (F : Fin q → ↑((affineSpaceIndexedBy k (UFS M n)).presheaf.obj (Opposite.op ⊤))) (D : (affineSpaceIndexedBy k (UFS M n)).Opens)
def graphMorphismToAffineSpace :
    toScheme D ⟶ affineSpaceIndexedBy k (UFS M q) :=
  AffineSpace.homOfVector
    (ι D ≫ affineSpaceIndexedByToSpec k (UFS M n))
    (fun i =>
      elim
        (fun a : Fin M =>
          (ConcreteCategory.hom $ appTop D.i)
            (AffineSpace.coord (Sp k)
              (up (inl a) : UFS M n)))
        (fun j : Fin q => (ConcreteCategory.hom $ appTop D.i) $ F j)
        i.down)


theorem graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec :
    graphMorphismToAffineSpace k M n q F D ≫ affineSpaceIndexedByToSpec k (UFS M q) =
      ι D ≫ affineSpaceIndexedByToSpec k (UFS M n) := by
  simp [graphMorphismToAffineSpace]

theorem graphMorphismToAffineSpace_appTop_coord_inl (a : Fin M) :
    (ConcreteCategory.hom $ appTop $ graphMorphismToAffineSpace k M n q F D)
        (AffineSpace.coord (Sp k)
          (up (inl a) : UFS M q)) =
      (ConcreteCategory.hom $ appTop D.i)
        (AffineSpace.coord (Sp k)
          (up (inl a) : UFS M n)) := by
  simp [graphMorphismToAffineSpace]

theorem graphMorphismToAffineSpace_appTop_coord_inr (j : Fin q) :
    (ConcreteCategory.hom $ appTop $ graphMorphismToAffineSpace k M n q F D)
        (AffineSpace.coord (Sp k)
          (up (inr j) : UFS M q)) =
      (ConcreteCategory.hom $ appTop D.i) (F j) := by
  simp [graphMorphismToAffineSpace]
end

def SmoothPullbackHasGraphChart : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X Y A : Sch)
    (pX : X ⟶ Sp k) (pY : Y ⟶ Sp k)
    (pA : A ⟶ Sp k) [IsAffine A] [Smooth pA]
    [LocallyOfFiniteType pA] [QuasiCompact pA]
    (i : X ⟶ A) [IsClosedImmersion i], i ≫ pA = pX →
    ∀ (M : ℕ) (rh_ : A ⟶ affineSpaceIndexedBy k (UFin M)) [IsClosedImmersion rh_],
      rh_ ≫ affineSpaceIndexedByToSpec k (UFin M) = pA →
    ∀ (r : ℕ) (h : Y ⟶ X) [SmoothOfRelativeDimension r h], h ≫ pX = pY →
    ∀ y : Y,
      ∃ (V : Opn Y) (_ : y ∈ V) (_ : IsAffineOpen V)
        (A' : Sch) (pA' : A' ⟶ Sp k),
        IsAffine A' ∧ Smooth pA' ∧ LocallyOfFiniteType pA' ∧ QuasiCompact pA' ∧
        ∃ g : A' ⟶ A, Smooth g ∧ g ≫ pA = pA' ∧
          ∃ j : toScheme V ⟶ A', IsClosedImmersion j ∧
            IsPullback j (ι V ≫ h) g i ∧
            ∃ (n q : ℕ), n = q + r ∧
              ∃ σ : A' ⟶ affineSpaceIndexedBy k (UFS M n),
                IsClosedImmersion σ ∧
                σ ≫ projLeft k M n = g ≫ rh_ ∧
                ∃ (F : Fin q →
                    ↑((affineSpaceIndexedBy k $ UFS M n).presheaf.obj
                      (Opposite.op ⊤)))
                  (De_ : ↑((affineSpaceIndexedBy k $ UFS M n).presheaf.obj
                      (Opposite.op ⊤))),
                  ker (CommRingCat.Hom.hom $ appTop σ) =
                      Ideal.map (CommRingCat.Hom.hom $ appTop $ projLeft k M n)
                        (ker $ CommRingCat.Hom.hom $ appTop rh_) ⊔
                      span (range F) ∧
                  σ ⁻¹ᵁ ((affineSpaceIndexedBy k $ UFS M n).basicOpen De_) = ⊤ ∧
                  Smooth (graphMorphismToAffineSpace k M n q F
                    ((affineSpaceIndexedBy k $ UFS M n).basicOpen De_))





section
variable (k : Type) [Field k] (M n q) (F : Fin q → ↑((affineSpaceIndexedBy k (UFS M n)).presheaf.obj (Opposite.op ⊤))) (j : Fin q)
def polynomialOfSection : MvPolynomial (UFS M n) k :=
  (mvPolynomialEquivGlobalSections k $ UFS M n).symm $ F j

theorem mvPolynomialEquivGlobalSections_polynomialOfSection :
    mvPolynomialEquivGlobalSections k (UFS M n) (polynomialOfSection k M n q F j) = F j :=
  (mvPolynomialEquivGlobalSections k $ UFS M n).apply_symm_apply $ F j
end

section
variable (M n q : ℕ) (s : Fin q → Fin n)
def sumVariableMap :
    UFS M q → UFS M n :=
  fun i =>
    up $ elim (fun a : Fin M => inl a) (fun j : Fin q => inr $ s j) i.down

end

section
variable (k : Type) [Field k] (M n q) (F : Fin q → ↑((affineSpaceIndexedBy k (UFS M n)).presheaf.obj (Opposite.op ⊤)))
section
variable (s : Fin q → Fin n)
def jacobianMatrixOfSections :
    Matrix (Fin q) (Fin q) $ MvPolynomial (UFS M n) k :=
  Matrix.of fun i j =>
    (pderiv (up (inr $ s i) : UFS M n))
      (polynomialOfSection k M n q F j)

theorem jacobianMatrixOfSections_apply (i j : Fin q) :
    jacobianMatrixOfSections k M n q F s i j =
      (pderiv (up (inr $ s i) : UFS M n))
        (polynomialOfSection k M n q F j) := rfl
end

def graphCoordinates :
    UFS M q → MvPolynomial (UFS M n) k :=
  fun i =>
    elim
      (fun a : Fin M => MvPolynomial.X (up (inl a) : UFS M n))
      (fun j : Fin q => polynomialOfSection k M n q F j) i.down

theorem graphCoordinates_inl
    (a : Fin M) :
    graphCoordinates k M n q F (up $ inl a) =
      MvPolynomial.X (up (inl a) : UFS M n) := rfl

theorem graphCoordinates_inr
    (j : Fin q) :
    graphCoordinates k M n q F (up $ inr j) = polynomialOfSection k M n q F j := rfl

section
variable (s : Fin q → Fin n)
theorem graphJacobianMinorDet_graphCoordinates :
    graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap M n q s) =
      graphAlgebraEquiv (graphCoordinates k M n q F) (jacobianMatrixOfSections k M n q F s).det := by
  let _a3 := jacobianMatrixOfSections k M n q F s
  let _a4 := sumVariableMap M n q s
  let _a5 := graphCoordinates k M n q F
  have h := by
    let _a0 := UFS M n
    have hup : ∀ x y : Fin M ⊕ Fin n,
        (up x) = up y → x = y :=
      fun _ _ h => congrArg down h
    have hXne : ∀ i j : _a0, i ≠ j →
        (pderiv i)
            (m7 j : MvPolynomial _a0 k) = 0 := by simp_all
    let _a1 := graphJacobianMinorMatrix _a5 _a4
    have key :
        _a1.submatrix
            (ulift.symm : (Fin M ⊕ Fin q) ≃ UFS M q)
            (ulift.symm : (Fin M ⊕ Fin q) ≃ UFS M q) =
          fromBlocks
            1
            (m53 fun a j =>
              (pderiv (up (m44 a) : _a0))
                (polynomialOfSection k M n q F j))
            0 _a3 := by
      apply Matrix.ext
      intro x y
      simp [submatrix_apply]
      cases x with
      | inl a =>
        cases y with
        | inl b =>
          show (pderiv (up (m44 a) : _a0))
                (m7 (up (m44 b) : _a0)) =
              (1 : (Matrix (Fin M) (Fin M) $ MvPolynomial _a0 k)) a b
          by_cases h : a = b
          subst h
          rw [pderiv_X_self, one_apply_eq]
          rw [one_apply_ne h]
          exact hXne _ _ fun hc => h $ inl_injective $ hup _ _ hc
        | inr j => rfl
      | inr i =>
        cases y with
        | inl b =>
          show (pderiv (up (m50 $ s i) : _a0))
                (m7 (up (m44 b) : _a0)) = 0
          refine hXne _ _ ?_
          intro hc
          have hc' := hup _ _ hc
          simp at hc'
        | inr j => rfl
    have hdet := det_submatrix_equiv_self
        (ulift.symm : (Fin M ⊕ Fin q) ≃ UFS M q)
        _a1
    rw [key, Matrix.det_fromBlocks_zero₂₁, det_one, one_mul] at hdet
    exact sy_ hdet
  let _a0 := _a5
  show graphAlgebraEquiv _a0
      (graphJacobianMinorMatrix _a0 _a4).det =
    graphAlgebraEquiv _a0 _a3.det
  rw [h]

def jacobianDetSection :
    ↑((affineSpaceIndexedBy k $ UFS M n).presheaf.obj $ Opposite.op ⊤) :=
  mvPolynomialEquivGlobalSections k (UFS M n) (jacobianMatrixOfSections k M n q F s).det

def specGraphAwayToSpecGraphAlgebra :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) $ sumVariableMap M n q s)) ⟶
      Spec (CommRingCat.of (GraphAlgebra $ graphCoordinates k M n q F)) :=
  Spec.map $ ofHom
    (algebraMap (GraphAlgebra $ graphCoordinates k M n q F)
      (GraphAlgebraAway (graphCoordinates k M n q F) $ sumVariableMap M n q s))
end
end

instance instIsOpenImmersionGraphAwaySpecHom (k : Type) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k $ UFS M n).presheaf.obj $ Opposite.op ⊤))
    (s : Fin q → Fin n) :
    IsOpenImmersion $ specGraphAwayToSpecGraphAlgebra k M n q F s :=
  by
  unfold specGraphAwayToSpecGraphAlgebra
  infer_instance

def basicOpenToSpecGraphAlgebra (k : Type) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k $ UFS M n).presheaf.obj $ Opposite.op ⊤))
    (s : Fin q → Fin n) :
    ((affineSpaceIndexedBy k $ UFS M n).basicOpen
        (jacobianDetSection k M n q F s)).toScheme ⟶
      Spec (CommRingCat.of (GraphAlgebra $ graphCoordinates k M n q F)) :=
  ((affineSpaceIndexedBy k $ UFS M n).basicOpen
      (jacobianDetSection k M n q F s)).ι ≫
    (affineSpaceIsoSpecMvPolynomial k $ UFS M n).hom ≫
      Spec.map (ofHom
        ((graphAlgebraEquiv $ graphCoordinates k M n q F).symm.toRingEquiv.toRingHom))

def specIsoOfRingEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Sp B ≅ Sp A :=
  Scheme.Spec.mapIso e.toCommRingCatIso.op

instance instIsOpenImmersionGraphChartHom (k : Type) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k $ UFS M n).presheaf.obj $ Opposite.op ⊤))
    (s : Fin q → Fin n) :
    IsOpenImmersion $ basicOpenToSpecGraphAlgebra k M n q F s :=
  by
  have : IsIso $ Spec.map $ ofHom
      ((graphAlgebraEquiv $ graphCoordinates k M n q F).symm.toRingEquiv.toRingHom) :=
    by
    let e := ((graphAlgebraEquiv $ graphCoordinates k M n q F).symm.toRingEquiv)
    refine ⟨(specIsoOfRingEquiv e).inv, ?_, ?_⟩
    · exact (specIsoOfRingEquiv e).hom_inv_id
    · exact (specIsoOfRingEquiv e).inv_hom_id
  unfold basicOpenToSpecGraphAlgebra
  infer_instance

section
variable {X Y Z : Sch}
section
variable (f : X ⟶ Y) (g : Y ⟶ Z)
private theorem base_comp_apply x :
    ⇑(f ≫ g).base x = ⇑g.base (⇑f.base x) := rfl

theorem image_base_comp S :
    ⇑(f ≫ g).base '' S = ⇑g.base '' (⇑f.base '' S) := by
  ext z
  constructor
  simp_all
  simp_all

private theorem range_base_comp :
    range ⇑(f ≫ g).base = ⇑g.base '' range ⇑f.base := by
  ext z
  constructor
  simp_all
  simp_all
end

private theorem appTop_comp_apply (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : ↑(Z.presheaf.obj $ Opposite.op ⊤)) :
    (appTop $ a ≫ b) x
      = (appTop a) ((appTop b) x) := rfl
end

section
variable (k : Type) [Field k] (M n q) (F : Fin q → ↑((affineSpaceIndexedBy k (UFS M n)).presheaf.obj (Opposite.op ⊤)))
def specGraphAwayToAffineSpace
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) $ sumVariableMap M n q s)) ⟶
      Spec (CommRingCat.of (MvPolynomial (UFS M q) k)) :=
  Spec.map $ ofHom
    (algebraMap (MvPolynomial (UFS M q) k)
      (GraphAlgebraAway (graphCoordinates k M n q F) $ sumVariableMap M n q s))

theorem graphAlgebraEquiv_symm_comp_algebraMap_comp_C :
    ((((graphAlgebraEquiv $ graphCoordinates k M n q F).symm.toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (UFS M q) k)
          (GraphAlgebra $ graphCoordinates k M n q F))).comp
        (MvPolynomial.C : k →+* MvPolynomial (UFS M q) k))
      = (MvPolynomial.C : k →+* MvPolynomial (UFS M n) k) := by
  ext c
  simp [algebraMap_graphAlgebra, algebraMap_eq]
end

section
variable {X Y : Sch} (e : X ≅ Y)
theorem image_hom_preimage_eq U :
    ⇑e.hom.base '' ((e.hom.pre U : Opn X) : Set ↥X) = (U : Set ↥Y) := by
  ext y
  constructor
  rintro ⟨x, hx, rfl⟩
  exact hx
  intro hy
  refine ⟨e.inv.base y, ?_, inv_hom_apply e y⟩
  show e.hom.base (e.inv.base y) ∈ U
  rwa [inv_hom_apply e y]

theorem image_hom_eq_preimage_inv U :
    ⇑e.hom.base '' ((U : Opn X) : Set ↥X) = ((e.inv.pre U : Opn Y) : Set ↥Y) := by
  ext y
  constructor
  rintro ⟨x, hx, rfl⟩
  show e.inv.base (e.hom.base x) ∈ opS U
  rwa [hom_inv_apply e x]
  intro hy
  exact ⟨e.inv.base y, hy, inv_hom_apply e y⟩
end

theorem image_basicOpen_spec_map_ringEquiv {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) a :
    ⇑(Spec.map $ ofHom e.toRingHom).base ''
        (basicOpen (e a) : Set $ PrimeSpectrum B)
      = (basicOpen a : Set $ PrimeSpectrum A) := by
  let _s0 := (basicOpen (e a) : Opens $ PrimeSpectrum B)
  let _a0 := isoI (GSpecIso $ m10 B) $ e a
  let _a7 := bOpn (Sp B) _a0
  have h2 : _s0
      = _a7 := by
    have h2' : _a7
        = _s0 :=
      basicOpen_eq_of_affine _
    exact sy_ h2'
  let _a1 := m12 $ ofHom e.symm.toRingHom
  let _a11 := (appTop _a1) _a0
  have h3 : m12 (ofHom e.symm.toRingHom) ⁻¹ᵁ
        _a7
      = bOpn (Sp A)
          _a11 :=
    preimage_basicOpen _a1 _
  let _a6 := GSpecIso $ m10 A
  have h4 : _a11
      = isoI _a6 ((e.symm.toRingHom) $ e a) :=
    (congr_fun (congrArg m4
      (Scheme.ΓSpecIso_inv_naturality $ ofHom e.symm.toRingHom)) $ e a).symm
  have h5 : (e.symm.toRingHom) (e a) = a := by simp
  have h6 : bOpn (Sp A)
          (isoI _a6 a)
      = (basicOpen a : Opens $ PrimeSpectrum A) :=
    basicOpen_eq_of_affine _
  have hop : (m12 (ofHom e.symm.toRingHom) ⁻¹ᵁ
        _s0)
      = (basicOpen a : Opens $ PrimeSpectrum A) := by
    rwa [h2, h3, h4, h5]
  exact tr_ (image_hom_eq_preimage_inv (specIsoOfRingEquiv e) $ basicOpen $ e a) $ congrArg (fun U : Opn (Sp A) =>
    opS U) hop

section
variable (k : Type) [Field k] (M n q) (F : Fin q → ↑((affineSpaceIndexedBy k (UFS M n)).presheaf.obj (Opposite.op ⊤))) (s : Fin q → Fin n)
theorem range_specGraphAwayToSpecGraphAlgebra_eq :
    range ⇑(specGraphAwayToSpecGraphAlgebra k M n q F s).base =
      range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base := by
  let _a0 := UFS M n
  let _a2 := jacobianDetSection k M n q F s
  let _a5 := affineSpaceIndexedBy k _a0
  let _a7 := affineSpaceIsoSpecMvPolynomial k _a0
  have hDopen : bOpn _a5
        _a2
      = isoH _a7 ⁻¹ᵁ
          (basicOpen (jacobianMatrixOfSections k M n q F s).det) :=
    mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum k _a0
      (jacobianMatrixOfSections k M n q F s).det
  let _a8 := PrimeSpectrum $ MvPolynomial _a0 k
  have himg1 : _a7.hom.base ''
        ((bOpn _a5
            _a2 :
          Opn _a5) :
          Set _a5)
      = (basicOpen (jacobianMatrixOfSections k M n q F s).det :
          Set _a8) := by
    rw [hDopen]
    exact image_hom_preimage_eq _a7
      (basicOpen (jacobianMatrixOfSections k M n q F s).det)
  have hdet : (jacobianMatrixOfSections k M n q F s).det
      = (graphAlgebraEquiv $ graphCoordinates k M n q F).symm.toRingEquiv
          (graphJacobianMinorDet (graphCoordinates k M n q F) $ sumVariableMap M n q s) := by
    rw [graphJacobianMinorDet_graphCoordinates]
    simp
  have himg2 : (m12 $ ofHom
        ((graphAlgebraEquiv $ graphCoordinates k M n q F).symm.toRingEquiv.toRingHom)).base ''
        (basicOpen (jacobianMatrixOfSections k M n q F s).det :
          Set _a8)
      = (basicOpen
            (graphJacobianMinorDet (graphCoordinates k M n q F) $ sumVariableMap M n q s) :
          Set $ PrimeSpectrum $ GraphAlgebra $ graphCoordinates k M n q F) := by
    rw [hdet]
    exact image_basicOpen_spec_map_ringEquiv ((graphAlgebraEquiv $ graphCoordinates k M n q F).symm.toRingEquiv)
      (graphJacobianMinorDet (graphCoordinates k M n q F) $ sumVariableMap M n q s)
  have hrange := himg2
  rw [← himg1, ← image_base_comp, ← (q1 _), ← range_base_comp (opI $ bOpn _a5 _a2) $ isoH _a7 ≫ m12 (ofHom $ (graphAlgebraEquiv $ graphCoordinates k M n q F).symm.toRingEquiv.toRingHom)] at hrange
  exact tr_ (range_specMap_algebraMap_graphAlgebraAway (graphCoordinates k M n q F) $ sumVariableMap M n q s) hrange.symm

def specGraphAwayIsoBasicOpen :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) $ sumVariableMap M n q s)) ≅
      ((affineSpaceIndexedBy k $ UFS M n).basicOpen
        (jacobianDetSection k M n q F s)).toScheme :=
  isoOfRangeEq (specGraphAwayToSpecGraphAlgebra k M n q F s) (basicOpenToSpecGraphAlgebra k M n q F s)
    (range_specGraphAwayToSpecGraphAlgebra_eq k M n q F s)

theorem specGraphAwayIsoBasicOpen_inv_comp :
    (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToSpecGraphAlgebra k M n q F s =
      basicOpenToSpecGraphAlgebra k M n q F s := IsOpenImmersion.isoOfRangeEq_inv_fac (specGraphAwayToSpecGraphAlgebra k M n q F s)
    (basicOpenToSpecGraphAlgebra k M n q F s) $ range_specGraphAwayToSpecGraphAlgebra_eq k M n q F s

theorem graphMorphismToAffineSpace_basicOpen_jacobianDetSection_eq :
    graphMorphismToAffineSpace k M n q F
        ((affineSpaceIndexedBy k $ UFS M n).basicOpen
          (jacobianDetSection k M n q F s)) =
      (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToAffineSpace k M n q F s ≫
        (affineSpaceIsoSpecMvPolynomial k $ UFS M q).inv := by
  let _c0 := UFS M q
  let _c1 := UFS M n
  let _c2 := graphCoordinates k M n q F
  let _c3 := jacobianDetSection k M n q F s
  let _c4 := Sp k
  have hgc : basicOpenToSpecGraphAlgebra k M n q F s =
      (bOpn (affineSpaceIndexedBy k _c1)
          _c3).ι ≫
        (affineSpaceIsoSpecMvPolynomial k _c1).hom ≫
          Spec.map (ofHom
            ((graphAlgebraEquiv _c2).symm.toRingEquiv.toRingHom)) := rfl
  have h1 : specGraphAwayToAffineSpace k M n q F s =
      specGraphAwayToSpecGraphAlgebra k M n q F s ≫
        Spec.map (ofHom
          (algebraMap (MvPolynomial _c0 k)
            (GraphAlgebra _c2))) :=
    specMap_algebraMap_graphAlgebraAway_eq_comp _c2 $ sumVariableMap M n q s
  have hre : ∀ {Z : Sch}
      (g : Spec (CommRingCat.of (GraphAlgebra _c2)) ⟶ Z),
      (specGraphAwayIsoBasicOpen k M n q F s).inv ≫ specGraphAwayToSpecGraphAlgebra k M n q F s ≫ g
        = basicOpenToSpecGraphAlgebra k M n q F s ≫ g := by
    intro Z g
    rw [← assoc, specGraphAwayIsoBasicOpen_inv_comp]
  have key : isoI (specGraphAwayIsoBasicOpen k M n q F s) ≫ specGraphAwayToAffineSpace k M n q F s ≫
        (affineSpaceIsoSpecMvPolynomial k _c0).inv
      = opI (bOpn (affineSpaceIndexedBy k _c1)
            _c3) ≫
          (affineSpaceIsoSpecMvPolynomial k _c1).hom ≫
            Spec.map (ofHom
              (((graphAlgebraEquiv _c2).symm.toRingEquiv.toRingHom).comp
                (algebraMap (MvPolynomial _c0 k)
                  (GraphAlgebra _c2)))) ≫
              (affineSpaceIsoSpecMvPolynomial k _c0).inv := by
    rw [h1, assoc, hre, hgc, ofHom_comp, map_comp]
    simp only [assoc]
  have hta : isoI (affineSpaceIsoSpecMvPolynomial k _c0) ≫
      affineSpaceIndexedByToSpec k _c0
      = Spec.map (ofHom
          MvPolynomial.C) := by
    simp
  have hsg_ : isoI (affineSpaceIsoSpecMvPolynomial k _c1) ≫
      affineSpaceIndexedByToSpec k _c1
      = Spec.map (ofHom
          MvPolynomial.C) := by
    simp
  have hA : (opI (bOpn (affineSpaceIndexedBy k _c1)
            _c3) ≫
          (affineSpaceIsoSpecMvPolynomial k _c1).hom ≫
            Spec.map (ofHom
              (((graphAlgebraEquiv _c2).symm.toRingEquiv.toRingHom).comp
                (algebraMap (MvPolynomial _c0 k)
                  (GraphAlgebra _c2)))) ≫
              (affineSpaceIsoSpecMvPolynomial k _c0).inv) ≫
        affineSpaceIndexedByToSpec k _c0
      = opI (bOpn (affineSpaceIndexedBy k _c1)
            _c3) ≫
          affineSpaceIndexedByToSpec k _c1 := by
    simp only [assoc]
    rw [hta, ← map_comp, ← ofHom_comp, graphAlgebraEquiv_symm_comp_algebraMap_comp_C k M n q F, ← hsg_,
      hom_inv_id_assoc]
  have hB : ∀ i,
      (appTop $ graphMorphismToAffineSpace k M n q F
          (bOpn (affineSpaceIndexedBy k _c1)
            _c3))
        (AffineSpace.coord _c4 i)
      = appTop (opI (bOpn (affineSpaceIndexedBy k _c1)
            _c3) ≫
          (affineSpaceIsoSpecMvPolynomial k _c1).hom ≫
            Spec.map (ofHom
              (((graphAlgebraEquiv _c2).symm.toRingEquiv.toRingHom).comp
                (algebraMap (MvPolynomial _c0 k)
                  (GraphAlgebra _c2)))) ≫
              (affineSpaceIsoSpecMvPolynomial k _c0).inv)
          (AffineSpace.coord _c4 i) := by
    intro i
    have e1 : (appTop (affineSpaceIsoSpecMvPolynomial k _c0).inv)
          (AffineSpace.coord _c4 i)
        = isoI (GSpecIso
            (CommRingCat.of (MvPolynomial _c0 k)))
            (MvPolynomial.X i) := by
      rw [← st_ (mvPolynomialEquivGlobalSections_symm_apply k _c0 $ AffineSpace.coord _c4 i) $ mvPolynomialEquivGlobalSections_symm_coord k _c0 i, hom_inv_id_apply]
    have e2 : (appTop $ Spec.map $ ofHom
          (((graphAlgebraEquiv _c2).symm.toRingEquiv.toRingHom).comp
            (algebraMap (MvPolynomial _c0 k)
              (GraphAlgebra _c2))))
          (isoI (GSpecIso
            (CommRingCat.of (MvPolynomial _c0 k)))
            (MvPolynomial.X i))
        = isoI (GSpecIso
            (CommRingCat.of (MvPolynomial _c1 k)))
            (graphCoordinates k M n q F i) := by
      have _i4 : (((graphAlgebraEquiv $ graphCoordinates k M n q F).symm.toRingEquiv.toRingHom).comp $ algebraMap (MvPolynomial (UFS M q) k) $ GraphAlgebra $ graphCoordinates k M n q F) (MvPolynomial.X i) = graphCoordinates k M n q F i := by
        simp [algebraMap_graphAlgebra]
      rw [← _i4]
      exact (congr_fun (congrArg CommRingCat.Hom.hom
        (Scheme.ΓSpecIso_inv_naturality $ ofHom
          (((graphAlgebraEquiv _c2).symm.toRingEquiv.toRingHom).comp
            (algebraMap (MvPolynomial _c0 k)
              (GraphAlgebra _c2)))))
        (MvPolynomial.X i)).symm
    rw [appTop_comp_apply, appTop_comp_apply, appTop_comp_apply, e1, e2, (mvPolynomialEquivGlobalSections_apply k _c1 $ graphCoordinates k M n q F i).symm]
    obtain ⟨i⟩ := i
    cases i with
    | inl a =>
      rw [graphCoordinates_inl, mvPolynomialEquivGlobalSections_X]
      exact graphMorphismToAffineSpace_appTop_coord_inl k M n q F _ a
    | inr j =>
      rw [graphCoordinates_inr, mvPolynomialEquivGlobalSections_polynomialOfSection]
      exact graphMorphismToAffineSpace_appTop_coord_inr k M n q F _ j
  rw [key]
  apply AffineSpace.hom_ext
  exact tr_ (graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec k M n q F _) hA.symm
  exact hB
end




namespace SequenceOfBlowups

section
variable {X' X} (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (hlen : length t = length s) (hcen : ∀ i : ℕ, i < length s → (center t i = ⊤ ↔ center s i = ⊤))
include hlen hcen
private theorem nextNontrivialIndex_le_of_center_eq_top_iff a :
    t.nextNontrivialIndex a ≤ s.nextNontrivialIndex a := by
  refine t.nextNontrivialIndex_le (s.le_nextNontrivialIndex a) ?_
  rcases s.center_nextNontrivialIndex_ne_top_or_length_le a with hd | hd
  by_cases hlt : s.nextNontrivialIndex a < length s
  simp_all
  simp_all
  simp_all

theorem nextNontrivialIndex_congr a :
    t.nextNontrivialIndex a = s.nextNontrivialIndex a :=
  le_antisymm (nextNontrivialIndex_le_of_center_eq_top_iff t s hlen hcen a)
    (nextNontrivialIndex_le_of_center_eq_top_iff s t hlen.symm (fun i hi => symm $ hcen i $ by omega) a)

theorem nontrivialIndex_congr (j : ℕ) :
    t.nontrivialIndex j = s.nontrivialIndex j := by
  induction j with
  | zero =>
      rw [nontrivialIndex_zero, nontrivialIndex_zero]
      exact nextNontrivialIndex_congr t s hlen hcen 0
  | succ j ih =>
      rw [nontrivialIndex_succ, nontrivialIndex_succ, ih]
      exact nextNontrivialIndex_congr t s hlen hcen _

theorem lengthWithoutIsoBlowups_le_of_center_eq_top_iff :
    t.lengthWithoutIsoBlowups ≤ s.lengthWithoutIsoBlowups := by
  by_contra hc
  have h1 := t.nontrivialIndex_lt_length $ mp_ not_le hc
  have h2 := s.nontrivialIndex_lengthWithoutIsoBlowups
  have h3 := nontrivialIndex_congr t s hlen hcen s.lengthWithoutIsoBlowups
  omega

theorem lengthWithoutIsoBlowups_congr :
    t.lengthWithoutIsoBlowups = s.lengthWithoutIsoBlowups :=
  le_antisymm (lengthWithoutIsoBlowups_le_of_center_eq_top_iff t s hlen hcen)
    (lengthWithoutIsoBlowups_le_of_center_eq_top_iff s t hlen.symm fun i hi => symm $ hcen i $ by omega)
end

section
variable {X : Sch}
section
variable (s : SequenceOfBlowups X)
theorem transitionMap_eq_eqToHom {a b} (h : a ≤ b)
    (h' : a = b) : transitionMap s h = eqToHom (congrArg s.schemeAt h'.symm) := by
  subst h'
  rw [s.transitionMap_self h, eqToHom_refl]

theorem eqToHom_comp_transitionMap {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b') :
    eqToHom (congrArg s.schemeAt hb) ≫ transitionMap s h' = transitionMap s h ≫ eqToHom (congrArg s.schemeAt ha) := by
  subst ha
  subst hb
  rw [eqToHom_refl, eqToHom_refl, id_comp, comp_id]

section
variable {a b} (h : a = b)
private theorem eqToHom_comp_projectionToBase :
    eqToHom (congrArg s.schemeAt h) ≫ projectionToBase s b = projectionToBase s a := by
  subst h
  rw [eqToHom_refl, id_comp]

theorem center_comap_eqToHom :
    (center s b).comap (eqToHom $ congrArg s.schemeAt h) = center s a := by
  subst h
  simp
end
end

theorem withoutIsoBlowups_isomorphic_self (t : SequenceOfBlowups X)
    (h : ∀ i : ℕ, i < length t → center t i ≠ ⊤) : t.withoutIsoBlowups.Isomorphic t := by
  have hnext : ∀ a, t.nextNontrivialIndex a = a := by
    intro a
    refine le_antisymm (t.nextNontrivialIndex_le le_rfl ?_) $ t.le_nextNontrivialIndex a
    by_cases ha : a < length t
    simp_all
    simp_all
  have hret : ∀ j, t.nontrivialIndex j = j := by
    intro j
    induction j with
    | zero => rw [t.nontrivialIndex_zero, hnext]
    | succ j ih => rw [t.nontrivialIndex_succ, hnext, ih]
  have hplen : t.withoutIsoBlowups.length = length t := by
    have h2 := t.nontrivialIndex_lengthWithoutIsoBlowups
    rwa [hret] at h2
  have h1 : isoH (eqToIso $ congrArg t.schemeAt $ hret 0) ≫ sbIzH t = t.withoutIsoBlowups.isoZero.hom := by
    rw [t.withoutIsoBlowups_isoObjZero, t.objNontrivialIndexZeroIso_hom, t.projectionToBase_def,
      t.transitionMap_eq_eqToHom _ (hret 0).symm]
    rfl
  have h2 : ∀ i, i < t.withoutIsoBlowups.length →
      hom (eqToIso $ congrArg t.schemeAt $ hret $ i + 1) ≫ transitionMapSucc t i
        = t.withoutIsoBlowups.transitionMapSucc i ≫ isoH (eqToIso $ congrArg t.schemeAt $ hret i) := by
    intro i _
    rw [t.withoutIsoBlowups_blowupMorphism, t.blowupMorphism_eq_transitionMap]
    exact t.eqToHom_comp_transitionMap (hret i) (hret $ i + 1) _ _
  have h3 : ∀ i, i < t.withoutIsoBlowups.length →
      (center t i).comap (eqToIso $ congrArg t.schemeAt $ hret i).hom = t.withoutIsoBlowups.center i := by
    intro i _
    exact t.center_comap_eqToHom $ hret i
  unfold SequenceOfBlowups.Isomorphic
  exact ⟨hplen, fun i _ => eqToIso $ congrArg t.schemeAt $ hret i, h1, h2, h3⟩
end

end SequenceOfBlowups

theorem isPullback_eqToHom_right {P Y X Z X' Z' : Sch}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (hX : X = X') (hZ : Z = Z') {f' : X' ⟶ Z'}
    (hf : eqToHom hX ≫ f' = f ≫ eqToHom hZ) :
    IsPullback (fst ≫ eqToHom hX) snd f' $ g ≫ eqToHom hZ := by
  subst hX
  subst hZ
  simp [eqToHom_refl, comp_id, id_comp] at hf ⊢
  rwa [hf]

theorem center_eq_comap_comp_eqToHom {X' X : Sch} (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) {a b : ℕ} (hab : a = b) (f : schemeAt t a ⟶ schemeAt s a)
    (hf : center t a = (center s a).comap f) :
    center t a = (center s b).comap (f ≫ eqToHom (congrArg s.schemeAt hab)) := by
  subst hab
  simp [eqToHom_refl, comp_id]
  exact hf

theorem IsStrictPullbackBlowupSeq.withoutIsoBlowups {X' X : Sch} {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) :
    IsStrictPullbackBlowupSeq g t.withoutIsoBlowups s.withoutIsoBlowups := by
  have hiff :=
    fun i hi => h.center_eq_top_iff i hi
  have hlen := h.length_eq
  have hret := SequenceOfBlowups.nontrivialIndex_congr t s hlen hiff
  unfold IsStrictPullbackBlowupSeq at h ⊢
  obtain ⟨-, σ, hzero, hstep, hcen⟩ := h
  have h1 : (σ (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (zero_le _)) ≫
        eqToHom (congrArg s.schemeAt (hret 0))) ≫ s.withoutIsoBlowups.isoZero.hom
      = t.withoutIsoBlowups.isoZero.hom ≫ g := by
    rw [s.withoutIsoBlowups_isoObjZero, t.withoutIsoBlowups_isoObjZero, s.objNontrivialIndexZeroIso_hom, t.objNontrivialIndexZeroIso_hom,
      assoc, SequenceOfBlowups.eqToHom_comp_projectionToBase s (hret 0)]
    exact ((isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length σ hzero hstep) (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (zero_le _))).w
  have h2 : ∀ j, ∀ hj,
      IsPullback
        (σ (t.nontrivialIndex (j + 1)) (t.nontrivialIndex_le_length hj) ≫
          eqToHom (congrArg s.schemeAt (hret (j + 1))))
        (t.withoutIsoBlowups.transitionMapSucc j) (s.withoutIsoBlowups.transitionMapSucc j)
        (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)) ≫
          eqToHom (congrArg s.schemeAt (hret j))) := by
    intro j hj
    rw [t.withoutIsoBlowups_blowupMorphism, s.withoutIsoBlowups_blowupMorphism]
    let _a0 := t.nontrivialIndex_monotone $ le_succ j
    exact isPullback_eqToHom_right
      ((isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep) (t.nontrivialIndex j) (t.nontrivialIndex (j + 1)) _a0
        (t.nontrivialIndex_le_length hj))
      (congrArg s.schemeAt (hret (j + 1))) (congrArg s.schemeAt (hret j))
      (SequenceOfBlowups.eqToHom_comp_transitionMap s (hret j) (hret (j + 1))
        _a0 (s.nontrivialIndex_monotone (le_succ j)))
  refine ⟨SequenceOfBlowups.lengthWithoutIsoBlowups_congr t s hlen hiff, fun j hj => σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length hj) ≫
    eqToHom (congrArg s.schemeAt (hret j)), h1, h2, ?_⟩
  intro j hj
  exact center_eq_comap_comp_eqToHom t s (hret j)
    (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)))
    (hcen (t.nontrivialIndex j) (t.nontrivialIndex_lt_length hj))

theorem isStrictPullbackSequenceOfBlowups_id_of_isomorphic {X} {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') : IsStrictPullbackBlowupSeq (𝟙 X) B B' := by
  unfold SequenceOfBlowups.Isomorphic at h
  unfold IsStrictPullbackBlowupSeq
  obtain ⟨hlen, e, hzero, hstep, hcen⟩ := h
  refine ⟨hlen, fun i hi => isoH $ e i hi, ?_, ?_, ?_⟩
  rwa [comp_id]
  intro i hi
  exact of_horiz_isIso ⟨hstep i hi⟩
  intro i hi
  exact sy_ $ hcen i hi

theorem SequenceOfBlowups.Isomorphic.withoutIsoBlowups {X : Sch} {t1_ t2_ : SequenceOfBlowups X}
    (h : t1_.Isomorphic t2_) : t1_.withoutIsoBlowups.Isomorphic t2_.withoutIsoBlowups :=
  ((isStrictPullbackSequenceOfBlowups_id_of_isomorphic h).withoutIsoBlowups).isomorphic
    (isStrictPullbackSequenceOfBlowups_id_of_isomorphic $ SequenceOfBlowups.isomorphic_refl t2_.withoutIsoBlowups)


private theorem support_nonempty_iff_ne_top {A : Sch} (I : ISD A) :
    (∃ x, x ∈ support I) ↔ I ≠ ⊤ := by
  constructor
  rintro ⟨x, hx⟩ rfl
  rwa [support_top] at hx
  intro hne
  by_contra hc
  push Not at hc
  exact hne $ mp_ (support_eq_bot_iff I)
    (SetLike.ext fun x => iff_of_false (hc x) fun hmem => hmem)

theorem comap_isoHom_eq_top_iff {A B : Sch} (e : A ≅ B) (J : ISD B) :
    J.comap e.hom = ⊤ ↔ J = ⊤ := by
  constructor
  intro hJ
  have h1 : (J.comap e.hom).comap e.inv = J := by
    rw [← comap_comp, e.inv_hom_id, comap_id]
  rw [← h1, hJ]
  simp
  rintro rfl
  simp

namespace SequenceOfBlowups

variable {X : Sch}

theorem withoutIsoBlowups_projectionToBase (s : SequenceOfBlowups X) j :
    s.withoutIsoBlowups.projectionToBase j = projectionToBase s (s.nontrivialIndex j) := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = sbPrj s (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  rw [projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
  exact s.transitionMap_comp_projectionToBase $ s.nontrivialIndex_monotone $ zero_le j

theorem exists_nontrivialIndex_eq_of_center_ne_top (s : SequenceOfBlowups X) {i} (hi : i < length s)
    (h : center s i ≠ ⊤) :
    ∃ j, j < s.lengthWithoutIsoBlowups ∧ s.nontrivialIndex j = i := by
  have hex : ∃ n, i < s.nontrivialIndex n :=
    ⟨s.lengthWithoutIsoBlowups, by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi⟩
  obtain ⟨n, hn1, hn2, hn3⟩ :
      ∃ n, i < s.nontrivialIndex n ∧ (∀ m, m < n → ¬ (i < s.nontrivialIndex m)) ∧ n ≤ s.lengthWithoutIsoBlowups :=
    ⟨find hex, find_spec hex, fun m hm => find_min hex hm,
      find_le (by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi)⟩
  cases n with
  | zero => exact absurd (s.center_eq_top_of_lt_nontrivialIndex_zero hn1) h
  | succ m =>
      have hmi := mp_ not_lt $ hn2 m $ lt_succ_self m
      refine ⟨m, by omega, ?_⟩
      rcases eq_or_lt_of_le hmi with heq | hlt
      exact heq
      exact absurd (s.center_eq_top_of_nontrivialIndex_lt hlt hn1) h

end SequenceOfBlowups

namespace IsStrictPullbackBlowupSeq

theorem isPullbackSequenceOfBlowups_withoutIsoBlowups {X' X} {ph_}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq ph_ t s) :
    IsPullbackBlowupSequence ph_ t.withoutIsoBlowups s := by
  obtain ⟨hlen, σ, hzero, hstep, hcen⟩ := h
  have hstructPB :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism ph_ t s t.length σ hzero hstep
  obtain ⟨e, he1, he2⟩ :
      ∃ e : ∀ i, i ≤ t.withoutIsoBlowups.length →
          (t.withoutIsoBlowups.schemeAt i ≅ m131 ph_ (sbPrj s $ t.nontrivialIndex i)),
        (∀ i (hi : i ≤ t.withoutIsoBlowups.length),
            (e i hi).hom ≫ m57 ph_ (sbPrj s $ t.nontrivialIndex i)
              = sbPrj t (t.nontrivialIndex i)) ∧
        (∀ i (hi : i ≤ t.withoutIsoBlowups.length),
            (e i hi).hom ≫ m47 ph_ (sbPrj s $ t.nontrivialIndex i)
              = σ (t.nontrivialIndex i)
                  (t.nontrivialIndex_le_length $ show i ≤ t.lengthWithoutIsoBlowups from hi)) := by
    refine ⟨fun i hi => ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length $ show i ≤ t.lengthWithoutIsoBlowups from hi)).flip).isoPullback, ?_, ?_⟩
    intro i hi
    exact ((hstructPB (t.nontrivialIndex i)
      (t.nontrivialIndex_le_length $ show i ≤ t.lengthWithoutIsoBlowups from hi)).flip).isoPullback_hom_fst
    intro i hi
    exact ((hstructPB (t.nontrivialIndex i)
      (t.nontrivialIndex_le_length $ show i ≤ t.lengthWithoutIsoBlowups from hi)).flip).isoPullback_hom_snd
  refine ⟨t.nontrivialIndex, e, ?_, ?_, t.nontrivialIndex_lengthWithoutIsoBlowups.trans hlen, ?_, ?_, ?_, ?_⟩
  intro i hi
  have h1 := t.nontrivialIndex_lt_length hi
  omega
  intro i j _ hij
  exact t.nontrivialIndex_strictMono hij
  intro i hi
  have hi' : i < t.length := by omega
  let _a0 := (hstructPB i hi'.le).flip
  have hcomap : ((center s i).comap $ m47 ph_ $ sbPrj s i).comap
      (_a0.isoPullback.hom) = center t i := by
    rw [← comap_comp,
      _a0.isoPullback_hom_snd]
    exact sy_ $ hcen i hi'
  rw [support_nonempty_iff_ne_top]
  constructor
  intro hne
  refine t.exists_nontrivialIndex_eq_of_center_ne_top hi' ?_
  intro htop
  exact hne $ mp_ (comap_isoHom_eq_top_iff _ _) $ tr_ hcomap htop
  rintro ⟨j, hj, rfl⟩
  intro htop
  refine t.center_nontrivialIndex_ne_top hj ?_
  rw [← hcomap, htop]
  simp
  intro i hi
  rw [he1 i hi, t.withoutIsoBlowups_projectionToBase]
  intro i hi hr
  apply Limits.pullback.hom_ext
  rw [assoc, assoc, he1, s.pullbackTransitionMap_fst, he1, t.withoutIsoBlowups_blowupMorphism i]
  exact t.transitionMap_comp_projectionToBase $ t.nontrivialIndex_monotone $ le_succ i
  rw [assoc, assoc, he2, s.pullbackTransitionMap_snd, ← assoc, he2,
    t.withoutIsoBlowups_blowupMorphism i]
  exact ((isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep) (t.nontrivialIndex i) (t.nontrivialIndex $ i + 1)
    (t.nontrivialIndex_monotone $ le_succ i) $ t.nontrivialIndex_le_length $ show i + 1 ≤ t.lengthWithoutIsoBlowups from hi).w.symm
  intro i hi
  rw [he2 i hi.le]
  exact hcen (t.nontrivialIndex i) $ t.nontrivialIndex_lt_length hi

end IsStrictPullbackBlowupSeq




section
variable (k : Type) [Field k] (M n : ℕ)
def mvPolynomialToSumCoordinateRing :
    MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k $ UFin M, ⊤) →+*
      Γ(affineSpaceIndexedBy k $ UFS M n, ⊤) :=
  eval₂Hom (appTop $ projLeft k M n).hom
    (fun i : Fin n =>
      AffineSpace.coord (Sp k)
        (up (inr i) : UFS M n))

@[simp]
theorem mvPolynomialToSumCoordinateRing_C
    (t : Γ(affineSpaceIndexedBy k $ UFin M, ⊤)) :
    mvPolynomialToSumCoordinateRing k M n (MvPolynomial.C t) = appTop (projLeft k M n) t := by
  simp [mvPolynomialToSumCoordinateRing]

@[simp]
theorem mvPolynomialToSumCoordinateRing_X (i : Fin n) :
    mvPolynomialToSumCoordinateRing k M n (MvPolynomial.X i) =
      AffineSpace.coord (Sp k)
        (up (inr i) : UFS M n) := by
  simp [mvPolynomialToSumCoordinateRing]
end

theorem comp_appTop_apply_eq {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z) (t : Γ(Z, ⊤)) :
    appTop (f ≫ g) t = appTop f (appTop g t) := rfl

theorem id_appTop_apply (X : Sch) (t : Γ(X, ⊤)) :
    appTop (𝟙 X : X ⟶ X) t = t := by simp

theorem specToAffineSpaceExtendCoords_appTop_mvPolynomial (k : Type) [Field k] (A : Sch)
    [IsAffine A] (pA : A ⟶ Sp k) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (UFin M)) {B' : CRC}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (he : e ≫ affineSpaceIndexedByToSpec k (UFin M) = pA)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k $ UFin M, ⊤)) :
    appTop (specToAffineSpaceExtendCoords k A pA M e σ n b) (mvPolynomialToSumCoordinateRing k M n p) =
      inv (GSpecIso B')
        (eval₂ σ.hom b $ MvPolynomial.map (appTop e).hom p) := by
  induction p using induction_on with
  | C a =>
      have h1 : hAT (specToAffineSpaceExtendCoords k A pA M e σ n b) (hAT (projLeft k M n) a)
          = isoI (GSpecIso B') (σ $ hAT e a) := by
        rw [← comp_appTop_apply_eq, specToAffineSpaceExtendCoords_comp_projLeft k A pA M e σ n b he,
          comp_appTop_apply_eq, specHomOfGlobalSections_appTop]
      rw [mvPolynomialToSumCoordinateRing_C, h1]
      simp
  | add p q hp hq =>
      simp [map_add, eval₂_add, hp, hq]
  | mul_X p i hp =>
      simp [map_mul, eval₂_mul, mvPolynomialToSumCoordinateRing_X, hp,
        specToAffineSpaceExtendCoords_appTop_coord_inr, map_X, eval₂_X]

theorem appTop_surjective_of_isClosedImmersion {X Y : Sch}
    (f : X ⟶ Y) [IsAffine Y] [IsClosedImmersion f] :
    Surjective ⇑((f.appTop).hom) :=
  (isAffine_surjective_of_isAffine (f := f)).2

theorem appTop_ext {X Y : Sch} {f g : X ⟶ Y}
    (h : ∀ t : Γ(Y, ⊤), appTop f t = appTop g t) : appTop f = appTop g := by
  ext t
  exact h t

theorem specMap_appTop_GaSpecIso_inv {R S} f r :
    appTop (Spec.map f) (inv (GSpecIso R) r) = inv (GSpecIso S) (f r) := by
  have h := congrArg (fun m : R ⟶ Γ(Spec S, ⊤) => m4 m r)
    (Scheme.ΓSpecIso_inv_naturality f)
  simp only [hom_comp, comp_apply] at h
  exact sy_ h

section
variable (k : Type) [Field k]
section
variable (M n : ℕ)
def polynomialRingOverGlobalSections : CRC :=
  CommRingCat.of (MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k $ UFin M, ⊤))

def globalSectionsToPolynomialRing :
    Γ(affineSpaceIndexedBy k $ UFin M, ⊤) ⟶ polynomialRingOverGlobalSections k M n :=
  ofHom
    (MvPolynomial.C :
      Γ(affineSpaceIndexedBy k $ UFin M, ⊤) →+*
        MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k $ UFin M, ⊤))

theorem globalSectionsToPolynomialRing_apply
    (t : Γ(affineSpaceIndexedBy k $ UFin M, ⊤)) :
    globalSectionsToPolynomialRing k M n t = MvPolynomial.C t := rfl

def polynomialRingVariables : Fin n → polynomialRingOverGlobalSections k M n :=
  fun i => MvPolynomial.X i

def specPolynomialRingToAffineSpaceSum :
    Spec (polynomialRingOverGlobalSections k M n) ⟶ affineSpaceIndexedBy k (UFS M n) :=
  specToAffineSpaceExtendCoords k (affineSpaceIndexedBy k $ UFin M)
    (affineSpaceIndexedByToSpec k $ UFin M) M (𝟙 _) (globalSectionsToPolynomialRing k M n) n $ polynomialRingVariables k M n

def affineSpaceSumToSpecPolynomialRing :
    affineSpaceIndexedBy k (UFS M n) ⟶ Spec (polynomialRingOverGlobalSections k M n) :=
  (affineSpaceIndexedBy k $ UFS M n).isoSpec.hom ≫
    Spec.map (ofHom $ mvPolynomialToSumCoordinateRing k M n)

theorem comp_affineSpaceIndexedByToSpec_eq :
    specPolynomialRingToAffineSpaceSum k M n ≫ affineSpaceIndexedByToSpec k (UFS M n) =
      specHomOfGlobalSections (affineSpaceIndexedBy k $ UFin M) (globalSectionsToPolynomialRing k M n) ≫
        affineSpaceIndexedByToSpec k (UFin M) :=
  specToAffineSpaceExtendCoords_comp_toSpec k (affineSpaceIndexedBy k $ UFin M)
    (affineSpaceIndexedByToSpec k $ UFin M) M (𝟙 _) (globalSectionsToPolynomialRing k M n) n $ polynomialRingVariables k M n

theorem appTop_coord_inl_eq_C (a : Fin M) :
    appTop (specPolynomialRingToAffineSpaceSum k M n)
        (AffineSpace.coord (Sp k)
          (up (inl a) : UFS M n)) =
      inv (GSpecIso $ polynomialRingOverGlobalSections k M n)
        (MvPolynomial.C $ AffineSpace.coord (Sp k) $ up a) := by
  have h := specToAffineSpaceExtendCoords_appTop_coord_inl k (affineSpaceIndexedBy k $ UFin M)
    (affineSpaceIndexedByToSpec k $ UFin M) M (𝟙 _) (globalSectionsToPolynomialRing k M n) n (polynomialRingVariables k M n) a
  rwa [comp_id, specHomOfGlobalSections_appTop] at h

theorem appTop_coord_inr_eq_X (j : Fin n) :
    appTop (specPolynomialRingToAffineSpaceSum k M n)
        (AffineSpace.coord (Sp k)
          (up (inr j) : UFS M n)) =
      inv (GSpecIso $ polynomialRingOverGlobalSections k M n) (MvPolynomial.X j) :=
  specToAffineSpaceExtendCoords_appTop_coord_inr k (affineSpaceIndexedBy k $ UFin M)
    (affineSpaceIndexedByToSpec k $ UFin M) M (𝟙 _) (globalSectionsToPolynomialRing k M n) n (polynomialRingVariables k M n) j

theorem appTop_GaSpecIso_inv_eq_mvPolynomialToSumCoordinateRing
    (r : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k $ UFin M, ⊤)) :
    appTop (affineSpaceSumToSpecPolynomialRing k M n) (inv (GSpecIso $ polynomialRingOverGlobalSections k M n) r) =
      mvPolynomialToSumCoordinateRing k M n r := by
  let _c0 := isoI (GSpecIso $ polynomialRingOverGlobalSections k M n) r
  let _a0 := ofHom $ mvPolynomialToSumCoordinateRing k M n
  let _a1 := affineSpaceIndexedBy k $ UFS M n
  let _a2 := hAT (m12 _a0) _c0
  have h1 : _a2 =
      inv (GSpecIso Γ(_a1, ⊤))
        (mvPolynomialToSumCoordinateRing k M n r) :=
    specMap_appTop_GaSpecIso_inv _a0 r
  have h2 : hAT (affineSpaceSumToSpecPolynomialRing k M n) _c0 =
      appTop (_a1.isoSpec.hom)
        _a2 := rfl
  rw [h2, h1]
  simp [isoSpec_hom, Scheme.toSpecΓ_appTop]
end

section
variable (A : Sch)
theorem exists_mvPolynomial_map_appTop_eq (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (UFin M))
    [IsClosedImmersion e] (n q : ℕ)
    (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤)) (j : Fin q) :
    ∃ P : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k $ UFin M, ⊤),
      MvPolynomial.map (e.appTop).hom P = rel j := by
  obtain ⟨P, hP⟩ := map_surjective ((hAT e).hom)
    (appTop_surjective_of_isClosedImmersion e) $ rel j
  exact ⟨P, hP⟩

section
variable [IsAffine A] (pA : A ⟶ Sp k) (M) (e : A ⟶ affineSpaceIndexedBy k (UFin M))
theorem preimage_basicOpen_specToAffineSpaceExtendCoords {B' : CRC}
    (σ : Γ(A, ⊤) ⟶ B') (n : ℕ) (b : Fin n → B')
    (f : Γ(affineSpaceIndexedBy k $ UFS M n, ⊤))
    (hf : IsUnit $ appTop (specToAffineSpaceExtendCoords k A pA M e σ n b) f) :
    (Opens.map (specToAffineSpaceExtendCoords k A pA M e σ n b).base).obj
        ((affineSpaceIndexedBy k $ UFS M n).basicOpen f) = ⊤ := by
  let _m0 := specToAffineSpaceExtendCoords k A pA M e σ n b
  let _a0 := bOpn (Spec B') $ hAT _m0 f
  have h1 : (m54 _m0.base).obj
        (bOpn (affineSpaceIndexedBy k $ UFS M n) f) =
      _a0 :=
    preimage_basicOpen ..
  have h2 : _a0 = ⊤ :=
    basicOpen_of_isUnit (Spec B') hf
  rw [h1, h2]
end
end
end

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits Opposite

namespace FunctorialResolution.EmbeddedResolution

section
variable {X X' : Sch}
def IsPullbackUpToEmptyCenters (ph_ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) : Prop :=
  ∃ (r : ℕ → ℕ) (e : ∀ i, i ≤ s'.length → (s'.schemeAt i ≅ pullback ph_ (s.projectionToBase $ r i))),
    (∀ i < s'.length, r i < s.length) ∧
    (∀ i j : ℕ, j ≤ s'.length → i < j → r i < r j) ∧
    r s'.length = s.length ∧
    (∀ i < s.length, (¬ ∃ j < s'.length, r j = i) →
      ¬ ∃ x, x ∈ ((s.center i).comap $ pullback.snd ph_ $ s.projectionToBase i).support) ∧
    (∀ (i : ℕ) (hi : i ≤ s'.length),
      (e i hi).hom ≫ pullback.fst ph_ (s.projectionToBase $ r i) = s'.projectionToBase i) ∧
    (∀ (i : ℕ) (hi : i < s'.length) (hr : r i ≤ r (i + 1)),
      s'.transitionMapSucc i ≫ (e i $ Nat.le_of_lt hi).hom =
        (e (i + 1) $ succ_le_of_lt hi).hom ≫ s.pullbackTransitionMap ph_ hr) ∧
    (∀ (i : ℕ) (hi : i < s'.length),
      s'.center i =
        (s.center $ r i).comap
          ((e i $ Nat.le_of_lt hi).hom ≫ pullback.snd ph_ (s.projectionToBase $ r i)))

theorem center_comap_pullback_snd_ne_top_congr (ph_ : X' ⟶ X) (s : SequenceOfBlowups X)
    {a b : ℕ} (hab : a = b)
    (h : (s.center b).comap (pullback.snd ph_ $ s.projectionToBase b) ≠ ⊤) :
    (s.center a).comap (pullback.snd ph_ $ s.projectionToBase a) ≠ ⊤ := by
  subst hab
  exact h

section
variable (s : SequenceOfBlowups X) (ph_ : X' ⟶ X)
theorem pullbackTransitionMap_snd_assoc
    {i i' : ℕ} (h : i ≤ i') {W : Sch} (k : s.schemeAt i ⟶ W) :
    s.pullbackTransitionMap ph_ h ≫ pullback.snd ph_ (s.projectionToBase i) ≫ k
      = pullback.snd ph_ (s.projectionToBase i') ≫ s.transitionMap h ≫ k := by
  rw [← assoc, s.pullbackTransitionMap_snd, assoc]

section
variable {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
theorem pullbackTransitionMap_comp :
    s.pullbackTransitionMap ph_ hbc ≫ s.pullbackTransitionMap ph_ hab = s.pullbackTransitionMap ph_ (hab.trans hbc) := by
  refine pullback.hom_ext ?_ ?_
  rw [assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
  rw [assoc, s.pullbackTransitionMap_snd, ← assoc, s.pullbackTransitionMap_snd, assoc,
    s.transitionMap_trans, s.pullbackTransitionMap_snd]

theorem pullbackTransitionMap_comp_assoc {W : Sch}
    (k : pullback ph_ (s.projectionToBase a) ⟶ W) :
    s.pullbackTransitionMap ph_ hbc ≫ s.pullbackTransitionMap ph_ hab ≫ k
      = s.pullbackTransitionMap ph_ (hab.trans hbc) ≫ k := by
  rw [← assoc, pullbackTransitionMap_comp]
end

theorem pullbackTransitionMap_self {i}
    (h : i ≤ i) : s.pullbackTransitionMap ph_ h = 𝟙 (pullback ph_ $ s.projectionToBase i) := by
  refine pullback.hom_ext ?_ ?_
  rw [s.pullbackTransitionMap_fst, id_comp]
  rw [s.pullbackTransitionMap_snd, s.transitionMap_self, comp_id, id_comp]
end
end

section
variable {X X' Z Z' : Sch} (ph_ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X) (th_ : Z ≅ Z') (hth : hom th_ ≫ g = f)
noncomputable def pullbackCongrRightHom : pullback ph_ f ⟶ pullback ph_ g :=
  pullback.lift (pullback.fst ph_ f) (pullback.snd ph_ f ≫ hom th_)
    (by rw [assoc, hth]; exact pullback.condition)

theorem pullbackCongrRightHom_fst :
    pullbackCongrRightHom ph_ f g th_ hth ≫ pullback.fst ph_ g = pullback.fst ph_ f :=
  pullback.lift_fst _ _ _

theorem pullbackCongrRightHom_snd :
    pullbackCongrRightHom ph_ f g th_ hth ≫ pullback.snd ph_ g = pullback.snd ph_ f ≫ hom th_ :=
  pullback.lift_snd _ _ _

noncomputable def pullbackCongrRightIso : pullback ph_ f ≅ pullback ph_ g where
  hom := pullbackCongrRightHom ph_ f g th_ hth
  inv := pullbackCongrRightHom ph_ g f th_.symm $ by rw [← hth, symm_hom, inv_hom_id_assoc]
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [assoc, pullbackCongrRightHom_fst, pullbackCongrRightHom_fst, id_comp]
    · rw [assoc, pullbackCongrRightHom_snd, ← assoc, pullbackCongrRightHom_snd, assoc, symm_hom,
        th_.hom_inv_id, comp_id, id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [assoc, pullbackCongrRightHom_fst, pullbackCongrRightHom_fst, id_comp]
    · rw [assoc, pullbackCongrRightHom_snd, ← assoc, pullbackCongrRightHom_snd, assoc, symm_hom,
        th_.inv_hom_id, comp_id, id_comp]

theorem pullbackCongrRightIso_hom_fst :
    hom (pullbackCongrRightIso ph_ f g th_ hth) ≫ pullback.fst ph_ g = pullback.fst ph_ f :=
  pullbackCongrRightHom_fst ph_ f g th_ hth

theorem pullbackCongrRightIso_hom_snd :
    hom (pullbackCongrRightIso ph_ f g th_ hth) ≫ pullback.snd ph_ g = pullback.snd ph_ f ≫ hom th_ :=
  pullbackCongrRightHom_snd ph_ f g th_ hth
end

section
variable {X : Sch}
theorem ne_top_iff_exists_mem_support (I : ISD X) :
    I ≠ ⊤ ↔ ∃ x, x ∈ support I := by
  have hiff : support I = ⊥ ↔ I = ⊤ := by simp
  constructor
  intro hne
  by_contra hx
  exact hne $ mp_ hiff $ SetLike.ext fun y => ⟨fun hy => absurd (⟨y, hy⟩ : ∃ x, x ∈ support I) hx, fun hy => (hy : False).elim⟩
  rintro ⟨x, hx⟩ hI
  rwa [mpr_ hiff hI] at hx

section
variable (s : SequenceOfBlowups X)
theorem transitionMap_comp_eqToIso {p q p' q'}
    (hp : p = p') (hq : q = q') (hpq : p ≤ q) (hpq' : p' ≤ q') :
    s.transitionMap hpq ≫ hom (eqToIso $ congrArg s.schemeAt hp)
      = hom (eqToIso $ congrArg s.schemeAt hq) ≫ s.transitionMap hpq' := by
  subst hp
  subst hq
  simp

section
variable {a b} (hab : a = b)
theorem eqToIso_hom_comp_projectionToBase :
    hom (eqToIso $ congrArg s.schemeAt hab) ≫ s.projectionToBase b = s.projectionToBase a := by
  subst hab
  simp

theorem center_comap_eqToIso_hom :
    (s.center b).comap (eqToIso $ congrArg s.schemeAt hab).hom = s.center a := by
  subst hab
  simp
end
end
end

theorem comap_congr_morphism {A B : Sch} {u v : A ⟶ B} (h : u = v) (I : ISD B) :
    I.comap u = I.comap v := by
  rw [h]

theorem comap_congr_idealSheaf {A B : Sch} (u : A ⟶ B) {I J : ISD B}
    (h : I = J) : I.comap u = J.comap u := by
  rw [h]

theorem exists_pullbackIso_of_iso {X X' A Z Z' : Sch} (ph_ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (u : A ≅ pullback ph_ f) (th_ : Z ≅ Z') (hth : hom th_ ≫ g = f) :
    ∃ v : A ≅ pullback ph_ g,
      hom v ≫ pullback.fst ph_ g = hom u ≫ pullback.fst ph_ f ∧
      hom v ≫ pullback.snd ph_ g = hom u ≫ pullback.snd ph_ f ≫ hom th_ := by
  refine ⟨u ≪≫ pullbackCongrRightIso ph_ f g th_ hth, ?_, ?_⟩
  rw [trans_hom, assoc, pullbackCongrRightIso_hom_fst]
  rw [trans_hom, assoc, pullbackCongrRightIso_hom_snd]

theorem comp_comp_eq_of_comp_eq {A B C D : Sch} {u : A ⟶ B} {v : B ⟶ C} {w : A ⟶ C}
    (h : u ≫ v = w) (k : C ⟶ D) : u ≫ v ≫ k = w ≫ k := by
  rw [← assoc, h]

private theorem comap_iso_hom_ne_top {X Y : Sch} (E : X ≅ Y) (J : ISD Y)
    (h : J ≠ ⊤) : J.comap E.hom ≠ ⊤ := by
  intro hc
  apply h
  have hJ : J = (J.comap E.hom).comap E.inv := by
    rw [← comap_comp, E.inv_hom_id, comap_id]
  rw [hJ, hc, comap_top]

theorem comap_pullback_snd_ne_top_iff_of_iso {X X' Z Z' : Sch} (ph_ : X' ⟶ X) (f : Z ⟶ X)
    (g : Z' ⟶ X) (th_ : Z ≅ Z') (hth : hom th_ ≫ g = f) (I : ISD Z)
    (J : ISD Z') (hIJ : J.comap th_.hom = I) :
    (I.comap (pullback.snd ph_ f) ≠ ⊤) ↔ (J.comap (pullback.snd ph_ g) ≠ ⊤) := by
  let _a0 := pullbackCongrRightIso ph_ f g th_ hth
  have hkey : (J.comap $ pullback.snd ph_ g).comap _a0.hom
      = I.comap (pullback.snd ph_ f) := by
    rw [← comap_comp, pullbackCongrRightIso_hom_snd, comap_comp, hIJ]
  constructor
  intro h hc
  apply h
  rw [← hkey, hc, comap_top]
  intro h
  rw [← hkey]
  exact comap_iso_hom_ne_top _a0 _ h

theorem nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups {X X' : Sch} (ph_ : X' ⟶ X) (s : SequenceOfBlowups X)
    (i : ℕ) :
    ((s.center $ s.nontrivialIndex i).comap (pullback.snd ph_ $ s.projectionToBase $ s.nontrivialIndex i) ≠ ⊤) ↔
      ((s.withoutIsoBlowups.center i).comap (pullback.snd ph_ $ s.withoutIsoBlowups.projectionToBase i) ≠ ⊤) :=
  comap_pullback_snd_ne_top_iff_of_iso ph_ (sbPrj s $ s.nontrivialIndex i) (s.withoutIsoBlowups.projectionToBase i) (refl _)
    (tr_ (id_comp $ s.withoutIsoBlowups.projectionToBase i) $ s.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex i)
    (sbCtr s $ s.nontrivialIndex i) (s.withoutIsoBlowups.center i) $ comap_id _

namespace IsPullbackUpToEmptyCenters

theorem isPullbackSequenceOfBlowups_withoutIsoBlowups {X X'} {ph_} {s' : SequenceOfBlowups X'}
    {s : SequenceOfBlowups X} (h : IsPullbackUpToEmptyCenters ph_ s' s) :
    IsPullbackBlowupSequence ph_ s'.withoutIsoBlowups s.withoutIsoBlowups := by
  obtain ⟨r, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hle : ∀ j, j ≤ s'.lengthWithoutIsoBlowups → s'.nontrivialIndex j ≤ s'.length := fun j hj =>
    s'.nontrivialIndex_le_length hj
  have hrmono : ∀ i i', i ≤ i' → i' ≤ s'.length → r i ≤ r i' := by
    intro i i' hii hi'
    rcases eq_or_lt_of_le hii with rfl | hlt
    exact le_rfl
    exact le_of_lt $ h2 i i' hi' hlt
  have hdown : ∀ i i' (hii' : i ≤ i') (hi' : i' ≤ s'.length) {W : Sch}
      (k : pullback ph_ (sbPrj s $ r i) ⟶ W),
      s'.transitionMap hii' ≫ (e i $ hii'.trans hi').hom ≫ k
        = (e i' hi').hom ≫ s.pullbackTransitionMap ph_ (hrmono i i' hii' hi') ≫ k := by
    intro i i' hii'
    induction i', hii' using le_induction with
    | base =>
      intro hi W k
      rw [s'.transitionMap_self, id_comp, pullbackTransitionMap_self, id_comp]
    | succ m hm ih =>
      intro hi W k
      have hstep := h6 m (lt_of_lt_of_le (lt_succ_self m) hi) $ hrmono m (m + 1) (le_succ m) hi
      have hdec : s'.transitionMap (hm.trans $ le_succ m) = s'.transitionMapSucc m ≫ s'.transitionMap hm := by
        rw [s'.blowupMorphism_eq_transitionMap]
        exact (s'.transitionMap_trans hm $ le_succ m).symm
      rw [hdec, assoc, ih (le_trans (le_succ m) hi) k, ← assoc, hstep, assoc,
        pullbackTransitionMap_comp_assoc]
  have key : ∀ j, ∃ k, j ≤ s'.lengthWithoutIsoBlowups → s.nontrivialIndex k = r (s'.nontrivialIndex j) := by
    intro j
    rcases lt_trichotomy j s'.lengthWithoutIsoBlowups with hj | hj | hj
    have ha := s'.nontrivialIndex_lt_length hj
    have hc2 : s.center (r $ s'.nontrivialIndex j) ≠ ⊤ := by
      intro hcc
      apply s'.center_nontrivialIndex_ne_top hj
      rw [h7 (s'.nontrivialIndex j) ha, hcc, comap_top]
    obtain ⟨k, _, hk2⟩ := s.exists_nontrivialIndex_eq_of_center_ne_top (h1 _ ha) hc2
    exact ⟨k, fun _ => hk2⟩
    refine ⟨s.lengthWithoutIsoBlowups, fun _ => ?_⟩
    rw [s.nontrivialIndex_lengthWithoutIsoBlowups, hj, s'.nontrivialIndex_lengthWithoutIsoBlowups, h3]
    exact ⟨0, fun hle' => absurd hle' $ not_le.mpr hj⟩
  choose mu_ hmu_ using key
  have hth : ∀ j (hj : j ≤ s'.lengthWithoutIsoBlowups),
      (eqToIso $ congrArg s.schemeAt (hmu_ j hj).symm).hom ≫ s.withoutIsoBlowups.projectionToBase (mu_ j)
        = sbPrj s (r $ s'.nontrivialIndex j) := by
    intro j hj
    let hk := eqToIso_hom_comp_projectionToBase s (hmu_ j hj).symm
    rwa [s.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex $ mu_ j]
  have hEx : ∀ j (hj : j ≤ s'.lengthWithoutIsoBlowups),
      ∃ v : s'.withoutIsoBlowups.schemeAt j ≅ pullback ph_ (s.withoutIsoBlowups.projectionToBase $ mu_ j),
        v.hom ≫ pullback.fst ph_ (s.withoutIsoBlowups.projectionToBase $ mu_ j)
            = (e (s'.nontrivialIndex j) $ hle j hj).hom ≫
                pullback.fst ph_ (sbPrj s $ r $ s'.nontrivialIndex j) ∧
        v.hom ≫ pullback.snd ph_ (s.withoutIsoBlowups.projectionToBase $ mu_ j)
            = (e (s'.nontrivialIndex j) $ hle j hj).hom ≫
                pullback.snd ph_ (sbPrj s $ r $ s'.nontrivialIndex j) ≫
                  (eqToIso $ congrArg s.schemeAt (hmu_ j hj).symm).hom := by
    intro j hj
    exact exists_pullbackIso_of_iso ph_ (sbPrj s $ r $ s'.nontrivialIndex j) (s.withoutIsoBlowups.projectionToBase $ mu_ j)
      (e (s'.nontrivialIndex j) $ hle j hj) (eqToIso $ congrArg s.schemeAt (hmu_ j hj).symm) $ hth j hj
  choose E hEfst0 hEsnd0 using hEx
  have hEfst : ∀ j (hj : j ≤ s'.lengthWithoutIsoBlowups),
      (E j hj).hom ≫ pullback.fst ph_ (s.withoutIsoBlowups.projectionToBase $ mu_ j) = s'.withoutIsoBlowups.projectionToBase j := by
    intro j hj
    exact ((hEfst0 j hj).trans $ h5 (s'.nontrivialIndex j) $ hle j hj).trans
      (s'.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex j).symm
  unfold IsPullbackBlowupSequence
  refine ⟨mu_, E, ?_, ?_, ?_, ?_, fun i hi => hEfst i hi, ?_, ?_⟩
  intro j hj
  have hh := hmu_ j $ le_of_lt hj
  have hlt : s.nontrivialIndex (mu_ j) < s.nontrivialIndex s.lengthWithoutIsoBlowups := by
    rw [hh, s.nontrivialIndex_lengthWithoutIsoBlowups]
    exact h1 (s'.nontrivialIndex j) $ s'.nontrivialIndex_lt_length hj
  exact s.nontrivialIndex_strictMono.lt_iff_lt.mp hlt
  intro j k hk hjk
  have hj1 := le_of_lt $ lt_of_lt_of_le hjk hk
  refine s.nontrivialIndex_strictMono.lt_iff_lt.mp ?_
  rw [hmu_ j hj1, hmu_ k hk]
  exact h2 (s'.nontrivialIndex j) (s'.nontrivialIndex k) (hle k hk) $ s'.nontrivialIndex_strictMono hjk
  have hh : s.nontrivialIndex (mu_ s'.lengthWithoutIsoBlowups) = s.nontrivialIndex s.lengthWithoutIsoBlowups := by
    rw [hmu_ s'.lengthWithoutIsoBlowups le_rfl, s'.nontrivialIndex_lengthWithoutIsoBlowups, h3, s.nontrivialIndex_lengthWithoutIsoBlowups]
  exact s.nontrivialIndex_strictMono.injective hh
  intro i hi
  constructor
  intro hx
  have hne :=
    (nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups ph_ s i).mpr $ (ne_top_iff_exists_mem_support _).mpr hx
  obtain ⟨j0, hj0, hrj0⟩ : ∃ j < s'.length, r j = s.nontrivialIndex i := by
    by_contra hcon
    exact h4 (s.nontrivialIndex i) (s.nontrivialIndex_lt_length hi) hcon $ (ne_top_iff_exists_mem_support _).mp hne
  have hcen : s'.center j0 ≠ ⊤ := by
    rw [h7 j0 hj0, comap_comp]
    exact comap_iso_hom_ne_top (e j0 $ le_of_lt hj0) _ $ center_comap_pullback_snd_ne_top_congr ph_ s hrj0 hne
  obtain ⟨k, hk1, hk2⟩ := s'.exists_nontrivialIndex_eq_of_center_ne_top hj0 hcen
  refine ⟨k, hk1, ?_⟩
  apply s.nontrivialIndex_strictMono.injective
  rwa [hmu_ k $ le_of_lt hk1, hk2]
  rintro ⟨j, hj, rfl⟩
  refine (ne_top_iff_exists_mem_support _).mp $ (nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups ph_ s $ mu_ j).mp ?_
  refine center_comap_pullback_snd_ne_top_congr ph_ s (hmu_ j $ le_of_lt hj) ?_
  intro hcc
  refine s'.center_nontrivialIndex_ne_top hj ?_
  rw [h7 (s'.nontrivialIndex j) $ s'.nontrivialIndex_lt_length hj, comap_comp, hcc,
    comap_top]
  intro j hj hr
  have hj1 := le_of_lt hj
  have hj2 := hj
  have haj1 := hle (j + 1) hj2
  have hstep := le_of_lt $ s'.nontrivialIndex_lt_succ j
  have hrr :=
    hrmono (s'.nontrivialIndex j) (s'.nontrivialIndex $ j + 1) hstep haj1
  refine pullback.hom_ext ?_ ?_
  have hL : (s'.withoutIsoBlowups.transitionMapSucc j ≫ (E j hj1).hom)
      ≫ pullback.fst ph_ (s.withoutIsoBlowups.projectionToBase $ mu_ j) = s'.withoutIsoBlowups.projectionToBase (j + 1) := by
    rw [assoc, hEfst j hj1]
    exact (s'.withoutIsoBlowups.projectionToBase_succ j).symm
  have hR : ((E (j + 1) hj2).hom ≫ s.withoutIsoBlowups.pullbackTransitionMap ph_ hr)
      ≫ pullback.fst ph_ (s.withoutIsoBlowups.projectionToBase $ mu_ j) = s'.withoutIsoBlowups.projectionToBase (j + 1) := by
    rw [assoc, SequenceOfBlowups.pullbackTransitionMap_fst, hEfst (j + 1) hj2]
  exact hL.trans hR.symm
  have hL := (assoc (s'.withoutIsoBlowups.transitionMapSucc j) (E j hj1).hom
        (pullback.snd ph_ $ s.withoutIsoBlowups.projectionToBase $ mu_ j)).trans
      (((whisker_eq (s'.withoutIsoBlowups.transitionMapSucc j) $ hEsnd0 j hj1).trans
          (eq_whisker (s'.withoutIsoBlowups_blowupMorphism j) _)).trans
        ((hdown (s'.nontrivialIndex j) (s'.nontrivialIndex $ j + 1) hstep haj1 _).trans
          ((whisker_eq _ $ pullbackTransitionMap_snd_assoc s ph_ hrr _).trans
            (whisker_eq _ $ whisker_eq _
              (transitionMap_comp_eqToIso s (hmu_ j hj1).symm (hmu_ (j + 1) hj2).symm hrr
                (s.nontrivialIndex_monotone hr))))))
  have hR := (assoc (E (j + 1) hj2).hom (s.withoutIsoBlowups.pullbackTransitionMap ph_ hr)
        (pullback.snd ph_ $ s.withoutIsoBlowups.projectionToBase $ mu_ j)).trans
      ((whisker_eq (E (j + 1) hj2).hom
          (SequenceOfBlowups.pullbackTransitionMap_snd s.withoutIsoBlowups ph_ hr)).trans
        ((comp_comp_eq_of_comp_eq (hEsnd0 (j + 1) hj2) $ s.withoutIsoBlowups.transitionMap hr).trans
          ((assoc _ _ _).trans
            ((whisker_eq _ $ assoc _ _ _).trans
              (whisker_eq _ $ whisker_eq _
                (whisker_eq _ $ s.withoutIsoBlowups_transitionMap hr))))))
  exact hL.trans hR.symm
  intro j hj
  have hj1 := le_of_lt hj
  have haj := s'.nontrivialIndex_lt_length hj
  refine m32 ?_ (comap_congr_morphism (hEsnd0 j hj1) $ s.center $ s.nontrivialIndex $ mu_ j).symm
  have hA := (center_comap_eqToIso_hom s (hmu_ j hj1).symm).symm
  have hB := comap_congr_idealSheaf (pullback.snd ph_ $ sbPrj s $ r $ s'.nontrivialIndex j) hA
  have hC := comap_congr_idealSheaf (e (s'.nontrivialIndex j) $ hle j hj1).hom hB
  have hD : cmI (s.center $ r $ s'.nontrivialIndex j)
        ((e (s'.nontrivialIndex j) $ hle j hj1).hom ≫
          pullback.snd ph_ (sbPrj s $ r $ s'.nontrivialIndex j))
      = cmI (cmI (s.center $ r $ s'.nontrivialIndex j)
          (pullback.snd ph_ $ sbPrj s $ r $ s'.nontrivialIndex j))
            (e (s'.nontrivialIndex j) $ hle j hj1).hom := by
    simp [comap_comp]
  have hE2 : cmI (s.center $ s.nontrivialIndex $ mu_ j)
        ((e (s'.nontrivialIndex j) $ hle j hj1).hom ≫
          pullback.snd ph_ (sbPrj s $ r $ s'.nontrivialIndex j) ≫
            (eqToIso $ congrArg s.schemeAt (hmu_ j hj1).symm).hom)
      = (cmI (s.center $ s.nontrivialIndex $ mu_ j)
          (pullback.snd ph_ (sbPrj s $ r $ s'.nontrivialIndex j) ≫
            (eqToIso $ congrArg s.schemeAt (hmu_ j hj1).symm).hom)).comap
              (e (s'.nontrivialIndex j) $ hle j hj1).hom := by
    simp [comap_comp]
  refine (((h7 (s'.nontrivialIndex j) haj).trans hD).trans hC).trans (hE2.trans ?_).symm
  simp [comap_comp]

end IsPullbackUpToEmptyCenters

end FunctorialResolution.EmbeddedResolution
end
section

open scoped TensorProduct


namespace FunctorialResolution.EmbeddedResolution

namespace SmoothChartRelativeDimension

section
variable {S R C T : Type} [CommRing S] [CommRing R] [CommRing C] [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T) (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s))
def tensorProductLiftRingHom : (R ⊗[S] C) →+* T :=
  letI : Algebra S T := (a.comp $ algebraMap S R).toAlgebra
  letI : Algebra R T := a.toAlgebra
  haveI : IsScalarTower S R T := of_algebraMap_eq fun _ => rfl
  (Algebra.TensorProduct.productMap (toAlgHom S R T)
      ({ toRingHom := b, commutes' := fun s => symm $ hab s } : C →ₐ[S] T)).toRingHom

theorem tensorProductLiftRingHom_tmul (x : R) (y : C) :
    tensorProductLiftRingHom a b hab (x ⊗ₜ[S] y) = a x * b y := by
  let _ := (a.comp $ algebraMap S R).toAlgebra
  let _ := a.toAlgebra
  have : IsScalarTower S R T := of_algebraMap_eq fun _ => rfl
  exact Algebra.TensorProduct.productMap_apply_tmul (toAlgHom S R T)
    ({ toRingHom := b, commutes' := fun s => sy_ $ hab s } : C →ₐ[S] T) x y
end

theorem exists_affineOpen_isStandardSmoothOfRelativeDimension {X Y : Sch}
    [IsAffine X] (r : ℕ) (h : Y ⟶ X)
    [AlgebraicGeometry.SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Opn Y) (_ : y ∈ V) (_ : IsAffineOpen V),
      IsStandardSmoothOfRelativeDimension r
        (CommRingCat.Hom.hom ((V.ι ≫ h).appTop)) := by
  obtain ⟨U, hU, V, hV, hyV, e, hss⟩ := ‹m158 r h›.1 y
  let _a7 := homOfLE (le_top : U ≤ ⊤)
  obtain ⟨f0, hf0le, hf0mem⟩ :=
    (isAffineOpen_top X).exists_basicOpen_le (⟨bsM h y, e hyV⟩ : U) (by trivial)
  set g : X.sec U :=
    (m23 (pMap X _a7.op)) f0 with hgdef
  set s : Y.sec V := (m23 (appLE h U V e)) g with hsdef
  let _a0 := m4 $ appLE h U V e
  have hsg : s = _a0 g := rfl
  have hbg :=
    basicOpen_res X f0 _a7.op
  have hbgf := tr_ hbg $ mpr_ inf_eq_right hf0le
  have hbs :=
    Scheme.basicOpen_appLE h V U e g
  have hyW : y ∈ Y.basicOpen s := by
    rw [hbs]
    refine ⟨hyV, ?_⟩
    show bsM h y ∈ X.basicOpen g
    rwa [hbgf]
  have hle2_ : Y.basicOpen s ≤ h ⁻¹ᵁ X.basicOpen g := by simp_all
  have hle3 : bOpn Y s ≤ preU h (⊤) := by
    intro z hz
    trivial
  have hmm : Submonoid.map _a0 (powers g)
      = powers s := by simp_all
  have hlocX :=
    hU.isLocalization_basicOpen g
  let _a5 := Γ(Y, bOpn Y s)
  have hlocY : IsLocalization
      (Submonoid.map _a0 (powers g))
      _a5 := by
    rw [hmm]
    exact hV.isLocalization_basicOpen s
  have hloc := isStandardSmoothOfRelativeDimension_localizationPreserves r
    _a0 (powers g)
    (Γ(X, bOpn X g)) _a5 hss
  have hle_sub : powers g ≤ Submonoid.comap _a0
      (Submonoid.map _a0 (powers g)) :=
    fun x hx => ⟨x, hx, rfl⟩
  let _a2 := appLE h (bOpn X g) (bOpn Y s) hle2_
  have arrow : appLE h U V e ≫ pMap Y (homOfLE (Y.basicOpen_le s)).op
      = pMap X (homOfLE (X.basicOpen_le g)).op ≫ _a2 := by
    rw [appLE_map, map_appLE]
  have key : IsLocalization.map _a5
        _a0 hle_sub
      = m4 _a2 := by
    refine IsLocalization.ringHom_ext (powers g) ?_
    rw [IsLocalization.map_comp]
    exact congrArg m4 arrow
  have hP := hloc
  rw [key] at hP
  let _a1 := homOfLE (le_top : bOpn X g ≤ ⊤)
  let _ :=
    (m4
      (pMap X _a1.op)).toAlgebra
  have :=
    (isAffineOpen_top X).isLocalization_of_eq_basicOpen f0
      _a1 hbgf
  have hsrc :=
    (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway r).1
  have hcomp0 :=
    hsrc _ f0 _ hP
  have hmap :=
    map_appLE h hle2_ _a1.op
  have hcomp : IsStandardSmoothOfRelativeDimension r
      (CommRingCat.Hom.hom (appLE h ⊤ (bOpn Y s) hle3)) := by
    rwa [← hmap, hom_comp]
  have hBeq : ((bOpn Y s).i ''ᵁ ⊤) = bOpn Y s := by simp
  have hclean : h.appTop ≫ (pMap Y (homOfLE le_top).op ≫ pMap Y (homOfLE (le_of_eq hBeq.symm)).op)
      = appLE h (⊤) (bOpn Y s) hle3 := by
    rw [← m222]
    rfl
  have hiso : ((bOpn Y s).i ≫ h).appTop ≫ (bOpn Y s).topIso.hom
      = appLE h ⊤ (bOpn Y s) hle3 := by
    rwa [comp_appTop, assoc, topIso_hom, ι_appTop]
  have hgoal :=
    (eq_comp_inv _).mpr hiso
  refine ⟨bOpn Y s, hyW, hV.basicOpen s, ?_⟩
  rw [hgoal]
  exact an1 (isStandardSmoothOfRelativeDimension_respectsIso (n := r)) _
    (bOpn Y s).topIso.symm.commRingCatIsoToRingEquiv hcomp

theorem exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension {S R B : CRC}
    (ι : S ⟶ R) (hio : Surjective ⇑(CommRingCat.Hom.hom ι)) (ph_ : R ⟶ B) (r : ℕ)
    (hph : IsStandardSmoothOfRelativeDimension r $ CommRingCat.Hom.hom ph_) :
    ∃ (B' : CRC) (σ : S ⟶ B') (ps_ : B' ⟶ B),
      IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        Surjective ⇑(CommRingCat.Hom.hom ps_) ∧
        CategoryTheory.IsPushout ι σ ph_ ps_ := by
  let _ := (m4 ι).toAlgebra
  let _ := (m4 ph_).toAlgebra
  let _ :=
    ((m4 ph_).comp $ m4 ι).toAlgebra
  have : IsScalarTower S R B :=
    of_algebraMap_eq fun _ => rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension r R B := hph
  obtain ⟨C, hCring, hCalg, f, hss, hfs, e, he⟩ :=
    exists_lift_of_isStandardSmoothOfRelativeDimension S R
      B r hio
  let _a0 := ofHom $ algebraMap S C
  have hcond : ι ≫ ph_ = _a0 ≫
      ofHom f.toRingHom := by
    exact hom_ext $ m48 fun s => sy_ $ f.commutes s
  have hcc : ∀ (c : PushoutCocone ι
        _a0) (s : S),
      (m4 c.inl) (algebraMap S R s)
        = (m4 c.inr) (algebraMap S C s) := fun c s =>
    congrArg (fun t => (m4 t) s) c.condition
  have facR : ∀ c : PushoutCocone ι
      _a0,
      ofHom f.toRingHom ≫ ofHom
          ((tensorProductLiftRingHom (m4 c.inl) (m4 c.inr) $ hcc c).comp
            e.symm.toAlgHom.toRingHom) = c.inr := by
    intro c
    refine hom_ext $ m48 fun z => ?_
    let _a1 := e.symm $ f z
    show tensorProductLiftRingHom (m4 c.inl) (m4 c.inr) (hcc c)
        _a1 = (m4 c.inr) z
    rw [show _a1 = (1 : R) ⊗ₜ[S] z from
      e.symm_apply_eq.mpr (he z).symm, tensorProductLiftRingHom_tmul, map_one, one_mul]
  refine ⟨m10 C, _a0,
    ofHom f.toRingHom, mpr_ (isStandardSmoothOfRelativeDimension_algebraMap r) hss, hfs, ?_⟩
  refine CategoryTheory.IsPushout.of_isColimit' ⟨hcond⟩
    (CategoryTheory.Limits.PushoutCocone.IsColimit.mk hcond
      (fun c => ofHom
        ((tensorProductLiftRingHom (m4 c.inl) (m4 c.inr) $ hcc c).comp
          e.symm.toAlgHom.toRingHom)) ?_ facR ?_)
  intro c
  refine hom_ext $ m48 fun x => ?_
  obtain ⟨s, rfl⟩ := hio x
  have key : ι ≫ (ph_ ≫ ofHom
      ((tensorProductLiftRingHom (m4 c.inl) (m4 c.inr) $ hcc c).comp
        e.symm.toAlgHom.toRingHom)) = ι ≫ c.inl := by
    rw [← assoc, hcond, assoc, facR c, ← c.condition]
  exact congrArg (fun t => (m4 t) s) key
  intro c m h1_ h2_
  refine hom_ext $ m48 fun b => ?_
  obtain ⟨z, rfl⟩ := hfs b
  exact congrArg (fun t => (m4 t) z)
    (tr_ h2_ (facR c).symm)

end SmoothChartRelativeDimension

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

namespace PresentedSmoothChart

end PresentedSmoothChart

end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable (k : Type) [Field k] (M n : ℕ)
def renameSumInl :
    MvU M k →+* MvPolynomial (UFS M n) k :=
  (rename
      (fun a : UFin M =>
        (up (inl a.down) : UFS M n))).toRingHom

theorem renameSumInl_C c :
    renameSumInl k M n (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [renameSumInl]

theorem renameSumInl_X a :
    renameSumInl k M n (MvPolynomial.X $ up a) =
      MvPolynomial.X (up (inl a) : UFS M n) := by
  simp [renameSumInl]

theorem pderiv_inr_X_inl i a :
    pderiv (up (inr i) : UFS M n)
        (MvPolynomial.X (up (inl a) : UFS M n) :
          MvPolynomial (UFS M n) k) = 0 :=by simp_all
theorem pderiv_inr_renameSumInl (i : Fin n)
    (p : MvU M k) :
    pderiv (up (inr i) : UFS M n)
        (renameSumInl k M n p) = 0 := by
  classical
  induction p using induction_on
  rename_i c
  simp [renameSumInl_C]
  rename_i q r hq hr
  simp [hq, hr]
  rename_i q a hq
  obtain ⟨a⟩ := a
  rw [map_mul, renameSumInl_X, pderiv_mul, hq, pderiv_inr_X_inl]
  simp

theorem projLeft_appTop_affineSpaceIndexedByToSpec_appTop
    y :
    appTop (projLeft k M n) (appTop (affineSpaceIndexedByToSpec k $ UFin M) y) =
      appTop (affineSpaceIndexedByToSpec k $ UFS M n) y := by
  have h2 : hAT ((projLeft k M n) ≫ affineSpaceIndexedByToSpec k (UFin M)) y
      = hAT (affineSpaceIndexedByToSpec k $ UFS M n) y := by
    rw [projLeft_comp_affineSpaceIndexedByToSpec]
  exact h2

theorem projLeft_appTop_mvPolynomialEquivGlobalSections_C c :
    appTop (projLeft k M n) (mvPolynomialEquivGlobalSections k (UFin M) $ MvPolynomial.C c) =
      mvPolynomialEquivGlobalSections k (UFS M n) (MvPolynomial.C c) := by
  rw [mvPolynomialEquivGlobalSections_C, mvPolynomialEquivGlobalSections_C, projLeft_appTop_affineSpaceIndexedByToSpec_appTop]

theorem projLeft_appTop_mvPolynomialEquivGlobalSections_X
    (a : UFin M) :
    appTop (projLeft k M n) (mvPolynomialEquivGlobalSections k (UFin M) $ MvPolynomial.X a) =
      mvPolynomialEquivGlobalSections k (UFS M n)
        (MvPolynomial.X (up (inl a.down) : UFS M n)) := by
  obtain ⟨a⟩ := a
  simp

theorem mvPolynomialEquivGlobalSections_symm_projLeft_appTop
    p :
    (mvPolynomialEquivGlobalSections k $ UFS M n).symm
        ((projLeft k M n).appTop $ mvPolynomialEquivGlobalSections k (UFin M) p) =
      renameSumInl k M n p := by
  let _c0 := mvPolynomialEquivGlobalSections k $ UFS M n
  let _a0 := projLeft k M n
  have key :
      (_c0.symm.toRingHom).comp
          (((hAT _a0).hom).comp
            ((mvPolynomialEquivGlobalSections k $ UFin M).toRingHom))
        = renameSumInl k M n := by
    apply ringHom_ext
    intro c
    show _c0.symm
        (hAT _a0
          (mvPolynomialEquivGlobalSections k (UFin M) $ m8 c))
        = renameSumInl k M n (m8 c)
    rw [projLeft_appTop_mvPolynomialEquivGlobalSections_C, symm_apply_apply, renameSumInl_C]
    intro a
    show _c0.symm
        (hAT _a0
          (mvPolynomialEquivGlobalSections k (UFin M) $ m7 a))
        = renameSumInl k M n (m7 a)
    rw [projLeft_appTop_mvPolynomialEquivGlobalSections_X, symm_apply_apply]
    simp [renameSumInl]
  exact congr_fun key p

theorem mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing :
    ((mvPolynomialEquivGlobalSections k $ UFS M n).symm.toRingHom).comp (mvPolynomialToSumCoordinateRing k M n) =
      eval₂Hom
        ((renameSumInl k M n).comp $ (mvPolynomialEquivGlobalSections k $ UFin M).symm.toRingHom)
        (fun i =>
          MvPolynomial.X (up (inr i) : UFS M n)) := by
  apply ringHom_ext
  intro t
  have h := mvPolynomialEquivGlobalSections_symm_projLeft_appTop k M n
    ((mvPolynomialEquivGlobalSections k $ UFin M).symm t)
  simp [apply_symm_apply] at h
  simpa using h
  intro i
  simp

theorem mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k $ UFin M, ⊤)) :
    (mvPolynomialEquivGlobalSections k $ UFS M n).symm (mvPolynomialToSumCoordinateRing k M n p) =
      eval₂
        ((renameSumInl k M n).comp $ (mvPolynomialEquivGlobalSections k $ UFin M).symm.toRingHom)
        (fun i : Fin n =>
          MvPolynomial.X (up (inr i) : UFS M n)) p :=
  congr_fun (mvPolynomialEquivGlobalSections_symm_comp_mvPolynomialToSumCoordinateRing k M n) p

theorem pderiv_inr_eval2_X_inr
    (f : Γ(affineSpaceIndexedBy k $ UFin M, ⊤) →+*
      MvPolynomial (UFS M n) k) (i : Fin n)
    (hf : ∀ t, pderiv (up (inr i) : UFS M n) (f t) = 0)
    (p : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k $ UFin M, ⊤)) :
    pderiv (up (inr i) : UFS M n)
        (eval₂ f
          (fun j : Fin n =>
            MvPolynomial.X (up (inr j) : UFS M n)) p) =
      eval₂ f
        (fun j : Fin n =>
          MvPolynomial.X (up (inr j) : UFS M n))
        (pderiv i p) := by
  classical
  induction p using induction_on
  simp_all
  simp_all
  rename_i q j hq
  let _a0 := UFS M n
  have hX : pderiv (up (m50 i) : _a0)
      (m7 (up (m50 j) : _a0) :
        MvPolynomial _a0 k) =
      eval₂ f
        (fun l =>
          m7 (up (m50 l) : _a0))
        (pderiv i $ m7 j) := by
    by_cases h : i = j
    subst h
    simp
    simp_all
  simp [eval₂_mul, eval₂_X, pderiv_mul,
    eval₂_add, hq, hX]
end





section
variable (k : Type) [Field k]
theorem jacobianDetSection_mvPolynomialToSumCoordinateRing (M n q : ℕ)
    (lift : Fin q → MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k $ UFin M, ⊤))
    (s : Fin q → Fin n) :
    jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) s =
      mvPolynomialToSumCoordinateRing k M n
        (det (Matrix.of fun i j : Fin q => pderiv (s i) $ lift j)) := by
  let _a0 := UFS M n
  have key : ∀ i j,
      jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) s i j =
        (mvPolynomialEquivGlobalSections k _a0).symm
          (mvPolynomialToSumCoordinateRing k M n $ pderiv (s i) $ lift j) := by
    intro i j
    have h0 : polynomialOfSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) j
        = (mvPolynomialEquivGlobalSections k _a0).symm (mvPolynomialToSumCoordinateRing k M n $ lift j) := rfl
    rw [jacobianMatrixOfSections_apply, h0, mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing, mvPolynomialEquivGlobalSections_symm_mvPolynomialToSumCoordinateRing]
    refine pderiv_inr_eval2_X_inr k M n
      ((renameSumInl k M n).comp $ (mvPolynomialEquivGlobalSections k $ UFin M).symm.toRingHom) (s i) ?_ $ lift j
    intro t
    rw [comp_apply]
    exact pderiv_inr_renameSumInl k M n (s i) _
  have hmat : jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) s =
      ((((mvPolynomialEquivGlobalSections k _a0).symm.toRingHom).comp
          (mvPolynomialToSumCoordinateRing k M n)).mapMatrix)
        (m53 fun i j => pderiv (s i) $ lift j) := by
    refine Matrix.ext fun i j => ?_
    simp [mapMatrix_apply, map_apply, of_apply, coe_comp,
      m116, toRingHom_eq_coe, coe_coe]
    exact key i j
  show mvPolynomialEquivGlobalSections k _a0
      (jacobianMatrixOfSections k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) s).det = _
  rw [hmat, ← map_det]
  simp

end

theorem smoothPullbackHasGraphChart : SmoothPullbackHasGraphChart := by
  intro k _ _ X Y A pX pY pA _ _ _ _ i _ _ M rh_ _ hrh_ r h _ _ y
  have : IsAffine X := isAffine_of_isAffineHom (f := i)
  obtain ⟨V, hyV, hVaff, B', ta_, jV, hta, hjV, hpb⟩ : ∃ (V : Opn Y) (_ : y ∈ V) (_ : IsAffineOpen V) (B' : CRC) (σ : Γ(A, ⊤) ⟶ B') (j : (V : Sch) ⟶ Spec B'), IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧ IsClosedImmersion j ∧ CategoryTheory.IsPullback j (opI V ≫ h) (Spec.map σ ≫ A.isoSpec.inv) i := by
    obtain ⟨V, hyV, hV, hsm⟩ :=
      SmoothChartRelativeDimension.exists_affineOpen_isStandardSmoothOfRelativeDimension r h y
    have : IsAffine V := hV
    let _a0 := appTop $ opI V ≫ h
    obtain ⟨B', σ, ps_, hsg_, hps_, hpo⟩ :=
      SmoothChartRelativeDimension.exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension
        (appTop i)
        (isAffine_surjective_of_isAffine i).2
        _a0 r hsm
    have S1 : CategoryTheory.IsPullback (Spec.map ps_)
        (Spec.map _a0) (Spec.map σ)
        (Spec.map (appTop i)) := hpo.op.map Scheme.Spec
    have L : CategoryTheory.IsPullback (V : Sch).isoSpec.hom (opI V ≫ h)
        (Spec.map _a0) X.isoSpec.hom :=
      of_horiz_isIso ⟨isoSpec_hom_naturality (opI V ≫ h)⟩
    have C1 := L.paste_horiz S1
    rw [isoSpec_hom_naturality i] at C1
    refine ⟨V, hyV, hV, B', σ, (V : Sch).isoSpec.hom ≫ Spec.map ps_, hsg_, ?_, ?_⟩
    have := spec_of_surjective ps_ hps_
    infer_instance
    have t : CategoryTheory.IsPullback (𝟙 (Spec B')) (Spec.map σ ≫ A.isoSpec.inv)
        (Spec.map σ) A.isoSpec.hom :=
      of_horiz_isIso ⟨by simp⟩
    let _m0 := (V : Sch).isoSpec.hom ≫ Spec.map ps_
    have p : _m0 ≫ (Spec.map σ ≫ A.isoSpec.inv)
        = (opI V ≫ h) ≫ i := by
      rw [← assoc, C1.w]
      simp
    have s : CategoryTheory.IsPullback
        (_m0 ≫ 𝟙 (Spec B')) (opI V ≫ h)
        (Spec.map σ) (i ≫ A.isoSpec.hom) := by
      rwa [comp_id]
    exact of_right s p t
  have := hjV
  let _ := (CommRingCat.Hom.hom ta_).toAlgebra
  have halg : (algebraMap Γ(A, ⊤) B') = CommRingCat.Hom.hom ta_ := rfl
  obtain ⟨⟨ι, ka_, hka_, hio, P, hPdim⟩⟩ := hta
  have := hio
  have := hka_
  let _ := Fintype.ofFinite ka_
  let _ := decEq ka_
  let _a12 := specHomOfGlobalSections A ta_
  have hgsmooth : Smooth _a12 :=
    by
      have hs : RingHom.Smooth (CommRingCat.Hom.hom ta_) := by
        let := (CommRingCat.Hom.hom ta_).toAlgebra
        have : Algebra.IsStandardSmooth Γ(A, ⊤) B' := ⟨⟨ι, ka_, hka_, hio, ⟨P⟩⟩⟩
        exact ⟨inferInstance, inferInstance⟩
      have h1 :=
        (AlgebraicGeometry.HasRingHomProperty.Spec_iff
          (P := @Smooth)).mpr hs
      have h2 : Smooth A.isoSpec.inv := inferInstance
      exact MorphismProperty.comp_mem (@Smooth) _ _ h1 h2
  have := hgsmooth
  obtain ⟨n, ev, hn⟩ : ∃ (n : ℕ) (_ : ι ≃ Fin n), card ι = n :=
    ⟨_, Finite.equivFin ι, rfl⟩
  obtain ⟨q, er, hq⟩ : ∃ (q : ℕ) (_ : ka_ ≃ Fin q), card ka_ = q :=
    ⟨_, Finite.equivFin ka_, rfl⟩
  have hdim' : card ι - card ka_ = r := hPdim
  have hle : card ka_ ≤ card ι := card_le_card_of_injective P.map P.map_inj
  have hnq : n = q + r := by omega
  obtain ⟨b, hb⟩ : ∃ b : Fin n → B', b = fun t => P.val (ev.symm t) := ⟨_, rfl⟩
  obtain ⟨rel, hrel_def⟩ : ∃ rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤),
      rel = fun j => rename ev (P.relation (er.symm j)) := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : Fin q → Fin n, s = fun j => ev (P.map (er.symm j)) := ⟨_, rfl⟩
  have hsinj : Function.Injective s := by
    intro a1_ a2_ hab
    simp only [hs_def] at hab
    exact er.symm.injective $ P.map_inj (ev.injective hab)
  have hbev : (b ∘ ev) = P.val := by
    funext x
    simp [hb]
  have hvb : (P.val ∘ ev.symm) = b := by
    funext t
    simp [hb]
  let _a7 := MvPolynomial ι Γ(A, ⊤)
  have heval : ∀ p : _a7,
      eval₂ (CommRingCat.Hom.hom ta_) b (rename ev p) =
        aeval P.val p := by
    intro p
    rw [eval₂_rename, hbev, aeval_def, halg]
  have hE : ∀ x : MvPolynomial (Fin n) Γ(A, ⊤),
      aeval P.val (rename ev.symm x) =
        eval₂ (CommRingCat.Hom.hom ta_) b x := by
    intro x
    rw [aeval_def, eval₂_rename, hvb, halg]
  have hkerP : ∀ x : _a7,
      aeval P.val x = 0 ↔ x ∈ span (range P.relation) := by
    intro x
    rw [P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    simp [mem_ker]
  have hrel0 : ∀ j : ka_, aeval P.val (P.relation j) = 0 := fun j =>
    (hkerP _).mpr (subset_span ⟨j, rfl⟩)
  have hsub : Ideal.map (rename ev) (span (range P.relation))
      ≤ span (range rel) := by
    rw [map_le_iff_le_comap, span_le]
    rintro z ⟨j, rfl⟩
    simp only [mem_coe, mem_comap]
    exact subset_span ⟨er j, by simp [hrel_def]⟩
  have hker : ker (eval₂Hom (CommRingCat.Hom.hom ta_) b) =
      span (range rel) := by
    apply le_antisymm
    intro x hx
    have hx' : eval₂ (CommRingCat.Hom.hom ta_) b x = 0 := by simp_all
    have h1 : rename ev.symm x ∈ span (range P.relation) :=
      (hkerP _).mp (by rw [hE x]; exact hx')
    have h2 := hsub $ mem_map_of_mem _ h1
    rw [rename_rename, self_comp_symm] at h2
    simpa using h2
    rw [span_le]
    rintro z ⟨j, rfl⟩
    simp only [mem_coe, mem_ker, MvPolynomial.coe_eval₂Hom, hrel_def]
    rw [heval]
    exact hrel0 _
  have hjacEntry : ∀ i0_ j0_ : Fin q,
      eval₂ (CommRingCat.Hom.hom ta_) b (pderiv (s i0_) (rel j0_)) =
        aeval P.val (P.jacobiMatrix (er.symm i0_) (er.symm j0_)) := by
    intro i0_ j0_
    simp only [hs_def, hrel_def]
    rw [pderiv_rename (f := ev) ev.injective, heval, P.jacobiMatrix_apply]
  have hdet : (Matrix.of fun i0_ j0_ : Fin q =>
        eval₂ (CommRingCat.Hom.hom ta_) b
          (pderiv (s i0_) (rel j0_))).det = P.jacobian := by
    have h1 : (Matrix.of fun i0_ j0_ : Fin q =>
          eval₂ (CommRingCat.Hom.hom ta_) b
            (pderiv (s i0_) (rel j0_)))
        = (P.jacobiMatrix.map (aeval P.val).toRingHom).submatrix
            er.symm er.symm := by
      refine Matrix.ext fun i0_ j0_ => ?_
      simp only [of_apply, submatrix_apply, map_apply,
        AlgHom.toRingHom_eq_coe, coe_coe]
      exact hjacEntry i0_ j0_
    rw [h1, det_submatrix_equiv_self, ← mapMatrix_apply, ← map_det]
    simpa [Algebra.Generators.algebraMap_apply] using P.jacobian_eq_jacobiMatrix_det.symm
  have hgen : ∀ x : B', ∃ p : MvPolynomial (Fin n) Γ(A, ⊤),
      eval₂ (CommRingCat.Hom.hom ta_) b p = x := by
    intro x
    refine ⟨rename ev (P.σ x), ?_⟩
    rw [heval]
    exact P.aeval_val_σ x
  choose lift hliftmap using fun j : Fin q => exists_mvPolynomial_map_appTop_eq k A M rh_ n q rel j
  let _a5 := specToAffineSpaceExtendCoords k A pA M rh_ ta_ n b
  have hDe_ : IsUnit (hAT _a5
      (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) s)) := by
    have _i20 : hAT (specToAffineSpaceExtendCoords k A pA M rh_ ta_ n b) (jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) s) = (GSpecIso B').inv (det (Matrix.of fun i j : Fin q => eval₂ ta_.hom b ((pderiv (s i)) (rel j)))) := by
      have hmap : ∀ i j : Fin q,
          (MvPolynomial.map (CommRingCat.Hom.hom (appTop rh_)))
              (pderiv (s i) (lift j)) = pderiv (s i) (rel j) := by
        intro i j
        rw [← pderiv_map, hliftmap j]
      have hM1 : ((MvPolynomial.map (CommRingCat.Hom.hom (appTop rh_))).mapMatrix
            (Matrix.of fun i j : Fin q => pderiv (s i) $ lift j))
          = Matrix.of fun i j : Fin q => pderiv (s i) (rel j) := by
        refine Matrix.ext fun i j => ?_
        simpa [mapMatrix_apply] using hmap i j
      have hM2 : ((eval₂Hom (CommRingCat.Hom.hom ta_) b).mapMatrix
            (Matrix.of fun i j : Fin q => pderiv (s i) $ rel j))
          = Matrix.of fun i j : Fin q =>
              eval₂ (CommRingCat.Hom.hom ta_) b (pderiv (s i) (rel j)) := by
        refine Matrix.ext fun i j => ?_
        simp [mapMatrix_apply]
      rw [jacobianDetSection_mvPolynomialToSumCoordinateRing k M n q lift s,
        specToAffineSpaceExtendCoords_appTop_mvPolynomial k A pA M rh_ ta_ n b hrh_]
      congr 1
      rw [map_det, hM1]
      show (eval₂Hom (CommRingCat.Hom.hom ta_) b)
          (det (Matrix.of fun i j : Fin q => pderiv (s i) $ rel j)) = _
      rw [map_det, hM2]
    rw [_i20]
    have h2 : IsUnit ((Matrix.of fun i0_ j0_ : Fin q =>
        eval₂ (CommRingCat.Hom.hom ta_) b
          ((pderiv (s i0_)) (rel j0_))).det) := by
      rw [hdet]
      exact P.jacobian_isUnit
    exact h2.map ((GSpecIso B').inv).hom
  let _a3 := _a12 ≫ pA
  have hpA'Sm : Smooth _a3 := by infer_instance
  have hpA'ft : LocallyOfFiniteType _a3 := by infer_instance
  have hpA'qc : QuasiCompact _a3 := by infer_instance
  refine ⟨V, hyV, hVaff, Spec B', _a3, inferInstance, hpA'Sm,
    hpA'ft, hpA'qc, _a12, hgsmooth, rfl, jV, hjV, hpb, n, q, hnq,
    _a5, isClosedImmersion_specToAffineSpaceExtendCoords k A pA M rh_ ta_ n b hrh_ hgen, specToAffineSpaceExtendCoords_comp_projLeft k A pA M rh_ ta_ n b hrh_, fun j => mvPolynomialToSumCoordinateRing k M n $ lift j,
    jacobianDetSection k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) s, ?_, preimage_basicOpen_specToAffineSpaceExtendCoords k A pA M rh_ ta_ n b _ hDe_, ?_⟩
  let e := rh_
  let σ := ta_
  let _c0 := (hAT e).hom
  let _c1 := hAT (specToAffineSpaceExtendCoords k A pA M e σ n b)
  let _c2 := mvPolynomialToSumCoordinateRing k M n
  let _s0 := (MvPolynomial.map _c0 : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (UFin M), ⊤) →+* MvPolynomial (Fin n) Γ(A, ⊤))
  have hmap : Surjective _s0 :=
    map_surjective _ (appTop_surjective_of_isClosedImmersion e)
  have hsurjS : Surjective _c2 := by
    have hcomp : affineSpaceSumToSpecPolynomialRing k M n ≫ specPolynomialRingToAffineSpaceSum k M n =
        𝟙 (affineSpaceIndexedBy k (UFS M n)) := by
      refine AffineSpace.hom_ext ?_ ?_
      apply AlgebraicGeometry.ext_of_isAffine
      apply appTop_ext
      intro t
      rw [assoc, id_comp, comp_affineSpaceIndexedByToSpec_eq, comp_appTop_apply_eq,
        comp_appTop_apply_eq, specHomOfGlobalSections_appTop, globalSectionsToPolynomialRing_apply, appTop_GaSpecIso_inv_eq_mvPolynomialToSumCoordinateRing,
        mvPolynomialToSumCoordinateRing_C, ← comp_appTop_apply_eq, projLeft_comp_affineSpaceIndexedByToSpec]
      rintro ⟨i⟩
      obtain a | j := i
      rw [comp_appTop_apply_eq, appTop_coord_inl_eq_C, appTop_GaSpecIso_inv_eq_mvPolynomialToSumCoordinateRing, mvPolynomialToSumCoordinateRing_C,
        projLeft_appTop_coord, id_appTop_apply]
      rw [comp_appTop_apply_eq, appTop_coord_inr_eq_X, appTop_GaSpecIso_inv_eq_mvPolynomialToSumCoordinateRing, mvPolynomialToSumCoordinateRing_X,
        id_appTop_apply]
    intro x
    let _m1 := hAT (specPolynomialRingToAffineSpaceSum k M n) x
    let _a0 := (GSpecIso (polynomialRingOverGlobalSections k M n)).hom _m1
    refine ⟨_a0, ?_⟩
    have hx : hAT (affineSpaceSumToSpecPolynomialRing k M n) _m1 = x := by
      rw [← comp_appTop_apply_eq, hcomp, id_appTop_apply]
    rw [← appTop_GaSpecIso_inv_eq_mvPolynomialToSumCoordinateRing k M n
      _a0,
      hom_inv_id_apply]
    exact hx
  have hio : Injective ((GSpecIso B').inv) := by
    intro x y hxy
    have h := congrArg (fun z => (GSpecIso B').hom z) hxy
    simpa using h
  let _m0 := Γ(affineSpaceIndexedBy k (UFin M), ⊤)
  let _a2 := MvPolynomial (Fin n) _m0
  have step1 : ker (_c1.hom.comp
        _c2) =
      Ideal.comap (MvPolynomial.map _c0) (span (range rel)) := by
    rw [← hker]
    ext p
    simp only [mem_ker, comp_apply, mem_comap]
    rw [(fun p => specToAffineSpaceExtendCoords_appTop_mvPolynomial k A pA M e σ n b hrh_ p) p]
    constructor
    intro h
    have h0 : eval₂ σ.hom b (MvPolynomial.map _c0 p) = 0 := by
      apply hio
      rw [h]
      simp
    simpa [mem_ker] using h0
    intro h
    have h0 : eval₂ σ.hom b (MvPolynomial.map _c0 p) = 0 := by
      simpa [mem_ker] using h
    rw [h0]
    simp
  have step2 : span (range rel) =
      Ideal.map (MvPolynomial.map _c0) (span (range lift)) := by
    rw [map_span]
    congr 1
    rw [← range_comp]
    exact congrArg range $ funext fun j => (hliftmap j).symm
  have step3 : Ideal.comap (MvPolynomial.map _c0)
        (Ideal.map (MvPolynomial.map _c0) (span (range lift))) =
      span (range lift) ⊔
        ker _s0 :=
    comap_map_of_surjective _ hmap _
  have step4 : ker _s0 =
      Ideal.map
        (MvPolynomial.C :
          _m0 →+*
            _a2)
        (ker _c0) :=
    ker_map _
  have hcomapker : Ideal.comap _c2
        (ker _c1.hom) =
      ker (_c1.hom.comp _c2) := by
    ext p
    simp [mem_ker, mem_comap]
  have hcompEq : _c2.comp
      (MvPolynomial.C :
        _m0 →+*
          _a2)
      = (hAT (projLeft k M n)).hom := by
    ext t
    exact mvPolynomialToSumCoordinateRing_C k M n t
  have main := map_comap_of_surjective _c2 hsurjS
    (ker _c1.hom)
  rw [hcomapker, step1, step2, step3, step4] at main
  rw [← main, Ideal.map_sup, map_span, map_map, hcompEq]
  have hrange : (_c2 '' range lift)
      = range fun j : Fin q => mvPolynomialToSumCoordinateRing k M n $ lift j := by
    rw [← range_comp]
    rfl
  rw [hrange, sup_comm]
  have _i1 : Function.Injective (sumVariableMap M n q s) := by
    rintro ⟨x⟩ ⟨y⟩ h
    have h' : elim (fun a : Fin M => inl a) (fun j : Fin q => inr $ s j) x
        = elim (fun a : Fin M => inl a) (fun j : Fin q => inr $ s j) y :=
      congrArg down h
    have hxy : x = y := by
      cases x with
      | inl a =>
        cases y with
        | inl b =>
          have hab : a = b := by simpa using h'
          exact congrArg inl hab
        | inr j => simp at h'
      | inr i =>
        cases y with
        | inl b => simp at h'
        | inr j =>
          simp only [elim_inr, Sum.inr.injEq] at h'
          exact congrArg inr $ hsinj h'
    exact congrArg up hxy
  have hsm : Smooth (specGraphAwayToAffineSpace k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) s) :=
    smooth_specMap_algebraMap_graphAlgebraAway (graphCoordinates k M n q fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) (sumVariableMap M n q s)
      _i1
  rw [graphMorphismToAffineSpace_basicOpen_jacobianDetSection_eq k M n q (fun j => mvPolynomialToSumCoordinateRing k M n $ lift j) s]
  infer_instance





theorem exists_ideal_eq_span_singleton_of_le {X : Sch} (I : ISD X)
    (U V : X.affineOpens) (e : (V : Opn X) ≤ (U : Opn X)) (t : (X.sec (U : Opn X)))
    (ht : I.ideal U = span {t}) :
    ∃ t' : (X.sec V), I.ideal V = span {t'} := by
  have e' := e
  have h := comap_ideal_eq_map_appLE I (𝟙 X) U V e'
  rw [comap_id] at h
  refine ⟨(appLE (𝟙 X) U V e').hom t, ?_⟩
  rw [h, ht, map_span, image_singleton]

private theorem restrict_basicOpen_mem_nonZeroDivisors {W : Sch} (P : W.affineOpens)
    (d : (W.sec (P : Opn W))) {u : (W.sec (P : Opn W))}
    (hu : u ∈ nonZeroDivisors (W.sec (P : Opn W))) :
    (W.presheaf.map (homOfLE $ W.basicOpen_le d).op).hom u
      ∈ nonZeroDivisors Γ(W, W.basicOpen d) := by
  have := P.2.isLocalization_basicOpen d
  have halg : (algebraMap (xSec W P) Γ(W, bOpn W d))
      = (pMap W (homOfLE $ W.basicOpen_le d).op).hom := rfl
  have h :=
    nonZeroDivisors_le_comap (M := powers d)
      (S := Γ(W, bOpn W d)) hu
  rwa [halg] at h

theorem mem_nonZeroDivisors_of_dvd {R : Type} [CommRing R] {a b : R}
    (hb : b ∈ nonZeroDivisors R) (hab : a ∣ b) : a ∈ nonZeroDivisors R := by
  obtain ⟨c, hc⟩ := hab
  have key : ∀ z, a * z = 0 → z = 0 := by
    intro z hz
    refine an1 (mp_ mem_nonZeroDivisors_iff hb) z ?_
    rw [hc, mul_assoc, mul_comm c z, ← mul_assoc, hz, zero_mul]
  exact mpr_ mem_nonZeroDivisors_iff ⟨key, fun z hz => key z (by rw [mul_comm]; exact hz)⟩

theorem eq_zero_of_locally_eq_zero {W : Sch} (U : Opn W) (x : (W.sec U))
    (h : ∀ w ∈ U, ∃ (P : Opn W) (hP : P ≤ U), w ∈ P ∧
      (W.presheaf.map (homOfLE hP).op).hom x = 0) : x = 0 := by
  classical
  choose P hP hmem hzero using h
  refine TopCat.Sheaf.eq_of_locally_eq' W.sheaf
    (fun w : { w : W // w ∈ U } => P w.1 w.2) U
    (fun w => homOfLE $ hP w.1 w.2) (fun w hw => Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hmem w hw⟩) x 0 ?_
  intro w
  rw [map_zero]
  exact hzero w.1 w.2

section
variable {X X1 S : Sch} (j : S ⟶ X)
theorem ker_le_ker_strictTransform_subschemeio_comp (pi_ : X1 ⟶ X) (Z : ISD X) :
    j.ker ≤ (subschemeι (Blowup.strictTransform pi_ Z j.ker) ≫ pi_).ker := by
  rw [ker_comp, q2,
    le_map_iff_comap_le]
  exact comap_le_strictTransform pi_ Z j.ker

section
variable [IsClosedImmersion j]
section
variable (pi_ : X1 ⟶ X) (Z : ISD X)
theorem exists_comp_eq_strictTransform_subschemeio_comp :
    ∃ q : subscheme (Blowup.strictTransform pi_ Z j.ker) ⟶ S,
      q ≫ j = subschemeι (Blowup.strictTransform pi_ Z j.ker) ≫ pi_ :=
  ⟨m64 j (siI (p6 pi_ Z j.ker) ≫ pi_)
      (ker_le_ker_strictTransform_subschemeio_comp j pi_ Z),
    lift_fac j _ _⟩

def strictTransformLiftOfClosedImmersion :
    subscheme (Blowup.strictTransform pi_ Z j.ker) ⟶ S :=
  (exists_comp_eq_strictTransform_subschemeio_comp j pi_ Z).choose

theorem strictTransformLiftOfClosedImmersion_comp :
    strictTransformLiftOfClosedImmersion j pi_ Z ≫ j = subschemeι (Blowup.strictTransform pi_ Z j.ker) ≫ pi_ :=
  (exists_comp_eq_strictTransform_subschemeio_comp j pi_ Z).choose_spec
end

theorem isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion [IsLocallyNoetherian X1]
    (pi_ : X1 ⟶ X) (Z : ISD X) (h : IsBlowupAlongIdealSheaf pi_ Z) :
    IsBlowupAlongIdealSheaf (strictTransformLiftOfClosedImmersion j pi_ Z) $ Z.comap j := by
  let _c0 := p6 pi_ Z j.ker
  have : QuasiCompact $ strictTransformio pi_ Z j.ker :=
    quasiCompact_strictTransformio_of_isLocallyNoetherian pi_ Z j.ker
  have hcomap : (Z.comap j).comap (strictTransformLiftOfClosedImmersion j pi_ Z)
      = (Z.comap pi_).comap _c0.si := by
    rw [← comap_comp, strictTransformLiftOfClosedImmersion_comp,
      comap_comp]
  refine ⟨?_, ?_⟩
  rw [hcomap]
  intro x
  obtain ⟨V, t, hxV, -, hVspan⟩ := h.1 $ _c0.subschemeι.base x
  refine ⟨⟨_c0.si.pre (V : Opn X1),
    V.2.preimage _c0.si⟩,
    (_c0.subschemeι.app (V : Opn X1)).hom t, hxV, ?_, ?_⟩
  have key : ∀ z : Γ(_c0.subscheme,
      _c0.si.pre (V : Opn X1)),
      z * (_c0.subschemeι.app (V : Opn X1)).hom t = 0 → z = 0 := by
    intro z hz
    have hinj : Injective
        ((_c0.subschemeObjIso V).hom.hom) := by
      intro A B hAB
      have h1 : (((_c0.subschemeObjIso V).hom ≫
          (_c0.subschemeObjIso V).inv).hom) A
          = (((_c0.subschemeObjIso V).hom ≫
          (_c0.subschemeObjIso V).inv).hom) B := by
        simp only [hom_comp, coe_comp, m116, hAB]
      simpa using h1
    have hcompo : (_c0.subschemeι.app (V : Opn X1))
        ≫ (_c0.subschemeObjIso V).hom
        = ofHom (m5 $ _c0.ideal V) := by
      rw [subschemeι_app, assoc, m114,
        comp_id]
    have hft : ((_c0.subschemeObjIso V).hom.hom)
        ((_c0.subschemeι.app (V : Opn X1)).hom t)
        = m5 (_c0.ideal V) t := by
      have h2 : (((_c0.subschemeι.app (V : Opn X1))
          ≫ (_c0.subschemeObjIso V).hom).hom) t
          = (_c0.subschemeObjIso V).hom.hom
            ((_c0.subschemeι.app (V : Opn X1)).hom t) := by
        rw [hom_comp]
        rfl
      rw [← h2, hcompo]
      rfl
    obtain ⟨z0, hz0_⟩ := mk_surjective
      (((_c0.subschemeObjIso V).hom.hom) z)
    have h1 : ((_c0.subschemeObjIso V).hom.hom) z *
        ((_c0.subschemeObjIso V).hom.hom)
          ((_c0.subschemeι.app (V : Opn X1)).hom t) = 0 := by
      rw [← map_mul, hz, map_zero]
    rw [hft, ← hz0_] at h1
    have h2 : m5 (_c0.ideal V) (z0 * t) = 0 := by simp_all
    have h3 :=
      (eq_zero_iff_mem).mp h2
    have h4 : z0 ∈ (p6 pi_ Z j.ker).ideal V := by
      let hf : t * z0 ∈ (p6 pi_ Z j.ker).ideal V := by rwa [mul_comm] at h3
      obtain ⟨n, hn⟩ := (mem_strictTransform_ideal_iff pi_ Z j.ker V t hVspan $ t * z0).mp hf
      refine (mem_strictTransform_ideal_iff pi_ Z j.ker V t hVspan z0).mpr ⟨n + 1, ?_⟩
      rwa [pow_succ, mul_assoc]
    have h5 : ((_c0.subschemeObjIso V).hom.hom) z = 0 := by
      rw [← hz0_]
      exact (eq_zero_iff_mem).mpr h4
    refine hinj ?_
    rw [h5, map_zero]
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun z hz => key z (by rw [mul_comm]; exact hz), key⟩
  rw [comap_ideal_eq_map_appLE (Z.comap pi_)
      _c0.si V
      ⟨_c0.si.pre (V : Opn X1),
        V.2.preimage _c0.si⟩ le_rfl,
    hVspan, map_span, appLE_eq_app, image_singleton]
  intro W g hg
  have hECg := hg
  rw [← comap_comp] at hECg
  obtain ⟨a, hacomp⟩ : ∃ a, a ≫ pi_ = g ≫ j :=
    ⟨h.lift (g ≫ j) hECg, h.lift_comp (g ≫ j) hECg⟩
  have hWcomap : (Z.comap j).comap g = (Z.comap pi_).comap a := by
    rw [← comap_comp, ← comap_comp, hacomp]
  have hDker : (j.ker).comap pi_ ≤ a.ker := by
    rw [← le_map_iff_comap_le, ← ker_comp, hacomp]
    apply le_ker_comp
  have hD'ker : p6 pi_ Z j.ker ≤ a.ker := by
    have hker : a.ker = ofIdeals
        (fun U => ker (a.app (U : Opn X1)).hom) := rfl
    rw [hker, le_ofIdeals_iff]
    intro V s hs
    rw [mem_ker]
    let _a19 := a.pre (V : Opn X1)
    refine eq_zero_of_locally_eq_zero _a19 ((a.app (V : Opn X1)).hom s) ?_
    intro w hw
    obtain ⟨V0, t0, hyV0, -, hV0span⟩ := h.1 $ a.base w
    obtain ⟨c, hcle, hcmem⟩ :=
      V.2.exists_basicOpen_le (⟨a.base w, hyV0⟩ : (V0 : Opn X1)) hw
    obtain ⟨P0, u, hwP0, hunzd, hP0span⟩ := hg w
    obtain ⟨d, hdle, hdmem⟩ :=
      P0.2.exists_basicOpen_le (⟨w, hcmem⟩ : (a.pre $ X1.basicOpen c)) hwP0
    let _a2 := (W.affineBasicOpen d : W.affineOpens)
    let _a3 := (X1.affineBasicOpen c : X1.affineOpens)
    let _a11 := (_a2 : Opn W)
    have hdle' : _a11
        ≤ a.pre (_a3 : Opn X1) := hdle
    have hPU' : _a11 ≤ _a19 :=
      fun z hz => X1.basicOpen_le c $ hdle hz
    have hCV : (_a3 : Opn X1) ≤ (V : Opn X1) :=
      X1.basicOpen_le c
    obtain ⟨t', ht'⟩ :=
      exists_ideal_eq_span_singleton_of_le (Z.comap pi_) V0 (X1.affineBasicOpen c) hcle t0 hV0span
    let _a1 := (pMap X1 (homOfLE hCV).op).hom s
    have hs1_ : _a1
        ∈ _c0.ideal (X1.affineBasicOpen c) := by
      rw [← map_ideal_basicOpen]
      exact mem_map_of_mem _ hs
    obtain ⟨n, hn⟩ := (mem_strictTransform_ideal_iff pi_ Z j.ker (X1.affineBasicOpen c) t' ht'
      _a1).mp hs1_
    let _a12 := a.app (_a3 : Opn X1)
    have hkerapp : _a12.hom
        (t' ^ n * _a1) = 0 := by
      have h1 := (le_def.mp hDker) (X1.affineBasicOpen c) hn
      exact RingHom.mem_ker.mp $ ideal_ker_le a _ h1
    let _a0 := appLE a ((X1.affineBasicOpen c : X1.affineOpens) : Opn X1) ((W.affineBasicOpen d : W.affineOpens) : Opn W) hdle'
    have hph : _a0
        = _a12
          ≫ pMap W (homOfLE hdle').op := rfl
    have hzero1 : _a0.hom
        (t' ^ n * _a1) = 0 := by
      rw [hph, hom_comp, comp_apply, hkerapp, map_zero]
    have hmulzero : (_a0.hom t') ^ n *
        _a0.hom
          _a1 = 0 := by
      rwa [← map_pow, ← map_mul]
    let _a5 := pMap W (homOfLE $ W.basicOpen_le d).op
    have hPspan : ((Z.comap pi_).comap a).ideal (W.affineBasicOpen d)
        = span {_a5.hom u} := by
      rw [← map_ideal_basicOpen, ← hWcomap, hP0span, map_span,
        image_singleton]
    have hPspan' : ((Z.comap pi_).comap a).ideal (W.affineBasicOpen d)
        = span {_a0.hom t'} := by
      rw [comap_ideal_eq_map_appLE (Z.comap pi_) a
          (X1.affineBasicOpen c) (W.affineBasicOpen d) hdle', ht', map_span,
        image_singleton]
    have hu'nzd : _a5.hom u
        ∈ nonZeroDivisors _ := restrict_basicOpen_mem_nonZeroDivisors P0 d hunzd
    have hdvd : _a0.hom t' ∣
        _a5.hom u := by
      have hmem : _a5.hom u
          ∈ span {_a0.hom t'} := by
        rw [← hPspan', hPspan]
        exact mem_span_singleton_self _
      exact mem_span_singleton.mp hmem
    have happLE : _a0.hom
        _a1 = 0 :=
      (mem_nonZeroDivisors_iff.mp $ Submonoid.pow_mem (nonZeroDivisors _) (mem_nonZeroDivisors_of_dvd hu'nzd hdvd) n).1 _ hmulzero
    refine ⟨_a11, hPU', hdmem, ?_⟩
    have h0 : ((pMap X1 (homOfLE hCV).op
          ≫ _a0).hom) s = 0 := by
      rwa [hom_comp, comp_apply]
    rw [map_appLE a hdle' (homOfLE hCV).op] at h0
    have hEq : (pMap W (homOfLE hPU').op).hom ((a.app (V : Opn X1)).hom s)
        = (appLE a (V : Opn X1)
            (_a2 : Opn W) hPU').hom s := rfl
    rwa [hEq]
  have hkerio : Scheme.Hom.ker _c0.si
      ≤ Scheme.Hom.ker a := by
    rwa [ker_subschemeι]
  have hbio : AlgebraicGeometry.IsClosedImmersion.lift
      _c0.si a hkerio
      ≫ _c0.si = a :=
    lift_fac _ _ _
  refine ⟨m64
    _c0.si a hkerio, ?_, ?_⟩
  have hfac : (m64
      _c0.si a hkerio
      ≫ strictTransformLiftOfClosedImmersion j pi_ Z) ≫ j = g ≫ j := by
    rw [assoc, strictTransformLiftOfClosedImmersion_comp, ← assoc, hbio, hacomp]
  exact (cancel_mono j).mp hfac
  intro y hy
  have h1 : (y ≫ _c0.si) ≫ pi_ = g ≫ j := by
    rw [assoc, ← strictTransformLiftOfClosedImmersion_comp, ← assoc, hy]
  have h2 : ((m64
      _c0.si a hkerio)
      ≫ _c0.si) ≫ pi_ = g ≫ j := by simp_all
  have h3 := h.hom_ext_of_comp_eq hECg h1 h2
  exact (cancel_mono _c0.si).mp h3
end
end

theorem isLocallyNoetherian_of_isBlowupAlongIdealSheaf {X X1 : Sch}
    [IsLocallyNoetherian X] (pi_ : X1 ⟶ X) (Z : ISD X)
    (h : IsBlowupAlongIdealSheaf pi_ Z) : IsLocallyNoetherian X1 := by
  have := blowupIsProper X X1 pi_ Z h
  exact isLocallyNoetherian pi_

theorem strictTransformIsBlowupOfClosedSubscheme : StrictTransformIsBlowupOfClosedSubscheme := by
  intro X X1 S hX j hj pi_ Z hpi_ _
  have := hX
  have := hj
  have := isLocallyNoetherian_of_isBlowupAlongIdealSheaf pi_ Z hpi_
  exact ⟨strictTransformLiftOfClosedImmersion j pi_ Z, strictTransformLiftOfClosedImmersion_comp j pi_ Z,
    isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion j pi_ Z hpi_⟩

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

theorem map_mem_nonZeroDivisors_of_flat {R S : Type} [CommRing R] [CommRing S]
    (ph_ : R →+* S) (hph : ph_.Flat) {s : R} (hs : s ∈ nonZeroDivisors R) :
    ph_ s ∈ nonZeroDivisors S := by
  let _ := ph_.toAlgebra
  have : Module.Flat R S := hph
  have hmul : ∀ x, ph_ s * x = s • x := by
    intro x
    rw [smul_def, algebraMap_toAlgebra]
  have hL : Injective $ mulLeft R s := by
    intro a b hab
    have h1 : s * a = s * b := by
      simpa only [mulLeft_apply] using hab
    have h2 : s * (a - b) = 0 := by rw [mul_sub, h1, sub_self]
    exact mp_ sub_eq_zero $ (an1 $ mp_ mem_nonZeroDivisors_iff hs) _ h2
  have key : ∀ t, ph_ s * t = 0 → t = 0 := by
    intro t ht
    have hsmul : s • t = 0 := by rw [← hmul t]
                                 exact ht
    have e1 : TensorProduct.tmul R s t = 0 := by
      have h3 : TensorProduct.tmul R s t = TensorProduct.tmul R 1 (s • t) := by
        rw [← smul_tmul, smul_eq_mul, mul_one]
      rw [h3, hsmul, tmul_zero]
    let _a0 := (mulLeft R s).rTensor S
    let _a1 := TensorProduct.tmul R (1 : R) t
    have e0 : _a0 _a1
        = _a0 0 := by
      rwa [rTensor_tmul, map_zero, mulLeft_apply, mul_one]
    let _a3 := lid R S
    have h2 : _a3 _a1
        = _a3 0 := by rw [(Module.Flat.rTensor_preserves_injective_linearMap (M := S) _ hL) e0]
    rwa [lid_tmul, one_smul, map_zero] at h2
  exact mpr_ mem_nonZeroDivisors_iff
    ⟨key, fun t ht => key t (by rw [mul_comm]; exact ht)⟩

private theorem exists_affineOpen_mem_le {Y : Sch} (y : Y) (W : Opn Y) (hy : y ∈ W) :
    ∃ V : Y.affineOpens, y ∈ (V : Opn Y) ∧ (V : Opn Y) ≤ W := by
  obtain ⟨V, hVmem, hyV, hVle⟩ :=
    isBasis_iff_nbhd.mp Y.isBasis_affineOpens hy
  exact ⟨⟨V, hVmem⟩, hyV, hVle⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat {X Y : Sch} {D : ISD X}
    (hD : IsLocallyGeneratedByNonZeroDivisor D) (f : Y ⟶ X) [Flat f] :
    IsLocallyGeneratedByNonZeroDivisor $ D.comap f := by
  unfold IsLocallyGeneratedByNonZeroDivisor at hD ⊢
  intro y
  obtain ⟨U, s, hxU, hs, hUs⟩ := hD $ bsM f y
  obtain ⟨V, hyV, hVle⟩ :=
    EmbeddedResolution.exists_affineOpen_mem_le y (preU f U)
      (show y ∈ preU f U from hxU)
  have hU2 := U.2
  have hV2 := V.2
  let _m0 := appLE f U V hVle
  have hflat : _m0.hom.Flat := by
    apply flat_appLE <;> assumption
  refine ⟨V, _m0.hom s, hyV, _root_.FunctorialResolution.EmbeddedResolution.map_mem_nonZeroDivisors_of_flat _ hflat hs, ?_⟩
  rw [comap_ideal_eq_map_appLE D f U V hVle, hUs, map_span,
    image_singleton]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.pullback_snd_of_flat {X Y B : Sch} {pi_ : B ⟶ X}
    {J : ISD X} (h : IsBlowupAlongIdealSheaf pi_ J) (g : Y ⟶ X) [Flat g] :
    IsBlowupAlongIdealSheaf (pullback.snd pi_ g) $ J.comap g := by
  let _a0 := pullback.fst pi_ g
  have e1 : (cmI J g).comap (pullback.snd pi_ g)
      = (cmI J pi_).comap _a0 := by
    rw [← comap_comp, ← comap_comp,
      pullback.condition]
  constructor
  rw [e1]
  exact h.1.comap_of_flat _a0
  intro W m hm
  have hm' := hm
  rw [← comap_comp] at hm'
  obtain ⟨b, hb, hbuniq⟩ := an2 h W (m ≫ g) hm'
  refine ⟨pullback.lift b m hb, pullback.lift_snd b m hb, ?_⟩
  intro a ha
  refine pullback.hom_ext ?_ ?_
  rw [pullback.lift_fst]
  refine hbuniq _ ?_
  show (a ≫ _a0) ≫ pi_ = m ≫ g
  rw [assoc, pullback.condition, ← assoc, ha]
  rw [pullback.lift_snd, ha]

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_isPullback_of_flat {X Y B P : Sch} {pi_ : B ⟶ X}
    {J : ISD X} (h : IsBlowupAlongIdealSheaf pi_ J) (g : Y ⟶ X) [Flat g]
    {p : P ⟶ B} {q : P ⟶ Y} (hsq : IsPullback p q pi_ g) :
    IsBlowupAlongIdealSheaf q $ J.comap g := by
  have h4 := (h.pullback_snd_of_flat g).iso_hom_comp hsq.isoPullback
  rwa [hsq.isoPullback_hom_snd] at h4

theorem _root_.FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.exists_isPullback_of_flat {X Y B B' : Sch} {pi_ : B ⟶ X}
    {J : ISD X} (h : IsBlowupAlongIdealSheaf pi_ J) (g : Y ⟶ X) [Flat g]
    {pi' : B' ⟶ Y} (h' : IsBlowupAlongIdealSheaf pi' $ J.comap g) :
    ∃ q : B' ⟶ B, q ≫ pi_ = pi' ≫ g ∧ IsPullback q pi' pi_ g := by
  obtain ⟨e, he⟩ := h'.exists_iso $ h.pullback_snd_of_flat g
  let _a0 := isoH e ≫ pullback.fst pi_ g
  have hc : _a0 ≫ pi_ = pi' ≫ g := by
    rw [assoc, pullback.condition, ← assoc, he]
  exact ⟨_a0, hc, of_iso_pullback ⟨hc⟩ e rfl he⟩

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite


namespace FunctorialResolution.EmbeddedResolution

variable {Y : Sch}

section
variable {X' Y' : Sch} (f : X' ⟶ Y')
theorem coe_image_of_isOpenImmersion
    [IsOpenImmersion f] (V : Opn X') :
    ((f ''ᵁ V : Opn Y') : Set Y') = f.base '' (V : Set X') := rfl

private theorem basicOpen_appLE {U : Opn Y'}
    {V : Opn X'} (h : V ≤ f ⁻¹ᵁ U) (r : (Y'.sec U)) :
    X'.basicOpen ((appLE f U V h).hom r) = V ⊓ f ⁻¹ᵁ (Y'.basicOpen r) := by
  have h1 : (appLE f U V h).hom r
      = (pMap X' (homOfLE h).op).hom ((f.app U).hom r) := rfl
  rw [h1, basicOpen_res, preimage_basicOpen]

theorem coe_preimage_opens (V : Opn Y') :
    ((f ⁻¹ᵁ V : Opn X') : Set X') = f.base ⁻¹' (V : Set Y') := rfl
end

section
variable {Y' : Sch}
theorem mul_ideal_apply (F G : ISD Y')
    U : (F * G).ideal U = F.ideal U * G.ideal U := rfl

section
variable (F : ISD Y')
theorem exists_ideal_eq_span_singleton_congr
    {W W' : Y'.affineOpens} (hW : W = W')
    (h : ∃ f : (Y'.sec W'), F.ideal W' = span {f}) :
    ∃ f : (Y'.sec W), F.ideal W = span {f} := by
  subst hW
  exact h

theorem exists_basicOpen_ideal_eq_span_singleton
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (U : Y'.affineOpens) (y : Y')
    (hy : y ∈ (U : Opn Y')) :
    ∃ g : (Y'.sec U), y ∈ Y'.basicOpen g ∧
      ∃ f : Γ(Y', Y'.affineBasicOpen g), F.ideal (Y'.affineBasicOpen g) = span {f} := by
  obtain ⟨V, fV, hyV, hfV, hFV⟩ := hF y
  obtain ⟨g, h, heq, hyg⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩
  refine ⟨g, hyg, ?_⟩
  have habo : Y'.affineBasicOpen g = Y'.affineBasicOpen h := m26 heq
  refine exists_ideal_eq_span_singleton_congr F habo ?_
  have hmap := F.map_ideal_basicOpen V h
  rw [hFV, map_span, image_singleton] at hmap
  exact ⟨_, sy_ hmap⟩

theorem pow_ideal_apply n
    U : (F ^ n).ideal U = F.ideal U ^ n :=by simp_all
end

section
variable (U : Opn Y')
noncomputable def sectionsOpensImageIso
    (V : U.toScheme.Opens) : Γ(Y', ι U ''ᵁ V) ≅ (U.toScheme.sec V) := U.ι.appIso V

theorem restrictAppIso_hom (V : U.toScheme.Opens) :
    hom (sectionsOpensImageIso U V)
      = U.ι.appLE (ι U ''ᵁ V) V (U.ι.preimage_image_eq V).ge :=
  appIso_hom' U.i V

theorem range_opensio :
    range U.ι.base = (U : Set Y') := U.range_ι

theorem image_opensio_le (V : U.toScheme.Opens) :
    (ι U ''ᵁ V : Opn Y') ≤ U := by
  intro z hz
  have hz' : z ∈ opIb U '' V := hz
  obtain ⟨w, -, rfl⟩ := hz'
  have hr : opIb U w ∈ range U.ib := mem_range_self w
  rwa [range_opensio] at hr
end
end

section
variable {Y : Sch}

theorem span_eq_top_of_forall_exists_mem_basicOpen {U : Opn Y}
    (hU : IsAffineOpen U) (s : Set $ Y.sec U)
    (h : ∀ x : Y, x ∈ U → ∃ f : s, x ∈ Y.basicOpen (f : (Y.sec U))) :
    span s = ⊤ := by
  rw [← self_le_iSup_basicOpen_iff hU]
  intro x hx
  exact mpr_ mem_iSup $ h x hx

section
variable {F J J' : ISD Y} (h : F * J ≤ F * J') (W : Y.affineOpens)
include h
theorem mul_ideal_le_mul_ideal :
    F.ideal W * J.ideal W ≤ F.ideal W * J'.ideal W := h W

theorem ideal_le_ideal_of_mul_le_mul t
    (hFW : F.ideal W = span {t}) (ht : t ∈ nonZeroDivisors (Y.sec (W : Opn Y))) :
    J.ideal W ≤ J'.ideal W := by
  intro b hb
  have h1 : t * b ∈ F.ideal W * J.ideal W := by
    rw [hFW]
    exact mul_mem_mul (mem_span_singleton_self t) hb
  have h2 := mul_ideal_le_mul_ideal h W h1
  rw [hFW, mem_span_singleton_mul] at h2
  obtain ⟨j, hj, hje⟩ := h2
  have h3 : (b - j) * t = 0 := by simp_all
  rwa [eq_of_sub_eq_zero $ (mp_ mem_nonZeroDivisors_iff ht).2 (b - j) h3]
end

end

section
variable {R : Type} [CommRing R]
theorem mem_colon_span (I : Ideal R) s
    x (h : ∀ g ∈ s, x * g ∈ I) : x ∈ I.colon (Submodule.span R s) := by
  refine mem_colon.2 ?_
  intro p hp
  rw [smul_eq_mul]
  induction hp using span_induction with
  | mem g hg => exact h g hg
  | zero => rw [mul_zero]; exact zero_mem I
  | add y z _ _ ihy ihz => rw [mul_add]; exact add_mem ihy ihz
  | smul c y _ ih =>
    rw [smul_eq_mul, ← mul_assoc, mul_comm x c, mul_assoc]
    exact I.mul_mem_left c ih

theorem span_singleton_mul_colon {P J : Ideal R}
    (hP : ∃ f : R, P = span {f}) (hJ : J ≤ P) : P * J.colon P = J := by
  obtain ⟨f, rfl⟩ := hP
  refine le_antisymm ?_ ?_
  rw [mul_le]
  intro a ha b hb
  have hb' := mp_ mem_colon hb a ha
  rw [smul_eq_mul] at hb'
  rwa [mul_comm a b]
  intro y hy
  obtain ⟨c, rfl⟩ := mp_ mem_span_singleton' $ hJ hy
  have hc : c ∈ J.colon (span {f}) := by simp_all
  have hmem := mul_mem_mul (mem_span_singleton_self f) hc
  rwa [mul_comm f c] at hmem
end

section
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (r : R) [IsLocalization.Away r S]
include r
theorem exists_pow_mul_mem_of_algebraMap_mem_map (I : Ideal R) x
    (hx : algebraMap R S x ∈ Ideal.map (algebraMap R S) I) : ∃ n, r ^ n * x ∈ I := by
  rw [mem_map_algebraMap_iff (M := powers r) (S := S)] at hx
  obtain ⟨w, hy⟩ := hx
  rw [← map_mul] at hy
  obtain ⟨c, hc⟩ := mp_ (eq_iff_exists (M := powers r) (S := S)) hy
  obtain ⟨p, hp⟩ : ∃ p, r ^ p = c := c.2
  obtain ⟨q, hq⟩ : ∃ q, r ^ q = w.2 := w.2.2
  refine ⟨p + q, ?_⟩
  have h2 : r ^ (p + q) * x = c * w.1 := by
    rw [pow_add, hp, hq, ← hc]
    ring
  rw [h2]
  exact I.mul_mem_left _ w.1.2

theorem map_colon_eq_colon_map_away (I J : Ideal R) (hJ : J.FG) :
    Ideal.map (algebraMap R S) (I.colon J) =
      (Ideal.map (algebraMap R S) I).colon (Ideal.map (algebraMap R S) J) := by
  let _a5 := algebraMap R S
  let _a1 := m6 _a5 $ I.colon J
  refine le_antisymm ?_ ?_
  have hsub : _a1 * m6 _a5 J ≤
      m6 _a5 I := by
    rw [← m220]
    refine map_mono $ Ideal.mul_le.2 ?_
    intro a ha b hb
    have ha' := mp_ mem_colon ha b hb
    rwa [smul_eq_mul] at ha'
  intro z hz
  refine mem_colon.2 ?_
  intro p hp
  rw [smul_eq_mul]
  exact hsub $ mul_mem_mul hz hp
  intro b hb
  obtain ⟨s, hs⟩ := hJ
  obtain ⟨w, hab⟩ := surj (M := powers r) b
  have key : ∀ g ∈ s, ∃ n, r ^ n * (w.1 * g) ∈ I := by
    intro g hg
    have hgJ : g ∈ J := by
      rw [← hs]
      exact Submodule.subset_span hg
    have h1 := mp_ mem_colon hb (algebraMap R S g) $ mem_map_of_mem _ hgJ
    rw [smul_eq_mul] at h1
    have h2 : algebraMap R S (w.1 * g) ∈ m6 _a5 I := by
      have heq : algebraMap R S (w.1 * g) =
          b * algebraMap R S g * algebraMap R S w.2 := by
        rw [map_mul, ← hab]
        ring
      rw [heq]
      exact mul_mem_right _ _ h1
    exact exists_pow_mul_mem_of_algebraMap_mem_map r I (w.1 * g) h2
  choose! n hn using key
  let _a0 := r ^ (s.sup n)
  have hNa : _a0 * w.1 ∈ I.colon J := by
    rw [← hs]
    refine mem_colon_span I (s) (_a0 * w.1) ?_
    intro g hg
    let _a4 := r ^ (s.sup n - n g)
    have hpow : _a4 * r ^ (n g) = _a0 := by
      rw [← pow_add, sub_add_cancel $ le_sup $ Finset.mem_coe.mp hg]
    have hre : _a0 * w.1 * g = _a4 * (r ^ (n g) * (w.1 * g)) := by
      rw [← hpow]
      ring
    rw [hre]
    exact I.mul_mem_left _ $ hn g hg
  let _a2 := w.2
  obtain ⟨v, hv⟩ := (map_units (M := powers r) S ⟨_a0 * _a2, mul_mem (pow_mem (Submonoid.mem_powers r) _) w.2.2⟩).exists_right_inv
  let _m0 := _a0 * _a2
  have hb2 : b * algebraMap R S _m0 ∈
      _a1 := by
    have heq : b * algebraMap R S _m0 =
        algebraMap R S (_a0 * w.1) := by
      rw [map_mul, map_mul, ← hab]
      ring
    rw [heq]
    exact mem_map_of_mem _ hNa
  have hbv := mul_mem_right v _a1 hb2
  rwa [mul_assoc, hv, mul_one] at hbv
end

section
variable [IsLocallyNoetherian Y] (I' F : ISD Y)
theorem idealSheafColon_ideal_map_basicOpen (U : Y.affineOpens) f :
    Ideal.map (CommRingCat.Hom.hom $ Y.presheaf.map (homOfLE $ Y.basicOpen_le f).op)
        ((I'.ideal U).colon $ F.ideal U) =
      (I'.ideal $ Y.affineBasicOpen f).colon (F.ideal $ Y.affineBasicOpen f) := by
  have := m188 U
  have := U.2.isLocalization_basicOpen f
  have key := map_colon_eq_colon_map_away (S := Γ(Y, bOpn Y f)) f (I'.ideal U) (F.ideal U)
    (m187 $ F.ideal U)
  rwa [← I'.map_ideal_basicOpen U f, ← F.map_ideal_basicOpen U f]

def idealSheafColon :
    IdealSheafData Y where
  ideal U := (I'.ideal U).colon $ F.ideal U
  map_ideal_basicOpen := idealSheafColon_ideal_map_basicOpen I' F

@[simp]
theorem idealSheafColon_ideal
    (U : Y.affineOpens) :
    (idealSheafColon I' F).ideal U = (I'.ideal U).colon (F.ideal U) :=
  rfl
end

theorem span_eq_top_of_cover_basicOpen {Y' : Sch} (U : Y'.affineOpens)
    (T : Set $ Y'.sec U)
    (hcov : ∀ y : Y', y ∈ (U : Opn Y') → ∃ g ∈ T, y ∈ Y'.basicOpen g) :
    span T = ⊤ := by
  refine span_eq_top_of_forall_exists_mem_basicOpen U.2 T ?_
  intro y hy
  obtain ⟨g, hgT, hyg⟩ := hcov y hy
  exact ⟨⟨g, hgT⟩, hyg⟩

theorem exists_pow_mul_mem_mul_colon {Y' : Sch} [IsLocallyNoetherian Y']
    (F I' : ISD Y') (hIle : ∀ U : Y'.affineOpens, I'.ideal U ≤ F.ideal U)
    (U : Y'.affineOpens) x (hx : x ∈ I'.ideal U) g
    f
    (hf : F.ideal (Y'.affineBasicOpen g) = span {f}) :
    ∃ n, g ^ n * x ∈ F.ideal U * (I'.ideal U).colon (F.ideal U) := by
  let _c0 := m4 $ pMap Y' (homOfLE $ Y'.basicOpen_le g).op
  have := U.2.isLocalization_basicOpen g
  have h1 : Ideal.map _c0
      (F.ideal U * (I'.ideal U).colon (F.ideal U)) = I'.ideal (Y'.affineBasicOpen g) := by
    rw [Ideal.map_mul, F.map_ideal_basicOpen U g,
      idealSheafColon_ideal_map_basicOpen I' F U g]
    exact span_singleton_mul_colon ⟨f, hf⟩ $ hIle $ Y'.affineBasicOpen g
  have h2 : _c0 x ∈
      Ideal.map _c0
        (F.ideal U * (I'.ideal U).colon (F.ideal U)) := by
    rw [h1, ← I'.map_ideal_basicOpen U g]
    exact mem_map_of_mem _ hx
  exact exists_pow_mul_mem_of_algebraMap_mem_map g _ x h2

section
variable [hv0_0 : IsLocallyNoetherian Y] {F I' : ISD Y} (hF : IsLocallyGeneratedByNonZeroDivisor F) (hI : I' ≤ F)
include hv0_0 hF hI
theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.mul_idealSheafColon :
    F * EmbeddedResolution.idealSheafColon I' F = I' := by
  refine m29 $ funext ?_
  intro U
  rw [EmbeddedResolution.mul_ideal_apply, EmbeddedResolution.idealSheafColon_ideal]
  refine le_antisymm ?_ ?_
  rw [mul_le]
  intro a ha b hb
  have hb' := mp_ mem_colon hb a ha
  rw [smul_eq_mul] at hb'
  rwa [mul_comm a b]
  intro x hx
  have hspan : span {g : (Y.sec U) | ∃ f : Γ(Y, Y.affineBasicOpen g),
      F.ideal (Y.affineBasicOpen g) = span {f}} = ⊤ := by
    refine EmbeddedResolution.span_eq_top_of_cover_basicOpen U _ ?_
    intro y hy
    obtain ⟨g, hyg, hfg⟩ := EmbeddedResolution.exists_basicOpen_ideal_eq_span_singleton F hF U y hy
    exact ⟨g, hfg, hyg⟩
  refine mem_of_span_eq_top_of_smul_pow_mem _ _ hspan x ?_
  intro r
  obtain ⟨f, hf⟩ := r.2
  obtain ⟨n, hn⟩ := EmbeddedResolution.exists_pow_mul_mem_mul_colon F I' hI U x hx r f hf
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.exists_mul_eq :
    ∃ J, F * J = I' :=
  ⟨EmbeddedResolution.idealSheafColon I' F, hF.mul_idealSheafColon hI⟩
end

section
variable {F J J' : ISD Y} (hF : IsLocallyGeneratedByNonZeroDivisor F)
include hF
theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_mul_le_mul (h : F * J ≤ F * J') : J ≤ J' := by
  refine (fun H => H) fun U => ?_
  intro b hb
  have hU := U.2
  have hcover :
      span {g : (Y.sec U) | ∃ n, g ^ n * b ∈ J'.ideal U} = ⊤ := by
    refine EmbeddedResolution.span_eq_top_of_forall_exists_mem_basicOpen hU _ ?_
    intro x hx
    obtain ⟨V, t, hxV, htz, hFt⟩ : ∃ (W : affO Y) (t : Y.sec (W : Opn Y)), x ∈ (W : Opn Y) ∧ t ∈ nonZeroDivisors (W : Opn Y).sec ∧ F.ideal W = span {t} := by
      unfold Blowup.IsLocallyGeneratedByNonZeroDivisor at hF
      exact hF x
    have hxUV : x ∈ (U : Opn Y) ⊓ (V : Opn Y) := ⟨hx, hxV⟩
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU V.2 x hxUV
    have hWfg : Y.affineBasicOpen f = Y.affineBasicOpen g := m26 hfg
    have hcan : J.ideal (Y.affineBasicOpen f) ≤ J'.ideal (Y.affineBasicOpen f) := by
      rw [hWfg]
      refine EmbeddedResolution.ideal_le_ideal_of_mul_le_mul h (Y.affineBasicOpen g)
        ((pMap Y (homOfLE $ Y.basicOpen_le g).op).hom t) ?_ ?_
      rw [← F.map_ideal_basicOpen V g, hFt, map_span, image_singleton]
      rfl
      have := V.2.isLocalization_basicOpen g
      exact nonZeroDivisors_le_comap (.powers g) Γ(Y, bOpn Y g) htz
    let _s0 := pMap Y (homOfLE $ Y.basicOpen_le f).op
    have hbW : _s0.hom b
        ∈ J.ideal (Y.affineBasicOpen f) := by
      rw [← J.map_ideal_basicOpen U f]
      exact mem_map_of_mem _ hb
    have hbW2 : _s0.hom b
        ∈ m6 _s0.hom (J'.ideal U) := by
      have hbW3 := hcan hbW
      rwa [← J'.map_ideal_basicOpen U f] at hbW3
    have := hU.isLocalization_basicOpen f
    obtain ⟨n, hn⟩ :=
      EmbeddedResolution.exists_pow_mul_mem_of_algebraMap_mem_map (S := Γ(Y, bOpn Y f)) f (J'.ideal U) b hbW2
    exact ⟨⟨f, n, hn⟩, hxf⟩
  refine mem_of_span_eq_top_of_smul_pow_mem (J'.ideal U) _ hcover b ?_
  intro r
  obtain ⟨n, hn⟩ := r.2
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul (h : F * J = F * J') : J = J' :=
  le_antisymm (hF.le_of_mul_le_mul $ le_of_eq h) $ hF.le_of_mul_le_mul $ le_of_eq h.symm
end

theorem exists_affineOpen_mem_subset (Z : Sch) (x : Z) (W : Opn Z)
    (hx : x ∈ W) : ∃ V : Z.affineOpens, x ∈ (V : Opn Z) ∧ (V : Opn Z) ≤ W := by
  obtain ⟨V, hV, hxV, hVW⟩ :=
    isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

section
variable {F : ISD Y} (hF : IsLocallyGeneratedByNonZeroDivisor F)
include hF
theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.pow (n : ℕ) :
    IsLocallyGeneratedByNonZeroDivisor $ F ^ n := by
  unfold IsLocallyGeneratedByNonZeroDivisor at hF ⊢
  intro x
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  refine ⟨U, f ^ n, hxU, pow_mem hf n, ?_⟩
  rw [EmbeddedResolution.pow_ideal_apply, hFU, span_singleton_pow]

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_opensio
    (U : Opn Y) : IsLocallyGeneratedByNonZeroDivisor (F.comap U.ι) := by
  intro x
  obtain ⟨W, t, hyW, ht, hFW⟩ := hF $ opIb U x
  obtain ⟨V0, hxV0, hV0⟩ :=
    EmbeddedResolution.exists_affineOpen_mem_subset U.toScheme x (opI U ⁻¹ᵁ W) hyW
  let _s0 := V0
  obtain ⟨a, b, hab, hya⟩ :=
    exists_basicOpen_le_affine_inter W.2 (V0.2.image_of_isOpenImmersion U.i) (U.ib x) ⟨hyW, ⟨x, hxV0, rfl⟩⟩
  have hDD0 : Y.basicOpen a ≤ imU U.i _s0 := by
    rw [hab]
    exact Y.basicOpen_le b
  have hDW : bOpn Y a ≤ W := Y.basicOpen_le a
  have hpreV0 : opI U ⁻¹ᵁ (bOpn Y a) ≤ _s0 := by
    intro z hz
    have h2 : z ∈ opI U ⁻¹ᵁ (opI U ''ᵁ _s0) := hDD0 hz
    rwa [U.ι.preimage_image_eq] at h2
  have hV1eq : U.toScheme.basicOpen
      ((U.ι.appLE W _s0 hV0).hom a)
      = opI U ⁻¹ᵁ (bOpn Y a) := by
    rw [_root_.FunctorialResolution.EmbeddedResolution.basicOpen_appLE]
    exact inf_eq_right.mpr hpreV0
  have hV1aff : IsAffineOpen (opI U ⁻¹ᵁ (bOpn Y a)) := by
    rw [← hV1eq]
    exact V0.2.basicOpen _
  have himg : opI U ''ᵁ (opI U ⁻¹ᵁ (bOpn Y a)) = (bOpn Y a) := by
    apply m55
    rw [coe_image_of_isOpenImmersion, coe_preimage_opens, image_preimage_eq_inter_range,
      range_opensio]
    exact inter_eq_self_of_subset_left (hDD0.trans $ EmbeddedResolution.image_opensio_le U _s0)
  have himgW : (opI U ''ᵁ (opI U ⁻¹ᵁ (bOpn Y a))) ≤ W := by simp_all
  have hleW : (opI U ⁻¹ᵁ (bOpn Y a)) ≤ opI U ⁻¹ᵁ W := fun z hz => hDW hz
  refine ⟨⟨opI U ⁻¹ᵁ (bOpn Y a), hV1aff⟩,
    (U.ι.appLE W (opI U ⁻¹ᵁ (bOpn Y a)) hleW).hom t, hya, ?_, ?_⟩
  have := W.2.isLocalization_basicOpen a
  let _a1 := pMap Y (homOfLE hDW).op
  let _a0 := _root_.FunctorialResolution.EmbeddedResolution.sectionsOpensImageIso U $ opI U ⁻¹ᵁ (bOpn Y a)
  let _a2 := pMap Y (eqToHom himg).op
  have hmor : _a1 ≫ _a2 ≫
      _a0.hom
      = U.ι.appLE W (opI U ⁻¹ᵁ (bOpn Y a)) hleW := by
    rw [EmbeddedResolution.restrictAppIso_hom, ← assoc, ← m222]
    have h3 : eqToHom himg ≫ homOfLE hDW = homOfLE himgW := m111 _ _
    have h3' : (homOfLE hDW).op ≫ (eqToHom himg).op = (homOfLE himgW).op := by simp_all
    rw [h3']
    exact map_appLE U.i _ (homOfLE himgW).op
  have hfin : (U.ι.appLE W (opI U ⁻¹ᵁ (bOpn Y a)) hleW).hom t
      = _a0.hom.hom
          (_a2.hom
            (_a1.hom t)) := by
    rw [← hmor]
    rfl
  rw [hfin]
  exact map_mem_nonZeroDivisors_of_iso
    (Y.presheaf.mapIso (eqToIso himg).op ≪≫ _a0) (nonZeroDivisors_le_comap (.powers a) Γ(Y, bOpn Y a) ht)
  rw [comap_ideal_eq_map_appLE F U.i W
    ⟨opI U ⁻¹ᵁ (bOpn Y a), hV1aff⟩ hleW, hFW, map_span, image_singleton]

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul_comap_opensio (U : Opn Y) {J J'}
    (h : F.comap U.i * J = F.comap U.i * J') : J = J' :=
  (hF.comap_opensio U).eq_of_mul_eq_mul h
end

theorem _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor.existsUnique_mul_eq [IsLocallyNoetherian Y]
    {F I' : ISD Y} (hF : IsLocallyGeneratedByNonZeroDivisor F) (hI : I' ≤ F) :
    ∃! J : ISD Y, F * J = I' := by
  refine ⟨EmbeddedResolution.idealSheafColon I' F, hF.mul_idealSheafColon hI, ?_⟩
  intro J hJ
  exact hF.eq_of_mul_eq_mul $ tr_ hJ (hF.mul_idealSheafColon hI).symm

variable {X X1 : Sch}

theorem comap_le_exceptionalIdeal_pow (pi_ : X1 ⟶ X) {Z I : ISD X} {n : ℕ}
    (hI : I ≤ Z ^ n) : I.comap pi_ ≤ exceptionalIdeal pi_ Z ^ n := by
  rw [p9, ← comap_pow]
  apply comap_mono
  exact hI

section
variable [hv0_0 : IsLocallyNoetherian X1] (pi_ : X1 ⟶ X) (Z I : ISD X) (n : ℕ)
include hv0_0
theorem existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (hI : I ≤ Z ^ n) :
    ∃! J : ISD X1, exceptionalIdeal pi_ Z ^ n * J = I.comap pi_ := by
  have hZ := an1 hpi_
  rw [← p9] at hZ
  exact (hZ.pow n).existsUnique_mul_eq $ comap_le_exceptionalIdeal_pow pi_ hI

def controlledTransform (_hπ : IsBlowupAlongIdealSheaf pi_ Z) (_hI : I ≤ Z ^ n) : ISD X1 :=
  idealSheafColon (I.comap pi_) $ exceptionalIdeal pi_ Z ^ n

section
variable (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (hI : I ≤ Z ^ n)
theorem exceptionalIdeal_pow_mul_controlledTransform :
    exceptionalIdeal pi_ Z ^ n * controlledTransform pi_ Z I n hpi_ hI = I.comap pi_ := by
  have hZ := an1 hpi_
  rw [← p9] at hZ
  exact (hZ.pow n).mul_idealSheafColon $ comap_le_exceptionalIdeal_pow pi_ hI

theorem eq_controlledTransform_of_mul_eq_comap
    J (hJ : exceptionalIdeal pi_ Z ^ n * J = I.comap pi_) :
    J = controlledTransform pi_ Z I n hpi_ hI :=
  (existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf pi_ Z I n hpi_ hI).unique hJ
    (exceptionalIdeal_pow_mul_controlledTransform pi_ Z I n hpi_ hI)
end
end

end FunctorialResolution.EmbeddedResolution

end
section


namespace FunctorialResolution.EmbeddedResolution

universe v

section
variable (R : Type) [CommRing R] {σ : Type}
section
variable (S : Finset σ)
def coordIdeal : Ideal $ MvPolynomial σ R :=
  span $ (MvPolynomial.X : σ → MvPolynomial σ R) '' (S : Set σ)

theorem X_mem_coordIdeal {i}
    (hi : i ∈ S) : (MvPolynomial.X i : MvPolynomial σ R) ∈ coordIdeal R S :=
  subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩

section
variable (i) (hi : i ∈ S)
def coordIdealGen :
    ↥(coordIdeal R S) :=
  ⟨MvPolynomial.X i, X_mem_coordIdeal R S hi⟩

@[simp] theorem coe_coordIdealGen :
    ((coordIdealGen R S i hi : ↥(coordIdeal R S)) : MvPolynomial σ R) = MvPolynomial.X i := rfl
end

theorem coordIdeal_eq_span :
    coordIdeal R S = span ((MvPolynomial.X : σ → MvPolynomial σ R) '' (S : Set σ)) := rfl
end

section
variable [hv3_0 : DecidableEq σ] (S : Finset σ) (s : σ)
include hv3_0
section
variable (hs : s ∈ S)
def mvPolynomialToCoordBlowupChart :
    MvPolynomial σ R →+* Away (reesGrading $ coordIdeal R S)
      (reesGenerator (coordIdeal R S) $ coordIdealGen R S s hs) :=
  eval₂Hom
    ((chartRingHom (coordIdeal R S) $ coordIdealGen R S s hs).comp
      (MvPolynomial.C : R →+* MvPolynomial σ R))
    (fun i => if h : i ∈ S ∧ i ≠ s then
        chartFraction (coordIdeal R S) (coordIdealGen R S s hs) $ coordIdealGen R S i h.1
      else chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) $ MvPolynomial.X i)

theorem awayCoordGenEquivMvPolynomial_invFun_C r :
    mvPolynomialToCoordBlowupChart R S s hs (MvPolynomial.C r)
      = chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.C r) :=
  eval₂Hom_C _ _ r

theorem awayCoordGenEquivMvPolynomial_invFun_X i :
    mvPolynomialToCoordBlowupChart R S s hs (MvPolynomial.X i)
      = if h : i ∈ S ∧ i ≠ s then
          chartFraction (coordIdeal R S) (coordIdealGen R S s hs) $ coordIdealGen R S i h.1
        else chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) $ MvPolynomial.X i :=
  eval₂Hom_X' _ _ i

theorem awayCoordGenEquivMvPolynomial_invFun_X_self :
    mvPolynomialToCoordBlowupChart R S s hs (MvPolynomial.X s)
      = chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) (MvPolynomial.X s) := by
  rw [awayCoordGenEquivMvPolynomial_invFun_X, dif_neg]
  rintro ⟨-, h⟩
  exact h rfl
end

def coordBlowupSubst :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i =>
    if i ∈ S ∧ i ≠ s then (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s
    else MvPolynomial.X i

theorem coordBlowupSubst_X i :
    coordBlowupSubst R S s (MvPolynomial.X i) =
      if i ∈ S ∧ i ≠ s then (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s
      else MvPolynomial.X i :=
  aeval_X _ i

@[simp] theorem coordBlowupSubst_X_of_mem {i : σ} (hi : i ∈ S) (hne : i ≠ s) :
    coordBlowupSubst R S s (MvPolynomial.X i) =
      (MvPolynomial.X i : MvPolynomial σ R) * MvPolynomial.X s := by
  rw [coordBlowupSubst_X, if_pos ⟨hi, hne⟩]

theorem coordBlowupSubst_C r :
    coordBlowupSubst R S s (MvPolynomial.C r) = (MvPolynomial.C r : MvPolynomial σ R) := by
  rw [← algebraMap_eq]
  exact (coordBlowupSubst R S s).commutes r

@[simp] theorem coordBlowupSubst_X_self :
    coordBlowupSubst R S s (MvPolynomial.X s) = (MvPolynomial.X s : MvPolynomial σ R) := by
  rw [coordBlowupSubst_X, if_neg]
  rintro ⟨-, h⟩
  exact h rfl

@[simp] theorem coordBlowupSubst_X_of_not_mem_erase {i : σ} (h : ¬ (i ∈ S ∧ i ≠ s)) :
    coordBlowupSubst R S s (MvPolynomial.X i) = (MvPolynomial.X i : MvPolynomial σ R) := by
  rw [coordBlowupSubst_X, if_neg h]

theorem mvPolynomialToChart_coordBlowupSubst (hs : s ∈ S) f :
    mvPolynomialToCoordBlowupChart R S s hs (coordBlowupSubst R S s f)
      = chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) f := by
  let _a0 := coordIdealGen R S s hs
  let _a1 := coordIdeal R S
  have key : (mvPolynomialToCoordBlowupChart R S s hs).comp ((coordBlowupSubst R S s).toRingHom)
      = p51 _a1 _a0 := by
    refine ringHom_ext ?_ ?_
    intro r
    show mvPolynomialToCoordBlowupChart R S s hs (coordBlowupSubst R S s $ m8 r) = _
    rw [coordBlowupSubst_C, awayCoordGenEquivMvPolynomial_invFun_C]
    intro i
    show mvPolynomialToCoordBlowupChart R S s hs (coordBlowupSubst R S s $ m7 i) = _
    by_cases h : i ∈ S ∧ i ≠ s
    rw [coordBlowupSubst_X_of_mem R S s h.1 h.2, map_mul, awayCoordGenEquivMvPolynomial_invFun_X, dif_pos h, awayCoordGenEquivMvPolynomial_invFun_X_self]
    have hb := chartRingHom_coe_eq_chartFraction_mul _a1 _a0
      (coordIdealGen R S i h.1)
    rw [coe_coordIdealGen, coe_coordIdealGen] at hb
    exact sy_ hb
    rw [coordBlowupSubst_X_of_not_mem_erase R S s h, awayCoordGenEquivMvPolynomial_invFun_X, dif_neg h]
  exact m156 key f

theorem map_coordIdeal_coordBlowupSubst (hs : s ∈ S) :
    Ideal.map (coordBlowupSubst R S s).toRingHom (coordIdeal R S)
      = span {(MvPolynomial.X s : MvPolynomial σ R)} := by
  let _a0 := coordBlowupSubst R S s
  apply le_antisymm
  rw [coordIdeal_eq_span, map_span, span_le]
  rintro y ⟨x, ⟨i, hi, rfl⟩, rfl⟩
  show _a0.toRingHom (m7 i) ∈
    span {(m7 s)}
  by_cases h : i ∈ S ∧ i ≠ s
  rw [show _a0.toRingHom (m7 i)
      = (m7 i) * m7 s from
    coordBlowupSubst_X_of_mem R S s h.1 h.2]
  exact mul_mem_left _ _ $ mem_span_singleton_self _
  have hieq : i = s := by
    by_contra hne
    exact h ⟨Finset.mem_coe.mp hi, hne⟩
  rw [show _a0.toRingHom (m7 i)
      = (m7 i) from coordBlowupSubst_X_of_not_mem_erase R S s h, hieq]
  exact mem_span_singleton_self _
  rw [span_le, singleton_subset_iff]
  have h2 := mem_map_of_mem (_a0.toRingHom) $ X_mem_coordIdeal R S hs
  rw [show _a0.toRingHom (m7 s)
      = (m7 s) from coordBlowupSubst_X_self R S s] at h2
  exact h2
end

theorem X_mem_nonZeroDivisors i :
    (MvPolynomial.X i : MvPolynomial σ R) ∈ nonZeroDivisors (MvPolynomial σ R) := by
  have key : ∀ x : MvPolynomial σ R, x * m7 i = 0 → x = 0 := by simp_all
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩

section
variable [hv3_0 : DecidableEq σ] (S : Finset σ) (s : σ) (hs : s ∈ S)
include hv3_0
def coordIdealReesAlgebraLift :
    ↥(reesAlgebra $ coordIdeal R S) →+* MvPolynomial σ R :=
  reesAlgebraLift (coordIdeal R S) (coordBlowupSubst R S s).toRingHom (MvPolynomial.X s)
    (map_coordIdeal_coordBlowupSubst R S s hs) $ X_mem_nonZeroDivisors R s

theorem reesAlgebraToMvPolynomial_algebraMap r :
    coordIdealReesAlgebraLift R S s hs (algebraMap (MvPolynomial σ R) ↥(reesAlgebra $ coordIdeal R S) r)
      = coordBlowupSubst R S s r :=
  reesAlgebraLift_algebraMap (coordIdeal R S) (coordBlowupSubst R S s).toRingHom (m7 s)
    (map_coordIdeal_coordBlowupSubst R S s hs) (X_mem_nonZeroDivisors R s) r

theorem reesAlgebraToMvPolynomial_reesGenerator :
    coordIdealReesAlgebraLift R S s hs (reesGenerator (coordIdeal R S) (coordIdealGen R S s hs)) = 1 :=
  reesAlgebraLift_reesGenerator (coordIdeal R S) (coordBlowupSubst R S s).toRingHom (m7 s)
    (map_coordIdeal_coordBlowupSubst R S s hs) (X_mem_nonZeroDivisors R s)
    (coordIdealGen R S s hs) (by rw [coe_coordIdealGen]; exact coordBlowupSubst_X_self R S s)

theorem isUnit_reesAlgebraToMvPolynomial_powers :
    ∀ y : ↥(powers $ reesGenerator (coordIdeal R S) $ coordIdealGen R S s hs),
      IsUnit $ coordIdealReesAlgebraLift R S s hs (y : ↥(reesAlgebra $ coordIdeal R S)) := by
  rintro ⟨y, n, rfl⟩
  show IsUnit $ coordIdealReesAlgebraLift R S s hs
    ((p35 (coordIdeal R S) $ coordIdealGen R S s hs) ^ n)
  rw [map_pow, reesAlgebraToMvPolynomial_reesGenerator, one_pow]
  exact isUnit_one
end
end

section
variable {A : Type} [CommRing A]
theorem reesGenerator_mem_homogeneousIdeal_of_span (s : Set A)
    (P : HomogeneousIdeal $ reesGrading $ span s)
    (hP : ∀ y ∈ s, ∀ hy : y ∈ span s, reesGenerator (span s) ⟨y, hy⟩ ∈ P)
    (a : ↥(span s)) : reesGenerator (span s) a ∈ P :=
  by
  obtain ⟨r, hr⟩ := a
  induction hr using span_induction with
  | mem x hx => exact (fun y hy hy2 => hP y hy hy2) x hx _
  | zero =>
      have e : p35 (m17 s) (0 : (m17 s)) = 0 := by
        apply m26
        simp [reesGenerator_coe]
      show p35 (m17 s) (0 : (m17 s)) ∈ P.toIdeal
      rw [e]
      exact P.toIdeal.zero_mem
  | add x y hx hy ihx ihy =>
      have e : p35 (span s) ((⟨x, hx⟩ : (span s)) + ⟨y, hy⟩)
          = p35 (m17 s) ⟨x, hx⟩ + p35 (m17 s) ⟨y, hy⟩ := by
        apply m26
        simp [reesGenerator_coe]
      show p35 (m17 s) ((⟨x, hx⟩ : (m17 s)) + ⟨y, hy⟩) ∈ P.toIdeal
      rw [e]
      exact P.toIdeal.add_mem ihx ihy
  | smul c x hx ih =>
      have e : p35 (span s) (c • (⟨x, hx⟩ : (span s)))
          = c • p35 (m17 s) ⟨x, hx⟩ := by
        apply m26
        simp [reesGenerator_coe, Polynomial.smul_monomial, smul_eq_mul]
      show p35 (m17 s) (c • (⟨x, hx⟩ : (m17 s))) ∈ P.toIdeal
      rw [e, smul_def]
      exact mul_mem_left P.toIdeal _ ih

section
variable (I : Ideal A)
theorem coe_reesDegreeZeroEquiv r :
    ((reesDegreeZeroEquiv I r : ↥(reesGrading I 0)) : ↥(reesAlgebra I))
      = algebraMap A ↥(reesAlgebra I) r := by
  apply m26
  rw [reesDegreeZeroEquiv_coe_coe]
  simp [Polynomial.C_eq_algebraMap]

def homogeneousAwayToLocalization (a : ↥I) :
    Away (reesGrading I) (reesGenerator I a) →+*
      Localization (powers $ reesGenerator I a) :=
  algebraMap (Away (reesGrading I) $ reesGenerator I a)
    (Localization $ powers $ reesGenerator I a)

theorem homogeneousLocalizationVal_apply a
    z :
    homogeneousAwayToLocalization I a z = val z :=
  HomogeneousLocalization.algebraMap_apply ..
end
end

section
variable (R : Type) [CommRing R] {σ : Type}
theorem iSup_opensRange_affineBlowupChart_coordIdealGen
    (S : Finset σ) :
    (⨆ i : ↥S, Scheme.Hom.opensRange
        (affineBlowupChart (coordIdeal R S) (coordIdealGen R S i.1 i.2)))
      = (⊤ : (affineBlowup (coordIdeal R S)).Opens) := by
  refine le_antisymm le_top ?_
  rw [SetLike.le_def]
  intro x _
  let _a0 := coordIdeal R S
  have hxtop : x ∈ (⨆ a : _a0,
      Proj.basicOpen (reesGrading _a0) (p35 _a0 a)) := by
    rw [iSup_proj_basicOpen_reesGenerator_eq_top]
    trivial
  obtain ⟨a, ha⟩ := mp_ mem_iSup hxtop
  by_contra hxn
  refine mp_ (Proj.mem_basicOpen ..) ha ?_
  refine reesGenerator_mem_homogeneousIdeal_of_span
    (imS (m7 : σ → MvPolynomial σ R) (S : Set σ)) _ ?_ a
  intro y hy hy2
  obtain ⟨i, hiS, rfl⟩ := hy
  by_contra hcon
  refine hxn (mpr_ mem_iSup ⟨⟨i, Finset.mem_coe.mp hiS⟩, ?_⟩)
  rw [opensRange_affineBlowupChart_eq_basicOpen]
  exact mpr_ (Proj.mem_basicOpen ..) hcon

section
variable [hv3_0 : DecidableEq σ] (S : Finset σ) (s : σ) (hs : s ∈ S)
include hv3_0
def coordBlowupChartToMvPolynomial :
    Away (reesGrading $ coordIdeal R S)
        (reesGenerator (coordIdeal R S) $ coordIdealGen R S s hs) →+* MvPolynomial σ R :=
  (IsLocalization.lift $ isUnit_reesAlgebraToMvPolynomial_powers R S s hs).comp
    (homogeneousAwayToLocalization (coordIdeal R S) $ coordIdealGen R S s hs)

theorem chartToMvPolynomial_apply
    z :
    coordBlowupChartToMvPolynomial R S s hs z =
      IsLocalization.lift (isUnit_reesAlgebraToMvPolynomial_powers R S s hs) (val z) := by
  show IsLocalization.lift (isUnit_reesAlgebraToMvPolynomial_powers R S s hs)
      (homogeneousAwayToLocalization (coordIdeal R S) (coordIdealGen R S s hs) z) = _
  rw [homogeneousLocalizationVal_apply]

theorem chartToMvPolynomial_chartRingHom r :
    coordBlowupChartToMvPolynomial R S s hs (chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) r)
      = coordBlowupSubst R S s r := by
  let _a0 := coordIdeal R S
  have hval : val (p51 _a0 (coordIdealGen R S s hs) r)
      = Localization.mk
          (reesDegreeZeroEquiv _a0 r : (reesAlgebra _a0)) 1 := rfl
  rw [chartToMvPolynomial_apply, hval, Localization.mk_eq_mk', mk'_one,
    lift_eq, coe_reesDegreeZeroEquiv, reesAlgebraToMvPolynomial_algebraMap]

theorem chartToMvPolynomial_mvPolynomialToChart f :
    coordBlowupChartToMvPolynomial R S s hs (mvPolynomialToCoordBlowupChart R S s hs f) = f := by
  let _a0 := coordBlowupChartToMvPolynomial R S s hs
  have key : _a0.comp (mvPolynomialToCoordBlowupChart R S s hs) = m99 (MvPolynomial σ R) := by
    refine ringHom_ext ?_ ?_
    intro r
    show coordBlowupChartToMvPolynomial R S s hs (mvPolynomialToCoordBlowupChart R S s hs $ m8 r) = m8 r
    rw [awayCoordGenEquivMvPolynomial_invFun_C, chartToMvPolynomial_chartRingHom, coordBlowupSubst_C]
    intro i
    show coordBlowupChartToMvPolynomial R S s hs (mvPolynomialToCoordBlowupChart R S s hs $ m7 i) = m7 i
    by_cases h : i ∈ S ∧ i ≠ s
    rw [awayCoordGenEquivMvPolynomial_invFun_X, dif_pos h]
    have hb := chartRingHom_coe_eq_chartFraction_mul (coordIdeal R S) (coordIdealGen R S s hs)
      (coordIdealGen R S i h.1)
    rw [coe_coordIdealGen, coe_coordIdealGen] at hb
    have h2 := congrArg _a0 hb
    rw [chartToMvPolynomial_chartRingHom, map_mul, chartToMvPolynomial_chartRingHom,
      coordBlowupSubst_X_of_mem R S s h.1 h.2, coordBlowupSubst_X_self] at h2
    exact mp_ (mul_cancel_right_mem_nonZeroDivisors $ X_mem_nonZeroDivisors R s) h2.symm
    rw [awayCoordGenEquivMvPolynomial_invFun_X, dif_neg h, chartToMvPolynomial_chartRingHom, coordBlowupSubst_X_of_not_mem_erase R S s h]
  exact m156 key f

theorem mvPolynomialToChart_surjective : Surjective $ mvPolynomialToCoordBlowupChart R S s hs := by
  let _c0 := coordIdealGen R S s hs
  let _c1 := coordIdeal R S
  intro z
  obtain ⟨n, r, hr⟩ := exists_mul_pow_eq_chartRingHom _c1 _c0 z
  let _a6 := coordBlowupChartToMvPolynomial R S s hs
  let _a3 := coordBlowupChartToMvPolynomial R S s hs z
  have h2 : _a3 * ((m7 s : MvPolynomial σ R) ^ n)
      = coordBlowupSubst R S s r := by
    have hcg := congrArg _a6 hr
    rwa [map_mul, map_pow _a6 (p51 _c1 _c0 ((coordIdealGen R S s hs) : MvPolynomial σ R)) n, chartToMvPolynomial_chartRingHom, coe_coordIdealGen, coordBlowupSubst_X_self, chartToMvPolynomial_chartRingHom] at hcg
  let _a5 := mvPolynomialToCoordBlowupChart R S s hs
  have h3 : mvPolynomialToCoordBlowupChart R S s hs _a3 *
      (p51 _c1 _c0 $ m7 s) ^ n
      = p51 _c1 _c0 r := by
    have hcg := congrArg _a5 h2
    rwa [map_mul, map_pow _a5 (m7 s) n, awayCoordGenEquivMvPolynomial_invFun_X_self, mvPolynomialToChart_coordBlowupSubst] at hcg
  refine ⟨_a3, ?_⟩
  have h := sy_ hr
  rw [← h3] at h
  exact mp_ (mul_cancel_right_mem_nonZeroDivisors $ pow_mem (chartRingHom_mem_nonZeroDivisors _c1 _c0) n) h

theorem exists_ringEquiv_away_mvPolynomial :
    ∃ e : Away (reesGrading $ coordIdeal R S)
        (reesGenerator (coordIdeal R S) $ coordIdealGen R S s hs) ≃+* MvPolynomial σ R,
      e.symm.toRingHom.comp (coordBlowupSubst R S s).toRingHom
        = chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) := by
  let _a0 := mvPolynomialToCoordBlowupChart R S s hs
  have hL : LeftInverse (coordBlowupChartToMvPolynomial R S s hs) _a0 :=
    fun f => chartToMvPolynomial_mvPolynomialToChart R S s hs f
  refine ⟨(ofBijective _a0
      ⟨hL.injective, mvPolynomialToChart_surjective R S s hs⟩).symm, ?_⟩
  rw [symm_symm]
  exact m48 fun f => mvPolynomialToChart_coordBlowupSubst R S s hs f

def awayCoordGenEquivMvPolynomial :
    Away (reesGrading $ coordIdeal R S)
        (reesGenerator (coordIdeal R S) $ coordIdealGen R S s hs) ≃+* MvPolynomial σ R :=
  (exists_ringEquiv_away_mvPolynomial R S s hs).choose

theorem awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst :
    (awayCoordGenEquivMvPolynomial R S s hs).symm.toRingHom.comp (coordBlowupSubst R S s).toRingHom
      = chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) :=
  (exists_ringEquiv_away_mvPolynomial R S s hs).choose_spec
end
end





def uliftFinset (m : ℕ) (S : FinSet m) : Finset $ UFin m :=
  S.map ⟨fun j => (up j : UFin m), fun _ _ h => congrArg down h⟩

section
variable {m : ℕ}
@[simp] theorem mem_uliftFinset (S : FinSet m) (x : UFin m) :
    x ∈ uliftFinset m S ↔ x.down ∈ S := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := mem_map.mp h
    exact ha
  · intro h
    exact mem_map.mpr ⟨x.down, h, rfl⟩

section
variable {S : FinSet m}
theorem up_mem_uliftFinset {j : Fin m} (hj : j ∈ S) :
    (up j : UFin m) ∈ uliftFinset m S :=
  (mem_uliftFinset S _).mpr hj

theorem down_mem_of_mem_uliftFinset {x : UFin m}
    (hx : x ∈ uliftFinset m S) : x.down ∈ S :=
  (mem_uliftFinset S x).mp hx
end
end

section
variable (k : Type) [Field k] (m : ℕ)
abbrev finCoordIdeal (S : FinSet m) :
    Ideal $ MvU m k :=
  coordIdeal k $ uliftFinset m S

def affineSpaceSpecIso :
    affineSpaceFin k m ≅ Spec (CommRingCat.of (MvU m k)) :=
  AffineSpace.SpecIso (UFin m) $ CommRingCat.of k
end

theorem appTop_comp_apply_eq_appTop_appTop {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Γ(Z, ⊤)) : (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl

theorem appTop_specMap_GaSpecIso_inv_apply {R S : CRC} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop.hom ((GSpecIso R).inv.hom x)
      = (GSpecIso S).inv.hom (f.hom x) := by
  have h : (GSpecIso R).inv ≫ hAT (m12 f) = f ≫ (GSpecIso S).inv := by simp_all
  have h2 : ((GSpecIso R).inv ≫ hAT (m12 f)).hom x
      = (f ≫ (GSpecIso S).inv).hom x := by rw [h]
  exact h2

section
variable (k : Type) [Field k] (m : ℕ)
theorem affineSpaceSpecIso_inv_appTop_coord
    (j : UFin m) :
    (affineSpaceSpecIso k m).inv.appTop.hom (AffineSpace.coord (Sp k) j)
      = (Scheme.GSpecIso $ CommRingCat.of (MvU m k)).inv.hom
          (MvPolynomial.X j) := by
  apply AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord

theorem affineSpaceSpecIso_hom_appTop_X
    (j : UFin m) :
    (affineSpaceSpecIso k m).hom.appTop.hom
        ((GSpecIso $ CommRingCat.of (MvU m k)).inv.hom
          (MvPolynomial.X j))
      = AffineSpace.coord (Sp k) j := by
  rw [← affineSpaceSpecIso_inv_appTop_coord k m j, ← appTop_comp_apply_eq_appTop_appTop, m145]
  simp

theorem affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec :
    inv (affineSpaceSpecIso k m) ≫ affineSpaceFinToSpec k m
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvU m k)) := by
  simp [affineSpaceSpecIso, affineSpaceFinToSpec]

section
variable (S : FinSet m)
abbrev affineSpaceCoordBlowup : Sch :=
  affineBlowup $ finCoordIdeal k m S

def affineSpaceCoordBlowupMap :
    affineSpaceCoordBlowup k m S ⟶ affineSpaceFin k m :=
  Blowup.AffineBlowup.toSpec (finCoordIdeal k m S) ≫ inv (affineSpaceSpecIso k m)

theorem comap_specIdealSheaf_finCoordIdeal :
    (specIdealSheaf $ finCoordIdeal k m S).comap (affineSpaceSpecIso k m).hom
      = coordSubspaceIdeal k m S := by
  have : IsAffine $ affineSpaceFin k m := inferInstance
  let _a0 := GSpecIso $ m10 $ MvPolynomial (UFin m) k
  let _a2 := uliftFinset m S
  have hset : ((affineSpaceSpecIso k m).hom.appTop.hom) ''
      ((_a0.inv.hom) ''
        (imS m7 (_a2)))
      = (fun i => m9 (Sp k) $ up i) ''
          (S : Set $ Fin m) := by
    ext x
    constructor
    rintro ⟨y, ⟨z, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
    exact ⟨j.down, Finset.mem_coe.mpr $ down_mem_of_mem_uliftFinset $ Finset.mem_coe.mp hj,
      symm $ affineSpaceSpecIso_hom_appTop_X k m j⟩
    rintro ⟨i, hi, rfl⟩
    exact ⟨_a0.inv.hom
        (m7 $ up i),
      ⟨m7 $ up i,
        ⟨up i, Finset.mem_coe.mpr $ up_mem_uliftFinset $ Finset.mem_coe.mp hi, rfl⟩, rfl⟩,
      affineSpaceSpecIso_hom_appTop_X k m $ up i⟩
  have hI : (finCoordIdeal k m S)
      = span (imS m7 (_a2)) :=
    coordIdeal_eq_span k _a2
  rw [specIdealSheaf_eq_ofIdealTop, comap_ofIdealTop, coordSubspaceIdeal_eq_ofIdealTop_span_coord, hI,
    map_span, map_span, hset]

theorem isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap :
    IsBlowupAlongIdealSheaf (affineSpaceCoordBlowupMap k m S) $ coordSubspaceIdeal k m S := by
  rw [← comap_specIdealSheaf_finCoordIdeal k m S]
  exact (isBlowupAlongIdealSheaf_affineBlowup_toSpec $ finCoordIdeal k m S).comp_iso_hom
    (affineSpaceSpecIso k m).symm

section
variable (s : Fin m) (hs : s ∈ S)
abbrev finCoordIdealGen :
    ↥(finCoordIdeal k m S) :=
  coordIdealGen k (uliftFinset m S) (up s) $ up_mem_uliftFinset hs

abbrev coordBlowupChartRing :=
  Away (reesGrading $ finCoordIdeal k m S)
    (reesGenerator (finCoordIdeal k m S) $ finCoordIdealGen k m S s hs)

def coordBlowupChartRingEquiv :
    coordBlowupChartRing k m S s hs ≃+* MvU m k :=
  @awayCoordGenEquivMvPolynomial k _ (UFin m) (decEq _) (uliftFinset m S) (up s)
    (up_mem_uliftFinset hs)

def coordBlowupChartRingCatIso :
    CommRingCat.of (coordBlowupChartRing k m S s hs) ≅
      CommRingCat.of (MvU m k) :=
  (coordBlowupChartRingEquiv k m S s hs).toCommRingCatIso

def specCoordBlowupChartRingIso :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅
      Spec (CommRingCat.of (MvU m k)) where
  hom := Spec.map (coordBlowupChartRingCatIso k m S s hs).inv
  inv := Spec.map (coordBlowupChartRingCatIso k m S s hs).hom
  hom_inv_id := by rw [← map_comp, Iso.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, Iso.inv_hom_id, map_id]

def specCoordBlowupChartRingIsoAffineSpace :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅ affineSpaceFin k m :=
  specCoordBlowupChartRingIso k m S s hs ≪≫ (affineSpaceSpecIso k m).symm

def affineSpaceCoordBlowupChart :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ⟶ affineSpaceCoordBlowup k m S :=
  affineBlowupChart (finCoordIdeal k m S) $ finCoordIdealGen k m S s hs
end
end
end

instance instIsOpenImmersionModelBlowupChart (k : Type) [Field k] (m : ℕ) (S : FinSet m)
    (s : Fin m) (hs : s ∈ S) : IsOpenImmersion $ affineSpaceCoordBlowupChart k m S s hs :=
  instIsOpenImmersionAffineBlowupChart (finCoordIdeal k m S) $ finCoordIdealGen k m S s hs

section
variable (k : Type) [Field k] (m : ℕ) (S : FinSet m)
section
variable (s : Fin m)
def coordBlowupSubstUliftFin :
    MvU m k →ₐ[k] MvU m k :=
  @coordBlowupSubst k _ (UFin m) (decEq _) (uliftFinset m S) $ up s

theorem specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv :
    Spec.map (ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
        ≫ (affineSpaceSpecIso k m).inv
      = (affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s := by
  let _a3 := isoI $ affineSpaceSpecIso k m
  let _a0 := m12 (ofHom (coordBlowupSubstUliftFin k m S s).toRingHom) ≫ _a3
  let _a1 := _a3 ≫ coordBlowupSubstMap k m S s
  refine m46 ?_ ?_
  show _a0 ≫ affineSpaceFinToSpec k m
    = _a1 ≫ affineSpaceFinToSpec k m
  rw [assoc, assoc, coordBlowupSubstMap_comp_affineSpaceFinToSpec, affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec,
    ← map_comp]
  congr 1
  ext r
  simp [coordBlowupSubstUliftFin]
  intro i
  let _a2 := m9 (Sp k) i
  show _a0.appTop.hom
          _a2
    = _a1.appTop.hom
          _a2
  rw [appTop_comp_apply_eq_appTop_appTop, appTop_comp_apply_eq_appTop_appTop, affineSpaceSpecIso_inv_appTop_coord,
    appTop_specMap_GaSpecIso_inv_apply, coordBlowupSubstMap_appTop_coord]
  by_cases hc : i.down ∈ S ∧ i.down ≠ s
  rw [if_pos hc, map_mul, affineSpaceSpecIso_inv_appTop_coord, affineSpaceSpecIso_inv_appTop_coord]
  simp [coordBlowupSubstUliftFin, ext_iff, an1 hc, an2 hc]
  rw [if_neg hc, affineSpaceSpecIso_inv_appTop_coord]
  simp [coordBlowupSubstUliftFin, ext_iff, hc]

theorem affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap (hs : s ∈ S) :
    affineSpaceCoordBlowupChart k m S s hs ≫ affineSpaceCoordBlowupMap k m S =
      (specCoordBlowupChartRingIsoAffineSpace k m S s hs).hom ≫ coordBlowupSubstMap k m S s := by
  let _a0 := finCoordIdeal k m S
  let _a1 := finCoordIdealGen k m S s hs
  have hring : ofHom (chartRingHom _a0 _a1)
      = ofHom (coordBlowupSubstUliftFin k m S s).toRingHom ≫
        ofHom (coordBlowupChartRingEquiv k m S s hs).symm.toRingHom := by
    rw [← @awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst k _ (UFin m) (decEq _) (uliftFinset m S) (up s) $ up_mem_uliftFinset hs]
    rfl
  show affineBlowupChart _a0 _a1 ≫
      (p13 _a0 ≫ isoI (affineSpaceSpecIso k m))
    = isoH (specCoordBlowupChartRingIsoAffineSpace k m S s hs) ≫ coordBlowupSubstMap k m S s
  rw [← assoc, affineBlowupChart_comp_toSpec, algebraMap_chart_eq_chartRingHom, hring,
    map_comp, assoc, specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv k m S s, ← assoc]
  rfl
end

theorem iSup_opensRange_affineSpaceCoordBlowupChart :
    (⨆ i : ↥S, Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2))
      = (⊤ : (affineSpaceCoordBlowup k m S).Opens) := by
  refine le_antisymm le_top ?_
  rw [← iSup_opensRange_affineBlowupChart_coordIdealGen k $ uliftFinset m S]
  refine iSup_le fun j => ?_
  exact le_iSup_of_le ⟨j.1.down, down_mem_of_mem_uliftFinset j.2⟩ le_rfl
end

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution


structure BlowupChart {X X1 : Sch} {k : Type} [Field k]
    {p : X ⟶ Sp k} (pi_ : X1 ⟶ X) {U : Opn X} {m : ℕ}
    (c : EtaleChart p U m) (S : FinSet m) (s : Fin m) where
  domain : Opn X1
  domain_le : domain ≤ pre pi_ U
  chart : EtaleChart (pi_ ≫ p) domain m
  comm : chart.map ≫ coordBlowupSubstMap k m S s = pi_.resLE U domain domain_le ≫ c.map

theorem exists_opens_isPullback_of_opens {X1 M : Sch} (V : Opn X1)
    (q : toScheme V ⟶ M) (W : Opn M) :
    ∃ (dom : Opn X1) (_hle : dom ≤ V) (g : toScheme dom ⟶ toScheme W)
      (r : toScheme dom ⟶ toScheme V),
      IsPullback g r W.i q ∧ r ≫ ι V = ι dom ∧
        ∀ y, q.base y ∈ W → V.ib y ∈ dom := by
  let _a0 := opI $ preU q W
  let _c0 := _a0 ≫ opI V
  classical
  have hdle : opensRange _c0 ≤ V := by
    rintro x ⟨y, rfl⟩
    have h1 : opIb V ((preU q W).ib y) ∈ range V.ib := ⟨_, rfl⟩
    rwa [q1] at h1
  obtain ⟨e, he⟩ : ∃ e : oSch (opensRange _c0) ≅
      toScheme (preU q W),
      isoH e ≫ _c0 = opI (opensRange _c0) :=
    ⟨isoOfRangeEq (opensRange _c0).i
        _c0 $ q1 _,
      isoOfRangeEq_hom_fac _ _ _⟩
  refine ⟨opensRange _c0, hdle, isoH e ≫ mrU q W,
    hom e ≫ _a0, ?_, ?_, ?_⟩
  have h1 : IsPullback e.hom (isoH e ≫ _a0) _a0 $ 𝟙 _ :=
    of_horiz_isIso ⟨by simp⟩
  have h2 := h1.paste_horiz $ isPullback_morphismRestrict q W
  rwa [id_comp] at h2
  rwa [assoc]
  intro y hy
  exact ⟨⟨y, hy⟩, rfl⟩

section
variable {X X1 : Sch} {k : Type} [Field k] {p : X ⟶ Sp k} (pi_ : X1 ⟶ X) {U : Opn X} {m : ℕ} (c : EtaleChart p U m) (S : FinSet m)
theorem exists_blowupChart_family_isPullback_covering (Z : ISD X)
    (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (hZ : restrictIdeal Z U = c.coordIdeal S) :
    ∃ F : ∀ s : Fin m, s ∈ S → BlowupChart pi_ c S s,
      (∀ s hs,
          IsPullback (F s hs).chart.map
            (pi_.resLE U (F s hs).domain (F s hs).domain_le)
            (coordBlowupSubstMap k m S s) c.map) ∧
      (∀ x : ↥X1, x ∈ pre pi_ U → ∃ s hs, x ∈ (F s hs).domain) := by
  classical
  have := c.isEtale
  have : Flat c.map := inferInstance
  have hres : p15 (mrU pi_ U) (cmI (coordSubspaceIdeal k m S) c.map) := by
    have h1 := hpi_.restrict U
    rwa [← restrictIdeal_eq_comap_io, hZ, p33] at h1
  obtain ⟨q, -, hq⟩ := (isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap k m S).exists_isPullback_of_flat c.map hres
  have key : ∀ s (hs : s ∈ S), ∃ B : BlowupChart pi_ c S s,
      IsPullback B.chart.map (pi_.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map ∧
        ∀ y, bsM q y ∈ opensRange (affineSpaceCoordBlowupChart k m S s hs) →
          (preU pi_ U).ib y ∈ B.domain := by
    intro s hs
    obtain ⟨dom, hle, g, r, hpb, hrio, hmem⟩ :=
      exists_opens_isPullback_of_opens (preU pi_ U) q (opensRange (affineSpaceCoordBlowupChart k m S s hs))
    have hrange :=
      q1 (opensRange (affineSpaceCoordBlowupChart k m S s hs))
    let _a0 := opensRange $ affineSpaceCoordBlowupChart k m S s hs
    obtain ⟨eW, heW⟩ : ∃ e : oSch _a0 ≅
        affineSpaceFin k m,
        hom e ≫ coordBlowupSubstMap k m S s =
          opI _a0 ≫ affineSpaceCoordBlowupMap k m S := by
      refine ⟨isoOfRangeEq
          (opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
          (affineSpaceCoordBlowupChart k m S s hs) hrange ≪≫ specCoordBlowupChartRingIsoAffineSpace k m S s hs, ?_⟩
      have hfac := isoOfRangeEq_hom_fac
        (opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
        (affineSpaceCoordBlowupChart k m S s hs) hrange
      rw [trans_hom, assoc, ← affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap,
        ← assoc, hfac]
    have heW' : isoI eW ≫ opI _a0 ≫
        affineSpaceCoordBlowupMap k m S = coordBlowupSubstMap k m S s := by
      rw [← heW, inv_hom_id_assoc]
    have hleft : r ≫ (mrU pi_ U) = pi_.resLE U dom hle := by
      rw [← cancel_mono U.i, assoc, morphismRestrict_ι, q4,
        ← assoc, hrio]
    have hsq : IsPullback (g ≫ isoH eW) (pi_.resLE U dom hle) (coordBlowupSubstMap k m S s) c.map := by
      have h1 : IsPullback (g ≫ isoH eW) (𝟙 _) eW.inv g :=
        of_vert_isIso ⟨by simp⟩
      have h2 := h1.paste_vert $ hpb.paste_vert hq
      rwa [id_comp, hleft, heW'] at h2
    refine ⟨⟨dom, hle, ⟨g ≫ isoH eW, ?_, m122 hsq.flip c.isEtale⟩, hsq.w⟩, hsq, hmem⟩
    let _a3 := affineSpaceFinToSpec k m
    calc (g ≫ isoH eW) ≫ _a3
        = (g ≫ isoH eW) ≫ coordBlowupSubstMap k m S s ≫ _a3 := by
          rw [coordBlowupSubstMap_comp_affineSpaceFinToSpec]
      _ = ((g ≫ isoH eW) ≫ coordBlowupSubstMap k m S s) ≫ _a3 := by
          simp [assoc]
      _ = (pi_.resLE U dom hle ≫ c.map) ≫ _a3 := by rw [hsq.w]
      _ = pi_.resLE U dom hle ≫ c.map ≫ _a3 := by simp [assoc]
      _ = pi_.resLE U dom hle ≫ opI U ≫ p := by rw [c.comp_struct]
      _ = (pi_.resLE U dom hle ≫ opI U) ≫ p := by simp [assoc]
      _ = (opI dom ≫ pi_) ≫ p := by rw [q4]
      _ = opI dom ≫ pi_ ≫ p := by simp [assoc]
  choose F hF1 hF2 using key
  refine ⟨F, hF1, ?_⟩
  intro x hx
  have hx' : x ∈ range (preU pi_ U).ib := by simp_all
  obtain ⟨y, rfl⟩ := hx'
  have hy : bsM q y ∈
      (⨆ i : S, opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2)) := by
    rw [iSup_opensRange_affineSpaceCoordBlowupChart k m S]
    simp
  obtain ⟨i, hi⟩ := mp_ mem_iSup hy
  exact ⟨i.1, i.2, hF2 i.1 i.2 y hi⟩

section
variable {Z : ISD X} (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
section
variable (s : Fin m) (hs : s ∈ S)
def blowupChartOfIsBlowup : BlowupChart pi_ c S s :=
  (exists_blowupChart_family_isPullback_covering pi_ c S Z hpi_ hZ).choose s hs

theorem isPullback_blowupChart_of_isBlowupAlongIdealSheaf :
    IsPullback (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).chart.map
      (pi_.resLE U (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).domain
        (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).domain_le)
      (coordBlowupSubstMap k m S s) c.map :=
  (exists_blowupChart_family_isPullback_covering pi_ c S Z hpi_ hZ).choose_spec.1 s hs
end

theorem exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf
    (x : ↥X1) (hx : x ∈ pre pi_ U) :
    ∃ s hs, x ∈ (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).domain :=
  (exists_blowupChart_family_isPullback_covering pi_ c S Z hpi_ hZ).choose_spec.2 x hx
end
end





namespace BlowupChart

variable {X X1 : Sch} {k : Type} [Field k]
  {p : X ⟶ Sp k} {pi_ : X1 ⟶ X} {U : Opn X} {m : ℕ}
  {c : EtaleChart p U m} {S : FinSet m} {s : Fin m}

theorem comp_hom_apply {R1_ R2_ R3 : CRC} (a : R1_ ⟶ R2_)
    (b : R2_ ⟶ R3) (x : R1_) : (a ≫ b).hom x = b.hom (a.hom x) := rfl

private theorem comp_appTop_apply {A B C : Sch} (ph_ : A ⟶ B) (ps_ : B ⟶ C)
    (t : Γ(C, ⊤)) :
    ((ph_ ≫ ps_).appTop).hom t = (ph_.appTop).hom ((ps_.appTop).hom t) := rfl

section
variable {T : Type} [TopologicalSpace T] (F : (TopologicalSpace.Opens T)ᵒᵖ ⥤ CRC)
private theorem presheaf_map_eq
    {A B : (TopologicalSpace.Opens T)ᵒᵖ} (al_ be_ : A ⟶ B) : F.map al_ = F.map be_ := by
  rw [unop_inj $ m111 al_.unop be_.unop]

private theorem presheaf_map_comp_eq
    {A B C : (TopologicalSpace.Opens T)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) :
    F.map a ≫ F.map b = F.map c := by
  rw [← F.map_comp]
  exact presheaf_map_eq F _ c
end

theorem top_le_io_preimage {Y : Sch} (W : Opn Y) :
    (⊤ : W.toScheme.Opens) ≤ ι W ⁻¹ᵁ W :=by simp_all
theorem top_le_preimage_top {Y Y1 : Sch} g :
    (⊤ : Opn Y1) ≤ g ⁻¹ᵁ (⊤ : Opn Y) := by
  simp

theorem topIso_inv_eq_io_appLE {Y : Sch} (W : Opn Y) :
    W.topIso.inv = W.ι.appLE W ⊤ (top_le_io_preimage W) := by
  simp [appLE]
  exact sy_ $ presheaf_map_comp_eq Y.presheaf _ _ _

section
variable {Y Y1 : Sch}
theorem appLE_congr (g1_ g2_ : Y1 ⟶ Y) (h : g1_ = g2_)
    W V e1_ e2_ :
    appLE g1_ W V e1_ = appLE g2_ W V e2_ := by
  subst h
  rfl

section
variable (f : Y1 ⟶ Y) (W : Opn Y) (V : Opn Y1) (hV : V ≤ pre f W)
theorem appLE_topIso_inv_comp :
    appLE f W V hV ≫ V.topIso.inv = W.topIso.inv ≫ appTop (f.resLE W V hV) := by
  have happ : appTop (f.resLE W V hV)
      = appLE (f.resLE W V hV) ⊤ ⊤ (top_le_preimage_top $ f.resLE W V hV) :=
    symm $ appLE_eq_app $ f.resLE W V hV
  rw [topIso_inv_eq_io_appLE, topIso_inv_eq_io_appLE, happ,
    m91, m91]
  exact appLE_congr (opI V ≫ f) (f.resLE W V hV ≫ opI W) (by simp) W ⊤ _ _

theorem topIso_hom_comp_appLE :
    W.topIso.hom ≫ appLE f W V hV = appTop (f.resLE W V hV) ≫ V.topIso.hom := by
  let _a0 := hAT $ f.resLE W V hV
  calc W.topIso.hom ≫ appLE f W V hV
      = W.topIso.hom ≫ (appLE f W V hV ≫ V.topIso.inv) ≫ V.topIso.hom := by
        simp only [assoc, m114, comp_id]
    _ = W.topIso.hom ≫ (W.topIso.inv ≫ _a0) ≫ V.topIso.hom := by rw [appLE_topIso_inv_comp f W V hV]
    _ = _a0 ≫ V.topIso.hom := by
        simp only [assoc, hom_inv_id_assoc]

theorem appLE_topIso_hom_apply (y : Γ(W.toScheme, ⊤)) :
    (appLE f W V hV).hom (W.topIso.hom.hom y)
      = V.topIso.hom.hom ((f.resLE W V hV).appTop.hom y) := by
  have h2 : (W.topIso.hom ≫ appLE f W V hV).hom y
      = (hAT (f.resLE W V hV) ≫ V.topIso.hom).hom y := by
    rw [topIso_hom_comp_appLE f W V hV]
  rwa [comp_hom_apply, comp_hom_apply] at h2

theorem topIso_inv_appLE_apply (a : (Y.sec W)) :
    V.topIso.inv.hom ((appLE f W V hV).hom a)
      = ((f.resLE W V hV).appTop).hom (W.topIso.inv.hom a) := by
  have h2 := congrArg (fun ph_ : xSec Y W ⟶ Γ(oSch V, ⊤) => m4 ph_ a) $ appLE_topIso_inv_comp f W V hV
  rwa [comp_hom_apply, comp_hom_apply] at h2
end
end

section
variable (B : BlowupChart pi_ c S s)
theorem restrictIdeal_comap (D : ISD X) :
    restrictIdeal (D.comap pi_) B.domain =
      (restrictIdeal D U).comap (pi_.resLE U B.domain B.domain_le) := by
  rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io,
    ← comap_comp,
    ← comap_comp,
    resLE_comp_ι]

theorem restrictIdeal_exceptionalIdeal
    (Z : ISD X) (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S) :
    restrictIdeal (exceptionalIdeal pi_ Z) B.domain = B.chart.coordIdeal {s} := by
  rw [p9, restrictIdeal_comap B Z, hZ]
  exact comap_coordIdeal_center c B.chart (pi_.resLE U B.domain B.domain_le) B.comm hs

section
variable (D : ISD X)
theorem restrictIdeal_comap_coordIdeal_of_mem j (hj : j ∈ S) (hjs : j ≠ s)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (D.comap pi_) B.domain =
      B.chart.coordIdeal {j} * B.chart.coordIdeal {s} := by
  rw [restrictIdeal_comap B D, hD]
  exact comap_coordIdeal_singleton_of_mem c B.chart
    (pi_.resLE U B.domain B.domain_le) B.comm j hj hjs

theorem restrictIdeal_comap_coordIdeal_self (hD : restrictIdeal D U = c.coordIdeal {s}) :
    restrictIdeal (D.comap pi_) B.domain = B.chart.coordIdeal {s} := by
  rw [restrictIdeal_comap B D, hD]
  exact comap_coordIdeal_singleton_self c B.chart
    (pi_.resLE U B.domain B.domain_le) B.comm

theorem restrictIdeal_comap_coordIdeal_of_not_mem j (hj : j ∉ S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (D.comap pi_) B.domain = B.chart.coordIdeal {j} := by
  rw [restrictIdeal_comap B D, hD]
  exact comap_coordIdeal_singleton_of_notMem c B.chart
    (pi_.resLE U B.domain B.domain_le) B.comm j hj

theorem restrictIdeal_comap_top (hD : restrictIdeal D U = ⊤) :
    restrictIdeal (D.comap pi_) B.domain = ⊤ := by
  rw [restrictIdeal_comap B D, hD, comap_top]
end

theorem appLE_coord_of_mem (i : Fin m)
    (hi : i ∈ S) (his : i ≠ s) :
    (appLE pi_ U B.domain B.domain_le).hom (c.coord i) =
      B.chart.coord i * B.chart.coord s := by
  have h0 :=
    congrArg (fun ph_ : B.domain.toScheme ⟶ affineSpaceFin k m =>
      (hAT ph_).hom
        (m9 (Sp k) $ up i)) B.comm
  rw [comp_appTop_apply, comp_appTop_apply,
    coordBlowupSubstMap_appTop_coord_of_mem k m S s i hi his, map_mul] at h0
  rw [coord_def c i, coord_def B.chart i, coord_def B.chart s,
    appLE_topIso_hom_apply pi_ U B.domain B.domain_le, sy_ h0, map_mul]

theorem appLE_coord_self :
    (appLE pi_ U B.domain B.domain_le).hom (c.coord s) = B.chart.coord s := by
  let _a1 := coordBlowupSubstMap k m S s
  let _a2 := pi_.resLE U B.domain B.domain_le
  have h1 : hAT _a1 ≫ B.chart.map.appTop
      = c.map.appTop ≫ hAT _a2 := by
    exact hom_ext $ m48 fun z => congrArg (fun ph_ : B.domain.toScheme ⟶ affineSpaceFin k m => (hAT ph_).hom z) B.comm
  let _a0 := m9 (Sp k) $ up s
  have h2 : B.chart.map.appTop.hom
        (_a1.appTop.hom
          _a0)
      = _a2.appTop.hom
          (c.map.appTop.hom
            _a0) := by
    have h3 : (hAT _a1 ≫ B.chart.map.appTop).hom
          _a0
        = (c.map.appTop ≫ hAT _a2).hom
          _a0 := by
      rw [h1]
    exact h3
  rw [coordBlowupSubstMap_appTop_coord_self] at h2
  rw [coord_def c s, coord_def B.chart s, h2]
  exact appLE_topIso_hom_apply pi_ U B.domain B.domain_le _

theorem appLE_coord_of_not_mem (i : Fin m) (hi : i ∉ S) :
    (appLE pi_ U B.domain B.domain_le).hom (c.coord i) = B.chart.coord i := by
  let _a1 := hAT (coordBlowupSubstMap k m S s) ≫ hAT (B.chart.map)
  let _a3 := pi_.resLE U B.domain B.domain_le
  let _a2 := hAT (c.map) ≫ hAT _a3
  have hcomm : _a1
      = _a2 := by
    exact hom_ext $ m48 fun z => congrArg (fun ph_ : B.domain.toScheme ⟶ affineSpaceFin k m => (hAT ph_).hom z) B.comm
  let _a0 := m9 (Sp k) $ up i
  have hx : (B.chart.map).appTop.hom
        ((coordBlowupSubstMap k m S s).appTop.hom
          _a0)
      = _a3.appTop.hom
        ((c.map).appTop.hom
          _a0) := by
    have h2 : _a1.hom
          _a0
        = _a2.hom
          _a0 := by
      rw [hcomm]
    rwa [comp_hom_apply, comp_hom_apply] at h2
  rw [coordBlowupSubstMap_appTop_coord_of_notMem k m S s i hi] at hx
  simp only [coord_def]
  rw [hx]
  exact appLE_topIso_hom_apply pi_ U B.domain B.domain_le _

theorem appLE_coord i :
    (appLE pi_ U B.domain B.domain_le).hom (c.coord i) =
      if i ∈ S ∧ i ≠ s then B.chart.coord i * B.chart.coord s else B.chart.coord i := by
  by_cases h : i ∈ S ∧ i ≠ s
  rw [if_pos h]
  exact B.appLE_coord_of_mem i h.1 h.2
  rw [if_neg h]
  by_cases hi : i ∈ S
  have hieq : i = s := by
    by_contra hne
    exact h ⟨hi, hne⟩
  rw [hieq]
  exact B.appLE_coord_self
  exact B.appLE_coord_of_not_mem i hi

def coordEvalHom :
    MvPolynomial (UFin m) (X.sec U) →+* (X1.sec B.domain) :=
  eval₂Hom (appLE pi_ U B.domain B.domain_le).hom
    (fun i : UFin m => B.chart.coord i.down)


theorem coordEvalHom_C (a : (X.sec U)) :
    B.coordEvalHom (MvPolynomial.C a) = (appLE pi_ U B.domain B.domain_le).hom a := by
  simp [coordEvalHom]

theorem coordEvalHom_X (i : Fin m) :
    B.coordEvalHom (MvPolynomial.X (up i : UFin m)) = B.chart.coord i := by
  simp [coordEvalHom]
end

def coordRelation (_B : BlowupChart pi_ c S s) (i : Fin m) :
    MvPolynomial (UFin m) $ X.sec U :=
  (if i ∈ S ∧ i ≠ s then
      MvPolynomial.X (up i : UFin m) *
        MvPolynomial.X (up s : UFin m)
    else MvPolynomial.X (up i : UFin m)) - MvPolynomial.C (c.coord i)

section
variable (B : BlowupChart pi_ c S s)
theorem coordRelation_def i :
    B.coordRelation i =
      (if i ∈ S ∧ i ≠ s then
          MvPolynomial.X (up i : UFin m) *
            MvPolynomial.X (up s : UFin m)
        else MvPolynomial.X (up i : UFin m)) -
        MvPolynomial.C (c.coord i) := rfl

theorem coordEvalHom_coordRelation i :
    B.coordEvalHom (B.coordRelation i) = 0 := by
  rw [coordRelation_def]
  by_cases h : i ∈ S ∧ i ≠ s
  rw [if_pos h, map_sub, map_mul, coordEvalHom_X, coordEvalHom_X, coordEvalHom_C, B.appLE_coord i,
    if_pos h, sub_self]
  rw [if_neg h, map_sub, coordEvalHom_X, coordEvalHom_C, B.appLE_coord i, if_neg h, sub_self]

theorem coordEvalHom_eq_zero_of_mem_span
    a
    (ha : a ∈ span (range B.coordRelation)) : B.coordEvalHom a = 0 := by
  have h : span (range B.coordRelation) ≤ ker B.coordEvalHom := by
    rw [span_le]
    rintro x ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr $ B.coordEvalHom_coordRelation i
  exact RingHom.mem_ker.mp $ h ha

def coordEvalQuotientHom :
    (MvPolynomial (UFin m) (X.sec U) ⧸ span (range B.coordRelation)) →+*
      (X1.sec B.domain) :=
  lift (span (range B.coordRelation)) B.coordEvalHom
    B.coordEvalHom_eq_zero_of_mem_span

theorem coordEvalQuotientHom_mk
    (a : MvPolynomial (UFin m) (X.sec U)) :
    B.coordEvalQuotientHom (Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) a) = B.coordEvalHom a := rfl
end

section
variable {R T : CRC} (e : R ≅ T)
theorem iso_inv_hom_apply (x : R) :
    e.inv.hom (e.hom.hom x) = x :=by simp_all
theorem iso_hom_inv_apply (x : T) :
    e.hom.hom (e.inv.hom x) = x :=by simp_all
end

section
variable (k : Type) [Field k] (m : ℕ)
def mvPolynomialIsoGlobalSectionsAffineSpace :
    CommRingCat.of (MvU m k) ≅ Γ(affineSpaceFin k m, ⊤) :=
  (Scheme.GSpecIso $ CommRingCat.of (MvU m k)).symm ≪≫
    Scheme.Γ.mapIso (AffineSpace.SpecIso (UFin m) $ CommRingCat.of k).op

theorem mvPolynomialIsoGlobalSectionsAffineSpace_hom_apply
    x :
    (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom x = affineSpaceGlobalSectionsHom k m x := rfl

theorem mvPolynomialIsoGlobalSectionsAffineSpace_hom_X
    i :
    (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom (MvPolynomial.X i)
      = AffineSpace.coord (Sp k) i := by
  let _c0 := m69 (UFin m) $ m10 k
  have hcancel : ∀ x : Γ(affineSpaceFin k m, ⊤),
      (_c0.hom.appTop).hom
        ((_c0.inv.appTop).hom x) = x := by
    intro x
    exact iso_hom_inv_apply
      (Scheme.Γ.mapIso _c0.op) x
  have h2 : (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom (m7 i)
      = (_c0.hom.appTop).hom
        (((GSpecIso $ m10 $ MvU m k).inv).hom
          (m7 i)) := rfl
  rw [h2, ← AffineSpace.SpecIso_inv_appTop_coord (m10 k) i, hcancel]

theorem specIso_hom_comp_map_C :
    hom (AffineSpace.SpecIso (UFin m) $ CommRingCat.of k) ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvU m k)) =
      affineSpaceFinToSpec k m := by
  have h : isoI (AffineSpace.SpecIso (UFin m) $ CommRingCat.of k) ≫
      affineSpaceFinToSpec k m =
      Spec.map (ofHom
        MvPolynomial.C) := by
    simp
  rw [← h, hom_inv_id_assoc]

theorem mvPolynomialIsoGlobalSectionsAffineSpace_hom_C a :
    (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom (MvPolynomial.C a)
      = ((affineSpaceFinToSpec k m).appTop).hom
        (((Scheme.GSpecIso $ CommRingCat.of k).inv).hom a) := by
  let _a3 := MvU m k
  let _a0 := CommRingCat.ofHom (m8 : RingHom k _a3)
  let _a2 := (m69 (UFin m) $ m10 k).hom.appTop
  let _a4 := hAT $ affineSpaceFinToSpec k m
  have h0 : hAT (m12 _a0) ≫
      _a2
      = _a4 := by
    refine hom_ext $ m48 fun z => ?_
    exact congrArg (fun ph_ : affineSpaceFin k m ⟶ Sp k =>
      (hAT ph_).hom z) $ specIso_hom_comp_map_C k m
  let _a1 := isoI (GSpecIso $ m10 _a3) ≫ _a2
  have key : _a0 ≫
      _a1
      = isoI (GSpecIso $ m10 k) ≫ _a4 := by
    rw [← assoc, Scheme.ΓSpecIso_inv_naturality, assoc, h0]
  have e1 : (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom (m8 a)
      = (_a0 ≫
          _a1) a := rfl
  rw [e1, key]
  rfl

theorem affineSpaceFin_globalSections_hom_ext {T : CRC}
    (u v : Γ(affineSpaceFin k m, ⊤) ⟶ T)
    (hta : ∀ t : Γ(Sp k, ⊤),
      u.hom (((affineSpaceFinToSpec k m).appTop).hom t)
        = v.hom (((affineSpaceFinToSpec k m).appTop).hom t))
    (hc : ∀ j : Fin m,
      u.hom (AffineSpace.coord (Sp k) (up j : UFin m))
        = v.hom (AffineSpace.coord (Sp k) (up j : UFin m))) :
    u = v := by
  let _a0 := mvPolynomialIsoGlobalSectionsAffineSpace k m
  have key : ∀ w,
      u.hom (_a0.hom.hom w) = v.hom (_a0.hom.hom w) := by
    intro w
    refine induction_on
      (motive := fun z =>
        u.hom (_a0.hom.hom z) = v.hom (_a0.hom.hom z))
      w (fun a => ?_) (fun q r hq hr => ?_) fun q i hq => ?_
    rw [mvPolynomialIsoGlobalSectionsAffineSpace_hom_C]
    exact hta _
    simp [map_add]
    rw [hq, hr]
    obtain ⟨j⟩ := i
    simp [map_mul]
    rw [hq, mvPolynomialIsoGlobalSectionsAffineSpace_hom_X, hc j]
  refine hom_ext $ m48 fun z => ?_
  have h := key $ _a0.inv.hom z
  rwa [iso_hom_inv_apply] at h
end

theorem coordBlowupSubstMap_appTop_affineSpaceFinToSpec (t : Γ(Sp k, ⊤)) :
    ((coordBlowupSubstMap k m S s).appTop).hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = ((affineSpaceFinToSpec k m).appTop).hom t := by
  have h :=
    congrArg (fun ph_ : affineSpaceFin k m ⟶ Sp k => (hAT ph_).hom t)
      (coordBlowupSubstMap_comp_affineSpaceFinToSpec k m S s)
  rwa [comp_appTop_apply] at h

theorem chart_appTop_coordBlowupSubstMap_apply (B : BlowupChart pi_ c S s) (z : Γ(affineSpaceFin k m, ⊤)) :
    (B.chart.map.appTop).hom (((coordBlowupSubstMap k m S s).appTop).hom z)
      = ((pi_.resLE U B.domain B.domain_le).appTop).hom ((c.map.appTop).hom z) := by
  have h :=
    congrArg (fun ph_ : B.domain.toScheme ⟶ affineSpaceFin k m => (hAT ph_).hom z) B.comm
  rwa [comp_appTop_apply, comp_appTop_apply] at h

theorem etaleChart_appTop_affineSpaceFinToSpec_apply {Y : Sch} {q : Y ⟶ Sp k}
    {W : Opn Y} (d : EtaleChart q W m) (t : Γ(Sp k, ⊤)) :
    W.topIso.hom.hom ((d.map.appTop).hom $ ((affineSpaceFinToSpec k m).appTop).hom t)
      = sectionsAlgebraMap k q W (((GSpecIso $ CommRingCat.of k).hom).hom t) := by
  have ha : affineSpaceGlobalSectionsHom k m
      (m8 $ ((GSpecIso $ m10 k).hom).hom t)
      = (hAT $ affineSpaceFinToSpec k m).hom t := by
    rw [← mvPolynomialIsoGlobalSectionsAffineSpace_hom_apply k m, mvPolynomialIsoGlobalSectionsAffineSpace_hom_C, iso_inv_hom_apply]
  rw [← ha]
  exact coordRingHom_C d _

section
variable (B : BlowupChart pi_ c S s)
def constToCoordRelationQuotient :
    (X.sec U) →+*
      (MvPolynomial (UFin m) (X.sec U) ⧸ Ideal.span (Set.range B.coordRelation)) :=
  (Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))).comp MvPolynomial.C

section
variable (y : (X.sec U))
theorem constToCoordRelationQuotient_apply :
    constToCoordRelationQuotient B y = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.C y) := rfl

theorem coordEvalQuotientHom_constToCoordRelationQuotient :
    B.coordEvalQuotientHom (constToCoordRelationQuotient B y) = (appLE pi_ U B.domain B.domain_le).hom y := by
  rw [constToCoordRelationQuotient_apply, coordEvalQuotientHom_mk, coordEvalHom_C]
end

def affineSectionsToCoordRelationQuotient :
    Γ(affineSpaceFin k m, ⊤) ⟶
      CommRingCat.of
        (MvPolynomial (UFin m) (X.sec U) ⧸ span (range B.coordRelation)) :=
  ofHom
    ((eval₂Hom ((constToCoordRelationQuotient B).comp (sectionsAlgebraMap k p U))
        (fun i : UFin m =>
          Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.X i))).comp
      (mvPolynomialIsoGlobalSectionsAffineSpace k m).inv.hom)

def openSectionsToCoordRelationQuotient :
    Γ(toScheme U, ⊤) ⟶
      CommRingCat.of
        (MvPolynomial (UFin m) (X.sec U) ⧸ span (range B.coordRelation)) :=
  ofHom ((constToCoordRelationQuotient B).comp (U.topIso.hom.hom))

theorem openSectionsToCoordRelationQuotient_apply (y : Γ(U.toScheme, ⊤)) :
    (openSectionsToCoordRelationQuotient B).hom y
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.C (U.topIso.hom.hom y)) := rfl

theorem affineSectionsToCoordRelationQuotient_coord (j : Fin m) :
    (affineSectionsToCoordRelationQuotient B).hom
        (AffineSpace.coord (Sp k) (ULift.up j : UFin m))
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.X (ULift.up j : UFin m)) := by
  let _a1 := mvPolynomialIsoGlobalSectionsAffineSpace k m
  have h : _a1.inv.hom
      (AffineSpace.coord (Sp k) $ up j)
      = MvPolynomial.X (up j) := by
    rw [← mvPolynomialIsoGlobalSectionsAffineSpace_hom_X k m $ up j, iso_inv_hom_apply]
  have h2 : (affineSectionsToCoordRelationQuotient B).hom
        (m9 (Sp k) $ up j)
      = eval₂Hom ((constToCoordRelationQuotient B).comp $ sectionsAlgebraMap k p U)
          (fun i =>
            m5 (m17 $ m30 B.coordRelation) $ m7 i)
        (_a1.inv.hom
          (m9 (Sp k) $ ULift.up j)) := rfl
  rw [h2, h, eval₂Hom_X']

theorem affineSectionsToCoordRelationQuotient_affineSpaceFinToSpec
    (t : Γ(Sp k, ⊤)) :
    (affineSectionsToCoordRelationQuotient B).hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = constToCoordRelationQuotient B (sectionsAlgebraMap k p U
          (((GSpecIso (CommRingCat.of k)).hom).hom t)) := by
  have ha : (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom
      (m8 $ ((GSpecIso $ m10 k).hom).hom t)
      = (hAT $ affineSpaceFinToSpec k m).hom t := by
    rw [mvPolynomialIsoGlobalSectionsAffineSpace_hom_C, iso_inv_hom_apply]
  have h : (mvPolynomialIsoGlobalSectionsAffineSpace k m).inv.hom ((hAT $ affineSpaceFinToSpec k m).hom t)
      = m8 (((GSpecIso $ m10 k).hom).hom t) := by
    rw [← ha, iso_inv_hom_apply]
  have h2 : (affineSectionsToCoordRelationQuotient B).hom ((hAT $ affineSpaceFinToSpec k m).hom t)
      = eval₂Hom ((constToCoordRelationQuotient B).comp $ sectionsAlgebraMap k p U)
          (fun i =>
            m5 (m17 $ m30 B.coordRelation) $ m7 i)
        ((mvPolynomialIsoGlobalSectionsAffineSpace k m).inv.hom $ (hAT $ affineSpaceFinToSpec k m).hom t) := rfl
  rw [h2, h, eval₂Hom_C]
  rfl

theorem openSectionsToCoordRelationQuotient_coord (j : Fin m) :
    (openSectionsToCoordRelationQuotient B).hom
        ((c.map.appTop).hom
          (AffineSpace.coord (Sp k) (ULift.up j : UFin m)))
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.C (c.coord j)) := by
  rw [openSectionsToCoordRelationQuotient_apply, ← coord_def c j]

theorem mk_eq_mk_C_coord (j : Fin m) :
    Ideal.Quotient.mk (span $ range B.coordRelation)
        ((if j ∈ S ∧ j ≠ s then
            MvPolynomial.X (up j : UFin m) *
              MvPolynomial.X (up s : UFin m)
          else MvPolynomial.X (ULift.up j : UFin m)) :
            MvPolynomial (UFin m) $ X.sec U)
      = Ideal.Quotient.mk (Ideal.span $ Set.range B.coordRelation)
        (MvPolynomial.C $ c.coord j) := by
  have h : m5 (span $ range B.coordRelation) (B.coordRelation j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr $ subset_span ⟨j, rfl⟩
  rwa [coordRelation_def, map_sub, sub_eq_zero] at h

theorem appTop_comp_affineSectionsToCoordRelationQuotient :
    (coordBlowupSubstMap k m S s).appTop ≫ affineSectionsToCoordRelationQuotient B = c.map.appTop ≫ openSectionsToCoordRelationQuotient B := by
  refine affineSpaceFin_globalSections_hom_ext k m _ _ (fun t => ?_) fun j => ?_
  rw [comp_hom_apply, comp_hom_apply, coordBlowupSubstMap_appTop_affineSpaceFinToSpec,
    affineSectionsToCoordRelationQuotient_affineSpaceFinToSpec, openSectionsToCoordRelationQuotient_apply, etaleChart_appTop_affineSpaceFinToSpec_apply c t]
  rfl
  rw [comp_hom_apply, comp_hom_apply, openSectionsToCoordRelationQuotient_coord]
  by_cases hjS : j ∈ S
  by_cases hjs : j = s
  subst hjs
  rw [coordBlowupSubstMap_appTop_coord_self, affineSectionsToCoordRelationQuotient_coord]
  have hrel := mk_eq_mk_C_coord B j
  rwa [if_neg $ by simp] at hrel
  rw [coordBlowupSubstMap_appTop_coord_of_mem k m S s j hjS hjs, map_mul, affineSectionsToCoordRelationQuotient_coord,
    affineSectionsToCoordRelationQuotient_coord, ← map_mul]
  have hrel := mk_eq_mk_C_coord B j
  rwa [if_pos ⟨hjS, hjs⟩] at hrel
  rw [coordBlowupSubstMap_appTop_coord_of_notMem k m S s j hjS, affineSectionsToCoordRelationQuotient_coord]
  have hrel := mk_eq_mk_C_coord B j
  rwa [if_neg $ by tauto] at hrel

section
variable (hU : IsAffineOpen U) (hB : IsPullback B.chart.map (pi_.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
include hU hB
theorem bijective_coordEvalQuotientHom_of_isPullback :
    Bijective B.coordEvalQuotientHom := by
  have hUaff : IsAffine U.toScheme := hU
  let _a1 := coordBlowupSubstMap k m S s
  have hPaff : IsAffine (m131 _a1 c.map) :=
    inferInstance
  have hDaff : IsAffine B.domain.toScheme := IsAffine.of_isIso hB.isoPullback.hom
  let _a0 := pi_.resLE U B.domain B.domain_le
  have HP : IsPushout _a1.appTop c.map.appTop B.chart.map.appTop
      _a0.appTop :=
    AlgebraicGeometry.isPushout_appTop_of_isPullback hB
  obtain ⟨De_, hinl, hinr⟩ :
      ∃ De_ : Γ(B.domain.toScheme, ⊤) ⟶
          m10
            (MvPolynomial (UFin m) U.sec ⧸ span (range B.coordRelation)),
        B.chart.map.appTop ≫ De_ = affineSectionsToCoordRelationQuotient B ∧
          _a0.appTop ≫ De_ = openSectionsToCoordRelationQuotient B :=
    ⟨HP.desc (affineSectionsToCoordRelationQuotient B) (openSectionsToCoordRelationQuotient B) (appTop_comp_affineSectionsToCoordRelationQuotient B),
      HP.inl_desc _ _ _, HP.inr_desc _ _ _⟩
  have hinl' : ∀ z, De_.hom ((B.chart.map.appTop).hom z) = (affineSectionsToCoordRelationQuotient B).hom z := by
    intro z
    have h := congrArg (m4 · z) hinl
    rwa [comp_hom_apply] at h
  have hinr' : ∀ y, De_.hom ((hAT _a0).hom y)
      = (openSectionsToCoordRelationQuotient B).hom y := by
    intro y
    have h := congrArg (m4 · y) hinr
    rwa [comp_hom_apply] at h
  have hbeta : De_ ≫ ofHom B.coordEvalQuotientHom = B.domain.topIso.hom := by
    refine HP.hom_ext ?_ ?_
    rw [← assoc, hinl]
    refine affineSpaceFin_globalSections_hom_ext k m _ _ (fun t => ?_) fun j => ?_
    rw [comp_hom_apply, comp_hom_apply, affineSectionsToCoordRelationQuotient_affineSpaceFinToSpec,
      ← etaleChart_appTop_affineSpaceFinToSpec_apply c t, hom_ofHom, coordEvalQuotientHom_constToCoordRelationQuotient,
      appLE_topIso_hom_apply pi_ U B.domain B.domain_le,
      ← chart_appTop_coordBlowupSubstMap_apply B $ (hAT (affineSpaceFinToSpec k m)).hom t,
      coordBlowupSubstMap_appTop_affineSpaceFinToSpec]
    rw [comp_hom_apply, comp_hom_apply, affineSectionsToCoordRelationQuotient_coord,
      CommRingCat.hom_ofHom, coordEvalQuotientHom_mk, coordEvalHom_X, coord_def B.chart j]
    rw [← assoc, hinr]
    refine CommRingCat.hom_ext $ m48 fun y => ?_
    rw [comp_hom_apply, comp_hom_apply, CommRingCat.hom_ofHom,
      openSectionsToCoordRelationQuotient_apply, coordEvalQuotientHom_mk, coordEvalHom_C,
      appLE_topIso_hom_apply pi_ U B.domain B.domain_le]
  have hbeta' : ∀ z, B.coordEvalQuotientHom (De_.hom z) = B.domain.topIso.hom.hom z := by
    intro z
    have h := congrArg (m4 · z) hbeta
    rwa [comp_hom_apply] at h
  have hring : (De_.hom).comp ((B.domain.topIso.inv.hom).comp B.coordEvalQuotientHom)
      = m99 _ := by
    refine Ideal.Quotient.ringHom_ext ?_
    refine ringHom_ext (fun a => ?_) fun i => ?_
    simp only [m82, id_apply]
    rw [coordEvalQuotientHom_mk, coordEvalHom_C, topIso_inv_appLE_apply, hinr', openSectionsToCoordRelationQuotient_apply,
      iso_hom_inv_apply]
    obtain ⟨j⟩ := i
    simp only [m82, id_apply]
    rw [coordEvalQuotientHom_mk, coordEvalHom_X, coord_def B.chart j, iso_inv_hom_apply,
      hinl', affineSectionsToCoordRelationQuotient_coord]
  have halpha : ∀ q, De_.hom (B.domain.topIso.inv.hom (B.coordEvalQuotientHom q)) = q := by
    intro q
    simpa only [m82, id_apply] using (congr_fun hring q)
  refine ⟨fun x y hxy => ?_, fun y => ⟨De_.hom (B.domain.topIso.inv.hom y), ?_⟩⟩
  rw [← halpha x, ← halpha y, hxy]
  rw [hbeta', iso_hom_inv_apply]

theorem surjective_coordEvalHom :
    Surjective B.coordEvalHom := by
  intro y
  obtain ⟨q, hq⟩ := an2 (bijective_coordEvalQuotientHom_of_isPullback B hU hB) y
  obtain ⟨a, rfl⟩ := mk_surjective q
  exact ⟨a, hq⟩

theorem bijective_coordEvalQuotientHom :
    Bijective B.coordEvalQuotientHom :=
  bijective_coordEvalQuotientHom_of_isPullback B hU hB
end
end

end BlowupChart




variable {X X1 : Sch} {k : Type} [Field k]
  {p : X ⟶ Sp k} {pi_ : X1 ⟶ X} {Z : ISD X}
  {E : Bdy X}

section
variable (hZ : HasStrictNormalCrossingsWith p Z E) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
include hZ hpi_
theorem hasStrictNormalCrossingsWith_exceptionalIdeal :
    HasStrictNormalCrossingsWith (pi_ ≫ p) (exceptionalIdeal pi_ Z) [] := by
  rw [hasStrictNormalCrossingsWith_iff]
  intro x hx
  rw [p9] at hx
  have hy : bsM pi_ x ∈ spI Z := by
    simp at hx
    exact hx
  obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hy
  obtain ⟨s, hs, hxs⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZU x hyU
  let _a1 := blowupChartOfIsBlowup pi_ c S hpi_ hZU s hs
  refine ⟨_a1.domain, hxs, m,
    _a1.chart, fun _ => none, {s}, ?_, ?_, ?_, BlowupChart.restrictIdeal_exceptionalIdeal (blowupChartOfIsBlowup pi_ c S hpi_ hZU s hs) Z hs hZU⟩
  simp_all
  intro i hi
  exact absurd hi $ not_lt_zero i
  intro i hi
  exact absurd hi $ not_lt_zero i

theorem isSmoothDivisor_exceptionalIdeal :
    IsSmoothDivisor (pi_ ≫ p) $ exceptionalIdeal pi_ Z := by
  let _a0 := p5 pi_ Z
  have hcart := an1 hpi_
  rw [← p9] at hcart
  exact mpr_ (isSmoothDivisor_iff (pi_ ≫ p) _a0) ⟨hcart, smooth_subschemeio_comp_of_hasStrictNormalCrossingsWith _a0 [] $ hasStrictNormalCrossingsWith_exceptionalIdeal hZ hpi_⟩
end

theorem smooth_io_comp_of_etaleChart {Y : Sch} {K : Type}
    [Field K] {q : Y ⟶ Sp K} {V : Opn Y} {n : ℕ} (c : EtaleChart q V n) :
    Smooth $ ι V ≫ q := by
  have := c.isEtale
  rw [← c.comp_struct]
  infer_instance

theorem smooth_comp_of_isBlowupAlongIdealSheaf [Smooth p] (hZ : HasStrictNormalCrossingsWith p Z E) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) :
    Smooth $ pi_ ≫ p := by
  let _a1 := pi_ ≫ p
  have key : ∀ x, ∃ V : Opn X1, x ∈ V ∧ Smooth (opI V ≫ _a1) := by
    intro x
    by_cases hxs : bsM pi_ x ∈ spI Z
    obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hxs
    obtain ⟨s, hs, hxB⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZU x hyU
    let _a0 := blowupChartOfIsBlowup pi_ c S hpi_ hZU s hs
    exact ⟨_a0.domain, hxB,
      smooth_io_comp_of_etaleChart _a0.chart⟩
    refine ⟨pre pi_ $ suppC Z, hxs, ?_⟩
    have :=
      blowupIsIsoOffCenter X X1 pi_ Z hpi_
    have h1 : opI (pre pi_ $ suppC Z) ≫ _a1 =
        morphismRestrict pi_ (suppC Z) ≫
          (p4 (suppC Z) ≫ p) := by
      rw [← assoc, ← morphismRestrict_ι, assoc]
    rw [h1]
    infer_instance
  choose U hU hsm using key
  refine smooth_of_iSup_eq_top _a1 U ?_ hsm
  rw [eq_top_iff]
  intro x _
  exact mpr_ mem_iSup ⟨x, hU x⟩

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch} {k : Type} [Field k] {p : X ⟶ Sp k} {U : Opn X} {m : ℕ}
section
variable (c : EtaleChart p U m)
section
variable (V : U.toScheme.Opens)
def EtaleChart.restrictOpens : EtaleChart (ι U ≫ p) V m where
  map := ι V ≫ c.map
  comp_struct := by
    rw [assoc, c.comp_struct]
  isEtale := by
    have : Etale c.map := c.isEtale
    infer_instance

@[simp]
theorem EtaleChart.restrictOpens_map :
    (c.restrictOpens V).map = ι V ≫ c.map := rfl

theorem EtaleChart.restrictIdeal_coordIdeal T :
    restrictIdeal (c.coordIdeal T) V = (c.restrictOpens V).coordIdeal T := by
  simp [restrictIdeal_eq_comap_io, coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrictOpens_map,
    comap_comp]
end

section
variable {V} (hV : IsAffineOpen V)
theorem EtaleChart.coordIdeal_ideal_eq_span T :
    (c.coordIdeal T).ideal ⟨V, hV⟩ = span ((c.restrictOpens V).coord '' ↑T) :=
  ideal_eq_span_coord (c.restrictOpens V) hV (c.coordIdeal T) T
    (c.restrictIdeal_coordIdeal V T)

theorem EtaleChart.coordIdeal_singleton_ideal_eq_span i :
    (c.coordIdeal {i}).ideal ⟨V, hV⟩ = span {(c.restrictOpens V).coord i} := by
  rw [c.coordIdeal_ideal_eq_span hV {i}, coe_singleton, image_singleton]
end

theorem EtaleChart.saturation_mul_coordIdeal
    j s (hjs : j ≠ s)
    [QuasiCompact $ saturationio (c.coordIdeal {s})
      (c.coordIdeal {j} * c.coordIdeal {s})] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {j} * c.coordIdeal {s}) = c.coordIdeal {j} := by
  let _a0 := c.coordIdeal {j}
  refine m29 $ funext ?_
  intro V
  have ht :=
    c.coordIdeal_singleton_ideal_eq_span V.2 s
  have hfactor : (_a0 * (c.coordIdeal {s})).ideal V =
      span {((c.restrictOpens V.1).coord s)} * _a0.ideal V := by
    rw [ideal_mul, Pi.mul_apply, ht]
    exact mul_comm _ _
  refine saturation_ideal_eq_of_eq_mul _ _ V _ ht _ hfactor ?_
  intro g hg
  rw [c.coordIdeal_singleton_ideal_eq_span V.2 j] at hg ⊢
  exact mem_span_coord_of_coord_mul_mem V.2 (c.restrictOpens V.1) hjs g hg

theorem EtaleChart.saturation_coordIdeal_self s
    [QuasiCompact $ saturationio (c.coordIdeal {s}) $ c.coordIdeal {s}] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {s}) = ⊤ := by
  have key : ∀ V : U.toScheme.affineOpens,
      (saturation (c.coordIdeal {s}) $ c.coordIdeal {s}).ideal V = ⊤ := by
    intro V
    have ht :=
      c.coordIdeal_singleton_ideal_eq_span V.2 s
    exact saturation_ideal_eq_top_of_span_pow_le (c.coordIdeal {s}) (c.coordIdeal {s}) V
      ((c.restrictOpens V.1).coord s) ht 1 $ by simp [ht]
  ext V
  simp [key V, ideal_top]
end

theorem mem_span_coord_of_coord_pow_mul_mem
    (hU : IsAffineOpen U) (c : EtaleChart p U m) {j s} (hjs : j ≠ s) :
    ∀ n (x : ↑(X.presheaf.obj $ op U)),
      c.coord s ^ n * x ∈ span {c.coord j} → x ∈ span {c.coord j} := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa using hx
  | succ n ih =>
      intro x hx
      refine mem_span_coord_of_coord_mul_mem hU c hjs x $ ih (c.coord s * x) ?_
      have h : c.coord s ^ n * (c.coord s * x) = c.coord s ^ (n + 1) * x := by ring
      rwa [h]

theorem EtaleChart.saturation_coordIdeal_of_ne (c : EtaleChart p U m)
    j s (hjs : j ≠ s)
    [QuasiCompact $ saturationio (c.coordIdeal {s}) $ c.coordIdeal {j}] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {j}) = c.coordIdeal {j} := by
  ext V f
  rw [mem_saturation_ideal_iff (c.coordIdeal {s}) (c.coordIdeal {j}) V
      ((c.restrictOpens V.1).coord s) (c.coordIdeal_singleton_ideal_eq_span V.2 s) f, c.coordIdeal_singleton_ideal_eq_span V.2 j]
  constructor
  rintro ⟨n, hn⟩
  exact mem_span_coord_of_coord_pow_mul_mem V.2 (c.restrictOpens V.1) hjs n f hn
  intro hf
  exact ⟨0, by simpa using hf⟩
end

namespace BlowupChart

variable {X X1 : Sch} {k : Type} [Field k]
  {p : X ⟶ Sp k} {pi_ : X1 ⟶ X} {U : Opn X} {m : ℕ}
  {c : EtaleChart p U m} {S : FinSet m} {s : Fin m}

section
variable (B : BlowupChart pi_ c S s) (Z D : ISD X)
section
variable [QuasiCompact (strictTransformio pi_ Z D)] (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
include hs hZ
theorem restrictIdeal_strictTransform_of_mem_of_ne
    (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform pi_ Z D) B.domain = B.chart.coordIdeal {j} := by
  have hqc : QuasiCompact $ saturationio (cmI Z pi_) $ cmI D pi_ :=
    inferInstanceAs $ QuasiCompact $ strictTransformio pi_ Z D
  have hE : restrictIdeal (cmI Z pi_) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [p9] at h
  have hDrestrict :=
    B.restrictIdeal_comap_coordIdeal_of_mem D j hj hjs hD
  have hq := quasiCompact_saturationio_restrictIdeal (cmI Z pi_) (cmI D pi_) B.domain
  rw [hE, hDrestrict] at hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (cmI Z pi_) (cmI D pi_) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_mul_coordIdeal j s hjs

theorem restrictIdeal_strictTransform_coordIdeal_self
    (hD : restrictIdeal D U = c.coordIdeal {s}) :
    restrictIdeal (Blowup.strictTransform pi_ Z D) B.domain = ⊤ := by
  have hqc : QuasiCompact $ saturationio (cmI Z pi_) $ cmI D pi_ :=
    inferInstanceAs $ QuasiCompact $ strictTransformio pi_ Z D
  have hE : restrictIdeal (cmI Z pi_) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [p9] at h
  have hDrestrict :=
    B.restrictIdeal_comap_coordIdeal_self D hD
  have hq := quasiCompact_saturationio_restrictIdeal (cmI Z pi_) (cmI D pi_) B.domain
  rw [hE, hDrestrict] at hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (cmI Z pi_) (cmI D pi_) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_coordIdeal_self s

theorem restrictIdeal_strictTransform_coordIdeal_of_notMem
    j (hj : j ∉ S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform pi_ Z D) B.domain = B.chart.coordIdeal {j} := by
  have hqc : QuasiCompact $ saturationio (cmI Z pi_) $ cmI D pi_ :=
    inferInstanceAs $ QuasiCompact $ strictTransformio pi_ Z D
  have hjs : j ≠ s := by
    rintro rfl
    exact hj hs
  have hE : restrictIdeal (cmI Z pi_) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [p9] at h
  have hDrestrict :=
    B.restrictIdeal_comap_coordIdeal_of_not_mem D j hj hD
  have hq := quasiCompact_saturationio_restrictIdeal (cmI Z pi_) (cmI D pi_) B.domain
  rw [hE, hDrestrict] at hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (cmI Z pi_) (cmI D pi_) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_coordIdeal_of_ne j s hjs

theorem restrictIdeal_strictTransform_coordIdeal
    (j : Fin m) (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform pi_ Z D) B.domain =
      if j = s then ⊤ else B.chart.coordIdeal {j} := by
  by_cases hj : j = s
  rw [if_pos hj]
  refine B.restrictIdeal_strictTransform_coordIdeal_self Z D hs hZ ?_
  rw [hD, hj]
  rw [if_neg hj]
  by_cases hjS : j ∈ S
  exact B.restrictIdeal_strictTransform_of_mem_of_ne Z D hs hZ j hjS hj hD
  exact B.restrictIdeal_strictTransform_coordIdeal_of_notMem Z D hs hZ j hjS hD
end

theorem restrictIdeal_strictTransform_of_eq_top (hD : restrictIdeal D U = ⊤) :
    restrictIdeal (Blowup.strictTransform pi_ Z D) B.domain = ⊤ := by
  have h3 : restrictIdeal (cmI D pi_) B.domain ≤
      restrictIdeal (p6 pi_ Z D) B.domain := by
    rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io]
    exact comap_mono (p4 B.domain) $ comap_le_strictTransform pi_ Z D
  rw [B.restrictIdeal_comap_top D hD] at h3
  exact le_antisymm le_top h3
end

end BlowupChart





variable {X X1 : Sch} {k : Type} [Field k]
  {p : X ⟶ Sp k} {pi_ : X1 ⟶ X} {U : Opn X} {m : ℕ}
  {c : EtaleChart p U m} {S : FinSet m} {s : Fin m}

section
variable (hU : IsAffineOpen U)
include hU
theorem mk_coord_eq_zero_of_mem (Z : ISD X)
    (hZ : restrictIdeal Z U = c.coordIdeal S) i (hi : i ∈ S) :
    (Ideal.Quotient.mk $ Z.ideal ⟨U, hU⟩) (c.coord i) = 0 := by
  rw [eq_zero_iff_mem, ideal_eq_span_coord c hU Z S hZ]
  exact subset_span $ mem_image_of_mem c.coord $ Finset.mem_coe.mpr hi

section
variable (Z : ISD X)
section
variable (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart pi_ c S s)
include hZ
theorem quotientMk_comp_appLE_eq_zero_of_mem :
    ∀ a ∈ Z.ideal ⟨U, hU⟩,
      ((Ideal.Quotient.mk $ span {B.chart.coord s}).comp
          (appLE pi_ U B.domain B.domain_le).hom) a = 0 := by
  let _a0 := appLE pi_ U B.domain B.domain_le
  let _a1 := span {B.chart.coord s}
  have key : span (c.coord '' (S : Set $ Fin m)) ≤
      m119 _a0.hom
        _a1 := by
    rw [span_le]
    rintro x ⟨i, hi, rfl⟩
    have hmem : _a0.hom (c.coord i) ∈
        _a1 := by
      by_cases his : i = s
      subst his
      rw [BlowupChart.appLE_coord_self B]
      exact mem_span_singleton_self _
      rw [BlowupChart.appLE_coord_of_mem B i (Finset.mem_coe.mp hi) his]
      exact mul_mem_left _ _ $ mem_span_singleton_self _
    exact hmem
  intro a ha
  rw [comp_apply, eq_zero_iff_mem]
  rw [ideal_eq_span_coord c hU Z S hZ] at ha
  exact Ideal.mem_comap.mp $ key ha

def exceptionalQuotientBaseHom (_hs : s ∈ S) :
    ((X.sec U) ⧸ Z.ideal ⟨U, hU⟩) →+* ((X1.sec B.domain) ⧸ span {B.chart.coord s}) :=
  lift (Z.ideal ⟨U, hU⟩)
    ((Ideal.Quotient.mk $ span {B.chart.coord s}).comp
      (appLE pi_ U B.domain B.domain_le).hom)
    (quotientMk_comp_appLE_eq_zero_of_mem hU Z hZ B)

section
variable (hs : s ∈ S)
theorem exceptionalQuotientBaseHom_mk
    a :
    exceptionalQuotientBaseHom hU Z hZ B hs ((Ideal.Quotient.mk $ Z.ideal ⟨U, hU⟩) a) =
      (Ideal.Quotient.mk $ span {B.chart.coord s})
        ((appLE pi_ U B.domain B.domain_le).hom a) :=
  rfl

def mvPolynomialToExceptionalQuotient :
    MvPolynomial ↥(S.erase s) ((X.sec U) ⧸ Z.ideal ⟨U, hU⟩) →+*
      ((X1.sec B.domain) ⧸ span {B.chart.coord s}) :=
  eval₂Hom (exceptionalQuotientBaseHom hU Z hZ B hs)
    (fun t => (Ideal.Quotient.mk $ span {B.chart.coord s}) $ B.chart.coord t.1)

theorem mvPolynomialToExceptionalQuotient_C
    r :
    mvPolynomialToExceptionalQuotient hU Z hZ B hs (MvPolynomial.C r) = exceptionalQuotientBaseHom hU Z hZ B hs r :=
  eval₂Hom_C _ _ r

theorem mvPolynomialToExceptionalQuotient_X
    (t : ↥(S.erase s)) :
    mvPolynomialToExceptionalQuotient hU Z hZ B hs (MvPolynomial.X t) =
      (Ideal.Quotient.mk $ span {B.chart.coord s}) (B.chart.coord t.1) :=
  eval₂Hom_X' _ _ t
end
end

section
variable (cc : EtaleChart p U m) (SS : FinSet m) (ss : Fin m)
section
variable (j : Fin m)
def exceptionalVar :
    MvPolynomial ↥(SS.erase ss) $ (X.sec U) ⧸ Z.ideal ⟨U, hU⟩ :=
  if h : j ∈ SS.erase ss then MvPolynomial.X ⟨j, h⟩
  else MvPolynomial.C $ (Ideal.Quotient.mk $ Z.ideal ⟨U, hU⟩) $ cc.coord j

theorem exceptionalVar_of_mem
    (h : j ∈ SS.erase ss) :
    exceptionalVar hU Z cc SS ss j = MvPolynomial.X ⟨j, h⟩ :=
  dif_pos h

theorem exceptionalVar_of_not_mem
    (h : j ∉ SS.erase ss) :
    exceptionalVar hU Z cc SS ss j =
      MvPolynomial.C ((Ideal.Quotient.mk $ Z.ideal ⟨U, hU⟩) $ cc.coord j) :=
  dif_neg h
end

def exceptionalEvalHom :
    MvPolynomial (UFin m) (X.sec U) →+*
      MvPolynomial ↥(SS.erase ss) ((X.sec U) ⧸ Z.ideal ⟨U, hU⟩) :=
  eval₂Hom
    ((MvPolynomial.C : ((X.sec U) ⧸ Z.ideal ⟨U, hU⟩) →+*
        MvPolynomial ↥(SS.erase ss) ((X.sec U) ⧸ Z.ideal ⟨U, hU⟩)).comp
      (Ideal.Quotient.mk $ Z.ideal ⟨U, hU⟩))
    (fun i => exceptionalVar hU Z cc SS ss i.down)

theorem exceptionalEval_C a :
    exceptionalEvalHom hU Z cc SS ss (MvPolynomial.C a) =
      MvPolynomial.C ((Ideal.Quotient.mk $ Z.ideal ⟨U, hU⟩) a) :=
  eval₂Hom_C _ _ a

theorem exceptionalEval_X j :
    exceptionalEvalHom hU Z cc SS ss (MvPolynomial.X $ up j) = exceptionalVar hU Z cc SS ss j :=
  eval₂Hom_X' _ _ $ up j
end

section
variable (hZ : restrictIdeal Z U = c.coordIdeal S) (B : BlowupChart pi_ c S s) (hs : s ∈ S)
include hZ hs
theorem exceptionalEval_eq_zero_of_mem_span_coordRelation :
    ∀ a ∈ span (range B.coordRelation), exceptionalEvalHom hU Z c S s a = 0 := by
  have hsub : span (range B.coordRelation) ≤ ker (exceptionalEvalHom hU Z c S s) := by
    rw [span_le]
    rintro x ⟨i, rfl⟩
    simp [mem_coe, mem_ker]
    have hpr : B.coordRelation i =
        (if i ∈ S ∧ i ≠ s then
            m7 (up i) * m7 (up s)
          else m7 $ up i) - m8 (c.coord i) := rfl
    have hsnot : s ∉ S.erase s := fun hc => an1 (mp_ mem_erase hc) rfl
    rw [hpr]
    by_cases h : i ∈ S ∧ i ≠ s
    rw [if_pos h, map_sub, map_mul, exceptionalEval_X, exceptionalEval_X, exceptionalEval_C,
      exceptionalVar_of_not_mem hU Z c S s s hsnot,
      mk_coord_eq_zero_of_mem hU Z hZ s hs, mk_coord_eq_zero_of_mem hU Z hZ i h.1, map_zero,
      mul_zero, sub_zero]
    have hnot := fun hc =>
      h ⟨an2 $ mp_ mem_erase hc, an1 $ mp_ mem_erase hc⟩
    rw [if_neg h, map_sub, exceptionalEval_X, exceptionalEval_C,
      exceptionalVar_of_not_mem hU Z c S s i hnot, sub_self]
  intro a ha
  exact RingHom.mem_ker.mp $ hsub ha

section
variable (hB : IsPullback B.chart.map (pi_.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map)
include hB
def exceptionalHomOfChart :
    (X1.sec B.domain) →+* MvPolynomial ↥(S.erase s) ((X.sec U) ⧸ Z.ideal ⟨U, hU⟩) :=
  (lift (span (range B.coordRelation)) (exceptionalEvalHom hU Z c S s)
      (exceptionalEval_eq_zero_of_mem_span_coordRelation hU Z hZ B hs)).comp
    (ofBijective B.coordEvalQuotientHom (B.bijective_coordEvalQuotientHom hU hB)).symm.toRingHom

theorem exceptionalHomOfChart_coordEvalHom
    f :
    exceptionalHomOfChart hU Z hZ B hs hB (B.coordEvalHom f) = exceptionalEvalHom hU Z c S s f := by
  let _a0 := ofBijective B.coordEvalQuotientHom $ B.bijective_coordEvalQuotientHom hU hB
  let _a1 := span $ range B.coordRelation
  let _a2 := _a0.symm $ B.coordEvalHom f
  have h1 : _a2 = (m5 _a1) f := by
    apply _a0.injective
    rw [RingEquiv.apply_symm_apply]
    exact (BlowupChart.coordEvalQuotientHom_mk B f).symm
  have h2 : exceptionalHomOfChart hU Z hZ B hs hB (B.coordEvalHom f)
      = m201 _a1 (exceptionalEvalHom hU Z c S s)
          (exceptionalEval_eq_zero_of_mem_span_coordRelation hU Z hZ B hs)
          _a2 := rfl
  simp [h2, h1, lift_mk]

theorem exceptionalHomOfChart_coord
    i :
    exceptionalHomOfChart hU Z hZ B hs hB (B.chart.coord i) = exceptionalVar hU Z c S s i := by
  rw [← BlowupChart.coordEvalHom_X B i, exceptionalHomOfChart_coordEvalHom, exceptionalEval_X]

theorem exceptionalHomOfChart_coord_self :
    exceptionalHomOfChart hU Z hZ B hs hB (B.chart.coord s) = 0 := by
  rw [exceptionalHomOfChart_coord hU Z hZ B hs hB s,
    exceptionalVar_of_not_mem hU Z c S s s fun hc => an1 (mp_ mem_erase hc) rfl,
    mk_coord_eq_zero_of_mem hU Z hZ s hs, map_zero]

def exceptionalHomOfQuotientCoord :
    ((X1.sec B.domain) ⧸ span {B.chart.coord s}) →+*
      MvPolynomial ↥(S.erase s) ((X.sec U) ⧸ Z.ideal ⟨U, hU⟩) :=
  lift (span {B.chart.coord s}) (exceptionalHomOfChart hU Z hZ B hs hB)
    (by
      intro a ha
      obtain ⟨x, rfl⟩ := mem_span_singleton'.mp ha
      rw [map_mul, exceptionalHomOfChart_coord_self hU Z hZ B hs hB, mul_zero])

theorem exceptionalHomOfQuotientCoord_mk
    a :
    exceptionalHomOfQuotientCoord hU Z hZ B hs hB ((Ideal.Quotient.mk (span {B.chart.coord s})) a)
      = exceptionalHomOfChart hU Z hZ B hs hB a :=
  rfl

theorem bijective_mvPolynomialToExceptionalQuotient :
    Bijective (mvPolynomialToExceptionalQuotient hU Z hZ B hs) := by
  let _a0 := mvPolynomialToExceptionalQuotient hU Z hZ B hs
  have hcomp : _a0.comp (exceptionalEvalHom hU Z c S s)
      = (m5 $ span {B.chart.coord s}).comp B.coordEvalHom := by
    refine ringHom_ext ?_ ?_
    intro a
    simp [comp_apply]
    rw [exceptionalEval_C, BlowupChart.coordEvalHom_C B a, mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk]
    rintro ⟨i⟩
    simp [comp_apply]
    rw [exceptionalEval_X, BlowupChart.coordEvalHom_X B i]
    by_cases h : i ∈ S.erase s
    rw [exceptionalVar_of_mem hU Z c S s i h, mvPolynomialToExceptionalQuotient_X]
    have hEq : (appLE pi_ U B.domain B.domain_le).hom (c.coord i) = B.chart.coord i := by
      by_cases his : i = s
      subst his
      exact BlowupChart.appLE_coord_self B
      exact BlowupChart.appLE_coord_of_not_mem B i
        (fun hi => h $ mpr_ mem_erase ⟨his, hi⟩)
    rw [exceptionalVar_of_not_mem hU Z c S s i h, mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk, hEq]
  constructor
  have hleft : (exceptionalHomOfQuotientCoord hU Z hZ B hs hB).comp _a0
      = m99 (MvPolynomial (S.erase s) $ U.sec ⧸ Z.ideal ⟨U, hU⟩) := by
    refine ringHom_ext ?_ ?_
    intro r
    obtain ⟨a, rfl⟩ := m108 r
    simp [m82, id_apply]
    rw [mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk, exceptionalHomOfQuotientCoord_mk, ← BlowupChart.coordEvalHom_C B a,
      exceptionalHomOfChart_coordEvalHom, exceptionalEval_C]
    intro t
    simp [m82, id_apply]
    rw [mvPolynomialToExceptionalQuotient_X, exceptionalHomOfQuotientCoord_mk, exceptionalHomOfChart_coord]
    exact exceptionalVar_of_mem hU Z c S s t.1 t.2
  intro x y hxy
  have hx : exceptionalHomOfQuotientCoord hU Z hZ B hs hB (_a0 x) = x :=
    m156 hleft x
  have hy : exceptionalHomOfQuotientCoord hU Z hZ B hs hB (_a0 y) = y :=
    m156 hleft y
  rw [← hx, ← hy, hxy]
  intro y
  obtain ⟨b, rfl⟩ := mk_surjective y
  obtain ⟨f, rfl⟩ := B.surjective_coordEvalHom hU hB b
  exact ⟨exceptionalEvalHom hU Z c S s f, m156 hcomp f⟩

def exceptionalQuotientEquivMvPolynomial :
    ((X1.sec B.domain) ⧸ span {B.chart.coord s}) ≃+*
      MvPolynomial ↥(S.erase s) ((X.sec U) ⧸ Z.ideal ⟨U, hU⟩) :=
  (ofBijective (mvPolynomialToExceptionalQuotient hU Z hZ B hs) $ bijective_mvPolynomialToExceptionalQuotient hU Z hZ B hs hB).symm

theorem exceptionalQuotientEquivMvPolynomial_symm_apply
    f :
    (exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB).symm f = mvPolynomialToExceptionalQuotient hU Z hZ B hs f :=
  rfl

theorem exceptionalQuotientEquivMvPolynomial_mk_appLE
    (a : (X.sec U)) :
    exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB
        ((Ideal.Quotient.mk $ span {B.chart.coord s})
          ((appLE pi_ U B.domain B.domain_le).hom a)) =
      MvPolynomial.C ((Ideal.Quotient.mk $ Z.ideal ⟨U, hU⟩) a) := by
  apply (exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB).symm.injective
  rw [symm_apply_apply, exceptionalQuotientEquivMvPolynomial_symm_apply, mvPolynomialToExceptionalQuotient_C, exceptionalQuotientBaseHom_mk]

theorem exceptionalQuotientEquivMvPolynomial_mk_coord
    (i : Fin m) (hi : i ∈ S) (his : i ≠ s) :
    exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB
        ((Ideal.Quotient.mk $ span {B.chart.coord s}) $ B.chart.coord i) =
      MvPolynomial.X ⟨i, mem_erase.mpr ⟨his, hi⟩⟩ := by
  apply (exceptionalQuotientEquivMvPolynomial hU Z hZ B hs hB).symm.injective
  rw [symm_apply_apply, exceptionalQuotientEquivMvPolynomial_symm_apply]
  exact sy_ $ mvPolynomialToExceptionalQuotient_X hU Z hZ B hs ⟨i, mpr_ mem_erase ⟨his, hi⟩⟩
end
end
end

section
variable {Z : ISD X} (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (hZ : restrictIdeal Z U = c.coordIdeal S) (hs : s ∈ S)
theorem isAffineOpen_blowupChart_domain :
    IsAffineOpen (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).domain :=
  by
    have hUaff : IsAffine U.toScheme := hU
    have hA : IsAffine $ affineSpaceFin k m := inferInstance
    have hP : IsAffine $ m131 (coordBlowupSubstMap k m S s) c.map := inferInstance
    exact IsAffine.of_isIso (isPullback_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZ s hs).isoPullback.hom

def exceptionalQuotientEquivOfIsBlowup :
    (Γ(X1, (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).domain) ⧸
        span {(blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).chart.coord s}) ≃+*
      MvPolynomial ↥(S.erase s) ((X.sec U) ⧸ Z.ideal ⟨U, hU⟩) :=
  exceptionalQuotientEquivMvPolynomial hU Z hZ (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs) hs
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZ s hs)

theorem exceptionalQuotientEquiv_mk_appLE
    (a : (X.sec U)) :
    exceptionalQuotientEquivOfIsBlowup hU hpi_ hZ hs
        ((Ideal.Quotient.mk
            (span {(blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).chart.coord s}))
          ((appLE pi_ U (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).domain
            (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).domain_le).hom a)) =
      MvPolynomial.C ((Ideal.Quotient.mk $ Z.ideal ⟨U, hU⟩) a) :=
  exceptionalQuotientEquivMvPolynomial_mk_appLE hU Z hZ (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs) hs
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZ s hs) a

theorem exceptionalQuotientEquiv_mk_coord
    (i : Fin m) (hi : i ∈ S) (his : i ≠ s) :
    exceptionalQuotientEquivOfIsBlowup hU hpi_ hZ hs
        ((Ideal.Quotient.mk
            (span {(blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).chart.coord s}))
          ((blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).chart.coord i)) =
      MvPolynomial.X ⟨i, mem_erase.mpr ⟨his, hi⟩⟩ :=
  exceptionalQuotientEquivMvPolynomial_mk_coord hU Z hZ (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs) hs
    (isPullback_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZ s hs) i hi his

theorem exceptionalIdeal_ideal_blowupChart_domain :
    (exceptionalIdeal pi_ Z).ideal
        ⟨(blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).domain,
          isAffineOpen_blowupChart_domain hU hpi_ hZ hs⟩ =
      span {(blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).chart.coord s} := by
  let _a0 := blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs
  rw [ideal_eq_span_coord _a0.chart
      (isAffineOpen_blowupChart_domain hU hpi_ hZ hs) (p5 pi_ Z) {s}
      (BlowupChart.restrictIdeal_exceptionalIdeal _a0 Z hs hZ),
    coe_singleton, image_singleton]
end
end

end FunctorialResolution.EmbeddedResolution

end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
theorem exists_closure_singleton_eq_of_maximal_irreducible {C S : Set X}
    (hC : IsIrreducible C) (hCS : C ⊆ S)
    (hmax : ∀ T : Set X, IsIrreducible T → T ⊆ S → C ⊆ T → T = C)
    (hS : IsClosed S) : ∃ xi_ : X, closure ({xi_} : Set X) = C := by
  have hCclosed : IsClosed C := by
    exact mp_ closure_eq_iff_isClosed $ hmax (closure C) hC.closure (hS.closure_subset_iff.mpr hCS) subset_closure
  obtain ⟨xi_, hxi_⟩ := m140 hC hCclosed
  exact ⟨xi_, hxi_⟩

theorem eq_of_mem_closure_singleton_of_maximal_irreducible {C S : Set X}
    (_hC : IsIrreducible C) (_hCS : C ⊆ S)
    (hmax : ∀ T : Set X, IsIrreducible T → T ⊆ S → C ⊆ T → T = C)
    (hS : IsClosed S) {xi_ xi' : X} (hxi_ : closure ({xi_} : Set X) = C) (hxi_' : xi' ∈ S)
    (hspec : xi_ ∈ closure ({xi'} : Set X)) : xi' = xi_ := by
  have hCsub : C ⊆ closure ({xi'} : Set X) := by
    rw [← hxi_]
    exact closure_minimal (mpr_ singleton_subset_iff hspec) isClosed_closure
  refine (mpr_ inseparable_iff_closure_eq ?_).eq
  rw [hmax _ ((isIrreducible_singleton (x := xi')).closure) (hS.closure_subset_iff.mpr $ mpr_ singleton_subset_iff hxi_') hCsub, hxi_]

section
variable {U} (hU : IsAffineOpen U)
theorem map_germ_primeIdealOf_le_maximalIdeal (x : ↥U) :
    Ideal.map (CommRingCat.Hom.hom $ X.presheaf.germ U x.1 x.2) (hU.primeIdealOf x).asIdeal
      ≤ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x.1) := by
  have := hU.isLocalization_stalk x
  refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
  rw [mem_comap]
  exact mpr_ (IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hU.primeIdealOf x).asIdeal a) ha

theorem exists_primeIdealOf_eq (q : PrimeSpectrum (X.sec U)) :
    ∃ y : ↥U, hU.primeIdealOf y = q := by
  exact ⟨hU.isoSpec.inv.base q, congrArg (fun f : Spec U.sec ⟶ Spec U.sec => bsM f q) hU.isoSpec.inv_hom_id⟩
end

theorem le_orderAt_of_ideal_le_pow (J : ISD X) {U : Opn X}
    (hU : IsAffineOpen U) (x : ↥U) (n : ℕ)
    (h : J.ideal ⟨U, hU⟩ ≤ asIdeal (hU.primeIdealOf x) ^ n) :
    ((n : ℕ) : ENat) ≤ orderAt J (x : X) := by
  let _c0 := m4 $ pGerm X U x.1 x.2
  rw [le_orderAt_iff, stalkIdeal_eq_map_germ J x ⟨U, hU⟩ x.2]
  calc m6 _c0 (J.ideal ⟨U, hU⟩)
      ≤ m6 _c0
          (asIdeal (hU.primeIdealOf x) ^ n) := map_mono h
    _ = (m6 _c0
          (hU.primeIdealOf x).asIdeal) ^ n := m219 _ _ _
    _ ≤ m16 (stkX X x.1) ^ n :=
        pow_right_mono (map_germ_primeIdealOf_le_maximalIdeal hU x) n

private theorem mem_support_iff_ideal_le_primeIdealOf (I : ISD X)
    {U : Opn X} (hU : IsAffineOpen U) (x : ↥U) :
    (x : X) ∈ support I ↔ I.ideal ⟨U, hU⟩ ≤ asIdeal (hU.primeIdealOf x) := by
  constructor
  intro hx
  exact ideal_le_primeIdealOf I hU x.2 hx
  intro hx
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_eq_map_germ I x ⟨U, hU⟩ x.2]
  exact le_trans (map_mono hx) $ map_germ_primeIdealOf_le_maximalIdeal hU x
end

section
variable {A : Type} [CommRing A] {T : Type}
section
variable (x : T → A)
def powProd (f : T →₀ ℕ) : A :=
  f.prod fun t n => x t ^ n

theorem prod_pow_mem_pow_sum (I : Ideal A) (hx : ∀ t : T, x t ∈ I) (g : T → ℕ) (s : Finset T) :
    (∏ t ∈ s, x t ^ g t) ∈ I ^ (∑ t ∈ s, g t) := by
  classical
  refine Finset.induction_on s ?_ ?_
  simp
  intro a s ha ih
  rw [prod_insert ha, sum_insert ha, pow_add]
  exact mul_mem_mul (pow_mem_pow (hx a) $ g a) ih

theorem powProd_add (f g : T →₀ ℕ) :
    powProd x (f + g) = powProd x f * powProd x g := by
  show (f + g).prod (fun t n => x t ^ n)
      = f.prod (fun t n => x t ^ n) * g.prod fun t n => x t ^ n
  exact prod_add_index' (fun a => pow_zero $ x a) fun a b1_ b2_ => pow_add (x a) b1_ b2_

theorem powProd_zero :
    powProd x (0 : T →₀ ℕ) = 1 := by
  simp [powProd]
end

theorem powProd_single [DecidableEq T] (x : T → A)
    (t : T) (n : ℕ) : powProd x (single t n) = x t ^ n := by
  show (single t n).prod (fun t m => x t ^ m) = x t ^ n
  exact prod_single_index $ pow_zero $ x t
end

section
variable {R : Type} [CommRing R]
theorem isPrime_map_C (P : Ideal R) [P.IsPrime] (σ : Type) :
    (Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) P).IsPrime := by
  have _i43 : Ideal.map MvPolynomial.C P = ker (MvPolynomial.map (Ideal.Quotient.mk P) : MvPolynomial σ R →+* MvPolynomial σ (R ⧸ P)) := by
    rw [ker_map, mk_ker]
  rw [_i43]
  constructor
  rw [ne_top_iff_one]
  intro hmem
  have h1 := RingHom.mem_ker.mp hmem
  rw [map_one] at h1
  have h2 := congrArg constantCoeff h1
  simp only [map_one, map_zero] at h2
  exact one_ne_zero h2
  intro x y hxy
  rw [mem_ker, map_mul] at hxy
  rcases mp_ mul_eq_zero hxy with h | h
  exact m51 $ RingHom.mem_ker.mpr h
  exact m61 $ RingHom.mem_ker.mpr h

theorem C_coeff_mem_of_minimal_prime {σ : Type}
    (Pp : Ideal $ MvPolynomial σ R) [Pp.IsPrime]
    (hmin : ∀ K : Ideal $ MvPolynomial σ R, K.IsPrime → K ≤ Pp → Pp ≤ K)
    {p : MvPolynomial σ R} (hp : p ∈ Pp) (d : σ →₀ ℕ) :
    MvPolynomial.C (p.coeff d) ∈ Pp := by
  have hge := hmin _
    (isPrime_map_C (m119 (m8 : R →+* MvPolynomial σ R) Pp) σ) $ Ideal.map_le_iff_le_comap.mpr le_rfl
  exact Ideal.mem_comap.mp $ (mp_ mem_map_C_iff $ hge hp) d

theorem C_mul_powProd_X_eq_monomial {σ : Type}
    (f : σ →₀ ℕ) (r : R) :
    MvPolynomial.C r * powProd (fun t : σ => (MvPolynomial.X t : MvPolynomial σ R)) f
      = monomial f r :=
  symm monomial_eq
end

section
variable {T : Type}
def totalDegree (f : T →₀ ℕ) : ℕ := f.sum fun _ n => n

theorem totalDegree_single [DecidableEq T] (t : T) (n : ℕ) :
    totalDegree (single t n) = n := by
  show (single t n).sum (fun _ m => m) = n
  exact sum_single_index rfl

theorem totalDegree_add (f g : T →₀ ℕ) : totalDegree (f + g) = totalDegree f + totalDegree g := by
  show (f + g).sum (fun _ n => n) = f.sum (fun _ n => n) + g.sum fun _ n => n
  exact sum_add_index' (fun _ => rfl) fun _ _ _ => rfl

theorem totalDegree_zero : totalDegree (0 : T →₀ ℕ) = 0 := by
  simp [totalDegree]
end

section
variable {A B : Type} [CommRing A] [CommRing B] {T : Type} (ph_ : A →+* B)
theorem map_powProd
    (x : T → A) (f : T →₀ ℕ) : ph_ (powProd x f) = powProd (fun t => ph_ $ x t) f := by
  classical
  simp [powProd, Finsupp.prod, map_prod, map_pow]

end

section
variable {A : Type} [CommRing A]
theorem powProd_mem_pow_totalDegree {T : Type} (x : T → A) (I : Ideal A)
    (hx : ∀ t : T, x t ∈ I) (f : T →₀ ℕ) : powProd x f ∈ I ^ totalDegree f := by
  have h1 : powProd x f = ∏ t ∈ f.support, x t ^ f t := rfl
  have h2 : totalDegree f = ∑ t ∈ f.support, f t := rfl
  rw [h1, h2]
  exact prod_pow_mem_pow_sum x I hx f f.support

section
variable {m} (x : Fin m → A) (S : FinSet m) (s : Fin m)
section
variable (c : ℕ)
def chartMonomial (f : ↥(S.erase s) →₀ ℕ) : A :=
  x s ^ (c - totalDegree f) * powProd (fun t : ↥(S.erase s) => x t.1) f

def chartMonomialIdeal : Ideal A :=
  span {a : A | ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧ a = chartMonomial x S s c f}

theorem chartMonomialIdeal_eq_span :
    chartMonomialIdeal x S s c =
      span {a : A | ∃ f : ↥(S.erase s) →₀ ℕ, totalDegree f ≤ c ∧
        a = chartMonomial x S s c f} := rfl

section
variable (f) (hf : totalDegree f ≤ c)
include hf
theorem chartMonomial_mem_chartMonomialIdeal :
    chartMonomial x S s c f ∈ chartMonomialIdeal x S s c := by
  rw [chartMonomialIdeal_eq_span x S s c]
  exact subset_span ⟨f, hf, rfl⟩

end
end

theorem pow_span_image_le_chartMonomialIdeal (_hs : s ∈ S) (c : ℕ) :
    span (x '' (S : Set $ Fin m)) ^ c ≤ chartMonomialIdeal x S s c := by
  induction c with
  | zero =>
      rw [pow_zero, m217, top_le_iff, eq_top_iff_one]
      have h0 : 1 = chartMonomial x S s 0 0 := by
        simp [chartMonomial, totalDegree_zero, powProd_zero]
      rw [h0]
      exact chartMonomial_mem_chartMonomialIdeal x S s 0 0 totalDegree_zero.le
  | succ c ih =>
      rw [pow_succ]
      refine Ideal.mul_le.mpr ?_
      intro r hr y hy
      have key : span (x '' (S : Set $ Fin m)) ≤
          Submodule.comap (mulRight A r) (chartMonomialIdeal x S s $ c + 1) := by
        refine Ideal.span_le.mpr ?_
        rintro a ⟨i, hi, rfl⟩
        simp [mem_coe, mulRight_apply]
        rw [mul_comm (x i) r]
        have key : chartMonomialIdeal x S s c ≤
            Submodule.comap (mulRight A $ x i) (chartMonomialIdeal x S s $ c + 1) := by
          rw [chartMonomialIdeal_eq_span x S s c]
          refine Ideal.span_le.mpr ?_
          rintro a ⟨f, hf, rfl⟩
          simp [mem_coe, mulRight_apply]
          by_cases his : i = s
          have hx : chartMonomial x S s c f * x i = chartMonomial x S s c f * x s := by rw [his]
          rw [hx]
          have h1 : c + 1 - totalDegree f = (c - totalDegree f) + 1 := by omega
          have h2 : chartMonomial x S s c f * x s = chartMonomial x S s (c + 1) f := by
            simp [chartMonomial, h1, pow_succ]
            ring
          rw [h2]
          exact chartMonomial_mem_chartMonomialIdeal x S s (c + 1) f $ hf.trans $ le_succ c
          let t : (S.erase s) := ⟨i, mpr_ mem_erase ⟨his, Finset.mem_coe.mp hi⟩⟩
          have hdeg : totalDegree (f + single t 1) = totalDegree f + 1 := by
            rw [totalDegree_add, totalDegree_single]
          have h3 : c + 1 - (totalDegree f + 1) = c - totalDegree f := by omega
          have h2 : chartMonomial x S s c f * x t.1
              = chartMonomial x S s (c + 1) (f + single t 1) := by
            simp [chartMonomial, hdeg, h3, powProd_add, powProd_single, pow_one]
            ring
          rw [h2]
          refine chartMonomial_mem_chartMonomialIdeal x S s (c + 1) (f + single t 1) ?_
          rw [hdeg]
          omega
        have h := key $ ih hr
        rwa [Submodule.mem_comap, mulRight_apply] at h
      have h := key hy
      rw [Submodule.mem_comap, mulRight_apply] at h
      rwa [mul_comm r y]
end
end

section
variable {A B : Type} [CommRing A] [CommRing B] (ph_ : A →+* B) {m} (x : Fin m → A) (y : Fin m → B) (S : FinSet m) (s : Fin m)
theorem map_chartMonomial
    (hphs : ph_ (x s) = y s)
    (hph : ∀ i ∈ S, i ≠ s → ph_ (x i) = y i * y s)
    (c : ℕ) (f : ↥(S.erase s) →₀ ℕ) (hf : totalDegree f ≤ c) :
    ph_ (chartMonomial x S s c f) =
      y s ^ c * powProd (fun t : ↥(S.erase s) => y t.1) f := by
  let _a0 := S.erase s
  have hfun : ∀ t : _a0, ph_ (x t.1) = y t.1 * y s := by
    intro t
    obtain ⟨hts, htS⟩ := mp_ mem_erase t.2
    exact hph t.1 htS hts
  have hmon : chartMonomial x S s c f
      = x s ^ (c - totalDegree f) * powProd (fun t : _a0 => x t.1) f := rfl
  have key : ph_ (powProd (fun t : _a0 => x t.1) f) = powProd (fun t : _a0 => y t.1) f * (y s) ^ totalDegree f := by
    classical
    refine induction_linear f ?_ ?_ ?_
    simp [powProd_zero, totalDegree_zero, pow_zero, mul_one, map_one]
    intro p q hp hq
    simp [powProd_add, totalDegree_add, map_mul, hp, hq, pow_add]
    ring
    intro t n
    simp [powProd_single, totalDegree_single, map_pow, hfun, mul_pow]
  rw [hmon, map_mul, map_pow, hphs, key]
  have hc : y s ^ c = y s ^ (c - totalDegree f) * y s ^ totalDegree f := by
    rw [← pow_add, sub_add_cancel hf]
  rw [hc]
  ring

theorem ideal_le_comap_pow_succ_of_map_le_span_pow_mul (hs : s ∈ S)
    (hphs : ph_ (x s) = y s)
    (hph : ∀ i ∈ S, i ≠ s → ph_ (x i) = y i * y s)
    (hy : y s ∈ nonZeroDivisors B)
    (e : (B ⧸ span {y s}) ≃+*
      MvPolynomial ↥(S.erase s) (A ⧸ span (x '' (S : Set (Fin m)))))
    (heC : ∀ a : A, e (Ideal.Quotient.mk (span {y s}) (ph_ a)) =
      MvPolynomial.C (Ideal.Quotient.mk (span (x '' (S : Set (Fin m)))) a))
    (heX : ∀ t : ↥(S.erase s),
      e (Ideal.Quotient.mk (span {y s}) (y t.1)) = MvPolynomial.X t)
    (P : Ideal B) [P.IsPrime] (hyP : y s ∈ P)
    (hPmin : ∀ Q : Ideal B, Q.IsPrime → Q ≤ P → y s ∈ Q → P ≤ Q)
    (c : ℕ) (J : Ideal A) (hJ : J ≤ span (x '' (S : Set (Fin m))) ^ c)
    (J' : Ideal B) (hJ'P : J' ≤ P)
    (hmap : Ideal.map ph_ J ≤ span {y s ^ c} * J') :
    J ≤ Ideal.comap ph_ P ^ (c + 1) := by
  classical
  let _a0 := span $ x '' (S : Set (Fin m))
  let _a1 := span {y s}
  obtain ⟨Ps_, hPssurj, hPs_⟩ :
      ∃ Ps_ : B →+* MvPolynomial (S.erase s) (A ⧸ _a0),
        Surjective Ps_ ∧
          ∀ b, Ps_ b = e (m5 _a1 b) := by
    refine ⟨e.toRingHom.comp (m5 _a1), ?_, ?_⟩
    intro q
    obtain ⟨z, hz⟩ := e.surjective q
    obtain ⟨b, hb⟩ := mk_surjective z
    refine ⟨b, ?_⟩
    show e (m5 _a1 b) = q
    rw [hb, hz]
    intro b
    simp
  have hPs0 : Ps_ (y s) = 0 := by
    rw [hPs_, Ideal.Quotient.eq_zero_iff_mem.mpr $ mem_span_singleton_self (y s), map_zero]
  have hPsC : ∀ a, Ps_ (ph_ a)
      = m8 (m5 _a0 a) := by
    intro a
    rw [hPs_]
    exact heC a
  let _a2 := S.erase s
  have hPsX : ∀ t : _a2, Ps_ (y t.1) = m7 t := by
    intro t
    rw [hPs_]
    exact heX t
  have hkerP : ker Ps_ ≤ P := by
    intro b hb
    have hb0 := RingHom.mem_ker.mp hb
    rw [hPs_] at hb0
    refine Ideal.span_le.mpr (mpr_ singleton_subset_iff hyP)
      (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
    apply e.injective
    rw [hb0, map_zero]
  let _a3 := m6 Ps_ P
  have hcomapP : m119 Ps_ _a3 ≤ P := by
    intro b hb
    obtain ⟨p0, hp0P, hp0b⟩ :=
      (mem_map_iff_of_surjective Ps_ hPssurj).mp (Ideal.mem_comap.mp hb)
    have hkb : b - p0 ∈ ker Ps_ := by
      rw [mem_ker, map_sub, hp0b, sub_self]
    simpa using (P.add_mem (hkerP hkb) hp0P)
  have hPprime : _a3.IsPrime := by
    constructor
    intro htop
    have h1 : (1 : MvPolynomial (S.erase s) (A ⧸ _a0))
        ∈ _a3 := by
      rw [htop]
      exact mem_top
    have h2 : 1 ∈ m119 Ps_ _a3 := by simp_all
    have hPtop : P = ⊤ := by simp_all
    exact Ideal.IsPrime.ne_top ‹P.IsPrime› hPtop
    intro p q hpq
    obtain ⟨b, rfl⟩ := hPssurj p
    obtain ⟨b', rfl⟩ := hPssurj q
    have hb : b * b' ∈ P := by
      apply hcomapP
      rwa [mem_comap, map_mul]
    rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hb with h | h
    exact m51 $ mem_map_of_mem Ps_ h
    exact m61 $ mem_map_of_mem Ps_ h
  have hmin : ∀ K : Ideal (MvPolynomial (S.erase s)
      (A ⧸ _a0)),
      K.IsPrime → K ≤ _a3 → _a3 ≤ K := by
    intro K hK hle
    have h2 := le_trans (Ideal.comap_mono hle) hcomapP
    have h3 : y s ∈ m119 Ps_ K := by simp_all
    exact le_trans (map_mono (hPmin (m119 Ps_ K) (comap_isPrime Ps_ K) h2 h3)) $ Ideal.map_le_iff_le_comap.mpr le_rfl
  let _a5 := m119 ph_ P
  have hxQ : ∀ i ∈ S, x i ∈ _a5 := by
    intro i hi
    rw [mem_comap]
    by_cases h : i = s
    rwa [h, hphs]
    rw [hph i hi h]
    exact mul_mem_left _ _ hyP
  have hmonQ : ∀ f, totalDegree f ≤ c →
      chartMonomial x S s c f ∈ _a5 ^ c := by
    intro f hf
    have h1 : x s ^ (c - totalDegree f) ∈ _a5 ^ (c - totalDegree f) :=
      pow_mem_pow (hxQ s hs) _
    have h2 :=
      powProd_mem_pow_totalDegree (fun t : _a2 => x t.1) _a5
        (fun t => hxQ t.1 $ mem_of_mem_erase t.2) f
    have h3 := mul_mem_mul h1 h2
    rwa [← pow_add, sub_add_cancel hf] at h3
  intro a ha
  obtain ⟨cf, hcfsupp, hcfsum⟩ := mp_ mem_span_set (pow_span_image_le_chartMonomialIdeal x S s hs c (hJ ha))
  have hex : ∀ g ∈ cf.support, ∃ f,
      totalDegree f ≤ c ∧ g = chartMonomial x S s c f := by
    intro g hg
    exact hcfsupp $ Finset.mem_coe.mpr hg
  choose! fsel hfdeg hfeq using hex
  have hinj : ∀ g ∈ cf.support, ∀ g' ∈ cf.support, fsel g = fsel g' → g = g' := by
    intro g hg g' hg' hgg
    have e1 := hfeq g hg
    rw [hgg] at e1
    exact tr_ e1 (hfeq g' hg').symm
  have hsum : a = ∑ i ∈ cf.support, cf i * i := by
    rw [← hcfsum]
    simp [Finsupp.sum, smul_eq_mul]
  have ha' : a = ∑ i ∈ cf.support, cf i * chartMonomial x S s c (fsel i) := by
    rw [hsum]
    refine sum_congr rfl ?_
    intro i hi
    rw [← hfeq i hi]
  have hpha : ph_ a = y s ^ c *
      ∑ i ∈ cf.support, ph_ (cf i) * powProd (fun t : _a2 => y t.1) (fsel i) := by
    rw [ha', map_sum, mul_sum]
    refine sum_congr rfl ?_
    intro i hi
    rw [map_mul, map_chartMonomial ph_ x y S s hphs hph c (fsel i) (hfdeg i hi)]
    ring
  obtain ⟨j, hjJ', hjeq⟩ := mp_ mem_span_singleton_mul (hmap $ mem_map_of_mem ph_ ha)
  have hueq : (∑ i ∈ cf.support, ph_ (cf i) *
      powProd (fun t : _a2 => y t.1) (fsel i)) = j := by
    refine mp_ (mul_cancel_left_mem_nonZeroDivisors (pow_mem hy c)) ?_
    rw [← hpha]
    exact sy_ hjeq
  have huP := hJ'P hjJ'
  rw [← hueq] at huP
  have hPsu : Ps_ (∑ i ∈ cf.support, ph_ (cf i) *
        powProd (fun t : _a2 => y t.1) (fsel i))
      = ∑ i ∈ cf.support, monomial (fsel i)
          (m5 _a0 (cf i)) := by
    rw [map_sum]
    refine sum_congr rfl ?_
    intro i _
    rw [map_mul, hPsC, map_powProd, funext hPsX]
    exact C_mul_powProd_X_eq_monomial (fsel i) _
  have hcoeff : ∀ g0_ ∈ cf.support,
      (∑ i ∈ cf.support, monomial (fsel i)
            (m5 _a0 (cf i))).coeff (fsel g0_)
        = m5 _a0 (cf g0_) := by
    intro g0_ hg0_
    have hstep : ∀ g ∈ cf.support, g ≠ g0_ →
        (monomial (fsel g)
          (m5 _a0 (cf g))).coeff (fsel g0_) = 0 := by
      intro g hg hne
      have hne' := fun hh => hne $ hinj g hg g0_ hg0_ hh
      rw [coeff_monomial, if_neg hne']
    rw [coeff_sum, sum_eq_single_of_mem g0_ hg0_ hstep,
      coeff_monomial]
    simp
  have hcfQ : ∀ g ∈ cf.support, cf g ∈ _a5 := by
    intro g hg
    have h1 :=
      mem_map_of_mem Ps_ huP
    rw [hPsu] at h1
    have h2 := C_coeff_mem_of_minimal_prime _a3 hmin h1 $ fsel g
    rw [hcoeff g hg] at h2
    have h3 : Ps_ (ph_ (cf g)) ∈ _a3 := by
      rwa [hPsC]
    exact Ideal.mem_comap.mpr $ hcomapP (Ideal.mem_comap.mpr h3)
  rw [ha']
  refine m133 _ ?_
  intro i hi
  rw [pow_succ, mul_comm]
  exact mul_mem_mul (hcfQ i hi) $ hmonQ (fsel i) (hfdeg i hi)
end

theorem controlledTransform_not_subset_support {k : Type} [Field k] [CharZero k]
    {X X1 : Sch} (p : X ⟶ Sp k) [Smooth p]
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1]
    (Z : ISD X) (E : Bdy X) (hE : HasStrictNormalCrossingsWith p Z E)
    (pi_ : X1 ⟶ X) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
    (J : ISD X) (c : ℕ)
    (hord : ∀ x : X, x ∈ Z.support → orderAt J x = (c : ENat))
    (J' : ISD X1)
    (htr : exceptionalIdeal pi_ Z ^ c * J' = J.comap pi_)
    (C : Set X1)
    (hCirr : IsIrreducible C)
    (hCsub : C ⊆ ((exceptionalIdeal pi_ Z).support : Set X1))
    (hCmax : ∀ T : Set X1, IsIrreducible T →
      T ⊆ ((exceptionalIdeal pi_ Z).support : Set X1) → C ⊆ T → T = C) :
    ¬ (C ⊆ (J'.support : Set X1)) := by
  let _c0 := exceptionalIdeal pi_ Z
  classical
  intro hCJ'
  have hZsm :=
    smooth_subschemeio_comp_of_hasStrictNormalCrossingsWith Z E hE
  have hclosed :=
    _c0.support.2
  obtain ⟨xi_, hxi_⟩ := exists_closure_singleton_eq_of_maximal_irreducible hCirr hCsub hCmax hclosed
  have hxiC_ : xi_ ∈ C := by
    rw [← hxi_]
    exact subset_closure rfl
  have hxiE := hCsub hxiC_
  have hzZ : bsM pi_ xi_ ∈ Z.support := by
    have h1 : xi_ ∈ (Z.comap pi_).support := by
      rwa [← Blowup.exceptionalIdeal_eq_comap pi_ Z]
    rwa [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at h1
  obtain ⟨U, hU, m, cc, S, hzU, hspan⟩ :=
    exists_chart_ideal_eq_span_coord p Z (bsM pi_ xi_) hzZ
  have hZU :=
    restrictIdeal_eq_coordIdeal_of_ideal_eq_span hU cc Z S hspan
  obtain ⟨s, hs, hxiV_⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ cc S hpi_ hZU xi_ hzU
  set B := blowupChartOfIsBlowup pi_ cc S hpi_ hZU s hs with hBdef
  have hV := isAffineOpen_blowupChart_domain hU hpi_ hZU hs
  set ph_ := (appLE pi_ U B.domain B.domain_le).hom with hphdef
  set P : Ideal B.domain.sec := asIdeal (hV.primeIdealOf ⟨xi_, hxiV_⟩) with hPdef
  have hPprime := (hV.primeIdealOf ⟨xi_, hxiV_⟩).isPrime
  have hexcid :=
    exceptionalIdeal_ideal_blowupChart_domain hU hpi_ hZU hs
  have hyP : B.chart.coord s ∈ P := by
    have h := mp_ (mem_support_iff_ideal_le_primeIdealOf _c0 hV ⟨xi_, hxiV_⟩) hxiE
    rw [hexcid] at h
    exact h $ mem_span_singleton_self _
  have hJ'P :=
    (mem_support_iff_ideal_le_primeIdealOf J' hV ⟨xi_, hxiV_⟩).mp $ hCJ' hxiC_
  have hphs := B.appLE_coord_self
  have hph : ∀ i ∈ S, i ≠ s → ph_ (cc.coord i) = B.chart.coord i * B.chart.coord s := by
    intro i hi his
    exact B.appLE_coord_of_mem i hi his
  let _a0 := span $ cc.coord '' (S : Set $ Fin m)
  have hy :=
    coord_mem_nonZeroDivisors hV B.chart s
  set e0 := exceptionalQuotientEquivOfIsBlowup hU hpi_ hZU hs with he0
  set e : (B.domain.sec ⧸ span {B.chart.coord s}) ≃+*
      MvPolynomial (S.erase s)
        (U.sec ⧸ _a0) :=
    e0.trans (mapEquiv (S.erase s) $ quotEquivOfEq hspan) with hedef
  let _m0 := span {B.chart.coord s}
  have heC : ∀ a, e (Ideal.Quotient.mk _m0 $ ph_ a) =
      MvPolynomial.C (Ideal.Quotient.mk _a0 a) := by
    intro a
    have h1 :=
      exceptionalQuotientEquiv_mk_appLE hU hpi_ hZU hs a
    show MvPolynomial.map (quotEquivOfEq hspan).toRingHom
        (e0 $ Ideal.Quotient.mk _m0 $ ph_ a)
      = MvPolynomial.C (Ideal.Quotient.mk _a0 a)
    rw [h1, map_C]
    exact congrArg MvPolynomial.C $ quotEquivOfEq_mk hspan a
  have heX : ∀ t : (S.erase s),
      e (Ideal.Quotient.mk _m0 $ B.chart.coord t.1)
        = MvPolynomial.X t := by
    intro t
    obtain ⟨hts, htS⟩ := mp_ mem_erase t.2
    have h1 :=
      exceptionalQuotientEquiv_mk_coord hU hpi_ hZU hs t.1 htS hts
    show MvPolynomial.map (quotEquivOfEq hspan).toRingHom
        (e0 $ Ideal.Quotient.mk _m0 $ B.chart.coord t.1)
      = MvPolynomial.X t
    rw [h1]
    exact map_X _ _
  have hPmin : ∀ Q : Ideal B.domain.sec, Q.IsPrime → Q ≤ P → B.chart.coord s ∈ Q → P ≤ Q := by
    intro Q hQ hQP hyQ
    obtain ⟨pt, hpt⟩ := exists_primeIdealOf_eq hV ⟨Q, hQ⟩
    let _a6 := (pt : X1)
    have hptE : _a6 ∈ _c0.support := by
      rw [mem_support_iff_ideal_le_primeIdealOf _c0 hV pt, hpt, hexcid]
      exact Ideal.span_le.mpr $ mpr_ singleton_subset_iff hyQ
    let _a1 := PrimeSpectrum $ X1.sec B.domain
    let _a11 := (⟨Q, hQ⟩ : _a1)
    have hmem : hV.primeIdealOf ⟨xi_, hxiV_⟩ ∈
        closure ({_a11} :
          Set _a1) :=
      (le_iff_mem_closure _ _).mp hQP
    let _a5 := hV.fromSpec.base $ hV.primeIdealOf ⟨xi_, hxiV_⟩
    have hfxi : _a5 = xi_ :=
      hV.fromSpec_primeIdealOf ⟨xi_, hxiV_⟩
    have hfQ : hV.fromSpec.base (⟨Q, hQ⟩ : _a1) = _a6 := by
      rw [← hpt]
      exact hV.fromSpec_primeIdealOf pt
    let _s0 := ({_a6} : Set X1)
    have hpre : IsClosed $ preimage hV.fromSpec.base $ closure _s0 :=
      IsClosed.preimage (hV.fromSpec.base.hom.continuous) isClosed_closure
    have hQin : _a11 ∈
        preimage hV.fromSpec.base (closure _s0) := by
      show hV.fromSpec.base (⟨Q, hQ⟩ : _a1)
        ∈ closure _s0
      rw [hfQ]
      exact subset_closure rfl
    have h2 : xi_ ∈ closure _s0 := by
      have h3 : _a5
          ∈ closure _s0 := closure_minimal (mpr_ singleton_subset_iff hQin) hpre hmem
      rwa [hfxi] at h3
    have hxx := eq_of_mem_closure_singleton_of_maximal_irreducible hCirr hCsub hCmax hclosed
      hxi_ hptE h2
    have hpteq : pt = (⟨xi_, hxiV_⟩ : (B.domain)) := Subtype.ext hxx
    rw [hpteq] at hpt
    exact le_of_eq $ congrArg asIdeal hpt
  have hcosupp : ∀ x, x ∈ Z.support → x ∈ U → x ∈ orderAtLeastLocus J c := by
    intro x hx _
    rw [mem_orderAtLeastLocus_iff]
    exact le_of_eq (hord x hx).symm
  have hJpow : J.ideal ⟨U, hU⟩ ≤ _a0 ^ c := by
    have h := ideal_le_pow_of_restrictIdeal_eq_coordIdeal p hU cc Z S hZU c J hcosupp
    rwa [hspan] at h
  have hmap : Ideal.map ph_ (J.ideal ⟨U, hU⟩)
      ≤ span {B.chart.coord s ^ c} * J'.ideal ⟨B.domain, hV⟩ := by
    have h1 :=
      comap_ideal_eq_map_appLE J pi_ ⟨U, hU⟩
        ⟨B.domain, hV⟩ B.domain_le
    have h2 : (_c0 ^ c * J').ideal ⟨B.domain, hV⟩
        = (_c0.ideal ⟨B.domain, hV⟩) ^ c * J'.ideal ⟨B.domain, hV⟩ := by
      rw [show (_c0 ^ c * J').ideal ⟨B.domain, hV⟩
          = (_c0 ^ c).ideal ⟨B.domain, hV⟩ * J'.ideal ⟨B.domain, hV⟩ from rfl,
        ideal_pow]
      rfl
    rw [← h1, ← htr, h2, hexcid, ← span_singleton_pow]
  have hle := ideal_le_comap_pow_succ_of_map_le_span_pow_mul ph_ cc.coord B.chart.coord S s hs hphs hph hy
    e heC heX P hyP hPmin c (J.ideal ⟨U, hU⟩) hJpow (J'.ideal ⟨B.domain, hV⟩) hJ'P hmap
  have hQcprime := comap_isPrime ph_ P
  obtain ⟨pt', hpt'q⟩ :=
    exists_primeIdealOf_eq hU ⟨Ideal.comap ph_ P, hQcprime⟩
  have hz'Z : (pt' : X) ∈ Z.support := by
    rw [mem_support_iff_ideal_le_primeIdealOf Z hU pt', hpt'q, hspan]
    refine Ideal.span_le.mpr ?_
    rintro a ⟨i, hi, rfl⟩
    show cc.coord i ∈ Ideal.comap ph_ P
    rw [mem_comap]
    by_cases his : i = s
    subst his
    rwa [hphs]
    rw [hph i hi his]
    exact mul_mem_left _ _ hyP
  have horder : ((c + 1) : ENat) ≤ orderAt J pt' := by
    refine le_orderAt_of_ideal_le_pow J hU pt' (c + 1) ?_
    rwa [hpt'q]
  rw [hord _ hz'Z] at horder
  have hcc : c + 1 ≤ c := by exact_mod_cast horder
  omega





section
variable {X X1 : Sch}
section
variable (pi_ : X1 ⟶ X)
theorem restrictIdeal_comap_preimage
    (D : ISD X) (W : Opn X) :
    restrictIdeal (D.comap pi_) (pre pi_ W) = (restrictIdeal D W).comap (pi_.mr W) := by
  rw [restrictIdeal_eq_comap_io, restrictIdeal_eq_comap_io, ← comap_comp,
    ← comap_comp, morphismRestrict_ι]

section
variable (Z : ISD X) (E : Bdy X)
theorem length_strictTransform_append_exceptionalIdeal :
    length (E.map (Blowup.strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z]) = length E + 1 := by
  simp

theorem getElem_strictTransform_append_exceptionalIdeal_of_lt (i : ℕ) (hi : i < length E)
    {h : i < length (E.map (Blowup.strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z])} :
    (E.map (Blowup.strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z])[i]'h
      = Blowup.strictTransform pi_ Z (E[i]'hi) :=by simp_all
theorem getElem_length_strictTransform_append_exceptionalIdeal
    {h : length E < length (E.map (Blowup.strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z])} :
    (E.map (Blowup.strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z])[length E]'h
      = exceptionalIdeal pi_ Z :=by simp_all
end
end

theorem isIso_morphismRestrict_of_isBlowupAlongIdealSheaf {pi_ : X1 ⟶ X}
    {Z : ISD X} (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (W : Opn X)
    (hW : ∀ x : X, x ∈ W → x ∉ support Z) :
    IsIso $ pi_ ∣_ W := by
  have h1 := hpi_.restrict W
  have h2 : Z.comap (p4 W) = ⊤ := by
    refine p39 _ Z fun x => ?_
    show x.1 ∉ support Z
    exact hW x.1 x.2
  rw [h2] at h1
  exact h1.isIso_of_top

section
variable (pi_ : X1 ⟶ X)
section
variable (Z D : ISD X) [QuasiCompact (strictTransformio pi_ Z D)] (V : Opn X1)
theorem restrictIdeal_strictTransform_eq_comap_of_le_compl (hV : V ≤ pre pi_ Z.support.compl) :
    restrictIdeal (Blowup.strictTransform pi_ Z D) V = restrictIdeal (D.comap pi_) V := by
  have := quasiCompact_strictTransformio_comp_io pi_ Z D V
  let _a0 := opI V ≫ pi_
  have hZ : cmI Z _a0 = ⊤ := by
    refine p39 _ Z fun x => ?_
    show bsM pi_ x.1 ∉ spI Z
    exact hV x.2
  rw [restrictIdeal_strictTransform pi_ Z D V, restrictIdeal_eq_comap_io, ← comap_comp]
  refine m29 ?_
  funext W
  exact strictTransform_ideal_eq_comap_of_isUnit _a0 Z D W 1 (by simp [hZ]) isUnit_one

theorem restrictIdeal_strictTransform_eq_comap_of_notMem_support (hV : ∀ x : X1, x ∈ V → pi_.base x ∉ support Z) :
    restrictIdeal (Blowup.strictTransform pi_ Z D) V = restrictIdeal (D.comap pi_) V := by
  refine restrictIdeal_strictTransform_eq_comap_of_le_compl pi_ Z D V ?_
  intro x hx
  exact hV x hx
end

section
variable (Z : ISD X) (V : Opn X1)
theorem restrictIdeal_exceptionalIdeal_eq_top_of_le_compl (hV : V ≤ pre pi_ Z.support.compl) :
    restrictIdeal (exceptionalIdeal pi_ Z) V = ⊤ := by
  rw [restrictIdeal_eq_comap_io, p9, ← m56]
  refine p39 _ Z fun x => ?_
  show bsM pi_ x.1 ∉ spI Z
  exact hV x.2

theorem restrictIdeal_exceptionalIdeal_eq_top_of_notMem_support
    (hV : ∀ x : X1, x ∈ V → pi_.base x ∉ support Z) :
    restrictIdeal (exceptionalIdeal pi_ Z) V = ⊤ := by
  refine restrictIdeal_exceptionalIdeal_eq_top_of_le_compl pi_ Z V ?_
  intro x hx
  exact hV x hx
end
end

section
variable {k : Type} [Field k] [hv1_2 : NoetherianSpace X1] (p : X ⟶ Sp k) (pi_ : X1 ⟶ X) (Z : ISD X)
include hv1_2
section
variable (E : Bdy X) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
include hpi_
theorem inStrictNormalCrossingPositionAt_strictTransform_of_mem_support
    (hZE : HasStrictNormalCrossingsWith p Z E) (x1_ : X1) (hx1_ : pi_.base x1_ ∈ support Z) :
    InStrictNormalCrossingPositionAt (pi_ ≫ p) (E.map (Blowup.strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z]) x1_ := by
  classical
  unfold HasStrictNormalCrossingsWith at hZE
  obtain ⟨U, hxU, m, c, a, S, ha1, ha2, ha3, hZU⟩ := hZE _ hx1_
  obtain ⟨s, hs, hx1B⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZU x1_ hxU
  set B := blowupChartOfIsBlowup pi_ c S hpi_ hZU s hs with hBdef
  have hlen :=
    length_strictTransform_append_exceptionalIdeal pi_ Z E
  unfold InStrictNormalCrossingPositionAt
  refine ⟨B.domain, hx1B, m, B.chart,
    fun i => if i = length E then some s else if a i = some s then none else a i, ?_, ?_, ?_⟩
  intro i hi j hj t hti htj
  have hti' : (if i = length E then some s else if a i = some s then none else a i) = some t :=
    hti
  have htj' : (if j = length E then some s else if a j = some s then none else a j) = some t :=
    htj
  rw [hlen] at hi hj
  by_cases hiE : i = length E
  by_cases hjE : j = length E
  rw [hiE, hjE]
  exfalso
  rw [if_pos hiE] at hti'
  rw [if_neg hjE] at htj'
  have hts := m105 hti'
  by_cases haj : a j = some s
  rw [if_pos haj] at htj'
  simp at htj'
  rw [if_neg haj] at htj'
  exact haj $ by rw [htj', ← hts]
  by_cases hjE : j = length E
  exfalso
  rw [if_pos hjE] at htj'
  rw [if_neg hiE] at hti'
  have hts := m105 htj'
  by_cases hai : a i = some s
  rw [if_pos hai] at hti'
  simp at hti'
  rw [if_neg hai] at hti'
  exact hai $ by rw [hti', ← hts]
  rw [if_neg hiE] at hti'
  rw [if_neg hjE] at htj'
  by_cases hai : a i = some s
  rw [if_pos hai] at hti'
  simp at hti'
  rw [if_neg hai] at hti'
  by_cases haj : a j = some s
  rw [if_pos haj] at htj'
  simp at htj'
  rw [if_neg haj] at htj'
  exact ha1 i (by omega) j (by omega) t hti' htj'
  intro i h hnone
  have hnone' : (if i = length E then some s else if a i = some s then none else a i) = none :=
    hnone
  by_cases hiE : i = length E
  rw [if_pos hiE] at hnone'
  simp at hnone'
  have hi : i < length E := by omega
  rw [getElem_strictTransform_append_exceptionalIdeal_of_lt pi_ Z E i hi]
  rw [if_neg hiE] at hnone'
  by_cases hai : a i = some s
  have hD := ha3 i hi s hai
  simpa using (BlowupChart.restrictIdeal_strictTransform_coordIdeal B Z (E[i]'hi) hs hZU s hD)
  rw [if_neg hai] at hnone'
  exact BlowupChart.restrictIdeal_strictTransform_of_eq_top B Z (E[i]'hi) $ ha2 i hi hnone'
  intro i h t hti
  have hti' : (if i = length E then some s else if a i = some s then none else a i) = some t :=
    hti
  by_cases hiE : i = length E
  subst hiE
  rw [getElem_length_strictTransform_append_exceptionalIdeal pi_ Z E]
  have hts : s = t := by simpa using hti'
  rw [← hts]
  exact BlowupChart.restrictIdeal_exceptionalIdeal B Z hs hZU
  have hi : i < length E := by omega
  rw [getElem_strictTransform_append_exceptionalIdeal_of_lt pi_ Z E i hi]
  rw [if_neg hiE] at hti'
  by_cases hai : a i = some s
  rw [if_pos hai] at hti'
  simp at hti'
  rw [if_neg hai] at hti'
  have hts : t ≠ s := by simp_all
  rw [BlowupChart.restrictIdeal_strictTransform_coordIdeal B Z (E[i]'hi) hs hZU t $ ha3 i hi t hti',
    if_neg hts]

theorem inStrictNormalCrossingPosition_strictTransform_append (hE : InStrictNormalCrossingPosition p E)
    (hZE : HasStrictNormalCrossingsWith p Z E) :
    InStrictNormalCrossingPosition (pi_ ≫ p) $ E.map (Blowup.strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z] := by
  classical
  let _a2 := pi_ ≫ p
  have hat : ∀ x1_,
      InStrictNormalCrossingPositionAt _a2 (E.map (Blowup.strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z]) x1_ := by
    intro x1_
    by_cases hx : bsM pi_ x1_ ∈ spI Z
    exact inStrictNormalCrossingPositionAt_strictTransform_of_mem_support p pi_ Z E hpi_ hZE x1_ hx
    let hx1_ := hx
    classical
    rw [inStrictNormalCrossingPosition_iff] at hE
    obtain ⟨hEdiv, hEpos⟩ := hE
    have hpos := hEpos $ bsM pi_ x1_
    unfold InStrictNormalCrossingPositionAt at hpos
    obtain ⟨U, hxU, m, c, a, ha1, ha2, ha3⟩ := hpos
    have hWU : U ⊓ suppC Z ≤ U := inf_le_left
    let _a1 := pre pi_ $ U ⊓ suppC Z
    have hVle : _a1 ≤ pre pi_ (suppC Z) := fun x hx => hx.2
    let _a0 := c.restrict hWU
    have hcs : ((pi_.mr $ U ⊓ suppC Z) ≫ _a0.map) ≫ affineSpaceFinToSpec k m
        = opI _a1 ≫ _a2 := by
      rw [assoc, _a0.comp_struct, ← assoc, morphismRestrict_ι,
        assoc]
    have het : Etale $ (pi_.mr $ U ⊓ suppC Z) ≫ _a0.map := by
      have := isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hpi_ (U ⊓ suppC Z) fun x hx => hx.2
      have := _a0.isEtale
      infer_instance
    have hlen :=
      length_strictTransform_append_exceptionalIdeal pi_ Z E
    unfold InStrictNormalCrossingPositionAt
    refine ⟨pre pi_ $ U ⊓ suppC Z, ⟨hxU, hx1_⟩, m,
      ⟨(pi_.mr $ U ⊓ suppC Z) ≫ _a0.map, hcs, het⟩,
      fun i => if i = length E then none else a i, ?_, ?_, ?_⟩
    intro i hi j hj t hti htj
    have hti' : (if i = length E then none else a i) = some t := hti
    have htj' : (if j = length E then none else a j) = some t := htj
    rw [hlen] at hi hj
    have hiE : i ≠ length E := by simp_all
    have hjE : j ≠ length E := by simp_all
    rw [if_neg hiE] at hti'
    rw [if_neg hjE] at htj'
    exact ha1 i (by omega) j (by omega) t hti' htj'
    intro i h hnone
    by_cases hiE : i = length E
    subst hiE
    rw [getElem_length_strictTransform_append_exceptionalIdeal pi_ Z E]
    exact restrictIdeal_exceptionalIdeal_eq_top_of_le_compl pi_ Z _ hVle
    have hi : i < length E := by omega
    have hnone' : (if i = length E then none else a i) = none := hnone
    rw [if_neg hiE] at hnone'
    rw [getElem_strictTransform_append_exceptionalIdeal_of_lt pi_ Z E i hi,
      restrictIdeal_strictTransform_eq_comap_of_le_compl pi_ Z (E[i]'hi) _ hVle,
      restrictIdeal_comap_preimage pi_ (E[i]'hi) $ U ⊓ suppC Z,
      restrictIdeal_eq_top_of_le (E[i]'hi) hWU $ ha2 i hi hnone']
    exact comap_top _
    intro i h t hti
    have hti' : (if i = length E then none else a i) = some t := hti
    have hiE : i ≠ length E := by simp_all
    have hi : i < length E := by omega
    rw [if_neg hiE] at hti'
    rw [getElem_strictTransform_append_exceptionalIdeal_of_lt pi_ Z E i hi,
      restrictIdeal_strictTransform_eq_comap_of_le_compl pi_ Z (E[i]'hi) _ hVle,
      restrictIdeal_comap_preimage pi_ (E[i]'hi) $ U ⊓ suppC Z,
      restrictIdeal_eq_restrict_coordIdeal_of_le hWU c (E[i]'hi) {t} $ ha3 i hi t hti']
    simp only [coordIdeal_eq_comap_coordSubspaceIdeal]
    exact sy_ $ comap_comp ..
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, hat⟩
  intro D hD
  obtain ⟨i, hi, rfl⟩ := mp_ mem_iff_getElem hD
  refine isSmoothDivisor_of_locally_coordIdeal _ fun x1_ => ?_
  have hx := hat x1_
  unfold InStrictNormalCrossingPositionAt at hx
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := hx
  refine ⟨U, hxU, m, c, ?_⟩
  cases hai : a i with
  | none => exact Or.inl $ h2 i hi hai
  | some t => exact Or.inr ⟨t, h3 i hi t hai⟩
end

theorem inStrictNormalCrossingPosition_strictTransform_cons_append
    H (E : Bdy X) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
    (hE : InStrictNormalCrossingPosition p (H :: E)) (hZE : HasStrictNormalCrossingsWith p Z (H :: E)) :
    InStrictNormalCrossingPosition (pi_ ≫ p)
      (Blowup.strictTransform pi_ Z H :: (E.map (Blowup.strictTransform pi_ Z) ++ [exceptionalIdeal pi_ Z])) :=
  inStrictNormalCrossingPosition_strictTransform_append p pi_ Z (H :: E) hpi_ hE hZE
end
end




section
variable {Y W : Sch} (g : Y ⟶ W) [IsOpenImmersion g] (y : Y)
theorem ringKrullDim_stalk_eq_of_isOpenImmersion :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (W.presheaf.stalk $ g.base y) := by
  have : IsIso $ g.stalkMap y := inferInstance
  exact sy_ $ ringKrullDim_eq_of_ringEquiv (asIso $ g.stalkMap y).commRingCatIsoToRingEquiv

theorem isNoetherianRing_stalk_of_isOpenImmersion
    [IsNoetherianRing $ W.presheaf.stalk $ g.base y] :
    IsNoetherianRing $ Y.presheaf.stalk y := by
  have : IsIso $ g.stalkMap y := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (CategoryTheory.asIso $ g.stalkMap y).commRingCatIsoToRingEquiv
end

section
variable {k : Type} [Field k]
theorem ringKrullDim_stalk_le_of_etaleChart {Y : Sch}
    (p : Y ⟶ Sp k) [IsLocallyNoetherian Y]
    {U : Opn Y} {m : ℕ} (c : EtaleChart p U m) (y : Y) (hy : y ∈ U) :
    ringKrullDim (Y.presheaf.stalk y) ≤ ((m : ENat) : WithBot ENat) := by
  have := c.isEtale
  let _m0 := (⟨y, hy⟩ : U)
  have hbase : opIb U _m0 = y := rfl
  have h0 : IsNoetherianRing $ stkX Y $ opIb U _m0 := by
    rw [hbase]
    exact inferInstance
  have h1 :=
    isNoetherianRing_stalk_of_isOpenImmersion U.i _m0
  have h2 := ringKrullDim_stalk_le_of_etale_affineSpace c.map _m0
  have h3 := ringKrullDim_stalk_eq_of_isOpenImmersion U.i _m0
  rw [hbase] at h3
  rwa [← h3]

end

theorem withBotSuccToNat_mono_of_lt_top {a b : WithBot ENat} (hab : a ≤ b) (hb : b < ⊤) :
    withBotSuccToNat a ≤ withBotSuccToNat b := by
  revert hab hb
  induction a using WithBot.recBotCoe with
  | bot =>
      intro _ _
      rw [withBotSuccToNat_bot]
      exact zero_le _
  | coe x =>
      induction b using WithBot.recBotCoe with
      | bot =>
          intro hab _
          exact absurd (mp_ le_bot_iff hab) $ by simp
      | coe y =>
          intro hab hb
          have hy : y ≠ ⊤ := fun h => hb.ne $ by simp [h]
          obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hy
          have hxy := WithBot.coe_le_coe.mp hab
          have hx : x ≠ ⊤ := by
            intro h
            rw [h, top_le_iff] at hxy
            exact absurd hxy $ by simp
          obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hx
          have hmn : m ≤ n := by exact_mod_cast hxy
          rw [withBotSuccToNat_coe, withBotSuccToNat_coe]
          have h1 : (m : ENat).toNat = m := by simp
          have h2 : (n : ENat).toNat = n := by simp
          omega

section
variable {k : Type} [Field k] {X X1 : Sch} (p : X ⟶ Sp k) [LocallyOfFiniteType p]
theorem topologicalKrullDim_le_of_blowup_strictNormalCrossings
    (pi_ : X1 ⟶ X) (Z : ISD X) (E : Bdy X)
    (hZE : HasStrictNormalCrossingsWith p Z E) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) :
    topologicalKrullDim ↥X1 ≤ topologicalKrullDim ↥X := by
  have hXN :=
    isLocallyNoetherian p
  have hX1N :=
    isLocallyNoetherian_of_isBlowupAlongIdealSheaf pi_ Z hpi_
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le X1 _ ?_
  intro x1_
  by_cases hx : bsM pi_ x1_ ∈ spI Z
  obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := hZE.exists_etaleChart hx
  obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ h4 x1_ hU
  have hle := ringKrullDim_stalk_le_of_etaleChart (pi_ ≫ p)
    (blowupChartOfIsBlowup pi_ c S hpi_ h4 s hs).chart x1_ hmem
  have _i48 : ((m : ENat) : WithBot ENat) ≤ topologicalKrullDim X := by
    let hU : (U : Set X).Nonempty := ⟨bsM pi_ x1_, hU⟩
    have := c.isEtale
    have :=
      isLocallyNoetherian p
    obtain ⟨x0, hx0⟩ := hU
    obtain ⟨V, hVaff, hxv, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := oSch U) (x := ⟨x0, hx0⟩) (U := ⊤) trivial
    obtain ⟨y, hy⟩ := exists_isClosed_singleton_of_isAffineOpen V hVaff ⟨_, hxv⟩
    have he1 : Etale $ p4 V := inferInstance
    let _a1 := opI V ≫ c.map
    have he2 : Etale _a1 := inferInstance
    let _a0 := opI V ≫ opI U
    let _m0 := bsM _a0 y
    have : IsNoetherianRing $ stkX X _m0 := inferInstance
    have :=
      isNoetherianRing_stalk_of_isOpenImmersion _a0 y
    calc (m : WithBot ENat)
        = ringKrullDim (V.toScheme.presheaf.stalk y) :=
          symm $ ringKrullDim_stalk_eq_of_etale_affineSpace _a1 y hy
      _ = ringKrullDim (stkX X _m0) :=
          ringKrullDim_stalk_eq_of_isOpenImmersion _a0 y
      _ ≤ topologicalKrullDim X :=
          ringKrullDim_stalk_le_topologicalKrullDim X _m0
  exact hle.trans _i48
  have _i49 : ringKrullDim (stkX X1 x1_) = ringKrullDim (stkX X $ bsM pi_ x1_) := by
    obtain ⟨W, hWeq⟩ : ∃ W : Opn X, (W : Set X) = (spI Z : Set X)ᶜ :=
      ⟨⟨(spI Z : Set X)ᶜ, Z.support.2.isOpen_compl⟩, rfl⟩
    have hW : ∀ x : X, x ∈ W → x ∉ spI Z := by
      intro x hxm
      have h2 : x ∈ (W : Set X) := hxm
      rwa [hWeq] at h2
    have hxW : bsM pi_ x1_ ∈ W := by
      have h2 : bsM pi_ x1_ ∈ (spI Z : Set X)ᶜ := hx
      rwa [← hWeq] at h2
    have hx : x1_ ∈ preU pi_ W := hxW
    have hiso := isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hpi_ W hW
    have hoi : IsOpenImmersion $ mrU pi_ W := inferInstance
    have e1 := ringKrullDim_stalk_eq_of_isOpenImmersion (p4 $ preU pi_ W)
      (⟨x1_, hx⟩ : (preU pi_ W))
    have e2 := ringKrullDim_stalk_eq_of_isOpenImmersion ((mrU pi_ W) ≫ p4 W)
      (⟨x1_, hx⟩ : (preU pi_ W))
    rw [morphismRestrict_ι] at e2
    exact st_ e1 e2
  rw [_i49]
  exact ringKrullDim_stalk_le_topologicalKrullDim X $ bsM pi_ x1_

theorem krullDimSucc_le_of_blowup_strictNormalCrossings
    [QuasiCompact p]
    (pi_ : X1 ⟶ X) (Z : ISD X) (E : Bdy X)
    (hZE : HasStrictNormalCrossingsWith p Z E) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) :
    krullDimSucc X1 ≤ krullDimSucc X := by
  simp [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  exact withBotSuccToNat_mono_of_lt_top (topologicalKrullDim_le_of_blowup_strictNormalCrossings p pi_ Z E hZE hpi_) $ topologicalKrullDim_lt_top_of_finiteType p inferInstance inferInstance
end

end FunctorialResolution.EmbeddedResolution
end
section
open Opposite TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable (m : ℕ) (S : FinSet m) (a : Fin m)
def complEmbPreimage :
    Finset $ Fin $ m - ({a} : FinSet m).card :=
  filter (fun i => complOrderEmb m {a} i ∈ S) univ

theorem mem_complEmbPreimage
    i :
    i ∈ complEmbPreimage m S a ↔ complOrderEmb m {a} i ∈ S := by
  simp [complEmbPreimage]

theorem mem_complEmbPreimage_of_complOrderEmb_eq
    {s : Fin m} (hs : s ∈ S) {i : Fin $ m - ({a} : FinSet m).card}
    (hi : complOrderEmb m {a} i = s) : i ∈ complEmbPreimage m S a := by
  rwa [mem_complEmbPreimage, hi]
end

variable {X X1 : Sch} {k : Type} [Field k]
  {p : X ⟶ Sp k} {pi_ : X1 ⟶ X} {U : Opn X} {m : ℕ}
  {c : EtaleChart p U m} {S : FinSet m} {s : Fin m}

section
variable (B : BlowupChart pi_ c S s)
section
variable (V : Opn X1) (hV : V ≤ B.domain)
def BlowupChart.restrict :
    BlowupChart pi_ c S s where
  domain := V
  domain_le := hV.trans B.domain_le
  chart := B.chart.restrict hV
  comm := by
    have key : X1.homOfLE hV ≫ pi_.resLE U B.domain B.domain_le
        = pi_.resLE U V (hV.trans B.domain_le) := by simp_all
    rw [restrict_map, assoc, B.comm, ← assoc, key]

@[simp] theorem BlowupChart.restrict_domain : (B.restrict V hV).domain = V := rfl
end

theorem restrictToSubscheme_map_comp_affineSpaceFinToSpec
    (hB : IsAffineOpen B.domain) (Z H : ISD X)
    [QuasiCompact $ strictTransformio pi_ Z H]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    a (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    q
    (hq : q ≫ subschemeι H = subschemeι (Blowup.strictTransform pi_ Z H) ≫ pi_) :
    (B.chart.restrictToSubscheme hB (Blowup.strictTransform pi_ Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map ≫
          affineSpaceFinToSpec k (m - ({a} : FinSet m).card) =
      ι (subschemeι (Blowup.strictTransform pi_ Z H) ⁻¹ᵁ B.domain) ≫ (q ≫ (subschemeι H ≫ p)) := by
  let _a0 := p6 pi_ Z H
  have h := (B.chart.restrictToSubscheme hB _a0 {a}
    (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).comp_struct
  rw [h, ← assoc _a0.si pi_ p, ← hq, assoc]

theorem BlowupChart.strictTransform_subschemeio_preimage_domain_eq_bot
    (Z H : ISD X) [QuasiCompact $ strictTransformio pi_ Z H]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hH : restrictIdeal H U = c.coordIdeal {s}) :
    subschemeι (Blowup.strictTransform pi_ Z H) ⁻¹ᵁ B.domain = ⊥ := by
  let _c0 := p6 pi_ Z H
  rw [eq_bot_iff]
  intro y hy
  have hxB : _c0.subschemeι.base y ∈ B.domain := hy
  have hxsupp : _c0.subschemeι.base y ∈ support _c0 := by
    have hr : _c0.subschemeι.base y ∈
        range _c0.subschemeι.base := mem_range_self y
    rwa [q5] at hr
  have h1 : (⟨_, hxB⟩ : ↥B.domain) ∈ support (_c0.comap B.domain.i) := by
    rwa [m19]
  rw [← restrictIdeal_eq_comap_io, B.restrictIdeal_strictTransform_coordIdeal_self Z H hs hZ hH, Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨_, hxB⟩ : ↥B.domain) ∈ ((⊥) : Set ↥B.domain) :=
    h1
  simp at h2

theorem strictTransform_preimage_domain_le_preimage
    (Z H : ISD X)
    q
    (hq : q ≫ subschemeι H = subschemeι (Blowup.strictTransform pi_ Z H) ≫ pi_) :
    subschemeι (Blowup.strictTransform pi_ Z H) ⁻¹ᵁ B.domain ≤ q ⁻¹ᵁ (subschemeι H ⁻¹ᵁ U) := by
  intro y hy
  have h2 : bsM (siI (p6 pi_ Z H) ≫ pi_) y ∈ U := B.domain_le hy
  rwa [← hq] at h2

theorem BlowupChart.exists_isAffineOpen_mem_le_domain (x : X1)
    (hx : x ∈ B.domain) :
    ∃ V : Opn X1, V ≤ B.domain ∧ IsAffineOpen V ∧ x ∈ V := by
  obtain ⟨V, hV, hxV, hVU⟩ :=
    isBasis_iff_nbhd.mp X1.isBasis_affineOpens hx
  exact ⟨V, hVU, hV, hxV⟩
end

section
variable {Y : Sch}
theorem opensio_appLE_top_eq_topIso_inv (V : Opn Y) :
    V.ι.appLE V ⊤ (ι_preimage_self V).ge = V.topIso.inv := by
  simp
  rfl

section
variable {K : Type} [Field K] {p' : Y ⟶ Sp K} {V : Opn Y} {n : ℕ}
theorem coordIdeal_ideal_top_eq_map [IsAffine V.toScheme]
    (d : EtaleChart p' V n) T :
    (d.coordIdeal T).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩ =
      Ideal.map V.topIso.inv.hom (span $ d.coord '' (T : Set $ Fin n)) := by
  rw [coordIdeal_eq_comap_coordSubspaceIdeal, comap_ideal_top_eq_map_appTop,
    coordSubspaceIdeal_eq_ofIdealTop_span_coord, ofIdealTop_ideal_top, map_span,
    map_span, ← image_comp, ← image_comp]
  exact congrArg span $ image_congr fun j _ => sy_ $ CommRingCat.inv_hom_apply V.topIso _

theorem etaleChart_map_appTop_coord (d : EtaleChart p' V n)
    j :
    (appTop d.map).hom (AffineSpace.coord (Sp K) $ up j)
      = V.topIso.inv.hom (d.coord j) := by
  rw [coord_def]
  exact sy_ $ CommRingCat.inv_hom_apply V.topIso _
end

theorem comap_opensio_ideal_top_eq_map (J : ISD Y)
    {V : Opn Y} (hV : IsAffineOpen V) [IsAffine V.toScheme] :
    (J.comap V.i).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
      = Ideal.map V.topIso.inv.hom (J.ideal ⟨V, hV⟩) := by
  rw [← opensio_appLE_top_eq_topIso_inv V]
  exact comap_ideal_eq_map_appLE J V.i ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ (ι_preimage_self V).ge
end

theorem restrictIdeal_comap_subschemeio_eq_coordIdeal (c : EtaleChart p U m)
    (hU : IsAffineOpen U) (Z H : ISD X) (S : FinSet m) (a : Fin m)
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hH : restrictIdeal H U = c.coordIdeal {a}) :
    restrictIdeal (Z.comap H.si) (H.si ⁻¹ᵁ U) =
      (c.restrictToSubscheme hU H {a} hH).coordIdeal (complEmbPreimage m S a) := by
  classical
  have hW := isAffineOpen_preimage_subschemeio H hU
  let _s0 := siPre H U
  have : IsAffine _s0.toScheme := hW
  have hmem : c.coord a ∈ H.ideal ⟨U, hU⟩ := by
    rw [c.ideal_eq_span_coord hU H {a} hH]
    exact subset_span ⟨a, by simp, rfl⟩
  have hpha : (H.subschemeι.appLE U _s0 le_rfl).hom (c.coord a) = 0 := by
    have hval := congrArg (fun f => (m4 f) $ c.coord a) $ subschemeι_app H ⟨U, hU⟩
    simp [hom_comp, comp_apply] at hval
    rw [appLE_eq_app, hval,
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  have hspan : span
        ((H.subschemeι.appLE U _s0 le_rfl).hom ''
          (c.coord '' (S : Set $ Fin m)))
      = span ((c.restrictToSubscheme hU H {a} hH).coord ''
          ((complEmbPreimage m S a : Finset $ Fin $ m - ({a} : FinSet m).card) :
            Set $ Fin $ m - ({a} : FinSet m).card)) := by
    apply le_antisymm
    rw [span_le]
    rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    by_cases hja : j = a
    subst hja
    rw [hpha]
    exact m216 _
    have hjnot : j ∉ ({a} : FinSet m) := by simpa using hja
    obtain ⟨i, hi⟩ := exists_complOrderEmb_eq m ({a} : FinSet m) hjnot
    refine subset_span ⟨i, Finset.mem_coe.mpr $ mem_complEmbPreimage_of_complOrderEmb_eq m S a (Finset.mem_coe.mp hj) hi, ?_⟩
    rw [c.restrictToSubscheme_coord hU H {a} hH i, hi]
    rw [span_le]
    rintro x ⟨i, hi, rfl⟩
    rw [c.restrictToSubscheme_coord hU H {a} hH i]
    exact subset_span ⟨c.coord $ complOrderEmb m {a} i,
      ⟨complOrderEmb m {a} i, Finset.mem_coe.mpr $ (mem_complEmbPreimage m S a i).mp
        (Finset.mem_coe.mp hi), rfl⟩, rfl⟩
  have hideal : (restrictIdeal (cmI Z H.si) _s0).ideal
        ⟨⊤, isAffineOpen_top _s0.toScheme⟩
      = ((c.restrictToSubscheme hU H {a} hH).coordIdeal $ complEmbPreimage m S a).ideal
        ⟨⊤, isAffineOpen_top _s0.toScheme⟩ := by
    rw [restrictIdeal_eq_comap_io, comap_opensio_ideal_top_eq_map (cmI Z H.si) hW,
      coordIdeal_ideal_top_eq_map,
      comap_ideal_eq_map_appLE Z H.si ⟨U, hU⟩
        ⟨siPre H U, hW⟩ le_rfl,
      c.ideal_eq_span_coord hU Z S hZ, map_span, hspan]
  exact (equivOfIsAffine
    (X := oSch _s0)).injective hideal

private theorem appLE_top_top_eq_appTop {A B : Sch} (f : A ⟶ B)
    e :
    appLE f (⊤ : Opn B) (⊤ : Opn A) e = appTop f := by
  let _a0 := pMap A (homOfLE e).op
  have h1 : _a0 = 𝟙 Γ(A, ⊤) := A.presheaf.map_id $ op (⊤)
  calc f.appLE (⊤) (⊤) e
      = f.app (⊤) ≫ _a0 := rfl
    _ = f.app (⊤) ≫ 𝟙 Γ(A, ⊤) := by rw [h1]
    _ = appTop f := comp_id _

section
variable (B : BlowupChart pi_ c S s) (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain) (Z H : ISD X) [QuasiCompact (strictTransformio pi_ Z H)] (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S) (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a}) (s' : Fin (m - ({a} : FinSet m).card)) (hs' : complOrderEmb m {a} s' = s) (q : subscheme (Blowup.strictTransform pi_ Z H) ⟶ subscheme H) (hq : q ≫ subschemeι H = subschemeι (Blowup.strictTransform pi_ Z H) ≫ pi_)
def BlowupChart.restrictToStrictTransform :
    BlowupChart q (c.restrictToSubscheme hU H {a} hH) (complEmbPreimage m S a) s' where
  domain := (Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain
  domain_le := strictTransform_preimage_domain_le_preimage B Z H q hq
  chart :=
    { map := (B.chart.restrictToSubscheme hB (Blowup.strictTransform pi_ Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map
      comp_struct :=
        restrictToSubscheme_map_comp_affineSpaceFinToSpec B hB Z H hs hZ a ha has hH q hq
      isEtale := (B.chart.restrictToSubscheme hB (Blowup.strictTransform pi_ Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).isEtale }
  comm :=
    by
    classical
    have hle := strictTransform_preimage_domain_le_preimage B Z H q hq
    have hr : q.resLE (H.si ⁻¹ᵁ U)
          ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle ≫ (H.subschemeι ⁻¹ᵁ U).i
        = ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain).ι ≫ q := by
      rw [resLE_comp_ι]
    refine AffineSpace.hom_ext ?_ ?_
    · rw [assoc, assoc, coordBlowupSubstMap_comp_affineSpaceFinToSpec,
        restrictToSubscheme_map_comp_affineSpaceFinToSpec B hB Z H hs hZ a ha has hH q hq,
        (c.restrictToSubscheme hU H {a} hH).comp_struct]
      simp only [← assoc]
      rw [hr]
    · rintro ⟨i0_⟩
      have hL : ∀ j : Fin (m - ({a} : FinSet m).card),
          (appTop (B.chart.restrictToSubscheme hB (Blowup.strictTransform pi_ Z H) {a}
              (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map).hom
              (AffineSpace.coord (Sp k) (up j))
            = ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain).topIso.inv.hom
                (((Blowup.strictTransform pi_ Z H).subschemeι.appLE B.domain
                  ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) le_rfl).hom
                  (B.chart.coord (complOrderEmb m {a} j))) := by
        intro j
        rw [etaleChart_map_appTop_coord, restrictToSubscheme_coord]
      have hM : ∀ j : Fin (m - ({a} : FinSet m).card),
          (appTop (c.restrictToSubscheme hU H {a} hH).map).hom
              (AffineSpace.coord (Sp k) (up j))
            = (H.si ⁻¹ᵁ U).topIso.inv.hom
                ((H.subschemeι.appLE U (H.si ⁻¹ᵁ U) le_rfl).hom
                  (c.coord (complOrderEmb m {a} j))) := by
        intro j
        rw [etaleChart_map_appTop_coord, restrictToSubscheme_coord]
      have hkey : H.subschemeι.appLE U (H.si ⁻¹ᵁ U) le_rfl
            ≫ appLE q (H.si ⁻¹ᵁ U)
                ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle
          = appLE pi_ U B.domain B.domain_le
            ≫ (Blowup.strictTransform pi_ Z H).subschemeι.appLE B.domain
                ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) le_rfl := by
        rw [Scheme.Hom.appLE_comp_appLE q H.subschemeι U (H.subschemeι ⁻¹ᵁ U)
            ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) le_rfl hle,
          Scheme.Hom.appLE_comp_appLE (Blowup.strictTransform pi_ Z H).si pi_ U B.domain
            ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) B.domain_le le_rfl]
        exact appLE_congr_hom hq _ _ _ _
      have hkeyfun : ∀ x : (X.sec U),
          (appLE q (H.si ⁻¹ᵁ U)
              ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle).hom
            ((H.subschemeι.appLE U (H.si ⁻¹ᵁ U) le_rfl).hom x)
          = ((Blowup.strictTransform pi_ Z H).subschemeι.appLE B.domain
              ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) le_rfl).hom
            ((appLE pi_ U B.domain B.domain_le).hom x) := by
        intro x
        have h := congrArg (fun f => (CommRingCat.Hom.hom f) x) hkey
        simp only [hom_comp, comp_apply] at h
        exact h
      have e2 : (⊤ : ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain).toScheme.Opens)
          ≤ (q.resLE (H.si ⁻¹ᵁ U)
              ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle)
              ⁻¹ᵁ (⊤ : (H.si ⁻¹ᵁ U).toScheme.Opens) := by simp
      have hres : (H.si ⁻¹ᵁ U).topIso.inv ≫
            appTop (q.resLE (H.si ⁻¹ᵁ U)
              ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle)
          = appLE q (H.si ⁻¹ᵁ U)
              ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle
            ≫ ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain).topIso.inv := by
        rw [← opensio_appLE_top_eq_topIso_inv (H.subschemeι ⁻¹ᵁ U),
          ← appLE_top_top_eq_appTop (q.resLE (H.si ⁻¹ᵁ U)
            ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle) e2,
          Scheme.Hom.appLE_comp_appLE (q.resLE (H.si ⁻¹ᵁ U)
              ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle)
            (H.subschemeι ⁻¹ᵁ U).i (H.si ⁻¹ᵁ U) ⊤ ⊤ (ι_preimage_self _).ge e2,
          ← opensio_appLE_top_eq_topIso_inv
            ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain),
          Scheme.Hom.appLE_comp_appLE
            ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain).ι q (H.si ⁻¹ᵁ U)
            ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) ⊤ hle
            (ι_preimage_self _).ge]
        exact appLE_congr_hom hr _ _ _ _
      have hstar : ∀ y : Γ(H.subscheme, H.si ⁻¹ᵁ U),
          (appTop (q.resLE (H.si ⁻¹ᵁ U)
              ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle)).hom
            ((H.si ⁻¹ᵁ U).topIso.inv.hom y)
          = ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain).topIso.inv.hom
              ((appLE q (H.si ⁻¹ᵁ U)
                ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) hle).hom y) := by
        intro y
        have h := congrArg (fun f => (CommRingCat.Hom.hom f) y) hres
        simp only [hom_comp, comp_apply] at h
        exact h
      have hcond : (complOrderEmb m {a} i0_ ∈ S ∧ complOrderEmb m {a} i0_ ≠ s)
          ↔ (i0_ ∈ complEmbPreimage m S a ∧ i0_ ≠ s') := by
        rw [mem_complEmbPreimage]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun hh => h2 (by rw [hh, hs'])⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun hh => h2 ((complOrderEmb m {a}).injective (by rw [hh, hs']))⟩
      rw [comp_appTop, comp_appTop]
      simp only [hom_comp, comp_apply]
      rw [coordBlowupSubstMap_appTop_coord, hM i0_, hstar, hkeyfun,
        BlowupChart.appLE_coord B (complOrderEmb m {a} i0_)]
      by_cases hP : complOrderEmb m {a} i0_ ∈ S ∧ complOrderEmb m {a} i0_ ≠ s
      · rw [if_pos hP, if_pos (hcond.mp hP)]
        simp only [map_mul]
        rw [hL i0_, hL s', hs']
      · rw [if_neg hP, if_neg fun hh => hP (hcond.mpr hh)]
        exact hL i0_


theorem BlowupChart.restrictToStrictTransform_chart_map :
    (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s' hs' q hq).chart.map =
      (B.chart.restrictToSubscheme hB (Blowup.strictTransform pi_ Z H) {a}
        (B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH)).map := rfl
end

end FunctorialResolution.EmbeddedResolution

end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

section
variable {A : Type} [CommRing A] (J : Ideal A)
noncomputable def saturationByPowers (a : A) : Ideal A :=
  _root_.UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers J a

theorem mem_saturationByPowers_iff a x :
    x ∈ saturationByPowers J a ↔ ∃ n, a ^ n * x ∈ J := m22
end

section
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
theorem map_saturationByPowers_le
    (J : Ideal A) a :
    (saturationByPowers J a).map (algebraMap A B) ≤
      saturationByPowers (J.map $ algebraMap A B) (algebraMap A B a) := by
  rw [map_le_iff_le_comap]
  rintro x ⟨n, hn⟩
  rw [mem_comap, mem_saturationByPowers_iff]
  refine ⟨n, ?_⟩
  have h := mem_map_of_mem (algebraMap A B) hn
  rwa [map_mul, map_pow] at h

theorem map_saturationByPowers_of_flat
    [Module.Flat A B] (J : Ideal A) a :
    (saturationByPowers J a).map (algebraMap A B) =
      saturationByPowers (J.map $ algebraMap A B) (algebraMap A B a) := by
  let _a3 := algebraMap A B
  refine le_antisymm (map_saturationByPowers_le J a) ?_
  rintro y ⟨n, hy⟩
  obtain ⟨u, hu⟩ : ∃ u : A →ₗ[A] (A ⧸ J), u = J.mkQ ∘ₗ lsmul A A (a ^ n) := ⟨_, rfl⟩
  have hker : ∀ c, u c = 0 ↔ a ^ n * c ∈ J := by
    intro c
    rw [hu, LinearMap.comp_apply, lsmul_apply, mkQ_apply, smul_eq_mul,
      Submodule.Quotient.mk_eq_zero]
  have hex : Exact (m177 u).subtype u := by
    intro c
    constructor
    simp_all
    simp_all
  have key : lTensor B u (y ⊗ₜ[A] 1) = 0 := by
    have hmapJ : (Ideal.map _a3 J)
        = span (_a3 '' J) := rfl
    rw [hmapJ] at hy
    obtain ⟨k, cf, gg, hsum⟩ := mem_span_set'.1 hy
    have hgg : ∀ i, ∃ c, c ∈ J ∧ algebraMap A B c = (gg i) := by
      intro i
      obtain ⟨c, hc1, hc2⟩ := (gg i).2
      exact ⟨c, hc1, hc2⟩
    choose c hcJ hcmap using hgg
    have e1 : lTensor B u (y ⊗ₜ[A] 1) = y ⊗ₜ[A] (J.mkQ $ a ^ n) := by
      rw [lTensor_tmul, hu]
      simp
    have e2 : (J.mkQ (a ^ n) : A ⧸ J) = (a ^ n) • (J.mkQ 1) := by
      rw [← map_smul]
      simp
    have e3 : algebraMap A B (a ^ n) * y = ∑ i, c i • cf i := by
      rw [map_pow, ← hsum]
      refine sum_congr rfl fun i _ => ?_
      rw [← hcmap i, smul_eq_mul, smul_def]
      ring
    rw [e1, e2, ← smul_tmul, smul_def, e3, sum_tmul]
    refine sum_eq_zero fun i _ => ?_
    rw [smul_tmul]
    have hz : (c i) • (J.mkQ 1) = 0 := by
      have hz1 : (c i) • (J.mkQ 1) = J.mkQ (c i) := by
        rw [← map_smul, smul_eq_mul, mul_one]
      rw [hz1, mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hcJ i
    rw [hz, tmul_zero]
  obtain ⟨w, hw⟩ := ((Module.Flat.lTensor_exact B hex) $ y ⊗ₜ[A] 1).1 key
  have main : ∀ z : TensorProduct A B $ m177 u,
      rid A B (lTensor B (m177 u).subtype z) ∈
        (saturationByPowers J a).map _a3 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b cc =>
        have hcc : (cc : A) ∈ saturationByPowers J a := ⟨n, (hker _).1 cc.2⟩
        simpa [smul_def] using (mul_mem_right b _ $ mem_map_of_mem _a3 hcc)
    | add z1_ z2_ h1_ h2_ =>
        rw [map_add, map_add]
        exact m128 _ h1_ h2_
  have hy2 : y = rid A B (lTensor B (m177 u).subtype w) := by
    rw [hw]
    simp
  rw [hy2]
  exact main w

theorem exists_pow_mul_mem_of_mem_map_away (f : A) [IsLocalization.Away f B] (I : Ideal A) (x : A)
    (hx : algebraMap A B x ∈ I.map (algebraMap A B)) : ∃ n : ℕ, f ^ n * x ∈ I := by
  rw [mem_map_algebraMap_iff (powers f) B] at hx
  obtain ⟨⟨i, m⟩, hxe⟩ := hx
  obtain ⟨p, hp⟩ := m.2
  let _a0 := m
  have hp' : f ^ p = _a0 := hp
  have h2 : algebraMap A B (x * _a0) = algebraMap A B i := by simp_all
  obtain ⟨cc, hcc⟩ := (eq_iff_exists (powers f) B).1 h2
  obtain ⟨q, hq⟩ := cc.2
  have hq' : f ^ q = cc := hq
  refine ⟨q + p, ?_⟩
  have h3 : f ^ (q + p) * x = cc * (x * _a0) := by
    rw [pow_add, hp', hq']
    ring
  rw [h3, hcc]
  exact I.mul_mem_left _ i.2
end

section
variable {X : Sch}
private theorem span_eq_top_of_basicOpen_cover (U : Opn X)
    (hU : IsAffineOpen U) (s : Set $ X.sec U)
    (hcov : ∀ y : X, y ∈ U → ∃ f ∈ s, y ∈ X.basicOpen f) :
    span s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hsm⟩ := exists_le_maximal _ hne
  have hmp := hm.isPrime
  let _a0 := bsM (fromSpec hU) ⟨m, hmp⟩
  have hy : _a0 ∈ U := by
    have hr : _a0 ∈
        range (fromSpec hU).base := mem_range_self _
    rwa [range_fromSpec] at hr
  obtain ⟨f, hfs, hf⟩ := hcov _ hy
  have h1 : (⟨m, hmp⟩ : PrimeSpectrum $ xSec X U) ∈
      (fromSpec hU) ⁻¹ᵁ bOpn X f := hf
  rw [fromSpec_preimage_basicOpen hU f] at h1
  exact ((m209 f _).1 h1) $ hsm $ subset_span hfs

theorem ideal_eq_of_ideal_basicOpen_eq_of_span_eq_top (I J : ISD X)
    (U : X.affineOpens) (s : Set Γ(X, U.1)) (hs : span s = ⊤)
    (h : ∀ f ∈ s, I.ideal (X.affineBasicOpen f) = J.ideal (X.affineBasicOpen f)) :
    I.ideal U = J.ideal U := by
  have key : ∀ P Q : ISD X,
      (∀ f ∈ s, P.ideal (X.affineBasicOpen f) = Q.ideal (X.affineBasicOpen f)) →
      P.ideal U ≤ Q.ideal U := by
    intro P Q hPQ x hx
    refine mem_of_span_eq_top_of_smul_pow_mem _ s hs x ?_
    rintro ⟨f, hf⟩
    let _m0 := m4 $ pMap X (homOfLE $ X.basicOpen_le f).op
    have h1 : _m0 x ∈
        Ideal.map _m0
          (Q.ideal U) := by
      rw [Q.2 U f, ← hPQ f hf, ← P.2 U f]
      exact mem_map_of_mem _ hx
    obtain ⟨m, hm⟩ := by
      let I := Q.ideal U
      have := U.2.isLocalization_basicOpen f
      exact exists_pow_mul_mem_of_mem_map_away (A := Γ(X, U.1)) (B := Γ(X, bOpn X f)) f I x h1
    exact ⟨m, by simpa [smul_eq_mul] using hm⟩
  exact le_antisymm (key I J h) $ key J I fun f hf => sy_ $ h f hf
end

theorem comap_saturation_of_flat {Y Y' : Sch} (g : Y' ⟶ Y)
    [Flat g] (F T : ISD Y) (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F)
    [QuasiCompact $ saturationio F T]
    [QuasiCompact $ saturationio (F.comap g) $ T.comap g] :
    (saturation F T).comap g = saturation (F.comap g) (T.comap g) := by
  classical
  refine m29 $ funext fun V => ?_
  refine ideal_eq_of_ideal_basicOpen_eq_of_span_eq_top _ _ V
    {f : Γ(Y', V.1) | ∃ (U : affO Y) (t : Γ(Y, U.1)), F.ideal U = span {t} ∧
      bOpn Y' f ≤ (m54 g.base).obj U.1} ?_ ?_
  refine span_eq_top_of_basicOpen_cover V.1 V.2 _ ?_
  intro y hy
  obtain ⟨U, t, hUmem, -, ht⟩ := hF $ bsM g y
  obtain ⟨f, hf1, hf2⟩ := exists_basicOpen_le V.2
    (⟨y, ⟨hy, hUmem⟩⟩ : (V.1 ⊓ (m54 g.base).obj U.1 : Opn Y')) hy
  exact ⟨f, ⟨U, t, ht, le_trans hf1 inf_le_right⟩, hf2⟩
  rintro f ⟨U, t, ht, hle⟩
  let V := Y'.affineBasicOpen f
  let e := hle
  let _a2 := m4 $ appLE g U.1 V.1 e
  let _ := _a2.toAlgebra
  have halg : algebraMap Γ(Y, U.1) Γ(Y', V.1) = _a2 := rfl
  have : Module.Flat Γ(Y, U.1) Γ(Y', V.1) :=
    (inferInstance : Flat g).1 U.2 V.2 e
  let _a3 := (saturation F T).ideal U
  have h1 : (cmI (saturation F T) g).ideal V
      = m6 (algebraMap Γ(Y, U.1) Γ(Y', V.1)) _a3 := by
    rw [halg]
    exact comap_ideal_eq_map_appLE _ g U V e
  let _a4 := (cmI T g).ideal V
  have h3 : _a4
      = m6 (algebraMap Γ(Y, U.1) Γ(Y', V.1)) (T.ideal U) := by
    rw [halg]
    exact comap_ideal_eq_map_appLE _ g U V e
  have h2 : _a3 = saturationByPowers (T.ideal U) t := by
    ext w
    rw [mem_saturationByPowers_iff]
    exact mem_saturation_ideal_iff F T U t ht w
  have h4 : (cmI F g).ideal V = span {algebraMap Γ(Y, U.1) Γ(Y', V.1) t} := by
    rw [halg]
    simpa using (comap_ideal_eq_span_image F g U V e {t} ht)
  have h5 : (saturation (cmI F g) $ cmI T g).ideal V
      = saturationByPowers _a4 (algebraMap Γ(Y, U.1) Γ(Y', V.1) t) := by
    ext w
    rw [mem_saturationByPowers_iff]
    exact mem_saturation_ideal_iff (cmI F g) (cmI T g) V _ h4 w
  rw [h1, h2, h5, h3]
  exact map_saturationByPowers_of_flat (T.ideal U) t

section
variable {X X1 X' X1' : Sch} (pi_ : X1 ⟶ X) (g : X' ⟶ X) (pi' : X1' ⟶ X') (g1_ : X1' ⟶ X1) [Flat g]
theorem comap_strictTransform_of_flat_of_isLocallyNoetherian [IsLocallyNoetherian X1] [IsLocallyNoetherian X1']
    (hsq : IsPullback g1_ pi' pi_ g)
    (Z D : ISD X) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) :
    (Blowup.strictTransform pi_ Z D).comap g1_ = Blowup.strictTransform pi' (Z.comap g) (D.comap g) := by
  have hZ : (Z.comap pi_).comap g1_ = (Z.comap g).comap pi' := by
    rw [← comap_comp, hsq.w, comap_comp]
  have hD : (D.comap pi_).comap g1_ = (D.comap g).comap pi' := by
    rw [← comap_comp, hsq.w, comap_comp]
  have : Flat g1_ :=
    m122 (P := @Flat)
      hsq.flip inferInstance
  have i1 : QuasiCompact $ saturationio (cmI Z pi_) $ cmI D pi_ :=
    inferInstanceAs $ QuasiCompact $ strictTransformio pi_ Z D
  have i2 : QuasiCompact $ saturationio ((Z.comap pi_).comap g1_) $ (D.comap pi_).comap g1_ := by
    rw [hZ, hD]
    exact inferInstanceAs $ QuasiCompact $ strictTransformio pi' (cmI Z g) $ cmI D g
  simp [strictTransform_eq_saturation]
  rw [comap_saturation_of_flat g1_ (Z.comap pi_) (D.comap pi_) hpi_.1, hZ, hD]
end

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

theorem surjective_hom_iso_inv {A B : CRC} (e : A ≅ B) :
    Surjective $ CommRingCat.Hom.hom e.inv := by
  intro a
  refine ⟨m4 e.hom a, ?_⟩
  simp

section
variable {Y : Sch}
section
variable (I : ISD Y) (U : Y.affineOpens)
theorem surjective_subschemeio_app :
    Surjective $ CommRingCat.Hom.hom $ I.subschemeι.app (U : Opn Y) := by
  rw [subschemeι_app, hom_comp, hom_ofHom,
    coe_comp]
  exact (surjective_hom_iso_inv $ I.subschemeObjIso U).comp mk_surjective

theorem appLE_subschemeio_apply_eq_zero_of_mem (V : I.subscheme.Opens)
    (e : V ≤ (Opens.map I.subschemeι.base).obj (U : Opn Y))
    {t : ↑(Y.presheaf.obj $ Opposite.op (U : Opn Y))} (ht : t ∈ I.ideal U) :
    (CommRingCat.Hom.hom $ I.subschemeι.appLE (U : Opn Y) V e) t = 0 := by
  have happ : (CommRingCat.Hom.hom $ I.subschemeι.app U) t = 0 := by
    rw [subschemeι_app, hom_comp, comp_apply,
      hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.mpr ht, map_zero]
  have hcomp : I.subschemeι.appLE U V e =
      I.subschemeι.app U ≫ I.subscheme.presheaf.map (homOfLE e).op := rfl
  rw [hcomp, hom_comp, comp_apply, happ, map_zero]

theorem ideal_eq_top_of_one_eq_zero
    (h1 : (1 : ↑(I.subscheme.presheaf.obj
      (Opposite.op $ (Opens.map I.subschemeι.base).obj (U : Opn Y)))) = 0) :
    I.ideal U = ⊤ := by
  have happ : (CommRingCat.Hom.hom $ I.subschemeι.app U) 1 = 0 := by simp_all
  rw [subschemeι_app, hom_comp, comp_apply,
    hom_ofHom] at happ
  have h5 := CommRingCat.hom_inv_apply (I.subschemeObjIso U)
      ((m5 $ I.ideal U) (1 : (pObj Y $ m112 U)))
  exact mpr_ (eq_top_iff_one _) $ Ideal.Quotient.eq_zero_iff_mem.mp $ h5.symm.trans $ tr_ (congrArg (m4 (I.subschemeObjIso U).hom) happ) $ map_zero _
end

theorem notMem_support_of_restrictIdeal_eq_top (D : ISD Y)
    (U : Opn Y) (x : Y) (hx : x ∈ U) (h : restrictIdeal D U = ⊤) : x ∉ support D :=
  notMem_support_of_comap_ι_eq_top D h hx

theorem isLocallyNoetherian_subscheme [IsLocallyNoetherian Y]
    (I : ISD Y) : IsLocallyNoetherian I.subscheme := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun U : affO Y =>
      (⟨siPre I U, isAffineOpen_preimage_subschemeio I U.2⟩ :
        I.subscheme.affineOpens)) ?_ ?_
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  have hx : I.subschemeι.base x ∈ (⨆ V : affO Y, (V : Opn Y)) := by
    rw [iSup_affineOpens_eq_top Y]
    trivial
  obtain ⟨V, hV⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨V, hV⟩
  intro U
  have := m188 U
  exact isNoetherianRing_of_surjective _ _ _ $ surjective_subschemeio_app I U

theorem presheaf_map_eq_id {P : (Y.Opens)ᵒᵖ} (f : P ⟶ P) :
    Y.presheaf.map f = 𝟙 (Y.presheaf.obj P) := by
  have hf : f = 𝟙 P := unop_inj $ m111 _ _
  rw [hf, CategoryTheory.Functor.map_id]

theorem presheaf_map_comp_comp_eq_id {P Q R : (Y.Opens)ᵒᵖ}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ P) :
    (Y.presheaf.map f ≫ Y.presheaf.map g) ≫ Y.presheaf.map h = 𝟙 (Y.presheaf.obj P) := by
  rw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
  exact presheaf_map_eq_id _
end

section
variable {X : Sch}
section
variable {k : Type} [Field k]
theorem mem_of_restrictIdeal_eq_coordIdeal_of_le
    {p : X ⟶ Sp k} {U : Opn X} {m : ℕ} (hU : IsAffineOpen U)
    (c : EtaleChart p U m) (Z H : ISD X) (S : FinSet m) (a : Fin m)
    (hHZ : H ≤ Z) (hH : restrictIdeal H U = c.coordIdeal {a})
    (hZ : restrictIdeal Z U = c.coordIdeal S)
    (x : X) (hxU : x ∈ U) (hxZ : x ∈ support Z) : a ∈ S := by
  by_contra ha
  obtain ⟨i, hi⟩ := exists_complOrderEmb_eq m S ha
  have hHid := c.ideal_eq_span_coord hU H {a} hH
  have hmemH : c.coord a ∈ H.ideal ⟨U, hU⟩ := by simp_all
  let _a0 := c.restrictToSubscheme hU Z S hZ
  have hcoord : _a0.coord i = 0 := by
    rw [restrictToSubscheme_coord, hi]
    exact appLE_subschemeio_apply_eq_zero_of_mem Z ⟨U, hU⟩ _ _ $ hHZ ⟨U, hU⟩ hmemH
  exact notMem_support_of_restrictIdeal_eq_top Z U x hxU
    (mpr_ (comap_ι_eq_top_iff_ideal_eq_top Z hU) $ ideal_eq_top_of_one_eq_zero Z ⟨U, hU⟩ $ (mp_ mem_nonZeroDivisors_iff $ coord_mem_nonZeroDivisors (isAffineOpen_preimage_subschemeio Z hU) _a0 i).1 1 $ by rw [hcoord, zero_mul]) hxZ

theorem exists_etaleChart_of_hasStrictNormalCrossingsWith
    (p : X ⟶ Sp k) (Z H : ISD X) (E : Bdy X)
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (D : ISD X) (hD : D ∈ E) (y : X)
    (hy : y ∈ support Z) :
    ∃ (U : Opn X) (_ : y ∈ U) (_ : IsAffineOpen U) (m : ℕ) (c : EtaleChart p U m)
      (S : FinSet m) (_ : restrictIdeal Z U = c.coordIdeal S),
      restrictIdeal H U = ⊤ ∨ ∃ a : Fin m, restrictIdeal H U = c.coordIdeal {a} ∧
        (restrictIdeal D U = ⊤ ∨ ∃ b : Fin m, b ≠ a ∧ restrictIdeal D U = c.coordIdeal {b}) := by
  obtain ⟨U, hyU, m, c, av, S, hinj, hnone, hsome, hZ⟩ := hsnc y hy
  obtain ⟨i, hi, hEi⟩ : ∃ (i : ℕ) (h : i < length E), E[i] = D := mp_ mem_iff_getElem hD
  have hlt0 : 0 < length (H :: E) := by rw [length_cons]
                                        omega
  have hlti : i + 1 < length (H :: E) := by rw [length_cons]
                                            omega
  have hH0 : ∀ t, av 0 = some t → restrictIdeal H U = c.coordIdeal {t} := by
    intro t ht
    have h := hsome 0 hlt0 t ht
    rwa [getElem_cons_zero] at h
  have hHn : av 0 = none → restrictIdeal H U = ⊤ := by
    intro ht
    have h := hnone 0 hlt0 ht
    rwa [getElem_cons_zero] at h
  have hD0 : ∀ t, av (i + 1) = some t → restrictIdeal D U = c.coordIdeal {t} := by
    intro t ht
    have h := hsome (i + 1) hlti t ht
    simp [getElem_cons_succ] at h
    rwa [hEi] at h
  have hDn : av (i + 1) = none → restrictIdeal D U = ⊤ := by
    intro ht
    have h := hnone (i + 1) hlti ht
    simp [getElem_cons_succ] at h
    rwa [hEi] at h
  obtain ⟨V, hVaff, hyV, hVle⟩ := m227 hyU
  refine ⟨V, hyV, hVaff, m, c.restrict hVle, S,
    restrictIdeal_eq_restrict_coordIdeal_of_le hVle c Z S hZ, ?_⟩
  cases h0 : av 0 with
  | none => exact m51 $ restrictIdeal_eq_top_of_le H hVle $ hHn h0
  | some t =>
      refine m61 ⟨t, restrictIdeal_eq_restrict_coordIdeal_of_le hVle c H {t} $ hH0 t h0, ?_⟩
      cases h1 : av (i + 1) with
      | none => exact m51 $ restrictIdeal_eq_top_of_le D hVle $ hDn h1
      | some t' =>
          refine m61 ⟨t', ?_, restrictIdeal_eq_restrict_coordIdeal_of_le hVle c D {t'} $ hD0 t' h1⟩
          intro htt
          subst htt
          have hz := hinj 0 hlt0 (i + 1) hlti t' h0 h1
          omega

theorem coordIdeal_eq_of_map_eq
    {p1_ p2_ : X ⟶ Sp k} {U : Opn X} {m : ℕ}
    (c1_ : EtaleChart p1_ U m) (c2_ : EtaleChart p2_ U m) (h : c1_.map = c2_.map) (T : FinSet m) :
    c1_.coordIdeal T = c2_.coordIdeal T := by
  rw [coordIdeal_eq_comap_coordSubspaceIdeal, coordIdeal_eq_comap_coordSubspaceIdeal]
  exact congrArg (fun f => cmI (coordSubspaceIdeal k m T) f) h
end

theorem subschemeio_base_mem_support (I : ISD X)
    (x : subscheme I) : I.subschemeι.base x ∈ (support I : Set X) := by
  rw [← range_subschemeι]
  exact mem_range_self x
end

section
variable {X X1 : Sch} {k : Type} [Field k] {p : X ⟶ Sp k}
theorem restrictIdeal_comap_strictTransform_eq_of_blowupChart {pi_ : X1 ⟶ X} [IsLocallyNoetherian X1]
    {U : Opn X} {m : ℕ} {c : EtaleChart p U m} {S : FinSet m} {s : Fin m}
    (B : BlowupChart pi_ c S s) (hU : IsAffineOpen U) (hB : IsAffineOpen B.domain)
    (Z H : ISD X) (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (a : Fin m) (ha : a ∈ S) (has : a ≠ s) (hH : restrictIdeal H U = c.coordIdeal {a})
    (D : ISD X)
    (hDd : restrictIdeal D U = ⊤ ∨ ∃ b : Fin m, b ≠ a ∧ restrictIdeal D U = c.coordIdeal {b})
    (q : (Blowup.strictTransform pi_ Z H).subscheme ⟶ H.subscheme)
    (hq : q ≫ H.si = (Blowup.strictTransform pi_ Z H).si ≫ pi_) :
    restrictIdeal ((Blowup.strictTransform pi_ Z D).comap (Blowup.strictTransform pi_ Z H).si)
        ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) =
      restrictIdeal (Blowup.strictTransform q (Z.comap H.si) (D.comap H.si))
        ((Blowup.strictTransform pi_ Z H).si ⁻¹ᵁ B.domain) := by
  let _a0 := p6 pi_ Z H
  let _a1 := p6 q (cmI Z H.si) $ cmI D H.si
  let _a2 := p6 pi_ Z D
  have : IsLocallyNoetherian _a0.subscheme :=
    isLocallyNoetherian_subscheme _
  have := quasiCompact_strictTransformio_of_isLocallyNoetherian q
    (cmI Z H.si) (cmI D H.si)
  have hsa : s ∉ ({a} : FinSet m) := by
    simp [mem_singleton]
    exact fun h => has h.symm
  obtain ⟨s', hs'⟩ := exists_complOrderEmb_eq m ({a} : FinSet m) hsa
  have hs'S := mem_complEmbPreimage_of_complOrderEmb_eq m S a hs hs'
  have hZ' :=
    restrictIdeal_comap_subschemeio_eq_coordIdeal c hU Z H S a hZ hH
  have hFa :=
    B.restrictIdeal_strictTransform_of_mem_of_ne Z H hs hZ a ha has hH
  rcases hDd with hDtop | ⟨b, hba, hDb⟩
  have hL :=
    restrictIdeal_comap_subschemeio_eq_top _a0 B.domain
      _a2 (B.restrictIdeal_strictTransform_of_eq_top Z D hDtop)
  have hR : restrictIdeal _a1
      (_a0.si.pre B.domain) = ⊤ := by
    have h := (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
        hs' q hq).restrictIdeal_strictTransform_of_eq_top (cmI Z H.si)
        (cmI D H.si) (restrictIdeal_comap_subschemeio_eq_top H U D hDtop)
    exact h
  rw [hL, hR]
  have hb : b ∉ ({a} : FinSet m) := by
    simp [mem_singleton]
    exact hba
  obtain ⟨b', hb'⟩ := exists_complOrderEmb_eq m ({a} : FinSet m) hb
  have hDb' := hDb
  rw [← hb'] at hDb'
  have hRD :=
    restrictToSubscheme_coordIdeal_singleton c hU H {a} hH b' D hDb'
  have hiff : (b = s) ↔ (b' = s') := by
    constructor
    intro h
    apply (complOrderEmb m ({a} : FinSet m)).injective
    rw [hb', hs', h]
    intro h
    rw [← hb', ← hs', h]
  by_cases hbs : b = s
  have hL : restrictIdeal (cmI _a2 _a0.si)
      (_a0.si.pre B.domain) = ⊤ := by
    refine restrictIdeal_comap_subschemeio_eq_top _a0 B.domain
      _a2 ?_
    rw [B.restrictIdeal_strictTransform_coordIdeal Z D hs hZ b hDb, if_pos hbs]
  have hR : restrictIdeal _a1
      (_a0.si.pre B.domain) = ⊤ := by
    have h := (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
        hs' q hq).restrictIdeal_strictTransform_coordIdeal (cmI Z H.si)
        (cmI D H.si) hs'S hZ' b' hRD
    rwa [if_pos (mp_ hiff hbs)] at h
  rw [hL, hR]
  have hL : restrictIdeal (cmI _a2 _a0.si)
      (_a0.si.pre B.domain)
      = (B.chart.restrictToSubscheme hB _a0 {a} hFa).coordIdeal {b'} := by
    refine restrictToSubscheme_coordIdeal_singleton B.chart hB
      _a0 {a} hFa b' _a2 ?_
    rw [B.restrictIdeal_strictTransform_coordIdeal Z D hs hZ b hDb, if_neg hbs, hb']
  have hR : restrictIdeal _a1
      (_a0.si.pre B.domain)
      = (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
          hs' q hq).chart.coordIdeal {b'} := by
    have h := (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s'
        hs' q hq).restrictIdeal_strictTransform_coordIdeal (cmI Z H.si)
        (cmI D H.si) hs'S hZ' b' hRD
    rwa [if_neg fun hxx => hbs $ mpr_ hiff hxx] at h
  rw [hL, hR]
  exact coordIdeal_eq_of_map_eq
    (B.chart.restrictToSubscheme hB _a0 {a} hFa)
    (B.restrictToStrictTransform hU hB Z H hs hZ a ha has hH s' hs' q hq).chart
    (B.restrictToStrictTransform_chart_map hU hB Z H hs hZ a ha has hH s' hs' q hq).symm {b'}

theorem exists_restrictIdeal_eq_of_mem_preimage (pi_ : X1 ⟶ X) [IsLocallyNoetherian X1]
    (Z H : ISD X) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
    (q : subscheme (Blowup.strictTransform pi_ Z H) ⟶ subscheme H)
    (hq : q ≫ subschemeι H = subschemeι (Blowup.strictTransform pi_ Z H) ≫ pi_)
    (D : ISD X) {U : Opn X} (hU : IsAffineOpen U) {m : ℕ} (c : EtaleChart p U m)
    {S : FinSet m} (hZ : restrictIdeal Z U = c.coordIdeal S) {a : Fin m} (ha : a ∈ S)
    (hH : restrictIdeal H U = c.coordIdeal {a})
    (hDd : restrictIdeal D U = ⊤ ∨ ∃ b : Fin m, b ≠ a ∧ restrictIdeal D U = c.coordIdeal {b})
    (x : subscheme $ Blowup.strictTransform pi_ Z H)
    (hxU : (Blowup.strictTransform pi_ Z H).subschemeι.base x ∈ pi_.pre U) :
    ∃ W : (Blowup.strictTransform pi_ Z H).subscheme.Opens, x ∈ W ∧
      restrictIdeal ((Blowup.strictTransform pi_ Z D).comap (Blowup.strictTransform pi_ Z H).si) W =
        restrictIdeal (Blowup.strictTransform q (Z.comap H.si) $ D.comap H.si) W := by
  let _m0 := p6 pi_ Z H
  have : IsLocallyNoetherian _m0.subscheme :=
    isLocallyNoetherian_subscheme _
  obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZ
    (_m0.subschemeι.base x) hxU
  have has : a ≠ s := by
    intro hasEq
    have hH' : restrictIdeal H U = c.coordIdeal {s} := by rw [hH, hasEq]
    have hbot := (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).strictTransform_subschemeio_preimage_domain_eq_bot
      Z H hs hZ hH'
    have hx0 : x ∈ siI _m0 ⁻¹ᵁ
        (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).domain := hmem
    rwa [hbot] at hx0
  obtain ⟨V, hVle, hVaff, hxV⟩ :=
    (blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).exists_isAffineOpen_mem_le_domain
      (_m0.subschemeι.base x) hmem
  exact ⟨siPre _m0 V, hxV, restrictIdeal_comap_strictTransform_eq_of_blowupChart ((blowupChartOfIsBlowup pi_ c S hpi_ hZ s hs).restrict V hVle) hU hVaff Z H hs hZ a ha has hH D hDd q hq⟩
end

theorem exists_strictTransform_lift_of_ker_eq {X X1 S : Sch} (pi_ : X1 ⟶ X) (Z : ISD X)
    (j : S ⟶ X) [IsClosedImmersion j] (H : ISD X)
    (hker : j.ker = H) :
    ∃ q : subscheme (Blowup.strictTransform pi_ Z H) ⟶ S,
      q ≫ j = subschemeι (Blowup.strictTransform pi_ Z H) ≫ pi_ := by
  subst hker
  exact exists_comp_eq_strictTransform_subschemeio_comp j pi_ Z

theorem isBlowupAlongIdealSheaf_comap_of_ker_eq {X X1 S : Sch} [IsLocallyNoetherian X1]
    (pi_ : X1 ⟶ X) (Z : ISD X) (j : S ⟶ X)
    [IsClosedImmersion j] (H : ISD X) (hker : j.ker = H)
    (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (q : subscheme (Blowup.strictTransform pi_ Z H) ⟶ S)
    (hq : q ≫ j = subschemeι (Blowup.strictTransform pi_ Z H) ≫ pi_) :
    IsBlowupAlongIdealSheaf q $ Z.comap j := by
  subst hker
  have h2 : q ≫ j = strictTransformLiftOfClosedImmersion j pi_ Z ≫ j := by
    rw [hq, strictTransformLiftOfClosedImmersion_comp]
  rw [mp_ (cancel_mono j) h2]
  exact isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion j pi_ Z hpi_

section
variable {X X1 : Sch}
section
variable (pi_ : X1 ⟶ X) (Z H : ISD X)
def strictTransformSubschemeLift :
    subscheme (Blowup.strictTransform pi_ Z H) ⟶ subscheme H :=
  ((exists_strictTransform_lift_of_ker_eq pi_ Z H.si H
    (ker_subschemeι H))).choose

theorem strictTransformSubschemeLift_comp_subschemeio :
    strictTransformSubschemeLift pi_ Z H ≫ subschemeι H = subschemeι (Blowup.strictTransform pi_ Z H) ≫ pi_ :=
  (exists_strictTransform_lift_of_ker_eq pi_ Z H.si H
    (ker_subschemeι H)).choose_spec
end

theorem isBlowupAlongIdealSheaf_strictTransformSubschemeLift [IsLocallyNoetherian X1]
    (pi_ : X1 ⟶ X) (Z H : ISD X) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) :
    IsBlowupAlongIdealSheaf (strictTransformSubschemeLift pi_ Z H) $ Z.comap H.si :=
  isBlowupAlongIdealSheaf_comap_of_ker_eq pi_ Z H.si H
    (ker_subschemeι H) hpi_
    (strictTransformSubschemeLift pi_ Z H) $ strictTransformSubschemeLift_comp_subschemeio pi_ Z H
end

section
variable {R : Type} [CommRing R] (J : Ideal R)
def colonSpanSingleton (x : R) : Ideal R where
  carrier := {r | r * x ∈ J}
  add_mem' := fun {a b} ha hb => by
    show (a + b) * x ∈ J
    rw [add_mul]
    exact J.add_mem ha hb
  zero_mem' := by
    show (0 : R) * x ∈ J
    rw [zero_mul]
    exact J.zero_mem
  smul_mem' := fun c a ha => by
    show (c • a) * x ∈ J
    rw [smul_eq_mul, mul_assoc]
    exact J.mul_mem_left c ha

theorem mem_colonSpanSingleton x r :
    r ∈ colonSpanSingleton J x ↔ r * x ∈ J := m22
end

theorem ideal_eq_of_map_eq_of_comp_eq_id {R S : CRC} (f : R ⟶ S) (g : S ⟶ R)
    (hfg : f ≫ g = 𝟙 R) {I J : Ideal R}
    (hIJ : Ideal.map (CommRingCat.Hom.hom f) I = Ideal.map (CommRingCat.Hom.hom f) J) : I = J := by
  have key : ∀ K,
      Ideal.map (CommRingCat.Hom.hom g) (Ideal.map (CommRingCat.Hom.hom f) K) = K := by
    intro K
    rw [map_map, ← hom_comp, hfg, hom_id, Ideal.map_id]
  rw [← key I, hIJ, key J]

theorem ideal_eq_of_restrictIdeal_eq {Y : Sch} (A B : ISD Y)
    (V : Y.affineOpens) (h : restrictIdeal A (V : Opn Y) = restrictIdeal B (V : Opn Y)) :
    A.ideal V = B.ideal V := by
  let _c0 := p4 (V : Opn Y)
  have e : (⊤ : Opn $ toScheme (V : Opn Y)) ≤
      Scheme.Opens.ι (V : Opn Y) ⁻¹ᵁ (V : Opn Y) := by
    intro x _
    exact x.2
  have h' : A.comap _c0 = B.comap _c0 := by
    simpa only [restrictIdeal_eq_comap_io] using h
  have hA := comap_ideal_eq_map_appLE A
    _c0 V ⟨⊤, isAffineOpen_top _⟩ e
  have hB := comap_ideal_eq_map_appLE B
    _c0 V ⟨⊤, isAffineOpen_top _⟩ e
  rw [h'] at hA
  refine sy_ $ ideal_eq_of_map_eq_of_comp_eq_id
    (appLE _c0 (V : Opn Y) ⊤ e)
    (topIso (V : Opn Y)).hom ?_ $ st_ hB hA
  simp [appLE]
  exact presheaf_map_comp_comp_eq_id _ _ _

theorem exists_pow_mul_mem_of_algebraMap_mem_map_of_isLocalizationAway {R S : Type} [CommRing R] [CommRing S]
    [Algebra R S] f [IsLocalization.Away f S] (J : Ideal R) x
    (hx : algebraMap R S x ∈ Ideal.map (algebraMap R S) J) : ∃ n, f ^ n * x ∈ J := by
  rw [mem_map_algebraMap_iff (powers f) S] at hx
  obtain ⟨⟨a, m⟩, hxa⟩ := hx
  rw [← map_mul] at hxa
  obtain ⟨c, hcx⟩ := mp_ (eq_iff_exists (powers f) S) hxa
  obtain ⟨q, hq⟩ := m.2
  obtain ⟨p, hp⟩ := c.2
  refine ⟨p + q, ?_⟩
  have key : f ^ (p + q) * x = c * (x * m) := by
    rw [← hp, ← hq]
    ring
  rw [key, hcx]
  exact J.mul_mem_left _ a.2

section
variable {Y : Sch}
section
variable {ι : Type} (A B : ISD Y) (U : ι → Opn Y) (hU : (⨆ i, U i) = ⊤) (h : ∀ i, restrictIdeal A (U i) = restrictIdeal B (U i))
include hU h
theorem ideal_le_of_restrictIdeal_eq_of_iSup_eq_top
    (V : Y.affineOpens) : A.ideal V ≤ B.ideal V := by
  let _c0 := pObj Y $ m112 V
  intro x hx
  have hV := V.2
  obtain ⟨T, hT⟩ :
      ∃ T,
        ∀ r, r ∈ T ↔ r * x ∈ B.ideal V :=
    ⟨colonSpanSingleton (B.ideal V) x, mem_colonSpanSingleton (B.ideal V) x⟩
  have hcover : (V : Opn Y) ≤
      ⨆ g : (T : Set _c0),
        bOpn Y (g : _c0) := by
    intro y hy
    have hy' : y ∈ (⨆ i, U i) := by rw [hU]
                                    trivial
    obtain ⟨i, hyi⟩ := Opens.mem_iSup.mp hy'
    obtain ⟨f, hfle, hyf⟩ := hV.exists_basicOpen_le (⟨y, hyi⟩ : (U i)) hy
    have hAB :=
      ideal_eq_of_restrictIdeal_eq A B (Y.affineBasicOpen f)
        (restrictIdeal_eq_of_le_of_eq hfle $ h i)
    have := hV.isLocalization_basicOpen f
    let _a1 := pObj Y $ m112 $ bOpn Y f
    have halg : algebraMap _c0
          _a1 =
        (pMap Y (CategoryTheory.homOfLE $ Y.basicOpen_le f).op).hom := rfl
    have hmem : algebraMap _c0
          _a1 x ∈
        Ideal.map (algebraMap _c0
          _a1) (B.ideal V) := by
      rw [halg, B.map_ideal_basicOpen V f, ← hAB, ← A.map_ideal_basicOpen V f]
      exact mem_map_of_mem _ hx
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_algebraMap_mem_map_of_isLocalizationAway f (B.ideal V) x hmem
    let _a0 := f ^ (n + 1)
    have hgT : _a0 ∈ T := by
      have hmul : _a0 * x ∈ B.ideal V := by
        have hfx : _a0 * x = f * (f ^ n * x) := by ring
        rw [hfx]
        exact mul_mem_left _ _ hn
      exact mpr_ (hT _) hmul
    have hyg : y ∈ Y.basicOpen _a0 := by
      rwa [basicOpen_pow]
      exact succ_pos n
    exact Opens.mem_iSup.mpr ⟨⟨_a0, hgT⟩, hyg⟩
  have hspan :=
    hV.self_le_iSup_basicOpen_iff.mp hcover
  have h1 : 1 ∈ T := by simp_all
  have h2 := mp_ (hT 1) h1
  rwa [one_mul] at h2

theorem eq_of_restrictIdeal_eq_of_iSup_eq_top : A = B :=
  m29
    (funext fun V =>
      le_antisymm (ideal_le_of_restrictIdeal_eq_of_iSup_eq_top A B U hU h V)
        (ideal_le_of_restrictIdeal_eq_of_iSup_eq_top B A U hU (fun i => sy_ $ h i) V))
end

theorem eq_of_locally_restrictIdeal_eq (A B : ISD Y)
    (h : ∀ x : Y, ∃ U : Opn Y, x ∈ U ∧ restrictIdeal A U = restrictIdeal B U) : A = B := by
  choose U hxU hAB using h
  refine eq_of_restrictIdeal_eq_of_iSup_eq_top A B U ?_ hAB
  ext x
  exact ⟨fun _ => trivial, fun _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩⟩
end

section
variable {X X1 : Sch} {k : Type} [Field k] (p : X ⟶ Sp k) (pi_ : X1 ⟶ X) [IsLocallyNoetherian X1] (Z H : ISD X) (E : Bdy X) (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z)
include hsnc hHZ hpi_
theorem comap_strictTransform_eq_strictTransform_of_comp_eq
    (q : subscheme (Blowup.strictTransform pi_ Z H) ⟶ subscheme H)
    (hq : q ≫ subschemeι H = subschemeι (Blowup.strictTransform pi_ Z H) ≫ pi_)
    (D : ISD X) (hD : D ∈ E) :
    (Blowup.strictTransform pi_ Z D).comap (Blowup.strictTransform pi_ Z H).si =
      Blowup.strictTransform q (Z.comap H.si) (D.comap H.si) := by
  let _a0 := p6 pi_ Z H
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : bsM pi_ (_a0.subschemeι.base x) ∈ spI Z
  obtain ⟨U, hyU, hU, m, c, S, hZc, hcase⟩ :=
    exists_etaleChart_of_hasStrictNormalCrossingsWith p Z H E hsnc D hD
      (bsM pi_ (_a0.subschemeι.base x)) hx
  rcases hcase with hHtop | ⟨a, hH, hDd⟩
  have _i55 : False := by
    let _a0 := p6 pi_ Z H
    obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c S hpi_ hZc
      (_a0.subschemeι.base x) hyU
    let _a1 := blowupChartOfIsBlowup pi_ c S hpi_ hZc s hs
    exact notMem_support_of_restrictIdeal_eq_top _a0
      _a1.domain
      (_a0.subschemeι.base x) hmem (_a1.restrictIdeal_strictTransform_of_eq_top Z H hHtop)
      (subschemeio_base_mem_support _a0 x)
  exact _i55.elim
  exact exists_restrictIdeal_eq_of_mem_preimage pi_ Z H hpi_ q hq D hU c hZc
    (mem_of_restrictIdeal_eq_coordIdeal_of_le hU c Z H S a hHZ hH hZc
      (bsM pi_ (_a0.subschemeι.base x)) hyU hx) hH hDd x hyU
  let _c0 := p6 pi_ Z H
  let _c1 := pre pi_ (suppC Z)
  have : IsLocallyNoetherian _c0.subscheme :=
    isLocallyNoetherian_subscheme _
  have := quasiCompact_strictTransformio_of_isLocallyNoetherian q
    (cmI Z H.si) (cmI D H.si)
  have hZcomap : (Z.comap H.si).comap q
      = (Z.comap pi_).comap _c0.si := by
    rw [← comap_comp,
      ← comap_comp, hq]
  have hVmem : ∀ z, z ∈ _c1 → bsM pi_ z ∉ spI Z := fun z hz => hz
  have hWmem : ∀ z,
      z ∈ (_c0.si.pre _c1) →
        q.base z ∉ spI (cmI Z H.si) := by
    intro z hz hmem
    have h1 : z ∈ support ((Z.comap H.si).comap q) := by
      rwa [m19]
    rw [hZcomap, m19] at h1
    have h2 := h1
    rw [m19] at h2
    exact hz h2
  refine ⟨_c0.si.pre _c1, hx, ?_⟩
  rw [restrictIdeal_comap_eq_comap_resLE_restrictIdeal _c0.si
      (p6 pi_ Z D) _c1
      (_c0.si.pre _c1) le_rfl,
    restrictIdeal_strictTransform_eq_comap_of_notMem_support pi_ Z D _ hVmem,
    ← restrictIdeal_comap_eq_comap_resLE_restrictIdeal _c0.si
      (cmI D pi_) _c1
      (_c0.si.pre _c1) le_rfl,
    restrictIdeal_strictTransform_eq_comap_of_notMem_support q (cmI Z H.si)
      (cmI D H.si) _ hWmem,
    ← comap_comp,
    ← comap_comp, hq]

theorem comap_strictTransform_eq_strictTransformSubschemeLift
    (D : ISD X) (hD : D ∈ E) :
    (Blowup.strictTransform pi_ Z D).comap (Blowup.strictTransform pi_ Z H).si =
      Blowup.strictTransform (strictTransformSubschemeLift pi_ Z H) (Z.comap H.si) (D.comap H.si) :=
  comap_strictTransform_eq_strictTransform_of_comp_eq p pi_ Z H E hsnc hHZ hpi_
    (strictTransformSubschemeLift pi_ Z H) (strictTransformSubschemeLift_comp_subschemeio pi_ Z H) D hD
end





theorem restrictIdeal_mul {X : Sch} (I J : ISD X) (U : Opn X) :
    restrictIdeal (I * J) U = restrictIdeal I U * restrictIdeal J U :=
  comap_mul I J U.i

section
variable {X X' : Sch}
section
variable {k : Type} [Field k] (p : X ⟶ Sp k) (pi_ : X' ⟶ X) {U : Opn X} {m : ℕ} (c : EtaleChart p U m) (V : Opn X') (hV : V ≤ pre pi_ U)
section
variable (he : Etale (pi_.resLE U V hV))
include he
def EtaleChart.comap : EtaleChart (pi_ ≫ p) V m where
  map := pi_.resLE U V hV ≫ c.map
  comp_struct := by
    have h1 : pi_.resLE U V hV ≫ ι U = ι V ≫ pi_ := by simp
    rw [assoc, c.comp_struct, ← assoc, h1, assoc]
  isEtale := by
    have := he
    have := c.isEtale
    infer_instance

theorem EtaleChart.comap_map :
    (EtaleChart.comap p pi_ c V hV he).map = pi_.resLE U V hV ≫ c.map := rfl

theorem EtaleChart.comap_coordIdeal (S : FinSet m) :
    (EtaleChart.comap p pi_ c V hV he).coordIdeal S =
      (c.coordIdeal S).comap (pi_.resLE U V hV) := by
  rw [coordIdeal_eq_comap_coordSubspaceIdeal, coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.comap_map,
    comap_comp]
end
end

theorem restrictIdeal_comap_eq_top_of_notMem_support (pi_ : X' ⟶ X)
    (B : ISD X) (V : Opn X') (hV : ∀ y : X', y ∈ V → pi_.base y ∉ support B) :
    restrictIdeal (B.comap pi_) V = ⊤ := by
  have hcc : B.comap (ι V ≫ pi_) = (B.comap pi_).comap V.i := by
    rw [m56]
  have htop : B.comap (ι V ≫ pi_) = ⊤ := by
    refine p39 (opI V ≫ pi_) B ?_
    intro y
    have hy : opIb V y ∈ Set.range V.ib := mem_range_self y
    rw [range_ι] at hy
    simpa using (hV _ hy)
  rwa [restrictIdeal_eq_comap_io, ← hcc]

theorem isSmoothDivisor_comap_of_isBlowupAlongIdealSheaf {k : Type} [Field k]
    [CharZero k] (p : X ⟶ Sp k) [Smooth p]
    (pi_ : X' ⟶ X) [Smooth $ pi_ ≫ p] (Z B : ISD X)
    (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (hB : IsSmoothDivisor p B)
    (hdisj : Disjoint (support Z : Set X) (support B : Set X)) :
    IsSmoothDivisor (pi_ ≫ p) $ B.comap pi_ := by
  refine isSmoothDivisor_of_locally_coordIdeal (cmI B pi_) ?_
  intro x'
  by_cases hx : bsM pi_ x' ∈ spI B
  obtain ⟨U, m, c, j, hxU, hBU⟩ :=
    exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton p B hB (bsM pi_ x') hx
  have hxZ := fun hZ => (mp_ disjoint_left hdisj hZ) hx
  let _s0 := U ⊓ suppC Z
  have hWle : _s0 ≤ U := inf_le_left
  have hiso2 := isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hpi_ _s0 fun y hy => an2 hy
  rw [← resLE_eq_morphismRestrict] at hiso2
  refine ⟨pre pi_ _s0, ⟨hxU, hxZ⟩, m,
    EtaleChart.comap p pi_ (c.restrict hWle)
      (pre pi_ _s0) le_rfl inferInstance, m61 ⟨j, ?_⟩⟩
  rw [EtaleChart.comap_coordIdeal,
    restrictIdeal_comap_eq_comap_resLE_restrictIdeal pi_ B _s0
      (preU pi_ _s0) le_rfl,
    restrictIdeal_eq_restrict_coordIdeal_of_le hWle c B {j} hBU]
  obtain ⟨U, m, hxU, hUW, -, ⟨c⟩⟩ :=
    exists_etaleChart_le (pi_ ≫ p) x' (pre pi_ $ suppC B) hx
  refine ⟨U, hxU, m, c, m51 ?_⟩
  refine restrictIdeal_comap_eq_top_of_notMem_support pi_ B U ?_
  intro y hy
  exact hUW hy

theorem strictTransform_mul_of_disjoint_support [IsLocallyNoetherian X']
    (pi_ : X' ⟶ X) (Z A B : ISD X)
    (hBZ : Disjoint (support B : Set X) (support Z : Set X)) :
    Blowup.strictTransform pi_ Z (A * B) = Blowup.strictTransform pi_ Z A * B.comap pi_ := by
  let _c0 := opI (pre pi_ $ suppC B) ≫ pi_
  refine eq_of_locally_restrictIdeal_eq _ _ ?_
  intro x
  by_cases hx : bsM pi_ x ∈ spI Z
  have hxB := fun hB => (mp_ disjoint_left hBZ hB) hx
  refine ⟨pre pi_ $ suppC B, hxB, ?_⟩
  have hVmem : ∀ y, y ∈ pre pi_ (suppC B) → bsM pi_ y ∉ spI B := by
    intro y hy
    exact hy
  have hBtop :=
    restrictIdeal_comap_eq_top_of_notMem_support pi_ B _ hVmem
  have hcomapB : B.comap _c0 = ⊤ := by
    rwa [comap_comp]
  have hD : (A * B).comap _c0
      = A.comap _c0 := by
    rw [comap_mul, hcomapB, mul_top]
  rw [restrictIdeal_mul, hBtop, mul_top,
    restrictIdeal_strictTransform pi_ Z (A * B) $ pre pi_ $ suppC B,
    restrictIdeal_strictTransform pi_ Z A $ pre pi_ $ suppC B]
  exact strictTransform_eq_of_comap_eq _ _ Z (A * B) Z A rfl hD
  refine ⟨pre pi_ $ suppC Z, hx, ?_⟩
  have hVmem : ∀ y, y ∈ pre pi_ (suppC Z) → bsM pi_ y ∉ spI Z := by
    intro y hy
    exact hy
  rw [restrictIdeal_strictTransform_eq_comap_of_notMem_support pi_ Z (A * B) _ hVmem,
    comap_mul, restrictIdeal_mul, restrictIdeal_mul,
    restrictIdeal_strictTransform_eq_comap_of_notMem_support pi_ Z A _ hVmem]
end




theorem presheaf_map_eq__b27 {X : Sch} {A B} (f g : A ⟶ B) :
    X.presheaf.map f = X.presheaf.map g := by
  rw [unop_inj $ m111 f.unop g.unop]

private theorem exists_affineOpen_le {X : Sch} (x : ↥X) (W : Opn X)
    (hx : x ∈ W) : ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨U, hU, hxU, hUW⟩ := m227 hx
  exact ⟨⟨U, hU⟩, hxU, hUW⟩

section
variable {Y : Sch}
theorem idealSheafData_mul_le_mul {A B C D : ISD Y}
    (h1 : A ≤ B) (h2 : C ≤ D) : A * C ≤ B * D := by
  refine mpr_ le_def fun U => ?_
  rw [ideal_mul, ideal_mul]
  exact mul_mono (mp_ le_def h1 U)
    (mp_ le_def h2 U)

private theorem ideal_eq_of_comap_io_eq {A B : ISD Y}
    (V : Y.affineOpens) (h : A.comap (V : Opn Y).i = B.comap (V : Opn Y).i) :
    A.ideal V = B.ideal V := by
  have e : (⊤ : (V : Opn Y).toScheme.Opens) ≤ (V : Opn Y).i.pre (V : Opn Y) := by simp
  have h1 := A.comap_ideal_eq_map_appLE (V : Opn Y).i V ⟨⊤, isAffineOpen_top _⟩ e
  rw [h, B.comap_ideal_eq_map_appLE (V : Opn Y).i V ⟨⊤, isAffineOpen_top _⟩ e] at h1
  have hbij : Bijective ((V : Opn Y).ι.appLE (V : Opn Y) ⊤ e).hom := by
    let V := (V : Opn Y)
    have h : V.ι.appLE V ⊤ e = V.topIso.inv := by
      simp
      exact presheaf_map_eq__b27 _ _
    rw [h]
    exact ConcreteCategory.bijective_of_isIso _
  let _m0 := (V : Opn Y).ι.appLE (V : Opn Y) ⊤ e
  have hbot : Ideal.comap _m0.hom
      (⊥ : Ideal Γ(oSch (V : Opn Y), ⊤)) = ⊥ :=
    (injective_iff_ker_eq_bot _).mp hbij.1
  have h3 := congrArg (Ideal.comap _m0.hom) h1
  rw [comap_map_of_surjective _ hbij.2, comap_map_of_surjective _ hbij.2, hbot,
    sup_bot_eq, sup_bot_eq] at h3
  exact sy_ h3

theorem le_of_forall_exists_affineOpen {A B : ISD Y}
    (h : ∀ y : ↥Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧ A.ideal U ≤ B.ideal U) :
    A ≤ B := by
  refine mpr_ le_def fun U => ?_
  refine of_affine_open_cover (P := fun W => A.ideal W ≤ B.ideal W)
    (fun y => (h y).choose) ?_ U ?_ ?_ ?_
  rw [eq_top_iff]
  intro y _
  exact mpr_ mem_iSup ⟨y, (h y).choose_spec.1⟩
  intro W f hW
  rw [← A.map_ideal_basicOpen W f, ← B.map_ideal_basicOpen W f]
  exact map_mono hW
  intro W s hspan hs x hxA
  refine mem_of_span_eq_top_of_smul_pow_mem (B.ideal W) (s : Set Γ(Y, W.1)) hspan x ?_
  rintro ⟨f, hf⟩
  let _a1 := homOfLE $ Y.basicOpen_le f
  let _a0 := pMap Y _a1.op
  have hmem : _a0.hom x ∈
      (B.ideal W).map _a0.hom := by
    rw [B.map_ideal_basicOpen W f]
    refine hs ⟨f, Finset.mem_coe.mp hf⟩ ?_
    rw [← A.map_ideal_basicOpen W f]
    exact mem_map_of_mem _ hxA
  obtain ⟨n, hn⟩ : ∃ n, f ^ n * x ∈ (B.ideal W) := by
    let U := W
    have := U.2.isLocalization_basicOpen f
    have halg : (algebraMap Γ(Y, U.1) Γ(Y, bOpn Y f)) =
        (pMap Y _a1.op).hom := rfl
    rw [← halg] at hmem
    obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hxy⟩ :=
      (mem_map_algebraMap_iff (powers f) Γ(Y, bOpn Y f)).mp hmem
    simp only at hxy
    rw [← map_mul] at hxy
    obtain ⟨⟨c, hc⟩, hcc⟩ :=
      (eq_iff_exists (powers f) Γ(Y, bOpn Y f)).mp hxy
    obtain ⟨a, rfl⟩ := hm
    obtain ⟨b, rfl⟩ := hc
    refine ⟨b + a, ?_⟩
    simp only at hcc
    have h2 : f ^ (b + a) * x = f ^ b * y := by rw [← hcc]
                                                ring
    rw [h2]
    exact (B.ideal W).mul_mem_left _ hy
  exact ⟨n, by simpa [smul_eq_mul] using hn⟩
  intro y
  exact (h y).choose_spec.2

private theorem idealSheafData_mul_le_left (A B : ISD Y) :
    A * B ≤ A := by
  refine mpr_ le_def fun U => ?_
  rw [ideal_mul]
  exact Ideal.mul_le.mpr fun r hr s _ => mul_mem_right _ _ hr

theorem idealSheafData_pow_le_pow_of_le (A : ISD Y) {i j : ℕ}
    (h : j ≤ i) : A ^ i ≤ A ^ j := by
  obtain ⟨d, rfl⟩ := exists_eq_add_of_le h
  calc A ^ (j + d) = A ^ j * A ^ d := by rw [pow_add]
    _ ≤ A ^ j := idealSheafData_mul_le_left _ _
end

section
variable (k : Type)
section
variable [Field k] [CharZero k]
theorem derivIdealSheafIterate_pow_mul_le {Y : Sch}
    (q : Y ⟶ Sp k) [Smooth q]
    (F J : ISD Y) (m j : ℕ) (hj : j ≤ m) :
    derivIdealSheafIterate k q j (F ^ m * J) ≤ F ^ (m - j) * derivIdealSheafIterate k q j J := by
  let _a1 := derivIdealSheaf k q F
  revert hj
  induction j with
  | zero =>
    intro _
    rw [derivIdealSheafIterate_zero, derivIdealSheafIterate_zero, m130]
  | succ j ih =>
    intro hj
    let _a0 := m - (j + 1)
    have h1 : m - j = _a0 + 1 := by omega
    rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ]
    refine le_trans (derivIdealSheaf_mono k q $ ih $ m212 hj) ?_
    rw [h1]
    let J := derivIdealSheafIterate k q j J
    let n := _a0
    refine le_trans (derivIdealSheaf_mul_le k q (F ^ (n + 1)) J) $ sup_le (idealSheafData_mul_le_mul (idealSheafData_pow_le_pow_of_le F $ le_succ n) le_rfl) ?_
    calc J * derivIdealSheaf k q (F ^ (n + 1))
        ≤ J * (F ^ n * _a1) :=
          idealSheafData_mul_le_mul le_rfl $ derivIdealSheaf_pow_succ_le k q F n
      _ = F ^ n * (J * _a1) := mul_left_comm _ _ _
      _ ≤ F ^ n * derivIdealSheaf k q J :=
          idealSheafData_mul_le_mul le_rfl
            (le_trans (idealSheafData_mul_le_left J _a1)
              (le_derivIdealSheaf k q J))

theorem derivIdealSheafIterate_le_pow_of_hasStrictNormalCrossingsWith
    {X : Sch} (p : X ⟶ Sp k) [Smooth p]
    (Z I : ISD X) (E : Bdy X) (hZ : HasStrictNormalCrossingsWith p Z E) (m : ℕ)
    (hI : I ≤ Z ^ m) (j : ℕ) :
    derivIdealSheafIterate k p j I ≤ Z ^ (m - j) :=
  le_pow_of_hasStrictNormalCrossingsWith p Z (derivIdealSheafIterate k p j I) E hZ (m - j)
    (m90 (support_subset_orderAtLeastLocus_of_le_pow Z I m hI)
      (orderAtLeastLocus_subset_orderAtLeastLocus_derivIdealSheafIterate k p I j m))
end

theorem derivIdealSheafIterate_congr_hom [CommRing k] [IsNoetherianRing k]
    {X : Sch} (q q' : X ⟶ Sp k) [LocallyOfFiniteType q]
    [LocallyOfFiniteType q'] (hq : q = q') (r : ℕ) (I : ISD X) :
    derivIdealSheafIterate k q r I = derivIdealSheafIterate k q' r I := by
  subst hq
  rfl

section
variable [hv1_0 : Field k] [hv1_1 : CharZero k] {X X1 : Sch} (p : X ⟶ Sp k) [Smooth p] (pi_ : X1 ⟶ X)
include hv1_0 hv1_1
theorem exists_affineOpen_comap_derivIdealSheafIterate_eq [Smooth (pi_ ≫ p)] (W : Opn X)
    [IsIso $ morphismRestrict pi_ W] (x : ↥X1) (hx : x ∈ pre pi_ W)
    (j : ℕ) (I : ISD X) :
    ∃ V : X1.affineOpens, x ∈ V.1 ∧ V.1 ≤ pre pi_ W ∧
      ((derivIdealSheafIterate k p j I).comap pi_).ideal V =
        (derivIdealSheafIterate k (pi_ ≫ p) j $ I.comap pi_).ideal V := by
  obtain ⟨V, hxV, hVW⟩ := exists_affineOpen_le x (preU pi_ W) hx
  refine ⟨V, hxV, hVW, ?_⟩
  have hfac : opI (V : Opn X1) ≫ pi_
      = X1.homOfLE hVW ≫ (morphismRestrict pi_ W ≫ opI W) := by simp_all
  have : IsOpenImmersion $ opI (V : Opn X1) ≫ pi_ := by rw [hfac]
                                                        infer_instance
  have : Smooth $ opI (V : Opn X1) ≫ pi_ := inferInstance
  have hcomp : ∀ A : ISD X,
      A.comap (opI (V : Opn X1) ≫ pi_) = cmI (cmI A pi_) (V : Opn X1).i := by simp_all
  let _a1 := pi_ ≫ p
  have h1 := derivIdealSheafIterate_comap k p (opI (V : Opn X1) ≫ pi_) j I
  rw [hcomp I] at h1
  rw [derivIdealSheafIterate_congr_hom k ((opI (V : Opn X1) ≫ pi_) ≫ p)
      (opI (V : Opn X1) ≫ _a1) (assoc _ _ _) j $ cmI (cmI I pi_) (V : Opn X1).i] at h1
  have key := derivIdealSheafIterate_comap k _a1 (V : Opn X1).i j $ cmI I pi_
  rw [h1, hcomp $ derivIdealSheafIterate k p j I] at key
  exact ideal_eq_of_comap_io_eq V key

theorem comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul [IsLocallyNoetherian X1] (Z : ISD X) (E : Bdy X)
    (hZ : HasStrictNormalCrossingsWith p Z E) (hpi_ : IsBlowupAlongIdealSheaf pi_ Z) (I : ISD X) (m : ℕ)
    (hI : I ≤ Z ^ m) (j : ℕ) (hj : j ≤ m) :
    haveI : Smooth (pi_ ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hZ hpi_
    cmI (derivIdealSheafIterate k p j I) pi_ ≤
      exceptionalIdeal pi_ Z ^ (m - j) *
        derivIdealSheafIterate k (pi_ ≫ p) j (controlledTransform pi_ Z I m hpi_ hI) := by
  have := smooth_comp_of_isBlowupAlongIdealSheaf hZ hpi_
  refine le_of_forall_exists_affineOpen ?_
  intro x
  by_cases hxs : bsM pi_ x ∈ spI Z
  obtain ⟨U, hxU, n, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hxs
  obtain ⟨U0_, hxU0, hU0U⟩ := exists_affineOpen_le (bsM pi_ x) U hxU
  have hle := hU0U
  set c0_ := c.restrict hle with hc0_
  have hZU0 : restrictIdeal Z U0_ = c0_.coordIdeal S := by
    rw [hc0_]
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hle c Z S hZU
  obtain ⟨s, hs, hxB⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf pi_ c0_ S hpi_ hZU0 x hxU0
  set Bc := blowupChartOfIsBlowup pi_ c0_ S hpi_ hZU0 s hs with hBc
  obtain ⟨V, hxV, hVle⟩ := exists_affineOpen_le x Bc.domain hxB
  refine ⟨V, hxV, ?_⟩
  have hVdom := hVle
  have hVU := le_trans hVdom Bc.domain_le
  set cV := Bc.chart.restrict hVdom with hcV
  have hcoordres : ∀ i,
      cV.coord i = (pMap X1 (homOfLE hVdom).op).hom (Bc.chart.coord i) := by
    intro i
    rw [hcV]
    exact coord_restrict Bc.chart hVdom i
  have hE : (exceptionalIdeal pi_ Z).ideal V = span {cV.coord s} := by
    have h1 : restrictIdeal (exceptionalIdeal pi_ Z) V = cV.coordIdeal {s} := by
      rw [hcV]
      exact restrictIdeal_eq_restrict_coordIdeal_of_le hVdom Bc.chart (exceptionalIdeal pi_ Z) {s}
        (Bc.restrictIdeal_exceptionalIdeal Z hs hZU0)
    have h2 := ideal_eq_span_coord cV V.2 (exceptionalIdeal pi_ Z) {s} h1
    simpa using h2
  have hEpow : ∀ t C,
      (exceptionalIdeal pi_ Z ^ t * C).ideal V = span {cV.coord s ^ t} * C.ideal V := by
    intro t C
    rw [ideal_mul, ideal_pow]
    show (exceptionalIdeal pi_ Z).ideal V ^ t * C.ideal V
      = span {cV.coord s ^ t} * C.ideal V
    rw [hE, span_singleton_pow]
  let algU := c0_.algebra
  let algV := cV.algebra
  let kU := sectionsAlgebra k p U0_
  let kV := sectionsAlgebra k (pi_ ≫ p) V
  have towerU := c0_.isScalarTower
  have towerV := cV.isScalarTower
  have feU := c0_.algebra_formallyEtale U0_.2
  have feV := cV.algebra_formallyEtale V.2
  let phA : X.sec U0_ →ₐ[k] (X1.sec V) :=
    { (appLE pi_ U0_ V hVU).hom with
      commutes' := fun a => sectionsAlgebraMap_appLE_apply k p pi_ _ _ hVU a }
  have hph : ∀ y, phA y
      = (pMap X1 (homOfLE hVdom).op).hom
          ((appLE pi_ U0_ Bc.domain Bc.domain_le).hom y) := by
    intro y
    show (appLE pi_ U0_ V hVU).hom y = _
    rw [← CommRingCat.comp_apply, appLE_map]
  have hmap : ∀ J : Ideal (X.sec U0_),
      Ideal.map phA J
        = Ideal.map (appLE pi_ U0_ V hVU).hom J := fun J => rfl
  have hcoordU : ∀ i : UFin n,
      @EtaleCoordinates.coord k _ (UFin n) (X.sec U0_) _ algU i
        = c0_.coord i.down := by
    rintro ⟨i⟩
    exact c0_.etaleCoordinates_coord i
  have hcoordV : ∀ i : UFin n,
      @EtaleCoordinates.coord k _ (UFin n) (X1.sec V) _ algV i
        = cV.coord i.down := by
    rintro ⟨i⟩
    exact cV.etaleCoordinates_coord i
  have hcoordVs := cV.etaleCoordinates_coord s
  have hin : ∀ i ∈ uliftFinset n S, i ≠ (up s) →
      phA (@EtaleCoordinates.coord k _ (UFin n) (X.sec U0_) _ algU i)
        = @EtaleCoordinates.coord k _ (UFin n) (X1.sec V) _ algV i *
          @EtaleCoordinates.coord k _ (UFin n) (X1.sec V) _ algV
            (up s) := by
    intro i hi his
    have hids := fun hh => his $ ULift.ext i (up s) hh
    rw [hcoordU i, hcoordV i, hcoordVs, hph, Bc.appLE_coord_of_mem i.down (down_mem_of_mem_uliftFinset hi) hids, map_mul, hcoordres, hcoordres]
  have hsc : phA (@EtaleCoordinates.coord k _ (UFin n) (X.sec U0_) _ algU
        (up s))
      = @EtaleCoordinates.coord k _ (UFin n) (X1.sec V) _ algV
          (up s) := by
    rw [hcoordU (up s), hcoordVs, hph, Bc.appLE_coord_self, hcoordres]
  have hout : ∀ i ∉ uliftFinset n S,
      phA (@EtaleCoordinates.coord k _ (UFin n) (X.sec U0_) _ algU i)
        = @EtaleCoordinates.coord k _ (UFin n) (X1.sec V) _ algV i := by
    intro i hi
    have hid := fun hh => hi $ mpr_ (mem_uliftFinset S i) hh
    rw [hcoordU i, hcoordV i, hph, Bc.appLE_coord_of_not_mem i.down hid, hcoordres]
  have hnzd : @EtaleCoordinates.coord k _ (UFin n) (X1.sec V) _ algV
      (up s) ∈ nonZeroDivisors (X1.sec V) := by
    rw [hcoordVs]
    exact coord_mem_nonZeroDivisors V.2 cV s
  have hJ : Ideal.map phA (I.ideal U0_) ≤
      span {(@EtaleCoordinates.coord k _ (UFin n) (X1.sec V) _ algV
        (up s)) ^ m} * (controlledTransform pi_ Z I m hpi_ hI).ideal V := by
    have h1 :=
      I.map_appLE_le_comap_ideal pi_ U0_ V hVU
    rw [← exceptionalIdeal_pow_mul_controlledTransform pi_ Z I m hpi_ hI,
      hEpow m (controlledTransform pi_ Z I m hpi_ hI)] at h1
    rwa [hcoordVs, hmap]
  have hring := EtaleCoordinates.map_derivIdealIterate_le_span_pow_mul k (UFin n)
    (X.sec U0_) (X1.sec V) phA (uliftFinset n S) (up s)
    hin hsc hout (up_mem_uliftFinset hs) hnzd (I.ideal U0_) ((controlledTransform pi_ Z I m hpi_ hI).ideal V) m hJ j hj
  rw [hcoordVs] at hring
  rw [(derivIdealSheafIterate k p j I).comap_ideal_eq_map_appLE pi_ U0_ V hVU,
    derivIdealSheafIterate_ideal,
    hEpow (m - j) (derivIdealSheafIterate k (pi_ ≫ p) j (controlledTransform pi_ Z I m hpi_ hI)),
    derivIdealSheafIterate_ideal, ← hmap]
  exact hring
  have :=
    blowupIsIsoOffCenter X X1 pi_ Z hpi_
  obtain ⟨V, hxV, hVW, heq⟩ :=
    exists_affineOpen_comap_derivIdealSheafIterate_eq k p pi_ Z.support.compl x hxs j I
  refine ⟨V, hxV, ?_⟩
  rw [heq]
  have h2 := derivIdealSheafIterate_pow_mul_le k (pi_ ≫ p) (exceptionalIdeal pi_ Z)
    (controlledTransform pi_ Z I m hpi_ hI) m j hj
  rw [exceptionalIdeal_pow_mul_controlledTransform pi_ Z I m hpi_ hI] at h2
  exact mp_ le_def h2 V
end
end

end FunctorialResolution.EmbeddedResolution
end
end
