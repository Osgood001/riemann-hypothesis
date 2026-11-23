import Mathlib
abbrev Sch := AlgebraicGeometry.Scheme.{0}
abbrev CRC := CommRingCat.{0}
noncomputable abbrev Sp (R : Type) [CommRing R] := AlgebraicGeometry.Spec $ CommRingCat.of.{0} R
abbrev UFin (n : ℕ) := ULift.{0, 0} $ Fin n
abbrev UFS (m n : ℕ) := ULift.{0, 0} $ Fin m ⊕ Fin n
abbrev FinSet (m : ℕ) := Finset $ Fin m
abbrev MvU (m : ℕ) (k : Type) [CommSemiring k] := MvPolynomial (UFin m) k
abbrev List.lget.{u} {al_ : Type u} (L : List al_) (j : ℕ) (hj : j < L.length) := L.get ⟨j, hj⟩
abbrev CSet (X : Sch) := Set ↥X
abbrev AlgebraicGeometry.Scheme.sec (X : Sch) (U : X.Opens) := X.presheaf.obj $ Opposite.op U
section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry (SmoothOfRelativeDimension smoothOfRelativeDimension_iff)
open Limits.Sigma (desc)
open Finset (sum_add_distrib sum_congr)
open Ideal (smul_eq_mul subset_span)
open Ideal.Quotient (eq_zero_iff_mem)
open IsLocalRing (CotangentSpace mem_maximalIdeal)
open Nat (exists_eq_add_of_le mul_comm zero_add)
open Set (image_image)
open Scheme.Hom (appLE)
noncomputable abbrev AlgebraicGeometry.Scheme.Opens.sec {X : Sch} (U : X.Opens) := X.presheaf.obj $ Opposite.op U
noncomputable abbrev AlgebraicGeometry.Scheme.Opens.i {X : Sch} (U : X.Opens) := U.ι
noncomputable abbrev AlgebraicGeometry.Scheme.Opens.ib {X : Sch} (U : X.Opens) := U.ι.base
noncomputable abbrev AlgebraicGeometry.Scheme.IdealSheafData.si {X : Sch} (I : X.IdealSheafData) := I.subschemeι
noncomputable abbrev AlgebraicGeometry.Scheme.GSpecIso.{u} (R : CommRingCat.{u}) := AlgebraicGeometry.Scheme.ΓSpecIso R
noncomputable abbrev AlgebraicGeometry.Scheme.Hom.pre {X Y : Sch} (f : X ⟶ Y) (U : Y.Opens) := f ⁻¹ᵁ U
noncomputable abbrev AlgebraicGeometry.Scheme.Hom.im {X Y : Sch} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) := f ''ᵁ U
noncomputable abbrev AlgebraicGeometry.Scheme.Hom.mr {X Y : Sch} (f : X ⟶ Y) (U : Y.Opens) := f ∣_ U
end
abbrev AlgebraicGeometry.Scheme.IdealSheafData.supp {X : Sch} (I : X.IdealSheafData) : Set ↥X := (I.support : Set ↥X)
noncomputable section
open CategoryTheory AlgebraicGeometry
-- BEGIN_E2_B00_ABBREVS
abbrev ISD (X : Sch) := X.IdealSheafData
abbrev Bdy (X : Sch) := List X.IdealSheafData
abbrev Opn (X : Sch) := X.Opens
abbrev opI {X : Sch} (U : X.Opens) := U.ι
abbrev opIb {X : Sch} (U : X.Opens) := U.ι.base
abbrev opS {X : Sch} (U : X.Opens) : Set ↥X := (U : Set ↥X)
abbrev opSec {X : Sch} (U : X.Opens) := X.presheaf.obj $ Opposite.op U
abbrev xSec (X : Sch) (U : X.Opens) := X.presheaf.obj $ Opposite.op U
abbrev bOpn (X : Sch) {U : X.Opens} (f : X.presheaf.obj (Opposite.op U)) := X.basicOpen f
abbrev subS {X : Sch} (I : X.IdealSheafData) := I.subscheme
abbrev siI {X : Sch} (I : X.IdealSheafData) := I.subschemeι
abbrev suppI {X : Sch} (I : X.IdealSheafData) : Set ↥X := (I.support : Set ↥X)
abbrev suppC {X : Sch} (I : X.IdealSheafData) := I.support.compl
abbrev cmI {X Y : Sch} (I : Y.IdealSheafData) (f : X ⟶ Y) := I.comap f
abbrev preU {X Y : Sch} (f : X ⟶ Y) (U : Y.Opens) := f ⁻¹ᵁ U
abbrev pIm {α β : Type*} (f : α → β) (s : Set β) := f ⁻¹' s
abbrev imU {X Y : Sch} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) := f ''ᵁ U
abbrev mrU {X Y : Sch} (f : X ⟶ Y) (U : Y.Opens) := f ∣_ U
abbrev siPre {X : Sch} (I : X.IdealSheafData) (U : X.Opens) := I.subschemeι ⁻¹ᵁ U
abbrev opPre {X : Sch} (U V : X.Opens) := U.ι ⁻¹ᵁ V
abbrev stkX (X : Sch) (x : ↥X) := X.presheaf.stalk x
abbrev pGerm (X : Sch) := X.presheaf.germ
abbrev pObj (X : Sch) := X.presheaf.obj
abbrev affO (X : Sch) := X.affineOpens
abbrev bsM {X Y : Sch} (f : X ⟶ Y) := f.base
abbrev isoH {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) := e.hom
abbrev isoI {C : Type*} [Category C] {X Y : C} (e : X ≅ Y) := e.inv
abbrev ihB_ {X Y : Sch} (e : X ≅ Y) := e.hom.base
abbrev ibM {X Y : Sch} (e : X ≅ Y) := e.inv.base
abbrev kCm {X Y Z : Sch} (f : X ⟶ Y) (g : Z ⟶ Y) := f.ker.comap g
abbrev sy_ {α : Sort*} {a b : α} (h : a = b) := h.symm
abbrev tr_ {α : Sort*} {a b c : α} (h1 : a = b) (h2 : b = c) := h1.trans h2
abbrev st_ {α : Sort*} {a b c : α} (h1 : b = a) (h2 : b = c) := h1.symm.trans h2
abbrev lenL {α : Type*} (L : List α) := L.length
abbrev an1 {a b : Prop} (h : a ∧ b) := h.1
abbrev an2 {a b : Prop} (h : a ∧ b) := h.2
abbrev mp_ {a b : Prop} (h : a ↔ b) := h.mp
abbrev mpr_ {a b : Prop} (h : a ↔ b) := h.mpr
abbrev m4 := @CommRingCat.Hom.hom
abbrev m5 := @Ideal.Quotient.mk
abbrev m6 := @Ideal.map
abbrev m7 := @MvPolynomial.X
abbrev m8 := @MvPolynomial.C
abbrev m9 := @AffineSpace.coord
abbrev m10 := @CommRingCat.of
abbrev m12 := @Spec.map
abbrev m13 := @KaehlerDifferential.D
abbrev m14 := @IsLocalRing.ResidueField
abbrev m15 := @Set.Subset.antisymm
abbrev m16 := @IsLocalRing.maximalIdeal
abbrev m17 := @Ideal.span
abbrev m19 := @Scheme.IdealSheafData.support_comap
abbrev m22 := @Iff.rfl
abbrev m23 := @ConcreteCategory.hom
abbrev m26 := @Subtype.ext
abbrev m29 := @Scheme.IdealSheafData.ext
abbrev m30 := @Set.range
abbrev m32 := @Eq.trans
abbrev m39 := @List.map
abbrev m41 := @RingHom.ker
abbrev m43 := @IsOpenImmersion.lift
abbrev m44 := @Sum.inl
abbrev m45 := @MvPolynomial.map
abbrev m46 := @AffineSpace.hom_ext
abbrev m47 := @Limits.pullback.snd
abbrev m48 := @RingHom.ext
abbrev m49 := @Nat.le_of_lt
abbrev m50 := @Sum.inr
abbrev m51 := @Or.inl
abbrev m52 := @AffineSpace.homOfVector
abbrev m53 := @Matrix.of
abbrev m54 := @TopologicalSpace.Opens.map
abbrev m55 := @TopologicalSpace.Opens.ext
abbrev m56 := @Scheme.IdealSheafData.comap_comp
abbrev m57 := @Limits.pullback.fst
abbrev m60 := @Submodule.add_mem
abbrev m61 := @Or.inr
abbrev m63 := @Nat.lt_or_ge
abbrev m64 := @IsClosedImmersion.lift
abbrev m65 := @Finset.range
abbrev m67 := @Nat.zero_le
abbrev m69 := @AffineSpace.SpecIso
abbrev m72 := @Submodule.span
abbrev m73 := @Nat.eq_zero_or_pos
abbrev m74 := @CategoryStruct.id
abbrev m75 := @List.map_cons
abbrev m78 := @CommRingCat.comp_apply
abbrev m82 := @RingHom.comp_apply
abbrev m83 := @CategoryTheory.inv
abbrev m86 := @TopologicalSpace.NoetherianSpace
abbrev m87 := @AffineSpace.homOfVector_appTop_coord
abbrev m90 := @Set.Subset.trans
abbrev m91 := @Scheme.Hom.appLE_comp_appLE
abbrev m97 := @Submodule.zero_mem
abbrev m98 := @MorphismProperty.of_isPullback
abbrev m99 := @RingHom.id
abbrev m100 := @Ideal.subset_span
abbrev m105 := @Option.some.inj
abbrev m107 := @Limits.pullback.lift
abbrev m108 := @Ideal.Quotient.mk_surjective
abbrev m111 := @Subsingleton.elim
abbrev m112 := @Opposite.op
abbrev m113 := @Ne.symm
abbrev m114 := @Iso.inv_hom_id
abbrev m115 := @IsOpenImmersion.lift_fac
abbrev m116 := @Function.comp_apply
abbrev m117 := @IsIso.inv_hom_id
abbrev m118 := @IsIso.hom_inv_id
abbrev m119 := @Ideal.comap
abbrev m120 := @Function.Injective
abbrev m121 := @Algebra.Etale
abbrev m122 := @MorphismProperty.IsStableUnderBaseChange.of_isPullback
abbrev m127 := @List.range
abbrev m128 := @Ideal.add_mem
abbrev m129 := @HEq.rfl
abbrev m130 := @Nat.sub_zero
abbrev m131 := @Limits.pullback
abbrev m132 := @KaehlerDifferential.map
abbrev m133 := @Ideal.sum_mem
abbrev m134 := @TopologicalSpace.Closeds.ext
abbrev m135 := @Scheme.Hom.comp_apply
abbrev m139 := @Algebra.FormallySmooth.comp
abbrev m140 := @QuasiSober.sober
abbrev m141 := @Polynomial.C
abbrev m142 := @Set.preimage
abbrev m144 := @List.map_append
abbrev m145 := @Iso.hom_inv_id
abbrev m146 := @Category.assoc
abbrev m149 := @Scheme.Hom.ker
abbrev m154 := @IsClosedImmersion.lift_fac
abbrev m156 := @DFunLike.congr_fun
abbrev m157 := @And.intro
abbrev m158 := @AlgebraicGeometry.SmoothOfRelativeDimension
abbrev m159 := @AffineSpace.reindex
abbrev m161 := @Subtype.val
abbrev m162 := @Submodule.sub_mem
abbrev m163 := @Set.mem_preimage
abbrev m164 := @Nat.le_refl
abbrev m165 := @MvPolynomial.aeval
abbrev m166 := @Ideal.map_top
abbrev m167 := @Ideal.map_id
abbrev m169 := @TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
abbrev m170 := @Scheme.IdealSheafData.ext_of_isAffine
abbrev m175 := @Submonoid.subset_closure
abbrev m176 := @Nat.one_pos
abbrev m177 := @LinearMap.ker
abbrev m178 := @Finset.induction_on
abbrev m179 := @AffineSpace.homOfVector_over
abbrev m182 := @TopologicalSpace.Closeds
abbrev m183 := @Spec.map_comp
abbrev m184 := @PrimeSpectrum.vanishingIdeal
abbrev m185 := @MvPolynomial.algebraMap_eq
abbrev m186 := @IsPullback.of_hasPullback
abbrev m187 := @IsNoetherian.noetherian
abbrev m188 := @IsLocallyNoetherian.component_noetherian
abbrev m189 := @ConcreteCategory.bijective_of_isIso
abbrev m190 := @Bool.rec
abbrev m197 := @Set.Finite.subset
abbrev m198 := @Scheme.Pullback.exists_preimage_pullback
abbrev m201 := @Ideal.Quotient.lift
abbrev m202 := @Ideal.Quotient.eq
abbrev m203 := @Ideal.Quotient.algebraMap_eq
abbrev m207 := @Scheme.homeoOfIso
abbrev m208 := @RingHom.mem_ker
abbrev m209 := @PrimeSpectrum.mem_basicOpen
abbrev m210 := @PrimeSpectrum.ext
abbrev m212 := @Nat.le_of_succ_le
abbrev m213 := @Iso.inv_hom_id_assoc
abbrev m215 := @IsLocalization.Away
abbrev m216 := @Ideal.zero_mem
abbrev m217 := @Ideal.one_eq_top
abbrev m218 := @Ideal.map_span
abbrev m219 := @Ideal.map_pow
abbrev m220 := @Ideal.map_mul
abbrev m222 := @Functor.map_comp
abbrev m223 := @Fin.cons
abbrev m225 := @CommRingCat.hom_comp
abbrev m226 := @AlgebraicGeometry.isPullback_morphismRestrict
abbrev m227 := @AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
abbrev m228 := @AffineSpace.map
-- END_E2_B00_ABBREVS
-- BEGIN_F2_B00_ABBREVS
abbrev spI {X : Sch} (I : X.IdealSheafData) := I.support
abbrev oSch {X : Sch} (U : X.Opens) := U.toScheme
abbrev pMap (X : Sch) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ} (f : U ⟶ V) := X.presheaf.map f
abbrev hAT {X Y : Sch} (f : X ⟶ Y) := f.appTop
abbrev pr1 {α β : Type*} (p : α × β) := p.1
abbrev pr2 {α β : Type*} (p : α × β) := p.2
abbrev ltLe {α : Type*} [Preorder α] {a b : α} (h : a < b) := h.le
abbrev imS {α β : Type*} (f : α → β) (s : Set α) := f '' s
abbrev RH (R S : Type*) [Semiring R] [Semiring S] := R →+* S
abbrev q1 := @Scheme.Opens.range_ι
abbrev q2 := @Scheme.IdealSheafData.ker_subschemeι
abbrev q3 := @MvPolynomial.eval
abbrev q4 := @Scheme.Hom.resLE_comp_ι
abbrev q5 := @Scheme.IdealSheafData.range_subschemeι
abbrev q6 := @Set.mem_iUnion
abbrev q7 := @Limits.PullbackCone.fst
abbrev q8 := @Limits.Sigma.desc
abbrev q9 := @Set.disjoint_left
abbrev q10 := @AlgebraicGeometry.Surjective
-- END_F2_B00_ABBREVS
open Ideal (eq_top_iff_one exists_minimalPrimes_le iInf_pow_eq_bot_of_isLocalRing map_le_iff_le_comap map_map map_mono map_span mem_bot mem_comap mem_map_iff_of_surjective mem_map_of_mem mem_span_singleton mem_span_singleton' mem_span_singleton_mul mem_span_singleton_self mk_ker mul_le mul_le_inf mul_le_left mul_le_right mul_mem_left mul_mem_mul mul_mem_right mul_mono mul_mono_right one_eq_top pow_le_pow_right pow_le_self pow_mem_pow pow_right_mono radical_mono span_eq span_le span_singleton_eq_top span_singleton_le_iff_mem subset_union_prime toCotangent toCotangent_eq toCotangent_eq_zero toCotangent_surjective unit_mul_mem_iff_mem)
open Finset (Ico add_sum_erase card_erase_of_mem card_image_le card_pos card_range coe_image dvd_prod_of_mem eq_singleton_iff_unique_mem exists_min_image finite_toSet mem_Ico mem_compl mem_erase mem_filter mem_insert mem_insert_of_mem mem_insert_self mem_of_mem_erase mem_product mem_range mem_univ mul_prod_erase mul_sum ne_of_mem_erase prod prod_congr prod_empty prod_eq_single prod_insert prod_mul_distrib prod_ne_zero_iff prod_range_succ range range_eq_Ico range_zero single_le_sum smul_sum sum_Ico_consecutive sum_Ico_eq_sum_range sum_Ico_succ_top sum_add_distrib sum_comm sum_congr sum_const sum_eq_single sum_eq_single_of_mem sum_eq_zero sum_equiv sum_erase_eq_sub sum_filter_add_sum_filter_not sum_le_sum sum_mul sum_pair sum_product' sum_range_succ sum_range_succ' sum_singleton sum_subset univ)
open Nat (add_comm add_le_add_right add_mul_mod_self_right add_sub_cancel' cast_add cast_mul cast_ne_zero cast_one choose_eq_zero_of_lt choose_mul_factorial_mul_factorial choose_pos choose_succ_succ choose_zero_right exists_eq_add_of_le exists_eq_succ_of_ne_zero factorial_pos le_add_right le_of_succ_le le_sub_one_of_lt lt_succ_iff lt_succ_of_lt lt_succ_self mod_eq_of_lt mul_le_mul not_lt_zero not_succ_le_zero one_le_iff_ne_zero sub_add_cancel sub_le sub_ne_zero_of_lt sub_pos_of_lt succ_add succ_pos succ_pred_eq_of_pos zero_le)
open Submodule (eq_bot_of_le_smul_of_le_jacobson_bot eq_bot_of_subsingleton eq_top_iff' fg_span iSup_eq_span iSup_induction iSup_mul le_of_le_smul_of_le_jacobson_bot map_subtype_top mem_iInf mem_inf mem_span_finset mem_span_range_iff_exists_fun mem_sup mem_sup_left mem_sup_right mem_top mul_iSup mul_induction_on smul_mem spanFinrank spanRank_span_le_card span_induction span_insert_zero subset_span subtype_apply)
open Set (disjoint_left eq_empty_iff_forall_notMem image_image image_insert_eq image_singleton image_univ inter_subset_left mem_compl_iff mem_iUnion mem_range_self mem_sUnion_of_mem mem_sdiff_of_mem mem_singleton mem_singleton_iff mem_union_left mem_union_right sUnion_eq_biUnion sdiff_subset singleton_subset_iff)
open LinearMap (coe_restrictScalars compDer exists_extend extendScalarsOfIsLocalization ker_eq_bot ker_eq_bot' liftBaseChange liftBaseChange_tmul mem_ker mulLeft)
open ENat (eq_top_iff_forall_ge forall_natCast_le_iff_le ne_top_iff_exists recTopCoe)
open List (getElem_cons_succ getElem_cons_zero prod_append prod_cons range_succ)
open IsPullback (of_bot of_hasPullback of_horiz_isIso of_isLimit' of_iso_pullback)
open Fin (cons_succ cons_zero foldr foldr_succ foldr_zero pos prod_univ_succ succ_injective succ_ne_zero sum_univ_succ val_succ)
open Matrix (det_neg det_one nonsing_inv_mul one_apply)
open Algebra (Extension FormallyEtale FormallySmooth FormallyUnramified Generators H1Cotangent PreSubmersivePresentation Presentation SubmersivePresentation algebra_ext linearMap linearMap_apply ofId smul_def)
open Algebra.PreSubmersivePresentation (comp_jacobian_eq_jacobian_smul_jacobian jacobiMatrix_apply jacobian_eq_jacobiMatrix_det)
open IsLocalRing (jacobson_eq_maximalIdeal le_maximalIdeal maximalIdeal_le_jacobson mem_maximalIdeal notMem_maximalIdeal of_surjective' residue residue_eq_zero_iff residue_surjective ringJacobson_eq_maximalIdeal spanFinrank_maximalIdeal_eq_finrank_cotangentSpace span_eq_top_of_tmul_eq_basis)
open Units (inv_mul mk0)
open Finsupp (lapply lapply_apply single_apply single_eq_same)
open IsClosedImmersion (isIso_iff_ker_eq_bot of_isPreimmersion)
open RingHom (IsStandardSmooth IsStandardSmoothOfRelativeDimension coe_comp id_apply isStandardSmoothOfRelativeDimension_holdsForLocalizationAway isStandardSmoothOfRelativeDimension_localizationPreserves kerLift kerLift_injective mapMatrix_apply map_det toAlgebra)
open IsLocalization (algEquiv algebraMap_mem_map_algebraMap_iff eq_iff_exists lift_eq map_units mem_map_algebraMap_iff surj)
open AlgEquiv (ofBijective ofRingEquiv)
open MvPolynomial (aeval_C aeval_X algebraTensorAlgEquiv induction_on map_C map_X pderiv pderiv_C pderiv_map renameEquiv ringHom_ext)
open Scheme (GSpecIso homeoOfIso isoSpec_hom preimage_basicOpen range_fromSpecStalk)
open Function (Bijective Injective Surjective comp_apply iterate_add_apply iterate_fixed iterate_succ_apply iterate_succ_apply' iterate_zero_apply surjInv surjInv_eq)
open TensorProduct (inductionOn smul_tmul smul_tmul' tmul_add tmul_sub tmul_sum tmul_zero zero_tmul)
open Fintype (card card_congr card_fin card_sum equivFin equivFinOfCardEq linearIndependent_iff mem_piFinset piFinset sum_sum_type)
open Submonoid (mem_powers mul_mem powers prod_mem)
open Ideal.Quotient (eq_zero_iff_mem isDomain_iff_prime mk_surjective)
open Scheme.Hom (app appIso_hom' appLE appLE_map comp_appTop ker map_appLE opensRange resLE_appLE support_ker)
open Module (Basis End FinitePresentation finBasis finrank finrank_eq_card_basis)
open Module.Basis (det_apply linearIndependent map_apply mk_apply reindex_apply repr_self repr_sum_self sum_repr toMatrix_apply)
open Derivation (leibniz leibniz_pow liftKaehlerDifferential_comp_D map_algebraMap mk')
open Scheme.IdealSheafData (le_radical subschemeObjIso support_comap support_eq_bot_iff support_eq_top_iff support_radical vanishingIdeal vanishingIdeal_support)
open IsScalarTower (algebraMap_apply of_algebraMap_eq toAlgHom)
open KaehlerDifferential (exact_mapBaseChange_map isBaseChange_of_formallyEtale mapBaseChange mapBaseChange_tmul map_D mvPolynomialBasis mvPolynomialBasis_apply span_range_derivation)
open Category (assoc comp_id id_comp)
open Equiv (apply_symm_apply refl sumComm sumCompl sumCongr)
open Algebra.TensorProduct (basis basis_apply comm)
open Localization (Away)
open Opposite (op)
open Algebra.FormallyEtale (comp of_isLocalization)
open CommRingCat (hom_comp hom_id ofHom)
open IsLocalRing.ResidueField (algebraMap_eq)
open Limits.Sigma (desc)
open Discrete (functor natTrans)
open Set.Finite (image subset)
open Pi (single)
open Algebra.FormallySmooth (comp_liftOfSurjective liftOfSurjective subsingleton_h1Cotangent)
open Module.Free (chooseBasis)
open DFunLike (congr_fun)
open IsLocalRing.maximalIdeal (isMaximal)
open ULift (up)
open IsNoetherian (noetherian)
open Sum (elim)
open SetLike (mem_coe)
open Ne (symm)
section
noncomputable def UpperTheory.Reformulated.B.SaturationByPowers.saturationByPowers.{u_1} :
    {A : Type u_1} → [inst : CommRing A] → Ideal A → A → Ideal A :=
  fun {A} _ J a =>
    { carrier := {x : A | ∃ n : ℕ, a ^ n * x ∈ J}
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : a ^ (m + n) * (x + y) = a ^ n * (a ^ m * x) + a ^ m * (a ^ n * y) := by ring
        rw [h]
        exact J.add_mem (J.mul_mem_left _ hm) $ J.mul_mem_left _ hn
      zero_mem' := ⟨0, by rw [mul_zero]; exact J.zero_mem⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : a ^ n * (c • x) = c * (a ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact J.mul_mem_left _ hn }
end
section

namespace FunctorialResolution.EmbeddedResolution

instance instJacobsonSpaceAffineSpace (k : Type) [Field k] (n : Type) [Finite n] :
    JacobsonSpace $ AffineSpace n $ Sp k :=
  (JacobsonSpace.of_isClosedEmbedding
    (homeoOfIso $ m69 n $ m10 k).isClosedEmbedding)

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace AlgebraicGeometry.Scheme.Opens

theorem isClosedImmersion_ι_of_isClosed {X : Sch} (U : Opn X)
    (hU : IsClosed (U : Set X)) : IsClosedImmersion U.i :=
  of_isPreimmersion U.i (by rw [U.range_ι]; exact hU)

end AlgebraicGeometry.Scheme.Opens

namespace FunctorialResolution.EmbeddedResolution

section
variable {X : Sch}
section
variable [IsReduced X] (C : Opn X)
theorem exists_iso_subscheme_vanishingIdeal_of_coe_eq (Z : Closeds X) (hZ : (Z : Set X) = (C : Set X)) :
    ∃ e : (vanishingIdeal Z).subscheme ≅ C.toScheme,
      e.hom ≫ C.i = (vanishingIdeal Z).si := by
  have hCclosed : IsClosed (C : Set X) := by rw [← hZ]
                                             exact Z.2
  have :=
    of_isPreimmersion C.i (by rw [C.range_ι]; exact hCclosed)
  have hkersupp := sy_ hZ
  rw [← hCclosed.closure_eq, ← C.range_ι, ← support_ker] at hkersupp
  have hZsupp := m134 hkersupp
  have hvan : vanishingIdeal Z = (ker C.i).radical := by
    rw [← hZsupp]
    exact vanishingIdeal_support
  have hsupp := hZsupp
  rw [← support_radical, ← hvan] at hsupp
  have hrange := hZ
  rw [← hsupp, ← q5] at hrange
  have hle : ker C.i ≤
      ker (vanishingIdeal Z).si := by
    rw [q2, hvan]
    exact le_radical _
  let ph_ : (vanishingIdeal Z).subscheme ⟶ C.toScheme :=
    m64 C.i (vanishingIdeal Z).si hle
  have hph : ph_ ≫ C.i = (vanishingIdeal Z).si :=
    m154 _ _ hle
  have hphbase : ∀ x, ⇑C.i (⇑ph_ x) =
      ⇑(vanishingIdeal Z).si x := by
    intro x
    rw [← hph]
    simp
  have hsurj : Surjective ⇑ph_ := by
    intro y
    have hy : ⇑C.i y ∈ Set.range ⇑(vanishingIdeal Z).si := by
      rw [hrange, ← C.range_ι]
      exact mem_range_self y
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, C.ι.isOpenEmbedding.injective ?_⟩
    rwa [hphbase x]
  have : IsPreimmersion $ ph_ ≫ C.i := by rw [hph]
                                          infer_instance
  have := IsPreimmersion.of_comp ph_ C.i
  have :=
    of_isPreimmersion ph_ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have hker : ker ph_ = ⊥ := by
    rw [← support_eq_top_iff]
    refine m134 ?_
    rw [support_ker, hsurj.range_eq, closure_univ]
    simp
  have := mpr_ isIso_iff_ker_eq_bot hker
  exact ⟨asIso ph_, hph⟩

theorem exists_iso_subscheme_vanishingIdeal_of_isClosed (hC : IsClosed (C : Set X)) :
    ∃ e : (vanishingIdeal
        (⟨C, hC⟩ : m182 X)).subscheme ≅ C.toScheme,
      e.hom ≫ C.i =
        (vanishingIdeal
          (⟨(C : Set X), hC⟩ : m182 X)).subschemeι :=
  exists_iso_subscheme_vanishingIdeal_of_coe_eq C _ rfl
end

section
variable (C) (hC : IsClosed (C : Set X))
def complOpensOfIsClosed : Opn X :=
  ⟨(C : Set X)ᶜ, hC.isOpen_compl⟩

@[simp]
theorem coe_complOpensOfIsClosed :
    ((complOpensOfIsClosed C hC : Opn X) : Set X) = (C : Set X)ᶜ := rfl
end
end

end FunctorialResolution.EmbeddedResolution
end
section
open CategoryTheory.Limits


namespace FunctorialResolution.EmbeddedResolution

section
variable {ι : Type} [Finite ι]
theorem isIso_sigmaDesc_of_isPullback {P : Sch}
    (B C : ι → Sch) (f : P ⟶ ∐ B) (j : ∀ a, C a ⟶ B a) (u : ∀ a, C a ⟶ P)
    (hsq : ∀ a, IsPullback (u a) (j a) f $ Sigma.ι B a) : IsIso $ desc u := by
  let _a0 := colimit.cocone $ functor B
  let _a2 := Cofan.mk P u
  have e1 : (natTrans (F := functor C) (G := functor B)
        fun a => j a.as) ≫ _a0.ι
      = _a2.ι ≫ (Functor.const $ Discrete ι).map f := by
    apply NatTrans.ext
    funext x
    obtain ⟨a⟩ := x
    exact sy_ $ (hsq a).w
  have hpb : ∀ x, IsPullback (_a2.ι.app x)
      ((natTrans (F := functor C) (G := functor B)
        fun a => j a.as).app x) f $ _a0.ι.app x := by
    rintro ⟨a⟩
    exact hsq a
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (colimit.isColimit $ functor B) _a2
      (natTrans (F := functor C) (G := functor B) fun a => j a.as)
      f e1 (NatTrans.Equifibered.of_discrete _) hpb
  let _a1 := colimit.isColimit $ functor C
  have key : desc u
      = isoH (IsColimit.coconePointUniqueUpToIso _a1 hc') := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_desc]
    exact sy_ $ IsColimit.comp_coconePointUniqueUpToIso_hom
      _a1 hc' ⟨a⟩
  rw [key]
  infer_instance

theorem isPullback_sigmaMap_sigmaDesc {A Y : Sch} (i : Y ⟶ A)
    (B C : ι → Sch) (j : ∀ a, C a ⟶ B a) (q : ∀ a, C a ⟶ Y) (h : ∀ a, B a ⟶ A)
    (hsq : ∀ a, IsPullback (j a) (q a) (h a) i) :
    IsPullback (Limits.Sigma.map j) (desc q) (desc h) i := by
  have hcomm : ∀ a, (j a ≫ Sigma.ι B a) ≫ desc h = q a ≫ i := by
    intro a
    rw [assoc, Sigma.ι_desc]
    exact (hsq a).w
  obtain ⟨u, hufst, husnd⟩ : ∃ u : ∀ a, C a ⟶ pullback (desc h) i,
      (∀ a, u a ≫ pullback.fst (desc h) i = j a ≫ Sigma.ι B a) ∧
        (∀ a, u a ≫ pullback.snd (desc h) i = q a) :=
    ⟨fun a => pullback.lift (j a ≫ Sigma.ι B a) (q a) $ hcomm a,
      fun a => pullback.lift_fst _ _ _, fun a => pullback.lift_snd _ _ _⟩
  have hsq2 : ∀ a, IsPullback (j a) (u a) (Sigma.ι B a) $ pullback.fst (desc h) i := by
    intro a
    refine of_bot ?_ (hufst a).symm $ of_hasPullback _ _
    rw [husnd a, Sigma.ι_desc]
    exact hsq a
  have :=
    isIso_sigmaDesc_of_isPullback B C (pullback.fst (desc h) i) j u
      (fun a => (hsq2 a).flip)
  have hcs : CommSq (Limits.Sigma.map j) (desc q) (desc h) i := by
    constructor
    apply Sigma.hom_ext
    intro a
    simp [(hsq a).w]
  refine of_iso_pullback hcs (asIso $ desc u) ?_ ?_
  apply Sigma.hom_ext
  intro a
  simp [hufst a]
  apply Sigma.hom_ext
  intro a
  simp [husnd a]
end


section
variable (X1 X2 : Sch)
def boolFamily : ULift Bool → Sch :=
  fun i => cond i.down X1 X2

noncomputable def sigmaBoolFamilyInl : X1 ⟶ ∐ boolFamily X1 X2 :=
  Limits.Sigma.ι (boolFamily X1 X2) ⟨true⟩

noncomputable def sigmaBoolFamilyInr : X2 ⟶ ∐ boolFamily X1 X2 :=
  Limits.Sigma.ι (boolFamily X1 X2) ⟨false⟩
end

noncomputable def isoCoprodInitial (P : Sch) : P ≅ P ⨿ (⊥_ Sch) where
  hom := coprod.inl
  inv := coprod.desc (𝟙 P) $ initial.to P
  hom_inv_id := coprod.inl_desc (𝟙 P) $ initial.to P
  inv_hom_id := by
    apply coprod.hom_ext
    · rw [← assoc, coprod.inl_desc, id_comp, comp_id]
    · exact initial.hom_ext _ _

theorem coprodInitialIsoRight_hom (P : Sch) :
    (isoCoprodInitial P).hom = (coprod.inl : P ⟶ P ⨿ (⊥_ Sch)) := rfl


theorem isPullback_of_isPullback_of_iso {P X Y Z P' X' : Sch}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {fst' : P' ⟶ X'} {snd' : P' ⟶ Y} {f' : X' ⟶ Z}
    (h : IsPullback fst snd f g) (eP : P' ≅ P) (eX : X' ≅ X)
    (h1 : fst' ≫ eX.hom = eP.hom ≫ fst) (h2 : eX.hom ≫ f = f')
    (h3 : eP.hom ≫ snd = snd') : IsPullback fst' snd' f' g := by
  have sq2 : CommSq eX.inv f f' $ 𝟙 Z := by
    refine ⟨?_⟩
    rw [← h2, m213, comp_id]
  have sq1 : CommSq eP.hom (isoH eP ≫ snd) snd $ 𝟙 Y := by simp_all
  have hfst : fst' = isoH eP ≫ fst ≫ isoI eX := by
    rw [← assoc, ← h1, assoc, m145, comp_id]
  rw [hfst, ← h3]
  simpa using ((of_horiz_isIso sq1).paste_horiz $ h.paste_horiz $ of_horiz_isIso sq2)

theorem sigmaPair_hom_ext {X1 X2 Z : Sch} (f g : (∐ boolFamily X1 X2) ⟶ Z)
    (ht : sigmaBoolFamilyInl X1 X2 ≫ f = sigmaBoolFamilyInl X1 X2 ≫ g)
    (hf : sigmaBoolFamilyInr X1 X2 ≫ f = sigmaBoolFamilyInr X1 X2 ≫ g) : f = g := by
  apply Limits.Sigma.hom_ext
  rintro ⟨_ | _⟩
  exact hf
  exact ht

noncomputable def isInitialOfIsEmptyScheme {X : Sch} (h : IsEmpty X) : IsInitial X := by
  haveI := h
  exact isInitialOfIsEmpty

theorem isPullback_initial_of_isEmpty {X Y Y' : Sch} (f : X ⟶ Y) (u : Y' ⟶ Y)
    (h : ∀ (P : Sch) (a : P ⟶ X) (b : P ⟶ Y'), a ≫ f = b ≫ u → IsEmpty P) :
    IsPullback (initial.to X) (initial.to Y') f u := by
  refine of_isLimit' ⟨initial.hom_ext _ _⟩ $ PullbackCone.isLimitAux' _ fun s => ?_
  have hinit := isInitialOfIsEmptyScheme $ h s.pt s.fst s.snd s.condition
  refine ⟨hinit.to _, hinit.hom_ext _ _, hinit.hom_ext _ _, ?_⟩
  intro m _ _
  exact hinit.hom_ext _ _

def boolFamilyMap {X1 X2 Y1 Y2 : Sch} (f1_ : X1 ⟶ Y1) (f2_ : X2 ⟶ Y2) :
    ∀ i, boolFamily X1 X2 i ⟶ boolFamily Y1 Y2 i
  | ⟨true⟩ => f1_
  | ⟨false⟩ => f2_

def boolFamilyDesc {X1 X2 Y : Sch} (f1_ : X1 ⟶ Y) (f2_ : X2 ⟶ Y) :
    ∀ i, boolFamily X1 X2 i ⟶ Y
  | ⟨true⟩ => f1_
  | ⟨false⟩ => f2_

section
variable {X1 X2 Y : Sch} (f1_ : X1 ⟶ Y) (f2_ : X2 ⟶ Y)
theorem pairInl_comp_desc :
    sigmaBoolFamilyInl X1 X2 ≫ desc (boolFamilyDesc f1_ f2_) = f1_ :=
  Limits.Sigma.ι_desc (boolFamilyDesc f1_ f2_) ⟨true⟩

theorem pairInr_comp_desc :
    sigmaBoolFamilyInr X1 X2 ≫ desc (boolFamilyDesc f1_ f2_) = f2_ :=
  Limits.Sigma.ι_desc (boolFamilyDesc f1_ f2_) ⟨false⟩
end

section
variable {X1 X2 P1 P2 : Sch} (a1_ : P1 ⟶ X1) (a2_ : P2 ⟶ X2)
theorem pairInl_comp_map :
    sigmaBoolFamilyInl P1 P2 ≫ Limits.Sigma.map (boolFamilyMap a1_ a2_) = a1_ ≫ sigmaBoolFamilyInl X1 X2 :=
  Limits.Sigma.ι_map (boolFamilyMap a1_ a2_) ⟨true⟩

theorem pairInr_comp_map :
    sigmaBoolFamilyInr P1 P2 ≫ Limits.Sigma.map (boolFamilyMap a1_ a2_) = a2_ ≫ sigmaBoolFamilyInr X1 X2 :=
  Limits.Sigma.ι_map (boolFamilyMap a1_ a2_) ⟨false⟩
end

noncomputable def coprodIsoSigmaBoolFamily (X1 X2 : Sch) : (X1 ⨿ X2) ≅ ∐ boolFamily X1 X2 where
  hom := coprod.desc (sigmaBoolFamilyInl X1 X2) $ sigmaBoolFamilyInr X1 X2
  inv := desc $ boolFamilyDesc (coprod.inl : X1 ⟶ X1 ⨿ X2) (coprod.inr : X2 ⟶ X1 ⨿ X2)
  hom_inv_id := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, pairInl_comp_desc, comp_id]
    · rw [coprod.inr_desc_assoc, pairInr_comp_desc, comp_id]
  inv_hom_id := by
    apply sigmaPair_hom_ext
    · rw [← assoc, pairInl_comp_desc, coprod.inl_desc, comp_id]
    · rw [← assoc, pairInr_comp_desc, coprod.inr_desc, comp_id]

theorem pairCoprodIso_hom (X1 X2 : Sch) :
    (coprodIsoSigmaBoolFamily X1 X2).hom = coprod.desc (sigmaBoolFamilyInl X1 X2) (sigmaBoolFamilyInr X1 X2) := rfl

theorem isPullback_coprodMap_coprodDesc {X1 X2 P1 P2 Y Y' : Sch}
    (a1_ : P1 ⟶ X1) (a2_ : P2 ⟶ X2) (b1_ : P1 ⟶ Y') (b2_ : P2 ⟶ Y')
    (f1_ : X1 ⟶ Y) (f2_ : X2 ⟶ Y) (u : Y' ⟶ Y)
    (h1_ : IsPullback a1_ b1_ f1_ u) (h2_ : IsPullback a2_ b2_ f2_ u) :
    IsPullback (coprod.map a1_ a2_) (coprod.desc b1_ b2_) (coprod.desc f1_ f2_) u := by
  have hsq : ∀ i,
      IsPullback (boolFamilyMap a1_ a2_ i) (boolFamilyDesc b1_ b2_ i) (boolFamilyDesc f1_ f2_ i) u := by
    rintro ⟨_ | _⟩
    exact h2_
    exact h1_
  have key := isPullback_sigmaMap_sigmaDesc u (boolFamily X1 X2) (boolFamily P1 P2)
      (boolFamilyMap a1_ a2_) (boolFamilyDesc b1_ b2_) (boolFamilyDesc f1_ f2_) hsq
  have E1 : coprod.map a1_ a2_ ≫ isoH (coprodIsoSigmaBoolFamily X1 X2)
      = isoH (coprodIsoSigmaBoolFamily P1 P2) ≫ Limits.Sigma.map (boolFamilyMap a1_ a2_) := by
    simp only [pairCoprodIso_hom]
    apply coprod.hom_ext
    rw [coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc, pairInl_comp_map]
    rw [coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc, pairInr_comp_map]
  have E2 : isoH (coprodIsoSigmaBoolFamily X1 X2) ≫ desc (boolFamilyDesc f1_ f2_)
      = coprod.desc f1_ f2_ := by
    simp only [pairCoprodIso_hom]
    apply coprod.hom_ext
    rw [coprod.inl_desc_assoc, pairInl_comp_desc, coprod.inl_desc]
    rw [coprod.inr_desc_assoc, pairInr_comp_desc, coprod.inr_desc]
  refine isPullback_of_isPullback_of_iso key (coprodIsoSigmaBoolFamily P1 P2) (coprodIsoSigmaBoolFamily X1 X2) E1 E2 ?_
  simp only [pairCoprodIso_hom]
  apply coprod.hom_ext
  rw [coprod.inl_desc_assoc, pairInl_comp_desc, coprod.inl_desc]
  rw [coprod.inr_desc_assoc, pairInr_comp_desc, coprod.inr_desc]

theorem isPullback_comp_inl_coprodDesc {P X Y Y' F : Sch}
    (a : P ⟶ X) (b : P ⟶ Y') (q : X ⟶ Y) (u : Y' ⟶ Y) (r : F ⟶ Y)
    (hsq : IsPullback a b q u)
    (hF : ∀ (Q : Sch) (c : Q ⟶ F) (d : Q ⟶ Y'), c ≫ r = d ≫ u → IsEmpty Q) :
    IsPullback (a ≫ coprod.inl) b (coprod.desc q r) u := by
  let _a0 := Iso.refl $ X ⨿ F
  have E1 : (a ≫ coprod.inl) ≫ _a0.hom
      = (isoCoprodInitial P).hom ≫ coprod.map a (initial.to F) := by
    rw [Iso.refl_hom, comp_id, coprodInitialIsoRight_hom, coprod.inl_map]
  have E2 : _a0.hom ≫ coprod.desc q r = coprod.desc q r := by
    rw [Iso.refl_hom, id_comp]
  refine isPullback_of_isPullback_of_iso (isPullback_coprodMap_coprodDesc a (initial.to F) b (initial.to Y') q r u hsq $ isPullback_initial_of_isEmpty r u hF) (isoCoprodInitial P) _a0 E1 E2 ?_
  rw [coprodInitialIsoRight_hom, coprod.inl_desc]

end FunctorialResolution.EmbeddedResolution
end
section
variable {R : Type} {S : Type} {S' : Type} {N : Type}
variable [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup N]
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [Module R N] [Module S N] [Module S' N]
variable [IsScalarTower R S N] [IsScalarTower S S' N] [IsScalarTower R S' N]

namespace Derivation

section
variable (M : Submonoid S) [hv0_1 : IsLocalization M S']
include hv0_1
theorem isUnit_algebraMap_moduleEnd (y : M) :
    IsUnit $ (algebraMap S $ End S N) (y : S) := by
  obtain ⟨u, hu⟩ := map_units (M := M) S' y
  have hcomm : ∀ (s : S) (c : S') (n : N), c • s • n = s • c • n := by
    intro s c n
    rw [← IsScalarTower.algebraMap_smul S' s n, ← IsScalarTower.algebraMap_smul S' s $ c • n,
      smul_smul, smul_smul, mul_comm]
  let _s0 := ((u⁻¹ : S'ˣ) : S')
  have h1 : ∀ n : N, (y : S) • (_s0 • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) $ _s0 • n, ← hu, smul_smul,
      u.mul_inv, one_smul]
  have h2 : ∀ n : N, _s0 • ((y : S) • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) n, ← hu, smul_smul, u.inv_mul, one_smul]
  exact ⟨⟨(algebraMap S $ End S N) (y : S),
    { toFun := fun n => _s0 • n
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun s n => hcomm s _s0 n },
    LinearMap.ext h1, LinearMap.ext h2⟩, rfl⟩

section
variable [FinitePresentation S (KaehlerDifferential R S)]
theorem exists_derivation_mul_eq_of_isLocalization (D : Derivation R S' S') :
    ∃ (m : M) (D0_ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D0_ s) := by
  obtain ⟨m, D0_, h⟩ : ∃ (m : M) (D0_ : Derivation R S S), ∀ s : S, algebraMap S S' (m : S) * (D.compAlgebraMap S) s = algebraMap S S' (D0_ s) := by
    let D := D.compAlgebraMap S
    obtain ⟨ps_, m, hps_⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
      M (linearMap S S') D.liftKaehlerDifferential
    refine ⟨m, compDer ps_ $ m13 R S, fun s => ?_⟩
    let _a0 := m13 R S s
    have h1 : algebraMap S S' (ps_ _a0)
        = (m : S) • D.liftKaehlerDifferential _a0 :=
      LinearMap.congr_fun hps_ _a0
    rw [liftKaehlerDifferential_comp_D, smul_def] at h1
    exact sy_ h1
  exact ⟨m, D0_, h⟩
end
end

section
variable (D : Derivation R S N) (M : Submonoid S) [IsLocalization M S']
include M
theorem exists_liftToLocalization :
    ∃ D' : Derivation R S' N, ∀ s : S, D' (algebraMap S S' s) = D s := by
  let _c0 := m132 R R S S'
  have hu : ∀ y : M, IsUnit $ (algebraMap S $ End S N) y := fun y =>
    isUnit_algebraMap_moduleEnd (S' := S') M y
  have : IsLocalizedModule M _c0 := inferInstance
  refine ⟨(extendScalarsOfIsLocalization M S'
      (IsLocalizedModule.lift M _c0
        D.liftKaehlerDifferential hu)).compDer $ m13 R S', fun s => ?_⟩
  dsimp
  let _a0 := m13 R S s
  have key : IsLocalizedModule.lift M _c0
        D.liftKaehlerDifferential hu
        (m132 R R S S' _a0)
      = D.liftKaehlerDifferential _a0 :=
    LinearMap.congr_fun
      (IsLocalizedModule.lift_comp M _c0
        D.liftKaehlerDifferential hu) _a0
  rw [← map_D R R S S' s, key]
  exact D.liftKaehlerDifferential_comp_D s

noncomputable def liftToLocalization : Derivation R S' N :=
  (exists_liftToLocalization (S' := S') D M).choose

@[simp]
theorem liftToLocalization_algebraMap (s : S) :
    (D.liftToLocalization (S' := S') M) (algebraMap S S' s) = D s :=
  (exists_liftToLocalization (S' := S') D M).choose_spec s
end

section
variable (D : Derivation R S S) (M : Submonoid S) [IsLocalization M S']
include M
theorem exists_mapToLocalization :
    ∃ D' : Derivation R S' S', ∀ s : S,
      D' (algebraMap S S' s) = algebraMap S S' (D s) := by
  obtain ⟨D', hD'⟩ :=
    exists_liftToLocalization (S' := S') (N := S') ((linearMap S S').compDer D) M
  exact ⟨D', hD'⟩

noncomputable def mapToLocalization : Derivation R S' S' :=
  (exists_mapToLocalization (S' := S') D M).choose

@[simp]
theorem mapToLocalization_algebraMap (s : S) :
    (D.mapToLocalization (S' := S') M) (algebraMap S S' s) = algebraMap S S' (D s) :=
  (exists_mapToLocalization (S' := S') D M).choose_spec s
end

end Derivation
end
section
namespace IsOpenMap

theorem mem_closure_singleton_of_apply {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hopen : IsOpenMap f) (hinj : Injective f)
    {a b : A} (h : f b ∈ closure ({f a} : Set B)) : b ∈ closure ({a} : Set A) := by
  rw [mem_closure_iff]
  intro O hO hbO
  obtain ⟨y, hymem, hy⟩ := (mp_ mem_closure_iff h) (imS f O) (hopen O hO) ⟨b, hbO, rfl⟩
  obtain ⟨z, hzO, hz⟩ := hymem
  rw [mem_singleton_iff] at hy
  have hza := hinj $ tr_ hz hy
  subst hza
  exact ⟨z, hzO, rfl⟩

end IsOpenMap

namespace FunctorialResolution.EmbeddedResolution

section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isIrreducible_inter_open {S U : Set X} (hS : IsIrreducible S) (hU : IsOpen U)
    (hne : (S ∩ U).Nonempty) : IsIrreducible $ S ∩ U := by
  refine ⟨hne, ?_⟩
  rintro u v hu hv ⟨a, ⟨haS, haU⟩, hau⟩ ⟨b, ⟨hbS, hbU⟩, hbv⟩
  obtain ⟨c, hcS, hc⟩ := an2 hS (U ∩ u) (U ∩ v) (hU.inter hu) (hU.inter hv)
    ⟨a, haS, haU, hau⟩ ⟨b, hbS, hbU, hbv⟩
  exact ⟨c, ⟨hcS, hc.1.1⟩, hc.1.2, hc.2.2⟩

theorem closure_inter_open_eq {S U : Set X} (hS : IsClosed S) (hirr : IsIrreducible S)
    (hU : IsOpen U) (hne : (S ∩ U).Nonempty) : closure (S ∩ U) = S := by
  apply m15
  exact hS.closure_subset_iff.mpr inter_subset_left
  intro x hx
  rw [mem_closure_iff]
  intro o ho hxo
  obtain ⟨c, hcS, hc⟩ := an2 hirr o U ho hU ⟨x, hx, hxo⟩ hne
  exact ⟨c, an1 hc, hcS, an2 hc⟩

section
variable {f : Y → X}
theorem isIrreducible_preimage_of_isEmbedding (hf : Topology.IsEmbedding f)
    {T : Set X} (hT : IsIrreducible T) (hTr : T ⊆ Set.range f) :
    IsIrreducible $ f ⁻¹' T := by
  obtain ⟨t, ht⟩ := an1 hT
  obtain ⟨y, rfl⟩ := hTr ht
  refine ⟨⟨y, ht⟩, ?_⟩
  rintro u v hu hv ⟨a, haT, hau⟩ ⟨b, hbT, hbv⟩
  obtain ⟨u', hu', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hv
  obtain ⟨c, hcT, hcu, hcv⟩ := an2 hT u' v' hu' hv' ⟨f a, haT, hau⟩ ⟨f b, hbT, hbv⟩
  obtain ⟨z, rfl⟩ := hTr hcT
  exact ⟨z, hcT, hcu, hcv⟩

theorem isGenericPoint_preimage_of_isInducing (hf : Topology.IsInducing f)
    {xi_ : X} {T : Set X} (h : IsGenericPoint xi_ T) {y : Y} (hy : f y = xi_) :
    IsGenericPoint y $ f ⁻¹' T := by
  have h2 : closure ({y} : Set Y) = f ⁻¹' closure (f '' ({y} : Set Y)) :=
    hf.closure_eq_preimage_closure_image _
  rwa [image_singleton, hy, IsGenericPoint.def h] at h2

theorem isGenericPoint_image_of_isClosedEmbedding
    (hf : Topology.IsClosedEmbedding f) {y : Y} {T : Set Y} (h : IsGenericPoint y T) :
    IsGenericPoint (f y) $ f '' T := by
  apply m15
  have hcl : IsClosed $ imS f T := by
    rw [← IsGenericPoint.def h]
    exact hf.isClosedMap _ isClosed_closure
  exact hcl.closure_subset_iff.mpr $ Set.singleton_subset_iff.mpr ⟨y, IsGenericPoint.mem h, rfl⟩
  have h2 : f '' closure ({y} : Set Y) ⊆ closure (f '' ({y} : Set Y)) :=
    image_closure_subset_closure_image hf.continuous
  rw [image_singleton] at h2
  rwa [← IsGenericPoint.def h]
end

theorem closure_image_genericPoint {f : X → Y} (hcont : Continuous f) {S : Set X} {xi_ : X}
    (hxi_ : IsGenericPoint xi_ S) : closure (f '' S) = closure ({f xi_} : Set Y) := by
  refine m15 ?_ ?_
  refine closure_minimal ?_ isClosed_closure
  have hsub := image_closure_subset_closure_image (f := f) (s := ({xi_} : Set X)) hcont
  rw [image_singleton] at hsub
  rwa [← hxi_]
  refine closure_mono ?_
  refine Set.singleton_subset_iff.2 ⟨xi_, ?_, rfl⟩
  rw [← hxi_]
  exact subset_closure rfl

theorem isOpen_sUnion_of_irreducibleComponents {Z : Type} [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Z] (C : Set (Set Z))
    (hdisj : ∀ S ∈ C, ∀ W ∈ irreducibleComponents Z, W ∉ C → Disjoint S W) :
    IsOpen (⋃₀ C) := by
  have hclosed : IsClosed (⋃₀ (irreducibleComponents Z \ C)) := by
    rw [sUnion_eq_biUnion]
    exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset sdiff_subset).isClosed_biUnion fun i hi => isClosed_of_mem_irreducibleComponents i hi.1
  have heq : ⋃₀ C = (⋃₀ (irreducibleComponents Z \ C))ᶜ := by
    apply m15
    rintro x ⟨S, hSmem, hxS⟩
    have hx : x ∉ ⋃₀ (irreducibleComponents Z \ C) := by
      rintro ⟨W, ⟨hW, hWC⟩, hxW⟩
      exact mp_ disjoint_left (hdisj S hSmem W hW hWC) hxS hxW
    exact hx
    intro x hx
    rw [mem_compl_iff] at hx
    by_cases hmem : irreducibleComponent x ∈ C
    exact mem_sUnion_of_mem mem_irreducibleComponent hmem
    exact absurd (mem_sUnion_of_mem mem_irreducibleComponent
      (mem_sdiff_of_mem (irreducibleComponent_mem_irreducibleComponents x) hmem)) hx
  rw [heq]
  exact hclosed.isOpen_compl

end

section


theorem support_comap_eq {X Y : Sch} (f : X ⟶ Y) (I : ISD Y) :
    ((I.comap f).support : Set X) = f.base ⁻¹' (I.support : Set Y) :=
  congrArg (fun s : m182 X => (s : Set X))
    (support_comap I f)

theorem comap_io_eq_top_of_disjoint {X : Sch} (I : ISD X) (U : Opn X)
    (h : Disjoint (U : Set X) (I.support : Set X)) : I.comap U.i = ⊤ := by
  have hempty : (spI (cmI I U.i) : Set U) = ∅ := by
    rw [support_comap_eq]
    refine mpr_ eq_empty_iff_forall_notMem fun x hx => ?_
    refine mp_ disjoint_left h ?_ hx
    rw [← q1]
    exact ⟨x, rfl⟩
  rw [← support_eq_bot_iff]
  exact SetLike.ext' hempty

end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

open Set TopologicalSpace

section
variable {X : Type} [TopologicalSpace X] [NoetherianSpace X]
theorem isClosed_sUnion_of_subset_irreducibleComponents {Ac_ : Set (Set X)} (hAc : ∀ C ∈ Ac_, C ∈ irreducibleComponents X) :
    IsClosed $ ⋃₀ Ac_ := by
  have hsub := fun C hC => hAc C hC
  rw [sUnion_eq_biUnion]
  exact ((m169 ..).subset hsub).isClosed_biUnion
    (fun C hC => isClosed_of_mem_irreducibleComponents _ $ hAc C hC)

theorem isOpen_sUnion_of_subset_irreducibleComponents
    (hsep : ∀ C1_ ∈ irreducibleComponents X, ∀ C2_ ∈ irreducibleComponents X,
      (C1_ ∩ C2_).Nonempty → C1_ = C2_)
    {Ac_ : Set $ Set X} (hAc : ∀ C ∈ Ac_, C ∈ irreducibleComponents X) :
    IsOpen $ ⋃₀ Ac_ := by
  have key : (⋃₀ Ac_)ᶜ = ⋃₀ (irreducibleComponents X \ Ac_) := by
    apply m15
    intro y hy
    refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩,
      mem_irreducibleComponent ..⟩
    intro hmem
    exact hy ⟨irreducibleComponent y, hmem, mem_irreducibleComponent ..⟩
    intro y hyc
    obtain ⟨C, ⟨hC, hCA⟩, hyC⟩ := hyc
    intro hy
    obtain ⟨D, hD, hyD⟩ := hy
    rw [hsep C hC D (hAc D hD) ⟨y, hyC, hyD⟩] at hCA
    exact hCA hD
  rw [← isClosed_compl_iff, key]
  exact isClosed_sUnion_of_subset_irreducibleComponents fun C hC => an1 hC
end

theorem irreducibleComponents_eq_of_stalk_isDomain (X : Sch)
    (hX : ∀ x : X, IsDomain $ X.presheaf.stalk x) {C1_ C2_ : Set X}
    (h1_ : C1_ ∈ irreducibleComponents X) (h2_ : C2_ ∈ irreducibleComponents X)
    {x : X} (hx1_ : x ∈ C1_) (hx2_ : x ∈ C2_) : C1_ = C2_ := by
  obtain ⟨xi1_, hg1_⟩ := m140 h1_.1 $ isClosed_of_mem_irreducibleComponents _ h1_
  obtain ⟨xi2_, hg2_⟩ := m140 h2_.1 $ isClosed_of_mem_irreducibleComponents _ h2_
  have hxi1 : closure {xi1_} = C1_ := hg1_
  have hxi2 : closure {xi2_} = C2_ := hg2_
  have hrange : m30 (X.fromSpecStalk x).base = {y | y ⤳ x} :=
    range_fromSpecStalk ..
  have hm1_ : xi1_ ∈ m30 (X.fromSpecStalk x).base := by
    rw [hrange]
    exact mpr_ specializes_iff_mem_closure (by rw [hxi1]; exact hx1_)
  have hm2_ : xi2_ ∈ m30 (X.fromSpecStalk x).base := by
    rw [hrange]
    exact mpr_ specializes_iff_mem_closure (by rw [hxi2]; exact hx2_)
  have himg : IsIrreducible $ Set.range (X.fromSpecStalk x).base := by
    rw [← image_univ]
    exact (IrreducibleSpace.isIrreducible_univ ..).image _ ((X.fromSpecStalk x).continuous).continuousOn
  have hcl := himg.closure
  have hs1_ : C1_ ⊆ closure (m30 (X.fromSpecStalk x).base) := by
    rw [← hxi1]
    exact closure_mono $ Set.singleton_subset_iff.mpr hm1_
  have hs2_ : C2_ ⊆ closure (m30 (X.fromSpecStalk x).base) := by
    rw [← hxi2]
    exact closure_mono $ Set.singleton_subset_iff.mpr hm2_
  exact m15 (hs1_.trans $ an2 h2_ hcl hs2_) $ hs2_.trans $ an2 h1_ hcl hs1_

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution


end FunctorialResolution.EmbeddedResolution
end
section
namespace AlgebraicGeometry



namespace IsOpenImmersion

theorem bijective_appLE_of_image_eq {A B : Sch} (f : A ⟶ B) [IsOpenImmersion f]
    (O : Opn B) (S : Opn A) (e : S ≤ f.pre O) (h : f.im S = O) :
    Bijective $ CommRingCat.Hom.hom $ appLE f O S e := by
  subst h
  have : IsIso $ appLE f (imU f S) S e := by
    rw [← appIso_hom' f S]
    infer_instance
  constructor
  intro a b hab
  have h1 : (m4 $ appLE f (imU f S) S e ≫
        inv (appLE f (imU f S) S e)) a
      = (m4 $ appLE f (imU f S) S e ≫
        inv (appLE f (imU f S) S e)) b := by
    simp only [hom_comp, m82, hab]
  rw [m118] at h1
  simpa only [hom_id, id_apply] using h1
  intro y
  refine ⟨(m4 $ inv $ appLE f (imU f S) S e) y, ?_⟩
  have h3 := congrArg (fun mm => (m4 mm) y)
    (m117 $ appLE f (imU f S) S e)
  simpa only [hom_comp, m82, hom_id,
    id_apply] using h3

end IsOpenImmersion

end AlgebraicGeometry
end
section

namespace FunctorialResolution.EmbeddedResolution

theorem isReduced_stalk_of_isAffineOpen {Z : Sch} {V : Opn Z}
    (hV : IsAffineOpen V)
    (hred : _root_.IsReduced ↥(Z.presheaf.obj $ op V)) (x : V) :
    _root_.IsReduced ↥(Z.presheaf.stalk x.1) := by
  have := hV.isLocalization_stalk x
  exact isReduced_localizationPreserves (hV.primeIdealOf x).asIdeal.primeCompl
    (stkX Z x.1) hred

section
variable {W X : Sch} (f : W ⟶ X) [IsReduced W] [QuasiCompact f]
theorem isReduced_presheaf_obj_subscheme_ker (U : X.affineOpens) :
    _root_.IsReduced ↥((ker f).subscheme.presheaf.obj
      (op $ (TopologicalSpace.Opens.map
        (ker f).subschemeι.base).obj U.1)) := by
  have hid : (ker f).ideal U
      = m41 (app f U.1).hom := by
    simp
  have hq : _root_.IsReduced $ (pObj X $ op U.1) ⧸
      (ker f).ideal U := by
    rw [hid]
    exact isReduced_of_injective (kerLift (app f U.1).hom)
      (kerLift_injective _)
  let _a0 := subschemeObjIso (ker f) U
  exact isReduced_of_injective
    (_a0.hom.hom)
    _a0.commRingCatIsoToRingEquiv.injective

theorem isReduced_stalk_subscheme_ker
    (y : (ker f).subscheme) :
    _root_.IsReduced ↥((ker f).subscheme.presheaf.stalk y) := by
  obtain ⟨U, hU, hyU⟩ : ∃ U, IsAffineOpen U ∧
      (ker f).subschemeι.base y ∈ U :=
    ⟨(X.affineCover.f $ X.affineCover.idx _).opensRange,
      AlgebraicGeometry.isAffineOpen_opensRange _, X.affineCover.covers _⟩
  exact isReduced_stalk_of_isAffineOpen (hU.preimage (ker f).si) (isReduced_presheaf_obj_subscheme_ker f ⟨U, hU⟩) ⟨y, hyU⟩

theorem isReduced_subscheme_ker :
    IsReduced (ker f).subscheme := by
  have : ∀ y : subS $ ker f,
      _root_.IsReduced $ (ker f).subscheme.presheaf.stalk y :=
    fun y => isReduced_stalk_subscheme_ker f y
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _
end


section
variable {R : Type} [CommRing R]
theorem prod_notMem_of_isPrime {ι : Type} [DecidableEq ι]
    {I : Ideal R} (hI : I.IsPrime) (g : ι → R) (t : Finset ι) :
    (∀ j ∈ t, g j ∉ I) → ∏ j ∈ t, g j ∉ I := by
  induction t using m178 with
  | empty =>
      intro _ h1
      rw [prod_empty] at h1
      refine hI.ne_top ?_
      rwa [eq_top_iff_one]
  | @insert a u ha ih =>
      intro h hmem
      rw [prod_insert ha] at hmem
      rcases hI.mem_or_mem hmem with h1 | h1
      simp_all
      simp_all

theorem span_singleton_mul_eq_inf {a b : R}
    (hpa : (Ideal.span ({a} : Set R)).IsPrime) (hb : b ∉ Ideal.span ({a} : Set R)) :
    Ideal.span ({a * b} : Set R) = Ideal.span ({a} : Set R) ⊓ Ideal.span ({b} : Set R) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  rw [span_singleton_le_iff_mem]
  exact mpr_ mem_span_singleton ⟨b, rfl⟩
  rw [span_singleton_le_iff_mem]
  exact mpr_ mem_span_singleton ⟨a, mul_comm a b⟩
  intro z hz
  rw [mem_inf] at hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨v, rfl⟩ := mp_ mem_span_singleton hz2
  obtain ⟨w, rfl⟩ := mp_ mem_span_singleton $ (hpa.mem_or_mem hz1).resolve_left hb
  exact mpr_ mem_span_singleton ⟨w, by ring⟩

section
variable {ι : Type} [DecidableEq ι] (f : ι → R) (s : Finset ι) (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime) (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R))
include hp hdvd
theorem span_singleton_prod_eq_biInf :
    Ideal.span ({∏ i ∈ s, f i} : Set R) = ⨅ i ∈ s, Ideal.span ({f i} : Set R) := by
  revert hp hdvd
  induction s using m178 with
  | empty =>
      intro _ _
      simp
  | @insert a u ha ih =>
      intro hp hdvd
      let _a0 := mem_insert_self a u
      have hpa := hp a _a0
      have hP : (∏ i ∈ u, f i) ∉ m17 ({f a} : Set R) := by
        refine prod_notMem_of_isPrime hpa f u ?_
        intro j hj
        exact hdvd a _a0 j (mem_insert_of_mem hj)
          (by rintro rfl; exact ha hj)
      have ihu := ih (fun i hi => hp i $ mem_insert_of_mem hi)
        (fun i hi j hj hij =>
          hdvd i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
      rw [prod_insert ha, span_singleton_mul_eq_inf hpa hP, ihu, Finset.iInf_insert]

theorem isRadical_span_singleton_prod_finset :
    (Ideal.span ({∏ i ∈ s, f i} : Set R)).IsRadical := by
  rw [span_singleton_prod_eq_biInf f s hp hdvd]
  refine le_iInf fun i => le_iInf fun hi => ?_
  exact le_trans (radical_mono $ iInf_le_of_le i $ iInf_le _ hi) (hp i hi).isRadical
end
end

end FunctorialResolution.EmbeddedResolution

namespace IsLocalization

theorem map_eq_map_of_map_eq_map {R S T : Type} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (M : Submonoid R) [IsLocalization M S]
    [IsLocalization M T] {I J : Ideal R}
    (h : Ideal.map (algebraMap R S) I = Ideal.map (algebraMap R S) J) :
    Ideal.map (algebraMap R T) I = Ideal.map (algebraMap R T) J := by
  let _a0 := algEquiv M S T
  let _a1 := algebraMap R S
  have he : (_a0.toAlgHom.toRingHom).comp _a1
      = algebraMap R T :=
    RingHom.ext fun r => by
      exact _a0.commutes r
  have hmap : ∀ K, Ideal.map (algebraMap R T) K =
      Ideal.map (_a0.toAlgHom.toRingHom)
        (Ideal.map _a1 K) := by
    intro K
    rw [Ideal.map_map, he]
  rw [hmap, hmap, h]

end IsLocalization

namespace Ideal

theorem list_prod_le_getElem {R : Type} [CommRing R] (L : List (Ideal R)) (i : ℕ)
    (hi : i < L.length) : L.prod ≤ (L[i]'hi) := by
  revert i hi
  induction L with
  | nil =>
      intro i hi
      simp at hi
  | cons A L ih =>
      intro i hi
      cases i with
      | zero =>
          simp [prod_cons, getElem_cons_zero]
          exact le_trans mul_le_inf inf_le_left
      | succ i' =>
          have hi' := by simpa using hi
          simp [prod_cons, getElem_cons_succ]
          exact le_trans (le_trans mul_le_inf inf_le_right) $ ih i' hi'

end Ideal

namespace KaehlerDifferential

theorem residue_tmul_D_mul_of_mem_maximalIdeal (k : Type) [CommRing k] (A : Type)
    [CommRing A]
    [Algebra k A] [IsLocalRing A] (x c : A) (hx : x ∈ IsLocalRing.maximalIdeal A) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x * c) =
      residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x) := by
  have hsm : ∀ a, a • 1 = residue A a := by
    intro a
    rw [smul_def, mul_one, algebraMap_eq]
  have hx0 := hx
  rw [← residue_eq_zero_iff] at hx0
  have hstep : residue A c •
        (1 ⊗ₜ[A] m13 k A x)
      = (residue A c * 1) ⊗ₜ[A] m13 k A x := rfl
  rw [leibniz, tmul_add, ← smul_tmul,
    ← smul_tmul, hsm, hsm, hx0, zero_tmul, zero_add, hstep,
    mul_one]

end KaehlerDifferential
end
section
namespace IsRegularLocalRing

open IsLocalRing


section
variable {R : Type} [CommRing R]
theorem spanFinrank_span_finset_le_card (s : Finset R) :
    spanFinrank (Ideal.span (s : Set R)) ≤ s.card := by
  have h1 : (m17 (s : Set R)).spanRank ≤ Cardinal.mk (s : Set R) :=
    spanRank_span_le_card _
  rw [Submodule.FG.spanRank_eq_spanFinrank $ fg_span s.finite_toSet] at h1
  have h3 : Cardinal.mk (s : Set R) = (s.card : Cardinal) := by simp
  rw [h3] at h1
  exact_mod_cast h1

theorem le_of_le_of_mem_minimalPrimes {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q :=
  an2 hp ⟨hq, bot_le⟩ hle

theorem isLocalRing_quotient_span_singleton [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing $ R ⧸ Ideal.span ({x} : Set R) := by
  let _m0 := ({x} : Set R)
  have hIle : m17 _m0 ≤ maximalIdeal R := by
    rwa [span_le, singleton_subset_iff]
  have hIne : m17 _m0 ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hIle
    exact (isMaximal R).ne_top hIle
  have hone : (1 : R ⧸ m17 _m0) ≠ 0 := by
    intro h
    refine hIne $ mpr_ (eq_top_iff_one _) ?_
    rwa [← eq_zero_iff_mem, map_one]
  have : Nontrivial $ R ⧸ m17 _m0 := ⟨⟨1, 0, hone⟩⟩
  exact IsLocalRing.of_surjective' (m5 _) m108

theorem isPrime_of_mem_minimalPrimes {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := hp.1.1
end

section
variable (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  by_contra hcon
  push Not at hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ i ∈ ((insert (maximalIdeal R ^ 2) t : Finset $ Ideal R) : Set $ Ideal R), (i : Set R) := by
    intro y hy
    rcases em (y ∈ maximalIdeal R ^ 2) with hm2 | hm2
    simp_all
    simp_all
  have hp : ∀ i ∈ (insert (maximalIdeal R ^ 2) t : Finset $ Ideal R),
      i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime := by
    intro i hi h1 _
    have hit : i ∈ t := by simp_all
    refine isPrime_of_mem_minimalPrimes ?_
    rw [← ht]
    exact Finset.mem_coe.mpr hit
  obtain ⟨i, hi, hle⟩ := mp_ (subset_union_prime _ _ hp) hsub
  rcases mem_insert.mp hi with hh | hh
  subst hh
  exact hsq hle
  refine hmin ⟨i, ?_, hle⟩
  rw [← ht]
  exact Finset.mem_coe.mpr hh
end

theorem exists_repr_ne_zero {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : b.repr v = 0 := by
    ext j
    simp [h j]
  apply hv
  simpa using (congrArg (b.repr.symm) h0)

theorem eq_natCast_and_add_one_eq_of_le {a : WithBot ENat} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ENat) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ENat)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ENat) ∧ a + 1 = ((n : ℕ) : WithBot ENat) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = (m : WithBot ENat) := by
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      rw [WithBot.bot_add, le_bot_iff] at h1
      exact WithBot.natCast_ne_bot n h1
    | coe e =>
      induction e using recTopCoe with
      | top =>
        exfalso
        have h2' : (⊤ : ENat) ≤ (d : ENat) := by exact_mod_cast h2
        simp at h2'
      | coe m => exact ⟨m, by norm_cast⟩
  have hmd : m ≤ d := by exact_mod_cast h2
  have hnm : n ≤ m + 1 := by exact_mod_cast h1
  have hm : m = d := by omega
  have hn : n = m + 1 := by omega
  constructor
  rw [hm]
  rw [hn]
  norm_cast

theorem span_insert_image_erase_eq_top {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v $ ⇑b '' ↑(Finset.univ.erase j)) = ⊤ := by
  let _c0 := insert v $ b '' (Finset.univ.erase j)
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [mem_coe]
  by_cases hij : i = j
  rw [hij]
  have hmem2 : ∑ l ∈ Finset.univ.erase j, b.repr v l • b l ∈
      m72 K _c0 := by
    exact Submodule.sum_mem _ fun l hl => smul_mem _ _ $ subset_span $ Set.mem_insert_of_mem _ ⟨l, Finset.mem_coe.mpr hl, rfl⟩
  let _a0 := b.repr v j
  have hsub : v - ∑ l ∈ Finset.univ.erase j, b.repr v l • b l = _a0 • b j := by
    rw [sum_erase_eq_sub $ mem_univ j, b.sum_repr v]
    abel
  have hkey : _a0 • b j ∈
      m72 K _c0 := by
    rw [← hsub]
    exact m162 _ (subset_span $ Set.mem_insert _ _) hmem2
  have h2 := smul_mem _ _a0⁻¹ hkey
  rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h2
  exact subset_span $ Set.mem_insert_of_mem _ ⟨i, by simp [hij], rfl⟩

section
variable (R : Type) [CommRing R]
theorem spanFinrank_maximalIdeal_quotient_add_one_le_finrank [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing $ R ⧸ Ideal.span ({x} : Set R)] :
    spanFinrank (maximalIdeal $ R ⧸ Ideal.span ({x} : Set R)) + 1 ≤
      finrank (ResidueField R) (CotangentSpace R) := by
  classical
  have hv0 : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rwa [Ne, toCotangent_eq_zero]
  obtain ⟨j, hj⟩ := exists_repr_ne_zero (finBasis (ResidueField R) $ CotangentSpace R) hv0
  obtain ⟨z, hz⟩ : ∃ z : Fin (finrank (ResidueField R) $ CotangentSpace R) →
      (maximalIdeal R), ∀ i, (maximalIdeal R).toCotangent (z i) =
        finBasis (ResidueField R) (CotangentSpace R) i := by
    choose z hz using fun i => (toCotangent_surjective _) $ finBasis (ResidueField R) (CotangentSpace R) i
    exact ⟨z, hz⟩
  set s : Set $ maximalIdeal R :=
    insert (⟨x, hx⟩ : maximalIdeal R) (z '' (Finset.univ.erase j)) with hsdef
  have htop : Submodule.span R s = ⊤ := by
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff]
    have himg : (maximalIdeal R).toCotangent '' s =
        insert ((maximalIdeal R).toCotangent ⟨x, hx⟩)
          ((finBasis (ResidueField R) $ CotangentSpace R) ''
            (Finset.univ.erase j)) := by
      rw [hsdef, image_insert_eq, image_image]
      simp [hz]
    rw [himg]
    exact span_insert_image_erase_eq_top _ _ hj
  have hmspan : Ideal.span (Subtype.val '' s) = maximalIdeal R := by
    have h := congrArg (Submodule.map (maximalIdeal R).subtype) htop
    rw [Submodule.map_span, map_subtype_top] at h
    simpa using h
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rwa [Ideal.span_le, Set.singleton_subset_iff]
  have hmapS : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.map (Ideal.Quotient.mk $ Ideal.span ({x} : Set R)) (maximalIdeal R) := by
    apply le_antisymm
    intro y hy
    obtain ⟨r, rfl⟩ := mk_surjective y
    refine mem_map_of_mem _ ?_
    by_contra hr
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy
    exact hy $ hr.map $ Ideal.Quotient.mk $ Ideal.span ({x} : Set R)
    refine IsLocalRing.le_maximalIdeal ?_
    intro h
    rw [eq_top_iff_one, mem_map_iff_of_surjective _ mk_surjective] at h
    obtain ⟨r, hrm, hr1⟩ := h
    have h2 : r - 1 ∈ Ideal.span ({x} : Set R) := by
      rw [← Ideal.Quotient.eq]
      simpa using hr1
    refine (isMaximal R).ne_top $ mpr_ (eq_top_iff_one _) ?_
    have h4 := sub_mem hrm $ hIle h2
    simp at h4
  have himg : (Ideal.Quotient.mk $ Ideal.span ({x} : Set R)) ''
      (Subtype.val '' s) =
      insert 0 ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) $ z i) ''
        (Finset.univ.erase j)) := by
    rw [hsdef, image_image, Set.image_insert_eq, image_image]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr $ Ideal.mem_span_singleton_self x]
  have hquot : maximalIdeal (R ⧸ Ideal.span ({x} : Set R)) =
      Ideal.span ((fun i => Ideal.Quotient.mk (Ideal.span ({x} : Set R)) $ z i) ''
        (Finset.univ.erase j)) := by
    rw [hmapS]
    conv_lhs => rw [← hmspan]
    rw [map_span, himg]
    exact span_insert_zero
  have hcard : spanFinrank (maximalIdeal $ R ⧸ Ideal.span ({x} : Set R)) ≤
      (Finset.univ.erase j).card := by
    rw [hquot, ← coe_image]
    exact le_trans (spanFinrank_span_finset_le_card _) card_image_le
  have hjpos := pos j
  have hcard2 : (Finset.univ.erase j).card =
      finrank (ResidueField R) (CotangentSpace R) - 1 := by simp_all
  omega

theorem spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing $ R ⧸ Ideal.span ({x} : Set R)] :
    ((spanFinrank (maximalIdeal $ R ⧸ Ideal.span ({x} : Set R)) : ℕ) : WithBot ENat)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  let _a0 := m17 ({x} : Set R)
  let _c0 := R ⧸ _a0
  have hRdim : ((finrank (ResidueField R) (CotangentSpace R) : ℕ) : WithBot ENat)
      = ringKrullDim R := by
    rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal
  have hdimQuot : ringKrullDim _c0 ≤
      ((spanFinrank (maximalIdeal _c0) : ℕ) :
        WithBot ENat) := by
    exact_mod_cast ringKrullDim_le_spanFinrank_maximalIdeal _c0
  have hIj : _a0 ≤ Ring.jacobson R := by
    refine le_trans ?_ (ringJacobson_eq_maximalIdeal R).ge
    rwa [span_le, singleton_subset_iff]
  have hdimLe := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
      _a0 hIj
  have h1 := by
    simpa using (spanFinrank_span_finset_le_card ({x} : Finset R))
  have hcast : ((spanFinrank _a0) : WithBot ENat) ≤ 1 := by
    exact_mod_cast h1
  obtain ⟨hA, hB⟩ := eq_natCast_and_add_one_eq_of_le
    (d := spanFinrank $ maximalIdeal _c0)
    (n := finrank (ResidueField R) $ CotangentSpace R)
    (by rw [hRdim]; exact hdimLe.trans $ add_le_add le_rfl hcast) hdimQuot $ spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
  refine ⟨sy_ hA, ?_⟩
  rw [hB, hRdim]
end

section
variable {R : Type} [CommRing R] [IsRegularLocalRing R] {x} (hx : x ∈ IsLocalRing.maximalIdeal R) (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2)
include hx hx2
theorem isRegularLocalRing_quotient_span_singleton :
    IsRegularLocalRing $ R ⧸ Ideal.span ({x} : Set R) := by
  have := isLocalRing_quotient_span_singleton hx
  rw [isRegularLocalRing_iff]
  exact_mod_cast (spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq R hx hx2).1

theorem ringKrullDim_quotient_span_singleton_add_one :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient_span_singleton hx
  exact an2 $ spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq R hx hx2
end

theorem isDomain_of_forall_spanFinrank_lt (R : Type) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S],
      spanFinrank (maximalIdeal S) < spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R := by
  classical
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  let R := R
  let h : maximalIdeal R = ⊥ := by
    refine eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
      (noetherian _) ?_ $ maximalIdeal_le_jacobson ⊥
    dsimp
    rwa [← pow_two]
  have hp := (maximalIdeal.isMaximal R).isPrime
  rw [h] at hp
  have := hp
  exact IsDomain.of_bot_isPrime R
  by_cases hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p
  exfalso
  obtain ⟨p, hp, hple⟩ := hmin
  have hpp := isPrime_of_mem_minimalPrimes hp
  have hpm := le_antisymm (le_maximalIdeal hpp.ne_top) hple
  have hallideal : ∀ q : Ideal R, q.IsPrime → q = maximalIdeal R := by
    intro q hq
    refine le_antisymm (le_maximalIdeal hq.ne_top) ?_
    rw [← hpm]
    exact le_of_le_of_mem_minimalPrimes hp hq
      (by rw [hpm]; exact le_maximalIdeal hq.ne_top)
  have h2 : ringKrullDim R ≤ 0 := by
    have hPQ : ∀ P Q : PrimeSpectrum R, P = Q := by
      intro P Q
      apply PrimeSpectrum.ext
      rw [hallideal P.asIdeal P.isPrime, hallideal Q.asIdeal Q.isPrime]
    have : Subsingleton $ PrimeSpectrum R := ⟨hPQ⟩
    exact Order.krullDim_nonpos_of_subsingleton
  obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 := by
    by_contra hc
    push Not at hc
    exact hsq fun y hy => hc y hy
  have := isLocalRing_quotient_span_singleton hx
  have hpos := spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
  have hdim :=
    (mp_ (IsRegularLocalRing.iff_finrank_cotangentSpace R) inferInstance).symm
  rw [hdim] at h2
  have hle0 : finrank (ResidueField R) (CotangentSpace R) ≤ 0 := by exact_mod_cast h2
  omega
  obtain ⟨x, hx, hx2, hxp⟩ :=
    exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin
  have := isLocalRing_quotient_span_singleton hx
  have hrq :=
    isRegularLocalRing_quotient_span_singleton hx hx2
  have hlt : spanFinrank (maximalIdeal $ R ⧸ Ideal.span ({x} : Set R)) <
      spanFinrank (maximalIdeal R) := by
    have h1 := spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
    have h2 : spanFinrank (maximalIdeal R)
        = finrank (ResidueField R) (CotangentSpace R) := by
      rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    omega
  have hprime :=
    (isDomain_iff_prime _).mp $ IH (R ⧸ Ideal.span ({x} : Set R)) hlt
  obtain ⟨p, hp, hple⟩ :=
    exists_minimalPrimes_le (bot_le : (⊥) ≤ Ideal.span ({x} : Set R))
  have hpp := isPrime_of_mem_minimalPrimes hp
  have hpbot : p = ⊥ := by
    refine eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
      (noetherian p) ?_ $ maximalIdeal_le_jacobson ⊥
    intro y hy
    obtain ⟨a, rfl⟩ := mp_ mem_span_singleton $ hple hy
    refine mul_mem_mul hx ?_
    rcases hpp.mem_or_mem hy with hh | hh
    simp_all
    exact hh
  rw [hpbot] at hpp
  have := hpp
  exact IsDomain.of_bot_isPrime R

theorem isDomain_of_spanFinrank_le :
    ∀ n (R : Type) [CommRing R] [IsRegularLocalRing R],
      spanFinrank (maximalIdeal R) ≤ n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact absurd (lt_of_lt_of_le hS h) $ not_lt_zero _
  | succ n IH =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact IH S $ by omega

theorem isDomain (R : Type) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_le (spanFinrank $ m16 R) R le_rfl

instance (priority := 100) instIsDomain {R : Type} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

theorem false_of_eq_smul_of_linearIndependent {K M : Type} {ι : Type} [Field K]
    [AddCommGroup M] [Module K M] {v : ι → M} (h : LinearIndependent K v) {i j : ι}
    (hij : i ≠ j) (c : K) (he : v j = c • v i) : False := by
  classical
  have key : ∑ k ∈ ({i, j} : Finset ι),
      (fun k => if k = i then c else if k = j then (-1) else 0) k • v k = 0 := by
    rw [sum_pair hij]
    simp [m113 hij, he]
  have h2 := mp_ linearIndependent_iff' h {i, j}
      (fun k => if k = i then c else if k = j then (-1) else 0) key j $ by simp
  simp [m113 hij] at h2

section
variable {R : Type} [CommRing R] [IsRegularLocalRing R] {ι : Type}
section
variable (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R) (hli : LinearIndependent (IsLocalRing.ResidueField R) (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ : ι → CotangentSpace R))
include hli
theorem notMem_maximalIdeal_sq
    (i : ι) : x i ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hmem
  refine hli.ne_zero i ?_
  rwa [toCotangent_eq_zero]

theorem isPrime_span_singleton
    (i : ι) : (Ideal.span ({x i} : Set R)).IsPrime := by
  have :=
    isRegularLocalRing_quotient_span_singleton (hx i) $ notMem_maximalIdeal_sq x hx hli i
  rw [← isDomain_iff_prime]
  exact IsRegularLocalRing.isDomain _

theorem notMem_span_singleton
    {i j : ι} (hij : i ≠ j) : x j ∉ Ideal.span ({x i} : Set R) := by
  intro hmem
  obtain ⟨r, hr⟩ := mp_ mem_span_singleton' hmem
  have hmem2 := hx j
  rw [← hr] at hmem2
  have key : ((m16 R).toCotangent ⟨x j, hx j⟩ :
      CotangentSpace R)
      = algebraMap R (m14 R) r •
        ((m16 R).toCotangent ⟨x i, hx i⟩ :
          CotangentSpace R) := by
    have hsub : (⟨x j, hx j⟩ : m16 R) = ⟨r * x i, hmem2⟩ :=
      m26 hr.symm
    rw [hsub]
    let a := x i
    have h1 : (⟨r * a, hmem2⟩ : m16 R)
        = r • (⟨a, hx i⟩ : m16 R) := m26 rfl
    rw [algebraMap_smul, h1, map_smul]
  exact false_of_eq_smul_of_linearIndependent hli hij _ key
end

theorem isRadical_span_singleton_prod
    [Fintype ι] (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → CotangentSpace R)) :
    (Ideal.span ({∏ i, x i} : Set R)).IsRadical := by
  classical
  exact FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset x univ
    (fun i _ => isPrime_span_singleton x hx hli i)
    (fun i _ j _ hij => notMem_span_singleton x hx hli hij)
end

end IsRegularLocalRing
end
section
open CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

theorem preimage_comp {X Y Z : Sch} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opn Z) :
    (f ≫ g).pre U = f.pre (g ⁻¹ᵁ U) := by
  simp

theorem image_preimage_of_le {X : Sch} (U A : Opn X) (hA : A ≤ U) :
    U.i ''ᵁ (U.i ⁻¹ᵁ A) = A := by
  apply le_antisymm
  rintro z ⟨w, hw, rfl⟩
  exact hw
  intro z hz
  exact ⟨⟨z, hA hz⟩, hz, rfl⟩

private theorem basicOpen_appLE {X Y : Sch} (f : X ⟶ Y) {U : Opn Y} {V : Opn X}
    (e : V ≤ f ⁻¹ᵁ U) (s : ↑(Y.presheaf.obj $ op U)) :
    X.basicOpen ((appLE f U V e).hom s) =
      V ⊓ f ⁻¹ᵁ Y.basicOpen s := by
  simp [appLE, preimage_basicOpen]

theorem algebraMap_basicOpen_eq_presheaf_map {X : Sch} {U : Opn X}
    (s : ↑(X.presheaf.obj $ op U)) :
    algebraMap ↑(X.presheaf.obj $ op U)
        ↑(X.presheaf.obj $ op $ X.basicOpen s) =
      (X.presheaf.map (homOfLE $ X.basicOpen_le s).op).hom :=
  rfl

section
variable {X Y : Sch} (f : X ⟶ Y) (n : ℕ)
theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_target {U : Opn Y}
    (hU : IsAffineOpen U) {V : Opn X}
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (s : ↑(Y.presheaf.obj (op U)))
    (hs : IsStandardSmoothOfRelativeDimension n
      (appLE f U V e).hom)
    (hle : X.basicOpen ((appLE f U V e).hom s) ≤
      f ⁻¹ᵁ Y.basicOpen s) :
    IsStandardSmoothOfRelativeDimension n
      (appLE f (Y.basicOpen s)
        (X.basicOpen ((appLE f U V e).hom s)) hle).hom := by
  let _a0 := appLE f U V e
  let _c0 := pObj X $ op (bOpn X (_a0.hom s))
  let _a1 := pObj Y $ op (bOpn Y s)
  have i1 : m215 s ↑_a1 :=
    hU.isLocalization_basicOpen s
  have i2 : m215 (_a0.hom s)
      ↑_c0 :=
    hV.isLocalization_basicOpen _
  have i3 : IsLocalization
      (Submonoid.map _a0.hom (powers s))
      ↑_c0 := by simp_all
  have key := isStandardSmoothOfRelativeDimension_localizationPreserves n
    _a0.hom (powers s)
    ↑_a1
    ↑_c0 hs
  convert key using 1
  apply IsLocalization.ringHom_ext $ powers s
  rw [IsLocalization.map_comp, algebraMap_basicOpen_eq_presheaf_map,
    algebraMap_basicOpen_eq_presheaf_map, ← hom_comp,
    ← hom_comp, map_appLE,
    appLE_map]

theorem isStandardSmoothOfRelativeDimension_appLE_basicOpen_source {U : Opn Y}
    {V : Opn X} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : IsStandardSmoothOfRelativeDimension n
      (appLE f U V e).hom)
    (t : ↑(X.presheaf.obj $ op V)) (hle : X.basicOpen t ≤ f ⁻¹ᵁ U) :
    IsStandardSmoothOfRelativeDimension n
      (appLE f U (X.basicOpen t) hle).hom := by
  let _a0 := pObj X $ op $ bOpn X t
  have : m215 t ↑_a0 :=
    hV.isLocalization_basicOpen t
  have h0 : IsStandardSmoothOfRelativeDimension 0
      (algebraMap ↑(pObj X $ op V)
        ↑_a0) :=
    isStandardSmoothOfRelativeDimension_holdsForLocalizationAway _ t
  have hcomp := h0.comp hs
  rw [zero_add, algebraMap_basicOpen_eq_presheaf_map, ← hom_comp,
    appLE_map] at hcomp
  exact hcomp

theorem isStandardSmoothOfRelativeDimension_appLE_congr {U U' : Opn Y}
    {V V' : Opn X} (hU : U' = U) (hV : V' = V) (e : V ≤ f.pre U) (e' : V' ≤ f.pre U')
    (hstd : IsStandardSmoothOfRelativeDimension n
      (appLE f U V e).hom) :
    IsStandardSmoothOfRelativeDimension n
      (appLE f U' V' e').hom := by
  subst hU
  subst hV
  exact hstd
end

section
variable {X X' : Sch} (ph_ : X' ⟶ X) (r) [SmoothOfRelativeDimension r ph_]
theorem exists_affineChart_isStandardSmoothOfRelativeDimension (A0_ : Opn X) (B0_ : Opn X')
    (hB0_ : B0_ ≤ ph_ ⁻¹ᵁ A0_) (y : ↥X') (hy : y ∈ B0_) :
    ∃ A B, IsAffineOpen A ∧
      IsAffineOpen B ∧ A ≤ A0_ ∧ B ≤ B0_ ∧ y ∈ B ∧
      ∃ e : B ≤ ph_ ⁻¹ᵁ A, IsStandardSmoothOfRelativeDimension r
        (appLE ph_ A B e).hom := by
  obtain ⟨U, hU, V, hV, hyV, e, hstd⟩ :=
    (smoothOfRelativeDimension_iff r ph_).mp inferInstance y
  obtain ⟨s, hsA0, hys⟩ := hU.exists_basicOpen_le (⟨bsM ph_ y, hB0_ hy⟩ : ↥A0_) $ e hyV
  let _s0 := (appLE ph_ U V e).hom s
  have hB1eq := basicOpen_appLE ph_ e s
  have hB1le : X'.basicOpen _s0 ≤
      ph_ ⁻¹ᵁ X.basicOpen s := by
    rw [hB1eq]
    exact inf_le_right
  have hB1aff : IsAffineOpen
      (X'.basicOpen _s0) := hV.basicOpen _
  have hyB1 : y ∈ X'.basicOpen _s0 := by
    rw [hB1eq]
    exact ⟨hyV, hys⟩
  obtain ⟨t, htB0, hyt⟩ := hB1aff.exists_basicOpen_le (⟨y, hy⟩ : ↥B0_) hyB1
  have hBle :=
    le_trans (X'.basicOpen_le t) hB1le
  exact ⟨bOpn X s, bOpn X' t, hU.basicOpen s, hB1aff.basicOpen t, hsA0, htB0, hyt,
    hBle, isStandardSmoothOfRelativeDimension_appLE_basicOpen_source ph_ r hB1aff hB1le (isStandardSmoothOfRelativeDimension_appLE_basicOpen_target ph_ r hU hV e s hstd hB1le) t hBle⟩

theorem smoothOfRelativeDimension_resLE (U0_ : Opn X) (V0 : Opn X')
    (h : V0 ≤ ph_.pre U0_) :
    SmoothOfRelativeDimension r $ ph_.resLE U0_ V0 h := by
  rw [smoothOfRelativeDimension_iff]
  intro x
  have hx : opIb V0 x ∈ V0 := by
    have hmem : opIb V0 x ∈ opensRange V0.i := ⟨x, rfl⟩
    rwa [AlgebraicGeometry.Scheme.Opens.opensRange_ι] at hmem
  obtain ⟨A, B, hA, hB, hAU0, hBV0, hxB, e, hstd⟩ :=
    exists_affineChart_isStandardSmoothOfRelativeDimension ph_ r U0_ V0 h (opIb V0 x) hx
  let _a0 := ph_.resLE U0_ V0 h
  have hpre : _a0.pre (preU U0_.i A) = V0.i.pre (preU ph_ A) := by
    rw [← preimage_comp, ← preimage_comp, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
  have he' : V0.i.pre B ≤ _a0.pre (preU U0_.i A) := by
    rw [hpre]
    exact fun z hz => e hz
  refine ⟨opPre U0_ A, hA.preimage_of_isOpenImmersion U0_.i $ by simp [hAU0],
    opPre V0 B, hB.preimage_of_isOpenImmersion V0.i $ by simp [hBV0], hxB, he', ?_⟩
  rw [resLE_appLE]
  exact isStandardSmoothOfRelativeDimension_appLE_congr ph_ r (image_preimage_of_le U0_ A hAU0)
    (image_preimage_of_le V0 B hBV0) e _ hstd
end

instance instSmoothOfRelativeDimensionResLE {X X' : Sch} (ph_ : X' ⟶ X) (r : ℕ)
    [SmoothOfRelativeDimension r ph_] (U0_ : Opn X) (V0 : Opn X')
    (h : V0 ≤ ph_.pre U0_) :
    SmoothOfRelativeDimension r $ ph_.resLE U0_ V0 h :=
  smoothOfRelativeDimension_resLE ph_ r U0_ V0 h


variable {k S T : Type} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

section
variable (f : S →ₐ[k] T)
theorem map_derivation_eq_of_map_eq (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom)
    {s s' : S} (h : f s = f s') : f (D s) = f (D s') := by
  have hker : s - s' ∈ m41 f.toRingHom := by simp_all
  have hD' := hD _ hker
  rw [m208, map_sub D s s'] at hD'
  refine eq_of_sub_eq_zero ?_
  simp_all

section
variable (hf : Surjective f) (D : Derivation k S S)
noncomputable def derivationOfSurjectiveFun : T → T :=
  fun t => f $ D $ surjInv hf t

section
variable (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom)
include hD
theorem derivationOfSurjectiveFun_apply (s : S) :
    derivationOfSurjectiveFun f hf D (f s) = f (D s) := by
  exact map_derivation_eq_of_map_eq f D hD $ surjInv_eq hf $ f s

noncomputable def derivationOfSurjectiveLinearMap : T →ₗ[k] T where
  toFun := derivationOfSurjectiveFun f hf D
  map_add' := by
    intro t t'
    obtain ⟨a, rfl⟩ := hf t
    obtain ⟨b, rfl⟩ := hf t'
    rw [← map_add f a b]
    simp only [derivationOfSurjectiveFun_apply f hf D hD]
    rw [map_add D a b, map_add f (D a) $ D b]
  map_smul' := by
    intro c t
    obtain ⟨a, rfl⟩ := hf t
    have h1 := map_smul f c a
    have h2 : D (c • a) = c • D a := by
      simp
    have h3 := map_smul f c $ D a
    rw [← h1]
    simp only [derivationOfSurjectiveFun_apply f hf D hD]
    rw [h2]
    exact h3

theorem derivationOfSurjectiveFun_one :
    derivationOfSurjectiveFun f hf D 1 = 0 := by
  rw [sy_ $ map_one f, derivationOfSurjectiveFun_apply f hf D hD, D.map_one_eq_zero, map_zero]

theorem derivationOfSurjectiveFun_mul :
    ∀ a b : T, derivationOfSurjectiveFun f hf D (a * b)
      = a • derivationOfSurjectiveFun f hf D b + b • derivationOfSurjectiveFun f hf D a := by
  intro a b
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  rw [← map_mul f x y]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [D.leibniz]
  simp [smul_eq_mul]

noncomputable def derivationOfSurjective :
    Derivation k T T where
  toLinearMap := derivationOfSurjectiveLinearMap f hf D hD
  map_one_eq_zero' := derivationOfSurjectiveFun_one f hf D hD
  leibniz' := derivationOfSurjectiveFun_mul f hf D hD

@[simp]
theorem derivationOfSurjective_apply (s : S) :
    derivationOfSurjective f hf D hD (f s) = f (D s) :=
  derivationOfSurjectiveFun_apply f hf D hD s
end
end
end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

section
variable {k : Type} [CommRing k] {S : Type} [CommRing S] [Algebra k S]
theorem derivation_apply_mem_of_mem_span
    (D : Derivation k S S) {G : Set S} {T : Ideal S} (hGT : Ideal.span G ≤ T)
    (hD : ∀ g ∈ G, D g ∈ T) {x : S} (hx : x ∈ Ideal.span G) : D x ∈ T := by
  induction hx using span_induction with
  | mem g hg => exact hD g hg
  | zero => simp
  | add a b _ _ iha ihb => simpa using m60 T iha ihb
  | smul a b hb ihb =>
      have hD' : D (a • b) = a • D b + b • D a := by simp_all
      rw [hD', smul_eq_mul, smul_eq_mul]
      exact m60 T (mul_mem_left T a ihb) $ mul_mem_right (D a) T $ hGT hb

theorem derivation_apply_mem_pow_of_mem_pow_succ (J : Ideal S) (D : Derivation k S S) :
    ∀ n : ℕ, ∀ x ∈ J ^ (n + 1), D x ∈ J ^ n := by
  intro n
  induction n with
  | zero =>
      intro x _
      rw [pow_zero, one_eq_top]
      exact mem_top
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine mul_induction_on hx ?_ ?_
      intro a ha b hb
      simp [leibniz, smul_eq_mul]
      refine m60 _ (mul_mem_right _ _ ha) ?_
      have hb' := mul_mem_mul (ih a ha) hb
      rw [← pow_succ] at hb'
      rwa [mul_comm b $ D a]
      intro a b ha hb
      rw [map_add]
      exact m60 _ ha hb
end

section
variable (k : Type) [CommRing k] {S : Type} [CommRing S] [Algebra k S]
section
variable (J : Ideal S)
def derivIdeal : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D : Derivation k S S, ∃ y ∈ J, D y = x}

theorem derivIdeal_eq_sup_span :
    derivIdeal k J = J ⊔ Ideal.span {x : S | ∃ D : Derivation k S S, ∃ y ∈ J, D y = x} := rfl

section
variable (D : Derivation k S S)
theorem derivation_apply_mem_derivIdeal {x : S} (hx : x ∈ J) :
    D x ∈ derivIdeal k J := by
  rw [derivIdeal_eq_sup_span]
  exact mem_sup_right $ m100 ⟨D, x, hx, rfl⟩

theorem derivation_apply_mem_pow_mul_derivIdeal :
    ∀ n : ℕ, ∀ x ∈ J ^ (n + 1), D x ∈ J ^ n * derivIdeal k J := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx' := by simpa using hx
      simpa using (derivation_apply_mem_derivIdeal k J D hx')
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine mul_induction_on hx ?_ ?_
      intro a ha b hb
      have hL : D (a * b) = a * D b + b * D a := by simp_all
      rw [hL]
      refine m60 _ (mul_mem_mul ha $ derivation_apply_mem_derivIdeal k J D hb) ?_
      have h2 :=
        mul_mem_mul hb $ ih a ha
      have h3 : J * (J ^ n * derivIdeal k J) = J ^ (n + 1) * derivIdeal k J := by
        rw [← mul_assoc, pow_succ, mul_comm J $ J ^ n]
      rwa [h3] at h2
      intro y z hy hz
      simpa using m60 _ hy hz
end

theorem le_derivIdeal : J ≤ derivIdeal k J := by
  rw [derivIdeal_eq_sup_span]
  exact le_sup_left
end

theorem derivIdeal_le_iff
    (J K : Ideal S) :
    derivIdeal k J ≤ K ↔ J ≤ K ∧ ∀ D : Derivation k S S, ∀ x ∈ J, D x ∈ K := by
  rw [derivIdeal_eq_sup_span, sup_le_iff, span_le]
  constructor
  rintro ⟨h1, h2⟩
  exact ⟨h1, fun D x hx => h2 ⟨D, x, hx, rfl⟩⟩
  rintro ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  rintro x ⟨D, y, hy, rfl⟩
  exact h2 D y hy

theorem derivIdeal_iSup_le
    {ι : Sort*} (J : ι → Ideal S) :
    derivIdeal k (⨆ i, J i) ≤ ⨆ i, derivIdeal k (J i) := by
  have hspan : (⨆ i, J i) = Ideal.span (⋃ i, (J i)) := iSup_eq_span J
  have hle :=
    iSup_le fun i => (le_derivIdeal k $ J i).trans $ le_iSup (fun j => derivIdeal k $ J j) i
  rw [derivIdeal_le_iff]
  refine ⟨hle, ?_⟩
  intro D x hx
  rw [hspan] at hx
  refine derivation_apply_mem_of_mem_span D ?_ ?_ hx
  rwa [← hspan]
  intro g hg
  obtain ⟨i, hi⟩ := mp_ mem_iUnion hg
  exact le_iSup (fun j => derivIdeal k $ J j) i
    (derivation_apply_mem_derivIdeal k (J i) D hi)

section
variable (J : Ideal S) (n : ℕ)
theorem derivIdeal_pow_succ_le : derivIdeal k (J ^ (n + 1)) ≤ J ^ n * derivIdeal k J := by
  rw [derivIdeal_le_iff]
  exact ⟨by rw [pow_succ]; exact Ideal.mul_le.mpr fun _ ha _ hb => mul_mem_mul ha $ le_derivIdeal k J hb,
    fun D x hx => derivation_apply_mem_pow_mul_derivIdeal k J D n x hx⟩

theorem derivIdeal_pow_succ_le_pow : derivIdeal k (J ^ (n + 1)) ≤ J ^ n := by
  rw [derivIdeal_le_iff]
  constructor
  intro x hx
  rw [pow_succ] at hx
  refine mul_induction_on hx ?_ ?_
  intro m hm y _
  exact mul_mem_right _ _ hm
  intro a b ha hb
  exact m60 _ ha hb
  intro D x hx
  exact derivation_apply_mem_pow_of_mem_pow_succ J D n x hx
end

theorem derivIdeal_mul_le
    (I J : Ideal S) :
    derivIdeal k (I * J) ≤ I * derivIdeal k J ⊔ J * derivIdeal k I := by
  rw [derivIdeal_le_iff]
  constructor
  rw [mul_le]
  intro r hr s hs
  exact mem_sup_left $ mul_mem_mul hr $ le_derivIdeal k J hs
  intro D x hx
  refine mul_induction_on hx ?_ ?_
  intro m hm n hn
  simp [leibniz, smul_eq_mul]
  exact m60 _ (mem_sup_left $ mul_mem_mul hm $ derivation_apply_mem_derivIdeal k J D hn) $ mem_sup_right $ mul_mem_mul hn $ derivation_apply_mem_derivIdeal k I D hm
  intro a b ha hb
  rw [map_add]
  exact m60 _ ha hb

theorem derivIdeal_mono :
    Monotone (derivIdeal k : Ideal S → Ideal S) := by
  intro I J h
  rw [derivIdeal_le_iff]
  exact ⟨h.trans $ le_derivIdeal k J, fun D x hx => derivation_apply_mem_derivIdeal k J D $ h hx⟩

theorem derivIdeal_le_pow_of_le_pow
    {I P : Ideal S} {n : ℕ} (h : I ≤ P ^ n) : derivIdeal k I ≤ P ^ (n - 1) := by
  cases n with
  | zero =>
      have hP : P ^ (0 - 1) = (⊤) := by simp_all
      exact le_of_le_of_eq le_top hP.symm
  | succ m =>
      have hm : m + 1 - 1 = m := by omega
      exact le_of_le_of_eq ((derivIdeal_mono k h).trans $ derivIdeal_pow_succ_le_pow k P m) $ congrArg (fun i => P ^ i) hm.symm

theorem derivIdeal_le_derivIdeal
    {I J : Ideal S} (h : I ≤ J) : derivIdeal k I ≤ derivIdeal k J :=
  derivIdeal_mono k h

theorem derivIdeal_bot :
    derivIdeal k (⊥ : Ideal S) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [derivIdeal_le_iff]
  refine ⟨le_rfl, fun D x hx => ?_⟩
  rw [mem_bot] at hx
  subst hx
  simp
end

def derivIdealIterate (k : Type) [CommRing k] {S : Type} [CommRing S] [Algebra k S] :
    ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => derivIdeal k $ derivIdealIterate k r J

section
variable (k : Type) [CommRing k] {S : Type} [CommRing S] [Algebra k S]
theorem derivIdealIterate_zero
    (J : Ideal S) : derivIdealIterate k 0 J = J := rfl

theorem derivIdealIterate_one
    (J : Ideal S) : derivIdealIterate k 1 J = derivIdeal k J := rfl

section
variable (r : ℕ) (J : Ideal S)
theorem derivIdealIterate_succ :
    derivIdealIterate k (r + 1) J = derivIdeal k (derivIdealIterate k r J) := rfl

theorem le_derivIdealIterate : J ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact (derivIdealIterate_zero k J).ge
  | succ r ih =>
      rw [derivIdealIterate_succ]
      exact ih.trans $ le_derivIdeal k _
end

theorem derivIdealIterate_le_pow_of_le_pow {I P : Ideal S} {n : ℕ} (r : ℕ) (h : I ≤ P ^ n) :
    derivIdealIterate k r I ≤ P ^ (n - r) := by
  induction r with
  | zero =>
      rwa [derivIdealIterate_zero, m130]
  | succ r ih =>
      rw [derivIdealIterate_succ]
      let _a0 := n - r
      have h2 : derivIdeal k (P ^ _a0) ≤ P ^ (_a0 - 1) := by
        obtain _ | m := _a0
        have h : (P ^ (0 - 1) : Ideal S) = ⊤ := by simp
        exact le_top.trans h.ge
        have key : derivIdeal k (P ^ (m + 1)) ≤ P ^ m := by
          rw [derivIdeal_le_iff]
          refine ⟨?_,
            fun D x hx => derivation_apply_mem_pow_of_mem_pow_succ P D m x hx⟩
          rw [pow_succ]
          exact Ideal.mul_le.mpr fun r hr s _ => mul_mem_right s _ hr
        exact key
      have h3 : n - r - 1 = n - (r + 1) := by omega
      rw [h3] at h2
      exact (derivIdeal_mono k ih).trans h2

theorem derivIdealIterate_add
    (r s : ℕ) (J : Ideal S) :
    derivIdealIterate k (r + s) J = derivIdealIterate k r (derivIdealIterate k s J) := by
  induction r with
  | zero => rw [zero_add, derivIdealIterate_zero]
  | succ r ih => rw [succ_add, derivIdealIterate_succ, derivIdealIterate_succ, ih]

theorem derivIdealIterate_le_of_le
    {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    derivIdealIterate k r J ≤ derivIdealIterate k r' J := by
  obtain ⟨d, rfl⟩ := exists_eq_add_of_le h
  rw [Nat.add_comm r d, derivIdealIterate_add]
  exact le_derivIdealIterate k d _
end


variable {k : Type} {S : Type} {S' : Type}

section
variable [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
section
variable (M : Submonoid S) [IsLocalization M S']
include M
theorem map_derivIdeal_le
    (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) ≤
      derivIdeal k (Ideal.map (algebraMap S S') J) := by
  let _a0 := algebraMap S S'
  rw [map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  intro x hx
  exact Ideal.mem_comap.mpr $ le_derivIdeal k _ $ mem_map_of_mem _a0 hx
  intro D x hx
  refine Ideal.mem_comap.mpr ?_
  have h := derivation_apply_mem_derivIdeal k (m6 _a0 J)
    (D.mapToLocalization (S' := S') M) $ mem_map_of_mem _a0 hx
  rwa [Derivation.mapToLocalization_algebraMap] at h

section
variable [FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S)
theorem derivIdeal_map_le :
    derivIdeal k (Ideal.map (algebraMap S S') J) ≤
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨map_mono $ le_derivIdeal k J, ?_⟩
  intro D x hx
  rw [mem_map_algebraMap_iff M S'] at hx
  obtain ⟨⟨a, m⟩, hax⟩ := hx
  let _s1 := algebraMap S S' a
  let _a0 := algebraMap S S' m
  have h1 : D (x * _a0) = D _s1 := by rw [hax]
  rw [leibniz, smul_eq_mul, smul_eq_mul] at h1
  have hA : D _s1 ∈ (m6 (algebraMap S S') $ derivIdeal k J) :=
    by
    obtain ⟨m, D0_, hm⟩ := Derivation.exists_derivation_mul_eq_of_isLocalization (R := k) M D
    refine mp_ (unit_mul_mem_iff_mem _ $ map_units S' m) ?_
    rw [hm a]
    exact mem_map_of_mem _ $ derivation_apply_mem_derivIdeal k J D0_ a.2
  let _s0 := _a0
  refine mp_ (unit_mul_mem_iff_mem _ $ map_units S' m)
    (mp_ (unit_mul_mem_iff_mem _ $ map_units S' m) ?_)
  have h2 : _a0 * (_a0 * D x) =
      _a0 * D _s1 -
        algebraMap S S' a * D _s0 := by
    linear_combination _s0 * h1 - (D _s0) * hax
  rw [h2]
  exact sub_mem (mul_mem_left _ _ hA) $ mul_mem_right _ _ $ mem_map_of_mem _ $ le_derivIdeal k J a.2

theorem map_derivIdeal :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  le_antisymm (map_derivIdeal_le M J) $ derivIdeal_map_le M J
end
end

theorem map_derivIdeal_away (g : S) [IsLocalization.Away g S']
    [FinitePresentation S $ KaehlerDifferential k S] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  map_derivIdeal (powers g) J
end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

open IsLocalRing

variable {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

section
variable (I : Ideal R)
noncomputable def idealOrder : ENat :=
  sSup $ (fun n : ℕ => (n : ENat)) '' {n : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ n}

theorem le_idealOrder_iff (n : ℕ) :
    (n : ENat) ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R ^ n := by
  have hdef : idealOrder I
      = sSup ((fun k : ℕ => (k : ENat)) '' {k : ℕ | I ≤ m16 R ^ k}) := rfl
  constructor
  intro h
  by_contra hI
  rw [hdef] at h
  have hn : n ≠ 0 := by
    rintro rfl
    apply hI
    rw [pow_zero, one_eq_top]
    exact le_top
  have hsup : sSup ((fun k : ℕ => (k : ENat)) '' {k : ℕ | I ≤ m16 R ^ k})
      ≤ ((n - 1 : ℕ) : ENat) := by
    apply sSup_le
    rintro x ⟨k, hk, rfl⟩
    have hkn : k < n := by
      by_contra hkn
      push Not at hkn
      exact hI $ le_trans hk $ pow_le_pow_right hkn
    have hk2 : k ≤ n - 1 := by omega
    dsimp
    exact_mod_cast hk2
  have hcon : n ≤ n - 1 := by exact_mod_cast h.trans hsup
  omega
  intro h
  rw [hdef]
  exact le_sSup ⟨n, h, rfl⟩

theorem idealOrder_eq_top_iff :
    idealOrder I = ⊤ ↔ ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n := by
  constructor
  intro h n
  rw [← le_idealOrder_iff, h]
  exact le_top
  intro h
  rw [eq_top_iff_forall_ge]
  intro n
  exact mpr_ (le_idealOrder_iff I n) $ h n

theorem mul_idealOrder_le_idealOrder_pow (c : ℕ) :
    (c : ENat) * idealOrder I ≤ idealOrder (I ^ c) := by
  rcases m73 c with rfl | hc
  simp_all
  have hc1 := hc
  rcases eq_or_ne (idealOrder I) ⊤ with hI | hI
  have hIall :=
    (idealOrder_eq_top_iff I).mp hI
  have htop : idealOrder (I ^ c) = ⊤ := by
    rw [idealOrder_eq_top_iff]
    intro n
    have h1 : I ^ c ≤ I ^ 1 := pow_le_pow_right hc1
    rw [pow_one] at h1
    exact le_trans h1 $ hIall n
  rw [htop]
  exact le_top
  obtain ⟨k, hk⟩ := mp_ ne_top_iff_exists hI
  rw [← hk, ← cast_mul, le_idealOrder_iff]
  calc I ^ c ≤ (m16 R ^ k) ^ c :=
        pow_right_mono (mp_ (le_idealOrder_iff I k) hk.le) c
    _ = m16 R ^ (c * k) := by rw [← pow_mul, mul_comm k c]

theorem one_le_idealOrder_iff :
    1 ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R := by
  have h := le_idealOrder_iff I 1
  rwa [cast_one, pow_one] at h

theorem one_le_idealOrder_iff_ne_top :
    1 ≤ idealOrder I ↔ I ≠ ⊤ := by
  rw [one_le_idealOrder_iff]
  constructor
  intro h hI
  rw [hI] at h
  exact (maximalIdeal.isMaximal R).ne_top $ mp_ top_le_iff h
  intro h
  exact le_maximalIdeal h

theorem idealOrder_eq_zero_iff :
    idealOrder I = 0 ↔ ¬ I ≤ IsLocalRing.maximalIdeal R := by
  rw [← one_le_idealOrder_iff, not_le, Order.lt_one_iff]
end

section
variable (f : R →+* S) (hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S)
include hf
theorem map_maximalIdeal_pow_le_pow (n : ℕ) :
    ((IsLocalRing.maximalIdeal R) ^ n).map f ≤ (IsLocalRing.maximalIdeal S) ^ n := by
  induction n with
  | zero =>
      have hS : (m16 S) ^ 0 = (⊤) := by simp_all
      rw [hS]
      exact le_top
  | succ n ih =>
      rw [pow_succ, pow_succ, m220]
      exact mul_mono ih hf

theorem idealOrder_le_idealOrder_map (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map f) := by
  refine mp_ forall_natCast_le_iff_le fun n hn => ?_
  rw [le_idealOrder_iff] at hn ⊢
  exact le_trans (map_mono hn) $ map_maximalIdeal_pow_le_pow f hf n
end

section
variable [hv0_0 : IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥)
include hv0_0 hI
theorem idealOrder_ne_top_of_ne_bot :
    idealOrder I ≠ ⊤ := by
  intro h
  rw [idealOrder_eq_top_iff] at h
  refine hI $ mp_ le_bot_iff ?_
  rw [← iInf_pow_eq_bot_of_isLocalRing (I := m16 R) (isMaximal R).ne_top]
  exact le_iInf h

theorem exists_idealOrder_eq_coe :
    ∃ n : ℕ, idealOrder I = (n : ENat) := by
  obtain ⟨n, hn⟩ := mp_ ne_top_iff_exists $ idealOrder_ne_top_of_ne_bot hI
  exact ⟨n, sy_ hn⟩
end

theorem enat_add_le_of_forall_natCast_add_le {a b c : ENat}
    (h : ∀ m n : ℕ, (m : ENat) ≤ a → (n : ENat) ≤ b → ((m + n : ℕ) : ENat) ≤ c) : a + b ≤ c := by
  rcases eq_or_ne a ⊤ with rfl | ha
  have hc : c = ⊤ := by
    rw [eq_top_iff_forall_ge]
    intro n
    simpa using (h n 0 le_top $ by simp)
  rw [hc]
  exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  have hc : c = ⊤ := by
    rw [eq_top_iff_forall_ge]
    intro n
    simpa using (h 0 n (by simp) le_top)
  rw [hc]
  exact le_top
  lift a to ℕ using ha
  lift b to ℕ using hb
  simpa using (h a b le_rfl le_rfl)

theorem add_idealOrder_le_idealOrder_mul (I J : Ideal R) :
    idealOrder I + idealOrder J ≤ idealOrder (I * J) := by
  refine enat_add_le_of_forall_natCast_add_le fun m n hm hn => ?_
  rw [le_idealOrder_iff] at hm hn ⊢
  rw [pow_add]
  exact mul_mono hm hn

theorem idealOrder_le_of_le {I J : Ideal R} (h : I ≤ J) : idealOrder J ≤ idealOrder I := by
  have hI : idealOrder I
      = sSup ((fun k : ℕ => (k : ENat)) '' {k : ℕ | I ≤ m16 R ^ k}) := rfl
  have hJ : idealOrder J
      = sSup ((fun k : ℕ => (k : ENat)) '' {k : ℕ | J ≤ m16 R ^ k}) := rfl
  rw [hI, hJ]
  apply sSup_le
  rintro x ⟨n, hn, rfl⟩
  exact le_sSup ⟨n, le_trans h hn, rfl⟩

theorem idealOrder_sup (I J : Ideal R) :
    idealOrder (I ⊔ J) = min (idealOrder I) (idealOrder J) := by
  apply le_antisymm
  exact le_min (idealOrder_le_of_le le_sup_left)
    (idealOrder_le_of_le le_sup_right)
  apply mp_ forall_natCast_le_iff_le
  intro n hn
  rw [le_min_iff] at hn
  rw [le_idealOrder_iff]
  exact sup_le (mp_ (le_idealOrder_iff I n) hn.1) $ mp_ (le_idealOrder_iff J n) hn.2

theorem idealOrder_top : idealOrder (⊤ : Ideal R) = 0 := by
  by_contra h
  have h1 : (1 : ENat) ≤ idealOrder (⊤ : Ideal R) := by
    rwa [Order.one_le_iff_ne_zero]
  rw [one_le_idealOrder_iff_ne_top] at h1
  exact h1 rfl

theorem idealOrder_bot : idealOrder (⊥ : Ideal R) = ⊤ := by
  rw [idealOrder_eq_top_iff]
  intro n
  exact bot_le

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

open IsLocalRing

section
variable (k : Type) [CommRing k] {R : Type} [CommRing R] [Algebra k R] {ι : Type}
noncomputable def eulerDerivation [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) : Derivation k R R :=
  ∑ i, x i • D i

theorem sum_smul_derivation_apply (s : Finset ι) (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    (∑ i ∈ s, x i • D i) a = ∑ i ∈ s, x i * D i a :=by simp_all
section
variable [Fintype ι]
section
variable (x : ι → R) (D : ι → Derivation k R R) (a : R)
theorem eulerDerivation_apply :
    eulerDerivation k x D a = ∑ i, x i * D i a := by
  exact sum_smul_derivation_apply k univ x D a

theorem eulerDerivation_apply_mem_span :
    eulerDerivation k x D a ∈ Ideal.span (Set.range x) := by
  rw [eulerDerivation_apply]
  exact m133 _ fun i _ => mul_mem_right _ _ $ m100 ⟨i, rfl⟩
end

section
variable [hv7_0 : DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R) (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
include hv7_0 hD
theorem eulerDerivation_apply_generator (j : ι) :
    eulerDerivation k x D (x j) = x j := by
  rw [eulerDerivation_apply]
  simp [hD]

theorem eulerDerivation_sub_self_mem_sq {f : R}
    (hf : f ∈ Ideal.span (Set.range x)) :
    eulerDerivation k x D f - f ∈ Ideal.span (Set.range x) ^ 2 := by
  induction hf using span_induction with
  | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      rw [eulerDerivation_apply_generator k x D hD j, sub_self]
      exact m97 _
  | zero =>
      rw [map_zero, sub_zero]
      exact m97 _
  | add a b _ _ iha ihb =>
      have key : eulerDerivation k x D (a + b) - (a + b)
          = (eulerDerivation k x D a - a) + (eulerDerivation k x D b - b) := by
        rw [map_add]
        ring
      rw [key]
      exact m60 _ iha ihb
  | smul c a ha iha =>
      have key : eulerDerivation k x D (c • a) - c • a
          = c * (eulerDerivation k x D a - a) + a * eulerDerivation k x D c := by
        rw [smul_eq_mul, leibniz, smul_eq_mul, smul_eq_mul]
        ring
      rw [key]
      refine m60 _ (mul_mem_left _ _ iha) ?_
      have h2 := mul_mem_mul ha $ eulerDerivation_apply_mem_span k x D c
      rwa [← pow_two] at h2

theorem forall_eulerDerivation_sub_natCast_mul_mem (r : ℕ) :
    ∀ f : R, f ∈ Ideal.span (Set.range x) ^ r →
      eulerDerivation k x D f - (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  induction r with
  | zero =>
      intro f _
      have h := eulerDerivation_apply_mem_span k x D f
      simpa using h
  | succ r ih =>
      intro f hf
      rw [pow_succ] at hf
      refine mul_induction_on hf ?_ ?_
      intro a ha b hb
      let _a0 := m17 (m30 x) ^ (r + 2)
      let _a1 := eulerDerivation k x D b - b
      have h1 : a * _a1 ∈ _a0 := by
        have h := mul_mem_mul ha $ eulerDerivation_sub_self_mem_sq k x D hD hb
        rwa [← pow_add] at h
      let _m0 := eulerDerivation k x D a - (r : R) * a
      have h2 : _m0 * b
          ∈ _a0 := by
        have hb1 : b ∈ m17 (m30 x) ^ 1 := by rwa [pow_one]
        have h := mul_mem_mul (ih a ha) hb1
        have e : r + 1 + 1 = r + 2 := by omega
        rwa [← pow_add, e] at h
      have key : eulerDerivation k x D (a * b) - ((r + 1 : ℕ) : R) * (a * b)
          = a * _a1 + _m0 * b := by
        rw [leibniz, smul_eq_mul, smul_eq_mul]
        push_cast
        ring
      rw [key]
      exact m60 _ h1 h2
      intro y z hy hz
      have key : eulerDerivation k x D (y + z) - ((r + 1 : ℕ) : R) * (y + z)
          = eulerDerivation k x D y - ((r + 1 : ℕ) : R) * y
            + (eulerDerivation k x D z - ((r + 1 : ℕ) : R) * z) := by
        rw [map_add]
        ring
      rw [key]
      exact m60 _ hy hz

section
variable {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
include hr
theorem mem_pow_succ_of_deriv_mem_pow
    {f : R} (hf : f ∈ Ideal.span (Set.range x) ^ r)
    (hdf : ∀ i, D i f ∈ Ideal.span (Set.range x) ^ r) :
    f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  let _a0 := m17 (m30 x) ^ (r + 1)
  have hgen : ∀ i, x i * D i f ∈ _a0 := by
    intro i
    have hx1 : x i ∈ m17 (m30 x) ^ 1 := by
      rw [pow_one]
      exact m100 ⟨i, rfl⟩
    have h := Ideal.mul_mem_mul hx1 $ hdf i
    rwa [← pow_add, Nat.add_comm 1 r] at h
  have h1 : eulerDerivation k x D f ∈ _a0 := by
    rw [eulerDerivation_apply]
    exact m133 _ fun i _ => hgen i
  have h3 := by
    simpa using (m162 _ h1 $ forall_eulerDerivation_sub_natCast_mul_mem k x D hD r f hf)
  obtain ⟨u, hu⟩ := hr
  have key : (↑u⁻¹) * (r * f) = f := by
    rw [← hu, ← mul_assoc, u.inv_mul, one_mul]
  rw [← key]
  exact mul_mem_left _ _ h3

theorem not_derivIdeal_le_pow
    {I : Ideal R} (h1 : I ≤ Ideal.span (Set.range x) ^ r)
    (h2 : ¬ I ≤ Ideal.span (Set.range x) ^ (r + 1)) :
    ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r := by
  intro h
  apply h2
  intro f hf
  exact mem_pow_succ_of_deriv_mem_pow k x D hD hr (h1 hf)
    (fun i => h $ derivation_apply_mem_derivIdeal k I (D i) hf)
end
end
end
end

theorem eq_natCast_of_le_of_not_succ_le (n : ℕ) (a : ENat) (h1 : (n : ENat) ≤ a)
    (h2 : ¬ ((n + 1 : ℕ) : ENat) ≤ a) : a = (n : ENat) := by
  rcases eq_top_or_lt_top a with rfl | hlt
  exact absurd le_top h2
  lift a to ℕ using hlt.ne
  have hn : n ≤ a := by exact_mod_cast h1
  have hn2 : ¬ (n + 1 ≤ a) := by
    intro hc
    exact h2 $ by exact_mod_cast hc
  have ha : a = n := by omega
  exact_mod_cast ha

section
variable (k : Type) [CommRing k] {R : Type} [CommRing R] [IsLocalRing R] [Algebra k R] {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R) (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R) (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) {I : Ideal R} {r : ℕ}
include hD hx hunit
theorem idealOrder_derivIdeal_of_isUnit_natCast (hr : 1 ≤ r) (hI : idealOrder I = (r : ENat)) :
    idealOrder (derivIdeal k I) = ((r - 1 : ℕ) : ENat) := by
  have hIr := mp_ (le_idealOrder_iff I r) hI.ge
  have hIr1 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (r + 1) := by
    intro hc
    have h := mpr_ (le_idealOrder_iff I $ r + 1) hc
    rw [hI] at h
    have h' : r + 1 ≤ r := by exact_mod_cast h
    omega
  have hnot : ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r :=
    not_derivIdeal_le_pow k x D hD (hunit r hr) (by rw [hx]; exact hIr) (by rw [hx]; exact hIr1)
  let _a0 := r - 1
  refine eq_natCast_of_le_of_not_succ_le (r - 1) _ ((le_idealOrder_iff _ $ r - 1).mpr $ derivIdeal_le_pow_of_le_pow k hIr) ?_
  intro hc
  have h := mp_ (le_idealOrder_iff _ $ _a0 + 1) hc
  apply hnot
  rw [hx]
  have hrr : _a0 + 1 = r := by omega
  rwa [hrr] at h

theorem idealOrder_derivIdealIterate_of_isUnit_natCast (hI : idealOrder I = (r : ENat)) {j : ℕ} (hj : j ≤ r) :
    idealOrder (derivIdealIterate k j I) = ((r - j : ℕ) : ENat) := by
  revert hj
  induction j with
  | zero =>
      intro _
      rwa [derivIdealIterate_zero, m130]
  | succ j ih =>
      intro hj
      have hj' : j ≤ r := by omega
      have h1 : 1 ≤ r - j := by omega
      have h := idealOrder_derivIdeal_of_isUnit_natCast k x D hD hx hunit h1 $ ih hj'
      rw [derivIdealIterate_succ]
      have heq : r - j - 1 = r - (j + 1) := by omega
      rwa [heq] at h
end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

variable (k : Type) [CommRing k] {S : Type} [CommRing S] [Algebra k S]

section
variable (P : Ideal S)
def tangentDerivations : Submodule S $ Derivation k S S where
  carrier := {D : Derivation k S S | ∀ x ∈ P, D x ∈ P}
  add_mem' := by
    intro D D' hD hD' x hx
    have h := P.add_mem (hD x hx) $ hD' x hx
    simpa using h
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro a D hD x hx
    have h := mul_mem_left P a $ hD x hx
    simpa [smul_eq_mul] using h

theorem mem_tangentDerivations (D : Derivation k S S) :
    D ∈ tangentDerivations k P ↔ ∀ x ∈ P, D x ∈ P := m22

theorem smul_mem_tangentDerivations {p : S} (hp : p ∈ P)
    (D : Derivation k S S) : p • D ∈ tangentDerivations k P := by
  rw [mem_tangentDerivations]
  intro x _
  simpa [smul_eq_mul] using (mul_mem_right (D x) P hp)
end

section
variable (P J : Ideal S)
def logDerivIdeal : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x}

theorem logDerivIdeal_eq_sup_span :
    logDerivIdeal k P J =
      J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x} := rfl

theorem derivation_apply_mem_logDerivIdeal (D : Derivation k S S)
    (hD : D ∈ tangentDerivations k P) {x : S} (hx : x ∈ J) :
    D x ∈ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span]
  exact mem_sup_right $ m100 ⟨D, hD, x, hx, rfl⟩

theorem le_logDerivIdeal : J ≤ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span]
  exact le_sup_left
end

theorem logDerivIdeal_le_iff (P J K : Ideal S) :
    logDerivIdeal k P J ≤ K ↔
      J ≤ K ∧ ∀ D ∈ tangentDerivations k P, ∀ x ∈ J, D x ∈ K := by
  rw [logDerivIdeal_eq_sup_span, sup_le_iff, span_le]
  constructor
  rintro ⟨h1, h2⟩
  exact ⟨h1, fun D hD x hx => h2 ⟨D, hD, x, hx, rfl⟩⟩
  rintro ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  rintro x ⟨D, hD, y, hy, rfl⟩
  exact h2 D hD y hy

theorem logDerivIdeal_mono (P : Ideal S) : Monotone (logDerivIdeal k P : Ideal S → Ideal S) := by
  intro I J h
  rw [logDerivIdeal_le_iff]
  exact ⟨h.trans $ le_logDerivIdeal k P J, fun D hD x hx => derivation_apply_mem_logDerivIdeal k P J D hD $ h hx⟩

theorem logDerivIdeal_le_logDerivIdeal (P : Ideal S) {I J : Ideal S} (h : I ≤ J) :
    logDerivIdeal k P I ≤ logDerivIdeal k P J :=
  logDerivIdeal_mono k P h

theorem logDerivIdeal_le_derivIdeal (P J : Ideal S) :
    logDerivIdeal k P J ≤ derivIdeal k J := by
  rw [logDerivIdeal_le_iff]
  exact ⟨le_derivIdeal k J, fun D _ x hx => derivation_apply_mem_derivIdeal k J D hx⟩

theorem logDerivIdeal_iSup_le {ι : Sort*} (P : Ideal S) (J : ι → Ideal S) :
    logDerivIdeal k P (⨆ i, J i) ≤ ⨆ i, logDerivIdeal k P (J i) := by
  rw [logDerivIdeal_le_iff]
  refine ⟨iSup_mono fun i => le_logDerivIdeal k P $ J i, ?_⟩
  intro D hD x hx
  refine iSup_induction
    (motive := fun z => D z ∈ ⨆ i, logDerivIdeal k P (J i)) J hx ?_ ?_ ?_
  intro i y hy
  exact le_iSup (fun i => logDerivIdeal k P (J i)) i
    (derivation_apply_mem_logDerivIdeal k P (J i) D hD hy)
  simpa only [map_zero] using m97 (⨆ i, logDerivIdeal k P (J i))
  intro a b ha hb
  simpa only [map_add] using m60 (⨆ i, logDerivIdeal k P (J i)) ha hb

theorem logDerivIdeal_top_eq_derivIdeal (J : Ideal S) :
    logDerivIdeal k (⊤ : Ideal S) J = derivIdeal k J := by
  refine le_antisymm (logDerivIdeal_le_derivIdeal k ⊤ J) ?_
  rw [derivIdeal_le_iff]
  refine ⟨le_logDerivIdeal k ⊤ J, fun D x hx => ?_⟩
  refine derivation_apply_mem_logDerivIdeal k ⊤ J D ?_ hx
  rw [mem_tangentDerivations]
  intro y _
  exact mem_top

theorem mem_tangentDerivations_span_singleton (x : S) (D : Derivation k S S) :
    D ∈ tangentDerivations k (Ideal.span ({x} : Set S)) ↔
      D x ∈ Ideal.span ({x} : Set S) := by
  rw [mem_tangentDerivations]
  constructor
  intro hD
  exact hD x $ m100 $ mem_singleton x
  intro hD y hy
  refine derivation_apply_mem_of_mem_span D le_rfl ?_ hy
  intro g hg
  rw [mem_singleton_iff] at hg
  subst hg
  exact hD

def logDerivIdealIterate (P : Ideal S) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => logDerivIdeal k P $ logDerivIdealIterate P r J

theorem logDerivIdealIterate_zero (P J : Ideal S) : logDerivIdealIterate k P 0 J = J := rfl

section
variable (P : Ideal S)
section
variable (r : ℕ)
theorem logDerivIdealIterate_succ (J : Ideal S) :
    logDerivIdealIterate k P (r + 1) J = logDerivIdeal k P (logDerivIdealIterate k P r J) := rfl


theorem le_logDerivIdealIterate (J : Ideal S) :
    J ≤ logDerivIdealIterate k P r J := by
  induction r with
  | zero => exact (logDerivIdealIterate_zero k P J).ge
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      exact ih.trans $ le_logDerivIdeal k P _

theorem logDerivIdealIterate_mono :
    Monotone (logDerivIdealIterate k P r : Ideal S → Ideal S) := by
  induction r with
  | zero =>
      intro I J h
      rwa [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
  | succ r ih =>
      intro I J h
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact logDerivIdeal_mono k P $ ih h
end

theorem logDerivIdealIterate_add (r s : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + s) J =
      logDerivIdealIterate k P r (logDerivIdealIterate k P s J) := by
  induction r with
  | zero => rw [zero_add, logDerivIdealIterate_zero]
  | succ r ih => rw [succ_add, logDerivIdealIterate_succ, logDerivIdealIterate_succ, ih]

theorem logDerivIdealIterate_le_of_le {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    logDerivIdealIterate k P r J ≤ logDerivIdealIterate k P r' J := by
  obtain ⟨d, rfl⟩ := exists_eq_add_of_le h
  rw [Nat.add_comm r d, logDerivIdealIterate_add]
  exact le_logDerivIdealIterate k P d _
end

theorem logDerivIdealIterate_iSup_le {ι : Sort*} (P : Ideal S) (r : ℕ) (J : ι → Ideal S) :
    logDerivIdealIterate k P r (⨆ i, J i) ≤ ⨆ i, logDerivIdealIterate k P r (J i) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      refine le_trans (logDerivIdeal_mono k P ih) ?_
      exact le_trans (logDerivIdeal_iSup_le k P fun i => logDerivIdealIterate k P r $ J i) $ iSup_mono fun i => le_of_eq (logDerivIdealIterate_succ k P r $ J i).symm

theorem logDerivIdealIterate_top_eq_derivIdealIterate (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k (⊤ : Ideal S) r J = derivIdealIterate k r J := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, derivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ, ih, logDerivIdeal_top_eq_derivIdeal]

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

variable (k : Type) [CommRing k]
variable {S : Type} [CommRing S] [Algebra k S]
variable {S' : Type} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']

section
variable {R : Type} [CommRing R] {A : Type} [CommRing A]
theorem derivation_mem_map_of_forall_mem
    {B : Type} [CommRing B] [Algebra A B] [Algebra R B]
    (D' : Derivation R B B) {P : Ideal A}
    (hgen : ∀ p ∈ P, D' (algebraMap A B p) ∈ P.map (algebraMap A B)) :
    ∀ x ∈ P.map (algebraMap A B), D' x ∈ P.map (algebraMap A B) := by
  intro x hx
  have hx' := hx
  clear hx
  induction hx' using span_induction with
  | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact hgen p hp
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D' (y + z) = D' y + D' z := by simp
      rw [h]
      exact m128 _ ihy ihz
  | smul a y hy ih =>
      rw [smul_eq_mul, D'.leibniz]
      simp [smul_eq_mul]
      exact m128 _ (mul_mem_left _ _ ih) $ mul_mem_right _ _ hy

theorem derivation_smul_apply
    [Algebra R A] (c : A) (D0_ : Derivation R A A) (x : A) : (c • D0_) x = c * D0_ x := rfl

theorem mul_derivation_mem_of_span_eq
    [Algebra R A] {G : Set A} {P : Ideal A} (hP : Ideal.span G = P) (D0_ : Derivation R A A)
    (c : A) (hG : ∀ g ∈ G, c * D0_ g ∈ P) : ∀ x ∈ P, c * D0_ x ∈ P := by
  intro x hx
  rw [← hP] at hx
  induction hx using span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D0_ (y + z) = D0_ y + D0_ z := by simp
      rw [h, mul_add]
      exact P.add_mem ihy ihz
  | smul a y hy ih =>
      have hyP : y ∈ P := by rw [← hP]
                             exact hy
      rw [smul_eq_mul, D0_.leibniz]
      simp [smul_eq_mul, mul_add]
      refine P.add_mem ?_ $ P.mul_mem_left c $ P.mul_mem_right (D0_ a) hyP
      have h1 : c * (a * D0_ y) = a * (c * D0_ y) := by ring
      rw [h1]
      exact P.mul_mem_left a ih
end

section
variable {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B] (M : Submonoid A) [IsLocalization M B]
theorem exists_mem_mul_algebraMap_eq_of_mem_map (J : Ideal A) {x : B}
    (hx : x ∈ J.map (algebraMap A B)) :
    ∃ (y : A) (t : M), y ∈ J ∧ x * algebraMap A B (t : A) = algebraMap A B y := by
  obtain ⟨u, hu⟩ := mp_ (mem_map_algebraMap_iff (M := M) (S := B)) hx
  exact ⟨u.1, u.2, u.1.2, hu⟩

theorem exists_mul_mem_of_algebraMap_mem_map (P : Ideal A) {y : A}
    (hy : algebraMap A B y ∈ P.map (algebraMap A B)) :
    ∃ m : M, (m : A) * y ∈ P := by
  obtain ⟨p, t, hp, h⟩ := exists_mem_mul_algebraMap_eq_of_mem_map M P hy
  have h2 : algebraMap A B (y * (t : A)) = algebraMap A B p := by simp_all
  obtain ⟨c, hc⟩ := mp_ (eq_iff_exists (M := M) (S := B)) h2
  refine ⟨c * t, ?_⟩
  have heq : ((c * t : M) : A) * y = (c : A) * p := by
    push_cast
    linear_combination hc
  rw [heq]
  exact P.mul_mem_left _ hp
end

section
variable (M : Submonoid S) [IsLocalization M S']
include M
theorem map_logDerivIdeal_le (P J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') ≤
      logDerivIdeal k (P.map $ algebraMap S S') (J.map $ algebraMap S S') := by
  rw [map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  intro x hx
  rw [mem_comap]
  exact le_logDerivIdeal k _ _ $ mem_map_of_mem _ hx
  intro D hD x hx
  rw [mem_comap]
  have h : algebraMap S S' (D x) =
      (D.mapToLocalization (S' := S') M) (algebraMap S S' x) := by
    rw [Derivation.mapToLocalization_algebraMap]
  rw [h]
  refine derivation_apply_mem_logDerivIdeal k _ _ _
    ?_
    (mem_map_of_mem _ hx)
  rw [mem_tangentDerivations]
  refine derivation_mem_map_of_forall_mem (D.mapToLocalization (S' := S') M) ?_
  intro p hp
  rw [Derivation.mapToLocalization_algebraMap]
  exact mem_map_of_mem _ $ (mp_ (mem_tangentDerivations k P D) hD) p hp

section
variable [FinitePresentation S (KaehlerDifferential k S)] {P : Ideal S} (hP : P.FG)
include hP
theorem exists_mem_tangentDerivations_mul_eq (D : Derivation k S' S')
    (hD : D ∈ tangentDerivations k (P.map $ algebraMap S S')) :
    ∃ (m : M) (D1 : Derivation k S S), D1 ∈ tangentDerivations k P ∧
      ∀ s : S, algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D1 s) := by
  let _a0 := P.map $ algebraMap S S'
  obtain ⟨m0, D0_, hD0_⟩ :=
    Derivation.exists_derivation_mul_eq_of_isLocalization (S' := S') M D
  obtain ⟨G, hG⟩ := hP
  have key : ∀ g : S, ∃ n : M, g ∈ G → n * D0_ g ∈ P := by
    intro g
    by_cases hg : g ∈ G
    have hgP : g ∈ P := by
      rw [← hG]
      exact m100 $ Finset.mem_coe.mpr hg
    have h3 : algebraMap S S' (D0_ g) ∈ _a0 := by
      rw [← hD0_ g]
      exact mul_mem_left _ _ $ (mp_ (mem_tangentDerivations k _a0 D) hD) _ $ mem_map_of_mem _ hgP
    obtain ⟨n, hn⟩ := exists_mul_mem_of_algebraMap_mem_map M P h3
    exact ⟨n, fun _ => hn⟩
    exact ⟨1, fun h => absurd h hg⟩
  choose f hf using key
  obtain ⟨c, hcM, hcP⟩ : ∃ c : S, c ∈ M ∧ ∀ g ∈ G, c * D0_ g ∈ P := by
    refine ⟨prod G fun g => f g,
      prod_mem M fun g _ => (f g).2, ?_⟩
    intro g hg
    obtain ⟨r, hr⟩ := dvd_prod_of_mem (fun g => (f g : S)) hg
    have h4 : (f g : S) * r * D0_ g = r * (((f g : S)) * D0_ g) := by ring
    rw [hr, h4]
    exact P.mul_mem_left _ $ hf g hg
  refine ⟨⟨c * m0, M.mul_mem hcM m0.2⟩, c • D0_, ?_, ?_⟩
  have hgen := fun g hg => hcP g $ Finset.mem_coe.mp hg
  rw [mem_tangentDerivations]
  intro x hx
  have h := mul_derivation_mem_of_span_eq hG D0_ c hgen x hx
  rwa [derivation_smul_apply]
  intro s
  rw [derivation_smul_apply, map_mul, map_mul, mul_assoc, hD0_ s]

theorem logDerivIdeal_map_le_map_logDerivIdeal (J : Ideal S) :
    logDerivIdeal k (P.map $ algebraMap S S') (J.map $ algebraMap S S') ≤
      (logDerivIdeal k P J).map (algebraMap S S') := by
  rw [logDerivIdeal_le_iff]
  let _a1 := le_logDerivIdeal k P J
  refine ⟨map_mono _a1, ?_⟩
  intro D hD x hx
  obtain ⟨m, D1, hD1_, hm⟩ := exists_mem_tangentDerivations_mul_eq k M hP D hD
  obtain ⟨y, t, hy, hxt⟩ := exists_mem_mul_algebraMap_eq_of_mem_map M J hx
  have h1 : D (x * algebraMap S S' (t : S)) = D (algebraMap S S' y) := by rw [hxt]
  rw [D.leibniz] at h1
  simp [smul_eq_mul] at h1
  let _s0 := (m : S) * (t : S)
  have hmul : algebraMap S S' _s0 * D x
      = algebraMap S S' (D1 y) - x * algebraMap S S' (D1 (t : S)) := by
    rw [map_mul]
    linear_combination algebraMap S S' (m : S) * h1 + hm y - x * hm (t : S)
  have hmem : algebraMap S S' _s0 * D x ∈
      (logDerivIdeal k P J).map (algebraMap S S') := by
    rw [hmul]
    exact sub_mem (mem_map_of_mem _ $ derivation_apply_mem_logDerivIdeal k P J D1 hD1_ hy) $ mul_mem_right _ _ $ map_mono _a1 hx
  have hu : IsUnit $ algebraMap S S' _s0 := by
    rw [map_mul]
    exact (map_units (M := M) (S := S') m).mul
      (map_units (M := M) (S := S') t)
  obtain ⟨u, hu'⟩ := hu
  have hrw : D x = (↑u⁻¹ : S') * (algebraMap S S' _s0 * D x) := by
    rw [← hu', ← mul_assoc, inv_mul, one_mul]
  rw [hrw]
  exact mul_mem_left _ _ hmem

theorem logDerivIdeal_map (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map $ algebraMap S S') (J.map $ algebraMap S S') :=
  le_antisymm (map_logDerivIdeal_le k M P J) $ logDerivIdeal_map_le_map_logDerivIdeal k M hP J

end
end

section
variable (g : S) [IsLocalization.Away g S'] [FinitePresentation S (KaehlerDifferential k S)] {P : Ideal S} (hP : P.FG)
include g hP
theorem logDerivIdeal_map_away (J : Ideal S) :
    (logDerivIdeal k P J).map (algebraMap S S') =
      logDerivIdeal k (P.map $ algebraMap S S') (J.map $ algebraMap S S') :=
  logDerivIdeal_map k (powers g) hP J

theorem logDerivIdealIterate_map_away (r : ℕ) (J : Ideal S) :
    (logDerivIdealIterate k P r J).map (algebraMap S S') =
      logDerivIdealIterate k (P.map $ algebraMap S S') r (J.map $ algebraMap S S') :=
  by
    induction r with
    | zero => rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
    | succ r ih =>
        rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ, logDerivIdeal_map k (powers g) hP, ih]
end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

variable (k : Type) [CommRing k] {S T : Type} [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

section
variable (f : S →ₐ[k] T) (hf : Surjective f)
include hf
theorem map_logDerivIdeal_ker_le_derivIdeal_map (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdeal k (RingHom.ker f.toRingHom) J)
      ≤ derivIdeal k (Ideal.map f.toRingHom J) := by
  let _a0 := m6 f.toRingHom J
  rw [map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  intro x hx
  rw [mem_comap]
  exact le_derivIdeal k _a0 $ mem_map_of_mem f.toRingHom hx
  intro D hD x hx
  have hmem : f x ∈ _a0 := mem_map_of_mem f.toRingHom hx
  have h2 := derivation_apply_mem_derivIdeal k _a0
    (derivationOfSurjective f hf D $ (mem_tangentDerivations k (m41 f.toRingHom) D).mp hD) hmem
  rw [derivationOfSurjective_apply] at h2
  rwa [mem_comap]

theorem map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker {P} (hP : P = RingHom.ker f.toRingHom)
    r J :
    Ideal.map f.toRingHom (logDerivIdealIterate k P r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  subst hP
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ]
      exact (map_logDerivIdeal_ker_le_derivIdeal_map k f hf _).trans $ derivIdeal_mono k ih
end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]

def multiIndexDeriv {h : ℕ} (D : Fin h → Derivation k R R) (al_ : Fin h → ℕ) (x : R) : R :=
  foldr h (fun i y => (⇑(D i))^[al_ i] y) x

def unitMultiIndex {h : ℕ} (i : Fin h) : Fin h → ℕ := fun j => if j = i then 1 else 0

theorem derivation_natCast_mul {B S : Type} [CommRing B] [CommRing S] [Algebra B S]
    (D : Derivation B S S) (m : ℕ) (x : S) : D ((m : S) * x) = (m : S) * D x :=by simp_all
@[simp]
theorem multiIndexDeriv_of_isEmpty (D : Fin 0 → Derivation k R R) (al_ : Fin 0 → ℕ) :
    multiIndexDeriv D al_ = id := by
  funext x
  simp [multiIndexDeriv]

theorem foldr_eq_self_of_forall_eq_self {A : Type} :
    ∀ n (f : Fin n → A → A), (∀ i (y : A), f i y = y) →
      ∀ x, foldr n f x = x := by
  intro n
  induction n with
  | zero =>
      intro f hf x
      simp
  | succ n ih =>
      intro f hf x
      rw [foldr_succ, ih (fun i => f i.succ) (fun i y => hf i.succ y) x]
      exact hf 0 x

theorem foldr_eq_of_eq_id_of_ne {A : Type} :
    ∀ (n : ℕ) (F : Fin n → A → A) (i : Fin n) (f : A → A),
      (∀ j : Fin n, j ≠ i → ∀ y : A, F j y = y) → (∀ y : A, F i y = f y) →
      ∀ x : A, foldr n F x = f x := by
  intro n
  induction n with
  | zero =>
      intro F i
      exact i.elim0
  | succ m ih =>
      intro F i
      induction i using Fin.cases with
      | zero =>
          intro f hne heq x
          rw [foldr_succ, foldr_eq_self_of_forall_eq_self m (fun j : Fin m => F j.succ) (fun j y => hne j.succ (succ_ne_zero j) y) x]
          exact heq x
      | succ j =>
          intro f hne heq x
          rw [Fin.foldr_succ, ih (fun j' : Fin m => F j'.succ) j f (fun j' hj' y => hne j'.succ (fun hc => hj' $ succ_injective m hc) y) heq x]
          exact hne 0 (m113 $ Fin.succ_ne_zero j) $ f x

section
variable {h : ℕ}
section
variable (D : Fin h → Derivation k R R) (f : R)
@[simp]
theorem multiIndexDeriv_zero :
    multiIndexDeriv D (0 : Fin h → ℕ) f = f := by
  unfold multiIndexDeriv
  exact foldr_eq_self_of_forall_eq_self h (fun i y => (⇑(D i))^[(0 : Fin h → ℕ) i] y)
    (fun i y => by simp) f

@[simp]
theorem multiIndexDeriv_fun_zero :
    multiIndexDeriv D (fun _ => 0) f = f :=
  multiIndexDeriv_zero D f
end

@[simp]
theorem unitMultiIndex_apply (i j : Fin h) :
    unitMultiIndex i j = if j = i then 1 else 0 := rfl

theorem multiIndexDeriv_unitMultiIndex (D : Fin h → Derivation k R R) (i : Fin h) (x : R) :
    multiIndexDeriv D (unitMultiIndex i) x = D i x := by
  refine foldr_eq_of_eq_id_of_ne h (fun j y => (⇑(D j))^[unitMultiIndex i j] y) i
    (⇑(D i)) ?_ ?_ x
  simp_all
  simp_all

theorem sum_unitMultiIndex (i : Fin h) : ∑ j, unitMultiIndex i j = 1 := by
  simp [unitMultiIndex]
end

section
variable (J : Ideal R)
theorem mul_pow_sub_one_le n :
    J * J ^ (n - 1) ≤ J ^ n := by
  cases n with
  | zero =>
      dsimp
      rw [pow_zero, one_eq_top]
      exact le_top
  | succ m =>
      dsimp
      exact le_of_eq $ by rw [mul_comm, ← pow_succ]

section
variable (D : Derivation k R R)
theorem derivation_mem_pow_sub_one :
    ∀ n f, f ∈ J ^ n → D f ∈ J ^ (n - 1) := by
  intro n
  induction n with
  | zero =>
      intro f _
      rw [pow_zero, one_eq_top]
      exact mem_top
  | succ m ih =>
      intro f hf
      rw [pow_succ] at hf
      refine mul_induction_on (C := fun x => D x ∈ J ^ m) hf ?_ ?_
      intro a ha b hb
      have hL : D (a * b) = a * D b + b * D a := by simp_all
      rw [hL]
      exact m60 _ (mul_mem_right _ _ ha) $ mul_pow_sub_one_le J m $ mul_mem_mul hb $ ih a ha
      intro x y hx hy
      rw [map_add]
      exact m60 _ hx hy

theorem iterate_derivation_mem_pow_sub :
    ∀ m n f, f ∈ J ^ n → (⇑D)^[m] f ∈ J ^ (n - m) := by
  intro m
  induction m with
  | zero =>
      intro n f hf
      rwa [iterate_zero_apply, m130]
  | succ m ih =>
      intro n f hf
      rw [iterate_succ_apply]
      have h2 := ih (n - 1) (D f) $ derivation_mem_pow_sub_one J D n f hf
      have h3 : n - 1 - m = n - (m + 1) := by omega
      rwa [h3] at h2
end

theorem foldr_iterate_mem_pow_sub :
    ∀ (h : ℕ) (D : Fin h → Derivation k R R) (al_ : Fin h → ℕ) (n : ℕ) (f : R), f ∈ J ^ n →
      foldr h (fun i y => (⇑(D i))^[al_ i] y) f ∈ J ^ (n - ∑ i, al_ i) := by
  intro h
  induction h with
  | zero =>
      intro D al_ n f hf
      have hz : ∑ i : Fin 0, al_ i = 0 := by simp
      rwa [foldr_zero, hz, m130]
  | succ h ih =>
      intro D al_ n f hf
      have h2 := iterate_derivation_mem_pow_sub J (D 0) (al_ 0)
        (n - ∑ i : Fin h, al_ i.succ) _ $ ih (fun i => D i.succ) (fun i => al_ i.succ) n f hf
      have hs : n - ∑ i, al_ i = n - (∑ i : Fin h, al_ i.succ) - al_ 0 := by
        rw [sum_univ_succ al_]
        omega
      rwa [foldr_succ, hs]
end

theorem multiIndexDeriv_mem_pow_sub {h : ℕ} (D : Fin h → Derivation k R R) (J : Ideal R) (n : ℕ)
    {f : R} (hf : f ∈ J ^ n) (al_ : Fin h → ℕ) :
    multiIndexDeriv D al_ f ∈ J ^ (n - ∑ i, al_ i) := by
  exact foldr_iterate_mem_pow_sub J h D al_ n f hf

section
variable {B S : Type} [CommRing B] [CommRing S] [Algebra B S]
section
variable (D : Derivation B S S)
theorem iterate_derivation_natCast_mul (m c : ℕ) (x : S) :
    (⇑D)^[m] ((c : S) * x) = (c : S) * (⇑D)^[m] x := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp [iterate_succ_apply']
      rw [ih, derivation_natCast_mul]

theorem iterate_derivation_sum (m : ℕ) {ι : Type} (s : Finset ι) (F : ι → S) :
    (⇑D)^[m] (∑ i ∈ s, F i) = ∑ i ∈ s, (⇑D)^[m] (F i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp [iterate_succ_apply']
      rw [ih, map_sum]

theorem iterate_derivation_mul (n : ℕ) (x y : S) :
    (⇑D)^[n] (x * y)
      = ∑ i ∈ range (n + 1), ((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n - i] y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let _a0 := ⇑D
      have hstep : ∀ i ∈ range (n + 1),
          D (((n.choose i) : S) * (_a0^[i] x * _a0^[n - i] y))
            = ((n.choose i) : S) * (_a0^[i + 1] x * _a0^[n - i] y)
              + ((n.choose i) : S) * (_a0^[i] x * _a0^[n + 1 - i] y) := by
        intro i hi
        rw [mem_range] at hi
        have e1 := sy_ $ iterate_succ_apply' (⇑D) i x
        have e2 : D (_a0^[n - i] y) = _a0^[n + 1 - i] y := by
          have hni : n + 1 - i = n - i + 1 := by omega
          rw [hni]
          exact sy_ $ iterate_succ_apply' (⇑D) (n - i) y
        rw [derivation_natCast_mul, D.leibniz, e1, e2]
        simp [smul_eq_mul]
        ring
      rw [iterate_succ_apply', ih, map_sum]
      refine m32 (sum_congr rfl hstep) ?_
      rw [sum_add_distrib]
      let u := fun i => _a0^[i] x
      let v := fun i => _a0^[i] y
      have e1 : (∑ i ∈ range (n + 1), ((n.choose i) : S) * (u (i + 1) * v (n - i)))
          = (∑ i ∈ range n, ((n.choose i) : S) * (u (i + 1) * v (n - i)))
            + u (n + 1) * v 0 := by
        rw [sum_range_succ]
        simp
      have e2 : (∑ i ∈ range (n + 1), ((n.choose i) : S) * (u i * v (n + 1 - i)))
          = (∑ i ∈ range n, ((n.choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
            + u 0 * v (n + 1) := by
        rw [sum_range_succ']
        simp
      have e3 : (∑ i ∈ range (n + 1 + 1), (((n + 1).choose i : ℕ) : S) * (u i * v (n + 1 - i)))
          = (∑ i ∈ range (n + 1), (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
            + u 0 * v (n + 1) := by
        rw [sum_range_succ']
        simp
      have e4 : (∑ i ∈ range (n + 1),
            (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
          = (∑ i ∈ range n, (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
            + u (n + 1) * v 0 := by
        rw [sum_range_succ]
        simp
      have e5 : (∑ i ∈ range n,
            (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
          = (∑ i ∈ range n, ((n.choose i) : S) * (u (i + 1) * v (n - i)))
            + (∑ i ∈ range n, ((n.choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i))) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        rw [choose_succ_succ n i]
        push_cast
        ring
      rw [e1, e2, e3, e4, e5]
      ring
end

theorem multiIndexDeriv_succ
    {m : ℕ} (D : Fin (m + 1) → Derivation B S S) (al_ : Fin (m + 1) → ℕ) (x : S) :
    multiIndexDeriv D al_ x
      = (⇑(D 0))^[al_ 0] (multiIndexDeriv (fun i => D i.succ) (fun i => al_ i.succ) x) := by
  simp [multiIndexDeriv, foldr_succ]
end

theorem fin_cons_self_tail {m : ℕ} (be_ : Fin (m + 1) → ℕ) :
    Fin.cons (be_ 0) (fun i => be_ i.succ) = be_ := by
  funext i
  refine Fin.cases ?_ ?_ i
  simp
  intro j
  simp

def finSuccFunEquivProd (m : ℕ) : (Fin (m + 1) → ℕ) ≃ ℕ × (Fin m → ℕ) where
  toFun be_ := (be_ 0, fun i => be_ i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv be_ := fin_cons_self_tail be_
  right_inv p := by
    rcases p with ⟨a, b⟩
    simp

theorem sum_piFinset_succ {M : Type} [AddCommMonoid M] {m : ℕ}
    (s : Fin (m + 1) → Finset ℕ) (F : (Fin (m + 1) → ℕ) → M) :
    ∑ be_ ∈ piFinset s, F be_
      = ∑ j ∈ s 0, ∑ ga_ ∈ piFinset fun i => s i.succ, F (Fin.cons j ga_) := by
  rw [← sum_product']
  refine sum_equiv (finSuccFunEquivProd m) ?_ ?_
  intro be_
  constructor
  intro hbe_
  have hbe' := Fintype.mem_piFinset.1 hbe_
  exact mem_product.2 ⟨hbe' 0, Fintype.mem_piFinset.2 fun i => hbe' i.succ⟩
  intro hbe_
  have h1 := mem_product.1 hbe_
  refine Fintype.mem_piFinset.2 fun i => ?_
  refine Fin.cases h1.1 ?_ i
  intro j
  exact Fintype.mem_piFinset.1 h1.2 j
  intro be_ _
  exact congrArg F (fin_cons_self_tail be_).symm

section
variable {h : ℕ} (D : Fin h → Derivation k R R)
theorem multiIndexDeriv_mul (al_ : Fin h → ℕ) (f g : R) :
    multiIndexDeriv D al_ (f * g) =
      ∑ be_ ∈ piFinset fun i => range $ al_ i + 1,
        ((∏ i, (al_ i).choose (be_ i) : ℕ) : R) * multiIndexDeriv D be_ f *
          multiIndexDeriv D (fun i => al_ i - be_ i) g := by
  induction h with
  | zero =>
      have hset : (piFinset fun i => range $ al_ i + 1)
          = {fun _ => 0} := by
        refine eq_singleton_iff_unique_mem.2 ⟨Fintype.mem_piFinset.2 (·.elim0), ?_⟩
        intro x _
        funext i
        exact i.elim0
      rw [hset, sum_singleton]
      simp
  | succ h ih =>
      have hcons : ∀ j ga_ x,
          multiIndexDeriv D (m223 j ga_) x
            = (⇑(D 0))^[j] (multiIndexDeriv (fun i => D i.succ) ga_ x) := by
        intro j ga_ x
        rw [multiIndexDeriv_succ D (m223 j ga_) x]
        simp
      have hcons2 : ∀ j ga_ x,
          multiIndexDeriv D (fun i => al_ i - (m223 j ga_ : Fin (h + 1) → ℕ) i) x
            = (⇑(D 0))^[al_ 0 - j]
                (multiIndexDeriv (fun i => D i.succ) (fun i => al_ i.succ - ga_ i) x) := by
        intro j ga_ x
        rw [multiIndexDeriv_succ D (fun i => al_ i - (m223 j ga_ : Fin (h + 1) → ℕ) i) x]
        simp
      have key : ∀ ga_,
          (⇑(D 0))^[al_ 0] (((∏ i, (al_ i.succ).choose (ga_ i) : ℕ) : R)
              * multiIndexDeriv (fun i => D i.succ) ga_ f
              * multiIndexDeriv (fun i => D i.succ) (fun i => al_ i.succ - ga_ i) g)
            = ∑ j ∈ range (al_ 0 + 1),
                ((∏ i, (al_ i).choose ((m223 j ga_ : Fin (h + 1) → ℕ) i) : ℕ) : R)
                  * multiIndexDeriv D (m223 j ga_) f
                  * multiIndexDeriv D (fun i => al_ i - (m223 j ga_ : Fin (h + 1) → ℕ) i) g := by
        intro ga_
        rw [mul_assoc _ _ _, iterate_derivation_natCast_mul, iterate_derivation_mul, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [hcons j ga_ f, hcons2 j ga_ g, prod_univ_succ]
        simp [cons_zero, cons_succ]
        push_cast
        ring
      rw [multiIndexDeriv_succ D al_ $ f * g, ih (fun i => D i.succ) fun i => al_ i.succ,
        iterate_derivation_sum]
      refine m32 (sum_congr rfl fun ga_ _ => key ga_) ?_
      rw [sum_comm]
      exact (sum_piFinset_succ (fun i : Fin (h + 1) => range $ al_ i + 1)
        (fun be_ => ((∏ i, (al_ i).choose (be_ i) : ℕ) : R) * multiIndexDeriv D be_ f *
          multiIndexDeriv D (fun i => al_ i - be_ i) g)).symm

theorem multiIndexDeriv_mul_sub_sum_mem (J : Ideal R)
    (r s : ℕ) (al_ : Fin h → ℕ) (hal_ : ∑ i, al_ i = r + s) {f g : R}
    (hf : f ∈ J ^ r) (hg : g ∈ J ^ s) :
    multiIndexDeriv D al_ (f * g) -
        ∑ be_ ∈ (piFinset fun i => range $ al_ i + 1).filter
            (fun be_ => ∑ i, be_ i = r),
          ((∏ i, (al_ i).choose (be_ i) : ℕ) : R) * multiIndexDeriv D be_ f *
            multiIndexDeriv D (fun i => al_ i - be_ i) g ∈ J := by
  rw [multiIndexDeriv_mul D al_ f g,
    ← sum_filter_add_sum_filter_not
      (piFinset fun i => range $ al_ i + 1) fun be_ => ∑ i, be_ i = r,
    add_sub_cancel_left]
  refine m133 _ ?_
  intro be_ hbe_
  rw [mem_filter] at hbe_
  obtain ⟨hbemem, hbene⟩ := hbe_
  have hbei : ∀ i, be_ i ≤ al_ i := fun i =>
    lt_succ_iff.mp $ Finset.mem_range.mp $ Fintype.mem_piFinset.mp hbemem i
  have h1 : (∑ i, (al_ i - be_ i)) + ∑ i, be_ i = r + s := by
    rw [← hal_, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => sub_add_cancel $ hbei i
  by_cases hlt : ∑ i, be_ i < r
  have hmem :=
    multiIndexDeriv_mem_pow_sub D J r hf be_
  have hx := by
    have hpos : 0 < r - ∑ i, be_ i := by omega
    exact pow_le_self hpos.ne' hmem
  exact mul_mem_right _ _ $ mul_mem_left _ _ hx
  have hmem :=
    multiIndexDeriv_mem_pow_sub D J s hg fun i => al_ i - be_ i
  have hy := by
    have hpos : 0 < s - ∑ i, (al_ i - be_ i) := by omega
    exact pow_le_self hpos.ne' hmem
  exact mul_mem_left _ _ hy
end

theorem foldr_comm_of_comm {A : Type} (E : A → A) :
    ∀ n F, (∀ i y, E (F i y) = F i (E y)) →
      ∀ x : A, E (foldr n F x) = foldr n F (E x) := by
  intro n
  induction n with
  | zero =>
      intro F _ x
      simp
  | succ n ih =>
      intro F hF x
      rw [foldr_succ, foldr_succ, hF 0,
        ih (fun i => F i.succ) (fun i y => hF i.succ y) x]

theorem multiIndexDeriv_add_of_comm_forall :
    ∀ (n : ℕ) (D : Fin n → Derivation k R R),
      (∀ i j : Fin n, ∀ x : R, D i (D j x) = D j (D i x)) →
      ∀ (al_ be_ : Fin n → ℕ) (x : R),
        multiIndexDeriv D (al_ + be_) x = multiIndexDeriv D al_ (multiIndexDeriv D be_ x) := by
  intro n
  induction n with
  | zero =>
      intro D _ al_ be_ x
      simp
  | succ n ih =>
      intro D hD al_ be_ x
      let _a0 := ⇑(D 0)
      have key : ∀ (ga_ : Fin (n + 1) → ℕ) y,
          multiIndexDeriv D ga_ y =
            _a0^[ga_ 0]
              (multiIndexDeriv (fun i : Fin n => D i.succ) (fun i : Fin n => ga_ i.succ) y) := by
        intro ga_ y
        exact foldr_succ (fun (i : Fin $ n + 1) z => (⇑(D i))^[ga_ i] z) y
      have hcomm0 : ∀ ga_ y,
          (⇑(D 0)) (multiIndexDeriv (fun i : Fin n => D i.succ) ga_ y) =
            multiIndexDeriv (fun i : Fin n => D i.succ) ga_ ((⇑(D 0)) y) := by
        intro ga_ y
        have hc : ∀ i z,
            (⇑(D 0)) ((⇑(D i.succ))^[ga_ i] z) = (⇑(D i.succ))^[ga_ i] ((⇑(D 0)) z) := by
          intro i z
          have hcomm : Function.Commute (⇑(D 0) : R → R) (⇑(D i.succ) : R → R) :=
            fun w => hD 0 i.succ w
          exact hcomm.iterate_right (ga_ i) z
        exact foldr_comm_of_comm (⇑(D 0)) n (fun i z => (⇑(D i.succ))^[ga_ i] z) hc y
      have hcomm : ∀ m ga_ y,
          _a0^[m] (multiIndexDeriv (fun i : Fin n => D i.succ) ga_ y) =
            multiIndexDeriv (fun i : Fin n => D i.succ) ga_ (_a0^[m] y) := by
        intro m ga_ y
        have hc : Function.Commute (multiIndexDeriv (fun i : Fin n => D i.succ) ga_)
            (⇑(D 0) : R → R) := fun w => sy_ $ hcomm0 ga_ w
        exact sy_ $ hc.iterate_right m y
      have hidx : (fun i : Fin n => (al_ + be_) i.succ)
          = (fun i : Fin n => al_ i.succ) + (fun i : Fin n => be_ i.succ) := by
        funext i
        simp
      rw [key (al_ + be_) x, hidx,
        ih (fun i : Fin n => D i.succ) (fun i j w => hD i.succ j.succ w)
          (fun i : Fin n => al_ i.succ) (fun i : Fin n => be_ i.succ) x,
        key be_ x, key al_, Pi.add_apply, Function.iterate_add_apply,
        hcomm (be_ 0) (fun i : Fin n => al_ i.succ)
          (multiIndexDeriv (fun i : Fin n => D i.succ) (fun i : Fin n => be_ i.succ) x)]


end


open IsLocalRing

section
variable {R : Type} [CommRing R]
theorem idealOrder_eq_of_le_of_not_le [IsLocalRing R] {n : ℕ}
    {I : Ideal R} (h1 : I ≤ IsLocalRing.maximalIdeal R ^ n)
    (h2 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (n + 1)) : idealOrder I = (n : ENat) := by
  have h3 := mpr_ (le_idealOrder_iff I n) h1
  have h4 : ¬ (((n + 1) : ENat) ≤ idealOrder I) := fun hc =>
    h2 $ mp_ (le_idealOrder_iff I $ n + 1) hc
  rw [not_le] at h4
  obtain ⟨m, hm⟩ := mp_ ne_top_iff_exists $ ne_top_of_lt h4
  rw [← hm] at h3 h4 ⊢
  have hle : n ≤ m := by exact_mod_cast h3
  have hlt : m < n + 1 := by exact_mod_cast h4
  have hme : m = n := by omega
  exact_mod_cast hme

theorem sum_notMem_of_unique_notMem {I : Ideal R} {ι : Type}
    [DecidableEq ι] (t : Finset ι) (F : ι → R) (a : ι) (ha : a ∈ t) (hFa : F a ∉ I)
    (hrest : ∀ b ∈ t, b ≠ a → F b ∈ I) : (∑ b ∈ t, F b) ∉ I := by
  intro hsum
  refine hFa ?_
  have h3 := sub_mem hsum $ m133 _ fun b hb => hrest b (mem_of_mem_erase hb) $ ne_of_mem_erase hb
  rwa [← add_sum_erase t F ha, add_sub_cancel_right] at h3
end

section
variable (N : ℕ)
def ofDigitsFin {h : ℕ} (be_ : Fin h → ℕ) : ℕ := ∑ i, be_ i * N ^ (i : ℕ)

theorem ofDigits_add {h : ℕ} (be_ ga_ : Fin h → ℕ) :
    ofDigitsFin N (fun i => be_ i + ga_ i) = ofDigitsFin N be_ + ofDigitsFin N ga_ := by
  simp [ofDigitsFin, add_mul]
  rw [sum_add_distrib]

theorem ofDigits_fin_succ {n} δ :
    ofDigitsFin N δ = δ 0 + (ofDigitsFin N fun i : Fin n => δ i.succ) * N := by
  simp [ofDigitsFin]
  rw [sum_univ_succ, sum_mul]
  congr 1
  simp
  refine sum_congr rfl fun i _ => ?_
  rw [val_succ, pow_succ, mul_assoc]

theorem ofDigits_injective_of_lt (hN : 0 < N) : ∀ (h : ℕ) (be_ ga_ : Fin h → ℕ),
    (∀ i, be_ i < N) → (∀ i, ga_ i < N) → ofDigitsFin N be_ = ofDigitsFin N ga_ → be_ = ga_ := by
  intro h
  induction h with
  | zero =>
    intro be_ ga_ _ _ _
    funext i
    exact i.elim0
  | succ n ih =>
    intro be_ ga_ hbe_ hga_ hsum
    rw [ofDigits_fin_succ N be_, ofDigits_fin_succ N ga_] at hsum
    have h0 : be_ 0 = ga_ 0 := by
      have hmod : (be_ 0 + (ofDigitsFin N fun i : Fin n => be_ i.succ) * N) % N
          = (ga_ 0 + (ofDigitsFin N fun i : Fin n => ga_ i.succ) * N) % N := by rw [hsum]
      rwa [add_mul_mod_self_right, add_mul_mod_self_right,
        mod_eq_of_lt $ hbe_ 0, mod_eq_of_lt $ hga_ 0] at hmod
    rw [h0] at hsum
    funext i
    refine Fin.cases h0 ?_ i
    intro j
    exact congrFun (ih _ _ (fun i => hbe_ i.succ) (fun i => hga_ i.succ) $ Nat.eq_of_mul_eq_mul_right hN $ Nat.add_left_cancel hsum) j
end

def multiIndicesOfDegree (h r : ℕ) : Finset $ Fin h → ℕ :=
  (piFinset fun _ : Fin h => range $ r + 1).filter fun be_ => ∑ i, be_ i = r

theorem mem_multiIndicesOfDegree {h r : ℕ} (be_ : Fin h → ℕ) :
    be_ ∈ multiIndicesOfDegree h r ↔ ∑ i, be_ i = r := by
  simp only [multiIndicesOfDegree, mem_filter, mem_piFinset, mem_range]
  constructor
  exact fun hbe_ => an2 hbe_
  intro hs
  refine ⟨fun i => ?_, hs⟩
  have h1 : be_ i ≤ r := by
    rw [← hs]
    exact single_le_sum (f := be_) (fun j _ => zero_le _) $ mem_univ i
  omega

section
variable {k R : Type} [CommRing k] [CommRing R] [IsLocalRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R) (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R) (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a)) (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) (r : ℕ)
include hx hD hDD hunit
theorem mem_maximalIdeal_pow_succ_of_multiIndexDeriv_mem :
    ∀ f : R, f ∈ IsLocalRing.maximalIdeal R ^ r →
      (∀ be_ : Fin h → ℕ, (∑ i, be_ i = r) → multiIndexDeriv D be_ f ∈ IsLocalRing.maximalIdeal R) →
      f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) := by
  induction r with
  | zero =>
    intro f _ hbe_
    have h0 := hbe_ (fun _ => 0) $ by simp
    rw [multiIndexDeriv_fun_zero] at h0
    simpa using h0
  | succ r ih =>
    intro f hf hbe_
    have key : ∀ i, D i f ∈ m16 R ^ (r + 1) := by
      intro i
      refine ih (D i f) ?_ ?_
      have h1 := multiIndexDeriv_mem_pow_sub D (m16 R) (r + 1) hf
        (unitMultiIndex i)
      rw [multiIndexDeriv_unitMultiIndex, sum_unitMultiIndex] at h1
      simpa using h1
      intro be_ hbe'
      have hsum : ∑ j, (be_ + unitMultiIndex i) j = r + 1 := by
        simp only [Pi.add_apply]
        rw [sum_add_distrib, hbe', sum_unitMultiIndex]
      have h2 := hbe_ (be_ + unitMultiIndex i) hsum
      have _i30 : multiIndexDeriv D (be_ + unitMultiIndex i) f = multiIndexDeriv D be_ (D i f) := by
        rw [multiIndexDeriv_add_of_comm_forall h D hDD be_ (unitMultiIndex i) f, multiIndexDeriv_unitMultiIndex D i f]
      rwa [_i30] at h2
    have hfx : f ∈ Ideal.span (Set.range x) ^ (r + 1) := by rw [hx]
                                                            exact hf
    have hdx : ∀ i, D i f ∈ m17 (m30 x) ^ (r + 1) := by simp_all
    have hres := mem_pow_succ_of_deriv_mem_pow k x D hD (hunit (r + 1) $ by omega) hfx hdx
    rwa [hx] at hres

theorem mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem {f : R} (hf : f ∈ IsLocalRing.maximalIdeal R ^ r) :
    f ∈ IsLocalRing.maximalIdeal R ^ (r + 1) ↔
      ∀ be_ ∈ multiIndicesOfDegree h r, multiIndexDeriv D be_ f ∈ IsLocalRing.maximalIdeal R := by
  constructor
  intro hfs be_ hbe_
  have hm := multiIndexDeriv_mem_pow_sub D (m16 R) (r + 1) hfs be_
  rw [mp_ (mem_multiIndicesOfDegree be_) hbe_] at hm
  have hr1 : r + 1 - r = 1 := by omega
  rwa [hr1, pow_one] at hm
  intro hall
  exact mem_maximalIdeal_pow_succ_of_multiIndexDeriv_mem x D hx hD hDD hunit r f hf
    (fun be_ hb => hall be_ $ mpr_ (mem_multiIndicesOfDegree be_) hb)
end

theorem exists_ofDigits_le_of_sum_eq {h : ℕ} (P : (Fin h → ℕ) → Prop) (r N : ℕ)
    (hex : ∃ be_ : Fin h → ℕ, (∑ i, be_ i = r) ∧ P be_) :
    ∃ be0 : Fin h → ℕ, (∑ i, be0 i = r) ∧ P be0 ∧
      ∀ be_ : Fin h → ℕ, (∑ i, be_ i = r) → P be_ → ofDigitsFin N be0 ≤ ofDigitsFin N be_ := by
  classical
  obtain ⟨be1, hbe1, hP1⟩ := hex
  obtain ⟨be0, hmem, hmin⟩ := exists_min_image
    ((multiIndicesOfDegree h r).filter P) (ofDigitsFin N)
    ⟨be1, Finset.mem_filter.mpr ⟨mpr_ (mem_multiIndicesOfDegree be1) hbe1, hP1⟩⟩
  rw [mem_filter, mem_multiIndicesOfDegree] at hmem
  exact ⟨be0, an1 hmem, an2 hmem, fun be_ hbe_ hPbe =>
    hmin be_ (Finset.mem_filter.mpr ⟨mpr_ (mem_multiIndicesOfDegree be_) hbe_, hPbe⟩)⟩

section
variable {k R : Type} [CommRing k] [CommRing R] [IsLocalRing R]
theorem mul_notMem_maximalIdeal_pow_add_succ [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {r s : ℕ} {f g : R} (hf : f ∈ IsLocalRing.maximalIdeal R ^ r)
    (hnf : f ∉ IsLocalRing.maximalIdeal R ^ (r + 1))
    (hg : g ∈ IsLocalRing.maximalIdeal R ^ s)
    (hng : g ∉ IsLocalRing.maximalIdeal R ^ (s + 1)) :
    f * g ∉ IsLocalRing.maximalIdeal R ^ (r + s + 1) := by
  have hfex : ∃ be_, (∑ i, be_ i = r) ∧
      multiIndexDeriv D be_ f ∉ m16 R := by
    by_contra hcon
    push Not at hcon
    refine hnf $ mpr_ (mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit r hf) ?_
    intro be_ hbe_
    exact hcon be_ $ mp_ (mem_multiIndicesOfDegree be_) hbe_
  have hgex : ∃ ga_, (∑ i, ga_ i = s) ∧
      multiIndexDeriv D ga_ g ∉ m16 R := by
    by_contra hcon
    push Not at hcon
    refine hng $ mpr_ (mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit s hg) ?_
    intro ga_ hga_
    exact hcon ga_ $ mp_ (mem_multiIndicesOfDegree ga_) hga_
  obtain ⟨be0, hbe0deg, hbe0f, hbe0min⟩ := exists_ofDigits_le_of_sum_eq
    (fun be_ => multiIndexDeriv D be_ f ∉ m16 R) r (r + s + 1) hfex
  obtain ⟨ga0, hga0deg, hga0g, hga0min⟩ := exists_ofDigits_le_of_sum_eq
    (fun ga_ => multiIndexDeriv D ga_ g ∉ m16 R) s (r + s + 1) hgex
  obtain ⟨al_, hal_⟩ : ∃ al_ : Fin h → ℕ, ∀ i, al_ i = be0 i + ga0 i := ⟨_, fun _ => rfl⟩
  have halsum : ∑ i, al_ i = r + s := by
    rw [sum_congr rfl fun i _ => hal_ i, sum_add_distrib, hbe0deg, hga0deg]
  have hbase := congrArg (ofDigitsFin $ r + s + 1) $ funext hal_
  rw [ofDigits_add] at hbase
  intro hmem
  have hfg : f * g ∈ m16 R ^ (r + s) := by
    rw [pow_add]
    exact mul_mem_mul hf hg
  have hkey := mp_ (mem_maximalIdeal_pow_succ_iff_multiIndexDeriv_mem x D hx hD hDD hunit (r + s) hfg) hmem
    al_ $ mpr_ (mem_multiIndicesOfDegree al_) halsum
  have hT := sub_mem hkey $ multiIndexDeriv_mul_sub_sum_mem D (m16 R) r s al_ halsum hf hg
  rw [sub_sub_cancel] at hT
  refine (sum_notMem_of_unique_notMem _ _ be0 ?_ ?_ ?_) hT
  simp_all
  have hgaeq : (fun i => al_ i - be0 i) = ga0 := by
    funext i
    have := hal_ i
    omega
  rw [hgaeq]
  refine mpr_ notMem_maximalIdeal
    (((hunit _ $ mpr_ one_le_iff_ne_zero ?_).mul
      (mp_ notMem_maximalIdeal hbe0f)).mul
      (mp_ notMem_maximalIdeal hga0g))
  rw [prod_ne_zero_iff]
  intro i _
  refine (choose_pos ?_).ne'
  have := hal_ i
  omega
  intro be_ hbet_ hbene
  rw [mem_filter, mem_piFinset] at hbet_
  obtain ⟨hberange, hbesum⟩ := hbet_
  have hbele : ∀ i, be_ i ≤ al_ i := fun i =>
    lt_succ_iff.mp $ Finset.mem_range.mp $ hberange i
  by_cases hcase : multiIndexDeriv D be_ f ∈ m16 R
  simp_all
  have hmin1 := hbe0min be_ hbesum hcase
  have hbbe : ∀ i, be_ i < r + s + 1 := by
    intro i
    have h1 : be_ i ≤ r := by
      rw [← hbesum]
      exact single_le_sum (f := be_) (fun j _ => zero_le _) $ mem_univ i
    omega
  have hbbe0 : ∀ i, be0 i < r + s + 1 := by
    intro i
    have h1 : be0 i ≤ r := by
      rw [← hbe0deg]
      exact single_le_sum (f := be0) (fun j _ => zero_le _) $ mem_univ i
    omega
  let _a0 := ofDigitsFin (r + s + 1) be_
  have hne : (ofDigitsFin (r + s + 1) be0) ≠ _a0 := fun heq =>
    hbene $ ofDigits_injective_of_lt (r + s + 1) (by omega) h be_ be0 hbbe hbbe0 heq.symm
  have hgasum : ∑ i, (al_ i - be_ i) = s := by
    have h1 : ∑ i, ((al_ i - be_ i) + be_ i) = ∑ i, al_ i :=
      sum_congr rfl fun i _ => by
        have := hbele i
        omega
    rw [sum_add_distrib, hbesum, halsum] at h1
    omega
  have hsplit : _a0 + ofDigitsFin (r + s + 1) (fun i => al_ i - be_ i)
      = ofDigitsFin (r + s + 1) al_ := by
    rw [← ofDigits_add]
    exact congrArg (ofDigitsFin $ r + s + 1) (funext fun i => by
      have := hbele i
      omega)
  have hgalt : ofDigitsFin (r + s + 1) (fun i => al_ i - be_ i) < ofDigitsFin (r + s + 1) ga0 := by
    omega
  have hgmem : multiIndexDeriv D (fun i => al_ i - be_ i) g ∈ m16 R := by
    by_contra hcon2
    exact absurd (hga0min _ hgasum hcon2) $ by omega
  exact mul_mem_left _ _ hgmem

section
variable [IsNoetherianRing R] [hv4_1 : Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R) (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R) (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a)) (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
include hv4_1 hx hD hDD hunit
theorem idealOrder_mul (I J : Ideal R) :
    idealOrder (I * J) = idealOrder I + idealOrder J := by
  by_cases hI : I = ⊥
  subst hI
  have hbm : (⊥) * J = ⊥ := by simp_all
  rw [hbm, idealOrder_bot]
  exact le_antisymm le_self_add le_top
  by_cases hJ : J = ⊥
  subst hJ
  have hbm : I * (⊥) = ⊥ := by simp_all
  rw [hbm, idealOrder_bot]
  exact le_antisymm le_add_self le_top
  obtain ⟨r, hr⟩ := exists_idealOrder_eq_coe hI
  obtain ⟨s, hs⟩ := exists_idealOrder_eq_coe hJ
  have hIr :=
    (le_idealOrder_iff I r).mp $ le_of_eq hr.symm
  have hJs :=
    (le_idealOrder_iff J s).mp $ le_of_eq hs.symm
  let _a0 := m16 R ^ (r + 1)
  have hIn : ¬ I ≤ _a0 := by
    intro hc
    have hle := mpr_ (le_idealOrder_iff I $ r + 1) hc
    rw [hr] at hle
    have hnat : r + 1 ≤ r := by exact_mod_cast hle
    omega
  let _a1 := m16 R ^ (s + 1)
  have hJn : ¬ J ≤ _a1 := by
    intro hc
    have hle := mpr_ (le_idealOrder_iff J $ s + 1) hc
    rw [hs] at hle
    have hnat : s + 1 ≤ s := by exact_mod_cast hle
    omega
  obtain ⟨a, haI, han⟩ : ∃ a ∈ I, a ∉ _a0 := by
    by_contra hc
    push Not at hc
    exact hIn fun y hy => hc y hy
  obtain ⟨b, hbJ, hbn⟩ : ∃ b ∈ J, b ∉ _a1 := by
    by_contra hc
    push Not at hc
    exact hJn fun y hy => hc y hy
  have h2 : I * J ≤ m16 R ^ (r + s) := by
    rw [pow_add]
    exact mul_mono hIr hJs
  rw [idealOrder_eq_of_le_of_not_le h2 fun hc => mul_notMem_maximalIdeal_pow_add_succ x D hx hD hDD hunit (hIr haI) han (hJs hbJ) hbn $ hc $ mul_mem_mul haI hbJ, hr, hs]
  exact cast_add r s

theorem idealOrder_pow (I : Ideal R) (c : ℕ) :
    idealOrder (I ^ c) = (c : ENat) * idealOrder I := by
  induction c with
  | zero =>
    rw [pow_zero, one_eq_top, idealOrder_top]
    simp
  | succ c ih =>
    rw [pow_succ, idealOrder_mul x D hx hD hDD hunit, ih, cast_add, cast_one, add_mul,
      one_mul]
end
end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution.TaylorExpansion

section

variable {A R : Type} [CommRing A] [CommRing R] [Algebra A R]

section
variable (D : Derivation A R R) (n : ℕ) (f g : R)
theorem iterate_deriv_mul_eq_sum_nsmul :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let _a0 := ⇑D
    have key : ∀ i,
        ⇑D (n.choose i • (_a0^[i] f * _a0^[n - i] g))
          = n.choose i • (_a0^[i] f * _a0^[n - i + 1] g)
            + n.choose i • (_a0^[i + 1] f * _a0^[n - i] g) := by
      intro i
      rw [map_nsmul, leibniz, smul_eq_mul, smul_eq_mul,
        ← iterate_succ_apply' (⇑D) (n - i) g,
        ← iterate_succ_apply' (⇑D) i f,
        mul_comm (_a0^[n - i] g) (_a0^[i + 1] f), smul_add]
    let _a1 := range $ n + 1
    have e3 : ∑ i ∈ _a1, n.choose (i + 1) • (_a0^[i + 1] f * _a0^[n - i] g)
        = ∑ i ∈ range n, n.choose (i + 1) • (_a0^[i + 1] f * _a0^[n - i] g) := by
      rw [sum_range_succ, choose_eq_zero_of_lt $ show n < n + 1 by omega, zero_smul,
        add_zero]
    have e1 : ∑ i ∈ _a1, n.choose i • (_a0^[i] f * _a0^[n - i + 1] g)
        = (∑ i ∈ range n, n.choose (i + 1) • (_a0^[i + 1] f * _a0^[n - i] g))
          + f * _a0^[n + 1] g := by
      have inner : ∑ i ∈ range n,
            n.choose (i + 1) • (_a0^[i + 1] f * _a0^[n - (i + 1) + 1] g)
          = ∑ i ∈ range n, n.choose (i + 1) • (_a0^[i + 1] f * _a0^[n - i] g) := by
        refine sum_congr rfl fun i hi => ?_
        have h := Finset.mem_range.mp hi
        have hi' : n - (i + 1) + 1 = n - i := by omega
        rw [hi']
      rw [sum_range_succ', inner]
      simp [choose_zero_right, one_smul, iterate_zero_apply]
    let _a2 := n + 1
    let _a3 := range $ n + 1 + 1
    have e2 : ∑ i ∈ _a3,
          _a2.choose i • (_a0^[i] f * _a0^[n + 1 - i] g)
        = ((∑ i ∈ _a1, n.choose i • (_a0^[i + 1] f * _a0^[n - i] g))
            + ∑ i ∈ range n, n.choose (i + 1) • (_a0^[i + 1] f * _a0^[n - i] g))
          + f * _a0^[n + 1] g := by
      have inner2 : ∑ i ∈ _a1,
            _a2.choose (i + 1) • (_a0^[i + 1] f * _a0^[n + 1 - (i + 1)] g)
          = (∑ i ∈ _a1, n.choose i • (_a0^[i + 1] f * _a0^[n - i] g))
            + ∑ i ∈ range n, n.choose (i + 1) • (_a0^[i + 1] f * _a0^[n - i] g) := by
        rw [← e3, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        have hs : n + 1 - (i + 1) = n - i := by omega
        rw [choose_succ_succ n i, hs, add_smul]
      rw [sum_range_succ', inner2]
      simp [choose_zero_right, one_smul, iterate_zero_apply]
    calc _a0^[n + 1] (f * g)
        = ⇑D (_a0^[n] (f * g)) := iterate_succ_apply' _ _ _
      _ = ⇑D (∑ i ∈ _a1, n.choose i • (_a0^[i] f * _a0^[n - i] g)) := by
            rw [ih]
      _ = ∑ i ∈ _a1, ⇑D (n.choose i • (_a0^[i] f * _a0^[n - i] g)) := by
            rw [map_sum]
      _ = ∑ i ∈ _a1, (n.choose i • (_a0^[i] f * _a0^[n - i + 1] g)
            + n.choose i • (_a0^[i + 1] f * _a0^[n - i] g)) :=
            sum_congr rfl fun i _ => key i
      _ = (∑ i ∈ _a1, n.choose i • (_a0^[i] f * _a0^[n - i + 1] g))
            + ∑ i ∈ _a1, n.choose i • (_a0^[i + 1] f * _a0^[n - i] g) :=
            sum_add_distrib
      _ = ∑ i ∈ _a3,
            _a2.choose i • (_a0^[i] f * _a0^[n + 1 - i] g) := by
            rw [e1, e2]
            ring

theorem iterate_deriv_mul :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ range (n + 1), (n.choose i : R) * ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  rw [iterate_deriv_mul_eq_sum_nsmul D n f g]
  exact sum_congr rfl fun i _ => by rw [nsmul_eq_mul]
end

end

section

variable {A R S : Type} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

section
variable (σ : R →+* S) (D : Derivation A R R)
def coeff (i : ℕ) (f : R) : S :=
  algebraMap ℚ S ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f)

section
variable (be_ : S) (N : ℕ)
def truncatedSeries (f : R) : S :=
  ∑ j ∈ range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * be_ ^ j

@[simp]
theorem truncatedSeries_apply (f : R) :
    truncatedSeries σ D be_ N f =
      ∑ j ∈ range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * be_ ^ j :=
  rfl

section
variable (hN : 1 ≤ N)
include hN
theorem truncatedSeries_of_deriv_eq_zero (f : R) (hf : D f = 0) : truncatedSeries σ D be_ N f = σ f := by
  have key : ∀ k, (⇑D)^[k + 1] f = 0 := by simp_all
  rw [truncatedSeries_apply, sum_eq_single 0]
  simp
  intro b _ hb0
  obtain ⟨k, rfl⟩ := exists_eq_succ_of_ne_zero hb0
  rw [key k]
  simp
  intro h
  exact absurd (Finset.mem_range.mpr (by omega : 0 < N)) h

theorem truncatedSeries_sub_mem_span_singleton (f : R) :
    truncatedSeries σ D be_ N f - σ f ∈ Ideal.span ({be_} : Set S) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, sy_ $ succ_pred_eq_of_pos hN⟩
  have key : truncatedSeries σ D be_ (M + 1) f - σ f =
      ∑ j ∈ range M,
        algebraMap ℚ S (((j + 1).factorial : ℚ)⁻¹) * σ ((⇑D)^[j + 1] f) * be_ ^ (j + 1) := by
    rw [truncatedSeries_apply, sum_range_succ']
    simp
  rw [key]
  refine m133 _ fun j _ => ?_
  rw [mem_span_singleton]
  exact dvd_mul_of_dvd_right (dvd_pow_self be_ j.succ_ne_zero) _

theorem truncatedSeries_one :
    truncatedSeries σ D be_ N 1 = 1 := by
  have h1 : D 1 = 0 := by simp
  rw [truncatedSeries_of_deriv_eq_zero σ D be_ N hN 1 h1, map_one]
end

theorem truncatedSeries_add (f g : R) :
    truncatedSeries σ D be_ N (f + g) = truncatedSeries σ D be_ N f + truncatedSeries σ D be_ N g := by
  have key : ∀ j, (⇑D)^[j] (f + g) = (⇑D)^[j] f + (⇑D)^[j] g := by simp_all
  simp only [truncatedSeries_apply]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [key j, map_add]
  ring

theorem mk_truncatedSeries_add
    J f g :
    Ideal.Quotient.mk J (truncatedSeries σ D be_ N $ f + g) =
      Ideal.Quotient.mk J (truncatedSeries σ D be_ N f) +
        Ideal.Quotient.mk J (truncatedSeries σ D be_ N g) := by
  rw [truncatedSeries_add, map_add]

theorem truncatedSeries_zero :
    truncatedSeries σ D be_ N 0 = 0 :=by simp_all
end
end

section
variable {T : Type}
theorem sum_range_sum_range_succ_eq_sum_sum_Ico [AddCommMonoid T] (N : ℕ) (h : ℕ → ℕ → T) :
    ∑ j ∈ range N, ∑ i ∈ range (j + 1), h i j
      = ∑ i ∈ range N, ∑ j ∈ Ico i N, h i j := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hR2 : ∑ i ∈ range N, ∑ j ∈ Ico i (N + 1), h i j
        = (∑ i ∈ range N, ∑ j ∈ Ico i N, h i j)
          + ∑ i ∈ range N, h i N := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      exact sum_Ico_succ_top (le_of_lt $ Finset.mem_range.mp hi) $ h i
    have hR3 : ∑ j ∈ Ico N (N + 1), h N j = h N N := by simp_all
    rw [sum_range_succ (fun j => ∑ i ∈ range (j + 1), h i j) N, sum_range_succ (fun i => ∑ j ∈ Ico i (N + 1), h i j) N, hR2, hR3, ih, sum_range_succ (h · N) N, add_assoc]

theorem sum_Ico_mul_pow_eq_sum_range [CommRing T] (a b : ℕ → T) (be_ : T) (N i : ℕ) :
    ∑ j ∈ Ico i N, a i * b (j - i) * be_ ^ j
      = ∑ k ∈ range (N - i), a i * b k * be_ ^ (i + k) := by
  rw [sum_Ico_eq_sum_range]
  refine sum_congr rfl fun k _ => ?_
  have hk : i + k - i = k := by omega
  simp [hk]

end

theorem coeff_eq {A' R' S' : Type} [CommRing A'] [CommRing R'] [CommRing S']
    [Algebra A' R'] [Algebra ℚ S'] (σ : R' →+* S') (D : Derivation A' R' R') (i : ℕ) (f : R') :
    coeff σ D i f = algebraMap ℚ S' ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f) := rfl

section
variable (σ : R →+* S) (D : Derivation A R R) (be_ : S) (N : ℕ)
section
variable (J : Ideal S)
section
variable (hbe_ : be_ ^ N ∈ J) (f g : R)
include hbe_
theorem truncatedSeries_mul_sub_mem :
    truncatedSeries σ D be_ N (f * g) - truncatedSeries σ D be_ N f * truncatedSeries σ D be_ N g ∈ J := by
  have hf : truncatedSeries σ D be_ N f
      = ∑ j ∈ range N, coeff σ D j f * be_ ^ j := rfl
  have hg : truncatedSeries σ D be_ N g
      = ∑ j ∈ range N, coeff σ D j g * be_ ^ j := rfl
  have _i36 : truncatedSeries σ D be_ N (f * g) = ∑ j ∈ range N, be_ ^ j * ∑ i ∈ range (j + 1), coeff σ D i f * coeff σ D (j - i) g := by
    rw [truncatedSeries_apply]
    refine sum_congr rfl fun j _ => ?_
    rw [iterate_deriv_mul D j f g, map_sum, mul_sum, sum_mul, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hij := mp_ lt_succ_iff $ Finset.mem_range.mp hi
    let _a1 := (j - i).factorial
    have key : algebraMap ℚ S (j.factorial⁻¹) * (j.choose i) = algebraMap ℚ S (i.factorial⁻¹) * algebraMap ℚ S ((_a1 : ℚ)⁻¹) := by
      have hj : j.factorial ≠ 0 := mpr_ cast_ne_zero (factorial_pos j).ne'
      have hi : i.factorial ≠ 0 := mpr_ cast_ne_zero (factorial_pos i).ne'
      have hji : (_a1 : ℚ) ≠ 0 := mpr_ cast_ne_zero (factorial_pos $ j - i).ne'
      have h1 : (j.choose i) * i.factorial * (_a1 : ℚ)
          = (j.factorial : ℚ) := by
        exact_mod_cast choose_mul_factorial_mul_factorial hij
      have key : (j.factorial : ℚ)⁻¹ * (j.choose i : ℚ)
          = (i.factorial : ℚ)⁻¹ * (_a1 : ℚ)⁻¹ := by
        field_simp
        linear_combination h1
      simpa only [map_mul, map_natCast] using (congrArg (algebraMap ℚ S) key)
    simp [coeff_eq, map_mul, map_natCast]
    linear_combination (σ ((⇑D)^[i] f) * σ ((⇑D)^[j - i] g) * be_ ^ j) * key
  rw [_i36, hf, hg]
  let a := fun i => coeff σ D i f
  let b := fun i => coeff σ D i g
  have hprod : (∑ j ∈ range N, a j * be_ ^ j) * (∑ j ∈ range N, b j * be_ ^ j)
      = ∑ i ∈ range N, ∑ k ∈ range N, a i * b k * be_ ^ (i + k) := by
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have htri : (∑ j ∈ range N, be_ ^ j * ∑ i ∈ range (j + 1), a i * b (j - i))
      = ∑ i ∈ range N, ∑ k ∈ range (N - i), a i * b k * be_ ^ (i + k) := by
    have e1 : (∑ j ∈ range N, be_ ^ j * ∑ i ∈ range (j + 1), a i * b (j - i))
        = ∑ j ∈ range N, ∑ i ∈ range (j + 1), a i * b (j - i) * be_ ^ j := by
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring
    exact tr_ e1 $ tr_ (sum_range_sum_range_succ_eq_sum_sum_Ico N fun i j => a i * b (j - i) * be_ ^ j) $ sum_congr rfl fun i _ => sum_Ico_mul_pow_eq_sum_range a b be_ N i
  have hdist : (∑ i ∈ range N, ∑ k ∈ range (N - i), a i * b k * be_ ^ (i + k))
      - (∑ i ∈ range N, ∑ k ∈ range N, a i * b k * be_ ^ (i + k))
      = ∑ i ∈ range N, ((∑ k ∈ range (N - i), a i * b k * be_ ^ (i + k))
          - ∑ k ∈ range N, a i * b k * be_ ^ (i + k)) := by simp_all
  rw [hprod, htri, hdist]
  refine m133 _ fun i hi => ?_
  have hiN := Finset.mem_range.mp hi
  let _a0 := Ico (N - i) N
  have hsplit : ∑ k ∈ range N, a i * b k * be_ ^ (i + k)
      = (∑ k ∈ range (N - i), a i * b k * be_ ^ (i + k))
        + ∑ k ∈ _a0, a i * b k * be_ ^ (i + k) := by
    rw [range_eq_Ico, range_eq_Ico]
    exact sy_ $ sum_Ico_consecutive _ (zero_le $ N - i) $ sub_le N i
  rw [hsplit]
  have hre : (∑ k ∈ range (N - i), a i * b k * be_ ^ (i + k))
      - ((∑ k ∈ range (N - i), a i * b k * be_ ^ (i + k))
        + ∑ k ∈ _a0, a i * b k * be_ ^ (i + k))
      = -(∑ k ∈ _a0, a i * b k * be_ ^ (i + k)) := by ring
  rw [hre]
  refine neg_mem $ m133 _ fun k hk => ?_
  have hk1 := an1 $ mp_ mem_Ico hk
  have hpow : be_ ^ (i + k) ∈ J := by
    have he : i + k = N + (i + k - N) := by omega
    rw [he, pow_add]
    exact mul_mem_right _ _ hbe_
  exact mul_mem_left _ _ hpow

theorem mk_truncatedSeries_mul :
    Ideal.Quotient.mk J (truncatedSeries σ D be_ N $ f * g) =
      Ideal.Quotient.mk J (truncatedSeries σ D be_ N f) *
        Ideal.Quotient.mk J (truncatedSeries σ D be_ N g) := by
  rw [Ideal.Quotient.eq.mpr $ truncatedSeries_mul_sub_mem σ D be_ N J hbe_ f g, map_mul]
end

section
variable (hN : 1 ≤ N) (hbe_ : be_ ^ N ∈ J)
def truncatedSeriesRingHom : R →+* S ⧸ J :=
  { toFun := fun f => Ideal.Quotient.mk J (truncatedSeries σ D be_ N f)
    map_one' := by
      have h1 : D 1 = 0 := by simp
      rw [truncatedSeries_of_deriv_eq_zero σ D be_ N hN 1 h1]
      simp
    map_mul' := mk_truncatedSeries_mul σ D be_ N J hbe_
    map_zero' := by
      rw [truncatedSeries_zero, map_zero]
    map_add' := mk_truncatedSeries_add σ D be_ N J }

@[simp]
theorem truncatedSeriesRingHom_apply (f : R) :
    truncatedSeriesRingHom σ D be_ N J hN hbe_ f = Ideal.Quotient.mk J (truncatedSeries σ D be_ N f) :=
  rfl
end
end
end

end

end FunctorialResolution.EmbeddedResolution.TaylorExpansion
end
section
namespace FunctorialResolution.EmbeddedResolution

section

variable {k S : Type} [CommRing k] [CommRing S] [Algebra k S]

theorem exists_mul_deriv_pow_eq_pow_mul {k : Type} [CommRing k] {S : Type}
    [CommRing S] [Algebra k S] (De_ : Derivation k S S) (b : S) (n : ℕ) :
    ∃ c : S, b * De_ (b ^ n) = b ^ n * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + De_ b, ?_⟩
      let _a0 := b ^ m
      have hbp : b ^ (m + 1) = b * _a0 := by ring
      have hl : De_ (b * _a0) = b * De_ _a0 + _a0 * De_ b := by
        simp
      rw [hbp, hl]
      linear_combination b * hc

theorem pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le (k : Type) [CommRing k] {S : Type} [CommRing S] [Algebra k S]
    (M J : Ideal S) (De_ : Derivation k S S) (b : S)
    (hMJ : M * derivIdeal k J ≤ J) (hb : b ∈ M) :
    ∀ j g, g ∈ J → b ^ j * (⇑De_)^[j] g ∈ J := by
  intro j
  induction j with
  | zero =>
      intro g hg
      simpa using hg
  | succ j ih =>
      intro g hg
      have hIH := ih g hg
      obtain ⟨c, hc⟩ := exists_mul_deriv_pow_eq_pow_mul De_ b j
      let _a0 := (⇑De_)^[j] g
      let _a1 := b ^ j
      have hleib : De_ (_a1 * _a0)
          = _a1 * De_ _a0 + _a0 * De_ _a1 := by
        simp
      have hEq : b ^ (j + 1) * (⇑De_)^[j + 1] g
          = b * De_ (_a1 * _a0) - c * (_a1 * _a0) := by
        rw [iterate_succ_apply' (⇑De_) j g, hleib]
        linear_combination (-_a0) * hc
      rw [hEq]
      exact m162 J (hMJ $ mul_mem_mul hb $ derivation_apply_mem_derivIdeal k J De_ hIH) $ mul_mem_left J c hIH

end

section

variable {A R S : Type} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

section
variable (σ : R →+* S) (D : Derivation A R R) (be_ : S)
theorem truncatedSeries_length_one f :
    TaylorExpansion.truncatedSeries σ D be_ 1 f = σ f :=by simp_all
theorem truncatedSeries_of_deriv_deriv_eq_zero N
    (hN : 2 ≤ N) f (hf : D (D f) = 0) :
    TaylorExpansion.truncatedSeries σ D be_ N f = σ f + σ (D f) * be_ := by
  have h2 : (⇑D)^[2] f = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iterate_add_apply]
    simp [hf]
  have hvan : ∀ j, 2 ≤ j → (⇑D)^[j] f = 0 := by
    intro j hj
    obtain ⟨m, rfl⟩ := exists_eq_add_of_le hj
    rw [add_comm, iterate_add_apply, h2]
    exact iterate_fixed (by simp) m
  have hsum : ∑ j ∈ range 2,
        algebraMap ℚ S (j.factorial⁻¹) * σ ((⇑D)^[j] f) * be_ ^ j
      = ∑ j ∈ range N,
        algebraMap ℚ S (j.factorial⁻¹) * σ ((⇑D)^[j] f) * be_ ^ j := by
    refine sum_subset (fun j hj => Finset.mem_range.mpr $ lt_of_lt_of_le (Finset.mem_range.mp hj) hN) ?_
    intro j _ hj
    have hj2 : 2 ≤ j := by
      rcases m63 j 2 with h | h
      simp_all
      exact h
    rw [hvan j hj2]
    simp
  rw [TaylorExpansion.truncatedSeries_apply, ← hsum]
  simp [sum_range_succ]
end

end

section

open IsLocalRing

section
variable (P : Type)
def IsTaylorExpansionOn [CommRing P] {A R B : Type} [CommRing A] [CommRing R]
    [CommRing B] [Algebra P R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (ph_ ph' : R →+* B) (D : Derivation A R R) (be_ : B) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ x : P,
    TaylorExpansion.truncatedSeries ph_ D be_ N (algebraMap P R x) - ph' (algebraMap P R x) ∈ maximalIdeal B ^ N

theorem sub_mem_pow_succ_of_sub_mem_pow {R B : Type} [CommRing P] [CommRing R]
    [CommRing B] [Algebra P R] [FormallyUnramified P R]
    (ph' : R →+* B) (m : Ideal B) (T : R → B) (k : ℕ) (hk : 1 ≤ k)
    (hadd : ∀ x y : R, T (x + y) = T x + T y)
    (hone : T 1 = 1)
    (hmul : ∀ x y : R, T (x * y) - T x * T y ∈ m ^ (k + 1))
    (hP : ∀ x : P, T (algebraMap P R x) - ph' (algebraMap P R x) ∈ m ^ (k + 1))
    (hind : ∀ x : R, T x - ph' x ∈ m ^ k) (x : R) :
    T x - ph' x ∈ m ^ (k + 1) := by
  let _a0 := m ^ (k + 1)
  let _c0 := B ⧸ _a0
  let _ := ph'.toAlgebra
  let _ := (ph'.comp $ algebraMap P R).toAlgebra
  have : IsScalarTower P R B := of_algebraMap_eq fun _ => rfl
  have : IsScalarTower P R _c0 := of_algebraMap_eq fun _ => rfl
  have hleib : ∀ a b,
      T (a * b) - ph' (a * b) - (ph' a * (T b - ph' b) + ph' b * (T a - ph' a)) ∈ _a0 := by
    intro a b
    have h1 := hmul a b
    have h2 : (T a - ph' a) * (T b - ph' b) ∈ _a0 := by
      have h3 :=
        mul_mem_mul (hind a) $ hind b
      have h4 : m ^ k * m ^ k ≤ _a0 := by
        rw [← pow_add]
        exact pow_le_pow_right $ by omega
      exact h4 h3
    have heq : T (a * b) - ph' (a * b) - (ph' a * (T b - ph' b) + ph' b * (T a - ph' a))
        = T (a * b) - T a * T b + (T a - ph' a) * (T b - ph' b) := by
      rw [map_mul]
      ring
    rw [heq]
    exact m128 _ h1 h2
  let d : Derivation P R _c0 :=
    { toFun := fun y => m5 _a0 $ T y - ph' y
      map_add' := by
        intro a b
        show m5 _a0 (T (a + b) - ph' (a + b))
            = m5 _a0 (T a - ph' a)
              + m5 _a0 (T b - ph' b)
        have harg : T (a + b) - ph' (a + b) = T a - ph' a + (T b - ph' b) := by
          rw [hadd, map_add]
          ring
        rw [harg, map_add]
      map_smul' := by
        intro p a
        show m5 _a0 (T (p • a) - ph' (p • a))
            = p • m5 _a0 (T a - ph' a)
        simp only [smul_def]
        let _a1 := algebraMap P R p
        have halg : (algebraMap P _c0) p
            = m5 _a0 (ph' _a1) := rfl
        rw [halg, ← map_mul]
        refine Ideal.Quotient.eq.mpr ?_
        have h1 := hleib _a1 a
        let _s0 := T _a1 - ph' _a1
        have h2 : ph' a * _s0 ∈ _a0 :=
          mul_mem_left _ _ $ hP p
        have h3 := m128 _ h1 h2
        let _m0 := _a1 * a
        have heq : T _m0 - ph' _m0
              - (ph' _a1 * (T a - ph' a)
                + ph' a * _s0)
              + ph' a * _s0
            = T _m0 - ph' _m0
              - ph' _a1 * (T a - ph' a) := by
          ring
        rwa [heq] at h3
      map_one_eq_zero' := by
        show m5 _a0 (T 1 - ph' 1) = 0
        rw [hone, map_one, sub_self, map_zero]
      leibniz' := by
        intro a b
        show m5 _a0 (T (a * b) - ph' (a * b))
            = a • m5 _a0 (T b - ph' b)
              + b • m5 _a0 (T a - ph' a)
        simp only [smul_def]
        have halg : ∀ y, (algebraMap R _c0) y
            = m5 _a0 (ph' y) := fun _ => rfl
        rw [halg a, halg b, ← map_mul, ← map_mul, ← map_add]
        exact Ideal.Quotient.eq.mpr $ hleib a b }
  have hdx :=
    by
    have h0 : m13 P R x = 0 := m111 _ _
    have h1 :=
      liftKaehlerDifferential_comp_D d x
    rw [h0, map_zero] at h1
    exact sy_ h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp hdx

section
variable [hv1_0 : CommRing P] {A R B : Type} [CommRing A] [CommRing R] [CommRing B] [hv1_5 : Algebra P R] [Algebra A R] [hv1_7 : FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B] (ph_ ph' : R →+* B) (D : Derivation A R R) (be_ : B) (hcong : ∀ f : R, ph_ f - ph' f ∈ maximalIdeal B) (hbe_ : be_ ∈ maximalIdeal B) (hrep : IsTaylorExpansionOn P ph_ ph' D be_)
include hv1_0 hv1_5 hv1_7 hcong hbe_ hrep
section
variable (N : ℕ) (hN : 1 ≤ N) (f : R)
include hN
theorem truncatedSeries_sub_mem_maximalIdeal_pow :
    TaylorExpansion.truncatedSeries ph_ D be_ N f - ph' f ∈ maximalIdeal B ^ N := by
  let _a0 := maximalIdeal B ^ N
  have hbeN := pow_mem_pow hbe_ N
  have hmulN :=
    fun x y => TaylorExpansion.truncatedSeries_mul_sub_mem ph_ D be_ N _a0 hbeN x y
  have hbound := fun x => hrep N hN x
  have hbase : ∀ x, TaylorExpansion.truncatedSeries ph_ D be_ N x - ph' x ∈ maximalIdeal B ^ 1 := by
    intro x
    rw [pow_one]
    have h2 : m17 ({be_} : Set B) ≤ maximalIdeal B := by simp_all
    have h4 : TaylorExpansion.truncatedSeries ph_ D be_ N x - ph' x
        = TaylorExpansion.truncatedSeries ph_ D be_ N x - ph_ x + (ph_ x - ph' x) := by ring
    rw [h4]
    exact m128 _ (h2 $ TaylorExpansion.truncatedSeries_sub_mem_span_singleton ph_ D be_ N hN x) $ hcong x
  have key : ∀ k, 1 ≤ k → k ≤ N →
      ∀ x, TaylorExpansion.truncatedSeries ph_ D be_ N x - ph' x ∈ maximalIdeal B ^ k := by
    intro k
    induction k with
    | zero => intro h; exact absurd h $ by omega
    | succ k ih =>
      intro _ hkN
      rcases m73 k with hk0 | hk1
      subst hk0
      exact hbase
      have hk1' := hk1
      have hkle : _a0 ≤ maximalIdeal B ^ (k + 1) :=
        pow_le_pow_right hkN
      exact fun x =>
        sub_mem_pow_succ_of_sub_mem_pow P ph' (maximalIdeal B) (TaylorExpansion.truncatedSeries ph_ D be_ N) k hk1'
          (fun a b => TaylorExpansion.truncatedSeries_add ph_ D be_ N a b)
          (TaylorExpansion.truncatedSeries_one ph_ D be_ N hN)
          (fun a b => hkle $ hmulN a b)
          (fun p => hkle $ hbound p)
          (ih hk1' $ by omega) x
  exact key N hN le_rfl f

end

end
end

theorem isTaylorExpansionOn_mvPolynomial {k : Type} [CommRing k] {ι : Type}
    {A R B : Type} [CommRing A] [CommRing R] [CommRing B]
    [Algebra (MvPolynomial ι k) R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (ph_ ph' : R →+* B) (D : Derivation A R R) (be_ : B)
    (hbe_ : be_ ∈ maximalIdeal B)
    (hconst : ∀ c : k,
      ph_ (algebraMap (MvPolynomial ι k) R $ MvPolynomial.C c) =
        ph' (algebraMap (MvPolynomial ι k) R $ MvPolynomial.C c))
    (hDconst : ∀ c : k, D (algebraMap (MvPolynomial ι k) R $ MvPolynomial.C c) = 0)
    (hvar : ∀ i N, 1 ≤ N →
      TaylorExpansion.truncatedSeries ph_ D be_ N (algebraMap (MvPolynomial ι k) R $ MvPolynomial.X i) -
          ph' (algebraMap (MvPolynomial ι k) R $ MvPolynomial.X i) ∈ maximalIdeal B ^ N) :
    IsTaylorExpansionOn (MvPolynomial ι k) ph_ ph' D be_ := by
  intro N hN x
  let _a2 := maximalIdeal B ^ N
  have key :
      (TaylorExpansion.truncatedSeriesRingHom ph_ D be_ N _a2 hN $ pow_mem_pow hbe_ N).comp
          (algebraMap (MvPolynomial ι k) R) =
        ((m5 _a2).comp ph').comp
          (algebraMap (MvPolynomial ι k) R) := by
    apply ringHom_ext
    intro c
    have h1 : TaylorExpansion.truncatedSeries ph_ D be_ N
          (algebraMap (MvPolynomial ι k) R $ m8 c)
        = ph' (algebraMap (MvPolynomial ι k) R $ m8 c) := by
      rw [TaylorExpansion.truncatedSeries_of_deriv_eq_zero ph_ D be_ N hN
        (algebraMap (MvPolynomial ι k) R $ m8 c) $ hDconst c]
      exact hconst c
    simp only [coe_comp, comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply, h1]
    intro i
    simp only [coe_comp, comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply]
    exact Ideal.Quotient.eq.2 $ hvar i N hN
  have h := RingHom.congr_fun key x
  simp only [coe_comp, comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply] at h
  exact Ideal.Quotient.eq.1 h

theorem mem_of_forall_mem_sup_maximalIdeal_pow {B : Type} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (J : Ideal B) (hJ : J ≤ IsLocalRing.maximalIdeal B) (x : B)
    (hx : ∀ N : ℕ, x ∈ J ⊔ IsLocalRing.maximalIdeal B ^ N) : x ∈ J := by
  have hmne := (isMaximal B).ne_top
  have hJne : J ≠ ⊤ := by
    intro h
    apply hmne
    rw [eq_top_iff]
    rwa [h] at hJ
  have : Nontrivial $ B ⧸ J := by
    refine ⟨0, 1, fun h => hJne ?_⟩
    rw [eq_top_iff_one]
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [map_one]
    exact sy_ h
  have :=
    of_surjective' (m5 J) mk_surjective
  let _a0 := m6 (m5 J) $ m16 B
  have hIne : _a0 ≠ ⊤ := by
    intro h
    have h1 : 1 ∈ _a0 := by simp_all
    obtain ⟨y, hy, hy1⟩ :=
      (mem_map_iff_of_surjective (m5 J) mk_surjective).1 h1
    have h2 : 1 - y ∈ J := by
      refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
      rw [map_sub, hy1, map_one, sub_self]
    refine hmne $ (eq_top_iff_one _).2 ?_
    have h4 := m60 (m16 B) (hJ h2) hy
    simp at h4
  have hbot : (⨅ i : ℕ,
      _a0 ^ i) = ⊥ := by
    apply iInf_pow_eq_bot_of_isLocalRing
    exact hIne
  have hmem : ∀ N, m5 J x ∈
      _a0 ^ N := by
    intro N
    obtain ⟨j, hj, y, hy, hxy⟩ := mem_sup.1 $ hx N
    have hxe : m5 J x = m5 J y := by
      rw [← hxy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
    rw [hxe]
    exact (m219 (m5 J) (m16 B) N).le
      (mem_map_of_mem _ hy)
  have hfin :=
    (mem_iInf _).2 hmem
  rw [hbot, mem_bot] at hfin
  exact Ideal.Quotient.eq_zero_iff_mem.1 hfin

section
variable (P : Type) [CommRing P] {A R B : Type} [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R] [FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B] (ph_ ph' : R →+* B) (D : Derivation A R R) (be_ : B)
section
variable (hcong : ∀ f : R, ph_ f - ph' f ∈ maximalIdeal B) (hbe_ : be_ ∈ maximalIdeal B) (hrep : IsTaylorExpansionOn P ph_ ph' D be_)
include hcong hbe_ hrep
theorem sub_mem_of_isTaylorExpansionOn
    (I : Ideal B) (hI : be_ ∈ I) (f : R) :
    ph_ f - ph' f ∈ I := by
  let _a0 := m17 ({be_} : Set B)
  have hmem : ph_ f - ph' f ∈ _a0 := by
    have h : ph_ f - ph' f ∈ ⨅ N : ℕ, (m17 ({be_} : Set B) ⊔ maximalIdeal B ^ N) := by
      refine Submodule.mem_iInf _ |>.2 ?_
      intro N
      rcases m73 N with rfl | hN
      have h0 : (m17 ({be_} : Set B) ⊔ maximalIdeal B ^ 0) = ⊤ := by
        rw [pow_zero, one_eq_top, sup_top_eq]
      rw [h0]
      exact mem_top
      have h1 :=
        TaylorExpansion.truncatedSeries_sub_mem_span_singleton ph_ D be_ N hN f
      have hEq : ph_ f - ph' f
          = (TaylorExpansion.truncatedSeries ph_ D be_ N f - ph' f) - (TaylorExpansion.truncatedSeries ph_ D be_ N f - ph_ f) := by
        ring
      rw [hEq]
      exact m162 _ (mem_sup_right $ truncatedSeries_sub_mem_maximalIdeal_pow P ph_ ph' D be_ hcong hbe_ hrep N hN f) $ mem_sup_left h1
    exact mem_of_forall_mem_sup_maximalIdeal_pow _a0
      (Ideal.span_le.2 $ Set.singleton_subset_iff.2 hbe_) (ph_ f - ph' f) $ (mem_iInf _).1 h
  exact (Ideal.span_le.mpr $ Set.singleton_subset_iff.mpr hI) hmem
end

theorem map_le_map_of_pow_mul_iterate_deriv_mem b J
    (hcong : ∀ f : R, ph_ f - ph' f ∈ maximalIdeal B)
    (hbe_ : be_ ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P ph_ ph' D be_)
    (hb : ph_ b = be_)
    (hstab : ∀ j g, g ∈ J → b ^ j * (⇑D)^[j] g ∈ J) :
    Ideal.map ph' J ≤ Ideal.map ph_ J := by
  refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
  refine Ideal.mem_comap.mpr ?_
  by_cases htop : m6 ph_ J = ⊤
  simp_all
  refine mem_of_forall_mem_sup_maximalIdeal_pow (m6 ph_ J)
    (le_maximalIdeal htop) (ph' g) ?_
  intro n
  by_cases hn : n = 0
  simp_all
  have hn1 := mpr_ one_le_iff_ne_zero hn
  let _a0 := TaylorExpansion.truncatedSeries ph_ D be_ n g
  have h1 : _a0 ∈ m6 ph_ J := by
    have hmem : TaylorExpansion.truncatedSeries ph_ D (ph_ b) n g ∈ m6 ph_ J := by
      rw [TaylorExpansion.truncatedSeries_apply]
      refine m133 _ fun j _ => ?_
      have h :=
        mem_map_of_mem ph_ $ hstab j g hg
      rw [map_mul, map_pow] at h
      have h2 := mul_mem_left (m6 ph_ J) (algebraMap ℚ B $ j.factorial⁻¹) h
      let _a0 := (⇑D)^[j] g
      have h3 : algebraMap ℚ B (j.factorial⁻¹) * ph_ _a0 * ph_ b ^ j
          = algebraMap ℚ B (j.factorial⁻¹) * (ph_ b ^ j * ph_ _a0) := by
        ring
      rwa [h3]
    rwa [hb] at hmem
  have hEq : ph' g = _a0 - (_a0 - ph' g) := by
    ring
  rw [hEq]
  exact m162 _ (mem_sup_left h1) $ mem_sup_right $ truncatedSeries_sub_mem_maximalIdeal_pow P ph_ ph' D be_ hcong hbe_ hrep n hn1 g
end

end

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable (k : Type) [Field k] (n : Type)
abbrev affineSpaceIndexedBy : Sch :=
  AffineSpace n $ Sp k

abbrev affineSpaceIndexedByToSpec :
    affineSpaceIndexedBy k n ⟶ Sp k :=
  affineSpaceIndexedBy k n ↘ Sp k
end

section
variable {k : Type} [Field k] {Y : Sch}
section
variable {n : Type} (f : Y ⟶ affineSpaceIndexedBy k n) (i : n)
def pullbackCoord : Γ(Y, ⊤) :=
  f.appTop $ AffineSpace.coord (Sp k) i

@[simp]
theorem pullbackCoord_def :
    pullbackCoord f i = f.appTop (AffineSpace.coord (Sp k) i) := rfl
end

section
variable (n m : ℕ)
section
variable (f : Y ⟶ affineSpaceIndexedBy k (UFin n))
def coordVectorInl :
    UFS n m → Γ(Y, ⊤) :=
  fun i => elim (fun a => pullbackCoord f $ up a) (fun _ => 0) i.down

@[simp]
theorem coordVectorInl_inl (a : Fin n) :
    coordVectorInl n m f (up $ Sum.inl a) = pullbackCoord f (up a) := rfl

@[simp]
theorem coordVectorInl_inr (b : Fin m) :
    coordVectorInl n m f (up $ Sum.inr b) = 0 := rfl
end

section
variable (f : Y ⟶ affineSpaceIndexedBy k (UFin m))
def coordVectorInr :
    UFS n m → Γ(Y, ⊤) :=
  fun i => elim (fun _ => 0) (fun b => pullbackCoord f $ up b) i.down

@[simp]
theorem coordVectorInr_inl (a : Fin n) :
    coordVectorInr n m f (up $ Sum.inl a) = 0 := rfl

@[simp]
theorem coordVectorInr_inr (b : Fin m) :
    coordVectorInr n m f (up $ Sum.inr b) = pullbackCoord f (up b) := rfl
end
end
end


variable {X Y : Sch} {W : Opn X} {V : Opn Y} {n : Type}

section
variable (g : V.toScheme ⟶ AffineSpace n W.toScheme)
noncomputable def chartCoeffHom :
    (X.sec W) →+* (Y.sec V) :=
  (W.topIso.inv ≫ (g ≫ (AffineSpace n W.toScheme ↘ W.toScheme)).appTop ≫ V.topIso.hom).hom

noncomputable def chartVar (j : n) : (Y.sec V) :=
  V.topIso.hom.hom $ g.appTop.hom $ AffineSpace.coord (S := W.toScheme) j
end

noncomputable def chartEvalHom (_hW : IsAffineOpen W) (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    MvPolynomial n (X.sec W) →+* (Y.sec V) :=
  MvPolynomial.eval₂Hom (chartCoeffHom g) $ chartVar g

section
variable {X' Y' : Sch} (h : Y' ⟶ X') (W' : Opn X') (V' : Opn Y') (e : V' ≤ h.pre W')
theorem resLE_appTop_eq :
    (h.resLE W' V' e).appTop = W'.topIso.hom ≫ appLE h W' V' e ≫ V'.topIso.inv := by
  simp

theorem resLE_appTop_conj_topIso_eq_appLE :
    W'.topIso.inv ≫ (h.resLE W' V' e).appTop ≫ V'.topIso.hom = appLE h W' V' e := by
  rw [resLE_appTop_eq]
  simp only [assoc, m213, m114, comp_id]
end

section
variable (hW : IsAffineOpen W)
include hW
section
variable (h : Y ⟶ X) (e) (g) (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e)
include hg
theorem chartEvalHom_comp_C :
    (chartEvalHom hW g).comp (MvPolynomial.C : (X.sec W) →+* MvPolynomial n (X.sec W)) =
      (appLE h W V e).hom := by
  have key : chartCoeffHom g = (appLE h W V e).hom := by
    simp only [chartCoeffHom, hg, resLE_appTop_conj_topIso_eq_appLE]
  refine m48 fun a => ?_
  have h1 : chartEvalHom hW g (m8 a) = chartCoeffHom g a := by simp [chartEvalHom]
  rw [m82, h1, key]

theorem chartEvalHom_C a :
    chartEvalHom hW g (MvPolynomial.C a) = (appLE h W V e).hom a :=
  RingHom.congr_fun (chartEvalHom_comp_C hW h e g hg) a
end

@[reducible]
noncomputable def chartAlgebra
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) :
    Algebra (MvPolynomial n $ X.sec W) $ Y.sec V :=
  (chartEvalHom hW g).toAlgebra

theorem chartAlgebra_isScalarTower (h : Y ⟶ X) e
    g
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    letI : Algebra (X.sec W) $ Y.sec V := (appLE h W V e).hom.toAlgebra
    letI := chartAlgebra hW g
    IsScalarTower W.sec (MvPolynomial n W.sec) V.sec := by
  let := (appLE h W V e).hom.toAlgebra
  let := chartAlgebra hW g
  refine of_algebraMap_eq fun a => ?_
  show (appLE h W V e).hom a = chartEvalHom hW g (algebraMap W.sec (MvPolynomial n W.sec) a)
  rw [m185, chartEvalHom_C hW h e g hg]
end

section
variable {R S : Type} [CommRing R] [CommRing S]
theorem algebraEtale_congr {f f' : R →+* S}
    (h : f = f') (hf : @Algebra.Etale R S _ _ f.toAlgebra) :
    @Algebra.Etale R S _ _ f'.toAlgebra := by
  subst h
  exact hf

end

theorem algebraEtale_comp_equiv {R R' S S' : Type} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] (eR : R' ≃+* R) (f : R →+* S) (eS : S ≃+* S')
    (hf : @Algebra.Etale R S _ _ f.toAlgebra) :
    @Algebra.Etale R' S' _ _ $ ((eS : S →+* S').comp $ f.comp (eR : R' →+* R)).toAlgebra := by
  let : Algebra R S := f.toAlgebra
  have : m121 R S := hf
  let : Algebra R' R := (eR : RingHom R' R).toAlgebra
  let _a0 := (eS : RingHom S S')
  let : Algebra R S' := (_a0.comp f).toAlgebra
  let : Algebra R' S' := (_a0.comp $ f.comp (eR : RingHom R' R)).toAlgebra
  have : IsScalarTower R' R S' := of_algebraMap_eq fun _ => rfl
  have : m121 R' R' := inferInstance
  have :=
    Algebra.Etale.of_equiv (R := R') (A := R') $ ofRingEquiv (f := eR) fun _ => rfl
  have :=
    Algebra.Etale.of_equiv (R := R) (A := S) $ ofRingEquiv (f := eS) fun _ => rfl
  exact Algebra.Etale.comp R' R S'

private theorem comp_appTop_apply {A B C : Sch} (f : A ⟶ B) (k : B ⟶ C) (z : Γ(C, ⊤)) :
    (f ≫ k).appTop.hom z = f.appTop.hom (k.appTop.hom z) :=
  congrArg (fun m : Γ(C, ⊤) ⟶ Γ(A, ⊤) => m4 m z) $ comp_appTop f k

theorem specMap_appTop_apply {R S : CRC} (u : R ⟶ S) (a : R) :
    (Spec.map u).appTop.hom ((GSpecIso R).inv.hom a) =
      (GSpecIso S).inv.hom (u.hom a) :=
  (congrArg (fun m : R ⟶ Γ(Spec S, ⊤) => m4 m a)
    (Scheme.ΓSpecIso_inv_naturality u)).symm

theorem isoSpec_hom_appTop_apply (Z : Sch) [IsAffine Z] (a : Γ(Z, ⊤)) :
    Z.isoSpec.hom.appTop.hom ((GSpecIso Γ(Z, ⊤)).inv.hom a) = a := by
  rw [isoSpec_hom, Scheme.toSpecΓ_appTop]
  exact congrArg (fun m : Γ(Z, ⊤) ⟶ Γ(Z, ⊤) => m4 m a)
    (GSpecIso Γ(Z, ⊤)).inv_hom_id

section
variable {X' : Sch} {W' : Opn X'} (hW : IsAffineOpen W')
noncomputable def affineOpenIsoSpec :
    W'.toScheme ≅ Spec (X'.sec W') :=
  haveI : IsAffine W'.toScheme := hW
  W'.toScheme.isoSpec ≪≫ Scheme.Spec.mapIso W'.topIso.symm.op

theorem affineOpenIsoSpec_hom_appTop_apply (a : (X'.sec W')) :
    (affineOpenIsoSpec hW).hom.appTop.hom ((GSpecIso $ X'.sec W').inv.hom a) =
      W'.topIso.inv.hom a := by
  have : IsAffine W'.toScheme := hW
  show (W'.toScheme.isoSpec.hom ≫ m12 W'.topIso.symm.hom).appTop.hom
      ((GSpecIso W'.sec).inv.hom a) = W'.topIso.inv.hom a
  rw [comp_appTop_apply, specMap_appTop_apply, isoSpec_hom_appTop_apply]
  rfl

section
variable (m : Type)
noncomputable def affineSpaceOpenIsoSpecMvPolynomial :
    AffineSpace m W'.toScheme ≅ Spec (CommRingCat.of (MvPolynomial m $ X'.sec W')) :=
  (AffineSpace.functor.obj $ op m).mapIso (affineOpenIsoSpec hW) ≪≫
    AffineSpace.SpecIso m (X'.sec W')

theorem affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_X (j : m) :
    (affineSpaceOpenIsoSpecMvPolynomial hW m).hom.appTop.hom
        ((GSpecIso $ CommRingCat.of (MvPolynomial m $ X'.sec W')).inv.hom
          (MvPolynomial.X j)) =
      AffineSpace.coord W'.toScheme j := by
  have key : (m69 m W'.sec).hom.appTop.hom
      ((GSpecIso $ m10 $ MvPolynomial m W'.sec).inv.hom
        (m7 j)) = m9 (Spec W'.sec) j := by simp_all
  show ((m228 m (affineOpenIsoSpec hW).hom) ≫
      (m69 m W'.sec).hom).appTop.hom
      ((GSpecIso $ m10 $ MvPolynomial m W'.sec).inv.hom
        (m7 j)) = m9 W'.toScheme j
  rw [comp_appTop_apply, key, AffineSpace.map_appTop_coord]

theorem affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_C (a : (X'.sec W')) :
    (affineSpaceOpenIsoSpecMvPolynomial hW m).hom.appTop.hom
        ((Scheme.GSpecIso $ CommRingCat.of (MvPolynomial m $ X'.sec W')).inv.hom
          (MvPolynomial.C a)) =
      (AffineSpace m W'.toScheme ↘ W'.toScheme).appTop.hom (W'.topIso.inv.hom a) := by
  let _a3 := MvPolynomial m $ X'.sec W'
  let _a0 := (GSpecIso W'.sec).inv.hom a
  let _a1 := (GSpecIso $ CommRingCat.of _a3).inv.hom $ MvPolynomial.C a
  have h1 : (Spec.map $ ofHom
        (MvPolynomial.C : xSec X' W' →+* _a3)).appTop.hom
        _a0 =
      _a1 :=
    specMap_appTop_apply _ a
  let _a2 := AffineSpace.SpecIso m $ xSec X' W'
  have key : _a2.hom.appTop.hom
      _a1 =
      (AffineSpace m (Spec W'.sec) ↘ Spec W'.sec).appTop.hom
        _a0 := by
    rw [← h1, ← comp_appTop_apply, ← AffineSpace.SpecIso_inv_over, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  show ((AffineSpace.map m (affineOpenIsoSpec hW).hom) ≫
      isoH _a2).appTop.hom
      _a1 =
      (AffineSpace m W'.toScheme ↘ W'.toScheme).appTop.hom (W'.topIso.inv.hom a)
  rw [comp_appTop_apply, key, ← comp_appTop_apply, AffineSpace.map_over, comp_appTop_apply,
    affineOpenIsoSpec_hom_appTop_apply]
end
end

section
variable (hW : IsAffineOpen W) (hV : IsAffineOpen V) (g) [Etale g]
include hW hV g
theorem chartAlgebra_etale :
    letI : Algebra (MvPolynomial n $ X.sec W) $ Y.sec V := chartAlgebra hW g
    m121 (MvPolynomial n W.sec) V.sec := by
  let : Algebra (MvPolynomial n W.sec) V.sec := chartAlgebra hW g
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  have hEt : Etale $ g ≫ isoH (affineSpaceOpenIsoSpecMvPolynomial hW n) := inferInstance
  have h2 := algebraEtale_comp_equiv
    (GSpecIso $ m10 $ MvPolynomial n W.sec).symm.commRingCatIsoToRingEquiv
    (g ≫ isoH (affineSpaceOpenIsoSpecMvPolynomial hW n)).appTop.hom V.topIso.commRingCatIsoToRingEquiv $ (fun _ h => h) _ $ (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp hEt
  refine algebraEtale_congr ?_ h2
  refine ringHom_ext (fun a => ?_) fun j => ?_
  have hC : chartEvalHom hW g (m8 a) = chartCoeffHom g a := by simp [chartEvalHom]
  show V.topIso.hom.hom ((g ≫ isoH (affineSpaceOpenIsoSpecMvPolynomial hW n)).appTop.hom
      ((GSpecIso $ m10 $ MvPolynomial n W.sec).inv.hom
        (m8 a))) = chartEvalHom hW g (m8 a)
  rw [comp_appTop_apply, affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_C, ← comp_appTop_apply, hC]
  rfl
  show V.topIso.hom.hom ((g ≫ isoH (affineSpaceOpenIsoSpecMvPolynomial hW n)).appTop.hom
      ((GSpecIso $ m10 $ MvPolynomial n W.sec).inv.hom
        (m7 j))) = chartEvalHom hW g (m7 j)
  rw [comp_appTop_apply, affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_X]
  simp [chartEvalHom, chartVar]

theorem chartAlgebra_formallyEtale :
    letI : Algebra (MvPolynomial n $ X.sec W) $ Y.sec V := chartAlgebra hW g
    FormallyEtale (MvPolynomial n W.sec) V.sec := by
  let := chartAlgebra hW g
  have := chartAlgebra_etale hW hV g
  infer_instance
end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

variable (k : Type) [CommRing k] (ι S : Type) [CommRing S]

section

variable [Algebra (MvPolynomial ι k) S]

noncomputable def coord (i : ι) : S := algebraMap (MvPolynomial ι k) S $ MvPolynomial.X i

theorem coord_def i :
    coord k ι S i = algebraMap (MvPolynomial ι k) S (MvPolynomial.X i) := rfl

end

section

variable [Algebra (MvPolynomial ι k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]

include ι

theorem exists_basisKaehler :
    ∃ b : Basis ι S $ KaehlerDifferential k S,
      ∀ i, b i = KaehlerDifferential.D k S (coord k ι S i) := by
  refine ⟨(basis S
    (mvPolynomialBasis k ι)).map (isBaseChange_of_formallyEtale k (MvPolynomial ι k) S).equiv, fun i => ?_⟩
  simp [map_apply, basis_apply,
    mvPolynomialBasis_apply, IsBaseChange.equiv_tmul, one_smul,
    map_D]
  rfl

noncomputable def basisKaehler : Basis ι S $ KaehlerDifferential k S :=
  (exists_basisKaehler k ι S).choose

section
variable (i : ι)
@[simp] theorem basisKaehler_apply :
    basisKaehler k ι S i = KaehlerDifferential.D k S (coord k ι S i) :=
  (exists_basisKaehler k ι S).choose_spec i

noncomputable def partialDerivFun (s : S) : S :=
  (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i

noncomputable def partialDerivLinear : S →ₗ[k] S where
  toFun := partialDerivFun k ι S i
  map_add' := by
    intro x y
    let _a0 := basisKaehler k ι S
    show _a0.repr (KaehlerDifferential.D k S $ x + y) i
        = _a0.repr (KaehlerDifferential.D k S x) i
          + _a0.repr (KaehlerDifferential.D k S y) i
    rw [map_add, map_add, Finsupp.add_apply]
  map_smul' := by
    intro c x
    have h1 := smul_def c x
    let _a0 := basisKaehler k ι S
    show _a0.repr (KaehlerDifferential.D k S $ c • x) i
        = c • _a0.repr (KaehlerDifferential.D k S x) i
    rw [h1, leibniz, map_algebraMap, smul_zero, add_zero, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, ← smul_def]

theorem partialLinear_leibniz :
    ∀ a b, partialDerivLinear k ι S i (a * b)
      = a • partialDerivLinear k ι S i b + b • partialDerivLinear k ι S i a := by
  intro a b
  let _a0 := basisKaehler k ι S
  have h2 : _a0.repr (m13 k S $ a * b) i
      = a * _a0.repr (m13 k S b) i
        + b * _a0.repr (m13 k S a) i := by simp_all
  exact h2

noncomputable def partialDeriv : Derivation k S S :=
  mk' (partialDerivLinear k ι S i) $ partialLinear_leibniz k ι S i

theorem partialDeriv_apply (s : S) :
    partialDeriv k ι S i s = (basisKaehler k ι S).repr (KaehlerDifferential.D k S s) i := rfl

theorem partialDeriv_coord_self :
    partialDeriv k ι S i (coord k ι S i) = 1 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S i, repr_self,
    single_eq_same]
end

@[simp] theorem partialDeriv_coord [DecidableEq ι] (i j : ι) :
    partialDeriv k ι S i (coord k ι S j) = if i = j then (1 : S) else 0 := by
  rw [partialDeriv_apply, ← basisKaehler_apply k ι S j, repr_self,
    single_apply]
  exact if_congr eq_comm rfl rfl

theorem partialDeriv_coord_of_ne (i j : ι) (h : i ≠ j) :
    partialDeriv k ι S i (coord k ι S j) = 0 := by
  classical
  rw [partialDeriv_coord k ι S i j, if_neg h]

omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [FormallyEtale (MvPolynomial ι k) S] in
theorem sum_smul_derivation_apply__b28 (c : ι → S) (f : ι → Derivation k S S)
    (s : S) (t : Finset ι) :
    (∑ i ∈ t, c i • f i) s = ∑ i ∈ t, c i * f i s :=by simp_all
theorem span_range_partialDeriv [Finite ι] :
    Submodule.span S (Set.range (partialDeriv k ι S)) = (⊤ : Submodule S (Derivation k S S)) := by
  obtain ⟨hio⟩ := nonempty_fintype ι
  refine mpr_ eq_top_iff' fun D => ?_
  have key : D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by
    ext s
    have h1 : ∑ i : ι, partialDeriv k ι S i s • m13 k S (coord k ι S i)
        = m13 k S s := by
      rw [← sum_repr (basisKaehler k ι S) (m13 k S s)]
      exact sum_congr rfl fun i _ => by rw [basisKaehler_apply, partialDeriv_apply]
    have h2 : D.liftKaehlerDifferential
        (∑ i : ι, partialDeriv k ι S i s • m13 k S (coord k ι S i))
        = D.liftKaehlerDifferential (m13 k S s) := by rw [h1]
    simp only [map_sum, map_smul, liftKaehlerDifferential_comp_D] at h2
    rw [sum_smul_derivation_apply__b28, ← h2]
    exact sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  rw [key]
  exact sum_mem fun i _ =>
    smul_mem _ _ (subset_span (mem_range_self i))

section
variable [Fintype ι]
theorem eq_sum_smul_partialDeriv (D : Derivation k S S) :
    D = ∑ i : ι, D (coord k ι S i) • partialDeriv k ι S i := by
  ext s
  rw [sum_smul_derivation_apply__b28 k ι S (fun i => D $ coord k ι S i) (partialDeriv k ι S) s univ]
  let _a0 := m13 k S s
  have h1 : D s = D.liftKaehlerDifferential _a0 := by
    rw [liftKaehlerDifferential_comp_D]
  rw [h1, ((basisKaehler k ι S).sum_repr _a0).symm, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_smul, basisKaehler_apply, liftKaehlerDifferential_comp_D, smul_eq_mul,
    ← partialDeriv_apply]
  exact mul_comm _ _

section
variable [DecidableEq ι]
theorem exists_basisDerivation :
    ∃ b : Basis ι S $ Derivation k S S, ∀ i : ι, b i = partialDeriv k ι S i := by
  let _a0 := partialDeriv k ι S
  have hli : LinearIndependent S _a0 := by
    rw [linearIndependent_iff']
    intro s g hg j hj
    let _m0 := coord k ι S j
    have h0 : (∑ i ∈ s, g i • partialDeriv k ι S i) _m0 = 0 := by
      rw [hg]
      simp
    rw [sum_smul_derivation_apply__b28 k ι S g _a0
      _m0 s] at h0
    have key : ∑ i ∈ s, g i * partialDeriv k ι S i _m0
        = g j * partialDeriv k ι S j _m0 := by
      refine sum_eq_single j ?_ ?_
      intro i _ hij
      rw [partialDeriv_coord_of_ne k ι S i j hij, mul_zero]
      intro hj'
      exact absurd hj hj'
    rwa [key, partialDeriv_coord_self, mul_one] at h0
  have hsp :=
    (span_range_partialDeriv k ι S).ge
  exact ⟨Module.Basis.mk hli hsp, fun i => mk_apply hli hsp i⟩

noncomputable def basisDerivation :
    Basis ι S $ Derivation k S S :=
  (exists_basisDerivation k ι S).choose

@[simp] theorem basisDerivation_apply (i : ι) :
    basisDerivation k ι S i = partialDeriv k ι S i :=
  (exists_basisDerivation k ι S).choose_spec i
end
end

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace JacobianCriterion

section

variable (k : Type) [CommRing k] (ι S : Type) [CommRing S]
variable [Algebra (MvPolynomial ι k) S]

noncomputable def coord (i : ι) : S := algebraMap (MvPolynomial ι k) S $ MvPolynomial.X i

end

section

variable (k : Type) [CommRing k] (ι S : Type) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]

omit [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S] in
theorem linearIndependent_one_tmul_D_X :
    LinearIndependent S fun i =>
      (1 : S) ⊗ₜ[MvPolynomial ι k]
        (KaehlerDifferential.D k (MvPolynomial ι k) $ MvPolynomial.X i) := by
  let _a0 := basis S $ mvPolynomialBasis k ι
  have hfun : (fun i => 1 ⊗ₜ[MvPolynomial ι k]
        (m13 k (MvPolynomial ι k) $ m7 i)) =
      ⇑_a0 := by
    funext i
    rw [basis_apply, mvPolynomialBasis_apply]
  rw [hfun]
  exact _a0.linearIndependent

section
variable (K : Type) [CommRing K] (σ : Type)
theorem D_mem_span_range_D_X
    f :
    KaehlerDifferential.D K (MvPolynomial σ K) f ∈
      Submodule.span (MvPolynomial σ K)
        (Set.range fun i =>
          KaehlerDifferential.D K (MvPolynomial σ K) $ MvPolynomial.X i) := by
  induction f using induction_on
  rename_i a
  rw [← m185, Derivation.map_algebraMap]
  exact m97 _
  rename_i p q hp hq
  rw [map_add]
  exact m60 _ hp hq
  rename_i p i hp
  rw [leibniz]
  exact m60 _
    (smul_mem _ _ $ subset_span ⟨i, rfl⟩)
    (smul_mem _ _ hp)

theorem span_range_D_X_eq_top :
    Submodule.span (MvPolynomial σ K)
        (Set.range fun i : σ =>
          KaehlerDifferential.D K (MvPolynomial σ K) $ MvPolynomial.X i) = ⊤ := by
  refine mpr_ eq_top_iff ?_
  rw [← span_range_derivation, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact D_mem_span_range_D_X K σ f
end

section
variable (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (M : Type) [AddCommGroup M] [Module R M]
theorem smul_one_tmul (a : A) (m : M) :
    a • ((1 : A) ⊗ₜ[R] m) = a ⊗ₜ[R] m := by
  let _a0 := (1 : A)
  have h2 : a • _a0 = a := by rw [smul_eq_mul, mul_one]
  have h1 : ((a • _a0) ⊗ₜ[R] m : A ⊗[R] M) = a • (_a0 ⊗ₜ[R] m) := by
    rw [smul_tmul']
  rw [h2] at h1
  exact sy_ h1

theorem top_le_span_range_one_tmul
    (ta_ : Type) (g : ta_ → M)
    (hs : Submodule.span R (Set.range g) = ⊤) :
    ⊤ ≤ Submodule.span A (Set.range fun i : ta_ => (1 : A) ⊗ₜ[R] g i) := by
  have key : ∀ m : M, ∀ a : A,
      a ⊗ₜ[R] m ∈ m72 A (m30 fun i : ta_ => 1 ⊗ₜ[R] g i) := by
    intro m
    have hm : m ∈ m72 R (m30 g) := by simp_all
    refine span_induction ?_ ?_ ?_ ?_ hm
    rintro x ⟨i, rfl⟩ a
    rw [← smul_one_tmul R A M a $ g i]
    exact smul_mem _ _ $ subset_span ⟨i, rfl⟩
    intro a
    rw [tmul_zero]
    exact m97 _
    intro x y _ _ hx hy a
    rw [tmul_add]
    exact m60 _ (hx a) $ hy a
    intro r x _ hx a
    have e : a ⊗ₜ[R] (r • x) = (r • a) ⊗ₜ[R] x := by
      rw [smul_tmul]
    rw [e]
    exact hx $ r • a
  intro w _
  refine inductionOn w ?_ ?_
  intro a m
  exact key m a
  intro u v hu hv
  exact m60 _ hu hv
end

omit [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S] in
theorem top_le_span_one_tmul_D_X :
    ⊤ ≤ Submodule.span S (Set.range fun i : ι =>
        (1 : S) ⊗ₜ[MvPolynomial ι k]
          (KaehlerDifferential.D k (MvPolynomial ι k) $ MvPolynomial.X i)) :=
  top_le_span_range_one_tmul (MvPolynomial ι k) S (KaehlerDifferential k $ MvPolynomial ι k) ι
    (fun i => m13 k (MvPolynomial ι k) $ m7 i)
    (span_range_D_X_eq_top k ι)

noncomputable def tensorKaehlerBasis :
    Basis ι S $ S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k) :=
  Module.Basis.mk (linearIndependent_one_tmul_D_X k ι S) $ top_le_span_one_tmul_D_X k ι S

@[simp]
theorem tensorKaehlerBasis_mapBaseChange (i : ι) :
    mapBaseChange k (MvPolynomial ι k) S (tensorKaehlerBasis k ι S i) =
      KaehlerDifferential.D k S (coord k ι S i) := by
  let _a0 := MvPolynomial ι k
  have h : tensorKaehlerBasis k ι S i =
      1 ⊗ₜ[_a0]
        (m13 k _a0 $ m7 i) :=
    mk_apply (linearIndependent_one_tmul_D_X k ι S) (top_le_span_one_tmul_D_X k ι S) i
  have h2 : coord k ι S i = algebraMap _a0 S (m7 i) := rfl
  rw [h, mapBaseChange_tmul, one_smul, map_D, h2]

theorem formallyEtale_of_basis [FormallySmooth k S]
    (b : Basis ι S $ KaehlerDifferential k S)
    (hb : ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i)) :
    FormallyEtale (MvPolynomial ι k) S := by
  let _a1 := MvPolynomial ι k
  let _a2 := tensorKaehlerBasis k ι S
  have hbij : Bijective $ mapBaseChange k _a1 S := by
    have h : (mapBaseChange k _a1 S) =
        ((_a2.equiv b $ refl ι) :
          (S ⊗[_a1] KaehlerDifferential k _a1) →ₗ[S]
            KaehlerDifferential k S) := by
      refine _a2.ext fun i => ?_
      rw [tensorKaehlerBasis_mapBaseChange]
      simp [hb i]
    have hx : ∀ x, mapBaseChange k _a1 S x =
        (_a2.equiv b $ refl ι) x := by simp_all
    constructor
    intro x y hxy
    apply (_a2.equiv b $ refl ι).injective
    rw [← hx, ← hx, hxy]
    intro y
    obtain ⟨x, hxe⟩ := (_a2.equiv b $ refl ι).surjective y
    exact ⟨x, tr_ (hx x) hxe⟩
  have hfu : FormallyUnramified _a1 S := by
    let _a0 := _a1
    have hD : ∀ s, m13 _a0 S s = 0 := by
      intro s
      obtain ⟨y, hy⟩ := an2 hbij $ m13 k S s
      have h2 := (exact_mapBaseChange_map k _a0 S).apply_apply_eq_zero y
      rw [hy, map_D] at h2
      simpa using h2
    have key : ∀ x : KaehlerDifferential _a0 S, x = 0 := by
      intro x
      have hx : x ∈ Submodule.span S
          (Set.range $ KaehlerDifferential.D _a0 S) := by
        rw [span_range_derivation]
        exact mem_top
      induction hx using span_induction with
      | mem y hy =>
          obtain ⟨s, rfl⟩ := hy
          exact hD s
      | zero => rfl
      | add a b _ _ ha hb => rw [ha, hb, add_zero]
      | smul c a _ ha => rw [ha, smul_zero]
    exact Algebra.FormallyUnramified.mk ⟨fun a b => by rw [key a, key b]⟩
  let _a0 := H1Cotangent _a1 S
  have hh1 : Subsingleton _a0 := by
    have key : ∀ z : _a0, z = 0 := by
      intro z
      have hz : Algebra.H1Cotangent.δ k _a1 S z = 0 := by
        have h0 := (Algebra.H1Cotangent.exact_δ_mapBaseChange k _a1
          S).apply_apply_eq_zero z
        refine an1 hbij ?_
        rw [h0, map_zero]
      obtain ⟨w, hw⟩ := mp_ (Algebra.H1Cotangent.exact_map_δ k _a1 S z) hz
      rw [← hw, m111 w 0, map_zero]
    exact ⟨fun x y => by rw [key x, key y]⟩
  constructor
  infer_instance
  infer_instance

end

section

variable (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι]
variable (S : Type) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]

omit [IsScalarTower k (MvPolynomial ι k) S] in
theorem linearIndependent_D_coord_of_isUnit_det (b : Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S $ coord k ι S i)) :
    LinearIndependent S fun i => KaehlerDifferential.D k S $ coord k ι S i :=
  (b.is_basis_iff_det.mpr h).1

omit [IsScalarTower k (MvPolynomial ι k) S] in
theorem top_le_span_D_coord_of_isUnit_det (b : Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S $ coord k ι S i)) :
    ⊤ ≤ Submodule.span S
        (Set.range fun i => KaehlerDifferential.D k S $ coord k ι S i) := by
  exact (b.is_basis_iff_det.mpr h).2.ge

noncomputable def coordBasis (b : Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S $ coord k ι S i)) :
    Basis ι S $ KaehlerDifferential k S :=
  Module.Basis.mk (linearIndependent_D_coord_of_isUnit_det k ι S b h) $ top_le_span_D_coord_of_isUnit_det k ι S b h

omit [IsScalarTower k (MvPolynomial ι k) S] in
@[simp]
theorem coordBasis_apply (b : Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S $ coord k ι S i)) (i : ι) :
    coordBasis k ι S b h i = KaehlerDifferential.D k S (coord k ι S i) :=
  mk_apply (linearIndependent_D_coord_of_isUnit_det k ι S b h) (top_le_span_D_coord_of_isUnit_det k ι S b h) i

theorem formallyEtale_of_isUnit_det [FormallySmooth k S]
    (b : Basis ι S $ KaehlerDifferential k S)
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S $ coord k ι S i)) :
    FormallyEtale (MvPolynomial ι k) S :=
  formallyEtale_of_basis k ι S (coordBasis k ι S b h) $ coordBasis_apply k ι S b h

end

section

variable (k : Type) [CommRing k] (ι S : Type) [CommRing S] [Algebra k S]
variable (S' : Type) [CommRing S'] [Algebra k S'] [Algebra S S'] [IsScalarTower k S S']
variable [FormallyEtale S S']

section
variable (b : Basis ι S (KaehlerDifferential k S))
theorem linearIndependent_kaehlerMap_basis :
    LinearIndependent S' fun i => KaehlerDifferential.map k k S S' $ b i := by
  have hbc := isBaseChange_of_formallyEtale k S S'
  let _a0 := (basis S' b).map hbc.equiv
  have hfun : (fun i => m132 k k S S' $ b i) =
      ⇑_a0 := by
    funext i
    rw [map_apply, basis_apply, hbc.equiv_tmul, one_smul]
  rw [hfun]
  exact _a0.linearIndependent

theorem top_le_span_kaehlerMap_basis :
    ⊤ ≤ Submodule.span S'
        (Set.range fun i : ι => KaehlerDifferential.map k k S S' $ b i) := by
  have hsub : Subsingleton $ KaehlerDifferential S S' :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  let _a0 := mapBaseChange k S S'
  have hsurj : Surjective _a0 := by
    intro x
    obtain ⟨y, hy⟩ := mp_ ((exact_mapBaseChange_map k S S') x) $ m111 _ _
    exact ⟨y, hy⟩
  have hle : m72 S' (m30 fun i => 1 ⊗ₜ[S] b i) ≤
      Submodule.comap _a0
        (m72 S'
          (m30 fun i => m132 k k S S' $ b i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : mapBaseChange k S S' (1 ⊗ₜ[S] b i) ∈
        m72 S'
          (m30 fun j => m132 k k S S' $ b j) := by
      rw [mapBaseChange_tmul, one_smul]
      exact subset_span ⟨i, rfl⟩
    exact h1
  intro x _
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle $ (top_le_span_range_one_tmul S S' (KaehlerDifferential k S) ι (⇑b) b.span_eq) mem_top

noncomputable def inducedBasis :
    Basis ι S' $ KaehlerDifferential k S' :=
  Module.Basis.mk (linearIndependent_kaehlerMap_basis k ι S S' b) $ top_le_span_kaehlerMap_basis k ι S S' b

@[simp]
theorem inducedBasis_apply (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.map k k S S' (b i) :=
  mk_apply (linearIndependent_kaehlerMap_basis k ι S S' b)
    (top_le_span_kaehlerMap_basis k ι S S' b) i

theorem inducedBasis_apply_D (x : ι → S)
    (hx : ∀ i : ι, b i = KaehlerDifferential.D k S (x i)) (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.D k S' (algebraMap S S' $ x i) :=by simp_all
end

end

end JacobianCriterion
end FunctorialResolution.EmbeddedResolution
end
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {ι : Type}
theorem exists_minimal_spanning_finset [DecidableEq ι] (C : Set V) (bb : ι → V) :
    ∀ (n : ℕ) (J : Finset ι), J.card ≤ n →
      Submodule.span K (C ∪ bb '' (↑J : Set ι)) = ⊤ →
      ∃ J' : Finset ι, Submodule.span K (C ∪ bb '' (↑J' : Set ι)) = ⊤ ∧
        ∀ j ∈ J', Submodule.span K (C ∪ bb '' (↑(J'.erase j) : Set ι)) ≠ ⊤ := by
  intro n
  induction n with
  | zero =>
      intro J hcard hJ
      refine ⟨J, hJ, fun j hj => ?_⟩
      have hpos := mpr_ card_pos ⟨j, hj⟩
      exact absurd hcard $ by omega
  | succ n ih =>
      intro J hcard hJ
      by_cases hs : ∃ j ∈ J, m72 K (C ∪ bb '' (↑(J.erase j) : Set ι)) = ⊤
      obtain ⟨j, hjJ, hPj⟩ := hs
      refine ih (J.erase j) ?_ hPj
      have hce := card_erase_of_mem hjJ
      omega
      push Not at hs
      exact ⟨J, hJ, hs⟩

theorem span_union_image_erase_eq_top [DecidableEq ι] {C : Set V} {bb : ι → V} {J : Finset ι} {j0 : ι}
    (hJtop : Submodule.span K (C ∪ bb '' (↑J : Set ι)) = ⊤)
    (hb : bb j0 ∈ Submodule.span K (C ∪ bb '' (↑(J.erase j0) : Set ι))) :
    Submodule.span K (C ∪ bb '' (↑(J.erase j0) : Set ι)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hJtop, Submodule.span_le]
  rintro v (hv | ⟨j, hj, rfl⟩)
  exact subset_span $ mem_union_left _ hv
  by_cases hjj : j = j0
  rwa [hjj]
  exact subset_span $ mem_union_right _
    ⟨j, Finset.mem_coe.mpr $ mpr_ mem_erase ⟨hjj, Finset.mem_coe.mp hj⟩, rfl⟩

theorem exists_basis_sum_of_linearIndependent [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (h : ℕ)
    (c : Fin h → V) (hc : LinearIndependent K c) :
    ∃ (J : Finset ι) (B : Basis (Fin h ⊕ {j : ι // j ∈ J}) K V),
      (∀ i : Fin h, B (Sum.inl i) = c i) ∧
        ∀ j : {j : ι // j ∈ J}, B (Sum.inr j) = b (j : ι) := by
  classical
  have hPuniv : m72 K
      (m30 c ∪ (⇑b) '' (↑(univ : Finset ι) : Set ι)) = ⊤ := by simp_all
  obtain ⟨J, hJtop, hJmin⟩ :=
    exists_minimal_spanning_finset (K := K) (m30 c) (⇑b)
      Finset.univ.card univ le_rfl hPuniv
  have hrange : m30 (elim c fun j : {j : ι // j ∈ J} => b j)
      = m30 c ∪ imS (⇑b) (↑J) := by
    ext v
    constructor
    simp_all
    rintro (⟨i, rfl⟩ | ⟨j, hj, rfl⟩)
    exact ⟨m44 i, rfl⟩
    exact ⟨m50 ⟨j, Finset.mem_coe.mp hj⟩, rfl⟩
  have hli : LinearIndependent K $ elim c fun j : {j : ι // j ∈ J} => b j := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let _a1 := (∑ i : Fin h, g (m44 i) • c i)
    have hg' : _a1
        + (∑ j : {j : ι // j ∈ J}, g (m50 j) • b j) = 0 := by
      rwa [sum_sum_type] at hg
    have hz : ∀ j : {j : ι // j ∈ J}, g (m50 j) = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨j0, hj0⟩ := hcon
      rw [(add_sum_erase univ (fun j : {j : ι // j ∈ J} => g (m50 j) • b j) $ mem_univ j0).symm] at hg'
      let _a0 := m72 K $ m30 c ∪ (⇑b) '' (↑(J.erase j0) : Set ι)
      have hA : _a1
          ∈ _a0 := by
        exact Submodule.sum_mem _ fun i _ => smul_mem _ _ $ subset_span $ mem_union_left _ ⟨i, rfl⟩
      have hB : (∑ j ∈ Finset.univ.erase j0, g (m50 j) • b j)
          ∈ _a0 := by
        refine Submodule.sum_mem _ fun j hj => smul_mem _ _ ?_
        have hne := fun hh => (ne_of_mem_erase hj) $ m26 hh
        exact subset_span $ mem_union_right _
          ⟨j, Finset.mem_coe.mpr $ mpr_ mem_erase ⟨hne, j.2⟩, rfl⟩
      let _a2 := b j0
      let _a3 := g $ m50 j0
      have hxmem : _a3 • _a2
          ∈ _a0 := by
        have hid : _a3 • _a2
            = _a1
                + (_a3 • _a2
                  + ∑ j ∈ Finset.univ.erase j0, g (m50 j) • b j)
              - _a1
              - ∑ j ∈ Finset.univ.erase j0, g (m50 j) • b j := by
          abel
        rw [hid, hg']
        exact m162 _ (m162 _ (m97 _) hA) hB
      refine hJmin j0 j0.2 $ span_union_image_erase_eq_top hJtop ?_
      have hsm := smul_mem _ _a3⁻¹ hxmem
      rwa [smul_smul, inv_mul_cancel₀ hj0, one_smul] at hsm
    intro x
    cases x with
    | inl i =>
        have hzero : (∑ j : {j : ι // j ∈ J}, g (m50 j) • b j) = 0 :=
          sum_eq_zero fun j _ => by rw [hz j, zero_smul]
        rw [hzero, add_zero] at hg'
        exact linearIndependent_iff.mp hc (fun i => g $ m44 i) hg' i
    | inr j => exact hz j
  have hsp : (⊤)
      ≤ m72 K (m30 $ elim c fun j : {j : ι // j ∈ J} => b j) := by simp_all
  refine ⟨J, Module.Basis.mk hli hsp, fun i => ?_, fun j => ?_⟩
  simp_all
  simp_all

end

section

variable (k : Type) [CommRing k] (ι S : Type) [CommRing S] (S' : Type) [CommRing S']
  [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S'] [Algebra S S']
  [IsScalarTower (MvPolynomial ι k) S S']

theorem algebraMap_coord (i : ι) :
    algebraMap S S' (coord k ι S i) = coord k ι S' i := by
  rw [coord_def, coord_def]
  exact sy_ $ algebraMap_apply (MvPolynomial ι k) S S' $ m7 i

end

section

variable (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι]
  (S : Type) [CommRing S] (S' : Type) [CommRing S']
  [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
  [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
  [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
  [FormallyEtale (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S']

theorem repr_map_basisKaehler
    (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (S : Type) [CommRing S] (S' : Type) [CommRing S']
    [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
    [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
    [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
    [FormallyEtale (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S']
    (om_ : KaehlerDifferential k S) (i : ι) :
    (basisKaehler k ι S').repr (KaehlerDifferential.map k k S S' om_) i
      = algebraMap S S' ((basisKaehler k ι S).repr om_ i) := by
  have hb : ∀ j, m132 k k S S' (basisKaehler k ι S j)
      = basisKaehler k ι S' j := by
    intro j
    simp only [basisKaehler_apply, map_D,
      algebraMap_coord]
  have key : m132 k k S S' om_
      = ∑ j : ι, algebraMap S S' ((basisKaehler k ι S).repr om_ j) • basisKaehler k ι S' j := by
    conv_lhs => rw [((basisKaehler k ι S).sum_repr om_).symm]
    rw [map_sum]
    refine sum_congr rfl ?_
    intro j _
    rw [map_smul, hb j]
    exact algebra_compatible_smul S' ((basisKaehler k ι S).repr om_ j) $ basisKaehler k ι S' j
  rw [key]
  simp only [repr_sum_self]

theorem algebraMap_det_basisKaehler (v : ι → S) :
    algebraMap S S' ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S $ v i) =
      (basisKaehler k ι S').det
        fun i : ι => KaehlerDifferential.D k S' $ algebraMap S S' $ v i := by
  have hmat : (algebraMap S S').mapMatrix
        ((basisKaehler k ι S).toMatrix fun i => m13 k S $ v i)
      = (basisKaehler k ι S').toMatrix
        fun i => m13 k S' $ algebraMap S S' $ v i := by
    ext i j
    have h0 : m13 k S' (algebraMap S S' $ v j)
        = m132 k k S S' (m13 k S $ v j) := by
      simp only [map_D]
    simp only [mapMatrix_apply, Matrix.map_apply, toMatrix_apply, h0]
    exact sy_ $ repr_map_basisKaehler k ι S S' (m13 k S $ v j) i
  rw [det_apply, det_apply, map_det, hmat]

end

section

theorem formallyEtale_of_isUnit_det_of_eq_coord (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    [DecidableEq ι] (T : Type) [CommRing T] [Algebra k T] [Algebra (MvPolynomial ι k) T]
    [IsScalarTower k (MvPolynomial ι k) T] [FormallySmooth k T]
    (e : Basis ι T $ KaehlerDifferential k T) (w : ι → T)
    (hw : ∀ i : ι, w i = JacobianCriterion.coord k ι T i)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k T $ w i)) :
    FormallyEtale (MvPolynomial ι k) T := by
  have hfun : (fun i => m13 k T $ JacobianCriterion.coord k ι T i) =
      fun i => m13 k T $ w i := by simp_all
  have h := hdet
  rw [← hfun] at h
  exact JacobianCriterion.formallyEtale_of_isUnit_det k ι T e h

theorem formallyEtale_aeval_of_isUnit_det {k : Type} [CommRing k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {T : Type} [CommRing T] [Algebra k T] [FormallySmooth k T]
    (e : Basis ι T $ KaehlerDifferential k T) (w : ι → T)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k T $ w i)) :
    letI : Algebra (MvPolynomial ι k) T :=
      (m165 w).toRingHom.toAlgebra
    FormallyEtale (MvPolynomial ι k) T := by
  let instAeval :=
    (m165 w : MvPolynomial ι k →ₐ[k] T).toRingHom.toAlgebra
  have hmap : ∀ p,
      algebraMap (MvPolynomial ι k) T p = m165 w p := fun _ => rfl
  have instTower : IsScalarTower k (MvPolynomial ι k) T :=
    of_algebraMap_eq fun x => by
      rw [hmap, m185, aeval_C]
  show FormallyEtale (MvPolynomial ι k) T
  refine formallyEtale_of_isUnit_det_of_eq_coord k ι T e w (fun i => ?_) hdet
  show w i = algebraMap (MvPolynomial ι k) T (m7 i)
  rw [hmap, aeval_X]

end

section

theorem span_range_eq_span_range_of_eq_mul_isUnit {A : Type} [CommRing A] {n : ℕ}
    (y z c : Fin n → A) (hc : ∀ i, IsUnit $ c i) (hz : ∀ i, z i = y i * c i) :
    Ideal.span (Set.range z) = Ideal.span (Set.range y) := by
  apply le_antisymm
  rw [span_le]
  rintro w ⟨i, rfl⟩
  rw [mem_coe, hz i]
  exact mul_mem_right _ _ $ m100 ⟨i, rfl⟩
  rw [span_le]
  rintro w ⟨i, rfl⟩
  obtain ⟨v, hv⟩ := hc i
  have hy : y i = z i * (↑v⁻¹) := by
    rw [hz i, ← hv, mul_assoc, Units.mul_inv, mul_one]
  rw [mem_coe, hy]
  exact mul_mem_right _ _ $ m100 ⟨i, rfl⟩

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section

section
variable (k : Type) [CommRing k] (A : Type) [CommRing A] [Algebra k A] [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)] [FormallySmooth k (IsLocalRing.ResidueField A)]
theorem mem_maximalIdeal_sq_of_tmul_D_eq_zero
    (x : A) (hx : x ∈ IsLocalRing.maximalIdeal A)
    (h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x = 0) :
    x ∈ IsLocalRing.maximalIdeal A ^ 2 := by
  classical
  obtain ⟨w, h1, h2, h3, h4, h5⟩ : ∃ w : A → A, (∀ a : A, a - w a ∈ m16 A) ∧ (∀ a b : A, w a + w b - w (a + b) ∈ m16 A ^ 2) ∧ (∀ (c : k) (a : A), c • w a - w (c • a) ∈ m16 A ^ 2) ∧ (∀ a b : A, w a * w b - w (a * b) ∈ m16 A ^ 2) ∧ (∀ a : A, a ∈ m16 A → w a ∈ m16 A ^ 2) := by
    let _c0 := A ⧸ m16 A ^ 2
    classical
    let _a1 := toAlgHom k A $ m14 A
    have hsq : ∀ a ∈ m16 A ^ 2,
        _a1 a = 0 := by
      intro a ha
      show algebraMap A (m14 A) a = 0
      rw [algebraMap_eq, residue_eq_zero_iff]
      exact pow_le_self (by norm_num) ha
    obtain ⟨rh_, hrhmk⟩ : ∃ rh_ : _c0 →ₐ[k]
        m14 A,
        ∀ a, rh_ (m5 (m16 A ^ 2) a)
          = residue A a := by
      refine ⟨Ideal.Quotient.liftₐ (m16 A ^ 2)
        _a1 hsq, fun a => ?_⟩
      show algebraMap A (m14 A) a = residue A a
      rw [algebraMap_eq]
    have hrhsurj : Surjective rh_ := by
      intro c
      obtain ⟨a, ha⟩ := residue_surjective (R := A) c
      exact ⟨m5 _ a, by rw [hrhmk a]; exact ha⟩
    let _s0 := (rh_ : _c0 →+* m14 A)
    have hker2 : m41 _s0 ^ 2 = ⊥ := by
      have hexp : m41 _s0 ^ 2
          = m41 _s0
            * m41 _s0 := pow_two _
      rw [hexp]
      refine le_antisymm ?_ bot_le
      rw [mul_le]
      intro u hu v hv
      have hu' := RingHom.mem_ker.mp hv
      obtain ⟨a, rfl⟩ := mk_surjective u
      obtain ⟨b, rfl⟩ := mk_surjective v
      have ha : a ∈ m16 A := by
        rwa [← residue_eq_zero_iff, ← hrhmk a]
      have hb : b ∈ m16 A := by
        rwa [← residue_eq_zero_iff, ← hrhmk b]
      refine mpr_ (Submodule.mem_bot _) ?_
      rw [← map_mul, eq_zero_iff_mem, pow_two]
      exact mul_mem_mul ha hb
    obtain ⟨σ, hsg_⟩ : ∃ σ : m14 A →ₐ[k]
        _c0, ∀ c, rh_ (σ c) = c := by
      refine ⟨liftOfSurjective
        (AlgHom.id k $ m14 A) rh_ hrhsurj ⟨2, hker2⟩, fun c => ?_⟩
      have h := comp_liftOfSurjective
        (AlgHom.id k $ m14 A) rh_ hrhsurj ⟨2, hker2⟩
      have h2 := congr_fun h c
      simpa using h2
    obtain ⟨w, hw⟩ : ∃ w : A → A, ∀ a : A,
        m5 (m16 A ^ 2) (w a)
          = σ (residue A a) := by
      exact ⟨fun a => surjInv mk_surjective
        (σ $ residue A a), fun a => surjInv_eq mk_surjective _⟩
    refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
    intro a
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hrhmk $ w a, hw a,
      hsg_ $ residue A a]
    intro a b
    rw [← eq_zero_iff_mem, map_sub, map_add, hw a, hw b, hw $ a + b, map_add,
      map_add, sub_self]
    intro c a
    have hres : residue A (c • a) = c • residue A a := by
      rw [smul_def, map_mul, smul_def,
        ← algebraMap_eq,
        ← algebraMap_apply k A $ m14 A]
    have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) (c • w a)
        = c • Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ 2) (w a) := by
      rw [smul_def, map_mul, smul_def, ← Ideal.Quotient.algebraMap_eq,
        ← algebraMap_apply k A _c0]
    rw [← eq_zero_iff_mem, map_sub, hw $ c • a, hmk, hres, map_smul, hw a,
      sub_self]
    intro a b
    rw [← eq_zero_iff_mem, map_sub, map_mul, hw a, hw b, hw $ a * b, map_mul,
      map_mul, sub_self]
    intro a ha
    have hres := ha
    rw [← residue_eq_zero_iff] at hres
    rw [← eq_zero_iff_mem, hw a, hres, map_zero]
  have hco : ∀ a b (ha : a ∈ m16 A)
      (hb : b ∈ m16 A),
      a - b ∈ m16 A ^ 2 →
      toCotangent (m16 A) ⟨a, ha⟩
        = toCotangent (m16 A) ⟨b, hb⟩ := by
    intro a b ha hb hab
    exact mpr_ (toCotangent_eq _) hab
  have hadd : ∀ a b,
      toCotangent (m16 A) ⟨a + b - w (a + b), h1 $ a + b⟩
        = toCotangent (m16 A) ⟨a - w a, h1 a⟩
          + toCotangent (m16 A) ⟨b - w b, h1 b⟩ := by
    intro a b
    rw [← map_add]
    refine hco _ _ _ _ ?_
    let _a4 := (a - w a) + (b - w b)
    show a + b - w (a + b) - _a4 ∈ m16 A ^ 2
    have heq : a + b - w (a + b) - _a4 = w a + w b - w (a + b) := by ring
    rw [heq]
    exact h2 a b
  have hsmul : ∀ c (a : A),
      toCotangent (m16 A) ⟨c • a - w (c • a), h1 $ c • a⟩
        = (m99 k) c •
          toCotangent (m16 A) ⟨a - w a, h1 a⟩ := by
    intro c a
    show toCotangent (m16 A) ⟨c • a - w (c • a), h1 $ c • a⟩
      = c • toCotangent (m16 A) ⟨a - w a, h1 a⟩
    rw [← algebraMap_smul A c
      (toCotangent (m16 A) ⟨a - w a, h1 a⟩), ← map_smul]
    refine hco _ _ _ _ ?_
    let _a6 := algebraMap k A c
    show c • a - w (c • a) - _a6 • (a - w a)
      ∈ m16 A ^ 2
    have heq : c • a - w (c • a) - _a6 • (a - w a)
        = c • w a - w (c • a) := by
      rw [smul_def c a, smul_def c $ w a, smul_eq_mul]
      ring
    rw [heq]
    exact h3 c a
  have hleib : ∀ a b,
      toCotangent (m16 A) ⟨a * b - w (a * b), h1 $ a * b⟩
        = a • toCotangent (m16 A) ⟨b - w b, h1 b⟩
          + b • toCotangent (m16 A) ⟨a - w a, h1 a⟩ := by
    intro a b
    rw [← map_smul, ← map_smul, ← map_add]
    refine hco _ _ _ _ ?_
    show a * b - w (a * b) - (a • (b - w b) + b • (a - w a))
      ∈ m16 A ^ 2
    have heq : a * b - w (a * b) - (a • (b - w b) + b • (a - w a))
        = -((a - w a) * (b - w b)) + (w a * w b - w (a * b)) := by
      simp [smul_eq_mul]
      ring
    rw [heq]
    refine m60 _ (neg_mem ?_) $ h4 a b
    rw [pow_two]
    exact mul_mem_mul (h1 a) $ h1 b
  obtain ⟨Dder, hDderapp⟩ : ∃ D : Derivation k A (m16 A).Cotangent,
      ∀ a, D a = toCotangent (m16 A) ⟨a - w a, h1 a⟩ :=
    ⟨mk'
      { toFun := fun a => toCotangent (m16 A) ⟨a - w a, h1 a⟩
        map_add' := hadd
        map_smul' := hsmul } hleib, fun a => rfl⟩
  have hDx : Dder x = toCotangent (m16 A) ⟨x, hx⟩ := by
    rw [hDderapp x]
    refine hco _ _ _ _ ?_
    show x - w x - x ∈ m16 A ^ 2
    have heq : x - w x - x = -(w x) := by ring
    rw [heq]
    exact neg_mem $ h5 x hx
  have hlin := congrArg (fun z => (Dder.liftKaehlerDifferential.liftBaseChange
    (m14 A)) z) h0
  have hDx0 : Dder x = 0 := by
    simpa [liftBaseChange_tmul, liftKaehlerDifferential_comp_D] using hlin
  have hz := hDx0
  rw [hDx] at hz
  exact mp_ (toCotangent_eq_zero _ ⟨x, hx⟩) hz
end

theorem exists_fun_sum_smul_eq_of_mem_span {K M : Type} [CommRing K] [AddCommGroup M]
    [Module K M] {n : ℕ} (v : Fin n → M) {x : M}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ c : Fin n → K, ∑ i, c i • v i = x := by
  classical
  let P : Submodule K M :=
    { carrier := {y : M | ∃ c : Fin n → K, ∑ i, c i • v i = y}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        intro a b ha hb
        obtain ⟨ca, hca⟩ := ha
        obtain ⟨cb, hcb⟩ := hb
        refine ⟨ca + cb, ?_⟩
        rw [← hca, ← hcb, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, add_smul]
      smul_mem' := by
        intro r a ha
        obtain ⟨ca, hca⟩ := ha
        refine ⟨r • ca, ?_⟩
        rw [← hca, Finset.smul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_assoc] }
  have hsub : m30 v ⊆ P := by
    rintro _ ⟨i, rfl⟩
    refine ⟨single i 1, ?_⟩
    rw [sum_eq_single_of_mem i $ mem_univ i]
    simp
    simp_all
  exact (Submodule.span_le.mpr hsub) hx

private theorem exists_local_parameters (k : Type) [CommRing k] (A : Type) [CommRing A]
    [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k $ IsLocalRing.ResidueField A]
    [IsScalarTower k A $ IsLocalRing.ResidueField A]
    [FormallySmooth k $ IsLocalRing.ResidueField A] :
    ∃ h y,
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) := by
  let _a0 := (1 : IsLocalRing.ResidueField A)
  classical
  obtain ⟨sF, hsF0⟩ : (IsLocalRing.maximalIdeal A).FG := noetherian _
  have hsF := hsF0
  obtain ⟨b, hbsub, hbspan, hbind⟩ :=
    exists_linearIndependent (K := IsLocalRing.ResidueField A)
      (t := (fun a => _a0 ⊗ₜ[A]
        KaehlerDifferential.D k A a) '' (↑sF : Set A))
  let instFintypeB := (subset (image _ sF.finite_toSet) hbsub).fintype
  choose pre hpre1 hpre2 using fun x : b => hbsub x.2
  obtain ⟨y, hy⟩ : ∃ y : Fin (card b) → A,
      ∀ i, y i = pre ((equivFin b).symm i) := ⟨_, fun _ => rfl⟩
  have hfun : (fun i : Fin (card b) => _a0 ⊗ₜ[A]
      KaehlerDifferential.D k A (y i))
      = fun i : Fin (card b) =>
        (((equivFin b).symm i : b) : IsLocalRing.ResidueField A ⊗[A]
          KaehlerDifferential k A) := by simp_all
  have hind : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : Fin (card b) => _a0 ⊗ₜ[A]
        KaehlerDifferential.D k A (y i)) := by
    rw [hfun]
    exact hbind.comp _ (equivFin b).symm.injective
  have hrange : Set.range (fun i : Fin (card b) =>
      _a0 ⊗ₜ[A] KaehlerDifferential.D k A (y i)) = b := by
    rw [hfun]
    ext v
    constructor
    rintro ⟨i, rfl⟩
    exact ((equivFin b).symm i).2
    intro hv
    exact ⟨(equivFin b) ⟨v, hv⟩, by simp⟩
  have hymem : ∀ i, y i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hsF, hy i]
    exact subset_span $ hpre1 _
  refine ⟨card b, y, ?_, hind⟩
  refine le_antisymm ?_ ?_
  rw [span_le]
  rintro _ ⟨i, rfl⟩
  exact hymem i
  have hkey : ∀ a ∈ (↑sF : Set A),
      a ∈ Ideal.span (Set.range y) ⊔ IsLocalRing.maximalIdeal A ^ 2 := by
    intro a ha
    have hav : _a0 ⊗ₜ[A] KaehlerDifferential.D k A a
        ∈ Submodule.span (IsLocalRing.ResidueField A)
          (Set.range fun i : Fin (card b) =>
            _a0 ⊗ₜ[A]
              KaehlerDifferential.D k A (y i)) := by
      rw [hrange, hbspan]
      exact subset_span ⟨a, ha, rfl⟩
    obtain ⟨c, hc0⟩ := exists_fun_sum_smul_eq_of_mem_span
      (fun i : Fin (card b) => _a0 ⊗ₜ[A]
        KaehlerDifferential.D k A (y i)) hav
    obtain ⟨c', hc'⟩ : ∃ c' : Fin (card b) → A,
        ∀ i, residue A (c' i) = c i := by
      choose c' hc' using fun i => mk_surjective $ c i
      exact ⟨c', hc'⟩
    have hsum : _a0 ⊗ₜ[A]
        KaehlerDifferential.D k A (∑ i, c' i * y i)
        = ∑ i, c i • (_a0 ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) := by
      rw [map_sum, tmul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_comm (c' i) $ y i,
        KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal k A (y i) (c' i) $ hymem i,
        hc' i]
    have hx0 : _a0 ⊗ₜ[A]
        KaehlerDifferential.D k A (a - ∑ i, c' i * y i) = 0 := by
      rw [map_sub, tmul_sub, hsum, hc0, sub_self]
    have hxm : a - ∑ i, c' i * y i ∈ IsLocalRing.maximalIdeal A := by
      refine Submodule.sub_mem _ ?_
        (Submodule.sum_mem _ fun i _ => mul_mem_left _ _ $ hymem i)
      rw [← hsF]
      exact subset_span ha
    have hrewrite : a = (a - ∑ i, c' i * y i) + ∑ i, c' i * y i := by ring
    rw [hrewrite]
    exact Submodule.add_mem _ (mem_sup_right $ mem_maximalIdeal_sq_of_tmul_D_eq_zero k A _ hxm hx0) $ mem_sup_left $ Ideal.sum_mem _ fun i _ => mul_mem_left _ _ $ subset_span ⟨i, rfl⟩
  have hsmul : (IsLocalRing.maximalIdeal A • IsLocalRing.maximalIdeal A : Ideal A)
      = IsLocalRing.maximalIdeal A ^ 2 := by
    rw [smul_eq_mul, pow_two]
  have hstep : Ideal.span (↑sF : Set A) ≤ Ideal.span (Set.range y)
      ⊔ IsLocalRing.maximalIdeal A • IsLocalRing.maximalIdeal A := by
    rw [span_le]
    intro a ha
    rw [mem_coe, hsmul]
    exact hkey a ha
  rw [hsF] at hstep
  refine le_of_le_smul_of_le_jacobson_bot (noetherian _)
    (jacobson_eq_maximalIdeal (⊥ : Ideal A) ?_).ge hstep
  simp_all

theorem residue_det_ne_zero_of_basis_tmul {A : Type} [CommRing A] [IsLocalRing A]
    {M : Type} [AddCommGroup M] [Module A M] {ι : Type} [Fintype ι] [DecidableEq ι]
    (bA : Basis ι A M) (G : ι → M)
    (B' : Basis ι (IsLocalRing.ResidueField A) $ IsLocalRing.ResidueField A ⊗[A] M)
    (hB' : ∀ i, B' i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] G i) :
    residue A (bA.det G) ≠ 0 := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Basis ι (m14 A)
      (m14 A ⊗[A] M),
      ∀ i, bk i = (1 : m14 A) ⊗ₜ[A] bA i :=
    ⟨basis (m14 A) bA, fun i => by simp⟩
  have hkey : ∀ (c : A) (m : M), (1 : m14 A) ⊗ₜ[A] (c • m)
      = residue A c • ((1 : m14 A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : m14 A) ⊗ₜ[A] (c • m)
        = (c • (1 : m14 A)) ⊗ₜ[A] m := sy_ $ smul_tmul c 1 m
    have hA2 : c • (1 : m14 A) = residue A c := by
      rw [smul_def, mul_one, algebraMap_eq]
    have hA3 : residue A c • ((1 : m14 A) ⊗ₜ[A] m)
        = (residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hmat : ∀ i j : ι, bk.repr (B' j) i = residue A (bA.toMatrix G i j) := by
    intro i j
    have hGj : B' j = ∑ l : ι, residue A (bA.repr (G j) l) • bk l := by
      rw [hB' j]
      conv_lhs => rw [← bA.sum_repr $ G j]
      rw [tmul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [hkey, hbk l]
    rw [hGj, toMatrix_apply]
    simp only [repr_sum_self]
  have hdet : bk.det (⇑B') = residue A (bA.det G) := by
    rw [det_apply, det_apply, map_det]
    congr 1
    ext i j
    simp only [toMatrix_apply]
    exact hmat i j
  rw [← hdet]
  exact (bk.isUnit_det B').ne_zero

theorem exists_adapted_parameters (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (S : Type) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]
    (q : Ideal S) [q.IsPrime] (A : Type) [CommRing A] [Algebra S A] [Algebra k A]
    [IsScalarTower k S A] [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k $ IsLocalRing.ResidueField A] [IsScalarTower k A $ IsLocalRing.ResidueField A]
    [FormallySmooth k $ IsLocalRing.ResidueField A] :
    ∃ (g : S) (w : ι → S) (J : Finset ι),
      g ∉ q ∧
      (∀ j ∈ J, w j ∈ q) ∧
      Ideal.map (algebraMap S A) (Ideal.span $ w '' (↑J : Set ι)) =
        IsLocalRing.maximalIdeal A ∧
      (∀ j ∉ J, ∃ i : ι, w j = coord k ι S i) ∧
      g = (basisKaehler k ι S).det (fun i : ι => KaehlerDifferential.D k S $ w i) ∧
      IsUnit (algebraMap S (Away g)
        ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S $ w i)) := by
  let _a3 := basisKaehler k ι S
  classical
  have instFEloc : FormallyEtale S A :=
    of_isLocalization (M := q.primeCompl)
  let _s0 := MvPolynomial ι k
  let _a6 := algebraMap S A
  let instPA :=
    (_a6.comp $ algebraMap _s0 S).toAlgebra
  have instT1 : IsScalarTower _s0 S A :=
    of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k _s0 A :=
    of_algebraMap_eq fun x => by
      rw [algebraMap_apply k S A x,
        algebraMap_apply k _s0 S x]
      rfl
  have instFEPA :=
    comp _s0 S A
  obtain ⟨h, y, hyspan, hyind⟩ := exists_local_parameters k A
  obtain ⟨s, hsq, hsspan, hsind⟩ : ∃ s : Fin h → S, (∀ i : Fin h, s i ∈ q) ∧ Ideal.span (Set.range fun i : Fin h => _a6 $ s i) = IsLocalRing.maximalIdeal A ∧ LinearIndependent (IsLocalRing.ResidueField A) fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (algebraMap S A $ s i) := by
    classical
    choose p hp using fun i : Fin h =>
      surj (M := q.primeCompl) (S := A) $ y i
    obtain ⟨s, c, hcu, hmul⟩ : ∃ s c,
        (∀ i, IsUnit $ c i) ∧ ∀ i, algebraMap S A (s i) = y i * c i :=
      ⟨fun i => (p i).1, fun i => algebraMap S A ((p i).2 : S),
        fun i => map_units (M := q.primeCompl) (S := A) $ (p i).2,
        fun i => sy_ $ hp i⟩
    have hymem : ∀ i : Fin h, y i ∈ IsLocalRing.maximalIdeal A := by
      intro i
      rw [← hyspan]
      exact subset_span ⟨i, rfl⟩
    refine ⟨s, ?_, ?_, ?_⟩
    intro i
    by_contra hni
    have hunit :=
      map_units (M := q.primeCompl) (S := A) ⟨s i, hni⟩
    refine mp_ mem_nonunits_iff (mp_ (mem_maximalIdeal _) ?_) hunit
    simp_all
    exact Eq.trans (span_range_eq_span_range_of_eq_mul_isUnit y (fun i : Fin h => _a6 $ s i) c hcu hmul) hyspan
    have hne := fun i =>
      ((hcu i).map $ residue A).ne_zero
    let _a0 := (1 : IsLocalRing.ResidueField A)
    have hfun : (fun i : Fin h => _a0 ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A $ s i)) =
        fun i : Fin h => residue A (c i) •
          (_a0 ⊗ₜ[A] KaehlerDifferential.D k A (y i)) := by
      funext i
      rw [hmul i]
      exact KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal k A (y i) (c i) $ hymem i
    have hsmul : ((fun i : Fin h => mk0 (residue A $ c i) $ hne i) •
        fun i : Fin h => _a0 ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) =
        fun i : Fin h => residue A (c i) •
          (_a0 ⊗ₜ[A] KaehlerDifferential.D k A (y i)) := by
      funext i
      simp [Units.smul_def]
    have key := hyind.units_smul
      (fun i : Fin h => mk0 (residue A $ c i) $ hne i)
    rwa [hfun, ← hsmul]
  obtain ⟨bk, hbk⟩ : ∃ bk : Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      ∀ i, bk i = 1 ⊗ₜ[A] (basisKaehler k ι A i) :=
    ⟨basis (IsLocalRing.ResidueField A) $ basisKaehler k ι A,
      fun i => by simp⟩
  obtain ⟨Jst, B, hbasisInl, hbasisInr⟩ := exists_basis_sum_of_linearIndependent bk h
    (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A $ s i)) hsind
  have hcard1 := finrank_eq_card_basis B
  have hcard2 :=
    finrank_eq_card_basis bk
  have hcard3 : card {j : ι // j ∈ Jst} + card {j : ι // ¬ (j ∈ Jst)}
      = card ι := by
    rw [← card_sum]
    exact card_congr $ sumCompl fun j : ι => j ∈ Jst
  rw [card_sum, card_fin] at hcard1
  have hcard4 : card {j : ι // ¬ (j ∈ Jst)} = h := by omega
  have e := equivFinOfCardEq hcard4
  obtain ⟨ta_, htal, htar⟩ : ∃ ta_ : Fin h ⊕ {j : ι // j ∈ Jst} ≃ ι,
      (∀ l : Fin h, ta_ (Sum.inl l) = (e.symm l : ι)) ∧
      (∀ j : {j : ι // j ∈ Jst}, ta_ (Sum.inr j) = (j : ι)) :=
    ⟨(sumCongr e.symm $ refl {j : ι // j ∈ Jst}).trans
      ((sumComm _ _).trans $ sumCompl fun j : ι => j ∈ Jst),
      fun l => rfl, fun j => rfl⟩
  obtain ⟨w, hwJ, hwn⟩ : ∃ w : ι → S, (∀ j, j ∈ Jst → w j = coord k ι S j) ∧
      (∀ x : {j : ι // ¬ (j ∈ Jst)}, w x = s (e x)) := by
    exact ⟨fun j => if hj : j ∈ Jst then coord k ι S j else s $ e ⟨j, hj⟩,
      fun j hj => dif_pos hj, fun x => dif_neg x.2⟩
  have hbasisApply : ∀ x : Fin h ⊕ {j : ι // j ∈ Jst},
      B x = 1 ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A $ w $ ta_ x) := by
    rintro (l | j)
    rw [hbasisInl l, htal l, hwn $ e.symm l, apply_symm_apply]
    rw [hbasisInr j, htar j, hwJ j j.2, hbk j, basisKaehler_apply,
      algebraMap_coord]
  have hB'G : ∀ i : ι, (B.reindex ta_) i = 1 ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A $ w i) := by
    intro i
    rw [reindex_apply, hbasisApply $ ta_.symm i, apply_symm_apply]
  have hdetne := residue_det_ne_zero_of_basis_tmul (basisKaehler k ι A)
    (fun i : ι => KaehlerDifferential.D k A $ algebraMap S A $ w i) (B.reindex ta_) hB'G
  have hdetA :=
    algebraMap_det_basisKaehler k ι S A w
  have hmapq :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q A
  refine ⟨_a3.det fun i : ι => KaehlerDifferential.D k S $ w i, w, Jstᶜ,
    ?_, ?_, ?_, ?_, rfl, map_units (Away (_a3.det fun i : ι => KaehlerDifferential.D k S $ w i)) ⟨_, mem_powers _⟩⟩
  intro hgq
  apply hdetne
  rw [← hdetA, residue_eq_zero_iff, ← hmapq]
  exact mem_map_of_mem _ hgq
  intro j hj
  have hj' := mp_ mem_compl hj
  have hwj := hwn ⟨j, hj'⟩
  rw [hwj]
  exact hsq _
  rw [map_span, ← hsspan]
  congr 1
  ext x
  constructor
  rintro ⟨u, ⟨j, hj, rfl⟩, rfl⟩
  have hj' := mp_ mem_compl $ Finset.mem_coe.mp hj
  have hwj := hwn ⟨j, hj'⟩
  exact ⟨e ⟨j, hj'⟩, by rw [hwj]⟩
  rintro ⟨i, rfl⟩
  refine ⟨w $ e.symm i, ⟨e.symm i, ?_, rfl⟩, ?_⟩
  exact Finset.mem_coe.mpr $ mem_compl.mpr (e.symm i).2
  have hwj := hwn $ e.symm i
  rw [hwj, apply_symm_apply]
  intro j hj
  refine ⟨j, hwJ j ?_⟩
  simp_all

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section
variable {S : Type} [CommRing S]
theorem algebraMap_mem_map_of_mul_mem G (T : Type)
    [CommRing T] [Algebra S T] [IsLocalization (powers G) T] J g r x
    (hG : G = g * r) (hgx : g * x ∈ J) :
    algebraMap S T x ∈ Ideal.map (algebraMap S T) J := by
  have hGu :=
    map_units T (⟨G, mem_powers G⟩ : powers G)
  rw [hG, map_mul] at hGu
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hGu
  have hx : algebraMap S T x = (↑u⁻¹) * algebraMap S T (g * x) := by
    rw [map_mul, ← hu, ← mul_assoc, inv_mul, one_mul]
  rw [hx]
  exact mul_mem_left _ _ $ mem_map_of_mem _ hgx

theorem exists_away_map_ideal_eq (q : Ideal S) [q.IsPrime]
    (A : Type) [CommRing A] [Algebra S A] [IsLocalization q.primeCompl A]
    (I J : Ideal S) (hI : I.FG) (hJ : J.FG)
    (h : Ideal.map (algebraMap S A) I = Ideal.map (algebraMap S A) J) :
    ∃ g : S, g ∉ q ∧
      Ideal.map (algebraMap S $ Away g) I =
        Ideal.map (algebraMap S $ Away g) J := by
  let _a0 := algebraMap S A
  classical
  obtain ⟨tI, htI⟩ := hI
  obtain ⟨tJ, htJ⟩ := hJ
  have keyI : ∀ u, ∃ g, g ∈ q.primeCompl ∧ (u ∈ I → g * u ∈ J) := by
    intro u
    by_cases hu : u ∈ I
    have hmem : algebraMap S A u ∈ Ideal.map _a0 J := by
      rw [← h]
      exact mem_map_of_mem _ hu
    rw [algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
    obtain ⟨g, hg, hgu⟩ := hmem
    exact ⟨g, hg, fun _ => hgu⟩
    exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hu⟩
  have keyJ : ∀ v, ∃ g, g ∈ q.primeCompl ∧ (v ∈ J → g * v ∈ I) := by
    intro v
    by_cases hv : v ∈ J
    have hmem : algebraMap S A v ∈ Ideal.map _a0 I := by
      rw [h]
      exact mem_map_of_mem _ hv
    rw [algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
    obtain ⟨g, hg, hgv⟩ := hmem
    exact ⟨g, hg, fun _ => hgv⟩
    exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hv⟩
  choose gI hgI hgIu using keyI
  choose gJ hgJ hgJu using keyJ
  let G := (∏ u ∈ tI, gI u) * ∏ v ∈ tJ, gJ v
  refine ⟨G, mul_mem _ (prod_mem _ fun u _ => hgI u) $ prod_mem _ fun v _ => hgJ v, le_antisymm ?_ ?_⟩
  rw [← htI, map_span, span_le]
  rintro _ ⟨u, hu, rfl⟩
  have huI : u ∈ I := by
    rw [← htI]
    exact m100 hu
  refine algebraMap_mem_map_of_mul_mem G (Away G) J (gI u)
    ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) u ?_ $ hgIu u huI
  show (∏ z ∈ tI, gI z) * (∏ v ∈ tJ, gJ v) = _
  rw [← mul_prod_erase tI gI $ Finset.mem_coe.mp hu]
  ring
  rw [← htJ, map_span, span_le]
  rintro _ ⟨v, hv, rfl⟩
  have hvJ : v ∈ J := by
    rw [← htJ]
    exact m100 hv
  refine algebraMap_mem_map_of_mul_mem G (Away G) I (gJ v)
    ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) v ?_ $ hgJu v hvJ
  show (∏ u ∈ tI, gI u) * (∏ z ∈ tJ, gJ z) = _
  rw [← mul_prod_erase tJ gJ $ Finset.mem_coe.mp hv]
  ring
end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section

section
variable {A : Type} [CommRing A] [IsLocalRing A] {M : Type} [AddCommGroup M] [Module A M]
theorem repr_mem_maximalIdeal_of_tmul_eq_zero {n : Type} [Fintype n]
    (bb : Basis n A M) x
    (h : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x = 0) i :
    bb.repr x i ∈ IsLocalRing.maximalIdeal A := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Basis n (m14 A)
      (m14 A ⊗[A] M),
      ∀ j, bk j = (1 : m14 A) ⊗ₜ[A] bb j :=
    ⟨basis (m14 A) bb, fun j => by simp⟩
  have hkey : ∀ c (m : M), (1 : m14 A) ⊗ₜ[A] (c • m)
      = residue A c • ((1 : m14 A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : m14 A) ⊗ₜ[A] (c • m)
        = (c • (1 : m14 A)) ⊗ₜ[A] m := sy_ $ smul_tmul c 1 m
    have hA2 : c • (1 : m14 A) = residue A c := by
      rw [smul_def, mul_one, algebraMap_eq]
    have hA3 : residue A c • ((1 : m14 A) ⊗ₜ[A] m)
        = (residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hxsum : (1 : m14 A) ⊗ₜ[A] x
      = ∑ j : n, residue A (bb.repr x j) • bk j := by
    conv_lhs => rw [← bb.sum_repr x]
    rw [tmul_sum]
    exact sum_congr rfl fun j _ => by rw [hkey, hbk j]
  have h2 : bk.repr (1 ⊗ₜ[A] x) i = 0 := by
    rw [h]
    simp
  rw [hxsum, repr_sum_self] at h2
  rwa [← residue_eq_zero_iff]

theorem residue_det_ne_zero_of_tmul_eq_basis {ι : Type} [Fintype ι] [DecidableEq ι]
    (bA : Basis ι A M) (G : ι → M)
    (B' : Basis ι (IsLocalRing.ResidueField A) $ IsLocalRing.ResidueField A ⊗[A] M)
    (hB' : ∀ i, B' i = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] G i) :
    residue A (bA.det G) ≠ 0 := by
  classical
  obtain ⟨bk, hbk⟩ : ∃ bk : Basis ι (m14 A)
      (m14 A ⊗[A] M),
      ∀ i, bk i = (1 : m14 A) ⊗ₜ[A] bA i :=
    ⟨basis (m14 A) bA, fun i => by simp⟩
  have hkey : ∀ c (m : M), (1 : m14 A) ⊗ₜ[A] (c • m)
      = residue A c • ((1 : m14 A) ⊗ₜ[A] m) := by
    intro c m
    have hA1 : (1 : m14 A) ⊗ₜ[A] (c • m)
        = (c • (1 : m14 A)) ⊗ₜ[A] m := sy_ $ smul_tmul c 1 m
    have hA2 : c • (1 : m14 A) = residue A c := by
      rw [smul_def, mul_one, algebraMap_eq]
    have hA3 : residue A c • ((1 : m14 A) ⊗ₜ[A] m)
        = (residue A c * 1) ⊗ₜ[A] m := rfl
    rw [hA1, hA2, hA3, mul_one]
  have hmat : ∀ i j, bk.repr (B' j) i = residue A (bA.toMatrix G i j) := by
    intro i j
    have hGj : B' j = ∑ l : ι, residue A (bA.repr (G j) l) • bk l := by
      rw [hB' j]
      conv_lhs => rw [← bA.sum_repr $ G j]
      rw [tmul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [hkey, hbk l]
    rw [hGj, repr_sum_self, toMatrix_apply]
  have hdet : bk.det (⇑B') = residue A (bA.det G) := by
    rw [det_apply, det_apply, map_det]
    congr 1
    ext i j
    simp [toMatrix_apply]
    exact hmat i j
  rw [← hdet]
  exact (bk.isUnit_det B').ne_zero
end

section
variable (k : Type) [CommRing k]
section
variable (A : Type) [CommRing A] [Algebra k A] [IsLocalRing A] {n : Type} [Fintype n] (bb : Basis n A (KaehlerDifferential k A)) (J : Ideal A)
include bb
theorem mem_maximalIdeal_mul_of_tmul_D_eq_zero (hJmax : J ≤ IsLocalRing.maximalIdeal A)
    [FormallySmooth k $ A ⧸ J] z (hz : z ∈ J)
    (h0 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A z = 0) :
    z ∈ IsLocalRing.maximalIdeal A * J := by
  classical
  obtain ⟨Jm, hJmdef⟩ : ∃ Jm : Ideal A, Jm = m16 A * J := ⟨_, rfl⟩
  have hmulJ : ∀ c ∈ m16 A, ∀ u ∈ J, c * u ∈ Jm := by
    intro c hc u hu
    rw [hJmdef]
    exact mul_mem_mul hc hu
  have hJmle : Jm ≤ J := by
    rw [hJmdef]
    exact mul_le_right
  have hsmulg : ∀ c x, c • x = m5 Jm c * x := by
    intro c x
    rw [smul_def, m203]
  have hsmulmk : ∀ c u : A,
      c • (m5 Jm u) = m5 Jm (c * u) := by
    intro c u
    rw [hsmulg, ← map_mul]
  have hrh0 : ∀ a ∈ Jm, (Ideal.Quotient.mkₐ A J) a = 0 := by
    intro a ha
    dsimp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr $ hJmle ha
  let rhA :=
    Ideal.Quotient.liftₐ Jm (Ideal.Quotient.mkₐ A J) hrh0
  let rh_ := rhA.restrictScalars k
  have hrhmkA : ∀ a : A, rhA (m5 Jm a) = m5 J a := fun _ => rfl
  have hrhmk : ∀ a : A, rh_ (m5 Jm a) = m5 J a := fun _ => rfl
  have hrhsurj : Surjective rh_ := by
    intro c
    obtain ⟨a, rfl⟩ := mk_surjective c
    exact ⟨m5 Jm a, hrhmk a⟩
  let _m0 := (rh_ : RH (A ⧸ Jm) $ A ⧸ J)
  have hker2 : m41 _m0 ^ 2 = ⊥ := by
    rw [pow_two]
    refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
    intro u hu v hv
    obtain ⟨a, rfl⟩ := mk_surjective u
    obtain ⟨b, rfl⟩ := mk_surjective v
    have ha : a ∈ J := by
      have h1 : m5 J a = 0 := by
        rw [← hrhmk a]
        exact RingHom.mem_ker.mp hu
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    have hb : b ∈ J := by
      have h1 : m5 J b = 0 := by
        rw [← hrhmk b]
        exact RingHom.mem_ker.mp hv
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    refine mpr_ (Submodule.mem_bot _) ?_
    rw [← map_mul, eq_zero_iff_mem]
    exact hmulJ a (hJmax ha) b hb
  have hprod : ∀ u v : A ⧸ Jm, rhA u = 0 → rhA v = 0 → u * v = 0 := by
    intro u v hu hv
    have hmem : u * v ∈ m41 _m0 ^ 2 := by
      rw [pow_two]
      exact mul_mem_mul (RingHom.mem_ker.mpr hu) $ RingHom.mem_ker.mpr hv
    rw [hker2] at hmem
    simpa using hmem
  obtain ⟨σ, hsg_⟩ : ∃ σ : (A ⧸ J) →ₐ[k] (A ⧸ Jm), ∀ c, rh_ (σ c) = c := by
    refine ⟨liftOfSurjective
      (AlgHom.id k $ A ⧸ J) rh_ hrhsurj ⟨2, hker2⟩, fun c => ?_⟩
    have h := comp_liftOfSurjective
      (AlgHom.id k $ A ⧸ J) rh_ hrhsurj ⟨2, hker2⟩
    have h2 := congr_fun h c
    simpa using h2
  have hrhsg : ∀ c : A ⧸ J, rhA (σ c) = c := hsg_
  have hkerel : ∀ a : A,
      rhA (m5 Jm a - σ (m5 J a)) = 0 := by
    intro a
    rw [map_sub, hrhmkA a, hrhsg $ m5 J a, sub_self]
  have hmkJmsmul : ∀ (c : k) (a : A),
      Ideal.Quotient.mk Jm (c • a) = c • Ideal.Quotient.mk Jm a := by
    intro c a
    rw [smul_def, map_mul, smul_def, ← Ideal.Quotient.algebraMap_eq,
      ← algebraMap_apply k A $ A ⧸ Jm]
  have hmkJsmul : ∀ (c : k) (a : A),
      Ideal.Quotient.mk J (c • a) = c • Ideal.Quotient.mk J a := by
    intro c a
    rw [smul_def, map_mul, smul_def, ← Ideal.Quotient.algebraMap_eq,
      ← algebraMap_apply k A $ A ⧸ J]
  have hadd : ∀ a b : A,
      m5 Jm (a + b) - σ (m5 J $ a + b)
        = m5 Jm a - σ (m5 J a)
          + (m5 Jm b - σ (m5 J b)) := by
    intro a b
    simp [map_add]
    ring
  have hsmulk : ∀ c a,
      m5 Jm (c • a) - σ (m5 J $ c • a)
        = (m99 k) c • (m5 Jm a - σ (m5 J a)) := by
    intro c a
    dsimp
    rw [hmkJmsmul c a, hmkJsmul c a, map_smul, smul_sub]
  have hleib : ∀ a b : A,
      m5 Jm (a * b) - σ (m5 J $ a * b)
        = a • (m5 Jm b - σ (m5 J b))
          + b • (m5 Jm a - σ (m5 J a)) := by
    intro a b
    have hz2 := hprod (m5 Jm a - σ (m5 J a))
      (m5 Jm b - σ (m5 J b)) (hkerel a) $ hkerel b
    rw [hsmulg a, hsmulg b]
    simp [map_mul]
    linear_combination -hz2
  obtain ⟨Dder, hDapp⟩ : ∃ D : Derivation k A $ A ⧸ Jm,
      ∀ a : A, D a = m5 Jm a - σ (m5 J a) :=
    ⟨mk'
      { toFun := fun a => m5 Jm a - σ (m5 J a)
        map_add' := hadd
        map_smul' := hsmulk } hleib, fun _ => rfl⟩
  have hderivLift : ∀ a : A,
      Dder.liftKaehlerDifferential (m13 k A a) = Dder a := by
    intro a
    simp [liftKaehlerDifferential_comp_D]
  have hcomp : ∀ om_ : KaehlerDifferential k A,
      rhA (Dder.liftKaehlerDifferential om_) = 0 := by
    have hker : (⊤ : Submodule A $ KaehlerDifferential k A) ≤
        m177 (rhA.toLinearMap.comp Dder.liftKaehlerDifferential) := by
      rw [← span_range_derivation, Submodule.span_le]
      rintro y ⟨a, rfl⟩
      rw [mem_coe, mem_ker, LinearMap.comp_apply]
      dsimp
      rw [hderivLift a, hDapp a]
      exact hkerel a
    intro om_
    have h2 := hker (mem_top : om_ ∈ ⊤)
    rwa [mem_ker, LinearMap.comp_apply] at h2
  let _a0 := m13 k A z
  have hcoef : ∀ i : n,
      bb.repr _a0 i ∈ m16 A :=
    fun i => repr_mem_maximalIdeal_of_tmul_eq_zero bb _a0 h0 i
  have hLb : ∀ i : n, ∃ u : A, u ∈ J ∧
      Dder.liftKaehlerDifferential (bb i) = m5 Jm u := by
    intro i
    obtain ⟨u, hu⟩ := mk_surjective $ Dder.liftKaehlerDifferential $ bb i
    refine ⟨u, ?_, sy_ hu⟩
    have h1 : rhA (m5 Jm u) = 0 := by
      rw [hu]
      exact hcomp $ bb i
    rw [hrhmkA u] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hsum : Dder.liftKaehlerDifferential _a0 = 0 := by
    conv_lhs => rw [← bb.sum_repr _a0]
    rw [map_sum]
    refine sum_eq_zero fun i _ => ?_
    obtain ⟨u, huJ, hu⟩ := hLb i
    rw [map_smul, hu, hsmulmk, eq_zero_iff_mem]
    exact hmulJ _ (hcoef i) u huJ
  have hzval : m5 Jm z
      = Dder.liftKaehlerDifferential _a0 := by
    rw [hderivLift z, hDapp z, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero, sub_zero]
  have hfinal : m5 Jm z = 0 := by
    rw [hzval, hsum]
  rw [← hJmdef]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfinal

theorem ideal_eq_span_of_tmul_D_mem_span (hJfg : J.FG)
    (hJmax : J ≤ IsLocalRing.maximalIdeal A) [FormallySmooth k $ A ⧸ J] (r : ℕ)
    (x : Fin r → A) (hxJ : ∀ i : Fin r, x i ∈ J)
    (hspan : ∀ y ∈ J,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          (Set.range fun i : Fin r =>
            (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x i))) :
    J = Ideal.span (Set.range x) := by
  classical
  have hsmeq : (m16 A • J)
      = m16 A * J := by
    rw [smul_eq_mul]
  refine le_antisymm ?_ ?_
  have hstep : J ≤ m17 (m30 x) ⊔ m16 A • J := by
    rw [hsmeq]
    intro y hy
    have hy' := hspan y hy
    rw [mem_span_range_iff_exists_fun] at hy'
    obtain ⟨c, hc⟩ := hy'
    obtain ⟨c', hc'⟩ : ∃ c' : Fin r → A, ∀ i, residue A (c' i) = c i := by
      choose c' hc' using fun i => mk_surjective $ c i
      exact ⟨c', hc'⟩
    let _a0 := (1 : m14 A)
    have hsum : _a0 ⊗ₜ[A]
        m13 k A (∑ i, c' i * x i)
        = ∑ i, c i • (_a0 ⊗ₜ[A]
          m13 k A (x i)) := by
      rw [map_sum, tmul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_comm (c' i) $ x i,
        KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal, hc' i]
      exact hJmax $ hxJ i
    have h0 : _a0 ⊗ₜ[A]
        m13 k A (y - ∑ i, c' i * x i) = 0 := by
      rw [map_sub, tmul_sub, hsum, hc, sub_self]
    have hrw : y = (y - ∑ i, c' i * x i) + ∑ i, c' i * x i := by ring
    rw [hrw]
    exact m60 _ (mem_sup_right $ mem_maximalIdeal_mul_of_tmul_D_eq_zero k A bb J hJmax _ (m162 _ hy $ Submodule.sum_mem _ fun i _ => mul_mem_left _ _ $ hxJ i) h0) $ mem_sup_left $ m133 _ fun i _ => mul_mem_left _ _ $ m100 ⟨i, rfl⟩
  refine le_of_le_smul_of_le_jacobson_bot hJfg
    (jacobson_eq_maximalIdeal (⊥) ?_).ge hstep
  simp_all
  rw [span_le]
  rintro _ ⟨i, rfl⟩
  exact hxJ i
end

theorem formallyEtale_away_of_isUnit_det (ι : Type) [Fintype ι]
    [DecidableEq ι] (S : Type) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]
    (g : S) (T : Type) [CommRing T] [Algebra S T] [IsLocalization (powers g) T]
    (w : ι → S)
    (hdet : IsUnit $ algebraMap S T
      ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S $ w i)) :
    @FormallyEtale (MvPolynomial ι k) T _ _
      (toAlgebra
        (MvPolynomial.eval₂Hom ((algebraMap S T).comp $ algebraMap k S)
          (fun j : ι => algebraMap S T $ w j))) := by
  classical
  let _a0 := algebraMap S T
  let instKT := (_a0.comp $ algebraMap k S).toAlgebra
  let _s0 := MvPolynomial ι k
  let instAlgebraMvPolynomial :=
    (_a0.comp $ algebraMap _s0 S).toAlgebra
  have instTkS : IsScalarTower k S T := of_algebraMap_eq fun _ => rfl
  have instTPS : IsScalarTower _s0 S T :=
    of_algebraMap_eq fun _ => rfl
  have instTkP : IsScalarTower k _s0 T :=
    of_algebraMap_eq fun x => by
      rw [algebraMap_apply k S T x,
        algebraMap_apply k _s0 S x]
      rfl
  have instFEST : FormallyEtale S T :=
    of_isLocalization (M := powers g)
  have instFEPT : FormallyEtale _s0 T :=
    comp _s0 S T
  have instFSkT :=
    m139 k _s0 T
  have hdet' := hdet
  rw [algebraMap_det_basisKaehler k ι S T w] at hdet'
  have h := formallyEtale_aeval_of_isUnit_det (basisKaehler k ι T)
    (fun i => algebraMap S T $ w i) hdet'
  exact h
end

theorem map_eq_of_map_eq_of_away_mul {S : Type} [CommRing S] {T1_ T2_ : Type}
    [CommRing T1_] [CommRing T2_] [Algebra S T1_] [Algebra S T2_] (g1_ d : S)
    [IsLocalization (powers g1_) T1_]
    [IsLocalization (powers $ g1_ * d) T2_] (I J : Ideal S)
    (h : Ideal.map (algebraMap S T1_) I = Ideal.map (algebraMap S T1_) J) :
    Ideal.map (algebraMap S T2_) I = Ideal.map (algebraMap S T2_) J := by
  have hgu :=
    map_units (M := powers $ g1_ * d) T2_
      ⟨g1_ * d, mem_powers _⟩
  rw [map_mul] at hgu
  have hFu : ∀ y : powers g1_, IsUnit $ algebraMap S T2_ y := by
    rintro ⟨y, m, rfl⟩
    dsimp
    rw [map_pow]
    exact (isUnit_of_mul_isUnit_left hgu).pow m
  let _a0 := algebraMap S T1_
  let _a1 := algebraMap S T2_
  obtain ⟨F, hF⟩ : ∃ F : RingHom T1_ T2_, F.comp _a0 = _a1 :=
    ⟨IsLocalization.lift (M := powers g1_) (S := T1_) hFu,
      RingHom.ext fun x => lift_eq hFu x⟩
  calc Ideal.map _a1 I
      = Ideal.map F (Ideal.map _a0 I) := by rw [map_map, hF]
    _ = Ideal.map F (Ideal.map _a0 J) := by rw [h]
    _ = Ideal.map _a1 J := by rw [map_map, hF]

end

section

variable (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι]
  (S : Type) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]
  [IsNoetherianRing S] (I q : Ideal S) [q.IsPrime]

section
variable (A : Type) [CommRing A] [Algebra S A] [Algebra k A] [IsScalarTower k S A] [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A] [FormallySmooth k (A ⧸ Ideal.map (algebraMap S A) I)] (hIq : I ≤ q)
include A hIq
theorem exists_away_ideal_eq_span_and_isUnit_det :
    ∃ (g : S) (w : ι → S) (T : Finset ι),
      g ∉ q ∧
      (∀ j ∈ T, w j ∈ I) ∧
      Ideal.map (algebraMap S $ Away g) (Ideal.span $ w '' (↑T : Set ι)) =
        Ideal.map (algebraMap S $ Away g) I ∧
      (∀ j ∉ T, ∃ i : ι, w j = coord k ι S i) ∧
      IsUnit (algebraMap S (Away g)
        ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S $ w i)) := by
  let _a11 := KaehlerDifferential.D k S
  let _a3 := basisKaehler k ι S
  classical
  have instFEloc : FormallyEtale S A :=
    of_isLocalization (M := q.primeCompl)
  let _s0 := MvPolynomial ι k
  let instPA :=
    ((algebraMap S A).comp $ algebraMap _s0 S).toAlgebra
  have instT1 : IsScalarTower _s0 S A :=
    of_algebraMap_eq fun _ => rfl
  have t2Space_cuspAdeles : IsScalarTower k _s0 A :=
    of_algebraMap_eq fun x => by
      rw [algebraMap_apply k S A x,
        algebraMap_apply k _s0 S x]
      rfl
  have instFEPA :=
    comp _s0 S A
  have hmapq :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q A
  have hJAm : Ideal.map (algebraMap S A) I ≤ IsLocalRing.maximalIdeal A := by
    rw [← hmapq]
    exact map_mono hIq
  obtain ⟨tF, htF⟩ := noetherian I
  have hspanI : Ideal.span (↑(tF.image $ algebraMap S A) : Set A)
      = Ideal.map (algebraMap S A) I := by
    rw [coe_image, ← htF, map_span]
  obtain ⟨bset, hbsub, hbspan, hbind⟩ :=
    exists_linearIndependent (K := IsLocalRing.ResidueField A)
      (t := (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A a) '' (↑(tF.image $ algebraMap S A) : Set A))
  have hbfin : bset.Finite :=
    subset (image _ $ finite_toSet _) hbsub
  let _ := hbfin.fintype
  choose pre hpre1 hpre2 using fun v : bset => hbsub v.2
  have hpre1' : ∀ v, ∃ t, t ∈ tF ∧ algebraMap S A t = pre v := by simp_all
  choose pres hpres1 hpres2 using hpre1'
  obtain ⟨s, hs⟩ : ∃ s : Fin (card bset) → S,
      ∀ i, s i = pres ((equivFin bset).symm i) := ⟨_, fun _ => rfl⟩
  have hsI : ∀ i, s i ∈ I := by
    intro i
    rw [hs i, ← htF]
    exact subset_span $ Finset.mem_coe.mpr $ hpres1 _
  have hfun : (fun i : Fin (card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A $ s i))
      = fun i : Fin (card bset) =>
        (((equivFin bset).symm i : bset) :
          IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) := by simp_all
  have hind : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : Fin (card bset) => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A $ s i)) := by
    rw [hfun]
    exact hbind.comp _ (equivFin bset).symm.injective
  have hrange : Set.range (fun i : Fin (card bset) =>
      1 ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A $ s i)) = bset := by
    rw [hfun]
    ext v
    constructor
    rintro ⟨i, rfl⟩
    exact ((equivFin bset).symm i).2
    intro hv
    exact ⟨(equivFin bset) ⟨v, hv⟩, by simp⟩
  have hxJ : ∀ i, algebraMap S A (s i) ∈ Ideal.map (algebraMap S A) I := fun i =>
    mem_map_of_mem _ $ hsI i
  have hgen : ∀ y ∈ Ideal.map (algebraMap S A) I,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          ((fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A a) '' (↑(tF.image $ algebraMap S A) : Set A)) := by
    intro y hy
    rw [← hspanI] at hy
    obtain ⟨f, -, hf⟩ := mem_span_finset.mp hy
    rw [← hf, map_sum, tmul_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have ham : a ∈ IsLocalRing.maximalIdeal A := by
      refine hJAm ?_
      rw [← hspanI]
      exact subset_span $ Finset.mem_coe.mpr ha
    have heq : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f a • a)
        = residue A (f a) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A a) := by
      rw [smul_eq_mul, mul_comm,
        KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal]
      exact ham
    rw [heq]
    exact smul_mem _ _
      (subset_span ⟨a, Finset.mem_coe.mpr ha, rfl⟩)
  have hspanx : ∀ y ∈ Ideal.map (algebraMap S A) I,
      (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A y ∈
        Submodule.span (IsLocalRing.ResidueField A)
          (Set.range fun i : Fin (card bset) =>
            (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
              KaehlerDifferential.D k A (algebraMap S A $ s i)) := by simp_all
  have hJAeq :=
    ideal_eq_span_of_tmul_D_mem_span k A (basisKaehler k ι A) (Ideal.map (algebraMap S A) I)
      (noetherian _) hJAm
      (card bset) (fun i => algebraMap S A $ s i) hxJ hspanx
  obtain ⟨bkk, hbk⟩ : ∃ bkk : Basis ι (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A),
      ∀ i, bkk i = 1 ⊗ₜ[A] (basisKaehler k ι A i) :=
    ⟨basis (IsLocalRing.ResidueField A) $ basisKaehler k ι A,
      fun i => by simp⟩
  obtain ⟨Jst, B, hbasisInl, hbasisInr⟩ := exists_basis_sum_of_linearIndependent bkk (card bset)
    (fun i : Fin (card bset) => 1 ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A $ s i)) hind
  have hcard1 :=
    finrank_eq_card_basis B
  have hcard2 :=
    finrank_eq_card_basis bkk
  have hcard3 : card {j : ι // j ∈ Jst} + card {j : ι // ¬ (j ∈ Jst)}
      = card ι := by
    rw [← card_sum]
    exact card_congr $ sumCompl fun j => j ∈ Jst
  rw [card_sum, card_fin] at hcard1
  have hcard4 : card {j : ι // ¬ (j ∈ Jst)} = card bset := by omega
  have e := equivFinOfCardEq hcard4
  obtain ⟨ta_, htal, htar⟩ : ∃ ta_ : Fin (card bset) ⊕ {j : ι // j ∈ Jst} ≃ ι,
      (∀ l : Fin $ card bset, ta_ (Sum.inl l) = (e.symm l : ι)) ∧
      (∀ j : {j : ι // j ∈ Jst}, ta_ (Sum.inr j) = (j : ι)) :=
    ⟨(sumCongr e.symm $ refl {j : ι // j ∈ Jst}).trans
      ((sumComm _ _).trans $ sumCompl fun j : ι => j ∈ Jst),
      fun l => rfl, fun j => rfl⟩
  obtain ⟨w, hwJ, hwn⟩ : ∃ w : ι → S, (∀ j, j ∈ Jst → w j = coord k ι S j) ∧
      (∀ x : {j : ι // ¬ (j ∈ Jst)}, w x = s (e x)) := by
    exact ⟨fun j => if hj : j ∈ Jst then coord k ι S j else s $ e ⟨j, hj⟩,
      fun j hj => dif_pos hj, fun x => dif_neg x.2⟩
  have hbasisApply : ∀ x : Fin (card bset) ⊕ {j : ι // j ∈ Jst},
      B x = 1 ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A $ w $ ta_ x) := by
    rintro (l | j)
    rw [hbasisInl l, htal l, hwn $ e.symm l, apply_symm_apply]
    rw [hbasisInr j, htar j, hwJ j j.2, hbk j, basisKaehler_apply,
      algebraMap_coord]
  have hB'G : ∀ i, (B.reindex ta_) i = 1 ⊗ₜ[A]
      KaehlerDifferential.D k A (algebraMap S A $ w i) := by
    intro i
    rw [reindex_apply, hbasisApply $ ta_.symm i, apply_symm_apply]
  have hdetne := residue_det_ne_zero_of_tmul_eq_basis (basisKaehler k ι A)
    (fun i => KaehlerDifferential.D k A $ algebraMap S A $ w i) (B.reindex ta_) hB'G
  have hdetA :=
    algebraMap_det_basisKaehler k ι S A w
  have hg0q : (_a3.det fun i => _a11 $ w i) ∉ q := by
    intro hgq
    apply hdetne
    rw [← hdetA, residue_eq_zero_iff, ← hmapq]
    exact mem_map_of_mem _ hgq
  let _m0 := Ideal.span $ w '' (↑(Jstᶜ) : Set ι)
  have hspanA : Ideal.map (algebraMap S A) _m0
      = Ideal.map (algebraMap S A) I := by
    rw [map_span, hJAeq]
    congr 1
    ext v
    constructor
    rintro ⟨u, ⟨j, hj, rfl⟩, rfl⟩
    have hj' := mem_compl.mp $ Finset.mem_coe.mp hj
    have hwj := hwn ⟨j, hj'⟩
    exact ⟨e ⟨j, hj'⟩, by rw [hwj]⟩
    rintro ⟨i, rfl⟩
    refine ⟨w $ e.symm i, ⟨e.symm i, Finset.mem_coe.mpr $ mem_compl.mpr (e.symm i).2, rfl⟩, ?_⟩
    have hwj : w (e.symm i) = s (e $ e.symm i) := hwn $ e.symm i
    rw [hwj, apply_symm_apply]
  obtain ⟨g1_, hg1q, hg1eq⟩ := exists_away_map_ideal_eq q A
    _m0 I
    (fg_span $ image w $ finite_toSet _)
    (noetherian I) hspanA
  refine ⟨g1_ * (_a3.det fun i => _a11 $ w i), w,
    Jstᶜ, ?_, ?_, map_eq_of_map_eq_of_away_mul g1_ (_a3.det fun i => _a11 $ w i) _ _ hg1eq, ?_, ?_⟩
  intro hmem
  rcases Ideal.IsPrime.mem_or_mem ‹q.IsPrime› hmem with h1 | h2
  exact hg1q h1
  exact hg0q h2
  intro j hj
  have hj' := mem_compl.mp hj
  have hwj := hwn ⟨j, hj'⟩
  rw [hwj]
  exact hsI _
  intro j hj
  refine ⟨j, hwJ j ?_⟩
  simp_all
  have hu : IsUnit $ algebraMap S
      (Away $ g1_ *
        (_a3.det fun i => _a11 $ w i))
      (g1_ * (_a3.det fun i => _a11 $ w i)) :=
    map_units _ ⟨_, mem_powers _⟩
  rw [map_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem exists_away_ideal_eq_span_and_formallyEtale :
    ∃ (g : S) (w : ι → S) (T : Finset ι),
      g ∉ q ∧
      (∀ j ∈ T, w j ∈ I) ∧
      Ideal.map (algebraMap S $ Away g) (Ideal.span $ w '' (↑T : Set ι)) =
        Ideal.map (algebraMap S $ Away g) I ∧
      (∀ j ∉ T, ∃ i : ι, w j = coord k ι S i) ∧
      @FormallyEtale (MvPolynomial ι k) (Away g) _ _
        (toAlgebra
          (MvPolynomial.eval₂Hom
            ((algebraMap S $ Away g).comp $ algebraMap k S)
            (fun j : ι => algebraMap S (Away g) $ w j))) := by
  classical
  obtain ⟨g, w, T, hgq, hwI, hmap, hcoord, hdet⟩ :=
    exists_away_ideal_eq_span_and_isUnit_det k ι S I q A hIq
  exact ⟨g, w, T, hgq, hwI, hmap, hcoord,
    formallyEtale_away_of_isUnit_det k ι S g (Away g) w hdet⟩
end

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end
section
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution

noncomputable def residueFieldExtension (k A : Type) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [Algebra k $ IsLocalRing.ResidueField A]
    [IsScalarTower k A $ IsLocalRing.ResidueField A] :
    Extension k $ IsLocalRing.ResidueField A :=
  { Ring := A
    σ := surjInv (mk_surjective :
      Surjective $ algebraMap A $ IsLocalRing.ResidueField A)
    algebraMap_σ := surjInv_eq _ }

section
variable (A : Type) [CommRing A] [IsLocalRing A]
theorem one_tmul_residueField_surjective
    (M : Type) [AddCommGroup M] [Module A M] :
    Surjective fun x : M => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x := by
  let _a0 := (1 : m14 A)
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a x =>
      obtain ⟨a0_, rfl⟩ := residue_surjective a
      refine ⟨a0_ • x, ?_⟩
      have h1 : (a0_ • _a0) = residue A a0_ := by
        rw [smul_def, mul_one]
        rfl
      dsimp
      rw [← smul_tmul, h1]
  | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      dsimp
      rw [tmul_add, show _a0 ⊗ₜ[A] u = x from hu,
        show _a0 ⊗ₜ[A] v = y from hv]

theorem tmul_eq_zero_of_toCotangent_eq_zero
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (x : ↥I)
    (hx : I.toCotangent x = 0) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x
      = (0 : IsLocalRing.ResidueField A ⊗[A] ↥I) := by
  rw [toCotangent_eq_zero] at hx
  have key : ∀ t, t ∈ I ^ 2 →
      t ∈ I ∧ ∀ ht, (1 : m14 A) ⊗ₜ[A] (⟨t, ht⟩ : ↥I) = 0 := by
    intro t ht
    rw [sq] at ht
    refine mul_induction_on ht ?_ ?_
    intro a ha b hb
    refine ⟨mul_mem_right _ _ ha, ?_⟩
    intro hab
    have h2 : (⟨a * b, hab⟩ : ↥I) = a • (⟨b, hb⟩ : ↥I) := by
      ext
      simp [smul_eq_mul]
    have h3 : a • (1 : m14 A) = 0 := by
      rw [smul_def, mul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.2 $ hI ha
    rw [h2, ← smul_tmul, h3, zero_tmul]
    rintro u v ⟨hu, hu2⟩ ⟨hv, hv2⟩
    refine ⟨m128 _ hu hv, ?_⟩
    intro huv
    have h4 : (⟨u + v, huv⟩ : ↥I) = (⟨u, hu⟩ : ↥I) + ⟨v, hv⟩ := rfl
    rw [h4, tmul_add, hu2, hv2, add_zero]
  exact an2 (key x hx) x.2
end

section
variable (k A : Type) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
noncomputable def kerToTensorResidueField :
    ↥(RingHom.ker $ algebraMap A $ IsLocalRing.ResidueField A) →ₗ[A]
      IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A :=
  KaehlerDifferential.kerToTensor k A $ IsLocalRing.ResidueField A

theorem dTensor_apply (x : ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))) :
    kerToTensorResidueField k A x
      = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A)) := rfl

end

section

variable (k A : Type) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A $ KaehlerDifferential k A] [Module.Finite A $ KaehlerDifferential k A]
  [Algebra k $ IsLocalRing.ResidueField A]
  [IsScalarTower k A $ IsLocalRing.ResidueField A]
  [Algebra.FormallySmooth k $ IsLocalRing.ResidueField A]

omit [IsNoetherianRing A] [Module.Free A $ KaehlerDifferential k A]
  [Module.Finite A $ KaehlerDifferential k A] in
omit [IsNoetherianRing A] [Module.Free A $ KaehlerDifferential k A]
  [Module.Finite A $ KaehlerDifferential k A] in
theorem linearIndependent_tensor_D_of_ideal_eq_ker {ι : Type} (I : Ideal A)
    (hI : I = RingHom.ker (algebraMap A $ IsLocalRing.ResidueField A))
    (m : ι → ↥I)
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A $ (m i : A))) := by
  subst hI
  classical
    have _i51 : Function.Injective $ LinearMap.liftBaseChange (IsLocalRing.ResidueField A) $ kerToTensorResidueField k A := by
      let _c0 := residueFieldExtension k A
      rw [← ker_eq_bot, ker_eq_bot']
      intro z hz
      let _a0 := m41 $ algebraMap A $ m14 A
      obtain ⟨x, rfl⟩ := one_tmul_residueField_surjective A
        (↥_a0) z
      let _a2 := m13 k A (x : A)
      let _a3 := (1 : m14 A)
      have h1 : liftBaseChange (m14 A) (kerToTensorResidueField k A)
          (_a3 ⊗ₜ[A] x)
          = _a3 ⊗ₜ[A] _a2 := by
        rw [liftBaseChange_tmul, one_smul, dTensor_apply]
      have h2 : _a3 ⊗ₜ[A] _a2
          = (0 : m14 A ⊗[A] KaehlerDifferential k A) := by
        rwa [← h1]
      let _a1 := (x : A)
      have h3 : _a1 ∈ _a0 ^ 2 :=
        by
        have : FormallySmooth k _c0.Ring :=
          inferInstanceAs $ FormallySmooth k A
        have hs0 : Subsingleton $ H1Cotangent k $ m14 A :=
          subsingleton_h1Cotangent
        have hsub : Subsingleton _c0.H1Cotangent :=
          (Algebra.Extension.equivH1CotangentOfFormallySmooth _c0).toEquiv.subsingleton
        have hsub2 : Subsingleton ↥(m177 _c0.cotangentComplex) := hsub
        have hbot : m177 _c0.cotangentComplex = ⊥ :=
          eq_bot_of_subsingleton
        have hx2 : _a1 ∈ _c0.ker := x.2
        have h0 : _c0.cotangentComplex
            (Algebra.Extension.Cotangent.mk ⟨_a1, hx2⟩) = 0 := by
          rwa [Algebra.Extension.cotangentComplex_mk]
        have h1 : Algebra.Extension.Cotangent.mk (⟨_a1, hx2⟩ : _c0.ker) = 0 :=
          (mp_ ker_eq_bot hbot) $ by rw [h0, map_zero]
        rwa [Algebra.Extension.Cotangent.mk_eq_zero_iff] at h1
      have hle : _a0
          ≤ m16 A := by
        intro a ha
        exact Ideal.Quotient.eq_zero_iff_mem.mp ha
      refine tmul_eq_zero_of_toCotangent_eq_zero A
        _a0 hle x ?_
      rwa [toCotangent_eq_zero]
    have hmain := hm.map' (liftBaseChange (m14 A)
        (kerToTensorResidueField k A)) $ ker_eq_bot.mpr _i51
    have heq : (⇑(liftBaseChange (m14 A) $ kerToTensorResidueField k A) ∘
        fun i => (1 : m14 A) ⊗ₜ[A] (m i))
        = fun i =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (m i : A)) := by
      funext i
      simp only [comp_apply, liftBaseChange_tmul, one_smul, dTensor_apply]
    rwa [heq] at hmain

omit [IsNoetherianRing A] [Module.Free A $ KaehlerDifferential k A]
  [Module.Finite A $ KaehlerDifferential k A] in
theorem linearIndependent_tensor_D_of_maximalIdeal {ι : Type}
    (m : ι → (IsLocalRing.maximalIdeal A : Ideal A))
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A $ (m i : A))) :=
  linearIndependent_tensor_D_of_ideal_eq_ker k A (m16 A)
    (mk_ker).symm m hm

omit [Module.Free A $ KaehlerDifferential k A] [Module.Finite A $ KaehlerDifferential k A] in
theorem exists_local_parameters :
    ∃ h y,
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i : Fin h =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A $ y i)) := by
  let _a0 := m16 A
  let _c0 := m14 A ⊗[A] ↥_a0
  classical
  obtain ⟨y, hy⟩ : ∃ y : Fin (finrank (m14 A)
      _c0) →
      ↥_a0,
      ∀ i, 1 ⊗ₜ[A] (y i)
        = finBasis (m14 A)
            _c0 i := by
    choose y hy using fun i => one_tmul_residueField_surjective A (↥_a0)
      (finBasis (m14 A)
        _c0 i)
    exact ⟨y, hy⟩
  refine ⟨_, fun i => y i, ?_, ?_⟩
  have h3 := congrArg (Submodule.map (m16 A).subtype) $ span_eq_top_of_tmul_eq_basis y (finBasis (m14 A) _c0) hy
  rw [Submodule.map_span, map_subtype_top] at h3
  have himg : (_a0.subtype '' m30 y)
      = m30 fun i => (y i : A) := by
    ext t
    simp
  rwa [himg] at h3
  have hfun := funext hy
  refine linearIndependent_tensor_D_of_maximalIdeal k A y ?_
  rw [hfun]
  exact linearIndependent _

theorem exists_local_parameters_and_dual_derivations :
    ∃ (h : ℕ) (y : Fin h → A) (δ : Fin h → Derivation k A A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      ∀ i j : Fin h, δ i (y j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨h, y, hspan, hind⟩ := exists_local_parameters k A
  obtain ⟨v, hv⟩ : ∃ v : Fin h → (m14 A ⊗[A] KaehlerDifferential k A),
      v = fun i => 1 ⊗ₜ[A] (m13 k A $ y i) :=
    ⟨_, rfl⟩
  rw [← hv] at hind
  have hps_ : ∀ i, ∃ ps_ : (m14 A ⊗[A] KaehlerDifferential k A)
      →ₗ[m14 A] m14 A,
      ∀ j, ps_ (v j) = if i = j then 1 else 0 := by
    intro i
    obtain ⟨g, hg⟩ := exists_extend
      ((lapply i).comp hind.repr)
    refine ⟨g, fun j => ?_⟩
    have hmem : v j ∈ m72 (m14 A) (m30 v) :=
      subset_span $ mem_range_self j
    have h1 : hind.repr ⟨v j, hmem⟩ = Finsupp.single j 1 := hind.repr_eq_single j _ rfl
    have h2 := LinearMap.congr_fun hg ⟨v j, hmem⟩
    simp only [LinearMap.coe_comp, comp_apply, subtype_apply,
      h1, lapply_apply, single_apply] at h2
    rw [h2]
    by_cases hij : i = j
    simp [hij]
    simp [hij, symm hij]
  choose ps_ hps' using hps_
  simp only [hv] at hps'
  have hsurj : Surjective $ algebraMap A $ m14 A :=
    mk_surjective
  obtain ⟨ph_, hph⟩ : ∃ ph_ : Fin h → (KaehlerDifferential k A →ₗ[A] A),
      ∀ i j, ph_ i (chooseBasis A (KaehlerDifferential k A) j)
        = surjInv hsurj (ps_ i $ 1 ⊗ₜ[A]
            (chooseBasis A (KaehlerDifferential k A) j)) :=
    ⟨fun i => (chooseBasis A $ KaehlerDifferential k A).constr A
        (fun j => surjInv hsurj $ ps_ i $ 1 ⊗ₜ[A]
          (chooseBasis A (KaehlerDifferential k A) j)),
      fun i j => by simp⟩
  have hres : ∀ i om_,
      algebraMap A (m14 A) (ph_ i om_)
        = ps_ i (1 ⊗ₜ[A] om_) := by
    intro i
    have hmaps : (linearMap A $ m14 A).comp (ph_ i)
        = ((ps_ i).restrictScalars A).comp
            (TensorProduct.mk A (m14 A) (KaehlerDifferential k A) 1) := by
      refine (chooseBasis A $ KaehlerDifferential k A).ext fun j => ?_
      simp only [LinearMap.comp_apply, linearMap_apply, hph, surjInv_eq hsurj,
        coe_restrictScalars, TensorProduct.mk_apply]
    intro om_
    have hh := LinearMap.congr_fun hmaps om_
    simpa using hh
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin h) (Fin h) A,
      M = m53 fun i j => ph_ i $ m13 k A $ y j := ⟨_, rfl⟩
  have hMapp : ∀ a b, M a b = ph_ a (m13 k A $ y b) := by simp_all
  have hMres : ∀ a b, algebraMap A (m14 A) (M a b)
      = if a = b then 1 else 0 := by
    intro a b
    rw [hMapp, hres a, hps' a b]
  have hmapM : M.map (algebraMap A $ m14 A) = 1 := by
    ext a b
    rw [Matrix.map_apply, hMres, one_apply]
  have hdet : IsUnit M.det := by
    by_contra hcon
    have hzero : algebraMap A (m14 A) M.det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr $ le_maximalIdeal (fun hq => hcon $ mp_ span_singleton_eq_top hq) $ mem_span_singleton_self _
    rw [map_det, mapMatrix_apply, hmapM, det_one] at hzero
    exact one_ne_zero hzero
  have hinvMul := nonsing_inv_mul M hdet
  refine ⟨h, y, fun i => (∑ l : Fin h, (M⁻¹ i l) • ph_ l).compDer $ m13 k A,
    hspan, ?_⟩
  intro i j
  have hsum : (∑ l : Fin h, M⁻¹ i l * M l j) = if i = j then 1 else 0 := by
    rw [← Matrix.mul_apply, hinvMul, Matrix.one_apply]
  dsimp
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  calc (∑ l : Fin h, M⁻¹ i l * ph_ l (m13 k A $ y j))
      = ∑ l : Fin h, M⁻¹ i l * M l j := by
        refine sum_congr rfl ?_
        intro l _
        rw [hMapp]
    _ = if i = j then 1 else 0 := hsum

end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

open MvPolynomial

section

variable (k : Type) [CommRing k] (ι ka_ : Type)

noncomputable def sumEvalIter :
    MvPolynomial (ι ⊕ ka_) k →ₐ[k] MvPolynomial ka_ (MvPolynomial ι k) :=
  aeval $ elim (fun i : ι => (C (X i) : MvPolynomial ka_ $ MvPolynomial ι k))
    (fun j : ka_ => (X j : MvPolynomial ka_ $ MvPolynomial ι k))

@[reducible] noncomputable def sumEvalIterAlgebra :
    Algebra (MvPolynomial (ι ⊕ ka_) k) $ MvPolynomial ka_ $ MvPolynomial ι k :=
  (sumEvalIter k ι ka_).toRingHom.toAlgebra

end

section

variable (k : Type) [CommRing k] (ι ka_ : Type)

noncomputable def iterToSumRingHom :
    MvPolynomial ka_ (MvPolynomial ι k) →+* MvPolynomial (ι ⊕ ka_) k :=
  eval₂Hom (eval₂Hom (C : k →+* MvPolynomial (ι ⊕ ka_) k)
      (fun i : ι => (X (Sum.inl i) : MvPolynomial (ι ⊕ ka_) k)))
    (fun j : ka_ => (X (Sum.inr j) : MvPolynomial (ι ⊕ ka_) k))

theorem iterToSumHom_C_C a :
    iterToSumRingHom k ι ka_ (C $ C a) = C a := by
  simp [iterToSumRingHom]

theorem iterToSumHom_C_X i :
    iterToSumRingHom k ι ka_ (C $ X i) = X (Sum.inl i) := by
  simp [iterToSumRingHom]

theorem iterToSumHom_X j :
    iterToSumRingHom k ι ka_ (X j) = X (Sum.inr j) := by
  simp [iterToSumRingHom]

theorem sumEvalIter_C a :
    sumEvalIter k ι ka_ (C a) = C (C a) :=by simp_all
theorem sumEvalIter_X_inl i :
    sumEvalIter k ι ka_ (X $ Sum.inl i) = C (X i) := by
  simp [sumEvalIter]

theorem sumEvalIter_X_inr j :
    sumEvalIter k ι ka_ (X $ Sum.inr j) = X j := by
  simp [sumEvalIter]

theorem iterToSumHom_sumEvalIter p :
    iterToSumRingHom k ι ka_ (sumEvalIter k ι ka_ p) = p := by
  induction p using induction_on
  next a => rw [sumEvalIter_C, iterToSumHom_C_C]
  next q r hq hr => simp [map_add, hq, hr]
  next q v hq =>
    rcases v with i | j
    simp [map_mul, hq, sumEvalIter_X_inl, iterToSumHom_C_X]
    simp [map_mul, hq, sumEvalIter_X_inr, iterToSumHom_X]

theorem sumEvalIter_iterToSumHom_C r :
    sumEvalIter k ι ka_ (iterToSumRingHom k ι ka_ $ C r) = C r := by
  induction r using induction_on
  next a => rw [iterToSumHom_C_C, sumEvalIter_C]
  next p q hp hq => simp [map_add, hp, hq]
  next p i hp => simp [map_mul, hp, iterToSumHom_C_X, sumEvalIter_X_inl]

theorem sumEvalIter_iterToSumHom q :
    sumEvalIter k ι ka_ (iterToSumRingHom k ι ka_ q) = q := by
  induction q using induction_on
  next r => exact sumEvalIter_iterToSumHom_C k ι ka_ r
  next p p' hp hp' => simp [map_add, hp, hp']
  next p j hp => simp [map_mul, hp, iterToSumHom_X, sumEvalIter_X_inr]

attribute [local instance] sumEvalIterAlgebra

theorem formallyEtale_sumEvalIter :
    FormallyEtale (MvPolynomial (ι ⊕ ka_) k) $ MvPolynomial ka_ $ MvPolynomial ι k := by
  refine Algebra.FormallyEtale.of_equiv
    (ofBijective
      (ofId (MvPolynomial (ι ⊕ ka_) k) $ MvPolynomial ka_ $ MvPolynomial ι k) ?_)
  constructor
  exact Function.LeftInverse.injective $ iterToSumHom_sumEvalIter k ι ka_
  exact fun q => ⟨iterToSumRingHom k ι ka_ q, sumEvalIter_iterToSumHom k ι ka_ q⟩

end

section

variable (k : Type) [CommRing k] (ι ka_ S : Type) [CommRing S]
  [Algebra (MvPolynomial ι k) S]

@[reducible] noncomputable def mapCoeffAlgebra :
    Algebra (MvPolynomial ka_ $ MvPolynomial ι k) $ MvPolynomial ka_ S :=
  (MvPolynomial.map $ algebraMap (MvPolynomial ι k) S).toAlgebra

attribute [local instance] mapCoeffAlgebra

theorem algebraMap_eq_mvPolynomial_map p :
    algebraMap (MvPolynomial ka_ $ MvPolynomial ι k) (MvPolynomial ka_ S) p
      = MvPolynomial.map (algebraMap (MvPolynomial ι k) S) p := rfl

end

section

theorem formallyEtale_mvPolynomial_map (R : Type) [CommRing R] (A : Type) [CommRing A]
    [Algebra R A] [FormallyEtale R A] (σ : Type) :
    @FormallyEtale (MvPolynomial σ R) (MvPolynomial σ A) _ _
      (toAlgebra $ MvPolynomial.map $ algebraMap R A) := by
  let : Algebra (MvPolynomial σ R) $ MvPolynomial σ A :=
    toAlgebra $ m45 $ algebraMap R A
  let _a0 := TensorProduct R (MvPolynomial σ R) A
  have : FormallyEtale (MvPolynomial σ R)
      _a0 := inferInstance
  have e :=
    ofRingEquiv
      (f := (comm R (MvPolynomial σ R) A).toRingEquiv.trans
        (algebraTensorAlgEquiv R A).toRingEquiv)
      (fun p => by
        have hp : algebraMap (MvPolynomial σ R) _a0 p
            = p ⊗ₜ[R] 1 := rfl
        have hq : algebraMap (MvPolynomial σ R) (MvPolynomial σ A) p
            = m45 (algebraMap R A) p := rfl
        rw [hp, hq]
        simp)
  exact Algebra.FormallyEtale.of_equiv e

end

section

variable (k : Type) [CommRing k] (ι ka_ S : Type) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]

noncomputable def sumEval : MvPolynomial (ι ⊕ ka_) k →ₐ[k] MvPolynomial ka_ S :=
  aeval $ elim (fun i : ι => (C (coord k ι S i) : MvPolynomial ka_ S))
    (fun j : ka_ => (X j : MvPolynomial ka_ S))

@[reducible] noncomputable def sumEvalAlgebra :
    Algebra (MvPolynomial (ι ⊕ ka_) k) $ MvPolynomial ka_ S :=
  (sumEval k ι ka_ S).toRingHom.toAlgebra

attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra

theorem sumEvalAlgebra_isScalarTower :
    IsScalarTower k (MvPolynomial (ι ⊕ ka_) k) $ MvPolynomial ka_ S :=
  of_algebraMap_eq fun x => sy_ $ (sumEval k ι ka_ S).commutes x

theorem algebraMap_eq_sumEval p :
    algebraMap (MvPolynomial (ι ⊕ ka_) k) (MvPolynomial ka_ S) p = sumEval k ι ka_ S p := rfl

@[simp] theorem algebraMap_X_inl (i : ι) :
    algebraMap (MvPolynomial (ι ⊕ ka_) k) (MvPolynomial ka_ S) (X (Sum.inl i))
      = C (coord k ι S i) := by
  simp [algebraMap_eq_sumEval, sumEval]

@[simp] theorem algebraMap_X_inr (j : ka_) :
    algebraMap (MvPolynomial (ι ⊕ ka_) k) (MvPolynomial ka_ S) (X (Sum.inr j))
      = (X j : MvPolynomial ka_ S) := by
  simp [algebraMap_eq_sumEval, sumEval]

@[simp] theorem coord_inl (i : ι) :
    coord k (ι ⊕ ka_) (MvPolynomial ka_ S) (Sum.inl i) = C (coord k ι S i) :=
  (coord_def k (ι ⊕ ka_) (MvPolynomial ka_ S) (m44 i)).trans (algebraMap_X_inl k ι ka_ S i)

@[simp] theorem coord_inr (j : ka_) :
    coord k (ι ⊕ ka_) (MvPolynomial ka_ S) (Sum.inr j) = (X j : MvPolynomial ka_ S) :=
  (coord_def k (ι ⊕ ka_) (MvPolynomial ka_ S) (m50 j)).trans (algebraMap_X_inr k ι ka_ S j)

theorem algebraMap_eq_sumEvalIter p :
    algebraMap (MvPolynomial (ι ⊕ ka_) k) (MvPolynomial ka_ $ MvPolynomial ι k) p
      = sumEvalIter k ι ka_ p := rfl

section
variable [IsScalarTower k (MvPolynomial ι k) S]
theorem mapCoeffAlgebra_isScalarTower_of_isScalarTower :
    IsScalarTower k (MvPolynomial ka_ $ MvPolynomial ι k) $ MvPolynomial ka_ S :=
  of_algebraMap_eq fun x => by
    have h1 : algebraMap k (MvPolynomial ka_ $ MvPolynomial ι k) x
        = C (algebraMap k (MvPolynomial ι k) x) := rfl
    have h2 : algebraMap k (MvPolynomial ka_ S) x = C (algebraMap k S x) := rfl
    rw [h2, h1, algebraMap_eq_mvPolynomial_map, map_C,
      algebraMap_apply k (MvPolynomial ι k) S]

theorem mapCoeffAlgebra_isScalarTower :
    IsScalarTower (MvPolynomial (ι ⊕ ka_) k) (MvPolynomial ka_ $ MvPolynomial ι k)
      (MvPolynomial ka_ S) := by
  have := mapCoeffAlgebra_isScalarTower_of_isScalarTower k ι ka_ S
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine ringHom_ext (fun r => ?_) fun v => ?_
  simp [algebraMap_eq_sumEval, m82, algebraMap_eq_sumEvalIter,
    sumEval, sumEvalIter, aeval_C]
  exact algebraMap_apply k (MvPolynomial ka_ $ MvPolynomial ι k) (MvPolynomial ka_ S) r
  rcases v with i | j <;>
    simp [m82, algebraMap_eq_sumEval, algebraMap_eq_sumEvalIter,
      sumEval, sumEvalIter, algebraMap_eq_mvPolynomial_map, coord_def]

theorem formallyEtale_mvPolynomial_sum
    [FormallyEtale (MvPolynomial ι k) S] :
    FormallyEtale (MvPolynomial (ι ⊕ ka_) k) $ MvPolynomial ka_ S := by
  have := mapCoeffAlgebra_isScalarTower_of_isScalarTower k ι ka_ S
  have := mapCoeffAlgebra_isScalarTower k ι ka_ S
  have h1 := formallyEtale_sumEvalIter k ι ka_
  let _a0 := MvPolynomial ι k
  have h2 :=
    formallyEtale_mvPolynomial_map _a0 S ka_
  exact comp (MvPolynomial (ι ⊕ ka_) k) (MvPolynomial ka_ _a0)
    (MvPolynomial ka_ S)
end

variable (T : Type) [CommRing T]

theorem formallyEtale_trans [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra (MvPolynomial ka_ S) T] [Algebra (MvPolynomial (ι ⊕ ka_) k) T]
    [IsScalarTower (MvPolynomial (ι ⊕ ka_) k) (MvPolynomial ka_ S) T]
    [FormallyEtale (MvPolynomial ι k) S]
    [FormallyEtale (MvPolynomial ka_ S) T] :
    FormallyEtale (MvPolynomial (ι ⊕ ka_) k) T := by
  have := formallyEtale_mvPolynomial_sum k ι ka_ S
  exact comp (MvPolynomial (ι ⊕ ka_) k) (MvPolynomial ka_ S) T

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

namespace SmoothEtaleChart

theorem exists_etale_mvPolynomial_ulift {R S : Type} [CommRing R] [CommRing S] {n : ℕ}
    (g : MvPolynomial (Fin n) R →+* S) (hg : g.Etale) (f : R →+* S)
    (hf : g.comp MvPolynomial.C = f) :
    ∃ g' : MvU n R →+* S,
      g'.comp MvPolynomial.C = f ∧ g'.Etale := by
  set E : MvU n R ≃+* MvPolynomial (Fin n) R :=
    (renameEquiv R Equiv.ulift).toRingEquiv with hE
  refine ⟨g.comp E.toRingHom, ?_, RingHom.Etale.respectsIso.right g E hg⟩
  refine m48 fun a => ?_
  have h1 : E (m8 a) = m8 a := by
    simp [hE]
  have h2 : g (m8 a) = f a := by rw [← hf]
                                 rfl
  simp [coe_comp, comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h1, h2]

theorem exists_etale_over_affineSpace_of_isStandardSmooth {R S : CRC}
    (ph_ : R ⟶ S) (hph : IsStandardSmooth $ CommRingCat.Hom.hom ph_) :
    ∃ (d : ℕ) (g : Spec S ⟶ AffineSpace (UFin d) (Spec R)),
      Etale g ∧
        g ≫ (AffineSpace (UFin d) (Spec R) ↘ Spec R) = Spec.map ph_ := by
  obtain ⟨n, gr, hgrC, hgrEt⟩ := hph.exists_etale_mvPolynomial
  obtain ⟨g', hg'C, hg'Et⟩ := exists_etale_mvPolynomial_ulift gr hgrEt _ hgrC
  let _a0 := m12 $ ofHom g'
  have hSpecEt : Etale _a0 := by
    rwa [HasRingHomProperty.Spec_iff (P := @Etale)]
  refine ⟨n, _a0 ≫
      (m69 (UFin n) R).inv, inferInstance, ?_⟩
  rw [assoc, AffineSpace.SpecIso_inv_over, ← m183]
  exact congrArg m12 $ CommRingCat.hom_ext hg'C

section
variable {X Y : Sch} (h : Y ⟶ X)
section
variable {W : Opn X} {V : Opn Y} (hW : IsAffineOpen W) (hV : IsAffineOpen V) (e : V ≤ h.pre W)
include hW hV
theorem exists_etale_over_affineSpace_resLE_of_isStandardSmooth
    (hstd : IsStandardSmooth $ CommRingCat.Hom.hom $ appLE h W V e) :
    ∃ (d : ℕ) (g : V.toScheme ⟶ AffineSpace (UFin d) W.toScheme),
      Etale g ∧
        g ≫ (AffineSpace (UFin d) W.toScheme ↘ W.toScheme) = h.resLE W V e := by
  obtain ⟨d, g0_, hg0et, hg0_⟩ :=
    exists_etale_over_affineSpace_of_isStandardSmooth (appLE h W V e) hstd
  let _s0 := UFin d
  let _a0 := m228 _s0 hW.isoSpec.inv
  have : IsIso _a0 :=
    ⟨⟨m228 _s0 hW.isoSpec.hom, by
        rw [← AffineSpace.map_comp, m114, AffineSpace.map_id], by
        rw [← AffineSpace.map_comp, m145, AffineSpace.map_id]⟩⟩
  have : Etale hV.isoSpec.hom := inferInstance
  have : Etale _a0 := inferInstance
  refine ⟨d, hV.isoSpec.hom ≫ g0_ ≫ _a0,
    inferInstance, ?_⟩
  rw [assoc, assoc, AffineSpace.map_over, ← assoc g0_, hg0_, ← cancel_mono W.i, q4]
  simp only [assoc]
  rw [hW.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec h hW hV e, ← hV.isoSpec_inv_ι]
  simp
end

section
variable [Smooth h]
private theorem smooth_resLE (W : Opn X)
    (V : Opn Y) (e : V ≤ h.pre W) : Smooth $ h.resLE W V e := by
  rw [HasRingHomProperty.iff_appLE (P := @Smooth)]
  intro U U' e'
  rw [resLE_appLE]
  exact HasRingHomProperty.appLE @Smooth h ‹Smooth h›
    ⟨opI W ''ᵁ U.1, U.2.image_of_isOpenImmersion _⟩
    ⟨opI V ''ᵁ U'.1, U'.2.image_of_isOpenImmersion _⟩ _

section
variable (y : Y) (W0 : Opn X) (hW0 : h.base y ∈ W0) (V0 : Opn Y) (hV0 : y ∈ V0)
include hW0 hV0
theorem exists_isAffineOpen_etale_resLE_le :
    ∃ W V d e,
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W0 ∧ V ≤ V0 ∧
      ∃ g : V.toScheme ⟶ AffineSpace (UFin d) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (UFin d) W.toScheme ↘ W.toScheme) = h.resLE W V e :=
  by
    let _a0 := V0 ⊓ preU h W0
    have e0_ : _a0 ≤ preU h W0 := inf_le_right
    have hy' : y ∈ _a0 := ⟨hV0, hW0⟩
    let _a1 := h.resLE W0 (V0 ⊓ preU h W0) e0_
    obtain ⟨W', hW', V', hV', hyV', e', hstd⟩ :=
      Smooth.exists_isStandardSmooth _a1 ⟨y, hy'⟩
    have h1 : _a1 ≫ opI W0 = opI _a0 ≫ h := by
      rw [q4]
    have hb : ∀ z : ↥_a0,
        bsM h (opIb _a0 z)
          = opIb W0 (bsM _a1 z) := by
      intro z
      exact sy_ $ congrArg (fun m : oSch _a0 ⟶ X => bsM m z) h1
    have hWle : (W0.i.im W') ≤ W0 := by
      rintro x ⟨z, -, rfl⟩
      exact z.2
    let _s0 := _a0.i.im V'
    have hVle : _s0 ≤ V0 := by
      rintro x ⟨z, -, rfl⟩
      exact z.2.1
    have e : _s0 ≤ preU h (opI W0 ''ᵁ W') := by
      rintro x ⟨z, hz, rfl⟩
      exact ⟨bsM _a1 z, e' hz, sy_ $ hb z⟩
    have hWaff := hW'.image_of_isOpenImmersion W0.i
    have hVaff : IsAffineOpen _s0 :=
      hV'.image_of_isOpenImmersion _
    rw [resLE_appLE h e0_ W' V' e'] at hstd
    obtain ⟨d, g, hg, hgpi⟩ := exists_etale_over_affineSpace_resLE_of_isStandardSmooth h hWaff hVaff e hstd
    exact ⟨W0.i.im W', _a0.i.im V', d, e, hWaff, hVaff,
      ⟨⟨y, hy'⟩, hyV', rfl⟩, hWle, hVle, g, hg, hgpi⟩
end
end
end

end SmoothEtaleChart

namespace EtaleCoordinates

section
variable (k : Type) [CommRing k]
section
variable (S : Type) [CommRing S] (T : Type) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
section
variable (D : Derivation k T T)
def derivationCompAlgebraMap :
    Derivation k S T :=
  mk' (D.toLinearMap.comp (toAlgHom k S T).toLinearMap) $ by
    intro a b
    show D (algebraMap S T $ a * b) = a • D (algebraMap S T b) + b • D (algebraMap S T a)
    rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, smul_def, smul_def]

theorem derivation_comp_algebraMap_apply s :
    derivationCompAlgebraMap k S T D s = D (algebraMap S T s) := rfl
end

section
variable (D : Derivation k S S)
def algebraMapCompDerivation :
    Derivation k S T :=
  mk' ((toAlgHom k S T).toLinearMap.comp D.toLinearMap) $ by
    intro a b
    show algebraMap S T (D $ a * b) = a • algebraMap S T (D b) + b • algebraMap S T (D a)
    rw [D.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, smul_def,
      smul_def]

theorem algebraMap_comp_derivation_apply s :
    algebraMapCompDerivation k S T D s = algebraMap S T (D s) := rfl
end
end

section
variable (ι : Type)
theorem derivation_ext_of_coord (S : Type) [CommRing S]
    [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
    [FormallyEtale (MvPolynomial ι k) S]
    (M : Type) [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (D1 D2_ : Derivation k S M)
    (h : ∀ i : ι, D1 (coord k ι S i) = D2_ (coord k ι S i)) : D1 = D2_ := by
  have key : D1.liftKaehlerDifferential = D2_.liftKaehlerDifferential := by
    refine (basisKaehler k ι S).ext ?_
    intro i
    rw [basisKaehler_apply, liftKaehlerDifferential_comp_D,
      liftKaehlerDifferential_comp_D]
    exact h i
  refine Derivation.ext fun x => ?_
  rw [← liftKaehlerDifferential_comp_D D1 x,
    ← liftKaehlerDifferential_comp_D D2_ x, key]

section
variable (ka_ : Type)
theorem partialDeriv_inl_algebraMap
    [DecidableEq ι] [DecidableEq ka_]
    (S : Type) [CommRing S] (T : Type) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ ka_) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ ka_) k) T]
    [FormallyEtale (MvPolynomial (ι ⊕ ka_) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ ka_) T (Sum.inl i))
    i s :
    partialDeriv k (ι ⊕ ka_) T (Sum.inl i) (algebraMap S T s)
      = algebraMap S T (partialDeriv k ι S i s) := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ ka_) T $ m44 i)
      = algebraMapCompDerivation k S T (partialDeriv k ι S i) := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro j
    rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply, hcoord j]
    by_cases hij : i = j
    simp_all
    simp_all
  have h2 := congr_fun key s
  rwa [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply] at h2

theorem map_derivIdeal_sum
    [Fintype ι] [Fintype ka_] [DecidableEq ι] [DecidableEq ka_]
    (S : Type) [CommRing S] (T : Type) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ ka_) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ ka_) k) T]
    [FormallyEtale (MvPolynomial (ι ⊕ ka_) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ ka_) T (Sum.inl i))
    J :
    Ideal.map (algebraMap S T) (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S T) J) := by
  let _a0 := algebraMap S T
  have key1 : ∀ (D : Derivation k S S) (y : S), y ∈ J →
      algebraMap S T (D y) ∈ derivIdeal k (m6 _a0 J) := by
    intro D y hy
    have hsp : D ∈ Submodule.span S (Set.range $ partialDeriv k ι S) := by
      rw [span_range_partialDeriv]
      exact mem_top
    induction hsp using span_induction with
    | mem D hD =>
        obtain ⟨i, rfl⟩ := hD
        rw [← partialDeriv_inl_algebraMap k ι ka_ S T hcoord i y]
        exact derivation_apply_mem_derivIdeal k _ _ $ mem_map_of_mem _ hy
    | zero =>
        have h0 : (0 : Derivation k S S) y = 0 := rfl
        rw [h0, map_zero]
        exact m97 _
    | add a b _ _ ha hb =>
        have h0 : (a + b) y = a y + b y := rfl
        rw [h0, map_add]
        exact m128 _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) y = c * a y := rfl
        rw [h0, map_mul]
        exact mul_mem_left _ _ ha
  have key2 : ∀ (D' : Derivation k T T) (y : S), y ∈ J →
      D' (algebraMap S T y) ∈ m6 _a0 (derivIdeal k J) := by
    intro D' y hy
    have hsp : D' ∈ Submodule.span T (Set.range $ partialDeriv k (ι ⊕ ka_) T) := by
      rw [span_range_partialDeriv]
      exact mem_top
    induction hsp using span_induction with
    | mem D hD =>
        obtain ⟨x, rfl⟩ := hD
        cases x with
        | inl i =>
            rw [partialDeriv_inl_algebraMap k ι ka_ S T hcoord i y]
            exact mem_map_of_mem _
              (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) hy)
        | inr j =>
            have _i53 : partialDeriv k (ι ⊕ ka_) T (m50 j) (algebraMap S T y) = 0 := by
              let _a0 := (0 : Derivation k S T)
              have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ ka_) T $ m50 j) = 0 := by
                refine derivation_ext_of_coord k ι S T _ _ ?_
                intro i
                rw [derivation_comp_algebraMap_apply, hcoord i,
                  partialDeriv_coord_of_ne k (ι ⊕ ka_) T (m50 j) (m44 i) $ by simp]
                have h0 : _a0 (coord k ι S i) = 0 := rfl
                rw [h0]
              have h2 := congr_fun key y
              rw [derivation_comp_algebraMap_apply] at h2
              have h0 : _a0 y = 0 := rfl
              rwa [h0] at h2
            rw [_i53]
            exact m97 _
    | zero =>
        have h0 : (0 : Derivation k T T) (algebraMap S T y) = 0 := rfl
        rw [h0]
        exact m97 _
    | add a b _ _ ha hb =>
        have h0 : (a + b) (algebraMap S T y)
            = a (algebraMap S T y) + b (algebraMap S T y) := rfl
        rw [h0]
        exact m128 _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) (algebraMap S T y) = c * a (algebraMap S T y) := rfl
        rw [h0]
        exact mul_mem_left _ _ ha
  refine le_antisymm ?_ ?_
  rw [map_le_iff_le_comap, derivIdeal_le_iff]
  refine ⟨fun y hy => Ideal.mem_comap.mpr $ le_derivIdeal k _ $ mem_map_of_mem _ hy, ?_⟩
  intro D y hy
  exact Ideal.mem_comap.mpr $ key1 D y hy
  rw [derivIdeal_le_iff]
  refine ⟨map_mono $ le_derivIdeal k J, ?_⟩
  intro D' z hz
  have hspan : Ideal.map _a0 J
      = Ideal.span (_a0 '' (J : Set S)) := by
    rw [← map_span, span_eq]
  rw [hspan] at hz
  refine derivation_apply_mem_of_mem_span D' ?_ ?_ hz
  rw [← hspan]
  exact map_mono $ le_derivIdeal k J
  rintro g ⟨y, hy, rfl⟩
  exact key2 D' y hy
end
end
end

end EtaleCoordinates
namespace DerivIdealBaseChange

open FunctorialResolution.EmbeddedResolution.EtaleCoordinates

theorem apply_mem_of_forall_partialDeriv_mem {k : Type} [CommRing k] {ι : Type} [Finite ι]
    {S : Type} [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]
    (X : Set S) (K : Ideal S)
    (h : ∀ i : ι, ∀ x ∈ X, partialDeriv k ι S i x ∈ K)
    (D : Derivation k S S) {x : S} (hx : x ∈ X) : D x ∈ K := by
  classical
  let _a0 := Derivation k S S
  let N : Submodule S _a0 :=
    { carrier := {D : _a0 | ∀ y ∈ X, D y ∈ K}
      add_mem' := by
        intro a b ha hb
        intro y hy
        have hab : (a + b) y = a y + b y := rfl
        rw [hab]
        exact m128 K (ha y hy) $ hb y hy
      zero_mem' := by
        intro y _
        have h0 : (0 : _a0) y = 0 := rfl
        rw [h0]
        exact m216 K
      smul_mem' := by
        intro c a ha
        intro y hy
        have hc : (c • a) y = c * a y := rfl
        rw [hc]
        exact mul_mem_left K _ $ ha y hy }
  have hspan : (⊤) ≤ N := by
    rw [← span_range_partialDeriv k ι S, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  exact (hspan mem_top) x hx

section

variable (k : Type) [CommRing k] (L : Type) [CommRing L] [Algebra k L]
  (ι : Type) [DecidableEq ι]
  (S : Type) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]
  (S' : Type) [CommRing S'] [Algebra L S'] [Algebra (MvPolynomial ι L) S']
  [IsScalarTower L (MvPolynomial ι L) S'] [FormallyEtale (MvPolynomial ι L) S']
  [Algebra k S'] [IsScalarTower k L S']

section
variable (ph_ : S →ₐ[k] S') (hph : ∀ i : ι, ph_ (coord k ι S i) = coord L ι S' i) (i : ι)
include hph
theorem partialDeriv_algHom_apply (f : S) :
    partialDeriv L ι S' i (ph_ f) = ph_ (partialDeriv k ι S i f) := by
  let _ := ph_.toRingHom.toAlgebra
  have hsmul : ∀ (s : S) (x : S'), s • x = ph_ s * x := fun _ _ => rfl
  have hphsmul : ∀ (c : k) (x : S), ph_ (c • x) = c • ph_ x := by simp_all
  have hcomp : ∀ (c : k) (y : S'), c • y = (algebraMap k L c) • y := by simp_all
  have hadd1 : ∀ x y : S', partialDeriv L ι S' i (x + y)
      = partialDeriv L ι S' i x + partialDeriv L ι S' i y :=
    fun x y => (partialDeriv L ι S' i).toLinearMap.map_add x y
  have hadd2 : ∀ x y : S, partialDeriv k ι S i (x + y)
      = partialDeriv k ι S i x + partialDeriv k ι S i y :=
    fun x y => (partialDeriv k ι S i).toLinearMap.map_add x y
  have hsm1 : ∀ c y, partialDeriv L ι S' i (c • y) = c • partialDeriv L ι S' i y :=
    fun c y => (partialDeriv L ι S' i).toLinearMap.map_smul c y
  have hsm2 : ∀ c x, partialDeriv k ι S i (c • x) = c • partialDeriv k ι S i x :=
    fun c x => (partialDeriv k ι S i).toLinearMap.map_smul c x
  have hpsmul : ∀ (c : k) (y : S'),
      partialDeriv L ι S' i (c • y) = c • partialDeriv L ι S' i y := by
    intro c y
    rw [hcomp c y, hsm1, ← hcomp]
  let F1 : S →ₗ[k] S' :=
    { toFun := fun s => partialDeriv L ι S' i (ph_ s)
      map_add' := by
        intro x y
        show partialDeriv L ι S' i (ph_ $ x + y)
            = partialDeriv L ι S' i (ph_ x) + partialDeriv L ι S' i (ph_ y)
        rw [map_add, hadd1]
      map_smul' := by
        intro c x
        show partialDeriv L ι S' i (ph_ $ c • x) = c • partialDeriv L ι S' i (ph_ x)
        rw [hphsmul, hpsmul] }
  let F2 : S →ₗ[k] S' :=
    { toFun := fun s => ph_ (partialDeriv k ι S i s)
      map_add' := by
        intro x y
        show ph_ (partialDeriv k ι S i $ x + y)
            = ph_ (partialDeriv k ι S i x) + ph_ (partialDeriv k ι S i y)
        rw [hadd2, map_add]
      map_smul' := by
        intro c x
        show ph_ (partialDeriv k ι S i $ c • x) = c • ph_ (partialDeriv k ι S i x)
        rw [hsm2, hphsmul] }
  let D1 := mk' F1 $ by
    intro a b
    show partialDeriv L ι S' i (ph_ $ a * b)
        = a • partialDeriv L ι S' i (ph_ b) + b • partialDeriv L ι S' i (ph_ a)
    rw [map_mul, (partialDeriv L ι S' i).leibniz]
    simp [hsmul, smul_eq_mul]
  let D2_ := mk' F2 $ by
    intro a b
    show ph_ (partialDeriv k ι S i $ a * b)
        = a • ph_ (partialDeriv k ι S i b) + b • ph_ (partialDeriv k ι S i a)
    rw [(partialDeriv k ι S i).leibniz]
    simp [hsmul, smul_eq_mul, map_add, map_mul]
  have hcoords : ∀ j : ι, D1 (coord k ι S j) = D2_ (coord k ι S j) := by
    intro j
    show partialDeriv L ι S' i (ph_ $ coord k ι S j) = ph_ (partialDeriv k ι S i $ coord k ι S j)
    rw [hph j, partialDeriv_coord, partialDeriv_coord]
    split_ifs with hij
    simp_all
    simp_all
  exact congr_fun (derivation_ext_of_coord k ι S S' D1 D2_ hcoords) f

end

section
variable [hv0_0 : Fintype ι] (ph_ : S →ₐ[k] S') (hph : ∀ i : ι, ph_ (coord k ι S i) = coord L ι S' i) (J : Ideal S)
include hv0_0 hph
theorem map_derivIdeal_le :
    Ideal.map ph_ (derivIdeal k J) ≤ derivIdeal L (Ideal.map ph_ J) := by
  let _a0 := m6 ph_ J
  rw [map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  intro y hy
  rw [mem_comap]
  exact le_derivIdeal L _a0 $ mem_map_of_mem ph_ hy
  intro D x hx
  refine apply_mem_of_forall_partialDeriv_mem (ι := ι) J
    (m119 ph_ $ derivIdeal L _a0) ?_ D (hx)
  intro i y hy
  rw [mem_comap,
    ← partialDeriv_algHom_apply (k := k) (L := L) (ι := ι) (S := S) (S' := S') ph_ hph i y]
  exact derivation_apply_mem_derivIdeal L _a0 (partialDeriv L ι S' i)
    (mem_map_of_mem ph_ (hy))

theorem derivIdeal_map_le :
    derivIdeal L (Ideal.map ph_ J) ≤ Ideal.map ph_ (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨map_mono $ le_derivIdeal k J, ?_⟩
  intro D g hg
  let _a1 := derivIdeal k J
  refine apply_mem_of_forall_partialDeriv_mem (ι := ι) ((m6 ph_ J) : Set S')
    (m6 ph_ _a1) ?_ D
    (hg)
  intro i y hy
  let _c0 := ⇑ph_ '' J
  have hle : m6 ph_ J ≤ m17 _c0 := by
    rw [map_le_iff_le_comap]
    intro y hy
    rw [mem_comap]
    exact m100 ⟨y, hy, rfl⟩
  have hGT : m17 _c0 ≤ (m6 ph_ _a1) := by
    rw [span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact mem_map_of_mem ph_ $ le_derivIdeal k J (hy)
  refine derivation_apply_mem_of_mem_span (partialDeriv L ι S' i) hGT ?_ $ hle hy
  rintro _ ⟨y, hy, rfl⟩
  rw [partialDeriv_algHom_apply (k := k) (L := L) (ι := ι) (S := S) (S' := S') ph_ hph i y]
  exact mem_map_of_mem ph_
    (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) (hy))

theorem map_derivIdeal :
    Ideal.map ph_ (derivIdeal k J) = derivIdeal L (Ideal.map ph_ J) :=
  le_antisymm
    (map_derivIdeal_le (k := k) (L := L) (ι := ι) (S := S) (S' := S') ph_ hph J)
    (derivIdeal_map_le (k := k) (L := L) (ι := ι) (S := S) (S' := S') ph_ hph J)
end

end

end DerivIdealBaseChange
namespace EtaleCoordinates

variable (k : Type) [CommRing k] (ι : Type) [DecidableEq ι]
  (S : Type) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]
  (S1_ : Type) [CommRing S1_] [Algebra k S1_] [Algebra (MvPolynomial ι k) S1_]
  [IsScalarTower k (MvPolynomial ι k) S1_] [FormallyEtale (MvPolynomial ι k) S1_]
  (ph_ : S →ₐ[k] S1_) (T : Finset ι) (s : ι)

section
variable (hin : ∀ i ∈ T, i ≠ s → ph_ (coord k ι S i) = coord k ι S1_ i * coord k ι S1_ s) (hs : ph_ (coord k ι S s) = coord k ι S1_ s) (hout : ∀ i ∉ T, ph_ (coord k ι S i) = coord k ι S1_ i)
include hin hs hout
theorem partialDeriv_map_of_mem
    i (hiT : i ∈ T) (his : i ≠ s) f :
    partialDeriv k ι S1_ i (ph_ f)
      = coord k ι S1_ s * ph_ (partialDeriv k ι S i f) := by
  let _ := ph_.toRingHom.toAlgebra
  have : IsScalarTower k S S1_ := by
    refine of_algebraMap_eq fun x => ?_
    show algebraMap k S1_ x = ph_ (algebraMap k S x)
    exact sy_ $ ph_.commutes x
  have hsmul : ∀ a z, a • z = ph_ a * z := fun _ _ => rfl
  let L1_ := (partialDeriv k ι S1_ i).toLinearMap.comp ph_.toLinearMap
  let L2_ :=
    (mulLeft k $ coord k ι S1_ s).comp
      (ph_.toLinearMap.comp (partialDeriv k ι S i).toLinearMap)
  have h1_ : ∀ a b, L1_ (a * b) = a • L1_ b + b • L1_ a := by
    intro a b
    show partialDeriv k ι S1_ i (ph_ $ a * b)
        = a • partialDeriv k ι S1_ i (ph_ b) + b • partialDeriv k ι S1_ i (ph_ a)
    simp only [hsmul, map_mul, (partialDeriv k ι S1_ i).leibniz, smul_eq_mul]
  have h2_ : ∀ a b, L2_ (a * b) = a • L2_ b + b • L2_ a := by
    intro a b
    show coord k ι S1_ s * ph_ (partialDeriv k ι S i $ a * b)
        = a • (coord k ι S1_ s * ph_ (partialDeriv k ι S i b))
          + b • (coord k ι S1_ s * ph_ (partialDeriv k ι S i a))
    simp only [hsmul, (partialDeriv k ι S i).leibniz, smul_eq_mul, map_add, map_mul]
    ring
  have hD : mk' L1_ h1_ = mk' L2_ h2_ := by
    refine derivation_ext_of_coord k ι S S1_ _ _ ?_
    intro j
    show partialDeriv k ι S1_ i (ph_ $ coord k ι S j)
        = coord k ι S1_ s * ph_ (partialDeriv k ι S i $ coord k ι S j)
    by_cases hjT : j ∈ T
    by_cases hjs : j = s
    simp_all
    rw [hin j hjT hjs, (partialDeriv k ι S1_ i).leibniz]
    simp only [smul_eq_mul, partialDeriv_coord, if_neg his, mul_zero, zero_add]
    by_cases hij : i = j
    simp [hij]
    simp [hij]
    rw [hout j hjT]
    have hij : i ≠ j := by rintro rfl
                           exact hjT hiT
    simp only [partialDeriv_coord, if_neg hij, map_zero, mul_zero]
  exact congr_fun hD f

theorem map_partialDeriv_eq_pow_mul_of_mem
    (hnzd : coord k ι S1_ s ∈ nonZeroDivisors S1_)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (f : S) (g : S1_) (e : ℕ) (hfg : ph_ f = coord k ι S1_ s ^ (e + 1) * g) :
    ph_ (partialDeriv k ι S i f) = coord k ι S1_ s ^ e * partialDeriv k ι S1_ i g := by
  have h1 :=
    partialDeriv_map_of_mem k ι S S1_ ph_ T s hin hs hout i hiT his f
  rw [hfg, leibniz, leibniz_pow, partialDeriv_coord_of_ne k ι S1_ i s his, smul_zero, smul_zero, smul_zero, add_zero, smul_eq_mul] at h1
  have key : (ph_ (partialDeriv k ι S i f)
      - coord k ι S1_ s ^ e * partialDeriv k ι S1_ i g) * coord k ι S1_ s = 0 := by
    linear_combination -h1
  linear_combination ((mp_ mem_nonZeroDivisors_iff hnzd).2 _ key)

section
variable (hsT : s ∈ T)
include hsT
section
variable (i) (hiT : i ∉ T) (f : S)
include hiT
theorem map_partialDeriv_eq_pow_mul_of_notMem (g : S1_) (e : ℕ) (hfg : ph_ f = coord k ι S1_ s ^ (e + 1) * g) :
    ph_ (partialDeriv k ι S i f) = coord k ι S1_ s ^ (e + 1) * partialDeriv k ι S1_ i g := by
  have his : i ≠ s := fun h => hiT (by rw [h]; exact hsT)
  have hpow : partialDeriv k ι S1_ i (coord k ι S1_ s ^ (e + 1)) = 0 := by simp_all
  have _i54 : partialDeriv k ι S1_ i (ph_ f) = ph_ (partialDeriv k ι S i f) := by
    let _c0 := ph_.toLinearMap
    let _ := ph_.toRingHom.toAlgebra
    have halg : ∀ x, algebraMap S S1_ x = ph_ x := fun x => rfl
    have : IsScalarTower k S S1_ :=
      of_algebraMap_eq fun x => by rw [halg]
                                   exact sy_ $ ph_.commutes x
    have hsmul : ∀ a x, a • x = ph_ a * x := by
      intro a x
      rw [smul_def, halg]
    have his : i ≠ s := fun h => hiT (by rw [h]; exact hsT)
    have h1_ : ∀ a b,
        ((partialDeriv k ι S1_ i).toLinearMap.comp _c0) (a * b)
          = a • ((partialDeriv k ι S1_ i).toLinearMap.comp _c0) b
            + b • ((partialDeriv k ι S1_ i).toLinearMap.comp _c0) a := by
      intro a b
      show partialDeriv k ι S1_ i (ph_ $ a * b)
          = a • partialDeriv k ι S1_ i (ph_ b) + b • partialDeriv k ι S1_ i (ph_ a)
      rw [map_mul, leibniz]
      simp [hsmul, smul_eq_mul]
    have h2_ : ∀ a b,
        (_c0.comp (partialDeriv k ι S i).toLinearMap) (a * b)
          = a • (_c0.comp (partialDeriv k ι S i).toLinearMap) b
            + b • (_c0.comp (partialDeriv k ι S i).toLinearMap) a := by
      intro a b
      show ph_ (partialDeriv k ι S i $ a * b)
          = a • ph_ (partialDeriv k ι S i b) + b • ph_ (partialDeriv k ι S i a)
      rw [leibniz]
      simp [smul_eq_mul, map_add, map_mul, hsmul]
    have key :
        mk' ((partialDeriv k ι S1_ i).toLinearMap.comp _c0) h1_
          = mk' (_c0.comp
              (partialDeriv k ι S i).toLinearMap) h2_ := by
      refine derivation_ext_of_coord k ι S S1_ _ _ ?_
      intro j
      show partialDeriv k ι S1_ i (ph_ $ coord k ι S j) = ph_ (partialDeriv k ι S i $ coord k ι S j)
      by_cases hj : j ∈ T
      by_cases hjs : j = s
      rw [hjs, hs, partialDeriv_coord_of_ne k ι S1_ i s his,
        partialDeriv_coord_of_ne k ι S i s his, map_zero]
      have hij : i ≠ j := fun h => hiT (by rw [h]; exact hj)
      rw [hin j hj hjs, leibniz, partialDeriv_coord_of_ne k ι S1_ i s his,
        partialDeriv_coord_of_ne k ι S1_ i j hij, partialDeriv_coord_of_ne k ι S i j hij,
        smul_zero, smul_zero, add_zero, map_zero]
      rw [hout j hj, partialDeriv_coord, partialDeriv_coord]
      split_ifs with h
      simp_all
      simp_all
    exact congr_fun key f
  rw [← _i54, hfg,
    leibniz, hpow, smul_zero, add_zero, smul_eq_mul]
end

theorem map_partialDeriv_self_eq_pow_mul (hnzd : coord k ι S1_ s ∈ nonZeroDivisors S1_)
    (f : S) (g : S1_) (e : ℕ) (hfg : ph_ f = coord k ι S1_ s ^ (e + 1) * g) :
    ph_ (partialDeriv k ι S s f)
      = coord k ι S1_ s ^ e
        * (coord k ι S1_ s * partialDeriv k ι S1_ s g + ((e + 1 : ℕ) : S1_) * g
            - ∑ i ∈ T.erase s, coord k ι S1_ i * partialDeriv k ι S1_ i g) := by
  have hpow : partialDeriv k ι S1_ s (coord k ι S1_ s ^ (e + 1))
      = ((e + 1 : ℕ) : S1_) * coord k ι S1_ s ^ e := by simp_all
  have h2 : partialDeriv k ι S1_ s (ph_ f)
      = coord k ι S1_ s ^ (e + 1) * partialDeriv k ι S1_ s g
        + ((e + 1 : ℕ) : S1_) * coord k ι S1_ s ^ e * g := by
    rw [hfg, leibniz, hpow]
    simp [smul_eq_mul]
    ring
  have hsum2 : ∑ i ∈ T.erase s, ph_ (coord k ι S i * partialDeriv k ι S i f)
      = coord k ι S1_ s ^ (e + 1)
        * ∑ i ∈ T.erase s, coord k ι S1_ i * partialDeriv k ι S1_ i g := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hiT := mem_of_mem_erase hi
    have his := ne_of_mem_erase hi
    rw [map_mul, hin i hiT his,
      map_partialDeriv_eq_pow_mul_of_mem k ι S S1_ ph_ T s hin hs hout hnzd i hiT his f g e hfg]
    ring
  let _a3 := partialDeriv k ι S s f
  have h1 : coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ f)
      = coord k ι S1_ s * ph_ _a3
        + coord k ι S1_ s ^ (e + 1)
          * ∑ i ∈ T.erase s, coord k ι S1_ i * partialDeriv k ι S1_ i g := by
    have _i49 : coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ f) = ph_ (coord k ι S s * partialDeriv k ι S s f + ∑ i ∈ T.erase s, coord k ι S i * partialDeriv k ι S i f) := by
      have _i55 : coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ f) = ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i f) := by
        let _ := ph_.toRingHom.toAlgebra
        have :=
          of_algebraMap_eq fun c => sy_ $ ph_.commutes c
        have hsmul : ∀ a (z : S1_), a • z = ph_ a * z := fun a z => smul_def a z
        have hsum_add : ∀ x y,
            (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (x + y))
              = (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
                + (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i y) := by
          intro x y
          rw [← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          rw [map_add, mul_add]
        have hsum_smul : ∀ (c : k) (x : S),
            (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (c • x))
              = c • (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x) := by
          intro c x
          rw [smul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [Derivation.map_smul, mul_smul_comm]
        have hsum_leib : ∀ a b,
            (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (a * b))
              = a * (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i b)
                + b * (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i a) := by
          intro a b
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          rw [leibniz]
          simp [smul_eq_mul]
          ring
        let L1_ : S →ₗ[k] S1_ :=
          { toFun := fun x => coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ x)
            map_add' := by
              intro x y
              show coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ $ x + y)
                = coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ x)
                  + coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ y)
              rw [map_add, map_add, mul_add]
            map_smul' := by
              intro c x
              show coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ $ c • x)
                = c • (coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ x))
              rw [map_smul, Derivation.map_smul, mul_smul_comm] }
        let L2_ : S →ₗ[k] S1_ :=
          { toFun := fun x => ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
            map_add' := by
              intro x y
              show ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (x + y))
                = ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
                  + ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i y)
              rw [hsum_add, map_add]
            map_smul' := by
              intro c x
              show ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (c • x))
                = c • ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i x)
              rw [hsum_smul, map_smul] }
        have hleib1 : ∀ a b, L1_ (a * b) = a • L1_ b + b • L1_ a := by
          intro a b
          show coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ $ a * b)
            = a • (coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ b))
              + b • (coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ a))
          rw [map_mul, leibniz, hsmul a, hsmul b]
          simp [smul_eq_mul]
          ring
        have hleib2 : ∀ a b, L2_ (a * b) = a • L2_ b + b • L2_ a := by
          intro a b
          show ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i (a * b))
            = a • ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i b)
              + b • ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i a)
          rw [hsum_leib, map_add, map_mul, map_mul, hsmul a, hsmul b]
        have hD : mk' L1_ hleib1 = mk' L2_ hleib2 := by
          refine derivation_ext_of_coord k ι S S1_ _ _ fun j => ?_
          let _m0 := coord k ι S j
          show coord k ι S1_ s * partialDeriv k ι S1_ s (ph_ _m0)
            = ph_ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i _m0)
          have hsum : (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i _m0)
              = if j ∈ T then coord k ι S j else 0 := by
            have hterm : ∀ i ∈ T, coord k ι S i * partialDeriv k ι S i _m0
                = if i = j then coord k ι S j else 0 := by
              intro i _
              rw [partialDeriv_coord]
              by_cases h : i = j
              subst h
              simp
              simp [h]
            rw [sum_congr rfl hterm]
            by_cases hj : j ∈ T
            rw [sum_eq_single j]
            simp [hj]
            simp_all
            simp_all
            simp_all
          rw [hsum]
          by_cases hjs : j = s
          subst hjs
          rw [hs, if_pos hsT, hs, partialDeriv_coord_self, mul_one]
          by_cases hjT : j ∈ T
          have h1 :=
            partialDeriv_coord_self k ι S1_ s
          have h2 :=
            partialDeriv_coord_of_ne k ι S1_ s j $ m113 hjs
          rw [if_pos hjT, hin j hjT hjs, Derivation.leibniz, h1, h2]
          simp [smul_eq_mul]
          ring
          have hne : s ≠ j := by
            rintro rfl
            exact hjT hsT
          rw [if_neg hjT, map_zero, hout j hjT,
            partialDeriv_coord_of_ne k ι S1_ s j hne, mul_zero]
        exact congr_fun hD f
      rw [_i55]
      exact congrArg ph_ $ sy_ $ add_sum_erase T (fun i => coord k ι S i * partialDeriv k ι S i f) hsT
    rw [_i49, map_add, map_mul, hs, map_sum, hsum2]
  rw [h2] at h1
  have h0 : (ph_ _a3
      - coord k ι S1_ s ^ e
        * (coord k ι S1_ s * partialDeriv k ι S1_ s g + ((e + 1 : ℕ) : S1_) * g
            - ∑ i ∈ T.erase s, coord k ι S1_ i * partialDeriv k ι S1_ i g))
      * coord k ι S1_ s = 0 := by
    linear_combination -h1
  linear_combination (an2 (mp_ mem_nonZeroDivisors_iff hnzd) _ h0)
end
end

theorem mul_mem_span_singleton_mul {R : Type} [CommRing R] a I
    {g} (hg : g ∈ I) : a * g ∈ Ideal.span ({a} : Set R) * I :=
  mul_mem_mul (m100 $ Set.mem_singleton_iff.mpr rfl) hg

section
variable [Fintype ι] (hin : ∀ i ∈ T, i ≠ s → ph_ (coord k ι S i) = coord k ι S1_ i * coord k ι S1_ s) (hs : ph_ (coord k ι S s) = coord k ι S1_ s) (hout : ∀ i ∉ T, ph_ (coord k ι S i) = coord k ι S1_ i) (hsT : s ∈ T) (hnzd : coord k ι S1_ s ∈ nonZeroDivisors S1_) (J : Ideal S) (J1 : Ideal S1_) (m : ℕ)
include hin hs hout hsT hnzd
theorem map_derivIdeal_le_span_pow_mul (hm : 1 ≤ m)
    (hJ : Ideal.map ph_ J ≤ Ideal.span {coord k ι S1_ s ^ m} * J1) :
    Ideal.map ph_ (derivIdeal k J)
      ≤ Ideal.span {coord k ι S1_ s ^ (m - 1)} * derivIdeal k J1 := by
  obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
  simp
  let _a0 := coord k ι S1_ s
  have hmem : ∀ x ∈ J, ∃ g ∈ J1, ph_ x = _a0 ^ (e + 1) * g := by
    intro x hx
    obtain ⟨g, hg, hgx⟩ := mem_span_singleton_mul.1 $ hJ $ mem_map_of_mem ph_ hx
    exact ⟨g, hg, sy_ hgx⟩
  have hkey : ∀ x ∈ J, ∀ i,
      ph_ (partialDeriv k ι S i x) ∈ m17 {_a0 ^ e} * derivIdeal k J1 := by
    intro x hx i
    obtain ⟨g, hg, hgx⟩ := hmem x hx
    by_cases hiT : i ∈ T
    by_cases his : i = s
    have hbr : _a0 * partialDeriv k ι S1_ s g + ((e + 1 : ℕ) : S1_) * g
        - ∑ j ∈ T.erase s, coord k ι S1_ j * partialDeriv k ι S1_ j g
          ∈ derivIdeal k J1 := by
      refine sub_mem (add_mem (mul_mem_left _ _ $ derivation_apply_mem_derivIdeal k J1 (partialDeriv k ι S1_ s) hg) $ mul_mem_left _ _ $ le_derivIdeal k J1 hg) ?_
      refine sum_mem fun j _ => ?_
      exact mul_mem_left _ _
        (derivation_apply_mem_derivIdeal k J1 (partialDeriv k ι S1_ j) hg)
    rw [his, map_partialDeriv_self_eq_pow_mul k ι S S1_ ph_ T s hin hs hout hsT hnzd x g e hgx]
    exact mul_mem_span_singleton_mul _ _ hbr
    rw [map_partialDeriv_eq_pow_mul_of_mem k ι S S1_ ph_ T s hin hs hout hnzd i hiT his x g e hgx]
    exact mul_mem_span_singleton_mul _ _
      (derivation_apply_mem_derivIdeal k J1 (partialDeriv k ι S1_ i) hg)
    rw [map_partialDeriv_eq_pow_mul_of_notMem k ι S S1_ ph_ T s hin hs hout hsT i hiT x g e hgx,
      pow_succ, mul_assoc]
    exact mul_mem_span_singleton_mul _ _
      (mul_mem_left _ _
        (derivation_apply_mem_derivIdeal k J1 (partialDeriv k ι S1_ i) hg))
  rw [map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  intro x hx
  obtain ⟨g, hg, hgx⟩ := hmem x hx
  refine Ideal.mem_comap.mpr ?_
  rw [hgx, pow_succ, mul_assoc]
  exact mul_mem_span_singleton_mul _ _
    (mul_mem_left _ _ $ le_derivIdeal k J1 hg)
  intro D x hx
  refine Ideal.mem_comap.mpr ?_
  have h1 :=
    congrArg (fun E => E x) $ eq_sum_smul_partialDeriv k ι S D
  have hDx : D x = ∑ i : ι, D (coord k ι S i) * partialDeriv k ι S i x := by simp_all
  rw [hDx, map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_mul]
  exact mul_mem_left _ _ $ hkey x hx i

theorem map_derivIdealIterate_le_span_pow_mul
    (hJ : Ideal.map ph_ J ≤ Ideal.span {coord k ι S1_ s ^ m} * J1)
    j (hj : j ≤ m) :
    Ideal.map ph_ (derivIdealIterate k j J)
      ≤ Ideal.span {coord k ι S1_ s ^ (m - j)} * derivIdealIterate k j J1 := by
  have key : ∀ r, r ≤ m → m6 ph_ (derivIdealIterate k r J)
      ≤ m17 {coord k ι S1_ s ^ (m - r)} * derivIdealIterate k r J1 := by
    intro r
    induction r with
    | zero =>
        intro _
        rwa [derivIdealIterate_zero k J, derivIdealIterate_zero k J1, m130]
    | succ r ih =>
        intro hr
        have h1 : 1 ≤ m - r := by omega
        have hstep := map_derivIdeal_le_span_pow_mul k ι S S1_ ph_ T s hin hs hout hsT hnzd
          (derivIdealIterate k r J) (derivIdealIterate k r J1) (m - r) h1 $ ih $ le_of_succ_le hr
        have hmm : m - r - 1 = m - (r + 1) := by omega
        rw [hmm] at hstep
        rwa [derivIdealIterate_succ k r J, derivIdealIterate_succ k r J1]
  exact key j hj
end

end EtaleCoordinates
namespace EtaleCoordinates

section
variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A]
theorem finset_sum_derivation_apply {mu_ : Type} (u : Finset mu_) (D : mu_ → Derivation R A A) (x : A) :
    (∑ j ∈ u, D j) x = ∑ j ∈ u, (D j) x :=by simp_all
theorem smul_derivation_apply (a : A) (D : Derivation R A A) (x : A) : (a • D) x = a * D x := by
  simp
end

variable (k : Type) [CommRing k] (ι : Type) [DecidableEq ι]
  (S : Type) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [FormallyEtale (MvPolynomial ι k) S]
  (S1_ : Type) [CommRing S1_] [Algebra k S1_] [Algebra (MvPolynomial ι k) S1_]
  [IsScalarTower k (MvPolynomial ι k) S1_] [FormallyEtale (MvPolynomial ι k) S1_]
  (ph_ : S →ₐ[k] S1_) (T : Finset ι) (s : ι)

theorem partialDeriv_mem_sup_of_span_pow_mul_eq_map
    (hin : ∀ i ∈ T, i ≠ s → ph_ (coord k ι S i) = coord k ι S1_ i * coord k ι S1_ s)
    (hs : ph_ (coord k ι S s) = coord k ι S1_ s)
    (hout : ∀ i ∉ T, ph_ (coord k ι S i) = coord k ι S1_ i)
    (hnzd : coord k ι S1_ s ∈ nonZeroDivisors S1_)
    i (hiT : i ∈ T) (his : i ≠ s)
    J L L' c
    (hJ : Ideal.span {coord k ι S1_ s ^ (c + 1)} * L = Ideal.map ph_ J)
    (hD : Ideal.map ph_ (derivIdeal k J) ≤ Ideal.span {coord k ι S1_ s ^ c} * L')
    g (hg : g ∈ L) :
    partialDeriv k ι S1_ i g ∈ L ⊔ L' := by
  let _c0 := ⇑ph_ '' J
  have hmapspan : Ideal.span _c0 = Ideal.map ph_ J := by
    rw [← map_span, span_eq]
  let _a0 := coord k ι S1_ s ^ (c + 1)
  have hgen : ∀ x ∈ _c0,
      partialDeriv k ι S1_ i x ∈ m17 {_a0} * (L ⊔ L') := by
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := mp_ mem_span_singleton_mul $ hD $ mem_map_of_mem ph_ $ derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) $ SetLike.mem_coe.mp hf
    rw [partialDeriv_map_of_mem k ι S S1_ ph_ T s hin hs hout i hiT his f, ← hzeq]
    exact mpr_ mem_span_singleton_mul ⟨z, mem_sup_right hz, by ring⟩
  have hGT : Ideal.span _c0
      ≤ Ideal.span {_a0} * (L ⊔ L') := by
    rw [hmapspan, ← hJ]
    exact mul_mono_right le_sup_left
  have hmem : _a0 * g ∈ Ideal.span _c0 := by
    rw [hmapspan, ← hJ]
    exact mpr_ mem_span_singleton_mul ⟨g, hg, rfl⟩
  have key := derivation_apply_mem_of_mem_span (partialDeriv k ι S1_ i) hGT hgen hmem
  have hDypow : partialDeriv k ι S1_ i _a0 = 0 := by
    rw [leibniz_pow, partialDeriv_coord_of_ne k ι S1_ i s his, smul_zero, smul_zero]
  have hexp : partialDeriv k ι S1_ i (_a0 * g)
      = _a0 * partialDeriv k ι S1_ i g := by simp_all
  rw [hexp] at key
  obtain ⟨w, hw, hweq⟩ := mp_ mem_span_singleton_mul key
  have h0 : (partialDeriv k ι S1_ i g - w) * _a0 = 0 := by
    linear_combination -hweq
  rwa [mp_ sub_eq_zero $ (mp_ mem_nonZeroDivisors_iff $ pow_mem hnzd $ c + 1).2 _ h0]

section
variable [Fintype ι] (hin : ∀ i ∈ T, i ≠ s → ph_ (coord k ι S i) = coord k ι S1_ i * coord k ι S1_ s) (hs : ph_ (coord k ι S s) = coord k ι S1_ s) (hout : ∀ i ∉ T, ph_ (coord k ι S i) = coord k ι S1_ i) (hsT : s ∈ T) (hnzd : coord k ι S1_ s ∈ nonZeroDivisors S1_) (i) (hiT : i ∈ T) (his : i ≠ s) (J : Ideal S) (J1 : Ideal S1_) (m : ℕ)
include hin hs hout hsT hnzd hiT his
theorem map_logDerivIdeal_le_span_pow_mul (hm : 1 ≤ m)
    (hJ : Ideal.map ph_ J ≤ Ideal.span {coord k ι S1_ s ^ m} * J1) :
    Ideal.map ph_ (logDerivIdeal k (Ideal.span {coord k ι S i}) J)
      ≤ Ideal.span {coord k ι S1_ s ^ (m - 1)}
          * logDerivIdeal k (Ideal.span {coord k ι S1_ i}) J1 := by
  let _a2 := partialDeriv k ι S1_ i
  let _a0 := coord k ι S1_ s
  let _a1 := coord k ι S1_ i
  let _c0 := m17 {_a1}
  obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
  simp
  have hJmem : ∀ f ∈ J, ∃ f1_ ∈ J1, ph_ f = _a0 ^ (e + 1) * f1_ := by
    intro f hf
    obtain ⟨f1_, hf1_, hfe⟩ := mp_ mem_span_singleton_mul $ hJ $ mem_map_of_mem ph_ hf
    exact ⟨f1_, hf1_, sy_ hfe⟩
  have htan : ∀ j, j ≠ i →
      partialDeriv k ι S1_ j ∈ tangentDerivations k _c0 := by
    intro j hj
    rw [mem_tangentDerivations_span_singleton, partialDeriv_coord_of_ne k ι S1_ j i hj]
    exact m97 _
  rw [map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  intro f hf
  rw [mem_comap]
  obtain ⟨f1_, hf1_, hfe⟩ := hJmem f hf
  refine mpr_ mem_span_singleton_mul ⟨_a0 * f1_, le_logDerivIdeal k _c0 J1 $ J1.mul_mem_left _ hf1_, ?_⟩
  rw [hfe]
  ring
  intro D hD f hf
  rw [mem_comap]
  obtain ⟨f1_, hf1_, hfe⟩ := hJmem f hf
  have hpd : ∀ j, j ≠ i →
      partialDeriv k ι S1_ j f1_ ∈ logDerivIdeal k _c0 J1 := by
    intro j hj
    exact derivation_apply_mem_logDerivIdeal k _c0 J1
      (partialDeriv k ι S1_ j) (htan j hj) hf1_
  have hpdi : _a1 * partialDeriv k ι S1_ i f1_
      ∈ logDerivIdeal k _c0 J1 := by
    have h := derivation_apply_mem_logDerivIdeal k _c0 J1
      (_a1 • _a2) (smul_mem_tangentDerivations k _c0 (m100 $ mem_singleton _) _a2) hf1_
    rwa [smul_derivation_apply] at h
  obtain ⟨a, ha⟩ := mp_ mem_span_singleton' $ (mem_tangentDerivations_span_singleton k (coord k ι S i) D).mp hD
  have hDf : ph_ (D f) = ∑ j : ι, ph_ (D $ coord k ι S j) * ph_ (partialDeriv k ι S j f) := by
    have h0 : D f = ∑ j : ι, D (coord k ι S j) * partialDeriv k ι S j f := by
      conv_lhs => rw [eq_sum_smul_partialDeriv k ι S D]
      rw [finset_sum_derivation_apply]
      exact sum_congr rfl fun j _ => smul_derivation_apply _ _ _
    rw [h0, map_sum]
    exact sum_congr rfl fun j _ => map_mul ph_ _ _
  rw [hDf]
  refine m133 _ ?_
  intro j _
  by_cases hji : j = i
  rw [hji]
  have h1 :=
    map_partialDeriv_eq_pow_mul_of_mem k ι S S1_ ph_ T s hin hs hout hnzd i hiT his f f1_ e hfe
  rw [h1, ← ha, map_mul, hin i hiT his]
  exact mpr_ mem_span_singleton_mul
    ⟨ph_ a * _a0 * (_a1 * partialDeriv k ι S1_ i f1_),
      mul_mem_left _ _ hpdi, by ring⟩
  have hkey : ph_ (partialDeriv k ι S j f)
      ∈ m17 {_a0 ^ e}
          * logDerivIdeal k _c0 J1 := by
    by_cases hjT : j ∈ T
    by_cases hjs : j = s
    rw [hjs]
    have h1 := map_partialDeriv_self_eq_pow_mul k ι S S1_ ph_ T s hin hs hout hsT hnzd f f1_ e hfe
    have hbr : _a0 * partialDeriv k ι S1_ s f1_ + ((e + 1 : ℕ) : S1_) * f1_
        - ∑ l ∈ T.erase s, coord k ι S1_ l * partialDeriv k ι S1_ l f1_
        ∈ logDerivIdeal k _c0 J1 := by
      refine Ideal.sub_mem _ (m128 _ (mul_mem_left _ _ $ hpd s his.symm) $ mul_mem_left _ _ $ le_logDerivIdeal k _c0 J1 hf1_) ?_
      refine m133 _ ?_
      intro l _
      by_cases hli : l = i
      rwa [hli]
      exact mul_mem_left _ _ $ hpd l hli
    rw [h1]
    exact mpr_ mem_span_singleton_mul ⟨_, hbr, rfl⟩
    have h1 :=
      map_partialDeriv_eq_pow_mul_of_mem k ι S S1_ ph_ T s hin hs hout hnzd j hjT hjs f f1_ e hfe
    rw [h1]
    exact mpr_ mem_span_singleton_mul ⟨_, hpd j hji, rfl⟩
    have h1 :=
      map_partialDeriv_eq_pow_mul_of_notMem k ι S S1_ ph_ T s hin hs hout hsT j hjT f f1_ e hfe
    rw [h1]
    exact mpr_ mem_span_singleton_mul
      ⟨_a0 * partialDeriv k ι S1_ j f1_,
        mul_mem_left _ _ $ hpd j hji, by ring⟩
  exact mul_mem_left _ _ hkey

theorem map_logDerivIdealIterate_le_span_pow_mul
    (hJ : Ideal.map ph_ J ≤ Ideal.span {coord k ι S1_ s ^ m} * J1)
    j (hj : j ≤ m) :
    Ideal.map ph_ (logDerivIdealIterate k (Ideal.span {coord k ι S i}) j J)
      ≤ Ideal.span {coord k ι S1_ s ^ (m - j)}
          * logDerivIdealIterate k (Ideal.span {coord k ι S1_ i}) j J1 := by
  revert hj
  induction j with
  | zero =>
      intro _
      rwa [logDerivIdealIterate_zero, logDerivIdealIterate_zero, m130]
  | succ j ih =>
      intro hj
      have h2 := map_logDerivIdeal_le_span_pow_mul k ι S S1_ ph_ T s hin hs hout hsT hnzd i hiT his
        (logDerivIdealIterate k (m17 {coord k ι S i}) j J)
        (logDerivIdealIterate k (m17 {coord k ι S1_ i}) j J1) (m - j) (by omega) $ ih $ le_of_succ_le hj
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      have hsub : m - j - 1 = m - (j + 1) := by omega
      rwa [hsub] at h2
end

end EtaleCoordinates

variable {X : Sch}

def IsMonomialIn (E : Bdy X) (M : ISD X) : Prop :=
  ∀ x : X, ∃ U : Opn X, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
    M.comap U.i = ∏ i : Fin E.length, (E.get i).comap U.i ^ a i

structure IsMonomialSplitting (E : Bdy X) (I M N : ISD X) :
    Prop where
  eq_mul : I = M * N
  monomial_support : (M.support : Set X) ⊆ ⋃ D ∈ E, (D.support : Set X)
  monomial : IsMonomialIn E M
  transversal : ∀ D ∈ E, ∀ C : Set X, IsIrreducible C → C ⊆ (D.support : Set X) →
    (∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C) →
    ¬ C ⊆ (N.support : Set X)

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

section
variable (m : ℕ)
def tuningWeight (c : ℕ → ℕ) : ℕ := ∑ j ∈ range m, (m - j) * c j

theorem tuningWeight_eq_sum c :
    tuningWeight m c = ∑ j ∈ range m, (m - j) * c j := rfl

section
variable (c d : ℕ → ℕ)
theorem tuningWeight_fun_add :
    tuningWeight m (fun j => c j + d j) = tuningWeight m c + tuningWeight m d := by
  simp [tuningWeight, Nat.mul_add, sum_add_distrib]

theorem tuningWeight_add :
    tuningWeight m (c + d) = tuningWeight m c + tuningWeight m d :=
  tuningWeight_fun_add m c d
end
end

section
variable (m n : ℕ) (c : ℕ → ℕ)
theorem tuningWeight_mul_left :
    tuningWeight m (fun j => n * c j) = n * tuningWeight m c := by
  simp [tuningWeight, mul_sum, Nat.mul_left_comm]

theorem tuningWeight_nsmul :
    tuningWeight m (n • c) = n * tuningWeight m c := by
  have : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [this, tuningWeight_mul_left]
end

theorem tuningWeight_single (m i : ℕ) (hi : i ∈ range m) :
    tuningWeight m (single i 1) = m - i := by
  rw [tuningWeight_eq_sum, sum_eq_single i]
  simp
  simp_all
  simp_all

theorem listProd_map_range_eq_prod {M : Type} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (List.map f $ List.range m).prod = ∏ j ∈ range m, f j := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [range_succ, m144, prod_append, ih, prod_range_succ]
      simp

section

variable (k : Type) [CommRing k] {S : Type} [CommRing S] [Algebra k S]

section
variable (J : Ideal S)
section
variable (m : ℕ)
def tuningMonomial (c : ℕ → ℕ) : Ideal S :=
  ∏ j ∈ range m, derivIdealIterate k j J ^ c j

theorem tuningMonomial_eq_prod (c : ℕ → ℕ) :
    tuningMonomial k J m c = ∏ j ∈ range m, derivIdealIterate k j J ^ c j := rfl

theorem tuningMonomial_zero :
    tuningMonomial k J m (fun _ => 0) = ⊤ := by
  simp [tuningMonomial_eq_prod, one_eq_top]

section
variable (c d : ℕ → ℕ)
theorem tuningMonomial_mul_fun_add :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m fun j => c j + d j := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod, tuningMonomial_eq_prod, ← prod_mul_distrib]
  exact prod_congr rfl fun j _ => sy_ $ pow_add _ _ _

theorem tuningMonomial_mul :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (c + d) :=
  tuningMonomial_mul_fun_add k J m c d
end
end

section
variable (m n : ℕ) (c : ℕ → ℕ)
theorem tuningMonomial_pow_fun_mul :
    tuningMonomial k J m c ^ n = tuningMonomial k J m fun j => n * c j := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [prod_range_succ, mul_pow, ih, prod_range_succ, ← pow_mul,
        mul_comm (c m) n]

theorem tuningMonomial_pow :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (n • c) := by
  have h : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [h, tuningMonomial_pow_fun_mul]
end

theorem tuningMonomial_single (m i : ℕ) (hi : i ∈ range m) :
    tuningMonomial k J m (single i 1) = derivIdealIterate k i J := by
  rw [tuningMonomial_eq_prod, prod_eq_single i]
  simp
  simp_all
  simp_all

section
variable (m s : ℕ)
def tunedIdeal : Ideal S :=
  ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c

theorem tunedIdeal_eq_iSup :
    tunedIdeal k J m s = ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c := rfl

theorem tuningMonomial_le_tunedIdeal (c : ℕ → ℕ)
    (hc : s ≤ tuningWeight m c) : tuningMonomial k J m c ≤ tunedIdeal k J m s :=
  le_iSup_of_le c $ le_iSup_of_le hc le_rfl

theorem tunedIdeal_le_iff (K : Ideal S) :
    tunedIdeal k J m s ≤ K ↔ ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → tuningMonomial k J m c ≤ K := by
  constructor
  intro h c hc
  exact le_trans (tuningMonomial_le_tunedIdeal k J m s c hc) h
  intro h
  exact iSup_le fun c => iSup_le fun hc => h c hc
end

theorem tunedIdeal_zero m : tunedIdeal k J m 0 = ⊤ := by
  refine mpr_ eq_top_iff ?_
  rw [← tuningMonomial_zero k J m]
  exact tuningMonomial_le_tunedIdeal k J m 0 (fun _ => 0) $ zero_le _

theorem tunedIdeal_antitone (m : ℕ) {s t : ℕ} (h : s ≤ t) :
    tunedIdeal k J m t ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_le_iff]
  intro c hc
  exact tuningMonomial_le_tunedIdeal k J m s c $ le_trans h hc

theorem tunedIdeal_mul_le m s t :
    tunedIdeal k J m s * tunedIdeal k J m t ≤ tunedIdeal k J m (s + t) := by
  rw [tunedIdeal_eq_iSup, tunedIdeal_eq_iSup, iSup_mul]
  refine iSup_le fun c => ?_
  rw [iSup_mul]
  refine iSup_le fun hc => ?_
  rw [mul_iSup]
  refine iSup_le fun d => ?_
  rw [mul_iSup]
  refine iSup_le fun hd => ?_
  rw [tuningMonomial_mul_fun_add]
  refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
  rw [tuningWeight_fun_add]
  exact Nat.add_le_add hc hd
end

theorem mul_sup_le {R : Type} [CommRing R] (B X Y T : Ideal R)
    (hX : B * X ≤ T) (hY : B * Y ≤ T) : B * (X ⊔ Y) ≤ T := by
  refine Ideal.mul_le.mpr ?_
  intro b hb z hz
  rcases mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
  rw [mul_add]
  exact m60 T (hX $ mul_mem_mul hb hx) $ hY $ mul_mem_mul hb hy

theorem derivIdeal_one {A : Type} [CommRing A] {R : Type} [CommRing R]
    [Algebra A R] : derivIdeal A (1 : Ideal R) = 1 := by
  rw [one_eq_top]
  exact mpr_ eq_top_iff $ le_derivIdeal A ⊤

theorem tuningWeight_eq_add_sub_of_succ (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) :
    tuningWeight m c = tuningWeight m d + (m - i) := by
  have hmem : i ∈ range m := Finset.mem_range.mpr hi
  let _a0 := (range m).erase i
  have keyc : tuningWeight m c
      = (m - i) * c i + ∑ j ∈ _a0, (m - j) * c j := by
    rw [tuningWeight_eq_sum]
    exact sy_ $ add_sum_erase (range m) (fun j => (m - j) * c j) hmem
  have keyd : tuningWeight m d
      = (m - i) * d i + ∑ j ∈ _a0, (m - j) * d j := by
    rw [tuningWeight_eq_sum]
    exact sy_ $ add_sum_erase (range m) (fun j => (m - j) * d j) hmem
  have h3 : ∑ j ∈ _a0, (m - j) * d j
      = ∑ j ∈ _a0, (m - j) * c j :=
    sum_congr rfl fun j hj => by rw [hne j $ ne_of_mem_erase hj]
  rw [keyc, keyd, h3, ← hdi]
  ring

section
variable {A : Type} [CommRing A] {R : Type} [CommRing R] [Algebra A R]
theorem tuningMonomial_eq_derivIdealIterate_mul_of_succ (J : Ideal R) (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i = c i + 1) :
    tuningMonomial A J m d = derivIdealIterate A i J * tuningMonomial A J m c := by
  have hmem : i ∈ range m := Finset.mem_range.mpr hi
  let _a0 := (range m).erase i
  have keyd : tuningMonomial A J m d
      = derivIdealIterate A i J ^ d i *
        ∏ j ∈ _a0, derivIdealIterate A j J ^ d j := by
    rw [tuningMonomial_eq_prod]
    exact sy_ $ mul_prod_erase (range m) (fun j => derivIdealIterate A j J ^ d j) hmem
  have keyc : tuningMonomial A J m c
      = derivIdealIterate A i J ^ c i *
        ∏ j ∈ _a0, derivIdealIterate A j J ^ c j := by
    rw [tuningMonomial_eq_prod]
    exact sy_ $ mul_prod_erase (range m) (fun j => derivIdealIterate A j J ^ c j) hmem
  have h3 : ∏ j ∈ _a0, derivIdealIterate A j J ^ d j
      = ∏ j ∈ _a0, derivIdealIterate A j J ^ c j :=
    prod_congr rfl fun j hj => by rw [hne j $ ne_of_mem_erase hj]
  rw [keyd, keyc, h3, hdi, pow_succ]
  simp [mul_comm, mul_assoc]

theorem derivIdealIterate_succ_mul_tuningMonomial_le (J : Ideal R) (m s i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) (hc : s + 1 ≤ tuningWeight m c) :
    derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tunedIdeal A J m s := by
  have hw :=
    tuningWeight_eq_add_sub_of_succ m i hi c d hne hdi
  rcases m63 (i + 1) m with hlt | hge
  have hmono : tuningMonomial A J m (fun j => if j = i + 1 then d j + 1 else d j)
      = derivIdealIterate A (i + 1) J * tuningMonomial A J m d :=
    tuningMonomial_eq_derivIdealIterate_mul_of_succ J m (i + 1) hlt d (fun j => if j = i + 1 then d j + 1 else d j)
      (fun j hj => by simp [hj]) $ by simp
  have hw' :=
    tuningWeight_eq_add_sub_of_succ m (i + 1) hlt (fun j => if j = i + 1 then d j + 1 else d j) d
      (fun j hj => by simp [hj]) $ by simp
  refine le_trans (le_of_eq hmono.symm)
    (tuningMonomial_le_tunedIdeal A J m s (fun j => if j = i + 1 then d j + 1 else d j) ?_)
  omega
  have hle : derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tuningMonomial A J m d :=
    Ideal.mul_le.mpr fun r _ t ht => mul_mem_left _ r ht
  refine le_trans hle $ tuningMonomial_le_tunedIdeal A J m s d ?_
  omega

theorem mul_derivIdeal_prod_le (J T : Ideal R) (c : ℕ → ℕ) :
    ∀ n B,
      B * (∏ j ∈ range n, derivIdealIterate A j J ^ c j) ≤ T →
      (∀ i, i < n → ∀ d : ℕ → ℕ, (∀ j, j ≠ i → d j = c j) → d i + 1 = c i →
        B * (derivIdealIterate A (i + 1) J *
          ∏ j ∈ range n, derivIdealIterate A j J ^ d j) ≤ T) →
      B * derivIdeal A (∏ j ∈ range n, derivIdealIterate A j J ^ c j) ≤ T := by
  intro n
  induction n with
  | zero =>
      intro B h1 _
      rw [range_zero, prod_empty, derivIdeal_one, mul_one]
      rwa [range_zero, prod_empty, mul_one] at h1
  | succ n ih =>
      intro B h1 h2
      rw [prod_range_succ] at h1
      rw [prod_range_succ]
      refine le_trans (Ideal.mul_mono le_rfl (derivIdeal_mul_le A _ _)) ?_
      refine mul_sup_le B _ _ T ?_ ?_
      rcases m73 (c n) with h0 | hpos
      rw [h0, pow_zero, mul_one] at h1
      rwa [h0, pow_zero, derivIdeal_one, mul_one]
      obtain ⟨e, he⟩ : ∃ e, c n = e + 1 := ⟨c n - 1, by omega⟩
      have hq1 : (∏ j ∈ range n, derivIdealIterate A j J ^ (if j = n then e else c j))
          = ∏ j ∈ range n, derivIdealIterate A j J ^ c j :=
        prod_congr rfl fun j hj => by
          rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
      have hq2 : derivIdealIterate A n J ^ (if n = n then e else c n)
          = derivIdealIterate A n J ^ e := by simp
      have hprod : (∏ j ∈ range (n + 1),
            derivIdealIterate A j J ^ (if j = n then e else c j))
          = (∏ j ∈ range n, derivIdealIterate A j J ^ c j) *
            derivIdealIterate A n J ^ e := by
        rw [prod_range_succ, hq1, hq2]
      have hd : B * (derivIdealIterate A (n + 1) J *
          ((∏ j ∈ range n, derivIdealIterate A j J ^ c j) *
            derivIdealIterate A n J ^ e)) ≤ T := by
        rw [← hprod]
        exact h2 n (lt_succ_self n) (fun j => if j = n then e else c j)
          (fun j hj => by simp [hj]) (by simp [he])
      have hstep : derivIdeal A (derivIdealIterate A n J ^ c n)
          ≤ derivIdealIterate A n J ^ e * derivIdealIterate A (n + 1) J := by
        rw [he, derivIdealIterate_succ, derivIdeal_le_iff]
        constructor
        rw [pow_succ]
        exact Ideal.mul_le.mpr fun a ha b hb => mul_mem_mul ha $ le_derivIdeal A (derivIdealIterate A n J) hb
        intro D x hx
        exact derivation_apply_mem_pow_mul_derivIdeal A (derivIdealIterate A n J) D e x hx
      refine le_trans (mul_mono le_rfl (mul_mono le_rfl hstep)) ?_
      refine le_trans (le_of_eq ?_) hd
      simp [mul_comm, mul_left_comm, mul_assoc]
      have heq : B * (derivIdealIterate A n J ^ c n *
          derivIdeal A (∏ j ∈ range n, derivIdealIterate A j J ^ c j))
          = (B * derivIdealIterate A n J ^ c n) *
            derivIdeal A (∏ j ∈ range n, derivIdealIterate A j J ^ c j) :=
        (mul_assoc _ _ _).symm
      rw [heq]
      refine ih (B * derivIdealIterate A n J ^ c n) ?_ ?_
      refine le_trans (le_of_eq ?_) h1
      simp [mul_comm, mul_assoc]
      intro i hi d hne hdi
      have hd := h2 i (lt_succ_of_lt hi) d hne hdi
      rw [prod_range_succ, hne n (by omega : n ≠ i)] at hd
      refine le_trans (le_of_eq ?_) hd
      simp [mul_comm, mul_left_comm, mul_assoc]
end

section
variable (J : Ideal S)
theorem derivIdeal_tunedIdeal_succ_le m s :
    derivIdeal k (tunedIdeal k J m (s + 1)) ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_eq_iSup k J m $ s + 1]
  refine (derivIdeal_iSup_le k _).trans $ iSup_le ?_
  intro c
  refine (derivIdeal_iSup_le k _).trans $ iSup_le ?_
  intro hc
  rw [tuningMonomial_eq_prod]
  refine le_trans (le_of_eq (one_mul _).symm) ?_
  refine mul_derivIdeal_prod_le J (tunedIdeal k J m s) c m 1 ?_ ?_
  rw [one_mul]
  exact tuningMonomial_le_tunedIdeal k J m s c $ by omega
  intro i hi d hne hdi
  rw [one_mul]
  exact derivIdealIterate_succ_mul_tuningMonomial_le J m s i hi c d hne hdi hc

theorem derivIdealIterate_tunedIdeal_le (m s j : ℕ) :
    derivIdealIterate k j (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - j) := by
  induction j with
  | zero =>
      simp only [derivIdealIterate_zero, m130]
      exact le_rfl
  | succ j ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      rcases m73 (s - j) with h | h
      have hsj : s - (j + 1) = 0 := by omega
      rw [hsj, tunedIdeal_zero]
      exact le_top
      obtain ⟨t, ht⟩ : ∃ t, s - j = t + 1 := ⟨s - j - 1, by omega⟩
      have hsj : s - (j + 1) = t := by omega
      rw [ht, hsj]
      exact derivIdeal_tunedIdeal_succ_le k J m t

theorem derivIdealIterate_mul_derivIdeal_tunedIdeal_le m s (hs : 1 ≤ s) :
    derivIdealIterate k (s - 1) (tunedIdeal k J m s) * derivIdeal k (tunedIdeal k J m s) ≤
      tunedIdeal k J m s := by
  have hss : s - (s - 1) = 1 := by omega
  have hsum : 1 + (s - 1) = s := by omega
  let _a0 := tunedIdeal k J m s
  have h1 : derivIdealIterate k (s - 1) _a0 ≤ tunedIdeal k J m 1 := by
    have h := derivIdealIterate_tunedIdeal_le k J m s $ s - 1
    rwa [hss] at h
  have h2 : derivIdeal k _a0 ≤ tunedIdeal k J m (s - 1) := by
    have h := derivIdealIterate_tunedIdeal_le k J m s 1
    rwa [derivIdealIterate_one] at h
  refine le_trans (mul_mono h1 h2) ?_
  have h3 := tunedIdeal_mul_le k J m 1 $ s - 1
  rwa [hsum] at h3
end

theorem exists_ne_zero_of_one_le_tuningWeight {m : ℕ} {c : ℕ → ℕ}
    (hc : 1 ≤ tuningWeight m c) : ∃ j ∈ range m, c j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz : tuningWeight m c = 0 := by
    rw [tuningWeight_eq_sum]
    exact sum_eq_zero fun j hj => by rw [hcon j hj, Nat.mul_zero]
  rw [hz] at hc
  exact not_succ_le_zero 0 hc

theorem tunedIdeal_one_le_derivIdealIterate (J : Ideal S) (m : ℕ) (_hm : 1 ≤ m) :
    tunedIdeal k J m 1 ≤ derivIdealIterate k (m - 1) J := by
  rw [tunedIdeal_le_iff]
  intro c hc
  obtain ⟨j, hj, hcj⟩ := exists_ne_zero_of_one_le_tuningWeight hc
  refine le_trans ?_ $ derivIdealIterate_le_of_le k (le_sub_one_of_lt $ Finset.mem_range.mp hj) J
  rw [tuningMonomial_eq_prod, ← mul_prod_erase (range m) (fun x => derivIdealIterate k x J ^ c x) hj]
  exact le_trans mul_le_left $ pow_le_self hcj

theorem mul_tunedIdeal_le_iff (I J : Ideal S) (m s : ℕ) (K : Ideal S) :
    I * tunedIdeal k J m s ≤ K ↔
      ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → I * tuningMonomial k J m c ≤ K := by
  constructor
  intro h c hc
  exact le_trans (mul_mono le_rfl $ tuningMonomial_le_tunedIdeal k J m s c hc) h
  intro h
  rw [tunedIdeal_eq_iSup, mul_iSup]
  refine iSup_le fun c => ?_
  rw [mul_iSup]
  exact iSup_le fun hc => h c hc

section
variable (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S} (hx : x ∈ derivIdealIterate k (m - 1) J)
include hm hx
theorem span_pow_mul_tunedIdeal_le (n t : ℕ) :
    Ideal.span {x ^ n} * tunedIdeal k J m t ≤ tunedIdeal k J m (t + n) := by
  rw [mul_tunedIdeal_le_iff]
  intro c hc
  have _i66 : m17 {x ^ n} * tuningMonomial k J m c ≤ tunedIdeal k J m (tuningWeight m c + n) := by
    have hmem : (m - 1) ∈ range m := Finset.mem_range.mpr $ by omega
    have hspan : m17 {x ^ n} ≤ tuningMonomial k J m (n • single (m - 1) 1) := by
      rw [← tuningMonomial_pow, tuningMonomial_single k J m (m - 1) hmem,
        span_singleton_le_iff_mem]
      exact pow_mem_pow hx n
    refine le_trans (mul_mono hspan le_rfl) ?_
    rw [tuningMonomial_mul]
    refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
    rw [tuningWeight_add, tuningWeight_nsmul, tuningWeight_single m (m - 1) hmem]
    have hmm : m - (m - 1) = 1 := by omega
    rw [hmm]
    omega
  exact le_trans _i66 $ tunedIdeal_antitone k J m $ add_le_add_right hc n
end

section

variable [Algebra ℚ S]

theorem mem_of_natCast_add_one_mul_mem {A : Type} [CommRing A] [Algebra ℚ A] (n : ℕ)
    (I : Ideal A) (y : A) (h : ((n : A) + 1) * y ∈ I) : y ∈ I := by
  let _a0 := (n : ℚ)
  have hpos : (0 : ℚ) < _a0 + 1 := by positivity
  have hmap : algebraMap ℚ A (_a0 + 1) = (n : A) + 1 := by
    rw [map_add, map_one, map_natCast]
  have h1 : algebraMap ℚ A (_a0 + 1)⁻¹ * (((n : A) + 1) * y) ∈ I :=
    mul_mem_left I _ h
  rwa [← hmap, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hpos.ne', map_one, one_mul] at h1

section
variable (R : Type) [CommRing R] {A : Type} [CommRing A] [Algebra R A]
theorem pow_mul_mem_tunedIdeal (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (s n p : ℕ) {g : A}
    (hg : g ∈ derivIdealIterate R n (tunedIdeal R J m s)) :
    x ^ p * g ∈ tunedIdeal R J m ((s - n) + p) := by
  exact span_pow_mul_tunedIdeal_le R J m hm hx p (s - n)
    (mul_mem_mul (mem_span_singleton_self $ x ^ p) $ derivIdealIterate_tunedIdeal_le R J m s n hg)

theorem pow_mul_mem_derivIdeal_tunedIdeal_succ [Algebra ℚ A] (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (δ : Derivation R A A) (hde_ : δ x = 1) (s : ℕ) :
    ∀ d n : ℕ, s + 1 ≤ n + d → ∀ g : A, g ∈ derivIdealIterate R n (tunedIdeal R J m s) →
      x ^ n * g ∈ derivIdeal R (tunedIdeal R J m $ s + 1) := by
  intro d
  induction d with
  | zero =>
      intro n hn g hg
      have h2 : s + 1 ≤ (s - n) + n := by omega
      exact le_derivIdeal R _ $ tunedIdeal_antitone R J m h2 $ pow_mul_mem_tunedIdeal R J m hm hx s n n hg
  | succ d ih =>
      intro n hn g hg
      have h2 : s + 1 ≤ (s - n) + (n + 1) := by omega
      let _a1 := tunedIdeal R J m $ s + 1
      let _a3 := tunedIdeal R J m s
      have h5 : δ g ∈ derivIdealIterate R (n + 1) _a3 := by
        rw [derivIdealIterate_succ]
        exact derivation_apply_mem_derivIdeal R (derivIdealIterate R n _a3) δ hg
      have h6 :=
        ih (n + 1) (by omega) (δ g) h5
      have hd1 : δ (x ^ (n + 1)) = (n + 1) * x ^ n := by
        have hpow := δ.leibniz_pow x $ n + 1
        rw [hde_] at hpow
        simpa using hpow
      have hkey : (n + 1) * (x ^ n * g)
          = δ (x ^ (n + 1) * g) - x ^ (n + 1) * δ g := by
        rw [leibniz, hd1]
        simp [smul_eq_mul]
        ring
      refine mem_of_natCast_add_one_mul_mem n (derivIdeal R _a1)
        (x ^ n * g) ?_
      rw [hkey]
      exact m162 _ (derivation_apply_mem_derivIdeal R _a1 δ $ tunedIdeal_antitone R J m h2 $ pow_mul_mem_tunedIdeal R J m hm hx s n (n + 1) hg) h6
end

theorem tunedIdeal_le_derivIdeal_tunedIdeal_succ (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (δ : Derivation k S S) (hde_ : δ x = 1) (s : ℕ) :
    tunedIdeal k J m s ≤ derivIdeal k (tunedIdeal k J m $ s + 1) := by
  intro g hg
  have h := pow_mul_mem_derivIdeal_tunedIdeal_succ k J m hm hx δ hde_ s (s + 1) 0 (by omega) g
    (by rw [derivIdealIterate_zero]; exact hg)
  rwa [pow_zero, one_mul] at h

end

end


theorem tuningWeight_sub m c c' (h : ∀ j, c' j ≤ c j) :
    tuningWeight m (fun j => c j - c' j) = tuningWeight m c - tuningWeight m c' := by
  have key : tuningWeight m (fun j => c j - c' j) + tuningWeight m c' = tuningWeight m c := by
    rw [← tuningWeight_fun_add m (fun j => c j - c' j) c', funext fun j => sub_add_cancel $ h j]
  omega

theorem tuningWeight_ite m j q (hj : j ∈ range m) :
    tuningWeight m (fun i => if i = j then q else 0) = (m - j) * q := by
  simp only [tuningWeight_eq_sum]
  rw [sum_eq_single j]
  simp
  simp_all
  simp_all

theorem exists_le_tuningWeight_eq_mul m L r (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) c
    (hc : r * L + (m - 1) * L ≤ tuningWeight m c) :
    ∃ c', (∀ j, c' j ≤ c j) ∧ tuningWeight m c' = r * L := by
  induction r generalizing c with
  | zero =>
      refine ⟨fun _ => 0, fun i => zero_le _, ?_⟩
      simp [tuningWeight_eq_sum]
  | succ r ih =>
      have hWpos :=
        lt_of_lt_of_le (mul_pos (succ_pos r) hL) $ le_trans (le_add_right _ _) hc
      have hm : 0 < m := by
        rcases m73 m with h0 | h0
        rw [h0] at hWpos
        simp [tuningWeight_eq_sum] at hWpos
        exact h0
      have hlt1 : ∀ a b, a < b → a ≤ b - 1 := by
        intro a b h
        omega
      have hex : ∃ j ∈ range m, L ≤ (m - j) * c j := by
        by_contra hcon
        push Not at hcon
        let _a0 := L - 1
        have h1 : tuningWeight m c ≤ ∑ _x ∈ range m, _a0 := by
          rw [tuningWeight_eq_sum]
          refine sum_le_sum ?_
          intro i hi
          exact hlt1 _ _ $ hcon i hi
        have h2 : ∑ _x ∈ range m, _a0 = m * _a0 := by
          rw [sum_const, card_range, smul_eq_mul]
        rw [h2] at h1
        have hA : m * _a0 + m = m * L := by
          calc m * _a0 + m = m * (L - 1 + 1) := by ring
            _ = m * L := by rw [sub_add_cancel hL]
        have hB : (m - 1) * L + L = m * L := by
          calc (m - 1) * L + L = (m - 1 + 1) * L := by ring
            _ = m * L := by rw [sub_add_cancel hm]
        have hC : L ≤ (r + 1) * L := by
          calc L = 1 * L := sy_ (one_mul L)
            _ ≤ (r + 1) * L := mul_le_mul (by omega) $ le_refl L
        have key : ∀ X Y Z W mm p,
            X + Y ≤ Z → Z + mm = W → Y + p = W → p ≤ X → 1 ≤ mm → False := by
          intro X Y Z W mm p k1 k2 k3 k4 k5
          omega
        exact key ((r + 1) * L) ((m - 1) * L) (m * _a0) (m * L) m L
          (le_trans hc h1) hA hB hC hm
      obtain ⟨j, hjmem, hjL⟩ := hex
      have hw0 := sub_pos_of_lt $ Finset.mem_range.mp hjmem
      obtain ⟨q, hq⟩ := hdvd (m - j) hw0 $ sub_le m j
      have hqc : q ≤ c j := by
        refine Nat.le_of_mul_le_mul_left ?_ hw0
        rwa [← hq]
      have hule : ∀ i, (if i = j then q else 0) ≤ c i := by
        intro i
        by_cases hij : i = j
        simp_all
        simp_all
      have hu := sy_ hq
      rw [← tuningWeight_ite m j q hjmem] at hu
      have hd : tuningWeight m (fun i => c i - (if i = j then q else 0)) = tuningWeight m c - L := by
        have h := tuningWeight_sub m c (if · = j then q else 0) hule
        rwa [hu] at h
      have hc2 : r * L + L + (m - 1) * L ≤ tuningWeight m c := by
        calc r * L + L + (m - 1) * L = (r + 1) * L + (m - 1) * L := by ring
          _ ≤ tuningWeight m c := hc
      have hc' : r * L + (m - 1) * L
          ≤ tuningWeight m fun i => c i - (if i = j then q else 0) := by
        rw [hd]
        have h9 : ∀ A B C W : ℕ, A + C + B ≤ W → A + B ≤ W - C := by
          intro A B C W h
          omega
        exact h9 _ _ _ _ hc2
      obtain ⟨e, he1, he2⟩ := ih (fun i => c i - (if i = j then q else 0)) hc'
      refine ⟨fun i => e i + (if i = j then q else 0), ?_, ?_⟩
      intro i
      have h1 := he1 i
      have h2 := hule i
      dsimp
      by_cases hij : i = j
      rw [if_pos hij] at h1 h2 ⊢
      omega
      rw [if_neg hij] at h1 h2 ⊢
      omega
      have hsplit :=
        tuningWeight_fun_add m e (if · = j then q else 0)
      rw [hsplit, he2, hu]
      ring

section

variable (k : Type) [CommRing k] {S : Type} [CommRing S] [Algebra k S]

section
variable (J : Ideal S)
theorem tunedIdeal_pow_le m a n :
    tunedIdeal k J m a ^ n ≤ tunedIdeal k J m (n * a) := by
  induction n with
  | zero => simp [tunedIdeal_zero]
  | succ n ih =>
      let _a0 := tunedIdeal k J m a
      let _a1 := n + 1
      calc _a0 ^ _a1
          = _a0 ^ n * _a0 := pow_succ _ _
        _ ≤ tunedIdeal k J m (n * a) * _a0 := mul_mono ih le_rfl
        _ ≤ tunedIdeal k J m (n * a + a) := tunedIdeal_mul_le k J m _ _
        _ = tunedIdeal k J m (_a1 * a) := by
            rw [(by ring : n * a + a = _a1 * a)]

section
variable (m L) (hL : 0 < L) (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L)
include hL hdvd
theorem tunedIdeal_mul_eq_tunedIdeal_add r t (ht : (m - 1) * L ≤ t) :
    tunedIdeal k J m (r * L) * tunedIdeal k J m t = tunedIdeal k J m (r * L + t) := by
  refine le_antisymm (tunedIdeal_mul_le k J m _ _) ?_
  rw [tunedIdeal_le_iff]
  intro c hc
  obtain ⟨c', hc'le, hc'w⟩ := exists_le_tuningWeight_eq_mul m L r hL hdvd c $ le_trans (Nat.add_le_add_left ht $ r * L) hc
  have hsplit : tuningMonomial k J m c' * tuningMonomial k J m (fun j => c j - c' j)
      = tuningMonomial k J m c := by
    rw [tuningMonomial_mul_fun_add k J m c' fun j => c j - c' j, funext fun j => add_sub_cancel' $ hc'le j]
  rw [← hsplit]
  refine mul_mono (tuningMonomial_le_tunedIdeal k J m (r * L) c' $ le_of_eq hc'w.symm) ?_
  refine tuningMonomial_le_tunedIdeal k J m t _ ?_
  rw [tuningWeight_sub m c c' hc'le, hc'w]
  have h9 : ∀ A B W : ℕ, A + B ≤ W → B ≤ W - A := by
    intro A B W h
    omega
  exact h9 (r * L) t (tuningWeight m c) hc

section
variable (r) (hr : m - 1 ≤ r)
include hr
theorem tunedIdeal_pow_eq_tunedIdeal_mul j (hj : 1 ≤ j) :
    tunedIdeal k J m (r * L) ^ j = tunedIdeal k J m (j * (r * L)) := by
  induction j with
  | zero => exact absurd hj $ by omega
  | succ n ih =>
      rcases m73 n with hn | hn
      subst hn
      simp
      have hn1 := hn
      let _a0 := r * L
      have hmt : (m - 1) * L ≤ n * _a0 := by
        calc (m - 1) * L ≤ r * L := mul_le_mul hr $ le_refl L
          _ = 1 * _a0 := sy_ $ one_mul _
          _ ≤ n * _a0 := mul_le_mul hn1 $ le_refl $ r * L
      let _a1 := tunedIdeal k J m $ r * L
      let _a2 := n + 1
      let _a3 := tunedIdeal k J m $ n * _a0
      calc _a1 ^ _a2
          = _a1 ^ n * _a1 := pow_succ _ _
        _ = _a3 * _a1 := by rw [ih hn1]
        _ = _a1 * _a3 := mul_comm _ _
        _ = tunedIdeal k J m (r * L + n * _a0) :=
            tunedIdeal_mul_eq_tunedIdeal_add k J m L hL hdvd r (n * _a0) hmt
        _ = tunedIdeal k J m (_a2 * _a0) := by
            rw [(by ring : r * L + n * _a0 = _a2 * _a0)]

theorem derivIdealIterate_tunedIdeal_pow_le i (hi : i < r * L) :
    derivIdealIterate k i (tunedIdeal k J m $ r * L) ^ (r * L) ≤
      tunedIdeal k J m (r * L) ^ (r * L - i) := by
  let _a0 := r * L - i
  let _a1 := tunedIdeal k J m $ r * L
  let _a2 := r * L
  calc derivIdealIterate k i _a1 ^ _a2
      ≤ tunedIdeal k J m (r * L - i) ^ _a2 :=
        pow_right_mono (derivIdealIterate_tunedIdeal_le k J m (r * L) i) $ r * L
    _ ≤ tunedIdeal k J m (r * L * _a0) := tunedIdeal_pow_le k J m (r * L - i) $ r * L
    _ = tunedIdeal k J m (_a0 * _a2) := by
        rw [mul_comm (r * L) $ r * L - i]
    _ = _a1 ^ _a0 :=
        (tunedIdeal_pow_eq_tunedIdeal_mul k J m L hL hdvd r hr (r * L - i) $ mpr_ one_le_iff_ne_zero $ sub_ne_zero_of_lt hi).symm
end
end
end

end

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

section
variable (k : Type) [Field k] (v : Type)
abbrev affineSpaceIsoSpecMvPolynomial :
    affineSpaceIndexedBy k v ≅ Spec (CommRingCat.of (MvPolynomial v k)) :=
  AffineSpace.SpecIso v $ CommRingCat.of k

def mvPolynomialToGlobalSections :
    MvPolynomial v k →+* Γ(affineSpaceIndexedBy k v, ⊤) :=
  ((affineSpaceIsoSpecMvPolynomial k v).hom.appTop).hom.comp
    ((GSpecIso $ CommRingCat.of (MvPolynomial v k)).inv).hom

theorem mvPolynomialToGlobalSections_apply
    p :
    mvPolynomialToGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((GSpecIso $ CommRingCat.of (MvPolynomial v k)).inv p) := rfl

def globalSectionsToMvPolynomial :
    Γ(affineSpaceIndexedBy k v, ⊤) →+* MvPolynomial v k :=
  ((GSpecIso $ CommRingCat.of (MvPolynomial v k)).hom).hom.comp
    ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop).hom

theorem globalSectionsToMvPolynomial_apply
    s :
    globalSectionsToMvPolynomial k v s =
      (GSpecIso $ CommRingCat.of (MvPolynomial v k)).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl
end

section
variable {X Y : Sch} (e : X ≅ Y)
theorem appTop_inv_hom_apply s :
    e.inv.appTop (e.hom.appTop s) = s := by
  rw [← m78, ← comp_appTop, e.inv_hom_id]
  simp

theorem appTop_hom_inv_apply s :
    e.hom.appTop (e.inv.appTop s) = s := by
  rw [← m78, ← comp_appTop, e.hom_inv_id]
  simp
end

section
variable (k : Type) [Field k] (v : Type)
def mvPolynomialEquivGlobalSections :
    MvPolynomial v k ≃+* Γ(affineSpaceIndexedBy k v, ⊤) where
  toFun := mvPolynomialToGlobalSections k v
  invFun := globalSectionsToMvPolynomial k v
  left_inv := by
    intro p
    rw [mvPolynomialToGlobalSections_apply, globalSectionsToMvPolynomial_apply, appTop_inv_hom_apply]
    simp
  right_inv := by
    intro s
    rw [globalSectionsToMvPolynomial_apply, mvPolynomialToGlobalSections_apply, Iso.hom_inv_id_apply,
      appTop_hom_inv_apply]
  map_mul' := map_mul $ mvPolynomialToGlobalSections k v
  map_add' := map_add $ mvPolynomialToGlobalSections k v

section
variable (p : MvPolynomial v k)
theorem mvPolynomialEquivGlobalSections_apply :
    mvPolynomialEquivGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((GSpecIso $ CommRingCat.of (MvPolynomial v k)).inv p) := rfl

theorem mvPolynomialEquivGlobalSections_basicOpen :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (Spec $ CommRingCat.of (MvPolynomial v k)).basicOpen
          ((GSpecIso $ CommRingCat.of (MvPolynomial v k)).inv p) := by
  rw [mvPolynomialEquivGlobalSections_apply, preimage_basicOpen]
  rfl

theorem mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (PrimeSpectrum.basicOpen p : Opens $ PrimeSpectrum $ MvPolynomial v k) := by
  rw [mvPolynomialEquivGlobalSections_basicOpen, basicOpen_eq_of_affine]
end

theorem mvPolynomialEquivGlobalSections_symm_apply
    s :
    (mvPolynomialEquivGlobalSections k v).symm s =
      (GSpecIso $ CommRingCat.of (MvPolynomial v k)).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl

@[simp]
theorem mvPolynomialEquivGlobalSections_X (i : v) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.X i) = AffineSpace.coord (Sp k) i := by
  have _i69 : (affineSpaceIsoSpecMvPolynomial k v).inv.appTop (m9 (Sp k) i) = isoI (GSpecIso $ m10 $ MvPolynomial v k) (m7 i) := by
    rw [AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord]
  rw [mvPolynomialEquivGlobalSections_apply, ← _i69, appTop_hom_inv_apply]

@[simp]
theorem mvPolynomialEquivGlobalSections_symm_coord (i : v) :
    (mvPolynomialEquivGlobalSections k v).symm (AffineSpace.coord (Sp k) i) =
      MvPolynomial.X i := by
  rw [← mvPolynomialEquivGlobalSections_X k v i, RingEquiv.symm_apply_apply]

theorem mvPolynomialEquivGlobalSections_C c :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.C c) =
      (affineSpaceIndexedByToSpec k v).appTop ((GSpecIso $ CommRingCat.of k).inv c) := by
  rw [mvPolynomialEquivGlobalSections_apply]
  have key : (affineSpaceIsoSpecMvPolynomial k v).inv.appTop
      (hAT (affineSpaceIndexedByToSpec k v) $ isoI (GSpecIso $ m10 k) c) =
      (GSpecIso $ m10 $ MvPolynomial v k).inv (m8 c) := by
    rw [← m78, ← comp_appTop]
    simp
    rw [← m78, ← (Scheme.ΓSpecIso_inv_naturality _), m78]
    simp
  rw [← key, appTop_hom_inv_apply]
end



variable {R : Type} [CommRing R] {σ ta_ : Type}

section

def GraphAlgebra (_f : ta_ → MvPolynomial σ R) : Type := MvPolynomial σ R

instance instCommRingGraphAlgebra (f : ta_ → MvPolynomial σ R) : CommRing $ GraphAlgebra f :=
  inferInstanceAs $ CommRing $ MvPolynomial σ R

instance instAlgebraGraphAlgebra (f : ta_ → MvPolynomial σ R) : Algebra R $ GraphAlgebra f :=
  inferInstanceAs $ Algebra R $ MvPolynomial σ R

section
variable (f : ta_ → MvPolynomial σ R)
def graphAlgebraEquiv : MvPolynomial σ R ≃ₐ[R] GraphAlgebra f :=
  AlgEquiv.refl

def aevalGraphAlgebra : MvPolynomial ta_ R →ₐ[R] GraphAlgebra f :=
  (graphAlgebraEquiv f).toAlgHom.comp $ MvPolynomial.aeval f
end

instance instAlgebraBaseGraphAlgebra (f : ta_ → MvPolynomial σ R) :
    Algebra (MvPolynomial ta_ R) $ GraphAlgebra f :=
  (aevalGraphAlgebra f).toRingHom.toAlgebra

section
variable (f : ta_ → MvPolynomial σ R)
theorem algebraMap_graphAlgebra p :
    algebraMap (MvPolynomial ta_ R) (GraphAlgebra f) p = graphAlgebraEquiv f (MvPolynomial.aeval f p) :=
  rfl



def graphRelation (i : ta_) : MvPolynomial σ $ MvPolynomial ta_ R :=
  MvPolynomial.C (MvPolynomial.X i)
    - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial ta_ R) (f i)

abbrev graphRelationIdeal : Ideal $ MvPolynomial σ $ MvPolynomial ta_ R :=
  Ideal.span $ Set.range $ graphRelation f

def graphAlgebraAeval :
    MvPolynomial σ (MvPolynomial ta_ R) →ₐ[MvPolynomial ta_ R] GraphAlgebra f :=
  MvPolynomial.aeval fun i : σ => graphAlgebraEquiv f $ MvPolynomial.X i

theorem graphAlgebraAeval_X i :
    graphAlgebraAeval f (MvPolynomial.X i) = graphAlgebraEquiv f (MvPolynomial.X i) :=
  aeval_X _ i

theorem graphAlgebraAeval_C a :
    graphAlgebraAeval f (MvPolynomial.C a) = graphAlgebraEquiv f (MvPolynomial.aeval f a) := by
  have h : graphAlgebraAeval f (m8 a)
      = algebraMap (MvPolynomial ta_ R) (GraphAlgebra f) a := by
    simp [graphAlgebraAeval]
  rw [h, algebraMap_graphAlgebra]

theorem graphAlgebraAeval_map_C p :
    graphAlgebraAeval f (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial ta_ R) p)
      = graphAlgebraEquiv f p := by
  induction p using induction_on with
  | C r =>
      simp only [map_C, graphAlgebraAeval_C, aeval_C,
        m185]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, map_X, hp, graphAlgebraAeval_X]

theorem graphAlgebraAeval_map_C_graphAlgebraEquiv_symm x :
    graphAlgebraAeval f (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial ta_ R)
      ((graphAlgebraEquiv f).symm x)) = x := by
  rw [graphAlgebraAeval_map_C, AlgEquiv.apply_symm_apply]

def graphSubstitutionHom :
    MvPolynomial σ (MvPolynomial ta_ R) →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.aeval f : MvPolynomial ta_ R →ₐ[R] MvPolynomial σ R).toRingHom)
    MvPolynomial.X

theorem graphSubstitutionHom_C a :
    graphSubstitutionHom f (MvPolynomial.C a) = MvPolynomial.aeval f a := by
  simp [graphSubstitutionHom]

theorem graphSubstitutionHom_X i :
    graphSubstitutionHom f (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [graphSubstitutionHom]

section
variable (p : MvPolynomial σ (MvPolynomial ta_ R))
theorem graphAlgebraAeval_eq_graphAlgebraEquiv_graphSubstitutionHom :
    graphAlgebraAeval f p = graphAlgebraEquiv f (graphSubstitutionHom f p) := by
  induction p using induction_on with
  | C a => rw [graphAlgebraAeval_C, graphSubstitutionHom_C]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X q i hq => simp [map_mul, hq, graphAlgebraAeval_X, graphSubstitutionHom_X]

theorem sub_map_C_mem_graphRelationIdeal :
    p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial ta_ R) (graphSubstitutionHom f p)
      ∈ graphRelationIdeal f := by
  induction p using induction_on with
  | C a =>
      rw [graphSubstitutionHom_C]
      induction a using induction_on with
      | C r =>
          have key : (m8 (m8 r) :
                MvPolynomial σ $ MvPolynomial ta_ R)
              - m45 m8
                (m165 f $ m8 r) = 0 := by
            simp
          rw [key]
          exact m216 _
      | add p q hp hq =>
          have key : (m8 (p + q) : MvPolynomial σ $ MvPolynomial ta_ R)
              - m45 m8
                (m165 f $ p + q)
              = m8 p - m45 m8
                  (m165 f p)
                + (m8 q - m45 m8
                  (m165 f q)) := by
            simp [map_add]
            ring
          rw [key]
          exact m128 _ hp hq
      | mul_X p j hp =>
          have key : (m8 (p * m7 j) : MvPolynomial σ $ MvPolynomial ta_ R)
              - m45 m8
                (m165 f $ p * m7 j)
              = m8 p * graphRelation f j
                + (m8 p - m45 m8
                    (m165 f p))
                  * m45 m8 (f j) := by
            simp [graphRelation, map_mul]
            ring
          rw [key]
          exact m128 _ (mul_mem_left _ _ $ m100 ⟨j, rfl⟩) $ mul_mem_right _ _ hp
  | add p q hp hq =>
      have key : p + q
          - m45 m8 (graphSubstitutionHom f $ p + q)
          = p - m45 m8 (graphSubstitutionHom f p)
            + (q - m45 m8
                (graphSubstitutionHom f q)) := by
        simp [map_add]
        ring
      rw [key]
      exact m128 _ hp hq
  | mul_X q i hq =>
      have key : q * m7 i
          - m45 m8
              (graphSubstitutionHom f $ q * m7 i)
          = (q - m45 m8 (graphSubstitutionHom f q))
            * m7 i := by
        simp [map_mul, graphSubstitutionHom_X, map_X]
        ring
      rw [key]
      exact mul_mem_right _ _ hq
end

def graphAlgebraGenerators :
    Generators (MvPolynomial ta_ R) (GraphAlgebra f) σ where
  val := fun i => graphAlgebraEquiv f $ MvPolynomial.X i
  σ' := fun x =>
    MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial ta_ R) $ (graphAlgebraEquiv f).symm x
  aeval_val_σ' := graphAlgebraAeval_map_C_graphAlgebraEquiv_symm f

theorem mem_ker_graphAlgebraGenerators_iff
    p :
    p ∈ (graphAlgebraGenerators f).ker ↔ graphAlgebraAeval f p = 0 := m22

def graphPresentation :
    Presentation (MvPolynomial ta_ R) (GraphAlgebra f) σ ta_ where
  toGenerators := graphAlgebraGenerators f
  relation := graphRelation f
  span_range_relation_eq_ker := by
    apply le_antisymm
    · rw [span_le]
      rintro x ⟨i, rfl⟩
      simp only [mem_coe]
      have _i72 : graphAlgebraAeval f (graphRelation f i) = 0 := by
        simp only [graphRelation, map_sub, graphAlgebraAeval_C, graphAlgebraAeval_map_C, aeval_X, sub_self]
      exact (mem_ker_graphAlgebraGenerators_iff f _).2 _i72
    · intro p hp
      have hp' := (mem_ker_graphAlgebraGenerators_iff f p).1 hp
      have h0 : graphSubstitutionHom f p = 0 := by
        have h1 := graphAlgebraAeval_eq_graphAlgebraEquiv_graphSubstitutionHom f p
        rw [hp'] at h1
        have h2 : graphAlgebraEquiv f (graphSubstitutionHom f p) = graphAlgebraEquiv f 0 := by
          rw [← h1, map_zero]
        exact (graphAlgebraEquiv f).injective h2
      have hmem := sub_map_C_mem_graphRelationIdeal f p
      rwa [h0, map_zero, sub_zero] at hmem

section
variable (v : ta_ → σ)
section
variable (hv : Injective v)
def graphPreSubmersivePresentation :
    PreSubmersivePresentation (MvPolynomial ta_ R) (GraphAlgebra f) σ ta_ where
  toPresentation := graphPresentation f
  map := v
  map_inj := hv

@[simp] theorem graphPreSubmersivePresentation_relation :
    (graphPreSubmersivePresentation f v hv).relation = graphRelation f :=
  rfl

@[simp] theorem graphPreSubmersivePresentation_map :
    (graphPreSubmersivePresentation f v hv).map = v :=
  rfl
end

def graphJacobianMinorMatrix : Matrix ta_ ta_ $ MvPolynomial σ R :=
  Matrix.of fun i j => pderiv (v i) $ f j

theorem graphJacobianMinorMatrix_apply i j :
    graphJacobianMinorMatrix f v i j = pderiv (v i) (f j) :=
  rfl
end
end

section
variable [Fintype ta_] [DecidableEq ta_] (f : ta_ → MvPolynomial σ R) (v) (hv : Injective v)
theorem graphPreSubmersivePresentation_jacobiMatrix :
    (graphPreSubmersivePresentation f v hv).jacobiMatrix
      = -((graphJacobianMinorMatrix f v).map
          (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial ta_ R) p)) := by
  ext i j
  rw [jacobiMatrix_apply]
  simp [graphPreSubmersivePresentation_relation, graphPreSubmersivePresentation_map,
    graphRelation, map_sub, pderiv_C, pderiv_map, zero_sub,
    Matrix.neg_apply, Matrix.map_apply, graphJacobianMinorMatrix_apply]

theorem graphPreSubmersivePresentation_jacobian :
    (graphPreSubmersivePresentation f v hv).jacobian
      = (-1 : GraphAlgebra f) ^ card ta_ * graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det := by
  let _a0 := graphJacobianMinorMatrix f v
  have hmap : (_a0.map
      (fun p => m45 (m8 : R →+* MvPolynomial ta_ R) p)).det
      = m45 (m8 : R →+* MvPolynomial ta_ R) _a0.det :=
    (map_det (m45 (m8 : R →+* MvPolynomial ta_ R))
      _a0).symm
  rw [jacobian_eq_jacobiMatrix_det,
    graphPreSubmersivePresentation_jacobiMatrix, det_neg, hmap, map_mul, map_pow,
    map_neg, map_one]
  congr 1
  exact graphAlgebraAeval_map_C f _
end

end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution

variable {R : Type} [CommRing R] {σ ta_ : Type}

section

variable [Fintype ta_] [DecidableEq ta_]
section
variable (f : ta_ → MvPolynomial σ R) (v : ta_ → σ)
abbrev graphJacobianMinorDet :
    GraphAlgebra f :=
  graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det

abbrev GraphAlgebraAway : Type :=
  Away $ graphJacobianMinorDet f v

def graphAlgebraAwayLocalizationPresentation :
    SubmersivePresentation (GraphAlgebra f) (GraphAlgebraAway f v) Unit Unit :=
  Algebra.SubmersivePresentation.localizationAway (S := GraphAlgebraAway f v) (r := graphJacobianMinorDet f v)
end

section
variable [hv2_0 : Fintype σ] (f : ta_ → MvPolynomial σ R) (v) (hv : Injective v)
include hv2_0
def graphAlgebraAwayPreSubmersivePresentation :
    PreSubmersivePresentation (MvPolynomial ta_ R) (GraphAlgebraAway f v) (Unit ⊕ σ) $ Unit ⊕ ta_ :=
  Algebra.PreSubmersivePresentation.comp (graphAlgebraAwayLocalizationPresentation f v).toPreSubmersivePresentation
    (graphPreSubmersivePresentation f v hv)

theorem isUnit_jacobian_presentation_graphAlgebraAway :
    IsUnit (graphAlgebraAwayPreSubmersivePresentation f v hv).jacobian := by
  rw [graphAlgebraAwayPreSubmersivePresentation,
    comp_jacobian_eq_jacobian_smul_jacobian,
    smul_def]
  let _a0 := GraphAlgebraAway f v
  have _i74 : IsUnit $ algebraMap (GraphAlgebra f) _a0 (graphPreSubmersivePresentation f v hv).jacobian := by
    rw [graphPreSubmersivePresentation_jacobian, map_mul, map_pow, map_neg, map_one]
    exact ((isUnit_one.neg).pow _).mul $ map_units (M := powers $ graphJacobianMinorDet f v) _a0
      ⟨graphJacobianMinorDet f v, mem_powers _⟩
  exact _i74.mul (graphAlgebraAwayLocalizationPresentation f v).jacobian_isUnit

def graphAlgebraAwaySubmersivePresentation :
    SubmersivePresentation (MvPolynomial ta_ R) (GraphAlgebraAway f v)
      (Unit ⊕ Fin (card σ)) $ Unit ⊕ Fin (card ta_) :=
  Algebra.SubmersivePresentation.reindex
    { toPreSubmersivePresentation := graphAlgebraAwayPreSubmersivePresentation f v hv
      jacobian_isUnit := isUnit_jacobian_presentation_graphAlgebraAway f v hv }
    (sumCongr (refl Unit) (equivFin σ).symm)
    (sumCongr (refl Unit) (equivFin ta_).symm)
end

end

end FunctorialResolution.EmbeddedResolution
end
section
namespace FunctorialResolution.EmbeddedResolution


variable {R : Type} [CommRing R] {σ ta_ : Type} [Fintype ta_] [DecidableEq ta_]

theorem smooth_specMap_algebraMap_graphAlgebraAway [Fintype σ]
    (f : ta_ → MvPolynomial σ R) (v : ta_ → σ) (hv : Injective v) :
    Smooth $ Spec.map $ ofHom $ algebraMap (MvPolynomial ta_ R) $ GraphAlgebraAway f v := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  let _a0 := MvPolynomial ta_ R
  let _a1 := GraphAlgebraAway f v
  have : Algebra.IsStandardSmooth _a0 _a1 :=
    by
    constructor
    exact ⟨Unit ⊕ Fin (card σ), Unit ⊕ Fin (card ta_), inferInstance, inferInstance,
      ⟨graphAlgebraAwaySubmersivePresentation f v hv⟩⟩
  let _m0 := algebraMap _a0 _a1
  show @Algebra.Smooth _ _ _ _ _m0.toAlgebra
  have h : _m0.toAlgebra =
      (inferInstance : Algebra _a0 _a1) :=
    algebra_ext _ _ fun _ => rfl
  rw [h]
  refine ⟨?_, ?_⟩ <;> infer_instance

instance instIsOpenImmersionSpecMapGraphAway
    (f : ta_ → MvPolynomial σ R) (v : ta_ → σ) :
    IsOpenImmersion
      (Spec.map $ ofHom $ algebraMap (GraphAlgebra f) $ GraphAlgebraAway f v) :=
  by
  have : IsLocalization.Away (graphJacobianMinorDet f v) $ GraphAlgebraAway f v := inferInstance
  exact IsOpenImmersion.of_isLocalization (graphJacobianMinorDet f v) ..

section
variable (f : ta_ → MvPolynomial σ R) (v : ta_ → σ)
theorem range_specMap_algebraMap_graphAlgebraAway :
    Set.range ⇑(Spec.map
        (ofHom $ algebraMap (GraphAlgebra f) $ GraphAlgebraAway f v)).base =
      (PrimeSpectrum.basicOpen (graphJacobianMinorDet f v) : Set $ PrimeSpectrum $ GraphAlgebra f) := by
  have h := PrimeSpectrum.localization_away_comap_range (R := GraphAlgebra f)
    (GraphAlgebraAway f v) $ graphJacobianMinorDet f v
  exact h

theorem specMap_algebraMap_graphAlgebraAway_eq_comp :
    Spec.map (ofHom $ algebraMap (MvPolynomial ta_ R) $ GraphAlgebraAway f v) =
      Spec.map (ofHom $ algebraMap (GraphAlgebra f) $ GraphAlgebraAway f v) ≫
        Spec.map (ofHom $ algebraMap (MvPolynomial ta_ R) $ GraphAlgebra f) := by
  rw [IsScalarTower.algebraMap_eq (MvPolynomial ta_ R) (GraphAlgebra f) $ GraphAlgebraAway f v, CommRingCat.ofHom_comp, m183]
end

end FunctorialResolution.EmbeddedResolution
end
section
open TopologicalSpace


namespace FunctorialResolution.EmbeddedResolution

theorem apply_mem_irreducibleComponent_iff_of_flat
    {X Y} (f : X ⟶ Y) [Flat f]
    {C} (hC : C ∈ irreducibleComponents ↥Y) x :
    (fun x => f x) x ∈ C ↔
      ∃ C', C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x => f x) '' C') = C := by
  constructor
  intro hx
  obtain ⟨et_, het_⟩ := m140 hC.1 $ isClosed_of_mem_irreducibleComponents C hC
  have het' := het_
  have hxmem := hx
  rw [← het'] at hxmem
  obtain ⟨x', hx'spec, hfx'⟩ := (AlgebraicGeometry.Flat.generalizingMap (f := f)) $ mpr_ specializes_iff_mem_closure hxmem
  refine ⟨irreducibleComponent x', irreducibleComponent_mem_irreducibleComponents x',
    ?_, ?_⟩
  have hsub : closure ({x'} : Set ↥X) ⊆ irreducibleComponent x' :=
    closure_minimal (Set.singleton_subset_iff.2 mem_irreducibleComponent)
      isClosed_irreducibleComponent
  exact hsub $ mp_ specializes_iff_mem_closure hx'spec
  have hsub : C ⊆ closure (f '' irreducibleComponent x') := by
    rw [← het']
    exact closure_minimal (Set.singleton_subset_iff.2 $ subset_closure ⟨x', mem_irreducibleComponent, hfx'⟩) isClosed_closure
  exact m15 (an2 hC ((isIrreducible_irreducibleComponent.image f f.base.hom.continuous.continuousOn).closure) hsub) hsub
  rintro ⟨C', -, hxC', rfl⟩
  exact subset_closure ⟨x, hxC', rfl⟩

end FunctorialResolution.EmbeddedResolution
end
end
-- BEGIN_E2_PROJ_Bundle00
noncomputable section
open CategoryTheory AlgebraicGeometry FunctorialResolution.EmbeddedResolution
abbrev p4 := @AlgebraicGeometry.Scheme.Opens.i
abbrev p10 := @EtaleCoordinates.coord
abbrev p27 := @EtaleCoordinates.partialDeriv
abbrev p45 := @support_comap_eq
end
-- END_E2_PROJ_Bundle00
