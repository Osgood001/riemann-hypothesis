module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobenius
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsMapAlgHomStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ContinuousUnitsInvOfContinuousCoeFiniteQpAlgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsEps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiltByRestrictScalarsOfResidualCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineUpperTriangularIffMemFiniteCocycles
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsTypeAndIsLocallyCrystallineRz
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module
  UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology TensorProduct
open UpperTheory.V.UnitaryThreeInertia (psi)
open UpperTheory (filtBy_restrictScalars_of_residual_characters
  isCrystalline_extension_iff_mem_finiteCocycles isCrystalline_upperTriangular_iff_mem_finiteCocycles
  continuous_units_inv_of_continuous_coe_finite_Qp_algebra)
open GlobalTheory.OrdLoc (fr_isFr hl_basic)
open OrdinaryDeformation (qcont_map cont_col glue_hom dcr_pair map_conjBy conjBy_left conjBy_right)
open Matrix (diagonal scalar GeneralLinearGroup)

namespace GlobalTheory.OrdLoc.CrystallineLocus

/-! ### Part 1: Linear algebra, local rings, and general Galois cohomology -/

private theorem exists_GL_conj_eq_diagonal {R : Type} [CommRing R] [IsLocalRing R]
    (A : Matrix (Fin 3) (Fin 3) R) (p : Fin 3 → R)
    (hp : ∀ a b, a ≠ b → IsUnit (p a - p b)) (hchar : A.charpoly = ∏ a, (X - C (p a))) :
    ∃ h : GL (Fin 3) R, (h : Matrix (Fin 3) (Fin 3) R) * A *
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = diagonal p := by
  classical
  let P (a : Fin 3) : R[X] := ∏ b ∈ Finset.univ.erase a, (X - C (p b))
  let E (a : Fin 3) : Matrix (Fin 3) (Fin 3) R := aeval A (P a)
  have hfull (a) : (X - C (p a)) * P a = ∏ b, (X - C (p b)) :=
    Finset.mul_prod_erase Finset.univ (fun b => X - C (p b)) (Finset.mem_univ a)
  have hz : aeval A (∏ b, (X - C (p b))) = 0 := by rw [← hchar]; exact Matrix.aeval_self_charpoly A
  have key (f : R[X]) (a) : aeval A (f * P a) = f.eval (p a) • E a := by
    have hsplit := modByMonic_add_div f (X - C (p a))
    rw [modByMonic_X_sub_C_eq_C_eval] at hsplit
    conv_lhs => rw [← hsplit]
    rw [add_mul, mul_comm (X - C (p a)), mul_assoc, hfull]
    simp only [map_add (f := _), map_mul, hz, mul_zero, add_zero, aeval_C, Algebra.smul_def, E]
  have hq (a) : IsUnit ((P a).eval (p a)) := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun b hb => hp a b (Finset.ne_of_mem_erase hb).symm)
  have hq0 (a b) (hab : a ≠ b) : (P a).eval (p b) = 0 := by
    simp only [P, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩) (sub_self _)
  have hBA (a) : E a * A = p a • E a := by
    have h := key X a; rwa [mul_comm, map_mul, aeval_X, eval_X] at h
  have hBB (a b) : E a * E b = (P a).eval (p b) • E b := by rw [← map_mul]; exact key (P a) b
  have hex (a : Fin 3) : ∃ i j, IsUnit (E a i j) := by
    by_contra hne; push Not at hne
    let k := ResidueField R
    let φ : R →+* k := residue R
    have hmap : φ.mapMatrix (E a) = 0 := by
      ext i j; exact (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 (hne i j))
    have hcomm (q : R[X]) : φ.mapMatrix (aeval A q) = aeval (φ.mapMatrix A) (q.map φ) := by
      induction q using Polynomial.induction_on' with
      | add r s hr hs => simp [map_add, hr, hs]
      | monomial n c =>
        simp only [aeval_monomial, map_monomial, map_mul, map_pow]
        congr 1; ext i j; by_cases h : i = j <;> simp [Algebra.algebraMap_eq_smul_one, h]
    have hdet : (scalar (Fin 3) (φ (p a)) - φ.mapMatrix A).det = 0 := by
      rw [← Matrix.eval_charpoly, RingHom.mapMatrix_apply, Matrix.charpoly_map, hchar, Polynomial.map_prod, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hvA : (φ.mapMatrix A).mulVec v = φ (p a) • v := by
      ext i
      have hi := congrFun hv i
      simp only [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.sub_apply,
        Pi.zero_apply, sub_eq_zero] at hi
      simpa [Pi.smul_apply, smul_eq_mul] using hi.symm
    have hpow (m : ℕ) : (φ.mapMatrix A ^ m).mulVec v = φ (p a) ^ m • v := by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hvA, smul_smul, pow_succ]
    have hvpoly (q : R[X]) : (aeval (φ.mapMatrix A) (q.map φ)).mulVec v = φ (q.eval (p a)) • v := by
      induction q using Polynomial.induction_on' with
      | add r s hr hs =>
        rw [Polynomial.map_add, map_add, Matrix.add_mulVec, hr, hs, eval_add, map_add, add_smul]
      | monomial n c =>
        rw [Polynomial.map_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
          Matrix.one_mul, Matrix.smul_mulVec, hpow, eval_monomial, map_mul, map_pow, smul_smul]
    have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M.mulVec v) hmap
    rw [Matrix.zero_mulVec, hcomm, hvpoly] at h0
    rcases smul_eq_zero.1 h0 with h | h
    · exact ((residue_ne_zero_iff_isUnit _).2 (hq a)) h
    · exact hv0 h
  choose i j hij using hex
  let H : Matrix (Fin 3) (Fin 3) R := Matrix.of fun a k => E a (i a) k
  let Q : Matrix (Fin 3) (Fin 3) R := Matrix.of fun k b => E b k (j b)
  have hHQ : H * Q = diagonal fun a => (P a).eval (p a) * E a (i a) (j a) := by
    ext a b
    change (E a * E b) (i a) (j b) = _
    rw [hBB, Matrix.smul_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp
    · rw [hq0 a b hab, zero_mul, Matrix.diagonal_apply_ne _ hab]
  have hdetH : IsUnit H.det := by
    have h2 : IsUnit (H * Q).det := by
      rw [hHQ, Matrix.det_diagonal]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun a _ => (hq a).mul (hij a))
    rw [Matrix.det_mul] at h2; exact isUnit_of_mul_isUnit_left h2
  have hHA : H * A = diagonal p * H := by
    ext a k; change (E a * A) (i a) k = _; rw [hBA, Matrix.diagonal_mul]; simp [H]
  have hU := (Matrix.isUnit_iff_isUnit_det H).2 hdetH
  exact ⟨hU.unit, by rw [IsUnit.unit_spec, hHA, mul_assoc, hU.mul_val_inv, mul_one]⟩

private theorem exists_coefficientField {l : ℕ} [Fact l.Prime] (B : Type) [CommRing B] [IsLocalRing B]
    [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] :
    ∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[l] E) (_ : FiniteDimensional ℚ_[l] E)
      (_ : Algebra E B) (_ : IsScalarTower ℚ_[l] E B) (π : B →ₐ[E] E), ∀ a, π a = 0 → IsNilpotent a := by
  have : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  let g : B →ₐ[ℚ_[l]] ResidueField B := Ideal.Quotient.mkₐ ℚ_[l] (maximalIdeal B)
  have : Algebra.FormallyEtale ℚ_[l] (ResidueField B) := Algebra.FormallyEtale.of_isSeparable ℚ_[l] _
  have hker : RingHom.ker (g : B →+* ResidueField B) = maximalIdeal B := Ideal.mk_ker
  have hnil : IsNilpotent (RingHom.ker (g : B →+* ResidueField B)) := by
    rw [hker, ← ringJacobson_eq_maximalIdeal]; exact IsArtinianRing.isNilpotent_jacobson B
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id ℚ_[l] _) g Ideal.Quotient.mk_surjective hnil
  let alg : Algebra (ResidueField B) B := s.toRingHom.toAlgebra
  have tower : IsScalarTower ℚ_[l] (ResidueField B) B := IsScalarTower.of_algebraMap_eq fun r => (s.commutes r).symm
  refine ⟨ResidueField B, inferInstance, inferInstance, inferInstance, alg, tower,
    { (g : B →+* ResidueField B) with
      commutes' := Algebra.FormallySmooth.liftOfSurjective_apply _ g Ideal.Quotient.mk_surjective hnil },
    fun a ha => Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr (by rw [← hker]; exact ha)⟩

private theorem exists_finite_local_lift {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (J : Ideal R) (d : R)
    (hreg : ∀ a, d * a ∈ J → a ∈ J)
    (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
    [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B]
    (f : R →ₐ[O] B) (hJf : J ≤ RingHom.ker f) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsLocalRing B') (_ : Algebra ℚ_[l] B') (_ : Module.Finite ℚ_[l] B')
      (_ : Algebra O B') (_ : Algebra ℤ_[l] B') (_ : IsScalarTower ℤ_[l] O B') (_ : IsScalarTower ℤ_[l] ℚ_[l] B')
      (f' : R →ₐ[O] B') (q : B' →ₐ[ℚ_[l]] B),
      J ≤ RingHom.ker f' ∧ (∀ a, q (f' a) = f a) ∧ ∀ b, f' d * b = 0 → q b = 0 := by
  classical
  let mB := maximalIdeal B
  let M0 : Ideal R := mB.comap f
  let RM := Localization.AtPrime M0
  let mRM := maximalIdeal RM
  have hgu (y : M0.primeCompl) : IsUnit ((f : R →+* B) y) :=
    by_contra fun h => Ideal.mem_primeCompl_iff.1 y.2 ((mem_maximalIdeal _).2 h)
  let g : RM →+* B := IsLocalization.lift (M := M0.primeCompl) (S := RM) (g := (f : R →+* B)) hgu
  have hg (r : R) : g (algebraMap R RM r) = f r := IsLocalization.lift_eq hgu r
  let α : O →+* RM := (algebraMap R RM).comp (algebraMap O R)
  let ψ : ℤ_[l] →+* RM := α.comp (algebraMap ℤ_[l] O)
  have hfψ (y : ℤ_[l]) : g (ψ y) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] y) := by
    change g (algebraMap R RM (algebraMap O R (algebraMap ℤ_[l] O y))) = _
    rw [hg, f.commutes, ← IsScalarTower.algebraMap_apply ℤ_[l] O B y, ← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B y]
  have hψu (y : nonZeroDivisors ℤ_[l]) : IsUnit (ψ y) := by
    have hy0 : algebraMap ℤ_[l] ℚ_[l] y ≠ 0 := fun h =>
      nonZeroDivisors.coe_ne_zero y ((IsFractionRing.injective ℤ_[l] ℚ_[l]) (h.trans (map_zero _).symm))
    have hr : IsUnit (f (algebraMap O R (algebraMap ℤ_[l] O y))) := by
      rw [← hg]; have h1 := (isUnit_iff_ne_zero.2 hy0).map (algebraMap ℚ_[l] B); rwa [← hfψ y] at h1
    exact (IsLocalization.AtPrime.isUnit_to_map_iff RM M0 _).2
      (Ideal.mem_primeCompl_iff.2 fun h => ((mem_maximalIdeal _).1 h) hr)
  let φ : ℚ_[l] →+* RM := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) (S := ℚ_[l]) hψu
  have hφ (y : ℤ_[l]) : φ (algebraMap ℤ_[l] ℚ_[l] y) = ψ y := IsLocalization.lift_eq hψu y
  have hgφ : g.comp φ = algebraMap ℚ_[l] B := IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l])
    (RingHom.ext fun y => by simp only [RingHom.comp_apply, hφ, hfψ])
  have : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  obtain ⟨N0, hN0⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).1 inferInstance
  have hmaxg (x) (hx : x ∈ mRM ^ N0) : g x = 0 := by
    rw [show mRM = M0.map (algebraMap R RM) from (IsLocalization.AtPrime.map_eq_maximalIdeal M0 RM).symm,
      ← Ideal.map_pow] at hx
    refine RingHom.mem_ker.1 ((Ideal.map_le_iff_le_comap.2 fun r hr => ?_) hx)
    rw [Ideal.mem_comap, RingHom.mem_ker, hg]
    have h1 : f r ∈ (M0.map f) ^ N0 := by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem f hr
    have h2 := Ideal.pow_right_mono (Ideal.map_comap_le (f := (f : R →+* B))) N0 h1
    rwa [hN0, Submodule.zero_eq_bot, Ideal.mem_bot] at h2
  let J' : Ideal RM := J.map (algebraMap R RM)
  have hJg (x) (hx : x ∈ J') : g x = 0 :=
    RingHom.mem_ker.1 ((Ideal.map_le_iff_le_comap.2 fun r hr => by
      rw [Ideal.mem_comap, RingHom.mem_ker, hg]; exact RingHom.mem_ker.1 (hJf hr)) hx)
  let d' := algebraMap R RM d
  have hreg' (a : RM) (ha : d' * a ∈ J') : a ∈ J' := by
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M0.primeCompl a
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_map_algebraMap_iff] at ha
    obtain ⟨t, ht, htJ⟩ := ha
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨t, ht, hreg _ (by rwa [mul_left_comm])⟩
  let qd := Ideal.Quotient.mk J' d'
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul mRM (Submodule.span RM {qd})
  have hkey (c : RM) (hc : d' * c ∈ J' ⊔ mRM ^ (N0 + k)) : g c = 0 := by
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 hc
    have hx1 : Ideal.Quotient.mk J' (d' * c) ∈ (mRM ^ (N0 + k)) • (⊤ : Submodule RM (RM ⧸ J')) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hjy, map_add (f := _),
        Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
      exact Ideal.mem_map_of_mem _ hy
    have hx2 : Ideal.Quotient.mk J' (d' * c) ∈ Submodule.span RM {qd} := by
      rw [show Ideal.Quotient.mk J' (d' * c) = c • qd by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm c]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have h4 : Ideal.Quotient.mk J' (d' * c) ∈ mRM ^ (N0 + k - k) • (mRM ^ k • ⊤ ⊓ Submodule.span RM {qd}) := by
      rw [← hk (N0 + k) (by omega)]; exact Submodule.mem_inf.2 ⟨hx1, hx2⟩
    rw [Nat.add_sub_cancel] at h4
    obtain ⟨a, ha, hav⟩ := Submodule.mem_smul_span_singleton.1 (Submodule.smul_mono le_rfl inf_le_right h4)
    have hca : c - a ∈ J' := hreg' _ (by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mul_sub, map_sub, ← hav, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm a, sub_self])
    rw [show c = (c - a) + a by ring, map_add (f := _), hJg _ hca, hmaxg _ ha, add_zero]
  let I : Ideal RM := J' ⊔ mRM ^ (N0 + k)
  let mk := Ideal.Quotient.mk I
  have hIg (x) (hx : x ∈ I) : g x = 0 := by
    obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), hJg _ hj, hmaxg _ (Ideal.pow_le_pow_right (by omega) hy), add_zero]
  have : Nontrivial (RM ⧸ I) := Ideal.Quotient.nontrivial_iff.2 fun h => by
    have := hIg 1 (h ▸ Submodule.mem_top); simp at this
  have hloc : IsLocalRing (RM ⧸ I) := of_surjective' mk Ideal.Quotient.mk_surjective
  let aQ : Algebra ℚ_[l] (RM ⧸ I) := (mk.comp φ).toAlgebra
  let aO : Algebra O (RM ⧸ I) := (mk.comp α).toAlgebra
  let aZ : Algebra ℤ_[l] (RM ⧸ I) := (mk.comp ψ).toAlgebra
  have t1 : @IsScalarTower ℤ_[l] O (RM ⧸ I) _ aO.toSMul aZ.toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have t2 : IsScalarTower ℤ_[l] ℚ_[l] (RM ⧸ I) := IsScalarTower.of_algebraMap_eq fun x => by
    change mk (ψ x) = mk (φ (algebraMap ℤ_[l] ℚ_[l] x)); rw [hφ]
  let f' : R →ₐ[O] (RM ⧸ I) := { mk.comp (algebraMap R RM) with commutes' := fun _ => rfl }
  let q : (RM ⧸ I) →ₐ[ℚ_[l]] B :=
    { Ideal.Quotient.lift I g hIg with
      commutes' := fun c => by
        change Ideal.Quotient.lift I g hIg (mk (φ c)) = _
        rw [Ideal.Quotient.lift_mk]; exact RingHom.congr_fun hgφ c }
  have hmaxQ : maximalIdeal (RM ⧸ I) ≤ mRM.map mk := fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (by_contra fun hy =>
      ((mem_maximalIdeal _).1 hx) ((not_not.1 ((mem_maximalIdeal _).not.1 hy)).map _))
  have hnil : maximalIdeal (RM ⧸ I) ^ (N0 + k) = ⊥ := eq_bot_iff.2 <|
    (Ideal.pow_right_mono hmaxQ _).trans <| (Ideal.map_pow _ _ _).symm.le.trans <|
      (Ideal.map_mono le_sup_right).trans (Ideal.map_quotient_self I).le
  have : IsArtinianRing (RM ⧸ I) := (isArtinianRing_iff_isNilpotent_maximalIdeal _).2 ⟨N0 + k, hnil⟩
  have hfin : Module.Finite ℚ_[l] (RM ⧸ I) := by
    have hle : maximalIdeal (RM ⧸ I) ≤ mB.comap q := fun x hx => by
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hx0 : x ^ (N0 + k) = 0 := Ideal.mem_bot.1 (hnil ▸ Ideal.pow_mem_pow hx _)
      exact not_isUnit_zero (M₀ := B) (by simpa [← map_pow, hx0] using hu.pow (N0 + k))
    have : Module.Finite ℚ_[l] (B ⧸ mB) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[l] mB).toLinearMap (Ideal.Quotient.mkₐ_surjective ℚ_[l] _)
    have : Module.Finite ℚ_[l] ((RM ⧸ I) ⧸ Ring.jacobson (RM ⧸ I)) := by
      rw [ringJacobson_eq_maximalIdeal]
      exact Module.Finite.of_injective (Ideal.quotientMapₐ mB q hle).toLinearMap
        (Ideal.quotientMap_injective' (H := hle) (le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))))
    exact IsSemiprimaryRing.finite_of_isArtinian ℚ_[l] (RM ⧸ I) (RM ⧸ I)
  refine ⟨RM ⧸ I, inferInstance, hloc, aQ, hfin, aO, aZ, t1, t2, f', q,
    fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)),
    fun a => by change Ideal.Quotient.lift I g hIg (mk (algebraMap R RM a)) = _; rw [Ideal.Quotient.lift_mk, hg],
    fun b hb => by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
      change Ideal.Quotient.lift I g hIg (mk c) = 0
      rw [Ideal.Quotient.lift_mk]
      exact hkey c (Ideal.Quotient.eq_zero_iff_mem.1 (by rwa [map_mul]))⟩

private def glPart {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G)
    (r : G →* GG (m := m) (R := R)) (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem filtBy_of_exact {G E V₁ V V₂ : Type} [Group G] [Field E]
    [AddCommGroup V₁] [Module E V₁] [AddCommGroup V] [Module E V] [AddCommGroup V₂] [Module E V₂]
    {ρ₁ : Representation E G V₁} {ρ : Representation E G V} {ρ₂ : Representation E G V₂}
    {S : Set (G →* Eˣ)} (i : V₁ →ₗ[E] V) (p : V →ₗ[E] V₂)
    (hp : Function.Surjective p) (hex : LinearMap.ker p = LinearMap.range i)
    (hi : ∀ g x, i (ρ₁ g x) = ρ g (i x)) (hpρ : ∀ g x, p (ρ g x) = ρ₂ g (p x))
    (h1 : FiltBy ρ₁ S) (h2 : FiltBy ρ₂ S) : FiltBy ρ S := by
  obtain ⟨n₁, F₁, h0₁, hn₁, hs₁⟩ := h1
  obtain ⟨n₂, F₂, h0₂, hn₂, hs₂⟩ := h2
  have hmid : (F₁ n₁).map i = (F₂ 0).comap p := by
    rw [hn₁, h0₂, Submodule.map_top, ← hex, Submodule.comap_bot]
  let F : ℕ → Submodule E V := fun k => if k ≤ n₁ then (F₁ k).map i else (F₂ (k - n₁)).comap p
  have hF_ge (k : ℕ) (hk : n₁ ≤ k) : F k = (F₂ (k - n₁)).comap p := by
    by_cases h : k = n₁
    · subst h; simp [F, hmid]
    · simp [F, show ¬ k ≤ n₁ by omega]
  refine ⟨n₁ + n₂, F, by simp [F, h0₁], ?_, fun k hk => ?_⟩
  · rw [hF_ge (n₁ + n₂) (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hn₂, Submodule.comap_top]
  · by_cases hkn : k < n₁
    · obtain ⟨hle, κ, hκ, x, hFx, hact⟩ := hs₁ k hkn
      have h1' : k ≤ n₁ := hkn.le; have h2' : k + 1 ≤ n₁ := hkn
      refine ⟨by simpa [F, h1', h2'] using Submodule.map_mono hle, κ, hκ, i x, ?_, fun g => ?_⟩
      · simp only [F, h1', h2', ite_eq_left, hFx, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
      · simp only [F, h1', ite_eq_left]
        exact ⟨ρ₁ g x - ((κ g : Eˣ) : E) • x, hact g, by rw [map_sub, map_smul, hi]⟩
    · have hkge : n₁ ≤ k := by omega
      obtain ⟨hle, κ, hκ, y, hFy, hact⟩ := hs₂ (k - n₁) (by omega)
      obtain ⟨x, rfl⟩ := hp y
      have hsub : k + 1 - n₁ = k - n₁ + 1 := by omega
      refine ⟨by rw [hF_ge k hkge, hF_ge (k + 1) (by omega), hsub]; exact Submodule.comap_mono hle,
        κ, hκ, x, ?_, fun g => ?_⟩
      · rw [hF_ge k hkge, hF_ge (k + 1) (by omega), hsub]
        refine le_antisymm (fun v hv => ?_) (sup_le (Submodule.comap_mono hle)
          (Submodule.span_le.2 (Set.singleton_subset_iff.2 (by
            show p x ∈ F₂ (k - n₁ + 1); rw [hFy]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))))
        obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (show p v ∈ F₂ (k - n₁) ⊔ E ∙ p x from hFy ▸ hv)
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
        have hvc : v - c • x ∈ (F₂ (k - n₁)).comap p := by
          show p (v - c • x) ∈ F₂ (k - n₁); rw [map_sub, map_smul, ← huw, add_sub_cancel_right]; exact hu
        rw [show v = (v - c • x) + c • x by abel]
        exact Submodule.add_mem_sup hvc (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      · rw [hF_ge k hkge]
        show p (ρ g x - ((κ g : Eˣ) : E) • x) ∈ F₂ (k - n₁)
        rw [map_sub, map_smul, hpρ]; exact hact g

private theorem actC_resCoef {l : ℕ} [Fact l.Prime] {G : Type} [Group G]
    {E : Type} [Field E] [Algebra ℚ_[l] E] (φ : G →* GQ l) {B : Type} [CommRing B] [Algebra ℚ_[l] B]
    [Algebra E B] [IsScalarTower ℚ_[l] E B] (ρ : Representation B G B) (g : G) (y : B ⊗[ℚ_[l]] Bcr l) :
    actC φ (resCoef E ρ) g y = actC φ ρ g y := by
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp [actC, resCoef]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

private theorem finrank_dualInv_eq_ker {G E : Type} [Group G] [Field E]
    {B : Type} [CommRing B] [Algebra E B] [Module.Finite E B]
    {N : Type} [AddCommGroup N] [Module B N] [Module E N] [IsScalarTower E B N] [Module.Finite E N]
    (χ : G →* Bˣ) (ε : G →* Eˣ) (ρ : Representation E G N) (hρ : ∀ g x, ρ g x = (χ g : B) • x)
    (δ : B) (hδ : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) = Ideal.span {δ}) :
    finrank E ↥(H0dual ε ρ) = finrank E ↥(LinearMap.ker ((LinearMap.lsmul B N δ).restrictScalars E)) := by
  let L := (LinearMap.lsmul B N δ).restrictScalars E
  have key : H0dual ε ρ = (LinearMap.range L).dualAnnihilator := by
    ext f
    rw [Submodule.mem_dualAnnihilator]
    let S : Ideal B :=
      { carrier := {b | ∀ x : N, f (b • x) = 0}
        add_mem' := fun ha hb x => by rw [add_smul, map_add (f := _), ha x, hb x, add_zero]
        zero_mem' := fun x => by simp
        smul_mem' := fun c b hb x => by rw [smul_eq_mul, mul_comm, mul_smul]; exact hb _ }
    have hgen (g) : (∀ x, f (ρ g x) = (ε g : E) * f x) ↔ ((χ g : B) - algebraMap E B (ε g)) ∈ S :=
      forall_congr' fun x => by rw [hρ, sub_smul, map_sub, algebraMap_smul, f.map_smul, smul_eq_mul, sub_eq_zero]
    constructor
    · intro h
      have hle : Ideal.span {δ} ≤ S := hδ ▸ Ideal.span_le.2 (by rintro _ ⟨g, rfl⟩; exact (hgen g).1 (h g))
      rintro _ ⟨x, rfl⟩; exact hle (Ideal.subset_span rfl) x
    · intro h g
      have hle : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) ≤ S := by
        rw [hδ, Ideal.span_le, Set.singleton_subset_iff]; exact fun x => h _ ⟨x, rfl⟩
      exact (hgen g).2 (hle (Ideal.subset_span ⟨g, rfl⟩))
  rw [key]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range L)
  have h2 := LinearMap.finrank_range_add_finrank_ker L
  change finrank E _ = finrank E ↥(LinearMap.ker L)
  omega

/-! ### Part 2: Positive-weight crystalline cohomology & local-to-global crystallinity -/

section PosCrys

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E]

omit [IsTopologicalGroup G] in
private theorem span_range_sub_cyc_top (φ : G →* GQ l) (hφ : IsOpenEmbedding φ)
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B]
    (χ : G →* Bˣ) (w : ℤ) (hw : 2 ≤ w) (hI : ∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) :
    Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = ⊤ := by
  obtain ⟨_, ⟨⟨g, rfl⟩, hg⟩, hs⟩ := ((cycInertia l).2 φ.range hφ.isOpen_range).2
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = ((n + 2 : ℕ) : ℤ) := ⟨(w - 2).toNat, by omega⟩
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨g, rfl⟩) ?_
  show IsUnit ((χ g : B) - (cycA l l B (φ g) : B))
  rw [hI g hg, zpow_natCast, Units.val_pow_eq_pow_val,
    show (cycA l l B (φ g) : B) = algebraMap ℚ_[l] B (((cyc l l (φ g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) from
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B _, ← map_pow, ← map_sub]
  refine IsUnit.map _ (Ne.isUnit fun h => hs (isOfFinOrder_iff_pow_eq_one.2 ⟨n + 1, n.succ_pos, ?_⟩))
  have h2 : cyc l l (φ g) ^ (n + 2) = cyc l l (φ g) := Units.ext <| Subtype.ext <| by
    rw [Units.val_pow_eq_pow_val]; push_cast; exact sub_eq_zero.1 h
  rw [pow_succ] at h2; exact mul_eq_right.1 h2

private theorem span_range_sub_cyc_one (φ : G →* GQ l) (hφ : IsOpenEmbedding φ)
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B]
    [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B]
    (χ : G →* Bˣ) (hχ : Continuous fun g => (χ g : B))
    (hI : ∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g))
    (σ : G) (hσ : ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤) :
    Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) =
      Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} := by
  refine le_antisymm ?_ (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨σ, rfl⟩))
  let J := Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)}
  have hJcl : IsClosed (J : Set B) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨f, hf, hJ⟩ := Submodule.exists_le_ker_of_notMem (p := J.restrictScalars ℚ_[l]) (v := x) hx
    exact Filter.mem_of_superset ((isOpen_ne.preimage (IsModuleTopology.continuous_of_linearMap f)).mem_nhds hf)
      fun y hy h => hy (hJ h)
  have hε : Continuous fun g => (cycA l l B (φ g) : B) := by
    have hA (g : GQ l) : (cycA l l B g : B) = algebraMap ℚ_[l] B (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) :=
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B _
    simp only [hA]
    have h2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
    exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] B)).comp
      (h2.comp (Units.continuous_val.comp ((cycFacts l l).1.comp hφ.continuous)))
  let q : Bˣ →* (B ⧸ J)ˣ := Units.map (Ideal.Quotient.mk J : B →* B ⧸ J)
  let H : Subgroup G := (q.comp χ).eqLocus (q.comp ((cycA l l B).comp φ))
  have hH (g) : g ∈ H ↔ (χ g : B) - (cycA l l B (φ g) : B) ∈ J := by rw [← Ideal.Quotient.eq]; exact Units.ext_iff
  have hcl : IsClosed (H : Set G) := by
    rw [show (H : Set G) = (fun g => (χ g : B) - (cycA l l B (φ g) : B)) ⁻¹' (J : Set B) from Set.ext hH]
    exact hJcl.preimage (hχ.sub hε)
  have htop := Subgroup.topologicalClosure_minimal ((Iq l).comap φ ⊔ Subgroup.zpowers σ)
    (sup_le (fun g hg => (hH g).2 (by rw [hI g hg, sub_self]; exact J.zero_mem))
      (Subgroup.zpowers_le.2 ((hH σ).2 (Ideal.subset_span rfl)))) hcl
  rw [hσ] at htop
  rw [Ideal.span_le]; rintro _ ⟨g, rfl⟩; exact (hH g).1 (htop (Subgroup.mem_top g))

private theorem cocycleDim_positive (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (hP : LocalPublishedTheorems)
    {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
    (ρ : Representation E G V) (hρ : ContAction ρ) (hpos : Positive φ ρ) :
    Module.Finite E ↥(Z1 ρ) ∧
      finrank E ↥(Z1 ρ) = finrank E ↥(finiteCocycles φ ρ) + finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) := by
  have : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite ℚ_[l] E V
  obtain ⟨hH0, -, hfinf, hdimf⟩ := posBasic hP φ hφ ρ hρ hpos
  obtain ⟨hf1, -, e1, e2⟩ := tateRat hP (v := l) (l := l) φ hφ ρ hρ
  simp only [↓reduceIte] at e1; rw [hH0, finrank_bot, e2] at e1
  have hBf : Module.Finite E ↥(B1 ρ) := by unfold B1; infer_instance
  have sandwich (S : Submodule E (G → V)) (hBS : B1 ρ ≤ S) (hSZ : S ≤ Z1 ρ)
      (hQ : Module.Finite E ↥((S.comap (Z1 ρ).subtype).map ((B1 ρ).comap (Z1 ρ).subtype).mkQ)) :
      Module.Finite E S ∧
        finrank E S = finrank E ↥((S.comap (Z1 ρ).subtype).map ((B1 ρ).comap (Z1 ρ).subtype).mkQ) + finrank E ↥(B1 ρ) := by
    let f : S →ₗ[E] (Z1 ρ ⧸ (B1 ρ).comap (Z1 ρ).subtype) :=
      ((B1 ρ).comap (Z1 ρ).subtype).mkQ ∘ₗ Submodule.inclusion hSZ
    have hr : LinearMap.range f = (S.comap (Z1 ρ).subtype).map ((B1 ρ).comap (Z1 ρ).subtype).mkQ := by
      rw [LinearMap.range_comp, Submodule.range_inclusion]
    have hk : LinearMap.ker f = (B1 ρ).comap S.subtype := by ext x; simp [f]
    have eB := Submodule.comapSubtypeEquivOfLe hBS
    have hkf : Module.Finite E ↥(LinearMap.ker f) := by rw [hk]; exact Module.Finite.equiv eB.symm
    have hrf : Module.Finite E ↥(LinearMap.range f) := by rw [hr]; exact hQ
    have hS : Module.Finite E S := Module.finite_def.2 (Submodule.fg_of_fg_map_of_fg_inf_ker f
      (by rw [Submodule.map_top]; exact Module.Finite.iff_fg.1 hrf)
      (by rw [top_inf_eq]; exact Module.Finite.iff_fg.1 hkf))
    exact ⟨hS, by rw [← LinearMap.finrank_range_add_finrank_ker f, hr, hk, eB.finrank_eq]⟩
  obtain ⟨-, hSd⟩ := sandwich _ ((z1fMap (l := l) φ ρ ρ).1 hρ) (fun _ h => h.1) hfinf
  have htop : ((Z1 ρ).comap (Z1 ρ).subtype).map ((B1 ρ).comap (Z1 ρ).subtype).mkQ = ⊤ := by
    rw [Submodule.comap_subtype_self, Submodule.map_top, Submodule.range_mkQ]
  obtain ⟨hZ, hZd⟩ := sandwich _ (coboundaries_le_cocycles ρ hρ) le_rfl
    (by rw [htop]; exact Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl).symm)
  rw [htop, finrank_top] at hZd
  refine ⟨hZ, ?_⟩
  change finrank E ↥(Z1 ρ) = finrank E (H1 ρ) + finrank E ↥(B1 ρ) at hZd
  change finrank E ↥(finiteCocycles φ ρ) = finrank E ↥(finiteCohomology φ ρ) + finrank E ↥(B1 ρ) at hSd
  omega

private theorem cocycle_eq_crys_add_sub (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (hP : LocalPublishedTheorems)
    {W V : Type} [AddCommGroup W] [Module E W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] E W]
    [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W]
    [IsTopologicalAddGroup W] [ContinuousConstSMul E W]
    [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
    (ρW : Representation E G W) (ρ : Representation E G V)
    (hcW : ContAction ρW) (hc : ContAction ρ) (hpW : Positive φ ρW) (hp : Positive φ ρ)
    (i : W →ₗ[E] V) (hi : Function.Injective i) (hiρ : ∀ g x, i (ρW g x) = ρ g (i x))
    (hdim : finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρ))
    (c : G → V) (hcZ : c ∈ Z1 ρ) :
    ∃ c' ∈ Z1 ρW, (c - fun g => i (c' g)) ∈ finiteCocycles φ ρ := by
  obtain ⟨hfinW, hdW⟩ := cocycleDim_positive φ hφ hP ρW hcW hpW
  obtain ⟨hfin, hd⟩ := cocycleDim_positive φ hφ hP ρ hc hp
  have hic : Continuous i := IsModuleTopology.continuous_of_linearMap (i.restrictScalars ℚ_[l])
  let S := (finiteCocycles φ ρ).comap (Z1 ρ).subtype
  let SW := (finiteCocycles φ ρW).comap (Z1 ρW).subtype
  let M : Z1 ρW →ₗ[E] Z1 ρ := LinearMap.codRestrict (Z1 ρ) ((LinearMap.compLeft i G).comp (Z1 ρW).subtype)
    (fun c' => ⟨hic.comp c'.2.1, fun g h => by simp [c'.2.2 g h, map_add, hiρ]⟩)
  let L : Z1 ρW →ₗ[E] Z1 ρ ⧸ S := S.mkQ ∘ₗ M
  have hker : LinearMap.ker L = SW := by
    ext c'
    simp only [L, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      S, SW, Submodule.mem_comap, Submodule.subtype_apply]
    exact ⟨fun h => (posExact hP φ hφ ρW ρ hcW hc hpW i hiρ).2 hi hp _ c'.2 h,
      fun h => (z1fMap φ ρW ρ).2 (i.restrictScalars ℚ_[l]) (fun g x => hiρ g x) _ h⟩
  have eW : SW ≃ₗ[E] finiteCocycles φ ρW := Submodule.comapSubtypeEquivOfLe fun _ h => h.1
  have eV : S ≃ₗ[E] finiteCocycles φ ρ := Submodule.comapSubtypeEquivOfLe fun _ h => h.1
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := Submodule.finrank_quotient_add_finrank S
  rw [hker, eW.finrank_eq] at h1; rw [eV.finrank_eq] at h2
  have hr : LinearMap.range L = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  obtain ⟨c', hc'⟩ : S.mkQ ⟨c, hcZ⟩ ∈ LinearMap.range L := hr ▸ Submodule.mem_top
  exact ⟨c', c'.2, (Submodule.Quotient.eq S).1 hc'.symm⟩

section PosCrysB

variable {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
  [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B]
  [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B]

omit [FiniteDimensional ℚ_[l] E] [IsTopologicalRing B] in
private theorem positive_scalar_rep (φ : G →* GQ l) (hφ : IsOpenEmbedding φ)
    (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a)
    (χ : G →* Bˣ) (hχc : Continuous fun g => (χ g : B)) (w : ℤ) (hw : 1 ≤ w)
    (hχI : ∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w)
    {N : Type} [AddCommGroup N] [Module B N] [Module E N] [Module ℚ_[l] N]
    [IsScalarTower E B N] [IsScalarTower ℚ_[l] E N] [IsScalarTower ℚ_[l] B N]
    [FiniteDimensional ℚ_[l] N] [TopologicalSpace N] [IsModuleTopology ℚ_[l] N] [IsTopologicalAddGroup N]
    (ρ : Representation E G N) (hρ : ∀ g x, ρ g x = (χ g : B) • x) :
    ContAction ρ ∧ Positive φ ρ := by
  let bil : B →ₗ[ℚ_[l]] N →ₗ[ℚ_[l]] N := LinearMap.mk₂ ℚ_[l] (fun b x => b • x) (fun _ _ _ => add_smul _ _ _)
    (fun c b x => smul_assoc c b x) (fun _ _ _ => smul_add _ _ _)
    (fun c b x => by rw [← algebraMap_smul B c x, ← algebraMap_smul B c (b • x), smul_smul, smul_smul, mul_comm])
  have hcont : ContAction ρ := by
    unfold ReciprocityTheory.Gal.ContAction; simp only [hρ]
    exact (IsModuleTopology.continuous_bilinear_of_finite_left bil).comp ((hχc.comp continuous_fst).prodMk continuous_snd)
  have : ContinuousConstSMul E N := ⟨fun c => IsModuleTopology.continuous_of_linearMap
    ((LinearMap.lsmul E N c).restrictScalars ℚ_[l])⟩
  have hcr : IsCr φ ρ := crUnr φ hφ ρ hcont w fun g hg x => by
    rw [hρ, hχI g hg, ← algebraMap_smul B (((cycA l l E (φ g) ^ w : Eˣ) : E)) x,
      ← algebraMap_cycA (E := E) (B := B), ← map_zpow]; rfl
  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have : Module.Finite B N := Module.Finite.of_restrictScalars_finite ℚ_[l] B N
  obtain ⟨_, s, hs⟩ := Module.Finite.exists_fin (R := B) (M := N)
  let ρB : Representation B G N :=
    { toFun := fun g => ((χ g : Bˣ) : B) • LinearMap.id
      map_one' := by ext; simp
      map_mul' := fun g h => LinearMap.ext fun x => by
        simp only [map_mul, Units.val_mul, mul_apply_eq_comp, LinearMap.smul_apply, LinearMap.id_apply, mul_smul] }
  let κ : G →* Eˣ := (Units.map (π : B →* E)).comp χ
  have hres : resCoef E ρB = ρ := MonoidHom.ext fun g => LinearMap.ext fun x => (hρ g x).symm
  have hκ : κ ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} :=
    ⟨w, hw, ⊤, by simp, fun g _ hg => Units.ext <| by
      change π ((χ g : Bˣ) : B) = _
      rw [hχI g hg, ← algebraMap_cycA (E := E) (B := B), ← map_zpow]; exact π.commutes _⟩
  refine ⟨hcont, (isCrys_isDR_restrict_openSubgroup φ hφ ρ hcont).1 hcr, ?_⟩
  rw [← hres]
  refine filtBy_restrictScalars_of_residual_characters π hπ ρB _ s (fun _ => κ) hs (fun _ => hκ) fun g j => ?_
  have hm : ((χ g : B) - algebraMap E B (π (χ g : B))) • s j ∈ (RingHom.ker (π : B →+* E)) • (⊤ : Submodule B N) :=
    Submodule.smul_mem_smul (by simp) trivial
  convert hm using 1; rw [sub_smul, algebraMap_smul]; rfl

private theorem cocycle_crys_add_ann (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (hP : LocalPublishedTheorems)
    (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a)
    (χ : G →* Bˣ) (hχc : Continuous fun g => (χ g : B)) (w : ℤ) (hw : 1 ≤ w)
    (hχI : ∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w)
    (δ : B) (hspan : Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = Ideal.span {δ})
    (c : G → B) (hc : c ∈ Z1 (chRep χ)) :
    ∃ c' : G → B, (∀ g, δ * c' g = 0) ∧ c - c' ∈ finiteCocycles φ (chRep χ) := by
  have : ContinuousConstSMul E B := contConstSMul_alg E
  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hspanE : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E)) =
      Ideal.span {δ} := by
    have e (g) : algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E) = (cycA l l B (φ g) : B) :=
      congrArg Units.val (algebraMap_cycA (E := E) (B := B) (φ g))
    simpa only [e] using hspan
  let I : Submodule B B := LinearMap.ker (LinearMap.lsmul B B δ)
  let : TopologicalSpace I := moduleTopology ℚ_[l] I
  have : IsModuleTopology ℚ_[l] I := ⟨rfl⟩
  have : IsTopologicalAddGroup I := IsModuleTopology.isTopologicalAddGroup ℚ_[l] I
  have : ContinuousConstSMul E I := ⟨fun a => IsModuleTopology.continuous_of_linearMap
    ((LinearMap.lsmul E I a).restrictScalars ℚ_[l])⟩
  have : FiniteDimensional ℚ_[l] I := Module.Finite.of_injective (I.subtype.restrictScalars ℚ_[l]) Subtype.val_injective
  let ρV : Representation E G B := resCoef E (chRep χ)
  let ρW : Representation E G I :=
    { toFun := fun g => (LinearMap.lsmul B I (χ g : B)).restrictScalars E
      map_one' := by ext; simp
      map_mul' := fun g h => LinearMap.ext fun x => by
        simp only [map_mul, Units.val_mul, mul_apply_eq_comp, LinearMap.restrictScalars_apply,
          LinearMap.lsmul_apply, mul_smul] }
  have hV := positive_scalar_rep φ hφ π hπ χ hχc w hw hχI ρV fun _ _ => rfl
  have hW := positive_scalar_rep φ hφ π hπ χ hχc w hw hχI ρW fun _ _ => rfl
  have dV := finrank_dualInv_eq_ker χ ((cycA l l E).comp φ) ρV (fun _ _ => rfl) δ hspanE
  have dW := finrank_dualInv_eq_ker χ ((cycA l l E).comp φ) ρW (fun _ _ => rfl) δ hspanE
  have kW : LinearMap.ker ((LinearMap.lsmul B I δ).restrictScalars E) = ⊤ := by
    ext x; simp only [LinearMap.mem_ker, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply,
      Submodule.mem_top, iff_true]; exact Subtype.ext x.2
  have hdim : finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρV) := by
    rw [dV, dW, kW, finrank_top]; exact (LinearEquiv.refl E I).finrank_eq
  obtain ⟨cW, -, ⟨⟨hc1, hc2⟩, x, hx⟩⟩ := cocycle_eq_crys_add_sub φ hφ hP ρW ρV hW.1 hV.1 hW.2 hV.2
    (I.subtype.restrictScalars E) Subtype.val_injective (fun _ _ => rfl) hdim c hc
  exact ⟨fun g => (cW g : B), fun g => (cW g).2, ⟨⟨hc1, hc2⟩, x, fun g => (hx g).trans (by rw [actC_resCoef])⟩⟩

private theorem tri_crys (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (hP : LocalPublishedTheorems)
    (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a)
    (e : ℕ) (he : 1 ≤ e) (κ : Fin 3 → G →* Bˣ) (hκ : ∀ i, Continuous fun g => (κ i g : B))
    (hI : ∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i))
    (x y z : G → B) (ρ : G →* GL (Fin 3) B) (hz : Continuous z)
    (hρ : ∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g))
    (hxf : x ∈ finiteCocycles φ (chRep (κ 0 / κ 1))) (hyf : y ∈ finiteCocycles φ (chRep (κ 1 / κ 2))) :
    IsCr φ (colRep ρ) := by
  have : ContinuousConstSMul E B := contConstSMul_alg E
  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hxc : Continuous x := hxf.1.1; have hyc : Continuous y := hyf.1.1
  have hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := hxf.1.2
  have cd (i j) : Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := cont_char_div (hκ i) (hκ j)
  have ined (i j g) (hg : φ g ∈ Iq l) : (κ i / κ j) g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) := by
    rw [MonoidHom.div_apply, hI g hg i, hI g hg j, zpow_sub, div_eq_mul_inv]
  have crκ (i) : IsCr φ (chRep (κ i)) := crUnr φ hφ _ (contAction_chRep (hκ i)) ((e : ℤ) * wt1 i)
    fun g hg _ => by rw [chRep_apply, hI g hg i, smul_eq_mul]
  have crd (i j) : IsCr φ (chRep (κ i / κ j)) := crUnr φ hφ _ (contAction_chRep (cd i j))
    ((e : ℤ) * wt1 i - (e : ℤ) * wt1 j) fun g hg _ => by rw [chRep_apply, ined i j g hg, smul_eq_mul]
  have hext : IsCr φ (ext2 (κ 0) (κ 1) x hx) :=
    (isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ 0) (hκ 1) x hx hxc (crκ 0) (crκ 1)).2 hxf
  have hZ : (fun g => (z g, y g)) ∈ Z1 (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
    refine ⟨hz.prodMk hyc, fun g h => ?_⟩
    have hmul : (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) = (ρ g : Matrix (Fin 3) (Fin 3) B) * (ρ h : Matrix (Fin 3) (Fin 3) B) := by
      rw [map_mul, Units.val_mul]
    have h02 := congrFun (congrFun hmul 0) 2; have h12 := congrFun (congrFun hmul 1) 2
    rw [hρ, hρ, hρ] at h02 h12
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h02 h12
    set a := ((κ 2 g : Bˣ) : B); set ai := (((κ 2 g)⁻¹ : Bˣ) : B)
    set b := ((κ 2 h : Bˣ) : B); set bi := (((κ 2 h)⁻¹ : Bˣ) : B)
    have hu : a * ai = 1 := Units.mul_inv _; have hv : b * bi = 1 := Units.mul_inv _
    rw [twist_apply, characterExtensionRep_apply, MonoidHom.inv_apply]
    ext <;> simp
    · linear_combination ai * bi * h02 - (z (g * h) - z g) * b * bi * hu -
        (z (g * h) - z g - ai * (((κ 0 g : Bˣ) : B) * z h + x g * ((κ 1 g : Bˣ) : B) * y h)) * hv
    · linear_combination ai * bi * h12 - (y (g * h) - y g) * b * bi * hu -
        (y (g * h) - y g - ai * (((κ 1 g : Bˣ) : B) * y h)) * hv
  have ed : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hx' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [ed]; exact hx
  have eM : twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx) = ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx' :=
    MonoidHom.ext fun g => LinearMap.ext fun v => by
      simp only [twist_apply, characterExtensionRep_apply, div_eq_mul_inv, MonoidHom.mul_apply,
        Units.val_mul, Prod.smul_mk, smul_eq_mul]; ext <;> simp only [] <;> ring
  refine (isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ x y z ρ hxc hyc hz hρ hx hext (crκ 2)).2 ?_
  rw [eM] at hZ ⊢
  let M := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hx'
  have cM : ContAction M := contAction_charExtension_of_continuous_cocycle (cd 0 2) (cd 1 2) hx' hxc
  have crM : IsCr φ M :=
    (isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (cd 0 2) (cd 1 2) x hx' hxc (crd 0 2) (crd 1 2)).2 (by rw [ed]; exact hxf)
  have hin02 (g) (hg : φ g ∈ Iq l) : (κ 0 / κ 2) g = cycA l l B (φ g) ^ (2 * (e : ℤ)) := by
    rw [ined 0 2 g hg]; congr 1; simp [wt1]; ring
  have hin12 (g) (hg : φ g ∈ Iq l) : (κ 1 / κ 2) g = cycA l l B (φ g) ^ (e : ℤ) := by
    rw [ined 1 2 g hg]; congr 1; simp [wt1]
  have hP02 := positive_scalar_rep φ hφ π hπ (κ 0 / κ 2) (cd 0 2) (2 * (e : ℤ)) (by omega) hin02
    (resCoef E (chRep (κ 0 / κ 2))) fun _ _ => rfl
  have hP12 := positive_scalar_rep φ hφ π hπ (κ 1 / κ 2) (cd 1 2) (e : ℤ) (by exact_mod_cast he) hin12
    (resCoef E (chRep (κ 1 / κ 2))) fun _ _ => rfl
  have pM : Positive φ (resCoef E M) :=
    ⟨(isCrys_isDR_restrict_openSubgroup φ hφ _ cM).1 crM,
      filtBy_of_exact (LinearMap.inl E B B) (LinearMap.snd E B B) Prod.snd_surjective
        (by ext ⟨a, b⟩; simp [eq_comm]) (fun _ _ => by simp [M, resCoef, characterExtensionRep_apply, chRep_apply])
        (fun _ _ => rfl) hP02.2.2 hP12.2.2⟩
  obtain ⟨c, hc, hcy⟩ := (posExact hP φ hφ (resCoef E M) (resCoef E (chRep (κ 1 / κ 2))) cM
    (contAction_chRep (cd 1 2)) pM (LinearMap.snd E B B) (fun _ _ => rfl)).1 Prod.snd_surjective y hyf
  have hcM : c ∈ finiteCocycles φ M := hc
  have hc2 (g) : (c g).2 = y g := congrFun hcy g
  have hd : z - (fun g => (c g).1) ∈ Z1 (chRep (κ 0 / κ 2)) := by
    refine ⟨hZ.1.fst.sub hcM.1.1.fst, fun g h => ?_⟩
    have hzm := congrArg Prod.fst (hZ.2 g h)
    have hcm := congrArg Prod.fst (hcM.1.2 g h)
    simp only [M, characterExtensionRep_apply, Prod.fst_add, hc2] at hzm hcm
    simp only [Pi.sub_apply, hzm, hcm, chRep_apply]; ring
  have hspan02 : Ideal.span (Set.range fun g => (((κ 0 / κ 2) g : Bˣ) : B) - (cycA l l B (φ g) : B)) = Ideal.span {1} := by
    rw [Ideal.span_singleton_one]; exact span_range_sub_cyc_top φ hφ (κ 0 / κ 2) (2 * (e : ℤ)) (by omega) hin02
  obtain ⟨c', hc', hdf⟩ := cocycle_crys_add_ann φ hφ hP π hπ (κ 0 / κ 2) (cd 0 2) (2 * (e : ℤ)) (by omega) hin02 1 hspan02 _ hd
  have hc'0 : c' = 0 := funext fun g => by simpa using hc' g
  rw [hc'0, sub_zero] at hdf
  have h1 := (z1fMap φ (chRep (κ 0 / κ 2)) M).2 ((LinearMap.inl E B B).restrictScalars ℚ_[l])
    (fun _ _ => by simp [M, characterExtensionRep_apply, chRep_apply]) _ hdf
  convert add_mem h1 hcM using 1
  funext g; ext <;> simp [hc2]

end PosCrysB
end PosCrys

private theorem tri_crys_push (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ)
    {B' : Type} [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B']
    [TopologicalSpace B'] [IsModuleTopology ℚ_[l] B'] [IsTopologicalRing B']
    [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] ℚ_[l] B']
    {B : Type} [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
    (q : B' →ₐ[ℚ_[l]] B) (e : ℕ) (he : 1 ≤ e)
    (κ : Fin 3 → G →* B'ˣ) (hκ : ∀ i, Continuous fun g => (κ i g : B'))
    (hI : ∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B' (φ g) ^ ((e : ℤ) * wt1 i))
    (x y z : G → B') (ρ : G →* GL (Fin 3) B') (hz : Continuous z)
    (hρ : ∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B') = triM (fun i => κ i g) (x g) (y g) (z g))
    (hx : x ∈ Z1 (chRep (κ 0 / κ 1))) (hy : y ∈ Z1 (chRep (κ 1 / κ 2)))
    (σ : G) (hσ : ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤)
    (hqx : ∀ b, (((κ 0 / κ 1) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0)
    (hqy : ∀ b, (((κ 1 / κ 2) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) :
    IsCr φ (colRep ((GeneralLinearGroup.map (q : B' →+* B)).comp ρ)) := by
  obtain ⟨E', _, _, _, _, _, π', hπ'⟩ := exists_coefficientField (l := l) B'
  obtain ⟨E, _, _, _, _, _, π, hπ⟩ := exists_coefficientField (l := l) B
  let : Algebra ℤ_[l] E' := Algebra.compHom E' (algebraMap ℤ_[l] ℚ_[l])
  have : IsScalarTower ℤ_[l] ℚ_[l] E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra ℤ_[l] E := Algebra.compHom E (algebraMap ℤ_[l] ℚ_[l])
  have : IsScalarTower ℤ_[l] ℚ_[l] E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra ℤ_[l] B := Algebra.compHom B (algebraMap ℤ_[l] ℚ_[l])
  have : IsScalarTower ℤ_[l] ℚ_[l] B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : TopologicalSpace B := moduleTopology ℚ_[l] B
  have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  have hqc : Continuous (q : B' → B) := IsModuleTopology.continuous_of_linearMap q.toLinearMap
  let qm : B' →* B := (q : B' →+* B)
  let κB (i) : G →* Bˣ := (Units.map qm).comp (κ i)
  have hqcyc (h : GQ l) : Units.map qm (cycA l l B' h) = cycA l l B h := Units.ext <| by
    change q (algebraMap ℤ_[l] B' _) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] _)
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B', q.commutes]
  have push_coc (i j : Fin 3) (c : G → B') (hIij : ∀ g, φ g ∈ Iq l → (κ i / κ j) g = cycA l l B' (φ g) ^ (e : ℤ))
      (hc : c ∈ Z1 (chRep (κ i / κ j)))
      (hqk : ∀ b, (((κ i / κ j) σ : B'ˣ) - (cycA l l B' (φ σ) : B')) * b = 0 → q b = 0) :
      (fun g => q (c g)) ∈ finiteCocycles φ (chRep (κB i / κB j)) := by
    have hcd : Continuous fun g => (((κ i / κ j) g : B'ˣ) : B') := cont_char_div (hκ i) (hκ j)
    let δ : B' := if (e : ℤ) = 1 then ((κ i / κ j) σ : B'ˣ) - (cycA l l B' (φ σ) : B') else 1
    have hspan : Ideal.span (Set.range fun g => (((κ i / κ j) g : B'ˣ) : B') - (cycA l l B' (φ g) : B')) = Ideal.span {δ} := by
      by_cases he1 : (e : ℤ) = 1
      · rw [show δ = ((κ i / κ j) σ : B'ˣ) - (cycA l l B' (φ σ) : B') from by simp [δ, he1]]
        exact span_range_sub_cyc_one φ hφ (κ i / κ j) hcd (fun g hg => by simpa [he1] using hIij g hg) σ hσ
      · rw [show δ = 1 from by simp [δ, he1], Ideal.span_singleton_one]
        exact span_range_sub_cyc_top φ hφ (κ i / κ j) (e : ℤ) (by omega) hIij
    obtain ⟨c', hc', hcf⟩ := cocycle_crys_add_ann φ hφ hP π' hπ' (κ i / κ j) hcd (e : ℤ) (by exact_mod_cast he) hIij δ hspan c hc
    have hqc' (g) : q (c' g) = 0 := by
      by_cases he1 : (e : ℤ) = 1
      · exact hqk _ (by simpa [δ, he1] using hc' g)
      · rw [show c' g = 0 by simpa [δ, he1] using hc' g, map_zero]
    have hpush := (z1fMap φ (chRep (κ i / κ j)) (chRep (κB i / κB j))).2 q.toLinearMap
      (fun g v => by
        show q ((((κ i / κ j) g : B'ˣ) : B') * v) = (((κB i / κB j) g : Bˣ) : B) * q v
        rw [map_mul]; congr 1
        simp only [κB, MonoidHom.div_apply, MonoidHom.comp_apply, ← _root_.map_div, Units.coe_map]; rfl) _ hcf
    convert hpush using 2 with g; simp [hqc' g]
  have hxB := push_coc 0 1 x (fun g hg => by rw [MonoidHom.div_apply, hI g hg 0, hI g hg 1]; simp [wt1]) hx hqx
  have hyB := push_coc 1 2 y (fun g hg => by rw [MonoidHom.div_apply, hI g hg 1, hI g hg 2]; simp [wt1]) hy hqy
  refine tri_crys φ hφ hP π hπ e he κB (fun i => hqc.comp (hκ i))
    (fun g hg i => by simp only [κB, MonoidHom.comp_apply, hI g hg i, map_zpow, hqcyc])
    (fun g => q (x g)) (fun g => q (y g)) (fun g => q (z g))
    ((GeneralLinearGroup.map (q : B' →+* B)).comp ρ) (hqc.comp hz) ?_ hxB hyB
  intro g; change (ρ g : Matrix (Fin 3) (Fin 3) B').map q = _
  rw [hρ g]; ext i j; fin_cases i <;> fin_cases j <;> simp [triM, κB, qm]

private theorem isCr_of_local {l : ℕ} [Fact l.Prime]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ)
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
    (ρ : G →* GL (Fin 3) B) (hc : ∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j)
    (h : ∀ (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B']
      [Algebra B B'] [IsScalarTower ℚ_[l] B B'],
      IsCr φ (colRep ((GeneralLinearGroup.map (algebraMap B B')).comp ρ))) :
    IsCr φ (colRep ρ) := by
  have : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  have : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let M (m : MaximalSpectrum B) := Fin 3 → Localization.AtPrime m.asIdeal
  have step (S : Finset (MaximalSpectrum B)) :
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
        (_ : TopologicalSpace W) (_ : IsModuleTopology ℚ_[l] W) (_ : IsTopologicalAddGroup W)
        (σ : Representation ℚ_[l] G W) (f : (Fin 3 → B) →ₗ[ℚ_[l]] W),
        ContAction σ ∧ IsCr φ σ ∧ (∀ g x, f (resCoef ℚ_[l] (colRep ρ) g x) = σ g (f x)) ∧
        ∀ x, f x = 0 → ∀ m ∈ S, ∀ i, algebraMap B (Localization.AtPrime m.asIdeal) (x i) = 0 := by
    classical
    induction S using Finset.induction_on with
    | empty =>
      let : TopologicalSpace PUnit := moduleTopology ℚ_[l] PUnit
      have : IsModuleTopology ℚ_[l] PUnit := ⟨rfl⟩
      exact ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        IsModuleTopology.isTopologicalAddGroup ℚ_[l] PUnit, 1, 0,
        (continuous_const : Continuous fun _ : G × PUnit => PUnit.unit),
        by unfold IsCr; rw [finrank_zero_of_subsingleton, finrank_zero_of_subsingleton, mul_zero],
        fun _ _ => Subsingleton.elim _ _, by simp⟩
    | insert m S _ ih =>
      obtain ⟨W, _, _, _, _, _, _, σ, f, h1, h2, h3, h4⟩ := ih
      let A := Localization.AtPrime m.asIdeal
      let a : B →ₗ[ℚ_[l]] A := (IsScalarTower.toAlgHom ℚ_[l] B A).toLinearMap
      have : Module.Finite ℚ_[l] A := Module.Finite.of_surjective a (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
      let : TopologicalSpace A := moduleTopology ℚ_[l] A
      have : IsModuleTopology ℚ_[l] A := ⟨rfl⟩
      have : IsTopologicalRing A := IsModuleTopology.isTopologicalRing ℚ_[l] A
      let σ' := resCoef ℚ_[l] (colRep ((GeneralLinearGroup.map (algebraMap B A)).comp ρ))
      have h1' : ContAction σ' := cont_col _ fun i j => qcont_map a (hc i j)
      exact ⟨W × M m, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        σ.prod σ', f.prod (a.compLeft (Fin 3)),
        (h1.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk (h1'.comp (continuous_fst.prodMk continuous_snd.snd)),
        (isCrys_isDR_prod φ hφ σ σ' h1 h1').1 h2 (h _),
        fun g x => Prod.ext (h3 g x) (funext fun k => RingHom.map_mulVec (algebraMap B A) _ x k),
        fun x hx m' hm' => (Finset.mem_insert.1 hm').elim
          (fun hm => hm ▸ fun i => congrFun (congrArg Prod.snd hx) i)
          (h4 x (congrArg Prod.fst hx) m')⟩
  obtain ⟨W, _, _, _, _, _, _, σ, f, h1, h2, h3, h4⟩ := step Finset.univ
  let : TopologicalSpace B := moduleTopology ℚ_[l] B
  have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  refine ((isCrys_isDR_sub_quot φ hφ (resCoef ℚ_[l] (colRep ρ)) σ (cont_col ρ hc) h1 f h3).1 ?_).1 h2
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  exact fun x hx => funext fun i => eq_zero_of_localization _ fun J hJ => h4 x hx ⟨J, hJ⟩ (Finset.mem_univ _) i

private theorem isCr_of_conjGL {l : ℕ} [Fact l.Prime] {G B : Type} [Group G] [CommRing B] [Algebra ℚ_[l] B]
    (φ : G →* GQ l) (ρ : G →* GL (Fin 3) B) (h : GL (Fin 3) B) (hc : IsCr φ (colRep (conjGL h ρ))) :
    IsCr φ (colRep ρ) := by
  let f : (Fin 3 → B) ≃ₗ[ℚ_[l]] (Fin 3 → B) := (Matrix.toLinearEquiv' (h : Matrix (Fin 3) (Fin 3) B) h.invertible).restrictScalars ℚ_[l]
  let F : (Fin 3 → B) ⊗[ℚ_[l]] Bcr l ≃ₗ[ℚ_[l]] (Fin 3 → B) ⊗[ℚ_[l]] Bcr l := TensorProduct.congr f (LinearEquiv.refl _ _)
  have hf (g x) : f (colRep ρ g x) = colRep (conjGL h ρ) g (f x) := by
    simp [f, colRep, conjGL, Matrix.toLinearEquiv', Matrix.mul_assoc]
  have hF (g x) : F (actC φ (resCoef ℚ_[l] (colRep ρ)) g x) = actC φ (resCoef ℚ_[l] (colRep (conjGL h ρ))) g (F x) := by
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b => simp [F, actC, resCoef, hf]
  have hD : (Dcr φ (resCoef ℚ_[l] (colRep ρ))).map F.toLinearMap = Dcr φ (resCoef ℚ_[l] (colRep (conjGL h ρ))) := by
    ext x; obtain ⟨x, rfl⟩ := F.surjective x
    rw [Submodule.mem_map_equiv, F.symm_apply_apply]
    simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, ← hF, F.injective.eq_iff]
  unfold IsCr at hc ⊢; rwa [← hD, LinearEquiv.finrank_map_eq, f.finrank_eq] at hc

/-! ### Part 3: Ordinary locus vs. crystalline locus (`PtsCr` and `CrPts`) -/

private theorem dd_of_diag_s0 {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C))
    (h : (r D.s0).mat = diagonal fun a => algebraMap O C (psi D.Ψ a D.s0)) (a : Fin 3) :
    D.dd r a = algebraMap O C (D.cc a * D.cc (a + 1)) *
      ((r D.fr).mat a a - algebraMap O C ((cycA l l O D.fr : Oˣ) : O) * (r D.fr).mat (a + 1) (a + 1)) := by
  have hsh (b : Fin 3) : D.sh r b D.s0 = diagonal fun c =>
      algebraMap O C (psi D.Ψ c D.s0) - algebraMap O C (psi D.Ψ b D.s0) := by
    rw [Dat3.sh, h, Matrix.scalar_apply, Matrix.diagonal_sub]
  have htr (b : Fin 3) : D.tr r b = algebraMap O C (D.cc b) * (r D.fr).mat b b := by
    rw [Dat3.tr, hsh, hsh, Matrix.diagonal_mul_diagonal, Matrix.trace, Fin.sum_univ_three]
    simp only [Matrix.diag, Matrix.diagonal_mul, Dat3.cc, map_mul, map_sub]
    fin_cases b <;> simp
  simp only [Dat3.dd, htr, map_mul]; ring

section Dat3Core

variable {l : ℕ} [Fact l.Prime]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O]
  (D : Dat3 l O)

omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in
private theorem isUnit_charDiff_s0 (B : Type) [CommRing B] [Algebra ℚ_[l] B]
    [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] :
    (∀ a b : Fin 3, a ≠ b → IsUnit (algebraMap O B (psi D.Ψ a D.s0) - algebraMap O B (psi D.Ψ b D.s0))) ∧
    ∀ a, IsUnit (algebraMap O B (D.cc a)) := by
  obtain ⟨-, -, -, hΨ, hH, hI, hc⟩ := hl_basic D
  have diff (a b : Fin 3) (hab : a ≠ b) : IsUnit (algebraMap O B (psi D.Ψ a D.s0) - algebraMap O B (psi D.Ψ b D.s0)) := by
    have key (c : Fin 3) : psi D.Ψ c D.s0 = algebraMap ℤ_[l] O ((cyc l l D.s0 ^ ((D.e : ℤ) * wt1 c) : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [psi, hΨ _ hH hI, cycA, MonoidHom.comp_apply, ← map_pow, ← map_zpow, Units.coe_map, zpow_mul, zpow_natCast]; rfl
    rw [key a, key b, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← map_sub,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B]
    refine IsUnit.map _ (Ne.isUnit ?_)
    have he0 : (D.e : ℤ) ≠ 0 := by have := D.e_pos; omega
    have hexp : (D.e : ℤ) * wt1 a ≠ (D.e : ℤ) * wt1 b := fun hw => hab <| by
      have := mul_left_cancel₀ he0 hw; fin_cases a <;> fin_cases b <;> simp [wt1] at this ⊢
    intro hz
    have h0 : ((cyc l l D.s0 ^ ((D.e : ℤ) * wt1 a) : ℤ_[l]ˣ) : ℤ_[l]) -
        ((cyc l l D.s0 ^ ((D.e : ℤ) * wt1 b) : ℤ_[l]ˣ) : ℤ_[l]) = 0 :=
      (IsFractionRing.injective ℤ_[l] ℚ_[l]) (by simpa using hz)
    exact hc (isOfFinOrder_iff_zpow_eq_one.2 ⟨(D.e : ℤ) * wt1 a - (D.e : ℤ) * wt1 b, sub_ne_zero.2 hexp,
      by rw [zpow_sub, Units.ext (sub_eq_zero.1 h0), mul_inv_cancel]⟩)
  exact ⟨diff, fun a => by
    rw [Dat3.cc, map_mul, map_sub, map_sub]
    exact (diff a (a + 1) (by fin_cases a <;> decide)).mul (diff a (a + 2) (by fin_cases a <;> decide))⟩

omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in
private theorem triangular_of_ordIdeal_eq_bot
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B]
    [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B]
    (r : GQ l →* GG (m := 3) (R := B)) (hmult : HasMult D.η r)
    (hcont : ∀ a b, QCont l fun g => (r g).mat a b) (hbot : ordIdeal D r = ⊥) :
    ∃ (h : GL (Fin 3) B) (ρ : ↥D.HL →* GL (Fin 3) B) (κ : Fin 3 → ↥D.HL →* Bˣ) (x y z : ↥D.HL → B),
      (∀ g, ρ g = (conjBy h r g).left) ∧ (∀ i, Continuous fun g => (κ i g : B)) ∧
      (∀ g : ↥D.HL, (g : GQ l) ∈ Iq l → ∀ i, κ i g = cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i)) ∧
      Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧
      x ∈ Z1 (chRep (κ 0 / κ 1)) ∧ y ∈ Z1 (chRep (κ 1 / κ 2)) ∧
      ∀ hσ : D.fr ∈ D.HL,
        (∃ v : Bˣ, D.dd r 0 = v * (((κ 0 / κ 1) ⟨_, hσ⟩ : Bˣ) - (cycA l l B D.fr : B))) ∧
        (∃ v : Bˣ, D.dd r 1 = v * (((κ 1 / κ 2) ⟨_, hσ⟩ : Bˣ) - (cycA l l B D.fr : B))) := by
  obtain ⟨hHLn, -, -, hPsi, hsHL, hsIq, -⟩ := hl_basic D
  obtain ⟨hpu, hcc⟩ := isUnit_charDiff_s0 D B
  have pu (a b : Fin 3) (hab : a ≠ b := by decide) := hpu a b hab
  let p (a : Fin 3) : B := algebraMap O B (psi D.Ψ a D.s0)
  have hchar : (r D.s0).mat.charpoly = ∏ a : Fin 3, (X - C (p a)) := by
    rw [← sub_eq_zero]; ext i
    have hm : ((r D.s0).mat.charpoly - ∏ a : Fin 3, (X - C (p a))).coeff i ∈ ordIdeal D r :=
      Ideal.subset_span (Set.mem_union_left _ ⟨D.s0, ⟨hsHL, hsIq⟩, i, rfl⟩)
    rwa [hbot, Ideal.mem_bot] at hm
  obtain ⟨h, hh⟩ := exists_GL_conj_eq_diagonal (r D.s0).mat p hpu hchar
  have hright (g) (hg : g ∈ D.HL) : (r g).right = 1 := (hmult g).trans hg.1
  let r' := conjBy h r
  have hright' (g) (hg : g ∈ D.HL) : (r' g).right = 1 := (conjBy_right h r g).trans (hright g hg)
  let H : Matrix (Fin 3) (Fin 3) B := h
  let K : Matrix (Fin 3) (Fin 3) B := (h⁻¹ : GL (Fin 3) B)
  have hKH : K * H = 1 := h.inv_val
  have hHK : H * K = 1 := h.val_inv
  let conjM (A : Matrix (Fin 3) (Fin 3) B) := H * A * K
  have hconj_mul (A N) : conjM A * conjM N = conjM (A * N) := by
    simp only [conjM, Matrix.mul_assoc]; rw [← Matrix.mul_assoc K H, hKH, Matrix.one_mul]
  have hmat (g) (hg : g ∈ D.HL) : (r' g).mat = conjM (r g).mat := by
    simp only [r', GG.mat, conjBy_left, hright g hg, sgnAct_one, Units.val_mul, conjM, H, K]
  have hshift (a s) (hs : s ∈ D.HL) : D.sh r' a s = conjM (D.sh r a s) := by
    rw [Dat3.sh, Dat3.sh, hmat s hs]
    have hsc (c : B) : conjM (scalar (Fin 3) c) = scalar (Fin 3) c := by
      unfold conjM; rw [← (Matrix.scalar_commute c (fun _ => Commute.all _ _) H), Matrix.mul_assoc, hHK, Matrix.mul_one]
    simp only [conjM, Matrix.mul_sub, Matrix.sub_mul] at hsc ⊢; rw [hsc]
  have hs0' : (r' D.s0).mat = diagonal p := (hmat _ hsHL).trans hh
  have hsh (s : Fin 3 → GQ l) (hs : ∀ a, s a ∈ D.HL ⊓ Iq l) :
      D.sh r' 0 (s 0) * D.sh r' 1 (s 1) * D.sh r' 2 (s 2) = 0 := by
    have hzero : D.sh r 0 (s 0) * D.sh r 1 (s 1) * D.sh r 2 (s 2) = 0 := by
      ext i j
      have hm : (D.sh r 0 (s 0) * D.sh r 1 (s 1) * D.sh r 2 (s 2)) i j ∈ ordIdeal D r :=
        Ideal.subset_span (Set.mem_union_right _ ⟨s, hs, i, j, rfl⟩)
      rwa [hbot, Ideal.mem_bot] at hm
    rw [hshift _ _ (hs 0).1, hshift _ _ (hs 1).1, hshift _ _ (hs 2).1, hconj_mul, hconj_mul, hzero]; simp [conjM]
  have hdiag_sub (c : B) : diagonal p - scalar (Fin 3) c = diagonal (fun i => p i - c) := by
    rw [Matrix.scalar_apply, Matrix.diagonal_sub]
  have htriI (t) (ht : t ∈ D.HL ⊓ Iq l) :
      (r' t).mat 1 0 = 0 ∧ (r' t).mat 2 0 = 0 ∧ (r' t).mat 2 1 = 0 ∧
      (r' t).mat 0 0 = algebraMap O B (psi D.Ψ 0 t) ∧ (r' t).mat 1 1 = algebraMap O B (psi D.Ψ 1 t) ∧
      (r' t).mat 2 2 = algebraMap O B (psi D.Ψ 2 t) := by
    have h0 := hsh ![t, D.s0, D.s0] fun a => by fin_cases a; exacts [ht, ⟨hsHL, hsIq⟩, ⟨hsHL, hsIq⟩]
    have h1 := hsh ![D.s0, t, D.s0] fun a => by fin_cases a; exacts [⟨hsHL, hsIq⟩, ht, ⟨hsHL, hsIq⟩]
    have h2 := hsh ![D.s0, D.s0, t] fun a => by fin_cases a; exacts [⟨hsHL, hsIq⟩, ⟨hsHL, hsIq⟩, ht]
    simp only [Dat3.sh, hs0', hdiag_sub, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
    have k {x a b : B} (ha : IsUnit a) (hb : IsUnit b) (h : x * a * b = 0) : x = 0 :=
      (ha.mul hb).mul_left_eq_zero.mp (by rwa [← mul_assoc])
    have e10 := congrFun (congrFun h0 1) 0; have e20 := congrFun (congrFun h0 2) 0
    have e00 := congrFun (congrFun h0 0) 0; have e21 := congrFun (congrFun h1 2) 1
    have e11 := congrFun (congrFun h1 1) 1; have e22 := congrFun (congrFun h2 2) 2
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul] at e10 e20 e00 e21 e11 e22
    exact ⟨k (pu 0 1) (pu 0 2) e10, k (pu 0 1) (pu 0 2) e20,
      k (pu 2 0) (pu 1 2) (by rwa [mul_comm (p 2 - p 0)] at e21),
      sub_eq_zero.1 (k (pu 0 1) (pu 0 2) e00),
      sub_eq_zero.1 (k (pu 1 0) (pu 1 2) (by rwa [mul_comm (p 1 - p 0)] at e11)),
      sub_eq_zero.1 (((pu 2 0).mul (pu 2 1)).mul_left_eq_zero.1 (by rwa [mul_comm] at e22))⟩
  have hmm (x y : GG (m := 3) (R := B)) (hx : x.right = 1) : (x * y).mat = x.mat * y.mat := by
    simp [GG.mat, SemidirectProduct.mul_left, hx]
  have htri (g) (hg : g ∈ D.HL) : (r' g).mat 1 0 = 0 ∧ (r' g).mat 2 0 = 0 ∧ (r' g).mat 2 1 = 0 := by
    have ht : g * D.s0 * g⁻¹ ∈ D.HL ⊓ Iq l := ⟨hHLn.conj_mem _ hsHL g, (iqBasic l).1.conj_mem _ hsIq g⟩
    obtain ⟨t10, t20, t21, -, d1, d2⟩ := htriI _ ht
    have hpc (a) : psi D.Ψ a (g * D.s0 * g⁻¹) = psi D.Ψ a D.s0 := by simp [psi, mul_inv_cancel_comm]
    rw [hpc] at d1 d2
    have hmul : (r' (g * D.s0 * g⁻¹)).mat * (r' g).mat = (r' g).mat * diagonal p := by
      rw [← hs0', ← hmm _ _ (hright' _ ht.1), ← hmm _ _ (hright' _ hg), ← map_mul, ← map_mul,
        show g * D.s0 * g⁻¹ * g = g * D.s0 by group]
    have e20 := congrFun (congrFun hmul 2) 0; have e10 := congrFun (congrFun hmul 1) 0
    have e21 := congrFun (congrFun hmul 2) 1
    rw [Matrix.mul_diagonal] at e20 e10 e21
    simp only [Matrix.mul_apply, Fin.sum_univ_three, t10, t20, t21, d1, d2] at e20 e10 e21
    have m20 : (r' g).mat 2 0 = 0 := (pu 2 0).mul_right_eq_zero.1 (by dsimp only [p] at e20; linear_combination e20)
    have m10 : (r' g).mat 1 0 = 0 := (pu 1 0).mul_right_eq_zero.1
      (by dsimp only [p] at e10; linear_combination e10 - (r' (g * D.s0 * g⁻¹)).mat 1 2 * m20)
    have m21 : (r' g).mat 2 1 = 0 := (pu 2 1).mul_right_eq_zero.1 (by dsimp only [p] at e21; linear_combination e21)
    exact ⟨m10, m20, m21⟩
  have htri_mul (A N : Matrix (Fin 3) (Fin 3) B)
      (hA : A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0) (hN : N 1 0 = 0 ∧ N 2 0 = 0 ∧ N 2 1 = 0) :
      (∀ i, (A * N) i i = A i i * N i i) ∧ (A * N) 0 1 = A 0 0 * N 0 1 + A 0 1 * N 1 1 ∧
        (A * N) 1 2 = A 1 1 * N 1 2 + A 1 2 * N 2 2 := by
    obtain ⟨a10, a20, a21⟩ := hA; obtain ⟨b10, b20, b21⟩ := hN
    exact ⟨fun i => by fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21],
      by simp [Matrix.mul_apply, Fin.sum_univ_three, b21], by simp [Matrix.mul_apply, Fin.sum_univ_three, a10]⟩
  let M (g : ↥D.HL) : Matrix (Fin 3) (Fin 3) B := (r' g).mat
  have hMc (i j) : Continuous fun g : ↥D.HL => M g i j := by
    have hr : Continuous fun g : GQ l => (r g).mat := continuous_matrix fun a b => by
      have := hcont a b; unfold QCont at this; rwa [← eq_moduleTopology ℚ_[l] B] at this
    have he : (fun g : ↥D.HL => M g i j) = fun g : ↥D.HL => (H * (r g).mat * K) i j :=
      funext fun g => congrFun (congrFun (hmat g g.2) i) j
    rw [he]
    exact ((continuous_const.matrix_mul (hr.comp continuous_subtype_val)).matrix_mul continuous_const).matrix_elem i j
  have hmulHL (a b : ↥D.HL) : M (a * b) = M a * M b := by
    simp only [M, Subgroup.coe_mul, map_mul, hmm _ _ (hright' _ a.2)]
  have hdiag (a b : ↥D.HL) (i) : M (a * b) i i = M a i i * M b i i := by
    rw [hmulHL]; exact (htri_mul _ _ (htri _ a.2) (htri _ b.2)).1 i
  have hunit (a : ↥D.HL) (i) : M a i i * M a⁻¹ i i = 1 := by
    rw [← hdiag a a⁻¹, mul_inv_cancel]; simp [M, GG.mat]
  let κ (i : Fin 3) : ↥D.HL →* Bˣ := MonoidHom.mk'
    (fun g => ⟨M g i i, M g⁻¹ i i, hunit g i, by rw [mul_comm]; exact hunit g i⟩)
    (fun a b => Units.ext (hdiag a b i))
  let ρ : ↥D.HL →* GL (Fin 3) B := glPart D.HL r' hright'
  have hκ (i) (g : ↥D.HL) : ((κ i g : Bˣ) : B) = M g i i := rfl
  have hq (i j : Fin 3) (a : ↥D.HL) : (((κ i / κ j) a : Bˣ) : B) = M a i i * M a⁻¹ j j := by
    rw [MonoidHom.div_apply, div_eq_mul_inv, Units.val_mul]; rfl
  have hcyc (s) : Units.map (algebraMap O B : O →* B) (cycA l l O s) = cycA l l B s :=
    Units.ext (by simp [cycA, ← IsScalarTower.algebraMap_apply])
  refine ⟨h, ρ, κ, fun g => M g 0 1 * M g⁻¹ 1 1, fun g => M g 1 2 * M g⁻¹ 2 2, fun g => M g 0 2 * M g⁻¹ 2 2,
    fun _ => rfl, fun i => hMc i i, ?_, (hMc 0 2).mul ((hMc 2 2).comp continuous_inv), ?_, ?_, ?_, ?_⟩
  · intro g hgI i
    obtain ⟨-, -, -, d0, d1, d2⟩ := htriI _ ⟨g.2, hgI⟩
    have key (k : Fin 3) : algebraMap O B (psi D.Ψ k g) = ((cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 k) : Bˣ) : B) := by
      rw [psi, hPsi _ g.2 hgI, ← hcyc, ← map_zpow, Units.coe_map, zpow_mul, zpow_natCast]; rfl
    ext; fin_cases i
    · exact d0.trans (key 0)
    · exact d1.trans (key 1)
    · exact d2.trans (key 2)
  · intro g
    obtain ⟨t10, t20, t21⟩ := htri _ g.2
    have u1 := hunit g 1; have u2 := hunit g 2
    change M g = _
    ext i j; fin_cases i <;> fin_cases j <;> simp [triM, hκ, M, t10, t20, t21] at u1 u2 ⊢
    all_goals first
      | linear_combination -M g 0 1 * u1
      | linear_combination -M g 0 2 * u2
      | linear_combination -M g 1 2 * u2
  · refine ⟨(hMc 0 1).mul ((hMc 1 1).comp continuous_inv), fun a b => ?_⟩
    dsimp only; rw [chRep_apply, hq, mul_inv_rev, hmulHL, hmulHL]
    rw [(htri_mul _ _ (htri _ a.2) (htri _ b.2)).2.1, (htri_mul _ _ (htri _ (b⁻¹).2) (htri _ (a⁻¹).2)).1 1]
    linear_combination M a 0 1 * M a⁻¹ 1 1 * hunit b 1
  · refine ⟨(hMc 1 2).mul ((hMc 2 2).comp continuous_inv), fun a b => ?_⟩
    dsimp only; rw [chRep_apply, hq, mul_inv_rev, hmulHL, hmulHL]
    rw [(htri_mul _ _ (htri _ a.2) (htri _ b.2)).2.2, (htri_mul _ _ (htri _ (b⁻¹).2) (htri _ (a⁻¹).2)).1 2]
    linear_combination M a 1 2 * M a⁻¹ 2 2 * hunit b 2
  · intro hσ
    have htr (a) : D.tr r' a = D.tr r a := by
      rw [Dat3.tr, Dat3.tr, hshift _ _ hsHL, hshift _ _ hsHL, hmat _ hσ, hconj_mul, hconj_mul]
      unfold conjM; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hKH, Matrix.one_mul]
    have hdd (a) : D.dd r a = D.dd r' a := by simp only [Dat3.dd, htr]
    have hc' : algebraMap O B ((cycA l l O D.fr : Oˣ) : O) = (cycA l l B D.fr : B) := by rw [← hcyc]; rfl
    let frH : ↥D.HL := ⟨_, hσ⟩
    have u1 := hunit frH 1; have u2 := hunit frH 2
    refine ⟨⟨(hcc 0).unit * (hcc 1).unit * κ 1 frH, ?_⟩, ⟨(hcc 1).unit * (hcc 2).unit * κ 2 frH, ?_⟩⟩
    · rw [hdd, dd_of_diag_s0 D r' hs0' 0, hq, Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hκ, ← hc']
      rw [show (0 : Fin 3) + 1 = 1 from rfl, map_mul]
      linear_combination -(algebraMap O B (D.cc 0) * algebraMap O B (D.cc 1) * M frH 0 0) * u1
    · rw [hdd, dd_of_diag_s0 D r' hs0' 1, hq, Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hκ, ← hc']
      rw [show (1 : Fin 3) + 1 = 2 from rfl, map_mul]
      linear_combination -(algebraMap O B (D.cc 1) * algebraMap O B (D.cc 2) * M frH 1 1) * u2

private theorem ptsCr_IY (hP : LocalPublishedTheorems)
    (U : Univ (GCond.noCondition O D.η D.Ψ)) : PtsCr D U (IY D U) := by
  intro B _ _ _ _ _ _ _ f hf
  obtain ⟨-, -, hemb, -, -⟩ := hl_basic D
  have hright (g) (hg : g ∈ D.HL) : (push f U.r.hom g).right = 1 := (U.r.hasMult g).trans hg.1
  let ρ := glPart D.HL (push f U.r.hom) hright
  refine ⟨ρ, fun _ => rfl, isCr_of_local D.HL.subtype hemb ρ (fun i j => ?_) fun B' _ _ _ _ _ _ => ?_⟩
  · have h := (ptCont (l := l) U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat i j) (U.r.cont i j)
    unfold QCont at h ⊢
    exact @Continuous.comp ↥D.HL (GQ l) B _ _ (moduleTopology ℚ_[l] B) Subtype.val _ h continuous_subtype_val
  · let aO' : Algebra O B' := Algebra.compHom B' (algebraMap O B)
    let aZ' : Algebra ℤ_[l] B' := Algebra.compHom B' (algebraMap ℤ_[l] B)
    have : IsScalarTower ℤ_[l] O B' := IsScalarTower.of_algebraMap_eq fun x =>
      congrArg (algebraMap B B') (IsScalarTower.algebraMap_apply ℤ_[l] O B x)
    have : IsScalarTower ℤ_[l] ℚ_[l] B' := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B B' (algebraMap ℤ_[l] B x) = algebraMap ℚ_[l] B' (algebraMap ℤ_[l] ℚ_[l] x)
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B, IsScalarTower.algebraMap_apply ℚ_[l] B B']
    let f1 : U.R →ₐ[O] B' :=
      { toRingHom := (algebraMap B B').comp (f : U.R →+* B)
        commutes' := fun x => congrArg (algebraMap B B') (f.commutes x) }
    have hf1 : IY D U ≤ RingHom.ker f1 := fun a ha => by
      change algebraMap B B' (f a) = 0; rw [show f a = 0 from hf ha, map_zero]
    have hsat (a : U.R) : del D U.r.hom * a ∈ IY D U → a ∈ IY D U := fun ⟨n, hn⟩ =>
      ⟨n + 1, by rw [pow_succ, mul_assoc]; exact hn⟩
    obtain ⟨B'', _, _, _, _, _, _, _, _, f', q, hJ, hqf, hkill⟩ :=
      exists_finite_local_lift (l := l) U.R (IY D U) (del D U.r.hom) hsat B' f1 hf1
    let : TopologicalSpace B'' := moduleTopology ℚ_[l] B''
    have : IsModuleTopology ℚ_[l] B'' := ⟨rfl⟩
    have : IsTopologicalRing B'' := IsModuleTopology.isTopologicalRing ℚ_[l] B''
    obtain ⟨hnat, -, hdel⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D f' U.r.hom
    have hzero : ordIdeal D (push f' U.r.hom) = ⊥ := by
      rw [← hnat, Ideal.map_eq_bot_iff_le_ker]; exact le_trans (b := IY D U) (fun a ha => ⟨0, by simpa using ha⟩) hJ
    obtain ⟨h, ρ'', κ, x, y, z, hρ'', hκc, hκI, hz, hρM, hx, hy, hσd⟩ :=
      triangular_of_ordIdeal_eq_bot D B'' (push f' U.r.hom) (fun g => U.r.hasMult g)
        (fun a b => (ptCont U.R B'' f').1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)) hzero
    obtain ⟨⟨hσ, hcl⟩, -⟩ := fr_isFr D
    obtain ⟨⟨v0, hv0⟩, ⟨v1, hv1⟩⟩ := hσd hσ
    have hdel' : f' (del D U.r.hom) = (l : B'') * dd D (push f' U.r.hom) 0 * dd D (push f' U.r.hom) 1 := hdel
    have hcr := tri_crys_push hP D.HL.subtype hemb q D.e D.e_pos κ hκc hκI x y z ρ'' hz hρM hx hy ⟨_, hσ⟩ hcl
      (fun b hb => hkill b (by
        dsimp only [Subgroup.coe_subtype] at hb
        rw [hdel', hv0]; linear_combination ((l : B'') * (v0 : B'') * dd D (push f' U.r.hom) 1) * hb))
      (fun b hb => hkill b (by
        dsimp only [Subgroup.coe_subtype] at hb
        rw [hdel', hv1]; linear_combination ((l : B'') * dd D (push f' U.r.hom) 0 * (v1 : B'')) * hb))
    have e : (GeneralLinearGroup.map (q : B'' →+* B')).comp ρ'' =
        conjGL (GeneralLinearGroup.map (q : B'' →+* B') h) ((GeneralLinearGroup.map (algebraMap B B')).comp ρ) := by
      have hq' : (GG.map (q : B'' →+* B')).comp (push f' U.r.hom) = push f1 U.r.hom :=
        MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext <| Matrix.ext fun i j => hqf _) rfl
      refine MonoidHom.ext fun g => ?_
      have h1 := DFunLike.congr_fun ((map_conjBy (q : B'' →+* B') h (push f' U.r.hom)).trans (by rw [hq'])) (g : GQ l)
      have h2 : ((GeneralLinearGroup.map (q : B'' →+* B')).comp ρ'') g =
          (conjBy (GeneralLinearGroup.map (q : B'' →+* B') h) (push f1 U.r.hom) (g : GQ l)).left := by
        rw [MonoidHom.comp_apply, hρ'' g, ← h1]; rfl
      rw [h2, conjBy_left, show (push f1 U.r.hom (g : GQ l)).right = 1 from (U.r.hasMult g).trans g.2.1, sgnAct_one,
        show (push f1 U.r.hom (g : GQ l)).left = ((GeneralLinearGroup.map (algebraMap B B')).comp ρ) g from
          Units.ext (Matrix.ext fun i j => rfl)]
      rfl
    exact isCr_of_conjGL D.HL.subtype _ _ (e ▸ hcr)

omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in
private theorem del_unr_twist (E : Type) [Field E] [Algebra O E] [IsFractionRing O E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    (t : B) (ht : IsNilpotent t) :
    ∃ u : GQ l →* Bˣ, QCont l (fun g => (u g : B)) ∧ (∀ g ∈ Iq l, u g = 1) ∧ (∀ g, IsNilpotent ((u g : B) - 1)) ∧
      ∃ (j : ℕ) (v : Bˣ), j ≤ 2 ∧
        del D (r0 D.η ((Units.map (algebraMap O B : O →* B)).comp D.Ψ * u)) = t ^ j * v := by
  obtain ⟨-, σ₀, m, hF, hm, hI⟩ := fr_isFr D
  obtain ⟨-, -, -, -, hs0⟩ := hl_basic D
  let : Algebra ℚ B := Algebra.compHom B (algebraMap ℚ ℚ_[l])
  let : TopologicalSpace B := moduleTopology ℚ_[l] B
  have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  have : IsTopologicalAddGroup B := IsModuleTopology.isTopologicalAddGroup ℚ_[l] B
  have : ContinuousSMul ℚ_[l] B := IsModuleTopology.toContinuousSMul ℚ_[l] B
  have exp_sq {a : B} (ha : IsNilpotent a) : ∃ s, IsNilpotent.exp a = 1 + a + a ^ 2 * s := by
    obtain ⟨k, hk⟩ := ha
    refine ⟨∑ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i, ?_⟩
    have hsum : a ^ 2 * ∑ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ i =
        ∑ i ∈ Finset.range k, (((i + 1 + 1).factorial : ℚ))⁻¹ • a ^ (i + 1 + 1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm]; congr 1; ring
    rw [IsNilpotent.exp_eq_sum (k := k + 2) (pow_eq_zero_of_le (by omega) hk), Finset.sum_range_succ',
      Finset.sum_range_succ', hsum]
    simp only [zero_add, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, pow_one, pow_zero]
    ring
  obtain ⟨c, ⟨hc, hcI, hcσ⟩, -⟩ := existsUnique_unramified_cocycle_frobenius_value (v := l) (l := l) (A := ℚ_[l]) (V := ℚ_[l])
    (1 : Representation ℚ_[l] (GQ l) ℚ_[l]) continuous_snd (fun _ _ => rfl) σ₀ hF 1
  have hadd (g h) : c (g * h) = c g + c h := hc.2 g h
  have hc1 : c 1 = 0 := hcI 1 (one_mem _)
  have hcpow (n : ℕ) : c (σ₀ ^ n) = n := by
    induction n with
    | zero => simp [hc1]
    | succ n ih => rw [pow_succ, hadd, ih, hcσ]; push_cast; ring
  let f : GQ l →* B :=
    { toFun := fun g => IsNilpotent.exp (c g • t)
      map_one' := by rw [hc1, zero_smul, IsNilpotent.exp_zero]
      map_mul' := fun g h => by rw [hadd, add_smul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (ht.smul _) (ht.smul _)] }
  have hf : Continuous f := by
    obtain ⟨k, hk⟩ := ht
    have e : (f : GQ l → B) = fun g => ∑ i ∈ Finset.range k, ((((i.factorial : ℚ)⁻¹ : ℚ) : ℚ_[l]) * c g ^ i) • t ^ i := by
      funext g; change IsNilpotent.exp (c g • t) = _
      rw [IsNilpotent.exp_eq_sum (k := k) (by rw [_root_.smul_pow, hk, smul_zero])]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul, Rat.cast_smul_eq_qsmul, _root_.smul_pow]
    have hcc : Continuous c := hc.1; rw [e]; fun_prop
  let u := f.toHomUnits
  have huI (g) (hg : g ∈ Iq l) : u g = 1 := Units.ext <| by
    change IsNilpotent.exp (c g • t) = 1; rw [hcI g hg, zero_smul, IsNilpotent.exp_zero]
  have hunil (g) : IsNilpotent ((u g : B) - 1) := by
    change IsNilpotent (IsNilpotent.exp (c g • t) - 1)
    obtain ⟨s, hs⟩ := exp_sq (ht.smul (c g))
    rw [hs, show 1 + c g • t + (c g • t) ^ 2 * s - 1 = (c g • t) * (1 + (c g • t) * s) by ring]
    exact (Commute.all _ _).isNilpotent_mul_right (ht.smul (c g))
  refine ⟨u, hf, huI, hunil, ?_⟩
  obtain ⟨s, hs⟩ := exp_sq (ht.smul (m : ℚ_[l]))
  have huσ : u D.fr = u (σ₀ ^ m) := by
    calc u D.fr = u (σ₀ ^ m * ((σ₀ ^ m)⁻¹ * D.fr)) := by rw [mul_inv_cancel_left]
      _ = u (σ₀ ^ m) := by rw [map_mul, huI _ hI, mul_one]
  set w : B := (m : B) + t * ((m : B) ^ 2 * s)
  have hb : (u D.fr : B) - 1 = t * w := by
    rw [huσ]; change IsNilpotent.exp (c (σ₀ ^ m) • t) - 1 = _
    rw [hcpow m, hs, show ((m : ℚ_[l]) • t) = (m : B) * t by rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]]; ring
  obtain ⟨-, hcc⟩ := isUnit_charDiff_s0 D B
  let rU := r0 D.η ((Units.map (algebraMap O B : O →* B)).comp D.Ψ * u)
  have hdiag : (rU D.s0).mat = diagonal fun a => algebraMap O B (psi D.Ψ a D.s0) := by
    change diagonal _ = _
    simp only [MonoidHom.mul_apply, huI _ hs0.2.1, mul_one]
    congr 1; funext a; rw [MonoidHom.comp_apply, ← map_zpow, Units.coe_map]; rfl
  have h0 := dd_of_diag_s0 D rU hdiag 0; have h1 := dd_of_diag_s0 D rU hdiag 1
  set y : Bˣ := (Units.map (algebraMap O B : O →* B)).comp D.Ψ D.fr * u D.fr
  have hmat0 : (rU D.fr).mat 0 0 = (y : B) := by change diagonal _ 0 0 = _; simp [wt1, y]
  have hmat1 : (rU D.fr).mat 1 1 = 1 := by change diagonal _ 1 1 = _; simp [wt1]
  have hmat2 : (rU D.fr).mat 2 2 = ((y⁻¹ : Bˣ) : B) := by change diagonal _ 2 2 = _; simp [wt1, y]
  rw [hmat0, show (0 : Fin 3) + 1 = 1 from rfl, hmat1, mul_one] at h0
  rw [hmat1, show (1 : Fin 3) + 1 = 2 from rfl, hmat2] at h1
  set a₀ := algebraMap O B (D.Ψ D.fr : O)
  set c₀ := algebraMap O B ((cycA l l O D.fr : Oˣ) : O)
  set k0 := algebraMap O B (D.cc 0 * D.cc 1); set k1 := algebraMap O B (D.cc 1 * D.cc 2)
  set Q := (l : B) * k0 * k1 * ((y⁻¹ : Bˣ) : B)
  have hyv : (y : B) = a₀ * (1 + t * w) := by
    simp only [y, a₀, Units.val_mul, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_ofClass]
    linear_combination algebraMap O B (D.Ψ D.fr : O) * hb
  have hl : IsUnit (l : B) := by
    simpa using (isUnit_iff_ne_zero.2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)).map (algebraMap ℚ_[l] B)
  have hmu : IsUnit (m : B) := by
    simpa using (isUnit_iff_ne_zero.2 (by exact_mod_cast (show m ≠ 0 by omega) : (m : ℚ_[l]) ≠ 0)).map (algebraMap ℚ_[l] B)
  have hw : IsUnit w :=
    show IsUnit ((m : B) + t * ((m : B) ^ 2 * s)) from
      ((Commute.all _ _).isNilpotent_mul_right ht).isUnit_add_left_of_commute hmu (Commute.all _ _)
  have ha : IsUnit a₀ := (D.Ψ D.fr).isUnit.map (algebraMap O B)
  have hk0 : IsUnit k0 := by simp only [k0, map_mul]; exact (hcc 0).mul (hcc 1)
  have hk1 : IsUnit k1 := by simp only [k1, map_mul]; exact (hcc 1).mul (hcc 2)
  have hQ : IsUnit Q := ((hl.mul hk0).mul hk1).mul y⁻¹.isUnit
  have hprod : del D rU = Q * ((a₀ - c₀) + t * (a₀ * w)) ^ 2 := by
    unfold del; rw [h0, h1]
    have hinv := y.mul_inv; rw [hyv] at hinv ⊢
    linear_combination -((l : B) * k0 * k1 * (a₀ * (1 + t * w) - c₀)) * hinv
  rw [hprod]
  by_cases hc0 : (D.Ψ D.fr : O) - ((cycA l l O D.fr : Oˣ) : O) = 0
  · have : a₀ - c₀ = 0 := by rw [← map_sub, hc0, map_zero]
    rw [this, zero_add]
    exact ⟨2, (hQ.mul ((ha.mul hw).pow 2)).unit, le_rfl, by rw [IsUnit.unit_spec]; ring⟩
  · have hnu : IsUnit (a₀ - c₀) := by
      rw [← map_sub, IsScalarTower.algebraMap_apply O E B]
      exact (Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective O E)).2 hc0)).map _
    have hn : IsUnit ((a₀ - c₀) + t * (a₀ * w)) :=
      ((Commute.all _ _).isNilpotent_mul_right ht).isUnit_add_left_of_commute hnu (Commute.all _ _)
    exact ⟨0, (hQ.mul (hn.pow 2)).unit, by norm_num, by rw [IsUnit.unit_spec, pow_zero, one_mul]⟩

private theorem twist_inDcr (E : Type) [Field E] [Algebra O E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    (π : B →ₐ[E] E) (u : GQ l →* Bˣ) (hc : QCont l fun g => (u g : B))
    (hI : ∀ g ∈ Iq l, u g = 1) (hu : ∀ g, IsNilpotent ((u g : B) - 1)) :
    D.InDcr (π : B →+* E) (r0 D.η ((Units.map (algebraMap O B : O →* B)).comp D.Ψ * u)) := by
  let : TopologicalSpace B := moduleTopology ℚ_[l] B
  have : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℚ_[l] B
  let j : Oˣ →* Bˣ := Units.map (algebraMap O B : O →* B)
  let ψ : GQ l →* Bˣ := j.comp D.Ψ * u
  have hψv (g) : (ψ g : B) = algebraMap O B (D.Ψ g : O) * (u g : B) := rfl
  have hu1 (g) : π (u g : B) = 1 := sub_eq_zero.1 (by simpa using ((hu g).map π).eq_zero)
  have hψ : Continuous fun g => (ψ g : B) := by
    simp only [hψv]; exact ((ptCont (l := l) O B (Algebra.ofId O B)).1 _ _ D.Ψ_cont).mul hc
  have hψi : Continuous fun g => (((ψ g)⁻¹ : Bˣ) : B) :=
    continuous_units_inv_of_continuous_coe_finite_Qp_algebra (l := l) (fun g => ψ g) hψ
  have hψ' : Continuous ψ := Units.continuous_iff.2 ⟨hψ, hψi⟩
  have r0_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (χ : GQ l →* Rˣ) :
      (GG.map f).comp (r0 D.η χ) = r0 D.η ((Units.map (f : R →* S)).comp χ) :=
    MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext <| by
      change (diagonal _).map f = diagonal _
      rw [Matrix.diagonal_map (map_zero _)]; congr 1; funext a
      exact congrArg Units.val (map_zpow (Units.map (f : R →* S)) _ _)) rfl
  refine ⟨fun _ => rfl, ?_, fun a b => ?_, ?_⟩
  · show (GG.map (π : B →+* E)).comp (r0 D.η ψ) = (GG.map (algebraMap O E)).comp (r0 D.η D.Ψ)
    rw [r0_map, r0_map]; congr 1; ext g
    change π (ψ g : B) = algebraMap O E (D.Ψ g : O)
    rw [hψv, map_mul, hu1, mul_one, IsScalarTower.algebraMap_apply O E B, π.commutes,
      Algebra.algebraMap_self, RingHom.id_apply]
  · show Continuous fun g => ((r0 D.η ψ g).left : Matrix (Fin 3) (Fin 3) B) a b
    simp only [unitaryThreeReflection_left, tor_val]
    by_cases hab : a = b
    · subst hab; simp only [Matrix.diagonal_apply_eq]
      fin_cases a
      · simpa [wt1] using hψ
      · simpa [wt1] using (continuous_const : Continuous fun _ : GQ l => (1 : B))
      · simpa [wt1] using hψi
    · simp only [Matrix.diagonal_apply_ne _ hab]; exact continuous_const
  · obtain ⟨-, -, hφ, -, -⟩ := hl_basic D
    let κ (a : Fin 3) : ↥D.HL →* Bˣ := ((zpowGroupHom (wt1 a)).comp ψ).comp D.HL.subtype
    have hcyc (g) : j (cycA l l O g) = cycA l l B g := Units.ext (IsScalarTower.algebraMap_apply ℤ_[l] O B _).symm
    have hc_ch (a) : ContAction (chRep (κ a)) :=
      (Units.continuous_val.comp (((hψ'.zpow _).comp continuous_subtype_val).comp continuous_fst)).mul continuous_snd
    have hcr (a) : IsCr D.HL.subtype (chRep (κ a)) := crUnr D.HL.subtype hφ _ (hc_ch a) ((D.e : ℤ) * wt1 a) fun g hg _ => by
      simp only [chRep_apply, smul_eq_mul]; congr 1
      exact congrArg Units.val <| by
        change ψ g ^ wt1 a = cycA l l B g ^ ((D.e : ℤ) * wt1 a)
        have hψg : ψ g = cycA l l B g ^ D.e := by
          change j (D.Ψ g) * u g = _; rw [hI g hg, mul_one, D.Ψ_I g hg, g.2.2, mul_one, map_pow, hcyc]
        rw [hψg, ← zpow_natCast, ← zpow_mul]
    let ρ : ↥D.HL →* GL (Fin 3) B := ((tor B).comp ψ).comp D.HL.subtype
    have hp (a g x) : LinearMap.proj a (colRep ρ g x) = chRep (κ a) g (LinearMap.proj a x) :=
      R0.proj_diag (κ := κ) (fun _ => rfl) a g x
    have h0 : ContAction (colRep ρ) := continuous_pi fun a =>
      ((hc_ch a).comp (continuous_fst.prodMk ((continuous_apply a).comp continuous_snd))).congr fun p => (hp a p.1 p.2).symm
    have cprod {V V' : Type} [AddCommGroup V] [Module B V] [TopologicalSpace V] [AddCommGroup V'] [Module B V']
        [TopologicalSpace V'] {r1 : Representation B ↥D.HL V} {r2 : Representation B ↥D.HL V'}
        (h1 : ContAction r1) (h2 : ContAction r2) : ContAction (r1.prod r2) :=
      (h1.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk (h2.comp (continuous_fst.prodMk continuous_snd.snd))
    have h1 := (isCrys_isDR_prod _ hφ _ _ (hc_ch 0) (cprod (hc_ch 1) (hc_ch 2))).1 (hcr 0)
      ((isCrys_isDR_prod _ hφ _ _ (hc_ch 1) (hc_ch 2)).1 (hcr 1) (hcr 2))
    refine ⟨ρ, fun _ => rfl, ((isCrys_isDR_sub_quot _ hφ _ _ h0 (cprod (hc_ch 0) (cprod (hc_ch 1) (hc_ch 2)))
      ((LinearMap.proj 0).prod ((LinearMap.proj 1).prod (LinearMap.proj 2)))
      (fun g x => Prod.ext (hp 0 g x) (Prod.ext (hp 1 g x) (hp 2 g x)))).1 fun x y h => funext fun a => by
        fin_cases a
        · exact congrArg Prod.fst h
        · exact congrArg (fun z => z.2.1) h
        · exact congrArg (fun z => z.2.2) h).1 h1⟩

section CrPtsCore

variable (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E]
  [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E]
  (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
  [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B]

private theorem ordIdeal_eq_bot_of_inDcr (hL : LocalPublishedTheorems)
    (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* GG (m := 3) (R := B))
    (hr : D.InDcr (π : B →+* E) r) : ordIdeal D r = ⊥ := by
  obtain ⟨u, m, hu, -, -, rfl⟩ := (ordEq hL D E B π hπ r).1 hr
  have hd := triDiag D E B π hπ u hu
  have hm (s) (hs : s ∈ Iq l) : (conjBy m u s).mat =
      (m : Matrix (Fin 3) (Fin 3) B) * (u s).mat * ((m⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) := by
    simp only [GG.mat, conjBy_left, (hu.mult s).trans (D.η_unr s hs), sgnAct_one, Units.val_mul]
  have hc (A : Matrix (Fin 3) (Fin 3) B) (c : B) :
      (m : Matrix (Fin 3) (Fin 3) B) * A * ((m⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) - scalar _ c =
      (m : Matrix (Fin 3) (Fin 3) B) * (A - scalar _ c) * ((m⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) := by
    rw [mul_sub, sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).eq,
      mul_assoc (scalar _ c), Units.mul_inv, mul_one]
  rw [eq_bot_iff, ordIdeal, Ideal.span_le]
  rintro x (⟨s, hs, i, rfl⟩ | ⟨s, hs, i, j, rfl⟩)
  · have hcp : (conjBy m u s).mat.charpoly = ∏ a, (X - C (algebraMap O B (psi D.Ψ a s))) := by
      rw [hm s hs.2, Matrix.coe_units_inv, Matrix.charpoly_units_conj, Matrix.charpoly_of_isUpperTriangular]
      · simp only [hd s hs.2]
      · intro a b hab; exact hu.tri s a b (by have : (b : ℕ) < a := hab; simp only [wt, wt1]; omega)
    rw [hcp, sub_self, coeff_zero]; exact Submodule.zero_mem _
  · have hprod : ((u (s 0)).mat - scalar _ (algebraMap O B (psi D.Ψ 0 (s 0)))) *
        ((u (s 1)).mat - scalar _ (algebraMap O B (psi D.Ψ 1 (s 1)))) *
        ((u (s 2)).mat - scalar _ (algebraMap O B (psi D.Ψ 2 (s 2)))) = 0 := by
      have h10 (g) := hu.tri g 1 0 (by decide); have h20 (g) := hu.tri g 2 0 (by decide)
      have h21 (g) := hu.tri g 2 1 (by decide)
      ext p q; fin_cases p <;> fin_cases q <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, hd _ (hs 0).2, hd _ (hs 1).2, hd _ (hs 2).2]
    have hconj0 : D.sh (conjBy m u) 0 (s 0) * D.sh (conjBy m u) 1 (s 1) * D.sh (conjBy m u) 2 (s 2) = 0 := by
      simp only [Dat3.sh, hm _ (hs 0).2, hm _ (hs 1).2, hm _ (hs 2).2, hc]
      generalize (u (s 0)).mat - _ = A at hprod ⊢; generalize (u (s 1)).mat - _ = B' at hprod ⊢
      generalize (u (s 2)).mat - _ = C' at hprod ⊢
      simp only [mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc B', ← mul_assoc A, ← mul_assoc A, hprod, zero_mul, mul_zero]
    simp only [hconj0]; exact Submodule.zero_mem _

private theorem crPts_fracO (hL : LocalPublishedTheorems)
    (U : Univ (GCond.noCondition O D.η D.Ψ))
    (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (f : U.R →ₐ[O] B)
    (hf : D.InDcr (π : B →+* E) (push f U.r.hom)) : IY D U ≤ RingHom.ker f := by
  classical
  rintro a ⟨k, hk⟩
  have : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have : IsArtinianRing B := IsArtinianRing.of_finite E B
  obtain ⟨e, he⟩ : IsNilpotent (RingHom.ker (π : B →+* E)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    exact fun c hc => mem_nilradical.2 (hπ c (by simpa using hc))
  let N := 2 * k * e + 1
  have hN0 : N ≠ 0 := by omega
  let fE : E[X] := X ^ N; let fB : B[X] := X ^ N
  let C := AdjoinRoot fE; let T := AdjoinRoot fB
  have : Module.Finite E C := (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  have : Module.Finite B T := (AdjoinRoot.powerBasis' (monic_X_pow N)).finite
  have : Module.Finite E T := Module.Finite.trans B T
  have : Module.Finite ℚ_[l] C := Module.Finite.trans E C
  have : Module.Finite ℚ_[l] T := Module.Finite.trans E T
  set xE : C := AdjoinRoot.root fE; set xB : T := AdjoinRoot.root fB
  have hrootE : xE ^ N = 0 := by dsimp only [xE]; rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  have hrootB : xB ^ N = 0 := by dsimp only [xB]; rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  let πC : C →ₐ[E] E := AdjoinRoot.liftAlgHom fE (AlgHom.id E E) 0 (by simp [fE, hN0])
  let p₁ : T →ₐ[E] B := AdjoinRoot.liftAlgHom fB (AlgHom.id E B) 0 (by simp [fB, hN0])
  let p₂ : T →ₐ[E] C := AdjoinRoot.liftAlgHom fB ((Algebra.ofId E C).comp π) xE (by rw [eval₂_X_pow]; exact hrootE)
  have hp1 (q : B[X]) : p₁ (AdjoinRoot.mk fB q) = q.coeff 0 := by rw [AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]; rfl
  have hπC (q : E[X]) : πC (AdjoinRoot.mk fE q) = q.coeff 0 := by rw [AdjoinRoot.liftAlgHom_mk, eval₂_at_zero]; rfl
  have hp2 (q : B[X]) : p₂ (AdjoinRoot.mk fB q) = AdjoinRoot.mk fE (q.map (π : B →+* E)) := by
    rw [AdjoinRoot.liftAlgHom_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]; rfl
  have hp2map (q : E[X]) : p₂ (AdjoinRoot.mk fB (q.map (algebraMap E B))) = AdjoinRoot.mk fE q := by
    rw [hp2, Polynomial.map_map]; congr 1; conv_rhs => rw [← Polynomial.map_id (p := q)]
    congr 1; ext r; simp
  have hnilT (x : T) (hx : π (p₁ x) = 0) : IsNilpotent x := by
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x; rw [hp1] at hx
    obtain ⟨r, hr⟩ := X_dvd_iff.2 (show (q - Polynomial.C (q.coeff 0)).coeff 0 = 0 by simp)
    rw [show q = Polynomial.C (q.coeff 0) + X * r by rw [← hr]; ring, map_add (f := _), map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    exact Commute.isNilpotent_add (Commute.all _ _) ((hπ _ hx).map _) ⟨N, by rw [mul_pow, hrootB, zero_mul]⟩
  have hcomm : π.comp p₁ = πC.comp p₂ := AlgHom.ext fun x => by
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x; simp only [AlgHom.comp_apply, hp1, hp2, hπC, coeff_map]; rfl
  have hsurj (b : B) (c : C) (hbc : π b = πC c) : ∃ s, p₁ s = b ∧ p₂ s = c := by
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective c; rw [hπC] at hbc
    refine ⟨AdjoinRoot.of fB b + AdjoinRoot.mk fB (q.map (algebraMap E B)) - AdjoinRoot.of fB (algebraMap E B (q.coeff 0)),
      by rw [map_sub, map_add (f := _), ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp1, hp1, hp1]; simp,
      by rw [map_sub, map_add (f := _), hp2map, ← AdjoinRoot.mk_C, ← AdjoinRoot.mk_C, hp2, hp2]; simp [hbc]⟩
  obtain ⟨u, hu1, hu2, hu3, j, v, hj, hdel⟩ := del_unr_twist D E C xE ⟨N, hrootE⟩
  have hr₂ := twist_inDcr D E C πC u hu1 hu2 hu3
  let J : Ideal T := RingHom.ker p₁ ⊓ RingHom.ker p₂
  let qT : T →ₐ[E] (T ⧸ J) := Ideal.Quotient.mkₐ E J
  let q₁ : (T ⧸ J) →ₐ[E] B := Ideal.Quotient.liftₐ J p₁ fun _ h => h.1
  let q₂ : (T ⧸ J) →ₐ[E] C := Ideal.Quotient.liftₐ J p₂ fun _ h => h.2
  have hqsep (x y : T ⧸ J) (h1 : q₁ x = q₁ y) (h2 : q₂ x = q₂ y) : x = y := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective E J x
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mkₐ_surjective E J y
    exact Ideal.Quotient.eq.2 ⟨by change p₁ (s - t') = 0; rw [map_sub, sub_eq_zero]; exact h1,
      by change p₂ (s - t') = 0; rw [map_sub, sub_eq_zero]; exact h2⟩
  have hqsurj (b : B) (c : C) (h : π b = πC c) : ∃ x, q₁ x = b ∧ q₂ x = c := by
    obtain ⟨s, hs1, hs2⟩ := hsurj b c h; exact ⟨qT s, hs1, hs2⟩
  have hqnil (x : T ⧸ J) (hx : (π.comp q₁) x = 0) : IsNilpotent x := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective E J x; exact (hnilT s hx).map qT
  obtain ⟨r', hg₁, hg₂⟩ := glue_hom (q₁ : (T ⧸ J) →+* B) (q₂ : (T ⧸ J) →+* C)
    (π : B →+* E) (πC : C →+* E) hqsep hqsurj (push f U.r.hom) _ (hf.red.trans hr₂.red.symm)
  have hr' : D.InDcr ((π.comp q₁ : (T ⧸ J) →ₐ[E] E) : (T ⧸ J) →+* E) r' :=
    dcr_pair (q₁.restrictScalars ℚ_[l]) (q₂.restrictScalars ℚ_[l]) hqsep (hg₁.symm ▸ hf) (hg₂.symm ▸ hr₂)
  obtain ⟨r, hr, rfl⟩ := crLift hL D E T (π.comp p₁) hnilT (T ⧸ J) (π.comp q₁) hqnil qT
    (Ideal.Quotient.mkₐ_surjective E J) rfl r' hr'
  have hr₁ : (GG.map (p₁ : T →+* B)).comp r = push f U.r.hom := by rw [← hg₁]; rfl
  have hr₂' : (GG.map (p₂ : T →+* C)).comp r = r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u) := by rw [← hg₂]; rfl
  obtain ⟨F, hF, -⟩ := unramified_lift_deformation D U E T (π.comp p₁) hnilT ((π.restrictScalars O).comp f) r hr.mult
    (hr.red.trans hf.red.symm) hr.cont
  have hF1 : (p₁.restrictScalars O).comp F = f := by
    obtain ⟨_, -, hg⟩ := unramified_lift_deformation D U E B π hπ ((π.restrictScalars O).comp f) (push f U.r.hom) hf.mult rfl hf.cont
    exact (hg _ (by change (GG.map (p₁ : T →+* B)).comp (push F U.r.hom) = _; rw [hF]; exact hr₁)).trans (hg f rfl).symm
  have h0 := ordIdeal_eq_bot_of_inDcr D E T hL (π.comp p₁) hnilT r hr
  obtain ⟨hmap, -, hdelF⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D F U.r.hom
  have hPy : del D r ^ k * F a = 0 := by
    have h1 := Ideal.mem_map_of_mem (F : U.R →+* T) hk
    rw [hmap, hF, h0, Submodule.mem_bot, map_mul, map_pow] at h1
    change F (del D U.r.hom) ^ k * F a = 0 at h1; rwa [hdelF, hF] at h1
  obtain ⟨-, -, hdel2⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D (p₂.restrictScalars O) r
  have hP : p₂ (del D r ^ k) = xE ^ (j * k) * ((v ^ k : Cˣ) : C) := by
    have hdel2' : p₂ (del D r) = xE ^ j * (v : C) :=
      hdel2.trans (by change D.del ((GG.map (p₂ : T →+* C)).comp r) = _; rw [hr₂']; exact hdel)
    rw [map_pow, hdel2', mul_pow, ← pow_mul, Units.val_pow_eq_pow_val]
  obtain ⟨qv, hqv⟩ := AdjoinRoot.mk_surjective ((v ^ k : Cˣ) : C)
  let V : T := AdjoinRoot.mk fB (qv.map (algebraMap E B))
  have hV : p₂ V = (v ^ k : Cˣ) := by rw [hp2map, hqv]
  have hVu : IsUnit V := by
    have hw : π (p₁ V) ≠ 0 := by rw [← AlgHom.comp_apply, hcomm, AlgHom.comp_apply, hV]; exact ((v ^ k).isUnit.map πC).ne_zero
    have h1 : IsNilpotent (V - AdjoinRoot.of fB (algebraMap E B (π (p₁ V)))) := hnilT _ (by
      rw [map_sub, map_sub, AdjoinRoot.liftAlgHom_of, AlgHom.id_apply, π.commutes]; simp)
    simpa using h1.isUnit_add_left_of_commute (((Ne.isUnit hw).map (algebraMap E B)).map (AdjoinRoot.of fB)) (Commute.all _ _)
  obtain ⟨Vi, hVi⟩ := hVu.exists_right_inv
  let Q : T := del D r ^ k - xB ^ (j * k) * V
  have hQ2 : p₂ Q = 0 := by rw [map_sub, hP, map_mul, map_pow, hV, AdjoinRoot.liftAlgHom_root, sub_self]
  let K : Ideal T := (RingHom.ker (π : B →+* E)).map (AdjoinRoot.of fB)
  have hQK : Q ∈ K := by
    obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective Q; rw [← hq] at hQ2 ⊢; rw [hp2, AdjoinRoot.mk_eq_zero] at hQ2
    have hmod : (q %ₘ fB).map (π : B →+* E) = 0 := by
      rw [map_modByMonic _ (monic_X_pow N), show fB.map (π : B →+* E) = fE by simp [fB, fE]]
      exact (modByMonic_eq_zero_iff_dvd (monic_X_pow N)).2 hQ2
    have hmk : AdjoinRoot.mk fB q = AdjoinRoot.mk fB (q %ₘ fB) := by
      conv_lhs => rw [← modByMonic_add_div q fB]
      rw [map_add (f := _), map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    have hin : q %ₘ fB ∈ (RingHom.ker (π : B →+* E)).map (Polynomial.C : B →+* B[X]) :=
      Ideal.mem_map_C_iff.2 fun n => by rw [RingHom.mem_ker]; simpa using congrArg (fun p => p.coeff n) hmod
    rw [show K = ((RingHom.ker (π : B →+* E)).map Polynomial.C).map (AdjoinRoot.mk fB) by rw [Ideal.map_map]; rfl]
    exact Ideal.mem_map_of_mem _ hin
  let R' := -(Q * Vi)
  have hxR : xB ^ (j * k) * F a = R' * F a := by
    dsimp only [R', Q]; linear_combination -(xB ^ (j * k) * F a) * hVi + Vi * hPy
  have hpow (n : ℕ) : xB ^ (j * k * n) * F a = R' ^ n * F a := by
    induction n with
    | zero => simp
    | succ n ih => rw [mul_add, mul_one, @pow_add T _ xB (j * k * n) (j * k), mul_assoc, hxR]; linear_combination R' * ih
  have hRe : R' ^ e = 0 := Ideal.mem_bot.1 <| by
    have h3 : R' ^ e ∈ K ^ e := Ideal.pow_mem_pow (K.neg_mem (K.mul_mem_right _ hQK)) e
    rwa [← Ideal.map_pow, he, Ideal.zero_eq_bot, Ideal.map_bot] at h3
  have hy0 : xB ^ (j * k * e) * F a = 0 := by rw [hpow, hRe, zero_mul]
  change f a = 0; rw [← hF1]; change p₁ (F a) = 0
  obtain ⟨qy, hqy⟩ := AdjoinRoot.mk_surjective (F a)
  rw [← hqy, hp1]
  rw [← hqy, show xB = AdjoinRoot.mk fB X from AdjoinRoot.mk_X.symm, ← map_pow, ← map_mul, AdjoinRoot.mk_eq_zero] at hy0
  obtain ⟨s, hs⟩ := hy0
  have h4 := congrArg (fun p => p.coeff (j * k * e)) hs
  simp only [fB, coeff_X_pow_mul'] at h4
  have hlt : j * k * e < N := Nat.lt_succ_of_le (Nat.mul_le_mul_right e (Nat.mul_le_mul_right k hj))
  simpa [Nat.not_le.2 hlt] using h4

end CrPtsCore

private theorem crPts_IY (hP : LocalPublishedTheorems)
    (U : Univ (GCond.noCondition O D.η D.Ψ)) : CrPts D U (IY D U) := by
  intro E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ f hD
  classical
  have hi : Function.Injective (algebraMap ℤ_[l] O) := by
    rw [RingHom.injective_iff_ker_eq_bot]; by_contra h
    have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := (inferInstance : Ideal.IsPrime _).isMaximal h
    exact IsDiscreteValuationRing.not_a_field O
      (eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) ⊥ hm)).symm
  have : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  let E₀ := FractionRing O
  have hi2 : Function.Injective (algebraMap ℤ_[l] E₀) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O E₀]; exact (IsFractionRing.injective O E₀).comp hi
  let : Algebra ℚ_[l] E₀ := (IsFractionRing.lift hi2).toAlgebra
  have : IsScalarTower ℤ_[l] ℚ_[l] E₀ := IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  have : Module.Finite ℚ_[l] E₀ := Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])
  have hOE : Function.Injective (algebraMap O E) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_under_eq_bot (R := ℤ_[l]) ?_
    change Ideal.comap (algebraMap ℤ_[l] O) (RingHom.ker (algebraMap O E)) = ⊥
    rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq, ← RingHom.injective_iff_ker_eq_bot,
      IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  let : Algebra E₀ E := (IsFractionRing.lift hOE).toAlgebra
  have : IsScalarTower O E₀ E := IsScalarTower.of_algebraMap_eq fun c => (IsFractionRing.lift_algebraMap hOE c).symm
  let : Algebra E₀ B := Algebra.compHom B (algebraMap E₀ E)
  have : IsScalarTower E₀ E B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower O E₀ B := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap E B (algebraMap E₀ E (algebraMap O E₀ c))
    rw [← IsScalarTower.algebraMap_apply O E₀ E, ← IsScalarTower.algebraMap_apply O E B]
  have hQ : (algebraMap E₀ E).comp (algebraMap ℚ_[l] E₀) = algebraMap ℚ_[l] E :=
    IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => by
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E₀, IsScalarTower.algebraMap_apply ℤ_[l] O E₀,
        ← IsScalarTower.algebraMap_apply O E₀ E, ← IsScalarTower.algebraMap_apply ℤ_[l] O E,
        IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E])
  have : IsScalarTower ℚ_[l] E₀ B := IsScalarTower.of_algebraMap_eq fun q => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] E B, ← hQ]; rfl
  have : IsScalarTower ℤ_[l] E₀ B := IsScalarTower.of_algebraMap_eq fun z => by
    change _ = algebraMap E B (algebraMap E₀ E (algebraMap ℤ_[l] E₀ z))
    rw [IsScalarTower.algebraMap_apply ℤ_[l] O E₀, ← IsScalarTower.algebraMap_apply O E₀ E,
      ← IsScalarTower.algebraMap_apply O E B, ← IsScalarTower.algebraMap_apply ℤ_[l] O B]
  obtain ⟨x, hx, -⟩ := univEx D U
  have hpb (F : Type) [Field F] [Algebra O F] : push ((Algebra.ofId O F).comp x) U.r.hom = D.rz F := by
    unfold Dat3.rz; rw [← show push x U.r.hom = r0 D.η D.Ψ from hx]; rfl
  have hfx (a : U.R) : π (f a) = algebraMap O E (x a) := by
    let y : U.R →ₐ[O] E := (π.restrictScalars O).comp f
    obtain ⟨_, -, hu⟩ := unramified_lift_deformation D U E E (AlgHom.id E E) (fun _ h => by simpa using h) y (push y U.r.hom)
      (fun g => U.r.hasMult g) rfl (fun a b => (ptCont (l := l) U.R E y).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b))
    exact congrArg (fun φ : U.R →ₐ[O] E => φ a) ((hu y rfl).trans (hu ((Algebra.ofId O E).comp x) ((hpb E).trans hD.red.symm)).symm)
  let B₀ : Subalgebra E₀ B :=
    { carrier := {b | π b ∈ Set.range (algebraMap E₀ E)}
      mul_mem' := by rintro a b ⟨u, hu⟩ ⟨v, hv⟩; exact ⟨u * v, by rw [map_mul, hu, hv, map_mul]⟩
      add_mem' := by rintro a b ⟨u, hu⟩ ⟨v, hv⟩; exact ⟨u + v, by rw [map_add (f := _), hu, hv, map_add (f := _)]⟩
      algebraMap_mem' := fun c => ⟨c, by rw [IsScalarTower.algebraMap_apply E₀ E B, π.commutes]; rfl⟩ }
  let f₀ : U.R →ₐ[O] B₀ := f.codRestrict (B₀.restrictScalars O) fun a =>
    ⟨algebraMap O E₀ (x a), by rw [hfx, IsScalarTower.algebraMap_apply O E₀ E]⟩
  choose p hp using fun b : B₀ => b.2
  have hinj : Function.Injective (algebraMap E₀ E) := (algebraMap E₀ E).injective
  let π₀ : B₀ →ₐ[E₀] E₀ :=
    { toFun := p
      map_one' := hinj (by rw [hp]; simp)
      map_mul' := fun a b => hinj (by rw [hp, map_mul, hp, hp]; simp)
      map_zero' := hinj (by rw [hp]; simp)
      map_add' := fun a b => hinj (by rw [hp, map_add (f := _), hp, hp]; simp)
      commutes' := fun c => hinj (by rw [hp]; show π (algebraMap E₀ B c) = _; rw [IsScalarTower.algebraMap_apply E₀ E B, π.commutes]; rfl) }
  have hπ₀ (a : B₀) (ha : π₀ a = 0) : IsNilpotent a := by
    obtain ⟨n, hn⟩ := hπ _ (by rw [← hp a]; change algebraMap E₀ E (π₀ a) = 0; rw [ha, map_zero])
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  let val' : B₀ →ₐ[ℚ_[l]] B := B₀.val.restrictScalars ℚ_[l]
  have : Module.Finite ℚ_[l] B₀ := Module.Finite.of_injective val'.toLinearMap Subtype.val_injective
  have hpush : (GG.map (val' : B₀ →+* B)).comp (push f₀ U.r.hom) = push f U.r.hom := rfl
  have hq := dcr_pair (D := D) val' val' (fun _ _ h _ => Subtype.ext h) (r := push f₀ U.r.hom)
    (hpush.symm ▸ hD) (hpush.symm ▸ hD)
  have h1 : (π₀.restrictScalars O).comp f₀ = (Algebra.ofId O E₀).comp x := AlgHom.ext fun a => hinj <| by
    change algebraMap E₀ E (p (f₀ a)) = algebraMap E₀ E (algebraMap O E₀ (x a))
    rw [hp, ← IsScalarTower.algebraMap_apply O E₀ E]; exact hfx a
  have hD₀ : D.InDcr (π₀ : B₀ →+* E₀) (push f₀ U.r.hom) :=
    ⟨hq.mult, by rw [← hpb E₀, ← h1]; rfl, hq.cont, hq.cr⟩
  intro a ha
  exact congrArg Subtype.val (crPts_fracO D E₀ B₀ hP U π₀ hπ₀ f₀ hD₀ ha)

end Dat3Core

end GlobalTheory.OrdLoc.CrystallineLocus

set_option linter.overlappingInstances false in
public theorem _root_.GlobalTheory.T.saturatedOrdinaryIdeal_cuts_out_crystalline_locus :
    LocalPublishedTheorems →
      ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
        [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O]
        (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)),
        GlobalTheory.OrdLoc.PtsCr D U (GlobalTheory.OrdLoc.IY D U) ∧
        GlobalTheory.OrdLoc.CrPts D U (GlobalTheory.OrdLoc.IY D U) :=
  fun hP _ _ _ _ _ _ _ _ _ _ D U =>
    ⟨GlobalTheory.OrdLoc.CrystallineLocus.ptsCr_IY D hP U,
     GlobalTheory.OrdLoc.CrystallineLocus.crPts_IY D hP U⟩
