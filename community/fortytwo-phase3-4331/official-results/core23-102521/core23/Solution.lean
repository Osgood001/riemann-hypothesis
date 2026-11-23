import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormChernIntegrableOfPrincipalisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightNonnegVerticalOfNefOnFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalyticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantProjArithSurjectiveComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSmallSectionsLeOfHermLBLeBySmallSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfSmallSectionLogCountUpperBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithmeticCoverOverModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasepointFreeSectionTupleAmpleArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirationalModelTotallyOrderedFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermPairAdaptedTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermLineBundlePairPullbackDominantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensEtaleGenericallyFiniteDominantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecNonzeroOnFiniteOfGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistNefSquarefreeMonomialsSmallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianMetricGrading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLeShiftOfSmallSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyWeightIncrementSemiPositiveCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePullBirationalModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightGenericPointNonnegAmpleSemiPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeNonnegOfSemiPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodSectionGroupFamilyAmpleMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeAddMulLogSqOfLeAddMulLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNcardUnitBallLeOfIndependentLevelBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundAlongResidues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralEqSumEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefAtOfPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreOfNormsPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFubiniStudyBoxFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFnFamilySmallPullbackBirationalModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectAddBundleSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySectionsGeneratedBundlesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySideEqGenericFibrePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqOneOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedArchIntegralEqSumClosureIntegralsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionCountGrowthMetricNearGeneratorMaxStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionCanonicalWeightsTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionMonoOfHeightNefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfPullbackGenericallyEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullOfGenericallySmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullbackGenericallyBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPositivePullbackGenericallyEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveOfIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLogTwistContinuityAboveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsPairSumRatFnFamilyTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogSectionCountChangeOfMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAmpleGloballyGenerated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfInducedOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistMove

theorem exists_generating_secs_tens_lbPow {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F)
    (H : LB X) (N : ℕ) (s : Fin (N + 1) → H.Sec) (hH : H.IsLB) (hs : AbLaw.VeryAmpleBy p H s)
    (M : LB X) (hM : M.IsLB) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (n : ℕ) (u : Fin n → (CechPic.tens M (lbPow H m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated F X p H N s hH hs M hM
  refine ⟨t₀.toNat, fun m hm => ?_⟩
  obtain ⟨n, u, hu⟩ := ht m (by omega)
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens M (lbPow H m)).IsLB := isLB_tens hM hP
  have e : cls (AbLaw.tw M H m) (AbLaw.isLB_tw hM hH _) =
      cls M hM - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hM (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hM hH _)
  have e' : cls (AbLaw.tw M H m) (AbLaw.isLB_tw hM hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hM hP, cls_lbPow hH, neg_zsmul, natCast_zsmul,
      sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨_, v, hv⟩

theorem exists_twist_generated_sec_nonzero : ∀ (F : Type) [Field F] [Infinite F] (X : Scheme.{0}) (p : X ⟶ Sp F), IsProjOver p → ∀ (B : LB X), B.IsLB → ∀ S : Set X, S.Finite → ∃ (A : LB X) (_ : A.IsLB) (a : A.Sec), (∃ (n : ℕ) (u : Fin n → A.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ (∃ (n : ℕ) (u : Fin n → (CechPic.tens B A).Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ ∀ z ∈ S, z ∈ nonzeroLocus a := by
  intro F _ _ X p hp B hB S hS
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨N, ι, hι, e⟩ := hp
  haveI := hι
  have hs := ProjSpace.veryAmpleBy_secPull_coord ι
  rw [e] at hs
  have hH : ((ProjSpace.O1 F N).pull ι).IsLB := pull_isLB (ProjSpace.O1_isLB F N) _
  obtain ⟨H, hH, s, hs⟩ : ∃ H : LB X, H.IsLB ∧ ∃ s : Fin (N + 1) → H.Sec, AbLaw.VeryAmpleBy p H s :=
    ⟨_, hH, _, hs⟩
  obtain ⟨m₁, h₁⟩ := exists_generating_secs_tens_lbPow p H N s hH hs B hB
  obtain ⟨m₂, h₂⟩ := exists_generating_secs_tens_lbPow p H N s hH hs (LB.triv X) (LB.isLB_triv X)
  obtain ⟨n₁, u₁, hu₁⟩ := h₁ (max m₁ m₂) (le_max_left _ _)
  obtain ⟨n₂, u₂, hu₂⟩ := h₂ (max m₁ m₂) (le_max_right _ _)
  have hP : (lbPow H (max m₁ m₂)).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens (LB.triv X) (lbPow H (max m₁ m₂))).IsLB := isLB_tens (LB.isLB_triv X) hP
  have e₂ : cls _ hT = cls _ hP := by rw [cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hP e₂ _ u₂ hu₂
  obtain ⟨a, ha⟩ := exists_sec_nonzero_on_finite_of_generated F X p _ hP _ v hv S hS
  exact ⟨_, hP, a, ⟨_, v, hv⟩, ⟨_, u₁, hu₁⟩, ha⟩

end GlobalTheory.TwistMove
end


section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm

namespace GlobalTheory.NefHodgeTateAt

section Curves

variable {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem topSelf_of_cls_eq_add (hp : IsProjOver p) {N A B : LB X} (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (h : cls N hN = cls A hA + cls B hB) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ (N.pull i) 1 = topSelfIntersection κ (A.pull i) 1 + topSelfIntersection κ (B.pull i) 1 := by
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have e2 (L : LB X) : topSelfIntersection κ (L.pull i) 1 = interNum κ (structureModule Z) ![L.pull i] := by
    rw [topSelf_def]
    congr 1
    funext j
    fin_cases j
    rfl
  rw [e2, e2, e2]
  refine interNum_one_of_cls_eq_add (hH.pull_of_isClosedImmersion i) hd (LB.isLB_pull hN i) (LB.isLB_pull hA i)
    (LB.isLB_pull hB i) ?_
  rw [cls_pull hN, cls_pull hA, cls_pull hB, h, map_add]

theorem topSelf_pow (hp : IsProjOver p) (L : HermLB p) (m : ℕ) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
  have c (n : ℕ) : cls (L.pow n).B (L.pow n).isLB = n • cls L.B L.isLB := cls_lbPow L.isLB n _
  induction m with
  | zero =>
    have := topSelf_of_cls_eq_add hp (L.pow 0).isLB (L.pow 0).isLB (L.pow 0).isLB (by rw [c]; simp) Z i κ hd
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ n ih =>
    rw [topSelf_of_cls_eq_add hp (L.pow (n + 1)).isLB (L.pow n).isLB L.isLB (by rw [c, c, succ_nsmul]) Z i κ hd, ih]
    push_cast
    ring

theorem nefOver_tens (hp : IsProjOver p) {L M : HermLB p} {l : ℕ} (hL : NefOver L l) (hM : NefOver M l) :
    NefOver (L.tens M) l := fun Z i _ _ κ _ _ _ _ hd => by
  rw [topSelf_of_cls_eq_add hp (L.tens M).isLB L.isLB M.isLB (cls_tens L.isLB M.isLB _) Z i κ hd]
  exact add_nonneg (hL Z i κ hd) (hM Z i κ hd)

theorem nefOver_pow (hp : IsProjOver p) {L : HermLB p} {l : ℕ} (hL : NefOver L l) (m : ℕ) :
    NefOver (L.pow m) l := fun Z i _ _ κ _ _ _ _ hd => by
  rw [topSelf_pow hp L m Z i κ hd]
  exact mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)

theorem nefOver_of_pow (hp : IsProjOver p) {L : HermLB p} {l m : ℕ} (hm : 0 < m) (hL : NefOver (L.pow m) l) :
    NefOver L l := fun Z i _ _ κ _ _ _ _ hd => by
  have h := hL Z i κ hd
  rw [topSelf_pow hp L m Z i κ hd] at h
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm)).1 h

omit [Module.Finite ℤ k] in

theorem nefOver_of_cls_eq {L M : HermLB p} {l : ℕ} (h : cls L.B L.isLB = cls M.B M.isLB) (hM : NefOver M l) :
    NefOver L l := fun Z i _ _ κ _ _ _ _ hd => by
  have : topSelfIntersection κ (L.B.pull i) 1 = topSelfIntersection κ (M.B.pull i) 1 :=
    interNum_congr_cls κ _ (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull M.isLB i) fun _ => by
      rw [cls_pull L.isLB, cls_pull M.isLB, h]
  rw [this]
  exact hM Z i κ hd

end Curves

theorem cls_eq_of_presents {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L M : LB X} {r : L.ι → X.functionFieldˣ}
    {r' : M.ι → X.functionFieldˣ} (h : Presents D L r) (h' : Presents D M r') : cls L h.isLB = cls M h'.isLB := by
  choose a ha using fun q : M.ι × L.ι => exists_unit_fnOf_eq (U := M.U q.1 ⊓ L.U q.2)
    fun x hx => (h.isEqn _ x hx.2).iff_unitAt.1 (h'.isEqn _ x hx.1)
  refine (cls_eq_iff _ _).2 ⟨⟨a⟩, fun p q => Units.ext (Cartier.fn_ext fun hpq => ?_)⟩
  have e := congrArg (fnOf (L.U p.2 ⊓ L.U q.2) (memInf hpq.1.2 hpq.2.2)) (L.g p.2 q.2).inv_mul
  rw [map_mul, map_one] at e
  refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ hpq _) (fnOf_resG _ hpq _)))
    (fnOf_resG _ hpq _))).symm)
  refine (ha p _).trans (Eq.trans ?_ (congrArg _ (ha q _)).symm)
  rw [h.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2), h'.isRatSec p.1 q.1 (memInf hpq.1.1 hpq.2.1),
    mul_div_mul_comm, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_left e]
  rfl

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem j_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h₁ (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
    change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
    have := ((V.π ≫ Y.str) y).isPrime
    rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have h₂ {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
    rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
    change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans (h₁ _).le)
  obtain ⟨y, hy⟩ := h₂ h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem w_div_eq_one {Z : Scheme.{0}} [IsIntegral Z] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ Z) {c a b : Z.functionField} (ha : UnitAt (below z) (c * a))
    (hb : UnitAt (below z) (c * b))
    (h : Real.log (e.w (valAt z (c * a))) = Real.log (e.w (valAt z (c * b)))) :
    e.w (valAt z (b / a)) = 1 := by
  have hc : c ≠ 0 := left_ne_zero_of_mul ha.ne_zero
  have ha0 : a ≠ 0 := right_ne_zero_of_mul ha.ne_zero
  have e₁ : b / a = (c * b) * (c * a)⁻¹ := by field_simp
  have pa := e.w.pos (SmallSec.valAt_ne_zero ha)
  have pb := e.w.pos (SmallSec.valAt_ne_zero hb)
  have e₂ := Real.log_injOn_pos pa pb h
  rw [e₁, SmallSec.valAt_mul hb.regAt ha.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv ha, map_mul, map_inv₀, ← e₂,
    mul_inv_cancel₀ pa.ne']

theorem cls_eq_of_norms {V : Cover Y} {L L' : HermLB V.p} {f : Y.X → Y.Fn} {a a' : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (h' : Norms V L' f a' l) :
    cls L.B L.isLB = cls L'.B L'.isLB := by
  obtain ⟨r, hr, hu, -, hf⟩ := h
  obtain ⟨r', hr', hu', -, hf'⟩ := h'
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField), valAt (y ≫ V.j) g = valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr
  have hR' := InducedIsom.isRatSec_lift V.j ρ hρ hj L'.B hr'
  have hP := presents_divOfRatSec L.isLB hR
  have eρ (a b : V.G.functionFieldˣ) : ρ ((Units.map ρ.symm.toMonoidHom b : V.X.functionField) /
      (Units.map ρ.symm.toMonoidHom a : V.X.functionField)) = (b : V.G.functionField) / a := by
    rw [map_div₀]
    exact congrArg₂ (· / ·) (ρ.apply_symm_apply _) (ρ.apply_symm_apply _)
  have key : ∀ (i : L.B.ι) (j : L'.B.ι) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
      (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) →
      spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ (L.B.U i ⊓ L'.B.U j) →
      e.w (valAt z (((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField) /
        ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) = 1 ∧
      e.w (valAt z (((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) /
        ((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField))) = 1 := by
    intro i j v e z yt hz e₂ hU
    let y : AlgPt Y := ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩
    have h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U ((fun _ => i : (L.B.pull V.j).ι) PUnit.unit) := fun w hw => (hU hw).1
    have h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U ((fun _ => j : (L'.B.pull V.j).ι) PUnit.unit) := fun w hw => (hU hw).2
    have H₁ := hf v e y z yt (fun _ => i) rfl e₂ h₁
    have H₂ := hf' v e y z yt (fun _ => j) rfl e₂ h₂
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U i ⊓ L'.B.U j := by
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have m₁ : below z ∈ (L.B.pull V.j).U (fun _ => i) := Set.mem_iInter.2 fun _ => hpt.1
    have m₂ : below z ∈ (L'.B.pull V.j).U (fun _ => j) := Set.mem_iInter.2 fun _ => hpt.2
    have hπ : V.π (below z) = below y.1 := rfl
    have u₁ := hu _ _ m₁
    have u₂ := hu' _ _ m₂
    rw [hπ] at u₁ u₂
    exact ⟨w_div_eq_one e z u₁ u₂ (H₁.symm.trans H₂), w_div_eq_one e z u₂ u₁ (H₂.symm.trans H₁)⟩
  refine cls_eq_of_presents hP ⟨L'.isLB, hR', fun j x hxj => ?_⟩
  obtain ⟨i, hxi⟩ := exists_chart L.isLB x
  refine (hP.isEqn i x hxi).iff_unitAt.2
    ((unitAt_iff (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))).2 ⟨?_, ?_⟩)
  · refine Cover.RegCrit.regAt_of_integral_values F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩
    rw [hv, eρ]
    exact (key i j v e z yt hz h hU).1.le
  · rw [inv_div]
    refine Cover.RegCrit.regAt_of_integral_values F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩
    rw [hv, eρ]
    exact (key i j v e z yt hz h hU).2.le

theorem norms_scale {V : Cover Y} {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) {b : F} (hb : b ≠ 0) :
    ∃ a', Norms V L f a' fun v e y => Real.log (NumberField.HeightOneSpectrum.adicAbv F v b) + l v e y := by
  have hu (x : Y.X) := IndScale.unitAt_constFn Y.str x hb
  obtain ⟨r, hr, h₁, h₂, h₃⟩ := norms_mul_unit F Y V L f a l (fun _ => Cartier.constFn Y.str b) hu h
  let c : V.G.functionFieldˣ := Units.mk0 (V.φ (Cartier.constFn Y.str b))
    ((map_ne_zero V.φ).2 (hu (genericPoint Y.X)).ne_zero)
  have e (g : Y.Fn) (i) : V.φ g * ((c * r i : V.G.functionFieldˣ) : V.G.functionField) =
      V.φ (Cartier.constFn Y.str b * g) * r i := by
    rw [map_mul, Units.val_mul, Units.val_mk0]
    ring
  refine ⟨fun σ y => Real.log ‖ratVal (Cartier.constFn Y.str b) y‖ + a σ y, fun i => c * r i, fun i j hij => ?_,
    fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_, fun v ε y z yt i e₁ e₂ hi => ?_⟩
  · rw [Units.val_mul, Units.val_mul, hr i j hij]
    ring
  · rw [e]
    exact h₁ i x hx
  · rw [e]
    exact h₂ σ z y y' i e₁ e₂ hi
  · have := h₃ v ε y z yt i e₁ e₂ hi
    beta_reduce at this
    rw [IndScale.valAt_constFn Y.str _ y.1 y.2, ε.w_alg] at this
    rw [e]
    exact this

theorem exists_integral_point (V : Cover Y) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) :
    ∃ (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 ∧
      spMap e.O.subtype ≫ yt = z ≫ V.j := by
  obtain ⟨y⟩ := ValGroup.nonempty_algPt Y
  obtain ⟨z, hz⟩ := exists_lift_pt V.π y.1
  have hP : IsProper V.p := (isProper_and_exists_isAmpleLB_of_isProjOver V.ar.isProjOver).1
  have hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O := by
    intro a
    rw [e.mem_O, RingHom.comp_apply, e.w_alg]
    exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  let φ : 𝓞 F →+* e.O := ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem
  have hE : ValuativeCriterion.Existence V.p := by
    have h : UniversallyClosed V.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hsq : CommSq (z ≫ V.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) V.p (spMap φ) := by
    refine ⟨?_⟩
    rw [Category.assoc, V.pb.w, ← Category.assoc, ← Category.assoc z, hz, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := z ≫ V.j, i₂ := spMap φ, commSq := hsq }
  exact ⟨y, z, l.l, hz, l.fac_left⟩

theorem nefOver_of_norms {V : Cover Y} {L L' : HermLB V.p} {f : Y.X → Y.Fn} {a a' : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} {c : HeightOneSpectrum (𝓞 F) → ℝ}
    (hc : (Function.support c).Finite) (h : Norms V L f a fun v e y => l v e y + c v) (h' : Norms V L' f a' l) {q : ℕ}
    (hq : NefOver L' q) : NefOver L q := by
  obtain ⟨m, b, b', hb, hb', E⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F c hc fun v => by
    obtain ⟨e⟩ : Nonempty (Ext v) := inferInstance
    obtain ⟨y, z, yt, e₁, e₂⟩ := exists_integral_point V v e
    obtain ⟨r, -, -, -, hf⟩ := h
    obtain ⟨r', -, -, -, hf'⟩ := h'
    have chart (B : HermLB V.p) : ∃ i, ⊤ ≤ yt ⁻¹ᵁ B.B.U i := by
      obtain ⟨i, hi⟩ := exists_chart B.isLB (yt (IsLocalRing.closedPoint e.O))
      exact ⟨i, ((IsLocalRing.closedPoint_mem_iff (R := e.O) (yt ⁻¹ᵁ B.B.U i)).1 hi).ge⟩
    obtain ⟨i, hi⟩ := chart L
    obtain ⟨i', hi'⟩ := chart L'
    have h₁ := hf v e y z yt (fun _ => i) e₁ e₂ hi
    have h₂ := hf' v e y z yt (fun _ => i') e₁ e₂ hi'
    obtain ⟨α, hα, h₃⟩ := ValGroup.exists_log_sub e.w
      (valAt z (V.φ (f (below y.1)) * (r' fun _ => i' : V.G.functionFieldˣ)))
      (valAt z (V.φ (f (below y.1)) * (r fun _ => i : V.G.functionFieldˣ)))
    have : c v = Real.log (e.w α) := by
      rw [← h₃, ← h₁, ← h₂]
      ring
    rw [this]
    exact GlobalTheory.ExtValueGroup.log_w_rat F v e α hα
  have ne {x : 𝓞 F} (hx : x ≠ 0) : algebraMap (𝓞 F) F x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hx
  obtain ⟨a₁, h₁⟩ := norms_scale (norms_pow F Y V L _ _ _ m h) (ne hb')
  obtain ⟨a₂, h₂⟩ := norms_scale (norms_pow F Y V L' _ _ _ m h') (ne hb)
  have hcl := cls_eq_of_norms h₁ (h₂.congr (fun _ => rfl) (fun _ _ => rfl) fun v e y => by
    linear_combination -E v)
  exact nefOver_of_pow V.ar.isProjOver m.pos (nefOver_of_cls_eq hcl (nefOver_pow V.ar.isProjOver hq m))

theorem norms_of_comb {V : Cover Y} {C : CxSt F} {A : Adl C Y} {ι : Type} [Fintype ι] {ρ : ι → Adl C Y} {q : ℕ} {b : ι → ℤ}
    (hD : q • A.D = ∑ i, b i • (ρ i).D)
    (hfin : ∀ v e y, q * A.lg v e y =
      Real.log (e.w (valAt y.1 (genAt A.D (below y.1) ^ q / ∏ i, genAt (ρ i).D (below y.1) ^ b i))) +
        ∑ i, b i * (ρ i).lg v e y) {N : HermLB V.p} {K : ℕ} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    (h : Norms V N (fun x => (∏ i, genAt (ρ i).D x ^ b i) ^ K) a fun v e y => K * ∑ i, b i * (ρ i).lg v e y) :
    ∃ a', Norms V N (fun x => genAt A.D x ^ (K * q)) a' fun v e y => ((K * q : ℕ) : ℝ) * A.lg v e y := by
  classical
  have hu0 : ∀ x, UnitAt x (genAt A.D x ^ q / ∏ i, genAt (ρ i).D x ^ b i) := by
    intro x
    have h₁ := (Base.isEqn_eqn A.D x).nsmul q
    have h₂ : (∑ i, b i • (ρ i).D).IsEqn x (∏ i, eqn (ρ i).D x ^ b i) := by
      have key : ∀ s : Finset ι, (∑ i ∈ s, b i • (ρ i).D).IsEqn x (∏ i ∈ s, eqn (ρ i).D x ^ b i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using CartierDiv.isEqn_zero x
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.prod_insert hj]
          exact ((Base.isEqn_eqn (ρ j).D x).zsmul (b j)).add ih
      exact key _
    rw [hD] at h₁
    have h₃ := h₁.iff_unitAt.1 h₂
    convert h₃ using 1
    simp only [genAt, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Units.coe_prod, inv_pow, inv_zpow', Finset.prod_inv_distrib]
    simp only [zpow_neg, Finset.prod_inv_distrib, div_inv_eq_mul]
    rw [mul_comm, div_eq_mul_inv]
  have hP : ∀ x, (∏ i, genAt (ρ i).D x ^ b i) ≠ 0 := fun x =>
    Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (Units.ne_zero _)
  have h2 := norms_mul_unit F Y V _ _ _ _ (fun x => (genAt A.D x ^ q / ∏ i, genAt (ρ i).D x ^ b i) ^ K)
    (fun x => InducedPow.unitAt_pow (hu0 x) K) h
  refine ⟨_, h2.congr (fun x => ?_) (fun _ _ => rfl) fun v w y => ?_⟩
  · rw [← mul_pow, div_mul_cancel₀ _ (hP x), ← pow_mul, mul_comm q K]
  · rw [InducedPow.valAt_pow _ (hu0 _).regAt K, map_pow, Real.log_pow]
    have H := hfin v w y
    generalize Real.log (w.w (TrueGeo.valAt y.1 (genAt A.D (below y.1) ^ q / ∏ i, genAt (ρ i).D (below y.1) ^ b i))) = Aq at H ⊢
    push_cast
    linear_combination -(K : ℝ) * H

theorem nefAt_of_cover {C : CxSt F} {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+}
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hI : A.Induced M L k cf) (V : Cover Y) (l : ℕ) [Fact l.Prime]
    (h : ∀ V' : Cover Y, (∀ (B : HermLB V.p) f a g, Norms V B f a g → ∃ B' : HermLB V'.p, Norms V' B' f a g) →
      ∃ (N : HermLB V'.p) (m : ℕ) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), 0 < m ∧
        (Norms V' N (fun x => genAt A.D x ^ m) a fun v e y => m * A.lg v e y) ∧ NefOver N l)
    (Z : Scheme.{0}) (i : Z ⟶ M.X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod l) Γ(Z, ⊤)]
    (hd : topologicalKrullDim Z = 1) : 0 ≤ topSelfIntersection (ZMod l) (L.B.pull i) 1 := by
  obtain ⟨P, π, -, hP, hπ, -, hj, -, hU, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  have h₁ := InducedPull.induced_pull F C Y A M P π hπ hj L k cf hI
  have h₂ := h₁.twist_fin (c := -cf) (by rw [Function.support_neg]; exact hI.1)
  rw [add_neg_cancel] at h₂
  have h₃ := norms_of_induces (Cover.induces_ofModel hP h₂)
  obtain ⟨V', a, g, b, ha, hb, e₁, e₂, e₃, e₄⟩ := CoverDom.exists_cover_dominating F Y V P
  have hη : V'.π (genericPoint V'.G) = genericPoint Y.X := by
    have := (genericPoint_spec V'.G).image V'.π.continuous
    rw [Set.image_univ, V'.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  have h₄ := GlobalTheory.T.norms_pullback_along_cover F Y (Cover.ofModel P hP) V' b hb V'.π e₄ (Category.comp_id _) hη _ _ _ _ h₃
  have hbη := (CoverDeg.map_genericPoint_and_deg F Y (Cover.ofModel P hP) V' b hb V'.π e₄ (Category.comp_id _) hη).1
  obtain ⟨N, m, aN, hm, hN, hnef⟩ := h V' fun B f a' g' hB =>
    ⟨_, GlobalTheory.T.norms_pullback_along_cover F Y V V' a ha g e₁ e₂ e₃ B f a' g' hB⟩
  have h₅ := norms_pow F Y V' _ _ _ _ m h₄
  have h₆ := norms_pow F Y V' _ _ _ _ k hN
  have h₇ : NefOver (((L.pull π hπ).pull b hb).pow m) l :=
    nefOver_of_norms (c := fun v => (m : ℝ) * k * (A.n : ℕ) * cf v)
      (hI.1.subset fun v hv h0 => hv (by simp [h0]))
      (h₅.congr (fun x => by rw [← pow_mul, ← pow_mul, mul_comm]; rfl) (fun _ _ => rfl) fun v e y => by
        simp only [Adl.twist, Pi.neg_apply]
        ring) h₆ (nefOver_pow V'.ar.isProjOver hnef k)
  have h₈ := nefOver_of_pow V'.ar.isProjOver hm h₇
  have := P.ar.isIntegral
  have : IsProper P.p := (isProper_and_exists_isAmpleLB_of_isProjOver P.ar.isProjOver).1
  have : IsProper (b ≫ P.p) := by
    rw [hb]
    exact (isProper_and_exists_isAmpleLB_of_isProjOver V'.ar.isProjOver).1
  have : IsProper b := IsProper.of_comp b P.p
  have hbs : Function.Surjective b := fun x =>
    (genericPoint_specializes x).mem_closed b.isClosedMap.isClosed_range ⟨_, hbη⟩
  exact NefDeRhamAt.nefAt_of_pull _ M.X P.X M.p P.p M.ar.isProjOver P.ar.isProjOver π hπ
    (NefFibUniq.surjective_of_models M P π hπ hU) L l
    (NefDeRhamAt.nefAt_of_pull _ P.X V'.X P.p V'.p P.ar.isProjOver V'.ar.isProjOver b hb hbs _ l
      fun Z i _ _ _ hd => h₈ Z i (ZMod l) hd) Z i hd

end Covers

open Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4
open scoped ENNReal Classical

theorem nefAt_of_weights (hP : Hypotheses2) {D : D7} {O : Setup D} (hO : O.Core) {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y}
    (h : O.Reads A T H) {B : ℝ} (hB : 2 ≤ B) {u : Wt O.Y} {s : ℚ} (hu : IsRat O.Y u) (hs : 0 < s)
    (hdom : WeightThresholdDefs.Dominant O.Y (A.sh u s)) (c : O.s.Comp) (q : ℕ) [Fact q.Prime]
    (hw : ∀ (V : Cover (O.var c)) (L : DV.Rt D.what₂.Tau O.N → HermLB V.p),
      (∀ x, Norms V (L x) (fun z => genAt (O.root0 c (FlagAr.setB O.Y B) x).D z)
        (fun σ y => lnAdl (O.root0 c (FlagAr.setB O.Y B) x) σ y) fun v e y => (O.root0 c (FlagAr.setB O.Y B) x).lg v e y) →
      ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb L fun x => -n x.1 x.2) q)
    {M : TrueGeo.Model (O.var c)} {L : HermLB M.p} {k : ℕ+} {cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ}
    (hI : (O.Mb B u s c).Induced M L k cf) (Z : Scheme.{0}) (i : Z ⟶ M.X) [IsClosedImmersion i] [IsIntegral Z]
    [Algebra (ZMod q) Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) : 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1 := by
  have hab : (O.met.ab c).NefFib := by
    obtain ⟨x, P, hc⟩ := hO
    rw [hc.ab_eq]
    exact P.nefFib_ab c
  obtain ⟨m, b, hm, hb, hD, -, hfin⟩ := hO.mbIs B hB u s hu hs (A.sh u s)
    (by rw [← h.aux.dir]; rfl) hdom c
  let W := h.mdl (FlagAr.setB O.Y B) c
  refine nefAt_of_cover hI W.V q (fun V pl => ?_) Z i hd
  obtain ⟨amp, hamp⟩ := pl _ _ _ _ (norms_of_induces W.amp_spec)
  choose R hR using fun x => pl _ _ _ _ (norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c W _ subset_rfl x))
  replace hR := fun x => (hR x).congr (f' := fun z => genAt (O.root0 c (FlagAr.setB O.Y B) x).D z)
    (a' := fun σ y => lnAdl (O.root0 c (FlagAr.setB O.Y B) x) σ y)
    (l' := fun v e y => (O.root0 c (FlagAr.setB O.Y B) x).lg v e y) (fun _ => pow_one _) (fun _ _ => by simp)
    fun _ _ _ => by simp
  have hmn : (0 : ℝ) < (m : ℝ) * ((O.Mb B u s c).n : ℕ) := mul_pos (Nat.cast_pos.2 hm) (Nat.cast_pos.2 (O.Mb B u s c).n.2)
  have hb0 : 0 ≤ b none := by
    have h₁ : (m : ℝ) * ((O.Mb B u s c).n : ℕ) * (s : ℝ) = b none * ((O.met.ab c).n : ℕ) := hb none
    have h₂ : (0 : ℝ) < b none * ((O.met.ab c).n : ℕ) := h₁ ▸ mul_pos hmn (by exact_mod_cast hs)
    have h₃ : (0 : ℝ) < b none := by
      by_contra hh
      push Not at hh
      nlinarith [(Nat.cast_nonneg ((O.met.ab c).n : ℕ) : (0 : ℝ) ≤ _)]
    exact_mod_cast h₃.le
  have hbx (x : DV.Rt D.what₂.Tau O.N) : (m : ℝ) * ((O.Mb B u s c).n : ℕ) * -A.sh u s x.1 x.2 = b (some x) :=
    (hb (some x)).trans (by
      change _ * (((1 : ℕ+) : ℕ) : ℝ) = _
      simp)
  have hn := hw V R hR (fun τ j => -b (some (τ, j))) fun τ j j' hj => by
    have h₁ := hbx (τ, j)
    have h₂ := hbx (τ, j')
    have h₃ := mul_le_mul_of_nonneg_left (hdom τ j j' hj) hmn.le
    have : ((-b (some (τ, j')) : ℤ) : ℝ) ≤ (-b (some (τ, j)) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  simp only [neg_neg] at hn
  have hna := (nefFib_iff amp).1 (GlobalTheory.T.nef_fibre_of_norms_power hP _ _ _ hab V amp W.k W.k_pos hamp) q Fact.out
  have hN := norms_tens _ _ V _ _ _ _ _ _ _ _ (norms_pow _ _ V _ _ _ _ (b none).toNat hamp)
    (norms_pow _ _ V _ _ _ _ W.k (norms_comb hR fun x => b (some x)))
  have hc : (((b none).toNat : ℕ) : ℝ) = b none := by exact_mod_cast Int.toNat_of_nonneg hb0
  obtain ⟨a', ha'⟩ := norms_of_comb (K := W.k) hD hfin (hN.congr (fun x => by
    rw [Fintype.prod_option, mul_pow, ← pow_mul, mul_comm W.k, pow_mul]
    refine congrArg₂ (· * ·) (congrArg (· ^ W.k) ?_) rfl
    rw [← zpow_natCast, Int.toNat_of_nonneg hb0]
    rfl) (fun _ _ => rfl) fun v e y => by
    rw [Fintype.sum_option, hc]
    simp only [Option.elim]
    ring)
  exact ⟨_, W.k * m, a', Nat.mul_pos W.k_pos hm, ha',
    nefOver_tens V.ar.isProjOver (nefOver_pow V.ar.isProjOver hna _) (nefOver_pow V.ar.isProjOver hn _)⟩

end GlobalTheory.NefHodgeTateAt
end


section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.GeoSwap

open HermLB

section Shift

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem isometric_pull_shift (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ)
    (π : Y ⟶ X) (hπ : π ≫ p = q) : ((L.shift t ht).pull π hπ).Isometric ((L.pull π hπ).shift t ht) :=
  isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t σ) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t σ) π hπ a y).symm

theorem isometric_shift_of_isometric {L M : HermLB p} (h : L.Isometric M) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) : (L.shift t ht).Isometric (M.shift t ht) := by
  obtain ⟨w, hw, h⟩ := h
  refine ⟨w, hw, fun σ a b y ha hb => ?_⟩
  have e := h σ a b y ha hb
  exact (congrArg (· + 2 * t σ) e).trans (add_right_comm _ _ _)

theorem isometric_tens_shift_left (L M : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) :
    ((L.shift t ht).tens M).Isometric ((L.tens M).shift t ht) :=
  isometric_of_eqOn fun σ a y _ => by
    show ((L.φ σ).φ a.1 y + (M.φ σ).φ a.2 y) + 2 * t σ = ((L.φ σ).φ a.1 y + 2 * t σ) + (M.φ σ).φ a.2 y
    ring

variable (p) in

def constB (t : ℝ) : HermLB p := (triv p).shift (fun _ => t) fun _ => rfl

theorem icls_shift_const (L : HermLB p) (t : ℝ) :
    (L.shift (fun _ => t) fun _ => rfl).icls = L.icls + (constB p t).icls := by
  rw [add_comm, constB, ← icls_tens, icls_eq_iff]
  exact (isometric_shift_of_isometric (isometric_triv_tens L).symm _ _).trans
    (isometric_tens_shift_left _ _ _ _).symm

theorem icls_constB_add (s t : ℝ) : (constB p (s + t)).icls = (constB p s).icls + (constB p t).icls := by
  rw [← icls_shift_const, icls_eq_iff]
  exact isometric_of_eqOn fun σ a y _ => by
    show ((0 : ℝ) + 2 * s) + 2 * t = (0 : ℝ) + 2 * (s + t)
    ring

variable (p) in

def constHom : ℝ →+ IsomClass p := AddMonoidHom.mk' (fun t => (constB p t).icls) icls_constB_add

theorem gdeg_shift_const (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) :
    gdeg (L.shift t ht) D = gdeg L D := by
  simp only [gdeg, chInt, HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

theorem isometric_comb_three_shift (S Q A A' : HermLB p)
    (hA : A'.Isometric (A.shift (fun _ => 1) fun _ => rfl)) (m : Fin 3 → ℤ) (c : ℝ) (hc : ((m 2 : ℤ) : ℝ) = c) :
    (comb ![S, Q, A'] m).Isometric ((comb ![S, Q, A] m).shift (fun _ => c) fun _ => rfl) := by
  subst hc
  refine icls_eq_iff.1 ?_
  rw [icls_shift_const, icls_comb, icls_comb, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [icls_eq_iff.2 hA, icls_shift_const]
  have e : (constB p ((m 2 : ℤ) : ℝ)).icls = m 2 • (constB p 1).icls := by
    have := map_zsmul (constHom p) (m 2) 1
    simpa [constHom] using this
  rw [e, smul_add]
  abel

end Shift

theorem rename_lin_swap {κ : Type} [Fintype κ] [DecidableEq κ] (x y : κ) (c : κ → ℝ) :
    rename (Equiv.swap x y) (lin c) = lin fun z => c (Equiv.swap x y z) := by
  simp only [lin, map_sum, map_mul, rename_C, rename_X]
  exact Fintype.sum_equiv (Equiv.swap x y) _ _ fun z => by simp [Equiv.swap_apply_self]

theorem cast_triple (u v : ℤ) : (fun j => (((![u, v, 1] : Fin 3 → ℤ) j : ℤ) : ℝ)) = ![(u : ℝ), v, 1] := by
  funext j
  fin_cases j <;> simp

end GlobalTheory.CovTest.GeoSwap

end
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set : ∀ (F : Type) [Field F] [Infinite F] (X : Scheme.{0}) (p : X ⟶ Sp F), IsProjOver p → ∀ (B : LB X), B.IsLB → ∀ S : Set X, S.Finite → ∃ (A : LB X) (_ : A.IsLB) (a : A.Sec), (∃ (n : ℕ) (u : Fin n → A.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ (∃ (n : ℕ) (u : Fin n → (CechPic.tens B A).Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ ∀ z ∈ S, z ∈ nonzeroLocus a := by
  first | exact @GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero | exact GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero | (intros; apply GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.NefTens

theorem isNef_tens : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.IsNef D → M.IsNef D → (L.tens M).IsNef D := by
  intro HC k _ X _ p D hX L M NL NM
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  refine ⟨NL.semiPos.tens NM.semiPos, ?_, fun Z i _ _ _ hc hd => ?_⟩
  · intro Z i _ _ κ _ _ _ hd
    rw [NefHodgeTateAt.topSelf_of_cls_eq_add hp (L.tens M).isLB L.isLB M.isLB (cls_tens L.isLB M.isLB _) Z i κ hd]
    exact add_nonneg (NL.vertical Z i κ hd) (NM.vertical Z i κ hd)
  · obtain ⟨h, H⟩ := hex L
    obtain ⟨h', H'⟩ := hex M
    obtain ⟨h'', H''⟩ := hex (L.tens M)
    obtain ⟨r, hr⟩ := exists_isRatSec ((L.tens M).restr i).isLB
    obtain ⟨r₁, hr₁, h1⟩ := NL.horizontal Z i hc hd
    obtain ⟨r₂, hr₂, h2⟩ := NM.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H''.point Z i hc hd r hr,
      PtHtComb.height_tens hX H H' H'' (HtSelfInter.isAlgPt_genericPoint i hc hd),
      H.point Z i hc hd r₁ hr₁, H'.point Z i hc hd r₂ hr₂]
    exact add_nonneg h1 h2

example : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ L M : HermLB p, L.IsNef D → M.IsNef D → (L.tens M).IsNef D := isNef_tens

end GlobalTheory.NefTens
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.NefFibTens

theorem nefFib_pow_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → NefFib A → NefFib ((L.pow n).tens A) := by
  intro k _ X _ p D hX L A n hL hA Z i _ _ κ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  rw [NefHodgeTateAt.topSelf_of_cls_eq_add hp ((L.pow n).tens A).isLB (L.pow n).isLB A.isLB
    (cls_tens (L.pow n).isLB A.isLB _) Z i κ hd, NefHodgeTateAt.topSelf_pow hp L n Z i κ hd]
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)) (hA Z i κ hd)

end GlobalTheory.NefFibTens
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

theorem isNoetherian_of_locallyNoetherian_projOverField {F : Type} [Field F] {X : Scheme.{0}} [IsLocallyNoetherian X] {p : X ⟶ Sp F}
    (hproj : IsProjOver p) : AlgebraicGeometry.IsNoetherian X := by
  obtain ⟨n, i, hi, hpi⟩ := hproj
  have := isProper_str F n
  have : IsProper p := hpi ▸ inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact {}

theorem infinite_of_ringHom_complex {F : Type} [Field F] (σ : F →+* ℂ) : Infinite F := by
  haveI : CharZero F := σ.charZero
  exact Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective

theorem reciprocity_of_generated_right (hP : GlobalTheory.Published.Principalisation) (F : Type) [Field F] (X : Scheme.{0})
    [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ) (hproj : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t)
    (hcod : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t)
    (hN : ∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) :
    side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) =
      side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  haveI := isNoetherian_of_locallyNoetherian_projOverField hproj
  haveI := infinite_of_ringHom_complex σ
  let S : Set X := {genericPoint X} ∪ {z | Order.coheight z = 1 ∧ z ∉ nonzeroLocus t}
  have hS : S.Finite := (Set.finite_singleton _).union (GlobalTheory.T.finite_coheight_one_notMem_of_genericPoint_mem X (nonzeroLocus t) ht)
  obtain ⟨A, hA, a, hAgen, hMAgen, haS⟩ := GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set F X p hproj M.B M.φ.isLB S hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ A hA hAgen
  let A' : MLine p σ := ⟨A, φ, hφ⟩
  have ha : genericPoint X ∈ nonzeroLocus a := haS _ (Or.inl rfl)
  have haz : ∀ z : X, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ nonzeroLocus a :=
    fun z hz hzt => haS z (Or.inr ⟨hz, hzt⟩)
  obtain ⟨s₁, h₁, hloc, hadd⟩ := GlobalTheory.T.reciprocityDefect_add_bundleSection hP F X p σ e hproj hdim L M A' N s hs a ha t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · exact Or.inl ⟨(hcod z hz).resolve_right hzt, haz z hz hzt⟩)
  have h0A := GlobalTheory.T.reciprocity_sections_generatedBundles hP F X p σ e hproj hdim L A' N a ha t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · exact Or.inl (haz z hz hzt)) hAgen hN
  have h0MA := GlobalTheory.T.reciprocity_sections_generatedBundles hP F X p σ e hproj hdim L (M.tens A') N s₁ h₁ t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · left
      rw [hloc]
      exact ⟨(hcod z hz).resolve_right hzt, haz z hz hzt⟩) hMAgen hN
  linarith

theorem reciprocity_of_noCommonDivisor : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod
  haveI := isNoetherian_of_locallyNoetherian_projOverField hproj
  haveI := infinite_of_ringHom_complex σ
  let S : Set X := {genericPoint X} ∪ {z | Order.coheight z = 1 ∧ z ∉ nonzeroLocus s}
  have hS : S.Finite := (Set.finite_singleton _).union (GlobalTheory.T.finite_coheight_one_notMem_of_genericPoint_mem X (nonzeroLocus s) hs)
  obtain ⟨A, hA, a, hAgen, hNAgen, haS⟩ := GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set F X p hproj N.B N.φ.isLB S hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ A hA hAgen
  let A' : MLine p σ := ⟨A, φ, hφ⟩
  have ha : genericPoint X ∈ nonzeroLocus a := haS _ (Or.inl rfl)
  have haz : ∀ z : X, Order.coheight z = 1 → z ∉ nonzeroLocus s → z ∈ nonzeroLocus a :=
    fun z hz hzs => haS z (Or.inr ⟨hz, hzs⟩)
  obtain ⟨t₁, h₁, hloc, hadd⟩ := GlobalTheory.T.reciprocityDefect_add_bundleSection hP F X p σ e hproj hdim L N A' M t ht a ha s hs (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inr hzs
    · exact Or.inl ⟨(hcod z hz).resolve_left hzs, haz z hz hzs⟩)
  have h0A := reciprocity_of_generated_right hP F X p σ e hproj hdim L M A' s hs a ha (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inl hzs
    · exact Or.inr (haz z hz hzs)) hAgen
  have h0NA := reciprocity_of_generated_right hP F X p σ e hproj hdim L M (N.tens A') s hs t₁ h₁ (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inl hzs
    · right
      rw [hloc]
      exact ⟨(hcod z hz).resolve_left hzs, haz z hz hzs⟩) hNAgen
  linarith

end GlobalTheory.Mix
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundle_isNef_tens : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.IsNef D → M.IsNef D → (L.tens M).IsNef D := by
  first | exact @GlobalTheory.NefTens.isNef_tens | exact GlobalTheory.NefTens.isNef_tens | (intros; apply GlobalTheory.NefTens.isNef_tens <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lowerBound_along_div : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c n : ℕ) (α : ℝ), 0 < n → NefFib P.L → P.L.SemiPos D → IsAmpleLB P.A.B → P.A.SemiPos D → ((P.L.pow n).tens P.A).IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (α / (D + 1).factorial / (n : ℝ) ^ (D + 1) - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M ((M / n : ℕ) - c) 1 := by
  intro _ hHS k _ X _ p D hX P c n α hn hL hLs hA hAs hα ε hε
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  have hLn : NefFib (P.L.pow n) := fun Z i _ _ κ _ _ _ hd => by
    rw [NefHodgeTateAt.topSelf_pow hp P.L n Z i κ hd]
    exact mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)
  have hAmp : IsAmpleLB ((P.L.pow n).tens P.A).B := GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX _ _ hLn hA
  have hSP : ((P.L.pow n).tens P.A).SemiPos D := (hLs.pow n).tens hAs
  have hRep : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := Pair.rep_pow k X p P 1 0 P.L n (Pair.rep_base k X p P).1
    have h2 := Pair.rep_tens k X p P _ _ 0 1 _ _ h1 (Pair.rep_base k X p P).2.1
    simpa using h2
  refine lowerBound_along_residues (D + 1) n (fun M => P.lc M ((M / n : ℕ) - c) 1) (α / (D + 1).factorial) hn
    (fun r hr ε' hε' => ?_) ε hε
  filter_upwards [GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos hHS k X p D hX P n 1 r (-(c : ℤ)) _ α hRep hAmp hSP hα ε' hε'] with q hq
  have e : (n * q + r) / n = q := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr, zero_add]
  simp only [e]
  convert hq using 2 <;> push_cast <;> ring

end GlobalTheory.HSNef
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithReciprocity_noCommonDivisor_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.Mix.reciprocity_of_noCommonDivisor | exact GlobalTheory.Mix.reciprocity_of_noCommonDivisor | (intros; apply GlobalTheory.Mix.reciprocity_of_noCommonDivisor <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.KleimanStep

theorem selfInter_nonneg : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D →
    (∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h → ∀ z, z ≠ genericPoint X → 0 ≤ h z) →
    ∀ (C : HermLB p) (c : ℝ), C.IsNef D → C.IsSelfInter c → 0 ≤ c := by
  intro hC hHS k _ X _ p D hX hD hlow C c hnef hc
  obtain ⟨A, hA, hAn, -⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hC k X p D hX
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.SelfInterGrowth.main hC k X p D hX C A c hc
  refine ge_of_tendsto' hlim fun n => div_nonneg ?_ (by positivity)
  have hpow := GlobalTheory.NefPow.isNef_pow hC k X p D hX C n hnef
  have htens := GlobalTheory.T.hermLineBundle_isNef_tens hC k X p D hX _ _ hpow hAn
  have hamp := GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX _ A hpow.vertical hA
  obtain ⟨h, hh, he⟩ := hα n
  rw [← he]
  exact GlobalTheory.T.height_genericPoint_nonneg_ample_semiPositive hC hHS k X p D hX hD _ h hamp htens.semiPos hh (hlow _ h htens hh)

end GlobalTheory.KleimanStep
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_lowerBound_nef_plus_ample : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c n : ℕ) (α : ℝ), 0 < n → NefFib P.L → P.L.SemiPos D → IsAmpleLB P.A.B → P.A.SemiPos D → ((P.L.pow n).tens P.A).IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (α / (D + 1).factorial / (n : ℝ) ^ (D + 1) - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M ((M / n : ℕ) - c) 1 := by
  first | exact @GlobalTheory.HSNef.lowerBound_along_div | exact GlobalTheory.HSNef.lowerBound_along_div | (intros; apply GlobalTheory.HSNef.lowerBound_along_div <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixRec

theorem injective_of_finite_int {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (σ : k →+* ℂ) : Function.Injective σ := by
  rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  intro a ha
  have : a ∈ RingHom.ker σ := ha
  rwa [hker, Ideal.mem_bot] at this

theorem exists_extension {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (K : Type) [Field K] [Algebra k K] [IsFractionRing k K] (σ : k →+* ℂ) :
    ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
  ⟨IsFractionRing.lift (A := k) (K := K) (injective_of_finite_int σ),
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := K) (injective_of_finite_int σ) x).symm⟩

theorem side_symm : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP k _ X _ _ p e h σ
  haveI := h.isDomain
  haveI := h.finite
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra k K), IsFractionRing k K :=
    ⟨FractionRing k, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨τ, hτ⟩ := exists_extension K σ
  subst hτ
  intro L M N s hs t ht hcod
  obtain ⟨G, j, q, hp⟩ : ∃ (G : Scheme.{0}) (j : G ⟶ X) (q : G ⟶ Sp K),
      IsPullback j q p (spMap (algebraMap k K)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, hcoh, -⟩ :=
    GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) h
  obtain ⟨s', hs', hsl, hsm, hslog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk M s hs hgen
  obtain ⟨t', ht', htl, htm, htlog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk N t ht hgen
  have hcod' : ∀ z : G, Order.coheight z = 1 → z ∈ nonzeroLocus s' ∨ z ∈ nonzeroLocus t' := by
    intro z hz
    rw [hsl, htl]
    exact hcod (j z) ((hcoh z).trans hz)
  have hrec := GlobalTheory.T.arithReciprocity_noCommonDivisor_projective hP K G q τ e hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ)
    (N.bc hp.w τ) s' hs' t' ht' hcod'
  have e1 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ hsm N L (M.logSec s) (N.logSec t)
  have e2 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ htm M L (N.logSec t) (M.logSec s)
  have hsf : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hslog
  have htf : (N.bc hp.w τ).logSec t' = fun y => N.logSec t (bcPt hp.w τ y) := funext htlog
  rw [hsf, htf] at hrec
  exact e1.symm.trans (hrec.trans e2)

end GlobalTheory.MixRec
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithKleiman_selfIntersection_nonneg : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → (∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h → ∀ z, z ≠ genericPoint X → 0 ≤ h z) → ∀ (C : HermLB p) (c : ℝ), C.IsNef D → C.IsSelfInter c → 0 ≤ c := by
  first | exact @GlobalTheory.KleimanStep.selfInter_nonneg | exact GlobalTheory.KleimanStep.selfInter_nonneg | (intros; apply GlobalTheory.KleimanStep.selfInter_nonneg <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSLowerTwist

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → NefFib P.L → P.L.SemiPos D → ∀ a : ℝ, P.L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (a / (D + 1).factorial - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M (-c) 1 := by
  intro hC hHS k _ X _ p D hX P b s t hG c hgen hreg hnef hsemi a ha ε hε
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.SelfInterGrowth.main hC k X p D hX P.L P.A a ha
  have hε3 : 0 < ε / 3 := by positivity
  have h1 := GlobalTheory.T.smallSectionCount_log_twist_continuity_above k X p D hX P b s t hG c hgen hreg (ε / 3) hε3
  have h2 : ∀ᶠ n : ℕ in atTop, a / ((D + 1).factorial : ℝ) - ε / 3 <
      α n / (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) :=
    (hlim.div_const ((D + 1).factorial : ℝ)).eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, ⟨hn1, hn2⟩, hn0⟩ := ((h1.and h2).and (eventually_gt_atTop 0)).exists
  have h3 := GlobalTheory.T.arithHilbertSamuel_lowerBound_nef_plus_ample hC hHS k X p D hX P c n (α n) hn0 hnef hsemi hG.ample hG.nef.semiPos (hα n) (ε / 3) hε3
  filter_upwards [hn1, h3] with M hM1 hM3
  have hM : (0 : ℝ) ≤ (M : ℝ) ^ (D + 1) := by positivity
  rw [div_right_comm] at hM3
  have h4 := mul_le_mul_of_nonneg_right hn2.le hM
  nlinarith

end GlobalTheory.HSLowerTwist
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_reciprocity_at_complex_embedding : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.MixRec.side_symm | exact GlobalTheory.MixRec.side_symm | (intros; apply GlobalTheory.MixRec.side_symm <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.KleimanNef

theorem htNef_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D := by
  intro hA hAmp hSP
  suffices H : ∀ D : ℕ, ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
      IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D by
    intro k _ X _ p D hX C hC
    exact H D k X p hX C hC
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro k _ X _ p hX C hC
  have hng : ∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h →
      ∀ z, z ≠ genericPoint X → 0 ≤ h z := by
    intro C h hC hh z hz
    by_cases hcz : CharZero (X.residueField z)
    swap
    · exact GlobalTheory.T.arithHeight_nonneg_vertical_of_nefOnFibres k X p D hX C h (nefFib_of_isNef hC) hh z hcz
    obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    rcases hX.vertical_or_horizontal i with ⟨ℓ, hℓ, ⟨alg⟩⟩ | ⟨hc, e, he⟩
    · exfalso
      have hcz' : CharZero (Z.residueField (genericPoint Z)) :=
        (RingHom.charZero_iff (i.residueFieldMap (genericPoint Z)).hom.injective).1 hcz
      let f : ZMod ℓ →+* Z.residueField (genericPoint Z) :=
        (Z.evaluation ⊤ (genericPoint Z) trivial).hom.comp (algebraMap (ZMod ℓ) Γ(Z, ⊤))
      have h2 := congrArg f (ZMod.natCast_self ℓ)
      rw [map_natCast, map_zero] at h2
      exact hℓ.out.ne_zero (by exact_mod_cast h2)
    · have hZ : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc he
      have hamb := GlobalTheory.MixHt.isAmb_of_isArithVar hX
      obtain ⟨-, -, -, -, hcl, hgd⟩ := GlobalTheory.MixHt.hasDim_basic k X p hamb
      have hd : GlobalTheory.MixHt.HasDim (i (genericPoint Z)) (e + 1) := (hcl Z i _ _).2 ((hgd Z _).2 he)
      have hco := GlobalTheory.DimCoheight.coheight_add_eq k X p hamb (D + 1) hX.dim_eq _ _ hd
      have hne : Order.coheight (i (genericPoint Z)) ≠ 0 := by
        intro h0
        rw [Order.coheight_eq_zero] at h0
        apply hz
        have h1 : i (genericPoint Z) ≤ genericPoint X := genericPoint_specializes _
        exact (Specializes.antisymm (h0 h1) (genericPoint_specializes _)).eq
      have heD : e < D := by
        by_contra hle
        push_neg at hle
        obtain ⟨c, hc'⟩ : ∃ c : ℕ, Order.coheight (i (genericPoint Z)) = c := by
          refine ⟨(Order.coheight (i (genericPoint Z))).toNat, (ENat.coe_toNat fun ht => ?_).symm⟩
          rw [ht, top_add] at hco
          exact ENat.top_ne_coe _ hco
        rw [hc'] at hco hne
        have : c + (e + 1) = D + 1 := by exact_mod_cast hco
        have : c ≠ 0 := by exact_mod_cast hne
        omega
      have hnef : (C.pull i rfl).IsNef e := GlobalTheory.T.hermitianLineBundle_isNef_pullback hA hSP k X Z p (i ≫ p) D e hX hZ i rfl C hC
      exact (ih e heD k Z (i ≫ p) hZ _ hnef).2 _ (hh.restrict hX i rfl) (genericPoint Z)
  refine ⟨hC.semiPos, fun h hh x => ?_⟩
  by_cases hx : x = genericPoint X
  · subst hx
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have := ((hh.isNef_iff hX).1 hC).2 X (𝟙 X) (by simpa using hX.dim_eq)
      simpa using this
    · exact GlobalTheory.T.arithKleiman_selfIntersection_nonneg hA hAmp k X p D hX hD hng C _ hC ⟨h, hh, rfl⟩
  · exact hng C h hC hh x hx

end GlobalTheory.KleimanNef
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallSections_lowerBound_ample_minus_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → NefFib P.L → P.L.SemiPos D → ∀ a : ℝ, P.L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (a / (D + 1).factorial - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M (-c) 1 := by
  first | exact @GlobalTheory.HSLowerTwist.main | exact GlobalTheory.HSLowerTwist.main | (intros; apply GlobalTheory.HSLowerTwist.main <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem archRecip_of_principalisation (hP : GlobalTheory.Published.Principalisation) : ArchRecip := by
  intro k _ Y _ _ q e hq M N L s t hs ht hcov
  have : IsNoetherian Y := hq.isNoetherian
  have : Finite (k →+* ℂ) := hq.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hcons (A : HermLB q) (σ : k →+* ℂ) :
      (fun i => MLine.ofHerm ((Fin.cons A L : Fin (e + 1) → HermLB q) i) σ) =
        Fin.cons (MLine.ofHerm A σ) (fun i => MLine.ofHerm (L i) σ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, ((divOfSec A.isLB a ha).mult z : ℝ) *
          cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm B σ).logSec b) z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [GlobalTheory.T.restrictedArchIntegral_eq_sum_closureIntegrals hP k Y q e hq L B b z hz ((hab z hz).resolve_left hza), finsum_eq_sum_of_fintype,
        Finset.mul_sum]
  have fin (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
    D.finite_support_mult.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h
      simp [h] at hz
  have hside (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) :
      mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) A (isRatSec_ratOfSec a ha) +
          ∑ᶠ z, ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, side (MLine.ofHerm B σ) (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm A σ).logSec a)
          ((MLine.ofHerm B σ).logSec b) (divOfSec (MLine.ofHerm A σ).φ.isLB a ha) := by
    rw [GlobalTheory.T.mixedArchLogNormIntegral_eq_sum_embeddings hP k Y q (e + 1) hq, finsum_eq_sum_of_fintype, finsum_congr (key A B a b ha hab),
      finsum_sum_comm _ _ (fun σ _ => fin _ _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [side, ← hcons]
    rfl
  rw [hside M N s t hs hcov, hside N M t s ht fun z hz => (hcov z hz).symm]
  exact Finset.sum_congr rfl fun σ _ => GlobalTheory.T.arith_variety_reciprocity_at_complex_embedding hP k Y q e hq σ (fun i => MLine.ofHerm (L i) σ)
    (MLine.ofHerm M σ) (MLine.ofHerm N σ) s hs t ht hcov

end GlobalTheory.MixHt
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithKleiman_heightNef_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D := by
  first | exact @GlobalTheory.KleimanNef.htNef_of_isNef | exact GlobalTheory.KleimanNef.htNef_of_isNef | (intros; apply GlobalTheory.KleimanNef.htNef_of_isNef <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LowerNef

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), NefFib L → L.SemiPos D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (a / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
  intro hAr hHS k _ X _ p D hX L N a hNef hSP hSI ε hε
  obtain ⟨P, b, s, t, c, hPL, hG, hGen, hReg, hLe⟩ := GlobalTheory.T.exists_goodHermPair_adapted_twist hAr hHS k X p D hX L N
  subst hPL
  have hlow := GlobalTheory.T.smallSections_lowerBound_ample_minus_twist hAr hHS k X p D hX P b s t hG c hGen hReg hNef hSP a hSI ε hε
  filter_upwards [hlow] with m hm
  obtain ⟨h1, h2, -⟩ := Pair.rep_base k X p P
  have hRep : P.Rep (m : ℤ) (-(c : ℤ)) ((P.L.pow m).tens ((P.A.pow c).dual)) := by
    have := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ m h1)
      (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ c h2))
    simpa using this
  have hE := SmallBall.encard_eq_Bl P hRep ((P.L.pow m).tens ((P.A.pow c).dual)).smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have hle := GlobalTheory.T.encard_smallSections_le_of_hermLBLeBySmallSection k X p _ _ ((GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift k X p _ _ (P.L.pow m)).1 hLe)
  have hfin := GlobalTheory.T.finite_smallSec_hermitian_line_bundle_arith_variety k X p D hX ((P.L.pow m).tens N)
  have hBle : (P.Bl m (-c) 1).encard ≤ ((P.L.pow m).tens N).smallSec.encard := hE ▸ hle
  have hBfin : (P.Bl m (-c) 1).Finite :=
    Set.finite_of_encard_le_coe (hBle.trans_eq hfin.cast_ncard_eq.symm)
  have hone : (1 : ℕ∞) ≤ (P.Bl m (-c) 1).encard :=
    hE ▸ Set.one_le_encard_iff_nonempty.2 ⟨_, ((P.L.pow m).tens ((P.A.pow c).dual)).zero_mem_smallSec⟩
  have hc1 : 1 ≤ (P.Bl m (-c) 1).ncard := by
    have := hBfin.cast_ncard_eq ▸ hone
    exact_mod_cast this
  have hc2 : (P.Bl m (-c) 1).ncard ≤ ((P.L.pow m).tens N).smallSec.ncard := by
    have := hBfin.cast_ncard_eq ▸ hfin.cast_ncard_eq ▸ hBle
    exact_mod_cast this
  refine hm.trans ?_
  unfold Pair.lc
  exact Real.log_le_log (by exact_mod_cast hc1) (by exact_mod_cast hc2)

end GlobalTheory.HSNef.LowerNef
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archLogNormReciprocity_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchRecip := by
  first | exact @GlobalTheory.MixHt.archRecip_of_principalisation | exact GlobalTheory.MixHt.archRecip_of_principalisation | (intros; apply GlobalTheory.MixHt.archRecip_of_principalisation <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNefMono

theorem selfInter_mono_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), A.IsNef D → B.IsNef D → Le B A → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  intro hc hA hS k _ X _ p D hv A B α β hAn hBn hle hα hβ
  refine GlobalTheory.T.selfIntersection_mono_of_height_nef hc k X p D hv A B α β hle (fun x y => ?_) hα hβ
  exact GlobalTheory.T.arithKleiman_heightNef_of_isNef hc hA hS k X p D hv _
    (GlobalTheory.T.hermLineBundle_isNef_tens hc k X p D hv _ _ (GlobalTheory.NefPow.isNef_pow hc k X p D hv A x hAn)
      (GlobalTheory.NefPow.isNef_pow hc k X p D hv B y hBn))

end GlobalTheory.HSNefMono
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_lowerBound_semiPos_nefOnFibres : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), NefFib L → L.SemiPos D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (a / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
  first | exact @GlobalTheory.HSNef.LowerNef.main | exact GlobalTheory.HSNef.LowerNef.main | (intros; apply GlobalTheory.HSNef.LowerNef.main <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem GlobalTheory.MixHt.arCalc_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArCalc := fun h =>
  (GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic (GlobalTheory.T.archLogNormChernIntegrable_of_principalisation h) (GlobalTheory.T.archLogNormReciprocity_of_principalisation h)).1
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithSelfIntersection_mono_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), A.IsNef D → B.IsNef D → Le B A → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  first | exact @GlobalTheory.HSNefMono.selfInter_mono_of_isNef | exact GlobalTheory.HSNefMono.selfInter_mono_of_isNef | (intros; apply GlobalTheory.HSNefMono.selfInter_mono_of_isNef <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.ChangeSing

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
  {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem up_pull_isometric (L : HermLB p) (u : SmFn p) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q) :
    (up (L.pull ρ hρ) (u.pull ρ hρ)).Isometric ((up L u).pull ρ hρ) := by
  refine HermLB.isometric_of_eqOn ?_
  intro σ a y _
  erw [Weight.pull_φ]
  exact (congrArg (· + u.u σ (Points.PtsOver.map ρ hρ (spMap σ) y)) (Weight.pull_φ (L.φ σ) ρ hρ a y)).symm

theorem ballIn_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (Λ : AddSubgroup X.functionField) (a b : ℤ)
    (hn : ∀ f ∈ Λ, ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (R : ℝ) : ballIn Q (Λ.map e.toAddMonoidHom) a b R = e '' ballIn P Λ a b R := by
  ext g
  constructor
  · rintro ⟨⟨f, hf, rfl⟩, hR⟩
    refine ⟨f, ⟨hf, fun σ x => ?_⟩, rfl⟩
    obtain ⟨y, rfl⟩ := hs σ x
    rw [← hn f hf σ y]
    exact hR σ y
  · rintro ⟨f, ⟨hf, hR⟩, rfl⟩
    refine ⟨⟨f, hf, rfl⟩, fun σ y => ?_⟩
    rw [hn f hf σ y]
    exact hR σ _

theorem ncard_ballIn_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (Λ : AddSubgroup X.functionField) (a b : ℤ)
    (hn : ∀ f ∈ Λ, ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (R : ℝ) : (ballIn Q (Λ.map e.toAddMonoidHom) a b R).ncard = (ballIn P Λ a b R).ncard := by
  rw [ballIn_map P Q e ρ hρ hs Λ a b hn R]
  exact Set.ncard_image_of_injective _ e.injective

theorem goodFam_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (he : ∀ (a b : ℤ), ∀ f ∈ P.H a b, e f ∈ Q.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts q σ),
      Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (D : ℕ) (g : ℝ) (Λ : ℕ → AddSubgroup X.functionField) (h : GoodFam P D g Λ) :
    GoodFam Q D g (fun m => (Λ m).map e.toAddMonoidHom) where
  le m := by
    rintro _ ⟨f, hf, rfl⟩
    exact (he m 1 f (h.le m hf)).1
  fg m := by
    classical
    obtain ⟨s, hs'⟩ := h.fg m
    refine ⟨s.image e, ?_⟩
    rw [Finset.coe_image, ← hs', AddMonoidHom.map_closure]
    rfl
  small := by
    obtain ⟨C, hC, hCm⟩ := h.small
    refine ⟨C, hC, fun m hm => ?_⟩
    have hn : ∀ f ∈ Λ m, ∀ (σ : k →+* ℂ) (y : CxPts q σ),
        Q.nu m 1 σ y (e f) = P.nu m 1 σ (Points.PtsOver.map ρ hρ (spMap σ) y) f :=
      fun f hf => (he m 1 f (h.le m hf)).2
    rw [ballIn_map P Q e ρ hρ hs (Λ m) m 1 hn]
    exact (AddSubgroup.map_mono (hCm m hm)).trans
      (AddMonoidHom.map_closure e.toAddMonoidHom (ballIn P (Λ m) m 1 (C ^ m))).le
  rank := by
    have e' : ∀ m, Module.finrank ℤ ((Λ m).map e.toAddMonoidHom) = Module.finrank ℤ (Λ m) := fun m =>
      ((AddSubgroup.equivMapOfInjective (Λ m) e.toAddMonoidHom e.injective).toIntLinearEquiv.finrank_eq).symm
    simp only [e']
    exact h.rank

end GlobalTheory.HSAmp.ChangeSing

namespace GlobalTheory.HSAmp.ChangeSing

theorem count_change_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → GoodFam P D (gdeg P.L D / D.factorial) (fun m => P.H m 1) → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  intro hPr k _ X _ p D hX P a hsp hsi hgf
  have hC : Published.ArCalc := MixHt.arCalc_of_principalisation hPr
  obtain ⟨Y, hY, ρ, hYa, hYs, hgen, hdeg⟩ := GenRes.exists_birational_genSmooth hPr k X p D hX
  obtain ⟨Q, e, hQL, -, he⟩ := T.exists_hermLineBundlePair_pullback_dominant k X p Y (ρ ≫ p) ρ rfl hgen P
  have hs : ∀ σ : k →+* ℂ, Function.Surjective
      (Points.PtsOver.map ρ rfl (spMap σ) : CxPts (ρ ≫ p) σ → CxPts p σ) :=
    T.dominant_projArith_surjective_complexPoints k X p D hX Y (ρ ≫ p) D hYa ρ rfl hgen
  have hne : ρ.residueDegree (genericPoint Y) ≠ 0 := by rw [hdeg]; exact one_ne_zero
  have hproj := hC.2.2.2.2.1 k X Y p (ρ ≫ p) D hX hYa ρ rfl hgen hne
  have hdeg' : ((ρ.residueDegree (genericPoint Y) : ℕ) : ℝ) = 1 := by rw [hdeg]; simp
  have hQsp : Q.L.SemiPos D := by
    rw [hQL]; exact T.semiPos_pullback_generically_birational k X p D hX Y (ρ ≫ p) hYa ρ rfl hgen hdeg P.L hsp
  have hQsi : Q.L.IsSelfInter a := by
    have h := hproj.1 P.L a hsi
    rw [hdeg', one_mul] at h
    rw [hQL]; exact h
  have hQg : gdeg Q.L D = gdeg P.L D := by
    rw [hQL, CovTest.gdegPull k X Y p (ρ ≫ p) D hX hYa ρ rfl hgen hne, hdeg', one_mul]
  have hgf' := goodFam_map P Q e ρ rfl hs he D _ _ hgf
  rw [← hQg] at hgf'
  obtain ⟨t₀, ht⟩ := T.tendsto_logSectionCount_change_of_metric hC k Y (ρ ≫ p) D hYa hYs Q a hQsp hQsi _ hgf'
  refine ⟨t₀, fun u B a' hB hu husp husi t ht' => ?_⟩
  have hiso : (up Q.L (u.pull ρ rfl)).Isometric ((up P.L u).pull ρ rfl) := by
    rw [hQL]; exact up_pull_isometric P.L u ρ rfl
  have h1 : (up Q.L (u.pull ρ rfl)).SemiPos D :=
    HermLB.Isometric.semiPos _ _ D hiso.symm (T.semiPos_pullback_generically_birational k X p D hX Y (ρ ≫ p) hYa ρ rfl hgen hdeg _ husp)
  have h2 : (up Q.L (u.pull ρ rfl)).IsSelfInter a' := by
    have h := hproj.1 (up P.L u) a' husi
    rw [hdeg', one_mul] at h
    exact hiso.symm.isSelfInter hYa h
  have h3 := ht (u.pull ρ rfl) B a' hB (fun σ y => hu σ _) h1 h2 t ht'
  have hnP : ∀ m : ℕ, ∀ f ∈ P.H (m : ℤ) 1, ∀ (σ : k →+* ℂ) (y : CxPts (ρ ≫ p) σ),
      Q.nu m 1 σ y (e f) = P.nu m 1 σ (Points.PtsOver.map ρ rfl (spMap σ) y) f :=
    fun m f hf => (he m 1 f hf).2
  have hnU : ∀ m : ℕ, ∀ f ∈ P.H (m : ℤ) 1, ∀ (σ : k →+* ℂ) (y : CxPts (ρ ≫ p) σ),
      (upperParabolic Q (u.pull ρ rfl)).nu m 1 σ y (e f) =
        (upperParabolic P u).nu m 1 σ (Points.PtsOver.map ρ rfl (spMap σ) y) f := by
    intro m f hf σ y
    rw [((T.raiseFirstWeight_sections_loci_values_norms k Y (ρ ≫ p) Q (u.pull ρ rfl) m 1).2.2 σ y (e f)).2,
      ((T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ _ f).2, hnP m f hf σ y]
    rfl
  refine h3.congr fun m => ?_
  rw [ncard_ballIn_map (upperParabolic P u) (upperParabolic Q (u.pull ρ rfl)) e ρ rfl hs _ _ _ (hnU m),
    ncard_ballIn_map P Q e ρ rfl hs _ _ _ (hnP m)]

end GlobalTheory.HSAmp.ChangeSing
end


section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SemiPullAll

theorem isometric_pull_pull {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R := L.refines_pull_pull f hf g hg hc
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem semiPull_of_principalisation : GlobalTheory.Published.Principalisation → SemiPull := by
  intro hP k _ X Y p q D E hp hq π hπ L hL
  have := hp.isIntegral
  have := hq.isIntegral
  obtain ⟨X', _, ρ, hρ, hsm, hgen, hdeg⟩ := GlobalTheory.GenRes.exists_birational_genSmooth hP k X p D hp
  obtain ⟨V, hV, het⟩ := GlobalTheory.T.exists_opens_etale_generically_finite_dominant k X X' p (ρ ≫ p) D hp hρ ρ rfl hgen (by rw [hdeg]; exact one_ne_zero)
  have h₁ : (L.pull ρ rfl).SemiPos D := GlobalTheory.T.semiPositive_pullback_generically_etale k X X' p (ρ ≫ p) D hp hρ ρ rfl V hV het L hL
  have hπp : IsArithVar (π ≫ p) E := by rw [hπ]; exact hq
  obtain ⟨Y', _, g, π', hcomm, hY', hggen, hgdeg⟩ := GlobalTheory.T.exists_arithmeticCover_over_modification k X X' Y p D E ρ π hp hρ hπp hgen
  have hY'q : IsArithVar (g ≫ q) E := by rw [← hπ]; exact hY'
  have e₁ : π' ≫ ρ ≫ p = g ≫ q := by rw [← Category.assoc, hcomm, Category.assoc, hπ]
  have e₂ : (g ≫ π) ≫ p = g ≫ q := by rw [Category.assoc, hπ]
  have h₂ : ((L.pull ρ rfl).pull π' e₁).SemiPos E :=
    GlobalTheory.T.semiPos_pull_of_genericallySmooth k X' Y' (ρ ≫ p) (g ≫ q) D E hsm π' e₁ (L.pull ρ rfl) h₁
  have iso : ((L.pull ρ rfl).pull π' e₁).Isometric ((L.pull π hπ).pull g rfl) :=
    (isometric_pull_pull L ρ rfl π' e₁ (g ≫ π) e₂ hcomm).trans
      (isometric_pull_pull L π hπ g rfl (g ≫ π) e₂ rfl).symm
  have h₃ : ((L.pull π hπ).pull g rfl).SemiPos E :=
    (GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric (GlobalTheory.MixHt.arCalc_of_principalisation hP) k Y' (g ≫ q) E hY'q _ _ iso).1 h₂
  obtain ⟨W, hW, hWet⟩ := GlobalTheory.T.exists_opens_etale_generically_finite_dominant k Y Y' q (g ≫ q) E hq hY'q g rfl hggen hgdeg
  exact GlobalTheory.T.semiPos_of_pullback_generically_etale k Y Y' q (g ≫ q) E hq hY'q g rfl W hW hWet (L.pull π hπ) h₃

end GlobalTheory.SemiPullAll
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem Total.comp {X : Scheme.{0}} [IsIntegral X] {J J' : Type} {f : J → X.functionField} (h : Total f)
    (ι : J' → J) : Total (f ∘ ι) :=
  ⟨fun j => h.1 (ι j), fun x j l => h.2 x (ι j) (ι l)⟩

theorem selfInter_nonneg_of_isFS (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) {k : Type} [CommRing k]
    {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {M : HermLB p} {J : Type} [Fintype J]
    {f : J → X.functionField} {w : J → ℝ} (hM : IsFS M f w) (hw : ∀ j, 0 ≤ w j) {μ : ℝ} (hμ : M.IsSelfInter μ) :
    0 ≤ μ := by
  have hnef := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M J f w hM hw
  have hht := (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX M hnef).2
  obtain ⟨h, hh, rfl⟩ := hμ
  exact hht h hh _

theorem levels_le_selfInter (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (x : Fin D → X.functionField) (Δ : ℝ)
    (hx : AlgebraicIndependent ℤ x) (hΔ : 0 < Δ) :
    ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ),
      LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) →
      M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ∑ j, (n j : ℝ) ≤ μ := by
  intro N
  induction N with
  | zero =>
    intro J _ e n M μ _ hn _ hM hμ
    have h0 : ∀ j, n j = 0 := fun j => Nat.le_zero.1 (hn j)
    simp only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
    exact selfInter_nonneg_of_isFS hC hA hS hX hM (fun c => by simp [h0]) hμ
  | succ N ih =>
    intro J _ e n M μ he hn ht hM hμ
    classical
    have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
    by_cases hJ : ∀ j, n j = 0
    · simp only [hJ, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
      exact selfInter_nonneg_of_isFS hC hA hS hX hM hw0 hμ
    push_neg at hJ
    obtain ⟨j₀, hj₀⟩ := hJ
    let J' := {j // 1 ≤ n j}
    let e' : J' → X.functionField := fun j => e j.1
    let n' : J' → ℕ := fun j => n j.1 - 1
    let ι : J' × Finset (Fin D) → J × Finset (Fin D) := fun c => (c.1.1, c.2)
    have hι : Function.Injective ι := by
      rintro ⟨⟨a, ha⟩, s⟩ ⟨⟨b, hb⟩, t⟩ h
      simp only [ι, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hbox : boxFam e' x = boxFam e x ∘ ι := rfl
    haveI : Nonempty (J' × Finset (Fin D)) := ⟨(⟨j₀, Nat.one_le_iff_ne_zero.2 hj₀⟩, ∅)⟩
    have ht' : Total (boxFam e' x) := hbox ▸ ht.comp ι
    obtain ⟨M', hM'⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k X p (J' × Finset (Fin D)) (boxFam e' x) (fun c => (n' c.1 : ℝ) * Δ) ht'
    obtain ⟨h', hh'⟩ := (hC.arExists k X p D hX).1 M'
    have hμ' : M'.IsSelfInter (h' (genericPoint X)) := ⟨h', hh', rfl⟩
    have he' : LinearIndependent ℤ e' := he.comp _ Subtype.val_injective
    have hn' : ∀ j, n' j ≤ N := fun j => by
      have := hn j.1
      simp only [n']
      omega
    have IH := ih J' e' n' M' _ he' hn' ht' hM' hμ'
    have hw0' : ∀ c : J' × Finset (Fin D), 0 ≤ (n' c.1 : ℝ) * Δ := fun c => by positivity
    have hstep : ∀ c : J' × Finset (Fin D), (n' c.1 : ℝ) * Δ + Δ ≤ (n (ι c).1 : ℝ) * Δ := fun c => by
      have h1 := c.1.2
      simp only [n', ι]
      rw [Nat.cast_sub h1]
      push_cast
      linarith
    have hle : Le (M'.shift (fun _ => Δ) fun _ => rfl) M :=
      GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family k X p M M' (J × Finset (Fin D)) (J' × Finset (Fin D)) (boxFam e x) (fun c => (n c.1 : ℝ) * Δ)
        (fun c => (n' c.1 : ℝ) * Δ) ι Δ hι hM (hbox ▸ hM') hstep
    have hnefM := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M _ _ _ hM hw0
    have hnefM' := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M' _ _ _ hM' hw0'
    have hnefS := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX M' Δ hΔ.le hnefM'
    have hsh := hC.arShift k X p D hX M' _ Δ hμ'
    have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hC hA hS k X p D hX M _ μ _ hnefM hnefS hle hμ hsh
    have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M' J' e' x (fun c => (n' c.1 : ℝ) * Δ) he' hx hw0' hM'
    have hsum : ∑ j, (n j : ℝ) = ∑ j : J', (n' j : ℝ) + Fintype.card J' := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 1 ≤ n j) (fun j => (n j : ℝ))]
      have h2 : ∑ j : {j // ¬ 1 ≤ n j}, (n j.1 : ℝ) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          have := j.2
          have : n j.1 = 0 := by omega
          simp [this]
      rw [h2, add_zero]
      have h3 : ∀ j : J', (n j.1 : ℝ) = (n' j : ℝ) + 1 := fun j => by
        simp only [n']
        rw [Nat.cast_sub j.2]
        ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rfl
    have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J' ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := by
      calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J' = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J') := by
            rw [hf]; ring
        _ ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := mul_le_mul_of_nonneg_left hrk (by positivity)
    rw [hsum, mul_add]
    linarith

theorem chain_moving_parts : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  intro hC hA hS k _ X _ p D hX x Δ hx hΔ N J _ e n M μ he hn ht hM hμ
  have key := levels_le_selfInter hC hA hS k X p D hX x Δ hx hΔ N J e n M μ he hn ht hM hμ
  have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
  have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M J e x (fun c => (n c.1 : ℝ) * Δ) he hx hw0 hM
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J ≤ ((D : ℝ) + 1) * Δ * gdeg M D := by
    calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J) := by
          rw [hf]; ring
      _ ≤ ((D : ℝ) + 1) * Δ * gdeg M D := mul_le_mul_of_nonneg_left hrk (by positivity)
  have hsum : ((∑ j, (n j + 1) : ℕ) : ℝ) = ∑ j, (n j : ℝ) + Fintype.card J := by
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum, mul_add]
  linarith

end GlobalTheory.HSNef
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_smallSections_change_of_metric : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → GoodFam P D (gdeg P.L D / D.factorial) (fun m => P.H m 1) → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  first | exact @GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation | exact GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation | (intros; apply GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxFamily_movingParts_chain_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  first | exact @GlobalTheory.HSNef.chain_moving_parts | exact GlobalTheory.HSNef.chain_moving_parts | (intros; apply GlobalTheory.HSNef.chain_moving_parts <;> assumption)
end


section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem ampleHS_of_principalisation : GlobalTheory.Published.Principalisation → AmpleHS := by
  intro hPr k _ X _ p D hX P a hA hS ha
  have hC := GlobalTheory.MixHt.arCalc_of_principalisation hPr
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hA
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hx
  have hG := GlobalTheory.T.isGoodSectionGroupFamily_ampleMultiples hC k X p D hX P hA
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.arithHilbertSamuel_smallSections_change_of_metric hPr k X p D hX P a hS ha hG
  obtain ⟨C, hCb⟩ := GlobalTheory.T.selfIntersection_canonicalWeights_tendsto_zero hC k X p D hX P hA e x hx
  refine ⟨max (t₀ + B) 1, fun t ht => ?_⟩
  have ht1 : t₀ + B ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hball : ∀ (u : SmFn p) (m : ℕ) (R : ℝ), ballIn (upperParabolic P u) (P.H m 1) m 1 R = (upperParabolic P u).Bl m 1 R :=
    fun _ _ _ => rfl
  have hball' : ∀ (m : ℕ) (R : ℝ), ballIn P (P.H m 1) m 1 R = P.Bl m 1 R := fun _ _ => rfl
  have hF : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hF1 : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hLg : 0 ≤ Real.log ((D : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  set g := gdeg P.L D with hg
  have hc : (a + ((D : ℝ) + 1) * t * g) / ((D + 1).factorial : ℝ) = g / D.factorial * t + a / (D + 1).factorial := by
    rw [Nat.factorial_succ]; push_cast; field_simp; ring
  have key : ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      |P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) - (g / D.factorial * t + a / (D + 1).factorial)|
        ≤ |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * n) / e) + |C| / n / (D + 1).factorial + 2 * ε := by
    intro n hn ε hε
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨u, hu, huB⟩ := hB n hn
    have hsemi := GlobalTheory.T.fubiniStudyWeightIncrement_semiPositive_curvature k X p D hX P e x hx n u hn hu
    obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (up P.L u)
    have hsi : (up P.L u).IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
    have han := hCb n u _ hn hu hsi
    have hdiff := ht₀ u B _ hB0 huB hsemi hsi t ht1
    obtain ⟨hnu1, hnu2, hgu, -, -⟩ := GlobalTheory.T.norm_basepointFree_sections_le_one_fubiniStudy k X p D hX P e x hx n u hn hu
    have hκ1 : Real.exp (-(Real.log ((D : ℝ) + 1) / (2 * n))) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg hLg (by positivity)))
    have hcnt := GlobalTheory.T.sectionCount_growth_metric_near_generatorMax hC k X p D hX (upperParabolic P u) hA e x hgu _ t (Real.exp_pos _) hκ1 ht2 hnu1 hnu2 ε hε
    rw [show (upperParabolic P u).L = up P.L u from rfl, GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hC k X p D hX P.L u, Real.log_exp, ← hg] at hcnt
    simp only [hball, hball'] at hdiff
    have hd := hdiff.eventually (Metric.ball_mem_nhds _ hε)
    set an := h (genericPoint X)
    set T := Real.log ((D : ℝ) + 1) / (2 * n) / e with hT
    have hT0 : 0 ≤ T := by positivity
    have hup : g / D.factorial * (t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e) ≤ g / D.factorial * t + |g| / D.factorial * T := by
      rw [show t - -(Real.log ((D : ℝ) + 1) / (2 * n)) / e = t + T by rw [hT]; ring, mul_add]
      gcongr
      exact le_abs_self g
    have han1 : an / (D + 1).factorial ≤ |C| / n / (D + 1).factorial :=
      div_le_div_of_nonneg_right ((le_abs_self an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    have hgT : 0 ≤ |g| / D.factorial * T := by positivity
    have han2 : -(an / (D + 1).factorial) ≤ |C| / n / (D + 1).factorial := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right ((neg_le_abs an).trans (han.trans (div_le_div_of_nonneg_right (le_abs_self C) hn0.le))) hF1.le
    filter_upwards [hd, hcnt] with m hm1 hm2
    rw [Real.dist_eq, abs_sub_lt_iff] at hm1
    have hsplit : P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) =
        (upperParabolic P u).lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) -
          (Real.log ((upperParabolic P u).Bl m 1 (Real.exp (t * m))).ncard - Real.log (P.Bl m 1 (Real.exp (t * m))).ncard) /
            (m : ℝ) ^ (D + 1) := by
      simp only [Pair.lc]; ring
    have hq : (an - a) / ((D + 1).factorial : ℝ) = an / (D + 1).factorial - a / (D + 1).factorial := sub_div _ _ _
    rw [hsplit, abs_le]
    constructor <;> linarith [hm2.1, hm2.2]
  rw [hc]
  refine Metric.tendsto_nhds.2 fun δ hδ => ?_
  set K := |g| / D.factorial * (Real.log ((D : ℝ) + 1) / 2 / e) + |C| / (D + 1).factorial with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K / δ)
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hKn : |g| / D.factorial * (Real.log ((D : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) / e) +
      |C| / ((n + 1 : ℕ) : ℝ) / (D + 1).factorial = K / ((n + 1 : ℕ) : ℝ) := by
    rw [hK]; field_simp
  have hKlt : K / ((n + 1 : ℕ) : ℝ) < δ / 2 := by
    have h1 : 2 * K / δ < ((n + 1 : ℕ) : ℝ) := hn.trans (by exact_mod_cast Nat.lt_succ_self n)
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ hn1]
    linarith
  filter_upwards [key (n + 1) (Nat.le_add_left 1 n) (δ / 8) (by positivity)] with m hm
  rw [hKn] at hm
  rw [Real.dist_eq]
  linarith

end GlobalTheory.HSNef
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNefCore

theorem key_ineq : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  intro hA hAmp hSP k _ X _ p D hX B β hB hβ x Δ hx hΔ J _ _ e n he hsm

  have hne : ∀ c, boxFam e x c ≠ 0 := by
    intro c
    simp only [boxFam]
    refine mul_ne_zero (he.ne_zero c.1) ?_
    exact Finset.prod_ne_zero_iff.2 fun i _ => hx.ne_zero i
  obtain ⟨Y, hY, π, φ, hvarY, hmod, htot⟩ := GlobalTheory.T.exists_birationalModel_totallyOrdered_family k X p D hX (J × Finset (Fin D)) (boxFam e x) hne
  haveI := hY
  set q := π ≫ p with hq
  set f : J × Finset (Fin D) → Y.functionField := fun c => φ (boxFam e x c) with hf
  have hbox : f = boxFam (φ ∘ e) (φ ∘ x) := by
    funext c
    simp [hf, boxFam, map_mul, map_prod]
  have hx' : AlgebraicIndependent ℤ (φ ∘ x) := hx.map' (f := φ.toIntAlgHom) φ.injective
  have he' : LinearIndependent ℤ (φ ∘ e) :=
    he.map' φ.toIntAlgHom.toLinearMap (LinearMap.ker_eq_bot.2 φ.injective)
  set w : J × Finset (Fin D) → ℝ := fun c => n c.1 * Δ with hw
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k Y q (J × Finset (Fin D)) f w htot
  obtain ⟨μ, hμ⟩ : ∃ μ, M.IsSelfInter μ := by
    obtain ⟨Φ, hΦ⟩ := ((hA.arExists k Y q D hvarY).2 PUnit fun _ => M).1
    exact ⟨_, ((hA.arIso k Y q D hvarY).2 PUnit _ Φ hΦ).1 PUnit.unit⟩

  have hN : ∀ j, n j ≤ ∑ i, n i := fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hchain := GlobalTheory.T.boxFamily_movingParts_chain_bound hA hAmp hSP k Y q D hvarY (φ ∘ x) Δ hx' hΔ (∑ i, n i) J (φ ∘ e) n M μ he' hN
    (hbox ▸ htot) (hbox ▸ hM) hμ

  set s : ℝ := Real.log (Fintype.card (J × Finset (Fin D))) / 2 with hs
  set B' := B.pull π rfl with hB'
  have hsmall : SmallFam B' f w := GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel k X Y p q π rfl φ hmod B _ (boxFam e x) w hsm
  have hle : Le M (B'.shift (fun _ => s) fun _ => rfl) := GlobalTheory.T.fubiniStudy_le_shift_of_smallSections k Y q M B' _ f w hM hsmall
  have hle' := (GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift k Y q (B'.shift (fun _ => s) fun _ => rfl) M M).2.2.2 Δ hle

  have hs0 : 0 ≤ s := by
    rw [hs]
    have : (1 : ℝ) ≤ Fintype.card (J × Finset (Fin D)) := by exact_mod_cast Fintype.card_pos
    have := Real.log_nonneg this
    linarith
  have hMnef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hA k Y q D hvarY M _ f w hM fun c => by
    simp only [hw]; exact mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have hB'nef : B'.IsNef D := GlobalTheory.T.hermitianLineBundle_isNef_pullback hA hSP k X Y p q D D hX hvarY π rfl B hB
  have hA1 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY B' s hs0 hB'nef
  have hA2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY _ Δ hΔ.le hA1
  have hM2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY M Δ hΔ.le hMnef

  obtain ⟨hg, hgs⟩ := GlobalTheory.T.geometricDegree_pull_birationalModel hA k X Y p q D hX hvarY π rfl φ hmod B
  have h1 := hgs β s hβ
  have h2 := hA.arShift k Y q D hvarY _ _ Δ h1
  have h3 := hA.arShift k Y q D hvarY M μ Δ hμ
  have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hA hAmp hSP k Y q D hvarY _ _ _ _ hA2 hM2 hle' h2 h3
  rw [GlobalTheory.CovTest.GeoSwap.gdeg_shift_const, hg] at hmono

  have hcard : s = Real.log (Fintype.card J) / 2 + D * Real.log 2 / 2 := by
    rw [hs, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
    push_cast
    rw [Real.log_mul (by exact_mod_cast Fintype.card_ne_zero) (by positivity), Real.log_pow]
    ring
  rw [hcard] at hmono
  nlinarith [hchain, hmono]

end GlobalTheory.HSNefCore
end


section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.HSNef.AmpleHS := by
  first | exact @GlobalTheory.HSNef.ampleHS_of_principalisation | exact GlobalTheory.HSNef.ampleHS_of_principalisation | (intros; apply GlobalTheory.HSNef.ampleHS_of_principalisation <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_hermitian_small_sections_key_inequality : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  first | exact @GlobalTheory.HSNefCore.key_ineq | exact GlobalTheory.HSNefCore.key_ineq | (intros; apply GlobalTheory.HSNefCore.key_ineq <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.lc_le_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  intro hC hA hS k _ X _ p D hX P x β q hx hxB hNef hSI hq
  haveI := hX.charZero
  haveI hcz : CharZero X.functionField :=
    charZero_of_injective_ringHom (f := (X.germToFunctionField ⊤).hom) (X.germToFunctionField_injective ⊤)
  have hβ : 0 ≤ β := by
    obtain ⟨h, hh, rfl⟩ := hSI
    exact (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX _ hNef).2 h hh _
  have hg : 0 ≤ gdeg (P.L.tens P.A) D := GlobalTheory.T.hermLineBundleGeometricDegree_nonneg_of_semiPos k X p D hX _ hNef.semiPos
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hΔ : 0 < Real.log ((q:ℝ)/2) := Real.log_pos (by linarith)
  have hF : (0:ℝ) < ((D+1).factorial : ℝ) := by positivity
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hFD : 0 < ((D+1).factorial : ℝ) * Real.log ((q:ℝ)/2) := mul_pos hF hΔ
  set g := gdeg (P.L.tens P.A) D with hgdef
  set Δ := Real.log ((q:ℝ)/2) with hΔdef
  set α := (β + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ) with hαdef
  set β' := (D + 1) * g / (2 * ((D + 1).factorial * Δ)) with hβ'def
  have hα : 0 ≤ α := div_nonneg (by positivity) hFD.le
  have hβ' : 0 ≤ β' := div_nonneg (by positivity) (by positivity)
  have hT : 0 ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) :=
    add_nonneg hα (mul_nonneg hβ' (Real.log_nonneg (by nlinarith)))
  have hexp : ∀ m : ℕ, (2 / q : ℝ) ^ m = Real.exp (-(m * Δ)) := by
    intro m
    have e1 : (2 / q : ℝ) = Real.exp (-Δ) := by
      rw [Real.exp_neg, hΔdef, Real.exp_log (by positivity), inv_div]
    rw [e1, ← Real.exp_nat_mul]
    congr 1
    ring
  have key : ∀ (r : ℕ) (e : Fin r → X.functionField) (n : Fin r → ℕ), LinearIndependent ℤ e →
      (∀ j, e j ∈ P.Bl 1 0 ((2 / q : ℝ) ^ n j)) →
      ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) := by
    intro r e n he hB
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using hT
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hsmall : SmallFam (P.L.tens P.A) (boxFam e x) (fun c => n c.1 * Δ) := by
      apply GlobalTheory.T.smallSections_pairSum_ratFnFamily_tensor k X p P
      rintro ⟨j, S⟩
      have h1 := hB j
      have h2 := hxB S
      obtain ⟨hm, hnu⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P 1 0 0 1 _ _ h1.1 h2.1
      have e10 : ((1:ℤ) + 0) = 1 := by norm_num
      have e01 : ((0:ℤ) + 1) = 1 := by norm_num
      rw [e10, e01] at hm hnu
      refine ⟨hm, fun σ y => ?_⟩
      show P.nu 1 1 σ y (e j * ∏ i ∈ S, x i) ≤ _
      rw [hnu, ← hexp]
      have h0 : 0 ≤ P.nu 1 0 σ y (e j) := by unfold Pair.nu; positivity
      exact (mul_le_of_le_one_right h0 (h2.2 σ y)).trans (h1.2 σ y)
    have hcore := GlobalTheory.T.nef_hermitian_small_sections_key_inequality hC hA hS k X p D hX _ β hNef hSI x Δ hx hΔ (Fin r) e n he hsmall
    rw [Fintype.card_fin] at hcore
    have hrs : (r:ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      have : r ≤ ∑ j : Fin r, (n j + 1) := by
        calc r = ∑ _j : Fin r, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun j _ => by omega)
      exact_mod_cast this
    have hs : ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log r := by
      have e2 : α + β' * Real.log r =
          (β + ((D:ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log r / 2) * g) / ((D + 1).factorial * Δ) := by
        rw [hαdef, hβ'def]
        field_simp
        ring
      rw [e2, le_div_iff₀ hFD]
      linarith
    exact GlobalTheory.le_add_mul_log_sq_of_le_add_mul_log α β' r _ hα hβ' (by exact_mod_cast hr) hrs hs
  have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 1 0 1
  exact GlobalTheory.T.log_ncard_unitBall_le_of_independent_level_bound X.functionField (P.H 1 0) (P.Bl 1 0) (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0) hfin q _ hq hT key
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_log_small_sections_upper_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  first | exact @GlobalTheory.HSNef.lc_le_bound | exact GlobalTheory.HSNef.lc_le_bound | (intros; apply GlobalTheory.HSNef.lc_le_bound <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefUpper

theorem log_ncard_smallSec {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) :
    Real.log (P.L.smallSec.ncard : ℝ) = P.lc 1 0 1 := by
  have h := SmallBall.encard_eq_Bl P (Pair.rep_base k X p P).1 P.L.smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  unfold Pair.lc
  rw [Set.ncard_def, Set.ncard_def, h]

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro HC HA HS k _ X _ p D hX L N a hL ha ε hε
  obtain ⟨⟨x, hx⟩, -⟩ := GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX
  obtain ⟨H, hNH, hbox⟩ := GlobalTheory.T.exists_twist_nef_squarefree_monomials_small HC k X p D hX N x
  set G := N.tens H with hG

  have hnef : ∀ m : ℕ, ((L.pow m).tens G).IsNef D := fun m =>
    GlobalTheory.T.hermLineBundle_isNef_tens HC k X p D hX _ _ (GlobalTheory.NefPow.isNef_pow HC k X p D hX L m hL) hNH
  obtain ⟨α, hα, hαlim⟩ := GlobalTheory.SelfInterGrowth.main HC k X p D hX L G a ha
  have hα0 : ∀ m, 0 ≤ α m := fun m => by
    obtain ⟨h, Hh, e⟩ := hα m
    rw [← e]
    exact (GlobalTheory.T.arithKleiman_heightNef_of_isNef HC HA HS k X p D hX _ (hnef m)).2 h Hh _
  have hg0 : ∀ m, 0 ≤ gdeg ((L.pow m).tens G) D := fun m =>
    GlobalTheory.T.hermLineBundleGeometricDegree_nonneg_of_semiPos k X p D hX _ (hnef m).semiPos
  have hglim := GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow HC k X p D hX L G
  refine GlobalTheory.T.eventually_le_of_smallSectionLogCountUpperBound D (fun m => Real.log (((L.pow m).tens N).smallSec.ncard : ℝ)) α
    (fun m => gdeg ((L.pow m).tens G) D) a (gdeg L D) hα0 hg0 hαlim hglim (fun m q hq => ?_) ε hε
  obtain ⟨P, hPL, hPA, hPbox⟩ := hbox ((L.pow m).tens N)
  have hiso : (P.L.tens P.A).Isometric ((L.pow m).tens G) := by
    rw [hPL, hPA]
    exact HermLB.isometric_tens_assoc _ _ _
  have T := GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric HC k X p D hX _ _ hiso.symm
  have hb := GlobalTheory.T.arith_log_small_sections_upper_bound HC HA HS k X p D hX P x (α m) q hx.1 hPbox (T.2.1 (hnef m)) (T.2.2.2.1 _ (hα m)) hq
  rw [hiso.gdeg_eq, ← log_ncard_smallSec] at hb
  have e : Real.log (P.L.smallSec.ncard : ℝ) = Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
    rw [hPL]
  simpa only [e] using hb

end GlobalTheory.NefUpper
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_nef_volume_upper_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.NefUpper.main | exact GlobalTheory.NefUpper.main | (intros; apply GlobalTheory.NefUpper.main <;> assumption)
end


section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_nef_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → GlobalTheory.Published.ArithHilbertSamuel := by
  intro hC hA hS k _ X _ p D hX L N a hL ha
  refine ⟨Eventually.of_forall fun m => GlobalTheory.T.finite_smallSec_hermitian_line_bundle_arith_variety k X p D hX _, ?_⟩
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  filter_upwards [GlobalTheory.T.arith_nef_volume_upper_bound hC hA hS k X p D hX L N a hL ha c hc,
    GlobalTheory.T.arithHilbertSamuel_lowerBound_semiPos_nefOnFibres hC hA k X p D hX L N a (nefFib_of_isNef hL) hL.semiPos ha c hc] with m h1 h2
  have hm : ‖(m : ℝ) ^ (D + 1)‖ = (m : ℝ) ^ (D + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, hm, abs_le]
  constructor <;> linarith
end


section
namespace GlobalTheory

theorem arithHilbertSamuel_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArithHilbertSamuel :=
  fun h => GlobalTheory.T.arithHilbertSamuel_nef_of_ample (GlobalTheory.MixHt.arCalc_of_principalisation h) (GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation h)
    (GlobalTheory.SemiPullAll.semiPull_of_principalisation h)

end GlobalTheory
end


namespace AlpogeRHCore23

theorem arithHilbertSamuelOfPrincipalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArithHilbertSamuel := by
  exact GlobalTheory.arithHilbertSamuel_of_principalisation

end AlpogeRHCore23
