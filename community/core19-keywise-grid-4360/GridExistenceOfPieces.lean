module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
public import Mathlib
public import Development.AutomorphicArithmetic.CharacterBoxes.ExS
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.CarriedPlMap
public import Formalism.LocalToGlobal.SelSide
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.ColPins
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
public import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem gridKey_heq_of_eq_preData_components (P P' : Pre) (h : P = P') (v : Pl P.host.F) (v' : Pl P'.host.F) (w : Pl P.host.F → Pl P.host.E)
    (w' : Pl P'.host.F → Pl P'.host.E) (c : ℕ → HChar P.host.E) (c' : ℕ → HChar P'.host.E) (hv : HEq v v') (hw : HEq w w')
    (hc : HEq c c') :
    HEq ((v, w v, fun a : Fin P.R.m => c (a.1 + 1)) : GKey P) ((v', w' v', fun a : Fin P'.R.m => c' (a.1 + 1)) : GKey P') := by
  subst h; subst hv; subst hw; subst hc; rfl

theorem gkeyOf_heq {X X' : Stages} {T T' : Type} {L : Formalism.IndefR.Links.LevCh X.toD7 T} {L' : Formalism.IndefR.Links.LevCh X'.toD7 T'} {sc : GlobalTheory.ChiGrid.Consts}
    {G : GridData L sc} {G' : GridData L' sc} (h : GAgree G G') (hp : X'.B.toPre = X.B.toPre) : HEq (gkeyOf G') (gkeyOf G) :=
  gridKey_heq_of_eq_preData_components _ _ hp _ _ _ _ _ _ h.v0 h.w h.chiH

end GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem.LiteralAutomorphy


set_option maxHeartbeats 3200000 in
/-- With the two transport keys fixed, grid existence needs only one algebraic
coefficient-field element, independent of the compatible stage. Neither set of
keys needs to be finite for this statement. -/
theorem exGrid_for_key_pair_of :
    WeilEx → IsEx → NFAll → NFSq → CarryG → CarryW → CarryS → TrEasy → TrPhase →
      TrJet → TrBot → TrSq →
    ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ s : Scale, s.eps = ε → x₀ ≤ s.x →
      ∀ (P : Pre) (f : Fr P) (κ : Key P) (γ : GKey P), ∃ a : ℂ, IsAlgebraic ℚ a ∧
      ∀ (X : Stages) (f' : Fr X.B.toPre), X.B.toPre = P → HEq f' f → ∀ large₂ : SizeData₂ X.toD7, large₂.sc = s → GlobalTheory.SqTop.Rec large₂ →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) [Field Ks]
        [NumberField Ks] [Algebra Ks X.toD7.what₂.LL] (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F →
        R.C = Fr.at X f' → TwistPlacesOffPrimeQZero R.toLevCh → HEq (keyOf R.toLevCh) κ → ∀ G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩,
        HEq (gkeyOf G₀) γ → a ∈ Set.range X.toD7.what₂.embLL →
        ∃ G : GridData R.toLevCh ⟨1, CF, s.b⟩, gkeyOf G = gkeyOf G₀ ∧ Full R G := by
  classical
  intro h1 h2 h3 h4 cG cW cS t1 t2 t3 t4 t5
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  obtain ⟨a4, h4⟩ := h4
  refine ⟨max a1 (max a2 (max a3 a4)), fun ε CF hC => ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x2, h2⟩ := h2 ε CF (le_of_max_le_left (le_of_max_le_right hC))
  obtain ⟨x3, h3⟩ := h3 ε CF (le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hC)))
  obtain ⟨x4, h4⟩ := h4 ε CF (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hC)))
  refine ⟨max x1 (max x2 (max x3 x4)), fun s he hx P f κ γ => ?_⟩
  have hx1 := le_of_max_le_left hx
  have hx2 := le_of_max_le_left (le_of_max_le_right hx)
  have hx3 := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hx))
  have hx4 := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hx))
  by_cases H : ∃ (X : Stages) (f' : Fr X.B.toPre) (_ : X.B.toPre = P) (_ : HEq f' f) (large₂ : SizeData₂ X.toD7) (_ : large₂.sc = s)
      (_ : GlobalTheory.SqTop.Rec large₂) (Γ : Type) (_ : Group Γ) (_ : Fintype Γ) (Pl0 T : Type)
      (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks)
      (_ : Algebra Ks X.toD7.what₂.LL) (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A) (G₀ : GridData R.toLevCh ⟨1, CF, s.b⟩),
      HidaSetting large₂ R F ∧ R.C = Fr.at X f' ∧ TwistPlacesOffPrimeQZero R.toLevCh ∧ HEq (keyOf R.toLevCh) κ ∧ HEq (gkeyOf G₀) γ
  swap
  · exact ⟨0, isAlgebraic_zero, fun X f' a b large₂ c r Γ _ _ Pl0 T A Ks _ _ _ R F d e g i G₀ j _ =>
      absurd ⟨X, f', a, b, large₂, c, r, Γ, _, _, Pl0, T, A, Ks, _, _, _, R, F, G₀, d, e, g, i, j⟩ H⟩
  obtain ⟨X0, f0, a0, b0, Lg0, rfl, r0, Γ0, _, _, Pl00, T0, A0, Ks0, _, _, _, R0, F0, G00, d0, e0, g0, i0, j0⟩ := H
  obtain ⟨W0, hW0, ⟨S0⟩⟩ := h1 _ Lg0 he hx1 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS, hIs⟩ := h2 _ Lg0 he hx2 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G00 W0 hW0 S0
  obtain ⟨N, hN, hAll⟩ := h3 _ Lg0 he hx3 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 _ hIs rfl
  obtain ⟨N2, hN2, hSq⟩ := h4 _ Lg0 he hx4 r0 T0 R0.toLevCh A0.μ0 d0.core.lev G00
  let : FiniteDimensional ℚ N := hN
  let : FiniteDimensional ℚ N2 := hN2
  let K : IntermediateField ℚ ℂ := N ⊔ N2
  obtain ⟨a, ha⟩ := Field.exists_primitive_element ℚ K
  have hK : IntermediateField.adjoin ℚ {(a : ℂ)} = K := by
    rw [← IntermediateField.lift_adjoin_simple ℚ K a, ha, IntermediateField.lift_top]
  refine ⟨a, IntermediateField.isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic a), ?_⟩
  intro X f' a' b' large₂ hs hr Γ _ _ Pl0 T A Ks _ _ _ R F d e' g i G₀ j hz
  let L : IntermediateField ℚ ℂ := X.toD7.what₂.embLL.fieldRange.toIntermediateField
    (fun q => SubfieldClass.ratCast_mem _ q)
  have hKL : K ≤ L := by
    rw [← hK, IntermediateField.adjoin_simple_le_iff]
    exact hz
  have r1 : Set.range (algebraMap N ℂ) ⊆ Set.range X.toD7.what₂.embLL := by
    rintro _ ⟨y, rfl⟩
    exact hKL (show (y : ℂ) ∈ K from (show N ≤ K from le_sup_left) y.2)
  have r2 : Set.range (algebraMap N2 ℂ) ⊆ Set.range X.toD7.what₂.embLL := by
    rintro _ ⟨y, rfl⟩
    exact hKL (show (y : ℂ) ∈ K from (show N2 ≤ K from le_sup_right) y.2)
  have hk : HEq (keyOf R.toLevCh) (keyOf R0.toLevCh) := i.trans i0.symm
  have hpre : X.B.toPre = X0.B.toPre := a'.trans a0.symm
  have key : ∀ (P P' : Pre) (_ : P = P') (k : Key P) (k' : Key P'), HEq k k' → ∀ x ∈ k, ∃ y ∈ k', HEq x.1 y.1 ∧ HEq x.2 y.2 := by
    rintro P _ rfl k k' h x hx
    obtain rfl := eq_of_heq h
    exact ⟨x, hx, HEq.rfl, HEq.rfl⟩
  have hι : ∀ t : T, ∃ t0 : T0, HEq (R.xiH t) (R0.xiH t0) ∧ HEq (R.Q t) (R0.Q t0) := fun t => by
    obtain ⟨_, ⟨t0, rfl⟩, h⟩ := key _ _ hpre _ _ hk _ ⟨t, rfl⟩
    exact ⟨t0, h⟩
  choose ι hι using hι
  have one : ∀ (P P' : Pre) (_ : P = P'), HEq (1 : HChar P.host.E) (1 : HChar P'.host.E) := by rintro P _ rfl; rfl
  have hb : ι A.μ0 = A0.μ0 := d0.core.lev.xi_inj (by
    rw [d0.core.lev.xi_base]
    have := (hι A.μ0).1
    rw [d.core.lev.xi_base] at this
    exact eq_of_heq (this.symm.trans (one _ _ hpre)))
  have hL : LAgree R0.toLevCh R.toLevCh A0.μ0 A.μ0 ι :=
    ⟨hpre, d0.core.lev, d.core.lev, ⟨f0, f', b'.trans b0.symm, e0, e'⟩, hb, fun t => (hι t).1, fun t => (hι t).2, d0.betaX,
      d.betaX⟩
  obtain ⟨G, hG⟩ := cG _ _ _ _ _ _ _ _ _ hL _ G00
  obtain ⟨W, hW, hWA⟩ := cW _ _ _ _ _ Γ Pl0 A Ks R _ ι hL d.core.chain d.core.models _ G00 G hG W0
  obtain ⟨S', hS'⟩ := cS _ _ _ _ _ _ _ _ _ hL _ G00 G hG W0 W hWA S.toGridChoice
  have hA : Agree S.toGridChoice S' A0.μ0 A.μ0 ι := ⟨hL, hG, hWA, hS'⟩
  have h2' := h2 _ large₂ (hs ▸ he) (hs ▸ hx2) Γ Pl0 T A Ks R F d
  rw [hs] at h2'
  obtain ⟨M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hS2, hIs'⟩ := h2' G W hW S'
  have gk : gkeyOf G = gkeyOf G₀ := eq_of_heq ((gkeyOf_heq hG hpre).trans (j0.trans j.symm))
  refine ⟨G, gk, W, M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hIs', ?_, ?_⟩
  · obtain ⟨u1, u2, u3⟩ := t1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N (algebraMap N ℂ)
    have hAll' : AllIn (algebraMap N ℂ) S' A.μ0 := ⟨u1 hAll.chars, u2 hAll.root,
      t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.phase, t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.jet, u3 hAll.ratios,
      t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.bot⟩
    subst hS2
    exact hAll'.numbersIn.mono r1
  · exact (t5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N2 _ hSq).mono r2

theorem exGrid_of : WeilEx → IsEx → NFAll → NFSq → CarryG → CarryW → CarryS → TrEasy → TrPhase → TrJet → TrBot → TrSq → KeyFin →
    GKeyFin → ExGrid := by
  classical
  intro h1 h2 h3 h4 cG cW cS t1 t2 t3 t4 t5 kF gF
  obtain ⟨CF0, hCF⟩ := exGrid_for_key_pair_of h1 h2 h3 h4 cG cW cS t1 t2 t3 t4 t5
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF ε CF hC
  refine ⟨x₀, fun s he hs P f Ξ hΞ => ?_⟩
  obtain ⟨𝒦, hK, HK⟩ := kF P Ξ hΞ
  obtain ⟨𝒢, hG, HG⟩ := gF P 1
  choose a ha hgrid using hx s he hs P f
  refine ⟨(hK.toFinset ×ˢ hG.toFinset).image (fun p => a p.1 p.2), ?_, ?_⟩
  · intro z hz
    obtain ⟨⟨κ, γ⟩, -, rfl⟩ := Finset.mem_image.mp hz
    exact ha κ γ
  intro X f' Ξ' hP hf hΞ' hz large₂ hscale hRec Γ _ _ Pl0 T A Ks _ _ _ R F st hCf ho htw G₀
  subst hP
  obtain rfl := eq_of_heq hΞ'
  obtain ⟨κ, hκ, hk⟩ := HK X T R.toLevCh A.μ0 rfl st.core.lev htw
  obtain ⟨γ, hγ, hg⟩ := HG X T R.toLevCh _ G₀ rfl rfl
  exact hgrid κ γ X f' rfl hf large₂ hscale hRec Γ Pl0 T A Ks R F st hCf ho hk G₀ hg
    (hz _ (Finset.mem_image_of_mem (fun p : Key _ × GKey _ => a p.1 p.2)
      (a := (κ, γ)) (Finset.mem_product.mpr ⟨hK.mem_toFinset.mpr hκ, hG.mem_toFinset.mpr hγ⟩)))

end GlobalTheory.Mem.LiteralAutomorphy

end
