module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralsTermsOneDoubleCosetStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphismCovolumeEqLatticeMassStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelCharacterUnipotentPartOfAdmissibilityWitnesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhaseStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEqStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCosetStatement

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpTerm

theorem gval_of_movesTo {D : D7} {T T' : D.host.E} {F00 F : LFlag (D.sp.Y 0) D.R.rS T}
    {F'0 F' : LFlag (D.sp.Y 0) D.R.rS T'} {ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h : MovesTo F00 F'0 F F' ρ U U') : Gval F F' = Gval F00 F'0 := by
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := h
  have hZ : ZhatL F F' = U.conjTranspose * ZhatL F00 F'0 * U' := by
    ext a b
    have e1 : ZhatL F F' a b = (VS D).hT (ρ (frame F a)) (ρ (frame F' b)) := by
      rw [hρ]; rfl
    have hz : ∀ c d, ZhatL F00 F'0 c d = (VS D).hT (frame F00 c) (frame F'0 d) := fun _ _ => rfl
    rw [e1, hF a, hF' b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, hz, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Matrix.conjTranspose_apply, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
    simp only [RingHom.id_apply]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))
    ring
  have hD : ∀ l, Dl F.fl F'.fl l = Dl F00.fl F'0.fl l := by
    intro l
    have := Formalism.L2.SG.Pf.leadMinor_uni U.conjTranspose (ZhatL F00 F'0) U'
      (fun a c hac => by simp [Matrix.conjTranspose_apply, (hU c a).1 hac])
      (fun a => by simp [Matrix.conjTranspose_apply, (hU a a).2 rfl])
      (fun d b hbd => (hU' d b).1 hbd) (fun b => (hU' b b).2 rfl) l
    rw [← hZ] at this
    exact this
  simp only [Gval, Gflag, hD]

theorem G_eq_gval {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    t.G = Gval (lf D (X.Fu u)) t.frame :=
  Formalism.L2.SG.TermDef.Gt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩

theorem lam_eq_of_row {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} {t t₀ : TauC Y u u'}
    (h : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) : t.lam = t₀.lam ∧ t.lam' = t₀.lam' :=
  ⟨congrArg (fun r => r.1.1) h, congrArg (fun r => r.2.1.1) h⟩

theorem exists_admissibleWitness_rowTerm {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    ∃ ξ, AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ :=
  t.rep.2.2.2.2.2.1

end GlobalTheory.AmpTerm

namespace GlobalTheory.AmpTerm


open scoped ComplexConjugate in
open Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.RealObj Formalism.L2.SG.PairVal in
/-- A relevant term has the Hilbert–Schmidt norm of its canonical pinned operator,
multiplied by the strictly positive stabilizer covolume of any measurable transversal. -/
theorem orbital_norm_at_point {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (hν : NuQPin X u u' ν)
    (t : TauC Y u u') (hr : t.relevant) (hG : t.G ≠ 0) :
    let w := ptOf t.toTerm
    have := FiniteDimensional.completeSpace ℂ (X.Vpi u)
    ∃ μ : Measure X.B.I.Ginf, VolPin.IsPinnedR t w μ ∧ ∀ K, LoopTerm.IsFundR t K →
      0 < (μ K).toReal ∧ ‖PackageTie.hsEmb (OOt t)‖ = (μ K).toReal *
        ‖PackageTie.hsEmb (OO (ν (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))‖ := by
  have := FiniteDimensional.completeSpace ℂ (X.Vpi u)
  have hAt := LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'
  obtain ⟨w₀, hw₀⟩ := hAt t.toTerm hG hr
  have hw := ptOf_spec _ ⟨w₀, hw₀, hr⟩
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := RowForm.realDecompC_gamW X Y u u'
    (RowForm.RealDecompL.realDecompC_of X Y u u' hAt) t hr hG
  obtain ⟨μ, hp, hform⟩ := formTransp_pinned X Y u u' ν hν t
    (RelChar.relCharC_holds D X Y u u' t hr) _ hpt g hg g' hg' hdec
  refine ⟨μ, hp, fun K hK => ?_⟩
  have hpos := LoopBPin.covolPos_holds u u' t hr hG _ μ K hw hp hK
  refine ⟨hpos, ?_⟩
  have hphase : ‖X.psiInfU u g * conj (X.psiInfU u' g')‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, Vanish.psiInfU_norm, Vanish.psiInfU_norm, one_mul]
  have move := RowForm.ClassFrameNormal.oo_map_mulLeft (ν (gamW X u u' (ptOf t.toTerm))) (X.Wu u) (X.Wu u')
    (gamW X u u' (ptOf t.toTerm)) g g' (X.psiInfU u g) (X.psiInfU u' g')
    (InfCut.piIso X u g hg) (InfCut.piIso X u' g' hg')
    (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x)
  have h := hform K hK.1 hK.2
  rw [hdec, move] at h
  rw [h, ← Complex.coe_smul, map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  exact congrArg (fun n : ℝ => (μ K).toReal * n)
    (GlobalTheory.CosetOrbital.norm_hsEmb_unitary _ hphase (InfCut.piIso X u g hg) (InfCut.piIso X u' g' hg') _)

open Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.RealObj Formalism.L2.SG.PairVal in
/-- Among relevant terms with nonzero G invariant, whether the orbital operator vanishes
depends only on the canonical point, not on the row or double coset. -/
theorem orbital_eq_zero_iff_of_ptOf_eq {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t s : TauC Y u u') (ht : t.relevant) (hs : s.relevant) (hGt : t.G ≠ 0) (hGs : s.G ≠ 0)
    (hpts : ptOf t.toTerm = ptOf s.toTerm) : OOt t = 0 ↔ OOt s = 0 := by
  have := FiniteDimensional.completeSpace ℂ (X.Vpi u)
  choose ν hreg _ hpin using NGPin.exists_at X u u' (NGPin.pinHaarEx_of_place NGPin.placeHaar_holds)
  have hν : NuQPin X u u' ν := ⟨hreg, fun w hw => hpin _ w hw rfl⟩
  have hz (a : TauC Y u u') (hr : a.relevant) (hG : a.G ≠ 0) :
      OOt a = 0 ↔ ‖PackageTie.hsEmb (OO (ν (gamW X u u' (ptOf a.toTerm))) Set.univ
        (X.Wu u) (X.Wu u') (gamW X u u' (ptOf a.toTerm)))‖ = 0 := by
    obtain ⟨μ, _, hform⟩ := orbital_norm_at_point Y u u' ν hν a hr hG
    obtain ⟨hpos, hn⟩ := hform _ (LoopBPin.isFundR_fundOf a)
    have hzero : ‖PackageTie.hsEmb (OOt a)‖ = 0 ↔ OOt a = 0 :=
      ⟨fun h => KExpCut.hsEmb_injective (by simpa only [map_zero] using norm_eq_zero.mp h), fun h => by simp [h]⟩
    rw [← hzero, hn, mul_eq_zero, or_iff_right hpos.ne']
  rw [hz t ht hGt, hz s hs hGs, hpts]


open Formalism.L2.SG.PairVal in
theorem amp_eq_mass_phase : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = ((((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat (ρ * n) t.lam) : ℝ) : ℂ) * G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat (ρ * n) t.lam)) • T := by
  intro D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c ν hν t₀ ρ U U' hmv hrel hpt
  have hG0 : t₀.G ≠ 0 := by
    rw [G_eq_gval]; exact fun h => hG ((gval_of_movesTo hmv).symm.trans h)
  obtain ⟨-, T0, hT0, hform⟩ := GlobalTheory.T.orbital_integrals_terms_one_doubleCoset D X Y u u' hS ν hν t₀ hrel hG0 w hpt.symm
  have hpU : psiInf (gS D) (sgUp U) ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U); rw [h, norm_zero] at this; exact zero_ne_one this
  have hpU' : psiInf (gS D) (sgUp U') ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U'); rw [h, norm_zero] at this; exact zero_ne_one this
  refine ⟨(((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
      psiInf (gS D) (sgUp U) * (psiInf (gS D) (sgUp U'))⁻¹) • T0, ?_, ?_⟩
  · rw [map_smul, norm_smul, hT0]
    unfold Jw
    rw [map_smul, norm_smul, norm_mul, norm_mul, norm_inv, norm_psiInf, norm_psiInf]
    simp
  · rintro t n m hrow ⟨hn, hm, hlin⟩
    obtain ⟨hlam, hlam'⟩ := lam_eq_of_row hrow
    have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
    obtain ⟨xn, hxn, -⟩ := hL.1 n hn.1
    obtain ⟨xm, hxm, -⟩ := hL.1 m hm.1
    obtain ⟨μR, K, hpin, hK, hOO⟩ := hform t n m xn xm ⟨hn, hm, hlin⟩ hxn hxm
    obtain ⟨-, -, -, -, -, hgrp⟩ :=
      GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
    obtain ⟨A, A', hA, hA', hnA, hmA', hmv'⟩ := hgrp t n m ⟨hn, hm, hlin⟩
    have hcos := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hS t₀ t n m hrel hG0 ⟨hn, hm, hlin⟩
    have hvol := GlobalTheory.T.automorphismCovolume_eq_latticeMass D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv' hcos.1 μR hpin K hK
    obtain ⟨ξ, hξ⟩ := exists_admissibleWitness_rowTerm t
    have hchi := GlobalTheory.T.levelCharacter_unipotentPart_of_admissibilityWitness D X Y u u' hS t ξ hξ
    have hterm := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv').2 ξ hξ
    have hdat := (GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv t n m hlam hlam'
      ⟨hn, hm, hlin⟩).1 hrow
    rw [hdat] at hterm
    have hpn := (hL.2.2 u xn n hxn).2 hn A hnA
    have hpm := (hL.2.2 u' xm m hxm).2 hm A' hmA'
    have hU := hmv.2.1
    have hU' := hmv.2.2.1
    unfold ampN
    rw [hchi, hOO, hpn, hpm, hvol, hterm, Formalism.L2.SG.Pf.sgUp_mul hU hA, Formalism.L2.SG.Pf.sgUp_mul hU' hA',
      Formalism.L2.SG.Pf.psiInf_add, Formalism.L2.SG.Pf.psiInf_add, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp

end GlobalTheory.AmpTerm
