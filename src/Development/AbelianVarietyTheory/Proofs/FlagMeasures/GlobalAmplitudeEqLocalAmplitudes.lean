module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeExpansionOverFinitePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDatumOfTermInMovedLatticeOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhaseStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumOrbitNormaliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodOfHpEqOne

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.AmpLoc


set_option maxHeartbeats 1000000 in
theorem global_amp_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (R : ∀ p, LocNG.Reps (FP p)) (S1 : Finset (PlF D)) (Om : Finset {p // p ∈ S1}) (d : ∀ p : {p // p ∈ S1}, LocNG.Datum (FP p.1)), (∀ p, p ∉ S1 → (FP p).PrimeTo) → (∀ p, p ∈ Om ↔ ¬ (FP p.1).PrimeTo) → (∀ p : {p // p ∈ S1}, Over (FP p.1) (d p) (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1 t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u'))) → ∀ Q : Prop → Prop, ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ = ‖∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) else LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t))‖ := by
  intro D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv R S1 Om d hout hOm hover Q
  have hT : G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) :=
    (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv).1
  have hW := fun p => GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p)
    D.R.rS D.R.k (FP p) (G.S p) (c.c p)
  obtain ⟨-, -, -, -, hgood⟩ := GlobalTheory.HL.BadPlaces.bad_places _ _ _ G hk _ _ hT
  have hOmS : G.Om ⊆ (S1 : Set (PlF D)) := by
    intro p hp
    by_contra hn
    exact hp ((hW p).2.2.2.1 (hout p hn))
  obtain ⟨κ, hκ, hdec⟩ := GlobalTheory.T.amplitude_products_over_finite_places _ _ _ G hk _ ⟨_, hT⟩ S1 hOmS
  rw [hdec Q, norm_mul, hκ, one_mul]

  have hloc : ∀ p : {p // p ∈ S1},
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1)
          (fun Λ => ¬ (G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1) Λ) =
        LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) ∧
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1) ((G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1)) =
        LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t) := by
    intro p
    have := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).lf
    have := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).char0
    have hu : (Function.update (G.datOf (c.lat ρ t₀.lam)) p.1 ((c.c p.1).dat (d p))) p.1 = (c.c p.1).dat (d p) :=
      Function.update_self _ _ _
    obtain ⟨h, hh, hδ⟩ := GlobalTheory.T.localDatum_of_term_in_movedLattice_orbit D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv p.1 (d p)
      (hover p) _ hu
    rw [hu] at hδ
    obtain ⟨e1, e2⟩ := (hW p.1).2.2.2.2 (R p.1) (d p)
    rw [e1, e2, ← hδ]
    constructor
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq hb
        exact hq ((GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.1 hb)
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact not_congr ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq
        exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.2 hq
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
  have hzero : ∀ p ∈ S1, (FP p).PrimeTo →
      (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ) = 0 := by
    intro p _ hp
    have hBB := (hgood p (fun hm => hm ((hW p).2.2.2.1 hp))).1
    unfold Frames.amp
    calc
      _ = ∑' _ : MulAction.orbitRel.Quotient (G.S p).St (Submodule _ (G.S p).V), (0 : ℂ) := by
        apply tsum_congr
        intro o
        rw [ite_eq_right]
        rintro ⟨ht, hb⟩
        exact hb (hBB _ _ ht)
      _ = 0 := tsum_zero
  rw [Formalism.HermitianLatticeCounting.DefectSum.filter_ambient]
  simp only [← Finset.prod_coe_sort S1, ← (fun p => (hloc p).1), ← (fun p => (hloc p).2)]
  congr 4
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : p ∈ Om
  · simp [hp]
  · have hprime : (FP p.1).PrimeTo := not_not.mp (fun h => hp ((hOm p).2 h))
    simp [hp, hzero p.1 p.2 hprime]

end GlobalTheory.HL.AmpLoc
