module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameNormal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagTermInvariantsConstOnRationalDoubleCosetStatement

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.CosetOrbital

open Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FormTranspose

theorem sum_norm_sq_basis_indep {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {ι : Type} [Fintype ι] (T : Wq →L[ℂ] Wp) (b e : OrthonormalBasis ι ℂ Wq) :
    ∑ i, ‖T (b i)‖ ^ 2 = ∑ i, ‖T (e i)‖ ^ 2 :=
  Formalism.L2.SG.Pf.RowForm.ClassFrameOperators.sum_norm_sq_indep T b e

theorem norm_hsEmb_unitary {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (c : ℂ) (hc : ‖c‖ = 1) (A : Wp ≃ₗᵢ[ℂ] Wp) (B : Wq ≃ₗᵢ[ℂ] Wq) (O : Wq →L[ℂ] Wp) :
    ‖Formalism.L2.SG.PackageTie.hsEmb (c • ((A.toContinuousLinearEquiv : Wp →L[ℂ] Wp).comp
      (O.comp (B.symm.toContinuousLinearEquiv : Wq →L[ℂ] Wq))))‖ =
      ‖Formalism.L2.SG.PackageTie.hsEmb O‖ := by
  rw [map_smul, norm_smul, hc, one_mul]
  exact Formalism.L2.SG.Pf.RowForm.ClassFrameOperators.norm_hsEmb_conj A B O

variable {D : D7} (X : HidaSetting D)

theorem psi_inv (u : D.what₂.Word) {n : X.B.I.Ginf} (hn : n ∈ X.NinfU u) :
    X.psiInfU u n⁻¹ = (X.psiInfU u n)⁻¹ := by
  have hC := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  have hne : ∀ s, X.psiInfU u s ≠ 0 := by
    intro s h0; have := psiInfU_norm X u s; rw [h0, norm_zero] at this; exact zero_ne_one this
  have h1 : X.psiInfU u 1 = 1 := by
    have e := (hC.2.1 1 hC.1 1 hC.1).2
    rw [one_mul] at e
    have e2 : X.psiInfU u 1 * (X.psiInfU u 1 - 1) = 0 := by rw [mul_sub, ← e]; ring
    rcases mul_eq_zero.1 e2 with h | h
    · exact absurd h (hne 1)
    · exact sub_eq_zero.1 h
  have e := (hC.2.1 n hn n⁻¹ (hC.2.2 n hn)).2
  rw [mul_inv_cancel, h1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

end GlobalTheory.CosetOrbital

namespace GlobalTheory.CosetOrbital
open Formalism.L2.SG.Pf.FormTranspose

theorem wu_move {D : D7} (X : HidaSetting D) (v : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.NinfU v) (h : X.B.I.Ginf)
    (hh : h ∈ X.SinfU v) (x : X.B.I.Ginf) :
    X.Wu v ((s⁻¹ * h) * x) = (X.psiInfU v s⁻¹ * X.psiInfU v h) •
      (Formalism.L2.SG.RealObj.InfCut.piIso X v h hh) (X.Wu v x) := by
  have hNS : ∀ {s : X.B.I.Ginf}, s ∈ X.NinfU v → s ∈ X.SinfU v := fun hs p => (hs p).1
  have hsi : s⁻¹ ∈ X.NinfU v := ninf_inv X v hs
  rw [mul_assoc, (X.Wu_spec v).1 s⁻¹ (hNS hsi) (h * x), (X.piU_rep v).2.2.2.1 s⁻¹ hsi,
    one_apply_eq_self, (X.Wu_spec v).1 h hh x, Formalism.L2.SG.RealObj.InfCut.piIso_apply, smul_smul]
  rfl

end GlobalTheory.CosetOrbital

namespace GlobalTheory.CosetOrbital

open Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FormTranspose Set

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

theorem pinned_form (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hP : Formalism.L2.SG.RealObj.NuQPin X u u' νq)
    (t : TauC Y u u') (hrel : t.relevant) (w : Point D.host.E (D.R.rS + 1))
    (hreal : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ)
    (g : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (g' : X.B.I.Ginf) (hg' : g' ∈ X.SinfU u')
    (hdec : t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' w * g'⁻¹) :
    ∃ μR : Measure X.B.I.Ginf, Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧
      (MeasurableSet (FundOf t) ∧ ∀ y ∈ Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ FundOf t) ∧
      OOt t = (μR (FundOf t)).toReal •
        (haveI := FiniteDimensional.completeSpace ℂ (X.Vpi u)
         OO ((νq (Formalism.L2.SG.RealObj.gamW X u u' w)).map (fun x => g * x)) Set.univ (X.Wu u) (X.Wu u') t.pt.1) := by
  obtain ⟨μR, hPin, hform⟩ := Formalism.L2.SG.Pf.formTransp_pinned X Y u u' νq hP t
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' t hrel) w hreal g hg g' hg' hdec
  obtain ⟨hKm, hKu⟩ := Formalism.L2.SG.Pf.fundOf_transversal X Y u u' t
  exact ⟨μR, hPin, ⟨hKm, hKu⟩, hform _ hKm hKu⟩

end GlobalTheory.CosetOrbital

namespace GlobalTheory.CosetOrbital

open Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.Pf.FormTranspose

theorem conj_inv_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) : conj (z⁻¹) = z := by
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have h1 : conj z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_right h1

/-- On a rational double coset, one operator of the prescribed Hilbert–Schmidt norm works for every measurable
fundamental domain of each pinned stabilizer, not just for one choice of domain. -/
theorem coset_orbital_form_all :
    ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν →
      ∀ t₀ : TauC Y u u', t₀.relevant → t₀.G ≠ 0 → ∀ w, w = Formalism.L2.SG.PairVal.ptOf t₀.toTerm →
        (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧ ∃ T : X.Vpi u' →L[ℂ] X.Vpi u,
          ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.completeSpace ℂ (X.Vpi u);
             OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w))‖ ∧
          ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (xn xm : X.B.I.GA),
            n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m →
            RatLink X xn n → RatLink X xm m →
            ∃ μR : Measure X.B.I.Ginf, Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧ ∀ K : Set X.B.I.Ginf,
              (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ K) →
              OOt t = (((μR K).toReal : ℂ) * ((X.psiInfU u xn.1)⁻¹ * X.psiInfU u' xm.1)) • T := by
  intro D X Y u u' hSt ν hν t₀ hrel₀ hG₀ w hw
  have := FiniteDimensional.completeSpace ℂ (X.Vpi u)
  have hRD := Formalism.L2.SG.Pf.RowForm.RealDecompL.realDecompC_of X Y u u'
    (Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := Formalism.L2.SG.Pf.RowForm.realDecompC_gamW X Y u u' hRD t₀ hrel₀ hG₀
  subst hw
  set O := OO (ν (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm))) Set.univ (X.Wu u) (X.Wu u')
    (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm)) with hO
  set A := Formalism.L2.SG.RealObj.InfCut.piIso X u g hg with hA
  set B := Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg' with hB
  set c0 := X.psiInfU u g * conj (X.psiInfU u' g') with hc0
  have hc0n : ‖c0‖ = 1 := by
    rw [hc0, norm_mul, Complex.norm_conj, psiInfU_norm, psiInfU_norm, one_mul]
  refine ⟨hpt, c0 • ((A.toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u).comp
    (O.comp (B.symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'))), norm_hsEmb_unitary c0 hc0n A B O, ?_⟩
  rintro t n m xn xm ⟨hn, hm, hlin⟩ hxn hxm
  obtain ⟨hrel, -, hptt, -⟩ := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hSt t₀ t n m hrel₀ hG₀ ⟨hn, hm, hlin⟩
  have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hxnN : xn.1 ∈ X.NinfU u := ((hL.2.2 u xn n hxn).1).1 hn
  have hxmN : xm.1 ∈ X.NinfU u' := ((hL.2.2 u' xm m hxm).1).1 hm
  have hlink : RatLink X (xn⁻¹ * t₀.pt * xm) t.lin := by
    rw [hlin]
    have h1 := (hL.2.1 _ _ _ _ hxn t₀.rep.2.1).2.1
    exact (hL.2.1 _ _ _ _ (hL.2.1 _ _ _ _ h1 t₀.rep.2.1).1 hxm).1
  have hpt_eq : t.pt = xn⁻¹ * t₀.pt * xm := (hL.1 t.lin t.rep.2.2.1).unique t.rep.2.1 hlink
  have hpt1 : t.pt.1 = xn.1⁻¹ * t₀.pt.1 * xm.1 := by rw [hpt_eq]; rfl
  have hNS : ∀ (v : D.what₂.Word) {s : X.B.I.Ginf}, s ∈ X.NinfU v → s ∈ X.SinfU v := fun v s hs => fun p => (hs p).1
  have hgt : xn.1⁻¹ * g ∈ X.SinfU u :=
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)).mul_mem (hNS u (ninf_inv X u hxnN)) hg
  have hgt' : xm.1⁻¹ * g' ∈ X.SinfU u' :=
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u')).mul_mem (hNS u' (ninf_inv X u' hxmN)) hg'
  have hdect : t.pt.1 = (xn.1⁻¹ * g) * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm) *
      (xm.1⁻¹ * g')⁻¹ := by
    rw [hpt1, hdec]; group
  obtain ⟨μR, hPin, hform⟩ := Formalism.L2.SG.Pf.formTransp_pinned X Y u u' ν hν t
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' t hrel) _ hpt _ hgt _ hgt' hdect
  refine ⟨μR, hPin, ?_⟩
  rintro K ⟨hKm, hKu⟩
  have hFA := hform K hKm hKu

  have hmove := Formalism.L2.SG.Pf.RowForm.ClassFrameNormal.oo_map_mulLeft
    (ν (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm))) (X.Wu u) (X.Wu u')
    (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t₀.toTerm)) (xn.1⁻¹ * g) (xm.1⁻¹ * g')
    (X.psiInfU u xn.1⁻¹ * X.psiInfU u g) (X.psiInfU u' xm.1⁻¹ * X.psiInfU u' g') A B
    (wu_move X u xn.1 hxnN g hg) (wu_move X u' xm.1 hxmN g' hg')
  rw [hFA, hdect, hmove]
  rw [psi_inv X u hxnN, psi_inv X u' hxmN, map_mul, conj_inv_of_norm_one _ (psiInfU_norm X u' xm.1),
    ← Complex.coe_smul, smul_smul, smul_smul, hc0]
  congr 1
  ring

theorem coset_orbital_form : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ t₀ : TauC Y u u', t₀.relevant → t₀.G ≠ 0 → ∀ w, w = Formalism.L2.SG.PairVal.ptOf t₀.toTerm → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧ ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.completeSpace ℂ (X.Vpi u); OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w))‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (xn xm : X.B.I.GA), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → RatLink X xn n → RatLink X xm m → ∃ (μR : Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧ (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ K) ∧ OOt t = (((μR K).toReal : ℂ) * ((X.psiInfU u xn.1)⁻¹ * X.psiInfU u' xm.1)) • T := by
  intro D X Y u u' hSt ν hν t₀ hrel hG w hw
  obtain ⟨hw', T, hT, hform⟩ := coset_orbital_form_all D X Y u u' hSt ν hν t₀ hrel hG w hw
  refine ⟨hw', T, hT, ?_⟩
  intro t n m xn xm hn hxn hxm
  obtain ⟨μR, hPin, hK⟩ := hform t n m xn xm hn hxn hxm
  have hFund := Formalism.L2.SG.Pf.fundOf_transversal X Y u u' t
  exact ⟨μR, FundOf t, hPin, hFund, hK _ hFund⟩

end GlobalTheory.CosetOrbital
