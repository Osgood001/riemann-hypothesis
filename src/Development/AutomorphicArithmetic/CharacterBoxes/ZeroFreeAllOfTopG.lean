module

public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV
public import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales
public import Development.AutomorphicArithmetic.PrimitiveCosets.Imports

@[expose] public section

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX

def TopG : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore) → FamilyClassConnected (G.cls la)

def TopGOn : Prop :=
  ∀ (P : ℝ → Prop) (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), P eps → G.cls la Fm → HypV Fm.toFamCore) →
      FamilyClassConnectedOn P (G.cls la)

theorem FReq.cls_whenEps {G : FReq} {P : ℝ → Prop} {eps la : ℝ} {Fm : FamP eps}
    (he : P eps) (h : (G.whenEps P).cls la Fm) : G.cls la Fm := by
  refine ⟨h.1, fun x hx i => h.2 x hx i ?_⟩
  rwa [Fm.L_eps x i]

/-- In the zero-free argument the arithmetic bound is used only for sufficiently small ε. -/
def TopGAt : Prop :=
  ∀ (δ la : ℝ) (G : FReq), 0 < δ → 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), eps < δ → G.cls la Fm → HypV Fm.toFamCore) →
      FamilyClassConnected (G.cls la)

theorem TopGOn.toTopGAt (h : TopGOn) : TopGAt := by
  intro δ la G hδ hla hH hV
  obtain ⟨eD, eL, η, hη, hF⟩ := h (· < δ) la G hla hH hV
  exact ⟨eD, eL, min δ η, lt_min hδ hη, fun eps hp hlt =>
    hF eps hp (hlt.trans_le (min_le_right _ _)) (hlt.trans_le (min_le_left _ _))⟩

theorem TopGAt.toTopG (h : TopGAt) : TopG :=
  fun la G hla hH hV => h 1 la G zero_lt_one hla hH (fun Fm _ => hV Fm)

theorem FReq.cls_of_below {G : FReq} {δ eps la : ℝ} {Fm : FamP eps} (he : eps < δ)
    (h : (G.below δ).cls la Fm) : G.cls la Fm := FReq.cls_whenEps he h

theorem hypV_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) : HypV Fm.toFamCore :=
  ⟨Fm.x1 + 1, fun x hx i => (h.2 x (by linarith) i).2⟩

theorem eFamC_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) :
    EFamC (Level.cyc ψ) Fm.toFamCore := by
  refine ⟨4, Fm.x1 + 1, fun x hx i => ?_⟩
  have h1 := (h.2 x (by linarith) i).1
  rw [Fm.L_x x i (by linarith), Fm.L_eps x i] at h1
  exact h1

theorem zeroFreeAll_of_topG {la : ℝ} (hla : 1 < la) (h : TopG) (hS : ∀ ψ : PChar, HostExW la (GChi ψ).req) : ZeroFreeAll := by
  have key : ZeroFreeOn fun _ => True :=
    zeroFreeOn_of_tiedWin_cyc (Fam := FamP) (core := fun Fm => Fm.toFamCore) (Tied := fun Fm => ChainTied Fm) hla
      (fun ψ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _) (fun ψ _ => UpperTheory.Comparison₂.formB _) fun ψ _ => by
        obtain ⟨eD, eL, ε₁, h1, h2⟩ := h la (GChi ψ) hla (hS ψ) (hypV_of_cls ψ la)
        refine ⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩
        obtain ⟨Fm, c, d⟩ := h2 eps a b
        exact ⟨Fm, eFamC_of_cls ψ la Fm c, c.1, d⟩
  exact key

private theorem cyclicLevel_of_connected_on {P : ℝ → Prop} {la : ℝ} (hla : 1 < la)
    (hP : ∀ η > (0 : ℝ), ∃ eps > (0 : ℝ), eps < η ∧ P eps) (ψ : PChar)
    (hFam : FamilyClassConnectedOn P (((GChi ψ).whenEps P).cls la)) : (Level.cyc ψ).ZeroFreeLevel := by
  obtain ⟨eD, eL, ε₁, h₁, hF⟩ := hFam
  intro ψ' hψ' s hs
  let Δ := min (s.re - 1 / 2) (1 / 2) / 2
  have hΔ : 0 < Δ := half_pos (lt_min (by linarith) (by norm_num))
  have h1 : Δ ≤ (s.re - 1 / 2) / 2 := by unfold Δ; gcongr; exact min_le_left _ _
  have h2 : Δ ≤ (1 / 2 : ℝ) / 2 := by unfold Δ; gcongr; exact min_le_right _ _
  have hA : 0 < |eD + eL + 7| + 1 := by positivity
  obtain ⟨eps, he, he', hE⟩ := hP (min ε₁ (Δ / (|eD + eL + 7| + 1))) (lt_min h₁ (div_pos hΔ hA))
  obtain ⟨he₁, he₂⟩ := lt_min_iff.mp he'
  obtain ⟨Fm, hc, ht⟩ := hF eps he he₁ hE
  have hC := FReq.cls_whenEps hE hc
  obtain ⟨x₀, hx⟩ := UpperTheory.Comparison₂.level_gm_le_on_family_scales (Level.cyc ψ) eD eL eps he Fm
    (eFamC_of_cls ψ la Fm hC) ht
  have hb : (eD + eL + 7) * eps ≤ Δ := calc
    _ ≤ (|eD + eL + 7| + 1) * eps := mul_le_mul_of_nonneg_right (by linarith [le_abs_self (eD + eL + 7)]) he.le
    _ ≤ Δ := by simpa only [mul_comm] using ((lt_div_iff₀ hA).mp he₂).le
  apply UpperTheory.Comparison₂.formB (Level.cyc ψ) la hla (1 / 2 + Δ) (by linarith) (by linarith) _ ψ' hψ' s (by linarith)
  apply ((windows_iff Fm.toFamCore la).mp hC.1).mono (x0 := max x₀ 1)
  intro y hy hw
  exact (hx y (le_of_max_le_left hy) hw).trans <|
    Real.rpow_le_rpow_of_exponent_le (le_of_max_le_right hy) (by linarith)

theorem cyclicLevel_of_coinitial_hosts {P : ℝ → Prop} {la : ℝ} (hla : 1 < la)
    (hTop : TopGOn) (hP : ∀ η > (0 : ℝ), ∃ eps > (0 : ℝ), eps < η ∧ P eps)
    (ψ : PChar) (hH : HostExW la ((GChi ψ).whenEps P).req) : (Level.cyc ψ).ZeroFreeLevel := by
  apply cyclicLevel_of_connected_on hla hP ψ
  exact hTop P la ((GChi ψ).whenEps P) hla hH fun Fm he hf => hypV_of_cls ψ la Fm (FReq.cls_whenEps he hf)

theorem cyclicLevel_zeroFree_of_topG_at {la δ : ℝ} (ψ : PChar) (hla : 1 < la) (h : TopGAt)
    (hδ : 0 < δ) (hH : HostExW la ((GChi ψ).below δ).req) : (Level.cyc ψ).ZeroFreeLevel := by
  refine cyclicLevel_of_connected_on (P := (· < δ)) hla ?_ ψ ?_
  · intro η hη
    exact ⟨min η δ / 2, half_pos (lt_min hη hδ), (half_lt_self (lt_min hη hδ)).trans_le (min_le_left _ _),
      (half_lt_self (lt_min hη hδ)).trans_le (min_le_right _ _)⟩
  · obtain ⟨eD, eL, ε₁, h₁, hF⟩ := h δ la ((GChi ψ).below δ) hδ hla hH
      fun Fm he hf => hypV_of_cls ψ la Fm (FReq.cls_of_below he hf)
    exact ⟨eD, eL, ε₁, h₁, fun eps hp hlt _ => hF eps hp hlt⟩

theorem zeroFreeAll_of_topG_at {la : ℝ} (hla : 1 < la) (h : TopGAt)
    (hS : ∀ ψ : PChar, ∃ δ > 0, HostExW la ((GChi ψ).below δ).req) : ZeroFreeAll := by
  intro ψ _
  obtain ⟨δ, hδ, hH⟩ := hS ψ
  exact cyclicLevel_zeroFree_of_topG_at ψ hla h hδ hH ψ (Level.mem_cyc ψ)

end UpperTheory.Top

end
