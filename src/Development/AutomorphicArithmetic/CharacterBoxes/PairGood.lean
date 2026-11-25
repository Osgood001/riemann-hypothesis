module

public import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

@[expose] public section

noncomputable section

namespace UpperTheory.Top

open Formalism.HC

def tw (ξ : ℕ → ℂ) (q d : ℕ) (i j : Fin 2) (a : ℕ) : ℂ :=
  ξ a * ((jacobiSym (a : ℤ) q : ℤ) : ℂ) ^ (i : ℕ) * ((jacobiSym (a : ℤ) d : ℤ) : ℂ) ^ (j : ℕ)

def ZeroBox (Q : ℝ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0

def height (M : ℕ) (eps Y : ℝ) (j : Fin 2) : ℝ :=
  8 * M * Real.exp (Y ^ (eps / 5)) * Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) ^ (j : ℕ)

structure PairGood (M : ℕ) (eps Y X : ℝ) (q d : ℕ) : Prop where
  pair : WinPair eps Y q d
  coprime : Nat.Coprime M (q * d)
  bounds : ∀ (ξ : DirichletCharacter ℂ M) (i j : Fin 2), (i ≠ 0 ∨ j ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), An.Induces χ (tw (fun a => ξ (a : ZMod M)) q d i j) (2 * M * q * d) →
      ∀ y : ℝ, Y ≤ y → y ≤ X → ‖An.gChi χ y‖ ≤ y ^ ((1 : ℝ) / 2 + eps / 2) ∧ ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log y
  boxes : ∀ ρ : PChar, ρ.IsReal → ρ.N ∣ 8 * M → ∀ i j : Fin 2, (i ≠ 0 ∨ j ≠ 0) →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), An.Induces χ (tw ρ.val q d i j) (2 * M * q * d) →
      ZeroBox (height M eps Y j) χ

def PairEx : Prop :=
  ∀ (M : ℕ), 0 < M → ∀ eps A : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ A →
    ∃ Y1 : ℝ, ∀ Y ≥ Y1, ∃ q d : ℕ, PairGood M eps Y (Y ^ A) q d

def RealBox {φ : Frame} (H : HostRaw φ) : Prop :=
  ∀ ψ : PChar, H.IsCharE ψ.χ → ψ.IsReal → (H.q ∣ ψ.N ∨ H.d ∣ ψ.N) →
    ∀ β : ℝ, 1 - 1 / 400 < β → DirichletCharacter.LFunction ψ.χ β ≠ 0

def ThinH : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (φ : Frame) (H : HostRaw φ),
    ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ B → Real.log (H.condN : ℝ) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 → RealBox H →
      H.ChebyshevCharacterBound x eps c

theorem PairGood.mono {M : ℕ} {eps Y X X' : ℝ} {q d : ℕ} (h : PairGood M eps Y X q d) (hX : X' ≤ X) : PairGood M eps Y X' q d :=
  ⟨h.pair, h.coprime, fun ξ i j hij N _ χ hχ y a b => h.bounds ξ i j hij N χ hχ y a (b.trans hX), h.boxes⟩

/-- A jointly good character window at epsilon `eps`, of power width `w`. -/
def JointWindowAtWidth (ψ : PChar) (eps w : ℝ) (cut : ℝ → ℝ) : Prop :=
  ∃ J : ℝ, 1 ≤ J ∧
    ∀ A : ℝ, ∃ X ≥ A, ∃ q d : ℕ, PairGood ψ.N eps (X ^ (1 / J)) X q d ∧
      ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ w ≤ X ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ w →
        ∃ e : ℕ, PageN eps x e ∧ ∀ (E : Type) [Field E] [NumberField E],
          IsChiField ψ e q d E → VVle E ⌊cut x⌋₊ (Real.sqrt (Real.exp (x ^ eps)))

def JointWindowAt (ψ : PChar) (eps : ℝ) (cut : ℝ → ℝ) : Prop :=
  JointWindowAtWidth ψ eps 2 cut

/-- One prime pair at each retained scale suffices, provided it meets both the
arithmetic and the window conditions. These witnesses cannot be chosen separately. -/
def JointVWinFor (ψ : PChar) (cut : ℝ → ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → JointWindowAt ψ eps (cut eps)

/-- Only sufficiently small positive ε are needed for the analytic conclusion. -/
def JointVWinBelowWidth (ψ : PChar) (δ w : ℝ) (cut : ℝ → ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → eps < δ → JointWindowAtWidth ψ eps w (cut eps)

def JointVWinBelow (ψ : PChar) (δ : ℝ) (cut : ℝ → ℝ → ℝ) : Prop :=
  JointVWinBelowWidth ψ δ 2 cut

theorem JointVWinBelow.mono {ψ : PChar} {δ δ' : ℝ} {cut : ℝ → ℝ → ℝ}
    (h : JointVWinBelow ψ δ cut) (hle : δ' ≤ δ) : JointVWinBelow ψ δ' cut :=
  fun eps he he' hδ => h eps he he' (lt_of_lt_of_le hδ hle)

theorem JointVWinFor.below {ψ : PChar} {cut : ℝ → ℝ → ℝ} (h : JointVWinFor ψ cut) (δ : ℝ) :
    JointVWinBelow ψ δ cut := fun eps he he' _ => h eps he he'

theorem CofinalVWinFor.toJoint {ψ : PChar} {cut : ℝ → ℝ → ℝ}
    (hV : CofinalVWinFor ψ cut) (hP : PairEx) : JointVWinFor ψ cut := by
  intro eps he he'
  obtain ⟨J, hJ, hᵥ⟩ := hV eps he he'
  obtain ⟨Y₀, h₀⟩ := hP ψ.N (Nat.pos_of_ne_zero (NeZero.ne _)) eps J he he' hJ
  refine ⟨J, hJ, fun A => ?_⟩
  let B := max 1 Y₀
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hJ₀ : 0 < J := zero_lt_one.trans_le hJ
  obtain ⟨X, hX, hv⟩ := hᵥ (max A (B ^ J))
  have hBX := (le_max_right _ _).trans hX
  have hX₀ := (Real.rpow_nonneg hB J).trans hBX
  have hY : Y₀ ≤ X ^ (1 / J) := calc
    Y₀ ≤ B := le_max_right _ _
    _ = (B ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hB hJ₀.ne']
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hB _) hBX (one_div_nonneg.mpr hJ₀.le)
  obtain ⟨q, d, hp⟩ := h₀ _ hY
  have hpow : (X ^ (1 / J)) ^ J = X := by rw [one_div, Real.rpow_inv_rpow hX₀ hJ₀.ne']
  rw [hpow] at hp
  exact ⟨X, (le_max_left _ _).trans hX, q, d, hp, hv q d hp.pair⟩

/-- At depth zero, prime-pair existence supplies any power width greater than one. -/
theorem jointWindowAtWidth_zero (ψ : PChar) (eps w : ℝ) (he : 0 < eps) (he' : eps < 1 / 52)
    (hw : 1 < w) (hP : PairEx) : JointWindowAtWidth ψ eps w (fun _ => 0) := by
  obtain ⟨Y₀, h₀⟩ := hP ψ.N (Nat.pos_of_ne_zero (NeZero.ne _)) eps w he he' hw.le
  obtain ⟨e, hepage⟩ := exists_pageN eps he
  refine ⟨w, hw.le, fun A => ?_⟩
  let Y := max A (max 1 Y₀)
  have hY : 1 ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hAY : A ≤ Y ^ w := calc
    A ≤ Y := le_max_left _ _
    _ = Y ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ Y ^ w := Real.rpow_le_rpow_of_exponent_le hY hw.le
  obtain ⟨q, d, hp⟩ := h₀ Y ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨Y ^ w, hAY, q, d, ?_⟩
  rw [one_div, Real.rpow_rpow_inv (zero_le_one.trans hY) (zero_lt_one.trans hw).ne']
  refine ⟨hp, Y, le_rfl, le_rfl, fun x hx _ => ⟨e x, hepage x (hY.trans hx), ?_⟩⟩
  intro E _ _ _ Ω _ _ _ ld
  exact ⟨by simp, fun S => by simp⟩

theorem jointVWinFor_zero (ψ : PChar) (hP : PairEx) : JointVWinFor ψ (fun _ _ => 0) :=
  fun eps he he' => jointWindowAtWidth_zero ψ eps 2 he he' (by norm_num) hP

theorem JointVWinBelowWidth.extend {ψ : PChar} {δ w : ℝ} {cut : ℝ → ℝ → ℝ}
    (h : JointVWinBelowWidth ψ δ w cut) (hw : 1 < w) (hP : PairEx)
    (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) :
    JointWindowAtWidth ψ eps w (fun x => if eps < δ then cut eps x else 0) := by
  by_cases hδ : eps < δ
  · simpa [hδ] using h eps he he' hδ
  · simpa [hδ] using jointWindowAtWidth_zero ψ eps w he he' hw hP

theorem JointVWinBelow.extend {ψ : PChar} {δ : ℝ} {cut : ℝ → ℝ → ℝ} (h : JointVWinBelow ψ δ cut)
    (hP : PairEx) : JointVWinFor ψ (fun eps x => if eps < δ then cut eps x else 0) :=
  JointVWinBelowWidth.extend h (by norm_num) hP

end UpperTheory.Top

end
