module

public import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm

@[expose] public section

open Formalism.HC UpperTheory.Top

namespace UpperTheory.Top

/-- The arithmetic output of a window, at the depth needed by its consumer. -/
structure WinDatumAt (ψ : PChar) (eps J c x Y : ℝ) (q d e : ℕ) (t : ℕ) : Prop where
  lo : x ^ (1 / J) ≤ Y
  up : Y ≤ x
  good : PairGood ψ.N eps Y x q d
  n_lo : x ^ (2 + 8 * eps) ≤ c * 2 ^ e
  n_up : c * 2 ^ e ≤ 2 * x ^ (2 + 8 * eps)
  bound : ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
    VVle E t (Real.sqrt (Real.exp (x ^ eps)))

end UpperTheory.Top

/-- Transport a character window to host scales once its cutoff eventually covers the
required depth under the field-order rescaling. -/
theorem UpperTheory.Top.winPairsForWidth (ψ : PChar) (eps c w la : ℝ) (cut need : ℝ → ℝ)
    (heps : 0 < eps) (hc : 1 ≤ c) (hla : 1 < la) (hlw : la < w) (hV : JointWindowAtWidth ψ eps w cut)
    (hdom : ∀ k : ℝ, 1 ≤ k → k ^ (2 + 8 * eps) = c →
      ∃ M : ℝ, ∀ x ≥ M, need (k * x) ≤ cut x) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ la →
      ∃ (Y : ℝ) (q d e : ℕ), WinDatumAt ψ eps J c x Y q d e ⌊need x⌋₊ := by
  obtain ⟨J, hJ, hX⟩ := hV
  have ha : 0 < 2 + 8 * eps := by linarith
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨k, hk1, hka⟩ : ∃ k : ℝ, 1 ≤ k ∧ k ^ (2 + 8 * eps) = c := by
    refine ⟨c ^ (1 / (2 + 8 * eps)), Real.one_le_rpow hc (one_div_nonneg.2 ha.le), ?_⟩
    rw [one_div, Real.rpow_inv_rpow hc0 ha.ne']
  have hk0 : 0 ≤ k := by linarith
  obtain ⟨B, hB⟩ := hdom k hk1 hka
  refine ⟨J, hJ, fun y => ?_⟩
  have hJ0 : J ≠ 0 := ne_of_gt (by linarith)
  have hJi : 0 ≤ 1 / J := one_div_nonneg.2 (by linarith)
  have hgap : 0 < w - la := sub_pos.mpr hlw
  let K := k ^ (la / (w - la))
  let M := max y (max B K)
  have hKM : K ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hM1 : 1 ≤ M := (Real.one_le_rpow hk1 (div_nonneg (zero_lt_one.trans hla).le hgap.le)).trans hKM
  have hyM : y ≤ M := le_max_left _ _
  have hBM : B ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨X, hXM, q, d, hpg, W, hW0, hWw, hWV⟩ := hX (M ^ J)
  have hM0 : 0 ≤ M := by linarith
  have hY0M : M ≤ X ^ (1 / J) := by
    calc M = (M ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hM0 hJ0]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hXM hJi
  have hWM : M ≤ W := hY0M.trans hW0
  have hW1 : 1 ≤ W := hM1.trans hWM
  have hWnn : 0 ≤ W := by linarith
  have hkW : k ^ la ≤ W ^ (w - la) := calc
    k ^ la = K ^ (w - la) := by rw [← Real.rpow_mul hk0, div_mul_cancel₀ _ hgap.ne']
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hk0 _) (hKM.trans hWM) hgap.le
  have hlem : (k * W) ^ la ≤ W ^ w := calc
    (k * W) ^ la = k ^ la * W ^ la := Real.mul_rpow hk0 hWnn
    _ ≤ W ^ (w - la) * W ^ la := mul_le_mul_of_nonneg_right hkW (Real.rpow_nonneg hWnn _)
    _ = W ^ w := by rw [← Real.rpow_add (zero_lt_one.trans_le hW1), sub_add_cancel]
  refine ⟨k * W, hyM.trans (hWM.trans (le_mul_of_one_le_left hWnn hk1)), fun x hZx hxZ => ?_⟩
  have hkpos : 0 < k := by linarith
  have hxWw : x ≤ W ^ w := hxZ.trans hlem
  have hxX : x ≤ X := hxWw.trans hWw
  have hx1 : W ≤ x := (le_mul_of_one_le_left hWnn hk1).trans hZx
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨x', rfl⟩ : ∃ x', x = k * x' := ⟨x / k, by field_simp⟩
  have hWx' : W ≤ x' := le_of_mul_le_mul_left hZx hkpos
  have hx'0 : 0 ≤ x' := hWnn.trans hWx'
  have hx'x : x' ≤ k * x' := le_mul_of_one_le_left hx'0 hk1
  obtain ⟨e, hpage, hv⟩ := hWV x' hWx' (hx'x.trans hxWw)
  have hpow : (k * x') ^ (2 + 8 * eps) = c * x' ^ (2 + 8 * eps) := by rw [Real.mul_rpow hk0 hx'0, hka]
  refine ⟨X ^ (1 / J), q, d, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.rpow_le_rpow hx0 hxX hJi
  · exact hW0.trans hx1
  · exact hpg.mono hxX
  · rw [hpow]
    exact mul_le_mul_of_nonneg_left hpage.1 hc0
  · rw [hpow]
    calc c * 2 ^ e ≤ c * (2 * x' ^ (2 + 8 * eps)) := mul_le_mul_of_nonneg_left hpage.2 hc0
      _ = 2 * (c * x' ^ (2 + 8 * eps)) := by ring
  · intro E _ _ hE
    refine (hv E hE).mono ?_ ?_
    · exact Nat.floor_mono (hB x' (hBM.trans (hWM.trans hWx')))
    · exact Real.sqrt_le_sqrt (Real.exp_le_exp.2 (Real.rpow_le_rpow hx'0 hx'x heps.le))

theorem UpperTheory.Top.winPairsFor (ψ : PChar) (eps c : ℝ) (cut : ℝ → ℝ → ℝ) (need : ℝ → ℝ)
    (heps : 0 < eps) (heps52 : eps < 1 / 52) (hc : 1 ≤ c) (hV : JointVWinFor ψ cut)
    (hdom : ∀ k : ℝ, 1 ≤ k → k ^ (2 + 8 * eps) = c →
      ∃ M : ℝ, ∀ x ≥ M, need (k * x) ≤ cut eps x) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
      ∃ (Y : ℝ) (q d e : ℕ), WinDatumAt ψ eps J c x Y q d e ⌊need x⌋₊ :=
  winPairsForWidth ψ eps c 2 (3 / 2) (cut eps) need heps hc (by norm_num) (by norm_num) (hV eps heps heps52) hdom

theorem UpperTheory.Top.winPairs_of_cofinal :
    ∀ (ψ : PChar) (eps c : ℝ), 0 < eps → eps < 1 / 52 → 1 ≤ c → CofinalVWinAt ψ 401 → PairEx →
      ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
        ∃ (Y : ℝ) (q d e : ℕ), WinDatum ψ eps J c x Y q d e := by
  intro ψ eps c heps heps52 hc hV hP
  have hdom (k : ℝ) (hk : 1 ≤ k) (_ : k ^ (2 + 8 * eps) = c) :
      ∃ M : ℝ, ∀ x ≥ M, (k * x) ^ (400 : ℝ) ≤ x ^ (401 : ℝ) := by
    refine ⟨max 1 (k ^ (400 : ℝ)), fun x hx => ?_⟩
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hx)
    rw [Real.mul_rpow (by linarith : 0 ≤ k) hx0.le, show (401 : ℝ) = 1 + 400 by norm_num,
      Real.rpow_add hx0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hx) (Real.rpow_nonneg hx0.le _)
  obtain ⟨J, hJ, hwin⟩ := winPairsFor ψ eps c (fun _ x => x ^ (401 : ℝ)) (fun x => x ^ (400 : ℝ))
    heps heps52 hc (CofinalVWinFor.toJoint hV hP) hdom
  refine ⟨J, hJ, fun y => ?_⟩
  obtain ⟨Z, hZ, h⟩ := hwin y
  refine ⟨Z, hZ, fun x hx hx' => ?_⟩
  obtain ⟨Y, q, d, e, w⟩ := h x hx hx'
  exact ⟨Y, q, d, e, w.lo, w.up, w.good, w.n_lo, w.n_up, w.bound⟩

theorem UpperTheory.Top.winPairs :
    ∀ (ψ : PChar) (eps c : ℝ), 0 < eps → eps < 1 / 52 → 1 ≤ c → VWinAt ψ 401 → PairEx →
      ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
        ∃ (Y : ℝ) (q d e : ℕ), WinDatum ψ eps J c x Y q d e :=
  fun ψ eps c he he' hc hV => winPairs_of_cofinal ψ eps c he he' hc hV.cofinal
