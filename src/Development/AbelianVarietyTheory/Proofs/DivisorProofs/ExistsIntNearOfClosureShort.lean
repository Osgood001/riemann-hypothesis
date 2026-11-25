module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.AbsTwoMulInnerLeOfNormSubEqInfDist

@[expose] public section

open scoped Matrix

namespace GlobalTheory.HSAmp

open Finset

theorem span_intCast_image_eq_top {ι : Type} [Fintype ι] [DecidableEq ι] (T : Set (ι → ℤ))
    (hT : AddSubgroup.closure T = ⊤) :
    Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T) = ⊤ := by
  have h : ∀ z : ι → ℤ, (fun i => (z i : ℝ)) ∈
      Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T) := by
    intro z
    have hz : z ∈ AddSubgroup.closure T := by rw [hT]; trivial
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero =>
      have : (fun i => (((0 : ι → ℤ) i : ℤ) : ℝ)) = 0 := by ext i; simp
      rw [this]; exact Submodule.zero_mem _
    | add u v _ _ hu hv =>
      have : (fun i => (((u + v) i : ℤ) : ℝ)) = (fun i => (u i : ℝ)) + fun i => (v i : ℝ) := by
        ext i; simp
      rw [this]; exact Submodule.add_mem _ hu hv
    | neg u _ hu =>
      have : (fun i => (((-u) i : ℤ) : ℝ)) = -(fun i => (u i : ℝ)) := by
        ext i; simp
      rw [this]; exact Submodule.neg_mem _ hu
  rw [eq_top_iff]
  intro x _
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have := h (fun j => if i = j then 1 else 0)
  convert this using 2 with j
  split_ifs <;> simp

/-- Spanning by integral vectors of quadratic length at most ρ gives the optimal
uniform covering radius √n · ρ / 2. The upper estimate does not require definiteness. -/
theorem exists_int_near_of_span_short {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (T : Set (ι → ℤ)) (ρ : ℝ)
    (hspanT : Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T) = ⊤)
    (hz : ∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) (x : ι → ℝ) :
    ∃ z : ι → ℤ, ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤
      (Real.sqrt (Fintype.card ι) * ρ / 2) ^ 2 := by
  classical
  set B : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toBilin' A with hB
  have hBq : ∀ v : ι → ℝ, ∑ i, ∑ j, A i j * v i * v j = B v v := by
    intro v
    rw [hB, Matrix.toBilin'_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨b, hbS, hspan, hli⟩ :=
    exists_linearIndependent ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T)
  rw [hspanT] at hspan
  have hfin : b.Finite := hli.setFinite
  let : Fintype b := hfin.fintype
  have hcard : Fintype.card b ≤ Fintype.card ι := by
    simpa using hli.fintype_card_le_finrank
  have hx : x ∈ Submodule.span ℝ (Set.range ((↑) : b → ι → ℝ)) := by
    rw [Subtype.range_coe, hspan]; trivial
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  choose w hwT hw using fun a : b => hbS a.2
  have hq : ∀ a : b, B a a ≤ ρ ^ 2 := by
    intro a
    rw [← hBq, ← hw a]
    exact hz _ (hwT a)
  obtain ⟨k, hk⟩ := GlobalTheory.exists_int_round_bilin B (fun a : b => (a : ι → ℝ)) t
  refine ⟨∑ a : b, k a • w a, ?_⟩
  have hy : (fun i => x i - ((∑ a : b, k a • w a) i : ℤ)) =
      ∑ a : b, (t a - k a) • (a : ι → ℝ) := by
    ext i
    rw [← ht]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
      ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    have hv : (w a i : ℝ) = (a : ι → ℝ) i := congrFun (hw a) i
    rw [hv]
    ring
  rw [hBq, hy]
  apply hk.trans
  calc _ ≤ ∑ _a : b, ρ ^ 2 / 4 := by
         refine sum_le_sum fun a _ => ?_
         let f := Int.fract (t a)
         have hf : 0 ≤ f * (1 - f) := mul_nonneg (Int.fract_nonneg _) (sub_nonneg.mpr (Int.fract_lt_one _).le)
         exact (mul_le_mul_of_nonneg_left (hq a) hf).trans
           (by nlinarith [mul_nonneg (sq_nonneg (f - 1 / 2)) (sq_nonneg ρ)])
       _ ≤ _ := by
         simp only [sum_const, card_univ, nsmul_eq_mul]
         rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
         have : (Fintype.card b : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
         nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg ρ)]

theorem exists_int_near_of_closure_short_sqrt (ι : Type) [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (T : Set (ι → ℤ)) (ρ : ℝ) (_hρ : 0 ≤ ρ) (hT : AddSubgroup.closure T = ⊤)
    (hz : ∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) (x : ι → ℝ) :
    ∃ z : ι → ℤ, ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤
      (Real.sqrt (Fintype.card ι) * ρ / 2) ^ 2 :=
  exists_int_near_of_span_short A T ρ (span_intCast_image_eq_top T hT) hz x

theorem exists_int_near_of_closure_short :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ : ℝ), 0 ≤ ρ → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → ∀ x : ι → ℝ, ∃ z : ι → ℤ, ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤ (Fintype.card ι * ρ) ^ 2 := by
  intro ι _ _ A _ T ρ hρ hT hz x
  obtain ⟨z, h⟩ := exists_int_near_of_closure_short_sqrt ι A T ρ hρ hT hz x
  refine ⟨z, h.trans ?_⟩
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hd : (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := by
    exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) (Fintype.card ι)
  nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg ρ), mul_nonneg (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _) (sq_nonneg ρ)]

end GlobalTheory.HSAmp
