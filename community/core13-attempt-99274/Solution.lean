import Mathlib
import Formalism.HermitianCurvature.Statement

open Finset Real NumberField Matrix FractionalIdeal InfinitePlace Formalism.FourierDecayAlt

noncomputable section
open scoped Classical

namespace AlpogeRHCore13

private lemma boxSumOne : BoxSumOne := by
  intro Kx hKx
  set p := (2⁻¹ : ℝ) ^ Kx
  set q := 4 * p
  have hq1 : q < 1 := by
    have h := rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num) hKx
    rw [rpow_two] at h; dsimp [q, p]; linarith
  refine ⟨128 / (1 - q), fun E _ _ _ b hb x hx hX S hS ↦ ?_⟩
  let W := InfinitePlace E
  set d := Fintype.card W
  set N : ℝ := (absNorm b : ℝ)
  have hNpos : 0 < N := by
    have h1 := congrArg absNorm $ mul_inv_cancel₀ hb
    have : 0 < absNorm b := (absNorm_nonneg b).lt_of_ne' fun h0 ↦ by simp [h0] at h1
    dsimp [N]
    exact_mod_cast this
  have hNle l (hlb : l ∈ b) (hl0 : l ≠ 0) : N ≤ ∏ w : W, w l ^ 2 := by
    obtain ⟨I, hI⟩ := le_one_iff_exists_coeIdeal.1 <|
      (mul_le_mul_right (spanSingleton_le_iff_mem.2 hlb) _).trans_eq $ inv_mul_cancel₀ hb
    have h1 : absNorm b * I.absNorm = |Algebra.norm ℚ l| := by
      rw [← coeIdeal_absNorm (K := E), hI, ← map_mul, mul_inv_cancel_left₀ hb, absNorm_span_singleton $ 𝓞 E]
    have h2 : (1 : ℚ) ≤ I.absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero $ Ideal.absNorm_eq_zero_iff.not.2 fun h ↦ by
        rw [h] at hI; simp [hb] at hI; exact hl0 $ spanSingleton_eq_zero_iff.1 hI
    simpa [N, ← Rat.cast_abs, ← prod_eq_abs_norm] using
      Rat.cast_le (K := ℝ).2 (by nlinarith [absNorm_nonneg b] : absNorm b ≤ |Algebra.norm ℚ l|)
  let kv l (w : W) := Nat.log 2 ⌊w l / x w⌋₊
  have hfib k (_ : k ∈ S.image kv) :
      ∑ l ∈ S with kv l = k, ∏ w, min 1 ((x w / w l) ^ Kx) ≤ 128 ^ d * ∏ w, q ^ (k w) := by
    let P := S.filter fun l ↦ kv l = k
    let ρ w := 2 ^ (k w + 1) * x w
    have hρ w : 0 < ρ w := by have := hx w; positivity
    set R := ∏ w, ρ w ^ 2
    have hP l (hl : l ∈ P) : l ∈ b ∧ l ≠ 0 ∧ ∀ w, w l < ρ w := by
      obtain ⟨hlS, rfl⟩ := mem_filter.1 hl
      refine ⟨(hS l hlS).1, (hS l hlS).2, fun w ↦ (div_lt_iff₀ $ hx w).1 ?_⟩
      have : (⌊w l / x w⌋₊ + 1 : ℝ) ≤ (2 : ℝ) ^ (kv l w + 1) := by
        exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two _
      linarith [Nat.lt_floor_add_one $ w l / x w]
    have hcard : (P.card : ℝ) ≤ 32 ^ d * R / N := by
      rcases P.eq_empty_or_nonempty with h | ⟨l₀, hl₀⟩
      rw [h]; simp; positivity
      set X := 2 ^ d * R / N
      set s := X ^ (((2 * d : ℕ) : ℝ)⁻¹)
      have hs1 : 1 ≤ s := one_le_rpow ((one_le_div hNpos).2 $ by
        have : ∏ w : W, w l₀ ^ 2 ≤ R := by dsimp [R]
                                           gcongr with w
                                           exact ((hP l₀ hl₀).2.2 w).le
        have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ one_le_two
        nlinarith [hNle l₀ (hP l₀ hl₀).1 (hP l₀ hl₀).2.1]) $ by positivity
      have hsX : s ^ (2 * d) = X := rpow_inv_natCast_pow (by positivity) $ by positivity
      set m := ⌈s⌉₊
      let δ w := ρ w / s
      have hδ w : 0 < δ w := div_pos (hρ w) $ by positivity
      let cd (z : ℂ) (t : Bool) := if t then z.re else z.im
      let f l (u : W × Bool) := ⌊cd (u.1.embedding l) u.2 / δ u.1⌋
      let T := Fintype.piFinset fun _ : W × Bool ↦ Ico (-(m : ℤ)) m
      have hmaps : Set.MapsTo f P T := fun l hlP ↦ Fintype.mem_piFinset.2 fun ⟨w, t⟩ ↦ mem_Ico.2 <| by
        have hlt' : |cd (w.embedding l) t / δ w| < s := by
          rw [abs_div, abs_of_pos $ hδ w, div_lt_iff₀ $ hδ w, mul_div_cancel₀ _ $ by positivity]
          refine lt_of_le_of_lt ?_ $ norm_embedding_eq w l ▸ (hP l $ mem_coe.1 hlP).2.2 w
          cases t <;> [exact Complex.abs_im_le_norm _; exact Complex.abs_re_le_norm _]
        have := abs_lt.1 hlt'
        have hm : s ≤ m := Nat.le_ceil s
        constructor <;> [apply Int.le_floor.2; apply Int.floor_lt.2] <;> (dsimp [f]; push_cast; linarith)
      have hinj : Set.InjOn f P := fun l hlP l' hlP' hfl ↦ by
        by_contra hne
        have hsub0 := sub_ne_zero.2 hne
        have hsmall w : w (l - l') ^ 2 < 2 * δ w ^ 2 := by
          have hd t : |cd (w.embedding l) t - cd (w.embedding l') t| < δ w := by
            have := Int.abs_sub_lt_one_of_floor_eq_floor $ congrFun hfl (w, t)
            rwa [← sub_div, abs_div, abs_of_pos $ hδ w, div_lt_one $ hδ w] at this
          have hre := abs_lt.1 $ hd true
          have him := abs_lt.1 $ hd false
          simp [cd] at hre him
          rw [← norm_embedding_eq, map_sub, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
          nlinarith
        obtain ⟨w₀, hw₀⟩ := univ_nonempty (α := W)
        have hlt : ∏ w : W, w (l - l') ^ 2 < ∏ w : W, (2 * δ w ^ 2) := by
          rw [← mul_prod_erase _ _ hw₀, ← mul_prod_erase _ _ hw₀]
          exact mul_lt_mul (hsmall w₀) (by gcongr with w; exact (hsmall w).le)
            (prod_pos fun w _ ↦ sq_pos_of_pos $ pos_iff.2 hsub0) $ by positivity
        have hprod : ∏ w : W, (2 * δ w ^ 2) = N := by
          have hR : R ≠ 0 := (prod_pos fun w _ ↦ sq_pos_of_pos $ hρ w).ne'
          simp [δ, prod_mul_distrib, prod_const, card_univ, div_pow, prod_div_distrib, ← pow_mul]
          change 2 ^ d * (R / s ^ (2 * d)) = N
          rw [hsX]
          dsimp [X]
          field_simp
        linarith [hNle (l - l') (Submodule.sub_mem (b : Submodule (𝓞 E) E) (hP l $ mem_coe.1 hlP).1 (hP l' $ mem_coe.1 hlP').1) hsub0]
      have hcard' : (P.card : ℝ) ≤ (2 * m) ^ (2 * d) := by
        have := card_le_card_of_injOn f hmaps hinj
        simp [T, Int.card_Ico, show (m : ℤ) - -(m : ℤ) = ↑(2 * m) by omega, mul_comm (Fintype.card W) 2] at this
        exact_mod_cast this
      refine (le_trans hcard' $ pow_le_pow_left₀ (by positivity)
        (show 2 * (m : ℝ) ≤ 4 * s by linarith [Nat.ceil_lt_add_one $ le_trans zero_le_one hs1]) _).trans_eq ?_
      rw [mul_pow, pow_mul 4, hsX]
      norm_num
      rw [show (32 : ℝ) = 16 * 2 by norm_num, mul_pow]; ring
    have hterm l (hl : l ∈ P) : ∏ w, min 1 ((x w / w l) ^ Kx) ≤ ∏ w, p ^ (k w) := by
      obtain ⟨hlS, rfl⟩ := mem_filter.1 hl
      gcongr with w
      intro w _; have := hx w; positivity
      have hwl : 0 < w l := pos_iff.2 (hS l hlS).2
      rcases eq_or_ne (kv l w) 0 with hk0 | hk0
      rw [hk0, pow_zero]; exact min_le_left _ _
      have h1 := (le_div_iff₀ $ hx w).1 $
        (by exact_mod_cast Nat.pow_log_le_self 2 (fun h ↦ hk0 $ by dsimp [kv]; rw [h, Nat.log_zero_right]) : (2 : ℝ) ^ kv l w ≤ ⌊w l / x w⌋₊).trans
          (Nat.floor_le (div_pos hwl $ hx w).le)
      rw [show p ^ kv l w = ((2⁻¹) ^ kv l w) ^ Kx by
        rw [← rpow_natCast, ← rpow_natCast $ 2⁻¹, ← rpow_mul $ by norm_num, ← rpow_mul $ by norm_num, mul_comm]]
      exact (min_le_right _ _).trans $ rpow_le_rpow (div_nonneg (hx w).le hwl.le) (by
        rw [inv_pow, ← one_div, div_le_div_iff₀ hwl $ by positivity]; linarith) $ by linarith
    have hid : R * ∏ w, p ^ (k w) = 4 ^ d * (∏ w, x w) ^ 2 * ∏ w, q ^ (k w) := by
      rw [← prod_mul_distrib]
      have hpt w : ρ w ^ 2 * p ^ (k w) = 4 * x w ^ 2 * q ^ (k w) := by
        dsimp [ρ, q]; rw [mul_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, pow_right_comm]; ring
      simp_rw [hpt, prod_mul_distrib, prod_const, card_univ, prod_pow]
      rfl
    refine ((by simpa using sum_le_card_nsmul _ _ _ hterm : ∑ l ∈ P, _ ≤ _).trans $
      mul_le_mul_of_nonneg_right hcard $ by positivity).trans ?_
    rw [div_mul_eq_mul_div, mul_assoc, hid, div_le_iff₀ hNpos, show (128 : ℝ) = 32 * 4 by norm_num, mul_pow]
    have hX2 := (pow_le_pow_left₀ (prod_nonneg fun w _ ↦ (hx w).le) hX 2).trans_eq $ sq_sqrt hNpos.le
    nlinarith [show 0 ≤ 32 ^ d * 4 ^ d * ∏ w, q ^ (k w) by positivity]
  rw [← sum_fiberwise_of_maps_to fun l hl ↦ mem_image_of_mem kv hl]
  set M := (S.image kv).sup (fun k ↦ univ.sup k) + 1
  have hsub : S.image kv ⊆ Fintype.piFinset fun _ : W ↦ range M := fun k hk ↦
    Fintype.mem_piFinset.2 fun i ↦ mem_range.2 $ Nat.lt_succ_of_le $ (le_sup $ mem_univ i).trans $ le_sup hk
  refine (sum_le_sum hfib).trans ?_
  rw [← mul_sum, show (128 / (1 - q)) ^ d = 128 ^ d * ∏ _w : W, (1 / (1 - q)) by simp [d, div_eq_mul_inv, mul_pow]]
  gcongr
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans ?_
  rw [← prod_univ_sum]; gcongr with _w
  simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := M) (by positivity) hq1

private lemma recursionSharp : RecursionSharp := by
  refine ⟨80, fun r a ε e σ ha ha2 hε hx he hσ hrec ↦ ?_⟩
  let Pp i := ∏ k ∈ Icc 1 i, √(1 + e k)
  have hPs k : Pp (k + 1) = Pp k * √(1 + e (k + 1)) := by simp [Pp, prod_Icc_succ_top $ Nat.le_add_left 1 k]
  have hgeom k : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) + 2 * a ^ (k + 1) ≤ 2 * a := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_Icc_succ_top $ by omega, show k + 1 + 1 - 1 = k + 1 by omega, pow_succ a $ k + 1]
      nlinarith [mul_le_mul_of_nonneg_left ha2 $ pow_nonneg ha $ k + 1]
  set ρ := 1 + ε + 2 * a
  have hgrow i : i ≤ r + 1 → σ i ≤ Pp i * ρ ^ i * σ 0 := by
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases i with _ | k
      simp [Pp]
      have h1 := hrec (k + 1) (by omega) hi
      rw [Nat.add_sub_cancel] at h1
      have hsum : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * σ (k + 1 - t) ≤ 2 * a * (Pp (k + 1) * ρ ^ k * σ 0) := by
        have := hσ 0
        trans (∑ t ∈ Icc 2 $ k + 1, a ^ (t - 1)) * (Pp (k + 1) * ρ ^ k * σ 0)
        rw [sum_mul]; gcongr with t ht
        have := mem_Icc.1 ht
        refine (ih (k + 1 - t) (by omega) $ by omega).trans ?_
        gcongr
        · exact (monotone_nat_of_le_succ fun k ↦ by
            rw [hPs]
            exact le_mul_of_one_le_right (by positivity) $ one_le_sqrt.2 $ by linarith [he $ k + 1]) $ by omega
        · linarith
        · omega
        gcongr
        linarith [hgeom k, pow_nonneg ha $ k + 1]
      have ihk := ih k (by omega) $ by omega
      rw [hPs] at hsum ⊢
      rw [pow_succ]
      nlinarith [mul_nonneg (show 0 ≤ 1 + ε by linarith) $ sqrt_nonneg $ 1 + e (k + 1)]
  set u := (r + 1) * (ε + a)
  have hu0 : 0 ≤ u := by positivity
  have hpb : (ρ ^ (r + 1)) ^ 2 ≤ 1 + 80 * u := by
    have h1 : (ρ ^ (r + 1)) ^ 2 ≤ exp u ^ 4 := by
      rw [show exp u ^ 4 = (exp (2 * (ε + a)) ^ (r + 1)) ^ 2 by
        rw [← exp_nat_mul, ← exp_nat_mul, ← exp_nat_mul]
        congr 1
        push_cast
        ring]
      gcongr
      linarith [add_one_le_exp $ 2 * (ε + a)]
    have h2 : exp u ≤ 1 + 2 * u := by have := exp_bound' hu0 hx one_pos
                                      simp at this
                                      linarith
    have : exp u ^ 4 ≤ (1 + 2 * u) ^ 4 := by gcongr
    have : (1 + 2 * u) ^ 2 ≤ 1 + 8 * u := by nlinarith
    nlinarith
  have hPQ : Pp (r + 1) ^ 2 = ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by
    simp [Pp, ← prod_pow]
    exact prod_congr rfl fun i _ ↦ sq_sqrt $ by linarith [he i]
  have hQ0 : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := prod_nonneg fun i _ ↦ by linarith [he i]
  refine (pow_le_pow_left₀ (hσ _) (hgrow _ le_rfl) 2).trans ?_
  rw [mul_pow, mul_pow, hPQ]
  nlinarith [mul_nonneg hQ0 $ sq_nonneg $ σ 0]

private lemma leadingMinorsCount : LeadingMinorsCount := by
  open Fin Fintype in
  intro K _ _ r
  let M a b := Matrix (Fin a) (Fin b) K
  let Lead n (C : M n n) := ∀ (j : ℕ) (hj : j ≤ n), (C.submatrix (castLE hj) $ castLE hj).det ≠ 0
  have hcm m n : card (Matrix (Fin m) (Fin n) K) = card K ^ (m * n) := by rw [card_congr of.symm]
                                                                          simp [← pow_mul, mul_comm]
  rw [Nat.card_eq_fintype_card, show card {C : M r r // Lead r C} =
      ∑ C : M r r, if Lead r C then 1 else 0 by rw [Fintype.card_subtype, card_filter]]
  induction r with
  | zero =>
    simp [M, hcm, show ∀ X : M 0 0, Lead 0 X from fun _ _ hj ↦ by obtain rfl := Nat.le_zero.1 hj; simp]
  | succ r ih =>
    let B (A : M r r) (v : M r 1) (u : M 1 r) (D : M 1 1) :=
      reindex finSumFinEquiv finSumFinEquiv $ fromBlocks A v u D
    let e0 : M (r + 1) (r + 1) ≃ M r r × M r 1 × M 1 r × M 1 1 :=
      { toFun := fun C ↦ let N := reindex finSumFinEquiv.symm finSumFinEquiv.symm C
      (N.toBlocks₁₁, N.toBlocks₁₂, N.toBlocks₂₁, N.toBlocks₂₂)
        invFun := fun ⟨A, v, u, D⟩ ↦ B A v u D
        left_inv := fun C ↦ by simp [B, fromBlocks_toBlocks]
        right_inv := fun ⟨A, v, u, D⟩ ↦ by simp [B] }
    have hlead A v u D : Lead (r + 1) (B A v u D) ↔ Lead r A ∧ (B A v u D).det ≠ 0 := by
      have hsm j (hj : j ≤ r) :
          (B A v u D).submatrix (castLE $ le_trans hj $ Nat.le_succ r) (castLE $ le_trans hj $ Nat.le_succ r) =
            A.submatrix (castLE hj) (castLE hj) := by
        ext i k
        have h (x : Fin j) : (finSumFinEquiv (m := r) (n := 1)) (Sum.inl $ castLE hj x) = castLE (le_trans hj $ Nat.le_succ r) x := by ext
                                                                                                                                       simp
        simp [B, ← h]
      refine ⟨fun h ↦ ⟨fun j hj ↦ hsm j hj ▸ h j _, by simpa using h (r + 1) le_rfl⟩, fun ⟨hA, hd⟩ j hj ↦ ?_⟩
      rcases lt_or_ge j (r + 1) with hlt | hge
      rw [hsm j $ Nat.lt_succ_iff.1 hlt]; exact hA j _
      obtain rfl := le_antisymm hj hge
      simpa using hd
    rw [sum_equiv e0 _ (fun p ↦ if Lead (r + 1) (B p.1 p.2.1 p.2.2.1 p.2.2.2) then 1 else 0)
      fun C ↦ by congr 2
                 exact (e0.left_inv C).symm]
    simp only [sum_prod_type]
    have hinner A v u : (∑ D : M 1 1, if Lead (r + 1) (B A v u D) then 1 else 0) =
        (if Lead r A then 1 else 0) * (card K - 1) := by
      dsimp [M] at A v u ⊢
      by_cases hA : Lead r A
      have hA0 : A.det ≠ 0 := by simpa using hA r le_rfl
      let _ := A.invertibleOfIsUnitDet hA0.isUnit
      have heq (D : Matrix (Fin 1) (Fin 1) K) : Lead (r + 1) (B A v u D) ↔ D ≠ u * ⅟A * v := by
        rw [hlead, and_iff_right hA, show (B A v u D).det = A.det * (D - u * ⅟A * v).det by simp [B, det_fromBlocks₁₁],
          mul_ne_zero_iff, and_iff_right hA0, det_fin_one, Matrix.sub_apply, sub_ne_zero, ne_eq, ne_eq, ← Matrix.ext_iff]
        simp
      simp only [heq, hA, ↓reduceIte, one_mul, ← card_filter, filter_ne', card_erase_of_mem $ mem_univ _, card_univ, hcm, mul_one, pow_one]
      simp [hlead, hA]
    simp only [hinner, M, Finset.sum_const, card_univ, hcm, mul_one, one_mul, smul_eq_mul, ← mul_sum, ← sum_mul, ih]
    rw [show (r + 1) ^ 2 - (r + 1) = r ^ 2 - r + r + r from Nat.sub_eq_of_eq_add $ by rw [Nat.sub_add_cancel $ Nat.le_self_pow two_ne_zero r]; ring,
      pow_add, pow_add, pow_succ]; ring

theorem hermitianCurvatureBounds :
    BoxSumOne ∧ RecursionSharp ∧ LeadingMinorsCount :=
  ⟨boxSumOne, recursionSharp, leadingMinorsCount⟩

end AlpogeRHCore13
