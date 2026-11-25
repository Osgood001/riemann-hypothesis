module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.FNil

/-! # Joint shifted collisions in the Hecke discriminant -/

@[expose] public section

namespace UpperTheory.V.Th

open Finset

private theorem linear_chain_pow_eq_zero {S : Type*} [CommRing S] {q x y z : S}
    {A B C k : ℕ} (hx : x ^ (A + 1) = 0) (hy : y ^ (B + 1) = 0)
    (hz : z ^ (C + 1) = 0) (h : A + B + C < 2 * k) :
    ((x - q * y) * (y - q * z)) ^ k = 0 := by
  classical
  rw [mul_pow, sub_eq_add_neg, sub_eq_add_neg, add_pow, add_pow, sum_mul]
  refine sum_eq_zero fun i hi => ?_
  rw [mul_sum]
  refine sum_eq_zero fun j hj => ?_
  have hi' : i ≤ k := Nat.le_of_lt_succ (mem_range.mp hi)
  have hj' : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
  have he :
      x ^ i * (-(q * y)) ^ (k - i) * (k.choose i : S) *
          (y ^ j * (-(q * z)) ^ (k - j) * (k.choose j : S)) =
      x ^ i * y ^ (k - i + j) * z ^ (k - j) *
          ((-q) ^ (k - i) * (-q) ^ (k - j) * (k.choose i : S) * (k.choose j : S)) := by
    rw [← neg_mul, ← neg_mul, mul_pow, mul_pow, pow_add]
    ring
  rw [he]
  by_cases ha : A < i
  · simp [pow_eq_zero_of_le (Nat.succ_le_of_lt ha) hx]
  by_cases hb : B < k - i + j
  · simp [pow_eq_zero_of_le (Nat.succ_le_of_lt hb) hy]
  have hc : C < k - j := by omega
  simp [pow_eq_zero_of_le (Nat.succ_le_of_lt hc) hz]

/-- Two consecutive shifted collisions may be counted together. The three deviations
need nilpotence bounds; the other roots are unrestricted. -/
theorem heckeDiscriminant_pow_of_shift_chain {S : Type*} [CommRing S] {n : ℕ} {q a : S}
    {U : Fin n → S} {i j l : Fin n} {A B C k : ℕ} (hij : i ≠ j) (hjl : j ≠ l)
    (hi : (U i - q * (q * a)) ^ (A + 1) = 0) (hj : (U j - q * a) ^ (B + 1) = 0)
    (hl : (U l - a) ^ (C + 1) = 0) (h : A + B + C < 2 * k) :
    heckeDiscriminant q U ^ k = 0 := by
  classical
  let row (i : Fin n) := ∏ j ∈ univ.erase i, (U i - U j) * (U i - q * U j)
  have divides (s t : Fin n) (hst : s ≠ t) : U s - q * U t ∣ row s :=
    (dvd_mul_left _ _).trans (dvd_prod_of_mem _ (mem_erase.mpr ⟨hst.symm, mem_univ _⟩))
  have hdiv : (U i - q * U j) * (U j - q * U l) ∣ heckeDiscriminant q U := by
    refine (mul_dvd_mul (divides _ _ hij) (divides _ _ hjl)).trans ?_
    simpa [row, heckeDiscriminant, hij] using
      prod_dvd_prod_of_subset {i, j} univ row (subset_univ _)
  have hzero := linear_chain_pow_eq_zero (q := q) hi hj hl h
  have e₁ : U i - q * (q * a) - q * (U j - q * a) = U i - q * U j := by ring
  have e₂ : U j - q * a - q * (U l - a) = U j - q * U l := by ring
  rw [e₁, e₂] at hzero
  exact zero_dvd_iff.mp (hzero ▸ pow_dvd_pow_of_dvd hdiv k)

noncomputable section

open MvPolynomial

/-- Each monomial obtained by choosing either endpoint of each ordered edge
has positive coefficient in the product with positive edge signs. -/
private theorem chain_coeff_pos (k u v : ℕ) (hu : u ≤ k) (hv : v ≤ k) :
    0 < (((X 0 + X 1) * (X 1 + X 2) : MvPolynomial (Fin 3) ℚ) ^ k).coeff
      (Finsupp.equivFunOnFinite.symm ![u, (k - u) + (k - v), v]) := by
  classical
  let a : Fin 3 → ℚ := ![1, 1, 0]
  let b : Fin 3 → ℚ := ![0, 1, 1]
  let e : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![u, k - u, 0]
  let f : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![0, k - v, v]
  have ha : (X 0 + X 1 : MvPolynomial (Fin 3) ℚ) = ∑ i, a i • X i := by
    simp [a, Fin.sum_univ_three]
  have hb : (X 1 + X 2 : MvPolynomial (Fin 3) ℚ) = ∑ i, b i • X i := by
    simp [b, Fin.sum_univ_three]
  have he : e.sum (fun _ j => j) = k := by
    simp [e, Finsupp.sum_of_support_subset e (Finset.subset_univ e.support), Fin.sum_univ_three,
      Nat.add_sub_of_le hu]
  have hf : f.sum (fun _ j => j) = k := by
    simp [f, Finsupp.sum_of_support_subset f (Finset.subset_univ f.support), Fin.sum_univ_three,
      Nat.sub_add_cancel hv]
  have hef : e + f = Finsupp.equivFunOnFinite.symm ![u, (k - u) + (k - v), v] := by
    ext i
    fin_cases i <;> simp [e, f]
  rw [← hef, mul_pow, ha, hb, coeff_mul]
  apply Finset.sum_pos'
  · rintro ⟨r, s⟩ _
    rw [coeff_linearCombination_X_pow_of_fintype, coeff_linearCombination_X_pow_of_fintype]
    have hnonneg (g : Fin 3 → ℚ) (v : Fin 3 →₀ ℕ) (hg : ∀ i, 0 ≤ g i) :
        0 ≤ (v.multinomial : ℚ) * v.prod (fun i n => g i ^ n) :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (hg i) _)
    apply mul_nonneg <;> split
    · exact hnonneg a r (by intro i; fin_cases i <;> norm_num [a])
    · exact le_rfl
    · exact hnonneg b s (by intro i; fin_cases i <;> norm_num [b])
    · exact le_rfl
  · refine ⟨(e, f), ?_, ?_⟩
    · simp
    · rw [coeff_linearCombination_X_pow_of_fintype, coeff_linearCombination_X_pow_of_fintype,
        ite_eq_left he, ite_eq_left hf, e.prod_fintype _ (fun _ => pow_zero _),
        f.prod_fintype _ (fun _ => pow_zero _), Fin.prod_univ_three, Fin.prod_univ_three]
      have he' : 0 < e.multinomial := Nat.multinomial_pos _ _
      have hf' : 0 < f.multinomial := Nat.multinomial_pos _ _
      simpa [a, b, e, f] using
        mul_pos (Nat.cast_pos.mpr he' : 0 < (e.multinomial : ℚ))
          (Nat.cast_pos.mpr hf' : 0 < (f.multinomial : ℚ))

private def shiftChainIdeal (N : Fin 3 → ℕ) : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span ((fun d => monomial d (1 : ℚ)) '' Set.range (fun i : Fin 3 => Finsupp.single i (N i)))

private abbrev ShiftTrunc (N : Fin 3 → ℕ) := MvPolynomial (Fin 3) ℚ ⧸ shiftChainIdeal N

private def truncChainX (N : Fin 3 → ℕ) (i : Fin 3) : ShiftTrunc N := Ideal.Quotient.mk _ (X i)

private theorem truncChainX_pow (N : Fin 3 → ℕ) (i : Fin 3) : truncChainX N i ^ N i = 0 := by
  rw [truncChainX, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, X_pow_eq_monomial]
  exact Ideal.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩

private theorem truncChain_mk_ne_zero_of_coeff {N : Fin 3 → ℕ}
    {p : MvPolynomial (Fin 3) ℚ} {d : Fin 3 →₀ ℕ}
    (hc : p.coeff d ≠ 0) (hd : ∀ i, d i < N i) :
    Ideal.Quotient.mk (shiftChainIdeal N) p ≠ 0 := by
  classical
  intro hz
  obtain ⟨_, ⟨i, rfl⟩, hle⟩ := mem_ideal_span_monomial_image.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    d (mem_support_iff.mpr hc)
  exact (Nat.not_le_of_lt (hd i)) (by simpa using hle i)

private theorem truncChain_product_ne_zero {A B C k : ℕ} (hk₁ : k ≤ A + B) (hk₂ : k ≤ B + C)
    (hk₃ : 2 * k ≤ A + B + C) :
    let N := ![A + 1, B + 1, C + 1]
    let x := truncChainX N
    ((x 0 + x 1) * (x 1 + x 2)) ^ k ≠ 0 := by
  dsimp only
  let u := min k A
  let v := min k C
  have hu : u ≤ k := min_le_left _ _
  have hv : v ≤ k := min_le_left _ _
  have hy : (k - u) + (k - v) ≤ B := by
    dsimp [u, v]
    omega
  have h := truncChain_mk_ne_zero_of_coeff (N := ![A + 1, B + 1, C + 1])
    (chain_coeff_pos k u v hu hv).ne' (show ∀ i : Fin 3,
      (Finsupp.equivFunOnFinite.symm ![u, (k - u) + (k - v), v]) i <
        (![A + 1, B + 1, C + 1] : Fin 3 → ℕ) i by
      intro i
      fin_cases i
      · simp [u]
      · simpa [u, v] using Nat.lt_succ_of_le hy
      · simp [v])
  simpa only [map_pow, map_mul, map_add, truncChainX] using h

private theorem isUnit_linear_lift {S : Type*} [CommRing S] [Algebra ℚ S]
    {q a b : ℚ} {x y : S} (hx : IsNilpotent x) (hy : IsNilpotent y) (h : a - q * b ≠ 0) :
    IsUnit (algebraMap ℚ S a + x - algebraMap ℚ S q * (algebraMap ℚ S b + y)) := by
  have hr :
      algebraMap ℚ S a + x - algebraMap ℚ S q * (algebraMap ℚ S b + y) =
        (x - algebraMap ℚ S q * y) + algebraMap ℚ S (a - q * b) := by
    rw [map_sub, map_mul]
    ring
  rw [hr]
  exact ((Commute.all _ _).isNilpotent_sub hx
    ((Commute.all _ _).isNilpotent_mul_left hy)).isUnit_add_right_of_commute
      (h.isUnit.map (algebraMap ℚ S)) (.all _ _)

private theorem isUnit_diff_lift {S : Type*} [CommRing S] [Algebra ℚ S]
    {a b : ℚ} {x y : S} (hx : IsNilpotent x) (hy : IsNilpotent y) (h : a ≠ b) :
    IsUnit (algebraMap ℚ S a + x - (algebraMap ℚ S b + y)) := by
  simpa using (isUnit_linear_lift (q := 1) hx hy (by simpa using sub_ne_zero.mpr h))

private theorem discr_three {S : Type*} [CommRing S] (q r s t : S) :
    heckeDiscriminant q ![r, s, t] =
      ((r - q * s) * (s - q * t)) *
        ((r - s) * (r - t) * (s - r) * (s - t) * (t - r) * (t - s) *
          (r - q * t) * (s - q * r) * (t - q * r) * (t - q * s)) := by
  have h0 : univ.erase (0 : Fin 3) = {1, 2} := by decide
  have h1 : univ.erase (1 : Fin 3) = {0, 2} := by decide
  have h2 : univ.erase (2 : Fin 3) = {0, 1} := by decide
  simp [heckeDiscriminant, Fin.prod_univ_three, h0, h1, h2, prod_insert]
  ring

private theorem discr_chain_ne_zero {A B C k : ℕ} (hk₁ : k ≤ A + B) (hk₂ : k ≤ B + C)
    (hk₃ : 2 * k ≤ A + B + C) :
    let N := ![A + 1, B + 1, C + 1]
    let X := truncChainX N
    heckeDiscriminant 2 ![4 + 4 * X 0, 2 + (-2) * X 1, 1 + X 2] ^ k ≠ 0 := by
  let N := ![A + 1, B + 1, C + 1]
  let S := ShiftTrunc N
  let X := truncChainX N
  let x : S := 4 * X 0
  let y : S := (-2) * X 1
  let z : S := X 2
  let r : S := 4 + x
  let s : S := 2 + y
  let t : S := 1 + z
  change heckeDiscriminant (2 : S) ![r, s, t] ^ k ≠ 0
  have hx : IsNilpotent x := ⟨N 0, by
    dsimp only [x, X]
    rw [mul_pow, truncChainX_pow N 0, mul_zero]⟩
  have hy : IsNilpotent y := ⟨N 1, by
    dsimp only [y, X]
    rw [mul_pow, truncChainX_pow N 1, mul_zero]⟩
  have hz : IsNilpotent z := ⟨N 2, truncChainX_pow N 2⟩
  have diff (a b : ℕ) (u v : S) (hu : IsNilpotent u) (hv : IsNilpotent v) (h : a ≠ b) :
      IsUnit ((a : S) + u - ((b : S) + v)) := by
    simpa using (isUnit_diff_lift (a := (a : ℚ)) (b := (b : ℚ)) hu hv (by exact_mod_cast h))
  have shift (a b : ℕ) (u v : S) (hu : IsNilpotent u) (hv : IsNilpotent v)
      (h : a ≠ 2 * b) : IsUnit ((a : S) + u - 2 * ((b : S) + v)) := by
    simpa [map_ofNat] using (isUnit_linear_lift (q := 2) (a := (a : ℚ)) (b := (b : ℚ)) hu hv
      (sub_ne_zero.mpr (by exact_mod_cast h)))
  have hrest : IsUnit ((r - s) * (r - t) * (s - r) * (s - t) * (t - r) * (t - s) *
      (r - 2 * t) * (s - 2 * r) * (t - 2 * r) * (t - 2 * s)) := by
    dsimp only [r, s, t]
    exact (diff 4 2 x y hx hy (by decide)).mul (diff 4 1 x z hx hz (by decide))
      |>.mul (diff 2 4 y x hy hx (by decide)) |>.mul (diff 2 1 y z hy hz (by decide))
      |>.mul (diff 1 4 z x hz hx (by decide)) |>.mul (diff 1 2 z y hz hy (by decide))
      |>.mul (shift 4 1 x z hx hz (by decide)) |>.mul (shift 2 4 y x hy hx (by decide))
      |>.mul (shift 1 4 z x hz hx (by decide)) |>.mul (shift 1 2 z y hz hy (by decide))
  have hlead : (r - 2 * s) * (s - 2 * t) =
      (-8 : S) * ((X 0 + X 1) * (X 1 + X 2)) := by
    dsimp only [r, s, t, x, y, z]
    ring
  have hunit : IsUnit (-8 : S) := by
    have hq : IsUnit (-8 : ℚ) := by norm_num
    simpa only [map_neg, map_ofNat] using hq.map (algebraMap ℚ S)
  rw [discr_three, hlead, mul_pow, ne_eq, (hrest.pow k).mul_left_eq_zero,
    mul_pow, (hunit.pow k).mul_right_eq_zero]
  exact truncChain_product_ne_zero hk₁ hk₂ hk₃

/-- Exact universal exponent for a rank-three shifted chain. The outer roots
and center may have different nilpotence bounds. Use the first, second or
both shifted factors, whichever yields the earliest vanishing. -/
theorem heckeDiscriminant_shift_chain_universal_pow_iff {A B C k : ℕ} :
    (∀ (S : Type) [CommRing S] (q a x y z : S), x ^ (A + 1) = 0 → y ^ (B + 1) = 0 →
      z ^ (C + 1) = 0 →
      heckeDiscriminant q ![q * (q * a) + x, q * a + y, a + z] ^ k = 0) ↔
    A + B < k ∨ B + C < k ∨ A + B + C < 2 * k := by
  constructor
  · intro h
    by_contra! hbad
    let N := ![A + 1, B + 1, C + 1]
    let X := truncChainX N
    have hh := h (ShiftTrunc N) 2 1 (4 * X 0) ((-2) * X 1) (X 2)
      (by simp [X, mul_pow, ← show N 0 = A + 1 by rfl, truncChainX_pow])
      (by simp [X, mul_pow, ← show N 1 = B + 1 by rfl, truncChainX_pow])
      (truncChainX_pow N 2)
    apply discr_chain_ne_zero hbad.1 hbad.2.1 hbad.2.2
    have hfour : (2 : ShiftTrunc N) * 2 = 4 := by norm_num
    simpa only [mul_one, hfour, X] using hh
  · intro h S _ q a x y z hx hy hz
    let U : Fin 3 → S := ![q * (q * a) + x, q * a + y, a + z]
    have hx' : (U 0 - q * (q * a)) ^ (A + 1) = 0 := by simpa [U] using hx
    have hy' : (U 1 - q * a) ^ (B + 1) = 0 := by simpa [U] using hy
    have hz' : (U 2 - a) ^ (C + 1) = 0 := by simpa [U] using hz
    rcases h with h | h | h
    · exact pow_eq_zero_of_le (by omega : A + 1 + (B + 1) - 1 ≤ k)
        (heckeDiscriminant_pow_of_shift (by decide : (0 : Fin 3) ≠ 1) hx' hy')
    · exact pow_eq_zero_of_le (by omega : B + 1 + (C + 1) - 1 ≤ k)
        (heckeDiscriminant_pow_of_shift (by decide : (1 : Fin 3) ≠ 2) hy' hz')
    · exact heckeDiscriminant_pow_of_shift_chain (by decide : (0 : Fin 3) ≠ 1)
        (by decide : (1 : Fin 3) ≠ 2) hx' hy' hz' h

/-- The exact common-order bound is `⌊3t/2⌋ + 1` when each deviation
vanishes to power `t+1`, versus the shifted-pair bound `2t+1`. -/
theorem heckeDiscriminant_shift_chain_uniform_pow_iff {t k : ℕ} :
    (∀ (S : Type) [CommRing S] (q a x y z : S), x ^ (t + 1) = 0 → y ^ (t + 1) = 0 →
      z ^ (t + 1) = 0 →
      heckeDiscriminant q ![q * (q * a) + x, q * a + y, a + z] ^ k = 0) ↔
    (3 * t) / 2 + 1 ≤ k := by
  rw [heckeDiscriminant_shift_chain_universal_pow_iff]
  omega

end

end UpperTheory.V.Th
