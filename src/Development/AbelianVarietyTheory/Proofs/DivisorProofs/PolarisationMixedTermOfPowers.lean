module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory

theorem addMonoidHom_intCast_mul_real {A : Type} [CommRing A] (θ : A →+ ℝ) (k : ℤ) (z : A) :
    θ ((k : A) * z) = (k : ℝ) * θ z := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

private noncomputable def pencilPolynomial {R : Type} [CommRing R] (f : R →+ ℝ) (a b : R) (m : ℕ) : Polynomial ℝ :=
    ∑ i ∈ Finset.range (m + 1), Polynomial.C (f (a ^ i * b ^ (m - i)) * (m.choose i : ℝ)) * Polynomial.X ^ i

private theorem eval_pencilPolynomial {R : Type} [CommRing R] (f : R →+ ℝ) (a b : R) (m : ℕ) (t : ℤ) :
      (pencilPolynomial f a b m).eval (t : ℝ) = f (((t : R) * a + b) ^ m) := by
    rw [add_pow, map_sum]
    simp only [pencilPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro i _
    have step : ((t : R) * a) ^ i * b ^ (m - i) * (m.choose i : R) =
        ((t ^ i * (m.choose i : ℤ) : ℤ) : R) * (a ^ i * b ^ (m - i)) := by push_cast; ring
    rw [step, addMonoidHom_intCast_mul_real]
    push_cast
    ring

private theorem degree_pencilPolynomial {R : Type} [CommRing R] (f : R →+ ℝ) (a b : R) (m : ℕ) : (pencilPolynomial f a b m).natDegree ≤ m :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ hi =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

private theorem coeff_pencilPolynomial {R : Type} [CommRing R] (f : R →+ ℝ) (a b : R)
    (m k : ℕ) (hk : k ≤ m) : (pencilPolynomial f a b m).coeff k =
    f (a ^ k * b ^ (m - k)) * (m.choose k : ℝ) := by
  simp only [pencilPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Finset.sum_ite_eq, Finset.mem_range, ite_eq_left (Nat.lt_succ_of_le hk)]

open Polynomial in
/-- On a grid of `D + 1` distinct nodes whose sum is zero, evaluations determine
the coefficient of degree `D` even for polynomials of degree `D + 1`. -/
private theorem pencil_penultimate_coeff_eq {K : Type*} [Field K] {D : ℕ}
    (s : Fin (D + 1) ↪ K) (hs : ∑ i, s i = 0) (p q : K[X])
    (hp : p.natDegree ≤ D + 1) (hq : q.natDegree ≤ D + 1)
    (hv : ∀ i, p.eval (s i) = q.eval (s i)) : p.coeff D = q.coeff D := by
  classical
  let g : K[X] := ∏ i, (X - C (s i))
  have hd : g.natDegree = D + 1 := by simp [g]
  have hn : g.nextCoeff = 0 := by
    simp only [g, Monic.nextCoeff_prod _ _ (fun i _ => monic_X_sub_C (s i)), nextCoeff_X_sub_C,
      Finset.sum_neg_distrib, hs, neg_zero]
  have hc : g.coeff D = 0 := by simpa [nextCoeff, hd] using hn
  have hdiv : g ∣ p - q := Finset.prod_dvd_of_coprime
    (fun i _ j _ hij => pairwise_coprime_X_sub_C s.injective hij)
    (fun i _ => dvd_iff_isRoot.mpr (by simpa [IsRoot] using sub_eq_zero.mpr (hv i)))
  have he := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (show g.Monic from monic_prod_X_sub_C s Finset.univ) hdiv
    (by rw [hd]; exact (natDegree_sub_le p q).trans (max_le hp hq))
  apply sub_eq_zero.mp
  simpa [coeff_C_mul, hc] using congrArg (fun f : K[X] => f.coeff D) he


/-- The `D + 1` distinct integer weights `-D, -D + 2, …, D` sum to zero. -/
def centeredPencilWeights (D : ℕ) : Fin (D + 1) ↪ ℤ where
  toFun i := 2 * (i : ℤ) - D
  inj' := by
    intro i j h
    apply Fin.ext
    change 2 * (i.val : ℤ) - D = 2 * (j.val : ℤ) - D at h
    omega

theorem sum_centeredPencilWeights (D : ℕ) : ∑ i, centeredPencilWeights D i = 0 := by
  have h (i : Fin (D + 1)) :
      centeredPencilWeights D (Fin.revPerm i) = -centeredPencilWeights D i := by
    change 2 * ((Fin.rev i).val : ℤ) - D = -(2 * (i.val : ℤ) - D)
    simp only [Fin.val_rev]
    have hi := i.isLt
    omega
  have e := Equiv.sum_comp (Fin.revPerm (n := D + 1)) (fun i => centeredPencilWeights D i)
  simp only [h, Finset.sum_neg_distrib] at e
  omega

/-- Agreement at `D+1` centered weights suffices for the term with one copy of
`x`. Its binomial coefficient occurs one below the top degree in `(x+t*y)^(D+1)`. -/
theorem first_mixed_power_of_zero_sum_pencil {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+ ℝ) (ψ : B →+ ℝ) (x y : A) (u v : B) (D : ℕ) (s : Fin (D + 1) ↪ ℤ)
    (hs : ∑ i, s i = 0)
    (h : ∀ i, φ ((x + (s i : A) * y) ^ (D + 1)) = ψ ((u + (s i : B) * v) ^ (D + 1))) :
    φ (x * y ^ D) = ψ (u * v ^ D) := by
  let t : Fin (D + 1) ↪ ℝ := s.trans ⟨Int.cast, Int.cast_injective⟩
  have ht : ∑ i, t i = 0 := by
    change ∑ i, (s i : ℝ) = 0
    exact_mod_cast hs
  have sample (i) : (pencilPolynomial φ y x (D + 1)).eval (t i) =
      (pencilPolynomial ψ v u (D + 1)).eval (t i) := by
    change (pencilPolynomial φ y x (D + 1)).eval (s i : ℝ) =
      (pencilPolynomial ψ v u (D + 1)).eval (s i : ℝ)
    simpa only [eval_pencilPolynomial, add_comm] using h i
  have hc := pencil_penultimate_coeff_eq t ht _ _ (degree_pencilPolynomial φ y x (D + 1))
    (degree_pencilPolynomial ψ v u (D + 1)) sample
  simp only [coeff_pencilPolynomial _ _ _ (D + 1) D (Nat.le_succ D), Nat.add_sub_cancel_left,
    pow_one] at hc
  simpa only [mul_comm x, mul_comm u] using mul_right_cancel₀
    (by exact_mod_cast (Nat.choose_pos (Nat.le_succ D)).ne') hc

/-- Agreement on `m+1` distinct diagonal powers on a pencil determines all of its
mixed powers, not just the term that is linear in the first direction. -/
theorem mixed_powers_of_pencil {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+ ℝ) (ψ : B →+ ℝ) (x y : A) (u v : B) (m : ℕ) (s : Fin (m + 1) ↪ ℤ)
    (h : ∀ i, φ (((s i : A) * x + y) ^ m) = ψ (((s i : B) * u + v) ^ m))
    (k : ℕ) (hk : k ≤ m) : φ (x ^ k * y ^ (m - k)) = ψ (u ^ k * v ^ (m - k)) := by
  have eqP : pencilPolynomial φ x y m = pencilPolynomial ψ u v m := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (Int.cast_injective.comp s.injective)
    · intro i
      simpa only [Function.comp_apply, eval_pencilPolynomial] using h i
    · simpa using Nat.lt_succ_of_le (max_le (degree_pencilPolynomial φ x y m)
        (degree_pencilPolynomial ψ u v m))
  have c := congrArg (fun p : Polynomial ℝ => p.coeff k) eqP
  simp only [coeff_pencilPolynomial _ _ _ _ k hk] at c
  exact mul_right_cancel₀ (by exact_mod_cast (Nat.choose_pos hk).ne') c

open Polynomial in
/-- Fewer than `m + 1` polynomial probes cannot determine the values of an arbitrary
additive measurement on all the first `m + 1` monomials. -/
theorem exists_measurement_vanishing_on_probes {m r : ℕ} (hr : r ≤ m)
    (p : Fin r → ℝ[X]) :
    ∃ φ : ℝ[X] →+ ℝ, (∀ j, φ (p j) = 0) ∧ ∃ i : Fin (m + 1), φ (Polynomial.X ^ (i : ℕ)) ≠ 0 := by
  let T : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
    LinearMap.pi fun j => ∑ i : Fin (m + 1), (p j).coeff i • LinearMap.proj i
  have hn : LinearMap.ker T ≠ ⊥ := by
    intro he
    have hd := T.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp he)
    simp at hd
    omega
  obtain ⟨a, ha, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let L : ℝ[X] →ₗ[ℝ] ℝ := ∑ i : Fin (m + 1), a i • Polynomial.lcoeff ℝ i
  refine ⟨L.toAddMonoidHom, ?_, ?_⟩
  · intro j
    simpa [L, T, mul_comm] using congrFun (LinearMap.mem_ker.mp ha) j
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨i, ?_⟩
    simpa [L, Polynomial.coeff_X_pow, ← Fin.ext_iff] using hi

open MvPolynomial

/-- For a fixed bundle combination, the nonnegative parameters `0,…,m`
recover every mixed coefficient of the degree-`m` pencil. -/
theorem polarisation_mixed_terms_on_pencil (A : Type) [CommRing A] (θ : A →+ ℝ)
    (ι : Type) [Fintype ι] (x : Option ι → A) (m : ℕ)
    (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ) (n : ι → ℤ)
    (h : ∀ i : Fin (m + 1), let r : Option ι → ℤ := fun o => o.elim i.val n
      Φ (lin (fun o => (r o : ℝ)) ^ m) = θ ((∑ o, r o • x o) ^ m))
    (k : ℕ) (hk : k ≤ m) :
    Φ (MvPolynomial.X none ^ k * rename some (lin fun i => (n i : ℝ)) ^ (m - k)) =
      θ (x none ^ k * (∑ i, n i • x (some i)) ^ (m - k)) := by
  let L := rename some (lin fun i => (n i : ℝ))
  let y := ∑ i, n i • x (some i)
  let s : Fin (m + 1) ↪ ℤ := ⟨fun i => i.val, fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
  have test (i : Fin (m + 1)) :
      Φ (((s i : MvPolynomial (Option ι) ℝ) * MvPolynomial.X none + L) ^ m) =
        θ (((s i : A) * x none + y) ^ m) := by
    change Φ ((((i.val : ℤ) : MvPolynomial (Option ι) ℝ) * MvPolynomial.X none + L) ^ m) =
      θ ((((i.val : ℤ) : A) * x none + y) ^ m)
    simpa [L, y, lin, Fintype.sum_option, zsmul_eq_mul, map_sum] using
      h i
  exact mixed_powers_of_pencil Φ.toAddMonoidHom θ (MvPolynomial.X none) L (x none) y m s test k hk

/-- The mixed-height induction only needs one distinguished factor, so it suffices
to test the `D+1` centered weights on the other bundle combination. -/
theorem polarisation_first_mixed_term_on_centered_pencil (A : Type) [CommRing A] (θ : A →+ ℝ)
    (ι : Type) [Fintype ι] (x : Option ι → A) (D : ℕ)
    (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ) (n : ι → ℤ)
    (h : ∀ i : Fin (D + 1), let r : Option ι → ℤ := fun o => o.elim 1 (fun j => centeredPencilWeights D i * n j)
      Φ (lin (fun o => (r o : ℝ)) ^ (D + 1)) = θ ((∑ o, r o • x o) ^ (D + 1))) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
      θ ((∑ i, n i • x (some i)) ^ D * x none) := by
  let L := rename some (lin fun i => (n i : ℝ))
  let y := ∑ i, n i • x (some i)
  have test (i : Fin (D + 1)) :
      Φ ((MvPolynomial.X none + (centeredPencilWeights D i : MvPolynomial (Option ι) ℝ) * L) ^ (D + 1)) =
        θ ((x none + (centeredPencilWeights D i : A) * y) ^ (D + 1)) := by
    simpa [L, y, lin, Fintype.sum_option, zsmul_eq_mul, map_sum, Finset.mul_sum, mul_assoc] using h i
  simpa [L, y, mul_comm] using first_mixed_power_of_zero_sum_pencil Φ.toAddMonoidHom θ
    (MvPolynomial.X none) L (x none) y D (centeredPencilWeights D) (sum_centeredPencilWeights D) test

theorem polarisation_mixed_term_of_powers : ∀ (A : Type) [CommRing A] (θ : A →+ ℝ) (ι : Type) [Fintype ι] (x : Option ι → A) (D : ℕ) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), (∀ n : Option ι → ℤ, Φ (lin (fun o => (n o : ℝ)) ^ (D + 1)) = θ ((∑ o, n o • x o) ^ (D + 1))) → ∀ n : ι → ℤ, Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = θ ((∑ i, n i • x (some i)) ^ D * x none) := by
  intro A _ θ ι _ x D Φ h n
  simpa [mul_comm] using polarisation_mixed_terms_on_pencil A θ ι x (D + 1) Φ n
    (fun i => h (fun o => o.elim i.val n)) 1 (Nat.succ_pos D)

end GlobalTheory
