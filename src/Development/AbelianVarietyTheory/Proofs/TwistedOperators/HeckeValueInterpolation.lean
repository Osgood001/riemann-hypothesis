module
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section
open Polynomial
namespace GridInterpolation

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/- Project both polynomials along one linear functional, normalized on the
   denominator at the target. The resulting cross products agree on the samples. -/
private noncomputable def projected (f : E →ₗ[K] K) (P : E[X]) : K[X] :=
  ∑ i ∈ Finset.range (P.natDegree + 1), monomial i (f (P.coeff i))

private theorem eval_projected (f : E →ₗ[K] K) (P : E[X]) (x : K) :
    (projected f P).eval x = f (P.eval (algebraMap K E x)) := by
  change (Polynomial.evalRingHom x) _ = _
  rw [projected, map_sum, Polynomial.eval_eq_sum_range (p := P), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (monomial i (f (P.coeff i))).eval x = _
  rw [Polynomial.eval_monomial, mul_comm (P.coeff i), ← map_pow, ← Algebra.smul_def, map_smul]
  simp [mul_comm]

private theorem projected_degree (f : E →ₗ[K] K) (P : E[X]) :
    (projected f P).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  exact fun i hi => (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- More than deg(P) + deg(Q) distinct base-field evaluations suffice to detect
base-field values everywhere away from poles. -/
theorem value_descends_of_samples (P Q : E[X]) (S : Finset K) (hS : P.natDegree + Q.natDegree < S.card)
    (h : ∀ x ∈ S, ∃ c : K, P.eval (algebraMap K E x) = c • Q.eval (algebraMap K E x))
    (x : K) (hx : Q.eval (algebraMap K E x) ≠ 0) :
    ∃ c : K, P.eval (algebraMap K E x) / Q.eval (algebraMap K E x) = algebraMap K E c := by
  let e := algebraMap K E
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hx
  let A := (projected f P).map e
  let B := (projected f Q).map e
  have heval (T : E[X]) (z : K) :
      ((projected f T).map e).eval (e z) = e (f (T.eval (e z))) := by
    rw [Polynomial.eval_map_apply, eval_projected]
  have he : P * B = Q * A := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (f := fun z : S => e z.val)
      ((FaithfulSMul.algebraMap_injective K E).comp Subtype.val_injective)
    · intro ⟨z, hz⟩
      obtain ⟨c, hc⟩ := h z hz
      change (P * B).eval (e z) = (Q * A).eval (e z)
      simp only [eval_mul, A, B, heval]
      rw [hc, map_smul]
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, map_mul, e]
      ring
    · have hA : A.natDegree ≤ P.natDegree := Polynomial.natDegree_map_le.trans (projected_degree f P)
      have hB : B.natDegree ≤ Q.natDegree := Polynomial.natDegree_map_le.trans (projected_degree f Q)
      rw [Fintype.card_coe]
      apply lt_of_le_of_lt (max_le _ _) hS
      · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left hB _)
      · exact Polynomial.natDegree_mul_le.trans ((Nat.add_le_add_left hA _).trans_eq (Nat.add_comm ..))
  refine ⟨f (P.eval (e x)), (div_eq_iff hx).mpr ?_⟩
  have hh := congrArg (Polynomial.eval (e x)) he
  change f (Q.eval (e x)) = 1 at hf
  simpa only [eval_mul, A, B, heval, hf, map_one, one_mul, mul_comm] using hh

theorem value_descends (P Q : E[X]) (S : Set K) (hS : S.Infinite)
    (h : ∀ x ∈ S, ∃ c : K, P.eval (algebraMap K E x) = c • Q.eval (algebraMap K E x))
    (x : K) (hx : Q.eval (algebraMap K E x) ≠ 0) :
    ∃ c : K, P.eval (algebraMap K E x) / Q.eval (algebraMap K E x) = algebraMap K E c := by
  obtain ⟨s, hs, hc⟩ := hS.exists_subset_card_eq (P.natDegree + Q.natDegree + 1)
  exact value_descends_of_samples P Q s (by omega) (fun z hz => h z (hs hz)) x hx

end GridInterpolation

noncomputable section
open Polynomial ComplexConjugate

namespace GlobalTheory.RelativeGrid

private theorem even_phase (z : ℂ) (hz : z ≠ 0) (b : ℤ) :
    (z / (‖z‖:ℂ)) ^ (2*b) = (z / conj z) ^ b := by
  rw [zpow_mul]
  congr 1
  rw [zpow_ofNat, div_pow]
  apply (div_eq_div_iff (pow_ne_zero _ (by exact_mod_cast norm_ne_zero_iff.mpr hz)) (by simpa using hz)).mpr
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  ring

private def factors (P Q : ℂ[X]) : ℤ → ℂ[X] × ℂ[X]
  | .ofNat n => (P^n,Q^n)
  | .negSucc n => (Q^(n+1),P^(n+1))

private theorem eval_factors (P Q : ℂ[X]) (t : ℂ) (hp : P.eval t ≠ 0) (hq : Q.eval t ≠ 0) (n : ℤ) :
    ((factors P Q n).1.eval t ≠ 0) ∧ ((factors P Q n).2.eval t ≠ 0) ∧
      (P.eval t / Q.eval t)^n = (factors P Q n).1.eval t / (factors P Q n).2.eval t := by
  cases n <;> simp [factors, hp, hq, div_pow, zpow_negSucc]

/-- A single pair of polynomials controls all nonzero rational points of
1+t*s. Both are nonvanishing there, even for negative or zero weights. -/
theorem arch_line_model {L I : Type*} [Field L] [CharZero L] [Fintype I]
    (φ : I → L →+* ℂ) (b : I → ℤ) (s : L) :
    ∃ P Q : ℂ[X], P.natDegree ≤ ∑ i, (b i).natAbs ∧ Q.natDegree ≤ ∑ i, (b i).natAbs ∧ ∀ (t : ℚ) (u : Lˣ), (u:L) = 1 + (t:L)*s →
      P.eval (t:ℂ) ≠ 0 ∧ Q.eval (t:ℂ) ≠ 0 ∧
      (∏ i, (φ i (u:L) / (‖φ i (u:L)‖:ℂ)) ^ (2*b i)) = P.eval (t:ℂ) / Q.eval (t:ℂ) := by
  let lin (z : ℂ) : ℂ[X] := 1 + C z * X
  let F i := factors (lin (φ i s)) (lin (conj (φ i s))) (b i)
  have hlin (z : ℂ) : (lin z).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp) (natDegree_mul_le.trans (by simp))
  have hp (z : ℂ) (n : ℕ) : (lin z ^ n).natDegree ≤ n := by
    simpa using natDegree_pow_le_of_le n (hlin z)
  have hd (i : I) : (F i).1.natDegree ≤ (b i).natAbs ∧ (F i).2.natDegree ≤ (b i).natAbs := by
    unfold F; cases b i <;> exact ⟨hp _ _, hp _ _⟩
  refine ⟨∏ i, (F i).1, ∏ i, (F i).2, ?_, ?_, ?_⟩
  · exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun i _ => (hd i).1))
  · exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun i _ => (hd i).2))
  intro t u hu
  have hv i : (lin (φ i s)).eval (t:ℂ) = φ i (u:L) := by
    rw [hu, map_add, map_one, map_mul, map_ratCast]
    simp only [lin, eval_add, eval_one, eval_mul, eval_C, eval_X]; ring
  have hw i : (lin (conj (φ i s))).eval (t:ℂ) = conj (φ i (u:L)) := by
    rw [← hv i]
    simp only [lin, eval_add, eval_one, eval_mul, eval_C, eval_X, map_add, map_one, map_mul, map_ratCast]
  have hf i := eval_factors (lin (φ i s)) (lin (conj (φ i s))) (t:ℂ)
    (hv i ▸ (_root_.map_ne_zero (φ i)).mpr u.ne_zero) (hw i ▸ (by simp [Units.ne_zero])) (b i)
  change (∏ i, (F i).1).eval _ ≠ _ ∧ (∏ i, (F i).2).eval _ ≠ _ ∧ _
  simp only [eval_prod]
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hf i).1),
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hf i).2.1), ?_⟩
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [even_phase _ ((_root_.map_ne_zero (φ i)).mpr u.ne_zero)]
  simpa only [hv, hw] using (hf i).2.2

/-- A common rational function for all invertible points on the affine line,
including the target at the inverse step size. -/
def RationalArchLine {L : Type*} [Field L] [CharZero L]
    (χ : Lˣ → ℂ) (k : Lˣ) (M D : ℕ) : Prop :=
  ∃ P Q : ℂ[X], P.natDegree ≤ D ∧ Q.natDegree ≤ D ∧
    (∀ (t : ℚ) (u : Lˣ), (u:L) = 1 + (t:L) * ((M:L)*((k:L)-1)) →
      P.eval (t:ℂ) ≠ 0 ∧ Q.eval (t:ℂ) ≠ 0 ∧ χ u = P.eval (t:ℂ) / Q.eval (t:ℂ)) ∧
    P.eval ((M:ℂ)⁻¹) ≠ 0 ∧ Q.eval ((M:ℂ)⁻¹) ≠ 0 ∧
      χ k = P.eval ((M:ℂ)⁻¹) / Q.eval ((M:ℂ)⁻¹)

theorem rationalArchLine_of_even_phase {L I : Type*} [Field L] [CharZero L] [Fintype I]
    (φ : I → L →+* ℂ) (b : I → ℤ) (χ : Lˣ → ℂ)
    (hχ : ∀ u : Lˣ, χ u = ∏ i, (φ i (u:L) / (‖φ i (u:L)‖:ℂ)) ^ (2*b i))
    (k : Lˣ) {M : ℕ} (hM : M ≠ 0) : RationalArchLine χ k M (∑ i, (b i).natAbs) := by
  obtain ⟨P,Q,hP,hQ,hPQ⟩ := arch_line_model φ b ((M:L)*((k:L)-1))
  have he (t : ℚ) (u : Lˣ) (hu : (u:L) = 1 + (t:L)*((M:L)*((k:L)-1))) :=
    (hPQ t u hu).imp_right (fun h => h.imp_right ((hχ u).trans ·))
  refine ⟨P,Q,hP,hQ,he,?_⟩
  have ht : (k:L) = 1 + (((M:ℚ)⁻¹:ℚ):L) * ((M:L)*((k:L)-1)) := by
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hM]; ring
  simpa using he (M:ℚ)⁻¹ k ht

end GlobalTheory.RelativeGrid
