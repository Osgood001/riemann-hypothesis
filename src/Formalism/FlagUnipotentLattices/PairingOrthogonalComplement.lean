module

public import Mathlib
public import Formalism.SobolevGaussianKernels.StatementEI

@[expose] public section

namespace Formalism.HermitianLatticeCounting.S4

open Finset
open Formalism.SL.IwahoriBlocks (IsHerm eich)

section defs
variable {E : Type*} [CommRing E] [StarRing E] {V : Type*} [AddCommGroup V] [Module E V]

end defs

def ValuationProductBound : Prop :=
  ∀ (B : Type) [Fintype B] (s : B → ℕ) (vh ve vt : B → ℝ) (q A : ℝ) (r : ℕ),
    1 ≤ q → (∀ b, 1 ≤ s b ∧ s b ≤ r + 1) → (∀ b, 0 ≤ vh b) → (∀ b, 0 ≤ ve b) →
    (∀ b, (s b : ℝ) * vt b = ve b - vh b) → ∑ b, vh b ≤ A → ∑ b, ve b ≤ A →
    ∏ b, q ^ (2 * (s b : ℝ) * vh b) ≤ (q ^ A) ^ (2 * ((r : ℝ) + 1)) ∧
    ∏ b, q ^ (vt b * ((s b : ℝ) * ((s b : ℝ) - 1) / 2)) ≤ (q ^ A) ^ (((r : ℝ) + 1) / 2)

section herm
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [StarRing E]

end herm

def LocalDensityShareBound : Prop :=
  ∀ (Ov : Type) [Fintype Ov] (dens dl : Ov → ℝ) (κ be disc tot : ℝ) (k r : ℕ),
    1 ≤ k → 0 ≤ κ → 1 ≤ be → (Fintype.card Ov : ℝ) ≤ disc ^ (2 * r + 2) →
    (∀ M, dens M = κ * ((be ^ (k + 2 * r + 1))⁻¹ / (be ^ (2 * r + 2))⁻¹) * dl M) →
    (∀ M, dl M ≤ 2) → κ / 2 ≤ tot →
    ∑ M, dens M ≤ 4 * disc ^ (2 * r + 2) * (be ^ (k - 1))⁻¹ * tot

def WeightedCS : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : Type) [SeminormedAddCommGroup V] (v : ι → V) (W : ι → ℝ),
    (∀ i, 0 < W i) → ‖∑ i, v i‖ ^ 2 ≤ (∑ i, (W i)⁻¹) * ∑ i, W i * ‖v i‖ ^ 2

def OmCount : Prop :=
  ∀ (P : Type) (Om : Finset P) (H : P → ℝ), (∀ p ∈ Om, 2 ≤ H p) → (2 : ℝ) ^ Om.card ≤ ∏ p ∈ Om, H p

def Step4 : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P] (Om : Finset P) (D : P → Type) [∀ p, Fintype (D p)]
    (w : ∀ p, D p → ℝ) (aN aZ : ∀ p, D p → ℂ) (H nn ngen : P → ℝ) (q : P → ℕ) (c κ : ℕ),
    (∀ p d, 0 ≤ w p d) → (∀ p, 1 ≤ H p) → (∀ p, 2 ≤ q p) → (∀ p, 0 ≤ nn p) →
    (∀ p ∈ Om, ∑ d, w p d * ‖aN p d‖ ^ 2 ≤ H p ^ c * ((q p : ℝ) ^ κ)⁻¹ * nn p) →
    (∀ p, ∑ d, w p d * ‖aZ p d‖ ^ 2 ≤ H p ^ c * nn p) →
    (∀ p, nn p ≤ H p ^ c * ngen p) →
    ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
        ‖∑ A ∈ Om.powerset.filter (fun A => A.Nonempty),
            ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
      ≤ (4 : ℝ) ^ Om.card * (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p


private theorem weighted_minkowski_sq {I J : Type*} [Fintype J] (s : Finset I)
    (w : J → ℝ) (hw : ∀ d, 0 ≤ w d) (v : I → J → ℂ) (z : I → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i)
    (h : ∀ i ∈ s, ∑ d, w d * ‖v i d‖ ^ 2 ≤ z i ^ 2) :
    ∑ d, w d * ‖∑ i ∈ s, v i d‖ ^ 2 ≤ (∑ i ∈ s, z i) ^ 2 := by
  classical
  let W (v : J → ℂ) : EuclideanSpace ℂ J :=
    WithLp.toLp 2 (fun d => (Real.sqrt (w d) : ℂ) * v d)
  have normW (v : J → ℂ) : ‖W v‖ ^ 2 = ∑ d, w d * ‖v d‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply sum_congr rfl
    intro d _
    simp [W, mul_pow, Real.sq_sqrt (hw d)]
  have hsum : W (fun d => ∑ i ∈ s, v i d) = ∑ i ∈ s, W (v i) := by
    apply WithLp.ofLp_injective
    rw [WithLp.ofLp_sum]
    ext d
    simp [W, mul_sum]
  rw [← normW, hsum]
  apply (sq_le_sq₀ (norm_nonneg _) (sum_nonneg hz)).mpr
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
  exact (sq_le_sq₀ (norm_nonneg _) (hz i hi)).mp ((normW (v i)).le.trans (h i hi))

private theorem sum_nonempty_products {P : Type*} (s : Finset P) (x : P → ℝ) :
    ∑ A ∈ s.powerset.filter (fun A => A.Nonempty), ∏ p ∈ A, x p =
      (∏ p ∈ s, (1 + x p)) - 1 := by
  classical
  rw [prod_one_add, eq_sub_iff_add_eq]
  simp [show s.powerset.filter (fun A => A.Nonempty) = s.powerset.erase ∅ by
    ext; simp [Finset.nonempty_iff_ne_empty, and_comm]]

/-- Sharp squared-norm bound for the sum of all nonempty defect patterns, retaining
the damping factor at every exceptional place. -/
theorem defect_mass_le {P : Type*} [Fintype P] [DecidableEq P] (Om : Finset P)
    (D : P → Type*) [∀ p, Fintype (D p)] (w : ∀ p, D p → ℝ)
    (aN aZ : ∀ p, D p → ℂ) (B t : P → ℝ)
    (hw : ∀ p x, 0 ≤ w p x) (hB : ∀ p, 0 ≤ B p) (ht : ∀ p ∈ Om, 0 ≤ t p)
    (hN : ∀ p ∈ Om, ∑ x, w p x * ‖aN p x‖ ^ 2 ≤ B p * t p ^ 2)
    (hZ : ∀ p, ∑ x, w p x * ‖aZ p x‖ ^ 2 ≤ B p) :
    ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
        ‖∑ A ∈ Om.powerset.filter (fun A => A.Nonempty),
            ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2 ≤
      (∏ p, B p) * ((∏ p ∈ Om, (1 + t p)) - 1) ^ 2 := by
  classical
  let v (A : Finset P) (d : ∀ p, D p) := ∏ p, if p ∈ A then aN p (d p) else aZ p (d p)
  let W (d : ∀ p, D p) := ∏ p, w p (d p)
  let z (A : Finset P) := Real.sqrt (∏ p, B p) * ∏ p ∈ A, t p
  have hB0 := Finset.prod_nonneg (s := univ) fun p _ => hB p
  have one (A : Finset P) (hA : A ⊆ Om) : ∑ d, W d * ‖v A d‖ ^ 2 ≤ z A ^ 2 := by
    calc ∑ d, W d * ‖v A d‖ ^ 2 =
        ∏ p, ∑ x : D p, w p x * ‖if p ∈ A then aN p x else aZ p x‖ ^ 2 := by
          rw [prod_univ_sum, Fintype.piFinset_univ]
          apply sum_congr rfl
          intro d _
          simp [W, v, norm_prod, prod_pow, prod_mul_distrib]
      _ ≤ ∏ p, B p * (if p ∈ A then t p ^ 2 else 1) := by
        refine prod_le_prod₀ (fun p _ => sum_nonneg fun x _ => mul_nonneg (hw p x) (sq_nonneg _))
          (fun p _ => ?_)
        by_cases hp : p ∈ A
        · simpa only [ite_eq_left hp] using hN p (hA hp)
        · simpa only [ite_eq_right hp, mul_one] using hZ p
      _ = z A ^ 2 := by rw [prod_mul_distrib, Fintype.prod_ite_mem]; simp only [z, prod_pow, mul_pow, Real.sq_sqrt hB0]
  calc _ ≤ (∑ A ∈ Om.powerset.filter (fun A => A.Nonempty), z A) ^ 2 :=
         weighted_minkowski_sq _ W (fun d => prod_nonneg fun p _ => hw p _) v z
           (fun A hA => mul_nonneg (Real.sqrt_nonneg _) (prod_nonneg fun p hp =>
             ht p (mem_powerset.mp (mem_filter.mp hA).1 hp)))
           (fun A hA => one A (mem_powerset.mp (mem_filter.mp hA).1))
       _ = _ := by rw [show (∑ A ∈ Om.powerset.filter (fun A => A.Nonempty), z A) =
                         Real.sqrt (∏ p, B p) * ((∏ p ∈ Om, (1 + t p)) - 1) by
                          simp only [z, ← mul_sum, sum_nonempty_products], mul_pow, Real.sq_sqrt hB0]

/-- A single datum at each place and aligned real amplitudes attain the coefficient. -/
theorem defect_mass_attained {P : Type*} [Fintype P] [DecidableEq P] (Om : Finset P)
    (t : P → ℝ) :
    ∑ _d : (P → Unit), ‖∑ A ∈ Om.powerset.filter (fun A => A.Nonempty),
      ∏ p : P, (if p ∈ A then (t p : ℂ) else 1)‖ ^ 2 =
        ((∏ p ∈ Om, (1 + t p)) - 1) ^ 2 := by
  classical
  simp only [Fintype.prod_ite_mem, Finset.sum_const, Finset.card_univ,
    Fintype.card_unique, one_nsmul]
  have h : (∑ A ∈ Om.powerset.filter (fun A => A.Nonempty), ∏ p ∈ A, (t p : ℂ)) =
      (((∏ p ∈ Om, (1 + t p)) - 1 : ℝ) : ℂ) := by
    exact_mod_cast sum_nonempty_products Om t
  rw [h, Complex.norm_real, Real.norm_eq_abs, sq_abs]


/-- A product of local losses, with the no-loss term removed, uses one copy of the
largest possible loss. The remaining factors cost at most two each. -/
theorem prod_one_add_sub_one_le_uniform {ι : Type*} (s : Finset ι) (u : ι → ℝ) {t : ℝ}
    (ht' : t ≤ 1) (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ t) :
    0 ≤ (∏ i ∈ s, (1 + u i)) - 1 ∧
        (∏ i ∈ s, (1 + u i)) - 1 ≤ ((2 : ℝ) ^ s.card - 1) * t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    obtain ⟨hi₀, hit⟩ := hu i (Finset.mem_insert_self ..)
    obtain ⟨h₀, h⟩ := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    let D := (∏ j ∈ s, (1 + u j)) - 1
    have hstep : (1 + u i) * (∏ j ∈ s, (1 + u j)) - 1 = (1 + u i) * D + u i := by
      dsimp [D]
      ring
    rw [hstep]
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) h₀) hi₀
    · calc
        _ ≤ 2 * D + t := add_le_add (mul_le_mul_of_nonneg_right (by linarith) h₀) hit
        _ ≤ 2 * (((2 : ℝ) ^ s.card - 1) * t) + t := by linarith
        _ = _ := by ring

/-- With a positive uniform loss the squared coefficient strictly beats 4^|s| t²,
including for the empty set. -/
theorem prod_one_add_sub_one_sq_lt {ι : Type*} (s : Finset ι) (u : ι → ℝ) {t : ℝ}
    (ht : 0 < t) (ht' : t ≤ 1) (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ t) :
    ((∏ i ∈ s, (1 + u i)) - 1) ^ 2 < (4 : ℝ) ^ s.card * t ^ 2 := by
  obtain ⟨h₀, h⟩ := prod_one_add_sub_one_le_uniform s u ht' hu
  have hs : (∏ i ∈ s, (1 + u i)) - 1 < (2 : ℝ) ^ s.card * t := by linarith
  calc
    _ < ((2 : ℝ) ^ s.card * t) ^ 2 := by nlinarith
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]; norm_num

theorem local_defect_sq_lt_legacy {ι : Type*} (s : Finset ι) (q : ι → ℕ) (κ : ℕ)
    (hq : ∀ i ∈ s, 2 ≤ q i) :
    ((∏ i ∈ s, (1 + Real.sqrt (((q i : ℝ) ^ κ)⁻¹))) - 1) ^ 2 <
      (4 : ℝ) ^ s.card * ((2 : ℝ) ^ κ)⁻¹ := by
  have hp : 0 < (2 : ℝ) ^ κ := by positivity
  have hs : 0 < Real.sqrt (((2 : ℝ) ^ κ)⁻¹) := Real.sqrt_pos.2 (inv_pos.2 hp)
  have ht : Real.sqrt (((2 : ℝ) ^ κ)⁻¹) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact (inv_le_one₀ hp).2 (one_le_pow₀ (by norm_num))
  have hu (i) (hi : i ∈ s) : Real.sqrt (((q i : ℝ) ^ κ)⁻¹) ≤ Real.sqrt (((2 : ℝ) ^ κ)⁻¹) := by
    apply Real.sqrt_le_sqrt
    apply inv_anti₀ hp
    exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq i hi) _
  simpa only [Real.sq_sqrt (inv_pos.2 hp).le] using
    prod_one_add_sub_one_sq_lt s _ hs ht (fun i hi => ⟨Real.sqrt_nonneg _, hu i hi⟩)

end Formalism.HermitianLatticeCounting.S4
