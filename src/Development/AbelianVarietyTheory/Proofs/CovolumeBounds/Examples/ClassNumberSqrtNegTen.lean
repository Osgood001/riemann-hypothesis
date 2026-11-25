module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr

/-! Actual class-number count for ℚ(√−10). The divisor-sum bound is eight; the quadratic
primitive bound is seven. There are three ideals in the Minkowski window, and
sieving the rational scalar (2) leaves exactly two. The norm-two class is genuinely nonprincipal. -/

@[expose] public section
noncomputable section
open NumberField
namespace NumberField.SqrtNegTen

abbrev K := QuadraticAlgebra ℚ ((-10 : ℤ) : ℚ) ((0 : ℤ) : ℚ)
abbrev O := QuadraticAlgebra ℤ (-10) 0

instance : Fact (¬ IsSquare (QuadraticAlgebra.discr ((-10 : ℤ) : ℚ) ((0 : ℤ) : ℚ))) := by
  refine ⟨fun ⟨z, hz⟩ => ?_⟩
  norm_num [QuadraticAlgebra.discr_def] at hz
  nlinarith [sq_nonneg z]

instance : NumberField K := NumberField.of_module_finite ℚ _

theorem fundamental : Int.IsFundamentalDiscr (QuadraticAlgebra.discr (-10 : ℤ) 0) := by
  rw [Int.isFundamentalDiscr_iff_squarefree]
  norm_num [QuadraticAlgebra.discr_def, ← Int.squarefree_natAbs]
  exact (Nat.squarefree_mul (by decide : Nat.Coprime 2 5)).mpr
    ⟨Nat.prime_two.squarefree, (by decide : Nat.Prime 5).squarefree⟩

def model : O ≃ₐ[ℤ] 𝓞 K := QuadraticAlgebra.Int.algEquivIntegralClosure fundamental

theorem discr_K : NumberField.discr K = -40 := by
  let B := QuadraticAlgebra.basis (-10 : ℤ) 0
  rw [← NumberField.discr_eq_discr _ (B.map model.toLinearEquiv)]
  change Algebra.discr ℤ (model ∘ B) = _
  rw [← Algebra.discr_eq_discr_of_algEquiv]
  exact (Algebra.discr_quadraticAlgebra (a := (-10 : ℤ)) (b := 0)).trans (by norm_num [QuadraticAlgebra.discr_def])

/-- The prime above 2, given by reduction with √−10 ↦ 0 in the residue field. -/
def primeTwo : Ideal (𝓞 K) :=
  let φ : O →ₐ[ℤ] ZMod 2 := QuadraticAlgebra.lift ⟨0, by decide⟩
  RingHom.ker (φ.toRingHom.comp model.symm.toRingHom)

theorem absNorm_primeTwo : Ideal.absNorm primeTwo = 2 :=
  GlobalTheory.QuadraticZeta.absNorm_ker _

theorem norm_form (x y : ℤ) : Algebra.norm ℤ (model ⟨x,y⟩) = x^2 + 10*y^2 := by
  rw [Algebra.norm_eq_of_algEquiv model, Algebra.norm_quadraticAlgebra_apply]
  change x*x + 0*x*y - (-10)*y*y = x^2 + 10*y^2
  ring

theorem primeTwo_not_principal : ¬ primeTwo.IsPrincipal := by
  rintro ⟨a, ha⟩
  obtain ⟨⟨x,y⟩, rfl⟩ := model.surjective a
  have hh := absNorm_primeTwo
  rw [ha, Ideal.absNorm_span_singleton, norm_form] at hh
  have hf : 0 ≤ x^2 + 10*y^2 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have h2 : x^2 + 10*y^2 = 2 := by
    have h := Int.natAbs_of_nonneg hf
    omega
  have hy : y = 0 := by
    by_contra h
    have := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg x]
  subst y
  norm_num at h2
  have : -2 < x ∧ x < 2 := by constructor <;> nlinarith [sq_nonneg (x+1),sq_nonneg (x-1)]
  obtain ⟨_, _⟩ := this
  interval_cases x <;> norm_num at h2

open scoped nonZeroDivisors

theorem primeTwo_nonzero : primeTwo ∈ (Ideal (𝓞 K))⁰ :=
  mem_nonZeroDivisors_iff_ne_zero.mpr (fun h => by simpa [h] using absNorm_primeTwo)

theorem class_primeTwo_ne_one : ClassGroup.mk0 ⟨primeTwo, primeTwo_nonzero⟩ ≠ 1 :=
  fun h => primeTwo_not_principal ((ClassGroup.mk0_eq_one_iff primeTwo_nonzero).mp h)

theorem classNumber_ge_two : 2 ≤ classNumber K := by
  have h := classNumber_pos K
  by_contra! h'
  have hp := classNumber_eq_one_iff.mp (show classNumber K = 1 by omega)
  exact primeTwo_not_principal (hp.principal primeTwo)

open NumberField.InfinitePlace Module Finset GlobalTheory GlobalTheory.QuadraticZeta
open scoped Real ArithmeticFunction.zeta

theorem complexCount : nrComplexPlaces K = 1 := by
  have h := NumberField.sign_discr K
  rw [discr_K] at h
  have hr := card_add_two_mul_card_eq_rank K
  rw [QuadraticAlgebra.finrank_eq_two] at hr
  by_contra! hn
  have hz : nrComplexPlaces K = 0 := by omega
  rw [hz] at h
  exact absurd h (by decide)

theorem minkowski_floor : ⌊minkowskiBound K⌋₊ = 4 := by
  apply (Nat.floor_eq_iff' (by decide : 4 ≠ 0)).mpr
  rw [minkowskiBound, complexCount, QuadraticAlgebra.finrank_eq_two, discr_K]
  norm_num
  have hs : Real.sqrt 40 ^ 2 = 40 := Real.sq_sqrt (by norm_num)
  have hp := Real.pi_lt_d2
  have hl := Real.pi_gt_three
  constructor
  · field_simp
    nlinarith [Real.sqrt_nonneg 40, sq_nonneg (Real.sqrt 40 - 6.3)]
  · field_simp
    nlinarith [Real.sqrt_nonneg 40, sq_nonneg (Real.sqrt 40 - 6.4)]

theorem divisor_sum_eq_eight : ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊,
    (ζ ^ finrank ℚ K : ArithmeticFunction ℕ) n = 8 := by
  rw [minkowski_floor, QuadraticAlgebra.finrank_eq_two]
  decide +kernel

/-- The degree-two primitive count before any field-specific splitting is used. -/
theorem quadratic_count_eq_seven :
    ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, 2 ^ n.primeFactors.card = 7 := by
  rw [minkowski_floor, show Ioc 0 4 = {1,2,3,4} from by decide]
  norm_num [Finset.sum_insert, Nat.prime_two.primeFactors, Nat.prime_three.primeFactors,
    show (4 : ℕ).primeFactors = {2} from Nat.primeFactors_prime_pow (k := 2) (by decide) Nat.prime_two]

/-- In this window the Kronecker recurrence gives the four actual ideal counts:
one, one, zero, one. No residue ideals need be enumerated. -/
private theorem ideal_counts :
    idealCount K 1 = 1 ∧ idealCount K 2 = 1 ∧ idealCount K 3 = 0 ∧ idealCount K 4 = 1 := by
  have h1 : idealCount K 1 = 1 := by
    unfold idealCount
    simpa only [Ideal.absNorm_eq_one_iff, Set.ofPred_eq_eq_singleton] using
      Set.ncard_singleton (⊤ : Ideal (𝓞 K))
  have k2 : kroneckerAt (-40) 2 = 0 := by norm_num [kroneckerAt]; decide +kernel
  have k3 : kroneckerAt (-40) 3 = -1 := by norm_num [kroneckerAt]
  have h2 := idealCount_prime_mul (K := K) (QuadraticAlgebra.finrank_eq_two _ _) Nat.prime_two 1
  have h3 := idealCount_prime_mul (K := K) (QuadraticAlgebra.finrank_eq_two _ _) Nat.prime_three 1
  have h4 := idealCount_prime_mul (K := K) (QuadraticAlgebra.finrank_eq_two _ _) Nat.prime_two 2
  norm_num [discr_K, k2, k3, h1] at h2 h3 h4
  exact ⟨h1, h2, h3, by omega⟩

private theorem without_sieve (n : ℕ) :
    (scalarSieveFibre K ∅ n).ncard = idealCount K n := by
  simp [scalarSieveFibre, idealCount]

theorem unsieved_count_eq_three :
    ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, (scalarSieveFibre K ∅ n).ncard = 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := ideal_counts
  rw [minkowski_floor, show Ioc 0 4 = {1,2,3,4} from by decide]
  norm_num [Finset.sum_insert, without_sieve, h1, h2, h3, h4]

theorem sieved_count_eq_two :
    ∑ n ∈ Ioc 0 ⌊minkowskiBound K⌋₊, (scalarSieveFibre K n.primeFactors n).ncard = 2 := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := ideal_counts
  have sieve (p : ℕ) (hp : p.Prime) (n : ℕ) :
      (scalarSieveFibre K {p} n).ncard = (scalarSieveFibre K ∅ n).ncard -
        if p^2 ∣ n then (scalarSieveFibre K ∅ (n / p^2)).ncard else 0 := by
    simpa only [LawfulSingleton.insert_empty_eq, QuadraticAlgebra.finrank_eq_two] using
      ncard_scalarSieveFibre_insert K ∅ hp (by simp) n
  rw [minkowski_floor, show Ioc 0 4 = {1,2,3,4} from by decide]
  norm_num [Finset.sum_insert, Nat.primeFactors_one, Nat.prime_two.primeFactors,
    Nat.prime_three.primeFactors, show (4 : ℕ).primeFactors = {2} from Nat.primeFactors_prime_pow (k := 2) (by decide) Nat.prime_two,
    sieve 2 Nat.prime_two, sieve 3 Nat.prime_three, without_sieve, h1, h2, h3, h4]

theorem classNumber_eq_two : classNumber K = 2 :=
  le_antisymm (sieved_count_eq_two ▸ classNumber_le_sum_scalarSieve K) classNumber_ge_two

end NumberField.SqrtNegTen
