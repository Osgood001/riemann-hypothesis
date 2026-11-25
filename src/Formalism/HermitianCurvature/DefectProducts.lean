module

public import Mathlib

@[expose] public section

namespace Formalism.HermitianLatticeCounting.DefectSum
open Finset
variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- The total of all nonempty defect masks is the product of local totals minus
the empty mask. No enumeration of masks is needed. -/
theorem nonempty (s : Finset ι) (bad good : ι → R) :
    ∑ b ∈ s.powerset.erase ∅, ∏ i ∈ s, (if i ∈ b then bad i else good i) =
      (∏ i ∈ s, (bad i + good i)) - ∏ i ∈ s, good i := by
  classical
  let w (b : Finset ι) := ∏ i ∈ s, (if i ∈ b then bad i else good i)
  have h : ∑ b ∈ s.powerset, w b = ∏ i ∈ s, (bad i + good i) := by
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro b hb
    simpa [w, Finset.piecewise, Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hb)] using
      Finset.prod_piecewise s b bad good
  have hs := Finset.sum_erase_add s.powerset w (by simp : ∅ ∈ s.powerset)
  exact eq_sub_of_add_eq (by simpa [w] using hs.trans h)

theorem filter_nonempty (s : Finset ι) (bad good : ι → R) (Q : Prop → Prop)
    [DecidablePred (fun b : Finset ι => Q b.Nonempty)] [Decidable (Q True)] [Decidable (Q False)] :
    ∑ b ∈ s.powerset.filter (fun b => Q b.Nonempty), ∏ i ∈ s, (if i ∈ b then bad i else good i) =
      (if Q False then ∏ i ∈ s, good i else 0) +
      (if Q True then (∏ i ∈ s, (bad i + good i)) - ∏ i ∈ s, good i else 0) := by
  classical
  let w (b : Finset ι) := ∏ i ∈ s, (if i ∈ b then bad i else good i)
  rw [Finset.sum_filter, ← Finset.add_sum_erase _ _ (by simp : ∅ ∈ s.powerset)]
  congr 1
  · simp
  · change ∑ b ∈ s.powerset.erase ∅, (if Q b.Nonempty then w b else 0) = _
    have he (b : Finset ι) (hb : b ∈ s.powerset.erase ∅) : b.Nonempty = True :=
      propext (iff_true_intro (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hb).1))
    by_cases hQ : Q True
    · rw [ite_eq_left hQ]
      refine Eq.trans ?_ (nonempty s bad good)
      exact Finset.sum_congr rfl fun b hb => ite_eq_left ((congrArg Q (he b hb)).mpr hQ)
    · rw [ite_eq_right hQ]
      exact Finset.sum_eq_zero fun b hb => ite_eq_right (fun h => hQ ((congrArg Q (he b hb)).mp h))
/-- With a finite ambient product, places outside the exception set always contribute
their good factor. This remains valid if some of those factors vanish. -/
theorem filter_ambient [Fintype ι] (s : Finset ι) (bad good : ι → R) (Q : Prop → Prop)
    [DecidablePred (fun b : Finset ι => Q b.Nonempty)] [Decidable (Q True)] [Decidable (Q False)] :
    ∑ b ∈ s.powerset.filter (fun b => Q b.Nonempty), ∏ i, (if i ∈ b then bad i else good i) =
      (if Q False then ∏ i, good i else 0) +
        (if Q True then (∏ i, if i ∈ s then bad i + good i else good i) - ∏ i, good i else 0) := by
  classical
  let c := ∏ i ∈ univ \ s, good i
  have split (f : ι → R) (outside : ∀ i ∈ univ \ s, f i = good i) :
      ∏ i, f i = (∏ i ∈ s, f i) * c := by
    dsimp only [c]
    rw [← Finset.prod_congr rfl outside, mul_comm, Finset.prod_sdiff (Finset.subset_univ s)]
  have goodEq := split good fun _ _ => rfl
  have totalEq : (∏ i, if i ∈ s then bad i + good i else good i) = (∏ i ∈ s, (bad i + good i)) * c := by
    rw [split _ (fun i hi => ite_eq_right (Finset.mem_sdiff.mp hi).2)]
    congr 1
    exact Finset.prod_congr rfl fun i hi => ite_eq_left hi
  rw [totalEq, goodEq]
  calc
    _ = (∑ b ∈ s.powerset.filter (fun b => Q b.Nonempty), ∏ i ∈ s, if i ∈ b then bad i else good i) * c := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b hb => split _ fun i hi => ?_
      exact ite_eq_right (fun h => (Finset.mem_sdiff.mp hi).2 ((Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1) h))
    _ = _ := by
      rw [filter_nonempty]
      by_cases h₀ : Q False <;> by_cases h₁ : Q True <;> simp [h₀, h₁]
      ring

open scoped ComplexConjugate

/-- The squared distance between two product amplitudes requires only their local
second moments and cross moments. The real weights need not be positive. -/
theorem weighted_sq_sub_prod {P : Type*} [Fintype P] [DecidableEq P]
    {D : P → Type*} [∀ p, Fintype (D p)] (w : ∀ p, D p → ℝ) (a z : ∀ p, D p → ℂ) :
    ∑ d : (∀ p, D p), (∏ p, w p (d p)) * ‖(∏ p, a p (d p)) - ∏ p, z p (d p)‖ ^ 2 =
      (∏ p, ∑ j, w p j * ‖a p j‖ ^ 2) + (∏ p, ∑ j, w p j * ‖z p j‖ ^ 2) -
        2 * (∏ p, ∑ j, (w p j : ℂ) * (z p j * conj (a p j))).re := by
  classical
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib, Finset.prod_pow, ← norm_prod,
    ← map_prod, ← Complex.ofReal_prod, Complex.re_sum, Complex.re_ofReal_mul]
  rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  rw [@norm_sub_sq ℂ, RCLike.inner_apply]
  simp only [RCLike.re_to_complex]
  ring

end Formalism.HermitianLatticeCounting.DefectSum
