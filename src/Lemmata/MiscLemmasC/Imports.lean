module

public import Mathlib

@[expose] public section

open Finset

namespace Bl.SecondBlockLemmaD

theorem goal1 {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [DecidableEq B]
    (π : A →+ B) (hπ : Function.Surjective π) (G : B → ℂ) :
    (Fintype.card A : ℂ)⁻¹ * ∑ a, G (π a) = (Fintype.card B : ℂ)⁻¹ * ∑ b, G b := by
  have hfib : ∀ b : B, (univ.filter fun a => π a = b).card = (univ.filter fun a => π a = 0).card :=
    fun b => AddMonoidHom.card_fiber_eq_of_mem_range π (hπ b) (hπ 0)
  set c := (univ.filter fun a => π a = 0).card with hc
  have hc0 : c ≠ 0 := by aesop
  have hsum : ∑ a, G (π a) = ∑ b, (c : ℂ) * G b := by
    rw [← Finset.sum_fiberwise Finset.univ π (fun a => G (π a))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.1 ha).2]), Finset.sum_const,
      hfib b, nsmul_eq_mul]
  have hcard : Fintype.card A = Fintype.card B * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := univ)
      (fun _ _ => Finset.mem_univ _)]
    rw [Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hsum, ← Finset.mul_sum, hcard]
  push_cast
  field_simp

end Bl.SecondBlockLemmaD
