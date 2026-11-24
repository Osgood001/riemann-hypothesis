module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_second_ter

theorem goal1 :
  ∀ {n : Nat} (Q : Fin n → Prop) [inst : DecidablePred.{1} Q],
  (∀ (q q' : Fin n), LE.le.{0} q' q → Q q → Q q') →
    ∀ (p : Fin n), Iff (Q p) (LT.lt.{0} p.val (Finset.card.{0} (Finset.filter.{0} Q Finset.univ.{0}))) := by
  intro n Q _ hQ p
  constructor
  · intro hp
    have h : Finset.Iic p ⊆ Finset.filter Q Finset.univ := by grind
    have hc := Finset.card_le_card h
    rw [Fin.card_Iic] at hc
    omega
  · intro hlt
    by_contra hp
    have h : Finset.filter Q Finset.univ ⊆ Finset.Iio p := by grind
    have hc := Finset.card_le_card h
    rw [Fin.card_Iio] at hc
    omega

end Bl.general_b_fact_second_ter
