module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_bis

theorem goal1 :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) := by simp

end Bl.general_b_fact_bis
