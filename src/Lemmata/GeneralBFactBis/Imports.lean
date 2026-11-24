module

public import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Order.AddGroupWithTop

@[expose] public section

namespace Bl.general_b_fact_bis

theorem goal1 :
  ∀ {x : WithBot.{0} ENat} {m : Nat},
  Eq.{1} (HAdd.hAdd.{0, 0, 0} x 1) (Nat.cast.{0} (HAdd.hAdd.{0, 0, 0} m 1)) → Eq.{1} x (Nat.cast.{0} m) := by
  intro x m h
  apply ENat.WithBot.add_one_cancel.mp
  simpa only [Nat.cast_add, Nat.cast_one] using h

end Bl.general_b_fact_bis
