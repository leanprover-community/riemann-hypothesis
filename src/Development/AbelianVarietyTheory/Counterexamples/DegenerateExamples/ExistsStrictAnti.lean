import Mathlib
import Formalism.JacquetSubsetSums.JacquetSubsetSum

namespace GlobalTheory.ConeCharCheck

def antiMon (r : ℕ) : Submonoid (Multiplicative (Fin r → ℤ)) where
  carrier := {g | Antitone (Multiplicative.toAdd g)}
  one_mem' := fun _ _ _ => le_rfl
  mul_mem' := fun {a b} ha hb i j h => add_le_add (ha h) (hb h)


end GlobalTheory.ConeCharCheck
