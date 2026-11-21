import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

namespace GlobalTheory.CompanionTheory.Ar.BT.OpsModel

open GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] {T H : Type} [CommGroup T] [CommGroup H]

theorem pullFun_apply (ι : H →* T) (f : T → R) (h : H) : pullFun R ι f h = f (ι h) := rfl

theorem mem_quotOrder (π : T →* H) (A : Subalgebra R (T → R)) (f : H → R) :
    f ∈ quotOrder π A ↔ (fun t => f (π t)) ∈ A := Iff.rfl







def evChar (t : T) : (T →* Rˣ) →* Rˣ where
  toFun χ := χ t
  map_one' := rfl
  map_mul' _ _ := rfl











end GlobalTheory.CompanionTheory.Ar.BT.OpsModel
