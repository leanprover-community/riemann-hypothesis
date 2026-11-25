module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NormNum.LegendreSymbol

@[expose] public section

namespace GlobalTheory.LowerTriangularMul

theorem lowerTriangular_mul {S : Type} [CommRing S] {n : ℕ} (A B : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), i < j → A i j = (0 : S))
    (hB : ∀ (i j : Fin n), i < j → B i j = (0 : S)) :
    ∀ (i j : Fin n), i < j → (A * B) i j = (0 : S) := fun i j hij =>
  Matrix.BlockTriangular.mul (b := (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ)) hA hB
    (show OrderDual.toDual j < OrderDual.toDual i from hij)

alias main := _root_.GlobalTheory.LowerTriangularMul.lowerTriangular_mul

end GlobalTheory.LowerTriangularMul
