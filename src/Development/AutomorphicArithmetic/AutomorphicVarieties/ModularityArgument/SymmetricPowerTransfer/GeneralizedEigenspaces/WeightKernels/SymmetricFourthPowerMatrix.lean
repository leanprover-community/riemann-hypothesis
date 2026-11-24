module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open UpperTheory.V.Af

namespace UpperTheory.V.Z.Sym.Ga



def symmetricFourthPowerMatrix (R : Type) [CommRing R] : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 5) (Fin 5) R where
  toFun g := !![g 0 0 ^ 4, g 0 0 ^ 3 * g 0 1, g 0 0 ^ 2 * g 0 1 ^ 2, g 0 0 * g 0 1 ^ 3, g 0 1 ^ 4;
    4 * g 0 0 ^ 3 * g 1 0, g 0 0 ^ 3 * g 1 1 + 3 * g 0 0 ^ 2 * g 1 0 * g 0 1, 2 * g 0 0 ^ 2 * g 0 1 * g 1 1 + 2 * g 0 0 * g 1 0 * g 0 1 ^ 2, 3 * g 0 0 * g 0 1 ^ 2 * g 1 1 + g 1 0 * g 0 1 ^ 3, 4 * g 0 1 ^ 3 * g 1 1;
    6 * g 0 0 ^ 2 * g 1 0 ^ 2, 3 * g 0 0 ^ 2 * g 1 0 * g 1 1 + 3 * g 0 0 * g 1 0 ^ 2 * g 0 1, g 0 0 ^ 2 * g 1 1 ^ 2 + 4 * g 0 0 * g 1 0 * g 0 1 * g 1 1 + g 1 0 ^ 2 * g 0 1 ^ 2, 3 * g 0 0 * g 0 1 * g 1 1 ^ 2 + 3 * g 1 0 * g 0 1 ^ 2 * g 1 1, 6 * g 0 1 ^ 2 * g 1 1 ^ 2;
    4 * g 0 0 * g 1 0 ^ 3, 3 * g 0 0 * g 1 0 ^ 2 * g 1 1 + g 1 0 ^ 3 * g 0 1, 2 * g 0 0 * g 1 0 * g 1 1 ^ 2 + 2 * g 1 0 ^ 2 * g 0 1 * g 1 1, g 0 0 * g 1 1 ^ 3 + 3 * g 1 0 * g 0 1 * g 1 1 ^ 2, 4 * g 0 1 * g 1 1 ^ 3;
    g 1 0 ^ 4, g 1 0 ^ 3 * g 1 1, g 1 0 ^ 2 * g 1 1 ^ 2, g 1 0 * g 1 1 ^ 3, g 1 1 ^ 4]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

variable {Γ k : Type} [Group Γ] [Field k]

def sym4 (ρ : Γ →* GL (Fin 2) k) : Γ →* GL (Fin 5) k :=
  tw ((Units.map (symmetricFourthPowerMatrix k)).comp ρ) ((Matrix.GeneralLinearGroup.det.comp ρ)⁻¹ ^ 2)

end UpperTheory.V.Z.Sym.Ga

end
