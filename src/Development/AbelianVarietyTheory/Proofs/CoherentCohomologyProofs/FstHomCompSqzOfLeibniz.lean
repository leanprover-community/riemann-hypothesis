module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.SquareZeroLeibnizPoint

open TrivSqZeroExt

section PointsOfDual

variable {O C : Type*} [CommRing O] [CommRing C] {ι : Type*} [Fintype ι]

end PointsOfDual

section Leibniz

variable {A O M : Type*} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M]

theorem leibniz_map_one (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : d 1 = 0 := by
  have h := hd 1 1
  simpa using h

variable [Module Oᵐᵒᵖ M] [IsCentralScalar O M]

def sqzOfLeibniz (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : A →+* TrivSqZeroExt O M where
  toFun f := (ε f, d f)
  map_one' := TrivSqZeroExt.ext (map_one ε) (leibniz_map_one ε d hd)
  map_zero' := TrivSqZeroExt.ext (map_zero ε) (map_zero d)
  map_add' f f' := TrivSqZeroExt.ext (map_add ε f f') (map_add d f f')
  map_mul' f f' := TrivSqZeroExt.ext (map_mul ε f f') (by
    change d (f * f') = ε f • d f' + MulOpposite.op (ε f') • d f
    rw [op_smul_eq_smul]
    exact hd f f')

end Leibniz

end GlobalTheory.SquareZeroLeibnizPoint
