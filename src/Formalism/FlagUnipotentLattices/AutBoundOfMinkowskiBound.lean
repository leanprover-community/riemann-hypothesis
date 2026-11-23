module

public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.HermitianLatticeCounting.Final.S6

theorem nFJZero : Formalism.HermitianLatticeCounting.S6.NFJZero := by
  first
    | exact Formalism.HermitianLatticeCounting.P.normalFormZero
    | exact Formalism.HermitianLatticeCounting.P.S6e.normalFormZero

theorem normalForm : Formalism.HermitianLatticeCounting.S6.NormalForm := by
  first
    | exact Formalism.HermitianLatticeCounting.P.existsNormalForm
    | exact Formalism.HermitianLatticeCounting.P.S6e.existsNormalForm

theorem normSgBound : Formalism.HermitianLatticeCounting.S6.NormSgBound := by
  first
    | exact Formalism.HermitianLatticeCounting.P.norm_singular_value_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.norm_singular_value_bound

theorem finalSum : Formalism.HermitianLatticeCounting.S6.FinalSum := by
  first
    | exact Formalism.HermitianLatticeCounting.P.final_sum_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.final_sum_bound

end Formalism.HermitianLatticeCounting.Final.S6
