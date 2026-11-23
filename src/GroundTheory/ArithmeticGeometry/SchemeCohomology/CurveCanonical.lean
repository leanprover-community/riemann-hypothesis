module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveDivisors
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorInvertible
public import GroundTheory.FunctionField.WeilDifferential
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

@[expose] public section

open CategoryTheory AlgebraicGeometry Order Topology Module MonoidalCategory

universe u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsNoetherian X] [IsLocallyFactorial X] [IsProper (X ↘ Spec (.of k))]
  [IsFunctionField k X.functionField]


omit [IsProper (X ↘ Spec (.of k))] [IsFunctionField k X.functionField] in
noncomputable def invertibleDegree {L : X.Modules} (hL : IsInvertibleSheaf L) : ℤ :=
  WeilDivisor.degree (k := k) (divisorOfInvertible hL)



variable (hX : topologicalKrullDim X ≤ 1)

noncomputable def canonicalDifferential : WeilDifferential k X.functionField :=
  (WeilDifferential.exists_ne_zero (k := k) (K := X.functionField)).choose


noncomputable def canonicalDivisor : WeilDivisor X :=
  (divisorEquiv (k := k) hX).symm (canonicalDifferential (k := k) (X := X)).divisor

noncomputable def canonicalSheaf : X.Modules :=
  divisorSheaf (canonicalDivisor (k := k) hX)

end GroundTheory.Arith.SchemeCoh
