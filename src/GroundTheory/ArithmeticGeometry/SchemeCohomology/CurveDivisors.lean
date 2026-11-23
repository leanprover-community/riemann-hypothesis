module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurvePlaces
public import GroundTheory.FunctionField.Divisor
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

set_option maxSynthPendingDepth 1

open CategoryTheory AlgebraicGeometry Order Topology Module

open scoped WithZero

universe u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormalScheme X]

namespace PrimeDivisor


noncomputable def degree (Z : PrimeDivisor X) : ℕ :=
  finrank k (IsLocalRing.ResidueField (X.presheaf.stalk Z.point))

end PrimeDivisor

noncomputable def WeilDivisor.degree : WeilDivisor X →+ ℤ :=
  Finsupp.liftAddHom fun Z => AddMonoidHom.mulRight ((Z.degree (k := k) : ℕ) : ℤ)

variable [IsProper (X ↘ Spec (.of k))]

noncomputable def divisorEquiv (hX : topologicalKrullDim X ≤ 1) :
    WeilDivisor X ≃+ Divisor k X.functionField :=
  Finsupp.domCongr (placeEquiv hX)

variable [IsFunctionField k X.functionField]

end GroundTheory.Arith.SchemeCoh
