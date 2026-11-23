module

public import Formalism.LagrangeIdealLifts.Statement
public import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.Graded
public import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.LagrangeIdeal
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.LagrangeIdealCyc
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.UChase
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.UClaim
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.LIFT

theorem lift_LagrangeIdeal : LagrangeIdeal := lagrangian_ideal_holds
theorem lift_LagrangeIdealInt : LagrangeIdealInt := lagrangian_ideal_integral_holds
theorem lift_WBTail : WBTail := wBTail_of gammaGradedStep_holds (lagrangeIdealCyc_of lagrangian_ideal_holds)
theorem lift_LemmaU : LemmaU := lemmaU_of (uClaim_of (uGraded_of gammaGradedStep_holds) gammaGradedStep_holds) uChase_proof

end Formalism.LIFT
