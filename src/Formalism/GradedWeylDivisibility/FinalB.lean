module

public import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQBilin
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQPos
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWInClosed
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLine
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWLineTall
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivClosedGraded
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylEqNablaQ
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylRationalOf
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

namespace Formalism.GradedWeylDivisibility

theorem hwLine : HWLine := highest_weight_line
theorem hwLineTall : HWLineTall := highest_weight_line_tall
theorem fockQPos : FockQPos := fischerInnerRatPos
theorem fockQBilin : FockQBilin := fischerInnerRatBilinear
theorem fockQRowDivAdj : FockQRowDivAdj := fock_space_row_divided_adjoint
theorem rowDivClosedGraded : RowDivClosedGraded := row_divided_closed_graded
theorem hwInClosed : HWInClosed := hwInClosed_of hwLine rowDivClosedGraded
theorem closedEqNabla : ClosedEqNabla := closedEqNabla_of hwInClosed fockQPos fockQBilin fockQRowDivAdj
theorem weylEqNablaQ : WeylEqNablaQ := weylEqNablaQ_of closedEqNabla

theorem weylRational : WeylRational := weyl_module_rational weylEqNablaQ

end Formalism.GradedWeylDivisibility
