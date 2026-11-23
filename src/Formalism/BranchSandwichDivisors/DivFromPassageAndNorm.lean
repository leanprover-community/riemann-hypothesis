module

public import Formalism.BranchSandwichDivisors.StatementL
public import Formalism.BranchSandwichDivisors.StatementW
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
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

namespace Formalism.BranchingDeterminantCap

theorem mapMu : MapMu := map_slope_mu
theorem scaleSandwich : ScaleSandwich := scale_sandwich_bound
theorem orthSum : OrthSum := orthogonal_sum_slope
theorem powMu : PowMu := power_slope_mu
theorem orthSandwich : OrthSandwich := orthogonal_sandwich_bound
theorem transferPart : TransferPart := transferPart_of mapMu powMu
theorem transferMuMax : TransferMuMax := transferMuMax_of scaleSandwich orthSum powMu
theorem transferDeg : TransferDeg := degreeTransferBound
theorem interlaceIdent : InterlaceIdent := interlaceIdentities
theorem capConst : CapConst := capacity_constant_bound
theorem weylDimBound : WeylDimBound := weyl_dimension_bound
theorem branchMap : BranchMap := branch_map_formula
theorem xiNorm : XiNorm := xi_norm_bound

end Formalism.BranchingDeterminantCap
