module

public import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated
public import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin
public import Formalism.LatticeSlopes.LatticeSlopesProofs.OrthSum
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.F

theorem covolEqGram : CovolEqGram := covol_eq_gram
theorem covolPos : CovolPos := covol_pos'
theorem covolBasic : CovolBasic := covol_basic_properties
theorem covolEqCovolume : CovolEqCovolume := covol_eq_covolume'
theorem gramDetLe : GramDetLe := gram_det_le
theorem slopesBdd : SlopesBdd := slopesBdd_of gramDetLe
theorem slopeLeMuMax : SlopeLeMuMax := slopeLeMuMax_of slopesBdd
theorem degQuot : DegQuot := degree_quotient
theorem covolAntiSameRank : CovolAntiSameRank := covol_anti_same_rank
theorem saturProps : SaturProps := saturation_properties
theorem shortVector : ShortVector := shortVector_of covolEqCovolume
theorem finiteSaturated : FiniteSaturated := finiteSaturated_of shortVector
theorem muMaxLeMin : MuMaxLeMin := muMaxLeMin_of covolPos shortVector
theorem orthSum : OrthSum := orthogonal_sum_slope

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem covol_pos (L : Submodule ℤ E) [DiscreteTopology L] : 0 < covol L :=
  covolPos E L ‹_›

theorem deg_eq_deg_add_deg_quot {L N : Submodule ℤ E} [DiscreteTopology L] (hN : IsSaturated L N) :
    deg L = deg N + deg (quot L N) :=
  (degQuot E L N ‹_› hN).2.2

end

end Formalism.F
