module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
public import Formalism.FilteredPoleLength.LocalDescentLevels.DetMulEqSumPrincipal
public import Formalism.FilteredPoleLength.LocalDescentLevels.ExistsSumOfMemSpanImage
public import Formalism.FilteredPoleLength.LocalDescentLevels.GAdjugateNormBound
public import Formalism.FilteredPoleLength.LocalDescentLevels.IntegralMulExpNegSq
public import Formalism.FilteredPoleLength.LocalDescentLevels.MinimumChainBounds
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2.Ext

theorem all : All :=
  ⟨Formalism.LatticeBaseChangeAlt.packingCount, Formalism.LatticeBaseChangeAlt.gaussian_tail_bound, Formalism.LatticeBaseChangeAlt.ballVolume, Formalism.LatticeBaseChangeAlt.gHadamard,
    Formalism.LatticeBaseChangeAlt.nearestPlane, Formalism.LatticeBaseChangeAlt.cauchyBinetMax, Formalism.LatticeBaseChangeAlt.detPerturbation,
    Formalism.LatticeBaseChangeAlt.detPerturbNumeric, Formalism.LatticeBaseChangeAlt.detProductRest⟩

end ReciprocityTheory.ChartRestriction.G.I2.Ext
