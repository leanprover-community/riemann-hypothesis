module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CountingExponentialSumHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientQuantitativeHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientsOfVectorGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLineOfCovering
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorBoundOfCoefficientBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorSixthLemmaPrimeHolds

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem shortVectorBound : ShortVectorBound (E := E) :=
  shortVectorBound_of_coefficient_bounds fourier_coefficients_holds cusp_coefficient_quantitative_holds flowCoefficientDecay coefficientIndex_lowerBound coefficientHeight_bound counting_exponential_sum_holds isotropic_outside_line

end ReciprocityTheory.ChartRestriction.G.FD
