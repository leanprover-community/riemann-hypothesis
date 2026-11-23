module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.DivLeExpOfAbsLogSubLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.FourierJacobiDifferentiable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames

@[expose] public section

open PIW.FdPA in
theorem fd_point_assembly {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] : ReciprocityTheory.ChartRestriction.G.FD.ShortVectorBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalFlagTranslate (E := E) → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartNormControl (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NearSupremumTransference (E := E) → ReciprocityTheory.ChartRestriction.G.FD.SchwarzLemmaBall → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalShortVectorBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.IsotropicCoefficientSplitting (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NoShortVectorLowerBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.UnitaryUnipotentMove (E := E) → ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainPointBound (E := E) :=
  fun _ h0 h1 h2 h3 h4 _ _ h7 =>
    fundamentalDomain_of_parts fourierJacobi_differentiable fourierJacobi_boundaryEq fourierJacobi_bounded orthonormal_domain unitary_domain borel_flag_translate
      chartNorm_smul chartNorm_nonneg normFactor_pos_alt chart_zero_eq_alt h0 h1 h2 h3 h4 h7
