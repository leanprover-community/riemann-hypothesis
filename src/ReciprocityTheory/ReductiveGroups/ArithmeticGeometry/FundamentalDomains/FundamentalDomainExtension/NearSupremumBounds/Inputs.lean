module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.NearSupremumBounds.FdFjNearSupOf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds

@[expose] public section

namespace PI.FdFjNearSup.W

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem fourierJacobi_holomorphic : FjHolo (E := E) := by
  intro r X la P ξ ν hP hξ
  exact ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_diffOn X la P hP.1 hξ ν

theorem fourierJacobi_realFlow : FjRealFlow (E := E) := by
  intro r X la P ξ ν hP hξ x hx s
  have hP' : X.IsBddSec la P ∧ ∀ ξ', X.IsIso ξ' → ∀ y ∈ X.dom, X.fj la ξ' 0 P y = 0 := hP

  exact X.fj_flow_real la ξ hξ ν P hP'.1.1 hP'.1.2 x hx s

theorem fd_fj_near_sup_full :
    HolomorphicPeriodicityExtension (E := E) → FlowNormRatio (E := E) → ModerateCoefficientPositivity (E := E) →
      NearSupremumTransference (E := E) :=
  fd_fj_near_sup_of flowDomainCriterion_holds fourierJacobi_holomorphic fourierJacobi_realFlow orthonormalFlagTranslate_holds

end PI.FdFjNearSup.W
