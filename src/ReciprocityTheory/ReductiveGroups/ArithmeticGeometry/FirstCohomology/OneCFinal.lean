module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaBarEnum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.DVR

theorem cmLiftCondition_of_dimSplit (hL : ReciprocityTheory.ChartRestriction.G.Out.Laws) (h1c : PositiveValuationMaximalIdeal) (h2f : DvrLevelFrame)
    (h3 : FiniteOrderValuationInvariance) (hU : UUStatement) (hC : CanonLiftFixStatement) (hdim : DimSplitStatement) :
    OneCStatement :=
  oneC_of hL (phiFun_of_globalFns hL.globalFns) h1c
    (pullback_valuation_forward_of (pullGen_of hL.globalFns) (QuadraticAlgebraValuation.qAl_of hL)) h2f h3 hU (finOrdExists_of_laws hL)
    (alphaBarEnum_holds hL.weil hL.mulN) hC alphaPair_holds hdim

theorem cmLiftCondition_of_torsion (hL : ReciprocityTheory.ChartRestriction.G.Out.Laws) (h1c : PositiveValuationMaximalIdeal) (hTW : TWStatement)
    (hU : UUStatement) (hC : CanonLiftFixStatement) (hdim : DimSplitStatement) : OneCStatement :=
  cmLiftCondition_of_dimSplit hL h1c (levelFrame_of_laws hL) (galois_fixed_adelic_matrices_descend hL hTW) hU hC hdim

end ReciprocityTheory.ChartRestriction.G.H1
