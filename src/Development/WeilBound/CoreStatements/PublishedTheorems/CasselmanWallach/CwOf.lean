module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachLift
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigBasis
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BilinearFormCasimir
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3B
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3C
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C7
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegative
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegativeSymmetric
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasselmanWallachAdmissible
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.D5
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.DerivativeContinuity
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.DerivativeRepresentation
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.E3D
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenOrthogonalForm
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenspacesOrthogonal
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsFunctional
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsNormingFunctional
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExponentialKSet
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.HighestWeightKernel
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.HilbertSchmidtSqEq
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.Imports
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KTypesFiniteOfHighestWeight
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionAdditive
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionLinear
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.PageTheorem
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SeminormApproximation
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SlopeLimitConstant
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.TendstoPiZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ZeroOnDense
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ZetaClassicalZeroFreeRegion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

namespace PositivityTheory.CW

theorem lift_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallachLift := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact lift_of_steps hM hmodel c4 c5 c6 c7 d0 d1b d2 d3 d4b d5

theorem cw_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallach := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact cw_of_steps hM hmodel c5 d0 (lift_of hM) e1a e1b e2a e2b e2c e2d e3a e3b e3c e3d

end PositivityTheory.CW
