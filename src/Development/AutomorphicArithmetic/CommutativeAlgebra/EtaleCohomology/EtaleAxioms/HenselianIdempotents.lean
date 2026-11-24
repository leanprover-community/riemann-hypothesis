module

public import Development.EtaleCohomology.EtaleSheaves.LIdemLiftPf
public import Development.EtaleCohomology.EtaleSheaves.SurjectiveCharts
import Development.AutomorphicArithmetic.CommutativeAlgebra.LiftIdempotentFactorizationHolds
import Development.EtaleCohomology.EtaleSheaves.FiniteChartSurjPf
import Development.EtaleCohomology.EtaleSheaves.LIdemPf
public import Development.EtaleCohomology.EtaleSheaves.LJacPf
import Development.EtaleCohomology.EtaleSheaves.LMonicPf
public import Development.EtaleCohomology.EtaleSheaves.SurjectiveCharts.EtaleSurjectiveChartOfFiniteChartSurj
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace UpperTheory.Et.HenselianIdempotents

theorem a0 : LateralTheory.E.HensIdemCut.LJac := LateralTheory.E.LJacPf.LJac_of
theorem a1 : LateralTheory.E.HensIdemCut.LMonic := LateralTheory.E.LMonicPf.LMonic_of
theorem a2 : LateralTheory.E.LIdemLiftPf.LFact := UpperTheory.liftIdempotentFactorization_holds
theorem a3 : LateralTheory.E.LChartPf.LIdemLift := LateralTheory.E.LIdemLiftPf.LIdemLift_of a2
theorem a4 : LateralTheory.E.LSurjChartPf.FiniteChartSurj := LateralTheory.E.FiniteChartSurjPf.FiniteChartSurj_of
theorem a5 : LateralTheory.E.LChartPf.LSurjChart := LateralTheory.E.LSurjChartPf.etale_surjective_chart_of_finite_chart_surj a4
theorem a6 : LateralTheory.E.LEtaleLiftPf.LChart := LateralTheory.E.LChartPf.LChart_of a3 a5
theorem a7 : LateralTheory.E.LFactorPf.LEtaleLift := LateralTheory.E.LEtaleLiftPf.LEtaleLift_of a6
theorem a8 : LateralTheory.E.HensIdemCut.LFactor := LateralTheory.E.LFactorPf.LFactor_of a7
theorem a9 : LateralTheory.E.HensIdemCut.LIdem := LateralTheory.E.LIdemPf.LIdem_of
theorem a10 : LateralTheory.E.t_E1Cut.HensIdem := LateralTheory.E.HensIdemCut.goal_of a0 a1 a8 a9

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.HensIdem := a10

end UpperTheory.Et.HenselianIdempotents
