module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.FrTruncFixIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.KillAddVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PsiCover
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
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpAct

@[expose] public section

namespace GlobalTheory

open Formalism.MainNotions.ModuliIntegralCharts.H1

theorem harmonicValue_chart_independent : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := by
  have hAct : ExpActOfSt := by
    refine expActOf_of_eig ?_
    intro E _ _ _ H Dw l Xo c _ S _ _ _ y C a ℓ i
    exact EigDir.linEig_holds E H Dw l Xo c S y C a ℓ i
  refine chartIndep2_verb ?_ (GlobalTheory.BalancedTwist.frTruncFix_iff.mp frTruncFix_holds) germFix_holds (harmInv_of hAct)
  refine chartIndepTrunc_of (expChartOf_of hAct) (ExpGauge.expGaugeOf_of hAct) tie_holds ExpUniqChart.expUniqTan
    (gaugeUniq_of_global globalFns_holds) (killAddVal_of ?_)
  intro E _ _ _ H
  exact psiCover_holds H

end GlobalTheory
