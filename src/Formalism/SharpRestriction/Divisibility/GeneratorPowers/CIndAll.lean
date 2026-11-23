module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndEnc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerbB
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.KillAddVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEigPf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open ReciprocityTheory.ChartRestriction.G.Out NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem chartIndep2_of_open (hGauge : ExpGaugeOfSt) (hKill : KillAddValSt) (hGlob : GlobalFnsSt)
    (hFix : FrTruncFixSt) (hInv : HarmInvSt) : ChartIndepSt2 :=
  chartIndep2_of_fix
    (chartIndepTrunc_of (expChartOf_of (expActOf_of linEigSt_holds)) hGauge tie_holds ExpUniqChart.expUniqTan
      (gaugeUniq_of_global hGlob) hKill)
    hFix germFix_holds hInv

theorem chartIndep2_of_open' (hGauge : ExpGaugeOfSt) (hPsi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E), PsiCoverSt H) (hGlob : GlobalFnsSt) (hFix : FrTruncFixSt) (hInv : HarmInvSt) : ChartIndepSt2 :=
  chartIndep2_of_open hGauge (killAddVal_of hPsi) hGlob hFix hInv

theorem chartIndep2_of_open'' (hGauge : ExpGaugeOfSt) (hGlob : GlobalFnsSt) (hFix : FrTruncFixSt)
    (hInv : HarmInvSt) : ChartIndepSt2 :=
  chartIndep2_of_open' hGauge (fun _ _ _ _ H => psiCover_holds H) hGlob hFix hInv

theorem chartIndep2_of_gauge (hGauge : ExpGaugeOfSt) (hGlob : GlobalFnsSt) (hFix : FrTruncFixSt) : ChartIndepSt2 :=
  chartIndep2_of_open'' hGauge hGlob hFix (harmInv_of (expActOf_of linEigSt_holds))

end Formalism.MainNotions.ModuliIntegralCharts.H1
