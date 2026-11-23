module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.TieLDB
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.Room

theorem assemble (K M P z s lc lL lr lR lo ld ln : ℝ) (hz : 1 ≤ z) (hP : z ≤ P) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hs : 1 ≤ s) (hc : lc ≤ K * z) (hL : lL ≤ M * P) (hr : lr ≤ K * z) (hR : lR ≤ z) (ho : lo ≤ K * z)
    (hd : ld ≤ K * z) (hn : ln ≤ M * P) :
    4 * Real.pi + (lc / 2 + lL + lr + lR) * s ≤ (17 + 2 * K + M) * P * s ∧
    ((1 + lo) / 2 + (1 / 2) * lL) * s ≤ (17 + 2 * K + M) * P * s ∧
    ld + ln ≤ (17 + 2 * K + M) * P := by
  have hKz : K * z ≤ K * P := mul_le_mul_of_nonneg_left hP (by linarith)
  have hKP : 0 ≤ K * P := by nlinarith
  have hMP : 0 ≤ M * P := mul_nonneg hM (by linarith)
  have hpi := Real.pi_le_four
  refine ⟨?_, ?_, ?_⟩
  · have h1 : lc / 2 + lL + lr + lR ≤ (1 + 2 * K + M) * P := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ s)
    have h3 : 1 ≤ P * s := by nlinarith
    nlinarith
  · refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    nlinarith
  · nlinarith

theorem log_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ x := Real.log_le_self hx

end GlobalTheory.ArcCM.Room
