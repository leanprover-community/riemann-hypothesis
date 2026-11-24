module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem osgood : _root_.ReciprocityTheory.AnForm.Osgood.OsgoodStatement := by
  intro e U f hU hf z₀ hz₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have hs : 0 < r / 2 := half_pos hr
  have hcl : Metric.closedBall z₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hd : ∀ ζ ∈ Metric.closedBall z₀ (r / 2), DifferentiableAt ℂ f ζ :=
    fun ζ hζ => hf.differentiableAt (hU.mem_nhds (hcl hζ))
  set L := ReciprocityTheory.AnForm.Osgood.fctlCLM z₀ hs f hd
  have hg : AnalyticAt ℂ (fun z => ((2 * (Real.pi : ℂ) * Complex.I) ^ e)⁻¹ *
      L (ReciprocityTheory.AnForm.Osgood.kern z₀ (r / 2) z)) z₀ :=
    analyticAt_const.mul ((L.analyticAt _).comp (ReciprocityTheory.AnForm.Osgood.kern_analyticAt z₀ hs))
  refine hg.congr ?_
  filter_upwards [Metric.ball_mem_nhds z₀ hs] with z hz
  rw [ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hs hd hz]
  exact inv_mul_cancel_left₀ (pow_ne_zero _ Complex.two_pi_I_ne_zero) _

end ReciprocityTheory.ChartRestriction.G.Geo
