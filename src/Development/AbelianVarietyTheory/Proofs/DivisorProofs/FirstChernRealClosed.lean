module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm.FirstChern

open Filter Topology GlobalTheory.HermFrame GlobalTheory.Points
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder ComplexConjugate

theorem chernAt_exp_neg {n : ℕ} {u : V n → ℝ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    chernAt (fun x => (Matrix.of fun _ _ : Unit => ((Real.exp (-u x) : ℝ) : ℂ))) v 1 = ofValues (ddc u v) := by
  have h1 (G : V n → Matrix Unit Unit ℂ) : chernAt G v 1 = ofValues (chernOne G v) := by
    unfold chernAt ofValues GlobalTheory.GoodMetric.chernPoly chernOne
    rw [Matrix.coeff_charpolyRev_eq_neg_trace, Matrix.trace_neg, neg_neg, pow_one]

    simp only [Matrix.trace, Matrix.diag, GlobalTheory.GoodMetric.curvPoly, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, ← Algebra.smul_def, mul_smul, ← Finset.smul_sum, Finset.sum_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [h1]
  congr 1
  funext ξ η
  rw [chernOne_line (f := fun x => Real.exp (-u x)) (Real.contDiff_exp.contDiffAt.comp v hu.neg) (Real.exp_ne_zero _)
    (Eventually.of_forall fun _ => rfl)]
  simp only [Real.log_exp, ddc, leviForm_neg]
  simp

end GlobalTheory.LineForm.FirstChern
