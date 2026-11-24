module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffCurvatureCompHolomorphic
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

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_curvature_comp_holomorphic : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → MContDiffAt 2 G (φ w) → IsUnit (G (φ w)).det → mixTop (fun _ => curvAt (fun x => G (φ x)) w) = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * mixTop fun _ => curvAt G (φ w) := by
  first | exact @GlobalTheory.GoodTop.mixTop_curvAt_comp_holo | exact GlobalTheory.GoodTop.mixTop_curvAt_comp_holo | (intros; apply GlobalTheory.GoodTop.mixTop_curvAt_comp_holo <;> assumption)
