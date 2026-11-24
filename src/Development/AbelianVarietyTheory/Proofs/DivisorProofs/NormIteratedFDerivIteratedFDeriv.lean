module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem norm_iteratedFDeriv_iteratedFDeriv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by
  induction n generalizing j with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.zero_add]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      norm_iteratedFDeriv_fderiv, ih (j + 1)]
    rw [show n + (j + 1) = n + 1 + j by omega]

end GlobalTheory
