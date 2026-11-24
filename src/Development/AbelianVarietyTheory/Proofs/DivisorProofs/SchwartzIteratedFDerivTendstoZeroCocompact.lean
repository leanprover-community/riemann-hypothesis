module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem schwartz_iteratedFDeriv_tendsto_zero_cocompact
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (j : ℕ) :
    Tendsto (fun z => iteratedFDeriv ℝ j f z) (cocompact E) (𝓝 0) := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  obtain ⟨C, -, hC⟩ := f.decay 1 j
  have hn : Tendsto (fun z : E => ‖z‖) (cocompact E) atTop := by first | exact tendsto_norm_cocompact_atTop | exact tendsto_norm_cocompact_atTop _
  have h0 : Tendsto (fun z : E => C / ‖z‖) (cocompact E) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [hn.eventually_gt_atTop 0] with z hz
  rw [le_div_iff₀ hz, mul_comm]
  simpa using hC z

end GlobalTheory
