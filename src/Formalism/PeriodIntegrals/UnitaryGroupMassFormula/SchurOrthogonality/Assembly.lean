module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat
public import Formalism.PeriodIntegrals.SchurFock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params

@[expose] public section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory

theorem schurFock_of_steps (hB : HaarU) (hC : SchurOrth) : PI.SchurFock := by
  intro N lam s hs hbd
  obtain ⟨μ, hμ⟩ := hB N
  have hprob := hμ.1
  have hae := hμ.2.1
  rw [hC N lam μ hμ s hs]
  have hint : ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ 1 := by
    calc ∫ x, ‖evalM x s‖ ^ 2 ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ := by
          apply integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (integrable_const 1)
          filter_upwards [hae] with x hx
          exact pow_le_one₀ (norm_nonneg _) (hbd x hx)
      _ = 1 := by simp
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) hint

end PI.WSF
