module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.howeBall :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (c : ℤ) (ρ : ValueGroupWithZero E), 0 < ρ →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, howeSet n ϖ a c ⊆ ball n ρ := by
  intro E _ _ _ _ n ϖ hϖ c ρ hρ
  have h1 : valuation E (ϖ : E) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  have h0 : 0 < valuation E (ϖ : E) := by rw [hϖ]; exact uniformizer_pos
  haveI : MulArchimedean (ValueGroupWithZero E) := isRankLeOne_iff_mulArchimedean.1 inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 (Units.mk0 ρ hρ.ne')
  refine ⟨N + |c| * n, fun a ha g hg i j => (hg i j).trans ?_⟩
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  refine le_trans ?_ hN.le
  rw [← zpow_natCast]
  refine zpow_le_zpow_right_of_le_one₀ h0 h1.le ?_
  have hi := i.2
  have hj := j.2
  have h2 : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ n := by
    rw [abs_le]; constructor <;> omega
  have h3 : |c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))| ≤ |c| * n := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h4 := (abs_le.1 h3).1
  linarith
