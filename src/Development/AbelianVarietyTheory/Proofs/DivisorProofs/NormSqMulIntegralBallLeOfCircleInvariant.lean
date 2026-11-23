module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory

theorem norm_sq_mul_integral_ball_le_of_circle_invariant :
    ∀ (n : ℕ) (δ : ℝ) (U : Set (V n)) (f : V n → ℂ) (W : V n → ℝ), 0 < δ → IsOpen U →
      closedBall 0 δ ⊆ U → DifferentiableOn ℂ f U → ContinuousOn W (closedBall 0 δ) →
      (∀ w, 0 ≤ W w) → (∀ (θ : ℂ) (w : V n), ‖θ‖ = 1 → W (θ • w) = W w) →
      ‖f 0‖ ^ 2 * ∫ w in ball (0 : V n) δ, W w ≤ ∫ w in ball (0 : V n) δ, ‖f w‖ ^ 2 * W w := by
  intro n δ U f W _ hU hsub hf hW hW0 hinv
  classical
  have hS : MeasurableSet (ball (0 : V n) δ) := measurableSet_ball
  have hWb : ContinuousOn W (ball (0 : V n) δ) := hW.mono ball_subset_closedBall
  set W' : V n → ℝ := (ball (0 : V n) δ).piecewise W (fun _ => 0) with hW'
  have hm : Measurable W' := hWb.measurable_piecewise continuousOn_const hS
  have heq : ∀ z ∈ ball (0 : V n) δ, W' z = W z := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  have h := enorm_pow_mul_lintegral_le_of_balanced (volume : Measure (V n)) hS balanced_ball_zero
    (φ := f) (fun z hz => hf.differentiableAt (hU.mem_nhds (hsub (ball_subset_closedBall hz))))
    (w := fun z => ENNReal.ofReal (W' z)) hm.ennreal_ofReal
    (fun c hc z hz => by
      have hz' : c • z ∈ ball (0 : V n) δ := by
        simpa [norm_smul, hc] using hz
      rw [heq _ hz', heq _ hz, hinv c z hc]) 2
  have e1 : ∫⁻ z in ball (0 : V n) δ, ENNReal.ofReal (W' z) =
      ∫⁻ z in ball (0 : V n) δ, ENNReal.ofReal (W z) :=
    setLIntegral_congr_fun hS fun z hz => by simp only [heq z hz]
  have e2 : ∫⁻ z in ball (0 : V n) δ, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (W' z) =
      ∫⁻ z in ball (0 : V n) δ, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (W z) :=
    setLIntegral_congr_fun hS fun z hz => by simp only [heq z hz]
  rw [e1, e2] at h
  have hfc : ContinuousOn f (closedBall 0 δ) := hf.continuousOn.mono hsub
  have hi : IntegrableOn W (ball (0 : V n) δ) :=
    (hW.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hi' : IntegrableOn (fun z => ‖f z‖ ^ 2 * W z) (ball (0 : V n) δ) :=
    (((hfc.norm.pow 2).mul hW).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  have h0 : ∀ z : V n, 0 ≤ ‖f z‖ ^ 2 * W z := fun z => mul_nonneg (by positivity) (hW0 z)
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg h0), ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hW0),
    ofReal_integral_eq_lintegral_ofReal hi' (Filter.Eventually.of_forall h0)]
  simpa [ENNReal.ofReal_mul, ENNReal.ofReal_pow] using h

end GlobalTheory
