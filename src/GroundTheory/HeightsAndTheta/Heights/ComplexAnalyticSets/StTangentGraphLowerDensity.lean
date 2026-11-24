module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ENNReal

noncomputable section

def TangentGraphLowerDensity.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))) (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
    (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (w₀ : I₀ → ℂ),
    I₀.card = d → IsOpen Ω → IsOpen V → w₀ ∈ Ω → DifferentiableOn ℂ g Ω →
    (∀ w ∈ Ω, frameProj b I₀ (g w) = w) → S ∩ V = g '' Ω →
    (∀ j ∉ I₀, fderiv ℂ (fun w => inner ℂ (b j) (g w)) w₀ = 0) →
    ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ρ ∈ Set.Ioo (0 : ℝ) r₀,
      ENNReal.ofReal (θ * ρ ^ (2 * d)) *
          μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) ≤
        μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball (g w₀) ρ)

theorem TangentGraphLowerDensity.unitBall_pos (d : ℕ) :
    0 < μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
  have h : ((2 * d : ℕ) : ℝ) = ((Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℕ) : ℝ) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin d)), Complex.finrank_real_complex,
      finrank_euclideanSpace_fin]
  rw [h]
  exact Metric.isOpen_ball.measure_pos _ ⟨0, Metric.mem_ball_self one_pos⟩

end

end GroundTheory.Heights₂.Heights
