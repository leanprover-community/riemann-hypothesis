module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff ComplexOrder

noncomputable section

def ev {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) : ℝ :=
  (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) / r ^ 2

def PolarStatement (n : ℕ) : Prop :=
  1 ≤ n → ∀ a b : ℝ, 0 < a → a ≤ b →
    ∫⁻ y in {y : V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}, ENNReal.ofReal ((‖y‖ ^ 2) ^ (-(n : ℝ))) =
      ENNReal.ofReal (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) * Real.log (b / a))

def CovStatement (n : ℕ) : Prop :=
  ∀ (W : Set (V n)) (G : V n → V n) (f : V n → ℝ≥0∞), IsOpen W → DifferentiableOn ℂ G W →
    Set.InjOn G W → Measurable f →
    ∫⁻ y in G '' W, f y =
      ∫⁻ y in W, ENNReal.ofReal (‖LinearMap.det (fderiv ℂ G y : V n →ₗ[ℂ] V n)‖ ^ 2) * f (G y)

end

end ReciprocityTheory.L2DbarEstimates.I
