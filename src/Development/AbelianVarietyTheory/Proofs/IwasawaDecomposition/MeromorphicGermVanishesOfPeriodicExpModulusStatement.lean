module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeromorphicGermVanishesOfPeriodicExpModulus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem _root_.GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus : ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  first | exact @GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic | exact GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic | (intros; apply GlobalTheory.ShFam.BdArc.tendsto_zero_of_norm_eq_mul_exp_periodic <;> assumption)
