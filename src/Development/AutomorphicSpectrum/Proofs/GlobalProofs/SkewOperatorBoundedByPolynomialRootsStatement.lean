module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOperatorBoundedByPolynomialRoots
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

@[expose] public section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.skew_operator_bounded_by_polynomial_roots :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (ι : M →ₗ[ℂ] H), Function.Injective ι → ∀ T : Module.End ℂ M,
      (∀ x y, ⟪ι (T x), ι y⟫_ℂ = -⟪ι x, ι (T y)⟫_ℂ) →
      ∀ m : Polynomial ℂ, m ≠ 0 → ∀ κ : ℝ, 0 ≤ κ → (∀ r ∈ m.roots, ‖r‖ ≤ κ) →
      ∀ x, Polynomial.aeval T m x = 0 → ‖ι (T x)‖ ≤ κ * ‖ι x‖ :=
  GlobalTheory.CompanionTheory.SkewSpec.norm_le_of_aeval_eq_zero
