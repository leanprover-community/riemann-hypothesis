module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsPolyGrowthOfBoundedCoisotropic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.periods_polyGrowth_of_bounded_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic | exact GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic <;> assumption)
