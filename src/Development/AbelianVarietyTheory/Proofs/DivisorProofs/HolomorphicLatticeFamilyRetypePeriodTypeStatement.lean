module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicLatticeFamilyRetypePeriodType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.holomorphic_lattice_family_retype_periodType : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (D : PLat O bar) (m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B → b₀ ∈ B → (∀ x, DifferentiableOn ℂ (fun b => P b x) B) → IsPeriod D ρ (P b₀) → (∀ b ∈ B, Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ ∀ a : O, ∃ M : Matrix (Fin g) (Fin g) ℂ, ∀ x, P b (a • x) = M *ᵥ P b x) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ (a : O) x, h b *ᵥ P b (a • x) = ρ a *ᵥ (h b *ᵥ P b x) := by
  first | exact @GlobalTheory.PELU.Retype.retype | exact GlobalTheory.PELU.Retype.retype | (intros; apply GlobalTheory.PELU.Retype.retype; all_goals assumption)
