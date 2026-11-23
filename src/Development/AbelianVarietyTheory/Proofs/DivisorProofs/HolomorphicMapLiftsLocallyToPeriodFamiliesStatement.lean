module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamilies
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (b₀ : Fin m → ℂ) P₀ e₀, 0 < N → (∀ a, F.eta a ^ N = 1) → LocallyOfFiniteType F.s → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → UnifAt F (RingHom.id ℂ) ρ N D' t P₀ (y b₀) e₀ → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ρ B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b) := by
  first | exact @GlobalTheory.PELU.holomorphic_map_lifts_to_periods | exact GlobalTheory.PELU.holomorphic_map_lifts_to_periods | (intros; apply GlobalTheory.PELU.holomorphic_map_lifts_to_periods <;> assumption)
