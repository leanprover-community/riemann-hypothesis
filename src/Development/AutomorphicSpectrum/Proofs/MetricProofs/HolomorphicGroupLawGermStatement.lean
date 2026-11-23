module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicGroupLawGerm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Set

theorem _root_.GlobalTheory.T.holomorphic_lattice_family_local : ∀ (n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Countable Λ] (B : Set (Fin n → ℂ)), IsOpen B → Convex ℝ B → ∀ (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ) (e : Λ → Λ → ℝ), (∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) N) ∧ ∀ b ∈ N, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y) → ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_global_marking_of_local | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_global_marking_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_global_marking_of_local <;> assumption)
