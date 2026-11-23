module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
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
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX

@[expose] public section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal

theorem _root_.GlobalTheory.T.cone_degree_growth_chowForm_integrality : (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → ∀ δ : ℕ, IsImageDeg ev D δ → growth D (fun k => hilb ev (a * k)) = (a : ℝ≥0∞) ^ D * δ) ∧ (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → growth D (fun k => hilb ev (a * k)) ≠ 0 → growth D (fun k => hilb ev (a * k)) ≠ ⊤ → ∃ δ : ℕ, IsImageDeg ev D δ) ∧ (∀ (K V Ω : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D a : ℕ), 1 ≤ a → ∀ S : ℕ → Submodule K Ω, (∀ k, ∀ t ∈ S k, IsIntDeg ev (a * k) t ∧ IsRatio ev (a * k) t) → growth D (fun k => Cardinal.toENat (Module.rank K (S k))) ≤ growth D (fun k => hilb ev (a * k))) ∧ (∀ (K A : Type) [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] (σ : K →+* ℂ) (n k : ℕ) (w : Fin n → A) (s : A) (C : ℝ), (∀ φ : A →+* ℂ, φ.comp (algebraMap K A) = σ → ‖φ s‖ ≤ C * (1 + ∑ i, ‖φ (w i)‖) ^ k) → IsIntegral (Algebra.adjoin K (Set.range w)) s) := by
  first | exact @GlobalTheory.ConeDeg.degree_growth_integral | exact GlobalTheory.ConeDeg.degree_growth_integral | (intros; apply GlobalTheory.ConeDeg.degree_growth_integral <;> assumption)
