module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicElementHomogRelation
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

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem _root_.GlobalTheory.T.algebraic_element_homog_relation : ∀ (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (i : Ω₀ →+* Ω) (α : Ω), Birational y₀ → (letI := i.toAlgebra; IsAlgebraic Ω₀ α) → ∃ (n : ℕ) (c : ℕ → MRing J₀) (a : K₀ → ℕ) (G : MRing J₀) (b : K₀ → ℕ), (∀ j, IsMultiHomog (c j) a) ∧ IsMultiHomog G b ∧ G ∉ mCoordIdeal y₀ ∧ (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * α ^ j = 0) ∧ ∀ w ∈ mcPts (mCoordIdeal y₀), eval w (map (Int.castRingHom ℂ) G) ≠ 0 → ∀ τ : ℂ, ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ (j - 1) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly | exact GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly | (intros; apply GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly <;> assumption)
