module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMarkedLatticePeriodRepresentatives
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

theorem _root_.GlobalTheory.T.exists_finite_markedLattice_period_representatives : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → ∃ (n : ℕ) (Di : Fin n → PLat O bar) (t : ∀ i, Λ → (Di i).La), (∀ i, C (Di i) (t i) ∧ ∃ P, IsPeriod (Di i) ρ P) ∧ (∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w) ∧ ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j := by
  first | exact @GlobalTheory.PELU.exists_finite_representatives | exact GlobalTheory.PELU.exists_finite_representatives | (intros; apply GlobalTheory.PELU.exists_finite_representatives <;> assumption)
