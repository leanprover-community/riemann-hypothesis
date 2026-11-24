module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDimensionalFieldDegenerationValues
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_finiteDimensional_field_degenerationValues : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra.IsAlgebraic (FractionRing R) F] (N : NumD F) (_ : NumOf D F N) (T : Set N.A), T.Finite → ∃ (K₁ : IntermediateField (FractionRing R) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing R) K₁ ∧ (∀ x ∈ T, x ∈ A₀) ∧ (∀ χ, N.c χ ∈ A₀) ∧ (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) ∧ (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) ∧ (∀ x ∈ A₀, N.th x ∈ K₁) ∧ ∀ χ, (N.ψ χ : F) ∈ K₁ := by
  first | exact @GlobalTheory.FiniteValues.exists_finite_field_of_values | exact GlobalTheory.FiniteValues.exists_finite_field_of_values | (intros; apply GlobalTheory.FiniteValues.exists_finite_field_of_values <;> assumption)
