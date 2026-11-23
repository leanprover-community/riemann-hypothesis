module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexLinearOfPureTypesFiniteIndex
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
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_complexLinear_of_pure_types_finite_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La) (N : ℕ), 0 < N → (∀ v : D.La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) → (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  first | exact @GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index | exact GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index | (intros; apply GlobalTheory.CompRat.exists_complex_linear_of_pure_types_of_index <;> assumption)
