module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGaugeFiniteExtension
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_integral_gauge_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)), ∃ (N' : GlobalTheory.Ex.NumD (Kb R)) (ν' : GlobalTheory.Ex.NumOf D.toPre (Kb R) N') (q' : N'.QT (m ^ 2)) (S : Subalgebra R (Kb R)), ν'.th = ν.th ∧ ν'.QPt p q' ∧ Module.Finite R S ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x'' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.θ x x' x'' : Kb R) ∈ S ∧ (((N'.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.σ x : Kb R) ∈ S ∧ (((N'.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ χ, N'.th (N'.c χ * (q'.1.2 ^ m).b) ∈ S) ∧ (∀ χ, (N'.ψ χ : Kb R) ∈ S) ∧ ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N'.ψ χ}.Finite := by
  first | exact @GlobalTheory.FinGauge.gauge | exact GlobalTheory.FinGauge.gauge | (intros; apply GlobalTheory.FinGauge.gauge <;> assumption)
