module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionClassesDescendFiniteAlgebra
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

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsionClasses_descend_finite_algebra : ∀ (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (S : ValuationSubring F), (∀ x, x ∈ S ↔ IsIntegral O x) → ∀ (N : NumD F) (K₁ : IntermediateField (FractionRing O) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing O) K₁ → (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) → (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) → (∀ x ∈ A₀, N.th x ∈ K₁) → (∀ χ, (N.ψ χ : F) ∈ K₁) → (∀ x y u, S.valuation (N.θ x y u : F) = 1) → (∀ x, S.valuation (N.σ x : F) = 1) → (∀ x, N.th x ∈ S) → (∀ χ, S.valuation (N.ψ χ : F) = 1) → ∀ (Ix : Type) [Finite Ix] (k : Ix → ℕ) (p : ∀ i, N.QT (k i)), (∀ i, 0 < k i) → (∀ i, (p i).1.2.b ∈ A₀) → ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∃ (N₀ : NumD O₁) (I : NumD.Hom O₁.val.toRingHom N₀ N), I.lam = 1 ∧ ∀ i (p' : N.QT (k i)), N.QEq (p i) p' → ∃ p₀ : N₀.QT (k i), p'.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p'.1.2 := by
  first | exact @GlobalTheory.Ex.TorsDesc.descend | exact GlobalTheory.Ex.TorsDesc.descend | (intros; apply GlobalTheory.Ex.TorsDesc.descend <;> assumption)
