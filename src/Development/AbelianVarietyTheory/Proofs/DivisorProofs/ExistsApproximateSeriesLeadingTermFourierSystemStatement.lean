module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximateSeriesLeadingTermFourierSystem
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

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_approximate_series_leading_term_fourierSystem : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O), BddAct bar → ∀ (q : ℕ) (φ : InvFun O), IsPolFan bar q φ → ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (N₁ : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y₀ : Φ.Y) (γ : Fin (Φ.m y₀) → LinearMap.BilinForm ℤ (Φ.X y₀)) (M : ℕ), 1 ≤ M → (∀ i, Φ.δ y₀ i = (M : ℤ) • γ i) → ∀ (d l : ℕ) (a : Fin l × Fin s → Φ.X y₀), Dominant bar φ d N₁ W γ a → ∀ (c : Fin l → Φ.Q) (e : ℕ), ∃ f : A, Φ.OrdGe φ d e f ∧ Φ.Leads y₀ a c e f := by
  first | exact @GlobalTheory.Poinc.approx_of_vsys | exact GlobalTheory.Poinc.approx_of_vsys | (intros; apply GlobalTheory.Poinc.approx_of_vsys <;> assumption)
