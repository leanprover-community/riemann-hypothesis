module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPeriodEqPeriodOverThickening
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.taylor_period_eq_period_over_thickening_alt : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B D : Type} [CommRing B] [CommRing D] [Algebra ℂ D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (u₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → 0 ∈ F.V → (∀ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, u₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (π : D →ₐ[ℂ] ℂ), IsNilpotent (RingHom.ker π) → ∀ {J : Ideal D} (dl : DividedPowers J), (∀ d ∈ J, π d = 0) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap (π : D →+* ℂ) → ∀ (n : IsMor (dp0 B) s dl s' j φ₀) (ψ : X₀ ⟶ X₀) (k : IsMor (dp0 ℂ) s₀ dl s' (algebraMap ℂ D) ψ), ψ = 𝟙 X₀ → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ {io : Type} (S : Finset io) (d : io → D) (a : io → FirstDeRham s₀) (p : io → Λ → ℂ) (p' : io → (Λ →+ Hol F₀.V)), (∀ i l, p' i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod u₀ (a i) (p' i)) → n.pull1 c = ∑ i ∈ S, d i • k.pull1 (a i) → ∀ l, ∑ i ∈ S, d i * algebraMap ℂ D (p i l) = taylor N t (per l).fn := by
  exact @GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening
