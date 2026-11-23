module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsInCoordinatesFromBasePullDeg
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem _root_.GlobalTheory.T.periodsInCoordinates_fromBase_pullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁), Function.Injective ρ → ∀ (Q : DegPre V) (D : DegPre V₁) (p : IsPullDeg ρ Q D) (τ₀ : GlobalTheory.UChart.Gens Q) (N : ℕ) (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) (ε₁ : Fin N → LinearMap.BilinForm ℤ D.X), (∀ k a b, ε₁ k a b = ε k (p.xe a) (p.xe b)) → GlobalTheory.UChart.TauIn Q τ₀ s ε → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), GlobalTheory.UChart.FromBase Q τ₀ ib → ∃ τ₁ : GlobalTheory.UChart.Gens D, GlobalTheory.UChart.TauIn D τ₁ (fun k => ρ (s k)) ε₁ ∧ GlobalTheory.UChart.FromBase D τ₁ (ρ.comp ib) := by
  first | exact @GlobalTheory.USep.tauIn_fromBase_pull | exact GlobalTheory.USep.tauIn_fromBase_pull | (intros; apply GlobalTheory.USep.tauIn_fromBase_pull <;> assumption)
