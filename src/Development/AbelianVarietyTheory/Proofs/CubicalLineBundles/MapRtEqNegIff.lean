module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem map_rt_eq_neg_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {R : Type} [CommRing R]
    [CharZero R] {ρ : R} (hρ : ρ ^ 2 = -(H.d : R)) {k : Type} [Field k] (β : R →+* k) (hβ : Function.Injective β)
    (τ : 𝓞 E →+* k) : τ H.rt = β (-ρ) ↔ τ H.rt ≠ β ρ := by
  have h1 : (τ H.rt) ^ 2 = (β ρ) ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, hρ]; simp
  have h2 : β (-ρ) ≠ β ρ := by
    intro h
    have h3 : -ρ = ρ := hβ h
    have h4 : ((2 * H.d : ℕ) : R) = 0 := by
      push_cast
      linear_combination 2 * hρ + ρ * h3
    have h5 : 2 * H.d = 0 := Nat.cast_eq_zero.mp h4
    have := H.d_prime.pos
    omega
  constructor
  · intro h h'
    exact h2 (h.symm.trans h')
  · intro h
    rw [map_neg]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left h

theorem hasType_neg_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [CharZero R] (G : Over (Sp R)) [GrpObj G] (act : OAct (𝓞 E) G) (ρ : R) (p q : ℕ), ρ ^ 2 = -(H.d : R) → (HasType H act ρ p q ↔ HasType H act (-ρ) q p) := by
  intro E _ _ _ H R _ _ G _ act ρ p q hρ
  unfold HasType
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun β =>
    forall_congr' fun hβ => forall_congr' fun τ => ?_
  have h := map_rt_eq_neg_iff H hρ β hβ τ
  rw [ne_eq (τ H.rt) (β (-ρ)), h, not_not]
  exact and_comm

end GlobalTheory.CM
