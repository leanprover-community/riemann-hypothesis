module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ci.Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R]
  [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

theorem one (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 := ⟨h, 1, map_one _, map_one _⟩

theorem mul {a b : Ω} {r s : R} (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  obtain ⟨_, v, rfl, rfl⟩ := hb
  exact ⟨h, u * v, map_mul _ _ _, map_mul _ _ _⟩

theorem pow {a : Ω} {r : R} (ha : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨h, u, rfl, rfl⟩ := ha
  exact ⟨h, u ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem prod (h : genPt ξ ⤳ centre z) {ι : Type} (T : Finset ι) {a : ι → Ω} {r : ι → R}
    (ha : ∀ k, ValAt ξ z (a k) (r k)) : ValAt ξ z (∏ k ∈ T, a k) (∏ k ∈ T, r k) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact one h
  | insert k T hk ih => rw [Finset.prod_insert hk, Finset.prod_insert hk]; exact mul (ha k) ih

theorem mem {a : Ω} {r : R} (ha : ValAt ξ z a r) (h : genPt ξ ⤳ centre z) : a ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨_, u, rfl, -⟩ := ha
  exact ⟨u, rfl⟩

theorem of_mem {a : Ω} {h : genPt ξ ⤳ centre z} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨u, rfl⟩ := ha
  exact ⟨_, h, u, rfl, rfl⟩

theorem zpow {K : Type} [Field K] {z : Spec (CommRingCat.of K) ⟶ X} {a : Ω} {r : K} (ha : ValAt ξ z a r)
    (ha' : ValAt ξ z a⁻¹ r⁻¹) (n : ℤ) : ValAt ξ z (a ^ n) (r ^ n) := by
  cases n with
  | ofNat n => simpa using pow ha n
  | negSucc n => simpa only [zpow_negSucc, inv_pow] using pow ha' (n + 1)

end PositivityTheory.HtPt.Ci.Val
