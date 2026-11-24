module

public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.SA

open NumberField Module Formalism.BasicNotions

def CMStar (E : Type) [Field E] [StarRing E] : Prop :=
  ∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)

section AnySpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def NDLat (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : Prop :=
  M.FG ∧ ∀ x ∈ Submodule.span E (M : Set V), (∀ y ∈ M, h y x = 0) → x = 0




omit [NumberField E] [IsScalarTower (𝓞 E) E V] in
theorem orth_span (h : V →ₗ⋆[E] V →ₗ[E] E) {M : Submodule (𝓞 E) V} {x : V} (hx : ∀ y ∈ M, h y x = 0) :
    ∀ y ∈ Submodule.span E (M : Set V), h y x = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hx y hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]


omit [NumberField E] in
theorem ndLat_of_isLattice {h : V →ₗ⋆[E] V →ₗ[E] E} (hn : h.Nondegenerate) {M : Submodule (𝓞 E) V}
    (hM : Submodule.IsFullLattice E M) : NDLat h M :=
  ⟨hM.fg, fun x _ h0 => hn.2 x fun y => orth_span h h0 y (by rw [hM.span_eq_top]; trivial)⟩

end AnySpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

structure Amb (S : HSpace E) (k r : ℕ) : Prop where
  cm : CMStar E
  dim : finrank E S.V = k + 2 * r + 1
  neg : ∀ (τ : E →+* ℂ) (U : Submodule E S.V), (∀ x ∈ U, (τ (S.hT x x)).re ≤ 0) → finrank E U ≤ r + 1

section Diagonal

open Formalism.BasicNotions.Examples₂

def wittSigns (k r : ℕ) : Fin (k + 2 * r + 1) → Bool := fun i => decide ((i : ℕ) < r + 1)

def wittSpace (E : Type) [Field E] [NumberField E] [StarRing E] (k r : ℕ) : HSpace E :=
  stdSpace star_isIntegral (k + 2 * r + 1) (wittSigns k r) (k + r) (r + 1)

end Diagonal

end GlobalTheory.SA

end
