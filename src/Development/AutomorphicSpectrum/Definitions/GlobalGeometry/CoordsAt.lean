module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def InChart (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type} (x : κ → Ω) (c : κ) (p : Cpt ξ) : Prop :=
  x c ≠ 0 ∧ ∀ c', x c' / x c ∈ regAt ξ p

structure CoordTie (o : Type) [CommRing o] [Algebra o Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type}
    (x : κ → Ω) : Prop where
  gen : IsCptGen ξ
  cover : ∀ p : Cpt ξ, ∃ c, InChart ξ x c p
  affine : ∀ c, x c ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧
    ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩
  ring : ∀ c, x c ≠ 0 → ∀ a : Ω, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔
    ∀ p : Cpt ξ, InChart ξ x c p → a ∈ regAt ξ p

variable {R : Type} [CommRing R] [IsLocalRing R]

def centre (z : Spec (CommRingCat.of R) ⟶ X) : X := z (IsLocalRing.closedPoint R)

def ValAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (s : X.presheaf.stalk (centre z)),
    genMap ξ ⟨centre z, h⟩ s = a ∧ (Scheme.stalkClosedPointTo z).hom s = r

def CoordsAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω)
    (z : Spec (CommRingCat.of R) ⟶ X) (w : (Σ k, ι k) → R) : Prop :=
  (∀ k, ∃ c, IsUnit (w ⟨k, c⟩)) ∧ ∀ k c, IsUnit (w ⟨k, c⟩) → y ⟨k, c⟩ ≠ 0 ∧
    ∀ i, ∃ r : R, ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c⟩) r ∧ w ⟨k, i⟩ = r * w ⟨k, c⟩

def InFibre (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : ℕ) (q : Cpt ξ) : Prop := ¬ unitAt ξ q (p : Ω)

end GlobalTheory.CompanionTheory.Ar
