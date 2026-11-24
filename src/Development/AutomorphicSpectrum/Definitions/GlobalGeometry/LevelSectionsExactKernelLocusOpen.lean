module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn
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

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def genFibre (O : Type) [CommRing O] [Algebra O Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Cpt ξ) :=
  {p | ∀ o : O, o ≠ 0 → unitAt ξ p (algebraMap O Ω o)}

def ConstClosed (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] : Prop :=
  ∀ a : Ω, IsAlgebraic O a → ∃ x y : O, y ≠ 0 ∧ a * algebraMap O Ω y = algebraMap O Ω x

def lineLat (A B : Lat ξ E) (p q : ℕ) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) : Lat ξ Ω := fun x =>
  Submodule.span (regAt ξ x) {t | ∃ f : Ω, IsCoeffAt A B p q a b x f ∧ t = f⁻¹}

def SplitModAt (A : Lat ξ E) (ϖ : Ω) {N : ℕ} (J : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω))) (x y : Cpt ξ) : Prop :=
  (∀ w ∈ A y, ∀ k, J x w k ∈ regAt ξ y ∧ (J x w k - J y w k) / ϖ ∈ regAt ξ y) ∧
    ∃ R : (Fin N → Ω) →ₗ[Ω] E, (∀ k, R (Pi.single k 1) ∈ A y) ∧ ∀ w ∈ A y, ∃ w' ∈ A y, R (J x w) = w + ϖ • w'

def ExactModLat (A B : Lat ξ E) (ϖ : Ω) (N : ℕ) : Prop :=
  ∃ J J' : Cpt ξ → (E →ₗ[Ω] (Fin N → Ω)), ∀ x : Cpt ξ, ¬ unitAt ξ x ϖ → ∃ U : X.Opens, x.1 ∈ U ∧
    ∀ y : Cpt ξ, y.1 ∈ U → ¬ unitAt ξ y ϖ → SplitModAt A ϖ J x y ∧ SplitModAt B ϖ J' x y ∧
      ∀ w ∈ A y, ∀ w' ∈ B y, dotProduct (J x w) (J' x w') / ϖ ∈ regAt ξ y

end GlobalTheory.CompanionTheory.Ar.Flat
