module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
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

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module GlobalTheory.CompanionTheory.Ar.BT

abbrev LevGrp (La : Type) [AddCommGroup La] (p n : ℕ) : Type :=
  Multiplicative (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La)))

def lev {La : Type} [AddCommGroup La] (p n : ℕ) (a : La) : LevGrp La p n :=
  Multiplicative.ofAdd (Submodule.Quotient.mk a)

structure OrdTower (p : ℕ) (O : Type) [CommRing O] (La : Type) [AddCommGroup La]
    (L : Type) [AddCommGroup L] [Module O L] where

  A : ∀ n, Subalgebra O (LevGrp La p n → O)
  hopf : ∀ n, IsHopfOrder (A n)
  res_iff : ∀ n (g : LevGrp La p n → O),
    g ∈ A n ↔ ∃ f ∈ A (n + 1), ∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))
  ker_res : ∀ n (f : A (n + 1)), (∀ a : La, f.1 (lev p (n + 1) (p • a)) = 0) →
    f ∈ Ideal.span {g : A (n + 1) | ∃ h ∈ A (n + 1), ∀ t, g.1 t = h (t ^ p ^ n) - h 1}

  der : ∀ n, (LevGrp La p n → O) → Module.Dual O L → Prop
  der_ex : ∀ n, ∀ f ∈ A n, ∃ w, der n f w
  der_unique : ∀ n f w w', der n f w → (der n f w' ↔ ∃ u : Module.Dual O L, w' = w + (p ^ n) • u)
  der_onto : ∀ n w, ∃ f ∈ A n, der n f w
  der_add : ∀ n f g w w', der n f w → der n g w' → der n (f + g) (w + w')
  der_mul : ∀ n f g w w', der n f w → der n g w' → der n (f * g) (f 1 • w' + g 1 • w)
  der_const : ∀ n (r : O), der n (fun _ => r) 0
  der_zero : ∀ n (f : augIdeal (A n)), der n f.1.1 0 → (f : A n) ∈ augIdeal (A n) ^ 2
  der_res : ∀ n f g w, der (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → der n g w

namespace OrdTower

variable {p : ℕ} {O : Type} [CommRing O] {La : Type} [AddCommGroup La]
  {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

def Acts (φ : La →+ La) (dφ : L →ₗ[O] L) : Prop :=
  ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) →
    (f ∈ X.A n → g ∈ X.A n) ∧ ∀ w, X.der n f w → X.der n g (w ∘ₗ dφ)

def PairingExtends (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ) : Prop :=
  ∀ n, ∃ s ∈ prodSpan (X.A n), ∀ a b, s (lev p n a, lev p n b) = ((ζ n ^ B a b : Oˣ) : O)

structure Realises [Fact p.Prime] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) : Prop where
  res : ∀ n (f : G.A (n + 1)) (a : La), (e n (G.res n f)).1 (lev p n a) = (e (n + 1) f).1 (lev p (n + 1) (p • a))
  pt : ∀ (a : La) n (f : G.A n), (τ a).pt n f = (e n f).1 (lev p n a)

end OrdTower

end GlobalTheory.CompanionTheory.Ar.HT
