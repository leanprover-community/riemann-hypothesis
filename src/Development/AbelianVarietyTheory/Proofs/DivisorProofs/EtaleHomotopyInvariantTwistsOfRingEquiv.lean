module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.HInvIso

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact CategoryTheory.Functor.map_id _ _

theorem pull_spMap_bij {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext a; simp
    rw [this, spMap_id', pull_id]
  have h2 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by ext a; simp
    rw [this, spMap_id', pull_id]
  exact ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩

end GlobalTheory.EtC.HInvIso

namespace GlobalTheory.EtC


open HInvIso in
theorem hInv_of_ringEquiv : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], (A ≃+* B) → HInv q A → HInv q B := by
  intro q _ A B _ _ e hA i n
  have hsq : (Polynomial.C : B →+* Polynomial B).comp (e : A →+* B) =
      ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B).comp Polynomial.C := by
    ext a; simp
  have hpull : ∀ x, pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) =
      pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n x) := by
    intro x
    rw [← pull_comp, ← pull_comp, ← spMap_comp', ← spMap_comp', hsq]
  have hc : Function.Bijective ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) := by
    have : ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) =
      (pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n) ∘
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n) := funext hpull
    rw [this]
    exact (pull_spMap_bij _ _ n).comp (hA i n)
  exact (Function.Bijective.of_comp_iff _ (pull_spMap_bij e _ n)).1 hc

end GlobalTheory.EtC
