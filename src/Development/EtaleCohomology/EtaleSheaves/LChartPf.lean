module

public import Development.EtaleCohomology.EtaleSheaves.LEtaleLiftPf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace LateralTheory.E.LChartPf

def IdemLiftInt (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def LIdemLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IdemLiftInt A I

def LSurjChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ → IdemLiftInt A I →
  ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Function.Surjective (algebraMap A (Localization.Away g))

theorem isStandardEtale_of_surjective (A : Type) [CommRing A] (A' : Type) [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (g : A') (hs : Function.Surjective (algebraMap A (Localization.Away g))) :
    Algebra.IsStandardEtale A (Localization.Away g) :=
  Algebra.IsStandardEtale.of_surjective (S := A) (Algebra.ofId A _) hs

theorem LChart_of (h1 : LIdemLift) (h2 : LSurjChart) : LateralTheory.E.LEtaleLiftPf.LChart := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hs⟩ := h2 A I (by simpa only [Ideal.jacobson_bot] using
    (HenselianRing.jac : I ≤ Ring.jacobson A)) (h1 A I) A' φ
  exact ⟨g, hg, isStandardEtale_of_surjective A A' g hs⟩

end LateralTheory.E.LChartPf
