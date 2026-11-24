module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleExcisionVanishingUnderRefinement
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

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleExcision_vanishing_under_refinement : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ) (x : Ht q (sp A) (n + 1) i), pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x = 0 → pull _ (spMap (algebraMap A A')) _ _ x = 0 → ∃ w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i, ∀ (g : A), IsCoprime f g → ∀ (A₂ C : Type) [CommRing A₂] [CommRing C] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂] [Algebra A C], IsExcisionNbhd A A₂ f → IsUnit (algebraMap A A₂ g) → IsExcisionNbhd A C g → ∀ a : Ht q (sp (Localization.Away (f * g))) n i, pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → (∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap A _) = (algebraMap A₂ _).comp (algebraMap A A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a) → x = 0 := by
  first | (exact @GlobalTheory.EtC.mvRefine_main) | (exact GlobalTheory.EtC.mvRefine_main) | (intros; apply GlobalTheory.EtC.mvRefine_main <;> assumption)
