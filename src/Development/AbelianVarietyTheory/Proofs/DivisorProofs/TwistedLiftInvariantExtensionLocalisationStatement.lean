module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLiftInvariantExtensionLocalisation
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.twisted_lift_invariantExtension_localisation : ∀ (A B A₂ : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [CommRing A₂] [IsLocalRing A₂] (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] (f : B →+* A₂), IsLocalHom (f.comp (algebraMap A B)) → (∀ y : A₂, ∃ b s : B, IsUnit (f s) ∧ y * f s = f b) → (∀ b : B, f b = 0 → ∃ s : B, IsUnit (f s) ∧ s * b = 0) → ∀ (V' : Type) [CommRing V'] [IsLocalRing V'] (e₁ : A →+* V') (β : B →+* V'), IsLocalHom e₁ → β.comp (algebraMap A B) = e₁ → ∃ ev₂ : A₂ →+* V', IsLocalHom ev₂ ∧ ev₂.comp (f.comp (algebraMap A B)) = e₁ := by
  first | exact @GlobalTheory.twisted_lift_to_localisation | exact GlobalTheory.twisted_lift_to_localisation | (intros; apply GlobalTheory.twisted_lift_to_localisation <;> assumption)
