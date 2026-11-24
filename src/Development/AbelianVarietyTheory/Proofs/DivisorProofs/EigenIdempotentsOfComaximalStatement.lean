module

public import Mathlib.RingTheory.Ideal.Span
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIdempotentsOfComaximal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u

theorem _root_.GlobalTheory.T.exists_eigen_idempotents_of_comaximal : ∀ {C : Type} [CommRing C] {A : Type} [CommRing A] {W : Type u} [AddCommGroup W] [Module C W]
  (σ : A →+* Module.End C W) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∃ e : Fin a → Module.End C W,
    (∀ i (T : Module.End C W), (∀ c, T * σ c = σ c * T) → T * e i = e i * T) ∧
    (∀ i w, (∀ c, σ c w = χ i c • w) → e i w = w) ∧
    (∀ i j w, j ≠ i → (∀ c, σ c w = χ j c • w) → e i w = 0) := by
  first | exact @GlobalTheory.eigenIdempotents_of_comaximal | exact GlobalTheory.eigenIdempotents_of_comaximal | (intros; apply GlobalTheory.eigenIdempotents_of_comaximal <;> assumption)
