module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreTail
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

open Polynomial

namespace GlobalTheory

theorem exists_dvr_localization_of_minimal_prime : ∀ {κ : Type} [Field κ] (R : Subring κ)
    [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R κ] (Q : Ideal R) [Q.IsPrime],
    Q ≠ ⊥ → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q) →
    ∃ W : ValuationSubring κ, IsDiscreteValuationRing W ∧ (∀ r : R, (r : κ) ∈ W) ∧
      (∀ r : R, r ∉ Q → (r : κ)⁻¹ ∈ W) ∧ (∀ r : R, r ∈ Q → r ≠ 0 → (r : κ)⁻¹ ∉ W) ∧
      (∀ w ∈ W, ∃ b s : R, s ∉ Q ∧ w = b / s) := by
  first
  | exact @_root_.GlobalTheory.AuxiliaryLemmaSecond.main
  | exact _root_.GlobalTheory.AuxiliaryLemmaSecond.main
  | (apply _root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AuxiliaryLemmaSecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AuxiliaryLemmaSecond.main ..)

end GlobalTheory
