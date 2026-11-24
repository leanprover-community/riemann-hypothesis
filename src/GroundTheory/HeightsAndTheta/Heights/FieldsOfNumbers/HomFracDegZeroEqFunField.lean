module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PfContractedHypothesesExample
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

section

variable {F : Type*} [Field F] {K : Type*} {ι : K → Type*}

theorem relDim_eq_iff_hasRelDim [Fintype K] (I : Ideal (MRing ι F)) (n : ℕ) :
    relDim I = (n : WithBot (WithTop ℤ)) ↔ IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim I n := by
  unfold relDim IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x
  have e1 : ((n : ℕ) : WithBot (WithTop ℤ)) = some (some (n : ℤ)) := rfl
  have e2 : ((n + Fintype.card K : ℕ) : WithBot ℕ∞) = some (some (n + Fintype.card K)) := rfl
  rw [e1, e2]
  rcases x with _ | _ | e
  · simp [WithBot.map]
  · simp only [WithBot.map, WithTop.map, Option.map]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · simp only [WithBot.map, WithTop.map, Option.map]
    constructor
    · intro h
      have h1 : (e : ℤ) - Fintype.card K = n := Option.some.inj (Option.some.inj h)
      have h2 : e = n + Fintype.card K := by omega
      rw [h2]
      exact rfl
    · intro h
      have h1 : e = n + Fintype.card K := Option.some.inj (Option.some.inj h)
      subst h1
      congr 2
      push_cast
      ring

variable [DecidableEq K]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
