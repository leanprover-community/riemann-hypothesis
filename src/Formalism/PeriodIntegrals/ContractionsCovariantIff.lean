module

public import Formalism.HermitianCurvature.StatementQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Matrix Finset

namespace PI

open Formalism.REAL Formalism.FourierDecayAlt.Q

def QnCovLin : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    Q * P = 1 → ∀ (a b : Fin t → Fin n) (u : ℂ),
      qminor (Econj E P Q) a b u =
        ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n,
          ((∏ k, P (c k) (a k)) * ∏ k, Q (b k) (d k)) • qminor E c d u

def QnCovDet : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    GlRel E → Q * P = 1 → P * Q = 1 → ∀ u : ℂ, qdet (Econj E P Q) u = qdet E u

def QnCovHat : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    GlRel E → Q * P = 1 → P * Q = 1 → ∀ (u : ℂ) (a β : Fin n → ℂ),
      chatA (Econj E P Q) u (Q *ᵥ a) (β ᵥ* P) = chatA E u a β

def QnCovHat2 : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    GlRel E → Q * P = 1 → P * Q = 1 → ∀ (u : ℂ) (a a' β β' : Fin n → ℂ),
      chat2A (Econj E P Q) u (Q *ᵥ a) (Q *ᵥ a') (β ᵥ* P) (β' ᵥ* P) = chat2A E u a a' β β'

theorem contractionsCovariant_iff : ContractionsCovariant ↔ QnCovDet ∧ QnCovHat ∧ QnCovHat2 := by
  unfold ContractionsCovariant QnCovDet QnCovHat QnCovHat2
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro A _ _ n E P Q hE hQP hPQ u
      exact (h A n E P Q hE hQP hPQ u 0 0 0 0).1
    · intro A _ _ n E P Q hE hQP hPQ u a β
      exact (h A n E P Q hE hQP hPQ u a 0 β 0).2.1
    · intro A _ _ n E P Q hE hQP hPQ u a a' β β'
      exact (h A n E P Q hE hQP hPQ u a a' β β').2.2
  · rintro ⟨h1, h2, h3⟩ A _ _ n E P Q hE hQP hPQ u a a' β β'
    exact ⟨h1 A n E P Q hE hQP hPQ u, h2 A n E P Q hE hQP hPQ u a β,
      h3 A n E P Q hE hQP hPQ u a a' β β'⟩

end PI
