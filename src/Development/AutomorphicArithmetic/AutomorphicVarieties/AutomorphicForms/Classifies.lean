module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

noncomputable section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N

namespace UpperTheory.V.Af

structure TrData (q e : ℕ) where

  S : Type
  fin : Finite S

  t : S → ℂ
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ u : S ≃ S, ∀ s, t (u s) = σ (t s)
  bd : ∀ s, ‖t s‖ ≤ 3
  int : ∀ s, IsIntegral ℤ ((q : ℂ) ^ e * t s)

instance {q e : ℕ} : Inhabited (TrData q e) :=
  ⟨⟨Empty, inferInstance, fun s => s.elim, fun _ => ⟨.refl _, fun s => s.elim⟩, fun s => s.elim, fun s => s.elim⟩⟩

namespace TrData

variable {q e : ℕ}

def Classifies {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (D : TrData q e) (ι : Qbar l ≃+* ℂ) (g : Γ)
    (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, (r.1 g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace = ι.symm (D.t (cl r))

def sum (D D' : TrData q e) : TrData q e where
  S := D.S ⊕ D'.S
  fin := by have := D.fin; have := D'.fin; infer_instance
  t := Sum.elim D.t D'.t
  conj σ := by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨u', hu'⟩ := D'.conj σ
    exact ⟨u.sumCongr u', fun s => by cases s <;> simp [hu, hu']⟩
  bd s := by cases s; exacts [D.bd _, D'.bd _]
  int s := by cases s; exacts [D.int _, D'.int _]

theorem card_sum (D D' : TrData q e) : Nat.card (D.sum D').S = Nat.card D.S + Nat.card D'.S := by
  have := D.fin; have := D'.fin
  exact Nat.card_sum

end TrData

end UpperTheory.V.Af
