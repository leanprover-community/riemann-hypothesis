module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.ShuffleWords

variable {T : Type u}

theorem interleave_exchange {u v w : List T} (h : Interleave u v w) :
    ∀ {u' x : List T}, Interleave u' x v →
      ∃ v', Interleave u' v' w ∧ Interleave u x v' := by
  induction h with
  | nil =>
    intro u' x h'
    cases h'
    exact ⟨[], Interleave.nil, Interleave.nil⟩
  | @left a u v w _ ih =>
    intro u' x h'
    obtain ⟨v', h₁, h₂⟩ := ih h'
    exact ⟨a :: v', Interleave.right h₁, Interleave.left h₂⟩
  | @right a u v w _ ih =>
    intro u' x h'
    cases h' with
    | left h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨v', Interleave.left h₁, h₂⟩
    | right h' =>
      obtain ⟨v', h₁, h₂⟩ := ih h'
      exact ⟨a :: v', Interleave.right h₁, Interleave.right h₂⟩

theorem shuffle_swap {a b : List T} {us : List (List T)} {w : List T}
    (h : Shuffle (a :: b :: us) w) : Shuffle (b :: a :: us) w := by
  cases h with
  | cons hv hw =>
    cases hv with
    | cons hx hv =>
      obtain ⟨v', h₁, h₂⟩ := interleave_exchange hw hv
      exact Shuffle.cons (Shuffle.cons hx h₂) h₁

theorem shuffle_perm {T : Type u} (us us' : List (List T)) (w : List T)
    (h : Shuffle us w) (hp : us.Perm us') : Shuffle us' w := by
  induction hp generalizing w with
  | nil => exact h
  | cons a _ ih =>
    cases h with
    | cons hv hw => exact Shuffle.cons (ih _ hv) hw
  | swap a b l => exact shuffle_swap h
  | trans _ _ ih₁ ih₂ => exact ih₂ _ (ih₁ _ h)

end GlobalTheory.CompanionTheory.ShuffleWords
