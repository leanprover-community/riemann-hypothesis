module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem isDominant_one_and_mul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (J : Subgroup (GL (Fin N) k)) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N),
      IsDominant k N J d hd 1 ∧ ∀ t t' : Levi k (Bl d), IsDominant k N J d hd t →
        IsDominant k N J d hd t' → IsDominant k N J d hd (t * t') := by
  intro k _ _ _ _ N J h d hd
  refine ⟨⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ?_⟩, ?_⟩
  · simpa using hn
  · simpa using hn
  · simpa using hx
  · rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
    · have key := h1 _ (h1' n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := h2' _ (h2 n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := (h3 _ (h3' x hx).1).1
      convert key using 1
      group
    · have key := (h3' _ (h3 x hx).2).2
      convert key using 1
      group

end GlobalTheory.CompanionTheory.Lbc
