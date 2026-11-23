module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh

private theorem simplePath_cons_iff {n : ℕ} (χ : Fin n → ℂ) (a : Fin n) (l : List (Fin n)) :
    SimplePath χ (a :: l) ↔ (∀ r, r ≠ a → χ r ≠ χ a) ∧ SimplePath (χ + Pi.single a 1) l :=
  Iff.rfl

theorem simplePath_ne {n : ℕ} (ss : List (Fin n)) :
    ∀ χ : Fin n → ℂ, SimplePath χ ss → ∀ r s, r ≠ s → (r ∈ ss ∨ s ∈ ss) → χ r ≠ χ s := by
  induction ss with
  | nil =>
    intro χ _ r s _ h
    simp at h
  | cons a l ih =>
    intro χ hp r s hrs hmem
    rw [simplePath_cons_iff] at hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hra : r = a
    · subst hra
      exact (h1 s (Ne.symm hrs)).symm
    by_cases hsa : s = a
    · subst hsa
      exact h1 r hrs
    have hmem' : r ∈ l ∨ s ∈ l := by
      simp only [List.mem_cons] at hmem
      tauto
    have h3 := ih _ h2 r s hrs hmem'
    simpa [Pi.single_apply, hra, hsa] using h3

theorem simpleDistinct (n : ℕ) (χ : Fin n → ℂ) (ss : List (Fin n))
    (hp : SimplePath χ ss) (hall : ∀ s, s ∈ ss) : Function.Injective χ := by
  intro r s heq
  by_contra hne
  exact simplePath_ne ss χ hp r s hne (Or.inl (hall r)) heq

end GlobalTheory.CompanionTheory.RgExhFin
