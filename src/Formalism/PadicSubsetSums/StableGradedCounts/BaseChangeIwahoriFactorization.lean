module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Lemmata.FirstBlockLemmaG.Imports
public import Lemmata.MiscLemmasA.Imports
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

namespace Formalism.IrreducibleCountingLemmas.Z

theorem isUnit_sub_of_mem_maximalIdeal {O : Type} [CommRing O] [IsLocalRing O] {a m : O}
    (ha : IsUnit a) (hm : m ∈ IsLocalRing.maximalIdeal O) : IsUnit (a - m) := by
  first | exact Bl.FirstBlockLemmaG.goal1 .. | (apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaG.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaG.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha hm | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m ha | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a m | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› a | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O ‹_› | exact @Bl.FirstBlockLemmaG.goal1 O

theorem iwahori_factorization_exists (O : Type) [CommRing O] [IsLocalRing O] (U L : Ideal O)
    (hL : L ≤ IsLocalRing.maximalIdeal O) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), (∀ i, IsUnit (g i i)) →
    (∀ i j, i < j → g i j ∈ U) → (∀ i j, j < i → g i j ∈ L) →
    ∃ (x y : Matrix (Fin n) (Fin n) O) (δ : Fin n → O),
      (∀ i j, g i j = ∑ k, x i k * δ k * y k j) ∧
      (∀ i, x i i = 1) ∧ (∀ i j, j < i → x i j = 0) ∧ (∀ i j, i < j → x i j ∈ U) ∧
      (∀ i, IsUnit (δ i)) ∧ (∀ i, δ i - g i i ∈ U * L) ∧
      (∀ i, y i i = 1) ∧ (∀ i j, i < j → y i j = 0) ∧ (∀ i j, j < i → y i j ∈ L) := by
  first | exact Bl.SecondBlockLemmaB.goal1 .. | (apply Bl.SecondBlockLemmaB.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaB.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaB.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaB.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaB.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n g | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL n | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L hL | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U L | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› U | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O ‹_› | exact @Bl.SecondBlockLemmaB.goal1 O

end Formalism.IrreducibleCountingLemmas.Z
