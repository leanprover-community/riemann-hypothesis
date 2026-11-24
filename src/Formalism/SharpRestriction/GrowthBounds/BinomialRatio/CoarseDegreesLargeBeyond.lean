module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def PairFactsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ∀ (mu : Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) (lam : Fin X.m → ℤ),
          IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          pairC mu 0 = (A : ℤ) ∧ (∀ l, 0 ≤ pairC mu l) ∧
          (∀ i : Fin (segS X.TT j), 0 ≤ pairRho mu i ∧ pairRho mu i ≤ pairC mu i ∧
            ((pairRho mu i : ℤ) : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2) ∧
            -(4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2) ≤
              ((pairO mu (clA C0 CE1 CE2 X j rz ry) i - pairRho mu i : ℤ) : ℝ)) ∧
          0 ≤ lam 0 ∧ lam 0 ≤ pairC mu (segS X.TT j) ∧
          ∀ i : Fin (segS X.TT j), 0 ≤ pairN (s := segS X.TT j) lam i ∧
            ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2)

def CoarseDegreesLargeAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        X.k ^ 3 ≤ (A : ℝ) ∧ (∀ i, X.k ^ 3 ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ)) ∧
          (∀ i, X.k ^ 3 ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ)) ∧ X.k ^ 2 ≤ (X.p : ℝ) ∧ 10 ≤ X.k ∧
          1 ≤ X.La C0 ∧ 4 * X.La C0 ≤ X.k

def RestPairFacts : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PairFactsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def CoarseDegreesLargeBeyond : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => CoarseDegreesLargeAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
