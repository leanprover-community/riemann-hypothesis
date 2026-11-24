module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
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

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

def sortedIndices {n : ℕ} (J : Finset (Fin n)) : List ℕ :=
  (J.sort (· ≤ ·)).map Fin.val

theorem sortedIndices_eq_map_sort {n : ℕ} (J : Finset (Fin n)) :
    sortedIndices J = (J.sort (· ≤ ·)).map Fin.val := rfl

theorem mem_sortedIndices {n : ℕ} (J : Finset (Fin n)) (a : ℕ) :
    a ∈ sortedIndices J ↔ ∃ j ∈ J, (j : ℕ) = a := by
  simp [sortedIndices, List.mem_map, Finset.mem_sort]

structure CenterInvariant (n : ℕ) : Type where
  positions : Finset (Fin n)
  rank : ℕ
  value : ℕ∞

def CenterInvariant.sortedIndices {n : ℕ} (K : CenterInvariant n) : List ℕ :=
  _root_.FunctorialResolution.EmbeddedResolution.MonomialCenter.sortedIndices K.positions

def CenterInvariant.Lt {n n' : ℕ} (K : CenterInvariant n) (K' : CenterInvariant n') : Prop :=
  K.rank < K'.rank ∨
    (K.rank = K'.rank ∧
      (K'.value < K.value ∨
        (K.value = K'.value ∧
          List.Lex (· < ·) K.sortedIndices K'.sortedIndices)))

def CenterInvariant.Le {n n' : ℕ} (K : CenterInvariant n) (K' : CenterInvariant n') : Prop :=
  K.Lt K' ∨
    (K.rank = K'.rank ∧ K.value = K'.value ∧ K.sortedIndices = K'.sortedIndices)

def centerInvariant {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData) :
    CenterInvariant L.length where
  positions := lexMaxIndices I m L
  rank := minIndexCard I m L
  value := maxCandidateOrder I m L

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
