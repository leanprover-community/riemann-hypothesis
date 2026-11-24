module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.Algebra.Group.End
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace Formalism.L2.S

open Formalism.BasicNotions

def IsPtL {K : Type*} [Zero K] (l : List (ℕ × K)) (i : ℕ) : Prop :=
  (l.map Prod.fst).sum = i ∧ ∀ b ∈ l, 1 ≤ b.1 ∧ b.2 ≠ 0

def ptList {K : Type*} [Zero K] {i : ℕ} (p : Formalism.MainNotions.S.Point K i) : List (ℕ × K) :=
  p.1.map Prod.swap

theorem ptList_isPtL {K : Type*} [Zero K] {i : ℕ} (p : Formalism.MainNotions.S.Point K i) : IsPtL (ptList p) i := by
  refine ⟨?_, ?_⟩
  · show ((p.1.map Prod.swap).map Prod.fst).sum = i
    rw [List.map_map]
    exact p.2.2
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (show b ∈ p.1.map Prod.swap from hb)
    exact ⟨(p.2.1 c hc).2, (p.2.1 c hc).1⟩

def ptEquiv (K : Type*) [Zero K] (i : ℕ) : Formalism.MainNotions.S.Point K i ≃ {l : List (ℕ × K) // IsPtL l i} where
  toFun p := ⟨ptList p, ptList_isPtL p⟩
  invFun l := ⟨l.1.map Prod.swap, by
    refine ⟨?_, ?_⟩
    · intro b hb
      simp only [List.mem_map] at hb
      obtain ⟨c, hc, rfl⟩ := hb
      exact ⟨(l.2.2 c hc).2, (l.2.2 c hc).1⟩
    · have h := l.2.1
      show ((l.1.map Prod.swap).map Prod.snd).sum = i
      rw [List.map_map]
      exact h⟩
  left_inv p := by
    apply Subtype.ext
    simp [ptList, List.map_map]
  right_inv l := by
    apply Subtype.ext
    simp [ptList, List.map_map]

end Formalism.L2.S
