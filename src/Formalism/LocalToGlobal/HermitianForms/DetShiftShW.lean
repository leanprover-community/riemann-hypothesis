module

public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.Forms

open Formalism.BasicNotions

variable {N : ℕ}

def shW (l : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => l.w i - c
  anti := fun i j h => by
    have := l.anti h
    show l.w j - c ≤ l.w i - c
    omega

theorem shW_zero (l : DomWeight N) : shW l 0 = l := by
  cases l
  simp only [shW, sub_zero]

theorem detShift_shW (l : DomWeight N) (c : ℤ) (hN : 0 < N) : (shW l c).detShift = l.detShift - c := by
  simp [DomWeight.detShift, hN, shW]

theorem natW_shW (l : DomWeight N) (c : ℤ) : (shW l c).natW = l.natW := by
  funext i
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.2
  simp only [DomWeight.natW, detShift_shW l c hN]
  congr 1
  simp only [shW]
  ring

theorem delSq_shW (R : Type) [CommRing R] (l : DomWeight N) (c : ℤ) : delSq R N (shW l c) = delSq R N l := by
  unfold delSq
  rw [natW_shW]

theorem CSpan_shW {ι : Type} [Fintype ι] (lam : ι → DomWeight N) (c : ι → ℤ) :
    CSpan (fun τ => shW (lam τ) (c τ)) = CSpan lam := by
  simp only [CSpan, delSq_shW]

end Formalism.L2.Forms
