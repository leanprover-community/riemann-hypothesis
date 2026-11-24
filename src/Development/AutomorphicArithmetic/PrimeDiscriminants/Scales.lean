module

public import Formalism.LocalRingCardinality.DataParams₂
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace GlobalTheory.EX

open Formalism.BasicNotions

structure Scales (la : ℝ) where
  J : ℝ
  one_le_J : 1 ≤ J
  Win : Set ℝ
  windows : ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ Win

namespace Scales

variable {la : ℝ}

def Mem (S : Scales la) (s : Scale) : Prop := s.J = S.J ∧ s.x ∈ S.Win

theorem unb (S : Scales la) (hla : 1 ≤ la) (y : ℝ) : ∃ x ∈ S.Win, y ≤ x := by
  obtain ⟨Y, hY, hW⟩ := S.windows (max y 1)
  have h1 : 1 ≤ Y := le_trans (le_max_right y 1) hY
  refine ⟨Y, hW Y le_rfl ?_, le_trans (le_max_left y 1) hY⟩
  calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
    _ ≤ Y ^ la := Real.rpow_le_rpow_of_exponent_le h1 hla

def scale (S : Scales la) (x eps : ℝ) (hx : 1 < x) (h0 : 0 < eps) (h1 : eps < 1 / 52) : Scale :=
  ⟨x, eps, hx, h0, h1, S.J, S.one_le_J⟩

end Scales

end GlobalTheory.EX

end
