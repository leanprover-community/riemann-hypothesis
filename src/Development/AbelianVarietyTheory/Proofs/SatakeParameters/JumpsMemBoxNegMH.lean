module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem HTW.WordData.jumps_mem_box {n : ℕ} (W : WordData n) (hsz : ∀ i, 0 ≤ W.sz i) (hT : W.T1) :
    ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  intro i u hu
  have h0 := hsz i
  have ht := Int.self_le_toNat (W.sz i + W.S)
  have hT' := hT i u hu
  have hm1 : (W.η : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) := le_max_left _ _
  have hm2 : (((W.sz i + W.S).toNat : ℕ) : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) :=
    le_max_right _ _
  rcases hT' with h | h
  · by_cases hup : W.up i
    · rw [if_pos hup] at h
      simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · rw [if_neg hup] at h
      simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega
  · have h' := abs_le.mp h
    by_cases hup : W.up i
    · simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega

end GlobalTheory
