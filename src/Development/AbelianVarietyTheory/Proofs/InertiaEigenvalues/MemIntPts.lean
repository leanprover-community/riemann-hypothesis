module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Finite.Basic
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
public import Mathlib.Data.Int.Cast.Lemmas

@[expose] public section

noncomputable section

open Classical

namespace GlobalTheory.PositionData

def intPts (A : Set ℚ) : Finset ℤ :=
  if h : ((fun z : ℤ => (z : ℚ)) ⁻¹' A).Finite then h.toFinset else ∅

theorem mem_intPts {A : Set ℚ} (hA : A.Finite) (z : ℤ) : z ∈ intPts A ↔ (z : ℚ) ∈ A := by
  have h : ((fun z : ℤ => (z : ℚ)) ⁻¹' A).Finite :=
    hA.preimage (Set.injOn_of_injective Int.cast_injective)
  unfold intPts
  rw [dite_eq_left h, Set.Finite.mem_toFinset]
  rfl

def mnLo (Fl : Finset ℤ) : ℤ := (insert 0 Fl).min' (Finset.insert_nonempty _ _)

def mxLo (t : ℕ) (Fl : Finset ℤ) : ℤ := (insert ((t : ℤ) - 1) Fl).max' (Finset.insert_nonempty _ _)

def mnAll (Fl Fc : Finset ℤ) : ℤ := (insert 0 (Fl ∪ Fc)).min' (Finset.insert_nonempty _ _)

def mxAll (t : ℕ) (Fl Fc : Finset ℤ) : ℤ :=
  (insert ((t : ℤ) - 1) (Fl ∪ Fc)).max' (Finset.insert_nonempty _ _)

def wS (up : Bool) (Fl Fc : Finset ℤ) : ℕ :=
  if up then (1 - mnLo Fl).toNat else (1 - mnAll Fl Fc).toNat

def etaS (t : ℕ) (Fl : Finset ℤ) : ℕ := (mxLo t Fl - mnLo Fl + 1).toNat

def hS (up : Bool) (t : ℕ) (Fl Fc : Finset ℤ) : ℕ :=
  if up then (mxAll t Fl Fc + wS up Fl Fc + 1).toNat else (mxLo t Fl + wS up Fl Fc + 1).toNat

def US (up : Bool) (Fl Fc : Finset ℤ) : Multiset ℤ :=
  (Fl ∪ Fc).val.map (fun z => z + (wS up Fl Fc : ℤ))

theorem count_US (up : Bool) (Fl Fc : Finset ℤ) (b : ℤ) :
    (US up Fl Fc).count (b + wS up Fl Fc) = if b ∈ Fl ∪ Fc then 1 else 0 := by
  unfold US
  rw [Multiset.count_map_eq_count' _ _ (add_left_injective _)]
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem (Fl ∪ Fc).nodup h
  · exact Multiset.count_eq_zero.mpr h

end GlobalTheory.PositionData
