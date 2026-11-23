module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem valuation_le_one_of_val_nonneg (K : UQ) (e : K.E) (he : e ≠ 0) (h : 0 ≤ val K.O e) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≤ 1 := by
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E e ≠ 0 := by simpa using he
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem val_nonneg_of_int (K : UQ) (x : K.O) : 0 ≤ val K.O (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · rw [hx]; unfold val; simp
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) x
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem map_int (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (x : K.O) :
    ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  by_cases hx : algebraMap K.O K.E x = 0
  · exact ⟨0, by rw [hx, map_zero, map_zero]⟩
  have hφ : φ (algebraMap K.O K.E x) ≠ 0 := by simpa using hx
  have hv : 0 ≤ val K'.O (φ (algebraMap K.O K.E x)) := by
    rw [hU.2.2.1]; exact val_nonneg_of_int K x
  exact IsDiscreteValuationRing.exists_lift_of_le_one (valuation_le_one_of_val_nonneg K' _ hφ hv)

end GlobalTheory.UnitLemma.Unr
