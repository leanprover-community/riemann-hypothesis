module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_add_etaHat_add_sHat_le_hPage {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  have ht : 5 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hη : 0 < L.etaSz := L.etaSz_pos
  have hS : 0 < L.Sc := L.Sc_pos
  obtain ⟨hC, hw1, hw2, hwb, -, hb⟩ := h
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have hb' : (100 : ℝ) ≤ L.sc.b' := hw1.trans hwb
  have hfac : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbig : 100 * L.sc.b' ≤ L.sc.b := by
    have := mul_le_mul_of_nonneg_right hfac (by linarith : (0 : ℝ) ≤ L.sc.b')
    linarith
  have htR : ((D.R.t : ℕ) : ℝ) ≤ L.sc.b := by nlinarith
  have hb0 : 0 ≤ L.sc.b := by linarith
  set c := (D.R.t + 1) / 2 with hcdef
  have hc3 : 3 ≤ c := by omega
  have hct : c ≤ D.R.t := by omega
  have htc : D.R.t ≤ ⌈L.sc.b⌉₊ := by exact_mod_cast htR.trans (Nat.le_ceil _)
  have hcle : c ≤ ⌈L.sc.b⌉₊ := hct.trans htc
  have h1 : (⌈L.sc.b⌉₊ : ℝ) < L.sc.b + 1 := Nat.ceil_lt_add_one hb0
  have h2 : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le hη.le
  have h3 : (⌊L.Sc⌋₊ : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have hc3R : (3 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc3
  unfold bHat etaHat sHat hPage
  rw [← hcdef, Nat.cast_sub hcle]
  push_cast
  linarith

end GlobalTheory.HTW
