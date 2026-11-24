module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd
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

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory.PrimeLogSum


open scoped BigOperators Matrix in
open Polynomial in
theorem _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le_real : ∀ (B : ℝ), 1 ≤ B →
    ∑ p ∈ (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ Real.log B + 3 := by
  intro B hB
  have h := _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le ⌊B⌋₊
  have hN : (1 : ℝ) ≤ (⌊B⌋₊ : ℝ) := by
    have : 1 ≤ ⌊B⌋₊ := Nat.le_floor (by exact_mod_cast hB)
    exact_mod_cast this
  have hle : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hlog : Real.log (⌊B⌋₊ : ℝ) ≤ Real.log B :=
    Real.log_le_log (by linarith) hle
  linarith

end GlobalTheory.PrimeLogSum
