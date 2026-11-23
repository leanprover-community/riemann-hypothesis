module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
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

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem ramBig_of_ramShare : ∀ (D : D7) (u : D.what₂.Word), RamShare D u → 0 < d0 D u → 2 < (D.mem u).A.T →
    RamBig D u ((D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1)) := by
  intro D u hS hd hT
  have hT' : (2 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast hT
  have hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1 := by linarith
  set a : ℝ := -(1 / (((D.mem u).A.T : ℝ) - 1)) with ha
  have ha1 : 1 / (((D.mem u).A.T : ℝ) - 1) < 1 := by
    rw [div_lt_one hpos]; linarith
  have ha0 : 0 < 1 / (((D.mem u).A.T : ℝ) - 1) := by positivity
  have hb : -2 ≤ a := by rw [ha]; linarith
  have hB := one_add_mul_le_pow hb D.R.f
  have hd' : (0 : ℝ) < (d0 D u : ℝ) := by exact_mod_cast hd
  unfold RamShare at hS
  unfold RamBig
  have hbase : 0 < 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by linarith
  have hp : 0 < (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f := pow_pos hbase _
  refine ⟨?_, ?_⟩
  · have : (0 : ℝ) < (dU D u : ℝ) := by rw [hS]; exact mul_pos hd' hp
    exact_mod_cast this
  · rw [hS]
    have e1 : 1 + a = 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by rw [ha]; ring
    rw [e1] at hB
    have e2 : 1 + (D.R.f : ℝ) * a = 1 - (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) := by rw [ha]; ring
    rw [e2] at hB
    rw [mul_comm ((d0 D u : ℝ))]
    exact mul_le_mul_of_nonneg_right hB hd'.le

end GlobalTheory.Core.Rk
