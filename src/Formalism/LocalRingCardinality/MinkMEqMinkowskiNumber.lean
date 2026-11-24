module

public import Formalism.LocalRingCardinality.DataMink
public import Formalism.LocalRingCardinality.DataErr
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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

namespace Formalism.BasicNotions

open Formalism.HermitianLatticeCounting.S6 (minkowskiM minkowskiExp)

theorem minkM_pos (n : ℕ) : 0 < minkM n :=
  Finset.prod_pos fun _ hp => pow_pos (Finset.mem_filter.1 hp).2.pos _

theorem minkM_dvd_factorial (n : ℕ) : minkM n ∣ (2 * n).factorial := Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial n

theorem log_minkM_le_two (n : ℕ) : Real.log (minkM n : ℝ) ≤ 2 * n * Real.log (2 * n) := by
  have h1 : minkM n ≤ (2 * n) ^ (2 * n) :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (minkM_dvd_factorial n)).trans (Nat.factorial_le_pow _)
  have h2 : (minkM n : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ (2 * n) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < minkM n := by exact_mod_cast minkM_pos n
  have h4 := Real.log_le_log h3 h2
  rw [Real.log_pow] at h4
  push_cast at h4
  exact h4

theorem Ranks.two_le_fN (R : Ranks) : 2 ≤ R.f * R.N R.m := by
  have hf : 2 ≤ R.f := by
    have h1 := R.two_le_m
    have h2 := R.m_le_f
    unfold Ranks.f Ranks.n; omega
  have hN : 1 ≤ R.N R.m := by
    have h1 := R.k_ge
    have h2 : R.k ≤ R.N R.m := Nat.le_add_right _ _
    omega
  calc 2 = 2 * 1 := rfl
    _ ≤ R.f * R.N R.m := Nat.mul_le_mul hf hN

theorem DGamMink.mem {D : D7} (h : DGamMink D) (hD : DGamDef D) (u : D.what₂.Word) :
    (D.mem u).C.DGam = minkM (2 * D.R.f * D.R.N D.R.m) := by
  rw [← hD.one u D.u₀ D.what₂.mu0, hD.one D.u₀ D.u₀ D.what₂.mu0]; exact h

theorem DGamMink.fact {D : D7} (h : DGamMink D) (hD : DGamDef D) : FactDGam D 12 := by
  intro u
  rw [h.mem hD u]
  have hy : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.N D.R.m := by exact_mod_cast D.R.two_le_fN
  have h1 := log_minkM_le_two (2 * D.R.f * D.R.N D.R.m)
  have e : ((2 * D.R.f * D.R.N D.R.m : ℕ) : ℝ) = 2 * ((D.R.f : ℝ) * D.R.N D.R.m) := by push_cast; ring
  rw [e] at h1
  have e2 : (2 : ℝ) * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) = 2 * 2 * ((D.R.f : ℝ) * D.R.N D.R.m) := by ring
  have h2 : Real.log (2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m))) =
      Real.log 2 + Real.log 2 + Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by
    rw [e2, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) (by norm_num)]
  have h3 : Real.log 2 ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := Real.log_le_log (by norm_num) hy
  rw [h2] at h1
  have h4 : 2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (Real.log 2 + Real.log 2 + Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) ≤
      2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (3 * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  calc Real.log (minkM (2 * D.R.f * D.R.N D.R.m) : ℝ)
      ≤ 2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (3 * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) := h1.trans h4
    _ = 12 * D.R.f * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by ring

end Formalism.BasicNotions
