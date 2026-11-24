module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPairsEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEulLocal

theorem wtS_eq_sum (n : ℕ) (a : Fin n → ℤ) :
    GlobalTheory.CellDec.wtS n a = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * a i := by
  apply GlobalTheory.WeightSumSplit.wtS_eq <;> assumption


open GlobalTheory.JSW in
theorem localTerm_eq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  intro q hq n α β x v h0 hv
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : Antitone (fun i => (v i).toNat) := fun i j hij => Int.toNat_le_toNat (hv hij)
  have hcast : ∀ i, (((v i).toNat : ℕ) : ℂ) = ((v i : ℝ) : ℂ) := by
    intro i
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (h0 i)]
    simp
  set cR : ℝ := ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℕ)) * (v i : ℝ) with hcR
  have hc : (∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (((v i).toNat : ℕ) : ℂ))) = (cR : ℂ) := by
    rw [hcR]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcast i, Complex.ofReal_intCast]
  set A : ℝ := (q : ℝ) ^ (-cR / 2) with hA'
  have hA : (q : ℂ) ^ (-(cR : ℂ) / 2) = (A : ℂ) := by
    rw [hA', Complex.ofReal_cpow hqR.le]
    push_cast
    rfl
  have hW : (GlobalTheory.CellDec.wtS n v : ℝ) = cR := by
    rw [GlobalTheory.ZEulLocal.wtS_eq_sum, hcR]
    push_cast
    rfl
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) = 1 := by
    rw [hA', ← Real.rpow_add hqR, ← Real.rpow_intCast, ← Real.rpow_add hqR, hW]
    rw [show cR + (-cR / 2 + -cR / 2) = 0 by ring, Real.rpow_zero]
  have key2 : (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat) := by
    have e : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hqR.le]
      push_cast
      rfl
    rw [e, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    congr 3
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i)).symm
  rw [sphW, sphW, if_pos hl, if_pos hl, hc, hA, GlobalTheory.ZEul.rsTerm, if_pos ⟨h0, hv⟩, key2, map_mul,
    Complex.conj_ofReal]
  calc _ = (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) : ℝ) : ℂ) *
        (schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
          ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)) := by push_cast; ring
    _ = _ := by rw [key]; simp

end GlobalTheory.ZEulLocal
