module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem volU_succ_eq_mul (m : ℕ) :
    volU (m + 1) = volU m * (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) := by
  have h : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := by
    have := Nat.triangle_succ m
    simpa using this
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)), h, pow_add]
  simp only [Nat.add_sub_cancel]
  ring

theorem vInv_pos_of_numberField (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  positivity

theorem mass_ratio_mul_unitary_volume :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ), 1 ≤ M →
      Formalism.HermitianLatticesTheory.massRatioRightSide E M * volU M ^ Formalism.HermitianLatticesTheory.fDeg E =
        rankFac E M * volU (M - 1) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  intro E _ _ _ M hM
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hv := vInv_pos_of_numberField E
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide rankFac
  simp only [Nat.add_sub_cancel]
  rw [volU_succ_eq_mul]
  set v := Formalism.HermitianLatticesTheory.vInv E
  set f := Formalism.HermitianLatticesTheory.fDeg E
  have h2 : 0 < 2 * v := by positivity
  have hfac : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hpi := Real.pi_pos.ne'
  have key : ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1)) *
      (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) = (2 * v) ^ (m + 1) := by
    rw [div_pow, mul_pow]
    field_simp
    ring
  have hr : (2 * v) ^ ((f : ℝ) * (((m + 1 : ℕ) : ℝ) - 1 / 2)) =
      ((2 * v) ^ (m + 1)) ^ f / Real.sqrt ((2 * v) ^ f) := by
    rw [Real.sqrt_eq_rpow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul h2.le, ← Real.rpow_sub h2]
    congr 1
    push_cast
    ring
  rw [hr, ← key, mul_pow (volU m), mul_pow ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1))]
  ring

end GlobalTheory.FlagMeas
