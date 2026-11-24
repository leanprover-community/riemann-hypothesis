module

public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.InertD
import Development.AutomorphicArithmetic.FrobeniusLocalisation.LayerBot
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.VdLe
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.inertQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs

@[expose] public section

open UpperTheory.HF

open NumberField Formalism.HC

theorem UpperTheory.cmDatum_discriminantDepth_bounds :
    ∀ {φ : Frame} (H : HostAx φ), (∀ l ∈ H.small, H.vdH l ≤ (padicValNat l H.QS : ℝ) ∧ (padicValNat l H.QS : ℝ) ≤ Real.logb 2 H.QS) ∧
      H.vdH H.q ≤ 1 / 2 ∧ H.vdH H.d ≤ 1 / 2 ∧ 0 ≤ Real.logb 2 H.QS ∧
      ∀ p : ℕ, H.vdH p = (padicValInt p (discr H.E) : ℝ) / (Module.finrank ℚ H.E : ℝ) := by
  intro φ H
  have hQ : (1 : ℝ) ≤ H.QS := by exact_mod_cast H.QS_pos
  refine ⟨fun l hl => ?_, ?_, (UpperTheory.HF.inert_d H).2.2.1.le, Real.logb_nonneg one_lt_two hQ, fun p => by simp only [HostRaw.vdH]; push_cast; simp [padicValInt, Nat.padicValNat_def]⟩
  · obtain ⟨hp, hd⟩ := H.mem_small_iff.1 hl
    have hq : l ≠ H.q := fun h => H.q_notMem_small (h ▸ hl)
    have hdd : l ≠ H.d := fun h => H.d_notMem_small (h ▸ hl)
    have hle := (UpperTheory.HF.layer_bot H.toHostRaw (j := 0) hp (Nat.zero_le _)).2.2
    have hfac : H.condN.factorization l = padicValNat l H.QS := by
      rw [HostRaw.condN, Nat.factorization_mul (mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) H.d_prime.ne_zero,
        Nat.factorization_mul H.QS_ne_zero H.q_prime.ne_zero, Finsupp.add_apply, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (n := H.q)
          (fun h => hq ((Nat.prime_dvd_prime_iff_eq hp H.q_prime).1 h)),
        Nat.factorization_eq_zero_of_not_dvd (n := H.d)
          (fun h => hdd ((Nat.prime_dvd_prime_iff_eq hp H.d_prime).1 h)),
        Nat.factorization_def _ hp]
      simp [Nat.padicValNat_def]
    refine ⟨(UpperTheory.HF.vd_le H hp).2.trans (by exact_mod_cast hfac ▸ hle), ?_⟩
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_natCast]
    have h1 : 2 ^ padicValNat l H.QS ≤ H.QS :=
      (Nat.pow_le_pow_left hp.two_le _).trans (Nat.le_of_dvd H.QS_pos (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)))
    exact_mod_cast h1
  · obtain ⟨-, -, h1, h2, -⟩ := UpperTheory.HF.inert_q H
    by_cases h : H.q ∈ H.ram
    · exact (h1 h).2.1.le
    · rw [h2 h]; norm_num
