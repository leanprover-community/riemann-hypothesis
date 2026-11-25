module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.IntegralModels.ComapEqMaximalIdeal, GroundTheory.HeightsAndTheta.Heights.IntegralModels.CpEqPrimeWeight, GroundTheory.HeightsAndTheta.Heights.IntegralModels.IicEqRange, GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsAlt, GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp, GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.ComapEqMaximalIdeal =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.IntegralModels.ComapEqMaximalIdeal", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.ComapEqMaximalIdeal =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.CpEqPrimeWeight =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.IntegralModels.CpEqPrimeWeight", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.CpEqPrimeWeight =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.IicEqRange =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.IntegralModels.IicEqRange", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.IicEqRange =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsAlt =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsAlt", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsAlt =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem primeWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ primeWeight p := by
  unfold primeWeight
  split_ifs
  · norm_num
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg zero_le_one (by linarith)

theorem primeWeight_le {p : ℕ} (hp : p.Prime) : primeWeight p ≤ 4 / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold primeWeight
  split_ifs with h
  · subst h; norm_num
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith

theorem SumCp.proof (hM : MertensUpper.Statement) : SumCp.Statement := by
  obtain ⟨CM, hCM⟩ := hM
  intro d hd
  set T := d.natAbs.primeFactors with hT
  set K1 : ℝ := ∑ p ∈ T, primeWeight p * Real.log p
  set K2 : ℝ := ∑ p ∈ T, 2 * (padicValInt p d : ℝ) * Real.log p
  set A : ℝ := |4 * CM + K1 + K2|
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 + A / Real.log 2, fun B hB S hS => ?_⟩
  set P := (Finset.Iic ⌊B⌋₊).filter Nat.Prime
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
  have hlog : ∀ p : ℕ, p.Prime → 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hSsub : S ⊆ P ∪ T := by
    intro p hp
    obtain ⟨hpp, hpB | hpd⟩ := hS p hp
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Iic.mpr (Nat.le_floor hpB), hpp⟩)
    · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
        ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)

  have hW : ∑ p ∈ S, primeWeight p * Real.log p ≤ 4 * (Real.log B + CM) + K1 := by
    have hnn : ∀ p ∈ P ∪ T, 0 ≤ primeWeight p * Real.log p := by
      intro p hp
      have hpp : p.Prime := (Finset.mem_union.mp hp).elim (hPprime p) (hTprime p)
      exact mul_nonneg (primeWeight_nonneg hpp) (hlog p hpp)
    calc ∑ p ∈ S, primeWeight p * Real.log p
        ≤ ∑ p ∈ P ∪ T, primeWeight p * Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun p hp _ => hnn p hp)
      _ ≤ ∑ p ∈ P, primeWeight p * Real.log p + K1 := by
          rw [← Finset.sum_union_inter]
          have : 0 ≤ ∑ p ∈ P ∩ T, primeWeight p * Real.log p :=
            Finset.sum_nonneg fun p hp => hnn p (Finset.mem_union_left _ (Finset.mem_inter.mp hp).1)
          linarith
      _ ≤ ∑ p ∈ P, 4 * (Real.log p / p) + K1 := by
          have hsum : ∑ p ∈ P, primeWeight p * Real.log p ≤ ∑ p ∈ P, 4 * (Real.log p / p) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hpp := hPprime p hp
            have hw := mul_le_mul_of_nonneg_right (primeWeight_le hpp) (hlog p hpp)
            calc primeWeight p * Real.log p ≤ 4 / p * Real.log p := hw
              _ = 4 * (Real.log p / p) := by ring
          linarith
      _ ≤ 4 * (Real.log B + CM) + K1 := by
          rw [← Finset.mul_sum]
          linarith [hCM B hB]

  have hV : ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p ≤ K2 := by
    rw [← Finset.sum_filter_of_ne (p := fun p => p ∈ T)]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp; exact (Finset.mem_filter.mp hp).2
      · intro p hp _
        exact mul_nonneg (by positivity) (hlog p (hTprime p hp))
    · intro p hp hne
      by_contra hpT
      apply hne
      have hpp := (hS p hp).1
      have hnd : ¬ (p : ℤ) ∣ d := fun hpd => hpT (Nat.mem_primeFactors.mpr
        ⟨hpp, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩)
      rw [padicValInt.eq_zero_of_not_dvd hnd]
      simp
  have hsplit : ∑ p ∈ S, (primeWeight p + 2 * padicValInt p d) * Real.log p
      = ∑ p ∈ S, primeWeight p * Real.log p + ∑ p ∈ S, 2 * (padicValInt p d : ℝ) * Real.log p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hA : 4 * CM + K1 + K2 ≤ A := le_abs_self _
  have hA0 : 0 ≤ A := abs_nonneg _
  have habs : A ≤ A / Real.log 2 * Real.log B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlogB hA0
  rw [hsplit]
  nlinarith [hW, hV, hA, habs]

end GroundTheory.Heights₂.Heights.Model
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ComapEqMaximalIdeal\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.CpEqPrimeWeight\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteTypeSectionsOfIsFiniteTypeOverZ\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IicEqRange\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ImportsAlt\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBlowUpChart\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVR\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizuki\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PKrullAkizukiQuotientLength\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PMertensUpper\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSumCp\npublic import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

alias BlowUpChart.full := _root_.GroundTheory.Heights₂.Heights.Model.BlowUpChart.proof

alias FiniteIntegralClosure.full := _root_.GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.proof

alias MertensUpper.full := _root_.GroundTheory.Heights₂.Heights.Model.MertensUpper.proof

alias TorsionFreeQuotientLength.full := _root_.GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.proof

theorem KrullAkizukiQuotientLength.full : KrullAkizukiQuotientLength.Statement :=
  KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.proof KrullAkizukiQuotientLength.full

theorem DominatingDVR.full : DominatingDVR.Statement :=
  DominatingDVR.proof KrullAkizuki.full BlowUpChart.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.proof MertensUpper.full

end GroundTheory.Heights₂.Heights.Model

end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly =====
