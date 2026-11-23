module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PZeroLocusDimH
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped NNReal ENNReal

noncomputable section

theorem NullSmaller.zeroSetEuc_eq_preimage_equiv {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSetEuc J =
      (EuclideanSpace.equiv (Fin n) ℂ) ⁻¹' {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} := by
  ext z
  rfl

theorem NullSmaller.ringKrullDim_le_of_lt_succ {R : Type*} [CommRing R] {k : ℕ}
    (h : ringKrullDim R < ((k + 1 : ℕ) : WithBot ℕ∞)) : ringKrullDim R ≤ (k : WithBot ℕ∞) := by
  generalize ringKrullDim R = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe a =>
      have h' : a < k + 1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.1 h'

theorem NullSmaller.proof : NullSmaller.Statement := by
  intro n d J hJ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have htop : J = ⊤ := by
      by_contra h
      have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.2 h
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
      exact absurd (h0.trans_lt hJ) (by simp)
    have hempty : zeroSetEuc J = ∅ := by
      ext z
      simp only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨1, htop ▸ Submodule.mem_top, by simp⟩
    rw [hempty, measure_empty]
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have hk := ZeroLocusDimH.proof n k J (NullSmaller.ringKrullDim_le_of_lt_succ hJ)
    have hlt : dimH (zeroSetEuc J) < (((2 * (k + 1) : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [NullSmaller.zeroSetEuc_eq_preimage_equiv, ContinuousLinearEquiv.dimH_preimage]
      refine hk.trans_lt ?_
      have : 2 * k < 2 * (k + 1) := by omega
      exact_mod_cast this
    have h0 := hausdorffMeasure_of_dimH_lt hlt
    simpa using h0

end

end GroundTheory.Heights₂.Heights
