module

public import Formalism.RealPlaceAnalysis.Complexify
public import Mathlib.Analysis.InnerProductSpace.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.SkewSpan

theorem skew_conj {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) : Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε = -B := by
  have h' : Bᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * B) := eq_neg_of_add_eq_zero_left h
  rw [Matrix.mul_assoc, h', Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self,
    Matrix.one_mul]

theorem trace_twisted {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) (X : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace = - starRingEnd ℂ (X * Bᴴ).trace := by
  have h1 : (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace
      = (Xᴴ * (Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : starRingEnd ℂ (X * Bᴴ).trace = (Xᴴ * B).trace := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  rw [h1, h2, skew_conj ε h, Matrix.mul_neg, Matrix.trace_neg]

theorem real_span (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (s : Set (Fin d)) (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hG : ∀ i, Formalism.REAL.inG ε (B i)) :
    (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧
    (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧
    ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace
      = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  have h2 : ∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0 := by
    intro X hX i hi
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [hB, if_neg]
      rintro rfl
      exact hi hk
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  have hexp : ∀ X ∈ Submodule.span ℂ (B '' s), X = ∑ i, (X * (B i)ᴴ).trace • B i := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      simp [hB]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Matrix.add_mul, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | smul c x _ hx =>
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_assoc, ← Finset.smul_sum]
      rw [← hx]
  refine ⟨fun X => ⟨?_, ?_⟩, h2, fun X i => trace_twisted ε (hG i) X⟩
  · rintro ⟨hX, hXG⟩
    rw [hexp X hX]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ s
    · have h3 := trace_twisted ε (hG i) X
      rw [skew_conj ε hXG, Matrix.neg_mul, Matrix.trace_neg, neg_inj] at h3
      have h4 : (X * (B i)ᴴ).trace = (((X * (B i)ᴴ).trace.re : ℝ) : ℂ) :=
        (Complex.conj_eq_iff_re.mp h3.symm).symm
      rw [h4, Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [h2 X hX i hi, zero_smul]
      exact Submodule.zero_mem _
  · intro hX
    refine ⟨Submodule.span_le_restrictScalars ℝ ℂ _ hX, ?_⟩
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hG k
    | zero => simp [Formalism.REAL.inG]
    | add x y _ _ hx hy =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hx, hy,
        add_zero]
    | smul c x _ hx =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
        hx, smul_zero]

end GlobalTheory.SkewSpan
