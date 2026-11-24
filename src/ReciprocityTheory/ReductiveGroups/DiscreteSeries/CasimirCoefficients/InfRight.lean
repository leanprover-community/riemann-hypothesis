module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InfRightA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LowMinusUpExpand

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

private lemma smul_cancel_lemma {E : Type*} [AddCommGroup E] [Module ℂ E] {c : ℂ} (hc : c ≠ 0)
    {u v : E} (h : c • u = c • v) : u = v := by
  have h' := congrArg (fun w => c⁻¹ • w) h
  simpa [smul_smul, inv_mul_cancel₀ hc] using h'

lemma infR_skew (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    fderiv ℂ (psM T μ) x (x * A) = -(T.dτ A * psM T μ x) ∧
      fderiv ℂ (psM T μ) x (A * x) = -(psM T μ x * T.dτ A) := by
  obtain ⟨hAs, hAb⟩ := (inK_iff ε A).1 hA
  have hH : IsBlock ε (Complex.I • A) := by
    intro i j hij
    rw [Matrix.smul_apply, hAb i j hij, smul_zero]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hHh : (Complex.I • A)ᴴ = Complex.I • A := by
    rw [Matrix.conjTranspose_smul, hAs, hI, neg_smul_neg]
  have h1 := psM_inf_herm T μ hμ hx hH hHh
  have e1 : Complex.I • A * x + x * (Complex.I • A) = Complex.I • (A * x + x * A) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_add]
  rw [e1] at h1

  have hs : fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A) =
      -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) := by
    apply smul_cancel_lemma Complex.I_ne_zero
    simpa only [map_smul, map_add (f := _), smul_mul_assoc, mul_smul_comm, smul_add, smul_neg] using h1

  have hd : fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x) =
      psM T μ x * T.dτ A - T.dτ A * psM T μ x := by
    rw [← map_sub]
    exact infR_conj T μ hx hA
  constructor
  · apply smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)
    rw [two_smul, two_smul]
    calc fderiv ℂ (psM T μ) x (x * A) + fderiv ℂ (psM T μ) x (x * A)
        = (fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A)) +
          (fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x)) := by abel
      _ = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) +
          (psM T μ x * T.dτ A - T.dτ A * psM T μ x) := by rw [hs, hd]
      _ = -(T.dτ A * psM T μ x) + -(T.dτ A * psM T μ x) := by abel
  · apply smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)
    rw [two_smul, two_smul]
    calc fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (A * x)
        = (fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A)) -
          (fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x)) := by abel
      _ = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) -
          (psM T μ x * T.dτ A - T.dτ A * psM T μ x) := by rw [hs, hd]
      _ = -(psM T μ x * T.dτ A) + -(psM T μ x * T.dτ A) := by abel

theorem psM_inf_right (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsBlock ε Y) :
    fderiv ℂ (psM T μ) x (x * Y) = -(T.dτ Y * psM T μ x) ∧
      fderiv ℂ (psM T μ) x (Y * x) = -(psM T μ x * T.dτ Y) := by

  obtain ⟨A, B, hA, hB, rfl, -⟩ := block_decomp hY
  have hA' := infR_skew T μ hμ hx hA
  have hB' := infR_skew T μ hμ hx hB
  constructor
  · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add (f := _), map_smul, hA'.1, hB'.1,
      neg_add, smul_neg]
  · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add (f := _), map_smul, hA'.2, hB'.2,
      neg_add, smul_neg]

end ReciprocityTheory.ChartRestriction.DS.S7
