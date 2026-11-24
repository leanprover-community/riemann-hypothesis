module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

namespace GlobalTheory

theorem quad_eq_sum_symplDual (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ]
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ))
    (h : ∀ w, ∑ i, sympl (v i) w • u i = w) :
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i)) := by
  have hJ : ∀ (x : l ⊕ l → ℝ) (b : l ⊕ l), sympl x (Matrix.J l ℝ *ᵥ Pi.single b 1) = x b := by
    intro x b
    rcases b with b | b <;>
      simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Pi.single_apply,
        Matrix.one_apply]
  have hcol : ∀ b, ∑ i, v i b • u i = Matrix.J l ℝ *ᵥ Pi.single b 1 := by
    intro b
    have := h (Matrix.J l ℝ *ᵥ Pi.single b 1)
    simp only [hJ] at this
    exact this
  have hcoef : ∀ a b, ∑ i, (X *ᵥ u i) a * v i b = (X * Matrix.J l ℝ) a b := by
    intro a b
    have := congrArg (fun w => (X *ᵥ w) a) (hcol b)
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_mulVec] at this
    have e : ((X * Matrix.J l ℝ) *ᵥ Pi.single b 1) a = (X * Matrix.J l ℝ) a b := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← e, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hT : ∀ i, dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i) =
      ∑ a, ∑ b, (((X *ᵥ u i) a * v i b : ℝ) : ℂ) •
        (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1)) := by
    intro i
    rw [dRho_eq_sum (X *ᵥ u i), dRho_eq_sum (v i)]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
    conv_lhs => arg 1; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    module
  rw [quad]
  congr 1
  simp_rw [hT, ← hcoef, Finset.sum_div, Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  ring

end GlobalTheory
