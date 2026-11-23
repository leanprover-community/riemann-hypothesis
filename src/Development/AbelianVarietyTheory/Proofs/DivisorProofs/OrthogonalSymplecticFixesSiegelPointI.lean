module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem holPart_eq_and_gaussian_of_orthogonal_symplectic (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (ho : sᵀ * s = 1) (hd : P.det ≠ 0) :
    GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ,
      cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) =
        cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  have hJ : s * J l ℝ = J l ℝ * s := by
    have h2 : s * J l ℝ * sᵀ = J l ℝ := SymplecticGroup.mem_iff.mp hs
    calc s * J l ℝ = s * J l ℝ * (sᵀ * s) := by rw [ho, Matrix.mul_one]
      _ = (s * J l ℝ * sᵀ) * s := by simp only [Matrix.mul_assoc]
      _ = J l ℝ * s := by rw [h2]
  have e1 : ∀ a b, s (.inl a) (.inr b) = - s (.inr a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inl b)
    simpa [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have e2 : ∀ a b, s (.inr a) (.inr b) = s (.inl a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inr b)
    simp [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at this
    linarith
  have hh : GlobalTheory.Published.Metaplectic.holPart s = P := by
    ext a b
    simp only [GlobalTheory.Published.Metaplectic.holPart, hP, e2, e1]
    push_cast; ring
  have hQP : Q = (-I) • P := by
    ext a b
    simp only [hP, hQ, e2, e1, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring_nf; rw [I_sq]; ring
  have hinv : -(Q * P⁻¹) = I • (1 : Matrix l l ℂ) := by
    rw [hQP, Matrix.smul_mul, mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hd), neg_smul, neg_neg]
  refine ⟨hh, fun x => ?_⟩
  rw [hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct]
  push_cast
  ring_nf; rw [I_sq]; ring

end GlobalTheory
