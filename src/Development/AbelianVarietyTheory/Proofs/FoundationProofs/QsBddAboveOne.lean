module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane Complex
open scoped Real

namespace GlobalTheory.EisM

private theorem norm_cexp_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-(2 * π * n * τ.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : (2 * π * Complex.I * n * τ : ℂ) = ((2 * π * n : ℝ) : ℂ) * (Complex.I * τ) := by
    push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

theorem qs_bdd_above_one : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  intro b hb
  obtain ⟨hs, -⟩ := qs_summable_continuous b hb
  refine ⟨∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖, fun τ hτ => ?_⟩
  have hpt : ∀ n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖ := by
    intro n
    rw [norm_mul, norm_mul, norm_cexp_qterm, norm_cexp_qterm]
    gcongr
    simp only [UpperHalfPlane.I_im, mul_one]
    have h0 : (0 : ℝ) ≤ 2 * π * n := by positivity
    nlinarith
  calc ‖qs b τ‖ ≤ ∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ := by
        unfold qs; exact norm_tsum_le_tsum_norm (hs τ)
    _ ≤ _ := Summable.tsum_le_tsum hpt (hs τ) (hs _)

end GlobalTheory.EisM
