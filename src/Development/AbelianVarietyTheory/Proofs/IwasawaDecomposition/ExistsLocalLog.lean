module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.LocalLog

theorem exists_local_log (n : ℕ) : ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    (∀ᶠ g in 𝓝 (1 : Mx n), NormedSpace.exp (L g) = g) ∧
    ∀ᶠ X in 𝓝 (0 : Mx n), L (NormedSpace.exp X) = X := by
  letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mx n) := Matrix.linftyOpNormedAlgebra
  have h : HasStrictFDerivAt (NormedSpace.exp : Mx n → Mx n)
      ((ContinuousLinearEquiv.refl ℂ (Mx n) : Mx n ≃L[ℂ] Mx n) : Mx n →L[ℂ] Mx n) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  have h0 : NormedSpace.exp (0 : Mx n) = 1 := NormedSpace.exp_zero
  refine ⟨h.localInverse _ _ _, ?_, ?_, ?_, h.eventually_left_inverse⟩
  · have := h.localInverse_continuousAt
    rwa [h0] at this
  · have := h.localInverse_apply_image
    rwa [h0] at this
  · have := h.eventually_right_inverse
    rwa [h0] at this

theorem local_log_UJ : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    ∀ᶠ g in 𝓝 (1 : Mx n), g ∈ UJset ε → L g ∈ lieSet ε ∧ NormedSpace.exp (L g) = g := by
  intro n ε
  obtain ⟨L, hc, h1, hr, hl⟩ := exists_local_log n
  refine ⟨L, hc, h1, ?_⟩
  have hJ := Jm_mul_self ε
  have ht : Tendsto (fun g => Jm ε * (-(L g)ᴴ) * Jm ε) (𝓝 1) (𝓝 0) := by
    have hcont : Continuous fun X : Mx n => Jm ε * (-Xᴴ) * Jm ε := by fun_prop
    have := (hcont.tendsto 0).comp (h1 ▸ hc.tendsto)
    simpa [Function.comp_def] using this
  filter_upwards [hr, ht.eventually hl] with g hg hg' hU
  refine ⟨?_, hg⟩
  have hU' : gᴴ * Jm ε * g = Jm ε := hU
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJ
  have he : NormedSpace.exp (Jm ε * (-(L g)ᴴ) * Jm ε) = g := by
    have h2 := Matrix.exp_conj (Jm ε) (-(L g)ᴴ) (isUnit_Jm ε)
    rw [hinv, Matrix.exp_neg, Matrix.exp_conjTranspose, hg] at h2
    rw [h2]
    have h3 : (gᴴ)⁻¹ = Jm ε * g * Jm ε := by
      apply Matrix.inv_eq_right_inv
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', hJ]
    rw [h3]
    calc Jm ε * (Jm ε * g * Jm ε) * Jm ε = (Jm ε * Jm ε) * g * (Jm ε * Jm ε) := by simp only [Matrix.mul_assoc]
      _ = g := simp [hJ]
  rw [he] at hg'
  show (L g)ᴴ * Jm ε + Jm ε * L g = 0
  nth_rewrite 2 [hg']
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  simp

end GlobalTheory.LocalLog
