module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.GramStep
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace PI.UD

lemma herm_decomp {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  · rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h
    have e : (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℂ) =
        fun i => ((hA.eigenvalues i : ℝ) : ℂ) := by
      funext i; rfl
    rw [e] at h
    exact h

lemma det_ne_zero_of_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) :
    Uᴴ.det ≠ 0 := by
  have h := congrArg det hU
  rw [det_mul, det_one] at h
  exact left_ne_zero_of_mul_eq_one h

private theorem exists_diagonal_unitary_gram_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosDef) :
    ∃ (s : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ), (∀ i, s i ≠ 0) ∧ Vᴴ * V = 1 ∧
      V * Vᴴ = 1 ∧ G = (diagonal s * Vᴴ)ᴴ * (diagonal s * Vᴴ) := by
  obtain ⟨V, h1, h2, hV⟩ := herm_decomp hG.1
  refine ⟨fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ), V, ?_, h1, h2, ?_⟩
  · intro i
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hG.eigenvalues_pos i)).ne'
  · have hd : (diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)))ᴴ *
        diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)) =
        diagonal (fun i => ((hG.1.eigenvalues i : ℝ) : ℂ)) := by
      rw [diagonal_conjTranspose, diagonal_mul_diagonal]
      refine congrArg diagonal (funext fun i => ?_)
      change star (↑(Real.sqrt (hG.1.eigenvalues i)) : ℂ) *
        ↑(Real.sqrt (hG.1.eigenvalues i)) = ↑(hG.1.eigenvalues i)
      simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hG.eigenvalues_pos i).le]
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc G = V * diagonal (fun i => ((hG.1.eigenvalues i : ℝ) : ℂ)) * Vᴴ := hV
      _ = V * ((diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)))ᴴ *
          diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ))) * Vᴴ := by rw [hd]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem gramStep : GramStep := by
  intro n G hG
  obtain ⟨s, V, hs, hV1, -, hGe⟩ := exists_diagonal_unitary_gram_of_posDef hG
  refine ⟨diagonal s * Vᴴ, hGe.symm, ?_⟩
  rw [det_mul, det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hs i)
    (det_ne_zero_of_unitary hV1)

theorem svdStep : SVDStep := by
  intro n g hg
  have hinj : Function.Injective g.mulVec :=
    mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg))
  have hP : (gᴴ * g).PosDef := PosDef.conjTranspose_mul_self g hinj
  obtain ⟨s, V, hs, hV1, hV2, hG⟩ := exists_diagonal_unitary_gram_of_posDef hP
  set C := diagonal s * Vᴴ with hC
  have hCdet : IsUnit C.det := by
    refine isUnit_iff_ne_zero.2 ?_
    rw [hC, det_mul, det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hs i)
      (det_ne_zero_of_unitary hV1)
  have hCH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hCdet.star
  refine ⟨g * C⁻¹, Vᴴ, s, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc (Cᴴ)⁻¹ * gᴴ * (g * C⁻¹) = (Cᴴ)⁻¹ * (gᴴ * g) * C⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (Cᴴ)⁻¹ * (Cᴴ * C) * C⁻¹ := by rw [hG]
      _ = ((Cᴴ)⁻¹ * Cᴴ) * (C * C⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hCH, mul_nonsing_inv _ hCdet, Matrix.one_mul]
  · rw [conjTranspose_conjTranspose]
    exact hV2
  · rw [Matrix.mul_assoc (g * C⁻¹) (diagonal s) Vᴴ, ← hC, nonsing_inv_mul_cancel_right C g hCdet]

end PI.UD
