module

public import Formalism.FormalDegreeBessel.StatementG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.Matrix.Hermitian

@[expose] public section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.HermCongr


open scoped ComplexOrder in
theorem posDef_of_herm_re_pos {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) : J₀.PosDef := by
  have hA : J₀.IsHermitian := hH
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA ?_
  intro x hx
  have hre : 0 < (star x ⬝ᵥ J₀ *ᵥ x).re := hp x hx
  have him : (star x ⬝ᵥ J₀ *ᵥ x).im = 0 := hA.im_star_dotProduct_mulVec_self x
  exact Complex.pos_iff.2 ⟨hre, him.symm⟩

theorem exists_congr_one {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) :
    ∃ A Ai : Matrix (Fin m) (Fin m) ℂ, A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 := by
  have hP := posDef_of_herm_re_pos hH hp
  have hA : J₀.IsHermitian := hH
  have hd : ∀ i, 0 < hA.eigenvalues i := hP.eigenvalues_pos
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hJ : J₀ = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  let s : Fin m → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)
  let t : Fin m → ℂ := fun i => (((Real.sqrt (hA.eigenvalues i))⁻¹ : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ this, Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ this, Complex.ofReal_one]
  have htdt : diagonal t * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have h0 : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    have h1 : Real.sqrt (hA.eigenvalues i) * Real.sqrt (hA.eigenvalues i) = hA.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have h2 : (Real.sqrt (hA.eigenvalues i))⁻¹ * hA.eigenvalues i * (Real.sqrt (hA.eigenvalues i))⁻¹ = 1 := by
      have h3 : ∀ r : ℝ, r ≠ 0 → r⁻¹ * (r * r) * r⁻¹ = 1 := by
        intro r hr
        field_simp
      have h4 := h3 _ h0
      rwa [h1] at h4
    simp only [t]
    exact_mod_cast h2
  have htH : (diagonal t)ᴴ = diagonal t := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp [t]
  refine ⟨U * diagonal t, diagonal s * star U, ?_, ?_, ?_⟩
  · calc U * diagonal t * (diagonal s * star U) = U * (diagonal t * diagonal s) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hts, Matrix.mul_one, hUU']
  · calc diagonal s * star U * (U * diagonal t) = diagonal s * (star U * U) * diagonal t := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, hst]
  · rw [conjTranspose_mul, htH, ← star_eq_conjTranspose]
    calc diagonal t * star U * J₀ * (U * diagonal t)
        = diagonal t * star U * (U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U)
            * (U * diagonal t) := by rw [← hJ]
      _ = diagonal t * (star U * U) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
            * (star U * U) * diagonal t := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, Matrix.mul_one, htdt]

end UpperTheory.Lit.Bur.HermCongr

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.hermitian_form_pos_congruent_identity : ∀ {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀) (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re), ∃ A Ai : Matrix (Fin m) (Fin m) ℂ, A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 := by
  exact @UpperTheory.Lit.Bur.HermCongr.exists_congr_one
