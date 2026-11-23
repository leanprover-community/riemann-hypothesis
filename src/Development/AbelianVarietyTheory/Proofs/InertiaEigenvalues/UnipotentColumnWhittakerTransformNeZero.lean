module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLastStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMulStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem colT_ne_zero_of_good : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → f ≠ 0 → colT ψ (m + 1) f ≠ 0 := by
  intro E _ _ a ψ hψ m f hma hG hf
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, f g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (funext h)
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ0 : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp only [Pi.zero_apply] at h1
    apply hg₀
    have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
    rw [e, one_mul] at h1
    exact h1
  obtain ⟨ξ, hξ⟩ : ∃ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, coefF ψ (m + 1) ξ f g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ0 (GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer h)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hξ
    have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
    have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
      intro x
      simp [dot]
    simp only [coefF, e, one_mul]
    exact hv
  obtain ⟨γ, hγ, hγξ⟩ := GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0
  intro h
  apply hξ
  have h1 := congrFun h (ratGL E a γ * g₀)
  simp only [Pi.zero_apply, colT] at h1
  rw [GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
  have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ :=
    funext hγξ
  rw [e] at h1
  exact h1

end GlobalTheory.CuspGeneric
