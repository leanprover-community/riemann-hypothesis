module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem mulVec_mulVec_of_mul_eq_mul_diagonal {g : ℕ} (Sb A : Matrix (Fin g) (Fin g) ℂ) (d : Fin g → ℂ)
    (h : A * Sb = Sb * Matrix.diagonal d) (w : Fin g → ℂ) :
    A *ᵥ (Sb *ᵥ w) = Sb *ᵥ (fun j => d j * w j) := by
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
  congr 1
  funext j
  simp [Matrix.mulVec_diagonal]

theorem UpperTheory.Gal.W2.markDiag_of :
    UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.MarkDiag := by
  intro hTC F _ _ O _ bar g ρ a n t₀ ε hsig H Sb ty ev hD mu
  classical
  obtain ⟨hdet, hρ, hH⟩ := hD
  have hcard := (hTC F O bar g ρ a n t₀ ε hsig H Sb ty ev ⟨hdet, hρ, hH⟩ t₀).1
  rw [show typeMult n t₀ ε t₀ = 1 by simp [typeMult]] at hcard
  unfold evAt at hcard ⊢
  rw [Multiset.card_map, Finset.card_val, Finset.card_eq_one] at hcard
  obtain ⟨i₀, hi₀⟩ := hcard
  rw [hi₀, Finset.singleton_val, Multiset.map_singleton, Multiset.singleton_inj]
  have hmemS : ∀ j, ty j = t₀ ↔ j = i₀ := by
    intro j
    have := congrArg (j ∈ ·) hi₀
    simpa using this
  have hcol := mulVec_mulVec_of_mul_eq_mul_diagonal Sb
  have hinj := Matrix.mulVec_injective_of_det_ne_zero hdet
  constructor
  · rintro ⟨v, hv0, hvρ, hvH⟩
    have hunit : IsUnit Sb.det := isUnit_iff_ne_zero.2 hdet
    obtain ⟨w, hvw⟩ : ∃ w, v = Sb *ᵥ w :=
      ⟨Sb⁻¹ *ᵥ v, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]⟩
    subst hvw
    have hsupp : ∀ j, w j ≠ 0 → j = i₀ := by
      intro j hj
      rw [← hmemS]
      apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
      ext c
      have h1 := hvρ c
      rw [hcol _ _ (hρ c), ← Matrix.mulVec_smul] at h1
      have h2 := congr_fun (hinj h1) j
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      simp only [RingHom.comp_apply]
      exact mul_right_cancel₀ hj h2
    have hw0 : w ≠ 0 := by
      intro h; apply hv0; rw [h, Matrix.mulVec_zero]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
    rw [hsupp j hj] at hj
    have h1 := hvH
    rw [hcol _ _ hH, ← Matrix.mulVec_smul] at h1
    have h2 := congr_fun (hinj h1) i₀
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact mul_right_cancel₀ hj h2
  · intro h
    refine ⟨Sb *ᵥ Pi.single i₀ 1, ?_, fun c => ?_, ?_⟩
    · intro h0
      have : Pi.single i₀ (1 : ℂ) = 0 := hinj (by rw [h0, Matrix.mulVec_zero])
      simpa using congr_fun this i₀
    · rw [hcol _ _ (hρ c), ← Matrix.mulVec_smul]
      congr 1
      funext j
      by_cases hj : j = i₀
      · subst hj
        simp [(hmemS _).2 rfl]
      · simp [Pi.single_apply, hj]
    · rw [hcol _ _ hH, ← Matrix.mulVec_smul]
      congr 1
      funext j
      by_cases hj : j = i₀
      · subst hj
        simp [h]
      · simp [Pi.single_apply, hj]
