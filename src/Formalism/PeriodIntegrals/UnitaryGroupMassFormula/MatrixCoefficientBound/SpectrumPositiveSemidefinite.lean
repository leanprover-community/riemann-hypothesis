module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

open scoped ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

theorem spectrum_positive_semidefinite : SpecPSD := by
  intro X _ M c hM hev
  have gen : ∀ (A : Matrix X X ℂ) (hA : A.IsHermitian) (b : ℝ),
      (∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → A *ᵥ w = μ • w → ∃ r : ℝ, μ = r ∧ b ≤ r) →
      ∀ j, b ≤ hA.eigenvalues j := by
    intro A hA b h j
    have hv := hA.mulVec_eigenvectorBasis j
    have hne := hA.eigenvectorBasis.orthonormal.ne_zero j
    have key : ∀ v : X → ℂ, v ≠ 0 → A *ᵥ v = hA.eigenvalues j • v → b ≤ hA.eigenvalues j := by
      intro v hv0 hAv
      obtain ⟨r, hr, hbr⟩ := h v (hA.eigenvalues j : ℂ) hv0 (by rw [hAv]; ext i; simp)
      have hre : hA.eigenvalues j = r := by exact_mod_cast hr
      rw [hre]
      exact hbr
    exact key _ (fun h0 => hne (by ext i; simpa using congrFun h0 i)) hv
  have h1 : ((c : ℂ) • (1 : Matrix X X ℂ)).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  have hN : ((c : ℂ) • (1 : Matrix X X ℂ) - M).IsHermitian := h1.sub hM
  have hNev : ∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → ((c : ℂ) • (1 : Matrix X X ℂ) - M) *ᵥ w = μ • w →
      ∃ r : ℝ, μ = r ∧ 0 ≤ r := by
    intro w μ hw h
    have hMw : M *ᵥ w = ((c : ℂ) - μ) • w := by
      rw [Matrix.sub_mulVec] at h
      first
        | rw [Matrix.smul_mulVec] at h
        | rw [Matrix.smul_mulVec_assoc] at h
        | simp only [Matrix.smul_mulVec_assoc] at h
      rw [Matrix.one_mulVec] at h
      rw [sub_smul, ← h]
      abel
    obtain ⟨r, hr, _, hrc⟩ := hev w ((c : ℂ) - μ) hw hMw
    refine ⟨c - r, ?_, by linarith⟩
    push_cast
    linear_combination -hr
  constructor
  · refine hM.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen M hM 0 ?_ j
    intro w μ hw h
    obtain ⟨r, hr, h0, _⟩ := hev w μ hw h
    exact ⟨r, hr, h0⟩
  · exact hN.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen _ hN 0 hNev j

end PI.GGMatBoundW
