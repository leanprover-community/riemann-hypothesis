module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem selfDual_comp_selfAdjoint : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ) (T : V ≃ₜ V) (δ : ℝ≥0), δ ≠ 0 → μ = δ • μ.map T → (∀ x y, χ x (T y) = χ (T x) y) → SelfDual μ χ → SelfDual (NNReal.sqrt δ • μ) (fun x y => χ x (T y)) := by
  intro V _ _ _ _ _ _ _ _ μ χ T δ hδ hμ hχ hsd
  have hH := hsd.1
  have hs0 : NNReal.sqrt δ ≠ 0 := by simpa using hδ
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul μ hs0, ?_⟩
  intro Φ hc hcs hI z
  set s : ℝ≥0 := NNReal.sqrt δ with hs
  set F : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ with hF
  have hT : ∀ y, ∫ x, Φ x * χ x (T y) ∂(s • μ) = (s : ℂ) * F (T y) := by
    intro y
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hmap : μ.map T = μ.map T.toMeasurableEquiv := rfl
  simp only [hT] at hI ⊢
  have h1 : Integrable (fun y => F (T y)) μ := by
    have h2 : Integrable (fun y => (s : ℂ) * F (T y)) μ := by
      have := hI.smul_measure_nnreal (c := s⁻¹)
      rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
    have := h2.const_mul ((s : ℂ)⁻¹)
    simpa [← mul_assoc, inv_mul_cancel₀ hsC] using this
  have h3 : Integrable F μ := by
    rw [hμ]
    apply Integrable.smul_measure_nnreal
    rw [hmap, integrable_map_equiv]
    exact h1
  have h4 := hsd.2 Φ hc hcs h3 z
  rw [← h4]
  have h5 : ∫ y, F y * χ y z ∂μ = (δ : ℂ) * ∫ y, F (T y) * χ (T y) z ∂μ := by
    conv_lhs => rw [hμ]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hmap, integral_map_equiv]
    rfl
  have hss : (s : ℂ) * (s : ℂ) = (δ : ℂ) := by
    have : s * s = δ := NNReal.mul_self_sqrt δ
    rw [← this]; push_cast; rfl
  change _ = ∫ y, F y * χ y z ∂μ
  rw [h5, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, ← hss, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  congr 1
  ext y
  rw [hχ, mul_assoc]

end GlobalTheory.GaugeEx
