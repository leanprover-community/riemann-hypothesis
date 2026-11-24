module

public import Mathlib.Basic.Real.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowLe, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMoments

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowLe =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowLe", "h": "module\n\npublic import Mathlib.Basic.Real.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory.OneAddPowBound

theorem one_add_pow_le : ∀ {t : ℝ}, (0 : ℝ) ≤ t → ∀ (k : ℕ),
    ((1 : ℝ) + t) ^ k ≤ (2 : ℝ) ^ k * ((1 : ℝ) + t ^ k) := by
  intro t ht k
  have htk : 0 ≤ t ^ k := pow_nonneg ht k
  have h2 : (0 : ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
  have h1 : (0 : ℝ) ≤ 1 + t := by linarith
  rcases le_total t 1 with h | h
  · have ha : (1 + t) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    have hb : (2 : ℝ) ^ k * 1 ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith
  · have ha : (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    rw [mul_pow] at ha
    have hb : (2 : ℝ) ^ k * t ^ k ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith

end GlobalTheory.OneAddPowBound
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowLe =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMoments =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMoments", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowLe\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\n\n"}
section -- clump:auto
@[expose] public section

set_option synthInstance.maxSize 1000

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic.GJMatrix GlobalTheory.ThetaPoisson

open scoped Classical

namespace GlobalTheory.SchwartzBruhatMoments

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem pInfPi_eq (x : Fin m → Ad E) :
    (fun i => pInf E (x i)) = (toMixedPi E m).symm (infPartPi x) := by
  rw [← toMixedPi_pInf, ContinuousLinearEquiv.symm_apply_apply]

theorem integrable_arch (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ) (k : ℕ) :
    Integrable (fun u => ‖φ u‖ * (1 + ‖(toMixedPi E m).symm u‖) ^ k) (mixedMeasurePi E) := by
  set S := (toMixedPi E m).symm
  set C := ‖(S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E))‖
  have hC : 0 ≤ C := norm_nonneg _
  have hint : Integrable (fun u => ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖))
      (mixedMeasurePi E) :=
    ((φ.integrable (μ := mixedMeasurePi E)).norm.add
      (φ.integrable_pow_mul (mixedMeasurePi E) k)).const_mul _
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact (φ.continuous.norm.mul ((continuous_const.add S.continuous.norm).pow k)).aestronglyMeasurable
  · have h1 : ‖S u‖ ≤ C * ‖u‖ := (S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E)).le_opNorm u
    have h2 : 1 + ‖S u‖ ≤ (1 + C) * (1 + ‖u‖) := by nlinarith [norm_nonneg u, norm_nonneg (S u)]
    have h3 : (1 + ‖S u‖) ^ k ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) := by
      calc (1 + ‖S u‖) ^ k ≤ ((1 + C) * (1 + ‖u‖)) ^ k := pow_le_pow_left₀ (by positivity) h2 k
        _ = (1 + C) ^ k * (1 + ‖u‖) ^ k := mul_pow _ _ _
        _ ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) :=
          mul_le_mul_of_nonneg_left (_root_.GlobalTheory.OneAddPowBound.one_add_pow_le (norm_nonneg u) k) (by positivity)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖φ u‖ * (1 + ‖S u‖) ^ k ≤ ‖φ u‖ * ((1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k))) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖) := by ring

theorem aestronglyMeasurable_weight (k : ℕ) :
    AEStronglyMeasurable (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply]
    rw [pInfPi_eq]
  rw [h]
  exact ((((continuous_const.add (toMixedPi E m).symm.continuous.norm).pow k).measurable.comp
    measurable_fst).comp (splitEquivPi E (Fin m)).measurable).aestronglyMeasurable

theorem integrable_tensor (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ)
    {g : (Fin m → Af E) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi E) (k : ℕ) :
    Integrable (fun x => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (‖φ p.1‖ * (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) * ‖g p.2‖) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply, schwartzBruhatTensorPi, norm_mul]
    rw [pInfPi_eq]
    ring
  rw [h, measurePreserving_splitEquivPi.integrable_comp_emb (splitEquivPi E (Fin m)).measurableEmbedding]
  exact (integrable_arch φ k).mul_prod (integrable_of_mem_finiteSchwartzBruhatPi hg).norm

theorem compactSupport_and_integrable_moments :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (F : (Fin m → Ad E) → ℂ),
    F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m) →
    (∃ L : Set (Fin m → Af E), IsCompact L ∧ ∀ x, F x ≠ 0 → (fun i => pFin E (x i)) ∈ L) ∧
    ∀ k : ℕ, Integrable (fun x => ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) := by
  intro E _ _ _ m F hF
  refine ⟨?_, fun k => ?_⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      refine ⟨tsupport g, hg.2, fun x hx => ?_⟩
      have e : (fun i => pFin E (x i)) = finPartPi x := rfl
      rw [e]
      apply subset_tsupport
      intro h0
      apply hx
      simp only [schwartzBruhatTensorPi, h0, mul_zero]
    | zero => exact ⟨∅, isCompact_empty, fun x hx => absurd rfl hx⟩
    | add G H _ _ hG hH =>
      obtain ⟨L1, h1, hL1⟩ := hG
      obtain ⟨L2, h2, hL2⟩ := hH
      refine ⟨L1 ∪ L2, h1.union h2, fun x hx => ?_⟩
      by_cases hGx : G x = 0
      · right
        apply hL2
        intro hH0
        apply hx
        simp [hGx, hH0]
      · left
        exact hL1 x hGx
    | smul c G _ hG =>
      obtain ⟨L, hL, hLx⟩ := hG
      exact ⟨L, hL, fun x hx => hLx x fun h0 => hx (by simp [h0])⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      exact integrable_tensor φ hg k
    | zero => simp
    | add G H hGm hHm hG hH =>
      refine (hG.add hH).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (integrable_of_mem_schwartzBruhatPi (K := E) (ι := Fin m)
          (Submodule.add_mem _ hGm hHm)).aestronglyMeasurable.norm.mul (aestronglyMeasurable_weight k)
      · have hw : 0 ≤ (1 + ‖fun i => pInf E (x i)‖) ^ k := by positivity
        simp only [Pi.add_apply]
        rw [Real.norm_of_nonneg (by positivity), ← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
    | smul c G _ hG =>
      refine (hG.const_mul ‖c‖).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      ring

end GlobalTheory.SchwartzBruhatMoments
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatIntegrableMoments =====
