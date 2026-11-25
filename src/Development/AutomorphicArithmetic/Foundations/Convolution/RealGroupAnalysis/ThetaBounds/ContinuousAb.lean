module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAdeleInfHom
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_nonneg' {K : Type} [Field K] [NumberField K]
    (S : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)) (N : ℕ) (v : V4 K) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

theorem UpperTheory.ConvolutionTheory.R2.Ff.lDom :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), LDom W := by
  intro F E _ _ _ _ _ _ _ D W ι s Φ hΦ C hC
  obtain ⟨K, hK, hΦ⟩ := hΦ
  obtain ⟨ρ, hρ, hact, hnu, -, -⟩ := actCont F E D

  let r : GL (Fin 2) (A E) → GL (Fin 4) (A F) := fun h => ρ h⁻¹
  have hr : Continuous r := hρ.comp continuous_inv
  obtain ⟨K', hK', hlin⟩ := wtLin F (r '' C) (hC.image hr) K hK

  let β : GL (Fin 2) (A E) → ℝ := fun h => (ab (nu F h))⁻¹
  have hβ : Continuous β :=
    (continuous_ab.comp hnu).inv₀ fun h => (ab_pos _).ne'
  obtain ⟨A₀, hA₀⟩ := (hC.image hβ).bddAbove
  refine ⟨K', hK', fun N => ?_⟩
  obtain ⟨B, hB⟩ := hΦ N
  obtain ⟨B', hB'⟩ := hlin N
  refine ⟨|A₀| * (|B| * B'), ?_⟩
  rintro ⟨h, i⟩ ⟨hh, hi⟩ v
  have hβ0 : 0 ≤ β h := (inv_pos.2 (ab_pos _)).le
  have hβA : β h ≤ |A₀| := (hA₀ ⟨h, hh, rfl⟩).trans (le_abs_self _)
  have hnorm : ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := by
    rw [W.L_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ0]
  have h1 : ‖(Φ i).1 (D.act h⁻¹ v)‖ ≤ |B| * (B' * wt K' N v) := by
    have h2 : wt K N ((r h).val *ᵥ v) ≤ B' * wt K' N v := hB' (r h) ⟨h, hh, rfl⟩ v
    have h3 := hB i hi (D.act h⁻¹ v)
    rw [hact h⁻¹ v] at h3 ⊢
    calc _ ≤ B * wt K N ((r h).val *ᵥ v) := h3
      _ ≤ |B| * wt K N ((r h).val *ᵥ v) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg' _ _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  calc ‖(W.L h (Φ i)).1 v‖ = β h * ‖(Φ i).1 (D.act h⁻¹ v)‖ := hnorm
    _ ≤ |A₀| * (|B| * (B' * wt K' N v)) :=
      mul_le_mul hβA h1 (norm_nonneg _) (abs_nonneg _)
    _ = |A₀| * (|B| * B') * wt K' N v := by ring
