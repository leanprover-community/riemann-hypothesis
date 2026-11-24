module

public import Mathlib.MeasureTheory.Group.Measure
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.MeasureTheory.Group.LIntegral

@[expose] public section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

theorem unfold : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] (ι : H →* G), Continuous ι → ∀ (F : G → ENNReal), Measurable F → ∀ (S C : Set G) (U : Set H), MeasurableSet S → MeasurableSet C → MeasurableSet U → (∀ g ∈ S, ∃ h₀ : H, ∀ u ∈ U, (ι (h₀ * u))⁻¹ * g ∈ C) → ∀ s : ENNReal, (∀ c ∈ C, ∫⁻ h, F (ι h * c) ∂ν ≤ s) → ν U * ∫⁻ g in S, F g ∂μ ≤ μ C * s := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ ι hι F hF S C U hS hC hU hSC s hs
  have hind : Measurable (C.indicator (1 : G → ENNReal)) := measurable_one.indicator hC
  have hin : ∀ g : G, Measurable (fun h : H => C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g)) :=
    fun g => hind.comp (((hι.inv).mul continuous_const).measurable)
  have step1 : ∀ g ∈ S, ν U ≤ ∫⁻ h, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) ∂ν := by
    intro g hg
    obtain ⟨h₀, hh₀⟩ := hSC g hg
    have hT : MeasurableSet ((fun h => h₀⁻¹ * h) ⁻¹' U) := measurable_const_mul h₀⁻¹ hU
    calc ν U = ν ((fun h => h₀⁻¹ * h) ⁻¹' U) := (measure_preimage_mul ν h₀⁻¹ U).symm
      _ = ∫⁻ h, ((fun h => h₀⁻¹ * h) ⁻¹' U).indicator 1 h ∂ν := (lintegral_indicator_one hT).symm
      _ ≤ ∫⁻ h, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) ∂ν := by
        refine lintegral_mono fun h => ?_
        by_cases hm : h ∈ (fun h => h₀⁻¹ * h) ⁻¹' U
        · have hc := hh₀ _ hm
          simp only [mul_inv_cancel_left] at hc
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem hc]
          simp
        · rw [Set.indicator_of_notMem hm]
          exact bot_le
  calc ν U * ∫⁻ g in S, F g ∂μ = ∫⁻ g in S, ν U * F g ∂μ := (lintegral_const_mul _ hF).symm
    _ = ∫⁻ g, S.indicator (fun g => ν U * F g) g ∂μ := (lintegral_indicator hS _).symm
    _ ≤ ∫⁻ g, ∫⁻ h, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) * F g ∂ν ∂μ := by
        refine lintegral_mono fun g => ?_
        by_cases hg : g ∈ S
        · rw [Set.indicator_of_mem hg, lintegral_mul_const _ (hin g)]
          exact mul_le_mul' (step1 g hg) le_rfl
        · rw [Set.indicator_of_notMem hg]
          exact bot_le
    _ = ∫⁻ h, ∫⁻ g, C.indicator (1 : G → ENNReal) ((ι h)⁻¹ * g) * F g ∂μ ∂ν := by
        refine lintegral_lintegral_swap ?_
        exact ((hind.comp (((hι.comp continuous_snd).inv.mul continuous_fst).measurable)).mul
          (hF.comp measurable_fst)).aemeasurable
    _ = ∫⁻ h, ∫⁻ c, C.indicator (1 : G → ENNReal) c * F (ι h * c) ∂μ ∂ν := by
        refine lintegral_congr fun h => ?_
        rw [← lintegral_mul_left_eq_self _ (ι h)]
        simp only [inv_mul_cancel_left]
    _ = ∫⁻ c, ∫⁻ h, C.indicator (1 : G → ENNReal) c * F (ι h * c) ∂ν ∂μ := by
        refine lintegral_lintegral_swap ?_
        exact ((hind.comp measurable_snd).mul
          (hF.comp ((hι.comp continuous_fst).mul continuous_snd).measurable)).aemeasurable
    _ = ∫⁻ c, C.indicator (1 : G → ENNReal) c * ∫⁻ h, F (ι h * c) ∂ν ∂μ := by
        refine lintegral_congr fun c => ?_
        exact lintegral_const_mul _ (hF.comp (hι.mul continuous_const).measurable)
    _ ≤ ∫⁻ c, C.indicator (1 : G → ENNReal) c * s ∂μ := by
        refine lintegral_mono fun c => ?_
        by_cases hc : c ∈ C
        · rw [Set.indicator_of_mem hc]
          simpa using hs c hc
        · rw [Set.indicator_of_notMem hc]
          simp
    _ = μ C * s := by
        rw [lintegral_mul_const _ hind, lintegral_indicator_one hC]

end PositivityTheory.UnitaryDecomposition.X4
