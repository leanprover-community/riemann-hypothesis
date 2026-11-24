module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped Pointwise

namespace GlobalTheory

theorem fubini_compact_quotient : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (Γ : Subgroup H), Countable Γ → DiscreteTopology Γ → (∃ K : Set H, IsCompact K ∧ ∀ g, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → ∀ (X : Type) [MeasurableSpace X] (m : Measure X) [SFinite m] (f : H → X → ℂ), Measurable (Function.uncurry f) → (∀ γ ∈ Γ, ∀ h x, f (γ * h) x = f h x) → (∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ h ∈ K, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B) → Integrable (Function.uncurry f) ((μ.restrict 𝓕).prod m) := by
  intro H _ _ _ _ _ _ _ _ μ _ Γ hΓc hΓd hK 𝓕 h𝓕 X _ m _ f hf hinv hB
  obtain ⟨K, hKc, hKcov⟩ := hK
  obtain ⟨B, hB⟩ := hB K hKc
  haveI : Countable Γ := hΓc

  have hbd : ∀ h, ∫⁻ x, ‖f h x‖ₑ ∂m ≤ B := by
    intro h
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    have := hB _ hk
    simpa only [hinv γ hγ h] using this

  have hfin : μ 𝓕 < ⊤ := by
    have hcover : 𝓕 ⊆ ⋃ g : Γ, (g • K) := by
      intro h _
      obtain ⟨γ, hγ, hk⟩ := hKcov h
      refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
      refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
      simp [Subgroup.smul_def]
    have hle : μ 𝓕 ≤ μ K := by
      calc μ 𝓕 = μ ((⋃ g : Γ, (g • K)) ∩ 𝓕) := by
              rw [Set.inter_eq_right.2 hcover]
        _ = μ (⋃ g : Γ, (g • K ∩ 𝓕)) := by rw [Set.iUnion_inter]
        _ ≤ ∑' g : Γ, μ (g • K ∩ 𝓕) := measure_iUnion_le _
        _ = μ K := (h𝓕.measure_eq_tsum K).symm
    exact hle.trans_lt hKc.measure_lt_top
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hm : AEMeasurable (fun z : H × X => ‖Function.uncurry f z‖ₑ) ((μ.restrict 𝓕).prod m) :=
    hf.enorm.aemeasurable
  rw [HasFiniteIntegral, lintegral_prod _ hm]
  calc ∫⁻ h, ∫⁻ x, ‖Function.uncurry f (h, x)‖ₑ ∂m ∂(μ.restrict 𝓕)
      ≤ ∫⁻ _, (B : ENNReal) ∂(μ.restrict 𝓕) := lintegral_mono (fun h => hbd h)
    _ = B * μ 𝓕 := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin

end GlobalTheory
