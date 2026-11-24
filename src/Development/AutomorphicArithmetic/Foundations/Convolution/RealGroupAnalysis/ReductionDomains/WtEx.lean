module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtEx :
    ∀ (F : Type) [Field F] [NumberField F], ∃ β : G1 F → ℝ≥0∞, M.NWt β := by
  intro F _ _
  have hinj : Function.Injective (fun ξ : F => (nU (rt ξ : A F) : G1 F)) := by
    intro a b h
    have h1 : (nU (rt a : A F) : G1 F) 0 1 = (nU (rt b : A F) : G1 F) 0 1 := by
      rw [show (nU (rt a : A F) : G1 F) = nU (rt b : A F) from h]
    have h2 : (rt a : A F) = rt b := by simpa [nU] using h1
    exact AdeleRing.algebraMap_injective (𝓞 F) F h2
  let N : Subgroup (G1 F) :=
    { carrier := Set.range fun ξ : F => (nU (rt ξ : A F) : G1 F)
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp only [rt, map_add (f := _), M.nU_add]⟩
      one_mem' := ⟨0, by simp only [rt, map_zero, M.nU_zero]⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, by simp only [rt, map_neg, M.nU_neg]⟩ }
  have hle : N ≤ Gam F := by
    rintro _ ⟨ξ, rfl⟩
    exact M.nU_rt_mem ξ
  haveI : DiscreteTopology N :=
    DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup N
  refine ⟨D.indicator 1, measurable_one.indicator hD, fun g => ?_⟩
  obtain ⟨n, hn, huniq⟩ := hu g
  obtain ⟨ξ₀, hξ₀⟩ := n.2
  have hn' : (nU (rt ξ₀ : A F) : G1 F) * g ∈ D := by
    have : (n : G1 F) * g ∈ D := hn
    rwa [← hξ₀] at this
  rw [tsum_eq_single ξ₀]
  · rw [Set.indicator_of_mem hn']
    rfl
  · intro ξ hξ
    refine Set.indicator_of_notMem (fun hmem => hξ ?_) _
    have h1 : (⟨nU (rt ξ : A F), ⟨ξ, rfl⟩⟩ : N) = n := huniq _ hmem
    have h2 : (nU (rt ξ : A F) : G1 F) = n := congrArg Subtype.val h1
    exact hinj (h2.trans hξ₀.symm)
