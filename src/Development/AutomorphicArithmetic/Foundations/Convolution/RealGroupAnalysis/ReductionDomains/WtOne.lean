module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.AutomorphicForms.ReductionMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtOne :
    ∀ (F : Type) [Field F] [NumberField F] (β : G1 F → ℝ≥0∞), M.NWt β → ∀ g, ∫⁻ b, β (nU b * g) ∂(adeleMeasure F) = 1 := by
  intro F _ _ β hβ g
  obtain ⟨hm, hs⟩ := hβ
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let e : F → AdeleRing.principalSubgroup (𝓞 F) F := fun ξ => ⟨rt ξ, ξ, rfl⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b h
      exact AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)
    · rintro ⟨_, ξ, rfl⟩
      exact ⟨ξ, rfl⟩
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := he.surjective.countable
  have hfd := isAddFundamentalDomain_fundamentalSet F
  have hf : Measurable fun b : A F => β (nU b * g) :=
    hm.comp (M.continuous_nU.mul continuous_const).measurable
  rw [hfd.lintegral_eq_tsum'' (fun b => β (nU b * g)), ← lintegral_tsum]
  · have hone : ∀ x : A F,
        ∑' k : AdeleRing.principalSubgroup (𝓞 F) F, β (nU (k +ᵥ x) * g) = 1 := by
      intro x
      rw [← (Equiv.ofBijective e he).tsum_eq, ← hs (nU x * g)]
      refine tsum_congr fun ξ => ?_
      change β (nU (rt ξ + x) * g) = _
      rw [M.nU_add, mul_assoc]
    simp only [hone, lintegral_const, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter,
      adeleMeasure_fundamentalSet, one_mul]
  · intro k
    exact (hf.comp (measurable_const_vadd k)).aemeasurable
