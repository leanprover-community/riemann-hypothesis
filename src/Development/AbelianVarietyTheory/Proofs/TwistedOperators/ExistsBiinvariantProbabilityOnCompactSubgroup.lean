module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem exists_biinvariant_probability_on_compact_subgroup :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ mK : Measure G, IsProbabilityMeasure mK ∧ mK (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, Measure.map (fun x => k * x) mK = mK) ∧ ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK := by
  intro G _ _ _ _ _ _ _ K hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : BorelSpace K := Subtype.borelSpace (fun x => x ∈ (K : Set G))
  let μ : Measure K := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨by
    have := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    simpa using this⟩
  have : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hv : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hKm : MeasurableSet (K : Set G) := hK.isClosed.measurableSet
  refine ⟨μ.map Subtype.val, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hv hKm.compl]
    have : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x; simp
    rw [this]; simp
  · intro k hk
    rw [Measure.map_map (measurable_const_mul k) hv]
    have h1 : μ.map (fun x : K => (⟨k, hk⟩ : K) * x) = μ := map_mul_left_eq_self μ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_const_mul _)]
    rfl
  · intro k hk
    rw [Measure.map_map (measurable_mul_const k) hv]
    have h1 : μ.map (fun x : K => x * (⟨k, hk⟩ : K)) = μ := by
      have : (μ.map (fun x : K => x * (⟨k, hk⟩ : K))).IsHaarMeasure :=
        Measure.isHaarMeasure_map_mul_right μ _
      exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_mul_const _)]
    rfl

end GlobalTheory
