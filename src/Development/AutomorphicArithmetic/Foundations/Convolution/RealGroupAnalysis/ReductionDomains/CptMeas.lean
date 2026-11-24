module

public import Mathlib.MeasureTheory.Group.Measure
public import GroundTheory.AutomorphicForms.RealIwasawaIntegration
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.cptMeas :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ μK : Measure K, μK.IsHaarMeasure ∧ IsProbabilityMeasure μK ∧ (μK.map Subtype.val) (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, (μK.map Subtype.val).map (k * ·) = μK.map Subtype.val) ∧ ∀ k ∈ K, (μK.map Subtype.val).map (· * k) = μK.map Subtype.val := by
  intro G _ _ _ _ _ _ _ _ K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKm : MeasurableSet (K : Set G) := hK.isClosed.measurableSet
  have hval : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  let μ : Measure K := Measure.haarMeasure ⊤
  haveI hH : μ.IsHaarMeasure := inferInstance
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
    simpa using this
  haveI : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  haveI : μ.IsMulRightInvariant := GroundTheory.Automorphic.isMulRightInvariant_of_compactSpace μ
  refine ⟨μ, hH, hprob, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hval hKm.compl]
    have : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x; simp
    simp [this]
  · intro k hk
    have hcomp : (fun x : G => k * x) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => (⟨k, hk⟩ : K) * x) := by
      ext x; simp
    rw [Measure.map_map (measurable_const_mul k) hval, hcomp,
      ← Measure.map_map hval (measurable_const_mul _), map_mul_left_eq_self]
  · intro k hk
    have hcomp : (fun x : G => x * k) ∘ (Subtype.val : K → G) = Subtype.val ∘ (fun x : K => x * (⟨k, hk⟩ : K)) := by
      ext x; simp
    rw [Measure.map_map (measurable_mul_const k) hval, hcomp,
      ← Measure.map_map hval (measurable_mul_const _), map_mul_right_eq_self]
