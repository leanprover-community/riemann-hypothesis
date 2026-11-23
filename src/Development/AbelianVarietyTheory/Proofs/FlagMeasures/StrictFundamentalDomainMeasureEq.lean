module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem strictFD_measure_eq_tsum {G X : Type} [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hmeas : ∀ g, Measurable (ρ g)) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = ∑' g, μ (D ∩ NN ∩ (ρ g)⁻¹' D') := by
  have h1 : μ D = μ (D ∩ NN) := by
    rw [← measure_inter_add_diff D hNN]
    have : μ (D \ NN) = 0 := measure_mono_null (fun x hx => hx.2) hnull
    rw [this, add_zero]
  rw [h1]
  have hU : D ∩ NN = ⋃ g, D ∩ NN ∩ (ρ g)⁻¹' D' := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hxD, hxN⟩
      obtain ⟨g, hg, -⟩ := hu' x hxN
      exact ⟨g, ⟨hxD, hxN⟩, hg⟩
    · rintro ⟨g, ⟨hxD, hxN⟩, -⟩
      exact ⟨hxD, hxN⟩
  conv_lhs => rw [hU]
  apply measure_iUnion
  · intro g h hgh
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨⟨-, hxN⟩, hg⟩ ⟨⟨-, -⟩, hh⟩
    exact hgh ((hu' x hxN).unique hg hh)
  · intro g
    exact (hD.inter hNN).inter (hmeas g hD')

theorem strictFD_measure_eq {G X : Type} [Group G] [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hone : ∀ x, ρ 1 x = x) (hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (hinv : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN) (hmp : ∀ g, MeasurePreserving (ρ g) μ μ)
    (hu : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = μ D' := by
  have hmeas : ∀ g, Measurable (ρ g) := fun g => (hmp g).measurable
  rw [strictFD_measure_eq_tsum μ ρ NN D D' hNN hnull hD hD' hmeas hu',
    strictFD_measure_eq_tsum μ ρ NN D' D hNN hnull hD' hD hmeas hu]
  conv_rhs => rw [← (Equiv.inv G).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.inv_apply]
  have hS : MeasurableSet (D' ∩ NN ∩ (ρ g⁻¹)⁻¹' D) :=
    (hD'.inter hNN).inter (hmeas g⁻¹ hD)
  rw [← (hmp g).measure_preimage hS.nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  have hx : ρ g⁻¹ (ρ g x) = x := by rw [← hmul, inv_mul_cancel, hone]
  rw [hx]
  constructor
  · rintro ⟨⟨hxD, hxN⟩, hgx⟩
    exact ⟨⟨hgx, hinv g x hxN⟩, hxD⟩
  · rintro ⟨⟨hgx, hgxN⟩, hxD⟩
    refine ⟨⟨hxD, ?_⟩, hgx⟩
    have := hinv g⁻¹ _ hgxN
    rwa [hx] at this

end GlobalTheory.SnMass.VolN
