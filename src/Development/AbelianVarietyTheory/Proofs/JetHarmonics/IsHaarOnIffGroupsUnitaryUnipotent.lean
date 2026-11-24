module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.HaarNotions


open Formalism.FourierDecayAlt.P.B2x1 in
theorem finite_compact_of_sigmaFinite {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) [SigmaFinite μ] (hc : μ Uᶜ = 0)
    (hl : ∀ a ∈ U, μ.map (Formalism.QuantumDeterminants.lmulM a) = μ) (K : Set (Formalism.QuantumDeterminants.Mt k r)) (hK : IsCompact K) : μ K < ∞ := by
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ hl
  have : SigmaFinite (pull hU μ) := by
    have h : SigmaFinite ((pull hU μ).map inc) := by rw [map_pull μ hc]; infer_instance
    exact SigmaFinite.of_map _ inc_memb.measurable.aemeasurable h
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Gp U hU)) := inferInstance
  have huniq := Measure.haarMeasure_unique (pull hU μ) K₀
  have hfin : pull hU μ K₀ ≠ ∞ := by
    intro hinf
    rw [hinf] at huniq
    have hzero : ∀ n, Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) = 0 := by
      intro n
      by_contra hne
      have h1 := measure_spanningSets_lt_top (pull hU μ) n
      have h2 : pull hU μ (spanningSets (pull hU μ) n) =
          ∞ * Measure.haarMeasure K₀ (spanningSets (pull hU μ) n) :=
        congrArg (fun m : Measure (Gp U hU) => m (spanningSets (pull hU μ) n)) huniq
      rw [h2, ENNReal.top_mul hne] at h1
      exact lt_irrefl _ h1
    have huniv : Measure.haarMeasure K₀ Set.univ = 0 := by
      rw [← iUnion_spanningSets (pull hU μ)]
      exact measure_iUnion_null hzero
    have h1 : Measure.haarMeasure K₀ K₀ = 0 := measure_mono_null (Set.subset_univ _) huniv
    rw [Measure.haarMeasure_self] at h1
    exact one_ne_zero h1
  have hK' : IsCompact ((inc : Gp U hU → Formalism.QuantumDeterminants.Mt k r) ⁻¹' K) := inc_closedEmb.isCompact_preimage hK
  have h3 : pull hU μ (inc ⁻¹' K) = pull hU μ K₀ * Measure.haarMeasure K₀ (inc ⁻¹' K) :=
    congrArg (fun m : Measure (Gp U hU) => m (inc ⁻¹' K)) huniq
  rw [← map_pull (hU := hU) μ hc, inc_memb.map_apply, h3]
  exact ENNReal.mul_lt_top hfin.lt_top hK'.measure_lt_top

theorem isHaarOn_iff {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    (hex : ∃ ν : Measure (Formalism.QuantumDeterminants.Mt k r), B.IsHaarOn U ν) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) :
    PI.BesselPeriodGGP.IsHaarOn U μ ↔ B.IsHaarOn U μ := by
  constructor
  · rintro ⟨hσ, h0, hc, hl⟩
    obtain ⟨ν, hν⟩ := hex
    have hfin := finite_compact_of_sigmaFinite hU μ hc hl
    obtain ⟨c, hcν⟩ := P.haar_measure_unique_up_to_scalar k r U ν μ hU hν hc hl hfin
    refine { ne_zero := h0, conc := hc, left := hl, right := ?_, finite_compact := hfin }
    intro a ha
    rw [hcν, Measure.map_smul, hν.right a ha]
    exact (show Continuous (B.rmulF a) from by
      unfold B.rmulF
      exact continuous_id.matrix_mul continuous_const).measurable.aemeasurable
  · intro h
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem isHaarOn_iff_groups : ∀ (k r : ℕ) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)), (PI.BesselPeriodGGP.IsHaarOn (GG k r) μ ↔ B.IsHaarOn (GG k r) μ) ∧ (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) ∧ ∀ z, Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → 1 ≤ k → (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ) :=
  fun k r μ =>
    ⟨isHaarOn_iff (P.unitary_group_closed k r) (P.unitary_group_haar_exists k r) μ,
      isHaarOn_iff (P.unipotent_radical_closed k r) (P.unipotent_haar_exists k r) μ,
      fun z hz hT _ => isHaarOn_iff (P.weyl_subgroup_closed k r z) (P.weyl_haar_exists k r z hz hT) μ⟩

end GlobalTheory.HaarNotions
