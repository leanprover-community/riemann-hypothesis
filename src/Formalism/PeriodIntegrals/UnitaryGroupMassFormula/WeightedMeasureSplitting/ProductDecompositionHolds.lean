module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContSplit
public import Formalism.PeriodIntegrals.LevelKSplit
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.T2SpaceGeneralLinearGroup
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField

theorem amb_eq_map_mul_of_lintegral {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [MeasurableMul₂ G] {K N H : Subgroup G} (μK : Measure K) (μN : Measure N) (μH : Measure H)
    [SFinite μN] [SFinite μH]
    (h : ∀ f : G → ENNReal, Measurable f →
      ∫⁻ k, f (k : G) ∂μK = ∫⁻ m, ∫⁻ x, f ((m : G) * (x : G)) ∂μH ∂μN) :
    amb μK = ((amb μN).prod (amb μH)).map (fun p => p.1 * p.2) := by
  ext B hB
  have hf : Measurable (B.indicator (1 : G → ENNReal)) := measurable_one.indicator hB
  have hv : Measurable (Prod.map (Subtype.val : N → G) (Subtype.val : H → G)) :=
    measurable_subtype_coe.prodMap measurable_subtype_coe
  have hm : Measurable (fun p : G × G => p.1 * p.2) := measurable_mul
  calc amb μK B = ∫⁻ x, B.indicator 1 x ∂(amb μK) := (lintegral_indicator_one hB).symm
    _ = ∫⁻ k, B.indicator 1 (k : G) ∂μK := lintegral_map hf measurable_subtype_coe
    _ = ∫⁻ m, ∫⁻ x, B.indicator 1 ((m : G) * (x : G)) ∂μH ∂μN := h _ hf
    _ = ∫⁻ p, B.indicator 1 ((p.1 : G) * (p.2 : G)) ∂(μN.prod μH) :=
        (lintegral_prod _ (hf.comp (hm.comp hv)).aemeasurable).symm
    _ = ∫⁻ q, B.indicator 1 (q.1 * q.2) ∂((μN.prod μH).map
          (Prod.map (Subtype.val : N → G) (Subtype.val : H → G))) :=
        (lintegral_map (hf.comp hm) hv).symm
    _ = ∫⁻ q, B.indicator 1 (q.1 * q.2) ∂((amb μN).prod (amb μH)) := by
        rw [Measure.map_prod_map μN μH measurable_subtype_coe measurable_subtype_coe]
    _ = ∫⁻ x, B.indicator 1 x ∂(((amb μN).prod (amb μH)).map (fun p => p.1 * p.2)) :=
        (lintegral_map hf hm).symm
    _ = (((amb μN).prod (amb μH)).map (fun p => p.1 * p.2)) B := lintegral_indicator_one hB

theorem product_decomposition_holds : SProd := by
  intro F E _ _ _ _ _ σ n J r P T hCM hJ hStd μNf μHf hN hH
  obtain ⟨⟨μS, hμS, hprod⟩, -⟩ := level_s_all_split F E σ hCM n J hJ hJ r P T hStd ∅ ∅ ∅
    (by simp [PI.LevelKSplit.Adapted]) μNf hN μHf hH
  refine ⟨μS, hμS, ?_⟩
  have := hN
  have := hH
  exact amb_eq_map_mul_of_lintegral μS μNf μHf hprod

end PI.UnitaryGroupMassFormula.MeasWCore
