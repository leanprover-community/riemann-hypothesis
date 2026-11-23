module

public import GroundTheory.AutomorphicForms.QuotientMeasure
public import GroundTheory.AutomorphicForms.ReductionMahler
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import GroundTheory.AutomorphicForms.Reduction
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Set

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

theorem isFundamentalDomain_preimage_mulRight (μ : Measure G) (g : G) :
    IsFundamentalDomain Γ ((· * g) ⁻¹' fundamentalDomain Γ) μ := by
  refine IsFundamentalDomain.mk'
    ((measurableSet_fundamentalDomain Γ).preimage (measurable_mul_const g)).nullMeasurableSet
    fun x => ?_
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_smul_mem_fundamentalDomain Γ (x * g)
  refine ⟨γ, ?_, fun δ hδ => huniq δ ?_⟩
  · change γ • x * g ∈ fundamentalDomain Γ
    rwa [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  · change δ • x * g ∈ fundamentalDomain Γ at hδ
    rwa [Subgroup.smul_def, smul_eq_mul, mul_assoc] at hδ

theorem measure_fundamentalDomain_pos_lt_top (μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasure (quotientMeasure Γ μ)] :
    0 < μ (fundamentalDomain Γ) ∧ μ (fundamentalDomain Γ) < ⊤ := by
  have hq : quotientMeasure Γ μ univ = μ (fundamentalDomain Γ) := by
    rw [quotientMeasure, Measure.map_apply (measurable_mk Γ) MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
  rw [← hq]
  refine ⟨?_, measure_lt_top _ _⟩
  obtain ⟨x⟩ : Nonempty (RightCosetSpace Γ) := ⟨mk Γ 1⟩
  exact (isOpen_univ.measure_pos (quotientMeasure Γ μ) ⟨x, mem_univ x⟩)

theorem isMulRightInvariant_of_isFiniteMeasure_quotientMeasure (μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasure (quotientMeasure Γ μ)] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hmap : Measure.map (· * g) μ = Measure.modularCharacterFun g • μ :=
    Measure.map_right_mul_eq_modularCharacterFun_smul μ g
  obtain ⟨hpos, hfin⟩ := measure_fundamentalDomain_pos_lt_top Γ μ
  have hF := isFundamentalDomain_fundamentalDomain Γ μ
  have hF' := isFundamentalDomain_preimage_mulRight Γ μ g
  have heq : Measure.map (· * g) μ (fundamentalDomain Γ) = μ (fundamentalDomain Γ) := by
    rw [Measure.map_apply (measurable_mul_const g) (measurableSet_fundamentalDomain Γ)]
    exact hF'.measure_eq hF
  rw [hmap, Measure.smul_apply] at heq
  have hc : (Measure.modularCharacterFun g : ENNReal) = 1 := by
    have h1 : (Measure.modularCharacterFun g : ENNReal) * μ (fundamentalDomain Γ) =
        1 * μ (fundamentalDomain Γ) := by
      rw [one_mul]
      simpa [ENNReal.smul_def] using heq
    exact (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h1
  rw [hmap]
  have : Measure.modularCharacterFun g = 1 := by exact_mod_cast hc
  rw [this, one_smul]

end RightCosetSpace

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem isMulRightInvariant_normOneGL (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  exact RightCosetSpace.isMulRightInvariant_of_isFiniteMeasure_quotientMeasure (rationalGLOne (K := K) (n := n)) μ

end Reduction

end

end GroundTheory.Automorphic
