module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import GroundTheory.AutomorphicForms.MeasuresModulus
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Matrix Pointwise NNReal

namespace GlobalTheory.ChangeVarPi

theorem map_symm_eq_smul (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι]
    (μ : Measure (ι → k)) [μ.IsAddHaarMeasure] (M : (ι → k) ≃ₗ[k] (ι → k)) :
    μ.map M.symm = (distribHaarChar k (LinearEquiv.det M)) • μ := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : Continuous M.symm := (M.symm : (ι → k) →ₗ[k] (ι → k)).continuous_on_pi
  ext s hs
  rw [Measure.map_apply hc.measurable hs, Measure.smul_apply, ← GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq,
    ENNReal.smul_def, smul_eq_mul, distribHaarChar_mul μ M s]
  have : (M.symm : (ι → k) → (ι → k)) ⁻¹' s = M • s := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      exact ⟨M.symm x, h, by simp [LinearEquiv.smul_def]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [LinearEquiv.smul_def] using hy
  rw [this]

end GlobalTheory.ChangeVarPi
