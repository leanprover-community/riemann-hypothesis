module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaInj
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaInjSet
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionFormula
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

theorem AreaFormulaInj.proof (h : AreaFormulaInjSet.Statement) : AreaFormulaInj.Statement := by
  classical
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U A f g hU hf hAU hA hinj hg
  let f' : E → F := U.piecewise f (fun _ => 0)
  have hf'm : Measurable f' := hf.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hEq : ∀ x ∈ A, f' x = f x := fun x hx => Set.piecewise_eq_of_mem _ _ _ (hAU hx)
  have hJ : Measurable fun x : E => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) :=
    ENNReal.measurable_ofReal.comp (continuous_areaJacobian.measurable.comp (measurable_fderiv ℝ f))
  let ρ : Measure E := ((μH[(k : ℝ)] : Measure E).restrict A).withDensity
    fun x : E => ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F))
  have hmap : ρ.map f' = (μH[(k : ℝ)] : Measure F).restrict (f '' A) := by
    ext S hS
    have hpre : MeasurableSet (f' ⁻¹' S) := hf'm hS
    rw [Measure.map_apply hf'm hS, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
      Measure.restrict_apply hS,
      ← h E F k hk U _ f hU hf (by exact fun x hx => hAU hx.2) (hpre.inter hA) (hinj.mono fun x hx => hx.2)]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hyA⟩, rfl⟩
      exact ⟨by simpa [Set.mem_preimage, hEq y hyA] using hyS, y, hyA, rfl⟩
    · rintro ⟨hzS, y, hyA, rfl⟩
      exact ⟨y, ⟨by simpa [Set.mem_preimage, hEq y hyA] using hzS, hyA⟩, rfl⟩
  calc ∫⁻ y in f '' A, g y ∂(μH[(k : ℝ)]) = ∫⁻ z, g z ∂(ρ.map f') := by rw [hmap]
    _ = ∫⁻ x, g (f' x) ∂ρ := lintegral_map hg hf'm
    _ = ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) * g (f' x)
          ∂(μH[(k : ℝ)]) := lintegral_withDensity_eq_lintegral_mul _ hJ (hg.comp hf'm)
    _ = _ := setLIntegral_congr_fun hA fun x hx => by rw [hEq x hx, mul_comm]

end GroundTheory.Heights₂.Heights
