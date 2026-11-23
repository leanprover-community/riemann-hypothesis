module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem linearMap_comp_eq_on_smul_of_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (A B : V →L[ℝ] V)
    (h1 : ∀ x, B (A x) = x) (h2 : ∀ x, A (B x) = x) (f : V → ℂ) :
    ∫ x, f (A x) ∂μ = ((|(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| : ℝ) : ℂ) * ∫ x, f x ∂μ := by
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.equivOfInverse A B h1 h2
  have hd : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hm : MeasurableEmbedding (A : V →ₗ[ℝ] V) := e.toHomeomorph.measurableEmbedding
  have := hm.integral_map (μ := μ) f
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)] at this
  rw [← Complex.real_smul, this]
  rfl

theorem UpperTheory.V.Af.Smo.linChange :
    UpperTheory.V.Af.Smo.LinChange := by
  intro E _ _ n
  refine ⟨fun s => ((|(LinearMap.det (lmul (toL s.val) : Lie E n →ₗ[ℝ] Lie E n))⁻¹| : ℝ) : ℂ), ?_, fun s f => ?_⟩
  · have : (lmul (toL (1 : GL (Fin n) (Rinf E)).val) : Lie E n →ₗ[ℝ] Lie E n) = LinearMap.id :=
      LinearMap.ext fun x => one_mul (Matrix.of x)
    simp only [this]
    simp
  · haveI : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
    haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    exact linearMap_comp_eq_on_smul_of_eq volume (lmul (toL s.val)) (lmul (toL (s⁻¹).val))
      (fun x => s.inv_mul_cancel_left (Matrix.of x)) (fun x => s.mul_inv_cancel_left (Matrix.of x)) f
