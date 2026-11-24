module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem map_withDensity_of_jacobian_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (J : E → ℝ) (ψ : E → E) (hψ : Continuous ψ)
    (hb : Function.Bijective ψ)
    (h : ∀ B, ∃ P : E →L[ℝ] E, HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) :
    Measure.map ψ (μ.withDensity fun B => ENNReal.ofReal (J B)) =
      μ.withDensity fun B => ENNReal.ofReal (J B) := by

  choose P hP hJ using h
  have hm : Measurable ψ := hψ.measurable
  ext A hA
  rw [Measure.map_apply hm hA, withDensity_apply _ hA, withDensity_apply _ (hm hA)]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hm hA)
    (fun x _ => (hP x).hasFDerivWithinAt) hb.injective.injOn (fun y => ENNReal.ofReal (J y))
  rw [Set.image_preimage_eq A hb.surjective] at hcv
  rw [hcv]
  refine lintegral_congr (fun x => ?_)
  rw [← ENNReal.ofReal_mul (abs_nonneg _), hJ x]

theorem map_withDensity_of_jacobian : ∀ (p q : ℕ) (J : (Fin p → Fin q → ℂ) → ℝ) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous J → Continuous ψ → Function.Bijective ψ → (∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) → Measure.map ψ (volume.withDensity fun B => ENNReal.ofReal (J B)) = volume.withDensity fun B => ENNReal.ofReal (J B) := by

  intro p q J ψ _ hψ hb h
  haveI hrow : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; infer_instance
  haveI hall : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  exact map_withDensity_of_jacobian_gen (volume : Measure (Fin p → Fin q → ℂ)) J ψ hψ hb h

end GlobalTheory
