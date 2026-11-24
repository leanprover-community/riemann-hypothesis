module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
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
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.unitA :
    ∀ (F : Type) [Field F] [NumberField F] (x : A F), IsUnit x ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (x.2 v) = 1 := by
  intro F _ _ x
  constructor
  · rintro ⟨a, rfl⟩
    have hinf : ∀ w, (a : A F).1 w * ((a⁻¹ : (A F)ˣ) : A F).1 w = 1 := fun w =>
      congrArg (fun z : A F => z.1 w) a.mul_inv
    have hfin : ∀ v, (a : A F).2 v * ((a⁻¹ : (A F)ˣ) : A F).2 v = 1 := fun v =>
      congrArg (fun z : A F => z.2 v) a.mul_inv
    refine ⟨fun w h => ?_, fun v h => ?_, ?_⟩
    · have := hinf w
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · have := hfin v
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · filter_upwards [(a : A F).2.2, ((a⁻¹ : (A F)ˣ) : A F).2.2] with v h3 h4
      have hm := congrArg Valued.v (hfin v)
      rw [map_mul, map_one] at hm
      refine le_antisymm h3 ?_
      rw [← hm]
      exact mul_le_of_le_one_right' h4
  · rintro ⟨h1, h2, h3⟩
    have hmem : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
        (x.2 v)⁻¹ ∈ v.adicCompletionIntegers F := by
      filter_upwards [h3] with v hv
      change Valued.v (x.2 v)⁻¹ ≤ 1
      rw [map_inv₀, hv, inv_one]
    let y : A F := (fun w => (x.1 w)⁻¹, ⟨fun v => (x.2 v)⁻¹, hmem⟩)
    refine IsUnit.of_mul_eq_one y (Prod.ext (funext fun w => ?_) ?_)
    · exact mul_inv_cancel₀ (h1 w)
    · apply RestrictedProduct.ext
      intro v
      exact mul_inv_cancel₀ (h2 v)
