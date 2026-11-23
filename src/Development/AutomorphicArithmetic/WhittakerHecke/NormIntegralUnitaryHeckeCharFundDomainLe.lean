module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le :
    ∀ (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (f : IdeleGroup ℚ → G1 ℚ → ℂ) (B : ℝ), (∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) → Measurable (Function.uncurry f) →
        (∀ u ∈ UU, ∀ g, ‖f u g‖ ≤ B) →
        (∀ u ∈ UU, IntegrableOn (f u) M.D M.μ) ∧ Integrable (fun u => ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ) U.υ ∧
          ‖∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ ∂U.υ‖ ≤ B * M.μ.real M.D := by
  intro M U χ f B hχ hf hB
  haveI := U.prob
  have hD : M.μ M.D < ⊤ := UpperTheory.ConvolutionTheory.R2.M.volD ℚ M
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using hD⟩
  have hfu : ∀ u, Measurable (f u) := fun u => hf.comp measurable_prodMk_left
  have hae : ∀ᵐ u ∂U.υ, u ∈ (UU : Set (A ℚ)ˣ) := mem_ae_iff.mpr U.supp
  have hI : StronglyMeasurable (fun u => ∫ g in M.D, f u g ∂M.μ) :=
    (hf.stronglyMeasurable).integral_prod_right
  have hχm : Measurable (fun u : IdeleGroup ℚ => ((χ.1 u : ℂˣ) : ℂ)) :=
    (Units.continuous_val.comp χ.2.1).measurable
  have hbd : ∀ᵐ u ∂U.υ, ‖((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ‖ ≤ B * M.μ.real M.D := by
    filter_upwards [hae] with u hu
    rw [norm_mul, hχ, one_mul]
    exact norm_setIntegral_le_of_norm_le_const hD (fun g _ => hB u hu g)
  refine ⟨fun u hu => Integrable.of_bound (hfu u).aestronglyMeasurable B (Eventually.of_forall (hB u hu)), ?_, ?_⟩
  · exact Integrable.of_bound (hχm.aestronglyMeasurable.mul hI.aestronglyMeasurable) _ hbd
  · simpa using norm_integral_le_of_norm_le_const hbd
