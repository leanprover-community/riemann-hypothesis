module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem parCont_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Continuous (TR.infGL F 2) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((TR.continuous_infEq F).prodMk continuous_const :
    Continuous fun x : TR.Rinf F => ((TR.infEq F x, 0) : InfiniteAdeleRing F × Af F))))

private theorem parCont_val {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {c : ℝ → GL (Fin 2) (TR.Rinf F)} {Y : TR.Lie F 2} (h : Par c Y) :
    Continuous fun t => (c t).val := by
  have h0 : ContinuousAt (fun t => (c t).val) 0 := h.2.continuousAt
  refine continuous_iff_continuousAt.2 fun t => ?_
  have e : (fun s => (c s).val) = fun s => (c t).val * (c (s - t)).val := by
    funext s
    rw [← Units.val_mul, ← h.1, add_sub_cancel]
  rw [e]
  have hs : ContinuousAt (fun s : ℝ => s - t) t := (continuous_id.sub continuous_const).continuousAt
  have h0' : ContinuousAt (fun t => (c t).val) ((fun s : ℝ => s - t) t) := by
    simpa using h0
  exact continuousAt_const.mul (ContinuousAt.comp (f := fun s : ℝ => s - t) h0' hs)

theorem UpperTheory.ConvolutionTheory.R2.Ff.parCont :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ParCont F := by
  intro F _ _ _
  refine ⟨parCont_infGL F, fun c Y h => ?_⟩
  have h1 : c 0 = 1 := by
    have := h.1 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← h.1, add_neg_cancel, h1])
  have hv := parCont_val h
  refine ⟨h1, Units.continuous_iff.2 ⟨hv, ?_⟩, ?_, ?_⟩
  · have : (fun t => ((c t)⁻¹ : GL (Fin 2) (TR.Rinf F)).val) = fun t => (c (-t)).val := by
      funext t; rw [hinv]
    change Continuous (fun t => ((c t)⁻¹ : GL (Fin 2) (TR.Rinf F)).val)
    rw [this]
    exact hv.comp continuous_neg
  · intro s t
    change c (-(s + t)) = c (-s) * c (-t)
    rw [neg_add, h.1]
  · have h2 : HasDerivAt (fun t => TR.toL (c t).val) Y (-(0 : ℝ)) := by simpa using h.2
    have := HasDerivAt.scomp (0 : ℝ) h2 (hasDerivAt_neg 0)
    simpa [Function.comp_def] using this
