module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAb
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousScalarFour
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.IntegrableMulChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThDer
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.thDerOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ThDerOm W := by
  intro F E _ _ _ _ _ _ _ D W φ φ' hφ' G hG hD g h t

  have hcomm : ∀ (g : G1 F) (x : S4 F),
      W.Om g (W.L h x) = W.L h (W.Om (cD (nu F h)⁻¹ g) x) := by
    intro g x
    have e := W.comm h (cD (nu F h)⁻¹ g)
    rw [← cD_mul_left, mul_inv_cancel, cD_one_left] at e
    have e' := congrArg (fun T : Module.End ℂ (S4 F) => T x) e
    simpa only [Module.End.mul_apply] using e'.symm
  have hmul : ∀ (a b : G1 F) (x : S4 F), W.Om (a * b) x = W.Om a (W.Om b x) := by
    intro a b x
    rw [map_mul, Module.End.mul_apply]

  have hDL : Der (fun s => W.L h (W.Om (G s) φ)) (fun s => W.L h (W.Om (G s) φ')) := by
    intro s v
    simp only [W.L_apply]
    exact (hD s _).const_mul _

  have hdom : ∀ (g : G1 F) (t : ℝ),
      Dom (Metric.ball t 1) fun s => (W.Om g (W.L h (W.Om (G s) φ'))).1 := by
    intro g t
    let c : ℝ → G1 F := fun s => cD (nu F h)⁻¹ g * G s
    have hc : Continuous c := continuous_const.mul hG
    have hC : IsCompact (c '' Metric.closedBall t 1) := (isCompact_closedBall t 1).image hc
    obtain ⟨K, hK, hB⟩ := lDom F E D W (G1 F) (c '' Metric.closedBall t 1) (fun k => W.Om k φ')
      (omCpt F E D W φ' hφ' _ hC) {h} isCompact_singleton
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB⟩ := hB N
    refine ⟨B, fun s hs v => ?_⟩
    have hmem : ((h, c s) : GL (Fin 2) (A E) × G1 F) ∈ ({h} : Set _) ×ˢ (c '' Metric.closedBall t 1) :=
      ⟨rfl, s, Metric.ball_subset_closedBall hs, rfl⟩
    have := hB _ hmem v
    simpa only [hcomm, hmul, c] using this
  exact thDer F _ _ (omDer F E D W _ _ hDL hdom g) t (hdom g t)
