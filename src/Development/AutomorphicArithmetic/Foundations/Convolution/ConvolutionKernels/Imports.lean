module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalAdEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistExAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory NumberField PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.K

theorem UpperTheory.ConvolutionTheory.K.g0 :
    G0 := by
  refine ⟨fun F E _ _ _ _ _ _ σ _ n _ μ _ => ?_, fun F _ _ n μ _ g => ?_⟩
  · obtain ⟨θ, h⟩ := galTwistEx E n μ σ.toRingEquiv
    exact ⟨θ, fun g => by rw [galAdEq]; exact h g⟩
  · rw [galAdEq]
    ext i j : 2
    exact ((adBasic F).2.1 _).symm
