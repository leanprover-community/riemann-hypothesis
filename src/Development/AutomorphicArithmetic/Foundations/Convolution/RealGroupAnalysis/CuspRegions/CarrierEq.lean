module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

namespace UpperTheory.ConvolutionTheory.Dr

structure Carries {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (π : TR.CuspSub E n) (V : Submodule ℂ (LL μ)) : Prop where
  summand : IsSummand μ V
  carrier_eq : Fb.carrier π = formsIn μ V

def ExCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)), IsSummand μ V → ∃! π : TR.CuspSub E n, Carries μ π V

end UpperTheory.ConvolutionTheory.Dr

end
