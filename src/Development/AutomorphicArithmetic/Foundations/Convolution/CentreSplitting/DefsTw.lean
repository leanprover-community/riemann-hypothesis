module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.V

namespace UpperTheory.ConvolutionTheory.Dp

def TwUnitary : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ), (∀ v, ‖θ.U v‖ = ‖v‖) ∧ Function.Surjective θ.U ∧
      ∀ g v, θ.U (rightRegularRep (rationalGLOne (K := K) (n := n)) μ g v) = rightRegularRep (rationalGLOne (K := K) (n := n)) μ (θ.e g) (θ.U v)

def TwCls : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ), ∀ φ ∈ centralCuspForms K n, ∀ ψ ∈ centralCuspForms K n,
      (θ.U (clsL μ ψ) = clsL μ φ ↔ ∀ x : normOneGL (K := K) (n := n), ψ.1 x = φ.1 (θ.e x : normOneGL (K := K) (n := n)))

def TwSummand : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ) (V : Submodule ℂ (LL μ)), IsSummand μ V ↔ IsSummand μ (V.map θ.U.toLinearMap)

def GalCentral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (σ : E ≃+* E) (s : Ad E ≃+* Ad E),
    UpperTheory.CBC.IsGalAd σ s → (∀ s', UpperTheory.CBC.IsGalAd σ s' → s' = s) ∧
      ∀ t, Matrix.GeneralLinearGroup.map s.toRingHom (centralSection E n t) = centralSection E n t

def ConjCarries : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ) (σ : E ≃+* E) (s : Ad E ≃+* Ad E), UpperTheory.CBC.IsGalAd σ s →
    (∀ g : normOneGL (K := E) (n := n), ((θ.e g : normOneGL (K := E) (n := n)) : GA E n) = Matrix.GeneralLinearGroup.map s.toRingHom (g : GA E n)) →
    ∀ (π π' : CuspSub E n) (V' : Submodule ℂ (LL μ)),
      (UpperTheory.CBC.Cusp.cx π').space =
        (fun f : GA E n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (UpperTheory.CBC.Cusp.cx π).space →
      (Carries μ π' V' ↔ Carries μ π (V'.map θ.U.toLinearMap))

def ConjIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
    (θ : PositivityTheory.Rg.Tf.Core.Twist μ) (σ : E ≃+* E) (s : Ad E ≃+* Ad E), UpperTheory.CBC.IsGalAd σ s →
    (∀ g : normOneGL (K := E) (n := n), ((θ.e g : normOneGL (K := E) (n := n)) : GA E n) = Matrix.GeneralLinearGroup.map s.toRingHom (g : GA E n)) →
    ∀ (π : CuspSub E n) (V : Submodule ℂ (LL μ)), Carries μ π V →
      ((UpperTheory.CBC.Cusp.cx π).ConjIso σ ↔ V.map θ.U.toLinearMap = V)

end UpperTheory.ConvolutionTheory.Dp
