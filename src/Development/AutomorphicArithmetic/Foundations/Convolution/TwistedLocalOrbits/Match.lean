module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc

noncomputable section

namespace UpperTheory.ConvolutionTheory.Loc

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} [TopologicalSpace k] [TopologicalSpace E]
  [MeasurableSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)]

def Match (σ : E ≃ₐ[k] E) (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) (φ : GL (Fin n) E → ℂ) (f : GL (Fin n) k → ℂ) : Prop :=
  (∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
      (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
      IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ → μδ.IsHaarMeasure → μγ.IsHaarMeasure →
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
        Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
      twOrbIntegralC (sigmaGL σ) μE δ μδ φ = orbIntegralC μk γ μγ f) ∧
  ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
    IsRegSemisimple γ → (¬ ∃ δ : GL (Fin n) E, IsNormOf σ δ γ) → μγ.IsHaarMeasure → orbIntegralC μk γ μγ f = 0

end UpperTheory.ConvolutionTheory.Loc

end
