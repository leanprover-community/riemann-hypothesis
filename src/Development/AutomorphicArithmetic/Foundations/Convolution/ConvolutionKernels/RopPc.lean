module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.CommProj
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj
public import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.ropPc :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n),
      Rop μ f ∘L Pc μ = Pc μ ∘L Rop μ f := by
  intro K _ _ n μ _ f
  have h : ∀ g : CC K n, ∀ v ∈ cuspidalL2 μ, Rop μ g v ∈ cuspidalL2 μ := by
    intro g v hv
    rw [← Submodule.orthogonal_orthogonal (cuspidalL2 μ), Submodule.mem_orthogonal]
    intro u hu
    rw [Rop, inner_integrated_ccToL1]
    have : ∀ x, ⟪u, rightRegularRep (Gam K n) μ x v⟫_ℂ = 0 := fun x =>
      (Submodule.mem_orthogonal' _ _).1 hu _ (isInvariant_cuspidalL2 μ x v hv)
    simp [this]
  exact commProj (cuspidalL2 μ) (Rop μ f) (h f) (fun v hv => by rw [ropAdj]; exact h _ v hv)
