module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

section Coordinate

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def unipCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (n : unipRadical h v x₀) :
    InfinitePlace E → ι → ℂ :=
  fun w => (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
    vecAt v w₀ w

omit [NumberField E] in
theorem unipCoord_apply (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (n : unipRadical h v x₀) (w : InfinitePlace E) :
    unipCoord h v x₀ w₀ n w =
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
        vecAt v w₀ w :=
  rfl


omit [NumberField E] in
theorem continuous_unipCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    Continuous (unipCoord h v x₀ w₀) := by
  refine continuous_pi fun w => ?_
  have hc : Continuous fun n : unipRadical h v x₀ =>
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
    Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  exact (hc.matrix_mulVec continuous_const).sub continuous_const

def UnipotentCoordProper.Statement [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ → ∀ K : Set (InfinitePlace E → ι → ℂ), IsCompact K →
    IsCompact {n : unipRadical h v x₀ | unipCoord h v x₀ w₀ n ∈ K}

end Coordinate

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
