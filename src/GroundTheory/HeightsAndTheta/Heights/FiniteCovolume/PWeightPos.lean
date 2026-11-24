module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
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

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module Matrix
open scoped ComplexOrder

section Steps

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem WeightPos.proof (h : GroundTheory.Automorphic.HermitianForm F E W) (v : Basis ι E W)
    (h₁ : VecAtNeZero.Statement v) : WeightPos.Statement h v := by
  intro M g x hx w
  set k : GL ι ℂ := ((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w with hk
  have hne : invApply g (vecAt v x) w ≠ 0 := by
    intro hz
    have hz' : (k : Matrix ι ι ℂ) *ᵥ vecAt v x w = 0 := hz
    have h2 : ((k⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ ((k : Matrix ι ι ℂ) *ᵥ vecAt v x w) = 0 := by
      rw [hz', mulVec_zero]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at h2
    exact h₁ x hx w h2
  have hpos := (M.posDef w).dotProduct_mulVec_pos hne
  exact (Complex.pos_iff.mp hpos).1

end Steps

end GroundTheory.Heights₂.Heights.FiniteCovolume
