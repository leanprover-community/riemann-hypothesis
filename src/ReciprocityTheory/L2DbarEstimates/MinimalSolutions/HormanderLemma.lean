module

public import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolutionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

section WeakAdjLemmas

variable {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

theorem WeakAdj.sub {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f f' : H₂} {w w' : H₁}
    (h : WeakAdj ι t f w) (h' : WeakAdj ι t f' w') : WeakAdj ι t (f - f') (w - w') := by
  intro g
  rw [inner_sub_right, inner_sub_right, h g, h' g]

end WeakAdjLemmas

theorem split (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] :
    SplitStatement E H₁ H₂ := by
  intro ι t K hK hrange f w hfw
  haveI : CompleteSpace K := hK.completeSpace_coe
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := K.exists_add_mem_mem_orthogonal f
  have h2 : WeakAdj ι t f₂ 0 := by
    intro g
    rw [inner_zero_right]
    exact Submodule.inner_right_of_mem_orthogonal (hrange (LinearMap.mem_range_self t g)) hf₂
  refine ⟨f₁, f₂, rfl, hf₁, hf₂, ?_, h2⟩
  have h1 := hfw.sub h2
  simpa using h1

end ReciprocityTheory.L2DbarEstimates
