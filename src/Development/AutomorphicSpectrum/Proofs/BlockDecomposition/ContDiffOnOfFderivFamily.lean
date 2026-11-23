module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open PositivityTheory.jumpWindows
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothVectors

theorem contDiffOn_of_fderiv_family {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {U : Set E} (hU : IsOpen U)
    (o : P → E → F) (S : Set P) (A : Fin n → E → E →L[ℝ] ℝ)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (h : ∀ v ∈ S, ∃ w : Fin n → P, (∀ i, w i ∈ S) ∧
      ∀ M ∈ U, HasFDerivAt (o v) (∑ i, (A i M).smulRight (o (w i) M)) M) :
    ∀ v ∈ S, ContDiffOn ℝ ∞ (o v) U := by
  have key : ∀ m : ℕ, ∀ v ∈ S, ContDiffOn ℝ m (o v) U := by
    intro m
    induction m with
    | zero =>
      intro v hv
      obtain ⟨w, -, hw⟩ := h v hv
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun M hM => (hw M hM).continuousAt.continuousWithinAt
    | succ m ih =>
      intro v hv
      obtain ⟨w, hwS, hw⟩ := h v hv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun M hM => (hw M hM).differentiableAt.differentiableWithinAt, fun hm => ?_, ?_⟩
      · exact absurd hm (by simp)
      · refine ContDiffOn.congr (f := fun M => ∑ i, (A i M).smulRight (o (w i) M)) ?_
          fun M hM => (hw M hM).fderiv
        exact ContDiffOn.sum fun i _ =>
          (contDiffOn_infty.1 (hA i) m).smulRight (ih (w i) (hwS i))
  intro v hv
  exact contDiffOn_infty.2 fun m => key m v hv

section Chart

variable {ι : Type} [Fintype ι] {a : ℕ}

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

end Norm

end Chart

section Orbit

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

end Orbit

end GlobalTheory.CompanionTheory.SmoothVectors

end
