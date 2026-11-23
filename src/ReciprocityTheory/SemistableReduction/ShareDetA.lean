module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix Filter Topology Set

theorem analyticOnNhd_V_of_differentiableOn {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℂ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (hf : DifferentiableOn ℂ f B) :
    AnalyticOnNhd ℂ f B := by
  intro x hx
  let e : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' B) := hB.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' B) :=
    hf.comp e.symm.differentiable.differentiableOn (fun y hy => hy)
  have ha := ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU hg (e x) (by simpa using hx)
  have hfe : f = (f ∘ e.symm) ∘ e := by ext y; simp
  rw [hfe]
  exact ha.comp ((e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)).analyticAt x)

theorem differentiableOn_finset_prod' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [DecidableEq ι] {F : ι → E → ℂ} {B : Set E}
    (hF : ∀ i, DifferentiableOn ℂ (F i) B) (s : Finset ι) :
    DifferentiableOn ℂ (fun v => ∏ i ∈ s, F i v) B := by
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a).mul ih

theorem differentiableOn_det_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Type} [Fintype U] [DecidableEq U] {F : U → U → E → ℂ} {B : Set E}
    (hF : ∀ a b, DifferentiableOn ℂ (F a b) B) :
    DifferentiableOn ℂ (fun v => (Matrix.of fun a b => F a b v).det) B := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  exact (differentiableOn_const _).mul
    (differentiableOn_finset_prod' (F := fun i v => F (σ i) i v) (fun i => hF _ _) _)

end ReciprocityTheory.MultiplicativeHeights
