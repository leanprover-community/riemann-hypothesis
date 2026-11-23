module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.Couple

theorem psi_eq_sum_coupIdx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z] (T : Chain k s X Z) (A : RepFam k s X) (c₁ c₂ : kˣ) (_ : T.Adapted A (box _ c₁) (box _ c₂)) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (ε : k) (S : Finset ((X (s + 1) → k) ⧸ box (X (s + 1)) c₂)) (_ : T.coupIdx A (box _ c₁) (box _ c₂) ⊆ S), ∀ g ∈ A s 0 rfl, ∀ x₀, (∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y) ∧ ∀ η, GlobalTheory.StepData.hat ψ ν ε (T.Psi g x₀) η = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * GlobalTheory.StepData.hat ψ ν ε (cosetInd (box _ c₂) yb) η := by
  intro k _ _ _ _ _ _ s X _ _ Z _ _ T A c₁ c₂ hA ψ hψ ν _ ε S hS g hg x₀
  classical
  have key : ∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := by
    intro y
    have hc : ∀ yb, cosetInd (box _ c₂) yb y = if Submodule.Quotient.mk y = yb then 1 else 0 := by
      intro yb; simp [cosetInd, Set.indicator_apply]
    simp_rw [hc, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · exact (T.xiPen_mk hA hg y x₀).symm
    · by_contra hne
      exact hm (Finset.mem_coe.1 (hS ⟨y, (hA g hg x₀ y).1 hne, rfl, g, hg, x₀, hne⟩))
  refine ⟨key, fun η => ?_⟩
  have hfun : T.Psi g x₀ = fun y => ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := funext key
  rw [hfun]
  simp only [GlobalTheory.StepData.hat, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun yb _ => ?_
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  · intro yb _
    simp_rw [mul_assoc]
    exact (integrable_hat ψ ν ε hψ (cosetInd_mem_SB c₂ yb) η).const_mul _

end GlobalTheory.Couple
