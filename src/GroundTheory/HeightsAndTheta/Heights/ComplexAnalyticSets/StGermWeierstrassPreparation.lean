module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassDivision
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def weierstrassPolynomial {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (x : Option σ → ℂ) : ℂ :=
  x none ^ d + ∑ j : Fin d, c j (fun i => x (some i)) * x none ^ (j : ℕ)

theorem weierstrassPolynomial_pointWithLast_zero {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, c j 0 = 0) (t : ℂ) : weierstrassPolynomial c (pointWithLast 0 t) = t ^ d := by
  have h : (fun i => pointWithLast (0 : σ → ℂ) t (some i)) = 0 := rfl
  simp only [weierstrassPolynomial, h, hc, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

def WeierstrassPreparation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 →
    analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = d →
    ∃ (e : (Option σ → ℂ) → ℂ) (c : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ e 0 ∧ e 0 ≠ 0 ∧ (∀ j, AnalyticAt ℂ (c j) 0) ∧ (∀ j, c j 0 = 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = e x * weierstrassPolynomial c x

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
