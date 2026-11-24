module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def UnifRestrictStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s →
    ∀ (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X), IsPotential A L' → IsSection A L' v →
      IsSNC A L' v ![1] ![Dg] →
      IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg) →
      ∃ (B : FinHolAtlas e Dg) (hB : HoloMap B A Subtype.val) (n' : ℕ) (m' : Fin n' → ℕ)
        (W' : Fin n' → Set Dg),
        IsPotential B (Θ.pullback Subtype.val hB.1) ∧ IsPosPot B (Θ.pullback Subtype.val hB.1) ∧
          IsSNC B (L.pullback Subtype.val hB.1) (fun x y => s x.1 y.1) m' W'

theorem mInt_neg_integrand {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (g : X → ℝ) : mInt A Φ (fun y => -g y) = -mInt A Φ g := by
  unfold mInt
  split_ifs
  · simp only [integralWith, mul_neg, neg_mul, integral_neg, Finset.sum_neg_distrib]
  · simp

end

end ReciprocityTheory.AnForm.P
