module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial
open scoped TensorProduct Pointwise

namespace GlobalTheory.CM

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem baseChange_neg_form (D : Datum H) (x y : ℝ ⊗[ℤ] D.La) :
    (-D.EF).baseChange ℝ x y = -D.EF.baseChange ℝ x y := by
  induction x with
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
  | tmul r a =>
    induction y with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]; ring
    | tmul s b => simp

def oppDatum (D : Datum H) : Datum H where
  La := D.La
  fin := D.fin
  proj := D.proj
  EF := -D.EF
  alt x := by simp [D.alt]
  unimod := by
    have : (⇑(-D.EF) : D.La → _) = (fun f => -f) ∘ D.EF := rfl
    rw [this]
    exact neg_involutive.bijective.comp D.unimod
  adj a x y := by simp [D.adj]
  p := D.q
  q := D.p
  rank := by rw [D.rank, add_comm]
  dom := by
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    refine ⟨-J, fun x => by simp [h1], fun x y => ?_, fun x hx => ?_, fun a A t hA ht => ?_⟩
    · simp [baseChange_neg_form, h2]
    · simpa [baseChange_neg_form] using h3 x hx
    · obtain ⟨e1, e2, e3⟩ := h4 a A (starRingEnd ℂ t) hA (by

        rw [ht, map_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp [add_comm])
      refine ⟨by rw [LinearMap.neg_comp, LinearMap.comp_neg, e1], by simpa using e2, ?_⟩
      rw [LinearMap.neg_comp, map_neg, e3]
      simp

end General

namespace CyclotomicTwentyEight

end CyclotomicTwentyEight

end GlobalTheory.CM
