module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorDefs
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {C : Type} [Field C] (K : Subfield C) (W : WeierstrassCurve C)

theorem inSub_zero : InSub K (0 : W.toAffine.Point) := trivial

theorem negY_mem_sub (hW : CoeffSub K W) {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    W.toAffine.negY x y ∈ K := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  simp only [WeierstrassCurve.Affine.negY]
  repeat (first
    | assumption
    | exact K.zero_mem
    | exact K.one_mem
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)

theorem slope_mem_sub (hW : CoeffSub K W) {x₁ x₂ y₁ y₂ : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hy₁ : y₁ ∈ K) (hy₂ : y₂ ∈ K) : W.toAffine.slope x₁ x₂ y₁ y₂ ∈ K := by
  have n1 := negY_mem_sub K W hW hx₁ hy₁
  have n2 := negY_mem_sub K W hW hx₂ hy₂
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have c2 : (2 : C) ∈ K := by
    have h0 := natCast_mem K 2
    simpa using h0
  have c3 : (3 : C) ∈ K := by
    have h0 := natCast_mem K 3
    simpa using h0
  unfold WeierstrassCurve.Affine.slope
  split_ifs
  · exact K.zero_mem
  · repeat (first
    | assumption
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)
  · repeat (first
    | assumption
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.neg_mem)

theorem addX_mem_sub (hW : CoeffSub K W) {x₁ x₂ s : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hs : s ∈ K) : W.toAffine.addX x₁ x₂ s ∈ K := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  simp only [WeierstrassCurve.Affine.addX]
  repeat (first
    | assumption
    | exact K.zero_mem
    | exact K.one_mem
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)

theorem addY_mem_sub (hW : CoeffSub K W) {x₁ x₂ y₁ s : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hy₁ : y₁ ∈ K) (hs : s ∈ K) : W.toAffine.addY x₁ x₂ y₁ s ∈ K := by
  have hX := addX_mem_sub K W hW hx₁ hx₂ hs
  have hN : W.toAffine.negAddY x₁ x₂ y₁ s ∈ K := by
    simp only [WeierstrassCurve.Affine.negAddY]
    repeat (first
    | assumption
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.neg_mem)
  simp only [WeierstrassCurve.Affine.addY]
  exact negY_mem_sub K W hW hX hN

theorem inSub_neg (hW : CoeffSub K W) (P : W.toAffine.Point) (hP : InSub K P) : InSub K (-P) := by
  cases P with
  | zero => trivial
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact ⟨hP.1, negY_mem_sub K W hW hP.1 hP.2⟩

theorem inSub_add (hW : CoeffSub K W) (P Q : W.toAffine.Point) (hP : InSub K P) (hQ : InSub K Q) :
    InSub K (P + Q) := by
  cases P with
  | zero =>
    change InSub K ((0 : W.toAffine.Point) + _)
    rwa [zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change InSub K (_ + (0 : W.toAffine.Point))
      rwa [add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        trivial
      · rw [WeierstrassCurve.Affine.Point.add_some hxy]
        have hs := slope_mem_sub K W hW hP.1 hQ.1 hP.2 hQ.2
        exact ⟨addX_mem_sub K W hW hP.1 hQ.1 hs, addY_mem_sub K W hW hP.1 hQ.1 hP.2 hs⟩

theorem inSub_nsmul (hW : CoeffSub K W) (n : ℕ) (P : W.toAffine.Point) (hP : InSub K P) :
    InSub K (n • P) := by
  induction n with
  | zero => rw [zero_smul]; exact inSub_zero K W
  | succ n ih => rw [succ_nsmul]; exact inSub_add K W hW _ _ ih hP

theorem inSub_px (P : W.toAffine.Point) (hP : InSub K P) : px W P ∈ K ∧ py W P ∈ K := by
  cases P with
  | zero => exact ⟨K.zero_mem, K.zero_mem⟩
  | some x y h => exact hP

end ReciprocityTheory.ChartRestriction.L1
