module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mul_prod_of_separately {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (b : ∀ i, X i → ℂ) (β : (∀ i, X i) → ℂ)
    (h : ∀ i x, ∃ c : ℂ, ∀ y, β (Function.update x i y) = c * b i y) : ∃ l : ℂ, ∀ x, β x = (∏ i, b i (x i)) * l := by
  by_cases h0 : ∃ i, ∀ y, b i y = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun x => ?_⟩
    obtain ⟨c, hc⟩ := h i x
    have := hc (x i)
    rw [Function.update_eq_self, hi] at this
    simp [this]
  push_neg at h0
  choose x₀ hx₀ using h0
  have key : ∀ s : Finset ι, ∀ x, (∀ i, i ∉ s → x i = x₀ i) →
      β x * ∏ i ∈ s, b i (x₀ i) = β x₀ * ∏ i ∈ s, b i (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; rw [show x = x₀ from funext fun i => hx i (by simp)]
    | insert j s hj ih =>
      intro x hx
      obtain ⟨c, hc⟩ := h j x
      have e1 := hc (x j)
      rw [Function.update_eq_self] at e1
      have e2 := ih (Function.update x j (x₀ j)) fun i hi => by
        by_cases e : i = j
        · subst e; simp
        · rw [Function.update_of_ne e]; exact hx i (by simp [e, hi])
      have e3 : ∏ i ∈ s, b i (Function.update x j (x₀ j) i) = ∏ i ∈ s, b i (x i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
      rw [hc, e3] at e2
      rw [Finset.prod_insert hj, Finset.prod_insert hj, e1]
      linear_combination b j (x j) * e2
  have hn : ∏ i, b i (x₀ i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hx₀ i
  refine ⟨β x₀ / ∏ i, b i (x₀ i), fun x => ?_⟩
  have := key Finset.univ x (by simp)
  field_simp
  linear_combination this

end GlobalTheory.SepRows

end
