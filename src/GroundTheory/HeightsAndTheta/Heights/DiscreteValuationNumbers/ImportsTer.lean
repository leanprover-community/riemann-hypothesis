module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem LocalCoefficient.proof (h₁ : LeftTermSupport.Statement.{u})
    (h₂ : RightTermSupport.Statement.{u}) (h₃ : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno U hUdim
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U
  swap
  ·
    have hl := h₁ O ϖ K ι P hP.multiProj.multiHomog b f g hD.1 c s hs
    have hr := h₂ O ϖ K ι P hP.multiProj.multiHomog b f g hD c s hs hH
    unfold cycEval
    rw [finsum_congr fun G => hl G U hU, finsum_congr fun W => hr W U hU, finsum_zero]
  obtain ⟨hUp, hUm, hUr, hϖU, hPU⟩ := hU
  have hUdim' := hUdim hUp hUm hUr hϖU
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hrel : ∀ W : Ideal (MRing ι O), W ≤ U → IsRelevant W := fun W hW k =>
    let ⟨i, hi⟩ := hUr k
    ⟨i, fun h => hi (hW h)⟩
  have hcyc : ∀ J W : Ideal (MRing ι O), IsRelevant W → idealCycle J W = locCycle J W := by
    intro J W hW
    unfold idealCycle locCycle
    by_cases hm : W ∈ J.minimalPrimes
    · rw [dite_eq_left ⟨hm, hW⟩, dite_eq_left hm]
      rfl
    · rw [dite_eq_right fun h => hm h.1, dite_eq_right hm]
  have hzero : ∀ J : Ideal (MRing ι O), ¬ J ≤ U → locCycle J U = 0 := by
    intro J hJ
    unfold locCycle
    rw [dite_eq_right fun h => hJ h.1.2]
  have hL : ∀ G, ratDiv P f g G * divCycle G s U =
      (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U := by
    intro G
    rw [divCycle_eq_idealCycle, hcyc _ _ hUr]
    by_cases hG : G ≤ U
    · unfold ratDiv
      rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel G hG), hcyc _ _ (hrel G hG)]
    · rw [hzero _ fun h => hG (le_sup_left.trans h), mul_zero, mul_zero]
  have hR : ∀ W, divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U =
      locCycle (P ⊔ Ideal.span {s}) W * locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U := by
    intro W
    show divCycle P s W * idealCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U = _
    rw [hcyc _ _ hUr]
    by_cases hW : W ≤ U
    · rw [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    · rw [hzero _ fun h => hW (le_sup_left.trans h), mul_zero, mul_zero]

  have hchain : ∀ Q₁ Q₂ : Ideal (MRing ι O), Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U →
      False := by
    intro Q₁ Q₂ _ _ hPQ hQQ hQU
    have e₁ := DimStrictDrop.proof (MRing ι O) P Q₁ hPQ
    have e₂ := DimStrictDrop.proof (MRing ι O) Q₁ Q₂ hQQ
    have e₃ := DimStrictDrop.proof (MRing ι O) Q₂ U hQU
    rw [hP.dim] at e₁
    have key : ((d + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 + 1 + 1 ≤
        ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      ((add_le_add (add_le_add (add_le_add hUdim' le_rfl) le_rfl) le_rfl).trans
        ((add_le_add (add_le_add e₃ le_rfl) le_rfl).trans ((add_le_add e₂ le_rfl).trans e₁)))
    have key' : ((d + Fintype.card K + 3 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two, two_add_one_eq_three] using key
    have := WithBot.coe_le_coe.mp key'
    norm_cast at this
    omega

  obtain ⟨u', v', hu', huv⟩ := hD.2 U hUp hPU hUr

  have hnc : ∀ W : Ideal (MRing ι O), W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W := by
    intro W hW h
    have hs' : divCycle P s W ≠ 0 := by rwa [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    have hr : ratDiv P f g W = 0 := by
      by_cases hϖW : (C ϖ : MRing ι O) ∈ W
      · exact hno W hϖW hs'
      · by_contra h
        exact hϖW (hD.1.vertical W h)
    unfold ratDiv at hr
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel W hW),
      hcyc _ _ (hrel W hW)] at hr
    omega
  unfold cycEval
  rw [finsum_congr hL, finsum_congr hR]
  exact h₃ (MRing ι O) P U hPp hUp hPU hchain f g s u' v' hD.1.num_not_mem hD.1.den_not_mem hsP hu'
    huv hnc

end GroundTheory.Heights₂.Heights.NumbersDVR
