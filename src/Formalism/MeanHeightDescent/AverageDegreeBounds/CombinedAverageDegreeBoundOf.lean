module

public import Formalism.MeanHeightDescent.CombinedAverageDegreeBound
public import Formalism.MeanHeightDescent.BadRowsNumeric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

namespace Formalism.ExtensionFiltration

theorem meanHeightLowerBound : MeanHeights := by
  intro ι _ _ h sl cs cc ρ X hρ0 hρ1 hX hpos hsl hmean
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply max_le
  · exact div_nonneg (Finset.sum_nonneg fun c _ => hpos c) hN.le
  · rw [le_div_iff₀ hN]
    rw [le_div_iff₀ hN] at hmean
    have hpt : ∀ c ∈ (univ : Finset ι), (1 - ρ) * (sl c + cs) - cc ≤ h c + cs := fun c _ => by
      have h1 := hsl c
      have h2 : sl c + cs ≤ max 0 (sl c + cs) := le_max_right _ _
      nlinarith
    have hsum := Finset.sum_le_sum hpt
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at hsum ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (by linarith : (0 : ℝ) ≤ (∑ c, sl c) + X * Fintype.card ι),
      mul_nonneg (mul_nonneg hρ0 hX) hN.le]

theorem combinedAverageDegreeBound_of (h1 : MeanHeights) (h2 : SumComponents) : CombinedAverageDegreeBound := by
  intro ι _ _ T D A cs X cc z ρ R1 R2 Bn δ' h sl δ dc degc LL0 U b Ca Cb PPf e1 e2 muU hD hT hA hcs hX hcc
    hz0 hz1 hρ0 hρ1 hR1 hR2 hBn hδ' hδ hdc hhc hsl hmean hdeg hTX hTcc hb hmu
  have hm := h1 ι h sl cs cc ρ X hρ0 hρ1.le hX hhc hsl hmean
  have hs := h2 ι T D A cs X cc z ρ R1 R2 Bn δ' h δ dc degc hD hT hA hcs hX hcc hz0 hz1 hρ0 hρ1 hR1 hR2
    hBn hδ' hδ hdc (fun c => by linarith [hhc c]) hdeg hm
  nlinarith

end Formalism.ExtensionFiltration
