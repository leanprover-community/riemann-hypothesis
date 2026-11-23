module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem MinimalPrimesSpanSingleton.proof : MinimalPrimesSpanSingleton.Statement.{u} := by
  intro A _ _ _ x hx W
  constructor
  · intro hW
    have hWp : W.IsPrime := hW.isPrime
    have hxW : x ∈ W := hW.1.2 (Ideal.mem_span_singleton_self x)
    refine ⟨hWp, ?_, hxW⟩
    have hle : W.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) W hW
    have hne : W.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      rw [hbot, Ideal.mem_bot] at hxW
      exact hx hxW
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  · rintro ⟨hWp, hh, hxW⟩
    refine ⟨⟨hWp, (Ideal.span_singleton_le_iff_mem W).mpr hxW⟩, ?_⟩
    rintro Q ⟨hQp, hxQ⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ (h ▸ le_refl Q))
    have hfin : W.FiniteHeight := W.finiteHeight_iff.mpr (Or.inr (by rw [hh]; exact ENat.one_ne_top))
    have hQh : Q.height < 1 := hh ▸ Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    have hQ0 : Q.height = 0 := Order.lt_one_iff.mp hQh
    rw [Ideal.height_eq_zero_iff_eq_bot] at hQ0
    have hx0 : x ∈ (⊥ : Ideal A) := hQ0 ▸ (Ideal.span_singleton_le_iff_mem Q).mp hxQ
    exact hx ((Ideal.mem_bot).mp hx0)

end GroundTheory.Heights₂.Heights.NumbersDVR
