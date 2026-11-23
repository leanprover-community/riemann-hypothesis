module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section


open Coinv in
theorem CoinvIdealRepresentation.proof : CoinvIdealRepresentation.Statement := by
  intro K _ f n J hJ
  induction hJ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m₀, b₀, h1, h2, rfl⟩ := hx
    refine ⟨fun m b => if m = m₀ ∧ b = b₀ then 1 else 0, ?_⟩
    have hm₀ : m₀ ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨h1, h2⟩
    symm
    rw [Finset.sum_eq_single m₀]
    · rw [Finset.sum_eq_single b₀]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ b₀) h
    · intro m _ hm
      apply Finset.sum_eq_zero
      intro b _
      simp [hm]
    · intro h
      exact absurd hm₀ h
  | zero =>
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hy
    refine ⟨a + a', ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  | smul r x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨fun m b => r * a m b, ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun b _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights.RestTerms
