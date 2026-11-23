module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain
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

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_range_of_integral_at_heightOne_over :
    ∀ (B K : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
      [Field K] [Algebra B K] [IsFractionRing B K] (ϖ : B) (x : K), ϖ ≠ 0 →
      (∃ (N : ℕ) (b : B), algebraMap B K b = algebraMap B K ϖ ^ N * x) →
      (∀ P : Ideal B, P.IsPrime → P.height = 1 → ϖ ∈ P →
        ∃ (b c : B), c ∉ P ∧ algebraMap B K b = algebraMap B K c * x) →
      ∃ b : B, algebraMap B K b = x := by
  intro B K _ _ _ _ _ _ _ ϖ x _ hN hP
  obtain ⟨N, b, hb⟩ := hN
  obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := B) (K := K) x
    (fun p hp h1 => by
      by_cases hm : ϖ ∈ p
      · obtain ⟨b', c, hc, hbc⟩ := hP p hp h1 hm
        exact ⟨b', c, hc, by rw [hbc, mul_comm]⟩
      · exact ⟨b, ϖ ^ N, fun h => hm (hp.mem_of_pow_mem N h), by rw [hb, map_pow, mul_comm]⟩)
  exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.Ar.Flat
