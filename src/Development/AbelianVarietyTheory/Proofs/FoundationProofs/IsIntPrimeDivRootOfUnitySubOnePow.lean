module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

@[expose] public section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.K5.PDiv

open Polynomial

theorem prod_one_sub_pow_dvd {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (ζ : Ω) (hζ : IsIntegral (O0 p) ζ) (S : Finset Ω) (hS : ∀ μ ∈ S, ∃ i : ℕ, ζ ^ i = μ) :
    ∃ c : Ω, IsIntegral (O0 p) c ∧ ∏ μ ∈ S, (1 - μ) = (ζ - 1) ^ S.card * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, isIntegral_one, by simp⟩
  | insert a S ha ih =>
    obtain ⟨c, hc, e⟩ := ih (fun μ hμ => hS μ (Finset.mem_insert_of_mem hμ))
    obtain ⟨i, rfl⟩ := hS _ (Finset.mem_insert_self _ _)
    refine ⟨-(∑ k ∈ Finset.range i, ζ ^ k) * c, ?_, ?_⟩
    · refine IsIntegral.mul (IsIntegral.neg ?_) hc
      have : (∑ k ∈ Finset.range i, ζ ^ k) ∈ integralClosure (O0 p) Ω :=
        Subalgebra.sum_mem _ fun k _ => Subalgebra.pow_mem _ hζ k
      exact this
    · rw [Finset.prod_insert ha, e, Finset.card_insert_of_notMem ha, pow_succ]
      have g := geom_sum_mul ζ i
      linear_combination ((ζ - 1) ^ S.card * c) * g

theorem pdiv : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (T : Tower p Ω) (j s : ℕ), 1 ≤ j → s ≤ Nat.totient (p ^ j) →
      IsInt (p := p) ((p : Ω) / (T.ζ j - 1) ^ s) := by
  intro p _ Ω _ _ T j s hj hs
  classical
  have hprim := T.prim j
  have hpos : 0 < p ^ j := pow_pos (Fact.out : p.Prime).pos j
  have hζ : IsIntegral (O0 p) (T.ζ j) := ⟨X ^ (p ^ j) - C 1, monic_X_pow_sub_C 1 hpos.ne', by simp [hprim.pow_eq_one]⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hne : T.ζ (j' + 1) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact hprim.ne_one (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt)
  have hp : (p : Ω) = ∏ μ ∈ primitiveRoots (p ^ (j' + 1)) Ω, (1 - μ) := by
    rw [← eval_one_cyclotomic_prime_pow (R := Ω) j', cyclotomic_eq_prod_X_sub_primitiveRoots hprim,
      eval_prod]
    simp
  obtain ⟨c, hc, e⟩ := prod_one_sub_pow_dvd (T.ζ (j' + 1)) hζ (primitiveRoots (p ^ (j' + 1)) Ω)
    (fun μ hμ => by
      have hμ' := (mem_primitiveRoots hpos).1 hμ
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hμ'.pow_eq_one
      exact ⟨i, hi⟩)
  rw [hprim.card_primitiveRoots] at e
  have key : (p : Ω) / (T.ζ (j' + 1) - 1) ^ s =
      (T.ζ (j' + 1) - 1) ^ (Nat.totient (p ^ (j' + 1)) - s) * c := by
    rw [div_eq_iff (pow_ne_zero _ hne), hp, e, mul_right_comm, ← pow_add, Nat.sub_add_cancel hs]
  rw [IsInt, key]
  exact IsIntegral.mul (IsIntegral.pow (IsIntegral.sub hζ isIntegral_one) _) hc

end GlobalTheory.K5.PDiv
