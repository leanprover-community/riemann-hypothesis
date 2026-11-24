module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def hwTerm (μ : Fin n → ℝ) (a b : Fin n) : ℝ :=
  if a = b then μ a * μ a else if a < b then μ a - μ b else 0

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem pair_apply_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (hd : ∀ a, E a a v = (μ a : ℂ) • v) {a b : Fin n}
    (hab : a < b → E a b v = 0) (hba : b < a → E b a v = 0) :
    (E a b * E b a) v = ((hwTerm μ a b : ℝ) : ℂ) • v := by
  rcases lt_trichotomy a b with h | rfl | h
  ·
    have hc := congrArg (fun f : Module.End ℂ M => f v) (hE a b b a)
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, hab h, map_zero,
      sub_zero] at hc
    rw [Module.End.mul_apply, hc, hd, hd]
    simp [hwTerm, h, h.ne, sub_smul]
  · rw [Module.End.mul_apply, hd, map_smul, hd, smul_smul]
    simp [hwTerm]
  · rw [Module.End.mul_apply, hba h, map_zero]
    simp [hwTerm, h.ne', not_lt.2 h.le]

theorem sum_pair_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (S : Fin n → Fin n → Prop) [DecidableRel S] (hS : ∀ a b, S a b → S b a)
    (hd : ∀ a, E a a v = (μ a : ℂ) • v) (hv : ∀ a b, a < b → S a b → E a b v = 0) :
    (∑ a, ∑ b ∈ univ.filter (fun b => S a b), E a b * E b a) v =
      ((∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b : ℝ) : ℂ) • v := by
  simp only [LinearMap.sum_apply, Complex.ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : S a b := (Finset.mem_filter.1 hb).2
  exact pair_apply_hw hE hd (fun h => hv a b h hab) (fun h => hv b a h (hS a b hab))

end Alg

theorem sum_hwTerm (S : Fin n → Fin n → Prop) [DecidableRel S] (hrefl : ∀ a, S a a)
    (hS : ∀ a b, S a b → S b a) (μ r : Fin n → ℝ)
    (hr : ∀ a, 2 * r a = ((univ.filter fun b => a < b ∧ S a b).card : ℝ) -
      ((univ.filter fun b => b < a ∧ S a b).card : ℝ)) :
    ∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b = nsq (μ + r) - nsq r := by
  classical
  have hpt : ∀ a b, (if S a b then hwTerm μ a b else 0) =
      (if a = b then μ a * μ a else 0) +
        ((if a < b ∧ S a b then μ a else 0) - (if a < b ∧ S a b then μ b else 0)) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · by_cases hs : S a b <;> simp [hwTerm, h, h.ne, hs]
    · simp [hwTerm, hrefl]
    · by_cases hs : S a b <;> simp [hwTerm, h.ne', not_lt.2 h.le, hs]

  have hL : ∑ a, ∑ b ∈ univ.filter (fun b => S a b), hwTerm μ a b =
      ∑ a, μ a * μ a + ∑ a, ∑ b, ((if a < b ∧ S a b then μ a else 0) -
        (if a < b ∧ S a b then μ b else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    simp only [hpt a, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  have hR : nsq (μ + r) - nsq r = ∑ a, μ a * μ a + ∑ a, ∑ b, ((if a < b ∧ S a b then μ a else 0) -
        (if b < a ∧ S a b then μ a else 0)) := by
    rw [← Finset.sum_add_distrib]
    unfold nsq dot
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : ∑ b, ((if a < b ∧ S a b then μ a else 0) - (if b < a ∧ S a b then μ a else 0)) =
        μ a * (2 * r a) := by
      rw [hr a, Finset.natCast_card_filter, Finset.natCast_card_filter, mul_sub, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [mul_ite, mul_one, mul_zero]
    rw [h2, Pi.add_apply]
    ring
  rw [hL, hR]
  congr 1
  simp only [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b < a ∧ S a b
  · rw [if_pos h, if_pos ⟨h.1, hS a b h.2⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1, hS b a h'.2⟩]

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem casimir_hwVec {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {μ : Fin n → ℝ}
    {v : M} (hv : IsHWVec E μ v) :
    casimir E v = ((nsq (μ + rho n) - nsq (rho n) : ℝ) : ℂ) • v := by
  classical
  have hc : casimir E = ∑ a, ∑ b ∈ univ.filter (fun _ => True), E a b * E b a := by
    simp [casimir]
  have hsum := sum_pair_hw hE (fun _ _ => True) (fun _ _ h => h) hv.1 (fun a b h _ => hv.2 a b h)
  rw [hc, hsum, sum_hwTerm (fun _ _ => True) (fun _ => trivial) (fun _ _ h => h) μ (rho n)]
  intro a
  have ha : 1 + (a : ℕ) ≤ n := by have := a.isLt; omega
  simp only [and_true, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi,
    Fin.card_Iio, rho]
  rw [Nat.sub_sub, Nat.cast_sub ha]
  push_cast
  ring

theorem casimirK_khwVec (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    {μ : Fin n → ℝ} {v : M} (hv : IsKHWVec ε E μ v) :
    casimirK ε E v = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • v := by
  classical
  have hsum := sum_pair_hw hE (fun a b => ε b = ε a) (fun _ _ h => h.symm) hv.1
    (fun a b h hs => hv.2 a b h hs.symm)
  rw [casimirK, hsum, sum_hwTerm (fun a b => ε b = ε a) (fun _ => rfl) (fun _ _ h => h.symm) μ
    (rhoC ε)]
  intro a
  simp only [rhoC]
  ring

end Alg

end ReciprocityTheory.ChartRestriction.DS
