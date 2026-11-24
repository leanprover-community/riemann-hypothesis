module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanSumNonzeroUnfold
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.DedekindZeta
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
public import Mathlib.NumberTheory.LSeries.SumCoeff

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.Mem

theorem tsum_eq_exp_tsum_neg_log_of_primes {α ι : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    (p : ι → α) (hp : ∀ i, Prime (p i)) (hdvd : ∀ i j, p i ∣ p j → i = j)
    (f : α → ℂ) (hmul : ∀ a b, f (a * b) = f a * f b) (h1 : f 1 = 1)
    (hex : ∀ a, a ≠ 1 → f a ≠ 0 → ∃ i, p i ∣ a) (hsum : Summable fun a => ‖f a‖)
    (hne : ∀ i, 1 - f (p i) ≠ 0) :
    ∑' a, f a = exp (∑' i, -log (1 - f (p i))) := by
  classical
  set g : Finset ι → α → ℂ := fun S a => if ∀ i ∈ S, ¬ p i ∣ a then f a else 0 with hg
  have hgle : ∀ S a, ‖g S a‖ ≤ ‖f a‖ := by
    intro S a
    simp only [hg]
    split_ifs <;> simp
  have hgs : ∀ S, Summable (g S) := fun S => Summable.of_norm_bounded hsum (hgle S)
  have key : ∀ S : Finset ι, (∏ i ∈ S, (1 - f (p i))) * ∑' a, f a = ∑' a, g S a := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [hg]
    | insert i S hi ih =>
      rw [Finset.prod_insert hi, mul_assoc, ih]
      have hinj : Function.Injective fun b : α => p i * b := mul_right_injective₀ (hp i).ne_zero
      have e1 : ∀ a, g (insert i S) a = g S a - (if p i ∣ a then g S a else 0) := by
        intro a
        simp only [hg, Finset.forall_mem_insert]
        by_cases h : p i ∣ a <;> simp [h]
      have hs2 : Summable fun a => if p i ∣ a then g S a else 0 :=
        Summable.of_norm_bounded hsum (fun a => by
          split_ifs
          · exact hgle S a
          · simp)
      have e2 : ∑' a, (if p i ∣ a then g S a else 0) = f (p i) * ∑' a, g S a := by
        rw [← hinj.tsum_eq, ← tsum_mul_left]
        · refine tsum_congr fun b => ?_
          rw [if_pos (dvd_mul_right _ _)]
          have : (∀ j ∈ S, ¬ p j ∣ p i * b) ↔ ∀ j ∈ S, ¬ p j ∣ b := by
            refine forall₂_congr fun j hj => not_congr ?_
            rw [(hp j).dvd_mul]
            refine or_iff_right fun h => hi ?_
            rwa [← hdvd _ _ h]
          simp only [hg, this, hmul]
          split_ifs <;> simp
        · intro a ha
          by_cases h : p i ∣ a
          · obtain ⟨b, rfl⟩ := h
            exact ⟨b, rfl⟩
          · simp [h] at ha
      simp only [e1]
      rw [(hgs S).tsum_sub hs2, e2]
      ring
  have lim1 : Tendsto (fun S : Finset ι => ∑' a, g S a) atTop
      (𝓝 (∑' a : α, if a = 1 then (1 : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun a => ?_)
      (Eventually.of_forall fun S a => hgle S a)
    by_cases ha : a = 1
    · subst ha
      have : ∀ S, g S 1 = 1 := fun S => by
        simp only [hg]
        rw [if_pos fun i _ => (hp i).not_dvd_one, h1]
      simp [this]
    · rw [if_neg ha]
      by_cases hf : f a = 0
      · simp [hg, hf]
      · obtain ⟨i, hi⟩ := hex a ha hf
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with S hS
        simp only [hg]
        rw [if_neg]
        intro h
        exact h i (hS (Finset.mem_singleton_self i)) hi
  rw [tsum_ite_eq] at lim1
  have pinj : Function.Injective p := fun i j h => hdvd i j (h ▸ dvd_rfl)
  have hl : Summable fun i => log (1 - f (p i)) :=
    Summable.clog_one_sub (hsum.of_norm.comp_injective pinj)
  have lim2 : Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - f (p i))) atTop
      (𝓝 (exp (∑' i, log (1 - f (p i))))) := Complex.hasProd_of_hasSum_log hne hl.hasSum
  have lim3 := lim2.mul_const (∑' a, f a)
  simp only [key] at lim3
  have := tendsto_nhds_unique lim3 lim1
  rw [tsum_neg, exp_neg]
  exact eq_inv_of_mul_eq_one_right this

theorem lseriesSummable_card_absNorm (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  apply GlobalTheory.FlagBase.SiegelUnfold.lseriesSummable_idealCount <;> assumption

instance finite_absNorm_fiber (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

theorem summable_norm_absNorm_cpow (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ => by exact norm_nonneg _)]
  refine ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card_absNorm K hs).norm.congr fun n => ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖) ∘
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ = ‖(n : ℂ) ^ (-s)‖ := by
    rintro ⟨I, rfl⟩; rfl
  rw [tsum_congr this, tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hs0]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg, norm_mul]
    simp

end GlobalTheory.Mem
