module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

@[expose] public section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.int_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v → ∀ y : K, IsIntegral O y → y ≠ 0 → 0 ≤ v y := by
  intro O _ _ _ _ _ K _ _ _ _ v hv y hy hy0
  have v1 : v 1 = 0 := by
    have h := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [one_mul] at h
    linarith
  have vneg : ∀ z : K, z ≠ 0 → v (-z) = v z := by
    intro z hz
    have h1 := hv.mul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_one_mul, neg_neg, v1] at h1
    have h2 := hv.mul (-1) z (neg_ne_zero.mpr one_ne_zero) hz
    rw [neg_one_mul] at h2
    linarith
  have vpow : ∀ k : ℕ, v (y ^ k) = k * v y := by
    intro k
    induction k with
    | zero => simp [v1]
    | succ k ih =>
      rw [pow_succ, hv.mul _ _ (pow_ne_zero _ hy0) hy0, ih]
      push_cast
      ring
  have vsum : ∀ (s : Finset ℕ) (f : ℕ → K) (c : ℝ), (∀ i ∈ s, f i ≠ 0 → c ≤ v (f i)) →
      (∑ i ∈ s, f i) ≠ 0 → c ≤ v (∑ i ∈ s, f i) := by
    intro s f c
    induction s using Finset.induction_on with
    | empty => intro _ h; simp at h
    | insert a s ha ih =>
      intro hf hs
      rw [Finset.sum_insert ha] at hs ⊢
      by_cases hfa : f a = 0
      · rw [hfa, zero_add] at hs ⊢
        exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hs
      by_cases hS : (∑ i ∈ s, f i) = 0
      · rw [hS, add_zero]
        exact hf a (Finset.mem_insert_self a s) hfa
      have h1 := hv.add _ _ hfa hS hs
      have h2 := hf a (Finset.mem_insert_self a s) hfa
      have h3 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hS
      exact le_trans (le_min h2 h3) h1
  by_contra hneg
  push_neg at hneg
  obtain ⟨p, hpm, hp⟩ := hy
  have hsum := hp
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hS : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) = -(y ^ p.natDegree) :=
    eq_neg_of_add_eq_zero_left hsum
  have hyn : y ^ p.natDegree ≠ 0 := pow_ne_zero _ hy0
  have hS0 : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) ≠ 0 := by
    rw [hS]
    exact neg_ne_zero.mpr hyn
  have hnpos : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exfalso
      rw [h, Finset.sum_range_zero, pow_zero] at hS
      exact one_ne_zero (neg_eq_zero.mp hS.symm)
    · exact h
  have hterm : ∀ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i ≠ 0 →
      ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ v (algebraMap O K (p.coeff i) * y ^ i) := by
    intro i hi hne
    have hc : p.coeff i ≠ 0 := by
      intro h
      apply hne
      simp [h]
    have hmc : algebraMap O K (p.coeff i) ≠ 0 := by
      intro h
      apply hc
      exact (FaithfulSMul.algebraMap_injective O K) (by rw [h, map_zero])
    rw [hv.mul _ _ hmc (pow_ne_zero _ hy0), hv.base _ hc, vpow]
    have hi' : i ≤ p.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hle : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ (i : ℝ) * v y := by
      apply mul_le_mul_of_nonpos_right _ hneg.le
      exact_mod_cast hi'
    have h0 : (0 : ℝ) ≤ ((IsDiscreteValuationRing.addVal O (p.coeff i)).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤
      v (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) :=
    vsum (Finset.range p.natDegree) (fun i => algebraMap O K (p.coeff i) * y ^ i) _ hterm hS0
  rw [hS, vneg _ hyn, vpow, Nat.cast_pred hnpos] at hbound
  linarith
