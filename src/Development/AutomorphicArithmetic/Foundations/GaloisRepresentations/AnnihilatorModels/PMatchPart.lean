module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.matchPart_of :
    SameNormBasic → Matching → PermOfMap → MatchPart := by
  intro hSN hMatch hPerm B _ ϖ hϖ ι _ I I' _ _ N hI hI' u u' hsame e he hdiv hcmp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : B →+* B ⧸ Ideal.span {1 - e}, ρ = Ideal.Quotient.mk _ := ⟨_, rfl⟩
  have hsurj : Function.Surjective ρ := by
    subst hρ
    exact Ideal.Quotient.mk_surjective
  have hker : ∀ a b : B, ρ a = ρ b ↔ a - b ∈ Ideal.span {1 - e} := by
    subst hρ
    exact fun a b => Ideal.Quotient.eq
  have he' : e * e = e := he
  have hρe : ρ e = 1 := by
    rw [← map_one ρ]
    exact (hker e 1).mpr (Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩)
  have L1 : ∀ a b : B, ρ a = ρ b → e * a = e * b := by
    intro a b hab
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hker a b).mp hab)
    linear_combination (-e) * hc + (-c) * he'
  have L2 : ∀ a b : B, ρ a ∣ ρ b → a ∣ e * b := by
    rintro a b ⟨c', hc'⟩
    obtain ⟨c, rfl⟩ := hsurj c'
    rw [← map_mul] at hc'
    have := L1 _ _ hc'
    exact ⟨e * c, by rw [this]; ring⟩
  have L3 : ∀ a b : B, a ∣ e * b → ρ a ∣ ρ b := by
    intro a b h
    have := map_dvd ρ h
    rwa [map_mul, hρe, one_mul] at this
  by_cases hu : IsUnit (ρ ϖ)
  · obtain ⟨σ⟩ : Nonempty (I ≃ I') := ⟨Fintype.equivOfCardEq (hI.trans hI'.symm)⟩
    refine ⟨σ, fun i k => L2 _ _ hu.dvd⟩
  have hnzd : ρ ϖ ∈ nonZeroDivisors (B ⧸ Ideal.span {1 - e}) := by
    have hr : ∀ z' : B ⧸ Ideal.span {1 - e}, z' * ρ ϖ = 0 → z' = 0 := by
      intro z' hz'
      obtain ⟨z, rfl⟩ := hsurj z'
      rw [← map_mul, ← map_zero ρ] at hz'
      have h1 := L1 _ _ hz'
      have h2 : e * z * ϖ = 0 := by
        rw [mul_zero] at h1
        rw [mul_assoc]
        exact h1
      have h3 : e * z = 0 := (mem_nonZeroDivisors_iff.mp hϖ).2 _ h2
      rw [← one_mul (ρ z), ← hρe, ← map_mul, h3, map_zero]
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun z hz => hr z (by rw [mul_comm]; exact hz), hr⟩
  have hle : Ideal.span {ϖ ^ (N + 1) ^ N} ≤ (Ideal.span {ρ ϖ ^ (N + 1) ^ N}).comap ρ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  have hsame' : SameNorm
      (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val))
      (redMod (ρ ϖ ^ (N + 1) ^ N) (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val)) := by
    have := (hSN (B ⧸ Ideal.span {ϖ ^ (N + 1) ^ N}) ι).1 _ (Ideal.quotientMap _ ρ hle) _ _ hsame
    convert this using 1 <;>
      simp [redMod, Multiset.map_map, Function.comp_def, Ideal.quotientMap_mk]
  have hM := hMatch (B ⧸ Ideal.span {1 - e}) (ρ ϖ) hnzd hu ι N
    (Multiset.map (fun i k => ρ (u i k)) Finset.univ.val)
    (Multiset.map (fun i k => ρ (u' i k)) Finset.univ.val) (by simp [hI]) (by simp [hI']) hsame' ?_ ?_
  · simp only [redMod, Multiset.map_map] at hM
    obtain ⟨σ, hσ⟩ := hPerm I I' _ _ _ hM
    refine ⟨σ, fun i k => ?_⟩
    have := congrFun (hσ i) k
    simp only [Function.comp_apply] at this
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub] at this
    exact L2 _ _ this
  · intro x hx y hy k k' hxy
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨i', rfl⟩ := hy
    rw [← map_sub, ← map_pow] at hxy
    rw [← map_sub, ← map_sub]
    rcases hcmp i i' k k' (L2 _ _ hxy) with h | h
    · exact Or.inl (L3 _ _ h)
    · exact Or.inr (L3 _ _ h)
  · intro x hx y hy k j hj
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨i', rfl⟩ := hy
    have hm : (N + 1) ^ j ≤ (N + 1) ^ N := Nat.pow_le_pow_right (Nat.succ_pos N) hj
    rw [← map_sub, ← map_pow]
    rcases hdiv i i' k _ hm with h | h
    · exact Or.inl (L3 _ _ h)
    · exact Or.inr (L3 _ _ h)
