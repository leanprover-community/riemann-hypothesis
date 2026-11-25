module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicComplete
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLeOneIffIsIntegralOfCompleteDvr
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory.K5.Dense

theorem exists_near_root {Ωl : Type} [Field Ωl] [CharZero Ωl] (v : Valuation Ωl ℝ≥0)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Ωl) (e : Ωl) (t : ℝ≥0) (Q : ℤ[X])
    (h : v (Q.eval₂ (Int.castRingHom Ωl) e) < v (Q.leadingCoeff : Ωl) * t ^ Q.natDegree) :
    ∃ a : Ω, v (e - j a) < t := by
  have : CharZero Ω := j.charZero
  by_contra hcon
  push Not at hcon
  set R : Polynomial Ω := Q.map (Int.castRingHom Ω) with hR
  have hinj : Function.Injective (Int.castRingHom Ω) := Int.cast_injective
  have hdeg : R.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj Q
  have hlc : R.leadingCoeff = (Q.leadingCoeff : Ω) := leadingCoeff_map_of_injective hinj Q
  have hcard : Multiset.card R.roots = R.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have h1 : Q.eval₂ (Int.castRingHom Ωl) e = R.eval₂ j e := by
    rw [hR, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have h2 : R.eval₂ j e = (Q.leadingCoeff : Ωl) * (R.roots.map fun a => e - j a).prod := by
    conv_lhs => rw [← hprod]
    rw [eval₂_mul, eval₂_C, eval₂_multiset_prod, Multiset.map_map, hlc, map_intCast]
    simp
  rw [h1, h2, map_mul, map_multiset_prod, Multiset.map_map] at h
  have h3 : t ^ Q.natDegree ≤ (R.roots.map (v ∘ fun a => e - j a)).prod := by
    have := Multiset.pow_card_le_prod (s := R.roots.map (v ∘ fun a => e - j a)) (a := t) (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
      exact hcon a)
    rwa [Multiset.card_map, hcard, hdeg] at this
  exact absurd h (not_lt.2 (by gcongr))

theorem exists_approx {p : ℕ} [Fact p.Prime] (P : ℤ_[p][X]) (N : ℕ) :
    ∃ (Q : ℤ[X]) (R : ℤ_[p][X]), Q.natDegree ≤ P.natDegree ∧
      P = Q.map (Int.castRingHom ℤ_[p]) + C ((p : ℤ_[p]) ^ N) * R := by
  have h : ∀ x : ℤ_[p], ∃ (m : ℤ) (r : ℤ_[p]), x = m + (p : ℤ_[p]) ^ N * r := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec N x)
    exact ⟨PadicInt.appr x N, r, by push_cast; linear_combination hr⟩
  choose m r hmr using h
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), monomial i (m (P.coeff i)),
    ∑ i ∈ Finset.range (P.natDegree + 1), monomial i (r (P.coeff i)), ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

  · rw [Polynomial.map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [P.as_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_monomial, C_mul_monomial, ← map_add (f := _), eq_intCast, ← hmr]

end GlobalTheory.K5.Dense
