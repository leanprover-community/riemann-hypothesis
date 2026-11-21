import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceSumOrderEqFinrank
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow

section
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

open Polynomial

variable {k L : Type} [Field k] [Field L] [Algebra k L]

theorem place_aeval_le_one (x : L) (u : Place k L) (hx : u.1 x ≤ 1) (p : k[X]) :
    u.1 (aeval x p) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  refine mul_le_one' ?_ (pow_le_one' hx _)
  by_cases hc : p.coeff i = 0
  · simp [hc]
  · rw [u.2.2 _ hc]

theorem place_aeval_eq_one (x : L) (u : Place k L) (hx : u.1 x < 1) (q : k[X]) (hq : q.coeff 0 ≠ 0) :
    u.1 (aeval x q) = 1 := by
  have h1 : u.1 (algebraMap k L (q.coeff 0)) = 1 := u.2.2 _ hq
  have h2 : u.1 (x * aeval x q.divX) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hx (place_aeval_le_one x u hx.le _)
  conv_lhs => rw [← X_mul_divX_add q]
  rw [map_add, map_mul, aeval_X, aeval_C, Valuation.map_add_eq_of_lt_right u.1 (by rw [h1]; exact h2), h1]

theorem place_aeval_eq_pow (x : L) (u : Place k L) (hx : u.1 x < 1) (p : k[X]) (hp : p ≠ 0) :
    u.1 (aeval x p) = u.1 x ^ p.rootMultiplicity 0 := by
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h; apply hq; simpa [X_dvd_iff] using h
  conv_lhs => rw [hpq]
  simp [map_mul, map_pow, place_aeval_eq_one x u hx q hq0]

end GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial

theorem exists_unique_place_ord_eq_one (k L : Type) [Field k] [Field L] [Algebra k L] (x : L)
    (hx : Transcendental k x) (htop : k⟮x⟯ = ⊤) :
    ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  have hmem : ∀ y : L, ∃ r s : k[X], y = aeval x r / aeval x s := fun y =>
    (IntermediateField.mem_adjoin_simple_iff (F := k) (α := x) y).1 (by rw [htop]; trivial)
  have hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0 := fun p hp h => hx ⟨p, hp, h⟩
  have hval : ∀ u : Place k L, u.1 x < 1 → u.1 x = WithZero.exp (-1 : ℤ) := by
    intro u hu
    have hx0 : u.1 x ≠ 0 := by
      rw [Valuation.ne_zero_iff]; intro h; apply hne X X_ne_zero; simpa using h
    set b := WithZero.log (u.1 x) with hb
    have hub : u.1 x = WithZero.exp b := (WithZero.exp_log hx0).symm
    have hb0 : b < 0 := by
      have : WithZero.exp b < WithZero.exp (0 : ℤ) := by rw [← hub, WithZero.exp_zero]; exact hu
      exact WithZero.exp_lt_exp.1 this
    obtain ⟨y, hy⟩ := u.2.1 (WithZero.exp (-1 : ℤ))
    obtain ⟨r, s, rfl⟩ := hmem y
    have hr : r ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    have hs : s ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    rw [map_div₀, place_aeval_eq_pow x u hu r hr, place_aeval_eq_pow x u hu s hs, hub,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub, WithZero.exp_inj] at hy
    have hmul : b * ((r.rootMultiplicity 0 : ℤ) - s.rootMultiplicity 0) = -1 := by
      rw [← hy]; simp only [nsmul_eq_mul]; ring
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hmul with h | h
    · omega
    · rw [hub, h]
  have hpol : ∀ u : Place k L, u.1 x < 1 → ∀ p : k[X], p ≠ 0 →
      u.1 (aeval x p) = WithZero.exp (-1 : ℤ) ^ p.rootMultiplicity 0 := fun u hu p hp => by
    rw [place_aeval_eq_pow x u hu p hp, hval u hu]
  let e : RatFunc k ≃ₐ[k] L := ((RatFunc.algEquivOfTranscendental x hx).trans
    (IntermediateField.equivOfEq htop)).trans IntermediateField.topEquiv
  have heX : e RatFunc.X = x := by simp [e]
  have heXs : e.symm x = RatFunc.X := by rw [← heX, AlgEquiv.symm_apply_apply]
  let V := (Polynomial.idealX k).valuation (RatFunc k)
  let v0 : Valuation L (WithZero (Multiplicative ℤ)) := V.comap (e.symm : L →+* RatFunc k)
  have hv0 : ∀ y, v0 y = V (e.symm y) := fun y => rfl
  have hVX : V RatFunc.X = WithZero.exp (-1 : ℤ) := by
    rw [← RatFunc.algebraMap_X, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ X_ne_zero (Polynomial.idealX_span k)
  let v : Place k L := ⟨v0, fun γ => by
      obtain ⟨r, hr⟩ := RatFunc.valuation_surjective (K := k) γ
      exact ⟨e r, by rw [hv0, AlgEquiv.symm_apply_apply]; exact hr⟩,
    fun c hc => by
      rw [hv0, AlgEquiv.commutes, IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      intro hmem'
      rw [Polynomial.idealX_span, Ideal.mem_span_singleton, X_dvd_iff] at hmem'
      simp [hc] at hmem'⟩
  have hvx : v.1 x = WithZero.exp (-1 : ℤ) := by
    show v0 x = _; rw [hv0, heXs, hVX]
  refine ⟨v, by simp [ord, hvx], fun w hw => ?_⟩
  have hvl : v.1 x < 1 := by rw [hvx]; exact WithZero.exp_lt_exp.2 (by norm_num) |>.trans_eq WithZero.exp_zero
  apply Subtype.ext
  ext y
  obtain ⟨r, s, rfl⟩ := hmem y
  rw [map_div₀, map_div₀]
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  rw [hpol w hw r hr, hpol w hw s hs, hpol v hvl r hr, hpol v hvl s hs]

end GlobalTheory.Nef
end
end

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (x : L), Transcendental k x → k⟮x⟯ = ⊤ → ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  atlas_forward_decl GlobalTheory.Nef.exists_unique_place_ord_eq_one
end

section
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem adjoin_gen_eq_top {k F : Type} [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯ = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  have hm : (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) = k⟮x⟯ := by
    rw [IntermediateField.adjoin_map]; simp
  have hy : (y : F) ∈ (k⟮(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯)⟯).map (k⟮x⟯.val) := by
    rw [hm]; exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

theorem val_lt_one_of_ord_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (t : F)
    (h : ord v t = 1) : v.1 t < 1 := by
  unfold ord at h
  by_cases h0 : v.1 t = 0
  · rw [h0] at h; simp at h
  · have hl : WithZero.log (v.1 t) < WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      simp; omega
    exact (WithZero.log_lt_log h0 one_ne_zero).1 hl

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem zeros_finite_sum_eq_degree : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, Transcendental k x → {v : Place k F | v.1 x < 1}.Finite ∧
      ∑ᶠ v ∈ {v : Place k F | v.1 x < 1}, ord v x = Module.finrank k⟮x⟯ F := by
  intro k F _ _ _ _ _ hF x hx
  haveI : FiniteDimensional k⟮x⟯ F := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).1 x hx
  set t : k⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ with ht
  have htx : algebraMap k⟮x⟯ F t = x := rfl
  have htr : Transcendental k t := by
    intro ha
    exact hx ((IntermediateField.isAlgebraic_iff).1 ha)
  have htop : k⟮t⟯ = ⊤ := adjoin_gen_eq_top x
  have hL : IsFF k k⟮x⟯ := by
    refine ⟨t, htr, ?_⟩
    rw [htop]
    exact Module.finite_of_finrank_eq_succ (IntermediateField.finrank_top)
  obtain ⟨v0, hv0, huniq⟩ := GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator k k⟮x⟯ t htr htop
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).1
  have ht0 : t ≠ 0 := by
    intro h; apply hx; rw [← htx, h, map_zero]; exact isAlgebraic_zero
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.functionFieldPlace_sum_order_eq_finrank k k⟮x⟯ F hL ρ hρ v0 t ht0 hv0
  have hset : {v : Place k F | v.1 x < 1} = {p | ρ p = v0} := by
    ext p
    obtain ⟨e, he, hpow, -⟩ := (GlobalTheory.T.functionFieldPlace_restriction_exists_pow k k⟮x⟯ F).2 ρ hρ p
    simp only [Set.mem_setOf_eq]
    change p.1 (algebraMap k⟮x⟯ F t) < 1 ↔ ρ p = v0
    rw [hpow t]
    constructor
    · intro h
      apply huniq
      by_contra hn
      exact absurd h (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))
    · intro h
      rw [h]
      exact pow_lt_one₀ zero_le' (val_lt_one_of_ord_eq_one v0 t hv0) he.ne'
  rw [hset]
  exact ⟨hfin, by simpa [htx] using hsum⟩

end GlobalTheory.Nef
end

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ x : F, Transcendental k x → {v : Place k F | v.1 x < 1}.Finite ∧ ∑ᶠ v ∈ {v : Place k F | v.1 x < 1}, ord v x = Module.finrank k⟮x⟯ F := by
  atlas_forward_decl GlobalTheory.Nef.zeros_finite_sum_eq_degree
end

section
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem functionFieldPlaceOrder_inv {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (x : F) (hx : x ≠ 0) :
    ord v x⁻¹ = - ord v x := by
  have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ord
  rw [map_inv₀, WithZero.log_inv, neg_neg]

theorem adjoin_simple_inv_eq (k F : Type) [Field k] [Field F] [Algebra k F] (x : F) :
    k⟮x⁻¹⟯ = k⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k x⁻¹)
    rwa [inv_inv] at this

theorem finite_support_and_sum_ord_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
    ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  intro k F _ _ _ _ _ hF x hx
  by_cases htr : Transcendental k x
  · have htr' : Transcendental k x⁻¹ := by
      intro h
      apply htr
      have := h.inv
      rwa [inv_inv] at this
    obtain ⟨hA, hsA⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x htr
    obtain ⟨hB, hsB⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hF x⁻¹ htr'
    rw [adjoin_simple_inv_eq] at hsB
    set A := {v : Place k F | v.1 x < 1}
    set B := {v : Place k F | v.1 x⁻¹ < 1}
    have hsub : {v : Place k F | v.1 x ≠ 1} ⊆ A ∪ B := by
      intro v hv
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_or_gt_of_ne hv with h | h
      · exact Or.inl h
      · right
        show v.1 x⁻¹ < 1
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ h
    refine ⟨(hA.union hB).subset hsub, ?_⟩
    have hpt : ∀ v : Place k F, ord v x = A.indicator (fun w => ord w x) v - B.indicator (fun w => ord w x⁻¹) v := by
      intro v
      have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
      rcases lt_trichotomy (v.1 x) 1 with h | h | h
      · have hB' : v ∉ B := by
          show ¬ v.1 x⁻¹ < 1
          rw [map_inv₀, not_lt]
          exact (one_le_inv₀ (zero_lt_iff.2 h0)).2 h.le
        rw [Set.indicator_of_mem (show v ∈ A from h), Set.indicator_of_notMem hB', sub_zero]
      · have e : ord v x = 0 := by unfold ord; rw [h, WithZero.log_one, neg_zero]
        rw [e, Set.indicator_of_notMem (show v ∉ A from fun h' => by change v.1 x < 1 at h'; rw [h] at h'; exact lt_irrefl _ h'),
          Set.indicator_of_notMem (show v ∉ B from by
            show ¬ v.1 x⁻¹ < 1
            rw [map_inv₀, h, inv_one]; exact lt_irrefl _)]
        simp
      · have hA' : v ∉ A := fun h' => lt_asymm h h'
        have hB' : v ∈ B := by
          show v.1 x⁻¹ < 1
          rw [map_inv₀]
          exact inv_lt_one_of_one_lt₀ h
        rw [Set.indicator_of_notMem hA', Set.indicator_of_mem hB', functionFieldPlaceOrder_inv v x hx, zero_sub, neg_neg]
    have hfA : (Function.support (A.indicator fun w => ord w x)).Finite :=
      hA.subset (Set.support_indicator_subset)
    have hfB : (Function.support (B.indicator fun w => ord w x⁻¹)).Finite :=
      hB.subset (Set.support_indicator_subset)
    rw [finsum_congr hpt, finsum_sub_distrib hfA hfB, ← finsum_mem_def, ← finsum_mem_def, hsA, hsB, sub_self]
  · have halg : IsAlgebraic k x := by
      by_contra h
      exact htr h
    have hint : IsIntegral k x := halg.isIntegral
    have hdeg : (minpoly k x).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, rfl⟩ := minpoly.mem_range_of_degree_eq_one k x hdeg
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx (map_zero _)
    have hv : ∀ v : Place k F, v.1 (algebraMap k F c) = 1 := fun v => v.2.2 c hc
    refine ⟨by simp [hv], ?_⟩
    have : ∀ v : Place k F, ord v (algebraMap k F c) = 0 := by
      intro v; unfold ord; rw [hv v, WithZero.log_one, neg_zero]
    simp [this]

end GlobalTheory.Nef
end

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionField_finite_support_sum_order_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  atlas_forward_decl GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero
end
