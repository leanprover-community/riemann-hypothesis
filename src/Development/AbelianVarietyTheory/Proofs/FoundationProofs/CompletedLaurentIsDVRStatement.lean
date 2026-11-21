import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

section
open GlobalTheory.K5

namespace GlobalTheory.K5

noncomputable def lauRed (p : ℕ) [Fact p.Prime] : Lau p →+* LaurentSeries (ZMod p) where
  toFun x := HahnSeries.map x (PadicInt.toZMod (p := p))
  map_one' := HahnSeries.map_one (PadicInt.toZMod (p := p)).toMonoidWithZeroHom
  map_mul' x y := HahnSeries.map_mul (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem lauRed_coeff (p : ℕ) [Fact p.Prime] (x : Lau p) (n : ℤ) :
    (lauRed p x).coeff n = PadicInt.toZMod (x.coeff n) := rfl

theorem lauRed_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (lauRed p) := by
  intro y
  refine ⟨HahnSeries.map y (⟨fun a => ((ZMod.val a : ℕ) : ℤ_[p]), by simp⟩ : ZeroHom (ZMod p) ℤ_[p]), ?_⟩
  ext n
  rw [lauRed_coeff]
  show PadicInt.toZMod ((ZMod.val (y.coeff n) : ℕ) : ℤ_[p]) = _
  simp

theorem ker_lauRed (p : ℕ) [Fact p.Prime] : RingHom.ker (lauRed p) = pI p := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h : ∀ n, ∃ c : ℤ_[p], x.coeff n = (p : ℤ_[p]) * c := by
      intro n
      have h1 : x.coeff n ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
        rw [RingHom.mem_ker, ← lauRed_coeff, hx]; rfl
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
      exact h1
    choose c hc using h
    have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    refine Ideal.mem_span_singleton.2 ⟨⟨c, x.isPWO_support.mono ?_⟩, ?_⟩
    · intro n hn
      rw [HahnSeries.mem_support, hc n]
      exact mul_ne_zero hp hn
    · ext n
      rw [← nsmul_eq_mul, HahnSeries.coeff_nsmul, hc n]
      simp
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show lauRed p _ = 0
    rw [map_natCast]
    ext n
    rw [← Nat.smul_one_eq_cast, HahnSeries.coeff_nsmul]
    simp

theorem exists_completedLaurent_quot_prime_equiv_laurentFp (p : ℕ) [Fact p.Prime] : ∃ e : (O0 p ⧸ Ideal.span {(p : O0 p)}) ≃+* LaurentSeries (ZMod p),
    e (Ideal.Quotient.mk _ (qO p)) = HahnSeries.single (1 : ℤ) (1 : ZMod p) := by
  have fg : (pI p).FG := Submodule.fg_span_singleton _
  have hker := AdicCompletion.ker_evalOneₐ_eq_map (pI p) fg
  have hsurj : Function.Surjective (AdicCompletion.evalOneₐ (pI p)) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap _ _ a, (AdicCompletion.evalOneₐ (pI p)).commutes a⟩
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h1 : Ideal.span {(p : O0 p)} = RingHom.ker (AdicCompletion.evalOneₐ (pI p)).toRingHom := by
    rw [← hmap]; exact hker.symm
  refine ⟨(Ideal.quotEquivOfEq h1).trans
    ((RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (pI p)).toRingHom) hsurj).trans
      ((Ideal.quotEquivOfEq (ker_lauRed p).symm).trans
        (RingHom.quotientKerEquivOfSurjective (lauRed_surjective p)))), ?_⟩
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hq : (AdicCompletion.evalOneₐ (pI p)).toRingHom (qO p) =
      Ideal.Quotient.mk (pI p) (HahnSeries.single (1 : ℤ) (1 : ℤ_[p])) :=
    (AdicCompletion.evalOneₐ (pI p)).commutes _
  rw [hq, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  ext n
  rw [lauRed_coeff]
  by_cases hn : n = 1
  · subst hn; simp
  · simp [HahnSeries.coeff_single_of_ne hn]

end GlobalTheory.K5
end

section
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem dvr_of_separated {S : Type*} [CommRing S] (π : S) (hn : ∀ n : ℕ, π ^ n ≠ 0)
    (hnu : ¬ IsUnit π) (hu : ∀ x, ¬ π ∣ x → IsUnit x) (hsep : ∀ x, (∀ n : ℕ, π ^ n ∣ x) → x = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  classical
  have hfac : ∀ x : S, x ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra h
      push Not at h
      exact hx (hsep x fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (h n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · have := Nat.find_min hex (m := m) (by omega)
        simpa using this
    obtain ⟨u, hxu⟩ := h1
    refine ⟨Nat.find hex, u, hu u ?_, hxu⟩
    rintro ⟨v, hv⟩
    exact Nat.find_spec hex ⟨v, by rw [pow_succ, mul_assoc, ← hv]; exact hxu⟩
  have : Nontrivial S := ⟨⟨π ^ 0, 0, hn 0⟩⟩
  have : NoZeroDivisors S := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨a, u, hu', rfl⟩ := hfac x h.1
    obtain ⟨b, v, hv', rfl⟩ := hfac y h.2
    apply hn (a + b)
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy]; ring
    exact ((hu'.mul hv').mul_left_eq_zero).1 this⟩
  have hd : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := by simpa using hn 1
  have hprime : Prime π := by
    refine ⟨hπ0, hnu, fun a b hab => ?_⟩
    by_contra h
    push Not at h
    exact hnu (isUnit_of_dvd_unit hab ((hu a h.1).mul (hu b h.2)))
  refine ⟨hd, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, hprime.irreducible, fun {x} hx => ?_⟩, hprime.irreducible⟩
  obtain ⟨n, u, hu', rfl⟩ := hfac x hx
  exact ⟨n, hu'.unit, rfl⟩

theorem adicCompletion_dvr {R : Type*} [CommRing R] [IsDomain R] (a : R) (ha : a ≠ 0)
    (hmax : (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a}).IsMaximal) :
    ∃ _ : IsDomain (AdicCompletion (Ideal.span {a}) R),
      IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R) ∧
        Irreducible (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := by
  have fg : (Ideal.span {a}).FG := Submodule.fg_span_singleton _
  have hc := AdicCompletion.isAdicComplete_self (Ideal.span {a}) fg
  rw [Ideal.map_span, Set.image_singleton] at hc
  have hnu : ¬ IsUnit (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := fun h =>
    hmax.ne_top (Ideal.span_singleton_eq_top.2 h)
  have := isLocalRing_of_isAdicComplete_maximal
    (Ideal.span {algebraMap R (AdicCompletion (Ideal.span {a}) R) a})
  refine dvr_of_separated _ (fun n hn => ?_) hnu (fun x hx => ?_) (fun x hx => ?_)
  · rw [← map_pow] at hn
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (n + 1)) hn
    rw [AlgHom.commutes, map_zero, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ] at h2
    have h3 : a ^ n * a ∣ a ^ n * 1 := by simpa using h2
    exact hnu ((isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n ha)).1 h3)).map _)
  · by_contra hxu
    have : x ∈ IsLocalRing.maximalIdeal _ := hxu
    rw [← IsLocalRing.eq_maximalIdeal hmax, Ideal.mem_span_singleton] at this
    exact hx this
  · refine hc.toIsHausdorff.haus' x fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hx n

theorem completed_laurent_isDVR (p : ℕ) [Fact p.Prime] :
    ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  have hp : (p : Lau p) ≠ 0 := by
    have h : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rw [← map_natCast (HahnSeries.C : ℤ_[p] →+* Lau p)]
    exact HahnSeries.C_ne_zero h
  obtain ⟨e⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))
  have := adicCompletion_dvr (p : Lau p) hp (by rw [map_natCast]; exact hmax)
  rw [map_natCast] at this
  exact this

end GlobalTheory.K5
end
