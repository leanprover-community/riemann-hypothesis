import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.NuLe
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostApprox
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuSumApprox
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycGrp

section
open NumberField Formalism.HC KStar.Tree

private theorem nuQD_unit (N M l : ℕ) [Fact l.Prime] (hN : N = M * l) (hM : M ≠ 0) (hc : M.Coprime l)
    (u : ℤ_[l]ˣ) :
    ∃ v : (ZMod N)ˣ, (v : ZMod N).val ≡ 1 [MOD M] ∧
      (l : ℤ_[l]) ^ N.factorization l ∣
        ((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) - ((((v ^ 2 : (ZMod N)ˣ) : ZMod N).val : ℕ) : ℤ_[l]) := by
  subst hN
  have hl : l.Prime := Fact.out
  haveI : NeZero M := ⟨hM⟩
  haveI : NeZero (M * l) := ⟨mul_ne_zero hM hl.ne_zero⟩
  let e := ZMod.chineseRemainder hc
  let w : (ZMod M × ZMod l)ˣ := MulEquiv.prodUnits.symm (1, Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom u)
  let v : (ZMod (M * l))ˣ := Units.map e.symm.toRingHom.toMonoidHom w
  have he : e (v : ZMod (M * l)) = (w : ZMod M × ZMod l) := by
    simp [v]
  have hw : (w : ZMod M × ZMod l) = (1, PadicInt.toZMod (u : ℤ_[l])) := rfl
  have h1 : ZMod.cast (v : ZMod (M * l)) = (1 : ZMod M) := by
    have := congrArg Prod.fst he
    rw [hw] at this
    simpa [e, ZMod.chineseRemainder] using this
  have h2 : ZMod.cast (v : ZMod (M * l)) = PadicInt.toZMod (u : ℤ_[l]) := by
    have := congrArg Prod.snd he
    rw [hw] at this
    simpa [e, ZMod.chineseRemainder] using this
  have hfac : (M * l).factorization l = 1 := by
    rw [Nat.factorization_mul hM hl.ne_zero]
    simp only [Finsupp.add_apply, hl.factorization_self]
    have : ¬ l ∣ M := fun h => by
      have h' := Nat.Coprime.coprime_dvd_left h hc
      have h'' : l = 1 := by simpa using h'
      exact hl.one_lt.ne' h''
    rw [Nat.factorization_eq_zero_of_not_dvd this]
  refine ⟨v, ?_, ?_⟩
  · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, h1, Nat.cast_one]
  · rw [hfac, pow_one]
    have hk : PadicInt.toZMod (((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) - ((((v ^ 2 : (ZMod (M * l))ˣ) : ZMod (M * l)).val : ℕ) : ℤ_[l])) = 0 := by
      rw [map_sub, map_natCast, ZMod.natCast_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        map_pow, ZMod.cast_pow (dvd_mul_left l M), h2, sub_self]
    have hmem : _ ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := hk
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    exact hmem

theorem UpperTheory.Mu.nuQD :
    ∀ (φ : Frame) (H : HostRaw φ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), (l = H.q ∨ l = H.d) → ¬ (l - 1) / 2 ∣ n → nuOf l (cyc l H.E Ω) n = 0 := by
  intro φ H l _ Ω _ _ _ n hl hn
  have hl2 : l ≠ 2 := by
    rcases hl with rfl | rfl
    · exact H.q_ne_two
    · exact H.d_ne_two
  obtain ⟨u, hu⟩ := exists_sq_unit_not_dvd l n hn hl2
  have hle := nuOf_le_of_approx l (cyc l H.E Ω) n 0 (u ^ 2) ?_ hu
  · omega
  intro k
  have hN : H.condN = H.QS * H.q * H.d := rfl
  rcases hl with rfl | rfl
  · obtain ⟨v, hv1, hv⟩ := nuQD_unit H.condN (H.QS * H.d) H.q (by rw [hN]; ring)
      (mul_ne_zero H.QS_ne_zero H.d_prime.ne_zero) H.coprime_QSd_q u
    have ha : H.art (v ^ 2) = 1 := by
      rw [map_pow]
      exact H.art_q v hv1
    exact UpperTheory.Mu.hostApprox φ H H.q Ω (v ^ 2) ha (u ^ 2) hv k
  · obtain ⟨v, hv1, hv⟩ := nuQD_unit H.condN (H.QS * H.q) H.d hN
      (mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero) H.coprime_QSq_d u
    have ha : H.art (v ^ 2) = 1 := by
      haveI : NeZero (H.QS * H.q) := ⟨mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero⟩
      haveI : NeZero H.condN := ⟨H.condN_ne_zero⟩
      have hdvd : H.QS * H.q ∣ H.condN := ⟨H.d, hN⟩
      have hv2 : ((v ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] := by
        have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hv1
        rw [ZMod.natCast_val] at h1
        rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, Units.val_pow_eq_pow_val,
          ZMod.cast_pow hdvd, h1]
        simp
      have hd2 := H.art_d (v ^ 2) hv2
      rw [map_pow] at hd2 ⊢
      rcases H.art_d v hv1 with h | h
      · rw [h, one_pow]
      · rw [h] at hd2 ⊢
        rcases hd2 with h' | h'
        · exact h'
        · have hi : φ.iod = 1 := by
            rw [pow_two] at h'
            exact mul_eq_left.mp h'
          rw [hi, one_pow]
    exact UpperTheory.Mu.hostApprox φ H H.d Ω (v ^ 2) ha (u ^ 2) hv k
end

section
open NumberField Formalism.HC KStar.Tree

private theorem sum_factorization_mul_log_le (m : ℕ) (S : Finset ℕ) :
    ∑ l ∈ S, (m.factorization l : ℝ) * Real.log l ≤ Real.log m := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ S, (m.factorization l : ℝ) * Real.log l
      = ∑ l ∈ S.filter (· ∈ m.factorization.support), (m.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne ?_).symm
        intro l _ h
        by_contra hs
        rw [Finsupp.notMem_support_iff.mp hs] at h
        simp at h
    _ ≤ ∑ l ∈ m.factorization.support, (m.factorization l : ℝ) * Real.log l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          exact (Finset.mem_filter.mp hl).2
        · intro l hl _
          have hp : l.Prime := Nat.prime_of_mem_primeFactors (by simpa using hl)
          apply mul_nonneg (Nat.cast_nonneg _)
          exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

theorem UpperTheory.Mu.nuSum :
    ∀ (φ : Frame) (H : HostRaw φ) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), Odd n → ¬ (H.q - 1) / 2 ∣ n → ¬ (H.d - 1) / 2 ∣ n → ∀ ν : ℕ → ℕ, (∀ (l : ℕ) [Fact l.Prime], ν l = nuOf l (cyc l H.E Ω) n) → ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (ν l : ℝ) * Real.log l ≤ Real.log H.QS + Real.log n := by
  intro φ H Ω _ _ _ n hn hq hd ν hν S hS
  have key : ∀ l ∈ S, (ν l : ℝ) * Real.log l ≤
      (H.QS.factorization l : ℝ) * Real.log l + (n.factorization l : ℝ) * Real.log l := by
    intro l hl
    have hp : l.Prime := hS l hl
    haveI : Fact l.Prime := ⟨hp⟩
    have hlog : 0 ≤ Real.log l := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hnat : ν l ≤ H.QS.factorization l + n.factorization l := by
      rw [hν l]
      by_cases hlq : l = H.q
      · rw [UpperTheory.Mu.nuQD φ H l Ω n (Or.inl hlq) (hlq ▸ hq)]
        exact Nat.zero_le _
      by_cases hld : l = H.d
      · rw [UpperTheory.Mu.nuQD φ H l Ω n (Or.inr hld) (hld ▸ hd)]
        exact Nat.zero_le _
      have := UpperTheory.Mu.nuLe φ H l Ω n hn hlq hld
      split_ifs at this <;> omega
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ hlog
    exact_mod_cast hnat
  calc ∑ l ∈ S, (ν l : ℝ) * Real.log l
      ≤ ∑ l ∈ S, ((H.QS.factorization l : ℝ) * Real.log l + (n.factorization l : ℝ) * Real.log l) :=
        Finset.sum_le_sum key
    _ = ∑ l ∈ S, (H.QS.factorization l : ℝ) * Real.log l + ∑ l ∈ S, (n.factorization l : ℝ) * Real.log l :=
        Finset.sum_add_distrib
    _ ≤ Real.log H.QS + Real.log n :=
        add_le_add (sum_factorization_mul_log_le H.QS S) (sum_factorization_mul_log_le n S)
end

section
open NumberField Formalism.HC KStar.Tree

private theorem wDvdQS_crt {N A B : ℕ} [NeZero N] (h : N = A * B) (hAB : A.Coprime B) (y : ℕ) (hy : y.Coprime B) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ 1 [MOD A] ∧ (u : ZMod N).val ≡ y [MOD B] := by
  subst h
  obtain ⟨u, hu1, hu2⟩ := Formalism.HC.Der.exists_unit_crt hAB 1 y (Nat.coprime_one_left A) hy
  exact ⟨u, hu1, hu2⟩

private theorem wDvdQS_not_dvd {φ : Frame} (H : HostRaw φ) (A p : ℕ) (hp : p.Prime) (h3 : 3 < p)
    (hN : H.condN = A * p) (hA : A.Coprime p)
    (hart : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD A] → H.art u ^ 2 = 1) : ¬ p ∣ H.w := by
  intro hdvd
  haveI : NeZero H.condN := ⟨by rw [hN]; exact mul_ne_zero (fun h0 => by simp [h0] at hA; exact hp.one_lt.ne' hA) hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := H.exists_primitiveRoot_w
  have hζp : IsPrimitiveRoot (ζ ^ (H.w / p)) p := hζ.pow H.w_pos (Nat.div_mul_cancel hdvd).symm
  have hξ : IsPrimitiveRoot (Formalism.HC.Der.emb H (ζ ^ (H.w / p))) p :=
    hζp.map_of_injective (Formalism.HC.Der.emb H).toRingHom.injective
  have hpN : p ∣ H.condN := ⟨A, by rw [hN, mul_comm]⟩
  have hcop : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  obtain ⟨u, hu1, hu2⟩ := wDvdQS_crt hN hA 2 hcop
  have ha : H.art (u ^ 2) = 1 := by rw [map_pow]; exact hart u hu1
  have he := Formalism.HC.Der.emb_art H (u ^ 2) (ζ ^ (H.w / p))
  rw [ha, map_one, AlgEquiv.one_apply, Formalism.HC.Der.tauN_root] at he
  · have hmod : ((u ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1 [MOD p] := by
      have he' : (Formalism.HC.Der.emb H (ζ ^ (H.w / p))) ^ ((u ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val
          = (Formalism.HC.Der.emb H (ζ ^ (H.w / p))) ^ 1 := by
        rw [pow_one]; exact he.symm
      have := (hξ.isOfFinOrder hp.ne_zero).pow_eq_pow_iff_modEq.mp he'
      rwa [← hξ.eq_orderOf] at this
    have h4 : ((u ^ 2 : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 2 * 2 [MOD p] := by
      rw [Units.val_pow_eq_pow_val, sq, ZMod.val_mul]
      exact ((Nat.mod_modEq _ _).of_dvd hpN).trans (Nat.ModEq.mul hu2 hu2)
    have h41 : 1 ≡ 4 [MOD p] := hmod.symm.trans h4
    have h3 : p ∣ 3 := (Nat.modEq_iff_dvd' (by norm_num)).mp h41
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  · exact (hξ.pow_eq_one_iff_dvd _).mpr hpN

theorem UpperTheory.Mu.wDvdQS :
    ∀ (φ : Frame) (H : HostRaw φ), H.q ≠ 3 → H.w ∣ H.QS ∧ ¬ H.q ∣ H.w ∧ ¬ H.d ∣ H.w := by
  intro φ H hq3
  have hq := H.hyp.1
  have hd := H.hyp.2.1
  have hq8 := H.hyp.2.2.1
  have hd16 := H.hyp.2.2.2.1
  have hqd : Nat.Coprime H.q H.d := (Nat.coprime_primes hq hd).2 (by omega)
  have h1 : ¬ H.q ∣ H.w :=
    wDvdQS_not_dvd H (H.QS * H.d) H.q hq (by omega) (by ring)
      (Nat.Coprime.mul_left H.QS_coprime.coprime_mul_right_right hqd.symm) H.art_q
  have h2 : ¬ H.d ∣ H.w := by
    refine wDvdQS_not_dvd H (H.QS * H.q) H.d hd (by omega) rfl (Der.cop_QSq_d H) fun u hu => ?_
    rcases H.art_d u hu with h | h
    · rw [h, one_pow]
    · rw [h, sq]
      exact Prod.ext (show ((1, -1) : Formalism.FrobeniusOrbits.G0) * (1, -1) = 1 by decide) (mul_one _)
  refine ⟨?_, h1, h2⟩
  have h3 : H.w ∣ H.QS * H.q :=
    ((hd.coprime_iff_not_dvd.2 h2).symm).dvd_of_dvd_mul_right H.w_dvd_condN
  exact ((hq.coprime_iff_not_dvd.2 h1).symm).dvd_of_dvd_mul_right h3
end

section
open NumberField IsDedekindDomain Formalism.HC

open Ideal in
theorem UpperTheory.Mu.splitNotDvd :
    ∀ (φ : Frame) (H : HostAx φ), H.toHostRaw.Exact → ∀ p : ℕ, p.Prime → {v : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E → ¬ p ∣ H.QS := by
  intro φ H hex p hp hcard hdvd
  haveI hpf : Fact p.Prime := ⟨hp⟩
  haveI hgal : IsGalois ℚ H.E := H.galois
  obtain ⟨u, hu, hne⟩ := hex p hp hdvd
  set pZ : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)} with hpZ
  haveI hmax : pZ.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hmem : ∀ P : Ideal (𝓞 H.E), P.IsPrime → (((p : ℕ) : 𝓞 H.E) ∈ P ↔ P.LiesOver pZ) := by
    intro P hP
    constructor
    · intro h
      rw [Ideal.liesOver_iff]
      refine hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) ?_
      rw [hpZ, Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under] using h
    · intro h
      have hz : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
        rw [← (Ideal.liesOver_iff P pZ).1 h]
        exact Ideal.subset_span rfl
      simpa [Ideal.under] using hz
  have hset : (pZ.primesOver (𝓞 H.E)).ncard = Module.finrank ℚ H.E := by
    rw [← hcard]
    have heq : pZ.primesOver (𝓞 H.E) =
        (fun v : HeightOneSpectrum (𝓞 H.E) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal} := by
      ext P
      constructor
      · rintro ⟨hP, hl⟩
        have hnb : P ≠ ⊥ := by
          intro hb
          have hz := (hmem P hP).2 hl
          rw [hb, Ideal.mem_bot] at hz
          exact hp.ne_zero (by exact_mod_cast hz)
        exact ⟨⟨P, hP, hnb⟩, (hmem P hP).2 hl, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.isPrime, (hmem _ v.isPrime).1 hv⟩
    rw [heq, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  have hn : 0 < Module.finrank ℚ H.E := Module.finrank_pos
  obtain ⟨P, hPp, hPl⟩ := Set.nonempty_of_ncard_ne_zero (hset ▸ hn.ne')
  haveI := hPp
  haveI := hPl
  have key := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := Gal(H.E/ℚ)) pZ P
  rw [hset, IsGalois.card_aut_eq_finrank, mul_assoc] at key
  have h1 : Nat.card (Ideal.inertia Gal(H.E/ℚ) P) * P.inertiaDeg ℤ = 1 :=
    Nat.eq_of_mul_eq_mul_left hn (key.trans (mul_one _).symm)
  have hI : Nat.card (Ideal.inertia Gal(H.E/ℚ) P) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hbot := Subgroup.eq_bot_of_card_eq _ hI
  set σ : Gal(H.E/ℚ) := H.gal.symm (H.art u) with hσ
  have hin : ∀ x : 𝓞 H.E, σ • x - x ∈ P := by
    refine (H.der.inertia p P σ).2 ⟨u, ?_, by simp [σ]⟩
    refine Nat.ModEq.of_dvd ?_ hu
    have hpc : p ∣ H.condN := dvd_trans hdvd (HostRaw.QS_dvd_condN _)
    have hv : p ^ H.condN.factorization p ∣ H.condN := Nat.ordProj_dvd _ _
    refine Nat.div_dvd_div_left hv ?_
    exact dvd_pow_self p (Nat.Prime.factorization_pos_of_dvd hp (HostRaw.condN_ne_zero _) hpc).ne'
  have hσI : σ ∈ Ideal.inertia Gal(H.E/ℚ) P := AddSubgroup.mem_inertia.2 hin
  rw [hbot, Subgroup.mem_bot] at hσI
  apply hne
  simpa [σ] using congrArg H.gal hσI
end

section
open NumberField Formalism.BasicNotions KStar.Tree

namespace UpperTheory.Mu

theorem tr_odd (R : Ranks) : Odd (R.t * R.r) := by
  refine Nat.odd_mul.2 ⟨R.t_odd, ?_⟩
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have hm := R.two_le_m
  unfold Ranks.r
  exact ⟨a + b - 1, by omega⟩

variable {R : Ranks} (H : Host R)

theorem half_not_dvd {l : ℕ} (h : l = H.q ∨ l = H.d) : ¬ (l - 1) / 2 ∣ R.t * R.r := by
  have hpos : 0 < R.t * R.r := (tr_odd R).pos
  obtain ⟨hq, hd⟩ := H.qd_big
  have e : 4 * R.t * R.r = 4 * (R.t * R.r) := by ring
  rw [e] at hq hd
  apply Nat.not_dvd_of_pos_of_lt hpos
  generalize R.t * R.r = N at *
  rcases h with rfl | rfl <;> omega

theorem w_dvd_QS : H.w ∣ H.QS := (wDvdQS _ H.toHostRaw H.q_ne_three).1

variable (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

theorem nu_eq_zero_of_qd (l : ℕ) [Fact l.Prime] (h : l = H.q ∨ l = H.d) : nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 :=
  nuQD _ H.toHostRaw l Ω _ h (half_not_dvd H h)

theorem nu_eq_zero_of_not_dvd (l : ℕ) [Fact l.Prime] (h : ¬ l ∣ H.QS) : nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 := by
  by_cases hqd : l = H.q ∨ l = H.d
  · exact nu_eq_zero_of_qd H Ω l hqd
  · push_neg at hqd
    have hle := nuLe _ H.toHostRaw l Ω (R.t * R.r) (tr_odd R) hqd.1 hqd.2
    rw [if_neg h, Nat.factorization_eq_zero_of_not_dvd h] at hle
    omega

theorem nu_eq_zero_of_split (l : ℕ) [hl : Fact l.Prime]
    (h : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E) | ((l : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E) :
    nuOf l (cyc l H.E Ω) (R.t * R.r) = 0 :=
  nu_eq_zero_of_not_dvd H Ω l (splitNotDvd _ H.toHostAx H.QS_exact l hl.out h)

theorem sum_nu_le (ν : ℕ → ℝ) (hν : ∀ (l : ℕ) [Fact l.Prime], ν l = (nuOf l (cyc l H.E Ω) (R.t * R.r) : ℝ))
    (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∑ l ∈ S, ν l * Real.log l ≤ Real.log (H.QS : ℝ) + Real.log ((R.t * R.r : ℕ) : ℝ) := by
  classical
  let μ : ℕ → ℕ := fun l => if h : l.Prime then (haveI := Fact.mk h; nuOf l (cyc l H.E Ω) (R.t * R.r)) else 0
  have hμ : ∀ (l : ℕ) [Fact l.Prime], μ l = nuOf l (cyc l H.E Ω) (R.t * R.r) := fun l hl => dif_pos hl.out
  refine le_of_eq_of_le (Finset.sum_congr rfl fun l hl => ?_)
    (nuSum _ H.toHostRaw Ω _ (tr_odd R) (half_not_dvd H (Or.inl rfl)) (half_not_dvd H (Or.inr rfl)) μ hμ S hS)
  haveI := Fact.mk (hS l hl)
  rw [hν l, hμ l]

theorem budget_le : Real.log (H.QS : ℝ) + Real.log ((R.t * R.r : ℕ) : ℝ) ≤
    2 * Real.log R.n + Real.log R.t + Real.log R.r := by
  have h1 : Real.log (H.QS : ℝ) ≤ 2 * Real.log R.n := by
    have : ((H.QS : ℕ) : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast H.QS_le
    have h0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
    simpa using Real.log_le_log h0 this
  have h2 := (tr_odd R).pos
  have ht : (R.t : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right h2).ne'
  have hr : (R.r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left h2).ne'
  rw [Nat.cast_mul, Real.log_mul ht hr]
  linarith

end UpperTheory.Mu
end
