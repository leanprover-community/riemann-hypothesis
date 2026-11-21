import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittUnramified.GhostComponentG
import Formalism.PeriodIntegrals.WittUnram

section
noncomputable section

namespace PI.WittUnramWork

open WittVector Finset

variable {p : ℕ} [hp : Fact p.Prime] {W k : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field k] [CharP k p] [PerfectRing k p]

theorem psi_injective (ψ : W →+* WittVector p k) (hirr : Irreducible (p : W)) :
    Function.Injective ψ := by
  refine (injective_iff_map_eq_zero ψ).2 ?_
  intro x hx
  by_contra hne
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hirr
  obtain ⟨u, hu⟩ := hn
  have h2 : ψ ((p : W) ^ n) = 0 := by rw [← hu, map_mul, hx, zero_mul]
  rw [map_pow, map_natCast] at h2
  exact pow_ne_zero n (WittVector.p_nonzero p k) h2

theorem psi_step (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (w : WittVector p k) :
    ∃ a : W, ∃ b : WittVector p k, w = ψ a + (p : WittVector p k) * b := by
  obtain ⟨a, ha⟩ := hres (w.coeff 0)
  refine ⟨a, ?_⟩
  by_cases hz : w - ψ a = 0
  · exact ⟨0, by rw [mul_zero, add_zero]; exact sub_eq_zero.mp hz⟩
  · obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul (w - ψ a) hz
    have hc : (w - ψ a).coeff 0 = 0 := by
      have h3 := WittVector.add_coeff_zero (ψ a) (w - ψ a)
      rw [show ψ a + (w - ψ a) = w by abel, h0, ha] at h3
      linear_combination -h3
    have hm : m ≠ 0 := by
      rintro rfl
      apply hb0
      rw [pow_zero, one_mul] at hb
      rw [← hb]
      exact hc
    refine ⟨(p : WittVector p k) ^ (m - 1) * b, ?_⟩
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm), ← hb]
    ring

theorem psi_surjective (ψ : W →+* WittVector p k) (res : W →+* k) (hres : Function.Surjective res)
    (h0 : ∀ x, (ψ x).coeff 0 = res x) (hC : IsAdicComplete (Ideal.span {(p : W)}) W) :
    Function.Surjective ψ := by
  intro w
  choose A B hAB using psi_step ψ res hres h0
  obtain ⟨r, hr0, hrs⟩ : ∃ r : ℕ → WittVector p k, r 0 = w ∧ ∀ n, r (n + 1) = B (r n) :=
    ⟨fun n => B^[n] w, rfl, fun n => Function.iterate_succ_apply' B n w⟩
  obtain ⟨s, hs0, hss⟩ : ∃ s : ℕ → W, s 0 = 0 ∧ ∀ n, s (n + 1) = s n + A (r n) * (p : W) ^ n :=
    ⟨fun n => ∑ i ∈ Finset.range n, A (r i) * (p : W) ^ i, by simp, fun n => Finset.sum_range_succ _ _⟩
  have hinv : ∀ n, w = ψ (s n) + (p : WittVector p k) ^ n * r n := by
    intro n
    induction n with
    | zero => rw [hs0, hr0, map_zero, pow_zero, one_mul, zero_add]
    | succ n ih =>
      calc w = ψ (s n) + (p : WittVector p k) ^ n * r n := ih
        _ = ψ (s n) + (p : WittVector p k) ^ n * (ψ (A (r n)) + (p : WittVector p k) * B (r n)) := by
          rw [← hAB (r n)]
        _ = ψ (s (n + 1)) + (p : WittVector p k) ^ (n + 1) * r (n + 1) := by
          rw [hss, hrs, map_add, map_mul, map_pow, map_natCast]
          ring
  have hdiv : ∀ m n, m ≤ n → (p : W) ^ m ∣ s n - s m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hss, add_sub_right_comm]
      exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow _ hmn) _)
  have hI : ∀ n (x : W), x ∈ (Ideal.span {(p : W)} ^ n • ⊤ : Submodule W W) ↔ (p : W) ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec (f := s) (fun {m n} hmn => by
    rw [SModEq.sub_mem, hI]
    exact dvd_sub_comm.mp (hdiv m n hmn))
  have hw : ∀ n, (p : WittVector p k) ^ n ∣ w - ψ L := by
    intro n
    obtain ⟨c, hc⟩ := (hI n _).1 (SModEq.sub_mem.1 (hL n))
    refine ⟨ψ c + r n, ?_⟩
    have h2 : ψ (s n) - ψ L = (p : WittVector p k) ^ n * ψ c := by
      rw [← map_sub, hc, map_mul, map_pow, map_natCast]
    calc w - ψ L = ψ (s n) + (p : WittVector p k) ^ n * r n - ψ L := by rw [← hinv n]
      _ = (p : WittVector p k) ^ n * (ψ c + r n) := by linear_combination h2
  have hzero : w - ψ L = 0 := by
    by_contra hne
    obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul (w - ψ L) hne
    obtain ⟨c, hc⟩ := hw (m + 1)
    rw [hb, pow_succ, mul_assoc] at hc
    have hp : (p : WittVector p k) ^ m ≠ 0 := pow_ne_zero m (WittVector.p_nonzero p k)
    have hbc := mul_left_cancel₀ hp hc
    apply hb0
    rw [hbc]
    first
    | rw [WittVector.mul_coeff_zero, WittVector.coeff_p_zero, zero_mul]
    | simp
  exact ⟨L, (sub_eq_zero.mp hzero).symm⟩

end PI.WittUnramWork
end
end

section
noncomputable section

namespace PI.WittUnramWork

open WittVector

private theorem map_frobenius' {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (x : WittVector p R) :
    WittVector.map g (WittVector.frobenius x) = WittVector.frobenius (WittVector.map g x) := by
  ext n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem wittUnram_main : PI.WittUnram := by
  intro p f _ W Qq _ _ _ _ _ σ hfrac hirr hcard hcomp hσ
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have hF : ∀ x : W, ∃ y : W, sigW hinj σ hσ x = x ^ p + (p : W) * y := sigW_lift hinj σ hσ
  set I : Ideal W := Ideal.span {(p : W)} with hI
  haveI hmax : I.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field (W ⧸ I) := Ideal.Quotient.field I
  have hp0 : ((p : ℕ) : W ⧸ I) = 0 := by
    have h : Ideal.Quotient.mk I (p : W) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rwa [map_natCast] at h
  haveI hchar : CharP (W ⧸ I) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0
  haveI hfin : Finite (W ⧸ I) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨e⟩ : Nonempty ((W ⧸ I) ≃+* GaloisField p f) := by
    letI : Algebra (ZMod p) (W ⧸ I) := (ZMod.castHom (dvd_refl p) (W ⧸ I)).toAlgebra
    exact ⟨(GaloisField.algEquivGaloisField p f hcard).toRingEquiv⟩
  have hpQ : ((p : ℕ) : Qq) ≠ 0 := by
    rw [← map_natCast (algebraMap W Qq) p]
    exact fun h => hirr.ne_zero (hinj (h.trans (map_zero _).symm))
  letI : Invertible ((p : ℕ) : Qq) := invertibleOfNonzero hpQ
  let ψ : W →+* WittVector p (W ⧸ I) :=
    (WittVector.map (Ideal.Quotient.mk I)).comp (sHom p Qq (sigW hinj σ hσ) hF hinj)
  have h0 : ∀ x, (ψ x).coeff 0 = Ideal.Quotient.mk I x := by
    intro x
    show (WittVector.map (Ideal.Quotient.mk I) (sHom p Qq (sigW hinj σ hσ) hF hinj x)).coeff 0 = _
    rw [WittVector.map_coeff, sHom_coeff_zero]
  have hψi : Function.Injective ψ := psi_injective ψ hirr
  have hψs : Function.Surjective ψ :=
    psi_surjective ψ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective h0 hcomp
  let χ : W →+* WittVector p (GaloisField p f) := (WittVector.map (e : (W ⧸ I) →+* GaloisField p f)).comp ψ
  have hχ : Function.Bijective χ :=
    ⟨(WittVector.map_injective _ e.injective).comp hψi, (WittVector.map_surjective _ e.surjective).comp hψs⟩
  have hφ : ∀ w, (RingEquiv.ofBijective χ hχ).symm (χ w) = w := by
    intro w
    have h := (RingEquiv.ofBijective χ hχ).symm_apply_apply w
    rwa [RingEquiv.ofBijective_apply] at h
  have hfrob : ∀ w, WittVector.frobenius (χ w) = χ (sigW hinj σ hσ w) := by
    intro w
    show _ = WittVector.map (e : (W ⧸ I) →+* GaloisField p f)
      (WittVector.map (Ideal.Quotient.mk I) (sHom p Qq (sigW hinj σ hσ) hF hinj (sigW hinj σ hσ w)))
    rw [sHom_frob, map_frobenius', map_frobenius']
    rfl
  refine ⟨(RingEquiv.ofBijective χ hχ).symm, ?_⟩
  intro x
  obtain ⟨w, rfl⟩ := hχ.2 x
  rw [hfrob, hφ, hφ]
  exact (sigW_spec hinj σ hσ w).symm

end PI.WittUnramWork
end
end
