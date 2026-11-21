import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcEqOfPowEqOne
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder

section
open NumberField Formalism.HC

theorem UpperTheory.rootOfUnity_galois_action_CMDatum :
    ∀ (φ : Frame) (H : HostAx φ) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      H.gal.symm φ.iod z = z ∧ H.conj z = z⁻¹ ∧ H.gal.symm φ.sg z = z⁻¹ := by
  intro φ H z hz
  have C : HostCore H.toHostRaw := { H.der with }
  have h1 : H.gal.symm φ.iod z = z :=
    Der.kc_iod_fix H.toHostRaw C _ (H.gal.apply_symm_apply _) z hz
  have h2 : H.conj z = z⁻¹ :=
    eq_inv_of_mul_eq_one_right (Der.kc_conj_mul_self H.toHostRaw C z hz)
  refine ⟨h1, h2, ?_⟩
  rw [← φ.cc_mul_iod, map_mul, AlgEquiv.mul_apply, h1]
  exact h2
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions

private theorem prod_pair {G : Type*} [Group G] [Fintype G] {M : Type*} [CommMonoid M]
    (s : G) (hs1 : s ≠ 1) (hs2 : s * s = 1) (f : G → M) (hf : ∀ g, f g * f (g * s) = 1) :
    ∏ g, f g = 1 := by
  refine Finset.prod_involution (fun g _ => g * s) (fun g _ => hf g) ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro g _ _ h
    apply hs1
    simpa using h
  · intro g _
    rw [mul_assoc, hs2, mul_one]

private theorem phase_pair (w : ℂ) (m : ℕ) (hm : 0 < m) (hw : w ^ m = 1) (hz : 1 + w ≠ 0) :
    (1 + w) / ((‖1 + w‖ : ℝ) : ℂ) * ((1 + w⁻¹) / ((‖1 + w⁻¹‖ : ℝ) : ℂ)) = 1 := by
  have hn : ‖w‖ = 1 := by
    have h := congrArg (‖·‖) hw
    simp only [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) hm.ne').1 h
  have hinv : w⁻¹ = (starRingEnd ℂ) w := by
    have : Complex.normSq w = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn, one_pow]
    rw [Complex.inv_def, this, inv_one, Complex.ofReal_one, mul_one]
  have hconj : 1 + w⁻¹ = (starRingEnd ℂ) (1 + w) := by
    rw [hinv, map_add, map_one]
  rw [hconj, Complex.norm_conj]
  set a := 1 + w with ha
  have hna : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  rw [div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

theorem UpperTheory.prod_cmType_phase_one_add_rootOfUnity :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → z ≠ -1 →
      ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) (1 + z) / ((‖H.emb ((eT τ : R.Psi) : R.GG) (1 + z)‖ : ℝ) : ℂ)) = 1 := by
  intro R H ι _ eT z hz hzne
  letI : Fintype R.Psi := Fintype.ofEquiv ι eT
  set F : R.Psi → ℂ := fun p =>
    H.emb (p : R.GG) (1 + z) / ((‖H.emb (p : R.GG) (1 + z)‖ : ℝ) : ℂ) with hF
  change ∏ τ, F (eT τ) = 1
  rw [Equiv.prod_comp eT F]
  obtain ⟨m, hm, hzm⟩ := hz
  have hsg := (UpperTheory.rootOfUnity_galois_action_CMDatum R.toFrame H.toHostAx z ⟨m, hm, hzm⟩).2.2
  refine prod_pair ⟨R.sg, R.sg_mem_Psi⟩ ?_ ?_ F ?_
  · intro h
    exact R.sg_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext R.sg_mul_sg
  · intro g
    have hz1 : 1 + z ≠ 0 := by
      intro h
      apply hzne
      linear_combination h
    have key : H.emb ((g * ⟨R.sg, R.sg_mem_Psi⟩ : R.Psi) : R.GG) (1 + z)
        = 1 + (H.emb (g : R.GG) z)⁻¹ := by
      simp only [Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, Subgroup.coe_mul, map_mul,
        RingHom.comp_apply]
      change H.φ₀ ((H.gal.symm (g : R.GG) * H.gal.symm R.sg) (1 + z))
        = 1 + (H.φ₀ ((H.gal.symm (g : R.GG)) z))⁻¹
      rw [AlgEquiv.mul_apply, map_add, map_one, hsg, map_add, map_one, map_inv₀, map_add,
        map_one, map_inv₀]
    have hne : 1 + H.emb (g : R.GG) z ≠ 0 := by
      have : H.emb (g : R.GG) (1 + z) ≠ 0 := (map_ne_zero _).2 hz1
      simpa using this
    simp only [hF, key]
    have e1 : H.emb (g : R.GG) (1 + z) = 1 + H.emb (g : R.GG) z := by simp
    rw [e1]
    exact phase_pair _ m hm (by rw [← map_pow, hzm, map_one]) hne
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions

private theorem emb_sqd {R : Ranks} (H : Host R) (g : R.Psi) :
    H.emb (g : R.GG) H.sqd = Complex.I * (Real.sqrt H.d : ℂ) := by
  have hfix : (H.gal.symm (g : R.GG)) H.sqd = H.sqd := by
    have := (Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx (H.gal.symm (g : R.GG))).1
    apply this
    simp [Formalism.HC.HostRaw.galE]
  have h0 := H.φ₀_mem
  simp only [Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq] at h0
  simp only [Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, RingHom.comp_apply]
  change H.φ₀ ((H.gal.symm (g : R.GG)) H.sqd) = _
  rw [hfix, h0]

private theorem four_dvd {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : 4 ∣ Nat.card φ.Psi := by
  rw [Formalism.HC.Frame.natCard_Psi]
  have h1 : 4 ∣ 2 ^ φ.e := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact Nat.pow_dvd_pow 2 H.two_le_e
  exact Dvd.dvd.mul_left (h1.trans φ.two_pow_dvd_ord) 2

private theorem val_sqrt {L : Type} [Field L] [NumberField L] (d : ℕ) (δ : L) (h : δ ^ 2 = -(d : L))
    (P : HeightOneSpectrum (𝓞 L)) (hP : ((d : ℕ) : 𝓞 L) ∉ P.asIdeal) : P.valuation L δ = 1 := by
  have hd : P.valuation L (d : L) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 L) L) d, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact hP
  have h2 : P.valuation L δ ^ 2 = 1 := by
    rw [← map_pow, h, Valuation.map_neg, hd]
  exact sq_eq_one.mp h2

private theorem val_one_add {L : Type} [Field L] [NumberField L] (N : ℕ) (hN : Even N) (hN0 : 0 < N) (z : L)
    (hz : z ^ N = 1) (hne : z ≠ -1) (P : HeightOneSpectrum (𝓞 L)) (hP : ((N : ℕ) : 𝓞 L) ∉ P.asIdeal) :
    P.valuation L (1 + z) = 1 := by
  have hint : IsIntegral ℤ z := by
    refine ⟨Polynomial.X ^ N - 1, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C 1 hN0.ne'
    · simp [hz]
  set zi : 𝓞 L := ⟨z, hint⟩ with hzi
  have hcoe : algebraMap (𝓞 L) L zi = z := rfl
  have hzi1 : zi ^ N = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, hcoe, hz, map_one]
  have hm1 : (-1 : 𝓞 L) ^ N = 1 := hN.neg_one_pow
  have hmem : (1 + zi) ∉ P.asIdeal := by
    intro h
    apply hne
    have : zi = -1 := by
      refine Formalism.HC.Der.kc_eq_of_pow_eq_one P.asIdeal hP hzi1 hm1 ?_
      simpa [sub_neg_eq_add, add_comm] using h
    have := congrArg (algebraMap (𝓞 L) L) this
    rwa [hcoe, map_neg, map_one] at this
  have : (1 + z : L) = algebraMap (𝓞 L) L (1 + zi) := by
    rw [map_add, map_one, hcoe]
  rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
  exact hmem

theorem UpperTheory.exists_unit_eq_rootOfUnity_mul_conj_phase_one :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      ∃ δ : (H.E)ˣ, (δ : H.E) = z * H.conj (δ : H.E) ∧
        (∀ P : HeightOneSpectrum (𝓞 H.E), ((H.condN : ℕ) : 𝓞 H.E) ∉ P.asIdeal → P.valuation H.E (δ : H.E) = 1) ∧
        ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) (δ : H.E) / ((‖H.emb ((eT τ : R.Psi) : R.GG) (δ : H.E)‖ : ℝ) : ℂ)) = 1 := by
  intro R H ι _ eT z hz
  by_cases hne : z = -1
  · subst hne
    have hs : H.sqd ≠ 0 := H.sqd_ne_zero
    refine ⟨Units.mk0 H.sqd hs, ?_, ?_, ?_⟩
    · have hc : H.conj H.sqd = -H.sqd := H.conj_sqd
      rw [Units.val_mk0, hc]
      ring
    · intro P hP
      refine val_sqrt H.d _ H.sqd_sq P fun hm => hP ?_
      obtain ⟨k, hk⟩ := H.d_dvd_condN
      rw [hk, Nat.cast_mul]
      exact P.asIdeal.mul_mem_right _ hm
    · have hd : 0 < H.d := H.hyp.2.1.pos
      have hr : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
      have ht : ∀ g : R.Psi, H.emb (g : R.GG) H.sqd / ((‖H.emb (g : R.GG) H.sqd‖ : ℝ) : ℂ) = Complex.I := fun g => by
        rw [emb_sqd H g, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hr.le, mul_div_assoc, div_self (by exact_mod_cast hr.ne'), mul_one]
      simp only [Units.val_mk0, ht]
      rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_congr eT]
      obtain ⟨k, hk⟩ : 4 ∣ Nat.card R.Psi := four_dvd H.toHostRaw
      rw [hk, pow_mul, Complex.I_pow_four, one_pow]
  · have hδ : 1 + z ≠ 0 := fun h0 => hne (by linear_combination h0)
    have hconj : H.conj z = z⁻¹ := (UpperTheory.rootOfUnity_galois_action_CMDatum _ H.toHostAx z hz).2.1
    have hz0 : z ≠ 0 := UpperTheory.root_ne_zero hz
    refine ⟨Units.mk0 (1 + z) hδ, ?_, ?_, ?_⟩
    · rw [Units.val_mk0, map_add, map_one, hconj]
      field_simp
      ring
    · intro P hP
      have hw : z ^ H.toHostRaw.w = 1 := (H.toHostRaw.isMu_iff z).1 hz
      obtain ⟨k, hk⟩ := H.toHostRaw.w_dvd_condN
      have hN : z ^ H.condN = 1 := by rw [hk, pow_mul, hw, one_pow]
      exact val_one_add H.condN (even_iff_two_dvd.2 H.two_dvd_condN) (Nat.pos_of_ne_zero H.condN_ne_zero) z hN hne P hP
    · exact UpperTheory.prod_cmType_phase_one_add_rootOfUnity R H ι eT z hz hne
end
