import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.VdTameWild
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDifferentExponentDenominator
import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiscrK
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiff

section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem exists_unit {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) :
    ∃ u : (ZMod N)ˣ, (u : ZMod N).val ≡ l [MOD ordCompl[l] N] ∧ (u : ZMod N).val ≡ 1 [MOD ordProj[l] N] := by
  have hcl : Nat.Coprime l (ordCompl[l] N) := Nat.coprime_ordCompl hl hN
  have hcop : Nat.Coprime (ordCompl[l] N) (ordProj[l] N) := (Nat.Coprime.pow_left _ hcl).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop l 1
  have hc1 : Nat.Coprime k (ordCompl[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk1]
    exact hcl
  have hc2 : Nat.Coprime k (ordProj[l] N) := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hk2]
    simp
  have hco : Nat.Coprime k N := by
    have h := Nat.Coprime.mul_right hc2 hc1
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at h
  refine ⟨ZMod.unitOfCoprime k hco, ?_, ?_⟩
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordCompl_dvd N l)).trans hk1
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact ((Nat.mod_modEq k N).of_dvd (Nat.ordProj_dvd N l)).trans hk2

private theorem unit_unique {N l : ℕ} (hN : N ≠ 0) (hl : l.Prime) {u v : (ZMod N)ˣ}
    (h1 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordCompl[l] N])
    (h2 : (u : ZMod N).val ≡ (v : ZMod N).val [MOD ordProj[l] N]) : u = v := by
  have hcop : Nat.Coprime (ordProj[l] N) (ordCompl[l] N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl hN)
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h1⟩
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h
  haveI : NeZero N := ⟨hN⟩
  apply Units.ext
  apply ZMod.val_injective
  have hu := ZMod.val_lt (u : ZMod N)
  have hv := ZMod.val_lt (v : ZMod N)
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] at h

private theorem val_iff {N f : ℕ} [NeZero N] (hf : f ∣ N) (u : (ZMod N)ˣ) (a : ℕ) :
    (u : ZMod N).val ≡ a [MOD f] ↔ ((ZMod.unitsMap hf u : (ZMod f)ˣ) : ZMod f) = (a : ZMod f) := by
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.natCast_eq_natCast_iff]

theorem UpperTheory.HF.artL_spec :
    ∀ {φ : Frame} (H : HostRaw φ) {l : ℕ}, l.Prime → (∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] ∧ H.artL l = H.art u) ∧ (∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] → (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l) ∧ ∀ g : φ.GG, g ∈ H.decG l ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
  intro φ H l hl
  haveI : NeZero H.condN := ⟨H.condN_ne_zero⟩
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hex := exists_unit hN hl
  have hart : H.artL l = H.art hex.choose := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.artL
    rw [dif_pos hex]
  obtain ⟨hc1, hc2⟩ := hex.choose_spec
  have part2 : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] →
      (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] → H.art u = H.artL l := by
    intro u hu1 hu2
    rw [hart, unit_unique hN hl (hu1.trans hc1.symm) (hu2.trans hc2.symm)]
  refine ⟨⟨hex.choose, hc1, hc2, hart⟩, part2, ?_⟩
  have hA : ordCompl[l] H.condN ∣ H.condN := Nat.ordCompl_dvd _ _
  haveI : NeZero (ordCompl[l] H.condN) :=
    ⟨fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hA))⟩
  obtain ⟨lA, hlA⟩ : ∃ w : (ZMod (ordCompl[l] H.condN))ˣ, (w : ZMod (ordCompl[l] H.condN)) = (l : ZMod _) :=
    ⟨ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl hN), ZMod.coe_unitOfCoprime _ _⟩
  have key : ∀ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ↔ ZMod.unitsMap hA u = lA ^ k := by
    intro u k
    rw [val_iff hA u (l ^ k), Units.ext_iff, Units.val_pow_eq_pow_val, hlA, Nat.cast_pow]
  let T : Subgroup φ.GG := ((Subgroup.zpowers lA).comap (ZMod.unitsMap hA)).map H.art
  have memT : ∀ g, g ∈ T ↔ ∃ (u : (ZMod H.condN)ˣ) (k : ℕ),
      (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ g = H.art u := by
    intro g
    simp only [T, Subgroup.mem_map, Subgroup.mem_comap, ← mem_powers_iff_mem_zpowers,
      Submonoid.mem_powers_iff]
    constructor
    · rintro ⟨u, ⟨k, hk⟩, rfl⟩
      exact ⟨u, k, (key u k).mpr hk.symm, rfl⟩
    · rintro ⟨u, k, hk, rfl⟩
      exact ⟨u, ⟨k, ((key u k).mp hk).symm⟩, rfl⟩
  have hle1 : UpperTheory.HF.Formalism.HC.HostRaw.decG H l ≤ T := by
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l g).mp hg
      exact (memT _).mpr ⟨u, 0, by simpa using hu, rfl⟩
    · rw [Subgroup.zpowers_le, hart]
      exact (memT _).mpr ⟨hex.choose, 1, by simpa using hc1, rfl⟩
  have hu1 : ZMod.unitsMap hA hex.choose = lA := by
    have h := (key hex.choose 1).mp (by simpa using hc1)
    simpa using h
  have hle2 : T ≤ UpperTheory.HF.Formalism.HC.HostRaw.decG H l := by
    intro g hg
    obtain ⟨u, k, hk, rfl⟩ := (memT g).mp hg
    have hw : ((u * (hex.choose ^ k)⁻¹ : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ 1
        [MOD ordCompl[l] H.condN] := by
      have h := (key (u * (hex.choose ^ k)⁻¹) 0).mpr
        (by rw [map_mul, map_inv, map_pow, hu1, (key u k).mp hk]; simp)
      simpa using h
    have hmem : H.art (u * (hex.choose ^ k)⁻¹) ∈ UpperTheory.HF.Formalism.HC.HostRaw.inertG H l :=
      (UpperTheory.HF.Formalism.HC.HostRaw.mem_inertG H l _).mpr ⟨_, hw, rfl⟩
    have heq : H.art u = H.art (u * (hex.choose ^ k)⁻¹) * H.artL l ^ k := by
      rw [hart, map_mul, map_inv, map_pow, inv_mul_cancel_right]
    rw [heq]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.decG
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)
  intro g
  rw [show UpperTheory.HF.Formalism.HC.HostRaw.decG H l = T from le_antisymm hle1 hle2]
  exact memT g
end

section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem card_eq_of_iff {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {A : Subgroup G} {B : Subgroup G'}
    (h : ∀ g, g ∈ A ↔ e g ∈ B) : Nat.card A = Nat.card B :=
  Nat.card_congr (e.toEquiv.subtypeEquiv h)

theorem UpperTheory.HF.grp_bridge :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ H.gal σ ∈ H.inertG l) ∧ (∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer _ P ↔ H.gal σ ∈ H.decG l) ∧ P.ramificationIdx ℤ = H.el l ∧ P.inertiaDeg ℤ = H.nw l ∧ Nat.card (H.decG l) = H.el l * H.nw l ∧ (primesOver (span {(l : ℤ)}) (𝓞 H.E)).ncard * (H.el l * H.nw l) = 4 * φ.ord := by
  intro φ H l hl P _ _
  haveI : Fact l.Prime := ⟨hl⟩
  haveI := H.galois
  haveI hmax : (span {(l : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have hI : ∀ σ : H.E ≃ₐ[ℚ] H.E, (∀ x : 𝓞 H.E, σ • x - x ∈ P) ↔ H.gal σ ∈ H.inertG l := fun σ =>
    (H.der.inertia l P σ).trans (H.mem_inertG l _).symm
  have hD : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer _ P ↔ H.gal σ ∈ H.decG l := fun σ =>
    (H.der.decomp l P σ).trans ((UpperTheory.HF.artL_spec H.toHostRaw hl).2.2 _).symm
  have hcI : Nat.card (P.inertia Gal(H.E/ℚ)) = H.el l :=
    card_eq_of_iff H.gal (fun σ => AddSubgroup.mem_inertia.trans (hI σ))
  have hcD : Nat.card (MulAction.stabilizer Gal(H.E/ℚ) P) = Nat.card (H.decG l) :=
    card_eq_of_iff H.gal hD
  have hle : H.inertG l ≤ H.decG l := le_sup_left
  have hmul : Nat.card (H.decG l) = H.el l * H.nw l := by
    rw [← ((H.inertG l).subgroupOf (H.decG l)).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    rfl
  have he : (span {(l : ℤ)}).ramificationIdxIn (𝓞 H.E) = H.el l := by
    rw [← hcI, card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P]
  have hf : (span {(l : ℤ)}).inertiaDegIn (𝓞 H.E) = H.nw l := by
    have h := card_stabilizer_eq (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P
    rw [hcD, hmul, he] at h
    exact (Nat.eq_of_mul_eq_mul_left (H.el_pos l) h).symm
  refine ⟨hI, hD, ?_, ?_, hmul, ?_⟩
  · rw [← he, ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P Gal(H.E/ℚ)]
  · rw [← hf, inertiaDegIn_eq_inertiaDeg (span {(l : ℤ)}) P Gal(H.E/ℚ)]
  · rw [← he, ← hf, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(l : ℤ)}) (𝓞 H.E) Gal(H.E/ℚ),
      IsGalois.card_aut_eq_finrank, H.der.finrank_E]
end

section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.diff_mult :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l ∧ multiplicity P (span {(l : 𝓞 H.E)}) = H.el l ∧ (¬ l ∣ H.el l → multiplicity P (differentIdeal ℤ (𝓞 H.E)) = H.el l - 1) ∧ (l ∣ H.el l → H.el l ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E))) := by
  intro φ H l hl P _ _
  haveI := H.galois
  obtain ⟨-, -, hram, -⟩ := grp_bridge H hl P
  have hmap : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) = span {(l : 𝓞 H.E)} := by
    simp [Ideal.map_span]
  have hne : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≠ ⊥ :=
    map_ne_bot_of_ne_bot (by simp [hl.ne_zero])
  have hmult : multiplicity P (span {(l : 𝓞 H.E)}) = H.el l := by
    rw [← hmap, ← IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hne, hram]
  have hmem : (l : 𝓞 H.E) ∈ P := by
    have hle : span {(l : 𝓞 H.E)} ≤ P := by
      rw [← hmap]
      exact map_le_of_le_comap (Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)})).le
    exact hle (Ideal.mem_span_singleton_self _)
  have hrat := GlobalTheory.DifferentElement.mult_ratio H.E l hl P inferInstance hmem
  rw [hmult, Nat.factorization_def _ hl] at hrat
  have hel0 : (0 : ℝ) < H.el l := by exact_mod_cast HostRaw.el_pos _ l
  have hvd : H.vdH l = (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) / H.el l := by
    have hr := congrArg (fun q : ℚ => (q : ℝ)) hrat
    push_cast at hr
    simp only [HostRaw.vdH]
    exact hr.symm
  have h1 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l := by
    rw [hvd]
    field_simp
  obtain ⟨htw1, htw2, -⟩ := vd_tame_wild H hl
  refine ⟨h1, hmult, fun hnd => ?_, fun hd => ?_⟩
  · have hv := htw1 hnd
    have hle : 1 ≤ H.el l := HostRaw.el_pos _ l
    have h2 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = ((H.el l - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle, h1, hv]
      field_simp
      push_cast
      ring
    exact_mod_cast h2
  · have hv := htw2 hd
    have h2 : (H.el l : ℝ) ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E)) := by
      rw [h1]
      nlinarith
    exact_mod_cast h2
end

section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem natMem {M : Type} [Field M] [NumberField M] (l : ℕ) (P : Ideal (𝓞 M))
    [h : P.LiesOver (span {(l : ℤ)})] (n : ℕ) : (n : 𝓞 M) ∈ P ↔ l ∣ n := by
  have h1 : (n : 𝓞 M) = algebraMap ℤ (𝓞 M) (n : ℤ) := by simp
  rw [h1, ← Ideal.mem_comap, ← Ideal.under_def, ← h.over, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

private theorem sq_lemma' {φ : Frame} (H : HostAx φ) (s : 𝓞 H.E) (hs : (s : H.E) = H.sqd) :
    s * s = -(H.d : 𝓞 H.E) := by
  apply RingOfIntegers.coe_injective
  have h2 := H.sqd_sq
  rw [← hs] at h2
  rw [← pow_two]
  push_cast
  exact h2

theorem UpperTheory.HF.diff_EK_supp :
    ∀ {φ : Frame} (H : HostAx φ), (∀ σ : H.E ≃ₐ[ℚ] H.E, σ • differentIdeal (𝓞 H.K) (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E)) ∧ (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], P ∣ differentIdeal (𝓞 H.K) (𝓞 H.E) ↔ ∃ l ∈ H.ramI, P.LiesOver (span {(l : ℤ)})) ∧ (∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) : ℝ) = H.el l * H.vdH l) ∧ 2 ∈ H.ramI := by
  intro φ H
  have hd := H.der
  obtain ⟨-, s, hs, -, hdiff⟩ := discr_K H
  have key : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.LiesOver (span {(l : ℤ)})],
      ¬ P ∣ span {s} := by
    intro l hl hld P _ hPs
    rw [Ideal.dvd_span_singleton] at hPs
    have hsq : s * s ∈ P := P.mul_mem_left s hPs
    rw [sq_lemma' H s hs, neg_mem_iff, natMem l P] at hsq
    exact hld ((Nat.prime_dvd_prime_iff_eq hl H.d_prime).1 hsq)
  have mult : ∀ l : ℕ, l.Prime → l ≠ H.d → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime]
      [P.LiesOver (span {(l : ℤ)})],
      multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)) = multiplicity P (differentIdeal ℤ (𝓞 H.E)) := by
    intro l hl hld P hPp _
    have hP0 : P ≠ ⊥ := by
      intro h0
      have hl' : (l : 𝓞 H.E) ∈ P := (natMem l P l).2 dvd_rfl
      rw [h0, Ideal.mem_bot] at hl'
      exact hl.ne_zero (by exact_mod_cast hl')
    have hpr : Prime P := Ideal.prime_of_isPrime hP0 hPp
    have hz : emultiplicity P (span {s}) = 0 := emultiplicity_eq_zero.2 (key l hl hld P)
    unfold multiplicity
    rw [hdiff, emultiplicity_mul hpr, hz, add_zero]
  refine ⟨fun σ => Formalism.HC.Der.kc_diff_smul_eq H.toHostRaw σ, ?_, ?_, ?_⟩
  · intro P hPp
    constructor
    · intro hPd
      have hmem := hd.diffSupport P hPp hPd
      have hne : H.QS * H.q ≠ 0 := mul_ne_zero H.QS_ne_zero H.q_prime.ne_zero
      obtain ⟨l, hl, hlq, hover⟩ := Formalism.HC.Der.kc_exists_prime P _ hne hmem
      refine ⟨l, ?_, hover⟩
      have hld : l ≠ H.d := by
        rintro rfl
        exact H.d_not_dvd_QSq hlq
      simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase]
      refine ⟨hld, ?_⟩
      rw [(mem_ram H hl).1]
      intro hel
      have h0 : multiplicity P (differentIdeal ℤ (𝓞 H.E)) = 0 := by
        rw [(diff_mult H hl P).2.2.1 (by rw [hel]; exact hl.not_dvd_one), hel]
      have hdv : P ∣ differentIdeal ℤ (𝓞 H.E) := hdiff ▸ dvd_mul_of_dvd_left hPd _
      exact multiplicity_eq_zero.1 h0 hdv
    · rintro ⟨l, hlI, hover⟩
      simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase] at hlI
      obtain ⟨hld, hlr⟩ := hlI
      have hl : l.Prime := by
        simp only [UpperTheory.HF.Formalism.HC.HostRaw.ram, Nat.mem_primeFactors] at hlr
        exact hlr.1
      have hv : H.vdH l ≠ 0 := ((mem_ram H hl).2.2.1).1 hlr
      have hm := (diff_mult H hl P).1
      have hne : (H.el l : ℝ) * H.vdH l ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (UpperTheory.HF.Formalism.HC.HostRaw.el_pos H.toHostRaw l).ne') hv
      rw [← hm, ← mult l hl hld P] at hne
      by_contra hnd
      exact hne (by exact_mod_cast multiplicity_eq_zero.2 hnd)
  · intro l hl hld P _ _
    rw [mult l hl hld P]
    exact (diff_mult H hl P).1
  · simp only [UpperTheory.HF.Formalism.HC.HostRaw.ramI, Finset.mem_erase, UpperTheory.HF.Formalism.HC.HostRaw.ram,
      Nat.mem_primeFactors]
    refine ⟨H.d_ne_two.symm, Nat.prime_two, ?_, ?_⟩
    · exact Int.ofNat_dvd_left.1 hd.discr_primes.2.1
    · exact Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.E)
end

section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.half_supp :
    ∀ {φ : Frame} (H : HostAx φ) (𝔟 : Ideal (𝓞 H.E)), differentIdeal (𝓞 H.K) (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) → 𝔟 ⊔ H.conj • 𝔟 = ⊤ → (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime], ((P ∣ 𝔟 ∨ H.conj • P ∣ 𝔟) ↔ ∃ l ∈ H.ramI, P.LiesOver (span {(l : ℤ)})) ∧ ¬ (P ∣ 𝔟 ∧ H.conj • P ∣ 𝔟) ∧ (P ∣ 𝔟 → multiplicity P 𝔟 = multiplicity P (differentIdeal (𝓞 H.K) (𝓞 H.E)))) ∧ ∃ s : 𝓞 H.E, (s : H.E) = H.sqd ∧ differentIdeal ℤ (𝓞 H.E) = 𝔟 * (H.conj • 𝔟) * span {s} := by
  intro φ H B hD hcop
  have mono : ∀ {I J : Ideal (𝓞 H.E)}, I ≤ J → H.conj • I ≤ H.conj • J := by
    intro I J h
    rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
    exact Ideal.map_mono h
  have inv : ∀ I : Ideal (𝓞 H.E), H.conj • H.conj • I = I := by
    intro I
    rw [smul_smul, H.conj_mul_conj, one_smul]
  have sw : ∀ {I J : Ideal (𝓞 H.E)}, H.conj • I ≤ J ↔ I ≤ H.conj • J := by
    intro I J
    constructor
    · intro h
      simpa only [inv] using mono h
    · intro h
      simpa only [inv] using mono h
  refine ⟨fun P hP => ?_, ?_⟩
  · have hsupp := (UpperTheory.HF.diff_EK_supp H).2.1 P
    have notboth : ¬ (B ≤ P ∧ B ≤ H.conj • P) := by
      rintro ⟨h1, h2⟩
      apply hP.ne_top
      rw [eq_top_iff, ← hcop]
      exact sup_le h1 (sw.2 h2)
    have hncB : P ∣ B → ¬ P ∣ H.conj • B := by
      intro h1 h2
      rw [Ideal.dvd_iff_le] at h1 h2
      exact notboth ⟨h1, sw.1 h2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hsupp, hD]
      constructor
      · rintro (h | h)
        · exact dvd_mul_of_dvd_left h _
        · rw [Ideal.dvd_iff_le] at h ⊢
          exact le_trans Ideal.mul_le_right (sw.2 h)
      · intro h
        rw [Ideal.dvd_iff_le] at h
        rcases hP.mul_le.1 h with h1 | h1
        · exact Or.inl (Ideal.dvd_iff_le.2 h1)
        · exact Or.inr (Ideal.dvd_iff_le.2 (sw.1 h1))
    · rintro ⟨h1, h2⟩
      rw [Ideal.dvd_iff_le] at h1 h2
      exact notboth ⟨h1, h2⟩
    · intro h1
      have hP0 : P ≠ ⊥ := by
        rintro rfl
        rw [Ideal.dvd_iff_le, le_bot_iff] at h1
        have hle : B ⊔ H.conj • B ≤ ⊥ := sup_le h1.le (sw.2 (by rw [h1]; exact bot_le))
        rw [hcop] at hle
        exact hP.ne_top (eq_top_iff.2 hle)
      have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
      unfold multiplicity
      rw [hD, emultiplicity_mul hpr, emultiplicity_eq_zero.2 (hncB h1), add_zero]
  · obtain ⟨-, s, hs, -, hdiff⟩ := discr_K H
    exact ⟨s, hs, hdiff.trans (by rw [hD])⟩
end
