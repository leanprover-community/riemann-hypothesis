import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith

section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.imgOne_gcd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ H.condN → g ∣ H.condN → H.imgOne (Nat.gcd f g) = H.imgOne f ⊔ H.imgOne g := by
  intro φ H f g hf hg
  have hgcd : Nat.gcd f g ∣ H.condN := (Nat.gcd_dvd_left f g).trans hf
  apply le_antisymm
  · rintro x hx
    rw [H.mem_imgOne hgcd] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have key := Der.Rd.KK_gcd (N := H.condN) ((H.imgOne f ⊔ H.imgOne g).comap H.art) hf hg
      (fun v hv => Subgroup.mem_sup_left ((H.mem_imgOne hf _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      (fun v hv => Subgroup.mem_sup_right ((H.mem_imgOne hg _).2 ⟨v, Der.Rd.mem_KK.1 hv, rfl⟩))
      u (Der.Rd.mem_KK.2 hu)
    exact key
  · exact sup_le (H.imgOne_anti (Nat.gcd_dvd_left f g) hf) (H.imgOne_anti (Nat.gcd_dvd_right f g) hg)
end

section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.condE_spec :
    ∀ {φ : Frame} (H : HostRaw φ), H.condE ∣ H.condN ∧ 0 < H.condE ∧ ∀ f : ℕ, f ∣ H.condN → (H.imgOne f = ⊥ ↔ H.condE ∣ f) := by
  intro φ H
  have hN0 : H.condN ≠ 0 := H.condN_ne_zero
  have hN : H.imgOne H.condN = ⊥ := by
    rw [H.imgOne_eq_bot_iff dvd_rfl]
    intro u hu
    have h1 : u = 1 := by
      haveI : NeZero H.condN := ⟨hN0⟩
      apply Units.ext
      have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 hu
      rw [ZMod.natCast_zmod_val, Nat.cast_one] at h2
      exact h2
    rw [h1, map_one]
  have hmem : H.condE ∣ H.condN ∧ H.imgOne H.condE = ⊥ :=
    Nat.sInf_mem (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥}) ⟨H.condN, dvd_rfl, hN⟩
  have hpos : 0 < H.condE := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hN0)
  refine ⟨hmem.1, hpos, fun f hf => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hg : H.imgOne (Nat.gcd H.condE f) = ⊥ := by
      rw [UpperTheory.HF.imgOne_gcd H hmem.1 hf, hmem.2, h, sup_bot_eq]
    have hle : H.condE ≤ Nat.gcd H.condE f :=
      Nat.sInf_le (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥})
        ⟨(Nat.gcd_dvd_right _ _).trans hf, hg⟩
    have heq : Nat.gcd H.condE f = H.condE := le_antisymm (Nat.gcd_le_left _ hpos) hle
    rw [← heq]
    exact Nat.gcd_dvd_right _ _
  · exact le_bot_iff.1 (hmem.2 ▸ H.imgOne_anti h hf)
end

section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem card_map_dvd {G G' : Type*} [Group G] [Group G'] (a : G →* G') {A B : Subgroup G} (h : A ≤ B) :
    Nat.card (B.map a) ∣ Nat.card (A.map a) * A.relIndex B := by
  have hAB : A.map a ≤ B.map a := Subgroup.map_mono h
  have hc : Nat.card (B.map a) = Nat.card (A.map a) * (A.map a).relIndex (B.map a) := by
    rw [Subgroup.relIndex, ← Subgroup.card_mul_index ((A.map a).subgroupOf (B.map a))]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rw [hc]
  apply mul_dvd_mul_left
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_dvd_of_le_left B (Subgroup.le_comap_map a A)

private theorem index_unitsOne {φ : Frame} (H : HostRaw φ) {f : ℕ} (hf : f ∣ H.condN) :
    (H.unitsOne f).index = f.totient := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.1 hf)
  have hg : Nat.gcd f H.condN = f := Nat.gcd_eq_left hf
  haveI : NeZero (Nat.gcd f H.condN) := ⟨by rw [hg]; exact hf0⟩
  unfold HostRaw.unitsOne
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (ZMod.unitsMap_surjective _), Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, hg]

theorem UpperTheory.HF.card_imgOne_dvd :
    ∀ {φ : Frame} (H : HostRaw φ) {f g : ℕ}, f ∣ g → g ∣ H.condN → Nat.card (H.imgOne f) ∣ Nat.card (H.imgOne g) * (g.totient / f.totient) := by
  intro φ H f g hfg hg
  have hf : f ∣ H.condN := hfg.trans hg
  have hle : H.unitsOne g ≤ H.unitsOne f := by
    intro u hu
    rw [H.mem_unitsOne hg] at hu
    rw [H.mem_unitsOne hf]
    exact Nat.ModEq.of_dvd hfg hu
  have hd := card_map_dvd H.art hle
  have hidx := Subgroup.relIndex_mul_index hle
  rw [index_unitsOne H hf, index_unitsOne H hg] at hidx
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      subst h0
      exact H.condN_ne_zero (zero_dvd_iff.1 hf)
    · exact h0
  have htot : 0 < f.totient := Nat.totient_pos.2 hf0
  have hr : g.totient / f.totient = (H.unitsOne g).relIndex (H.unitsOne f) := by
    rw [← hidx, Nat.mul_div_cancel _ htot]
  rw [hr]
  exact hd
end

section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem layer_dvd {N l j : ℕ} (hj : j ≤ N.factorization l) : ordCompl[l] N * l ^ j ∣ N := by
  have h := Nat.ordProj_mul_ordCompl_eq_self N l
  conv_rhs => rw [← h, mul_comm]
  exact mul_dvd_mul_left _ (pow_dvd_pow l hj)

private theorem dvd_layer_iff {N c l j : ℕ} (hl : l.Prime) (hN : N ≠ 0) (hc : c ∣ N) :
    c ∣ ordCompl[l] N * l ^ j ↔ c.factorization l ≤ j := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.1 hc)
  have hM : 0 < ordCompl[l] N := Nat.ordCompl_pos l hN
  have hM0 : ordCompl[l] N * l ^ j ≠ 0 := Nat.mul_ne_zero hM.ne' (pow_ne_zero _ hl.ne_zero)
  have hfM : (ordCompl[l] N * l ^ j).factorization = N.factorization.erase l + Finsupp.single l j := by
    rw [Nat.factorization_mul hM.ne' (pow_ne_zero _ hl.ne_zero), Nat.factorization_ordCompl,
      hl.factorization_pow]
  have hcN := (Nat.factorization_le_iff_dvd hc0 hN).2 hc
  rw [← Nat.factorization_le_iff_dvd hc0 hM0, hfM]
  constructor
  · intro h
    have := h l
    simpa using this
  · intro h q
    by_cases hq : q = l
    · subst hq
      simpa using h
    · rw [Finsupp.add_apply, Finsupp.erase_ne hq]
      exact le_add_right (hcN q)

theorem UpperTheory.HF.layer_bot :
    ∀ {φ : Frame} (H : HostRaw φ) {l j : ℕ}, l.Prime → j ≤ H.condN.factorization l → (H.imgOne (ordCompl[l] H.condN * l ^ j) = ⊥ ↔ H.condE.factorization l ≤ j) ∧ (j ≤ H.condE.factorization l → Nat.card (H.imgOne (ordCompl[l] H.condN * l ^ j)) ∣ (l ^ H.condE.factorization l).totient / (l ^ j).totient) ∧ H.condE.factorization l ≤ H.condN.factorization l := by
  intro φ H l j hl hj
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  obtain ⟨hE, hEpos, hspec⟩ := condE_spec H
  have hEN : H.condE.factorization l ≤ H.condN.factorization l :=
    (Nat.factorization_le_iff_dvd hEpos.ne' hN).2 hE l
  have part1 : ∀ k, k ≤ H.condN.factorization l →
      (H.imgOne (ordCompl[l] H.condN * l ^ k) = ⊥ ↔ H.condE.factorization l ≤ k) := by
    intro k hk
    rw [hspec _ (layer_dvd hk)]
    exact dvd_layer_iff hl hN hE
  refine ⟨part1 j hj, fun hje => ?_, hEN⟩
  set e := H.condE.factorization l with he
  have hdiv : ordCompl[l] H.condN * l ^ j ∣ ordCompl[l] H.condN * l ^ e :=
    mul_dvd_mul_left _ (pow_dvd_pow l hje)
  have hc := card_imgOne_dvd H hdiv (layer_dvd hEN)
  rw [(part1 e hEN).2 le_rfl, Subgroup.card_bot, one_mul] at hc
  have hcop : ∀ k, (ordCompl[l] H.condN).Coprime (l ^ k) := fun k =>
    ((Nat.coprime_ordCompl hl hN).pow_left k).symm
  have hM : 0 < ordCompl[l] H.condN := Nat.ordCompl_pos l hN
  rw [Nat.totient_mul (hcop e), Nat.totient_mul (hcop j),
    Nat.mul_div_mul_left _ _ (Nat.totient_pos.2 hM)] at hc
  exact hc
end
