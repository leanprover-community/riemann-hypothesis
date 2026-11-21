import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCongruentLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Matrix

namespace GlobalTheory.AdaptCongr

open GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.UnRep.Move

theorem trivAt_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {Λ : GenLat E n} {a b : ℕ}
    (ha : Λ.TrivAt a) (hb : Λ.TrivAt b) : Λ.TrivAt (a * b) := by
  obtain ⟨k, hk, h1, h2⟩ := ha
  obtain ⟨m, hm, h3, h4⟩ := hb
  have hg : Ideal.span {((Nat.gcd k m : ℕ) : 𝓞 E)} ≤ Ideal.span {(k : 𝓞 E)} ⊔ Ideal.span {(m : 𝓞 E)} := by
    rw [Ideal.span_singleton_le_iff_mem]
    have e : ((Nat.gcd k m : ℕ) : 𝓞 E) = (k : 𝓞 E) * (Nat.gcdA k m : ℤ) + (m : 𝓞 E) * (Nat.gcdB k m : ℤ) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) (Nat.gcd_eq_gcd_ab k m)
      push_cast at this
      exact this
    rw [e]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  refine ⟨Nat.gcd k m, (hk.coprime_dvd_left (Nat.gcd_dvd_left _ _)).mul_right
    (hm.coprime_dvd_left (Nat.gcd_dvd_right _ _)), ?_, ?_⟩
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h1 h3
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h2 h4

theorem exists_move_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n M bad : ℕ) (Λ : GenLat E n), 0 < M → 0 < bad → Λ.Unimod → Λ.TrivAt M → ∃ (γ : GL (Fin n) E) (Λ' : GenLat E n), IsUnE (IsCMField.complexConj E) 1 γ.1 ∧ CongAt (stdLat E n) M M γ.1 ∧ (∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La) ∧ Λ'.Unimod ∧ ∃ s : 𝓞 E, s ≠ 0 ∧ Ideal.span {s} • Λ'.La ≤ stdLat E n ∧ Ideal.span {s} • stdLat E n ≤ Λ'.La ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P ∧ ((bad * M : ℕ) : 𝓞 E) ∉ P) ∧ ∃ k : ℕ, k.Coprime (bad * M) ∧ Ideal.span {(k : 𝓞 E)} • Λ'.La ≤ stdLat E n ∧ Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ'.La := by
  intro E _ _ _ H n M bad Λ hM hbad hU hT
  obtain ⟨hherm, hrk, hfg, hsp, -, -, hmov, hun⟩ := GlobalTheory.T.standardHermitianForm_hostField_inhabitant E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.T.exists_adelic_unitary_translate_standardLattice E H n M Λ hM hU hT
  obtain ⟨γ, hγ, ⟨t₁, ht₁, hc₁⟩, s, ⟨hs0, hs⟩, hint⟩ := GlobalTheory.T.exists_rational_unitary_split_denominator (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g (bad * M) hg (Nat.mul_pos hbad hM)
  obtain ⟨t₂, ht₂, hc₂⟩ := hgc M hM
  have hrat := (hat_rational_points_and_approx (maximalRealSubfield E) E n (stdLat E n) hfg hsp).1
  have hmem : ∀ v, v ∈ Λ.La ↔ ∃ z ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)),
      g.1 *ᵥ z = fv (maximalRealSubfield E) v := by
    intro v
    rw [← SetLike.mem_coe, hΛ]
    rfl
  have hinv : ∀ v : Fin n → E, (γ⁻¹).1 *ᵥ (γ.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin n → E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  let Λ' : GenLat E n := ⟨Λ.La.comap ((Matrix.mulVecLin (γ⁻¹).1).restrictScalars (𝓞 E))⟩
  have hΛ' : ∀ v, v ∈ Λ'.La ↔ (γ⁻¹).1 *ᵥ v ∈ Λ.La := fun v => Iff.rfl
  have hmove : ∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La := fun v => by rw [hΛ', hinv]
  have hsE : ∀ v : Fin n → E, s • v = (s : E) • v := fun v => rfl
  have h1 : ∀ v ∈ Λ'.La, s • v ∈ stdLat E n := by
    intro v hv
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 ((hΛ' v).1 hv)
    have := (hint z hz).1
    rw [← Matrix.mulVec_mulVec, hzv, ← fv_mulVec, hinv', ← fv_smul] at this
    rw [hsE]
    exact (hrat _).1 this
  have h2 : ∀ v ∈ stdLat E n, s • v ∈ Λ'.La := by
    intro v hv
    have := (hint _ ((hrat v).2 hv)).2
    rw [hΛ', hmem]
    refine ⟨_, this, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul, ← fv_mulVec, ← fv_smul, hsE, Matrix.mulVec_smul]
  obtain ⟨k, hk, hsk⟩ := exists_nat_coprime s (bad * M) fun P hP hsP => (hs P hP hsP).2
  refine ⟨γ, Λ', hγ, ?_, hmove, unimod_move γ hγ Λ Λ' hmove hU, s, hs0, (span_smul_le _ _ _).2 h1,
    (span_smul_le _ _ _).2 h2, fun P hP hsP => ⟨(hmov P hP).1 (hs P hP hsP).1, (hs P hP hsP).2⟩, k, hk,
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h1 v hv),
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h2 v hv)⟩
  · obtain ⟨j, hj, -, hj2⟩ := hT
    refine ⟨t₁ * t₂ * j, (ht₁.coprime_mul_left_right.mul_left ht₂).mul_left hj, fun v hv => ?_⟩
    have hjv : j • v ∈ Λ.La := by
      have := (span_smul_le _ _ _).1 hj2 v hv
      rwa [Nat.cast_smul_eq_nsmul] at this
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 hjv
    obtain ⟨w₁, hw₁, e₁⟩ := hc₁ z hz
    obtain ⟨w₂, hw₂, e₂⟩ := hc₂ z hz
    have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (t₁ * t₂ * j) • (γ.1 *ᵥ v - v) = M • ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v))) := by
      rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
    refine ⟨_, ?_, key⟩
    rw [← hrat]
    have e : fv (maximalRealSubfield E) ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v)))
        = (t₂ * bad) • w₁ - t₁ • w₂ := by
      refine nsmul_cancel _ hM ?_
      rw [← cap_fv_nsmul, ← key, mul_smul, smul_sub j, ← Matrix.mulVec_smul, cap_fv_nsmul, fv_sub, fv_mulVec,
        ← hzv, Matrix.mulVec_mulVec]
      have a1 : M • ((t₂ * bad) • w₁) = t₂ • ((bad * M) • w₁) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      have a2 : M • (t₁ • w₂) = t₁ • (M • w₂) := smul_comm _ _ _
      rw [smul_sub M, a1, a2, ← e₁, ← e₂, smul_smul, smul_smul, mul_comm t₂ t₁, ← smul_sub, sub_sub_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem hw₁ _) (nsmul_mem hw₂ _)

theorem not_mem_of_coprime {R : Type} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) {a b : ℕ} (h : a.Coprime b)
    (hb : (b : R) ∈ I) : (a : R) ∉ I := fun ha => by
  obtain ⟨u, v, huv⟩ := (Nat.Coprime.cast (R := R) h)
  exact hI ((Ideal.eq_top_iff_one _).2 (huv ▸ I.add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)))


end GlobalTheory.AdaptCongr
