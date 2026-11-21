import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionRingFrobeniusAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrExtensionEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompleteDvrPrimitiveRoot
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_frobenius_lift : ∀ (E : Type) [Field E] [NumberField E] (p n : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → φ ^ n = 1 → ∃ (W Qq : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field Qq) (_ : Algebra W Qq) (i : E →+* Qq) (σ : Qq ≃+* Qq), IsFractionRing W Qq ∧ Irreducible (p : W) ∧ Nat.card (W ⧸ Ideal.span {(p : W)}) = Nat.card (𝓞 E ⧸ Q.asIdeal) ∧ IsAdicComplete (Ideal.span {(p : W)}) W ∧ (∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) ∧ σ ^ n = 1 ∧ (∀ x : E, σ (i x) = i (φ x)) ∧ (∀ x : E, Formalism.L2.Col.IntAt Q x ↔ i x ∈ Set.range (algebraMap W Qq)) ∧ ∀ (y : W) (k : ℕ), ∃ (x : 𝓞 E) (z : W), i (x : E) = algebraMap W Qq (y + (p : W) ^ k * z) := by
  first | exact @GlobalTheory.UnramCompletion.exists_completion_frobenius | exact GlobalTheory.UnramCompletion.exists_completion_frobenius | (intros; apply GlobalTheory.UnramCompletion.exists_completion_frobenius <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_embedding : ∀ (W Qq E K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [Field E] [Field K] [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : W), ∃ (O Kf : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Field Kf) (_ : Algebra O Kf) (ι : Qq →+* Kf) (j : W →+* O) (w : O) (eK : K →+* Kf), IsFractionRing O Kf ∧ (∀ x : W, ι (algebraMap W Qq x) = algebraMap O Kf (j x)) ∧ j.Finite ∧ IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ w ^ 2 = j a ∧ ∀ x : E, eK (e x) = ι (i x) := by
  first | exact @GlobalTheory.exists_complete_dvr_ext_numberField_sqrt | exact GlobalTheory.exists_complete_dvr_ext_numberField_sqrt | (intros; apply GlobalTheory.exists_complete_dvr_ext_numberField_sqrt <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

open scoped Pointwise

namespace GlobalTheory.UnramifiedFrobenius

theorem exists_frobenius : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ), p.Prime → Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) → ∃ (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 ∧ (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) = p ^ orderOf φ ∧ (∀ g : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, g • x ∈ Q.asIdeal ↔ x ∈ Q.asIdeal) ↔ g ∈ Subgroup.zpowers φ) ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ Q'.asIdeal → ∃ g : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, x ∈ Q'.asIdeal ↔ g • x ∈ Q.asIdeal := by
  intro E _ _ _ p hp hunr
  have : Fact p.Prime := ⟨hp⟩
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).2 hpz
  have hover : ∀ R : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ R.asIdeal →
      R.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := fun R hR =>
    (Ideal.liesOver_span_iff R.isPrime.ne_top hpz).mpr (by simpa using hR)
  obtain ⟨Q, hQ⟩ := GlobalTheory.CyclotomicCompletion.exists_place_above E hp
  have := Q.isPrime
  have hQo := hover Q hQ
  have : Finite (𝓞 E ⧸ Q.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  obtain ⟨φ, hφ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) Q.asIdeal
  have he : Q.asIdeal.ramificationIdx ℤ = 1 := hunr.ramificationIdx_eq_one hQo
  have hin : Nat.card (Q.asIdeal.inertia (E ≃ₐ[ℚ] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (Ideal.span {(p : ℤ)}) Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) Q.asIdeal (E ≃ₐ[ℚ] E), he]
  have hbot : Q.asIdeal.inertia (E ≃ₐ[ℚ] E) = ⊥ := Subgroup.eq_bot_of_card_eq _ hin
  have hstab : MulAction.stabilizer (E ≃ₐ[ℚ] E) Q.asIdeal = Subgroup.zpowers φ := by
    refine le_antisymm (fun σ hσ => ?_) (Subgroup.zpowers_le.2 hφ.mem_stabilizer)
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul p Q.asIdeal φ σ hφ hσ
    have h1 : ρ ∈ Q.asIdeal.inertia (E ≃ₐ[ℚ] E) := hρ
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, one_mul]
    exact Subgroup.npow_mem_zpowers φ k
  refine ⟨Q, φ, hQ, ?_, ?_, ?_, ?_, ?_⟩
  · intro h2
    have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) =
        Ideal.span {((p : ℕ) : 𝓞 E)} := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) Q.asIdeal
      (by simpa using hp.ne_zero)] at he
    refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · rw [hmap]; exact (Ideal.span_singleton_le_iff_mem _).2 hQ
    · rw [hmap]; exact (Ideal.span_singleton_le_iff_mem _).2 h2
  · intro x
    have h1 := hφ x
    rw [Formalism.TwoAdicCyclotomicDecomposition.odd_card_under p Q.asIdeal] at h1
    exact h1
  · have h1 := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := E ≃ₐ[ℚ] E)
      (Ideal.span {(p : ℤ)}) Q.asIdeal
    rw [hin, one_mul, hstab, Nat.card_zpowers] at h1
    rw [h1, Ideal.pow_inertiaDeg p Q.asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro g
    rw [← hstab]
    exact ⟨Formalism.FrobeniusOrbits.Decomp.mem_stab_of g Q.asIdeal,
      Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab g Q.asIdeal⟩
  · intro Q' hQ'
    have := Q'.isPrime
    have := hover Q' hQ'
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) Q'.asIdeal
      Q.asIdeal (E ≃ₐ[ℚ] E)
    refine ⟨g, fun x => ?_⟩
    rw [← hg]
    exact Ideal.smul_mem_pointwise_smul_iff.symm

end GlobalTheory.UnramifiedFrobenius
end

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_decomposition_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ), p.Prime → Algebra.IsUnramifiedIn (𝓞 E) (Ideal.span {(p : ℤ)}) → ∃ (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 ∧ (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) = p ^ orderOf φ ∧ (∀ g : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, g • x ∈ Q.asIdeal ↔ x ∈ Q.asIdeal) ↔ g ∈ Subgroup.zpowers φ) ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ Q'.asIdeal → ∃ g : E ≃ₐ[ℚ] E, ∀ x : 𝓞 E, x ∈ Q'.asIdeal ↔ g • x ∈ Q.asIdeal := by
  atlas_forward_decl GlobalTheory.UnramifiedFrobenius.exists_frobenius
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem frobenius_moves_quadratic_subfield_of_inert :
    ∀ (E : Type) [Field E] [NumberField E] (M : Subfield E) (p : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → Module.finrank ℚ M = 2 → (Ideal.span {((p : ℕ) : 𝓞 M)}).IsPrime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → ∃ x ∈ M, φ x ≠ x := by
  intro E _ _ M p Q φ hp hM hP hQ hφ
  by_contra h
  push_neg at h
  haveI : FiniteDimensional ℚ M := Module.finite_of_finrank_pos (by omega)
  haveI : NumberField M := {}
  let f : 𝓞 M →+* 𝓞 E := RingOfIntegers.mapRingHom M.subtype
  have hp0 : ((p : ℕ) : 𝓞 M) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hcard : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 M)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hM]
  set P : Ideal (𝓞 M) := Ideal.span {((p : ℕ) : 𝓞 M)} with hPdef
  have hne : P ≠ ⊥ := by
    rw [hPdef, Ne, Ideal.span_singleton_eq_bot]; exact hp0
  have hmax : P.IsMaximal := hP.isMaximal hne
  have hcom : P = Q.asIdeal.comap f := by
    refine hmax.eq_of_le (Ideal.comap_ne_top f Q.isPrime.ne_top) ?_
    rw [hPdef, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hQ
  have key : ∀ x : 𝓞 M ⧸ P, x ^ p = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, eq_comm, Ideal.Quotient.eq, hcom, Ideal.mem_comap, map_sub, map_pow]
    have h1 : φ • f y = f y := by
      apply Subtype.ext
      exact h _ (y : M).2
    have h2 := hφ (f y)
    rwa [h1] at h2
  haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  letI : Fintype (𝓞 M ⧸ P) := Fintype.ofFinite _
  haveI : IsDomain (𝓞 M ⧸ P) := Ideal.Quotient.isDomain P
  have hc : Fintype.card (𝓞 M ⧸ P) = p ^ 2 := by
    rw [← hcard, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  classical
  have h1 : 1 < p := hp.one_lt
  have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 M ⧸ P)).natDegree = p := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [h1]
  have hnz : (Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 M ⧸ P)) ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
    omega
  have hle : (Finset.univ : Finset (𝓞 M ⧸ P)).card ≤ p := by
    refine le_trans ?_ hdeg.le
    apply Polynomial.card_le_degree_of_subset_roots
    intro x _
    rw [Polynomial.mem_roots hnz]
    simp [key x]
  rw [Finset.card_univ, hc] at hle
  nlinarith

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_nontrivial_on_inert_quadratic : ∀ (E : Type) [Field E] [NumberField E] (M : Subfield E) (p : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → Module.finrank ℚ M = 2 → (Ideal.span {((p : ℕ) : 𝓞 M)}).IsPrime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → ∃ x ∈ M, φ x ≠ x := by
  atlas_forward_decl GlobalTheory.frobenius_moves_quadratic_subfield_of_inert
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem pow_mem_iff_even_of_index_two_notMem {G : Type} [Group G] (H : Subgroup G) (hH : H.index = 2)
    (a : G) (ha : a ∉ H) (k : ℕ) : a ^ k ∈ H ↔ Even k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Subgroup.mul_mem_iff_of_index_two hH, Nat.even_add_one, ih]
    simp [ha]

theorem frobenius_orbit_positions_comm (G : Type) [CommGroup G] [Finite G] (H : Subgroup G) (φ c : G)
    (hH : H.index = 2) (hφ : φ ∉ H) (hc : c ∉ H) (hcc : c * c = 1) (hcZ : c ∉ Subgroup.zpowers φ) :
    2 ≤ orderOf φ ∧ Even (orderOf φ) ∧ ∃ (N : ℕ) (g : Fin N → G) (pos : (Σ _ : Fin N, Fin (orderOf φ)) ≃ H), 0 < N ∧ (∀ v s, (pos ⟨v, s⟩ : G) = φ ^ s.val * g v * c ^ s.val) ∧ (∀ v v', g v' * (g v)⁻¹ ∈ Subgroup.zpowers φ → v = v') ∧ (∀ v v', g v' * c * (g v)⁻¹ ∉ Subgroup.zpowers φ) ∧ ∀ x : G, ∃ v, g v * x⁻¹ ∈ Subgroup.zpowers φ ∨ g v * c * x⁻¹ ∈ Subgroup.zpowers φ := by
  classical
  have hφk := pow_mem_iff_even_of_index_two_notMem H hH φ hφ
  have hck := pow_mem_iff_even_of_index_two_notMem H hH c hc
  have hev : Even (orderOf φ) := (hφk _).1 (by rw [pow_orderOf_eq_one]; exact H.one_mem)
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hce : ∀ k : ℕ, Even k → c ^ k = 1 := by
    rintro k ⟨m, rfl⟩
    rw [pow_add, ← mul_pow, hcc, one_pow]
  have hco : ∀ k : ℕ, ¬ Even k → c ^ k = c := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.1 hk
    rw [pow_succ, hce _ (even_two_mul m), one_mul]
  refine ⟨by obtain ⟨m, hm⟩ := hev; omega, hev, ?_⟩
  set Z := Subgroup.zpowers φ with hZ
  let D : Subgroup G := Z ⊔ Subgroup.zpowers c
  have hZD : Z ≤ D := le_sup_left
  have hcD : c ∈ D := (le_sup_right : Subgroup.zpowers c ≤ D) (Subgroup.mem_zpowers c)
  have hφD : φ ∈ D := hZD (Subgroup.mem_zpowers φ)
  have hD : ∀ x ∈ D, x ∈ Z ∨ x * c ∈ Z := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hz : z ∈ Submonoid.powers c)
    by_cases hk : Even k
    · left; simpa [hce k hk] using hy
    · right; simpa [hco k hk, mul_assoc, hcc] using hy
  have hZpow : ∀ x ∈ Z, ∃ s : Fin (orderOf φ), φ ^ s.val = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hx : x ∈ Submonoid.powers φ)
    exact ⟨⟨k % orderOf φ, Nat.mod_lt _ hpos⟩, pow_mod_orderOf φ k⟩
  have hr : ∀ q : G ⧸ D, ∃ a : G, a ∈ H ∧ (a : G ⧸ D) = q := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    by_cases ha : a ∈ H
    · exact ⟨a, ha, rfl⟩
    · refine ⟨a * c, ?_, ?_⟩
      · rw [Subgroup.mul_mem_iff_of_index_two hH]; simp [ha, hc]
      · exact QuotientGroup.mk_mul_of_mem a hcD
  choose r hrH hrq using hr
  let e : Fin (Nat.card (G ⧸ D)) ≃ G ⧸ D := (Finite.equivFin (G ⧸ D)).symm
  let g : Fin (Nat.card (G ⧸ D)) → G := fun v => r (e v)
  have hgH : ∀ v, g v ∈ H := fun v => hrH _
  have key : ∀ v v', g v' * (g v)⁻¹ ∈ D → v = v' := by
    intro v v' h
    apply e.injective
    rw [← hrq (e v), ← hrq (e v'), QuotientGroup.eq, mul_comm]
    exact h
  have cover : ∀ x : G, ∃ v, g v * x⁻¹ ∈ D := by
    intro x
    refine ⟨e.symm (x : G ⧸ D), ?_⟩
    have h := hrq (x : G ⧸ D)
    rw [eq_comm, QuotientGroup.eq, mul_comm] at h
    simpa [g] using h
  let f : (Σ _ : Fin (Nat.card (G ⧸ D)), Fin (orderOf φ)) → H := fun p =>
    ⟨φ ^ p.2.val * g p.1 * c ^ p.2.val, by
      rw [Subgroup.mul_mem_iff_of_index_two hH, H.mul_mem_cancel_right (hgH _), hφk, hck]⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v, s⟩ ⟨v', t⟩ h
      have h' : φ ^ s.val * g v * c ^ s.val = φ ^ t.val * g v' * c ^ t.val := congrArg Subtype.val h
      have hv : v = v' := by
        apply key
        have : g v' * (g v)⁻¹ = φ ^ s.val * c ^ s.val * (φ ^ t.val * c ^ t.val)⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
          calc g v' * (φ ^ t.val * c ^ t.val) = φ ^ t.val * g v' * c ^ t.val := by ac_rfl
            _ = φ ^ s.val * g v * c ^ s.val := h'.symm
            _ = _ := by ac_rfl
        rw [this]
        exact D.mul_mem (D.mul_mem (D.pow_mem hφD _) (D.pow_mem hcD _))
          (D.inv_mem (D.mul_mem (D.pow_mem hφD _) (D.pow_mem hcD _)))
      subst hv
      have h2 : φ ^ s.val * c ^ s.val = φ ^ t.val * c ^ t.val := by
        apply mul_left_cancel (a := g v)
        calc g v * (φ ^ s.val * c ^ s.val) = φ ^ s.val * g v * c ^ s.val := by ac_rfl
          _ = φ ^ t.val * g v * c ^ t.val := h'
          _ = _ := by ac_rfl
      have hZp : ∀ k : ℕ, φ ^ k ∈ Z := fun k => Z.pow_mem (Subgroup.mem_zpowers φ) k
      have h3 : φ ^ s.val = φ ^ t.val := by
        by_cases hs : Even s.val <;> by_cases ht : Even t.val
        · simpa [hce _ hs, hce _ ht] using h2
        · exfalso
          rw [hce _ hs, hco _ ht, mul_one] at h2
          exact hcZ ((Z.mul_mem_cancel_left (hZp t.val)).1 (h2 ▸ hZp s.val))
        · exfalso
          rw [hco _ hs, hce _ ht, mul_one] at h2
          exact hcZ ((Z.mul_mem_cancel_left (hZp s.val)).1 (h2 ▸ hZp t.val))
        · rw [hco _ hs, hco _ ht] at h2
          exact mul_right_cancel h2
      have h4 : s = t := Fin.ext (pow_injOn_Iio_orderOf s.2 t.2 h3)
      subst h4
      rfl
    · rintro ⟨h, hh⟩
      obtain ⟨v, hv⟩ := cover h
      have hv' : h * (g v)⁻¹ ∈ D := by
        have := D.inv_mem hv
        rwa [mul_inv_rev, inv_inv] at this
      have hH' : h * (g v)⁻¹ ∈ H := H.mul_mem hh (H.inv_mem (hgH v))
      rcases hD _ hv' with h1 | h1
      · obtain ⟨s, hs⟩ := hZpow _ h1
        refine ⟨⟨v, s⟩, Subtype.ext ?_⟩
        have hes : Even s.val := (hφk _).1 (hs ▸ hH')
        show φ ^ s.val * g v * c ^ s.val = h
        rw [hce _ hes, hs]; simp
      · obtain ⟨s, hs⟩ := hZpow _ h1
        refine ⟨⟨v, s⟩, Subtype.ext ?_⟩
        have hes : ¬ Even s.val := by
          rw [← hφk, hs, H.mul_mem_cancel_left hH']; exact hc
        show φ ^ s.val * g v * c ^ s.val = h
        rw [hco _ hes, hs]
        calc h * (g v)⁻¹ * c * g v * c = h * ((g v)⁻¹ * g v) * (c * c) := by ac_rfl
          _ = h := by simp [hcc]
  refine ⟨Nat.card (G ⧸ D), g, Equiv.ofBijective f hf, Nat.card_pos, fun v s => rfl,
    fun v v' h => key v v' (hZD h), ?_, ?_⟩
  · intro v v' h
    have h1 : g v' * c * (g v)⁻¹ = g v' * (g v)⁻¹ * c := by ac_rfl
    rw [h1] at h
    have hv := key v v' ((D.mul_mem_cancel_right hcD).1 (hZD h))
    subst hv
    exact hcZ (by simpa using h)
  · intro x
    obtain ⟨v, hv⟩ := cover x
    refine ⟨v, (hD _ hv).imp id fun h => ?_⟩
    have h1 : g v * c * x⁻¹ = g v * x⁻¹ * c := by ac_rfl
    rwa [h1]

theorem frobenius_orbit_positions : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (φ c : G), (∀ a b : G, a * b = b * a) → H.index = 2 → φ ∉ H → c ∉ H → c * c = 1 → c ∉ Subgroup.zpowers φ → 2 ≤ orderOf φ ∧ Even (orderOf φ) ∧ ∃ (N : ℕ) (g : Fin N → G) (pos : (Σ _ : Fin N, Fin (orderOf φ)) ≃ H), 0 < N ∧ (∀ v s, (pos ⟨v, s⟩ : G) = φ ^ s.val * g v * c ^ s.val) ∧ (∀ v v', g v' * (g v)⁻¹ ∈ Subgroup.zpowers φ → v = v') ∧ (∀ v v', g v' * c * (g v)⁻¹ ∉ Subgroup.zpowers φ) ∧ ∀ x : G, ∃ v, g v * x⁻¹ ∈ Subgroup.zpowers φ ∨ g v * c * x⁻¹ ∈ Subgroup.zpowers φ := by
  intro G inst _ H φ c hcomm
  letI : CommGroup G := { inst with mul_comm := hcomm }
  exact frobenius_orbit_positions_comm G H φ c

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_decomposition_even_order : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (φ c : G), (∀ a b : G, a * b = b * a) → H.index = 2 → φ ∉ H → c ∉ H → c * c = 1 → c ∉ Subgroup.zpowers φ → 2 ≤ orderOf φ ∧ Even (orderOf φ) ∧ ∃ (N : ℕ) (g : Fin N → G) (pos : (Σ _ : Fin N, Fin (orderOf φ)) ≃ H), 0 < N ∧ (∀ v s, (pos ⟨v, s⟩ : G) = φ ^ s.val * g v * c ^ s.val) ∧ (∀ v v', g v' * (g v)⁻¹ ∈ Subgroup.zpowers φ → v = v') ∧ (∀ v v', g v' * c * (g v)⁻¹ ∉ Subgroup.zpowers φ) ∧ ∀ x : G, ∃ v, g v * x⁻¹ ∈ Subgroup.zpowers φ ∨ g v * c * x⁻¹ ∈ Subgroup.zpowers φ := by
  atlas_forward_decl GlobalTheory.frobenius_orbit_positions
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem exists_algEquiv_comp_of_normal_rat {E K : Type} [Field E] [Field K] [CharZero E] [CharZero K]
    [Normal ℚ E] (φ ψ : E →+* K) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ψ x = φ (g x) := by
  letI : Algebra E K := φ.toAlgebra
  haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  refine ⟨AlgHom.restrictNormal' ψ.toRatAlgHom E, fun x => ?_⟩
  have := AlgHom.restrictNormal_commutes ψ.toRatAlgHom E x
  exact this.symm

theorem cmType_equiv_fixingSubgroup : ∀ (X : Formalism.L2.Col.Fields), X.Core → IsGalois ℚ X.E → ∃ (τ₀ : X.Tau) (H : Subgroup (X.E ≃ₐ[ℚ] X.E)) (γ : H ≃ X.Tau) (c : X.E ≃ₐ[ℚ] X.E), H.index = 2 ∧ (∀ g ∈ H, ∀ x ∈ X.Kq, g x = x) ∧ (∀ (h : H) (x : X.E), X.emb (γ h) x = X.emb τ₀ (h.1 x)) ∧ (∀ x, c x = star x) ∧ c ∉ H := by
  intro X hX hG
  classical
  have hpos : 0 < Fintype.card X.Tau := by
    rw [hX.card_Tau]; exact Module.finrank_pos
  obtain ⟨τ₀⟩ := Fintype.card_pos_iff.1 hpos
  let L : IntermediateField ℚ X.E := X.Kq.toIntermediateField (fun q => by
    intro τ τ'
    simp)
  have hL : Module.finrank ℚ L = 2 := hX.quad
  let H : Subgroup (X.E ≃ₐ[ℚ] X.E) := L.fixingSubgroup
  have hH : ∀ g, g ∈ H ↔ ∀ x ∈ X.Kq, g x = x := fun g => IntermediateField.mem_fixingSubgroup_iff L g
  have hidx : H.index = 2 := by
    rw [← hL]; exact (IntermediateField.finrank_eq_fixingSubgroup_index X.E L).symm
  have hcardG : Nat.card (X.E ≃ₐ[ℚ] X.E) = Fintype.card X.Tau * 2 := by
    rw [IsGalois.card_aut_eq_finrank, hX.card_Tau, ← hX.rankE, Module.finrank_mul_finrank]
  have hcardH : Nat.card X.Tau = Nat.card H := by
    have := H.card_mul_index
    rw [hidx, hcardG] at this
    rw [Nat.card_eq_fintype_card]
    omega
  choose g hg using fun τ => exists_algEquiv_comp_of_normal_rat (X.emb τ₀) (X.emb τ)
  have hgH : ∀ τ, g τ ∈ H := fun τ => (hH _).2 fun x hx => by
    apply (X.emb τ₀).injective
    rw [← hg]
    exact hx τ τ₀
  let δ : X.Tau → H := fun τ => ⟨g τ, hgH τ⟩
  have hδ : Function.Injective δ := by
    intro τ τ' h
    have h' : g τ = g τ' := congrArg Subtype.val h
    apply hX.emb_inj
    ext x
    rw [hg, hg τ', h']
  have hbij : Function.Bijective δ :=
    (Nat.bijective_iff_injective_and_card δ).2 ⟨hδ, hcardH⟩
  let e : X.Tau ≃ H := Equiv.ofBijective δ hbij
  have hγ : ∀ (h : H) (x : X.E), X.emb (e.symm h) x = X.emb τ₀ (h.1 x) := by
    intro h x
    have : g (e.symm h) = h.1 := congrArg Subtype.val (e.apply_symm_apply h)
    rw [hg, this]
  let c : X.E ≃ₐ[ℚ] X.E := AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut X.E)) (fun q => by simp)
  have hc : ∀ x, c x = star x := fun x => rfl
  refine ⟨τ₀, H, e.symm, c, hidx, fun g hg => (hH g).1 hg, hγ, hc, fun hcH => ?_⟩
  apply hX.emb_ne (e.symm ⟨c, hcH⟩) τ₀
  ext x
  rw [hγ]
  rfl

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_index_two_cm_conjugation : ∀ (X : Formalism.L2.Col.Fields), X.Core → IsGalois ℚ X.E → ∃ (τ₀ : X.Tau) (H : Subgroup (X.E ≃ₐ[ℚ] X.E)) (γ : H ≃ X.Tau) (c : X.E ≃ₐ[ℚ] X.E), H.index = 2 ∧ (∀ g ∈ H, ∀ x ∈ X.Kq, g x = x) ∧ (∀ (h : H) (x : X.E), X.emb (γ h) x = X.emb τ₀ (h.1 x)) ∧ (∀ x, c x = star x) ∧ c ∉ H := by
  atlas_forward_decl GlobalTheory.cmType_equiv_fixingSubgroup
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.GO

def primeUnder {E : Type} [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) (Q : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 E) :=
  Q.comap (MulSemiringAction.toRingHom (E ≃ₐ[ℚ] E) (𝓞 E) g) fun x => ⟨g⁻¹ • x, by simp⟩

theorem mem_primeUnder {E : Type} [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    x ∈ (primeUnder g Q).asIdeal ↔ g • x ∈ Q.asIdeal := Iff.rfl



end GlobalTheory.GO
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.GO.EighthRoots

section Quartic

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (σ : E ≃ₐ[ℚ] E)

@[reducible] def quarticFields : Fields where
  F := maximalRealSubfield E
  E := E
  K := E
  starE := IsCMField.starRing E
  starK := IsCMField.starRing E
  Tau := Bool
  emb := fun b => if b then (σ : E →+* E) else RingHom.id E

def conj : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ

theorem conj_conj (x : E) : conj E (conj E x) = x := IsCMField.complexConj_apply_apply E x

theorem conj_ne_one : conj E ≠ 1 := fun h =>
  IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)

theorem mem_Kq (x : E) : x ∈ (quarticFields E σ).Kq ↔ σ x = x := by
  constructor
  · intro h
    exact h true false
  · intro h a b
    cases a <;> cases b
    · rfl
    · exact h.symm
    · exact h
    · rfl


end Quartic







end GlobalTheory.GO.EighthRoots
end
end

section
open NumberField IsDedekindDomain IsLocalRing Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

set_option linter.style.haveILetI false

noncomputable section

namespace GlobalTheory.GO.PlWitt

section Global

variable {E : Type} [Field E] [NumberField E]

def intAlg {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (f : A →+* B) : A →ₐ[ℤ] B :=
  { f with commutes' := fun r => RingHom.congr_fun (RingHom.ext_int (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)) r }

omit [NumberField E] in

theorem exists_intHom {O Kf : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] (ψ : E →+* Kf) : ∃ g : 𝓞 E →+* O, ∀ x : 𝓞 E, algebraMap O Kf (g x) = ψ x := by
  have h : ∀ x : 𝓞 E, ∃ y : O, algebraMap O Kf y = ψ x := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 ((x.isIntegral_coe.map ψ.toIntAlgHom).tower_top)
  choose g hg using h
  have hinj := IsFractionRing.injective O Kf
  exact ⟨{ toFun := g, map_one' := hinj (by simp [hg]), map_mul' := fun a b => hinj (by simp [hg]),
           map_zero' := hinj (by simp [hg]), map_add' := fun a b => hinj (by simp [hg]) }, hg⟩

omit [NumberField E] in

theorem eq_of_cong {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (Q : HeightOneSpectrum (𝓞 E))
    [Algebra.IsUnramifiedAt ℤ Q.asIdeal] (g g' : 𝓞 E →+* O) (hQ : ∀ x, x ∈ Q.asIdeal ↔ g x ∈ maximalIdeal O)
    (h : ∀ x, residue O (g x) = residue O (g' x)) : g = g' := by
  have hu : ∀ y : Q.asIdeal.primeCompl, IsUnit (g y) := fun y => by
    have := y.2
    rw [Ideal.mem_primeCompl_iff, hQ] at this
    simpa using this
  have hu' : ∀ y : Q.asIdeal.primeCompl, IsUnit (g' y) := fun y => by
    have := hu y
    rw [← residue_ne_zero_iff_isUnit] at this ⊢
    rwa [← h]
  let G : Localization.AtPrime Q.asIdeal →+* O := IsLocalization.lift hu
  let G' : Localization.AtPrime Q.asIdeal →+* O := IsLocalization.lift hu'
  have e : (residue O).comp G = (residue O).comp G' :=
    IsLocalization.ringHom_ext Q.asIdeal.primeCompl (RingHom.ext fun x => by simp [G, G', h])
  have := Algebra.FormallyUnramified.ext_of_iInf (R := ℤ) (maximalIdeal O)
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top)
    (g₁ := intAlg G) (g₂ := intAlg G') fun x => RingHom.congr_fun e x
  refine RingHom.ext fun x => ?_
  have h2 : G (algebraMap _ _ x) = G' (algebraMap _ _ x) := AlgHom.congr_fun this (algebraMap _ _ x)
  simpa [G, G'] using h2

theorem exists_wittHom (p : ℕ) [Fact p.Prime] (Q : HeightOneSpectrum (𝓞 E)) (hp : (p : 𝓞 E) ∈ Q.asIdeal)
    [Algebra.IsUnramifiedAt ℤ Q.asIdeal] :
    ∃ (n : ℕ) (g : 𝓞 E →+* WittVector p (GaloisField p n)), n ≠ 0 ∧
      Function.Surjective (fun x => WittVector.constantCoeff (g x)) ∧
      ∀ x, x ∈ Q.asIdeal ↔ WittVector.constantCoeff (g x) = 0 := by
  haveI := Q.isMaximal
  letI : Field (𝓞 E ⧸ Q.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ Q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.ne_bot
  letI : Fintype (𝓞 E ⧸ Q.asIdeal) := Fintype.ofFinite _
  haveI : CharP (𝓞 E ⧸ Q.asIdeal) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast (Ideal.Quotient.mk Q.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hp)
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ Q.asIdeal) p
  letI : Algebra (ZMod p) (𝓞 E ⧸ Q.asIdeal) := ZMod.algebra _ p
  let e := GaloisField.algEquivGaloisFieldOfFintype p n hn
  let W := WittVector p (GaloisField p n)
  let f : 𝓞 E →+* GaloisField p n := e.toRingEquiv.toRingHom.comp (Ideal.Quotient.mk Q.asIdeal)
  have hf : ∀ x, x ∈ Q.asIdeal ↔ f x = 0 := fun x => by
    simp [f, Ideal.Quotient.eq_zero_iff_mem]
  have hu : ∀ y : Q.asIdeal.primeCompl, IsUnit (f y) := fun y => by
    have := y.2
    rw [Ideal.mem_primeCompl_iff, hf] at this
    exact IsUnit.mk0 _ this
  haveI : Algebra.FinitePresentation ℤ (𝓞 E) := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI : Algebra.IsEtaleAt ℤ Q.asIdeal := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat _
  let F : Localization.AtPrime Q.asIdeal →+* W ⧸ Ideal.span {(p : W)} :=
    (WittVector.quotientPEquiv (p := p) (k := GaloisField p n)).symm.toRingHom.comp (IsLocalization.lift hu)
  obtain ⟨G, hG⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (R := ℤ) (intAlg F)
  have key : ∀ x : 𝓞 E, WittVector.constantCoeff (G (algebraMap _ _ x)) = f x := fun x => by
    have h1 : Ideal.Quotient.mk _ (G (algebraMap _ _ x)) = F (algebraMap _ _ x) := AlgHom.congr_fun hG _
    have h2 := congrArg (WittVector.quotientPEquiv (p := p) (k := GaloisField p n)) h1
    have h3 : WittVector.quotientPEquiv (Ideal.Quotient.mk _ (G (algebraMap _ _ x))) = f x := by simpa [F] using h2
    exact h3
  refine ⟨n, G.toRingHom.comp (algebraMap _ _), n.ne_zero, fun y => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := (e.surjective.comp Ideal.Quotient.mk_surjective) y
    exact ⟨x, (key x).trans hx⟩
  · exact (hf x).trans (by rw [← key]; rfl)

theorem exists_frob_pow (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) {Ω : Type} [Field Ω] (a b : GaloisField p n →+* Ω) :
    (∃ s < n, ∀ x, b x = a (x ^ p ^ s)) := by
  haveI : CharP Ω p := charP_of_injective_ringHom a.injective p
  letI : Algebra (ZMod p) Ω := ZMod.algebra _ p
  let al : (GaloisField p n →+* Ω) → (GaloisField p n →ₐ[ZMod p] Ω) := fun c =>
    { c with commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod (c.comp (algebraMap _ _)) (algebraMap _ _)) r }
  have hb := FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (GaloisField p n)
  let u : Fin (Module.finrank (ZMod p) (GaloisField p n)) → (GaloisField p n →ₐ[ZMod p] Ω) := fun s =>
    (al a).comp (FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p n) ^ s.val)
  have hu : Function.Injective u := fun s t h => hb.1 (AlgHom.ext fun x => a.injective (AlgHom.congr_fun h x))
  have hs : Function.Surjective u := (hu.bijective_of_nat_card_le (by
    simpa using card_algHom_le_finrank (ZMod p) (GaloisField p n) Ω)).2
  obtain ⟨s, hs⟩ := hs (al b)
  refine ⟨s, by simpa [GaloisField.finrank p hn] using s.2, fun x => ?_⟩
  have := AlgHom.congr_fun hs x
  refine this.symm.trans (congrArg a ?_)
  simp [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom]

theorem frob_pow_inj (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) {s t : ℕ} (hs : s < n) (ht : t < n)
    (h : ∀ x : GaloisField p n, x ^ p ^ s = x ^ p ^ t) : s = t := by
  have hb := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) (GaloisField p n)).1
  have := @hb ⟨s, by rwa [GaloisField.finrank p hn]⟩ ⟨t, by rwa [GaloisField.finrank p hn]⟩ (AlgHom.ext fun x => by
    simpa [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom] using h x)
  exact congrArg Fin.val this

end Global

section Local

variable {E : Type} [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime]

abbrev Wn (n : ℕ) : Type := WittVector p (GaloisField p n)

abbrev Qn (n : ℕ) : Type := FractionRing (Wn p n)

abbrev Fr (n : ℕ) : Qn p n ≃+* Qn p n := WittVector.FractionRing.frobenius p (GaloisField p n)

variable {p} {n : ℕ}

theorem cc_eq_zero (x : Wn p n) : WittVector.constantCoeff x = 0 ↔ (p : Wn p n) ∣ x := by
  rw [← RingHom.mem_ker, WittVector.ker_constantCoeff, Ideal.mem_span_singleton]

theorem isUnit_of_cc {x : Wn p n} (h : WittVector.constantCoeff x ≠ 0) : IsUnit x :=
  WittVector.isUnit_of_coeff_zero_ne_zero _ h

theorem fr_pow (s : ℕ) (x : Wn p n) : ∃ y : Wn p n, (Fr p n ^ s) (algebraMap _ _ x) = algebraMap _ _ y ∧
    WittVector.constantCoeff y = WittVector.constantCoeff x ^ p ^ s := by
  induction s with
  | zero => exact ⟨x, rfl, by simp⟩
  | succ s ih =>
    obtain ⟨y, h, hy⟩ := ih
    refine ⟨WittVector.frobenius y, ?_, ?_⟩
    · rw [pow_succ', RingAut.mul_apply, h, SqrtUnif.fractionRing_frobenius_algebraMap]
    · rw [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP, ← WittVector.constantCoeff_apply, hy,
        ← pow_mul, pow_succ]

def Good (Q : HeightOneSpectrum (𝓞 E)) (i : E →+* Qn p n) : Prop :=
  ∃ g : 𝓞 E →+* Wn p n, (∀ x : 𝓞 E, i x = algebraMap _ _ (g x)) ∧
    Function.Surjective (fun x => WittVector.constantCoeff (g x)) ∧
    ∀ x, x ∈ Q.asIdeal ↔ WittVector.constantCoeff (g x) = 0

theorem exists_good (Q : HeightOneSpectrum (𝓞 E)) (hQ : (p : 𝓞 E) ∈ Q.asIdeal) [Algebra.IsUnramifiedAt ℤ Q.asIdeal] :
    ∃ (n : ℕ) (i : E →+* Qn p n), n ≠ 0 ∧ Good Q i := by
  obtain ⟨n, g, hn, hs, hk⟩ := exists_wittHom p Q hQ
  have hg : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    have hm := (RingHom.ker_isPrime g).isMaximal h
    have := hm.eq_of_le Q.isPrime.ne_top fun x hx => (hk x).2 (by rw [(RingHom.mem_ker).1 hx, map_zero])
    rw [← this, RingHom.mem_ker, map_natCast] at hQ
    exact (WittVector.irreducible p (k := GaloisField p n)).ne_zero hQ
  have hg' : Function.Injective ((algebraMap (Wn p n) (Qn p n)).comp g) := (IsFractionRing.injective _ _).comp hg
  exact ⟨n, IsFractionRing.lift hg', hn, g, fun x => IsFractionRing.lift_algebraMap hg' x, hs, hk⟩

variable {Q : HeightOneSpectrum (𝓞 E)} {i : E →+* Qn p n}

omit [NumberField E] in
theorem Good.twist (h : Good Q i) : Good Q ((Fr p n).toRingHom.comp i) := by
  obtain ⟨g, hg, hs, hk⟩ := h
  have e : ∀ x : Wn p n, WittVector.constantCoeff (WittVector.frobenius x) = frobenius _ p (WittVector.constantCoeff x) :=
    fun x => WittVector.coeff_frobenius_charP p x 0
  refine ⟨WittVector.frobenius.comp g, fun x => ?_, fun y => ?_, fun x => ?_⟩
  · exact (congrArg (Fr p n) (hg x)).trans (SqrtUnif.fractionRing_frobenius_algebraMap p _)
  · obtain ⟨x, hx⟩ := ((surjective_frobenius (GaloisField p n) p).comp hs) y
    exact ⟨x, (e _).trans hx⟩
  · rw [hk, RingHom.comp_apply, e, map_eq_zero (frobenius (GaloisField p n) p)]

theorem Good.intAt (h : Good Q i) (x : E) : IntAt Q x ↔ i x ∈ Set.range (algebraMap (Wn p n) (Qn p n)) := by
  obtain ⟨g, hg, hs, hk⟩ := h
  have hinj := IsFractionRing.injective (Wn p n) (Qn p n)
  have H : ∀ x : E, ∀ r s : 𝓞 E, s ∉ Q.asIdeal → (s : E) * x = r →
      ∃ u : (Wn p n)ˣ, i x = algebraMap _ _ (g r * u) := fun x r s hs h => by
    obtain ⟨u, hu⟩ := isUnit_of_cc (mt (hk s).2 hs)
    refine ⟨u⁻¹, ?_⟩
    have := congrArg i h
    rw [map_mul, hg, hg, ← hu] at this
    rw [map_mul, ← this, mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
  constructor
  · rintro ⟨r, s, hs, h⟩
    obtain ⟨u, hu⟩ := H x r s hs h
    exact ⟨_, hu.symm⟩
  · rintro ⟨y, hy⟩
    by_contra hx
    have hv : ∀ z : E, Q.valuation E z ≤ 1 → IntAt Q z := fun z hz => by
      obtain ⟨r, s, h⟩ := Q.exists_primeCompl_mul_eq_of_integer z hz
      exact ⟨r, s, s.2, by rw [mul_comm]; exact h⟩
    have h1 : 1 < Q.valuation E x := lt_of_not_ge fun h => hx (hv x h)
    have hx0 : x ≠ 0 := by rintro rfl; simp at h1
    obtain ⟨r, s, hs, h⟩ := hv x⁻¹ (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ h1.le)
    have hr : r ∈ Q.asIdeal := by
      by_contra hr
      exact hx ⟨s, r, hr, by rw [← h]; field_simp⟩
    obtain ⟨u, hu⟩ := H x⁻¹ r s hs h
    have h2 : y * (g r * u) = 1 := hinj (by rw [map_mul, ← hu, hy, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one])
    have h3 := congrArg WittVector.constantCoeff h2
    rw [map_mul, map_mul, (hk r).1 hr] at h3
    simp at h3

omit [NumberField E] in
theorem Good.dense (h : Good Q i) (y : Wn p n) (k : ℕ) :
    ∃ (x : 𝓞 E) (z : Wn p n), i (x : E) = algebraMap (Wn p n) (Qn p n) (y + (p : Wn p n) ^ k * z) := by
  obtain ⟨g, hg, hs, -⟩ := h
  simp only [hg]
  suffices ∃ (x : 𝓞 E) (z : Wn p n), g x = y + (p : Wn p n) ^ k * z by
    obtain ⟨x, z, h⟩ := this
    exact ⟨x, z, congrArg _ h⟩
  induction k with
  | zero => exact ⟨0, -y, by simp⟩
  | succ k ih =>
    obtain ⟨x, z, h⟩ := ih
    obtain ⟨x', hx'⟩ := hs (WittVector.constantCoeff z)
    obtain ⟨z', hz'⟩ := (cc_eq_zero (z - g x')).1 (by rw [map_sub]; exact sub_eq_zero.2 hx'.symm)
    refine ⟨x - p ^ k * x', z', ?_⟩
    rw [map_sub, map_mul, map_pow, map_natCast, h, pow_succ, mul_assoc, ← hz']
    ring

omit [NumberField E] in
theorem Good.pow_inj (h : Good Q i) (hn : n ≠ 0) {s t : ℕ} (hs : s < n) (ht : t < n)
    (e : ∀ x, (Fr p n ^ s) (i x) = (Fr p n ^ t) (i x)) : s = t := by
  obtain ⟨g, hg, hsur, -⟩ := h
  refine frob_pow_inj p n hn hs ht fun y => ?_
  obtain ⟨x, rfl⟩ := hsur y
  obtain ⟨a, ha, ha'⟩ := fr_pow s (g x)
  obtain ⟨b, hb, hb'⟩ := fr_pow t (g x)
  have := e x
  rw [hg, ha, hb] at this
  simp only
  rw [← ha', ← hb', IsFractionRing.injective (Wn p n) (Qn p n) this]

variable {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]

variable (O) in

def Ov (ψ : E →+* Kf) (Q : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : 𝓞 E, x ∈ Q.asIdeal ↔ ∃ y ∈ maximalIdeal O, algebraMap O Kf y = ψ x

omit [NumberField E] [IsFractionRing O Kf] in
theorem Ov.eq {ψ : E →+* Kf} {Q Q' : HeightOneSpectrum (𝓞 E)} (h : Ov O ψ Q) (h' : Ov O ψ Q') : Q = Q' :=
  HeightOneSpectrum.ext (Ideal.ext fun x => (h x).trans (h' x).symm)

omit [IsFractionRing O Kf] in
theorem Ov.conj [StarRing E] {ψ : E →+* Kf} (h : Ov O ψ Q) : Ov O (ψ.comp (starRingEnd E)) (conjPrime₂ Q) :=
  fun x => h (cO E x)

omit [NumberField E] in
theorem ov_iff {ψ : E →+* Kf} {g : 𝓞 E →+* O} (hg : ∀ x : 𝓞 E, algebraMap O Kf (g x) = ψ x) :
    Ov O ψ Q ↔ ∀ x, x ∈ Q.asIdeal ↔ g x ∈ maximalIdeal O := by
  refine forall_congr' fun x => iff_congr Iff.rfl ⟨?_, fun h => ⟨_, h, hg x⟩⟩
  rintro ⟨y, hy, e⟩
  rwa [IsFractionRing.injective O Kf (e.trans (hg x).symm)] at hy

theorem exists_ov (hO : (p : O) ∈ maximalIdeal O) (ψ : E →+* Kf) :
    ∃ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal ∧ Ov O ψ Q := by
  obtain ⟨g, hg⟩ := exists_intHom (O := O) ψ
  have h : (p : 𝓞 E) ∈ (maximalIdeal O).comap g := by rwa [Ideal.mem_comap, map_natCast]
  refine ⟨⟨(maximalIdeal O).comap g, inferInstance, fun e => ?_⟩, h, (ov_iff hg).2 fun x => Iff.rfl⟩
  rw [e, Ideal.mem_bot] at h
  exact hp.out.ne_zero (Nat.cast_eq_zero.1 h)

variable {ι : Qn p n →+* Kf} {j : Wn p n →+* O}

omit [IsFractionRing O Kf] [Algebra O Kf] in
theorem exists_res (hO : (p : O) ∈ maximalIdeal O) (j : Wn p n →+* O) :
    ∃ a : GaloisField p n →+* ResidueField O, ∀ x, a (WittVector.constantCoeff x) = residue O (j x) := by
  refine ⟨RingHom.liftOfSurjective _ (WittVector.constantCoeff_surjective p) ⟨(residue O).comp j, fun x hx => ?_⟩,
    fun x => RingHom.liftOfRightInverse_comp_apply _ _ _ _ x⟩
  obtain ⟨y, rfl⟩ := (cc_eq_zero x).1 hx
  rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_natCast, residue_eq_zero_iff]
  exact Ideal.mul_mem_right _ _ hO

omit [NumberField E] in
theorem Good.ov (h : Good Q i) (hO : (p : O) ∈ maximalIdeal O) (hι : ∀ x, ι (algebraMap _ _ x) = algebraMap O Kf (j x))
    (s : ℕ) {ψ : E →+* Kf} (hψ : ∀ x, ψ x = ι ((Fr p n ^ s) (i x))) : Ov O ψ Q := by
  obtain ⟨g, hg, -, hk⟩ := h
  obtain ⟨a, ha⟩ := exists_res hO j
  intro x
  obtain ⟨y, hy, hy'⟩ := fr_pow s (g x)
  rw [hψ, hg, hy, hι, hk]
  simp only [(IsFractionRing.injective O Kf).eq_iff, exists_eq_right]
  rw [← residue_eq_zero_iff, ← ha, hy', map_eq_zero a, pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)]

theorem Good.exists_pow [Algebra.IsUnramifiedAt ℤ Q.asIdeal] (h : Good Q i) (hn : n ≠ 0) (hO : (p : O) ∈ maximalIdeal O)
    (hι : ∀ x, ι (algebraMap _ _ x) = algebraMap O Kf (j x)) {ψ : E →+* Kf} (hψ : Ov O ψ Q) :
    ∃ s < n, ∀ x, ψ x = ι ((Fr p n ^ s) (i x)) := by
  obtain ⟨g, hg, hs, hk⟩ := h
  obtain ⟨a, ha⟩ := exists_res hO j
  obtain ⟨f, hf⟩ := exists_intHom (O := O) ψ
  have hQ := (ov_iff hf).1 hψ
  let b : GaloisField p n →+* ResidueField O :=
    RingHom.liftOfSurjective (WittVector.constantCoeff.comp g) hs ⟨(residue O).comp f, fun x hx => by
      rw [RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff, ← hQ, hk]; exact hx⟩
  have hb : ∀ x, b (WittVector.constantCoeff (g x)) = residue O (f x) :=
    fun x => RingHom.liftOfRightInverse_comp_apply (WittVector.constantCoeff.comp g) _ _ _ x
  obtain ⟨s, hsn, e⟩ := exists_frob_pow p n hn a b
  let ψ' : E →+* Kf := ι.comp ((Fr p n ^ s).toRingHom.comp i)
  obtain ⟨f', hf'⟩ := exists_intHom (O := O) ψ'
  have : f = f' := eq_of_cong Q f f' hQ fun x => by
    obtain ⟨y, hy, hy'⟩ := fr_pow s (g x)
    have h1 : f' x = j y := IsFractionRing.injective O Kf (by
      rw [hf', ← hι, ← hy, ← hg]; rfl)
    rw [← hb, e, h1, ← ha, hy']
  have h2 : ψ = ψ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x =>
    (hf x).symm.trans (this ▸ hf' x))
  exact ⟨s, hsn, fun x => RingHom.congr_fun h2 x⟩

end Local

section Types

variable {X : Fields} {Kf : Type} [Field Kf] (eK : X.K →+* Kf)

end Types

end GlobalTheory.GO.PlWitt

namespace GlobalTheory.GO

open PlWitt

end GlobalTheory.GO
end
end
