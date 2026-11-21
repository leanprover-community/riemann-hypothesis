import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Nakayama
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LevelOfCongruence

section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
  have h' : Submodule.Quotient.mk (p := (maximalIdeal L ^ n • ⊤ : Submodule L L)) a = 0 := by
    simpa [AdicCompletion.eval] using h
  rw [Submodule.Quotient.mk_eq_zero] at h'
  simpa using h'

private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, sub_eq_zero, ← ha]
  simp [AdicCompletion.eval]

theorem UpperTheory.V.CA.cpl_is :
    ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (x : Ideal C) [x.IsMaximal], ∃ _ : IsLocalRing (Cpl x), IsCplAt x (Cpl x) := by
  intro C _ _ x hx
  refine ⟨inferInstance, ?_⟩
  have hL : ∀ (n : ℕ) (a : Localization.AtPrime x),
      a ∈ maximalIdeal (Localization.AtPrime x) ^ n →
      algebraMap (Localization.AtPrime x) (Cpl x) a ∈ maximalIdeal (Cpl x) ^ n := by
    intro n a ha
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  refine
    { noeth := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
      complete := inferInstance
      comap_pow := fun n => ?_
      dense := fun n r => ?_ }
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.comap_comap]
    have e : Ideal.comap (algebraMap (Localization.AtPrime x) (Cpl x)) (maximalIdeal (Cpl x) ^ n) =
        maximalIdeal (Localization.AtPrime x) ^ n := by
      ext a
      exact ⟨strict_loc _ n a, hL n a⟩
    rw [e, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    refine IsLocalization.comap_map_of_isPrimary_disjoint x.primeCompl _ ?_ ?_
    · apply Ideal.isPrimary_of_isMaximal_radical
      rw [Ideal.radical_pow _ hn.ne', (inferInstance : x.IsPrime).radical]
      infer_instance
    · exact Set.disjoint_left.mpr fun s hs hs' => hs (Ideal.pow_le_self hn.ne' hs')
  · obtain ⟨a, ha⟩ := dense_loc _ n r
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective x.primeCompl a
    have hsx : Ideal.span {(s : C)} ⊔ x = ⊤ := by
      rw [sup_comm]
      have hm : (s : C) ∈ x ⊔ Ideal.span {(s : C)} :=
        Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      refine hx.out.2 _ (lt_of_le_of_ne le_sup_left fun e => s.2 ?_)
      rwa [← e] at hm
    have h1 : (1 : C) ∈ Ideal.span {(s : C)} ⊔ x ^ n := by
      rw [Ideal.sup_pow_eq_top hsx]
      trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    refine ⟨c * t, ?_⟩
    have key : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) =
        IsLocalization.mk' (Localization.AtPrime x) c s * algebraMap C _ z := by
      have hs := IsLocalization.mk'_spec (Localization.AtPrime x) c s
      have hz' : z = 1 - t * s := by
        rw [← hyz]
        ring
      rw [hz', map_sub, map_one, map_mul, map_mul, ← hs]
      ring
    have hmem : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) ∈
        maximalIdeal (Localization.AtPrime x) ^ n := by
      rw [key, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hz)
    have hsum := Ideal.add_mem _ ha (hL n _ hmem)
    rw [map_sub, ← IsScalarTower.algebraMap_apply C (Localization.AtPrime x) (Cpl x)] at hsum
    convert hsum using 1
    ring
end

section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cu_uniq {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (F G : R →+* T)
    (e : F.comp (algebraMap C R) = G.comp (algebraMap C R))
    (hF : maximalIdeal R ≤ J.comap F) (hG : maximalIdeal R ≤ J.comap G) : F = G := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' J
  intro n r
  obtain ⟨c, hc⟩ := h.dense n r
  have h1 : F (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow F n (Ideal.pow_right_mono hF n hc)
  have h2 : G (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow G n (Ideal.pow_right_mono hG n hc)
  have h3 : F (algebraMap C R c) = G (algebraMap C R c) := RingHom.congr_fun e c
  rw [Ideal.Quotient.eq]
  have := sub_mem h1 h2
  rw [map_sub, map_sub, h3] at this
  simpa using this

private theorem cu_ex {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T)
    (hf : x ≤ J.comap f) :
    ∃ F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F :=
  _root_.UpperTheory.Reformulated.B.LevelOfCongruence.cu_ex h J f hf

private theorem cu_le {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x ≤ (maximalIdeal R).comap (algebraMap C R) := by
  have := h.comap_pow 1
  rw [pow_one, pow_one] at this
  exact this.ge

private theorem cu_map {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x.map (algebraMap C R) = maximalIdeal R := by
  haveI := h.noeth
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 (cu_le h)) ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (IsNoetherian.noetherian _)
    (maximalIdeal_le_jacobson _) fun r hr => ?_
  obtain ⟨c, hc⟩ := h.dense 2 r
  have h1 : algebraMap C R c ∈ maximalIdeal R := by
    have := sub_mem hr (Ideal.pow_le_self two_ne_zero hc)
    simpa using this
  have h2 : c ∈ x := by
    have := h.comap_pow 1
    rw [pow_one, pow_one] at this
    rw [← this]; exact h1
  have h3 : r = algebraMap C R c + (r - algebraMap C R c) := by ring
  rw [h3]
  refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h2) ?_
  rw [smul_eq_mul, ← pow_two]
  exact hc

private theorem cu_equiv {C R S : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R]
    [CommRing S] [Algebra C S] [IsLocalRing S] {x : Ideal C}
    (h : IsCplAt x R) (h' : IsCplAt x S) : Nonempty (R ≃ₐ[C] S) := by
  haveI := h.complete
  haveI := h'.complete
  obtain ⟨F, hF1, hF2⟩ := cu_ex h (maximalIdeal S) (algebraMap C S) (cu_le h')
  obtain ⟨G, hG1, hG2⟩ := cu_ex h' (maximalIdeal R) (algebraMap C R) (cu_le h)
  have e1 : G.comp F = RingHom.id R :=
    cu_uniq h (maximalIdeal R) _ _ (by rw [RingHom.comp_assoc, hF1, hG1, RingHom.id_comp])
      (fun r hr => hG2 (hF2 hr)) (fun r hr => hr)
  have e2 : F.comp G = RingHom.id S :=
    cu_uniq h' (maximalIdeal S) _ _ (by rw [RingHom.comp_assoc, hG1, hF1, RingHom.id_comp])
      (fun r hr => hF2 (hG2 hr)) (fun r hr => hr)
  exact ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom F G e2 e1) fun c => RingHom.congr_fun hF1 c⟩

theorem UpperTheory.V.CA.cpl_uniq :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → (∀ (T : Type) [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T), x ≤ J.comap f → ∃! F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F) ∧ Nonempty (R ≃ₐ[C] Cpl x) ∧ x.map (algebraMap C R) = maximalIdeal R := by
  intro C R _ _ _ _ _ x _ h
  refine ⟨fun T _ J _ f hf => ?_, ?_, cu_map h⟩
  · obtain ⟨F, hF⟩ := cu_ex h J f hf
    exact ⟨F, hF, fun G hG => cu_uniq h J G F (hG.1.trans hF.1.symm) hG.2 hF.2⟩
  · obtain ⟨_, h'⟩ := cpl_is C x
    exact cu_equiv h h'
end
