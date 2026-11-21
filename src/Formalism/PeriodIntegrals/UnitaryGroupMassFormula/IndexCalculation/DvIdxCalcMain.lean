import Mathlib
import Formalism.PeriodIntegrals.IdxCalc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ElementDenominator

section
noncomputable section

namespace PI.Dv.IdxW

open Module

section Gen

variable {R : Type*} [CommRing R] (S : Submonoid R)


variable {V : Type*} [AddCommGroup V] [Module R V]

def lenS (M N : Submodule R V) : ℕ∞ :=
  Module.length (Localization S) (LocalizedModule S (↥M ⧸ N.comap M.subtype))

theorem comap_inf (M N : Submodule R V) : N.comap M.subtype = (M ⊓ N).comap M.subtype := by
  ext x
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩






theorem length_quot_free {A : Type*} [CommRing A] [StrongRankCondition A] (J : Ideal A)
    (N : Type*) [AddCommGroup N] [Module A N] [Module.Free A N] [Module.Finite A N] :
    Module.length A (N ⧸ J • (⊤ : Submodule A N)) =
      (Module.finrank A N : ℕ∞) * Module.length A (A ⧸ J) := by
  let b := Module.finBasis A N
  let e : (N ⧸ J • (⊤ : Submodule A N)) ≃ₗ[A] (Fin (Module.finrank A N) → A ⧸ J) :=
    (TensorProduct.quotTensorEquivQuotSMul N J).symm ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl A (A ⧸ J)) b.equivFun ≪≫ₗ
        TensorProduct.piScalarRight A A (A ⧸ J) (Fin (Module.finrank A N))
  rw [e.length_eq, Module.length_pi_of_fintype]
  simp

end Gen

section Frac

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

variable (K) in
include K in
theorem smul_eq_zero_iff' {c : R} (hc : c ≠ 0) {x : V} : c • x = 0 ↔ x = 0 := by
  rw [← algebraMap_smul K c x, smul_eq_zero]
  have : algebraMap R K c ≠ 0 := by
    intro h
    exact hc ((IsFractionRing.injective R K) (by rw [h, map_zero]))
  simp [this]

theorem eltDen (Y : Submodule R V) {y : V} (hy : y ∈ Submodule.span K (Y : Set V)) :
    ∃ s : R, s ≠ 0 ∧ s • y ∈ Y :=
  _root_.UpperTheory.Reformulated.B.ElementDenominator.eltDen Y hy

theorem den (X Y : Submodule R V) (hX : X.FG) (hXY : ∀ x ∈ X, x ∈ Submodule.span K (Y : Set V)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x ∈ X, c • x ∈ Y := by
  classical
  obtain ⟨s, rfl⟩ := hX
  have hc : ∀ a ∈ s, ∃ c : R, c ≠ 0 ∧ c • a ∈ Y := fun a ha =>
    eltDen (K := K) Y (hXY a (Submodule.subset_span ha))
  choose! c hc0 hcY using hc
  refine ⟨∏ a ∈ s, c a, Finset.prod_ne_zero_iff.mpr hc0, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem a ha =>
    rw [← Finset.prod_erase_mul s c ha, mul_smul]
    exact Y.smul_mem _ (hcY a ha)
  | zero => rw [smul_zero]; exact Y.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Y.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact Y.smul_mem r hx

omit [IsScalarTower R K V] in
theorem den_of_span (X Y : Submodule R V) (hX : X.FG) [IsScalarTower R K V]
    (h : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x ∈ X, c • x ∈ Y :=
  den (K := K) X Y hX fun x hx => h ▸ Submodule.subset_span hx

variable (K) in
include K in
theorem isTorsionFree_V : Module.IsTorsionFree R V :=
  Module.isTorsionFree_iff_smul_eq_zero.mpr fun r v h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr ((smul_eq_zero_iff' K hr).mp h)

variable (K) in
include K in
theorem isTorsionFree_sub (M : Submodule R V) : Module.IsTorsionFree R M :=
  Module.isTorsionFree_iff_smul_eq_zero.mpr fun r v h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · refine Or.inr (Subtype.ext ?_)
      have : r • (v : V) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
      exact (smul_eq_zero_iff' K hr).mp this

def toSpan (M : Submodule R V) : ↥M →ₗ[R] ↥(Submodule.span K (M : Set V)) where
  toFun x := ⟨x, Submodule.subset_span x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance isLocalizedModule_toSpan (M : Submodule R V) :
    IsLocalizedModule (nonZeroDivisors R) (toSpan (K := K) M) where
  map_units x := by
    rw [Module.End.isUnit_iff]
    have hx0 : (x : R) ≠ 0 := nonZeroDivisors.ne_zero x.2
    have hx' : algebraMap R K x ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      apply Subtype.ext
      have : (x : R) • ((y : V) - z) = 0 := by
        rw [smul_sub, sub_eq_zero]
        exact congrArg Subtype.val hyz
      exact sub_eq_zero.mp ((smul_eq_zero_iff' K hx0).mp this)
    · intro y
      refine ⟨(algebraMap R K x)⁻¹ • y, ?_⟩
      apply Subtype.ext
      show (x : R) • ((algebraMap R K x)⁻¹ • (y : V)) = y
      rw [← algebraMap_smul K (x : R), smul_smul, mul_inv_cancel₀ hx', one_smul]
  surj y := by
    obtain ⟨s, hs, hsy⟩ := eltDen (K := K) M y.2
    refine ⟨(⟨s • (y : V), hsy⟩, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), ?_⟩
    apply Subtype.ext
    rfl
  exists_of_eq {x₁ x₂} h := by
    refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val h
    have : x₁ = x₂ := Subtype.ext h'
    rw [this]

theorem finrank_span_eq (M : Submodule R V) :
    Module.finrank K (Submodule.span K (M : Set V)) = Module.finrank R M := by
  rw [IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl]
  exact IsLocalizedModule.finrank_eq (nonZeroDivisors R) (toSpan (K := K) M) le_rfl

end Frac

end PI.Dv.IdxW
end
end

section
noncomputable section

namespace PI.Dv.IdxW

open NumberField IsDedekindDomain Module

section Gen

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

theorem comap_smul_top (I : Ideal R) (M : Submodule R V) :
    (I • M).comap M.subtype = I • (⊤ : Submodule R M) := by
  have e := Submodule.map_smul'' I (⊤ : Submodule R M) M.subtype
  rw [Submodule.map_subtype_top] at e
  rw [← e, Submodule.comap_map_eq_of_injective M.injective_subtype]

theorem ideal_localized' (S : Submonoid R) (I : Ideal R) :
    I.localized' (Localization S) S (Algebra.linearMap R (Localization S)) =
      I.map (algebraMap R (Localization S)) := by
  exact Ideal.localized'_eq_map (Localization S) S I

theorem span_smul_le (c : R) (M N : Submodule R V) (h : ∀ x ∈ M, c • x ∈ N) :
    Ideal.span {c} • M ≤ N := by
  rw [Submodule.smul_le]
  intro r hr x hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  rw [mul_smul]
  exact N.smul_mem a (h x hx)


theorem lenS_ker_img (S : Submonoid R) {V' : Type*} [AddCommGroup V'] [Module R V']
    (φ : V →ₗ[R] V') (k : Submodule R V) (hk : ∀ x, x ∈ k ↔ φ x = 0) (D X : Submodule R V)
    (hDX : D ≤ X) :
    lenS S X D = lenS S (X ⊓ k) (D ⊓ k) + lenS S (X.map φ) (D.map φ) := by
  let f0 : ↥(X ⊓ k) →ₗ[R] ↥X := Submodule.inclusion inf_le_left
  let g0 : ↥X →ₗ[R] ↥(X.map φ) := φ.submoduleMap X
  let f := Submodule.mapQ ((D ⊓ k).comap (X ⊓ k).subtype) (D.comap X.subtype) f0 (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, f0, Submodule.coe_inclusion] at hx ⊢
    exact (Submodule.mem_inf.1 hx).1)
  let g := Submodule.mapQ (D.comap X.subtype) ((D.map φ).comap (X.map φ).subtype) g0 (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, g0, LinearMap.submoduleMap_coe_apply] at hx ⊢
    exact Submodule.mem_map_of_mem hx)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply, f0, Submodule.coe_inclusion] at ha ⊢
      exact Submodule.mem_inf.2 ⟨ha, (Submodule.mem_inf.1 x.2).2⟩
  have hg : Function.Surjective g := by
    intro c
    induction c using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 y.2
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      simp only [g, Submodule.mapQ_apply]
      congr 1
      ext
      simp [g0, hxy]
  have hex : Function.Exact f g := by
    intro b
    induction b using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro h
        simp only [g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.subtype_apply, g0, LinearMap.submoduleMap_coe_apply] at h
        obtain ⟨d, hd, hdx⟩ := Submodule.mem_map.1 h
        have hmem : (x : V) - d ∈ X ⊓ k :=
          Submodule.mem_inf.2 ⟨X.sub_mem x.2 (hDX hd), (hk _).2 (by rw [map_sub, hdx, sub_self])⟩
        refine ⟨Submodule.Quotient.mk ⟨(x : V) - d, hmem⟩, ?_⟩
        simp only [f, Submodule.mapQ_apply]
        rw [Submodule.Quotient.eq]
        simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, f0,
          Submodule.coe_inclusion, sub_sub_cancel_left, neg_mem_iff]
        exact hd
      · rintro ⟨a, ha⟩
        rw [← ha]
        induction a using Submodule.Quotient.induction_on with
        | H z =>
          simp only [f, g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
            Submodule.subtype_apply, f0, g0, LinearMap.submoduleMap_coe_apply, Submodule.coe_inclusion]
          rw [(hk _).1 (Submodule.mem_inf.1 z.2).2]
          exact Submodule.zero_mem _
  unfold lenS
  exact Module.length_eq_add_of_exact (LocalizedModule.map S f) (LocalizedModule.map S g)
    (LocalizedModule.map_injective S f hf) (LocalizedModule.map_surjective S g hg)
    (LocalizedModule.map_exact S f g hex)

end Gen

variable {K : Type} [Field K] [NumberField K]

instance instIsPrimeW (w : HeightOneSpectrum (𝓞 K)) : w.asIdeal.IsPrime := w.isPrime

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem lenAt_eq (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) :
    lenAt w M N = lenS w.asIdeal.primeCompl M N := rfl

theorem len_pow (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) (hM : M.FG) (F : ℕ) :
    lenS w.asIdeal.primeCompl M ((w.asIdeal ^ F) • M) = ((F * Formalism.HN.rkK M : ℕ) : ℕ∞) := by
  set S := w.asIdeal.primeCompl with hS
  have hSle : S ≤ nonZeroDivisors (𝓞 K) := Ideal.primeCompl_le_nonZeroDivisors _
  have : IsDiscreteValuationRing (Localization.AtPrime w.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot
      (Localization.AtPrime w.asIdeal)
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM
  have : Module.IsTorsionFree (𝓞 K) M := isTorsionFree_sub K M
  have : Module.Finite (Localization S) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)
  have : Module.Free (Localization S) (LocalizedModule S M) :=
    Module.free_of_finite_type_torsion_free'
  have hr : Module.finrank (Localization S) (LocalizedModule S M) = Formalism.HN.rkK M := by
    rw [IsLocalization.finrank_eq (Localization S) S hSle,
      IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hSle]
    unfold Formalism.HN.rkK
    rw [finrank_span_eq (K := K)]
  have hloc : ((w.asIdeal ^ F • (⊤ : Submodule (𝓞 K) M)).localized S) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime w.asIdeal) ^ F) •
        (⊤ : Submodule (Localization S) (LocalizedModule S M)) := by
    dsimp only [Submodule.localized]
    rw [Submodule.localized'_smul, Submodule.localized'_top, ideal_localized', Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal]
  unfold lenS
  rw [comap_smul_top, ← (localizedQuotientEquiv S (w.asIdeal ^ F • (⊤ : Submodule (𝓞 K) M))).length_eq,
    hloc, length_quot_free, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, hr]
  push_cast
  ring

theorem fact (w : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ≠ 0) :
    ∃ k : ℕ, Formalism.BasicNotions.vAdd w (algebraMap (𝓞 K) K c) = k ∧ c ∈ w.asIdeal ^ k ∧
      ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∀ y ∈ w.asIdeal ^ k, s * y ∈ Ideal.span {c} := by
  classical
  set v := w.intValuation c with hv
  have hv0 : v ≠ 0 := w.intValuation_ne_zero c hc
  have hv1 : v ≤ 1 := w.intValuation_le_one c
  have hval : w.valuation K (algebraMap (𝓞 K) K c) = v := w.valuation_of_algebraMap c
  obtain ⟨m, hm⟩ : ∃ m : ℤ, v = WithZero.exp m := ⟨WithZero.log v, (WithZero.exp_log hv0).symm⟩
  have hm0 : m ≤ 0 := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv1
    exact hv1
  have hkm : (((-m).toNat : ℕ) : ℤ) = -m := by omega
  have hck : c ∈ w.asIdeal ^ (-m).toNat := by
    rw [← w.intValuation_le_pow_iff_mem, ← hv, hm, hkm, neg_neg]
  have hck1 : c ∉ w.asIdeal ^ ((-m).toNat + 1) := by
    intro h
    have h' := (w.intValuation_le_pow_iff_mem c _).2 h
    rw [← hv, hm, WithZero.exp_le_exp] at h'
    push_cast at h'
    omega
  refine ⟨(-m).toNat, ?_, hck, ?_⟩
  · simp only [Formalism.BasicNotions.vAdd, hval, hm, WithZero.log_exp]
    omega
  obtain ⟨J, hJ⟩ : w.asIdeal ^ (-m).toNat ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hck)
  have hJp : ¬ J ≤ w.asIdeal := by
    intro hle
    apply hck1
    have hle' : Ideal.span {c} ≤ w.asIdeal ^ ((-m).toNat + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact hle' (Ideal.mem_span_singleton_self c)
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.1 hJp
  refine ⟨s, hsp, fun y hy => ?_⟩
  rw [hJ, mul_comm s y]
  exact Ideal.mul_mem_mul hy hsJ





omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem idx_via (w : HeightOneSpectrum (𝓞 K)) (M N D : Submodule (𝓞 K) V) (hDM : D ≤ M)
    (hDN : D ≤ N) (hM : lenS w.asIdeal.primeCompl M D ≠ ⊤)
    (hN : lenS w.asIdeal.primeCompl N D ≠ ⊤) :
    idxAt w M N = ((lenS w.asIdeal.primeCompl M D).toNat : ℤ) -
      (lenS w.asIdeal.primeCompl N D).toNat := by
  have lenS_zero : ∀ X Y : Submodule (𝓞 K) V, X ≤ Y → lenS w.asIdeal.primeCompl X Y = 0 := by
    intro X Y h
    unfold lenS
    rw [Module.length_eq_zero_iff]
    have : Subsingleton (↥X ⧸ Y.comap X.subtype) := by
      rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
      intro x _
      exact h x.2
    constructor
    intro a b
    induction a using LocalizedModule.induction_on with
    | h m s =>
      induction b using LocalizedModule.induction_on with
      | h m' s' =>
        rw [Subsingleton.elim m 0, Subsingleton.elim m' 0, LocalizedModule.zero_mk,
          LocalizedModule.zero_mk]
  have split : ∀ M N D : Submodule (𝓞 K) V, D ≤ M → D ≤ N →
      lenS w.asIdeal.primeCompl M D = lenS w.asIdeal.primeCompl M N +
        lenS w.asIdeal.primeCompl (M ⊓ N) D := by
    intro M N D hDM hDN
    have hk : ∀ x, x ∈ N ↔ N.mkQ x = 0 := fun x => by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have h1 := lenS_ker_img w.asIdeal.primeCompl N.mkQ N hk D M hDM
    have h2 := lenS_ker_img w.asIdeal.primeCompl N.mkQ N hk (M ⊓ N) M inf_le_left
    have hbot : ∀ E : Submodule (𝓞 K) V, E ≤ N → E.map N.mkQ = ⊥ := fun E hE => by
      refine eq_bot_iff.2 fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hE hx
    rw [inf_eq_left.2 hDN, hbot D hDN] at h1
    rw [hbot _ inf_le_right, lenS_zero _ _ (le_inf le_rfl inf_le_right), zero_add] at h2
    have hc : lenS w.asIdeal.primeCompl M N = lenS w.asIdeal.primeCompl M (M ⊓ N) := by
      have e : N.comap M.subtype = (M ⊓ N).comap M.subtype := by
        ext x
        simp [Submodule.mem_inf, x.2]
      unfold lenS
      rw [e]
    rw [h1, hc, h2, add_comm]
  have hs := split M N D hDM hDN
  have hs' := split N M D hDN hDM
  rw [inf_comm] at hs'
  unfold PI.Dv.idxAt
  rw [lenAt_eq, lenAt_eq, hs, hs']
  rw [hs] at hM
  rw [hs'] at hN
  rw [ENat.toNat_add (WithTop.add_ne_top.1 hM).1 (WithTop.add_ne_top.1 hM).2,
    ENat.toNat_add (WithTop.add_ne_top.1 hN).1 (WithTop.add_ne_top.1 hN).2]
  push_cast
  ring

end PI.Dv.IdxW
end
end

section
noncomputable section

namespace PI.Dv.IdxW

open NumberField IsDedekindDomain Module


end PI.Dv.IdxW
end
end
