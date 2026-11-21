import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocChar

section
open IsLocalRing UpperTheory.V.Hi

private theorem coe_mem_smul_iff {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (Y : Submodule A M) (J : Ideal A) (y : Y) :
    (y : M) ∈ J • Y ↔ y ∈ J • (⊤ : Submodule A Y) :=
  (Submodule.mem_smul_top_iff J Y y).symm

private theorem restr_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {t : Module.End A Y} {f : Module.End A M} (h : Restr t f) (n : ℕ) :
    Restr (t ^ n) (f ^ n) := by
  induction n with
  | zero => intro y; simp
  | succ n ih =>
    intro y
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem mem_iSup_iff {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {t : Module.End A Y} {f : Module.End A M} (h : Restr t f) (J : Ideal A) (y : Y) :
    (y : M) ∈ (⨆ n : ℕ, (J • Y).comap (f ^ n)) ↔ ∃ n : ℕ, (t ^ n) y ∈ J • (⊤ : Submodule A Y) := by
  have hf : ∀ x ∈ J • Y, f x ∈ J • Y := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr z hz
      rw [map_smul]
      refine Submodule.smul_mem_smul hr ?_
      have := h ⟨z, hz⟩
      simp only at this
      rw [← this]
      exact (t ⟨z, hz⟩).2
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  have hmono : Monotone fun n : ℕ => (J • Y).comap (f ^ n) := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hf _ hx
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  refine exists_congr fun n => ?_
  rw [Submodule.mem_comap, ← restr_pow h n y, coe_mem_smul_iff]

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → ∃ e ∈ heckeAlg Y op, IsIdempotentElem e ∧ (∀ y : Y, (y : M) ∈ locPart Y op a ↔ e y = y) ∧ ∀ φ : Module.End A Y, (∀ i t, Restr t (op i) → φ * t = t * φ) → φ * e = e * φ := by
  intro A M ι _ _ _ _ Y _ op a h
  obtain ⟨T, _, _, j, t, -, hr, ht, htop, hfin⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeModel A M ι Y op h
  haveI : Module.Finite A T := hfin inferInstance inferInstance
  obtain ⟨e, he, h1, h2, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs A T ι t a htop
  have hI : ∀ μ ∈ (maximalIdeal A).map (algebraMap A T), ∀ x,
      (j : T →+* Module.End A Y) μ x ∈ maximalIdeal A • (⊤ : Submodule A Y) := by
    intro μ hμ
    have hμ' : μ ∈ maximalIdeal A • (⊤ : Submodule A T) := by
      rw [Ideal.smul_top_eq_map]
      exact hμ
    intro x
    change j μ x ∈ _
    refine Submodule.smul_induction_on hμ' ?_ ?_
    · intro r hr z _
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro b c hb hc
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hb hc
  have hchar := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar A Y T ι (j : T →+* Module.End A Y) _
    (fun i => t i - algebraMap A T (a i)) e hI he h1 h2
  have hres : ∀ i, Restr (j (t i - algebraMap A T (a i))) (op i - algebraMap A _ (a i)) := by
    intro i y
    rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub,
      ht i y, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul]
  have hmem : j e ∈ heckeAlg Y op := by
    rw [← hr]
    exact ⟨e, rfl⟩
  refine ⟨j e, hmem, he.map j, fun y => ?_, fun φ hφ => ?_⟩
  · refine Iff.trans ?_ (hchar y).symm
    unfold locPart
    rw [Submodule.mem_inf, and_iff_right y.2, Submodule.mem_iInf]
    refine forall_congr' fun i => ?_
    rw [Submodule.mem_iInf]
    refine forall_congr' fun k => ?_
    exact mem_iSup_iff (hres i) _ y
  · refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hmem ?_
    rintro s ⟨i, hi⟩
    exact hφ i s hi
end

section
open IsLocalRing UpperTheory.V.Hi

private theorem pres_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    (T : Module.End A M) (h : ∀ y ∈ N, T y ∈ N) (n : ℕ) : ∀ y ∈ N, (T ^ n) y ∈ N := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact h _ (ih y hy)

private theorem pres_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    (I : Ideal A) (T : Module.End A M) (h : ∀ y ∈ N, T y ∈ N) : ∀ y ∈ I • N, T y ∈ I • N := by
  intro y hy
  refine Submodule.smul_induction_on hy (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr (h n hn)
  · rw [map_add]; exact add_mem hx hy

private theorem pres_sub {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    (T : Module.End A M) (c : A) (h : ∀ y ∈ N, T y ∈ N) :
    ∀ y ∈ N, (T - algebraMap A (Module.End A M) c) y ∈ N := by
  intro y hy
  rw [LinearMap.sub_apply, Module.algebraMap_end_apply]
  exact sub_mem (h y hy) (N.smul_mem c hy)

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locFree :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → CommOn (locPart Y op a) op ∧ locPart (locPart Y op a) op a = locPart Y op a ∧ Module.Finite A (locPart Y op a) ∧ (∃ Z : Submodule A M, Disjoint (locPart Y op a) Z ∧ locPart Y op a ⊔ Z = Y ∧ ∀ i, ∀ z ∈ Z, op i z ∈ Z) ∧ (Module.Projective A Y → Module.Free A (locPart Y op a)) := by
  intro A M ι _ _ _ _ Y _ op a h
  obtain ⟨e, -, he, hmem, hcomm⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A M ι Y op a h
  have hLY : locPart Y op a ≤ Y := inf_le_left
  have hee : ∀ y : Y, e (e y) = e y := fun y => by
    rw [← Module.End.mul_apply, he.eq]
  have heL : ∀ y : Y, (e y : M) ∈ locPart Y op a := fun y => (hmem _).2 (hee y)
  have hc : ∀ j (y : Y), e ⟨op j y, h.1 j y y.2⟩ = ⟨op j (e y), h.1 j _ (e y).2⟩ := by
    intro j y
    have := hcomm ((op j).restrict (h.1 j)) (fun i t ht => by
      ext z
      have h1 : ∀ w : Y, (t w : M) = op i w := ht
      simp only [Module.End.mul_apply, h1, LinearMap.restrict_coe_apply]
      exact h.2 j i z z.2)
    exact (LinearMap.congr_fun this y).symm
  have hst : ∀ i, ∀ y ∈ locPart Y op a, op i y ∈ locPart Y op a := by
    intro i y hy
    have h1 := (hmem ⟨y, hLY hy⟩).1 hy
    refine (hmem ⟨op i y, h.1 i y (hLY hy)⟩).2 ?_
    have h2 := hc i ⟨y, hLY hy⟩
    rw [h2]
    simp only [h1]
  let E : Y →ₗ[A] locPart Y op a := LinearMap.codRestrict _ (Y.subtype ∘ₗ e) heL
  have hE : E ∘ₗ Submodule.inclusion hLY = LinearMap.id := by
    ext x
    exact congrArg (fun w : Y => (w : M)) ((hmem ⟨x, hLY x.2⟩).1 x.2)
  have hfin : Module.Finite A (locPart Y op a) :=
    Module.Finite.of_surjective E fun x => ⟨_, LinearMap.congr_fun hE x⟩
  have hkey : ∀ (I : Ideal A), ∀ w ∈ locPart Y op a, w ∈ I • Y → w ∈ I • locPart Y op a := by
    intro I w hw hw'
    have h0 : ∀ y ∈ I • (⊤ : Submodule A Y), (e y : M) ∈ I • locPart Y op a := by
      intro y hy
      refine Submodule.smul_induction_on hy (fun r hr n _ => ?_) (fun x y hx hy => ?_)
      · rw [map_smul]; exact Submodule.smul_mem_smul hr (heL n)
      · rw [map_add]; exact add_mem hx hy
    have h1 := h0 ⟨w, hLY hw⟩ ((Submodule.mem_smul_top_iff I Y _).2 hw')
    rwa [(hmem ⟨w, hLY hw⟩).1 hw] at h1
  refine ⟨⟨hst, fun i j y hy => h.2 i j y (hLY hy)⟩, ?_, hfin, ?_, fun hP => ?_⟩
  · refine le_antisymm inf_le_left fun x hx => ⟨hx, ?_⟩
    have hx2 := hx.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf] at hx2 ⊢
    intro i k
    have hmono : Monotone fun n : ℕ =>
        (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A (Module.End A M) (a i)) ^ n) := by
      refine monotone_nat_of_le_succ fun n y hy => ?_
      rw [Submodule.mem_comap] at hy ⊢
      rw [pow_succ', Module.End.mul_apply]
      exact pres_smul Y _ _ (pres_sub Y _ _ (h.1 i)) _ hy
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 (hx2 i k)
    refine Submodule.mem_iSup_of_mem n ?_
    exact hkey _ _ (pres_pow _ _ (pres_sub _ _ _ (hst i)) n x hx) hn
  · refine ⟨(LinearMap.ker e).map Y.subtype, ?_, ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      rintro x hx ⟨y, hy, rfl⟩
      have h1 := (hmem y).1 hx
      have h2 : e y = 0 := hy
      rw [← h1, h2, map_zero]
    · refine le_antisymm (sup_le hLY (Submodule.map_subtype_le _ _)) fun x hx => ?_
      have : x = (e ⟨x, hx⟩ : M) + Y.subtype (⟨x, hx⟩ - e ⟨x, hx⟩) := by simp
      rw [this]
      refine Submodule.add_mem_sup (heL _) ⟨_, ?_, rfl⟩
      change e _ = 0
      rw [map_sub, hee, sub_self]
    · rintro i x ⟨y, hy, rfl⟩
      have h2 : e y = 0 := hy
      refine ⟨⟨op i y, h.1 i y y.2⟩, ?_, rfl⟩
      change e _ = 0
      rw [hc]
      simp [h2]
  · haveI : Module.Projective A (locPart Y op a) := Module.Projective.of_split _ _ hE
    exact Module.free_of_flat_of_isLocalRing
end
