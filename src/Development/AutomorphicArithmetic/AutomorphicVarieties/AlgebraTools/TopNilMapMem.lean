import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnAlgMapSmulMem

section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_idem_topNil :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      ∃ e ∈ Algebra.adjoin R (Set.range T), IsIdempotentElem e ∧ LinearMap.range e = topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ _ T hT
  classical
  let S := Algebra.adjoin R (Set.range T)
  haveI : Module.Finite R S := by
    haveI : IsNoetherian R (Subalgebra.toSubmodule S) := inferInstance
    exact (inferInstance : Module.Finite R (Subalgebra.toSubmodule S))
  letI : CommRing S := Algebra.adjoinCommRingOfComm R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hT i j)
  let t : κ → S := fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  obtain ⟨e, he, -, hx⟩ := topNil_eq_idem R S κ t
  have hfun : (fun i => (Algebra.lsmul R R M) (t i)) = T := by
    funext i
    rfl
  have he' : IsIdempotentElem (e : Module.End R M) := congrArg Subtype.val he
  refine ⟨(e : Module.End R M), e.2, he', ?_⟩
  ext x
  have h := hx M x
  rw [hfun] at h
  rw [h]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun he' y
  · intro h2
    exact ⟨x, h2⟩
end

section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.topNil_free :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      (∃ C : Submodule R M, IsCompl (topNil (IsLocalRing.maximalIdeal R) T) C ∧ ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
        (∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T) ∧ ∀ x ∈ C, φ x ∈ C) ∧
      (∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (∀ i, ∃ r : ℕ, ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, (T i ^ r) x ∈ (IsLocalRing.maximalIdeal R) • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (Module.Free R M → Module.Free R (topNil (IsLocalRing.maximalIdeal R) T) ∧ Module.finrank R (topNil (IsLocalRing.maximalIdeal R) T) ≤ Module.finrank R M) := by
  intro R _ _ _ _ κ M _ _ _ T hT
  obtain ⟨e, he, hid, hr⟩ := UpperTheory.V.AlgebraTools.exists_idem_topNil R κ M T hT
  have hee : ∀ x, e (e x) = e x := fun x => by
    have h := congrArg (fun f : Module.End R M => f x) hid.eq
    simpa using h
  have hfix : ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, e x = x := by
    rw [← hr]
    rintro _ ⟨y, rfl⟩
    exact hee y
  have hmem : ∀ x, e x ∈ topNil (IsLocalRing.maximalIdeal R) T := fun x => by
    rw [← hr]; exact ⟨x, rfl⟩
  have hcomm : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) → ∀ x, φ (e x) = e (φ x) := by
    intro φ hφ x
    have h : Commute φ e := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute he ?_
      rintro _ ⟨i, rfl⟩
      exact hφ i
    have h2 := congrArg (fun f : Module.End R M => f x) h.eq
    simpa using h2
  have hstab : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
      ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T := by
    intro φ hφ x hx
    rw [← hfix x hx, hcomm φ hφ]
    exact hmem _
  have hI : ∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T =
      I • topNil (IsLocalRing.maximalIdeal R) T := by
    intro I
    refine le_antisymm ?_ (le_inf (Submodule.smul_mono le_rfl le_top) Submodule.smul_le_right)
    rintro x ⟨hx1, hx2⟩
    have h1 : e x ∈ Submodule.map e (I • ⊤ : Submodule R M) := ⟨x, hx1, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, hr, hfix x hx2] at h1
    exact h1
  refine ⟨⟨LinearMap.ker e, ?_, fun φ hφ => ⟨hstab φ hφ, ?_⟩⟩, hI, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hx hk
      rw [← hfix x hx]
      exact hk
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      refine Submodule.mem_sup.2 ⟨e x, hmem x, x - e x, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hee, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hcomm φ hφ, hx, map_zero]
  · intro i
    obtain ⟨S, hS⟩ := IsNoetherian.noetherian (topNil (IsLocalRing.maximalIdeal R) T)
    have hev : ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
        (T i ^ r) x ∈ ((IsLocalRing.maximalIdeal R) ^ 1 • ⊤ : Submodule R M) := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hx' : x ∈ topNil (IsLocalRing.maximalIdeal R) T := hS ▸ Submodule.subset_span hx
      exact mem_topNil.1 hx' i 1
    obtain ⟨r, hr'⟩ := hev.exists
    refine ⟨r, fun x hx => ?_⟩
    rw [← hI]
    refine ⟨?_, hstab _ (fun j => (hT i j).pow_left r) x hx⟩
    have hle : Submodule.span R (S : Set M) ≤
        Submodule.comap (T i ^ r) ((IsLocalRing.maximalIdeal R) • ⊤ : Submodule R M) := by
      rw [Submodule.span_le]
      intro y hy
      have h := hr' y hy
      rw [pow_one] at h
      exact h
    rw [hS] at hle
    exact hle hx
  · intro hF
    refine ⟨?_, Submodule.finrank_le _⟩
    have hP : Module.Projective R (topNil (IsLocalRing.maximalIdeal R) T) :=
      Module.Projective.of_split (topNil (IsLocalRing.maximalIdeal R) T).subtype
        (LinearMap.codRestrict _ e hmem) (by
          ext x
          simpa using hfix x.1 x.2)
    exact Module.free_of_flat_of_isLocalRing
end

section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem topNil_map_mem {R M M' κ : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (T : κ → Module.End R M)
    (T' : κ → Module.End R M') (f : M →ₗ[R] M') (hf : ∀ i x, f (T i x) = T' i (f x))
    {x : M} (hx : x ∈ topNil I T) : f x ∈ topNil I T' := by
  rw [mem_topNil] at hx ⊢
  intro i j
  have hpow : ∀ r : ℕ, f ((T i ^ r) x) = (T' i ^ r) (f x) := by
    intro r
    induction r with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hf, ih]
  have hle : Submodule.map f (I ^ j • (⊤ : Submodule R M)) ≤ I ^ j • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  filter_upwards [hx i j] with r hr
  rw [← hpow]
  exact hle ⟨_, hr, rfl⟩

theorem UpperTheory.V.AlgebraTools.topNil_map :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] (M' : Type) [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M'] (T : κ → Module.End R M) (T' : κ → Module.End R M'),
      (∀ i j, Commute (T i) (T j)) → (∀ i j, Commute (T' i) (T' j)) → ∀ f : M →ₗ[R] M', (∀ i x, f (T i x) = T' i (f x)) →
      (topNil (IsLocalRing.maximalIdeal R) T).map f = topNil (IsLocalRing.maximalIdeal R) T' ⊓ LinearMap.range f ∧
      ∀ I : Ideal R, LinearMap.ker f = I • ⊤ → LinearMap.ker f ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ M' _ _ _ _ T T' hT hT' f hf
  obtain ⟨_, hsmul, -, -⟩ := topNil_free R κ M T hT
  refine ⟨le_antisymm ?_ ?_, fun I hI => by rw [hI]; exact hsmul I⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    exact ⟨topNil_map_mem _ T T' f hf hx, x, rfl⟩
  · rintro y ⟨hy, x, rfl⟩
    have hTx : ∀ i j x, T i (T j x) = T j (T i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT i j).eq, Module.End.mul_apply]
    have hT'x : ∀ i j x, T' i (T' j x) = T' j (T' i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT' i j).eq, Module.End.mul_apply]
    let S : κ → Module.End R (M × M') := fun i => (T i).prodMap (T' i)
    have hS : ∀ i j, Commute (S i) (S j) := by
      intro i j
      show S i * S j = S j * S i
      apply LinearMap.ext
      intro p
      simp [S, Module.End.mul_apply, hTx i j, hT'x i j]
    obtain ⟨⟨C, hC, hstab⟩, -⟩ := topNil_free R κ (M × M') S hS
    let φ : Module.End R (M × M') := (LinearMap.inr R M M').comp (f.comp (LinearMap.fst R M M'))
    have hφ : ∀ i, Commute φ (S i) := by
      intro i
      show φ * S i = S i * φ
      apply LinearMap.ext
      intro p
      simp [φ, S, Module.End.mul_apply, hf]
    have hmem : ((x, 0) : M × M') ∈ topNil (IsLocalRing.maximalIdeal R) S ⊔ C := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn, c, hc, hnc⟩ := Submodule.mem_sup.mp hmem
    have hn1 : n.1 ∈ topNil (IsLocalRing.maximalIdeal R) T :=
      topNil_map_mem _ S T (LinearMap.fst R M M') (fun i p => rfl) hn
    have hφc : φ c ∈ C := (hstab φ hφ).2 c hc
    have hx : x = n.1 + c.1 := by
      have := congrArg Prod.fst hnc
      simpa using this.symm
    have hfc : f c.1 ∈ topNil (IsLocalRing.maximalIdeal R) T' := by
      have : f c.1 = f x - f n.1 := by
        rw [hx]
        simp
      rw [this]
      exact Submodule.sub_mem _ hy (topNil_map_mem _ T T' f hf hn1)
    have hφn : φ c ∈ topNil (IsLocalRing.maximalIdeal R) S := by
      have := topNil_map_mem _ T' S (LinearMap.inr R M M') (fun i y => by simp [S]) hfc
      simpa [φ] using this
    have h0 : φ c = 0 := (Submodule.disjoint_def.mp hC.disjoint) _ hφn hφc
    have hfc0 : f c.1 = 0 := by
      have := congrArg Prod.snd h0
      simpa [φ] using this
    refine ⟨n.1, hn1, ?_⟩
    rw [hx, map_add, hfc0, add_zero]
end
