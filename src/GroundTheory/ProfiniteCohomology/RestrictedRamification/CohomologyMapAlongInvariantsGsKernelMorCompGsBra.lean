import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction
import GroundTheory.ProfiniteCohomology.Factor
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplit
import GroundTheory.ProfiniteCohomology.GlobalClassFormation

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

theorem eq_zero_of_coprime_nsmul_of_pow_nsmul {M : Type*} [AddCommGroup M] {ℓ m j : ℕ}
    (hm : m.Coprime ℓ) {x : M} (h1 : m • x = 0) (h2 : ℓ ^ j • x = 0) : x = 0 := by
  have hd : addOrderOf x ∣ Nat.gcd m (ℓ ^ j) :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h1) (addOrderOf_dvd_of_nsmul_eq_zero h2)
  rw [Nat.Coprime.gcd_eq_one (hm.pow_right j), Nat.dvd_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.1 hd

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem eq_zero_of_cohomologyInfl_three_eq_zero (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G)
    [N.Normal] (hN : IsClosed (N : Set G)) (h1 : IsZero (cohomology (Rep.res N.subtype A) 1)) (ℓ : ℕ)
    (h2 : ∀ y : cohomology (Rep.res N.subtype A) 2, ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0)
    (x : cohomology (A.quotientToInvariants N) 3) (hx : (cohomologyInfl A N 3).hom x = 0)
    (j : ℕ) (hj : ℓ ^ j • x = 0) : x = 0 := by
  have hX := coindShortComplex_shortExact A
  have hS := shortExact_map_res N hX
  have hQ := shortExact_map_quotientToInvariants_coindShortComplex A N h1
  have hδQ : IsIso (δ hQ (1 + 1) (1 + 1 + 1) rfl) := isIso_δ_of_isZero hQ 1
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N 1)
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N (1 + 1))
  have hδX : IsIso (δ hX (1 + 1) (1 + 1 + 1) rfl) := isIso_δ_of_isZero hX 1
    (isZero_cohomology_discreteCoind k G A 1) (isZero_cohomology_discreteCoind k G A (1 + 1))
  have hδS : IsIso (δ hS (0 + 1) (0 + 1 + 1) rfl) := isIso_δ_of_isZero hS 0
    (isZero_cohomology_res_discreteCoind (k := k) A N hN 0)
    (isZero_cohomology_res_discreteCoind (k := k) A N hN (0 + 1))
  have injQ : Function.Injective (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have injX : Function.Injective (δ hX (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have injS : Function.Injective (δ hS (0 + 1) (0 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have surjQ : Function.Surjective (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x', rfl⟩ := surjQ x
  have hsq := δ_comp_cohomologyInfl N hX hQ (1 + 1) (1 + 1 + 1) rfl
  have hx' : (cohomologyInfl (coindCokernel A) N (1 + 1)).hom x' = 0 := by
    have e : (δ hX (1 + 1) (1 + 1 + 1) rfl).hom ((cohomologyInfl (coindCokernel A) N (1 + 1)).hom x') =
        (cohomologyInfl A N 3).hom ((δ hQ (1 + 1) (1 + 1 + 1) rfl).hom x') :=
      (congrArg (fun φ => ModuleCat.Hom.hom φ x') hsq).symm
    exact injX (e.trans (hx.trans (map_zero _).symm))
  have hmem : x' ∈ LinearMap.ker (cohomologyInfl (coindCokernel A) N 2).hom := hx'
  rw [← (fiveTerm_exact (coindCokernel A) N hN).2.2.2] at hmem
  obtain ⟨w, rfl⟩ := hmem
  obtain ⟨m, hm, hmw⟩ := h2 ((δ hS (0 + 1) (0 + 1 + 1) rfl).hom w.1)
  have hw : m • w = 0 := by
    apply Subtype.ext
    apply injS
    exact (map_nsmul (δ hS (0 + 1) (0 + 1 + 1) rfl).hom m w.1).trans (hmw.trans (map_zero _).symm)
  have h1' : m • transgression (coindCokernel A) N hN w = 0 := by
    rw [← map_nsmul, hw, map_zero]
  have h2' : ℓ ^ j • transgression (coindCokernel A) N hN w = 0 := by
    apply injQ
    exact (map_nsmul _ (ℓ ^ j) _).trans (hj.trans (map_zero _).symm)
  have h0 := eq_zero_of_coprime_nsmul_of_pow_nsmul hm h1' h2'
  exact (congrArg (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom h0).trans (map_zero _)

section Extension

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem inv_mul_contractNth_mem {n : ℕ} (V : Subgroup G) [V.Normal] (g g' : Fin (n + 1) → G)
    (h : ∀ i, (g i)⁻¹ * g' i ∈ V) (j : Fin (n + 1)) (i : Fin n) :
    (Fin.contractNth j (· * ·) g i)⁻¹ * Fin.contractNth j (· * ·) g' i ∈ V := by
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hij, Fin.contractNth_apply_of_lt _ _ _ _ hij]
    exact h _
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ hij, Fin.contractNth_apply_of_eq _ _ _ _ hij]
    have h1 := h (Fin.castSucc i)
    have h2 := h i.succ
    have h3 : (g i.succ)⁻¹ * ((g (Fin.castSucc i))⁻¹ * g' (Fin.castSucc i)) * g i.succ ∈ V := by
      have := ‹V.Normal›.conj_mem _ h1 (g i.succ)⁻¹
      rwa [inv_inv] at this
    have := mul_mem h3 h2
    convert this using 1
    group
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ hij, Fin.contractNth_apply_of_gt _ _ _ _ hij]
    exact h _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem coe_contractNth {N : Subgroup G} {n : ℕ} (j : Fin (n + 1)) (g : Fin (n + 1) → N) (i : Fin n) :
    ((Fin.contractNth j (· * ·) g i : N) : G) = Fin.contractNth j (· * ·) (fun k => (g k : G)) i := by
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ h]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_eq _ _ _ _ h]
    rfl
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h, Fin.contractNth_apply_of_gt _ _ _ _ h]

end Extension

section ExtensionLemma

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]

theorem exists_isOpen_cohomologyResLE_eq (N : Subgroup G) (hN : IsClosed (N : Set G)) (n : ℕ)
    (y : cohomology (Rep.res N.subtype A) n) :
    ∃ (H : Subgroup G) (_ : IsOpen (H : Set G)) (hNH : N ≤ H)
      (y' : cohomology (Rep.res H.subtype A) n), (cohomologyResLE A hNH n).hom y' = y := by
  classical
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ n y
  set c : (Fin n → N) → A := cochainOf _ (cocycleι _ n z) with hc_def
  have hc : IsLocallyConstant c := isLocallyConstant_cochainOf _
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hc
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 U.isOpen'
  have hfin : (Set.range c).Finite := hc.range_finite
  set W : Set G := O ∩ ⋂ a ∈ Set.range c, (stabilizer A.ρ a : Set G) with hW
  have hWo : IsOpen W := hO.inter (hfin.isOpen_biInter fun a _ => isOpen_stabilizer A a)
  have hOU' : ∀ m : N, (m : G) ∈ O ↔ m ∈ U := fun m => Set.ext_iff.1 hOU m
  have h1O : (1 : G) ∈ O := by
    have : ((1 : N) : G) ∈ O := (hOU' 1).2 (one_mem U)
    simpa using this
  have h1W : (1 : G) ∈ W := ⟨h1O, Set.mem_iInter₂.2 fun a _ => (stabilizer A.ρ a).one_mem⟩
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
  have hVO : ∀ v ∈ (V : Subgroup G), v ∈ O := fun v hv => (hV hv).1
  have hVfix : ∀ v ∈ (V : Subgroup G), ∀ a ∈ Set.range c, A.ρ v a = a := fun v hv a ha =>
    (Set.mem_iInter₂.1 (hV hv).2 a ha)
  set H : Subgroup G := N ⊔ (V : Subgroup G)
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono le_sup_right V.isOpen'
  have hsel : ∀ h : H, ∃ m : N, ((m : G))⁻¹ * h ∈ (V : Subgroup G) := by
    intro h
    obtain ⟨m, hm, v, hv, hmv⟩ := Subgroup.mem_sup_of_normal_right.1 h.2
    exact ⟨⟨m, hm⟩, by rw [← hmv]; simpa using hv⟩
  choose sel hsel using hsel

  have hP : ∀ (x : Fin n → N) (x' : Fin n → N),
      (∀ i, ((x i : G))⁻¹ * x' i ∈ (V : Subgroup G)) → c x = c x' := by
    intro x x' hxx'
    apply hU
    intro i
    exact (hOU' _).1 (hVO _ (by simpa using hxx' i))
  set c' : (Fin n → H) → A := fun h => c (fun i => sel (h i)) with hc'_def
  have hP' : ∀ (x : Fin n → N) (h : Fin n → H),
      (∀ i, ((x i : G))⁻¹ * (h i : G) ∈ (V : Subgroup G)) → c' h = c x := by
    intro x h hxh
    refine (hP x (fun i => sel (h i)) fun i => ?_).symm
    have := mul_mem (hxh i) (inv_mem (hsel (h i)))
    convert this using 1
    group
  have hc' : IsLocallyConstant c' := by
    rw [IsLocallyConstant.iff_exists_open]
    intro h
    refine ⟨⋂ i, (fun h' : Fin n → H => ((h i : G))⁻¹ * (h' i : G)) ⁻¹' (V : Set G),
      isOpen_iInter_of_finite fun i => V.isOpen'.preimage
        (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))),
      Set.mem_iInter.2 fun i => by simp, fun h' hh' => ?_⟩
    have hh'' : ∀ i, ((h i : G))⁻¹ * (h' i : G) ∈ (V : Subgroup G) := fun i => Set.mem_iInter.1 hh' i
    refine (hP' (fun i => sel (h i)) h' fun i => ?_).trans rfl
    have := mul_mem (hsel (h i)) (hh'' i)
    convert this using 1
    group
  have t0 : ∀ h : Fin (n + 1) → H, (Rep.res H.subtype A).ρ (h 0) (c' fun i => h i.succ) =
      (Rep.res N.subtype A).ρ (sel (h 0)) (c fun i => sel (h i.succ)) := by
    intro h
    have hv := hsel (h 0)
    change A.ρ (h 0 : G) (c fun i => sel (h i.succ)) = A.ρ (sel (h 0) : G) (c fun i => sel (h i.succ))
    calc A.ρ (h 0 : G) (c fun i => sel (h i.succ))
        = A.ρ ((sel (h 0) : G) * ((sel (h 0) : G)⁻¹ * h 0)) (c fun i => sel (h i.succ)) := by
          rw [mul_inv_cancel_left]
      _ = A.ρ (sel (h 0) : G) (A.ρ ((sel (h 0) : G)⁻¹ * h 0) (c fun i => sel (h i.succ))) := by
          rw [map_mul]
          rfl
      _ = A.ρ (sel (h 0) : G) (c fun i => sel (h i.succ)) := by
          rw [hVfix _ hv _ ⟨_, rfl⟩]
  have tj : ∀ (h : Fin (n + 1) → H) (j : Fin (n + 1)),
      c' (Fin.contractNth j (· * ·) h) = c (Fin.contractNth j (· * ·) fun i => sel (h i)) := by
    intro h j
    refine hP' _ _ fun i => ?_
    rw [coe_contractNth, coe_contractNth]
    exact inv_mul_contractNth_mem (V : Subgroup G) (fun k => (sel (h k) : G)) (fun k => (h k : G))
      (fun k => hsel (h k)) j i
  have hdc : (inhomogeneousCochains.d (Rep.res H.subtype A) n).hom c' = 0 := by
    have hz := d_cocycleι z
    funext h
    have hz' := congrFun hz (fun i => sel (h i))
    rw [inhomogeneousCochains.d_hom_apply] at hz' ⊢
    rw [t0, Finset.sum_congr rfl fun j _ => by rw [tj h j]]
    exact hz'
  let z' : cocycles (Rep.res H.subtype A) n :=
    (cochainsComplex (Rep.res H.subtype A)).cyclesMk (mkCochain _ c' hc') (n + 1) (by simp) (by
      apply cochainOf_injective (A := Rep.res H.subtype A)
      exact (cochainOf_d _).trans hdc)
  have hz' : cochainOf _ (cocycleι _ n z') = c' :=
    congrArg (cochainOf (Rep.res H.subtype A)) ((cochainsComplex (Rep.res H.subtype A)).i_cyclesMk _ _ _ _)
  refine ⟨H, hHo, le_sup_left, cohomologyπ _ n z', ?_⟩
  rw [cohomologyResLE_eq, cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMapAlong, hz']
  funext g
  exact hP' g (fun i => Subgroup.inclusion le_sup_left (g i)) fun i => by simp

end ExtensionLemma

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

abbrev gsKernel : Subgroup K.1.fixingSubgroup := (gsRestrict K S).ker

theorem isClosed_gsKernel : IsClosed (gsKernel K S : Set K.1.fixingSubgroup) := by
  have ht2 : T2Space (galUnramifiedOutside K.1 ℚ̄ S) :=
    galois_t2Space K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
  have : T1Space (galUnramifiedOutside K.1 ℚ̄ S) := @T2Space.t1Space _ _ ht2
  exact (isClosed_singleton (x := (1 : galUnramifiedOutside K.1 ℚ̄ S))).preimage (continuous_gsRestrict K S)

theorem mem_gsKernel_iff (σ : K.1.fixingSubgroup) :
    σ ∈ gsKernel K S ↔ ∀ x ∈ maxUnramifiedOutside K.1 ℚ̄ S, (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) x = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x hx
    have := congrArg (fun τ : galUnramifiedOutside K.1 ℚ̄ S =>
      ((τ ⟨x, hx⟩ : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) h
    rw [gsRestrict_apply] at this
    exact this
  · intro h
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [gsRestrict_apply]
    exact h x x.2

theorem exists_finiteSubfield_of_isOpen (U : Subgroup K.1.fixingSubgroup)
    (hU : IsOpen (U : Set K.1.fixingSubgroup)) (hNU : gsKernel K S ≤ U) :
    ∃ (L : FiniteSubfield) (_ : Fact (K ≤ L)), (∀ x ∈ L.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S) ∧
      U = L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let U' : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄) := U.map K.1.fixingSubgroup.subtype
  have hKo : IsOpen (K.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := K.1.fixingSubgroup_isOpen
  have hU'o : IsOpen (U' : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
    have e : (U' : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) = Subtype.val '' (U : Set K.1.fixingSubgroup) := by
      ext σ
      simp [U', Subgroup.coe_map]
    rw [e]
    exact hKo.isOpenMap_subtype_val _ hU
  have hU'c : IsClosed (U' : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := Subgroup.isClosed_of_isOpen _ hU'o
  let L' : IntermediateField ℚ ℚ̄ := IntermediateField.fixedField U'
  have hfix : L'.fixingSubgroup = U' := InfiniteGalois.fixingSubgroup_fixedField ⟨U', hU'c⟩
  have hfin : FiniteDimensional ℚ L' := (InfiniteGalois.isOpen_iff_finite L').1 (hfix ▸ hU'o)
  let L : FiniteSubfield := ⟨L', hfin⟩
  have hmemU' : ∀ τ : K.1.fixingSubgroup, (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ U' ↔ τ ∈ U := fun τ =>
    Subgroup.mem_map_iff_mem K.1.fixingSubgroup.subtype_injective
  have hKL : K ≤ L := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.1 hσ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 τ.2 x hx
  refine ⟨L, ⟨hKL⟩, fun x hx => ?_, ?_⟩
  · let KS' : IntermediateField ℚ ℚ̄ := (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ
    have hx' : x ∈ IntermediateField.fixedField KS'.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hσK : σ ∈ K.1.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
          ((maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem (⟨y, hy⟩ : K.1))
      have hσN : (⟨σ, hσK⟩ : K.1.fixingSubgroup) ∈ gsKernel K S :=
        (mem_gsKernel_iff K S _).2 fun y hy =>
          (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y hy
      have hσU' : σ ∈ U' := (hmemU' ⟨σ, hσK⟩).2 (hNU hσN)
      exact (IntermediateField.mem_fixedField_iff _ _).1 hx σ hσU'
    rw [InfiniteGalois.fixedField_fixingSubgroup KS'] at hx'
    exact hx'
  · ext τ
    rw [Subgroup.mem_subgroupOf, ← hmemU', ← hfix]

theorem isZero_cohomology_one_gsKernel :
    IsZero (cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) 1) := by
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b => ?_⟩
  suffices h : ∀ y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) 1, y = 0 by
    rw [h a, h b]
  intro y
  obtain ⟨U, hU, hNU, y', rfl⟩ :=
    exists_isOpen_cohomologyResLE_eq (unitsLimitRep K) (gsKernel K S) (isClosed_gsKernel K S) 1 y
  obtain ⟨L, hL, -, rfl⟩ := exists_finiteSubfield_of_isOpen K S U hU hNU
  have hz : Subsingleton (cohomology (Rep.res (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).subtype
      (unitsLimitRep K)) 1) :=
    ModuleCat.subsingleton_of_isZero (isZero_cohomology_one_res_subgroupOf (K := K) (E := L))
  rw [Subsingleton.elim y' 0, map_zero]

theorem exists_unitsResField_eq_zero_of_pow_nsmul (L : FiniteSubfield) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (x : cohomology (unitsLimitRep L) 2) (k : ℕ) (hx : ℓ ^ k • x = 0) :
    ∃ (E : FiniteSubfield) (_ : Fact (L ≤ E)) (b : ℕ),
      E.1 = L.1 ⊔ Cyclotomic.rootsOfUnityField (ℓ ^ b) ∧ (unitsResField L E 2).hom x = 0 := by
  classical
  have hℓ2 : 2 < ℓ ^ 2 := by nlinarith [hℓ.two_le]
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hℓ.ne_zero⟩

  let F₂ : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ 2), inferInstance⟩
  let K' : FiniteSubfield := CyclotomicSymbol.compositum L F₂
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (F₂ ≤ K') := CyclotomicSymbol.fact_le_compositum_right L F₂
  have : IsTotallyComplex F₂.1 := IsCyclotomicExtension.Rat.isTotallyComplex (n := ℓ ^ 2) F₂.1 hℓ2
  let _ : Algebra F₂.1 K'.1 := FiniteSubfield.algebraOfLE (Fact.out : F₂ ≤ K')
  have : IsTotallyComplex K'.1 := NumberField.isTotallyComplex_of_algebra (F := F₂.1) K'.1
  obtain ⟨ι'⟩ := nonempty_localEmbeddings K'
  set x' := (unitsResField L K' 2).hom x with hx'
  have hm : (ℓ ^ k) • x' = 0 := by rw [hx', ← map_nsmul, hx, map_zero]

  let T : Finset (HeightOneSpectrum (𝓞 K'.1)) :=
    (brauerLocal ι' x').support.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨r, ⟨N, hr⟩, hdeg⟩ :=
    CyclotomicLayer.exists_pow_dvd_finrank_cyclotomicLayer K' T (pow_ne_zero k hℓ.ne_zero)
  let E' : FiniteSubfield := CyclotomicLayer.cyclotomicLayer K' r
  have hsplit : (unitsResField K' E' 2).hom x' = 0 := by
    refine unitsResField_eq_zero_of_dvd_finrank ι' x' (ℓ ^ k) hm (fun v => ?_) fun v hv w => ?_
    · have := subsingleton_cohomology_two_of_isComplex v (IsTotallyComplex.isComplex v)
      exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _
    · exact hdeg v (by rw [Finset.mem_preimage, DFinsupp.mem_support_iff]; exact hv) w

  let a := k * (N + 1)
  let b := a + Cyclotomic.unitsLevel ℓ + 2
  have : NeZero (ℓ ^ b) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  let F : FiniteSubfield := ⟨Cyclotomic.rootsOfUnityField (ℓ ^ b), inferInstance⟩
  let E : FiniteSubfield := CyclotomicSymbol.compositum L F
  have hrq : r = Cyclotomic.primePowPNat ℓ a := by
    apply PNat.eq
    rw [hr, Cyclotomic.coe_primePowPNat, ← pow_mul]
  have hF₂F : F₂.1 ≤ F.1 := rootsOfUnityField_pow_le (by omega)
  have hZF : (CyclotomicLayer.zhatLayer r).1 ≤ F.1 := by
    rw [hrq, CyclotomicLayer.zhatLayer_coe]
    exact (CyclotomicLayer.zhatLayerField_le_rootsOfUnityField ⟨ℓ, hℓ⟩ a).trans
      (rootsOfUnityField_pow_le (a := a + Cyclotomic.unitsLevel ℓ) (b := b) (by omega))
  have hE'E : E' ≤ E := by
    change (L.1 ⊔ F₂.1) ⊔ (CyclotomicLayer.zhatLayer r).1 ≤ L.1 ⊔ F.1
    exact sup_le (sup_le le_sup_left (hF₂F.trans le_sup_right)) (hZF.trans le_sup_right)
  have : Fact (E' ≤ E) := ⟨hE'E⟩
  have hres : (unitsResField L E 2).hom x = 0 := by
    have hKE' : Fact (L ≤ E') := ⟨(Fact.out : L ≤ K').trans (Fact.out : K' ≤ E')⟩
    have h1 := unitsResField_comp_unitsResField (K := L) (E := E') (M := E) 2
    have h2 := unitsResField_comp_unitsResField (K := L) (E := K') (M := E') 2
    rw [← h1, ConcreteCategory.comp_apply, ← h2, ConcreteCategory.comp_apply]
    change (unitsResField E' E 2).hom ((unitsResField K' E' 2).hom x') = 0
    rw [hsplit, map_zero]
  exact ⟨E, inferInstance, b, rfl, hres⟩

section SubgroupOf

variable {K}

abbrev unitsSubgroupOfMap (L : FiniteSubfield) [Fact (K ≤ L)] (n : ℕ) :
    cohomology (Rep.res (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).subtype (unitsLimitRep K)) n ⟶
      cohomology (unitsLimitRep L) n :=
  cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe
      (IntermediateField.fixingSubgroup_le (Fact.out : K ≤ L))).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom _ unitsRep) n

theorem unitsSubgroupOfMap_injective (L : FiniteSubfield) [Fact (K ≤ L)] (n : ℕ) :
    Function.Injective (unitsSubgroupOfMap (K := K) L n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

theorem fixingSubgroup_subgroupOf_mono {L E : FiniteSubfield} (h : L ≤ E) :
    E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup ≤ L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup :=
  fun _ hσ => IntermediateField.fixingSubgroup_le h hσ

theorem cohomologyResLE_comp_unitsSubgroupOfMap {L E : FiniteSubfield} [Fact (K ≤ L)] [Fact (K ≤ E)]
    [Fact (L ≤ E)] (n : ℕ) :
    cohomologyResLE (unitsLimitRep K) (fixingSubgroup_subgroupOf_mono (K := K) (Fact.out : L ≤ E)) n ≫
      unitsSubgroupOfMap E n = unitsSubgroupOfMap L n ≫ unitsResField L E n := by
  rw [cohomologyResLE_eq, ← cohomologyMapAlong_comp, unitsResField, ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext; rfl) (fun _ => rfl) n

end SubgroupOf

theorem exists_coprime_smul_cohomology_two_gsKernel {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (y : cohomology (Rep.res (gsKernel K S).subtype (unitsLimitRep K)) 2) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0 := by
  obtain ⟨U, hU, hNU, y', rfl⟩ :=
    exists_isOpen_cohomologyResLE_eq (unitsLimitRep K) (gsKernel K S) (isClosed_gsKernel K S) 2 y
  obtain ⟨L, hL, hLS, rfl⟩ := exists_finiteSubfield_of_isOpen K S U hU hNU
  set yL := (unitsSubgroupOfMap L 2).hom y'
  have htor := isTorsion_cohomology (unitsLimitRep L) (by norm_num : 1 ≤ 2) yL
  set M := addOrderOf yL
  have hM : M ≠ 0 := (IsOfFinAddOrder.addOrderOf_pos htor).ne'
  set a := M.factorization ℓ
  set M' := M / ℓ ^ a
  have hMN : ℓ ^ a * M' = M := Nat.ordProj_mul_ordCompl_eq_self M ℓ
  have hcop : Nat.Coprime M' ℓ := (Nat.coprime_ordCompl hℓ hM).symm
  have hz : ℓ ^ a • (M' • yL) = 0 := by
    rw [smul_smul, hMN]
    exact addOrderOf_nsmul_eq_zero yL
  obtain ⟨E, hE, b, hEb, hres⟩ := exists_unitsResField_eq_zero_of_pow_nsmul L hℓ (M' • yL) a hz
  have hES : ∀ x ∈ E.1, x ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
    have hle : E.1 ≤ (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ := by
      rw [hEb]
      refine sup_le (fun x hx => hLS x hx) fun x hx => ?_
      exact mem_maxUnramifiedOutside_of_mem_rootsOfUnityField hℓ hS b x hx
    exact fun x hx => hle hx
  have : Fact (K ≤ E) := ⟨hL.out.trans hE.out⟩
  have hNE : gsKernel K S ≤ E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
      (mem_gsKernel_iff K S σ).1 hσ x (hES x hx)
  have hEL := fixingSubgroup_subgroupOf_mono (K := K) hE.out

  have hr : (cohomologyResLE (unitsLimitRep K) hEL 2).hom (M' • y') = 0 := by
    apply unitsSubgroupOfMap_injective E 2
    have e := congrArg (fun φ => ModuleCat.Hom.hom φ (M' • y'))
      (cohomologyResLE_comp_unitsSubgroupOfMap (K := K) (L := L) (E := E) 2)
    refine e.trans ?_
    change (unitsResField L E 2).hom ((unitsSubgroupOfMap L 2).hom (M' • y')) = _
    rw [map_nsmul, hres, map_zero]
  refine ⟨M', hcop, ?_⟩
  rw [← map_nsmul, ← cohomologyResLE_comp (unitsLimitRep K) hEL hNE 2, ConcreteCategory.comp_apply, hr,
    map_zero]

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

theorem gsRestrict_surjective : Function.Surjective (gsRestrict K S) :=
  (gsRestrict_gsLift K S).surjective

def gsQuotientEquiv : galUnramifiedOutside K.1 ℚ̄ S ≃* K.1.fixingSubgroup ⧸ gsKernel K S :=
  (QuotientGroup.quotientKerEquivOfSurjective (gsRestrict K S) (gsRestrict_surjective K S)).symm

theorem gsQuotientEquiv_gsRestrict (σ : K.1.fixingSubgroup) :
    gsQuotientEquiv K S (gsRestrict K S σ) = QuotientGroup.mk σ := by
  rw [gsQuotientEquiv, MulEquiv.symm_apply_eq]
  rfl

theorem gsQuotientEquiv_symm_mk (σ : K.1.fixingSubgroup) :
    (gsQuotientEquiv K S).symm (QuotientGroup.mk σ) = gsRestrict K S σ := by
  rw [MulEquiv.symm_apply_eq, gsQuotientEquiv_gsRestrict]

theorem isQuotientMap_gsRestrict : Topology.IsQuotientMap (gsRestrict K S) := by
  have : T2Space (galUnramifiedOutside K.1 ℚ̄ S) := galois_t2Space K.1 (maxUnramifiedOutside K.1 ℚ̄ S)
  exact ((continuous_gsRestrict K S).isClosedMap).isQuotientMap (continuous_gsRestrict K S)
    (gsRestrict_surjective K S)

theorem continuous_gsQuotientEquiv : Continuous (gsQuotientEquiv K S).toMonoidHom := by
  rw [(isQuotientMap_gsRestrict K S).continuous_iff]
  have e : (gsQuotientEquiv K S).toMonoidHom ∘ gsRestrict K S = QuotientGroup.mk' (gsKernel K S) :=
    funext fun σ => gsQuotientEquiv_gsRestrict K S σ
  rw [e]
  exact continuous_quotientGroup_mk' _

theorem continuous_gsQuotientEquiv_symm : Continuous (gsQuotientEquiv K S).symm.toMonoidHom := by
  rw [(QuotientGroup.isQuotientMap_mk (gsKernel K S)).continuous_iff]
  have e : (gsQuotientEquiv K S).symm.toMonoidHom ∘ (QuotientGroup.mk : K.1.fixingSubgroup → _) =
      gsRestrict K S := funext fun σ => gsQuotientEquiv_symm_mk K S σ
  rw [e]
  exact continuous_gsRestrict K S

abbrev unitsInvariantsGsKernel :=
  Representation.invariants ((unitsLimitRep K).ρ.comp (gsKernel K S).subtype)

theorem mem_maxUnramifiedOutside_of_mem_invariantsGsKernel (a : unitsInvariantsGsKernel K S) :
    (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let KS' : IntermediateField ℚ ℚ̄ := (maxUnramifiedOutside K.1 ℚ̄ S).restrictScalars ℚ
  have h : (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) ∈
      IntermediateField.fixedField KS'.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hK : g ∈ K.1.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        ((maxUnramifiedOutside K.1 ℚ̄ S).algebraMap_mem (⟨y, hy⟩ : K.1))
    have hN : (⟨g, hK⟩ : K.1.fixingSubgroup) ∈ gsKernel K S :=
      (mem_gsKernel_iff K S _).2 fun y hy => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y hy
    have := a.2 ⟨⟨g, hK⟩, hN⟩
    exact congrArg (fun z : Additive ℚ̄ˣ => ((Additive.toMul z : ℚ̄ˣ) : ℚ̄)) this
  rw [InfiniteGalois.fixedField_fixingSubgroup KS'] at h
  exact h

def invariantsGsKernelFun : unitsInvariantsGsKernel K S →+ Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ where
  toFun a := Additive.ofMul (Units.mk0
      (⟨(((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄),
        mem_maxUnramifiedOutside_of_mem_invariantsGsKernel K S a⟩ : maxUnramifiedOutside K.1 ℚ̄ S)
      (fun h => (Additive.toMul (a : Additive ℚ̄ˣ)).ne_zero (congrArg Subtype.val h)))
  map_zero' := Additive.toMul.injective (Units.ext (Subtype.ext rfl))
  map_add' _ _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))

theorem coe_invariantsGsKernelFun (a : unitsInvariantsGsKernel K S) :
    ((((Additive.toMul (invariantsGsKernelFun K S a)) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) :
      maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = (((Additive.toMul (a : Additive ℚ̄ˣ)) : ℚ̄ˣ) : ℚ̄) :=
  rfl

theorem invariantsGsKernelFun_bijective : Function.Bijective (invariantsGsKernelFun K S) := by
  refine ⟨fun a b h => ?_, fun y => ?_⟩
  · apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    exact congrArg (fun z : Additive (maxUnramifiedOutside K.1 ℚ̄ S)ˣ =>
      (((Additive.toMul z : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) h
  · refine ⟨⟨Additive.ofMul (Units.map (maxUnramifiedOutside K.1 ℚ̄ S).val.toRingHom.toMonoidHom
      (Additive.toMul y)), fun σ => ?_⟩, ?_⟩
    · apply Additive.toMul.injective
      apply Units.ext
      have hσ := (mem_gsKernel_iff K S σ.1).1 σ.2 _ (Additive.toMul y : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ).1.2
      exact hσ
    · apply Additive.toMul.injective
      apply Units.ext
      apply Subtype.ext
      rfl

theorem invariantsGsKernelFun_smul (τ : galUnramifiedOutside K.1 ℚ̄ S) (a : unitsInvariantsGsKernel K S) :
    invariantsGsKernelFun K S
        ((((unitsLimitRep K).quotientToInvariants (gsKernel K S)).ρ (gsQuotientEquiv K S τ)) a) =
      (uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S))).ρ τ (invariantsGsKernelFun K S a) := by
  have hτ := gsRestrict_gsLift K S τ
  have h1 : gsQuotientEquiv K S τ = QuotientGroup.mk (gsLift K S τ) := by
    rw [← gsQuotientEquiv_gsRestrict, hτ]
  refine (congrArg (fun q => invariantsGsKernelFun K S
    ((((unitsLimitRep K).quotientToInvariants (gsKernel K S)).ρ q) a)) h1).trans ?_
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  have h2 := gsRestrict_apply K S (gsLift K S τ) ⟨_, mem_maxUnramifiedOutside_of_mem_invariantsGsKernel K S a⟩
  rw [hτ] at h2
  exact h2.symm

def invariantsGsKernelMor :
    Rep.res (gsQuotientEquiv K S).toMonoidHom ((unitsLimitRep K).quotientToInvariants (gsKernel K S)) ⟶
      uliftIntToIntRep (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) :=
  Rep.ofHom ⟨(invariantsGsKernelFun K S).toIntLinearMap, fun τ =>
    LinearMap.ext fun a => invariantsGsKernelFun_smul K S τ a⟩

instance isDiscreteRep_quotientToInvariants_gsKernel :
    IsDiscreteRep ((unitsLimitRep K).quotientToInvariants (gsKernel K S)) :=
  isDiscreteRep_quotientToInvariants_of_normal _ _

instance isIso_cohomologyMapAlong_invariantsGsKernelMor (n : ℕ) :
    IsIso (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom (continuous_gsQuotientEquiv K S)
      (invariantsGsKernelMor K S) n) :=
  isIso_cohomologyMapAlong_of_mulEquiv (gsQuotientEquiv K S) (continuous_gsQuotientEquiv K S)
    (continuous_gsQuotientEquiv_symm K S) _ (invariantsGsKernelFun_bijective K S) n

theorem cohomologyMapAlong_invariantsGsKernelMor_comp_gsBrauerInfl (n : ℕ) :
    cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom (continuous_gsQuotientEquiv K S)
      (invariantsGsKernelMor K S) n ≫ gsBrauerInfl K S n =
      cohomologyInfl (unitsLimitRep K) (gsKernel K S) n := by
  rw [gsBrauerInfl, ← cohomologyMapAlong_comp, cohomologyInfl]
  refine cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun σ => gsQuotientEquiv_gsRestrict K S σ)
    (fun a => ?_) n
  apply Additive.toMul.injective
  apply Units.ext
  exact coe_invariantsGsKernelFun K S a

set_option maxHeartbeats 1000000 in

theorem eq_zero_of_h3_gsUnits (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3) (k : ℕ) (hx : ℓ ^ k • x = 0) :
    x = 0 := by
  have hsurj : Function.Surjective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) 3).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hinj : Function.Injective (cohomologyMapAlong (gsQuotientEquiv K S).toMonoidHom
      (continuous_gsQuotientEquiv K S) (invariantsGsKernelMor K S) 3).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  obtain ⟨x0, hx0⟩ := hsurj (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3 x)
  have hk0 : ℓ ^ k • x0 = 0 := by
    apply hinj
    refine (map_nsmul _ (ℓ ^ k) x0).trans ?_
    refine (congrArg (fun z => ℓ ^ k • z) hx0).trans ?_
    refine (map_nsmul (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3)
      (ℓ ^ k) x).symm.trans ?_
    refine (congrArg _ hx).trans ?_
    exact (map_zero _).trans (map_zero _).symm
  have hinf : (cohomologyInfl (unitsLimitRep K) (gsKernel K S) 3).hom x0 = 0 := by
    have : Subsingleton (cohomology (unitsLimitRep K) 3) := subsingleton_cohomology_three_unitsLimitRep K
    exact Subsingleton.elim _ _
  have h0 := eq_zero_of_cohomologyInfl_three_eq_zero (unitsLimitRep K) (gsKernel K S)
    (isClosed_gsKernel K S) (isZero_cohomology_one_gsKernel K S) ℓ
    (exists_coprime_smul_cohomology_two_gsKernel K S hℓ hS) x0 hinf k hk0
  apply (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 3).injective
  rw [← hx0, h0, map_zero, map_zero]

end

end GroundTheory.ProfCoh
end
