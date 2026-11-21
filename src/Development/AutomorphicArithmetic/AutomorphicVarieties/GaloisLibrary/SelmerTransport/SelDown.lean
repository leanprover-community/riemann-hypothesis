import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_le_of_ker_le {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {C : Type} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B)
    (g : LinearMap.ker f →ₗ[R] C) (hg : Function.Injective g) :
    Module.length R A ≤ Module.length R C + Module.length R B := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))]
  exact add_le_add (Module.length_le_of_injective g hg)
    (Module.length_le_of_injective (LinearMap.range f).subtype (Submodule.subtype_injective _))

theorem UpperTheory.V.Base.selLocal :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R ((LocSel ρ U' 𝒟).comap (resU ρ h)) ≤ Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 ι _ D hD hcov
  set X := (LocSel ρ U' 𝒟).comap (resU ρ h) with hX
  have key0 : ∀ x ∈ X, ∀ D' ∈ 𝒟, resU ρ (le_trans inf_le_left h : U' ⊓ D' ≤ U) x = 0 := by
    intro x hx D' hD'
    have e := (mem_locSel.mp (Submodule.mem_comap.mp hx)) D' hD'
    rw [resU_resU] at e
    exact e
  have key : ∀ x ∈ X, ∀ D' ∈ 𝒟,
      resU ρ (inf_le_inf_right D' h) (resU ρ (inf_le_left : U ⊓ D' ≤ U) x) = 0 := by
    intro x hx D' hD'
    rw [resU_resU]
    exact key0 x hx D' hD'
  let f : X →ₗ[R] (∀ i, LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) :=
    LinearMap.pi fun i => LinearMap.codRestrict _
      ((resU ρ (inf_le_left : U ⊓ D i ≤ U)).comp X.subtype)
      (fun x => LinearMap.mem_ker.mpr (key x.1 x.2 (D i) (hD i)))
  have hmem : ∀ y ∈ LinearMap.ker f, ((y : H1U ρ U)) ∈ LocSel ρ U 𝒟 := by
    intro y hy
    have hy' : ∀ i, resU ρ (inf_le_left : U ⊓ D i ≤ U) (y : H1U ρ U) = 0 := by
      intro i
      simpa [f] using congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hy) i)
    rw [mem_locSel]
    intro D' hD'
    rcases hcov D' hD' with hle | ⟨i, u, hu, hconj⟩
    · have e := resU_resU ρ (le_inf hle inf_le_right : U ⊓ D' ≤ U' ⊓ D')
        (le_trans inf_le_left h) (y : H1U ρ U)
      rw [key0 _ y.2 D' hD', map_zero] at e
      exact e.symm
    · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (y : H1U ρ U)
      have h0 := hy' i
      rw [← hz] at h0 ⊢
      rw [resU_mk_eq_zero] at h0 ⊢
      obtain ⟨m, hm⟩ := h0
      refine ⟨ρ u m - z.1 ⟨u, hu⟩, fun v => ?_⟩
      have hvU : (v : G) ∈ U := (Subgroup.mem_inf.mp v.2).1
      have hwD : u⁻¹ * (v : G) * u ∈ D i := hconj v v.2
      have hwU : u⁻¹ * (v : G) * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) hvU) hu
      have e1 : z.1 ⟨u⁻¹ * (v : G) * u, hwU⟩ = ρ (u⁻¹ * (v : G) * u) m - m :=
        hm ⟨u⁻¹ * (v : G) * u, Subgroup.mem_inf.mpr ⟨hwU, hwD⟩⟩
      have hc := z.2.2
      have c1 := hc ⟨v, hvU⟩ ⟨u, hu⟩
      have c2 := hc ⟨u, hu⟩ ⟨u⁻¹ * (v : G) * u, hwU⟩
      have eq : (⟨v, hvU⟩ * ⟨u, hu⟩ : U) = ⟨u, hu⟩ * ⟨u⁻¹ * (v : G) * u, hwU⟩ :=
        Subtype.ext (by simp [mul_assoc])
      rw [eq, c2, e1] at c1
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at c1
      have hr : ρ u (ρ (u⁻¹ * (v : G) * u) m) = ρ v (ρ u m) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [map_sub, hr] at c1
      show z.1 ⟨v, hvU⟩ = _
      rw [eq_sub_of_add_eq c1.symm]
      simp only [map_sub]
      abel
  let g : LinearMap.ker f →ₗ[R] LocSel ρ U 𝒟 :=
    LinearMap.codRestrict _ (X.subtype.comp (LinearMap.ker f).subtype) (fun y => hmem y.1 y.2)
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have e := congrArg Subtype.val hab
    exact e
  have e := length_le_of_ker_le f g hg
  rwa [Module.length_pi_of_fintype] at e
end

section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_addMonoidHom_le_of_card_eq {R A B C X : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup X] [Module R X]
    (f : A →ₗ[R] X) (j : B →ₗ[R] X) (hj : Function.Injective j) (g : B →ₗ[R] C)
    (h : ∀ x, g x = 0 → j x ∈ LinearMap.range f) :
    Module.length R B ≤ Module.length R A + Module.length R C := by
  have hex : Function.Exact (LinearMap.ker g).subtype g.rangeRestrict := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      have := congrArg Subtype.val hx
      simpa [LinearMap.mem_ker] using this
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simpa using y.2
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict hex]
  gcongr
  · let φ : LinearMap.ker g →ₗ[R] LinearMap.range f :=
      (j.comp (LinearMap.ker g).subtype).codRestrict (LinearMap.range f) (fun x => h x x.2)
    have hφ : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply hj
      exact congrArg Subtype.val hab
    calc Module.length R (LinearMap.ker g) ≤ Module.length R (LinearMap.range f) :=
          Module.length_le_of_injective φ hφ
      _ ≤ Module.length R A := Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  · exact Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)

theorem UpperTheory.V.Base.selDown :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟) (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R (selEig ρ U' h𝒟 U 1) ≤ Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) + Module.length R (resCoker ρ h) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U _ h 𝒟 h𝒟 ι _ D hD hcov
  have hinv : ∀ x : selEig ρ U' h𝒟 U 1,
      ((x : LocSel ρ U' 𝒟) : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U' := by
    intro x
    rw [Representation.mem_invariants]
    intro u
    have := (mem_eig.mp x.2) u
    simpa [selRep, Representation.subrepresentation] using congrArg Subtype.val this
  let j : selEig ρ U' h𝒟 U 1 →ₗ[R] H1U ρ U' :=
    (LocSel ρ U' 𝒟).subtype.comp (selEig ρ U' h𝒟 U 1).subtype
  let g : selEig ρ U' h𝒟 U 1 →ₗ[R] resCoker ρ h :=
    (Submodule.mkQ _).comp (LinearMap.codRestrict (invariantsUnderSubgroupH1 ρ U U') j hinv)
  let A := Submodule.comap (resU ρ h) (LocSel ρ U' 𝒟)
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hker : ∀ x, g x = 0 → j x ∈ LinearMap.range ((resU ρ h).comp A.subtype) := by
    intro x hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨⟨y, ?_⟩, hy⟩
    show resU ρ h y ∈ LocSel ρ U' 𝒟
    rw [hy]
    exact (x : LocSel ρ U' 𝒟).2
  refine le_trans (length_addMonoidHom_le_of_card_eq ((resU ρ h).comp A.subtype) j hj g hker) ?_
  gcongr
  exact selLocal R G M ρ U' U h 𝒟 ι D hD hcov
end
