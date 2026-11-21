import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt

section
private theorem starProjection_apply_comm_of_invariant_adjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (Y : Submodule ℂ H) [Y.HasOrthogonalProjection] (B C : H →L[ℂ] H)
    (hB : ∀ y ∈ Y, B y ∈ Y) (hC : ∀ y ∈ Y, C y ∈ Y)
    (hBC : ContinuousLinearMap.adjoint B = C) (x : H) :
    Y.starProjection (B x) = B (Y.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal' (z := B (x - Y.starProjection x))
    (hB _ (Y.starProjection_apply_mem x))
  · rw [Submodule.mem_orthogonal]
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left, hBC]
    exact Submodule.inner_right_of_mem_orthogonal (hC y hy)
      (Submodule.sub_starProjection_mem_orthogonal (K := Y) x)
  · rw [← map_add, add_sub_cancel]

private theorem exists_finiteDimensional_invariant_le_of_fg {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : ι → H →L[ℂ] H) (W M : Submodule ℂ H) (hM : M.FG) (hMW : M ≤ W)
    (hW : ∀ w ∈ W, ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ w ∈ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y) :
    ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ M ≤ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have key : ∀ t : Finset H, (↑t : Set H) ⊆ W → ∃ Y ≤ W, FiniteDimensional ℂ Y ∧
      (↑t : Set H) ⊆ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨⊥, bot_le, inferInstance, by simp, fun i y hy => ?_⟩
      rw [(Submodule.mem_bot ℂ).1 hy, map_zero]
      exact Submodule.zero_mem _
    | insert a t ha ih =>
      intro hsub
      rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨Y1, h1W, h1f, h1t, h1A⟩ := ih hsub.2
      obtain ⟨Y2, h2W, h2f, h2a, h2A⟩ := hW a hsub.1
      haveI := h1f
      haveI := h2f
      refine ⟨Y1 ⊔ Y2, sup_le h1W h2W, inferInstance, ?_, ?_⟩
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨Submodule.mem_sup_right h2a, h1t.trans (SetLike.coe_subset_coe.2 le_sup_left)⟩
      · intro i y hy
        obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add]
        exact Submodule.add_mem_sup (h1A i y1 hy1) (h2A i y2 hy2)
  obtain ⟨Y, hYW, hYf, hsY, hYA⟩ := key s (Submodule.span_le.1 hMW)
  exact ⟨Y, hYW, hYf, Submodule.span_le.2 hsY, hYA⟩

theorem UpperTheory.V.KernelIndexFullLattice.absApprox_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsApprox := by
  intro ι H _ _ _ A hA W N hN hW v hv hP
  classical
  haveI := hN
  have hfg : (N ⊓ W).FG := by
    haveI : FiniteDimensional ℂ ↥(N ⊓ W) := Submodule.finiteDimensional_of_le inf_le_left
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  obtain ⟨Y0, hY0W, hY0f, hNY0, hY0A⟩ := exists_finiteDimensional_invariant_le_of_fg A W (N ⊓ W) hfg inf_le_right hW
  haveI := hY0f
  have hproj : ∀ (Y : Submodule ℂ H) [FiniteDimensional ℂ Y], Y ≤ W →
      (∀ i, ∀ y ∈ Y, A i y ∈ Y) → Y0 ≤ Y → Y0.starProjection v = Y.starProjection v := by
    intro Y _ hYW hYA hY0Y
    have h1 : Y.starProjection v ∈ N := by
      apply hP
      · intro i x
        obtain ⟨j, hj⟩ := hA i
        exact starProjection_apply_comm_of_invariant_adjoint Y (A i) (A j) (hYA i) (hYA j) hj x
      · intro x
        exact hYW (Y.starProjection_apply_mem x)
    have h2 : Y.starProjection v ∈ Y0 := hNY0 ⟨h1, hYW (Y.starProjection_apply_mem v)⟩
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero h2
    intro w hw
    exact Submodule.starProjection_inner_eq_zero v w (hY0Y hw)
  have horth : ∀ w ∈ W, inner ℂ w (v - Y0.starProjection v) = 0 := by
    intro w hw
    obtain ⟨Y1, h1W, h1f, hw1, h1A⟩ := hW w hw
    haveI := h1f
    have hY := hproj (Y0 ⊔ Y1) (sup_le hY0W h1W) (fun i y hy => by
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add]
      exact Submodule.add_mem_sup (hY0A i y1 hy1) (h1A i y2 hy2)) le_sup_left
    rw [hY, inner_eq_zero_symm]
    exact Submodule.starProjection_inner_eq_zero v w (Submodule.mem_sup_right hw1)
  have hcl : v - Y0.starProjection v ∈ W.topologicalClosure :=
    W.topologicalClosure.sub_mem hv
      (W.le_topologicalClosure (hY0W (Y0.starProjection_apply_mem v)))
  have hsub : closure (W : Set H) ⊆ {x | inner ℂ x (v - Y0.starProjection v) = 0} :=
    closure_minimal horth (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
  have hzero : inner ℂ (v - Y0.starProjection v) (v - Y0.starProjection v) = 0 := by
    apply hsub
    rw [← Submodule.topologicalClosure_coe]
    exact hcl
  rw [inner_self_eq_zero, sub_eq_zero] at hzero
  rw [hzero]
  exact hY0W (Y0.starProjection_apply_mem v)
end

section
open GroundTheory.Automorphic

private theorem UpperTheory.V.KernelIndexFullLattice.orbit_finite {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (v : V)
    (hv : IsOpen {g : G | τ g v = v}) (U : Set G) (hU : IsCompact U) :
    ((fun g => τ g v) '' U).Finite := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun g : G => (fun x : G => g⁻¹ * x) ⁻¹' {h : G | τ h v = v})
    (fun g => hv.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine (t.finite_toSet.image (fun g => τ g v)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (ht hx)
  have hs : τ (g⁻¹ * x) v = v := hxg
  refine ⟨g, hg, ?_⟩
  have e : x = g * (g⁻¹ * x) := by group
  show τ g v = τ x v
  rw [e, map_mul, Module.End.mul_apply, hs]

private theorem UpperTheory.V.KernelIndexFullLattice.mul_two_dim_algebra_stable {C G : Type*} [Group C] [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ C V) (τ : Representation ℂ G V)
    (hσ : ∀ v : V, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : C => σ k v)))
    (hc : ∀ k g, σ k * τ g = τ g * σ k) (U : Subgroup G) (v : V)
    (hf : ((fun g => τ g v) '' (U : Set G)).Finite) :
    ∃ Y : Submodule ℂ V, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ (∀ k, ∀ y ∈ Y, σ k y ∈ Y) ∧
      ∀ u ∈ U, ∀ y ∈ Y, τ u y ∈ Y := by
  classical
  let Y : Submodule ℂ V := hf.toFinset.sup (fun w => Submodule.span ℂ (Set.range fun k : C => σ k w))
  have mem : ∀ w ∈ (fun g => τ g v) '' (U : Set G), ∀ k, σ k w ∈ Y := by
    intro w hw k
    exact Finset.le_sup (f := fun w => Submodule.span ℂ (Set.range fun k : C => σ k w))
      (hf.mem_toFinset.2 hw) (Submodule.subset_span ⟨k, rfl⟩)
  have stab : ∀ φ : Module.End ℂ V,
      (∀ w ∈ (fun g => τ g v) '' (U : Set G), ∀ k, φ (σ k w) ∈ Y) → ∀ y ∈ Y, φ y ∈ Y := by
    intro φ hφ y hy
    have hle : Y ≤ Y.comap φ := by
      refine Finset.sup_le fun w hw => ?_
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hφ w (hf.mem_toFinset.1 hw) k
    exact hle hy
  refine ⟨Y, ?_, ?_, ?_, ?_⟩
  · refine Finset.sup_induction (p := fun N : Submodule ℂ V => FiniteDimensional ℂ N) ?_ ?_ ?_
    · exact inferInstance
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
    · intro w _
      exact hσ w
  · have h1 := mem v ⟨1, U.one_mem, by simp⟩ 1
    simpa using h1
  · intro k
    refine stab (σ k) ?_
    intro w hw k'
    rw [← Module.End.mul_apply, ← map_mul]
    exact mem w hw _
  · intro u hu
    refine stab (τ u) ?_
    rintro _ ⟨g, hg, rfl⟩ k
    have e : τ u (σ k (τ g v)) = σ k (τ (u * g) v) := by
      rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (τ u) (σ k), ← hc k u,
        Module.End.mul_apply]
    rw [e]
    exact mem _ ⟨u * g, U.mul_mem hu hg, rfl⟩ k

theorem UpperTheory.V.KernelIndexFullLattice.stabFin_holds :
    UpperTheory.V.KernelIndexFullLattice.StabFin := by
  intro K _ _ n V _ _ M hM U hU v
  exact UpperTheory.V.KernelIndexFullLattice.mul_two_dim_algebra_stable M.gk.σ M.τ M.gk.locallyFinite M.comm_σ U v
    (UpperTheory.V.KernelIndexFullLattice.orbit_finite M.τ v (hM v) _ hU)
end

section
open GroundTheory.Automorphic

private theorem UpperTheory.V.KernelIndexFullLattice.homFin_comp {R B S : Type} [Ring R] [AddCommGroup B] [Module R B]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    isotypicComponent R B S = ⊥ ∨ isotypicComponent R B S ∈ isotypicComponents R B := by
  by_cases h : isotypicComponent R B S = ⊥
  · exact Or.inl h
  · right
    obtain ⟨m, ⟨e⟩, -⟩ : ∃ m ∈ {m : Submodule R B | Nonempty (m ≃ₗ[R] S)}, m ≠ ⊥ := by
      by_contra hc
      push_neg at hc
      exact h (sSup_eq_bot.mpr hc)
    haveI : IsSimpleModule R m := IsSimpleModule.congr e
    exact ⟨m, inferInstance, e.isotypicComponent_eq.symm⟩

theorem UpperTheory.V.KernelIndexFullLattice.homFin_holds :
    UpperTheory.V.KernelIndexFullLattice.HomFin := by
  intro C M X _ _ _ _ _ _ _ _ _ _ σ hσ τ hτ F hF
  have hτK : CompactRep.IsKFinite τ := ⟨fun _ => inferInstance, hτ⟩
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ C) τ.asModule := CompactRep.isSemisimpleModule_asModule hτK
  haveI : IsNoetherian ℂ τ.asModule := inferInstanceAs (IsNoetherian ℂ X)
  haveI hτT : IsScalarTower ℂ (MonoidAlgebra ℂ C) τ.asModule := by
    refine ⟨fun c a v => ?_⟩
    show τ.asAlgebraHom (c • a) _ = c • τ.asAlgebraHom a _
    rw [map_smul]
    rfl
  haveI hσT : IsScalarTower ℂ (MonoidAlgebra ℂ C) σ.asModule := by
    refine ⟨fun c a v => ?_⟩
    show σ.asAlgebraHom (c • a) _ = c • σ.asAlgebraHom a _
    rw [map_smul]
    rfl
  haveI : IsNoetherian (MonoidAlgebra ℂ C) τ.asModule := isNoetherian_of_tower ℂ inferInstance
  obtain ⟨t, ht, htop⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact
    (Submodule (MonoidAlgebra ℂ C) τ.asModule) {m | IsSimpleModule (MonoidAlgebra ℂ C) m}
  rw [IsSemisimpleModule.sSup_simples_eq_top] at htop
  let W : Submodule (MonoidAlgebra ℂ C) τ.asModule → Submodule ℂ M := fun m =>
    F ⊓ ((isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m).restrictScalars ℂ : Submodule ℂ σ.asModule)
  refine ⟨t.sup W, ?_, ?_⟩
  · refine Finset.sup_induction (p := fun N : Submodule ℂ M => FiniteDimensional ℂ N) ?_ ?_ ?_
    · exact inferInstance
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
    · intro m hm
      haveI : IsSimpleModule (MonoidAlgebra ℂ C) m := ht hm
      rcases UpperTheory.V.KernelIndexFullLattice.homFin_comp (R := MonoidAlgebra ℂ C) (B := σ.asModule) (S := m) with h | hc
      · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
        intro v hv
        have hv2 : (show σ.asModule from v) ∈ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m := hv.2
        rw [h] at hv2
        have hv0 : (show σ.asModule from v) = 0 := (Submodule.mem_bot (MonoidAlgebra ℂ C)).1 hv2
        exact (Submodule.mem_bot ℂ).2 hv0
      · haveI := hF _ hc
        refine Submodule.finiteDimensional_of_le
          (S₂ := LinearMap.range (CompactRep.kProj hσ hc ∘ₗ F.subtype)) ?_
        intro v hv
        exact ⟨⟨v, hv.1⟩, (CompactRep.kProj_apply_eq_self_iff hσ hc).2 hv.2⟩
  · intro f hf hFf x
    let f' : τ.asModule →ₗ[ℂ] σ.asModule :=
      σ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ τ.asModuleEquiv.toLinearMap
    let g : τ.asModule →ₗ[MonoidAlgebra ℂ C] σ.asModule :=
      MonoidAlgebra.equivariantOfLinearOfComm f'
        (fun k v => by
          simp [f']
          exact hf k v)
    have hg : ∀ y : τ.asModule, g y = f y := fun y => rfl
    have one : ∀ m ∈ t, ∀ y ∈ m, g y ∈ t.sup W := by
      intro m hm y hy
      haveI : IsSimpleModule (MonoidAlgebra ℂ C) m := ht hm
      refine Finset.le_sup (f := W) hm ⟨?_, ?_⟩
      · rw [hg]
        exact hFf y
      show g y ∈ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m
      rcases (g.domRestrict m).injective_or_eq_zero with hi | h0
      · have hle : LinearMap.range (g.domRestrict m) ≤ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m :=
          le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
        exact hle ⟨⟨y, hy⟩, rfl⟩
      · have h1 : g y = 0 := by simpa using LinearMap.congr_fun h0 ⟨y, hy⟩
        rw [h1]
        exact zero_mem _
    have key : ∀ s : Finset (Submodule (MonoidAlgebra ℂ C) τ.asModule), s ⊆ t →
        ∀ y ∈ s.sup id, g y ∈ t.sup W := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _ y hy
        have hy0 : y = 0 := by simpa using hy
        rw [hy0, map_zero]
        exact zero_mem _
      | insert a s ha ih =>
        intro hs y hy
        rw [Finset.sup_insert] at hy
        obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add]
        exact add_mem (one a (hs (Finset.mem_insert_self a s)) y1 hy1)
          (ih ((Finset.subset_insert a s).trans hs) y2 hy2)
    have hx : (show τ.asModule from x) ∈ t.sup id := htop ▸ Submodule.mem_top
    have := key t subset_rfl _ hx
    rw [hg] at this
    exact this
end

section
open NumberField MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem UpperTheory.V.KernelIndexFullLattice.pvFin_abs {G E M : Type} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [AddCommGroup M] [Module ℂ M]
    (C : Subgroup G) [IsTopologicalGroup C] [CompactSpace C] [T2Space C] (ρ : BanachRep G E)
    (σ : Representation ℂ C M) (hσ : CompactRep.IsKFinite σ) (j : M →ₗ[ℂ] E) (hj : Function.Injective j)
    (hjσ : ∀ (k : C) m, j (σ k m) = ρ k (j m)) (F : Submodule ℂ M)
    (hF : ∀ (c : Submodule (MonoidAlgebra ℂ C) σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ C) σ.asModule),
      FiniteDimensional ℂ (LinearMap.range (CompactRep.kProj hσ hc ∘ₗ F.subtype)))
    (v : E) (hv : FiniteDimensional ℂ (ρ.kSpan C v)) :
    ∃ N : Submodule ℂ E, FiniteDimensional ℂ N ∧ ∀ P : E →L[ℂ] E,
      (∀ (k : C) x, P (ρ k x) = ρ k (P x)) → (∀ x ∈ ρ.kSpan C v, ∃ m ∈ F, j m = P x) → P v ∈ N := by
  let S : Subrepresentation (ρ.restrict C).toRepresentation :=
    ⟨ρ.kSpan C v, fun k _ hw => ρ.map_mem_kSpan_of_mem C hw k⟩
  have hc : Representation.HasContinuousCoeff (W := ρ.kSpan C v) S.toRepresentation := by
    intro φ w
    refine φ.continuous_of_finiteDimensional.comp ?_
    exact Continuous.subtype_mk ((ρ.continuous_orbit (w : E)).comp continuous_subtype_val) _
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.homFin_holds C M (ρ.kSpan C v) σ hσ S.toRepresentation hc F hF
  refine ⟨N.map j, inferInstance, fun P hP hPF => ?_⟩
  have hr : ∀ x : ρ.kSpan C v, ((P : E →ₗ[ℂ] E) ∘ₗ (ρ.kSpan C v).subtype) x ∈ LinearMap.range j := by
    intro x
    obtain ⟨m, -, hm⟩ := hPF x x.2
    exact ⟨m, hm⟩
  let f : ρ.kSpan C v →ₗ[ℂ] M := (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range j) _ hr
  have hf : ∀ x, j (f x) = P x := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply ⟨_, hr x⟩)
  refine ⟨f ⟨v, ρ.mem_kSpan_self C v⟩, hN' f (fun k x => hj ?_) (fun x => ?_) _, hf _⟩
  · rw [hjσ, hf, hf, ← hP]
    rfl
  · obtain ⟨m, hm, e⟩ := hPF x x.2
    rwa [hj ((hf x).trans e.symm)]

theorem UpperTheory.V.KernelIndexFullLattice.pvFin_holds :
    UpperTheory.V.KernelIndexFullLattice.PvFin := by
  intro K _ _ n μ₁ _ π U hUc hUo v hv hfin
  let j : π.carrier →ₗ[ℂ] CuspL2 μ₁ := cuspVecL μ₁ ∘ₗ π.carrier.subtype
  have hj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun m hm => Subtype.ext ?_
    exact eq_zero_of_cuspVecL_eq_zero (μ := μ₁) (π.le_central m.2) hm
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.pvFin_abs (archCompact K n) (archRepT μ₁) π.toModule.gk.σ
    π.toModule.gk.isKFinite j hj (fun k m => cuspToL2_sigma μ₁ k (π.le_central m.2))
    (fixedVectors π.toModule.τ U) (π.isAdmissible.2 U hUc hUo) v hfin
  refine ⟨N, hN, fun P hPk hPu hP => hN' P hPk fun x hx => ?_⟩
  have hxU : ∀ u ∈ U, cuspRepT μ₁ (retractOne (finEmb K n u)) x = x := by
    intro u hu
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have hcomm : retractOne (finEmb K n u) * archP K n k = archP K n k * retractOne (finEmb K n u) := by
        rw [← retract_infEmb, ← retractOne_mul, ← retractOne_mul, infEmb_mul_finEmb_comm]
      have h1 := (cuspRepT μ₁).map_mul_apply (retractOne (finEmb K n u)) (archP K n k) v
      have h2 := (cuspRepT μ₁).map_mul_apply (archP K n k) (retractOne (finEmb K n u)) v
      rw [hv u hu, ← hcomm, h1] at h2
      exact h2
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  obtain ⟨φ, hφ, e⟩ := hP x
  refine ⟨⟨φ, hφ⟩, fun u hu => hj ?_, e⟩
  have h := cuspToL2_finRepCusp μ₁ u (π.le_central hφ)
  rw [e, ← hPu u hu, hxU u hu, ← e] at h
  exact h
end

section
open NumberField MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.kFinMem_holds :
    UpperTheory.V.KernelIndexFullLattice.KFinMem := by
  intro K _ _ n μ₁ _ π v hv hop hfin
  have h1 : retractOne (1 : AdelicGLn.AdelicGL K n) = 1 := retractOne_coe (1 : Reduction.normOneGL K n)
  let r : AdelicGLn.FiniteAdelicGL K n →* Reduction.normOneGL K n :=
    { toFun := fun h => retractOne (finEmb K n h)
      map_one' := by rw [map_one, h1]
      map_mul' := fun a b => by rw [map_mul, retractOne_mul] }
  let S : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {h | cuspRepT μ₁ (r h) v = v}
      one_mem' := by
        show cuspRepT μ₁ (r 1) v = v
        rw [map_one r]
        simp
      mul_mem' := fun {a b} ha hb => by
        have ha' : cuspRepT μ₁ (r a) v = v := ha
        have hb' : cuspRepT μ₁ (r b) v = v := hb
        show cuspRepT μ₁ (r (a * b)) v = v
        rw [map_mul r, UnitaryRep.map_mul_apply, hb', ha']
      inv_mem' := fun {a} ha => by
        have ha' : cuspRepT μ₁ (r a) v = v := ha
        show cuspRepT μ₁ (r a⁻¹) v = v
        have h := (cuspRepT μ₁).map_mul_apply (r a⁻¹) (r a) v
        rw [ha', ← map_mul r, inv_mul_cancel, map_one r] at h
        rw [← h]
        simp }
  have hSo : IsOpen (S : Set (AdelicGLn.FiniteAdelicGL K n)) := hop
  let U : Subgroup (AdelicGLn.FiniteAdelicGL K n) := S ⊓ AdelicGLn.integralFiniteGL K n
  have hUo : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := hSo.inter (AdelicGLn.isOpen_integralFiniteGL K n)
  have hUc : IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (U.isClosed_of_isOpen hUo) fun _ h => h.2
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.pvFin_holds K n μ₁ π U hUc hUo v (fun u hu => hu.1) hfin
  let A : archCompact K n ⊕ U → CuspL2 μ₁ →L[ℂ] CuspL2 μ₁ :=
    Sum.elim (fun k => cuspRepT μ₁ (archP K n k)) fun u => cuspRepT μ₁ (r u)
  refine UpperTheory.V.KernelIndexFullLattice.absApprox_holds (archCompact K n ⊕ U) (CuspL2 μ₁) A ?_ _ N hN ?_ v hv
    fun P hP hPW => hN' P (fun k x => hP (.inl k) x) (fun u hu x => hP (.inr ⟨u, hu⟩) x) hPW
  · rintro (k | u)
    · refine ⟨.inl k⁻¹, ?_⟩
      show ContinuousLinearMap.adjoint (cuspRepT μ₁ (archP K n k)) = cuspRepT μ₁ (archP K n (k : archGroup K n)⁻¹)
      rw [UnitaryRep.adjoint_map, map_inv (archP K n)]
    · refine ⟨.inr u⁻¹, ?_⟩
      show ContinuousLinearMap.adjoint (cuspRepT μ₁ (r u)) =
        cuspRepT μ₁ (r (u : AdelicGLn.FiniteAdelicGL K n)⁻¹)
      rw [UnitaryRep.adjoint_map, map_inv r]
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨Y, hY, hφY, hk, hu⟩ :=
      UpperTheory.V.KernelIndexFullLattice.stabFin_holds K n π.carrier π.toModule π.isAdmissible.1 U hUc ⟨φ, hφ⟩
    let j : π.carrier →ₗ[ℂ] CuspL2 μ₁ := cuspVecL μ₁ ∘ₗ π.carrier.subtype
    refine ⟨Y.map j, ?_, inferInstance, ⟨_, hφY, rfl⟩, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro (k | u) _ ⟨y, hy, rfl⟩
      · exact ⟨_, hk k y hy, cuspToL2_sigma μ₁ k (π.le_central y.2)⟩
      · exact ⟨_, hu u u.2 y hy, cuspToL2_finRepCusp μ₁ u (π.le_central y.2)⟩
end
