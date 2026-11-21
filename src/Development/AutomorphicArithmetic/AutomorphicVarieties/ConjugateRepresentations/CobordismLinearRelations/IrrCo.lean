import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps

section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem irrAbs_module {R M S W κ ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [AddCommGroup W] [Module R W] [IsSimpleModule R S] [Finite ι] (Φ : (κ →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ)
    (p : ι → W →ₗ[R] M) (hp : ∀ w, (∀ i, p i w = 0) → w = 0) (x : W) (hx : x ≠ 0) :
    ∃ f : S →ₗ[R] W, Function.Injective f := by
  haveI := IsSemisimpleModule.range Φ
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (LinearEquiv.ofTop _ (LinearMap.range_eq_top.2 hs)).symm
  let e : W →ₗ[R] (ι → M) := LinearMap.pi p
  have he : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact hp w fun i => congrFun hw i
  haveI : IsSemisimpleModule R W := IsSemisimpleModule.of_injective e he
  haveI : Nontrivial W := ⟨⟨x, 0, hx⟩⟩
  obtain ⟨N, hN⟩ := IsSemisimpleModule.exists_simple_submodule R W
  haveI := hN
  haveI := IsSimpleModule.nontrivial R N
  obtain ⟨y, hy⟩ := exists_ne (0 : N)
  have hex : ∃ i, p i (y : W) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (Subtype.ext (hp _ h))
  obtain ⟨i, hi⟩ := hex
  let g : N →ₗ[R] M := (p i).comp N.subtype
  have hg : Function.Injective g := by
    rcases g.injective_or_eq_zero with h | h
    · exact h
    · exact absurd (LinearMap.congr_fun h y) hi
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property g hg LinearMap.id
  have hrΦ : r.comp Φ ≠ 0 := by
    obtain ⟨z, hz⟩ := hs (g y)
    intro h
    apply hy
    have h1 := LinearMap.congr_fun h z
    have h2 := LinearMap.congr_fun hr y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at h1 h2
    rw [hz] at h1
    rw [← h2, h1]
  have hex2 : ∃ k, (r.comp Φ).comp (Finsupp.lsingle k) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hrΦ
    apply Finsupp.lhom_ext
    intro a b
    simpa using LinearMap.congr_fun (h a) b
  obtain ⟨k, hk⟩ := hex2
  have hf0 : Function.Injective ((r.comp Φ).comp (Finsupp.lsingle k)) :=
    (LinearMap.injective_or_eq_zero _).resolve_right hk
  exact ⟨N.subtype.comp ((r.comp Φ).comp (Finsupp.lsingle k)), N.injective_subtype.comp hf0⟩

theorem UpperTheory.V.Cj.irrAbs :
    UpperTheory.V.Cj.IrrAbs := by
  intro G S V W ι _ _ _ _ _ _ _ _ _ ρS ρV ρW hirr hsup p hp hsep
  classical
  let F : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)} →
      (ρS.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule) := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρS ρV
      ((f.1).intertwiningMap_of_isIntertwiningMap ρS ρV f.2)
  let Φ := Finsupp.lsum ℕ F
  have key : ∀ u : V, u ∈ (⨆ f : {f : S →ₗ[ℂ] V // ∀ (g : G) (v : S), f ((ρS g) v) = (ρV g) (f v)},
      LinearMap.range f.1) → ∃ z, Φ z = (show ρV.asModule from u) := by
    intro u hu
    refine Submodule.iSup_induction (motive := fun u : V => ∃ z, Φ z = (show ρV.asModule from u)) _ hu ?_ ?_ ?_
    · rintro f u ⟨s, rfl⟩
      exact ⟨Finsupp.single f s, Finsupp.lsum_single ℕ F f s⟩
    · exact ⟨0, map_zero Φ⟩
    · rintro a b ⟨za, ha⟩ ⟨zb, hb⟩
      exact ⟨za + zb, by rw [map_add, ha, hb]; rfl⟩
  have hΦ : Function.Surjective Φ := by
    intro v
    exact key v (by rw [hsup]; exact Submodule.mem_top)
  let P : ι → (ρW.asModule →ₗ[MonoidAlgebra ℂ G] ρV.asModule) := fun i =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρW ρV
      ((p i).intertwiningMap_of_isIntertwiningMap ρW ρV (hp i))
  have hP : ∀ w : ρW.asModule, (∀ i, P i w = 0) → w = 0 := fun w h => hsep w h
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρS.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρS).1 hirr
  obtain ⟨f, hf⟩ := irrAbs_module Φ hΦ P hP (show ρW.asModule from x) hx
  let f' := (Representation.IntertwiningMap.equivLinearMapAsModule ρS ρW).symm f
  exact ⟨f'.toLinearMap, hf, fun g v => f'.isIntertwining ρS ρW g v⟩
end

section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.irrCo :
    UpperTheory.V.Cj.IrrCo := by
  intro E _ _ _ a π τ hτ Ξ q P hP hst hV
  haveI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.2 hP
  haveI : Module.Finite ℝ (Herm E a) := inferInstance
  let b := Module.finBasis ℝ (Herm E a)
  let ρW : Representation ℂ (GL (Fin a) (Af E)) P :=
    { toFun := fun x => (transRep Ξ q x).restrict (fun ω hω => hst x ω hω)
      map_one' := LinearMap.ext fun w => Subtype.ext (by simp)
      map_mul' := fun x y => LinearMap.ext fun w =>
        Subtype.ext (LinearMap.congr_fun (map_mul (transRep Ξ q) x y) w.1) }
  let p : (Fin q → Fin (Module.finrank ℝ (Herm E a))) × Fin Ξ.d → P →ₗ[ℂ] π.V := fun j =>
    { toFun := fun w => ⟨Bor.cmp j.2 (w.1 fun k => b (j.1 k)), mem_tens.1 (hV w.1 w.2 _) j.2⟩
      map_add' := fun x y => Subtype.ext (by
        change Bor.cmp j.2 ((x.1 + y.1) _) = Bor.cmp j.2 _ + Bor.cmp j.2 _
        rw [AlternatingMap.add_apply, map_add])
      map_smul' := fun c x => Subtype.ext (by
        change Bor.cmp j.2 ((c • x.1) _) = c • Bor.cmp j.2 _
        rw [AlternatingMap.smul_apply, map_smul]) }
  obtain ⟨Φ, h1, h2⟩ := irrAbs _ τ.V π.V P _ τ.ρ π.finPart ρW τ.irred hτ.iSup_range p
    (fun j g w => Subtype.ext (cmp_trans g w.1 _ j.2))
    (fun w hw => Subtype.ext (by
      refine Module.Basis.ext_alternating b fun v _ => ?_
      rw [← sum_cmp (w.1 _)]
      have : ∀ i, Bor.cmp i (w.1 fun k => b (v k)) = 0 := fun i => congrArg Subtype.val (hw (v, i))
      simp [this]))
  exact ⟨P.subtype ∘ₗ Φ, P.subtype_injective.comp h1, fun v => (Φ v).2, fun g v => congrArg Subtype.val (h2 g v)⟩
end
