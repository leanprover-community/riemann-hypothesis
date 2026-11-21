import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.LinearAlgebra.Dimension.Basic

section
noncomputable section

open CategoryTheory

namespace UpperTheory.V.Lit.Dr

theorem acyclic : Acyclic := by
  intro Γ Ω _ _ _ ρ hP n
  obtain ⟨P, hconst, hequi⟩ := hP
  let S : Subgroup Γ := ⊥
  haveI : Subsingleton S := ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  let A : Rep ℂ S := Rep.of (Representation.trivial ℂ S Ω)
  let C : Rep ℂ Γ := Rep.coind S.subtype A
  have hC : Subsingleton (groupCohomology C (n + 1)) := by
    have hz : Limits.IsZero (groupCohomology C (n + 1)) :=
      (isZero_groupCohomology_succ_of_subsingleton A n).of_iso (groupCohomology.coindIso A (n + 1))
    have h0 : 𝟙 (groupCohomology C (n + 1)) = 0 := hz.eq_of_src _ _
    refine ⟨fun a b => ?_⟩
    have ha := congrArg (fun f => f.hom a) h0
    have hb := congrArg (fun f => f.hom b) h0
    simp only [ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.id_apply, LinearMap.zero_apply] at ha hb
    rw [ha, hb]
  let L : Ω →ₗ[ℂ] (Γ → Ω) := LinearMap.pi fun h => ρ h
  have hL : ∀ x, L x ∈ Representation.coindV S.subtype A.ρ := by
    intro x g h
    have hg : (g : Γ) = 1 := Subgroup.mem_bot.1 g.2
    simp [L, hg]
  let iL : Ω →ₗ[ℂ] Representation.coindV S.subtype A.ρ := LinearMap.codRestrict _ L hL
  let M : Representation.coindV S.subtype A.ρ →ₗ[ℂ] (Γ → Ω) :=
    LinearMap.pi fun g => ρ g ∘ₗ LinearMap.proj g⁻¹ ∘ₗ Submodule.subtype _
  let rL : Representation.coindV S.subtype A.ρ →ₗ[ℂ] Ω := P ∘ₗ M
  let i : Rep.of ρ ⟶ C := Rep.ofHom ⟨iL, fun γ => by
    refine LinearMap.ext fun x => Subtype.ext (funext fun h => ?_)
    simp only [iL, L, LinearMap.comp_apply]
    show (ρ h) ((ρ γ) x) = (ρ (h * γ)) x
    rw [map_mul, Module.End.mul_apply]⟩
  let r : C ⟶ Rep.of ρ := Rep.ofHom ⟨rL, fun γ => by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, rL, M]
    rw [hequi]
    congr 1
    funext g
    simp [mul_inv_rev, ← Module.End.mul_apply, ← map_mul]
    rfl⟩
  have hri : i ≫ r = 𝟙 _ := by
    ext x
    simp [i, r, rL, M, iL, L, ← Module.End.mul_apply, ← map_mul, hconst]
    show P (fun g => ρ g (ρ g⁻¹ x)) = x
    rw [show (fun g => ρ g (ρ g⁻¹ x)) = fun _ => x from
      funext fun g => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply], hconst]
  let F := groupCohomology.functor ℂ Γ (n + 1)
  have hinj : Function.Injective (F.map i).hom := by
    intro a b hab
    have key : ∀ z, (F.map r).hom ((F.map i).hom z) = z := by
      intro z
      rw [← ModuleCat.comp_apply, ← F.map_comp, hri, F.map_id]
      rfl
    rw [← key a, ← key b, hab]
  haveI : Subsingleton (F.obj C) := hC
  exact hinj.subsingleton

end UpperTheory.V.Lit.Dr
end
end

section
noncomputable section

open CategoryTheory

namespace UpperTheory.V.Lit.Dr

theorem shiftUp : ShiftUp := by
  intro Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex hΩ n
  let f : Rep.of ρM ⟶ Rep.of ρΩ := Rep.ofHom ⟨ι, fun γ => by ext m; exact hι γ m⟩
  let g : Rep.of ρΩ ⟶ Rep.of ρZ := Rep.ofHom ⟨π, fun γ => by ext x; exact hπ γ x⟩
  have hfg : f ≫ g = 0 := by
    ext m
    exact hex.apply_apply_eq_zero m
  let X : ShortComplex (Rep ℂ Γ) := ShortComplex.mk f g hfg
  have hX : X.ShortExact :=
    { exact := (forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _ <|
        (ShortComplex.moduleCat_exact_iff _).2 fun x hx => (hex x).1 hx
      mono_f := (Rep.mono_iff_injective _).2 hinj
      epi_g := (Rep.epi_iff_surjective _).2 hsurj }
  have hz : Limits.IsZero (groupCohomology X.X₂ (n + 1)) := by
    haveI := hΩ n
    exact ModuleCat.isZero_of_subsingleton _
  have hmono := groupCohomology.mono_δ_of_isZero hX (n + 1) hz
  have hinjδ := (ModuleCat.mono_iff_injective _).1 hmono
  exact LinearMap.rank_le_of_injective _ hinjδ

end UpperTheory.V.Lit.Dr
end
end

section
noncomputable section

namespace UpperTheory.V.Lit.Dr

open groupCohomology

theorem shiftOne : ShiftOne := by
  intro Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex n w hw hlift
  classical
  choose y hy using fun i => hsurj (w i)
  have hker : ∀ i γ, π (ρΩ γ (y i) - y i) = 0 := by
    intro i γ
    rw [map_sub, hπ, hy, hw, sub_self]
  choose φ hφ using fun i γ => (hex (ρΩ γ (y i) - y i)).1 (hker i γ)
  have hcoc : ∀ i, φ i ∈ groupCohomology.cocycles₁ (Rep.of ρM) := by
    intro i
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    apply hinj
    rw [Rep.of_ρ]
    change ι (φ i (g * h)) = ι ((ρM g) (φ i h) + φ i g)
    rw [map_add, hι, hφ, hφ, hφ, map_mul, Module.End.mul_apply, map_sub]
    abel
  let v : Fin n → groupCohomology (Rep.of ρM) 1 :=
    fun i => (groupCohomology.H1π (Rep.of ρM)).hom ⟨φ i, hcoc i⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (∑ i, g i • v i) =
        (groupCohomology.H1π (Rep.of ρM)).hom (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) := by
      simp only [map_sum, map_smul, v]
    rw [hsum, groupCohomology.H1π_eq_zero_iff] at hg
    obtain ⟨m, hm⟩ := hg
    have key : Subtype.val (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) = ∑ i, g i • φ i := by
      rw [Submodule.coe_sum]
      rfl
    have hm' : ∀ γ, ρM γ m - m = ∑ i, g i • φ i γ := by
      intro γ
      have := congrFun hm γ
      rw [groupCohomology.d₀₁_hom_apply, Rep.of_ρ] at this
      rw [this]
      exact (congrFun key γ).trans (Finset.sum_apply _ _ _)
    have hzero := hlift g ⟨(∑ i, g i • y i) - ι m, ?_, ?_⟩
    · intro i
      rw [hzero]
      rfl
    · intro γ
      have h1 : ι (ρM γ m) - ι m = ∑ i, g i • (ρΩ γ (y i) - y i) := by
        rw [← map_sub, hm', map_sum]
        simp only [map_smul, hφ]
      rw [hι] at h1
      rw [map_sub, map_sum]
      simp only [map_smul]
      simp only [smul_sub, Finset.sum_sub_distrib] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    · rw [map_sub, hex.apply_apply_eq_zero, sub_zero, map_sum]
      simp only [map_smul, hy]
  have := hli.cardinal_le_rank
  simpa using this

end UpperTheory.V.Lit.Dr
end
end

section
noncomputable section

namespace UpperTheory.V.Lit.Dr

theorem shiftZero : ShiftZero := by
  intro Γ M _ _ _ ρ n w hw hlin
  let v : Fin n → (Rep.of ρ).ρ.invariants :=
    fun i => ⟨w i, (Representation.mem_invariants _ _).2 (hw i)⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∑ i, g i • w i = 0 := by
      have := congrArg Subtype.val hg
      rw [Submodule.coe_sum] at this
      exact this
    rw [hlin g h0]
    intro i
    rfl
  have h1 := hli.cardinal_le_rank
  rw [Cardinal.mk_fin] at h1
  have hinj : Function.Injective (groupCohomology.H0Iso (Rep.of ρ)).inv.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact h1.trans (LinearMap.rank_le_of_injective _ hinj)

end UpperTheory.V.Lit.Dr
end
end

section
open UpperTheory.V.Lit.Dr

private def UpperTheory.V.Lit.Dr.kerRep {Γ A B : Type} [Group Γ] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρ : Representation ℂ Γ A) (σ : Representation ℂ Γ B) (f : A →ₗ[ℂ] B) (hf : ∀ γ x, f (ρ γ x) = σ γ (f x)) :
    Representation ℂ Γ (LinearMap.ker f) where
  toFun γ := (ρ γ).restrict (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hf, hx, map_zero])
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

private theorem UpperTheory.V.Lit.Dr.absPos (q : ℕ) :
    ∀ (Γ M : Type) (Ω : ℕ → Type) [Group Γ] [AddCommGroup M] [Module ℂ M] [∀ q, AddCommGroup (Ω q)] [∀ q, Module ℂ (Ω q)]
    (ρM : Representation ℂ Γ M) (ρ : ∀ q, Representation ℂ Γ (Ω q)) (ι : M →ₗ[ℂ] Ω 0) (d : ∀ q, Ω q →ₗ[ℂ] Ω (q + 1)),
    (∀ γ m, ι (ρM γ m) = ρ 0 γ (ι m)) → (∀ q γ x, d q (ρ q γ x) = ρ (q + 1) γ (d q x)) → Function.Injective ι →
    Function.Exact ι (d 0) → (∀ q, Function.Exact (d q) (d (q + 1))) → (∀ q, HasAverage (ρ q)) →
    ∀ (n : ℕ) (w : Fin n → Ω (q + 1)), (∀ i γ, ρ (q + 1) γ (w i) = w i) → (∀ i, d (q + 1) (w i) = 0) →
    (∀ c : Fin n → ℂ, (∃ y, (∀ γ, ρ q γ y = y) ∧ d q y = ∑ i, c i • w i) → c = 0) →
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of ρM) (q + 1)) := by
  induction q with
  | zero =>
    intro Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
    let π : Ω 0 →ₗ[ℂ] LinearMap.ker (d 1) := (d 0).codRestrict _ (fun x => (hex 0).apply_apply_eq_zero x)
    refine shiftOne Γ M (Ω 0) (LinearMap.ker (d 1)) ρM (ρ 0) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1)) ι π hι
      (fun γ x => Subtype.ext (hd 0 γ x)) hinj
      (fun z => by obtain ⟨y, hy⟩ := (hex 0 z.1).1 z.2; exact ⟨y, Subtype.ext hy⟩)
      (fun x => by rw [← hex0 x, Subtype.ext_iff]; rfl) n (fun i => ⟨w i, hdw i⟩)
      (fun i γ => Subtype.ext (hw i γ)) ?_
    rintro c ⟨y, hy, hy'⟩
    refine hind c ⟨y, hy, ?_⟩
    have h : (π y).1 = ∑ i, c i • w i := by rw [hy']; simp
    exact h
  | succ q ih =>
    intro Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
    let π : Ω 0 →ₗ[ℂ] LinearMap.ker (d 1) := (d 0).codRestrict _ (fun x => (hex 0).apply_apply_eq_zero x)
    refine le_trans (ih Γ (LinearMap.ker (d 1)) (fun k => Ω (k + 1)) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1))
      (fun k => ρ (k + 1)) (LinearMap.ker (d 1)).subtype (fun k => d (k + 1)) (fun γ m => rfl)
      (fun k => hd (k + 1)) Subtype.val_injective (LinearMap.exact_subtype_ker_map _) (fun k => hex (k + 1))
      (fun k => hav (k + 1)) n w hw hdw hind) ?_
    exact shiftUp Γ M (Ω 0) (LinearMap.ker (d 1)) ρM (ρ 0) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1)) ι π hι
      (fun γ x => Subtype.ext (hd 0 γ x)) hinj
      (fun z => by obtain ⟨y, hy⟩ := (hex 0 z.1).1 z.2; exact ⟨y, Subtype.ext hy⟩)
      (fun x => by rw [← hex0 x, Subtype.ext_iff]; rfl) (acyclic Γ (Ω 0) (ρ 0) (hav 0)) q

theorem UpperTheory.V.Lit.Dr.absMain :
    AbsMain := by
  intro q Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
  cases q with
  | zero =>
    choose m hm using fun i => (hex0 (w i)).1 (hdw i)
    refine shiftZero Γ M ρM n m (fun i γ => hinj (by rw [hι, hm, hw])) (fun c hc => hind c ?_)
    have := congrArg ι hc
    simpa [InvExact, hm] using this
  | succ q => exact absPos q Γ M Ω ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
end
