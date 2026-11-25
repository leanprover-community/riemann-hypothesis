module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Levels
public import GroundTheory.ProfiniteCohomology.Factor
import GroundTheory.ProfiniteCohomology.FilteredHomology
public import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  FiniteSubfield IdeleLimit

noncomputable section

variable (K : FiniteSubfield)

instance compactSpace_fixingSubgroup : CompactSpace K.1.fixingSubgroup :=
  isCompact_iff_compactSpace.1 K.1.fixingSubgroup_isClosed.isCompact

variable {K}

abbrev levelCochainsInfl (p : GLevel K) :
    cochainsComplex (ideleRep K.1 p.1.1) ⟶ cochainsComplex (limitRep K) :=
  cochainsMapAlong restrictHom continuous_restrictHom (levelMor K p.1)

abbrev levelCochainsMap {p q : GLevel K} (h : p ≤ q) :
    cochainsComplex (ideleRep K.1 p.1.1) ⟶ cochainsComplex (ideleRep K.1 q.1.1) :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  cochainsMapAlong (levelRestrict K p.1 q.1) continuous_levelRestrict (levelMap K p.1 q.1)

theorem levelCochainsMap_comp_levelCochainsInfl {p q : GLevel K} (h : p ≤ q) :
    levelCochainsMap h ≫ levelCochainsInfl q = levelCochainsInfl p :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  levelCochains_comp

section GenericColimit

theorem cochainsMapAlong_restrictHom_injective {L : Rep ℤ K.1.fixingSubgroup} [IsDiscreteRep L]
    (p : GLevel K) {A : Rep ℤ (p.1.1 ≃ₐ[K.1] p.1.1)} [IsDiscreteRep A]
    (mor : Rep.res (restrictHom (F := K) (E := p.1)) A ⟶ L)
    (hinj : Function.Injective mor.hom) (m : ℕ) :
    Function.Injective ((cochainsMapAlong restrictHom continuous_restrictHom mor).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι A).f m)).1 inferInstance
  funext τ
  let σ : Fin m → K.1.fixingSubgroup := fun i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have hσ : (fun i => restrictHom (E := p.1) (σ i)) = τ :=
    funext fun i => Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have h1 := congrFun (congrArg (fun c => ((cochainsComplexι L).f m).hom c) h) σ
  change mor.hom (((cochainsComplexι A).f m).hom y (fun i => restrictHom (E := p.1) (σ i))) =
    mor.hom (((cochainsComplexι A).f m).hom y' (fun i => restrictHom (E := p.1) (σ i))) at h1
  rw [hσ] at h1
  exact hinj h1

theorem exists_cochainsMapAlong_restrictHom_eq {L : Rep ℤ K.1.fixingSubgroup} [IsDiscreteRep L]
    (A : ∀ p : GLevel K, Rep ℤ (p.1.1 ≃ₐ[K.1] p.1.1)) [∀ p, IsDiscreteRep (A p)]
    (mor : ∀ p : GLevel K, Rep.res (restrictHom (F := K) (E := p.1)) (A p) ⟶ L)
    (hsurj : ∀ a : L, ∃ E : FiniteSubfield, ∀ p : GLevel K, E ≤ p.1 → ∃ z : A p, (mor p).hom z = a)
    (m : ℕ) (x : (cochainsComplex L).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (A p)).X m),
      ((cochainsMapAlong restrictHom continuous_restrictHom (mor p)).f m).hom y = x := by
  classical
  have hx : IsLocallyConstant (((cochainsComplexι L).f m).hom x :
      (Fin m → K.1.fixingSubgroup) → L) :=
    (show locallyConstantCochains L m from x).2
  set f := ((cochainsComplexι L).f m).hom x with hf
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hx
  obtain ⟨t, ht, htU⟩ := isOpen_induced_iff.1 U.isOpen
  have h1t : (1 : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ∈ t := by
    have : (1 : K.1.fixingSubgroup) ∈ Subtype.val ⁻¹' t := by
      rw [htU]
      exact U.one_mem
    exact this
  obtain ⟨E₀, hE₀fin, hE₀⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) t).1 (ht.mem_nhds h1t)
  have hfin : (Set.range f).Finite := hx.range_finite
  choose idx hidx using hsurj
  choose lev hlev using fun E : FiniteSubfield => GLevel.exists_le (K := K) E
  obtain ⟨p, hp⟩ := Finset.exists_le ((hfin.toFinset.image fun a => lev (idx a)) ∪
    {lev ⟨E₀, hE₀fin⟩})
  have hpE₀ : E₀ ≤ p.1.1 := (hlev ⟨E₀, hE₀fin⟩).trans
    (hp _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  have hker : ∀ g : K.1.fixingSubgroup, restrictHom (E := p.1) g = 1 → g ∈ U := by
    intro g hg
    have hg' : g ∈ p.1.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
      rw [← ker_restrictHom, MonoidHom.mem_ker]
      exact hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have : g ∈ Subtype.val ⁻¹' t := hE₀ (IntermediateField.fixingSubgroup_le hpE₀ hg')
    rw [htU] at this
    exact this
  have hval : ∀ g, ∃ z : A p, (mor p).hom z = f g := fun g =>
    hidx (f g) p ((hlev (idx (f g))).trans
      (hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp)))))
  choose z hz using hval
  let lift : (Fin m → (p.1.1 ≃ₐ[K.1] p.1.1)) → Fin m → K.1.fixingSubgroup := fun τ i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  refine ⟨p, ⟨fun τ => z (lift τ), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι L).f m)).1 inferInstance
  funext g
  change (mor p).hom (z (lift fun i => restrictHom (E := p.1) (g i))) = f g
  rw [hz]
  refine hU _ _ fun i => hker _ ?_
  rw [map_mul, map_inv, Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)),
    inv_mul_cancel]

theorem exists_cohomologyMapAlong_restrictHom_eq {L : Rep ℤ K.1.fixingSubgroup} [IsDiscreteRep L]
    (A : ∀ p : GLevel K, Rep ℤ (p.1.1 ≃ₐ[K.1] p.1.1)) [∀ p, IsDiscreteRep (A p)]
    (mor : ∀ p : GLevel K, Rep.res (restrictHom (F := K) (E := p.1)) (A p) ⟶ L)
    (hinj : ∀ p, Function.Injective (mor p).hom)
    (hsurj : ∀ a : L, ∃ E : FiniteSubfield, ∀ p : GLevel K, E ≤ p.1 → ∃ z : A p, (mor p).hom z = a)
    (n : ℕ) (x : cohomology L n) :
    ∃ (p : GLevel K) (y : cohomology (A p) n),
      (cohomologyMapAlong restrictHom continuous_restrictHom (mor p) n).hom y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainsComplex L).homologyπ n)).1 inferInstance x
  obtain ⟨p, y₀, hy₀⟩ := exists_cochainsMapAlong_restrictHom_eq A mor hsurj n
    (((cochainsComplex L).iCycles n).hom z)
  have hd : ((cochainsComplex (A p)).d n (n + 1)).hom y₀ = 0 := by
    apply cochainsMapAlong_restrictHom_injective p (mor p) (hinj p) (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨p, ((cochainsComplex (A p)).homologyπ n).hom w, ?_⟩
  refine (homologyMap_homologyπ_apply
      (cochainsMapAlong restrictHom continuous_restrictHom (mor p)) n w).trans (congrArg _ ?_)
  apply (ModuleCat.mono_iff_injective ((cochainsComplex L).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]

end GenericColimit

theorem levelCochains_injective (p : GLevel K) (m : ℕ) :
    Function.Injective ((levelCochainsInfl p).f m).hom :=
  cochainsMapAlong_restrictHom_injective p (levelMor K p.1)
    (fun _ _ h => congrArg Additive.ofMul (of_injective p.1 (congrArg Additive.toMul h))) m

theorem exists_levelCochains_eq (m : ℕ) (x : (cochainsComplex (limitRep K)).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (ideleRep K.1 p.1.1)).X m),
      ((levelCochainsInfl p).f m).hom y = x :=
  exists_cochainsMapAlong_restrictHom_eq (fun p => ideleRep K.1 p.1.1) (fun p => levelMor K p.1)
    (fun a => by
      obtain ⟨E, x', hx'⟩ := exists_of (Additive.toMul a)
      exact ⟨E, fun p hle => ⟨Additive.ofMul (ideleMap hle x'), by
        change Additive.ofMul (of p.1 (ideleMap hle x')) = a
        rw [of_ideleMap, hx']; rfl⟩⟩) m x

theorem exists_levelInfl_eq (n : ℕ) (x : cohomology (limitRep K) n) :
    ∃ (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n), (levelInfl K p.1 n).hom y = x :=
  exists_cohomologyMapAlong_restrictHom_eq (fun p => ideleRep K.1 p.1.1) (fun p => levelMor K p.1)
    (fun p _ _ h => congrArg Additive.ofMul (of_injective p.1 (congrArg Additive.toMul h)))
    (fun a => by
      obtain ⟨E, x', hx'⟩ := exists_of (Additive.toMul a)
      exact ⟨E, fun p hle => ⟨Additive.ofMul (ideleMap hle x'), by
        change Additive.ofMul (of p.1 (ideleMap hle x')) = a
        rw [of_ideleMap, hx']; rfl⟩⟩) n x



theorem exists_levelTransition_eq_zero (n : ℕ) (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (hy : (levelInfl K p.1 n).hom y = 0) :
    ∃ (q : GLevel K) (h : p ≤ q),
      (HomologicalComplex.homologyMap (levelCochainsMap h) n).hom y = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n).hom w = y :=
    (ModuleCat.epi_iff_surjective ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n)).1
      inferInstance y
  subst hw
  have hy' := (homologyMap_homologyπ_apply (levelCochainsInfl p) n w).symm.trans hy
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff _ _).1 hy'
  rw [iCycles_cyclesMap_apply] at hu
  obtain ⟨q, u', hu'⟩ := exists_levelCochains_eq _ u
  obtain ⟨r, hpr, hqr⟩ := GLevel.exists_ge p q
  refine ⟨r, hpr, (homologyMap_homologyπ_apply (levelCochainsMap hpr) n w).trans
    ((homologyπ_eq_zero_iff _ _).2 ⟨((levelCochainsMap hqr).f _).hom u', ?_⟩)⟩
  rw [iCycles_cyclesMap_apply]
  apply levelCochains_injective r n
  rw [hom_f_d_apply]
  have e1 := congrArg (fun φ => (φ.f _).hom u') (levelCochainsMap_comp_levelCochainsInfl hqr)
  have e2 := congrArg (fun φ => (φ.f n).hom (((cochainsComplex (ideleRep K.1 p.1.1)).iCycles n).hom w))
    (levelCochainsMap_comp_levelCochainsInfl hpr)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e1, e2, hu', hu]

end

end GroundTheory.ProfCoh
