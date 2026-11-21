import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LocalTransition
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LevelsColimit
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Levels

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange FiniteSubfield IdeleLimit SemiLocal GroundTheory.Global.IdeleGroup

open scoped Pointwise NumberField.LiesOver NumberField.AdeleRing

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

set_option synthInstance.maxHeartbeats 200000

variable {K F : FiniteSubfield} [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (w : PlacesOver F.1 v)

theorem finiteProj_smul_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
    (x : IdeleGroup F.1) :
    finiteProj w.1 ((σ : F.1 ≃ₐ[K.1] F.1) • x) = σ • finiteProj w.1 x := by
  apply Units.ext
  have h : w.1 = (σ : F.1 ≃ₐ[K.1] F.1) • w.1 :=
    (congrArg Subtype.val ((mem_stabilizer_iff_smul_eq v w σ).1 σ.2)).symm
  rw [coe_finiteProj, coe_smul_idele, smul_snd_eq_galHom _ _ w.1 w.1 h, galHom_eq_decomposition]
  rfl

def finiteComponentRep :
    Rep.res (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal).subtype (ideleRep K.1 F.1) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (finiteProj w.1)).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (finiteProj_smul_of_mem_stabilizer w σ x.toMul)⟩

def finiteComponent (n : ℕ) :
    cohomology (ideleRep K.1 F.1) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ) n :=
  cohomologyMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal).subtype
    continuous_of_discreteTopology (finiteComponentRep w) n

set_option maxHeartbeats 2000000 in

theorem placeProj_comp_finiteShapiroIso (n : ℕ) :
    cohomologyMap (finiteProjAboveRep (K := K.1) (L := F.1) v) n ≫ (finiteShapiroIso v w n).hom =
      finiteComponent w n := by
  change HomologicalComplex.homologyMap (cochainsMap (finiteProjAboveRep (K := K.1) (L := F.1) v)) n ≫
      (HomologicalComplex.homologyMap (cochainsMapAlong _ (continuous_subgroup_subtype _)
        (orbitProj (permutesFactors_finiteUnitsAboveRep v)
          (mem_stabilizer_iff_smul_eq v w))) n ≫
      HomologicalComplex.homologyMap (cochainsMap (stabRepFiniteIso v w).hom) n) = _
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1

omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in

theorem ideleEmbedding_snd_of_below_eq {E : FiniteSubfield} [Algebra F.1 E.1]
    (w' : HeightOneSpectrum (𝓞 E.1)) (u : HeightOneSpectrum (𝓞 F.1)) (hu : below F.1 w' = u)
    [w'.asIdeal.LiesOver u.asIdeal] (x : IdeleGroup F.1) :
    ((ideleEmbedding F.1 E.1 x : IdeleGroup E.1) : 𝔸[E.1]).2 w' =
      SemiLocal.completionMap u w' ((x : 𝔸[F.1]).2 u) := by
  subst hu
  rfl

variable {E : FiniteSubfield} [Fact (K ≤ E)] [Fact (F ≤ E)] [E.1.fixingSubgroup.Normal]

set_option maxHeartbeats 2000000 in

theorem levelTransition_comp_finiteComponent (w' : PlacesOver E.1 v)
    [w'.1.asIdeal.LiesOver w.1.asIdeal] (n : ℕ) :
    levelTransition K F E n ≫ finiteComponent w' n =
      finiteComponent w n ≫ localTransition K F E w w' n := by
  unfold levelTransition finiteComponent localTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ n)
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Units.ext
  change ((ideleEmbedding F.1 E.1 _ : IdeleGroup E.1) : 𝔸[E.1]).2 w'.1 =
    SemiLocal.completionMap w.1 w'.1 _
  exact ideleEmbedding_snd_of_below_eq w'.1 w.1 ((below_eq_iff w'.1 w.1).2 inferInstance) _

end Finite

section Infinite

variable {v : InfinitePlace K.1} (w : v.placesOver F.1)

omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in
theorem fst_eq_completionCongr (a : 𝔸[F.1]) {u u' : InfinitePlace F.1} (h : u = u') :
    a.1 u' = completionCongr h (a.1 u) := by
  subst h
  rfl

omit [F.1.fixingSubgroup.Normal] in
theorem eq_comap_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) :
    w.1 = w.1.comap (((σ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1) : F.1 →+* F.1) := by
  rw [comap_eq_inv_smul]
  exact (MulAction.mem_stabilizer_iff.1 (inv_mem σ.2)).symm

theorem infiniteProj_smul_of_mem_stabilizer (σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
    (x : IdeleGroup F.1) :
    infiniteProj w.1 ((σ : F.1 ≃ₐ[K.1] F.1) • x) = σ • infiniteProj w.1 x := by
  apply Units.ext
  rw [coe_infiniteProj, coe_smul_idele, smul_fst,
    fst_eq_completionCongr _ (eq_comap_of_mem_stabilizer w σ), infiniteCompletionMap_eq_decomposition]
  rfl

def infiniteComponentRep :
    Rep.res (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1).subtype (ideleRep K.1 F.1) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) (w.1.Completion)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (infiniteProj w.1)).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (infiniteProj_smul_of_mem_stabilizer w σ x.toMul)⟩

def infiniteComponent (n : ℕ) :
    cohomology (ideleRep K.1 F.1) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
        (w.1.Completion)ˣ) n :=
  cohomologyMapAlong (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1).subtype
    continuous_of_discreteTopology (infiniteComponentRep w) n

set_option maxHeartbeats 2000000 in

theorem placeProj_comp_infiniteShapiroIso (n : ℕ) :
    cohomologyMap (infiniteProjAboveRep (K := K.1) (L := F.1) v) n ≫ (infiniteShapiroIso v w n).hom =
      infiniteComponent w n := by
  change HomologicalComplex.homologyMap (cochainsMap (infiniteProjAboveRep (K := K.1) (L := F.1) v)) n ≫
      (HomologicalComplex.homologyMap (cochainsMapAlong _ (continuous_subgroup_subtype _)
        (orbitProj (permutesFactors_infiniteUnitsAboveRep v)
          (mem_stabilizer_iff_smul_eq_infinite v w))) n ≫
      HomologicalComplex.homologyMap (cochainsMap (stabRepInfiniteIso v w).hom) n) = _
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1

omit [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal] in

theorem ideleEmbedding_fst_of_comap_eq {E : FiniteSubfield} [Algebra F.1 E.1]
    (w' : InfinitePlace E.1) (u : InfinitePlace F.1) (hu : w'.comap (algebraMap F.1 E.1) = u)
    [w'.LiesOver u] (x : IdeleGroup F.1) :
    ((ideleEmbedding F.1 E.1 x : IdeleGroup E.1) : 𝔸[E.1]).1 w' =
      NumberField.LiesOver.completionMap (v := u) (w := w') ((x : 𝔸[F.1]).1 u) := by
  subst hu
  rfl

variable {E : FiniteSubfield} [Fact (K ≤ E)] [Fact (F ≤ E)] [E.1.fixingSubgroup.Normal]

set_option maxHeartbeats 2000000 in

theorem levelTransition_comp_infiniteComponent (w' : v.placesOver E.1) [w'.1.LiesOver w.1] (n : ℕ) :
    levelTransition K F E n ≫ infiniteComponent w' n =
      infiniteComponent w n ≫ infLocalTransition K F E w w' n := by
  unfold levelTransition infiniteComponent infLocalTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ n)
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Units.ext
  change ((ideleEmbedding F.1 E.1 _ : IdeleGroup E.1) : 𝔸[E.1]).1 w'.1 =
    NumberField.LiesOver.completionMap (v := w.1) (w := w'.1) _
  exact ideleEmbedding_fst_of_comap_eq w'.1 w.1 (InfinitePlace.LiesOver.comap_eq w'.1 w.1) _

end Infinite

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  FiniteSubfield IdeleLimit

noncomputable section

variable {K F E M : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (K ≤ M)] [Fact (F ≤ E)]
  [Fact (E ≤ M)] [Fact (F ≤ M)] [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]
  [M.1.fixingSubgroup.Normal]

theorem levelRestrict_levelRestrict (τ : M.1 ≃ₐ[K.1] M.1) :
    levelRestrict K F E (levelRestrict K E M τ) = levelRestrict K F M τ := by
  ext x
  have h1 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := F) (E := E)
    (levelRestrict K E M τ) x)
  have h2 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := E) (E := M) τ
    (algebraMap F.1 E.1 x))
  have h3 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := F) (E := M) τ x)
  exact h1.trans (h2.trans h3.symm)

set_option maxHeartbeats 2000000 in

theorem levelTransition_comp_levelTransition (n : ℕ) :
    levelTransition K F E n ≫ levelTransition K E M n = levelTransition K F M n := by
  unfold levelTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (ideleMap (Fact.out : E ≤ M) (ideleMap (Fact.out : F ≤ E)
      ((x.1 fun i => levelRestrict K F E (levelRestrict K E M (g i))).toMul))) =
    Additive.ofMul (ideleMap (Fact.out : F ≤ M) ((x.1 fun i => levelRestrict K F M (g i)).toMul))
  have hfun : (fun i => levelRestrict K F E (levelRestrict K E M (g i))) =
      fun i => levelRestrict K F M (g i) := funext fun i => levelRestrict_levelRestrict (g i)
  refine (congrArg Additive.ofMul (ideleMap_ideleMap (Fact.out : F ≤ E) (Fact.out : E ≤ M) _)).trans ?_
  rw [hfun]

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField GroundTheory.Global FiniteSubfield IdeleLimit DirectSum

noncomputable section

variable {K : FiniteSubfield} (n : ℕ)

abbrev levelTransitionG {p q : GLevel K} (h : p ≤ q) :
    cohomology (ideleRep K.1 p.1.1) n ⟶ cohomology (ideleRep K.1 q.1.1) n :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  levelTransition K p.1 q.1 n

theorem levelTransitionG_comp_levelInfl {p q : GLevel K} (h : p ≤ q) (y : cohomology (ideleRep K.1 p.1.1) n) :
    (levelInfl K q.1 n).hom ((levelTransitionG n h).hom y) = (levelInfl K p.1 n).hom y := by
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  exact congrArg (fun φ => φ.hom y) (levelTransition_comp_levelInfl (K := K) (F := p.1) (E := q.1) n)

theorem levelTransitionG_trans {p q r : GLevel K} (h₁ : p ≤ q) (h₂ : q ≤ r)
    (y : cohomology (ideleRep K.1 p.1.1) n) :
    (levelTransitionG n h₂).hom ((levelTransitionG n h₁).hom y) =
      (levelTransitionG n (h₁.trans h₂)).hom y := by
  haveI : Fact (p.1 ≤ q.1) := ⟨h₁⟩
  haveI : Fact (q.1 ≤ r.1) := ⟨h₂⟩
  haveI : Fact (p.1 ≤ r.1) := ⟨h₁.trans h₂⟩
  exact congrArg (fun φ => φ.hom y)
    (levelTransition_comp_levelTransition (K := K) (F := p.1) (E := q.1) (M := r.1) n)

variable (K) in

structure LevelDecomposition where

  L : Place K.1 → GLevel K → Type
  [grp : ∀ v p, AddCommGroup (L v p)]

  e : ∀ v (p : GLevel K), cohomology (placeRep p.1.1 v) n ≃+ L v p

  lt : ∀ v {p q : GLevel K}, p ≤ q → L v p →+ L v q

  compat : ∀ v {p q : GLevel K} (h : p ≤ q) (y : cohomology (ideleRep K.1 p.1.1) n),
    e v q ((cohomologyMap (placeProj v) n).hom ((levelTransitionG n h).hom y)) =
      lt v h (e v p ((cohomologyMap (placeProj v) n).hom y))

attribute [instance] LevelDecomposition.grp

structure LocalLimit {n : ℕ} (D : LevelDecomposition K n) where

  T : Place K.1 → Type
  [grp : ∀ v, AddCommGroup (T v)]

  infl : ∀ v (p : GLevel K), D.L v p →+ T v
  infl_compat : ∀ v {p q : GLevel K} (h : p ≤ q) (z : D.L v p), infl v q (D.lt v h z) = infl v p z
  exists_infl : ∀ v (t : T v), ∃ (p : GLevel K) (z : D.L v p), infl v p z = t
  exists_lt_eq_zero : ∀ v (p : GLevel K) (z : D.L v p), infl v p z = 0 →
    ∃ (q : GLevel K) (h : p ≤ q), D.lt v h z = 0

attribute [instance] LocalLimit.grp

variable {n} (D : LevelDecomposition K n) (T : LocalLimit D) (hn : 1 ≤ n)

include hn in

def levelSum (p : GLevel K) : cohomology (ideleRep K.1 p.1.1) n →+ ⨁ v : Place K.1, T.T v :=
  (DFinsupp.mapRange.addMonoidHom fun v => (T.infl v p).comp (D.e v p).toAddMonoidHom).comp
    (idelesCohomologyEquiv hn).symm.toAddMonoidHom

theorem levelSum_apply (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n) (v : Place K.1) :
    levelSum D T hn p y v = T.infl v p (D.e v p ((cohomologyMap (placeProj v) n).hom y)) := by
  change T.infl v p (D.e v p ((idelesCohomologyEquiv hn).symm y v)) = _
  rw [idelesCohomologyEquiv_symm_apply]

theorem levelSum_levelTransition {p q : GLevel K} (h : p ≤ q) (y : cohomology (ideleRep K.1 p.1.1) n) :
    levelSum D T hn q ((levelTransitionG n h).hom y) = levelSum D T hn p y := by
  ext v
  rw [levelSum_apply, levelSum_apply, D.compat, T.infl_compat]

theorem levelSum_eq_of_levelInfl_eq {p q : GLevel K} (y : cohomology (ideleRep K.1 p.1.1) n)
    (y' : cohomology (ideleRep K.1 q.1.1) n)
    (h : (levelInfl K p.1 n).hom y = (levelInfl K q.1 n).hom y') :
    levelSum D T hn p y = levelSum D T hn q y' := by
  obtain ⟨r, hpr, hqr⟩ := GLevel.exists_ge p q
  have hz : (levelInfl K r.1 n).hom
      ((levelTransitionG n hpr).hom y - (levelTransitionG n hqr).hom y') = 0 := by
    rw [map_sub, levelTransitionG_comp_levelInfl, levelTransitionG_comp_levelInfl, h, sub_self]
  obtain ⟨s, hrs, hs⟩ := exists_levelTransition_eq_zero n r _ hz
  have hs' : (levelTransitionG n hrs).hom
      ((levelTransitionG n hpr).hom y - (levelTransitionG n hqr).hom y') = 0 := hs
  rw [map_sub, sub_eq_zero] at hs'
  rw [← levelSum_levelTransition D T hn hpr, ← levelSum_levelTransition D T hn hrs, hs',
    levelSum_levelTransition, levelSum_levelTransition]

def pick (x : cohomology (limitRep K) n) : Σ p : GLevel K, cohomology (ideleRep K.1 p.1.1) n :=
  ⟨(exists_levelInfl_eq n x).choose, (exists_levelInfl_eq n x).choose_spec.choose⟩

theorem levelInfl_pick (x : cohomology (limitRep K) n) :
    (levelInfl K (pick x).1.1 n).hom (pick x).2 = x :=
  (exists_levelInfl_eq n x).choose_spec.choose_spec

def limitCohomologyFun (x : cohomology (limitRep K) n) : ⨁ v : Place K.1, T.T v :=
  levelSum D T hn (pick x).1 (pick x).2

theorem limitCohomologyFun_eq (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (x : cohomology (limitRep K) n) (h : (levelInfl K p.1 n).hom y = x) :
    limitCohomologyFun D T hn x = levelSum D T hn p y :=
  levelSum_eq_of_levelInfl_eq D T hn (pick x).2 y ((levelInfl_pick x).trans h.symm)

set_option maxHeartbeats 4000000 in
theorem limitCohomologyFun_add (x₁ x₂ : cohomology (limitRep K) n) :
    limitCohomologyFun D T hn (x₁ + x₂) = limitCohomologyFun D T hn x₁ + limitCohomologyFun D T hn x₂ := by
  obtain ⟨p₁, y₁, rfl⟩ := exists_levelInfl_eq n x₁
  obtain ⟨p₂, y₂, rfl⟩ := exists_levelInfl_eq n x₂
  obtain ⟨r, h1r, h2r⟩ := GLevel.exists_ge p₁ p₂
  have hsum : (levelInfl K r.1 n).hom ((levelTransitionG n h1r).hom y₁ +
      (levelTransitionG n h2r).hom y₂) = (levelInfl K p₁.1 n).hom y₁ + (levelInfl K p₂.1 n).hom y₂ := by
    rw [map_add, levelTransitionG_comp_levelInfl, levelTransitionG_comp_levelInfl]
  rw [limitCohomologyFun_eq D T hn p₁ y₁ _ rfl, limitCohomologyFun_eq D T hn p₂ y₂ _ rfl,
    limitCohomologyFun_eq D T hn r _ _ hsum, map_add, levelSum_levelTransition, levelSum_levelTransition]

def limitCohomologyHom : cohomology (limitRep K) n →+ ⨁ v : Place K.1, T.T v :=
  AddMonoidHom.mk' (limitCohomologyFun D T hn) (limitCohomologyFun_add D T hn)

theorem limitCohomologyHom_levelInfl (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n) :
    limitCohomologyHom D T hn ((levelInfl K p.1 n).hom y) = levelSum D T hn p y :=
  limitCohomologyFun_eq D T hn p y _ rfl

theorem eq_zero_of_forall_placeProj {n : ℕ} (hn : 1 ≤ n) (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (h : ∀ v : Place K.1, (cohomologyMap (placeProj v) n).hom y = 0) : y = 0 := by
  apply (idelesCohomologyEquiv hn).symm.injective
  rw [map_zero]
  ext v
  rw [idelesCohomologyEquiv_symm_apply, h v]
  rfl

theorem limitCohomologyHom_injective : Function.Injective (limitCohomologyHom D T hn) := by
  classical
  refine (injective_iff_map_eq_zero (limitCohomologyHom D T hn)).2 fun x hx => ?_
  obtain ⟨p, y, rfl⟩ := exists_levelInfl_eq n x
  rw [limitCohomologyHom_levelInfl] at hx
  have hv : ∀ v, T.infl v p (D.e v p ((cohomologyMap (placeProj v) n).hom y)) = 0 := fun v => by
    have := congrArg (fun ζ : ⨁ v : Place K.1, T.T v => ζ v) hx
    rw [levelSum_apply] at this
    exact this
  choose q hpq hq using fun v => T.exists_lt_eq_zero v p _ (hv v)
  obtain ⟨r, hr⟩ := Finset.exists_le (insert p (((idelesCohomologyEquiv hn).symm y).support.image q))
  have hpr : p ≤ r := hr _ (Finset.mem_insert_self _ _)
  have hzero : (levelTransitionG n hpr).hom y = 0 := by
    refine eq_zero_of_forall_placeProj hn r _ fun v => (D.e v r).injective ?_
    rw [map_zero]
    by_cases hvS : v ∈ ((idelesCohomologyEquiv hn).symm y).support
    · have hqr : q v ≤ r := hr _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hvS))
      rw [← levelTransitionG_trans n (hpq v) hqr, D.compat, D.compat, hq v, map_zero]
    · have h0 : (cohomologyMap (placeProj v) n).hom y = 0 := by
        rw [← idelesCohomologyEquiv_symm_apply hn]
        exact DFinsupp.notMem_support_iff.1 hvS
      rw [D.compat, h0, map_zero, map_zero]
  rw [← levelTransitionG_comp_levelInfl n hpr, hzero, map_zero]

theorem limitCohomologyHom_surjective : Function.Surjective (limitCohomologyHom D T hn) := by
  classical
  intro ζ
  choose p z hz using fun v => T.exists_infl v (ζ v)
  obtain ⟨p₀⟩ := (inferInstance : Nonempty (GLevel K))
  obtain ⟨r, hr⟩ := Finset.exists_le (insert p₀ (ζ.support.image p))
  have hpr : ∀ v ∈ ζ.support, p v ≤ r := fun v hv =>
    hr _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv))
  let ξ : ⨁ v : Place K.1, cohomology (placeRep r.1.1 v) n :=
    DFinsupp.mk ζ.support fun v => (D.e v.1 r).symm (D.lt v.1 (hpr v.1 v.2) (z v.1))
  refine ⟨(levelInfl K r.1 n).hom (idelesCohomologyEquiv hn ξ), ?_⟩
  rw [limitCohomologyHom_levelInfl]
  ext v
  rw [levelSum_apply, ← idelesCohomologyEquiv_symm_apply hn, AddEquiv.symm_apply_apply]
  by_cases hv : v ∈ ζ.support
  · have : ξ v = (D.e v r).symm (D.lt v (hpr v hv) (z v)) := by
      simp only [ξ, DFinsupp.mk_apply, dif_pos hv]
    rw [this, AddEquiv.apply_symm_apply, T.infl_compat, hz]
  · have : ξ v = 0 := by
      simp only [ξ, DFinsupp.mk_apply, dif_neg hv]
    rw [this, map_zero, map_zero, DFinsupp.notMem_support_iff.1 hv]

def limitCohomologyEquiv : cohomology (limitRep K) n ≃+ ⨁ v : Place K.1, T.T v :=
  AddEquiv.ofBijective (limitCohomologyHom D T hn)
    ⟨limitCohomologyHom_injective D T hn, limitCohomologyHom_surjective D T hn⟩

theorem limitCohomologyEquiv_levelInfl (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (v : Place K.1) :
    limitCohomologyEquiv D T hn ((levelInfl K p.1 n).hom y) v =
      T.infl v p (D.e v p ((cohomologyMap (placeProj v) n).hom y)) := by
  change limitCohomologyHom D T hn _ v = _
  rw [limitCohomologyHom_levelInfl, levelSum_apply]

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global FiniteSubfield
  IdeleLimit SemiLocal

open scoped Pointwise NumberField.LiesOver

noncomputable section

variable (K : FiniteSubfield)

structure CompatiblePlaces where

  fin : ∀ (v : HeightOneSpectrum (𝓞 K.1)) (p : GLevel K), PlacesOver p.1.1 v
  fin_liesOver : ∀ v {p q : GLevel K} (h : p ≤ q),
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    (fin v q).1.asIdeal.LiesOver (fin v p).1.asIdeal

  inf : ∀ (v : InfinitePlace K.1) (p : GLevel K), v.placesOver p.1.1
  inf_liesOver : ∀ v {p q : GLevel K} (h : p ≤ q),
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    (inf v q).1.LiesOver (inf v p).1

namespace CompatiblePlaces

variable {K} (P : CompatiblePlaces K) (n : ℕ)

def localGroup : Place K.1 → GLevel K → Type
  | .inl v, p => cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer (p.1.1 ≃ₐ[K.1] p.1.1) (P.inf v p).1) ((P.inf v p).1.Completion)ˣ) n
  | .inr v, p => cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer (p.1.1 ≃ₐ[K.1] p.1.1) (P.fin v p).1.asIdeal)
      ((P.fin v p).1.adicCompletion p.1.1)ˣ) n

instance (v : Place K.1) (p : GLevel K) : AddCommGroup (P.localGroup n v p) := by
  rcases v with v | v <;> exact inferInstanceAs (AddCommGroup (cohomology _ n))

def shapiro : ∀ (v : Place K.1) (p : GLevel K), cohomology (placeRep p.1.1 v) n ≃+ P.localGroup n v p
  | .inl v, p => (infiniteShapiroIso v (P.inf v p) n).toLinearEquiv.toAddEquiv
  | .inr v, p => (finiteShapiroIso v (P.fin v p) n).toLinearEquiv.toAddEquiv

def transition : ∀ (v : Place K.1) {p q : GLevel K}, p ≤ q → P.localGroup n v p →+ P.localGroup n v q
  | .inl v, p, q, h =>
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    haveI := P.inf_liesOver v h
    (infLocalTransition K p.1 q.1 (P.inf v p) (P.inf v q) n).hom.toAddMonoidHom
  | .inr v, p, q, h =>
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    haveI := P.fin_liesOver v h
    (localTransition K p.1 q.1 (P.fin v p) (P.fin v q) n).hom.toAddMonoidHom

set_option maxHeartbeats 4000000 in
theorem shapiro_placeProj_inr (v : HeightOneSpectrum (𝓞 K.1)) (p : GLevel K)
    (y : cohomology (ideleRep K.1 p.1.1) n) :
    P.shapiro n (.inr v) p ((cohomologyMap (placeProj (.inr v)) n).hom y) =
      (finiteComponent (P.fin v p) n).hom y := by
  change (finiteShapiroIso v (P.fin v p) n).hom.hom
    ((cohomologyMap (finiteProjAboveRep (K := K.1) (L := p.1.1) v) n).hom y) = _
  rw [← placeProj_comp_finiteShapiroIso (P.fin v p) n]
  rfl

set_option maxHeartbeats 4000000 in
theorem shapiro_placeProj_inl (v : InfinitePlace K.1) (p : GLevel K)
    (y : cohomology (ideleRep K.1 p.1.1) n) :
    P.shapiro n (.inl v) p ((cohomologyMap (placeProj (.inl v)) n).hom y) =
      (infiniteComponent (P.inf v p) n).hom y := by
  change (infiniteShapiroIso v (P.inf v p) n).hom.hom
    ((cohomologyMap (infiniteProjAboveRep (K := K.1) (L := p.1.1) v) n).hom y) = _
  rw [← placeProj_comp_infiniteShapiroIso (P.inf v p) n]
  rfl

set_option maxHeartbeats 8000000 in

def levelDecomposition : LevelDecomposition K n where
  L := P.localGroup n
  e := P.shapiro n
  lt := P.transition n
  compat v p q h y := by
    rcases v with v | v
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      haveI := P.inf_liesOver v h
      rw [shapiro_placeProj_inl, shapiro_placeProj_inl]
      exact congrArg (fun φ => φ.hom y)
        (levelTransition_comp_infiniteComponent (P.inf v p) (P.inf v q) n)
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      haveI := P.fin_liesOver v h
      rw [shapiro_placeProj_inr, shapiro_placeProj_inr]
      exact congrArg (fun φ => φ.hom y)
        (levelTransition_comp_finiteComponent (P.fin v p) (P.fin v q) n)

end CompatiblePlaces

end

end GroundTheory.ProfCoh
end
