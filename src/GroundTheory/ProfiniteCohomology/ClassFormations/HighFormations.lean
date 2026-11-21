import Mathlib
import GroundTheory.TateCohomology.TateCup
import GroundTheory.TateCohomology.CupTateNatural
import GroundTheory.TateCohomology.CupFunctorial
import GroundTheory.ProfiniteCohomology.ClassFormations.Corestriction
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.FormationThree
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolDefs
import GroundTheory.ProfiniteCohomology.CupProducts.GroupCohomology
import GroundTheory.ProfiniteCohomology.GlobalClassFormation

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.GroupCoh

open CategoryTheory MonoidalCategory groupCohomology Rep

section Top

variable {k : Type} [CommRing k] {Γ : Type} [Group Γ]

abbrev topHom (Γ : Type) [Group Γ] : Γ →* (⊤ : Subgroup Γ) :=
  (Subgroup.topEquiv (G := Γ)).symm.toMonoidHom

def topBackHom (A : Rep k Γ) : res (topHom Γ) (res (⊤ : Subgroup Γ).subtype A) ⟶ A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def topBackTrivialHom : res (topHom Γ) (Rep.trivial k (⊤ : Subgroup Γ) k) ⟶ Rep.trivial k Γ k :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

theorem map_topBackHom_map_subtype (A : Rep k Γ) (n : ℕ) (x : groupCohomology A n) :
    map (topHom Γ) (topBackHom A) n (map (⊤ : Subgroup Γ).subtype (𝟙 _) n x) = x := by
  have h := map_comp (⊤ : Subgroup Γ).subtype (topHom Γ) (𝟙 (res (⊤ : Subgroup Γ).subtype A))
    (topBackHom A) n
  have h' : map ((⊤ : Subgroup Γ).subtype.comp (topHom Γ))
      ((resFunctor (topHom Γ)).map (𝟙 (res (⊤ : Subgroup Γ).subtype A)) ≫ topBackHom A) n =
      map (MonoidHom.id Γ) (𝟙 A) n :=
    map_congr (MonoidHom.ext fun _ => rfl) rfl n
  rw [h', map_id] at h
  exact (congrArg (fun f => f.hom x) h).symm

theorem topBack_rightUnitor (A : Rep k Γ) :
    ((resFunctor (topHom Γ)).map (ρ_ (res (⊤ : Subgroup Γ).subtype A)).hom ≫
        topBackHom A).hom.toLinearMap =
      ((resFunctor (MonoidHom.id Γ)).map (resTensorHom (topHom Γ) (topBackHom A) topBackTrivialHom) ≫
        (ρ_ A).hom).hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

end Top

section Tate

variable {Γ : Type} [Group Γ] [Fintype Γ] (M : Rep ℤ Γ) (u : groupCohomology M 2)
  (h1 : ∀ S : Subgroup Γ, Limits.IsZero (groupCohomology (res S.subtype M) 1))
  (h2 : ∀ S : Subgroup Γ,
    addOrderOf (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
  (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (res S.subtype M) 2),
    ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

omit [Fintype Γ] in

theorem tateIsoH_map_apply' {X Y : Rep ℤ Γ} [Fintype Γ] (φ : X ⟶ Y) {p : ℤ} (n : ℕ) [NeZero n]
    (hp : p = n) (x : tateCohomology X p) :
    (tateIsoH Y p n hp).hom.hom (((tateCohomologyFunctor p).map φ).hom x) =
      groupCohomology.map (MonoidHom.id Γ) φ n ((tateIsoH X p n hp).hom.hom x) := by
  subst hp
  exact tateIsoH_map_apply φ n x

include h1 h2 h3

theorem exists_cupH_top (n : ℕ) [NeZero n] [Fintype (⊤ : Subgroup Γ)]
    (x : groupCohomology (res (⊤ : Subgroup Γ).subtype M) (n + 2)) :
    ∃ y : groupCohomology (Rep.trivial ℤ (⊤ : Subgroup Γ) ℤ) n, (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
      x = map (MonoidHom.id _) (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom (n + 2)
        (cupH (add_comm 2 n) (map (⊤ : Subgroup Γ).subtype (𝟙 (res (⊤ : Subgroup Γ).subtype M)) 2 u)
          y) := by
  have hp : ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  let T := tateTheoremIso M u h1 h2 h3 ⊤ (n : ℤ)
  let s : tateCohomology (res (⊤ : Subgroup Γ).subtype M) ((n : ℤ) + 2) :=
    (tateIsoH (res (⊤ : Subgroup Γ).subtype M) _ (n + 2) hp).inv.hom x
  let y0 := T.inv.hom s
  refine ⟨(tateIsoH (Rep.trivial ℤ (⊤ : Subgroup Γ) ℤ) n n rfl).hom.hom y0,
    ⟨Fintype.card (⊤ : Subgroup Γ), Fintype.card_ne_zero, ?_⟩, ?_⟩
  · rw [← map_nsmul, card_smul_tateCohomology, map_zero]
  · have hs : T.hom.hom y0 = s := T.inv_hom_id_apply s
    have hx : x = (tateIsoH (res (⊤ : Subgroup Γ).subtype M) _ (n + 2) hp).hom.hom s :=
      ((tateIsoH (res (⊤ : Subgroup Γ).subtype M) _ (n + 2) hp).inv_hom_id_apply x).symm
    rw [hx, ← hs, tateTheoremIso_hom_apply M u ⊤ h1 h2 h3 (n : ℤ) y0, tateIsoH_map_apply' _ _ hp]
    erw [tateIsoH_tateCup (show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num) rfl hp (add_comm 2 (n : ℤ))
        (add_comm 2 n)]
    exact congrArg (fun t => (groupCohomology.map (MonoidHom.id _)
      (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom (n + 2)) (cupH (add_comm 2 n) t
        ((tateIsoH (Rep.trivial ℤ (⊤ : Subgroup Γ) ℤ) n n rfl).hom.hom y0)))
      ((tateIsoH (res (⊤ : Subgroup Γ).subtype M) 2 2 (by norm_num)).inv_hom_id_apply
        (map (⊤ : Subgroup Γ).subtype (𝟙 (res (⊤ : Subgroup Γ).subtype M)) 2 u))

theorem exists_cupH_of_tate (n : ℕ) [NeZero n] (x : groupCohomology M (n + 2)) :
    ∃ y : groupCohomology (Rep.trivial ℤ Γ ℤ) n, (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
      x = map (MonoidHom.id Γ) (ρ_ M).hom (n + 2) (cupH (add_comm 2 n) u y) := by
  classical
  obtain ⟨y, ⟨m, hm, hmy⟩, hx⟩ := exists_cupH_top M u h1 h2 h3 n
    (map (⊤ : Subgroup Γ).subtype (𝟙 _) (n + 2) x)
  refine ⟨map (topHom Γ) topBackTrivialHom n y, ⟨m, hm, by rw [← map_nsmul, hmy, map_zero]⟩, ?_⟩
  have hback := map_topBackHom_map_subtype M (n + 2) x
  rw [hx] at hback
  rw [← hback]
  have e1 := map_comp (MonoidHom.id (⊤ : Subgroup Γ)) (topHom Γ)
    (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom (topBackHom M) (n + 2)
  have e2 := map_comp (topHom Γ) (MonoidHom.id Γ)
    (resTensorHom (topHom Γ) (topBackHom M) topBackTrivialHom) (ρ_ M).hom (n + 2)
  have e3 : map ((MonoidHom.id (⊤ : Subgroup Γ)).comp (topHom Γ))
      ((resFunctor (topHom Γ)).map (ρ_ (res (⊤ : Subgroup Γ).subtype M)).hom ≫ topBackHom M) (n + 2) =
      map ((topHom Γ).comp (MonoidHom.id Γ))
      ((resFunctor (MonoidHom.id Γ)).map (resTensorHom (topHom Γ) (topBackHom M) topBackTrivialHom) ≫
        (ρ_ M).hom) (n + 2) := by
    exact map_congr (MonoidHom.ext fun _ => rfl) (topBack_rightUnitor M) (n + 2)
  have e4 := congrArg (fun f => f.hom (cupH (add_comm 2 n)
    (map (⊤ : Subgroup Γ).subtype (𝟙 (res (⊤ : Subgroup Γ).subtype M)) 2 u) y)) (e1.symm.trans (e3.trans e2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e4
  rw [e4, map_resTensorHom_cupH, map_topBackHom_map_subtype]

end Tate

end GroundTheory.GroupCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory groupCohomology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem subsingleton_cohomology_of_top {k : Type} [CommRing k] (A : Rep.{0} k G) [IsDiscreteRep A]
    (r : ℕ) (h : Subsingleton (cohomology (Rep.res (⊤ : Subgroup G).subtype A) r)) :
    Subsingleton (cohomology A r) := by
  let φ := cohomologyMapAlong (Subgroup.topEquiv (G := G)).toMonoidHom continuous_subtype_val
    (B := Rep.res (⊤ : Subgroup G).subtype A) (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩) r
  have hi : IsIso φ := isIso_cohomologyMapAlong_of_mulEquiv (Subgroup.topEquiv (G := G))
    continuous_subtype_val (continuous_id.subtype_mk _) (B := Rep.res (⊤ : Subgroup G).subtype A)
    (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩) Function.bijective_id r
  exact ((ModuleCat.mono_iff_injective φ).1 inferInstance).subsingleton

section Int

variable {C : Rep.{0} ℤ G} [IsDiscreteRep C] (F : ClassFormation C)

include F in

theorem ClassFormation.exists_cupH_quot (U : OpenSubgroup G) (N : Subgroup (U : Subgroup G))
    [N.Normal] (hN : IsOpen (N : Set (U : Subgroup G))) (n : ℕ) [NeZero n]
    (w : groupCohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants N) (n + 2)) :
    ∃ (a : groupCohomology ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants N) 2)
      (y : groupCohomology (Rep.trivial ℤ ((U : Subgroup G) ⧸ N) ℤ) n),
      (∃ m : ℕ, m ≠ 0 ∧ m • y = 0) ∧
        w = map (MonoidHom.id _) (ρ_ _).hom (n + 2) (GroundTheory.GroupCoh.cupH (add_comm 2 n) a y) := by
  obtain ⟨V, hVU, rfl⟩ := exists_openSubgroup_subgroupOf_eq U N hN
  have : ((V : Subgroup G).subgroupOf U).FiniteIndex :=
    finiteIndex_openSubgroup (⟨_, hN⟩ : OpenSubgroup (U : Subgroup G))
  have : Finite ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) :=
    Subgroup.finite_quotient_of_finiteIndex
  let : Fintype ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) := Fintype.ofFinite _
  exact ⟨_, GroundTheory.GroupCoh.exists_cupH_of_tate _ (F.groupFundamentalClass U V)
    (fun S => (F.tate_hypotheses hVU S).1) (fun S => (F.tate_hypotheses hVU S).2.1)
    (fun S => (F.tate_hypotheses hVU S).2.2) n w⟩

def trivialToInvariantsHom {k H : Type} [CommRing k] [Group H] (N : Subgroup H) [N.Normal] :
    Rep.trivial k (H ⧸ N) k ⟶ (Rep.trivial k H k).quotientToInvariants N :=
  Rep.ofHom ⟨⟨⟨fun a => ⟨a, fun _ => rfl⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun g => by
    induction g using QuotientGroup.induction_on
    rfl⟩

theorem rightUnitor_quotientToInvariants {k H : Type} [CommRing k] [Group H] (A : Rep.{0} k H)
    (N : Subgroup H) [N.Normal] :
    ((𝟙 (A.quotientToInvariants N) ⊗ₘ trivialToInvariantsHom (k := k) N) ≫
        invariantsTensorHom A (Rep.trivial k H k) N ≫
        (Rep.quotientToInvariantsFunctor k N).map (ρ_ A).hom).hom.toLinearMap =
      (ρ_ (A.quotientToInvariants N)).hom.hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => Subtype.ext rfl

include F in

theorem ClassFormation.subsingleton_cohomology_of_three_le_int (U : OpenSubgroup G) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype C) r) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  have : NeZero n := ⟨by omega⟩
  suffices h : ∀ z : cohomology (Rep.res (U : Subgroup G).subtype C) (n + 2), z = 0 from
    ⟨fun a b => by rw [h a, h b]⟩
  intro z
  set A := Rep.res (U : Subgroup G).subtype C
  set B := Rep.trivial ℤ (U : Subgroup G) ℤ
  obtain ⟨W, w, rfl⟩ := exists_inflation_eq A (n + 2) z
  obtain ⟨a, y, ⟨m, hm, hmy⟩, hw⟩ :=
    F.exists_cupH_quot U (W : Subgroup (U : Subgroup G)) W.isOpen n w

  change inflation A W (n + 2) w = 0
  set t := inflation B W n
    (map (MonoidHom.id _) (trivialToInvariantsHom (W : Subgroup (U : Subgroup G))) n y) with ht
  have hmt : m • t = 0 := by
    rw [ht, ← map_nsmul, ← map_nsmul, hmy, map_zero, map_zero]

  have hz : inflation A W (n + 2) w =
      cohomologyMap (ρ_ A).hom (n + 2) (cup (add_comm 2 n) (inflation A W 2 a) t) := by
    have key := map_congr (f := MonoidHom.id ((U : Subgroup G) ⧸ (W : Subgroup (U : Subgroup G))))
      (g := MonoidHom.id _)
      (φ := (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))) ⊗ₘ
          trivialToInvariantsHom (k := ℤ) (W : Subgroup (U : Subgroup G))) ≫
        invariantsTensorHom A B (W : Subgroup (U : Subgroup G)) ≫
        (Rep.quotientToInvariantsFunctor ℤ (W : Subgroup (U : Subgroup G))).map (ρ_ A).hom)
      (ψ := (ρ_ (A.quotientToInvariants (W : Subgroup (U : Subgroup G)))).hom) rfl
      (rightUnitor_quotientToInvariants A (W : Subgroup (U : Subgroup G))) (n + 2)
    have hc := GroundTheory.GroupCoh.map_cupH (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))))
      (trivialToInvariantsHom (k := ℤ) (W : Subgroup (U : Subgroup G))) (add_comm 2 n) a y
    simp only [map_id, ModuleCat.hom_id, LinearMap.id_apply] at hc
    rw [ht, cup_inflation W A B (add_comm 2 n) a, cohomologyMap_inflation W (A := A ⊗ B) (A' := A) (ρ_ A).hom, hw, ← hc]
    congr 1
    refine (congrArg (fun f => f.hom (GroundTheory.GroupCoh.cupH (add_comm 2 n) a y)) key).symm.trans ?_
    have e1 := map_id_comp
      (𝟙 (A.quotientToInvariants (W : Subgroup (U : Subgroup G))) ⊗ₘ
          trivialToInvariantsHom (k := ℤ) (W : Subgroup (U : Subgroup G)))
      (invariantsTensorHom A B (W : Subgroup (U : Subgroup G)) ≫
        (Rep.quotientToInvariantsFunctor ℤ (W : Subgroup (U : Subgroup G))).map (ρ_ A).hom) (n + 2)
    have e2 := map_id_comp (invariantsTensorHom A B (W : Subgroup (U : Subgroup G)))
        ((Rep.quotientToInvariantsFunctor ℤ (W : Subgroup (U : Subgroup G))).map (ρ_ A).hom) (n + 2)
    refine (congrArg (fun f => f.hom (GroundTheory.GroupCoh.cupH (add_comm 2 n) a y)) e1).trans ?_
    exact congrArg (fun g => (map (MonoidHom.id _) (𝟙 (A.quotientToInvariants
      (W : Subgroup (U : Subgroup G))) ⊗ₘ trivialToInvariantsHom (k := ℤ) (W : Subgroup (U : Subgroup G)))
        (n + 2) ≫ g).hom (GroundTheory.GroupCoh.cupH (add_comm 2 n) a y)) e2

  obtain ⟨q, hq⟩ := QZ.exists_nsmul_eq hm (F.inv U (inflation A W 2 a))
  obtain ⟨β, rfl⟩ := (F.inv_bijective U).2 q
  have hβ : m • β = inflation A W 2 a :=
    (F.inv_bijective U).1 (by rw [map_nsmul, hq])
  rw [hz, ← hβ, map_nsmul, LinearMap.smul_apply, ← map_nsmul, hmt, map_zero, map_zero]

include F in

theorem ClassFormation.subsingleton_cohomology_top_of_three_le_int {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology C r) :=
  subsingleton_cohomology_of_top C r (F.subsingleton_cohomology_of_three_le_int ⊤ hr)

end Int

section ULift

variable {C : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep C] (F : ClassFormation C)

include F in

theorem ClassFormation.subsingleton_cohomology_of_three_le (U : OpenSubgroup G) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype C) r) := by
  have := (ClassFormation.toInt C F).subsingleton_cohomology_of_three_le_int U hr
  exact (cohomologyULiftIntAddEquiv (Rep.res (U : Subgroup G).subtype C) r).injective.subsingleton

include F in

theorem ClassFormation.subsingleton_cohomology_top_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology C r) :=
  subsingleton_cohomology_of_top C r (F.subsingleton_cohomology_of_three_le ⊤ hr)

end ULift

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

section Local

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem subsingleton_cohomology_galUnits_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology (galUnits.{0} K Ksep) r) :=
  (localClassFormationOfIsSepClosure K Ksep).subsingleton_cohomology_top_of_three_le hr

end Local

section Global

open GroundTheory.Global

theorem subsingleton_cohomology_classLimitRep_of_three_le (K : FiniteSubfield) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (classLimitRep K) r) :=
  (globalClassFormation K).subsingleton_cohomology_top_of_three_le_int hr

end Global

end GroundTheory.ProfCoh
end
