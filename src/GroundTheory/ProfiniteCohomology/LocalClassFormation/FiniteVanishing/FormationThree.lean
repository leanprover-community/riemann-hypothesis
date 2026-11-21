import Mathlib
import GroundTheory.ProfiniteCohomology.ClassFormations
import GroundTheory.ProfiniteCohomology.Colimit
import GroundTheory.ProfiniteCohomology.ShapiroDefs
import GroundTheory.TateCohomology.TateTheorem
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.IntScalars

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits groupCohomology

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem additive_addMonoidHom_int_eq_zero (f : Additive Γ →+ ℤ) : f = 0 := by
  refine AddMonoidHom.ext fun g => ?_
  have h : (Nat.card (Additive Γ) : ℤ) * f g = 0 := by
    rw [← nsmul_eq_mul, ← map_nsmul, card_nsmul_eq_zero', map_zero]
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 Nat.card_pos.ne')

theorem isZero_groupCohomology_one_trivial_int :
    IsZero (groupCohomology (Rep.trivial ℤ Γ ℤ) 1) := by
  refine IsZero.of_iso ?_ (H1IsoOfIsTrivial (Rep.trivial ℤ Γ ℤ))
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun f g => ?_⟩
  rw [additive_addMonoidHom_int_eq_zero f, additive_addMonoidHom_int_eq_zero g]

theorem subsingleton_groupCohomology_three_of_tate_int (M : Rep ℤ Γ) (u : groupCohomology M 2)
    (h1 : ∀ S : Subgroup Γ, IsZero (groupCohomology (Rep.res S.subtype M) 1))
    (h2 : ∀ S : Subgroup Γ,
      addOrderOf (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u) = Nat.card S)
    (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (Rep.res S.subtype M) 2),
      ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u) :
    Subsingleton (groupCohomology M 3) := by
  have hT1 : IsZero (tateCohomology (Rep.trivial ℤ Γ ℤ) ((1 : ℕ) : ℤ)) :=
    isZero_groupCohomology_one_trivial_int.of_iso
      ((TateCohomology.isoGroupCohomology 1).app (Rep.trivial ℤ Γ ℤ))
  have hT3 : IsZero (tateCohomology M (((1 : ℕ) : ℤ) + 2)) :=
    hT1.of_iso (GroundTheory.GroupCoh.tateTheoremIsoTop M u h1 h2 h3 _).symm
  have e3 : (((1 : ℕ) : ℤ) + 2) = ((3 : ℕ) : ℤ) := by norm_num
  rw [e3] at hT3
  exact ModuleCat.subsingleton_of_isZero
    (hT3.of_iso ((TateCohomology.isoGroupCohomology 3).app M).symm)

theorem subsingleton_groupCohomology_three_of_tate (M : Rep.{0} (ULift.{0} ℤ) Γ)
    (u : groupCohomology M 2)
    (h1 : ∀ S : Subgroup Γ, IsZero (groupCohomology (Rep.res S.subtype M) 1))
    (h2 : ∀ S : Subgroup Γ,
      addOrderOf ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2).hom u) = Nat.card S)
    (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (Rep.res S.subtype M) 2),
      ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2).hom u) :
    Subsingleton (groupCohomology M 3) := by
  have H := subsingleton_groupCohomology_three_of_tate_int (uliftIntToIntRep M)
    (groupCohomologyULiftIntAddEquiv M 2 u) (fun S => ?_) (fun S => ?_) (fun S y => ?_)
  · exact (groupCohomologyULiftIntAddEquiv M 3).injective.subsingleton
  · have : Subsingleton (groupCohomology (Rep.res S.subtype M) 1) :=
      ModuleCat.subsingleton_of_isZero (h1 S)
    have : Subsingleton (groupCohomology (uliftIntToIntRep (Rep.res S.subtype M)) 1) :=
      (groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) 1).symm.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · have e := groupCohomologyULiftIntAddEquiv_map_subtype M S 2 u
    change addOrderOf ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) 2).hom
      (groupCohomologyULiftIntAddEquiv M 2 u)) = Nat.card S
    rw [← e, AddEquiv.addOrderOf_eq]
    exact h2 S
  · obtain ⟨m, hm⟩ := h3 S ((groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) 2).symm y)
    refine ⟨m, ?_⟩
    change y = m • (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) 2).hom
      (groupCohomologyULiftIntAddEquiv M 2 u)
    rw [← groupCohomologyULiftIntAddEquiv_map_subtype, ← map_zsmul, ← hm, AddEquiv.apply_symm_apply]

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in

theorem exists_openSubgroup_subgroupOf_eq (U : OpenSubgroup G) (N : Subgroup (U : Subgroup G))
    (hN : IsOpen (N : Set (U : Subgroup G))) :
    ∃ V : OpenSubgroup G, V ≤ U ∧ (V : Subgroup G).subgroupOf U = N := by
  refine ⟨⟨N.map (U : Subgroup G).subtype, ?_⟩, Subgroup.map_subtype_le N, ?_⟩
  · exact U.isOpen.isOpenMap_subtype_val _ hN
  · exact Subgroup.comap_map_eq_self_of_injective (U : Subgroup G).subtype_injective N

variable {C : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep C] (F : ClassFormation C)

include F in

theorem ClassFormation.subsingleton_groupCohomology_three_quot (U : OpenSubgroup G)
    (N : Subgroup (U : Subgroup G)) [N.Normal] (hN : IsOpen (N : Set (U : Subgroup G))) :
    Subsingleton (groupCohomology
      ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants N) 3) := by
  obtain ⟨V, hVU, rfl⟩ := exists_openSubgroup_subgroupOf_eq U N hN
  have : ((V : Subgroup G).subgroupOf U).FiniteIndex :=
    finiteIndex_openSubgroup (⟨_, hN⟩ : OpenSubgroup (U : Subgroup G))
  have : Finite ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) :=
    Subgroup.finite_quotient_of_finiteIndex
  let : Fintype ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) := Fintype.ofFinite _
  exact subsingleton_groupCohomology_three_of_tate _ (F.groupFundamentalClass U V)
    (fun S => (F.tate_hypotheses hVU S).1) (fun S => (F.tate_hypotheses hVU S).2.1)
    (fun S => (F.tate_hypotheses hVU S).2.2)

include F in

theorem ClassFormation.subsingleton_cohomology_three (U : OpenSubgroup G) :
    Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype C) 3) := by
  have h0 : ∀ z : cohomology (Rep.res (U : Subgroup G).subtype C) 3, z = 0 := fun z => by
    obtain ⟨W, w, rfl⟩ := exists_inflation_eq (Rep.res (U : Subgroup G).subtype C) 3 z
    have := F.subsingleton_groupCohomology_three_quot U (W : Subgroup (U : Subgroup G)) W.isOpen
    rw [Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

end GroundTheory.ProfCoh
end
end
