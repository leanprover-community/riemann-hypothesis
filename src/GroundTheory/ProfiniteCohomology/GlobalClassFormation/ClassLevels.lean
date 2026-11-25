module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ClassLimitDefs
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LevelDefs
public import GroundTheory.ProfiniteCohomology.Factor
import GroundTheory.ProfiniteCohomology.FilteredHomology
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LevelsColimit
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.NatCardGroupCohomologyTwoIdeleClassRepDvd
public import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Level

variable {F : FiniteSubfield} [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

theorem classSmul_of_restrictHom (g : K.1.fixingSubgroup) (c : IdeleClassGroup F.1) :
    (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • IdeleClassLimit.of F c = IdeleClassLimit.of F (restrictHom (E := F) g • c) := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective F.1 c
  have hx := congrArg IdeleLimit.toClassLimit (smul_of_restrictHom g x)
  rw [IdeleLimit.toClassLimit_smul, IdeleLimit.toClassLimit_of, IdeleLimit.toClassLimit_of] at hx
  exact hx


variable (K F) in
def classLevelMor :
    Rep.res (restrictHom (F := K) (E := F)) (ideleClassRep K.1 F.1) ⟶ classLimitRep K :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (IdeleClassLimit.of F)).toIntLinearMap, fun g => LinearMap.ext fun x =>
    congrArg Additive.ofMul (classSmul_of_restrictHom g x.toMul).symm⟩


variable (K F) in
def classLevelInfl (n : ℕ) : cohomology (ideleClassRep K.1 F.1) n ⟶ cohomology (classLimitRep K) n :=
  cohomologyMapAlong restrictHom continuous_restrictHom (classLevelMor K F) n

end Level

section Colimit

abbrev classLevelCochainsInfl (p : GLevel K) :
    cochainsComplex (ideleClassRep K.1 p.1.1) ⟶ cochainsComplex (classLimitRep K) :=
  cochainsMapAlong restrictHom continuous_restrictHom (classLevelMor K p.1)

theorem classLevelCochains_injective (p : GLevel K) (m : ℕ) :
    Function.Injective ((classLevelCochainsInfl p).f m).hom :=
  cochainsMapAlong_restrictHom_injective p (classLevelMor K p.1)
    (fun _ _ h => congrArg Additive.ofMul (IdeleClassLimit.of_injective p.1 (congrArg Additive.toMul h))) m

theorem exists_classLevelCochains_eq (m : ℕ) (x : (cochainsComplex (classLimitRep K)).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (ideleClassRep K.1 p.1.1)).X m),
      ((classLevelCochainsInfl p).f m).hom y = x :=
  exists_cochainsMapAlong_restrictHom_eq (fun p => ideleClassRep K.1 p.1.1) (fun p => classLevelMor K p.1)
    (fun a => by
      obtain ⟨E, x', hx'⟩ := IdeleClassLimit.exists_of (Additive.toMul a)
      exact ⟨E, fun p hle => ⟨Additive.ofMul (ideleClassMap hle x'), by
        change Additive.ofMul (IdeleClassLimit.of p.1 (ideleClassMap hle x')) = a
        rw [IdeleClassLimit.of_ideleClassMap, hx']; rfl⟩⟩) m x

theorem exists_classLevelInfl_eq (n : ℕ) (x : cohomology (classLimitRep K) n) :
    ∃ (p : GLevel K) (y : cohomology (ideleClassRep K.1 p.1.1) n), (classLevelInfl K p.1 n).hom y = x :=
  exists_cohomologyMapAlong_restrictHom_eq (fun p => ideleClassRep K.1 p.1.1) (fun p => classLevelMor K p.1)
    (fun p _ _ h => congrArg Additive.ofMul (IdeleClassLimit.of_injective p.1 (congrArg Additive.toMul h)))
    (fun a => by
      obtain ⟨E, x', hx'⟩ := IdeleClassLimit.exists_of (Additive.toMul a)
      exact ⟨E, fun p hle => ⟨Additive.ofMul (ideleClassMap hle x'), by
        change Additive.ofMul (IdeleClassLimit.of p.1 (ideleClassMap hle x')) = a
        rw [IdeleClassLimit.of_ideleClassMap, hx']; rfl⟩⟩) n x


end Colimit


variable (K) in
theorem isZero_cohomology_one_classLimitRep : Limits.IsZero (cohomology (classLimitRep K) 1) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hz : ∀ x : cohomology (classLimitRep K) 1, x = 0 := by
    intro x
    obtain ⟨p, y, rfl⟩ := exists_classLevelInfl_eq 1 x
    have h0 : Limits.IsZero (cohomology (ideleClassRep K.1 p.1.1) 1) :=
      isZero_groupCohomology_one_ideleClassRep.of_iso (cohomologyIsoGroupCohomology _ 1)
    rw [ModuleCat.isZero_iff_subsingleton] at h0
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end

end GroundTheory.ProfCoh
