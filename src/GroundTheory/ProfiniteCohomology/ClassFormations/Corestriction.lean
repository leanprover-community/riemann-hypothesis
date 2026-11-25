module

public import GroundTheory.ProfiniteCohomology.ClassFormations.CorestrictionDefs
public import GroundTheory.ProfiniteCohomology.ClassFormations
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace QZ

theorem exists_nsmul_eq {n : ℕ} (hn : n ≠ 0) (x : QZ) : ∃ y : QZ, n • y = x := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (toAddCircle x)
  refine ⟨mk (r / n), ?_⟩
  rw [← mk_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hn)]
  change toAddCircle.symm (r : AddCircle (1 : ℚ)) = x
  rw [show ((r : AddCircle (1 : ℚ))) = toAddCircle x from hr]
  exact toAddCircle.symm_apply_apply x

end QZ

namespace PreClassFormation

variable [CompactSpace G] {C : Rep.{u} k G} [IsDiscreteRep C] (F : PreClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U)

theorem inv_cohomologyCoresLE_cohomologyResLE (x : H2Open C U) :
    F.inv U ((cohomologyCoresLE C hVU 2).hom
        ((cohomologyResLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom x)) =
      F.inv V ((cohomologyResLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom x) := by
  rw [cohomologyCoresLE_cohomologyResLE, map_nsmul, F.inv_res U V hVU x]


omit [CompactSpace G] in
theorem cohomologyResLE_eq_of_inv (hVinj : Function.Injective (F.inv V)) {x : H2Open C V}
    {y : H2Open C U} (hy : (V : Subgroup G).relIndex U • F.inv U y = F.inv V x) :
    (cohomologyResLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom y = x :=
  hVinj (by rw [F.inv_res U V hVU y, hy])

end PreClassFormation

namespace ClassFormation

variable [CompactSpace G] {C : Rep.{u} k G} [IsDiscreteRep C] (F : ClassFormation C)
  {U V : OpenSubgroup G} (hVU : V ≤ U)


include F in
theorem cohomologyResLE_surjective :
    Function.Surjective (cohomologyResLE C (show (V : Subgroup G) ≤ U from hVU) 2).hom := by
  intro x
  obtain ⟨q, hq⟩ := QZ.exists_nsmul_eq (relIndex_ne_zero_of_isOpen V.isOpen (U : Subgroup G))
    (F.inv V x)
  obtain ⟨y, rfl⟩ := F.exists_inv_eq U q
  exact ⟨y, F.toPreClassFormation.cohomologyResLE_eq_of_inv hVU (F.inv_injective V) hq⟩

theorem inv_cohomologyCoresLE (x : H2Open C V) :
    F.inv U ((cohomologyCoresLE C hVU 2).hom x) = F.inv V x := by
  obtain ⟨y, rfl⟩ := F.cohomologyResLE_surjective hVU x
  exact F.toPreClassFormation.inv_cohomologyCoresLE_cohomologyResLE hVU y

end ClassFormation

section Quot

variable {U V : Subgroup G} [(V.subgroupOf U).Normal]

instance compactSpace_quotientGroup {H : Type*} [Group H] [TopologicalSpace H] [CompactSpace H]
    (N : Subgroup H) : CompactSpace (H ⧸ N) :=
  Quotient.compactSpace

end Quot

section CoresNaturality

theorem coindMap_res_comp_coindTrace [CompactSpace G] (U : OpenSubgroup G) {A B : Rep.{u} k G}
    (φ : A ⟶ B) :
    Rep.coindMap (U : Subgroup G).subtype ((Rep.resFunctor (U : Subgroup G).subtype).map φ) ≫
        coindTrace (U : Subgroup G) B =
      coindTrace (U : Subgroup G) A ≫ φ := by
  ext f
  change (coindTrace (U : Subgroup G) B).hom
      ((Rep.coindMap (U : Subgroup G).subtype ((Rep.resFunctor (U : Subgroup G).subtype).map φ)).hom f) =
    φ.hom ((coindTrace (U : Subgroup G) A).hom f)
  rw [coindTrace_hom_apply, coindTrace_hom_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [coindTraceTerm_apply, coindTraceTerm_apply]
    change B.ρ x (φ.hom (f.1 x⁻¹)) = φ.hom (A.ρ x (f.1 x⁻¹))
    rw [Rep.hom_comm_apply]

theorem cohomologyCores_naturality [CompactSpace G] (U : OpenSubgroup G) {A B : Rep.{u} k G}
    [IsDiscreteRep A] [IsDiscreteRep B] (φ : A ⟶ B) (n : ℕ) :
    cohomologyCores U A n ≫ cohomologyMap φ n =
      cohomologyMap ((Rep.resFunctor (U : Subgroup G).subtype).map φ) n ≫ cohomologyCores U B n := by
  rw [cohomologyCores, cohomologyCores, Category.assoc, ← cohomologyMap_comp,
    ← coindMap_res_comp_coindTrace, cohomologyMap_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, shapiroMap_naturality]

end CoresNaturality

end GroundTheory.ProfCoh
