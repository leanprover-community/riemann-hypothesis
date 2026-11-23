module

public import GroundTheory.ProfiniteCohomology.ClassFormations.CorestrictionDefs
public import GroundTheory.ProfiniteCohomology.ClassFormations
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

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

namespace ClassFormation

variable [CompactSpace G] [TotallyDisconnectedSpace G] {C : Rep.{u} k G} [IsDiscreteRep C]
  (F : ClassFormation C) {U V : OpenSubgroup G} (hVU : V ≤ U)
  [((V : Subgroup G).subgroupOf U).Normal]

end ClassFormation

namespace ClassFormationAt

variable [CompactSpace G] {P : Set Nat.Primes} {C : Rep.{u} k G} [IsDiscreteRep C]
  (F : ClassFormationAt P C) {U V : OpenSubgroup G} (hVU : V ≤ U)

end ClassFormationAt

end GroundTheory.ProfCoh
