module

public import GroundTheory.ProfiniteCohomology.Shapiro
public import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
public import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section SubgroupOf

variable {U V : Subgroup G} (h : V ≤ U) (A : Rep.{u} k G)

def resSubgroupOfInvHom :
    Rep.res (Subgroup.subgroupOfEquivOfLe h).toMonoidHom (Rep.res V.subtype A) ⟶
      Rep.res (V.subgroupOf U).subtype (Rep.res U.subtype A) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable [IsDiscreteRep A]

@[reassoc]
theorem cohomologyMapAlong_resSubgroupOfHom_comp (n : ℕ) :
    cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
        (continuous_subgroupOfEquivOfLe_symm h) (resSubgroupOfHom h A) n ≫
      cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
        (continuous_subgroupOfEquivOfLe h) (resSubgroupOfInvHom h A) n = 𝟙 _ := by
  rw [← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_eq_id _ _ (by ext; rfl) (fun _ => rfl) n

end SubgroupOf

abbrev openSubgroupOf (U V : OpenSubgroup G) : OpenSubgroup (U : Subgroup G) where
  toSubgroup := (V : Subgroup G).subgroupOf U
  isOpen' := V.isOpen.preimage continuous_subtype_val

variable [CompactSpace G] (C : Rep.{u} k G) [IsDiscreteRep C]

noncomputable def cohomologyCoresLE {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    cohomology (Rep.res (V : Subgroup G).subtype C) n ⟶
      cohomology (Rep.res (U : Subgroup G).subtype C) n :=
  cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).toMonoidHom
      (continuous_subgroupOfEquivOfLe _) (resSubgroupOfInvHom _ C) n ≫
    cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) n

theorem cohomologyCoresLE_eq {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    cohomologyCoresLE C h n =
      cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).toMonoidHom
          (continuous_subgroupOfEquivOfLe _) (resSubgroupOfInvHom _ C) n ≫
        cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) n :=
  rfl

theorem cohomologyResLE_comp_cohomologyCoresLE {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ) :
    cohomologyResLE C (show (V : Subgroup G) ≤ U from h) n ≫ cohomologyCoresLE C h n =
      (V : Subgroup G).relIndex U • 𝟙 _ := by
  rw [cohomologyResLE_eq_cohomologyRes_comp, cohomologyCoresLE, Category.assoc,
    cohomologyMapAlong_resSubgroupOfHom_comp_assoc]
  exact cohomologyRes_comp_cohomologyCores (openSubgroupOf U V) (Rep.res (U : Subgroup G).subtype C) n

theorem cohomologyCoresLE_cohomologyResLE {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ)
    (x : cohomology (Rep.res (U : Subgroup G).subtype C) n) :
    (cohomologyCoresLE C h n).hom ((cohomologyResLE C (show (V : Subgroup G) ≤ U from h) n).hom x) =
      (V : Subgroup G).relIndex U • x := by
  have := congrArg (fun φ => φ.hom x) (cohomologyResLE_comp_cohomologyCoresLE C h n)
  simpa using this

end GroundTheory.ProfCoh
