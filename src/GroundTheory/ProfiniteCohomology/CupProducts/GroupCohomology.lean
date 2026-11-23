module

public import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
public import GroundTheory.ProfiniteCohomology.ColimitDefs
public import GroundTheory.TateCohomology.CupProduct
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]


variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}


section Levels

variable (U : OpenNormalSubgroup G) {p q n : ℕ}

theorem inflation_π (A : Rep.{u} k G) [IsDiscreteRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants (U : Subgroup G)) p) :
    inflation A U p (groupCohomology.π _ p z) =
      cohomologyπ A p (HomologicalComplex.cyclesMap (inflationCochains A U) p z) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (inflationCochains A U) p) z

theorem cochainOf_cocycleι_cyclesMap_inflationCochains (A : Rep.{u} k G) [IsDiscreteRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants (U : Subgroup G)) p) :
    cochainOf (A := A) (cocycleι (A := A) (p := p)
      (HomologicalComplex.cyclesMap (inflationCochains A U) p z)) =
      fun g => (groupCohomology.iCocycles (A.quotientToInvariants (U : Subgroup G)) p z
        (fun i => (g i : G ⧸ (U : Subgroup G))) : A) :=
  congrArg (fun ψ => cochainOf (A := A) (ψ.hom z))
    (HomologicalComplex.cyclesMap_i (inflationCochains A U) p)

theorem inflationCochains_comp_cochainsMap {A A' : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep A'] (f : A ⟶ A') :
    inflationCochains A U ≫ cochainsMap f =
      groupCohomology.cochainsMap (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) ≫ inflationCochains A' U := by
  ext n x : 3
  rfl

theorem inflation_comp_cohomologyMap {A A' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A']
    (f : A ⟶ A') (n : ℕ) :
    inflation A U n ≫ cohomologyMap f n =
      groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) n ≫ inflation A' U n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (inflationCochains_comp_cochainsMap U f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

theorem cohomologyMap_inflation {A A' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A']
    (f : A ⟶ A') (x : groupCohomology (A.quotientToInvariants (U : Subgroup G)) n) :
    cohomologyMap f n (inflation A U n x) =
      inflation A' U n (groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) n x) :=
  ConcreteCategory.congr_hom (inflation_comp_cohomologyMap U f n) x

variable (A B : Rep.{u} k G) [IsDiscreteRep A] [IsDiscreteRep B]

theorem cup_inflation (h : p + q = n)
    (x : groupCohomology (A.quotientToInvariants (U : Subgroup G)) p)
    (y : groupCohomology (B.quotientToInvariants (U : Subgroup G)) q) :
    GroundTheory.ProfCoh.cup h (inflation A U p x) (inflation B U q y) =
      inflation (A ⊗ B) U n (groupCohomology.map (MonoidHom.id _)
        (invariantsTensorHom A B (U : Subgroup G)) n (GroundTheory.GroupCoh.cupH h x y)) := by
  refine groupCohomology_induction_on x fun x => ?_
  refine groupCohomology_induction_on y fun y => ?_
  rw [inflation_π, inflation_π, cup_cohomologyπ, GroundTheory.GroupCoh.cupH_π,
    GroundTheory.GroupCoh.map_π_apply, inflation_π]
  congr 1
  apply cocycles_ext
  rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_cyclesMap_inflationCochains, cochainOf_cocycleι_cyclesMap_inflationCochains,
    cochainOf_cocycleι_cyclesMap_inflationCochains, GroundTheory.GroupCoh.iCocycles_cocyclesMap,
    GroundTheory.GroupCoh.iCocycles_cupCocycles]
  funext g
  simp only [GroundTheory.GroupCoh.cupCochain_apply]
  have hP : Fin.partialProd (fun i => (g i : G ⧸ (U : Subgroup G))) ⟨p, by omega⟩ =
      ((Fin.partialProd g ⟨p, by omega⟩ : G) : G ⧸ (U : Subgroup G)) :=
    partialProd_comp_monoidHom (QuotientGroup.mk' (U : Subgroup G)) g _
  rw [hP]
  rfl

end Levels

end GroundTheory.ProfCoh
