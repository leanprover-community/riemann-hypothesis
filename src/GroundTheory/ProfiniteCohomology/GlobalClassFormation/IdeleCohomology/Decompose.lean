module

public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
public import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.IsDiscreteRepCoindStabRep
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [DiscreteTopology G]
  {ι : Type*} {P : Rep.{u} k G} {A : ι → Rep.{u} k G}

theorem eq_sum_cohomologyMap_of_pi [DecidableEq ι] (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (e : ∀ i, A i ⟶ P)
    (hep : ∀ i, e i ≫ p i = 𝟙 _) (hep' : ∀ i j, i ≠ j → e i ≫ p j = 0) (T : Finset ι) (n : ℕ)
    (hT : ∀ i ∉ T, IsZero (cohomology (A i) n)) (y : cohomology P n) :
    y = ∑ i ∈ T, (cohomologyMap (e i) n).hom ((cohomologyMap (p i) n).hom y) := by
  apply (cohomology_pi_bijective p hp n).1
  funext j

  simp only [← cohomologyMapAlong_id_eq_cohomologyMap, map_sum]
  by_cases hj : j ∈ T
  · rw [Finset.sum_eq_single j]
    · rw [← ModuleCat.comp_apply, ← cohomologyMapAlong_id_comp, ← ModuleCat.comp_apply,
        ← cohomologyMapAlong_id_comp, hep, Category.comp_id]
    · intro i _ hij
      rw [← ModuleCat.comp_apply, ← cohomologyMapAlong_id_comp, ← ModuleCat.comp_apply,
        ← cohomologyMapAlong_id_comp, hep' i j hij, Limits.comp_zero]
      have h0 : cohomologyMapAlong (MonoidHom.id G) continuous_id (0 : P ⟶ A j) n = 0 := by
        rw [cohomologyMapAlong, cochainsMapAlong_zero, HomologicalComplex.homologyMap_zero]
        rfl
      rw [h0]
      rfl
    · intro h
      exact absurd hj h
  · exact (ModuleCat.isZero_iff_subsingleton.1 (hT j hj)).elim _ _

end GroundTheory.ProfCoh
