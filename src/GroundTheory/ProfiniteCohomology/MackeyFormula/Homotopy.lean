module

public import GroundTheory.ProfiniteCohomology.MackeyFormula.Cohomology
public import GroundTheory.ProfiniteCohomology.MackeyFormula.ConjHomotopy
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
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

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (V : OpenSubgroup G) (ι : H →ₜ* G) (N : Rep.{u} k (V : Subgroup G)) [IsDiscreteRep N]

noncomputable def shapiroCochains :
    cochainsComplex (Rep.coind (V : Subgroup G).subtype N) ⟶ cochainsComplex N :=
  cochainsMapAlong (V : Subgroup G).subtype (continuous_subgroup_subtype _)
    (coindEvalOne (V : Subgroup G) N)

omit [CompactSpace H] in
theorem homologyMap_shapiroCochains (n : ℕ) :
    HomologicalComplex.homologyMap (shapiroCochains V N) n = shapiroMap V N n :=
  rfl

noncomputable def mackeyCochainsMap (x : G) :
    cochainsComplex (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N)) ⟶
      cochainsComplex (mackeyRep (V : Subgroup G) ι.toMonoidHom N x) :=
  cochainsMap (mackeyProj (V : Subgroup G) ι.toMonoidHom N x) ≫
    cochainsMapAlong (mackeySubgroup (V : Subgroup G) ι.toMonoidHom x).subtype
      (continuous_subgroup_subtype _)
      (coindEvalOne (mackeySubgroup (V : Subgroup G) ι.toMonoidHom x)
        (mackeyRep (V : Subgroup G) ι.toMonoidHom N x))

theorem homologyMap_mackeyCochainsMap (x : G) (n : ℕ) :
    HomologicalComplex.homologyMap (mackeyCochainsMap V ι N x) n = mackeyCohomologyMap V ι N x n := by
  rw [mackeyCochainsMap, HomologicalComplex.homologyMap_comp]
  rfl

theorem innerConj_comp_mackeyCochainsMap (x : G) :
    cochainsMapAlong (innerConjHom x⁻¹) (continuous_innerConjHom x⁻¹)
        (innerConjMor (Rep.coind (V : Subgroup G).subtype N) x⁻¹) ≫
      cochainsMapAlong ι.toMonoidHom (continuous_toMonoidHom ι)
        (𝟙 (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N))) ≫
      mackeyCochainsMap V ι N x =
    shapiroCochains V N ≫ cochainsMapAlong (mackeyConj (V : Subgroup G) ι.toMonoidHom x)
      (continuous_toMonoidHom (mackeyConjₜ V ι x)) (𝟙 _) := by
  rw [mackeyCochainsMap, ← cochainsMapAlong_id_eq_cochainsMap, shapiroCochains]
  rw [← cochainsMapAlong_comp, ← cochainsMapAlong_comp, ← cochainsMapAlong_comp]
  refine Eq.trans ?_ (cochainsMapAlong_comp _ _ _ _ _ _)
  refine cochainsMapAlong_congr _ _ _ _ ?_ (fun f => ?_)
  · ext h
    change x⁻¹⁻¹ * ι.toMonoidHom (h : H) * x⁻¹ = x * ι.toMonoidHom (h : H) * x⁻¹
    rw [inv_inv]
  · change f.1 (x * ι.toMonoidHom 1 * x⁻¹) = f.1 1
    rw [map_one, mul_one, mul_inv_cancel]

noncomputable def mackeyHomotopy (x : G) :
    Homotopy (shapiroCochains V N ≫ cochainsMapAlong (mackeyConj (V : Subgroup G) ι.toMonoidHom x)
        (continuous_toMonoidHom (mackeyConjₜ V ι x)) (𝟙 _))
      (cochainsMapAlong ι.toMonoidHom (continuous_toMonoidHom ι)
          (𝟙 (Rep.res ι.toMonoidHom (Rep.coind (V : Subgroup G).subtype N))) ≫
        mackeyCochainsMap V ι N x) :=
  (Homotopy.ofEq (innerConj_comp_mackeyCochainsMap V ι N x).symm).trans
    ((conjHomotopy (Rep.coind (V : Subgroup G).subtype N) x⁻¹).compRightId _)

end GroundTheory.ProfCoh
