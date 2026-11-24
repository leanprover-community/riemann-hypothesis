module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FunctionFieldCoords

theorem map_genericPoint_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem functionFieldMap_finite {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W)
    [IsDominant f] (h : f.residueDegree (genericPoint M) ≠ 0) : (functionFieldMap f).Finite := by
  have hfin : (f.residueFieldMap (genericPoint M)).hom.Finite := by
    letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
    change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
      at h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  have hsurj : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      Function.Surjective (W.presheaf.stalkSpecializes h).hom := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact fun a => ⟨a, rfl⟩
  have hinj : Function.Injective (M.residue (genericPoint M)).hom :=
    RingHom.injective (f := ((M.residue (genericPoint M)).hom : M.functionField →+* _))
  let e := RingEquiv.ofBijective (M.residue (genericPoint M)).hom
    ⟨hinj, M.residue_surjective _⟩
  have key : ∀ (hs : f (genericPoint M) ⤳ genericPoint W),
      ((W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
    intro hs
    have hc : (M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (f.residueFieldMap (genericPoint M)).hom.comp
          ((W.residue _).hom.comp (W.presheaf.stalkSpecializes hs).hom) := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
        Category.assoc, Category.assoc, Scheme.residue_residueFieldMap]
    have h1 : ((M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
      rw [hc]
      exact hfin.comp (RingHom.Finite.of_surjective _
        ((W.residue_surjective _).comp (hsurj hs (map_genericPoint_eq f))))
    have h2 : (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (e.symm : _ →+* _).comp ((M.residue (genericPoint M)).hom.comp
          (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom) := by
      ext a
      exact (e.symm_apply_apply _).symm
    rw [h2]
    exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp h1
  exact key _

end GlobalTheory.FunctionFieldCoords

theorem GlobalTheory.functionField_coords : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f], f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) ∧ ∀ x, (∀ j, co j x = 0) → x = 0 := by
  intro M W _ _ f _ h
  letI := (functionFieldMap f).toAlgebra
  haveI : Module.Finite W.functionField M.functionField :=
    GlobalTheory.FunctionFieldCoords.functionFieldMap_finite f h
  let b := Module.finBasis W.functionField M.functionField
  refine ⟨Module.finrank W.functionField M.functionField, fun j => (b.coord j).toAddMonoidHom,
    fun j c x => ?_, fun x hx => ?_⟩
  · change b.coord j (c • x) = c * b.coord j x
    rw [map_smul, smul_eq_mul]
  · exact b.ext_elem fun i => by simpa using hx i
