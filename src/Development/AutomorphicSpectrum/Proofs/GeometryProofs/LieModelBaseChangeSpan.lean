module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.LieSpan

theorem span_range_pullback : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom c) ≫ x) E') (j : E → E'), (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) → Submodule.span R' (Set.range j) = ⊤ := by
  intro S G _ _ R R' _ _ c x E E' _ _ _ _ M M' j hj
  letI : Algebra R R' := c.toAlgebra
  letI : Module R E' := Module.compHom E' c
  haveI : IsScalarTower R R' E' :=
    ⟨fun r r' e => by
      show (c r * r') • e = c r • (r' • e)
      exact mul_smul _ _ _⟩
  let h : GlobalTheory.CompanionTheory.Ar.epsAt (Spec.map (CommRingCat.ofHom c) ≫ x) ⟶ GlobalTheory.CompanionTheory.Ar.epsAt x :=
    Over.homMk (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c))) (by
      show Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
        Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫
          Spec.map (CommRingCat.ofHom c) ≫ x
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom])
  have hl : h.left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) := rfl
  have hpt : ∀ e, M'.pt (j e) = h ≫ M.pt e := fun e =>
    Over.OverMorphism.ext (by rw [Over.comp_left, hl]; exact hj e)
  have hadd : ∀ a b, j (a + b) = j a + j b := by
    intro a b
    apply M'.inj
    rw [M'.add, hpt, hpt, hpt, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) (e : E), j (r • e) = c r • j e := by
    intro r e
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [M'.smul, hpt, hpt, Over.comp_left, Over.comp_left, M.smul, hl,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext a <;>
      simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom]
  let β : E →ₗ[R] E' :=
    { toFun := j, map_add' := hadd, map_smul' := fun r e => hsmul r e }
  obtain ⟨-, -, hbc⟩ := GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange S G R x E M
  have hb : IsBaseChange R' β := hbc R' E' M' β (fun e => hj e)
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := hb.equiv.surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s e =>
    rw [hb.equiv_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb' =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ ha hb'

end GlobalTheory.CompanionTheory.Ar.LieSpan
