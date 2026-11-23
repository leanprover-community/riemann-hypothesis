module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

theorem dualMap_comp_epsMul (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul]
  · simp [dualMap, epsMul, mul_comm]

def epsBase (c : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, dualMap_comp_algebraMap])

def ptBase (c : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap c ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap c) rfl

theorem isTanAt_base (G : Over S) [GrpObj G] (c : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap c ≫ x) (epsBase c x ≫ v) := by
  have h1 : (ptBase c x ≫ (1 : Over.mk x ⟶ G)) = 1 := MonObj.comp_one _
  have h2 : spMap c ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (spMap c ≫ x) ⟶ G).left := by
    rw [← h1]; rfl
  unfold IsTanAt at hv ⊢
  rw [← h2, ← hv]
  change Spec.map _ ≫ spMap (dualMap c) ≫ v.left = spMap c ≫ Spec.map _ ≫ v.left
  simp only [spMap]
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, fst_comp_dualMap]

theorem exists_isBaseChange (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type)
    [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E' : Type) [AddCommGroup E'] [Module R' E']
    [Module R E'] [IsScalarTower R R' E'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E) (M : LieModel G x E) (j : E →ₗ[R] E'),
      IsBaseChange R' j ∧ ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := by
  obtain ⟨E, iA, iM, ⟨M⟩⟩ := lieModel_exists S G R x
  have hex : ∀ e, ∃ e', M'.pt e' = epsBase (algebraMap R R') x ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base G _ x _ (M.tan e))
  choose f hf using hex
  have hleft : ∀ e, (M'.pt (f e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := fun e => by
    rw [hf e]; rfl
  let j : E →ₗ[R] E' :=
    { toFun := f
      map_add' := fun a b => M'.inj (by
        rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul])
      map_smul' := fun r a => M'.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, ← algebraMap_smul R' r (f a), M'.smul, hleft, hleft, M.smul]
        simp only [spMap]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp, dualMap_comp_epsMul])) }
  refine ⟨E, iA, iM, M, j, GlobalTheory.T.lie_model_isBaseChange S G R R' x E E' M M' j fun e => ?_, hleft⟩
  simpa only [Category.comp_id, j, LinearMap.coe_mk, AddHom.coe_mk] using hleft e

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
