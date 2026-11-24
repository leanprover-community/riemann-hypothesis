module

public import GroundTheory.TateCohomology.ResCores
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Additive

variable [Fintype G]

instance tateCohomologyFunctor_additive (n : ℤ) :
    (tateCohomologyFunctor (R := k) (G := G) n).Additive := by
  unfold tateCohomologyFunctor
  infer_instance

end Additive

section Rep

variable (S : Subgroup G) [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex


omit [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)] in
theorem indResAdjunction_counit_app_hom_mk (A : Rep.{u} k G) (g : G) (a : A) :
    ((indResAdjunction k S.subtype).counit.app A).hom
      (Representation.IndV.mk S.subtype (res S.subtype A).ρ g a) = A.ρ g⁻¹ a := by
  change ((indResHomEquiv _ _ _).symm (𝟙 _)).hom _ = _
  simp

theorem unit_comp_indCoindIso_inv_comp_counit (A : Rep.{u} k G) :
    (resCoindAdjunction.{u, u} k S.subtype).unit.app A ≫ (indCoindIso (res S.subtype A)).inv ≫
      (indResAdjunction.{u} k S.subtype).counit.app A = S.index • 𝟙 A := by
  ext a
  change ((indResAdjunction k S.subtype).counit.app A).hom
      (coindToInd (res S.subtype A) (((resCoindAdjunction.{u, u} k S.subtype).unit.app A).hom a)) =
    S.index • a

  rw [coindToInd_apply, map_sum]
  refine (Finset.sum_congr rfl (g := fun _ => a) fun x _ => ?_).trans ?_
  · induction x using Quotient.inductionOn with
    | h g =>
      rw [Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]
      change A.ρ g⁻¹ (A.ρ g a) = a
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · rw [Finset.sum_const, Finset.card_univ]
    congr 1
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]
    rfl

end Rep

section Tate

variable [Fintype G] (S : Subgroup G) [Fintype S]


open scoped Classical in
theorem tateIndIso_inv_eq (B : Rep.{u} k S) (n : ℤ) :
    (tateIndIso S B n).inv =
      (tateCoindIso S B n).inv ≫ (tateCohomologyFunctor n).map (indCoindIso.{u, u, u} B).inv :=
  rfl

theorem tateRes_app_comp_tateCores_app (A : Rep.{u} k G) (n : ℤ) :
    (tateRes S n).app A ≫ (tateCores S n).app A = S.index • 𝟙 (tateCohomology A n) := by
  rw [tateRes_app, tateCores_app, tateIndIso_inv_eq, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp,
    unit_comp_indCoindIso_inv_comp_counit, Functor.map_nsmul]
  exact congrArg (S.index • ·) ((tateCohomologyFunctor n).map_id A)

end Tate

end GroundTheory.GroupCoh
