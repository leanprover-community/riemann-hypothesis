module

public import GroundTheory.TateCohomology.TateShapiro
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]


section Res

noncomputable def tateRes (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := G) n ⟶
      resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Rep.resCoindAdjunction.{u, u} k S.subtype).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (resFunctor S.subtype) (tateCoindNatIso S n).hom

lemma tateRes_app (n : ℤ) (A : Rep.{u} k G) :
    (tateRes S n).app A =
      (tateCohomologyFunctor n).map ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A) ≫
        (tateCoindIso S (res S.subtype A) n).hom := by
  simp only [tateRes, NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

end Res

section Cores


open scoped Classical in
noncomputable def tateCores (n : ℤ) :
    resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n ⟶
      tateCohomologyFunctor (R := k) (G := G) n :=
  Functor.whiskerLeft (resFunctor S.subtype) (tateIndNatIso S n).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Rep.indResAdjunction.{u} k S.subtype).counit _ ≫
    (Functor.leftUnitor _).hom

lemma tateCores_app (n : ℤ) (A : Rep.{u} k G) :
    (tateCores S n).app A =
      (tateIndIso S (res S.subtype A) n).inv ≫
        (tateCohomologyFunctor n).map ((Rep.indResAdjunction.{u} k S.subtype).counit.app A) := by
  simp only [tateCores, NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

end Cores

end GroundTheory.GroupCoh
