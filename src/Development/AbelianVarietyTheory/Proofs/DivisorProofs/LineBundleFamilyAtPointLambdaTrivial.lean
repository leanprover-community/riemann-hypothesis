module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

theorem upa_mul {Y : Over (Sp V)} (x y : Y ⟶ bc A φ) : upa φ (x * y) = upa φ x * upa φ y := by
  have h := (isGrpPullback_pullback A (φ ≫ T.hom)).2 Y x y (upa φ x) (upa φ y) rfl rfl
  exact Over.OverMorphism.ext h.symm

theorem upa_one {Y : Over (Sp V)} : upa φ (1 : Y ⟶ bc A φ) = 1 := by
  have e := upa_mul φ (1 : Y ⟶ bc A φ) 1
  rw [_root_.mul_one] at e
  exact left_eq_mul.1 e

theorem pull_cls_twist {N : LB (A ⊗ T).left} (hN : N.IsLB) (h : (twist A φ N).IsLB) {Y : Over (Sp V)}
    (x : Y ⟶ bc A φ) : CechPic.pull x.left (cls _ h) = evc hN (upa φ x) (upt φ Y) := by
  let u : up φ Y ⟶ bcR A φ := Over.homMk x.left (by
    show x.left ≫ (bc A φ).hom ≫ φ ≫ T.hom = Y.hom ≫ φ ≫ T.hom
    rw [← Category.assoc, Over.w x])
  have ha : u ≫ pa A φ = upa φ x := Over.OverMorphism.ext rfl
  have ht : u ≫ pt A φ = upt φ Y := Over.OverMorphism.ext (by
    show x.left ≫ (bc A φ).hom ≫ φ = Y.hom ≫ φ
    rw [← Category.assoc, Over.w x])
  have e := pull_evc hN u (pa A φ) (pt A φ)
  rw [ha, ht] at e
  exact e


variable (A) in
theorem triv_lam_twist (N : LB (A ⊗ T).left) (hF : Fam A N) : Triv (abelian₂ (bc A φ) (twist A φ N)) := by
  have hO : (twist A φ N).IsLB := pull_isLB hF.isLB _
  have hP : (abelian₂ (bc A φ) (twist A φ N)).IsLB := LB.isLB_linComb hO _ _
  refine (cls_eq_zero_iff hP).1 ?_
  have e : cls _ hP = lam (G := bc A φ) (cls (X := (bc A φ).left) _ hO) (fst (bc A φ) (bc A φ)) (snd (bc A φ) (bc A φ)) := cls_cube_two (G := bc A φ) (L := twist A φ N) hO _ _ hP
  rw [e, lam, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO,
    pull_cls_twist φ hF.isLB hO, upa_mul, upa_one, (isAdditive_iff hF.isLB).1 hF.add, hF.add.evc_one hF.isLB]
  simp only [add_sub_cancel_left, sub_self, add_zero]

end GlobalTheory.TwistFlat
