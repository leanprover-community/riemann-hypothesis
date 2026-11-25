module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualCon

theorem cls_eq_evc_id {S : Scheme.{0}} {A T : Over S} {M : LB (A ⊗ T).left} (hM : M.IsLB) :
    cls M hM = evc hM (fst A T) (snd A T ≫ 𝟙 T) := by
  rw [Category.comp_id, evc, lift_fst_snd, Over.id_left, pull_id]

theorem cls_trans {S : Scheme.{0}} {A B B' B'' : Over S} {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left}
    {Q : LB (A ⊗ B'').left} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (x : B ⟶ B') (y : B' ⟶ B'')
    (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) (hy : LBIso P' (ev Q (fst A B') (snd A B' ≫ y))) :
    LBIso P (ev Q (fst A B) (snd A B ≫ x ≫ y)) := by
  refine (cls_eq_iff hP (pull_isLB hQ _)).1 ?_
  rw [(cls_eq_iff hP (pull_isLB hP' _)).2 hx, cls_ev hP', cls_ev hQ, evc,
    (cls_eq_iff hP' (pull_isLB hQ _)).2 hy, cls_ev hQ, pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

theorem rep_unique (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left)
    (b' : B' ⟶ S') (P' : LB (A ⊗ B').left) (h : Rep A b P) (h' : Rep A b' P') :
    ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  have hP := h.fam.isLB
  have hP' := h'.fam.isLB
  obtain ⟨x, ⟨hxb, hxP⟩, -⟩ := h'.univ B b P h.fam
  obtain ⟨y, ⟨hyb, hyP⟩, -⟩ := h.univ B' b' P' h'.fam
  have idB : LBIso P (ev P (fst A B) (snd A B ≫ 𝟙 B)) :=
    (cls_eq_iff hP (pull_isLB hP _)).1 (cls_eq_evc_id hP)
  have idB' : LBIso P' (ev P' (fst A B') (snd A B' ≫ 𝟙 B')) :=
    (cls_eq_iff hP' (pull_isLB hP' _)).1 (cls_eq_evc_id hP')
  have hxy : x ≫ y = 𝟙 B :=
    (h.univ B b P h.fam).unique ⟨by rw [Category.assoc, hyb, hxb], cls_trans hP hP' hP x y hxP hyP⟩
      ⟨Category.id_comp _, idB⟩
  have hyx : y ≫ x = 𝟙 B' :=
    (h'.univ B' b' P' h'.fam).unique ⟨by rw [Category.assoc, hxb, hyb], cls_trans hP' hP hP' y x hyP hxP⟩
      ⟨Category.id_comp _, idB'⟩
  exact ⟨⟨x, y, hxy, hyx⟩, hxb, (same_id_iff hP hP' x).2 hxP⟩

end GlobalTheory.DualCon
