module

public import Development.EtaleCohomology.EtaleSheaves.stupidPf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section
open CategoryTheory Limits ZeroObject

namespace LateralTheory.E.trunc0Pf

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

lemma isZero_tr (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (i : ℤ) (hi : i ≠ 0) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE 0)).X i) := by
  rcases lt_or_gt_of_ne hi with h | h
  · apply HomologicalComplex.isZero_stupidTrunc_X
    intro j; simp; omega
  · exact (K.isZero_of_isStrictlyLE 0 i h).of_iso
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := i.toNat) (by simp; omega))

lemma cochainComplex_singleFunctor_zero_map_f_zero {A B : C} (f : A ⟶ B) :
    ((CochainComplex.singleFunctor C 0).map f).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv :=
  HomologicalComplex.single_map_f_self _ _ f

def eIso (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE 0) ≅ (CochainComplex.singleFunctor C 0).obj (K.X 0) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if h : i = 0 then (by
        subst h
        exact K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp) ≪≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).symm)
      else (isZero_tr K i h).iso (HomologicalComplex.isZero_single_obj_X _ 0 _ i h))
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      by_cases hj : j = 0
      · exact (isZero_tr K i (by omega)).eq_of_src _ _
      · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ j hj).eq_of_tgt _ _)

lemma stupidTruncGEZeroIsoSingle_hom_f_zero (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    (eIso K).hom.f 0 = (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp)).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).inv := by
  simp [eIso]

lemma nat {K L : CochainComplex C ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE 0) ≫ (eIso L).hom =
      (eIso K).hom ≫ (CochainComplex.singleFunctor C 0).map (g.f 0) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = 0
  · subst h
    simp only [HomologicalComplex.comp_f, stupidTruncGEZeroIsoSingle_hom_f_zero, cochainComplex_singleFunctor_zero_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc]
    erw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ i h).eq_of_tgt _ _

theorem trunc0_of : LateralTheory.E.stupidPf.trunc0 := by
  intro R _ K L _ _ g
  exact ⟨eIso K, eIso L, nat g⟩

end LateralTheory.E.trunc0Pf
