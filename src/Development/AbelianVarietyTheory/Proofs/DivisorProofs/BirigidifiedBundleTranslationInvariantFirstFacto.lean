module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPic

namespace GlobalTheory.TranslFst

theorem iso_transl_fst : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB (G2 A).left), L.IsLB → (∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ h : 𝟙_ (Over S) ⟶ A, (∃ t : (L.pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, t.IsGen) → LBIso L (L.pull (GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A)).left) := by
  intro S A _ _ hA L hL h1 h2 h hh
  have hG : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have z : ∀ (f : A ⟶ G2 A), (∃ t : (L.pull f.left).Gen, t.IsGen) → pull f.left (cls L hL) = 0 := by
    intro f hf
    rw [← cls_pull hL _ (pull_isLB hL _)]
    exact (cls_eq_zero_iff _).2 hf
  have fac : ∀ (g : G2 A ⟶ A) (e : A ⟶ G2 A), pull e.left (cls L hL) = 0 → pull (g ≫ e).left (cls L hL) = 0 := by
    intro g e he
    rw [Over.comp_left, pull_comp, he, map_zero]
  have cube := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hG L hL (G2 A) (lift (fst A A) 1) (toUnit _ ≫ lift h 1)
    (lift 1 (snd A A))
  have e := (cls_linComb hL _ _ (LB.isLB_linComb hL _ _)).symm.trans ((cls_eq_zero_iff _).2 cube)
  have habc : (lift (fst A A) 1 : G2 A ⟶ G2 A) * (toUnit _ ≫ lift h 1) * lift 1 (snd A A) =
      GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A) := by
    ext <;> simp [GlobalTheory.UPel.HT.Hecke.transl, MonObj.mul_comp, MonObj.comp_mul]
  have hac : (lift (fst A A) 1 : G2 A ⟶ G2 A) * lift 1 (snd A A) = 𝟙 _ := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hbc : (toUnit _ ≫ lift h 1 : G2 A ⟶ G2 A) * lift 1 (snd A A) = snd A A ≫ lift (toUnit A ≫ h) (𝟙 A) := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hab : (lift (fst A A) 1 : G2 A ⟶ G2 A) * (toUnit _ ≫ lift h 1) = (fst A A * (toUnit _ ≫ h)) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have ha : (lift (fst A A) 1 : G2 A ⟶ G2 A) = fst A A ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hb : (toUnit _ ≫ lift h 1 : G2 A ⟶ G2 A) = (toUnit _ ≫ h) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have hc : (lift 1 (snd A A) : G2 A ⟶ G2 A) = snd A A ≫ lift 1 (𝟙 A) := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have h1' : (1 : G2 A ⟶ G2 A) = (1 : G2 A ⟶ A) ≫ lift (𝟙 A) 1 := by
    ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  simp only [Fin.sum_univ_eight, Matrix.cons_val] at e
  rw [habc, hac, hbc, hab, ha, hb, hc, h1', Over.id_left, pull_id] at e
  simp only [fun g => fac g _ (z _ h1), fun g => fac g _ (z _ h2), fun g => fac g _ (z _ hh)] at e
  have key : pull (GlobalTheory.UPel.HT.Hecke.transl (lift h 1 : 𝟙_ (Over S) ⟶ G2 A)).left (cls L hL) = cls L hL := by
    simp only [one_smul, neg_smul, smul_zero, neg_zero, add_zero, zero_add] at e
    exact eq_of_sub_eq_zero ((sub_eq_add_neg _ _).trans e)
  refine (cls_eq_iff hL (pull_isLB hL _)).1 ?_
  rw [cls_pull hL, key]

end GlobalTheory.TranslFst
