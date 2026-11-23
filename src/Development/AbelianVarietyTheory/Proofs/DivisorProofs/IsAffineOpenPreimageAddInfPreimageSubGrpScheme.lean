module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SumAffine

theorem isIso_shear {C : Type*} [Category C] [CartesianMonoidalCategory C] (A T : C) [GrpObj A]
    (b : T ⟶ A) : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)) := by
  refine ⟨lift (fst A T * (snd A T ≫ b⁻¹)) (snd A T), ?_, ?_⟩
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp

theorem isAffineOpen_preimage_translate (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R)) [IsAffine T.left] (b : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ b)).left ⁻¹ᵁ V) := by
  haveI : IsAffine (Sp R) := by unfold Sp; infer_instance
  haveI : IsAffineHom T.hom := inferInstance
  haveI : IsAffineHom (fst A T).left := by
    change IsAffineHom (pullback.fst A.hom T.hom)
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback A.hom T.hom).flip inferInstance
  haveI := isIso_shear A T b
  have h : fst A T * (snd A T ≫ b) = lift (fst A T * (snd A T ≫ b)) (snd A T) ≫ fst A T := by simp
  haveI : IsAffineHom (fst A T * (snd A T ≫ b)).left := by
    rw [h, Over.comp_left]
    haveI : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)).left :=
      inferInstanceAs (IsIso ((Over.forget (Sp R)).map (lift (fst A T * (snd A T ≫ b)) (snd A T))))
    infer_instance
  exact hV.preimage _

theorem isAffineOpen_preimage_add_inf_preimage_sub (R : Type) [CommRing R] (A : Over (Sp R))
    [GrpObj A] [IsSeparated A.hom] (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R))
    [IsAffine T.left] (a : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓
      (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  have h1 := isAffineOpen_preimage_translate R A V hV T a
  have h2 := isAffineOpen_preimage_translate R A V hV T a⁻¹
  rw [GrpObj.comp_inv] at h2
  haveI : IsSeparated (snd A T).left := by
    change IsSeparated (pullback.snd A.hom T.hom)
    infer_instance
  haveI : (A ⊗ T).left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (snd A T).left]
    infer_instance
  exact h1.inf h2

end GlobalTheory.SumAffine
