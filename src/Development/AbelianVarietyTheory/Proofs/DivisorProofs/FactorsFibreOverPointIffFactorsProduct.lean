module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem factor_ker_iff {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V]
    (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T) (Y : Over (Sp V)) (x : Y ⟶ bc A φ) :
    (∃ y : Y ⟶ ker A φ h, y ≫ kerι A φ h = x) ↔
      ∃ z : up φ Y ⟶ H, z ≫ h = lift (upa φ x) (upt φ Y) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y.left ≫ pullback.snd (h ≫ snd A T).left φ = Y.hom := Over.w y
    have hT : (h ≫ snd A T).left ≫ T.hom = H.hom := Over.w _
    have hc : (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ (h ≫ snd A T).left = Y.hom ≫ φ := by
      rw [← hy]
      exact (Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    refine ⟨Over.homMk (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ?_, ?_⟩
    · show (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ H.hom = Y.hom ≫ φ ≫ T.hom
      rw [← hT, ← Category.assoc, hc, Category.assoc]
    · apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc]
        apply Over.OverMorphism.ext
        have e : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
            = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
        exact (Category.assoc _ _ _).trans
          ((congrArg (y.left ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
      · rw [lift_snd, Category.assoc]
        apply Over.OverMorphism.ext
        exact hc
  · rintro ⟨z, hz⟩
    have h1 : z ≫ h ≫ fst A T = upa φ x := by rw [← Category.assoc, hz, lift_fst]
    have h2 : z ≫ h ≫ snd A T = upt φ Y := by rw [← Category.assoc, hz, lift_snd]
    have h1' : z.left ≫ (h ≫ fst A T).left = x.left ≫ pullback.fst A.hom (φ ≫ T.hom) :=
      congrArg (·.left) h1
    have h2' : z.left ≫ (h ≫ snd A T).left = Y.hom ≫ φ := congrArg (·.left) h2
    let l : Y.left ⟶ pullback (h ≫ snd A T).left φ := pullback.lift z.left Y.hom h2'
    have l1 : l ≫ pullback.fst _ _ = z.left := pullback.lift_fst _ _ _
    have l2 : l ≫ pullback.snd _ _ = Y.hom := pullback.lift_snd _ _ _
    refine ⟨Over.homMk l l2, ?_⟩
    apply Over.OverMorphism.ext
    have e1 : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
        = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
    have e2 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)
        = pullback.snd (h ≫ snd A T).left φ := pullback.lift_snd _ _ _
    have hx : x.left ≫ pullback.snd A.hom (φ ≫ T.hom) = Y.hom := Over.w x
    apply pullback.hom_ext (f := A.hom) (g := φ ≫ T.hom)
    · refine (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e1).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (h ≫ fst A T).left) l1).trans h1')
    · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e2).trans (l2.trans hx.symm))

end GlobalTheory.TwistFlat
