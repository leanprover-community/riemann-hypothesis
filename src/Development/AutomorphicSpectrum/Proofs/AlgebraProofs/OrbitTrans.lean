module

public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

private theorem exists_hom_of_comp_snd_eq_comp_smul {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {M X Y : C} [MonObj M] [ModObj M X] (a b : Y ⟶ M ⊗ X)
    (h : b ≫ SemiCartesianMonoidalCategory.snd M X = a ≫ ModObj.smul (M := M) (X := X)) :
    ∃ r : Y ⟶ M ⊗ X, r ≫ SemiCartesianMonoidalCategory.snd M X = a ≫ SemiCartesianMonoidalCategory.snd M X ∧
      r ≫ ModObj.smul (M := M) (X := X) = b ≫ ModObj.smul (M := M) (X := X) := by
  have key : ∀ c : Y ⟶ M ⊗ X, c ≫ ModObj.smul (M := M) (X := X) =
      (c ≫ SemiCartesianMonoidalCategory.fst M X) • (c ≫ SemiCartesianMonoidalCategory.snd M X) := by
    intro c
    rw [CategoryTheory.Hom.smul_def, CartesianMonoidalCategory.lift_comp_fst_snd]
  refine ⟨CartesianMonoidalCategory.lift
    ((b ≫ SemiCartesianMonoidalCategory.fst M X) * (a ≫ SemiCartesianMonoidalCategory.fst M X))
    (a ≫ SemiCartesianMonoidalCategory.snd M X), CartesianMonoidalCategory.lift_snd _ _, ?_⟩
  rw [← CategoryTheory.Hom.smul_def, mul_smul, ← key a, ← h, ← key b]

theorem orbit_trans {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x y w : X.left) :
    y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x := by
  simp only [GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
  rintro ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (ModObj.smul (M := G) (X := X)).left) (g := (SemiCartesianMonoidalCategory.snd G X).left)
    p q hq.symm
  have e₁ : (SemiCartesianMonoidalCategory.snd G X).left ≫ X.hom = (G ⊗ X).hom := Over.w _
  have e₂ : (ModObj.smul (M := G) (X := X)).left ≫ X.hom = (G ⊗ X).hom := Over.w _
  have hw : pullback.snd (ModObj.smul (M := G) (X := X)).left (SemiCartesianMonoidalCategory.snd G X).left ≫
      (G ⊗ X).hom =
      pullback.fst (ModObj.smul (M := G) (X := X)).left (SemiCartesianMonoidalCategory.snd G X).left ≫
      (G ⊗ X).hom := by
    rw [← e₂, pullback.condition_assoc, e₁, e₂]
  obtain ⟨r, hr₁, hr₂⟩ := exists_hom_of_comp_snd_eq_comp_smul
    (Y := Over.mk (pullback.fst (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left ≫ (G ⊗ X).hom))
    (Over.homMk (pullback.fst (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left) rfl)
    (Over.homMk (pullback.snd (ModObj.smul (M := G) (X := X)).left
      (SemiCartesianMonoidalCategory.snd G X).left) hw)
    (Over.OverMorphism.ext (by
      simp only [Over.comp_left, Over.homMk_left]
      exact pullback.condition.symm))
  refine ⟨r.left z, ?_, ?_⟩
  · have h₁ := congrArg Over.Hom.left hr₁
    simp only [Over.comp_left, Over.homMk_left] at h₁
    rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply, hz₁, hp]
  · have h₂ := congrArg Over.Hom.left hr₂
    simp only [Over.comp_left, Over.homMk_left] at h₂
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, hz₂]

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
