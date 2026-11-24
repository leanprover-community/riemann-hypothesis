module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem pullQuasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsAbelianScheme B → IsQuasiInv k ψ ψ' → IsGrpPullback A₁ A t φ → ∃ (B₁ : Over T) (_ : GrpObj B₁) (_ : IsCommMonObj B₁) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ ∧ IsGrpPullback B₁ B t θ ∧ IsQuasiInv k ψ₁ ψ₁' ∧ φ ≫ ψ.left = ψ₁.left ≫ θ ∧ θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ _ _ φ hB hq hA
  obtain ⟨hψ, hψ', h1, h2⟩ := hq
  obtain ⟨e, he, hφ⟩ := grpPullback_iso hA (isGrpPullback_pullback A t)
  have hinv : IsMonHom e.inv := inferInstance
  have hinvφ : e.inv.left ≫ φ = pullback.fst A.hom t := by
    rw [← hφ, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hmap : ∀ (X M : Over Y) [MonObj M] (f : X ⟶ M) (n : ℕ),
      (Over.pullback t).map (f ^ n) = ((Over.pullback t).map f) ^ n := fun X M _ f n => by
    rw [← Functor.homMonoidHom_apply, map_pow, Functor.homMonoidHom_apply]
  have hid : ∀ (M : Over Y) [GrpObj M], (Over.pullback t).map ((𝟙 M) ^ k) = (𝟙 _) ^ k := fun M _ => by
    rw [hmap, CategoryTheory.Functor.map_id]
  refine ⟨(Over.pullback t).obj B, inferInstance, inferInstance, pullback.fst B.hom t,
    e.hom ≫ (Over.pullback t).map ψ, (Over.pullback t).map ψ' ≫ e.inv,
    ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t B hB, isGrpPullback_pullback B t, ⟨inferInstance, inferInstance, ?_, ?_⟩, ?_, ?_⟩
  · calc (e.hom ≫ (Over.pullback t).map ψ) ≫ (Over.pullback t).map ψ' ≫ e.inv
          = e.hom ≫ (Over.pullback t).map (ψ ≫ ψ') ≫ e.inv := by simp
      _ = e.hom ≫ ((𝟙 ((Over.pullback t).obj A)) ^ k) ≫ e.inv := by rw [h1, hid]
      _ = (𝟙 A₁) ^ k := by
        rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, e.hom_inv_id]
  · calc ((Over.pullback t).map ψ' ≫ e.inv) ≫ e.hom ≫ (Over.pullback t).map ψ
          = (Over.pullback t).map (ψ' ≫ ψ) := by simp
      _ = (𝟙 _) ^ k := by rw [h2, hid]
  · rw [Over.comp_left, Category.assoc]
    show φ ≫ ψ.left = e.hom.left ≫ pullback.lift _ _ _ ≫ pullback.fst B.hom t
    rw [pullback.lift_fst, ← Category.assoc, hφ]
  · rw [Over.comp_left, Category.assoc, hinvφ]
    show pullback.fst B.hom t ≫ ψ'.left = pullback.lift _ _ _ ≫ pullback.fst A.hom t
    rw [pullback.lift_fst]

end GlobalTheory.UPel.HT.ES
