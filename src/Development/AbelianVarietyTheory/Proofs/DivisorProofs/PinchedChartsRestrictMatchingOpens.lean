module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem restrict_pinched : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  intro g S S' Z B' C Y s' z b' e i q h₁ h₂ V' V hV
  refine ⟨(Y.isoOfEq hV).hom ≫ (q ∣_ V), ?_, ?_, ?_⟩
  · have hq : ((Y.isoOfEq hV).hom ≫ (q ∣_ V)) ≫ V.ι ≫ e = (i ⁻¹ᵁ V').ι ≫ q ≫ e := by
      simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc]
    rw [hq, Category.assoc]
    exact (isPullback_morphismRestrict i V').paste_vert h₁
  · have P := (isPullback_morphismRestrict q V).paste_vert h₂
    refine IsPullback.of_iso P (Y.isoOfEq hV).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_inv_ι_assoc]
    · simp
    · simp
  · intro x hx
    obtain ⟨U, U', W₀, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := hx
    refine ⟨U, U', W₀, u, p, j ≫ V'.ι, n, k ≫ V.ι, hu, by simpa using hp, inferInstance, ?_, by simpa using hn, ?_⟩
    · obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    · intro T a a' haa
      obtain ⟨y, hy₁, hy₂⟩ := hl T a a' haa
      refine ⟨y ≫ (i ⁻¹ᵁ V').ι, ?_, ?_⟩
      · rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy₁, Category.assoc]
      · have hq : (Y.isoOfEq hV).hom ≫ (q ∣_ V) ≫ V.ι = (i ⁻¹ᵁ V').ι ≫ q := by
          simp [morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
        rw [Category.assoc, ← hq, reassoc_of% hy₂]

end GlobalTheory.Pinch
