module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueValuationRingLift
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_modelPoint_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c),
    (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp βK = κ →
    y ≫ pullback.snd _ _ = spMap βK → ∃ z : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ z = y ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y p κ V K _ _ _ _ _ _ j βK y hκ hj hjκ hy
  have hpr : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hmem : ∀ o : O, (βK.comp β) o ∈ (algebraMap V K).range := by
    intro o
    refine (hj _).1 ?_
    have h1 : j (βK (β o)) = κ (β o) := by rw [← hjκ]; rfl
    simp only [RingHom.comp_apply]
    rw [h1]
    exact (hκ _).2 ⟨o, rfl⟩
  let e : V ≃+* (algebraMap V K).range :=
    RingEquiv.ofBijective (algebraMap V K).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective V K (congrArg Subtype.val h),
        (algebraMap V K).rangeRestrict_surjective⟩
  let b : O →+* V := e.symm.toRingHom.comp ((βK.comp β).codRestrict _ hmem)
  have hb : (algebraMap V K).comp b = βK.comp β := by
    ext o
    have h2 : e (b o) = (βK.comp β).codRestrict _ hmem o := e.apply_symm_apply _
    exact congrArg Subtype.val h2
  have hsq : (y ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom ((algebraMap V K).comp b)) := by
    rw [hb]
    have h3 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
      simp only [Model.j, Category.assoc]
      rw [pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [Category.assoc, h3, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨z, ⟨hz, _⟩, _⟩ := existsUnique_valuationRing_lift O V K b Y.X Y.s (y ≫ Y.j) hsq
  exact ⟨z, hz⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
