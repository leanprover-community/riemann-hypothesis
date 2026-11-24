module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieJ

noncomputable def epsOver {X : Scheme.{0}} {Ω Ω' : Type} [CommRing Ω] [CommRing Ω'] (x : Sp Ω ⟶ X) (y : Sp Ω' ⟶ X) (i : Ω →+* Ω')
    (h : y = Spec.map (CommRingCat.ofHom i) ≫ x) : epsAt y ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualMap i))) (by
    subst h
    have hr : (dualMap i).comp (algebraMap Ω (DualNumber Ω)) = (algebraMap Ω' (DualNumber Ω')).comp i := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    show Spec.map (CommRingCat.ofHom (dualMap i)) ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ x =
      Spec.map (CommRingCat.ofHom (algebraMap Ω' (DualNumber Ω'))) ≫ Spec.map (CommRingCat.ofHom i) ≫ x
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hr])

theorem isTanAt_epsOver {X : Scheme.{0}} {Ω Ω' : Type} [CommRing Ω] [CommRing Ω'] (G : Over X) [GrpObj G]
    (x : Sp Ω ⟶ X) (y : Sp Ω' ⟶ X) (i : Ω →+* Ω') (h : y = Spec.map (CommRingCat.ofHom i) ≫ x)
    (v : epsAt x ⟶ G) (hv : IsTanAt G x v) : IsTanAt G y (epsOver x y i h ≫ v) := by
  have hr : (TrivSqZeroExt.fstHom Ω' Ω' Ω').toRingHom.comp (dualMap i) = i.comp (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  have hone : (Over.homMk (Spec.map (CommRingCat.ofHom i)) h.symm : Over.mk y ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) = 1 := by
    exact MonObj.comp_one _
  have h1 := congrArg (fun w => w.left) hone
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω' Ω' Ω').toRingHom) ≫ Spec.map (CommRingCat.ofHom (dualMap i)) ≫ v.left = _
  rw [← h1, Over.comp_left, ← hv, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

theorem exists_map : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → ∃ j : V →+ V', ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ φ V V' _ _ _ _ M M' hd hp
  obtain ⟨N, hN⟩ := (LiePull.lieModel_pullback X X' G G' f φ hp Ω' ξ' V').2 M'
  have ex : ∀ e, ∃ t, N.pt t = epsOver ξ (ξ' ≫ f) i hd ≫ M.pt e :=
    fun e => N.onto _ (isTanAt_epsOver G ξ (ξ' ≫ f) i hd _ (M.tan e))
  choose g hg using ex
  refine ⟨AddMonoidHom.mk' g fun a b => N.inj ?_, fun e => ?_⟩
  · rw [N.add, hg, hg, hg, M.add, comp_mul]
  · show (M'.pt (g e)).left ≫ φ = _
    rw [hN, hg]
    rfl

end GlobalTheory.CompanionTheory.Ar.LieJ
