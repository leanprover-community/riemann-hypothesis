module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma unit_pullback_left_comp_fst_eq_spMap_comp_unit {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ ≫ η[G].left := by
  simp [Functor.grpObjObj, Functor.monObjObj]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma unit_pullback_left_comp_snd_eq_id {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = 𝟙 _ := by
  have h := Over.w (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G])
  simpa using h


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.semilinear_symm_fixes_unit : ∀ (K W K' : Type) [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K'] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] (e : (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G ≅ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A), IsMonHom e.hom → ∀ (σ : K' ≃ₐ[K] K') (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K' ⟶ pullback G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K') ≫ η[G].left → x ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = 𝟙 _ → x ≫ (e.hom.left ≫ pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫ e.inv.left) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ x := by
  intro K W K' _ _ _ _ _ A _ G _ e he σ x hx₁ hx₂

  have hxη : x = (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left := by
    apply pullback.hom_ext
    · rw [hx₁, unit_pullback_left_comp_fst_eq_spMap_comp_unit]
    · rw [hx₂, unit_pullback_left_comp_snd_eq_id]
      rfl
  have hη : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left ≫ e.hom.left =
      (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') := by
    rw [_root_.GlobalTheory.spMap_comp_spMap]
    congr 1
    ext y
    exact σ.commutes y
  have hinv : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have hmap : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left ≫
      pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _)
        (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [unit_pullback_left_comp_fst_eq_spMap_comp_unit, ← Category.assoc, hσ]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, unit_pullback_left_comp_snd_eq_id]
      simp
  rw [hxη, ← Category.assoc, hη, ← Category.assoc, hmap, Category.assoc, ← hη, Category.assoc,
    hinv, Category.comp_id]

end GlobalTheory
