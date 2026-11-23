module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

namespace GlobalTheory.LBDescent

theorem coboundary_unit_basicOpen : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (V V₀ : Y.Opens)
    (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
    (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ)
    (r : Γ(Y, V₀)) (m s : Γ(X, f ⁻¹ᵁ V₀)) (n : ℕ),
    ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m * (res hle c).val = ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m →
    m * s = (f.app V₀).hom r ^ n →
    ∃ u : Γ(X, f ⁻¹ᵁ Y.basicOpen r)ˣ, ∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ Y.basicOpen r →
      gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u := by
  intro X Y f V V₀ h hle c r m s n hm hs
  have hD : Y.basicOpen r ≤ V₀ := Y.basicOpen_le r
  have hfD : f ⁻¹ᵁ Y.basicOpen r ≤ f ⁻¹ᵁ V₀ := fun x hx => hD hx
  have hB : f ⁻¹ᵁ Y.basicOpen r ≤ X.basicOpen ((f.app V₀).hom r) := (Scheme.preimage_basicOpen f r).le
  have hunitA : IsUnit ((X.presheaf.map (homOfLE hfD).op).hom ((f.app V₀).hom r)) := by
    have h1 : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le ((f.app V₀).hom r))).op).hom ((f.app V₀).hom r)) :=
      RingedSpace.isUnit_res_basicOpen X.toRingedSpace _
    have h2 := h1.map (X.presheaf.map (homOfLE hB).op).hom
    rw [← CommRingCat.comp_apply, ← Functor.map_comp] at h2
    exact h2
  have hunit : IsUnit ((X.presheaf.map (homOfLE hfD).op).hom m) := by
    apply isUnit_of_mul_isUnit_left (y := (X.presheaf.map (homOfLE hfD).op).hom s)
    rw [← map_mul, hs, map_pow]
    exact hunitA.pow n
  refine ⟨hunit.unit, fun z hz => ?_⟩
  have e : f (pullback.snd f f z) = f (pullback.fst f f z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hz1 : pullback.fst f f z ∈ f ⁻¹ᵁ Y.basicOpen r := hz
  have hz2 : pullback.snd f f z ∈ f ⁻¹ᵁ Y.basicOpen r := by
    show f (pullback.snd f f z) ∈ Y.basicOpen r
    rw [e]; exact hz
  have hz0 : z ∈ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ := hD hz
  have hzV : z ∈ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V := hle hz0
  apply Units.ext
  rw [Units.val_mul, gm_val _ z _ hz1, gm_val _ z _ hzV, gm_val _ z _ hz2, IsUnit.unit_spec]
  have k1 : ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen r) z hz1).hom
      (((pullback.fst f f).app (f ⁻¹ᵁ Y.basicOpen r)).hom ((X.presheaf.map (homOfLE hfD).op).hom m)) =
      ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom
        (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m) := by
    have e1 := congrArg (fun q => q.hom m) ((pullback.fst f f).naturality (homOfLE hfD).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    rw [e1]; exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hz0' : z ∈ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀ := h hz0
  have k2 : ((pullback f f).presheaf.germ (pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen r) z hz2).hom
      (((pullback.snd f f).app (f ⁻¹ᵁ Y.basicOpen r)).hom ((X.presheaf.map (homOfLE hfD).op).hom m)) =
      ((pullback f f).presheaf.germ (pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0').hom
        (((pullback.snd f f).app (f ⁻¹ᵁ V₀)).hom m) := by
    have e1 := congrArg (fun q => q.hom m) ((pullback.snd f f).naturality (homOfLE hfD).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    rw [e1]; exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have k4 : ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom
      (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m) =
      ((pullback f f).presheaf.germ (pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0').hom
        (((pullback.snd f f).app (f ⁻¹ᵁ V₀)).hom m) := by
    simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have k3 : ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom ((res hle c).val) =
      ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) z hzV).hom c.val := by
    simp only [res, Units.coe_map, MonoidHom.coe_coe]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hm' := congrArg ((pullback f f).presheaf.germ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) z hz0).hom hm
  rw [map_mul, k3, k4] at hm'
  rw [k1, k2, ← hm']
  congr 1

end GlobalTheory.LBDescent
