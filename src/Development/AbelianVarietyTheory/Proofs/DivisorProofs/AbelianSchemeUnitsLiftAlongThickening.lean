module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

theorem isUnit_of_isUnit_appTop_of_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) [Surjective f]
    (a : Γ(Y, ⊤)) (h : IsUnit (f.appTop a)) : IsUnit a := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y _ => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  have hx : x ∈ X.basicOpen (f.appTop a) := by
    rw [Scheme.basicOpen_of_isUnit _ h]; trivial
  rw [← Scheme.preimage_basicOpen_top] at hx
  exact (Y.mem_basicOpen _ _ (by trivial)).1 hx

theorem units_lift_of_thickening : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (T₂ T₀ : Over S) (k : T₀ ⟶ T₂), IsAffine T₂.left → IsClosedImmersion k.left → Surjective k.left →
      Function.Surjective (Units.map (A ◁ k).left.appTop.hom.toMonoidHom) := by
  intro S A _ hA T₂ T₀ k _ _ _ u
  have hb₀ : Function.Bijective (snd A T₀).left.appTop.hom :=
    CubeOpen.bijective_appTop GlobalTheory.globalFns_holds A hA (IsPullback.of_hasPullback A.hom T₀.hom)
  have hk : Function.Surjective k.left.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine k.left).2
  have hc : (A ◁ k).left ≫ (snd A T₂).left = (snd A T₀).left ≫ k.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have hc' : ∀ w, (A ◁ k).left.appTop ((snd A T₂).left.appTop w) =
      (snd A T₀).left.appTop (k.left.appTop w) := by
    intro w
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, hc]
  obtain ⟨v, hv⟩ := hb₀.2 (u : Γ((A ⊗ T₀).left, ⊤))
  obtain ⟨w, rfl⟩ := hk v
  let e := RingEquiv.ofBijective (snd A T₀).left.appTop.hom hb₀
  have hvu : IsUnit (k.left.appTop w) := by
    have : IsUnit (e (k.left.appTop w)) := by
      show IsUnit ((snd A T₀).left.appTop (k.left.appTop w)); rw [hv]; exact u.isUnit
    exact (isUnit_map_iff e _).1 this
  have hw : IsUnit w := isUnit_of_isUnit_appTop_of_surjective k.left w hvu
  obtain ⟨w', hw'⟩ := hw.map (snd A T₂).left.appTop.hom
  refine ⟨w', Units.ext ?_⟩
  show (A ◁ k).left.appTop (w' : Γ((A ⊗ T₂).left, ⊤)) = u
  rw [hw', hc', hv]

end GlobalTheory.DualOpen
