module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIsoTranslatedBundleLevelComparison
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_global_iso_translated_bundle_levelComparison : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (hwL : wL.IsGen) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left),
    ∃ W : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0)), W.IsGen ∧
      ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D₂.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U₂.LG.L.ι),
        (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U jM → (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U jM' →
        ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U jL' →
        Geo.Tor.gw W (r ≫ (U₂.gt e).pG.left) z jM jM' * Geo.Tor.gw (U₂.w e) r z jM' (fun _ => jL') =
          Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z jL jL' := by
  first | exact @GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global | exact GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global | (intros; apply GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global <;> assumption)
