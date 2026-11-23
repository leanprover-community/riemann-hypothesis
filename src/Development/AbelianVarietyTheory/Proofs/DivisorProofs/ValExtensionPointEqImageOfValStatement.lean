module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValExtensionPointEqImageOfVal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.val_extensionPoint_eq_image_of_val : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  first | exact @GlobalTheory.GSep.Tower.val_om_ext | exact GlobalTheory.GSep.Tower.val_om_ext | (intros; apply GlobalTheory.GSep.Tower.val_om_ext <;> assumption)
