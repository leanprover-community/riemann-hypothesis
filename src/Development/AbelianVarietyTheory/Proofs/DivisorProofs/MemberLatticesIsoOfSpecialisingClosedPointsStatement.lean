module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberLatticesIsoOfSpecialisingClosedPoints
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [IsDiscreteValuationRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (X₀ : Type) [AddCommGroup X₀] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ X₀) (𝔫₁ : UMem X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁) (ξ₁ : Sp V₁ ⟶ Y.Z) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] [IsDiscreteValuationRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (X : Type) [AddCommGroup X] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ X) (𝔫₂ : UMem X₁ z₁ act V₂ ev₂ X t₂ δ₂) (ξ₂ : Sp V₂ ⟶ Y.Z), ξ₁ ≫ πY = spMap ev₁ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₂ ≫ πY = spMap ev₂ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → Cmp.LatTo 𝔫₁ 𝔫₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes | exact GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes | (intros; apply GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes <;> assumption)
