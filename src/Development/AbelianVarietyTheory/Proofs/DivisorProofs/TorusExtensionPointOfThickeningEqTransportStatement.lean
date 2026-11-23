module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointOfThickeningEqTransport
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torusExtensionPoint_of_thickening_eq_transport : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → ∀ (Z : Scheme.{0}) (g : Z ⟶ (thickObj R' I e G').left), ∃ ξ' : GtPt E.toPre (Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)), GlobalTheory.TorusCoord.IsPointOf (U.gt e) g ξ' ∧ IsPullPt hE (𝟙 Z) (Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl)) ξ' := by
  first | exact @GlobalTheory.Mum.isPullPt_of_carries | exact GlobalTheory.Mum.isPullPt_of_carries | (intros; apply GlobalTheory.Mum.isPullPt_of_carries <;> assumption)
