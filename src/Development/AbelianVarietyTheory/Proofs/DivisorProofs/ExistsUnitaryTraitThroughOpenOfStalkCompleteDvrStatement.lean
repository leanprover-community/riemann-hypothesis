module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughOpenOfStalkCompleteDvr
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_unitaryTrait_through_open_of_stalk_complete_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (x : Y.Z) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], IsAdicComplete (maximalIdeal A) A → ∀ θ : Y.Z.presheaf.stalk x →+* A, Function.Injective θ → IsLocalHom θ → ∃ (T : UTrait Xo c) (f : A →+* T.V), Function.Injective f ∧ IsLocalHom f ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ T.y ≫ C.i = jK T.V ≫ (spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π := by
  first | exact @GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr | exact GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr | (intros; apply GlobalTheory.UPoinc.exists_uTrait_through_open_of_stalk_dvr <;> assumption)
