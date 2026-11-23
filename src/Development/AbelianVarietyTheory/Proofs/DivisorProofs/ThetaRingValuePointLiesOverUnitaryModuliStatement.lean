module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRingValuePointLiesOverUnitaryModuli
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.thetaRing_valuePoint_lies_over_unitaryModuli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ Xo.XF c), GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = y ≫ C.i → ∃ (yK : X₁.S.R →+* FractionRing V₁) (x' : Sp (FractionRing V₁) ⟶ Sp (ratHull X₁.S.R)), (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ x' ≫ spMap (toRat X₁.S.R) = spMap yK ∧ x' ≫ u = y := by
  first | exact @GlobalTheory.GSep.valPt_lies_over_unitary | exact GlobalTheory.GSep.valPt_lies_over_unitary | (intros; apply GlobalTheory.GSep.valPt_lies_over_unitary <;> assumption)
