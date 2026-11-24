module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.arcData_specialise_at_uniformiser : Laws → Laws2 → DVR.TwistBaseChangeStatement → UnifBaseChangeSt → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (V : Type) [CommRing V] [IsDomain V] [CharZero V] [IsDiscreteValuationRing V] (b : O →+* V) (ϖ : V) (a : Geo.Tor.ArcIn Dm l β V b), Irreducible ϖ → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (ev : PowerSeries V →+* V), (∀ x, ev (PowerSeries.C x) = x) → ev PowerSeries.X = ϖ → ∀ χ : Geo.Tor.Sp (PowerSeries V) ⟶ Y.X, χ ≫ Y.s = Geo.Tor.spMap (PowerSeries.C (R := V)) ≫ Geo.Tor.spMap b → Set.range (jK V ≫ Geo.Tor.spMap ev ≫ χ) ⊆ Set.range Y.j → Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := V)) PowerSeries.X χ → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id V) ϖ (Geo.Tor.spMap ev ≫ χ) := by
  first | exact @GlobalTheory.hasArcData_specialise | exact GlobalTheory.hasArcData_specialise | (intros; apply GlobalTheory.hasArcData_specialise <;> assumption)
