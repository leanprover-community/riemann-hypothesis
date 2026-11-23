module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeries
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

theorem _root_.GlobalTheory.T.thetaPoints_coords_relabelled_twistedData_series : GlobalTheory.UT.LL → BrGtSt → TXSt → EVSt → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (I : FullI o) (N N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (k : ℕ) (β : N.Form k) (u : Cˣ) (r : ℕ → Cˣ) (J : NumD.Iso (N.twist β u) N') (q : ∀ j : ℕ, D.La → N.QT j), (∀ j, 0 < j → ∀ x, ∃ (q' : N'.QT j) (p' : QkPt M.P.D.toPre C j) (z : TFK (R := M.W) C ⟶ M.P.A.A), TwJ β u (r j) J (q j x) q' ∧ ν'.QPt p' q' ∧ z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j p' z) → ∀ m, Odd m → ∀ p : D.La → (N.twist β u).QT (m ^ 2), (∀ x, TwRel β u (r (m ^ 2)) (q _ x) (p x)) → (withI o I).Theta m (fun x => (N.twist β u).tx m (p x)) ∧ ∀ j, 0 < j → ∀ z (p₀ : (N.twist β u).QT j), TwRel β u (r j) (q j z) p₀ → (withI o I).Coord m (I.ev j z) fun x => (N.twist β u).ev m (p x) p₀.1.2 := by
  first | exact @GlobalTheory.RelabelCoords.theta_coord | exact GlobalTheory.RelabelCoords.theta_coord | (intros; apply GlobalTheory.RelabelCoords.theta_coord <;> assumption)
