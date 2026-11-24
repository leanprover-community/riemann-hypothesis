module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvalPowerSeriesEqOneOfTwoAxes
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.evalPowerSeries_eq_one_of_two_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ a a' b : Fin d → A, (∀ j, a j ∈ Ideal.span {e}) → (∀ j, a' j ∈ Ideal.span {e}) → (∀ j, IsNilpotent (b j)) → evP ![a, a', b] ph = 1 := by
  first | exact @GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | exact GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | (intros; apply GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes <;> assumption)
