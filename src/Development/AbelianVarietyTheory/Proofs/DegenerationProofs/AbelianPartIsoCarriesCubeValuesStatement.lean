module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartIsoCarriesCubeValues
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

theorem _root_.GlobalTheory.T.abelianPartIso_carries_cube_values : GlobalFnsSt → AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f => ∀ x y u, (N'.θ (f x) (f y) (f u) : F) * wVal ν ν' w f (x * y) * wVal ν ν' w f (x * u) * wVal ν ν' w f (y * u) * wVal ν ν' w f 1 = (N.θ x y u : F) * wVal ν ν' w f (x * y * u) * wVal ν ν' w f x * wVal ν ν' w f y * wVal ν ν' w f u := by
  first | exact @GlobalTheory.Ex.AbPartCube.theta_move | exact GlobalTheory.Ex.AbPartCube.theta_move | (intros; apply GlobalTheory.Ex.AbPartCube.theta_move <;> assumption)
