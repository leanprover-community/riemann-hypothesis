module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularCharts
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) → ∃ (G : Over S) (_ : GrpObj G) (e : A.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback A G j e ∧ ∀ (x : S) (C : Chart j A x), ∃ π : C.G.left ⟶ G.left, IsGrpPullback C.G G C.ξ π ∧ C.α ≫ e = pullback.fst C.G.hom (jK C.R) ≫ π := by
  first | exact @GlobalTheory.Desc.descent_semiAbelian | exact GlobalTheory.Desc.descent_semiAbelian | (intros; apply GlobalTheory.Desc.descent_semiAbelian <;> assumption)
