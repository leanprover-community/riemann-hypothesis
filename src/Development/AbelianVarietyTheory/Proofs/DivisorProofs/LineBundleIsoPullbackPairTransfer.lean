module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullIsoCongr

theorem lbIso_pull_congr (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X) (h₁ : Q₁.IsLB) (h₂ : Q₂.IsLB)
    (e : LBIso Q₁ Q₂) (f : LBIso (Q₁.pull m) (Q₁.pull m')) : LBIso (Q₂.pull m) (Q₂.pull m') := by
  have a : LBIso (Q₂.pull m) (Q₁.pull m) :=
    LBIso.chartPull (chartPullPull Q₂ m m rfl) (chartPullPull Q₁ m m rfl) (LBIso.symm e)
  have b : LBIso (Q₁.pull m') (Q₂.pull m') :=
    LBIso.chartPull (chartPullPull Q₁ m' m' rfl) (chartPullPull Q₂ m' m' rfl) e
  exact LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m') (pull_isLB h₂ m')
    (LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m) (pull_isLB h₁ m') a f) b

theorem isocongr : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') :=
  fun X Y Q₁ Q₂ m m' h₁ h₂ e f => lbIso_pull_congr X Y Q₁ Q₂ m m' h₁ h₂ e f

end GlobalTheory.PullIsoCongr
