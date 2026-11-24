module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordPairingRetractBaseChange
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordPairingRetract_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (inc : G ⟶ G₀) (v : G₀ ⟶ G₀) (L : LB G₀.left) (L₁ : LB ((Over.pullback f).obj G₀).left) (P : LB (G2 G).left), L.IsLB → L₁.IsLB → P.IsLB → LBIso L₁ (L.pull (pullback.fst G₀.hom f)) → LBIso P ((abelian₂ G₀ L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ v) : G2 G ⟶ G2 G₀).left) → ∃ π₂ : (G2 ((Over.pullback f).obj G)).left ⟶ (G2 G).left, IsSquare (G' := (Over.pullback f).obj G) (G := G) (pullback.fst G.hom f) π₂ ∧ LBIso ((abelian₂ ((Over.pullback f).obj G₀) L₁).pull (lift (fst _ _ ≫ (Over.pullback f).map inc) (snd _ _ ≫ (Over.pullback f).map inc ≫ (Over.pullback f).map v) : G2 ((Over.pullback f).obj G) ⟶ G2 ((Over.pullback f).obj G₀)).left) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.lamRetract_baseChange | exact GlobalTheory.Mum.lamRetract_baseChange | (intros; apply GlobalTheory.Mum.lamRetract_baseChange <;> assumption)
