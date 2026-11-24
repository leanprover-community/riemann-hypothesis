module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepOfUniversalAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_homFixRep_iso_of_universal : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X), (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) → ∃ (R : HomFixRep A B L M) (e : R.H ≅ X), e.hom ≫ u.t = R.π := by
  first | exact @GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal | exact GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal | (intros; apply GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal; all_goals assumption)
