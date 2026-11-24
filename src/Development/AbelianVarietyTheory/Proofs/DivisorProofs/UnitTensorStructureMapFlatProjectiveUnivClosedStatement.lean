module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitTensorStructureMapFlatProjectiveUnivClosed
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.unitTensorStructureMap_flat_projective_univClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  first | (exact @GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (exact GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed) | (intros; apply GlobalTheory.HomFixUniv.fA_flat_isProjBy_universallyClosed  <;> assumption)
