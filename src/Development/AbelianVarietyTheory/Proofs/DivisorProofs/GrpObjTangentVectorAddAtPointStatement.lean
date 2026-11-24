module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPoint
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.grpObj_tangentVector_add_at_point : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S) (w : epsPtR x ⟶ G), spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left → ∀ (a b : R') (wa wb : epsPtR x ⟶ G), wa.left = spMap (epsScaleR a) ≫ w.left → wb.left = spMap (epsScaleR b) ≫ w.left → (wa * wb).left = spMap (epsScaleR (a + b)) ≫ w.left := by
  first | (exact @GlobalTheory.GrpTangentPt.tanadd) | (exact GlobalTheory.GrpTangentPt.tanadd) | (intros; apply GlobalTheory.GrpTangentPt.tanadd  <;> assumption)
