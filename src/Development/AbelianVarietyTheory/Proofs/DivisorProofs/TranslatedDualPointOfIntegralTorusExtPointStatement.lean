module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  first | exact @GlobalTheory.MBLow.trF_dualPoint_of_isPull | exact GlobalTheory.MBLow.trF_dualPoint_of_isPull | (intros; apply GlobalTheory.MBLow.trF_dualPoint_of_isPull <;> assumption)
