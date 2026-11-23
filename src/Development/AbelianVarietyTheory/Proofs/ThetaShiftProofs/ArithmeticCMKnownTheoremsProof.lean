module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmExistsClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProof
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcClauseClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
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

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem known_holds : Known :=
  have hL := GlobalTheory.firstFiveLaws
  have hh : GlobalTheory.CM.HomExtDvr := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr
  { laws := hL.1
    laws2 := hL.2.1
    ubc := hL.2.2.2.1.unifBaseChange
    laws5 := hL.2.2.2.2
    theta := GlobalTheory.thetaUnifAV_all
    n1ab := GlobalTheory.Moduli.jointExistence_and_moduliScheme.2
    n1c := GlobalTheory.closing_of_abelianSchemeLaws
    n5 := GlobalTheory.arcClause_closed
    models := GlobalTheory.Moduli.jointExistence_and_moduliScheme.1
    hom := hh
    key := GlobalTheory.KeyFam.keyFormula_holds
    cm := GlobalTheory.cmExists_closed
    deg := GlobalTheory.CM.PureDeg.degSt GlobalTheory.cmCurve_closed GlobalTheory.thetaUnifAV_all hL.1 hh
    ev := fun E _ _ _ H Dw l Xo c => (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1 }

end GlobalTheory.ArcCM
