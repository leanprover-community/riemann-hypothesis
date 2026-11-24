module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompareOffOwnAtRunsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRunsAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtremalVectorsSplitPartStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoStOfPageStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MaxStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoPathStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankAtPlacesRecStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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



section
set_option autoImplicit false
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn
theorem ontoX_of_twist_shares_exp_alt : _root_.GlobalTheory.BigOn.ExportedStatement → _root_.GlobalTheory.BigOn.TwistStatement' → _root_.GlobalTheory.BigOn.ShareStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement → _root_.GlobalTheory.BigOn.ExponentStatement → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro _ hT hS hB hE
  have hP : _root_.GlobalTheory.BigOn.PageStatement := _root_.GlobalTheory.T.page_estimate_statement'
  have hG : _root_.GlobalTheory.BigOn.GeometricStatement' := _root_.GlobalTheory.T.geoSt_of_pageSt' hP
  exact _root_.GlobalTheory.T.onto_x_of_all_estimates _root_.GlobalTheory.T.runs_estimate_statement' _root_.GlobalTheory.T.rational_estimate_statement' hG (_root_.GlobalTheory.T.rank_at_twisted_places_of_max_geo _root_.GlobalTheory.T.maximum_estimate_statement' hG _root_.GlobalTheory.T.bigOn_comparison_at_twisted_places) hT hS hB hE hP
end GlobalTheory.BigOn
end
