module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.EvStmt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.EvAdel
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdelicEstimatesHolds
public import Development.WeilBound.ThetaLifts.LeviDeterminants.SchwartzDq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem PositivityTheory.ThKF0.evCone : GlobalTheory.ThK.EvCone := PositivityTheory.ThKF0.evCone_of_adel PositivityTheory.Mix.adelic_estimates_holds

theorem PositivityTheory.ThKF0.evZero_of_adapted (h : PositivityTheory.ThKF0.AdaptedModelEvaluationAtZero) : GlobalTheory.ThK.EvZero :=
  PositivityTheory.ThKF0.evZero_of_adel PositivityTheory.Mix.adelic_estimates_holds PositivityTheory.ThKF0.schwartzDq h
