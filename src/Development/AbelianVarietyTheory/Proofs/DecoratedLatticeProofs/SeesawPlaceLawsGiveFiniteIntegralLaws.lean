module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLiftsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocallyFiniteOfTupleConditionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteIntegralsDoubleStepValueStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutesStatement
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem placeLaws_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c)
    (w : ∀ s, VTup (t s)), c.Is → c.VolLast → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) →
    (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v 𝒯 t w hc hvl hv ht hp
  refine ⟨fun s => ?_, ?_, ?_⟩
  · exact GlobalTheory.T.locally_finite_of_tuple_conditions D c v (t s) (w s) hc hv (ht s) (hp s).form (hp s).off (hp s).gs (hp s).qfin
  · exact GlobalTheory.T.seeSaw_finiteIntegrals_doubleStep_value D c v 𝒯 t w hc hv ht hp (GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D) (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.seeSawWeilBiAction_commutes D)
  · exact GlobalTheory.T.seeSawLastTwoSteps_doubleLiftPeriod_value D c v 𝒯 t w hc hvl hv ht hp (GlobalTheory.Unf.LastSteps.lastLaw D) (GlobalTheory.T.lastSeeSaw_thetaIdentity D)
      (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.seeSawWeilBiAction_commutes D)

end GlobalTheory.SeeSaw
