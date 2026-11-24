module

public import Formalism.PeriodIntegrals.JetsPhW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ChainSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.FirstJetIntegralGeneralHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.GlueHoldsVar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.HighGOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.InvOmega
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.SecondJetIntegralGeneralHolds
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

theorem jets_high_generation : PI.JetsPhW.HighG :=
  PI.JetsPhW.W.highG_of PI.JetsPhW.W.derivative_chain_rule PI.JetsPhW.W.derivative_self
    PI.JetsPhW.W.pderiv_subst_ne PI.JetsPhW.W.pderiv_subst_self PI.JetsPhW.W.evaluation_at_zero
    PI.JetsPhW.W.jet_derivative_integrality PI.JetsPhW.W.log_derivative_integral_jet_integrality PI.JetsPhW.W.derivative_integral

theorem jets_phase_weights : PI.JetsPhW.Target :=
  PI.JetsPhW.W.glue_holds_var PI.JetsPhW.Inv.inverse_omega_holds jets_high_generation
    PI.JetsPhW.Low.firstJetIntegralGeneral_holds PI.JetsPhW.Low.secondJetIntegralGeneral_holds

theorem jets_high : PI.JetsPhW.High :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).1

theorem jets_one : PI.JetsPhW.One :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.1

theorem jets_two : PI.JetsPhW.Two :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.2
