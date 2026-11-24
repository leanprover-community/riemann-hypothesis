module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementB
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementF
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CompEqZeroOfNotDle
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Discharge
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInv
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatticeBasisPolynomial
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.PolLeISupIsoW
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.SchurTraceOfHomInv
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.TypeInt
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeylInt
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.ZpClosedToAddSubgroup
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.InvariantFactorPaths.PW.Top

theorem weylInt : WeylInt := weyl_integral_holds
theorem weylP : WeylP := weylP_of weylInt lattice_basis_polynomial

private theorem intP_statement : IntP := by
  have hInv : InvInv := invariant_inverse_holds
  exact intP_of (typeInt_of invariant_natural_holds (homInv_of hInv) (schurTrace_of hInv)) lattice_basis_polynomial

theorem extP : ExtP := extP_of intP_statement
theorem dischargeW : DischargeW := dischargeW_of weylP
theorem dischargeE : DischargeE := dischargeE_of extP

end Formalism.InvariantFactorPaths.PW.Top
