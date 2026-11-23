module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementA
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementB
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementD
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementF
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CommProjectionHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Discharge
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInv
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatticeBasisPolynomial
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.OrthogonalIsomorphismHolds
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.PolLeISupIsoW
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.SchurTraceOfHomInv
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.TypeInt
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.InvariantFactorPaths.PW.Top

theorem invInv : InvInv := invariant_inverse_holds
theorem invNat : InvNat := invariant_natural_holds
theorem homInv : HomInv := homInv_of invInv
theorem schurTrace : SchurTrace := schurTrace_of invInv
theorem typeInt : TypeInt := typeInt_of invNat homInv schurTrace
theorem divInt : DivInt := divided_integral_holds
theorem latBasisPol : LatBasisPol := lattice_basis_polynomial
theorem projP : ProjP := projection_lattice_holds
theorem commP : CommP := comm_projection_holds
theorem intP : IntP := intP_of typeInt latBasisPol
theorem dischargeP : DischargeP := dischargeP_of projP commP intP

end Formalism.InvariantFactorPaths.PW.Top
