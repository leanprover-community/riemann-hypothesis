module

public import Formalism.LocalToGlobal.AlgebraicTheory.StatementC
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementD
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.DvdOfNormIntCastLt
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtJets
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtPower
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.JetsInOfOneVariable
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.LogDerivativeJetsIntegral
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ScalarConst
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensZEt
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensorFourthPowerScaling
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.UnitKer
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

namespace Formalism.L2.AlgTh

theorem logDerJets : LogDerJets := log_derivative_jets_integral
theorem powLogDer : PowLogDer := power_log_derivative_jets
theorem prodScaleJets : ProdScaleJets := product_scaling_jets
theorem linScale : LinScale := linear_scaling_jets
theorem unitKerInt : UnitKerInt := unit_kernel_integral_coords
theorem etPower : EtPower := etPower_of unitKerInt
theorem etJetsSigma : EtJetsSigma := etJetsSigma_of etPower logDerJets powLogDer
theorem etJetsTh0 : EtJetsTh0 := etJetsTh0_of etJetsSigma
theorem etThetaZ : EtThetaZ := etThetaZ_of etJetsTh0 prodScaleJets
theorem tensZEt : TensZEt := tensor_integral_torsion
theorem etLoc : EtLoc := etLoc_of tensZEt etThetaZ linScale
theorem scalarConst : ScalarConst := scalar_constant_value
theorem xiSwap : XiSwap := xi_swap
theorem xiEt : XiEt := xiEt_of etLoc

end Formalism.L2.AlgTh
