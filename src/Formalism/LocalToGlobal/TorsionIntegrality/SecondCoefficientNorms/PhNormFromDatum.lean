module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversal
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.JetExpShape
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormClosed
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Closure
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntPSDerivativeOfLG
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntegralEndomorphismFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
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

namespace Formalism.L2.Th1.C

theorem ptClosure : PtClosure := integralPointClosure'
theorem adjFromNorm : AdjFromNorm := adjoint_from_norm_form
theorem normAdjAll : NormAdjAll := norm_adjoint_all_places
theorem unitaryInv : UnitaryInv := unitary_inverse_identity
theorem hyperbolicSum : HyperbolicSum := hyperbolic_sum_identity

theorem endIntClosed : EndIntClosed := integralEndoClosed'
theorem binomClosed : BinomClosed := binomialScalarClosed'
theorem phNormClosed : PhNormClosed := logNormClosed'
theorem zLinClosed : ZLinClosed := scalarLinearClosed'
theorem zLinInt : ZLinInt := scalarLinearInt'
theorem endoAll : EndoAll := endoAll_of normAdjAll

theorem jetAdditive : JetAdditive := jetAdditivity
theorem jetOne : JetOne := jetOne'
theorem jetAdj : JetAdj := jetAdjoint'

theorem endIntFromDatum : EndIntFromDatum := integral_endomorphism_from_datum
theorem phNormFromDatum : PhNormFromDatum := phi_norm_from_datum
theorem endoAllFromData : EndoAllFromData := endoAllFromData_of endoAll

end Formalism.L2.Th1.C
