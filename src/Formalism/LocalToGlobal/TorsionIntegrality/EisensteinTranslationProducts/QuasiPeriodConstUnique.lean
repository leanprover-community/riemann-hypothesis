module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HermHalfRight
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OperatorUComm
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SgStar
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
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

namespace Formalism.L2.Th1.F

theorem areaPos : AreaPos := areaPos_thm
theorem etaSplit : EtaSplit := etaSplit_of legendre
theorem altEInt : AltEInt := alternating_form_integral
theorem altEBasis : AltEBasis := alternating_form_basis
theorem semiCharMul : SemiCharMul := semi_character_mul
theorem opUMul : OpUMul := operator_u_mul
theorem opUComm : OpUComm := operator_u_comm
theorem sgStarQuasi : SgStarQuasi := sgStarQuasi_of sigmaQuasi etaSplit
theorem sgStarFixed : SgStarFixed := sgStarFixed_of sgStarQuasi
theorem sigmaTaylorLow :
    ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0 :=
  sigmaTaylorLow_of sigmaEntire sigmaSummable
theorem sgStarBasic : SgStarBasic :=
  sgStarBasic_of sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaTaylorLow
theorem th0Const : ThetaZeroConstant := th0Const_of sgStarBasic
theorem th0Basic : ThetaZeroBasic := th0Basic_of sgStarBasic sgStarQuasi altEInt
theorem th0Class : ThetaZeroClass := th0Class_of sgStarBasic sgStarQuasi
theorem th0LogDeriv : ThetaZeroLogDerivative := th0LogDeriv_of sigmaLogDeriv etaSplit zetaQuasi zetaOdd

end Formalism.L2.Th1.F
