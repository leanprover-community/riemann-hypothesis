module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementP
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementT
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementU
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInVarEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInvTDen
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.NonsingularNorm
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledXEqOffOrigin
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledXOffOrigin
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Series
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

namespace Formalism.L2.Th1.E

theorem nonsingNorm : NonsingNorm := nonsingular_norm
theorem unitKap : UnitKap := UnitKap_of nonsingNorm
theorem unitPsi2 : UnitPsi2 := UnitPsi2_of nonsingNorm
theorem unitDiff : UnitDiff := UnitDiff_of nonsingNorm
theorem intRules : IntRules := integrality_rules
theorem unitAtRules : UnitAtRules := unit_at_rules
theorem rootInt : RootInt := root_integral_alt
theorem gaussMul : GaussMul := gauss_multiplicative
theorem xTShape : XTShape := XTShape_holds
theorem facShape : FacShape := FacShape_of intRules unitAtRules unitKap unitPsi2 unitDiff xTShape
theorem transPower : TransPower := translate_power
theorem parSumTwo : ParSumTwo := parallelogram_sum_two
theorem transUnit : TransUnit := TransUnit_of intRules unitAtRules rootInt facShape transPower
theorem transGauss : TransGauss := TransGauss_of intRules unitAtRules transUnit

theorem prodInt : ProdInt := product_integral
theorem substExpInt : SubstExpInt := subst_exp_integral
theorem congIffSimeq : CongIffSimeq := congruence_iff_simeq
theorem sumEBridge : SumEBridge := sum_series_analytic
theorem mapCob : MapCob := map_coboundary

end Formalism.L2.Th1.E
