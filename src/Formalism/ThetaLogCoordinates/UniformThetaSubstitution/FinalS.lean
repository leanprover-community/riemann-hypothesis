module

public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ConstantCoeffFirstTwoOfThree
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ConstantCoeffLawFirstTwoOfThree
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.IntegralPderivLgF
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LemmaTwoOf
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormLiftLeOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NotDvdChoosePowMul
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.PartialCoboundaryLinear
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ScalingSwapLemmas
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
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

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem frobExprG : FrobExprG := frobenius_expression_g
theorem valTable : ValTable := valuation_table
theorem expIntegral : ExpIntegral := exp_integral
theorem classChange : ClassChange := classChange_statement
theorem classMul : ClassMul := class_multiplication
theorem classSubst : ClassSubst := class_substitution
theorem classExp : ClassExp := class_exponential
theorem rescaleExact : RescaleExact := RescaleExact_of valTable expIntegral
theorem rescaleCore : RescaleCore := RescaleCore_of rescaleExact classExp classMul

theorem dworkMv : DworkMv := dwork_multivariable
theorem simeqRules : SimeqRules := equivalence_rules
theorem logRescale : LogRescale := log_rescale_alt
theorem logRescaleUnique : LogRescaleUnique := log_rescale_unique
theorem twoSums : TwoSums := two_sums
theorem thmSCore : ThmSCore :=
  ThmSCore_of rescaleCore classSubst classChange classMul twoSums logRescale logRescaleUnique
theorem theorem_s_from_k_one : CyclicPowerClassOfExpEquiv := theorem_s_from_k_one_of thmSCore simeqRules

theorem lawExists : LawExists := formal_law_exists
theorem lawSymm : LawSymm := formal_law_symmetric
theorem divDeriv : DivDeriv := divided_derivative
theorem deIntegral : DeIntegral := DeIntegral_of divDeriv lawSymm
theorem derivA : DerivA := derivative_a
theorem lemmaOne : LemmaOne := LemmaOne_of deIntegral lawSymm
theorem lemmaTwo : LemmaTwo := LemmaTwo_of lemmaOne lawSymm
theorem lamModule : LamModule := LamModule_of dworkMv
theorem zeroCondition : StepZero := StepZero_of lamModule simeqRules lawSymm
theorem firstDeriv : FirstDeriv := FirstDeriv_of lawSymm
theorem cobLin : CobLin := CobLin_of lawSymm
theorem stepI : StepI := StepI_of lemmaOne firstDeriv cobLin
theorem stepII : StepII := StepII_of dworkMv divDeriv deIntegral lawSymm
theorem swapRules : SwapRules := swap_rules
theorem stepH : StepH := StepH_of lemmaTwo swapRules lawSymm
theorem stepIII : StepIII := c_add_sigma_c_eq_zero
theorem stepIV : StepIV := StepIV_of dworkMv
theorem mapSimeq : MapSimeq := mapSimeq_statement
theorem betaIsG : BetaIsG :=
  BetaIsG_of zeroCondition stepI stepII stepH stepIII stepIV swapRules simeqRules

end Formalism.InvariantFactorPaths.G7.Top
