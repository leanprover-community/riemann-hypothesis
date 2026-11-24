module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionPointsIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.AtVariableArtinHasseEqOneLog
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionHypothesesOfConditions
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionOfExpSpec
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionPointsOfExpSpec
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExponentialSpecification
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FirstMomentIdempotentLaw
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IpNormPowSubPowLe
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstZeroOfConstantCoeff
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.TilInvariantLOf
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.Th1.D

alias expSpec := _root_.Formalism.L2.Th1.D.exponential_specification
alias frobSq := _root_.Formalism.L2.Th1.D.frobenius_square
alias ipLemma := _root_.Formalism.L2.Th1.D.integral_part_lemma
theorem mulSpec : MulSpec := MulSpec_of expSpec ipLemma _root_.Formalism.L2.Th1.D.integral_part_closure
theorem betaHypOfF : BetaHypOfF := BetaHypOfF_of _root_.Formalism.L2.Th1.D.teichmuller_sigma
theorem shiftIP : ShiftIP := ShiftIP_of_frobSq frobSq
alias substTil := _root_.Formalism.L2.Th1.D.subst_tilde
theorem pairRules : PairRules := PairRules_of expSpec ipLemma
theorem torus_sum_coboundary_condition : TorusSumCoboundaryCondition := fourth_condition_of_pairing_rules pairRules substTil shiftIP _root_.Formalism.L2.Th1.D.letter_shift
theorem biextension_hypotheses_of_level_one : MeanBiextensionHypothesesOfCocycle := biextension_hypotheses_of_conditions torus_sum_coboundary_condition _root_.Formalism.L2.Th1.D.torus_tilde _root_.Formalism.L2.Th1.D.teichmuller_sigma _root_.Formalism.L2.Th1.D.second_mean_condition _root_.Formalism.L2.Th1.D.third_mean_condition
theorem tilInvariantL : TilInvariantL := TilInvariantL_of pairRules substTil _root_.Formalism.L2.Th1.D.torus_tilde _root_.Formalism.L2.Th1.D.teichmuller_sigma shiftIP _root_.Formalism.L2.Th1.D.integral_part_closure _root_.Formalism.L2.Th1.D.dual_expansion frobSq
theorem meanSimeqL : MeanSimeqL := MeanSimeqL_of tilInvariantL
theorem beTilXY : BeTilXY := BeTilXY_of expSpec
theorem bMinus1 : BMinus1 := BMinus1_of' expSpec
theorem meanSimeq : MeanSimeq := MeanSimeq_of' meanSimeqL beTilXY _root_.Formalism.L2.Th1.D.letter_shift
theorem biextension_points_integral : BiextensionPointsIntegral := biextension_points_of_exp_spec expSpec meanSimeqL
theorem b0 : B0 := biextension_of_exp_spec expSpec biextension_points_integral
theorem oneLetterHalf : OneLetterHalf := OneLetterHalf_of meanSimeqL

end Formalism.L2.Th1.D
