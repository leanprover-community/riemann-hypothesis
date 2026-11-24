module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSig1S
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.EvalSecondZeroAtVariableZero
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PderivZeroZeroWeierstrassDifference
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassReducedEquations
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

namespace Formalism.L2.Th1.B

theorem expLogRules : ExpLogRules := by
  intro K _ _ ι
  exact ⟨fun f g hf hg => fExp_add hf hg, fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩,
    fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩
theorem expLogDeriv : ExpLogDeriv := by
  intro K _ _ ι _ i
  exact ⟨fun f hf => pd_fExp i hf, fun g hg => mul_pd_fLog i hg⟩
theorem expLogSubst : ExpLogSubst := by
  intro K _ _ ι κ _ φ hφ
  exact ⟨fun f hf => subst_fExp hφ hf, fun g hg => subst_fLog hφ hg⟩
theorem primRules : PrimRules := by
  intro K _ _ f
  exact ⟨dz_prim f, constantCoeff_prim f⟩
theorem addSigmaLog : AddSigmaLog :=
  AddSigmaLog_of expLogDeriv expLogSubst primRules _root_.Formalism.L2.Th1.B.wave_equation_unique _root_.Formalism.L2.Th1.B.wave_operator_kills _root_.Formalism.L2.Th1.B.parallelogram_cauchy_equation _root_.Formalism.L2.Th1.B.weierstrassReducedEquations _root_.Formalism.L2.Th1.B.difference_quotient_rule_holds
theorem addSigma : AddSigma := AddSigma_of addSigmaLog expLogRules expLogSubst _root_.Formalism.L2.Th1.B.difference_quotient_rule_holds
theorem addSgStar : AddSgStar := AddSgStar_of addSigma expLogRules expLogSubst
end Formalism.L2.Th1.B
