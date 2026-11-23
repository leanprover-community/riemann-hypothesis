module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementN
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSys
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.GeneralIntegrality
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.OpUTh0RootOf
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Taylor0ConstMul
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

theorem generalIntOf : GeneralIntOf := general_integrality
theorem torsionIntegral : TorsionIntegral := torsion_integral
theorem ptOfZero : PtOfZero := PtOfZero_of
theorem wpBridge : WpBridge := AnaSys.wpBridge
theorem transWpBridge : TransWpBridge := AnaSys.transWpBridge
theorem analyticSys : AnalyticSys := AnalyticSys_of transWpBridge
theorem opUTh0Root : OpUTh0Root := OpUTh0Root_of

theorem ptOfInt_of_add (hA : PtOfAdd) : PtOfInt := PtOfInt_of hA ptOfZero torsionIntegral
theorem kernelPtInt_of_add (hA : PtOfAdd) : KernelPtInt := KernelPtInt_of (ptOfInt_of_add hA)
theorem cm4Int_of_add (hA : PtOfAdd) : CMIntegrality := cm_integrality_of_torsion_points (ptOfInt_of_add hA)
theorem analyticTrans_of_add (hA : PtOfAdd) : AnalyticTrans :=
  AnalyticTrans_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit
theorem th0Analytic_of_add (hA : PtOfAdd) : ThetaZeroAnalytic :=
  Th0Analytic_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit transGauss opUTh0Root

theorem ptOfAdd : PtOfAdd := PtOfAdd_of
theorem ptOfInt : PtOfInt := ptOfInt_of_add ptOfAdd
theorem kernelPtInt : KernelPtInt := kernelPtInt_of_add ptOfAdd
theorem cm4Int : CMIntegrality := cm4Int_of_add ptOfAdd
theorem analyticTrans : AnalyticTrans := analyticTrans_of_add ptOfAdd
theorem th0Analytic : ThetaZeroAnalytic := th0Analytic_of_add ptOfAdd

end Formalism.L2.Th1.E
