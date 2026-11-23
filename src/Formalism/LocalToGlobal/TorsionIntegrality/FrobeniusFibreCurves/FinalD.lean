module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementD
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffLawWithInverseThree
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FirstLevelOfThreeVarParallelogram
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.RealAdelicInertTransportTypeFormsEqAlt
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Wp3ApplyEqSqMulSubSqMul
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.XTwoDvdOfRestrictThirdZero
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
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementF

@[expose] public section

namespace Formalism.L2.Th1.B

open Formalism.L2.Th1.A (bridgeWp bridgeLaw bridgeCurve bridgeCurve3)

theorem shearLemma : ShearLemma := Wr.shearedWronskianUniqueness
theorem tauRule : TauRule := Det.tau_derivative_rule_holds
theorem detRule : DetRule := Det.determinant_derivative_rule_holds
theorem frobStickLog : FrobStickLog := Fs.FrobStickLog_of shearLemma tauRule detRule
theorem frobStick : FrobStick := Fs.FrobStick_of frobStickLog
theorem frobStickStar : FrobStickStar := Fs.FrobStickStar_of frobStick
theorem fIUnit : FIUnit := E2.formal_inverse_unit_holds
theorem parThree : ParThree := E2.ParThree_of frobStickStar fIUnit
theorem cubeFromPars : CubeFromPars := E3.cube_relation_from_parallelograms
theorem first_level_all_formal_groups : LogSigmaPullbackCocycleJets := E3.log_sigma_pullback_cocycle_jets_of_parallelogram_and_cube parThree cubeFromPars

end Formalism.L2.Th1.B
