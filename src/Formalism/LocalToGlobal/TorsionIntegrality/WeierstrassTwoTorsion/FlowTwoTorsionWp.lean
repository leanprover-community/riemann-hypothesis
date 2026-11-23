module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementG
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementP
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementT
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementZ
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CompInv
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ConstCurveDL
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveL
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveSer
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.EqWSerSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowBasic
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowTrans
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowTwo
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalGroupEqWSeries
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.LogExp
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ToLTDenMulInv
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

universe u v

namespace Formalism.L2.Th1.A

theorem compInvSpec : CompInvSpec.{u} := composition_inverse_spec
theorem compInvMap : CompInvMap.{u, v} := composition_inverse_map
theorem integSpec : IntegSpec.{u} := integration_spec

theorem flowNegUW : FlowNegUW.{u} := chartFlowNegation
theorem chordRegular : ChordRegular.{u} := chordFormula
theorem flowLogDeriv : FlowLogDeriv.{u} := flowLogDerivative
theorem flowTwoTorsion : FlowTwoTorsion.{u} := twoTorsionTranslation
theorem flowTwoTorsionWp : FlowTwoTorsionWp.{u} := twoTorsionTranslationWeierstrassForm

theorem wSerSpec : WSerSpec.{u} := w_series_spec
theorem wSerFactor : WSerFactor.{u} := w_series_factorization
theorem unitSpec : UnitSpec.{u} := invariant_differential_units
theorem seriesMap : SeriesMap.{u, v} := series_map
theorem flowU : FlowU.{u} := unit_flow
theorem dLSpec : DLSpec.{u} := invariant_derivation_spec
theorem flowL : FlowL.{u} := invariant_flow
theorem iSerSpec : ISerSpec.{u} := iSerSpec_of wSerSpec wSerFactor unitSpec flowU flowNegUW

theorem logSpec : LogSpec.{u} := logSpec_of integSpec unitSpec
theorem expSpec : ExpSpec.{u} := expSpec_of integSpec compInvSpec unitSpec
theorem chainZ : ChainZ.{u} := chainZ_of integSpec compInvSpec unitSpec
theorem logNeg : LogNeg.{u} := logNeg_of integSpec compInvSpec unitSpec iSerSpec
theorem flowZ : FlowZ.{u} := flowZ_of expSpec chainZ
theorem wpODE : WpODE.{u} := wpODE_of expSpec chainZ

theorem fglMap : FglMap.{u, v} := formal_group_map
theorem fglChord : FglChord.{u} := formal_group_chord
theorem fglSum : FglSum.{u} := formal_group_sum

theorem tSpec : TSpec.{u} := tSpec_of iSerSpec
theorem plusChord : PlusChord.{u} := plusChord_of flowL
theorem plusFlow : PlusFlow.{u} := plusFlow_of dLSpec flowL
theorem plusMap : PlusMap.{u, v} := addition_map

end Formalism.L2.Th1.A
