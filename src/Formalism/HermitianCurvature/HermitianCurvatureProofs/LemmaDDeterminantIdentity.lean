module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovariantHatSqOfLin
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmIndep
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmStar
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnAdapted
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovHat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabGl
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnMinorLeft
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRdSkew
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleRight
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnYLeibniz
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylLevelElementProperties
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowExpansionMinor.FirstColumnSplitBijective
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkipSuccessorIndex.SkipSucc2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.PeriodIntegrals.ContractionsCovariantIff

@[expose] public section

theorem Formalism.FourierDecayAlt.P.expansion_first_column : Formalism.FourierDecayAlt.Q.ExpFirstCol := PI.QmColExpWork.expFirstCol

theorem Formalism.FourierDecayAlt.P.expansion_last_column : Formalism.FourierDecayAlt.Q.ExpLastCol := PI.QmColExpWork.expLastCol

theorem Formalism.FourierDecayAlt.P.expansion_first_line : Formalism.FourierDecayAlt.Q.ExpFirstRow := PI.QmRowExpWork.expFirstRow_of quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.expansion_last_line : Formalism.FourierDecayAlt.Q.ExpLastRow := PI.QmRowExpWork.expLastRow_of quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.line_form_of_minor : Formalism.FourierDecayAlt.Q.RowForm := quantum_minor_row_form

theorem Formalism.FourierDecayAlt.P.skip_succ_identity : Formalism.FourierDecayAlt.Q.SkipSucc := PI.QmSkipWork.skipSucc

theorem Formalism.FourierDecayAlt.P.skip_succ_double_identity : Formalism.FourierDecayAlt.Q.SkipSucc2 := PI.QmSkipWork.skipSucc2

theorem Formalism.FourierDecayAlt.P.star_quantum_minor : Formalism.FourierDecayAlt.Q.StarMinor := quantum_minor_star

theorem Formalism.FourierDecayAlt.P.rtt_independence : Formalism.FourierDecayAlt.Q.RTTIndependence := rtt_independence'

theorem Formalism.FourierDecayAlt.P.contractions_covariant : Formalism.FourierDecayAlt.Q.ContractionsCovariant := PI.contractionsCovariant_iff.mpr ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩

theorem Formalism.FourierDecayAlt.P.first_contraction_adapted : Formalism.FourierDecayAlt.Q.ChatAdapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).1

theorem Formalism.FourierDecayAlt.P.second_contraction_adapted : Formalism.FourierDecayAlt.Q.Chat2Adapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).2

theorem Formalism.FourierDecayAlt.P.generator_gl_level : Formalism.FourierDecayAlt.Q.EabGlLev := qnEabGl

theorem Formalism.FourierDecayAlt.P.generator_action_preserved : Formalism.FourierDecayAlt.Q.EabPres := qnEabPres

theorem Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian : Formalism.FourierDecayAlt.Q.QMinorLeftH := quantum_minor_left

theorem Formalism.FourierDecayAlt.P.right_differential_skew : Formalism.FourierDecayAlt.Q.RdSkew := qnRdSkew

theorem Formalism.FourierDecayAlt.P.right_action_rule : Formalism.FourierDecayAlt.Q.RuleRight := qnRuleRight

theorem Formalism.FourierDecayAlt.P.weyl_level_element_properties : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts := weyl_level_element_properties'

theorem Formalism.FourierDecayAlt.P.twisted_leibniz_rule : Formalism.FourierDecayAlt.Q.YLeibniz := qnYLeibniz
