module

public import Formalism.TruncatedSeriesCounting.StatementX
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ArcExp
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColAssembly
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColChain
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.FirstSigmaValuationBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.HCoefficientBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.KappaSecondExponentBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGIdeal
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGVal
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.QNumericalIdentity
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RamifiedValuationInequality
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SaturationCriterion
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubGen
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubSmulOneInjective
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncSig
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncationRemainderBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.UnitCoefficientPowerMod
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

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

end Formalism.TruncatedSeriesCounting.WachCoordinates

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

theorem ramified_coefficient_chain_bounds : HCoef ∧ ExpBound ∧ MaxZeroExponentInequality ∧ TwoIntervalValuationSumBound ∧ LemmaGVal ∧ LemmaGIdeal ∧ RamifiedValuationInequality ∧ LenPi0 ∧ ColChain ∧ SubGen ∧ ColAssembly :=
  ⟨h_coefficient_bound, expBound_statement, second_exponent_bound, first_sigma_valuation_bound, g_coeff_valuation_statement, g_ideal_valuation_statement, ramified_valuation_inequality, length_pi_zero_bound, column_chain_bound, submodule_generator_count, column_assembly_bound⟩

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

namespace Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

end Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

namespace Formalism.TruncatedSeriesCounting.R9

end Formalism.TruncatedSeriesCounting.R9

namespace Formalism.TruncatedSeriesCounting.X

theorem pX_conditions : QaNum ∧ TruncSig ∧ TruncRem1 ∧ ArcExp ∧ SatA ∧ UnitCoefficientPowerMod :=
  ⟨q_numerical_identity, truncation_signature_bound, truncation_remainder_bound, arc_exponential_identity, saturation_criterion, unit_coefficient_power_mod⟩

end Formalism.TruncatedSeriesCounting.X
