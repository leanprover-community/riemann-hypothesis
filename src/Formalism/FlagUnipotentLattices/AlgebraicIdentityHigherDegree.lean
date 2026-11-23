module

public import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CircleIntegralInvSubEqZeroOfOutside
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment
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

@[expose] public section

namespace Formalism.HermitianLatticeCounting.Final.ExpansionTerms

theorem integral_norm_estimate : Formalism.HermitianLatticeCounting.ExpansionTerms.AlgebraicIntegerNormGeOne := Formalism.HermitianLatticeCounting.P.integral_norm_estimate_holds
theorem component_total_sixty_four : Formalism.HermitianLatticeCounting.ExpansionTerms.BlockMinorSumPowSixtyFour := Formalism.HermitianLatticeCounting.P.block_minor_sum_pow_sixty_four
theorem integral_norm_application : Formalism.HermitianLatticeCounting.ExpansionTerms.NormGeOneMaxBound := Formalism.HermitianLatticeCounting.P.integral_norm_application_holds

theorem leadingMinorUnipotentInvariant : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorUnipotentInvariant := Formalism.HermitianLatticeCounting.P.invariant_value_holds
theorem e4aVanish : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorVanishesOffBlockEnds := Formalism.HermitianLatticeCounting.P.leading_minor_vanishes_off_block_ends
theorem e4aValue : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorAtBlockEnd := Formalism.HermitianLatticeCounting.P.leading_minor_at_block_end
theorem integral_evaluation_fourth : Formalism.HermitianLatticeCounting.ExpansionTerms.OrbitIntegralEntries := Formalism.HermitianLatticeCounting.P.orbit_integral_entries

theorem degStepBound : Formalism.HermitianLatticeCounting.ExpansionTerms.DegStepBound := Formalism.HermitianLatticeCounting.P.degree_increment_bound
theorem sup_l2_ratio_majorant : Formalism.HermitianLatticeCounting.ExpansionTerms.supL2RatioMajorant := Formalism.HermitianLatticeCounting.P.first_operator_norm_bound

end Formalism.HermitianLatticeCounting.Final.ExpansionTerms
