module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrationOverCyclesHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamUnifHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePeriodEqFamilyPeriodValueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrationOverCyclesLiftsLieLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PchernOfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodHomPushEndStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsExistAffineZeroSectionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

namespace GlobalTheory.AnPer

theorem gaussManinPeriods_of_span_taylor : PSpan → PTaylor → GlobalTheory.Published.GaussManinPeriods :=
  fun HS HT ↦ gaussManinPeriods_of_parts (-1) GlobalTheory.PeriodFamily.famUnif_holds GlobalTheory.T.periods_exist_affine_zero_section GlobalTheory.T.exists_integrationOverCyclesHom HS
    GlobalTheory.T.integrationOverCycles_lifts_lieLattice GlobalTheory.T.periodHom_push_end' GlobalTheory.T.pChern_neg_one GlobalTheory.T.fibrePeriod_eq_familyPeriod_value HT

end GlobalTheory.AnPer
