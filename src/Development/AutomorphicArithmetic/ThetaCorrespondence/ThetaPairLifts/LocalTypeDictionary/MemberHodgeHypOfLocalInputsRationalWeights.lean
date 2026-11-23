module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConditionOfMemberHypotheses
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalMultiplicityEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSiegelWeilIdentityOfSiegelWeilFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Mem
theorem member_hodgeHyp_of_localInputs_rationalWeights : _root_.GlobalTheory.Mem.LiteralAutomorphy.MemberHypotheses → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → RowRatW → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses :=
  fun m hm dc cw ws sw e1 e2 ud bz so r =>
    _root_.GlobalTheory.Mem.LiteralAutomorphy.condition_of_memberHypotheses dc (_root_.GlobalTheory.twisted_siegel_weil_identity_of_siegel_weil_formula GlobalTheory.Hk3.howeUnram_holds m.m3 m.m4 hm dc cw ws sw e1 e2 ud bz m.m14 so) GlobalTheory.Published.HeckeLPartialContinuation_holds
      (_root_.GlobalTheory.Mem.R3.Rw.MultAt.twisted_local_multiplicity_eq m.m1 m.m2 m.m3 m.m4 m.m5 m.m6 m.m7 m.m12 m.m13 m.m14) r
end GlobalTheory.Mem
end

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
theorem _root_.GlobalTheory.T.compatibleSystem_member_rationalWeights : _root_.GlobalTheory.Mem.LiteralAutomorphy.MemberHypotheses → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitarySchrodinger → GlobalTheory.Published.SiegelEisensteinContinuation → _root_.GlobalTheory.Published.UnusedSlot72 → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SchurOrthogonalitySquareIntegrable → RowRatW → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses :=
  _root_.GlobalTheory.Mem.member_hodgeHyp_of_localInputs_rationalWeights
end
