module

public import ReciprocityTheory.DualLattices.EmbeddingSeparatingGroupStatement
public import ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatement
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.EigenLengthProductStatementHolds
public import ReciprocityTheory.DualLattices.EigenLiftsFrobenius
public import ReciprocityTheory.DualLattices.ElementaryDivisorStatement
public import ReciprocityTheory.DualLattices.EmbeddingSeparatingGroup
public import ReciprocityTheory.DualLattices.EqZeroOfIsoZero
public import ReciprocityTheory.DualLattices.FrobeniusBlock
public import ReciprocityTheory.DualLattices.LenEx
import ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatementHolds
public import ReciprocityTheory.DualLattices.MatEquivApply
public import ReciprocityTheory.DualLattices.MonomialsSpanOfProdEq
public import ReciprocityTheory.DualLattices.RankEqRankOfPermAndZero
public import ReciprocityTheory.DualLattices.SumX
import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthOfLengthEigenLengthProduct

@[expose] public section

namespace ReciprocityTheory.PGsh.Up

theorem frobenius_of_length_lifts (hLen : LenIdStatement) (hEx : LenExStatement) (hTot : EigenLengthProductStatement)
    (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_length_eigenLengthProduct hLen hEx hTot (core_of (lifts_of hG hE hR) hB hF)

theorem unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement)
    (hR : EigenRankStatement) (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement :=
  frobenius_of_length_lifts lenId lenEx eigenLengthProductStatement_holds hG hE hR hB hF

theorem frobenius_of_group_divisors_rank (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hF1 : LiftMonomialDeterminantStatement) (hF2 : FrobeniusBlockStatement) (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_eigen_elementaryDivisor_rank_lifts hG hE hR monomials_span_of_prod_eq (frob_of hF1 hF2 hF3)

theorem unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound (hG : EmbeddingSeparatingGroupStatement) (hF1 : LiftMonomialDeterminantStatement) (hF2 : FrobeniusBlockStatement)
    (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  frobenius_of_group_divisors_rank hG elementary_divisor_statement rank_eq_rank_of_perm_and_zero hF1 hF2 hF3

theorem unramifiedCokernelLength_of_frobeniusLengthBound (hG : EmbeddingSeparatingGroupStatement) (hF3 : FrobeniusLengthBoundStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_monomialDeterminant_frobeniusBlock_lengthBound hG liftMonomialDeterminantStatement_holds frobeniusBlock hF3

theorem frobenius_of_group (hG : EmbeddingSeparatingGroupStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_frobeniusLengthBound hG u7F3

theorem u7 : UnramifiedCokernelLengthStatement :=
  frobenius_of_group embeddingSeparatingGroup

end ReciprocityTheory.PGsh.Up
