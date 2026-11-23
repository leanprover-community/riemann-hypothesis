module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ConservationOfNumber.proof (h1 : IntNumAssoc.Statement.{u})
    (h2 : SpecialCycleEval.Statement.{u}) (h3 : SpecialPieceRank.Statement.{u})
    (h4 : GenericPieceRank.Statement.{u}) (h5 : SpecialIdealMultiHomog.Statement.{u})
    (h6 : SpecialDimBound.Statement.{u}) : ConservationOfNumber.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a

  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have htors : ∀ x, C ϖ * x ∈ P → x ∈ P := fun x hx =>
    (hPprime.mem_or_mem hx).resolve_left hϖP
  have hhom : IsMultiHomogIdeal P := hP.multiProj.multiHomog

  have hhilb : hilbFn (genFib P) = hilbFn (specialIdeal P) := by
    funext m
    unfold hilbFn
    split_ifs
    · rw [h4 O K ι P hhom, h3 O ϖ hϖ K ι P hhom htors]
    · rfl
  have hg : gNum P a = intNum (IsLocalRing.ResidueField O) (specialIdeal P) a := by
    unfold gNum intNum
    rw [hhilb]
  rw [hg, h1 (IsLocalRing.ResidueField O) K ι d (specialIdeal P) (h5 O K ι P hhom)
    (h6 O ϖ hϖ K ι P d hP) a]
  exact h2 O ϖ hϖ K ι P (fun V => intNum (IsLocalRing.ResidueField O) V a)

end GroundTheory.Heights₂.Heights.NumbersDVR
