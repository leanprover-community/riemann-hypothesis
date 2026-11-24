module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

noncomputable section

theorem symmetricGroupCharacter_eq_cf {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho = cf (fun i => lam i + stair m i) (alternantPsum m rho) :=
  rfl

theorem CharacterBound.proof (h1 : CombTableEqWords.Statement) (h2 : CombCfBound.Statement) :
    CharacterBound.Statement := by
  intro m lam rho hlam hrho
  rw [symmetricGroupCharacter_eq_cf]
  refine (h2 m rho hrho lam hlam).trans ?_
  by_cases hs : ∑ i, lam i = rho.sum
  · rw [h1 m lam hlam, hs]
  · rw [latticeWords_eq_empty_of_sum_ne _ _ hs, Finset.card_empty, Nat.cast_zero]
    exact Nat.cast_nonneg _

end

end GroundTheory.Heights₂.Heights.RestTerms
