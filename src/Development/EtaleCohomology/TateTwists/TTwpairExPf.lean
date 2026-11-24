module

public import Development.EtaleCohomology.TateTwists.EtaleTwistedCupAssocOfTwistedPairingExistsAssoc
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleTateTwistCupPairingExistsAndCupUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
      ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem t_twpair_ex_of (htw : EtaleTateTwistCupPairingExistsAndCupUnique) : t_twpair_ex := by
  intro q _ i j
  exact ⟨twPair q i j, (htw q i j).1⟩

end LateralTheory.EtaleFoundations
