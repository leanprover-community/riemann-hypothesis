module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightSquareLengthLtStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegmentWords

theorem wt_inSh_antisymm : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L →
    AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) →
    InSh s (L : Multiset (ASeg T)) (wt s M) →
    (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by
  intro T s hs hj L M hL hM hLM hML
  by_contra hne
  have h1 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj L (M : Multiset (ASeg T)) hL hLM (Ne.symm hne)
  have h2 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj M (L : Multiset (ASeg T)) hM hML hne
  exact lt_asymm h1 h2

end GlobalTheory.CompanionTheory.SegmentWords
