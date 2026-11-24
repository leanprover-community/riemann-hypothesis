module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
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

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem splitPairs_subClosed2 : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed2 (splitPairs R n) := by
  intro R _ n z hz x w hx hw
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hw
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [hf i, hf j, h1 (f i) (f j)]
    simp only [f.eq_iff_eq]
  · obtain ⟨F, hF⟩ := h2
    refine ⟨fun i => F (g i), fun i j => ?_⟩
    rw [hg j, hF]
    simp only [g.eq_iff_eq]
  · intro y hy u hu
    exact h3 y (hx.subset hy) u (hw.subset hu)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.subClosed2_splitPairs : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed2 (splitPairs R n) := by
  first
  | exact @GlobalTheory.SeqCx.splitPairs_subClosed2
end
