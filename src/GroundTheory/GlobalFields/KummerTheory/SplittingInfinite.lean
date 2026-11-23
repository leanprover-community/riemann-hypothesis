module

public import GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
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
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GroundTheory.Global

open NumberField Module
open scoped NumberField.LiesOver TensorProduct

namespace InfinitePlace

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

def SplitsCompletely (v : NumberField.InfinitePlace K) : Prop :=
  ∀ w : NumberField.InfinitePlace L, w.LiesOver v → w.IsUnramified K

variable {L} (v : NumberField.InfinitePlace K)

theorem isUnramified_iff_finrank_eq_one (w : NumberField.InfinitePlace L) [w.LiesOver v] :
    w.IsUnramified K ↔ finrank v.Completion w.Completion = 1 := by
  refine ⟨fun h ↦ h.finrank_eq_one v, fun h ↦ ?_⟩
  rcases w.isUnramified_or_isRamified K with hu | hr
  · exact hu
  · exact absurd (h.symm.trans (hr.finrank_eq_two v)) (by norm_num)

theorem splitsCompletely_iff_forall_finrank :
    SplitsCompletely L v ↔
      ∀ w : v.placesOver L, finrank v.Completion (w : NumberField.InfinitePlace L).Completion = 1 :=
  ⟨fun h w ↦ (isUnramified_iff_finrank_eq_one v w.1).1 (h w.1 w.2),
    fun h w hw ↦ have := hw; (isUnramified_iff_finrank_eq_one v w).2 (h ⟨w, hw⟩)⟩

variable [NumberField K] [NumberField L]


variable (L) in
theorem nonempty_placesOver : Nonempty (v.placesOver L) := by
  classical
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_completion (L := L) v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

end InfinitePlace

end GroundTheory.Global
