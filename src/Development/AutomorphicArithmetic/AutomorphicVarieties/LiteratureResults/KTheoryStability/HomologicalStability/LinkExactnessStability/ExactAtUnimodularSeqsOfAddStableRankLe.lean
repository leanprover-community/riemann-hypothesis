module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtUnimodularSeqsOfLinkNilCoordSubspace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.LinksUnimodularSeqExactInStableRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleBoundedByCone
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem subsingleton_of_stableRangeLe_zero (R : Type) [CommRing R] (h : StableRangeLe R 0) :
    Subsingleton R := by
  have hu : Unimodular R (fun _ : Fin 1 => (1 : R)) :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one
  obtain ⟨t, ht⟩ := h 0 le_rfl (fun _ => 1) hu
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i : Fin 0 => (1 : R) + t i * 1) := by
    rw [show Ideal.span (Set.range fun i : Fin 0 => (1 : R) + t i * 1) = ⊤ from ht]
    exact Submodule.mem_top
  rw [Set.range_eq_empty, Ideal.span_empty, Ideal.mem_bot] at h1
  exact subsingleton_of_zero_eq_one h1.symm

theorem uniSeq_exactAt_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s →
    ∀ m q : ℕ, q + s ≤ m → ExactAt (uniSeq R m) q := by
  intro R _ s h m q hq
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · haveI := subsingleton_of_stableRangeLe_zero R h
    have hall : ∀ l : List (Fin m → R), l ∈ uniSeq R m :=
      fun l => ⟨fun _ => 0, fun _ _ => Subsingleton.elim _ _⟩
    exact GlobalTheory.T.seqChain_cycle_bounded_by_cone (Fin m → R) (uniSeq R m) (uniSeq R m) 0 (fun l _ => hall _) q
  · have hL := (GlobalTheory.SeqCx.linkExact_of_stableRangeLe R s h hs m).1
    exact GlobalTheory.T.exactAt_unimodularSeqs_of_link_nil_coordSubspace R m q (hL [] ⟨fun _ => 0, fun i _ => i.elim0⟩ q (by simpa using hq))

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_unimodularSeqs_of_add_stableRank_le : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ m q : ℕ, q + s ≤ m → ExactAt (uniSeq R m) q := by
  first
  | exact @GlobalTheory.uniSeq_exactAt_of_stableRangeLe
  | exact @GlobalTheory.subsingleton_of_stableRangeLe_zero
end
