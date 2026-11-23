module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem acris_basic : ∀ (l : ℕ) [Fact l.Prime], (∀ x : Formalism.Per.Acris l, ((l : ℕ) : Formalism.Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : Formalism.Per.Acris l)}) (Formalism.Per.Acris l) ∧ (∀ (k : ℕ) (x : Formalism.Per.Acris l), ∃ d : ↥(Formalism.Per.Acris0 l), x - algebraMap ↥(Formalism.Per.Acris0 l) (Formalism.Per.Acris l) d ∈ Ideal.span {((l : ℕ) : Formalism.Per.Acris l) ^ k}) ∧ ∀ (k : ℕ) (d : ↥(Formalism.Per.Acris0 l)), algebraMap ↥(Formalism.Per.Acris0 l) (Formalism.Per.Acris l) d ∈ Ideal.span {((l : ℕ) : Formalism.Per.Acris l) ^ k} ↔ d ∈ Ideal.span {((l : ℕ) : ↥(Formalism.Per.Acris0 l)) ^ k} := by
  intro l _
  obtain ⟨hc, ht, hd, hv⟩ := GlobalTheory.MemLoc.acris_basic l
  refine ⟨ht, hc, fun k x => ?_, fun k d => ?_⟩
  · obtain ⟨s, z, hz⟩ := hd x k
    exact ⟨s, Ideal.mem_span_singleton.2 ⟨z, by rw [hz, add_sub_cancel_left]⟩⟩
  · rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    exact hv d k

end GlobalTheory.Per
