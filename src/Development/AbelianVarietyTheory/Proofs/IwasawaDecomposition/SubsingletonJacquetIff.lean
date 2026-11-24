module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CuspEntries

theorem blk_two_stdSum {r t N : ℕ} (h : r + t = N) (a : Fin N) :
    blk (two (stdSum h)) a = decide (r ≤ (a : ℕ)) := by
  obtain ⟨a, rfl⟩ := (stdSum h).surjective a
  rcases a with a | a
  · rw [← two_false, blk_apply, two_false]
    simp [stdSum]
  · rw [← two_true, blk_apply, two_true]
    simp [stdSum]

theorem mem_unipRad_two_stdSum {R : Type} [CommRing R] {r t N : ℕ} (h : r + t = N) (u : GL (Fin N) R) :
    u ∈ unipRad R (two (stdSum h)) ↔ ∀ a b : Fin N, ¬ ((a : ℕ) < r ∧ r ≤ (b : ℕ)) →
      (u : Matrix (Fin N) (Fin N) R) a b = (1 : Matrix (Fin N) (Fin N) R) a b := by
  rw [CuspMax.mem_unipRad_iff_entries]
  refine forall₂_congr fun a b => imp_congr_left (not_congr ?_)
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : r ≤ (a : ℕ) <;> by_cases h2 : r ≤ (b : ℕ) <;> simp [h1, h2] <;> omega

end GlobalTheory.CuspEntries
