module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem VandCount.card_lt (N : ℕ) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card = N * (N - 1) / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

theorem VandCount.card_cross (N j : ℕ) (hj : j ≤ N) :
    (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card = j * (N - j) := by
  have h1 : (Finset.univ.filter (fun a : Fin N => (a : ℕ) < j)).card = j := by
    rw [Fin.card_filter_val_lt, min_eq_right hj]
  have h2 : (Finset.univ.filter (fun a : Fin N => j ≤ (a : ℕ))).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun a : Fin N => (a : ℕ) < j)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [← Finset.univ_product_univ, Finset.filter_product (fun a : Fin N => (a : ℕ) < j)
    (fun b : Fin N => j ≤ (b : ℕ)), Finset.card_product, h1, h2]

theorem VandCount.proof : VandCount.Statement := by
  intro Ψ _ _ N j hj
  unfold dimN vandCount dimFl
  have hc : Fintype.card (VandPair Ψ N j) = Fintype.card Ψ *
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card := by
    rw [Fintype.card_subtype, ← Finset.card_univ (α := Ψ), ← Finset.card_product, Finset.univ_product_univ.symm,
      Finset.filter_product_right (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))]
  have hsplit : (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2)).card =
      (Finset.univ.filter (fun ab : Fin N × Fin N =>
        ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))).card +
      (Finset.univ.filter (fun ab : Fin N × Fin N => (ab.1 : ℕ) < j ∧ j ≤ (ab.2 : ℕ))).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
      (fun ab : Fin N × Fin N => ab.1 < ab.2)) (fun ab => ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    ext ab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases ha : (ab.1 : ℕ) < j
      · exact ⟨ha, by by_contra hb; exact h2 ⟨fun _ => by omega, fun _ => ha⟩⟩
      · exact absurd ⟨fun h => absurd h ha, fun h => by omega⟩ h2
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, fun h => by have := h.1 h1; omega⟩
  rw [hc, ← VandCount.card_lt, hsplit, VandCount.card_cross N j hj]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
