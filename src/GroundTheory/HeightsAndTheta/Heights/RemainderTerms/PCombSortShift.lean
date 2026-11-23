module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
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
import Mathlib.Tactic.Linter.Style
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

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

namespace Comb

theorem add_index_le_of_strictAnti {m : ℕ} {f : Fin m → ℕ} (hf : StrictAnti f) (a b : Fin m)
    (hab : a ≤ b) : f b + (b : ℕ) ≤ f a + (a : ℕ) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have h1 := ih (by omega)
    have h2 : f ⟨n + 1, hb⟩ < f ⟨n, by omega⟩ := hf (by simp [Fin.lt_def])
    simp only at h1 ⊢
    omega

theorem CombSortShift.proof (h1 : CombSortLe.Statement) : CombSortShift.Statement := by
  intro m lam hlam q i hq hinj
  set u := Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) with hu
  obtain ⟨σ, hσ⟩ := exists_perm_strictAnti hinj
  have hge : ∀ k : Fin m, stair m k ≤ u (σ k) := by
    intro k
    have hk := add_index_le_of_strictAnti hσ k ⟨m - 1, by have := k.isLt; omega⟩ (by rw [Fin.le_def]; exact Nat.le_sub_one_of_lt k.isLt)
    simp only [Function.comp_apply] at hk
    simp only [stair]
    omega
  refine ⟨σ, fun k => u (σ k) - stair m k, ?_, ?_, ?_⟩
  · intro a b hab
    have h := add_index_le_of_strictAnti hσ a b hab
    have ha := hge a
    have hb := hge b
    simp only [Function.comp_apply, stair] at h ha hb ⊢
    omega
  · intro k
    have hl : Antitone (fun j => lam j + stair m j) := by
      intro a b hab
      have := hlam hab
      simp only [stair]
      have : (a : ℕ) ≤ b := hab
      omega
    have hul : ∀ j, u j ≤ lam j + stair m j := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [hu]
      · simp [hu, Function.update_of_ne hj]
    have := h1 m u (fun j => lam j + stair m j) σ hl hul hσ.antitone k
    show u (σ k) - stair m k ≤ lam k
    omega
  · intro k
    have := hge k
    show u (σ k) = u (σ k) - stair m k + stair m k
    omega

end Comb

end GroundTheory.Heights₂.Heights.RestTerms
