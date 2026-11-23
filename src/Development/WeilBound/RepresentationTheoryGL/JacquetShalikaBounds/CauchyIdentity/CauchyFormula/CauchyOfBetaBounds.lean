module

public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT
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

noncomputable section

open Finset GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace PositivityTheory.RgJS

namespace CauchyPositivity

theorem exists_pos (A B x : ℝ) (hx : 0 ≤ x) (h : x * A * B < 1) :
    ∃ δ : ℝ, 0 < δ ∧ x * max A δ * max B δ < 1 := by
  have hg : Continuous (fun δ : ℝ => x * max A δ * max B δ) := by fun_prop
  have h0 : x * max A 0 * max B 0 < 1 := by
    rcases le_total A 0 with hA | hA
    · rw [max_eq_right hA]; simp
    rcases le_total B 0 with hB | hB
    · rw [max_eq_right hB]; simp
    rw [max_eq_left hA, max_eq_left hB]; exact h
  have hn : ∀ᶠ δ in nhds (0:ℝ), x * max A δ * max B δ < 1 :=
    (hg.tendsto 0).eventually (gt_mem_nhds h0)
  have hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), x * max A δ * max B δ < 1 ∧ δ ∈ Set.Ioi (0:ℝ) :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds hn).and self_mem_nhdsWithin
  obtain ⟨δ, h1, h2⟩ := hev.exists
  exact ⟨δ, h2, h1⟩

end CauchyPositivity

open CauchyPositivity in
theorem cauchy_of_beta_bounds : BetaAll → SumBd → SchurJT → JTPad → Cauchy := by
  intro hBeta hSum hSchur hPad m m' hmm α β X A B hA hB hX
  obtain ⟨δ, hδ, hlt⟩ := exists_pos A B ‖X‖ (norm_nonneg X) hX
  have hA'pos : 0 < max A δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hB'pos : 0 < max B δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hαb : ∀ i, ‖((α i : ℂ))‖ ≤ max A δ := fun i => (hA i).trans (le_max_left _ _)
  have hβb : ∀ j, ‖((β j : ℂ))‖ ≤ max B δ := fun j => (hB j).trans (le_max_left _ _)
  have hH := hBeta m m' (fun i => (α i : ℂ)) β X (max A δ) (max B δ) hA'pos hB'pos hαb hβb hlt
  have e := fun l : Fin m' → ℕ => (hSchur m α (padN m l)).trans (hPad m m' hmm _ l)
  simp only [e]
  obtain ⟨hsum, hbdα⟩ := hSum m m' (max A δ) (max B δ) ‖X‖ hA'pos hB'pos (norm_nonneg _) hlt
  have hbdβ := (hSum m' m' (max B δ) (max B δ) 0 hB'pos hB'pos le_rfl (by simp)).2
  refine ⟨hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_), hH⟩
  rw [norm_mul, norm_mul, norm_pow, hSchur m' β]
  have h1 := hbdα (fun i => (α i : ℂ)) hαb l
  have h2 := hbdβ (fun j => (β j : ℂ)) hβb l
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
    (pow_nonneg (norm_nonneg _) _)

end PositivityTheory.RgJS
