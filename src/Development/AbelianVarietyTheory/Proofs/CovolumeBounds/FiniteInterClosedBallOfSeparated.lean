module

import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.TypeStar
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

open Metric MeasureTheory Module Set

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finset_card_le_of_separated (s : Finset E) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (x : E)
    (hs : ∀ a ∈ s, dist a x ≤ R) (hsep : (s : Set E).Pairwise fun a b => d ≤ dist a b) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ E := by
  apply Formalism.SA.P.card_le_of_separated s (fun a => a - x) d R hd hR
  · intro a ha b hb hab
    simpa only [← dist_eq_norm, dist_sub_right] using hsep ha hb hab
  · intro a ha
    simpa only [← dist_eq_norm] using hs a ha

theorem one_add_two_mul_div_pow_le {d R : ℝ} (hd : 0 < d) (hR : d ≤ R) (n : ℕ) :
    (1 + 2 * R / d) ^ n ≤ (3 * R / d) ^ n := by
  have hR0 : 0 ≤ R := hd.le.trans hR
  refine pow_le_pow_left₀ (by positivity) ?_ n
  have h1 : 1 ≤ R / d := (one_le_div hd).2 hR
  have : 3 * R / d = R / d + 2 * R / d := by ring
  linarith

end GlobalTheory
