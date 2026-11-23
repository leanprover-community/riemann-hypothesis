module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightIsoOfEqualCasimirStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.LowestType

theorem two_le_of_not_sameBlock {p q : ℕ} {a b : Ix p q} (h : ¬ sameBlock a b) : 2 ≤ p + q := by
  unfold sameBlock at h
  rcases a with i | i <;> rcases b with j | j
  · exact (h trivial).elim
  · have hi := i.pos
    have hj := j.pos
    omega
  · have hi := i.pos
    have hj := j.pos
    omega
  · exact (h trivial).elim

theorem gapGt_of_cube {p q : ℕ} {lam : Ix p q → ℚ} (hg : GapGt lam (((p + q : ℕ) : ℝ) ^ 3))
    {h : ℝ} (hh : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) → h ≤ ((p + q : ℕ) : ℝ) ^ 3) : GapGt lam h := by
  unfold GapGt at hg ⊢
  intro a b hab
  have h2 : (2 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast two_le_of_not_sameBlock hab
  exact lt_of_le_of_lt (hh h2) (hg a b hab)

private lemma cube_div_add_one_le_cube_and_sub_one_le {n : ℝ} (h2 : 2 ≤ n) : n ^ 3 / 24 + 1 ≤ n ^ 3 ∧ n - 1 ≤ n ^ 3 := by

  have hp : 0 ≤ n * (n - 1) * (n + 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have e : n * (n - 1) * (n + 1) = n ^ 3 - n := by ring
  constructor <;> linarith

theorem embeds_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3) → ∀ (A B : UGKMod p q) (u : A.M.V) (v : B.M.V), IsHW A.M.act (blattner lam) u → IsHW B.M.act (blattner lam) v → casimir A.M.act u = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • u → casimir B.M.act v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v → IrrGK B.M → ∃ e : B.M.V →ₗ[ℂ] A.M.V, Function.Injective e ∧ e v = u ∧ ∀ Z x, e (B.M.act Z x) = A.M.act Z (e x) := by
  intro hQ7 hQ8 p q lam hlam hgap A B u v hu hv hcu hcv hirr

  have g1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) :=
    gapGt_of_cube hgap (fun h2 => (cube_div_add_one_le_cube_and_sub_one_le h2).1)
  have g2 : GapGt lam (((p + q : ℕ) : ℝ) - 1) :=
    gapGt_of_cube hgap (fun h2 => (cube_div_add_one_le_cube_and_sub_one_le h2).2)
  obtain ⟨⟨e, he, hcomm, heu, -⟩, -⟩ :=
    GlobalTheory.T.highest_weight_iso_of_equal_casimir hQ7 hQ8 p q lam hlam g1 g2 A B u v hu hv hcu hcv hirr
  exact ⟨e, he, heu, hcomm⟩

end GlobalTheory.LowestType
