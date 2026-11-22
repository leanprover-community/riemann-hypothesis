module

public import Mathlib

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def GeomDistinct : Prop :=
  ∀ (p m0 : ℕ) (s : Finset ℕ), 2 ≤ p → (∀ D ∈ s, m0 ≤ D) → ∑ D ∈ s, (1 / (p : ℝ) ^ D) ≤ 2 / (p : ℝ) ^ m0

def AdmissibleSmallRatio : Prop :=
  ∀ (p k Ns D1 L1 R R' : ℕ) (a Y Qn be : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 < a → 0 < Qn → 1 ≤ L1 →
    be ≤ 4 * a / (p : ℝ) ^ (R + D1 + L1 + 1) →
    a / (8 * p * Y * (k : ℝ) ^ 2 * Ns * ((p : ℝ) ^ D1 * Qn)) < (p : ℝ) ^ R' →
    128 * (k : ℝ) ^ 2 * Ns * Y ^ 2 ≤ (p : ℝ) ^ (L1 - 1) →
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) < 32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ∧
    32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ≤ 1 / (4 * p * Y) ∧
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) ≤ 1 / (4 * Y)

end Formalism.InvariantFactorPaths.BranchingDimensions
