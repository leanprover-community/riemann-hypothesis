module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelevantBruhatCellsLevelDatum
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.exists_relevant_bruhat_cells_levelDatum : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N), L.sharp = false → (∀ a, L.co a = 1) → ∀ k : ℕ, 0 < k → k < N → ∃ R : Finset (GG g N), (g - 1) * g ^ (k - 1) ≤ R.card ∧ (∀ w ∈ R, (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (w : GG g N).val a b = if a = b then 1 else 0) ∧ ∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) ∧ ∀ w ∈ R, ∀ u u' : GG g N, IsUp g N u → IsUp g N u' → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0) → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u' : GG g N).val a b = if a = b then 1 else 0) → u * w = w * u' → L.chi u = L.chi u' := by
  first | exact @GlobalTheory.BadShare.Cells.relevant_cells | exact GlobalTheory.BadShare.Cells.relevant_cells | (intros; apply GlobalTheory.BadShare.Cells.relevant_cells <;> assumption)
