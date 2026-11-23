module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeriodMapEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.per_hecke_and_diamond_sub_mem_b1_of_lev : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ f : ModularForm (Lev N l) (k : ℤ),
  (∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
    per (Lev N l) (k - 2) (TqF (k : ℤ) q σ ⇑f) - TqZ (Lev N l) (k - 2) q σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) ∧
  per (Lev N l) (k - 2) (UlF (k : ℤ) l ⇑f) - UlZ (Lev N l) (k - 2) l (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2) ∧
  (∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    per (Lev N l) (k - 2) (DdF (k : ℤ) σ ⇑f) - DdZ (Lev N l) (k - 2) σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.HeckeEqv.period_map_equivariant | exact GlobalTheory.HeckeFamilyMatrices.HeckeEqv.period_map_equivariant | (intros; apply GlobalTheory.HeckeFamilyMatrices.HeckeEqv.period_map_equivariant <;> assumption)
