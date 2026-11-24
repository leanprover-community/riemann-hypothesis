module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_comap_injective :
    ∀ (G G' : Type) [Group G] [Group G'] (j : G' →* G) (R : ℕ → Subgroup G) (B : Subgroup G), Function.Injective j →
      jumpSum (fun t => (R t).comap j) ⊤ (B.comap j) = jumpSum R j.range B := by
  intro G G' _ _ j R B hj
  unfold jumpSum
  apply finsum_congr
  intro t
  have h1 : (⊤ ⊓ (R t).comap j ≤ B.comap j) ↔ (j.range ⊓ R t ≤ B) := by
    rw [top_inf_eq]
    constructor
    · rintro h x ⟨⟨y, rfl⟩, hy⟩
      exact h (show y ∈ (R t).comap j from hy)
    · intro h y hy
      exact h ⟨⟨y, rfl⟩, hy⟩
  have h2 : Nat.card ↥(⊤ ⊓ (R t).comap j) = Nat.card ↥(j.range ⊓ R t) := by
    rw [top_inf_eq, ← Subgroup.map_comap_eq, Subgroup.card_map_of_injective hj]
  rw [h2]
  by_cases h : j.range ⊓ R t ≤ B
  · rw [if_pos (h1.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (h1.mp h')), if_neg h]

end GlobalTheory.PMon.Ram
