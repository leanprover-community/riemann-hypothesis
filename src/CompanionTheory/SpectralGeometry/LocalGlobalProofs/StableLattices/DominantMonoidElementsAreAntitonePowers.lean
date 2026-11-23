module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem tExp_antitone (n : ℕ) (i : Fin (n + 2)) : Antitone (tExp n i) := by
  intro j k hjk
  have hjk' : (j : ℕ) ≤ (k : ℕ) := hjk
  unfold tExp
  by_cases h : (i : ℕ) = n + 1
  · simp [h]
  · simp only [h, if_false]
    by_cases hk : (k : ℕ) < i
    · have hj : (j : ℕ) < i := lt_of_le_of_lt hjk' hk
      simp [hj, hk]
    · by_cases hj : (j : ℕ) < i <;> simp [hj, hk]

theorem closure_tGen_antitone (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (p : Lˣ) (s : GL (Fin n) L)
    (hs : s ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L))) :
    ∃ a : Fin n → ℤ, Antitone a ∧ s = dPow p a := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨tExp n i, tExp_antitone n i, rfl⟩
  | one => exact ⟨0, fun _ _ _ => le_rfl, (dPow_zero p).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, ha.add hb, (dPow_add p a b).symm⟩

end GlobalTheory.CompanionTheory.CartGL
