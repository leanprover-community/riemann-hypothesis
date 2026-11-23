module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
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

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.WedgeNorm

theorem wedge_fromCols_le {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {N : Fam K ι}
    (h : IsWedge N) (κ κ' : Type) [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (X : Matrix ι κ K) (Z : Matrix ι κ' K) :
    N (κ ⊕ κ') (fromCols X Z) ≤ N κ X * N κ' Z := by
  by_cases hX : LinearIndependent K Xᵀ
  · obtain ⟨Y, hY⟩ := h.quot κ X hX
    obtain ⟨h1, h2, -⟩ := hY κ' Z
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (h.nonneg κ X)
  · have h0 : N (κ ⊕ κ') (fromCols X Z) = 0 := by
      by_contra hne
      have hli := (h.ne_zero _ _).1 hne
      apply hX
      have hc := hli.comp Sum.inl Sum.inl_injective
      have he : (((fromCols X Z)ᵀ : (κ ⊕ κ') → ι → K) ∘ Sum.inl) = (Xᵀ : κ → ι → K) := by
        funext i j
        rfl
      rwa [he] at hc
    rw [h0]
    exact mul_nonneg (h.nonneg _ _) (h.nonneg _ _)

theorem wedgeSub : WedgeSub := by
  intro K ι _ _ _ N h κ₀ κ₁ κ₂ _ _ _ _ _ _ B A C
  by_cases hB : LinearIndependent K Bᵀ
  · obtain ⟨Y, hY⟩ := h.quot κ₀ B hB
    obtain ⟨h1, -, -⟩ := hY (κ₁ ⊕ κ₂) (fromCols A C)
    obtain ⟨h2, -, -⟩ := hY κ₁ A
    obtain ⟨h3, -, -⟩ := hY κ₂ C
    rw [h1, h2, h3, Matrix.mul_fromCols]
    have hle := wedge_fromCols_le h κ₁ κ₂ ((1 - B * Y) * A) ((1 - B * Y) * C)
    have hn := h.nonneg κ₀ B
    calc N κ₀ B * N (κ₁ ⊕ κ₂) (fromCols ((1 - B * Y) * A) ((1 - B * Y) * C)) * N κ₀ B
        ≤ N κ₀ B * (N κ₁ ((1 - B * Y) * A) * N κ₂ ((1 - B * Y) * C)) * N κ₀ B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hn) hn
      _ = N κ₀ B * N κ₁ ((1 - B * Y) * A) * (N κ₀ B * N κ₂ ((1 - B * Y) * C)) := by ring
  · have h0 : N κ₀ B = 0 := by
      by_contra hne
      exact hB ((h.ne_zero _ _).1 hne)
    rw [h0, mul_zero]
    exact mul_nonneg (h.nonneg _ _) (h.nonneg _ _)

end GlobalTheory.CompanionTheory.WedgeNorm
