module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.ConjMonomial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  apply Fin.ext
  rw [stdBlocks_val]
  have hi : (i : ℕ) = 0 := by
    have := i.2
    simp only [ones] at this
    omega
  simp [ones, hi]

theorem tor_offDiag {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨s, rfl⟩ := hx
  have h : (leviEmb k (stdBlocks (ones N) (sum_ones N)) s : Matrix (Fin N) (Fin N) k)
      (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩)
      (stdBlocks (ones N) (sum_ones N) ⟨j, ⟨0, by simp [ones]⟩⟩) = 0 := by
    classical
    simp [leviEmb, Matrix.blockDiagonal'_apply, hij]
  rwa [stdBlocks_ones, stdBlocks_ones] at h

theorem mem_tor_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  have hd : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    intro i h0
    have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i i) (mul_inv_cancel x)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro l _
      by_cases hl : i = l
      · subst hl
        rw [h0, zero_mul]
      · rw [h i l hl, zero_mul]
  refine ⟨fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
    (Units.mk0 _ (hd a)), ?_⟩

  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    have h1 : (leviEmb k (stdBlocks (ones N) (sum_ones N))
        (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
          (Units.mk0 _ (hd a))) : Matrix (Fin N) (Fin N) k)
        (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩)
        (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩) = (x : Matrix (Fin N) (Fin N) k) i i := by
      simp [leviEmb, Matrix.blockDiagonal'_apply_eq, Matrix.algebraMap_matrix_apply]
    rw [stdBlocks_ones] at h1
    rw [h1]
  · have h1 : (leviEmb k (stdBlocks (ones N) (sum_ones N))
        (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
          (Units.mk0 _ (hd a))) : Matrix (Fin N) (Fin N) k)
        (stdBlocks (ones N) (sum_ones N) ⟨i, ⟨0, by simp [ones]⟩⟩)
        (stdBlocks (ones N) (sum_ones N) ⟨j, ⟨0, by simp [ones]⟩⟩) = 0 := by
      classical
      simp [leviEmb, Matrix.blockDiagonal'_apply, hij]
    rw [stdBlocks_ones, stdBlocks_ones] at h1
    rw [h i j hij]
    exact h1

end GlobalTheory.CompanionTheory.LbElem.ConjMonomial

end
