module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialOfConjTorus
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.TorComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones_eq (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    simp only [ones] at this
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [ones, hi]

theorem offDiag_of_mem {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  apply GlobalTheory.CompanionTheory.LbElem.ConjMonomial.tor_offDiag <;> assumption

theorem diag_ne_zero {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) (i : Fin N) :
    (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
  have hM : (x : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun l => (x : Matrix (Fin N) (Fin N) k) l l := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact h a b hab
  have hdet : (x : Matrix (Fin N) (Fin N) k).det ≠ 0 := (Matrix.isUnits_det_units x).ne_zero
  rw [hM, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

theorem mem_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  apply GlobalTheory.CompanionTheory.LbElem.ConjMonomial.mem_tor_of_offDiag <;> assumption

theorem eq_diagonal {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → M i j = 0) : M = Matrix.diagonal fun i => M i i := by
  ext a b
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab]
    exact h a b hab

theorem mul_comm_of_mem {N : ℕ} {a b : GL (Fin N) k} (ha : a ∈ Tor k N) (hb : b ∈ Tor k N) :
    a * b = b * a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul,
    eq_diagonal (a : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem ha hij),
    eq_diagonal (b : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem hb hij),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem tor_comm_and_mem_iff : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ),
    (∀ a ∈ PositivityTheory.Lbc.Tor k N, ∀ b ∈ PositivityTheory.Lbc.Tor k N, a * b = b * a) ∧
      ∀ x : GL (Fin N) k, x ∈ PositivityTheory.Lbc.Tor k N ↔
        ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  intro k _ _ _ _ N
  exact ⟨fun a ha b hb => mul_comm_of_mem ha hb,
    fun x => ⟨fun hx i j hij => offDiag_of_mem hx hij, mem_of_offDiag x⟩⟩

end GlobalTheory.CompanionTheory.LbElem.TorComm

end
