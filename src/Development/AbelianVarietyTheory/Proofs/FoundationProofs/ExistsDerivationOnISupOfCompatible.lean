module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem isDerOn_iSup_glue (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B : ℕ → Subalgebra A S) (hB : Monotone B) (D : ℕ → S → M)
    (hDer : ∀ m, IsDerOn (B m) (D m)) (hcomp : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) :
    ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  classical
  have hD : ∀ m k, m ≤ k → ∀ x ∈ B m, D k x = D m x := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => intro x _; rfl
    | succ k hmk ih =>
      intro x hx
      rw [hcomp k x (hB hmk hx), ih x hx]
  let D' : S → M := fun x => if h : ∃ m, x ∈ B m then D (Nat.find h) x else 0
  have hD' : ∀ m, ∀ x ∈ B m, D' x = D m x := by
    intro m x hx
    have h : ∃ m, x ∈ B m := ⟨m, hx⟩
    simp only [D', dif_pos h]
    exact (hD _ m (Nat.find_min' h hx) x (Nat.find_spec h)).symm
  have hmem : ∀ x ∈ (⨆ m, B m), ∃ m, x ∈ B m := fun x hx =>
    by
    have := hx
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hB.directed_le, Set.mem_iUnion] at this
    exact this
  refine ⟨D', ⟨?_, ?_, ?_⟩, hD'⟩
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (add_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).add x hx' y hy']
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (mul_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).mul x hx' y hy']
  · intro a
    rw [hD' 0 _ ((B 0).algebraMap_mem a), (hDer 0).alg a]

end GlobalTheory.AlmostEt
