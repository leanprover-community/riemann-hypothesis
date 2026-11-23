module

public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open Formalism.L2.DIV

namespace GlobalTheory

theorem absIrrChar_mem_closure_primitiveRoot {G : Type} [Group G] [Fintype G] {K : Type} [Field K]
    [CharZero K] (z : K) (hz : IsPrimitiveRoot z (Fintype.card G)) (χ : G → K) (hχ : IsAbsIrrChar χ)
    (g : G) : χ g ∈ Subring.closure ({z} : Set K) := by
  obtain ⟨n, ρ, -, hch⟩ := hχ
  set N := Fintype.card G with hN
  haveI : NeZero N := ⟨Fintype.card_ne_zero⟩
  set f := ρ g with hf
  have hfN : f ^ N = 1 := by rw [hf, ← map_pow, pow_card_eq_one, map_one]
  have htr : LinearMap.trace (AlgebraicClosure K) _ f = (LinearMap.charpoly f).roots.sum := by
    rw [LinearMap.trace_eq_matrix_trace (AlgebraicClosure K) (Pi.basisFun (AlgebraicClosure K) (Fin n)),
      Matrix.trace_eq_sum_roots_charpoly, LinearMap.charpoly_toMatrix]
  have hz' : IsPrimitiveRoot (algebraMap K (AlgebraicClosure K) z) N :=
    hz.map_of_injective (algebraMap K (AlgebraicClosure K)).injective
  have hroot : ∀ μ ∈ (LinearMap.charpoly f).roots,
      ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k) := by
    intro μ hμ
    have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := hv.pow_apply N
    rw [hfN] at h1
    have hμN : μ ^ N = 1 := by
      have h2 : (μ ^ N - 1) • v = 0 := by
        rw [sub_smul, ← h1, one_smul]; simp
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv.2
    obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hμN
    exact ⟨k, by rw [map_pow, hk]⟩
  have hsum : ∀ m : Multiset (AlgebraicClosure K),
      (∀ μ ∈ m, ∃ k : ℕ, μ = algebraMap K (AlgebraicClosure K) (z ^ k)) →
      ∃ y ∈ Subring.closure ({z} : Set K), algebraMap K (AlgebraicClosure K) y = m.sum := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; exact ⟨0, zero_mem _, by simp⟩
    | cons a m ih =>
      intro h
      obtain ⟨y, hy, hy'⟩ := ih (fun μ hμ => h μ (Multiset.mem_cons_of_mem hμ))
      obtain ⟨k, hk⟩ := h a (Multiset.mem_cons_self a m)
      refine ⟨z ^ k + y, add_mem (pow_mem (Subring.subset_closure (Set.mem_singleton z)) k) hy, ?_⟩
      rw [Multiset.sum_cons, map_add (f := _), hy', hk]
  obtain ⟨y, hy, hy'⟩ := hsum _ hroot
  have hχg : algebraMap K (AlgebraicClosure K) (χ g) = algebraMap K (AlgebraicClosure K) y := by
    rw [← hch g, hy', ← htr]; rfl
  rw [(algebraMap K (AlgebraicClosure K)).injective hχg]
  exact hy

end GlobalTheory
