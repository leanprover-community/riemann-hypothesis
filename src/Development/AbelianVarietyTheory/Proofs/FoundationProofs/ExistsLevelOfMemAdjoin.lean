module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace

@[expose] public section

noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
open Polynomial

namespace GlobalTheory.K5.Level

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev Bn (T : Tower p Ω) (n : ℕ) : Subalgebra (O0 p) Ω :=
  Algebra.adjoin (O0 p) {T.ζ n, T.qq n}

theorem bn_le_succ (T : Tower p Ω) (n : ℕ) : Bn T n ≤ Bn T (n + 1) := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · rw [← T.ζpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _
  · rw [← T.qpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _

theorem bn_mono (T : Tower p Ω) : Monotone (Bn T) :=
  monotone_nat_of_le_succ (bn_le_succ T)

theorem bn_le_B (T : Tower p Ω) (n : ℕ) :
    Bn T n ≤ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  apply Algebra.adjoin_mono
  rintro x (rfl | rfl)
  · exact Or.inl ⟨n, rfl⟩
  · exact Or.inr ⟨n, rfl⟩

theorem exists_mem_bn (T : Tower p Ω) {b : Ω}
    (hb : b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)) : ∃ n, b ∈ Bn T n := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact ⟨n, Algebra.subset_adjoin (by simp)⟩
    · exact ⟨n, Algebra.subset_adjoin (by simp)⟩
  | algebraMap r => exact ⟨0, Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := hy
    exact ⟨max m k, Subalgebra.add_mem _ (bn_mono T (le_max_left m k) hm)
      (bn_mono T (le_max_right m k) hk)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := hy
    exact ⟨max m k, Subalgebra.mul_mem _ (bn_mono T (le_max_left m k) hm)
      (bn_mono T (le_max_right m k) hk)⟩

theorem bn_le_range (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (h : IsEmb T n ι) :
    Bn T n ≤ ι.range := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact ⟨xn p n, h.1⟩
  · exact ⟨yn p n, h.2⟩

theorem range_le_bn (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (h : IsEmb T n ι)
    (w : On p n) : ι w ∈ Bn T n := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hX : ι (Ideal.Quotient.mk (towerIdeal p n) (C X)) ∈ Bn T n := by
    have : ι (xn p n) = T.ζ n := h.1
    simp only [xn] at this
    rw [this]; exact Algebra.subset_adjoin (by simp)
  have hY : ι (Ideal.Quotient.mk (towerIdeal p n) X) ∈ Bn T n := by
    have : ι (yn p n) = T.qq n := h.2
    simp only [yn] at this
    rw [this]; exact Algebra.subset_adjoin (by simp)
  have hC : ∀ a : Polynomial (O0 p), ι (Ideal.Quotient.mk (towerIdeal p n) (C a)) ∈ Bn T n := by
    intro a
    induction a using Polynomial.induction_on with
    | C c =>
      have : (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c := rfl
      rw [this, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg =>
      set_option synthInstance.maxHeartbeats 200000 in
        simpa only [map_add] using Subalgebra.add_mem (Bn T n) hf hg
    | monomial k c _ =>
      simp only [map_mul, map_pow]
      refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hX _)
      have : (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c := rfl
      rw [this, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ c
  induction P using Polynomial.induction_on with
  | C a => exact hC a
  | add f g hf hg =>
    set_option synthInstance.maxHeartbeats 200000 in
      simpa only [map_add] using Subalgebra.add_mem (Bn T n) hf hg
  | monomial k a _ =>
    simp only [map_mul, map_pow]
    exact Subalgebra.mul_mem _ (hC a) (Subalgebra.pow_mem _ hY _)

end GlobalTheory.K5.Level

theorem GlobalTheory.K5.exists_level_of_mem_adjoin :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
      ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
        ∃ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (w : On p n), 1 ≤ n ∧ IsEmb T n ι ∧ ι w = b ∧
          ∀ w' : On p n, ι w' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  intro p _ Ω _ _ _ T b hb
  obtain ⟨m, hm⟩ := GlobalTheory.K5.Level.exists_mem_bn T hb
  have hm1 : b ∈ GlobalTheory.K5.Level.Bn T (m + 1) := GlobalTheory.K5.Level.bn_le_succ T m hm
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T (m + 1)
  obtain ⟨w, hw⟩ := GlobalTheory.K5.Level.bn_le_range T (m + 1) ι hι hm1
  exact ⟨m + 1, ι, w, Nat.le_add_left 1 m, hι, hw, fun w' =>
    GlobalTheory.K5.Level.bn_le_B T (m + 1) (GlobalTheory.K5.Level.range_le_bn T (m + 1) ι hι w')⟩
