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

open GlobalTheory.K5 Polynomial

namespace GlobalTheory.K5

def dlogSub (p : ℕ) [Fact p.Prime] (n : ℕ) : Subalgebra (O0 p) (On p n) where
  carrier := {w | KaehlerDifferential.D (O0 p) (On p n) w ∈
    Submodule.span (On p n) ({KaehlerDifferential.D (O0 p) (On p n) (xn p n),
      KaehlerDifferential.D (O0 p) (On p n) (yn p n)} : Set _)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact add_mem ha hb
  algebraMap_mem' := by
    intro r
    simp only [Set.mem_setOf_eq, Derivation.map_algebraMap]
    exact zero_mem _

theorem mem_dlogSub (p : ℕ) [Fact p.Prime] (n : ℕ) (w : On p n) : w ∈ dlogSub p n := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hx : xn p n ∈ dlogSub p n :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hy : yn p n ∈ dlogSub p n :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hC : ∀ a : Polynomial (O0 p), Ideal.Quotient.mk (towerIdeal p n) (C a) ∈ dlogSub p n := by
    intro a
    induction a using Polynomial.induction_on with
    | C r =>
      have : Ideal.Quotient.mk (towerIdeal p n) (C (C r)) = algebraMap (O0 p) (On p n) r := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ r
    | add a b ha hb => rw [Polynomial.C_add, RingHom.map_add (Ideal.Quotient.mk (towerIdeal p n))]; exact add_mem ha hb
    | monomial k r _ =>
      rw [Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      refine mul_mem ?_ (pow_mem hx _)
      have : Ideal.Quotient.mk (towerIdeal p n) (C (C r)) = algebraMap (O0 p) (On p n) r := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ r
  induction f using Polynomial.induction_on with
  | C a => exact hC a
  | add a b ha hb => rw [RingHom.map_add (Ideal.Quotient.mk (towerIdeal p n))]; exact add_mem ha hb
  | monomial k a _ =>
    rw [map_mul, map_pow]
    exact mul_mem (hC a) (pow_mem hy _)

theorem exists_isDlog : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (w : (On p n)ˣ), ∃ α β : On p n, IsDlog p n (w : On p n) α β := by
  intro p _ n w
  have h : KaehlerDifferential.D (O0 p) (On p n) (w : On p n) ∈
      Submodule.span (On p n) ({KaehlerDifferential.D (O0 p) (On p n) (xn p n),
        KaehlerDifferential.D (O0 p) (On p n) (yn p n)} : Set _) := mem_dlogSub p n (w : On p n)
  obtain ⟨P, Q, hPQ⟩ := Submodule.mem_span_pair.mp h
  refine ⟨yn p n * Q * ((w⁻¹ : (On p n)ˣ) : On p n), xn p n * P * ((w⁻¹ : (On p n)ˣ) : On p n), ?_⟩
  unfold IsDlog
  rw [← hPQ, smul_add, smul_smul, smul_smul, add_comm]
  congr 1
  · congr 1
    have := w.mul_inv
    linear_combination (xn p n * yn p n * Q) * (-this)
  · congr 1
    have := w.mul_inv
    linear_combination (xn p n * yn p n * P) * (-this)

end GlobalTheory.K5
