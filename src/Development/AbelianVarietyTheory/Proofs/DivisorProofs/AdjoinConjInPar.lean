module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem adjoin_conj_inPar : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F'), (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} → InPar a (y₀⁻¹ * γ * y₀) → InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) := by
  intro F F' _ _ _ a n γ y₀ δ hδ hγ

  let T : Subalgebra F' (Matrix (Fin n) (Fin n) F') :=
    { carrier := {M | ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0}
      mul_mem' := by
        intro M N hM hN i j hj hi
        simp only [Set.mem_setOf_eq] at hM hN
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : (k : ℕ) < a
        · rw [hM i k hk hi, zero_mul]
        · rw [hN k j hj (not_lt.1 hk), mul_zero]
      add_mem' := by
        intro M N hM hN i j hj hi
        simp only [Set.mem_setOf_eq] at hM hN
        rw [Matrix.add_apply, hM i j hj hi, hN i j hj hi, add_zero]
      algebraMap_mem' := by
        intro r i j hj hi
        have hij : i ≠ j := by
          intro h; subst h; omega
        simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne hij] }
  let c : GL (Fin n) F' := incl F F' n y₀
  have key : ∀ (M : Matrix (Fin n) (Fin n) F') (hM : M ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')}),
      ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * M * (c : Matrix (Fin n) (Fin n) F') ∈ T := by
    intro M hM
    induction hM using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (c : Matrix (Fin n) (Fin n) F')
          = ((incl F F' n (y₀⁻¹ * γ * y₀) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
        simp only [c, map_mul, map_inv, Units.val_mul]
      rw [e]
      intro i j hj hi
      simp only [incl, gal, Matrix.GeneralLinearGroup.map_apply]
      rw [hγ i j hj hi, map_zero]
    | algebraMap r =>
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * algebraMap F' (Matrix (Fin n) (Fin n) F') r * (c : Matrix (Fin n) (Fin n) F')
          = algebraMap F' (Matrix (Fin n) (Fin n) F') r := by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]
      rw [e]; exact T.algebraMap_mem r
    | add x y _ _ hx hy =>
      rw [mul_add, add_mul]; exact T.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (x * y) * (c : Matrix (Fin n) (Fin n) F')
          = (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * x * (c : Matrix (Fin n) (Fin n) F')) *
            (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * y * (c : Matrix (Fin n) (Fin n) F')) := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
      rw [e]; exact T.mul_mem hx hy
  intro i j hj hi
  have := key _ hδ i j hj hi
  simpa [c, Units.val_mul] using this

end GlobalTheory
