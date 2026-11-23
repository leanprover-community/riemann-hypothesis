module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.Complex.Norm
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
public import Mathlib.Analysis.InnerProductSpace.Defs

@[expose] public section

theorem UpperTheory.Reformulated.B.DYhd3.main :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
      (∀ (u u' : V), (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u') = ((B : V → V →ₗ[ℂ] ℂ) u' : V → ℂ) u) →
        (∀ (u : V), (0 : ℝ) ≤ (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u).re) →
          ∀ (x y : V),
            ‖((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
              (((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ B hsymm hpos x y
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun u v => B u v
      conj_inner_symm := fun u v => hsymm v u
      re_inner_nonneg := fun u => hpos u
      add_left := fun u v w => by simp
      smul_left := fun u v r => by simp }
  have h : ‖B x y‖ * ‖B y x‖ ≤ (B x x).re * (B y y).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  have h2 : ‖B y x‖ = ‖B x y‖ := by
    rw [← hsymm x y]; exact RCLike.norm_conj _
  rw [h2] at h
  rw [sq]
  exact h
