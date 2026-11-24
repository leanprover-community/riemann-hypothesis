module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
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

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem mono_sub_mem_of_sub_mem {R : Type} [CommRing R] (I : Ideal R) (u v : Fin 2 → R)
    (h : ∀ i, u i - v i ∈ I) (a b : ℕ) : u 0 ^ a * u 1 ^ b - v 0 ^ a * v 1 ^ b ∈ I := by
  have h0 := Ideal.Quotient.eq.2 (h 0)
  have h1 := Ideal.Quotient.eq.2 (h 1)
  rw [← Ideal.Quotient.eq]
  simp only [map_mul, map_pow, h0, h1]

theorem Tower.B_sub_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] (b : X.Fn l) (hb : b ∈ X.B N l w) (n : ℕ) (u v : Fin 2 → ℤ_[l])
    (huv : ∀ i, u i - v i ∈ (idl l) ^ n) :
    b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, hc⟩ := hx.1
    rw [hc u, hc v, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← sub_smul]
    exact Submodule.smul_mem_smul (mono_sub_mem_of_sub_mem _ u v huv _ _) Submodule.mem_top
  | zero => simp
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    simp only [Pi.add_apply]
    convert this using 1
    abel
  | smul r x _ hx =>
    simp only [Pi.smul_apply, ← smul_sub]
    exact Submodule.smul_mem _ r hx

end GlobalTheory.KZ
