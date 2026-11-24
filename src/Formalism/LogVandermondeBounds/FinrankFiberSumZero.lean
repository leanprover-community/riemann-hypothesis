module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.LinearAlgebra.Dimension.Finrank
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Ops

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

def pair (f x : Fin r → k) : k := ∑ i, f i * x i

def opU (ψ : (Fin r → k) → R) (f : Fin r → k) : R :=
  ∑ x ∈ univ.filter (fun x => pair f x = 1), ψ x

def opD (φ : (Fin r → k) → R) (x : Fin r → k) : R :=
  ∑ f ∈ univ.filter (fun f => pair f x = 1), φ f

def diaP (c : kˣ) (φ : (Fin r → k) → R) (f : Fin r → k) : R := φ ((c : k) • f)

def diaV (c : kˣ) (ψ : (Fin r → k) → R) (x : Fin r → k) : R := ψ (((c⁻¹ : kˣ) : k) • x)

def nmP (φ : (Fin r → k) → R) (f : Fin r → k) : R := ∑ c : kˣ, diaP c φ f

def nmV (ψ : (Fin r → k) → R) (x : Fin r → k) : R := ∑ c : kˣ, diaV c ψ x

def trV (ψ : (Fin r → k) → R) : R := ∑ x ∈ univ.filter (fun x => x ≠ 0), ψ x

def trP (φ : (Fin r → k) → R) : R := ∑ f ∈ univ.filter (fun f => f ≠ 0), φ f

end Ops

def ramSub (ι H X K : Type) [DecidableEq ι] [Group H] [Fintype H] [MulAction (ι → H) X] [Field K] :
    Submodule K (X → K) where
  carrier := {φ | ∀ (v : ι) (x : X), ∑ c : H, φ ((Pi.mulSingle v c : ι → H) • x) = 0}
  add_mem' := fun {a b} ha hb v x => by
    have h1 : ∑ c : H, a ((Pi.mulSingle v c : ι → H) • x) = 0 := ha v x
    have h2 : ∑ c : H, b ((Pi.mulSingle v c : ι → H) • x) = 0 := hb v x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [h1, h2, add_zero]
  zero_mem' := fun v x => by simp
  smul_mem' := fun s a ha v x => by
    have h1 : ∑ c : H, a ((Pi.mulSingle v c : ι → H) • x) = 0 := ha v x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, h1, mul_zero]

def FinrankFiberSumZero : Prop :=
  ∀ (ι H X K : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] [Field K],
    (∀ (g : ι → H) (x : X), g • x = x → g = 1) →
    Module.finrank K (ramSub ι H X K) * Fintype.card H ^ Fintype.card ι =
      Fintype.card X * (Fintype.card H - 1) ^ Fintype.card ι

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
