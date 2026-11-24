module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

section Chart

variable (o : Type*) {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι : Type*}

def chartRing (x : ι → Ω) (i : ι) : Subalgebra o Ω :=
  Algebra.adjoin o (Set.range fun j => x j / x i)

structure ChartBundle (x : ι → Ω) (r : ℕ) (E : Type*) [AddCommGroup E] [Module Ω E] where

  lat : ι → AddSubgroup E

  stable : ∀ i, ∀ a ∈ chartRing o x i, ∀ e ∈ lat i, a • e ∈ lat i

  frame : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing o x i) ∧
    (∀ l, c l ∈ chartRing o x i) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ lat i) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing o x i) ∧ e = ∑ q, a q • b q

  overlap : ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ lat i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ lat j

variable {o}

theorem div_mem_chartRing (x : ι → Ω) (i j : ι) :
    x j / x i ∈ chartRing o x i :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem exists_pow_mul_mem_chartRing (x : ι → Ω) (i j : ι) (hi : x i ≠ 0)
    {a : Ω} (ha : a ∈ chartRing o x i) :
    ∃ m : ℕ, (x i / x j) ^ m * a ∈ chartRing o x j := by
  have hij : x i / x j ∈ chartRing o x j := div_mem_chartRing x j i
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have : x i / x j * (x k / x i) = x k / x j := by field_simp
    rw [pow_one, this]
    exact div_mem_chartRing x j k
  | algebraMap r =>
    exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y + z) =
        (x i / x j) ^ n * ((x i / x j) ^ m * y) + (x i / x j) ^ m * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hij _) hm) (mul_mem (pow_mem hij _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y * z) = ((x i / x j) ^ m * y) * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact mul_mem hm hn

variable (o)

def lineLat (x : ι → Ω) (d : ℕ) (i : ι) : AddSubgroup Ω :=
  ((Subalgebra.toSubmodule (chartRing o x i)).map (LinearMap.mulRight o (x i ^ d))).toAddSubgroup

variable {o}

variable (o)

end Chart

end ReciprocityTheory.ChartRestriction.G.Geo
