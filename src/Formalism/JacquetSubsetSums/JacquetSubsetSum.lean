module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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

open Module

noncomputable section

namespace Formalism.PacketSums

def NoFixedSum : Prop :=
  ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N],
    (∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) →
    ∀ x y : G, ∑ n : N, LinearMap.trace ℂ V (τ (x * (n : G) * y)) = 0

def IwahoriNewton : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (ϖ : O), ϖ ∈ IsLocalRing.maximalIdeal O →
    ∀ (r : ℕ) (a : Fin r → ℕ), StrictAnti a →
    ∀ i₁ i₂ : Matrix (Fin r) (Fin r) O,
    (∀ i, IsUnit (i₁ i i)) → (∀ i, IsUnit (i₂ i i)) →
    (∀ i j, j < i → ϖ ∣ i₁ i j) → (∀ i j, j < i → ϖ ∣ i₂ i j) →
    ∀ k : ℕ, k ≤ r → ∃ u : Oˣ,
      (i₁ * Matrix.diagonal (fun i => ϖ ^ a i) * i₂).charpoly.coeff (r - k) =
        (u : O) * ϖ ^ (∑ j ∈ Finset.univ.filter (fun j : Fin r => r - k ≤ (j : ℕ)), a j)

def numK {r : ℕ} (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK] (μ : Fin r → ℤ)
    (β : Fin r → ℂ) : ℂ :=
  ∑ w : WK, ((Equiv.Perm.sign (w : Equiv.Perm (Fin r)) : ℤ) : ℂ) *
    ∏ i, β i ^ μ ((w : Equiv.Perm (Fin r))⁻¹ i)

def vdm {r : ℕ} (β : Fin r → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), (β i - β j)

def PacketSum : Prop :=
  ∀ (r : ℕ) (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK] (T : Finset (Equiv.Perm (Fin r))),
    Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin r)))⁻¹ * (p.1 : Equiv.Perm (Fin r))) →
    ∀ (μ : Fin r → ℤ) (α : Fin r → ℂ), (∀ i, α i ≠ 0) → Function.Injective α →
      ∑ y ∈ T, numK WK μ (fun i => α (y⁻¹ i)) / vdm (fun i => α (y⁻¹ i)) =
        (∑ w : Equiv.Perm (Fin r), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, α i ^ μ (w⁻¹ i)) / vdm α

def SignEven : Prop :=
  ∀ p q : ℕ, Odd (p + q) → (-1 : ℤ) ^ (p * q) = 1

end Formalism.PacketSums
