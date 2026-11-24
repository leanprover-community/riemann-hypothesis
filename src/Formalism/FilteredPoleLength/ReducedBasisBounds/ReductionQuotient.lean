module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module Polynomial
open scoped ComplexOrder

def QuotientLength : Prop :=
  ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (c : V →ₗ[K] (Fin n → K)) (N : Submodule K V),
    LinearMap.ker c ≤ N → ∀ (X : Submodule O V) (e be : ℕ) (th : Fin n → V),
    (∀ x ∈ X, ∀ i, ∃ a : O, c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K a) →
    (∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X) →
    ∀ a a' : O, a ≠ 0 → a' ≠ 0 →
    algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a' →
      let Tj : Submodule O V := Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)
      ∃ m : ℕ, Module.length O (↥X ⧸ ((X ⊓ N.restrictScalars O) ⊔ Tj).comap X.subtype) = m ∧
        (m : ℤ) ≤ ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ)

def PoleOrderGood : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ) (e : ℤ), 1 ≤ ep → 0 ≤ c' → 0 ≤ vet →
    ν ≤ νs + c' * vet → (∃ n : ℤ, (ep : ℝ) * ν = n) → (T : ℝ) * νs ≤ e →
      ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def PoleOrderBad : Prop :=
  ∀ (ep T : ℕ) (ν νs c' vet : ℝ), 1 ≤ ep → 1 ≤ T → 0 ≤ c' → 0 ≤ vet → ν ≤ νs + c' * vet →
    let e : ℤ := ⌈(T : ℝ) * (νs + 1)⌉
    ((max 0 ⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) / ep ≤ T * c' * vet

def LevelsSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (ep f : ι → ℕ) (mm : ι → ℤ) (v : ι → ℝ) (T : ℕ) (c' : ℝ),
    (∀ z, (mm z : ℝ) ≤ ep z * T * c' * v z) →
      ∑ z, (mm z : ℝ) * f z ≤ T * c' * ∑ z, ((ep z : ℝ) * f z) * v z

end Formalism.LatticeBaseChangeAlt
