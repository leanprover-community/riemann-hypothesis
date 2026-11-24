module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset MvPolynomial Filter Topology

noncomputable section

namespace Formalism.ShimuraLimitIdentity

abbrev Pol (Ψ : Type) (N : ℕ) := MvPolynomial (Ψ × Fin N) ℝ

def top (N j : ℕ) : Finset (Fin N) := univ.filter (fun i : Fin N => i.val < j)

def psumAt {Ψ : Type} {N : ℕ} (τ : Ψ) (k : ℕ) : Pol Ψ N := ∑ i : Fin N, X (τ, i) ^ k

def Sh {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) (j : ℕ) (τ : Ψ) (F : Pol Ψ N) : ℝ :=
  I (∑ i ∈ top N j, pderiv (τ, i) F)

def Tot {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) (τ : Ψ) (F : Pol Ψ N) : ℝ :=
  I (∑ i : Fin N, pderiv (τ, i) F)

def Kills {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) : Prop :=
  ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → ∀ G : Pol Ψ N, I (psumAt τ k * G) = 0

end Formalism.ShimuraLimitIdentity
