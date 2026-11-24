module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
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

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.Lin

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def degL (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) : RP Ψ N →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ dimFl Ψ N) •
    ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (permExp σ)

theorem degL_apply (F : RP Ψ N) : degL Ψ N F = degFl F := by
  simp only [degL, degFl, LinearMap.smul_apply, LinearMap.sum_apply, MvPolynomial.lcoeff_apply,
    smul_eq_mul]

def shL (j : ℕ) (τ : Ψ) : RP Ψ N →ₗ[ℝ] ℝ :=
  (degL Ψ N).comp (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
    (pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)).toLinearMap)

theorem shL_apply (j : ℕ) (τ : Ψ) (F : RP Ψ N) : shL j τ F = Sh j τ F := by
  rw [shL, LinearMap.comp_apply, degL_apply, Sh]
  congr 1
  simp

def totL (τ : Ψ) : RP Ψ N →ₗ[ℝ] ℝ :=
  (degL Ψ N).comp (∑ i : Fin N, (pderiv (τ, i) : Derivation ℝ (RP Ψ N) (RP Ψ N)).toLinearMap)

theorem totL_apply (τ : Ψ) (F : RP Ψ N) : totL τ F = Tot τ F := by
  rw [totL, LinearMap.comp_apply, degL_apply, Tot]
  congr 1
  simp

end RootFieldNumerics.Lin
