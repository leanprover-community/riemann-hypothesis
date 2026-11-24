module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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

noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def expo (a : Ψ → Fin N → ℕ) (σ : Ψ → Equiv.Perm (Fin N)) : (Ψ × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => a x.1 (σ x.1 x.2))

def alt (a : Ψ → Fin N → ℕ) (G : RP Ψ N) : ℝ :=
  ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * G.coeff (expo a σ)

def rho : Ψ → Fin N → ℕ := fun _ c => N - 1 - (c : ℕ)

def bump (τ : Ψ) (c : Fin N) (k : ℕ) : Ψ → Fin N → ℕ :=
  fun τ' c' => N - 1 - (c' : ℕ) + if τ' = τ ∧ c' = c then k else 0

def lam (τ : Ψ) (k : ℕ) (G : RP Ψ N) : ℝ := ∑ c, alt (bump τ c k) G

def Maj (f : Polynomial ℝ) (c A : ℝ) : Prop := ∀ s : ℕ, |f.coeff s| ≤ c * A ^ s / (s.factorial : ℝ)

def gdet (e : Fin N → ℕ) (v : Fin N → Polynomial ℝ) : Polynomial ℝ :=
  Matrix.det (Matrix.of fun c b => Polynomial.C (((e c).factorial : ℝ)⁻¹) * v b ^ e c)

theorem degFl_eq (G : RP Ψ N) : degFl G = (-1) ^ dimFl Ψ N * alt rho G := rfl

theorem alt_add (a : Ψ → Fin N → ℕ) (F G : RP Ψ N) : alt a (F + G) = alt a F + alt a G := by
  simp [alt, mul_add, Finset.sum_add_distrib]

theorem alt_C_mul (a : Ψ → Fin N → ℕ) (r : ℝ) (G : RP Ψ N) : alt a (C r * G) = r * alt a G := by
  simp only [alt, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem alt_sum {ι : Type*} (a : Ψ → Fin N → ℕ) (s : Finset ι) (F : ι → RP Ψ N) :
    alt a (∑ i ∈ s, F i) = ∑ i ∈ s, alt a (F i) := by
  simp only [alt, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem lam_add (τ : Ψ) (k : ℕ) (F G : RP Ψ N) : lam τ k (F + G) = lam τ k F + lam τ k G := by
  simp [lam, alt_add, Finset.sum_add_distrib]

theorem lam_sum {ι : Type*} (τ : Ψ) (k : ℕ) (s : Finset ι) (F : ι → RP Ψ N) :
    lam τ k (∑ i ∈ s, F i) = ∑ i ∈ s, lam τ k (F i) := by
  simp only [lam, alt_sum]
  exact Finset.sum_comm

end RootFieldNumerics.M5
