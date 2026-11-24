module

public import Formalism.RealPlaceAnalysis.StatementE
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Matrix

namespace UpperTheory.V.Weyl

structure Pre (n : ℕ) where

  d : ℕ

  mat : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ
  poly : ∀ i j, ∃ p : MvPolynomial (Fin n × Fin n) ℂ, ∀ g, mat g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p

variable {n : ℕ}

def Pre.coef (Ξ : Pre n) (i j : Fin Ξ.d) (x : Fin n → Fin n → ℂ) : ℂ := Ξ.mat (Matrix.of x) i j

abbrev oneM (n : ℕ) : Fin n → Fin n → ℂ := Matrix.of.symm 1

def Pre.D (Ξ : Pre n) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun X := Matrix.of fun i j => fderiv ℂ (Ξ.coef i j) (oneM n) (Matrix.of.symm X)
  map_add' X Y := by ext i j; exact map_add (fderiv ℂ (Ξ.coef i j) (oneM n)) X Y
  map_smul' c X := by ext i j; exact map_smul (fderiv ℂ (Ξ.coef i j) (oneM n)) c X

def Pre.E (Ξ : Pre n) (a b : Fin n) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ := Ξ.D (Matrix.single a b 1)

def Pre.HasWt (Ξ : Pre n) (ν : Fin n → ℂ) : Prop :=
  ∀ u : ℂ, Formalism.REAL.qdet Ξ.E u = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def Pre.IsTop (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ) : Prop :=
  ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → Ξ.mat b *ᵥ v = (∏ k, b k k ^ ν k) • v

abbrev Pol (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) ℂ

def rtr (g : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n :=
  MvPolynomial.aeval fun ij => ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (g k ij.2)

def minor (k : Fin n) : Pol n :=
  (Matrix.of fun i j : Fin (k + 1) =>
    (MvPolynomial.X (Fin.castLE k.2 i, Fin.castLE k.2 j) : Pol n)).det

end UpperTheory.V.Weyl
