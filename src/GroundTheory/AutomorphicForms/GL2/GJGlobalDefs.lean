module

public import GroundTheory.AutomorphicForms.Reduction
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def ratMat (ξ : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) 𝔸[K] :=
  ξ.map (algebraMap K 𝔸[K])

theorem ratMat_mul (ξ η : Matrix (Fin n) (Fin n) K) : ratMat (ξ * η) = ratMat ξ * ratMat η :=
  Matrix.map_mul

theorem coe_diagonal (γ : GL (Fin n) K) :
    ((AdelicGLn.diagonal K n γ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ratMat (γ : Matrix (Fin n) (Fin n) K) := by
  ext i j
  rw [AdelicGLn.diagonal_apply]
  rfl

variable (μ : Measure (normOneGL (K := K) (n := n)))

def matrixCoeff (φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ x in fundamentalDomain (rationalGLOne (K := K) (n := n)), φ₁ ((x : AdelicGLn.AdelicGL K n) * g) *
    conj (φ₂ (x : AdelicGLn.AdelicGL K n)) ∂μ

def detPow (g : AdelicGLn.AdelicGL K n) (s : ℂ) : ℂ :=
  ((detModule K n g : ℝ) : ℂ) ^ s

def zetaIntegrand (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (f : AdelicGLn.AdelicGL K n → ℂ) (s : ℂ)
    (g : AdelicGLn.AdelicGL K n) : ℂ :=
  Φ (g : Matrix (Fin n) (Fin n) 𝔸[K]) * f g * detPow g (s + ((n : ℂ) - 1) / 2)

def globalZeta (ν : Measure (AdelicGLn.AdelicGL K n)) (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (f : AdelicGLn.AdelicGL K n → ℂ) (s : ℂ) : ℂ :=
  ∫ g, zetaIntegrand Φ f s g ∂ν

def thetaPairing (φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ) (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ x in fundamentalDomain (rationalGLOne (K := K) (n := n)), ∫ y in fundamentalDomain (rationalGLOne (K := K) (n := n)),
    conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
      ∑' γ : GL (Fin n) K, Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n)) ∂μ ∂μ

end GJGlobal

end

end GroundTheory.Automorphic
