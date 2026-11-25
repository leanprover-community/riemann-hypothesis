module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
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

open MvPolynomial NumberField

namespace GlobalTheory.ChowHt

structure IsChowForm {k : Type} [Field k] {N : ℕ} (I : Ideal (MvPolynomial (Fin N) k)) (D δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) k) : Prop where

  homog : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f

  irred : Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f)

  zero_iff : ∀ u : Fin (D + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f = 0 ↔
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
      ∀ i, ∑ j, u (i, j) * y j = 0

def linSubst {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f : MvPolynomial (Fin B × Fin N) R) : MvPolynomial (Fin B × Fin n) R :=
  MvPolynomial.aeval (fun p : Fin B × Fin N => ∑ k, C (M p.2 k) * X (p.1, k)) f

def frameNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖(A⁻¹.mulVec x) i‖ ^ 2)

def formHeight {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) : ℝ :=
  ((∑ᶠ v : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linSubst w f))) +
    ∑ σ : F →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) +
      (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2)) / (Module.finrank ℚ F : ℝ)

def pointHeight {F : Type} [Field F] [NumberField F] {N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    {K : Type} [Field K] [NumberField K] [Algebra F K] (y : Fin N → K) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (∑ j, algebraMap F K (w j k) * y j))) +
    ∑ τ : K →+* ℂ, Real.log (Real.sqrt
      (∑ i, ‖∑ j, A (τ.comp (algebraMap F K)) j i * τ (y j)‖ ^ 2))) / (Module.finrank ℚ K : ℝ)

def ConjCompat {F : Type} [Field F] {N : ℕ} (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (σ : F →+* ℂ) (x : Fin N → ℂ),
    frameNorm (A ((starRingEnd ℂ).comp σ)) (fun j => (starRingEnd ℂ) (x j)) = frameNorm (A σ) x

end GlobalTheory.ChowHt
