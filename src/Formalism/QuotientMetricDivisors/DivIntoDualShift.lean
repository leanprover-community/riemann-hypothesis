module

public import Formalism.QuotientMetricDivisors.Statement
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

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def smulLat {d : ℕ} (a : K) (N : Submodule (𝓞 K) (Fin d → K)) : Submodule (𝓞 K) (Fin d → K) :=
  N.map ((LinearMap.lsmul K (Fin d → K) a).restrictScalars (𝓞 K))

def IsShiftAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ) :
    Prop :=
  ∃ a : K, a ≠ 0 ∧ vw w a = -s ∧
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N)

def IsShift {d : ℕ} (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℤ) : Prop :=
  ∀ w, IsShiftAt w N N' (σ w)

def shiftIdeal (σ : HeightOneSpectrum (𝓞 K) → ℤ) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-σ w)

end Defs

def ShiftIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N N' : Submodule (𝓞 K) (Fin d → K)), Submodule.IsFullLattice K N →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (s : ℤ), IsShiftAt w N N' s →
      idx w N N' = -((d : ℤ) * s)

def MuLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ N : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K N →
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N = -(lcv X N) / d

def ShiftMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ N N' : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K N → Submodule.IsFullLattice K N' →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, IsShift N N' σ →
      lcv X N' = lcv X N - 2 * (d : ℝ) * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ) ∧
      (0 < d → (Function.support σ).Finite ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' =
          Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
            2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ))

def ShiftEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N : Submodule (𝓞 K) (Fin d → K)), Submodule.IsFullLattice K N →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, (Function.support σ).Finite →
      IsShift N (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) σ ∧
      Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) ∧
      ∀ N' : Submodule (𝓞 K) (Fin d → K), IsShift N N' σ →
        N' = Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N

def ShiftPairing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ), IsShiftAt w N N' s →
    ∀ f : (Fin d → K) →ₗ[K] K, (∀ φ ∈ N, f φ = 0 ∨ s ≤ vw w (f φ)) →
      ∀ φ ∈ N', f φ = 0 ∨ 0 ≤ vw w (f φ)

def DivIntoDualShift : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d D : ℕ)
    (R : Submodule (𝓞 K) (Fin D → K)) (B : (Fin d → K) →ₗ[K] (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (ι : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin d → K) →ₗ[K] (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K),
    (∀ w, ζ w ≠ 0) → (∀ w, vw w (ζ w) = 0) →
    (∀ w (φ : Fin d → K) (F : Fin (n w) → K),
      P w φ F = ζ w * B φ ((ι w).mulVec ((π w).mulVec F))) →
    ∀ (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℝ)
      (τ : HeightOneSpectrum (𝓞 K) → ℤ),
    (∀ w, ∀ φ ∈ N, ∀ F ∈ M w, P w φ F = 0 ∨ σ w ≤ (vw w (P w φ F) : ℝ)) →
    (∀ w, τ w ≤ ⌈σ w⌉) → IsShift N N' τ →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι w) (matLat (π w) (M w)))) →
    ∀ φ ∈ N', ∀ x ∈ R, B φ x ∈ Set.range (algebraMap (𝓞 K) K)

end Formalism.DivisionValues
