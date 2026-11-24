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
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def ProdFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a : K), a ≠ 0 →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)).Finite ∧
    (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ =
      ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w a : ℝ)

def DetCS : Prop :=
  ∀ (n D : ℕ) (Hc : Matrix (Fin n) (Fin n) ℂ), Hc.PosDef →
    ∀ A B : Matrix (Fin D) (Fin n) ℂ,
      ‖(A * Hc * Bᴴ).det‖ ^ 2 ≤ (A * Hc * Aᴴ).det.re * (B * Hc * Bᴴ).det.re

def LcvBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
        lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)).Finite ∧
      lcv X L = (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (gram X v e).det.re +
        2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)

def IdxChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (L : Submodule (𝓞 K) (Fin d → K)), Submodule.IsLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (γ : Matrix (Fin d) (Fin d) K),
      IsLocBasis L w (fun i => ∑ k, γ k i • e k) →
      idx w (Submodule.span (𝓞 K) (Set.range e)) L = vw w γ.det ∧
      idx (conjPl w) (Submodule.span (𝓞 K) (Set.range e)) L = vw (conjPl w) γ.det

def ValBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ a b : K, a ≠ 0 → b ≠ 0 → vw w (a * b) = vw w a + vw w b) ∧
    (∀ a : K, vw w (star a) = vw (conjPl w) a) ∧
    lw (conjPl w) = lw w ∧ conjPl (conjPl w) = w ∧ vw w 1 = 0 ∧
    (∀ a : K, vw w a⁻¹ = - vw w a) ∧
    (∀ a : 𝓞 K, 0 ≤ vw w (a : K))

def GramChange : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (D m : ℕ) (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) (γ : Matrix (Fin m) (Fin m) K),
      gramR Γ (fun i => ∑ k, γ k i • e k) = star γ.det * γ.det * gramR Γ e

def ImageLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (XS v).det) →
    (∀ v, IsUnit (XT v).det) →
    ∀ φ : Matrix (Fin d) (Fin d) K, IsUnit φ.det →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K L →
      lcv XT (matLat φ L) = lcv XS L + (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (detRatio XS XT φ v)

def IdxLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A B : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K A → Submodule.IsFullLattice K B →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)).Finite ∧
      lcv X B = lcv X A + 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w A B : ℝ)

def RatHermLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K T →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (jw H w T : ℝ)).Finite ∧
      lcv X T = - ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (jw H w T : ℝ)

def JwGram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K), IsLocBasis T w f →
      jw H w T = - vw w (gramR H f)

def FinsumConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (f : HeightOneSpectrum (𝓞 K) → ℝ),
    ∑ᶠ w, f (conjPl w) = ∑ᶠ w, f w

def LocBasisEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (L : Submodule (𝓞 K) (Fin d → K)),
    Submodule.IsFullLattice K L → ∀ w : HeightOneSpectrum (𝓞 K), ∃ f : Fin d → Fin d → K, IsLocBasis L w f

end Formalism.DivisionValues
