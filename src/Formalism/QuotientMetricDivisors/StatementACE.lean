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
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

def StepA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (n D : ℕ) (M : Submodule (𝓞 K) (Fin n → K)) (π : Matrix (Fin D) (Fin n) K)
    (ι : Matrix (Fin D) (Fin D) K)
    (B : (Fin D → K) →ₗ[K] K) (P : (Fin n → K) →ₗ[K] K) (ζ : K) (σ : ℤ),
    ζ ≠ 0 → vw w ζ = 0 →
    (∀ F : Fin n → K, P F = ζ * B (ι.mulVec (π.mulVec F))) →
    (∀ F ∈ M, P F = 0 ∨ σ ≤ vw w (P F)) →
    ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ι (matLat π M)), B x = 0 ∨ σ ≤ vw w (B x)

def BoundsSum : Prop :=
  ∀ (Pl J : Type) [Fintype J] (S : Finset Pl) (D : ℕ), 0 < D →
    ∀ (lcvR logκ LG E3 : ℝ) (lcvM L E1 E2 : J → ℝ) (l ell vG g : Pl → ℝ)
      (I Ic jT F err Jx η : Pl → J → ℝ),
    (∀ w, 0 ≤ l w) →
    lcvR ≤ (D : ℝ) * logκ + ∑ j, lcvM j +
      ∑ w ∈ S, l w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) →
    (∀ w ∈ S, vG w ≤ (D : ℝ) * g w) → ∑ w ∈ S, l w * g w ≤ LG →
    (∀ j, lcvM j / D ≤ L j) →
    (∀ w ∈ S, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ S, ∀ j, jT w j ≤ Jx w j * D + η w j) →
    (∀ j, ∑ w ∈ S, l w * (err w j + Jx w j) ≤ E1 j) →
    (∀ j, ∑ w ∈ S, l w * η w j / D ≤ E2 j) →
    ∑ w ∈ S, l w * (2 / ell w ^ 2) ≤ E3 →
      lcvR / D ≤ logκ + ∑ j, L j + 2 * ∑ j, ∑ w ∈ S, l w * F w j + LG + ∑ j, (E1 j + E2 j) + E3

end Formalism.DivisionValues
