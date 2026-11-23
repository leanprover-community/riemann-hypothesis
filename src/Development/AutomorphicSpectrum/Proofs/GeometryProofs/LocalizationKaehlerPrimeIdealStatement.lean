module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationKaehlerPrimeIdeal
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


theorem _root_.GlobalTheory.T.localization_kaehler_prime_ideal : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type)
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (bd : Ideal (MvPolynomial σ ℤ)) (S : Subalgebra ℚ Ω₀) (S' : Subalgebra ℚ Ω) (θ : S →+* S'),
    (∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s) → (∀ p, r₀ p ∈ S) → (∀ p, r₁ p ∈ S') →
    ∀ q : Ideal S',
    ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
      (∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q.comap θ)) := by
  exact @GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff
