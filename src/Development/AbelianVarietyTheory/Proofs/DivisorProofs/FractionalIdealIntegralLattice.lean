module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardQuotientBound
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.fractional_ideal_integral_lattice : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ I : Set (v.adicCompletion ℚ ⊗[ℚ] L), 0 ∈ I →
      (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ, IsIntB v ℓ ρ → ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x, IsIntB v ℓ x → (D : v.adicCompletion ℚ ⊗[ℚ] L) * x ∈ I) ∧
        ∀ x ∈ I, IsIntB v ℓ ((D : v.adicCompletion ℚ ⊗[ℚ] L) * x)) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, ∀ x, x ∈ I ↔ ∃ ρ, IsIntB v ℓ ρ ∧ x = ↑m * ρ := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (exact GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually  <;> assumption)
