module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralClosurePlaceRingsData
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

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_pow_section_associated_global_element : ∀ (F Ω X : Type) [Field F] [NumberField F] [Field Ω] (φ : F →+* Ω) (R : X → Subring Ω) (s : X → Ω) (pl : X → Option (HeightOneSpectrum (𝓞 F))) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ x, ∀ z : Ω, IsIntegral (R x) z → z ∈ R x) → (∀ x, pl x = none → (∀ a : F, φ a ∈ R x) ∧ s x ∈ R x ∧ s x ≠ 0 ∧ (s x)⁻¹ ∈ R x) → (∀ x v, pl x = some v → (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ R x) ∧ ∃ (m : ℕ) (n : ℤ) (π : F), 0 < m ∧ (n : ℚ) = m * r v ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ s x ≠ 0 ∧ s x ^ m / φ π ^ n ∈ R x ∧ φ π ^ n / s x ^ m ∈ R x) → ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧ v.valuation F α = WithZero.exp (-n)) ∧ ∀ x, s x ^ M / φ α ∈ R x ∧ φ α / s x ^ M ∈ R x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_global_generator | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_global_generator | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_global_generator <;> assumption)
