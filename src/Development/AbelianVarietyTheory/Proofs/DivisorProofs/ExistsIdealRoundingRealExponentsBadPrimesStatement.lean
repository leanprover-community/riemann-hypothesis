module

public import Formalism.LocalRingCardinality.DataArith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealRoundingRealExponentsBadPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

theorem _root_.GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes : ∀ (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ), (∀ p ∈ B, p.Prime) → (Function.support ρ).Finite → (∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) → ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧ (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧ (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤ -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.Rounding.exists_rounding | exact GlobalTheory.Rounding.exists_rounding | (intros; apply GlobalTheory.Rounding.exists_rounding <;> assumption)
