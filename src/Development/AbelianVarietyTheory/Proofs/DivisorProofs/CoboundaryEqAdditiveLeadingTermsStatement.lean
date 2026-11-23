module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTerms
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.coboundary_eq_additive_leading_terms : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (N : ℕ), (∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (addLaw R d i)) → (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, (γ.degree < N → coeff γ (cob1 μ f) = 0) ∧ (γ.degree ≤ N → coeff γ (cob1 μ f) = coeff γ (cob1 (addLaw R d) f))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≤ N → coeff γ (cob2 μ c) = coeff γ (cob2 (addLaw R d) c) := by
  first | exact @GlobalTheory.CobLead.cob_eq_additive_lead | exact GlobalTheory.CobLead.cob_eq_additive_lead | (intros; apply GlobalTheory.CobLead.cob_eq_additive_lead <;> assumption)
