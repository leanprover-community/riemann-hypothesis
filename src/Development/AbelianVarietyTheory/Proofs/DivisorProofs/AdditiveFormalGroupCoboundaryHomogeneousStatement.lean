module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneous
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

theorem _root_.GlobalTheory.T.additive_formal_group_coboundary_homogeneous : ∀ (R : Type) [CommRing R] (d N : ℕ), (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ (cob1 (addLaw R d) f) = 0) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≠ N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≠ N → coeff γ (cob2 (addLaw R d) c) = 0) ∧ (∀ (c : MvPowerSeries (Fin d ⊕ Fin d) R) (γ : Fin d ⊕ Fin d →₀ ℕ), coeff γ (swap c) = coeff (γ.mapDomain Sum.swap) c) ∧ ∀ (f : MvPowerSeries (Fin d) R) (β : Fin d →₀ ℕ) (i : Fin d), β ≠ 0 → coeff (β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) (cob1 (addLaw R d) f) = ((β i + 1 : ℕ) : R) * coeff (β + Finsupp.single i 1) f := by
  first | exact @GlobalTheory.homog_cob_addLaw | exact GlobalTheory.homog_cob_addLaw | (intros; apply GlobalTheory.homog_cob_addLaw <;> assumption)
