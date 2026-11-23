module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FunctionalValuesNonempty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Lemma
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

noncomputable section
open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.LeastExponentCompare
open scoped Pointwise

namespace GlobalTheory.LeastExponentProbe

variable {E : Type} [Field E] [NumberField E] {cj : E → E}
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def vals (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ,
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    (∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

theorem phiC_def (b : SymB cj Y) : phiC cj b = sInf (vals b) := rfl

private lemma vals_eq_functionalValues [IsCMField E] (b : SymB cj Y) : vals b = functionalValues b := by
  ext x
  constructor
  · rintro ⟨l, h1, h2, hx⟩
    exact ⟨l, ⟨h1, h2⟩, hx⟩
  · rintro ⟨l, ⟨h1, h2⟩, hx⟩
    exact ⟨l, h1, h2, hx⟩

section CM

variable [IsCMField E] [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem one_le_phiC (h : IsConj cj) (b : SymB cj Y)
    (hint : ∀ a c, ∃ z : ℤ, (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z)
    (hpos : ∀ a, 0 ≤ (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) (h0 : b ≠ 0) : 1 ≤ phiC cj b := by
  rw [phiC_def]
  refine le_csInf (by rw [vals_eq_functionalValues]; exact functionalValues_nonempty h b) ?_
  rintro x ⟨l, h1, h2, rfl⟩
  obtain ⟨z, hz⟩ := h1 b hint
  have hp := h2 b hpos h0
  rw [hz] at hp ⊢
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hp
  exact_mod_cast (show (1 : ℤ) ≤ z by omega)

end CM

end GlobalTheory.LeastExponentProbe

end
