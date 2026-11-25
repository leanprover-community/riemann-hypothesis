module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CohBoundFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWeylC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section




section
theorem UpperTheory.V.Af.card_k_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.CardK := by
  intro P K _ _ _ n hn
  obtain ⟨c₁, A₁, hW⟩ := _root_.UpperTheory.V.Af.weyl_complex_of_printed_results P K n
  obtain ⟨c₂, A₂, hC⟩ := UpperTheory.V.Af.cohBoundFree K (Or.inl inferInstance) n ⊤ inferInstance
  refine ⟨c₂ * c₁, A₁ + A₂, fun m hm H hH M hM S hS hiso => ?_⟩
  obtain ⟨Ξ, hΞ, hd⟩ := hW m hm H hH
  have h3 : 1 ≤ 3 * M := by omega
  have hB := P.borelC K n (by omega) (UpperTheory.V.Af.KLev K n (3 * M)) (by apply UpperTheory.V.Af.isOpen_KLev; exact h3)
    (by apply UpperTheory.V.Af.isCompact_KLev; exact h3) Ξ S hiso fun π hπ =>
      ⟨P.cohC K n (by omega) π Ξ fun τ => ⟨_, (hS π hπ).1 τ, hΞ τ⟩,
        (hS π hπ).2.2.imp fun _ hv =>
          ⟨hv.1, fun u hu => hv.2 u (UpperTheory.V.Af.KLev_le_of_dvd (dvd_mul_left M 3) hu)⟩⟩
  have h1 : S.card ≤ c₂ * M ^ A₂ * Ξ.d := Nat.cast_le.1 (hB.trans (hC M hM _ _))
  have h2 : M ^ A₂ ≤ M ^ (A₁ + A₂) := Nat.pow_le_pow_right hM (by omega)
  have h4 : (H + 1) ^ A₁ ≤ (H + 1) ^ (A₁ + A₂) := Nat.pow_le_pow_right (by omega) (by omega)
  calc S.card ≤ c₂ * M ^ A₂ * Ξ.d := h1
    _ ≤ c₂ * M ^ (A₁ + A₂) * (c₁ * (H + 1) ^ (A₁ + A₂)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) (hd.trans (Nat.mul_le_mul_left _ h4))
    _ = c₂ * c₁ * (M * (H + 1)) ^ (A₁ + A₂) := by rw [mul_pow]; ring
end
