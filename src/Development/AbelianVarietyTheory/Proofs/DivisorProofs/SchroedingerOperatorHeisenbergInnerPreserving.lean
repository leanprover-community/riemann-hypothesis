module

import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Linter.HaveILetI
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

open MeasureTheory Matrix

namespace GlobalTheory
open ValuativeRel

theorem norm_addChar_nonarch {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (t : k) : ‖ψ0 t‖ = 1 := by
  apply PositivityTheory.KCo.Mod.norm_one <;> assumption

theorem schr_unitary : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (μ : @Measure (κ → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ),
      ∫ y, GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ := by
  intro k _ _ _ _ _ ψ0 hψ κ _ μ hμ w φ φ'
  letI : MeasurableSpace (κ → k) := borel _
  haveI : BorelSpace (κ → k) := ⟨rfl⟩
  have h1 : ∀ s : k, ψ0 s * (starRingEnd ℂ) (ψ0 s) = 1 := fun s => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_addChar_nonarch ψ0 hψ s]; simp
  have h2 : (fun y => GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y)) =
      fun y => φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1)) := by
    funext y
    simp only [GlobalTheory.WeilM.schr, map_mul]
    have := h1 (y ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2))
    linear_combination (φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1))) * this
  rw [h2]
  exact integral_add_right_eq_self (fun y => φ y * (starRingEnd ℂ) (φ' y)) w.1

end GlobalTheory
