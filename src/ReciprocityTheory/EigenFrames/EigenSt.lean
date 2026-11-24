module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators
open NumberField

namespace ReciprocityTheory.EigenFramesTheory

universe u v


open Classical in
def EigenFrameDual : Prop := by
  classical
  exact
    ∀ (p : ℕ) [Fact p.Prime] (E : Type u) [Field E] [NumberField E] (κ : Type v) [Fintype κ]
      (b : Module.Basis κ ℤ (𝓞 E)) (ι : ℂ ≃+* ℂ_[p]), ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ τ₀ : E →+* ℂ, ∃ r : κ → ℂ_[p], (∀ i, ‖r i‖ ≤ 1) ∧
      ∀ φ : E →+* ℂ, ∑ i, r i * ι (φ ((b i : 𝓞 E) : E)) = if φ = τ₀ then 1 else 0

end ReciprocityTheory.EigenFramesTheory
