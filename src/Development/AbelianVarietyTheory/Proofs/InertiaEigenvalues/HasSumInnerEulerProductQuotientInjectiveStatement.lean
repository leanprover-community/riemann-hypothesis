module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerEulerProductQuotientInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.hasSum_inner_eulerProduct_quotient_injective : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) [DecidableEq ι] (c : ι → Γ →* Γ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (s : ι → ℝ) (e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}), (∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) → (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 → (∀ g, a g = ∏ᶠ v, a (c v g)) → (∀ g, ‖B g‖ ≤ 1) → B 1 = 1 → (∀ g k, k ∈ K → B (g * k) = B g) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset Γ), (∀ g ∈ C, c v g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ s v) → (∀ v γ, HasSum (fun x : Γ ⧸ K.comap (c v) => a (c v (Quotient.out x)) • B (γ * c v (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap (c v), a (c v (Quotient.out x)) • B (c v (Quotient.out x)))) → ∃ W : H →L[ℂ] H, Function.Injective W ∧ ∀ x y, HasSum (fun q : Γ ⧸ K => a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ) ⟪x, W y⟫_ℂ := by
  first | exact @GlobalTheory.hasSum_inner_quotient_eulerProduct_injective | exact GlobalTheory.hasSum_inner_quotient_eulerProduct_injective | (intros; apply GlobalTheory.hasSum_inner_quotient_eulerProduct_injective <;> assumption)
