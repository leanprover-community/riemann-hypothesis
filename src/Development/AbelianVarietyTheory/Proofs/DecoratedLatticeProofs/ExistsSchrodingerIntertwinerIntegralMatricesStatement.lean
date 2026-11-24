module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchrodingerIntertwinerIntegralMatrices
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

open ValuativeRel GlobalTheory.SplitWeil Matrix

theorem _root_.GlobalTheory.T.exists_schrodinger_intertwiner_integralMatrices : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Z : Type) [AddCommGroup Z] (χ : Matrix Y Y' k → Z → ℂ), (∀ a b z, χ (a + b) z = χ a z * χ b z) → (∀ a z z', χ a (z + z') = χ a z * χ a z') → (∀ z, χ 0 z = 1) → (∀ a, χ a 0 = 1) → (∀ n : ℕ, 0 < n → ∀ z : Z, ∃ z' : Z, n • z' = z) → (∀ n : ℕ, 0 < n → Function.Injective fun z : Z => n • z) → (∀ x : Matrix Y Y' k, (∀ z, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → χ x z = 1) → ∀ r q, x r q ∈ 𝒪[k]) → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Matrix Y Y' k → M →ₗ[ℂ] M) (μ : Z → M →ₗ[ℂ] M), (∀ x x' f, τ x (τ x' f) = τ (x + x') f) → (∀ z z' f, μ z (μ z' f) = μ (z + z') f) → (∀ x z f, τ x (μ z f) = χ x z • μ z (τ x f)) → (∀ f, τ 0 f = f) → (∀ f, μ 0 f = f) → ∀ f₀ : M, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → τ u f₀ = f₀) → (∀ z, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → μ z f₀ = f₀) → ∃ Tm : SB (Matrix Y Y' k) →ₗ[ℂ] M, (∀ (x : Matrix Y Y' k) (Φ Φ' : SB (Matrix Y Y' k)), (∀ t, Φ'.1 t = Φ.1 (t + x)) → Tm Φ' = τ x (Tm Φ)) ∧ (∀ (z : Z) (Φ Φ' : SB (Matrix Y Y' k)), (∀ t, Φ'.1 t = χ t z * Φ.1 t) → Tm Φ' = μ z (Tm Φ)) ∧ (∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → Tm Φ = f₀) ∧ ∀ Φ, Tm Φ ∈ Submodule.span ℂ (Set.range fun w : Matrix Y Y' k × Z => τ w.1 (μ w.2 f₀)) := by
  first | exact @GlobalTheory.SchrodExist.exists_intertwiner_matrix | exact GlobalTheory.SchrodExist.exists_intertwiner_matrix | (intros; apply GlobalTheory.SchrodExist.exists_intertwiner_matrix <;> assumption)
