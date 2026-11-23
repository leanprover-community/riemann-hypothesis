module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemSmulTopOfNeatLevel
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

open NumberField

theorem _root_.GlobalTheory.T.sub_mem_smul_top_of_neat_level_alt : ∀ (E : Type) [Field E] [NumberField E] (La Λ Q : Type) [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Q] [Module (𝓞 E) Q] (J : Ideal (𝓞 E)) (n N m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)) (ev : La →ₗ[𝓞 E] Q) (ψ : Λ →ₗ[𝓞 E] Q) (θ : Q →ₗ[𝓞 E] Q) (F : Λ →ₗ[𝓞 E] Λ) (gM : La →ₗ[𝓞 E] La), Module.Finite (𝓞 E) Λ → Module.IsTorsionFree (𝓞 E) Λ → 0 < n → (n : 𝓞 E) ∈ J → (∀ a, ev a = 0 ↔ a ∈ J • (⊤ : Submodule (𝓞 E) La)) → (∀ q : Q, (∀ c ∈ J, c • q = 0) → ∃ a, ev a = q) → (∀ b, ψ b = 0 ↔ ∃ b', b = n • b') → (∀ q : Q, n • q = 0 → ∃ b, ψ b = q) → (∀ b, ψ (F b) = θ (ψ b)) → (∀ a, θ (ev (gM a)) = ev a) → 0 < N → F ^ N = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → J ≤ I₁ → J ≤ I₂ → (∀ x, ((gM - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) La)) → (∀ x, ((gM - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) La)) → ∀ a, gM a - a ∈ J • (⊤ : Submodule (𝓞 E) La) := by
  first | exact @GlobalTheory.sub_mem_smul_top_of_neat_level | exact GlobalTheory.sub_mem_smul_top_of_neat_level | (intros; apply GlobalTheory.sub_mem_smul_top_of_neat_level <;> assumption)
