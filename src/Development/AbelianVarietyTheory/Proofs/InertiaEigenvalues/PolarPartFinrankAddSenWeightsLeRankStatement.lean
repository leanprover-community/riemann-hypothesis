module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarPartFinrankAddSenWeightsLeRank
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

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.polarPart_finrank_add_senWeights_le_rank : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (ψ : ZMod n → V →ₗ[k] V) (ψ0 : k⸨X⸩ →ₗ[k] k⸨X⸩), (∀ i a x, ψ i (a • D.φ i x) = ψ0 a • x) → (∀ a b, ψ0 (R.φ a * b) = a * ψ0 b) → ψ0 1 = 1 → (∀ i x, ψ i (D.γ i x) = D.γ (i - 1) (ψ i x)) → (∀ a : ℤ, 2 - (l : ℤ) ≤ a → a ≤ 1 → ψ0 '' {x | ∃ b : k⟦X⟧, x = vv k ^ a * (b : k⸨X⸩)} = Set.range (fun b : k⟦X⟧ => (b : k⸨X⸩))) → ∀ (i : ZMod n) (N₀ N : Submodule k⟦X⟧ V) (ws s : ℕ) (w : ℤ), IsLat N₀ → IsLat N → CondC (D.γ (i - 1)) N₀ → CondC (D.γ i) N → 1 ≤ ws → ws + 7 ≤ l → sh ws N ≤ pull (D.φ i) N₀ → pull (D.φ i) N₀ ≤ sh (-w) N → (ws : ℤ) + 2 ≤ l * (s + 3) - w → (∀ a : ℕ, a ≤ s + 1 → sen (D.γ (i - 1)) N₀ (a : k) = 0) → (∀ y ∈ sh (1 - ws) (pull (D.φ i) N₀), ψ i y = 0 → ∃ x ∈ sh (-ws) (pull (D.φ i) N₀), ψ i x = 0 ∧ D.γ i x - x = y) → (∀ x ∈ N, (∃ m : ℕ, ((nab (D.γ i)) ^ m) x ∈ sh (ws + 1) N) → nab (D.γ i) x ∈ sh (ws + 1) N) → ∀ Z : Submodule k V, (∀ x ∈ Z, x ∈ sh (-ws) (pull (D.φ i) N₀) ∧ D.γ i x - x ∈ sh (ws + 2) N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) + ∑ a ∈ Finset.range (ws + 1), sen (D.γ i) N (a : k) ≤ Module.finrank k⸨X⸩ V := by
  first | exact @GlobalTheory.PhiGam.PolarCount.main | exact GlobalTheory.PhiGam.PolarCount.main | (intros; apply GlobalTheory.PhiGam.PolarCount.main <;> assumption)
