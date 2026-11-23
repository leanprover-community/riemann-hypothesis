module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductValueNeZeroOfDepleted
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.muModelProduct_value_ne_zero_of_depleted : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ⁻¹ (fun n => conj (g n)) → α + β = χ l * conj (g l) → α * β = χ l * (l : ℂ) ^ (2 * e) → α ≠ 0 → θ (-1) = (-1) ^ e * ψ (-1) → θ * χ⁻¹ ≠ 1 → ∀ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ (fun q => χ q * conj (g q)) α B c → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ⁻¹)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 → ∀ (B' : ℕ) (c' : ℕ → ℂ), (∀ a a', MF (2 * e + 1) (N * l) (ch χ⁻¹) a → MF (2 * e + 1) (N * l) (ch χ) a' → qs a' = slz (2 * e + 1) !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a') → (∀ a, MF (2 * e + 1) (N * l) (ch χ⁻¹) a → lam B' c' (Uo l a) = χ⁻¹ l * α * lam B' c' a) → val B' c' l (χ⁻¹ l * α) 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ⁻¹)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.zm_val_ne_zero | exact GlobalTheory.zm_val_ne_zero | (intros; apply GlobalTheory.zm_val_ne_zero <;> assumption)
