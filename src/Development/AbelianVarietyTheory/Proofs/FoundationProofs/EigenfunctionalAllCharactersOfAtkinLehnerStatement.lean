module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenfunctionalAllCharactersOfAtkinLehner
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eigenfunctionalAllCharacters_of_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c → ∃ (B' : ℕ) (c' : ℕ → ℂ), EigAll k N l χ g (χ l * α) B' c' ∧ ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a' := by
  first | exact @GlobalTheory.EisM.eigAll_of_atkinLehner | exact GlobalTheory.EisM.eigAll_of_atkinLehner | (intros; apply GlobalTheory.EisM.eigAll_of_atkinLehner <;> assumption)
