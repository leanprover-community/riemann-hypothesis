module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerIntertwinesHeckeOperators
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.atkinLehner_intertwines_hecke_operators : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a a' : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (To k (ch χ q) q a)) = (ch χ q : ℂ) • qs (To k (ch χ⁻¹ q) q a')) ∧ slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (Uo l a)) = (ch χ l : ℂ) • qs (Uo l a') := by
  first | exact @GlobalTheory.EisM.AtkinLehner.alHecke | exact GlobalTheory.EisM.AtkinLehner.alHecke | (intros; apply GlobalTheory.EisM.AtkinLehner.alHecke <;> assumption)
