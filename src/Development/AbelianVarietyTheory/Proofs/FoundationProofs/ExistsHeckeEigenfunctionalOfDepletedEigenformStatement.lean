module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenform
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

theorem _root_.GlobalTheory.T.exists_heckeEigenfunctional_of_depletedEigenform : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  first | exact @GlobalTheory.EisM.eigF_of_prim | exact GlobalTheory.EisM.eigF_of_prim | (intros; apply GlobalTheory.EisM.eigF_of_prim <;> assumption)
