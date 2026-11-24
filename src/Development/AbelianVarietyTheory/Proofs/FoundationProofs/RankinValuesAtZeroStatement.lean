module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinValuesAtZero
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

theorem _root_.GlobalTheory.T.pet_eis_lat_eq_and_vo_eq_mul : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (c₀ : ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ g → Wt (N * l) ρ → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → φ ≠ 1 → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → ∃ P : ℂ, P ≠ 0 ∧ pet (2 * e + 1) ρ (qs fun n => conj (g n)) (fun τ => qs (eis e c₀ (ch ψ) (ch θ)) τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) = P ∧ pet (2 * e + 1) ρ (qs (Vo l fun n => conj (g n))) (fun τ => qs (eis e c₀ (ch ψ) (ch θ)) τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) = θ l / (l : ℂ) ^ (2 * e) * P := by
  first | exact @GlobalTheory.EisM.rankin_values_at_zero | exact GlobalTheory.EisM.rankin_values_at_zero | (intros; apply GlobalTheory.EisM.rankin_values_at_zero <;> assumption)
