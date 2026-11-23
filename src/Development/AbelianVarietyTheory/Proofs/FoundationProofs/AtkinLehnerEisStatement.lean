module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerEis
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

theorem _root_.GlobalTheory.T.exists_ne_zero_slz_qs_eis_eq_smul : ∀ (j N l : ℕ) (ω : DirichletCharacter ℂ l) (ν : DirichletCharacter ℂ N) (c₁ c₂ : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ j → 0 < N → l.Prime → ¬ l ∣ N → MF j (N * l) (fun d => ch ω d * ch ν d) (eis j c₁ (ch ω) (ch ν)) → MF j (N * l) (fun d => ch ω d * ch ν⁻¹ d) (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) → ∃ κ : ℂ, κ ≠ 0 ∧ slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (eis j c₁ (ch ω) (ch ν))) = κ • qs (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) := by
  first | exact @GlobalTheory.EisAL.atkin_lehner_eis | exact GlobalTheory.EisAL.atkin_lehner_eis | (intros; apply GlobalTheory.EisAL.atkin_lehner_eis <;> assumption)
