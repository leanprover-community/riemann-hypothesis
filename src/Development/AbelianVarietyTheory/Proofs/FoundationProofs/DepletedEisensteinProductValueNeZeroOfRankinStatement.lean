module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedEisensteinProductValueNeZeroOfRankin
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

theorem _root_.GlobalTheory.T.depletedEisensteinProduct_value_ne_zero_of_rankin : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (t : ℕ → ℂ) (α c₀ c₁ : ℂ) (B : ℕ) (c : ℕ → ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → α ≠ 0 → EigF (2 * e + 1) N l χ⁻¹ t α B c → θ (-1) = (-1) ^ e * ψ (-1) → χ (-1) = -1 → θ * χ ≠ 1 → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → MF (e + 1) (N * l) (ch φ⁻¹) (eis (e + 1) c₁ (hat φ) fun _ => 1) → lam B c (mul (eis e c₀ (ch ψ) (ch θ)) (eis (e + 1) c₁ (hat φ) fun _ => 1)) ≠ 0 → α ≠ θ l → α ≠ (l : ℂ) ^ e * χ⁻¹ l → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.EisM.val_depleted_ne_zero | exact GlobalTheory.EisM.val_depleted_ne_zero | (intros; apply GlobalTheory.EisM.val_depleted_ne_zero <;> assumption)
