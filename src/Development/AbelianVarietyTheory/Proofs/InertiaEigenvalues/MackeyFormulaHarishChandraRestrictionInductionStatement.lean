module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MackeyFormulaHarishChandraRestrictionInduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.mackey_formula_harishChandra_restriction_induction : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d → ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → ∀ h₁ h₂, res c d (hcT a b Φ n) h₁ h₂ = ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b), hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁ := by
  first | exact @GlobalTheory.GLq.Mackey.mackey_formula | exact GlobalTheory.GLq.Mackey.mackey_formula | (intros; apply GlobalTheory.GLq.Mackey.mackey_formula <;> assumption)
