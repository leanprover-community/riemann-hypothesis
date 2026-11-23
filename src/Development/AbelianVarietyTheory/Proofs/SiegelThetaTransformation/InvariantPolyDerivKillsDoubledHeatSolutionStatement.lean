module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolyDerivKillsDoubledHeatSolution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.invariant_polyDeriv_kills_doubled_heat_solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), r ≤ n → InvFam P → ∀ D : CM X.Ψ r r → CM X.Ψ n r → CM X.Ψ n r → ℂ, IsHeat X.Ψ D → (∀ Z ∈ Hn X.Ψ r, D Z 0 0 = 0) → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, biDeriv X hr idx P (fun z₁ w => kZero X idx x₁ x₂ z₁ w * D (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) = 0 := by
  first | exact @GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | exact GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | (intros; apply GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero <;> assumption)
