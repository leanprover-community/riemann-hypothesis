module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelOneThetaNeZeroOnIdealHalfLattice
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

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate Classical

theorem _root_.GlobalTheory.T.exists_levelOne_theta_ne_zero_on_ideal_half_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ (w : E) (L : Lt E r), SelfD X L → ∀ x ∈ X.dom, ∀ (𝔪 : Ideal (𝓞 E)) (M : ℕ), 2 ≤ M → 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)} → ∀ ϑ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L ϑ → ϑ ≠ 0 → ∃ u ∈ 𝔪 • L, ϑ (pv X idx x ((M : E)⁻¹ • u)) ≠ 0 := by
  first | exact @GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half | exact GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half | (intros; apply GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half <;> assumption)
