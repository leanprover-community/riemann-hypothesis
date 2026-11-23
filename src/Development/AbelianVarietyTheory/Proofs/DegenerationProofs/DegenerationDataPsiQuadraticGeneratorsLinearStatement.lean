module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinear
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
theorem _root_.GlobalTheory.T.degenerationData_psi_quadratic_generators_linear : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n : ℕ) (y : N.X), N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) ∧ N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) ∧ ∀ (g : N.Gt), g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n ∧ (g ^ n).s y * cubN N.θ n 1 g.b (N.c y) = g.s y ^ n := by
  first | exact @GlobalTheory.PsiQuadratic.main | exact GlobalTheory.PsiQuadratic.main | (intros; apply GlobalTheory.PsiQuadratic.main <;> assumption)
