module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLaws
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

theorem _root_.GlobalTheory.T.mulq_dbl_cubN_relations : ∀ (O : Type) [CommRing O] (B : NumB O) (a b : ℕ) (x y : B.A), mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) ∧ mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y * (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) ∧ dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) = dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 ∧ mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) := by
  first | exact @GlobalTheory.Ex.mulq_laws | exact GlobalTheory.Ex.mulq_laws | (intros; apply GlobalTheory.Ex.mulq_laws <;> assumption)
