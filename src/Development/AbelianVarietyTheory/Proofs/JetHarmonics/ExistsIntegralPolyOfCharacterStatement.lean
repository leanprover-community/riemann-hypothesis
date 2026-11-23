module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolyOfCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt

@[expose] public section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_integral_poly_of_character' : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (G : Type) [AddCommGroup G] [Fintype G] (x χ : G → K), Function.Injective x → (∀ i j, χ (i + j) = χ i * χ j) → (∀ k : Fin (Fintype.card G), ∃ c : Fin (Fintype.card G) → Fin (Fintype.card G) → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ i j, x (i + j) ^ (k : ℕ) = ∑ a, ∑ b, c a b * x i ^ (a : ℕ) * x j ^ (b : ℕ)) → ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ i, g.eval (x i) = χ i := by
  exact @GlobalTheory.ConvSer.exists_integral_poly_of_character
