module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormSymmBilinEqSumLiftsOdd
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PolFan GlobalTheory.LocM

theorem _root_.GlobalTheory.T.linForm_symmBilin_eq_sum_lifts_odd : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin n → ZMod N) → ℤ), 0 < D ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ cl, ν cl * b (μ cl) (μ cl) := by
  first | exact @GlobalTheory.Poinc.linForm_eq_sum_lifts | exact GlobalTheory.Poinc.linForm_eq_sum_lifts | (intros; apply GlobalTheory.Poinc.linForm_eq_sum_lifts <;> assumption)
