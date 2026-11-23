module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroup
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

open MeasureTheory

theorem _root_.GlobalTheory.T.eq_zero_of_integral_char_eq_zero_of_periodic_open : ∀ {H A : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure] [AddCommGroup A] (χ : A → H → ℂ), (∀ a s t, χ a (s + t) = χ a s * χ a t) → (∀ a, χ a 0 = 1) → (∀ t, χ 0 t = 1) → (∀ a b t, χ (a + b) t = χ a t * χ b t) → ∀ L : AddSubgroup H, IsOpen (L : Set H) → (∀ x, x ∉ L → ∃ a, (∀ l ∈ L, χ a l = 1) ∧ χ a x ≠ 1) → ∀ (φ : H → ℂ) (Kc : Set H), IsCompact Kc → (∀ t, t ∉ Kc → φ t = 0) → (∀ t, ∀ l ∈ L, φ (t + l) = φ t) → (∀ a, (∀ l ∈ L, χ a l = 1) → ∫ t, χ a t * φ t ∂μ = 0) → φ = 0 := by
  first | exact @GlobalTheory.fourier_uniqueness_of_openSubgroup | exact GlobalTheory.fourier_uniqueness_of_openSubgroup | (intros; apply GlobalTheory.fourier_uniqueness_of_openSubgroup <;> assumption)
