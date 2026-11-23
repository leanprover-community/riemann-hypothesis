module

public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainLemmaMultivariatePowerSeriesCoordinateForm
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

open ReciprocityTheory.PGsh

theorem _root_.GlobalTheory.T.chainLemma_multivariatePowerSeries_coordinate_form : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 3 ≤ l → ∀ (d M s₀ : ℕ) (good : Set (Fin d)) (Gs : ℕ → Finset (Fin d)) (al : Fin d → ℕ → Fin d → C) (π : ℕ → Fin d → Fin M → C)
    (t : Fin d → MvPowerSeries (Fin M) C), (∀ s c, c ∈ Gs s → c ∈ good) → (∀ s s' c, s ≤ s₀ → s' ≤ s₀ → c ∈ Gs s → c ∈ Gs s' → s = s') →
    (∀ c e, al c 0 e = if c = e then 1 else 0) → (∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ c ∈ good, al c 1 = 0 ∧ ∀ (n : ℕ) e, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) →
    (∀ s < s₀, ∀ c ∈ Gs s, ∀ e, e ∉ Gs (s + 1) → 0 ≤ v (al c 2 e)) →
    (∀ c j, 0 ≤ v (π 0 c j)) → (∀ c, c ∉ Gs 0 → π 0 c = 0) →
    (∀ s e j, π (s + 1) e j = ∑ c ∈ Gs s, (l : C) * al c 2 e * π s c j ^ (l ^ 2)) →
    (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ e, lgSum l al t e = ∑ j, MvPowerSeries.C (R := C) (π 0 e j) * MvPowerSeries.X j) →
    (∀ s ≤ s₀, ∀ c ∈ Gs s, OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c - ∑ j, MvPowerSeries.C (R := C) ((-1) ^ s * ((l : C) ^ (∑ u ∈ Finset.range s, (l ^ 2) ^ u))⁻¹ * π s c j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ ((l ^ 2) ^ s)) (1 + 1 / ((l : ℝ) ^ 2 - 1))) ∧
    ∀ c, (∀ s ≤ s₀, c ∉ Gs s) → OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1))) (t c) (1 + 1 / ((l : ℝ) ^ 2 - 1))) := by
  first | exact @GlobalTheory.ChainCoord.chain | exact GlobalTheory.ChainCoord.chain | (intros; apply GlobalTheory.ChainCoord.chain <;> assumption)
