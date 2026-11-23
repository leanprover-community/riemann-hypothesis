module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRules
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

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ : Type), (∀ (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g) ∧ (∀ (f : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f g' → g = g') ∧ (∀ g : MvPowerSeries σ k, Red p (Katz.lift p g) g) ∧ (∀ (f f' : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f' g' → Red p (f + f') (g + g') ∧ Red p (f - f') (g - g')) ∧ (∀ (r : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)) g, Red p f g → Red p (r • f) (WittVector.constantCoeff r • g)) ∧ (∀ f : MvPowerSeries (σ) (Fr p k), f ∈ intBy p k σ p ↔ Red p f 0) ∧ (∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g) := by
  first | exact @GlobalTheory.Katz.red_rules | exact GlobalTheory.Katz.red_rules | (intros; apply GlobalTheory.Katz.red_rules <;> assumption)
