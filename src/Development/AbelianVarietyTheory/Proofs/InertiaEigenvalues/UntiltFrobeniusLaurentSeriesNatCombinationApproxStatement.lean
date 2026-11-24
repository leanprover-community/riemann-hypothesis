module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesNatCombinationApprox
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_natCombination_approx : ∀ (l : ℕ) [Fact l.Prime] (h j d : ℕ) (r : ℝ) (x : Fin d → Fl l) (n : Fin d → ℕ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ a, ‖sh (x a)‖ ≤ r) → ‖sh (∑ a, n a • x a)‖ ≤ r ∧ ‖lam h j (∑ a, n a • x a) - ∑ a, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  first | exact @GlobalTheory.PSer.lamsum | exact GlobalTheory.PSer.lamsum | (intros; apply GlobalTheory.PSer.lamsum <;> assumption)
