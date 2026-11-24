module

public import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodIntegerPlanLowLevelsBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

theorem _root_.GlobalTheory.T.exists_goodIntegerPlan_low_levels_bound : ∀ (l d : ℕ) [NeZero d], 5 ≤ l → ∀ (n m k S : ℕ), 1 ≤ n → 1 ≤ k → ∀ (W : ZMod d → ℕ) (Ws : ZMod d → ℝ) (Good : ZMod d → ℕ → Set ℕ),
  (∀ a, 0 ≤ Ws a ∧ Ws a ≤ W a) → (∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows S (Good a i)) →
  ∃ p : Plan l d W, (∀ a i, i0 k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → p.y a i ∈ Good a i) ∧
    p.bound n m ≤ Fnum l d (fun a => (n : ℝ) * Ws a) + thl k l * n * (∑ a, Ws a) + n * gam l * (∑ a, ((W a : ℝ) - Ws a)) +
      m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) + 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) + d * (i0 k l : ℝ) * (n * ((S : ℝ) + Real.logb l n + 1)) := by
  first | exact @GlobalTheory.GoodPlan.exists_plan | exact GlobalTheory.GoodPlan.exists_plan | (intros; apply GlobalTheory.GoodPlan.exists_plan <;> assumption)
