module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPow
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.integers_eq_sum_zeta_pow_unique : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (i : ℕ), 2 ≤ i → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ i) → (∀ x : Om l, x ∈ Ks K i → ‖x‖ ≤ 1 → ∃ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1) ∧ ‖y a‖ ≤ 1) ∧ x = ∑ a : Fin l, ζ ^ (a : ℕ) * y a) ∧ ∀ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1)) → ∑ a : Fin l, ζ ^ (a : ℕ) * y a = 0 → ∀ a, y a = 0 := by
  first | exact @GlobalTheory.Cyc.integers_eq_sum_zeta_pow | exact GlobalTheory.Cyc.integers_eq_sum_zeta_pow | (intros; apply GlobalTheory.Cyc.integers_eq_sum_zeta_pow <;> assumption)
