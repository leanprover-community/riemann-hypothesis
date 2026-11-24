module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω), 0 < N → HasQ N f (fun n => ε (a n)) → ∃ h : HahnSeries ℚ Ω, IsExp ε f h ∧ (∀ k : ℕ, h.coeff ((k : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ (k : ℚ) / N) → h.coeff r = 0 := by
  first | exact @GlobalTheory.fn_hahnSeries_of_hasQ | exact GlobalTheory.fn_hahnSeries_of_hasQ | (intros; apply GlobalTheory.fn_hahnSeries_of_hasQ <;> assumption)
