module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonneg
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

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W), (∀ A, GoodSub W0 A S → cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A) ∧ (∀ A A', GoodSub W0 A S → A' ≤ A → A'.relIndex A ≠ 0 → GoodSub W0 A' S) ∧ 0 ≤ cont W0 S ∧ (IsCO W0 S → S.Nonempty → 0 < cont W0 S) := by
  first | exact @GlobalTheory.HL.cont_independent_pos | exact GlobalTheory.HL.cont_independent_pos | (intros; apply GlobalTheory.HL.cont_independent_pos <;> assumption)
