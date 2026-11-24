module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakProperties
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

open MeasureTheory Matrix Filter Topology

theorem _root_.GlobalTheory.T.unitaryRealTraceBump_peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧ (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧ ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1, ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  first | exact @GlobalTheory.KFinAvg.peak_properties | exact GlobalTheory.KFinAvg.peak_properties | (intros; apply GlobalTheory.KFinAvg.peak_properties <;> assumption)
