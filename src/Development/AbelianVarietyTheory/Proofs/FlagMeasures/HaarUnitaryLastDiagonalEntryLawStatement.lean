module

public import Formalism.PeriodIntegrals.QuotInv
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryLastDiagonalEntryLaw
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.haarUnitary_lastDiagonalEntry_law : ∀ (k : ℕ) (μ : Measure (PI.MtM (k + 1))), 1 ≤ k → PI.IsHaarOnM (UH (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) μ → μ Set.univ = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} = ENNReal.ofReal (t ^ k) := by
  first | exact @GlobalTheory.Amp.EntryLaw.measure_entry | exact GlobalTheory.Amp.EntryLaw.measure_entry | (intros; apply GlobalTheory.Amp.EntryLaw.measure_entry <;> assumption)
