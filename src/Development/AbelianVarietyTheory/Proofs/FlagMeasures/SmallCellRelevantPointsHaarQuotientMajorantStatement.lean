module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallCellRelevantPointsHaarQuotientMajorant
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

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem _root_.GlobalTheory.T.smallCell_relevant_points_haar_quotient_majorant : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GlobalTheory.CellAmp.GapCell k r h → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)) (ν : MeasureTheory.Measure (Formalism.MainNotions.S.PairSp k r)), Formalism.MainNotions.S.ThB.Gpt (Formalism.QuantumDeterminants.Tz k r L.z) (Formalism.QuantumDeterminants.Tz k r L.z') γ ≠ 0 → Formalism.MainNotions.S.IsPtRep L γ g → Formalism.MainNotions.S.IsRelStab L g → Formalism.MainNotions.S.IsRootMeas L γ g μR → Formalism.MainNotions.S.IsOrbQuot L g μR ν → IsHaarOn (Formalism.MainNotions.S.RStab k r g) μR ∧ (∃ νR : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (g⁻¹ * Matrix.of x * g) i j)) νR) ∧ ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ MeasureTheory.Integrable (GlobalTheory.CellAmp.pairMaj g b) ν := by
  first | exact @GlobalTheory.CellPts.cell_points | exact GlobalTheory.CellPts.cell_points | (intros; apply GlobalTheory.CellPts.cell_points <;> assumption)
