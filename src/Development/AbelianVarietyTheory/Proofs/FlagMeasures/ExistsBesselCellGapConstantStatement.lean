module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstant
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

theorem _root_.GlobalTheory.T.exists_besselCell_gap_constant : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  first | exact @GlobalTheory.GapConstant.gap_constant_exists | exact GlobalTheory.GapConstant.gap_constant_exists | (intros; apply GlobalTheory.GapConstant.gap_constant_exists <;> assumption)
