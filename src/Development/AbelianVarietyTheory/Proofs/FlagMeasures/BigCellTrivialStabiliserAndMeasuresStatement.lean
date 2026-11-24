module

public import Formalism.PeriodIntegrals.BesselPeriodGGP
public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellTrivialStabiliserAndMeasures
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

theorem _root_.GlobalTheory.T.bigCell_trivialStabiliser_and_measures : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ Formalism.MainNotions.S.IsRelStab L (Formalism.QuantumDeterminants.bigCell k r c μ) ∧ IsHaarOn (Formalism.MainNotions.S.RStab k r (Formalism.QuantumDeterminants.bigCell k r c μ)) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) ∧ Formalism.MainNotions.S.IsOrbQuot L (Formalism.QuantumDeterminants.bigCell k r c μ) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) (Formalism.MainNotions.S.pairMeas L) ∧ PI.BesselPeriodGGP.IsQuotMeas μG ((MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)).map (fun x => fun i j => ((Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ * Matrix.of x * Formalism.QuantumDeterminants.bigCell k r c μ) i j)) μG := by
  first | exact @GlobalTheory.AmpTK.bigCell_data | exact GlobalTheory.AmpTK.bigCell_data | (intros; apply GlobalTheory.AmpTK.bigCell_data <;> assumption)
