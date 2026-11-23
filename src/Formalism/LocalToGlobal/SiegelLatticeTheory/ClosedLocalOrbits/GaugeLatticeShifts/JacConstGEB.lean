module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB

def RhsHaar : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    ∃ ν : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ν ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂ν = rhs k r μb φ

def RhsWHaar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    ∃ ν : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) ν ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂ν = rhsW k r z z' μW μW' μsec φ

def WbDataEx : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), WbData k r z z' μW μW' a a' μsec

def ExistsGaugeMeasureForEachRank : Prop := ∀ r : ℕ, ∃ μ : Measure (Mt 0 r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb 0 r) μ

end Formalism.L2.SG.Pf.GE
