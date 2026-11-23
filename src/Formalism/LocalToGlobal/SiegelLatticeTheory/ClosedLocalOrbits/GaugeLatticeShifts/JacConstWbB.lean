module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConst
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.WB

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def rhsW (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (φ : Mt k r → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ζ : ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.zWeight k (Tz k r z) (Tz k r z') ζ) *
    ∫⁻ h, ∫⁻ h', φ (fun i j => (Matrix.of h * Formalism.FourierDecayAlt.B2.embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW

def zeta0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : ℂ := ((2 * Real.sqrt (Tz k r z * Tz k r z') : ℝ) : ℂ)

def mBase (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Formalism.FourierDecayAlt.B2.embWb k r (μsec (zeta0 k r z z'))

def bBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) ρ

def mBall (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ρ : ℝ) :
    Set (Mt k r) :=
  {x | (fun i j => ((mBase k r z z' μsec)⁻¹ * Matrix.of x) i j) ∈ bBall k r ρ}

def bVol (k r : ℕ) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) ρ)).toReal

structure WbData (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop where
  k_pos : 1 ≤ k
  z_mem : inWb k r z
  z'_mem : inWb k r z'
  T_pos : 0 < Tz k r z
  T'_pos : 0 < Tz k r z'
  haarW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW
  haarW' : Formalism.MainNotions.S.IsHaarOn (UWset k r z') μW'
  a_pos : 0 < a
  a'_pos : 0 < a'
  massW : μW Set.univ = ENNReal.ofReal a
  massW' : μW' Set.univ = ENNReal.ofReal a'
  sec : IsSection k r z z' μsec

def RankGauge : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μb μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec → IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    ∃ C : NNReal, 0 < C ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ m, φ m ∂μb = (C : ℝ≥0∞) * rhsW k r z z' μW μW' μsec φ

def GaugeShiftW : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μb μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec → Formalism.MainNotions.S.IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → ∀ ρ : ℝ, 0 < ρ →
      MeasurableSet (mBall k r z z' μsec ρ) ∧ μb (mBall k r z z' μsec ρ) = μb (bBall k r ρ)

def RhsWLim : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    Tendsto (fun ρ : ℝ => (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ)
      (𝓝[>] 0) (𝓝 (wbConst k (Tz k r z) (Tz k r z') a a')⁻¹)

end Formalism.L2.SG.Pf.WB
