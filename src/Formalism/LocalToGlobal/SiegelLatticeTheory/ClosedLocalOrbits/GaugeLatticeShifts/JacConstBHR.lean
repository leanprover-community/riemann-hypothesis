module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHB
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

open MeasureTheory Filter Topology Classical
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def rhoS (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (x : Mt k r) : ℝ≥0∞ :=
  ⨅ (Y : Formalism.MainNotions.S.lieE S)
    (_ : (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x),
    (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)

def Qf (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : ℝ≥0∞ :=
  rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + rhoS k r (Formalism.FourierDecayAlt.B2.UWb k r) m ^ 2 +
    rhoS k r (Nset k r) n' ^ 2

def Psi (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : Mt k r :=
  fun i j => (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) i j

def Sandwich : Prop :=
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ Formalism.FourierDecayAlt.B2.UWb k r →
      Matrix.of n' ∈ Nset k r →
      (Psi k r n c m n' ∈ gBall k r ρ → Qf k r n c m n' < ENNReal.ofReal (((1 + ε) * ρ) ^ 2)) ∧
      (Qf k r n c m n' < ENNReal.ofReal (((1 - ε) * ρ) ^ 2) → Psi k r n c m n' ∈ gBall k r ρ)

def Vol (k r : ℕ) (μb : Measure (Mt k r)) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
    ∫⁻ n, ∫⁻ m, ∫⁻ n', (if Qf k r n c m n' < ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0)
      ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1)

def VolLim : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    Tendsto (fun s : ℝ => (Vol k r μb s).toReal / gVol k r s) (𝓝[>] 0) (𝓝 ((2 : ℝ) ^ r)⁻¹)

end Formalism.L2.SG.Pf.BH
