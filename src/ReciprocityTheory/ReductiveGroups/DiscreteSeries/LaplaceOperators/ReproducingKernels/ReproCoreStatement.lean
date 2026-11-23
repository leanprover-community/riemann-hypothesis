module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
public import Formalism.HermitianCurvature.StatementB
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0

open Formalism.QuantumDeterminants

def nS (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

def q0S (k r : ℕ) : ℝ := ((min (k + r) (r + 1) : ℕ) : ℝ)

def bG (k r : ℕ) : ℝ := 2 * nS k r * q0S k r

def bS (k r : ℕ) : ℝ := 2 * (r : ℝ) * nS k r ^ 2

section Fdeg

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsFdegB (μG : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g : Mt k r => ⟪w, σ (Matrix.of g) v⟫_ℂ * star ⟪w', σ (Matrix.of g) v'⟫_ℂ) μG ∧
    ∫ g : Mt k r, ⟪w, σ (Matrix.of g) v⟫_ℂ * star ⟪w', σ (Matrix.of g) v'⟫_ℂ ∂μG =
      ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

end Fdeg

def IntSStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN →
    ∀ x₀ ∈ UH (Hpk k r), ∀ x ∈ UH (Hpk k r), ∀ b : ℝ, bS k r < b →
      Integrable (fun p : Mt k r × Mt k r =>
        Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b)) (μW.prod μN)

end ReciprocityTheory.ChartRestriction.DS.Lap.S0
