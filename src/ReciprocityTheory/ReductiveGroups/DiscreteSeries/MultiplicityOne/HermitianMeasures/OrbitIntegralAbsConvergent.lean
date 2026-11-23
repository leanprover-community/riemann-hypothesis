module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

def dimN (k r : ℕ) : ℕ := r * (2 * r + 2 * k + 1)

def bS (k r : ℕ) : ℝ := ((2 * r + k : ℕ) : ℝ) * (dimN k r : ℝ)

def SIntFin : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN →
    ∀ b : ℝ, bS k r < b →
      (∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)) ∂(μW.prod μN)) < ∞ ∧
      (∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) ∂(μW.prod μN)) < ∞

variable {k r : ℕ}

theorem bS_le (k r : ℕ) : bS k r ≤ 2 * (r : ℝ) * ReciprocityTheory.ChartRestriction.DS.Mult1.nR k r ^ 2 := by
  have h : (2 * r + k) * (r * (2 * r + 2 * k + 1)) ≤ 2 * r * (2 * r + k + 1) ^ 2 := by
    nlinarith [Nat.zero_le (r * r * r), Nat.zero_le (r * r * k), Nat.zero_le (r * k * k), Nat.zero_le (k * k * k),
      Nat.zero_le (r * r), Nat.zero_le (r * k), Nat.zero_le (k * k), Nat.zero_le r, Nat.zero_le k]
  unfold bS dimN ReciprocityTheory.ChartRestriction.DS.Mult1.nR
  exact_mod_cast h

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0
