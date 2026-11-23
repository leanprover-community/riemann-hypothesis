module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
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
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

def ClosedSubgroupsStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ),
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (UH (Hpk k r)) ∧
      Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (Nset k r) ∧
      (inWb k r z → 0 < Tz k r z →
        Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (UWset k r z) ∧
          Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (Sset k r z))

def HaarUniq2Statement : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ ν : Measure (Mt k r)),
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) U →
    Formalism.MainNotions.S.IsHaarOn U μ → Formalism.MainNotions.S.IsHaarOn U ν → ∃ c : ℝ≥0, 0 < c ∧ ν = c • μ

def HaarMapStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P →
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r))
      ((Formalism.REAL.muG ε).map (fun g : Formalism.REAL.UJ ε => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)))

def SchurBStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (μG : Measure (Mt k r)),
    Formalism.MainNotions.S.IsDSHpk k r ε lam σ → Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG →
    Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ ∧ ∃ d : ℝ, S0.IsFdegB μG σ d

end ReciprocityTheory.ChartRestriction.DS.Lap
