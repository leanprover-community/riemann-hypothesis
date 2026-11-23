module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.NIntStep
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem nIntAt_zero (hNB : NBase) (k : ℕ) : NIntAt k 0 := by
  intro μN hH b _
  have hc := hH.conc
  rw [hNB k] at hc
  have hae : ∀ᵐ x ∂μN, x ∈
      ({(show Mt k 0 from (1 : Matrix (Fin (2 * 0 + k + 1)) (Fin (2 * 0 + k + 1)) ℂ))} : Set (Mt k 0)) := by
    rw [ae_iff]
    exact hc
  rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_singleton]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hH.finite_compact _ isCompact_singleton)

theorem nIntAt_all (hNB : NBase) (hNR : NRecHaar) (hHU : HaarUnique) (hCN : ClosedN) (hHN : HaarNExists)
    (hGL : GNLower) (k r : ℕ) : NIntAt k r := by
  induction r with
  | zero => exact nIntAt_zero hNB k
  | succ r' ih =>
    have h := nIntAt_step hNR hHU hCN hHN hGL k r' ih
    rwa [Nat.add_comm 1 r'] at h

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
