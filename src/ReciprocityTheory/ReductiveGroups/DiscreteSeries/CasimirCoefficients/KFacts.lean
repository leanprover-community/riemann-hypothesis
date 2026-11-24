module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFactsA
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

instance kf_isHaar (ε : Fin n → Bool) : (muK ε).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

theorem compactSpace_KG (ε : Fin n → Bool) : CompactSpace (KG ε) := by
  have hc : IsCompact (Kset ε) := by
    have hsub : Kset ε ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
        (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) := by
      intro g hg i _ j _
      simpa [Metric.mem_closedBall, dist_zero_right] using entry_norm_bound_of_unitary hg.1 i j
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_Kset ε) hsub
  have hK : IsCompact ((KG ε : Set (UJ ε))) :=
    (isClosedEmbedding_toM ε).isCompact_preimage hc
  exact isCompact_iff_compactSpace.mp hK

theorem muK_univ_pos (ε : Fin n → Bool) : 0 < (muK ε Set.univ).toReal := by
  have := compactSpace_KG ε
  exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero (muK ε) Set.univ_nonempty)
    (isCompact_univ.measure_lt_top (μ := muK ε)).ne

theorem muK_rightInvariant (ε : Fin n → Bool) : (muK ε).IsMulRightInvariant := by
  have := compactSpace_KG ε
  refine ⟨fun k => ?_⟩
  set ν := Measure.map (fun x => x * k) (muK ε) with hν
  have : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (muK ε)
  have hu : ν Set.univ = muK ε Set.univ := by
    rw [hν, Measure.map_apply (measurable_mul_const k) MeasurableSet.univ, Set.preimage_univ]
  have hpos : muK ε Set.univ ≠ 0 := (isOpen_univ.measure_pos (muK ε) Set.univ_nonempty).ne'
  have htop : muK ε Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  rw [h, smul_apply, ENNReal.smul_def, smul_eq_mul] at hu
  have hc : (Measure.haarScalarFactor ν (muK ε) : ℝ≥0∞) = 1 := by
    have := (ENNReal.mul_eq_right hpos htop).mp hu
    exact this
  rw [h, ENNReal.coe_eq_one.mp hc, one_smul]

theorem exists_oneParam (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    ∃ γ : ℝ → KG ε, Continuous γ ∧ (∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) ∧
      ∀ s t, γ (s + t) = γ s * γ t := by
  exact ⟨kfaKG ε hY, kfa_continuous ε hY, kfa_toMK ε hY, kfa_add ε hY⟩

end ReciprocityTheory.ChartRestriction.DS.S7
