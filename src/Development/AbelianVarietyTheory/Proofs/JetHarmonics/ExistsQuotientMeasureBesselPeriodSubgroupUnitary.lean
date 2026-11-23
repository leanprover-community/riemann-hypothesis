module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaarStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeilStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodularStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_isQuotMeas_bessel_subgroup : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    PI.BesselPeriodGGP.IsHaarOn (GG k r) μG →
    ∃ νq, PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq := by
  intro k r z μW μN μG hz hT hW hN hG
  obtain ⟨hGgrp, hGinv⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  obtain ⟨hGhaar, _⟩ := hGinv μG hG
  obtain ⟨hSgrp, hSsub, hShaar, hSright⟩ := GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN
  exact GlobalTheory.T.exists_quotientMeasure_weil (2 * r + k + 1) (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN)
    hGgrp hSgrp hSsub hGhaar hShaar hSright

end GlobalTheory
