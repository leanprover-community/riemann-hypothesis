module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodularStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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

open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique

theorem normaliseQuotientClause : NormaliseQuotientClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH hG hH' dg _ ν _
  obtain ⟨⟨μ₀, hμ₀⟩, huniq⟩ := GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular G H hH hG hH'
  obtain ⟨dg₀, ⟨hdg₀, hF₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ₀ hμ₀
  set c : ℝ≥0 := haarScalarFactor dg dg₀ with hc
  have hcpos : 0 < c := haarScalarFactor_pos_of_isHaarMeasure dg dg₀
  have hdg : dg = c • dg₀ := isMulLeftInvariant_eq_smul dg dg₀
  have hR : IsInvariantRadon H (c • μ₀) := by
    haveI := hμ₀.finiteOnCompacts
    haveI := hμ₀.invariant
    refine ⟨?_, inferInstance, ⟨fun g s hs => ?_⟩⟩
    · intro h
      apply hμ₀.ne_zero
      have : c⁻¹ • (c • μ₀) = μ₀ := by
        rw [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
      rw [← this, h, smul_zero]
    · simp only [Measure.coe_nnreal_smul_apply]
      rw [SMulInvariantMeasure.measure_preimage_smul g hs]
  have hF : QuotientFormula H dg ν (c • μ₀) := by
    intro f hf
    obtain ⟨h1, h2⟩ := hF₀ f hf
    refine ⟨h1, ?_⟩
    rw [hdg, lintegral_smul_measure, lintegral_smul_measure, h2]
  refine ⟨c • μ₀, ⟨hR, hF⟩, ?_⟩
  rintro μ ⟨hμ, hμF⟩
  obtain ⟨d, -, hd⟩ := huniq _ _ hR hμ
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hKm : MeasurableSet (K : Set G) := K.isCompact.measurableSet
  have hfm : Measurable ((K : Set G).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hKm
  have e1 := (hF _ hfm).2
  have e2 := (hμF _ hfm).2
  rw [hd, lintegral_smul_measure, ← e1, lintegral_indicator_const hKm, one_mul] at e2
  have hpos : dg K ≠ 0 := (measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
  have hfin : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have hd1 : d = 1 := by
    have : (d : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]; exact e2.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).mp this
  rw [hd, hd1, one_smul]

end GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique
