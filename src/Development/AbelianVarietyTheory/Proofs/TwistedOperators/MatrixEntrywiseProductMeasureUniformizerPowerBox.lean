module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.BoxVolume

theorem prod_zpow_nnreal {ι : Type} (d : ℝ≥0) (hd : d ≠ 0) (f : ι → ℤ) (s : Finset ι) :
    ∏ i ∈ s, d ^ f i = d ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hd]

theorem volM_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [Fintype D] (c : A → D → ℤ),
    volM ν A D {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} =
      ν (𝒪[k] : Set k) ^ (Fintype.card A * Fintype.card D) *
        ENNReal.ofReal ((resCard k : ℝ) ^ (-∑ i, ∑ j, c i j)) := by
  intro k _ _ _ _ _ _ ν _ ϖ hϖ A D _ _ c
  haveI := secondCountable k
  haveI := t2Space k
  have hset : ({y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} :
      Set (A → D → k)) = Set.univ.pi fun i => Set.univ.pi fun j => cball (ϖ ^ c i j) := by
    ext y
    simp only [Set.mem_univ_pi, cball, Set.mem_setOf_eq, Units.val_zpow_eq_zpow_val]
    rfl
  set d : ℝ≥0 := distribHaarChar k ϖ with hd
  have hdq : (d : ℝ) = (resCard k : ℝ)⁻¹ := nabs_unif hϖ
  have hd0 : d ≠ 0 := (distribHaarChar_pos (A := k) (g := ϖ)).ne'
  have hcb : ∀ i j, ν (cball (ϖ ^ c i j)) = ((d ^ c i j : ℝ≥0) : ℝ≥0∞) * ν (𝒪[k] : Set k) := by
    intro i j
    rw [measure_cball, map_zpow]
  rw [volM]
  erw [hset, Measure.pi_pi]
  simp_rw [Measure.pi_pi, hcb, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (ν _ ^ _)]
  rw [Nat.mul_comm (Fintype.card D)]
  congr 1
  have hz : ∏ i, ∏ j, d ^ c i j = d ^ (∑ i, ∑ j, c i j) := by
    simp_rw [prod_zpow_nnreal d hd0]
  have hz' : (∏ i, ∏ j, ((d ^ c i j : ℝ≥0) : ℝ≥0∞)) =
      ((d ^ (∑ i, ∑ j, c i j) : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast hz
  rw [hz', ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_zpow, hdq, _root_.inv_zpow']

end GlobalTheory.BoxVolume
