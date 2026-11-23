module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.AutomorphicForms.ReductionMahler
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplit
import GroundTheory.AutomorphicForms.Reduction
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.HaarSplit


open GroundTheory.Automorphic.Reduction in
theorem map_prod_eq_smul (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ha : 0 < a)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ := by
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph E a ha
  have hfun : (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e := by
    funext p
    exact (he p.1 p.2).symm
  rw [hfun]
  set m : Measure (GA E a) := Measure.map e (ν.prod volume) with hm
  have hemeas : Measurable e := e.continuous.measurable
  have hinv : m.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨y, s⟩, rfl⟩ := e.surjective g
    have hcomp : (fun x => e (y, s) * x) ∘ e = e ∘ Prod.map (fun x => y * x) (fun t => s + t) := by
      funext p
      obtain ⟨x, t⟩ := p
      simp only [Function.comp, Prod.map, he]
      rw [splitCentre_add, Subgroup.coe_mul]
      rw [mul_assoc, mul_assoc, ← mul_assoc (y : GA E a), ← splitCentre_comm, mul_assoc]
    have hpres : MeasurePreserving (Prod.map (fun x : normOneGL (K := E) (n := a) => y * x) (fun t : ℝ => s + t))
        (ν.prod volume) (ν.prod volume) :=
      (measurePreserving_mul_left ν y).prod (measurePreserving_add_left volume s)
    rw [hm, Measure.map_map (by fun_prop) hemeas, hcomp, ← Measure.map_map hemeas hpres.measurable, hpres.map_eq]
  have hfin : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    change Measure.map e.toMeasurableEquiv (ν.prod volume) K < ⊤
    rw [e.toMeasurableEquiv.map_apply]
    exact (e.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
  have hopen : m.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  have hhaar : m.IsHaarMeasure := { }
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure m μ
  refine ⟨(Measure.haarScalarFactor m μ : NNReal), ENNReal.coe_ne_zero.2 hc.ne', ENNReal.coe_ne_top, ?_⟩
  exact Measure.isMulLeftInvariant_eq_smul m μ

end GlobalTheory.CompanionTheory.HaarSplit
