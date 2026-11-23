module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.KCountable
public import Formalism.PeriodIntegrals.AdUnimod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularIndex.PairwiseDisjointCosets
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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

namespace PI.WAU

open Formalism.MainNotions.S MeasureTheory Matrix Pointwise

theorem kg_one_eq (I : AutInst) : I.Kg 1 = I.Kset := by
  ext x
  refine ⟨fun h => h.1, fun h => ⟨h, fun y hy => ⟨(I.fmat x - 1) *ᵥ y, ?_, by simp⟩⟩⟩
  have h' : ∀ y, y ∈ I.Lf ↔ I.fmat x *ᵥ y ∈ I.Lf := h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem ((h' y).1 hy) hy

theorem kset_open (I : AutInst) : IsOpen I.Kset := by
  rw [← kg_one_eq]
  exact I.topf_open 1 le_rfl

theorem ksub_coe (I : AutInst) : ((Ksub I : Subgroup I.Gf) : Set I.Gf) = I.Kset := rfl

theorem sigmaFinite_of_K (I : AutInst) (μ : Measure I.Gf) (hμ : μ.IsHaarMeasure)
    (hKc : IsCompact I.Kset) (hQ : ∃ s : Set I.Gf, s.Countable ∧ ∀ x : I.Gf, ∃ y ∈ s, y⁻¹ * x ∈ I.Kset) :
    SigmaFinite μ := by
  haveI := hμ
  obtain ⟨s, hs, hcov⟩ := hQ
  refine Measure.sigmaFinite_of_countable (S := (fun y => (fun x => y * x) '' I.Kset) '' s)
    (hs.image _) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    show μ ((fun x => y * x) '' I.Kset) < ⊤
    rw [Set.image_mul_left, measure_preimage_mul]
    exact hKc.measure_lt_top
  · rw [Set.sUnion_image, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨y, hy, hyx⟩ := hcov x
    exact Set.mem_biUnion hy ⟨y⁻¹ * x, hyx, mul_inv_cancel_left y x⟩

theorem adUnimod_of (hA : KgSubgroup) (hC : KCompact) (hQ : KCountable) (hI : IndexEq) :
    PI.AdUnimod := by
  intro I μ hμ
  haveI := sigmaFinite_of_K I μ hμ (hC I) (hQ I)
  choose U hU using fun n : ℕ => hA I (n + 1) (by omega)
  refine PI.UnimodIdxWork.unimodIdx_main I.Gf μ hμ U (fun n => ?_) (fun V hV => ?_) (Ksub I) ?_ ?_ (hI I)
  · rw [hU n]
    exact I.topf_open (n + 1) (by omega)
  · obtain ⟨g, hg1, hgV⟩ := I.topf_basis V hV
    refine ⟨g - 1, ?_⟩
    rw [hU (g - 1), show g - 1 + 1 = g by omega]
    exact hgV
  · rw [ksub_coe]
    exact kset_open I
  · rw [ksub_coe]
    exact hC I

end PI.WAU
