module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Lemma
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

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal

private lemma UpperTheory.V.Af.Rs.unfM_mp (γ : SL(2, ℤ)) :
    MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
  have : (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z := rfl
  rw [this]
  exact measurePreserving_smul _ _

theorem UpperTheory.V.Af.Rs.unfM :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.FdCount → UpperTheory.V.Af.Rs.UnfM := by
  intro hFin hCount
  unfold UpperTheory.V.Af.Rs.UnfM
  unfold UpperTheory.V.Af.Rs.FdFin at hFin
  unfold UpperTheory.V.Af.Rs.FdCount at hCount
  obtain ⟨hfdm, -⟩ := hFin
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  ext s hs
  rw [Measure.sum_apply _ hs]
  have step : ∀ γ : SL(2, ℤ), Measure.map (fun z : ℍ => γ • z) (volume.restrict ModularGroup.fd) s
      = ∫⁻ z in s, ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z) := by
    intro γ
    have hm : Measurable (fun z : ℍ => γ • z) := (UpperTheory.V.Af.Rs.unfM_mp γ).measurable
    have hm' : Measurable (fun z : ℍ => γ⁻¹ • z) := (UpperTheory.V.Af.Rs.unfM_mp γ⁻¹).measurable
    have hP : MeasurableSet ((fun z : ℍ => γ⁻¹ • z) ⁻¹' ModularGroup.fd) := hm' hfdm
    rw [Measure.map_apply hm hs, Measure.restrict_apply (hm hs)]
    have hind : (fun z : ℍ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z))
        = ((fun z : ℍ => γ⁻¹ • z) ⁻¹' ModularGroup.fd).indicator 1 := by
      ext z
      by_cases h : γ⁻¹ • z ∈ ModularGroup.fd
      · rw [indicator_of_mem h, indicator_of_mem (show z ∈ _ from h)]
        rfl
      · rw [indicator_of_notMem h, indicator_of_notMem (show z ∉ _ from h)]
    rw [hind, lintegral_indicator_one hP, Measure.restrict_apply hP,
      ← (UpperTheory.V.Af.Rs.unfM_mp γ).measure_preimage (hP.inter hs).nullMeasurableSet]
    congr 1
    ext z
    simp only [mem_preimage, mem_inter_iff, inv_smul_smul]
    exact and_comm
  rw [tsum_congr step]
  have hmeas : ∀ γ : SL(2, ℤ), AEMeasurable
      (fun z : ℍ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z))
      (volume.restrict s) := fun γ =>
    ((measurable_const.indicator hfdm).comp (UpperTheory.V.Af.Rs.unfM_mp γ⁻¹).measurable).aemeasurable
  rw [← lintegral_tsum hmeas]
  have hre : ∀ z : ℍ, ∑' γ : SL(2, ℤ), ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z)
      = ∑' γ : SL(2, ℤ), ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ • z) :=
    fun z => (Equiv.inv SL(2, ℤ)).tsum_eq
      (fun γ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ • z))
  simp_rw [hre]
  rw [lintegral_congr_ae (ae_restrict_of_ae hCount), setLIntegral_const, Measure.smul_apply]
  first
    | rw [two_mul, two_nsmul]
    | rw [smul_eq_mul]
    | simp [two_mul, two_smul]
