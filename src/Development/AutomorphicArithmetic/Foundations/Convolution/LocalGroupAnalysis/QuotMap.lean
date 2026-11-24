module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal

theorem UpperTheory.ConvolutionTheory.G.quotMap_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotMap := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν hP μ' j' ν' hP' e y hμ hν F hF hinv
  obtain ⟨ρ0, -, hρ, -⟩ := hN G' T' μ' j' ν' hP'
  set ρ : G' → ℝ≥0∞ := fun g => (ρ0 g : ℝ≥0∞) with hρdef
  have hjc : Continuous j := hP.2.1.continuous
  have hj'c : Continuous j' := hP'.2.1.continuous
  have hec : Continuous e := e.continuous_toFun
  have hejc : Continuous (fun t => e (j t)) := hec.comp hjc
  haveI := hP.2.2.1
  haveI := hP'.1.1
  haveI := hP'.1.2
  have hrange : ∀ t, e (j t) ∈ Set.range j' := by
    have hcl : IsClosed (Set.range j') := hP'.2.1.isClosed_range
    have ho : IsOpen (Set.range j')ᶜ := hcl.isOpen_compl
    have h0 : (ν.map (fun t => e (j t))) (Set.range j')ᶜ = 0 := by
      rw [hν, Measure.map_apply hj'c.measurable ho.measurableSet]
      have : j' ⁻¹' (Set.range j')ᶜ = ∅ := by
        ext t; simp
      rw [this, measure_empty]
    rw [Measure.map_apply hejc.measurable ho.measurableSet] at h0
    have he := (ho.preimage hejc).eq_empty_of_measure_zero h0
    intro t
    by_contra hc
    have : t ∈ (fun t => e (j t)) ⁻¹' (Set.range j')ᶜ := hc
    rw [he] at this
    exact this
  have hφ : Measurable (fun g : G => e g * y) := (hec.mul continuous_const).measurable
  have hF1 : Measurable (fun g => F (e g * y)) := hF.comp hφ
  have hinv1 : ∀ t g, (fun g => F (e g * y)) (j t * g) = (fun g => F (e g * y)) g := by
    intro t g
    obtain ⟨t', ht'⟩ := hrange t
    simp only [map_mul, ← ht', mul_assoc, hinv]
  have hρ1 : UpperTheory.ConvolutionTheory.G.IsNrm j ν (fun g => ρ (e g * y)) := by
    refine ⟨hρ.1.comp hφ, fun x => ?_⟩
    have hm : Measurable (fun z : G' => ρ (z * (e x * y))) := hρ.1.comp (measurable_mul_const _)
    have h1 := lintegral_map (μ := ν) hm hejc.measurable
    have h2 := lintegral_map (μ := ν') hm hj'c.measurable
    rw [hν, h2, hρ.2] at h1
    simp only [map_mul, mul_assoc]
    exact h1.symm
  haveI : μ'.IsMulRightInvariant := by
    have h : μ'.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at h
  have hmp : MeasurePreserving (fun g : G => e g * y) μ μ' :=
    (measurePreserving_mul_right μ' y).comp ⟨hec.measurable, hμ⟩
  have hemb : MeasurableEmbedding (fun g : G => e g * y) :=
    (e.toHomeomorph.trans (Homeomorph.mulRight y)).measurableEmbedding
  obtain ⟨a1, -, a3⟩ := hE G T μ j ν hP _ hF1 hinv1 _ hρ1
  obtain ⟨b1, -, b3⟩ := hE G' T' μ' j' ν' hP' F hF hinv ρ hρ
  refine ⟨?_, ?_⟩
  · rw [a1, b1]
    exact hmp.integrable_comp_emb hemb (g := fun x => F x * ((ρ x).toReal : ℂ))
  · rw [a3, b3]
    exact hmp.integral_comp hemb (fun x => F x * ((ρ x).toReal : ℂ))
