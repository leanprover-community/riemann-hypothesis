module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open GlobalTheory.JR MeasureTheory

theorem GlobalTheory.JR.fourB_prod_iterated : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂] [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂] (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm → ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ), Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) → (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) → ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y, fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := by
  intro V V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he hes B B₁ B₂ hB₁ hB₂ hB μ μ₁ μ₂ hμ hμ₁ hμ₂
  let h : V ≃ₜ V₁ × V₂ := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  let hm : V ≃ᵐ V₁ × V₂ := h.toMeasurableEquiv
  haveI : (Measure.map e μ).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e he hes
  haveI : (μ₁.prod μ₂).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ₁ μ₂
  set k := Measure.addHaarScalarFactor (Measure.map e μ) (μ₁.prod μ₂) with hk
  have hkeq : Measure.map e μ = k • (μ₁.prod μ₂) := Measure.isAddLeftInvariant_eq_smul _ _
  have hkpos : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨((k : ℝ) : ℂ), by exact_mod_cast hkpos.ne', fun φ hφ y => ?_⟩
  have hmap : Measure.map hm μ = Measure.map e μ := rfl
  have step1 : fourB μ B φ y = ∫ q, φ (e.symm q) * B (e.symm q) y ∂(Measure.map e μ) := by
    rw [← hmap, hm.measurableEmbedding.integral_map]
    simp [fourB, hm, h]
  rw [step1, hkeq, integral_smul_nnreal_measure]
  have hcont : Continuous fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) :=
    (hφ.1.continuous.comp hes).mul ((hB₁.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.1, (e y).1))).mul
      (hB₂.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.2, (e y).2))))
  have hsupp : HasCompactSupport fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    have : HasCompactSupport (φ ∘ h.symm) := hφ.2.comp_homeomorph h.symm
    exact this.mul_right
  have hint := hcont.integrable_of_hasCompactSupport hsupp (μ := μ₁.prod μ₂)
  have e2 : (fun q : V₁ × V₂ => φ (e.symm q) * B (e.symm q) y) =
      fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    ext q; rw [hB]; simp
  rw [e2, integral_prod _ hint]
  simp only [NNReal.smul_def, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← integral_mul_const]
  congr 1; ext v; ring
