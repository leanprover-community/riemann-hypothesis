module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Esk.AnnihilatorQuotientResidues

variable {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] {μ : Measure Y}

def actEquiv (hP : Pres G μ) (g : G) : Y ≃ᵐ Y where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (hP g).measurable
  measurable_invFun := (hP g⁻¹).measurable

lemma embed (hP : Pres G μ) (g : G) : MeasurableEmbedding (fun y : Y => g • y) :=
  (actEquiv hP g).measurableEmbedding

lemma enorm_cut {b : Y → ℝ} (hb : IsCut G b) (y : Y) (x : ℂ) :
    ‖b y • x‖ₑ = ENNReal.ofReal (b y) * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal (hb.nonneg y)]

lemma lint_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ
      = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ := by
  rw [← lintegral_tsum]
  · congr 1
    funext y
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb'.nonneg _)
      (hb'.sum y).summable, (hb'.sum y).tsum_eq, ENNReal.ofReal_one, one_mul]
  · intro g
    exact ((ENNReal.measurable_ofReal.comp (hb'.meas.comp (hP g).measurable)).mul
      ((ENNReal.measurable_ofReal.comp hb.meas).mul hu)).aemeasurable

lemma lint_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℝ≥0∞)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ
      = ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ := by
  have h := (hP g).lintegral_comp_emb (embed hP g)
    (fun z => ENNReal.ofReal (b (g⁻¹ • z)) * (ENNReal.ofReal (b' z) * u z))
  rw [← h]
  congr 1
  funext y
  simp only [inv_smul_smul, hinv, mul_left_comm]

lemma lint_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ = ∫⁻ y, ENNReal.ofReal (b' y) * u y ∂μ := by
  rw [lint_split hP hb hb' u hu, lint_split hP hb' hb u hu]
  calc _ = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ :=
        tsum_congr (lint_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq
        (fun g => ∫⁻ y, ENNReal.ofReal (b (g • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ)

lemma integrable_swap [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) : Integrable (fun y => b' y • u y) μ := by
  refine ⟨(hb'.meas.smul hu).aestronglyMeasurable, ?_⟩
  have h := hi.hasFiniteIntegral
  have e := lint_eq hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm (fun g y => by simp only [hinv])
  simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h ⊢
  rwa [← e]

lemma int_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hi : Integrable (fun y => b y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∑' g : G, ∫ y, b' (g • y) • (b y • u y) ∂μ := by
  rw [← integral_tsum]
  · congr 1
    funext y
    rw [(hb'.sum y).summable.tsum_smul_const, (hb'.sum y).tsum_eq, one_smul]
  · intro g
    exact ((hb'.meas.comp (hP g).measurable).smul (hb.meas.smul hu)).aestronglyMeasurable
  · have h := hi.hasFiniteIntegral
    have e := lint_split hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm
    simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h e ⊢
    rw [← e]
    exact h.ne

lemma int_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℂ)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫ y, b' (g • y) • (b y • u y) ∂μ = ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := by
  have h := (hP g).integral_comp (embed hP g) (fun z => b (g⁻¹ • z) • (b' z • u z))
  rw [← h]
  congr 1
  funext y
  rw [inv_smul_smul, hinv, smul_comm]

lemma int_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) (hi' : Integrable (fun y => b' y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∫ y, b' y • u y ∂μ := by
  rw [int_split hP hb hb' u hu hi, int_split hP hb' hb u hu hi']
  calc _ = ∑' g : G, ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := tsum_congr (int_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq (fun g => ∫ y, b (g • y) • (b' y • u y) ∂μ)

end UpperTheory.Esk.AnnihilatorQuotientResidues

theorem UpperTheory.Esk.action_integral_swap_proof : UpperTheory.Esk.C1 := by
  intro G Y _ _ _ _ μ hP b b' hb hb'
  refine ⟨fun u hu hinv => UpperTheory.Esk.AnnihilatorQuotientResidues.lint_eq hP hb hb' u hu hinv, fun u hu hinv hi => ?_⟩
  have hi' := UpperTheory.Esk.AnnihilatorQuotientResidues.integrable_swap hP hb hb' u hu hinv hi
  exact ⟨hi', UpperTheory.Esk.AnnihilatorQuotientResidues.int_eq hP hb hb' u hu hinv hi hi'⟩
