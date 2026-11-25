module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
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

@[expose] public section

theorem UpperTheory.Reformulated.B.Qf46.cover :
    ∀ {G Y : Type} [inst : Group G] [Countable G] [inst_2 : MeasurableSpace Y] [inst_3 : MulAction G Y]
      (μ : MeasureTheory.Measure Y),
      UpperTheory.Esk.Pres G μ →
        ∀ (b : Y → ℝ),
          UpperTheory.Esk.IsCut G b →
            ∀ (S : Set Y),
              MeasurableSet S →
                (∀ (y : Y), ∃ (g : G), g • y ∈ S) → ∫⁻ (y : Y), ENNReal.ofReal (b y) ∂μ ≤ (μ : Set Y → ENNReal) S := by
  intro G Y _ _ _ _ μ hP b hb S hS hc
  have hB : Measurable fun y => ENNReal.ofReal (b y) := hb.meas.ennreal_ofReal
  have hF : ∀ g : G, Measurable (S.indicator fun y => ENNReal.ofReal (b (g⁻¹ • y))) :=
    fun g => (hB.comp (hP g⁻¹).measurable).indicator hS
  have hone : ∀ y, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
    intro y
    have h : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ∑' g : G, ENNReal.ofReal (b (g • y)) :=
      (Equiv.inv G).tsum_eq (fun g : G => ENNReal.ofReal (b (g • y)))
    rw [h, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) (hb.sum y).summable, (hb.sum y).tsum_eq,
      ENNReal.ofReal_one]
  calc ∫⁻ y, ENNReal.ofReal (b y) ∂μ
      ≤ ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ := by
        refine MeasureTheory.lintegral_mono fun y => ?_
        obtain ⟨g, hg⟩ := hc y
        refine le_trans ?_ (ENNReal.le_tsum g)
        rw [Set.indicator_of_mem hg, inv_smul_smul]
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ :=
        MeasureTheory.lintegral_tsum fun g => ((hF g).comp (hP g).measurable).aemeasurable
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        tsum_congr fun g => (hP g).lintegral_comp (hF g)
    _ = ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        (MeasureTheory.lintegral_tsum fun g => (hF g).aemeasurable).symm
    _ = ∫⁻ y, S.indicator 1 y ∂μ := by
        refine MeasureTheory.lintegral_congr fun y => ?_
        by_cases hy : y ∈ S
        · simp only [Set.indicator_of_mem hy, hone, Pi.one_apply]
        · simp only [Set.indicator_of_notMem hy, tsum_zero]
    _ = μ S := MeasureTheory.lintegral_indicator_one hS
