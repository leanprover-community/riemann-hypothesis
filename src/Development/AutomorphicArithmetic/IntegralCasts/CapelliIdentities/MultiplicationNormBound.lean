module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

theorem UpperTheory.Reformulated.B.MultiplicationNormBound.norm_mul_le {X : Type*} (c : X → ℝ) (hb : ∀ x, |c x| ≤ 1)
    (x : X) (z : ℂ) : ‖(c x : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb x)

theorem UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (c : X → ℝ) (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f : Lp ℂ 2 ν) :
    MemLp (fun x => (c x : ℂ) * f x) 2 ν :=
  (Lp.memLp f).of_le
    ((Complex.measurable_ofReal.comp hc).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => UpperTheory.Reformulated.B.MultiplicationNormBound.norm_mul_le c hb x (f x))

noncomputable def UpperTheory.Reformulated.B.MultiplicationNormBound.mulL.{u_1} :
    {X : Type u_1} →
      [inst : MeasurableSpace X] →
        {ν : MeasureTheory.Measure X} →
          (c : X → ℝ) →
            Measurable c →
              (∀ (x : X), |c x| ≤ (1 : ℝ)) →
                ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) →L[ℂ] ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) :=
  fun {X} _ {ν} c hc hb =>
    LinearMap.mkContinuous
      { toFun := fun f => (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).toLp (fun x => (c x : ℂ) * f x)
        map_add' := fun f g => by
          apply Lp.ext
          filter_upwards [(UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb (f + g)).coeFn_toLp,
            (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).coeFn_toLp,
            (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb g).coeFn_toLp, Lp.coeFn_add f g,
            Lp.coeFn_add ((UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).toLp _)
              ((UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb g).toLp _)] with x h1 h2 h3 h4 h5
          rw [h1, h5, h4, Pi.add_apply, Pi.add_apply, h2, h3, mul_add]
        map_smul' := fun a f => by
          apply Lp.ext
          filter_upwards [(UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb (a • f)).coeFn_toLp,
            (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).coeFn_toLp, Lp.coeFn_smul a f,
            Lp.coeFn_smul a ((UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).toLp _)] with x h1 h2 h3 h4
          rw [RingHom.id_apply, h1, h4, h3, Pi.smul_apply, Pi.smul_apply, h2, smul_eq_mul,
            smul_eq_mul, mul_left_comm] }
      1
      (fun f => by
        rw [one_mul]
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [(UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).coeFn_toLp] with x h
        exact h ▸ UpperTheory.Reformulated.B.MultiplicationNormBound.norm_mul_le c hb x (f x))
