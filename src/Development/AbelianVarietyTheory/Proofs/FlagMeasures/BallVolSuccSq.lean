module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.GaugeQuot.BallProd

theorem volume_ball_eq_ballVol {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hd : Module.finrank ℝ F = d) (r : ℝ) :
    (volume : Measure F) (Metric.ball 0 r) = ballVol d r := by
  subst hd
  unfold ballVol
  have h := (stdOrthonormalBasis ℝ F).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem prod_region_eq_ballVol (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ((volume : Measure (ℝ × Sp P Q)).prod
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} = ballVol ((P + Q + 1) ^ 2) r := by
  have h0 := GlobalTheory.volume_preserving_ofLp_complex (Fin P ⊕ Fin Q)
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).comp
    (WithLp.volume_preserving_ofLp ℝ (EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
  have h2 := (h1.prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))).comp
    (WithLp.volume_preserving_ofLp (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
      (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  rw [Measure.volume_eq_prod, ← h2.measure_preimage hm.nullMeasurableSet,
    ← volume_ball_eq_ballVol (F := WithLp 2 (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)) ×
      EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))]
  · congr 1
    ext x
    rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) hr.le, WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
    simp
  · rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ (Fin P ⊕ Fin Q → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring

theorem ballVol_succ_sq (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) *
      ((volume : Measure (ℝ × Sp P Q)).prod
        (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
        {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  have hs : (√2 : ℝ) ≠ 0 := by positivity
  have hfin : Module.finrank ℝ (Sp P Q) = 2 * (P + Q) := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring
  have h0 : MeasurePreserving (fun y : Sp P Q => (√2 : ℝ) • y) volume
      (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • volume) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_addHaar_smul _ hs, hfin, pow_mul, Real.sq_sqrt (by norm_num),
      abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num)]
    simp
  have hne : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ 0 := by simp
  have hnt : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ ⊤ := by simp
  haveI : SFinite (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • (volume : Measure (Sp P Q))) := inferInstance
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have h2 := h1.measure_preimage hm.nullMeasurableSet
  rw [Measure.prod_smul_right, Measure.prod_smul_left, Measure.smul_apply,
    ← Measure.volume_eq_prod, prod_region_eq_ballVol P Q r hr, smul_eq_mul] at h2
  have h3 : {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} =
      Prod.map (Prod.map id fun y : Sp P Q => (√2 : ℝ) • y) id ⁻¹'
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} := by
    ext p
    simp [tanSq, norm_smul, mul_pow, Finset.mul_sum, mul_add]
  rw [h3, h2, ← mul_assoc, ENNReal.mul_inv_cancel hne hnt, one_mul]

end GlobalTheory.GaugeQuot.BallProd
