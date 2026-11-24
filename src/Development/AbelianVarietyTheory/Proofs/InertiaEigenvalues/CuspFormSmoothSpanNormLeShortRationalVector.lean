module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperator, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperatorStatement, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormToLMulLe, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperator, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDirac, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStable, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperator, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpan, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperator =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperator", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.RapidKernelDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_inv (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_vecMul (x : Fin a → Ad E) (m : GA E a) :
    (fun i => pFin E ((x ᵥ* m.val) i)) = (fun i => pFin E (x i)) ᵥ* m.val.map (pFin E) := by
  funext i

  simp [vecMul, dotProduct, map_sum]

theorem norm_vecMul_infGL_le (y : GL (Fin a) (Cinf E)) (x : Fin a → Ad E) :
    ‖fun i => pInf E ((x ᵥ* (infGL E a y).val) i)‖ ≤ (a * height y) * ‖fun i => pInf E (x i)‖ := by
  have hy : ∀ j i, ‖pInf E ((infGL E a y).val j i)‖ ≤ height y := by
    intro j i
    have e : pInf E ((infGL E a y).val j i) = y.val j i :=
      congrArg (fun u : GL (Fin a) (Cinf E) => u.val j i) (pInf_infGL (E := E) y)
    rw [e]
    have : ‖y.val j i‖ ≤ ‖toL y.val‖ :=
      (norm_le_pi_norm (toL y.val j) i).trans (norm_le_pi_norm (toL y.val) j)
    unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h1 := one_le_height y
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_

  simp only [vecMul, dotProduct, map_sum, map_mul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (height y * ‖fun i => pInf E (x i)‖)
    fun j _ => ?_).trans ?_)
  · rw [mul_comm (height y)]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm (fun i => pInf E (x i)) j) (hy j i)
      (norm_nonneg _) (norm_nonneg _))
  · simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)

theorem ideleModule_det_infGL_le (z : GL (Fin a) (Cinf E)) :
    (ideleModule E (GeneralLinearGroup.det (infGL E a z)) : ℝ) ≤
      ((a.factorial : ℝ) * height z ^ a) ^ (2 * Fintype.card (InfinitePlace E)) := by
  set u := GeneralLinearGroup.det (infGL E a z) with hu
  have hB : 1 ≤ (a.factorial : ℝ) * height z ^ a :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast a.factorial_pos) (one_le_pow₀ (one_le_height z))
  have hinf : pInf E (u : Ad E) = (GeneralLinearGroup.det z : Cinf E) := by
    rw [hu, ← CuspRep.det_map, pInf_infGL]
  have hfin : pFin E (u : Ad E) = 1 := by
    rw [hu, ← CuspRep.det_map, pFin_infGL, map_one, Units.val_one]
  rw [ideleModule_eq]
  have h2 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(u : Ad E).2 v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      have : (u : Ad E).2 = 1 := hfin
      rw [this]
      exact norm_one
  rw [h2, mul_one, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ => ?_
  have h1 : ‖(u : Ad E).1 w‖ ≤ a.factorial * height z ^ a := by
    have hnorm : ‖pInf E (u : Ad E) w‖ = ‖(u : Ad E).1 w‖ :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (IsTotallyComplex.isComplex w)).isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (IsTotallyComplex.isComplex w))) ((u : Ad E).1 w)
    rw [← hnorm, hinf]
    exact (norm_le_pi_norm _ w).trans (norm_det_le _ (by unfold height; linarith [norm_nonneg (toL (z⁻¹).val)]))
  have hm : w.mult ≤ 2 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans (pow_le_pow_right₀ hB hm)

end GlobalTheory.RapidKernelDecay

namespace GlobalTheory.RapidKernelDecay

theorem decays_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ)
    (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
    GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.ShortVecDecay.Decays F →
      GlobalTheory.ShortVecDecay.Decays (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF L hL C₀ hC₀ N
  obtain ⟨-, -, hkI⟩ := hk
  obtain ⟨C, hC⟩ := hF L hL C₀ hC₀ N
  obtain ⟨M₁, hM₁, h₁⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀
  obtain ⟨M₂, hM₂, h₂⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀.inv
  set n := a * Module.finrank ℚ E with hn
  set p := 2 * Fintype.card (InfinitePlace E) with hp
  set K₀ : ℝ := (M₂ * a * M₁) ^ n * (a.factorial : ℝ) ^ p with hK₀
  set m := n + a * p with hm
  set I := ∫ x, ‖k x‖ * height (γ x) ^ (m * N) ∂ν with hI
  refine ⟨I * (|C| * K₀ ^ N), fun g c hc ξ hξ hξL => ?_⟩
  set v : Fin a → Ad E := fun j => algebraMap E (Ad E) (ξ j) with hv
  set Xn := ‖fun i => pInf E ((v ᵥ* g.val) i)‖ with hXn
  set G := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hG
  have hGpos : 0 < G := (ideleModule E _).2
  have key : ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * c * infGL E a y)‖ ≤ |C| * K₀ ^ N * height y ^ (m * N) * (Xn ^ n / G) ^ N := by
    intro y
    have hy1 := one_le_height y
    set g' := g * c * infGL E a y * c⁻¹ with hg'
    have eg : g * c * infGL E a y = g' * c := (inv_mul_cancel_right _ c).symm
    have hfin : (fun i => pFin E ((v ᵥ* g'.val) i)) = (fun i => pFin E ((v ᵥ* g.val) i)) := by
      rw [pFin_vecMul, pFin_vecMul]
      congr 1
      show (GeneralLinearGroup.map (pFin E) g').val = (GeneralLinearGroup.map (pFin E) g).val
      simp [hg', map_mul, map_inv, pFin_infGL]
    have hinf : ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ≤ M₂ * a * M₁ * height y * Xn := by
      have e : v ᵥ* g'.val = ((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) ᵥ* (c⁻¹ : GA E a).val := by
        simp only [hg', Units.val_mul, vecMul_vecMul]
      rw [e]
      calc _ ≤ M₂ * ‖fun i => pInf E (((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) i)‖ :=
            h₂ c⁻¹ (Set.inv_mem_inv.2 hc) _
        _ ≤ M₂ * ((a * height y) * ‖fun i => pInf E ((v ᵥ* g.val ᵥ* c.val) i)‖) :=
            mul_le_mul_of_nonneg_left (norm_vecMul_infGL_le y _) hM₂.le
        _ ≤ M₂ * ((a * height y) * (M₁ * Xn)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h₁ c hc _) (by positivity)) hM₂.le
        _ = _ := by ring
    set D := (ideleModule E (GeneralLinearGroup.det (infGL E a y)) : ℝ) with hD
    have hDpos : 0 < D := (ideleModule E _).2
    have hdet : (ideleModule E (GeneralLinearGroup.det g') : ℝ) = G * D := by
      have : GeneralLinearGroup.det g' = GeneralLinearGroup.det g * GeneralLinearGroup.det (infGL E a y) := by
        simp only [hg', map_mul, map_inv]
        rw [mul_right_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]
      rw [this, map_mul, Positive.val_mul]
    have hDinv : D⁻¹ ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by
      have h := ideleModule_det_infGL_le (E := E) y⁻¹
      rw [height_inv] at h
      have hDD : D * (ideleModule E (GeneralLinearGroup.det (infGL E a y⁻¹)) : ℝ) = 1 := by
        rw [hD, ← Positive.val_mul, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one]
        rfl
      rw [eq_inv_of_mul_eq_one_right hDD] at h
      exact h
    have hq : (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ≤
        K₀ * height y ^ m * (Xn ^ n / G) := by
      rw [hdet]
      have hXn0 : 0 ≤ Xn := norm_nonneg _
      have hb0 : 0 ≤ M₂ * a * M₁ * height y * Xn := by
        have := hM₁.le; have := hM₂.le; positivity
      have hc0 : 0 ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by positivity
      calc _ = ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n * D⁻¹ / G := by ring
        _ ≤ (M₂ * a * M₁ * height y * Xn) ^ n * ((a.factorial : ℝ) * height y ^ a) ^ p / G :=
            div_le_div_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hinf n) hDinv
              (inv_nonneg.2 hDpos.le) (pow_nonneg hb0 _)) hGpos.le
        _ = _ := by rw [hK₀, hm, pow_add, pow_mul]; ring
    have hL' : (fun i => pFin E ((v ᵥ* g'.val) i)) ∈ L := hfin ▸ hξL
    have hF' := hC g' c hc ξ hξ hL'
    rw [eg]
    have hnn : 0 ≤ (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
      pow_nonneg (div_nonneg (pow_nonneg (norm_nonneg _) _) (ideleModule E _).2.le) _
    calc ‖F (g' * c)‖ ≤ |C| * (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n /
          (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
          hF'.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnn)
      _ ≤ |C| * (K₀ * height y ^ m * (Xn ^ n / G)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (pow_nonneg (norm_nonneg _) _)
            (ideleModule E _).2.le) hq N) (abs_nonneg C)
      _ = _ := by ring
  have hint : Integrable (fun x => ‖k x‖ * height (γ x) ^ (m * N)) ν := hkI (m * N)
  show ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖ ≤ I * (|C| * K₀ ^ N) * (Xn ^ n / G) ^ N
  calc ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖
      ≤ ∫ x, ‖k x‖ * height (γ x) ^ (m * N) * (|C| * K₀ ^ N * (Xn ^ n / G) ^ N) ∂ν :=
        norm_integral_le_of_norm_le (hint.mul_const _) (.of_forall fun x => by
          rw [norm_mul]
          calc ‖k x‖ * ‖F (g * c * infGL E a (γ x))‖
              ≤ ‖k x‖ * (|C| * K₀ ^ N * height (γ x) ^ (m * N) * (Xn ^ n / G) ^ N) :=
                mul_le_mul_of_nonneg_left (key _) (norm_nonneg _)
            _ = _ := by ring)
    _ = _ := by rw [integral_mul_const, hI]; ring

end GlobalTheory.RapidKernelDecay
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperator =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperatorStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperatorStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperator\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

theorem _root_.GlobalTheory.T.decaysAtShortRationalVectors_rapidKernelOperator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.ShortVecDecay.Decays F → GlobalTheory.ShortVecDecay.Decays (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  first | exact @GlobalTheory.RapidKernelDecay.decays_integral
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperatorStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormToLMulLe =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormToLMulLe", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField\nimport GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe\nimport GroundTheory.GlobalFields.KummerTheory.LocalIndex\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.ColConvGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_toL_mul_le (M P : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (M * P)‖ ≤ (a : ℝ) * ‖toL M‖ * ‖toL P‖ := by
  have hM : ∀ i k, ‖M i k‖ ≤ ‖toL M‖ := fun i k =>
    (norm_le_pi_norm (toL M i) k).trans (norm_le_pi_norm (toL M) i)
  have hP : ∀ i k, ‖P i k‖ ≤ ‖toL P‖ := fun i k =>
    (norm_le_pi_norm (toL P i) k).trans (norm_le_pi_norm (toL P) i)
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i =>
    pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  change ‖(M * P) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ k, M i k * P k j‖ ≤ ∑ k, ‖M i k * P k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin a, ‖toL M‖ * ‖toL P‖ := Finset.sum_le_sum fun k _ =>
        (norm_mul_le _ _).trans (mul_le_mul (hM i k) (hP k j) (norm_nonneg _) (norm_nonneg _))
    _ = (a : ℝ) * ‖toL M‖ * ‖toL P‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

theorem height_mul_le (y u : GL (Fin a) (Cinf E)) :
    height (y * u) ≤ ((a : ℝ) + 1) * height y * height u := by
  have h1 := norm_toL_mul_le y.val u.val
  have h2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
  have e1 : (y * u).val = y.val * u.val := rfl
  have e2 : ((y * u)⁻¹).val = (u⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (toL u.val)
  have n4 := norm_nonneg (toL (u⁻¹).val)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  unfold height
  rw [e1, e2]
  nlinarith [mul_nonneg n1 n3, mul_nonneg n2 n4, mul_nonneg n1 n4, mul_nonneg n2 n3,
    mul_nonneg ha (mul_nonneg n1 n3), mul_nonneg ha (mul_nonneg n2 n4), mul_nonneg ha n1, mul_nonneg ha n2,
    mul_nonneg ha n3, mul_nonneg ha n4, mul_nonneg ha (mul_nonneg n1 n4), mul_nonneg ha (mul_nonneg n2 n3)]

end GlobalTheory.MSpanDecay.ColConvGrowth

namespace GlobalTheory.MSpanDecay

end GlobalTheory.MSpanDecay
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormToLMulLe =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperator =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperator", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormToLMulLe\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.KernelDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem fderiv_chart_apply {G : GA E a → ℂ} (hG : G ∈ Sm E a) (g : GA E a) (u : GL (Fin a) (Cinf E)) (V : Lie E a) :
    fderiv ℝ (chart G g) (toL u.val) V = lieD (toL ((u⁻¹).val * Matrix.of V)) G (g * infGL E a u) := by
  have h := chart_lieD hG (toL ((u⁻¹).val * Matrix.of V)) g (val_mem_invSet u)
  rw [chart_val] at h
  rw [h]
  congr 1
  change V = toL (u.val * ((u⁻¹).val * Matrix.of V))
  rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rfl

theorem norm_rmul_le (M : Lie E a) : ‖rmul M‖ ≤ (a : ℝ) * ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun V => ?_
  have h := ColConvGrowth.norm_toL_mul_le (Matrix.of V) (Matrix.of M)
  calc ‖rmul M V‖ = ‖toL (Matrix.of V * Matrix.of M)‖ := rfl
    _ ≤ (a : ℝ) * ‖V‖ * ‖M‖ := h
    _ = (a : ℝ) * ‖M‖ * ‖V‖ := by ring

theorem norm_toL_le_height (z : GL (Fin a) (Cinf E)) : ‖toL z.val‖ ≤ height z := by
  have := norm_nonneg (toL (z⁻¹).val); unfold height; linarith

theorem norm_toL_inv_le_height (z : GL (Fin a) (Cinf E)) : ‖toL (z⁻¹).val‖ ≤ height z := by
  have := norm_nonneg (toL z.val); unfold height; linarith

theorem norm_fderiv_chart_le {G : GA E a → ℂ} (hG : G ∈ Sm E a) (g : GA E a) (v : GL (Fin a) (Cinf E)) :
    ‖fderiv ℝ (chart G g) (toL v.val)‖ ≤
      (a : ℝ) * ‖toL (v⁻¹).val‖ * ‖fderiv ℝ (chart G (g * infGL E a v)) (oneL E a)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun V => ?_
  rw [fderiv_chart_apply hG g v V]
  have h := ColConvGrowth.norm_toL_mul_le (v⁻¹).val (Matrix.of V)
  calc ‖lieD (toL ((v⁻¹).val * Matrix.of V)) G (g * infGL E a v)‖
      ≤ ‖fderiv ℝ (chart G (g * infGL E a v)) (oneL E a)‖ * ‖toL ((v⁻¹).val * Matrix.of V)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (chart G (g * infGL E a v)) (oneL E a)‖ * ((a : ℝ) * ‖toL (v⁻¹).val‖ * ‖V‖) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

theorem exists_norm_D_le {G : GA E a → ℂ} (hG : Good G) (g : GA E a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ z : GL (Fin a) (Cinf E),
      ‖fderiv ℝ (chart G (g * infGL E a z)) (oneL E a)‖ ≤ C * height z ^ N := by
  let b := Module.finBasis ℝ (Lie E a)
  obtain ⟨Cb, hCb, hb⟩ := b.exists_opNorm_le (F := ℂ)
  have hgr : ∀ i, ∃ (C : ℝ) (N : ℕ), ∀ y : GL (Fin a) (Cinf E),
      ‖lieD (b i) G (g * infGL E a y)‖ ≤ C * height y ^ N := fun i => (hG.derivative (b i)).growth g
  choose C N hCN using hgr
  refine ⟨Cb * ∑ i, |C i|, ∑ i, N i, by positivity, fun z => ?_⟩
  have h1 := one_le_height z
  have hterm : ∀ i, ‖lieD (b i) G (g * infGL E a z)‖ ≤ |C i| * height z ^ (∑ j, N j) := fun i =>
    (hCN i z).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1
        (Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i))) (abs_nonneg _)))
  have hM : 0 ≤ ∑ i, ‖lieD (b i) G (g * infGL E a z)‖ := by positivity
  calc ‖fderiv ℝ (chart G (g * infGL E a z)) (oneL E a)‖
      ≤ Cb * ∑ i, ‖lieD (b i) G (g * infGL E a z)‖ :=
        hb hM fun i => Finset.single_le_sum (f := fun i => ‖lieD (b i) G (g * infGL E a z)‖)
          (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ Cb * ∑ i, |C i| * height z ^ (∑ j, N j) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) hCb.le
    _ = Cb * (∑ i, |C i|) * height z ^ (∑ i, N i) := by rw [← Finset.sum_mul]; ring

theorem eventually_inv_bound (y : GL (Fin a) (Cinf E)) :
    ∀ᶠ w in nhds (toL y.val), w ∈ invSet E a ∧ ‖toL (Matrix.of w)⁻¹‖ ≤ ‖toL (y⁻¹).val‖ + 1 ∧
      ‖w‖ ≤ ‖toL y.val‖ + 1 := by
  have h1 : ∀ᶠ w in nhds (toL y.val), w ∈ invSet E a := isOpen_invSet.mem_nhds (val_mem_invSet y)
  have hc : ContinuousAt (fun w : Lie E a => ‖toL (Matrix.of w)⁻¹‖) (toL y.val) := by
    refine continuous_norm.continuousAt.comp ?_
    have hd : ContinuousAt Ring.inverse (Matrix.of (toL y.val)).det := by
      have : (Matrix.of (toL y.val)).det = ((Matrix.GeneralLinearGroup.det y : (Cinf E)ˣ) : Cinf E) := rfl
      rw [this]
      exact NormedRing.inverse_continuousAt _
    exact continuousAt_matrix_inv (Matrix.of (toL y.val)) hd
  have hv : ‖toL (Matrix.of (toL y.val))⁻¹‖ = ‖toL (y⁻¹).val‖ := by
    congr 1
    exact (Matrix.coe_units_inv y).symm
  have h2 : ∀ᶠ w in nhds (toL y.val), ‖toL (Matrix.of w)⁻¹‖ < ‖toL (y⁻¹).val‖ + 1 :=
    hc.eventually_lt continuousAt_const (by rw [hv]; linarith)
  have h3 : ∀ᶠ w in nhds (toL y.val), ‖w‖ < ‖toL y.val‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by linarith)
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  exact ⟨hw1, hw2.le, hw3.le⟩

theorem measurable_chart {G : GA E a → ℂ} (hG : G ∈ Sm E a) (g : GA E a) : Measurable (chart G g) := by
  classical
  have e : chart G g = (invSet E a).piecewise (chart G g) 0 := by
    funext x
    by_cases h : x ∈ invSet E a
    · simp [Set.piecewise, h]
    · have h' : ¬ IsUnit (Matrix.of x) := h
      simp [Set.piecewise, h, chart, h']
  rw [e]
  exact ContinuousOn.measurable_piecewise (hG g).continuousOn continuousOn_const isOpen_invSet.measurableSet

def rmulL : Lie E a →L[ℝ] (Lie E a →L[ℝ] Lie E a) :=
  LinearMap.toContinuousLinearMap
    { toFun := rmul
      map_add' := fun M P => ContinuousLinearMap.ext fun V => by
        change Matrix.of V * (Matrix.of M + Matrix.of P) = Matrix.of V * Matrix.of M + Matrix.of V * Matrix.of P
        exact Matrix.mul_add _ _ _
      map_smul' := fun c M => ContinuousLinearMap.ext fun V => by
        change Matrix.of V * (c • Matrix.of M) = c • (Matrix.of V * Matrix.of M)
        exact Matrix.mul_smul _ _ _ }

theorem norm_fderiv_comp_le {G : GA E a → ℂ} (hG : G ∈ Sm E a) (g : GA E a) {C : ℝ} {N : ℕ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖fderiv ℝ (chart G (g * infGL E a z)) (oneL E a)‖ ≤ C * height z ^ N) {H : ℝ}
    (u z : GL (Fin a) (Cinf E)) (hu : height u ≤ H) :
    ‖(fderiv ℝ (chart G g) (toL (u * z).val)).comp (rmul (toL z.val))‖ ≤
      (a : ℝ) * (a : ℝ) * C * (((a : ℝ) + 1) * H) ^ (N + 1) * height z ^ (N + 2) := by
  have hz := one_le_height z
  have hu1 := one_le_height u
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hv : height (u * z) ≤ ((a : ℝ) + 1) * H * height z := by
    have := ColConvGrowth.height_mul_le u z
    have h2 : ((a : ℝ) + 1) * height u * height z ≤ ((a : ℝ) + 1) * H * height z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by linarith)) (by linarith)
    linarith
  have hv1 := one_le_height (u * z)
  have hD := hC (u * z)
  have hI := norm_toL_inv_le_height (u * z)
  have hF := norm_fderiv_chart_le hG g (u * z)
  have hR : ‖rmul (toL z.val)‖ ≤ (a : ℝ) * height z :=
    (norm_rmul_le _).trans (mul_le_mul_of_nonneg_left (norm_toL_le_height z) ha)
  have hcomp := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ (chart G g) (toL (u * z).val)) (rmul (toL z.val))
  have hd0 := norm_nonneg (fderiv ℝ (chart G (g * infGL E a (u * z))) (oneL E a))
  have hr0 := norm_nonneg (rmul (toL z.val))
  generalize height (u * z) = t at hv hv1 hD hI
  generalize ‖fderiv ℝ (chart G (g * infGL E a (u * z))) (oneL E a)‖ = d at hD hF hd0
  generalize ‖toL ((u * z)⁻¹).val‖ = i at hI hF
  generalize ‖fderiv ℝ (chart G g) (toL (u * z).val)‖ = f at hF hcomp
  generalize ‖rmul (toL z.val)‖ = r at hR hcomp hr0
  generalize ‖(fderiv ℝ (chart G g) (toL (u * z).val)).comp (rmul (toL z.val))‖ = c at hcomp ⊢
  generalize height z = h at hz hv hR ⊢
  have hH : 0 ≤ ((a : ℝ) + 1) * H := by nlinarith
  have s1 : f ≤ (a : ℝ) * C * t ^ (N + 1) := by
    have : (a : ℝ) * i * d ≤ (a : ℝ) * t * (C * t ^ N) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hI ha) hD hd0 (by positivity)
    calc f ≤ _ := hF
      _ ≤ _ := this
      _ = (a : ℝ) * C * t ^ (N + 1) := by rw [pow_succ]; ring
  have s2 : t ^ (N + 1) ≤ (((a : ℝ) + 1) * H * h) ^ (N + 1) := pow_le_pow_left₀ (by linarith) hv _
  have s3 : f ≤ (a : ℝ) * C * (((a : ℝ) + 1) * H * h) ^ (N + 1) :=
    s1.trans (mul_le_mul_of_nonneg_left s2 (by positivity))
  calc c ≤ f * r := hcomp
    _ ≤ ((a : ℝ) * C * (((a : ℝ) + 1) * H * h) ^ (N + 1)) * ((a : ℝ) * h) :=
        mul_le_mul s3 hR hr0 (by positivity)
    _ = _ := by rw [mul_pow, pow_succ h (N + 1)]; ring

theorem hasFDerivAt_chart_kernel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ)
    (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
    GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)),
    ∃ L : Lie E a →L[ℝ] ℂ, HasFDerivAt (chart (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) g) L
      (toL y.val) ∧ ∀ Z : Lie E a, L Z = ∫ x, k x * lieD (toL (((γ x)⁻¹).val * ((y⁻¹).val * Matrix.of Z) * (γ x).val))
        G (g * infGL E a (y * γ x)) ∂ν := by
  intro E _ _ _ a G X _ ν _ k γ hR hG g y
  obtain ⟨hk, hγ, hint⟩ := hR
  have hsm := hG.mem_Sm
  set cG := chart G g with hcG
  let Γ : X → Lie E a := fun x => toL (γ x).val
  let F : Lie E a → X → ℂ := fun w x => k x * cG (rmul (Γ x) w)
  let F' : Lie E a → X → (Lie E a →L[ℝ] ℂ) := fun w x => k x • ((fderiv ℝ cG (rmul (Γ x) w)).comp (rmul (Γ x)))
  obtain ⟨C, N, hC0, hC⟩ := exists_norm_D_le hG g
  set H : ℝ := 1 + (‖toL y.val‖ + 1) + (‖toL (y⁻¹).val‖ + 1) with hH
  let s := {w : Lie E a | w ∈ invSet E a ∧ ‖toL (Matrix.of w)⁻¹‖ ≤ ‖toL (y⁻¹).val‖ + 1 ∧ ‖w‖ ≤ ‖toL y.val‖ + 1}
  have hs : s ∈ nhds (toL y.val) := eventually_inv_bound y
  have hunit : ∀ w ∈ invSet E a, ∃ u : GL (Fin a) (Cinf E), toL u.val = w := fun w hw => ⟨hw.unit, rfl⟩
  have hHu : ∀ w ∈ s, ∀ u : GL (Fin a) (Cinf E), toL u.val = w → height u ≤ H := by
    rintro w ⟨_, h2, h3⟩ u rfl
    have e : toL (u⁻¹).val = toL (Matrix.of (toL u.val))⁻¹ := congrArg toL (Matrix.coe_units_inv u)
    unfold height
    rw [e]
    linarith
  have hrm : ∀ (u : GL (Fin a) (Cinf E)) x, rmul (Γ x) (toL u.val) = toL (u * γ x).val := fun _ _ => rfl
  have hE1 : ∀ u : GL (Fin a) (Cinf E),
      chart (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) g (toL u.val) = ∫ x, F (toL u.val) x ∂ν := by
    intro u
    rw [chart_val]
    congr 1
    funext x
    dsimp only [F]
    rw [hrm, hcG, chart_val, map_mul, mul_assoc]
  have heq : chart (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) g =ᶠ[nhds (toL y.val)]
      fun w => ∫ x, F w x ∂ν := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet y)] with w hw
    obtain ⟨u, rfl⟩ := hunit w hw
    exact hE1 u
  have hdiff : ∀ x, ∀ w ∈ invSet E a, HasFDerivAt (fun w => F w x) (F' w x) w := by
    intro x w hw
    obtain ⟨u, rfl⟩ := hunit w hw
    have h1 : HasFDerivAt cG (fderiv ℝ cG (rmul (Γ x) (toL u.val))) (rmul (Γ x) (toL u.val)) := by
      rw [hrm]
      exact ((contDiffAt_chart hsm g (val_mem_invSet _)).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp (toL u.val) (rmul (Γ x)).hasFDerivAt).const_smul (k x)
  have hΓm : Measurable Γ := hγ
  have t1 : ∀ w, Measurable (fun x => rmul (Γ x) w) := fun w => by
    have e : (fun x => rmul (Γ x) w) = ((rmulL (E := E) (a := a)).flip w) ∘ Γ := rfl
    rw [e]
    exact (ContinuousLinearMap.continuous _).measurable.comp hΓm
  have t2 : Measurable cG := measurable_chart hsm g
  have hFm : ∀ w, AEStronglyMeasurable (F w) ν := fun w => (hk.mul (t2.comp (t1 w))).aestronglyMeasurable

  let Ψ : Lie E a → (Lie E a →L[ℝ] ℂ) := fun M => (fderiv ℝ cG (rmul M (toL y.val))).comp (rmul M)
  have hΨc : ContinuousOn Ψ (invSet E a) := by
    have hfd : ContinuousOn (fderiv ℝ cG) (invSet E a) :=
      (hsm g).continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
    have hmaps : Set.MapsTo (fun M : Lie E a => rmul M (toL y.val)) (invSet E a) (invSet E a) :=
      fun M hM => IsUnit.mul y.isUnit hM
    have e1 : (fun M : Lie E a => rmul M (toL y.val)) = ((rmulL (E := E) (a := a)).flip (toL y.val)) := rfl
    have e2 : (fun M : Lie E a => rmul M) = ⇑(rmulL (E := E) (a := a)) := rfl
    have h1 : ContinuousOn (fun M : Lie E a => fderiv ℝ cG (rmul M (toL y.val))) (invSet E a) := by
      refine hfd.comp ?_ hmaps
      rw [e1]; exact (ContinuousLinearMap.continuous _).continuousOn
    have h2 : ContinuousOn (fun M : Lie E a => rmul M) (invSet E a) := by
      rw [e2]; exact (ContinuousLinearMap.continuous _).continuousOn
    exact h1.clm_comp h2
  have hF'm : AEStronglyMeasurable (F' (toL y.val)) ν := by
    classical
    borelize (Lie E a →L[ℝ] ℂ)
    have hm : Measurable ((invSet E a).piecewise Ψ 0) :=
      ContinuousOn.measurable_piecewise hΨc continuousOn_const isOpen_invSet.measurableSet
    have e : (fun x => Ψ (Γ x)) = (invSet E a).piecewise Ψ 0 ∘ Γ := by
      funext x
      simp [Γ, val_mem_invSet (γ x)]
    have h3 : AEStronglyMeasurable (fun x => Ψ (Γ x)) ν := by
      rw [e]; exact (hm.comp hΓm).aestronglyMeasurable
    exact hk.aestronglyMeasurable.smul h3

  have hFint : Integrable (F (toL y.val)) ν := by
    obtain ⟨Cg, Ng, hg⟩ := hG.growth g
    have hy1 := one_le_height y
    refine Integrable.mono' ((hint Ng).const_mul (|Cg| * (((a : ℝ) + 1) * height y) ^ Ng)) (hFm _)
      (Filter.Eventually.of_forall fun x => ?_)
    have hz := one_le_height (γ x)
    have hv := ColConvGrowth.height_mul_le y (γ x)
    have h1 : ‖G (g * infGL E a (y * γ x))‖ ≤ |Cg| * height (y * γ x) ^ Ng :=
      (hg (y * γ x)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by linarith [one_le_height (y * γ x)]) _))
    have h2 : height (y * γ x) ^ Ng ≤ (((a : ℝ) + 1) * height y) ^ Ng * height (γ x) ^ Ng := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith [one_le_height (y * γ x)]) hv _
    have e : F (toL y.val) x = k x * G (g * infGL E a (y * γ x)) := by
      simp only [F]; rw [hrm, hcG, chart_val]
    rw [e, norm_mul]
    calc ‖k x‖ * ‖G (g * infGL E a (y * γ x))‖ ≤ ‖k x‖ * (|Cg| * ((((a : ℝ) + 1) * height y) ^ Ng * height (γ x) ^ Ng)) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))) (norm_nonneg _)
      _ = _ := by ring

  set K : ℝ := (a : ℝ) * (a : ℝ) * C * (((a : ℝ) + 1) * H) ^ (N + 1) with hK
  have hbound : ∀ x, ∀ w ∈ s, ‖F' w x‖ ≤ K * (‖k x‖ * height (γ x) ^ (N + 2)) := by
    intro x w hw
    obtain ⟨u, rfl⟩ := hunit w hw.1
    have hu := hHu _ hw u rfl
    have h := norm_fderiv_comp_le hsm g hC0 hC u (γ x) hu
    simp only [F']
    rw [norm_smul, hrm]
    calc ‖k x‖ * ‖(fderiv ℝ cG (toL (u * γ x).val)).comp (rmul (Γ x))‖
        ≤ ‖k x‖ * (K * height (γ x) ^ (N + 2)) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by ring
  have hbint : Integrable (fun x => K * (‖k x‖ * height (γ x) ^ (N + 2))) ν := (hint (N + 2)).const_mul K
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le hs (Filter.Eventually.of_forall hFm) hFint hF'm
    (Filter.Eventually.of_forall hbound) hbint (Filter.Eventually.of_forall fun x w hw => hdiff x w hw.1)
  have hF'int : Integrable (F' (toL y.val)) ν :=
    Integrable.mono' hbint hF'm (Filter.Eventually.of_forall fun x => hbound x _ (mem_of_mem_nhds hs))
  refine ⟨∫ x, F' (toL y.val) x ∂ν, key.congr_of_eventuallyEq heq, fun Z => ?_⟩
  rw [ContinuousLinearMap.integral_apply hF'int]
  congr 1
  funext x
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hrm, hcG, fderiv_chart_apply hsm g, smul_eq_mul]
  congr 3
  change ((y * γ x)⁻¹).val * (Matrix.of Z * (γ x).val) = ((γ x)⁻¹).val * ((y⁻¹).val * Matrix.of Z) * (γ x).val
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.MSpanDecay.KernelDeriv
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperator =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDirac =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDirac", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\npublic import Mathlib.Analysis.Matrix.Normed\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector\nimport Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin\nimport Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField MeasureTheory Matrix Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutGrowth.ApproxId GlobalTheory.GLFin
open scoped ContDiff

namespace GlobalTheory.GLFin.Inhab
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiffOn_invL : ContDiffOn ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) (invSet E a) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  intro x hx
  have hu : IsUnit (S x) := hx
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (S x) := by simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  have h2 := (T.contDiff.contDiffAt.comp x (h1.comp x S.contDiff.contDiffAt)).contDiffWithinAt (s := invSet E a)
  refine h2.congr (fun y _ => ?_) ?_ <;> exact congrArg toL (Matrix.nonsing_inv_eq_ringInverse _)
end




end GlobalTheory.GLFin.Inhab
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDirac =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStable =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStable", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDirac\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\npublic import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField\nimport Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds\nimport GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe\nimport GroundTheory.GlobalFields.KummerTheory.LocalIndex\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section
open scoped ContDiff

namespace GlobalTheory.SmoothClosure

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem fderiv_chart_apply (F : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a)
    (hd : DifferentiableAt ℝ (chart F g) x) (Z : Lie E a) :
    fderiv ℝ (chart F g) x Z = chart (lieD (toL ((Matrix.of x)⁻¹ * Matrix.of Z)) F) g x := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  rw [chart_val, lieD, chart_mul]
  have e1 : lmul (toL u.val) (oneL E a) = toL u.val := mul_one u.val
  rw [fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL u.val)).differentiableAt, e1, ContinuousLinearMap.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  congr 1
  change Z = u.val * ((Matrix.of (toL u.val))⁻¹ * Matrix.of Z)
  have : (Matrix.of (toL u.val))⁻¹ = (↑(u⁻¹) : Matrix (Fin a) (Fin a) (Cinf E)) := by
    change (u.val)⁻¹ = _
    rw [Matrix.coe_units_inv]
  rw [this, ← mul_assoc, Units.mul_inv, one_mul]
  rfl

theorem chart_lieD_basis {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E a)) (F : GA E a → ℂ) (g : GA E a)
    {x : Lie E a} (hx : x ∈ invSet E a) (W : Lie E a) :
    chart (lieD W F) g x = ∑ k, b.repr W k • chart (lieD (b k) F) g x := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  simp only [chart_val, lieD]
  conv_lhs => rw [← b.sum_repr W]

  rw [map_sum]
  simp only [map_smul]

theorem le_Sm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Submodule ℂ (GA E a → ℂ)),
    (∀ F ∈ S, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a)) →
    (∀ F ∈ S, ∀ X : Lie E a, lieD X F ∈ S) → S ≤ Sm E a := by
  intro E _ _ _ a S hdiff hlie
  let b := Module.finBasis ℝ (Lie E a)
  have key : ∀ n : ℕ, ∀ F ∈ S, ∀ g : GA E a, ContDiffOn ℝ n (chart F g) (invSet E a) := by
    intro n
    induction n with
    | zero =>
      intro F hF g
      exact contDiffOn_zero.2 (hdiff F hF g).continuousOn
    | succ n ih =>
      intro F hF g
      rw [Nat.cast_succ]
      refine contDiffOn_succ_of_fderiv_apply (hdiff F hF g) (by simp) fun Z => ?_
      have hc : ∀ k, ContDiffOn ℝ n (fun x : Lie E a =>
          (b.coord k).toContinuousLinearMap (rmul Z (toL (Matrix.of x)⁻¹))) (invSet E a) := fun k =>
        (b.coord k).toContinuousLinearMap.contDiff.comp_contDiffOn
          ((rmul Z).contDiff.comp_contDiffOn (GlobalTheory.GLFin.Inhab.contDiffOn_invL.of_le (by exact_mod_cast le_top)))
      have hsum : ContDiffOn ℝ n (fun x => ∑ k ∈ Finset.univ, (b.coord k).toContinuousLinearMap
          (rmul Z (toL (Matrix.of x)⁻¹)) • chart (lieD (b k) F) g x) (invSet E a) :=
        ContDiffOn.sum fun k _ => (hc k).smul (ih _ (hlie F hF (b k)) g)
      refine hsum.congr fun x hx => ?_
      rw [fderivWithin_of_isOpen isOpen_invSet hx,
        fderiv_chart_apply F g hx ((hdiff F hF g).differentiableAt (isOpen_invSet.mem_nhds hx)) Z,
        chart_lieD_basis b F g hx]
      rfl
  intro F hF g
  exact contDiffOn_infty.2 fun n => key n F hF g

end GlobalTheory.SmoothClosure
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStable =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms", "h": "module\n\npublic import GroundTheory.AutomorphicForms.ReductionSiegel\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section
open scoped Pointwise
namespace GlobalTheory.HCF.ModGrowth
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_ringEquivComplex (w : InfinitePlace E) (hw : w.IsComplex) (x : w.Completion) :
    ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry.norm_map_of_map_zero
    (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)) x

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  norm_ringEquivComplex w (IsTotallyComplex.isComplex w) (x.1 w)

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans_eq
    (by simp [nsmul_eq_mul]))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
  · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  · exact (norm_le_pi_norm (toL B k) j).trans (norm_le_pi_norm (toL B) k)

theorem height_mul_le (y z : GL (Fin a) (Cinf E)) :
    GlobalTheory.CuspRep.height (y * z) ≤ (a + 1) * (GlobalTheory.CuspRep.height y * GlobalTheory.CuspRep.height z) := by
  have h1 := norm_toL_mul_le (E := E) y.val z.val
  have h2 := norm_toL_mul_le (E := E) (z⁻¹).val (y⁻¹).val
  unfold GlobalTheory.CuspRep.height
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  have p1 := norm_nonneg (toL y.val)
  have p2 := norm_nonneg (toL (y⁻¹).val)
  have q1 := norm_nonneg (toL z.val)
  have q2 := norm_nonneg (toL (z⁻¹).val)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith [mul_nonneg p1 q1, mul_nonneg p2 q2, mul_nonneg p1 q2, mul_nonneg p2 q1, mul_nonneg ha (mul_nonneg p1 q1),
    mul_nonneg ha (mul_nonneg p2 q2), mul_nonneg ha p1, mul_nonneg ha p2, mul_nonneg ha q1, mul_nonneg ha q2,
    mul_nonneg ha (mul_nonneg p1 q2), mul_nonneg ha (mul_nonneg p2 q1)]

theorem continuous_height : Continuous (GlobalTheory.CuspRep.height : GL (Fin a) (Cinf E) → ℝ) := by
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val :=
    Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp continuous_inv
  exact (continuous_const.add (continuous_norm.comp h1)).add (continuous_norm.comp h2)

theorem pFin_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) :
    Matrix.GeneralLinearGroup.map (pFin E) (diagUnits a fun i => posIdele (K := E) (r i) (hr i)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pFin E ((diagUnits a fun i => posIdele (K := E) (r i) (hr i) : GA E a) i j) = (1 : Matrix (Fin a) (Fin a) (Af E)) i j
  rw [coe_diagUnits, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by
      change ((posIdele (K := E) (r i) (hr i) : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).2 v = _
      rw [posIdele_finite]; rfl
  · exact map_zero _

theorem height_pInf_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) :
    GlobalTheory.CuspRep.height (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a fun i => posIdele (K := E) (r i) (hr i)))
      ≤ 1 + ∑ i, (r i + (r i)⁻¹) := by
  set d : Fin a → GroundTheory.Global.IdeleGroup E := fun i => posIdele (K := E) (r i) (hr i) with hd
  have hn : ∀ i w, ‖pInf E (d i : Ad E) w‖ = r i := fun i w => by
    rw [norm_pInf_apply]; exact norm_posIdele_infinite (r i) (hr i) w
  have hn' : ∀ i w, ‖pInf E (((d i)⁻¹ : GroundTheory.Global.IdeleGroup E) : Ad E) w‖ = (r i)⁻¹ := fun i w => by
    have e : pInf E (((d i)⁻¹ : GroundTheory.Global.IdeleGroup E) : Ad E) w * pInf E (d i : Ad E) w = 1 := by
      rw [← Pi.mul_apply, ← map_mul, Units.inv_mul, map_one, Pi.one_apply]
    have := congrArg norm e
    rw [norm_mul, hn, norm_one] at this
    exact eq_inv_of_mul_eq_one_left this
  have key : ∀ (f : Fin a → GroundTheory.Global.IdeleGroup E) (s : Fin a → ℝ), (∀ i w, ‖pInf E (f i : Ad E) w‖ = s i) →
      (∀ i, 0 ≤ s i) → ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a f)).val‖ ≤ ∑ i, s i := by
    intro f s hf hs
    have h0 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => hs i
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    change ‖pInf E ((diagUnits a f : GA E a) i j)‖ ≤ _
    rw [coe_diagUnits, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      refine (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
      rw [hf]
      exact Finset.single_le_sum (fun k _ => hs k) (Finset.mem_univ i)
    · rw [map_zero, norm_zero]; exact h0
  have h1 := key d r hn fun i => (hr i).le
  have h2 := key (fun i => (d i)⁻¹) (fun i => (r i)⁻¹) hn' fun i => (inv_pos.2 (hr i)).le
  have e : (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a d))⁻¹ =
      Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a fun i => (d i)⁻¹) := by
    rw [← map_inv, ← map_inv]; rfl
  unfold GlobalTheory.CuspRep.height
  rw [e, Finset.sum_add_distrib]
  linarith

theorem span_props {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ} {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    (∀ l ∈ L, finRep E a l φ = φ) ∧ ∀ g, ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
      ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    refine ⟨hx.2.1, fun g => ?_⟩
    obtain ⟨C, M, h⟩ := hx.1.growth g
    refine ⟨|C|, M, abs_nonneg _, fun y => (h y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) ?_)⟩
    exact pow_nonneg (zero_le_one.trans (one_le_height y)) _
  | zero => exact ⟨fun l _ => map_zero _, fun g => ⟨0, 0, le_rfl, fun y => by simp⟩⟩
  | add x y _ _ hx hy =>
    refine ⟨fun l hl => by rw [map_add (f := _), hx.1 l hl, hy.1 l hl], fun g => ?_⟩
    obtain ⟨C1, M1, h1, e1⟩ := hx.2 g
    obtain ⟨C2, M2, h2, e2⟩ := hy.2 g
    refine ⟨C1 + C2, M1 + M2, add_nonneg h1 h2, fun z => ?_⟩
    have hz := one_le_height z
    have p1 : GlobalTheory.CuspRep.height z ^ M1 ≤ GlobalTheory.CuspRep.height z ^ (M1 + M2) := pow_le_pow_right₀ hz (by omega)
    have p2 : GlobalTheory.CuspRep.height z ^ M2 ≤ GlobalTheory.CuspRep.height z ^ (M1 + M2) := pow_le_pow_right₀ hz (by omega)
    calc ‖(x + y).1 (g * infGL E a z)‖ = ‖x.1 (g * infGL E a z) + y.1 (g * infGL E a z)‖ := rfl
      _ ≤ ‖x.1 (g * infGL E a z)‖ + ‖y.1 (g * infGL E a z)‖ := norm_add_le _ _
      _ ≤ C1 * GlobalTheory.CuspRep.height z ^ (M1 + M2) + C2 * GlobalTheory.CuspRep.height z ^ (M1 + M2) :=
        add_le_add ((e1 z).trans (mul_le_mul_of_nonneg_left p1 h1)) ((e2 z).trans (mul_le_mul_of_nonneg_left p2 h2))
      _ = (C1 + C2) * GlobalTheory.CuspRep.height z ^ (M1 + M2) := by ring
  | smul c x _ hx =>
    refine ⟨fun l hl => by rw [map_smul, hx.1 l hl], fun g => ?_⟩
    obtain ⟨C, M, h, e⟩ := hx.2 g
    refine ⟨‖c‖ * C, M, by positivity, fun z => ?_⟩
    change ‖c * x.1 (g * infGL E a z)‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (e z) (norm_nonneg c)

theorem uniform_fin {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hinv : ∀ l ∈ L, finRep E a l φ = φ)
    (hg : ∀ g, ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M)
    {S : Set (GL (Fin a) (Af E))} (hS : IsCompact S) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ s ∈ S, ∀ y, ‖φ.1 (finGL E a s * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M := by
  classical
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : GL (Fin a) (Af E) => s • (L : Set (GL (Fin a) (Af E))))
    (fun s => hL.leftCoset s) (fun s _ => Set.mem_iUnion.2 ⟨s, Set.mem_smul_set.2 ⟨1, L.one_mem, mul_one s⟩⟩)
  choose C M hC hb using fun s : GL (Fin a) (Af E) => hg (finGL E a s)
  refine ⟨∑ s ∈ t, C s, ∑ s ∈ t, M s, Finset.sum_nonneg fun s _ => hC s, fun s' hs' y => ?_⟩
  obtain ⟨s, hst, hs⟩ := Set.mem_iUnion₂.1 (ht hs')
  obtain ⟨l, hl, rfl⟩ := Set.mem_smul_set.1 hs
  have e : φ.1 (finGL E a (s • l) * infGL E a y) = φ.1 (finGL E a s * infGL E a y) := by
    have h := congrArg (fun ψ : Sm E a => ψ.1 (finGL E a s * infGL E a y)) (hinv l hl)
    refine Eq.trans ?_ h
    change φ.1 (finGL E a (s * l) * infGL E a y) = φ.1 (finGL E a s * infGL E a y * finGL E a l)
    rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
  rw [e]
  have hy := one_le_height y
  refine (hb s y).trans (mul_le_mul (Finset.single_le_sum (fun s _ => hC s) hst)
    (pow_le_pow_right₀ hy (Finset.single_le_sum (fun s _ => Nat.zero_le (M s)) hst))
    (pow_nonneg (zero_le_one.trans hy) _) (Finset.sum_nonneg fun s _ => hC s))

end GlobalTheory.HCF.ModGrowth

namespace GlobalTheory.HCF.ModGrowth

theorem modGrowth_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ))
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N),
    ∀ Ω : Set (GA E a), IsCompact Ω → ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i),
    ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E),
    ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤
      C * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀ := by
  intro E _ _ _ a L hL W X N φ hφ Ω hΩ
  obtain ⟨hinv, hgr⟩ := span_props hφ
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h1 : ∀ g : GA E 0, g = 1 := fun g => Units.ext (Matrix.ext fun i => Fin.elim0 i)
    refine ⟨‖φ.1 1‖, 0, norm_nonneg _, fun b _ r hr k _ y => ?_⟩
    rw [h1 (b * _ * k * _)]
    simp
  have hS : IsCompact ((fun p : GA E a × GA E a => Matrix.GeneralLinearGroup.map (pFin E) (p.1 * p.2)) ''
      (Ω ×ˢ ((maxCompact : Subgroup (GA E a)) : Set (GA E a)))) :=
    (hΩ.prod isCompact_maxCompact).image ((ContAut.continuous_map_pFin E a).comp (continuous_fst.mul continuous_snd))
  obtain ⟨C1, M, hC1, hb1⟩ := uniform_fin hL hinv hgr hS
  have hf : Continuous fun g : GA E a => GlobalTheory.CuspRep.height (Matrix.GeneralLinearGroup.map (pInf E) g) :=
    continuous_height.comp (ContAut.continuous_map_pInf E a)
  obtain ⟨Mb, hMb⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Mk, hMk⟩ := (isCompact_maxCompact (K := E) (n := a)).exists_bound_of_continuousOn hf.continuousOn
  have hB : (0 : ℝ) ≤ (a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) := by positivity
  refine ⟨C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1)) ^ M, M, by positivity, fun b hb r hr k hk y => ?_⟩
  have hfin : Matrix.GeneralLinearGroup.map (pFin E) (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k *
      infGL E a y) = Matrix.GeneralLinearGroup.map (pFin E) (b * k) := by
    simp only [map_mul, pFin_diag, pFin_infGL, mul_one]
  have hinf : Matrix.GeneralLinearGroup.map (pInf E) (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k *
      infGL E a y) = Matrix.GeneralLinearGroup.map (pInf E) b *
        Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i))) *
        Matrix.GeneralLinearGroup.map (pInf E) k * y := by
    simp only [map_mul, pInf_infGL]
  have hx := infGL_mul_finGL (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)
  rw [infGL_comm, hfin, hinf] at hx
  rw [← hx]
  have hs : Matrix.GeneralLinearGroup.map (pFin E) (b * k) ∈ (fun p : GA E a × GA E a =>
      Matrix.GeneralLinearGroup.map (pFin E) (p.1 * p.2)) '' (Ω ×ˢ ((maxCompact : Subgroup (GA E a)) : Set (GA E a))) :=
    ⟨(b, k), ⟨hb, hk⟩, rfl⟩
  refine (hb1 _ hs _).trans ?_

  set A := Matrix.GeneralLinearGroup.map (pInf E) b
  set D := Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)))
  set K := Matrix.GeneralLinearGroup.map (pInf E) k
  set s := ∑ i, (r i + (r i)⁻¹)
  have hs1 : 1 ≤ s := by
    have h0 : ∀ i, 0 ≤ r i + (r i)⁻¹ := fun i => add_nonneg (hr i).le (inv_pos.2 (hr i)).le
    have h1 : 1 ≤ r ⟨0, ha⟩ + (r ⟨0, ha⟩)⁻¹ := by
      rcases le_total (r ⟨0, ha⟩) 1 with h | h
      · linarith [(one_le_inv₀ (hr ⟨0, ha⟩)).2 h, hr ⟨0, ha⟩]
      · linarith [inv_pos.2 (hr ⟨0, ha⟩)]
    exact h1.trans (Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ _))
  have hA : GlobalTheory.CuspRep.height A ≤ max Mb 1 :=
    ((Real.le_norm_self _).trans (hMb b hb)).trans (le_max_left _ _)
  have hK : GlobalTheory.CuspRep.height K ≤ max Mk 1 :=
    ((Real.le_norm_self _).trans (hMk k hk)).trans (le_max_left _ _)
  have hD : GlobalTheory.CuspRep.height D ≤ 2 * s := (height_pInf_diag r hr).trans (by linarith)
  have hA1 := one_le_height A
  have hD1 := one_le_height D
  have hK1 := one_le_height K
  have hy1 := one_le_height y
  have c0 : (0 : ℝ) ≤ a + 1 := by positivity
  have e3 := height_mul_le A D
  have e2 := height_mul_le (A * D) K
  have e1 := height_mul_le (A * D * K) y
  have hAD : GlobalTheory.CuspRep.height A * GlobalTheory.CuspRep.height D ≤ max Mb 1 * (2 * s) :=
    mul_le_mul hA hD (by linarith) (by positivity)
  have hADK : GlobalTheory.CuspRep.height (A * D * K) ≤ (a + 1) * ((a + 1) * (max Mb 1 * (2 * s)) * max Mk 1) :=
    e2.trans (mul_le_mul_of_nonneg_left (mul_le_mul (e3.trans (mul_le_mul_of_nonneg_left hAD c0)) hK (by linarith)
      (by positivity)) c0)
  have hz : GlobalTheory.CuspRep.height (A * D * K * y) ≤ (a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) * s * GlobalTheory.CuspRep.height y := by
    refine e1.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hADK (by linarith)) c0).trans_eq ?_)
    ring
  have hz0 : 0 ≤ GlobalTheory.CuspRep.height (A * D * K * y) := zero_le_one.trans (one_le_height _)
  calc C1 * GlobalTheory.CuspRep.height (A * D * K * y) ^ M
      ≤ C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) * s * GlobalTheory.CuspRep.height y) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz M) hC1
    _ = C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1)) ^ M * s ^ M * GlobalTheory.CuspRep.height y ^ M := by
        rw [mul_pow, mul_pow]; ring

end GlobalTheory.HCF.ModGrowth
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperator =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperator", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay

theorem growth_kernel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Growth F → GlobalTheory.MSpanDecay.Growth (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF g
  obtain ⟨C, N, hC⟩ := hF g
  set I := ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν with hI
  refine ⟨|C| * ((a : ℝ) + 1) ^ N * I, N, fun y => ?_⟩
  have hint := (hk.2.2 N).const_mul (|C| * ((a : ℝ) + 1) ^ N * height y ^ N)
  have hb : ∀ x, ‖k x * F (g * infGL E a y * infGL E a (γ x))‖ ≤
      |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
    intro x
    rw [mul_assoc g, ← map_mul, norm_mul]
    have h1 := hC (y * γ x)
    have hm := GlobalTheory.HCF.ModGrowth.height_mul_le y (γ x)
    have hy := one_le_height y
    have hg := one_le_height (γ x)
    have hz := one_le_height (y * γ x)
    have e1 : height (y * γ x) ^ N ≤ (((a : ℝ) + 1) * (height y * height (γ x))) ^ N :=
      pow_le_pow_left₀ (by linarith) hm N
    have e2 : ‖F (g * infGL E a (y * γ x))‖ ≤ |C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)).trans
        (mul_le_mul_of_nonneg_left e1 (abs_nonneg C)))
    calc ‖k x‖ * ‖F (g * infGL E a (y * γ x))‖ ≤ ‖k x‖ * (|C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N)) :=
          mul_le_mul_of_nonneg_left e2 (norm_nonneg _)
      _ = |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
          rw [mul_pow, mul_pow]; ring
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hb)).trans_eq ?_
  rw [integral_const_mul, hI]
  ring

end GlobalTheory.MSpanDecay
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperator =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpan =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpan", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_entry_le (A : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) : ‖A i j‖ ≤ ‖toL A‖ :=
  (norm_le_pi_norm (toL A i) j).trans (norm_le_pi_norm (toL A) i)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem measurable_comp_of_continuousOn {X : Type} [MeasurableSpace X] {f : Lie E a → ℂ}
    (hf : ContinuousOn f (invSet E a)) {φ : X → Lie E a} (hφ : Measurable φ) (hφ' : ∀ x, φ x ∈ invSet E a) :
    Measurable fun x => f (φ x) := by
  have e : (fun x => f (φ x)) = (invSet E a).restrict f ∘ fun x => (⟨φ x, hφ' x⟩ : invSet E a) := rfl
  rw [e]
  exact hf.restrict.measurable.comp (hφ.subtype_mk)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem measurable_inv {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => toL ((γ x)⁻¹).val := by
  have key : ∀ y : GL (Fin a) (Cinf E), ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) • (y : Matrix (Fin a) (Fin a) (Cinf E)).adjugate := by
    intro y
    refine Units.inv_eq_of_mul_eq_one_left ?_
    have hu : IsUnit (y : Matrix (Fin a) (Fin a) (Cinf E)).det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    have h1 : (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) * (y : Matrix (Fin a) (Fin a) (Cinf E)).det = 1 := by
      funext w
      have hw : (y : Matrix (Fin a) (Fin a) (Cinf E)).det w ≠ 0 :=
        ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).isUnit_map hu).ne_zero
      exact inv_mul_cancel₀ hw
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, h1, one_smul]
  have e : (fun x => toL ((γ x)⁻¹).val) = fun x => toL ((fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) •
      (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate) := funext fun x => congrArg toL (key (γ x))
  rw [e]
  have hdet : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)).det :=
    (contDiff_det (E := E) (a := a)).continuous.measurable.comp hγ
  have hadjc : Continuous fun m : Lie E a => (toL (Matrix.of m).adjugate : Lie E a) :=
    Continuous.matrix_adjugate continuous_id
  have hadj : Measurable fun x => toL (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate :=
    hadjc.measurable.comp hγ
  have hc : Measurable fun x => (fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹ : Cinf E) :=
    Measurable.of_eval fun w => ((measurable_pi_apply w).comp hdet).inv
  exact (continuous_smul (M := Cinf E) (X := Lie E a)).measurable.comp (hc.prodMk hadj)

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem measurable_mul {X : Type} [MeasurableSpace X] {A B : X → Lie E a} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => toL (Matrix.of (A x) * Matrix.of (B x)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => Measurable.of_eval fun w => ?_
  have e : (fun x => toL (Matrix.of (A x) * Matrix.of (B x)) i j w) = fun x => ∑ k, A x i k w * B x k j w := by
    funext x; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [e]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply w).comp ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA))).mul
      ((measurable_pi_apply w).comp ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB)))

theorem measurable_conj {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) (Y : Lie E a) :
    Measurable fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val) :=
  measurable_mul (measurable_mul (measurable_inv hγ) measurable_const) hγ

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_conj_le (y : GL (Fin a) (Cinf E)) (Y : Lie E a) :
    ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * a * ‖Y‖ * height y ^ 2 := by
  have h1 : ‖toL y.val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h2 : ‖toL (y⁻¹).val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL y.val)]
  have h3 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (‖toL (y⁻¹).val‖ * ‖Y‖) := _root_.GlobalTheory.AutGrowth.norm_toL_mul_le _ _
  calc ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * (‖toL ((y⁻¹).val * Matrix.of Y)‖ * ‖toL y.val‖) :=
        _root_.GlobalTheory.AutGrowth.norm_toL_mul_le _ _
    _ ≤ a * ((a * (height y * ‖Y‖)) * height y) := by
        have h4 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (height y * ‖Y‖) :=
          h3.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (Nat.cast_nonneg a))
        exact mul_le_mul_of_nonneg_left (mul_le_mul h4 h1 (norm_nonneg _) ((norm_nonneg _).trans h4)) (Nat.cast_nonneg a)
    _ = a * a * ‖Y‖ * height y ^ 2 := by ring

theorem lieD_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E a)) (W : Lie E a) (G : GA E a → ℂ)
    (g : GA E a) : lieD W G g = ∑ j, ((b.repr W j : ℝ) : ℂ) * lieD (b j) G g := by
  unfold lieD
  conv_lhs => rw [← b.sum_repr W]

  rw [map_sum]
  simp only [map_smul, Complex.real_smul]

theorem measurable_height {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => height (γ x) := by
  have e : (fun x => height (γ x)) = fun x => 1 + ‖toL (γ x).val‖ + ‖toL ((γ x)⁻¹).val‖ := rfl
  rw [e]
  exact (measurable_const.add hγ.norm).add (measurable_inv hγ).norm

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay


open RapidLie in
theorem integral_lieD_conj_mem_kSpan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (Y : Lie E a), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν) ∈ GlobalTheory.MSpanDecay.kSpan E a := by
  intro E _ _ _ a G X _ ν _ k γ Y hk hG
  obtain ⟨hkm, hγm, hint⟩ := hk
  have hγ : Measurable fun x => toL (γ x).val := hγm
  let b := Module.finBasis ℝ (Lie E a)
  let L : Fin (Module.finrank ℝ (Lie E a)) → Lie E a →L[ℝ] ℝ := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let W : X → Lie E a := fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)
  let c : Fin (Module.finrank ℝ (Lie E a)) → X → ℂ := fun j x => ((L j (W x) : ℝ) : ℂ)
  have hW : Measurable W := measurable_conj hγ Y
  have hc : ∀ j, Measurable (c j) := fun j => Complex.measurable_ofReal.comp ((L j).continuous.measurable.comp hW)
  set D : Fin (Module.finrank ℝ (Lie E a)) → ℝ := fun j => ‖L j‖ * (a * a * ‖Y‖) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by positivity
  have hcb : ∀ j x, ‖c j x‖ ≤ D j * height (γ x) ^ 2 := by
    intro j x
    have h := (L j).le_opNorm (W x)
    rw [Complex.norm_real]
    refine h.trans ?_
    rw [hD, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_conj_le (γ x) Y) (norm_nonneg _)
  have hG' : ∀ j, Good (lieD (b j) G) := fun j => hG.derivative _
  have hrap : ∀ j, GlobalTheory.JSW.IsRapidInf ν (fun x => k x * c j x) γ := by
    intro j
    refine ⟨hkm.mul (hc j), hγm, fun N => ?_⟩
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j))
      (((hkm.mul (hc j)).norm.mul ((measurable_height hγ).pow_const N)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    calc ‖k x‖ * ‖c j x‖ * height (γ x) ^ N ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * height (γ x) ^ N := by
          gcongr; exact hcb j x
      _ = D j * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have hmeasG : ∀ j g, Measurable fun x => lieD (b j) G (g * infGL E a (γ x)) := by
    intro j g
    have e : (fun x => lieD (b j) G (g * infGL E a (γ x))) = fun x => chart (lieD (b j) G) g (toL (γ x).val) :=
      funext fun x => (chart_val _ g (γ x)).symm
    rw [e]
    exact measurable_comp_of_continuousOn (((hG' j).mem_Sm g).continuousOn) hγ fun x => val_mem_invSet (γ x)
  have hintj : ∀ j g, Integrable (fun x => k x * c j x * lieD (b j) G (g * infGL E a (γ x))) ν := by
    intro j g
    obtain ⟨C, N, hCN⟩ := (hG' j).growth g
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j * |C|))
      (((hkm.mul (hc j)).mul (hmeasG j g)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    have hg : ‖lieD (b j) G (g * infGL E a (γ x))‖ ≤ |C| * height (γ x) ^ N :=
      (hCN (γ x)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
    rw [norm_mul, norm_mul]
    calc ‖k x‖ * ‖c j x‖ * ‖lieD (b j) G (g * infGL E a (γ x))‖
        ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * (|C| * height (γ x) ^ N) := by
          gcongr
          · exact hcb j x
      _ = D j * |C| * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have e : (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G
      (g * infGL E a (γ x)) ∂ν) =
      ∑ j, fun g : GA E a => ∫ x, k x * c j x * lieD (b j) G (g * infGL E a (γ x)) ∂ν := by
    funext g
    rw [Finset.sum_apply, ← integral_finsetSum _ fun j _ => hintj j g]
    congr 1
    funext x
    rw [lieD_eq_sum b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (mul_assoc (k x) (c j x) _).symm
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, _, γ, _, hrap j, hG' j, rfl⟩

end GlobalTheory.MSpanDecay
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpan =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperatorStatement\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslate\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealChartRapidKernelOperator\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStable\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperator\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpan\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

namespace GlobalTheory.MSpanDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_add (F G : GA E a → ℂ) (g : GA E a) : chart (F + G) g = chart F g + chart G g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_smul (z : ℂ) (F : GA E a → ℂ) (g : GA E a) : chart (z • F) g = z • chart F g := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem chart_zero (g : GA E a) : chart (0 : GA E a → ℂ) g = 0 := by
  funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]

theorem kSpan_diff : ∀ F ∈ kSpan E a, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a) := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    intro g x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    obtain ⟨L, hL, -⟩ := _root_.GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel E a G X ν k γ hk hG g u
    exact hL.differentiableAt.differentiableWithinAt
  | zero => intro g; rw [chart_zero]; exact differentiableOn_const 0
  | add F G _ _ hF hG => intro g; rw [chart_add]; exact (hF g).add (hG g)
  | smul z F _ hF => intro g; rw [chart_smul]; exact (hF g).const_smul z

theorem differentiableAt_one_of_mem {F : GA E a → ℂ} (hF : F ∈ kSpan E a) (g : GA E a) :
    DifferentiableAt ℝ (chart F g) (oneL E a) :=
  (kSpan_diff F hF g).differentiableAt (isOpen_invSet.mem_nhds isUnit_one)

theorem kSpan_lie : ∀ F ∈ kSpan E a, ∀ Y : Lie E a, lieD Y F ∈ kSpan E a := by
  intro F hF Y
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    have e : lieD Y (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) = fun g : GA E a =>
        ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν := by
      funext g
      obtain ⟨L, hL, hZ⟩ := _root_.GlobalTheory.MSpanDecay.KernelDeriv.hasFDerivAt_chart_kernel E a G X ν k γ hk hG g 1
      have e1 : toL (1 : GL (Fin a) (Cinf E)).val = oneL E a := rfl
      rw [lieD, ← e1, hL.fderiv, hZ Y]
      simp
    rw [e]
    exact _root_.GlobalTheory.MSpanDecay.integral_lieD_conj_mem_kSpan E a G X ν k γ Y hk hG
  | zero =>
    have e : lieD Y (0 : GA E a → ℂ) = 0 := by
      funext g; simp [lieD, chart_zero]
    rw [e]; exact zero_mem _
  | add F G hF' hG' hF hG =>
    have e : lieD Y (F + G) = lieD Y F + lieD Y G := by
      funext g
      simp only [lieD, chart_add, Pi.add_apply]
      rw [fderiv_add (differentiableAt_one_of_mem hF' g) (differentiableAt_one_of_mem hG' g)]
      rfl
    rw [e]; exact add_mem hF hG
  | smul z F hF' hF =>
    have e : lieD Y (z • F) = z • lieD Y F := by
      funext g
      simp only [lieD, chart_smul, Pi.smul_apply]
      rw [fderiv_const_smul (differentiableAt_one_of_mem hF' g)]
      rfl
    rw [e]; exact Submodule.smul_mem _ z hF

theorem kSpan_le_Sm : kSpan E a ≤ Sm E a := _root_.GlobalTheory.SmoothClosure.le_Sm E a _ kSpan_diff kSpan_lie

theorem kSpan_decays_growth : ∀ F ∈ kSpan E a, GlobalTheory.ShortVecDecay.Decays F ∧ Growth F := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨X, _, ν, _, k, γ, G, hk, hG, rfl⟩ := hF
    exact ⟨GlobalTheory.T.decaysAtShortRationalVectors_rapidKernelOperator E a G X ν k γ hk hG.decays, _root_.GlobalTheory.MSpanDecay.growth_kernel E a G X ν k γ hk hG.growth⟩
  | zero => exact ⟨GlobalTheory.ShortVecDecay.Decays.zero, Growth.zero⟩
  | add F G _ _ hF hG => exact ⟨hF.1.add hG.1, hF.2.add hG.2⟩
  | smul z F _ hF => exact ⟨hF.1.smul z, hF.2.smul z⟩

theorem word_mem_kSpan (l : List (Lie E a)) (φ : Sm E a) (hφ : φ.1 ∈ kSpan E a) :
    (GlobalTheory.GLFin.word l φ).1 ∈ kSpan E a := by
  induction l with
  | nil => simpa [GlobalTheory.GLFin.word] using hφ
  | cons Y l ih => rw [word_cons]; exact kSpan_lie _ ih Y

theorem Good.kernel {G : GA E a → ℂ} (hG : Good G) {X : Type} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : GlobalTheory.JSW.IsRapidInf ν k γ) :
    Good (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) := by
  have hm : (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) ∈ kSpan E a :=
    Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, k, γ, G, hk, hG, rfl⟩
  exact ⟨kSpan_le_Sm hm, fun l => kSpan_decays_growth _ (word_mem_kSpan l _ hm)⟩


variable (E a) in
def goodSub : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Good F}
  add_mem' := Good.add
  zero_mem' := good_zero
  smul_mem' c _ h := h.smul c

theorem mspanR_le_goodSub {π : CuspSub E a} (hπ : π.IsUnitary) : GlobalTheory.JSW.mspanR π ≤ goodSub E a :=
  sInf_le ⟨fun φ hφ => good_of_mem hπ hφ, fun F hF h => _root_.GlobalTheory.RtGood.good_mul_right E a F h hF,
    fun F hF X _ ν _ k γ hk => Good.kernel (G := F) hF hk⟩

theorem norm_le_of_short_vector_mspanR : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a), π.IsUnitary → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → ∀ l : List (Lie E a),
    ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
      ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
          ‖(GlobalTheory.GLFin.word l φ).1 (g * c)‖ ≤
            C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E) /
              (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N := by
  intro E _ _ _ a π hπ φ hφ l
  have hg : Good φ.1 := hφ.elim (good_of_mem hπ) fun h => mspanR_le_goodSub hπ h
  obtain ⟨h, hl⟩ := hg
  exact (hl l).1

end GlobalTheory.MSpanDecay
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector =====
