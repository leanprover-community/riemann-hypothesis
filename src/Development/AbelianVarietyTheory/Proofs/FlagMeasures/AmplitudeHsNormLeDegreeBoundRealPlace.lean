module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeDegenerateOperatorNormLeRealPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalDataStatement
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
import Mathlib.Tactic.Lemma
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

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

private lemma hsNormSq_eq_sum_norm_sq {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (J : Wq →L[ℂ] Wp) :
    hsNormSq J = ∑ i, ‖J (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_le_finrank_target_mul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (J : Wq →L[ℂ] Wp) : hsNormSq J ≤ Module.finrank ℂ Wp * ‖J‖ ^ 2 := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : CompleteSpace Wq := FiniteDimensional.complete ℂ Wq

  rw [hsNormSq_eq_sum_norm_sq]
  calc ∑ i, ‖J (stdOrthonormalBasis ℂ Wq i)‖ ^ 2
        = ∑ i, ∑ j, ‖⟪(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j),
            stdOrthonormalBasis ℂ Wq i⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← (stdOrthonormalBasis ℂ Wp).sum_sq_norm_inner_right (J (stdOrthonormalBasis ℂ Wq i))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (stdOrthonormalBasis ℂ Wq).sum_sq_norm_inner_left _
    _ ≤ ∑ _j : Fin (Module.finrank ℂ Wp), ‖J‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hle : ‖(ContinuousLinearMap.adjoint J) (stdOrthonormalBasis ℂ Wp j)‖ ≤ ‖J‖ := by
          calc _ ≤ ‖ContinuousLinearMap.adjoint J‖ * ‖stdOrthonormalBasis ℂ Wp j‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ = ‖J‖ := by
                rw [LinearIsometryEquiv.norm_map, (stdOrthonormalBasis ℂ Wp).orthonormal.1 j, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = Module.finrank ℂ Wp * ‖J‖ ^ 2 := by simp

theorem sqrt_hsNormSq_amplitude_le_degBd : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → ∀ (j : ℕ) (hj : j ≤ D.R.rS) (q : ℕ) (γ : Mat D.R.k D.R.rS) (s H₁ De : ℝ) (μR νR : Measure (Mt D.R.k D.R.rS)), 1 ≤ j → j + 2 ≤ D.R.k → 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ q → 0 < s → 1 ≤ H₁ → TailBd W.z W.νS A.Φ q H₁ → TailBd W.z' W.νS' A.Φ' q H₁ → DeOK D.R.k D.R.rS W.z W.z' γ De → IsNormalFormStabilizerMeasure D.R.k D.R.rS hj W.z W.z' γ s μR → IsQuotMeas W.μG μR νR → Real.sqrt (hsNormSq (A.J νR γ)) ≤ Real.sqrt (Module.finrank ℂ W.Wp) * (((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) / s * degBd D.R.k D.R.rS j q H₁ De (Dj D.R.k D.R.rS hj W.z W.z' γ) (sgV D.R.k D.R.rS W.z W.z' γ H₁)) := by
  intro D τ w w' θ W lam A hv hθ hw hw' hW hS j hj q γ s H₁ De μR νR hj1 hjk hq hs hH hT hT' hDe hN hQ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.amplitude_one_side_of_good_local_data D τ w w' θ W lam A hv hθ hw hw' hW hS
  have hκ : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ) (by positivity)
  have hb := (GlobalTheory.T.amplitude_degenerate_operatorNorm_le_realPlace D.R.k D.R.rS j hj W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' μR νR
    A.Φ A.Φ' γ A.cN _ s H₁ De q hj1 hjk hq hκ hs hH h1 h2 hT hT' hDe hN hQ).2

  calc Real.sqrt (hsNormSq (A.J νR γ))
        ≤ Real.sqrt (Module.finrank ℂ W.Wp * ‖A.J νR γ‖ ^ 2) :=
          Real.sqrt_le_sqrt (hsNormSq_le_finrank_target_mul (A.J νR γ))
    _ = Real.sqrt (Module.finrank ℂ W.Wp) * ‖A.J νR γ‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)

end GlobalTheory.Amp
