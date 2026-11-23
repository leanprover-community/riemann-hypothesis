module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTruncatedFourierTendstoZeroEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHeightSqLintegralLtTopStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerBoundBigCellStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LTwoLemma
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem u_locallyConstant (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    IsLocallyConstant (fun z => Ψ (wS A.K * nS z)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  obtain ⟨U, hU, hinv⟩ := h.1
  have h0 : (0 : A.K) ∈ U := mem_of_mem_nhds hU
  have ht : Tendsto (fun y : A.K => y - z) (𝓝 z) (𝓝 0) :=
    (continuous_sub_right z).tendsto' z 0 (sub_self z)
  filter_upwards [ht hU] with y hy
  simp only [Set.mem_preimage] at hy
  have he : wS A.K * nS y = (wS A.K * nS z) * nS (y - z) := by
    rw [mul_assoc]; congr 1; apply Subtype.ext
    show !![(1 : A.K), y; 0, 1] = !![1, z; 0, 1] * !![1, y - z; 0, 1]
    rw [Matrix.mul_fin_two]; simp
  rw [he]
  apply hinv
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nS, h0, hy]

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK; split_ifs <;> simp

theorem weyl_unipotent_l2_finite [Unram F E] (hB1 : type_of% GlobalTheory.T.whittaker_bound_big_cell) (hB2 : type_of% GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top) (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure)
    (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ < ⊤ := by
  obtain ⟨C, hC⟩ := hB1 F E A Ψ h
  have hB := hB2 F E A μ hμ
  have h0 : ENNReal.ofReal C + 1 ≠ 0 := by simp
  have hT : ENNReal.ofReal C + 1 ≠ ⊤ := by simp
  have hle : ∀ z, ‖Ψ (wS A.K * nS z)‖ₑ ≤ (ENNReal.ofReal C + 1) *
      ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK,
        α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s) := by
    intro z
    simp only [ENNReal.mul_iInf_of_ne h0 hT]
    refine le_iInf₂ fun s hs => ?_
    obtain ⟨hs1, hs2, α, hα, β, hβ, he⟩ := hs
    have hb := hC z s α β hα hβ hs1 hs2 he
    calc ‖Ψ (wS A.K * nS z)‖ₑ = ENNReal.ofReal ‖Ψ (wS A.K * nS z)‖ := (ofReal_norm_eq_enorm _).symm
      _ ≤ ENNReal.ofReal (C * A.absK s) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal C * ENNReal.ofReal (A.absK s) := ENNReal.ofReal_mul' (absK_nonneg A _)
      _ ≤ _ := by gcongr; exact le_self_add
  calc ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ z, ((ENNReal.ofReal C + 1) * ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ :=
        lintegral_mono fun z => pow_le_pow_left' (hle z) 2
    _ = (ENNReal.ofReal C + 1) ^ 2 * ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ := by
        simp_rw [mul_pow]
        exact lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hB

end GlobalTheory.JR.LTwoLemma

open GlobalTheory.JR.LTwoLemma in
theorem GlobalTheory.JR.kirillov_vanishing_l2 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd Ψ hI hlim
  have hμ : μK.IsAddHaarMeasure := hsd.1
  have hu : (fun z => Ψ (wS A.K * nS z)) = 0 :=
    GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale F E A ψ hψ μK hsd _ (u_locallyConstant A Ψ hI) (weyl_unipotent_l2_finite GlobalTheory.T.whittaker_bound_big_cell GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top A μK hμ Ψ hI) hlim
  have h1 : ∀ z, Ψ (wS A.K * nS z) = 0 := fun z => congrFun hu z
  exact ⟨h1, GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero F E A ψ μK hμ Ψ hI h1⟩
