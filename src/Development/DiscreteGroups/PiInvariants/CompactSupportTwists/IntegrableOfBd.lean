import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IntegralMulRightFd
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAut

noncomputable section

set_option linter.all false

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc GlobalTheory.ExpDeriv

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

def PairBd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (ψ φ : Sm E n) (u : ℝ → ℂ) (Ω : Set (GA E n)), IsCuspForm ψ → (∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) →
  IsAutForm φ → Continuous u → HasCompactSupport u → IsCompact Ω →
  ∃ C : ℝ, (∀ x : H E n 0, ∀ y ∈ Ω, ∀ y' ∈ Ω, ‖ψ.1 (x.1 * y) * u (ldet x) * φ.1 (x.1 * y')‖ ≤ C) ∧
    D.ν {x | u (ldet x) ≠ 0} < ⊤

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cont_infGL : Continuous (infGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)



theorem major_one (v : ℝ → ℂ) {M R : ℝ} (hM : ∀ x, ‖v x‖ ≤ M) (hR : tsupport v ⊆ Metric.closedBall 0 R) (c : ℝ)
    {R' M' : ℝ} (hRR : R ≤ R') (hMM : M ≤ M') (hM0 : 0 ≤ M') (s t : ℝ) (ht : |t| ≤ 1) :
    ‖v (s + t * c)‖ ≤ M' * max 0 (min 1 (R' + |c| + 1 - |s|)) := by
  by_cases h : s + t * c ∈ tsupport v
  · have h1 := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    have h2 : |t * c| ≤ |c| := by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht
    obtain ⟨a1, a2⟩ := abs_le.1 h1
    obtain ⟨b1, b2⟩ := abs_le.1 h2
    have h3 : |s| ≤ R' + |c| := abs_le.2 ⟨by linarith, by linarith⟩
    rw [min_eq_left (by linarith), max_eq_right zero_le_one, mul_one]
    exact (hM _).trans hMM
  · have h0 : v (s + t * c) = 0 := by
      by_contra hne
      exact h (subset_tsupport _ (Function.mem_support.2 hne))
    rw [h0, norm_zero]
    exact mul_nonneg hM0 (le_max_left _ _)

theorem exists_major (v₁ v₂ : ℝ → ℂ) (h₁ : Continuous v₁) (h₂ : Continuous v₂) (s₁ : HasCompactSupport v₁)
    (s₂ : HasCompactSupport v₂) (c : ℝ) : ∃ w : ℝ → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ s, 0 ≤ w s) ∧
      ∀ s t, |t| ≤ 1 → ‖v₁ (s + t * c)‖ ≤ w s ∧ ‖v₂ (s + t * c)‖ ≤ w s := by
  obtain ⟨M₁, hM₁⟩ := h₁.bounded_above_of_compact_support s₁
  obtain ⟨M₂, hM₂⟩ := h₂.bounded_above_of_compact_support s₂
  obtain ⟨R₁, hR₁⟩ := s₁.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨R₂, hR₂⟩ := s₂.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set R := max R₁ R₂
  set M := max M₁ 0 + max M₂ 0
  have hM0 : 0 ≤ M := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨fun s => M * max 0 (min 1 (R + |c| + 1 - |s|)), ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul (continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs)))
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R + |c| + 1)) fun s hs => ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hs
    have : min 1 (R + |c| + 1 - |s|) ≤ 0 := (min_le_right _ _).trans (by linarith)
    simp only [max_eq_left this, mul_zero]
  · exact fun s => mul_nonneg hM0 (le_max_left _ _)
  · intro s t ht
    exact ⟨major_one v₁ hM₁ hR₁ c (le_max_left _ _) ((le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _)))
        hM0 s t ht,
      major_one v₂ hM₂ hR₂ c (le_max_right _ _) ((le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _)))
        hM0 s t ht⟩

theorem pt_bd {a b v : ℂ} {s k C : ℝ} (hs : 0 ≤ s) (hk : 0 ≤ k) (hv : ‖v‖ ≤ k * s)
    (h : ‖a * ((s : ℝ) : ℂ) * b‖ ≤ C) : ‖star (a * v) * b‖ ≤ k * C ∧ (s = 0 → star (a * v) * b = 0) := by
  have e : ‖a * ((s : ℝ) : ℂ) * b‖ = ‖a‖ * s * ‖b‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  have h1 : ‖star (a * v) * b‖ ≤ k * (‖a‖ * s * ‖b‖) := by
    rw [norm_mul, norm_star, norm_mul]
    calc ‖a‖ * ‖v‖ * ‖b‖ ≤ ‖a‖ * (k * s) * ‖b‖ := by gcongr
      _ = k * (‖a‖ * s * ‖b‖) := by ring
  refine ⟨h1.trans (mul_le_mul_of_nonneg_left (by rw [← e]; exact h) hk), fun h0 => ?_⟩
  rw [h0] at h1
  simp only [mul_zero, zero_mul] at h1
  exact norm_le_zero_iff.1 h1




end DiscreteGroups.T1.G

end
