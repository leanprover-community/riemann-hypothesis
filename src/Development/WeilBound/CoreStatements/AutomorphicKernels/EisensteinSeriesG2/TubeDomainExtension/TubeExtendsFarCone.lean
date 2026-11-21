import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianIntegrableFiniteDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTimesGaussianBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionFiniteDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftTubeDomain
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftParametrisedIntegral

section
open Filter Topology

namespace EisTube

variable {ι : Type}

def reV (z : ι → ℂ) : ι → ℝ := fun i => (z i).re

def imV (z : ι → ℂ) : ι → ℝ := fun i => (z i).im

def tube (Ω : Set (ι → ℝ)) : Set (ι → ℂ) := {z | reV z ∈ Ω}

def farCone {J : Type*} [Fintype ι] (a : J → ι → ℝ) (R : ℝ) : Set (ι → ℝ) :=
  {x | ∀ j, R < ∑ i, x i * a j i}

def TubeExtends [Fintype ι] (P : Type*) [TopologicalSpace P] [FirstCountableTopology P] : Prop :=
  ∀ (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
  (∀ x : ι → ℝ, ∃ x₁ ∈ Ω, ∃ x₂ ∈ Ω, x = midpoint ℝ x₁ x₂) →
  ∀ (h : P → ℝ), (∀ p, 0 ≤ h p) → (∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U)) →
  ∀ (F : (ι → ℂ) → P → ℂ),
  (∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) →
  (∀ z ∈ tube Ω, Continuous (F z)) →
  (∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N) →
  ∃ G : (ι → ℂ) → P → ℂ,
    (∀ p, Differentiable ℂ (fun z => G z p)) ∧
    (∀ z ∈ tube Ω, ∀ p, G z p = F z p) ∧
    Continuous (Function.uncurry G) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p, ‖G z p‖ ≤ C * h p)

end EisTube
end

section
universe u

namespace EisTube

theorem gaussInt : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c →
    MeasureTheory.Integrable (fun y : ι → ℝ => Real.exp (-(c * ∑ i, y i ^ 2))) :=
  GlobalTheory.T.gaussian_integrable_finite_dim

theorem polyGaussBdd : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c → ∀ N : ℕ, ∃ M : ℝ, ∀ y : ι → ℝ,
    (1 + ‖y‖) ^ N * Real.exp (-(c * ∑ i, y i ^ 2)) ≤ M :=
  GlobalTheory.T.polynomial_times_gaussian_bounded

theorem fourierInvCoord : ∀ (ι : Type) [Fintype ι] (g : (ι → ℝ) → ℂ), Continuous g → MeasureTheory.Integrable g →
    MeasureTheory.Integrable (fun t : ι → ℝ =>
      ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) →
    ∀ y : ι → ℝ, (∫ t : ι → ℝ, (∫ y', g y' * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) = g y :=
  GlobalTheory.T.fourier_inversion_finite_dim

theorem tubeShift : ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
    ∀ H : (ι → ℂ) → ℂ, DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω} →
    (∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2)) →
    ∀ x₁ ∈ Ω, ∀ x₂ ∈ Ω,
      (∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I)) =
        ∫ y : ι → ℝ, H (fun i => (x₂ i : ℂ) + (y i : ℂ) * Complex.I) :=
  GlobalTheory.T.contour_shift_tube_domain

theorem laplaceEntire : ∀ (ι : Type) [Fintype ι] (P : Type u) [TopologicalSpace P] [FirstCountableTopology P] (h : P → ℝ), (∀ p, 0 ≤ h p) →
    (∀ p, ∃ U ∈ nhds p, BddAbove (h '' U)) →
    ∀ ψ : P → (ι → ℝ) → ℂ, (∀ p, MeasureTheory.AEStronglyMeasurable (ψ p)) →
    (∀ t, Continuous (fun p => ψ p t)) →
    (∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i))) →
    (∀ p (z : ι → ℂ), MeasureTheory.Integrable
        (fun t : ι → ℝ => ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    (∀ p, Differentiable ℂ (fun z : ι → ℂ =>
        ∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    Continuous (fun q : (ι → ℂ) × P =>
        ∫ t : ι → ℝ, ψ q.2 t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, q.1 i * t i)) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p,
        ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖ ≤ C * h p) :=
  GlobalTheory.T.contour_shift_parametrised_integral

end EisTube
end

section
open Filter Topology MeasureTheory

namespace EisTube

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

variable {ι : Type} [Fintype ι]

def cz (x y : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ) + (y i : ℂ) * Complex.I

lemma reV_cz (x y : ι → ℝ) : reV (cz x y) = x := by
  funext i; simp [reV, cz]

lemma imV_cz (x y : ι → ℝ) : imV (cz x y) = y := by
  funext i; simp [imV, cz]


lemma continuous_cz_right (x : ι → ℝ) : Continuous (fun y : ι → ℝ => cz x y) := by
  unfold cz; fun_prop

lemma sum_cz_mul (x y t : ι → ℝ) :
    ∑ i, cz x y i * (t i : ℂ) =
      ((∑ i, x i * t i : ℝ) : ℂ) + ((∑ i, y i * t i : ℝ) : ℂ) * Complex.I := by
  simp only [cz, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma norm_exp_sq_cz (x y : ι → ℝ) :
    ‖Complex.exp (∑ i, cz x y i ^ 2)‖ =
      Real.exp (∑ i, x i ^ 2) * Real.exp (-∑ i, y i ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add, Complex.re_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [cz, sq, Complex.mul_re]

noncomputable def kern (z : ι → ℂ) (t : ι → ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ i, z i * t i)

lemma norm_kern_cz (x y t : ι → ℝ) :
    ‖kern (cz x y) t‖ = Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) := by
  rw [kern, sum_cz_mul, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]



lemma gauss2 : Integrable (fun y : ι → ℝ => Real.exp (-(∑ i, y i ^ 2) / 2)) := by
  have := gaussInt ι (1 / 2) (by norm_num)
  refine this.congr (ae_of_all _ fun y => ?_)
  simp only
  congr 1; ring



lemma cz_mem_tube {Ω : Set (ι → ℝ)} {x : ι → ℝ} (hx : x ∈ Ω) (y : ι → ℝ) : cz x y ∈ tube Ω := by
  show reV (cz x y) ∈ Ω
  rw [reV_cz]; exact hx

section
variable {P : Type*} [TopologicalSpace P]

noncomputable def gf (F : (ι → ℂ) → P → ℂ) (z : ι → ℂ) (p : P) : ℂ :=
  F z p * Complex.exp (∑ i, z i ^ 2)

lemma gf_bound {Ω : Set (ι → ℝ)} {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {K : Set (ι → ℝ)} (hK : K ⊆ Ω) (hKc : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ (y : ι → ℝ) p,
      ‖gf F (cz x y) p‖ ≤ C * h p * Real.exp (-(∑ i, y i ^ 2) / 2) := by
  obtain ⟨C, N, hC⟩ := hbd K hK hKc
  obtain ⟨M, hM⟩ := polyGaussBdd ι (1 / 2) (by norm_num) N
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  obtain ⟨S, hS⟩ : BddAbove ((fun x : ι → ℝ => ∑ i, x i ^ 2) '' K) :=
    hKc.bddAbove_image (by fun_prop)
  refine ⟨|C| * Real.exp S * M, by positivity, fun x hx y p => ?_⟩
  have hxS : ∑ i, x i ^ 2 ≤ S := hS ⟨x, hx, rfl⟩
  have hF := hC (cz x y) (by rw [reV_cz]; exact hx) p
  rw [imV_cz] at hF
  have hF' : ‖F (cz x y) p‖ ≤ |C| * h p * (1 + ‖y‖) ^ N :=
    hF.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (h0 p)) (by positivity))
  have e1 : Real.exp (-∑ i, y i ^ 2) =
      Real.exp (-(1 / 2 * ∑ i, y i ^ 2)) * Real.exp (-(∑ i, y i ^ 2) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hB := hM y
  have hA : 0 ≤ |C| * h p := mul_nonneg (abs_nonneg _) (h0 p)
  rw [gf, norm_mul, norm_exp_sq_cz, e1]
  calc ‖F (cz x y) p‖ * (Real.exp (∑ i, x i ^ 2) *
          (Real.exp (-(1 / 2 * ∑ i, y i ^ 2)) * Real.exp (-(∑ i, y i ^ 2) / 2)))
      ≤ (|C| * h p * (1 + ‖y‖) ^ N) * (Real.exp (∑ i, x i ^ 2) *
          (Real.exp (-(1 / 2 * ∑ i, y i ^ 2)) * Real.exp (-(∑ i, y i ^ 2) / 2))) :=
        mul_le_mul_of_nonneg_right hF' (by positivity)
    _ = (|C| * h p) * Real.exp (∑ i, x i ^ 2) *
          ((1 + ‖y‖) ^ N * Real.exp (-(1 / 2 * ∑ i, y i ^ 2))) *
          Real.exp (-(∑ i, y i ^ 2) / 2) := by ring
    _ ≤ (|C| * h p) * Real.exp S * M * Real.exp (-(∑ i, y i ^ 2) / 2) := by
        gcongr
    _ = |C| * Real.exp S * M * h p * Real.exp (-(∑ i, y i ^ 2) / 2) := by ring

lemma gf_diff {Ω : Set (ι → ℝ)} {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) (p : P) (t : ι → ℝ) :
    DifferentiableOn ℂ (fun z => gf F z p * kern z t) (tube Ω) := by
  unfold gf kern
  refine ((hhol p).mul ?_).mul ?_ <;> apply Differentiable.differentiableOn <;> fun_prop

lemma gf_cont {Ω : Set (ι → ℝ)} {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) (p : P) {x : ι → ℝ} (hx : x ∈ Ω) :
    Continuous (fun y => gf F (cz x y) p) := by
  have : DifferentiableOn ℂ (fun z => gf F z p) (tube Ω) := by
    unfold gf
    exact (hhol p).mul (Differentiable.differentiableOn (by fun_prop))
  exact this.continuousOn.comp_continuous (continuous_cz_right x) (cz_mem_tube hx)

noncomputable def psiAt (F : (ι → ℂ) → P → ℂ) (x : ι → ℝ) (p : P) (t : ι → ℝ) : ℂ :=
  ∫ y, gf F (cz x y) p * kern (cz x y) t

lemma psi_indep {Ω : Set (ι → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₁ x₂ : ι → ℝ} (h₁ : x₁ ∈ Ω) (h₂ : x₂ ∈ Ω) (p : P) (t : ι → ℝ) :
    psiAt F x₁ p t = psiAt F x₂ p t := by
  refine tubeShift ι Ω hΩo hΩc (fun z => gf F z p * kern z t) (gf_diff hhol p t) ?_ x₁ h₁ x₂ h₂
  intro K hK hKc
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd hK hKc
  obtain ⟨Q, hQ⟩ : BddAbove ((fun x : ι → ℝ => Real.exp (-(2 * Real.pi * ∑ i, x i * t i))) '' K) :=
    hKc.bddAbove_image (by fun_prop)
  refine ⟨C * h p * Q, fun x hx y => ?_⟩
  show ‖gf F (cz x y) p * kern (cz x y) t‖ ≤ _
  rw [norm_mul, norm_kern_cz]
  have hq : Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) ≤ Q := hQ ⟨x, hx, rfl⟩
  calc ‖gf F (cz x y) p‖ * Real.exp (-(2 * Real.pi * ∑ i, x i * t i))
      ≤ (C * h p * Real.exp (-(∑ i, y i ^ 2) / 2)) * Q :=
        mul_le_mul (hC x hx y p) hq (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hC0 (h0 p)) (Real.exp_pos _).le)
    _ = C * h p * Q * Real.exp (-(∑ i, y i ^ 2) / 2) := by ring

end

section
variable {P : Type*} [TopologicalSpace P]



lemma psi_meas {Ω : Set (ι → ℝ)} {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (p : P) :
    AEStronglyMeasurable (psiAt F x₀ p) := by
  have hc : Continuous (fun q : (ι → ℝ) × (ι → ℝ) => gf F (cz x₀ q.2) p * kern (cz x₀ q.2) q.1) := by
    refine ((gf_cont hhol p h₀).comp continuous_snd).mul ?_
    unfold kern cz; fun_prop
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

lemma psi_cont [FirstCountableTopology P] {Ω : Set (ι → ℝ)} {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p)
    (hloc : ∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U)) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hcont : ∀ z ∈ tube Ω, Continuous (F z))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (t : ι → ℝ) :
    Continuous (fun p => psiAt F x₀ p t) := by
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd (Set.singleton_subset_iff.2 h₀) isCompact_singleton
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨U, hU, B, hB⟩ := hloc p₀
  set E := Real.exp (-(2 * Real.pi * ∑ i, x₀ i * t i))
  refine continuousAt_of_dominated (bound := fun y => (C * B * E) * Real.exp (-(∑ i, y i ^ 2) / 2))
    (Eventually.of_forall fun p => ?_) ?_ (gauss2.const_mul _) (ae_of_all _ fun y => ?_)
  · exact ((gf_cont hhol p h₀).mul (by unfold kern cz; fun_prop)).aestronglyMeasurable
  · filter_upwards [hU] with p hp
    refine ae_of_all _ fun y => ?_
    rw [norm_mul, norm_kern_cz]
    have hBp : h p ≤ B := hB ⟨p, hp, rfl⟩
    calc ‖gf F (cz x₀ y) p‖ * E ≤ (C * h p * Real.exp (-(∑ i, y i ^ 2) / 2)) * E :=
          mul_le_mul_of_nonneg_right (hC x₀ (Set.mem_singleton x₀) y p) (Real.exp_pos _).le
      _ ≤ (C * B * Real.exp (-(∑ i, y i ^ 2) / 2)) * E := by
          gcongr
      _ = _ := by ring
  · have : Continuous (fun p => gf F (cz x₀ y) p) := by
      unfold gf
      exact (hcont _ (cz_mem_tube h₀ y)).mul continuous_const
    exact (this.mul continuous_const).continuousAt

end

section
variable {P : Type*} [TopologicalSpace P]


end



end EisTube
end
