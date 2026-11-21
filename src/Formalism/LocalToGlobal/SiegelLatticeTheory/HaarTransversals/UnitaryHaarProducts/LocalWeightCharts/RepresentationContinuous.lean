import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.RepresentationUnitary

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.WuDecay Formalism.L2.SG.SplitPrimeNormLemmas

variable {k r : ℕ}

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem gr_left_inv {g : Mat k r} (hg : g ∈ Gr k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem gr_isUnit {g : Mat k r} (hg : g ∈ Gr k r) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (gr_left_inv hg)

theorem gr_inv_eq {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (gr_left_inv hg)

theorem gr_one : (1 : Mat k r) ∈ Gr k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem gr_mul {g h : Mat k r} (hg : g ∈ Gr k r) (hh : h ∈ Gr k r) : g * h ∈ Gr k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem gr_isClosed : IsClosed (Gr k r) := by
  have : Gr k r = (fun g : Mat k r => gᴴ * Hpk k r * g) ⁻¹' {Hpk k r} := rfl
  rw [this]
  exact isClosed_singleton.preimage
    (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id)

theorem opn_nonneg (M : Mat k r) : 0 ≤ opn M := norm_nonneg _

theorem opn_mul (A B : Mat k r) : opn (A * B) ≤ opn A * opn B := by
  unfold opn
  rw [map_mul]
  exact norm_mul_le _ _

theorem opn_conjTranspose (A : Mat k r) : opn Aᴴ = opn A := by
  unfold opn
  rw [← Matrix.star_eq_conjTranspose, map_star, norm_star]

local instance instAlgCLM (n : ℕ) :
    Algebra ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.algebra
local instance instModCLM (n : ℕ) :
    Module ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.module

theorem opn_continuous : Continuous (fun M : Mat k r => opn M) := by
  unfold opn
  have h : Continuous (fun M : Mat k r => Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) M) :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap)
  exact continuous_norm.comp h

theorem opn_inv_le {g : Mat k r} (hg : g ∈ Gr k r) :
    opn g⁻¹ ≤ opn (Hpk k r) * opn (Hpk k r) * opn g := by
  rw [gr_inv_eq hg]
  calc opn (Hpk k r * gᴴ * Hpk k r) ≤ opn (Hpk k r * gᴴ) * opn (Hpk k r) := opn_mul _ _
    _ ≤ opn (Hpk k r) * opn gᴴ * opn (Hpk k r) :=
        mul_le_mul_of_nonneg_right (opn_mul _ _) (opn_nonneg _)
    _ = opn (Hpk k r) * opn (Hpk k r) * opn g := by rw [opn_conjTranspose]; ring

theorem opn_le_mul_inv (y : Mat k r) {t : Mat k r} (ht : t ∈ Gr k r) :
    opn y ≤ opn (y * t) * opn t⁻¹ := by
  have : y = y * t * t⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gr_isUnit ht), Matrix.mul_one]
  calc opn y = opn (y * t * t⁻¹) := by rw [← this]
    _ ≤ _ := opn_mul _ _

theorem opn_pos {g : Mat k r} (hg : g ∈ Gr k r) : 0 < opn g := by
  rcases (opn_nonneg g).lt_or_eq with h | h
  · exact h
  · exfalso
    have h1 : opn (1 : Mat k r) ≤ opn g * opn g⁻¹ := by
      rw [← Matrix.mul_nonsing_inv _ (gr_isUnit hg)]; exact opn_mul _ _
    rw [← h, zero_mul] at h1
    have h2 : opn (1 : Mat k r) = 1 := by
      unfold opn; rw [map_one]; exact norm_one
    linarith

theorem nilradical_half_sum_nonneg : 0 ≤ N1H k r := by unfold N1H; positivity

def lmulH {y : Mat k r} (hy : y ∈ Gr k r) : Mt k r ≃ₜ Mt k r where
  toFun x := lmulM y x
  invFun x := lmulM y⁻¹ x
  left_inv x := by
    show y⁻¹ * (y * Matrix.of x) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gr_isUnit hy), Matrix.one_mul]
  right_inv x := by
    show y * (y⁻¹ * Matrix.of x) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gr_isUnit hy), Matrix.one_mul]
  continuous_toFun := by
    show Continuous fun x : Mat k r => y * x
    exact continuous_const.matrix_mul continuous_id
  continuous_invFun := by
    show Continuous fun x : Mat k r => y⁻¹ * x
    exact continuous_const.matrix_mul continuous_id

theorem lint_lmul {μ : Measure (Mt k r)} {y : Mat k r} (hy : y ∈ Gr k r)
    (hinv : μ.map (lmulM y) = μ) (F : Mt k r → ℝ≥0∞) :
    ∫⁻ t, F (lmulM y t) ∂μ = ∫⁻ t, F t ∂μ := by
  have h := lintegral_map_equiv F (lmulH hy).toMeasurableEquiv (μ := μ)
  have e : μ.map (lmulH hy).toMeasurableEquiv = μ.map (lmulM y) := rfl
  rw [e, hinv] at h
  exact h.symm

theorem ae_gr {μ : Measure (Mt k r)} (hconc : μ {x | Matrix.of x ∉ Gr k r} = 0) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ Gr k r :=
  ae_iff.mpr hconc

section Decay

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat k r → (H →L[ℂ] H)}

theorem inner_iso (hσ : IsURepOn (Gr k r) σ) {x : Mat k r} (hx : x ∈ Gr k r) (u v : H) :
    ⟪σ x u, σ x v⟫_ℂ = ⟪u, v⟫_ℂ :=
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ x).toLinearMap, norm_map' := hσ.2.1 x hx }
  L.inner_map_map u v

theorem sigma_mul (hσ : IsURepOn (Gr k r) σ) {x y : Mat k r} (hx : x ∈ Gr k r) (hy : y ∈ Gr k r)
    (v : H) : σ (x * y) v = σ x (σ y v) := by
  rw [hσ.1.2 x hx y hy]; rfl

theorem coef_weighted_transl (hσ : IsURepOn (Gr k r) σ) {μ : Measure (Mt k r)}
    (hconc : μ {x | Matrix.of x ∉ Gr k r} = 0) (hinv : ∀ s ∈ Gr k r, μ.map (lmulM s) = μ)
    (w : H) {x₀ : Mat k r} (hx₀ : x₀ ∈ Gr k r) :
    ∫⁻ g, ‖⟪σ x₀ w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μ ≤
      ENNReal.ofReal (opn x₀ ^ N1H k r) *
        ∫⁻ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μ := by
  rw [← lint_lmul hx₀ (hinv x₀ hx₀), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_gr hconc] with g hg
  show ‖⟪σ x₀ w, σ (x₀ * Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (x₀ * Matrix.of g) ^ N1H k r) ≤
    ENNReal.ofReal (opn x₀ ^ N1H k r) *
      (‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r))
  rw [sigma_mul hσ hx₀ hg, inner_iso hσ hx₀]
  have h1 : opn (x₀ * Matrix.of g) ^ N1H k r ≤ opn x₀ ^ N1H k r * opn (Matrix.of g) ^ N1H k r := by
    rw [← Real.mul_rpow (opn_nonneg _) (opn_nonneg _)]
    exact Real.rpow_le_rpow (opn_nonneg _) (opn_mul _ _) nilradical_half_sum_nonneg
  calc ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (x₀ * Matrix.of g) ^ N1H k r)
      ≤ ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ *
          (ENNReal.ofReal (opn x₀ ^ N1H k r) * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r)) := by
        gcongr
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (opn_nonneg _) _)]
        exact ENNReal.ofReal_le_ofReal h1
    _ = _ := by ring

theorem coef_reprod (hσ : IsURepOn (Gr k r) σ) {μ : Measure (Mt k r)} {w : H}
    {α : Mat k r → ℂ} {Ω : Set (Mat k r)} (hΩG : Ω ⊆ Gr k r) (hsupp : ∀ y, α y ≠ 0 → y ∈ Ω)
    (hint : Integrable (fun g : Mt k r => α (Matrix.of g) • σ (Matrix.of g) w) μ)
    (hrep : ∫ g, α (Matrix.of g) • σ (Matrix.of g) w ∂μ = w) (u : H) {y : Mat k r}
    (hy : y ∈ Gr k r) :
    ⟪u, σ y w⟫_ℂ = ∫ t, α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ ∂μ := by
  calc ⟪u, σ y w⟫_ℂ = ⟪u, σ y (∫ g, α (Matrix.of g) • σ (Matrix.of g) w ∂μ)⟫_ℂ := by rw [hrep]
    _ = ⟪u, ∫ g, σ y (α (Matrix.of g) • σ (Matrix.of g) w) ∂μ⟫_ℂ := by
        rw [(σ y).integral_comp_comm hint]
    _ = ∫ g, ⟪u, σ y (α (Matrix.of g) • σ (Matrix.of g) w)⟫_ℂ ∂μ :=
        (integral_inner ((σ y).integrable_comp hint) u).symm
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        by_cases hα : α (Matrix.of t) = 0
        · simp [hα]
        · have ht := hΩG (hsupp _ hα)
          show ⟪u, σ y (α (Matrix.of t) • σ (Matrix.of t) w)⟫_ℂ =
            α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ
          rw [map_smul, inner_smul_right, sigma_mul hσ hy ht]

theorem pt_decay_core (hσ : IsURepOn (Gr k r) σ) {μ : Measure (Mt k r)}
    (hinv : ∀ s ∈ Gr k r, μ.map (lmulM s) = μ) {w : H}
    {α : Mat k r → ℂ} {Ω : Set (Mat k r)} {a : ℝ} (hΩ : IsCompact Ω) (hΩG : Ω ⊆ Gr k r)
    (hsupp : ∀ y, α y ≠ 0 → y ∈ Ω) (hbd : ∀ y, ‖α y‖ ≤ a)
    (hint : Integrable (fun g : Mt k r => α (Matrix.of g) • σ (Matrix.of g) w) μ)
    (hrep : ∫ g, α (Matrix.of g) • σ (Matrix.of g) w ∂μ = w) (u : H) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ y ∈ Gr k r,
      ‖⟪u, σ y w⟫_ℂ‖ₑ * ENNReal.ofReal (opn y ^ N1H k r) ≤
        K * ∫⁻ g, ‖⟪u, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μ := by
  obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn (opn_continuous (k := k) (r := r)).continuousOn
  set M := opn (Hpk k r) * opn (Hpk k r) * max B 0 with hMdef
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (opn_nonneg _) (opn_nonneg _)) (le_max_right _ _)
  have hMt : ∀ t ∈ Ω, opn t⁻¹ ≤ M := by
    intro t ht
    refine (opn_inv_le (hΩG ht)).trans ?_
    have : opn t ≤ max B 0 := le_max_of_le_left ((Real.le_norm_self _).trans (hB t ht))
    rw [hMdef]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg (opn_nonneg _) (opn_nonneg _))
  have ha : 0 ≤ a := (norm_nonneg _).trans (hbd 0)
  have hN := nilradical_half_sum_nonneg (k := k) (r := r)
  refine ⟨ENNReal.ofReal (a * M ^ N1H k r), ENNReal.ofReal_ne_top, fun y hy => ?_⟩
  rw [coef_reprod hσ hΩG hsupp hint hrep u hy]
  set F : Mt k r → ℝ≥0∞ := fun g =>
    ‖⟪u, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) with hF
  calc ‖∫ t, α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ ∂μ‖ₑ * ENNReal.ofReal (opn y ^ N1H k r)
      ≤ (∫⁻ t, ‖α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ₑ ∂μ) *
          ENNReal.ofReal (opn y ^ N1H k r) := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ t, ‖α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ₑ *
          ENNReal.ofReal (opn y ^ N1H k r) ∂μ :=
        (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ t, ENNReal.ofReal (a * M ^ N1H k r) * F (lmulM y t) ∂μ := by
        apply lintegral_mono
        intro t
        show ‖α (Matrix.of t) * ⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn y ^ N1H k r) ≤
          ENNReal.ofReal (a * M ^ N1H k r) * (‖⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ₑ *
            ENNReal.ofReal (opn (y * Matrix.of t) ^ N1H k r))
        by_cases hα : α (Matrix.of t) = 0
        · simp [hα]
        · have htΩ := hsupp _ hα
          have ht := hΩG htΩ
          have h1 : opn y ^ N1H k r ≤ opn (y * Matrix.of t) ^ N1H k r * M ^ N1H k r := by
            rw [← Real.mul_rpow (opn_nonneg _) hM]
            refine Real.rpow_le_rpow (opn_nonneg _) ?_ hN
            exact (opn_le_mul_inv y ht).trans
              (mul_le_mul_of_nonneg_left (hMt _ htΩ) (opn_nonneg _))
          rw [← ofReal_norm, ← ofReal_norm,
            ← ENNReal.ofReal_mul (norm_nonneg _),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [norm_mul]
          calc ‖α (Matrix.of t)‖ * ‖⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ * opn y ^ N1H k r
              ≤ a * ‖⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ *
                  (opn (y * Matrix.of t) ^ N1H k r * M ^ N1H k r) := by
                exact mul_le_mul (mul_le_mul_of_nonneg_right (hbd _) (norm_nonneg _)) h1
                  (Real.rpow_nonneg (opn_nonneg _) _) (mul_nonneg ha (norm_nonneg _))
            _ = a * M ^ N1H k r * (‖⟪u, σ (y * Matrix.of t) w⟫_ℂ‖ *
                  opn (y * Matrix.of t) ^ N1H k r) := by ring
    _ = ENNReal.ofReal (a * M ^ N1H k r) * ∫⁻ t, F t ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lint_lmul hy (hinv y hy)]

end Decay

def PtDecay : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)) (w : H) (μG μS ν μW μN : Measure (Mt k r)),
    Hyp k r z c u v b σ π w μG μS ν μW μN →
    Formalism.L2.SG.HCReprodM.HCReprodDSm → CoefWeightedLoc → ∀ x₀ ∈ Gr k r,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Gr k r, ‖⟪σ x₀ w, σ y w⟫_ℂ‖ * opn y ^ N1H k r ≤ C

theorem ptDecay_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) : PtDecay := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀
  have hdec := hD hC k r z c u v b H σ Vp π w μG μS ν μW μN hH
  obtain ⟨α, Ω, a, hΩ, hΩG, _, hsupp, hbd, hint, hrep⟩ :=
    hRG hR k r z c u v b H σ Vp π w μG μS ν μW μN hH
  obtain ⟨_, hDS, _, _, hμG, _⟩ := hH
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨_, _, hconc, hinv⟩ := hμG
  obtain ⟨K, hK, hbound⟩ := pt_decay_core hσ hinv hΩ hΩG hsupp hbd hint hrep (σ x₀ w)
  have htr := coef_weighted_transl hσ hconc hinv w hx₀
  set D := ∫⁻ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG
  have hfin : K * (ENNReal.ofReal (opn x₀ ^ N1H k r) * D) ≠ ⊤ :=
    ENNReal.mul_ne_top hK (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdec.ne)
  refine ⟨(K * (ENNReal.ofReal (opn x₀ ^ N1H k r) * D)).toReal, ENNReal.toReal_nonneg, fun y hy => ?_⟩
  have hE : ‖⟪σ x₀ w, σ y w⟫_ℂ‖ₑ * ENNReal.ofReal (opn y ^ N1H k r) ≤
      K * (ENNReal.ofReal (opn x₀ ^ N1H k r) * D) := (hbound y hy).trans (by gcongr)
  have hnn : 0 ≤ ‖⟪σ x₀ w, σ y w⟫_ℂ‖ * opn y ^ N1H k r :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _)
  rw [← ENNReal.toReal_ofReal hnn, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  exact ENNReal.toReal_mono hfin hE

end WlocSk.PtD
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.WuDecay Formalism.L2.SG.SplitPrimeNormLemmas

variable {k r : ℕ}

def UWComp : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsCompact (UWset k r z)

theorem psiGen_norm (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat k r) :
    ‖psiGen k r z c g‖ = 1 := by
  unfold psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

section Bound

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Vp →L[ℂ] Vp)}

theorem bInt_bound (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hσ : IsURepOn (Gr k r) σ)
    {w w' : H} {Cφ : ℝ} (hCφ : ∀ y ∈ Gr k r, ‖⟪w', σ y w⟫_ℂ‖ * opn y ^ N1H k r ≤ Cφ)
    {Kw : ℝ} (hKw0 : 0 ≤ Kw) (ξ : Vp) (p : Mt k r × Mt k r)
    (hh : Matrix.of p.1 ∈ Gr k r) (hhinv : opn (Matrix.of p.1)⁻¹ ≤ Kw)
    (hπ : ‖π (Matrix.of p.1)⁻¹ ξ‖ = ‖ξ‖) (hm : Matrix.of p.2 ∈ Gr k r)
    {g : Mat k r} (hg : g ∈ Gr k r) :
    ‖bInt z c σ π w' ξ (σ g w) p‖ ≤
      Cφ * (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N1H k r * ‖ξ‖ *
        opn (Matrix.of p.2) ^ (-N1H k r) := by
  set h := Matrix.of p.1 with hdef
  set m := Matrix.of p.2 with mdef
  set N := N1H k r
  have hN : 0 ≤ N := nilradical_half_sum_nonneg
  have hmg : m * g ∈ Gr k r := gr_mul hm hg
  have hy : h * (m * g) ∈ Gr k r := gr_mul hh hmg
  have hhm : h * m ∈ Gr k r := gr_mul hh hm
  have hσeq : σ (h * m) (σ g w) = σ (h * (m * g)) w := by
    rw [← mul_assoc, sigma_mul hσ hhm hg]
  have hpsi : ‖star (psiGen k r z c m)‖ = 1 := by
    rw [norm_star]
    exact psiGen_norm z c m
  have hnorm : ‖bInt z c σ π w' ξ (σ g w) p‖ = ‖⟪w', σ (h * (m * g)) w⟫_ℂ‖ * ‖ξ‖ := by
    simp only [bInt]
    rw [norm_smul, norm_mul, hpsi, ← hdef, ← mdef, hσeq, hπ, mul_one]
  rw [hnorm]
  set y := h * (m * g)
  have hypos : 0 < opn y := opn_pos hy
  have hmpos : 0 < opn m := opn_pos hm
  have hCφ0 : 0 ≤ Cφ := le_trans (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _))
    (hCφ 1 gr_one)
  have hA : ‖⟪w', σ y w⟫_ℂ‖ ≤ Cφ * opn y ^ (-N) := by
    have h1 := hCφ y hy
    have hpow : 0 < opn y ^ N := Real.rpow_pos_of_pos hypos _
    rw [Real.rpow_neg (le_of_lt hypos), ← div_eq_mul_inv, le_div_iff₀ hpow]
    exact h1
  have hinvh : h⁻¹ * y = m * g := by
    simp only [y]
    rw [← mul_assoc, Matrix.nonsing_inv_mul h (gr_isUnit hh), one_mul]
  have hmle : opn m ≤ Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g) * opn y := by
    have e1 : opn m ≤ opn (m * g) * opn g⁻¹ := opn_le_mul_inv m hg
    have e2 : opn (m * g) ≤ opn h⁻¹ * opn y := by
      rw [← hinvh]
      exact opn_mul _ _
    have e3 : opn g⁻¹ ≤ opn (Hpk k r) * opn (Hpk k r) * opn g := opn_inv_le hg
    have e4 : opn h⁻¹ * opn y ≤ Kw * opn y := mul_le_mul_of_nonneg_right hhinv (le_of_lt hypos)
    calc opn m ≤ opn (m * g) * opn g⁻¹ := e1
      _ ≤ (Kw * opn y) * (opn (Hpk k r) * opn (Hpk k r) * opn g) := by
        apply mul_le_mul (e2.trans e4) e3 (opn_nonneg _)
        exact mul_nonneg hKw0 (le_of_lt hypos)
      _ = Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g) * opn y := by ring
  have hB0 : 0 ≤ Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g) :=
    mul_nonneg hKw0 (mul_nonneg (mul_nonneg (opn_nonneg _) (opn_nonneg _)) (opn_nonneg _))
  have hyN : opn y ^ (-N) ≤ (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * opn m ^ (-N) := by
    have hp : opn m ^ N ≤ (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * opn y ^ N := by
      rw [← Real.mul_rpow hB0 (le_of_lt hypos)]
      exact Real.rpow_le_rpow (le_of_lt hmpos) hmle hN
    have hmN : 0 < opn m ^ N := Real.rpow_pos_of_pos hmpos _
    have hyN' : 0 < opn y ^ N := Real.rpow_pos_of_pos hypos _
    rw [Real.rpow_neg (le_of_lt hypos), Real.rpow_neg (le_of_lt hmpos), ← div_eq_mul_inv,
      inv_le_iff_one_le_mul₀' hyN', mul_div_assoc', le_div_iff₀ hmN, one_mul]
    linarith [hp]
  calc ‖⟪w', σ y w⟫_ℂ‖ * ‖ξ‖ ≤ (Cφ * opn y ^ (-N)) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ ≤ (Cφ * ((Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * opn m ^ (-N))) * ‖ξ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hyN hCφ0
    _ = Cφ * (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N * ‖ξ‖ * opn m ^ (-N) := by ring

end Bound

private theorem measurable_ofReal_opn_rpow_snd : Measurable fun p : Mt k r × Mt k r => ENNReal.ofReal (opn (of p.2) ^ (-(N1H k r))) := by
  have hc : Continuous fun m : Mt k r => opn (of m) := (opn_continuous (k := k) (r := r)).comp continuous_id
  exact ENNReal.measurable_ofReal.comp ((hc.measurable.pow_const _).comp measurable_snd)

theorem aBound_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) : ABound := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hRD hCW x₀ hx₀ ξ
  obtain ⟨hset, hDS, hHCW, hLow, hGh, hSh, hQ, hWh, hNh, hWfin, hNfin⟩ := hyp
  have hinWb : inWb k r z := hset.2.2.1
  have hTz : 0 < Tz k r z := hset.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUWgrp, _, _⟩ := hS k r z c hinWb hTz
  have hπu := (hPi k r z u Vp π hinWb hTz hHCW).2
  obtain ⟨Cφ, _, hCφ⟩ := ptDecay_of hSG hD hRG k r z c u v b H σ Vp π w μG μS ν μW μN
    ⟨hset, hDS, hHCW, hLow, hGh, hSh, hQ, hWh, hNh, hWfin, hNfin⟩ hRD hCW x₀ hx₀
  obtain ⟨K0, hK0⟩ := (hU k r z hinWb hTz).exists_bound_of_continuousOn
    (opn_continuous (k := k) (r := r)).continuousOn
  set Kw := max K0 0
  have hKw0 : 0 ≤ Kw := le_max_right _ _
  have hKw : ∀ h ∈ UWset k r z, opn h⁻¹ ≤ Kw := by
    intro h hh
    have hinv : h⁻¹ ∈ UWset k r z := ((hUWgrp h hh h hh).2.1)
    have := hK0 _ hinv
    rw [Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) (le_trans this (le_max_left _ _))
  set N := N1H k r
  haveI : SigmaFinite μN := hNh.1
  haveI : SigmaFinite μW := hWh.1
  set I := ∫⁻ m : Mt k r, ENNReal.ofReal (opn (of m) ^ (-N)) ∂μN
  have hI : I < ∞ := hNI k r μN hNh hNfin
  set A := Cφ * (Kw * (opn (Hpk k r) * opn (Hpk k r))) ^ N * ‖ξ‖
  have hCφ0 : 0 ≤ Cφ := le_trans (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (opn_nonneg _) _))
    (hCφ 1 gr_one)
  have hH0 : 0 ≤ opn (Hpk k r) * opn (Hpk k r) := mul_nonneg (opn_nonneg _) (opn_nonneg _)
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg hCφ0 (Real.rpow_nonneg (mul_nonneg hKw0 hH0) _)) (norm_nonneg _)
  refine ⟨A * I.toReal * (μW Set.univ).toReal,
    mul_nonneg (mul_nonneg hA0 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg, ?_⟩
  intro g hg
  have hW_ae : ∀ᵐ x ∂μW, of x ∈ UWset k r z := ae_iff.mpr (by simpa using hWh.2.2.1)
  have hN_ae : ∀ᵐ x ∂μN, of x ∈ Nset k r := ae_iff.mpr (by simpa using hNh.2.2.1)
  have hae : ∀ᵐ p ∂(μW.prod μN), of p.1 ∈ UWset k r z ∧ of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW_ae).and (Measure.quasiMeasurePreserving_snd.ae hN_ae)
  have hg0 : 0 ≤ opn g := opn_nonneg g
  have hpt : ∀ p : Mt k r × Mt k r, of p.1 ∈ UWset k r z → of p.2 ∈ Nset k r →
      ‖bInt z c σ π (σ x₀ w) ξ (σ g w) p‖ ≤ (A * opn g ^ N) * opn (of p.2) ^ (-N) := by
    intro p h1 h2
    have hinv1 : (of p.1)⁻¹ ∈ UWset k r z := (hUWgrp _ h1 _ h1).2.1
    have hb := bInt_bound z c hσ (w := w) (w' := σ x₀ w) (fun y hy => hCφ y hy) hKw0 ξ p (hUWG h1)
      (hKw _ h1) (hπu _ hinv1 ξ) (hNG h2) hg
    have heq : (Kw * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N
        = (Kw * (opn (Hpk k r) * opn (Hpk k r))) ^ N * opn g ^ N := by
      rw [← Real.mul_rpow (mul_nonneg hKw0 hH0) hg0]
      ring_nf
    rw [heq] at hb
    calc _ ≤ _ := hb
      _ = (A * opn g ^ N) * opn (of p.2) ^ (-N) := by simp only [A]; ring
  have hmeas : Measurable fun p : Mt k r × Mt k r => ENNReal.ofReal (opn (of p.2) ^ (-N)) :=
    measurable_ofReal_opn_rpow_snd
  calc ∫⁻ p, ‖bInt z c σ π (σ x₀ w) ξ (σ g w) p‖ₑ ∂(μW.prod μN)
      ≤ ∫⁻ p, ENNReal.ofReal (A * opn g ^ N) * ENNReal.ofReal (opn (of p.2) ^ (-N)) ∂(μW.prod μN) := by
        apply lintegral_mono_ae
        filter_upwards [hae] with p hp
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (mul_nonneg hA0 (Real.rpow_nonneg hg0 _))]
        exact ENNReal.ofReal_le_ofReal (hpt p hp.1 hp.2)
    _ = ENNReal.ofReal (A * opn g ^ N) * (μW Set.univ * I) := by
        rw [lintegral_const_mul _ hmeas, lintegral_prod _ hmeas.aemeasurable]
        simp only [lintegral_const]
        ring
    _ = ENNReal.ofReal (A * I.toReal * (μW Set.univ).toReal * opn g ^ N) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hA0 ENNReal.toReal_nonneg) ENNReal.toReal_nonneg),
          ENNReal.ofReal_mul (mul_nonneg hA0 ENNReal.toReal_nonneg), ENNReal.ofReal_mul hA0,
          ENNReal.ofReal_mul hA0, ENNReal.ofReal_toReal hI.ne,
          ENNReal.ofReal_toReal (measure_ne_top μW Set.univ)]
        ring
    _ ≤ _ := le_rfl

end WlocSk.PtD
end
end

section
noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.WuDecay Formalism.L2.SG.SplitPrimeNormLemmas

variable {k r : ℕ}

def PiCont : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)), inWb k r z → 0 < Tz k r z →
    IsHCTypeW k r z u π → ∀ ξ : Vp, ContinuousOn (fun h => π h ξ) (UWset k r z)

theorem ellA_cont (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    Continuous (fun g : Mat k r => ellA k r z g a) := by
  unfold ellA
  split_ifs with h
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ fun j _ => (continuous_id.matrix_elem _ j).mul continuous_const

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (psiGen k r z c) := by
  unfold psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finset_sum _ fun a _ => continuous_const.mul (ellA_cont z a)))))

theorem inv_contOn : ContinuousOn (fun h : Mat k r => h⁻¹) (Gr k r) := by
  unfold Gr
  have key : ∀ h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), h⁻¹ = (h.det)⁻¹ • h.adjugate := fun h _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContinuousOn.congr ?_ key
  exact ((continuous_id.matrix_det.continuousOn).inv₀
    (fun h hh => (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh).ne_zero)).smul continuous_id.matrix_adjugate.continuousOn

theorem ae_product_mem_unipotent_and_nilradical {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hW : μW {x | Matrix.of x ∉ UWset k r z} = 0) (hN : μN {x | Matrix.of x ∉ Nset k r} = 0)
    (hUWG : UWset k r z ⊆ Gr k r) (hNG : Nset k r ⊆ Gr k r) :
    ∀ᵐ p ∂(μW.prod μN), (Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r) ∧
      (Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r) := by
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} = {x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p
      simp
    rw [e, Measure.prod_prod, hW, zero_mul]
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.2 ∈ Nset k r} = Set.univ ×ˢ {x | Matrix.of x ∉ Nset k r} := by
      ext p
      simp
    rw [e, Measure.prod_prod, hN, mul_zero]
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨⟨hp1, hp2⟩, hp1, Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (hUWG hp1) (hNG hp2)⟩

section Meas

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Vp →L[ℂ] Vp)}

theorem bInt_aesm (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hσ : IsURepOn (Gr k r) σ)
    {μW μN : Measure (Mt k r)}
    (hUWc : IsClosed (UWset k r z)) (hUWG : UWset k r z ⊆ Gr k r)
    (hUWinv : ∀ h ∈ UWset k r z, h⁻¹ ∈ UWset k r z)
    (hπc : ∀ ξ : Vp, ContinuousOn (fun h => π h ξ) (UWset k r z))
    (hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r)
    (w' : H) (ξ : Vp) (v : H) : AEStronglyMeasurable (bInt z c σ π w' ξ v) (μW.prod μN) := by
  set T : Set (Mt k r × Mt k r) :=
    {p | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r} with hTdef
  have hfst : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r) := continuous_fst
  have hsnd : Continuous fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r) := continuous_snd
  have hmul : Continuous fun p : Mt k r × Mt k r => Matrix.of p.1 * Matrix.of p.2 :=
    hfst.matrix_mul hsnd
  have hTc : IsClosed T := (hUWc.preimage hfst).inter (gr_isClosed.preimage hmul)
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1 * Matrix.of p.2) v) T :=
    (hσ.2.2 v).comp hmul.continuousOn (fun p hp => hp.2)
  have hi : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.1)⁻¹) T :=
    inv_contOn.comp hfst.continuousOn (fun p hp => hUWG hp.1)
  have h2 : ContinuousOn (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹ ξ) T :=
    (hπc ξ).comp hi (fun p hp => hUWinv _ hp.1)
  have h3 : Continuous fun p : Mt k r × Mt k r => star (psiGen k r z c (Matrix.of p.2)) :=
    continuous_star.comp ((psiGen_cont z c).comp hsnd)
  have hcont : ContinuousOn (bInt z c σ π w' ξ v) T :=
    ((continuousOn_const.inner h1).mul h3.continuousOn).smul h2
  have := hcont.aestronglyMeasurable (μ := μW.prod μN) hTc.measurableSet
  have hae' : ∀ᵐ p ∂(μW.prod μN), p ∈ T := hae
  rwa [Measure.restrict_eq_self_of_ae_mem hae'] at this

end Meas

theorem aInt_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) (hPC : PiCont) : AInt := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀ ξ g hg
  obtain ⟨C, _, hCb⟩ := aBound_of hSG hD hRG hS hPi hNI hU k r z c u v b H σ Vp π w μG μS ν μW μN
    hH hR hC x₀ hx₀ ξ
  obtain ⟨hSet, hDS, hHC, _, _, _, _, hμW, hμN, _, _⟩ := hH
  have hz := hSet.2.2.1
  have hT := hSet.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUW, _, _⟩ := hS k r z c hz hT
  have := hμW.1
  have := hμN.1
  have hae := ae_product_mem_unipotent_and_nilradical hμW.2.2.1 hμN.2.2.1 hUWG hNG
  refine ⟨bInt_aesm z c hσ (hU k r z hz hT).isClosed hUWG (fun h hh => (hUW h hh h hh).2.1)
    (hPC k r z u Vp π hz hT hHC) (hae.mono fun p hp => hp.2) _ _ _, ?_⟩
  exact (hCb g hg).trans_lt ENNReal.ofReal_lt_top

theorem aCont_of (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) (hPC : PiCont) : ACont := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hC x₀ hx₀ ξ g₀ hg₀
  have : FirstCountableTopology (Mat k r) :=
    inferInstanceAs (FirstCountableTopology (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨Cφ, hCφ0, hCφ⟩ := ptDecay_of hSG hD hRG k r z c u v b H σ Vp π w μG μS ν μW μN hH hR hC x₀ hx₀
  obtain ⟨hSet, hDS, hHC, _, _, _, _, hμW, hμN, hWfin, hNc⟩ := hH
  have hz := hSet.2.2.1
  have hT := hSet.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUW, _, _⟩ := hS k r z c hz hT
  have hPU := (hPi k r z u Vp π hz hT hHC).2
  obtain ⟨Kw, hKw⟩ := (hU k r z hz hT).exists_bound_of_continuousOn
    (opn_continuous (k := k) (r := r)).continuousOn
  have hKw0 : 0 ≤ max Kw 0 := le_max_right _ _
  have hinvb : ∀ h ∈ UWset k r z, opn h⁻¹ ≤ max Kw 0 := fun h hh =>
    le_max_of_le_left ((Real.le_norm_self _).trans (hKw _ (hUW h hh h hh).2.1))
  have := hμW.1
  have := hμN.1
  have hN := nilradical_half_sum_nonneg (k := k) (r := r)
  have hae := ae_product_mem_unipotent_and_nilradical hμW.2.2.1 hμN.2.2.1 hUWG hNG
  have hH2 : 0 ≤ opn (Hpk k r) * opn (Hpk k r) := mul_nonneg (opn_nonneg _) (opn_nonneg _)
  set K0 := Cφ * (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * (opn g₀ + 1))) ^ N1H k r * ‖ξ‖
    with hK0d
  have hK0 : 0 ≤ K0 := mul_nonneg (mul_nonneg hCφ0 (Real.rpow_nonneg (mul_nonneg hKw0
    (mul_nonneg hH2 (by linarith [opn_nonneg g₀]))) _)) (norm_nonneg _)
  have hmeas : Measurable fun m : Mt k r => opn (Matrix.of m) ^ (-N1H k r) :=
    (show Continuous fun m : Mt k r => opn (Matrix.of m) from opn_continuous).measurable.pow_const _
  have hgi : Integrable (fun m : Mt k r => opn (Matrix.of m) ^ (-N1H k r)) μN := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun m =>
      Real.rpow_nonneg (opn_nonneg _) _)]
    exact hNI k r μN hμN hNc
  have hbi : Integrable (fun p : Mt k r × Mt k r => K0 * opn (Matrix.of p.2) ^ (-N1H k r))
      (μW.prod μN) := by
    have := (integrable_const (1 : ℝ) (μ := μW)).mul_prod hgi
    simpa using this.const_mul K0
  show ContinuousWithinAt (fun g => ∫ p, bInt z c σ π (σ x₀ w) ξ (σ g w) p ∂(μW.prod μN))
    (Gr k r) g₀
  apply continuousWithinAt_of_dominated
    (bound := fun p : Mt k r × Mt k r => K0 * opn (Matrix.of p.2) ^ (-N1H k r))
  · exact Filter.Eventually.of_forall fun g => bInt_aesm z c hσ (hU k r z hz hT).isClosed hUWG
      (fun h hh => (hUW h hh h hh).2.1) (hPC k r z u Vp π hz hT hHC)
      (hae.mono fun p hp => hp.2) _ _ _
  · have hev1 : ∀ᶠ g in 𝓝[Gr k r] g₀, g ∈ Gr k r := self_mem_nhdsWithin
    have hev2 : ∀ᶠ g in 𝓝[Gr k r] g₀, opn g < opn g₀ + 1 :=
      eventually_nhdsWithin_of_eventually_nhds
        ((opn_continuous (k := k) (r := r)).continuousAt.eventually (gt_mem_nhds (lt_add_one _)))
    filter_upwards [hev1, hev2] with g hg hlt
    filter_upwards [hae] with p hp
    refine (bInt_bound z c hσ (π := π) hCφ hKw0 ξ p (hUWG hp.1.1) (hinvb _ hp.1.1)
      (hPU _ (hUW _ hp.1.1 _ hp.1.1).2.1 ξ) (hNG hp.1.2) hg).trans ?_
    have hle : (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * opn g)) ^ N1H k r ≤
        (max Kw 0 * (opn (Hpk k r) * opn (Hpk k r) * (opn g₀ + 1))) ^ N1H k r :=
      Real.rpow_le_rpow (mul_nonneg hKw0 (mul_nonneg hH2 (opn_nonneg _)))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlt.le hH2) hKw0) hN
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hle hCφ0) (norm_nonneg _)) (Real.rpow_nonneg (opn_nonneg _) _)
  · exact hbi
  · refine Filter.Eventually.of_forall fun p => ?_
    have h1 : ContinuousWithinAt (fun g => σ (Matrix.of p.1 * Matrix.of p.2) (σ g w)) (Gr k r) g₀ :=
      (σ _).continuous.continuousAt.comp_continuousWithinAt (hσ.2.2 w g₀ hg₀)
    exact ((continuousWithinAt_const.inner h1).mul continuousWithinAt_const).smul
      continuousWithinAt_const

end WlocSk.PtD
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WlocSk.PtD

open WlocSk Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

theorem representation_continuous : PiCont := by
  intro k r z u Vp _ _ π hz hT hπ ξ
  obtain ⟨g, hg, hπU⟩ := hπ
  obtain ⟨hgU, hgfix, hgz⟩ := hg
  obtain ⟨-, -, ⟨-, -, hcont⟩, -⟩ := hπU
  have hgi := WlocSk.UnitaryRepLocal.uh_inv hgU
  have hfixg : ∀ a ∈ UWset k r z, ∀ l, ¬ WlocSk.UnitaryRepLocal.inB k r l →
      a *ᵥ (g *ᵥ bvec l) = g *ᵥ bvec l := by
    intro a ha l hl
    unfold WlocSk.UnitaryRepLocal.inB at hl
    by_cases h1 : l.val < r
    · have hl' : l = eI k r ⟨l.val, h1⟩ := Fin.ext rfl
      rw [hl', (hgfix ⟨l.val, h1⟩).1, (ha.2.1 ⟨l.val, h1⟩).1]
    · by_cases h2 : r + k < l.val
      · have hl' : l = esI k r ⟨2 * r + k - l.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
        rw [hl', (hgfix _).2, (ha.2.1 _).2]
      · have hl' : l = wI k r (Fin.last k) := by apply Fin.ext; simp [wI]; omega
        have hs : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by
          have := Real.sqrt_pos.mpr hT; exact_mod_cast this.ne'
        obtain ⟨t, ht⟩ : ∃ t : ℂ, t = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) := ⟨_, rfl⟩
        rw [← ht] at hgz hs
        have hgw : g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • z := by
          calc g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • (t • g *ᵥ bvec (wI k r (Fin.last k))) := by
                rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
            _ = t⁻¹ • z := by rw [← Matrix.mulVec_smul, hgz]
        rw [hl', hgw, Matrix.mulVec_smul, ha.2.2]
  have hstruct : ∀ a ∈ UWset k r z, WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g) ∈ UJset (allPos k) ∧
      a = g * blockW k r (WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g)) * g⁻¹ := by
    intro a ha
    have hc : g⁻¹ * a * g ∈ UH (Hpk k r) :=
      WlocSk.UnitaryRepLocal.uh_mul (WlocSk.UnitaryRepLocal.uh_mul hgi.2.2 ha.1) hgU
    have hb : g⁻¹ * a * g = blockW k r (WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g)) := by
      refine WlocSk.UnitaryRepLocal.eq_blockW hc fun l hl => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfixg a ha l hl, Matrix.mulVec_mulVec,
        hgi.2.1, Matrix.one_mulVec]
    refine ⟨WlocSk.UnitaryRepLocal.ub_unitary hc hb, ?_⟩
    rw [← hb]
    calc a = (g * g⁻¹) * a * (g * g⁻¹) := by rw [hgi.1, Matrix.one_mul, Matrix.mul_one]
      _ = g * (g⁻¹ * a * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
  have hmul : Continuous fun a : Mat k r => g⁻¹ * a * g :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hubc : Continuous fun a : Mat k r => WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g) := by
    unfold WlocSk.UnitaryRepLocal.ub
    exact continuous_pi fun m => continuous_pi fun m' =>
      (continuous_apply _).comp ((continuous_apply _).comp hmul)
  refine ((hcont ξ).comp hubc.continuousOn (fun a ha => (hstruct a ha).1)).congr (fun a ha => ?_)
  show π a ξ = π (g * blockW k r (WlocSk.UnitaryRepLocal.ub (g⁻¹ * a * g)) * g⁻¹) ξ
  rw [← (hstruct a ha).2]

theorem wave_packet_integrable (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) : AInt :=
  aInt_of hSG hD hRG hS hPi hNI hU representation_continuous

theorem wave_packet_continuous (hSG : SigmaG) (hD : Decay) (hRG : ReprodG) (hS : SGrp) (hPi : PiUnit)
    (hNI : NIntDecay) (hU : UWComp) : ACont :=
  aCont_of hSG hD hRG hS hPi hNI hU representation_continuous

end WlocSk.PtD
end
end
