import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEHeightsilinear

section
noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open GLnLocal MeasureTheory Measure GJMatrix
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}

def indGL (S : Set (GL (Fin m) F)) : Matrix (Fin m) (Fin m) F → ℂ :=
  (Units.val '' S).indicator fun _ => 1

theorem indGL_val (S : Set (GL (Fin m) F)) (g : GL (Fin m) F) :
    indGL S (g : Matrix (Fin m) (Fin m) F) = S.indicator (fun _ => (1 : ℂ)) g := by
  classical
  simp only [indGL, Set.indicator_apply]
  congr 1
  exact propext ⟨fun ⟨h, hh, he⟩ => (Units.ext he) ▸ hh, fun hg => ⟨g, hg, rfl⟩⟩

theorem isSchwartzBruhat_indGL {S : Set (GL (Fin m) F)} (hSc : IsCompact S) (hSo : IsOpen S) :
    IsSchwartzBruhat (indGL S) := by
  classical
  have hopen : IsOpen (Units.val '' S : Set (Matrix (Fin m) (Fin m) F)) :=
    (Measures.isOpenEmbedding_val F m).isOpenMap _ hSo
  have hcpt : IsCompact (Units.val '' S : Set (Matrix (Fin m) (Fin m) F)) :=
    hSc.image Units.continuous_val
  refine ⟨(IsLocallyConstant.iff_isOpen_fiber).2 fun v => ?_, ?_⟩
  · by_cases h1 : v = 1
    · have : indGL S ⁻¹' {v} = Units.val '' S := by
        ext X
        simp only [Set.mem_preimage, Set.mem_singleton_iff, indGL, Set.indicator_apply, h1]
        split_ifs with h <;> simp [h]
      rw [this]; exact hopen
    · by_cases h0 : v = 0
      · have : indGL S ⁻¹' {v} = (Units.val '' S)ᶜ := by
          ext X
          simp only [Set.mem_preimage, Set.mem_singleton_iff, indGL, Set.indicator_apply, h0,
            Set.mem_compl_iff]
          split_ifs with h <;> simp [h]
        rw [this]; exact hcpt.isClosed.isOpen_compl
      · have : indGL S ⁻¹' {v} = ∅ := by
          ext X
          simp only [Set.mem_preimage, Set.mem_singleton_iff, indGL, Set.indicator_apply,
            Set.mem_empty_iff_false, iff_false]
          split_ifs with h
          · exact fun h' => h1 h'.symm
          · exact fun h' => h0 h'.symm
        rw [this]; exact isOpen_empty
  · refine HasCompactSupport.intro hcpt fun X hX => ?_
    simp only [indGL, Set.indicator_apply]
    rw [if_neg hX]

theorem indGL_support {S : Set (GL (Fin m) F)} (hSc : IsCompact S) :
    ∃ K : Set (GL (Fin m) F), IsCompact K ∧
      ∀ X, indGL S X ≠ 0 → ∃ g ∈ K, (g : Matrix (Fin m) (Fin m) F) = X := by
  classical
  refine ⟨S, hSc, fun X hX => ?_⟩
  by_contra h
  push Not at h
  apply hX
  simp only [indGL, Set.indicator_apply]
  rw [if_neg]
  rintro ⟨g, hg, rfl⟩
  exact h g hg rfl

theorem indGL_smul (x : GL (Fin m) F) (S : Set (GL (Fin m) F)) (X : Matrix (Fin m) (Fin m) F) :
    indGL (x • S) X = indGL S (((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * X) := by
  classical
  simp only [indGL, Set.indicator_apply]
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨g, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, by simp⟩
  · rintro ⟨k, hk, hkX⟩
    refine ⟨x * k, ⟨k, hk, rfl⟩, ?_⟩
    rw [Units.val_mul, hkX, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]

variable [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)]

theorem integral_indGL_mul (μ : Measure (GL (Fin m) F)) {S : Set (GL (Fin m) F)}
    (hS : MeasurableSet S) {f : GL (Fin m) F → ℂ} {x₀ : GL (Fin m) F}
    (hf : ∀ g ∈ S, f g = f x₀) :
    ∫ g, indGL S (g : Matrix (Fin m) (Fin m) F) * f g ∂μ = μ.real S * f x₀ := by
  classical
  have : (fun g : GL (Fin m) F => indGL S (g : Matrix (Fin m) (Fin m) F) * f g) =
      S.indicator (fun _ => f x₀) := by
    funext g
    rw [indGL_val]
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, one_mul, hf g hg]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  rw [this, integral_indicator_const _ hS, Complex.real_smul]

section Fourier

variable [MeasurableSpace F] [BorelSpace F]

theorem localMatrixFourier_comp_mul_right {ψ : AddChar F Circle}
    (Φ : Matrix (Fin m) (Fin m) F → ℂ) (y : GL (Fin m) F) (W : Matrix (Fin m) (Fin m) F) :
    localMatrixFourier ψ (fun Z => Φ (Z * (y : Matrix (Fin m) (Fin m) F))) W =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m)⁻¹ •
        localMatrixFourier ψ Φ (((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * W) := by
  have h := integral_comp_mul_right_matrix (LocalField.selfDualMeasure ψ) y
    (fun Z => Φ Z * ((ψ (Matrix.trace (Z * (((y⁻¹ : GL (Fin m) F) :
      Matrix (Fin m) (Fin m) F) * W))) : Circle) : ℂ))
  have htr : ∀ Z : Matrix (Fin m) (Fin m) F, Matrix.trace (Z * (y : Matrix (Fin m) (Fin m) F) *
      (((y⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * W)) = Matrix.trace (Z * W) := by
    intro Z
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (y : Matrix (Fin m) (Fin m) F), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp only [localMatrixFourier]
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only [htr]

theorem modulus_det_eq_one {k : GL (Fin m) F} (hk : k ∈ integralGL F m) :
    LocalField.modulus (k : Matrix (Fin m) (Fin m) F).det = 1 := by
  rw [LocalField.modulus_of_ne_zero (det_ne_zero k)]
  have := ordDet_of_mem_integralGL hk
  rw [ordDet] at this
  rw [this, neg_zero, zpow_zero]

theorem indGL_mul_left {K : Subgroup (GL (Fin m) F)} {k : GL (Fin m) F} (hk : k ∈ K)
    (X : Matrix (Fin m) (Fin m) F) :
    indGL (K : Set (GL (Fin m) F)) ((k : Matrix (Fin m) (Fin m) F) * X) =
      indGL (K : Set (GL (Fin m) F)) X := by
  have h := indGL_smul k⁻¹ (K : Set (GL (Fin m) F)) X
  rw [inv_inv, show (k⁻¹ • (K : Set (GL (Fin m) F))) = K from ?_] at h
  · exact h.symm
  · ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, smul_eq_mul, SetLike.mem_coe, SetLike.mem_coe]
    exact ⟨fun h' => by simpa using K.mul_mem (K.inv_mem hk) h', fun h' => K.mul_mem hk h'⟩

theorem indGL_mul_right {K : Subgroup (GL (Fin m) F)} {k : GL (Fin m) F} (hk : k ∈ K)
    (X : Matrix (Fin m) (Fin m) F) :
    indGL (K : Set (GL (Fin m) F)) (X * (k : Matrix (Fin m) (Fin m) F)) =
      indGL (K : Set (GL (Fin m) F)) X := by
  classical
  simp only [indGL, Set.indicator_apply]
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨g, hg, hgX⟩
    refine ⟨g * k⁻¹, K.mul_mem hg (K.inv_mem hk), ?_⟩
    rw [Units.val_mul, hgX, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * k, K.mul_mem hg hk, by rw [Units.val_mul]⟩

theorem localMatrixFourier_indGL_mul_right {ψ : AddChar F Circle} {K : Subgroup (GL (Fin m) F)}
    (hK : K ≤ integralGL F m) {k : GL (Fin m) F} (hk : k ∈ K) (W : Matrix (Fin m) (Fin m) F) :
    localMatrixFourier ψ (indGL (K : Set (GL (Fin m) F))) (W * (k : Matrix (Fin m) (Fin m) F)) =
      localMatrixFourier ψ (indGL (K : Set (GL (Fin m) F))) W := by
  have h := localMatrixFourier_comp_mul_left (ψ := ψ) (indGL (K : Set (GL (Fin m) F))) k⁻¹ W
  rw [inv_inv, modulus_det_eq_one (hK (K.inv_mem hk)), NNReal.coe_one, one_pow, inv_one,
    one_smul] at h
  rw [← h]
  congr 1
  funext Z
  exact indGL_mul_left (K.inv_mem hk) Z

theorem localMatrixFourier_indGL_mul_left {ψ : AddChar F Circle} {K : Subgroup (GL (Fin m) F)}
    (hK : K ≤ integralGL F m) {k : GL (Fin m) F} (hk : k ∈ K) (W : Matrix (Fin m) (Fin m) F) :
    localMatrixFourier ψ (indGL (K : Set (GL (Fin m) F))) ((k : Matrix (Fin m) (Fin m) F) * W) =
      localMatrixFourier ψ (indGL (K : Set (GL (Fin m) F))) W := by
  have h := localMatrixFourier_comp_mul_right (ψ := ψ) (indGL (K : Set (GL (Fin m) F))) k⁻¹ W
  rw [inv_inv, modulus_det_eq_one (hK (K.inv_mem hk)), NNReal.coe_one, one_pow, inv_one,
    one_smul] at h
  rw [← h]
  congr 1
  funext Z
  exact indGL_mul_right (K.inv_mem hk) Z

theorem localMatrixFourier_indGL_smul {ψ : AddChar F Circle} (K : Set (GL (Fin m) F))
    (x : GL (Fin m) F) (W : Matrix (Fin m) (Fin m) F) :
    localMatrixFourier ψ (indGL (x • K)) W =
      detPow x (m : ℂ) * localMatrixFourier ψ (indGL K) (W * (x : Matrix (Fin m) (Fin m) F)) := by
  have h := localMatrixFourier_comp_mul_left (ψ := ψ) (indGL K) x⁻¹ W
  rw [inv_inv] at h
  have he : indGL (x • K) = fun Z => indGL K (((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * Z) :=
    funext (indGL_smul x K)
  rw [he, h, detPow_natCast, detModulusPow, Complex.real_smul]
  congr 1
  have hinv : LocalField.modulus ((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F).det =
      (LocalField.modulus (x : Matrix (Fin m) (Fin m) F).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', LocalField.modulus_inv]
  rw [hinv]
  push_cast
  rw [inv_pow, inv_inv]

end Fourier

section Rep

variable [MeasurableSpace F] [BorelSpace F] [NeZero m]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin m) F × H) W}

theorem coeff_centralUnif_mul {α : ℂ} (hα : ∀ v, σ (centralUnif F m, 1) v = α • v) (v : W)
    (ℓ : Module.Dual ℂ W) (g : GL (Fin m) F) :
    ℓ (σ (centralUnif F m * g, 1) v) = α * ℓ (σ (g, 1) v) := by
  rw [show ((centralUnif F m * g, (1 : H)) : GL (Fin m) F × H) = (centralUnif F m, 1) * (g, 1) by
    simp, map_mul, Module.End.mul_apply, hα, map_smul, smul_eq_mul]

theorem isCentralCoeff_coeff (hσ : IsSmooth σ) {α : ℂ} (hα0 : α ≠ 0)
    (hα : ∀ v, σ (centralUnif F m, 1) v = α • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      ∃ C : Set (GL (Fin m) F), IsCompact C ∧
        ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C)
    (v : W) {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    IsCentralCoeff m α (fun g => ℓ (σ (g, 1) v)) := by
  refine ⟨?_, hα0, coeff_centralUnif_mul hα v ℓ, hsupp v ℓ hℓ⟩
  set K : Subgroup (GL (Fin m) F) := (stabilizerOf σ v).comap (MonoidHom.inl _ _)
  have hKo : IsOpen (K : Set (GL (Fin m) F)) :=
    (hσ v).preimage (continuous_id.prodMk continuous_const)
  refine (isLocallyConstant_of_mul_right hKo fun g k hk => ?_).continuous
  have hk' : σ (k, 1) v = v := mem_stabilizerOf.1 hk
  show ℓ (σ (g * k, 1) v) = ℓ (σ (g, 1) v)
  rw [show ((g * k, (1 : H)) : GL (Fin m) F × H) = (g, 1) * (k, 1) by simp, map_mul,
    Module.End.mul_apply, hk']

theorem norm_inv_mul_qs_sub_lt_one {α : ℂ} (hα0 : α ≠ 0) {s : ℂ}
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖) :
    ‖α⁻¹ * qs F ((m : ℂ) - s) ^ m‖ < 1 := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  have hq0 : (0 : ℝ) < LocalField.residueCard F := by linarith
  have hqs : ‖qs F ((m : ℂ) - s)‖ = ((LocalField.residueCard F : ℝ) ^ (-(m : ℝ))) / ‖qs F s‖ := by
    rw [norm_qs, norm_qs, Complex.sub_re, Complex.natCast_re, neg_sub, Real.rpow_sub hq0,
      Real.rpow_neg hq0.le, Real.rpow_neg hq0.le]
    field_simp
  have hpos : 0 < ‖α * qs F s ^ m‖ :=
    norm_pos_iff.2 (mul_ne_zero hα0 (pow_ne_zero _ (qs_ne_zero s)))
  rw [norm_mul, norm_inv, norm_pow, hqs, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
  rw [norm_mul, norm_pow] at hpos hs'
  have hlhs : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) =
      (LocalField.residueCard F : ℝ) ^ (-(m : ℝ) * m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
    push_cast
    ring_nf
  rw [hlhs] at hs'
  rw [inv_mul_eq_div, div_div, mul_comm (‖qs F s‖ ^ m), div_lt_one hpos]
  linarith

theorem integrable_blockA (hσ : IsSmooth σ) {α : ℂ} (hα0 : α ≠ 0)
    (hα : ∀ v, σ (centralUnif F m, 1) v = α • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      ∃ C : Set (GL (Fin m) F), IsCompact C ∧
        ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (v : W) {ℓ : Module.Dual ℂ W}
    (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1) :
    Integrable (fun g : GL (Fin m) F =>
      Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * ℓ (σ (g, 1) v)) μ :=
  (isCentralCoeff_coeff hσ hα0 hα hsupp v hℓ).integrable_zeta μ hΦ hs

theorem integrable_blockB (hσ : IsSmooth σ) {α : ℂ} (hα0 : α ≠ 0)
    (hα : ∀ v, σ (centralUnif F m, 1) v = α • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      ∃ C : Set (GL (Fin m) F), IsCompact C ∧
        ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {Φ : Matrix (Fin m) (Fin m) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (v : W) {ℓ : Module.Dual ℂ W}
    (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) {s : ℂ}
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖) :
    Integrable (fun g : GL (Fin m) F =>
      Φ (g : Matrix (Fin m) (Fin m) F) * detPow g ((m : ℂ) - s) * ℓ (σ (g⁻¹, 1) v)) μ :=
  (isCentralCoeff_coeff hσ hα0 hα hsupp v hℓ).inv.integrable_zeta μ hΦ
    (norm_inv_mul_qs_sub_lt_one hα0 hs')

theorem detPow_inv (g : GL (Fin m) F) (a : ℂ) : detPow g⁻¹ a = detPow g (-a) := by
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, ordDet_inv, zpow_neg, qs, qs, neg_neg,
    Complex.cpow_neg, inv_zpow, inv_inv]

def blockBForm (μ : Measure (GL (Fin m) F)) (σ : Representation ℂ (GL (Fin m) F × H) W)
    (Ψ : Matrix (Fin m) (Fin m) F → ℂ) (s : ℂ)
    (hint : ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ), Integrable (fun g : GL (Fin m) F =>
      Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g ((m : ℂ) - s) * ℓ (σ (g⁻¹, 1) w)) μ) :
    W →ₗ[ℂ] smoothVectors (Representation.dual σ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun w l => blockB μ σ Ψ w (l : Module.Dual ℂ W) s)
    (fun w₁ w₂ l => by
      simp only [blockB, map_add, mul_add]
      exact integral_add (hint _ _ l.2) (hint _ _ l.2))
    (fun c w l => by
      simp only [blockB, map_smul, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1; funext g; ring)
    (fun w l₁ l₂ => by
      simp only [blockB, Submodule.coe_add, LinearMap.add_apply, mul_add]
      exact integral_add (hint _ _ l₁.2) (hint _ _ l₂.2))
    (fun c w l => by
      simp only [blockB, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1; funext g; ring)

theorem blockBForm_apply (μ : Measure (GL (Fin m) F)) (Ψ : Matrix (Fin m) (Fin m) F → ℂ) (s : ℂ)
    (hint : ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ), Integrable (fun g : GL (Fin m) F =>
      Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g ((m : ℂ) - s) * ℓ (σ (g⁻¹, 1) w)) μ)
    (w : W) (l : smoothVectors (Representation.dual σ)) :
    blockBForm μ σ Ψ s hint w l = blockB μ σ Ψ w (l : Module.Dual ℂ W) s := rfl

theorem blockB_comm_H (μ : Measure (GL (Fin m) F)) (Ψ : Matrix (Fin m) (Fin m) F → ℂ) (y : H)
    (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ) :
    blockB μ σ Ψ (σ (1, y) w) ℓ s = blockB μ σ Ψ w (ℓ ∘ₗ σ (1, y)) s := by
  simp only [blockB, LinearMap.comp_apply]
  congr 1
  funext g
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 4
  simp

theorem blockB_indGL_smul (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle}
    (K : Set (GL (Fin m) F)) (x : GL (Fin m) F) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ) :
    blockB μ σ (localMatrixFourier ψ (indGL (x • K))) w ℓ s =
      detPow x s * blockB μ σ (localMatrixFourier ψ (indGL K)) w (ℓ ∘ₗ σ (x, 1)) s := by
  have : μ.IsMulRightInvariant := Measures.isMulRightInvariant_GL F m μ
  simp only [blockB, localMatrixFourier_indGL_smul]
  rw [← integral_mul_right_eq_self _ x⁻¹, ← integral_const_mul]
  congr 1
  funext h
  simp only [LinearMap.comp_apply]
  rw [Units.val_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one, mul_inv_rev, inv_inv, detPow_mul,
    show ((x * h⁻¹, (1 : H)) : GL (Fin m) F × H) = (x, 1) * (h⁻¹, 1) by simp, map_mul,
    Module.End.mul_apply, detPow_inv]
  have h2 : detPow x (m : ℂ) * detPow x (-((m : ℂ) - s)) = detPow x s := by
    rw [detPow_mul_detPow]; congr 1; ring
  rw [← h2]
  ring

theorem kernel_block (hσ : IsSmooth σ) {α : ℂ} (hα0 : α ≠ 0)
    (hα : ∀ v, σ (centralUnif F m, 1) v = α • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      ∃ C : Set (GL (Fin m) F), IsCompact C ∧
        ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {Φ Ψ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    (hΨ : IsSchwartzBruhat Ψ) (hΨK : ∃ K : Set (GL (Fin m) F), IsCompact K ∧
      ∀ X, Ψ X ≠ 0 → ∃ g ∈ K, (g : Matrix (Fin m) (Fin m) F) = X)
    {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖)
    (v : W) {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    ∫ g, Ψ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        blockB μ σ (localMatrixFourier ψ Φ) (σ (g, 1) v) ℓ s ∂μ =
      ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s *
        blockB μ σ (localMatrixFourier ψ Ψ) v (ℓ ∘ₗ σ (g, 1)) s ∂μ := by
  have hc := isCentralCoeff_coeff hσ hα0 hα hsupp v hℓ
  have h := integral_kernel_eq hc μ hψ hψ1 hΦ hΨ hΨK hs hs'
  convert h using 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [blockB]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    rw [← Module.End.mul_apply, ← map_mul]
    congr 4
    simp
  · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [blockB]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul]
    congr 4
    simp

theorem comp_mem_smoothVectors {ℓ : Module.Dual ℂ W}
    (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) (z : GL (Fin m) F × H) :
    ℓ ∘ₗ σ z ∈ smoothVectors (Representation.dual σ) := by
  have h := smooth_apply_mem (Representation.dual σ) hℓ z⁻¹
  convert h using 1
  ext v
  rw [dual_apply_apply, inv_inv]
  rfl

theorem exists_blockB_eq_smul (hσ : IsAdmissible σ) [σ.IsIrreducible] {α : ℂ} (hα0 : α ≠ 0)
    (hα : ∀ v, σ (centralUnif F m, 1) v = α • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      ∃ C : Set (GL (Fin m) F), IsCompact C ∧
        ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖)
    {K : Subgroup (GL (Fin m) F)} (hKc : IsCompact (K : Set (GL (Fin m) F)))
    (hKo : IsOpen (K : Set (GL (Fin m) F))) (hKint : K ≤ integralGL F m)
    {K' : Subgroup H} (hK'c : IsCompact (K' : Set H)) (hK'o : IsOpen (K' : Set H)) :
    ∃ c : ℂ, ∀ Φ : Matrix (Fin m) (Fin m) F → ℂ, IsSchwartzBruhat Φ →
      ∀ u ∈ fixedVectors σ (K.prod K'), ∀ ℓ ∈ smoothVectors (Representation.dual σ),
        μ.real (K : Set (GL (Fin m) F)) * blockB μ σ (localMatrixFourier ψ Φ) u ℓ s =
          c * blockA μ σ Φ u ℓ s := by
  have hσs := hσ.1
  have : μ.IsMulRightInvariant := Measures.isMulRightInvariant_GL F m μ
  set e := indGL (K : Set (GL (Fin m) F)) with he_def
  have he : IsSchwartzBruhat e := isSchwartzBruhat_indGL hKc hKo
  have heK := indGL_support hKc
  set ê := localMatrixFourier ψ e with hê_def
  have hê : IsSchwartzBruhat ê := he.localMatrixFourier hψ hψ1
  have hint : ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ), Integrable
      (fun g : GL (Fin m) F => ê (g : Matrix (Fin m) (Fin m) F) * detPow g ((m : ℂ) - s) *
        ℓ (σ (g⁻¹, 1) w)) μ :=
    fun w ℓ hℓ => integrable_blockB hσs hα0 hα hsupp μ hê w hℓ hs'
  set b := blockBForm μ σ ê s hint with hb
  set 𝕂 := K.prod K'
  have h𝕂c : IsCompact (𝕂 : Set (GL (Fin m) F × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hK'c
  have h𝕂o : IsOpen (𝕂 : Set (GL (Fin m) F × H)) := by
    rw [Subgroup.coe_prod]; exact hKo.prod hK'o
  have hêR : ∀ k ∈ K, ∀ X, ê (X * (k : Matrix (Fin m) (Fin m) F)) = ê X := fun k hk X =>
    localMatrixFourier_indGL_mul_right hKint hk X
  have hêL : ∀ k ∈ K, ∀ X, ê ((k : Matrix (Fin m) (Fin m) F) * X) = ê X := fun k hk X =>
    localMatrixFourier_indGL_mul_left hKint hk X
  have hdetK : ∀ k ∈ K, ∀ a : ℂ, detPow k a = 1 := fun k hk a =>
    detPow_of_mem_integralGL (hKint hk) a
  have h11 : σ (1, 1) = 1 := by
    rw [show ((1, 1) : GL (Fin m) F × H) = 1 from rfl, map_one]
  have hdet1 : detPow (1 : GL (Fin m) F) s = 1 := detPow_of_mem_integralGL (one_mem _) s
  have hmem1 : ∀ k ∈ K, ((k, (1 : H)) : GL (Fin m) F × H) ∈ 𝕂 := fun k hk =>
    Subgroup.mem_prod.2 ⟨hk, K'.one_mem⟩
  have hmem2 : ∀ k' ∈ K', (((1 : GL (Fin m) F), k') : GL (Fin m) F × H) ∈ 𝕂 := fun k' hk' =>
    Subgroup.mem_prod.2 ⟨K.one_mem, hk'⟩
  have hμK : μ.real (K : Set (GL (Fin m) F)) ≠ 0 := by
    rw [measureReal_ne_zero_iff (hKc.measure_lt_top.ne)]
    exact (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'

  have hcommG : ∀ w : W, (∀ k ∈ K, σ (k, 1) w = w) → ∀ ℓ : Module.Dual ℂ W,
      ℓ ∈ smoothVectors (Representation.dual σ) → (∀ k ∈ K, ∀ v, ℓ (σ (k, 1) v) = ℓ v) →
      ∀ x : GL (Fin m) F, blockB μ σ ê (σ (x, 1) w) ℓ s = blockB μ σ ê w (ℓ ∘ₗ σ (x, 1)) s := by
    intro w hw ℓ hℓ hℓK x
    have hxKc : IsCompact (x • (K : Set (GL (Fin m) F))) := hKc.smul x
    have hxKo : IsOpen (x • (K : Set (GL (Fin m) F))) := hKo.smul x
    have hk := kernel_block hσs hα0 hα hsupp μ hψ hψ1 he (isSchwartzBruhat_indGL hxKc hxKo)
      (indGL_support hxKc) hs hs' w hℓ
    simp only [mul_assoc] at hk
    rw [integral_indGL_mul μ hxKo.measurableSet (x₀ := x) (fun g hg => ?_),
      integral_indGL_mul μ hKo.measurableSet (x₀ := 1) (fun g hg => ?_)] at hk
    · have hμx : μ.real (x • (K : Set (GL (Fin m) F))) = μ.real (K : Set (GL (Fin m) F)) := by
        simp only [measureReal_def, measure_smul]
      rw [hμx, blockB_indGL_smul, h11, Module.End.one_eq_id, LinearMap.comp_id, hdet1,
        one_mul] at hk
      have hμK' : ((μ.real (K : Set (GL (Fin m) F)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμK
      have hdx : detPow x s ≠ 0 := by rw [detPow_eq_qs_zpow]; exact zpow_ne_zero _ (qs_ne_zero s)
      exact mul_left_cancel₀ hdx (mul_left_cancel₀ hμK' hk)
    · have hℓg : ℓ ∘ₗ σ (g, 1) = ℓ ∘ₗ σ (1, 1) := by
        ext v
        simp only [LinearMap.comp_apply]
        rw [hℓK g hg, show ((1, 1) : GL (Fin m) F × H) = 1 from rfl, map_one, Module.End.one_apply]
      rw [hdetK g hg, hdetK 1 (one_mem _), hℓg]
    · obtain ⟨k, hk, rfl⟩ := hg
      simp only [smul_eq_mul]
      rw [detPow_mul, hdetK k hk, mul_one,
        show ((x * k, (1 : H)) : GL (Fin m) F × H) = (x, 1) * (k, 1) by simp, map_mul,
        Module.End.mul_apply, hw k hk]
  have hinvR : ∀ u ∈ fixedVectors σ 𝕂, ∀ k ∈ 𝕂, ∀ l, b u (contragredient σ k l) = b u l := by
    intro u hu k hk l
    rw [blockBForm_apply, blockBForm_apply]
    simp only [blockB]
    obtain ⟨k₁, k₂⟩ := k
    obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_prod.1 hk
    have hval : ∀ h : GL (Fin m) F, ((contragredient σ (k₁, k₂) l : smoothVectors
        (Representation.dual σ)) : Module.Dual ℂ W) (σ (h⁻¹, 1) u) =
        (l : Module.Dual ℂ W) (σ ((h * k₁)⁻¹, 1) u) := by
      intro h
      rw [contragredient_apply_apply, ← Module.End.mul_apply, ← map_mul]
      have e1 : ((k₁, k₂) : GL (Fin m) F × H)⁻¹ * (h⁻¹, 1) = ((h * k₁)⁻¹, 1) * (1, k₂⁻¹) := by
        ext <;> simp [mul_inv_rev]
      rw [e1, map_mul, Module.End.mul_apply, hu _ (hmem2 _ (K'.inv_mem hk₂))]
    simp only [hval]
    rw [← integral_mul_right_eq_self (fun h : GL (Fin m) F => ê (h : Matrix (Fin m) (Fin m) F) *
      detPow h ((m : ℂ) - s) * (l : Module.Dual ℂ W) (σ (h⁻¹, 1) u)) k₁]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    rw [Units.val_mul, hêR k₁ hk₁, detPow_mul, hdetK k₁ hk₁, mul_one]
  have hinvL : ∀ l ∈ fixedVectors (contragredient σ) 𝕂, ∀ k ∈ 𝕂, ∀ w, b (σ k w) l = b w l := by
    intro l hl k hk w
    rw [blockBForm_apply, blockBForm_apply]
    simp only [blockB]
    obtain ⟨k₁, k₂⟩ := k
    obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_prod.1 hk
    have hlinv := mem_fixedVectors_contragredient.1 hl
    have hval : ∀ h : GL (Fin m) F, (l : Module.Dual ℂ W) (σ (h⁻¹, 1) (σ (k₁, k₂) w)) =
        (l : Module.Dual ℂ W) (σ ((k₁⁻¹ * h)⁻¹, 1) w) := by
      intro h
      rw [← Module.End.mul_apply, ← map_mul]
      have e1 : ((h⁻¹, (1 : H)) : GL (Fin m) F × H) * (k₁, k₂) = (1, k₂) * ((k₁⁻¹ * h)⁻¹, 1) := by
        ext <;> simp [mul_inv_rev]
      rw [e1, map_mul, Module.End.mul_apply, hlinv _ (hmem2 _ hk₂)]
    simp only [hval]
    rw [← integral_mul_left_eq_self (fun h : GL (Fin m) F => ê (h : Matrix (Fin m) (Fin m) F) *
      detPow h ((m : ℂ) - s) * (l : Module.Dual ℂ W) (σ (h⁻¹, 1) w)) k₁⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    rw [Units.val_mul, hêL _ (K.inv_mem hk₁), detPow_mul, hdetK _ (K.inv_mem hk₁), one_mul]
  have hcomm : ∀ u ∈ fixedVectors σ 𝕂, ∀ l ∈ fixedVectors (contragredient σ) 𝕂, ∀ z,
      b (σ z u) l = b u (contragredient σ z⁻¹ l) := by
    intro u hu l hl z
    obtain ⟨x, y⟩ := z
    rw [blockBForm_apply, blockBForm_apply]
    have hlinv := mem_fixedVectors_contragredient.1 hl
    have hz : σ (x, y) = σ (x, 1) * σ (1, y) := by
      rw [← map_mul]; congr 1; ext <;> simp
    rw [hz, Module.End.mul_apply]
    rw [hcommG (σ (1, y) u) (fun k hk => ?_) l l.2 (fun k hk v => hlinv _ (hmem1 k hk) v) x]
    · rw [blockB_comm_H]
      congr 1
      ext v
      simp only [LinearMap.comp_apply]
      rw [contragredient_apply_apply, inv_inv, hz, Module.End.mul_apply]
    · rw [← Module.End.mul_apply, ← map_mul,
        show ((k, (1 : H)) : GL (Fin m) F × H) * (1, y) = (1, y) * (k, 1) by ext <;> simp,
        map_mul, Module.End.mul_apply, hu _ (hmem1 k hk)]
  obtain ⟨c, hc⟩ := exists_smul_of_bilinear hσ h𝕂c h𝕂o b hinvR hinvL hcomm
  refine ⟨c, fun Φ hΦ u hu ℓ hℓ => ?_⟩
  have hk := kernel_block hσs hα0 hα hsupp μ hψ hψ1 hΦ he heK hs hs' u hℓ
  simp only [mul_assoc] at hk
  rw [integral_indGL_mul μ hKo.measurableSet (x₀ := 1) (fun g hg => ?_)] at hk
  · rw [hdet1, one_mul, h11, Module.End.one_apply] at hk
    rw [hk, blockA, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have := hc u hu ⟨ℓ ∘ₗ σ (g, 1), comp_mem_smoothVectors hℓ _⟩
    rw [blockBForm_apply] at this
    simp only
    rw [this]
    simp only [LinearMap.comp_apply]
    ring
  · rw [hdetK g hg, hdet1, hu _ (hmem1 g hg), h11, Module.End.one_apply]

end Rep

end GodementJacquet

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open GLnLocal MeasureTheory Polynomial GJMatrix
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {m : ℕ} [NeZero m] [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin m) F × H) W}

theorem denom_eval_ne_zero_of_div {P Q : ℂ[X]} {x : ℂ} (hQ : Q.eval x ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q).denom.eval x ≠ 0 := by
  intro h
  obtain ⟨r, hr⟩ := RatFunc.denom_div_dvd P Q
  apply hQ
  rw [hr, eval_mul, h, zero_mul]

def reflPoly (κ : ℂ) (d : ℕ) (P : ℂ[X]) : ℂ[X] :=
  ∑ i ∈ Finset.range (d + 1), C (P.coeff i * κ ^ i) * X ^ (d - i)

theorem eval_reflPoly (κ : ℂ) {d : ℕ} {P : ℂ[X]} (hd : P.natDegree ≤ d) {x : ℂ} (hx : x ≠ 0) :
    (reflPoly κ d P).eval x = x ^ d * P.eval (κ / x) := by
  rw [reflPoly, eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [eval_mul, eval_C, eval_pow, eval_X, div_pow, mul_div_assoc', pow_sub₀ x hx hid]
  field_simp

theorem exists_poly_eval_inv (κ : ℂ) (P Q : ℂ[X]) :
    ∃ P' Q' : ℂ[X], ∀ x : ℂ, x ≠ 0 → Q.eval (κ / x) ≠ 0 →
      Q'.eval x ≠ 0 ∧ P'.eval x / Q'.eval x = P.eval (κ / x) / Q.eval (κ / x) := by
  set d := max P.natDegree Q.natDegree
  refine ⟨reflPoly κ d P, reflPoly κ d Q, fun x hx hQ => ?_⟩
  have hQ' : (reflPoly κ d Q).eval x ≠ 0 := by
    rw [eval_reflPoly κ (le_max_right _ _) hx]
    exact mul_ne_zero (pow_ne_zero _ hx) hQ
  refine ⟨hQ', ?_⟩
  rw [eval_reflPoly κ (le_max_left _ _) hx, eval_reflPoly κ (le_max_right _ _) hx,
    mul_div_mul_left _ _ (pow_ne_zero _ hx)]

theorem qs_natCast_sub (s : ℂ) : qs F ((m : ℂ) - s) = qs F (m : ℂ) / qs F s := by
  rw [sub_eq_add_neg, qs_add, div_eq_mul_inv]
  congr 1
  rw [qs, qs, neg_neg, Complex.cpow_neg, inv_inv]

theorem norm_mul_qs_pow (α : ℂ) (s : ℂ) :
    ‖α * qs F s ^ m‖ = ‖α‖ * (LocalField.residueCard F : ℝ) ^ (-(m * s.re)) := by
  have hq0 : (0 : ℝ) ≤ LocalField.residueCard F := Nat.cast_nonneg _
  rw [norm_mul, norm_pow, norm_qs, ← Real.rpow_natCast, ← Real.rpow_mul hq0]
  ring_nf

theorem norm_mul_qs_pow_lt_one {α : ℂ} (hα0 : α ≠ 0) {s : ℂ}
    (hs : Real.logb (LocalField.residueCard F) ‖α‖ / m < s.re) :
    ‖α * qs F s ^ m‖ < 1 := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [norm_mul_qs_pow, ← Real.rpow_logb (by linarith) hq.ne' (norm_pos_iff.2 hα0),
    ← Real.rpow_add (by linarith)]
  refine Real.rpow_lt_one_of_one_lt_of_neg hq ?_
  rw [div_lt_iff₀ hm] at hs
  linarith

theorem lt_norm_mul_qs_pow {α : ℂ} (hα0 : α ≠ 0) {s : ℂ}
    (hs : s.re < Real.logb (LocalField.residueCard F) ‖α‖ / m + m) :
    ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖ := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [norm_mul_qs_pow, ← Real.rpow_logb (by linarith) hq.ne' (norm_pos_iff.2 hα0),
    ← Real.rpow_add (by linarith), ← Real.rpow_natCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (by linarith)]
  refine Real.rpow_lt_rpow_of_exponent_lt hq ?_
  have : s.re * m < Real.logb (LocalField.residueCard F) ‖α‖ + m * m := by
    have := (lt_div_iff₀ hm).1 (show s.re - m < Real.logb (LocalField.residueCard F) ‖α‖ / m by
      linarith)
    linarith
  push_cast
  nlinarith

theorem exists_fixed_prod (hσ : IsSmooth σ) (v : W) (r₀ : ℕ) (K₀' : Subgroup H)
    (hK₀'c : IsCompact (K₀' : Set H)) (hK₀'o : IsOpen (K₀' : Set H)) :
    ∃ r ≥ r₀, ∃ K' : Subgroup H, K' ≤ K₀' ∧ IsCompact (K' : Set H) ∧ IsOpen (K' : Set H) ∧
      v ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K') := by
  have hst : (stabilizerOf σ v : Set (GL (Fin m) F × H)) ∈ nhds (1, 1) :=
    (hσ v).mem_nhds (one_mem _)
  obtain ⟨u, hu, t, ht, hut⟩ := mem_nhds_prod_iff.1 hst
  obtain ⟨r₁, -, hr₁⟩ := (hasBasis_nhds_one F m).mem_iff.1 hu
  obtain ⟨K'', hK''c, hK''t⟩ := exists_openSubgroup_isCompact_subset ht
  refine ⟨max r₀ r₁, le_max_left _ _, K''.toSubgroup ⊓ K₀', inf_le_right, ?_, ?_, ?_⟩
  · exact hK₀'c.of_isClosed_subset (K''.isClosed.inter (Subgroup.isClosed_of_isOpen _ hK₀'o))
      Set.inter_subset_right
  · exact K''.isOpen.inter hK₀'o
  · refine mem_fixedVectors.2 fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    have hk1' : k.1 ∈ u := hr₁ (congruenceSubgroup_antitone F m (le_max_right r₀ r₁) hk1)
    have hk2' : k.2 ∈ t := hK''t (Subgroup.mem_inf.1 hk2).1
    exact mem_stabilizerOf.1 (hut ⟨hk1', hk2'⟩)

theorem exists_fixed_prod₀ (hσ : IsSmooth σ) (v : W) :
    ∃ r : ℕ, ∃ K' : Subgroup H, IsCompact (K' : Set H) ∧ IsOpen (K' : Set H) ∧
      v ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K') := by
  obtain ⟨K₀, hK₀c, -⟩ := exists_openSubgroup_isCompact_subset (G := H) (U := Set.univ)
    Filter.univ_mem
  obtain ⟨r, -, K', -, hc, ho, hv⟩ := exists_fixed_prod hσ v 0 K₀.toSubgroup hK₀c K₀.isOpen
  exact ⟨r, K', hc, ho, hv⟩

theorem blockA_indGL (μ : Measure (GL (Fin m) F)) {r : ℕ} {K' : Subgroup H} {v : W}
    (hv : v ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K')) (ℓ : Module.Dual ℂ W) (s : ℂ) :
    blockA μ σ (indGL (congruenceSubgroup F m r : Set (GL (Fin m) F))) v ℓ s =
      μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) * ℓ v := by
  have hdet : ∀ g ∈ congruenceSubgroup F m r, detPow g s = 1 := fun g hg =>
    detPow_of_mem_integralGL (congruenceSubgroup_le F m r hg) s
  have hfix : ∀ g ∈ congruenceSubgroup F m r, σ (g, 1) v = v := fun g hg =>
    mem_fixedVectors.1 hv _ (Subgroup.mem_prod.2 ⟨hg, K'.one_mem⟩)
  simp only [blockA, mul_assoc]
  rw [integral_indGL_mul μ (isOpen_congruenceSubgroup F m r).measurableSet (x₀ := 1)
    (fun g hg => by rw [hdet g hg, hdet 1 (one_mem _), hfix g hg, hfix 1 (one_mem _)]),
    hdet 1 (one_mem _), one_mul, hfix 1 (one_mem _)]

theorem blockB_mul_blockA_eq (hσ : IsAdmissible σ) [σ.IsIrreducible] {α : ℂ} (hα0 : α ≠ 0)
    (hα : ∀ v, σ (centralUnif F m, 1) v = α • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      ∃ C : Set (GL (Fin m) F), IsCompact C ∧
        ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C)
    (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {s : ℂ} (hs : ‖α * qs F s ^ m‖ < 1)
    (hs' : ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖)
    {r₀ : ℕ} {K₀' : Subgroup H} (hK₀'c : IsCompact (K₀' : Set H)) (hK₀'o : IsOpen (K₀' : Set H))
    {v₀ : W} (hv₀ : v₀ ∈ fixedVectors σ ((congruenceSubgroup F m r₀).prod K₀'))
    {ℓ₀ : Module.Dual ℂ W} (hℓ₀ : ℓ₀ ∈ smoothVectors (Representation.dual σ))
    {Φ : Matrix (Fin m) (Fin m) F → ℂ} (hΦ : IsSchwartzBruhat Φ) (v : W) {ℓ : Module.Dual ℂ W}
    (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    blockB μ σ (localMatrixFourier ψ Φ) v ℓ s *
        blockA μ σ (indGL (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))) v₀ ℓ₀ s =
      blockB μ σ (localMatrixFourier ψ (indGL (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))))
          v₀ ℓ₀ s * blockA μ σ Φ v ℓ s := by
  obtain ⟨r, hr, K', hK'le, hK'c, hK'o, hv⟩ := exists_fixed_prod hσ.1 v r₀ K₀' hK₀'c hK₀'o
  obtain ⟨c, hc⟩ := exists_blockB_eq_smul hσ hα0 hα hsupp μ hψ hψ1 hs hs'
    (isCompact_congruenceSubgroup F m r) (isOpen_congruenceSubgroup F m r)
    (congruenceSubgroup_le F m r) hK'c hK'o
  have hv₀' : v₀ ∈ fixedVectors σ ((congruenceSubgroup F m r).prod K') := by
    refine mem_fixedVectors.2 fun k hk => mem_fixedVectors.1 hv₀ k ?_
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hk
    exact Subgroup.mem_prod.2 ⟨congruenceSubgroup_antitone F m hr h1, hK'le h2⟩
  have he₀ := isSchwartzBruhat_indGL (isCompact_congruenceSubgroup F m r₀)
    (isOpen_congruenceSubgroup F m r₀)
  have h1 := hc Φ hΦ v hv ℓ hℓ
  have h2 := hc _ he₀ v₀ hv₀' ℓ₀ hℓ₀
  have hμK : ((μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) : ℝ) : ℂ) ≠ 0 := by
    have : μ.real (congruenceSubgroup F m r : Set (GL (Fin m) F)) ≠ 0 := by
      rw [measureReal_ne_zero_iff ((isCompact_congruenceSubgroup F m r).measure_lt_top.ne)]
      exact ((isOpen_congruenceSubgroup F m r).measure_pos μ ⟨1, one_mem _⟩).ne'
    exact_mod_cast this
  apply mul_left_cancel₀ hμK
  linear_combination (blockA μ σ (indGL (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))) v₀ ℓ₀ s) *
    h1 - (blockA μ σ Φ v ℓ s) * h2

theorem exists_blockFE (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure] (hσ : IsAdmissible σ)
    [σ.IsIrreducible] {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {α : ℂ}
    (hα : ∀ v, σ (centralUnif F m, 1) v = α • v)
    (hsupp : ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      ∃ C : Set (GL (Fin m) F), IsCompact C ∧
        ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C) :
    ∃ γ : RatFunc ℂ, ∃ s₁ : ℝ, ∀ Φ : Matrix (Fin m) (Fin m) F → ℂ, IsSchwartzBruhat Φ → ∀ v : W,
      ∀ ℓ ∈ smoothVectors (Representation.dual σ),
        (∀ s : ℂ, s₁ < s.re → Integrable (fun g : GL (Fin m) F =>
          Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * ℓ (σ (g, 1) v)) μ) ∧
        (∀ s : ℂ, s.re < -s₁ → Integrable (fun g : GL (Fin m) F =>
          GJMatrix.localMatrixFourier ψ Φ (g : Matrix (Fin m) (Fin m) F) * detPow g (m - s) *
            ℓ (σ (g⁻¹, 1) v)) μ) ∧
        RatFE F γ (blockA μ σ Φ v ℓ) (blockB μ σ (GJMatrix.localMatrixFourier ψ Φ) v ℓ) := by
  classical

  obtain ⟨v₀, hv₀ne⟩ := exists_ne_zero_of_isIrreducible (ρ := σ)
  have hα0 : α ≠ 0 := by
    intro h0
    apply hv₀ne
    have h1 := hα v₀
    rw [h0, zero_smul] at h1
    have h2 := congrArg (σ ((centralUnif F m, (1 : H))⁻¹)) h1
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at h2

  obtain ⟨r₀, K₀', hK₀'c, hK₀'o, hv₀⟩ := exists_fixed_prod₀ hσ.1 v₀
  set 𝕂₀ := (congruenceSubgroup F m r₀).prod K₀'
  have h𝕂₀c : IsCompact (𝕂₀ : Set (GL (Fin m) F × H)) := by
    rw [Subgroup.coe_prod]; exact (isCompact_congruenceSubgroup F m r₀).prod hK₀'c
  have h𝕂₀o : IsOpen (𝕂₀ : Set (GL (Fin m) F × H)) := by
    rw [Subgroup.coe_prod]; exact (isOpen_congruenceSubgroup F m r₀).prod hK₀'o
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (fixedVectors σ 𝕂₀), φ ⟨v₀, hv₀⟩ ≠ 0 := by
    by_contra h
    push Not at h
    exact hv₀ne (congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h))
  set ef := fixedContragredientEquiv hσ.1 h𝕂₀c h𝕂₀o with hef
  set ℓ₀ : Module.Dual ℂ W := (((ef.symm φ : fixedVectors (contragredient σ) 𝕂₀) :
    smoothVectors (Representation.dual σ)) : Module.Dual ℂ W) with hℓ₀def
  have hℓ₀ : ℓ₀ ∈ smoothVectors (Representation.dual σ) :=
    ((ef.symm φ : fixedVectors (contragredient σ) 𝕂₀) : smoothVectors (Representation.dual σ)).2
  have hℓ₀v₀ : ℓ₀ v₀ ≠ 0 := by
    have h := congrArg (fun f : Module.Dual ℂ (fixedVectors σ 𝕂₀) => f ⟨v₀, hv₀⟩)
      (ef.apply_symm_apply φ)
    rw [hef, fixedContragredientEquiv_apply, restrictFixed_apply] at h
    rw [hℓ₀def, hef, h]
    exact hφ
  set K₀ : Set (GL (Fin m) F) := (congruenceSubgroup F m r₀ : Set (GL (Fin m) F))
  have he₀ : IsSchwartzBruhat (indGL K₀) := isSchwartzBruhat_indGL
    (isCompact_congruenceSubgroup F m r₀) (isOpen_congruenceSubgroup F m r₀)
  set A₀ : ℂ := (μ.real K₀ : ℂ) * ℓ₀ v₀ with hA₀def
  have hA₀ : A₀ ≠ 0 := by
    refine mul_ne_zero ?_ hℓ₀v₀
    have : μ.real K₀ ≠ 0 := by
      rw [measureReal_ne_zero_iff ((isCompact_congruenceSubgroup F m r₀).measure_lt_top.ne)]
      exact ((isOpen_congruenceSubgroup F m r₀).measure_pos μ ⟨1, one_mem _⟩).ne'
    exact_mod_cast this
  have hA₀s : ∀ s, blockA μ σ (indGL K₀) v₀ ℓ₀ s = A₀ := fun s => blockA_indGL μ hv₀ ℓ₀ s

  set a : ℝ := Real.logb (LocalField.residueCard F) ‖α‖ / m with ha
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)

  have hdual : ∀ {v : W} {ℓ : Module.Dual ℂ W}, ℓ ∈ smoothVectors (Representation.dual σ) →
      ∀ {Φ : Matrix (Fin m) (Fin m) F → ℂ}, IsSchwartzBruhat Φ →
      ∃ P' Q' : ℂ[X], ∀ s : ℂ,
        ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖ →
          Q'.eval (qs F s) ≠ 0 ∧
            blockB μ σ (localMatrixFourier ψ Φ) v ℓ s = P'.eval (qs F s) / Q'.eval (qs F s) := by
    intro v ℓ hℓ Φ hΦ
    obtain ⟨P, N, hP⟩ := (isCentralCoeff_coeff hσ.1 hα0 hα hsupp v hℓ).inv.exists_eq_div_zeta μ
      (hΦ.localMatrixFourier hψ hψ1)
    obtain ⟨P', Q', hPQ⟩ := exists_poly_eval_inv (qs F (m : ℂ)) P (X ^ N * (1 - C α⁻¹ * X ^ m))
    refine ⟨P', Q', fun s hs' => ?_⟩
    have hlt := norm_inv_mul_qs_sub_lt_one hα0 hs'
    have hy : qs F ((m : ℂ) - s) = qs F (m : ℂ) / qs F s := qs_natCast_sub s
    have hQ : (X ^ N * (1 - C α⁻¹ * X ^ m) : ℂ[X]).eval (qs F (m : ℂ) / qs F s) ≠ 0 := by
      rw [← hy]
      simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
      refine mul_ne_zero (pow_ne_zero _ (qs_ne_zero _)) fun h => ?_
      have : α⁻¹ * qs F ((m : ℂ) - s) ^ m = 1 := by linear_combination -h
      rw [this, norm_one] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨hQ', heq⟩ := hPQ (qs F s) (qs_ne_zero s) hQ
    refine ⟨hQ', ?_⟩
    rw [heq, ← hy]
    have := hP ((m : ℂ) - s) hlt
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
    exact this
  obtain ⟨Pr, Qr, hPQr⟩ := hdual hℓ₀ he₀
  set γ : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) (C A₀⁻¹ * Pr) / algebraMap ℂ[X] (RatFunc ℂ) Qr
  refine ⟨γ, max a (-(a + m)), fun Φ hΦ v ℓ hℓ => ⟨fun s hs => ?_, fun s hs => ?_, ?_⟩⟩
  · exact integrable_blockA hσ.1 hα0 hα hsupp μ hΦ v hℓ
      (norm_mul_qs_pow_lt_one hα0 (lt_of_le_of_lt (le_max_left _ _) hs))
  · exact integrable_blockB hσ.1 hα0 hα hsupp μ (hΦ.localMatrixFourier hψ hψ1) v hℓ
      (lt_norm_mul_qs_pow hα0 (by have := le_max_right a (-(a + m)); linarith))
  ·
    obtain ⟨PA, NA, hPA⟩ := (isCentralCoeff_coeff hσ.1 hα0 hα hsupp v hℓ).exists_eq_div_zeta μ hΦ
    set QA : ℂ[X] := X ^ NA * (1 - C α * X ^ m)
    set RA : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) PA / algebraMap ℂ[X] (RatFunc ℂ) QA
    have hAeval : ∀ s : ℂ, ‖α * qs F s ^ m‖ < 1 →
        QA.eval (qs F s) ≠ 0 ∧ blockA μ σ Φ v ℓ s = RA.eval (RingHom.id ℂ) (qs F s) := by
      intro s hs
      have hQ : QA.eval (qs F s) ≠ 0 := by
        simp only [QA, eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
        refine mul_ne_zero (pow_ne_zero _ (qs_ne_zero _)) fun h => ?_
        have : α * qs F s ^ m = 1 := by linear_combination -h
        rw [this, norm_one] at hs
        exact lt_irrefl _ hs
      refine ⟨hQ, ?_⟩
      rw [eval_div_algebraMap _ _ hQ, blockA, hPA s hs]
      simp only [QA, eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
    obtain ⟨PB, QB, hPQB⟩ := hdual hℓ hΦ
    set RB : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) PB / algebraMap ℂ[X] (RatFunc ℂ) QB
    have hBeval : ∀ s : ℂ, ((LocalField.residueCard F : ℝ) ^ m) ^ (-(m : ℤ)) < ‖α * qs F s ^ m‖ →
        blockB μ σ (localMatrixFourier ψ Φ) v ℓ s = RB.eval (RingHom.id ℂ) (qs F s) := by
      intro s hs'
      obtain ⟨hQ, heq⟩ := hPQB s hs'
      rw [heq, eval_div_algebraMap _ _ hQ]

    have hid : RB = γ * RA := by
      set t : ℕ → ℝ := fun k => a + m / (k + 2)
      have ht : ∀ k, a < t k ∧ t k < a + m := fun k => by
        have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        refine ⟨by simp only [t]; have := div_pos hm hk; linarith, ?_⟩
        simp only [t]
        have : m / ((k : ℝ) + 2) < m := by
          rw [div_lt_iff₀ hk]; nlinarith
        linarith
      refine eq_of_eval_eq_of_infinite (S := Set.range fun k : ℕ => qs F ((t k : ℝ) : ℂ)) ?_ ?_
      · refine Set.infinite_range_of_injective fun k l hkl => ?_
        have hn := congrArg norm hkl
        simp only [norm_qs, Complex.ofReal_re] at hn
        have hq : (1 : ℝ) < LocalField.residueCard F := by
          exact_mod_cast LocalField.one_lt_residueCard
        have htt : t k = t l := by
          have hl := congrArg (Real.logb (LocalField.residueCard F)) hn
          rw [Real.logb_rpow (by linarith) hq.ne', Real.logb_rpow (by linarith) hq.ne'] at hl
          linarith
        simp only [t, add_right_inj] at htt
        have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have hl : (0 : ℝ) < (l : ℝ) + 2 := by positivity
        rw [div_eq_div_iff hk.ne' hl.ne'] at htt
        have : (k : ℝ) = l := by nlinarith
        exact_mod_cast this
      · rintro x ⟨k, rfl⟩
        set s : ℂ := ((t k : ℝ) : ℂ)
        have hsre : s.re = t k := Complex.ofReal_re _
        have hs : ‖α * qs F s ^ m‖ < 1 := norm_mul_qs_pow_lt_one hα0 (by rw [hsre]; exact (ht k).1)
        have hs' := lt_norm_mul_qs_pow hα0 (s := s) (by rw [hsre]; exact (ht k).2)
        obtain ⟨hQA, hA⟩ := hAeval s hs
        obtain ⟨hQr, hr⟩ := hPQr s hs'
        have hcross := blockB_mul_blockA_eq hσ hα0 hα hsupp μ hψ hψ1 hs hs' hK₀'c hK₀'o hv₀ hℓ₀ hΦ v
          hℓ
        rw [hA₀s] at hcross
        rw [← hBeval s hs', RatFunc.eval_mul (hx := denom_eval_ne_zero_of_div hQr)
          (hy := denom_eval_ne_zero_of_div hQA), eval_div_algebraMap _ _ hQr, ← hA]
        simp only [eval_mul, eval_C]
        rw [mul_div_assoc, ← hr]
        field_simp
        linear_combination hcross
    refine ⟨RA, max a (-(a + m)), fun s hs => ?_, fun s hs => ?_⟩
    · exact (hAeval s (norm_mul_qs_pow_lt_one hα0 (lt_of_le_of_lt (le_max_left _ _) hs))).2
    · rw [← hid]
      exact hBeval s (lt_norm_mul_qs_pow hα0 (by have := le_max_right a (-(a + m)); linarith))

end GodementJacquet

end GroundTheory.Automorphic
end
end
