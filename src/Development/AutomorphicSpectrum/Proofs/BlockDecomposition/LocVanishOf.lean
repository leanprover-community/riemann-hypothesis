import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfCommuteOfSeparable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBasisDiagonalTwistedCentralizer
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralFiberDecompositionInvariant

section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.NilChangeVar

namespace GlobalTheory.CompanionTheory.LocVan

theorem nilChange_of_flag : NilChange := by
  intro n d W₁ W₂ hreg _ hle h1 h2
  let L : nilrad W₁ W₂ ≃ₗ[ℝ] nilrad W₁ W₂ :=
    LinearEquiv.ofInjectiveEndo (slinN d h1 h2 - LinearMap.id) (slinN_injective d h1 h2 hreg)
  have hLval : ∀ X, (L X).1 = slin d X.1 - X.1 := fun X => by
    simp [L, slinN]
  have hLc : Continuous L := by
    refine Continuous.subtype_mk (f := fun X : nilrad W₁ W₂ => (L X).1) ?_ _ |>.congr fun X => rfl
    have e : (fun X : nilrad W₁ W₂ => (L X).1) = fun X => slin d X.1 - X.1 := funext hLval
    rw [e]
    exact ((continuous_slin d).comp continuous_subtype_val).sub continuous_subtype_val
  let Q : nilrad W₁ W₂ → nilrad W₁ W₂ := fun X =>
    ⟨quad d X.1, two_mem hle (quadratic_term_nilradical_mem d h1 h2 X.2).1 (quadratic_term_nilradical_mem d h1 h2 X.2).2⟩
  have hQc : Continuous Q :=
    Continuous.subtype_mk ((continuous_quad d).comp continuous_subtype_val) _
  have hLF : ∀ y ∈ nilrad2 W₁ W₂, L y ∈ nilrad2 W₁ W₂ := fun y hy => by
    obtain ⟨hT, hT'⟩ := semilinear_term_nilradical_mem d h1 h2 hy.1 hy.2
    refine ⟨fun z => ?_, fun z hz => ?_⟩
    · rw [hLval, Matrix.sub_mulVec]; exact W₁.sub_mem (hT z) (hy.1 z)
    · rw [hLval, Matrix.sub_mulVec, hT' z hz, hy.2 z hz, sub_zero]
  have hQF : ∀ X, Q X ∈ nilrad2 W₁ W₂ := fun X => quadratic_term_nilradical_mem d h1 h2 X.2
  have hQinv : ∀ X, ∀ Y ∈ nilrad2 W₁ W₂, Q (X + Y) = Q X := fun X Y hY =>
    Subtype.ext (quad_add d h1 h2 X.2 hle hY.1 hY.2)
  refine ⟨fun X => L X + Q X, hLc.add hQc, fun X => ?_, ?_⟩
  · rw [eq_inv_mul_iff_mul_eq]
    refine Units.ext ?_
    have e : (uOf (L X + Q X)).val = 1 + (slin d X.1 - X.1 + quad d X.1) := by
      rw [uOf_val, Submodule.coe_add, hLval]
    rw [Units.val_mul, e]
    exact twist_val d h1 h2 (uOf X) X.1 X.2 rfl
  · intro _ _ ν _
    obtain ⟨Φ, c, _, hΦ, hmap⟩ := exists_homeo_map_eq_smul ν (nilrad2 W₁ W₂) L hLF Q hQc hQF hQinv
    refine ⟨c, ?_⟩
    have e : (fun X => L X + Q X) = Φ := funext fun X => (hΦ X).symm
    rw [e]
    exact hmap

end GlobalTheory.CompanionTheory.LocVan
end

section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_change_of_variables : GlobalTheory.CompanionTheory.LocVan.NilChange := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.nilChange_of_flag | exact GlobalTheory.CompanionTheory.LocVan.nilChange_of_flag | (intros; apply GlobalTheory.CompanionTheory.LocVan.nilChange_of_flag <;> assumption)
end

section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_diagonal_twisted_centralizer : ∀ (n : ℕ) (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∃ P : GL (Fin n) ℂ,
    (∀ t ∈ twCent (thC n) d, ∃ a : Fin n → ℂ, (P⁻¹ * t * P).val = Matrix.diagonal a) ∧
    (∀ X ∈ nilrad W₁ W₂, ∀ i, ((P⁻¹ : GL (Fin n) ℂ).val * X * P.val) i i = 0) ∧
    (∀ t ∈ twCent (thC n) d, img t W₁ = W₁ ∧ img t W₂ = W₂) := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.Frame.eigenframe | exact GlobalTheory.CompanionTheory.LocVan.Frame.eigenframe | (intros; apply GlobalTheory.CompanionTheory.LocVan.Frame.eigenframe <;> assumption)
end

section
section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan.Slice

def dg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (Matrix.diag M)

theorem continuous_dg {n : ℕ} : Continuous (dg (n := n)) :=
  continuous_id.matrix_diag.matrix_diagonal

theorem dg_one_add_mul {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ)
    (hZ : ∀ i, Z i i = 0) : dg ((1 + Z) * Matrix.diagonal a) = Matrix.diagonal a := by
  unfold dg
  congr 1
  funext i
  simp [Matrix.diag_apply, Matrix.mul_diagonal, hZ]

theorem dg_mul_one_add {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ)
    (hZ : ∀ i, Z i i = 0) : dg (Matrix.diagonal a * (1 + Z)) = Matrix.diagonal a := by
  unfold dg
  congr 1
  funext i
  simp [Matrix.diag_apply, Matrix.diagonal_mul, hZ]

theorem isCompact_units {n : ℕ} {B₁ B₂ : Set (Matrix (Fin n) (Fin n) ℂ)}
    (h₁ : IsCompact B₁) (h₂ : IsCompact B₂) :
    IsCompact {u : GL (Fin n) ℂ | u.val ∈ B₁ ∧ (u⁻¹ : GL (Fin n) ℂ).val ∈ B₂} := by
  have h := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin n) (Fin n) ℂ)).isCompact_preimage
      (h₁.prod (h₂.image MulOpposite.continuous_op))
  convert h using 1
  ext u
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, ⟨_, h', rfl⟩⟩
  · rintro ⟨h, ⟨x, hx, e⟩⟩
    have e' : x = (u⁻¹ : GL (Fin n) ℂ).val := MulOpposite.op_injective e
    exact ⟨h, e' ▸ hx⟩

theorem conj_uOf_val {n : ℕ} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (P : GL (Fin n) ℂ)
    (X : nilrad W₁ W₂) :
    (P⁻¹ * uOf X * P).val = 1 + (P⁻¹ : GL (Fin n) ℂ).val * X.1 * P.val := by
  have h1 : (P⁻¹ : GL (Fin n) ℂ).val * P.val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem slice_measure_ne_top : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
  (P : GL (Fin n) ℂ), W₁ ≤ W₂ →
  (∀ t ∈ twCent (thC n) d, ∃ a : Fin n → ℂ, (P⁻¹ * t * P).val = Matrix.diagonal a) →
  (∀ X ∈ nilrad W₁ W₂, ∀ i, ((P⁻¹ : GL (Fin n) ℂ).val * X * P.val) i i = 0) →
  ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤ := by
  intro n _ _ d μd _ W₁ W₂ P hW hdiag hzero C hC g
  let D₁ : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun c => dg (P⁻¹ * (c * g⁻¹) * P).val
  let D₂ : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun c => dg (P⁻¹ * (g * c⁻¹) * P).val
  have hD₁ : Continuous D₁ := continuous_dg.comp
    (Units.continuous_val.comp ((continuous_const.mul (continuous_id.mul continuous_const)).mul
      continuous_const))
  have hD₂ : Continuous D₂ := continuous_dg.comp
    (Units.continuous_val.comp ((continuous_const.mul (continuous_const.mul continuous_inv)).mul
      continuous_const))
  have hK := isCompact_units (hC.image hD₁) (hC.image hD₂)
  have hK' := hK.image (f := fun u : GL (Fin n) ℂ => P * u * P⁻¹)
    ((continuous_const.mul continuous_id).mul continuous_const)
  have hKT := (isClosed_twCent d).isClosedEmbedding_subtypeVal.isCompact_preimage hK'
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) hKT.measure_lt_top)
  rintro ⟨t, ht⟩ ⟨X, c, hc, hX⟩
  change uOf X * c = t * g at hX
  obtain ⟨a, ha⟩ := hdiag t ht
  obtain ⟨b, hb⟩ := hdiag t⁻¹ ((twCent (thC n) d).inv_mem ht)
  have hcX : c = (uOf X)⁻¹ * (t * g) := eq_inv_mul_of_mul_eq hX
  have e₁ : P⁻¹ * (c * g⁻¹) * P = (P⁻¹ * uOf (ninv hW X) * P) * (P⁻¹ * t * P) := by
    rw [uOf_ninv, hcX]; group
  have e₂ : P⁻¹ * (g * c⁻¹) * P = (P⁻¹ * t⁻¹ * P) * (P⁻¹ * uOf X * P) := by
    rw [hcX]; group
  have e₃ : (P⁻¹ * t * P)⁻¹ = P⁻¹ * t⁻¹ * P := by group
  refine ⟨P⁻¹ * t * P, ⟨⟨c, hc, ?_⟩, ⟨c, hc, ?_⟩⟩, by group⟩
  · change dg (P⁻¹ * (c * g⁻¹) * P).val = _
    rw [e₁, Units.val_mul, conj_uOf_val, ha]
    exact dg_one_add_mul _ _ (hzero _ (ninv hW X).2)
  · change dg (P⁻¹ * (g * c⁻¹) * P).val = _
    rw [e₂, e₃, Units.val_mul, conj_uOf_val, hb]
    exact dg_mul_one_add _ _ (hzero _ X.2)

end GlobalTheory.CompanionTheory.LocVan.Slice
end
end

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_compact_of_diagonal_nilradical : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
  (P : GL (Fin n) ℂ), W₁ ≤ W₂ →
  (∀ t ∈ twCent (thC n) d, ∃ a : Fin n → ℂ, (P⁻¹ * t * P).val = Matrix.diagonal a) →
  (∀ X ∈ nilrad W₁ W₂, ∀ i, ((P⁻¹ : GL (Fin n) ℂ).val * X * P.val) i i = 0) →
  ∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LocVan.Slice.slice_measure_ne_top
end

section
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

theorem integral_eq_zero_of_unfolding {G H : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] [MeasurableSpace H] (ν : Measure H)
    [SFinite ν] (u : H → G) (hu : Measurable u) (w ρ : G → ℝ≥0∞) (F : G → ℂ)
    (hw : Measurable w) (hρ : Measurable ρ) (hF : Measurable F)
    (hw1 : ∀ g, ∫⁻ h, w ((u h)⁻¹ * g) ∂ν = 1) (hρu : ∀ h g, ρ (u h * g) = ρ g)
    (hF0 : ∀ q, ∫ h, F (u h * q) ∂ν = 0) : ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = 0 := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : G → ℂ, K = fun g => F g * ((ρ g).toReal : ℂ) := ⟨_, rfl⟩
  have hKm : Measurable K := by
    rw [hK]; exact hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)
  rw [show (∫ g, F g * ((ρ g).toReal : ℂ) ∂μ) = ∫ g, K g ∂μ by rw [hK]]
  by_cases hKi : Integrable K μ
  swap
  · exact integral_undef hKi
  obtain ⟨wT, hwT⟩ : ∃ wT : G → ℝ, wT = fun g => (w g).toReal := ⟨_, rfl⟩
  have hwTm : Measurable wT := by rw [hwT]; exact hw.ennreal_toReal
  have hs : Measurable (fun p : H × G => (u p.1)⁻¹ * p.2) :=
    (hu.comp measurable_fst).inv.mul measurable_snd
  have hone : ∀ g, ∫ h, wT ((u h)⁻¹ * g) ∂ν = 1 := by
    intro g
    have hm : Measurable fun h => w ((u h)⁻¹ * g) := hw.comp (hu.inv.mul_const g)
    have hfin : ∀ᵐ h ∂ν, w ((u h)⁻¹ * g) < ⊤ := ae_lt_top hm (by rw [hw1]; simp)
    rw [hwT]
    simp only []
    rw [integral_toReal hm.aemeasurable hfin, hw1]; simp
  obtain ⟨φ, hφ⟩ : ∃ φ : H × G → ℂ, φ = fun p => K p.2 * (wT ((u p.1)⁻¹ * p.2) : ℂ) := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]
    exact (hKm.comp measurable_snd).mul
      (Complex.measurable_ofReal.comp (hwTm.comp hs))
  have hφi : Integrable φ (ν.prod μ) := by
    refine ⟨hφm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hφm.enorm.aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono (g := fun g => ‖K g‖ₑ) ?_) hKi.2
    intro g
    have hb : ∀ h, ‖φ (h, g)‖ₑ ≤ ‖K g‖ₑ * w ((u h)⁻¹ * g) := by
      intro h
      rw [hφ, hwT]
      simp only [enorm_mul]
      gcongr
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
    calc ∫⁻ h, ‖φ (h, g)‖ₑ ∂ν ≤ ∫⁻ h, ‖K g‖ₑ * w ((u h)⁻¹ * g) ∂ν := lintegral_mono hb
      _ = ‖K g‖ₑ := by
        have hm : Measurable fun h => w ((u h)⁻¹ * g) := hw.comp (hu.inv.mul_const g)
        rw [lintegral_const_mul _ hm, hw1, mul_one]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : H × G → ℂ, ψ = fun p => K (u p.1 * p.2) * (wT p.2 : ℂ) := ⟨_, rfl⟩
  have hshear : MeasurePreserving (fun p : H × G => (p.1, u p.1 * p.2)) (ν.prod μ) (ν.prod μ) := by
    refine MeasurePreserving.skew_product (g := fun h x => u h * x) (MeasurePreserving.id ν)
      ((hu.comp measurable_fst).mul measurable_snd) ?_
    exact Filter.Eventually.of_forall fun h => map_mul_left_eq_self μ (u h)
  have hψφ : ψ = φ ∘ (fun p : H × G => (p.1, u p.1 * p.2)) := by
    funext p
    simp [hψ, hφ]
  have hψi : Integrable ψ (ν.prod μ) := by
    rw [hψφ]
    exact hshear.integrable_comp hφm.aestronglyMeasurable |>.mpr hφi
  have step1 : ∫ g, K g ∂μ = ∫ g, ∫ h, φ (h, g) ∂ν ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have : ∫ h, φ (h, g) ∂ν = K g * ((∫ h, wT ((u h)⁻¹ * g) ∂ν : ℝ) : ℂ) := by
      rw [hφ, ← integral_complex_ofReal, ← integral_const_mul]
    simp only [this, hone g, Complex.ofReal_one, mul_one]
  have step2 : ∫ g, ∫ h, φ (h, g) ∂ν ∂μ = ∫ h, ∫ g, φ (h, g) ∂μ ∂ν :=
    (integral_integral_swap (f := fun h g => φ (h, g)) hφi).symm
  have step3 : ∫ h, ∫ g, φ (h, g) ∂μ ∂ν = ∫ h, ∫ g, ψ (h, g) ∂μ ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    have := integral_mul_left_eq_self (μ := μ) (fun g => φ (h, g)) (u h)
    simp only []
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [hψ, hφ]
  have step4 : ∫ h, ∫ g, ψ (h, g) ∂μ ∂ν = ∫ g, ∫ h, ψ (h, g) ∂ν ∂μ :=
    integral_integral_swap (f := fun h g => ψ (h, g)) hψi
  have step5 : ∫ g, ∫ h, ψ (h, g) ∂ν ∂μ = 0 := by
    have : ∀ g, ∫ h, ψ (h, g) ∂ν = 0 := by
      intro g
      have e : ∀ h, ψ (h, g) = (((ρ g).toReal : ℂ) * (wT g : ℂ)) * F (u h * g) := by
        intro h
        rw [hψ, hK]
        simp only [hρu]
        ring
      simp only [e]
      rw [integral_const_mul, hF0, mul_zero]
    simp [this]
  rw [step1, step2, step3, step4, step5]

end GlobalTheory.CompanionTheory.LocVan
end

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unfold_weighted_average : ∀ {G H : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] [MeasurableSpace H] (ν : Measure H) [SFinite ν]
  (u : H → G), Measurable u → ∀ (w ρ : G → ℝ≥0∞) (F : G → ℂ), Measurable w → Measurable ρ → Measurable F →
  (∀ g, ∫⁻ h, w ((u h)⁻¹ * g) ∂ν = 1) → (∀ h g, ρ (u h * g) = ρ g) →
  (∀ q, ∫ h, F (u h * q) ∂ν = 0) → ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LocVan.integral_eq_zero_of_unfolding
end

section
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

theorem det_one_add_sqZero {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (M : E →ₗ[ℝ] E) (hM : M * M = 0) : LinearMap.det (1 + M) = 1 := by
  have hnil : IsNilpotent (-M) := ⟨2, by rw [pow_two, neg_mul_neg, hM]⟩
  have hc := hnil.charpoly_eq_X_pow_finrank
  let b := Module.finBasis ℝ E
  have h1 : (LinearMap.toMatrix b b (-M)).charpoly.eval 1 = 1 := by
    rw [LinearMap.charpoly_toMatrix, hc]; simp
  rw [Matrix.eval_charpoly] at h1
  rw [← LinearMap.det_toMatrix b, ← h1]
  congr 1
  simp [map_add, LinearMap.toMatrix_one]

theorem measurePreserving_add_one_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (ν : Measure E)
    [ν.IsAddHaarMeasure] (M : E →ₗ[ℝ] E) (hM : M * M = 0) (Y : E) :
    MeasurePreserving (fun X => Y + (1 + M) X) ν ν := by
  have hdet := det_one_add_sqZero M hM
  have hL : MeasurePreserving (fun X => (1 + M : E →ₗ[ℝ] E) X) ν ν := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := ν) (f := (1 + M : E →ₗ[ℝ] E))
      (by rw [hdet]; exact one_ne_zero)
    rw [this, hdet]; simp
  exact (measurePreserving_add_left ν Y).comp hL

theorem nmul_measurePreserving : ∀ (n : ℕ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] (Y : nilrad W₁ W₂),
  MeasurePreserving (nmul hW Y) ν ν := by
  intro n W₁ W₂ hW mS bS ν hν Y
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  let M : nilrad W₁ W₂ →ₗ[ℝ] nilrad W₁ W₂ :=
    { toFun := fun X => ⟨Y.1 * X.1, nil_mul_mem hW Y.2 X.2⟩
      map_add' := fun A B => Subtype.ext (by simp [mul_add])
      map_smul' := fun c A => Subtype.ext (by simp) }
  have hM : M * M = 0 := by
    ext1 X
    apply Subtype.ext
    change Y.1 * (Y.1 * X.1) = 0
    have h : ∀ y, (Y.1 * (Y.1 * X.1)) *ᵥ y = 0 := fun y => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact Y.2.2.2 _ (Y.2.2.1 _ (X.2.1 y))
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa using this
  haveI : FiniteDimensional ℝ (nilrad W₁ W₂) := FiniteDimensional.complexToReal _
  have key := @measurePreserving_add_one_add (nilrad W₁ W₂) (Submodule.normedAddCommGroup _)
    (Submodule.normedSpace _) _ mS bS ν hν M hM Y
  convert key using 1
  funext X
  apply Subtype.ext
  change Y.1 + X.1 + Y.1 * X.1 = Y.1 + (X.1 + Y.1 * X.1)
  abel

end GlobalTheory.CompanionTheory.LocVan
end

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_translation_measure_preserving : ∀ (n : ℕ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] (Y : nilrad W₁ W₂),
  MeasurePreserving (nmul hW Y) ν ν := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LocVan.nmul_measurePreserving
end

section
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.LocVan.TNorm

variable {n : ℕ}

theorem uOf_zero' (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) : uOf (0 : nilrad W₁ W₂) = 1 :=
  Units.ext (by simp)

theorem uOf_mul_mem_nSet {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    (C : Set (GL (Fin n) ℂ)) (X : nilrad W₁ W₂) (x : GL (Fin n) ℂ) :
    uOf X * x ∈ nSet W₁ W₂ C ↔ x ∈ nSet W₁ W₂ C := by
  constructor
  · rintro ⟨Y, c, hc, h⟩
    refine ⟨nmul hW (ninv hW X) Y, c, hc, ?_⟩
    rw [uOf_nmul, uOf_ninv, mul_assoc, h, inv_mul_cancel_left]
  · rintro ⟨Y, c, hc, rfl⟩
    exact ⟨nmul hW X Y, c, hc, by rw [uOf_nmul, mul_assoc]⟩

theorem nSet_mono (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {C C' : Set (GL (Fin n) ℂ)} (h : C ⊆ C') :
    nSet W₁ W₂ C ⊆ nSet W₁ W₂ C' := by
  rintro _ ⟨X, c, hc, rfl⟩
  exact ⟨X, c, h hc, rfl⟩

theorem isOpen_nSet (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {U : Set (GL (Fin n) ℂ)} (hU : IsOpen U) :
    IsOpen (nSet W₁ W₂ U) := by
  have e : nSet W₁ W₂ U = ⋃ X : nilrad W₁ W₂, (fun g => (uOf X)⁻¹ * g) ⁻¹' U := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨X, c, hc, rfl⟩
      exact ⟨X, by simpa using hc⟩
    · rintro ⟨X, hX⟩
      exact ⟨X, _, hX, by simp⟩
  rw [e]
  exact isOpen_iUnion fun X => hU.preimage (continuous_const.mul continuous_id)

theorem measurableSet_nSet [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {C : Set (GL (Fin n) ℂ)} (hC : IsCompact C) :
    MeasurableSet (nSet W₁ W₂ C) := by
  haveI := locallyCompact_nilrad W₁ W₂
  haveI := secondCountable_nilrad W₁ W₂
  let K := CompactExhaustion.choice (nilrad W₁ W₂)
  have hcont : Continuous fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => uOf p.1 * p.2 :=
    (continuous_uOf.comp continuous_fst).mul continuous_snd
  have e : nSet W₁ W₂ C =
      ⋃ k, (fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => uOf p.1 * p.2) '' (K k ×ˢ C) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨X, c, hc, rfl⟩
      obtain ⟨k, hk⟩ := K.exists_mem X
      exact ⟨k, (X, c), ⟨hk, hc⟩, rfl⟩
    · rintro ⟨k, ⟨X, c⟩, ⟨_, hc⟩, rfl⟩
      exact ⟨X, c, hc, rfl⟩
  rw [e]
  exact MeasurableSet.iUnion fun k => (((K.isCompact k).prod hC).image hcont).measurableSet

def zSet (T : Subgroup (GL (Fin n) ℂ)) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (U : Set (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ) :=
  {g | ∃ t ∈ T, ∃ X : nilrad W₁ W₂, ∃ c ∈ U, t * uOf X * c = g}

theorem isOpen_zSet (T : Subgroup (GL (Fin n) ℂ)) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    {U : Set (GL (Fin n) ℂ)} (hU : IsOpen U) : IsOpen (zSet T W₁ W₂ U) := by
  have e : zSet T W₁ W₂ U =
      ⋃ t : T, ⋃ X : nilrad W₁ W₂, (fun g => ((t : GL (Fin n) ℂ) * uOf X)⁻¹ * g) ⁻¹' U := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, X, c, hc, rfl⟩
      exact ⟨⟨t, ht⟩, X, by rwa [inv_mul_cancel_left]⟩
    · rintro ⟨t, X, hX⟩
      exact ⟨t, t.2, X, _, hX, mul_inv_cancel_left _ _⟩
  rw [e]
  exact isOpen_iUnion fun t => isOpen_iUnion fun X =>
    hU.preimage (continuous_const.mul continuous_id)

theorem mul_mem_zSet {T : Subgroup (GL (Fin n) ℂ)} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    {U : Set (GL (Fin n) ℂ)} {h : GL (Fin n) ℂ} (hh : h ∈ T) (x : GL (Fin n) ℂ) :
    h * x ∈ zSet T W₁ W₂ U ↔ x ∈ zSet T W₁ W₂ U := by
  constructor
  · rintro ⟨t, ht, X, c, hc, e⟩
    refine ⟨h⁻¹ * t, T.mul_mem (T.inv_mem hh) ht, X, c, hc, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_assoc t, e, inv_mul_cancel_left]
  · rintro ⟨t, ht, X, c, hc, rfl⟩
    exact ⟨h * t, T.mul_mem hh ht, X, c, hc, by simp only [mul_assoc]⟩

theorem exists_conj {T : Subgroup (GL (Fin n) ℂ)} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    (hconj : ∀ t ∈ T, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂)
    {t : GL (Fin n) ℂ} (ht : t ∈ T) (X : nilrad W₁ W₂) :
    ∃ X' : nilrad W₁ W₂, uOf X' = t * uOf X * t⁻¹ := by
  refine ⟨⟨t.val * X.1 * (t⁻¹ : GL (Fin n) ℂ).val, hconj t ht X.1 X.2⟩, Units.ext ?_⟩
  have h1 : t.val * (t⁻¹ : GL (Fin n) ℂ).val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem uOf_mul_mem_zSet {T : Subgroup (GL (Fin n) ℂ)} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    (hW : W₁ ≤ W₂)
    (hconj : ∀ t ∈ T, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂)
    (U : Set (GL (Fin n) ℂ)) (X : nilrad W₁ W₂) (x : GL (Fin n) ℂ) :
    uOf X * x ∈ zSet T W₁ W₂ U ↔ x ∈ zSet T W₁ W₂ U := by
  have fwd : ∀ (X : nilrad W₁ W₂) (x : GL (Fin n) ℂ), x ∈ zSet T W₁ W₂ U →
      uOf X * x ∈ zSet T W₁ W₂ U := by
    rintro X _ ⟨t, ht, Y, c, hc, rfl⟩
    obtain ⟨X', hX'⟩ := exists_conj hconj (T.inv_mem ht) X
    refine ⟨t, ht, nmul hW X' Y, c, hc, ?_⟩
    rw [uOf_nmul, hX', inv_inv]
    group
  refine ⟨fun h => ?_, fwd X x⟩
  have := fwd (ninv hW X) _ h
  rwa [uOf_ninv, inv_mul_cancel_left] at this

end GlobalTheory.CompanionTheory.LocVan.TNorm

namespace GlobalTheory.CompanionTheory.LocVan

open TNorm in

theorem tNormaliser : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ →
  (∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) →
  (∀ t ∈ twCent (thC n) d, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂) →
  (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤) →
  ∃ ρ : GL (Fin n) ℂ → ℝ≥0∞, IsQuotNormaliser (twCent (thC n) d) μd ρ ∧
    ∀ (X : nilrad W₁ W₂) (g : GL (Fin n) ℂ), ρ (uOf X * g) = ρ g := by
  intro n _ _ d μd _ W₁ W₂ hW hc hconj hfin
  haveI := secondCountable_GL n
  haveI := locallyCompact_GL n
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SFinite μd := by
    haveI := sigmaFinite_twCent d μd
    infer_instance
  obtain ⟨U, hUo, hUc, hUcov⟩ := exists_open_cover n
  have hact : Measurable fun p : twCent (thC n) d × GL (Fin n) ℂ =>
      (p.1 : GL (Fin n) ℂ) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  have hr : ∀ h₀ : twCent (thC n) d,
      MeasurePreserving (fun t : twCent (thC n) d => t * h₀) μd μd := by
    intro h₀
    have e : (fun t : twCent (thC n) d => t * h₀) = fun t => h₀ * t :=
      funext fun t => Subtype.ext (hc t t.2 h₀ h₀.2)
    rw [e]
    exact measurePreserving_mul_left μd h₀
  obtain ⟨ρ, hρm, hρ1, hρS⟩ := GlobalTheory.T.integral_fiber_decomposition_invariant μd
    (fun (t : twCent (thC n) d) (x : GL (Fin n) ℂ) => (t : GL (Fin n) ℂ) * x) hact
    (fun t₀ t => t * t₀) hr
    (fun h₀ h x => by simp only [Subgroup.coe_mul, mul_assoc])
    (fun i => nSet W₁ W₂ (closure (U i))) (fun i => zSet (twCent (thC n) d) W₁ W₂ (U i))
    (fun i => measurableSet_nSet W₁ W₂ (hUc i))
    (fun i => (isOpen_zSet _ W₁ W₂ (hUo i)).measurableSet)
    (fun i h x => mul_mem_zSet h.2 x)
    (fun x => by
      obtain ⟨i, hi⟩ := hUcov x
      exact ⟨i, 1, one_mem _, 0, x, hi, by simp [uOf_zero']⟩)
    (fun i x => hfin _ (hUc i) x)
    (fun i x hx => by
      obtain ⟨t₀, ht₀, X, c, hcU, rfl⟩ := hx
      have hopen : IsOpen {t : twCent (thC n) d |
          (t : GL (Fin n) ℂ) * (t₀ * uOf X * c) ∈ nSet W₁ W₂ (U i)} :=
        (isOpen_nSet W₁ W₂ (hUo i)).preimage (continuous_subtype_val.mul continuous_const)
      have hne : {t : twCent (thC n) d |
          (t : GL (Fin n) ℂ) * (t₀ * uOf X * c) ∈ nSet W₁ W₂ (U i)}.Nonempty :=
        ⟨⟨t₀⁻¹, inv_mem ht₀⟩, X, c, hcU, by simp [mul_assoc]⟩
      have hpos := hopen.measure_ne_zero μd hne
      intro h0
      exact hpos (measure_mono_null
        (fun t ht => nSet_mono W₁ W₂ subset_closure ht) h0))
    {s | ∃ X : nilrad W₁ W₂, s = fun g => uOf X * g}
    (by
      rintro _ ⟨X, rfl⟩ i x
      exact uOf_mul_mem_nSet hW _ X x)
    (by
      rintro _ ⟨X, rfl⟩ i x
      exact uOf_mul_mem_zSet hW hconj _ X x)
    (by
      rintro _ ⟨X, rfl⟩ h
      obtain ⟨X', hX'⟩ := exists_conj hconj h.2 X
      refine ⟨_, ⟨X', rfl⟩, fun x => ?_⟩
      simp only [hX']
      group)
  exact ⟨ρ, ⟨hρm, hρ1⟩, fun X g => hρS _ ⟨X, rfl⟩ g⟩

end GlobalTheory.CompanionTheory.LocVan
end
end

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_conj_twisted_centralizer : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ →
  (∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) →
  (∀ t ∈ twCent (thC n) d, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂) →
  (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤) →
  ∃ ρ : GL (Fin n) ℂ → ℝ≥0∞, IsQuotNormaliser (twCent (thC n) d) μd ρ ∧
    ∀ (X : nilrad W₁ W₂) (g : GL (Fin n) ℂ), ρ (uOf X * g) = ρ g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LocVan.tNormaliser
end

section
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

theorem exists_isCompact_uOf_subset {n : ℕ} (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (g : GL (Fin n) ℂ) {K : Set (GL (Fin n) ℂ)} (hK : IsCompact K) :
    ∃ C : Set (nilrad W₁ W₂), IsCompact C ∧ {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * g ∈ K} ⊆ C := by
  have hf : Continuous fun c : GL (Fin n) ℂ =>
      ((g * c⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1 :=
    (Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const
  have hK' := hK.image hf
  have hemb : Topology.IsClosedEmbedding
      (Subtype.val : nilrad W₁ W₂ → Matrix (Fin n) (Fin n) ℂ) :=
    (isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage hK', fun Y hY => ?_⟩
  refine ⟨(uOf Y)⁻¹ * g, hY, ?_⟩
  have : g * ((uOf Y)⁻¹ * g)⁻¹ = uOf Y := by group
  simp only [this, uOf_val, add_sub_cancel_left]

theorem isOpen_nSet {n : ℕ} (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {C : Set (GL (Fin n) ℂ)}
    (hC : IsOpen C) : IsOpen (nSet W₁ W₂ C) := by
  have : nSet W₁ W₂ C = ⋃ X : nilrad W₁ W₂, (fun g => (uOf X)⁻¹ * g) ⁻¹' C := by
    ext g
    simp only [nSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨X, c, hc, rfl⟩
      exact ⟨X, by simpa using hc⟩
    · rintro ⟨X, hX⟩
      exact ⟨X, _, hX, by simp⟩
  rw [this]
  exact isOpen_iUnion fun X => hC.preimage (continuous_const.mul continuous_id)

theorem inv_mul_mem_nSet_iff {n : ℕ} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    (C : Set (GL (Fin n) ℂ)) (h : nilrad W₁ W₂) (x : GL (Fin n) ℂ) :
    (uOf h)⁻¹ * x ∈ nSet W₁ W₂ C ↔ x ∈ nSet W₁ W₂ C := by
  constructor
  · rintro ⟨X, c, hc, e⟩
    refine ⟨nmul hW h X, c, hc, ?_⟩
    rw [uOf_nmul, mul_assoc, e]
    simp
  · rintro ⟨X, c, hc, rfl⟩
    refine ⟨nmul hW (ninv hW h) X, c, hc, ?_⟩
    rw [uOf_nmul, uOf_ninv, mul_assoc]

theorem exists_nilrad_normaliser : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure],
  (∀ Y : nilrad W₁ W₂, MeasurePreserving (nmul hW Y) ν ν) →
  ∃ w : GL (Fin n) ℂ → ℝ≥0∞, Measurable w ∧
    ∀ g : GL (Fin n) ℂ, ∫⁻ X, w ((uOf X)⁻¹ * g) ∂ν = 1 := by
  intro n _ _ W₁ W₂ hW _ _ ν _ hmp
  haveI := locallyCompact_nilrad W₁ W₂
  haveI := secondCountable_nilrad W₁ W₂
  haveI := secondCountable_GL n
  haveI := locallyCompact_GL n
  obtain ⟨U, hUo, hUc, hUcov⟩ := exists_open_cover n
  have hmeas : Measurable (fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => (uOf p.1)⁻¹ * p.2) :=
    (((continuous_uOf.comp continuous_fst).inv).mul continuous_snd).measurable
  obtain ⟨ρ, hρm, hρ, -⟩ := GlobalTheory.T.integral_fiber_decomposition_invariant ν (fun Y g => (uOf Y)⁻¹ * g) hmeas (nmul hW) hmp
    (fun h₀ h x => by simp only [uOf_nmul, _root_.mul_inv_rev, mul_assoc])
    (fun i => closure (U i)) (fun i => nSet W₁ W₂ (U i))
    (fun i => isClosed_closure.measurableSet)
    (fun i => (isOpen_nSet W₁ W₂ (hUo i)).measurableSet)
    (fun i h x => inv_mul_mem_nSet_iff hW (U i) h x)
    (fun x => by
      obtain ⟨i, hi⟩ := hUcov x
      exact ⟨i, 0, x, hi, by
        have : uOf (0 : nilrad W₁ W₂) = 1 := Units.ext (by simp)
        simp [this]⟩)
    (fun i x => by
      obtain ⟨C, hC, hsub⟩ := exists_isCompact_uOf_subset W₁ W₂ x (hUc i)
      exact ((measure_mono hsub).trans_lt hC.measure_lt_top).ne)
    (fun i x hx => by
      obtain ⟨Y₀, c, hc, rfl⟩ := hx
      have ho : IsOpen {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i} :=
        (hUo i).preimage ((continuous_uOf.inv).mul continuous_const)
      have hne : ({Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i}).Nonempty :=
        ⟨Y₀, by simpa using hc⟩
      have hpos := ho.measure_pos ν hne
      have hsub : {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i} ⊆
          {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ closure (U i)} :=
        fun Y hY => subset_closure hY
      exact (hpos.trans_le (measure_mono hsub)).ne')
    ∅ (by simp) (by simp) (by simp)
  exact ⟨ρ, hρm, hρ⟩

end GlobalTheory.CompanionTheory.LocVan
end

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_nilradical_integral_one : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure],
  (∀ Y : nilrad W₁ W₂, MeasurePreserving (nmul hW Y) ν ν) →
  ∃ w : GL (Fin n) ℂ → ℝ≥0∞, Measurable w ∧
    ∀ g : GL (Fin n) ℂ, ∫⁻ X, w ((uOf X)⁻¹ * g) ∂ν = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LocVan.exists_nilrad_normaliser
end

section
section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

theorem quotVanish : QuotVanish := by
  intro n _ _ μ _ d μd _ W₁ W₂ hsep hW0 hW hp1 hp2 F hF hFT _ hvan
  haveI := locallyCompact_GL n
  haveI := secondCountable_GL n
  haveI := sigmaFinite_twCent d μd
  obtain ⟨P, hdiag, hzero, himg⟩ := GlobalTheory.T.exists_basis_diagonal_twisted_centralizer n d W₁ W₂ hsep hW hp1 hp2
  have hc : ∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx⟩ := hdiag a ha
    obtain ⟨y, hy⟩ := hdiag b hb
    have e : (P⁻¹ * a * P) * (P⁻¹ * b * P) = (P⁻¹ * b * P) * (P⁻¹ * a * P) :=
      Units.ext (by
        rw [Units.val_mul (P⁻¹ * a * P), Units.val_mul (P⁻¹ * b * P), hx, hy, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_mul_diagonal]
        congr 1; funext i; exact mul_comm _ _)
    have e2 : P⁻¹ * (a * b) * P = P⁻¹ * (b * a) * P := by
      calc P⁻¹ * (a * b) * P = (P⁻¹ * a * P) * (P⁻¹ * b * P) := by group
        _ = (P⁻¹ * b * P) * (P⁻¹ * a * P) := e
        _ = P⁻¹ * (b * a) * P := by group
    exact mul_left_cancel (mul_right_cancel e2)
  haveI := invInvariant_twCent d μd hc
  have hnorm : ∀ t ∈ twCent (thC n) d, ∀ X ∈ nilrad W₁ W₂,
      t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂ := by
    intro t ht X hX
    have := conj_mem t hX
    rwa [(himg t ht).1, (himg t ht).2] at this
  obtain ⟨ρ, hρ, hρN⟩ := GlobalTheory.T.compact_conj_twisted_centralizer n d μd W₁ W₂ hW hc hnorm
    (GlobalTheory.T.conj_compact_of_diagonal_nilradical n d μd W₁ W₂ P hW hdiag hzero)
  rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hFT hρ]
  letI : MeasurableSpace (nilrad W₁ W₂) := borel _
  haveI : BorelSpace (nilrad W₁ W₂) := ⟨rfl⟩
  haveI := locallyCompact_nilrad W₁ W₂
  haveI := secondCountable_nilrad W₁ W₂
  let ν : Measure (nilrad W₁ W₂) := Measure.addHaar
  haveI : ν.IsAddHaarMeasure := by dsimp only [ν]; infer_instance
  obtain ⟨w, hwm, hw⟩ := GlobalTheory.T.exists_weight_nilradical_integral_one n W₁ W₂ hW ν (fun Y => GlobalTheory.T.nilradical_translation_measure_preserving n W₁ W₂ hW ν Y)
  exact GlobalTheory.T.integral_unfold_weighted_average μ ν uOf continuous_uOf.measurable w ρ F hwm hρ.1 hF hw hρN (fun q => hvan ν q)

end GlobalTheory.CompanionTheory.LocVan
end
end

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_vanishing : GlobalTheory.CompanionTheory.LocVan.QuotVanish := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LocVan.quotVanish
end

section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

theorem locVanish_of (hN : NilChange) (hQ : QuotVanish) : LocVanish := by
  intro n _ _ μ _ f u d μd _ W₁ W₂ hf hfc hV hsep hW1 hle h12 h21 hu hub huK huT huN
  have hTw : Continuous fun x : GL (Fin n) ℂ => twConj (thC n) x d :=
    (continuous_inv.mul continuous_const).mul continuous_thC
  refine hQ n μ d μd W₁ W₂ hsep hW1 hle h12 h21 _
    (((hf.comp hTw).measurable).mul hu) (fun t ht x => ?_) (fun x k hk => ?_) ?_
  · show f (twConj (thC n) (t * x) d) * u (t * x) = f (twConj (thC n) x d) * u x
    rw [twConj_mul_left _ _ ht, huT t ht]
  · show f (twConj (thC n) (x * k) d) * u (x * k) = f (twConj (thC n) x d) * u x
    have : twConj (thC n) (x * k) d = twConj (thC n) k (twConj (thC n) x d) := by
      simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [this, hV.1 k _ hk, huK x k hk]
  · intro _ _ ν _ q
    obtain ⟨Φ, hΦc, hΦ, hΦν⟩ := hN n d W₁ W₂ hsep hW1 hle h12 h21
    obtain ⟨c, hc⟩ := hΦν ν

    set g : nilrad W₁ W₂ → ℂ := fun Y => f (q⁻¹ * uOf Y * d * thC n q) with hg
    have hgc : Continuous g :=
      hf.comp (((continuous_const.mul continuous_uOf).mul continuous_const).mul continuous_const)
    have e1 : ∀ X : nilrad W₁ W₂,
        f (twConj (thC n) (uOf X * q) d) * u (uOf X * q) = u q * g (Φ X) := fun X => by
      have hm : (uOf X).val - 1 ∈ nilrad W₁ W₂ := by simpa using X.2
      rw [huN _ hm, mul_comm]
      congr 2
      simp only [hg, hΦ, twConj, map_mul, _root_.mul_inv_rev]
      group
    have e2 : ∫ X, g (Φ X) ∂ν = (c : ℝ) • ∫ Y, g Y ∂ν := by
      rw [← integral_map hΦc.measurable.aemeasurable hgc.aestronglyMeasurable, hc,
        integral_smul_measure]
      simp
    simp only [e1]
    rw [integral_const_mul, e2]
    suffices h : ∫ Y, g Y ∂ν = 0 by simp [h]

    letI : MeasurableSpace (nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) := borel _
    haveI : BorelSpace (nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) := ⟨rfl⟩
    have hcn := continuous_conjNil q W₁ W₂
    haveI : (ν.map (conjNil q W₁ W₂)).IsAddHaarMeasure :=
      (conjNil q W₁ W₂).isAddHaarMeasure_map ν hcn (continuous_conjNil_symm q W₁ W₂)
    have key := hV.2 (twConj (thC n) q d) (img q⁻¹ W₁) (img q⁻¹ W₂) (img_ne_bot _ hW1)
      (img_le_img _ hle) (by rw [perpD_twConj, h12]) (by rw [perpD_twConj, h21]) uOf
      (fun X => uOf_val X) (ν.map (conjNil q W₁ W₂))
    have hcont : Continuous fun Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) =>
        f (uOf Z * twConj (thC n) q d) := hf.comp (continuous_uOf.mul continuous_const)
    rw [integral_map hcn.measurable.aemeasurable hcont.aestronglyMeasurable] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    show f _ = f _
    rw [uOf_conjNil]
    congr 1
    simp only [twConj]
    group

theorem locVanish : LocVanish := locVanish_of GlobalTheory.T.nilradical_change_of_variables GlobalTheory.T.quotient_vanishing

end GlobalTheory.CompanionTheory.LocVan
end
end
