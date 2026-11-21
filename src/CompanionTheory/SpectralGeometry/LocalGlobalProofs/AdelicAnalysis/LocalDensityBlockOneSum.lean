import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import BuildAid.ForwardExisting
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresIntegralFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductIntegral
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductMeasurable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtension
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductPushforwardStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDensityStatement
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityUnique
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem exists_sqrt_near_unit : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ,
    ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧
      (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  classical
  intro R _ _ hR x
  obtain ⟨htr, -, -, -, -, -, hval, U, -, hq⟩ := hR

  let h : R ≃ₜ R :=
    { toFun := fun y => y * (x : R)
      invFun := fun y => y * ((x⁻¹ : Rˣ) : R)
      left_inv := fun y => by simp [mul_assoc]
      right_inv := fun y => by simp [mul_assoc]
      continuous_toFun := continuous_id.mul continuous_const
      continuous_invFun := continuous_id.mul continuous_const }
  let f : U → R := fun u => (((u : Rˣ) ^ 2 : Rˣ) : R) * (x : R)
  have hf : IsOpenEmbedding f :=
    h.isOpenEmbedding.comp (hval.comp hq)
  have hf1 : f 1 = (x : R) := by simp [f]
  let a : R → Rˣ := fun y => if y ∈ Set.range f then ((Function.invFun f y : U) : Rˣ) else 1
  have haf : ∀ u : U, a (f u) = (u : Rˣ) := by
    intro u
    have : Function.invFun f (f u) = u := Function.leftInverse_invFun hf.injective u
    simp only [a, Set.mem_range_self, if_true, this]
  refine ⟨Set.range f, a, hf.isOpen_range, ⟨1, hf1⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hf.continuousAt_iff]
    have : a ∘ f = fun u : U => (u : Rˣ) := funext haf
    rw [this]
    exact continuous_subtype_val.continuousAt
  · intro y hy
    simp only [a, if_neg hy]
  · rintro _ ⟨u, rfl⟩
    rw [haf]
    simp [f]
  · have := haf 1
    rw [hf1] at this
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_units_continuous_square_root : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ, ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧ (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.PiLocalization₂.exists_sqrt_near_unit
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem nnreal_eq_of_smul_haar {V : Type} [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {c e : ℝ≥0} (h : c • μ = e • μ) : c = e := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  have h1 : μ C ≠ ⊤ := hC.measure_lt_top.ne
  have h2 : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC0).ne'
  have h3 : (c : ℝ≥0∞) * μ C = (e : ℝ≥0∞) * μ C := by
    have h' : (c • μ) C = (e • μ) C := by rw [h]
    rwa [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul] at h'
  have h4 := (ENNReal.mul_left_inj h2 h1).1 h3
  exact_mod_cast h4

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def sclMat : R →* Matrix (Fin 1) (Fin 1) (R ⊗[F] E) where
  toFun u := Matrix.of fun _ _ => u ⊗ₜ[F] (1 : E)
  map_one' := by
    ext i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    rw [Matrix.one_apply_eq]
    rfl
  map_mul' u v := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    simp only [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem sclMat_apply (u : R) (i j : Fin 1) :
    sclMat (F := F) (E := E) R u i j = u ⊗ₜ[F] (1 : E) := rfl

def unitTens : Rˣ →* (R ⊗[F] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E).toMonoidHom

theorem unitTens_coe (u : Rˣ) :
    ((unitTens (F := F) (E := E) R u : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (u : R) ⊗ₜ[F] (1 : E) := rfl

theorem rmul_sclMat {M : ℕ} (X : Fin 1 → Fin M → R ⊗[F] E) (u : R) :
    rmul R X (sclMat (F := F) (E := E) R u) = scl (u ⊗ₜ[F] (1 : E)) X := by
  funext a i
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  simp only [rmul, scl, Fin.sum_univ_one, sclMat_apply]

theorem cT_sclMat_mul (σ : E →ₐ[F] E) (u s : R) :
    ((hermScal R σ (u ^ 2 * s) : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) (sclMat (F := F) (E := E) R u) *
        ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        sclMat (F := F) (E := E) R u := by
  ext i j
  have h1 : sigR R σ (u ⊗ₜ[F] (1 : E)) = u ⊗ₜ[F] (1 : E) := by simp [sigR]
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, sclMat_apply, h1]
  change (u ^ 2 * s) ⊗ₜ[F] (1 : E) = u ⊗ₜ[F] (1 : E) * s ⊗ₜ[F] (1 : E) * u ⊗ₜ[F] (1 : E)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  ring

end Alg

theorem fibre_scale_modulus_length_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J₁ : Matrix (Fin N) (Fin N) E), IsHermND σ J₁ → ∀ t : F, t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ : HermR R σ 1 → Measure (Fin 1 → Fin N → R ⊗[F] E), IsGramFib R σ J₁ 1 (coordW R b lam 1 N) (coordHerm R σ b lam 1) m₁ → ∃ κ₁ cm : Rˣ → ℝ≥0, Continuous κ₁ ∧ κ₁ 1 = 1 ∧ (∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) = κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))) ∧ Continuous cm ∧ (∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam) ∧ ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → cm 1 = c := by
  intro F E _ _ _ _ _ σ hCM N J₁ hJ t ht R _ _ _ _ _ hR d b lam hlam m₁ hm₁
  have hR0 := hR
  obtain ⟨i1, i2, i3, i4, -⟩ := hR0
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  obtain ⟨k1, k2, k3, k4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  haveI := hK
  obtain ⟨κ, hκc, -, hκ1, hκ⟩ :=
    GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hCM N J₁ hJ R hR 1 _ _ m₁ (hW 1 N) (hH 1) hm₁
  have hinc : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have h : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ => (1 : R ⊗[F] E)) continuous_id
        continuous_const
    refine h.congr fun r => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hcs : Continuous (sclMat (F := F) (E := E) R) :=
    continuous_pi fun _ => continuous_pi fun _ => hinc
  have hg : Continuous (Units.map (sclMat (F := F) (E := E) R)) := Continuous.units_map _ hcs
  have hu : Continuous (unitTens (F := F) (E := E) R) := Continuous.units_map _ hinc
  obtain ⟨χ, hχc, hχ⟩ := exists_continuous_modulus_of_continuous_action (R ⊗[F] E) (coordK R b lam)
    (R ⊗[F] E)ˣ
  let tU : (R ⊗[F] E)ˣ :=
    Units.map (inclR R : E →+* R ⊗[F] E).toMonoidHom
      (Units.mk0 (algebraMap F E t) ((map_ne_zero _).2 ht))
  have htU : (tU : R ⊗[F] E) = inclR R (algebraMap F E t) := rfl
  have hq : ∀ u : Rˣ, ((unitTens (F := F) (E := E) R u * tU : (R ⊗[F] E)ˣ) : R ⊗[F] E) =
      (u : R) ⊗ₜ[F] (algebraMap F E t) := by
    intro u
    rw [Units.val_mul, unitTens_coe, htU]
    change (u : R) ⊗ₜ[F] (1 : E) * (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨fun u => κ (Units.map (sclMat (F := F) (E := E) R) u),
    fun u => χ (unitTens (F := F) (E := E) R u * tU), hκc.comp hg, by simpa using hκ1, ?_,
    hχc.comp (hu.mul continuous_const), ?_, ?_⟩
  · intro u
    have h := hκ (Units.map (sclMat (F := F) (E := E) R) u) (hermScal R σ (algebraMap F R t))
      (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) (cT_sclMat_mul R σ (u : R) _)
    rw [h]
    congr 2
    funext X
    exact rmul_sclMat R X (u : R)
  · intro u
    have e : (fun y : R ⊗[F] E => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) =
        fun v => (unitTens (F := F) (E := E) R u * tU) • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, hq]
    rw [e]
    exact hχ _
  · intro c hc
    have e : (fun y : R ⊗[F] E => inclR R (algebraMap F E t) * y) = fun v => tU • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, htU]
    rw [e, hχ tU] at hc
    have := nnreal_eq_of_smul_haar (coordK R b lam) hc
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordK_map_mul_eq_smul_continuous_modulus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J₁ : Matrix (Fin N) (Fin N) E), IsHermND σ J₁ → ∀ t : F, t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ : HermR R σ 1 → Measure (Fin 1 → Fin N → R ⊗[F] E), IsGramFib R σ J₁ 1 (coordW R b lam 1 N) (coordHerm R σ b lam 1) m₁ → ∃ κ₁ cm : Rˣ → ℝ≥0, Continuous κ₁ ∧ κ₁ 1 = 1 ∧ (∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) = κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))) ∧ Continuous cm ∧ (∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam) ∧ ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → cm 1 = c := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_scale_modulus_length_one | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_scale_modulus_length_one | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_scale_modulus_length_one <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageValue

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem one_tmul_algebraMap (t : F) :
    (1 : R) ⊗ₜ[F] (algebraMap F E t) = (algebraMap F R t) ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

theorem corner_half_trace_eq_of_pure_tensor [CharZero F] (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) {x : R}
    (h : S 0 0 = x ⊗ₜ[F] (1 : E)) : s0 R S = x := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_eq_succ hfr
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfr
  have htr : Algebra.trace R (R ⊗[F] E) (x ⊗ₜ[F] (1 : E)) = 2 * x := by
    have h1 := Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) x
    rw [Algebra.TensorProduct.algebraMap_apply] at h1
    simpa [two_mul, two_nsmul] using h1
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    calc algebraMap F R (1 / 2) * 2 = algebraMap F R (1 / 2) * algebraMap F R 2 := by rw [map_ofNat]
      _ = algebraMap F R (1 / 2 * 2) := (map_mul _ _ _).symm
      _ = 1 := by rw [show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  unfold s0
  rw [h, htr, ← mul_assoc, h2, one_mul]

theorem vec_one_zero {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    vec ((1 : R) ⊗ₜ[F] (1 : E)) (0 : Fin n → R ⊗[F] E) X = consTup X := by
  rw [← Algebra.TensorProduct.one_def]
  rfl

end Alg

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (t : F) (a : R → Rˣ) {n : ℕ}

theorem corner_half_trace_block_one [CharZero F] (hfr : Module.finrank F E = 2) (T : Matrix (Fin n) (Fin n) E) :
    s0 R ((blockOne (algebraMap F E t) T).map (inclR (F := F) R)) = algebraMap F R t := by
  apply corner_half_trace_eq_of_pure_tensor R hfr
  rw [← one_tmul_algebraMap]
  rfl

theorem cvec_block (T : Matrix (Fin n) (Fin n) E) :
    cvec R t a ((blockOne (algebraMap F E t) T).map (inclR R)) = 0 := by
  funext j
  simp [cvec, blockOne]

theorem schurM_block (T : Matrix (Fin n) (Fin n) E) :
    schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) = T.map (inclR R) := by
  ext i j
  have hc := cvec_block R t a T
  simp only [schurM, hc, Pi.zero_apply, map_zero, zero_mul, sub_zero]
  simp [blockOne]

theorem schur_block (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) :
    schur R σ t a (hermOf R σ _ hT') = hermOf R σ T hT := by
  apply Subtype.ext
  have hm : schurM R σ t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
    show schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) ∈ HermR R σ n
    rw [schurM_block]
    exact map_mem_HermR R σ T hT
  rw [schur_coe R σ t a _ hm]
  exact schurM_block R σ t a T

theorem isUnit_det_map (T : Matrix (Fin n) (Fin n) E) (hdet : T.det ≠ 0) :
    IsUnit (T.map (inclR (F := F) R)).det := by
  have h := (IsUnit.mk0 _ hdet).map (inclR (F := F) R)
  rw [RingHom.map_det] at h
  exact h

end Main

theorem family_at_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ∧ fibS σ J t m₁ m' s B₀ a κ₁ cm (hermOf R σ _ hT') = cm 1 ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D T hT hdet hT'
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have hs0 : s0 R ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = algebraMap F R t :=
    corner_half_trace_block_one R t hfr T
  have hsch := schur_block R σ t a T hT hT'
  have hmem : hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
    refine ⟨by rw [hs0]; exact D.htB, ?_⟩
    rw [hsch]
    exact isUnit_det_map R T hdet
  refine ⟨hmem, ?_⟩
  have hc : cvec R t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = 0 := cvec_block R t a T
  unfold fibS
  rw [Set.indicator_of_mem hmem]
  simp only [hs0, D.ha1, hsch, hc, D.hκ1, one_mul, Units.val_one, vec_one_zero]

end GlobalTheory.CompanionTheory.SW.StageValue
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_at_block_one_eq_map_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ∧ fibS σ J t m₁ m' s B₀ a κ₁ cm (hermOf R σ _ hT') = cm 1 ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageValue.family_at_block | exact GlobalTheory.CompanionTheory.SW.StageValue.family_at_block | (intros; apply GlobalTheory.CompanionTheory.SW.StageValue.family_at_block <;> assumption)
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit

theorem det_eq_corner_mul {K : Type} [CommRing K] {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (w : K) (hw : S 0 0 * w = 1) :
    S.det = S 0 0 *
      (Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ).det := by
  let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
    { toFun := Sum.elim (fun _ => 0) Fin.succ
      invFun := fun i => Fin.cases (Sum.inl ()) Sum.inr i
      left_inv := by rintro (_ | j) <;> simp
      right_inv := by intro i; refine Fin.cases ?_ ?_ i <;> simp }
  have h1 : S.det = (S.submatrix e e).det := (Matrix.det_submatrix_equiv_self e S).symm
  let A : Matrix Unit Unit K := fun _ _ => S 0 0
  let B : Matrix Unit (Fin n) K := fun _ j => S 0 j.succ
  let C : Matrix (Fin n) Unit K := fun i _ => S i.succ 0
  let D : Matrix (Fin n) (Fin n) K := fun i j => S i.succ j.succ
  let Wm : Matrix Unit Unit K := fun _ _ => w
  have h2 : S.submatrix e e = Matrix.fromBlocks A B C D := by
    ext (_ | i) (_ | j) <;> rfl
  letI : Invertible A :=
    ⟨Wm, by ext i j; rw [Matrix.mul_apply]; simp [A, Wm]; rw [mul_comm]; exact hw,
      by ext i j; rw [Matrix.mul_apply]; simp [A, Wm, hw]⟩
  have hA : A.det = S 0 0 := by rw [Matrix.det_unique]
  have hD : D - C * ⅟A * B =
      Matrix.of fun i j : Fin n => S i.succ j.succ - S i.succ 0 * w * S 0 j.succ := by
    have hinv : ⅟A = Wm := rfl
    ext i j
    rw [hinv, Matrix.sub_apply, Matrix.mul_apply]
    simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.mul_apply, Matrix.of_apply]
    simp [C, B, D, Wm]
  rw [h1, h2, Matrix.det_fromBlocks₁₁, hA, hD]

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem half_trace_tmul (h2F : (2 : F) ≠ 0) (b : Module.Basis (Fin 2) F E) (r : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r := by
  have h : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b)]
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul, one_div, inv_mul_cancel₀ h2F, map_one]
  simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← mul_assoc, h2, one_mul]

theorem corner_mul_inv {t : F} (ht : t ≠ 0) (u : Rˣ) :
    (((u : R) ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E)) *
      ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * inclR R (algebraMap F E t) *
        (((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹))) = 1 := by
  have hi : inclR R (algebraMap F E t) = (1 : R) ⊗ₜ[F] (algebraMap F E t) := rfl
  have hE : algebraMap F E t⁻¹ * algebraMap F E t = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ht, map_one]
  have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  rw [hi, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, hE, mul_one, one_mul, one_mul]
  have e1 : (u : R) ^ 2 * algebraMap F R t * (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R)) =
      algebraMap F R t := by
    calc _ = ((u : R) * ((u⁻¹ : Rˣ) : R)) ^ 2 * algebraMap F R t := by ring
      _ = _ := by rw [hu]; ring
  rw [e1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def t,
    ← map_mul, mul_inv_cancel₀ ht, map_one]
  rfl

theorem isUnit_det_of_mem_Bset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S hS
  obtain ⟨-, -, -, -, hArt, hRed, -, -⟩ := D.hR
  obtain ⟨-, -, -, -, -, hfix, -⟩ := KAlg.algebra_tensor_invol F E σ D.hCM R
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b₂ : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfr
  have hsig : ∀ (p : R) (e : E), sigR R σ (p ⊗ₜ[F] e) = p ⊗ₜ[F] σ e := fun _ _ => rfl
  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E) := S.1 with hT
  have hH : ∀ i j, sigR R σ (T j i) = T i j := S.2
  obtain ⟨x, hx⟩ := hfix (T 0 0) (hH 0 0)
  have hs0 : s0 R T = x := by
    rw [s0, hx]; exact half_trace_tmul two_ne_zero b₂ x
  have hxB : x ∈ B₀ := by
    have h : s0 R T ∈ B₀ := hS.1
    rwa [hs0] at h
  set u : Rˣ := a x with hu
  set p : R ⊗[F] E := ((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹) with hp
  set τ : R ⊗[F] E := inclR R (algebraMap F E t) with hτ
  have hsp : sigR R σ p = p := by rw [hp, hsig, AlgHom.commutes]
  have hsτ : sigR R σ τ = τ := by
    show sigR R σ ((1 : R) ⊗ₜ[F] (algebraMap F E t)) = (1 : R) ⊗ₜ[F] (algebraMap F E t)
    rw [hsig, AlgHom.commutes]
  have hw : T 0 0 * (p * τ * p) = 1 := by
    rw [hx]
    have := corner_mul_inv (E := E) (R := R) D.ht u
    have hq : x = (u : R) ^ 2 * algebraMap F R t := D.hsq x hxB
    rwa [← hq] at this
  have hschur : ∀ i j, schurM R σ t a T i j = T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ := by
    intro i j
    have hc : ∀ k, cvec R t a T k = p * T 0 k.succ := by
      intro k; rw [cvec, hs0]
    simp only [schurM]
    rw [hc, hc, map_mul, hsp, hH]
    ring
  have hmem : schurM R σ t a T ∈ HermR R σ n := by
    intro i j
    rw [hschur, hschur, map_sub, map_mul, map_mul, map_mul, map_mul, hsp, hsτ, hH, hH, hH]
    ring
  have hdet := det_eq_corner_mul T _ hw
  have hU : IsUnit (T 0 0) := IsUnit.of_mul_eq_one _ hw
  have hsch : (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      Matrix.of fun i j : Fin n => T i.succ j.succ - T i.succ 0 * (p * τ * p) * T 0 j.succ := by
    rw [schur_coe R σ t a S hmem]
    ext i j
    exact hschur i j
  have h2 := hS.2
  rw [hsch] at h2
  rw [hdet]
  exact hU.mul h2

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_of_mem_Bset' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.PiLocalization₂.BsetUnit.isUnit_det_of_mem_Bset
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem measurable_vec {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) (c : Fin n → K) :
    Measurable (fun X : Fin n → Fin M → K => vec α c X) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
  induction i using Fin.cases with
  | zero => simpa [vec] using (measurable_const : Measurable fun _ : Fin n → Fin M → K =>
      (Fin.cons α (fun _ => 0) : Fin (M + 1) → K) k)
  | succ i =>
    induction k using Fin.cases with
    | zero => simpa [vec] using (measurable_const : Measurable fun _ : Fin n → Fin M → K => c i)
    | succ k =>
      have h : Measurable fun X : Fin n → Fin M → K => X i k :=
        (measurable_pi_apply k).comp (measurable_pi_apply i)
      simpa [vec] using h

theorem fibS_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibS σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ = 0 := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S
  by_cases hS : S ∈ Bset R σ t a B₀
  swap
  · simp [fibS, hS]
  obtain ⟨h1, h2, h3, h4, -⟩ := id D.hR
  have hk := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  have hH := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  obtain ⟨-, -, hscH, -, hbH, hactH⟩ := hH
  obtain ⟨-, -, hscK, hT2K, -, -, -, hbor, -, hgram⟩ := hk
  obtain ⟨hcont, -, -, hpres⟩ := hactH (n + 1)
  have hcoord := (GlobalTheory.T.gram_block_one_schur_coordinates F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).2
  have hker' := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  have hker₁ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, hlf', -, -, -, hfib'⟩ := hker'
  obtain ⟨-, hlf₁, -⟩ := hker₁
  haveI := hbor (n + 1) (M + 1)
  haveI := hbor n M
  haveI := hbor 1 (M + 1)
  haveI := hlf₁ (hermScal R σ (algebraMap F R t))
  haveI := hlf' (schur R σ t a S)
  let α : R ⊗[F] E := ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E)
  let c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) → (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)
  have hfm : Measurable f := by
    have := hcont.measurable.comp
      ((D.hs.comp measurable_fst).prodMk ((measurable_vec α c).comp measurable_snd))
    exact this
  have hcl : MeasurableSet ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))})ᶜ) :=
    ((isClosed_singleton.preimage (hgram (n + 1) (M + 1) (blockOne (algebraMap F E t) J))).measurableSet).compl
  have hae : ∀ᵐ p ∂((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))),
      gramR R σ (blockOne (algebraMap F E t) J) (f p) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) := by
    have h := (Measure.quasiMeasurePreserving_snd (μ := m₁ (hermScal R σ (algebraMap F R t)))
      (ν := m' (schur R σ t a S))).ae (hfib' (schur R σ t a S))
    filter_upwards [h] with p hp
    change gramR R σ (blockOne (algebraMap F E t) J)
      (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)) = _
    rw [hpres]
    exact hcoord S p.2 hS.1 hp
  have hsub : (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ ⊆
      (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))})ᶜ := by
    intro x hx hxS
    exact hx ⟨hxS, ⟨S, hS, (Set.mem_singleton_iff.1 hxS).symm⟩⟩
  refine measure_mono_null hsub ?_
  have hmap : (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f)
      ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))})ᶜ) = 0 := by
    rw [Measure.map_apply hfm hcl]
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro p hp hpS
    exact hp hpS
  unfold fibS
  rw [Set.indicator_of_mem hS, Measure.smul_apply]
  change _ • (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f) _ = 0
  rw [hmap, smul_zero]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_concentrated_on_fiber : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibS σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))))ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_support <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem integrable_map_prod_of_compact {A B W : Type} [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [T2Space A] [TopologicalSpace B] [MeasurableSpace B]
    [OpensMeasurableSpace B] [T2Space B] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν] (f : A × B → W) (hf : Measurable f) (φ : W → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (C₁ : Set A) (C₂ : Set B)
    (h₁ : IsCompact C₁) (h₂ : IsCompact C₂)
    (hs : ∀ᵐ y ∂μ, ∀ X, φ (f (y, X)) ≠ 0 → y ∈ C₁ ∧ X ∈ C₂) (k : ℝ≥0) :
    Integrable φ (k • (μ.prod ν).map f) ∧
      ∫ v, φ v ∂(k • (μ.prod ν).map f) = (k : ℝ) * ∫ y, ∫ X, φ (f (y, X)) ∂ν ∂μ := by
  obtain ⟨Bd, hBd⟩ := hφ.bounded_above_of_compact_support hc
  have hmeas : Measurable φ := hφ.measurable
  have hg : Measurable (φ ∘ f) := hmeas.comp hf
  have hPm : MeasurableSet (C₁ ×ˢ C₂) := h₁.measurableSet.prod h₂.measurableSet
  have hPfin : (μ.prod ν) (C₁ ×ˢ C₂) < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top h₁.measure_lt_top h₂.measure_lt_top
  have hae : ∀ᵐ p ∂(μ.prod ν), ‖(φ ∘ f) p‖ ≤ (C₁ ×ˢ C₂).indicator (fun _ => |Bd|) p := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs
    filter_upwards [h] with p hp
    by_cases h0 : φ (f p) = 0
    · simp only [Function.comp, h0, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
    · have hmem : p ∈ C₁ ×ˢ C₂ := hp p.2 h0
      rw [Set.indicator_of_mem hmem]
      exact (hBd _).trans (le_abs_self _)
  have hbound : Integrable ((C₁ ×ˢ C₂).indicator (fun _ => |Bd|)) (μ.prod ν) :=
    (integrable_indicator_iff hPm).2 (integrableOn_const hPfin.ne)
  have hI : Integrable (φ ∘ f) (μ.prod ν) := hbound.mono' hg.aestronglyMeasurable hae
  have hI2 : Integrable φ ((μ.prod ν).map f) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hf.aemeasurable).2 hI
  refine ⟨hI2.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, integral_map hf.aemeasurable hmeas.aestronglyMeasurable,
    integral_prod (fun p => φ (f p)) hI]
  simp [NNReal.smul_def]

theorem vec_zero {K : Type} [CommRing K] {M n : ℕ} (u : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    vec u c X 0 = u • (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → K) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [vec]

theorem continuous_vec {K : Type} [TopologicalSpace K] [Zero K] {M n : ℕ} (u : K) (c : Fin n → K) :
    Continuous (fun X : Fin n → Fin M → K => vec u c X) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun a' => ?_) a
  · simp only [vec, Fin.cons_zero]; exact continuous_const
  · refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [vec, Fin.cons_succ, Fin.cons_zero]; exact continuous_const
    · simp only [vec, Fin.cons_succ]
      exact continuous_apply_apply a' i'

theorem integrable_fibS_and_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S) ∧ ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = ((κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) * cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n : ℝ≥0) : ℝ) * Preal σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm hD φ hφ hcs S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := hD.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  obtain ⟨hKr, hKlc, hKsc, hKt2, -, -, -, hBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hD.hCM R
  have := hKr
  have := hKlc
  have := hKsc
  have := hKt2
  have hB1 : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := hBor 1 (M + 1)
  have hB2 : BorelSpace (Fin n → Fin M → R ⊗[F] E) := hBor n M
  have hB3 : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := hBor (n + 1) (M + 1)
  have hJ₁ := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J hD.hJ t hD.ht
  obtain ⟨hTG, -, hHsc, hHt2, hHB, hact⟩ :=
    GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hD.hCM (M + 1) (blockOne (algebraMap F E t) J) hJ₁ R
  have := hTG
  have := hHsc
  have := hHt2
  have := hHB
  obtain ⟨hcont, hone, hmul, -⟩ := hact (n + 1)
  have k1 := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hD.hCM (M + 1) 1 (blockOne (algebraMap F E t) J) hJ₁ R hD.hR d b lam
    hD.hlam m₁ hD.hm₁
  have k2 := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hD.hCM M n J hD.hJ R hD.hR d b lam hD.hlam m' hD.hm'
  obtain ⟨-, hlf₁, -, -, -, hgram⟩ := k1
  obtain ⟨-, hlf₂, -, -, -, -⟩ := k2
  set α : Rˣ := a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) with hα
  set c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) with hc
  set S' := schur R σ t a S with hS'
  set μ₁ := m₁ (hermScal R σ (algebraMap F R t)) with hμ₁
  set u : R ⊗[F] E := (α : R) ⊗ₜ[F] (1 : E) with hu
  set u' : R ⊗[F] E := ((α⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) with hu'
  have huu : u * u' = 1 := by
    simp [hu, hu', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
  have := hlf₁ (hermScal R σ (algebraMap F R t))
  have := hlf₂ S'
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) →
      Fin (n + 1) → Fin (M + 1) → R ⊗[F] E :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec u c p.2)
  have hfm : Measurable f :=
    hcont.measurable.comp ((hD.hs.comp measurable_fst).prodMk
      ((continuous_vec u c).measurable.comp measurable_snd))
  have hfib : fibS σ J t m₁ m' s B₀ a κ₁ cm S = (κ₁ α * cm α ^ n) • (μ₁.prod (m' S')).map f := by
    unfold fibS
    rw [Set.indicator_of_mem hS]
  set C := tsupport φ with hC
  have hCc : IsCompact C := hcs
  let e₁ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → Fin 1 → Fin (M + 1) → R ⊗[F] E :=
    fun Z _ i => Z 0 i * u'
  have he₁ : Continuous e₁ := by
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    exact (continuous_apply_apply (0 : Fin (n + 1)) i).mul continuous_const
  have hC₁ : IsCompact (e₁ '' C) := hCc.image he₁
  obtain ⟨C', hC'c, hC'⟩ := hD.hcpt (e₁ '' C) hC₁
  let e₂ : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) →
      Fin (n + 1) → Fin (M + 1) → R ⊗[F] E :=
    fun q => actW R σ (blockOne (algebraMap F E t) J) q.1⁻¹ q.2
  have he₂ : Continuous e₂ := hcont.comp ((continuous_fst.inv).prodMk continuous_snd)
  let e₃ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → Fin n → Fin M → R ⊗[F] E :=
    fun Z j i => Z j.succ i.succ
  have he₃ : Continuous e₃ := by
    refine continuous_pi fun j => continuous_pi fun i => ?_
    exact continuous_apply_apply j.succ i.succ
  have hC₂ : IsCompact (e₃ '' (e₂ '' (C' ×ˢ C))) := ((hC'c.prod hCc).image he₂).image he₃
  have hsupp : ∀ᵐ y ∂μ₁, ∀ X, φ (f (y, X)) ≠ 0 → y ∈ e₁ '' C ∧ X ∈ e₃ '' (e₂ '' (C' ×ˢ C)) := by
    filter_upwards [hgram (hermScal R σ (algebraMap F R t))] with y hy X hne
    have hZ : f (y, X) ∈ C := subset_tsupport _ hne
    have hy0 : e₁ (f (y, X)) = y := by
      have h1 := hD.hsec y hy
      funext i j
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have h2 : (f (y, X)) 0 = u • y 0 := by
        conv_rhs => rw [← h1]
        simp only [f, actW, actTup, vec_zero, Matrix.mulVec_smul]
      simp only [e₁, h2, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm u, mul_assoc, huu, mul_one]
    have hy1 : y ∈ e₁ '' C := ⟨_, hZ, hy0⟩
    have hsy : s y ∈ C' := hC' y hy1 hy
    have hv : e₂ (s y, f (y, X)) = vec u c X := by
      simp only [e₂, f]
      rw [← hmul, inv_mul_cancel, hone]
    refine ⟨hy1, vec u c X, ⟨(s y, f (y, X)), ⟨hsy, hZ⟩, hv⟩, ?_⟩
    funext j i
    simp [e₃, vec]
  rw [hfib]
  exact integrable_map_prod_of_compact μ₁ (m' S') f hfm φ hφ hcs _ _ hC₁ hC₂ hsupp _

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_integrable_and_integral_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S) ∧ ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = ((κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) * cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n : ℝ≥0) : ℝ) * Preal σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.integrable_fibS_and_integral | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.integrable_fibS_and_integral | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.integrable_fibS_and_integral <;> assumption)
end

section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_family_integral_isContDensityOn : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → ∀ φ : V → ℂ, Continuous φ → HasCompactSupport φ → HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B φ (fun b => ∫ v, φ v ∂(fib b)) ∧ ∀ b, Integrable φ (fib b) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral | exact GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral | (intros; apply GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral <;> assumption)
end

section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreJointCont

theorem continuousOn_integral_of_bounded {V X P : Type}
    [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace P]
    (fib : X → Measure V) (B : Set X) (hB : IsOpen B)
    (hloc : ∀ b, IsLocallyFiniteMeasure (fib b))
    (hbd : ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B →
      ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c)
    (hcont : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ →
      ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) B)
    (W : Set P) (Φ : P → V → ℝ)
    (hΦ : ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ)) (hW : IsOpen W)
    (C : Set V) (hC : IsCompact C) (hsupp : ∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) :
    ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by

  have hAt : ∀ p ∈ W, ∀ v, ContinuousAt (fun p : P × V => Φ p.1 p.2) (p, v) := fun p hp v =>
    hΦ.continuousAt ((hW.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ v⟩)
  have hslice : ∀ p ∈ W, Continuous (Φ p) := fun p hp =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (f := fun v : V => (p, v)) (g := fun p : P × V => Φ p.1 p.2)
        (hAt p hp v) (by fun_prop)
  have hcs : ∀ p ∈ W, HasCompactSupport (Φ p) := fun p hp =>
    HasCompactSupport.intro hC (hsupp p hp)
  have hint : ∀ p ∈ W, ∀ b, Integrable (Φ p) (fib b) := fun p hp b => by
    haveI := hloc b
    exact (hslice p hp).integrable_of_hasCompactSupport (hcs p hp)
  rintro ⟨p₀, b₀⟩ ⟨hp₀, hb₀⟩
  simp only [Set.mem_prod] at hp₀ hb₀ ⊢
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨D, hDn, hDB, hDc⟩ := local_compact_nhds (hB.mem_nhds hb₀)
  obtain ⟨c, hc⟩ := hbd C D hC hDc hDB
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set δ : ℝ := ε / (2 * ((c : ℝ) + 1)) with hδ
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hδ0 : 0 < δ := by positivity

  have htube : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ := by
    refine hC.eventually_forall_of_forall_eventually fun v _ => ?_
    have h1 : ContinuousAt (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (p₀, v) :=
      (hAt p₀ hp₀ v).sub
        (ContinuousAt.comp (f := fun z : P × V => z.2) (g := Φ p₀)
          (hslice p₀ hp₀).continuousAt continuousAt_snd)
    have h2 : Filter.Tendsto (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (𝓝 (p₀, v)) (𝓝 0) := by
      have h3 := h1.tendsto
      simp only [sub_self] at h3
      exact h3
    have h4 := (Metric.tendsto_nhds.1 h2) δ hδ0
    filter_upwards [h4] with z hz
    simpa [Real.dist_eq] using hz
  have hb : ∀ᶠ b in 𝓝 b₀,
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := by
    have h1 := ((hcont (Φ p₀) (hslice p₀ hp₀) (hcs p₀ hp₀)).continuousAt
      (hB.mem_nhds hb₀)).tendsto
    have h2 := (Metric.tendsto_nhds.1 h1) (ε / 2) (by positivity)
    filter_upwards [h2] with b hb
    simpa [Real.dist_eq] using hb
  rw [nhds_prod_eq]
  have hp : ∀ᶠ p in 𝓝 p₀, p ∈ W ∧ ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ :=
    Filter.Eventually.and (hW.mem_nhds hp₀) htube
  have hbb : ∀ᶠ b in 𝓝 b₀, b ∈ D ∧
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := Filter.Eventually.and hDn hb
  filter_upwards [hp.prod_mk hbb] with q hq
  obtain ⟨⟨hqW, hqt⟩, hqD, hqb⟩ := hq
  obtain ⟨p, b⟩ := q
  simp only at hqW hqt hqD hqb ⊢
  have hfin : fib b C < ∞ := (hc b hqD).trans_lt ENNReal.coe_lt_top
  have hdiff : ∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)
      = ∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b) := by
    rw [← integral_sub (hint p hqW b) (hint p₀ hp₀ b)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    rw [hsupp p hqW v hv, hsupp p₀ hp₀ v hv, sub_zero]
  have hreal : (fib b).real C ≤ c := by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top (hc b hqD)
    simpa [Measure.real] using this
  have hle : |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)| ≤ δ * (c : ℝ) := by
    rw [hdiff, ← Real.norm_eq_abs]
    have h5 : ‖∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b)‖ ≤ δ * (fib b).real C :=
      norm_setIntegral_le_of_norm_le_const (C := δ) hfin fun v hv => by
        rw [Real.norm_eq_abs]; exact (hqt v hv).le
    exact h5.trans (mul_le_mul_of_nonneg_left hreal hδ0.le)
  have hδc : δ * (c : ℝ) ≤ ε / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  calc |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)|
      = |(∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b))
          + (∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

theorem continuousOn_fibre_integral : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hfg B hB fib hF P _ W Φ hΦ hW C hC hsupp
  obtain ⟨hloc, -, -, hbd⟩ := GlobalTheory.T.fibre_family_locallyFinite_measurable_bdd_on_compact V X Y μ ν f g ι hι hg hfg B hB fib hF
  refine continuousOn_integral_of_bounded fib B hB hloc hbd ?_ W Φ hΦ hW C hC hsupp
  intro φ hφ hφc
  have h := (GlobalTheory.T.fibre_family_integral_isContDensityOn V X Y μ ν f g ι hι hg hfg B hB fib hF (fun v => (φ v : ℂ))
    (Complex.continuous_ofReal.comp hφ) (hφc.comp_left Complex.ofReal_zero)).1.1
  have h2 : ContinuousOn (fun b => Complex.re (∫ v, ((φ v : ℝ) : ℂ) ∂(fib b))) B :=
    Complex.continuous_re.comp_continuousOn h
  refine h2.congr fun b _ => ?_
  have := integral_ofReal (μ := fib b) (𝕜 := ℂ) (f := φ)
  simp only [Complex.coe_algebraMap] at this
  show ∫ v, φ v ∂(fib b) = (∫ v, ((φ v : ℝ) : ℂ) ∂(fib b)).re
  rw [this]
  simp

end GlobalTheory.CompanionTheory.SW.FibreJointCont
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

def tl {K : Type} {M n : ℕ} (Y : Fin (n + 1) → Fin (M + 1) → K) : Fin n → Fin M → K :=
  fun j i => Y j.succ i.succ

theorem tl_vec {K : Type} [Zero K] {M n : ℕ} (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    tl (vec α c X) = X := by
  funext j i
  simp [tl, vec]

theorem continuous_tl {K : Type} [TopologicalSpace K] {M n : ℕ} :
    Continuous (tl : (Fin (n + 1) → Fin (M + 1) → K) → Fin n → Fin M → K) := by
  refine continuous_pi fun j => continuous_pi fun i => ?_
  exact (continuous_apply i.succ).comp (continuous_apply j.succ)

theorem continuous_vec {K : Type} [Zero K] [TopologicalSpace K] {M n : ℕ} :
    Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => vec p.1 p.2.1 p.2.2) := by
  refine continuous_pi fun a => ?_
  refine Fin.cases ?_ (fun j => ?_) a
  · refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa [vec] using continuous_fst
    · simpa [vec] using continuous_const
  · refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · have h : Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => p.2.1 j) :=
        (continuous_apply j).comp (continuous_fst.comp continuous_snd)
      simpa [vec] using h
    · have h : Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => p.2.2 j k) :=
        (continuous_apply k).comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd))
      simpa [vec] using h

theorem actW_vec_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {N n : ℕ}
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (J' : Matrix (Fin (N + 1)) (Fin (N + 1)) E)
    (h : HA R σ J') (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E) (X : Fin n → Fin N → R ⊗[F] E) (i : Fin (N + 1)) :
    actW R σ J' h (vec A c X) 0 i =
      actW R σ J' h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) 0 i * A := by
  have hv : (Fin.cons A (fun _ => 0) : Fin (N + 1) → R ⊗[F] E) = A • Fin.cons 1 (fun _ => 0) := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  simp only [actW, actTup, vec, Fin.cons_zero]
  rw [hv, Matrix.mulVec_smul]
  simp [mul_comm]

theorem continuous_tmul_one {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun α : R => α ⊗ₜ[F] (1 : E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have h : Continuous (fun α : R => α • (1 : R ⊗[F] E)) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  convert h using 2 with α
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem cont_double : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Unt σ R n)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  haveI iTR : IsTopologicalRing R := D.hR.1
  haveI iLC : LocallyCompactSpace R := D.hR.2.1
  haveI iSC : SecondCountableTopology R := D.hR.2.2.1
  haveI iT2 : T2Space R := D.hR.2.2.2.1
  have hval : IsOpenEmbedding (Units.val : Rˣ → R) := D.hR.2.2.2.2.2.2.1
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := kTR
  haveI := kLC
  haveI := kSC
  haveI := kT2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨eLC, eSC, eT2, eB, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  haveI := eLC
  haveI := eSC
  haveI := eT2
  haveI := eB
  obtain ⟨g, hgc, hg⟩ := hlift M J D.hJ
  obtain ⟨gTG, gLC, gSC, gT2, gB, hactall⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  haveI := gTG
  haveI := gLC
  haveI := gSC
  haveI := gT2
  haveI := gB
  obtain ⟨hact, hact1, hactm, -⟩ := hactall (n + 1)
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ D.hCM R d b lam D.hlam
  haveI := hW n M
  haveI := hH n
  obtain ⟨hUo, -, -, -, hbd', -⟩ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -, -, -, hgram₁⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := kB n M
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := kB 1 (M + 1)
  have hfam : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam n M) (gramR R σ J) Subtype.val
      (g ⁻¹' Unt σ R n) (coordHerm R σ b lam n) (Unt σ R n) m' := by
    have he : g ⁻¹' Unt σ R n = {X | IsUnit (gramR R σ J X).det} := by
      ext X
      simp only [Set.mem_preimage, Unt, Set.mem_setOf_eq, hg X]
    rw [he]
    exact D.hm'

  have hCt : ∀ L : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact L →
      ∃ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C ∧ ∀ h ∈ L, ∀ A c X,
        φ (actW R σ _ h (vec A c X)) ≠ 0 → X ∈ C := by
    intro L hL
    refine ⟨(fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      tl (actW R σ _ p.1⁻¹ p.2)) '' (L ×ˢ tsupport φ), ?_, ?_⟩
    · refine (hL.prod hφc).image ?_
      exact continuous_tl.comp (hact.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd))
    · intro h hh A c X hne
      refine ⟨(h, actW R σ _ h (vec A c X)), ⟨hh, subset_tsupport _ hne⟩, ?_⟩
      simp only
      rw [← hactm, inv_mul_cancel, hact1, tl_vec]
  have cT := continuous_tmul_one (F := F) (E := E) R

  let G : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) × HermR R σ n → ℝ :=
    fun q => ∫ X, φ (actW R σ _ q.1.1 (vec (q.1.2.1 ⊗ₜ[F] (1 : E)) q.1.2.2 X)) ∂(m' q.2)
  have hG : ∀ q, q.2 ∈ Unt σ R n → ContinuousAt G q := by
    intro q hq
    obtain ⟨L, hLc, hLn⟩ := exists_compact_mem_nhds q.1.1
    obtain ⟨C, hC, hCv⟩ := hCt L hLc
    have hWo : IsOpen (interior L ×ˢ (Set.univ : Set (R × (Fin n → R ⊗[F] E)))) :=
      isOpen_interior.prod isOpen_univ
    have hcΦ : Continuous (fun p : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) ×
        (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ _ p.1.1 (vec (p.1.2.1 ⊗ₜ[F] (1 : E)) p.1.2.2 p.2))) := by
      refine hφ.comp (hact.comp ((continuous_fst.comp continuous_fst).prodMk ?_))
      exact continuous_vec.comp ((cT.comp (continuous_fst.comp (continuous_snd.comp continuous_fst))).prodMk
        ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd))
    have hj := GlobalTheory.CompanionTheory.SW.FibreJointCont.continuousOn_fibre_integral (Fin n → Fin M → R ⊗[F] E) (HermR R σ n) _ (coordW R b lam n M)
      (coordHerm R σ b lam n) (gramR R σ J) g Subtype.val Subtype.val_injective hgc hg (Unt σ R n) hUo m' hfam
      (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E))
      (interior L ×ˢ Set.univ)
      (fun p X => φ (actW R σ _ p.1 (vec (p.2.1 ⊗ₜ[F] (1 : E)) p.2.2 X))) hcΦ.continuousOn hWo C hC
      (by
        intro p hp v hv
        by_contra hne
        exact hv (hCv p.1 (interior_subset hp.1) _ _ _ hne))
    have hmem : ((interior L ×ˢ Set.univ) ×ˢ Unt σ R n) ∈ 𝓝 q :=
      (hWo.prod hUo).mem_nhds ⟨⟨mem_interior_iff_mem_nhds.2 hLn, trivial⟩, hq⟩
    exact hj.continuousAt hmem
  rintro ⟨α₀, c₀, S₀⟩ ⟨hα₀, -, hS₀⟩
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨N, hNn, hNs, hNc⟩ := local_compact_nhds (hval.isOpen_range.mem_nhds hα₀)
  have hUc : IsCompact ((Units.val : Rˣ → R) ⁻¹' N) := by
    rw [hval.isInducing.isCompact_iff, Set.image_preimage_eq_of_subset hNs]
    exact hNc
  have hNi : IsCompact ((Units.val : Rˣ → R) '' ((Units.val : Rˣ → R) ⁻¹' N)⁻¹) :=
    hUc.inv.image Units.continuous_val
  obtain ⟨Dc, hDn, hDs, hDc⟩ := local_compact_nhds (hUo.mem_nhds hS₀)
  let C₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) :=
    (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      scl (p.1 ⊗ₜ[F] (1 : E)) (fun _ : Fin 1 => p.2 0)) ''
        (((Units.val : Rˣ → R) '' ((Units.val : Rˣ → R) ⁻¹' N)⁻¹) ×ˢ tsupport φ)
  have hC₁c : IsCompact C₁ := by
    refine (hNi.prod hφc).image ?_
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    have h1 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.2 0 i) :=
      (continuous_apply i).comp ((continuous_apply 0).comp continuous_snd)
    have h2 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.1 ⊗ₜ[F] (1 : E)) :=
      cT.comp continuous_fst
    exact h1.mul h2
  obtain ⟨C', hC'c, hC'⟩ := D.hcpt C₁ hC₁c
  obtain ⟨C₂, hC₂c, hC₂⟩ := hCt C' hC'c
  obtain ⟨cD, hcD⟩ := hbd' C₂ Dc hC₂c hDc hDs
  obtain ⟨Bd, hBd⟩ := hφ.bounded_above_of_compact_support hφc
  have hBd0 : 0 ≤ Bd := (norm_nonneg _).trans (hBd 0)
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have eU : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.2.2 ∈ Unt σ R n :=
    (continuous_snd.comp continuous_snd).continuousAt (hUo.mem_nhds hS₀)
  have eD : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.2.2 ∈ Dc :=
    (continuous_snd.comp continuous_snd).continuousAt hDn
  have eN : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.1 ∈ N :=
    continuous_fst.continuousAt hNn
  have hmeas : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
      AEStronglyMeasurable (fun y₀ => G ((s y₀, z.1, z.2.1), z.2.2))
        (m₁ (hermScal R σ (algebraMap F R t))) := by
    filter_upwards [eU] with z hz
    have hc : Continuous (fun h : HA R σ (blockOne (algebraMap F E t) J) => G ((h, z.1, z.2.1), z.2.2)) := by
      refine continuous_iff_continuousAt.2 fun h => ?_
      refine ContinuousAt.comp (g := G) (f := fun h => ((h, z.1, z.2.1), z.2.2)) (hG _ hz) ?_
      exact (((continuous_id.prodMk continuous_const)).prodMk continuous_const).continuousAt
    exact (hc.measurable.comp D.hs).aestronglyMeasurable
  have hcont : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      ContinuousAt (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => G ((s y₀, z.1, z.2.1), z.2.2))
        (α₀, c₀, S₀) := by
    refine Filter.Eventually.of_forall fun y₀ => ?_
    refine ContinuousAt.comp (g := G)
      (f := fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => ((s y₀, z.1, z.2.1), z.2.2)) (hG _ hS₀) ?_
    exact ((continuous_const.prodMk (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)).continuousAt
  have hbound : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
      ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
        ‖G ((s y₀, z.1, z.2.1), z.2.2)‖ ≤ C₁.indicator (fun _ => Bd * (cD : ℝ)) y₀ := by
    filter_upwards [eN, eD] with z hzN hzD
    filter_upwards [hgram₁ (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    obtain ⟨u, hu⟩ := hNs hzN
    have hsec := D.hsec y₀ hy₀
    have hvan : ∀ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ≠ 0 → y₀ ∈ C₁ := by
      intro X hne
      refine ⟨(((u⁻¹ : Rˣ) : R), actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)),
        ⟨⟨u⁻¹, ?_, rfl⟩, subset_tsupport _ hne⟩, ?_⟩
      · simpa [Set.mem_inv, hu] using hzN
      · funext a i
        have ha : a = 0 := Subsingleton.elim _ _
        subst ha
        simp only [scl]
        rw [actW_vec_zero, hsec, ← hu, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv,
          mul_one, ← Algebra.TensorProduct.one_def, mul_one]
    by_cases hy : y₀ ∈ C₁
    · have h2 : s y₀ ∈ C' := hC' y₀ hy hy₀
      have hvanX : ∀ X, X ∉ C₂ → φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) = 0 :=
        fun X hX => by_contra fun hne => hX (hC₂ _ h2 _ _ _ hne)
      rw [Set.indicator_of_mem hy]
      change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvanX]
      have hfin : m' z.2.2 C₂ < ∞ := (hcD _ hzD).trans_lt ENNReal.coe_lt_top
      refine (norm_setIntegral_le_of_norm_le_const hfin (fun X _ => hBd _)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hBd0
      have := ENNReal.toReal_mono ENNReal.coe_ne_top (hcD _ hzD)
      simpa [Measure.real] using this
    · rw [Set.indicator_of_notMem hy]
      have h0 : (fun X => φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X))) = 0 :=
        funext fun X => by_contra fun hne => hy (hvan X hne)
      change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
      rw [h0]
      simp
  have hint : Integrable (C₁.indicator (fun _ => Bd * (cD : ℝ)))
      (m₁ (hermScal R σ (algebraMap F R t))) :=
    (integrable_indicator_iff hC₁c.isClosed.measurableSet).2 (integrableOn_const hC₁c.measure_lt_top.ne)
  exact continuousAt_of_dominated hmeas hbound hint hcont

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_preal_units_of_hasCompactSupport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Unt σ R n)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo.cont_double | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo.cont_double | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo.cont_double <;> assumption)
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_integrable_continuousOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S)) ∧ ContinuousOn (fun S => ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)) (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  have h1 := GlobalTheory.T.gram_fiber_cons_integrable_and_integral_eq F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  have h2 := GlobalTheory.T.continuousOn_preal_units_of_hasCompactSupport F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  obtain ⟨-, ha, hc, hsch, -⟩ := GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  refine ⟨fun S hS => (h1 S hS).1, ?_⟩
  have hsub : (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ⊆
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := fun S hS => hS.1
  have ha' := ha.mono hsub
  have hval := Units.continuous_val.comp_continuousOn ha'
  have hmap := hval.prodMk ((hc.mono hsub).prodMk (hsch.mono hsub))
  have hP := h2.comp hmap (fun S hS => ⟨(a _).isUnit, Set.mem_univ _, hS.2⟩)
  have hk := NNReal.continuous_coe.comp_continuousOn
    ((D.hκc.comp_continuousOn ha').mul ((D.hcmc.comp_continuousOn ha').pow n))
  exact (hk.mul hP).congr (fun S hS => (h1 S hS).2)
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_integrable_and_continuousOn_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S)) ∧ ContinuousOn (fun S => ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)) (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_integrable_continuousOn
end

section
section
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem fibre_family_near_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J), Measurable s → (∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y) → (∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C') → ∃ B : Set (HermR R σ (n + 1)), IsOpen B ∧ hermOf R σ _ hT' ∈ B ∧ (∀ S ∈ B, IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1)) (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B)) (coordHerm R σ b lam (n + 1)) B fib ∧ fib (hermOf R σ _ hT') = c ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hdet hT' R _ _ _ _ _ hR d b lam hlam m₁ m' hm₁ hm' c hc s hs hsec hcpt
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J hJ t ht
  obtain ⟨tu, htu⟩ : IsUnit (algebraMap F R t) := (isUnit_iff_ne_zero.mpr ht).map (algebraMap F R)
  obtain ⟨B₀, a, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.local_units_continuous_square_root R hR tu
  rw [htu] at h2 h5 h6
  obtain ⟨κ₁, cm, k1, k2, k3, k4, k5, k6⟩ := GlobalTheory.T.coordK_map_mul_eq_smul_continuous_modulus F E σ hCM (M + 1) _ hJ' t ht R hR d b lam hlam m₁ hm₁
  have D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm :=
    { hCM := hCM, hJ := hJ, ht := ht, hR := hR, hlam := hlam, hm₁ := hm₁, hm' := hm', hs := hs, hsec := hsec,
      hcpt := hcpt, hB₀ := h1, htB := h2, hac := h3, hoff := h4, hsq := h5, ha1 := h6, hκc := k1, hκ1 := k2,
      hscale := k3, hcmc := k4, hmod := k5 }
  have V := GlobalTheory.T.gram_fiber_cons_at_block_one_eq_map_prod F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D T hT hdet hT'
  refine ⟨Bset R σ t a B₀, (GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D).2.2.2.2, V.1,
    GlobalTheory.T.isUnit_det_of_mem_Bset' F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D, fibS σ J t m₁ m' s B₀ a κ₁ cm,
    ⟨GlobalTheory.T.gram_fiber_cons_concentrated_on_fiber F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D, ?_, ?_⟩, ?_⟩
  · intro φ hφ
    exact (GlobalTheory.T.setLIntegral_Uset_coordW_eq_Mid F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ).trans
      (GlobalTheory.T.gram_fiber_cons_iterated_lintegral_eq_Mid F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ).symm
  · intro φ hc hs' _
    exact GlobalTheory.T.gram_fiber_cons_integrable_and_continuousOn_integral F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hc hs'
  · rw [V.2, k6 c hc]

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibre_family_block_one_eq_map_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J), Measurable s → (∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y) → (∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C') → ∃ B : Set (HermR R σ (n + 1)), IsOpen B ∧ hermOf R σ _ hT' ∈ B ∧ (∀ S ∈ B, IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1)) (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B)) (coordHerm R σ b lam (n + 1)) B fib ∧ fib (hermOf R σ _ hT') = c ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_family_near_block
end
