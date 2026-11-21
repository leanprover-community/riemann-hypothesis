import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHilbertSchmidtNormSqBesselAmplitudeLe
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheoremStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChartStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityUnitaryGroupProbabilityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselDoubleCosetMeasureBigCellEq
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSides
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHypsStatement

section
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.ProdHaarS

theorem isHaarOn_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN →
    IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨-, -, h, -⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  exact h

end GlobalTheory.SgInf.ProdHaarS
end

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHaarOn_besselSubgroup_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN → IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  atlas_forward_decl GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map
end

section
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AdDens

theorem det_adjoint' {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A : V →ₗ[ℝ] V) : LinearMap.det (LinearMap.adjoint A) = LinearMap.det A := by
  classical
  let b := stdOrthonormalBasis ℝ V
  rw [← LinearMap.det_toMatrix b.toBasis A, ← LinearMap.det_toMatrix b.toBasis (LinearMap.adjoint A),
    LinearMap.toMatrix_adjoint b b A, Matrix.det_conjTranspose, star_trivial]

theorem volume_image_eq {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (L : V ≃ₗ[ℝ] W) (σ : V →ₗ[ℝ] V) (τ : W →ₗ[ℝ] W) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (h : ∀ x y, ⟪τ (L x), L y⟫_ℝ = ⟪σ x, y⟫_ℝ) (s : Set V) : volume (L '' s) = volume s := by
  classical
  have hfin : Module.finrank ℝ V = Module.finrank ℝ W := L.finrank_eq
  let e : V ≃ₗᵢ[ℝ] W := (stdOrthonormalBasis ℝ V).equiv (stdOrthonormalBasis ℝ W) (finCongr hfin)
  let M : V →ₗ[ℝ] V := e.symm.toLinearEquiv.toLinearMap ∘ₗ L.toLinearMap
  let T : V →ₗ[ℝ] V := e.symm.toLinearEquiv.toLinearMap ∘ₗ τ ∘ₗ e.toLinearEquiv.toLinearMap
  have hM : ∀ x, e (M x) = L x := fun x => by simp [M]
  have hT : ∀ x, e (T x) = τ (e x) := fun x => by simp [T]

  have key : LinearMap.adjoint M ∘ₗ T ∘ₗ M = σ := by
    refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.comp_apply,
      ← LinearIsometryEquiv.inner_map_map e, hT, hM, hM, h]
  have hsq : ∀ f : V →ₗ[ℝ] V, (∀ x, f (f x) = x) → LinearMap.det f ^ 2 = 1 := by
    intro f hf
    have : f ∘ₗ f = LinearMap.id := LinearMap.ext hf
    rw [sq, ← LinearMap.det_comp, this, LinearMap.det_id]
  have hT2 : ∀ x, T (T x) = x := fun x => e.injective (by rw [hT, hT, hτ])
  have hdet : |LinearMap.det M| = 1 := by
    have h1 := congrArg LinearMap.det key
    rw [LinearMap.det_comp, LinearMap.det_comp, det_adjoint'] at h1
    have h4 : |LinearMap.det M| ^ 4 = 1 := by
      have hs := hsq σ hσ
      have ht := hsq T hT2
      rw [← h1] at hs
      rw [pow_abs, abs_eq_self.mpr (by positivity)]
      nlinarith [hs, ht]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by norm_num)).mp h4
  have himg : L '' s = e '' (M '' s) := by
    rw [Set.image_image]; exact Set.image_congr fun x _ => (hM x).symm
  rw [himg, LinearIsometryEquiv.image_eq_preimage_symm,
    e.symm.measurePreserving.measure_preimage_emb e.symm.toHomeomorph.measurableEmbedding,
    MeasureTheory.Measure.addHaar_image_linearMap, hdet, ENNReal.ofReal_one, one_mul]

abbrev EE (m : ℕ) := EuclideanSpace ℝ (Fin m × Fin m × Bool)

def rl (m : ℕ) : Matrix (Fin m) (Fin m) ℂ ≃ₗ[ℝ] EE m where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  invFun := unrealify
  map_add' X Y := by
    ext ⟨i, j, b⟩; cases b <;> simp [realifyFun]
  map_smul' t X := by
    ext ⟨i, j, b⟩; cases b <;> simp [realifyFun]
  left_inv X := by
    ext i j; apply Complex.ext <;> simp [realifyFun, unrealify]
  right_inv x := by
    ext ⟨i, j, b⟩; cases b <;> simp [realifyFun, unrealify]

theorem rl_symm {m : ℕ} (x : EE m) : (rl m).symm x = unrealify x := rfl

theorem inner_rl {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℂ) : ⟪rl m X, rl m Y⟫_ℝ = (Matrix.trace (X * Yᴴ)).re := by
  simp only [rl, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply,
    Fintype.sum_prod_type, Fintype.sum_bool, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [realifyFun] <;> ring

def cj {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) : EE m →ₗ[ℝ] EE m where
  toFun x := rl m (A * unrealify x * B)
  map_add' x y := by rw [← rl_symm, ← rl_symm, ← rl_symm, map_add, Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' t x := by
    rw [← rl_symm, ← rl_symm, map_smul, Matrix.mul_smul, Matrix.smul_mul, map_smul]; rfl

theorem cj_apply {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (x : EE m) : cj A B x = rl m (A * unrealify x * B) := rfl

theorem unrealify_rl {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (rl m X) = X := by rw [← rl_symm]; exact (rl m).symm_apply_apply X

theorem rl_unrealify {m : ℕ} (x : EE m) : rl m (unrealify x) = x := by rw [← rl_symm]; exact (rl m).apply_symm_apply x

theorem cj_cj {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (h : A * B = 1) (x : EE m) : cj A B (cj B A x) = x := by
  rw [cj_apply, cj_apply, unrealify_rl,
    show A * (B * unrealify x * A) * B = (A * B) * unrealify x * (A * B) by simp only [Matrix.mul_assoc],
    h, Matrix.one_mul, Matrix.mul_one, rl_unrealify]

theorem mem_UH_conj {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : B * A = 1) (h : Bᴴ * H' * B = H)
    {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H') : A * g * B ∈ UH H := by
  change Bᴴ * H' * B = H at h
  change gᴴ * H' * g = H' at hg
  show (A * g * B)ᴴ * H * (A * g * B) = H
  rw [← h]
  calc (A * g * B)ᴴ * (Bᴴ * H' * B) * (A * g * B) = Bᴴ * (gᴴ * ((B * A)ᴴ * H' * (B * A)) * g) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Bᴴ * H' * B := by rw [hAB, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg]

theorem exp_cj {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (X : Matrix (Fin m) (Fin m) ℂ) :
    NormedSpace.exp (A * X * B) = A * NormedSpace.exp X * B := by
  have hB : B = A⁻¹ := (Matrix.inv_eq_right_inv hAB).symm
  subst hB
  exact Matrix.exp_conj A X ((Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse hAB))

theorem cj_mem {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    {x : EE m} (hx : x ∈ lieE (UH H')) : cj A B x ∈ lieE (UH H) := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hsub : (lieE (UH H')).map (cj A B) ≤ lieE (UH H) := by
    rw [lieE, Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨A * X * B, fun t => ?_, ?_⟩
    · have := mem_UH_conj hBA h (hX t)
      rwa [← exp_cj hAB, Matrix.mul_smul, Matrix.smul_mul] at this
    · change rl m (A * X * B) = cj A B (rl m X)
      rw [cj_apply, unrealify_rl]
  exact hsub (Submodule.mem_map_of_mem hx)

theorem isMatGroup_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) : PI.IsMatGroup (UH H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show IsClosed {g : Matrix (Fin N) (Fin N) ℂ | gᴴ * H * g = H}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · show (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * H * 1 = H
    rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · intro a ha b hb
    change aᴴ * H * a = H at ha
    change bᴴ * H * b = H at hb
    show (a * b)ᴴ * H * (a * b) = H
    calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [ha, hb]
  · intro a ha
    change aᴴ * H * a = H at ha
    have hl : (H * aᴴ * H) * a = 1 := by
      rw [show H * aᴴ * H * a = H * (aᴴ * H * a) by simp only [Matrix.mul_assoc], ha, hH]
    have hu : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hl
    have hr : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
    refine ⟨?_, hr⟩
    show (a⁻¹)ᴴ * H * a⁻¹ = H
    calc (a⁻¹)ᴴ * H * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha]
      _ = (a * a⁻¹)ᴴ * H * (a * a⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def cjM {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) : PI.MtM m ≃ₜ PI.MtM m where
  toFun x := Matrix.of.symm (A * Matrix.of x * B)
  invFun x := Matrix.of.symm (B * Matrix.of x * A)
  left_inv x := by
    show B * (A * Matrix.of x * B) * A = Matrix.of x
    calc _ = (B * A) * Matrix.of x * (B * A) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [mul_eq_one_comm.1 hAB]; simp
  right_inv x := by
    show A * (B * Matrix.of x * A) * B = Matrix.of x
    calc _ = (A * B) * Matrix.of x * (A * B) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hAB]; simp
  continuous_toFun := (continuous_const.matrix_mul (continuous_id (X := Matrix (Fin m) (Fin m) ℂ))).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul (continuous_id (X := Matrix (Fin m) (Fin m) ℂ))).matrix_mul continuous_const

theorem measurable_lmulQ {m : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) : Measurable (PI.lmulQ s) := by
  have hc : Continuous (PI.lmulQ s) := by
    unfold PI.lmulQ
    exact Continuous.matrix_mul continuous_const continuous_id
  exact hc.measurable

theorem haar_map {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') {μ : Measure (PI.MtM m)} (hμ : PI.IsHaarOnM (UH H') μ) :
    PI.IsHaarOnM (UH H) (μ.map (cjM hAB).toMeasurableEquiv) := by
  obtain ⟨hσ, hne, hnull, hinv⟩ := hμ
  set e := (cjM hAB).toMeasurableEquiv with he
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  refine ⟨e.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    apply hne
    have h1 := congrArg (fun ν => ν.map e.symm) h0
    simpa [Measure.map_map e.symm.measurable e.measurable] using h1
  · rw [e.map_apply]
    refine measure_mono_null ?_ hnull
    intro x hx
    exact fun hxm => hx (mem_UH_conj hBA h hxm)
  · intro s hs
    have hcomm : PI.lmulQ s ∘ e = e ∘ PI.lmulQ (B * s * A) := by
      funext x
      show s * (A * Matrix.of x * B) = A * (B * s * A * Matrix.of x) * B
      calc s * (A * Matrix.of x * B) = (A * B) * s * (A * Matrix.of x * B) := by rw [hAB, Matrix.one_mul]
        _ = A * (B * s * A * Matrix.of x) * B := by simp only [Matrix.mul_assoc]
    rw [Measure.map_map (measurable_lmulQ s) e.measurable, hcomm,
      ← Measure.map_map e.measurable (measurable_lmulQ _), hinv _ (mem_UH_conj hAB h' hs)]

def adL {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') : lieE (UH H) ≃ₗ[ℝ] lieE (UH H') :=
  LinearEquiv.ofLinear ((cj B A).restrict fun _ hx => cj_mem (mul_eq_one_comm.1 hAB) h' hx)
    ((cj A B).restrict fun _ hx => cj_mem hAB h hx)
    (by ext1 x; exact Subtype.ext (cj_cj (mul_eq_one_comm.1 hAB) _))
    (by ext1 x; exact Subtype.ext (cj_cj hAB _))

theorem adL_coe {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') (x : lieE (UH H)) : (adL hAB h h' x : EE m) = cj B A x := rfl

theorem volume_adL {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (hH' : H'ᴴ = H') (hH2' : H' * H' = 1) (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') (s : Set (lieE (UH H))) : volume (adL hAB h h' '' s) = volume s := by
  have hHH : Hᴴ * H * H = H := by rw [hH, Matrix.mul_assoc, hH2, Matrix.mul_one]
  have hHH' : H'ᴴ * H' * H' = H' := by rw [hH', Matrix.mul_assoc, hH2', Matrix.mul_one]
  let σ : lieE (UH H) →ₗ[ℝ] lieE (UH H) := (cj H H).restrict fun _ hx => cj_mem hH2 hHH hx
  let τ : lieE (UH H') →ₗ[ℝ] lieE (UH H') := (cj H' H').restrict fun _ hx => cj_mem hH2' hHH' hx
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB

  have k1 : H * (A * H' * Aᴴ) = 1 := by
    rw [← h]
    calc Bᴴ * H' * B * (A * H' * Aᴴ) = Bᴴ * (H' * ((B * A) * (H' * Aᴴ))) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBA, Matrix.one_mul, ← Matrix.mul_assoc H', hH2', Matrix.one_mul, ← Matrix.conjTranspose_mul,
          hAB, Matrix.conjTranspose_one]
  have k2 : A * H' * Aᴴ = H := by
    calc A * H' * Aᴴ = (H * H) * (A * H' * Aᴴ) := by rw [hH2, Matrix.one_mul]
      _ = H := by rw [Matrix.mul_assoc, k1, Matrix.mul_one]
  refine volume_image_eq (adL hAB h h') σ τ (fun x => Subtype.ext (cj_cj hH2 _))
    (fun x => Subtype.ext (cj_cj hH2' _)) (fun x y => ?_) s
  rw [Submodule.coe_inner, Submodule.coe_inner]
  simp only [σ, τ, LinearMap.restrict_coe_apply, LinearEquiv.coe_coe, adL_coe]
  simp only [cj_apply, unrealify_rl]
  rw [← rl_unrealify (y : EE m), inner_rl, inner_rl, unrealify_rl]
  congr 1
  set X := unrealify (x : EE m)
  set Y := unrealify (y : EE m)
  calc Matrix.trace (H' * (B * X * A) * H' * (B * Y * A)ᴴ)
      = Matrix.trace ((H' * B * X * (A * H' * Aᴴ) * Yᴴ) * Bᴴ) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (Bᴴ * (H' * B * X * (A * H' * Aᴴ) * Yᴴ)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Bᴴ * H' * B) * X * (A * H' * Aᴴ) * Yᴴ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (H * X * H * Yᴴ) := by rw [h, k2]

theorem strict_entry {m : ℕ} (V : Submodule ℝ (EE m)) (A B : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    ∃ D : V →L[ℝ] ℂ, HasStrictFDerivAt (fun x : V => (B * NormedSpace.exp (unrealify (x : EE m)) * A) i j) D 0 ∧
      ∀ v : V, D v = (B * unrealify (v : EE m) * A) i j := by
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let U : V →L[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    LinearMap.toContinuousLinearMap ((rl m).symm.toLinearMap ∘ₗ V.subtype)
  have hU : ∀ v : V, U v = unrealify (v : EE m) := fun v => rl_symm (v : EE m)
  let T : Matrix (Fin m) (Fin m) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => (B * M * A) i j
      map_add' := fun M M' => by simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
      map_smul' := fun t M => by simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, RingHom.id_apply] }
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ) (U 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  have hall := T.hasStrictFDerivAt.comp (0 : V) (hexp.comp (0 : V) U.hasStrictFDerivAt)
  refine ⟨T.comp ((1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ).comp U), ?_, fun v => ?_⟩
  · have hf : (fun x : V => (B * NormedSpace.exp (unrealify (x : EE m)) * A) i j) =
        T ∘ (NormedSpace.exp ∘ U) := by
      funext x
      simp only [Function.comp_apply, hU]
      rfl
    rw [hf]
    exact hall
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, hU]
    rfl

theorem dens_map {m : ℕ} {H H' A B : Matrix (Fin m) (Fin m) ℂ} (hH : Hᴴ = H) (hH2 : H * H = 1)
    (hH' : H'ᴴ = H') (hH2' : H' * H' = 1) (hAB : A * B = 1) (h : Bᴴ * H' * B = H)
    (h' : Aᴴ * H * A = H') {μ : Measure (PI.MtM m)} {c : ℝ≥0∞} (hμ : PI.IsHaarOnM (UH H') μ)
    (hd : HasDens (UH H') μ c) : HasDens (UH H) (μ.map (cjM hAB).toMeasurableEquiv) c := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  set e := (cjM hAB).toMeasurableEquiv with he
  let L : lieE (UH H) ≃L[ℝ] lieE (UH H') := (adL hAB h h').toContinuousLinearEquiv
  have hLie := (GlobalTheory.T.closed_matrix_subgroup_theorem m (UH H) (isMatGroup_UH H hH2)).1
  have hmain := GlobalTheory.T.tendsto_measure_image_ball_div_volume m (UH H') μ c (isMatGroup_UH H' hH2') hμ hd (lieE (UH H))
    (fun x => B * NormedSpace.exp (unrealify (x : EE m)) * A) L
    (by simp only [ZeroMemClass.coe_zero]; rw [show unrealify (0 : EE m) = 0 from
      (rl_symm (0 : EE m)).symm.trans (map_zero _), NormedSpace.exp_zero, Matrix.mul_one, hBA])
    (Filter.Eventually.of_forall fun x => by
      have hx := hLie x 1
      rw [Complex.ofReal_one, one_smul] at hx
      exact mem_UH_conj hAB h' hx)
    (fun i j => by
      obtain ⟨D, hD, hDv⟩ := strict_entry (lieE (UH H)) A B i j
      refine ⟨D, hD, fun v => ?_⟩
      rw [hDv]
      show (B * unrealify (v : EE m) * A) i j = unrealify ((adL hAB h h' v : lieE (UH H')) : EE m) i j
      rw [adL_coe, cj_apply, unrealify_rl])
  unfold GlobalTheory.Amp.HasDens
  refine hmain.congr fun ρ => ?_
  have hset : e ⁻¹' GlobalTheory.Amp.expSet (UH H) (Metric.ball 0 ρ) =
      (fun x : lieE (UH H) => Matrix.of.symm (B * NormedSpace.exp (unrealify (x : EE m)) * A)) '' Metric.ball 0 ρ := by
    ext x
    simp only [Set.mem_preimage, GlobalTheory.Amp.expSet, Set.mem_image]
    constructor
    · rintro ⟨X, hX, hx⟩
      refine ⟨X, hX, ?_⟩
      have hx' : NormedSpace.exp (unrealify (X : EE m)) = A * Matrix.of x * B := hx
      show B * NormedSpace.exp (unrealify (X : EE m)) * A = Matrix.of x
      rw [hx']
      calc B * (A * Matrix.of x * B) * A = (B * A) * Matrix.of x * (B * A) := by simp only [Matrix.mul_assoc]
        _ = Matrix.of x := by rw [hBA, Matrix.one_mul, Matrix.mul_one]
    · rintro ⟨X, hX, rfl⟩
      refine ⟨X, hX, ?_⟩
      show NormedSpace.exp (unrealify (X : EE m)) = A * (B * NormedSpace.exp (unrealify (X : EE m)) * A) * B
      calc NormedSpace.exp (unrealify (X : EE m)) = (A * B) * NormedSpace.exp (unrealify (X : EE m)) * (A * B) := by
            rw [hAB, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
  have hvol : volume (⇑L '' Metric.ball (0 : lieE (UH H)) ρ) = volume (Metric.ball (0 : lieE (UH H)) ρ) :=
    volume_adL hH hH2 hH' hH2' hAB h h' _
  rw [e.map_apply, hset, hvol]

theorem haar_dens_conj : ∀ (m : ℕ) (H H' P : Matrix (Fin m) (Fin m) ℂ), Hᴴ = H → H * H = 1 → H'ᴴ = H' → H' * H' = 1 → IsUnit P → Pᴴ * H' * P = H → ∀ (μ : Measure (PI.MtM m)) (c : ℝ≥0∞), PI.IsHaarOnM (UH H') μ → HasDens (UH H') μ c → PI.IsHaarOnM (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) ∧ HasDens (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) c := by
  intro m H H' P hH hH2 hH' hH2' hP hPH μ c hμ hd
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hAB : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have h' : (P⁻¹)ᴴ * H * P⁻¹ = H' := by
    rw [← hPH]
    calc (P⁻¹)ᴴ * (Pᴴ * H' * P) * P⁻¹ = (P * P⁻¹)ᴴ * H' * (P * P⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H' := by rw [hPP, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hf : (fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) = ⇑(cjM hAB).toMeasurableEquiv := rfl
  rw [hf]
  exact ⟨haar_map hAB hPH h' hμ, dens_map hH hH2 hH' hH2' hAB hPH h' hμ hd⟩

end GlobalTheory.AdDens
end
end

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_density_conj_unitaryHermitianGroups : ∀ (m : ℕ) (H H' P : Matrix (Fin m) (Fin m) ℂ), Hᴴ = H → H * H = 1 → H'ᴴ = H' → H' * H' = 1 → IsUnit P → Pᴴ * H' * P = H → ∀ (μ : Measure (PI.MtM m)) (c : ℝ≥0∞), PI.IsHaarOnM (UH H') μ → HasDens (UH H') μ c → PI.IsHaarOnM (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) ∧ HasDens (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) c := by
  atlas_forward_decl GlobalTheory.AdDens.haar_dens_conj
end

section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity : ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ (μ : Measure (Formalism.BasicNotions.UpqT P Q)) (c : ℝ≥0∞), μ.IsHaarMeasure → Formalism.BasicNotions.OmegaDensity μ c → PI.IsHaarOnM (UH (Formalism.REAL.Jm ε)) (μ.map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) ∧ HasDens (UH (Formalism.REAL.Jm ε)) (μ.map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) c := by
  first | exact @GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity | exact GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity | (intros; apply GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity <;> assumption)
end

section
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FdegDens

theorem volUn_pos (j : ℕ) : 0 < volUn j := by
  unfold volUn
  refine Finset.prod_pos fun i _ => ?_
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  exact div_pos (pow_pos h2π _) (by exact_mod_cast Nat.factorial_pos i)

theorem exists_sort {n : ℕ} (ε : Fin n → Bool) : ∃ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin n), p + q = n ∧
    (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false := by
  classical
  let A := {i : Fin n // ε i = true}
  let B := {i : Fin n // ¬ε i = true}
  let e : Fin (Fintype.card A) ⊕ Fin (Fintype.card B) ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin A).symm (Fintype.equivFin B).symm).trans
      (Equiv.sumCompl fun i => ε i = true)
  refine ⟨Fintype.card A, Fintype.card B, e, ?_, fun i => ?_, fun j => ?_⟩
  · simpa using Fintype.card_congr e
  · exact ((Fintype.equivFin A).symm i).2
  · show ε (((Fintype.equivFin B).symm j : B) : Fin n) = false
    simpa using ((Fintype.equivFin B).symm j).2

theorem measurable_reindex {n p q : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n) :
    Measurable fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) := by
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  have hmat : Continuous (Formalism.BasicNotions.UpqT.mat : Formalism.BasicNotions.UpqT p q → _) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous fun g : Formalism.BasicNotions.UpqT p q =>
      (Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) : PI.MtM n) :=
    hmat.matrix_reindex e e
  exact hc.measurable

theorem reindex_mem {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (g : Formalism.BasicNotions.UpqT p q) :
    Formalism.REAL.inUJ ε (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
  obtain ⟨g0, hg0⟩ := g
  have hg : ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Formalism.UG.Jpq p q *
      (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hg0
  show (Matrix.reindex e e ((g0 : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))ᴴ *
      Formalism.REAL.Jm ε * Matrix.reindex e e (g0 : GL (Fin p ⊕ Fin q) ℂ) = Formalism.REAL.Jm ε
  rw [GlobalTheory.OmegaFrobenius.jm_eq h1 h2, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem hasDens_unique {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c c' : ℝ≥0∞}
    (h : HasDens S μ c) (h' : HasDens S μ c') : c = c' := by
  unfold HasDens at h h'
  exact tendsto_nhds_unique h h'

theorem hasDens_smul {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ : Measure (Fin m → Fin m → ℂ)} {c : ℝ≥0∞}
    (h : HasDens S μ c) (t : NNReal) : HasDens S (t • μ) (t * c) := by
  unfold HasDens at h ⊢
  refine (ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top) (a := (t : ℝ≥0∞))).congr fun ρ => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]

theorem cd_dens {n p q : ℕ} (ε : Fin n → Bool) (e : Fin p ⊕ Fin q ≃ Fin n) (hpq : p + q = n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) (cd : Formalism.BasicNotions.CDHaar) :
    PI.IsHaarOnM (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) ∧
    HasDens (UH (Formalism.REAL.Jm ε))
      ((cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)))
      (ENNReal.ofReal (volUn n)⁻¹) := by
  subst hpq
  obtain ⟨c0, -, -, hc1, hc2⟩ := cd.trick p q
  have hK := GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity (p + q) (fun _ => true) (p + q) 0 (Equiv.sumEmpty _ _) (fun _ => rfl)
    (fun j => j.elim0) (cd.cd (p + q) 0) c0 (cd.haar _ _) hc2
  have hJ : Formalism.REAL.Jm (fun _ : Fin (p + q) => true) = 1 := by
    unfold Formalism.REAL.Jm
    simp
  rw [hJ] at hK
  have hprob : ((cd.cd (p + q) 0).map fun g => Matrix.of.symm (Matrix.reindex
      (Equiv.sumEmpty (Fin (p + q)) (Fin 0)) (Equiv.sumEmpty (Fin (p + q)) (Fin 0))
      (Formalism.BasicNotions.UpqT.mat g))) Set.univ = 1 := by
    rw [Measure.map_apply (measurable_reindex _) MeasurableSet.univ, Set.preimage_univ]
    haveI := cd.prob (p + q)
    exact measure_univ
  have hc0 : c0 = ENNReal.ofReal (volUn (p + q))⁻¹ :=
    hasDens_unique hK.2 (GlobalTheory.T.hasDensityAtIdentity_unitaryGroup_probability (p + q) _ hK.1 hprob)
  have hM := GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity (p + q) ε p q e h1 h2 (cd.cd p q) c0 (cd.haar p q) hc1
  rw [hc0] at hM
  exact hM

theorem umat_emb {n : ℕ} (ε : Fin n → Bool) :
    MeasurableEmbedding fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n) := by
  have h : Topology.IsClosedEmbedding (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM n)) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  exact h.measurableEmbedding

theorem conj_emb {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    MeasurableEmbedding fun x : PI.MtM n => (Matrix.of.symm (P⁻¹ * Matrix.of x * P) : PI.MtM n) := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hm : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      Measurable fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) := by
    intro A B
    have hx : Continuous fun x : PI.MtM n => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ) := continuous_id
    have hc : Continuous fun x : PI.MtM n => (Matrix.of.symm (A * Matrix.of x * B) : PI.MtM n) :=
      (continuous_const.matrix_mul hx).matrix_mul continuous_const
    exact hc.measurable
  let φ : PI.MtM n ≃ PI.MtM n :=
    { toFun := fun x => Matrix.of.symm (P⁻¹ * Matrix.of x * P)
      invFun := fun y => Matrix.of.symm (P * Matrix.of y * P⁻¹)
      left_inv := fun x => by
        show Matrix.of.symm (P * (P⁻¹ * Matrix.of x * P) * P⁻¹) = x
        simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, ← Matrix.mul_assoc P P⁻¹,
          Matrix.mul_nonsing_inv_cancel_left _ _ hu]
      right_inv := fun y => by
        show Matrix.of.symm (P⁻¹ * (P * Matrix.of y * P⁻¹) * P) = y
        simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hu] }
  exact (MeasurableEquiv.mk φ (hm _ _) (hm _ _)).measurableEmbedding

theorem schur_of_dens : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (cd : Formalism.BasicNotions.CDHaar) (sc : NNReal) (P : Mat k r) (d c : ℝ) (μG : Measure (Mt k r)), (∀ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin (2 * r + k + 1)), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A → ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) A = cd.cd p q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}) → IsCayley k r ε P → IsFdeg ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d → 0 < c → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → SchurH μG σ (d / (c * volUn (2 * r + k + 1))) := by
  intro k r H _ _ _ σ ε cd sc P d c μG hcomp hP hF hc hμG hdG
  obtain ⟨p, q, e, hpq, h1, h2⟩ := exists_sort ε
  have hU := umat_emb ε
  have hC := conj_emb P hP.1

  have hν : ((sc : ℝ≥0∞) • Formalism.REAL.muG ε).map (fun a : Formalism.REAL.UJ ε => (Matrix.of.symm (umat a) : PI.MtM (2 * r + k + 1))) =
      (cd.cd p q).map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) := by
    ext B hB
    rw [Measure.map_apply hU.measurable hB, Measure.map_apply (measurable_reindex e) hB,
      hcomp p q e h1 h2 _ (hU.measurable hB)]
    congr 1
    ext g
    constructor
    · rintro ⟨a, ha, hag⟩
      show Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)) ∈ B
      rw [← hag]
      exact ha
    · intro hg
      have hmem : Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) ∈ Set.range
          (fun a : Formalism.REAL.UJ ε => ((a : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
            Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
        rw [(Formalism.REAL.isClosedEmbeddingMatrix _ ε).2]
        exact reindex_mem ε e h1 h2 g
      obtain ⟨a, ha⟩ := hmem
      refine ⟨a, ?_, ha⟩
      show Matrix.of.symm (umat a) ∈ B
      rw [show umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g) from ha]
      exact hg
  have hcd := cd_dens ε e hpq h1 h2 cd
  rw [← hν] at hcd
  have hHk := Formalism.QuantumDeterminants.hpkFacts k r
  have hD := GlobalTheory.T.haar_density_conj_unitaryHermitianGroups (2 * r + k + 1) (Formalism.QuantumDeterminants.Hpk k r) (Formalism.REAL.Jm ε) P hHk.1 hHk.2.1
    (Formalism.REAL.Jm_conjTranspose ε) (Formalism.REAL.Jm_mul_self ε) hP.1 hP.2 _ _ hcd.1 hcd.2
  obtain ⟨t, -, httop, hμt⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _
    (GlobalTheory.AdDens.isMatGroup_UH _ hHk.2.1) hD.1).1 μG hμG
  have hdt : HasDens (GG k r) μG (t * ENNReal.ofReal (volUn (2 * r + k + 1))⁻¹) := by
    have h := hasDens_smul hD.2 t.toNNReal
    rwa [ENNReal.smul_def, ENNReal.coe_toNNReal httop.ne, ← hμt] at h
  have hV := volUn_pos (2 * r + k + 1)
  have htr : t.toReal = c * volUn (2 * r + k + 1) := by
    have h := congrArg ENNReal.toReal (hasDens_unique hdG hdt)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal (inv_nonneg.mpr hV.le)] at h
    rw [h, mul_assoc, inv_mul_cancel₀ hV.ne', mul_one]
  rw [Measure.map_map hC.measurable hU.measurable] at hμt
  have hemb := hC.comp hU
  obtain ⟨hd, hFd⟩ := hF
  refine ⟨div_pos hd (mul_pos hc hV), fun v w v' w' => ?_⟩
  obtain ⟨hI, hE⟩ := hFd v w v' w'
  rw [hμt]
  refine ⟨Integrable.smul_measure ?_ httop.ne, ?_⟩
  · rw [hemb.integrable_map_iff]
    exact hI
  rw [integral_smul_measure, hemb.integral_map]
  refine (congrArg (fun z : ℂ => t.toReal • z) hE).trans ?_
  rw [htr, Complex.real_smul]
  push_cast
  rw [div_div_eq_mul_div]
  ring

end GlobalTheory.FdegDens
end

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_schur_of_formalDegree_density : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (cd : Formalism.BasicNotions.CDHaar) (sc : NNReal) (P : Mat k r) (d c : ℝ) (μG : Measure (Mt k r)), (∀ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin (2 * r + k + 1)), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A → ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) A = cd.cd p q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}) → IsCayley k r ε P → IsFdeg ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d → 0 < c → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → SchurH μG σ (d / (c * volUn (2 * r + k + 1))) := by
  atlas_forward_decl GlobalTheory.FdegDens.schur_of_dens
end

section
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AmpMeas

theorem stronglyMeasurable_indicator_of_continuousOn {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {S : Set X}
    (hS : MeasurableSet S) {f : X → W} (hf : ContinuousOn f S) : StronglyMeasurable (S.indicator f) := by
  classical
  haveI : ProperSpace W := FiniteDimensional.proper ℂ W
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  have := hf.measurable_piecewise (g := fun _ => (0 : W)) continuousOn_const hS
  have h2 : S.indicator f = S.piecewise f fun _ => (0 : W) := by
    funext x; by_cases hx : x ∈ S <;> simp [hx]
  rw [h2]
  exact this.stronglyMeasurable

theorem continuous_hsNormSq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Continuous fun A : Wq →L[ℂ] Wp => hsNormSq A := by
  unfold hsNormSq hsInner
  refine Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => ?_)
  have : Continuous fun A : Wq →L[ℂ] Wp => A (stdOrthonormalBasis ℂ Wq i) :=
    (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  exact this.inner this

theorem measurable_hsNormSq_ampJ : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  intro k r Wp _ _ _ _ Wq _ _ _ μG c Φ Φ' hH hΦ hΦ'
  haveI : SigmaFinite μG := hH.1
  have hcl : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hcl' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := hcl
  set S : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ GG k r} with hSdef
  have hS : MeasurableSet S := hcl'.measurableSet
  have hmul : ∀ γ x : Mat k r, γ ∈ GG k r → x ∈ GG k r → γ * x ∈ GG k r := by
    intro γ x hγ hx
    have hs' : γᴴ * Hpk k r * γ = Hpk k r := hγ
    have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
    show (γ * x)ᴴ * Hpk k r * (γ * x) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * γᴴ * Hpk k r * (γ * x) = xᴴ * (γᴴ * Hpk k r * γ) * x := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hs', hx']
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  let F : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p =>
    (innerSL ℂ (Φ' (Matrix.of p.2))).smulRight (Φ (Matrix.of p.1 * Matrix.of p.2))
  have hcont : Continuous fun p : Wq × Wp => (innerSL ℂ p.1).smulRight p.2 := by
    have h1 : Continuous fun p : Wq × Wp => innerSL ℂ p.1 := (innerSL ℂ).continuous.comp continuous_fst
    exact ((ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂).comp (h1.prodMk continuous_snd)
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => Φ' (Matrix.of p.2)) (S ×ˢ S) :=
    hΦ'.comp (hof.comp continuous_snd).continuousOn fun p hp => hp.2
  have h2 : ContinuousOn (fun p : Mt k r × Mt k r => Φ (Matrix.of p.1 * Matrix.of p.2)) (S ×ˢ S) :=
    hΦ.comp ((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).continuousOn
      fun p hp => hmul _ _ hp.1 hp.2
  have hF : ContinuousOn F (S ×ˢ S) := hcont.comp_continuousOn (h1.prodMk h2)
  have hsm : StronglyMeasurable ((S ×ˢ S).indicator F) :=
    stronglyMeasurable_indicator_of_continuousOn (hS.prod hS) hF
  have hint : StronglyMeasurable fun γ => ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG :=
    hsm.integral_prod_right'
  have hm : Measurable fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) :=
    (continuous_hsNormSq.comp_stronglyMeasurable (hint.const_smul (c : ℂ)⁻¹)).measurable
  have hae : ∀ᵐ x ∂μG, x ∈ S := by rw [ae_iff]; exact hH.2.2.1
  have heq : (S.indicator fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) =
      S.indicator fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) := by
    refine Set.indicator_congr fun γ hγ => ?_
    unfold ampJ
    congr 2
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    have : (γ, x) ∈ S ×ˢ S := ⟨hγ, hx⟩
    simp only [Set.indicator_of_mem this, F]
  rw [heq]
  exact hm.indicator hS

end GlobalTheory.Amp.AmpMeas
end

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_hsNormSq_amplitude_besselUnitary : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  atlas_forward_decl GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ
end

section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp.SchurBound

theorem psi_eq_psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Formalism.QuantumDeterminants.psi k r z c = psiGen k r z (fun _ => c) := by
  funext g
  simp only [Formalism.QuantumDeterminants.psi, psiGen, Formalism.QuantumDeterminants.ell, ellA, Finset.mul_sum]

theorem volUn_pos (j : ℕ) : 0 < volUn j := by
  unfold volUn
  exact Finset.prod_pos fun i _ => div_pos (pow_pos (by positivity) _) (by exact_mod_cast Nat.factorial_pos i)

theorem bcWeight_nonneg (k r : ℕ) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) (pow_nonneg (sub_nonneg.mpr h) _)
  · exact le_rfl

theorem measurable_bcWeight (k r : ℕ) (T T' : ℝ) : Measurable (bcWeight k r T T') := by
  unfold bcWeight
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const (Complex.continuous_normSq.measurable.comp measurable_snd)
  · exact (by fun_prop : Continuous fun q : (Fin r → ℂ) × ℂ =>
      (∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Mdim k r a - 2))) * (Complex.normSq q.2 - T * T') ^ (k - 1)).measurable

open scoped Matrix.Norms.Elementwise in
theorem smooth_smul {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (a : ℂ) (v : H) (h : IsSmoothVec (k := k) (r := r) σ v) :
    IsSmoothVec (k := k) (r := r) σ (a • v) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hEq⟩ := h g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, fun g hg hgH => ?_⟩
  simp only [map_smul, hEq g hg hgH]

theorem DD_smul_le {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (a : ℂ) (v : H) : DD σ (a • v) ≤ DD σ v := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)

theorem lintegral_cell {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (w : X → ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (φ : X → Y) (S : Set Y) (F : Y → ℝ) (a : ℝ) (ha : 0 < a)
    (hφ : AEMeasurable φ (μ.withDensity fun x => ENNReal.ofReal (w x)))
    (hS : (ENNReal.ofReal a • (μ.withDensity fun x => ENNReal.ofReal (w x)).map φ) Sᶜ = 0)
    (hF : Measurable (S.indicator F)) :
    ∫⁻ y, ENNReal.ofReal (F y) ∂(ENNReal.ofReal a • (μ.withDensity fun x => ENNReal.ofReal (w x)).map φ) =
      ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal (w x * F (φ x)) ∂μ := by
  have ha' : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have hdm : Measurable fun x => ENNReal.ofReal (w x) := ENNReal.measurable_ofReal.comp hw
  have hg : Measurable fun y => ENNReal.ofReal (S.indicator F y) := ENNReal.measurable_ofReal.comp hF
  have h1 : ((μ.withDensity fun x => ENNReal.ofReal (w x)).map φ) Sᶜ = 0 := by
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hS
    exact hS.resolve_left ha'
  have h2 : ∀ᵐ y ∂((μ.withDensity fun x => ENNReal.ofReal (w x)).map φ), y ∈ S := by
    rw [ae_iff]
    exact h1
  have h3 : ∀ᵐ x ∂(μ.withDensity fun x => ENNReal.ofReal (w x)), φ x ∈ S := by
    rw [ae_iff]
    exact nonpos_iff_eq_zero.mp ((Measure.le_map_apply hφ Sᶜ).trans h1.le)
  have h4 : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) ≠ 0 → φ x ∈ S := (ae_withDensity_iff hdm).mp h3
  rw [lintegral_smul_measure]
  congr 1
  calc ∫⁻ y, ENNReal.ofReal (F y) ∂((μ.withDensity fun x => ENNReal.ofReal (w x)).map φ)
      = ∫⁻ y, ENNReal.ofReal (S.indicator F y) ∂((μ.withDensity fun x => ENNReal.ofReal (w x)).map φ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [h2] with y hy
        rw [Set.indicator_of_mem hy]
    _ = ∫⁻ x, ENNReal.ofReal (S.indicator F (φ x)) ∂(μ.withDensity fun x => ENNReal.ofReal (w x)) :=
        lintegral_map' hg.aemeasurable hφ
    _ = ∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal (S.indicator F (φ x)) ∂μ :=
        lintegral_withDensity_eq_lintegral_mul₀' hdm.aemeasurable (hg.comp_aemeasurable hφ)
    _ = ∫⁻ x, ENNReal.ofReal (w x * F (φ x)) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [h4] with x hx
        rw [ENNReal.ofReal_mul (hw0 x)]
        by_cases h0 : ENNReal.ofReal (w x) = 0
        · rw [h0, zero_mul, zero_mul]
        · rw [Set.indicator_of_mem (hx h0)]

def swapW {k r : ℕ} (W : LocW k r) : LocW k r where
  Wp := W.Wq
  Wq := W.Wp
  π := W.π'
  π' := W.π
  z := W.z'
  z' := W.z
  μG := W.μG
  μW := W.μW'
  μW' := W.μW
  μN := W.μN
  νS := W.νS'
  νS' := W.νS

def swapS {k r : ℕ} {W : LocW k r} (A : LocS W) : LocS (swapW W) where
  H := A.H
  σ := A.σ
  B := A.B'
  B' := A.B
  v0 := A.v0
  cN := A.cN
  deg := A.deg

theorem goodW_swap {D : D7} {τ w w' θ} {W : LocW D.R.k D.R.rS} (h : GoodW D τ w w' θ W) :
    GoodW D τ w' w θ (swapW W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h2, h1, h4, h3, h6, h5, h7, h10, h11, h8, h9, h12, h14, h13⟩

theorem goodS_swap {D : D7} {W : LocW D.R.k D.R.rS} {lam} {A : LocS W} (h : GoodS D lam A) :
    GoodS D lam (swapS A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h4, h3, h5, h6, h7, h8, h10, h9, h11⟩

theorem factor_le (b m T T' θ CT C1 C : ℝ) (r : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m) (hT0 : 0 < T) (hT0' : 0 < T')
    (hθ0 : 0 < θ) (hT : T ≤ b ^ (CT * m)) (hT' : T' ≤ b ^ (CT * m)) (hθ : θ ≤ b ^ (C1 * m ^ 2))
    (hC : 2 * |CT| + 2 * C1 ≤ C) : T * T' * θ ^ 2 / 2 ^ (r + 1) ≤ b ^ (C * m ^ 2) := by
  have hb0 : 0 < b := by linarith
  have hm2 : m ≤ m ^ 2 := by nlinarith
  have hx1 : CT * m ≤ |CT| * m ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self CT) (by linarith)).trans
      (mul_le_mul_of_nonneg_left hm2 (abs_nonneg CT))
  have h1 : T * T' ≤ b ^ (2 * |CT| * m ^ 2) := by
    calc T * T' ≤ b ^ (CT * m) * b ^ (CT * m) := mul_le_mul hT hT' hT0'.le (Real.rpow_nonneg hb0.le _)
      _ = b ^ (CT * m + CT * m) := (Real.rpow_add hb0 _ _).symm
      _ ≤ b ^ (2 * |CT| * m ^ 2) := Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  have h2 : θ ^ 2 ≤ b ^ (2 * C1 * m ^ 2) := by
    have hq : θ ^ 2 ≤ b ^ (C1 * m ^ 2) * b ^ (C1 * m ^ 2) := by nlinarith
    calc θ ^ 2 ≤ b ^ (C1 * m ^ 2) * b ^ (C1 * m ^ 2) := hq
      _ = b ^ (C1 * m ^ 2 + C1 * m ^ 2) := (Real.rpow_add hb0 _ _).symm
      _ = b ^ (2 * C1 * m ^ 2) := by ring_nf
  have h3 : T * T' * θ ^ 2 ≤ b ^ (C * m ^ 2) := by
    calc T * T' * θ ^ 2 ≤ b ^ (2 * |CT| * m ^ 2) * b ^ (2 * C1 * m ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg hb0.le _)
      _ = b ^ (2 * |CT| * m ^ 2 + 2 * C1 * m ^ 2) := (Real.rpow_add hb0 _ _).symm
      _ ≤ b ^ (C * m ^ 2) := Real.rpow_le_rpow_of_exponent_le hb (by nlinarith [sq_nonneg m])
  have hpos : 0 ≤ T * T' * θ ^ 2 := mul_nonneg (mul_pos hT0 hT0').le (sq_nonneg θ)
  have h2r : (1 : ℝ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
  exact (div_le_self hpos h2r).trans h3

private theorem dp_dq_div_eq_mul_div (dp dq c Vn Vk1 Vk deg T T' θ X P t : ℝ) (hc : 0 < c) (hVn : 0 < Vn)
    (hVk1 : 0 < Vk1) (hVk : 0 < Vk) (hdeg : 0 < deg) (hT : 0 < T) (hT' : 0 < T') (hθ : 0 < θ) (hX : 0 < X)
    (hP : 0 < P) (ht : 0 < t) :
    dp * dq / (deg / (c * Vn)) / (c * t * Vk ^ 2 / Vk1 / (P * (T * T')) / (X⁻¹ * θ) ^ 2) =
      P * (dp * dq * Vn * Vk1 / (deg * Vk ^ 2 * X ^ 2)) * (T * T' * θ ^ 2 / t) := by
  field_simp

end GlobalTheory.Amp.SchurBound

namespace GlobalTheory.Amp

open SchurBound

theorem schurSt_of_big_tie : ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → cdScaleTie D → BSch D large₂ C' Cl Cg cb Cu cT CT C0 → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 → SchurSt D large₂ C' Cl Cg cb Cu cT CT C0 C1 C := by
  intro Cg cb Cu cT CT C0 C1
  refine ⟨2 * |CT| + 2 * C1, fun C hC => ⟨0, ?_⟩⟩
  intro D large₂ C' Cl hBig hTie hBS hLI hZ τ w w' hTT θ hθw W hW A hA μsec hsec
  obtain ⟨-, -, hb, hm, hr, -, -, hmk, hv, -, -, -, -, -, -, -, hTr, -, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hBig.1 hZ
  have hb2 : (2 : ℝ) ≤ large₂.sc.b := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hk1 : 1 ≤ D.R.k := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (show 1 ≤ D.R.m by omega)
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθw.1
  have hv0 : 0 < D.host.v := by linarith
  have h2v : 0 < 2 * D.host.v := by linarith
  have hTw : 0 < Tr D w := by
    have h3 := hTT.2.2.1
    unfold Tr
    exact_mod_cast (show 0 < (D.mem w).A.T by omega)
  have hTw' : 0 < Tr D w' := by
    have h3 := hTT.2.2.2.1
    unfold Tr
    exact_mod_cast (show 0 < (D.mem w').A.T by omega)
  have hW0 := hW
  obtain ⟨-, -, hz, hz', hTz, hTz', hμG, hμW, hμW1, hμW', hμW'1, hμN, -, -⟩ := hW0
  have hA0 := hA
  obtain ⟨-, -, hB, hB', hsm, hv0ne, -, hcN, hl2, hl2', P, hCay, hFdeg⟩ := hA0
  obtain ⟨hUR, hIR, -, hOS, hOS'⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W (lamD D τ) A hθ0 hv0 hTT hW hA
  obtain ⟨-, -, hnt, hπU, hπI, -, -, -, hμNH, hQ, -, -, hΦc, -, -⟩ := hOS
  obtain ⟨-, -, hnt', hπU', hπI', -, -, -, -, hQ', -, -, hΦc', -, -⟩ := hOS'
  obtain ⟨hM, hM', hDec⟩ := hLI hZ τ w w' θ W hTT hW A hA
  have hTzp : 0 < Tz D.R.k D.R.rS W.z := by rw [hTz]; exact hTw
  have hTzp' : 0 < Tz D.R.k D.R.rS W.z' := by rw [hTz']; exact hTw'
  have hSide : SideIrr W.z W.π (muProd W.μW W.μN) :=
    ⟨⟨hz, hTzp, hπU, GlobalTheory.T.isHaarOn_besselSubgroup_prod_map _ _ _ _ _ hz hTzp hμW hμNH, inferInstance⟩, hπI, hnt⟩
  have hSide' : SideIrr W.z' W.π' (muProd W.μW' W.μN) :=
    ⟨⟨hz', hTzp', hπU', GlobalTheory.T.isHaarOn_besselSubgroup_prod_map _ _ _ _ _ hz' hTzp' hμW' hμNH, inferInstance⟩, hπI', hnt'⟩

  obtain ⟨c, hc0, hcD, -⟩ := GlobalTheory.T.exists_unique_haarDensity_at_identity (2 * D.R.rS + D.R.k + 1) (GG D.R.k D.R.rS) W.μG
    (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group D.R.k D.R.rS) hμG

  have hSch := GlobalTheory.T.besselModel_schur_of_formalDegree_density D.R.k D.R.rS A.σ (epsSH D.R) D.cd (D.s.cdScale _ (epsSH D.R)) P A.deg c W.μG
    (fun p q e h1 h2 S hS => hTie _ _ p q e h1 h2 S hS) hCay hFdeg hc0 hμG hcD
  have hVn := volUn_pos (2 * D.R.rS + D.R.k + 1)
  have hdeg : 0 < A.deg := by
    have h := hSch.1
    by_contra hn
    rw [not_lt] at hn
    have := div_nonpos_of_nonpos_of_nonneg hn (mul_pos hc0 hVn).le
    linarith
  have hnorm : ‖(((‖A.v0‖ : ℝ) : ℂ))⁻¹ • A.v0‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0ne)]
  have hStd : StdSm A.σ ((((‖A.v0‖ : ℝ) : ℂ))⁻¹ • A.v0) (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 5) W.μG
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1))) :=
    ⟨⟨hk1, hUR, hIR, hnorm, hμG, hSch, le_rfl,
      hDec.mono (SetLike.coe_subset_coe.mpr (DD_smul_le A.σ _ A.v0)), inferInstance⟩,
      smooth_smul A.σ _ A.v0 hsm⟩

  have hpsi : ∀ z, psiS D z = psiGen D.R.k D.R.rS z
      (fun _ => ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) :=
    fun z => psi_eq_psiGen _ _ _ _
  simp only [hpsi] at hM hB hM' hB'

  have hIso := hBS hZ τ w w' θ W hW A hA hTw
  have hIso' := hBS hZ τ w' w θ (swapW W) (goodW_swap hW) (swapS A) (goodS_swap hA) hTw'

  have hκ : 0 < (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ := mul_pos (Real.rpow_pos_of_pos h2v _) hθ0
  obtain ⟨hφ, hDis⟩ := GlobalTheory.T.besselDoubleCosetMeasure_bigCell_eq D.R.k D.R.rS W.z W.z' μsec W.μG W.μW W.μW' c
    ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ) hk1 hz hz' hTzp hTzp' hsec hc0 hκ hμG hcD hμW hμW1 hμW' hμW'1
  have hN : haarLie (Nset D.R.k D.R.rS) (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ)) = W.μN :=
    hμN.symm
  rw [hN, hTz, hTz'] at hDis
  rw [hTz, hTz'] at hφ

  have hF := GlobalTheory.T.measurable_hsNormSq_amplitude_besselUnitary D.R.k D.R.rS W.μG A.cN A.Φ A.Φ' hμG hΦc hΦc'
  have hX : 0 < (2 * D.host.v) ^ (D.R.rS * D.R.k) := pow_pos h2v _
  have hP : 0 < (Tr D w * Tr D w') ^ (D.R.k - 1) := pow_pos (mul_pos hTw hTw') _
  have ha : 0 < c * 2 ^ (D.R.rS + 1) * volUn D.R.k ^ 2 / volUn (D.R.k - 1) / (Tr D w * Tr D w') ^ D.R.k /
      ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ) ^ 2 := by
    have := volUn_pos D.R.k
    have := volUn_pos (D.R.k - 1)
    have := mul_pos hTw hTw'
    positivity
  have hcell := SchurBound.lintegral_cell volume (bcWeight D.R.k D.R.rS (Tr D w) (Tr D w'))
    (measurable_bcWeight _ _ _ _) (bcWeight_nonneg _ _ _ _)
    (fun q : (Fin D.R.rS → ℂ) × ℂ => (Matrix.of.symm (bigCell D.R.k D.R.rS q.1 (μsec q.2)) : Mt D.R.k D.R.rS))
    {x : Mt D.R.k D.R.rS | Matrix.of x ∈ GG D.R.k D.R.rS}
    (fun γ => hsNormSq (ampJ W.μG A.cN A.Φ A.Φ' (Matrix.of γ))) _ ha hφ (by
      refine measure_mono_null ?_ hDis.2.1
      intro x hx hG
      exact hx (Greg_subset _ _ hG)) hF
  have hBound := GlobalTheory.T.lintegral_hilbertSchmidtNormSq_besselAmplitude_le D.R.k D.R.rS A.σ A.v0 _ _ A.cN W.μG (muProd W.μW W.μN) (muProd W.μW' W.μN)
    W.νS W.νS' _ W.z W.z' _ _ W.π W.π' A.B A.B' hv0ne hStd hSide hSide' hQ hQ' hM hM' hB hB' hcN hl2 hl2'
    hIso hIso' hDis
  have key : ENNReal.ofReal (c * 2 ^ (D.R.rS + 1) * volUn D.R.k ^ 2 / volUn (D.R.k - 1) /
      (Tr D w * Tr D w') ^ D.R.k / ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ) ^ 2) *
      MMv D w w' A μsec ≤ ENNReal.ofReal ((Module.finrank ℂ W.Wp : ℝ) * Module.finrank ℂ W.Wq /
        (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1)))) :=
    hcell.symm.trans_le hBound
  have hXa : ∀ x y : ℝ, y ≠ 0 → y * (x / y) = x := fun x y hy => by field_simp
  have h2 : MMv D w w' A μsec ≤ ENNReal.ofReal ((Module.finrank ℂ W.Wp : ℝ) * Module.finrank ℂ W.Wq /
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1))) / (c * 2 ^ (D.R.rS + 1) * volUn D.R.k ^ 2 /
        volUn (D.R.k - 1) / (Tr D w * Tr D w') ^ D.R.k / ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ) ^ 2)) := by
    refine (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top).mp ?_
    rw [← ENNReal.ofReal_mul ha.le, hXa _ _ ha.ne']
    exact key
  refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hVk := volUn_pos D.R.k
  have hVk1 := volUn_pos (D.R.k - 1)
  have hE : (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) = ((2 * D.host.v) ^ (D.R.rS * D.R.k))⁻¹ := by
    rw [Real.rpow_neg h2v.le, ← Nat.cast_mul, Real.rpow_natCast]
  have hX2 : (2 * D.host.v) ^ (2 * D.R.rS * D.R.k) = ((2 * D.host.v) ^ (D.R.rS * D.R.k)) ^ 2 := by ring
  have hk' : (Tr D w * Tr D w') ^ D.R.k = (Tr D w * Tr D w') ^ (D.R.k - 1) * (Tr D w * Tr D w') := by
    rw [← pow_succ, Nat.sub_add_cancel hk1]
  rw [hE, hk', hX2, hr, SchurBound.dp_dq_div_eq_mul_div _ _ _ _ _ _ _ _ _ _ _ _ _ hc0 hVn (volUn_pos _) (volUn_pos _) hdeg hTw hTw' hθ0
    hX hP (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hP.le (by positivity))
  exact factor_le _ _ _ _ _ _ _ _ _ (by linarith) hm1 hTw hTw' hθ0 (hTr w) (hTr w') hθw.2 hC

end GlobalTheory.Amp
end
end
