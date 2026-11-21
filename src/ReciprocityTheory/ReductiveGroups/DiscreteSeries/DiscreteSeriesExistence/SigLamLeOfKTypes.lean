import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight

section
noncomputable section

open Finset Matrix MeasureTheory Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def cvA {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (v : H) : H :=
  ∫ g : Formalism.REAL.UJ ε, α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) v ∂(Formalism.REAL.muG ε)

theorem umat_mem_UJset (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat g ∈ UJset ε := g.2

theorem continuous_umatA (ε : Fin n → Bool) : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := Units.continuous_val.comp continuous_subtype_val

private theorem Jm_sq_lemma (e : Fin n → Bool) : Formalism.REAL.Jm e * Formalism.REAL.Jm e = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : e a <;> simp [h]

private theorem inv_eq_lemma_2 (e : Fin n → Bool) (g : Formalism.REAL.UJ e) :
    (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Formalism.REAL.Jm e * (Formalism.MainNotions.S.umat g)ᴴ * Formalism.REAL.Jm e := by
  have hg : (Formalism.MainNotions.S.umat g)ᴴ * Formalism.REAL.Jm e * Formalism.MainNotions.S.umat g = Formalism.REAL.Jm e := g.2
  have hl : (Formalism.REAL.Jm e * (Formalism.MainNotions.S.umat g)ᴴ * Formalism.REAL.Jm e) * Formalism.MainNotions.S.umat g = 1 := by
    calc (Formalism.REAL.Jm e * (Formalism.MainNotions.S.umat g)ᴴ * Formalism.REAL.Jm e) * Formalism.MainNotions.S.umat g
        = Formalism.REAL.Jm e * ((Formalism.MainNotions.S.umat g)ᴴ * Formalism.REAL.Jm e * Formalism.MainNotions.S.umat g) := by
          simp only [mul_assoc]
      _ = 1 := by rw [hg, Jm_sq_lemma]
  exact Units.inv_eq_of_mul_eq_one_left hl

theorem isClosedEmbedding_umatA (ε : Fin n → Bool) :
    IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := continuous_umatA ε
  have hJ : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) := by
    first
    | exact (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    | continuity
  have hF : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ =>
      (M, MulOpposite.op (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε))) := by
    first
    | exact continuous_id.prodMk (MulOpposite.continuous_op.comp hJ)
    | exact continuous_id.prod_mk (MulOpposite.continuous_op.comp hJ)
  have h2 : ((fun M : Matrix (Fin n) (Fin n) ℂ =>
      (M, MulOpposite.op (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε))) ∘ (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g))
      = Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) ∘ Subtype.val := by
    funext g
    simp only [Function.comp_apply, Units.embedProduct_apply]
    rw [inv_eq_lemma_2]
  have hind : IsInducing ((fun M : Matrix (Fin n) (Fin n) ℂ =>
      (M, MulOpposite.op (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε))) ∘ (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g)) := by
    rw [h2]
    have he : IsInducing (Units.embedProduct (Matrix (Fin n) (Fin n) ℂ)) := by
      first
      | exact Units.isEmbedding_embedProduct.isInducing
      | exact ⟨rfl⟩
    exact he.comp IsInducing.subtypeVal
  have hrange : Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g)
      = {M : Matrix (Fin n) (Fin n) ℂ | Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε} := by
    ext M
    constructor
    · rintro ⟨g, rfl⟩
      exact g.2
    · intro hM
      have hl : (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) * M = 1 := by
        calc (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) * M = Formalism.REAL.Jm ε * (Mᴴ * Formalism.REAL.Jm ε * M) := by
              simp only [mul_assoc]
          _ = 1 := by rw [hM, Jm_sq_lemma]
      have hr : M * (Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε) = 1 := by
        first
        | exact mul_eq_one_comm.mp hl
        | exact (Matrix.invertibleOfLeftInverse M _ hl).mul_invOf_self
        | (letI := Matrix.invertibleOfLeftInverse M _ hl; exact mul_invOf_self M)
      exact ⟨⟨⟨M, _, hr, hl⟩, hM⟩, rfl⟩
  refine ⟨⟨IsInducing.of_comp hc hF hind, ?_⟩, ?_⟩
  · intro a b h
    exact Subtype.ext (Units.ext h)
  · rw [hrange]
    have hq : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => Mᴴ * Formalism.REAL.Jm ε * M) := by
      first
      | exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
      | continuity
    exact isClosed_eq hq continuous_const

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem continuous_orbitA (hσ : IsURepOn (UJset ε) σ) (v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) := (hσ.2.2 v).comp_continuous (continuous_umatA ε) (fun g => umat_mem_UJset ε g)

private theorem muG_fin_lemma_3 (e : Fin n → Bool) : IsFiniteMeasureOnCompacts (Formalism.REAL.muG e) := by
  first
  | infer_instance
  | (unfold Formalism.REAL.muG; infer_instance)
  | (simp only [Formalism.REAL.muG]; infer_instance)

theorem integrable_cvA (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) (v : H) :
    Integrable (fun g : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) v) (Formalism.REAL.muG ε) := by
  haveI := muG_fin_lemma_3 ε
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) v) :=
    (hα.comp (continuous_umatA ε)).smul (continuous_orbitA hσ v)
  have h1 : HasCompactSupport (fun g : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat g)) :=
    hαc.comp_isClosedEmbedding (isClosedEmbedding_umatA ε)
  have hs : HasCompactSupport (fun g : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) v) := by
    apply h1.mono
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp [h0]
  exact hc.integrable_of_hasCompactSupport hs

theorem cvA_add_fun (hσ : IsURepOn (UJset ε) σ) {α β : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) (hβ : Continuous β) (hβc : HasCompactSupport β) (v : H) :
    cvA ε σ (α + β) v = cvA ε σ α v + cvA ε σ β v := by
  simp only [cvA]
  rw [← integral_add (integrable_cvA hσ hα hαc v) (integrable_cvA hσ hβ hβc v)]
  congr 1
  funext g
  rw [Pi.add_apply, add_smul]

theorem cvA_smul_fun (c : ℂ) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (v : H) :
    cvA ε σ (c • α) v = c • cvA ε σ α v := by
  simp only [cvA]
  rw [← integral_smul]
  congr 1
  funext g
  rw [Pi.smul_apply, smul_eq_mul, mul_smul]

theorem cvA_zero_fun (v : H) : cvA ε σ 0 v = 0 := by
  simp [cvA]

theorem cvA_add_vec (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) (v w : H) :
    cvA ε σ α (v + w) = cvA ε σ α v + cvA ε σ α w := by
  simp only [cvA, map_add, smul_add]
  exact integral_add (integrable_cvA hσ hα hαc v) (integrable_cvA hσ hα hαc w)

theorem cvA_smul_vec (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (c : ℂ) (v : H) :
    cvA ε σ α (c • v) = c • cvA ε σ α v := by
  simp only [cvA, map_smul]
  rw [← integral_smul]
  congr 1
  funext g
  exact smul_comm _ _ _

theorem cvA_near (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφ0 : ∀ g, 0 ≤ φ g)
    (hφ1 : ∫ g : Formalism.REAL.UJ ε, φ (Formalism.MainNotions.S.umat g) ∂(Formalism.REAL.muG ε) = 1) {w : H} {η : ℝ}
    (hη : ∀ g : Formalism.REAL.UJ ε, φ (Formalism.MainNotions.S.umat g) ≠ 0 → ‖σ (Formalism.MainNotions.S.umat g) w - w‖ ≤ η) :
    ‖cvA ε σ (fun g => (φ g : ℂ)) w - w‖ ≤ η := by
  haveI := muG_fin_lemma_3 ε
  have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (Formalism.MainNotions.S.umat g)) (Formalism.REAL.muG ε) :=
    (hφc.comp (continuous_umatA ε)).integrable_of_hasCompactSupport
      (hφs.comp_isClosedEmbedding (isClosedEmbedding_umatA ε))
  have hψc : Integrable (fun g : Formalism.REAL.UJ ε => ((φ (Formalism.MainNotions.S.umat g) : ℝ) : ℂ)) (Formalism.REAL.muG ε) :=
    hψi.ofReal
  have hI1 : Integrable (fun g : Formalism.REAL.UJ ε => ((φ (Formalism.MainNotions.S.umat g) : ℂ)) • σ (Formalism.MainNotions.S.umat g) w)
      (Formalism.REAL.muG ε) :=
    integrable_cvA hσ (α := fun g => (φ g : ℂ)) (Complex.continuous_ofReal.comp hφc)
      (hφs.comp_left Complex.ofReal_zero) w
  have hI2 : Integrable (fun g : Formalism.REAL.UJ ε => ((φ (Formalism.MainNotions.S.umat g) : ℂ)) • w) (Formalism.REAL.muG ε) :=
    hψc.smul_const w
  have hw : w = ∫ g : Formalism.REAL.UJ ε, ((φ (Formalism.MainNotions.S.umat g) : ℂ)) • w ∂(Formalism.REAL.muG ε) := by
    rw [integral_smul_const]
    first
    | rw [integral_ofReal, hφ1, Complex.ofReal_one, one_smul]
    | rw [integral_complex_ofReal, hφ1, Complex.ofReal_one, one_smul]
  have hdiff : ∫ g : Formalism.REAL.UJ ε, ((φ (Formalism.MainNotions.S.umat g) : ℂ)) • (σ (Formalism.MainNotions.S.umat g) w - w) ∂(Formalism.REAL.muG ε)
      = cvA ε σ (fun g => (φ g : ℂ)) w - w := by
    simp_rw [smul_sub]
    rw [integral_sub hI1 hI2, ← hw]
    rfl
  rw [← hdiff]
  calc ‖∫ g : Formalism.REAL.UJ ε, ((φ (Formalism.MainNotions.S.umat g) : ℂ)) • (σ (Formalism.MainNotions.S.umat g) w - w) ∂(Formalism.REAL.muG ε)‖
      ≤ ∫ g : Formalism.REAL.UJ ε, φ (Formalism.MainNotions.S.umat g) * η ∂(Formalism.REAL.muG ε) := by
        refine norm_integral_le_of_norm_le (hψi.mul_const η) (ae_of_all _ (fun g => ?_))
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hφ0 _)]
        by_cases h0 : φ (Formalism.MainNotions.S.umat g) = 0
        · rw [h0]
          simp
        · exact mul_le_mul_of_nonneg_left (hη g h0) (hφ0 _)
    _ = η := by rw [integral_mul_const, hφ1, one_mul]

section Bump

def hsdA (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖(g - 1) i j‖ ^ 2

theorem contDiff_entryA (i j : Fin n) : ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g i j) := by
  first
  | exact (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin n → ℂ) i)
  | fun_prop
  | exact ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i :
      (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → ℂ))).contDiff

theorem contDiff_hsdA : ContDiff ℝ ∞ (hsdA (n := n)) := by
  unfold hsdA
  refine ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => ?_))
  show ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => ‖g i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2)
  first
  | exact (contDiff_norm_sq ℂ).comp ((contDiff_entryA i j).sub contDiff_const)
  | exact (contDiff_norm_sq ℝ).comp ((contDiff_entryA i j).sub contDiff_const)

theorem hsdA_one : hsdA (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [hsdA]

theorem norm_sub_one_le_of_hsdA {g : Matrix (Fin n) (Fin n) ℂ} {δ : ℝ} (h : hsdA g ≤ δ) :
    ‖g - 1‖ ≤ Real.sqrt δ := by
  rw [Matrix.norm_le_iff (Real.sqrt_nonneg _)]
  intro i j
  have h2 : ‖(g - 1) i j‖ ^ 2 ≤ δ := by
    calc ‖(g - 1) i j‖ ^ 2 ≤ ∑ j', ‖(g - 1) i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖(g - 1) i j'‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ j)
      _ ≤ hsdA g :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖(g - 1) i' j'‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ i)
      _ ≤ δ := h
  have := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _)] at this

theorem hsdA_eq_trace (g : Matrix (Fin n) (Fin n) ℂ) :
    hsdA g = (trace ((g - 1)ᴴ * (g - 1))).re := by
  unfold hsdA
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  first
  | (rw [Complex.star_def, Complex.conj_mul']; norm_cast)
  | (simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]; ring)
  | (simp [Complex.mul_re, Complex.sq_abs, Complex.normSq_apply]; ring)

theorem hsdA_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : hsdA (k * g * star k) = hsdA g := by
  rw [hsdA_eq_trace, hsdA_eq_trace]
  have hk1 : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hk
  have hk2 : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have h1 : k * g * star k - 1 = k * (g - 1) * star k := by
    rw [mul_sub, sub_mul, mul_one, hk1]
  rw [h1]
  have hstar : (k * (g - 1) * star k)ᴴ = k * (g - 1)ᴴ * star k := by
    simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      mul_assoc]
  have h2 : k * (g - 1)ᴴ * star k * (k * (g - 1) * star k) = k * ((g - 1)ᴴ * (g - 1)) * star k := by
    calc k * (g - 1)ᴴ * star k * (k * (g - 1) * star k)
        = k * (g - 1)ᴴ * (star k * k) * (g - 1) * star k := by simp only [mul_assoc]
      _ = k * ((g - 1)ᴴ * (g - 1)) * star k := by rw [hk2, mul_one]; simp only [mul_assoc]
  rw [hstar, h2, Matrix.trace_mul_comm, ← mul_assoc, hk2, one_mul]

def bumpA (δ : ℝ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.smoothTransition (δ - hsdA g)

theorem contDiff_bumpA (δ : ℝ) : ContDiff ℝ ∞ (bumpA (n := n) δ) := Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_hsdA)

theorem bumpA_nonneg (δ : ℝ) (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ bumpA δ g := Real.smoothTransition.nonneg _

theorem bumpA_one_pos {δ : ℝ} (hδ : 0 < δ) : 0 < bumpA δ (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold bumpA
  rw [hsdA_one, sub_zero]
  exact Real.smoothTransition.pos_of_pos hδ

theorem hsdA_lt_of_bumpA {δ : ℝ} {g : Matrix (Fin n) (Fin n) ℂ} (h : bumpA δ g ≠ 0) : hsdA g < δ := by
  by_contra hc
  exact h (Real.smoothTransition.zero_of_nonpos (by linarith [not_lt.mp hc]))

theorem bumpA_conj {δ : ℝ} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : bumpA δ (k * g * star k) = bumpA δ g := by
  unfold bumpA
  rw [hsdA_conj hk]

theorem tsupport_bumpA (δ : ℝ) : tsupport (bumpA (n := n) δ) ⊆ {g | hsdA g ≤ δ} := closure_minimal (fun g hg => (hsdA_lt_of_bumpA hg).le) (isClosed_le contDiff_hsdA.continuous continuous_const)

theorem hasCompactSupport_bumpA (δ : ℝ) : HasCompactSupport (bumpA (n := n) δ) := by
  haveI : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := by
    first
    | infer_instance
    | exact (inferInstance : ProperSpace (Fin n → Fin n → ℂ))
    | exact FiniteDimensional.proper_real _
  have hsub : tsupport (bumpA (n := n) δ) ⊆ Metric.closedBall 1 (Real.sqrt δ) := by
    intro g hg
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact norm_sub_one_le_of_hsdA (tsupport_bumpA δ hg)
  exact (isCompact_closedBall 1 _).of_isClosed_subset (isClosed_tsupport _) hsub

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def AdmA (ε : Fin n → Bool) (U : Set (Matrix (Fin n) (Fin n) ℂ)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Prop :=
  ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U ∧ ∀ k ∈ Kset ε, ∀ g, α (k * g * star k) = α g

theorem AdmA.add {U : Set (Matrix (Fin n) (Fin n) ℂ)} {α β : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : AdmA ε U α) (hβ : AdmA ε U β) : AdmA ε U (α + β) := by
  obtain ⟨h1, h2, h3, h4⟩ := hα
  obtain ⟨k1, k2, k3, k4⟩ := hβ
  refine ⟨h1.add k1, h2.add k2, ?_, fun k hk g => ?_⟩
  · have ht : tsupport (α + β) ⊆ tsupport α ∪ tsupport β := by
      first
      | exact tsupport_add α β
      | exact closure_minimal ((Function.support_add α β).trans
          (Set.union_subset_union (subset_tsupport α) (subset_tsupport β)))
          ((isClosed_tsupport α).union (isClosed_tsupport β))
    exact ht.trans (Set.union_subset h3 k3)
  · show α (k * g * star k) + β (k * g * star k) = α g + β g
    rw [h4 k hk g, k4 k hk g]

theorem AdmA.smul {U : Set (Matrix (Fin n) (Fin n) ℂ)} {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : AdmA ε U α) (c : ℂ) : AdmA ε U (c • α) := by
  obtain ⟨h1, h2, h3, h4⟩ := hα
  refine ⟨h1.const_smul c, h2.mono (Function.support_const_smul_subset c α),
    (closure_mono (Function.support_const_smul_subset c α)).trans h3, fun k hk g => ?_⟩
  show c • α (k * g * star k) = c • α g
  rw [h4 k hk g]

theorem AdmA.zero (U : Set (Matrix (Fin n) (Fin n) ℂ)) : AdmA ε U 0 := by
  refine ⟨?_, HasCompactSupport.zero, ?_, fun _ _ _ => rfl⟩
  · first
    | exact contDiff_zero_fun
    | exact contDiff_const
  · rw [tsupport_zero]
    exact Set.empty_subset _

theorem one_mem_UJsetA (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  first
  | exact umat_mem_UJset ε 1
  | (show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε; simp)

private theorem muG_pos_lemma_4 (e : Fin n → Bool) : Measure.IsOpenPosMeasure (Formalism.REAL.muG e) := by
  first
  | infer_instance
  | (unfold Formalism.REAL.muG; infer_instance)
  | (simp only [Formalism.REAL.muG]; infer_instance)

theorem integral_bumpA_pos (ε : Fin n → Bool) {δ : ℝ} (hδ : 0 < δ) :
    0 < ∫ g : Formalism.REAL.UJ ε, bumpA δ (Formalism.MainNotions.S.umat g) ∂(Formalism.REAL.muG ε) := by
  haveI := muG_fin_lemma_3 ε
  haveI := muG_pos_lemma_4 ε
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((contDiff_bumpA δ).continuous.comp (continuous_umatA ε))
    ((hasCompactSupport_bumpA δ).comp_isClosedEmbedding (isClosedEmbedding_umatA ε))
    (fun g => bumpA_nonneg δ _)
    (show (bumpA δ ∘ fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) 1 ≠ 0 from (bumpA_one_pos hδ).ne')

theorem exists_nearA (hσ : IsURepOn (UJset ε) σ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) {m : ℕ} (b : Fin m → H) {η : ℝ} (hη : 0 < η) :
    ∃ α, AdmA ε U α ∧ ∀ i, ‖cvA ε σ α (b i) - b i‖ ≤ η := by
  obtain ⟨r₁, hr₁, hU₁⟩ := Metric.isOpen_iff.mp hU 1 h1
  have hev : ∀ᶠ M in 𝓝[UJset ε] (1 : Matrix (Fin n) (Fin n) ℂ), ∀ i, dist (σ M (b i)) (σ 1 (b i)) < η :=
    Filter.eventually_all.mpr (fun i => Metric.tendsto_nhds.mp (hσ.2.2 (b i) 1 (one_mem_UJsetA ε)) η hη)
  obtain ⟨r₂, hr₂, hU₂⟩ := Metric.mem_nhdsWithin_iff.mp hev
  obtain ⟨s, hs0, hs1, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s < r₁ ∧ s < r₂ :=
    ⟨min r₁ r₂ / 2, half_pos (lt_min hr₁ hr₂),
      by linarith [min_le_left r₁ r₂, half_lt_self (lt_min hr₁ hr₂)],
      by linarith [min_le_right r₁ r₂, half_lt_self (lt_min hr₁ hr₂)]⟩
  have hsq : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs0.le
  have hδ : 0 < s ^ 2 := by positivity
  have hc := integral_bumpA_pos ε hδ
  generalize hcd : (∫ g : Formalism.REAL.UJ ε, bumpA (s ^ 2) (Formalism.MainNotions.S.umat g) ∂(Formalism.REAL.muG ε)) = c at hc
  have hφc : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => bumpA (s ^ 2) M / c) :=
    (contDiff_bumpA (s ^ 2)).continuous.div_const c
  have hsupp : Function.support (fun M : Matrix (Fin n) (Fin n) ℂ => bumpA (s ^ 2) M / c)
      ⊆ Function.support (bumpA (n := n) (s ^ 2)) := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp [h0]
  have hφs : HasCompactSupport (fun M : Matrix (Fin n) (Fin n) ℂ => bumpA (s ^ 2) M / c) :=
    (hasCompactSupport_bumpA (s ^ 2)).mono hsupp
  have hφ0 : ∀ M : Matrix (Fin n) (Fin n) ℂ, 0 ≤ (fun M : Matrix (Fin n) (Fin n) ℂ => bumpA (s ^ 2) M / c) M :=
    fun M => div_nonneg (bumpA_nonneg _ _) hc.le
  have hφ1 : ∫ g : Formalism.REAL.UJ ε, (fun M : Matrix (Fin n) (Fin n) ℂ => bumpA (s ^ 2) M / c) (Formalism.MainNotions.S.umat g)
      ∂(Formalism.REAL.muG ε) = 1 := by
    show ∫ g : Formalism.REAL.UJ ε, bumpA (s ^ 2) (Formalism.MainNotions.S.umat g) / c ∂(Formalism.REAL.muG ε) = 1
    rw [integral_div, hcd, div_self hc.ne']
  refine ⟨fun M => ((bumpA (s ^ 2) M / c : ℝ) : ℂ), ⟨?_, ?_, ?_, ?_⟩, fun i => ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((contDiff_bumpA (s ^ 2)).div_const c)
  · exact hφs.comp_left Complex.ofReal_zero
  · intro M hM
    apply hU₁
    have hsupp' : Function.support (fun M : Matrix (Fin n) (Fin n) ℂ => ((bumpA (s ^ 2) M / c : ℝ) : ℂ))
        ⊆ Function.support (bumpA (n := n) (s ^ 2)) := by
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      simp [h0]
    have hM' : M ∈ tsupport (bumpA (n := n) (s ^ 2)) := closure_mono hsupp' hM
    have hn := norm_sub_one_le_of_hsdA (tsupport_bumpA (s ^ 2) hM')
    rw [hsq] at hn
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  · intro k hk g
    obtain ⟨hk1, -⟩ := hk
    show ((bumpA (s ^ 2) (k * g * star k) / c : ℝ) : ℂ) = ((bumpA (s ^ 2) g / c : ℝ) : ℂ)
    rw [bumpA_conj hk1]
  · refine cvA_near hσ hφc hφs hφ0 hφ1 (fun g hg => ?_)
    have hb : bumpA (s ^ 2) (Formalism.MainNotions.S.umat g) ≠ 0 := by
      intro h0
      apply hg
      simp [h0]
    have hn := norm_sub_one_le_of_hsdA (hsdA_lt_of_bumpA hb).le
    rw [hsq] at hn
    have hmem : Formalism.MainNotions.S.umat g ∈ Metric.ball (1 : Matrix (Fin n) (Fin n) ℂ) r₂ ∩ UJset ε := by
      refine ⟨?_, umat_mem_UJset ε g⟩
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have h3 : ∀ j, dist (σ (Formalism.MainNotions.S.umat g) (b j)) (σ 1 (b j)) < η := hU₂ hmem
    have h4 := h3 i
    rw [hσ.1.1, ContinuousLinearMap.one_apply, dist_eq_norm] at h4
    exact h4.le

end Bump

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kUJA (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : Formalism.REAL.UJ ε :=
  ⟨⟨k, star k, Matrix.mem_unitaryGroup_iff.1 hk.1, Matrix.mem_unitaryGroup_iff'.1 hk.1⟩, by
    show Formalism.REAL.inUJ ε k
    rw [mir_inUJ_iff]
    show kᴴ * Jm ε * k = Jm ε
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.1 hk.1, Matrix.one_mul]⟩

theorem cvA_equivariantA (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) (hαK : ∀ k ∈ Kset ε, ∀ g, α (k * g * star k) = α g)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : H) :
    σ k (cvA ε σ α v) = cvA ε σ α (σ k v) := by
  set κ := kUJA ε hk with hκdef
  have hκ : Formalism.MainNotions.S.umat κ = k := rfl
  have : (Formalism.REAL.muG ε).IsMulRightInvariant :=
    ⟨fun y => (measurePreserving_mul_right ε y).map_eq⟩
  have hmul : ∀ a b : Formalism.REAL.UJ ε,
      σ (Formalism.MainNotions.S.umat (a * b)) = (σ (Formalism.MainNotions.S.umat a)).comp (σ (Formalism.MainNotions.S.umat b)) :=
    fun a b => hσ.1.2 _ (umat_mem_UJset ε a) _ (umat_mem_UJset ε b)
  set F : Formalism.REAL.UJ ε → H := fun g => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat (g * κ)) v with hF
  have hR : cvA ε σ α (σ k v) = ∫ g, F g ∂(Formalism.REAL.muG ε) := by
    unfold cvA
    congr 1
    funext g
    rw [hF]
    dsimp only
    rw [hmul, ContinuousLinearMap.comp_apply, hκ]
  have hL : σ k (cvA ε σ α v) = ∫ g, F (κ * g * κ⁻¹) ∂(Formalism.REAL.muG ε) := by
    unfold cvA
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_cvA hσ hα hαc v)]
    congr 1
    funext g
    have hc : Formalism.MainNotions.S.umat (κ * g * κ⁻¹) = k * Formalism.MainNotions.S.umat g * star k := rfl
    rw [hF]
    dsimp only
    rw [inv_mul_cancel_right, hc, hαK k hk, hmul, ContinuousLinearMap.comp_apply, hκ, map_smul]
  rw [hL, hR]
  calc ∫ g, F (κ * g * κ⁻¹) ∂(Formalism.REAL.muG ε) = ∫ g, F (g * κ⁻¹) ∂(Formalism.REAL.muG ε) :=
        integral_mul_left_eq_self (fun x => F (x * κ⁻¹)) κ
    _ = ∫ g, F g ∂(Formalism.REAL.muG ε) := integral_mul_right_eq_self F κ⁻¹

theorem map_le_isoA (T : H →ₗ[ℂ] H) (hT : ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, σ k (T v) = T (σ k v))
    {μ : Fin n → ℝ} {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    S.map T ≤ sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} := by
  obtain ⟨hfin, hstab, hirr, ⟨w, hwS, hw0, hwt⟩, hdom⟩ := hS
  have hstab0 : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ LinearMap.ker T) := by
    intro g hg v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hv ⊢
    exact ⟨hstab g hg v hv.1, by rw [← hT g hg v, hv.2, _root_.map_zero]⟩
  rcases hirr _ inf_le_left hstab0 with h0 | h0
  · have hinj : ∀ x ∈ S, T x = 0 → x = 0 := fun x hx hTx => by
      have hx' : x ∈ S ⊓ LinearMap.ker T := Submodule.mem_inf.2 ⟨hx, LinearMap.mem_ker.2 hTx⟩
      rw [h0] at hx'
      exact (Submodule.mem_bot ℂ).1 hx'
    apply le_sSup
    show Formalism.MainNotions.S.IsKTypeOf ε σ μ (S.map T)
    unfold Formalism.MainNotions.S.IsKTypeOf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · haveI : FiniteDimensional ℂ S := hfin
      infer_instance
    · rintro g hg _ ⟨x, hx, rfl⟩
      rw [hT g hg x]
      exact Submodule.mem_map_of_mem (hstab g hg x hx)
    · intro S' hS' hS'st
      have hst : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap T) := by
        intro g hg v hv
        rw [Submodule.mem_inf, Submodule.mem_comap] at hv ⊢
        exact ⟨hstab g hg v hv.1, by rw [← hT g hg v]; exact hS'st g hg _ hv.2⟩
      rcases hirr _ inf_le_left hst with h1 | h1
      · left
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hS' hy
        have hx' : x ∈ S ⊓ S'.comap T := Submodule.mem_inf.2 ⟨hx, Submodule.mem_comap.2 hy⟩
        rw [h1, Submodule.mem_bot] at hx'
        rw [hx', _root_.map_zero]
        exact Submodule.zero_mem _
      · right
        refine le_antisymm hS' ?_
        rintro _ ⟨x, hx, rfl⟩
        have hx' : x ∈ S ⊓ S'.comap T := by rw [h1]; exact hx
        exact Submodule.mem_comap.1 (Submodule.mem_inf.1 hx').2
    · have hTw : T w ≠ 0 := fun h => hw0 (hinj w hwS h)
      refine ⟨T w, Submodule.mem_map_of_mem hwS, hTw, ?_⟩
      intro θ hθ
      rw [hT _ hθ w, hwt θ hθ, _root_.map_smul]
    · rintro μ' _ ⟨x, hx, rfl⟩ hne hwt'
      have hx0 : x ≠ 0 := fun h => hne (by rw [h, _root_.map_zero])
      refine hdom μ' x hx hx0 ?_
      intro θ hθ
      have h1 := hwt' θ hθ
      rw [hT _ hθ x] at h1
      refine sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hstab _ hθ x hx) (Submodule.smul_mem _ _ hx)) ?_)
      rw [_root_.map_sub, h1, _root_.map_smul, sub_self]
  · rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ S ⊓ LinearMap.ker T := by rw [h0]; exact hx
    rw [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx').2]
    exact Submodule.zero_mem _

theorem exists_cvA_idA (hσ : IsURepOn (UJset ε) σ)
    (hadm : ∀ μ : Fin n → ℝ, FiniteDimensional ℂ
      (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H))
    (W : Submodule ℂ H) (hWf : FiniteDimensional ℂ W)
    (hWsum : W ≤ sSup {S : Submodule ℂ H | ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S})
    {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) :
    ∃ α, AdmA ε U α ∧ ∀ w ∈ W, cvA ε σ α w = w := by
  classical
  let T : ∀ α, AdmA ε U α → H →ₗ[ℂ] H := fun α hα =>
    { toFun := cvA ε σ α
      map_add' := cvA_add_vec hσ hα.1.continuous hα.2.1
      map_smul' := fun c v => cvA_smul_vec α c v }
  have hTK : ∀ α (hα : AdmA ε U α), ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, σ k (T α hα v) = T α hα (σ k v) :=
    fun α hα k hk v => cvA_equivariantA hσ hα.1.continuous hα.2.1 hα.2.2.2
      (by rw [← mir_Kset_eq]; exact hk) v
  have hWc : IsCompactElement W :=
    (Submodule.fg_iff_compact W).1 (Module.Finite.iff_fg.1 hWf)
  obtain ⟨t, hts, hWt⟩ :=
    (CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup (k := W)).1 hWc _ hWsum
  let iso : Submodule ℂ H → Submodule ℂ H := fun S =>
    if h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S then sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'} else ⊥
  haveI hisoF : ∀ S, FiniteDimensional ℂ (iso S) := by
    intro S
    by_cases h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S
    · have e : iso S = sSup {S' | Formalism.MainNotions.S.IsKTypeOf ε σ h.choose S'} := dif_pos h
      rw [e]
      exact hadm _
    · have e : iso S = ⊥ := dif_neg h
      rw [e]
      infer_instance
  let W2 := t.sup iso
  have hS_le : ∀ S ∈ t, S ≤ iso S ∧ ∀ α (hα : AdmA ε U α), S.map (T α hα) ≤ iso S := by
    intro S hS
    have h : ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S := hts hS
    simp only [iso, dif_pos h]
    exact ⟨le_sSup h.choose_spec, fun α hα => map_le_isoA (T α hα) (hTK α hα) h.choose_spec⟩
  have hWW2 : W ≤ W2 :=
    hWt.trans (Finset.sup_le fun S hS => (hS_le S hS).1.trans (Finset.le_sup (f := iso) hS))
  have hmapW : ∀ α (hα : AdmA ε U α), ∀ w ∈ W, cvA ε σ α w ∈ W2 := by
    intro α hα w hw
    have : W ≤ W2.comap (T α hα) :=
      hWt.trans (Finset.sup_le fun S hS => Submodule.map_le_iff_le_comap.1
        (((hS_le S hS).2 α hα).trans (Finset.le_sup (f := iso) hS)))
    exact this hw
  let b := Module.finBasis ℂ W
  let bw : Fin (Module.finrank ℂ W) → H := fun i => (b i : H)
  let R : Submodule ℂ (Fin (Module.finrank ℂ W) → W2) :=
    { carrier := {p | ∃ α, AdmA ε U α ∧ ∀ i, cvA ε σ α (bw i) = (p i : H)}
      add_mem' := by
        rintro p q ⟨α, hα, hp⟩ ⟨β, hβ, hq⟩
        exact ⟨α + β, hα.add hβ, fun i => by
          rw [cvA_add_fun hσ hα.1.continuous hα.2.1 hβ.1.continuous hβ.2.1, hp, hq]
          rfl⟩
      zero_mem' := ⟨0, AdmA.zero U, fun i => by rw [cvA_zero_fun]; rfl⟩
      smul_mem' := by
        rintro c p ⟨α, hα, hp⟩
        exact ⟨c • α, hα.smul c, fun i => by rw [cvA_smul_fun, hp]; rfl⟩ }
  have hRc : IsClosed (R : Set (Fin (Module.finrank ℂ W) → W2)) := R.closed_of_finiteDimensional
  let p0 : Fin (Module.finrank ℂ W) → W2 := fun i => ⟨bw i, hWW2 (b i).2⟩
  have hp0 : p0 ∈ closure (R : Set (Fin (Module.finrank ℂ W) → W2)) := by
    rw [Metric.mem_closure_iff]
    intro η hη
    obtain ⟨α, hα, hnear⟩ := exists_nearA hσ hU h1 bw (half_pos hη)
    refine ⟨fun i => ⟨cvA ε σ α (bw i), hmapW α hα _ (b i).2⟩, ⟨α, hα, fun i => rfl⟩, ?_⟩
    rw [dist_pi_lt_iff hη]
    intro i
    show dist (bw i) (cvA ε σ α (bw i)) < η
    rw [dist_comm, dist_eq_norm]
    linarith [hnear i]
  rw [hRc.closure_eq] at hp0
  obtain ⟨α, hα, hfix⟩ := hp0
  refine ⟨α, hα, ?_⟩
  have hext : (T α hα).comp W.subtype = W.subtype := b.ext fun i => hfix i
  intro w hw
  exact LinearMap.congr_fun hext ⟨w, hw⟩

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def opConv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (v : H) : H :=
  ∫ g : Formalism.REAL.UJ ε, α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) v ∂(Formalism.REAL.muG ε)

def IsAdKInv (ε : Fin n → Bool) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ k ∈ Kset ε, ∀ g, α (k * g * star k) = α g

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_le_of_kTypes (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (W : Submodule ℂ (Hlam ε Ψ v₀)) (hWf : FiniteDimensional ℂ W)
    (hWfull : ∀ (μ : Fin n → ℝ) (S : Submodule ℂ (Hlam ε Ψ v₀)),
      Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S →
        (∃ S' ≤ W, Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S') → S ≤ W)
    (hWsum : W ≤ sSup {S : Submodule ℂ (Hlam ε Ψ v₀) | ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) μ S})
    (U : Set (Matrix (Fin n) (Fin n) ℂ)) (hU : IsOpen U) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U) :
    ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U ∧
      IsAdKInv ε α ∧ ∀ w ∈ W, opConv ε (sigLam ε Ψ v₀) α w = w := by
  obtain ⟨α, ⟨hsmooth, hcpt, hsupp, hinv⟩, hfix⟩ :=
    exists_cvA_idA (sigLam_isURepOn hgap hP hv₀) (sigLam_admissible hgap hP hv₀) W hWf hWsum hU h1
  exact ⟨α, hsmooth, hcpt, hsupp, fun k hk g => hinv k hk g, hfix⟩

end ReciprocityTheory.ChartRestriction.DS
end
end
