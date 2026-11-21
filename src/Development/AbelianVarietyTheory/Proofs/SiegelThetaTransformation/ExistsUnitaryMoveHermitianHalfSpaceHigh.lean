import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsNearlyPrimitive
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryExt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroNormSqLeMulCovolumeRpow
import BuildAid.ForwardExisting

section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.MinkowskiProductBounds

open Module Submodule

theorem mink {W V ι : Type} [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fintype ι] (b : Basis ι ℝ W) (e : W ≃ₗ[ℝ] V)
    (Δ ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, ∀ T : W →ₗ[ℝ] W, LinearMap.det T ≠ 0 →
      |LinearMap.det T| ≤ Δ → (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → ε ≤ ‖e (T x)‖) →
      ∃ v : Basis (Fin (finrank ℝ V)) ℝ W, ∀ i, v i ∈ span ℤ (Set.range b) ∧ ‖e (T (v i))‖ ≤ C := by
  classical
  borelize V
  have : FiniteDimensional ℝ W := Module.Finite.of_basis b
  let b0 := b.map e
  let c0 := MeasureTheory.volume.real (ZSpan.fundamentalDomain b0)
  have hc0 : 0 ≤ c0 := MeasureTheory.measureReal_nonneg
  refine ⟨(finrank ℝ V : ℝ) ^ ((finrank ℝ V : ℝ) / 2) * (Δ * c0) / ε ^ (finrank ℝ V - 1),
    fun T h0 hΔ hmin => ?_⟩
  let T' : W ≃ₗ[ℝ] W := LinearMap.equivOfDetNeZero T h0
  have hT' : ∀ x, T' x = T x := fun x => rfl
  let f := T'.trans e
  let b1 := b.map f
  let L := span ℤ (Set.range b1)
  have hL : ∀ y, y ∈ L ↔ f.symm y ∈ span ℤ (Set.range b) := by
    intro y
    rw [Basis.mem_span_iff_repr_mem, Basis.mem_span_iff_repr_mem]
    simp [b1]
  have hcov : ZLattice.covolume L = |LinearMap.det T| * c0 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b1 MeasureTheory.volume),
      ZSpan.measureReal_fundamentalDomain b1 MeasureTheory.volume b0]
    congr 2
    have : (b1 : ι → V) = e ∘ (T ∘ b) := by
      ext i; simp [b1, f, hT']
    rw [this, Basis.det_map]
    have h3 : (e.symm : V → W) ∘ e ∘ T ∘ b = T ∘ b := by ext i; simp
    rw [h3, Basis.det_comp, Basis.det_self, mul_one]
  obtain ⟨v, hv, hN⟩ := exists_basis_norm_eq_succMin L
  refine ⟨v.map f.symm, fun i => ⟨(hL _).1 (hv i), ?_⟩⟩
  have h1 : e (T (v.map f.symm i)) = v i := f.apply_symm_apply (v i)
  rw [h1, hN, le_div_iff₀ (by positivity)]
  have hne : L ≠ ⊥ := fun h => v.ne_zero i (by simpa [h] using hv i)
  have hm : ε ≤ minNorm L := le_minNorm hne fun y hy hy0 => by
    have := hmin _ ((hL y).1 hy) (by simpa using hy0)
    rwa [show e (T (f.symm y)) = y from f.apply_symm_apply y] at this
  have h2 := succMin_mul_minNorm_pow_le L (k := i + 1) (by omega) i.2
  refine le_trans ?_ (h2.trans ?_)
  · have := succMin_nonneg L (i + 1)
    gcongr
  · rw [hcov]; gcongr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}

theorem prod_type {M : Type} [CommMonoid M] (h : IsType Ψ) (f : (E →+* ℂ) → M) :
    ∏ σ, f σ = ∏ τ : Ψ, (f τ.1 * f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  rw [Finset.prod_mul_distrib, Finset.prod_coe_sort Ψ f,
    Finset.prod_coe_sort Ψ fun τ => f (ComplexEmbedding.conjugate τ),
    ← Finset.prod_mul_prod_compl Ψ f]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simpa using (h a).1 ha
  · intro a ha
    have := h a
    simp only [Finset.mem_compl] at ha
    tauto
  · intro a _; exact star_star a
  · intro a _; exact star_star a
  · intro a _; rfl

theorem one_le_prod (h : IsType Ψ) {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) :
    1 ≤ ∏ τ : Ψ, ‖τ.1 a‖ := by
  have h1 : (1 : ℝ) ≤ ∏ σ : E →+* ℂ, ‖σ a‖ := by
    have h2 := Algebra.norm_eq_prod_embeddings ℚ ℂ a
    have h3 : ∏ σ : E →+* ℂ, σ a = ∏ σ : E →ₐ[ℚ] ℂ, σ a :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl
    rw [← norm_prod, h3, ← h2]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ ha)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact h0 (by simpa using hz.symm)
    rw [← hz]
    simp only [eq_intCast, map_intCast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hz0
  rw [prod_type h] at h1
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, Finset.prod_mul_distrib] at h1
  have : 0 ≤ ∏ τ : Ψ, ‖τ.1 a‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  nlinarith

theorem card_type (h : IsType Ψ) : finrank ℚ E = Ψ.card * 2 := by
  have := prod_type (M := Multiplicative ℕ) h fun _ => Multiplicative.ofAdd 1
  rw [← Embeddings.card E ℂ]
  have h2 := congrArg Multiplicative.toAdd this
  simpa using h2

theorem basis_one (h : IsType Ψ) : ∃ b : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (Ψ → ℂ),
    ∀ x, x ∈ span ℤ (Set.range b) ↔ ∃ a : E, IsIntegral ℤ a ∧ x = fun τ => τ.1 a := by
  classical
  let u : Free.ChooseBasisIndex ℤ (𝓞 E) → Ψ → ℂ := fun j τ => τ.1 (integralBasis E j)
  have hli : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent
      (fun j => (c j : ℂ)) ?_ j
    · exact_mod_cast h1
    have key : ∀ τ ∈ Ψ, ∑ j, (c j : ℂ) * τ (integralBasis E j) = 0 := fun τ hτ => by
      simpa [u] using congrFun hc ⟨τ, hτ⟩
    ext σ
    simp only [canonicalEmbedding.latticeBasis_apply, Finset.sum_apply, Pi.smul_apply,
      canonicalEmbedding.apply_at, smul_eq_mul, Pi.zero_apply]
    by_cases hσ : σ ∈ Ψ
    · exact key σ hσ
    · have h2 : ComplexEmbedding.conjugate σ ∈ Ψ := by
        have := h σ; tauto
      have := congrArg conj (key _ h2)
      simpa using this
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℝ (Ψ → ℂ) := by
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, card_type h,
      Module.finrank_pi_fintype]
    simp
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' u hli hcard, fun x => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  let φ : E →ₗ[ℤ] (Ψ → ℂ) := (AddMonoidHom.pi fun τ : Ψ => τ.1.toAddMonoidHom).toIntLinearMap
  have : Set.range u = φ '' Set.range (integralBasis E) := by
    rw [← Set.range_comp]; rfl
  rw [this, span_image, Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨z, rfl⟩ := (mem_span_integralBasis E).1 ha
    exact ⟨_, z.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (mem_span_integralBasis E).2 ⟨⟨a, ha⟩, rfl⟩, rfl⟩

theorem basis_many (h : IsType Ψ) (m : ℕ) :
    ∃ b : Basis (Σ _ : Fin m, Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (Ψ → Fin m → ℂ),
    ∀ x, x ∈ span ℤ (Set.range b) ↔
      ∃ v : Fin m → E, (∀ a, IsIntegral ℤ (v a)) ∧ x = fun τ a => τ.1 (v a) := by
  obtain ⟨b, hb⟩ := basis_one h
  let e : (Fin m → Ψ → ℂ) ≃ₗ[ℝ] (Ψ → Fin m → ℂ) :=
    { toFun := fun x τ a => x a τ, invFun := fun x a τ => x τ a, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  refine ⟨(Pi.basis fun _ => b).map e, fun x => ?_⟩
  have : x ∈ span ℤ (Set.range ((Pi.basis fun _ : Fin m => b).map e)) ↔
      ∀ a, (fun τ => x τ a) ∈ span ℤ (Set.range b) := by
    simp only [Basis.mem_span_iff_repr_mem, Sigma.forall]
    rfl
  rw [this]
  simp only [hb]
  constructor
  · intro hx
    choose v hv hx using hx
    exact ⟨v, hv, by ext τ a; exact congrFun (hx a) τ⟩
  · rintro ⟨v, hv, rfl⟩ a
    exact ⟨v a, hv a, rfl⟩

theorem fac {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef) :
    ∃ B : Matrix (Fin m) (Fin m) ℂ, H = B * Bᴴ ∧ (∀ x y : Fin m → ℂ, x ⬝ᵥ H *ᵥ star y =
      inner ℂ (WithLp.toLp 2 (y ᵥ* B)) (WithLp.toLp 2 (x ᵥ* B))) ∧
      ∀ x : Fin m → ℂ, (x ⬝ᵥ H *ᵥ star x).re = ‖WithLp.toLp 2 (x ᵥ* B)‖ ^ 2 := by
  open MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hH.posSemidef.nonneg
  have h1 : H = Bᴴ * Bᴴᴴ := by simpa [star_eq_conjTranspose] using hB
  have h2 : ∀ x y : Fin m → ℂ, x ⬝ᵥ H *ᵥ star y =
      inner ℂ (WithLp.toLp 2 (y ᵥ* Bᴴ)) (WithLp.toLp 2 (x ᵥ* Bᴴ)) := by
    intro x y
    rw [EuclideanSpace.inner_toLp_toLp, h1, ← mulVec_mulVec, dotProduct_mulVec, star_vecMul]
  refine ⟨Bᴴ, h1, h2, fun x => ?_⟩
  rw [h2, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

theorem hval_eq {m : ℕ} (H : CM Ψ m m) (τ : Ψ) (v : Fin m → E) :
    hval Ψ H τ v = ((fun a => τ.1 (v a)) ⬝ᵥ H τ *ᵥ star fun a => τ.1 (v a)).re := rfl

theorem short (h : IsType Ψ) (m : ℕ) (Δ ε : ℝ) (hε : 0 < ε) : ∃ (n : ℕ) (C : ℝ),
    ∀ H : CM Ψ m m, (∀ τ, (H τ).PosDef) → ∏ τ, ‖(H τ).det‖ ≤ Δ →
    (∀ v : Fin m → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) → ε ≤ ∑ τ, hval Ψ H τ v) →
    ∃ V : Matrix (Fin n) (Fin m) E, IntM V ∧ (∃ S : Matrix (Fin m) (Fin n) E, S * V = 1) ∧
      ∀ i τ, hval Ψ H τ (V i) ≤ C := by
  classical
  obtain ⟨b, hb⟩ := basis_many h m
  let e : (Ψ → Fin m → ℂ) ≃ₗ[ℝ] PiLp 2 (fun _ : Ψ => EuclideanSpace ℂ (Fin m)) :=
    (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv 2 ℝ (Fin m → ℂ)).symm).trans
      (WithLp.linearEquiv 2 ℝ _).symm
  have he : ∀ x, ‖e x‖ ^ 2 = ∑ τ, ‖WithLp.toLp 2 (x τ)‖ ^ 2 := fun x =>
    PiLp.norm_sq_eq_of_L2 _ _
  obtain ⟨C, hC⟩ := mink b e Δ (√ε) (Real.sqrt_pos.2 hε)
  refine ⟨finrank ℝ (PiLp 2 fun _ : Ψ => EuclideanSpace ℂ (Fin m)), C ^ 2,
    fun H hH hΔ hmin => ?_⟩
  choose B hB1 hB2 hB3 using fun τ => fac (hH τ)
  let T : (Ψ → Fin m → ℂ) →ₗ[ℝ] (Ψ → Fin m → ℂ) := LinearMap.pi fun τ =>
    ((Matrix.toLin' (B τ)ᵀ).restrictScalars ℝ).comp (LinearMap.proj τ)
  have hT : ∀ x τ, T x τ = x τ ᵥ* B τ := fun x τ => by simp [T, mulVec_transpose]
  have hdet : LinearMap.det T = ∏ τ, ‖(H τ).det‖ := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_toLin',
      det_transpose, hB1 τ, det_mul, det_conjTranspose, norm_mul, norm_star, Complex.normSq_eq_norm_sq,
      sq]
  have hq : ∀ v : Fin m → E, ‖e (T fun τ a => τ.1 (v a))‖ ^ 2 = ∑ τ, hval Ψ H τ v := by
    intro v
    rw [he]
    exact Finset.sum_congr rfl fun τ _ => by rw [hT, hval_eq, hB3]
  obtain ⟨v, hv⟩ := hC T
    (by rw [hdet]; exact Finset.prod_ne_zero_iff.2 fun τ _ => norm_ne_zero_iff.2 (hH τ).det_pos.ne')
    (by rwa [hdet, abs_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)])
    (by
      intro x hx h0
      obtain ⟨w, hw, rfl⟩ := (hb x).1 hx
      rw [Real.sqrt_le_left (norm_nonneg _), hq]
      exact hmin w (by rintro rfl; exact h0 (by ext; simp)) hw)
  choose w hw hvw using fun i => (hb _).1 (hv i).1
  refine ⟨Matrix.of w, fun i a => hw i a, ?_, fun i τ => ?_⟩
  · have hinj : LinearMap.ker (Matrix.toLin' (Matrix.of w)) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro c hc
      obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
      obtain ⟨τ⟩ : Nonempty Ψ := by
        by_cases hσ : σ ∈ Ψ
        · exact ⟨⟨σ, hσ⟩⟩
        · exact ⟨⟨ComplexEmbedding.conjugate σ, by have := h σ; tauto⟩⟩
      let l : (Ψ → Fin m → ℂ) →ₗ[ℝ] ℂ :=
        { toFun := fun x => ∑ a, x τ a * τ.1 (c a)
          map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }
      have hl : l = 0 := v.ext fun i => by
        have := congrArg τ.1 (congrFun hc i)
        rw [hvw i]
        simpa [l, mulVec, dotProduct] using this
      ext a
      have := LinearMap.congr_fun hl fun _ => Pi.single a 1
      simpa [l, Pi.single_apply] using this
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
    refine ⟨LinearMap.toMatrix' g, ?_⟩
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  · have h1 := (hv i).2
    rw [hvw i] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [hq] at h2
    refine le_trans ?_ h2
    exact Finset.single_le_sum (f := fun τ => hval Ψ H τ (w i))
      (fun τ _ => by rw [hval_eq, hB3]; positivity) (Finset.mem_univ τ)

theorem gram_le {m : ℕ} {H G : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef) (hG : Gᴴ = G)
    (h0 : G.det ≠ 0) (hm : H * G⁻¹ * H = G) (x y : Fin m → ℂ) {C : ℝ}
    (hx : (x ⬝ᵥ H *ᵥ star x).re ≤ C) (hy : (y ⬝ᵥ H *ᵥ star y).re ≤ C) :
    ‖x ⬝ᵥ G *ᵥ star y‖ ≤ C := by
  obtain ⟨B, -, h2, h3⟩ := fac hH
  have hG' : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hG]
  have h4' : ∀ y, x ⬝ᵥ G *ᵥ y = (x ᵥ* (H * G⁻¹)) ⬝ᵥ H *ᵥ y := fun y => by
    rw [← dotProduct_mulVec, mulVec_mulVec, hm]
  have h5 : (x ᵥ* (H * G⁻¹)) ⬝ᵥ H *ᵥ star (x ᵥ* (H * G⁻¹)) = x ⬝ᵥ H *ᵥ star x := by
    rw [← h4', star_vecMul, mulVec_mulVec, conjTranspose_mul, hG', hH.1.eq,
      mul_nonsing_inv_cancel_left _ _ h0.isUnit]
  rw [← h5, h3] at hx
  rw [h3] at hy
  rw [h4', h2]
  refine (norm_inner_le_norm _ _).trans ?_
  nlinarith [sq_nonneg (‖WithLp.toLp 2 (y ᵥ* B)‖ - ‖WithLp.toLp 2 ((x ᵥ* (H * G⁻¹)) ᵥ* B)‖)]

theorem comb_le {m n : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef)
    (x : Fin n → Fin m → ℂ) (t : Fin n → ℂ) {C M : ℝ}
    (hx : ∀ j, (x j ⬝ᵥ H *ᵥ star (x j)).re ≤ C) (ht : ∀ j, ‖t j‖ ≤ M) :
    ((∑ j, t j • x j) ⬝ᵥ H *ᵥ star (∑ j, t j • x j)).re ≤ (n * (M * √C)) ^ 2 := by
  obtain ⟨B, -, -, h3⟩ := fac hH
  rw [h3]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have : WithLp.toLp 2 ((∑ j, t j • x j) ᵥ* B) = ∑ j, t j • WithLp.toLp 2 (x j ᵥ* B) := by
    simp [sum_vecMul, smul_vecMul]
  rw [this]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (M * √C) fun j _ => ?_).trans
    (by simp))
  rw [norm_smul]
  have h4 := hx j
  rw [h3] at h4
  exact mul_le_mul (ht j) (Real.le_sqrt_of_sq_le h4) (norm_nonneg _) ((norm_nonneg _).trans (ht j))

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem ccT_mul {α β γ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β γ E) :
    ccT (A * B) = ccT B * ccT A := by
  ext i j
  simp [ccT, cc, Matrix.mul_apply, mul_comm]

theorem ccT_smul {α β : Type} (k : ℤ) (A : Matrix α β E) :
    ccT ((k : E) • A) = (k : E) • ccT A := by
  ext i j
  simp [ccT, cc]

theorem ccT_one {α : Type} [DecidableEq α] : ccT (1 : Matrix α α E) = 1 := by
  ext i j
  simp [ccT, cc, Matrix.one_apply, apply_ite, eq_comm]

omit [NumberField E] [IsCMField E] in
theorem intM_mul {α β γ : Type} [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A)
    (hB : IntM B) : IntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun k _ => (hA i k).mul (hB k j)

theorem intM_ccT {α β : Type} {A : Matrix α β E} (hA : IntM A) : IntM (ccT A) := fun i j =>
  (hA j i).map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom

omit [NumberField E] [IsCMField E] in
theorem li_of_mul {k a b : ℕ} {A : Matrix (Fin k) (Fin a) E} {R : Matrix (Fin a) (Fin b) E}
    (h : LinearIndependent E fun i => (A * R) i) : LinearIndependent E fun i => A i :=
  LinearIndependent.of_comp (Matrix.vecMulLinear R) h

theorem det_le (h : IsType Ψ) {m D : ℕ} (hD : 0 < D) {G : Matrix (Fin m) (Fin m) E}
    {H : CM Ψ m m} (h0 : G.det ≠ 0) (hG : Den D G⁻¹) (hH : IsMaj Ψ G H) :
    ∏ τ, ‖(H τ).det‖ ≤ ∏ _τ : Ψ, (D : ℝ) ^ m := by
  have ha : IsIntegral ℤ ((D : E) • G⁻¹).det := IsIntegral.det hG
  have hd : ((D : E) • G⁻¹).det = (D : E) ^ m * (G.det)⁻¹ := by simp
  have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have h1 := one_le_prod h ha (by rw [hd]; exact mul_ne_zero (pow_ne_zero _ hD') (inv_ne_zero h0))
  refine (le_mul_of_one_le_right (Finset.prod_nonneg fun _ _ => norm_nonneg _) h1).trans_eq ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h2 := congrArg (fun A => ‖Matrix.det A‖) (hH τ).2
  have h3 : (G.map τ.1).det = τ.1 G.det := (RingHom.map_det _ _).symm
  have h4 : 0 < ‖τ.1 G.det‖ := by simpa using h0
  simp only [det_mul, det_nonsing_inv, Ring.inverse_eq_inv', h3, norm_mul, norm_inv] at h2
  have h5 : ‖(H τ).det‖ = ‖τ.1 G.det‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) h4.le]
    field_simp at h2
    exact h2
  rw [hd, h5]
  simp only [map_mul, map_pow, map_natCast, map_inv₀, norm_mul, norm_pow, norm_inv,
    Complex.norm_natCast]
  field_simp

def IsoRows' {k n : ℕ} (Γ : Matrix (Fin n) (Fin n) E) (T : Matrix (Fin k) (Fin n) E) : Prop :=
  LinearIndependent E (fun i => (T * Γ) i) ∧ T * Γ * ccT T = 0

theorem exists_int_rows {N m n D : ℕ} (hD : 0 < D) {G : Matrix (Fin m) (Fin m) E} (h0 : G.det ≠ 0)
    {W : Matrix (Fin N) (Fin m) E} (hW : IsoRows G W) {V : Matrix (Fin n) (Fin m) E}
    {S : Matrix (Fin m) (Fin n) E} (hS : S * V = 1) :
    ∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' (V * ((D : E) • G) * ccT V) T := by
  classical
  obtain ⟨k, hk, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin N × Fin n => (W * S) p.1 p.2)
  have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
  have h1 : ((k : E) • (W * S)) * V = (k : E) • W := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, hS, Matrix.mul_one]
  have h2 : ccT V * ccT S = 1 := by rw [← ccT_mul, hS, ccT_one]
  refine ⟨(k : E) • (W * S), fun i j => ?_, ?_, ?_⟩
  · simpa using hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  · refine li_of_mul (R := ((k : E)⁻¹ * (D : E)⁻¹) • (ccT S * G⁻¹)) ?_
    have : (k : E) • (W * S) * (V * ((D : E) • G) * ccT V) *
        ((k : E)⁻¹ * (D : E)⁻¹) • (ccT S * G⁻¹) = W := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (ccT V), h2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.one_mul,
        mul_nonsing_inv_cancel_right _ _ h0.isUnit]
      rw [show (k : E)⁻¹ * (D : E)⁻¹ * (D * k) = 1 by field_simp, one_smul]
    rw [this]
    exact hW.1
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (ccT V), ← ccT_mul, h1, ccT_smul]
    simp [hW.2]

end GlobalTheory.SW.MinkowskiProductBounds

open GlobalTheory.SW.MinkowskiProductBounds in

theorem GlobalTheory.SW.exists_shortIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N D : ℕ) (ε : ℝ), 0 < D → 0 < ε →
    ∃ C : ℝ, ShortIso Ψ N D ε C := by
  intro E _ _ _ Ψ h N D ε hD hε
  classical
  obtain ⟨n, C, hC⟩ := short h (2 * N) (∏ _τ : Ψ, (D : ℝ) ^ (2 * N)) ε hε
  let F : Set (Matrix (Fin n) (Fin n) E) :=
    {Γ | ∀ i j, Γ i j ∈ {x : E | IsIntegral ℤ x ∧ ∀ σ : E →+* ℂ, ‖σ x‖ ≤ D * C}}
  have hF : F.Finite :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => Embeddings.finite_of_norm_le E ℂ _
  have hex : ∀ Γ : Matrix (Fin n) (Fin n) E, ∃ T : Matrix (Fin N) (Fin n) E,
      (∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' Γ T) → IntM T ∧ IsoRows' Γ T := by
    intro Γ
    by_cases hΓ : ∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' Γ T
    · exact ⟨hΓ.choose, fun _ => hΓ.choose_spec⟩
    · exact ⟨0, fun h => absurd h hΓ⟩
  choose T hT using hex
  obtain ⟨M, hM⟩ := ((hF.prod (Set.finite_univ (α := Ψ × Fin N × Fin n))).image
    fun p => ‖p.2.1.1 (T p.1 p.2.2.1 p.2.2.2)‖).bddAbove
  refine ⟨(n * (M * √C)) ^ 2, fun G H hG h0 hD1 hD2 ⟨W, hW⟩ hH hmin => ?_⟩
  obtain ⟨V, hV, ⟨S, hS⟩, hVC⟩ := hC H (fun τ => (hH τ).1) (det_le h hD h0 hD2 hH) hmin
  set Γ := V * ((D : E) • G) * ccT V with hΓ
  have hΓF : Γ ∈ F := by
    intro i j
    refine ⟨intM_mul (intM_mul hV hD1) (intM_ccT hV) i j, ?_⟩
    have key : ∀ τ : Ψ, ‖τ.1 (Γ i j)‖ ≤ D * C := by
      intro τ
      have h1 : (G.map τ.1)ᴴ = G.map τ.1 := by
        ext a b
        have := congrArg τ.1 (congrFun (congrFun hG a) b)
        simpa [ccT, emb_cc] using this
      have h2 : (G.map τ.1).det ≠ 0 := by
        rw [show (G.map τ.1).det = τ.1 G.det from (RingHom.map_det _ _).symm]
        simpa using h0
      have h3 := gram_le (hH τ).1 h1 h2 (hH τ).2 _ _ (hVC i τ) (hVC j τ)
      have h4 : τ.1 (Γ i j) = D * ((fun a => τ.1 (V i a)) ⬝ᵥ G.map τ.1 *ᵥ
          star fun a => τ.1 (V j a)) := by
        rw [hΓ, Matrix.mul_assoc]
        simp [Matrix.mul_apply, ccT, emb_cc, dotProduct, mulVec, Finset.mul_sum, mul_assoc,
          mul_left_comm]
      rw [h4, norm_mul, Complex.norm_natCast]
      gcongr
    intro σ
    by_cases hσ : σ ∈ Ψ
    · exact key ⟨σ, hσ⟩
    · simpa using key ⟨ComplexEmbedding.conjugate σ, by have := h σ; tauto⟩
  obtain ⟨hT1, hT2, hT3⟩ := hT Γ (exists_int_rows hD h0 hW hS)
  refine ⟨T Γ * V, intM_mul hT1 hV, ⟨?_, ?_⟩, fun i τ => ?_⟩
  · refine li_of_mul (R := ((D : E) • G) * ccT V) ?_
    rwa [Matrix.mul_assoc, ← Matrix.mul_assoc V]
  · have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
    refine (smul_eq_zero_iff_right hD').1 ?_
    rw [← hT3, ccT_mul]
    simp only [hΓ, Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  · have h1 : (fun a => τ.1 ((T Γ * V) i a)) = ∑ j, τ.1 (T Γ i j) • fun a => τ.1 (V j a) := by
      ext a
      simp [Matrix.mul_apply]
    rw [hval_eq, h1]
    exact comb_le (hH τ).1 _ _ (fun j => hVC j τ) fun j =>
      hM ⟨(Γ, τ, i, j), ⟨hΓF, trivial⟩, rfl⟩
end

section
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.ShortStep

open MinkowskiProductBounds

theorem quot_maj {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G H : Matrix n n ℂ} {V w : Matrix (Fin 1) n ℂ} {B : Matrix m n ℂ} {S : Matrix n m ℂ}
    (hG : Gᴴ = G) (h0 : G.det ≠ 0) (hH : H.PosDef) (hm : H * G⁻¹ * H = G)
    (hw : V * G * wᴴ = 1) (hV : V * G * Vᴴ = 0) (hB : B * G * Vᴴ = 0)
    (hS : S * B = 1 - G * wᴴ * V - G * Vᴴ * w) (hd : (B * G * Bᴴ).det ≠ 0) :
    ∃ L : Matrix m (Fin 1) ℂ, ((B - L * V) * H * (B - L * V)ᴴ).PosDef ∧
      (B - L * V) * H * (B - L * V)ᴴ * (B * G * Bᴴ)⁻¹ * ((B - L * V) * H * (B - L * V)ᴴ) =
        B * G * Bᴴ := by
  have inj : ∀ {k : Type} [Fintype k] [DecidableEq k] (A : Matrix k n ℂ) (R : Matrix n k ℂ),
      A * R = 1 → Function.Injective A.vecMul := fun A R h x y e => by
    have := congrArg (fun z => z ᵥ* R) e
    simpa [vecMul_vecMul, h] using this
  have hh : (V * H * Vᴴ).PosDef :=
    hH.mul_mul_conjTranspose_same (inj V (G * wᴴ) (by rw [← Matrix.mul_assoc, hw]))
  have hu : IsUnit (V * H * Vᴴ).det := hh.det_pos.ne'.isUnit
  refine ⟨B * H * Vᴴ * (V * H * Vᴴ)⁻¹, ?_⟩
  generalize hL : B * H * Vᴴ * (V * H * Vᴴ)⁻¹ = L
  have e1 : (B - L * V) * H * Vᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc L, Matrix.mul_assoc L, ← hL,
      nonsing_inv_mul_cancel_right _ _ hu, sub_self]
  have e2 : (B - L * V) * G * Vᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc L, Matrix.mul_assoc L, hB, hV]; simp
  have hB' : V * G * Bᴴ = 0 := by
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose hB
  have e3 : (B - L * V) * G * (B - L * V)ᴴ = B * G * Bᴴ := by
    rw [conjTranspose_sub, conjTranspose_mul, Matrix.mul_sub, ← Matrix.mul_assoc, e2,
      Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc L, Matrix.mul_assoc L, hB']
    simp
  have e4 : S * (B - L * V) = 1 - (G * wᴴ + S * L) * V - G * Vᴴ * w := by
    rw [Matrix.mul_sub, hS, Matrix.add_mul, Matrix.mul_assoc S]; abel
  generalize B - L * V = P at e1 e2 e3 e4
  refine ⟨hH.mul_mul_conjTranspose_same (inj P (G * Pᴴ * (B * G * Bᴴ)⁻¹) ?_), ?_⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e3, mul_nonsing_inv _ hd.isUnit]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = P * H * G⁻¹ := ⟨_, rfl⟩
  have y1 : Y * G = P * H := by rw [hY, nonsing_inv_mul_cancel_right _ _ h0.isUnit]
  have y2 : Y * H = P * G := by
    rw [hY]; conv_rhs => rw [← hm]
    simp only [Matrix.mul_assoc]
  have y3 : Y * S * P = Y - Y * (G * wᴴ + S * L) * V := by
    rw [Matrix.mul_assoc, e4, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc Y (G * Vᴴ),
      ← Matrix.mul_assoc Y G, y1, e1, Matrix.mul_assoc]
    simp
  have y4 : Y * (G * wᴴ + S * L) = 0 := by
    have := congrArg (fun Z => Z * H * Vᴴ * (V * H * Vᴴ)⁻¹) y3
    simp only [Matrix.sub_mul] at this
    rw [y2, e2, Matrix.mul_assoc _ P, Matrix.mul_assoc _ (P * H), e1, Matrix.mul_assoc _ V,
      Matrix.mul_assoc _ (V * H), mul_nonsing_inv_cancel_right _ _ hu] at this
    simpa using this
  rw [y4, Matrix.zero_mul, sub_zero] at y3
  have y5 : P * H * Pᴴ = Y * S * (B * G * Bᴴ) := by
    rw [← e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, y3, y1]
  nth_rewrite 1 [y5]
  rw [mul_nonsing_inv_cancel_right _ _ hd.isUnit, ← Matrix.mul_assoc, ← Matrix.mul_assoc, y3, y2, e3]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}

theorem exists_close (h : IsType Ψ) : ∃ C : ℝ, ∀ x : Ψ → ℂ, ∃ a : E, IsIntegral ℤ a ∧
    ∀ τ : Ψ, ‖τ.1 a + x τ‖ ≤ C := by
  obtain ⟨b, hb⟩ := basis_one h
  refine ⟨∑ i, ‖b i‖, fun x => ?_⟩
  obtain ⟨a, ha, e⟩ := (hb _).1 (ZSpan.floor b x).2
  refine ⟨-a, ha.neg, fun τ => le_trans ?_ (ZSpan.norm_fract_le b x)⟩
  refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ τ)
  rw [ZSpan.fract_apply, e]
  simp [neg_add_eq_sub]

theorem quot_iso {N : ℕ} {n m : ℕ} {G : Matrix (Fin n) (Fin n) E} {V w : Matrix (Fin 1) (Fin n) E}
    {B : Matrix (Fin m) (Fin n) E} {S : Matrix (Fin n) (Fin m) E} (hG : Gᴴ = G)
    (hV : V * G * Vᴴ = 0) (hB : B * G * Vᴴ = 0)
    (hS : S * B = 1 - G * wᴴ * V - G * Vᴴ * w) {W : Matrix (Fin (N + 1)) (Fin n) E}
    (hW : IsoRows G W) : ∃ T : Matrix (Fin N) (Fin m) E, IsoRows (B * G * Bᴴ) T := by
  classical
  have hiso : W * G * Wᴴ = 0 := hW.2
  have hWi := Matrix.vecMul_injective_iff.2 hW.1
  have key : ∃ z : Matrix (Fin 1) (Fin n) E, ∀ t : Fin (N + 1) → E, t ᵥ* (W * G * zᴴ) = 0 →
      t ᵥ* (W * G * Vᴴ) = 0 ∧ (t ᵥ* (W * S) = 0 → t = 0) := by
    have main : ∀ t : Fin (N + 1) → E, t ᵥ* (W * G * Vᴴ) = 0 → t ᵥ* (W * S) = 0 →
        t ᵥ* W = (t ᵥ* (W * G * wᴴ)) ᵥ* V := fun t h1 h2 => by
      have h3 : W * S * B = W - W * G * wᴴ * V - W * G * Vᴴ * w := by
        rw [Matrix.mul_assoc, hS]; simp [Matrix.mul_sub, Matrix.mul_assoc]
      have := congrArg (fun Z => t ᵥ* Z) h3
      simp only [vecMul_sub] at this
      rw [← vecMul_vecMul t (W * S), h2, ← vecMul_vecMul t (W * G * Vᴴ), h1,
        ← vecMul_vecMul t (W * G * wᴴ)] at this
      simp only [zero_vecMul, sub_zero] at this
      exact sub_eq_zero.1 this.symm
    by_cases hv : ∃ s : Matrix (Fin 1) (Fin (N + 1)) E, s * W = V
    · obtain ⟨s, rfl⟩ := hv
      have h1 : W * G * (s * W)ᴴ = 0 := by
        rw [conjTranspose_mul, ← Matrix.mul_assoc, hiso, Matrix.zero_mul]
      refine ⟨w, fun t ht => ⟨by rw [h1, vecMul_zero], fun h2 => hWi ?_⟩⟩
      have := main t (by rw [h1, vecMul_zero]) h2
      simpa [ht] using this
    · refine ⟨V, fun t ht => ⟨ht, fun h2 => hWi ?_⟩⟩
      have h3 := main t ht h2
      generalize t ᵥ* (W * G * wᴴ) = α at h3
      by_cases hα : α 0 = 0
      · have : α = 0 := by ext i; rw [Subsingleton.elim i 0]; exact hα
        simpa [this] using h3
      · refine (hv ⟨Matrix.of fun _ => (α 0)⁻¹ • t, ?_⟩).elim
        ext i j
        have := congrFun h3 j
        rw [Subsingleton.elim i 0]
        change (((α 0)⁻¹ • t) ᵥ* W) j = _
        rw [smul_vecMul, Pi.smul_apply, this]
        simp [vecMul, dotProduct, hα]
  obtain ⟨z, hz⟩ := key
  have hr : N ≤ Module.finrank E (LinearMap.ker (W * G * zᴴ).vecMulLinear) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (W * G * zᴴ).vecMulLinear
    have h2 := Submodule.finrank_le (LinearMap.range (W * G * zᴴ).vecMulLinear)
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank hr
  have hu' := hu.map' _ (Submodule.ker_subtype _)
  let U : Matrix (Fin N) (Fin (N + 1)) E := Matrix.of fun i => (u i).1
  have hUi : Function.Injective U.vecMul := Matrix.vecMul_injective_iff.2 hu'
  have hU : U * (W * G * zᴴ) = 0 := by ext i j; exact congrFun (u i).2 j
  have hUV : U * (W * G * Vᴴ) = 0 := by ext i j; exact congrFun (hz _ (u i).2).1 j
  refine ⟨U * (W * S), Matrix.vecMul_injective_iff.1 ?_, ?_⟩
  · change Function.Injective (U * (W * S)).vecMulLinear
    rw [injective_iff_map_eq_zero]
    intro c hc
    refine hUi ?_
    have := (hz (c ᵥ* U) (by rw [vecMul_vecMul, hU, vecMul_zero])).2
      (by rw [vecMul_vecMul]; exact hc)
    simpa using this
  · have h3 : U * (W * S) * B = U * W - U * W * G * wᴴ * V := by
      have : U * (W * (G * (Vᴴ * w))) = 0 := by
        simpa [Matrix.mul_assoc] using congrArg (fun Z => Z * w) hUV
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hS]; simp [Matrix.mul_sub, Matrix.mul_assoc, this]
    have h4 : U * (W * S) * B * G * Vᴴ = 0 := by
      rw [Matrix.mul_assoc _ B, Matrix.mul_assoc _ (B * G), hB, Matrix.mul_zero]
    have h5 : V * G * (U * W)ᴴ = 0 := by
      simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose hUV
    have h6 : U * W * G * (U * W)ᴴ = 0 := by
      rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc U, Matrix.mul_assoc U, hiso]; simp
    have h7 : U * (W * S) * (B * G * Bᴴ) * (U * (W * S))ᴴ =
        U * (W * S) * B * G * (U * (W * S) * B)ᴴ := by
      rw [conjTranspose_mul _ B]; simp only [Matrix.mul_assoc]
    refine h7.trans ?_
    nth_rewrite 2 [h3]
    rw [conjTranspose_sub, conjTranspose_mul _ V, Matrix.mul_sub, ← Matrix.mul_assoc _ Vᴴ, h4, h3,
      Matrix.sub_mul, Matrix.sub_mul, h6, Matrix.mul_assoc _ V, Matrix.mul_assoc _ (V * G), h5]
    simp

omit [IsCMField E] in
theorem den_mul {α β γ : Type} [Fintype β] {a b : ℕ} {A : Matrix α β E} {B : Matrix β γ E}
    (hA : Den a A) (hB : Den b B) : Den (a * b) (A * B) := by
  have := intM_mul hA hB
  rwa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Nat.cast_mul] at this

omit [IsCMField E] in
theorem den_one {α β : Type} {A : Matrix α β E} (hA : IntM A) : Den 1 A := by
  simpa [Den] using hA

omit [IsCMField E] in
theorem den_dvd {α β : Type} {a b : ℕ} {A : Matrix α β E} (hA : Den a A) (h : a ∣ b) :
    Den b A := by
  obtain ⟨c, rfl⟩ := h
  have := RowExt.intM_nat c hA
  rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this

omit [IsCMField E] in
theorem den_sub {α β : Type} {a : ℕ} {A B : Matrix α β E} (hA : Den a A) (hB : Den a B) :
    Den a (A - B) := fun i j => by
  rw [smul_sub]; exact (hA i j).sub (hB i j)

theorem den_conj {α β : Type} {a : ℕ} {A : Matrix α β E} (hA : Den a A) : Den a Aᴴ := by
  have := RowExt.intM_conj hA
  rwa [conjTranspose_smul, star_natCast] at this

omit [IsCMField E] in
theorem den_inv_smul {α β : Type} {a c : ℕ} (hc : 0 < c) {A : Matrix α β E} (hA : Den a A) :
    Den (a * c) ((c : E)⁻¹ • A) := by
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  unfold Den
  rwa [smul_smul, Nat.cast_mul, mul_inv_cancel_right₀ hc0]

theorem exists_dual {n D c : ℕ} (hc : 0 < c) {G : Matrix (Fin n) (Fin n) E}
    {V : Matrix (Fin 1) (Fin n) E} {X : Matrix (Fin n) (Fin 1) E} (hG : Gᴴ = G) (h0 : G.det ≠ 0)
    (hD1 : Den D G) (hD2 : Den D G⁻¹) (hVi : IntM V) (hX : IntM X) (hVX : V * X = (c : E) • 1)
    (hV : V * G * Vᴴ = 0) : ∃ w : Matrix (Fin 1) (Fin n) E, Den (D * c * D * (D * c) * 2) w ∧
      V * G * wᴴ = 1 ∧ w * G * Vᴴ = 1 ∧ w * G * wᴴ = 0 := by
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  obtain ⟨u, hu⟩ : ∃ u, u = ((c : E)⁻¹ • (G⁻¹ * X))ᴴ := ⟨_, rfl⟩
  have hud : Den (D * c) u := by
    have := den_conj (den_inv_smul hc (den_mul hD2 (den_one hX)))
    rwa [mul_one, ← hu] at this
  have h1 : V * G * uᴴ = 1 := by
    rw [hu, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ h0.isUnit, hVX, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 : u * G * Vᴴ = 1 := by
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose h1
  obtain ⟨s, hs⟩ : ∃ s, s = ((2 : ℕ) : E)⁻¹ • (u * G * uᴴ) := ⟨_, rfl⟩
  have hsc : sᴴ = s := by
    simp [hs, conjTranspose_mul, hG, Matrix.mul_assoc]
  have hsd : Den (D * c * D * (D * c) * 2) s :=
    hs ▸ den_inv_smul two_pos (den_mul (den_mul hud hD1) (den_conj hud))
  have h3 : (u - s * V) * G * Vᴴ = 1 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, h2, Matrix.mul_assoc s, Matrix.mul_assoc s, hV]; simp
  refine ⟨u - s * V, den_sub (den_dvd hud ⟨D * (D * c) * 2, by ring⟩)
    (by simpa using den_mul hsd (den_one hVi)), ?_, h3, ?_⟩
  · simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose h3
  · rw [conjTranspose_sub, conjTranspose_mul, Matrix.mul_sub, ← Matrix.mul_assoc, h3, hsc,
      Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc s, Matrix.mul_assoc s, h1,
      Matrix.mul_one, Matrix.one_mul, hs, sub_sub, ← add_smul]
    norm_num

omit [NumberField E] [IsCMField E] in
theorem li_of_mul' {m n : ℕ} {B : Matrix (Fin m) (Fin n) E} (h : LinearIndependent E fun i => B i)
    {k : E} (hk : k ≠ 0) : LinearIndependent E fun i => (k • B) i := by
  refine li_of_mul (R := k⁻¹ • (1 : Matrix (Fin n) (Fin n) E)) ?_
  rwa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hk, one_smul, Matrix.mul_one]

omit [IsCMField E] in

theorem exists_span {n m : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (hn : n = m + Fintype.card κ) (R : Matrix κ (Fin n) E) (F : Matrix (Fin n) κ E)
    (h : R * F = 1) : ∃ (B : Matrix (Fin m) (Fin n) E) (S : Matrix (Fin n) (Fin m) E), IntM B ∧
      LinearIndependent E (fun i => B i) ∧ B * F = 0 ∧ S * B = 1 - F * R := by
  classical
  have hsurj : LinearMap.range F.vecMulLinear = ⊤ :=
    LinearMap.range_eq_top.2 fun y => ⟨y ᵥ* R, by simp [vecMul_vecMul, h]⟩
  have hr : Module.finrank E (LinearMap.ker F.vecMulLinear) = m := by
    have h1 := LinearMap.finrank_range_add_finrank_ker F.vecMulLinear
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at h1
    omega
  have hP : (1 - F * R) * F = 0 := by rw [Matrix.sub_mul, Matrix.mul_assoc, h]; simp
  generalize 1 - F * R = P at hP
  have hmem : ∀ i, P i ∈ LinearMap.ker F.vecMulLinear := fun i =>
    LinearMap.mem_ker.2 (congrFun hP i)
  have hker : ∀ x ∈ LinearMap.ker F.vecMulLinear, x ᵥ* F = 0 := fun x hx => LinearMap.mem_ker.1 hx
  generalize LinearMap.ker F.vecMulLinear = K at hr hmem hker
  let b := Module.finBasisOfFinrankEq E K hr
  let B : Matrix (Fin m) (Fin n) E := Matrix.of fun i => (b i).1
  have hBi : LinearIndependent E (fun i => B i) := by
    have := b.linearIndependent.map' K.subtype K.ker_subtype
    exact this
  have hBF : B * F = 0 := by ext i j; exact congrFun (hker _ (b i).2) j
  have hSB : (Matrix.of fun i j => b.repr ⟨_, hmem i⟩ j) * B = P := by
    ext i j
    have := congrFun (congrArg Subtype.val (b.sum_repr ⟨_, hmem i⟩)) j
    rw [Submodule.coe_sum, Finset.sum_apply] at this
    exact this
  generalize (Matrix.of fun i j => b.repr ⟨_, hmem i⟩ j) = S at hSB
  clear_value B
  obtain ⟨k, hk, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin m × Fin n => B p.1 p.2)
  have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
  refine ⟨(k : E) • B, (k : E)⁻¹ • S, fun i j => ?_, ?_,
    by rw [Matrix.smul_mul, hBF, smul_zero], ?_⟩
  · simpa using hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  · refine li_of_mul' hBi hk'
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hk', one_smul, hSB]

theorem exists_compl (m D b : ℕ) (hD : 0 < D) (hb : 0 < b) : ∃ D' : ℕ, 0 < D' ∧
    ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) E) (V w : Matrix (Fin 1) (Fin n) E), n = m + 2 →
    Gᴴ = G → G.det ≠ 0 → Den D G → Den D G⁻¹ → IntM V → Den b w → V * G * Vᴴ = 0 →
    V * G * wᴴ = 1 → w * G * Vᴴ = 1 → w * G * wᴴ = 0 →
    ∃ (B : Matrix (Fin m) (Fin n) E) (S : Matrix (Fin n) (Fin m) E), IntM B ∧ V * S = 0 ∧
      B * S = 1 ∧ B * G * Vᴴ = 0 ∧ S * B = 1 - G * wᴴ * V - G * Vᴴ * w ∧
      (B * G * Bᴴ).det ≠ 0 ∧ Den D' (B * G * Bᴴ) ∧ Den D' (B * G * Bᴴ)⁻¹ := by
  obtain ⟨c, C, hc, hprim⟩ := exists_nearly_primitive E m
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨D * b * c * D * (D * b * c), by positivity,
    fun n G V w hn hG h0 hD1 hD2 hVi hw h1 h2 h3 h4 => ?_⟩
  obtain ⟨B₀, S₀, hB₀, hli, hBF, hSB⟩ := exists_span (E := E) (m := m) (by simpa using hn)
    (fromRows V w) (fromCols (G * wᴴ) (G * Vᴴ)) (by
      rw [fromRows_mul_fromCols]
      simp only [← Matrix.mul_assoc, h1, h2, h3, h4, fromBlocks_one])
  rw [fromCols_mul_fromRows, ← sub_sub] at hSB
  obtain ⟨a, ha, -, hBi, hpr⟩ := hprim _ B₀ hB₀ hli
  have hBF' : a * B₀ * fromCols (G * wᴴ) (G * Vᴴ) = 0 := by
    rw [Matrix.mul_assoc, hBF, Matrix.mul_zero]
  have hli' : LinearIndependent E fun i => (a * B₀) i := by
    refine Matrix.vecMul_injective_iff.1 fun x y e => ?_
    refine Matrix.vecMul_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det a).2 ha.isUnit) ?_
    refine Matrix.vecMul_injective_iff.2 hli ?_
    simpa [vecMul_vecMul] using e
  have hSB' : S₀ * a⁻¹ * (a * B₀) = 1 - G * wᴴ * V - G * Vᴴ * w := by
    rw [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ ha.isUnit, hSB]
  generalize a * B₀ = B at hBi hpr hBF' hli' hSB'
  generalize S₀ * a⁻¹ = S at hSB'
  obtain ⟨X, hX, hBX⟩ := RowExt.exists_right_inv (c : E) B hBi hli' hpr
  rw [mul_fromCols, ← fromCols_zero] at hBF'
  obtain ⟨e1, e2⟩ := (fromCols_ext_iff _ _ _ _).1 hBF'
  obtain ⟨P, hP⟩ : ∃ P, P = 1 - G * wᴴ * V - G * Vᴴ * w := ⟨_, rfl⟩
  have hPd : Den (D * b) P := by
    rw [hP]
    refine den_sub (den_sub (den_dvd (den_one fun i j => ?_) (one_dvd _)) ?_) ?_
    · rw [Matrix.one_apply]; split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · simpa using den_mul (den_mul hD1 (den_conj hw)) (den_one hVi)
    · simpa using den_mul (den_mul hD1 (den_conj (den_one hVi))) hw
  have hBP : B * P = B := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc B (G * wᴴ),
      ← Matrix.mul_assoc B (G * Vᴴ), e1, e2]; simp
  have hVP : V * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, h1, h2]; simp
  have hPG : G * Pᴴ = P * G := by
    simp [hP, conjTranspose_mul, hG, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, sub_right_comm]
  rw [← hP] at hSB'
  have hS : S = (c : E)⁻¹ • (P * X) := by
    rw [← hSB', Matrix.mul_assoc, hBX]; simp [smul_smul, hc0]
  have hSd : Den (D * b * c) S := by
    have := den_inv_smul hc (den_mul hPd (den_one hX))
    rwa [mul_one, ← hS] at this
  have hBS : B * S = 1 := by
    rw [hS, Matrix.mul_smul, ← Matrix.mul_assoc, hBP, hBX]; simp [smul_smul, hc0]
  have hinv : B * G * Bᴴ * (Sᴴ * G⁻¹ * S) = 1 := by
    have : B * G * Bᴴ * (Sᴴ * G⁻¹ * S) = B * (G * (S * B)ᴴ) * G⁻¹ * S := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hSB', hPG, ← Matrix.mul_assoc, hBP, mul_nonsing_inv_cancel_right _ _ h0.isUnit, hBS]
  refine ⟨B, S, hBi, ?_, hBS, by rw [Matrix.mul_assoc, e2], by rw [hSB', hP],
    (isUnit_det_of_right_inverse hinv).ne_zero, ?_, ?_⟩
  · rw [hS, Matrix.mul_smul, ← Matrix.mul_assoc, hVP]; simp
  · exact den_dvd (den_mul (den_mul (den_one hBi) hD1) (den_conj (den_one hBi)))
      ⟨b * c * D * (D * b * c), by ring⟩
  · rw [inv_eq_right_inv hinv]
    exact den_mul (den_mul (den_conj hSd) hD2) hSd

theorem map_conj {α β : Type} (τ : E →+* ℂ) (A : Matrix α β E) : Aᴴ.map τ = (A.map τ)ᴴ :=
  Base.ccT_map τ A

omit [IsCMField E] in
theorem det_map_ne {α : Type} [Fintype α] [DecidableEq α] (τ : E →+* ℂ) {A : Matrix α α E}
    (h : A.det ≠ 0) : (A.map τ).det ≠ 0 := by
  rw [show (A.map τ).det = τ A.det from (RingHom.map_det _ _).symm]
  simpa using h

theorem map_proj {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (V w : Matrix (Fin 1) (Fin n) E) : (1 - G * wᴴ * V - G * Vᴴ * w).map τ =
      1 - G.map τ * (w.map τ)ᴴ * V.map τ - G.map τ * (V.map τ)ᴴ * w.map τ := by
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_mul, map_conj, map_conj, Matrix.map_one _ (map_zero _) (map_one _)]

theorem iso_of_short (h : IsType Ψ) {n D : ℕ} (hD : 0 < D) {G : Matrix (Fin n) (Fin n) E}
    {H : CM Ψ n n} (hG : Gᴴ = G) (h0 : G.det ≠ 0) (hD1 : Den D G) (hH : IsMaj Ψ G H)
    {V : Matrix (Fin 1) (Fin n) E} (hV : IntM V) (hs : ∀ τ, hval Ψ H τ (V 0) < 1 / D) :
    V * G * Vᴴ = 0 := by
  have hi := den_mul (den_mul (den_one hV) hD1) (den_conj (den_one hV)) 0 0
  have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hD'' : (0 : ℝ) < D := by exact_mod_cast hD
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  by_contra hne
  simp only [one_mul, mul_one, Matrix.smul_apply, smul_eq_mul] at hi
  have hne' := mul_ne_zero hD' hne
  have h1 := one_le_prod h hi hne'
  have hΨ : Nonempty Ψ := by
    have := card_type h
    have h2 := Module.finrank_pos (R := ℚ) (M := E)
    exact (Finset.card_pos.1 (by omega)).to_subtype
  have h2 : ∏ τ : Ψ, ‖τ.1 (D * (V * G * Vᴴ) 0 0)‖ < ∏ _τ : Ψ, (1 : ℝ) := by
    refine Finset.prod_lt_prod_of_nonempty (fun τ _ => norm_pos_iff.2 ((_root_.map_ne_zero _).2 hne')) (fun τ _ => ?_)
      Finset.univ_nonempty
    have h3 := gram_le (hH τ).1 (by rw [← map_conj, hG]) (det_map_ne τ.1 h0) (hH τ).2 _ _
      (le_of_eq (hval_eq H τ (V 0)).symm) (le_of_eq (hval_eq H τ (V 0)).symm)
    have h4 : τ.1 ((V * G * Vᴴ) 0 0) = ((fun a => τ.1 (V 0 a)) ⬝ᵥ G.map τ.1 *ᵥ
        star fun a => τ.1 (V 0 a)) := by
      rw [← Matrix.map_apply (f := τ.1), Matrix.map_mul, Matrix.map_mul, map_conj, Matrix.mul_assoc]
      rfl
    rw [map_mul, norm_mul, h4, map_natCast, Complex.norm_natCast]
    have := h3.trans_lt (hs τ)
    rwa [lt_div_iff₀' hD''] at this
  rw [Finset.prod_const_one] at h2
  exact absurd h1 h2.not_ge

theorem lift_le {n m : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (V : Matrix (Fin 1) (Fin n) ℂ) (B : Matrix (Fin m) (Fin n) ℂ) (L : Matrix (Fin m) (Fin 1) ℂ)
    (t : Fin m → ℂ) (α : ℂ) {C M : ℝ} (hM : 1 ≤ M) (h1 : (V 0 ⬝ᵥ H *ᵥ star (V 0)).re ≤ C)
    (h2 : (t ⬝ᵥ ((B - L * V) * H * (B - L * V)ᴴ) *ᵥ star t).re ≤ C)
    (h3 : ‖α + (t ᵥ* L) 0‖ ≤ M) :
    ((t ᵥ* B + α • V 0) ⬝ᵥ H *ᵥ star (t ᵥ* B + α • V 0)).re ≤ (2 * (M * √C)) ^ 2 := by
  have e : t ᵥ* B + α • V 0 = ∑ j, ![1, α + (t ᵥ* L) 0] j • ![t ᵥ* (B - L * V), V 0] j := by
    have : (t ᵥ* L) ᵥ* V = (t ᵥ* L) 0 • V 0 := by
      ext j; simp [vecMul, dotProduct]
    rw [Fin.sum_univ_two, vecMul_sub, ← vecMul_vecMul, this]
    simp [add_smul]
  rw [e]
  refine comb_le hH _ _ (fun j => ?_) fun j => ?_
  · fin_cases j
    · rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_vecMul] at h2
      exact h2
    · exact h1
  · fin_cases j
    · simpa using hM
    · exact h3

end GlobalTheory.SW.ShortStep

open GlobalTheory.SW.MinkowskiProductBounds GlobalTheory.SW.ShortStep in

theorem GlobalTheory.SW.shortIso_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, (∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C) → (∀ (D : ℕ) (ε : ℝ), 0 < D → 0 < ε → ∃ C : ℝ, ShortIso Ψ (N + 1) D ε C) → ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ (N + 1) D 0 C := by
  intro E _ _ _ Ψ h N ih hth D hD
  classical
  obtain ⟨C₀, hC₀⟩ := hth D (1 / D) hD (by positivity)
  obtain ⟨c, C₁, hc, hprim⟩ := exists_nearly_primitive E 1
  obtain ⟨D', hD', hcompl⟩ := exists_compl (E := E) (2 * N) D (D * c * D * (D * c) * 2) hD
    (by positivity)
  obtain ⟨C₂, hC₂⟩ := ih D' hD'
  obtain ⟨C₃, hC₃⟩ := exists_close h
  set C₄ := max (((1 : ℕ) * (C₁ * √(1 / D))) ^ 2) C₂ with hC₄
  refine ⟨max (max C₀ C₄) ((2 * (max 1 C₃ * √C₄)) ^ 2),
    fun G H hG h0 hD1 hD2 ⟨W, hW⟩ hH _ => ?_⟩
  by_cases hmin : ∀ v : Fin (2 * (N + 1)) → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) →
      1 / (D : ℝ) ≤ ∑ τ, hval Ψ H τ v
  · obtain ⟨W', h1, h2, h3⟩ := hC₀ G H hG h0 hD1 hD2 ⟨W, hW⟩ hH hmin
    exact ⟨W', h1, h2, fun i τ => (h3 i τ).trans ((le_max_left _ _).trans (le_max_left _ _))⟩
  push Not at hmin
  obtain ⟨v, hv0, hvi, hvs⟩ := hmin
  have hG' : Gᴴ = G := hG
  have hnn : ∀ {k : ℕ} {K : CM Ψ k k}, (∀ τ, (K τ).PosDef) → ∀ τ x, 0 ≤ hval Ψ K τ x := by
    intro k K hK τ x
    obtain ⟨B, -, -, h3⟩ := fac (hK τ)
    rw [hval_eq, h3]; positivity
  let V₀ : Matrix (Fin 1) (Fin (2 * (N + 1))) E := Matrix.of fun _ => v
  have hs : ∀ τ, hval Ψ H τ (V₀ 0) < 1 / D := fun τ =>
    (Finset.single_le_sum (f := fun τ => hval Ψ H τ v)
      (fun τ _ => hnn (fun τ => (hH τ).1) τ v) (Finset.mem_univ τ)).trans_lt hvs
  have hV₀ := iso_of_short h hD hG' h0 hD1 hH (V := V₀) (fun _ a => hvi a) hs
  obtain ⟨a, ha, haC, hVi, hpr⟩ := hprim _ V₀ (fun _ a => hvi a)
    (linearIndependent_unique_iff.2 hv0)
  have hV : a * V₀ * G * (a * V₀)ᴴ = 0 := by
    rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc a, Matrix.mul_assoc a, hV₀]; simp
  have hVne : (a * V₀) 0 ≠ 0 := by
    rw [det_fin_one] at ha
    have : (a * V₀) 0 = a 0 0 • v := by ext j; simp [Matrix.mul_apply, V₀]
    rw [this]
    exact smul_ne_zero ha hv0
  have hVC : ∀ τ, hval Ψ H τ ((a * V₀) 0) ≤ C₄ := fun τ => by
    have h1 : (fun j => τ.1 ((a * V₀) 0 j)) = ∑ j, τ.1 (a 0 j) • fun b => τ.1 (V₀ j b) := by
      ext j
      simp [Matrix.mul_apply]
    rw [hval_eq, h1]
    exact (comb_le (hH τ).1 _ _ (fun j => (hs τ).le) fun j => haC _ _ _).trans (le_max_left _ _)
  generalize a * V₀ = V at hVi hpr hV hVne hVC
  obtain ⟨X, hX, hVX⟩ := RowExt.exists_right_inv (c : E) V hVi
    (linearIndependent_unique_iff.2 hVne) hpr
  obtain ⟨w, hw, w1, w2, w3⟩ := exists_dual hc hG' h0 hD1 hD2 hVi hX hVX hV
  obtain ⟨B, S, hBi, hVS, hBS, hBV, hSB, hd, d1, d2⟩ :=
    hcompl _ G V w (by ring) hG' h0 hD1 hD2 hVi hw hV w1 w2 w3
  have hq := fun τ : Ψ => quot_maj (G := G.map τ.1) (H := H τ) (V := V.map τ.1) (w := w.map τ.1)
    (B := B.map τ.1) (S := S.map τ.1) (by rw [← map_conj, hG']) (det_map_ne τ.1 h0) (hH τ).1
    (hH τ).2
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul, w1,
      Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul, hV, Matrix.map_zero _ (map_zero _)])
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul, hBV, Matrix.map_zero _ (map_zero _)])
    (by rw [← Matrix.map_mul, hSB, map_proj])
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul]; exact det_map_ne τ.1 hd)
  choose L hL1 hL2 using hq
  obtain ⟨T, hTi, ⟨hT1, hT2⟩, hTC⟩ := hC₂ (B * G * Bᴴ)
    (fun τ => (B.map τ.1 - L τ * V.map τ.1) * H τ * (B.map τ.1 - L τ * V.map τ.1)ᴴ)
    (by
      rw [RowExt.ccT_eq, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG',
        Matrix.mul_assoc])
    hd d1 d2 (quot_iso hG' hV hBV hSB hW)
    (fun τ => ⟨hL1 τ, by rw [Matrix.map_mul, Matrix.map_mul, map_conj]; exact hL2 τ⟩)
    (fun x _ _ => Finset.sum_nonneg fun τ _ => hnn hL1 τ x)
  choose α hα hαC using fun i => hC₃ fun τ => ((fun j => τ.1 (T i j)) ᵥ* L τ) 0
  let T' : Matrix (Fin (N + 1)) (Fin (2 * N)) E := Matrix.of (Fin.cons 0 fun i => T i)
  let A : Matrix (Fin (N + 1)) (Fin 1) E := Matrix.of (Fin.cons 1 fun i _ => α i)
  have r0 : (T' * B + A * V) 0 = V 0 := by
    ext j; simp [T', A, Matrix.mul_apply]
  have r1 : ∀ i : Fin N, (T' * B + A * V) i.succ = T i ᵥ* B + α i • V 0 := fun i => by
    ext j; simp [T', A, Matrix.mul_apply, vecMul, dotProduct]
  refine ⟨T' * B + A * V, fun i j => ?_, ⟨?_, ?_⟩, fun i τ => ?_⟩
  · refine (intM_mul (A := T') (fun i j => ?_) hBi i j).add
      (intM_mul (A := A) (fun i j => ?_) hVi i j)
    · cases i using Fin.cases
      · exact isIntegral_zero
      · exact hTi _ _
    · cases i using Fin.cases
      · exact isIntegral_one
      · exact hα _
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ, r0] at hg
    simp only [r1] at hg
    have hVS' : V 0 ᵥ* S = 0 := congrFun hVS 0
    have h1 := congrArg (fun x => x ᵥ* S) hg
    simp only [add_vecMul, sum_vecMul, smul_vecMul, vecMul_vecMul, hBS, hVS', vecMul_one,
      smul_zero, add_zero, zero_add, zero_vecMul] at h1
    have h2 := Fintype.linearIndependent_iff.1 hT1 _ h1
    simp only [h2, zero_smul, Finset.sum_const_zero, add_zero] at hg
    intro i
    cases i using Fin.cases
    · exact (smul_eq_zero.1 hg).resolve_right hVne
    · exact h2 _
  · have hVB : V * G * Bᴴ = 0 := by
      simpa [conjTranspose_mul, hG', Matrix.mul_assoc] using congrArg conjTranspose hBV
    have h1 : T' * (B * G * Bᴴ) * T'ᴴ = 0 := by
      generalize B * G * Bᴴ = G' at hT2
      ext i j
      cases i using Fin.cases
      · simp [T', Matrix.mul_apply]
      cases j using Fin.cases
      · simp [T', Matrix.mul_apply]
      · exact congrFun (congrFun hT2 _) _
    have h2 : (T' * B + A * V) * G * (T' * B + A * V)ᴴ = T' * (B * G * Bᴴ) * T'ᴴ +
        T' * (B * G * Vᴴ) * Aᴴ + A * (V * G * Bᴴ) * T'ᴴ + A * (V * G * Vᴴ) * Aᴴ := by
      simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_assoc]
      abel
    refine h2.trans ?_
    rw [h1, hBV, hVB, hV]; simp
  · cases i using Fin.cases with
    | zero => rw [r0]; exact (hVC τ).trans ((le_max_right _ _).trans (le_max_left _ _))
    | succ i =>
      refine le_trans ?_ (le_max_right _ _)
      have e : (fun j => τ.1 ((T i ᵥ* B + α i • V 0) j)) =
          (fun j => τ.1 (T i j)) ᵥ* B.map τ.1 + τ.1 (α i) • V.map τ.1 0 := by
        ext j; simp [vecMul, dotProduct]
      rw [r1, hval_eq, e]
      exact lift_le (hH τ).1 _ _ (L τ) _ _ (le_max_left _ _) (hVC τ)
        ((hTC i τ).trans (le_max_right _ _)) ((hαC i τ).trans (le_max_right _ _))
end

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortIsotropicVectorsExistence_succ_of_very_short_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, (∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C) → (∀ (D : ℕ) (ε : ℝ), 0 < D → 0 < ε → ∃ C : ℝ, ShortIso Ψ (N + 1) D ε C) → ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ (N + 1) D 0 C := by
  atlas_forward_decl GlobalTheory.SW.shortIso_step
end

section
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.Reduct

section Cplx
variable {N : ℕ}

theorem le_trace {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.PosSemidef) {T : ℝ}
    (hT : M.trace.re ≤ T) : ((T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M).PosSemidef := by
  have hs := hM.1.spectral_theorem
  have ht := hM.1.trace_eq_sum_eigenvalues
  set U : Matrix (Fin N) (Fin N) ℂ := (hM.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hU
  have hUU : U * Uᴴ = 1 := (Unitary.coe_mul_star_self hM.1.eigenvectorUnitary)
  have hs' : M = U * diagonal (fun i => (hM.1.eigenvalues i : ℂ)) * Uᴴ := hs
  have e : (T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M =
      U * diagonal (fun i => ((T - hM.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have : diagonal (fun i => ((T - hM.1.eigenvalues i : ℝ) : ℂ)) =
        (T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - diagonal (fun i => (hM.1.eigenvalues i : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hs', Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hUU]
  rw [e]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ U
  refine Matrix.PosSemidef.diagonal fun i => ?_
  have h1 : hM.1.eigenvalues i ≤ ∑ j, hM.1.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)
  have h2 : M.trace.re = ∑ j, hM.1.eigenvalues j := by
    rw [ht]; simp
  simp only [Pi.zero_apply]
  exact_mod_cast (by linarith : 0 ≤ T - hM.1.eigenvalues i)

theorem ge_of_inv_le {Y M : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosSemidef) (hM : Mᴴ = M)
    (h : Y * M = 1) {T : ℝ} (hT : 0 < T)
    (hle : ((T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M).PosSemidef) :
    (Y - ((T⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
  have h' : M * Y = 1 := mul_eq_one_comm.1 h
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have p1 := hY.conjTranspose_mul_mul_same (1 - ((T⁻¹ : ℝ) : ℂ) • M)
  have p2 := hle.smul (a := ((T⁻¹ ^ 2 : ℝ) : ℂ)) (by exact_mod_cast sq_nonneg T⁻¹)
  convert p1.add p2 using 1
  have hc : star ((T⁻¹ : ℝ) : ℂ) = ((T⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hM, hc]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, h, h', smul_sub, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem exists_maj {Z : Matrix (Fin N) (Fin N) ℂ} (hZ : (imH Z).PosDef) :
    let H := fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) * (imH Z)⁻¹ * (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ + I • Matrix.J (Fin N) ℂ
    H.PosDef ∧ H * (I • Matrix.J (Fin N) ℂ) * H = I • Matrix.J (Fin N) ℂ := by
  intro H
  set Y := imH Z with hY
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hZ.isUnit
  have h1 : Y * Y⁻¹ = 1 := mul_nonsing_inv _ hu
  have h2 : Y⁻¹ * Y = 1 := nonsing_inv_mul _ hu
  have hd : Z = Zᴴ + (2 * I) • Y := by
    rw [hY, imH, smul_smul, mul_inv_cancel₀ (by simp), one_smul]; abel
  have hJ : (I • Matrix.J (Fin N) ℂ) * (I • Matrix.J (Fin N) ℂ) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.J_squared]; simp
  have hP : (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ * (I • Matrix.J (Fin N) ℂ) * fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) = (-2 : ℂ) • Y := by
    rw [Matrix.mul_smul, Matrix.smul_mul, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.J, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, Matrix.mul_one, conjTranspose_one, zero_add, Matrix.one_mul,
      Matrix.mul_neg, add_zero]
    have : Z + -Zᴴ = (2 * I) • Y := by nth_rewrite 1 [hd]; abel
    rw [this, smul_smul]
    congr 1
    linear_combination 2 * I_mul_I
  have hH : H * (I • Matrix.J (Fin N) ℂ) * H = I • Matrix.J (Fin N) ℂ := by
    simp only [H]
    generalize I • Matrix.J (Fin N) ℂ = G at hJ hP ⊢
    generalize fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) = P at hP ⊢
    have e : P * Y⁻¹ * Pᴴ * G * (P * Y⁻¹ * Pᴴ) = (-2 : ℂ) • (P * Y⁻¹ * Pᴴ) := by
      calc _ = P * Y⁻¹ * (Pᴴ * G * P) * Y⁻¹ * Pᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hP, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc P, h2,
            Matrix.mul_one]
    generalize P * Y⁻¹ * Pᴴ = K at e
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, e, Matrix.mul_assoc, hJ, Matrix.one_mul,
      Matrix.mul_one]
    module
  have hK : fromRows Zᴴ (1 : Matrix (Fin N) (Fin N) ℂ) * Y⁻¹ * (fromRows Zᴴ (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ =
      fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) * Y⁻¹ * (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ + (2 * I) • Matrix.J (Fin N) ℂ := by
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul Zᴴ _ Y⁻¹, fromRows_mul Z _ Y⁻¹,
      fromRows_mul_fromCols, fromRows_mul_fromCols, Matrix.J, fromBlocks_smul, fromBlocks_add,
      conjTranspose_conjTranspose, conjTranspose_one]
    generalize Zᴴ = W at hd
    rw [hd]
    congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, h1, h2, smul_zero, add_zero, smul_neg, add_neg_cancel_right, ← Matrix.mul_assoc Y]
  have hS : H.PosSemidef := by
    have p1 := hZ.inv.posSemidef.mul_mul_conjTranspose_same (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))
    have p2 := hZ.inv.posSemidef.mul_mul_conjTranspose_same (fromRows Zᴴ (1 : Matrix (Fin N) (Fin N) ℂ))
    have p3 := (p1.add p2).smul (a := (2⁻¹ : ℂ)) (by positivity)
    rw [hK] at p3
    refine (congrArg Matrix.PosSemidef ?_).mp p3
    simp only [H]; module
  refine ⟨?_, hH⟩
  refine hS.posDef_iff_isUnit.2 ?_
  have : H * ((I • Matrix.J (Fin N) ℂ) * H * (I • Matrix.J (Fin N) ℂ)) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hH, hJ]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse this)

end Cplx

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem shortIso_all {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N : ℕ) :
    ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C := by
  induction N with
  | zero =>
    intro D _
    refine ⟨0, fun G H _ _ _ _ hW _ _ => ?_⟩
    obtain ⟨W, hW⟩ := hW
    exact ⟨W, fun i => i.elim0, hW, fun i => i.elim0⟩
  | succ N ih =>
    exact GlobalTheory.T.shortIsotropicVectorsExistence_succ_of_very_short_step E Ψ hΨ N ih fun D ε hD hε => GlobalTheory.SW.exists_shortIso E Ψ hΨ (N + 1) D ε hD hε

theorem exists_imag : ∃ (ξ : E) (D : ℕ), ξ ≠ 0 ∧ cc ξ = -ξ ∧ 0 < D ∧ IsIntegral ℤ ((D : E) * ξ) ∧
    IsIntegral ℤ ((D : E) * ξ⁻¹) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, cc x ≠ x := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ ({x - cc x, (x - cc x)⁻¹} : Finset E)
  have key : ∀ t : E, IsIntegral ℤ (y • t) → IsIntegral ℤ ((y.natAbs : E) * t) := fun t ht => by
    rw [zsmul_eq_mul] at ht
    rcases Int.natAbs_eq y with e | e
    · rw [e] at ht; simpa using ht
    · rw [e] at ht; simpa using ht.neg
  refine ⟨x - cc x, y.natAbs, sub_ne_zero.2 hx.symm, by simp [cc], Int.natAbs_pos.2 hy,
    key _ (h _ (by simp)), key _ (h _ (by simp))⟩

omit [IsCMField E] in
theorem den_smul_J {N D : ℕ} {t : E} (h : IsIntegral ℤ ((D : E) * t)) :
    Den D (t • Matrix.J (Fin N) E) := by
  rintro (i | i) (j | j) <;> by_cases hij : i = j <;>
    simp [Matrix.J, Matrix.one_apply, hij, isIntegral_zero, h, h.neg]

omit [NumberField E] [IsCMField E] in
theorem map_J {N : ℕ} (τ : E →+* ℂ) : (Matrix.J (Fin N) E).map τ = Matrix.J (Fin N) ℂ := by
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [Matrix.J, Matrix.one_apply, hij]

omit [NumberField E] [IsCMField E] in
theorem li_submatrix {k α β : Type} (e : α ≃ β) {W : Matrix k β E}
    (h : LinearIndependent E fun i => W i) :
    LinearIndependent E fun i => W.submatrix id e i :=
  h.map' (LinearEquiv.funCongrLeft E E e).toLinearMap (LinearEquiv.ker _)

omit [NumberField E] [IsCMField E] in
theorem hval_eq {Ψ : Finset (E →+* ℂ)} {k m : ℕ} (H : CM Ψ m m) (τ : Ψ)
    (W : Matrix (Fin k) (Fin m) E) (i : Fin k) :
    hval Ψ H τ (W i) = ((W.map τ.1 * H τ * (W.map τ.1)ᴴ) i i).re := by
  rw [Matrix.mul_assoc]; rfl

theorem exists_rows {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Z ∈ Hn Ψ N, ∃ W : Matrix (Fin N) (Fin N ⊕ Fin N) E, IntM W ∧
      LinearIndependent E (fun i => W i) ∧ W * Matrix.J (Fin N) E * ccT W = 0 ∧
      ∀ τ : Ψ, (W.map τ.1 * (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) * (imH (Z τ))⁻¹ *
        (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (W.map τ.1)ᴴ).trace.re ≤ B := by
  obtain ⟨ξ, D, hξ, hc, hD, hi, hi'⟩ := exists_imag (E := E)
  obtain ⟨C, hC⟩ := shortIso_all hΨ N D hD
  let e : Fin (2 * N) ≃ Fin N ⊕ Fin N := (finCongr (two_mul N)).trans finSumFinEquiv.symm
  have ht : ∀ τ : E →+* ℂ, τ ξ = ((τ ξ).im : ℂ) * I := fun τ => by
    have h1 := Base.map_cc τ ξ
    rw [hc, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp only [neg_re, conj_re] at h2
    apply Complex.ext <;> simp
    linarith
  have ht0 : ∀ τ : E →+* ℂ, (τ ξ).im ≠ 0 := fun τ h => by
    have := ht τ
    rw [h] at this
    exact hξ (by simpa using this)
  refine ⟨∑ τ : Ψ, N * (|C| / |(τ.1 ξ).im|), by positivity, fun Z hZ => ?_⟩
  have hGi : (ξ • Matrix.J (Fin N) E)⁻¹ = (-ξ⁻¹) • Matrix.J (Fin N) E := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.J_squared]
    simp [hξ]
  have hGm : ∀ τ : E →+* ℂ, (ξ • Matrix.J (Fin N) E).map τ =
      ((τ ξ).im : ℂ) • (I • Matrix.J (Fin N) ℂ) := fun τ => by
    rw [smul_smul, ← ht, ← map_J τ]
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  let H0 : Ψ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ := fun τ =>
    fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) * (imH (Z τ))⁻¹ *
        (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ + I • Matrix.J (Fin N) ℂ
  let H : CM Ψ (2 * N) (2 * N) := fun τ => (((|(τ.1 ξ).im| : ℝ) : ℂ) • H0 τ).submatrix e e
  have hmaj : IsMaj Ψ ((ξ • Matrix.J (Fin N) E).submatrix e e) H := fun τ => by
    obtain ⟨p1, p2⟩ : (H0 τ).PosDef ∧ H0 τ * (I • Matrix.J (Fin N) ℂ) * H0 τ = _ :=
      exists_maj (hZ τ)
    refine ⟨(p1.smul (by exact_mod_cast abs_pos.2 (ht0 τ.1))).submatrix e.injective, ?_⟩
    have h0 : ((τ.1 ξ).im : ℂ) ≠ 0 := by exact_mod_cast ht0 τ.1
    have hinv : (((τ.1 ξ).im : ℂ) • (I • Matrix.J (Fin N) ℂ))⁻¹ =
        ((τ.1 ξ).im : ℂ)⁻¹ • (I • Matrix.J (Fin N) ℂ) := by
      apply Matrix.inv_eq_right_inv
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.J_squared]
      have : ((τ.1 ξ).im : ℂ)⁻¹ * I * ((τ.1 ξ).im * I) = -1 := by
        field_simp; simp
      rw [this]; simp
    simp only [H]
    rw [← Matrix.submatrix_map, hGm, Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hinv]
    congr 1
    generalize I • Matrix.J (Fin N) ℂ = G at p2 ⊢
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, p2]
    congr 1
    have : ((|(τ.1 ξ).im| : ℝ) : ℂ) * ((|(τ.1 ξ).im| : ℝ) : ℂ) = (τ.1 ξ).im * (τ.1 ξ).im := by
      exact_mod_cast abs_mul_abs_self _
    field_simp
    linear_combination this
  have iso : ∀ W : Matrix (Fin N) (Fin N ⊕ Fin N) E,
      W.submatrix id e * (ξ • Matrix.J (Fin N) E).submatrix e e * ccT (W.submatrix id e) =
        ξ • (W * Matrix.J (Fin N) E * ccT W) := fun W => by
    have : ccT (W.submatrix id e) = (ccT W).submatrix e id := rfl
    rw [this, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.submatrix_id_id]
  refine Exists.elim (hC ((ξ • Matrix.J (Fin N) E).submatrix e e) H ?_ ?_ ?_ ?_ ?_ hmaj ?_) ?_
  rotate_right
  · rintro W ⟨w1, ⟨w2, w3⟩, w4⟩
    have hW : W = (W.submatrix id e.symm).submatrix id e := by ext i j; simp
    have hli := li_submatrix e.symm w2
    have hint : IntM (W.submatrix id e.symm) := fun i j => w1 _ _
    generalize W.submatrix id e.symm = V at hW hli hint
    subst hW
    rw [iso, smul_eq_zero] at w3
    have w5 := w3.resolve_left hξ
    refine ⟨V, hint, hli, w5, fun τ => ?_⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ : Ψ => N * (|C| / |(τ.1 ξ).im|))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
    have w6 := congrArg (fun X => X.map τ.1) w5
    simp only [Matrix.map_mul, Base.ccT_map, map_J, Matrix.map_zero _ (map_zero τ.1)] at w6
    rw [Matrix.trace, Complex.re_sum]
    refine (Finset.sum_le_card_nsmul _ _ (|C| / |(τ.1 ξ).im|) fun i _ => ?_).trans (by simp)
    have w7 := w4 i τ
    rw [hval_eq] at w7
    simp only [H, H0] at w7
    rw [← Matrix.submatrix_map, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, w6, smul_zero, add_zero,
      Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul] at w7
    rw [le_div_iff₀' (abs_pos.2 (ht0 τ.1))]
    exact w7.trans (le_abs_self C)
  · have : ccT (ξ • Matrix.J (Fin N) E) = cc ξ • ccT (Matrix.J (Fin N) E) := by
      ext i j; simp [ccT, cc]
    change (ccT (ξ • Matrix.J (Fin N) E)).submatrix e e = _
    rw [this, hc, Base.ccT_J]; simp
  · rw [Matrix.det_submatrix_equiv_self, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ) (Matrix.isUnit_det_J _ _).ne_zero
  · exact fun i j => den_smul_J hi _ _
  · rw [Matrix.inv_submatrix_equiv, hGi]
    exact fun i j => den_smul_J (by simpa using hi'.neg) _ _
  · refine ⟨(fromCols (0 : Matrix (Fin N) (Fin N) E) (1 : Matrix (Fin N) (Fin N) E)).submatrix id e,
      li_submatrix e ?_, ?_⟩
    · have : LinearIndependent E fun i : Fin N ⊕ Fin N => (1 : M2 E N) i :=
        Matrix.linearIndependent_rows_iff_isUnit.2 isUnit_one
      convert this.comp Sum.inr Sum.inr_injective using 1
      ext i (j | j) <;> simp [Matrix.one_apply]
    · rw [iso]
      convert smul_zero ξ
      ext i j
      simp [ccT, cc, Matrix.J, Matrix.mul_apply, Matrix.one_apply]
  · intro v _ _
    refine Finset.sum_nonneg fun τ _ => ?_
    have := (hmaj τ).1.posSemidef.dotProduct_mulVec_nonneg (star fun a => τ.1 (v a))
    rw [star_star] at this
    exact (Complex.nonneg_iff.1 this).1

end GlobalTheory.SW.Reduct

open GlobalTheory.SW.Reduct in

theorem GlobalTheory.SW.exists_move_high : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, ∃ (c : ℕ) (δ : ℝ), 0 < c ∧ 0 < δ ∧ ∀ Z ∈ Hn Ψ N, ∃ γ ∈ UU E N, Den c γ ∧ hAct Ψ γ Z ∈ HnGe Ψ N δ := by
  intro E _ _ _ Ψ hΨ N
  obtain ⟨B, hB0, hB⟩ := exists_rows hΨ N
  obtain ⟨c, C, hc, hprim⟩ := GlobalTheory.SW.exists_nearly_primitive E N
  obtain ⟨c', hc', hext⟩ := GlobalTheory.SW.RowExt.exists_unitary_ext E N c hc
  have hT : 0 < B * (N * (N * C ^ 2)) + 1 := by positivity
  refine ⟨c', (B * (N * (N * C ^ 2)) + 1)⁻¹, hc', inv_pos.2 hT, fun Z hZ => ?_⟩
  obtain ⟨W, w1, w2, w3, w4⟩ := hB Z hZ
  obtain ⟨a, a1, a2, a3, a4⟩ := hprim _ W w1 w2
  have hli : LinearIndependent E fun i => (a * W) i := by
    refine Matrix.vecMul_injective_iff.1 fun x y hxy => ?_
    simp only [← Matrix.vecMul_vecMul] at hxy
    exact Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det a).2 (Ne.isUnit a1))
      (Matrix.vecMul_injective_iff.2 w2 hxy)
  obtain ⟨γ, hγ, hden, hrow⟩ := hext (a * W) a3 hli (by
    rw [Base.ccT_mul, Matrix.mul_assoc a, Matrix.mul_assoc a, ← Matrix.mul_assoc _ (ccT W), w3]
    simp) a4
  refine ⟨γ, hγ, hden, fun τ => ?_⟩
  obtain ⟨h1, h2, -⟩ := (GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  obtain ⟨hQ, -, -, hI⟩ := h1 τ
  have hQe : hDen Ψ γ Z τ =
      a.map τ.1 * (W.map τ.1 * fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    have : fromCols (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) = a.map τ.1 * W.map τ.1 := by
      rw [← Matrix.map_mul]
      ext i (j | j) <;> simp [← hrow, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
    rw [← Matrix.mul_assoc, ← this, fromCols_mul_fromRows, Matrix.mul_one, hDen]
  have hY := hZ τ
  have hM := w4 τ
  have hY' := h2 τ
  rw [show ∀ (V : Matrix (Fin N) (Fin N ⊕ Fin N) ℂ) (P : Matrix (Fin N ⊕ Fin N) (Fin N) ℂ)
      (Y : Matrix (Fin N) (Fin N) ℂ), V * (P * Y * Pᴴ) * Vᴴ = V * P * Y * (V * P)ᴴ from
    fun V P Y => by simp only [conjTranspose_mul, Matrix.mul_assoc]] at hM
  have ha : ∀ i j, ‖a.map τ.1 i j‖ ≤ C := a2 τ.1
  generalize W.map τ.1 * fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) = R at hQe hM
  generalize a.map τ.1 = A at hQe ha
  generalize hDen Ψ γ Z τ = Q at hQ hI hQe
  generalize imH (hAct Ψ γ Z τ) = Y' at hI hY' ⊢
  generalize imH (Z τ) = Y at hI hY hM
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit
  have hinv : Y' * (Q * Y⁻¹ * Qᴴ) = 1 := by
    have e : Y⁻¹ * (Qᴴ * Y' * Q) = 1 := by rw [hI]; exact nonsing_inv_mul _ hu
    rw [← Matrix.mul_assoc] at e
    have e' := mul_eq_one_comm.1 e
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at e'
    exact mul_eq_one_comm.1 e'
  refine ge_of_inv_le hY'.posSemidef (hY.inv.posSemidef.mul_mul_conjTranspose_same Q).1 hinv hT ?_
  have p1 := (le_trace (hY.inv.posSemidef.mul_mul_conjTranspose_same R) hM).mul_mul_conjTranspose_same A
  have htr : (A * Aᴴ).trace.re ≤ N * (N * C ^ 2) := by
    rw [Matrix.trace, Complex.re_sum]
    refine (Finset.sum_le_card_nsmul _ _ (N * C ^ 2) fun i _ => ?_).trans (by simp)
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    refine (Finset.sum_le_card_nsmul _ _ (C ^ 2) fun j _ => ?_).trans (by simp)
    rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
      Complex.ofReal_re]
    exact pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2
  have p2 := (le_trace (posSemidef_self_mul_conjTranspose A) htr).smul (a := (B : ℂ))
    (by exact_mod_cast hB0)
  refine (congrArg Matrix.PosSemidef ?_).mp ((p1.add p2).add Matrix.PosSemidef.one)
  subst hQe
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    conjTranspose_mul, Matrix.mul_assoc]
  push_cast
  module
end

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_move_hermitianHalfSpace_high : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, ∃ (c : ℕ) (δ : ℝ), 0 < c ∧ 0 < δ ∧ ∀ Z ∈ Hn Ψ N, ∃ γ ∈ UU E N, Den c γ ∧ hAct Ψ γ Z ∈ HnGe Ψ N δ := by
  atlas_forward_decl GlobalTheory.SW.exists_move_high
end
