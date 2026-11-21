import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCoverStatement

section
open NumberField GlobalTheory.AllWt Module TensorProduct Matrix GlobalTheory.SlopeExt
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SlopeGalois

theorem sum_dual_mul {K K' ι : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [Fintype ι] [DecidableEq ι] [DecidableEq (K' ≃ₐ[K] K')] (b : Basis ι ℚ K') (s : K' ≃ₐ[K] K') :
    ∑ r, s ((Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b r) * b r =
      if s = 1 then 1 else 0 := by
  classical
  set d := (Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b with hd
  let A : Matrix ι (K' →ₐ[ℚ] ℂ) ℂ := fun r ρ => ρ (d r)
  let B : Matrix (K' →ₐ[ℚ] ℂ) ι ℂ := fun ρ r => ρ (b r)
  have hAB : A * B = 1 := by
    ext r t
    rw [Matrix.mul_apply]
    have e : ∑ ρ : K' →ₐ[ℚ] ℂ, A r ρ * B ρ t = algebraMap ℚ ℂ (Algebra.trace ℚ K' (d r * b t)) := by
      rw [trace_eq_sum_embeddings]
      exact Finset.sum_congr rfl fun ρ _ => (map_mul ρ _ _).symm
    rw [e, ← Algebra.traceForm_apply, hd, LinearMap.BilinForm.apply_dualBasis_left, Matrix.one_apply]
    by_cases h : r = t
    · rw [if_pos h, if_pos h.symm, map_one]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have e : ι ≃ (K' →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis b, AlgHom.card])
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  let φ : K' →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ψ : K' →ₐ[ℚ] ℂ := φ.comp ((s : K' →+* K').toRatAlgHom)
  have key : φ (∑ r, s (d r) * b r) = (1 : Matrix (K' →ₐ[ℚ] ℂ) (K' →ₐ[ℚ] ℂ) ℂ) φ ψ := by
    rw [← hBA, Matrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [map_mul, mul_comm]; rfl
  apply φ.injective
  show φ _ = φ _
  rw [key]
  split_ifs with h
  · have : φ = ψ := by subst h; ext x; rfl
    rw [← this, Matrix.one_apply_eq, map_one]
  · rw [map_zero, Matrix.one_apply_ne]
    intro h'
    exact h (AlgEquiv.ext fun x => (φ.injective (AlgHom.congr_fun h' x)).symm)

theorem eq_sum_trace {K K' ι : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [IsGalois K K'] [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ K') (y : K') :
    ∑ r, algebraMap K K' (Algebra.trace K K'
      ((Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b r * y)) * b r = y := by
  classical
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  simp only [trace_eq_sum_automorphisms, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  have : ∀ s : K' ≃ₐ[K] K', ∑ r, s ((Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b r) * s y * b r
      = if s = 1 then y else 0 := fun s => by
    have h := sum_dual_mul b s
    simp only [mul_right_comm _ (s y), ← Finset.sum_mul, h]
    split_ifs with h1
    · simp [h1]
    · simp
  simp [this]


theorem gram_ge {K K' V V' ι κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [Field K']
    [NumberField K'] [StarRing K'] [Algebra K K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {b' : Basis κ K' V'} {X' : InfinitePlace K' → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K' →+* ℂ) → V' → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (φ : V →ₛₗ[algebraMap K K'] V') (ht : ∀ σ' x, N' σ' (φ x) = N (σ'.comp (algebraMap K K')) x)
    {j : ℕ} (e : Fin j → V) (w : InfinitePlace K') :
    (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤
      (Formalism.HN.gramPl b' X' w fun k => φ (e k)).det.re := by
  set σ := w.embedding.comp (algebraMap K K') with hσ
  have hv : w.comap (algebraMap K K') = InfinitePlace.mk σ := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  have hd : DenseRange σ := denseRange_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)
  have h1 : ∀ x : Fin j → K, N σ (∑ k, x k • e k) =
      1 * Formalism.HermitianLatticesTheory.cnorm (cols b' X' w (fun k => φ (e k)) *ᵥ fun k => σ (x k)) := fun x => by
    have h := ht w.embedding (∑ k, x k • e k)
    rw [← (hG' w).2, map_sum] at h
    simp only [map_smulₛₗ] at h
    rw [normAt_sum] at h
    rw [one_mul]
    exact h.symm
  rw [hv, gramPl_eq, gramPl_eq]
  refine le_of_le_of_eq ?_ (by rw [one_pow, one_mul] : (1 : ℝ) ^ (2 * j) * _ = _)
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · refine det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [this]
  · set B := cols b X (InfinitePlace.mk σ) e with hB
    have h2 : ((B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ)).det.re = (Bᴴ * B).det.re := by
      have : (B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (Bᴴ * B) := by
        ext a c
        simp [Matrix.mul_apply]
      rw [this, ← RingHom.map_det, Complex.conj_re]
    rw [← h2]
    refine det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [← hc]
    refine (this.trans ?_).symm
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.norm_conj]
    simp [Matrix.mulVec, dotProduct, hB]


end GlobalTheory.SlopeGalois
end
end

section
open NumberField GlobalTheory.AllWt Module TensorProduct Matrix GlobalTheory.SlopeExt GlobalTheory.SlopeGalois
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SlopeDifferent

theorem muDef_bot {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) :
    Formalism.HN.muDef b X (⊥ : Submodule (𝓞 K) V) = -Real.log 2 + Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ) := by
  have hz : Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = ⊥ := by
    unfold Formalism.HN.zl
    ext y
    simp
  unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope Formalism.F.rk
  rw [hz]
  simp

theorem slope_sq_bot {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {N : (K →+* ℂ) → V → ℝ} (hN : HasGram N) :
    slope_sq N (⊥ : Submodule (𝓞 K) V) = -Real.log 2 + Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  unfold slope_sq
  letI : StarRing K := starRingOfComm
  rw [dif_pos hN]
  exact muDef_bot _ _

theorem slope_sq_sub_le_of_different_smul {K K' V V' : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [Field K'] [NumberField K'] [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V']
    (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V)
    (M : Submodule (𝓞 K') V') (hGr : HasGram N) (hGr' : HasGram N')
    (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k)))
    (hM : M.FG) (hN : ∀ σ' x, N' σ' (ι x) = N (σ'.comp (algebraMap K K')) x) (hιM : ∀ x ∈ L, ι x ∈ M)
    (hDiff : ∀ δ ∈ differentIdeal ℤ (𝓞 K'), ∀ g ∈ M, δ • g ∈ Submodule.span (𝓞 K') (ι '' (L : Set V))) :
    slope_sq N' M - 2 * (Real.log |(discr K' : ℝ)| / Module.finrank ℚ K') ≤ slope_sq N L := by
  have hdisc : (discr K').natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero K')
  have hlogK : 0 ≤ Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
    have : 0 ≤ Real.log |(discr K : ℝ)| := by rw [Real.log_abs]; exact Real.log_intCast_nonneg _
    positivity
  have hlogK' : 0 ≤ Real.log |(discr K' : ℝ)| / (Module.finrank ℚ K' : ℝ) := by
    have : 0 ≤ Real.log |(discr K' : ℝ)| := by rw [Real.log_abs]; exact Real.log_intCast_nonneg _
    positivity
  by_cases h0 : M = ⊥
  · have hL0 : L = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : ι x ∈ M := hιM x hx
      rw [h0, Submodule.mem_bot] at h1
      rw [Submodule.mem_bot]
      by_contra hne
      have h2 : LinearIndependent K (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 fun h => hne h
      exact (hli 1 _ h2).ne_zero 0 h1
    rw [h0, hL0, slope_sq_bot hGr, slope_sq_bot hGr']
    linarith
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hGr
  obtain ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ := hGr'
  have hsM : (M : Set V') ⊆ Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V)) := by
    intro x hx
    have hne : differentIdeal ℤ (𝓞 K') ≠ ⊥ := fun h => hdisc (by
      rw [← absNorm_differentIdeal K' (𝓞 K'), h, Ideal.absNorm_bot])
    obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := hDiff δ hδ x hx
    have h2 : δ • x ∈ Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V)) := by
      have h3 : Submodule.span (𝓞 K') (ι '' (L : Set V)) ≤
          (Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V))).restrictScalars (𝓞 K') :=
        Submodule.span_le.2 (fun y hy => Submodule.subset_span (Set.image_mono Submodule.subset_span hy))
      exact h3 h1
    have hδK : (δ : K') ≠ 0 := fun h => hδ0 (RingOfIntegers.coe_eq_zero_iff.1 h)
    have h4 : x = (δ : K')⁻¹ • (δ : K') • x := by rw [smul_smul, inv_mul_cancel₀ hδK, one_smul]
    rw [h4]
    refine Submodule.smul_mem _ _ ?_
    have h5 : (δ : K') • x = δ • x := algebraMap_smul K' δ x
    rw [h5]
    exact h2
  classical
  letI : StarRing K := starRingOfComm
  letI : StarRing K' := starRingOfComm
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  haveI : Module.Finite K V := Module.Finite.of_basis b
  haveI : Module.Finite K' V' := Module.Finite.of_basis b'
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  letI : Module (𝓞 K) V' := Module.compHom V' (algebraMap (𝓞 K) (𝓞 K'))
  haveI : IsScalarTower (𝓞 K) (𝓞 K') V' := ⟨fun a s x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let l : L →ₗ[𝓞 K] V' :=
    { toFun := fun x => ι x
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        show ι (a • (x : V)) = algebraMap (𝓞 K) (𝓞 K') a • ι x
        rw [← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]
        rfl }
  have hr : Set.range l = ι '' (L : Set V) := by
    ext y; simp [l]
  have hL : L.FG := by
    haveI : Module.Finite (𝓞 K') M := Module.Finite.iff_fg.2 hM
    haveI : Module.Finite (𝓞 K) M := Module.Finite.trans (𝓞 K') M
    let l' : L →ₗ[𝓞 K] M :=
      { toFun := fun x => ⟨l x, hιM x x.2⟩
        map_add' := fun x y => Subtype.ext (l.map_add x y)
        map_smul' := fun a x => Subtype.ext (l.map_smul a x) }
    refine Module.Finite.iff_fg.1 (Module.Finite.of_injective l' ((injective_iff_map_eq_zero _).2 fun x hx => ?_))
    by_contra hne
    have h1 : LinearIndependent K (fun _ : Fin 1 => (x : V)) :=
      linearIndependent_unique_iff.2 fun h => hne (Subtype.ext h)
    exact (hli 1 _ h1).ne_zero 0 (congrArg Subtype.val hx)
  set L' := Submodule.span (𝓞 K') (ι '' (L : Set V)) with hL'
  have hL'M : L' ≤ M := Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hιM x hx)
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj : Formalism.HN.rkK L = finrank K (Submodule.span K (L : Set V)) := rfl
  generalize finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj
  have he' := hli j e he
  have hspM : Submodule.span K' (M : Set V') = Submodule.span K' (Set.range fun k => ι (e k)) := by
    refine le_antisymm (Submodule.span_le.2 (hsM.trans (Submodule.span_le.2 ?_))) (Submodule.span_mono ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ hx)
      rw [map_sum]
      exact Submodule.sum_mem _ fun k _ => by
        rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rintro _ ⟨k, rfl⟩; exact hιM _ (heL k)
  have hj' : Formalism.HN.rkK M = j := by
    rw [Formalism.HN.rkK, hspM, finrank_span_eq_card he', Fintype.card_fin]
  have hj0 := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b' M h0
  rw [hj'] at hj0
  have hD : differentIdeal ℤ (𝓞 K') • M ≤ L' := Submodule.smul_le.2 fun δ hδ x hx => hDiff δ hδ x hx
  have hdisc : (discr K').natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero K')
  have hDi := Formalism.HN.DualPolygon.twist_index M hM (differentIdeal ℤ (𝓞 K')) fun h => hdisc (by
    rw [← absNorm_differentIdeal K' (𝓞 K'), h, Ideal.absNorm_bot])
  rw [absNorm_differentIdeal K' (𝓞 K'), show finrank K' (Submodule.span K' (M : Set V')) = j from hj'] at hDi
  have hMi : L'.toAddSubgroup.relIndex M.toAddSubgroup ≤ (discr K').natAbs ^ j := by
    rw [← hDi]
    exact AddSubgroup.relIndex_le_of_le_left ((Submodule.toAddSubgroup_le _ _).2 hD)
      (by rw [hDi]; exact pow_ne_zero _ hdisc)
  obtain ⟨i1, g1, m1⟩ := rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  have hFL' : Submodule.span (𝓞 K') (Set.range fun k => ι (e k)) ≤ L' :=
    Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨e k, heL k, rfl⟩)
  obtain ⟨i2, g2, m2⟩ := rk_mul_mu_eq b' X' (fun v => (hG' v).1) _ he' M hM (hFL'.trans hL'M) hj'
  let eL : Fin j → L := fun k => ⟨e k, heL k⟩
  have hsub : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.addSubgroupOf L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup := by
    have : Submodule.span (𝓞 K) (Set.range e) = (Submodule.span (𝓞 K) (Set.range eL)).map L.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]; rfl
    ext x
    rw [this]
    exact ⟨fun ⟨y, hy, h⟩ => (Subtype.ext h : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have hidx : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := by
    rw [AddSubgroup.relIndex, hsub]; rfl
  rw [hidx] at i1 m1
  haveI : Finite (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := Nat.finite_of_card_ne_zero i1
  have hidx' := relIndex_span (S := 𝓞 K') l eL (he'.restrict_scalars' (𝓞 K'))
    (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : 𝓞 K)
    (fun x hx => by
      have h1 : ((Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : ℕ) : K) • (x : V) = 0 := by
        have := congrArg Subtype.val hx
        rw [Nat.cast_smul_eq_nsmul] at this ⊢
        exact this
      exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 i1)))
    (fun x => by
      rw [Nat.cast_smul_eq_nsmul]
      exact (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup.nsmul_index_mem x)
  rw [card_tensor K K' (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩), hr] at hidx'
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hFL')
    ((Submodule.toAddSubgroup_le _ _).2 hL'M)
  rw [show (Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex L'.toAddSubgroup = _
    from hidx'] at hmul
  have hlog : Real.log ((Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex
      M.toAddSubgroup : ℝ) ≤ finrank K K' * Real.log (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL))) +
        j * Real.log |(discr K' : ℝ)| := by
    rw [← Real.log_pow, ← Real.log_pow, ← Real.log_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 i1))
      (pow_ne_zero _ (abs_ne_zero.2 (Int.cast_ne_zero.2 (discr_ne_zero K')))), ← Int.cast_abs, ← Nat.cast_natAbs]
    refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero i2) ?_
    rw [← hmul]
    exact_mod_cast Nat.mul_le_mul_left _ hMi
  have hs : ∑ w : InfinitePlace K', Real.log (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤
      ∑ w, Real.log (Formalism.HN.gramPl b' X' w fun k => ι (e k)).det.re :=
    Finset.sum_le_sum fun w _ => Real.log_le_log (g1 _) (gram_ge hG hG' hc ι hN e w)
  rw [sum_comap K K' fun v => Real.log (Formalism.HN.gramPl b X v e).det.re] at hs
  have hf : (Formalism.HN.nPl K' : ℝ) = finrank K K' * Formalism.HN.nPl K := by
    simpa [Formalism.HN.nPl] using sum_comap K K' fun _ => 1
  have hf' : (0 : ℝ) < Formalism.HN.nPl K' := lt_of_le_of_ne (Nat.cast_nonneg _) Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero.symm
  have hn : (finrank ℚ K' : ℝ) = 2 * Formalism.HN.nPl K' := by
    simpa [Formalism.HN.nPl, Embeddings.card] using sum_mk K' fun _ => 1
  have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
  rw [slope_sq_eq hG hL, slope_sq_eq hG' hM]
  refine le_of_mul_le_mul_left (le_of_mul_le_mul_left ?_ hf') hjp
  have m4 := congrArg ((finrank K K' : ℝ) * ·) m1
  have h5 : (Formalism.HN.nPl K' : ℝ) * (j * (2 * (Real.log |(discr K' : ℝ)| / finrank ℚ K'))) =
      j * Real.log |(discr K' : ℝ)| := by
    rw [hn]; field_simp
  rw [mul_sub, mul_sub, h5, m2, hf]
  linarith

end GlobalTheory.SlopeDifferent
end
end

section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevelLiftModuliLaws_of_core : ∀ (D : D7) (T : CoreJ D) (j : ℕ), LawsJ T → InR D j → Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) ∧ ∀ (G : WTZ D.host.E) (σ : T.Q.c.F →+* ℂ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) G), normW (T.U j) (xiR D) (fun _ => D.sp.W j) (coreDict T.toCore j) G σ f = normW (T.U j) (xiR D) (T.V j) (T.dict j) G σ f := by
  first | exact @GlobalTheory.LevGeo.laws_of_coreJ | exact GlobalTheory.LevGeo.laws_of_coreJ | (intros; apply GlobalTheory.LevGeo.laws_of_coreJ <;> assumption)
end

section
section
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC

noncomputable section

namespace GlobalTheory.CoreRing

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem slope_sq_latOver_sub_le : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (T.R j)), LawsJ T → InR D j → Y.Good e o → Dom a n → S ⊆ (T.cuspA j a n : Set (T.R j)) → GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n) → GoodW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtZ a n) → slope_sq (Y.nrm (wtZ a n)) (Y.latOver (wtZ a n) S) - 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ slope_sq (normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n)) (latW (T.U j) (wtZ a n) ⊓ ((Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype).restrictScalars (𝓞 T.Q.c.F)) := by
  intro D T j Y e o a n S hT hj hY hDom hS hG hG₂
  obtain ⟨hLc, hNc⟩ := GlobalTheory.T.principalLevelLiftModuliLaws_of_core D T j hT hj
  obtain ⟨hLd, hGal, hPull⟩ := GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW
  letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra
  obtain ⟨π, hπP, hπli, hπN, hπlat, -, hπD⟩ := GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent D j _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle (T.U j)
    (coreDict T.toCore j) Y.d Y.U Y.dict hLc hLd hY.lev.1 hGal a n hDom hDom.2
  have hTC : IsTotallyComplex T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

  have hSc : ∀ f ∈ S, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) := fun f hf => by
    rw [cuspW_wtZ]; exact hS hf

  have hPf : ∀ f : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), Y.Pull (f : T.R j) (π f : Rul Y.d.Xo₂ Y.d.c₂) := fun f =>
    (hPull a n _ (cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (by rw [← cuspW_wtZ]; exact f.2)) _).2 (hπP f)

  have p0 : Y.Pull (0 : T.R j) (0 : Rul Y.d.Xo₂ Y.d.c₂) := by
    intro k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero]
  have pAdd : ∀ r₁ r₂ : Rul Y.d.Xo₂ Y.d.c₂, Y.Pull (0 : T.R j) r₁ → Y.Pull (0 : T.R j) r₂ →
      Y.Pull (0 : T.R j) (r₁ + r₂) := by
    intro r₁ r₂ hr₁ hr₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hr₂ k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_add] at e1 e2 ⊢
    rw [e1, e2, add_zero]
  have pSmul : ∀ (c : Y.d.c₂.F) (r : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull (0 : T.R j) r → Y.Pull (0 : T.R j) (c • r) := by
    intro c r hr k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hr k hA hk y₂ y' y h1 h2 h3 h4
    simp only [evR, evalAt_zero, evalAt_smul] at e1 ⊢
    rw [e1, mul_zero]
  have pSub : ∀ (f : T.R j) (g₁ g₂ : Rul Y.d.Xo₂ Y.d.c₂), Y.Pull f g₁ → Y.Pull f g₂ → Y.Pull (0 : T.R j) (g₁ - g₂) := by
    intro f g₁ g₂ hg₁ hg₂ k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hg₁ k hA hk y₂ y' y h1 h2 h3 h4
    have e2 := hg₂ k hA hk y₂ y' y h1 h2 h3 h4
    have e3 : evR Y.d.Xo₂ Y.d.c₂ (g₁ - g₂) y₂ = evR Y.d.Xo₂ Y.d.c₂ g₁ y₂ - evR Y.d.Xo₂ Y.d.c₂ g₂ y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) g₁ g₂
    rw [e3, e1, e2, sub_self]
    simp only [evR, evalAt_zero]
  have pSmul2 : ∀ (c : Y.d.c₂.F) (h : Rul Y.d.Xo₂ Y.d.c₂) (x : Y.V (wtZ a n)),
      Y.Pull (0 : T.R j) (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) →
        Y.Pull (0 : T.R j) (c • h - ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂)) := by
    intro c h x hp k _ _ _ _ _ hA hk y₂ y' y h1 h2 h3 h4
    have e1 := hp k hA hk y₂ y' y h1 h2 h3 h4
    have es1 : evR Y.d.Xo₂ Y.d.c₂ (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) y₂ =
        evR Y.d.Xo₂ Y.d.c₂ h y₂ - evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) h (x : Rul Y.d.Xo₂ Y.d.c₂)
    have es2 : evR Y.d.Xo₂ Y.d.c₂ (c • h - ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂)) y₂ =
        evR Y.d.Xo₂ Y.d.c₂ (c • h) y₂ - evR Y.d.Xo₂ Y.d.c₂ ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      map_sub (evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂) _ _
    have es3 : evR Y.d.Xo₂ Y.d.c₂ (c • h) y₂ = algebraMap Y.d.c₂.F k c * evR Y.d.Xo₂ Y.d.c₂ h y₂ := by
      simp only [evR, evalAt_smul]
    have es4 : evR Y.d.Xo₂ Y.d.c₂ ((c • x : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) y₂ =
        algebraMap Y.d.c₂.F k c * evR Y.d.Xo₂ Y.d.c₂ (x : Rul Y.d.Xo₂ Y.d.c₂) y₂ :=
      (map_smul ((evalL (K := Y.d.c₂.F) (fun S _ _ => FrPt Y.d.Xo₂ Y.d.c₂ S) (fun φ y z => FrMap φ y z) y₂).comp (Y.V (wtZ a n)).subtype) c x).trans (Algebra.smul_def c _)
    rw [es2, es3, es4, ← mul_sub, ← es1, e1]
    simp only [evR, evalAt_zero, mul_zero]
  set C : Submodule T.Q.c.F (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)) :=
    (Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype with hC
  have hCspan : C = Submodule.span T.Q.c.F ((cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype ⁻¹' S) := by
    rw [hC, ← Submodule.comap_map_eq_of_injective (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).injective_subtype
      (Submodule.span T.Q.c.F ((cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype ⁻¹' S)), Submodule.map_span,
      Set.image_preimage_eq_of_subset]
    intro f hf
    exact ⟨⟨f, hSc f hf⟩, rfl⟩
  have hCQ : ∀ x ∈ C, π x ∈
      (Submodule.span Y.d.c₂.F {g | ∃ f ∈ S, Y.Pull f g}).comap (Y.V (wtZ a n)).subtype := by
    rw [hCspan]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨(y : T.R j), hy, hPf y⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy => rw [π.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  have key : ∀ h ∈ Submodule.span Y.d.c₂.F {g | ∃ f ∈ S, Y.Pull f g},
      ∃ x : Y.V (wtZ a n), x ∈ Submodule.span Y.d.c₂.F (π '' (C : Set (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)))) ∧
        Y.Pull (0 : T.R j) (h - (x : Rul Y.d.Xo₂ Y.d.c₂)) := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨f, hfS, hpf⟩ := hh
      refine ⟨π ⟨f, hSc f hfS⟩, Submodule.subset_span ⟨⟨f, hSc f hfS⟩, Submodule.subset_span hfS, rfl⟩, ?_⟩
      exact pSub f _ _ hpf (hPf _)
    | zero => exact ⟨0, zero_mem _, by simpa using p0⟩
    | add h₁ h₂ _ _ ih₁ ih₂ =>
      obtain ⟨x₁, hx₁, p₁⟩ := ih₁
      obtain ⟨x₂, hx₂, p₂⟩ := ih₂
      refine ⟨x₁ + x₂, add_mem hx₁ hx₂, ?_⟩
      have : h₁ + h₂ - ((x₁ + x₂ : Y.V (wtZ a n)) : Rul Y.d.Xo₂ Y.d.c₂) =
          (h₁ - (x₁ : Rul Y.d.Xo₂ Y.d.c₂)) + (h₂ - (x₂ : Rul Y.d.Xo₂ Y.d.c₂)) := by
        rw [Submodule.coe_add]; abel
      rw [this]
      exact pAdd _ _ p₁ p₂
    | smul c h _ ih =>
      obtain ⟨x, hx, p⟩ := ih
      exact ⟨c • x, Submodule.smul_mem _ _ hx, pSmul2 c h x p⟩
  have hu := GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover D T j Y e o hT hj hY hY.unit hY.modelW a n hDom 0 (zero_mem _)
  have hDiff : ∀ δ ∈ differentIdeal ℤ (𝓞 Y.d.c₂.F), ∀ g ∈ Y.latOver (wtZ a n) S,
      δ • g ∈ Submodule.span (𝓞 Y.d.c₂.F) (π '' ((GlobalTheory.AllWt.latW (T.U j) (wtZ a n) ⊓ C.restrictScalars (𝓞 T.Q.c.F) :
        Submodule (𝓞 T.Q.c.F) (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))) : Set _)) := by
    intro δ hδ g hg
    have hgl := (Submodule.mem_inf.1 hg).1
    have hgP := (Submodule.mem_inf.1 hg).2
    obtain ⟨x, hx, px⟩ := key _ hgP
    have hgx : ((g : Rul Y.d.Xo₂ Y.d.c₂) - (x : Rul Y.d.Xo₂ Y.d.c₂)) = 0 :=
      hu.unique ⟨sub_mem g.2 x.2, px⟩ ⟨zero_mem _, p0⟩
    have hgx' : g = x := Subtype.ext (sub_eq_zero.1 hgx)
    have h1 := hπD C δ hδ g hgl (hgx' ▸ hx)
    have hset : {f | f ∈ C ∧ f ∈ GlobalTheory.AllWt.latW (T.U j) (wtZ a n)} =
        ((GlobalTheory.AllWt.latW (T.U j) (wtZ a n) ⊓ C.restrictScalars (𝓞 T.Q.c.F) :
          Submodule (𝓞 T.Q.c.F) (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n))) : Set _) := by
      ext f
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact And.comm
    rw [hset] at h1
    exact h1
  refine GlobalTheory.SlopeDifferent.slope_sq_sub_le_of_different_smul (K := T.Q.c.F) (K' := Y.d.c₂.F) _ _ π _ _ hG.1 hG₂.1
    ?_ hπli ?_ ?_ ?_ hDiff
  · intro σ f
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  · have hle : Y.latOver (wtZ a n) S ≤ GlobalTheory.AllWt.latW Y.U (wtZ a n) := inf_le_left
    haveI := isNoetherian_of_fg_of_noetherian _ hG₂.2.1
    have h1 := (IsNoetherian.noetherian ((Y.latOver (wtZ a n) S).comap (GlobalTheory.AllWt.latW Y.U (wtZ a n)).subtype)).map
      (GlobalTheory.AllWt.latW Y.U (wtZ a n)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h1
  · intro σ' x
    exact (hπN σ' x).trans (hNc _ _ x)
  · intro x hx
    obtain ⟨hxl, hxC⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨(hπlat x).2 hxl, ?_⟩
    exact hCQ x hxC

end GlobalTheory.CoreRing
end
end

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormLattice_slope_sq_goodCover_le_core : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (T.R j)), LawsJ T → InR D j → Y.Good e o → Dom a n → S ⊆ (T.cuspA j a n : Set (T.R j)) → GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n) → GoodW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtZ a n) → slope_sq (Y.nrm (wtZ a n)) (Y.latOver (wtZ a n) S) - 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ slope_sq (normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n)) (latW (T.U j) (wtZ a n) ⊓ ((Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype).restrictScalars (𝓞 T.Q.c.F)) := by
  atlas_forward_decl GlobalTheory.CoreRing.slope_sq_latOver_sub_le
end

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.RingStep

set_option maxHeartbeats 1000000 in

theorem ring_of (_hP : Hypotheses2) (hG : Gram) (hD : DeepGood) : Ring := by
  have hH := GlobalTheory.CovTop.Sizes.hostN 4
  refine Closed.imp ((hG.and hD).and hH) fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨A, -, h3⟩⟩ := h
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, hx⟩ := (h1.and h2).and h3
  refine ⟨x0, fun x hx' hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨g1, g2⟩, g3⟩ := hx x hx' hle ι p hp
  have gram := g1 i
  have deep := g2 i hi Y hY
  have host := g3 i
  have hB := GlobalTheory.T.cuspFormLattice_slope_sq_goodCover_le_core _ p.T ((i : ℕ) + 1) Y _ _ (wtA (p.κ i)) (p.κ i).n (typeK p.fw p.F.lv2 i) p.fw.laws
    ⟨Nat.succ_pos _, i.2⟩ hY.1 (dom_wtA _) (fun f hf => hf.1) gram.2.2.2 deep.1
  have hrd := (log_rd_le_fieldSz Y.d.c₂.F).trans hY.1.size
  obtain ⟨⟨-, hL10, hLx, -⟩, -, -, -, -, -, -, -, -, hpp, ⟨hA1, hPPx, -⟩, hroom, -⟩ := host
  have hb : 391 * zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.b := by
    have hm1 := (Fm.D x ι).R.two_le_m
    have hm2 := (Fm.D x ι).R.m_add_three_le_k
    have hf : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by have := (Fm.D x ι).R.toFrame.ord_pos; show 1 ≤ 2 * (Fm.D x ι).R.toFrame.ord; omega : 1 ≤ (Fm.D x ι).R.f)
    have hr : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ (Fm.D x ι).R.r)
    have hZ : 1 ≤ zBase (Fm.L x ι) := by
      unfold zBase
      have : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
      nlinarith
    have hX : (Fm.L x ι).sc.x ≤ (Fm.L x ι).sc.x ^ A := by
      calc (Fm.L x ι).sc.x = (Fm.L x ι).sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Fm.L x ι).sc.x ^ A := Real.rpow_le_rpow_of_exponent_le (by linarith) hA1
    have hX4 : ((Fm.L x ι).sc.x ^ A) ^ (4 : ℝ) = ((Fm.L x ι).sc.x ^ A) ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast ((Fm.L x ι).sc.x ^ A) 4
    have hZ2 : zBase (Fm.L x ι) ^ 2 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
    have h1 : zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.x ^ A := hZ2.trans (hpp.trans hPPx)
    generalize (Fm.L x ι).sc.x ^ A = X at *
    have hX10 : (10 : ℝ) ≤ X := (hL10.trans hLx).trans hX
    have h3 : (100 : ℝ) ≤ X * X := by nlinarith
    have h4 : (1000 : ℝ) ≤ X * X * X := by nlinarith
    have h2 : 391 * X ≤ X ^ 4 := by nlinarith
    rw [hX4] at hroom
    linarith
  show slope_sq _ (latDeep p i Y) - 2 * (Fm.L x ι).sc.b ≤ muCore p i
  have h2r : 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ 2 * (Fm.L x ι).sc.b := by linarith
  exact le_trans (sub_le_sub_left h2r _) hB

end GlobalTheory.CovTop.RingStep
end
