import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan

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
