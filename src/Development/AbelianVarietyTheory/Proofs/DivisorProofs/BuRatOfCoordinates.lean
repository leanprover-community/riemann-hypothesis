import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeInfKerLeOfBasis
import BuildAid.ForwardExisting

section
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_rational_orthogonal_projection_of_finrank_le (K : Type) [Field K] (σ : K →+* ℂ) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W)
    (hj : ∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) :
    ∀ (d : ℕ) (N : Submodule K (Fin n → K)), Module.finrank K N ≤ d → ∀ (x : Fin n → K),
      ∃ y ∈ N, ∀ m ∈ N, ⟪j m, j x - j y⟫_ℂ = 0 := by
  intro d
  induction d with
  | zero =>
    intro N hN x
    refine ⟨0, N.zero_mem, ?_⟩
    have hb : N = ⊥ := by
      rw [← Submodule.finrank_eq_zero]; omega
    intro m hm
    subst hb
    rw [Submodule.mem_bot] at hm
    subst hm
    simp
  | succ d ih =>
    intro N hN x
    by_cases h : ∃ v ∈ N, j v ≠ 0
    · obtain ⟨v, hvN, hv⟩ := h
      let f : (Fin n → K) →ₛₗ[σ] ℂ := (innerₛₗ ℂ (j v)).comp j
      have hf : ∀ z, f z = ⟪j v, j z⟫_ℂ := fun z => rfl
      let N' := N ⊓ LinearMap.ker f
      have hvv : ⟪j v, j v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
      have hlt : N' < N := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hvN' : v ∈ N' := heq ▸ hvN
        have h2 : f v = 0 := hvN'.2
        rw [hf] at h2
        exact hvv h2
      have hN' : Module.finrank K N' ≤ d := by
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      obtain ⟨a, ha⟩ := hj v v
      obtain ⟨b, hb⟩ := hj v x
      have hsa : σ a ≠ 0 := by rw [ha]; exact hvv
      obtain ⟨y', hy'N, hy'⟩ := ih N' hN' (x - (b / a) • v)
      refine ⟨(b / a) • v + y', N.add_mem (N.smul_mem _ hvN) (inf_le_left (a := N) hy'N), ?_⟩
      have key : j x - j ((b / a) • v + y') = j (x - (b / a) • v) - j y' := by
        simp only [map_add, map_sub]; abel
      rw [key]
      have hy'k : ⟪j v, j y'⟫_ℂ = 0 := by
        have : f y' = 0 := hy'N.2
        rwa [hf] at this
      have hv0 : ⟪j v, j (x - (b / a) • v) - j y'⟫_ℂ = 0 := by
        rw [inner_sub_right, map_sub, inner_sub_right, hy'k, map_smulₛₗ, inner_smul_right, ← ha, ← hb,
          map_div₀, div_mul_cancel₀ _ hsa]
        ring
      intro m hm
      obtain ⟨e, he⟩ := hj v m
      have hm' : m - (e / a) • v ∈ N' := by
        refine ⟨N.sub_mem hm (N.smul_mem _ hvN), ?_⟩
        show f (m - (e / a) • v) = 0
        rw [hf, map_sub, inner_sub_right, map_smulₛₗ, inner_smul_right, ← ha, ← he, map_div₀,
          div_mul_cancel₀ _ hsa, sub_self]
      have hsplit : j m = σ (e / a) • j v + j (m - (e / a) • v) := by
        rw [map_sub, map_smulₛₗ]; abel
      rw [hsplit, inner_add_left, inner_smul_left, hv0, mul_zero, zero_add]
      exact hy' _ hm'
    · push_neg at h
      refine ⟨0, N.zero_mem, ?_⟩
      intro m hm
      rw [h m hm, inner_zero_left]

theorem exists_mem_sub_mem_orthogonal_span_of_inner_mem_range : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by
  intro K _ σ W _ _ _ n j hj N x
  obtain ⟨y, hyN, hy⟩ := exists_rational_orthogonal_projection_of_finrank_le K σ W n j hj _ N le_rfl x
  refine ⟨y, hyN, ?_⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨m, hm, rfl⟩ := hu
    exact hy m hm
  | zero => exact inner_zero_left _
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]

end GlobalTheory
end

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_orthogonal_projection_semilinear : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by
  atlas_forward_decl GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range
end

section
open Formalism.BasicNotions Formalism.MainNotions Matrix
open scoped InnerProductSpace

namespace GlobalTheory

theorem buRat_of_coordinates : ∀ (D : D7) (μ : D.what₂.Tup), μ = D.what₂.mu0 → ∀ {n nV d : ℕ} (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) (V : Matrix (Fin n) (Fin nV) D.what₂.LL) (Pq : Matrix (Fin d) (Fin nV) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) (a : D.what₂.Word → ℕ) (eNu : ∀ u, (Fin (a u) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), Formalism.BasicNotions.Rows.BuDefQ D.what₂ → (∀ x y, ⟪jA x, jA y⟫_ℂ ∈ Set.range D.what₂.embLL) → D.what₂.V0 μ = Submodule.span ℂ (Set.range fun F0 => jA (V.mulVec F0)) → (∀ F0, D.what₂.iota μ (jA (V.mulVec F0)) = D.jEE (eRR (Pq.mulVec F0))) → Function.Surjective Pq.mulVec → (∀ u x F0, D.what₂.perCol u μ (D.jN u (eNu u x)) (jA (V.mulVec F0)) ∈ Set.range D.what₂.embLL) → Formalism.MainNotions.WeightDegreeSizes.RationalMapValues D := by
  intro D μ hμ n nV d jA V Pq eRR a eNu hB hinner hV hι hPq hper
  subst hμ
  intro u φ x
  obtain ⟨x', rfl⟩ := (eNu u).surjective φ
  obtain ⟨y, rfl⟩ := eRR.surjective x
  obtain ⟨G, rfl⟩ := hPq y
  have key := span_range_inf_ker_le_of_basis D.what₂.embLL D.div.RR.b (jA.comp V.mulVecLin) D.jEE
    (D.what₂.iota D.what₂.mu0) (eRR.toLinearMap ∘ₗ Pq.mulVecLin) D.jEE_basis.1 hι
  have hset : {x | (eRR.toLinearMap ∘ₗ Pq.mulVecLin) x = 0} = ((LinearMap.ker Pq.mulVecLin : Submodule D.what₂.LL (Fin nV → D.what₂.LL)) : Set (Fin nV → D.what₂.LL)) := by
    ext z
    simp
  have hU : D.what₂.Usp D.what₂.mu0 = Submodule.span ℂ ((jA.comp V.mulVecLin) ''
      ((LinearMap.ker Pq.mulVecLin : Submodule D.what₂.LL (Fin nV → D.what₂.LL)) : Set (Fin nV → D.what₂.LL))) := by
    rw [← hset, ← key, Formalism.BasicNotions.Rows.Data.Usp, hV]
    rfl
  obtain ⟨G', hG', hperp⟩ := GlobalTheory.T.exists_rational_orthogonal_projection_semilinear D.what₂.LL D.what₂.embLL (D.what₂.Amb D.what₂.mu0) nV (jA.comp V.mulVecLin)
    (fun x y => hinner _ _) (LinearMap.ker Pq.mulVecLin) G
  have hG'0 : Pq.mulVec G' = 0 := hG'
  set q : D.what₂.Amb D.what₂.mu0 := jA (V.mulVec (G - G')) with hq
  have hqeq : q = (jA.comp V.mulVecLin) G - (jA.comp V.mulVecLin) G' := by
    rw [hq, ← map_sub]
    rfl
  have hqV : q ∈ D.what₂.V0 D.what₂.mu0 := by
    rw [hV]
    exact Submodule.subset_span ⟨G - G', rfl⟩
  have hqU : q ∈ (D.what₂.Usp D.what₂.mu0)ᗮ := by
    rw [hU, hqeq]
    exact hperp
  have hqQ : q ∈ D.what₂.Qsp D.what₂.mu0 := ⟨hqV, hqU⟩
  have hιq : D.what₂.iota D.what₂.mu0 q = D.jEE (eRR (Pq.mulVec G)) := by
    rw [hq, hι, Matrix.mulVec_sub, hG'0, sub_zero]
  obtain ⟨z, hz⟩ := hper u x' (G - G')
  refine ⟨z, ?_⟩
  rw [hB u, ← hιq, D.what₂.sec_iota _ q hqQ, hz]

end GlobalTheory
end
