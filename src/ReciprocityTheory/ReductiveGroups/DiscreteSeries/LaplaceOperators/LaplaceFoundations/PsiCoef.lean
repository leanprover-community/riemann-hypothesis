import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.UniqueU
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsCompactUnitaryMat
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

variable {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem measurableEmbedding_leftMul_of_isUnit {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : IsUnit g) :
    MeasurableEmbedding (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) g) := by
  obtain ⟨u, rfl⟩ := hg
  let e : Formalism.QuantumDeterminants.Mt k r ≃ₜ Formalism.QuantumDeterminants.Mt k r :=
    { toFun := Formalism.QuantumDeterminants.lmulM (u : Matrix _ _ ℂ)
      invFun := Formalism.QuantumDeterminants.lmulM ((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ)
      left_inv := fun x => by
        change ((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * ((u : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun x => by
        change (u : Matrix _ _ ℂ) * (((u⁻¹ : (Matrix _ _ ℂ)ˣ) : Matrix _ _ ℂ) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      continuous_toFun := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      continuous_invFun := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id }
  exact e.toMeasurableEquiv.measurableEmbedding

theorem adjoint_comp_self_of_isometry (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) :
    (ContinuousLinearMap.adjoint A).comp A = 1 := by
  let L : V →ₗᵢ[ℂ] V := { toLinearMap := (A : V →ₗ[ℂ] V), norm_map' := hA }
  ext v
  refine ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  exact L.inner_map_map y v

theorem opNorm_le_one_of_isometry_alt (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) : ‖A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hA, one_mul]

theorem schur_orthogonality_unitary_rep (G : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) [IsProbabilityMeasure μ]
    (hG0 : μ {x | Matrix.of x ∉ G} = 0) (hGu : ∀ g ∈ G, IsUnit g)
    (hinv : ∀ g ∈ G, μ.map (Formalism.QuantumDeterminants.lmulM g) = μ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (V →L[ℂ] V))
    (hmul : ∀ g ∈ G, ∀ h ∈ G, σ (g * h) = σ g * σ h) (hunit : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ V, (∀ g ∈ G, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hmeas : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => σ (Matrix.of x)) μ) [Nontrivial V]
    (u u' v v' : V) :
    ∫ x, ⟪v', σ (Matrix.of x) u⟫_ℂ * ⟪σ (Matrix.of x) u', v⟫_ℂ ∂μ =
      ⟪v', v⟫_ℂ * ⟪u', u⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
  classical
  set A : V →L[ℂ] V := (innerSL ℂ u').smulRight u with hA
  set F : Formalism.QuantumDeterminants.Mt k r → (V →L[ℂ] V) := fun x =>
    (σ (Matrix.of x)).comp (A.comp (ContinuousLinearMap.adjoint (σ (Matrix.of x)))) with hF
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ G := by
    rw [ae_iff]; simpa using hG0
  have hFm : AEStronglyMeasurable F μ := by
    have hc : Continuous (fun S : V →L[ℂ] V => S.comp (A.comp (ContinuousLinearMap.adjoint S))) :=
      continuous_id.clm_comp (continuous_const.clm_comp
        (ContinuousLinearMap.adjoint : (V →L[ℂ] V) ≃ₗᵢ⋆[ℂ] (V →L[ℂ] V)).continuous)
    exact hc.comp_aestronglyMeasurable hmeas
  have hFb : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖A‖ := hae.mono fun x hx => by
    have h1 := opNorm_le_one_of_isometry_alt _ (hunit _ hx)
    have h2 : ‖ContinuousLinearMap.adjoint (σ (Matrix.of x))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact h1
    calc ‖F x‖ ≤ ‖σ (Matrix.of x)‖ * (‖A‖ * ‖ContinuousLinearMap.adjoint (σ (Matrix.of x))‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖A‖ * 1) := by gcongr
      _ = ‖A‖ := by ring
  have hFi : Integrable F μ := Integrable.of_bound hFm ‖A‖ hFb
  have hFzi : ∀ z, Integrable (fun x => F x z) μ := fun z => hFi.apply_continuousLinearMap z
  set B : V →L[ℂ] V := ∫ x, F x ∂μ with hB
  have happ : ∀ z, B z = ∫ x, F x z ∂μ := fun z => ContinuousLinearMap.integral_apply hFi z
  have hadj : ∀ g ∈ G, (ContinuousLinearMap.adjoint (σ g)).comp (σ g) = 1 :=
    fun g hg => adjoint_comp_self_of_isometry _ (hunit g hg)
  have hcomm : ∀ g ∈ G, ∀ z, σ g (B z) = B (σ g z) := by
    intro g hg z
    rw [happ, happ, ← ContinuousLinearMap.integral_comp_comm _ (hFzi z)]
    have key : ∀ᵐ x ∂μ, σ g (F x z) = F (Formalism.QuantumDeterminants.lmulM g x) (σ g z) := hae.mono fun x hx => by
      have e : Matrix.of (Formalism.QuantumDeterminants.lmulM g x) = g * Matrix.of x := rfl
      simp only [hF, e, hmul g hg _ hx]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
      simp only [ContinuousLinearMap.comp_apply]
      have := congrArg (fun T : V →L[ℂ] V => T z) (hadj g hg)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
      rw [this]
    rw [integral_congr_ae key]
    conv_rhs => rw [← hinv g hg]
    rw [(measurableEmbedding_leftMul_of_isUnit (hGu g hg)).integral_map]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ z, B z = c • z := by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (B : Module.End ℂ V)
    refine ⟨c, fun z => ?_⟩
    have hS : ∀ g ∈ G, ∀ v ∈ Module.End.eigenspace (B : Module.End ℂ V) c,
        σ g v ∈ Module.End.eigenspace (B : Module.End ℂ V) c := by
      intro g hg v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      change B (σ g v) = c • σ g v
      rw [← hcomm g hg]
      change σ g ((B : Module.End ℂ V) v) = c • σ g v
      rw [hv, map_smul]
    rcases hirr _ hS with h | h
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hv1 := hv.apply_eq_smul
      have hv0 := hv.2
      have : v ∈ Module.End.eigenspace (B : Module.End ℂ V) c := Module.End.mem_eigenspace_iff.2 hv1
      rw [h, Submodule.mem_bot] at this
      exact hv0 this
    · have : z ∈ Module.End.eigenspace (B : Module.End ℂ V) c := h ▸ Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.1 this
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have htr : c * (Module.finrank ℂ V : ℂ) = ⟪u', u⟫_ℂ := by
    let tr : (V →L[ℂ] V) →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ))
    have htrv : ∀ T : V →L[ℂ] V, tr T = LinearMap.trace ℂ V (T : V →ₗ[ℂ] V) := fun T => rfl
    have h1 : tr B = ∫ x, tr (F x) ∂μ := (ContinuousLinearMap.integral_comp_comm tr hFi).symm
    have h2 : ∀ᵐ x ∂μ, tr (F x) = ⟪u', u⟫_ℂ := hae.mono fun x hx => by
      rw [htrv]
      have e1 : ((F x : V →L[ℂ] V) : V →ₗ[ℂ] V) =
          ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) ∘ₗ
            (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V) := rfl
      rw [e1, LinearMap.trace_comp_comm']
      have e2 : (ContinuousLinearMap.adjoint (σ (Matrix.of x)) : V →ₗ[ℂ] V) ∘ₗ
          ((σ (Matrix.of x)).comp A : V →ₗ[ℂ] V) = (A : V →ₗ[ℂ] V) := by
        have := hadj _ hx
        ext y
        have h3 := congrArg (fun T : V →L[ℂ] V => T (A y)) this
        simpa using h3
      rw [e2]
      have e3 : (A : V →ₗ[ℂ] V) = ((innerSL ℂ u' : V →L[ℂ] ℂ) : V →ₗ[ℂ] ℂ).smulRight u := by
        ext y; rfl
      rw [e3, LinearMap.trace_smulRight]
      rfl
    have h3 : tr B = c * (Module.finrank ℂ V : ℂ) := by
      have eB : B = c • (1 : V →L[ℂ] V) := by ext z; simp [hc z]
      rw [htrv, eB]
      simp [LinearMap.trace_one]
    rw [← h3, h1, integral_congr_ae h2, integral_const]
    simp
  have hfin : ⟪v', B v⟫_ℂ = ∫ x, ⟪v', σ (Matrix.of x) u⟫_ℂ * ⟪σ (Matrix.of x) u', v⟫_ℂ ∂μ := by
    rw [happ, ← integral_inner (hFzi v)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF, hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      map_smul, inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
    ring
  rw [← hfin, hc, inner_smul_right]
  have hc' : c = ⟪u', u⟫_ℂ / (Module.finrank ℂ V : ℂ) := by
    rw [← htr]; field_simp
  rw [hc']
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def kE (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j => if hi : i.val < k then (if hj : j.val < k then h ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
    else (if i = j then 1 else 0)

def fI (k r : ℕ) (q : Fin k) : Fin (2 * r + k + 1) := ⟨q.val, by omega⟩

theorem fI_inj : Function.Injective (fI k r) := by
  intro a b h; simp [fI, Fin.ext_iff] at h; exact Fin.ext h

theorem sumF (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ p : Fin (2 * r + k + 1), ¬ p.val < k → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (fI k r q) := by
  symm
  refine Fintype.sum_of_injective (fI k r) fI_inj _ _ ?_ (fun _ => rfl)
  intro p hp
  apply hf
  intro hlt
  exact hp ⟨⟨p.val, hlt⟩, rfl⟩

theorem kE_ff (h : Matrix (Fin k) (Fin k) ℂ) (q q' : Fin k) : kE k r h (fI k r q) (fI k r q') = h q q' := by
  simp [kE, fI]

theorem kE_row (h : Matrix (Fin k) (Fin k) ℂ) {i : Fin (2 * r + k + 1)} (j : Fin (2 * r + k + 1))
    (hi : ¬ i.val < k) : kE k r h i j = if i = j then 1 else 0 := by
  simp [kE, hi]

theorem kE_col (h : Matrix (Fin k) (Fin k) ℂ) (i : Fin (2 * r + k + 1)) {j : Fin (2 * r + k + 1)}
    (hj : ¬ j.val < k) : kE k r h i j = if i = j then 1 else 0 := by
  by_cases hi : i.val < k
  · have hne : i ≠ j := by rintro rfl; exact hj hi
    simp [kE, hi, hj, hne]
  · simp [kE, hi]

theorem ex_fI {i : Fin (2 * r + k + 1)} (hi : i.val < k) : ∃ q, i = fI k r q :=
  ⟨⟨i.val, hi⟩, by ext; simp [fI]⟩

theorem kE_mul (a b : Matrix (Fin k) (Fin k) ℂ) : kE k r (a * b) = kE k r a * kE k r b := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < k
  · obtain ⟨qi, rfl⟩ := ex_fI hi
    rw [sumF _ (fun p hp => by rw [kE_col a _ hp, if_neg (by rintro rfl; exact hp hi), zero_mul])]
    by_cases hj : j.val < k
    · obtain ⟨qj, rfl⟩ := ex_fI hj
      simp only [kE_ff, Matrix.mul_apply]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]
      refine (Finset.sum_eq_zero fun q _ => ?_).symm
      rw [kE_col b _ hj, if_neg (by intro h; apply hj; rw [← h]; exact q.2), mul_zero]
  · rw [kE_row _ j hi]
    rw [Finset.sum_eq_single i (fun p _ hp => by rw [kE_row a p hi, if_neg (Ne.symm hp), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [kE_row a i hi, if_pos rfl, one_mul, kE_row b j hi]

theorem kE_one : kE k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext i j
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dif_pos hi, dif_pos hj, Matrix.one_apply, Fin.ext_iff]
    · rw [kE_col _ _ hj, Matrix.one_apply]
  · rw [kE_row _ _ hi, Matrix.one_apply]

theorem kE_conjTranspose (h : Matrix (Fin k) (Fin k) ℂ) : (kE k r h)ᴴ = kE k r hᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dif_pos hi, dif_pos hj, Matrix.conjTranspose_apply]
    · rw [kE_row _ _ hj, kE_col _ _ hj]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg (Ne.symm hij), if_neg hij, star_zero]
  · rw [kE_col _ _ hi, kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (Ne.symm hij), if_neg hij, star_zero]

variable {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem cay_col (hW : WCols k r P) (q : Fin k) (l : Fin (2 * r + k + 1)) :
    P l (StandardBasisEmbedding.eB k r q) = if l = fI k r q then 1 else 0 := by
  have h := congrFun (hW q) l
  have e : Formalism.QuantumDeterminants.wI k r q.castSucc = StandardBasisEmbedding.eB k r q := rfl
  rw [e] at h
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  rw [h]
  rfl

theorem cay_entry (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (q : Fin k) (j : Fin (2 * r + k + 1)) :
    Hpk k r (StandardBasisEmbedding.eB k r q) j = (if ε (fI k r q) then 1 else -1) * P (fI k r q) j := by
  rw [← hP.2, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cay_col hW, Formalism.REAL.Jm, Matrix.diagonal_apply]
  simp
  rw [Finset.sum_eq_single (fI k r q) (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem cay_eps (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (a : Fin (2 * r + k + 1))
    (ha : a.val < k) : ε a = true := by
  have h := cay_entry hP hW ⟨a.val, ha⟩ (StandardBasisEmbedding.eB k r ⟨a.val, ha⟩)
  rw [StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), if_pos rfl, cay_col hW, if_pos rfl, mul_one] at h
  have e : fI k r ⟨a.val, ha⟩ = a := Fin.ext rfl
  rw [e] at h
  by_contra hne
  rw [if_neg hne] at h
  norm_num at h

theorem cay_zero (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (q : Fin k) {j : Fin (2 * r + k + 1)}
    (hj : ¬ StandardBasisEmbedding.bl k r j) : P (fI k r q) j = 0 := by
  have h := cay_entry hP hW q j
  rw [StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), if_neg (by rintro rfl; exact hj (StandardBasisEmbedding.bl_eB q))] at h
  have hne : (if ε (fI k r q) then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  exact (mul_eq_zero.1 h.symm).resolve_left hne

theorem cay_mul (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (h : Matrix (Fin k) (Fin k) ℂ) :
    P * Formalism.MainNotions.S.blockW k r h = kE k r h * P := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hj : StandardBasisEmbedding.bl k r j
  · obtain ⟨q', rfl⟩ := StandardBasisEmbedding.ex_eB hj
    rw [StandardBasisEmbedding.sumB _ (fun p hp => by rw [StandardBasisEmbedding.bw_off h hp hj, mul_zero])]
    simp only [StandardBasisEmbedding.bw_ee, cay_col hW, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    by_cases hi : i.val < k
    · obtain ⟨qi, rfl⟩ := ex_fI hi
      simp only [ite_mul, one_mul, zero_mul, kE_ff]
      rw [Finset.sum_eq_single qi (fun b _ hb => by rw [if_neg (fun e => hb (fI_inj e).symm)])
        (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
    · rw [kE_row _ _ hi, if_neg (by intro e; apply hi; rw [e]; exact q'.2)]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [if_neg (by intro e; apply hi; rw [e]; exact q.2), zero_mul]
  · rw [Finset.sum_eq_single j (fun b _ hb => by rw [StandardBasisEmbedding.bw_col h b hj, if_neg hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), StandardBasisEmbedding.bw_col h j hj, if_pos rfl, mul_one]
    by_cases hi : i.val < k
    · obtain ⟨qi, rfl⟩ := ex_fI hi
      rw [cay_zero hP hW qi hj]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : l.val < k
      · obtain ⟨ql, rfl⟩ := ex_fI hl
        rw [cay_zero hP hW ql hj, mul_zero]
      · rw [kE_col _ _ hl, if_neg (by rintro rfl; exact hl (by simp [fI])), zero_mul]
    · rw [Finset.sum_eq_single i (fun b _ hb => by rw [kE_row h b hi, if_neg (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), kE_row h i hi, if_pos rfl, one_mul]

theorem cay_kE (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (h : Matrix (Fin k) (Fin k) ℂ) :
    P * Formalism.MainNotions.S.blockW k r h * P⁻¹ = kE k r h := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  rw [cay_mul hP hW, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem eq_smul_highestWeight_of_isWeight {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) {v : T.V}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (HW.torepSig T) Λ v) : ∃ c : ℂ, v = c • T.w := by
  by_cases h0 : v = 0
  · exact ⟨0, by simp [h0]⟩
  have hd := HW.torep_dτ_of_wt T hv
  have hraise : ∀ a b, a < b → ε a = ε b → T.dτ (Matrix.single a b 1) v = 0 := by
    intro a b hab he
    by_contra hx
    have hwx : ∀ c, T.dτ (Matrix.single c c 1) (T.dτ (Matrix.single a b 1) v) =
        (((Λ + Pi.single a 1 - Pi.single b 1 : Fin n → ℝ) c : ℝ) : ℂ) • T.dτ (Matrix.single a b 1) v := by
      intro c
      have hR := HW.KType.kRel T c c a b rfl he
      have h1 := congrArg (fun f : Module.End ℂ T.V => f v) hR
      simp only [HW.kunits, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe] at h1
      have hab' : a ≠ b := ne_of_lt hab
      rw [hd c, map_smul] at h1
      by_cases hca : c = a
      · subst hca
        have hcb : ¬ b = c := fun h => hab' h.symm
        rw [if_pos rfl, if_neg hcb] at h1
        simp only [LinearMap.zero_apply, sub_zero, ContinuousLinearMap.coe_coe] at h1
        rw [sub_eq_iff_eq_add] at h1
        rw [h1]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_pos rfl, if_neg (Ne.symm hcb)]
        push_cast
        module
      · by_cases hcb : b = c
        · subst hcb
          rw [if_neg hca, if_pos rfl] at h1
          simp only [LinearMap.zero_apply, zero_sub, ContinuousLinearMap.coe_coe] at h1
          rw [sub_eq_iff_eq_add] at h1
          rw [h1]
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_pos rfl, if_neg hca]
          push_cast
          module
        · rw [if_neg hca, if_neg hcb] at h1
          simp only [LinearMap.zero_apply, sub_zero] at h1
          rw [sub_eq_zero] at h1
          rw [h1]
          simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, if_neg hca, if_neg (Ne.symm hcb)]
          simp
    obtain ⟨cc, hc, he'⟩ := HW.KType.weight_le T hx hwx
    let ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun f => ∑ j : Fin n, ((j : ℕ) : ℝ) * f j
        map_add' := by
          intro f g
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r f
          simp [Finset.mul_sum, mul_left_comm] }
    have hψ : ∀ x : Fin n, ψ (Pi.single x 1) = ((x : ℕ) : ℝ) := by
      intro x
      simp [ψ, Pi.single_apply]
    have hl : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1 := by
      abel
    rw [hl] at he'
    have h := congrArg ψ he'
    simp only [map_sum, map_smul, root, map_sub, hψ, smul_eq_mul] at h
    have hr : ∑ x, ∑ y, (cc x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
      refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
      by_cases h0 : cc x y = 0
      · simp [h0]
      · have hxy := (hc x y h0).1
        have : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
        exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
    have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  obtain ⟨-, c, hc⟩ := HW.KType.hw_unique T h0 ⟨hd, hraise⟩
  exact ⟨c, hc⟩

section Span

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ}

theorem sumF' {M : Type*} [AddCommMonoid M] (f : Fin (2 * r + k + 1) → M)
    (hf : ∀ p : Fin (2 * r + k + 1), ¬ p.val < k → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (fI k r q) := by
  symm
  refine Fintype.sum_of_injective (fI k r) fI_inj _ _ ?_ (fun _ => rfl)
  intro p hp
  apply hf
  intro hlt
  exact hp ⟨⟨p.val, hlt⟩, rfl⟩

theorem kE_mem_Kset (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) : kE k r h ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, kE_conjTranspose, ← kE_mul]
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hh
    rw [hh, kE_one]
  · ext i j
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i.val < k
    · by_cases hj : j.val < k
      · rw [hε i hi, hε j hj]; simp
      · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp
    · rw [kE_row _ _ hi]
      by_cases hij : i = j
      · subst hij; ring
      · rw [if_neg hij]; simp

def dg (θ : Fin (2 * r + k + 1) → ℝ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

def th2 (θ : Fin (2 * r + k + 1) → ℝ) : Fin (2 * r + k + 1) → ℝ := fun a => if a.val < k then 0 else θ a

def th1 (θ : Fin (2 * r + k + 1) → ℝ) : Fin k → ℝ := fun q => θ (fI k r q)

def dgk (t : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal (fun a => Complex.exp ((t a : ℂ) * Complex.I))

theorem dg_mem (θ : Fin (2 * r + k + 1) → ℝ) : dg θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dg, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp
  · simp only [dg, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

theorem dgk_mem (t : Fin k → ℝ) : dgk t ∈ Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
  have := dg_mem (k := k) (r := 0) (ε := fun _ => true)
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, dgk, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    simp
  · simp only [dgk, Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

theorem dg_split (θ : Fin (2 * r + k + 1) → ℝ) : dg θ = kE k r (dgk (th1 θ)) * dg (th2 θ) := by
  ext i j
  unfold dg
  rw [Matrix.mul_diagonal]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [dg, dgk, kE, th1, th2, dif_pos hi, dif_pos hj, if_pos hj, Matrix.diagonal_apply, fI]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (by intro e; apply hij; exact Fin.ext (by simpa using e))]; simp
    · simp only [dg, th2, if_neg hj, Matrix.diagonal_apply]
      rw [kE_col _ _ hj]
      by_cases hij : i = j
      · subst hij; exact absurd hi hj
      · simp [hij]
  · simp only [dg, th2, Matrix.diagonal_apply]
    rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp [hi]
    · simp [hij]

theorem central_diagonal_commute (θ : Fin (2 * r + k + 1) → ℝ) (h : Matrix (Fin k) (Fin k) ℂ) :
    kE k r h * dg (th2 θ) = dg (th2 θ) * kE k r h := by
  ext i j
  rw [dg, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp [th2, hi, hj]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp
  · rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; ring
    · rw [if_neg hij]; simp

variable (T : S7.KType ε Λ)

def rhoK (h : Matrix (Fin k) (Fin k) ℂ) : T.V →L[ℂ] T.V := HW.torepSig T (kE k r h)

def spanW : Submodule ℂ T.V :=
  sInf {S | T.w ∈ S ∧ ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S, rhoK (k := k) (r := r) T h v ∈ S}

theorem w_mem_spanW : T.w ∈ spanW (k := k) (r := r) T :=
  Submodule.mem_sInf.2 fun _ hS => hS.1

theorem spanW_stable {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) {v : T.V}
    (hv : v ∈ spanW (k := k) (r := r) T) : rhoK (k := k) (r := r) T h v ∈ spanW (k := k) (r := r) T :=
  Submodule.mem_sInf.2 fun S hS => hS.2 h hh v (Submodule.mem_sInf.1 hv S hS)

theorem spanW_le {S : Submodule ℂ T.V} (hw : T.w ∈ S)
    (hS : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S, rhoK (k := k) (r := r) T h v ∈ S) :
    spanW (k := k) (r := r) T ≤ S :=
  sInf_le ⟨hw, hS⟩

theorem torep_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) (v : T.V) : HW.torepSig T (a * b) v = HW.torepSig T a (HW.torepSig T b v) := by
  rw [(HW.torep_isURepOn T).1.2 a ha b hb]; rfl

theorem spanW_scalar (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) (θ : Fin (2 * r + k + 1) → ℝ)
    {x : T.V} (hx : x ∈ spanW (k := k) (r := r) T) :
    HW.torepSig T (dg (th2 θ)) x = Complex.exp (((∑ a, Λ a * th2 θ a : ℝ) : ℂ) * Complex.I) • x := by
  set c := Complex.exp (((∑ a, Λ a * th2 θ a : ℝ) : ℂ) * Complex.I)
  let S : Submodule ℂ T.V := LinearMap.ker ((HW.torepSig T (dg (th2 θ)) : T.V →ₗ[ℂ] T.V) - c • LinearMap.id)
  have hmem : ∀ y, y ∈ S ↔ HW.torepSig T (dg (th2 θ)) y = c • y := by
    intro y
    simp [S, sub_eq_zero]
  have hle : spanW (k := k) (r := r) T ≤ S := by
    refine spanW_le T ((hmem _).2 (HW.torep_wt_w T (th2 θ) (dg_mem _))) ?_
    intro h hh v hv
    rw [hmem] at hv ⊢
    unfold rhoK
    rw [← torep_mul T (dg_mem _) (kE_mem_Kset hε hh), ← central_diagonal_commute, torep_mul T (kE_mem_Kset hε hh) (dg_mem _), hv,
      map_smul]
  exact (hmem x).1 (hle hx)

end Span

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

section Wt

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

theorem dgk_unit (t : Fin k → ℝ) : dgk t ∈ Matrix.unitaryGroup (Fin k) ℂ := (dgk_mem t).1

theorem wt_full (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {x : T.V}
    (hx : x ∈ spanW (k := k) (r := r) T) {μ : Fin k → ℝ}
    (hμ : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ x) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (HW.torepSig T)
      (fun a => if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) x := by
  intro θ _
  change HW.torepSig T (dg θ) x = _
  rw [dg_split, torep_mul T (kE_mem_Kset hε (dgk_unit _)) (dg_mem _), spanW_scalar T hε θ hx, map_smul]
  have h1 : HW.torepSig T (kE k r (dgk (th1 θ))) x =
      Complex.exp (((∑ q, μ q * th1 θ q : ℝ) : ℂ) * Complex.I) • x := hμ (th1 θ) (dgk_mem _)
  rw [h1, smul_smul, ← Complex.exp_add]
  congr 1
  have hs : (∑ a, (if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) * θ a) =
      (∑ a, Λ a * th2 θ a) + ∑ q, μ q * th1 θ q := by
    have e : ∑ q, μ q * th1 θ q = ∑ a : Fin (2 * r + k + 1), (if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0) := by
      rw [sumF' (k := k) (r := r) (fun a : Fin (2 * r + k + 1) => if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0)
        (fun p hp => by rw [dif_neg hp])]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hq : (fI k r q).val < k := q.2
      rw [dif_pos hq]
      rfl
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a.val < k
    · simp [th2, ha]
    · simp [th2, ha]
  rw [hs, Complex.ofReal_add, add_mul]

theorem root_sum_apply {m : ℕ} (c : Fin m → Fin m → ℕ) (x : Fin m) :
    (∑ a, ∑ b, (c a b : ℝ) • (Pi.single a (1 : ℝ) - Pi.single b 1 : Fin m → ℝ)) x =
      ∑ b, (c x b : ℝ) - ∑ a, (c a x : ℝ) := by
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  congr 1
  · rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  · simp [Finset.sum_ite_eq]

theorem wt_cdom (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {x : T.V}
    (hx : x ∈ spanW (k := k) (r := r) T) (hx0 : x ≠ 0) {μ : Fin k → ℝ}
    (hμ : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ x) :
    Formalism.MainNotions.S.CDom (Formalism.MainNotions.S.allPos k) μ (fun q => Λ (fI k r q)) := by
  have hfull := wt_full T hε hx hμ
  obtain ⟨c, hc, he⟩ := HW.KType.weight_le T hx0 (HW.torep_dτ_of_wt T hfull)
  have he' : ∀ y, (Λ - fun a => if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) y =
      ∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ) := by
    intro y
    rw [he]
    exact root_sum_apply c y

  have hzero : ∀ a b : Fin (2 * r + k + 1), a.val < k → ¬ b.val < k → c a b = 0 := by
    let g : Fin (2 * r + k + 1) → ℝ := fun y => if y.val < k then 0 else 1
    have hsum : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y.val < k
      · simp [g, hy]
      · rw [← he' y]; simp [g, hy]
    have hsum2 : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) =
        ∑ a, ∑ b, (c a b : ℝ) * (g a - g b) := by
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [hsum2] at hsum
    have hnp : ∀ a b : Fin (2 * r + k + 1), (c a b : ℝ) * (g a - g b) ≤ 0 := by
      intro a b
      by_cases h0 : c a b = 0
      · simp [h0]
      · have hab := (hc a b h0).1
        have hab' : a.val < b.val := hab
        refine mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ?_
        simp only [g]
        split_ifs with h1 h2 h2 <;> norm_num
        omega
    have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ => hnp a b)).1 hsum
    intro a b ha hb
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hnp a b)).1 (hall a (Finset.mem_univ _)) b
      (Finset.mem_univ _)
    simp only [g, if_pos ha, if_neg hb] at h1
    norm_num at h1
    exact_mod_cast h1
  refine ⟨fun q q' => c (fI k r q) (fI k r q'), fun q q' h => ⟨?_, rfl⟩, ?_⟩
  · have := (hc _ _ h).1
    exact this
  · funext q
    have hq : (fI k r q).val < k := q.2
    have h1 := he' (fI k r q)
    simp only [Pi.sub_apply, dif_pos hq] at h1
    have e1 : ∑ b, (c (fI k r q) b : ℝ) = ∑ q', (c (fI k r q) (fI k r q') : ℝ) :=
      sumF' _ (fun p hp => by rw [hzero _ _ hq hp]; simp)
    have e2 : ∑ a, (c a (fI k r q) : ℝ) = ∑ q', (c (fI k r q') (fI k r q) : ℝ) := by
      refine sumF' _ (fun p hp => ?_)
      by_cases h0 : c p (fI k r q) = 0
      · simp [h0]
      · have := (hc _ _ h0).1
        have : p.val < (fI k r q).val := this
        exact absurd (lt_trans this hq) hp
    rw [e1, e2] at h1
    have e3 : (⟨(fI k r q).val, hq⟩ : Fin k) = q := Fin.ext rfl
    rw [e3] at h1
    rw [show ((fun q => Λ (fI k r q)) - μ) q = Λ (fI k r q) - μ q from rfl, h1]
    have := root_sum_apply (fun q q' => c (fI k r q) (fI k r q')) q
    rw [← this]
    rfl

end Wt

section Irr

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

theorem kE_dgk (t : Fin k → ℝ) :
    kE k r (dgk t) = dg (fun a : Fin (2 * r + k + 1) => if h : a.val < k then t ⟨a.val, h⟩ else 0) := by
  ext i j
  simp only [dg, Matrix.diagonal_apply]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dgk, dif_pos hi, dif_pos hj, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (by intro e; apply hij; exact Fin.ext (by simpa using e))]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp [show i ≠ j by rintro rfl; exact hj hi]
  · rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp [hi]
    · simp [hij]

theorem kE_cont : Continuous (kE k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [kE]
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem w_wtK : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
    (fun q => Λ (fI k r q)) T.w := by
  intro t _
  change HW.torepSig T (kE k r (dgk t)) T.w = _
  rw [kE_dgk]
  unfold dg
  rw [HW.torep_wt_w T _ (dg_mem _)]
  congr 3
  congr 1
  refine (sumF' (M := ℝ) (k := k) (r := r) _ (fun p hp => ?_)).trans (Finset.sum_congr rfl fun q _ => ?_)
  · simp [hp]
  · have hq : (fI k r q).val < k := q.2
    simp only [dif_pos hq]
    rfl

theorem rhoK_one (v : T.V) : rhoK (k := k) (r := r) T 1 v = v := by
  unfold rhoK
  rw [kE_one, (HW.torep_isURepOn T).1.1]
  rfl

theorem rhoK_mul (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {a b : Matrix (Fin k) (Fin k) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin k) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin k) ℂ) (v : T.V) :
    rhoK (k := k) (r := r) T (a * b) v = rhoK (k := k) (r := r) T a (rhoK (k := k) (r := r) T b v) := by
  unfold rhoK
  rw [kE_mul, torep_mul T (kE_mem_Kset hε ha) (kE_mem_Kset hε hb)]

theorem rhoK_norm (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {a : Matrix (Fin k) (Fin k) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin k) ℂ) (v : T.V) : ‖rhoK (k := k) (r := r) T a v‖ = ‖v‖ :=
  (HW.torep_isURepOn T).2.1 _ (kE_mem_Kset hε ha) v

theorem rhoK_adj (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) (u v : T.V) :
    ⟪u, rhoK (k := k) (r := r) T h v⟫_ℂ = ⟪rhoK (k := k) (r := r) T (star h) u, v⟫_ℂ := by
  have hs : star h ∈ Matrix.unitaryGroup (Fin k) ℂ := Unitary.star_mem hh
  have hinv : rhoK (k := k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v) = v := by
    rw [← rhoK_mul T hε hs hh, Unitary.star_mul_self_of_mem hh, rhoK_one]
  let Lm : T.V →ₗᵢ[ℂ] T.V :=
    { toLinearMap := (rhoK (k := k) (r := r) T (star h) : T.V →ₗ[ℂ] T.V), norm_map' := rhoK_norm T hε hs }
  have := Lm.inner_map_map u (rhoK (k := k) (r := r) T h v)
  change ⟪rhoK (k := k) (r := r) T (star h) u, rhoK (k := k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v)⟫_ℂ = _
    at this
  rw [hinv] at this
  exact this.symm

theorem spanW_irred (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) (S' : Submodule ℂ T.V)
    (hle : S' ≤ spanW (k := k) (r := r) T)
    (hS' : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S', rhoK (k := k) (r := r) T h v ∈ S') :
    S' = ⊥ ∨ spanW (k := k) (r := r) T ≤ S' := by
  have hperp : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S'ᗮ, rhoK (k := k) (r := r) T h v ∈ S'ᗮ := by
    intro h hh v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    rw [rhoK_adj T hε hh]
    exact hv _ (hS' _ (Unitary.star_mem hh) u hu)
  have hbot : ∀ x, x ∈ S' → x ∈ S'ᗮ → x = 0 := by
    intro x h1 h2
    have hm : x ∈ S' ⊓ S'ᗮ := ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  obtain ⟨p, hp, q, hq, hpq⟩ := S'.exists_add_mem_mem_orthogonal T.w
  have hpw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (fun q => Λ (fI k r q)) p := by
    intro t ht
    have hu : dgk t ∈ Matrix.unitaryGroup (Fin k) ℂ := ht.1
    have h1 := w_wtK T t ht
    set c := Complex.exp (((∑ a, Λ (fI k r a) * t a : ℝ) : ℂ) * Complex.I)
    change rhoK (k := k) (r := r) T (dgk t) T.w = c • T.w at h1
    change rhoK (k := k) (r := r) T (dgk t) p = c • p
    rw [hpq, map_add, smul_add] at h1
    have hA : rhoK (k := k) (r := r) T (dgk t) p - c • p ∈ S' := S'.sub_mem (hS' _ hu _ hp) (S'.smul_mem _ hp)
    have hB : rhoK (k := k) (r := r) T (dgk t) p - c • p ∈ S'ᗮ := by
      have e : rhoK (k := k) (r := r) T (dgk t) p - c • p = c • q - rhoK (k := k) (r := r) T (dgk t) q := by
        rw [sub_eq_sub_iff_add_eq_add, h1]
        exact add_comm _ _
      rw [e]
      exact S'ᗮ.sub_mem (S'ᗮ.smul_mem _ hq) (hperp _ hu _ hq)
    exact sub_eq_zero.1 (hbot _ hA hB)
  have hqw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (fun q => Λ (fI k r q)) q := by
    intro t ht
    have h1 := w_wtK T t ht
    have h2 := hpw t ht
    have e : q = T.w - p := by rw [hpq]; abel
    rw [e, map_sub, h1, h2, smul_sub]
  have hpS : p ∈ spanW (k := k) (r := r) T := hle hp
  have hqS : q ∈ spanW (k := k) (r := r) T := by
    have e : q = T.w - p := by rw [hpq]; abel
    rw [e]; exact sub_mem (w_mem_spanW T) hpS
  have hfix : (fun a : Fin (2 * r + k + 1) => if h : a.val < k then (fun q => Λ (fI k r q)) ⟨a.val, h⟩ else Λ a) = Λ := by
    funext a; split_ifs <;> rfl
  have hp2 := wt_full T hε hpS hpw
  have hq2 := wt_full T hε hqS hqw
  rw [hfix] at hp2 hq2
  obtain ⟨a, ha⟩ := eq_smul_highestWeight_of_isWeight T hp2
  obtain ⟨b, hb⟩ := eq_smul_highestWeight_of_isWeight T hq2
  have hinner : ⟪p, q⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hp hq
  rw [ha, hb, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, T.w_norm] at hinner
  simp only [RCLike.ofReal_one, one_pow, mul_one] at hinner
  rcases mul_eq_zero.1 hinner with h | h
  · left
    have ha0 : a = 0 := by simpa using h
    have hq' : T.w = q := by rw [hpq, ha, ha0, zero_smul, zero_add]
    have hle' : spanW (k := k) (r := r) T ≤ S'ᗮ := spanW_le T (hq' ▸ hq) hperp
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hbot x hx (hle' (hle hx))
  · right
    have hp' : T.w = p := by rw [hpq, hb, h, zero_smul, add_zero]
    exact spanW_le T (hp' ▸ hp) hS'

end Irr

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

open Classical in

def rhoS (h : Matrix (Fin k) (Fin k) ℂ) : spanW (k := k) (r := r) T →L[ℂ] spanW (k := k) (r := r) T :=
  if hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ then
    LinearMap.toContinuousLinearMap ((rhoK (k := k) (r := r) T h : T.V →ₗ[ℂ] T.V).restrict
      (fun _ hv => spanW_stable T hh hv))
  else 0

theorem rhoS_apply {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ)
    (v : spanW (k := k) (r := r) T) : (rhoS T h v : T.V) = rhoK (k := k) (r := r) T h v := by
  simp only [rhoS, dif_pos hh]
  rfl

theorem uj_unit {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) :
    h ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  exact (HW.uqU_mem_Kset hh).1

theorem unit_ks {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    h ∈ Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
  refine ⟨hh, ?_⟩
  simp [Formalism.REAL.Jm, Formalism.MainNotions.S.allPos]

theorem unit_uj {h : Matrix (Fin k) (Fin k) ℂ} (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) := by
  have hJ : Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) = 1 := by simp [Formalism.REAL.Jm, Formalism.MainNotions.S.allPos]
  show hᴴ * Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) * h = Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k)
  rw [hJ, Matrix.mul_one, ← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mul_self_of_mem hh

theorem wtS_iff {μ : Fin k → ℝ} {v : spanW (k := k) (r := r) T} :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoS T) μ v ↔
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ (v : T.V) := by
  constructor
  · intro h t ht
    have := congrArg Subtype.val (h t ht)
    rw [rhoS_apply T ht.1] at this
    exact this
  · intro h t ht
    apply Subtype.ext
    rw [rhoS_apply T ht.1]
    exact h t ht

theorem rhoS_hc (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {u : Fin k → ℝ}
    (hΛ : ∀ q : Fin k, Λ (fI k r q) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u q) :
    Formalism.MainNotions.S.IsHCTypeU k u (rhoS T) := by
  have hΛ' : (fun q => Λ (fI k r q)) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u := funext hΛ
  refine ⟨⟨⟨⟨T.w, w_mem_spanW T⟩, 0, fun h => HW.KType.w_ne_zero T (congrArg Subtype.val h)⟩⟩,
    inferInstance, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨inferInstance, fun _ _ _ _ => Submodule.mem_top, ?_, ?_, ?_⟩⟩
  · ext v
    rw [rhoS_apply T (one_mem _), rhoK_one]
    rfl
  · intro a ha b hb
    ext v
    rw [rhoS_apply T (mul_mem (uj_unit ha) (uj_unit hb)), rhoK_mul T hε (uj_unit ha) (uj_unit hb)]
    change _ = ((rhoS T a (rhoS T b v)) : T.V)
    rw [rhoS_apply T (uj_unit ha), rhoS_apply T (uj_unit hb)]
  · intro g hg v
    change ‖(rhoS T g v : T.V)‖ = ‖(v : T.V)‖
    rw [rhoS_apply T (uj_unit hg), rhoK_norm T hε (uj_unit hg)]
  · intro v
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hc : ContinuousOn (fun g => rhoK (k := k) (r := r) T g v) (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) :=
      ((HW.torep_isURepOn T).2.2 v).comp kE_cont.continuousOn
        (fun g hg => kE_mem_Kset hε (uj_unit hg))
    refine hc.congr fun g hg => ?_
    exact rhoS_apply T (uj_unit hg) v
  · intro S' _ hS'
    let S'' : Submodule ℂ T.V := S'.map (spanW (k := k) (r := r) T).subtype
    have hle : S'' ≤ spanW (k := k) (r := r) T := by
      rintro _ ⟨v, _, rfl⟩
      exact v.2
    have hst : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S'', rhoK (k := k) (r := r) T h v ∈ S'' := by
      rintro h hh _ ⟨v, hv, rfl⟩
      refine ⟨rhoS T h v, hS' h (unit_ks hh) v hv, ?_⟩
      exact rhoS_apply T hh v
    rcases spanW_irred T hε S'' hle hst with h | h
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have : (v : T.V) ∈ S'' := ⟨v, hv, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact Subtype.ext this
    · right
      rw [eq_top_iff]
      intro v _
      obtain ⟨v', hv', he⟩ := h v.2
      have : v' = v := Subtype.ext he
      rw [← this]; exact hv'
  · refine ⟨⟨T.w, w_mem_spanW T⟩, Submodule.mem_top,
      fun h => HW.KType.w_ne_zero T (congrArg Subtype.val h), ?_⟩
    rw [wtS_iff, ← hΛ']
    exact w_wtK T
  · intro μ v _ hv hwt
    rw [wtS_iff] at hwt
    rw [← hΛ']
    exact wt_cdom T hε v.2 (fun h => hv (Subtype.ext h)) hwt

theorem lowestKType_intertwiner_exists (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {u : Fin k → ℝ}
    (hΛ : ∀ q : Fin k, Λ (fI k r q) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u q)
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    (π' : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp)) (hπ : Formalism.MainNotions.S.IsHCTypeU k u π') {ξ : Vp}
    (hξ : Formalism.MainNotions.S.IsWtOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π' (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) ξ) :
    ∃ (U : Vp ≃ₗᵢ[ℂ] spanW (k := k) (r := r) T) (α : ℂ),
      (∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v, rhoK (k := k) (r := r) T g (U v) = (U (π' g v) : T.V)) ∧
        (U ξ : T.V) = α • T.w := by
  obtain ⟨U, hU⟩ := HW.hcTypeU_unique π' (rhoS T) hπ (rhoS_hc T hε hΛ)
  have hint : ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v,
      rhoK (k := k) (r := r) T g (U v) = (U (π' g v) : T.V) := fun g hg v => by
    rw [← rhoS_apply T hg, hU g (unit_uj hg) v]
  have hΛ' : (fun q => Λ (fI k r q)) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u := funext hΛ
  have hwt : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) (U ξ : T.V) := by
    intro t ht
    rw [hint _ ht.1, hξ t (unit_uj ht.1), map_smul]
    rfl
  rw [← hΛ'] at hwt
  have hfull := wt_full T hε (U ξ).2 hwt
  have hfix : (fun a : Fin (2 * r + k + 1) => if h : a.val < k then (fun q => Λ (fI k r q)) ⟨a.val, h⟩ else Λ a) = Λ := by
    funext a; split_ifs <;> rfl
  rw [hfix] at hfull
  obtain ⟨α, hα⟩ := eq_smul_highestWeight_of_isWeight T hfull
  exact ⟨U, α, hint, hα⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants

variable {k r : ℕ}

theorem clm_continuousOn {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (σ : X → (V →L[ℂ] V)) (s : Set X)
    (h : ∀ v, ContinuousOn (fun g => σ g v) s) : ContinuousOn σ s := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_clm_apply.2 fun v => continuousOn_iff_continuous_domRestrict.1 (h v)

theorem isClosed_UW : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have e : {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)} =
      {x | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} ∩
        ((⋂ a : Fin r, ({x | Matrix.of x *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {x | Matrix.of x *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩
          {x | Matrix.of x *ᵥ z0 k r = z0 k r}) := by
    ext x
    simp only [UWset, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter (isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc)
    continuous_const) (IsClosed.inter (isClosed_iInter fun a => IsClosed.inter ?_ ?_) ?_)
  · exact isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const

theorem blk_cont : Continuous (fun x : Mt k r => StandardBasisEmbedding.blk (k := k) (r := r) (Matrix.of x)) := by
  refine continuous_pi fun q => continuous_pi fun q' => ?_
  exact (continuous_apply _).comp (continuous_apply _)

theorem uw_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UWset k r (z0 k r)) :
    g⁻¹ = Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) ∧ IsUnit g := by
  have hu := StandardBasisEmbedding.blk_unitary hg
  have h1 : g * Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) = 1 := by
    have e := StandardBasisEmbedding.eq_blockW hg
    rw [show g * Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) =
        Formalism.MainNotions.S.blockW k r (StandardBasisEmbedding.blk g) * Formalism.MainNotions.S.blockW k r (star (StandardBasisEmbedding.blk g)) from by rw [← e]]
    rw [← StandardBasisEmbedding.blockW_mul, Unitary.mul_star_self_of_mem hu, StandardBasisEmbedding.blockW_one]
  exact ⟨Matrix.inv_eq_right_inv h1, ⟨⟨g, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩⟩

theorem schur_orthogonality_whittaker {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {u : Fin k → ℝ}
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Vp →L[ℂ] Vp)) {ξ : Vp}
    {μW : Measure (Mt k r)} (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P)
    (hπ : Formalism.MainNotions.S.IsHCTypeU k u (fun h => π (Formalism.MainNotions.S.blockW k r h))) (hξn : ‖ξ‖ = 1)
    (hξ : Formalism.MainNotions.S.IsWtOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) (fun h => π (Formalism.MainNotions.S.blockW k r h))
      (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) ξ)
    (hΛ : ∀ a : Fin k, Λ ⟨a.val, by omega⟩ = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u a)
    (hμW : Formalism.MainNotions.S.IsHaarOn (UWset k r (z0 k r)) μW) (hμ1 : μW Set.univ = 1) (Y : T.V) :
    ∫ x, ⟪ξ, π (Matrix.of x)⁻¹ ξ⟫_ℂ * ⟪T.w, HW.torepSig T (P * Matrix.of x * P⁻¹) Y⟫_ℂ ∂μW =
      (Module.finrank ℂ Vp : ℂ)⁻¹ * ⟪T.w, Y⟫_ℂ := by
  classical
  set π' : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp) := fun h => π (Formalism.MainNotions.S.blockW k r h) with hπ'
  have hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true := fun a ha => cay_eps hP hW a ha
  have hΛ' : ∀ q : Fin k, Λ (fI k r q) = Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u q := fun q => hΛ q
  have : FiniteDimensional ℂ Vp := hπ.2.1
  have : Nontrivial Vp := hπ.1
  have : IsProbabilityMeasure μW := ⟨hμ1⟩
  obtain ⟨U, α, hint, hα⟩ := lowestKType_intertwiner_exists T hε hΛ' π' hπ hξ
  have hUR := hπ.2.2.1
  have hπadj : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ a b : Vp, ⟪a, π' h b⟫_ℂ = ⟪π' (star h) a, b⟫_ℂ := by
    intro h hh a b
    have hs : star h ∈ Matrix.unitaryGroup (Fin k) ℂ := Unitary.star_mem hh
    have hinv : π' (star h) (π' h b) = b := by
      have := hUR.1.2 _ (unit_uj hs) _ (unit_uj hh)
      rw [Unitary.star_mul_self_of_mem hh, hUR.1.1] at this
      have := congrArg (fun A : Vp →L[ℂ] Vp => A b) this
      simpa using this.symm
    let Lm : Vp →ₗᵢ[ℂ] Vp := { toLinearMap := (π' (star h) : Vp →ₗ[ℂ] Vp), norm_map' := hUR.2.1 _ (unit_uj hs) }
    have := Lm.inner_map_map a (π' h b)
    change ⟪π' (star h) a, π' (star h) (π' h b)⟫_ℂ = _ at this
    rw [hinv] at this
    exact this.symm
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hα
    have : U ξ = 0 := Subtype.ext hα
    rw [LinearIsometryEquiv.map_eq_zero_iff] at this
    rw [this, norm_zero] at hξn
    exact zero_ne_one hξn
  set η : Vp := α⁻¹ • ξ with hηdef
  have hη : (U η : T.V) = T.w := by
    rw [hηdef, map_smul, Submodule.coe_smul, hα, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  set Y' : Vp := U.symm ((spanW (k := k) (r := r) T).orthogonalProjectionOnto Y) with hY'
  have hproj : ∀ s : spanW (k := k) (r := r) T,
      ⟪(s : T.V), Y⟫_ℂ = ⟪s, (spanW (k := k) (r := r) T).orthogonalProjectionOnto Y⟫_ℂ := by
    intro s
    have h0 : ⟪(s : T.V), Y - ((spanW (k := k) (r := r) T).orthogonalProjectionOnto Y : T.V)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal s.2 ((spanW (k := k) (r := r) T).sub_starProjection_mem_orthogonal Y)
    rw [inner_sub_right, sub_eq_zero] at h0
    rw [h0]
    rfl
  have hUY : ∀ a : Vp, ⟪(U a : T.V), Y⟫_ℂ = ⟪a, Y'⟫_ℂ := by
    intro a
    rw [hproj, ← U.inner_map_map a Y', hY', U.apply_symm_apply]
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r (z0 k r) := by
    rw [ae_iff]; simpa using hμW.2.2.1
  have hpt : ∀ᵐ x ∂μW, ⟪ξ, π (Matrix.of x)⁻¹ ξ⟫_ℂ * ⟪T.w, HW.torepSig T (P * Matrix.of x * P⁻¹) Y⟫_ℂ =
      ⟪η, π (Matrix.of x) Y'⟫_ℂ * ⟪π (Matrix.of x) ξ, ξ⟫_ℂ := hae.mono fun x hx => by
    have hu : StandardBasisEmbedding.blk (Matrix.of x) ∈ Matrix.unitaryGroup (Fin k) ℂ := StandardBasisEmbedding.blk_unitary hx
    have hx' : Matrix.of x = Formalism.MainNotions.S.blockW k r (StandardBasisEmbedding.blk (Matrix.of x)) := StandardBasisEmbedding.eq_blockW hx
    have h1 : π (Matrix.of x)⁻¹ = π' (star (StandardBasisEmbedding.blk (Matrix.of x))) := by rw [(uw_inv hx).1]
    have h2 : HW.torepSig T (P * Matrix.of x * P⁻¹) = rhoK (k := k) (r := r) T (StandardBasisEmbedding.blk (Matrix.of x)) := by
      rw [rhoK, ← cay_kE hP hW, ← hx']
    have h3 : π (Matrix.of x) = π' (StandardBasisEmbedding.blk (Matrix.of x)) := by
      rw [hπ']; exact congrArg π hx'
    rw [h1, h2, h3]
    rw [rhoK_adj T hε hu, ← hη, hint _ (Unitary.star_mem hu), hUY, ← hπadj _ hu]
    rw [hπadj _ (Unitary.star_mem hu), star_star, mul_comm]
  rw [integral_congr_ae hpt]
  have hmul : ∀ g ∈ UWset k r (z0 k r), ∀ h ∈ UWset k r (z0 k r), π (g * h) = π g * π h := by
    intro g hg h hh
    have e1 := StandardBasisEmbedding.eq_blockW hg
    have e2 := StandardBasisEmbedding.eq_blockW hh
    rw [e1, e2, ← StandardBasisEmbedding.blockW_mul]
    exact hUR.1.2 _ (unit_uj (StandardBasisEmbedding.blk_unitary hg)) _ (unit_uj (StandardBasisEmbedding.blk_unitary hh))
  have hunit : ∀ g ∈ UWset k r (z0 k r), ∀ v, ‖π g v‖ = ‖v‖ := by
    intro g hg v
    rw [StandardBasisEmbedding.eq_blockW hg]
    exact hUR.2.1 _ (unit_uj (StandardBasisEmbedding.blk_unitary hg)) v
  have hirr : ∀ S : Submodule ℂ Vp, (∀ g ∈ UWset k r (z0 k r), ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    exact hπ.2.2.2.2.2.1 S le_top (fun g hg v hv => hS _ (StandardBasisEmbedding.mem_UW hg.1) v hv)
  have hmeas : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)) μW := by
    have hc : ContinuousOn (fun x : Mt k r => π' (StandardBasisEmbedding.blk (Matrix.of x))) {x | Matrix.of x ∈ UWset k r (z0 k r)} :=
      (clm_continuousOn π' _ hUR.2.2).comp blk_cont.continuousOn (fun x hx => unit_uj (StandardBasisEmbedding.blk_unitary hx))
    have h1 := hc.aestronglyMeasurable (μ := μW) isClosed_UW.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)}) hae] at h1
    exact h1.congr (hae.mono fun x hx => (congrArg π (StandardBasisEmbedding.eq_blockW hx)).symm)
  rw [schur_orthogonality_unitary_rep (UWset k r (z0 k r)) μW hμW.2.2.1 (fun g hg => (uw_inv hg).2) (fun g hg => hμW.2.2.2 g hg)
    π hmul hunit hirr hmeas Y' ξ ξ η]
  have e1 : ⟪η, ξ⟫_ℂ = (starRingEnd ℂ) α⁻¹ := by
    rw [hηdef, inner_smul_left, inner_self_eq_norm_sq_to_K, hξn]; simp
  have e2 : ⟪ξ, Y'⟫_ℂ = (starRingEnd ℂ) α * ⟪T.w, Y⟫_ℂ := by
    rw [← hUY, hα, inner_smul_left]
  rw [e1, e2, map_inv₀]
  have hc0 : (starRingEnd ℂ) α ≠ 0 := by simpa using hα0
  field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants

variable {k r : ℕ}

theorem inUJ_kmul {ε : Fin (2 * r + k + 1) → Bool} {κ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hκ : κ ∈ Kset ε) : inUJ ε (κ * g) ↔ inUJ ε g := by
  have hJ : κᴴ * Jm ε * κ = Jm ε := HW.torep_inUJ ε hκ
  unfold inUJ
  rw [Matrix.conjTranspose_mul]
  have e : gᴴ * κᴴ * Jm ε * (κ * g) = gᴴ * (κᴴ * Jm ε * κ) * g := by simp only [Matrix.mul_assoc]
  rw [e, hJ]

theorem psiM_zero {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : ¬ inUJ ε g) :
    S7.PsiM T μ g = 0 := by
  unfold S7.PsiM
  rw [dif_neg]
  rintro ⟨k', X, hX, rfl⟩
  exact hg (S7.inUJ_kexp k' hX)

theorem psiM_K {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) {κ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hκ : κ ∈ Kset ε)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    S7.PsiM T μ (κ * g) = HW.torepSig T κ * S7.PsiM T μ g := by
  by_cases hg : inUJ ε g
  · have h := S7.psiM_equiv T μ (HW.torepK ε hκ) 1 hg
    rw [HW.toMK_torepK] at h
    have h1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
    rw [h1, Matrix.mul_one] at h
    rw [h, HW.torepSig_of_mem T hκ]
    have : T.op 1 = 1 := by simp [S7.KType.op]
    rw [this, mul_one]
  · rw [psiM_zero T μ hg, psiM_zero T μ (fun h => hg ((inUJ_kmul hκ).1 h)), mul_zero]

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) : Continuous (Formalism.MainNotions.S.psiGen k r z c) := by
  unfold Formalism.MainNotions.S.psiGen
  have h : ∀ a : Fin r, Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      Formalism.MainNotions.S.ellA k r z g a) := by
    intro a
    unfold Formalism.MainNotions.S.ellA
    split_ifs
    · exact (continuous_apply _).comp (continuous_apply _)
    · simp only [Matrix.mulVec, dotProduct]
      exact continuous_finsetSum _ fun j _ =>
        (continuous_id.matrix_elem _ j).mul continuous_const
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (h a)))))

theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ‖Formalism.MainNotions.S.psiGen k r z c g‖ = 1 := by
  unfold Formalism.MainNotions.S.psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem coef_meas {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)
    (μ : Fin (2 * r + k + 1) → ℤ) (hcont : ContinuousOn (S7.PsiM T μ) (UJset ε)) (v w : T.V) :
    Measurable (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) := by
  classical
  set s : Set (Mt k r) := {M | inUJ ε (Matrix.of M)}
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have hs : IsClosed s :=
    isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  have hΦ : ContinuousOn (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) s := by
    have h1 : ContinuousOn (fun M : Mt k r => S7.PsiM T μ (Matrix.of M)) s :=
      hcont.comp hc.continuousOn (fun M hM => hM)
    exact continuousOn_const.inner (h1.clm_apply continuousOn_const)
  have he : (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) =
      s.piecewise (fun M : Mt k r => ⟪w, S7.PsiM T μ (Matrix.of M) v⟫_ℂ) (fun _ => 0) := by
    funext M
    by_cases hM : M ∈ s
    · rw [Set.piecewise_eq_of_mem _ _ _ hM]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hM, psiM_zero T μ hM]; simp
  rw [he]
  exact hΦ.measurable_piecewise continuousOn_const hs.measurableSet

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS Formalism.QuantumDeterminants SchurOrthogonalityLemmas

theorem b7b : WhittakerSchurOrthogonality := by
  intro k r ε Λ T μ P u c Vp _ _ _ π ξ μW μN _ hP hW hπ hξn hξ hΛ hμW hμ1 _ hcont hint
  classical
  set ψ := Formalism.MainNotions.S.psiGen k r (z0 k r) c with hψ
  set π' : Matrix (Fin k) (Fin k) ℂ → (Vp →L[ℂ] Vp) := fun h => π (Formalism.MainNotions.S.blockW k r h) with hπ'
  have hUR := hπ.2.2.1
  have : FiniteDimensional ℂ Vp := hπ.2.1
  have : IsProbabilityMeasure μW := ⟨hμ1⟩
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r (z0 k r) := by
    rw [ae_iff]; simpa using hμW.2.2.1
  have haeP : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r (z0 k r) :=
    Measure.quasiMeasurePreserving_fst.ae hae
  set F : Mt k r × Mt k r → Vp := fun p =>
    psiCoef T μ P T.w T.w ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1)) •
      chiInv ψ π (Matrix.of p.1) (Matrix.of p.2) ξ with hF
  have hA : aaFun T μ P μW μN ψ π T.w T.w ξ 1 1 = ∫ p, F p ∂(μW.prod μN) := rfl
  have hK : ∀ h : Mt k r, Matrix.of h ∈ UWset k r (z0 k r) → P * Matrix.of h * P⁻¹ ∈ Kset ε := by
    intro h hh
    rw [StandardBasisEmbedding.eq_blockW hh, cay_kE hP hW]
    exact kE_mem_Kset (fun a ha => cay_eps hP hW a ha) (StandardBasisEmbedding.blk_unitary hh)
  have hPsi : ∀ h m : Mt k r, Matrix.of h ∈ UWset k r (z0 k r) →
      S7.PsiM T μ (P * (Matrix.of h * Matrix.of m) * P⁻¹) =
        HW.torepSig T (P * Matrix.of h * P⁻¹) * S7.PsiM T μ (P * Matrix.of m * P⁻¹) := by
    intro h m hh
    have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
    have e : P * (Matrix.of h * Matrix.of m) * P⁻¹ = (P * Matrix.of h * P⁻¹) * (P * Matrix.of m * P⁻¹) := by
      have : (P * Matrix.of h * P⁻¹) * (P * Matrix.of m * P⁻¹) =
          P * Matrix.of h * (P⁻¹ * P) * Matrix.of m * P⁻¹ := by simp only [Matrix.mul_assoc]
      rw [this, Matrix.nonsing_inv_mul _ hu]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [e, psiM_K T μ (hK h hh)]
  have hunit : ∀ g ∈ UWset k r (z0 k r), ∀ v, ‖π g v‖ = ‖v‖ := by
    intro g hg v
    rw [StandardBasisEmbedding.eq_blockW hg]
    exact hUR.2.1 _ (unit_uj (StandardBasisEmbedding.blk_unitary hg)) v
  have hinvG : ∀ h : Mt k r, Matrix.of h ∈ UWset k r (z0 k r) → (Matrix.of h)⁻¹ ∈ UWset k r (z0 k r) := by
    intro h hh
    rw [(uw_inv hh).1]
    exact StandardBasisEmbedding.mem_UW (Unitary.star_mem (StandardBasisEmbedding.blk_unitary hh))
  have hFm : AEStronglyMeasurable F (μW.prod μN) := by
    have hc0 : Continuous (fun p : Mt k r × Mt k r =>
        (P * ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1)) * P⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
      fun_prop
    have hc1 : Continuous (fun p : Mt k r × Mt k r =>
        (Matrix.of.symm (P * ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1)) * P⁻¹) : Mt k r)) := by
      exact hc0
    have h1 : Measurable (fun p : Mt k r × Mt k r =>
        psiCoef T μ P T.w T.w ((1 : Mat k r)⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * 1))) := by
      exact (coef_meas T μ hcont T.w T.w).comp hc1.measurable
    have h2 : Continuous (fun p : Mt k r × Mt k r => star (ψ (Matrix.of p.2))) :=
      continuous_star.comp ((psiGen_cont _ _).comp continuous_snd)
    have h3 : AEStronglyMeasurable (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹ ξ) (μW.prod μN) := by
      have hc : ContinuousOn (fun x : Mt k r => π' (star (StandardBasisEmbedding.blk (Matrix.of x))) ξ)
          {x | Matrix.of x ∈ UWset k r (z0 k r)} :=
        (hUR.2.2 ξ).comp blk_cont.star.continuousOn
          (fun x hx => unit_uj (Unitary.star_mem (StandardBasisEmbedding.blk_unitary hx)))
      have h0 := hc.aestronglyMeasurable (μ := μW) isClosed_UW.measurableSet
      rw [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r (z0 k r)}) hae] at h0
      have h0' : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)⁻¹ ξ) μW :=
        h0.congr (hae.mono fun x hx => by dsimp only; rw [(uw_inv hx).1])
      exact h0'.comp_fst
    exact h1.aestronglyMeasurable.smul (h2.aestronglyMeasurable.smul h3)
  have hFb : ∀ᵐ p ∂(μW.prod μN), ‖F p‖ ≤ ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ := haeP.mono fun p hp => by
    simp only [hF, chiInv, psiCoef, inv_one, Matrix.one_mul, Matrix.mul_one]
    rw [hPsi _ _ hp, norm_smul, norm_smul, norm_star, hψ, norm_psiGen, one_mul, hunit _ (hinvG _ hp), hξn, mul_one]
    have hA1 : ‖HW.torepSig T (P * Matrix.of p.1 * P⁻¹)‖ ≤ 1 :=
      opNorm_le_one_of_isometry_alt _ ((HW.torep_isURepOn T).2.1 _ (hK _ hp))
    calc ‖⟪T.w, (HW.torepSig T (P * Matrix.of p.1 * P⁻¹) * S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)) T.w⟫_ℂ‖
        ≤ ‖T.w‖ * ‖(HW.torepSig T (P * Matrix.of p.1 * P⁻¹) * S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)) T.w‖ :=
          norm_inner_le_norm _ _
      _ ≤ 1 * (‖HW.torepSig T (P * Matrix.of p.1 * P⁻¹) * S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ * 1) := by
          rw [T.w_norm]
          gcongr
          calc _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
            _ = _ := by rw [T.w_norm]
      _ ≤ ‖HW.torepSig T (P * Matrix.of p.1 * P⁻¹)‖ * ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ := by
          rw [one_mul, mul_one]; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖ := by gcongr
      _ = _ := one_mul _
  have hFi : Integrable F (μW.prod μN) := by
    have hφ : Integrable (fun p : Mt k r × Mt k r => ‖S7.PsiM T μ (P * Matrix.of p.2 * P⁻¹)‖) (μW.prod μN) := by
      have := (integrable_const (1 : ℝ) (μ := μW)).mul_prod hint
      simpa using this
    exact hφ.mono' hFm hFb
  rw [hA, ← integral_inner hFi ξ, integral_prod_symm _ (hFi.const_inner ξ)]
  have hin : ∀ m : Mt k r, ∫ h, ⟪ξ, F (h, m)⟫_ℂ ∂μW =
      (Module.finrank ℂ Vp : ℂ)⁻¹ * (psiCoef T μ P T.w T.w (Matrix.of m) * starRingEnd ℂ (ψ (Matrix.of m))) := by
    intro m
    have hpt : ∀ᵐ h ∂μW, ⟪ξ, F (h, m)⟫_ℂ = starRingEnd ℂ (ψ (Matrix.of m)) *
        (⟪ξ, π (Matrix.of h)⁻¹ ξ⟫_ℂ * ⟪T.w, HW.torepSig T (P * Matrix.of h * P⁻¹)
          (S7.PsiM T μ (P * Matrix.of m * P⁻¹) T.w)⟫_ℂ) := hae.mono fun h hh => by
      simp only [hF, chiInv, psiCoef, inv_one, Matrix.one_mul, Matrix.mul_one, inner_smul_right]
      have e : ∀ (A B : T.V →L[ℂ] T.V) (v : T.V), (A * B) v = A (B v) := fun _ _ _ => rfl
      rw [hPsi _ _ hh, e, show star (ψ (Matrix.of m)) = starRingEnd ℂ (ψ (Matrix.of m)) from rfl]
      ring
    rw [integral_congr_ae hpt, integral_const_mul, schur_orthogonality_whittaker T π hP hW hπ hξn hξ hΛ hμW hμ1]
    simp only [psiCoef]
    ring
  simp only [hin]
  rw [integral_const_mul]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end
