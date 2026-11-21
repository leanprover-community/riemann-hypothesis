import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.VnuMapZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun

section
noncomputable section

open Matrix

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

theorem symmetricMeasure_l2Norm_eq_resolutionL2 (φ : LaC N nu) : ((l2 φ : ℝ) : ℂ) = ipl φ φ := by
  unfold l2 ipl
  rw [finsum_eq_sum_of_fintype]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem ipl_zero_left (ψ : LaC N nu) : ipl 0 ψ = 0 := by
  simp [ipl]

theorem ipl_add_left (φ φ' ψ : LaC N nu) : ipl (φ + φ') ψ = ipl φ ψ + ipl φ' ψ := by
  simp [ipl, add_mul, Finset.sum_add_distrib]

theorem ipl_smul_left (c : ℂ) (φ ψ : LaC N nu) : ipl (c • φ) ψ = starRingEnd ℂ c * ipl φ ψ := by
  simp [ipl, Finset.mul_sum, mul_assoc]

theorem isoInvMetric_of (hU : Unit) (hI : InvK) (hS : Stab) (hH : HvCols) (hN : Norm1)
    (hG : Gen) (hW : HW) : IsoInvMetric := by
  intro Lt _ _ N nu
  refine ⟨fun k hk => ⟨fun φ hφ => ⟨hS Lt N nu k φ hφ, ?_⟩, fun hle => ?_⟩, fun ip hip => ?_⟩
  · apply Complex.ofReal_injective
    rw [symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk]
  · rw [hH Lt N nu k]
    apply Complex.ofReal_injective
    rw [symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk, ← symmetricMeasure_l2Norm_eq_resolutionL2, hN Lt N nu hle]
  · have hu : u0 N nu ∈ Vnu N nu := Submodule.subset_span ⟨_, rfl⟩
    have key : ∀ φ ∈ Vnu N nu, ∀ ψ ∈ Vnu N nu, ip φ ψ = ipl φ ψ := by
      intro φ hφ ψ hψ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        obtain ⟨k, hk, c, hc⟩ := hG Lt N nu y
        obtain ⟨ψ', hψ', e1⟩ : ∃ ψ', ψ' ∈ Vnu N nu ∧ ψ = VnuMap nu k ψ' :=
          ⟨_, hS Lt N nu _ ψ hψ, (hI Lt N nu k hk ψ).symm⟩
        have h2 : ip (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ') =
            ipl (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ') := by
          rw [(hip k hk).1 _ hu _ hψ', hW Lt N nu ip hip ψ' hψ', hU Lt N nu k hk]
        rw [hc, hH Lt N nu k, LinearMap.map_smulₛₗ₂, ipl_smul_left, e1, h2, smul_eq_mul]
      | zero => simp [ipl_zero_left]
      | add x y _ _ hx hy => rw [LinearMap.map_add₂, hx, hy, ipl_add_left]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, ipl_smul_left, smul_eq_mul]
    intro φ hφ
    rw [symmetricMeasure_l2Norm_eq_resolutionL2]
    exact key φ hφ φ hφ

end PI.IsoInvMetricW
end
end

section
noncomputable section

open Matrix Classical

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

theorem oe_ge {h N : ℕ} (J : Fin h ↪o Fin N) : ∀ i : Fin h, (i : ℕ) ≤ (J i : ℕ) := by
  intro i
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 : J ⟨n, by omega⟩ < J ⟨n + 1, hn⟩ :=
      J.lt_iff_lt.mpr (Fin.mk_lt_mk.mpr (Nat.lt_succ_self n))
    rw [Fin.lt_def] at h2
    simp only at h1 ⊢
    omega

theorem det_tri {h N : ℕ} (J : Fin h ↪o Fin N) (w : Fin N → ℕ → ℂ)
    (hw : ∀ (a : Fin N) (j : ℕ), j < a → w a j = 0) :
    Matrix.det (Matrix.of fun i j : Fin h => w (J i) (j : ℕ)) = ∏ i : Fin h, w (J i) i := by
  rw [Matrix.det_of_upperTriangular]
  · rfl
  · intro i j hij
    simp only [id] at hij
    simp only [Matrix.of_apply]
    apply hw
    have h1 := oe_ge J i
    have h2 := Fin.lt_def.mp hij
    omega

def dg {Lt : Type} {N : ℕ} (w : Lt → Fin N → ℕ → ℂ) (s : Lt) (i : ℕ) : ℂ :=
  if h : i < N then w s ⟨i, h⟩ i else 0

theorem hv_tri {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (w : Lt → Fin N → ℕ → ℂ) (hw : ∀ s (a : Fin N) (j : ℕ), j < a → w s a j = 0)
    (J : ColChoice N nu) :
    hvC N nu w J = if (∀ s c i, (J s c i : ℕ) = i) then
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg w s i else 0 := by
  have e : hvC N nu w J =
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), w s (J s c i) i := by
    unfold hvC minY
    exact Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ =>
      det_tri (J s c) (w s) (hw s)
  rw [e]
  split_ifs with hstd
  · refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ =>
      Finset.prod_congr rfl fun i _ => ?_
    have hi : (i : ℕ) < N := by
      have := (J s c i).2
      rw [hstd s c i] at this
      exact this
    have : J s c i = ⟨i, hi⟩ := Fin.ext (hstd s c i)
    simp only [dg, hi, dite_true, this]
  · push_neg at hstd
    obtain ⟨s, c, i, hne⟩ := hstd
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply hw
    have := oe_ge (J s c) i
    omega

theorem hv_scalar {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (w : Lt → Fin N → ℕ → ℂ) (hw : ∀ s (a : Fin N) (j : ℕ), j < a → w s a j = 0) :
    hvC N nu w =
      (∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg w s i) • u0 N nu := by
  have h1 : ∀ s (a : Fin N) (j : ℕ), j < a →
      (fun _ : Lt => colsOf (1 : Matrix (Fin N) (Fin N) ℂ)) s a j = 0 := by
    intro s a j hja
    simp only [colsOf]
    split_ifs with hj
    · rw [Matrix.one_apply_ne]
      intro h
      rw [h] at hja
      simp at hja
    · rfl
  funext J
  rw [Pi.smul_apply, smul_eq_mul, u0, hv_tri nu w hw J, hv_tri nu _ h1 J]
  split_ifs with hstd
  · have : ∀ s (c : Fin ((nu s).rowLen 0)) (i : Fin ((nu s).colLen c)),
        dg (fun _ : Lt => colsOf (1 : Matrix (Fin N) (Fin N) ℂ)) s i = 1 := by
      intro s c i
      have hi : (i : ℕ) < N := by
        have := (J s c i).2
        rw [hstd s c i] at this
        exact this
      simp [dg, hi, colsOf]
    simp [this]
  · simp

theorem gen_of (hQ : QR) (hM : HvMap) : Gen := by
  intro Lt _ _ N nu x
  have hq := fun s => hQ N (Matrix.of fun a (j : Fin N) => x s a j)
  choose k hk htri using hq
  refine ⟨k, hk, ?_⟩
  let y := fr (fun s => star (k s)) x
  have hxy : x = fr k y := by
    funext s a j
    have hkk : k s * star (k s) = 1 := Matrix.mem_unitaryGroup_iff.mp (hk s)
    show x s a j = ∑ b, k s a b * ∑ c, star (k s) b c * x s c j
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have : ∀ c, ∑ b, k s a b * star (k s) b c = if a = c then 1 else 0 := fun c => by
      rw [← Matrix.one_apply, ← hkk, Matrix.mul_apply]
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have ytri : ∀ s (a : Fin N) (j : ℕ), j < a → y s a j = 0 := by
    intro s a j hja
    have hjN : j < N := lt_trans hja a.2
    have := htri s a ⟨j, hjN⟩ (Fin.lt_def.mpr hja)
    simpa [y, fr, Matrix.mul_apply] using this
  refine ⟨∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i : Fin ((nu s).colLen c), dg y s i, ?_⟩
  rw [hxy, ← hM Lt N nu k y, hv_scalar nu y ytri, vnuMap_smul, ← hvCols_of hM Lt N nu k]

end PI.IsoInvMetricW
end
end

section
noncomputable section

open Matrix

namespace PI.IsoInvMetricW

open InnerProductSpace

theorem quotient_rank : QR := by
  intro N X
  let f : Fin N → EuclideanSpace ℂ (Fin N) := fun j => (WithLp.equiv 2 _).symm (fun a => X a j)
  have hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N) := finrank_euclideanSpace
  let b := gramSchmidtOrthonormalBasis hd f
  let k : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a j => b j a
  have hinner : ∀ i j, ∑ a, star (b i a) * (f j) a = inner ℂ (b i) (f j) := by
    intro i j
    simp [PiLp.inner_apply, mul_comm]
  have hinner' : ∀ i j, ∑ a, star (b i a) * b j a = inner ℂ (b i) (b j) := by
    intro i j
    simp [PiLp.inner_apply, mul_comm]
  refine ⟨k, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have ho := orthonormal_iff_ite.mp b.orthonormal i j
    simp only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply, Matrix.one_apply]
    rw [hinner', ho]
  · intro a j hja
    have := gramSchmidtOrthonormalBasis_inv_triangular hd f hja
    simp only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply]
    rw [← this, ← hinner]
    rfl

end PI.IsoInvMetricW
end
end

section
noncomputable section

open Matrix Finset

namespace PI.IsoInvMetricW

theorem metric_constant_bound : CB := by
  intro h N A B
  classical
  rw [GenFrameSpan.det_mul_rect]
  have hR : ∀ J : Fin h ↪o Fin N, (A.submatrix id J).det * (B.submatrix J id).det
      = ∑ σ : Equiv.Perm (Fin h), (∏ i, B (J (σ i)) i) * (A.submatrix id (J ∘ σ)).det := by
    intro J
    rw [det_apply (B.submatrix J id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hA : A.submatrix id (J ∘ σ) = (A.submatrix id J).submatrix id σ := by
      ext i k; simp
    rw [hA, det_permute']
    simp only [Units.smul_def, zsmul_eq_mul, submatrix_apply, id]
    ring
  rw [Finset.sum_congr rfl (fun J _ => hR J), ← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (p.1 : Fin h → Fin N) ∘ p.2)
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨J, σ⟩ _ _ ⟨J', σ'⟩ _ _ heq
    have hr : Set.range J = Set.range J' := by
      have h1 : Set.range ((J : Fin h → Fin N) ∘ σ) = Set.range J :=
        σ.surjective.range_comp _
      have h2 : Set.range ((J' : Fin h → Fin N) ∘ σ') = Set.range J' :=
        σ'.surjective.range_comp _
      rw [← h1, ← h2]
      exact congrArg Set.range heq
    have hJ : J = J' := OrderEmbedding.range_inj.mp hr
    subst hJ
    have hσ : σ = σ' := by
      ext i
      have := congrFun heq i
      simp only [Function.comp_apply] at this
      rw [J.injective this]
    rw [hσ]
  · intro f _ hf
    have hinj : Function.Injective f := by
      by_contra hni
      apply hf
      have : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        push Not at hc
        exact hni fun i j e => hc i j e
      obtain ⟨i, j, hij, hne⟩ := this
      rw [Matrix.det_zero_of_column_eq hne (by intro r; simp [hij]), mul_zero]
    set s : Finset (Fin N) := Finset.univ.image f with hs
    have hcard : s.card = h := by
      rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ i, f i ∈ s := fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)
    let g : Fin h → Fin h := fun i => (s.orderIsoOfFin hcard).symm ⟨f i, hmem i⟩
    have hg : ∀ i, s.orderEmbOfFin hcard (g i) = f i := by
      intro i
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp [g]
    have ginj : Function.Injective g := by
      intro i j e
      apply hinj
      rw [← hg i, ← hg j, e]
    let σ : Equiv.Perm (Fin h) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj)
    refine ⟨(s.orderEmbOfFin hcard, σ), Finset.mem_univ _, ?_, ?_⟩
    · have hfi : ∀ i, (s.orderEmbOfFin hcard) (σ i) = f i := fun i => by simp [σ, hg]
      have : ((s.orderEmbOfFin hcard : Fin h ↪o Fin N) : Fin h → Fin N) ∘ σ = f := by
        funext i; exact hfi i
      rw [this]; dsimp only; simp only [hfi]; exact hf
    · funext i; simp [σ, hg]

end PI.IsoInvMetricW
end
end

section
noncomputable section

open Matrix Finset PI.IsoInvMetric

namespace PI.IsoInvMetricW

theorem sum_prod_cc {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
    (F : ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), (Fin ((nu s).colLen c) ↪o Fin N) → ℂ) :
    ∑ J : ColChoice N nu, ∏ s, ∏ c, F s c (J s c) = ∏ s, ∏ c, ∑ K, F s c K := by
  simp_rw [Fintype.prod_sum]
  rfl

theorem hermitian_vector_map : HvMap := by
  intro Lt _ _ N nu f x
  funext I
  simp only [VnuMap, hvC, minY, fr]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [← Finset.prod_mul_distrib]
  refine (sum_prod_cc (fun s c K =>
      (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (K k)).det *
      (Matrix.of fun i j : Fin ((nu s).colLen c) => x s (K i) (j : ℕ)).det)).trans ?_
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  have hcb := metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b)
    (Matrix.of fun (b : Fin N) (j : Fin ((nu s).colLen c)) => x s b (j : ℕ))
  calc _ = ∑ K : Fin ((nu s).colLen c) ↪o Fin N,
        ((Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b).submatrix id K).det *
        ((Matrix.of fun (b : Fin N) (j : Fin ((nu s).colLen c)) => x s b (j : ℕ)).submatrix K id).det := rfl
    _ = _ := hcb.symm
    _ = _ := by
      congr 1

theorem metric_mul : EMul := by
  intro Lt _ _ N nu f g I K
  simp only [E]
  simp_rw [← Finset.prod_mul_distrib]
  refine (sum_prod_cc (fun s c J =>
      (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J k)).det *
      (Matrix.of fun i k : Fin ((nu s).colLen c) => g s (J i) (K s c k)).det)).trans ?_
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  have hcb := metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b)
    (Matrix.of fun (b : Fin N) (k : Fin ((nu s).colLen c)) => g s b (K s c k))
  calc _ = ∑ J : Fin ((nu s).colLen c) ↪o Fin N,
        ((Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b).submatrix id J).det *
        ((Matrix.of fun (b : Fin N) (k : Fin ((nu s).colLen c)) => g s b (K s c k)).submatrix J id).det := rfl
    _ = _ := hcb.symm
    _ = _ := by
      congr 1

end PI.IsoInvMetricW
end
end

section
namespace PI.IsoInvMetricW

theorem isoInvMetric_of_hw (hW : HW) : PI.IsoInvMetric.IsoInvMetric :=
  isoInvMetric_of (unit_of metric_mul) (invK_of metric_mul) (stab_of hermitian_vector_map)
    (hvCols_of hermitian_vector_map) norm1' (gen_of quotient_rank hermitian_vector_map) hW

end PI.IsoInvMetricW
end
