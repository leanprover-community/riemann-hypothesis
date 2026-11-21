import Mathlib

section
namespace GlobalTheory.IntegralCriterion

theorem main : ∀ (k : Type) [inst : Field k] (n : ℕ) (v : Fin (n + (1 : ℕ)) → k), v ≠ (0 : Fin (n + (1 : ℕ)) → k) → ∃ (P : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k), IsUnit P ∧ ∀ (a : Fin (n + (1 : ℕ))), P a (0 : Fin (n + (1 : ℕ))) = v a := by
  intro k _ n v hv
  set e0 : Fin (n + 1) → k := Pi.single 0 1 with he0def
  have he0 : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e0] at this
  let f : (k ∙ e0) ≃ₗ[k] (k ∙ v) :=
    (LinearEquiv.toSpanNonzeroSingleton k _ e0 he0).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton k _ v hv
  have hf : (f ⟨e0, Submodule.mem_span_singleton_self e0⟩ : Fin (n + 1) → k) = v := by
    have h1 : (⟨e0, Submodule.mem_span_singleton_self e0⟩ : k ∙ e0) =
        LinearEquiv.toSpanNonzeroSingleton k _ e0 he0 1 := by
      ext; simp
    simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
    simp
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hge : g e0 = v := by
    rw [← hf, hg]
  refine ⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩
  · refine ⟨⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)),
      LinearMap.toMatrix' (g.symm : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩, rfl⟩
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
  · intro a
    rw [LinearMap.toMatrix'_apply]
    change g e0 a = v a
    rw [hge]

end GlobalTheory.IntegralCriterion
end

section
namespace GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues

open Module

theorem exists_common_eigenvector {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (f : ι → Module.End k V)
    (hcomm : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ →
      (∀ i, ∀ w ∈ W, (f i : V → V) w ∈ W) →
        ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ i, ∃ c : k, (f i : V → V) x = c • x := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hW hinv
  by_cases hs : ∀ i, ∃ c : k, ∀ w ∈ W, f i w = c • w
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨x, hx, hx0, fun i => let ⟨c, hc⟩ := hs i; ⟨c, hc x hx⟩⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    let g : Module.End k W := (f i).restrict (fun w hw => hinv i w hw)
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue g
    obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
    have hgv : g v = c • v := hv.apply_eq_smul
    have hv0 : v ≠ 0 := hv.2
    set W' : Submodule k V := W ⊓ Module.End.eigenspace (f i) c with hW'
    have hvW' : (v : V) ∈ W' := by
      refine ⟨v.2, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := congrArg Subtype.val hgv
      simpa [g] using this
    have hW'ne : W' ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hvW'
      exact hv0 (Subtype.ext hvW')
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h
      obtain ⟨w, hw, hne⟩ := hi c
      have : w ∈ W' := h ▸ hw
      exact hne ((Module.End.mem_eigenspace_iff).mp this.2)
    have hdlt : Module.finrank k W' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hinv' : ∀ j, ∀ w ∈ W', (f j : V → V) w ∈ W' := by
      intro j w hw
      refine ⟨hinv j w hw.1, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h1 : f i w = c • w := (Module.End.mem_eigenspace_iff).mp hw.2
      have h2 := congrArg (fun F : Module.End k V => F w) (hcomm i j)
      simp only [Module.End.mul_apply] at h2
      rw [h2, h1, map_smul]
    obtain ⟨x, hx, hx0, hxe⟩ := ih _ hdlt W' rfl hW'ne hinv'
    exact ⟨x, hx.1, hx0, hxe⟩

theorem target : ∀ {k ι V : Type} [inst : Field k] [IsAlgClosed k] [inst_2 : AddCommGroup V] [inst_3 : Module k V] [FiniteDimensional k V] (f : ι → Module.End k V), (∀ (i j : ι), f i * f j = f j * f i) → ∀ (d : ℕ) (W : Submodule k V), Module.finrank k ↥W = d → W ≠ ⊥ → (∀ (i : ι), ∀ w ∈ W, (f i : V → V) w ∈ W) → ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : k), (f i : V → V) x = c • x :=
  fun f hc => exists_common_eigenvector f hc

end GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
end

section
open scoped BigOperators

namespace GlobalTheory.CommTriang

theorem exists_common_eigenvector_commuting {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : ι → Module.End k V) (hc : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ → (∀ i, ∀ w ∈ W, f i w ∈ W) →
      ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : k, f i x = c • x := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target
  | (apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues.target ..)

theorem exists_common_eigenvector : ∀ (k ι : Type) [Field k] [IsAlgClosed k] (n : ℕ)
    (T : ι → Matrix (Fin (n+1)) (Fin (n+1)) k), (∀ i j, T i * T j = T j * T i) →
    ∃ v : Fin (n+1) → k, v ≠ 0 ∧ ∃ χ : ι → k, ∀ i, (T i).mulVec v = χ i • v := by
  intro k ι _ _ n T hT
  have hc : ∀ i j, Matrix.toLin' (T i) * Matrix.toLin' (T j) = Matrix.toLin' (T j) * Matrix.toLin' (T i) := by
    intro i j
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hT]
  obtain ⟨x, -, hx0, hx⟩ := exists_common_eigenvector_commuting (fun i => Matrix.toLin' (T i)) hc _ ⊤ rfl
    (by simp) (fun _ _ _ => Submodule.mem_top)
  choose χ hχ using hx
  exact ⟨x, hx0, χ, fun i => by simpa using hχ i⟩

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

theorem exists_unit_col_zero : ∀ (k : Type) [Field k] (n : ℕ) (v : Fin (n+1) → k), v ≠ 0 →
    ∃ P : Matrix (Fin (n+1)) (Fin (n+1)) k, IsUnit P ∧ ∀ a, P a 0 = v a := by
  first
  | exact @_root_.GlobalTheory.IntegralCriterion.main
  | exact _root_.GlobalTheory.IntegralCriterion.main
  | (apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralCriterion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralCriterion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralCriterion.main ..)

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

theorem lift_eigen : ∀ (k ι V : Type) [Field k] [AddCommGroup V] [Module k V] (f : ι → Module.End k V) (v u : V) (χ μ r : ι → k),
    (∀ i j, f i * f j = f j * f i) → v ≠ 0 → (∀ t : k, u + t • v ≠ 0) → (∀ i, f i v = χ i • v) →
    (∀ i, f i u = μ i • u + r i • v) → ∃ x : V, x ≠ 0 ∧ ∀ i, f i x = μ i • x := by
  intro k ι V _ _ _ f v u χ μ r hc hv0 hu0 hv hu
  by_cases h : ∀ i, χ i = μ i
  · exact ⟨v, hv0, fun i => by rw [hv, h]⟩
  push_neg at h
  obtain ⟨i₀, hi₀⟩ := h
  have hd : μ i₀ - χ i₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hi₀)
  set t : k := r i₀ / (μ i₀ - χ i₀) with ht
  have htd : t * (μ i₀ - χ i₀) = r i₀ := div_mul_cancel₀ _ hd
  have hfx : ∀ j, f j (u + t • v) = μ j • (u + t • v) + (r j + t * χ j - t * μ j) • v := by
    intro j
    rw [map_add, map_smul, hu, hv]
    module
  have h0 : f i₀ (u + t • v) = μ i₀ • (u + t • v) := by
    rw [hfx]
    have : r i₀ + t * χ i₀ - t * μ i₀ = 0 := by rw [← htd]; ring
    rw [this, zero_smul, add_zero]
  obtain ⟨x, hx⟩ : ∃ x, x = u + t • v := ⟨_, rfl⟩
  rw [← hx] at hfx h0
  refine ⟨x, hx ▸ hu0 t, fun j => ?_⟩
  have e1 : f i₀ (f j x) = f j (f i₀ x) := by
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
  rw [h0, map_smul, hfx j, map_add, map_smul, map_smul, h0, hv] at e1
  have e2 : ((r j + t * χ j - t * μ j) * (χ i₀ - μ i₀)) • v = 0 := by
    linear_combination (norm := module) e1
  rcases smul_eq_zero.mp e2 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rw [hfx j, h, zero_smul, add_zero]
    · exact absurd (sub_eq_zero.mp h) hi₀
  · exact absurd h hv0

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang

open Matrix

def blockOne {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n+1)) (Fin (n+1)) k :=
  Matrix.of fun a b => Fin.cases (motive := fun _ => k) (Fin.cases (motive := fun _ => k) 1 (fun _ => 0) b)
    (fun a' => Fin.cases (motive := fun _ => k) 0 (fun b' => Q a' b') b) a

section
variable {k : Type} [Field k] {n : ℕ}

@[simp] theorem blockOne_zero_zero (Q : Matrix (Fin n) (Fin n) k) : blockOne Q 0 0 = 1 := rfl
@[simp] theorem blockOne_zero_succ (Q : Matrix (Fin n) (Fin n) k) (b : Fin n) : blockOne Q 0 b.succ = 0 := rfl
@[simp] theorem blockOne_succ_zero (Q : Matrix (Fin n) (Fin n) k) (a : Fin n) : blockOne Q a.succ 0 = 0 := rfl
@[simp] theorem blockOne_succ_succ (Q : Matrix (Fin n) (Fin n) k) (a b : Fin n) : blockOne Q a.succ b.succ = Q a b := rfl

theorem blockOne_mul (Q R : Matrix (Fin n) (Fin n) k) : blockOne Q * blockOne R = blockOne (Q * R) := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockOne_one : blockOne (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext a b
  cases a using Fin.cases <;> cases b using Fin.cases <;> simp [Matrix.one_apply, Fin.succ_ne_zero] <;> exact (Fin.succ_ne_zero _).symm

theorem conj_succ_succ (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a b : Fin n) :
    (blockOne R * S * blockOne Q) a.succ b.succ = (R * S.submatrix Fin.succ Fin.succ * Q) a b := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem conj_succ_zero (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) (a : Fin n) :
    (blockOne R * S * blockOne Q) a.succ 0 = ∑ c, R a c * S c.succ 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem conj_zero_zero (R Q : Matrix (Fin n) (Fin n) k) (S : Matrix (Fin (n+1)) (Fin (n+1)) k) :
    (blockOne R * S * blockOne Q) 0 0 = S 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

end

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang
open Matrix

theorem isUnit_blockOne {k : Type} [Field k] {n : ℕ} (Q : Matrix (Fin n) (Fin n) k) (hQ : IsUnit Q) :
    IsUnit (blockOne Q) ∧ (blockOne Q)⁻¹ = blockOne Q⁻¹ := by
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have h : blockOne Q * blockOne Q⁻¹ = 1 := by
    rw [blockOne_mul, Matrix.mul_nonsing_inv _ hQd, blockOne_one]
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h), Matrix.inv_eq_right_inv h⟩

theorem exists_triangular (k ι : Type) [Field k] [IsAlgClosed k] : ∀ (n : ℕ) (T : ι → Matrix (Fin n) (Fin n) k),
    (∀ i j, T i * T j = T j * T i) →
    ∃ P : Matrix (Fin n) (Fin n) k, IsUnit P ∧ (∀ i, (P⁻¹ * T i * P).BlockTriangular id) ∧
      ∀ a, ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, (T i).mulVec x = (P⁻¹ * T i * P) a a • x := by
  intro n
  induction n with
  | zero => intro T _; exact ⟨1, isUnit_one, fun i a b _ => a.elim0, fun a => a.elim0⟩
  | succ n ih =>
    intro T hT
    obtain ⟨v, hv0, χ, hv⟩ := exists_common_eigenvector k ι n T hT
    obtain ⟨P₀, hP₀, hP₀v⟩ := exists_unit_col_zero k n v hv0
    have hP₀d : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det P₀).mp hP₀
    have hl : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hP₀d
    have hr : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP₀d
    set S : ι → Matrix (Fin (n+1)) (Fin (n+1)) k := fun i => P₀⁻¹ * T i * P₀ with hSdef
    have hST : ∀ i, P₀ * S i = T i * P₀ := by
      intro i; simp only [hSdef, ← Matrix.mul_assoc, hr, Matrix.one_mul]
    have hSc : ∀ i j, S i * S j = S j * S i := by
      intro i j
      have e : ∀ i j, S i * S j = P₀⁻¹ * (T i * T j) * P₀ := by
        intro i j
        simp only [hSdef, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P₀ P₀⁻¹, hr, Matrix.one_mul]
      rw [e, e, hT]
    set e0 : Fin (n+1) → k := Pi.single 0 1 with he0
    have hPe : P₀.mulVec e0 = v := by
      ext a; simp [he0, Matrix.mulVec, dotProduct, Pi.single_apply, hP₀v]
    have hSe : ∀ i, (S i).mulVec e0 = χ i • e0 := by
      intro i
      have : P₀⁻¹.mulVec v = e0 := by rw [← hPe, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
      simp only [hSdef]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPe, hv, Matrix.mulVec_smul, this]
    have hScol : ∀ i a, S i a 0 = χ i * e0 a := by
      intro i a
      have := congrFun (hSe i) a
      simpa [he0, Matrix.mulVec, dotProduct, Pi.single_apply] using this
    have hS0 : ∀ i (a : Fin n), S i a.succ 0 = 0 := by
      intro i a; rw [hScol]; simp [he0, Fin.succ_ne_zero]
    have hS00 : ∀ i, S i 0 0 = χ i := by
      intro i; rw [hScol]; simp [he0]
    set B : ι → Matrix (Fin n) (Fin n) k := fun i => (S i).submatrix Fin.succ Fin.succ with hBdef
    have hBc : ∀ i j, B i * B j = B j * B i := by
      intro i j; ext a b
      have := congrFun (congrFun (hSc i j) a.succ) b.succ
      simpa [hBdef, Matrix.mul_apply, Fin.sum_univ_succ, hS0] using this
    obtain ⟨Q, hQ, hQtri, hQev⟩ := ih B hBc
    obtain ⟨hDQ, hDQinv⟩ := isUnit_blockOne Q hQ
    refine ⟨P₀ * blockOne Q, hP₀.mul hDQ, ?_⟩
    have hM : ∀ i, (P₀ * blockOne Q)⁻¹ * T i * (P₀ * blockOne Q) = blockOne Q⁻¹ * S i * blockOne Q := by
      intro i
      rw [Matrix.mul_inv_rev, hDQinv]
      simp only [hSdef, Matrix.mul_assoc]
    refine ⟨?_, ?_⟩
    · intro i a b hab
      rw [hM]
      cases a using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ a =>
        cases b using Fin.cases with
        | zero => rw [conj_succ_zero]; simp [hS0]
        | succ b =>
          rw [conj_succ_succ]
          exact hQtri i (by simpa using hab)
    · intro a
      cases a using Fin.cases with
      | zero =>
        refine ⟨v, hv0, fun i => ?_⟩
        rw [hM, conj_zero_zero, hS00, hv]
      | succ a =>
        obtain ⟨y, hy0, hy⟩ := hQev a
        set μ : ι → k := fun i => (Q⁻¹ * B i * Q) a a with hμ
        set u : Fin (n+1) → k := Fin.cons 0 y with hu
        obtain ⟨x', hx'0, hx'⟩ := lift_eigen k ι (Fin (n+1) → k) (fun i => Matrix.toLin' (S i)) e0 u χ μ
          (fun i => ∑ b, S i 0 b.succ * y b)
          (by intro i j; rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hSc])
          (by simp [he0])
          (by
            intro t h
            obtain ⟨b, hb⟩ := Function.ne_iff.mp hy0
            have := congrFun h b.succ
            simp [hu, he0, Fin.succ_ne_zero] at this
            exact hb this)
          (fun i => by simpa using hSe i)
          (by
            intro i
            ext c
            cases c using Fin.cases with
            | zero => simp [hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
            | succ c =>
              have hyi : (B i).mulVec y = μ i • y := hy i
              have := congrFun hyi c
              simp only [hBdef, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.smul_apply, smul_eq_mul] at this
              simp [hu, he0, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hS0, Fin.succ_ne_zero, this])
        refine ⟨P₀.mulVec x', ?_, fun i => ?_⟩
        · intro h
          apply hx'0
          apply (Matrix.mulVec_injective_iff_isUnit.mpr hP₀)
          rw [h, Matrix.mulVec_zero]
        · have hx := hx' i
          simp only [Matrix.toLin'_apply] at hx
          rw [hM, conj_succ_succ, Matrix.mulVec_mulVec, ← hST, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

end GlobalTheory.CommTriang

namespace GlobalTheory.CommTriang
open Matrix

end GlobalTheory.CommTriang
end
