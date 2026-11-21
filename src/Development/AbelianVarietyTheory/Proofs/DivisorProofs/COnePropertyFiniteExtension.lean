import Mathlib
import BuildAid.ForwardExisting

section
section
open IsLocalRing

namespace GlobalTheory

open MvPolynomial

theorem norm_comp_homogeneous_isHomogeneous :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n d : ℕ)
      (f : MvPolynomial (Fin n) L), f.IsHomogeneous d →
      ∃ F : MvPolynomial (Fin n × Fin (Module.finrank K L)) K,
        F.IsHomogeneous (d * Module.finrank K L) ∧
        ∀ y : Fin n × Fin (Module.finrank K L) → K, MvPolynomial.eval y F =
          Algebra.norm K (MvPolynomial.eval
            (fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j) f) := by
  intro K L _ _ _ _ n d f hf
  classical
  set m := Module.finrank K L
  set b := Module.finBasis K L
  let g : Fin n → MvPolynomial (Fin n × Fin m) L := fun i => ∑ j, X (i, j) * C (b j)
  have hg : ∀ i, (g i).IsHomogeneous 1 := by
    intro i
    refine IsHomogeneous.sum _ _ _ (fun j _ => ?_)
    simpa using (isHomogeneous_X L (i, j)).mul (isHomogeneous_C _ (b j))
  let G : MvPolynomial (Fin n × Fin m) L := bind₁ g f
  have hG : G.IsHomogeneous d := by simpa [G, aeval_eq_bind₁] using hf.aeval g hg
  have hGev : ∀ y : Fin n × Fin m → K, eval (fun p => algebraMap K L (y p)) G =
      eval (fun i => ∑ j, algebraMap K L (y (i, j)) * b j) f := by
    intro y
    have key : ∀ (φ : MvPolynomial (Fin n) L) (x : Fin n × Fin m → L),
        eval x (bind₁ g φ) = eval (fun i => eval x (g i)) φ := by
      intro φ x
      induction φ using MvPolynomial.induction_on <;> simp_all
    rw [show G = bind₁ g f from rfl, key]
    congr 2
    funext i
    simp [g]
    rfl
  let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin m) K) :=
    fun i j => ∑ s ∈ G.support, monomial s (Algebra.leftMulMatrix b (coeff s G) i j)
  have hM : ∀ i j, (M i j).IsHomogeneous d := by
    intro i j
    refine IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ ?_)
    have := hG (mem_support_iff.mp hs)
    rwa [Finsupp.degree_eq_weight_one]
  refine ⟨M.det, ?_, ?_⟩
  · rw [Matrix.det_apply']
    refine IsHomogeneous.sum _ _ _ (fun σ _ => ?_)
    have hp : (∏ i, M (σ i) i).IsHomogeneous (d * m) := by
      have := IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => d) (fun i _ => hM _ _)
      simpa [mul_comm] using this
    have hε : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n × Fin m) K).IsHomogeneous 0 := by
      rw [← map_intCast (C : K →+* MvPolynomial (Fin n × Fin m) K)]
      exact isHomogeneous_C _ _
    simpa using hε.mul hp
  · intro y
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det b, ← hGev]
    congr 1
    ext i j
    show eval y (M i j) = _
    simp only [M, map_sum, eval_monomial]
    rw [eval_eq' _ G, map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have : coeff s G * ∏ k, (algebraMap K L (y k)) ^ (s k) = (∏ k, y k ^ s k) • coeff s G := by
      rw [Algebra.smul_def, mul_comm]
      simp [map_prod, map_pow]
    rw [this, map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm, Finsupp.prod_fintype]
    simp

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHomogeneous_eval_eq_norm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → ∃ F : MvPolynomial (Fin n × Fin (Module.finrank K L)) K, F.IsHomogeneous (d * Module.finrank K L) ∧ ∀ y : Fin n × Fin (Module.finrank K L) → K, MvPolynomial.eval y F = Algebra.norm K (MvPolynomial.eval (fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j) f) := by
  atlas_forward_decl GlobalTheory.norm_comp_homogeneous_isHomogeneous
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem c_one_of_finite_extension : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], (∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) → (∀ (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → L, x ≠ 0 ∧ MvPolynomial.eval x f = 0) := by
  intro K L _ _ _ _ hK n d f hf hd hdn
  obtain ⟨F, hFh, hFe⟩ := GlobalTheory.T.exists_isHomogeneous_eval_eq_norm K L n d f hf
  have hm0 : 0 < Module.finrank K L := Module.finrank_pos
  let e : Fin n × Fin (Module.finrank K L) ≃ Fin (n * Module.finrank K L) := finProdFinEquiv
  have hG : (MvPolynomial.rename e F).IsHomogeneous (d * Module.finrank K L) := hFh.rename_isHomogeneous
  obtain ⟨z, hz0, hz⟩ := hK (n * Module.finrank K L) (d * Module.finrank K L) (MvPolynomial.rename e F) hG
    (Nat.mul_pos hd hm0) (Nat.mul_lt_mul_of_pos_right hdn hm0)
  set y : Fin n × Fin (Module.finrank K L) → K := z ∘ e with hy
  rw [MvPolynomial.eval_rename] at hz
  have hy0 : y ≠ 0 := by
    intro h
    apply hz0
    funext k
    have := congrFun h (e.symm k)
    simpa [hy] using this
  refine ⟨fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j, ?_, ?_⟩
  · intro hx
    apply hy0
    funext ⟨i, j⟩
    have hi := congrFun hx i
    simp only [Pi.zero_apply] at hi
    have hli := (Module.finBasis K L).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun j => y (i, j)) (by simpa [Algebra.smul_def] using hi) j
    simpa using this
  · have := hFe y
    rw [hz] at this
    exact (Algebra.norm_eq_zero_iff (R := K)).mp this.symm

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.c_one_property_finite_extension : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], (∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) → (∀ (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → L, x ≠ 0 ∧ MvPolynomial.eval x f = 0) := by
  atlas_forward_decl GlobalTheory.c_one_of_finite_extension
end
