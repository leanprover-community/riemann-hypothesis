import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Formalism.PieriBlockIdeals.PieriColumnMinors.DepthNonnegative
import Formalism.SatakeDualWeyl.Statement
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom

section
section
open Matrix

namespace GlobalTheory

theorem matrix_exists_common_eigenvector_mem :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Set (Matrix (Fin n) (Fin n) K)),
      (∀ A ∈ S, ∀ B ∈ S, Commute A B) → ∀ (E : Submodule K (Fin n → K)), E ≠ ⊥ →
      (∀ A ∈ S, ∀ v ∈ E, A *ᵥ v ∈ E) → ∃ v ∈ E, v ≠ 0 ∧ ∀ A ∈ S, ∃ μ : K, A *ᵥ v = μ • v := by
  intro K _ _ n S hS E hE hst
  obtain ⟨v, hvE, hv0, hv⟩ := exists_common_eigenvector_mem (K := K) (V := Fin n → K)
    (fun A : S => Matrix.toLin' (A : Matrix (Fin n) (Fin n) K))
    (fun i j v => by
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      rw [(hS i i.2 j j.2).eq])
    E hE (fun i v hv => by simpa [Matrix.toLin'_apply] using hst i i.2 v hv)
  refine ⟨v, hvE, hv0, fun A hA => ?_⟩
  obtain ⟨l, hl⟩ := hv ⟨A, hA⟩
  exact ⟨l, by simpa [Matrix.toLin'_apply] using hl⟩

end GlobalTheory
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_eigenvector_mem_of_commute : ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Set (Matrix (Fin n) (Fin n) K)), (∀ A ∈ S, ∀ B ∈ S, Commute A B) → ∀ (E : Submodule K (Fin n → K)), E ≠ ⊥ → (∀ A ∈ S, ∀ v ∈ E, A *ᵥ v ∈ E) → ∃ v ∈ E, v ≠ 0 ∧ ∀ A ∈ S, ∃ μ : K, A *ᵥ v = μ • v := by
  atlas_forward_decl GlobalTheory.matrix_exists_common_eigenvector_mem
end

section
open Matrix

namespace GlobalTheory

theorem finite_joint_eigensystems : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  intro K _ n ι A hc
  let f : ι → Module.End K (Fin n → K) := fun i => Matrix.toLin' (A i)
  have hcf : ∀ i j, Commute (f i) (f j) := by
    intro i j
    exact (hc i j).map Matrix.toLinAlgEquiv'
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcf j i) φ)
  refine (WellFoundedGT.finite_ne_bot_of_iSupIndep hind).subset ?_
  rintro χ ⟨c, hc0, hχ⟩
  show (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥
  intro hbot
  apply hc0
  have hmem : c ∈ ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [Submodule.mem_iInf]
    intro i
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simpa [f] using hχ i
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).mp hmem

end GlobalTheory

alias _root_.GlobalTheory.T.finite_joint_eigenvalues_of_commute := _root_.GlobalTheory.finite_joint_eigensystems
end

section
section
open Matrix

namespace GlobalTheory

theorem exists_matrices_intertwining_of_semilinear : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l) (I M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∃ (n : ℕ) (σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V), (∀ p, σ p = 0 → ∀ x : M, p • x = 0) ∧ Function.Injective e ∧ (∀ c, e c ∈ Submodule.span (PadicAlgCl l) (Set.range j)) ∧ ∀ i c, Tq i (e c) = e ((σ (MvPolynomial.X i)).map emb *ᵥ c) := by
  intro l _ O _ _ _ emb I M _ _ _ _ hfin htf V _ _ j Tq hli hX
  have : NoZeroSMulDivisors O M := ⟨fun {c x} h => htf c x h⟩
  have : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let n := Module.finrank O M
  let b : Module.Basis (Fin n) O M := Module.finBasis O M
  let σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lsmul O O M)
  let e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V :=
    ∑ a, (LinearMap.proj a : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] PadicAlgCl l).smulRight (j (b a))
  have he : ∀ c, e c = ∑ a, c a • j (b a) := by
    intro c
    simp [e, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hσ : ∀ p a, p • b a = ∑ k, σ p k a • b k := by
    intro p a
    conv_lhs => rw [← b.sum_repr (p • b a)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp [σ, LinearMap.toMatrixAlgEquiv_apply]
  refine ⟨n, σ, e, ?_, ?_, ?_, ?_⟩
  · intro p hp x
    have h1 : (Algebra.lsmul O O M) p = 0 := by
      apply (LinearMap.toMatrixAlgEquiv b).injective
      simpa [σ] using hp
    simpa using LinearMap.congr_fun h1 x
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hl := Fintype.linearIndependent_iff.mp (hli n b b.linearIndependent) c (by rw [← he]; exact hc)
    funext a
    exact hl a
  · intro c
    rw [he]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b a, rfl⟩)
  · intro i c
    have key : ∀ a, Tq i (j (b a)) = ∑ k, emb (σ (MvPolynomial.X i) k a) • j (b k) := by
      intro a
      rw [← hX, hσ, map_sum]
      simp [LinearMap.map_smulₛₗ]
    rw [he, he, map_sum]
    simp_rw [LinearMap.map_smul, key, Finset.smul_sum, smul_smul]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]

end GlobalTheory
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrices_intertwining_of_semilinear_alt : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l) (I M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∃ (n : ℕ) (σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V), (∀ p, σ p = 0 → ∀ x : M, p • x = 0) ∧ Function.Injective e ∧ (∀ c, e c ∈ Submodule.span (PadicAlgCl l) (Set.range j)) ∧ ∀ i c, Tq i (e c) = e ((σ (MvPolynomial.X i)).map emb *ᵥ c) := by
  atlas_forward_decl GlobalTheory.exists_matrices_intertwining_of_semilinear
end

section
namespace GlobalTheory.EigenvalueNormAtMostOne

theorem norm_eigenvalue_le_one_of_entries {K : Type} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (c : Fin n → K) (μ : K) (hc : c ≠ 0) (h : A.mulVec c = μ • c) : ‖μ‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hc
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖c j‖)
    ⟨k, Finset.mem_univ k⟩
  have hpos : 0 < ‖c i‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hk) (hi k (Finset.mem_univ k))
  have hrow : ∑ j, A i j * c j = μ * c i := by
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct] using this
  have hle : ‖∑ j, A i j * c j‖ ≤ ‖c i‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j hj
    rw [norm_mul]
    calc ‖A i j‖ * ‖c j‖ ≤ 1 * ‖c i‖ :=
          mul_le_mul (hA i j) (hi j hj) (norm_nonneg _) zero_le_one
      _ = ‖c i‖ := one_mul _
  rw [hrow, norm_mul] at hle
  exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos

theorem norm_eigenvalue_le_one :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (O : Type) [inst_1 : CommRing O]
      (emb : O →+* PadicAlgCl l), (∀ (a : O), ‖(emb : O → PadicAlgCl l) a‖ ≤ (1 : ℝ)) →
      ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l) (μ : PadicAlgCl l),
        c ≠ (0 : Fin n → PadicAlgCl l) →
        Matrix.mulVec (Matrix.map N (⇑emb : O → PadicAlgCl l)) c = μ • c → ‖μ‖ ≤ (1 : ℝ) := by
  intro l _ O _ emb hemb n N c μ hc h
  exact norm_eigenvalue_le_one_of_entries _ (fun i j => hemb (N i j)) c μ hc h

end GlobalTheory.EigenvalueNormAtMostOne
end

section
section
open Matrix

namespace GlobalTheory.DeligneSerre

theorem eq_top_of_isUnit_det (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ)
    (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O) (m : Ideal R) (hker : ∀ p, σ p = 0 → p ∈ m) (p : R)
    (hp : p ∈ m) (hu : IsUnit (σ p).det) : m = ⊤ := by
  set f := (σ p).charpoly with hf
  have hq : Polynomial.aeval p f ∈ m := by
    apply hker
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]
  have h0 : algebraMap O R (f.coeff 0) ∈ m := by
    have h := hq
    rw [← Polynomial.X_mul_divX_add f, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact (Submodule.add_mem_iff_right m (m.mul_mem_right _ hp)).1 h
  have hc : IsUnit (f.coeff 0) := by
    rw [Matrix.det_eq_sign_charpoly_coeff] at hu
    exact isUnit_of_mul_isUnit_right hu
  exact Ideal.eq_top_of_isUnit_mem m h0 (hc.map _)

theorem eigen_ringHom (R : Type) [CommRing R] (K : Type) [Field K] (n : ℕ)
    (τ : R →+* Matrix (Fin n) (Fin n) K) (c : Fin n → K) (hc : c ≠ 0)
    (h : ∀ p, ∃ μ : K, τ p *ᵥ c = μ • c) : ∃ χ : R →+* K, ∀ p, τ p *ᵥ c = χ p • c := by
  choose μ hμ using h
  have inj : ∀ a b : K, a • c = b • c → a = b := fun a b h => smul_left_injective K hc h
  refine ⟨{ toFun := μ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hμ⟩
  · apply inj; rw [← hμ, map_one, one_mulVec, one_smul]
  · intro a b; apply inj
    rw [← hμ, map_mul, ← mulVec_mulVec, hμ b, mulVec_smul, hμ a, smul_smul, mul_comm (μ b)]
  · apply inj; rw [← hμ, map_zero, zero_mulVec, zero_smul]
  · intro a b; apply inj; rw [← hμ, map_add, add_mulVec, hμ a, hμ b, add_smul]

theorem norm_det_eq_one (K : Type) [NormedField K] [IsAlgClosed K] (n : ℕ)
    (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ μ : K, (∃ c : Fin n → K, c ≠ 0 ∧ N *ᵥ c = μ • c) → ‖μ‖ = 1) : ‖N.det‖ = 1 := by
  have hroot : ∀ μ ∈ N.charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    apply h
    have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
    have hr := (Polynomial.mem_roots hne).1 hμ
    rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hr
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hr
    refine ⟨v, hv0, ?_⟩
    rw [sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, mulVec_diagonal]
  rw [Matrix.det_eq_prod_roots_charpoly]
  revert hroot
  generalize N.charpoly.roots = s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro hs
    rw [Multiset.prod_cons, norm_mul, hs a (Multiset.mem_cons_self a s),
      ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)), one_mul]

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem norm_eigen_le_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l)
    (μ : PadicAlgCl l) (hc : c ≠ 0) (hN : N.map emb *ᵥ c = μ • c) : ‖μ‖ ≤ 1 := by
  first
  | (rename_i h_1 h_3; revert l h_1 O h_3 emb hle n N c μ hc hN; exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one)
  | exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | (apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one ..)

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem unitBall_prime (R : Type) [CommRing R] (l : ℕ) [Fact l.Prime] (χ : R →+* PadicAlgCl l)
    (h : ∀ p, ‖χ p‖ ≤ 1) : ∃ P : Ideal R, P.IsPrime ∧ ∀ p, p ∈ P ↔ ‖χ p‖ < 1 := by
  refine ⟨{ carrier := {p | ‖χ p‖ < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_,
    fun p => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  · simp
  · intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖χ c‖ * ‖χ x‖ ≤ 1 * ‖χ x‖ := by gcongr; exact h c
      _ < 1 := by simpa using hx
  · refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      show ¬ ‖χ 1‖ < 1
      simp
    · intro a b hab
      show ‖χ a‖ < 1 ∨ ‖χ b‖ < 1
      have hab' : ‖χ a‖ * ‖χ b‖ < 1 := by
        have : ‖χ (a * b)‖ < 1 := hab
        simpa [map_mul, norm_mul] using this
      by_contra hno
      push_neg at hno
      have : 1 * 1 ≤ ‖χ a‖ * ‖χ b‖ := mul_le_mul hno.1 hno.2 zero_le_one (norm_nonneg _)
      linarith

theorem core (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (hunit : ∀ a, ‖emb a‖ = 1 → IsUnit a)
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O)
    (m : Ideal R) (hm : m.IsMaximal) (hker : ∀ p, σ p = 0 → p ∈ m) :
    ∃ χ : R →+* PadicAlgCl l, (∀ p, ‖χ p‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖χ p‖ < 1) ∧
      (∀ a, χ (algebraMap O R a) = emb a) ∧
      ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧ ∀ p, (σ p).map emb *ᵥ c = χ p • c := by
  classical
  let τ : R →+* Matrix (Fin n) (Fin n) (PadicAlgCl l) :=
    (emb.mapMatrix).comp (σ : R →+* Matrix (Fin n) (Fin n) O)
  have hτ : ∀ p, τ p = (σ p).map emb := fun p => rfl
  have hcomm : ∀ p q, Commute (τ p) (τ q) := fun p q => by
    show τ p * τ q = τ q * τ p
    rw [← map_mul, ← map_mul, mul_comm]
  let X : Set (R →+* PadicAlgCl l) :=
    {χ | ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧ ∀ p, τ p *ᵥ c = χ p • c}
  have hXfin : X.Finite := by
    have h := GlobalTheory.T.finite_joint_eigenvalues_of_commute (PadicAlgCl l) n R τ hcomm
    refine Set.Finite.of_finite_image (f := fun χ : R →+* PadicAlgCl l => (χ : R → PadicAlgCl l))
      (h.subset ?_) DFunLike.coe_injective.injOn
    rintro _ ⟨χ, ⟨c, hc, hχ⟩, rfl⟩
    exact ⟨c, hc, hχ⟩
  have hXle : ∀ χ ∈ X, ∀ p, ‖χ p‖ ≤ 1 := by
    rintro χ ⟨c, hc, hχ⟩ p
    exact norm_eigen_le_one l O emb hle n (σ p) c (χ p) hc (hχ p)
  have hP : ∀ χ ∈ X, ∃ P : Ideal R, P.IsPrime ∧ ∀ p, p ∈ P ↔ ‖χ p‖ < 1 :=
    fun χ hχ => unitBall_prime R l χ (hXle χ hχ)
  choose! P hPprime hPmem using hP
  have key : ∃ χ ∈ X, m ≤ P χ := by
    by_contra hno
    push_neg at hno
    obtain ⟨p, hpm, hpX⟩ : ∃ p ∈ m, ∀ χ ∈ X, ¬ ‖χ p‖ < 1 := by
      rcases X.eq_empty_or_nonempty with hX | ⟨χ0, hχ0⟩
      · exact ⟨0, m.zero_mem, by simp [hX]⟩
      · have hns : ¬ ((m : Set R) ⊆ ⋃ χ ∈ X, (P χ : Set R)) := by
          rw [Ideal.subset_union_prime_finite hXfin χ0 χ0 (fun χ hχ _ _ => hPprime χ hχ)]
          rintro ⟨χ, hχ, hle'⟩
          exact hno χ hχ hle'
        rw [Set.not_subset] at hns
        obtain ⟨p, hpm, hp⟩ := hns
        refine ⟨p, hpm, fun χ hχ hlt => hp ?_⟩
        exact Set.mem_biUnion hχ ((hPmem χ hχ p).2 hlt)
    have hdet : ‖(τ p).det‖ = 1 := by
      apply norm_det_eq_one (PadicAlgCl l) n (τ p)
      rintro μ ⟨c, hc, hcμ⟩
      let E : Submodule (PadicAlgCl l) (Fin n → PadicAlgCl l) :=
        { carrier := {v | τ p *ᵥ v = μ • v}
          add_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq] at *
            rw [mulVec_add, ha, hb, smul_add]
          zero_mem' := by simp
          smul_mem' := by
            intro a v hv
            simp only [Set.mem_setOf_eq] at *
            rw [mulVec_smul, hv, smul_comm] }
      have hcE : c ∈ E := hcμ
      have hE : E ≠ ⊥ := fun h => hc ((Submodule.mem_bot _).1 (h ▸ hcE))
      have hstab : ∀ A ∈ Set.range τ, ∀ v ∈ E, A *ᵥ v ∈ E := by
        rintro _ ⟨q, rfl⟩ v hv
        have hv' : τ p *ᵥ v = μ • v := hv
        show τ p *ᵥ (τ q *ᵥ v) = μ • (τ q *ᵥ v)
        rw [mulVec_mulVec, (hcomm p q).eq, ← mulVec_mulVec, hv', mulVec_smul]
      obtain ⟨v, hvE, hv0, hv⟩ := GlobalTheory.T.exists_common_eigenvector_mem_of_commute (PadicAlgCl l) n (Set.range τ)
        (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hcomm a b) E hE hstab
      obtain ⟨χ, hχ⟩ := eigen_ringHom R (PadicAlgCl l) n τ v hv0 (fun q => hv (τ q) ⟨q, rfl⟩)
      have hχX : χ ∈ X := ⟨v, hv0, hχ⟩
      have hμ : χ p = μ := by
        have h1 : τ p *ᵥ v = μ • v := hvE
        exact smul_left_injective (PadicAlgCl l) hv0 ((hχ p).symm.trans h1)
      rw [← hμ]
      exact le_antisymm (hXle χ hχX p) (not_lt.1 (hpX χ hχX))
    have hdet' : ‖emb (σ p).det‖ = 1 := by
      rw [RingHom.map_det]
      exact hdet
    exact hm.ne_top (eq_top_of_isUnit_det O R n σ m hker p hpm (hunit _ hdet'))
  obtain ⟨χ, hχX, hmP⟩ := key
  have hmeq : m = P χ := hm.eq_of_le (hPprime χ hχX).ne_top hmP
  obtain ⟨c, hc, hχc⟩ := id hχX
  refine ⟨χ, hXle χ hχX, fun p => by rw [hmeq]; exact hPmem χ hχX p, ?_, c, hc, hχc⟩
  intro a
  have h1 := hχc (algebraMap O R a)
  have h2 : τ (algebraMap O R a) *ᵥ c = emb a • c := by
    rw [hτ, AlgHom.commutes, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero emb)]
    ext i
    simp [mulVec_diagonal]
  exact smul_left_injective (PadicAlgCl l) hc (h1.symm.trans h2)

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem exists_integral_eigensystem : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l), Function.Injective emb → (∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ Set.range emb = {x | x ∈ L ∧ ‖x‖ ≤ 1}) → ∀ (I : Type) (M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∀ (m : Ideal (MvPolynomial I O)), m.IsMaximal → (∀ p : MvPolynomial I O, (∀ x : M, p • x = 0) → p ∈ m) → ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧ ∃ v ∈ Submodule.span (PadicAlgCl l) (Set.range j), v ≠ 0 ∧ ∀ i, Tq i v = θ i • v := by
  intro l _ O _ _ _ emb hinj hL I M _ _ _ _ hfin htf V _ _ j Tq hli hcomp m hm hann
  obtain ⟨L, _, hL⟩ := hL
  have hmemL : ∀ a, emb a ∈ L ∧ ‖emb a‖ ≤ 1 := by
    intro a
    have h : emb a ∈ Set.range emb := ⟨a, rfl⟩
    rw [hL] at h
    exact h
  have hle : ∀ a, ‖emb a‖ ≤ 1 := fun a => (hmemL a).2
  have hunit : ∀ a, ‖emb a‖ = 1 → IsUnit a := by
    intro a ha
    have hne : emb a ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at ha
      exact zero_ne_one ha
    have hinv : (emb a)⁻¹ ∈ Set.range emb := by
      rw [hL]
      refine ⟨L.inv_mem (hmemL a).1, ?_⟩
      rw [norm_inv, ha, inv_one]
    obtain ⟨b, hb⟩ := hinv
    have hab : a * b = 1 := hinj (by rw [map_mul, hb, map_one, mul_inv_cancel₀ hne])
    exact IsUnit.of_mul_eq_one b hab
  obtain ⟨n, σ, e, hσ, he_inj, he_span, he_T⟩ :=
    GlobalTheory.T.exists_matrices_intertwining_of_semilinear_alt l O emb I M hfin htf V j Tq hli hcomp
  obtain ⟨χ, hχle, hχm, hχalg, c, hc, hχc⟩ :=
    core l O emb hle hunit (MvPolynomial I O) n σ m hm (fun p hp => hann p (hσ p hp))
  set θ : I → PadicAlgCl l := fun i => χ (MvPolynomial.X i) with hθ
  have hext : MvPolynomial.eval₂Hom emb θ = χ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq, hχalg]
    · intro i
      rw [MvPolynomial.eval₂Hom_X']
  have heval : ∀ p, MvPolynomial.eval₂ emb θ p = χ p := fun p =>
    congrArg (fun f : MvPolynomial I O →+* PadicAlgCl l => f p) hext
  refine ⟨θ, fun i => hχle _, fun p => by rw [heval]; exact hχm p, e c, he_span c, ?_, ?_⟩
  · intro h
    exact hc (he_inj (by rw [h, map_zero]))
  · intro i
    rw [he_T, hχc, map_smul]

end GlobalTheory.DeligneSerre
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_hecke_eigensystem_deligne_serre : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l), Function.Injective emb → (∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ Set.range emb = {x | x ∈ L ∧ ‖x‖ ≤ 1}) → ∀ (I : Type) (M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∀ (m : Ideal (MvPolynomial I O)), m.IsMaximal → (∀ p : MvPolynomial I O, (∀ x : M, p • x = 0) → p ∈ m) → ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧ ∃ v ∈ Submodule.span (PadicAlgCl l) (Set.range j), v ≠ 0 ∧ ∀ i, Tq i v = θ i • v := by
  atlas_forward_decl GlobalTheory.DeligneSerre.exists_integral_eigensystem
end

section
section
set_option autoImplicit false

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.UG Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame

theorem finite_forms_of_classes {O : Type} [CommRing O] {W : Type} [AddCommGroup W] [Module O W] [IsNoetherian O W]
    {G : Type} [Group G] (Γ K : Subgroup G) (ρ : Representation O K W)
    (h : ∃ S : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ κ ∈ K, g = γ * s * κ) : Module.Finite O (AMFK O Γ K ρ) := by
  obtain ⟨S, hS⟩ := h
  let ev : AMFK O Γ K ρ →ₗ[O] (S → W) :=
    (LinearMap.funLeft O W (Subtype.val : S → G)).comp (AMFK O Γ K ρ).subtype
  refine Module.Finite.of_injective ev ?_
  intro f f' hff
  ext g
  obtain ⟨γ, hγ, s, hs, κ, hκ, rfl⟩ := hS g
  have h1 := f.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h2 := f'.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h3 : (f : G → W) s = (f' : G → W) s := congrFun hff ⟨s, hs⟩
  exact h1.trans ((congrArg _ h3).trans h2.symm)

theorem Frame.finite_latticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  intro l _ ι _ _ N F mu jK hF
  have : ∀ τ : ι, Module.Finite F.O (dualWeyl F.O N N (res N (mu τ))) :=
    fun τ => dualWeyl_module_finite F.O N N _
  have : IsNoetherian F.O (NablaT F.O N mu) := inferInstance
  exact finite_forms_of_classes F.Γ F.K _ hF.classes

end GlobalTheory.ExpFrame
end

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_frameLatticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  atlas_forward_decl GlobalTheory.ExpFrame.Frame.finite_latticeForms
end

section
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

namespace GlobalTheory.BaseChangeIndep

theorem indep_pi {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {L : Type} [Field L] (emb : O →+* L)
    (hemb : Function.Injective emb) {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module L V]
    (b : M →ₛₗ[emb] V) (hbinj : Function.Injective b)
    (hb : ∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent L fun a => b (x a))
    {T : Type} [Finite T] (n : ℕ) (y : Fin n → T → M) (hy : LinearIndependent O y) :
    LinearIndependent L fun a t => b (y a t) := by
  classical
  haveI : Fintype T := Fintype.ofFinite T

  haveI : Module.IsTorsionFree O M := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m h
    have h1 : emb r • b m = 0 := by rw [← LinearMap.map_smulₛₗ, h, map_zero]
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (hemb (by rw [h2, map_zero]))
    · exact Or.inr (hbinj (by rw [h2, map_zero]))

  let P : Submodule O M := Submodule.span O (Set.range fun p : Fin n × T => y p.1 p.2)
  haveI : Module.Finite O P := Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range _))
  haveI : Module.Free O P := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O P
  let k := Module.finrank O P
  have hmem : ∀ a t, y a t ∈ P := fun a t => Submodule.subset_span ⟨(a, t), rfl⟩
  have he : LinearIndependent O fun i => ((e i : P) : M) :=
    e.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hbe : LinearIndependent L fun i => b (e i : M) := by
    have := hb k (fun i => (e i : M)) he
    exact this

  let Y : Fin n → T × Fin k → O := fun a p => e.repr ⟨y a p.1, hmem a p.1⟩ p.2
  let Φ : (T × Fin k → O) →ₗ[O] (T → M) :=
    { toFun := fun Z t => ∑ i, Z (t, i) • ((e i : P) : M)
      map_add' := by
        intro Z Z'; funext t; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c Z; funext t; simp [smul_smul, Finset.smul_sum] }
  have hΦ : ∀ a, Φ (Y a) = y a := by
    intro a; funext t
    have h2 : ((∑ i, e.repr ⟨y a t, hmem a t⟩ i • e i : P) : M) = y a t := by rw [e.sum_repr]
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    change ∑ i, Y a (t, i) • ((e i : P) : M) = y a t
    exact h2
  have hY : LinearIndependent O Y := by
    apply LinearIndependent.of_comp Φ
    have : (Φ ∘ Y) = y := funext hΦ
    rw [this]; exact hy
  letI : Algebra O L := emb.toAlgebra
  haveI : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 hemb
  have hY' : LinearIndependent L fun a => algebraMap O L ∘ Y a :=
    linearIndependent_algebraMap_comp_iff.2 hY
  let Ψ : (T × Fin k → L) →ₗ[L] (T → V) :=
    { toFun := fun Z t => ∑ i, Z (t, i) • b (e i : M)
      map_add' := by
        intro Z Z'; funext t; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c Z; funext t; simp [smul_smul, Finset.smul_sum] }
  have hΨ : LinearMap.ker Ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro Z hZ
    funext p
    have h1 : ∑ i, Z (p.1, i) • b (e i : M) = 0 := congrFun hZ p.1
    have := (Fintype.linearIndependent_iff.1 hbe) (fun i => Z (p.1, i)) h1 p.2
    simpa using this
  have key := hY'.map' Ψ hΨ
  have hfam : (Ψ ∘ fun a => algebraMap O L ∘ Y a) = fun a t => b (y a t) := by
    funext a t
    change ∑ i, (algebraMap O L (Y a (t, i))) • b (e i : M) = b (y a t)
    rw [← hΦ a]
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.map_smulₛₗ]
    rfl
  rw [hfam] at key
  exact key

end GlobalTheory.BaseChangeIndep

namespace GlobalTheory.BaseChangeIndep

theorem forms_indep : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ)
    (jK : F.K →* alg F.O N mu) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu), Function.Injective b → F.Ok →
    (∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a)) →
    ∀ (n : ℕ) (x : Fin n → Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)), LinearIndependent F.O x →
      LinearIndependent (PadicAlgCl l) fun a => (fun g => b ((x a : F.G → NablaT F.O N mu) g)) := by
  intro l _ ι _ _ N F mu jK b hbinj hOk hb n x hx
  obtain ⟨S, hS⟩ := hOk.classes
  let R : Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu) →ₗ[F.O] (S → NablaT F.O N mu) :=
    { toFun := fun f s => (f : F.G → NablaT F.O N mu) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf0
    apply Subtype.ext
    funext g
    obtain ⟨γ, hγ, s, hs, κ, hκ, rfl⟩ := hS g
    have hf : ∀ (γ : F.Γ) (g : F.G) (κ : F.K), (f : F.G → NablaT F.O N mu) ((γ : F.G) * g * κ) =
        repOf F.O (A := alg F.O N mu) jK (NablaT F.O N mu) κ⁻¹ ((f : F.G → NablaT F.O N mu) g) := f.2
    have h0 : (f : F.G → NablaT F.O N mu) s = 0 := congrFun hf0 ⟨s, hs⟩
    have h1 := hf ⟨γ, hγ⟩ s ⟨κ, hκ⟩
    rw [h1, h0, map_zero]
    rfl
  have hx' : LinearIndependent F.O (R ∘ x) := hx.map' R hR
  have hOk1 := hOk.ring.1
  have key := indep_pi F.emb hOk1 b hbinj hb n (R ∘ x) hx'
  let R' : (F.G → NablaT (PadicAlgCl l) N mu) →ₗ[PadicAlgCl l] (S → NablaT (PadicAlgCl l) N mu) :=
    { toFun := fun f s => f s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp R'
  exact key

end GlobalTheory.BaseChangeIndep
end
end

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_frameForms_baseChange : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu), Function.Injective b → F.Ok → (∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a)) → ∀ (n : ℕ) (x : Fin n → Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => (fun g => b ((x a : F.G → NablaT F.O N mu) g)) := by
  atlas_forward_decl GlobalTheory.BaseChangeIndep.forms_indep
end

section
section
namespace GlobalTheory

theorem lift_forms_of_card_isUnit : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G)
    (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q]
    (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π →
    (∀ κ x, π x = 0 → π (ρ κ x) = 0) →
    (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧
      IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) →
    ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) →
    ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by
  intro O _ G _ Γ K B Q _ _ _ _ ρ π hπ _hker hfin f hf
  classical

  have hlift : ∀ s : G, ∃ y : B, π y = f s ∧
      ∀ (h : Γ) (hk : s⁻¹ * (h : G) * s ∈ K), ρ ⟨_, hk⟩ y = y := by
    intro s
    obtain ⟨hF, hu⟩ := hfin s
    haveI : Fintype {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} := Fintype.ofFinite _
    obtain ⟨y0, hy0⟩ := hπ (f s)
    obtain ⟨u, hu'⟩ := hu
    let kk : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} → K := fun h => ⟨_, h.2⟩
    refine ⟨(↑u⁻¹ : O) • ∑ h, ρ (kk h) y0, ?_, ?_⟩
    · rw [map_smul, map_sum]
      have hval : ∀ h, π (ρ (kk h) y0) = f s := by
        intro h
        have e := hf h.1 s (kk h)⁻¹ y0 hy0.symm
        rw [inv_inv] at e
        rw [← e]
        congr 1
        simp only [kk, Subgroup.coe_inv]
        group
      simp_rw [hval, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul O, smul_smul, ← Nat.card_eq_fintype_card, ← hu', Units.inv_mul,
        one_smul]
    · intro h hk
      rw [map_smul, map_sum]
      congr 1
      have hmul : ∀ x : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K},
          s⁻¹ * ((h * x.1 : Γ) : G) * s ∈ K := by
        intro x
        have : s⁻¹ * ((h * x.1 : Γ) : G) * s = (s⁻¹ * (h : G) * s) * (s⁻¹ * (x.1 : G) * s) := by
          push_cast; group
        rw [this]; exact K.mul_mem hk x.2
      have hinvm : ∀ x : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K},
          s⁻¹ * ((h⁻¹ * x.1 : Γ) : G) * s ∈ K := by
        intro x
        have : s⁻¹ * ((h⁻¹ * x.1 : Γ) : G) * s = (s⁻¹ * (h : G) * s)⁻¹ * (s⁻¹ * (x.1 : G) * s) := by
          push_cast; group
        rw [this]; exact K.mul_mem (K.inv_mem hk) x.2
      let e : {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} ≃ {γ : Γ // s⁻¹ * (γ : G) * s ∈ K} :=
        { toFun := fun x => ⟨h * x.1, hmul x⟩
          invFun := fun x => ⟨h⁻¹ * x.1, hinvm x⟩
          left_inv := fun x => Subtype.ext (by simp)
          right_inv := fun x => Subtype.ext (by simp) }
      refine Fintype.sum_equiv e _ _ (fun x => ?_)
      rw [← Module.End.mul_apply, ← map_mul]
      congr 2
      apply Subtype.ext
      simp only [kk, e, Equiv.coe_fn_mk, Subgroup.coe_mul]
      push_cast
      group
  choose y hy hinv using hlift

  have hwd : ∀ (s : G) (γ γ' : Γ) (κ κ' : K), (γ : G) * s * κ = γ' * s * κ' →
      ρ κ⁻¹ (y s) = ρ κ'⁻¹ (y s) := by
    intro s γ γ' κ κ' e
    have hk : s⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * s = ((κ' * κ⁻¹ : K) : G) := by
      have h1 : (γ : G) * s = γ' * s * κ' * κ⁻¹ := by
        calc (γ : G) * s = (γ : G) * s * κ * (κ : G)⁻¹ := by group
          _ = γ' * s * κ' * (κ : G)⁻¹ := by rw [e]
      calc s⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * s = s⁻¹ * ((γ' : G)⁻¹ * ((γ : G) * s)) := by
            push_cast; group
        _ = ((κ' * κ⁻¹ : K) : G) := by rw [h1]; push_cast; group
    have hmem : s⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * s ∈ K := hk ▸ (κ' * κ⁻¹).2
    have hfix := hinv s (γ'⁻¹ * γ) hmem
    have heq : (⟨_, hmem⟩ : K) = κ' * κ⁻¹ := Subtype.ext hk
    rw [heq] at hfix
    calc ρ κ⁻¹ (y s) = ρ κ'⁻¹ (ρ (κ' * κ⁻¹) (y s)) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
      _ = ρ κ'⁻¹ (y s) := by rw [hfix]

  have hrep : ∃ rep : G → G, (∀ (γ : Γ) (g : G) (κ : K), rep ((γ : G) * g * κ) = rep g) ∧
      ∀ g : G, ∃ (γ : Γ) (κ : K), g = (γ : G) * rep g * κ := by
    refine ⟨fun g => (DoubleCoset.mk Γ K g).out, ?_, ?_⟩
    · intro γ g κ
      have : DoubleCoset.mk Γ K ((γ : G) * g * κ) = DoubleCoset.mk Γ K g :=
        (DoubleCoset.eq Γ K _ _).2 ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, (κ : G)⁻¹, K.inv_mem κ.2, by group⟩
      simp only [this]
    · intro g
      obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
      refine ⟨⟨h, hh⟩⁻¹, ⟨k, hk⟩⁻¹, ?_⟩
      simp only [e, Subgroup.coe_inv]
      group
  obtain ⟨rep, hrep1, hrep2⟩ := hrep
  choose γg κg hg using hrep2
  refine ⟨fun g => ρ (κg g)⁻¹ (y (rep g)), ?_, ?_⟩
  · intro γ g κ
    show ρ (κg ((γ : G) * g * κ))⁻¹ (y (rep ((γ : G) * g * κ))) = ρ κ⁻¹ (ρ (κg g)⁻¹ (y (rep g)))
    have e1 := hg ((γ : G) * g * κ)
    rw [hrep1] at e1 ⊢
    have e2 := hg g
    have key : ((γ * γg g : Γ) : G) * rep g * ((κg g * κ : K) : G) =
        (γg ((γ : G) * g * κ) : G) * rep g * (κg ((γ : G) * g * κ) : G) := by
      rw [← e1]
      conv_rhs => rw [e2]
      push_cast; group
    rw [← hwd (rep g) _ _ _ _ key, ← Module.End.mul_apply, ← map_mul, mul_inv_rev]
  · intro g
    calc π (ρ (κg g)⁻¹ (y (rep g))) = f ((γg g : G) * rep g * κg g) :=
          (hf (γg g) (rep g) (κg g) (y (rep g)) (hy (rep g)).symm).symm
      _ = f g := by rw [← hg g]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G) (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q] (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π → (∀ κ x, π x = 0 → π (ρ κ x) = 0) → (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧ IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) → ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) → ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by
  atlas_forward_decl GlobalTheory.lift_forms_of_card_isUnit
end

section
section
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

namespace GlobalTheory.ExpFrame.Frame

theorem isUnit_natCast_of_not_dvd : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N), F.Ok →
    ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : F.O) := by
  intro l _ ι _ N F hF n hn
  obtain ⟨hinj, L, _, hrange⟩ := hF.ring
  have hnorm : ‖(n : PadicAlgCl l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) n, PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hn
  have hne : (n : PadicAlgCl l) ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hmem : (n : PadicAlgCl l)⁻¹ ∈ Set.range F.emb := by
    rw [hrange]
    refine ⟨?_, ?_⟩
    · exact L.inv_mem (L.natCast_mem n)
    · rw [norm_inv, hnorm, inv_one]
  obtain ⟨y, hy⟩ := hmem
  have h1 : (n : F.O) * y = 1 := by
    apply hinj
    rw [map_mul, map_natCast, hy, map_one, mul_inv_cancel₀ hne]
  exact IsUnit.of_mul_eq_one y h1

end GlobalTheory.ExpFrame.Frame
end

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_natCast_frameCoeffRing_not_dvd : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N), F.Ok → ∀ n : ℕ, ¬ l ∣ n → IsUnit (n : F.O) := by
  atlas_forward_decl GlobalTheory.ExpFrame.Frame.isUnit_natCast_of_not_dvd
end

section
section
namespace GlobalTheory.NonDomZero

theorem exists_lt_lt_of_not_antitone {N : ℕ} {ν : Fin N → ℕ} (hν : ¬ Antitone ν) :
    ∃ a b : Fin N, a < b ∧ ν a < ν b := by
  simp only [Antitone, not_forall] at hν
  obtain ⟨a, b, hab, hlt⟩ := hν
  refine ⟨a, b, lt_of_le_of_ne hab ?_, lt_of_not_ge hlt⟩
  rintro rfl
  exact hlt le_rfl

theorem dualWeyl_eq_bot_of_not_antitone :
    ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ),
      ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  intro O _ _ _ N ν hν
  exact Formalism.GradedWeylDivisibility.dualWeylModuleNonDominant O N N ν (exists_lt_lt_of_not_antitone hν)

end GlobalTheory.NonDomZero
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_eq_bot_of_not_antitone' : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ), ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  atlas_forward_decl GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.ExpFrame.Eigenform

theorem mem_of_ann {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (m : Ideal R) [m.IsPrime]
    (hne : ¬ Subsingleton (LocalizedModule m.primeCompl M)) (p : R) (hp : ∀ x : M, p • x = 0) : p ∈ m := by
  by_contra hpm
  apply hne
  have key : ∀ z : LocalizedModule m.primeCompl M, z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h f s =>
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨p, hpm⟩, ?_⟩
      show (p : R) • ((s : R) • f) = (p : R) • ((s : R) • (0 : M))
      rw [smul_zero, smul_zero, hp]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem loc_subsingleton {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (S : Submonoid R)
    (h : ∀ x : M, x = 0) : Subsingleton (LocalizedModule S M) := by
  have key : ∀ z : LocalizedModule S M, z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h f s => rw [h f, LocalizedModule.zero_mk]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem nabla_zero_of_not_antitone {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (τ0 : ι) (hτ0 : ¬ Antitone (res N (mu τ0))) : ∀ z : NablaT F.O N mu, z = 0 := by
  have hbot := GlobalTheory.T.dualWeyl_eq_bot_of_not_antitone' F.O N (res N (mu τ0)) hτ0
  intro z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hx : x τ0 = 0 :=
      Subtype.ext ((Submodule.eq_bot_iff _).1 hbot ((x τ0 : Formalism.GradedWeylDivisibility.dualWeyl F.O N N (res N (mu τ0))) : MvPolynomial _ F.O) (x τ0).2)
    rw [(PiTensorProduct.tprod F.O).map_coord_zero τ0 hx, smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem quot_ker_stable {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (jKm : F.K →* alg F.O N mu) (ϖ : F.O) (κ : F.K) (x : NablaT F.O N mu)
    (hx : x ∈ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu))) :
    repOf F.O (A := alg F.O N mu) jKm (NablaT F.O N mu) κ x ∈ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)) := by
  have hle : (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)).map (repOf F.O (A := alg F.O N mu) jKm (NablaT F.O N mu) κ) ≤
      (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨x, hx, rfl⟩

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Lift
variable {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam mu : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) (jKm : F.K →* alg F.O N mu) (ϖ : F.O)
  (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm]
  [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)] [Module F.T (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu))]

theorem hecke_compat (hH : F.IsHecke lam jK Gm) (hHm : F.IsHecke mu jKm (NablaT F.O N mu))
    (π : NablaT F.O N mu →ₗ[F.O] (NablaT F.O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu))))
    (ψ : Gm →+ (NablaT F.O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu))))
    (hψs : ∀ (c : F.O) (w : Gm), ψ (c • w) = c • ψ w) (q : F.T)
    (x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) (z : Forms F.O (A := alg F.O N lam) F.Γ jK Gm)
    (hxz : ∀ g, π ((x : F.G → NablaT F.O N mu) g) = ψ ((z : F.G → Gm) g)) (g : F.G) :
    π (((q • x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) : F.G → NablaT F.O N mu) g) =
      ψ (((q • z : Forms F.O (A := alg F.O N lam) F.Γ jK Gm) : F.G → Gm) g) := by
  induction q using MvPolynomial.induction_on generalizing x z g with
  | C c =>
    rw [hHm.1, hH.1]
    simp only [Submodule.coe_smul, Pi.smul_apply]
    rw [map_smul, hxz, hψs]
  | add p q hp hq =>
    rw [add_smul, add_smul]
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    rw [hp x z hxz g, hq x z hxz g]
  | mul_X p i hp =>
    rw [mul_comm, mul_smul, mul_smul, hHm.2, hH.2, map_smul, hψs, map_sum, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => hp x z hxz (g * s)

theorem ann_lift (hOk : F.Ok) (hJ : F.IsJ lam jK) (hJm : F.IsJ mu jKm)
    (hH : F.IsHecke lam jK Gm) (hHm : F.IsHecke mu jKm (NablaT F.O N mu)) (hE : Embeds F.O N lam mu ϖ Gm) (p : F.T)
    (hp : ∀ x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu), p • x = 0)
    (y : Forms F.O (A := alg F.O N lam) F.Γ jK Gm) : p • y = 0 := by
  obtain ⟨ψ, hψi, hψc, hψg, -⟩ := hE
  have hψs : ∀ (c : F.O) (w : Gm), ψ (c • w) = c • ψ w := by
    intro c w
    rw [← algebraMap_smul (alg F.O N lam) c w, hψc]
  obtain ⟨Fm, hFm, hFπ⟩ := GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers F.O F.G F.Γ F.K (NablaT F.O N mu)
      (NablaT F.O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule F.O (NablaT F.O N mu)))
      (repOf F.O (A := alg F.O N mu) jKm (NablaT F.O N mu)) (Submodule.mkQ _) (Submodule.mkQ_surjective _)
      (by
        intro κ x hx
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
        exact quot_ker_stable F mu jKm ϖ κ x hx)
      (fun g => ⟨(hOk.tame g).1, GlobalTheory.T.isUnit_natCast_frameCoeffRing_not_dvd l ι N F hOk _ (hOk.tame g).2⟩)
      (fun g => ψ ((y : F.G → Gm) g))
      (by
        intro γ g κ yy hyy
        have hy := y.2 γ g κ
        show ψ ((y : F.G → Gm) ((γ : F.G) * g * κ)) = _
        rw [hy]
        show ψ (jK κ⁻¹ • (y : F.G → Gm) g) = Submodule.mkQ _ (jKm κ⁻¹ • yy)
        rw [hJ κ⁻¹, hJm κ⁻¹, smul_assoc, hψs, hψg _ _ _ hyy, smul_assoc, Submodule.mkQ_apply,
          Submodule.Quotient.mk_smul]
        rfl)
  apply Subtype.ext
  funext g
  apply hψi
  have := hecke_compat F lam mu jK jKm ϖ Gm hH hHm (Submodule.mkQ _) ψ hψs p ⟨Fm, hFm⟩ y (fun g => hFπ g) g
  rw [hp] at this
  simp only [Submodule.coe_zero, Pi.zero_apply, map_zero] at this ⊢
  exact this.symm

end Lift

section Eig
variable {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (mu : ι → ℕ → ℕ)
  (jKm : F.K →* alg F.O N mu)

theorem tf_forms (hOk : F.Ok) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu) (hbi : Function.Injective b)
    (c : F.O) (x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) (hcx : c • x = 0) : c = 0 ∨ x = 0 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  apply Subtype.ext
  funext g
  have h1 : c • (x : F.G → NablaT F.O N mu) g = 0 := by
    have := congrArg (fun y : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu) => (y : F.G → NablaT F.O N mu) g) hcx
    simpa using this
  have h2 : F.emb c • b ((x : F.G → NablaT F.O N mu) g) = 0 := by rw [← map_smulₛₗ, h1, map_zero]
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd (hOk.ring.1 (h.trans (map_zero _).symm)) hc
  · exact hbi (h.trans (map_zero b).symm)

def jmap (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu) :
    Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu) →ₛₗ[F.emb] (F.G → NablaT (PadicAlgCl l) N mu) where
  toFun x g := b ((x : F.G → NablaT F.O N mu) g)
  map_add' x y := by funext g; simp
  map_smul' c x := by funext g; simp [map_smulₛₗ]

def heckeQ (i : F.I) : (F.G → NablaT (PadicAlgCl l) N mu) →ₗ[PadicAlgCl l] (F.G → NablaT (PadicAlgCl l) N mu) where
  toFun h g := F.emb (F.cst i) • ∑ s ∈ F.tr i, h (g * s)
  map_add' h h' := by funext g; simp [Finset.sum_add_distrib, smul_add]
  map_smul' c h := by funext g; simp [Finset.smul_sum, smul_comm c]

theorem form_of_mem_span (hJm : F.IsJ mu jKm) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu)
    (hbg : ∀ g x, b (grp F.O N mu g x) = grp (PadicAlgCl l) N mu (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x))
    (w : F.G → NablaT (PadicAlgCl l) N mu) (hw : w ∈ Submodule.span (PadicAlgCl l) (Set.range (jmap F mu jKm b))) :
    F.IsForm mu w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    constructor
    · intro γ hγ g
      have hx := x.2 ⟨γ, hγ⟩ g 1
      show b ((x : F.G → NablaT F.O N mu) (γ * g)) = b ((x : F.G → NablaT F.O N mu) g)
      simp only [OneMemClass.coe_one, mul_one, inv_one, map_one] at hx
      rw [hx]
      rfl
    · intro κ g
      have hx := x.2 1 g κ
      simp only [OneMemClass.coe_one, one_mul] at hx
      show F.emb (F.chi κ) • grp (PadicAlgCl l) N mu _ (b ((x : F.G → NablaT F.O N mu) (g * κ))) =
        b ((x : F.G → NablaT F.O N mu) g)
      rw [← hbg, ← map_smulₛₗ, hx]
      congr 1
      show (F.chi κ : F.O) • grp F.O N mu (F.kap κ) (jKm κ⁻¹ • (x : F.G → NablaT F.O N mu) g) = _
      have h2 : (F.chi κ : F.O) • grp F.O N mu (F.kap κ) (jKm κ⁻¹ • (x : F.G → NablaT F.O N mu) g) =
          jKm κ • jKm κ⁻¹ • (x : F.G → NablaT F.O N mu) g := by
        rw [hJm κ, smul_assoc]
        rfl
      rw [h2, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  | zero => exact ⟨fun _ _ _ => rfl, fun _ _ => by simp⟩
  | add w w' _ _ hw hw' =>
    refine ⟨fun γ hγ g => by simp [hw.1 γ hγ g, hw'.1 γ hγ g], fun κ g => ?_⟩
    simp only [Pi.add_apply, map_add, smul_add]
    rw [hw.2 κ g, hw'.2 κ g]
  | smul c w _ hw =>
    refine ⟨fun γ hγ g => by simp [hw.1 γ hγ g], fun κ g => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [smul_comm, hw.2 κ g]

variable [Module F.T (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu))]
  [IsScalarTower F.O F.T (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu))]

theorem jmap_equiv (hHm : F.IsHecke mu jKm (NablaT F.O N mu)) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu)
    (i : F.I) (x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) :
    jmap F mu jKm b ((MvPolynomial.X i : F.T) • x) = heckeQ F mu i (jmap F mu jKm b x) := by
  funext g
  show b ((((MvPolynomial.X i : F.T) • x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) : F.G → NablaT F.O N mu) g) =
    F.emb (F.cst i) • ∑ s ∈ F.tr i, b ((x : F.G → NablaT F.O N mu) (g * s))
  rw [hHm.2 i x g, map_smulₛₗ, map_sum]

theorem eig_of_ann (hOk : F.Ok) (hJm : F.IsJ mu jKm) (hHm : F.IsHecke mu jKm (NablaT F.O N mu))
    (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu) (hbi : Function.Injective b)
    (hbg : ∀ g x, b (grp F.O N mu g x) = grp (PadicAlgCl l) N mu (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x))
    (hbli : ∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a))
    (m : Ideal F.T) [m.IsMaximal]
    (hannM : ∀ p : F.T, (∀ x : Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu), p • x = 0) → p ∈ m) :
    ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  have h1 := GlobalTheory.T.module_finite_frameLatticeForms l ι N F mu jKm hOk
  have h2 := tf_forms F mu jKm hOk b hbi
  have h3 := GlobalTheory.T.linearIndependent_frameForms_baseChange l ι N F mu jKm b hbi hOk hbli
  have h4 := jmap_equiv F mu jKm hHm b
  have h5 := @GlobalTheory.T.exists_integral_hecke_eigensystem_deligne_serre l _ F.O _ _ _ F.emb hOk.ring.1 hOk.ring.2 F.I (Forms F.O (A := alg F.O N mu) F.Γ jKm (NablaT F.O N mu)) _ _ _ _ h1
  obtain ⟨θ, hθ1, hθ2, v, hvspan, hv0, hvT⟩ := h5 h2 (F.G → NablaT (PadicAlgCl l) N mu) (jmap F mu jKm b) (heckeQ F mu) h3 h4 m inferInstance hannM
  exact ⟨θ, ⟨v, hv0, form_of_mem_span F mu jKm hJm b hbg v hvspan, fun i g => congrFun (hvT i) g⟩, hθ1, hθ2⟩

end Eig

theorem eigenform_of_surviving : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (ϖ : F.O), F.Ok → F.IsJ lam jK → Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)], F.IsHecke lam jK Gm → Embeds F.O N lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal], ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)) → ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  intro l _ ι _ _ N F lam mu jK ϖ hOk hJ hϖ Gm _ _ _ _ _ hH hE m _ hne
  have hann := mem_of_ann m hne
  by_cases hdom : ∀ τ, Antitone (res N (mu τ))
  swap
  · exfalso
    push_neg at hdom
    obtain ⟨τ0, hτ0⟩ := hdom
    have h0 := nabla_zero_of_not_antitone F mu τ0 hτ0
    obtain ⟨ψ, hψi, -, -, -⟩ := hE
    have hG : ∀ a : Gm, a = 0 := by
      intro a
      apply hψi
      obtain ⟨ya, hya⟩ := Submodule.Quotient.mk_surjective _ (ψ a)
      rw [map_zero, ← hya, h0 ya, Submodule.Quotient.mk_zero]
    exact hne (loc_subsingleton _ fun f => Subtype.ext (funext fun g => hG _))
  obtain ⟨jKm, hJm⟩ := GlobalTheory.ExpFrame.levelMap_exists l ι N F mu
  obtain ⟨instT, instTS, hHm⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module l ι N F mu jKm hOk hJm (NablaT F.O N mu)
  obtain ⟨b, hbi, -, -, hbg, hbli, -⟩ := GlobalTheory.LatBC.baseChange_lattices l ι N F mu hOk.ring.1 hdom
  exact eig_of_ann F mu jKm hOk hJm hHm b hbi hbg hbli m
    (fun p hp => hann p (ann_lift F lam mu jK jKm ϖ Gm hOk hJ hJm hH hHm hE p hp))

end GlobalTheory.ExpFrame.Eigenform

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charZero_eigenform_surviving_compositionFactor : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (ϖ : F.O), F.Ok → F.IsJ lam jK → Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)], F.IsHecke lam jK Gm → Embeds F.O N lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal], ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)) → ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  atlas_forward_decl GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving
end
