import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesOfIsConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.FinProjComplete

theorem mem_span_pow_smul_top_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M) ↔ ∃ m : M, x = (p ^ n : ℕ) • m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, Submodule.mem_top, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩

theorem smodEq_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M))] ↔
      ∃ m : M, x - y = (p ^ n : ℕ) • m := by
  rw [SModEq.sub_mem, mem_span_pow_smul_top_iff]

end GlobalTheory.FinProjComplete

open GlobalTheory.FinProjComplete in
theorem GlobalTheory.FinProjComplete.isAdicComplete_span_natCast : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  intro p O A _ _ _ _ _ hO
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' O A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π (LinearMap.id) hπ
  have hπs : ∀ a, π (s a) = a := fun a => by simpa using LinearMap.congr_fun hs a
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hc : ∀ i, s x i = 0 := by
      intro i
      apply hO.toIsHausdorff.haus'
      intro n
      obtain ⟨m, hm⟩ := (smodEq_iff p n x 0).1 (hx n)
      rw [smodEq_iff]
      refine ⟨s m i, ?_⟩
      rw [sub_zero] at hm ⊢
      rw [hm, map_nsmul, Pi.smul_apply]
    have : s x = 0 := funext hc
    rw [← hπs x, this, map_zero]
  · intro f hf
    have hcoord : ∀ i, ∃ L : O, ∀ n, s (f n) i ≡ L [SMOD ((Ideal.span {(p : O)}) ^ n • (⊤ : Submodule O O))] := by
      intro i
      apply hO.toIsPrecomplete.prec'
      intro m n hmn
      obtain ⟨c, hc⟩ := (smodEq_iff p m (f m) (f n)).1 (hf hmn)
      rw [smodEq_iff]
      refine ⟨s c i, ?_⟩
      rw [← Pi.sub_apply, ← map_sub, hc, map_nsmul, Pi.smul_apply]
    choose L hL using hcoord
    refine ⟨π L, fun n => ?_⟩
    have hd : ∀ i, ∃ c : O, s (f n) i - L i = (p ^ n : ℕ) • c := fun i => (smodEq_iff p n _ _).1 (hL i n)
    choose c hc using hd
    rw [smodEq_iff]
    refine ⟨π c, ?_⟩
    have hv : s (f n) - L = (p ^ n : ℕ) • c := funext fun i => by simpa using hc i
    rw [← map_nsmul, ← hv, map_sub, hπs]
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  atlas_forward_decl GlobalTheory.FinProjComplete.isAdicComplete_span_natCast
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CChartLimit

theorem smod_span_iff {R : Type} [CommRing R] (a x y : R) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem exists_series_of_compatible : ∀ (p : ℕ) (O σ : Type) [CommRing O] [Fintype σ]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (A : ℕ → Type) [∀ n, CommRing (A n)]
    [∀ n, Algebra O (A n)], (∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)) →
    ∀ (x : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n) (t : ∀ n, A n),
    (∀ n, IsEval p (x n) (E n)) → (∀ n, ∃ f, E n f = t n) →
    (∀ n f, E (n + 1) f = t (n + 1) → E n f = t n) →
    (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) →
    ∃ g, ∀ n, E n g = t n := by
  intro p O σ _ _ _ A _ _ hH x E t hE hs hstep hker
  classical
  choose g hg using hs
  have hdown : ∀ n d f, E (n + d) f = t (n + d) → E n f = t n := by
    intro n d f
    induction d with
    | zero => exact id
    | succ d ih => exact fun hf => ih (hstep (n + d) f hf)
  have hgk : ∀ n k, n ≤ k → E n (g k) = t n := by
    intro n k hnk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
    exact hdown n d _ (hg _)
  choose K hK using hker
  let K' : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup (fun i => max i (K i i))
  have hK'mono : Monotone K' := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
  have hK'ge : ∀ j, j ≤ K' j ∧ K j j ≤ K' j := fun j => by
    have := Finset.le_sup (f := fun i => max i (K i i)) (Finset.mem_range.mpr (Nat.lt_succ_self j))
    exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
  let h : ℕ → MvPowerSeries σ O := fun j => g (K' j)
  have hcau : ∀ j j', j ≤ j' → ∀ α : σ →₀ ℕ, α.degree < j →
      (p : O) ^ j ∣ coeff α (h j) - coeff α (h j') := by
    intro j j' hjj α hα
    have h0 : E (K j j) (h j - h j') = 0 := by
      rw [map_sub, hgk _ _ (hK'ge j).2, hgk _ _ ((hK'ge j).2.trans (hK'mono hjj)), sub_self]
    have := hK j j _ h0 α hα
    rwa [map_sub] at this
  have hc : ∀ α : σ →₀ ℕ, ∃ L : O, ∀ n, (p : O) ^ n ∣ coeff α (h (n + α.degree + 1)) - L := by
    intro α
    have hpre : IsPrecomplete (Ideal.span {(p : O)}) O := inferInstance
    obtain ⟨L, hL⟩ := hpre.prec (f := fun n => coeff α (h (n + α.degree + 1))) (by
      intro m n hmn
      rw [smod_span_iff]
      have := hcau (m + α.degree + 1) (n + α.degree + 1) (by omega) α (by omega)
      exact (pow_dvd_pow _ (by omega)).trans this)
    exact ⟨L, fun n => (smod_span_iff _ _ _ _).1 (hL n)⟩
  choose L hL using hc
  let μ : MvPowerSeries σ O := L
  have hμ : ∀ α, coeff α μ = L α := fun α => rfl
  refine ⟨μ, fun n => ?_⟩
  haveI := hH n
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A n)})).2
  intro m
  rw [smod_span_iff]
  obtain ⟨N, hN⟩ := (hE n).2 m
  have hj : E n (h (m + N + n)) = t n :=
    hgk n (K' (m + N + n)) (le_trans (by omega) (hK'ge (m + N + n)).1)
  have hd : ∀ α : σ →₀ ℕ, α.degree < N →
      (p : O) ^ m ∣ coeff α μ - coeff α (h (m + N + n)) := by
    intro α hα
    have h1 := hL α m
    have h2 := hcau (m + α.degree + 1) (m + N + n) (by omega) α (by omega)
    have h2' : (p : O) ^ m ∣ coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n)) :=
      (pow_dvd_pow _ (by omega)).trans h2
    have e : coeff α μ - coeff α (h (m + N + n)) =
        (coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n))) -
          (coeff α (h (m + α.degree + 1)) - L α) := by rw [hμ]; ring
    rw [e]; exact dvd_sub h2' h1
  choose q hq using hd
  let Q : MvPowerSeries σ O := fun α => if hα : α.degree < N then q α hα else 0
  have hQ : ∀ α (hα : α.degree < N), coeff α Q = q α hα := fun α hα => by
    show (if hα : α.degree < N then q α hα else 0) = q α hα
    rw [dif_pos hα]
  let R := μ - h (m + N + n) - (p : O) ^ m • Q
  have hR : ∀ α : σ →₀ ℕ, α.degree < N → coeff α R = 0 := by
    intro α hα
    simp only [R, map_sub, MvPowerSeries.coeff_smul, hQ α hα, smul_eq_mul, hq α hα, sub_self]
  have hER := hN R hR
  have hsplit : E n μ - t n = E n R + (p : A n) ^ m * E n Q := by
    have hμeq : μ = h (m + N + n) + ((p : O) ^ m • Q + R) := by simp only [R]; abel
    rw [hμeq, map_add, map_add, hj, map_smul, Algebra.smul_def, map_pow, map_natCast]
    ring
  rw [hsplit]
  exact dvd_add hER (dvd_mul_right _ _)

end GlobalTheory.CChartLimit
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_series_of_compatible' : ∀ (p : ℕ) (O σ : Type) [CommRing O] [Fintype σ] [IsAdicComplete (Ideal.span {(p : O)}) O] (A : ℕ → Type) [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)], (∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)) → ∀ (x : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n) (t : ∀ n, A n), (∀ n, IsEval p (x n) (E n)) → (∀ n, ∃ f, E n f = t n) → (∀ n f, E (n + 1) f = t (n + 1) → E n f = t n) → (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∃ g, ∀ n, E n g = t n := by
  atlas_forward_decl GlobalTheory.CChartLimit.exists_series_of_compatible
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SurjTens

variable {O σ ι : Type} [CommRing O]

open Classical in

def pushVars (j : σ → ι) (f : MvPowerSeries σ O) : MvPowerSeries ι O :=
  fun β => if h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β then coeff h.choose f else 0

theorem coeff_pushVars_mapDomain {j : σ → ι} (hj : Function.Injective j) (f : MvPowerSeries σ O)
    (α : σ →₀ ℕ) : coeff (Finsupp.mapDomain j α) (pushVars j f) = coeff α f := by
  have h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = Finsupp.mapDomain j α := ⟨α, rfl⟩
  rw [coeff_apply]
  unfold pushVars
  rw [dif_pos h, Finsupp.mapDomain_injective hj h.choose_spec]

theorem coeff_pushVars_of_not {j : σ → ι} (f : MvPowerSeries σ O) (β : ι →₀ ℕ)
    (h : ¬∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β) : coeff β (pushVars j f) = 0 := by
  rw [coeff_apply]
  unfold pushVars
  rw [dif_neg h]

theorem pushVars_add {j : σ → ι} (hj : Function.Injective j) (f g : MvPowerSeries σ O) :
    pushVars j (f + g) = pushVars j f + pushVars j g := by
  ext β
  by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
  · obtain ⟨α, rfl⟩ := h
    simp only [map_add, coeff_pushVars_mapDomain hj]
  · simp only [map_add, coeff_pushVars_of_not _ _ h, add_zero]

theorem pushVars_monomial {j : σ → ι} (hj : Function.Injective j) (α : σ →₀ ℕ) (c : O) :
    pushVars j (monomial α c) = monomial (Finsupp.mapDomain j α) c := by
  classical
  ext β
  by_cases h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = β
  · obtain ⟨α', rfl⟩ := h
    rw [coeff_pushVars_mapDomain hj, coeff_monomial, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hj).eq_iff]
  · rw [coeff_pushVars_of_not _ _ h, coeff_monomial, if_neg]
    rintro rfl
    exact h ⟨α, rfl⟩

theorem pushVars_coe {j : σ → ι} (hj : Function.Injective j) (P : MvPolynomial σ O) :
    pushVars j (P : MvPowerSeries σ O) = ((MvPolynomial.rename j P : MvPolynomial ι O) : MvPowerSeries ι O) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [MvPolynomial.coe_monomial, MvPolynomial.rename_monomial, MvPolynomial.coe_monomial,
      pushVars_monomial hj]
  | add P Q hP hQ =>
    rw [MvPolynomial.coe_add, pushVars_add hj, hP, hQ, map_add, MvPolynomial.coe_add]

theorem eval_coe {R A κ : Type} [CommRing R] [CommRing A] [Algebra R A] (z : κ → A)
    (E : MvPowerSeries κ R →ₐ[R] A) (hE : ∀ i, E (X i) = z i) (P : MvPolynomial κ R) :
    E (P : MvPowerSeries κ R) = MvPolynomial.aeval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom R) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

theorem exists_eval_pushVars (p : ℕ) {A C : Type} [CommRing A] [CommRing C] [Algebra O A] [Algebra O C]
    [Fintype σ] [IsHausdorff (Ideal.span {(p : C)}) C] (j : σ → ι) (hj : Function.Injective j)
    (x : σ → A) (z : ι → C) (φ : A →ₐ[O] C) (evA : MvPowerSeries σ O →ₐ[O] A)
    (E : MvPowerSeries ι O →ₐ[O] C) (hA : IsEval p x evA) (hE : IsEval p z E)
    (hz : ∀ i, z (j i) = φ (x i)) (f : MvPowerSeries σ O) :
    E (pushVars j f) = φ (evA f) := by
  classical
  have hpoly : ∀ P : MvPolynomial σ O, E (pushVars j (P : MvPowerSeries σ O)) = φ (evA P) := by
    intro P
    rw [pushVars_coe hj, eval_coe z E hE.1, eval_coe x evA hA.1, MvPolynomial.aeval_rename]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have hzj : z ∘ j = fun i => φ (x i) := funext hz
    rw [hzj]
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {(p : C)}) inferInstance _ fun m => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨N1, hN1⟩ := hE.2 m
  obtain ⟨N2, hN2⟩ := hA.2 m
  set N := max N1 N2
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  set P : MvPolynomial σ O := trunc' O n f
  set g : MvPowerSeries σ O := f - (P : MvPowerSeries σ O)
  have hg : ∀ α : σ →₀ ℕ, α.degree < N → coeff α g = 0 := by
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  have hgA : (p : A) ^ m ∣ evA g := hN2 g fun α hα => hg α (lt_of_lt_of_le hα (le_max_right _ _))
  have hgE : (p : C) ^ m ∣ E (pushVars j g) := by
    apply hN1
    intro β hβ
    by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
    · obtain ⟨α, rfl⟩ := h
      rw [coeff_pushVars_mapDomain hj]
      apply hg
      rw [Finsupp.degree_mapDomain] at hβ
      exact lt_of_lt_of_le hβ (le_max_left _ _)
    · exact coeff_pushVars_of_not _ _ h
  have hgφ : (p : C) ^ m ∣ φ (evA g) := by
    have := map_dvd φ hgA
    simpa only [map_pow, map_natCast] using this
  have hf : f = g + (P : MvPowerSeries σ O) := by simp [g]
  have key : E (pushVars j f) - φ (evA f) = E (pushVars j g) - φ (evA g) := by
    rw [hf, pushVars_add hj, map_add, map_add, map_add, hpoly P]
    ring
  rw [key]
  exact dvd_sub hgE hgφ

theorem surjective_eval_tmul : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] [IsHausdorff (Ideal.span {(p : A ⊗[O] B)}) (A ⊗[O] B)] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → Function.Surjective E := by
  intro p O A B σ τ _ _ _ _ _ _ _ _ x y evA evB E hA hB hE sA sB
  have hl : ∀ a : A, a ⊗ₜ[O] (1 : B) ∈ E.range := by
    intro a
    obtain ⟨f, rfl⟩ := sA a
    refine ⟨pushVars Sum.inl f, ?_⟩
    have := exists_eval_pushVars p Sum.inl Sum.inl_injective x _ Algebra.TensorProduct.includeLeft
      evA E hA hE (fun i => by simp) f
    simpa using this
  have hr : ∀ b : B, (1 : A) ⊗ₜ[O] b ∈ E.range := by
    intro b
    obtain ⟨g, rfl⟩ := sB b
    refine ⟨pushVars Sum.inr g, ?_⟩
    have := exists_eval_pushVars p Sum.inr Sum.inr_injective y _ Algebra.TensorProduct.includeRight
      evB E hB hE (fun i => by simp) g
    simpa using this
  intro t
  have : t ∈ E.range := by
    induction t using TensorProduct.induction_on with
    | zero => exact Subalgebra.zero_mem _
    | tmul a b =>
      have h := Subalgebra.mul_mem _ (hl a) (hr b)
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
    | add s t hs ht => exact Subalgebra.add_mem _ hs ht
  exact this

end GlobalTheory.SurjTens
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_isEval_tmul_of_surjective : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] [IsHausdorff (Ideal.span {(p : A ⊗[O] B)}) (A ⊗[O] B)] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → Function.Surjective E := by
  atlas_forward_decl GlobalTheory.SurjTens.surjective_eval_tmul
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory

theorem constantCoeff_eq_zero_of_eval_eq_comul : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : O)}) O] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, constantCoeff (μ i) = 0 := by
  intro p O A _ _ _ _ d x E₂ μ hx hE hμ i
  let φ : A ⊗[O] A →ₐ[O] O := Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O A)
    (Bialgebra.counitAlgHom O A) (fun _ _ => Commute.all _ _)
  have hφ : ∀ a b : A, φ (a ⊗ₜ[O] b) = Coalgebra.counit (R := O) a * Coalgebra.counit (R := O) b := by
    intro a b
    simp [φ, Algebra.TensorProduct.lift_tmul, Bialgebra.counitAlgHom_apply]

  have hφc : ∀ a : A, φ (Coalgebra.comul (R := O) a) = Coalgebra.counit (R := O) a := by
    intro a
    have hL : (φ.toLinearMap : A ⊗[O] A →ₗ[O] O) =
        (LinearMap.mul' O O) ∘ₗ (LinearMap.lTensor O (Coalgebra.counit (R := O) (A := A))) ∘ₗ
          (LinearMap.rTensor A (Coalgebra.counit (R := O) (A := A))) := by
      apply TensorProduct.ext'
      intro a b
      simp [hφ]
    have := LinearMap.congr_fun hL (Coalgebra.comul (R := O) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul,
      LinearMap.lTensor_tmul, LinearMap.mul'_apply, one_mul] at this
    exact this
  let c : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] O :=
    { (constantCoeff : MvPowerSeries (Fin d ⊕ Fin d) O →+* O) with
      commutes' := fun r => by
        first
        | exact constantCoeff_C r
        | (rw [MvPowerSeries.algebraMap_apply]; simp)
        | (show constantCoeff (C r) = r; simp)
        | simp [MvPowerSeries.algebraMap_apply'] }
  have hc : ∀ f, c f = constantCoeff f := fun _ => rfl
  have hnil : ∀ j : Fin d ⊕ Fin d, ∃ N : ℕ, (p : O) ∣ (fun _ => (0 : O)) j ^ N :=
    fun _ => ⟨1, by simp⟩
  obtain ⟨⟨E, _, huniq⟩, _⟩ := GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O O (Fin d ⊕ Fin d) (fun _ => (0 : O)) hnil
  have h1 : IsEval p (fun _ => (0 : O)) (φ.comp E₂) := by
    refine ⟨?_, ?_⟩
    · intro j
      rw [AlgHom.comp_apply, hE.1 j]
      cases j with
      | inl k => simp [hφ, hx]
      | inr k => simp [hφ, hx]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨a, ha⟩ := hN f hf
      refine ⟨φ a, ?_⟩
      rw [AlgHom.comp_apply, ha, map_mul, map_pow, map_natCast]
  have h2 : IsEval p (fun _ => (0 : O)) c := by
    refine ⟨fun j => by simp [hc], fun m => ⟨1, fun f hf => ?_⟩⟩
    have : constantCoeff f = 0 := by
      have := hf 0 (by simp)
      simpa [coeff_zero_eq_constantCoeff_apply] using this
    rw [hc, this]; exact dvd_zero _
  have e1 := huniq _ h1
  have e2 := huniq _ h2
  have := congrArg (fun F : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] O => F (μ i)) (e1.trans e2.symm)
  simp only [AlgHom.comp_apply, hμ, hφc, hx, hc] at this
  exact this.symm

end GlobalTheory
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_eq_zero_of_eval_eq_comul' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : O)}) O] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, constantCoeff (μ i) = 0 := by
  atlas_forward_decl GlobalTheory.constantCoeff_eq_zero_of_eval_eq_comul
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.ChartUnit

theorem isEval_comp {p : ℕ} {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (φ : A →ₐ[R] A') (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd φ (hN f hf)
  simpa using this

theorem lift_counit_eq {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] (t : A ⊗[O] A) :
    Algebra.TensorProduct.lift (AlgHom.id O A) ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A))
      (fun _ _ => Commute.all _ _) t = TensorProduct.rid O A (LinearMap.lTensor A (Coalgebra.counit (R := O)) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.smul_def, mul_comm]
  | add s t hs ht => simp only [map_add, hs, ht]

end GlobalTheory.ChartUnit

open GlobalTheory.ChartUnit in

theorem GlobalTheory.chart_unit : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A)}) A] {d : ℕ} (x : Fin d → A) (ev : MvPowerSeries (Fin d) O →ₐ[O] A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p x ev → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, ev (op μ (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0) i) = x i := by
  intro p O A _ _ _ _ d x ev E₂ μ hnil hcu hev hev₂ hcomul i
  set ψ : A ⊗[O] A →ₐ[O] A := Algebra.TensorProduct.lift (AlgHom.id O A)
    ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A)) (fun _ _ => Commute.all _ _) with hψ
  have key := (GlobalTheory.CEval.continuous_eval p O A (Fin d) x hnil).2 ev hev
  let u : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O :=
    Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0)
  have hE' : IsEval p (fun j => ev (u j)) (ψ.comp E₂) := by
    have h := isEval_comp ψ hev₂
    convert h using 2 with j
    rcases j with j | j
    · simp [u, hψ, hev.1 j]
    · simp [u, hψ, hcu j]
  have hu : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [u]
  have := key.1 (Fin d ⊕ Fin d) u (ψ.comp E₂) hu hE' (μ i)
  show ev (subst u (μ i)) = x i
  rw [this, AlgHom.comp_apply, hcomul, hψ, lift_counit_eq, Coalgebra.lTensor_counit_comul]
  simp
end

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_groupLaw_eval_right_unit : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A)}) A] {d : ℕ} (x : Fin d → A) (ev : MvPowerSeries (Fin d) O →ₐ[O] A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p x ev → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, ev (op μ (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0) i) = x i := by
  atlas_forward_decl GlobalTheory.chart_unit
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CommSwap

theorem eval_swap_eq : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  intro p O A _ _ _ _ _ d x E₂ μ hnil hE hμ i
  set y : Fin d ⊕ Fin d → A ⊗[O] A := Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i with hy
  have hny : ∀ j, ∃ N : ℕ, (p : A ⊗[O] A) ∣ y j ^ N := by
    intro j
    rcases j with j | j
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, a ⊗ₜ[O] 1, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inl, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, 1 ⊗ₜ[O] a, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeRight_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inr, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
  set T := (Algebra.TensorProduct.comm O A A).toAlgHom
  set E' := T.comp E₂
  set u : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) O :=
    Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)) with hu
  have hu0 : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [hu]
  have hE' : IsEval p (fun j => E₂ (u j)) E' := by
    refine ⟨?_, ?_⟩
    · intro j
      rcases j with j | j
      · simp [E', T, hu, hE.1, hy]
      · simp [E', T, hu, hE.1, hy]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨c, hc⟩ := hN f hf
      refine ⟨T c, ?_⟩
      simp [E', hc, map_mul, map_pow, map_natCast]
  have key := ((GlobalTheory.CEval.continuous_eval p O (A ⊗[O] A) (Fin d ⊕ Fin d) y hny).2 E₂ hE).1 (Fin d ⊕ Fin d) u E' hu0 hE' (μ i)
  have hs : swap (μ i) = subst u (μ i) := rfl
  rw [hs, key, hμ i]
  simp only [E', T, AlgHom.comp_apply, hμ i]
  exact Coalgebra.comm_comul (R := O) (x i)

end GlobalTheory.CommSwap
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_swap_eq' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  atlas_forward_decl GlobalTheory.CommSwap.eval_swap_eq
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Chart.Assoc

theorem isEval_comp (p : ℕ) {O A B σ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] B) (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨c, hc⟩ := hN f hf
  exact ⟨φ c, by simp [hc, map_mul, map_pow, map_natCast]⟩

theorem constantCoeff_op {O : Type} [CommRing O] {d : ℕ} {τ : Type}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ O) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (j : Fin d) : constantCoeff (op μ u v j) = 0 := by
  have h : ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    rintro (k | k) <;> simp [hu, hv]
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (hμ j)

theorem dvd_pow_map (p : ℕ) {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] (φ : A →ₐ[O] B) {a : A} (h : ∃ N : ℕ, (p : A) ∣ a ^ N) :
    ∃ N : ℕ, (p : B) ∣ φ a ^ N := by
  obtain ⟨N, c, hc⟩ := h
  exact ⟨N, φ c, by rw [← map_pow, hc, map_mul, map_natCast]⟩

end GlobalTheory.Chart.Assoc

namespace GlobalTheory.Chart.Assoc

theorem assoc_eval (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A]
    [IsAdicComplete (Ideal.span {(p : A ⊗[O] (A ⊗[O] A))}) (A ⊗[O] (A ⊗[O] A))] {d : ℕ}
    (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A)
    (E₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] A ⊗[O] (A ⊗[O] A))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hx : ∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (h2 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂)
    (h3 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) E₃)
    (hc : ∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) :
    ∀ i, E₃ (op μ (op μ x1 x2) x3 i) = E₃ (op μ x1 (op μ x2 x3) i) := by
  let Φ₁ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Algebra.TensorProduct.includeLeft (S := O))
  let Φ₃ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) := Algebra.TensorProduct.includeRight
  let Φ₂ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    (Algebra.TensorProduct.assoc O O O A A A).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom O A) (AlgHom.id O A))
  let Φ₄ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Bialgebra.comulAlgHom O A)
  have hnil : ∀ k, ∃ N : ℕ, (p : A ⊗[O] (A ⊗[O] A)) ∣ (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) k ^ N := by
    rintro (k | k | k)
    · exact dvd_pow_map p (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A ⊗[O] A)) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A))) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A))) (hx k)
  have sub := ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ hnil).2 E₃ h3).1
  have c1 : ∀ j, constantCoeff (x1 (R := O) (d := d) j) = 0 := fun j => by simp [x1]
  have c2 : ∀ j, constantCoeff (x2 (R := O) (d := d) j) = 0 := fun j => by simp [x2]
  have c3 : ∀ j, constantCoeff (x3 (R := O) (d := d) j) = 0 := fun j => by simp [x3]
  have ce : ∀ {u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O},
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) →
      ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    intro u v hu hv k; rcases k with k | k <;> simp [hu, hv]
  have L1 : ∀ j, E₃ (op μ x1 x2 j) = Φ₁ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₁ h2
    have := sub _ (Sum.elim x1 x2) (Φ₁.comp E₂) (ce c1 c2) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x1, x2, h3.1, Φ₁, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  have L3 : ∀ j, E₃ (op μ x2 x3 j) = Φ₃ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₃ h2
    have := sub _ (Sum.elim x2 x3) (Φ₃.comp E₂) (ce c2 c3) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x2, x3, h3.1, Φ₃, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  intro i
  have LL : E₃ (op μ (op μ x1 x2) x3 i) = Φ₂ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₂ h2
    have := sub _ (Sum.elim (op μ x1 x2) x3) (Φ₂.comp E₂)
      (ce (constantCoeff_op μ hμ _ _ c1 c2) c3) (by
      convert e using 2 with k
      rcases k with k | k
      · simp only [Sum.elim_inl]
        rw [L1]
        have key : ∀ c : A ⊗[O] A, Φ₁ c = (Algebra.TensorProduct.assoc O O O A A A) (c ⊗ₜ[O] 1) := by
          intro c
          induction c using TensorProduct.induction_on with
          | zero => simp
          | tmul a b => simp [Φ₁, Algebra.TensorProduct.one_def]
          | add a b ha hb => rw [map_add, ha, hb, TensorProduct.add_tmul, map_add]
        rw [key]
        simp [Φ₂]
      · simp [x3, h3.1, Φ₂, Algebra.TensorProduct.one_def]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  have RR : E₃ (op μ x1 (op μ x2 x3) i) = Φ₄ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₄ h2
    have := sub _ (Sum.elim x1 (op μ x2 x3)) (Φ₄.comp E₂)
      (ce c1 (constantCoeff_op μ hμ _ _ c2 c3)) (by
      convert e using 2 with k
      rcases k with k | k
      · simp [x1, h3.1, Φ₄, Algebra.TensorProduct.one_def]
      · simp only [Sum.elim_inr]
        rw [L3]
        simp [Φ₃, Φ₄]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  rw [LL, RR]
  have ka : ∀ w : (A ⊗[O] A) ⊗[O] A,
      (Algebra.TensorProduct.assoc O O O A A A) w = TensorProduct.assoc O A A A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      induction c using TensorProduct.induction_on with
      | zero => simp
      | tmul a a' => simp
      | add c c' hc hc' => rw [TensorProduct.add_tmul, map_add, hc, hc', map_add]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  have k2 : ∀ c : A ⊗[O] A, Φ₂ c = TensorProduct.assoc O A A A (LinearMap.rTensor A (Coalgebra.comul (R := O) (A := A)) c) := by
    intro c
    rw [← ka]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₂]
    | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]
  have k4 : ∀ c : A ⊗[O] A, Φ₄ c = LinearMap.lTensor A (Coalgebra.comul (R := O) (A := A)) c := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₄]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  rw [k2, k4, Coalgebra.coassoc_apply]

end GlobalTheory.Chart.Assoc
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEval_comul_assoc_of_isEval : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] (A ⊗[O] A))}) (A ⊗[O] (A ⊗[O] A))] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (E₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] A ⊗[O] (A ⊗[O] A)) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, constantCoeff (μ i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A)) (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A))) fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) E₃ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₃ (op μ (op μ x1 x2) x3 i) = E₃ (op μ x1 (op μ x2 x3) i) := by
  atlas_forward_decl GlobalTheory.Chart.Assoc.assoc_eval
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.ChartEx

theorem isEval_comp {p : ℕ} {O A A' σ : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A]
    [Algebra O A'] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] A')
    (h : IsEval p x E) : IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨a, ha⟩ := hN f hf
  exact ⟨φ a, by rw [AlgHom.comp_apply, ha, map_mul, map_pow, map_natCast]⟩

theorem nil_map {p : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {a : A}
    (h : ∃ N : ℕ, (p : A) ∣ a ^ N) : ∃ N : ℕ, (p : A') ∣ φ a ^ N := by
  obtain ⟨N, b, hb⟩ := h
  exact ⟨N, φ b, by rw [← map_pow, hb, map_mul, map_natCast]⟩

theorem eq_zero_of_dvd {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {c : O} (h : ∀ m : ℕ, (p : O) ^ m ∣ c) : c = 0 := by
  refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) c fun m => ?_
  obtain ⟨b, hb⟩ := h m
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨b, hb⟩

theorem eq_zero_of_ker {p : ℕ} {O σ : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {A : ℕ → Type} [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)]
    (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n)
    (hker : ∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f)
    {f : MvPowerSeries σ O} (hf : ∀ n, E n f = 0) : f = 0 := by
  ext α
  rw [map_zero]
  refine eq_zero_of_dvd (p := p) fun m => ?_
  obtain ⟨n, hn⟩ := hker m (α.degree + 1)
  exact hn f (hf n) α (Nat.lt_succ_self _)

theorem chart_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, ev, hnil, hev, hres, haug, hsurj, hker⟩ := GlobalTheory.T.exists_coordinates_of_isConnected p C v O hv G hG
  have hc2 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have hc3 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] (G.A n ⊗[O] G.A n))})
      (G.A n ⊗[O] (G.A n ⊗[O] G.A n)) := fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have hcA : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have nil2 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) j ^ N := by
    rintro n (i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
    · simpa using nil_map (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
  have nil3 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] (G.A n ⊗[O] G.A n)) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) j ^ N := by
    rintro n (i | i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
  have hE2 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n ⊗[O] G.A n,
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) E := by
    intro n
    haveI := hc2 n
    exact (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil2 n)).1.exists
  choose E₂ hE₂ using hE2
  have hE3 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n),
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) E := by
    intro n
    haveI := hc3 n
    exact (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil3 n)).1.exists
  choose E₃ hE₃ using hE3
  have hsurj2 : ∀ n, Function.Surjective (E₂ n) := fun n => by
    haveI := hc2 n
    exact GlobalTheory.T.surjective_isEval_tmul_of_surjective p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n)
  have hker2 : ∀ m N : ℕ, ∃ n, ∀ f, E₂ n f = 0 → ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    exact ⟨n, GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn⟩
  have hker3 : ∀ m N : ℕ, ∃ n, ∀ f, E₃ n f = 0 → ∀ α : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    have hn2 := GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn
    have hpt : (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) fun j => (1 : G.A n) ⊗ₜ[O] (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] x n i) j)) = (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) := by
      funext j
      rcases j with j | j | j <;> rfl
    have hE3' := hE₃ n
    rw [← hpt] at hE3'
    exact ⟨n, GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) _ (ev n) (E₂ n) (E₃ n) m N (hev n) (hE₂ n) hE3' (hsurj n) (hsurj2 n) hn hn2⟩
  have hstep : ∀ i n f, E₂ (n + 1) f = Coalgebra.comul (R := O) (x (n + 1) i) →
      E₂ n f = Coalgebra.comul (R := O) (x n i) := by
    intro i n f hf
    let ρ : G.A (n + 1) ⊗[O] G.A (n + 1) →ₐ[O] G.A n ⊗[O] G.A n :=
      Algebra.TensorProduct.map (AlgHomClass.toAlgHom (G.res n)) (AlgHomClass.toAlgHom (G.res n))
    have hρ : ρ.comp (E₂ (n + 1)) = E₂ n := by
      haveI := hc2 n
      refine (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil2 n)).1.unique ?_ (hE₂ n)
      have h1 := isEval_comp ρ (hE₂ (n + 1))
      convert h1 using 1
      funext j
      rcases j with j | j <;> simp [ρ, hres]
    rw [← hρ, AlgHom.comp_apply, hf]
    exact (CoalgHomClass.map_comp_comul_apply (G.res n) (x (n + 1) i)).trans (by rw [hres])
  have hμ : ∀ i, ∃ g, ∀ n, E₂ n g = Coalgebra.comul (R := O) (x n i) := by
    intro i
    exact GlobalTheory.T.exists_series_of_compatible' p O (Fin d ⊕ Fin d) (fun n => G.A n ⊗[O] G.A n) (fun n => (hc2 n).toIsHausdorff) _ E₂
      (fun n => Coalgebra.comul (R := O) (x n i)) hE₂ (fun n => hsurj2 n _) (hstep i) hker2
  choose μ hμ using hμ
  have hconst : ∀ i, constantCoeff (μ i) = 0 :=
    GlobalTheory.T.constantCoeff_eq_zero_of_eval_eq_comul' p O (G.A 0) (x 0) (E₂ 0) μ (haug 0) (hE₂ 0) (fun i => hμ i 0)
  refine ⟨d, ⟨⟨x, ev, E₂, μ, hnil, hev, hE₂, hres, haug, hsurj, hker, ?_, fun n i => hμ i n⟩⟩⟩
  refine ⟨hconst, ?_, fun i => ?_, ?_⟩
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) ev hker fun n => ?_)
    haveI := hcA n
    rw [map_sub, GlobalTheory.T.formalChart_groupLaw_eval_right_unit p O (G.A n) (x n) (ev n) (E₂ n) μ (hnil n) (haug n) (hev n) (hE₂ n) (fun i => hμ i n) i,
      (hev n).1 i, sub_self]
  · refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₂ hker2 fun n => ?_)
    haveI := hc2 n
    rw [map_sub, GlobalTheory.T.eval_swap_eq' p O (G.A n) (x n) (E₂ n) μ (hnil n) (hE₂ n) (fun i => hμ i n) i, sub_self]
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₃ hker3 fun n => ?_)
    haveI := hc3 n
    rw [map_sub, GlobalTheory.T.isEval_comul_assoc_of_isEval p O (G.A n) (x n) (E₂ n) (E₃ n) μ (hnil n) hconst (hE₂ n) (hE₃ n) (fun i => hμ i n) i, sub_self]

end GlobalTheory.ChartEx
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pDivGroupFormalChart_of_connected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  atlas_forward_decl GlobalTheory.ChartEx.chart_exists
end
