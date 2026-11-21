import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTwoMulRhoSubTr

section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open scoped Pointwise

theorem prod_mul_eq_zero_of_mem_span {S X ι : Type} [CommRing S] [Fintype ι] (N : ι → X → S) (W : S)
    (h : ∀ c : ι → X, (∏ j, N j (c j)) * W = 0) (f : ι → S)
    (hf : ∀ j, f j ∈ Ideal.span (Set.range (N j))) : (∏ j, f j) * W = 0 := by
  classical
  have hmem : (∏ j, f j) ∈ Ideal.span (∏ j, Set.range (N j)) := by
    rw [← Ideal.prod_span]
    exact Ideal.prod_mem_prod fun j _ => hf j
  refine Submodule.span_induction (p := fun x _ => x * W = 0) ?_ ?_ ?_ ?_ hmem
  · intro x hx
    obtain ⟨e, he, rfl⟩ := (Set.mem_finset_prod _ _ _).1 hx
    have : ∀ j, ∃ y, N j y = e j := fun j => he (Finset.mem_univ j)
    choose c hc using this
    simpa [hc] using h c
  · simp
  · intro x y _ _ hx hy; rw [add_mul, hx, hy, add_zero]
  · intro a x _ hx; rw [smul_eq_mul, mul_assoc, hx, mul_zero]

end GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

theorem mapMatrix_algebraMap_fin {B K : Type} [CommRing B] [CommRing K] (g : B →+* K) {n : ℕ} (x : B) :
    g.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) x) = algebraMap K (Matrix (Fin n) (Fin n) K) (g x) := by
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

theorem map_mul_projMat_eq_smul (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (B : Type) [CommRing B] (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K]
    (g : B →+* K) :
    lieIdeal b βB M ≤ RingHom.ker g → ∀ (i : Fin D.a) (c : 𝓞 D.F),
      (M c).map g * (projMat b βB M i).map g = g (βB (b.t i c)) • (projMat b βB M i).map g := by
  intro hI i c
  classical
  set M' : 𝓞 D.F →+* Matrix (Fin n) (Fin n) K := g.mapMatrix.comp M with hM'
  have hcomm : ∀ a ∈ Set.range M', ∀ a' ∈ Set.range M', a * a' = a' * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; rw [← map_mul, ← map_mul, mul_comm]
  let S := Algebra.adjoin K (Set.range M')
  letI : CommRing S := Algebra.adjoinCommRingOfComm K hcomm
  let m : 𝓞 D.F → S := fun x => ⟨M' x, Algebra.subset_adjoin ⟨x, rfl⟩⟩
  let sc : R → S := fun r => algebraMap K S (g (βB r))
  let N : Fin D.a → 𝓞 D.F → S := fun j x => m x - sc (b.t j x)
  let WS : S := m D.ω - sc ((D.tr : R) - b.ρ)
  let α : Fin D.a → S := fun j => (comaxC b i j).sum fun x r => sc r * N j x
  let PS : S := (List.ofFn fun j => if j = i then 1 else α j).prod * (sc (uInv b) * WS)
  have hsc : ∀ r, S.val (sc r) = g.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) (βB r)) := by
    intro r; rw [AlgHom.commutes, mapMatrix_algebraMap_fin]
  have hm : ∀ x, S.val (m x) = g.mapMatrix (M x) := fun _ => rfl
  have hN : ∀ j x, S.val (N j x) =
      g.mapMatrix (M x - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t j x))) := by
    intro j x; simp only [N, map_sub, hm, hsc]
  have hW : S.val WS = g.mapMatrix (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ))) := by
    simp only [WS, map_sub, hm, hsc]
  have hα : ∀ j, S.val (α j) = g.mapMatrix (alphaMat b βB M i j) := by
    intro j; simp only [α, alphaMat, Finsupp.sum, map_sum, map_mul, hsc, hN]
  have hP : S.val PS = g.mapMatrix (projMat b βB M i) := by
    simp only [PS, projMat, map_mul, map_list_prod, List.map_ofFn, hsc, hW]
    congr 2
    congr 1
    funext j
    simp only [Function.comp_apply]
    split_ifs
    · rw [map_one, map_one]
    · exact hα j
  have hlie : ∀ c' : Fin D.a → 𝓞 D.F, (∏ j, N j (c' j)) * WS = 0 := by
    intro c'
    have h0 : g.mapMatrix (lieMat b βB M c') = 0 := by
      ext k l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
      exact hI (Ideal.subset_span ⟨c', k, l, rfl⟩)
    rw [← List.prod_ofFn]
    refine (map_eq_zero_iff S.val Subtype.val_injective).1 ?_
    rw [← h0, lieMat, map_mul, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, hW]
    congr 2
    congr 1
    funext j
    simp only [Function.comp_apply, hN]
  have hkey : N i c * PS = 0 := by
    have hf : ∀ j, (if j = i then N i c else α j) ∈ Ideal.span (Set.range (N j)) := by
      intro j; split_ifs with hj
      · subst hj; exact Ideal.subset_span ⟨c, rfl⟩
      · exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)
    have h1 := prod_mul_eq_zero_of_mem_span N WS hlie _ hf
    have h2 : N i c * (∏ j, if j = i then (1 : S) else α j) = ∏ j, if j = i then N i c else α j := by
      rw [show (∏ j, if j = i then N i c else α j) =
          ∏ j, ((if j = i then N i c else 1) * if j = i then 1 else α j) from
          Finset.prod_congr rfl fun j _ => by split_ifs <;> simp, Finset.prod_mul_distrib, Finset.prod_ite_eq']
      simp
    simp only [PS, List.prod_ofFn]
    rw [← mul_assoc, h2, mul_left_comm, h1, mul_zero]
  have h3 := congrArg S.val hkey
  rw [map_mul, map_zero, hN, hP, map_sub, mapMatrix_algebraMap_fin, sub_mul] at h3
  change g.mapMatrix (M c) * g.mapMatrix (projMat b βB M i) = _
  rw [Algebra.smul_def, ← sub_eq_zero]
  exact h3

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end

section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K),
    lieIdeal b βB M ≤ RingHom.ker g → ∀ (i : Fin D.a) (c : 𝓞 D.F),
      (M c).map g * (projMat b βB M i).map g = g (βB (b.t i c)) • (projMat b βB M i).map g := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.map_mul_projMat_eq_smul  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

section Scal

variable {B K : Type} [CommRing B] [CommRing K] {n : ℕ} (g : B →+* K) (v : Fin n → K)

theorem algebraMap_map_mulVec (x : B) :
    (algebraMap B (Matrix (Fin n) (Fin n) B) x).map g *ᵥ v = g x • v := by
  ext k
  simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

theorem map_mul_mulVec_of_scal {X Y : Matrix (Fin n) (Fin n) B} {c d : K}
    (hX : X.map g *ᵥ v = c • v) (hY : Y.map g *ᵥ v = d • v) : (X * Y).map g *ᵥ v = (c * d) • v := by
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul, hX, smul_smul, mul_comm]

theorem map_sub_mulVec_of_scal {X Y : Matrix (Fin n) (Fin n) B} {c d : K}
    (hX : X.map g *ᵥ v = c • v) (hY : Y.map g *ᵥ v = d • v) : (X - Y).map g *ᵥ v = (c - d) • v := by
  rw [Matrix.map_sub _ (map_sub g), Matrix.sub_mulVec, hX, hY, sub_smul]

theorem map_sum_mulVec_of_scal {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin n) (Fin n) B) (c : ι → K)
    (h : ∀ x ∈ s, (X x).map g *ᵥ v = c x • v) : (∑ x ∈ s, X x).map g *ᵥ v = (∑ x ∈ s, c x) • v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.map_add _ (map_add g), Matrix.add_mulVec,
      h a (Finset.mem_insert_self _ _), ih (fun x hx => h x (Finset.mem_insert_of_mem hx)), add_smul]

theorem map_list_prod_mulVec_of_fix (L : List (Matrix (Fin n) (Fin n) B))
    (h : ∀ X ∈ L, X.map g *ᵥ v = v) : L.prod.map g *ᵥ v = v := by
  induction L with
  | nil => rw [List.prod_nil, Matrix.map_one _ (map_zero g) (map_one g), Matrix.one_mulVec]
  | cons X L ih =>
    rw [List.prod_cons, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY)), h X (by simp)]

end Scal

theorem projMat_map_mulVec_of_eig : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K)
    (i : Fin D.a) (v : Fin n → K), (∀ c : 𝓞 D.F, (M c).map g *ᵥ v = g (βB (b.t i c)) • v) →
      (projMat b βB M i).map g *ᵥ v = v := by
  intro p _ D R _ b B _ βB n M K _ g i v hv
  have hα : ∀ j, j ≠ i → (alphaMat b βB M i j).map g *ᵥ v = v := by
    intro j hj
    have hij : i ≠ j := fun h => hj h.symm
    unfold alphaMat
    rw [Finsupp.sum, map_sum_mulVec_of_scal g v _ _
      (fun x => g (βB (comaxC b i j x)) * (g (βB (b.t i x)) - g (βB (b.t j x))))
      (fun x _ => map_mul_mulVec_of_scal g v (algebraMap_map_mulVec g v _)
        (map_sub_mulVec_of_scal g v (hv x) (algebraMap_map_mulVec g v _)))]
    have hs := congrArg (fun y => g (βB y)) (comaxC_spec b hij)
    simp only [Finsupp.sum, map_sum, map_mul, map_sub, map_one] at hs
    rw [hs, one_smul]
  have hlast := map_mul_mulVec_of_scal g v (algebraMap_map_mulVec g v (βB (uInv b)))
    (map_sub_mulVec_of_scal g v (hv D.ω) (algebraMap_map_mulVec g v (βB ((D.tr : R) - b.ρ))))
  have h1 : g (βB (uInv b)) * (g (βB (b.t i D.ω)) - g (βB ((D.tr : R) - b.ρ))) = 1 := by
    have hu := congrArg (fun y => g (βB y)) (uInv_mul b)
    simp only [map_mul, map_sub, map_one, map_intCast, map_ofNat] at hu ⊢
    rw [b.t_ω]
    linear_combination hu
  rw [h1, one_smul] at hlast
  unfold projMat
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, hlast]
  refine map_list_prod_mulVec_of_fix g v _ ?_
  intro X hX
  rw [List.mem_ofFn] at hX
  obtain ⟨j, rfl⟩ := hX
  split_ifs with h
  · rw [Matrix.map_one _ (map_zero g) (map_one g), Matrix.one_mulVec]
  · exact hα j h

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end

section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K)
    (i : Fin D.a) (v : Fin n → K), (∀ c : 𝓞 D.F, (M c).map g *ᵥ v = g (βB (b.t i c)) • v) →
      (projMat b βB M i).map g *ᵥ v = v := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig  <;> assumption)
end

section
open Matrix TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemRankStalk

theorem finrank_range_baseChange_eq {R S M : Type} [CommRing R] [Field S] [Algebra R S]
    [AddCommGroup M] [Module R M] (e : M →ₗ[R] M) (he : e ∘ₗ e = e) :
    Module.finrank S (LinearMap.range (e.baseChange S)) =
      Module.finrank S (S ⊗[R] LinearMap.range e) := by
  let r : M →ₗ[R] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[R] M := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  have hir : e = i ∘ₗ r := LinearMap.ext fun _ => rfl
  have hS : r.baseChange S ∘ₗ i.baseChange S = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hsurj : Function.Surjective (r.baseChange S) := fun x =>
    ⟨i.baseChange S x, LinearMap.congr_fun hS x⟩
  have hinj : Function.Injective (i.baseChange S) := fun x y hxy => by
    have := congrArg (r.baseChange S) hxy
    rwa [← LinearMap.comp_apply, hS, ← LinearMap.comp_apply, hS] at this
  have h2 : e.baseChange S = i.baseChange S ∘ₗ r.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← hir]
  rw [h2, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj),
    LinearMap.finrank_range_of_inj hinj]

theorem finrank_range_map_eq_rankAtStalk (A : Type) [CommRing A] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (hP : P * P = P) (k : Type) [Field k] (g : A →+* k) :
    Module.finrank k (LinearMap.range (P.map g).mulVecLin) =
      Module.rankAtStalk (LinearMap.range P.mulVecLin)
        (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
  letI : Algebra A k := g.toAlgebra
  set e : (Fin n → A) →ₗ[A] (Fin n → A) := P.mulVecLin with he_def
  have he : e ∘ₗ e = e := by
    rw [he_def, ← Matrix.mulVecLin_mul, hP]

  let r : (Fin n → A) →ₗ[A] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[A] (Fin n → A) := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  haveI : Module.Projective A (LinearMap.range e) := Module.Projective.of_split i r hri

  have hst := Module.rankAtStalk_baseChange (R := A) (M := LinearMap.range e) (S := k) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at hst
  have hcomap : PrimeSpectrum.comap (algebraMap A k) (⊥ : PrimeSpectrum k) =
      (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
    ext x
    change x ∈ Ideal.comap (algebraMap A k) (⊥ : Ideal k) ↔ x ∈ RingHom.ker g
    rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker]
    rfl
  rw [hcomap] at hst
  rw [← hst, ← finrank_range_baseChange_eq e he]

  let Φ : k ⊗[A] (Fin n → A) ≃ₗ[k] (Fin n → k) := TensorProduct.piScalarRight A k k (Fin n)
  have hΦ : ∀ x, Φ (e.baseChange k x) = (P.map g).mulVecLin (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      ext j
      simp [Φ, e, TensorProduct.piScalarRight_apply, Matrix.mulVec, dotProduct,
        Finset.mul_sum, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    | add x y hx hy => simp only [map_add, hx, hy]
  have hrange : LinearMap.range (P.map g).mulVecLin =
      (LinearMap.range (e.baseChange k)).map (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) := by
    have hc : (P.map g).mulVecLin ∘ₗ (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) =
        (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) ∘ₗ e.baseChange k :=
      LinearMap.ext fun x => (hΦ x).symm
    rw [← LinearMap.range_comp, ← hc, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range Φ)]
  rw [hrange, LinearEquiv.finrank_map_eq]
  rfl

end GlobalTheory.IdemRankStalk
end
end

section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_map_idempotent_eq_rankAtStalk : ∀ (A : Type) [CommRing A] (n : ℕ) (P : Matrix (Fin n) (Fin n) A), P * P = P →
    ∀ (k : Type) [Field k] (g : A →+* k),
      Module.finrank k (LinearMap.range (P.map g).mulVecLin) =
        Module.rankAtStalk (LinearMap.range P.mulVecLin) (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
  first | (exact @GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (exact GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (intros; apply GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk  <;> assumption)
end

section
open Matrix

namespace GlobalTheory

theorem range_idempotent_projective {A : Type} [CommRing A] (n : ℕ) (P : Matrix (Fin n) (Fin n) A)
    (hP : P * P = P) : Module.Projective A (LinearMap.range P.mulVecLin) := by
  refine Module.Projective.of_split (LinearMap.range P.mulVecLin).subtype P.mulVecLin.rangeRestrict ?_
  ext ⟨v, w, rfl⟩ j
  simp [Matrix.mulVec_mulVec, hP]

theorem exists_rank_ideal_of_idempotent : ∀ (A : Type) [CommRing A] (I : Type) [Fintype I] (n : ℕ) (P : I → Matrix (Fin n) (Fin n) A),
    (∀ i, P i * P i = P i) → ∀ (m : ℕ), ∃ x : A, ∀ (T : Type) [CommRing T] (f : A →+* T),
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : I),
          Module.rankAtStalk (LinearMap.range (P i).mulVecLin)
            (⟨RingHom.ker (h.comp f), RingHom.ker_isPrime _⟩ : PrimeSpectrum A) = m) ↔ f x = 0) := by
  intro A _ I _ n P hP m
  let V : Set (PrimeSpectrum A) :=
    ⋂ i, {q | Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m}
  have hV : IsClopen V := by
    refine isClopen_iInter_of_finite fun i => ?_
    have := range_idempotent_projective n (P i) (hP i)
    have := Module.finitePresentation_of_projective A (LinearMap.range (P i).mulVecLin)
    exact (Module.isLocallyConstant_rankAtStalk (R := A)
      (M := LinearMap.range (P i).mulVecLin)).isClopen_fiber m
  obtain ⟨e, x, hmul, hadd, hVe⟩ := PrimeSpectrum.isClopen_iff_mul_add.mp hV
  refine ⟨x, fun T _ f => ?_⟩
  have hmem : ∀ q : PrimeSpectrum A, q ∈ V ↔ e ∉ q.asIdeal := by
    intro q; rw [hVe]; rfl
  have hmem' : ∀ q : PrimeSpectrum A, q ∈ V ↔ ∀ i, Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m := by
    intro q; simp [V]
  constructor
  · intro H
    have hxx : f x * f x = f x := by
      have : x * x = x := by
        have h1 : x = x * (e + x) := by rw [hadd, mul_one]
        calc x * x = x * (e + x) - x * e := by ring
          _ = x := by rw [← h1, mul_comm x e, hmul, sub_zero]
      rw [← map_mul, this]
    have hnil : IsNilpotent (f x) := by
      rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
      intro (Q : Ideal T) hQ
      haveI : Q.IsPrime := hQ
      let k := AlgebraicClosure (FractionRing (T ⧸ Q))
      let h : T →+* k := (algebraMap (FractionRing (T ⧸ Q)) k).comp
        ((algebraMap (T ⧸ Q) (FractionRing (T ⧸ Q))).comp (Ideal.Quotient.mk Q))
      have hker : RingHom.ker h = Q := by
        ext t
        simp only [h, RingHom.mem_ker, RingHom.comp_apply]
        rw [map_eq_zero_iff _ (algebraMap (FractionRing (T ⧸ Q)) k).injective,
          IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      have hq := (hmem _).mp ((hmem' _).mpr (H k h))
      have : e * x ∈ RingHom.ker (h.comp f) := by rw [hmul]; exact Ideal.zero_mem _
      rcases (RingHom.ker_isPrime (h.comp f)).mem_or_mem this with he | hx
      · exact absurd he hq
      · rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hker] at hx
        exact hx
    obtain ⟨N, hN⟩ := hnil
    have : ∀ j : ℕ, f x ^ (j + 1) = f x := by
      intro j; induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, ih, hxx]
    rcases N with _ | N
    · simp at hN; exact (subsingleton_of_zero_eq_one hN.symm).elim _ _
    · rw [this] at hN; exact hN
  · intro hx k _ _ h i
    refine ((hmem' _).mp ?_) i
    rw [hmem]
    show e ∉ RingHom.ker (h.comp f)
    rw [RingHom.mem_ker, RingHom.comp_apply]
    have : f e = 1 := by
      have := congrArg f hadd
      rw [map_add, hx, add_zero, map_one] at this; exact this
    rw [this, map_one]; exact one_ne_zero

end GlobalTheory
end

section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_ideal_of_idempotent' : ∀ (A : Type) [CommRing A] (I : Type) [Fintype I] (n : ℕ) (P : I → Matrix (Fin n) (Fin n) A),
    (∀ i, P i * P i = P i) → ∀ (m : ℕ), ∃ x : A, ∀ (T : Type) [CommRing T] (f : A →+* T),
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : I),
          Module.rankAtStalk (LinearMap.range (P i).mulVecLin)
            (⟨RingHom.ker (h.comp f), RingHom.ker_isPrime _⟩ : PrimeSpectrum A) = m) ↔ f x = 0) := by
  first | (exact @GlobalTheory.exists_rank_ideal_of_idempotent) | (exact GlobalTheory.exists_rank_ideal_of_idempotent) | (intros; apply GlobalTheory.exists_rank_ideal_of_idempotent  <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open Matrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

theorem exists_ideal_rank_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B),
    ∃ K₂ : Ideal B, ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f) := by
  intro p _ D R _ b B _ βB n M
  set J := lieIdeal b βB M with hJdef
  let P : Fin D.a → Matrix (Fin n) (Fin n) (B ⧸ J) := fun i => (projMat b βB M i).map (Ideal.Quotient.mk J)
  have hJmk : J ≤ RingHom.ker (Ideal.Quotient.mk J) := fun a ha => by
    rw [RingHom.mem_ker]; exact Ideal.Quotient.eq_zero_iff_mem.2 ha

  have hrange : ∀ (K : Type) [CommRing K] (g : B →+* K), J ≤ RingHom.ker g → ∀ i : Fin D.a,
      (eigSub (matAct M g) ((g.comp βB).comp (b.t i)) : Set (Fin n → K)) =
        LinearMap.range ((projMat b βB M i).map g).mulVecLin := by
    intro K _ g hg i
    ext v
    simp only [SetLike.mem_coe, mem_eigSub, matAct_apply, LinearMap.mem_range, Matrix.mulVecLin_apply,
      RingHom.coe_comp, Function.comp_apply]
    constructor
    · intro hv
      exact ⟨v, GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector p D R b B βB n M K g i v hv⟩
    · rintro ⟨w, rfl⟩ c
      rw [Matrix.mulVec_mulVec, GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar p D R b B βB n M K g hg i c, Matrix.smul_mulVec]
  have hidem : ∀ i, P i * P i = P i := by
    intro i
    apply (Matrix.toLin' (R := B ⧸ J) (m := Fin n) (n := Fin n)).injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec]
    apply GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector p D R b B βB n M _ (Ideal.Quotient.mk J) i
    intro c
    rw [Matrix.mulVec_mulVec, GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar p D R b B βB n M _ _ hJmk i c, Matrix.smul_mulVec]
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_rank_ideal_of_idempotent' (B ⧸ J) (Fin D.a) n P hidem D.m
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.span {x'}, fun T _ f hf => ?_⟩
  have hfa : ∀ a ∈ J, f a = 0 := fun a ha => RingHom.mem_ker.1 (hf ha)
  let fb : B ⧸ J →+* T := Ideal.Quotient.lift J f hfa
  have hfb : fb.comp (Ideal.Quotient.mk J) = f := Ideal.Quotient.lift_comp_mk _ _ _
  rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  have hx' := hx T fb
  rw [show fb (Ideal.Quotient.mk J x') = f x' from Ideal.Quotient.lift_mk _ _ _] at hx'
  rw [← hx']
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun h => forall_congr' fun i => ?_
  have e1 : eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i)) =
      LinearMap.range ((P i).map (h.comp fb)).mulVecLin := by
    apply SetLike.coe_injective
    show (eigSub (matAct M (h.comp f)) (((h.comp f).comp βB).comp (b.t i)) : Set (Fin n → k)) = _
    rw [hrange k (h.comp f) (fun a ha => by simp [hfa a ha]) i]
    congr 3
  rw [e1, GlobalTheory.T.finrank_range_map_idempotent_eq_rankAtStalk (B ⧸ J) n (P i) (hidem i) k (h.comp fb)]

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_geometric_rank_iff_of_lie_condition : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B),
    ∃ K₂ : Ideal B, ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f) := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.exists_ideal_rank_iff) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.exists_ideal_rank_iff) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.exists_ideal_rank_iff  <;> assumption)
end
