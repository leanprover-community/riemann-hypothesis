import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem midI_val (r : ℕ) (j : Fin r) : (midI r j).val = j.val + 1 := by
  simp [midI]

theorem midI_inj (r : ℕ) (i j : Fin r) : midI r i = midI r j ↔ i = j := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [midI_val, midI_val] at this
    exact Fin.ext (by omega)
  · rintro rfl; rfl

theorem midI_lt (r : ℕ) {i j : Fin r} (h : i < j) : midI r i < midI r j := by
  rw [Fin.lt_iff_val_lt_val, midI_val, midI_val]
  have := Fin.lt_iff_val_lt_val.mp h
  omega


theorem midOf_midI (r : ℕ) (j : Fin r) : midOf (midI r j) = some j := by
  have hv := midI_val r j
  have hj := j.isLt
  unfold midOf
  rw [dif_pos (by rw [hv]; exact ⟨Nat.succ_pos _, by omega⟩)]
  congr 1

theorem midOf_cases {r : ℕ} (t : Fin (r + 1 + 1)) :
    (∃ j, t = midI r j) ∨ (midOf t = none ∧ (t = 0 ∨ t = Fin.last (r + 1))) := by
  have ht := t.isLt
  by_cases h : 0 < t.val ∧ t.val < r + 1
  · left
    refine ⟨⟨t.val - 1, by omega⟩, ?_⟩
    ext
    rw [midI_val]
    dsimp only
    omega
  · right
    refine ⟨by unfold midOf; rw [dif_neg h], ?_⟩
    by_cases h0 : t.val = 0
    · left
      exact Fin.ext (by simp [h0])
    · right
      exact Fin.ext (by simp; omega)

theorem midOf_none_ne {r : ℕ} {t : Fin (r + 1 + 1)} (h : midOf t = none) (j : Fin r) : midI r j ≠ t := by
  rintro rfl
  rw [midOf_midI] at h
  exact Option.some_ne_none _ h

theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

theorem subY_X_none (A : Type) [CommRing A] (r : ℕ) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    subY A r (X (a, t)) = X (a, t) := by
  simp only [subY, aeval_X, h]

theorem subY_C (A : Type) [CommRing A] (r : ℕ) (a : A) : subY A r (C a) = C (C a) := by
  simp [subY]

section MAH

variable {R S1 S2 σ : Type} [CommRing R] [CommRing S1] [CommRing S2] [Algebra R S1] [Algebra R S2]

theorem mAH_coeff (f : S1 →ₐ[R] S2) (p : MvPolynomial σ S1) (u : σ →₀ ℕ) : coeff u (mapAlgHom f p) = f (coeff u p) := by
  show coeff u (map (f : S1 →+* S2) p) = _
  rw [coeff_map]
  rfl

theorem mAH_C (f : S1 →ₐ[R] S2) (b : S1) : mapAlgHom f (C b : MvPolynomial σ S1) = C (f b) := by
  show map (f : S1 →+* S2) (C b) = _
  rw [map_C]
  rfl

theorem mAH_X (f : S1 →ₐ[R] S2) (w : σ) : mapAlgHom f (X w : MvPolynomial σ S1) = X w := by
  show map (f : S1 →+* S2) (X w) = _
  rw [map_X]

end MAH

theorem mAH_subY_mid {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (f : MvPolynomial (Fin r × Fin r) A →ₐ[A] S) (a : Fin (r + 1 + 1)) (j : Fin r) :
    mapAlgHom f (subY A r (X (a, midI r j))) = ∑ i : Fin r, C (f (X (i, j))) * X (a, midI r i) := by
  rw [subY_X_mid]
  simp only [map_sum, map_mul, mAH_C, mAH_X]

theorem mAH_subY_none {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (f : MvPolynomial (Fin r × Fin r) A →ₐ[A] S) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    mapAlgHom f (subY A r (X (a, t))) = X (a, t) := by
  rw [subY_X_none A r a t h, mAH_X]

section Coef

variable {A : Type} [CommRing A] {r : ℕ} {σ : Type}

def CoefHom (μ : Fin r → ℕ) (h : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)) : Prop :=
  ∀ u, IsWeightedHomogeneous (colW r r) (coeff u h) μ

theorem CoefHom.sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)) (μ : Fin r → ℕ)
    (h : ∀ i ∈ s, CoefHom μ (f i)) : CoefHom μ (∑ i ∈ s, f i) := by
  intro u
  rw [coeff_sum]
  exact IsWeightedHomogeneous.sum _ _ _ (fun i hi => h i hi u)

theorem CoefHom.mul {μ μ' : Fin r → ℕ} {h1 h2 : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)}
    (a : CoefHom μ h1) (b : CoefHom μ' h2) : CoefHom (μ + μ') (h1 * h2) := by
  classical
  intro u
  rw [coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ (fun x _ => (a x.1).mul (b x.2))

theorem CoefHom.ofC {μ : Fin r → ℕ} {b : MvPolynomial (Fin r × Fin r) A} (hb : IsWeightedHomogeneous (colW r r) b μ) :
    CoefHom (σ := σ) μ (C b) := by
  classical
  intro u
  rw [coeff_C]
  split_ifs
  · exact hb
  · exact isWeightedHomogeneous_zero _ _ _

theorem CoefHom.ofX (w : σ) : CoefHom (A := A) (r := r) 0 (X w) := by
  classical
  intro u
  rw [coeff_X']
  split_ifs
  · exact isWeightedHomogeneous_one _ _
  · exact isWeightedHomogeneous_zero _ _ _

theorem CoefHom.one : CoefHom (A := A) (r := r) (σ := σ) 0 1 := by
  classical
  intro u
  rw [coeff_one]
  split_ifs
  · exact isWeightedHomogeneous_one _ _
  · intro d hd
    simp at hd

theorem CoefHom.pow {μ : Fin r → ℕ} {h : MvPolynomial σ (MvPolynomial (Fin r × Fin r) A)} (a : CoefHom μ h) (n : ℕ) :
    CoefHom (n • μ) (h ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact CoefHom.one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul a

theorem CoefHom.prod {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ (MvPolynomial (Fin r × Fin r) A))
    (μ : ι → Fin r → ℕ) (h : ∀ i ∈ s, CoefHom (μ i) (f i)) : CoefHom (∑ i ∈ s, μ i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact CoefHom.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end Coef

theorem subY_gen_coefHom (A : Type) [CommRing A] (r : ℕ) (w : Fin (r + 1 + 1) × Fin (r + 1 + 1)) :
    CoefHom (fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) (subY A r (X w)) := by
  obtain ⟨a, t⟩ := w
  rcases midOf_cases t with ⟨j, rfl⟩ | ⟨hn, -⟩
  · rw [subY_X_mid]
    have hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, midI r j) (midI r j')) = colW r r (j, j) := by
      funext j'
      simp only [colW, Pi.single_apply, midI_inj]
    rw [hf]
    apply CoefHom.sum
    intro i _
    have h := (CoefHom.ofC (σ := Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (isWeightedHomogeneous_X A (colW r r) (i, j))).mul (CoefHom.ofX (A := A) (r := r) (a, midI r i))
    rw [add_zero] at h
    exact h
  · rw [subY_X_none _ _ _ _ hn]
    have hf : (fun j' : Fin r => colW (r + 1 + 1) (r + 1 + 1) (a, t) (midI r j')) = 0 := by
      funext j'
      simp [colW, Pi.single_apply, midOf_none_ne hn j']
    rw [hf]
    exact CoefHom.ofX _

theorem subY_coefHom (A : Type) [CommRing A] (r : ℕ) (ν : Fin (r + 1 + 1) → ℕ)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) v ν) :
    CoefHom (fun j => ν (midI r j)) (subY A r v) := by
  classical
  rw [v.as_sum, map_sum]
  apply CoefHom.sum
  intro m hm
  have hw : Finsupp.weight (colW (r + 1 + 1) (r + 1 + 1)) m = ν := hv (mem_support_iff.mp hm)
  rw [monomial_eq, map_mul, subY_C, Finsupp.prod, map_prod]
  have hP : CoefHom (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j))
      (∏ w ∈ m.support, subY A r (X w ^ m w)) := by
    apply CoefHom.prod
    intro w _
    rw [map_pow]
    exact (subY_gen_coefHom A r w).pow _
  have hC : CoefHom (σ := Fin (r + 1 + 1) × Fin (r + 1 + 1)) (0 : Fin r → ℕ) (C (C (coeff m v))) := by
    apply CoefHom.ofC
    intro d hd
    rw [coeff_C] at hd
    split_ifs at hd with h0
    · subst h0
      simp
    · exact absurd rfl hd
  have h := hC.mul hP
  rw [zero_add] at h
  have hsum : (∑ w ∈ m.support, m w • fun j => colW (r + 1 + 1) (r + 1 + 1) w (midI r j)) =
      fun j => ν (midI r j) := by
    funext j
    rw [← hw]
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [hsum] at h
  exact h

theorem subY_inv (A : Type) [CommRing A] (r : ℕ) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen A l j v = rename some v) (l j : Fin r) (hlj : l < j)
    (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    colAddGen A l j (coeff u (subY A r v)) = rename some (coeff u (subY A r v)) := by
  classical
  let Φ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    mapAlgHom (colAddGen A l j)
  let Ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A) →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    mapAlgHom (rename some)
  let θ : MvPolynomial (Option (Fin (r + 1 + 1) × Fin (r + 1 + 1))) A →ₐ[A]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Option (Fin r × Fin r)) A) :=
    aeval fun o => Option.elim o (C (X none)) fun w => Ψ (subY A r (X w))
  have hθn : θ (X none) = C (X none) := by
    simp [θ]
  have hθs : ∀ w, θ (X (some w)) = Ψ (subY A r (X w)) := fun w => by
    simp [θ]
  have h1 : Φ.comp (subY A r) = θ.comp (colAddGen A (midI r l) (midI r j)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp only [AlgHom.comp_apply, colAddGen_X]
    rcases midOf_cases t with ⟨j', rfl⟩ | ⟨hn, -⟩
    · rw [mAH_subY_mid]
      by_cases hj : j' = j
      · subst hj
        rw [if_pos rfl, map_add, map_mul, hθn, hθs, hθs, mAH_subY_mid, mAH_subY_mid, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [colAddGen_X, if_true, rename_X, map_add, map_mul]
        ring
      · rw [if_neg (fun h => hj ((midI_inj r j' j).mp h)), hθs, mAH_subY_mid]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [colAddGen_X, if_neg hj, rename_X]
    · rw [if_neg (midOf_none_ne hn j).symm, hθs, mAH_subY_none _ _ _ _ hn, mAH_subY_none _ _ _ _ hn]
  have h2 : Ψ.comp (subY A r) = θ.comp (rename some) := by
    apply MvPolynomial.algHom_ext
    intro w
    simp only [AlgHom.comp_apply, rename_X, hθs]
  have h3 : Φ (subY A r v) = Ψ (subY A r v) := by
    have e1 := congrArg (fun F => F v) h1
    have e2 := congrArg (fun F => F v) h2
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, e2, hv _ _ (midI_lt r hlj)]
  have h4 := congrArg (coeff u) h3
  simp only [Φ, Ψ, mAH_coeff] at h4
  exact h4

theorem subCoeffP : SubCoeffP := by
  intro A _ r ν v hv u
  rw [lsat_mem_dualWeyl] at hv ⊢
  exact ⟨subY_coefHom A r ν v hv.1 u, fun l j hlj => subY_inv A r v hv.2 l j hlj u⟩

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def th (K : Type) [Field K] (r : ℕ) (b : Bool) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  (mapAlgHom (blockEmb K (k := r) (n := r) b)).comp (subY K r)

theorem blockEmb_X (K : Type) [Field K] {k n : ℕ} (b : Bool) (x : Fin k × Fin n) :
    blockEmb K b (X x) = (X (b, x) : MvPolynomial (Bool × (Fin k × Fin n)) K) := by
  show rename _ (X x) = _
  rw [rename_X]

theorem th_C (K : Type) [Field K] (r : ℕ) (b : Bool) (a : K) : th K r b (C a) = C (C a) := by
  rw [th, AlgHom.comp_apply, subY_C, mAH_C, algHom_C, algebraMap_eq]

theorem th_X_mid (K : Type) [Field K] (r : ℕ) (b : Bool) (a : Fin (r + 1 + 1)) (j : Fin r) :
    th K r b (X (a, midI r j)) = ∑ i : Fin r, C (X (b, (i, j))) * X (a, midI r i) := by
  rw [th, AlgHom.comp_apply, mAH_subY_mid]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockEmb_X]

theorem th_X_none (K : Type) [Field K] (r : ℕ) (b : Bool) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    th K r b (X (a, t)) = X (a, t) := by
  rw [th, AlgHom.comp_apply, mAH_subY_none r _ a t h]

theorem th_coeff (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    coeff u (th K r b v) = blockEmb K b (coeff u (subY K r v)) := by
  rw [th, AlgHom.comp_apply, mAH_coeff]

theorem block_substitution_embedding (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = th K r b v := by
  have : (sub2 K r).comp (blockEmb K (k := r + 1 + 1) (n := r + 1 + 1) b) = th K r b := by
    apply algHom_ext
    intro w
    rw [AlgHom.comp_apply, blockEmb_X]
    unfold sub2
    rw [aeval_X]
    rfl
  exact AlgHom.congr_fun this v

theorem lam_eq (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    lamOf K r L (blockEmb K true v * blockEmb K false t) = lcoef L (th K r true v * th K r false t) := by
  unfold lamOf
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, block_substitution_embedding, block_substitution_embedding]

section Psi

variable {K B σ : Type} [Field K] [CommRing B] [Algebra K B]

def psiB (B : Type) [CommRing B] [Algebra K B] (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) :
    MvPolynomial σ B →+* MvPolynomial σ B :=
  eval₂Hom C (fun w => map (algebraMap K B) (ψ (X w)))

theorem psiB_C (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (b : B) : psiB B ψ (C b) = C b := by
  show eval₂ _ _ (C b) = _
  rw [eval₂_C]

theorem psiB_X (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (w : σ) :
    psiB B ψ (X w) = map (algebraMap K B) (ψ (X w)) := by
  show eval₂ _ _ (X w) = _
  rw [eval₂_X]

theorem psiB_map (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (G : MvPolynomial σ K) :
    psiB B ψ (map (algebraMap K B) G) = map (algebraMap K B) (ψ G) := by
  have : (psiB B ψ).comp (map (algebraMap K B)) = (map (algebraMap K B)).comp (ψ : MvPolynomial σ K →+* MvPolynomial σ K) := by
    apply ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_C, psiB_C, algHom_C, algebraMap_eq]
    · intro w
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_X, psiB_X]
  exact RingHom.congr_fun this G

theorem lcoef_C_mul_map (L : B →ₗ[K] K) (b : B) (G : MvPolynomial σ K) :
    lcoef L (C b * map (algebraMap K B) G) = L b • G := by
  ext u
  rw [coeff_lcoef, coeff_C_mul, coeff_map, coeff_smul, smul_eq_mul, mul_comm b, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]

theorem lcoef_comm (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (L : B →ₗ[K] K) (h : MvPolynomial σ B) :
    ψ (lcoef L h) = lcoef L (psiB B ψ h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial u b =>
    have e : (monomial u b : MvPolynomial σ B) = C b * map (algebraMap K B) (monomial u 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, lcoef_C_mul_map, map_mul, psiB_map, psiB_C, lcoef_C_mul_map, map_smul]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

theorem hom_eq_on {S : Type} [CommRing S] (f g : MvPolynomial σ K →+* S) (hC : ∀ a, f (C a) = g (C a))
    (hX : ∀ w, f (X w) = g (X w)) (v : MvPolynomial σ K) : f v = g v := by
  rw [ringHom_ext hC hX]

end Psi

theorem pow_exp_inj {K : Type} [Field K] [Infinite K] (a b : ℕ) (h : ∀ c : K, c ≠ 0 → c ^ a = c ^ b) : a = b := by
  have h1 : (Polynomial.X ^ (a + 1) : Polynomial K) = Polynomial.X ^ (b + 1) := by
    apply Polynomial.funext
    intro c
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    by_cases hc : c = 0
    · rw [hc, zero_pow (Nat.succ_ne_zero _), zero_pow (Nat.succ_ne_zero _)]
    · rw [pow_succ, pow_succ, h c hc]
  have h2 := congrArg Polynomial.natDegree h1
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at h2
  omega

section Scale

variable {K : Type} [Field K]

theorem sc_monomial {σ : Type} (d : σ → K) (u : σ →₀ ℕ) (a : K) :
    aeval (fun w => C (d w) * X w) (monomial u a) = monomial u (a * u.prod fun w e => d w ^ e) := by
  rw [aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (d v) : MvPolynomial σ K) ^ e) = C (u.prod fun v e => d v ^ e) := by
    rw [map_finsuppProd]; simp only [map_pow]
  rw [hC, monomial_eq, C_mul, algebraMap_eq]
  ring

theorem sc_coeff {σ : Type} (d : σ → K) (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (aeval (fun w => C (d w) * X w) f) = coeff m f * m.prod fun w e => d w ^ e := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [sc_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, add_mul]

def scCol (K : Type) [Field K] (k : ℕ) (t0 : Fin k) (c : K) :
    MvPolynomial (Fin k × Fin k) K →ₐ[K] MvPolynomial (Fin k × Fin k) K :=
  aeval (fun w => C (if w.2 = t0 then c else 1) * X w)

theorem scCol_X {k : ℕ} (t0 : Fin k) (c : K) (w : Fin k × Fin k) :
    scCol K k t0 c (X w) = C (if w.2 = t0 then c else 1) * X w := by
  unfold scCol
  rw [aeval_X]

theorem sc_prod {k : ℕ} (t0 : Fin k) (c : K) (m : Fin k × Fin k →₀ ℕ) :
    (m.prod fun w e => (if w.2 = t0 then c else 1) ^ e) = c ^ (Finsupp.weight (colW k k) m t0) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, lccomp_weight_colW_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_eq_single t0]
  · simp
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem scCol_coeff {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (m : Fin k × Fin k →₀ ℕ) :
    coeff m (scCol K k t0 c f) = coeff m f * c ^ (Finsupp.weight (colW k k) m t0) := by
  unfold scCol
  rw [sc_coeff, sc_prod]

theorem scCol_of_hom {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (ν : Fin k → ℕ)
    (hf : IsWeightedHomogeneous (colW k k) f ν) : scCol K k t0 c f = c ^ ν t0 • f := by
  ext m
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm]
  by_cases h : coeff m f = 0
  · rw [h, mul_zero, mul_zero]
  · rw [hf h]

theorem wt_of_scale [Infinite K] {k : ℕ} (t0 : Fin k) (n : ℕ) (f : MvPolynomial (Fin k × Fin k) K)
    (h : ∀ c : K, c ≠ 0 → scCol K k t0 c f = c ^ n • f) (m : Fin k × Fin k →₀ ℕ) (hm : coeff m f ≠ 0) :
    Finsupp.weight (colW k k) m t0 = n := by
  apply pow_exp_inj (K := K)
  intro c hc
  have := congrArg (coeff m) (h c hc)
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm] at this
  exact mul_right_cancel₀ hm this

theorem colAdd_trivial {k : ℕ} (l j : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K)
    (hf : ∀ m, coeff m f ≠ 0 → Finsupp.weight (colW k k) m j = 0) : colAdd K l j c f = f := by
  classical
  have e : colAdd K l j c f = ∑ m ∈ f.support, colAdd K l j c (monomial m (coeff m f)) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
  rw [e]
  conv_rhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  unfold colAdd
  rw [aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  apply Finsupp.prod_congr
  intro w hw
  have hwj : w.2 ≠ j := by
    intro h
    have h0 := hf m (mem_support_iff.1 hm)
    rw [lccomp_weight_colW_apply] at h0
    have h1 := Finset.sum_eq_zero_iff.1 h0 w.1 (Finset.mem_univ _)
    have e2 : w = (w.1, j) := Prod.ext rfl h
    apply Finsupp.mem_support_iff.1 hw
    rw [e2]
    exact h1
  rw [if_neg hwj]

end Scale

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end
