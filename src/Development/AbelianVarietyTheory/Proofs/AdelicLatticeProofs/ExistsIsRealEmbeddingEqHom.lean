import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfOddPrimeDegree
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugatesStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangeProperties

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_basis_one_sqrt_of_finrank_two {F E : Type} [Field F] [CharZero F] [Field E]
    [Algebra F E] (h : Module.finrank F E = 2) :
    ∃ (e : Module.Basis (Fin 2) F E) (δ : F), δ ≠ 0 ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap F E δ := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hr : 1 < Module.rank F E := by
    rw [← Module.finrank_eq_rank, h]; norm_num
  obtain ⟨s, hs⟩ := exists_linearIndependent_pair_of_one_lt_rank hr (one_ne_zero (α := E))
  let b := basisOfLinearIndependentOfCardEqFinrank hs (by simp [h])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = s := by simp [b]
  obtain ⟨p, q, hpq⟩ : ∃ p q : F, s * s = algebraMap F E p + algebraMap F E q * s := by
    refine ⟨b.repr (s * s) 0, b.repr (s * s) 1, ?_⟩
    conv_lhs => rw [← b.sum_repr (s * s), Fin.sum_univ_two, hb0, hb1, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  have ht : LinearIndependent F ![(1 : E), s - algebraMap F E (q / 2)] := by
    rw [LinearIndependent.pair_iff] at hs ⊢
    intro x y hxy
    have := hs (x - y * (q / 2)) y (by
      rw [← hxy]; simp only [Algebra.smul_def, map_sub, map_mul]; ring)
    obtain ⟨h1, rfl⟩ := this
    exact ⟨by simpa using h1, rfl⟩
  have hsq : (s - algebraMap F E (q / 2)) * (s - algebraMap F E (q / 2))
      = algebraMap F E (p + (q / 2) ^ 2) := by
    have hq : algebraMap F E q = 2 * algebraMap F E (q / 2) := by
      rw [← map_ofNat (algebraMap F E) 2, ← map_mul]; congr 1; ring
    rw [map_add, map_pow]
    rw [hq] at hpq
    linear_combination hpq
  refine ⟨basisOfLinearIndependentOfCardEqFinrank ht (by simp [h]), p + (q / 2) ^ 2, ?_,
    by simp, by simpa using hsq⟩
  intro h0
  rw [h0, map_zero, mul_self_eq_zero] at hsq
  exact ht.ne_zero 1 (by simpa using hsq)

theorem TNorm.exists_sq_sub {F E : Type} [Field F] [Field E] [Algebra F E]
    (e : Module.Basis (Fin 2) F E) (h0 : e 0 = 1) {δ : F} (h1 : e 1 * e 1 = algebraMap F E δ)
    (L : Type) [Field L] [Algebra F L] {x : F} (h : TNorm F E L x) :
    ∃ a b : L, algebraMap F L x = a ^ 2 - algebraMap F L δ * b ^ 2 := by
  obtain ⟨z, hz⟩ := h
  let e' := Algebra.TensorProduct.basis L e
  refine ⟨e'.repr z 0, e'.repr z 1, ?_⟩
  rw [← hz, ← GlobalTheory.Published.norm_of_basis_one_sqrt e'
    (by rw [Algebra.TensorProduct.basis_apply, h0]; rfl) (algebraMap F L δ)
    (by
      rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, h1,
        ← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.algebraMap_apply' δ).symm)]
  congr 1
  conv_lhs => rw [← e'.sum_repr z, Fin.sum_univ_two]

theorem np_of_finrank_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → NP F E := by
  intro F E _ _ _ _ _ h x hx hloc
  obtain ⟨e, δ, hδ, h0, h1⟩ := exists_basis_one_sqrt_of_finrank_two h
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt F δ x hδ hx
    (fun σ => @TNorm.exists_sq_sub F E _ _ _ e h0 δ h1 ℝ _ σ.toAlgebra x (hloc.2 σ.toAlgebra))
    (fun v => TNorm.exists_sq_sub e h0 h1 _ (hloc.1 v))
  exact ⟨_, (GlobalTheory.Published.norm_of_basis_one_sqrt e h0 δ h1 a b).trans hab.symm⟩

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.np_of_finrank_two' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → NP F E := by
  atlas_forward_decl GlobalTheory.CNorm.np_of_finrank_two
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem tensor_exists_of_galois_fixed :
    ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional M E] [IsGalois M E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), (∀ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K) ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) y = y) → ∃ z : K ⊗[F] M, Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z = y := by
  intro F M E K _ _ _ _ _ _ _ _ _ _ _ _ y hy
  classical
  have key : ∀ x : K ⊗[F] E, ∃ z : K ⊗[F] M,
      Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z =
      ∑ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K)
        ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul k e =>
      refine ⟨k ⊗ₜ Algebra.trace M E e, ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← TensorProduct.tmul_sum]
      congr 1
      exact trace_eq_sum_automorphisms e
    | add a b ha hb =>
      obtain ⟨za, ha⟩ := ha
      obtain ⟨zb, hb⟩ := hb
      refine ⟨za + zb, ?_⟩
      simp only [map_add, Finset.sum_add_distrib, ha, hb]
  obtain ⟨z, hz⟩ := key y
  simp only [hy, Finset.sum_const, Finset.card_univ] at hz
  have hm : ((Fintype.card (E ≃ₐ[M] E) : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨((Fintype.card (E ≃ₐ[M] E) : ℕ) : F)⁻¹ • z, ?_⟩
  rw [LinearMapClass.map_smul_of_tower, hz, ← Nat.cast_smul_eq_nsmul F, smul_smul,
    inv_mul_cancel₀ hm, one_smul]

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_eq_of_fixed_by_algEquiv : ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional M E] [IsGalois M E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), (∀ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K) ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) y = y) → ∃ z : K ⊗[F] M, Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z = y := by
  atlas_forward_decl GlobalTheory.CNorm.tensor_exists_of_galois_fixed
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isUnit_of_forall_maximal {K A : Type} [Field K] [Infinite K] [CommRing A]
    [Algebra K A] [IsArtinianRing A] (Θ : A →ₗ[K] A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ c, Θ c ∉ 𝔪) : ∃ c, IsUnit (Θ c) := by
  classical
  have hfin := IsArtinianRing.setOf_isMaximal_finite A
  let s : Finset (Subspace K A) :=
    hfin.toFinset.image fun 𝔪 => (𝔪.restrictScalars K).comap Θ
  have hs : ⊤ ∉ s := by
    intro ht
    obtain ⟨𝔪, hm, he⟩ := Finset.mem_image.1 ht
    obtain ⟨c, hc⟩ := h 𝔪 (by simpa using hm)
    have : c ∈ (𝔪.restrictScalars K).comap Θ := by rw [he]; trivial
    exact hc this
  have hne := Subspace.biUnion_ne_univ_of_top_notMem hs
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
  refine ⟨c, ?_⟩
  by_contra hu
  obtain ⟨𝔪, hm, hle⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
  apply hc
  simp only [Set.mem_iUnion]
  exact ⟨_, Finset.mem_image.2 ⟨𝔪, by simpa using hm, rfl⟩, hle⟩

theorem hilbert90_baseChange : ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] (τ : E ≃ₐ[F] E) (m : ℕ), orderOf τ = m → ∀ x : K ⊗[F] E, ∏ i ∈ Finset.range m, (Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E))^[i] x = 1 → ∃ z : (K ⊗[F] E)ˣ, x * Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) z = z := by
  intro F E K _ _ _ _ _ _ _ τ m hm x hx
  classical
  set T := Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) with hT
  have hm0 : 0 < m := hm ▸ orderOf_pos τ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : IsArtinianRing (K ⊗[F] E) := IsArtinianRing.of_finite K _
  have hpow : ∀ (i : ℕ) (y : K ⊗[F] E), T^[i] y = (T ^ i) y := fun i y => by
    rw [AlgHom.coe_pow]
  have htm : ∀ (i : ℕ) (k : K) (c : E), (T ^ i) (k ⊗ₜ c) = k ⊗ₜ ((τ ^ i) c) := by
    intro i k c
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, ih, AlgEquiv.mul_apply]; simp [hT]
  have hTm : ∀ y, (T ^ m) y = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k c => rw [htm, ← hm, pow_orderOf_eq_one]; rfl
    | add a b ha hb => rw [map_add, ha, hb]
  simp only [hpow] at hx
  let a : ℕ → K ⊗[F] E := fun i => ∏ j ∈ Finset.range i, (T ^ j) x
  have ha : ∀ i, x * T (a i) = a (i + 1) := by
    intro i
    simp only [a, map_prod, Finset.prod_range_succ', pow_zero, AlgHom.one_apply, pow_succ',
      AlgHom.mul_apply]
    ring
  have ha0 : a 0 = 1 := by simp [a]
  have ham : a m = 1 := hx
  let Θ : K ⊗[F] E →ₗ[K] K ⊗[F] E :=
    ∑ i ∈ Finset.range m, (LinearMap.mulLeft K (a i)).comp (T ^ i).toLinearMap
  have hΘ : ∀ c, Θ c = ∑ i ∈ Finset.range m, a i * (T ^ i) c := by
    intro c
    simp [Θ, LinearMap.sum_apply]
  have hfix : ∀ c, x * T (Θ c) = Θ c := by
    intro c
    have h1 : x * T (Θ c) = ∑ i ∈ Finset.range m, a (i + 1) * (T ^ (i + 1)) c := by
      rw [hΘ, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← mul_assoc, ha, pow_succ', AlgHom.mul_apply]
    have h2 := Finset.sum_range_succ' (fun i => a i * (T ^ i) c) m
    rw [Finset.sum_range_succ, ham, ha0, hTm, pow_zero, AlgHom.one_apply] at h2
    rw [h1, hΘ]
    exact (add_right_cancel h2).symm
  obtain ⟨c, hc⟩ := exists_isUnit_of_forall_maximal Θ (fun 𝔪 h𝔪 => by
    by_contra hcon
    push_neg at hcon
    letI : Field ((K ⊗[F] E) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    let ι : E →+* (K ⊗[F] E) ⧸ 𝔪 :=
      (Ideal.Quotient.mk 𝔪).comp Algebra.TensorProduct.includeRight.toRingHom
    let φ : Fin m → (E →* (K ⊗[F] E) ⧸ 𝔪) := fun i =>
      ι.toMonoidHom.comp ((τ ^ (i : ℕ) : E ≃ₐ[F] E) : E →* E)
    have hφ : Function.Injective φ := by
      intro i j hij
      have : τ ^ (i : ℕ) = τ ^ (j : ℕ) := by
        ext c
        exact ι.injective (DFunLike.congr_fun hij c)
      exact Fin.ext (pow_injOn_Iio_orderOf (by simp [hm]) (by simp [hm]) this)
    have hli := (linearIndependent_monoidHom E ((K ⊗[F] E) ⧸ 𝔪)).comp φ hφ
    have := Fintype.linearIndependent_iff.1 hli (fun i => Ideal.Quotient.mk 𝔪 (a i)) (by
      ext c
      have h := Ideal.Quotient.eq_zero_iff_mem.2 (hcon (1 ⊗ₜ c))
      rw [hΘ, map_sum, Finset.sum_range] at h
      simp only [htm, map_mul] at h
      rw [Finset.sum_apply]
      exact h) ⟨0, hm0⟩
    simp only [ha0, map_one] at this
    exact one_ne_zero this)
  exact ⟨hc.unit, hfix c⟩

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert90_baseChange' : ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] (τ : E ≃ₐ[F] E) (m : ℕ), orderOf τ = m → ∀ x : K ⊗[F] E, ∏ i ∈ Finset.range m, (Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E))^[i] x = 1 → ∃ z : (K ⊗[F] E)ˣ, x * Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) z = z := by
  atlas_forward_decl GlobalTheory.CNorm.hilbert90_baseChange
end

section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm.LocStep

theorem iter_prod {A ι : Type} [CommMonoid A] (T : A →* A) (n : ℕ) (s : Finset ι) (f : ι → A) :
    T^[n] (∏ i ∈ s, f i) = ∏ i ∈ s, T^[n] (f i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih, map_prod]

theorem prod_range_mul_iter {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x : A) :
    ∏ i ∈ Finset.range (d * m), T^[i] x
      = ∏ k ∈ Finset.range m, (T^[d])^[k] (∏ j ∈ Finset.range d, T^[j] x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, Finset.prod_range_succ, ← Function.iterate_mul,
      iter_prod]
    congr 1
    exact Finset.prod_congr rfl fun j _ => Function.iterate_add_apply _ _ _ _

theorem prod_cyc {G A : Type} [Group G] [Fintype G] [CommMonoid A] (σ : G)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (f : G → A) :
    ∏ g, f g = ∏ i ∈ Finset.range (Nat.card G), f (σ ^ i) := by
  classical
  have ho : orderOf σ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers h
  symm
  refine Finset.prod_bij (fun i _ => σ ^ i) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj hij
    rw [← ho] at hi hj
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  · intro g _
    have := (mem_zpowers_iff_mem_range_orderOf).1 (h g)
    rw [Finset.mem_image] at this
    obtain ⟨i, hi, e⟩ := this
    exact ⟨i, ho ▸ hi, e⟩

theorem telescope {A : Type} [CommMonoid A] (T : A →* A) (d : ℕ) (z : A) :
    (∏ j ∈ Finset.range d, T^[j] (T z)) * z = (∏ j ∈ Finset.range d, T^[j] z) * T^[d] z := by
  rw [← Finset.prod_range_succ, Finset.prod_range_succ']
  rfl

theorem core {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x a b : A) (hab : a * b = 1)
    (hb : T b = b) (ha : T a = a) (hx : ∏ i ∈ Finset.range (d * m), T^[i] x = a ^ m)
    (h90 : ∀ u : A, ∏ k ∈ Finset.range m, (T^[d])^[k] u = 1 → ∃ z : Aˣ, u * T^[d] z = z) :
    ∃ x' : A, T^[d] x' = x' ∧ ∏ j ∈ Finset.range d, T^[j] x' = a := by
  set P : A → A := fun u => ∏ j ∈ Finset.range d, T^[j] u with hP
  have Pmul : ∀ u v, P (u * v) = P u * P v := fun u v => by
    simp only [hP, iterate_map_mul, Finset.prod_mul_distrib]
  have Pone : P 1 = 1 := by simp only [hP, iterate_map_one, Finset.prod_const_one]
  have hbk : ∀ k, T^[k] b = b := fun k => Function.IsFixedPt.iterate hb k
  obtain ⟨z, hz⟩ := h90 (P x * b) (by
    rw [prod_range_mul_iter] at hx
    have : ∀ k, (T^[d])^[k] (P x * b) = (T^[d])^[k] (P x) * b := fun k => by
      rw [← Function.iterate_mul, iterate_map_mul, hbk]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hx, ← mul_pow, hab, one_pow])
  have hzz : P z * P (z⁻¹ : Aˣ) = 1 := by rw [← Pmul, Units.mul_inv, Pone]
  have ht : ∀ u, P (T u) * u = P u * T^[d] u := fun u => telescope T d u
  have h1 : P (x * T z * (z⁻¹ : Aˣ)) = a := by
    rw [← Units.mul_left_inj z, Pmul, Pmul]
    calc P x * P (T z) * P (z⁻¹ : Aˣ) * z = P x * (P (T z) * z) * P (z⁻¹ : Aˣ) := by ac_rfl
      _ = P x * T^[d] z * (P z * P (z⁻¹ : Aˣ)) * (a * b) := by rw [ht, hab, mul_one]; ac_rfl
      _ = a * (P x * b * T^[d] z) := by rw [hzz, mul_one]; ac_rfl
      _ = a * z := by rw [hz]
  refine ⟨_, ?_, h1⟩
  generalize x * T z * (z⁻¹ : Aˣ) = w at h1
  have h2 : P (T w) = a := by
    rw [← ha, ← h1]
    simp only [hP, map_prod]
    exact Finset.prod_congr rfl fun j _ => Function.iterate_succ_apply' _ _ _
  have h3 := ht w
  rw [h1, h2] at h3
  calc T^[d] w = b * (a * T^[d] w) := by rw [← mul_assoc, mul_comm b, hab, one_mul]
    _ = w := by rw [← h3, ← mul_assoc, mul_comm b, hab, one_mul]

theorem map_pow_iter {F E K : Type} [Field F] [Field E] [Algebra F E] [CommRing K] [Algebra F K]
    (σ : E ≃ₐ[F] E) (i : ℕ) (y : K ⊗[F] E) :
    Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ i : E ≃ₐ[F] E) : E →ₐ[F] E) y
      = (Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E))^[i] y := by
  induction i with
  | zero =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp
    | add u v hu hv => rw [map_add, hu, hv]; rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ← ih]
    clear ih
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp [pow_succ']
    | add u v hu hv => simp only [map_add, hu, hv]

theorem exists_pow_of_pow_eq_one {G : Type} [Group G] [Finite G] (σ : G) (d m : ℕ) (hm : m ≠ 0)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (ho : orderOf σ = d * m) (g : G) (hg : g ^ m = 1) :
    ∃ k : ℕ, g = σ ^ (d * k) := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (h g))
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ho] at hg
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hm) hg
  exact ⟨k, rfl⟩

end GlobalTheory.CNorm.LocStep

namespace GlobalTheory.CNorm
open LocStep

theorem tnorm_of_tnorm_pow : ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E] [IsGalois F E] [Field K] [Algebra F K], IsCyclic (E ≃ₐ[F] E) → ∀ a : F, a ≠ 0 → TNorm F E K (a ^ Module.finrank M E) → TNorm F M K a := by
  intro F M E K _ _ _ _ _ _ _ _ _ _ _ _ hc a ha ⟨x, hx⟩
  haveI : IsAbelianGalois F E := IsAbelianGalois.of_isCyclic F E
  haveI : IsGalois F M := (IsAbelianGalois.tower_bot F M E).toIsGalois
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  haveI : FiniteDimensional F M := FiniteDimensional.left F M E
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  set d := Module.finrank F M with hd
  set m := Module.finrank M E with hm
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hm0 : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Nat.card (E ≃ₐ[F] E) = d * m := by
    rw [IsGalois.card_aut_eq_finrank, Module.finrank_mul_finrank]
  have ho : orderOf σ = d * m := (orderOf_eq_card_of_forall_mem_zpowers hσ).trans hcard
  have hτ : orderOf (σ ^ d) = m := by
    rw [orderOf_pow_of_dvd hd0 (ho ▸ dvd_mul_right d m), ho,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  set S := Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E) with hS
  let T : K ⊗[F] E →* K ⊗[F] E := S
  have hT : (T : K ⊗[F] E → K ⊗[F] E) = S := rfl
  have hSd : (Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ d : E ≃ₐ[F] E) : E →ₐ[F] E) :
      K ⊗[F] E → K ⊗[F] E) = S^[d] := funext fun y => map_pow_iter σ d y
  have haK : algebraMap F K a ≠ 0 := (_root_.map_ne_zero _).2 ha
  obtain ⟨w, hw, hw'⟩ := core T d m x (algebraMap K _ (algebraMap F K a))
    (algebraMap K _ (algebraMap F K a)⁻¹) (by rw [← map_mul, mul_inv_cancel₀ haK, map_one])
    (S.commutes _) (S.commutes _)
    (by
      have := GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F E K x
      rw [hx, prod_cyc σ hσ, hcard, map_pow, map_pow] at this
      rw [this]
      exact Finset.prod_congr rfl fun i _ => (map_pow_iter σ i x).symm)
    (by
      intro u hu
      have := GlobalTheory.T.hilbert90_baseChange' F E K (σ ^ d) m hτ u (by rw [hSd]; exact hu)
      rw [hSd] at this
      exact this)
  obtain ⟨z, rfl⟩ := GlobalTheory.T.exists_tensor_eq_of_fixed_by_algEquiv F M E K w (by
    intro h
    obtain ⟨k, hk⟩ := exists_pow_of_pow_eq_one σ d m hm0 hσ ho (h.restrictScalars F) (by
      have h1 : h ^ m = 1 := by
        rw [hm, ← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
      have := map_pow (AlgEquiv.restrictScalarsHom F (S := M) (A := E)) h m
      rw [h1, map_one] at this
      exact this.symm)
    rw [hk, map_pow_iter, Function.iterate_mul]
    exact Function.IsFixedPt.iterate hw k)
  set ι := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) with hι
  have hinj : Function.Injective ι :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom F M E).toLinearMap (algebraMap M E).injective
  let σ' : M ≃ₐ[F] M := AlgEquiv.restrictNormalHom M σ
  have hσ' : ∀ g, g ∈ Subgroup.zpowers σ' := by
    intro g
    obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) E g
    obtain ⟨k, rfl⟩ := hσ g'
    exact ⟨k, (map_zpow _ _ _).symm⟩
  have hcomm : ∀ u : K ⊗[F] M,
      ι (Algebra.TensorProduct.map (AlgHom.id K K) (σ' : M →ₐ[F] M) u) = S (ι u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul k e =>
      have : algebraMap M E (σ' e) = σ (algebraMap M E e) :=
        AlgEquiv.restrictNormal_commutes σ M e
      simp [hι, hS, this]
    | add u v hu hv => simp only [map_add, hu, hv]
  refine ⟨z, ?_⟩
  apply (algebraMap K (K ⊗[F] M)).injective
  apply hinj
  rw [GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F M K z, prod_cyc σ' hσ', IsGalois.card_aut_eq_finrank, ι.commutes, ← hw',
    map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow_iter]
  exact Function.Semiconj.iterate_right hcomm i z

end GlobalTheory.CNorm
end

section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem bijective_mul_out_inv {H G : Type} [Group H] [Group G] (φ : H →* G)
    (hφ : Function.Injective φ) :
    Function.Bijective (fun p : H × (G ⧸ φ.range) => φ p.1 * (p.2.out)⁻¹) := by
  constructor
  · rintro ⟨h, q⟩ ⟨h', q'⟩ e
    simp only at e
    have hq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      refine ⟨h⁻¹ * h', ?_⟩
      rw [map_mul, map_inv]
      calc (φ h)⁻¹ * φ h' = (φ h)⁻¹ * (φ h' * (q'.out)⁻¹) * q'.out := by group
        _ = (φ h)⁻¹ * (φ h * (q.out)⁻¹) * q'.out := by rw [e]
        _ = _ := by group
    subst hq
    rw [hφ (mul_right_cancel e)]
  · intro g
    have : ((g⁻¹ : G) : G ⧸ φ.range).out⁻¹ * g⁻¹ ∈ φ.range := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    obtain ⟨h, hh⟩ := this
    refine ⟨(h⁻¹, ((g⁻¹ : G) : G ⧸ φ.range)), ?_⟩
    simp only [map_inv, hh]
    group

theorem TNorm.of_tower (F M E K : Type) [Field F] [Field M] [Field E] [Algebra F M] [Algebra M E]
    [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E] [IsGalois F E] [Field K]
    [Algebra F K] [Algebra M K] [IsScalarTower F M K] (x : F) (hx : TNorm F E K x) :
    TNorm M E K (algebraMap F M x) := by
  classical
  obtain ⟨y, hy⟩ := hx
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  let π : K ⊗[F] E →ₐ[K] K ⊗[M] E := Algebra.TensorProduct.mapOfCompatibleSMul M F K K E
  let φ : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E) :=
    { toFun := fun h => h.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := AlgEquiv.restrictScalars_injective F
  haveI : Fintype ((E ≃ₐ[F] E) ⧸ φ.range) := Fintype.ofFinite _
  have key : ∀ (h : E ≃ₐ[M] E) (g : E ≃ₐ[F] E) (z : K ⊗[F] E),
      Algebra.TensorProduct.map (AlgHom.id K K) (h : E →ₐ[M] E)
        (π (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) z)) =
      π (Algebra.TensorProduct.map (AlgHom.id K K) ((φ h * g : E ≃ₐ[F] E) : E →ₐ[F] E) z) := by
    intro h g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨π (∏ q : (E ≃ₐ[F] E) ⧸ φ.range,
    Algebra.TensorProduct.map (AlgHom.id K K) (((q.out)⁻¹ : E ≃ₐ[F] E) : E →ₐ[F] E) y), ?_⟩
  apply (algebraMap K (K ⊗[M] E)).injective
  rw [GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates M E K, ← IsScalarTower.algebraMap_apply F M K x, ← hy, ← π.commutes,
    GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F E K, map_prod π, map_prod π,
    ← (bijective_mul_out_inv φ hφ).prod_comp (fun g : E ≃ₐ[F] E =>
      π (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y)), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun q _ => key h _ y

end GlobalTheory.CNorm
end

section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNormFromBaseChange_base_change_properties : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E], (∀ (K K' : Type) [Field K] [Algebra F K] [Field K'] [Algebra F K'] (_ : K →ₐ[F] K') (x : F), TNorm F E K x → TNorm F E K' x) ∧ (∀ (K : Type) [Field K] [Algebra F K] (e : E), TNorm F E K (Algebra.norm F e)) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x y : F), y ≠ 0 → TNorm F E K (x * y) → TNorm F E K y → TNorm F E K x := by
  first | exact @GlobalTheory.CNorm.tnorm_baseChange | exact GlobalTheory.CNorm.tnorm_baseChange | (intros; apply GlobalTheory.CNorm.tnorm_baseChange <;> assumption)
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem prod_univ_eq_prod_range_orderOf_of_generator {G β : Type} [Group G] [Fintype G] [CommMonoid β]
    {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (f : G → β) :
    ∏ σ, f σ = ∏ i ∈ Finset.range (orderOf g), f (g ^ i) := by
  classical
  rw [← IsCyclic.image_range_orderOf hg, Finset.prod_image]
  intro i hi j hj hij
  exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem prod_range_pow_pow_prod_range_eq_prod_range_mul {F E : Type} [Field F] [Field E] [Algebra F E]
    (τ : E ≃ₐ[F] E) (y : E) (d n : ℕ) :
    ∏ j ∈ Finset.range n, ((τ ^ d) ^ j) (∏ i ∈ Finset.range d, (τ ^ i) y) =
      ∏ m ∈ Finset.range (d * n), (τ ^ m) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.mul_succ, Finset.prod_range_add, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← AlgEquiv.mul_apply, ← pow_mul, ← pow_add]

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem exists_eq_pow_finrank_mul_norm_of_norm_eq_cyclic (F M E : Type) [Field F] [Field M] [Field E]
    [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E]
    [IsGalois F E] (hcyc : IsCyclic (E ≃ₐ[F] E)) (x : F) (hx : x ≠ 0) (e₀ : E)
    (he₀ : Algebra.norm M e₀ = algebraMap F M x) :
    ∃ b : F, ∃ c : E, c ≠ 0 ∧ x = b ^ Module.finrank M E * Algebra.norm F c := by
  classical
  haveI : FiniteDimensional M E := FiniteDimensional.right F M E
  haveI : FiniteDimensional F M := FiniteDimensional.left F M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  set n := Module.finrank M E with hn
  set d := Module.finrank F M with hd
  have hdn : d * n = Module.finrank F E := Module.finrank_mul_finrank F M E
  have hn0 : 0 < n := Module.finrank_pos
  have hd0 : 0 < d := Module.finrank_pos
  obtain ⟨τ, hτ⟩ := hcyc.exists_generator
  have hcomm : ∀ a b : E ≃ₐ[F] E, a * b = b * a := by
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ b)
    exact ((Commute.refl τ).zpow_zpow i j).eq
  let ρ : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E) :=
    { toFun := fun h => h.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hρ : Function.Injective ρ := AlgEquiv.restrictScalars_injective F
  have hρapp : ∀ (h : E ≃ₐ[M] E) (y : E), ρ h y = h y := fun _ _ => rfl
  let K := ρ.range
  haveI : K.Normal := ⟨fun a _ g => by rwa [hcomm g a, mul_inv_cancel_right]⟩
  have hcardK : Nat.card K = n := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv, IsGalois.card_aut_eq_finrank]
  have hcardG : Nat.card (E ≃ₐ[F] E) = d * n := by rw [IsGalois.card_aut_eq_finrank, hdn]
  have hindex : K.index = d := by
    have h := K.index_mul_card
    rw [hcardK, hcardG] at h
    exact Nat.eq_of_mul_eq_mul_right hn0 h
  have hτd : τ ^ d ∈ K := hindex ▸ K.pow_index_mem τ
  obtain ⟨g, hg⟩ := hτd
  have hordτ : orderOf τ = d * n := by rw [orderOf_eq_card_of_forall_mem_zpowers hτ, hcardG]
  have hordτd : orderOf (τ ^ d) = n := by
    rw [orderOf_pow' τ hd0.ne', hordτ, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ hd0]
  have hKz : Subgroup.zpowers (τ ^ d) = K := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le, ← hg]
      exact ⟨g, rfl⟩
    · rw [hcardK, Nat.card_zpowers, hordτd]
  have hgen : ∀ h : E ≃ₐ[M] E, h ∈ Subgroup.zpowers g := by
    intro h
    have hmem : ρ h ∈ Subgroup.zpowers (τ ^ d) := hKz ▸ ⟨h, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, hρ ?_⟩
    rw [map_zpow, hg, hk]
  haveI : IsCyclic (E ≃ₐ[M] E) := ⟨⟨g, hgen⟩⟩
  have hordg : orderOf g = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

  have hnormτ : ∀ y : E, algebraMap M E (Algebra.norm M (τ y)) =
      τ (algebraMap M E (Algebra.norm M y)) := by
    intro y
    rw [Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms, map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [← hρapp σ, ← hρapp σ, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, hcomm]
  have he₀0 : e₀ ≠ 0 := by
    rintro rfl
    exact hx ((algebraMap F M).injective (by rw [← he₀, Algebra.norm_zero, map_zero]))
  have hxE : algebraMap M E (Algebra.norm M e₀) = algebraMap F E x := by
    rw [he₀, ← IsScalarTower.algebraMap_apply]
  have hN0 : Algebra.norm M e₀ ≠ 0 := by rw [he₀]; exact (_root_.map_ne_zero _).mpr hx
  have hu : Algebra.norm M (τ e₀ / e₀) = 1 := by
    have h1 : Algebra.norm M (τ e₀ / e₀) * Algebra.norm M e₀ = Algebra.norm M (τ e₀) := by
      rw [← map_mul, div_mul_cancel₀ _ he₀0]
    have h2 : algebraMap M E (Algebra.norm M (τ e₀)) = algebraMap M E (Algebra.norm M e₀) := by
      rw [hnormτ, hxE, AlgEquiv.commutes]
    rw [(algebraMap M E).injective h2] at h1
    exact mul_right_cancel₀ hN0 (h1.trans (one_mul _).symm)
  obtain ⟨c, hc⟩ := groupCohomology.exists_div_of_norm_eq_one hgen hu
  have hgc : g (c : E) = (τ ^ d) (c : E) := by rw [← hρapp, hg]
  have hc0 : (c : E) ≠ 0 := c.ne_zero
  have hτdc0 : (τ ^ d) (c : E) ≠ 0 := by
    rw [← hgc]; exact (_root_.map_ne_zero _).mpr hc0
  set P := ∏ i ∈ Finset.range d, (τ ^ i) (c : E) with hPdef
  have hτP : τ P * c = P * (τ ^ d) (c : E) := by
    have hs : τ P = ∏ i ∈ Finset.range d, (τ ^ (i + 1)) (c : E) := by
      rw [hPdef, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    rw [hs]
    have h := Finset.prod_range_succ' (fun i => (τ ^ i) (c : E)) d
    rw [Finset.prod_range_succ] at h
    simp only [pow_zero, AlgEquiv.one_apply] at h
    exact h.symm
  have hτe₀ : τ e₀ * (τ ^ d) (c : E) = e₀ * c := by
    rw [← hgc]
    have h := hc
    rw [div_eq_div_iff ((_root_.map_ne_zero _).mpr hc0) he₀0] at h
    linear_combination -h
  have hfix : τ (e₀ * P) = e₀ * P := by
    rw [map_mul]
    apply mul_right_cancel₀ (mul_ne_zero hτdc0 hc0)
    linear_combination (τ P * c) * hτe₀ + (e₀ * c) * hτP
  obtain ⟨b, hb⟩ : ∃ b : F, algebraMap F E b = e₀ * P := by
    have hall : ∀ σ : E ≃ₐ[F] E, σ (e₀ * P) = e₀ * P := by
      intro σ
      have hst : τ ∈ MulAction.stabilizer (E ≃ₐ[F] E) (e₀ * P) := hfix
      exact (Subgroup.zpowers_le.mpr hst) (hτ σ)
    exact IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hall)
  have hnormP : algebraMap M E (Algebra.norm M P) =
      algebraMap M E (algebraMap F M (Algebra.norm F (c : E))) := by
    rw [Algebra.norm_eq_prod_automorphisms, prod_univ_eq_prod_range_orderOf_of_generator hgen, hordg,
      ← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_automorphisms,
      prod_univ_eq_prod_range_orderOf_of_generator hτ, hordτ, ← prod_range_pow_pow_prod_range_eq_prod_range_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hρapp, map_pow, hg]
  have hbn : algebraMap F M (b ^ n) = algebraMap F M (x * Algebra.norm F (c : E)) := by
    have h := congrArg (Algebra.norm M) hb
    rw [IsScalarTower.algebraMap_apply F M E, Algebra.norm_algebraMap, map_mul, he₀,
      (algebraMap M E).injective hnormP] at h
    rw [map_pow, map_mul, h]
  have hNc : Algebra.norm F (c : E) ≠ 0 := (c.isUnit.map (Algebra.norm F)).ne_zero
  refine ⟨b, ((c⁻¹ : Eˣ) : E), Units.ne_zero _, ?_⟩
  rw [map_units_inv (Algebra.norm F) c, (algebraMap F M).injective hbn, mul_inv_cancel_right₀ hNc]

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in

theorem _root_.GlobalTheory.CNorm.np_of_cyclic_tower : ∀ (F M E : Type) [Field F] [NumberField F] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E]
    [IsGalois F E], IsCyclic (E ≃ₐ[F] E) → _root_.GlobalTheory.CNorm.NP M E → _root_.GlobalTheory.CNorm.NP F M → _root_.GlobalTheory.CNorm.NP F E := by
  intro F M E _ _ _ _ _ _ _ _ _ _ _ hcyc hME hMF x hx0 hloc
  haveI : FiniteDimensional F E := inferInstance
  haveI : FiniteDimensional F M := inferInstance
  haveI : FiniteDimensional M E := inferInstance
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have hprops := _root_.GlobalTheory.CNorm.tnorm_baseChange F E
  have hxM : algebraMap F M x ≠ 0 := (_root_.map_ne_zero _).mpr hx0
  have h1 : _root_.GlobalTheory.CNorm.LocNorm M E (algebraMap F M x) := by
    refine ⟨fun w => ?_, fun a => ?_⟩
    · obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F M w
      letI : Algebra F (w.adicCompletion M) :=
        ((algebraMap M (w.adicCompletion M)).comp (algebraMap F M)).toAlgebra
      haveI : IsScalarTower F M (w.adicCompletion M) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      let ψ : (HeightOneSpectrum.under (𝓞 F) w).adicCompletion F →ₐ[F] w.adicCompletion M :=
        { φ with commutes' := fun r => (hφ r).trans rfl }
      exact _root_.GlobalTheory.CNorm.TNorm.of_tower F M E _ x
        (hprops.1 _ _ ψ x (hloc.1 _))
    · letI : Algebra F ℝ := ((algebraMap M ℝ).comp (algebraMap F M)).toAlgebra
      haveI : IsScalarTower F M ℝ := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact _root_.GlobalTheory.CNorm.TNorm.of_tower F M E ℝ x (hloc.2 _)
  obtain ⟨e₀, he₀⟩ := hME _ hxM h1
  obtain ⟨b, c, hc0, hxb⟩ := exists_eq_pow_finrank_mul_norm_of_norm_eq_cyclic F M E hcyc x hx0 e₀ he₀
  have hNc : Algebra.norm F c ≠ 0 := by
    intro h
    exact hx0 (by rw [hxb, h, mul_zero])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hxb, zero_pow Module.finrank_pos.ne', zero_mul])
  have hpow : ∀ (K : Type) [Field K] [Algebra F K], _root_.GlobalTheory.CNorm.TNorm F E K x →
      _root_.GlobalTheory.CNorm.TNorm F M K b := by
    intro K _ _ hK
    refine _root_.GlobalTheory.CNorm.tnorm_of_tnorm_pow F M E K hcyc b hb0 ?_
    exact hprops.2.2 K _ _ hNc (hxb ▸ hK) (hprops.2.1 K c)
  obtain ⟨m, hm⟩ := hMF b hb0 ⟨fun v => hpow _ (hloc.1 v), fun a => hpow ℝ (hloc.2 a)⟩
  refine ⟨algebraMap M E m * c, ?_⟩
  rw [map_mul, hxb, ← Algebra.norm_norm (S := M), Algebra.norm_algebraMap, map_pow, hm]

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasseNormPrinciple_of_cyclic_tower : ∀ (F M E : Type) [Field F] [NumberField F] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [IsGalois F E], IsCyclic (E ≃ₐ[F] E) → NP M E → NP F M → NP F E := by
  atlas_forward_decl GlobalTheory.CNorm.np_of_cyclic_tower
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem np_of_finrank_one (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 1) : NP F E := by
  intro x _ _
  refine ⟨algebraMap F E x, ?_⟩
  rw [Algebra.norm_algebraMap, h, pow_one]

theorem np_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E] (hp : p.Prime) (h : Module.finrank F E = p) :
    NP F E := by
  by_cases h2 : p = 2
  · exact GlobalTheory.T.np_of_finrank_two' F E (h2 ▸ h)
  · exact GlobalTheory.T.np_of_odd_prime_degree' p F E hp h2 h

theorem hasseNormPrinciple_cyclic_of_finrank (n : ℕ) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = n → IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F E _ _ _ _ _ hn hG hC
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  by_cases h1 : n = 1
  · exact np_of_finrank_one F E (hn.trans h1)
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = n := (IsGalois.card_aut_eq_finrank F E).trans hn
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := E ≃ₐ[F] E) p (hcard ▸ hpn)
  set H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers g with hH
  have hHc : Nat.card H = p := by rw [hH, Nat.card_zpowers, hg]
  have : H.Normal := by
    constructor
    intro a ha b
    have hc : b * a = a * b := by
      obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
      obtain ⟨i, rfl⟩ := hs a
      obtain ⟨j, rfl⟩ := hs b
      exact (Commute.zpow_zpow_self s j i).eq
    rw [hc, mul_inv_cancel_right]
    exact ha
  let M : IntermediateField F E := IntermediateField.fixedField H
  have : NumberField M := NumberField.of_module_finite F M
  have hME : Module.finrank M E = p :=
    (IntermediateField.finrank_fixedField_eq_card H).trans hHc
  have : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have hFM : IsGalois F M := IsGalois.of_fixedField_normal_subgroup H
  have hCM : IsCyclic (M ≃ₐ[F] M) :=
    isCyclic_of_surjective (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) M)
      (AlgEquiv.restrictNormalHom_surjective E)
  have hmul : Module.finrank F M * Module.finrank M E = n :=
    (Module.finrank_mul_finrank F M E).trans hn
  have hpos : 0 < Module.finrank F M := Module.finrank_pos
  have hlt : Module.finrank F M < n := by
    rw [← hmul, hME]
    exact lt_mul_of_one_lt_right hpos hp.one_lt
  exact GlobalTheory.T.hasseNormPrinciple_of_cyclic_tower F M E hC (np_of_finrank_prime p M E hp hME) (ih _ hlt F M rfl hFM hCM)

theorem np_cyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E :=
  fun F E _ _ _ _ _ hG hC => hasseNormPrinciple_cyclic_of_finrank _ F E rfl hG hC

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasseNormPrinciple_of_isCyclic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsGalois F E → IsCyclic (E ≃ₐ[F] E) → NP F E := by
  atlas_forward_decl GlobalTheory.CNorm.np_cyclic
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isReal_embedding_eq_hom {F : Type} [Field F] (σ : F →+* ℝ) :
    ∃ (v : InfinitePlace F) (hv : v.IsReal), InfinitePlace.embedding_of_isReal hv = σ := by
  have hr : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hv : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hr, rfl⟩
  refine ⟨_, hv, ?_⟩
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hr]
  rfl

theorem hasseNorm : GlobalTheory.Published.HasseNorm := by
  intro K L _ _ _ _ _ hG hC a ha hf hi
  refine GlobalTheory.T.hasseNormPrinciple_of_isCyclic K L hG hC a ha ⟨hf, fun alg => ?_⟩
  obtain ⟨v, hv, hσ⟩ := exists_isReal_embedding_eq_hom (algebraMap K ℝ)
  let φ : v.Completion →ₐ[K] ℝ :=
    { InfinitePlace.Completion.extensionEmbeddingOfIsReal hv with
      commutes' := fun x => by
        rw [← hσ]
        exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm x) }
  exact (GlobalTheory.T.isNormFromBaseChange_base_change_properties K L).1 v.Completion ℝ φ a (hi v)

end GlobalTheory.CNorm
end
