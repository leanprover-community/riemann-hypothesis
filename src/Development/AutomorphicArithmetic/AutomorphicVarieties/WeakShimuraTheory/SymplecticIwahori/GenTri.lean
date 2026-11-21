import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.GramCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Ideal.GoingUp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem UpperTheory.V.Ws.Pp.gf_adj_mul {R : Type} [CommRing R] (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev] <;> ring

private theorem UpperTheory.V.Ws.Pp.gf_adj_one {R : Type} [CommRing R] : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

private theorem UpperTheory.V.Ws.Pp.gf_conj {R : Type} [CommRing R] {ν : R} {X : M4 R} (h : IsGSp ν X) (u v : M4 R)
    (hv : v * u = 1) : adj (u * X * v) * (adj v * v) * (u * X * v) = ν • (adj v * v) := by
  have h1 : adj u * adj v = 1 := by
    rw [← gf_adj_mul, hv, gf_adj_one]
  unfold IsGSp at h
  rw [gf_adj_mul, gf_adj_mul]
  calc _ = adj v * (adj X * (adj u * adj v) * (v * u) * X) * v := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, hv, Matrix.mul_one, Matrix.mul_one, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

private theorem UpperTheory.V.Ws.Pp.gf_gram {K : Type} [Field K] {ν : K} {M A : M4 K} (hM : ∀ i j, j < i → M i j = 0)
    (h : adj M * A * M = ν • A)
    (hc : ∀ i j : Fin 4, j < i → M i.rev i.rev * M j j ≠ ν) : ∀ i j, j < i → A i j = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  have m10 := hM 1 0 (by decide)
  have m20 := hM 2 0 (by decide)
  have m30 := hM 3 0 (by decide)
  have m21 := hM 2 1 (by decide)
  have m31 := hM 3 1 (by decide)
  have m32 := hM 3 2 (by decide)
  have k : ∀ {a b x : K}, a ≠ b → a * x = b * x → x = 0 := fun hab hx => by
    by_contra h0
    exact hab (mul_right_cancel₀ h0 hx)
  have e30 := e 3 0
  have e20 := e 2 0
  have e10 := e 1 0
  have e31 := e 3 1
  have e21 := e 2 1
  have e32 := e 3 2
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, m10, m20, m30, m21, m31, m32] at e30 e20 e10 e31 e21 e32
  have a30 : A 3 0 = 0 := k (hc 3 0 (by decide)) (by show M 0 0 * M 0 0 * _ = _; linear_combination e30)
  rw [a30] at e20 e10 e31 e21 e32
  have a20 : A 2 0 = 0 := k (hc 2 0 (by decide)) (by show M 1 1 * M 0 0 * _ = _; linear_combination e20)
  have a31 : A 3 1 = 0 := k (hc 3 1 (by decide)) (by show M 0 0 * M 1 1 * _ = _; linear_combination e31)
  simp only [a20, a31] at e10 e21 e32
  have a10 : A 1 0 = 0 := k (hc 1 0 (by decide)) (by show M 2 2 * M 0 0 * _ = _; linear_combination e10)
  have a21 : A 2 1 = 0 := k (hc 2 1 (by decide)) (by show M 1 1 * M 1 1 * _ = _; linear_combination e21)
  have a32 : A 3 2 = 0 := k (hc 3 2 (by decide)) (by show M 0 0 * M 2 2 * _ = _; linear_combination e32)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

theorem UpperTheory.V.Ws.Pp.genFlag :
    ∀ {H K : Type} [Group H] [Field K] (I : Subgroup H) (ps : Fin 4 → H → K) (s₀ : H) (ν : K) (r : H →* M4 K), s₀ ∈ I → Function.Injective (fun i => ps i s₀) → (∀ i, ps i s₀ * ps i.rev s₀ = ν) → ν ≠ 0 → IsGSp ν (r s₀) → Ord I ps s₀ r → ∃ h : M4 K, IsGSp 1 h ∧ (∀ g, IsUp (adj h * r g * h)) ∧ (∀ s ∈ I, ∀ i, (adj h * r s * h) i i = ps i s) ∧ ∀ i g, (∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)) * (adj h * r g * h) i i = (prj (fun a => ps a s₀) (r s₀) i * r g).trace := by
  intro H K _ _ I ps s₀ ν r hs hinj hrev hν hg ho
  obtain ⟨u, κ, h1, h2, h3, h4⟩ := ordFlag I K ps s₀ r hinj ho
  have hA := gf_gram (h1 s₀) (gf_conj hg _ _ u.inv_mul) fun i j hij e => by
    rw [h2, h2, h3 _ _ hs, h3 _ _ hs, ← hrev i, mul_comm (ps i s₀)] at e
    have h0 : ps i.rev s₀ ≠ 0 := fun h => hν (by rw [← hrev i, h, mul_zero])
    exact hij.ne (hinj (mul_left_cancel₀ h0 e))
  obtain ⟨t, ht, hh⟩ := gram u⁻¹ hA
  have hadj : adj (((u⁻¹ : (M4 K)ˣ) : M4 K) * (t : M4 K)) = ((t⁻¹ : (M4 K)ˣ) : M4 K) * (u : M4 K) := by
    have e := adj_mul_self hh
    rw [← mul_assoc, Units.mul_eq_one_iff_eq_inv, Units.mul_inv_eq_iff_eq_mul] at e
    exact e
  have key : ∀ g, adj (((u⁻¹ : (M4 K)ˣ) : M4 K) * (t : M4 K)) * r g * (((u⁻¹ : (M4 K)ˣ) : M4 K) * (t : M4 K))
      = ((t⁻¹ : (M4 K)ˣ) : M4 K) * ((u : M4 K) * r g * ((u⁻¹ : (M4 K)ˣ) : M4 K)) * (t : M4 K) := fun g => by
    rw [hadj]
    simp only [mul_assoc]
  have up := fun g => upConj t.inv_mul (IsUp_inv ht) ht (h1 g)
  refine ⟨_, hh, fun g => ?_, fun s hs i => ?_, fun i g => ?_⟩
  · rw [key]
    exact (up g).1
  · rw [key, (up s).2, h2, h3 i s hs]
  · rw [key, (up g).2, h2, h4]
end

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.nilPoly :
    ∀ {B S : Type} [CommRing B] [IsLocalRing B] [CommRing S] [IsLocalRing S] [Algebra B S] [Module.Finite B S] (v : S), v ∈ maximalIdeal S → ∃ p : B[X], Dist (maximalIdeal B) p ∧ aeval v p = 0 := by
  intro B S _ _ _ _ _ _ v hv
  have hrad : v ∈ ((maximalIdeal B).map (algebraMap B S)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro J hJ'
    obtain ⟨hJ, hJp⟩ := hJ'
    have hle : maximalIdeal B ≤ Ideal.comap (algebraMap B S) J := by
      intro b hb
      exact hJ (Ideal.mem_map_of_mem _ hb)
    have hc : Ideal.comap (algebraMap B S) J = maximalIdeal B :=
      ((IsLocalRing.maximalIdeal.isMaximal B).eq_of_le (Ideal.comap_ne_top _ hJp.ne_top) hle).symm
    have hcm : (Ideal.comap (algebraMap B S) J).IsMaximal := by
      rw [hc]
      exact IsLocalRing.maximalIdeal.isMaximal B
    have hJm : J.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap J hcm
    rw [IsLocalRing.eq_maximalIdeal hJm]
    exact hv
  obtain ⟨n, hn⟩ := hrad
  have hN : v ^ (n + 1) ∈ (maximalIdeal B).map (algebraMap B S) := by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ hn
  have hrange : LinearMap.range (Algebra.lmul B S (v ^ (n + 1))) ≤
      (maximalIdeal B) • (⊤ : Submodule B S) := by
    rintro _ ⟨s, rfl⟩
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    simpa using Ideal.mul_mem_right s _ hN
  obtain ⟨p, hpm, -, hpc, hpa⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (R := B) (M := S) (Algebra.lmul B S (v ^ (n + 1))) (maximalIdeal B) hrange
  refine ⟨expand B (n + 1) p, ⟨hpm.expand (Nat.succ_pos n), ?_⟩, ?_⟩
  · intro k hk
    rw [natDegree_expand] at hk
    rw [coeff_expand (Nat.succ_pos n)]
    split_ifs with hd
    · have hlt : k / (n + 1) < p.natDegree := by
        rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos n)]
        exact hk
      exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hlt) (hpc _)
    · exact zero_mem _
  · rw [expand_aeval]
    rw [Polynomial.aeval_algHom_apply] at hpa
    have h1 := LinearMap.congr_fun hpa 1
    simpa using h1
end

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem nearPoly_local (B S : Type) [CommRing B] [HenselianLocalRing B] [CommRing S] [IsDomain S]
    [Algebra B S] [Module.Finite B S] : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian B q
  refine .of_unique_max_ideal ⟨q, hq, fun n hn => (H n hn).1 ?_⟩
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 he with h | h
  · exact absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)
  · rw [h]
    exact (Ideal.ne_top_iff_one _).1 hn.ne_top

theorem UpperTheory.V.Ws.Pp.nearPoly :
    ∀ {O B : Type} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [HenselianLocalRing B] [Algebra O B] (x : B →ₐ[O] O) (d : O) (t : B) (v : FractionRing B), d ≠ 0 → x t = 0 → IsIntegral B v → algebraMap B (FractionRing B) (algebraMap O B d) * v = algebraMap B (FractionRing B) t → ∃ p : B[X], Dist (maximalIdeal B) p ∧ aeval v p = 0 := by
  intro O B _ _ _ _ _ _ x d t v hd ht hv h
  let S := Algebra.adjoin B ({v} : Set (FractionRing B))
  haveI : Module.Finite B S := Module.Finite.iff_fg.2 hv.fg_adjoin_singleton
  haveI : IsLocalRing S := nearPoly_local B S
  let w : S := ⟨v, Algebra.self_mem_adjoin_singleton B v⟩
  have hw : w ∈ maximalIdeal S := by
    intro hu
    obtain ⟨u, hu⟩ := hu.exists_right_inv
    have h1 : algebraMap B S (algebraMap O B d) * w = algebraMap B S t := Subtype.ext h
    have h2 : algebraMap B S (algebraMap O B d) = algebraMap B S t * u := by
      rw [← h1, mul_assoc, hu, mul_one]
    haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
    have hinj : Function.Injective (algebraMap B S) := fun a b e =>
      IsFractionRing.injective B (FractionRing B) (congrArg Subtype.val e)
    obtain ⟨Q, _, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S) (RingHom.ker x)
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
    have h3 : t ∈ Q.comap (algebraMap B S) := by rw [hQ]; exact ht
    have h4 : algebraMap O B d ∈ Q.comap (algebraMap B S) := by
      rw [Ideal.mem_comap, h2]
      exact Q.mul_mem_right _ h3
    rw [hQ, RingHom.mem_ker, x.commutes] at h4
    exact hd h4
  obtain ⟨p, hp, h0⟩ := nilPoly (B := B) w hw
  refine ⟨p, hp, ?_⟩
  have := aeval_algHom_apply S.val w p
  rw [h0, map_zero] at this
  exact this
end

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

section Gen

variable {R K H : Type} [CommRing R] [CommRing K] [Group H] (f : R →+* K)

private theorem gt_rep (r : H →* M4 R) (g : H) : mapRep f r g = f.mapMatrix (r g) := rfl

private theorem gt_smul (a : R) (Y : M4 R) : f.mapMatrix (a • Y) = f a • f.mapMatrix Y := by
  ext i j
  simp

private theorem gt_adj (Y : M4 R) : adj (f.mapMatrix Y) = f.mapMatrix (adj Y) := by
  ext i j
  simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul]

private theorem gt_gsp {ν : R} {Y : M4 R} (h : IsGSp ν Y) : IsGSp (f ν) (f.mapMatrix Y) := by
  unfold IsGSp at *
  rw [gt_adj, ← map_mul, h, gt_smul, map_one]

private theorem gt_prj (c : Fin 4 → R) (Y : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix Y) i = f.mapMatrix (prj c Y i) := by
  unfold prj
  have h : ∀ p : R[X], aeval (f.mapMatrix Y) (p.map f) = f.mapMatrix (aeval Y p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, map_add, hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, map_mul, map_pow,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, gt_smul, map_one]
  rw [← h, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem gt_ord {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H} {r : H →* M4 R} (h : Ord I ps s₀ r) :
    Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) where
  charpoly := by
    rw [gt_rep, RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  stable g i j hij := by
    rw [gt_rep, gt_rep, gt_prj f (fun a => ps a s₀), gt_prj f (fun a => ps a s₀), ← map_mul, ← map_mul,
      h.stable g i j hij, map_zero]
  inert s hs i := by
    rw [gt_rep, gt_rep, gt_prj f (fun a => ps a s₀), ← map_one f.mapMatrix, ← gt_smul, ← map_sub, ← map_mul,
      ← map_mul, h.inert s hs i, map_zero]

private theorem gt_tr (c : Fin 4 → R) (Y Z : M4 R) (i : Fin 4) :
    (prj (fun a => f (c a)) (f.mapMatrix Y) i * f.mapMatrix Z).trace = f (prj c Y i * Z).trace := by
  rw [gt_prj, ← map_mul, RingHom.mapMatrix_apply, AddMonoidHom.map_trace]

private theorem gt_tr_diag (c a : Fin 4 → R) (i : Fin 4) :
    (prj c (Matrix.diagonal c) i * Matrix.diagonal a).trace = (∏ j ∈ Finset.univ.erase i, (c i - c j)) * a i := by
  have h : prj c (Matrix.diagonal c) i = Matrix.diagonal fun b => ∏ j ∈ Finset.univ.erase i, (c b - c j) := by
    unfold prj
    have h1 := aeval_algHom_apply (Matrix.diagonalAlgHom (n := Fin 4) (α := R) R) c
      (∏ j ∈ Finset.univ.erase i, (X - C (c j)))
    rw [Matrix.diagonalAlgHom_apply, Matrix.diagonalAlgHom_apply] at h1
    rw [h1]
    congr 1
    funext b
    simp [map_prod]
  rw [h, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Finset.sum_eq_single i]
  · intro b _ hb
    rw [Finset.prod_eq_zero (i := b) (by simp [hb]) (sub_self _), zero_mul]
  · simp

end Gen

private theorem gt_int {B K : Type} [CommRing B] [Field K] [Algebra B K] (Y : M4 B) {a b : M4 K} (hab : a * b = 1)
    (hM : IsUp (a * (algebraMap B K).mapMatrix Y * b)) (i : Fin 4) :
    IsIntegral B ((a * (algebraMap B K).mapMatrix Y * b) i i) := by
  refine ⟨Y.charpoly, Y.charpoly_monic, ?_⟩
  have e : (a * (algebraMap B K).mapMatrix Y * b).charpoly = ((algebraMap B K).mapMatrix Y).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, mul_eq_one_comm.1 hab, Matrix.one_mul]
  rw [eval₂_eq_eval_map, ← Matrix.charpoly_map, ← RingHom.mapMatrix_apply, ← e,
    Matrix.charpoly_of_upperTriangular _ (fun i j h => hM i j h), eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem UpperTheory.V.Ws.Pp.genTri :
    ∀ {O B H : Type} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [HenselianLocalRing B] [Algebra O B] [Group H] (I : Subgroup H) (ps : Fin 4 → H → O) (s₀ : H) (ν : O) (ρ : H →* M4 B) (x : B →ₐ[O] O), s₀ ∈ I → Function.Injective (fun i => ps i s₀) → (∀ i, ps i s₀ * ps i.rev s₀ = ν) → ν ≠ 0 → IsGSp (algebraMap O B ν) (ρ s₀) → Ord I (fun i g => algebraMap O B (ps i g)) s₀ ρ → (∀ g a b, x (ρ g a b) = Matrix.diagonal (fun i => ps i g) a b) → ∃ (h : M4 (FractionRing B)) (P : H → Fin 4 → B[X]), SpTri (fun g => ρ g) P (algebraMap B (FractionRing B)) h ∧ (∀ g i, ∃ q, Dist (maximalIdeal B) q ∧ P g i = q.comp (X - C (algebraMap O B (ps i g)))) ∧ ∀ s ∈ I, ∀ i, P s i = X - C (algebraMap O B (ps i s)) := by
  intro O B H _ _ _ _ _ _ _ I ps s₀ ν ρ x hs hinj hrev hν hG hρ hx
  have hB : Function.Injective (algebraMap O B) := fun a b e => by simpa using congrArg x e
  have hF := IsFractionRing.injective B (FractionRing B)
  obtain ⟨h, h1, h2, h3, h4⟩ := genFlag I (fun i g => algebraMap B (FractionRing B) (algebraMap O B (ps i g))) s₀
    (algebraMap B (FractionRing B) (algebraMap O B ν)) (mapRep (algebraMap B (FractionRing B)) ρ) hs
    (fun a b e => hinj (hB (hF e))) (fun i => by rw [← map_mul, ← map_mul, hrev])
    ((map_ne_zero_iff _ hF).2 ((map_ne_zero_iff _ hB).2 hν)) (gt_gsp _ hG) (gt_ord _ hρ)
  have key : ∀ g i, ∃ q : B[X], Dist (maximalIdeal B) q ∧
      aeval ((adj h * mapRep (algebraMap B (FractionRing B)) ρ g * h) i i -
        algebraMap B (FractionRing B) (algebraMap O B (ps i g))) q = 0 ∧ (g ∈ I → q = X) := by
    intro g i
    by_cases hg : g ∈ I
    · refine ⟨X, ⟨monic_X, fun n hn => ?_⟩, by rw [h3 g hg, sub_self, aeval_X], fun _ => rfl⟩
      rw [natDegree_X, Nat.lt_one_iff] at hn
      rw [hn, coeff_X_zero]
      exact zero_mem _
    let d : O := ∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)
    let t : B := (prj (fun a => algebraMap O B (ps a s₀)) (ρ s₀) i * ρ g).trace
    have hd : d ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 fun e => (Finset.mem_erase.1 hj).1 (hinj e).symm
    have hxt : x t = d * ps i g := by
      have e1 := gt_tr (x : B →+* O) (fun a => algebraMap O B (ps a s₀)) (ρ s₀) (ρ g) i
      have e2 : ∀ g, (x : B →+* O).mapMatrix (ρ g) = Matrix.diagonal fun i => ps i g := fun g => Matrix.ext (hx g)
      simp only [e2, RingHom.coe_coe, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at e1
      rw [gt_tr_diag] at e1
      exact e1.symm
    have hint : IsIntegral B ((adj h * mapRep (algebraMap B (FractionRing B)) ρ g * h) i i) :=
      gt_int (ρ g) (adj_mul_self h1) (h2 g) i
    have hk : algebraMap B (FractionRing B) (algebraMap O B d) *
        (adj h * mapRep (algebraMap B (FractionRing B)) ρ g * h) i i = algebraMap B _ t := by
      rw [← gt_tr (algebraMap B (FractionRing B)), map_prod, map_prod]
      simp only [map_sub]
      exact h4 i g
    obtain ⟨q, hq, h0⟩ := nearPoly x d (t - algebraMap O B (d * ps i g))
      ((adj h * mapRep (algebraMap B (FractionRing B)) ρ g * h) i i - algebraMap B _ (algebraMap O B (ps i g))) hd
      (by rw [map_sub, hxt, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
      (hint.sub isIntegral_algebraMap) (by rw [mul_sub, hk, map_sub, map_mul, map_mul])
    exact ⟨q, hq, h0, fun e => absurd e hg⟩
  choose q hq h0 hI using key
  refine ⟨h, fun g i => (q g i).comp (X - C (algebraMap O B (ps i g))), ⟨h1, fun g => ⟨h2 g, fun i => ?_⟩⟩,
    fun g i => ⟨_, hq g i, rfl⟩, fun s hs i => by simp only [hI s i hs, X_comp]⟩
  rw [← aeval_def, aeval_comp, map_sub, aeval_X, aeval_C]
  exact h0 g i
end
