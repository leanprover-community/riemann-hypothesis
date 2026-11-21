import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SinvOfSwt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.MatDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SmoothCompositionIdentity.MatOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.Weights

section
noncomputable section

open Matrix

namespace PositivityTheory.KB.BlockInvariants

namespace WeightOneEmbedding

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Ω × Ω) :=
  (Matrix.ofLinearEquiv ℂ).symm ≪≫ₗ (LinearEquiv.curry ℂ ℂ Ω Ω).symm ≪≫ₗ
    (WithLp.linearEquiv 2 ℂ (Ω × Ω → ℂ)).symm

theorem inner_embE (x y : Matrix Ω Ω ℂ) :
    inner ℂ (embE x) (embE y) = trace (xᴴ * y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [embE, LinearEquiv.trans_apply, dotProduct, trace, diag, mul_apply, conjTranspose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem comm_left (A : Submodule ℂ (Matrix Ω Ω ℂ)) (T : Matrix Ω Ω ℂ)
    (hT : ∀ Z : Matrix Ω Ω ℂ, (∀ a ∈ A, Z * a = a * Z) → T * Z = Z * T)
    (S : Matrix Ω Ω ℂ →ₗ[ℂ] Matrix Ω Ω ℂ) (hS : ∀ a ∈ A, ∀ y, S (a * y) = a * S y)
    (y : Matrix Ω Ω ℂ) : S (T * y) = T * S y := by
  have key : ∀ (a : Matrix Ω Ω ℂ) (c j : Ω), a * single c j 1 = ∑ b, a b c • single b j 1 := by
    intro a c j
    ext x z
    simp only [mul_apply, Matrix.sum_apply, Matrix.smul_apply, single, of_apply, smul_eq_mul]
    by_cases h : j = z <;> simp [h, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  let Z : Ω → Ω → Matrix Ω Ω ℂ := fun j k => Matrix.of fun x c => S (single c j 1) x k
  have hZr : ∀ (a : Matrix Ω Ω ℂ) (j k x c : Ω), (Z j k * a) x c = S (a * single c j 1) x k := by
    intro a j k x c
    rw [key, map_sum, Matrix.sum_apply]
    simp only [Z, mul_apply, of_apply, map_smul, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hZl : ∀ (a : Matrix Ω Ω ℂ) (j k x c : Ω), (a * Z j k) x c = (a * S (single c j 1)) x k := by
    intro a j k x c
    simp only [Z, mul_apply, of_apply]
  have hZ : ∀ j k, T * Z j k = Z j k * T := fun j k => hT _ fun a ha => by
    ext x c; rw [hZr, hZl, hS a ha]
  have hsingle : ∀ c j, S (T * single c j 1) = T * S (single c j 1) := by
    intro c j
    ext x k
    rw [← hZr, ← hZl, hZ]
  rw [matrix_eq_sum_single y]
  simp only [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  have : single c j (y c j) = y c j • single c j (1 : ℂ) := by
    rw [smul_single, smul_eq_mul, mul_one]
  rw [this, mul_smul_comm, map_smul, hsingle, map_smul, mul_smul_comm]

theorem bic (A : Submodule ℂ (Matrix Ω Ω ℂ)) (h1 : (1 : Matrix Ω Ω ℂ) ∈ A)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hstar : ∀ a ∈ A, aᴴ ∈ A) (T : Matrix Ω Ω ℂ)
    (hT : ∀ Z : Matrix Ω Ω ℂ, (∀ a ∈ A, Z * a = a * Z) → T * Z = Z * T) : T ∈ A := by
  let K : Submodule ℂ (EuclideanSpace ℂ (Ω × Ω)) := A.map (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).toLinearMap
  let P : Matrix Ω Ω ℂ →ₗ[ℂ] Matrix Ω Ω ℂ :=
    (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ K.starProjection.toLinearMap ∘ₗ
      (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).toLinearMap
  have hPe : ∀ y, embE (P y) = K.starProjection (embE y) := fun y => by
    simp [P]
  have P1 : ∀ y, P y ∈ A := by
    intro y
    obtain ⟨a, ha, e⟩ := Submodule.mem_map.1 (K.starProjection_apply_mem (embE y))
    have : P y = a := by
      apply (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).injective
      rw [hPe]; exact e.symm
    rw [this]; exact ha
  have P2 : ∀ a ∈ A, P a = a := by
    intro a ha
    apply (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).injective
    rw [hPe]
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.mem_map_of_mem ha)
  have P3 : ∀ a ∈ A, ∀ y, P (a * y) = a * P y := by
    intro a ha y
    apply (embE : Matrix Ω Ω ℂ ≃ₗ[ℂ] _).injective
    rw [hPe]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact Submodule.mem_map_of_mem (hmul a ha _ (P1 y))
    · intro w hw
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hw
      have h0 := Submodule.starProjection_inner_eq_zero (K := K) (embE y)
        (embE (aᴴ * b)) (Submodule.mem_map_of_mem (hmul _ (hstar a ha) b hb))
      rw [← hPe, ← map_sub, inner_embE] at h0
      change inner ℂ (embE (a * y) - embE (a * P y)) (embE b) = 0
      rw [← map_sub, inner_embE, ← mul_sub, conjTranspose_mul, Matrix.mul_assoc]
      exact h0
  have := comm_left A T hT P P3 1
  rw [P2 1 h1, Matrix.mul_one] at this
  rw [← this]
  exact P1 T

end WeightOneEmbedding

open WeightOneEmbedding

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

theorem perm'_mul (σ τ : Equiv.Perm (Fin q)) (w v : Fin q → W) :
    (perm' (m := m) σ w) * perm' τ v = if v = w ∘ σ then perm' (σ * τ) w else 0 := by
  ext I K
  rw [mul_apply, Finset.sum_eq_single (I ∘ σ)]
  · simp only [perm', of_apply, Equiv.Perm.coe_mul]
    by_cases hv : v = w ∘ σ
    · subst hv
      rw [if_pos rfl, of_apply]
      by_cases hI : ∀ i, (I i).1 = w i
      · simp [hI, Function.comp_assoc]
      · simp [hI]
    · rw [if_neg hv, Matrix.zero_apply]
      by_cases hI : ∀ i, (I i).1 = w i
      · have : ¬ ∀ i, ((I ∘ σ) i).1 = v i := fun h => hv (funext fun i => by
          rw [← h i]; exact hI (σ i))
        simp only [this, false_and, if_false, mul_zero]
      · simp [hI]
  · intro J _ hJ
    simp only [perm', of_apply]
    rw [if_neg (fun h => hJ h.2), zero_mul]
  · simp

theorem perm'_star (σ : Equiv.Perm (Fin q)) (w : Fin q → W) :
    (perm' (m := m) σ w)ᴴ = perm' σ⁻¹ (w ∘ σ) := by
  ext I J
  simp only [perm', conjTranspose_apply, of_apply]
  have e : (∀ i, (J i).1 = w i) ∧ I = J ∘ σ ↔ (∀ i, (I i).1 = (w ∘ σ) i) ∧ J = I ∘ ⇑(σ⁻¹) := by
    constructor
    · rintro ⟨h1, rfl⟩
      refine ⟨fun i => h1 (σ i), ?_⟩
      funext i; simp
    · rintro ⟨h1, rfl⟩
      refine ⟨fun i => ?_, ?_⟩
      · have := h1 (σ⁻¹ i); simpa using this
      · funext i; simp
  by_cases h : (∀ i, (J i).1 = w i) ∧ I = J ∘ σ
  · rw [if_pos h, if_pos (e.1 h), star_one]
  · rw [if_neg h, if_neg (fun h' => h (e.2 h')), star_zero]

theorem one_eq_sum_perm' : (1 : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) = ∑ w, perm' 1 w := by
  ext I J
  rw [Matrix.sum_apply, Finset.sum_eq_single (fun i => (I i).1)]
  · simp only [perm', of_apply, Equiv.Perm.coe_one, Function.comp_id, one_apply]
    by_cases h : I = J
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro w _ hw
    simp only [perm', of_apply]
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hw (funext fun i => (h i).symm)
  · simp

theorem sw1 : PlacePermOperatorBicommutantSpan := by
  intro W _ _ m q T hT
  set S := Set.range fun p : Equiv.Perm (Fin q) × (Fin q → W) => (perm' (m := m) p.1 p.2)
  have hgen : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span ℂ S := by
    rintro _ ⟨⟨σ, w⟩, rfl⟩ _ ⟨⟨τ, v⟩, rfl⟩
    dsimp only
    rw [perm'_mul]
    split_ifs
    · exact Submodule.subset_span ⟨(σ * τ, w), rfl⟩
    · exact Submodule.zero_mem _
  refine bic (Submodule.span ℂ S) ?_ ?_ ?_ T ?_
  · rw [one_eq_sum_perm']
    exact Submodule.sum_mem _ fun w _ => Submodule.subset_span ⟨(1, w), rfl⟩
  · intro a ha b hb
    have := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at this
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hgen x hx y hy
  · intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨σ, w⟩, rfl⟩ := hx
      dsimp only
      rw [perm'_star]
      exact Submodule.subset_span ⟨(σ⁻¹, w ∘ σ), rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [conjTranspose_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [conjTranspose_smul]; exact Submodule.smul_mem _ _ hx
  · intro Z hZ
    exact hT Z fun σ w => hZ _ (Submodule.subset_span ⟨(σ, w), rfl⟩)

end PositivityTheory.KB.BlockInvariants

end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.KB.BlockInvariants

namespace WeightTwoPolynomials

section Poly

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

def mt (x : Fin q → Matrix ι ι ℂ) : Matrix (Fin q → ι) (Fin q → ι) ℂ :=
  Matrix.of fun I J => ∏ i, x i (I i) (J i)

theorem tp_sum {K : Type} [Fintype K] [DecidableEq K] (M : K → Matrix ι ι ℂ) (c : K → ℂ) :
    tp q (∑ k, c k • M k) = ∑ f : Fin q → K, (∏ j, c (f j)) • mt (fun j => M (f j)) := by
  ext I J
  simp only [tp, mt, of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]

open MvPolynomial in

def polyOf {K : Type} [Fintype K] (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ)
    (M : K → Matrix ι ι ℂ) : MvPolynomial K ℂ :=
  ∑ f : Fin q → K, C (φ (mt fun j => M (f j))) * ∏ j, X (f j)

open MvPolynomial in
theorem eval_polyOf {K : Type} [Fintype K] [DecidableEq K]
    (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (M : K → Matrix ι ι ℂ) (c : K → ℂ) :
    eval c (polyOf φ M) = φ (tp q (∑ k, c k • M k)) := by
  rw [tp_sum, map_sum, polyOf, map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, eval_C, map_prod]
  simp only [eval_X]
  ring

open MvPolynomial in
theorem totalDegree_polyOf {K : Type} [Fintype K]
    (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (M : K → Matrix ι ι ℂ) :
    (polyOf φ M).totalDegree ≤ q := by
  unfold polyOf
  refine totalDegree_finsetSum_le fun f _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  simp [totalDegree_X]

theorem grid {K : Type} [Fintype K] [DecidableEq K]
    (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (M : K → Matrix ι ι ℂ) (S : K → Finset ℂ)
    (hS : ∀ k, q < (S k).card) (h0 : ∀ c : K → ℂ, (∀ k, c k ∈ S k) → φ (tp q (∑ k, c k • M k)) = 0)
    (c : K → ℂ) : φ (tp q (∑ k, c k • M k)) = 0 := by
  have hP : polyOf φ M = 0 := MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ S
    (fun k => lt_of_le_of_lt ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
      (totalDegree_polyOf φ M)) (hS k))
    (fun x hx => by rw [eval_polyOf]; exact h0 x hx)
  rw [← eval_polyOf, hP, map_zero]

end Poly

section GlobalTheory

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

theorem blk_apply (d : W → Matrix (Fin m) (Fin m) ℂ) (x y : Ix W m) :
    blk d x y = if x.1 = y.1 then d x.1 x.2 y.2 else 0 := rfl

theorem blk_add (d e : W → Matrix (Fin m) (Fin m) ℂ) : blk (d + e) = blk d + blk e := by
  ext x y; simp only [blk_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem blk_smul (a : ℂ) (d : W → Matrix (Fin m) (Fin m) ℂ) : blk (a • d) = a • blk d := by
  ext x y; simp only [blk_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem blk_sum {K : Type} (s : Finset K) (d : K → W → Matrix (Fin m) (Fin m) ℂ) :
    blk (∑ k ∈ s, d k) = ∑ k ∈ s, blk (d k) := by
  ext x y; simp only [blk_apply, Matrix.sum_apply, Finset.sum_apply]; split_ifs <;> simp

theorem eq_blk (M : Matrix (Ix W m) (Ix W m) ℂ) (hM : ∀ x y : Ix W m, x.1 ≠ y.1 → M x y = 0) :
    M = blk (fun w a b => M (w, a) (w, b)) := by
  ext x y
  change M x y = if x.1 = y.1 then M (x.1, x.2) (x.1, y.2) else 0
  split_ifs with h
  · obtain ⟨w, a⟩ := x; obtain ⟨w', b⟩ := y
    simp only at h; subst h; rfl
  · exact hM x y h

theorem herm_of_unit (φ : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ →ₗ[ℂ] ℂ)
    (hU : ∀ d : W → Matrix (Fin m) (Fin m) ℂ, (∀ w, d w ∈ unitaryGroup (Fin m) ℂ) → φ (tp q (blk d)) = 0)
    (d : W → Matrix (Fin m) (Fin m) ℂ) (hd : ∀ w, (d w).IsHermitian) : φ (tp q (blk d)) = 0 := by
  set v : W → Matrix (Fin m) (Fin m) ℂ := fun w => ((hd w).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have hv : ∀ w, v w ∈ unitaryGroup (Fin m) ℂ := fun w => ((hd w).eigenvectorUnitary).2
  let M : Ix W m → Matrix (Ix W m) (Ix W m) ℂ := fun k =>
    blk fun w => if w = k.1 then v w * diagonal (Pi.single k.2 1) * star (v w) else 0
  have hsum : ∀ c : Ix W m → ℂ, ∑ k, c k • M k =
      blk fun w => v w * diagonal (fun a => c (w, a)) * star (v w) := by
    intro c
    simp_rw [M, ← blk_smul, ← blk_sum]
    congr 1
    funext w
    rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single w]
    · simp only [Pi.smul_apply, if_true]
      have hd1 : ∑ x : Fin m, c (w, x) • diagonal (Pi.single x (1 : ℂ)) = diagonal fun a => c (w, a) := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
        split_ifs with h
        · subst h; simp [Pi.single_apply]
        · simp
      rw [← hd1, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
    · intro w' _ hw'
      simp [Ne.symm hw']
    · simp
  have hcirc : ∀ c : Ix W m → ℂ, (∀ k, ‖c k‖ = 1) → φ (tp q (∑ k, c k • M k)) = 0 := by
    intro c hc
    rw [hsum]
    refine hU _ fun w => ?_
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (hv w) ?_) (Unitary.star_mem (hv w))
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [Complex.star_def, Complex.mul_conj', hc (w, a)]
    simp
  have hq : 0 < q + 1 := Nat.succ_pos q
  have hζ := Complex.isPrimitiveRoot_exp (q + 1) (Nat.succ_ne_zero q)
  have hall := grid φ M (fun _ => Polynomial.nthRootsFinset (q + 1) (1 : ℂ))
    (fun _ => by rw [hζ.card_nthRootsFinset]; omega)
    (fun c hc => hcirc c fun k => Complex.norm_eq_one_of_pow_eq_one
      ((Polynomial.mem_nthRootsFinset hq (1 : ℂ)).1 (hc k)) (Nat.succ_ne_zero q))
  have := hall fun k => ((hd k.1).eigenvalues k.2 : ℂ)
  rw [hsum] at this
  have e : d = fun w => v w * diagonal (fun a => ((hd w).eigenvalues a : ℂ)) * star (v w) := by
    funext w
    conv_lhs => rw [(hd w).spectral_theorem]
    rfl
  rw [e]
  exact this

theorem all_of_herm (φ : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ →ₗ[ℂ] ℂ)
    (hH : ∀ d : W → Matrix (Fin m) (Fin m) ℂ, (∀ w, (d w).IsHermitian) → φ (tp q (blk d)) = 0)
    (d : W → Matrix (Fin m) (Fin m) ℂ) : φ (tp q (blk d)) = 0 := by
  set H : W → Matrix (Fin m) (Fin m) ℂ := fun w => (2 : ℂ)⁻¹ • (d w + (d w)ᴴ)
  set K : W → Matrix (Fin m) (Fin m) ℂ := fun w => ((2 : ℂ)⁻¹ * -Complex.I) • (d w - (d w)ᴴ)
  let M : Fin 2 → Matrix (Ix W m) (Ix W m) ℂ := ![blk H, blk K]
  have hM : ∀ c : Fin 2 → ℂ, ∑ k, c k • M k = blk (c 0 • H + c 1 • K) := by
    intro c
    simp [M, Fin.sum_univ_two, blk_add, blk_smul]
  have hall := grid φ M (fun _ => (Finset.range (q + 1)).image (Nat.cast : ℕ → ℂ))
    (fun _ => by rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]; omega)
    (fun c hc => by
      rw [hM]
      refine hH _ fun w => ?_
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hc 0)
      obtain ⟨b, -, hb⟩ := Finset.mem_image.1 (hc 1)
      rw [← ha, ← hb]
      simp only [IsHermitian, Pi.add_apply, Pi.smul_apply, H, K, conjTranspose_add,
        conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      simp only [star_natCast, star_mul', star_inv₀, star_ofNat, star_neg, Complex.star_def,
        Complex.conj_I]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring)
  have := hall ![1, Complex.I]
  rw [hM] at this
  have e : d = (![1, Complex.I] : Fin 2 → ℂ) 0 • H + (![1, Complex.I] : Fin 2 → ℂ) 1 • K := by
    funext w
    ext i j
    simp only [Pi.add_apply, Pi.smul_apply, H, K, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination (2 : ℂ)⁻¹ * (d w i j - (d w)ᴴ i j) * Complex.I_sq
  rw [e]
  exact this

end GlobalTheory

section Comm

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

theorem perm'_apply (σ : Equiv.Perm (Fin q)) (w : Fin q → W) (I J : Fin q → Ix W m) :
    perm' σ w I J = if (∀ i, (I i).1 = w i) ∧ J = I ∘ σ then 1 else 0 := rfl

theorem mul_perm' (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) (σ : Equiv.Perm (Fin q))
    (w : Fin q → W) (A B : Fin q → Ix W m) :
    (Z * perm' σ w : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) A B =
      if (∀ i, ((B ∘ σ.symm) i).1 = w i) then Z A (B ∘ σ.symm) else 0 := by
  have hB : (B ∘ σ.symm) ∘ σ = B := by funext i; simp
  rw [mul_apply, Finset.sum_eq_single (B ∘ σ.symm)]
  · rw [perm'_apply]
    split_ifs with h1 h2 h2
    · rw [mul_one]
    · exact absurd h1.1 h2
    · exact absurd ⟨h2, hB.symm⟩ h1
    · rw [mul_zero]
  · intro K _ hK
    rw [perm'_apply, if_neg, mul_zero]
    rintro ⟨-, rfl⟩
    exact hK (by funext i; simp)
  · simp

theorem perm'_mul (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) (σ : Equiv.Perm (Fin q))
    (w : Fin q → W) (A B : Fin q → Ix W m) :
    (perm' σ w * Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) A B =
      if (∀ i, (A i).1 = w i) then Z (A ∘ σ) B else 0 := by
  rw [mul_apply, Finset.sum_eq_single (A ∘ σ)]
  · rw [perm'_apply]
    split_ifs with h1 h2 h2
    · rw [one_mul]
    · exact absurd h1.1 h2
    · exact absurd ⟨h2, rfl⟩ h1
    · rw [zero_mul]
  · intro K _ hK
    rw [perm'_apply, if_neg, zero_mul]
    rintro ⟨-, rfl⟩
    exact hK rfl
  · simp

theorem compat_of_comm (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ)
    (hZ : ∀ (σ : Equiv.Perm (Fin q)) (w : Fin q → W), Z * perm' σ w = perm' σ w * Z)
    (I J : Fin q → Ix W m) (h : Z I J ≠ 0) : ∀ i, (I i).1 = (J i).1 := by
  have := congrFun (congrFun (hZ 1 fun i => (J i).1) I) J
  rw [mul_perm', perm'_mul] at this
  have e1 : J ∘ (1 : Equiv.Perm (Fin q)).symm = J := by funext i; rfl
  rw [e1] at this
  rw [if_pos (fun _ => rfl)] at this
  by_contra hne
  rw [if_neg hne] at this
  exact h this

theorem sym_of_comm (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ)
    (hZ : ∀ (σ : Equiv.Perm (Fin q)) (w : Fin q → W), Z * perm' σ w = perm' σ w * Z)
    (σ : Equiv.Perm (Fin q)) (I J : Fin q → Ix W m) : Z (I ∘ σ) (J ∘ σ) = Z I J := by
  have := congrFun (congrFun (hZ σ fun i => (I i).1) I) (J ∘ σ)
  rw [mul_perm', perm'_mul] at this
  have hJ : (J ∘ σ) ∘ σ.symm = J := by funext i; simp
  rw [hJ] at this
  rw [if_pos (fun _ => rfl)] at this
  rw [← this]
  by_cases h : Z I J = 0
  · rw [h]; split_ifs <;> rfl
  · rw [if_pos fun i => (compat_of_comm Z hZ I J h i).symm]

end Comm

section Sym

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

def symU (I J : Fin q → ι) : Matrix (Fin q → ι) (Fin q → ι) ℂ :=
  ∑ σ : Equiv.Perm (Fin q), Matrix.single (I ∘ σ) (J ∘ σ) 1

theorem decomp (Z : Matrix (Fin q → ι) (Fin q → ι) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin q)) I J, Z (I ∘ σ) (J ∘ σ) = Z I J) :
    ((Nat.factorial q : ℕ) : ℂ) • Z = ∑ I, ∑ J, Z I J • symU I J := by
  have key : ∀ (σ : Equiv.Perm (Fin q)) (K L : Fin q → ι),
      ∑ I, ∑ J, Z I J * Matrix.single (I ∘ σ) (J ∘ σ) (1 : ℂ) K L = Z K L := by
    intro σ K L
    rw [Finset.sum_eq_single (K ∘ σ.symm)]
    · rw [Finset.sum_eq_single (L ∘ σ.symm)]
      · have h1 : (K ∘ σ.symm) ∘ σ = K := by funext i; simp
        have h2 : (L ∘ σ.symm) ∘ σ = L := by funext i; simp
        rw [h1, h2, Matrix.single_apply_same, mul_one, hsym]
      · intro J _ hJ
        rw [Matrix.single_apply, if_neg, mul_zero]
        rintro ⟨-, h⟩
        exact hJ (by rw [← h]; funext i; simp)
      · simp
    · intro I _ hI
      refine Finset.sum_eq_zero fun J _ => ?_
      rw [Matrix.single_apply, if_neg, mul_zero]
      rintro ⟨h, -⟩
      exact hI (by rw [← h]; funext i; simp)
    · simp
  ext K L
  simp only [Matrix.smul_apply, Matrix.sum_apply, symU, smul_eq_mul, Finset.mul_sum]
  conv_rhs => enter [2, I]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem nu_iff (f : Fin q → Fin q) :
    (∑ j, Finsupp.single (f j) 1 : Fin q →₀ ℕ) = ∑ j, Finsupp.single j 1 ↔ Function.Bijective f := by
  constructor
  · intro h
    have hs : Function.Surjective f := by
      intro k
      by_contra hk
      push_neg at hk
      have := congrArg (fun g : Fin q →₀ ℕ => g k) h
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply] at this
      simp [hk] at this
    exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩
  · intro h
    exact Fintype.sum_bijective f h _ _ fun _ => rfl

theorem sum_perm_mt (x : Fin q → Matrix ι ι ℂ) (I J : Fin q → ι)
    (hx : ∀ j, x j = Matrix.single (I j) (J j) 1) :
    ∑ σ : Equiv.Perm (Fin q), mt (fun j => x (σ j)) = symU I J := by
  refine Finset.sum_congr rfl fun σ _ => ?_
  ext K L
  simp only [mt, of_apply, hx, Matrix.single_apply]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩
  · rintro ⟨h1, h2⟩ i
    exact ⟨congrFun h1 i, congrFun h2 i⟩

open MvPolynomial in

theorem sym_zero (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (x : Fin q → Matrix ι ι ℂ)
    (h0 : ∀ t : Fin q → ℂ, φ (tp q (∑ j, t j • x j)) = 0) :
    φ (∑ σ : Equiv.Perm (Fin q), mt (fun j => x (σ j))) = 0 := by
  have hP : polyOf φ x = 0 := MvPolynomial.funext fun t => by rw [eval_polyOf, h0, map_zero]
  have hc := congrArg (coeff (∑ j : Fin q, Finsupp.single j 1)) hP
  rw [coeff_zero, polyOf, coeff_sum] at hc
  have hX : ∀ f : Fin q → Fin q, (∏ j, X (f j) : MvPolynomial (Fin q) ℂ) =
      monomial (∑ j, Finsupp.single (f j) 1) 1 := fun f => by
    rw [monomial_sum_one]; rfl
  simp only [hX, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero] at hc
  rw [← Finset.sum_filter] at hc
  have hfil : (Finset.univ.filter fun f : Fin q → Fin q =>
      (∑ j, Finsupp.single (f j) 1 : Fin q →₀ ℕ) = ∑ j, Finsupp.single j 1) =
      Finset.univ.map ⟨fun σ : Equiv.Perm (Fin q) => (σ : Fin q → Fin q), DFunLike.coe_injective⟩ := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk,
      nu_iff]
    exact ⟨fun h => ⟨Equiv.ofBijective f h, rfl⟩, fun ⟨σ, hσ⟩ => hσ ▸ σ.bijective⟩
  rw [hfil, Finset.sum_map] at hc
  rw [map_sum]
  exact hc

end Sym

end WeightTwoPolynomials

open WeightTwoPolynomials in
theorem sw2 : PlacePermOperatorCommutantSpan := by
  intro W _ _ m q Z hZ
  by_contra hZS
  obtain ⟨φ, hφZ, hφS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hZS inferInstance
  have hφ : ∀ y ∈ Submodule.span ℂ {M | ∃ d : W → Matrix (Fin m) (Fin m) ℂ,
      (∀ w, d w ∈ Matrix.unitaryGroup (Fin m) ℂ) ∧ M = tp q (blk d)}, φ y = 0 := by
    intro y hy
    have : φ y ∈ (Submodule.span ℂ _).map φ := Submodule.mem_map_of_mem hy
    rw [hφS] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hU : ∀ d : W → Matrix (Fin m) (Fin m) ℂ, (∀ w, d w ∈ unitaryGroup (Fin m) ℂ) →
      φ (tp q (blk d)) = 0 := fun d hd => hφ _ (Submodule.subset_span ⟨d, hd, rfl⟩)
  have hAll := all_of_herm φ (herm_of_unit φ hU)
  apply hφZ
  have hfac : ((Nat.factorial q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero q)
  have hdec := congrArg φ (decomp Z (sym_of_comm Z hZ))
  rw [map_smul, smul_eq_mul, map_sum] at hdec
  have hterm : ∀ I J, φ (Z I J • symU I J) = 0 := by
    intro I J
    rw [map_smul, smul_eq_mul]
    by_cases h : Z I J = 0
    · rw [h, zero_mul]
    · have hc := compat_of_comm Z hZ I J h
      have h0 : ∀ t : Fin q → ℂ, φ (tp q (∑ j, t j • Matrix.single (I j) (J j) (1 : ℂ))) = 0 := by
        intro t
        rw [eq_blk (∑ j, t j • Matrix.single (I j) (J j) (1 : ℂ))]
        · exact hAll _
        · intro x y hxy
          simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [if_neg, mul_zero]
          rintro ⟨rfl, rfl⟩
          exact hxy (hc j)
      have hs := sym_zero φ (fun j => Matrix.single (I j) (J j) (1 : ℂ)) h0
      rw [sum_perm_mt _ I J fun _ => rfl] at hs
      rw [hs, mul_zero]
  simp only [map_sum, hterm, Finset.sum_const_zero] at hdec
  exact (mul_eq_zero.1 hdec).resolve_left hfac

end PositivityTheory.KB.BlockInvariants

end
end

section
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open Classical

namespace PositivityTheory.KB.BlockInvariants.ComplexBlocks

section Mat

variable {ι : Type} [Fintype ι] {q : ℕ}

def fT' (A : Matrix (Fin q → ι) (Fin q → ι) ℂ) (B : Fin q → Matrix ι ι ℂ) : ℂ :=
  ∑ I, ∑ J, A I J * ∏ i, B i (I i) (J i)

theorem prod_sum_sum (g : Fin q → ι → ι → ℂ) :
    ∏ i, (∑ x, ∑ y, g i x y) = ∑ I : Fin q → ι, ∑ J : Fin q → ι, ∏ i, g i (I i) (J i) := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Fintype.prod_sum]

theorem tp_mul (A B : Matrix ι ι ℂ) : tp q (A * B) = tp q A * tp q B := by
  ext I J
  simp only [tp, of_apply, mul_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

omit [Fintype ι] in
theorem tp_one [DecidableEq ι] : tp q (1 : Matrix ι ι ℂ) = 1 := by
  ext I J
  simp only [tp, of_apply, one_apply]
  by_cases h : I = J
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, I i ≠ J i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem sum4 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem sum3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem fT'_conj (A : Matrix (Fin q → ι) (Fin q → ι) ℂ) (P : Matrix ι ι ℂ) (B : Fin q → Matrix ι ι ℂ) :
    fT' A (fun i => P * B i * Pᴴ) = fT' (tp q Pᵀ * A * tp q (P.map star)) B := by
  have h1 : ∀ (b : Matrix ι ι ℂ) (x y : ι), (P * b * Pᴴ) x y = ∑ u, ∑ v, P x u * b u v * star (P y v) := by
    intro b x y
    simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  unfold fT'
  simp only [h1, prod_sum_sum, Finset.mul_sum]
  rw [sum4]
  refine Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun V _ => ?_
  simp only [mul_apply, tp, of_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun I _ => ?_
  simp only [Finset.prod_mul_distrib]
  ring

end Mat

section GlobalTheory

variable {W : Type} [Fintype W] {m : ℕ}

theorem blk_mul (d e : W → Matrix (Fin m) (Fin m) ℂ) : blk d * blk e = blk fun w => d w * e w := by
  ext x y
  simp only [blk, mul_apply, of_apply]
  rw [Fintype.sum_prod_type]
  simp only
  by_cases h : x.1 = y.1
  · rw [if_pos h, Finset.sum_eq_single x.1]
    · simp only [if_true, h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases h1 : x.1 = w
    · subst h1; simp [h]
    · simp [h1]

theorem blk_one : blk (fun _ : W => (1 : Matrix (Fin m) (Fin m) ℂ)) = 1 := by
  ext x y
  simp only [blk, of_apply, one_apply, Prod.ext_iff]
  by_cases h : x.1 = y.1 <;> simp [h]

theorem blk_transpose (d : W → Matrix (Fin m) (Fin m) ℂ) : (blk d)ᵀ = blk fun w => (d w)ᵀ := by
  ext x y
  simp only [blk, of_apply, transpose_apply]
  by_cases h : x.1 = y.1
  · rw [if_pos h.symm, if_pos h, h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem blk_map_star (d : W → Matrix (Fin m) (Fin m) ℂ) : (blk d).map star = blk fun w => (d w).map star := by
  ext x y
  simp only [blk, of_apply, map_apply]
  split_ifs <;> simp

theorem blk_conjTranspose (d : W → Matrix (Fin m) (Fin m) ℂ) : (blk d)ᴴ = blk fun w => (d w)ᴴ := by
  rw [conjTranspose, blk_transpose, blk_map_star]
  rfl

theorem tp_blk_supp {q : ℕ} (e : W → Matrix (Fin m) (Fin m) ℂ) (X Y : Fin q → Ix W m)
    (h : tp q (blk e) X Y ≠ 0) (i : Fin q) : (X i).1 = (Y i).1 := by
  by_contra hc
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [blk, hc]))

end GlobalTheory

section Herm

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

abbrev K (L : Type) [Field L] [NumberField L] (N : ℕ) : Type := InfinitePlace L × Fin N × Fin N × Bool

def Mm (a b : Fin N) (ε : Bool) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if ε then (if i = a ∧ j = b then Complex.I else 0) - (if i = b ∧ j = a then Complex.I else 0)
    else (if i = a ∧ j = b then 1 else 0) + (if i = b ∧ j = a then 1 else 0)

theorem Mm_herm (a b : Fin N) (ε : Bool) : (Mm a b ε).IsHermitian := by
  ext i j
  simp only [Mm, conjTranspose_apply, of_apply]
  have e1 : (j = a ∧ i = b) = (i = b ∧ j = a) := propext and_comm
  have e2 : (j = b ∧ i = a) = (i = a ∧ j = b) := propext and_comm
  simp only [e1, e2]
  cases ε <;> simp only [Bool.false_eq_true, if_false, if_true] <;> split_ifs <;> simp [Complex.conj_I]

theorem sd1 (f : Fin N → Fin N → ℂ) (i j : Fin N) :
    ∑ a, ∑ b, (if i = a ∧ j = b then f a b else 0) = f i j := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp
  · intro b _ hb; exact Finset.sum_eq_zero fun y _ => by simp [Ne.symm hb]
  · simp

theorem sd2 (f : Fin N → Fin N → ℂ) (i j : Fin N) :
    ∑ a, ∑ b, (if i = b ∧ j = a then f a b else 0) = f j i := by
  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp
  · intro b _ hb; exact Finset.sum_eq_zero fun y _ => by simp [Ne.symm hb]
  · simp

def MH (k : K L N) : HS L N :=
  mkHS (fun w => if w = k.1 then Mm k.2.1 k.2.2.1 k.2.2.2 else 0) fun w => by
    split_ifs
    · exact Mm_herm _ _ _
    · exact isHermitian_zero

def coef (k : K L N) (Y : HS L N) : ℝ :=
  if k.2.2.2 then (mat Y k.1 k.2.1 k.2.2.1).im / 2 else (mat Y k.1 k.2.1 k.2.2.1).re / 2

def c1 (ε : Bool) : ℂ := if ε then -Complex.I / 4 else 1 / 4

def c2 (ε : Bool) : ℂ := if ε then Complex.I / 4 else 1 / 4

theorem mat_expand (z : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ∑ a, ∑ b, ∑ ε, (c1 ε * z a b + c2 ε * z b a) * Mm a b ε i j = z i j := by
  simp only [Fintype.sum_bool, c1, c2, Mm, of_apply, if_true, Bool.false_eq_true, if_false, mul_add, mul_sub,
    mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, sd1, sd2]
  ring_nf
  rw [Complex.I_sq]
  ring

def gc (k : K L N) (x y : Ix (InfinitePlace L) N) : ℂ :=
  (if x = (k.1, k.2.1) ∧ y = (k.1, k.2.2.1) then c1 k.2.2.2 else 0) +
    (if x = (k.1, k.2.2.1) ∧ y = (k.1, k.2.1) then c2 k.2.2.2 else 0)

def lc (k : K L N) (B : Matrix (Ix (InfinitePlace L) N) (Ix (InfinitePlace L) N) ℂ) : ℂ :=
  ∑ x, ∑ y, gc k x y * B x y

theorem sum_delta (p p' : Ix (InfinitePlace L) N) (c : ℂ)
    (B : Matrix (Ix (InfinitePlace L) N) (Ix (InfinitePlace L) N) ℂ) :
    ∑ x, ∑ y, (if x = p ∧ y = p' then c else 0) * B x y = c * B p p' := by
  rw [Finset.sum_eq_single p, Finset.sum_eq_single p']
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; exact Finset.sum_eq_zero fun y _ => by simp [hb]
  · simp

theorem lc_eq (k : K L N) (B : Matrix (Ix (InfinitePlace L) N) (Ix (InfinitePlace L) N) ℂ) :
    lc k B = c1 k.2.2.2 * B (k.1, k.2.1) (k.1, k.2.2.1) + c2 k.2.2.2 * B (k.1, k.2.2.1) (k.1, k.2.1) := by
  simp only [lc, gc, add_mul, Finset.sum_add_distrib, sum_delta]

theorem blk_MH (k : K L N) (x y : Ix (InfinitePlace L) N) :
    blk (fun w => mat (MH k) w) x y = if x.1 = y.1 ∧ x.1 = k.1 then Mm k.2.1 k.2.2.1 k.2.2.2 x.2 y.2 else 0 := by
  simp only [blk, MH, mat_mkHS, of_apply]
  by_cases h : x.1 = y.1
  · rw [if_pos h]
    by_cases h' : x.1 = k.1
    · rw [if_pos h', if_pos ⟨h, h'⟩]
    · rw [if_neg h', if_neg (fun hh => h' hh.2)]; rfl
  · rw [if_neg h, if_neg (fun hh => h hh.1)]

theorem blk_expand (Z : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) :
    blk Z = ∑ k : K L N, lc k (blk Z) • blk (fun w => mat (MH k) w) := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, lc_eq, blk_MH]
  by_cases h : x.1 = y.1
  · have hb : blk Z x y = Z x.1 x.2 y.2 := by simp [blk, h]
    rw [hb, Fintype.sum_prod_type, Finset.sum_eq_single x.1]
    · simp only [true_and, if_true, h]
      simp only [blk, of_apply, if_true, Fintype.sum_prod_type]
      rw [← h]
      exact (mat_expand (Z x.1) x.2 y.2).symm
    · intro b _ hb
      exact Finset.sum_eq_zero fun r _ => by simp [Ne.symm hb]
    · simp
  · rw [show blk Z x y = 0 by simp [blk, h]]
    exact (Finset.sum_eq_zero fun r _ => by simp [h]).symm

theorem lc_herm (k : K L N) (Y : HS L N) : lc k (blk fun w => mat Y w) = (coef k Y : ℂ) := by
  rw [lc_eq]
  have hY : mat Y k.1 k.2.2.1 k.2.1 = star (mat Y k.1 k.2.1 k.2.2.1) := ((mat_herm Y k.1).apply _ _).symm
  simp only [blk, of_apply, if_true, hY, coef, c1, c2]
  apply Complex.ext <;> cases k.2.2.2 <;> simp <;> ring

theorem mat_sum {ι : Type} (s : Finset ι) (f : ι → HS L N) (w : InfinitePlace L) :
    mat (∑ i ∈ s, f i) w = ∑ i ∈ s, mat (f i) w := by
  ext a b
  simp [mat, Submodule.coe_sum, Finset.sum_apply, Matrix.sum_apply]

theorem herm_decomp (Y : HS L N) : Y = ∑ k : K L N, coef k Y • MH k := by
  refine HS_ext fun w => ?_
  ext a b
  have h := congrFun (congrFun (blk_expand (fun w => mat Y w)) (w, a)) (w, b)
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, lc_herm] at h
  simp only [blk, of_apply, if_true] at h
  rw [h, mat_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.real_smul]

variable {q : ℕ}

theorem f_expand (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ) (Y : Fin q → HS L N) :
    f Y = ∑ κ : Fin q → K L N, (∏ i, coef (κ i) (Y i)) * f (fun i => MH (κ i)) := by
  have : f Y = f (fun i => ∑ k : K L N, coef k (Y i) • MH k) := congrArg f (funext fun i => herm_decomp (Y i))
  rw [this, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

theorem fT'_expand (A : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (Z : Fin q → InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) :
    fT' A (fun i => blk (Z i)) =
      ∑ κ : Fin q → K L N, (∏ i, lc (κ i) (blk (Z i))) * fT' A (fun i => blk fun w => mat (MH (κ i)) w) := by
  have h : ∀ (i : Fin q) (x y : Ix (InfinitePlace L) N),
      blk (Z i) x y = ∑ k : K L N, lc k (blk (Z i)) * blk (fun w => mat (MH k) w) x y := by
    intro i x y
    conv_lhs => rw [blk_expand (Z i)]
    simp [Matrix.sum_apply]
  unfold fT'
  simp only [h, Fintype.prod_sum, Finset.prod_mul_distrib, Finset.mul_sum]
  rw [sum3]
  exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => by ring

def Tm (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ) :
    Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ :=
  fun I J => ∑ κ : Fin q → K L N, (∏ i, gc (κ i) (I i) (J i)) * (f (fun i => MH (κ i)) : ℂ)

theorem fT'_Tm (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ)
    (B : Fin q → Matrix (Ix (InfinitePlace L) N) (Ix (InfinitePlace L) N) ℂ) :
    fT' (Tm f) B = ∑ κ : Fin q → K L N, (∏ i, lc (κ i) (B i)) * (f (fun i => MH (κ i)) : ℂ) := by
  unfold fT' Tm lc
  simp only [prod_sum_sum, Finset.sum_mul]
  rw [sum3]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem fT'_Tm_herm (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ) (Y : Fin q → HS L N) :
    fT' (Tm f) (fun i => blk fun w => mat (Y i) w) = (f Y : ℂ) := by
  rw [fT'_Tm, f_expand f Y]
  simp only [lc_herm]
  push_cast
  rfl

theorem Tm_supp (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => HS L N) ℝ) (I J : Fin q → Ix (InfinitePlace L) N)
    (h : Tm f I J ≠ 0) (i : Fin q) : (I i).1 = (J i).1 := by
  by_contra hc
  apply h
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ i), zero_mul]
  have h1 : ¬(I i = ((κ i).1, (κ i).2.1) ∧ J i = ((κ i).1, (κ i).2.2.1)) := by
    rintro ⟨h1, h2⟩; exact hc (by rw [h1, h2])
  have h2 : ¬(I i = ((κ i).1, (κ i).2.2.1) ∧ J i = ((κ i).1, (κ i).2.1)) := by
    rintro ⟨h1, h2⟩; exact hc (by rw [h1, h2])
  simp only [gc, if_neg h1, if_neg h2, add_zero]

theorem conj_supp (d1 d2 : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ)
    (A : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (hA : ∀ I J, A I J ≠ 0 → ∀ i, (I i).1 = (J i).1) (X Y : Fin q → Ix (InfinitePlace L) N)
    (h : (tp q (blk d1) * A * tp q (blk d2)) X Y ≠ 0) (i : Fin q) : (X i).1 = (Y i).1 := by
  rw [mul_apply] at h
  obtain ⟨J, -, hJ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hJ
  rw [mul_apply] at h1
  obtain ⟨I, -, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨h3, h4⟩ := mul_ne_zero_iff.1 hI
  rw [tp_blk_supp d1 X I h3 i, hA I J h4 i, tp_blk_supp d2 J Y h2 i]

theorem blk_E (p p' : Ix (InfinitePlace L) N) (hp : p.1 = p'.1) (x y : Ix (InfinitePlace L) N) :
    blk (fun w => if w = p.1 then Matrix.of (fun a b => if a = p.2 ∧ b = p'.2 then (1 : ℂ) else 0) else 0) x y =
      if x = p ∧ y = p' then 1 else 0 := by
  rcases x with ⟨xw, xa⟩
  rcases y with ⟨yw, ya⟩
  rcases p with ⟨pw, pa⟩
  rcases p' with ⟨pw', pa'⟩
  simp only at hp
  subst hp
  simp only [blk, of_apply, Prod.mk.injEq]
  by_cases h1 : xw = yw
  · subst h1
    by_cases h2 : xw = pw
    · subst h2; simp
    · simp [h2]
  · rw [if_neg h1, if_neg]
    rintro ⟨⟨h2, -⟩, h3, -⟩
    exact h1 (h2.trans h3.symm)

theorem fT'_E (A : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (I J : Fin q → Ix (InfinitePlace L) N) (hc : ∀ i, (I i).1 = (J i).1) :
    fT' A (fun i => blk (fun w => if w = (I i).1 then
      Matrix.of (fun a b => if a = (I i).2 ∧ b = (J i).2 then (1 : ℂ) else 0) else 0)) = A I J := by
  unfold fT'
  simp only [blk_E _ _ (hc _), Finset.prod_boole, Finset.mem_univ, true_imp_iff]
  have e : ∀ I' J' : Fin q → Ix (InfinitePlace L) N, (∀ i, I' i = I i ∧ J' i = J i) ↔ (I' = I ∧ J' = J) := by
    intro I' J'
    simp only [funext_iff, forall_and]
  simp only [e, ite_and, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single I (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem uniq (A A' : Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (hA : ∀ I J, A I J ≠ 0 → ∀ i, (I i).1 = (J i).1) (hA' : ∀ I J, A' I J ≠ 0 → ∀ i, (I i).1 = (J i).1)
    (h : ∀ Z : Fin q → InfinitePlace L → Matrix (Fin N) (Fin N) ℂ,
      fT' A (fun i => blk (Z i)) = fT' A' (fun i => blk (Z i))) : A = A' := by
  ext I J
  by_cases hc : ∀ i, (I i).1 = (J i).1
  · have := h fun i w => if w = (I i).1 then
      Matrix.of (fun a b => if a = (I i).2 ∧ b = (J i).2 then (1 : ℂ) else 0) else 0
    rwa [fT'_E A I J hc, fT'_E A' I J hc] at this
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    have h1 : A I J = 0 := by by_contra h1; exact hi (hA I J h1 i)
    have h2 : A' I J = 0 := by by_contra h2; exact hi (hA' I J h2 i)
    rw [h1, h2]

end Herm

end PositivityTheory.KB.BlockInvariants.ComplexBlocks

namespace PositivityTheory.KB.BlockInvariants

open ComplexBlocks

theorem cplx : Cplx := by
  intro L _ _ N q f hf
  refine ⟨Tm f, fun Y => ?_, fun d hd => ?_⟩
  · show f Y = (fT' (Tm f) (fun i => blk fun w => mat (Y i) w)).re
    rw [fT'_Tm_herm, Complex.ofReal_re]
  · have hd1 : ∀ w, d w * (d w)ᴴ = 1 := fun w => by
      simpa [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.1 (hd w)
    have hd2 : ∀ w, (d w)ᴴ * d w = 1 := fun w => by
      simpa [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff'.1 (hd w)
    set d' : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ := fun w => (d w)ᵀ with hd'
    have ct : ∀ w, (d' w)ᴴ = ((d w)ᴴ)ᵀ := fun w => by ext i j; rfl
    have hu1 : ∀ w, d' w * (d' w)ᴴ = 1 := fun w => by
      rw [ct, hd', ← transpose_mul, hd2, transpose_one]
    have hu2 : ∀ w, (d' w)ᴴ * d' w = 1 := fun w => by
      rw [ct, hd', ← transpose_mul, hd1, transpose_one]
    let u : Gp L N := fun w => ⟨d' w, (d' w)ᴴ, hu1 w, hu2 w⟩
    have hmat : ∀ (Y : HS L N) w, mat (actL u Y) w = d' w * mat Y w * (d' w)ᴴ := by
      intro Y w
      rw [mat_actL]
      simp [u, Units.inv_mk, conjTranspose_conjTranspose]
    have hone : actL u (one L N).1 = (one L N).1 := HS_ext fun w => by
      rw [hmat]
      simp [one, hu1]
    have hinv := hf u hone
    have e1 : (blk d')ᵀ = blk d := by
      rw [blk_transpose]; rfl
    have e2 : (blk d').map star = blk fun w => (d w)ᴴ := by
      rw [blk_map_star]; rfl
    have key : tp q (blk d) * Tm f * tp q (blk fun w => (d w)ᴴ) = Tm f := by
      apply uniq
      · exact conj_supp _ _ _ (Tm_supp f)
      · exact Tm_supp f
      · intro Z
        rw [fT'_expand, fT'_expand]
        refine Finset.sum_congr rfl fun κ _ => ?_
        congr 1
        rw [← e1, ← e2, ← fT'_conj, fT'_Tm_herm]
        have hb : ∀ i, blk d' * blk (fun w => mat (MH (κ i)) w) * (blk d')ᴴ =
            blk fun w => mat (actL u (MH (κ i))) w := fun i => by
          rw [blk_conjTranspose, blk_mul, blk_mul]
          congr 1
          funext w
          rw [hmat]
        simp only [hb]
        rw [fT'_Tm_herm, hinv]
    calc tp q (blk d) * Tm f
        = tp q (blk d) * Tm f * (tp q (blk fun w => (d w)ᴴ) * tp q (blk d)) := by
          rw [← tp_mul, blk_mul, show (fun w => (d w)ᴴ * d w) = fun _ => 1 from funext hd2, blk_one, tp_one,
            Matrix.mul_one]
      _ = (tp q (blk d) * Tm f * tp q (blk fun w => (d w)ᴴ)) * tp q (blk d) := by
          simp only [Matrix.mul_assoc]
      _ = Tm f * tp q (blk d) := by rw [key]

end PositivityTheory.KB.BlockInvariants

end
end

section
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockInvariants

namespace FourierAssembly

variable {L : Type} [Field L] [NumberField L] {N q : ℕ}

theorem sum_place {W : Type} {N q : ℕ} (w : Fin q → W)
    (P : (Fin q → Ix W N) → Prop) [DecidablePred P] (hP : ∀ I, P I ↔ ∀ i, (I i).1 = w i)
    (g : (Fin q → Ix W N) → ℂ) [Fintype W] :
    ∑ I : Fin q → Ix W N, (if P I then g I else 0) = ∑ a : Fin q → Fin N, g (fun i => (w i, a i)) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun a i => (w i, a i)) (fun I i => (I i).2) ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp [hP]
  · intro I _
    simp
  · intro a _
    rfl
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP] at hI
    funext i
    exact Prod.ext (hI i).symm rfl
  · intro a _
    rfl

open Classical in

def fTL (Y : Fin q → HS L N) :
    Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ →ₗ[ℂ] ℂ where
  toFun T := fT T Y
  map_add' T T' := by
    simp only [fT, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a T := by
    simp only [fT, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, RingHom.id_apply]

open Classical in
theorem fT_sum {ι : Type} [Fintype ι] (c : ι → ℂ)
    (M : ι → Matrix (Fin q → Ix (InfinitePlace L) N) (Fin q → Ix (InfinitePlace L) N) ℂ)
    (Y : Fin q → HS L N) : fT (∑ p, c p • M p) Y = ∑ p, c p * fT (M p) Y := by
  calc fT (∑ p, c p • M p) Y = fTL Y (∑ p, c p • M p) := rfl
    _ = ∑ p, fTL Y (c p • M p) := map_sum _ _ _
    _ = ∑ p, c p * fT (M p) Y := by simp only [map_smul, smul_eq_mul]; rfl

open Classical in
theorem fT_perm' (σ : Equiv.Perm (Fin q)) (w : Fin q → InfinitePlace L) (Y : Fin q → HS L N) :
    fT (perm' (m := N) σ w) Y = tmC σ w Y := by
  unfold fT perm' tmC
  simp only [Matrix.of_apply, ite_mul, one_mul, zero_mul]
  have hin : ∀ x : Fin q → Ix (InfinitePlace L) N,
      (∑ J : Fin q → Ix (InfinitePlace L) N,
        if (∀ i, (x i).1 = w i) ∧ J = x ∘ σ then
          ∏ i, blk (fun v => mat (Y i) v) (x i) (J i) else 0) =
      if (∀ i, (x i).1 = w i) then ∏ i, blk (fun v => mat (Y i) v) (x i) (x (σ i)) else 0 := by
    intro x
    by_cases h : ∀ i, (x i).1 = w i
    · rw [if_pos h, Finset.sum_eq_single (x ∘ σ)]
      · rw [if_pos ⟨h, rfl⟩]
        rfl
      · intro J _ hJ
        rw [if_neg (fun hh => hJ hh.2)]
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    · simp [h]
  rw [Finset.sum_congr rfl (fun x _ => hin x)]
  rw [sum_place w _ (fun _ => Iff.rfl)]
  by_cases hw : ∀ i, w (σ i) = w i
  · rw [if_pos hw]
    simp [ContinuousMultilinearMap.sum_apply, blk, ent, hw]
    rfl
  · rw [if_neg hw]
    push_neg at hw
    obtain ⟨i, hi⟩ := hw
    simp only [ContinuousMultilinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [blk, Ne.symm hi]

theorem sign_sq_one (π : Equiv.Perm (Fin q)) :
    ((Equiv.Perm.sign π : ℤ) : ℝ) * ((Equiv.Perm.sign π : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

end FourierAssembly

open FourierAssembly in
open Classical in
theorem fft_of (hC : Cplx) (h1 : PlacePermOperatorBicommutantSpan) (h2 : PlacePermOperatorCommutantSpan) : FFT := by
  intro L _ _ N q β hβ
  obtain ⟨T, hT, hTc⟩ := hC L N q β.toContinuousMultilinearMap (by
    intro u hu Y
    have := congrArg (fun g => g Y) (hβ u hu)
    simpa [Function.comp_def] using this)
  have hTs : T ∈ Submodule.span ℂ (Set.range fun p : Equiv.Perm (Fin q) × (Fin q → InfinitePlace L) =>
      perm' (m := N) p.1 p.2) := by
    apply h1 (InfinitePlace L) N q T
    intro Z hZ
    have hZs := h2 (InfinitePlace L) N q Z hZ
    clear hZ
    induction hZs using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨d, hd, rfl⟩ := hM
      exact (hTc d hd).symm
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]
    | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc, hx]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hTs
  have hf : ∀ Z, β Z = ∑ p : Equiv.Perm (Fin q) × (Fin q → InfinitePlace L),
      ((c p).re * tmR p.1 p.2 false Z - (c p).im * tmR p.1 p.2 true Z) := by
    intro Z
    have := hT Z
    rw [← hc, fT_sum] at this
    simp only [fT_perm'] at this
    rw [show β Z = β.toContinuousMultilinearMap Z from rfl, this, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro p _
    simp [tmR, Complex.mul_re]
  have hperm : ∀ Z, β Z = ((q.factorial : ℕ) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin q), ((Equiv.Perm.sign σ : ℤ) : ℝ) * β (Z ∘ σ) := by
    intro Z
    have hp : ∀ σ : Equiv.Perm (Fin q), β (Z ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * β Z := by
      intro σ
      have := β.toAlternatingMap.map_perm Z σ
      rw [Units.smul_def, zsmul_eq_mul] at this
      exact this
    simp only [hp, ← mul_assoc, sign_sq_one, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨fun x => if x.2.2 then -(c (x.1, x.2.1)).im / (q.factorial : ℝ)
    else (c (x.1, x.2.1)).re / (q.factorial : ℝ), ?_⟩
  ext Y
  rw [hperm Y]
  simp only [hf, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, AT,
    ContinuousMultilinearMap.alternatization_apply_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    smul_eq_mul, Units.smul_def, zsmul_eq_mul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, if_true, Bool.false_eq_true,
    if_false]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  ring

end PositivityTheory.KB.BlockInvariants

end
end

section
noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped Kronecker ComplexOrder

namespace PositivityTheory.KB.BlockInvariants

namespace BlockSumPreservesCone

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
theorem mat_one (N : ℕ) (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

theorem mat_padL (n M : ℕ) (h : HS L n) (w : InfinitePlace L) :
    mat (padL n M h) w = padM (mat h w) := rfl

omit [NumberField L] in
theorem mat_eL (n M : ℕ) (w : InfinitePlace L) :
    mat (eL (L := L) n M) w = padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ) := rfl

def kr {R : Type} [CommRing R] (d : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (d * n)) (Fin (d * n)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) R) ⊗ₖ A)

theorem mat_blkL (d n : ℕ) (h : HS L n) (w : InfinitePlace L) :
    mat (blkL d n h) w = kr d (mat h w) := rfl

theorem padMat_eq {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (padMat ℂ A : Matrix (Fin M) (Fin M) ℂ) = padM A + padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n <;> simp [padMat, padM, hij]

theorem padMat_conjTranspose {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (padMat ℂ A : Matrix (Fin M) (Fin M) ℂ)ᴴ = padMat ℂ Aᴴ := by
  ext i j
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n
  · have hji : (j : ℕ) < n ∧ (i : ℕ) < n := ⟨hij.2, hij.1⟩
    simp [padMat, hij]
  · have hji : ¬((j : ℕ) < n ∧ (i : ℕ) < n) := fun h => hij ⟨h.2, h.1⟩
    by_cases e : i = j
    · subst e
      have hi : ¬(i : ℕ) < n := fun h' => hij ⟨h', h'⟩
      simp [padMat, hi]
    · simp [padMat, hij, hji, e, Ne.symm e]

theorem padMat_mul {n M : ℕ} (h : n ≤ M) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (padMat ℂ (A * B) : Matrix (Fin M) (Fin M) ℂ) = padMat ℂ A * padMat ℂ B :=
  (padHom ℂ h).map_mul A B

theorem padMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n M : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    (padMat R A : Matrix (Fin M) (Fin M) R).map f = padMat S (A.map f) := by
  ext i j
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n
  · simp [padMat, hij]
  · by_cases e : i = j
    · subst e
      have hi : ¬(i : ℕ) < n := fun h' => hij ⟨h', h'⟩
      simp [padMat, hi]
    · simp [padMat, hij, e]

theorem kr_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : (kr d A).map f = kr d (A.map f) := by
  ext i j
  simp only [kr, reindex_apply, map_apply, submatrix_apply, kroneckerMap_apply, one_apply]
  split_ifs <;> simp

theorem kr_conjTranspose (d : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : (kr d A)ᴴ = kr d Aᴴ := by
  ext i j
  simp only [kr, reindex_apply, conjTranspose_apply, submatrix_apply, kroneckerMap_apply, one_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

theorem kr_mul (d : ℕ) {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : kr d (A * B) = kr d A * kr d B := by
  simp only [kr, reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.mul_one]

omit [NumberField L] in
theorem coe_emb_inv {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← Pi.inv_apply, ← map_inv]
  rfl

theorem coe_stab {R : Type} [CommRing R] {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) R) :
    ((stab R n N h g : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) = padMat R (g : Matrix (Fin n) (Fin n) R) :=
  rfl

theorem coe_psi {R : Type} [CommRing R] (d n : ℕ) (g : GL (Fin n) R) :
    ((psi R d n g : GL (Fin (d * n)) R) : Matrix (Fin (d * n)) (Fin (d * n)) R) =
      kr d (g : Matrix (Fin n) (Fin n) R) :=
  rfl

theorem compCLM_comp {V W X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X] {q : ℕ} (f : X [⋀^Fin q]→L[ℝ] ℝ)
    (A : W →L[ℝ] X) (B : V →L[ℝ] W) :
    (f.compContinuousLinearMap A).compContinuousLinearMap B = f.compContinuousLinearMap (A.comp B) := by
  ext v; rfl

theorem fromBlocks_posDef {n k : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    (fromBlocks H 0 0 (1 : Matrix (Fin k) (Fin k) ℂ)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · unfold IsHermitian
    rw [fromBlocks_conjTranspose]
    simp [hH.isHermitian.eq]
  · have hxe : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := (Sum.elim_comp_inl_inr x).symm
    have hst : star x = Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) := by
      ext (i | i) <;> rfl
    rw [hst, hxe, fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add, Matrix.one_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
    by_cases ha : x ∘ Sum.inl = 0
    · have hb : x ∘ Sum.inr ≠ 0 := by
        intro hb
        apply hx
        rw [hxe, ha, hb]
        ext (i | i) <;> rfl
      rw [ha, Matrix.mulVec_zero, star_zero, dotProduct_zero, zero_add]
      exact dotProduct_star_self_pos_iff.2 hb
    · exact add_pos_of_pos_of_nonneg (hH.dotProduct_mulVec_pos ha) (dotProduct_star_self_nonneg _)

theorem padMat_posDef {n M : ℕ} (h : n ≤ M) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    (padMat ℂ H : Matrix (Fin M) (Fin M) ℂ).PosDef := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [padMat_add, reindex_apply]
  exact PosDef.submatrix (fromBlocks_posDef hH) (Equiv.injective _)

theorem kr_posDef (d : ℕ) {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) : (kr d H).PosDef := by
  rw [kr, reindex_apply]
  exact PosDef.submatrix (PosDef.one.kronecker hH) (Equiv.injective _)

end BlockSumPreservesCone

open BlockSumPreservesCone

theorem tStab : TStab := by
  intro L _ _ n N h γ
  apply HS_ext
  intro w
  rw [mat_add]
  show mat (actL (emb L N (stab (𝓞 L) n N h γ)) (one L N).1) w =
    padM (mat (actL (emb L n γ) (one L n).1) w) + padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ)
  rw [mat_actL, mat_actL, coe_emb_inv, coe_emb_inv, ← map_inv, coe_stab, padMat_map, mat_one, mat_one,
    padMat_conjTranspose]
  simp only [Matrix.mul_one]
  rw [← padMat_mul h, padMat_eq]

theorem tBlk : TBlk := by
  intro L _ _ d n γ
  apply HS_ext
  intro w
  show mat (actL (emb L (d * n) (psi (𝓞 L) d n γ)) (one L (d * n)).1) w =
    kr d (mat (actL (emb L n γ) (one L n).1) w)
  rw [mat_actL, mat_actL, coe_emb_inv, coe_emb_inv, ← map_inv, coe_psi, kr_map, mat_one, mat_one,
    kr_conjTranspose]
  simp only [Matrix.mul_one]
  rw [kr_mul]

theorem pStab : PStab := by
  intro L _ _ n N q hnN ω hω g h hh
  let g' : Gp L N := fun w => stab ℂ n N hnN (g w)
  have hg' : ∀ w, (((g' w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      padMat ℂ (((g w)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := fun w => by
    show (((stab ℂ n N hnN (g w))⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = _
    rw [← map_inv, coe_stab]
  have hpadM : ∀ Y : Matrix (Fin n) (Fin n) ℂ, (padM Y : Matrix (Fin N) (Fin N) ℂ) =
      padMat ℂ Y - padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ) := fun Y => by
    rw [padMat_eq Y, add_sub_cancel_right]
  have hJ : padL n N (actL g h) + eL n N = actL g' (padL n N h + eL n N) := HS_ext fun w => by
    rw [mat_add, mat_actL, mat_add, mat_padL, mat_padL, mat_eL, mat_actL, hg', ← padMat_eq (mat h w),
      padMat_conjTranspose, ← padMat_mul hnN, ← padMat_mul hnN, ← padMat_eq]
  have hP : (padL n N).comp (actL g) = (actL g').comp (padL (L := L) n N) := by
    ext1 Y
    apply HS_ext
    intro w
    simp only [ContinuousLinearMap.comp_apply]
    rw [mat_padL, mat_actL, mat_actL, mat_padL, hg', hpadM, hpadM, Matrix.mul_sub, Matrix.sub_mul,
      padMat_conjTranspose, ← padMat_mul hnN, ← padMat_mul hnN, ← padMat_mul hnN, ← padMat_mul hnN,
      Matrix.mul_zero, Matrix.zero_mul]
  have hpos : padL n N h + eL n N ∈ Pos L N := fun w => by
    rw [mat_add, mat_padL, mat_eL, ← padMat_eq]
    exact padMat_posDef hnN (hh w)
  show ((ω (padL n N (actL g h) + eL n N)).compContinuousLinearMap (padL n N)).compContinuousLinearMap
      (actL g) = (ω (padL n N h + eL n N)).compContinuousLinearMap (padL n N)
  rw [hJ, compCLM_comp, hP, ← compCLM_comp, hω g' _ hpos]

theorem blockSum_preserves_cone : PBlk := by
  intro L _ _ d n q ω hω g h hh
  let g' : Gp L (d * n) := fun w => psi ℂ d n (g w)
  have hg' : ∀ w, (((g' w)⁻¹ : GL (Fin (d * n)) ℂ) : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) =
      kr d (((g w)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := fun w => by
    show (((psi ℂ d n (g w))⁻¹ : GL (Fin (d * n)) ℂ) : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) = _
    rw [← map_inv, coe_psi]
  have hJ : blkL d n (actL g h) + 0 = actL g' (blkL d n h + 0) := HS_ext fun w => by
    rw [add_zero, add_zero, mat_actL, mat_blkL, mat_blkL, mat_actL, hg', kr_conjTranspose, kr_mul, kr_mul]
  have hP : (blkL d n).comp (actL g) = (actL g').comp (blkL (L := L) d n) := by
    ext1 Y
    apply HS_ext
    intro w
    simp only [ContinuousLinearMap.comp_apply]
    rw [mat_blkL, mat_actL, mat_actL, mat_blkL, hg', kr_conjTranspose, kr_mul, kr_mul]
  have hpos : blkL d n h + 0 ∈ Pos L (d * n) := fun w => by
    rw [add_zero, mat_blkL]
    exact kr_posDef d (hh w)
  show ((ω (blkL d n (actL g h) + 0)).compContinuousLinearMap (blkL d n)).compContinuousLinearMap
      (actL g) = (ω (blkL d n h + 0)).compContinuousLinearMap (blkL d n)
  rw [hJ, compCLM_comp, hP, ← compCLM_comp, hω g' _ hpos]

end PositivityTheory.KB.BlockInvariants

end
end

section
namespace PositivityTheory.KB.BlockInvariants

theorem aGood : AGood := TwAG.aGood

theorem swt_all (hE : SEv) (hS : SStokes) : SWt :=
  swt hE hS (fft_of cplx sw1 sw2) aGood wPad weylTwoBlockMatrix wInv wOne wCyc tStab tBlk pStab blockSum_preserves_cone

end PositivityTheory.KB.BlockInvariants
end
