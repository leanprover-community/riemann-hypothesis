import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.Reconstruction

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

section Arithmetic

variable {K : Type*} [Field K] [NumberField K]

theorem exists_int_trace_eq {t : K} (ht : IsIntegral ℤ t) : ∃ n : ℤ, Algebra.trace ℚ K t = n :=
  ⟨Algebra.trace ℤ (𝓞 K) ⟨t, ht⟩, (Algebra.coe_trace_int (K := K) ⟨t, ht⟩).symm⟩

theorem exists_int_isIntegral_of_trace :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ t : K, (∀ s, ∃ n : ℤ, Algebra.trace ℚ K (t * integralBasis K s) = n) →
      IsIntegral ℤ ((D : K) * t) := by
  classical
  let B := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_isIntegral (Finset.univ.image fun s => B s)
  refine ⟨D, hD0, fun t ht => ?_⟩
  have hexp : t = ∑ s, (Algebra.trace ℚ K (t * integralBasis K s) : K) * B s := by
    conv_lhs => rw [← B.sum_repr t]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Rat.smul_def]
  rw [hexp, Finset.mul_sum]
  refine IsIntegral.sum _ fun s _ => ?_
  obtain ⟨n, hn⟩ := ht s
  rw [hn, Rat.cast_intCast, mul_left_comm]
  exact (isIntegral_algebraMap (x := n)).mul (hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

end Arithmetic

section Cramer

theorem exists_int_factorial_mul_of_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℤ) (hZ : Z.det ≠ 0) (B : ℕ) (hB : Z.det.natAbs ≤ B) (c : n → ℚ)
    (hc : ∀ j, ∃ m : ℤ, (Z.map (Int.cast : ℤ → ℚ) *ᵥ c) j = m) (i : n) :
    ∃ m : ℤ, (B.factorial : ℚ) * c i = m := by
  choose w hw using hc
  have hZc : Z.map (Int.cast : ℤ → ℚ) *ᵥ c = fun j => (w j : ℚ) := funext hw
  have hadj : (Z.adjugate.map (Int.cast : ℤ → ℚ)) * Z.map (Int.cast : ℤ → ℚ) =
      (Z.det : ℚ) • (1 : Matrix n n ℚ) := by
    have h := congrArg (Int.castRingHom ℚ).mapMatrix (Matrix.adjugate_mul Z)
    simp only [map_mul, RingHom.mapMatrix_apply, Int.coe_castRingHom] at h
    rw [h]
    ext a b
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdetc : (Z.det : ℚ) • c = fun j => ((Z.adjugate *ᵥ w) j : ℚ) := by
    rw [← one_mulVec c, ← smul_mulVec, ← hadj, ← mulVec_mulVec, hZc]
    funext j
    simp [mulVec, dotProduct]
  have hdvd : Z.det ∣ (B.factorial : ℤ) := by
    rw [← Int.natAbs_dvd]
    exact_mod_cast Nat.dvd_factorial (Int.natAbs_pos.2 hZ) hB
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q * (Z.adjugate *ᵥ w) i, ?_⟩
  have := congrFun hdetc i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [show (B.factorial : ℚ) = ((Z.det * q : ℤ) : ℚ) by rw [← hq]; norm_cast]
  rw [Int.cast_mul, Int.cast_mul, mul_comm (Z.det : ℚ) (q : ℚ), mul_assoc, this]

end Cramer

section FiniteSets


end FiniteSets

section ShortBasis

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι E}
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

omit [Fintype κ] [DecidableEq κ] in
theorem intBasis_smul_mem_adelicLattice {b : Basis κ K E}
    {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E} (hx : x ∈ adelicLattice b H g)
    (s : IntBasisIdx K) : (integralBasis K s) • x ∈ adelicLattice b H g := by
  have := intSmul_mem_adelicLattice hx (RingOfIntegers.basis K s)
  rwa [integralBasis_apply]



end ShortBasis

section Coordinates

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι E}
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

omit [DecidableEq ι] [DecidableEq κ] in
theorem card_fin_eq_finrank {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) :
    Fintype.card (Fin N) = finrank ℚ ((ι × κ) × IntBasisIdx K → ℚ) := by
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, hN]

omit [DecidableEq ι] in
theorem ratForm_sum_left' {ι' : Type*} (θ : K) (s : Finset ι') (v : ι' → ι → K ⊗[K] E)
    (y : ι → K ⊗[K] E) : ratForm H θ (∑ i ∈ s, v i) y = ∑ i ∈ s, ratForm H θ (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := ratForm_add_left (H := H) θ 0 0 y
    rw [add_zero] at this
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratForm_add_left, ih]

omit [DecidableEq ι] in
theorem ratForm_sum_right' {ι' : Type*} (θ : K) (s : Finset ι') (x : ι → K ⊗[K] E)
    (v : ι' → ι → K ⊗[K] E) : ratForm H θ x (∑ i ∈ s, v i) = ∑ i ∈ s, ratForm H θ x (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := ratForm_add_right (H := H) θ x 0 0
    rw [add_zero] at this
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratForm_add_right, ih]

def ratBasis {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) :
    Basis (Fin N) ℚ ((ι × κ) × IntBasisIdx K → ℚ) :=
  basisOfCard (linearIndependent_ratCoords hli) (card_fin_eq_finrank hN)

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [DecidableEq κ] in
theorem ratBasis_apply {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K))
    {x : Fin N → ι → K ⊗[K] E} (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) (i : Fin N) :
    ratBasis b hN hli i = ratCoords b (x i) :=
  basisOfCard_apply _ _ _

def basisCoords {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) (y : ι → K ⊗[K] E) : Fin N → ℚ :=
  fun i => (ratBasis b hN hli).repr (ratCoords b y) i

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [DecidableEq κ] in
theorem eq_sum_basisCoords {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K))
    {x : Fin N → ι → K ⊗[K] E} (hli : LinearIndependent ℝ fun i => ratEmb b (x i))
    (y : ι → K ⊗[K] E) : y = ∑ i, (basisCoords b hN hli y i : K) • x i := by
  apply ratCoords_injective b
  rw [ratCoords_sum]
  simp only [ratCoords_smul, ← ratBasis_apply b hN hli, basisCoords]
  exact ((ratBasis b hN hli).sum_repr _).symm

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [DecidableEq κ] in
theorem basisCoords_sum {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K))
    {x : Fin N → ι → K ⊗[K] E} (hli : LinearIndependent ℝ fun i => ratEmb b (x i))
    (c : Fin N → ℚ) : basisCoords b hN hli (∑ i, (c i : K) • x i) = c := by
  funext i
  simp only [basisCoords, ratCoords_sum, ratCoords_smul, ← ratBasis_apply b hN hli]
  have : ∑ i, c i • ratBasis b hN hli i = (ratBasis b hN hli).equivFun.symm c :=
    (Basis.equivFun_symm_apply _ _).symm
  rw [this]
  exact congrFun ((ratBasis b hN hli).equivFun.apply_symm_apply c) i

omit [DecidableEq κ] in

theorem exists_int_factorial_mul_basisCoords (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {c₀ : ℤ} (hc₀ : c₀ ≠ 0) {L : AddSubgroup (ι → K ⊗[K] E)}
    (hQint : ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, (c₀ : ℚ) * ratForm H θ x y = n)
    {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) (hxL : ∀ i, x i ∈ L) {M : ℚ}
    (hM : ∀ i j, |ratForm H θ (x i) (x j)| ≤ M) (y : ι → K ⊗[K] E) (hy : y ∈ L) (i : Fin N) :
    ∃ n : ℤ, ((N.factorial * ⌈|(c₀ : ℚ)| * M⌉₊ ^ N).factorial : ℚ) * basisCoords b hN hli y i = n := by
  classical
  choose Z hZ using fun (j i : Fin N) => hQint (x i) (hxL i) (x j) (hxL j)
  set Zm : Matrix (Fin N) (Fin N) ℤ := Matrix.of Z
  set c := basisCoords b hN hli y
  have hyc : y = ∑ i, (c i : K) • x i := eq_sum_basisCoords b hN hli y

  have hZc : ∀ j, ∃ m : ℤ, (Zm.map (Int.cast : ℤ → ℚ) *ᵥ c) j = m := by
    intro j
    obtain ⟨n, hn⟩ := hQint y hy (x j) (hxL j)
    refine ⟨n, ?_⟩
    rw [← hn]
    conv_rhs => rw [hyc, ratForm_sum_left', Finset.mul_sum]
    simp only [mulVec, dotProduct, Matrix.map_apply, Zm, Matrix.of_apply, ← hZ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ratForm_ratSmul_left]
    ring

  have hZ0 : Zm.det ≠ 0 := by
    intro h0
    have h0' : (Zm.map (Int.cast : ℤ → ℚ)).det = 0 := by
      have := RingHom.map_det (Int.castRingHom ℚ) Zm
      rw [h0, map_zero] at this
      simpa [RingHom.mapMatrix_apply] using this.symm
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    set u := ∑ i, (v i : K) • x i
    have hu : ∀ j, ratForm H θ u (x j) = 0 := by
      intro j
      have h := congrFun hv j
      simp only [mulVec, dotProduct, Matrix.map_apply, Zm, Matrix.of_apply, ← hZ,
        Pi.zero_apply] at h
      have : (c₀ : ℚ) * ratForm H θ u (x j) = 0 := by
        rw [ratForm_sum_left', Finset.mul_sum, ← h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ratForm_ratSmul_left]
        ring
      exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hc₀)
    have huu : ratForm H θ u u = 0 := by
      conv_lhs => arg 4; rw [show u = ∑ i, (v i : K) • x i from rfl]
      rw [ratForm_sum_right']
      exact Finset.sum_eq_zero fun j _ => by rw [ratForm_ratSmul_right, hu, mul_zero]
    have hu0 : u = 0 := by
      by_contra hne
      have := ratForm_self_pos b hreal hθ hne
      linarith
    apply hv0
    have hc := basisCoords_sum b hN hli v
    rw [show ∑ i, ((v i : ℚ) : K) • x i = u from rfl, hu0] at hc
    rw [← hc]
    funext i
    simp [basisCoords, ratCoords_zero]

  have hZb : Zm.det.natAbs ≤ N.factorial * ⌈|(c₀ : ℚ)| * M⌉₊ ^ N := by
    have hentry : ∀ j i, |Zm j i| ≤ (⌈|(c₀ : ℚ)| * M⌉₊ : ℤ) := by
      intro j i
      have h1 : ((|Zm j i| : ℤ) : ℚ) = |(c₀ : ℚ)| * |ratForm H θ (x i) (x j)| := by
        simp only [Zm, Matrix.of_apply, Int.cast_abs, ← hZ, abs_mul]
      have h2 : |(c₀ : ℚ)| * |ratForm H θ (x i) (x j)| ≤ |(c₀ : ℚ)| * M :=
        mul_le_mul_of_nonneg_left (hM i j) (abs_nonneg _)
      have h3 : |(c₀ : ℚ)| * M ≤ (⌈|(c₀ : ℚ)| * M⌉₊ : ℚ) := Nat.le_ceil _
      have : ((|Zm j i| : ℤ) : ℚ) ≤ ((⌈|(c₀ : ℚ)| * M⌉₊ : ℤ) : ℚ) := by
        rw [h1]; push_cast; linarith
      exact_mod_cast this
    have hdet := Matrix.det_le (abv := AbsoluteValue.abs) (A := Zm) hentry
    rw [Fintype.card_fin] at hdet
    have : (Zm.det.natAbs : ℤ) ≤ ((N.factorial * ⌈|(c₀ : ℚ)| * M⌉₊ ^ N : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      simpa [nsmul_eq_mul] using hdet
    exact_mod_cast this
  exact exists_int_factorial_mul_of_mulVec Zm hZ0 _ hZb c hZc i

end Coordinates

section EBound

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι E}
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

omit [NumberField K] in

theorem conjBase_mul_self_algebraMap_mul (ω : K) (e : E) :
    conjBase K E K (algebraMap K (K ⊗[K] E) ω * (1 ⊗ₜ[K] e)) *
        (algebraMap K (K ⊗[K] E) ω * (1 ⊗ₜ[K] e)) =
      algebraMap K (K ⊗[K] E) (ω ^ 2 * Algebra.norm K e) := by
  rw [map_mul, conjBase_algebraMap, conjBase_tmul, map_mul, map_pow,
    Algebra.TensorProduct.algebraMap_apply' (Algebra.norm K e), ← mul_conj]
  have h2 : (1 : K) ⊗ₜ[K] (e * conj K E e) = ((1 : K) ⊗ₜ[K] e) * (1 ⊗ₜ[K] conj K E e) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h2]
  ring

omit [NumberField K] [DecidableEq ι] in
theorem hermTrace_smul_smul_of {z : K ⊗[K] E} {n : K}
    (hz : conjBase K E K z * z = algebraMap K (K ⊗[K] E) n) (x : ι → K ⊗[K] E) :
    hermTrace K H K (z • x) (z • x) = n * hermTrace K H K x x := by
  rw [hermTrace, hermPair_smul_smul, hz, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rfl


end EBound

end GroundTheory.Automorphic
