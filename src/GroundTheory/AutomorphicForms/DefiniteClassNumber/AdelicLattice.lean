import Mathlib
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Anisotropic
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.LatticeCompact
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)

section Trace

variable (K E) (R : Type*) [CommRing R] [Algebra K R]

def baseTrace : R ⊗[K] E →ₗ[R] R :=
  (Algebra.TensorProduct.rid K R R).toLinearMap ∘ₗ (Algebra.trace K E).baseChange R

variable {K E R}

omit [Algebra.IsQuadraticExtension K E] in
theorem baseTrace_tmul (r : R) (e : E) :
    baseTrace K E R (r ⊗ₜ e) = algebraMap K R (Algebra.trace K E e) * r := by
  simp [baseTrace, Algebra.smul_def]

theorem baseTrace_conjBase (z : R ⊗[K] E) : baseTrace K E R (conjBase K E R z) = baseTrace K E R z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    rw [conjBase_tmul, baseTrace_tmul, baseTrace_tmul, conj_apply, map_sub,
      trace_algebraMap_quadratic]
    congr 2
    ring
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem baseTrace_algebraMap (t : R) : baseTrace K E R (algebraMap R (R ⊗[K] E) t) = 2 * t := by
  have h1 : Algebra.trace K E 1 = 2 := by
    simpa using trace_algebraMap_quadratic (F := K) (E := E) 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    baseTrace_tmul, h1, map_ofNat]

omit [Algebra.IsQuadraticExtension K E] in

theorem baseTrace_tensorMap {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (z : R ⊗[K] E) : baseTrace K E S (tensorMap E f z) = f (baseTrace K E R z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [tensorMap_tmul, baseTrace_tmul, baseTrace_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Trace

section Pairing

variable (K) (R : Type*) [CommRing R] [Algebra K R]

def hermPair (x y : ι → R ⊗[K] E) : R ⊗[K] E :=
  (fun i => conjBase K E R (x i)) ⬝ᵥ (baseMatrix K H R *ᵥ y)

def hermTrace (x y : ι → R ⊗[K] E) : R := baseTrace K E R (hermPair K H R x y)

variable {K H R}

theorem hermPair_self (x : ι → R ⊗[K] E) : hermPair K H R x x = hermValue K H R x := rfl

omit [Fintype ι] in
theorem conjBase_vec_add (x x' : ι → R ⊗[K] E) :
    (fun i => conjBase K E R ((x + x') i)) =
      (fun i => conjBase K E R (x i)) + fun i => conjBase K E R (x' i) :=
  funext fun _ => map_add _ _ _

theorem hermPair_add_left (x x' y : ι → R ⊗[K] E) :
    hermPair K H R (x + x') y = hermPair K H R x y + hermPair K H R x' y := by
  unfold hermPair
  rw [conjBase_vec_add, add_dotProduct]

theorem hermPair_add_right (x y y' : ι → R ⊗[K] E) :
    hermPair K H R x (y + y') = hermPair K H R x y + hermPair K H R x y' := by
  unfold hermPair
  rw [mulVec_add, dotProduct_add]

theorem hermPair_smul_left (c : R ⊗[K] E) (x y : ι → R ⊗[K] E) :
    hermPair K H R (c • x) y = conjBase K E R c * hermPair K H R x y := by
  unfold hermPair
  have : (fun i => conjBase K E R ((c • x) i)) = conjBase K E R c • fun i => conjBase K E R (x i) :=
    funext fun i => by simp [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [this, smul_dotProduct, smul_eq_mul]

theorem hermPair_smul_right (c : R ⊗[K] E) (x y : ι → R ⊗[K] E) :
    hermPair K H R x (c • y) = c * hermPair K H R x y := by
  unfold hermPair
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem conjBase_algebraMap (c : R) :
    conjBase K E R (algebraMap R (R ⊗[K] E) c) = algebraMap R (R ⊗[K] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    conjBase_tmul, map_one]

theorem conjBase_conjBase (z : R ⊗[K] E) : conjBase K E R (conjBase K E R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [conjBase_tmul, conjBase_tmul, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem hermTrace_add_left (x x' y : ι → R ⊗[K] E) :
    hermTrace K H R (x + x') y = hermTrace K H R x y + hermTrace K H R x' y := by
  rw [hermTrace, hermPair_add_left, map_add]; rfl

theorem hermTrace_add_right (x y y' : ι → R ⊗[K] E) :
    hermTrace K H R x (y + y') = hermTrace K H R x y + hermTrace K H R x y' := by
  rw [hermTrace, hermPair_add_right, map_add]; rfl

theorem hermTrace_smul_left (c : R) (x y : ι → R ⊗[K] E) :
    hermTrace K H R (c • x) y = c * hermTrace K H R x y := by
  rw [hermTrace, ← algebraMap_smul (R ⊗[K] E) c x, hermPair_smul_left, conjBase_algebraMap,
    ← Algebra.smul_def, map_smul, smul_eq_mul]; rfl

theorem hermTrace_smul_right (c : R) (x y : ι → R ⊗[K] E) :
    hermTrace K H R x (c • y) = c * hermTrace K H R x y := by
  rw [hermTrace, ← algebraMap_smul (R ⊗[K] E) c y, hermPair_smul_right, ← Algebra.smul_def,
    map_smul, smul_eq_mul]; rfl

variable (K H R) in

def hermTraceBilin : (ι → R ⊗[K] E) →ₗ[R] (ι → R ⊗[K] E) →ₗ[R] R :=
  LinearMap.mk₂ R (hermTrace K H R) hermTrace_add_left hermTrace_smul_left hermTrace_add_right
    hermTrace_smul_right

@[simp]
theorem hermTraceBilin_apply (x y : ι → R ⊗[K] E) : hermTraceBilin K H R x y = hermTrace K H R x y :=
  rfl

section Invariance

variable [DecidableEq ι]

theorem hermPair_mulVec (g : unitaryPoints K E H R) (x y : ι → R ⊗[K] E) :
    hermPair K H R (unitaryMat g *ᵥ x) (unitaryMat g *ᵥ y) = hermPair K H R x y := by
  have hg : ((unitaryMat g).map (conjBase K E R))ᵀ * baseMatrix K H R * unitaryMat g =
      baseMatrix K H R := g.2
  have h1 : (fun i => conjBase K E R ((unitaryMat g *ᵥ x) i)) =
      (unitaryMat g).map (conjBase K E R) *ᵥ (fun i => conjBase K E R (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  unfold hermPair
  rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, Matrix.dotProduct_mulVec]

theorem hermTrace_mulVec (g : unitaryPoints K E H R) (x y : ι → R ⊗[K] E) :
    hermTrace K H R (unitaryMat g *ᵥ x) (unitaryMat g *ᵥ y) = hermTrace K H R x y := by
  rw [hermTrace, hermPair_mulVec]; rfl

end Invariance

theorem hermPair_swap (hH : IsHermitianFor (conjHom K E) H) (x y : ι → R ⊗[K] E) :
    hermPair K H R y x = conjBase K E R (hermPair K H R x y) := by
  have hHb : (baseMatrix K H R).map (conjBase K E R) = (baseMatrix K H R)ᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simp only [transpose_apply, map_apply] at this
    simp only [map_apply, transpose_apply, baseMatrix, Algebra.TensorProduct.includeRight_apply,
      conjBase_tmul, ← this]
    rfl
  unfold hermPair
  rw [RingHom.map_dotProduct]
  have h1 : (conjBase K E R) ∘ (fun i => conjBase K E R (x i)) = x :=
    funext fun i => conjBase_conjBase (x i)
  have h2 : (conjBase K E R) ∘ (baseMatrix K H R *ᵥ y) =
      (baseMatrix K H R).map (conjBase K E R) *ᵥ fun i => conjBase K E R (y i) :=
    funext fun i => RingHom.map_mulVec _ _ _ i
  rw [h1, h2, hHb, Matrix.mulVec_transpose, dotProduct_comm x, Matrix.dotProduct_mulVec]

theorem hermTrace_comm (hH : IsHermitianFor (conjHom K E) H) (x y : ι → R ⊗[K] E) :
    hermTrace K H R y x = hermTrace K H R x y := by
  simp only [hermTrace]
  rw [hermPair_swap hH x y, baseTrace_conjBase]

theorem tensorMap_hermPair {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x y : ι → R ⊗[K] E) :
    tensorMap E f (hermPair K H R x y) =
      hermPair K H S (fun i => tensorMap E f (x i)) (fun i => tensorMap E f (y i)) := by
  unfold hermPair
  have h := RingHom.map_dotProduct (tensorMap E f : R ⊗[K] E →+* S ⊗[K] E)
    (fun i => conjBase K E R (x i)) (baseMatrix K H R *ᵥ y)
  simp only [RingHom.coe_coe] at h
  rw [h]
  congr 1
  · funext i
    exact tensorMap_conjBase f (x i)
  · funext i
    have := RingHom.map_mulVec (tensorMap E f : R ⊗[K] E →+* S ⊗[K] E) (baseMatrix K H R) y i
    simp only [RingHom.coe_coe] at this
    rw [Function.comp_apply, this]
    have h2 := map_includeRight_tensorMap (H := H) f
    simp only [RingHom.coe_coe] at h2
    rw [h2]
    rfl

theorem hermTrace_tensorMap {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x y : ι → R ⊗[K] E) :
    f (hermTrace K H R x y) =
      hermTrace K H S (fun i => tensorMap E f (x i)) (fun i => tensorMap E f (y i)) := by
  rw [hermTrace, hermTrace, ← tensorMap_hermPair, baseTrace_tensorMap]

theorem hermTrace_self_of_hermValue {x : ι → R ⊗[K] E} {t : R}
    (ht : hermValue K H R x = algebraMap R (R ⊗[K] E) t) : hermTrace K H R x x = 2 * t := by
  rw [hermTrace, hermPair_self, ht, baseTrace_algebraMap]

theorem hermPair_smul_smul (c : R ⊗[K] E) (x y : ι → R ⊗[K] E) :
    hermPair K H R (c • x) (c • y) = (conjBase K E R c * c) * hermPair K H R x y := by
  rw [hermPair_smul_left, hermPair_smul_right, mul_assoc]

end Pairing

section Coordinates

variable [DecidableEq ι] (R : Type*) [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def vecCoords (x : ι → R ⊗[K] E) (a : ι × κ) : R :=
  (Algebra.TensorProduct.basis R b).repr (x a.1) a.2

def stdVec (a : ι × κ) : ι → R ⊗[K] E := Pi.single a.1 ((1 : R) ⊗ₜ b a.2)

variable {R}

omit [Algebra.IsQuadraticExtension K E] in

theorem sum_coords_smul_stdVec (x : ι → R ⊗[K] E) :
    ∑ a : ι × κ, vecCoords R b x a • stdVec R b a = x := by
  funext i
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [stdVec, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
  conv_rhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr (x i)]
  simp [vecCoords, Algebra.TensorProduct.basis_apply]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [Fintype κ] in

theorem tensorMap_stdVec (a : ι × κ) :
    (fun i => tensorMap E (Algebra.ofId K R) (stdVec K b a i)) = stdVec R b a := by
  funext i
  simp only [stdVec, Pi.single_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem hermTrace_eq_sum (x y : ι → R ⊗[K] E) :
    hermTrace K H R x y = ∑ a : ι × κ, ∑ c : ι × κ, vecCoords R b x a *
      vecCoords R b y c * algebraMap K R (hermTrace K H K (stdVec K b a) (stdVec K b c)) := by
  have hval : ∀ a c : ι × κ, algebraMap K R (hermTrace K H K (stdVec K b a) (stdVec K b c)) =
      hermTrace K H R (stdVec R b a) (stdVec R b c) := by
    intro a c
    rw [← tensorMap_stdVec (R := R) b a, ← tensorMap_stdVec (R := R) b c]
    exact hermTrace_tensorMap (Algebra.ofId K R) _ _
  simp only [hval]
  conv_lhs => rw [← sum_coords_smul_stdVec b x, ← sum_coords_smul_stdVec b y]
  rw [← hermTraceBilin_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hermTraceBilin_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

end Coordinates

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

section TotallyReal

abbrev realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal) (w : InfinitePlace K) : K →+* ℝ :=
  embedding_of_isReal (hreal w)

omit [NumberField K] in
theorem realEmb_eq_extension (hreal : ∀ w : InfinitePlace K, w.IsReal) (w : InfinitePlace K)
    (k : K) : Completion.extensionEmbeddingOfIsReal (hreal w) (algebraMap K w.Completion k) =
      realEmb hreal w k := by
  rw [Completion.algebraMap_apply]
  exact Completion.extensionEmbeddingOfIsReal_coe (hreal w) _

def embeddingsEquivPlaces (hreal : ∀ w : InfinitePlace K, w.IsReal) :
    (K →+* ℂ) ≃ InfinitePlace K where
  toFun := InfinitePlace.mk
  invFun w := w.embedding
  left_inv φ := by
    show (InfinitePlace.mk φ).embedding = φ
    rcases embedding_mk_eq φ with h | h
    · exact h
    · have hr := isReal_iff.1 (hreal (InfinitePlace.mk φ))
      rw [ComplexEmbedding.isReal_iff, h] at hr
      have hφ : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
      rw [h]
      exact hr.symm.trans hφ
  right_inv w := mk_embedding w

theorem trace_eq_sum_realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal) (t : K) :
    (Algebra.trace ℚ K t : ℝ) = ∑ w, realEmb hreal w t := by
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := t)
  have h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ t = ∑ φ : K →+* ℂ, φ t :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun φ => rfl).symm
  have h3 : ∑ φ : K →+* ℂ, φ t = ∑ w : InfinitePlace K, w.embedding t :=
    Fintype.sum_equiv (embeddingsEquivPlaces hreal) _ _ fun φ => by
      have := (embeddingsEquivPlaces hreal).left_inv φ
      exact (congrFun (congrArg DFunLike.coe this) t).symm
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ), h1, h2, h3, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun w _ => (embedding_of_isReal_apply (hreal w) t).symm


end TotallyReal

section Form

variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def traceGram : Matrix (ι × κ) (ι × κ) K :=
  fun a c => hermTrace K H K (stdVec K b a) (stdVec K b c)

variable (R : Type*) [CommRing R] [Algebra K R]

def vecOfCoords (c : ι × κ → R) : ι → R ⊗[K] E :=
  fun i => (Algebra.TensorProduct.basis R b).equivFun.symm fun k => c (i, k)

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem vecCoords_vecOfCoords (c : ι × κ → R) : vecCoords R b (vecOfCoords b R c) = c := by
  funext a
  simp only [vecCoords, vecOfCoords]
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem vecOfCoords_vecCoords (x : ι → R ⊗[K] E) : vecOfCoords b R (vecCoords R b x) = x := by
  funext i
  simp only [vecCoords, vecOfCoords]
  conv_rhs => rw [← (Algebra.TensorProduct.basis R b).equivFun.symm_apply_apply (x i)]
  rfl

variable {H b}

omit [NumberField K] in

theorem hermTrace_eq_sum_traceGram (x y : ι → R ⊗[K] E) :
    hermTrace K H R x y = ∑ a : ι × κ, ∑ c : ι × κ, vecCoords R b x a * vecCoords R b y c *
      algebraMap K R (traceGram H b a c) :=
  hermTrace_eq_sum H b x y

omit [NumberField K] in

theorem exists_sign_traceGram {w : InfinitePlace K} (hw : w.IsReal)
    (hdef : IsHermDefiniteAt H w hw) :
    ∃ ε : ℝ, ε ≠ 0 ∧ ∀ v : ι × κ → ℝ, v ≠ 0 →
      0 < ε * ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c) := by
  let ψ := Completion.ringEquivRealOfIsReal hw
  have key : ∀ v : ι × κ → ℝ, ψ (hermTrace K H w.Completion (vecOfCoords b w.Completion
      (fun a => ψ.symm (v a))) (vecOfCoords b w.Completion (fun a => ψ.symm (v a)))) =
      ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c) := by
    intro v
    rw [hermTrace_eq_sum_traceGram (H := H) (b := b) w.Completion,
      vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a)), map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    congr 1
    rw [Completion.ringEquivRealOfIsReal_apply, Completion.algebraMap_apply]
    exact Completion.extensionEmbeddingOfIsReal_coe hw _
  have hne : ∀ v : ι × κ → ℝ, v ≠ 0 →
      vecOfCoords b w.Completion (fun a => ψ.symm (v a)) ≠ 0 := by
    intro v hv h
    apply hv
    funext a
    have := congrFun (vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a))) a
    rw [h] at this
    have h0 : vecCoords w.Completion b (0 : ι → w.Completion ⊗[K] E) a = 0 := by
      simp [vecCoords]
    rw [h0] at this
    have := congrArg ψ this
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact this.symm
  rcases hdef with hpos | hneg
  · refine ⟨1, one_ne_zero, fun v hv => ?_⟩
    obtain ⟨t, ht, htpos⟩ := hpos _ (hne v hv)
    rw [one_mul, ← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]
    have : ψ t = Completion.extensionEmbeddingOfIsReal hw t := rfl
    rw [this]
    positivity
  · refine ⟨-1, by norm_num, fun v hv => ?_⟩
    obtain ⟨t, ht, htneg⟩ := hneg _ (hne v hv)
    rw [← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]
    have : ψ t = Completion.extensionEmbeddingOfIsReal hw t := rfl
    rw [this]
    linarith


omit [NumberField K] [Fintype κ] in

theorem traceGram_transpose (hH : IsHermitianFor (conjHom K E) H) :
    (traceGram H b)ᵀ = traceGram H b := by
  ext a c
  exact hermTrace_comm hH _ _

theorem realEmb_mul_hermTrace_pos {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {w : InfinitePlace K} (hw : w.IsReal) {x : ι → K ⊗[K] E} (hx : x ≠ 0) :
    0 < embedding_of_isReal hw (θ * hermTrace K H K x x) := by
  have hv : (fun a => embedding_of_isReal hw (vecCoords K b x a)) ≠ 0 := by
    intro h
    apply hx
    rw [← vecOfCoords_vecCoords b K x]
    have : vecCoords K b x = 0 := by
      funext a
      have := congrFun h a
      simpa using this
    rw [this]
    funext i
    simp [vecOfCoords]
  have := hθ w hw _ hv
  convert this using 1
  rw [hermTrace_eq_sum_traceGram (H := H) (b := b) K, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_mul]
  ring


variable (H b) in

def ratGram (θ : K) :
    Matrix ((ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K)) ((ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ :=
  fun j j' => Algebra.trace ℚ K (θ * integralBasis K j.2 * integralBasis K j'.2 * traceGram H b j.1 j'.1)

omit [Fintype κ] in
theorem ratGram_transpose (hH : IsHermitianFor (conjHom K E) H) (θ : K) :
    (ratGram H b θ)ᵀ = ratGram H b θ := by
  ext j j'
  simp only [transpose_apply, ratGram]
  have := congrFun (congrFun (traceGram_transpose (b := b) hH) j.1) j'.1
  rw [transpose_apply] at this
  rw [this]
  ring_nf



end Form

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain GroundTheory.Global

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

variable (K) in

abbrev FinAdele := FiniteAdeleRing (𝓞 K) K

section Coordinates

variable {R : Type*} [CommRing R] [Algebra K R]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem vecCoords_add (x y : ι → R ⊗[K] E) (a : ι × κ) :
    vecCoords R b (x + y) a = vecCoords R b x a + vecCoords R b y a := by
  simp [vecCoords]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem vecCoords_neg (x : ι → R ⊗[K] E) (a : ι × κ) :
    vecCoords R b (-x) a = -vecCoords R b x a := by
  simp [vecCoords]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem vecCoords_zero (a : ι × κ) : vecCoords R b (0 : ι → R ⊗[K] E) a = 0 := by
  simp [vecCoords]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem vecCoords_smul (c : R) (x : ι → R ⊗[K] E) (a : ι × κ) :
    vecCoords R b (c • x) a = c * vecCoords R b x a := by
  simp [vecCoords]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem mem_stdLattice_iff (O : Subring R) (x : ι → R ⊗[K] E) :
    x ∈ stdLattice ι R b O ↔ ∀ a, vecCoords R b x a ∈ O :=
  ⟨fun h a => h a.1 a.2, fun h i k => h (i, k)⟩

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [Fintype κ] in
theorem vecCoords_stdVec [DecidableEq κ] (a c : ι × κ) :
    vecCoords R b (stdVec R b a) c = if a = c then 1 else 0 := by
  obtain ⟨i, k⟩ := a
  obtain ⟨j, l⟩ := c
  simp only [vecCoords, stdVec, Pi.single_apply]
  by_cases hij : j = i
  · subst hij
    simp only [if_true]
    rw [← Algebra.TensorProduct.basis_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases h : k = l <;> simp [h]
  · have : ¬ (i, k) = (j, l) := fun h => hij (congrArg Prod.fst h).symm
    simp [hij, this]

end Coordinates

variable (K E ι) in

def toFinAdele : (ι → K ⊗[K] E) →+ (ι → FinAdele K ⊗[K] E) :=
  AddMonoidHom.compLeft (tensorMap E (Algebra.ofId K (FinAdele K))).toRingHom.toAddMonoidHom ι

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem toFinAdele_apply (x : ι → K ⊗[K] E) (i : ι) :
    toFinAdele K E ι x i = tensorMap E (Algebra.ofId K (FinAdele K)) (x i) := rfl

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem vecCoords_toFinAdele (x : ι → K ⊗[K] E) (a : ι × κ) :
    vecCoords (FinAdele K) b (toFinAdele K E ι x) a = algebraMap K (FinAdele K) (vecCoords K b x a) := by
  simp only [vecCoords, toFinAdele_apply, repr_tensorMap]
  rfl

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem toFinAdele_smul (k : K) (x : ι → K ⊗[K] E) :
    toFinAdele K E ι (k • x) = algebraMap K (FinAdele K) k • toFinAdele K E ι x := by
  funext i
  simp only [toFinAdele_apply, Pi.smul_apply, map_smul, algebraMap_smul]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem toFinAdele_mul_smul (z : K ⊗[K] E) (x : ι → K ⊗[K] E) :
    toFinAdele K E ι (z • x) = tensorMap E (Algebra.ofId K (FinAdele K)) z • toFinAdele K E ι x := by
  funext i
  simp only [toFinAdele_apply, Pi.smul_apply, smul_eq_mul, map_mul]

def finDiag (H : Matrix ι ι E) : unitaryPoints K E H K →* unitaryPoints K E H (FinAdele K) :=
  unitaryMap K E H (Algebra.ofId K (FinAdele K))

theorem toFinAdele_mulVec {H : Matrix ι ι E} (γ : unitaryPoints K E H K)
    (x : ι → K ⊗[K] E) :
    toFinAdele K E ι (unitaryMat γ *ᵥ x) = unitaryMat (finDiag H γ) *ᵥ toFinAdele K E ι x := by
  funext i
  rw [toFinAdele_apply, finDiag, unitaryMat_unitaryMap]
  exact RingHom.map_mulVec (tensorMap E (Algebra.ofId K (FinAdele K))).toRingHom (unitaryMat γ) x i

omit [Fintype ι] [DecidableEq ι] in

theorem denseRange_toFinAdele : DenseRange (toFinAdele K E ι) := by
  let b := Module.finBasis K E
  let Φ := vecCoordsHomeomorph (ι := ι) (FinAdele K) b
  have hd : DenseRange (Pi.map fun _ : ι => Pi.map fun _ : Fin (Module.finrank K E) => algebraMap K (FinAdele K)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      AdelicGLn.denseRange_algebraMap_finiteAdeleRing K
  have hrange : Set.range (Φ ∘ toFinAdele K E ι) =
      Set.range (Pi.map fun _ : ι => Pi.map fun _ : Fin (Module.finrank K E) => algebraMap K (FinAdele K)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨fun i k => vecCoords K b x (i, k), ?_⟩
      funext i k
      simp only [Φ, Function.comp_apply, Pi.map_apply, vecCoordsHomeomorph,
        Homeomorph.piCongrRight_apply, tensorCoordsHomeomorph_apply]
      exact (vecCoords_toFinAdele b x (i, k)).symm
    · rintro ⟨c, rfl⟩
      refine ⟨vecOfCoords b K fun a => c a.1 a.2, ?_⟩
      funext i k
      simp only [Φ, Function.comp_apply, Pi.map_apply, vecCoordsHomeomorph,
        Homeomorph.piCongrRight_apply, tensorCoordsHomeomorph_apply]
      have := vecCoords_toFinAdele b (vecOfCoords b K fun a => c a.1 a.2) (i, k)
      rw [vecCoords_vecOfCoords] at this
      exact this
  have h1 : DenseRange (Φ ∘ toFinAdele K E ι) := by
    unfold DenseRange
    rw [hrange]
    exact hd
  have h2 : toFinAdele K E ι = Φ.symm ∘ (Φ ∘ toFinAdele K E ι) := by
    funext x
    simp
  rw [h2]
  exact Φ.symm.surjective.denseRange.comp h1 Φ.symm.continuous

theorem exists_int_mul_isIntegral (s : Finset K) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ z ∈ s, IsIntegral ℤ ((m : K) * z) := by
  classical
  let ω := integralBasis K
  let m : ℤ := ∏ z ∈ s, ∏ t, ((ω.repr z t).den : ℤ)
  refine ⟨m, ?_, fun z hz => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun z _ => Finset.prod_ne_zero_iff.2 fun t _ => by
      exact_mod_cast (ω.repr z t).den_nz
  · have hω : ∀ t, IsIntegral ℤ (ω t) := fun t => by
      rw [integralBasis_apply]
      exact RingOfIntegers.isIntegral_coe _
    have hdvd : ∀ t, ((ω.repr z t).den : ℤ) ∣ m := fun t =>
      (Finset.dvd_prod_of_mem (fun t => ((ω.repr z t).den : ℤ)) (Finset.mem_univ t)).trans
        (Finset.dvd_prod_of_mem (fun z => ∏ t, ((ω.repr z t).den : ℤ)) hz)
    have hz' : (m : K) * z = ∑ t, ((m * ω.repr z t : ℚ) : K) * ω t := by
      conv_lhs => rw [← ω.sum_repr z]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Rat.smul_def]
      push_cast
      ring
    rw [hz']
    refine IsIntegral.sum _ fun t _ => IsIntegral.mul ?_ (hω t)
    obtain ⟨k, hk⟩ := hdvd t
    have : (m * ω.repr z t : ℚ) = (k * (ω.repr z t).num : ℤ) := by
      rw [hk]
      push_cast
      rw [mul_comm ((ω.repr z t).den : ℚ) k, mul_assoc, Rat.den_mul_eq_num]
    rw [this, Rat.cast_intCast]
    exact isIntegral_algebraMap (x := ((k * (ω.repr z t).num : ℤ)))

section Lattice

variable (H : Matrix ι ι E)

variable (K) in

abbrev intAdeles : Subring (FinAdele K) := integralFiniteAdeles (𝓞 K) K

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [Fintype ι] [Fintype κ] in
theorem stdLattice_add {x y : ι → FinAdele K ⊗[K] E} (hx : x ∈ stdLattice ι (FinAdele K) b (intAdeles K))
    (hy : y ∈ stdLattice ι (FinAdele K) b (intAdeles K)) :
    x + y ∈ stdLattice ι (FinAdele K) b (intAdeles K) := by
  rw [mem_stdLattice_iff] at *
  intro a
  rw [vecCoords_add]
  exact add_mem (hx a) (hy a)

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [Fintype ι] [Fintype κ] in
theorem stdLattice_smul {x : ι → FinAdele K ⊗[K] E} (hx : x ∈ stdLattice ι (FinAdele K) b (intAdeles K))
    {c : FinAdele K} (hc : c ∈ intAdeles K) : c • x ∈ stdLattice ι (FinAdele K) b (intAdeles K) := by
  rw [mem_stdLattice_iff] at *
  intro a
  rw [vecCoords_smul]
  exact mul_mem hc (hx a)

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [Fintype ι] [Fintype κ] in
theorem stdLattice_sum {s : Finset (ι × κ)} {x : ι × κ → ι → FinAdele K ⊗[K] E}
    (hx : ∀ a ∈ s, x a ∈ stdLattice ι (FinAdele K) b (intAdeles K)) :
    ∑ a ∈ s, x a ∈ stdLattice ι (FinAdele K) b (intAdeles K) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, mem_stdLattice_iff]
    intro a
    rw [vecCoords_zero]
    exact zero_mem _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact stdLattice_add b (hx a (Finset.mem_insert_self a s))
      (ih fun c hc => hx c (Finset.mem_insert_of_mem hc))

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [Fintype κ] in
theorem stdVec_mem_stdLattice [DecidableEq κ] (a : ι × κ) :
    stdVec (FinAdele K) b a ∈ stdLattice ι (FinAdele K) b (intAdeles K) := by
  rw [mem_stdLattice_iff]
  intro c
  rw [vecCoords_stdVec]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

omit [NumberField K] in
theorem unitaryMat_mul {R : Type*} [CommRing R] [Algebra K R] (g g' : unitaryPoints K E H R) :
    unitaryMat (g * g') = unitaryMat g * unitaryMat g' := rfl

omit [NumberField K] in
theorem unitaryMat_inv_mul {R : Type*} [CommRing R] [Algebra K R] (g : unitaryPoints K E H R) :
    unitaryMat g⁻¹ * unitaryMat g = 1 := by
  show (((g⁻¹ : unitaryPoints K E H R) : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) *
    ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

omit [NumberField K] in
theorem unitaryMat_mul_inv {R : Type*} [CommRing R] [Algebra K R] (g : unitaryPoints K E H R) :
    unitaryMat g * unitaryMat g⁻¹ = 1 := by
  show ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) *
    (((g⁻¹ : unitaryPoints K E H R) : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

def adelicLattice (g : unitaryPoints K E H (FinAdele K)) : AddSubgroup (ι → K ⊗[K] E) where
  carrier := {x | unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x ∈ stdLattice ι (FinAdele K) b (intAdeles K)}
  zero_mem' := by
    show unitaryMat g⁻¹ *ᵥ toFinAdele K E ι 0 ∈ stdLattice ι (FinAdele K) b (intAdeles K)
    rw [map_zero, mulVec_zero, mem_stdLattice_iff]
    intro a
    rw [vecCoords_zero]
    exact zero_mem _
  add_mem' := by
    intro x y hx hy
    show unitaryMat g⁻¹ *ᵥ toFinAdele K E ι (x + y) ∈ stdLattice ι (FinAdele K) b (intAdeles K)
    rw [map_add, mulVec_add]
    exact stdLattice_add b hx hy
  neg_mem' := by
    intro x hx
    show unitaryMat g⁻¹ *ᵥ toFinAdele K E ι (-x) ∈ stdLattice ι (FinAdele K) b (intAdeles K)
    rw [map_neg, mulVec_neg, mem_stdLattice_iff]
    intro a
    rw [vecCoords_neg]
    exact neg_mem (((mem_stdLattice_iff b _ _).1 hx) a)

variable {H b}

omit [Fintype κ] in
theorem mem_adelicLattice {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E} :
    x ∈ adelicLattice b H g ↔
      unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x ∈ stdLattice ι (FinAdele K) b (intAdeles K) := Iff.rfl

omit [Fintype κ] in

theorem intSmul_mem_adelicLattice {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E}
    (hx : x ∈ adelicLattice b H g) (z : 𝓞 K) : (z : K) • x ∈ adelicLattice b H g := by
  rw [mem_adelicLattice, toFinAdele_smul, mulVec_smul]
  exact stdLattice_smul b hx (algebraMap_integers_mem_integralFiniteAdeles K z)

end Lattice

section Topology

variable {H : Matrix ι ι E} {b}

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_vecCoords_finAdele (a : ι × κ) :
    Continuous fun z : ι → FinAdele K ⊗[K] E => vecCoords (FinAdele K) b z a := by
  have : (fun z : ι → FinAdele K ⊗[K] E => vecCoords (FinAdele K) b z a) =
      fun z => tensorCoordsHomeomorph (FinAdele K) b (z a.1) a.2 := by
    funext z
    rw [tensorCoordsHomeomorph_apply]
    rfl
  rw [this]
  exact (continuous_apply a.2).comp ((tensorCoordsHomeomorph (FinAdele K) b).continuous.comp
    (continuous_apply a.1))

variable (b H) in

def transLattice (g : unitaryPoints K E H (FinAdele K)) : Set (ι → FinAdele K ⊗[K] E) :=
  {z | unitaryMat g⁻¹ *ᵥ z ∈ stdLattice ι (FinAdele K) b (intAdeles K)}

omit [Fintype κ] in
theorem mem_transLattice {g : unitaryPoints K E H (FinAdele K)} {z : ι → FinAdele K ⊗[K] E} :
    z ∈ transLattice b H g ↔ unitaryMat g⁻¹ *ᵥ z ∈ stdLattice ι (FinAdele K) b (intAdeles K) :=
  Iff.rfl

theorem isOpen_transLattice (g : unitaryPoints K E H (FinAdele K)) : IsOpen (transLattice b H g) :=
  (isOpen_stdLattice (FinAdele K) b (isOpen_integralFiniteAdeles (R := 𝓞 K) (K := K))).preimage
    (continuous_const.matrix_mulVec continuous_id)

theorem isClosed_transLattice (g : unitaryPoints K E H (FinAdele K)) :
    IsClosed (transLattice b H g) := by
  have : T2Space (FinAdele K) := t2Space_finiteAdeleRing K
  have : T2Space (FinAdele K ⊗[K] E) := t2Space_tensor (FinAdele K)
  exact (isCompact_stdLattice (FinAdele K) b (isCompact_integralFiniteAdeles K)).isClosed.preimage
    (continuous_const.matrix_mulVec continuous_id)

theorem closure_image_adelicLattice (g : unitaryPoints K E H (FinAdele K)) :
    closure (toFinAdele K E ι '' (adelicLattice b H g : Set (ι → K ⊗[K] E))) = transLattice b H g := by
  have himage : toFinAdele K E ι '' (adelicLattice b H g : Set (ι → K ⊗[K] E)) =
      transLattice b H g ∩ Set.range (toFinAdele K E ι) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x, rfl⟩
    · rintro ⟨hz, x, rfl⟩
      exact ⟨x, hz, rfl⟩
  apply le_antisymm
  · exact closure_minimal (by rw [himage]; exact Set.inter_subset_left) (isClosed_transLattice g)
  · rw [himage]
    exact denseRange_toFinAdele.open_subset_closure_inter (isOpen_transLattice g)

end Topology

section Integrality

variable {H : Matrix ι ι E} {b}

omit [Fintype κ] [DecidableEq ι] in
theorem algebraMap_hermTrace (x y : ι → K ⊗[K] E) :
    algebraMap K (FinAdele K) (hermTrace K H K x y) =
      hermTrace K H (FinAdele K) (toFinAdele K E ι x) (toFinAdele K E ι y) :=
  hermTrace_tensorMap (Algebra.ofId K (FinAdele K)) x y

omit [Algebra.IsQuadraticExtension K E] in
theorem isIntegral_of_algebraMap_mem {t : K} (h : algebraMap K (FinAdele K) t ∈ intAdeles K) :
    IsIntegral ℤ t := by
  obtain ⟨z, hz⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K t fun v => h v
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

omit [Algebra.IsQuadraticExtension K E] in
theorem algebraMap_mem_of_isIntegral {t : K} (h : IsIntegral ℤ t) :
    algebraMap K (FinAdele K) t ∈ intAdeles K :=
  algebraMap_integers_mem_integralFiniteAdeles K ⟨t, h⟩

variable (H b) in

theorem exists_int_isIntegral_hermTrace : ∃ d : ℤ, d ≠ 0 ∧
    ∀ (g : unitaryPoints K E H (FinAdele K)) (x y : ι → K ⊗[K] E), x ∈ adelicLattice b H g →
      y ∈ adelicLattice b H g → IsIntegral ℤ ((d : K) * hermTrace K H K x y) := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_int_mul_isIntegral
    (Finset.univ.image fun p : (ι × κ) × (ι × κ) => traceGram H b p.1 p.2)
  refine ⟨d, hd0, fun g x y hx hy => isIntegral_of_algebraMap_mem ?_⟩
  rw [map_mul, algebraMap_hermTrace, ← hermTrace_mulVec g⁻¹,
    hermTrace_eq_sum_traceGram (H := H) (b := b) (FinAdele K), Finset.mul_sum]
  refine Subring.sum_mem _ fun a _ => ?_
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ fun c _ => ?_
  have h1 := ((mem_stdLattice_iff b _ _).1 hx) a
  have h2 := ((mem_stdLattice_iff b _ _).1 hy) c
  have h3 := algebraMap_mem_of_isIntegral (hd _ (Finset.mem_image_of_mem _
    (Finset.mem_univ (a, c))))
  rw [map_mul, map_intCast] at h3
  have : algebraMap K (FinAdele K) d * (vecCoords (FinAdele K) b
      (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x) a * vecCoords (FinAdele K) b
      (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι y) c * algebraMap K (FinAdele K) (traceGram H b a c)) =
      vecCoords (FinAdele K) b (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x) a *
        vecCoords (FinAdele K) b (unitaryMat g⁻¹ *ᵥ toFinAdele K E ι y) c *
        ((d : FinAdele K) * algebraMap K (FinAdele K) (traceGram H b a c)) := by
    rw [map_intCast]; ring
  rw [this]
  exact mul_mem (mul_mem h1 h2) h3

end Integrality

section Dual

variable {H : Matrix ι ι E} {b}

omit [DecidableEq ι] in
theorem continuous_sum_coords_mul (p : ι → FinAdele K ⊗[K] E)
    (C : ι × κ → ι × κ → FinAdele K) :
    Continuous fun z : ι → FinAdele K ⊗[K] E =>
      ∑ a, ∑ c, vecCoords (FinAdele K) b p a * vecCoords (FinAdele K) b z c * C a c :=
  continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun c _ =>
    (continuous_const.mul (continuous_vecCoords_finAdele c)).mul continuous_const

variable (H b) in

theorem exists_int_smul_mem_of_forall_isIntegral [DecidableEq κ] (hM : IsUnit (traceGram H b).det) (c : K)
    (hc : c ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ (g : unitaryPoints K E H (FinAdele K)) (y : ι → K ⊗[K] E),
      (∀ x ∈ adelicLattice b H g, IsIntegral ℤ (c * hermTrace K H K y x)) →
        (m : K) • y ∈ adelicLattice b H g := by
  classical
  set M := traceGram H b
  set A : Matrix (ι × κ) (ι × κ) K := c • Mᵀ
  have hA : IsUnit A.det := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 hc)).mul hM
  set N := A⁻¹
  obtain ⟨m, hm0, hm⟩ := exists_int_mul_isIntegral
    (Finset.univ.image fun p : (ι × κ) × (ι × κ) => N p.1 p.2)
  refine ⟨m, hm0, fun g y hy => ?_⟩
  set φ := algebraMap K (FinAdele K)
  set p := toFinAdele K E ι y
  set u := unitaryMat g⁻¹ *ᵥ p
  have hT2 : T2Space (FinAdele K) := t2Space_finiteAdeleRing K

  have hS : ∀ a, φ c * hermTrace K H (FinAdele K) p (unitaryMat g *ᵥ stdVec (FinAdele K) b a) ∈
      intAdeles K := by
    have hclosed : IsClosed {z : ι → FinAdele K ⊗[K] E |
        φ c * hermTrace K H (FinAdele K) p z ∈ intAdeles K} := by
      have hfun : (fun z : ι → FinAdele K ⊗[K] E => φ c * hermTrace K H (FinAdele K) p z) =
          fun z => φ c * ∑ a, ∑ c', vecCoords (FinAdele K) b p a * vecCoords (FinAdele K) b z c' *
            φ (M a c') := by
        funext z
        rw [hermTrace_eq_sum_traceGram (H := H) (b := b) (FinAdele K)]
      have hcont : Continuous fun z : ι → FinAdele K ⊗[K] E =>
          φ c * hermTrace K H (FinAdele K) p z := by
        rw [hfun]
        exact continuous_const.mul (continuous_sum_coords_mul p fun a c' => φ (M a c'))
      exact (isCompact_integralFiniteAdeles K).isClosed.preimage hcont
    have hsub : toFinAdele K E ι '' (adelicLattice b H g : Set (ι → K ⊗[K] E)) ⊆
        {z | φ c * hermTrace K H (FinAdele K) p z ∈ intAdeles K} := by
      rintro _ ⟨x, hx, rfl⟩
      show φ c * hermTrace K H (FinAdele K) p (toFinAdele K E ι x) ∈ intAdeles K
      rw [← algebraMap_hermTrace, ← map_mul]
      exact algebraMap_mem_of_isIntegral (hy x hx)
    have hcl := closure_minimal hsub hclosed
    rw [closure_image_adelicLattice] at hcl
    intro a
    apply hcl
    rw [mem_transLattice, mulVec_mulVec, unitaryMat_inv_mul, one_mulVec]
    exact stdVec_mem_stdLattice b a

  set cu : ι × κ → FinAdele K := fun a => vecCoords (FinAdele K) b u a
  have hAu : ∀ a, (A.map φ *ᵥ cu) a ∈ intAdeles K := by
    intro a
    have h := hS a
    rw [← hermTrace_mulVec g⁻¹, mulVec_mulVec, unitaryMat_inv_mul, one_mulVec,
      hermTrace_eq_sum_traceGram (H := H) (b := b) (FinAdele K)] at h
    simp only [vecCoords_stdVec, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    convert h using 1
    simp only [mulVec, dotProduct, Matrix.map_apply, A, Matrix.smul_apply, Matrix.transpose_apply,
      smul_eq_mul, map_mul, Finset.mul_sum, cu]
    refine Finset.sum_congr rfl fun a' _ => ?_
    ring
  have hcu : cu = N.map φ *ᵥ (A.map φ *ᵥ cu) := by
    rw [mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul A hA, Matrix.map_one φ (map_zero φ)
      (map_one φ), one_mulVec]
  rw [mem_adelicLattice, toFinAdele_smul, mulVec_smul, mem_stdLattice_iff]
  intro a
  rw [vecCoords_smul]
  change φ m * cu a ∈ intAdeles K
  rw [hcu, mulVec, dotProduct, Finset.mul_sum]
  refine Subring.sum_mem _ fun a' _ => ?_
  rw [Matrix.map_apply, ← mul_assoc, ← map_mul]
  exact mul_mem (algebraMap_mem_of_isIntegral (hm _ (Finset.mem_image_of_mem _
    (Finset.mem_univ (a, a'))))) (hAu a')

end Dual

section Generation

variable {H : Matrix ι ι E} {b}

theorem exists_int_smul_mem_adelicLattice [DecidableEq κ] (g : unitaryPoints K E H (FinAdele K)) :
    ∃ r : ℤ, r ≠ 0 ∧ ∀ x : ι → K ⊗[K] E, (∀ a, IsIntegral ℤ (vecCoords K b x a)) →
      (r : K) • x ∈ adelicLattice b H g := by
  classical
  set W0 : Set (FinAdele K) := {t | ∀ a : ι × κ, t • (unitaryMat g⁻¹ *ᵥ stdVec (FinAdele K) b a) ∈
    stdLattice ι (FinAdele K) b (intAdeles K)}
  have hW0 : W0 ∈ 𝓝 (0 : FinAdele K) := by
    have hopen : IsOpen W0 := by
      have : W0 = ⋂ a : ι × κ, (fun t : FinAdele K => t • (unitaryMat g⁻¹ *ᵥ
          stdVec (FinAdele K) b a)) ⁻¹' stdLattice ι (FinAdele K) b (intAdeles K) := by
        ext t
        simp [W0]
      rw [this]
      exact isOpen_iInter_of_finite fun a =>
        (isOpen_stdLattice (FinAdele K) b (isOpen_integralFiniteAdeles (R := 𝓞 K) (K := K))).preimage
          (continuous_id.smul continuous_const)
    refine hopen.mem_nhds fun a => ?_
    rw [zero_smul, mem_stdLattice_iff]
    intro c
    rw [vecCoords_zero]
    exact zero_mem _
  obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW0
  set r : ℕ := Ideal.absNorm (Ideal.span {d})
  have hr0 : r ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨r, by exact_mod_cast hr0, fun x hx => ?_⟩
  rw [mem_adelicLattice, toFinAdele_smul, mulVec_smul]
  have hx' : toFinAdele K E ι x =
      ∑ a, algebraMap K (FinAdele K) (vecCoords K b x a) • stdVec (FinAdele K) b a := by
    conv_lhs => rw [← sum_coords_smul_stdVec b (toFinAdele K E ι x)]
    simp only [vecCoords_toFinAdele]
  rw [hx', mulVec_sum, Finset.smul_sum]
  refine stdLattice_sum b fun a _ => ?_
  rw [mulVec_smul, smul_smul]
  have hre : ((r : ℤ) : K) = algebraMap (𝓞 K) K e * algebraMap (𝓞 K) K d := by
    rw [← map_mul, he, map_natCast, Int.cast_natCast]
  have : algebraMap K (FinAdele K) ((r : ℤ) : K) * algebraMap K (FinAdele K) (vecCoords K b x a) =
      algebraMap K (FinAdele K) (algebraMap (𝓞 K) K d) *
        algebraMap K (FinAdele K) (algebraMap (𝓞 K) K e * vecCoords K b x a) := by
    rw [hre]
    simp only [← map_mul]
    congr 1
    rw [map_mul]
    ring
  rw [this]
  exact hd _ (algebraMap_mem_of_isIntegral ((RingOfIntegers.isIntegral_coe e).mul (hx a))) a

variable (H b) in

theorem exists_int_smul_includeRight_mem (β : E) : ∃ D : ℤ, D ≠ 0 ∧
    ∀ (g : unitaryPoints K E H (FinAdele K)) (x : ι → K ⊗[K] E), x ∈ adelicLattice b H g →
      (D : K) • ((Algebra.TensorProduct.includeRight (R := K) (A := K) β : K ⊗[K] E) • x) ∈ adelicLattice b H g := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_isIntegral
    (Finset.univ.image fun p : κ × κ × κ => b.repr β p.1 * b.repr (b p.1 * b p.2.1) p.2.2)
  refine ⟨D, hD0, fun g x hx => ?_⟩
  rw [mem_adelicLattice, toFinAdele_smul, toFinAdele_mul_smul, mulVec_smul, mulVec_smul,
    mem_stdLattice_iff]
  intro a
  rw [vecCoords_smul]
  have hx' := (mem_stdLattice_iff b _ _).1 hx
  set u := unitaryMat g⁻¹ *ᵥ toFinAdele K E ι x
  have hz : tensorMap E (Algebra.ofId K (FinAdele K)) (Algebra.TensorProduct.includeRight β) =
      (1 : FinAdele K) ⊗ₜ[K] β := by
    rw [tensorMap_includeRight, Algebra.TensorProduct.includeRight_apply]
  have hcoord : vecCoords (FinAdele K) b (((1 : FinAdele K) ⊗ₜ[K] β : FinAdele K ⊗[K] E) • u) a =
      ∑ k, ∑ l, algebraMap K (FinAdele K) (b.repr β k) * vecCoords (FinAdele K) b u (a.1, l) *
        algebraMap K (FinAdele K) (b.repr (b k * b l) a.2) := by
    simp only [vecCoords, Pi.smul_apply, smul_eq_mul]
    rw [repr_mul]
    simp only [repr_one_tmul]
  rw [hz, hcoord, Finset.mul_sum]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ fun l _ => ?_
  have h1 := algebraMap_mem_of_isIntegral (hD _ (Finset.mem_image_of_mem _
    (Finset.mem_univ (k, l, a.2))))
  have : algebraMap K (FinAdele K) (D : K) * (algebraMap K (FinAdele K) (b.repr β k) *
      vecCoords (FinAdele K) b u (a.1, l) * algebraMap K (FinAdele K) (b.repr (b k * b l) a.2)) =
      algebraMap K (FinAdele K) ((D : K) * (b.repr β k * b.repr (b k * b l) a.2)) *
        vecCoords (FinAdele K) b u (a.1, l) := by
    simp only [map_mul]
    ring
  rw [this]
  exact mul_mem h1 (hx' (a.1, l))

end Generation

end GroundTheory.Automorphic
end
end
